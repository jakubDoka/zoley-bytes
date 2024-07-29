gpa: std.mem.Allocator,
files: []const Ast,
tmp: struct {
    todo: Alu(Ty) = .{},
    scratch: Alu(Ty) = .{},
    variables: Alu(Value) = .{},
    values: Alu(Id) = .{},
} = .{},
ctx: struct {
    structs: Alu(Struct) = .{},
    funcs: Alu(Func) = .{},
    allocated: Alu(Ty) = .{},
    computed: Ahmu(Symbol, Ty) = .{},
} = .{},
scope: struct {
    ret: Ty = undefined,
    entry: ?Id = null,
    returning: ?Id = null,
} = .{},
out: struct {
    store: Store = .{},
    errors: Alu(u8) = .{},
} = .{},

const std = @import("std");
const Alu = std.ArrayListUnmanaged;
const Ahmu = std.AutoHashMapUnmanaged;
const root = @import("root.zig");
const isa = @import("isa.zig");
const codegen = @import("codegen.zig");
const Vm = @import("vm.zig");
const Ast = @import("parser.zig");
const Lexer = @import("lexer.zig");
const HbvmCg = @import("codegen/hbvm.zig");

pub const Ty = codegen.Ty;
pub const Namespace = codegen.Namespace;
pub const Symbol = codegen.Symbol;
pub const Struct = codegen.Struct;
pub const Tuple = codegen.Tuple;
pub const File = codegen.File;
pub const Size = codegen.Size;

pub const testFmt = codegen.testFmt;
pub const runDiff = codegen.runDiff;
pub const buty = codegen.buty;

const Codegen = @This();

pub const Error = error{ Return, LoopControl, TooLongTuple } || std.mem.Allocator.Error;
pub const Id = root.EnumId(Kind);
pub const Slice = root.EnumSlice(Id);
pub const Store = root.EnumStore(Id, Instr);

const root_file = 0;

pub const Kind = enum {
    Void,
    Arg,
    Li64,
    Add64,
    Sub64,
    Mul64,
    Div64,
    Call,
    Ret,
};

pub const Instr = union(Kind) {
    Void,
    Arg,
    Li64: u64,
    Add64: BinOp,
    Sub64: BinOp,
    Mul64: BinOp,
    Div64: BinOp,
    Call: struct {
        func: Ty,
        args: Slice,
        goto: Id = undefined,
    },
    Ret: Id,

    const BinOp = struct { lhs: Id, rhs: Id };
};

pub const Func = struct {
    file: File,
    args: Tuple,
    ret: Ty,
    decl: Ast.Id,
    entry: Id = undefined,
};

const Value = struct {
    ty: Ty = buty(.void),
    id: Id = Id.zeroSized(.Void),
};

pub fn deinit(self: *Codegen) void {
    inline for (std.meta.fields(@TypeOf(self.tmp))) |field| {
        const f = &@field(self.tmp, field.name);
        if (f.items.len > 0) {
            std.debug.panic("temporary lefover in {s}\n", .{field.name});
        }
        f.deinit(self.gpa);
    }

    inline for (std.meta.fields(@TypeOf(self.ctx))) |field| {
        const f = &@field(self.ctx, field.name);
        f.deinit(self.gpa);
    }

    inline for (std.meta.fields(@TypeOf(self.out))) |field| {
        const f = &@field(self.out, field.name);
        f.deinit(self.gpa);
    }
}

pub fn generate(self: *Codegen) !void {
    _ = try self.findOrDeclare(Ast.Pos.init(0), root_file, "main");
    try self.generateFunc(0);
    try self.completeCallGraph();
}

fn completeCallGraph(self: *Codegen) !void {
    while (self.tmp.todo.popOrNull()) |ty| {
        switch (ty.tag()) {
            .func => try self.generateFunc(ty.index),
            else => |v| std.debug.panic("unhandled call graph type: {any}", .{v}),
        }
    }
}

fn generateFunc(self: *Codegen, id: usize) !void {
    var func = &self.ctx.funcs.items[id];
    const ast = self.files[func.file];
    self.scope = .{ .ret = func.ret };
    const decl = ast.exprs.getTyped(.Fn, func.decl).?;

    for (func.args.view(self.ctx.allocated.items), 0..) |arg_ty, i| {
        try self.tmp.variables.append(self.gpa, .{
            .ty = arg_ty,
            .id = Id.compact(.Arg, @intCast(i)),
        });
    }
    const last_return = try self.catchUnreachable(self.generateExpr(func.file, null, decl.body));
    self.ctx.funcs.items[id].entry = self.scope.entry orelse last_return;
    self.tmp.variables.items.len = 0;
}

fn catchUnreachable(self: *Codegen, res: anytype) Error!Id {
    _ = res catch |e| switch (e) {
        error.Return, error.LoopControl => return self.scope.returning.?,
        else => return e,
    };

    return error.OutOfMemory;
}

fn generateExpr(self: *Codegen, file: File, inferred: ?Ty, id: Ast.Id) Error!Value {
    const ast = self.files[file];
    const gi, const ty = switch (ast.exprs.get(id)) {
        .Void, .Comment => return .{},
        .Return => |ret| {
            self.passControlFlow(try self.out.store.alloc(
                self.gpa,
                .Ret,
                (try self.generateExpr(file, self.scope.ret, ret.value)).id,
            ));
            return error.Return;
        },
        .Integer => |i| .{ Instr{ .Li64 = std.fmt.parseInt(u64, Lexer.peekStr(ast.source, i.index), 10) catch unreachable }, buty(.int) },
        .Block => |block| {
            for (ast.exprs.view(block.stmts)) |stmt| {
                _ = try self.generateExpr(file, null, stmt);
            }
            unreachable;
        },
        .BinOp => |op| b: {
            const lhs = try self.generateExpr(file, inferred, op.lhs);
            const rhs = try self.generateExpr(file, lhs.ty, op.rhs);
            const body = .{ .lhs = lhs.id, .rhs = rhs.id };
            break :b .{ switch (op.op) {
                .@"+" => Instr{ .Add64 = body },
                .@"-" => Instr{ .Sub64 = body },
                .@"*" => Instr{ .Mul64 = body },
                .@"/" => Instr{ .Div64 = body },
                else => std.debug.panic("unhandled binop: {s}", .{@tagName(op.op)}),
            }, rhs.ty };
        },
        .Call => |call| {
            const called = ast.exprs.getTyped(.Ident, call.called).?;
            const func_id = try self.findOrDeclare(called.pos, file, called.id);
            std.debug.assert(func_id.tag() == .func);
            const func = self.ctx.funcs.items[func_id.index];

            for (ast.exprs.view(call.args), 0..) |arg, i| {
                const arg_ty = func.args.view(self.ctx.allocated.items)[i];
                const value = try self.generateExpr(file, arg_ty, arg);
                try self.tmp.values.append(self.gpa, value.id);
            }
            const base = self.tmp.values.items.len - ast.exprs.view(call.args).len;
            const args = try self.out.store.allocSlice(Id, self.gpa, self.tmp.values.items[base..]);
            self.tmp.values.items.len = base;
            const cid = try self.out.store.alloc(self.gpa, .Call, .{ .args = args, .func = func_id });
            self.passControlFlow(cid);
            return .{ .ty = func.ret, .id = cid };
        },
        .Ident => |i| return self.tmp.variables.items[i.id.index],
        else => |v| std.debug.panic("unhandled expr: {any}", .{v}),
    };
    return .{ .ty = ty, .id = try self.out.store.allocDyn(self.gpa, gi) };
}

fn passControlFlow(self: *Codegen, id: Id) void {
    self.scope.entry = self.scope.entry orelse id;
    if (self.scope.returning) |retr| switch (retr.tag()) {
        inline else => |t| {
            const Payload = std.meta.TagPayload(Instr, t);
            if (@typeInfo(Payload) != .Struct or !@hasField(Payload, "goto")) unreachable;
            std.debug.assert(!std.meta.eql(retr, id));
            self.out.store.getTypedPtr(t, retr).?.goto = id;
        },
    };
    self.scope.returning = id;
}

fn findOrDeclare(self: *Codegen, pos: Ast.Pos, file: File, query: anytype) Error!Ty {
    const ast = self.files[file];

    const msg = "Could not find declaration for {s}";
    const decl, const ident = if (@TypeOf(query) == Ast.Ident) b: {
        const decl = ast.decls[query.index];
        const expr = ast.exprs.getTyped(.BinOp, decl.expr).?;
        std.debug.assert(expr.op == .@":=");
        break :b .{ expr.rhs, decl.name };
    } else for (ast.exprs.view(ast.items)) |id| {
        const expr = ast.exprs.getTyped(.BinOp, id) orelse continue;
        std.debug.assert(expr.op == .@":=");
        const name = ast.exprs.getTyped(.Ident, expr.lhs).?;

        if (!switch (@TypeOf(query)) {
            Ast.Pos => query.index == name.id.index,
            else => Ast.cmp(name.pos.index, ast.source, query),
        }) continue;

        break .{ expr.rhs, name.id };
    } else return try self.report(buty(.void), file, pos, msg, .{
        switch (@TypeOf(query)) {
            Ast.Ident => Lexer.peekStr(ast.source, pos.index),
            else => query,
        },
    });

    const sym = Symbol{ .ns = Namespace.init(.file, file), .item = @bitCast(ident) };
    if (self.ctx.computed.get(sym)) |id| return id;

    switch (ast.exprs.get(decl)) {
        .Fn => |f| {
            const func = Func{
                .file = file,
                .decl = decl,
                .args = try self.makeTuple(.Arg, file, f.args),
                .ret = try self.resolveTy(file, f.ret),
            };
            const id = Ty.init(.func, self.ctx.funcs.items.len);
            try self.ctx.funcs.append(self.gpa, func);
            if (@TypeOf(query) == Ast.Ident or !std.mem.eql(u8, query, "main"))
                try self.tmp.todo.append(self.gpa, id);
            try self.ctx.computed.put(self.gpa, sym, id);
            return id;
        },
        .Struct => |s| {
            const stru = Struct{
                .file = file,
                .field_names = s.fields,
                .field_types = try self.makeTuple(.CtorField, file, s.fields),
            };
            const id = Ty.init(.@"struct", self.ctx.structs.items.len);
            try self.ctx.structs.append(self.gpa, stru);
            return id;
        },
        else => |v| std.debug.panic("unhandled declaration: {any}", .{v}),
    }
}

fn makeTuple(self: *Codegen, comptime kind: Ast.Kind, file: File, args: Ast.Slice) !Tuple {
    const ast = self.files[file];
    const arg_exprs = ast.exprs.view(args);
    for (arg_exprs) |id| {
        const arg = ast.exprs.getTyped(kind, id).?;
        const typ = switch (kind) {
            .Arg => arg.ty,
            .CtorField => arg.value,
            else => @compileError("wat"),
        };
        try self.tmp.scratch.append(self.gpa, try self.resolveTy(file, typ));
    }

    var prev_len = self.tmp.scratch.items.len - arg_exprs.len;
    try self.ctx.allocated.appendSlice(self.gpa, self.tmp.scratch.items[prev_len..]);
    self.tmp.scratch.items.len = prev_len;
    prev_len = self.ctx.allocated.items.len - arg_exprs.len;

    const raw_view: *[]const Ty.Repr = @ptrCast(&self.ctx.allocated.items);
    const allocate_types = raw_view.*[prev_len..];
    std.debug.assert(allocate_types.len == ast.exprs.view(args).len);
    const index = std.mem.indexOf(Ty.Repr, raw_view.*, allocate_types) orelse prev_len;
    raw_view.len = @max(prev_len, index + allocate_types.len);
    return try Tuple.init(index, allocate_types.len);
}

fn resolveTy(self: *Codegen, file: File, ty: Ast.Id) !Ty {
    const ast = self.files[file];
    return switch (ast.exprs.get(ty)) {
        .Buty => |b| Ty.init(.builtin, @intFromEnum(b.bt)),
        .UnOp => |u| try self.makePtr(try self.resolveTy(file, u.oper)),
        .Ident => |i| try self.findOrDeclare(i.pos, file, i.id),
        else => |v| std.debug.panic("unhandled type expression: {any}", .{v}),
    };
}

fn makePtr(self: *Codegen, ty: Ty) !Ty {
    if (std.mem.indexOfScalar(u32, @ptrCast(self.ctx.allocated.items), @bitCast(ty))) |idx|
        return Ty.init(.pointer, idx);
    try self.ctx.allocated.append(self.gpa, ty);
    return Ty.init(.pointer, self.ctx.allocated.items.len - 1);
}

pub fn sizeOf(self: *Codegen, ty: Ty) Size {
    return switch (ty.tag()) {
        .builtin => switch (@as(Lexer.Lexeme, @enumFromInt(ty.index))) {
            .void => 0,
            .int => @sizeOf(u64),
            else => std.debug.panic("unhandled builtin type: {s}", .{@tagName(ty.tag())}),
        },
        .pointer => @sizeOf(u64),
        .@"struct" => {
            const stru = self.ctx.structs.items[ty.index];
            var size: Size = 0;
            for (stru.field_types.view(self.ctx.allocated.items)) |fty| {
                size = root.alignTo(size, self.alignOf(fty));
                size += self.sizeOf(fty);
            }
            return size;
        },
        else => |v| std.debug.panic("unhandled type: {s}", .{@tagName(v)}),
    };
}

pub fn alignOf(self: *Codegen, ty: Ty) Size {
    return switch (ty.tag()) {
        .@"struct" => {
            const stru = self.ctx.structs.items[ty.index];
            var alignment: Size = 1;
            for (stru.field_types.view(self.ctx.allocated.items)) |fty| {
                alignment = @max(alignment, self.alignOf(fty));
            }
            return alignment;
        },
        else => self.sizeOf(ty),
    };
}

fn report(self: *Codegen, ph: anytype, file: u32, origin: anytype, comptime fmt: []const u8, args: anytype) !@TypeOf(ph) {
    const pos = self.files[file].posOf(origin);
    const line, const col = self.files[file].lineCol(pos.index);
    try self.out.errors.writer(self.gpa).print(
        "{s}:{d}:{d}: " ++ fmt,
        .{ self.files[file].path, line, col } ++ args,
    );
    return ph;
}

fn runTest(comptime name: []const u8) !void {
    const code = root.findReadmeSnippet(name) catch unreachable;
    try testFmt(name, name ++ ".hb", code);
    try testCodegen(name, code);
}

fn testCodegen(comptime name: []const u8, source: []const u8) !void {
    const gpa = std.testing.allocator;

    var ast = try Ast.init(name ++ ".hb", source, gpa);
    defer ast.deinit(gpa);

    const files = [_]Ast{ast};

    var cg = Codegen{
        .gpa = gpa,
        .files = &files,
    };
    defer cg.deinit();
    try cg.generate();

    var output = std.ArrayList(u8).init(gpa);
    defer output.deinit();

    var code = std.ArrayList(u8).init(gpa);
    defer code.deinit();

    var vm_codegen = HbvmCg{ .gpa = gpa, .cg = &cg, .out = &code };
    defer vm_codegen.deinit(gpa);
    for (0..cg.ctx.funcs.items.len) |id| {
        try vm_codegen.generateFunc(id);
    }
    vm_codegen.finalize();

    const stack = try gpa.alloc(u8, 1024 * 1024);
    defer gpa.free(stack);
    var vm = Vm{};
    vm.regs[HbvmCg.Regs.stack_ptr] = @intFromPtr(stack.ptr[stack.len..]);

    const not_terminated, const exec_log = if (cg.out.errors.items.len != 0) b: {
        try output.appendSlice("\nERRORS\n");
        try output.appendSlice(cg.out.errors.items);
        break :b .{ {}, std.ArrayList(u8).init(gpa) };
    } else b: {
        try output.writer().print("\nDISASM\n", .{});
        try isa.disasm(code.items, &output, false);

        var exec_log = std.ArrayList(u8).init(gpa);
        errdefer exec_log.deinit();
        try exec_log.writer().print("EXECUTION\n", .{});
        vm.fuel = 10000;
        vm.ip = @intFromPtr(code.items.ptr);
        vm.log_buffer = &exec_log;
        var ctx = Vm.UnsafeCtx{};
        const ntrm = std.testing.expectEqual(.tx, vm.run(&ctx));

        try output.writer().print("\nREGISTERS\n", .{});
        try output.writer().print("$1: {d}\n", .{vm.regs[1]});

        break :b .{ ntrm, exec_log };
    };
    defer exec_log.deinit();

    const old, const new = .{ "tests/" ++ name ++ ".temp2.old.txt", name ++ ".temp2.new.txt" };

    const update = std.process.getEnvVarOwned(gpa, "PT_UPDATE") catch "";
    defer gpa.free(update);
    if (update.len > 1) {
        try std.fs.cwd().writeFile(.{
            .sub_path = old,
            .data = std.mem.trim(u8, output.items, "\n"),
        });

        not_terminated catch {
            std.debug.print("\n{s}\n", .{exec_log.items});
        };
    } else {
        try std.fs.cwd().writeFile(.{
            .sub_path = new,
            .data = std.mem.trim(u8, output.items, "\n"),
        });
        const err = runDiff(gpa, old, new);
        try std.fs.cwd().deleteFile(new);

        not_terminated catch {
            std.debug.print("\n{s}\n", .{exec_log.items});
            std.debug.print("\n{s}\n", .{output.items});
        };

        err catch {
            std.debug.print("\n{s}\n", .{exec_log.items});
            std.debug.print("\n{s}\n", .{output.items});
        };

        try err;
    }

    try not_terminated;
}

test "main-fn" {
    try runTest("main-fn");
}

test "arithmetic" {
    try runTest("arithmetic");
}

test "functions" {
    try runTest("functions");
}

test "comments" {
    try runTest("comments");
}
