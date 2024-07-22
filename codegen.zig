gpa: std.mem.Allocator,
cx_stack: std.ArrayListUnmanaged(ItemCtx) = .{},
files: []const Ast = &.{},
cx: ItemCtx = .{},
ct: struct {
    vm: Vm,
    stack: [*]u8,
},
tys: struct {
    computed: std.AutoHashMapUnmanaged(Symbol, Ty) = .{},
    funcs: std.ArrayListUnmanaged(Func) = .{},
} = .{},
comp_stack: std.ArrayListUnmanaged(Ty) = .{},
code: std.ArrayListUnmanaged(u8) = .{},

const std = @import("std");
const root = @import("root.zig");
const isa = @import("isa.zig");
const Ast = @import("parser.zig");
const Vm = @import("vm.zig");
const Lexer = @import("lexer.zig");
const Codegen = @This();
const File = u32;

const stack_size = 1024 * 1024 * 2;
const root_file = 0;

// ## DECLS

const Error = error{Return} || std.mem.Allocator.Error;

const Func = struct {
    file: File,
    decl: Ast.Id,
    ret: Ty,
    base: u32 = std.math.maxInt(u32),
    size: u32 = std.math.maxInt(u32),
};

const Ty = root.TaggedIndex(u32, enum { builtin, func });

const Namespace = root.TaggedIndex(u32, enum { file });

const Symbol = struct {
    const Item = u32;

    ns: Namespace,
    item: Item,

    fn init(ns: Namespace, item: Item) Symbol {
        return .{ .ns = ns, .item = item };
    }
};

const Regs = struct {
    frees: [255]Id = undefined,
    free_count: u8 = 0,
    next: u8,
    max: u8,

    const Id = u8;
    const zero = 0;
    const ret = 1;
    const ret_addr = 31;
    const stack_ptr = 254;

    fn init(start: u8, end: u8) Regs {
        return .{ .next = start, .max = end };
    }

    fn alloc(self: *Regs) Id {
        if (self.free_count != 0) {
            self.free_count -= 1;
            return self.frees[self.free_count];
        }
        if (self.next == self.max) std.debug.panic("Runned out of registers, bummer.", .{});
        defer self.next += 1;
        return self.next;
    }

    fn free(self: *Regs, reg: Id) void {
        if (@import("builtin").mode == .Debug) {
            for (self.frees[0..self.free_count]) |r| {
                std.debug.assert(r != reg);
            }
        }

        self.frees[self.free_count] = reg;
        self.free_count += 1;
    }
};

const ItemCtx = struct {
    ret: ?Ty = null,
    snap: Snapshot = .{},
    regs: Regs = Regs.init(Regs.ret_addr + 1, Regs.stack_ptr - 1),
};

const Loc = struct {
    flags: packed struct(u8) {
        is_comptime: bool = false,
        is_derefed: bool = false,
        is_borrowed: bool = false,
        _: u5 = undefined,
    } = .{},
    reg: Regs.Id = 0,
};

const Value = struct {
    ty: Ty = buty(.void),
    loc: Loc = .{},
};

const Snapshot = struct {
    code: usize = 0,
};

const Ctx = struct {
    ty: ?Ty = null,
    loc: ?Loc = null,
};

// ## FUNCTIONS

pub fn init(gpa: std.mem.Allocator) !Codegen {
    var vm = Vm{};
    const stack = try gpa.alloc(u8, stack_size);
    vm.regs[Regs.stack_ptr] = @intFromPtr(stack.ptr[stack.len..]);

    return .{
        .gpa = gpa,
        .ct = .{
            .vm = vm,
            .stack = stack.ptr,
        },
    };
}

pub fn deinit(self: *Codegen) void {
    self.gpa.free(self.ct.stack[0..stack_size]);
    self.tys.funcs.deinit(self.gpa);
    self.tys.computed.deinit(self.gpa);
    std.debug.assert(self.comp_stack.items.len == 0);
    self.comp_stack.deinit(self.gpa);
    self.code.deinit(self.gpa);
}

pub fn generate(self: *Codegen) !void {
    _ = try self.findOrDeclare(Ast.Pos.init(0), root_file, "main");
    try self.generateFunc(true, 0);
    try self.completeCallGraph(0);
}

fn completeCallGraph(self: *Codegen, base: usize) !void {
    while (self.comp_stack.items.len > base) {
        const ty = self.comp_stack.pop();
        switch (ty.tag()) {
            .func => try self.generateFunc(false, ty.index),
            else => |v| std.debug.panic("unhandled call graph type: {any}", .{v}),
        }
    }
}

fn generateFunc(self: *Codegen, comptime entry: bool, id: usize) !void {
    const func = self.tys.funcs.items[id];
    const ast = self.files[func.file];
    self.cx.ret = func.ret;
    const decl = ast.exprs.getTyped(.Fn, func.decl).?;
    if (try catchUnreachable(self.generateExpr(func.file, .{}, decl.body)) != null) {
        self.report(func.file, ast.posOf(decl.body), "fuction does not return", .{});
    }
    if (entry) try self.emit(.tx, .{});
}

fn emit(self: *Codegen, comptime op: isa.Op, args: anytype) !void {
    try self.code.appendSlice(self.gpa, &isa.pack(op, args));
}

fn catchUnreachable(res: anytype) Error!?@typeInfo(@TypeOf(res)).ErrorUnion.payload {
    return res catch |e| switch (e) {
        error.Return => null,
        else => e,
    };
}

fn generateExpr(self: *Codegen, file: File, ctx: Ctx, id: Ast.Id) Error!Value {
    const ast = self.files[file];
    switch (ast.exprs.get(id)) {
        .Void => return .{},
        .Block => |block| {
            for (ast.exprs.view(block.stmts)) |stmt| {
                _ = try self.generateExpr(file, .{}, stmt);
            }
            return .{};
        },
        .Return => |ret| {
            const retCtx = Ctx{
                .ty = self.cx.ret,
                .loc = .{ .reg = 1, .flags = .{ .is_borrowed = true } },
            };
            _ = try self.generateExpr(file, retCtx, ret.value);
            return error.Return;
        },
        .Integer => |i| {
            const int_token = Lexer.peek(ast.source, i.index);
            const int_value = std.fmt.parseInt(u64, int_token.view(ast.source), 10) catch |e| {
                self.report(file, i, "Could not parse integer: {any}", .{e});
            };
            const loc = ctx.loc orelse Loc{ .reg = self.cx.regs.alloc() };
            try self.emit(.li64, .{ loc.reg, int_value });
            return Value{ .ty = ctx.ty orelse buty(.int), .loc = loc };
        },
        else => |v| std.debug.panic("unhandled expr: {any}", .{v}),
    }
}

fn buty(ty: Lexer.Lexeme) Ty {
    return Ty.init(.builtin, @intFromEnum(ty));
}

fn snapshot(self: *Codegen) Snapshot {
    return .{ .code = self.code };
}

fn findOrDeclare(self: *Codegen, pos: Ast.Pos, file: File, query: anytype) !Ty {
    const ast = self.files[file];

    const decl = for (ast.exprs.view(ast.items)) |id| {
        const expr = ast.exprs.getTyped(.BinOp, id).?;
        std.debug.assert(expr.op == .@":=");
        const name = ast.exprs.getTyped(.Ident, expr.lhs).?;

        if (!switch (@TypeOf(query)) {
            Ast.Ident => query == name.id,
            else => std.mem.eql(u8, query, name.id.view(ast.source)),
        }) continue;

        break expr.rhs;
    } else self.report(file, pos, "Could not find declaration for {s}", .{
        switch (@TypeOf(query)) {
            Ast.Ident => query.view(ast.source),
            else => query,
        },
    });

    return switch (ast.exprs.get(decl)) {
        .Fn => |f| b: {
            const ret = try self.resolveTy(file, f.ret);
            const func = Func{ .file = file, .decl = decl, .ret = ret };
            const id = Ty.init(.func, self.tys.funcs.items.len);
            try self.tys.funcs.append(self.gpa, func);
            if (@TypeOf(query) == Ast.Ident or !std.mem.eql(u8, query, "main"))
                try self.comp_stack.append(self.gpa, id);
            break :b id;
        },
        else => |v| std.debug.panic("unhandled declaration: {any}", .{v}),
    };
}

fn resolveTy(self: *Codegen, file: File, ty: Ast.Id) !Ty {
    const ast = self.files[file];
    return switch (ast.exprs.get(ty)) {
        .Buty => |b| Ty.init(.builtin, @intFromEnum(b.bt)),
        else => |v| std.debug.panic("unhandled type expression: {any}", .{v}),
    };
}

fn report(self: *Codegen, file: u32, pos: Ast.Pos, comptime fmt: []const u8, args: anytype) noreturn {
    const line, const col = self.files[file].lineCol(pos.index);
    std.debug.panic("{s}:{d}:{d}: " ++ fmt, .{ self.files[file].path, line, col } ++ args);
}

fn testSnippet(comptime name: []const u8) !void {
    const code = comptime root.findReadmeSnippet(name) catch unreachable;
    try testFmt(name, name ++ ".hb", code);
    try testCodegen(name, code);
}

fn testCodegen(comptime name: []const u8, code: []const u8) !void {
    const gpa = std.testing.allocator;

    var ast = try Ast.init(name ++ ".hb", code, gpa);
    defer ast.deinit(gpa);

    const files = [_]Ast{ast};

    var codegen = try Codegen.init(gpa);
    defer codegen.deinit();

    codegen.files = &files;

    try codegen.generate();

    var output = std.ArrayList(u8).init(gpa);
    defer output.deinit();

    try output.writer().print("EXECUTION\n", .{});

    codegen.ct.vm.fuel = 1000;
    codegen.ct.vm.ip = @intFromPtr(codegen.code.items.ptr);
    codegen.ct.vm.log_buffer = &output;
    var ctx = Vm.UnsafeCtx{};
    try std.testing.expectEqual(.tx, codegen.ct.vm.run(&ctx));

    try output.writer().print("\nDISASM\n", .{});

    try isa.disasm(codegen.code.items, &output);

    try output.writer().print("\nREGISTERS\n", .{});

    for (codegen.ct.vm.regs[1..], 1..) |r, i| {
        var reg = r;
        if (i == Regs.stack_ptr) {
            reg -= @as(u64, @intFromPtr(codegen.ct.stack));
            reg = stack_size - reg;
        }
        if (reg == 0) continue;
        try output.writer().print("${d}: {d}\n", .{ i, reg });
    }

    const old, const new = .{ "tests/" ++ name ++ ".temp.old.txt", name ++ ".temp.new.txt" };

    const update = std.process.getEnvVarOwned(gpa, "PT_UPDATE") catch "";
    defer gpa.free(update);

    if (update.len > 1) {
        try std.fs.cwd().writeFile(.{
            .sub_path = old,
            .data = std.mem.trim(u8, output.items, "\n"),
        });
    } else {
        try std.fs.cwd().writeFile(.{
            .sub_path = new,
            .data = std.mem.trim(u8, output.items, "\n"),
        });
        const err = runDiff(gpa, old, new);
        try std.fs.cwd().deleteFile(new);
        try err;
    }
}

fn testFmt(comptime name: []const u8, path: []const u8, code: []const u8) !void {
    const gpa = std.testing.allocator;

    var ast = try Ast.init(path, code, gpa);
    defer ast.deinit(gpa);

    var fmtd = std.ArrayList(u8).init(gpa);
    defer fmtd.deinit();

    try ast.fmt(&fmtd);

    const old, const new = .{ name ++ ".temp.old.txt", name ++ ".temp.new.txt" };

    try std.fs.cwd().writeFile(.{ .sub_path = new, .data = std.mem.trim(u8, fmtd.items, "\n") });
    try std.fs.cwd().writeFile(.{ .sub_path = old, .data = std.mem.trim(u8, code, "\n") });
    const err = runDiff(gpa, old, new);
    try std.fs.cwd().deleteFile(old);
    try std.fs.cwd().deleteFile(new);

    try err;
}

fn runDiff(gpa: std.mem.Allocator, old: []const u8, new: []const u8) !void {
    var child = std.process.Child.init(&.{ "diff", "--unified", "--color", old, new }, gpa);
    child.stdout_behavior = .Pipe;
    child.stderr_behavior = .Pipe;

    try child.spawn();

    const stdout = try child.stderr.?.readToEndAlloc(gpa, 1024 * 10);
    defer gpa.free(stdout);
    const stderr = try child.stdout.?.readToEndAlloc(gpa, 1024 * 10);
    defer gpa.free(stderr);

    const exit = (try child.wait()).Exited;
    if (exit != 0) {
        if (stdout.len > 0) std.debug.print("stdout:\n{s}", .{stdout});
        if (stderr.len > 0) std.debug.print("stderr:\n{s}", .{stderr});
    }
    try std.testing.expectEqual(0, exit);
}

test "main-fn" {
    try testSnippet("main-fn");
}
