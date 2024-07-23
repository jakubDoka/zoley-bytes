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
    allocated: std.ArrayListUnmanaged(Ty) = .{},
} = .{},
comp_stack: std.ArrayListUnmanaged(Ty) = .{},
value_buf: std.ArrayListUnmanaged(Value) = .{},
output: struct {
    code: std.ArrayListUnmanaged(u8) = .{},
    funcs: std.ArrayListUnmanaged(ItemReloc) = .{},
} = .{},
variables: std.ArrayListUnmanaged(Variable) = .{},
ret_relocs: std.ArrayListUnmanaged(i16) = .{},

const std = @import("std");
const root = @import("root.zig");
const isa = @import("isa.zig");
const Ast = @import("parser.zig");
const Vm = @import("vm.zig");
const Lexer = @import("lexer.zig");
const Codegen = @This();
const File = u32;

const vm_stack_size = 1024 * 1024 * 2;
const root_file = 0;
const debug = @import("builtin").mode == .Debug;

// ## DECLS

const Error = error{ Return, TooLongTuple } || std.mem.Allocator.Error;

const Variable = struct {
    name: Ast.Ident,
    value: Value,
};

const ItemReloc = struct {
    to: u32,
    offset: u32,
};

const Tuple = packed struct(u32) {
    const Len = u4;
    const Base = std.meta.Int(.unsigned, @bitSizeOf(u32) - @bitSizeOf(Len));

    len: Len,
    base: Base,

    pub fn init(base: usize, len: usize) !Tuple {
        if (base > std.math.maxInt(Base)) return error.TooLongTuple;
        return .{ .len = @intCast(len), .base = @intCast(base) };
    }

    pub fn view(self: Tuple, slice: []const Ty) []const Ty {
        return slice[self.base..][0..self.len];
    }
};

const Func = struct {
    file: File,
    decl: Ast.Id,
    args: Tuple,
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
    frees: [254]Id = undefined,
    free_count: u8 = 0,
    next: u8,
    min: u8,
    max: u8,
    ret_used: bool = false,

    allocs: if (debug) [10]AllocData else void = undefined,
    alloc_count: if (debug) u8 else void = if (debug) 0,
    const Id = u8;
    const zero = 0;
    const ret = 1;
    const ret_addr = 31;
    const stack_ptr = 254;

    const AllocData = struct {
        id: Id,
        index: usize,
        frames: [10]usize,
        frame_count: usize,
    };

    fn init(start: u8, end: u8) Regs {
        return .{ .next = start, .max = end, .min = start };
    }

    fn alloc_ret(self: *Regs) ?Id {
        if (self.ret_used) return null;
        if (debug) self.addAlloc(@returnAddress(), ret);
        self.ret_used = true;
        return ret;
    }

    fn alloc(self: *Regs) Id {
        if (self.free_count != 0) {
            self.free_count -= 1;
            if (debug) self.addAlloc(@returnAddress(), self.frees[self.free_count]);
            return self.frees[self.free_count];
        }
        if (self.next == self.max) std.debug.panic("Runned out of registers, bummer.", .{});
        defer self.next += 1;
        if (debug) self.addAlloc(@returnAddress(), self.next);
        return self.next;
    }

    fn addAlloc(self: *Regs, return_addr: usize, reg: Id) void {
        const alloc_data = &self.allocs[self.alloc_count];
        var stack_trace = std.builtin.StackTrace{
            .index = undefined,
            .instruction_addresses = &alloc_data.frames,
        };
        std.debug.captureStackTrace(return_addr, &stack_trace);
        alloc_data.id = reg;
        alloc_data.index = stack_trace.index;
        alloc_data.frame_count = stack_trace.instruction_addresses.len;
        self.alloc_count += 1;
    }

    fn free(self: *Regs, reg: Id) void {
        if (debug) {
            for (self.frees[0..self.free_count]) |r| {
                std.debug.assert(r != reg);
            }

            const index = for (self.allocs[0..self.alloc_count], 0..) |r, i| {
                if (r.id == reg) break i;
            } else std.debug.panic("Could not find reg in allocs: {d}", .{reg});

            self.alloc_count -= 1;
            std.mem.swap(AllocData, &self.allocs[index], &self.allocs[self.alloc_count]);
        }

        if (reg == ret) {
            self.ret_used = false;
            return;
        }

        self.frees[self.free_count] = reg;
        self.free_count += 1;
    }

    fn checkLeaks(self: *Regs) void {
        if (debug) {
            for (self.allocs[0..self.alloc_count]) |*alloc_data| {
                const stack_trace = std.builtin.StackTrace{
                    .index = alloc_data.index,
                    .instruction_addresses = alloc_data.frames[0..alloc_data.frame_count],
                };
                std.debug.print("leaked reg: {d}\n", .{alloc_data.id});
                std.debug.dumpStackTrace(stack_trace);
            }
        }
        if (self.free_count != self.next - self.min)
            std.debug.panic("Not all registers freed: {d} != {d}", .{ self.free_count, self.next - self.min });
    }
};

const ItemCtx = struct {
    ret: ?Ty = null,
    snap: Snapshot = .{},
    regs: Regs = Regs.init(Regs.ret_addr + 1, Regs.stack_ptr - 1),
    cond_op_size: ?*u8 = null,
};

const Loc = struct {
    flags: packed struct(u8) {
        is_comptime: bool = false,
        is_derefed: bool = false,
        is_borrowed: bool = false,
        _: u5 = undefined,
    } = .{},
    reg: Regs.Id = 0,

    fn borrow(self: Loc) Loc {
        var loc = self;
        loc.flags.is_borrowed = true;
        return loc;
    }
};

const Value = struct {
    ty: Ty = buty(.void),
    loc: Loc = .{},

    fn borrow(self: Value) Value {
        return .{ .ty = self.ty, .loc = self.loc.borrow() };
    }
};

const Snapshot = struct {
    code: usize = 0,
    funcs: usize = 0,
};

const Ctx = struct {
    ty: ?Ty = null,
    loc: ?Loc = null,
};

// ## FUNCTIONS

pub fn init(gpa: std.mem.Allocator) !Codegen {
    var vm = Vm{};
    const stack = try gpa.alloc(u8, vm_stack_size);
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
    self.gpa.free(self.ct.stack[0..vm_stack_size]);
    self.tys.funcs.deinit(self.gpa);
    self.tys.computed.deinit(self.gpa);
    self.tys.allocated.deinit(self.gpa);
    std.debug.assert(self.comp_stack.items.len == 0);
    self.comp_stack.deinit(self.gpa);
    self.output.code.deinit(self.gpa);
    self.output.funcs.deinit(self.gpa);
    std.debug.assert(self.variables.items.len == 0);
    self.variables.deinit(self.gpa);
    std.debug.assert(self.value_buf.items.len == 0);
    self.value_buf.deinit(self.gpa);
    std.debug.assert(self.ret_relocs.items.len == 0);
    self.ret_relocs.deinit(self.gpa);
}

pub fn generate(self: *Codegen) !void {
    _ = try self.findOrDeclare(Ast.Pos.init(0), root_file, "main");
    try self.generateFunc(true, 0);
    try self.completeCallGraph(0);
    try self.link();
}

fn link(self: *Codegen) !void {
    for (self.output.funcs.items) |func_reloc|
        self.relocateJump(self.tys.funcs.items[func_reloc.to].base, func_reloc.offset, 3);
}

fn relocateJump(self: *Codegen, to: anytype, offset: u32, sub_offset: u4) void {
    const Repr = std.meta.Int(.signed, @bitSizeOf(@TypeOf(to)));
    const jump = @as(Repr, @intCast(to)) - @as(Repr, @intCast(offset));
    self.writeReloc(Repr, offset + sub_offset, jump);
}

fn writeLocalReloc(self: *Codegen, comptime T: type, offset: usize, value: T) void {
    self.writeReloc(T, self.cx.snap.code + offset, value);
}

fn writeReloc(self: *Codegen, comptime T: type, offset: usize, value: T) void {
    std.debug.assert(std.mem.allEqual(u8, self.output.code.items[offset..][0..@sizeOf(T)], 0));
    self.output.code.items[offset..][0..@sizeOf(T)].* = @bitCast(value);
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
    var func = &self.tys.funcs.items[id];
    const ast = self.files[func.file];
    self.cx.ret = func.ret;
    self.cx.snap = self.snapshot();
    const decl = ast.exprs.getTyped(.Fn, func.decl).?;

    if (!entry) {
        try self.emit(.addi64, .{ Regs.stack_ptr, Regs.stack_ptr, 0 });
        try self.emit(.st, .{ Regs.ret_addr, Regs.stack_ptr, 0, 0 });
    }

    for (
        func.args.view(self.tys.allocated.items),
        ast.exprs.view(decl.args),
        2..,
    ) |arg_ty, arg_decl_id, arg_reg| {
        const arg_decl = ast.exprs.getTyped(.Arg, arg_decl_id).?;
        const msg = "Compiled does not (yes) support patterns here";
        const bindings = ast.exprs.getTyped(.Ident, arg_decl.bindings) orelse
            self.report(func.file, ast.posOf(arg_decl.bindings), msg, .{});
        const loc = Loc{ .reg = self.cx.regs.alloc() };
        try self.emit(.cp, .{ loc.reg, arg_reg });
        try self.variables.append(self.gpa, .{
            .name = bindings.id,
            .value = .{ .ty = arg_ty, .loc = loc },
        });
    }
    if (try catchUnreachable(self.generateExpr(func.file, .{}, decl.body)) != null) {
        self.report(func.file, ast.posOf(decl.body), "fuction does not return", .{});
    }

    func = &self.tys.funcs.items[id];
    for (self.variables.items[self.variables.items.len - func.args.len ..]) |variable|
        self.freeValue(variable.value);
    self.variables.items.len -= func.args.len;

    inline for (std.meta.fields(Snapshot)[1..]) |field| {
        const start = @field(self.cx.snap, field.name);
        for (@field(self.output, field.name).items[start..]) |*reloc|
            reloc.offset += @as(u32, @intCast(self.cx.snap.code));
    }

    if (entry) try self.emit(.tx, .{}) else {
        self.cx.regs.checkLeaks();
        const poped_regs_size = self.cx.regs.free_count * @as(u16, 8);
        const stack_size = 0;

        self.writeLocalReloc(u64, 3, 0 -% @as(u64, poped_regs_size + stack_size));
        self.writeLocalReloc(u64, 3 + 8 + 3, stack_size); // for now
        self.writeLocalReloc(u16, 3 + 8 + 3 + 8, poped_regs_size);

        const ret_offset = self.localOffset();
        for (self.ret_relocs.items) |offset| {
            self.writeLocalReloc(i32, @intCast(offset + 1), ret_offset - offset);
        }
        self.ret_relocs.items.len = 0;

        try self.emit(.ld, .{ Regs.ret_addr, Regs.stack_ptr, stack_size, poped_regs_size });
        try self.emit(.addi64, .{ Regs.stack_ptr, Regs.stack_ptr, poped_regs_size });
        try self.emit(.jala, .{ Regs.zero, Regs.ret_addr, 0 });

        func.base = @intCast(self.cx.snap.code);
        func.size = @intCast(self.output.code.items.len - func.base);
    }
}

fn emit(self: *Codegen, comptime op: isa.Op, args: anytype) !void {
    if (op == .cp and args[0] == args[1]) return;
    try self.output.code.appendSlice(self.gpa, &isa.pack(op, args));
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
        .Void, .Comment => return .{},
        .Block => |block| {
            for (ast.exprs.view(block.stmts)) |stmt| {
                self.freeValue(try self.generateExpr(file, .{}, stmt));
            }
            return .{};
        },
        .If => |i| {
            const const_ctx = Ctx{ .ty = buty(.bool) };
            var cond_op_size: u8 = 0;
            var cond: Value = undefined;
            {
                self.cx.cond_op_size = &cond_op_size;
                defer self.cx.cond_op_size = null;
                cond = try self.generateExpr(file, const_ctx, i.cond);
            }

            const cond_jump_offset = self.localOffset() - cond_op_size;
            if (cond_op_size == 0) {
                try self.emit(.jeq, .{ cond.loc.reg, 0, 0 });
                self.freeValue(cond);
            }

            const then_value = try self.handleReturn(self.generateExpr(file, .{}, i.body));
            if (then_value) |v| self.freeValue(v);
            var skip_then_dest = self.localOffset();

            var else_value: ?Value = null;
            if (i.else_.tag() != .Void) {
                const else_jump_offset = self.localOffset();
                if (then_value != null) {
                    try self.emit(.jmp, .{0});
                    skip_then_dest += isa.instrSize(.jmp);
                }

                else_value = try self.handleReturn(self.generateExpr(file, .{}, i.else_));
                if (else_value) |v| self.freeValue(v);

                if (then_value != null) {
                    const skip_else_dest = self.localOffset();
                    self.writeLocalReloc(i32, @intCast(else_jump_offset + 1), skip_else_dest - else_jump_offset);
                }
            }

            self.writeLocalReloc(i16, @intCast(cond_jump_offset + 3), skip_then_dest - cond_jump_offset);

            if (then_value == null and else_value == null) return error.Return;

            unreachable;
        },
        .Return => |ret| {
            // TODO: dettect functon calls in the expression to avoid this
            const retCtx = Ctx{
                .ty = self.cx.ret,
                .loc = .{ .reg = self.tryAllocZst(self.cx.ret) orelse
                    self.cx.regs.alloc_ret() orelse
                    self.cx.regs.alloc() },
            };
            const value = try self.generateExpr(file, retCtx, ret.value);
            std.debug.assert(!value.loc.flags.is_derefed);
            if (value.loc.reg != Regs.zero) try self.emit(.cp, .{ 1, value.loc.reg });
            self.freeValue(value);
            return error.Return;
        },
        .Call => |call| {
            const todo = "TODO: handle the complex function expression";
            const called = ast.exprs.getTyped(.Ident, call.called) orelse
                self.report(file, call.called, todo, .{});
            const func_id = try self.findOrDeclare(called.pos, file, called.id);
            std.debug.assert(func_id.tag() == .func);
            const func = self.tys.funcs.items[func_id.index];

            for (ast.exprs.view(call.args), 0..) |arg, i| {
                const arg_ty = func.args.view(self.tys.allocated.items)[i];
                const arg_ctx = Ctx{ .ty = arg_ty, .loc = .{ .reg = @intCast(i + 2), .flags = .{ .is_borrowed = true } } };
                try self.value_buf.append(self.gpa, try self.generateExpr(file, arg_ctx, arg));
            }
            const base = self.value_buf.items.len - ast.exprs.view(call.args).len;
            for (self.value_buf.items[base..]) |value| self.freeValue(value);
            self.value_buf.items.len = base;

            const ret = self.tryAllocZst(func.ret) orelse self.cx.regs.alloc_ret();
            var ret_temp: Regs.Id = Regs.zero;
            if (ret == null and ctx.loc == null) {
                ret_temp = self.cx.regs.alloc();
                try self.emit(.cp, .{ ret_temp, Regs.ret });
            }

            try self.addReloc("func", func_id.index);
            try self.emit(.jal, .{ Regs.ret_addr, Regs.zero, 0 });

            if (ctx.loc) |loc| {
                std.debug.assert(!loc.flags.is_derefed);
                try self.emit(.cp, .{ loc.reg, Regs.ret });
                return .{ .ty = func.ret, .loc = loc };
            }

            if (ret) |r| {
                return .{ .ty = func.ret, .loc = .{ .reg = r } };
            }

            try self.emit(.swa, .{ ret_temp, Regs.ret });
            return .{ .ty = func.ret, .loc = .{ .reg = ret_temp } };
        },
        .Ident => |i| {
            const msg = "Could not find variable: {s}";
            const variable = for (self.variables.items) |*v| {
                if (std.meta.eql(v.name, i.id)) break v;
            } else self.report(file, i.pos, msg, .{i.id.view(ast.source)});

            if (ctx.loc) |loc| {
                std.debug.assert(!loc.flags.is_derefed);
                try self.emit(.cp, .{ loc.reg, variable.value.loc.reg });
                return .{ .ty = variable.value.ty, .loc = loc };
            }

            return variable.value.borrow();
        },
        .Integer => |i| {
            const int_token = Lexer.peek(ast.source, i.index);
            const int_value = std.fmt.parseInt(u64, int_token.view(ast.source), 10) catch |e| {
                self.report(file, i, "Could not parse integer: {any}", .{e});
            };
            const loc = ctx.loc orelse Loc{ .reg = self.cx.regs.alloc() };
            try self.emit(.li64, .{ loc.reg, int_value });
            return .{ .ty = ctx.ty orelse buty(.int), .loc = loc };
        },
        .BinOp => |b| switch (b.op) {
            inline .@"+", .@"-", .@"*" => |op| {
                const dst = ctx.loc orelse Loc{ .reg = self.cx.regs.alloc() };
                const lhs = try self.generateExpr(file, .{ .ty = ctx.ty, .loc = dst }, b.lhs);
                const rhs = try self.generateExpr(file, .{ .ty = lhs.ty }, b.rhs);
                defer self.freeValue(rhs);
                const instr = switch (op) {
                    .@"+" => .add64,
                    .@"-" => .sub64,
                    .@"*" => .mul64,
                    else => |v| @compileError("unhandled binop: " ++ @tagName(v)),
                };
                try self.emit(instr, .{ dst.reg, dst.reg, rhs.loc.reg });
                return lhs;
            },
            .@"/" => {
                const dst = ctx.loc orelse Loc{ .reg = self.cx.regs.alloc() };
                const lhs = try self.generateExpr(file, .{ .ty = ctx.ty, .loc = dst }, b.lhs);
                const rhs = try self.generateExpr(file, .{ .ty = lhs.ty }, b.rhs);
                defer self.freeValue(rhs);
                try self.emit(.diru64, .{ dst.reg, 0, dst.reg, rhs.loc.reg });
                return lhs;
            },
            inline .@"<=" => |op| {
                if (self.cx.cond_op_size) |op_size| {
                    self.cx.cond_op_size = null;
                    const instr = switch (op) {
                        .@"<=" => .jgtu,
                        .@"<" => .jgeu,
                        else => @compileError("wat"),
                    };
                    op_size.* = @intCast(isa.instrSize(instr));

                    const lhs = try self.generateExpr(file, .{}, b.lhs);
                    defer self.freeValue(lhs);
                    const rhs = try self.generateExpr(file, .{ .ty = lhs.ty }, b.rhs);
                    defer self.freeValue(rhs);

                    try self.emit(instr, .{ lhs.loc.reg, rhs.loc.reg, 0 });

                    return .{};
                } else {
                    const dst = ctx.loc orelse Loc{ .reg = self.cx.regs.alloc() };
                    const lhs = try self.generateExpr(file, .{ .loc = dst }, b.lhs);
                    std.debug.assert(!lhs.loc.flags.is_derefed);
                    const rhs = try self.generateExpr(file, .{ .ty = lhs.ty }, b.rhs);
                    defer self.freeValue(rhs);

                    const against = switch (op) {
                        .@"<=" => 1,
                        .@"<" => Vm.toUnsigned(64, -1),
                        else => @compileError("wat"),
                    };
                    try self.emit(.cmpu, .{ dst.reg, dst.reg, rhs.loc.reg });
                    try self.emit(.cmpui, .{ dst.reg, dst.reg, against });
                    switch (op) {
                        .@"<" => try self.emit(.not, .{ dst.reg, dst.reg }),
                        else => {},
                    }
                    return .{ .ty = buty(.bool), .loc = dst };
                }
            },
            else => |v| std.debug.panic("unhandled binop: {s}", .{@tagName(v)}),
        },
        else => |v| std.debug.panic("unhandled expr: {any}", .{v}),
    }
}

fn handleReturn(self: *Codegen, value: Error!Value) Error!?Value {
    return value catch |e| switch (e) {
        error.Return => {
            try self.ret_relocs.append(self.gpa, self.localOffset());
            try self.emit(.jmp, .{0});
            return null;
        },
        error.OutOfMemory, error.TooLongTuple => return e,
    };
}

fn tryAllocZst(self: *Codegen, ty: ?Ty) ?Regs.Id {
    if (self.sizeOf(ty orelse return null) == 0) return Regs.zero;
    return null;
}

fn sizeOf(self: *Codegen, ty: Ty) usize {
    _ = self;
    return switch (ty.tag()) {
        .builtin => switch (@as(Lexer.Lexeme, @enumFromInt(ty.index))) {
            .void => 0,
            .int => @sizeOf(u64),
            else => std.debug.panic("unhandled builtin type: {s}", .{@tagName(ty.tag())}),
        },
        else => |v| std.debug.panic("unhandled type: {s}", .{@tagName(v)}),
    };
}

fn localOffset(self: *Codegen) i16 {
    return @intCast(self.output.code.items.len - self.cx.snap.code);
}

fn addReloc(self: *Codegen, comptime kind: []const u8, id: u32) !void {
    const offset = self.localOffset();
    try @field(self.output, kind ++ "s").append(self.gpa, .{
        .to = id,
        .offset = @intCast(offset),
    });
}

fn freeValue(self: *Codegen, value: Value) void {
    self.freeLoc(value.loc);
}

fn freeLoc(self: *Codegen, loc: Loc) void {
    if (loc.flags.is_borrowed) return;
    if (loc.reg != 0) self.cx.regs.free(loc.reg);
}

fn buty(ty: Lexer.Lexeme) Ty {
    return Ty.init(.builtin, @intFromEnum(ty));
}

fn snapshot(self: *Codegen) Snapshot {
    var snap: Snapshot = undefined;
    inline for (std.meta.fields(Snapshot)) |field|
        @field(snap, field.name) = @field(self.output, field.name).items.len;
    return snap;
}

fn findOrDeclare(self: *Codegen, pos: Ast.Pos, file: File, query: anytype) !Ty {
    const ast = self.files[file];

    const decl, const ident = for (ast.exprs.view(ast.items)) |id| {
        const expr = ast.exprs.getTyped(.BinOp, id) orelse continue;
        std.debug.assert(expr.op == .@":=");
        const name = ast.exprs.getTyped(.Ident, expr.lhs).?;

        if (!switch (@TypeOf(query)) {
            Ast.Ident => std.meta.eql(query, name.id),
            else => std.mem.eql(u8, query, name.id.view(ast.source)),
        }) continue;

        break .{ expr.rhs, name.id };
    } else self.report(file, pos, "Could not find declaration for {s}", .{
        switch (@TypeOf(query)) {
            Ast.Ident => query.view(ast.source),
            else => query,
        },
    });

    const sym = Symbol{ .ns = Namespace.init(.file, file), .item = @bitCast(ident) };
    if (self.tys.computed.get(sym)) |id| return id;

    return switch (ast.exprs.get(decl)) {
        .Fn => |f| b: {
            const func = Func{
                .file = file,
                .decl = decl,
                .args = try self.makeTuple(file, f.args),
                .ret = try self.resolveTy(file, f.ret),
            };
            const id = Ty.init(.func, self.tys.funcs.items.len);
            try self.tys.funcs.append(self.gpa, func);
            if (@TypeOf(query) == Ast.Ident or !std.mem.eql(u8, query, "main"))
                try self.comp_stack.append(self.gpa, id);
            try self.tys.computed.put(self.gpa, sym, id);
            break :b id;
        },
        else => |v| std.debug.panic("unhandled declaration: {any}", .{v}),
    };
}

fn makeTuple(self: *Codegen, file: File, args: Ast.Slice) !Tuple {
    const prev_len = self.tys.allocated.items.len;
    const ast = self.files[file];
    for (ast.exprs.view(args)) |id| {
        const arg = ast.exprs.getTyped(.Arg, id).?;
        try self.tys.allocated.append(self.gpa, try self.resolveTy(file, arg.ty));
    }
    const raw_view: *[]const Ty.Repr = @ptrCast(&self.tys.allocated.items);
    const allocate_types = raw_view.*[prev_len..];
    const index = std.mem.indexOf(Ty.Repr, raw_view.*, allocate_types) orelse prev_len;
    raw_view.len = @max(prev_len, index + allocate_types.len);
    return try Tuple.init(index, allocate_types.len);
}

fn resolveTy(self: *Codegen, file: File, ty: Ast.Id) !Ty {
    const ast = self.files[file];
    return switch (ast.exprs.get(ty)) {
        .Buty => |b| Ty.init(.builtin, @intFromEnum(b.bt)),
        else => |v| std.debug.panic("unhandled type expression: {any}", .{v}),
    };
}

fn report(self: *Codegen, file: u32, origin: anytype, comptime fmt: []const u8, args: anytype) noreturn {
    const pos = switch (@TypeOf(origin)) {
        Ast.Pos => origin,
        Ast.Id => self.files[file].posOf(origin),
        else => @compileError("TODO: handle " ++ @typeName(@TypeOf(origin))),
    };
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

    try output.writer().print("\nDISASM\n", .{});
    try isa.disasm(codegen.output.code.items, &output);

    var exec_log = std.ArrayList(u8).init(gpa);
    defer exec_log.deinit();
    try exec_log.writer().print("EXECUTION\n", .{});
    codegen.ct.vm.fuel = 10000;
    codegen.ct.vm.ip = @intFromPtr(codegen.output.code.items.ptr);
    codegen.ct.vm.log_buffer = &exec_log;
    var ctx = Vm.UnsafeCtx{};
    const not_terminated = std.testing.expectEqual(.tx, codegen.ct.vm.run(&ctx));

    try output.writer().print("\nREGISTERS\n", .{});
    try output.writer().print("$1: {d}\n", .{codegen.ct.vm.regs[1]});

    const old, const new = .{ "tests/" ++ name ++ ".temp.old.txt", name ++ ".temp.new.txt" };

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
            std.debug.print("\n\nEXEC_LOG\n\n{s}\n", .{exec_log.items});
        };

        err catch {
            std.debug.print("\n\nEXEC_LOG\n\n{s}\n", .{exec_log.items});
        };

        try err;
    }

    try not_terminated;
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
        const new_data = try std.fs.cwd().readFileAlloc(gpa, new, 1024 * 1024);
        defer gpa.free(new_data);
        const old_data = try std.fs.cwd().readFileAlloc(gpa, old, 1024 * 1024);
        defer gpa.free(old_data);
        const new_line_count: isize = @intCast(std.mem.count(u8, new_data, "\n"));
        const old_line_count: isize = @intCast(std.mem.count(u8, old_data, "\n"));
        std.debug.print("line count change: {d}\n", .{new_line_count - old_line_count});
        if (stdout.len > 0) std.debug.print("stdout:\n{s}", .{stdout});
        if (stderr.len > 0) std.debug.print("stderr:\n{s}", .{stderr});
    }
    try std.testing.expectEqual(0, exit);
}

test "main-fn" {
    try testSnippet("main-fn");
}

test "arithmetic" {
    try testSnippet("arithmetic");
}

test "functions" {
    try testSnippet("functions");
}

test "comments" {
    try testSnippet("comments");
}

test "if-statements" {
    try testSnippet("if-statements");
}
