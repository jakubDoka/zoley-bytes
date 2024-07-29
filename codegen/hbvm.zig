gpa: std.mem.Allocator,
cg: *Codegen,
out: *std.ArrayList(u8),

next_block: Codegen.Id = undefined,
regs: Regs = undefined,
computed: std.AutoHashMapUnmanaged(Codegen.Id, Loc) = .{},
args: std.ArrayListUnmanaged(Loc) = .{},
tmp_locs: std.ArrayListUnmanaged(Loc) = .{},
funcs: std.ArrayListUnmanaged(Func) = .{},
relocs: struct {
    funcs: std.ArrayListUnmanaged(FuncReloc) = .{},
} = .{},

const std = @import("std");
const root = @import("../root.zig");
const isa = @import("../isa.zig");
const Codegen = @import("../codegen2.zig");
const codegen = @import("../codegen.zig");
const HbvmCg = @This();

pub const Loc = codegen.Loc;
pub const Regs = codegen.Regs;
pub const Error = error{Goto} || std.mem.Allocator.Error;

const FuncReloc = struct {
    func: u32,
    offset: u32,
};

const Func = struct {
    base: u32,
    reloc_end: u32,
};

pub fn deinit(self: *HbvmCg, gpa: std.mem.Allocator) void {
    self.computed.deinit(gpa);
    self.args.deinit(gpa);
    self.funcs.deinit(gpa);
    self.relocs.funcs.deinit(gpa);
    std.debug.assert(self.tmp_locs.items.len == 0);
    self.tmp_locs.deinit(gpa);
}

pub fn generateFunc(self: *HbvmCg, func_id: usize) !void {
    self.reset();
    const func = &self.cg.ctx.funcs.items[func_id];
    const entry = func_id == 0;
    const base = self.out.items.len;

    try self.emit(.addi64, .{ Regs.stack_ptr, Regs.stack_ptr, 0 });
    if (!entry) try self.emit(.st, .{ Regs.ret_addr, Regs.stack_ptr, 0, 0 });

    if (self.cg.sizeOf(func.ret) > 16) _ = self.regs.allocRet().?;

    try self.args.resize(self.gpa, func.args.len);
    var arg_reg: u8 = 2;
    for (func.args.view(self.cg.ctx.allocated.items), self.args.items) |arg_ty, *arg| {
        arg.* = switch (self.cg.sizeOf(arg_ty)) {
            0 => Loc{},
            1...8 => b: {
                const loc = Loc{ .reg = self.regs.alloc() };
                try self.emit(.cp, .{ loc.reg, arg_reg });
                arg_reg += 1;
                break :b loc;
            },
            9...16 => b: {
                const loc = Loc{
                    .reg = self.regs.alloc(),
                    .sec_reg = self.regs.alloc(),
                };
                try self.emit(.brc, .{ loc.reg, arg_reg, 2 });
                arg_reg += 2;
                break :b loc;
            },
            else => b: {
                const loc = Loc{ .reg = self.regs.alloc() };
                try self.emit(.cp, .{ loc.reg, arg_reg });
                break :b loc.toggled("derefed", true);
            },
        };
    }

    self.next_block = func.entry;
    for (0..10000) |_| {
        _ = self.generate(null, self.next_block) catch |e| switch (e) {
            error.Goto => {
                continue;
            },
            else => return e,
        };
        break;
    } else unreachable;

    for (self.args.items) |arg| self.freeValue(arg);

    self.regs.checkLeaks();
    const stack_size = 0;
    const poped_regs_size = self.regs.free_count * @as(u16, 8) + 8;

    if (entry) {
        self.writeReloc(u64, base + 3, 0 -% @as(u64, stack_size));
        try self.emit(.addi64, .{ Regs.stack_ptr, Regs.stack_ptr, stack_size });
        try self.emit(.tx, .{});
    } else {
        self.writeReloc(u64, base + 3, 0 -% @as(u64, poped_regs_size + stack_size));
        self.writeReloc(u64, base + 3 + 8 + 3, stack_size); // for now
        self.writeReloc(u16, base + 3 + 8 + 3 + 8, poped_regs_size);
        try self.emit(.ld, .{ Regs.ret_addr, Regs.stack_ptr, stack_size, poped_regs_size });
        try self.emit(.addi64, .{ Regs.stack_ptr, Regs.stack_ptr, poped_regs_size });
        try self.emit(.jala, .{ Regs.zero, Regs.ret_addr, 0 });
    }

    try self.funcs.append(self.gpa, .{
        .base = @intCast(base),
        .reloc_end = @intCast(self.relocs.funcs.items.len),
    });
}

pub fn finalize(self: *HbvmCg) void {
    var prev_start: u32 = 0;
    for (self.funcs.items) |func| {
        for (self.relocs.funcs.items[prev_start..func.reloc_end]) |reloc| {
            const dest_offset = self.funcs.items[reloc.func].base;
            self.writeReloc(i32, reloc.offset + 3, @intCast(dest_offset - reloc.offset));
        }
        prev_start = func.reloc_end;
    }
}

fn generate(self: *HbvmCg, dst: ?Loc, id: Codegen.Id) !Loc {
    return switch (self.cg.out.store.get(id)) {
        .Void => .{},
        .Arg => b: {
            const loc = self.args.items[id.index].toggled("borrowed", true);
            if (dst) |d| try self.emit(.cp, .{ d.reg, loc.reg });
            break :b dst orelse loc;
        },
        .Li64 => |i| b: {
            const loc = dst orelse Loc{ .reg = self.regs.alloc() };
            try self.emit(.li64, .{ loc.reg, i });
            break :b loc;
        },
        .Ret => |ret| b: {
            const rdst = Loc{ .reg = 1, .flags = .{ .is_borrowed = true } };
            self.freeValue(try self.generate(rdst, ret));
            break :b .{};
        },
        .Call => |call| {
            if (self.computed.get(id)) |loc| {
                return loc;
            }

            std.debug.assert(call.func.tag() == .func);
            const func = self.cg.ctx.funcs.items[call.func.index];
            var arg_reg: Regs.Id = 2;
            for (
                self.cg.out.store.view(call.args),
                func.args.view(self.cg.ctx.allocated.items),
            ) |arg, arg_ty| {
                const value = switch (self.cg.sizeOf(arg_ty)) {
                    0 => Loc{},
                    8 => b: {
                        const arg_loc = Loc{ .reg = arg_reg, .flags = .{ .is_borrowed = true } };
                        arg_reg += 1;
                        break :b try self.generate(arg_loc, arg);
                    },
                    else => unreachable,
                };
                try self.tmp_locs.append(self.gpa, value);
            }
            const base = self.tmp_locs.items.len - func.args.len;
            for (self.tmp_locs.items[base..]) |value| self.freeValue(value);
            self.tmp_locs.items.len = base;

            switch (self.cg.sizeOf(func.ret)) {
                0 => {
                    try self.relocs.funcs.append(self.gpa, .{
                        .func = call.func.index,
                        .offset = @intCast(self.out.items.len),
                    });
                    try self.emit(.jal, .{ Regs.ret_addr, Regs.zero, 0 });
                },
                8 => {
                    const ret = self.regs.allocRet();
                    var ret_temp: ?Regs.Id = null;
                    if (ret == null) {
                        ret_temp = self.regs.alloc();
                        try self.emit(.cp, .{ ret_temp.?, Regs.ret });
                    }

                    try self.relocs.funcs.append(self.gpa, .{
                        .func = call.func.index,
                        .offset = @intCast(self.out.items.len),
                    });
                    try self.emit(.jal, .{ Regs.ret_addr, Regs.zero, 0 });

                    if (ret_temp) |r| try self.emit(.swa, .{ r, Regs.ret });

                    try self.computed.put(self.gpa, id, .{ .reg = ret orelse ret_temp.? });
                },
                else => unreachable,
            }
            self.next_block = call.goto;
            return error.Goto;
        },
        inline .Add64, .Sub64, .Mul64 => |body, t| b: {
            const lhs = try self.generate(dst, body.lhs);
            const rhs = try self.generate(null, body.rhs);
            defer self.freeValue(rhs);
            const instr = switch (t) {
                .Add64 => .add64,
                .Sub64 => .sub64,
                .Mul64 => .mul64,
                else => @compileError("wat"),
            };
            try self.emit(instr, .{ lhs.reg, lhs.reg, rhs.reg });
            break :b lhs;
        },
        .Div64 => |body| b: {
            const lhs = try self.generate(dst, body.lhs);
            const rhs = try self.generate(null, body.rhs);
            defer self.freeValue(rhs);
            try self.emit(.diru64, .{ lhs.reg, 0, lhs.reg, rhs.reg });
            break :b lhs;
        },
        //else => |v| std.debug.panic("unhandled expr: {any}", .{v}),
    };
}

fn freeValue(self: *HbvmCg, loc: Loc) void {
    if (loc.flags.is_borrowed) return;
    if (loc.reg == Regs.stack_ptr) {
        unreachable;
    } else if (loc.reg != 0) {
        if (loc.sec_reg != 0) self.regs.free(loc.sec_reg);
        self.regs.free(loc.reg);
    }
}

fn writeReloc(self: *HbvmCg, comptime T: type, offset: usize, value: T) void {
    std.debug.assert(std.mem.allEqual(u8, self.out.items[offset..][0..@sizeOf(T)], 0));
    self.out.items[offset..][0..@sizeOf(T)].* = @bitCast(value);
}

fn reset(self: *HbvmCg) void {
    self.computed.clearRetainingCapacity();
    self.regs = Regs.init(Regs.ret_addr + 1, Regs.stack_ptr - 1);
}

fn emit(self: *HbvmCg, comptime op: isa.Op, args: anytype) !void {
    if (op == .cp and args[0] == args[1]) return;
    try self.out.appendSlice(&isa.pack(op, args));
}
