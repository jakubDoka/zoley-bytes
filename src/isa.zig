const std = @import("std");

pub const instr_count = spec.len;

const Arg = enum { reg, imm8, imm16, imm32, imm64, rel16, rel32, abs64 };
const InstrSpec = struct { name: [:0]const u8, args: []const Arg, desc: []const u8 };

pub fn ArgType(comptime arg: Arg) type {
    return .{ u8, u8, u16, u32, u64, i16, i32, i64 }[@intFromEnum(arg)];
}

pub const Op = b: {
    var values: [spec.len]std.builtin.Type.EnumField = undefined;
    for (spec, &values, 0..) |instr, *value, i|
        value.* = .{ .name = instr.name, .value = i };
    break :b @Type(.{ .Enum = .{
        .tag_type = u8,
        .fields = &values,
        .decls = &.{},
        .is_exhaustive = true,
    } });
};

pub fn hasImm(op: Op) bool {
    return for (spec[@intFromEnum(op)].args) |arg| {
        if (arg != .reg) return true;
    } else false;
}

pub fn ArgsOf(comptime op: Op) type {
    const args = spec[@intFromEnum(op)].args;
    var fields: [args.len]std.builtin.Type.StructField = undefined;
    for (args, &fields, 0..) |arg, *field, i| field.* = .{
        .name = &[_:0]u8{ 'a', 'r', 'g', '0' + i },
        .type = ArgType(arg),
        .default_value = null,
        .alignment = 0,
        .is_comptime = false,
    };
    return @Type(.{ .Struct = .{
        .fields = &fields,
        .decls = &.{},
        .is_tuple = false,
        .layout = .@"extern",
    } });
}

pub fn instrSize(comptime op: Op) comptime_int {
    const args = spec[@intFromEnum(op)].args;
    var size = 1;
    for (args) |arg| size += @sizeOf(ArgType(arg));
    return size;
}

pub fn pack(comptime op: Op, args: anytype) [instrSize(op)]u8 {
    var out: [instrSize(op)]u8 = undefined;
    out[0] = @intFromEnum(op);
    comptime var i: usize = 1;
    inline for (std.meta.fields(ArgsOf(op)), 0..) |name, j| {
        @as(*align(1) name.type, @ptrCast(&out[i])).* = @truncate(args[j]);
        i += @sizeOf(name.type);
    }
    return out;
}

pub fn packMany(comptime instrs: anytype) []const u8 {
    comptime var cursor = 0;
    inline for (instrs) |instr| cursor += instrSize(instr[0]);

    comptime var out: [cursor]u8 = undefined;
    cursor = 0;
    inline for (instrs) |instr| {
        const op: Op = instr[0];
        out[cursor] = @intFromEnum(op);
        cursor += 1;
        inline for (std.meta.fields(ArgsOf(op)), 1..) |name, i| {
            @as(*align(1) name.type, @ptrCast(&out[cursor])).* = @truncate(instr[i]);
            cursor += @sizeOf(name.type);
        }
    }

    const outa = out;
    return &outa;
}

fn ni(name: [:0]const u8, args: anytype, desc: []const u8) InstrSpec {
    return .{ .name = name, .args = &args, .desc = desc };
}

fn nsi(name: [:0]const u8, args: anytype, attach_imm: bool, desc: []const u8) [4]InstrSpec {
    var ret: [4]InstrSpec = undefined;
    const names = .{ "8", "16", "32", "64" };
    for (&ret, names, 1..) |*r, nm, i|
        r.* = ni(
            name ++ nm,
            if (attach_imm) args ++ .{@as(Arg, @enumFromInt(i))} else args,
            desc,
        );
    return ret;
}

fn nfsi(name: [:0]const u8, args: anytype, attach_imm: bool, desc: []const u8) [2]InstrSpec {
    return nsi(name, args, attach_imm, desc)[2..].*;
}

const breg = .{ .reg, .reg, .reg };
const bregm = .{ .reg, .reg, .imm64 };

fn bdesc(op: []const u8) []const u8 {
    return std.fmt.comptimePrint("$0 = $1 {s} $2", .{op});
}

fn bdescm(op: []const u8) []const u8 {
    return std.fmt.comptimePrint("$0 = $1 {s} #2", .{op});
}

fn nsiop(name: [:0]const u8, op: []const u8) [4]InstrSpec {
    return nsi(name, breg, false, bdesc(op));
}

fn nsimop(name: [:0]const u8, op: []const u8) [4]InstrSpec {
    return nsi(name, breg, true, bdescm(op));
}

fn nfsiop(name: [:0]const u8, op: []const u8) [2]InstrSpec {
    return nfsi(name, breg, false, bdesc(op ++ "(floating point)"));
}

const cmp_mapping = " < => -1 : = => 0 : > => 1";

const spec = .{
    ni("un", .{}, "unreachable code reached"),
    ni("tx", .{}, "gracefully end execution"),
    ni("nop", .{}, "no operation"),
} ++
    nsiop("add", "+") ++
    nsiop("sub", "-") ++
    nsiop("mul", "*") ++ .{
    ni("and", breg, bdesc("&")),
    ni("or", breg, bdesc("|")),
    ni("xor", breg, bdesc("^")),
} ++
    nsiop("slu", "<<") ++
    nsiop("sru", ">>") ++
    nsiop("srs", ">> (signed)") ++ .{
    ni("cmpu", breg, "unsigned coimparison" ++ cmp_mapping),
    ni("cmps", breg, "signed coimparison" ++ cmp_mapping),
} ++
    nsi("diru", .{ .reg, .reg, .reg, .reg }, false, "$0 / $1 = $2, $3 % $1 = $4") ++
    nsi("dirs", .{ .reg, .reg, .reg, .reg }, false, "(signed) $0 / $1 = $2, $3 % $1 = $4") ++ .{
    ni("neg", .{ .reg, .reg }, "$0 = -$1"),
    ni("not", .{ .reg, .reg }, "$0 = !$1"),
    ni("sxt8", .{ .reg, .reg }, "$0 = (signextend) $1"),
    ni("sxt16", .{ .reg, .reg }, "$0 = (signextend) $1"),
    ni("sxt32", .{ .reg, .reg }, "$0 = (signextend) $1"),
} ++
    nsimop("addi", "+") ++
    nsimop("muli", "-") ++ .{
    ni("andi", bregm, bdesc("&")),
    ni("ori", bregm, bdesc("|")),
    ni("xori", bregm, bdesc("^")),
} ++
    nsimop("slui", "<<") ++
    nsimop("srui", ">>") ++
    nsimop("srsi", ">> (signed)") ++ .{
    ni("cmpui", bregm, "unsigned coimparison" ++ cmp_mapping),
    ni("cmpsi", bregm, "signed coimparison" ++ cmp_mapping),
    ni("cp", .{ .reg, .reg }, "$0 = $1"),
    ni("swa", .{ .reg, .reg }, "$0 = $1"),
} ++
    nsi("li", .{.reg}, true, "$0 = #1") ++ .{
    ni("lra", .{ .reg, .reg, .imm32 }, "$0 = ip + $1 + #2"),
    ni("ld", .{ .reg, .reg, .abs64, .imm16 }, "$0[#3] = ($1 + #2)[#3]"),
    ni("st", .{ .reg, .reg, .abs64, .imm16 }, "($1 + #2)[#3] = $0[#3]"),
    ni("ldr", .{ .reg, .reg, .rel32, .imm16 }, "$0[#3] = (pc + $1 + #2)[#3]"),
    ni("str", .{ .reg, .reg, .rel32, .imm16 }, "(pc + $1 + #2)[#3] = $0[#3]"),
    ni("bmc", .{ .reg, .reg, .imm16 }, "$0[#2] = $1[#2]"),
    ni("brm", .{ .reg, .reg, .imm16 }, "$0 = $1[#2]"),
    ni("jmp", .{.rel32}, "pc += #1"),
    ni("jal", .{ .reg, .reg, .rel32 }, "pc += #1"),
    ni("jala", .{ .reg, .reg, .abs64 }, "pc += #1"),
    ni("jltu", .{ .reg, .reg, .rel16 }, "Branch on lesser-than (unsigned)"),
    ni("jgtu", .{ .reg, .reg, .rel16 }, "Branch on greater-than (unsigned)"),
    ni("jlts", .{ .reg, .reg, .rel16 }, "Branch on lesser-than (signed)"),
    ni("jgts", .{ .reg, .reg, .rel16 }, "Branch on greater-than (signed)"),
    ni("eca", .{}, "interrupt"),
    ni("ebp", .{}, "breakpoint"),
} ++
    nfsiop("fadd", "+") ++
    nfsiop("fsub", "-") ++
    nfsiop("fmul", "*") ++
    nfsiop("fdiv", "/") ++
    nfsi("fma", .{ .reg, .reg, .reg, .reg }, false, "$0 = $1 * $2 + $3") ++
    nfsi("finv", .{ .reg, .reg }, false, "$0 = 1.0 / $1") ++
    nfsiop("fcmplt", "<") ++
    nfsiop("fcmpgt", ">") ++
    nfsi("itf", .{ .reg, .reg }, false, "$0 = (F<width>)$1") ++
    nfsi("fti", .{ .reg, .reg }, false, "$0 = (I<width>)$1") ++ .{
    ni("fc32t64", .{ .reg, .reg }, "$0 = (F64)$1"),
    ni("fc64t32", .{ .reg, .reg }, "$0 = (F32)$1"),
    ni("lra16", .{ .reg, .reg, .imm16 }, "$0 = ip + $1 + #2"),
    ni("ldr16", .{ .reg, .reg, .rel16, .imm16 }, "$0[#3] = (pc + $1 + #2)[#3]"),
    ni("str16", .{ .reg, .reg, .rel16, .imm16 }, "(pc + $1 + #2)[#3] = $0[#3]"),
    ni("jmp16", .{.rel16}, "pc += #1"),
};
