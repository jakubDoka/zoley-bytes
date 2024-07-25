const std = @import("std");

test {
    _ = @import("codegen.zig");
}

const debug = @import("builtin").mode == .Debug;

pub fn dbg(value: anytype) @TypeOf(value) {
    std.debug.print("{any}\n", .{value});
    return value;
}

pub const StaticTrace = struct {
    index: if (debug) usize else void,
    frames: if (debug) [frame_limit]usize else void,

    const frame_limit = 10;

    pub fn init(return_addr: usize) StaticTrace {
        if (!debug) return undefined;
        var trace: StaticTrace = undefined;
        var stack_trace = std.builtin.StackTrace{
            .index = undefined,
            .instruction_addresses = &trace.frames,
        };
        std.debug.captureStackTrace(return_addr, &stack_trace);
        trace.index = stack_trace.index;
        return trace;
    }

    pub fn dump(self: *StaticTrace) void {
        if (!debug) return;
        std.debug.dumpStackTrace(.{
            .index = self.index,
            .instruction_addresses = &self.frames,
        });
    }
};

pub fn isErr(value: anytype) bool {
    value catch return true;
    return false;
}

pub inline fn alignTo(offset: anytype, alignment: @TypeOf(offset)) @TypeOf(offset) {
    return (offset + alignment - 1) & ~(alignment - 1);
}

pub fn findReadmeSnippet(comptime name: []const u8) ![]const u8 {
    var readme: []const u8 = @embedFile("README.md");
    const headingPat = "#### " ++ name ++ "\n```hb";
    const index = std.mem.indexOf(u8, readme, headingPat) orelse return error.NoStart;
    readme = readme[index + headingPat.len ..];
    const endPat = "```";
    const code = readme[0 .. std.mem.indexOf(u8, readme, endPat) orelse return error.NoEnd];
    readme = readme[code.len + endPat.len ..];
    return code;
}

pub fn TaggedIndex(comptime R: type, comptime T: type) type {
    return packed struct(R) {
        tag_bits: std.meta.Tag(T),
        index: std.meta.Int(.unsigned, @bitSizeOf(R) - @bitSizeOf(T)),

        pub const Tag = T;
        pub const Repr = R;

        pub fn init(tag_bits: T, index: usize) @This() {
            return .{ .tag_bits = @intFromEnum(tag_bits), .index = @intCast(index) };
        }

        pub fn tag(self: @This()) T {
            return @enumFromInt(self.tag_bits);
        }
    };
}

pub fn toTuple(ty: anytype) TupleOf(@TypeOf(ty)) {
    var res: TupleOf(@TypeOf(ty)) = undefined;
    inline for (std.meta.fields(@TypeOf(ty)), 0..) |field, i| res[i] = @field(ty, field.name);
    return res;
}

pub fn TupleOf(comptime T: type) type {
    const fields = std.meta.fields(T);
    var types: [fields.len]std.builtin.Type.StructField = undefined;
    for (fields, &types, 0..) |field, *ty, i| ty.* = .{
        .name = &[1:0]u8{'0' + i},
        .type = field.type,
        .default_value = null,
        .alignment = @alignOf(field.type),
        .is_comptime = false,
    };
    return @Type(.{ .Struct = .{
        .fields = &types,
        .decls = &.{},
        .is_tuple = true,
        .layout = .auto,
    } });
}
