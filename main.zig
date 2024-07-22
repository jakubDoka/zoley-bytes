const std = @import("std");
const isa = @import("isa.zig");
const Vm = @import("vm.zig");
const codegen = @import("codegen.zig");
const root = @import("root.zig");

pub fn main() !void {}

test "simple test" {
    var list = std.ArrayList(i32).init(std.testing.allocator);
    defer list.deinit(); // try commenting this out and see if zig detects the memory leak!
    try list.append(42);
    try std.testing.expectEqual(@as(i32, 42), list.pop());
}
