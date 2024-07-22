exprs: Store,
path: []const u8,
source: []const u8,
items: Slice,

const std = @import("std");
const Lexer = @import("lexer.zig");
const Ast = @This();
const IdRepr = u32;
const Store = EnumStore(Id, Slice, Expr);
pub const Id = EnumId(Kind);
pub const Slice = EnumSlice(Kind);

pub const Ident = packed struct(Ident.Repr) {
    const Repr = u32;
    const Len = u6;

    index: std.meta.Int(.unsigned, @bitSizeOf(Repr) - @bitSizeOf(Len)),
    len: Len,

    pub fn init(token: Lexer.Token) !Ident {
        if (token.end - token.pos > std.math.maxInt(Len)) return error.TooLongIdent;
        return .{ .index = @intCast(token.pos), .len = @intCast(token.end - token.pos) };
    }

    pub fn view(self: Ident, source: []const u8) []const u8 {
        return source[self.index..][0..self.len];
    }
};

pub const Kind = enum {
    Void,
    Ident,
    Buty,
    Fn,
    Return,
    Block,
    BinOp,
    Integer,
};

pub const Expr = union(Kind) {
    Void,
    Ident: struct {
        pos: Pos,
        id: Ident,
    },
    Buty: struct {
        pos: Pos,
        bt: Lexer.Lexeme,
    },
    Fn: struct {
        pos: Pos,
        args: Slice,
        ret: Id,
        body: Id,
    },
    Return: struct {
        pos: Pos,
        value: Id,
    },
    Block: struct {
        pos: Pos,
        stmts: Slice,
    },
    BinOp: struct {
        lhs: Id,
        op: Lexer.Lexeme,
        rhs: Id,
    },
    Integer: Pos,
};

pub const Pos = packed struct(Pos.Repr) {
    const Repr = u32;

    index: std.meta.Int(.unsigned, @bitSizeOf(Repr) - @bitSizeOf(bool)),
    indented: bool = false,

    pub fn init(index: Lexer.Pos) Pos {
        return .{ .index = @intCast(index) };
    }
};

const Parser = struct {
    store: Store = .{},
    cur: Lexer.Token,
    lexer: Lexer,
    list_pos: Pos = undefined,
    no_semi: bool = false,
    arena: std.heap.ArenaAllocator,
    gpa: std.mem.Allocator,

    const Error = error{ TooLongIdent, UnexpectedToken } || std.mem.Allocator.Error;

    fn parse(self: *Parser) !Slice {
        var itemBuf = std.ArrayListUnmanaged(Id){};
        while (self.cur.kind != .Eof) {
            try itemBuf.append(self.arena.allocator(), try self.parseExpr());
        }
        return self.store.allocSlice(self.gpa, itemBuf.items);
    }

    fn parseExpr(self: *Parser) Error!Id {
        return self.parseBinExpr(try self.parseUnit(), 254);
    }

    fn parseBinExpr(self: *Parser, lhs: Id, prevPrec: u8) Error!Id {
        var acum = lhs;
        while (true) {
            const op = self.cur.kind;
            const prec = op.precedence();
            if (prec >= prevPrec) break;

            self.cur = self.lexer.next();
            const rhs = try self.parseExpr();
            acum = try self.store.alloc(
                self.gpa,
                .BinOp,
                .{ .lhs = acum, .op = op, .rhs = rhs },
            );
        }
        return acum;
    }

    fn parseUnit(self: *Parser) Error!Id {
        const token = self.advance();
        self.no_semi = false;
        defer self.no_semi = token.kind == .@"{";
        return try self.store.allocDyn(self.gpa, switch (token.kind) {
            .Ident => .{ .Ident = .{ .pos = Pos.init(token.pos), .id = try Ident.init(token) } },
            .@"fn" => .{ .Fn = .{
                .args = try self.parseList(.@"(", .@",", .@")", parseArg),
                .pos = self.list_pos,
                .ret = b: {
                    _ = try self.expectAdvance(.@":");
                    break :b try self.parseExpr();
                },
                .body = try self.parseExpr(),
            } },
            .@"{" => .{ .Block = .{
                .pos = Pos.init(token.pos),
                .stmts = b: {
                    var buf = std.ArrayListUnmanaged(Id){};
                    while (!self.tryAdvance(.@"}")) {
                        try buf.append(self.arena.allocator(), try self.parseExpr());
                        if (!self.no_semi) _ = try self.expectAdvance(.@";");
                    }
                    break :b try self.store.allocSlice(self.gpa, buf.items);
                },
            } },
            .int => .{ .Buty = .{ .pos = Pos.init(token.pos), .bt = token.kind } },
            .@"return" => .{ .Return = .{
                .pos = Pos.init(token.pos),
                .value = if (self.cur.kind != .@";")
                    try self.parseExpr()
                else
                    Id.zeroSized(.Void),
            } },
            .Integer => .{ .Integer = Pos.init(token.pos) },
            else => |k| std.debug.panic("{any}", .{k}),
        });
    }

    fn parseList(
        self: *Parser,
        start: ?Lexer.Lexeme,
        sep: ?Lexer.Lexeme,
        end: Lexer.Lexeme,
        comptime parser: fn (*Parser) Error!Id,
    ) Error!Slice {
        self.list_pos = .{ .index = @intCast(self.cur.pos), .indented = true };
        if (start) |s| _ = try self.expectAdvance(s);
        var buf = std.ArrayListUnmanaged(Id){};
        while (!self.tryAdvance(end)) {
            try buf.append(self.arena.allocator(), try parser(self));
            if (self.tryAdvance(end)) break;
            if (sep) |s| _ = try self.expectAdvance(s);
        } else self.list_pos.indented = false;
        return try self.store.allocSlice(self.gpa, buf.items);
    }

    fn parseArg(self: *Parser) Error!Id {
        _ = self;
        unreachable;
    }

    inline fn tryAdvance(self: *Parser, expected: Lexer.Lexeme) bool {
        _ = self.expectAdvance(expected) catch return false;
        return true;
    }

    inline fn expectAdvance(self: *Parser, expected: Lexer.Lexeme) !Lexer.Token {
        if (self.cur.kind != expected) return error.UnexpectedToken;
        return self.advance();
    }

    inline fn advance(self: *Parser) Lexer.Token {
        defer self.cur = self.lexer.next();
        return self.cur;
    }

    fn catchSynErr(expr: anytype) ?@TypeOf(expr) {
        return expr catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => return null,
        };
    }
};

const Fmt = struct {
    buf: *std.ArrayList(u8),
    indent: u32,
    ast: *const Ast,

    const Error = std.mem.Allocator.Error;

    fn fmt(self: *Fmt) Error!void {
        for (self.ast.exprs.view(self.ast.items)) |id| try self.fmtExpr(id);
    }

    fn fmtExpr(self: *Fmt, id: Id) Error!void {
        return self.fmtExprPrec(id, 255);
    }

    fn fmtExprPrec(self: *Fmt, id: Id, prec: u8) Error!void {
        switch (self.ast.exprs.get(id)) {
            .Void => {},
            .Ident => |i| try self.buf.appendSlice(i.id.view(self.ast.source)),
            .Fn => |f| {
                try self.buf.appendSlice("fn");
                try self.displaySlice(f.pos.indented, f.args, .@"(", .@",", .@")");
                try self.buf.appendSlice(": ");
                try self.fmtExpr(f.ret);
                try self.buf.appendSlice(" ");
                try self.fmtExpr(f.body);
            },
            .Buty => |b| try self.buf.appendSlice(b.bt.repr()),
            .Block => |b| {
                try self.displaySlice(true, b.stmts, .@"{", .@";", .@"}");
            },
            .Return => |r| {
                try self.buf.appendSlice("return");
                if (r.value.tag() != .Void) {
                    try self.buf.appendSlice(" ");
                    try self.fmtExpr(r.value);
                }
            },
            .BinOp => |o| {
                if (prec < o.op.precedence()) try self.buf.appendSlice("(");
                try self.fmtExpr(o.lhs);
                // TODO: linebreaks
                try self.buf.appendSlice(" ");
                try self.buf.appendSlice(o.op.repr());
                try self.buf.appendSlice(" ");
                try self.fmtExpr(o.rhs);
                if (prec < o.op.precedence()) try self.buf.appendSlice(")");
            },
            .Integer => |i| {
                const int_token = Lexer.peek(self.ast.source, i.index);
                try self.buf.appendSlice(self.ast.source[int_token.pos..int_token.end]);
            },
        }
    }

    fn displaySlice(
        self: *Fmt,
        indent: bool,
        slice: Slice,
        start: Lexer.Lexeme,
        sep: Lexer.Lexeme,
        end: Lexer.Lexeme,
    ) Error!void {
        try self.buf.appendSlice(start.repr());

        if (indent) {
            self.indent += 1;
            try self.buf.appendSlice("\n");
        }

        for (self.ast.exprs.view(slice)) |id| {
            for (0..self.indent) |_| try self.buf.appendSlice("    ");
            try self.fmtExpr(id);
            try self.buf.appendSlice(sep.repr());
            try self.buf.appendSlice("\n");
        }

        if (indent) {
            self.indent -= 1;
            for (0..self.indent) |_| try self.buf.appendSlice("    ");
        }

        try self.buf.appendSlice(end.repr());
    }
};

pub fn init(path: []const u8, code: []const u8, gpa: std.mem.Allocator) !Ast {
    var lexer = Lexer.init(code, 0);

    var parser = Parser{
        .cur = lexer.next(),
        .lexer = lexer,
        .arena = std.heap.ArenaAllocator.init(gpa),
        .gpa = gpa,
    };
    defer parser.arena.deinit();

    return .{
        .items = try parser.parse(),
        .exprs = parser.store,
        .source = code,
        .path = path,
    };
}

pub fn posOf(self: *const Ast, id: Id) Pos {
    return switch (self.exprs.get(id)) {
        inline else => |v| switch (@TypeOf(v)) {
            void => Pos.init(0),
            Pos => v,
            else => |Vt| if (@hasField(Vt, "pos"))
                v.pos
            else
                self.posOf(@field(v, std.meta.fields(Vt)[0].name)),
        },
    };
}

pub fn deinit(self: *Ast, gpa: std.mem.Allocator) void {
    self.exprs.deinit(gpa);
}

pub fn fmt(self: *const Ast, buf: *std.ArrayList(u8)) !void {
    var ft = Fmt{
        .buf = buf,
        .indent = 0,
        .ast = self,
    };
    try ft.fmt();
}

pub fn lineCol(self: *const Ast, index: isize) struct { usize, usize } {
    var line: usize = 0;
    var last_nline: isize = -1;
    for (self.source, 0..) |c, i| if (c == '\n') {
        line += 1;
        last_nline = @intCast(i);
    };
    return .{ line + 1, @intCast(index - last_nline) };
}

fn EnumId(comptime Tag: type) type {
    return packed struct(IdRepr) {
        taga: std.meta.Tag(Tag),
        index: std.meta.Int(.unsigned, @bitSizeOf(IdRepr) - @bitSizeOf(Tag)),

        pub fn zeroSized(taga: Tag) @This() {
            return .{ .taga = @intFromEnum(taga), .index = 0 };
        }

        pub fn tag(self: @This()) Tag {
            return @enumFromInt(self.taga);
        }
    };
}

fn EnumSlice(comptime T: type) type {
    return struct {
        comptime {
            _ = T;
        }

        start: u32,
        end: u32,
    };
}

fn EnumStore(comptime SelfId: type, comptime SelfSlice: type, comptime T: type) type {
    return struct {
        const Self = @This();
        const payload_align = b: {
            var max_align: u29 = 1;
            for (std.meta.fields(T)) |field| {
                max_align = @max(max_align, @alignOf(field.type));
            }
            break :b max_align;
        };

        store: std.ArrayListAlignedUnmanaged(u8, payload_align) = .{},

        pub fn allocDyn(self: *Self, gpa: std.mem.Allocator, value: T) !SelfId {
            return switch (value) {
                inline else => |v, t| try self.alloc(gpa, t, v),
            };
        }

        pub fn alloc(
            self: *Self,
            gpa: std.mem.Allocator,
            comptime tag: std.meta.Tag(T),
            value: std.meta.TagPayload(T, tag),
        ) !SelfId {
            const Value = @TypeOf(value);
            (try self.allocLow(gpa, Value, 1))[0] = value;
            return SelfId{
                .taga = @intFromEnum(tag),
                .index = @intCast(self.store.items.len - @sizeOf(Value)),
            };
        }

        pub fn allocSlice(
            self: *Self,
            gpa: std.mem.Allocator,
            slice: []const SelfId,
        ) !SelfSlice {
            const Ider = SelfId;
            std.mem.copyForwards(Ider, try self.allocLow(gpa, Ider, slice.len), slice);
            return SelfSlice{
                .start = @intCast(self.store.items.len - @sizeOf(Ider) * slice.len),
                .end = @intCast(self.store.items.len),
            };
        }

        fn allocLow(self: *Self, gpa: std.mem.Allocator, comptime E: type, count: usize) ![]E {
            const alignment: usize = @alignOf(E);
            const padded_len = (self.store.items.len + alignment - 1) & ~(alignment - 1);
            const required_space = padded_len + @sizeOf(E) * count;
            try self.store.resize(gpa, required_space);
            const dest: [*]E = @ptrCast(@alignCast(self.store.items.ptr[padded_len..]));
            return dest[0..count];
        }

        pub fn get(self: *const Self, id: SelfId) T {
            switch (@as(std.meta.Tag(T), @enumFromInt(id.taga))) {
                inline else => |t| {
                    const Value = std.meta.TagPayload(T, t);
                    const loc: *Value = @ptrCast(@alignCast(&self.store.items[id.index]));
                    return @unionInit(T, @tagName(t), loc.*);
                },
            }
        }

        pub fn getTyped(
            self: *const Self,
            comptime tag: std.meta.Tag(T),
            id: SelfId,
        ) ?std.meta.TagPayload(T, tag) {
            if (tag != id.tag()) return null;
            const Value = std.meta.TagPayload(T, tag);
            const loc: *Value = @ptrCast(@alignCast(&self.store.items[id.index]));
            return loc.*;
        }

        pub fn view(self: *const Self, slice: SelfSlice) []SelfId {
            const slc = self.store.items[slice.start..slice.end];
            const len = slc.len / @sizeOf(SelfId);
            const ptr: [*]SelfId = @ptrCast(@alignCast(slc.ptr));
            return ptr[0..len];
        }

        pub fn deinit(self: *Self, gpa: std.mem.Allocator) void {
            self.store.deinit(gpa);
        }
    };
}
