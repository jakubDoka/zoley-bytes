source: []const u8,
cursor: u32,

const std = @import("std");

const Lexer = @This();
pub const Pos = u32;

pub const Lexeme = enum(u8) {
    Eof = 0,
    @"{" = '{',
    @"}" = '}',
    @"(" = '(',
    @")" = ')',
    @":" = ':',
    @";" = ';',
    @"," = ',',
    Ident,
    Integer,
    @"fn",
    @"return",
    int,
    void,
    @":=" = ':' + 128,

    pub fn precedence(self: Lexeme) u8 {
        return switch (self) {
            .@":=" => 15,
            else => 255,
        };
    }

    pub fn repr(self: Lexeme) []const u8 {
        return @tagName(self);
    }
};

pub const Token = struct {
    pos: Pos,
    end: u32,
    kind: Lexeme,

    pub fn init(pos: Pos, end: u32, kind: Lexeme) Token {
        return Token{ .pos = pos, .end = end, .kind = kind };
    }

    pub fn view(self: Token, source: []const u8) []const u8 {
        return source[self.pos..self.end];
    }
};

pub fn init(source: []const u8, cursor: u32) Lexer {
    return Lexer{ .source = source, .cursor = cursor };
}

pub fn peek(source: []const u8, cursor: u32) Token {
    var lexer = init(source, cursor);
    return lexer.next();
}

pub fn next(self: *Lexer) Token {
    while (self.cursor < self.source.len) {
        const pos = self.cursor;
        self.cursor += 1;
        const kind: Lexeme = switch (self.source[pos]) {
            0...32 => continue,
            'a'...'z', 'A'...'Z', '_', 128...255 => b: {
                while (self.cursor < self.source.len) switch (self.source[self.cursor]) {
                    'a'...'z', 'A'...'Z', '0'...'9', '_', 128...255 => self.cursor += 1,
                    else => break,
                };
                const ident = self.source[pos..self.cursor];
                inline for (std.meta.fields(Lexeme)) |field| {
                    if (comptime !std.ascii.isLower(field.name[0])) continue;
                    if (std.mem.eql(u8, field.name, ident)) break :b @field(Lexeme, field.name);
                }
                break :b .Ident;
            },
            '0'...'9' => b: {
                while (self.cursor < self.source.len) switch (self.source[self.cursor]) {
                    '0'...'9' => self.cursor += 1,
                    else => break,
                };
                break :b .Integer;
            },
            ':' => |c| @enumFromInt(if (self.advanceIf('=')) c + 128 else c),
            else => |c| @enumFromInt(c),
        };
        return Token.init(pos, self.cursor, kind);
    }

    return Token.init(self.cursor, self.cursor, .Eof);
}

inline fn advanceIf(self: *Lexer, c: u8) bool {
    if (self.source[self.cursor] == c) {
        self.cursor += 1;
        return true;
    }
    return false;
}
