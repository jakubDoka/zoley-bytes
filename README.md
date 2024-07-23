# zoley-bytes

#### main-fn
```hb
main := fn(): int {
    return 42
}
```

#### arithmetic
```hb
main := fn(): int {
    return 10 - 20 / 2 + 4 * (2 + 2) - 4 * 4 + 1
}
```

#### functions
```hb
main := fn(): int {
    return add_one(10) + add_two(20)
}

add_two := fn(x: int): int {
    return x + 2
}

add_one := fn(x: int): int {
    return x + 1
}
```

#### comments
```hb
// commant is an item
main := fn(): int {
    // comment is a statement
    foo(/* comment is an exprression /* if you are crazy */ */)
    return 0
}

foo := fn(comment: void): void return /* comment evaluates to void */

// comments might be formatted in the future
```

#### if-statements
```hb
main := fn(): int {
    return fib(10)
}

fib := fn(x: int): int {
    if x <= 2 {
        return 1
    } else {
        return fib(x - 1) + fib(x - 2)
    }
}
```
