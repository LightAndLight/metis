# Calling convention

## Stack frame layout

Note: assumes 64 bit pointer size.

| Offset from `rbp`                                           | Value                 |
| ----------------------------------------------------------- | --------------------- |
| offset_of(stack argument n) + size_of(stack argument n)     | return address        |
| offset_of(stack argument n-1) + size_of(stack argument n-1) | stack argument n      |
| ...                                                         | ...                   |
| offset_of(stack argument 0) + size_of(stack argument 0)     | stack argument 1      |
| 8                                                           | stack argument 0      |
| 0                                                           | caller's base pointer |
| -size_of(stack local 1)                                     | stack local 0         |
| offset_of(stack local 0) - size_of(stack local 1)           | stack local 1         |
| ...                                                         | ...                   |
| offset_of(stack local n-1) - size_of(stack local n)         | stack local n         |

## Input locations

Function inputs are passed in registers where possible. On x86_64, arguments are passed in the
following registers (in order): `rax`, `rbx`, `rcx`, `rdx`, `rsi`, `rdi`, `r8`, `r9`, `r10`,
`r11`, `r12`, `r13`, `r14`, `r15`.

After the registers have been exhausted, the remaining arguments are passed via the stack.

## Output locations

Function outputs are passed in registers where possible, drawing from the same set of registers in
[Input Locations](#input-locations), and in the same order.

After the registers have been exhausted, the remaining outputs are passed via the stack.

When an output must be passed via the stack, the function recieves an extra pointer argument. To
"return" the output, the function stores a value at this pointer.

## Caller obligations

### Pre-call

1. Save call-clobbered registers
1. Push return address
1. Set up inputs
   * Move arguments into correct registers
   * Push arguments to stack when required
1. Push `rbp`
1. Set `rbp` to `rsp`

### Post-return

1. Persist return value when it's in a call-clobbered register
1. Restore call-clobbered registers

## Callee obligations

### Post-call

1. Allocate stack space for locals

### Pre-return

1. Set up outputs
   * Move results into correct registers
   * Store results in output pointers when required
1. Free locals
1. Pop `rbp`
1. Free stack arguments