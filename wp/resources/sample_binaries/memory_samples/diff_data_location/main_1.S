.global _start

.text

main:
    lea     -0x98(%rsp), %rsp
    movq    $0x2,        (%rsp)
    movq    $0x3,        0x8(%rsp)
    movq    $0x4,        0x10(%rsp)
    movq    $val,        %rax
    mov     (%rax),      %rax
    addq    0x10(%rsp),  %rax
    addq    0x8(%rsp),   %rax
    addq    (%rsp),      %rax
    lea     0x98(%rsp),  %rsp
    ret

_start:
    call    main
    mov     $0x3c,       %rax
    xor     %rdi,        %rdi
    syscall


.data

val:
    .int    1
