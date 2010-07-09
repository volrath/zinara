%macro prologue 0
        push    rbp
        mov     rbp,rsp
        push    rbx
        push    r12
        push    r13
        push    r14
        push    r15
%endmacro
%macro epilogue 0
        pop     r15
        pop     r14
        pop     r13
        pop     r12
        pop     rbx
        leave
        ret
%endmacro

section .rodata
    int_format  db  "%i",0
    float_format  db  "%f",0
    string_format db "%s",0
    write_mode db "w",0

section .text
    global  print_string, print_float, print_char, print_nl, print_int, read_int, open_file, write_file, close_file
    extern printf, scanf, putchar, fopen, fprintf, fclose

    print_string:
        prologue
        ; string address has to be passed in rdi
        mov     rsi,rdi
        mov     rdi,dword string_format
        xor     rax,rax
        call    printf
        epilogue

    print_char:
        prologue
        xor     rax,rax
        call    putchar
        epilogue

    print_nl:
        prologue
        mov     rdi,0xA
        xor     rax,rax
        call    putchar
        epilogue

    print_float:
        prologue
        mov     rsi, rdi
        mov     rdi, dword float_format
        xor     rax,rax
        call    printf
        epilogue

    print_bool:
        prologue
        mov     rsi, rdi
        mov     rdi, dword int_format
        xor     rax,rax
        call    printf
        epilogue

    print_int:
        prologue
        ;integer arg is in rdi
        mov     rsi, rdi
        mov     rdi, dword int_format
        xor     rax,rax
        call    printf
        epilogue

    read_int:
        prologue
        ;rdi is assumed to have the address of the int to be read in
        mov     rsi, rdi
        mov     rdi, dword int_format
        xor     rax,rax
        call    scanf
        epilogue
