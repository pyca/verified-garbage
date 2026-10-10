push rbx
mov rdx, 0x123456789
mov rcx, rsi
2:
mulx r8, rax, QWORD PTR [rdi]
mulx r9, r10, QWORD PTR [rdi+8]
mulx r11, rbx, QWORD PTR [rdi+16]
mulx r8, rax, QWORD PTR [rdi+24]
mulx r9, r10, QWORD PTR [rdi+32]
mulx r11, rbx, QWORD PTR [rdi+40]
mulx r8, rax, QWORD PTR [rdi+48]
mulx r9, r10, QWORD PTR [rdi+56]
dec rcx
jnz 2b
pop rbx
ret
