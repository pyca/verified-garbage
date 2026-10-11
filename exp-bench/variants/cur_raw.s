mov edx, edx
mov ecx, ecx
mov r8d, r8d
movq xmm0, rbx
movq xmm1, rbp
punpcklqdq xmm0, xmm1
movq xmm1, r12
movq xmm2, r13
punpcklqdq xmm1, xmm2
movq xmm2, r14
movq xmm3, r15
punpcklqdq xmm2, xmm3
movdqu xmm3, XMMWORD PTR [rdi+128]
movdqu xmm4, XMMWORD PTR [rdi+144]
movdqu xmm5, XMMWORD PTR [rdi+160]
mov rax, QWORD PTR [rdi+rdx*8+64]
mov QWORD PTR [rdi+128], rax
mov rax, QWORD PTR [rdi+rcx*8+64]
mov QWORD PTR [rdi+136], rax
mov rax, QWORD PTR [rdi+r8*8+64]
mov QWORD PTR [rdi+144], rax
mov rax, QWORD PTR [rdi+48]
sub rax, 8
ror rax, 3
shr rax, 27
mov r9, QWORD PTR [rdi+136]
mov r10, QWORD PTR [rdi+64]
mov r8, QWORD PTR [rdi+80]
add r8, 16
mov rbx, QWORD PTR [rdi+48]
mov r8, QWORD PTR [rdi+80]
mov r9, QWORD PTR [rdi+48]
shl r9, 4
add r9, r8
add r9, 16
mov rax, QWORD PTR [rdi+224]
mov QWORD PTR [r8], rax
mov rax, QWORD PTR [rdi+232]
mov QWORD PTR [r8+8], rax
mov rax, QWORD PTR [rdi+240]
mov QWORD PTR [r9], rax
mov rax, QWORD PTR [rdi+248]
mov QWORD PTR [r9+8], rax
mov eax, 0
mov QWORD PTR [rdi+224], rax
20:
mov rax, QWORD PTR [rdi+224]
shl rax, 3
mov rbp, QWORD PTR [rdi+136]
add rbp, rax
mov r8d, 0
mov r9d, 0
mov r10d, 0
mov r11d, 0
mov r12d, 0
mov r13d, 0
mov r14d, 0
mov r15d, 0
mov rsi, QWORD PTR [rdi+80]
mov rcx, QWORD PTR [rdi+224]
shl rcx, 4
add rcx, rsi
mov QWORD PTR [rcx+16], r8
mov QWORD PTR [rcx+136], r8
mov rdx, QWORD PTR [rbp]
xor eax, eax
mulx rbx, rsi, QWORD PTR [rbp+8]
adcx r8, rsi
adox r8, rax
mulx rax, rsi, QWORD PTR [rbp+16]
adcx r9, rsi
adox r9, rbx
mulx rbx, rsi, QWORD PTR [rbp+24]
adcx r10, rsi
adox r10, rax
mulx rax, rsi, QWORD PTR [rbp+32]
adcx r11, rsi
adox r11, rbx
mulx rbx, rsi, QWORD PTR [rbp+40]
adcx r12, rsi
adox r12, rax
mulx rax, rsi, QWORD PTR [rbp+48]
adcx r13, rsi
adox r13, rbx
mulx rbx, rsi, QWORD PTR [rbp+56]
adcx r14, rsi
adox r14, rax
adcx r15, r15
adox r15, rbx
mov QWORD PTR [rcx+24], r8
mov QWORD PTR [rcx+32], r9
mov r8d, 0
mov rdx, QWORD PTR [rbp+8]
xor eax, eax
mulx rbx, rsi, QWORD PTR [rbp+16]
adcx r10, rsi
adox r10, rax
mulx rax, rsi, QWORD PTR [rbp+24]
adcx r11, rsi
adox r11, rbx
mulx rbx, rsi, QWORD PTR [rbp+32]
adcx r12, rsi
adox r12, rax
mulx rax, rsi, QWORD PTR [rbp+40]
adcx r13, rsi
adox r13, rbx
mulx rbx, rsi, QWORD PTR [rbp+48]
adcx r14, rsi
adox r14, rax
mulx rax, rsi, QWORD PTR [rbp+56]
adcx r15, rsi
adox r15, rbx
adcx r8, r8
adox r8, rax
mov QWORD PTR [rcx+40], r10
mov QWORD PTR [rcx+48], r11
mov r10d, 0
mov rdx, QWORD PTR [rbp+16]
xor eax, eax
mulx rbx, rsi, QWORD PTR [rbp+24]
adcx r12, rsi
adox r12, rax
mulx rax, rsi, QWORD PTR [rbp+32]
adcx r13, rsi
adox r13, rbx
mulx rbx, rsi, QWORD PTR [rbp+40]
adcx r14, rsi
adox r14, rax
mulx rax, rsi, QWORD PTR [rbp+48]
adcx r15, rsi
adox r15, rbx
mulx rbx, rsi, QWORD PTR [rbp+56]
adcx r8, rsi
adox r8, rax
adcx r10, r10
adox r10, rbx
mov QWORD PTR [rcx+56], r12
mov QWORD PTR [rcx+64], r13
mov r12d, 0
mov rdx, QWORD PTR [rbp+24]
xor eax, eax
mulx rbx, rsi, QWORD PTR [rbp+32]
adcx r14, rsi
adox r14, rax
mulx rax, rsi, QWORD PTR [rbp+40]
adcx r15, rsi
adox r15, rbx
mulx rbx, rsi, QWORD PTR [rbp+48]
adcx r8, rsi
adox r8, rax
mulx rax, rsi, QWORD PTR [rbp+56]
adcx r10, rsi
adox r10, rbx
adcx r12, r12
adox r12, rax
mov QWORD PTR [rcx+72], r14
mov QWORD PTR [rcx+80], r15
mov r14d, 0
mov rdx, QWORD PTR [rbp+32]
xor eax, eax
mulx rbx, rsi, QWORD PTR [rbp+40]
adcx r8, rsi
adox r8, rax
mulx rax, rsi, QWORD PTR [rbp+48]
adcx r10, rsi
adox r10, rbx
mulx rbx, rsi, QWORD PTR [rbp+56]
adcx r12, rsi
adox r12, rax
adcx r14, r14
adox r14, rbx
mov QWORD PTR [rcx+88], r8
mov QWORD PTR [rcx+96], r10
mov r8d, 0
mov rdx, QWORD PTR [rbp+40]
xor eax, eax
mulx rbx, rsi, QWORD PTR [rbp+48]
adcx r12, rsi
adox r12, rax
mulx rax, rsi, QWORD PTR [rbp+56]
adcx r14, rsi
adox r14, rbx
adcx r8, r8
adox r8, rax
mov QWORD PTR [rcx+104], r12
mov QWORD PTR [rcx+112], r14
mov r12d, 0
mov rdx, QWORD PTR [rbp+48]
xor eax, eax
mulx rbx, rsi, QWORD PTR [rbp+56]
adcx r8, rsi
adox r8, rax
adcx r12, r12
adox r12, rbx
mov QWORD PTR [rcx+120], r8
mov QWORD PTR [rcx+128], r12
mov r8d, 0
mov rax, QWORD PTR [rdi+224]
add rax, 8
mov QWORD PTR [rdi+224], rax
cmp rax, QWORD PTR [rdi+48]
jne 20b
mov rax, QWORD PTR [rdi+48]
cmp rax, 8
je 21f
mov eax, 0
mov QWORD PTR [rdi+224], rax
23:
mov eax, 0
mov QWORD PTR [rdi+240], rax
mov rax, QWORD PTR [rdi+224]
add rax, 8
mov QWORD PTR [rdi+232], rax
mov rax, QWORD PTR [rdi+224]
shl rax, 3
mov rcx, QWORD PTR [rdi+136]
add rcx, rax
mov rdx, QWORD PTR [rdi+232]
shl rdx, 3
mov rbp, QWORD PTR [rdi+136]
add rbp, rdx
add rax, rdx
mov rsi, QWORD PTR [rdi+80]
add rsi, rax
add rsi, 16
mov r8, QWORD PTR [rsi]
mov r9, QWORD PTR [rsi+8]
mov r10, QWORD PTR [rsi+16]
mov r11, QWORD PTR [rsi+24]
mov r12, QWORD PTR [rsi+32]
mov r13, QWORD PTR [rsi+40]
mov r14, QWORD PTR [rsi+48]
mov r15, QWORD PTR [rsi+56]
24:
mov rdx, QWORD PTR [rcx]
mov rbx, r8
xor eax, eax
mulx r8, rax, QWORD PTR [rbp]
adcx rbx, rax
adox r8, r9
mulx r9, rax, QWORD PTR [rbp+8]
adcx r8, rax
adox r9, r10
mulx r10, rax, QWORD PTR [rbp+16]
adcx r9, rax
adox r10, r11
mulx r11, rax, QWORD PTR [rbp+24]
adcx r10, rax
adox r11, r12
mulx r12, rax, QWORD PTR [rbp+32]
adcx r11, rax
adox r12, r13
mulx r13, rax, QWORD PTR [rbp+40]
adcx r12, rax
adox r13, r14
mulx r14, rax, QWORD PTR [rbp+48]
adcx r13, rax
adox r14, r15
mulx r15, rax, QWORD PTR [rbp+56]
adcx r14, rax
mov eax, 0
adox r15, rax
adcx r15, rax
mov QWORD PTR [rsi], rbx
mov rdx, QWORD PTR [rcx+8]
mov rbx, r8
xor eax, eax
mulx r8, rax, QWORD PTR [rbp]
adcx rbx, rax
adox r8, r9
mulx r9, rax, QWORD PTR [rbp+8]
adcx r8, rax
adox r9, r10
mulx r10, rax, QWORD PTR [rbp+16]
adcx r9, rax
adox r10, r11
mulx r11, rax, QWORD PTR [rbp+24]
adcx r10, rax
adox r11, r12
mulx r12, rax, QWORD PTR [rbp+32]
adcx r11, rax
adox r12, r13
mulx r13, rax, QWORD PTR [rbp+40]
adcx r12, rax
adox r13, r14
mulx r14, rax, QWORD PTR [rbp+48]
adcx r13, rax
adox r14, r15
mulx r15, rax, QWORD PTR [rbp+56]
adcx r14, rax
mov eax, 0
adox r15, rax
adcx r15, rax
mov QWORD PTR [rsi+8], rbx
mov rdx, QWORD PTR [rcx+16]
mov rbx, r8
xor eax, eax
mulx r8, rax, QWORD PTR [rbp]
adcx rbx, rax
adox r8, r9
mulx r9, rax, QWORD PTR [rbp+8]
adcx r8, rax
adox r9, r10
mulx r10, rax, QWORD PTR [rbp+16]
adcx r9, rax
adox r10, r11
mulx r11, rax, QWORD PTR [rbp+24]
adcx r10, rax
adox r11, r12
mulx r12, rax, QWORD PTR [rbp+32]
adcx r11, rax
adox r12, r13
mulx r13, rax, QWORD PTR [rbp+40]
adcx r12, rax
adox r13, r14
mulx r14, rax, QWORD PTR [rbp+48]
adcx r13, rax
adox r14, r15
mulx r15, rax, QWORD PTR [rbp+56]
adcx r14, rax
mov eax, 0
adox r15, rax
adcx r15, rax
mov QWORD PTR [rsi+16], rbx
mov rdx, QWORD PTR [rcx+24]
mov rbx, r8
xor eax, eax
mulx r8, rax, QWORD PTR [rbp]
adcx rbx, rax
adox r8, r9
mulx r9, rax, QWORD PTR [rbp+8]
adcx r8, rax
adox r9, r10
mulx r10, rax, QWORD PTR [rbp+16]
adcx r9, rax
adox r10, r11
mulx r11, rax, QWORD PTR [rbp+24]
adcx r10, rax
adox r11, r12
mulx r12, rax, QWORD PTR [rbp+32]
adcx r11, rax
adox r12, r13
mulx r13, rax, QWORD PTR [rbp+40]
adcx r12, rax
adox r13, r14
mulx r14, rax, QWORD PTR [rbp+48]
adcx r13, rax
adox r14, r15
mulx r15, rax, QWORD PTR [rbp+56]
adcx r14, rax
mov eax, 0
adox r15, rax
adcx r15, rax
mov QWORD PTR [rsi+24], rbx
mov rdx, QWORD PTR [rcx+32]
mov rbx, r8
xor eax, eax
mulx r8, rax, QWORD PTR [rbp]
adcx rbx, rax
adox r8, r9
mulx r9, rax, QWORD PTR [rbp+8]
adcx r8, rax
adox r9, r10
mulx r10, rax, QWORD PTR [rbp+16]
adcx r9, rax
adox r10, r11
mulx r11, rax, QWORD PTR [rbp+24]
adcx r10, rax
adox r11, r12
mulx r12, rax, QWORD PTR [rbp+32]
adcx r11, rax
adox r12, r13
mulx r13, rax, QWORD PTR [rbp+40]
adcx r12, rax
adox r13, r14
mulx r14, rax, QWORD PTR [rbp+48]
adcx r13, rax
adox r14, r15
mulx r15, rax, QWORD PTR [rbp+56]
adcx r14, rax
mov eax, 0
adox r15, rax
adcx r15, rax
mov QWORD PTR [rsi+32], rbx
mov rdx, QWORD PTR [rcx+40]
mov rbx, r8
xor eax, eax
mulx r8, rax, QWORD PTR [rbp]
adcx rbx, rax
adox r8, r9
mulx r9, rax, QWORD PTR [rbp+8]
adcx r8, rax
adox r9, r10
mulx r10, rax, QWORD PTR [rbp+16]
adcx r9, rax
adox r10, r11
mulx r11, rax, QWORD PTR [rbp+24]
adcx r10, rax
adox r11, r12
mulx r12, rax, QWORD PTR [rbp+32]
adcx r11, rax
adox r12, r13
mulx r13, rax, QWORD PTR [rbp+40]
adcx r12, rax
adox r13, r14
mulx r14, rax, QWORD PTR [rbp+48]
adcx r13, rax
adox r14, r15
mulx r15, rax, QWORD PTR [rbp+56]
adcx r14, rax
mov eax, 0
adox r15, rax
adcx r15, rax
mov QWORD PTR [rsi+40], rbx
mov rdx, QWORD PTR [rcx+48]
mov rbx, r8
xor eax, eax
mulx r8, rax, QWORD PTR [rbp]
adcx rbx, rax
adox r8, r9
mulx r9, rax, QWORD PTR [rbp+8]
adcx r8, rax
adox r9, r10
mulx r10, rax, QWORD PTR [rbp+16]
adcx r9, rax
adox r10, r11
mulx r11, rax, QWORD PTR [rbp+24]
adcx r10, rax
adox r11, r12
mulx r12, rax, QWORD PTR [rbp+32]
adcx r11, rax
adox r12, r13
mulx r13, rax, QWORD PTR [rbp+40]
adcx r12, rax
adox r13, r14
mulx r14, rax, QWORD PTR [rbp+48]
adcx r13, rax
adox r14, r15
mulx r15, rax, QWORD PTR [rbp+56]
adcx r14, rax
mov eax, 0
adox r15, rax
adcx r15, rax
mov QWORD PTR [rsi+48], rbx
mov rdx, QWORD PTR [rcx+56]
mov rbx, r8
xor eax, eax
mulx r8, rax, QWORD PTR [rbp]
adcx rbx, rax
adox r8, r9
mulx r9, rax, QWORD PTR [rbp+8]
adcx r8, rax
adox r9, r10
mulx r10, rax, QWORD PTR [rbp+16]
adcx r9, rax
adox r10, r11
mulx r11, rax, QWORD PTR [rbp+24]
adcx r10, rax
adox r11, r12
mulx r12, rax, QWORD PTR [rbp+32]
adcx r11, rax
adox r12, r13
mulx r13, rax, QWORD PTR [rbp+40]
adcx r12, rax
adox r13, r14
mulx r14, rax, QWORD PTR [rbp+48]
adcx r13, rax
adox r14, r15
mulx r15, rax, QWORD PTR [rbp+56]
adcx r14, rax
mov eax, 0
adox r15, rax
adcx r15, rax
mov QWORD PTR [rsi+56], rbx
mov rdx, QWORD PTR [rdi+240]
add rsi, 64
xor eax, eax
adcx r8, QWORD PTR [rsi]
adox r8, rdx
adcx r9, QWORD PTR [rsi+8]
adox r9, rax
adcx r10, QWORD PTR [rsi+16]
adox r10, rax
adcx r11, QWORD PTR [rsi+24]
adox r11, rax
adcx r12, QWORD PTR [rsi+32]
adox r12, rax
adcx r13, QWORD PTR [rsi+40]
adox r13, rax
adcx r14, QWORD PTR [rsi+48]
adox r14, rax
adcx r15, QWORD PTR [rsi+56]
adox r15, rax
mov edx, 0
adcx rax, rdx
adox rax, rdx
mov QWORD PTR [rdi+240], rax
add rbp, 64
mov rax, QWORD PTR [rdi+232]
add rax, 8
mov QWORD PTR [rdi+232], rax
cmp rax, QWORD PTR [rdi+48]
jne 24b
mov QWORD PTR [rsi], r8
mov QWORD PTR [rsi+8], r9
mov QWORD PTR [rsi+16], r10
mov QWORD PTR [rsi+24], r11
mov QWORD PTR [rsi+32], r12
mov QWORD PTR [rsi+40], r13
mov QWORD PTR [rsi+48], r14
mov QWORD PTR [rsi+56], r15
mov rax, QWORD PTR [rdi+224]
add rax, 8
cmp rax, QWORD PTR [rdi+48]
je 25f
mov rbp, QWORD PTR [rdi+240]
add rsi, 64
mov rdx, QWORD PTR [rdi+48]
shl rdx, 4
add rdx, QWORD PTR [rdi+80]
add rdx, 16
mov ecx, 0
27:
mov r8, QWORD PTR [rsi]
mov r9, QWORD PTR [rsi+8]
mov r10, QWORD PTR [rsi+16]
mov r11, QWORD PTR [rsi+24]
mov r12, QWORD PTR [rsi+32]
mov r13, QWORD PTR [rsi+40]
mov r14, QWORD PTR [rsi+48]
mov r15, QWORD PTR [rsi+56]
xor eax, eax
adcx r8, rbp
adcx r9, rcx
adcx r10, rcx
adcx r11, rcx
adcx r12, rcx
adcx r13, rcx
adcx r14, rcx
adcx r15, rcx
mov ebp, 0
adcx rbp, rax
mov QWORD PTR [rsi], r8
mov QWORD PTR [rsi+8], r9
mov QWORD PTR [rsi+16], r10
mov QWORD PTR [rsi+24], r11
mov QWORD PTR [rsi+32], r12
mov QWORD PTR [rsi+40], r13
mov QWORD PTR [rsi+48], r14
mov QWORD PTR [rsi+56], r15
add rsi, 64
cmp rsi, rdx
jne 27b
jmp 26f
25:
26:
mov rax, QWORD PTR [rdi+224]
add rax, 8
mov QWORD PTR [rdi+224], rax
mov rcx, QWORD PTR [rdi+48]
sub rcx, 8
cmp rax, rcx
jne 23b
jmp 22f
21:
22:
mov r8, QWORD PTR [rdi+80]
mov r9, QWORD PTR [rdi+48]
shl r9, 4
add r9, r8
add r9, 16
mov rax, QWORD PTR [r8]
mov QWORD PTR [rdi+224], rax
mov rax, QWORD PTR [r8+8]
mov QWORD PTR [rdi+232], rax
mov rax, QWORD PTR [r9]
mov QWORD PTR [rdi+240], rax
mov rax, QWORD PTR [r9+8]
mov QWORD PTR [rdi+248], rax
mov eax, 0
mov QWORD PTR [r9], rax
mov QWORD PTR [r9+8], rax
mov r9, QWORD PTR [rdi+136]
mov r10, QWORD PTR [rdi+64]
mov r8, QWORD PTR [rdi+80]
add r8, 16
mov rbx, QWORD PTR [rdi+48]
mov r10, rbx
mov rax, r10
and rax, 7
cmp rax, 0
je 28f
mov rax, r10
and rax, 3
cmp rax, 0
je 210f
mov r15d, 0
mov ebp, 0
mov r14d, 0
212:
mov rdx, QWORD PTR [r9+rbp*8]
mov r11, QWORD PTR [r8+r14*8]
mov r12, QWORD PTR [r8+r14*8+8]
xor esi, esi
mov ebx, 0
mulx rax, rcx, rdx
adcx r11, r11
adox r11, rcx
adcx r12, r12
adox r12, rax
adcx rbx, rsi
adox rbx, rsi
adcx r11, r15
adcx r12, rsi
adcx rbx, rsi
mov QWORD PTR [r8+r14*8], r11
mov QWORD PTR [r8+r14*8+8], r12
mov r15, rbx
add rbp, 1
add r14, 2
cmp rbp, r10
jne 212b
jmp 211f
210:
mov r15d, 0
mov ebp, 0
mov r14d, 0
213:
mov rdx, QWORD PTR [r9+rbp*8]
mov r11, QWORD PTR [r8+r14*8]
mov r12, QWORD PTR [r8+r14*8+8]
mulx rax, rcx, rdx
add rcx, r15
adc rax, 0
xor esi, esi
adcx r11, r11
adox r11, rcx
adcx r12, r12
adox r12, rax
mov QWORD PTR [r8+r14*8], r11
mov QWORD PTR [r8+r14*8+8], r12
mov rdx, QWORD PTR [r9+rbp*8+8]
mov r11, QWORD PTR [r8+r14*8+16]
mov r12, QWORD PTR [r8+r14*8+24]
mulx rax, rcx, rdx
adcx r11, r11
adox r11, rcx
adcx r12, r12
adox r12, rax
mov QWORD PTR [r8+r14*8+16], r11
mov QWORD PTR [r8+r14*8+24], r12
mov rdx, QWORD PTR [r9+rbp*8+16]
mov r11, QWORD PTR [r8+r14*8+32]
mov r12, QWORD PTR [r8+r14*8+40]
mulx rax, rcx, rdx
adcx r11, r11
adox r11, rcx
adcx r12, r12
adox r12, rax
mov QWORD PTR [r8+r14*8+32], r11
mov QWORD PTR [r8+r14*8+40], r12
mov rdx, QWORD PTR [r9+rbp*8+24]
mov r11, QWORD PTR [r8+r14*8+48]
mov r12, QWORD PTR [r8+r14*8+56]
mulx rax, rcx, rdx
adcx r11, r11
adox r11, rcx
adcx r12, r12
adox r12, rax
mov QWORD PTR [r8+r14*8+48], r11
mov QWORD PTR [r8+r14*8+56], r12
mov r15d, 0
adcx r15, rsi
adox r15, rsi
add rbp, 4
add r14, 8
cmp rbp, r10
jne 213b
211:
jmp 29f
28:
mov r15d, 0
mov ebp, 0
mov r14d, 0
214:
mov rdx, QWORD PTR [r9+rbp*8]
mov r11, QWORD PTR [r8+r14*8]
mov r12, QWORD PTR [r8+r14*8+8]
mulx rax, rcx, rdx
add rcx, r15
adc rax, 0
xor esi, esi
adcx r11, r11
adox r11, rcx
adcx r12, r12
adox r12, rax
mov QWORD PTR [r8+r14*8], r11
mov QWORD PTR [r8+r14*8+8], r12
mov rdx, QWORD PTR [r9+rbp*8+8]
mov r11, QWORD PTR [r8+r14*8+16]
mov r12, QWORD PTR [r8+r14*8+24]
mulx rax, rcx, rdx
adcx r11, r11
adox r11, rcx
adcx r12, r12
adox r12, rax
mov QWORD PTR [r8+r14*8+16], r11
mov QWORD PTR [r8+r14*8+24], r12
mov rdx, QWORD PTR [r9+rbp*8+16]
mov r11, QWORD PTR [r8+r14*8+32]
mov r12, QWORD PTR [r8+r14*8+40]
mulx rax, rcx, rdx
adcx r11, r11
adox r11, rcx
adcx r12, r12
adox r12, rax
mov QWORD PTR [r8+r14*8+32], r11
mov QWORD PTR [r8+r14*8+40], r12
mov rdx, QWORD PTR [r9+rbp*8+24]
mov r11, QWORD PTR [r8+r14*8+48]
mov r12, QWORD PTR [r8+r14*8+56]
mulx rax, rcx, rdx
adcx r11, r11
adox r11, rcx
adcx r12, r12
adox r12, rax
mov QWORD PTR [r8+r14*8+48], r11
mov QWORD PTR [r8+r14*8+56], r12
mov rdx, QWORD PTR [r9+rbp*8+32]
mov r11, QWORD PTR [r8+r14*8+64]
mov r12, QWORD PTR [r8+r14*8+72]
mulx rax, rcx, rdx
adcx r11, r11
adox r11, rcx
adcx r12, r12
adox r12, rax
mov QWORD PTR [r8+r14*8+64], r11
mov QWORD PTR [r8+r14*8+72], r12
mov rdx, QWORD PTR [r9+rbp*8+40]
mov r11, QWORD PTR [r8+r14*8+80]
mov r12, QWORD PTR [r8+r14*8+88]
mulx rax, rcx, rdx
adcx r11, r11
adox r11, rcx
adcx r12, r12
adox r12, rax
mov QWORD PTR [r8+r14*8+80], r11
mov QWORD PTR [r8+r14*8+88], r12
mov rdx, QWORD PTR [r9+rbp*8+48]
mov r11, QWORD PTR [r8+r14*8+96]
mov r12, QWORD PTR [r8+r14*8+104]
mulx rax, rcx, rdx
adcx r11, r11
adox r11, rcx
adcx r12, r12
adox r12, rax
mov QWORD PTR [r8+r14*8+96], r11
mov QWORD PTR [r8+r14*8+104], r12
mov rdx, QWORD PTR [r9+rbp*8+56]
mov r11, QWORD PTR [r8+r14*8+112]
mov r12, QWORD PTR [r8+r14*8+120]
mulx rax, rcx, rdx
adcx r11, r11
adox r11, rcx
adcx r12, r12
adox r12, rax
mov QWORD PTR [r8+r14*8+112], r11
mov QWORD PTR [r8+r14*8+120], r12
mov r15d, 0
adcx r15, rsi
adox r15, rsi
add rbp, 8
add r14, 16
cmp rbp, r10
jne 214b
29:
movdqu XMMWORD PTR [rdi+128], xmm0
movdqu XMMWORD PTR [rdi+144], xmm1
movdqu XMMWORD PTR [rdi+160], xmm2
mov rbx, QWORD PTR [rdi+128]
mov rbp, QWORD PTR [rdi+136]
mov r12, QWORD PTR [rdi+144]
mov r13, QWORD PTR [rdi+152]
mov r14, QWORD PTR [rdi+160]
mov r15, QWORD PTR [rdi+168]
movdqu XMMWORD PTR [rdi+128], xmm3
movdqu XMMWORD PTR [rdi+144], xmm4
movdqu XMMWORD PTR [rdi+160], xmm5
ret
