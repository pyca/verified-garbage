mov edx, edx
mov ecx, ecx
mov r8d, r8d
movq xmm6, rbx
movq xmm7, rbp
movq xmm8, r12
movq xmm9, r13
movq xmm10, r14
movq xmm11, r15
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
je 20f
mov rbx, QWORD PTR [rdi+rdx*8+64]
mov r11, QWORD PTR [rdi+rcx*8+64]
mov r9, QWORD PTR [rdi+r8*8+64]
mov r10, QWORD PTR [rdi+64]
mov r8, QWORD PTR [rdi+80]
mov r12, QWORD PTR [rdi+48]
mov r15, QWORD PTR [rdi+56]
mov rsi, QWORD PTR [rdi+88]
mov eax, 0
mov r14, 0
22:
mov QWORD PTR [r8+r14*8], rax
add r14, 1
cmp r14, r12
jne 22b
mov QWORD PTR [r8+r12*8], rax
mov QWORD PTR [r8+r12*8+8], rax
mov r13, 0
23:
mov rcx, QWORD PTR [r11+r13*8]
mov ebp, 0
mov r14, 0
24:
mov rax, QWORD PTR [r9+r14*8]
mul rcx
add rax, rbp
adc rdx, 0
add rax, QWORD PTR [r8+r14*8]
adc rdx, 0
mov QWORD PTR [r8+r14*8], rax
mov rbp, rdx
add r14, 1
cmp r14, r12
jne 24b
mov rax, QWORD PTR [r8+r12*8]
add rax, rbp
mov QWORD PTR [r8+r12*8], rax
mov rax, QWORD PTR [r8+r12*8+8]
adc rax, 0
mov QWORD PTR [r8+r12*8+8], rax
mov rax, QWORD PTR [r8]
mul r15
mov rcx, rax
mov rax, QWORD PTR [r10]
mul rcx
add rax, QWORD PTR [r8]
adc rdx, 0
mov rbp, rdx
mov r14, 1
25:
mov rax, QWORD PTR [r10+r14*8]
mul rcx
add rax, rbp
adc rdx, 0
add rax, QWORD PTR [r8+r14*8]
adc rdx, 0
mov QWORD PTR [r8+r14*8-8], rax
mov rbp, rdx
add r14, 1
cmp r14, r12
jne 25b
mov rax, QWORD PTR [r8+r12*8]
add rax, rbp
mov QWORD PTR [r8+r12*8-8], rax
mov rax, QWORD PTR [r8+r12*8+8]
adc rax, 0
mov QWORD PTR [r8+r12*8], rax
mov eax, 0
mov QWORD PTR [r8+r12*8+8], rax
add r13, 1
cmp r13, r12
jne 23b
mov ebp, 0
mov r14, 0
26:
add rbp, rbp
mov rax, QWORD PTR [r8+r14*8]
sbb rax, QWORD PTR [r10+r14*8]
mov QWORD PTR [rsi+r14*8], rax
sbb rbp, rbp
add r14, 1
cmp r14, r12
jne 26b
mov rax, QWORD PTR [r8+r12*8]
add rbp, rbp
sbb rax, 0
sbb rbp, rbp
mov r14, 0
27:
mov rax, QWORD PTR [r8+r14*8]
mov rdx, QWORD PTR [rsi+r14*8]
xor rax, rdx
and rax, rbp
xor rax, rdx
mov QWORD PTR [rbx+r14*8], rax
add r14, 1
cmp r14, r12
jne 27b
jmp 21f
20:
cmp rcx, r8
je 28f
mov r9, QWORD PTR [rdi+144]
mov r10, QWORD PTR [rdi+64]
mov r8, QWORD PTR [rdi+80]
add r8, 16
mov rbx, QWORD PTR [rdi+48]
mov eax, 0
mov rcx, rbx
add rcx, rcx
mov r14d, 0
210:
mov QWORD PTR [r8+r14*8], rax
mov QWORD PTR [r8+r14*8+8], rax
mov QWORD PTR [r8+r14*8+16], rax
mov QWORD PTR [r8+r14*8+24], rax
mov QWORD PTR [r8+r14*8+32], rax
mov QWORD PTR [r8+r14*8+40], rax
mov QWORD PTR [r8+r14*8+48], rax
mov QWORD PTR [r8+r14*8+56], rax
add r14, 8
cmp r14, rcx
jne 210b
mov QWORD PTR [r8+r14*8], rax
mov QWORD PTR [r8+r14*8+8], rax
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
211:
mov eax, 0
mov QWORD PTR [rdi+240], rax
mov QWORD PTR [rdi+232], rax
mov rax, QWORD PTR [rdi+224]
shl rax, 3
mov rcx, QWORD PTR [rdi+136]
add rcx, rax
mov rdx, QWORD PTR [rdi+232]
shl rdx, 3
mov rbp, QWORD PTR [rdi+144]
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
212:
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
jne 212b
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
je 213f
mov rbp, QWORD PTR [rdi+240]
add rsi, 64
mov rdx, QWORD PTR [rdi+48]
shl rdx, 4
add rdx, QWORD PTR [rdi+80]
add rdx, 16
mov ecx, 0
215:
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
jne 215b
jmp 214f
213:
214:
mov rax, QWORD PTR [rdi+224]
add rax, 8
mov QWORD PTR [rdi+224], rax
cmp rax, QWORD PTR [rdi+48]
jne 211b
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
jmp 29f
28:
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
216:
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
jne 216b
mov rax, QWORD PTR [rdi+48]
cmp rax, 8
je 217f
mov eax, 0
mov QWORD PTR [rdi+224], rax
219:
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
220:
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
jne 220b
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
je 221f
mov rbp, QWORD PTR [rdi+240]
add rsi, 64
mov rdx, QWORD PTR [rdi+48]
shl rdx, 4
add rdx, QWORD PTR [rdi+80]
add rdx, 16
mov ecx, 0
223:
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
jne 223b
jmp 222f
221:
222:
mov rax, QWORD PTR [rdi+224]
add rax, 8
mov QWORD PTR [rdi+224], rax
mov rcx, QWORD PTR [rdi+48]
sub rcx, 8
cmp rax, rcx
jne 219b
jmp 218f
217:
218:
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
je 224f
mov rax, r10
and rax, 3
cmp rax, 0
je 226f
mov r15d, 0
mov ebp, 0
mov r14d, 0
228:
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
jne 228b
jmp 227f
226:
mov r15d, 0
mov ebp, 0
mov r14d, 0
229:
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
jne 229b
227:
jmp 225f
224:
mov r15d, 0
mov ebp, 0
mov r14d, 0
230:
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
jne 230b
225:
29:
mov rcx, QWORD PTR [rdi+80]
add rcx, 16
mov eax, 0
mov QWORD PTR [rcx-16], rax
231:
mov rsi, rcx
mov rbp, QWORD PTR [rdi+64]
mov r8, QWORD PTR [rsi]
mov r9, QWORD PTR [rsi+8]
mov r10, QWORD PTR [rsi+16]
mov r11, QWORD PTR [rsi+24]
mov r12, QWORD PTR [rsi+32]
mov r13, QWORD PTR [rsi+40]
mov r14, QWORD PTR [rsi+48]
mov r15, QWORD PTR [rsi+56]
mov rdx, r8
mulx rax, rdx, QWORD PTR [rdi+56]
mov QWORD PTR [rcx], rdx
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
mov rdx, r8
mulx rax, rdx, QWORD PTR [rdi+56]
mov QWORD PTR [rcx+8], rdx
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
mov rdx, r8
mulx rax, rdx, QWORD PTR [rdi+56]
mov QWORD PTR [rcx+16], rdx
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
mov rdx, r8
mulx rax, rdx, QWORD PTR [rdi+56]
mov QWORD PTR [rcx+24], rdx
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
mov rdx, r8
mulx rax, rdx, QWORD PTR [rdi+56]
mov QWORD PTR [rcx+32], rdx
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
mov rdx, r8
mulx rax, rdx, QWORD PTR [rdi+56]
mov QWORD PTR [rcx+40], rdx
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
mov rdx, r8
mulx rax, rdx, QWORD PTR [rdi+56]
mov QWORD PTR [rcx+48], rdx
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
mov rdx, r8
mulx rax, rdx, QWORD PTR [rdi+56]
mov QWORD PTR [rcx+56], rdx
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
mov eax, 0
mov QWORD PTR [rcx-8], rax
add rbp, 64
add rsi, 64
mov rax, QWORD PTR [rdi+48]
add rax, rax
add rax, rax
add rax, rax
add rax, QWORD PTR [rdi+64]
cmp rbp, rax
jne 232f
jmp 233f
232:
234:
mov rdx, QWORD PTR [rcx-8]
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
mov QWORD PTR [rcx-8], rax
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
add rbp, 64
add rsi, 64
mov rax, QWORD PTR [rdi+48]
add rax, rax
add rax, rax
add rax, rax
add rax, QWORD PTR [rdi+64]
cmp rbp, rax
jne 234b
233:
mov rdx, QWORD PTR [rcx-8]
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
mov edx, 0
adcx r8, QWORD PTR [rcx-16]
adcx r9, rdx
adcx r10, rdx
adcx r11, rdx
adcx r12, rdx
adcx r13, rdx
adcx r14, rdx
adcx r15, rdx
adcx rax, rdx
mov QWORD PTR [rsi], r8
mov QWORD PTR [rsi+8], r9
mov QWORD PTR [rsi+16], r10
mov QWORD PTR [rsi+24], r11
mov QWORD PTR [rsi+32], r12
mov QWORD PTR [rsi+40], r13
mov QWORD PTR [rsi+48], r14
mov QWORD PTR [rsi+56], r15
mov QWORD PTR [rcx+48], rax
add rcx, 64
cmp rcx, QWORD PTR [rdi+88]
jne 231b
mov r8, rcx
mov rbp, QWORD PTR [rdi+48]
mov r10, QWORD PTR [rcx-16]
mov QWORD PTR [r8+rbp*8], r10
mov eax, 0
mov QWORD PTR [r8+rbp*8+8], rax
mov r10, QWORD PTR [rdi+64]
mov r12, QWORD PTR [rdi+48]
mov r8, QWORD PTR [rdi+88]
mov rsi, QWORD PTR [rdi+80]
mov rbx, QWORD PTR [rdi+128]
mov ebp, 0
mov r14, 0
235:
add rbp, rbp
mov rax, QWORD PTR [r8+r14*8]
sbb rax, QWORD PTR [r10+r14*8]
mov QWORD PTR [rsi+r14*8], rax
mov rax, QWORD PTR [r8+r14*8+8]
sbb rax, QWORD PTR [r10+r14*8+8]
mov QWORD PTR [rsi+r14*8+8], rax
mov rax, QWORD PTR [r8+r14*8+16]
sbb rax, QWORD PTR [r10+r14*8+16]
mov QWORD PTR [rsi+r14*8+16], rax
mov rax, QWORD PTR [r8+r14*8+24]
sbb rax, QWORD PTR [r10+r14*8+24]
mov QWORD PTR [rsi+r14*8+24], rax
mov rax, QWORD PTR [r8+r14*8+32]
sbb rax, QWORD PTR [r10+r14*8+32]
mov QWORD PTR [rsi+r14*8+32], rax
mov rax, QWORD PTR [r8+r14*8+40]
sbb rax, QWORD PTR [r10+r14*8+40]
mov QWORD PTR [rsi+r14*8+40], rax
mov rax, QWORD PTR [r8+r14*8+48]
sbb rax, QWORD PTR [r10+r14*8+48]
mov QWORD PTR [rsi+r14*8+48], rax
mov rax, QWORD PTR [r8+r14*8+56]
sbb rax, QWORD PTR [r10+r14*8+56]
mov QWORD PTR [rsi+r14*8+56], rax
sbb rbp, rbp
add r14, 8
cmp r14, r12
jne 235b
mov rax, QWORD PTR [r8+r12*8]
add rbp, rbp
sbb rax, 0
sbb rbp, rbp
mov r14, 0
236:
add rbp, rbp
mov rax, QWORD PTR [rsi+r14*8]
cmovb rax, QWORD PTR [r8+r14*8]
mov QWORD PTR [rbx+r14*8], rax
mov rax, QWORD PTR [rsi+r14*8+8]
cmovb rax, QWORD PTR [r8+r14*8+8]
mov QWORD PTR [rbx+r14*8+8], rax
mov rax, QWORD PTR [rsi+r14*8+16]
cmovb rax, QWORD PTR [r8+r14*8+16]
mov QWORD PTR [rbx+r14*8+16], rax
mov rax, QWORD PTR [rsi+r14*8+24]
cmovb rax, QWORD PTR [r8+r14*8+24]
mov QWORD PTR [rbx+r14*8+24], rax
mov rax, QWORD PTR [rsi+r14*8+32]
cmovb rax, QWORD PTR [r8+r14*8+32]
mov QWORD PTR [rbx+r14*8+32], rax
mov rax, QWORD PTR [rsi+r14*8+40]
cmovb rax, QWORD PTR [r8+r14*8+40]
mov QWORD PTR [rbx+r14*8+40], rax
mov rax, QWORD PTR [rsi+r14*8+48]
cmovb rax, QWORD PTR [r8+r14*8+48]
mov QWORD PTR [rbx+r14*8+48], rax
mov rax, QWORD PTR [rsi+r14*8+56]
cmovb rax, QWORD PTR [r8+r14*8+56]
mov QWORD PTR [rbx+r14*8+56], rax
sbb rbp, rbp
add r14, 8
cmp r14, r12
jne 236b
21:
movq rbx, xmm6
movq rbp, xmm7
movq r12, xmm8
movq r13, xmm9
movq r14, xmm10
movq r15, xmm11
movdqu XMMWORD PTR [rdi+128], xmm3
movdqu XMMWORD PTR [rdi+144], xmm4
movdqu XMMWORD PTR [rdi+160], xmm5
ret
