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
212:
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
mov QWORD PTR [rsi], r8
mov QWORD PTR [rsi+8], r9
mov QWORD PTR [rsi+16], r10
mov QWORD PTR [rsi+24], r11
mov QWORD PTR [rsi+32], r12
mov QWORD PTR [rsi+40], r13
mov QWORD PTR [rsi+48], r14
mov QWORD PTR [rsi+56], r15
mov QWORD PTR [rdi+240], rax
mov rax, QWORD PTR [rdi+232]
add rax, 8
mov QWORD PTR [rdi+232], rax
cmp rax, QWORD PTR [rdi+48]
jne 212b
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
mov eax, 0
mov rcx, rbx
add rcx, rcx
mov r14d, 0
216:
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
jne 216b
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
217:
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
mov rdx, QWORD PTR [rbp]
xor ecx, ecx
mulx rax, rsi, QWORD PTR [rbp+8]
adcx r8, rsi
adox r8, rcx
mulx rbx, rsi, QWORD PTR [rbp+16]
adcx r9, rsi
adox r9, rax
mulx rax, rsi, QWORD PTR [rbp+24]
adcx r10, rsi
adox r10, rbx
mulx rbx, rsi, QWORD PTR [rbp+32]
adcx r11, rsi
adox r11, rax
mulx rax, rsi, QWORD PTR [rbp+40]
adcx r12, rsi
adox r12, rbx
mulx rbx, rsi, QWORD PTR [rbp+48]
adcx r13, rsi
adox r13, rax
mulx rax, rsi, QWORD PTR [rbp+56]
adcx r14, rsi
adox r14, rbx
adcx r15, rcx
adox r15, rax
mov rsi, QWORD PTR [rdi+80]
mov rcx, QWORD PTR [rdi+224]
shl rcx, 4
add rsi, rcx
mov QWORD PTR [rsi+24], r8
mov QWORD PTR [rsi+32], r9
mov r8d, 0
mov rdx, QWORD PTR [rbp+8]
xor ecx, ecx
mulx rax, rsi, QWORD PTR [rbp+16]
adcx r10, rsi
adox r10, rcx
mulx rbx, rsi, QWORD PTR [rbp+24]
adcx r11, rsi
adox r11, rax
mulx rax, rsi, QWORD PTR [rbp+32]
adcx r12, rsi
adox r12, rbx
mulx rbx, rsi, QWORD PTR [rbp+40]
adcx r13, rsi
adox r13, rax
mulx rax, rsi, QWORD PTR [rbp+48]
adcx r14, rsi
adox r14, rbx
mulx rbx, rsi, QWORD PTR [rbp+56]
adcx r15, rsi
adox r15, rax
adcx r8, rcx
adox r8, rbx
mov rsi, QWORD PTR [rdi+80]
mov rcx, QWORD PTR [rdi+224]
shl rcx, 4
add rsi, rcx
mov QWORD PTR [rsi+40], r10
mov QWORD PTR [rsi+48], r11
mov r10d, 0
mov rdx, QWORD PTR [rbp+16]
xor ecx, ecx
mulx rax, rsi, QWORD PTR [rbp+24]
adcx r12, rsi
adox r12, rcx
mulx rbx, rsi, QWORD PTR [rbp+32]
adcx r13, rsi
adox r13, rax
mulx rax, rsi, QWORD PTR [rbp+40]
adcx r14, rsi
adox r14, rbx
mulx rbx, rsi, QWORD PTR [rbp+48]
adcx r15, rsi
adox r15, rax
mulx rax, rsi, QWORD PTR [rbp+56]
adcx r8, rsi
adox r8, rbx
adcx r10, rcx
adox r10, rax
mov rsi, QWORD PTR [rdi+80]
mov rcx, QWORD PTR [rdi+224]
shl rcx, 4
add rsi, rcx
mov QWORD PTR [rsi+56], r12
mov QWORD PTR [rsi+64], r13
mov r12d, 0
mov rdx, QWORD PTR [rbp+24]
xor ecx, ecx
mulx rax, rsi, QWORD PTR [rbp+32]
adcx r14, rsi
adox r14, rcx
mulx rbx, rsi, QWORD PTR [rbp+40]
adcx r15, rsi
adox r15, rax
mulx rax, rsi, QWORD PTR [rbp+48]
adcx r8, rsi
adox r8, rbx
mulx rbx, rsi, QWORD PTR [rbp+56]
adcx r10, rsi
adox r10, rax
adcx r12, rcx
adox r12, rbx
mov rsi, QWORD PTR [rdi+80]
mov rcx, QWORD PTR [rdi+224]
shl rcx, 4
add rsi, rcx
mov QWORD PTR [rsi+72], r14
mov QWORD PTR [rsi+80], r15
mov r14d, 0
mov rdx, QWORD PTR [rbp+32]
xor ecx, ecx
mulx rax, rsi, QWORD PTR [rbp+40]
adcx r8, rsi
adox r8, rcx
mulx rbx, rsi, QWORD PTR [rbp+48]
adcx r10, rsi
adox r10, rax
mulx rax, rsi, QWORD PTR [rbp+56]
adcx r12, rsi
adox r12, rbx
adcx r14, rcx
adox r14, rax
mov rsi, QWORD PTR [rdi+80]
mov rcx, QWORD PTR [rdi+224]
shl rcx, 4
add rsi, rcx
mov QWORD PTR [rsi+88], r8
mov QWORD PTR [rsi+96], r10
mov r8d, 0
mov rdx, QWORD PTR [rbp+40]
xor ecx, ecx
mulx rax, rsi, QWORD PTR [rbp+48]
adcx r12, rsi
adox r12, rcx
mulx rbx, rsi, QWORD PTR [rbp+56]
adcx r14, rsi
adox r14, rax
adcx r8, rcx
adox r8, rbx
mov rsi, QWORD PTR [rdi+80]
mov rcx, QWORD PTR [rdi+224]
shl rcx, 4
add rsi, rcx
mov QWORD PTR [rsi+104], r12
mov QWORD PTR [rsi+112], r14
mov r12d, 0
mov rdx, QWORD PTR [rbp+48]
xor ecx, ecx
mulx rax, rsi, QWORD PTR [rbp+56]
adcx r8, rsi
adox r8, rcx
adcx r12, rcx
adox r12, rax
mov rsi, QWORD PTR [rdi+80]
mov rcx, QWORD PTR [rdi+224]
shl rcx, 4
add rsi, rcx
mov QWORD PTR [rsi+120], r8
mov QWORD PTR [rsi+128], r12
mov r8d, 0
mov rax, QWORD PTR [rdi+224]
add rax, 8
mov QWORD PTR [rdi+224], rax
cmp rax, QWORD PTR [rdi+48]
jne 217b
mov rax, QWORD PTR [rdi+48]
cmp rax, 8
je 218f
mov eax, 0
mov QWORD PTR [rdi+224], rax
220:
mov eax, 0
mov QWORD PTR [rdi+240], rax
mov rax, QWORD PTR [rdi+224]
add rax, 8
mov QWORD PTR [rdi+232], rax
221:
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
mov QWORD PTR [rsi], r8
mov QWORD PTR [rsi+8], r9
mov QWORD PTR [rsi+16], r10
mov QWORD PTR [rsi+24], r11
mov QWORD PTR [rsi+32], r12
mov QWORD PTR [rsi+40], r13
mov QWORD PTR [rsi+48], r14
mov QWORD PTR [rsi+56], r15
mov QWORD PTR [rdi+240], rax
mov rax, QWORD PTR [rdi+232]
add rax, 8
mov QWORD PTR [rdi+232], rax
cmp rax, QWORD PTR [rdi+48]
jne 221b
mov rax, QWORD PTR [rdi+224]
add rax, 8
cmp rax, QWORD PTR [rdi+48]
je 222f
mov rbp, QWORD PTR [rdi+240]
add rsi, 64
mov rdx, QWORD PTR [rdi+48]
shl rdx, 4
add rdx, QWORD PTR [rdi+80]
add rdx, 16
mov ecx, 0
224:
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
jne 224b
jmp 223f
222:
223:
mov rax, QWORD PTR [rdi+224]
add rax, 8
mov QWORD PTR [rdi+224], rax
mov rcx, QWORD PTR [rdi+48]
sub rcx, 8
cmp rax, rcx
jne 220b
jmp 219f
218:
219:
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
and rax, 3
cmp rax, 0
je 225f
mov r15d, 0
mov ebp, 0
mov r14d, 0
227:
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
jne 227b
jmp 226f
225:
mov r15d, 0
mov ebp, 0
mov r14d, 0
228:
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
jne 228b
226:
jmp 21f
29:
mov r8, QWORD PTR [rdi+80]
add r8, 16
mov r9, QWORD PTR [rdi+64]
mov rbp, QWORD PTR [rdi+48]
mov r10d, 0
229:
mov rdx, QWORD PTR [r8]
mulx rax, rdx, QWORD PTR [rdi+56]
mov rbx, rbp
mov ecx, 0
mov r14d, 0
mov r13, r8
mov r15, r9
230:
xor esi, esi
mulx rax, r11, QWORD PTR [r15]
adcx r11, QWORD PTR [r13]
adox r11, rcx
mov QWORD PTR [r13], r11
mulx rcx, r11, QWORD PTR [r15+8]
adcx r11, QWORD PTR [r13+8]
adox r11, rax
mov QWORD PTR [r13+8], r11
mulx rax, r11, QWORD PTR [r15+16]
adcx r11, QWORD PTR [r13+16]
adox r11, rcx
mov QWORD PTR [r13+16], r11
mulx rcx, r11, QWORD PTR [r15+24]
adcx r11, QWORD PTR [r13+24]
adox r11, rax
mov QWORD PTR [r13+24], r11
mulx rax, r11, QWORD PTR [r15+32]
adcx r11, QWORD PTR [r13+32]
adox r11, rcx
mov QWORD PTR [r13+32], r11
mulx rcx, r11, QWORD PTR [r15+40]
adcx r11, QWORD PTR [r13+40]
adox r11, rax
mov QWORD PTR [r13+40], r11
mulx rax, r11, QWORD PTR [r15+48]
adcx r11, QWORD PTR [r13+48]
adox r11, rcx
mov QWORD PTR [r13+48], r11
mulx rcx, r11, QWORD PTR [r15+56]
adcx r11, QWORD PTR [r13+56]
adox r11, rax
mov QWORD PTR [r13+56], r11
mov esi, 0
adox rcx, rsi
adcx rcx, rsi
add r13, 64
add r15, 64
add r14, 8
cmp r14, rbx
jne 230b
mov rax, QWORD PTR [r8+r14*8]
mov esi, 0
add rax, rcx
adc rsi, 0
add rax, r10
adc rsi, 0
mov QWORD PTR [r8+r14*8], rax
mov r10, rsi
add r8, 8
mov rax, QWORD PTR [rdi+88]
cmp r8, rax
jne 229b
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
231:
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
jne 231b
mov rax, QWORD PTR [r8+r12*8]
add rbp, rbp
sbb rax, 0
sbb rbp, rbp
mov r14, 0
232:
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
jne 232b
21:
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
.p2align 6
