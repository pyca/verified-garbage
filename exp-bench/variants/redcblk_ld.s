push rbx
push rbp
push r12
push r13
push r14
push r15
mov rdx, 0x123456789
mov rcx, rsi
mov rbp, rdi
mov r13, rbp
lea r15, [rbp+128]
xor r10d, r10d
2:
xor esi, esi
mov rbx, QWORD PTR [r13+0]
mulx rax, r11, QWORD PTR [r15+0]
adcx r11, rbx
adox r11, r10
mov QWORD PTR [r13+0], r11
mov rbx, QWORD PTR [r13+8]
mulx r10, r11, QWORD PTR [r15+8]
adcx r11, rbx
adox r11, rax
mov QWORD PTR [r13+8], r11
mov rbx, QWORD PTR [r13+16]
mulx rax, r11, QWORD PTR [r15+16]
adcx r11, rbx
adox r11, r10
mov QWORD PTR [r13+16], r11
mov rbx, QWORD PTR [r13+24]
mulx r10, r11, QWORD PTR [r15+24]
adcx r11, rbx
adox r11, rax
mov QWORD PTR [r13+24], r11
mov rbx, QWORD PTR [r13+32]
mulx rax, r11, QWORD PTR [r15+32]
adcx r11, rbx
adox r11, r10
mov QWORD PTR [r13+32], r11
mov rbx, QWORD PTR [r13+40]
mulx r10, r11, QWORD PTR [r15+40]
adcx r11, rbx
adox r11, rax
mov QWORD PTR [r13+40], r11
mov rbx, QWORD PTR [r13+48]
mulx rax, r11, QWORD PTR [r15+48]
adcx r11, rbx
adox r11, r10
mov QWORD PTR [r13+48], r11
mov rbx, QWORD PTR [r13+56]
mulx r10, r11, QWORD PTR [r15+56]
adcx r11, rbx
adox r11, rax
mov QWORD PTR [r13+56], r11
mov esi, 0
adox r10, rsi
adcx r10, rsi
dec rcx
jnz 2b
pop r15
pop r14
pop r13
pop r12
pop rbp
pop rbx
ret
