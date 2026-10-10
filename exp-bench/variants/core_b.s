push rbx
push rbp
push r12
push r13
push r14
push r15
mov rbp, rdi
mov rdx, 0x123456789
mov rcx, rsi
2:
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
dec rcx
jnz 2b
pop r15
pop r14
pop r13
pop r12
pop rbp
pop rbx
ret
