push rbx
push rbp
push r12
push r13
push r14
push r15
mov rdx, 0x123456789
mov rcx, rsi
mov rbp, rdi
2:
xor eax, eax
adcx r8, QWORD PTR [rbp+0]
adox r9, QWORD PTR [rbp+64]
adcx r8, QWORD PTR [rbp+8]
adox r9, QWORD PTR [rbp+72]
adcx r8, QWORD PTR [rbp+16]
adox r9, QWORD PTR [rbp+80]
adcx r8, QWORD PTR [rbp+24]
adox r9, QWORD PTR [rbp+88]
adcx r8, QWORD PTR [rbp+32]
adox r9, QWORD PTR [rbp+96]
adcx r8, QWORD PTR [rbp+40]
adox r9, QWORD PTR [rbp+104]
adcx r8, QWORD PTR [rbp+48]
adox r9, QWORD PTR [rbp+112]
adcx r8, QWORD PTR [rbp+56]
adox r9, QWORD PTR [rbp+120]
dec rcx
jnz 2b
pop r15
pop r14
pop r13
pop r12
pop rbp
pop rbx
ret
