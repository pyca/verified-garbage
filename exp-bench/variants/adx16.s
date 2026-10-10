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
adcx r8, r12
adox r9, r13
adcx r8, r12
adox r9, r13
adcx r8, r12
adox r9, r13
adcx r8, r12
adox r9, r13
adcx r8, r12
adox r9, r13
adcx r8, r12
adox r9, r13
adcx r8, r12
adox r9, r13
adcx r8, r12
adox r9, r13
dec rcx
jnz 2b
pop r15
pop r14
pop r13
pop r12
pop rbp
pop rbx
ret
