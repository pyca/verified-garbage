// The functions of `src/cast5.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cast5_expand_key:
	mov r12, r3
	str r4, [r12, #64]
	str r5, [r12, #68]
	str r6, [r12, #72]
	str r7, [r12, #76]
	str r8, [r12, #80]
	str r9, [r12, #84]
	str r10, [r12, #88]
	str r11, [r12, #92]
	str lr, [r12, #96]
	mov r3, #0
	str r3, [r12, #16]
	str r3, [r12, #20]
	str r3, [r12, #24]
	str r3, [r12, #28]
	add r3, r12, #16
20:
	ldrb r4, [r0, #0]
	strb r4, [r3, #0]
	add r0, r0, #1
	add r3, r3, #1
	subs r1, r1, #1
	bne 20b
	mov lr, r2
	mov r3, #2
21:
	mov r2, #0
22:
	cmp r2, #0
	beq 23f
	cmp r2, #1
	beq 25f
	cmp r2, #2
	beq 27f
	cmp r2, #3
	beq 29f
	cmp r2, #4
	beq 211f
	cmp r2, #5
	beq 213f
	cmp r2, #6
	beq 215f
	cmp r2, #7
	beq 217f
	cmp r2, #8
	beq 219f
	cmp r2, #9
	beq 221f
	cmp r2, #10
	beq 223f
	cmp r2, #11
	beq 225f
	cmp r2, #12
	beq 227f
	cmp r2, #13
	beq 229f
	cmp r2, #14
	beq 231f
	cmp r2, #15
	beq 233f
	cmp r2, #16
	beq 235f
	cmp r2, #17
	beq 237f
	cmp r2, #18
	beq 239f
	cmp r2, #19
	beq 241f
	cmp r2, #20
	beq 243f
	cmp r2, #21
	beq 245f
	cmp r2, #22
	beq 247f
	cmp r2, #23
	beq 249f
	cmp r2, #24
	beq 251f
	cmp r2, #25
	beq 253f
	cmp r2, #26
	beq 255f
	cmp r2, #27
	beq 257f
	cmp r2, #28
	beq 259f
	cmp r2, #29
	beq 261f
	cmp r2, #30
	beq 263f
	cmp r2, #31
	beq 265f
	cmp r2, #32
	beq 267f
	cmp r2, #33
	beq 269f
	cmp r2, #34
	beq 271f
	cmp r2, #35
	beq 273f
	cmp r2, #36
	beq 275f
	cmp r2, #37
	beq 277f
	cmp r2, #38
	beq 279f
	cmp r2, #39
	beq 281f
	b 282f
281:
	ldrb r4, [r12, #16]
	ldrb r5, [r12, #17]
	ldrb r6, [r12, #31]
	ldrb r7, [r12, #30]
282:
	b 280f
279:
	ldrb r4, [r12, #18]
	ldrb r5, [r12, #19]
	ldrb r6, [r12, #29]
	ldrb r7, [r12, #28]
280:
	b 278f
277:
	ldrb r4, [r12, #20]
	ldrb r5, [r12, #21]
	ldrb r6, [r12, #27]
	ldrb r7, [r12, #26]
278:
	b 276f
275:
	ldrb r4, [r12, #22]
	ldrb r5, [r12, #23]
	ldrb r6, [r12, #25]
	ldrb r7, [r12, #24]
276:
	b 274f
273:
	ldrb r4, [r12, #29]
	ldrb r5, [r12, #24]
	ldrb r6, [r12, #23]
	ldrb r7, [r12, #19]
274:
	b 272f
271:
	ldrb r4, [r12, #24]
	ldrb r5, [r12, #27]
	ldrb r6, [r12, #25]
	ldrb r7, [r12, #26]
272:
	b 270f
269:
	ldrb r4, [r12, #20]
	ldrb r5, [r12, #21]
	ldrb r6, [r12, #22]
	ldrb r7, [r12, #23]
270:
	b 268f
267:
	ldrb r4, [r12, #19]
	ldrb r5, [r12, #17]
	ldrb r6, [r12, #18]
	ldrb r7, [r12, #16]
268:
	b 266f
265:
	ldrb r4, [r12, #38]
	ldrb r5, [r12, #36]
	ldrb r6, [r12, #39]
	ldrb r7, [r12, #37]
266:
	b 264f
263:
	ldrb r4, [r12, #34]
	ldrb r5, [r12, #32]
	ldrb r6, [r12, #35]
	ldrb r7, [r12, #33]
264:
	b 262f
261:
	ldrb r4, [r12, #43]
	ldrb r5, [r12, #42]
	ldrb r6, [r12, #36]
	ldrb r7, [r12, #37]
262:
	b 260f
259:
	ldrb r4, [r12, #41]
	ldrb r5, [r12, #40]
	ldrb r6, [r12, #38]
	ldrb r7, [r12, #39]
260:
	b 258f
257:
	ldrb r4, [r12, #47]
	ldrb r5, [r12, #46]
	ldrb r6, [r12, #32]
	ldrb r7, [r12, #33]
258:
	b 256f
255:
	ldrb r4, [r12, #45]
	ldrb r5, [r12, #44]
	ldrb r6, [r12, #34]
	ldrb r7, [r12, #35]
256:
	b 254f
253:
	ldrb r4, [r12, #38]
	ldrb r5, [r12, #34]
	ldrb r6, [r12, #44]
	ldrb r7, [r12, #41]
254:
	b 252f
251:
	ldrb r4, [r12, #40]
	ldrb r5, [r12, #43]
	ldrb r6, [r12, #41]
	ldrb r7, [r12, #42]
252:
	b 250f
249:
	ldrb r4, [r12, #36]
	ldrb r5, [r12, #37]
	ldrb r6, [r12, #38]
	ldrb r7, [r12, #39]
250:
	b 248f
247:
	ldrb r4, [r12, #35]
	ldrb r5, [r12, #33]
	ldrb r6, [r12, #34]
	ldrb r7, [r12, #32]
248:
	b 246f
245:
	ldrb r4, [r12, #30]
	ldrb r5, [r12, #28]
	ldrb r6, [r12, #31]
	ldrb r7, [r12, #29]
246:
	b 244f
243:
	ldrb r4, [r12, #26]
	ldrb r5, [r12, #24]
	ldrb r6, [r12, #27]
	ldrb r7, [r12, #25]
244:
	b 242f
241:
	ldrb r4, [r12, #27]
	ldrb r5, [r12, #26]
	ldrb r6, [r12, #20]
	ldrb r7, [r12, #21]
242:
	b 240f
239:
	ldrb r4, [r12, #25]
	ldrb r5, [r12, #24]
	ldrb r6, [r12, #22]
	ldrb r7, [r12, #23]
240:
	b 238f
237:
	ldrb r4, [r12, #31]
	ldrb r5, [r12, #30]
	ldrb r6, [r12, #16]
	ldrb r7, [r12, #17]
238:
	b 236f
235:
	ldrb r4, [r12, #29]
	ldrb r5, [r12, #28]
	ldrb r6, [r12, #18]
	ldrb r7, [r12, #19]
236:
	b 234f
233:
	ldrb r4, [r12, #23]
	ldrb r5, [r12, #19]
	ldrb r6, [r12, #29]
	ldrb r7, [r12, #24]
234:
	b 232f
231:
	ldrb r4, [r12, #24]
	ldrb r5, [r12, #27]
	ldrb r6, [r12, #25]
	ldrb r7, [r12, #26]
232:
	b 230f
229:
	ldrb r4, [r12, #20]
	ldrb r5, [r12, #21]
	ldrb r6, [r12, #22]
	ldrb r7, [r12, #23]
230:
	b 228f
227:
	ldrb r4, [r12, #19]
	ldrb r5, [r12, #17]
	ldrb r6, [r12, #18]
	ldrb r7, [r12, #16]
228:
	b 226f
225:
	ldrb r4, [r12, #38]
	ldrb r5, [r12, #36]
	ldrb r6, [r12, #39]
	ldrb r7, [r12, #37]
226:
	b 224f
223:
	ldrb r4, [r12, #34]
	ldrb r5, [r12, #32]
	ldrb r6, [r12, #35]
	ldrb r7, [r12, #33]
224:
	b 222f
221:
	ldrb r4, [r12, #32]
	ldrb r5, [r12, #33]
	ldrb r6, [r12, #47]
	ldrb r7, [r12, #46]
222:
	b 220f
219:
	ldrb r4, [r12, #34]
	ldrb r5, [r12, #35]
	ldrb r6, [r12, #45]
	ldrb r7, [r12, #44]
220:
	b 218f
217:
	ldrb r4, [r12, #36]
	ldrb r5, [r12, #37]
	ldrb r6, [r12, #43]
	ldrb r7, [r12, #42]
218:
	b 216f
215:
	ldrb r4, [r12, #38]
	ldrb r5, [r12, #39]
	ldrb r6, [r12, #41]
	ldrb r7, [r12, #40]
216:
	b 214f
213:
	ldrb r4, [r12, #44]
	ldrb r5, [r12, #41]
	ldrb r6, [r12, #38]
	ldrb r7, [r12, #34]
214:
	b 212f
211:
	ldrb r4, [r12, #40]
	ldrb r5, [r12, #43]
	ldrb r6, [r12, #41]
	ldrb r7, [r12, #42]
212:
	b 210f
29:
	ldrb r4, [r12, #36]
	ldrb r5, [r12, #37]
	ldrb r6, [r12, #38]
	ldrb r7, [r12, #39]
210:
	b 28f
27:
	ldrb r4, [r12, #35]
	ldrb r5, [r12, #33]
	ldrb r6, [r12, #34]
	ldrb r7, [r12, #32]
28:
	b 26f
25:
	ldrb r4, [r12, #30]
	ldrb r5, [r12, #28]
	ldrb r6, [r12, #31]
	ldrb r7, [r12, #29]
26:
	b 24f
23:
	ldrb r4, [r12, #26]
	ldrb r5, [r12, #24]
	ldrb r6, [r12, #27]
	ldrb r7, [r12, #25]
24:
	str r2, [r12, #0]
	str r3, [r12, #4]
	movw r3, #:lower16:({VG_CAST5_S5678}
	movt r3, #:upper16:({VG_CAST5_S5678}
2:
	add r3, pc
3:
	mov r2, #0
	mov r8, #0
	mov r9, #0
	mov r10, #0
	mov r11, #0
283:
	ldr r1, [r3, #0]
	eor r0, r4, r2
	sub r0, r0, #1
	lsr r0, r0, #8
	orr r0, r0, r0, lsl #8
	and r1, r1, r0
	orr r8, r8, r1
	ldr r1, [r3, #4]
	eor r0, r5, r2
	sub r0, r0, #1
	lsr r0, r0, #8
	orr r0, r0, r0, lsl #8
	and r1, r1, r0
	orr r9, r9, r1
	ldr r1, [r3, #8]
	eor r0, r6, r2
	sub r0, r0, #1
	lsr r0, r0, #8
	orr r0, r0, r0, lsl #8
	and r1, r1, r0
	orr r10, r10, r1
	ldr r1, [r3, #12]
	eor r0, r7, r2
	sub r0, r0, #1
	lsr r0, r0, #8
	orr r0, r0, r0, lsl #8
	and r1, r1, r0
	orr r11, r11, r1
	add r3, r3, #16
	cmp r2, #255
	add r2, r2, #1
	bne 283b
	ldr r2, [r12, #0]
	ldr r3, [r12, #4]
	cmp r2, #0
	beq 284f
	cmp r2, #1
	beq 286f
	cmp r2, #2
	beq 288f
	cmp r2, #3
	beq 290f
	cmp r2, #4
	beq 292f
	cmp r2, #5
	beq 294f
	cmp r2, #6
	beq 296f
	cmp r2, #7
	beq 298f
	cmp r2, #8
	beq 2100f
	cmp r2, #9
	beq 2102f
	cmp r2, #10
	beq 2104f
	cmp r2, #11
	beq 2106f
	cmp r2, #12
	beq 2108f
	cmp r2, #13
	beq 2110f
	cmp r2, #14
	beq 2112f
	cmp r2, #15
	beq 2114f
	cmp r2, #16
	beq 2116f
	cmp r2, #17
	beq 2118f
	cmp r2, #18
	beq 2120f
	cmp r2, #19
	beq 2122f
	cmp r2, #20
	beq 2124f
	cmp r2, #21
	beq 2126f
	cmp r2, #22
	beq 2128f
	cmp r2, #23
	beq 2130f
	cmp r2, #24
	beq 2132f
	cmp r2, #25
	beq 2134f
	cmp r2, #26
	beq 2136f
	cmp r2, #27
	beq 2138f
	cmp r2, #28
	beq 2140f
	cmp r2, #29
	beq 2142f
	cmp r2, #30
	beq 2144f
	cmp r2, #31
	beq 2146f
	cmp r2, #32
	beq 2148f
	cmp r2, #33
	beq 2150f
	cmp r2, #34
	beq 2152f
	cmp r2, #35
	beq 2154f
	cmp r2, #36
	beq 2156f
	cmp r2, #37
	beq 2158f
	cmp r2, #38
	beq 2160f
	cmp r2, #39
	beq 2162f
	b 2163f
2162:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #48]
	eor r0, r0, r1
	str r0, [lr, #60]
2163:
	b 2161f
2160:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #52]
	eor r0, r0, r1
	str r0, [lr, #56]
2161:
	b 2159f
2158:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #56]
	eor r0, r0, r1
	str r0, [lr, #52]
2159:
	b 2157f
2156:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #60]
	eor r0, r0, r1
	str r0, [lr, #48]
2157:
	b 2155f
2154:
	str r8, [r12, #48]
	str r9, [r12, #52]
	str r10, [r12, #56]
	str r11, [r12, #60]
2155:
	b 2153f
2152:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #56]
	eor r0, r0, r1
	ldr r1, [r12, #44]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #28]
2153:
	b 2151f
2150:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #60]
	eor r0, r0, r1
	ldr r1, [r12, #36]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #24]
2151:
	b 2149f
2148:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #48]
	eor r0, r0, r1
	ldr r1, [r12, #32]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #20]
2149:
	b 2147f
2146:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #52]
	eor r0, r0, r1
	ldr r1, [r12, #40]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #16]
2147:
	b 2145f
2144:
	str r8, [r12, #48]
	str r9, [r12, #52]
	str r10, [r12, #56]
	str r11, [r12, #60]
2145:
	b 2143f
2142:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #48]
	eor r0, r0, r1
	str r0, [lr, #44]
2143:
	b 2141f
2140:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #52]
	eor r0, r0, r1
	str r0, [lr, #40]
2141:
	b 2139f
2138:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #56]
	eor r0, r0, r1
	str r0, [lr, #36]
2139:
	b 2137f
2136:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #60]
	eor r0, r0, r1
	str r0, [lr, #32]
2137:
	b 2135f
2134:
	str r8, [r12, #48]
	str r9, [r12, #52]
	str r10, [r12, #56]
	str r11, [r12, #60]
2135:
	b 2133f
2132:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #56]
	eor r0, r0, r1
	ldr r1, [r12, #20]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #44]
2133:
	b 2131f
2130:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #60]
	eor r0, r0, r1
	ldr r1, [r12, #28]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #40]
2131:
	b 2129f
2128:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #48]
	eor r0, r0, r1
	ldr r1, [r12, #24]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #36]
2129:
	b 2127f
2126:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #52]
	eor r0, r0, r1
	ldr r1, [r12, #16]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #32]
2127:
	b 2125f
2124:
	str r8, [r12, #48]
	str r9, [r12, #52]
	str r10, [r12, #56]
	str r11, [r12, #60]
2125:
	b 2123f
2122:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #48]
	eor r0, r0, r1
	str r0, [lr, #28]
2123:
	b 2121f
2120:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #52]
	eor r0, r0, r1
	str r0, [lr, #24]
2121:
	b 2119f
2118:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #56]
	eor r0, r0, r1
	str r0, [lr, #20]
2119:
	b 2117f
2116:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #60]
	eor r0, r0, r1
	str r0, [lr, #16]
2117:
	b 2115f
2114:
	str r8, [r12, #48]
	str r9, [r12, #52]
	str r10, [r12, #56]
	str r11, [r12, #60]
2115:
	b 2113f
2112:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #56]
	eor r0, r0, r1
	ldr r1, [r12, #44]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #28]
2113:
	b 2111f
2110:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #60]
	eor r0, r0, r1
	ldr r1, [r12, #36]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #24]
2111:
	b 2109f
2108:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #48]
	eor r0, r0, r1
	ldr r1, [r12, #32]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #20]
2109:
	b 2107f
2106:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #52]
	eor r0, r0, r1
	ldr r1, [r12, #40]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #16]
2107:
	b 2105f
2104:
	str r8, [r12, #48]
	str r9, [r12, #52]
	str r10, [r12, #56]
	str r11, [r12, #60]
2105:
	b 2103f
2102:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #48]
	eor r0, r0, r1
	str r0, [lr, #12]
2103:
	b 2101f
2100:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #52]
	eor r0, r0, r1
	str r0, [lr, #8]
2101:
	b 299f
298:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #56]
	eor r0, r0, r1
	str r0, [lr, #4]
299:
	b 297f
296:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #60]
	eor r0, r0, r1
	str r0, [lr, #0]
297:
	b 295f
294:
	str r8, [r12, #48]
	str r9, [r12, #52]
	str r10, [r12, #56]
	str r11, [r12, #60]
295:
	b 293f
292:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #56]
	eor r0, r0, r1
	ldr r1, [r12, #20]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #44]
293:
	b 291f
290:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #60]
	eor r0, r0, r1
	ldr r1, [r12, #28]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #40]
291:
	b 289f
288:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #48]
	eor r0, r0, r1
	ldr r1, [r12, #24]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #36]
289:
	b 287f
286:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #52]
	eor r0, r0, r1
	ldr r1, [r12, #16]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #32]
287:
	b 285f
284:
	str r8, [r12, #48]
	str r9, [r12, #52]
	str r10, [r12, #56]
	str r11, [r12, #60]
285:
	add r2, r2, #1
	cmp r2, #40
	bne 22b
	add lr, lr, #64
	subs r3, r3, #1
	bne 21b
	ldr r4, [r12, #64]
	ldr r5, [r12, #68]
	ldr r6, [r12, #72]
	ldr r7, [r12, #76]
	ldr r8, [r12, #80]
	ldr r9, [r12, #84]
	ldr r10, [r12, #88]
	ldr r11, [r12, #92]
	ldr lr, [r12, #96]
	bx lr

vg_cast5_ecb_encrypt:
	ldr r12, [sp, #0]
	str r4, [r12, #64]
	str r5, [r12, #68]
	str r6, [r12, #72]
	str r7, [r12, #76]
	str r8, [r12, #80]
	str r9, [r12, #84]
	str r10, [r12, #88]
	str r11, [r12, #92]
	str lr, [r12, #96]
	str r2, [r12, #0]
	str r3, [r12, #4]
	str r0, [r12, #8]
	str r1, [r12, #12]
	cmp r3, #0
	beq 20f
22:
	ldr r0, [r12, #0]
	ldr r2, [r0, #0]
	rev r2, r2
	ldr r3, [r0, #4]
	rev r3, r3
	ldr lr, [r12, #8]
	ldr r1, [r12, #12]
	str r1, [r12, #16]
	mov r1, #1
	str r1, [r12, #20]
23:
	ldr r0, [r12, #20]
	cmp r0, #1
	beq 24f
	cmp r0, #2
	beq 26f
	ldr r1, [lr, #0]
	sub r1, r1, r3
	b 27f
26:
	ldr r1, [lr, #0]
	eor r1, r1, r3
27:
	b 25f
24:
	ldr r1, [lr, #0]
	add r1, r1, r3
25:
	ldr r0, [lr, #64]
	and r4, r0, #1
	sub r4, r4, #1
	ror r5, r1, #31
	eor r1, r1, r5
	and r1, r1, r4
	eor r1, r1, r5
	lsr r0, r0, #1
	and r4, r0, #1
	sub r4, r4, #1
	ror r5, r1, #30
	eor r1, r1, r5
	and r1, r1, r4
	eor r1, r1, r5
	lsr r0, r0, #1
	and r4, r0, #1
	sub r4, r4, #1
	ror r5, r1, #28
	eor r1, r1, r5
	and r1, r1, r4
	eor r1, r1, r5
	lsr r0, r0, #1
	and r4, r0, #1
	sub r4, r4, #1
	ror r5, r1, #24
	eor r1, r1, r5
	and r1, r1, r4
	eor r1, r1, r5
	lsr r0, r0, #1
	and r4, r0, #1
	sub r4, r4, #1
	ror r5, r1, #16
	eor r1, r1, r5
	and r1, r1, r4
	eor r1, r1, r5
	and r4, r1, #255
	lsr r5, r1, #8
	and r5, r5, #255
	lsr r6, r1, #16
	and r6, r6, #255
	lsr r7, r1, #24
	str r2, [r12, #24]
	str r3, [r12, #28]
	movw r3, #:lower16:({VG_CAST5_S1234}
	movt r3, #:upper16:({VG_CAST5_S1234}
2:
	add r3, pc
3:
	mov r2, #0
	mov r8, #0
	mov r9, #0
	mov r10, #0
	mov r11, #0
28:
	ldr r1, [r3, #0]
	eor r0, r4, r2
	sub r0, r0, #1
	lsr r0, r0, #8
	orr r0, r0, r0, lsl #8
	and r1, r1, r0
	orr r8, r8, r1
	ldr r1, [r3, #4]
	eor r0, r5, r2
	sub r0, r0, #1
	lsr r0, r0, #8
	orr r0, r0, r0, lsl #8
	and r1, r1, r0
	orr r9, r9, r1
	ldr r1, [r3, #8]
	eor r0, r6, r2
	sub r0, r0, #1
	lsr r0, r0, #8
	orr r0, r0, r0, lsl #8
	and r1, r1, r0
	orr r10, r10, r1
	ldr r1, [r3, #12]
	eor r0, r7, r2
	sub r0, r0, #1
	lsr r0, r0, #8
	orr r0, r0, r0, lsl #8
	and r1, r1, r0
	orr r11, r11, r1
	add r3, r3, #16
	cmp r2, #255
	add r2, r2, #1
	bne 28b
	ldr r2, [r12, #24]
	ldr r3, [r12, #28]
	ldr r0, [r12, #20]
	cmp r0, #1
	beq 29f
	cmp r0, #2
	beq 211f
	add r1, r11, r10
	eor r1, r1, r9
	sub r1, r1, r8
	b 212f
211:
	sub r1, r11, r10
	add r1, r1, r9
	eor r1, r1, r8
212:
	b 210f
29:
	eor r1, r11, r10
	sub r1, r1, r9
	add r1, r1, r8
210:
	eor r1, r1, r2
	mov r2, r3
	mov r3, r1
	add lr, lr, #4
	ldr r0, [r12, #20]
	cmp r0, #3
	beq 213f
	add r0, r0, #1
	b 214f
213:
	mov r0, #1
214:
	str r0, [r12, #20]
	ldr r0, [r12, #16]
	subs r0, r0, #1
	str r0, [r12, #16]
	bne 23b
	ldr r0, [r12, #0]
	ldr r1, [r12, #4]
	ldr r4, [r12, #8]
	ldr r5, [r12, #12]
	rev r3, r3
	str r3, [r0, #0]
	rev r2, r2
	str r2, [r0, #4]
	str r0, [r12, #0]
	str r1, [r12, #4]
	str r4, [r12, #8]
	str r5, [r12, #12]
	ldr r0, [r12, #0]
	add r0, r0, #8
	str r0, [r12, #0]
	ldr r0, [r12, #4]
	subs r0, r0, #1
	str r0, [r12, #4]
	bne 22b
	b 21f
20:
21:
	ldr r4, [r12, #64]
	ldr r5, [r12, #68]
	ldr r6, [r12, #72]
	ldr r7, [r12, #76]
	ldr r8, [r12, #80]
	ldr r9, [r12, #84]
	ldr r10, [r12, #88]
	ldr r11, [r12, #92]
	ldr lr, [r12, #96]
	bx lr

vg_cast5_ecb_decrypt:
	ldr r12, [sp, #0]
	str r4, [r12, #64]
	str r5, [r12, #68]
	str r6, [r12, #72]
	str r7, [r12, #76]
	str r8, [r12, #80]
	str r9, [r12, #84]
	str r10, [r12, #88]
	str r11, [r12, #92]
	str lr, [r12, #96]
	str r2, [r12, #0]
	str r3, [r12, #4]
	str r0, [r12, #8]
	str r1, [r12, #12]
	cmp r3, #0
	beq 20f
22:
	ldr r0, [r12, #0]
	ldr r2, [r0, #0]
	rev r2, r2
	ldr r3, [r0, #4]
	rev r3, r3
	ldr lr, [r12, #8]
	ldr r1, [r12, #12]
	str r1, [r12, #16]
	add lr, lr, r1, lsl #2
	sub lr, lr, #4
	lsr r0, r1, #1
	movw r1, #9
	sub r1, r1, r0
	str r1, [r12, #20]
23:
	ldr r0, [r12, #20]
	cmp r0, #1
	beq 24f
	cmp r0, #2
	beq 26f
	ldr r1, [lr, #0]
	sub r1, r1, r3
	b 27f
26:
	ldr r1, [lr, #0]
	eor r1, r1, r3
27:
	b 25f
24:
	ldr r1, [lr, #0]
	add r1, r1, r3
25:
	ldr r0, [lr, #64]
	and r4, r0, #1
	sub r4, r4, #1
	ror r5, r1, #31
	eor r1, r1, r5
	and r1, r1, r4
	eor r1, r1, r5
	lsr r0, r0, #1
	and r4, r0, #1
	sub r4, r4, #1
	ror r5, r1, #30
	eor r1, r1, r5
	and r1, r1, r4
	eor r1, r1, r5
	lsr r0, r0, #1
	and r4, r0, #1
	sub r4, r4, #1
	ror r5, r1, #28
	eor r1, r1, r5
	and r1, r1, r4
	eor r1, r1, r5
	lsr r0, r0, #1
	and r4, r0, #1
	sub r4, r4, #1
	ror r5, r1, #24
	eor r1, r1, r5
	and r1, r1, r4
	eor r1, r1, r5
	lsr r0, r0, #1
	and r4, r0, #1
	sub r4, r4, #1
	ror r5, r1, #16
	eor r1, r1, r5
	and r1, r1, r4
	eor r1, r1, r5
	and r4, r1, #255
	lsr r5, r1, #8
	and r5, r5, #255
	lsr r6, r1, #16
	and r6, r6, #255
	lsr r7, r1, #24
	str r2, [r12, #24]
	str r3, [r12, #28]
	movw r3, #:lower16:({VG_CAST5_S1234}
	movt r3, #:upper16:({VG_CAST5_S1234}
2:
	add r3, pc
3:
	mov r2, #0
	mov r8, #0
	mov r9, #0
	mov r10, #0
	mov r11, #0
28:
	ldr r1, [r3, #0]
	eor r0, r4, r2
	sub r0, r0, #1
	lsr r0, r0, #8
	orr r0, r0, r0, lsl #8
	and r1, r1, r0
	orr r8, r8, r1
	ldr r1, [r3, #4]
	eor r0, r5, r2
	sub r0, r0, #1
	lsr r0, r0, #8
	orr r0, r0, r0, lsl #8
	and r1, r1, r0
	orr r9, r9, r1
	ldr r1, [r3, #8]
	eor r0, r6, r2
	sub r0, r0, #1
	lsr r0, r0, #8
	orr r0, r0, r0, lsl #8
	and r1, r1, r0
	orr r10, r10, r1
	ldr r1, [r3, #12]
	eor r0, r7, r2
	sub r0, r0, #1
	lsr r0, r0, #8
	orr r0, r0, r0, lsl #8
	and r1, r1, r0
	orr r11, r11, r1
	add r3, r3, #16
	cmp r2, #255
	add r2, r2, #1
	bne 28b
	ldr r2, [r12, #24]
	ldr r3, [r12, #28]
	ldr r0, [r12, #20]
	cmp r0, #1
	beq 29f
	cmp r0, #2
	beq 211f
	add r1, r11, r10
	eor r1, r1, r9
	sub r1, r1, r8
	b 212f
211:
	sub r1, r11, r10
	add r1, r1, r9
	eor r1, r1, r8
212:
	b 210f
29:
	eor r1, r11, r10
	sub r1, r1, r9
	add r1, r1, r8
210:
	eor r1, r1, r2
	mov r2, r3
	mov r3, r1
	sub lr, lr, #4
	ldr r0, [r12, #20]
	cmp r0, #1
	beq 213f
	sub r0, r0, #1
	b 214f
213:
	mov r0, #3
214:
	str r0, [r12, #20]
	ldr r0, [r12, #16]
	subs r0, r0, #1
	str r0, [r12, #16]
	bne 23b
	ldr r0, [r12, #0]
	ldr r1, [r12, #4]
	ldr r4, [r12, #8]
	ldr r5, [r12, #12]
	rev r3, r3
	str r3, [r0, #0]
	rev r2, r2
	str r2, [r0, #4]
	str r0, [r12, #0]
	str r1, [r12, #4]
	str r4, [r12, #8]
	str r5, [r12, #12]
	ldr r0, [r12, #0]
	add r0, r0, #8
	str r0, [r12, #0]
	ldr r0, [r12, #4]
	subs r0, r0, #1
	str r0, [r12, #4]
	bne 22b
	b 21f
20:
21:
	ldr r4, [r12, #64]
	ldr r5, [r12, #68]
	ldr r6, [r12, #72]
	ldr r7, [r12, #76]
	ldr r8, [r12, #80]
	ldr r9, [r12, #84]
	ldr r10, [r12, #88]
	ldr r11, [r12, #92]
	ldr lr, [r12, #96]
	bx lr
