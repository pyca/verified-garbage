// The functions of `src/internal/vg_cast5_key_sboxes.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cast5_key_sboxes:
	adrp x9, {VG_CAST5_PLANES}
	add x9, x9, {VG_CAST5_PLANES}
	eor v24.16b, v16.16b, v2.16b
	eor v25.16b, v16.16b, v3.16b
	eor v26.16b, v24.16b, v3.16b
	ldr q28, [x9, #4096]
	ldr q29, [x9, #4112]
	ldr q30, [x9, #4128]
	ldr q31, [x9, #4144]
	tbl v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v16.16b
	ldr q28, [x9, #4160]
	ldr q29, [x9, #4176]
	ldr q30, [x9, #4192]
	ldr q31, [x9, #4208]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #4224]
	ldr q29, [x9, #4240]
	ldr q30, [x9, #4256]
	ldr q31, [x9, #4272]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #4288]
	ldr q29, [x9, #4304]
	ldr q30, [x9, #4320]
	ldr q31, [x9, #4336]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #4352]
	ldr q29, [x9, #4368]
	ldr q30, [x9, #4384]
	ldr q31, [x9, #4400]
	tbl v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v16.16b
	ldr q28, [x9, #4416]
	ldr q29, [x9, #4432]
	ldr q30, [x9, #4448]
	ldr q31, [x9, #4464]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #4480]
	ldr q29, [x9, #4496]
	ldr q30, [x9, #4512]
	ldr q31, [x9, #4528]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #4544]
	ldr q29, [x9, #4560]
	ldr q30, [x9, #4576]
	ldr q31, [x9, #4592]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #4608]
	ldr q29, [x9, #4624]
	ldr q30, [x9, #4640]
	ldr q31, [x9, #4656]
	tbl v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v16.16b
	ldr q28, [x9, #4672]
	ldr q29, [x9, #4688]
	ldr q30, [x9, #4704]
	ldr q31, [x9, #4720]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #4736]
	ldr q29, [x9, #4752]
	ldr q30, [x9, #4768]
	ldr q31, [x9, #4784]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #4800]
	ldr q29, [x9, #4816]
	ldr q30, [x9, #4832]
	ldr q31, [x9, #4848]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #4864]
	ldr q29, [x9, #4880]
	ldr q30, [x9, #4896]
	ldr q31, [x9, #4912]
	tbl v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v16.16b
	ldr q28, [x9, #4928]
	ldr q29, [x9, #4944]
	ldr q30, [x9, #4960]
	ldr q31, [x9, #4976]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #4992]
	ldr q29, [x9, #5008]
	ldr q30, [x9, #5024]
	ldr q31, [x9, #5040]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #5056]
	ldr q29, [x9, #5072]
	ldr q30, [x9, #5088]
	ldr q31, [x9, #5104]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	zip1 v0.16b, v20.16b, v22.16b
	zip2 v1.16b, v20.16b, v22.16b
	zip1 v20.16b, v21.16b, v23.16b
	zip2 v22.16b, v21.16b, v23.16b
	zip1 v21.16b, v0.16b, v20.16b
	zip2 v23.16b, v0.16b, v20.16b
	zip1 v0.16b, v1.16b, v22.16b
	zip2 v1.16b, v1.16b, v22.16b
	mov v4.16b, v21.16b
	mov v5.16b, v23.16b
	mov v7.s[0], v23.s[1]
	mov v6.s[0], v0.s[0]
	eor v24.16b, v17.16b, v2.16b
	eor v25.16b, v17.16b, v3.16b
	eor v26.16b, v24.16b, v3.16b
	ldr q28, [x9, #5120]
	ldr q29, [x9, #5136]
	ldr q30, [x9, #5152]
	ldr q31, [x9, #5168]
	tbl v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v17.16b
	ldr q28, [x9, #5184]
	ldr q29, [x9, #5200]
	ldr q30, [x9, #5216]
	ldr q31, [x9, #5232]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #5248]
	ldr q29, [x9, #5264]
	ldr q30, [x9, #5280]
	ldr q31, [x9, #5296]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #5312]
	ldr q29, [x9, #5328]
	ldr q30, [x9, #5344]
	ldr q31, [x9, #5360]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #5376]
	ldr q29, [x9, #5392]
	ldr q30, [x9, #5408]
	ldr q31, [x9, #5424]
	tbl v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v17.16b
	ldr q28, [x9, #5440]
	ldr q29, [x9, #5456]
	ldr q30, [x9, #5472]
	ldr q31, [x9, #5488]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #5504]
	ldr q29, [x9, #5520]
	ldr q30, [x9, #5536]
	ldr q31, [x9, #5552]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #5568]
	ldr q29, [x9, #5584]
	ldr q30, [x9, #5600]
	ldr q31, [x9, #5616]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #5632]
	ldr q29, [x9, #5648]
	ldr q30, [x9, #5664]
	ldr q31, [x9, #5680]
	tbl v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v17.16b
	ldr q28, [x9, #5696]
	ldr q29, [x9, #5712]
	ldr q30, [x9, #5728]
	ldr q31, [x9, #5744]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #5760]
	ldr q29, [x9, #5776]
	ldr q30, [x9, #5792]
	ldr q31, [x9, #5808]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #5824]
	ldr q29, [x9, #5840]
	ldr q30, [x9, #5856]
	ldr q31, [x9, #5872]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #5888]
	ldr q29, [x9, #5904]
	ldr q30, [x9, #5920]
	ldr q31, [x9, #5936]
	tbl v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v17.16b
	ldr q28, [x9, #5952]
	ldr q29, [x9, #5968]
	ldr q30, [x9, #5984]
	ldr q31, [x9, #6000]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #6016]
	ldr q29, [x9, #6032]
	ldr q30, [x9, #6048]
	ldr q31, [x9, #6064]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #6080]
	ldr q29, [x9, #6096]
	ldr q30, [x9, #6112]
	ldr q31, [x9, #6128]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	zip1 v0.16b, v20.16b, v22.16b
	zip2 v1.16b, v20.16b, v22.16b
	zip1 v20.16b, v21.16b, v23.16b
	zip2 v22.16b, v21.16b, v23.16b
	zip1 v21.16b, v0.16b, v20.16b
	zip2 v23.16b, v0.16b, v20.16b
	zip1 v0.16b, v1.16b, v22.16b
	zip2 v1.16b, v1.16b, v22.16b
	eor v4.16b, v4.16b, v21.16b
	eor v5.16b, v5.16b, v23.16b
	mov v7.s[1], v23.s[1]
	mov v6.s[1], v0.s[0]
	eor v24.16b, v18.16b, v2.16b
	eor v25.16b, v18.16b, v3.16b
	eor v26.16b, v24.16b, v3.16b
	ldr q28, [x9, #6144]
	ldr q29, [x9, #6160]
	ldr q30, [x9, #6176]
	ldr q31, [x9, #6192]
	tbl v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v18.16b
	ldr q28, [x9, #6208]
	ldr q29, [x9, #6224]
	ldr q30, [x9, #6240]
	ldr q31, [x9, #6256]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #6272]
	ldr q29, [x9, #6288]
	ldr q30, [x9, #6304]
	ldr q31, [x9, #6320]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #6336]
	ldr q29, [x9, #6352]
	ldr q30, [x9, #6368]
	ldr q31, [x9, #6384]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #6400]
	ldr q29, [x9, #6416]
	ldr q30, [x9, #6432]
	ldr q31, [x9, #6448]
	tbl v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v18.16b
	ldr q28, [x9, #6464]
	ldr q29, [x9, #6480]
	ldr q30, [x9, #6496]
	ldr q31, [x9, #6512]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #6528]
	ldr q29, [x9, #6544]
	ldr q30, [x9, #6560]
	ldr q31, [x9, #6576]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #6592]
	ldr q29, [x9, #6608]
	ldr q30, [x9, #6624]
	ldr q31, [x9, #6640]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #6656]
	ldr q29, [x9, #6672]
	ldr q30, [x9, #6688]
	ldr q31, [x9, #6704]
	tbl v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v18.16b
	ldr q28, [x9, #6720]
	ldr q29, [x9, #6736]
	ldr q30, [x9, #6752]
	ldr q31, [x9, #6768]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #6784]
	ldr q29, [x9, #6800]
	ldr q30, [x9, #6816]
	ldr q31, [x9, #6832]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #6848]
	ldr q29, [x9, #6864]
	ldr q30, [x9, #6880]
	ldr q31, [x9, #6896]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #6912]
	ldr q29, [x9, #6928]
	ldr q30, [x9, #6944]
	ldr q31, [x9, #6960]
	tbl v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v18.16b
	ldr q28, [x9, #6976]
	ldr q29, [x9, #6992]
	ldr q30, [x9, #7008]
	ldr q31, [x9, #7024]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #7040]
	ldr q29, [x9, #7056]
	ldr q30, [x9, #7072]
	ldr q31, [x9, #7088]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #7104]
	ldr q29, [x9, #7120]
	ldr q30, [x9, #7136]
	ldr q31, [x9, #7152]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	zip1 v0.16b, v20.16b, v22.16b
	zip2 v1.16b, v20.16b, v22.16b
	zip1 v20.16b, v21.16b, v23.16b
	zip2 v22.16b, v21.16b, v23.16b
	zip1 v21.16b, v0.16b, v20.16b
	zip2 v23.16b, v0.16b, v20.16b
	zip1 v0.16b, v1.16b, v22.16b
	zip2 v1.16b, v1.16b, v22.16b
	eor v4.16b, v4.16b, v21.16b
	eor v5.16b, v5.16b, v23.16b
	mov v7.s[2], v23.s[1]
	mov v6.s[2], v0.s[0]
	eor v24.16b, v19.16b, v2.16b
	eor v25.16b, v19.16b, v3.16b
	eor v26.16b, v24.16b, v3.16b
	ldr q28, [x9, #7168]
	ldr q29, [x9, #7184]
	ldr q30, [x9, #7200]
	ldr q31, [x9, #7216]
	tbl v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v19.16b
	ldr q28, [x9, #7232]
	ldr q29, [x9, #7248]
	ldr q30, [x9, #7264]
	ldr q31, [x9, #7280]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #7296]
	ldr q29, [x9, #7312]
	ldr q30, [x9, #7328]
	ldr q31, [x9, #7344]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #7360]
	ldr q29, [x9, #7376]
	ldr q30, [x9, #7392]
	ldr q31, [x9, #7408]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #7424]
	ldr q29, [x9, #7440]
	ldr q30, [x9, #7456]
	ldr q31, [x9, #7472]
	tbl v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v19.16b
	ldr q28, [x9, #7488]
	ldr q29, [x9, #7504]
	ldr q30, [x9, #7520]
	ldr q31, [x9, #7536]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #7552]
	ldr q29, [x9, #7568]
	ldr q30, [x9, #7584]
	ldr q31, [x9, #7600]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #7616]
	ldr q29, [x9, #7632]
	ldr q30, [x9, #7648]
	ldr q31, [x9, #7664]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #7680]
	ldr q29, [x9, #7696]
	ldr q30, [x9, #7712]
	ldr q31, [x9, #7728]
	tbl v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v19.16b
	ldr q28, [x9, #7744]
	ldr q29, [x9, #7760]
	ldr q30, [x9, #7776]
	ldr q31, [x9, #7792]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #7808]
	ldr q29, [x9, #7824]
	ldr q30, [x9, #7840]
	ldr q31, [x9, #7856]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #7872]
	ldr q29, [x9, #7888]
	ldr q30, [x9, #7904]
	ldr q31, [x9, #7920]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #7936]
	ldr q29, [x9, #7952]
	ldr q30, [x9, #7968]
	ldr q31, [x9, #7984]
	tbl v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v19.16b
	ldr q28, [x9, #8000]
	ldr q29, [x9, #8016]
	ldr q30, [x9, #8032]
	ldr q31, [x9, #8048]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #8064]
	ldr q29, [x9, #8080]
	ldr q30, [x9, #8096]
	ldr q31, [x9, #8112]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #8128]
	ldr q29, [x9, #8144]
	ldr q30, [x9, #8160]
	ldr q31, [x9, #8176]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	zip1 v0.16b, v20.16b, v22.16b
	zip2 v1.16b, v20.16b, v22.16b
	zip1 v20.16b, v21.16b, v23.16b
	zip2 v22.16b, v21.16b, v23.16b
	zip1 v21.16b, v0.16b, v20.16b
	zip2 v23.16b, v0.16b, v20.16b
	zip1 v0.16b, v1.16b, v22.16b
	zip2 v1.16b, v1.16b, v22.16b
	eor v4.16b, v4.16b, v21.16b
	eor v5.16b, v5.16b, v23.16b
	mov v7.s[3], v23.s[1]
	mov v6.s[3], v0.s[0]
	ret
	.p2align 6
