// The functions of `src/sha3.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha3_224_update:
	lea esp, [esp-24]
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [esp], eax
	mov eax, 144
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [esp+20], eax
	call {vg_keccak_absorb_scratch}
	lea esp, [esp+24]
	ret
	.p2align 6

vg_sha3_224_finalize:
	lea esp, [esp-664]
	mov eax, DWORD PTR [esp+668]
	mov DWORD PTR [esp], eax
	mov eax, 144
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+672]
	mov DWORD PTR [esp+8], eax
	mov eax, 6
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+16], eax
	call {vg_keccak_pad_scratch}
	mov eax, DWORD PTR [esp+668]
	mov DWORD PTR [esp], eax
	mov eax, 144
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+676]
	mov DWORD PTR [esp+12], eax
	mov eax, 28
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	call {vg_keccak_squeeze_scratch}
	lea esp, [esp+664]
	ret
	.p2align 6

vg_sha3_256_update:
	lea esp, [esp-24]
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [esp+20], eax
	call {vg_keccak_absorb_scratch}
	lea esp, [esp+24]
	ret
	.p2align 6

vg_sha3_256_finalize:
	lea esp, [esp-664]
	mov eax, DWORD PTR [esp+668]
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+672]
	mov DWORD PTR [esp+8], eax
	mov eax, 6
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+16], eax
	call {vg_keccak_pad_scratch}
	mov eax, DWORD PTR [esp+668]
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+676]
	mov DWORD PTR [esp+12], eax
	mov eax, 32
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	call {vg_keccak_squeeze_scratch}
	lea esp, [esp+664]
	ret
	.p2align 6

vg_sha3_384_update:
	lea esp, [esp-24]
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [esp], eax
	mov eax, 104
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [esp+20], eax
	call {vg_keccak_absorb_scratch}
	lea esp, [esp+24]
	ret
	.p2align 6

vg_sha3_384_finalize:
	lea esp, [esp-664]
	mov eax, DWORD PTR [esp+668]
	mov DWORD PTR [esp], eax
	mov eax, 104
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+672]
	mov DWORD PTR [esp+8], eax
	mov eax, 6
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+16], eax
	call {vg_keccak_pad_scratch}
	mov eax, DWORD PTR [esp+668]
	mov DWORD PTR [esp], eax
	mov eax, 104
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+676]
	mov DWORD PTR [esp+12], eax
	mov eax, 48
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	call {vg_keccak_squeeze_scratch}
	lea esp, [esp+664]
	ret
	.p2align 6

vg_sha3_512_update:
	lea esp, [esp-24]
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [esp], eax
	mov eax, 72
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [esp+20], eax
	call {vg_keccak_absorb_scratch}
	lea esp, [esp+24]
	ret
	.p2align 6

vg_sha3_512_finalize:
	lea esp, [esp-664]
	mov eax, DWORD PTR [esp+668]
	mov DWORD PTR [esp], eax
	mov eax, 72
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+672]
	mov DWORD PTR [esp+8], eax
	mov eax, 6
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+16], eax
	call {vg_keccak_pad_scratch}
	mov eax, DWORD PTR [esp+668]
	mov DWORD PTR [esp], eax
	mov eax, 72
	mov DWORD PTR [esp+4], eax
	mov eax, 0
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+676]
	mov DWORD PTR [esp+12], eax
	mov eax, 64
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	call {vg_keccak_squeeze_scratch}
	lea esp, [esp+664]
	ret
	.p2align 6

vg_shake128_update:
	lea esp, [esp-24]
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [esp], eax
	mov eax, 168
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [esp+20], eax
	call {vg_keccak_absorb_scratch}
	lea esp, [esp+24]
	ret
	.p2align 6

vg_shake128_finalize:
	lea esp, [esp-660]
	mov eax, DWORD PTR [esp+664]
	mov DWORD PTR [esp], eax
	mov eax, 168
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+668]
	mov DWORD PTR [esp+8], eax
	mov eax, 31
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	call {vg_keccak_pad_scratch}
	lea esp, [esp+660]
	ret
	.p2align 6

vg_shake128_squeeze:
	lea esp, [esp-664]
	mov eax, DWORD PTR [esp+668]
	mov DWORD PTR [esp], eax
	mov eax, 168
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+672]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+676]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+680]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	call {vg_keccak_squeeze_scratch}
	lea esp, [esp+664]
	ret
	.p2align 6

vg_shake256_finalize:
	lea esp, [esp-660]
	mov eax, DWORD PTR [esp+664]
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+668]
	mov DWORD PTR [esp+8], eax
	mov eax, 31
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	call {vg_keccak_pad_scratch}
	lea esp, [esp+660]
	ret
	.p2align 6

vg_shake256_squeeze:
	lea esp, [esp-664]
	mov eax, DWORD PTR [esp+668]
	mov DWORD PTR [esp], eax
	mov eax, 136
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+672]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+676]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+680]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	call {vg_keccak_squeeze_scratch}
	lea esp, [esp+664]
	ret
	.p2align 6
