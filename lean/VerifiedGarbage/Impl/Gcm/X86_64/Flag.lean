module

public import VerifiedGarbage.TCB.X86_64.Isa
public import VerifiedGarbage.TCB.Code

/-!
# The prepared key context's flag, on x86-64

A prepared key context of 1032 bytes holds, at byte 1024, a word that is 1
when its powers are absent. `onFlag c₁ c₂` reads it and runs `c₁` if it is
not 1 (the powers are there) and `c₂` if it is (the code that reads only the
key context).
-/

@[expose] public section

namespace VG.Impl.Gcm.X86_64.Flag

open VG.X86_64

/-- The flag word's offset in the prepared key context. -/
def flagOff : Nat := 1024

/-- `mov rax, [rdi + 1024]; cmp rax, 1`. -/
def testFlag : List Instr :=
  [.mov .rax (.mem { base := .rdi, disp := flagOff }), .alu .cmp .rax (.imm 1)]

/-- `c₁` where the flag word of the key context at `rdi` is not 1, `c₂` where
it is. -/
def onFlag (c₁ c₂ : Prog isa) : Prog isa :=
  .seq (.block testFlag) (Code.iteCold .ne c₁ c₂)

/-- `mov rax, v; mov [rdi + 1024], rax`: sets the flag word to `v`. -/
def storeFlag (v : BitVec 32) : List Instr :=
  [.mov .rax (.imm v), .store { base := .rdi, disp := flagOff } .rax]

/-- `vg_aes_gcm_prepare` computing no powers: the flag word says they are
absent. -/
def prepareAbsent : Prog isa :=
  .block (storeFlag 1)

/-- `vg_aes_gcm_prepare` computing the powers with `c`, after setting the flag
word to 0, so that the functions on the context read them. -/
def prepareFlagged (c : Prog isa) : Prog isa :=
  .seq (.block (storeFlag 0)) c

/-- The bytes each store of `zeroStores avx` zeroes: 32 from `ymm0` with AVX,
16 from `xmm0` without. -/
def storeBytes (avx : Bool) : Nat := if avx then 32 else 16

/-- One store of `storeBytes avx` zero bytes at `rdi + d`: `vmovdqu` from
`ymm0` with AVX, `movdqu` from `xmm0` without. -/
def zeroStore (avx : Bool) (d : Nat) : Instr :=
  if avx then .vmovdquStore .l256 { base := .rdi, disp := d } .xmm0
  else .movdquStore { base := .rdi, disp := d } .xmm0

/-- `zeroStore avx` at `rdi + storeBytes avx * i` for `i` from `k` to
`k + n - 1`. -/
def zeroStores (avx : Bool) (k : Nat) : Nat → List Instr
  | 0 => []
  | n + 1 => zeroStore avx (storeBytes avx * k) :: zeroStores avx (k + 1) n

/-- Zeroes the register `zeroStore avx` stores from: `vpxor xmm0, xmm0, xmm0`
with AVX (whose `VEX.128` form zeroes bits 255:128 too), `pxor xmm0, xmm0`
without. -/
def zeroReg (avx : Bool) : Instr :=
  if avx then .vop (.vbin .vpxor .l128 .xmm0 .xmm0 .xmm0) else .xop (.bin .pxor .xmm0 .xmm0)

/-- Zeroes the `bytes` (a multiple of `storeBytes avx`) bytes at `rdi`, and
with AVX clears the upper halves of the vector registers after
(`vzeroupper`), for the SSE code the caller may run next. -/
def zeroBlocks (avx : Bool) (bytes : Nat) : List Instr :=
  zeroReg avx :: zeroStores avx 0 (bytes / storeBytes avx) ++ if avx then [.vop .vzeroupper] else []

/-- `vg_aes_gcm_wipe_prepared`: zeroes the 1024 bytes of the key context and
the powers if they are there, and the 256 bytes of the key context if they
are absent, all that `vg_aes_gcm_init` and `vg_aes_gcm_prepare` wrote but the
flag word; with AVX if `avx`. -/
def wipe (avx : Bool) : Prog isa :=
  onFlag (.block (zeroBlocks avx 1024)) (.block (zeroBlocks avx 256))

end VG.Impl.Gcm.X86_64.Flag
