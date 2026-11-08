module

public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Layout
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Packed

/-!
# Ed25519 on PPC64LE: scalars modulo `L`

The reduction folds the 64-byte input in a 64-bit word at a time, from the
top, into a remainder in `r8`–`r11` (`wordFold`), as on RISC-V
(`Impl/Ed25519/RISCV64/Scalar.lean`), with PPC64LE's carry: `L = 2^252 + c`
and `c`'s words in `r16` and `r19`. `vg_ed25519_scalar_mul_add` multiplies
first, into 16 limbs, and reduces the 64 bytes of the result.
`vg_ed25519_verify_equation`'s check that `S < L` computes `SR - L` at `SD`
as `SR + (2^256 - 1 - L) + 1`, whose carry out is 1 exactly when `SR ≥ L`
(`scalarCompare`). Every address is a pointer plus a constant or a counter,
and the only branches are on the counters.
-/

@[expose] public section

namespace VG.Impl.Ed25519.PPC64LE
open VG.PPC64LE
open VG.Impl.X25519.PPC64LE (prologue zeroAcc row addSrc)

/-- Word `k` of the complement of `L`, without its final carry-in. -/
def scalarComplement (k : Nat) : Nat := 2 ^ 32 - 1 - Spec.Ed25519.L / 2 ^ (32 * k) % 2 ^ 32

/-- Word `k` of `SR` plus that of the complement, which `lis` and `ori` build
and `rlwinm` zero-extends. -/
def scalarSubtractSrc (k : Nat) : List Instr :=
  [.load .w .r7 .r6 (SR + 4 * k), .lis .r5 (BitVec.ofNat 16 (scalarComplement k / 2 ^ 16)),
    .ori .r5 .r5 (BitVec.ofNat 16 (scalarComplement k)), .rotr .w .r5 .r5 0, .add .r7 .r7 .r5]

/-- Carry-out r8 is zero exactly when the unreduced scalar in SR is below L. -/
def scalarCompare : List Instr := [.li .r8 1] ++ pass .r6 SD scalarSubtractSrc

/-! ## The reduction

Division by `L = 2^252 + c` (`c < 2^125`) a 64-bit word at a time, from the
top: the remainder `r < L` (in `r8`–`r11`) becomes `v = 2^64 r + w` for the
next word `w`, which is `h 2^252 + l` with `h < 2^65`, and `v ≡ l + L - h c`
(mod L) since `2^252 ≡ -c`. With `t = h c < L`, that is `l - t` when `t ≤ l`
and `l + L - t` otherwise: the four-word difference `l - t`, plus `L` under
the mask of its borrow, is `v mod L` (`wordFold`). -/

/-- The low and high words of `c = L - 2^252`. -/
def orderLo : BitVec 64 := 0x5812631a5cf5d3ed
def orderHi : BitVec 64 := 0x14def9dea2f79cd6

/-- `d := v` for a 64-bit constant: the high word with `lis` and `ori`,
shifted up by `sldi`, then the low word with `oris` and `ori`. -/
def movImm64 (d : Reg) (v : BitVec 64) : List Instr :=
  [.lis d (v.extractLsb' 48 16), .ori d d (v.extractLsb' 32 16), .lsl d d 32,
   .oris d d (v.extractLsb' 16 16), .ori d d (v.extractLsb' 0 16)]

/-- The next word, from the top (`r15` counts its bytes down from 64), into `r12`. -/
def scalarLoad : List Instr := [.subi .r15 .r15 8, .add .r7 .r14 .r15, .load .d .r12 .r7 0]

/-- From `r = (r₀, r₁, r₂, r₃)` in `r8`–`r11` and `w` in `r12`: `h₀ = r₂ >> 60 | 2^4 r₃`
(`r3`) and `h₁ = r₃ >> 60` (`r4`), so that `h₀ + 2^64 h₁ = (2^64 r + w) >> 252`; and
`l = (w, r₀, r₁, r₂ mod 2^60)` into `r8`–`r11`. -/
def foldPrep : List Instr :=
  [.lsr .d .r3 .r10 60, .lsl .r4 .r11 4, .logic .or .r3 .r3 .r4, .lsr .d .r4 .r11 60,
    .lsl .r11 .r10 4, .lsr .d .r11 .r11 4, .addi .r10 .r9 0, .addi .r9 .r8 0, .addi .r8 .r12 0]

/-- `t = h₀ c + 2^64 h₁ c`, below `2^190`, into `r5`, `r7`, `r3`. -/
def foldMul : List Instr :=
  [.mul .r5 .r3 .r16, .mulhu .r7 .r3 .r16, .mul .r12 .r3 .r19, .mulhu .r3 .r3 .r19,
    .addc .r7 .r7 .r12, .addze .r3 .r3, .mul .r12 .r4 .r16, .addc .r7 .r7 .r12, .addze .r3 .r3,
    .mul .r12 .r4 .r19, .add .r3 .r3 .r12]

/-- `l - t` into `r8`–`r11`, and the mask of its borrow into `r12`: all ones if it borrows,
zero if not. -/
def foldSub : List Instr :=
  [.subc .r8 .r8 .r5, .sube .r9 .r9 .r7, .sube .r10 .r10 .r3, .li .r12 0, .sube .r11 .r11 .r12,
    .addze .r12 .r12, .subi .r12 .r12 1]

/-- `L` added to `r8`–`r11` under the mask in `r12`. -/
def foldAdd : List Instr :=
  [.logic .and .r3 .r16 .r12, .addc .r8 .r8 .r3, .logic .and .r3 .r19 .r12, .adde .r9 .r9 .r3,
    .addze .r10 .r10, .lsr .d .r3 .r12 63, .lsl .r3 .r3 60, .adde .r11 .r11 .r3]

/-- From the remainder `r < L` in `r8`–`r11` and the next word `w` in `r12`: `v mod L`
for `v = 2^64 r + w`, into `r8`–`r11`. -/
def wordFold : List Instr := foldPrep ++ foldMul ++ foldSub ++ foldAdd

def scalarWord : List Instr := scalarLoad ++ wordFold

def scalarInit : List Instr :=
  [.li .r8 0, .li .r9 0, .li .r10 0, .li .r11 0, .li .r15 64] ++ movImm64 .r16 orderLo ++
    movImm64 .r19 orderHi

/-- The remainder, into `SR`. -/
def scalarStore : List Instr :=
  [.store .d .r8 .r6 SR, .store .d .r9 .r6 (SR + 8), .store .d .r10 .r6 (SR + 16),
    .store .d .r11 .r6 (SR + 24)]

/-- Reduce the 64-byte integer at `r14`, into `SR`. -/
def scalarReduceEngine : Prog isa :=
  .seq (.block scalarInit) (.seq (.loop (.block scalarWord) (.nonzero .d .r15)) (.block scalarStore))

/-! ## Saving the nonvolatile registers -/

/-- The nonvolatile registers the functions change. -/
def savedRegs : List Reg := [.r14, .r15, .r16, .r17, .r18, .r19, .r26, .r27, .r28, .r29, .r30, .r31]

def scalarSave (base : Reg) : List Instr :=
  (List.range 12).map fun i => .store .d (savedRegs.getD i .r14) base (SAVE + 8 * i)

def scalarRestore : List Instr :=
  (List.range 12).map fun i => .load .d (savedRegs.getD i .r14) .r6 (SAVE + 8 * i)

/-! ## `vg_ed25519_scalar_reduce(out = r3, wide = r4, scratch = r5)` -/

def scalarReduceSetup : List Instr :=
  scalarSave .r5 ++ [.addi .r6 .r5 0, .addi .r27 .r3 0, .addi .r14 .r4 0]

def scalarFinish : List Instr := [.addi .r14 .r27 0] ++ packField SR 0 ++ scalarRestore

def scalarReduce : Prog isa :=
  .seq (.block scalarReduceSetup) (.seq scalarReduceEngine (.block scalarFinish))

/-! ## `vg_ed25519_scalar_mul_add(out = r3, r = r4, k = r5, s = r6, scratch = r7)` -/

/-- Exact 256-by-256 multiplication, before any modular reduction. -/
def scalarWideMul (x y : Nat) : Prog isa :=
  .seq (.block (prologue ++ zeroAcc ACC ++ [.addi .r9 .r6 0, .li .r11 8]))
    (.loop (.block (row ACC x y)) (.nonzero .d .r11))

def scalarWideAdd (r : Nat) : List Instr :=
  [.li .r8 0] ++ pass .r6 ACC (addSrc ACC r) ++ pass .r6 (ACC + 32) (ldSrc (ACC + 32))

/-- The packed 512-bit sum occupies bytes 512–575. -/
def scalarPackWide : List Instr :=
  [.addi .r14 .r6 512] ++ packField ACC 0 ++ packField (ACC + 32) 32

def scalarMulAddEngine : Prog isa :=
  .seq (scalarWideMul 96 128) <|
    .seq (.block (scalarWideAdd 64 ++ scalarPackWide)) scalarReduceEngine

def scalarLoadInput (o : Nat) (p : Reg) : List Instr := [.addi .r14 p 0] ++ unpackField o 0

def scalarMulAddArgs : List Instr :=
  scalarSave .r7 ++ [.addi .r18 .r3 0, .addi .r17 .r6 0, .addi .r6 .r7 0] ++
    scalarLoadInput 64 .r4 ++ scalarLoadInput 96 .r5 ++ scalarLoadInput 128 .r17

def scalarMulAddFinish : List Instr := [.addi .r14 .r18 0] ++ packField SR 0 ++ scalarRestore

def scalarMulAdd : Prog isa :=
  .seq (.block scalarMulAddArgs) (.seq scalarMulAddEngine (.block scalarMulAddFinish))

end VG.Impl.Ed25519.PPC64LE
