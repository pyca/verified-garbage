module

public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Layout
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Packed

/-!
# Ed25519 on PPC64LE: scalars modulo `L`

ARMv7's bit-serial reduction (`Impl/Ed25519/Arm/Scalar.lean`) in eight
32-bit limbs: the remainder at `SR` doubled, plus the next bit, then
`SR - L` computed at `SD` as `SR + (2^256 - 1 - L) + 1`, whose carry out is
1 exactly when `SR ≥ L`, and selected with a mask. The bytes are read from
the top, at `r14` (counted by `r15`, the byte in `r16`).
-/

@[expose] public section

namespace VG.Impl.Ed25519.PPC64LE
open VG.PPC64LE
open VG.Impl.X25519.PPC64LE (prologue zeroAcc row addSrc)

/-- Word `k` of the complement of `L`, without its final carry-in. -/
def scalarComplement (k : Nat) : Nat := 2 ^ 32 - 1 - Spec.Ed25519.L / 2 ^ (32 * k) % 2 ^ 32

def scalarDoubleSrc (k : Nat) : List Instr := [.load .w .r7 .r6 (SR + 4 * k), .add .r7 .r7 .r7]

/-- Word `k` of `SR` plus that of the complement, which `lis` and `ori` build
and `rlwinm` zero-extends. -/
def scalarSubtractSrc (k : Nat) : List Instr :=
  [.load .w .r7 .r6 (SR + 4 * k), .lis .r5 (BitVec.ofNat 16 (scalarComplement k / 2 ^ 16)),
    .ori .r5 .r5 (BitVec.ofNat 16 (scalarComplement k)), .rotr .w .r5 .r5 0, .add .r7 .r7 .r5]

/-- Consume bit j of r16, doubling the remainder and subtracting L if
necessary. -/
def scalarBit (j : Nat) : List Instr :=
  [.lsl .r8 .r16 (63 - j), .lsr .d .r8 .r8 63] ++ pass .r6 SR scalarDoubleSrc ++ [.li .r8 1] ++
    pass .r6 SD scalarSubtractSrc ++ [.li .r11 0, .sub .r11 .r11 .r8] ++ cswap SR SD

/-- Carry-out r8 is zero exactly when the unreduced scalar in SR is below L. -/
def scalarCompare : List Instr := [.li .r8 1] ++ pass .r6 SD scalarSubtractSrc

def scalarRead : List Instr := [.subi .r15 .r15 1, .add .r7 .r14 .r15, .lbz .r16 .r7 0]

def scalarByte : List Instr := scalarRead ++ (List.range 8).reverse.flatMap scalarBit

def scalarInit : List Instr := [.li .r7 0] ++ storeN .r7 SR 8 ++ [.li .r15 64]

/-- Read the complete 64-byte integer from r14. -/
def scalarReduceEngine : Prog isa :=
  .seq (.block scalarInit) (.loop (.block scalarByte) (.nonzero .d .r15))

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
