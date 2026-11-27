module

public import VerifiedGarbage.Impl.Ed25519.X86.CommonMemory
public import VerifiedGarbage.Spec.Ed25519

/-! Scalar reduction modulo the group's order `L`, on eight 32-bit limbs in scratch.

`scalarEngine` reduces the 512 bits `x` at byte 128 by Barrett's method with words of 32 bits: for
`μ = ⌊2⁵¹² / L⌋` (nine words), `q₁ = ⌊x / 2²²⁴⌋` (the input's words 7 to 15) and
`q₃ = ⌊q₁ μ / 2²⁸⁸⌋`, the difference `x - q₃ L` is below `3 L`, so its low 256 bits are the whole
of it: the product `q₁ μ` (`scalarQTerms`, 18 columns at `scalarQ`), the low eight words of `q₃ L`
(`scalarPTerms`, at `scalarP`; the words of `L` that are zero have no term), their difference from
`x`'s (`scalarDiffTerms`, into `scalarR`), and two masked subtractions of `L` (`scalarCondSub`). The
code is a straight line: every address is the working space's plus a constant. -/

@[expose] public section

namespace VG.Impl.Ed25519.X86
open VG.X86 VG.Impl.X25519.X86

def scalarR : Nat := 64

def scalarK (k : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((2 ^ 256 - VG.Spec.Ed25519.L) / 2 ^ (32 * k))

def scalarSubtract : List Instr := zeroAcc ++
  cols T 8 (fun k => [.addM (scalarR + 4 * k), .addI (scalarK k)])

def scalarMask : List Instr := [.mov .ecx (.imm 0), .alu .sub .ecx (.reg .ebx)]

def scalarSelect : List Instr := (List.range 8).flatMap fun k =>
  [.mov .eax (.mem (sc (scalarR + 4 * k))), .mov .edx (.mem (sc (T + 4 * k))),
    .alu .xor .edx (.reg .eax), .alu .and .edx (.reg .ecx),
    .alu .xor .eax (.reg .edx), .store (sc (scalarR + 4 * k)) .eax]

/-- `L` subtracted from `scalarR` if it is not below it. -/
def scalarCondSub : List Instr := scalarSubtract ++ scalarMask ++ scalarSelect

/-- Word `k` of `μ = ⌊2⁵¹² / L⌋`. -/
def scalarMu (k : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (2 ^ 256 * 2 ^ 256 / VG.Spec.Ed25519.L / 2 ^ (32 * k))

/-- Word `k` of `L`. -/
def scalarL (k : Nat) : BitVec 32 := BitVec.ofNat 32 (VG.Spec.Ed25519.L / 2 ^ (32 * k))

/-- Byte of the workspace holding the 18 words of `q₁ μ`. -/
def scalarQ : Nat := 384

/-- Byte of the workspace holding the low eight words of `q₃ L`. -/
def scalarP : Nat := 480

/-- Column `k` of `q₁ μ`: `q₁`'s word `i` is the input's word `7 + i`. -/
def scalarQTerms (k : Nat) : List Term :=
  ((List.range 9).filter fun i => i ≤ k && k - i < 9).map fun i => .mulI (156 + 4 * i) (scalarMu (k - i))

/-- Column `k < 8` of `q₃ L`: `q₃`'s word `i` is word `9 + i` of `q₁ μ`, and `L`'s words 4, 5 and 6
are zero. -/
def scalarPTerms (k : Nat) : List Term :=
  ((List.range 8).filter fun i => i ≤ k && (k - i < 4 || k - i == 7)).map fun i =>
    .mulI (scalarQ + 36 + 4 * i) (scalarL (k - i))

/-- Column `k` of `x - q₃ L` modulo `2²⁵⁶`: `x`'s word, the complement of `q₃ L`'s, and one. -/
def scalarDiffTerms (k : Nat) : List Term :=
  [.addM (128 + 4 * k), .addNot (scalarP + 4 * k)] ++ if k = 0 then [.addI 1] else []

/-- `scalarR` = the 512 bits at byte 128 modulo `L`. -/
def scalarEngine : Prog isa :=
  .block (zeroAcc ++ cols scalarQ 18 scalarQTerms ++ zeroAcc ++ cols scalarP 8 scalarPTerms ++
    zeroAcc ++ cols scalarR 8 scalarDiffTerms ++ scalarCondSub ++ scalarCondSub)

def scalarReduce : Prog isa :=
  .seq (.block (abiSave 2 ++ ([.mov .esi (.mem (at_ .esp 8))] : List Instr) ++ copyWords 128 16))
    (.seq scalarEngine (.block (finishWords scalarR)))
end VG.Impl.Ed25519.X86
