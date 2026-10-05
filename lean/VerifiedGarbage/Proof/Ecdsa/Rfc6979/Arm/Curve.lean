import VerifiedGarbage.Impl.Ecdsa.Arm
import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Layout

/-!
# Deterministic ECDSA on 32-bit ARM: the curve

What the proof needs of the curve (`RfcCurve`), as on x86
(`Proof/Ecdsa/Rfc6979/X86/Curve.lean`): the code of `vg_ecdsa_<curve>_sign`
for curves of `n` 64-bit words (`Impl.Ecdsa.Arm.Cfg`), the instance of
ECDSA it is, its sizes: `n` 4 or 6, the order `n` of its base point of
exactly `64 n` bits and `2^(64 n) < 2 n` (so that `bits2octets` is one
conditional subtraction), or, if `wide` (P-521), `n` 9, scalars of 66 bytes
and the order of 521 bits; and what is proven of the code: that it meets the
contract the proof of each curve is written against (`coreK`: P-256's
`signArm`, P-384's and P-521's at the curve's sizes), in constant time, that
it uses no stack, and, unless `wide`, the taint check of the block computing
`bits2octets`, which holds `n`'s words as immediates. Each curve's file builds one, so that the heavy algebra of
its proof stays out of the modules generic over the curve and the hash
function.
-/

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm Spec.Weierstrass Spec.Ecdsa

/-- The taint analysis's start: the registers `rs` public, the flags not. -/
def τr (rs : List Reg) : VG.Arm.Taint.T := { regs := RegSet.ofList rs, flags := false }

/-- The signature with `k` of the arguments, on the curve `E`, as the
specification computes it. -/
abbrev coreSigOf (E : Impl.Ecdsa.Arm.Cfg) (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith E.C (ofBytes (bytesAt m d E.C.len)) (hashToInt E.C (bytesAt m digest E.C.len))
    (ofBytes (bytesAt m k E.C.len))

/-- The contract of `vg_ecdsa_<curve>_sign` on the curve `E`, as each
curve's proof states it (`Proof.Ecdsa.Arm.signArm` for P-256). -/
def coreK (E : Impl.Ecdsa.Arm.Cfg) : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 2 * E.C.len⟩
    let d : Region := ⟨State.addr (s.gpr .r1), E.C.len⟩
    let digest : Region := ⟨State.addr (s.gpr .r2), E.C.len⟩
    let k : Region := ⟨State.addr (s.gpr .r3), E.C.len⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 8192⟩
    let args : Region := ⟨State.addr s.sp, 4⟩
    s.rd = [d, digest, k, args] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      out.Disjoint args ∧ scratch.Disjoint args ∧
      (s.gpr .r0).toNat + 2 * E.C.len ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + E.C.len ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + E.C.len ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + E.C.len ≤ 2 ^ 32 ∧
      (stackArg s 0).toNat + 8192 ≤ 2 ^ 32 ∧ s.sp.toNat + 4 ≤ 2 ^ 32
  post s s' :=
    match coreSigOf E s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2)) (State.addr (s.gpr .r3)) with
    | some rs => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1 ∧
      bytesAt s'.mem (State.addr (s.gpr .r0)) (2 * E.C.len) = encode E.C rs
    | none => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
      bytesAt s'.mem (State.addr (s.gpr .r0)) (2 * E.C.len) = List.replicate (2 * E.C.len) 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

/-- The code's blocks that depend on neither the hash function nor the
functions it calls, for scalars of `E`. -/
def cfgC (E : Impl.Ecdsa.Arm.Cfg) : Impl.Ecdsa.Rfc6979.Arm.Cfg where
  F := ⟨⟨0, 0, 0, 0, 0, "", .block [], "", .block [], "", .block []⟩, 0, "", .block [], "", .block [], "",
    .block []⟩
  w := 2 * E.n
  n := E.C.n
  tries := 8
  coreN := ""
  coreC := .block []

/-- A curve, for RFC 6979 on 32-bit ARM. -/
structure RfcCurve where
  /-- The curve, as the code of `vg_ecdsa_<curve>_sign` has it. -/
  E : Impl.Ecdsa.Arm.Cfg
  /-- The instance of ECDSA. -/
  inst : Spec.Ecdsa.Instance
  curve : inst.curve = E.C
  /-- Whether the scalars are longer than any hash function's output, so
  that two `V`s make a candidate (`Impl.Ecdsa.Rfc6979.Arm.Cfg.wide`). -/
  wide : Bool
  /-- Scalars of 4 or 6 64-bit words, `8 n` bytes, and `n` of exactly `64 n`
  bits, with `2^(64 n) < 2 n`; or, if `wide`, of 9 words and 66 bytes, and
  `n` of 521 bits. -/
  sizes : if wide then E.n = 9 ∧ E.C.len = 66 ∧ nBits E.C = 521
    else (E.n = 4 ∨ E.n = 6) ∧ E.C.len = 8 * E.n ∧ nBits E.C = 64 * E.n ∧ 2 ^ (64 * E.n) < 2 * E.C.n
  n_lt : E.C.n < 2 ^ (64 * E.n)
  /-- The bits the signature drops from its digest, `8 len - nBits`. -/
  sh : Nat
  sh_eq : E.sh = sh
  /-- `vg_ecdsa_<curve>_sign`, its name, and that it is correct and constant time. -/
  coreN : String
  coreC : Prog isa
  coreX : ∀ s, (coreK E).pre s → ∃ t s', Exec isa coreC s t s' ∧ abiPreserved s s' ∧ (coreK E).post s s'
  coreCT : ConstantTime isa (coreK E).pre (coreK E).pub coreC
  /-- It uses no stack. -/
  coreStack : VG.Arm.FrameStack.armStack coreC = 0
  /-- Unless `wide`, `bits2octets` and the initial `K` and `V` address
  memory only from the registers that hold the pointers (the taint analysis,
  of the block for `n`'s words). -/
  reduceT : wide = false → ∃ hc, (VG.Taint.check taint (τr ptrRegs)
    (.block ((cfgC E).reduce ++ Impl.Ecdsa.Rfc6979.Arm.Cfg.initKV)) hc).isSome = true

namespace RfcCurve

variable (R : RfcCurve)

theorem sizesA (h : R.wide = false) :
    (R.E.n = 4 ∨ R.E.n = 6) ∧ R.E.C.len = 8 * R.E.n ∧ nBits R.E.C = 64 * R.E.n ∧
      2 ^ (64 * R.E.n) < 2 * R.E.C.n := by
  have := R.sizes; rw [h] at this; exact this

theorem sizesW (h : R.wide = true) : R.E.n = 9 ∧ R.E.C.len = 66 ∧ nBits R.E.C = 521 := by
  have := R.sizes; rw [h] at this; exact this

theorem n4 : 4 ≤ R.E.n := by
  cases h : R.wide
  · rcases (R.sizesA h).1 with h | h <;> omega
  · rw [(R.sizesW h).1]; omega

theorem n9 : R.E.n ≤ 9 := by
  cases h : R.wide
  · rcases (R.sizesA h).1 with h | h <;> omega
  · rw [(R.sizesW h).1]

/-- The scalars' bytes fill their words, the last at least in part. -/
theorem len_words : 8 ≤ R.E.C.len ∧ 8 * R.E.n < R.E.C.len + 8 ∧ R.E.C.len ≤ 8 * R.E.n := by
  cases h : R.wide
  · have := R.sizesA h; have := R.n4; omega
  · have := R.sizesW h; omega

/-- `nBits` is within the scalars' last byte, and `sh` the bits beyond it. -/
theorem nBits_len : 8 * R.E.C.len < nBits R.E.C + 8 ∧ nBits R.E.C ≤ 8 * R.E.C.len ∧
    R.sh = 8 * R.E.C.len - nBits R.E.C := by
  rw [← R.sh_eq]
  cases h : R.wide
  · have := R.sizesA h; exact ⟨by omega, by omega, rfl⟩
  · have := R.sizesW h; exact ⟨by omega, by omega, rfl⟩

theorem n_ne : R.E.C.n ≠ 0 := fun h => by
  have h₁ := R.nBits_len; have h₂ := R.len_words
  have : nBits R.E.C = 1 := by show R.E.C.n.log2 + 1 = 1; rw [h]; rfl
  omega

end RfcCurve

end VG.Proof.Ecdsa.Rfc6979.Arm
