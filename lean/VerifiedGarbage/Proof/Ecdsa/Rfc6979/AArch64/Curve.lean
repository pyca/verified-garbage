import VerifiedGarbage.Impl.Ecdsa.AArch64
import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Impl.Ecdsa.Rfc6979.AArch64
import VerifiedGarbage.Impl.Sha256.AArch64.Stream
import VerifiedGarbage.Impl.Pbkdf2.AArch64

/-!
# Deterministic ECDSA on AArch64: the curve

What the proof needs of the curve (`RfcCurve`), as on x86-64
(`Proof/Ecdsa/Rfc6979/X86_64/Curve.lean`): the code of
`vg_ecdsa_<curve>_sign` for curves of `n` words (`Impl.Ecdsa.AArch64.Cfg`,
`n` 4 or 6), the instance of ECDSA it is, that the order `n` of its base
point has exactly `64 n` bits and `2^(64 n) < 2 n` (so that `bits2octets` is
one conditional subtraction), and what is proven of the code: that it meets
the contract the proof of each curve is written against (`coreK`: P-256's
`signAArch64` and P-384's at the curve's sizes), in constant time, that it
pushes no frame and writes no callee-saved SIMD register, and the taint
check of the block computing `bits2octets`, which holds `n`'s words as
immediates. Each curve's file builds one, so that the heavy algebra of its
proof stays out of the modules generic over the curve and the hash function.
-/

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 Spec.Weierstrass Spec.Ecdsa

/-- The signature with `k` of the arguments, on the curve `E`, as the
specification computes it. -/
abbrev coreSigOf (E : Impl.Ecdsa.AArch64.Cfg) (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith E.C (ofBytes (bytesAt m d (8 * E.n))) (hashToInt E.C (bytesAt m digest (8 * E.n)))
    (ofBytes (bytesAt m k (8 * E.n)))

/-- The contract of `vg_ecdsa_<curve>_sign` on the curve `E`, as each
curve's proof states it (`Proof.Ecdsa.AArch64.signAArch64` for P-256). -/
def coreK (E : Impl.Ecdsa.AArch64.Cfg) : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 16 * E.n⟩
    let d : Region := ⟨s.gpr .x1, 8 * E.n⟩
    let digest : Region := ⟨s.gpr .x2, 8 * E.n⟩
    let k : Region := ⟨s.gpr .x3, 8 * E.n⟩
    let scratch : Region := ⟨s.gpr .x4, 8192⟩
    s.rd = [d, digest, k] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint k ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      (s.gpr .x0).toNat + 16 * E.n ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match coreSigOf E s.mem (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) with
    | some rs => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x0) (16 * E.n) = encode E.C rs
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .x0) (16 * E.n) =
        List.replicate (16 * E.n) 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- The code's blocks that depend on neither the hash function nor the
compression function, for scalars of `E`. -/
def cfgC (E : Impl.Ecdsa.AArch64.Cfg) : Impl.Ecdsa.Rfc6979.AArch64.Cfg where
  H := ⟨Impl.Pbkdf2.AArch64.ofMd Impl.Sha256.AArch64.Stream.params, 32, 104, "", .block [], "", .block [], "",
    .block [], "", .block [], "", "", ""⟩
  w := E.n
  n := E.C.n
  tries := 8
  coreN := ""
  coreC := .block []

/-- A curve, for RFC 6979 on AArch64. -/
structure RfcCurve where
  /-- The curve, as the code of `vg_ecdsa_<curve>_sign` has it. -/
  E : Impl.Ecdsa.AArch64.Cfg
  /-- The instance of ECDSA. -/
  inst : Spec.Ecdsa.Instance
  curve : inst.curve = E.C
  /-- Scalars of 4 or 6 words. -/
  n46 : E.n = 4 ∨ E.n = 6
  len : E.C.len = 8 * E.n
  /-- `n` has exactly `64 n` bits, and `2^(64 n) < 2 n`. -/
  nBits : nBits E.C = 64 * E.n
  n_lt : E.C.n < 2 ^ (64 * E.n)
  lt_2n : 2 ^ (64 * E.n) < 2 * E.C.n
  /-- `vg_ecdsa_<curve>_sign`, its name, and that it is correct and constant time. -/
  coreN : String
  coreC : Prog isa
  coreX : ∀ s, (coreK E).pre s → ∃ t s', Exec isa coreC s t s' ∧ abiPreserved s s' ∧ (coreK E).post s s'
  coreCT : ConstantTime isa (coreK E).pre (coreK E).pub coreC
  /-- It pushes no frame, and none of its instructions writes a callee-saved SIMD register. -/
  coreNoFrames : coreC.noFrames = true
  coreKeepsV : coreC.allInstrs keepsV = true
  /-- `bits2octets` and the initial `K` and `V` address memory only from
  `sp` and `x1` (the taint analysis, of the block for `n`'s words), and
  write no callee-saved SIMD register. -/
  reduceT : ∃ hc, (taint.check (Taint.ofRegs [.x1])
    (.block ((cfgC E).reduce ++ Impl.Ecdsa.Rfc6979.AArch64.Cfg.initKV)) hc).isSome = true
  reduceKeepsV : (Code.block ((cfgC E).reduce ++ Impl.Ecdsa.Rfc6979.AArch64.Cfg.initKV) : Prog isa).allInstrs
    keepsV = true

theorem RfcCurve.n4 (R : RfcCurve) : 4 ≤ R.E.n := by rcases R.n46 with h | h <;> omega

theorem RfcCurve.n6 (R : RfcCurve) : R.E.n ≤ 6 := by rcases R.n46 with h | h <;> omega

end VG.Proof.Ecdsa.Rfc6979.AArch64
