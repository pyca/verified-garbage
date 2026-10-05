import VerifiedGarbage.Impl.Ecdsa.X86
import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Impl.Ecdsa.Rfc6979.X86

/-!
# Deterministic ECDSA on x86 (32-bit): the curve

What the proof needs of the curve (`RfcCurve`), as on x86-64
(`Proof/Ecdsa/Rfc6979/X86_64/Curve.lean`): the code of
`vg_ecdsa_<curve>_sign` for curves of `n` 64-bit words
(`Impl.Ecdsa.X86.Cfg`, `n` 4 or 6), the instance of ECDSA it is, that the
order `n` of its base point has exactly `64 n` bits and `2^(64 n) < 2 n` (so
that `bits2octets` is one conditional subtraction), and what is proven of the
code: that it meets the contract the proof of each curve is written against
(`coreK`: P-256's `signX86` and P-384's at the curve's sizes), in constant
time, that it never writes `esp` and uses no stack, and the taint check of
the block computing `bits2octets`, which holds `n`'s words as immediates.
Each curve's file builds one, so that the heavy algebra of its proof stays
out of the modules generic over the curve and the hash function.
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 Spec.Weierstrass Spec.Ecdsa

/-- The signature with `k` of the arguments, on the curve `E`, as the
specification computes it. -/
abbrev coreSigOf (E : Impl.Ecdsa.X86.Cfg) (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith E.C (ofBytes (bytesAt m d (8 * E.n))) (hashToInt E.C (bytesAt m digest (8 * E.n)))
    (ofBytes (bytesAt m k (8 * E.n)))

/-- The contract of `vg_ecdsa_<curve>_sign` on the curve `E`, as each
curve's proof states it (`Proof.Ecdsa.X86.signX86` for P-256). -/
def coreK (E : Impl.Ecdsa.X86.Cfg) : Contract X86.isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 16 * E.n⟩
    let d : Region := ⟨(arg s 1).setWidth 64, 8 * E.n⟩
    let digest : Region := ⟨(arg s 2).setWidth 64, 8 * E.n⟩
    let k : Region := ⟨(arg s 3).setWidth 64, 8 * E.n⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [d, digest, k, args] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint k ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      args.Disjoint out ∧ args.Disjoint scratch ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 16 * E.n ≤ 2 ^ 32 ∧ (arg s 1).toNat + 8 * E.n ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 8 * E.n ≤ 2 ^ 32 ∧ (arg s 3).toNat + 8 * E.n ≤ 2 ^ 32 ∧
      (arg s 4).toNat + 8192 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s s' :=
    match coreSigOf E s.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64) ((arg s 3).setWidth 64) with
    | some rs => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 1 ∧
      bytesAt s'.mem ((arg s 0).setWidth 64) (16 * E.n) = encode E.C rs
    | none => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 0 ∧
      bytesAt s'.mem ((arg s 0).setWidth 64) (16 * E.n) = List.replicate (16 * E.n) 0
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧
    arg s₁ 2 = arg s₂ 2 ∧ arg s₁ 3 = arg s₂ 3 ∧ arg s₁ 4 = arg s₂ 4

/-- The code's blocks that depend on neither the hash function nor the
functions it calls, for scalars of `E`. -/
def cfgC (E : Impl.Ecdsa.X86.Cfg) : Impl.Ecdsa.Rfc6979.X86.Cfg where
  F := ⟨⟨0, 0, 0, 0, 0, "", .block [], "", .block [], "", .block []⟩, 0, "", .block [], "", .block [], "",
    .block []⟩
  w := 2 * E.n
  n := E.C.n
  tries := 8
  coreN := ""
  coreC := .block []

/-- A curve, for RFC 6979 on x86. -/
structure RfcCurve where
  /-- The curve, as the code of `vg_ecdsa_<curve>_sign` has it. -/
  E : Impl.Ecdsa.X86.Cfg
  /-- The instance of ECDSA. -/
  inst : Spec.Ecdsa.Instance
  curve : inst.curve = E.C
  /-- Scalars of 4 or 6 64-bit words. -/
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
  /-- It never writes `esp`, and uses no stack. -/
  coreNs : NoSp coreC
  coreStack : stackUse coreC = 0
  /-- `bits2octets` and the initial `K` and `V` address memory only from
  `esp` and `esi` (the taint analysis, of the block for `n`'s words). -/
  reduceT : ∃ hc, (VG.Taint.check taint (τr [.esp, .esi])
    (.block ((cfgC E).reduce ++ Impl.Ecdsa.Rfc6979.X86.Cfg.initKV)) hc).isSome = true

theorem RfcCurve.n4 (R : RfcCurve) : 4 ≤ R.E.n := by rcases R.n46 with h | h <;> omega

theorem RfcCurve.n6 (R : RfcCurve) : R.E.n ≤ 6 := by rcases R.n46 with h | h <;> omega

end VG.Proof.Ecdsa.Rfc6979.X86
