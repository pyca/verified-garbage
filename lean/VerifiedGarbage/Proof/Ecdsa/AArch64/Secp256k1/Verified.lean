module

import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Main
import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Config
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Lit
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.AArch64
public import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Main
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Config
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Lit
meta import VerifiedGarbage.Impl.Ecdsa.Secp256k1.AArch64
public import VerifiedGarbage.Spec.Ecdsa.Secp256k1
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ecdsa.Secp256k1
meta import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Contract

/-! ### `Ecdsa.AArch64.Secp256k1.Contract`, which this module and modules that import it used -/

section

/-!
# ECDSA over secp256k1 on AArch64: the contract the proof is written against

The facts of `Proof.Ecdsa.Instance.signContract Spec.Ecdsa.Secp256k1.inst` for AArch64, by name:
`vg_ecdsa_secp256k1_sign(out = x0, d = x1, digest = x2, k = x3, scratch = x4)`,
the result in `w0`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.Secp256k1

open VG VG.AArch64 Spec.Weierstrass Spec.Ecdsa

/-- The signature of the arguments, as the specification computes it. -/
abbrev sig (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith Spec.Secp256k1.curve (ofBytes (bytesAt m d 32)) (hashToInt Spec.Secp256k1.curve (bytesAt m digest 32))
    (ofBytes (bytesAt m k 32))

def signAArch64 : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 64⟩
    let d : Region := ⟨s.gpr .x1, 32⟩
    let digest : Region := ⟨s.gpr .x2, 32⟩
    let k : Region := ⟨s.gpr .x3, 32⟩
    let scratch : Region := ⟨s.gpr .x4, 8192⟩
    s.rd = [d, digest, k] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint k ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      (s.gpr .x0).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match sig s.mem (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) with
    | some rs => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x0) 64 = encode Spec.Secp256k1.curve rs
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .x0) 64 = List.replicate 64 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

end VG.Proof.Ecdsa.AArch64.Secp256k1

end

end

/-! # secp256k1 signing on AArch64: correctness and constant time -/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.Secp256k1

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Weierstrass.AArch64

theorem setup_of {s : State} (h : signAArch64.pre s) : SetupPre secp256k1 s := by
  obtain ⟨hr, hw, _, _, _, _, hd, he, hk, _, hf⟩ := h
  exact ⟨by rw [hw]; simp,
    inRegions_words (by rw [show secp256k1.C.len = 32 from rfl, hr]; simp) (by decide),
    inRegions_words (by rw [show secp256k1.C.len = 32 from rfl, hr]; simp) (by decide),
    inRegions_words (by rw [show secp256k1.C.len = 32 from rfl, hr]; simp) (by decide), hd, he, hk, hf⟩

theorem output_of {s : State} (h : signAArch64.pre s) : SignOutput secp256k1 s :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.2.2.2.2.2.2.1⟩

theorem sign_a64 (hL : Weierstrass.Law Spec.Secp256k1.curve) (hI : InvSounds)
    (s : State) (hs : signAArch64.pre s) :
    ∃ t s', Exec isa signSecp256k1 s t s' ∧ abiPreserved s s' ∧ signAArch64.post s s' := by
  have hn : CallsKeep signSecp256k1 := by lit_decide
  have hu : KeepsUntouched signSecp256k1 := by lit_decide
  have hv : signSecp256k1.allInstrs keepsV = true := by lit_decide
  obtain ⟨t, s', he, hsv, hpost⟩ := sign_ok (secp256k1_ok hI) hL (setup_of hs) (output_of hs)
  exact ⟨t, s', he, abiPreserved_of he hn hu hv hsv, hpost⟩

theorem sign_ct : ConstantTime isa signAArch64.pre signAArch64.pub signSecp256k1 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun _ _ _ _ ⟨h0, h1, h2, h3, h4, hsp⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact h4⟩) (by taint_decide)

end VG.Proof.Ecdsa.AArch64.Secp256k1
