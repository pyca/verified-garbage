module

import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Main
import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Config
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Lit
public import VerifiedGarbage.Impl.Ecdsa.P192.AArch64
public import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Main
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Config
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Lit
meta import VerifiedGarbage.Impl.Ecdsa.P192.AArch64
public import VerifiedGarbage.Spec.Ecdsa.P192
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ecdsa.P192
meta import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Contract

/-! ### `Ecdsa.AArch64.P192.Contract`, which this module and modules that import it used -/

section

/-!
# ECDSA over p192 on AArch64: the contract the proof is written against

The facts of `Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P192.inst` for AArch64, by name:
`vg_ecdsa_p192_sign(out = x0, d = x1, digest = x2, k = x3, scratch = x4)`,
the result in `w0`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.P192

open VG VG.AArch64 Spec.Weierstrass Spec.Ecdsa

/-- The signature of the arguments, as the specification computes it. -/
abbrev sig (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith Spec.P192.curve (ofBytes (bytesAt m d 24)) (hashToInt Spec.P192.curve (bytesAt m digest 24))
    (ofBytes (bytesAt m k 24))

def signAArch64 : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 48⟩
    let d : Region := ⟨s.gpr .x1, 24⟩
    let digest : Region := ⟨s.gpr .x2, 24⟩
    let k : Region := ⟨s.gpr .x3, 24⟩
    let scratch : Region := ⟨s.gpr .x4, 8192⟩
    s.rd = [d, digest, k] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint k ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      (s.gpr .x0).toNat + 48 ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match sig s.mem (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) with
    | some rs => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x0) 48 = encode Spec.P192.curve rs
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .x0) 48 = List.replicate 48 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

end VG.Proof.Ecdsa.AArch64.P192

end

end

/-! # p192 signing on AArch64: correctness and constant time -/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.P192

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Weierstrass.AArch64

theorem setup_of {s : State} (h : signAArch64.pre s) : SetupPre p192 s := by
  obtain ⟨hr, hw, _, _, _, _, hd, he, hk, _, hf⟩ := h
  exact ⟨by rw [hw]; simp,
    inRegions_words (by rw [show p192.C.len = 24 from rfl, hr]; simp) (by decide),
    inRegions_words (by rw [show p192.C.len = 24 from rfl, hr]; simp) (by decide),
    inRegions_words (by rw [show p192.C.len = 24 from rfl, hr]; simp) (by decide), hd, he, hk, hf⟩

theorem output_of {s : State} (h : signAArch64.pre s) : SignOutput p192 s :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.2.2.2.2.2.2.1⟩

theorem sign_a64 (hL : Weierstrass.Law Spec.P192.curve) (hI : InvSounds)
    (s : State) (hs : signAArch64.pre s) :
    ∃ t s', Exec isa signP192 s t s' ∧ abiPreserved s s' ∧ signAArch64.post s s' := by
  have hn : CallsKeep signP192 := by lit_decide
  have hu : KeepsUntouched signP192 := by lit_decide
  have hv : signP192.allInstrs keepsV = true := by lit_decide
  obtain ⟨t, s', he, hsv, hpost⟩ := sign_ok (p192_ok hI) hL (setup_of hs) (output_of hs)
  exact ⟨t, s', he, abiPreserved_of he hn hu hv hsv, hpost⟩

theorem sign_ct : ConstantTime isa signAArch64.pre signAArch64.pub signP192 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun _ _ _ _ ⟨h0, h1, h2, h3, h4, hsp⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact h4⟩) (by taint_decide)

end VG.Proof.Ecdsa.AArch64.P192
