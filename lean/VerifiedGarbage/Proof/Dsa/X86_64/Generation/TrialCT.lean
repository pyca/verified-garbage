module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HeaderCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HeaderCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeTrial
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeTrial
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawCopyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawCopyCT
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMs
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMs

/-! # Trial division reads public workspace metadata in the generation arena -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaKeyGen.X86_64

structure PrimeCallPublic where
  draw : DrawPublic
  arena : Addr
  wr : List Region
  layout : PrimeHeaderLayout arena wr
  base : draw.prime.B = off arena 28672
  width : draw.prime.w ≤ 48
  tab : slot draw.prime.w aTab + 2048 ≤ draw.prime.Z
  large : 8161 < draw.prime.N
  policy : 1024 < Spec.Dsa.bitLength draw.prime.N ↔ 16 < draw.prime.w

def PrimeCallBefore (len drawBytes : Nat) (p : PrimeCallPublic) (s : State) : Prop :=
  (∃ mi, PrimeInput p.draw.prime mi p.draw.used s) ∧ s.wr = p.wr ∧
    p.draw.used ≤ p.draw.prime.rand.length ∧ p.draw.prime.len = len ∧ p.draw.prime.drawBytes = drawBytes

theorem primeTrial_ct (len drawBytes : Nat) : RelCT isa (Two (PrimeCallBefore len drawBytes))
    (seqs trial) (fun _ _ => True) := by
  apply primeHeader_ct PrimeCallPublic.arena PrimeCallPublic.wr gS
    (fun p => gvs p.draw.prime.B p.draw.prime.w) [] (by decide) (fun _ => gvs_fst _ _) ?_
    (pins_nil _) (by taint_decide)
  intro p s h
  obtain ⟨mi, hs⟩ := h.1
  exact ⟨p.layout, by rw [← p.base]; exact good_hp hs.good h.2.1⟩

def PrimeCallTested (len drawBytes : Nat) (p : PrimeCallPublic) (s : State) : Prop :=
  PrimeCallBefore len drawBytes p s ∧
    s.zf = some (!Spec.RsaKeyGen.obviouslyComposite (Spec.Dsa.bitLength p.draw.prime.N) p.draw.prime.N)

theorem primeTrial_tested {len drawBytes : Nat} {p : PrimeCallPublic} {s : State}
    (h : PrimeCallBefore len drawBytes p s) :
    WP isa (seqs trial) s (PrimeCallTested len drawBytes p) := by
  obtain ⟨mi, hs⟩ := h.1
  exact WP.mono (primeTrial_ok hs p.width p.tab p.large p.policy) fun _ ⟨hz, ht, _, hk⟩ =>
    ⟨⟨⟨mi, ht⟩, hk.2.2.trans h.2.1, h.2.2⟩, hz⟩

end VG.Proof.Dsa.X86_64.Generation
