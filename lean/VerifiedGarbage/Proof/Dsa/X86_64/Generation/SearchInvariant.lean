module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchSemantics
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchLoop
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchStable
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Generation.Memory

/-! # The p-search invariant retains its exact specification result -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def SearchOutcome (p : SearchPlan) (res : Option (Option Nat × List Byte))
    (W : Nat → BitVec 64) (used : Nat) (t : State) : Prop :=
  (W 19 = BitVec.ofNat 64 0 ∧ res = none) ∨
  (W 19 = BitVec.ofNat 64 1 ∧ ∃ value,
    res = some (some value, p.attempt.rand.drop used) ∧
    Spec.Rsa.bytesAt t.mem (off (p.attempt.construct.hash.W 5) Impl.Dsa.Generation.Layout.p) p.attempt.construct.len =
      Spec.Dsa.encodeBE p.attempt.construct.len value ∧
    Spec.Rsa.bytesAt t.mem (off (p.attempt.construct.hash.W 5) exponent) p.attempt.construct.len =
      Spec.Dsa.encodeBE p.attempt.construct.len ((value - 1) / Spec.Rsa.os2ip p.attempt.construct.qb)) ∨
  (W 19 = BitVec.ofNat 64 3 ∧ res = some (none, p.attempt.rand.drop used))

def SearchInvariant (p : SearchPlan) (res : Option (Option Nat × List Byte)) (s : State)
    (counter : Nat) (t : State) : Prop :=
  ∃ W used, SearchMemory p W t ∧ used ≤ p.attempt.rand.length ∧ W 16 = BitVec.ofNat 64 used ∧
    (0 < counter → W 19 = BitVec.ofNat 64 3) ∧ res = p.remaining counter used ∧
    Frame (searchWrites p.attempt p.C) s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr

def SearchFinished (p : SearchPlan) (res : Option (Option Nat × List Byte)) (s t : State) : Prop :=
  ∃ W used, SearchMemory p W t ∧ used ≤ p.attempt.rand.length ∧ W 16 = BitVec.ofNat 64 used ∧
    SearchOutcome p res W used t ∧ Frame (searchWrites p.attempt p.C) s.mem t.mem ∧
    t.rd = s.rd ∧ t.wr = s.wr

theorem controller_frame {C : Addr} {m m' : Mem} (hf : Outside C 0 24 m m') : Frame [⟨C, 24⟩] m m' := by
  intro a ha
  apply hf a
  right
  have hn := ha ⟨C, 24⟩ (by simp)
  change ¬ ofs C a < 24 at hn
  omega

theorem searchInvariant_stable (p : SearchPlan) (res : Option (Option Nat × List Byte)) (s : State) (c : Nat) :
    SearchPayload p.C (SearchInvariant p res s c) := by
  intro u t h hf hk
  obtain ⟨W, used, hm, hu, h16, h19, hr, ff, rd, wr⟩ := h
  exact ⟨W, used, SearchMemory.stable hm hf hk, hu, h16, h19, hr,
    ff.trans ((controller_frame hf).mono (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl; simp [searchWrites])), hk.2.1.trans rd, hk.2.2.trans wr⟩

theorem searchFinished_stable (p : SearchPlan) (res : Option (Option Nat × List Byte)) (s : State) :
    SearchPayload p.C (SearchFinished p res s) := by
  intro u t h hf hk
  obtain ⟨W, used, hm, hu, h16, ho, ff, rd, wr⟩ := h
  refine ⟨W, used, SearchMemory.stable hm hf hk, hu, h16, ?_,
    ff.trans ((controller_frame hf).mono (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl; simp [searchWrites])), hk.2.1.trans rd, hk.2.2.trans wr⟩
  rcases ho with ho | ⟨h19, value, hr, hp, he⟩ | ho
  · exact Or.inl ho
  · refine Or.inr (Or.inl ⟨h19, value, hr, ?_, ?_⟩)
    · rw [VG.Proof.Dsa.Generation.frame_bytesAt (controller_frame hf) (by
        intro r hr; rcases List.mem_singleton.mp hr with rfl; exact p.pControl)
        (by rcases p.attempt.construct.width with hh | hh | hh <;> omega), hp]
    · rw [VG.Proof.Dsa.Generation.frame_bytesAt (controller_frame hf) (by
        intro r hr; rcases List.mem_singleton.mp hr with rfl; exact p.exponentControl)
        (by rcases p.attempt.construct.width with hh | hh | hh <;> omega), he]
  · exact Or.inr (Or.inr ho)

theorem searchInvariant_done {p : SearchPlan} {res : Option (Option Nat × List Byte)} {s t : State}
    (h : SearchInvariant p res s (32 * p.attempt.construct.len) t) : SearchFinished p res s t := by
  obtain ⟨W, used, hm, hu, h16, h19, hr, ff, rd, wr⟩ := h
  refine ⟨W, used, hm, hu, h16, Or.inr (Or.inr ⟨h19 ?_, ?_⟩), ff, rd, wr⟩
  · rcases p.attempt.construct.width with hh | hh | hh <;> omega
  · exact hr.trans (p.remaining_done used)

end VG.Proof.Dsa.X86_64.Generation
