module
public import VerifiedGarbage.Impl.Dsa.AArch64.Random
public import VerifiedGarbage.Proof.Bignum.AArch64.Run

import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Termination rule for the sampler's status-controlled loop. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_statusTest_ok {s : State} {B : Addr} {status : BitVec 64}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hv : word s.mem B Random.oStatus = status) :
    WP isa (.block (Random.statusTest 4)) s fun t =>
      (t.gpr .x4 == 0#64) = (status == 4) ∧ t.mem = s.mem ∧ Keep [.x0, .x4] s t := by
  refine WP.mono (WP.keep [.x0, .x4] (Q := fun t =>
      (t.gpr .x4 == 0#64) = (status == 4) ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun _ ⟨⟨hz, hm⟩, hk⟩ => ⟨hz, hm, hk⟩
  unfold Random.statusTest
  brun [exec_ldrSp (show Random.oStatus % 8 = 0 ∧ Random.oStatus < 32768 by decide),
    hsp, hs.ld (d := Random.oStatus) (by decide), hv]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, BitVec.sub_eq_iff_eq_add, BitVec.zero_add]
  rfl

/-- A draw either produces a terminal result or strictly decreases fuel.
The actual status test is verified here; callers supply the draw invariant. -/
theorem random_statusLoop_rule (body : Prog isa) (B : Addr) (Inv : Nat → State → Prop) (Q : State → Prop)
    (hstable : ∀ n s t, Inv n s → t.mem = s.mem → Keep [.x0, .x4] s t → Inv n t)
    (hqstable : ∀ s t, Q s → t.mem = s.mem → Keep [.x0, .x4] s t → Q t)
    (hdraw : ∀ n s, Inv n s → WP isa body s fun t =>
      Scr t B Random.frameBytes ∧ t.sp = B ∧
      ((word t.mem B Random.oStatus ≠ 4 ∧ Q t) ∨
       (word t.mem B Random.oStatus = 4 ∧ ∃ k < n, Inv k t)))
    {n : Nat} {s : State} (hi : Inv n s) :
    WP isa (.loop (.seq body (.block (Random.statusTest 4))) (.zero .x .x4)) s Q := by
  refine WP.loop (M := isa) Inv ?_ n s hi
  intro n u hu
  refine WP.seq (WP.mono (hdraw n u hu) fun v ⟨hvs, hvsp, hv⟩ => ?_)
  refine WP.mono (random_statusTest_ok hvs hvsp rfl) fun t ⟨htz, htm, hkt⟩ => ?_
  rcases hv with ⟨hne, hq⟩ | ⟨he, k, hkn, hk⟩
  · exact Or.inl ⟨by
      change some (t.gpr .x4 == 0#64) = some false
      rw [htz, beq_eq_false_iff_ne.mpr hne],
      hqstable v t hq htm hkt⟩
  · exact Or.inr ⟨by
      change some (t.gpr .x4 == 0#64) = some true
      rw [htz, he, beq_self_eq_true], k, hkn,
      hstable k v t hk htm hkt⟩


theorem random_sampleLoop_rule (B : Addr) (Inv : Nat → State → Prop) (Q : State → Prop)
    (hstable : ∀ n s t, Inv n s → t.mem = s.mem → Keep [.x0, .x4] s t → Inv n t)
    (hqstable : ∀ s t, Q s → t.mem = s.mem → Keep [.x0, .x4] s t → Q t)
    (hdraw : ∀ n s, Inv n s → WP isa Random.draw s fun t =>
      Scr t B Random.frameBytes ∧ t.sp = B ∧
      ((word t.mem B Random.oStatus ≠ 4 ∧ Q t) ∨
       (word t.mem B Random.oStatus = 4 ∧ ∃ k < n, Inv k t)))
    {n : Nat} {s : State} (hi : Inv n s) :
    WP isa (.loop (.seq Random.draw (.block (Random.statusTest 4))) (.zero .x .x4)) s Q :=
  random_statusLoop_rule Random.draw B Inv Q hstable hqstable hdraw hi

end VG.Proof.Dsa.AArch64
