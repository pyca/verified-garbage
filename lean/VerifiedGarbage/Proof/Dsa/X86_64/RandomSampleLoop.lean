module
public import VerifiedGarbage.Impl.Dsa.X86_64.Random
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame

/-! Termination rule for the sampler's status-controlled loop. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem random_statusTest_ok {s : State} {B : Addr} {status : BitVec 64}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
    (hv : word s.mem B Random.oStatus = status) :
    WP isa (.block [.mov .rax (.mem (Random.sp Random.oStatus)), .alu .cmp .rax (.imm 4)]) s fun t =>
      t.zf = some (status == 4) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.zf = some (status == 4) ∧ t.mem = s.mem) ?_ rfl)
    fun _ ⟨⟨hz, hm⟩, hk⟩ => ⟨hz, hm, hk⟩
  xrun [random_ea_sp, hsp, hs.ld (d := Random.oStatus) (by decide), hv]
  exact sub_beq_zero status 4

/-- A draw either produces a terminal result or strictly decreases fuel.
The actual status test is verified here; callers supply the draw invariant. -/
theorem random_statusLoop_rule (body : Prog isa) (B : Addr) (Inv : Nat → State → Prop) (Q : State → Prop)
    (hstable : ∀ n s t, Inv n s → t.mem = s.mem → Keep [.rax] s t → Inv n t)
    (hqstable : ∀ s t, Q s → t.mem = s.mem → Keep [.rax] s t → Q t)
    (hdraw : ∀ n s, Inv n s → WP isa body s fun t =>
      Scr t B Random.frameBytes ∧ t.gpr .rsp = B ∧
      ((word t.mem B Random.oStatus ≠ 4 ∧ Q t) ∨
       (word t.mem B Random.oStatus = 4 ∧ ∃ k < n, Inv k t)))
    {n : Nat} {s : State} (hi : Inv n s) :
    WP isa (.loop (.seq body (.block [.mov .rax (.mem (Random.sp Random.oStatus)),
      .alu .cmp .rax (.imm 4)])) .e) s Q := by
  refine WP.loop (M := isa) Inv ?_ n s hi
  intro n u hu
  refine WP.seq (WP.mono (hdraw n u hu) fun v ⟨hvs, hvsp, hv⟩ => ?_)
  refine WP.mono (random_statusTest_ok hvs hvsp rfl) fun t ⟨htz, htm, hkt⟩ => ?_
  rcases hv with ⟨hne, hq⟩ | ⟨he, k, hkn, hk⟩
  · exact Or.inl ⟨by simp only [eval, htz, beq_eq_false_iff_ne.mpr hne],
      hqstable v t hq htm hkt⟩
  · exact Or.inr ⟨by simp only [eval, htz, he, beq_self_eq_true], k, hkn,
      hstable k v t hk htm hkt⟩


theorem random_sampleLoop_rule (B : Addr) (Inv : Nat → State → Prop) (Q : State → Prop)
    (hstable : ∀ n s t, Inv n s → t.mem = s.mem → Keep [.rax] s t → Inv n t)
    (hqstable : ∀ s t, Q s → t.mem = s.mem → Keep [.rax] s t → Q t)
    (hdraw : ∀ n s, Inv n s → WP isa Random.draw s fun t =>
      Scr t B Random.frameBytes ∧ t.gpr .rsp = B ∧
      ((word t.mem B Random.oStatus ≠ 4 ∧ Q t) ∨
       (word t.mem B Random.oStatus = 4 ∧ ∃ k < n, Inv k t)))
    {n : Nat} {s : State} (hi : Inv n s) :
    WP isa (.loop (.seq Random.draw (.block [.mov .rax (.mem (Random.sp Random.oStatus)),
      .alu .cmp .rax (.imm 4)])) .e) s Q :=
  random_statusLoop_rule Random.draw B Inv Q hstable hqstable hdraw hi

theorem random_statusLoop_rule_mx (body : Prog isa) (B : Addr) (Inv : Nat → State → Prop) (Q : State → Prop)
    (hstable : ∀ n s t, Inv n s → t.mem = s.mem → Keep [.rax] s t → t.mxcsr = s.mxcsr → Inv n t)
    (hqstable : ∀ s t, Q s → t.mem = s.mem → Keep [.rax] s t → t.mxcsr = s.mxcsr → Q t)
    (hdraw : ∀ n s, Inv n s → WP isa body s fun t =>
      Scr t B Random.frameBytes ∧ t.gpr .rsp = B ∧
      ((word t.mem B Random.oStatus ≠ 4 ∧ Q t) ∨
       (word t.mem B Random.oStatus = 4 ∧ ∃ k < n, Inv k t)))
    {n : Nat} {s : State} (hi : Inv n s) :
    WP isa (.loop (.seq body (.block [.mov .rax (.mem (Random.sp Random.oStatus)),
      .alu .cmp .rax (.imm 4)])) .e) s Q := by
  refine WP.loop (M := isa) Inv ?_ n s hi
  intro n u hu
  refine WP.seq (WP.mono (hdraw n u hu) fun v ⟨hvs, hvsp, hv⟩ => ?_)
  refine WP.mono_mx (by decide) (random_statusTest_ok hvs hvsp rfl) fun t ⟨htz, htm, hkt⟩ hmx => ?_
  rcases hv with ⟨hne, hq⟩ | ⟨he, k, hkn, hk⟩
  · exact Or.inl ⟨by simp only [eval, htz, beq_eq_false_iff_ne.mpr hne],
      hqstable v t hq htm hkt hmx⟩
  · exact Or.inr ⟨by simp only [eval, htz, he, beq_self_eq_true], k, hkn,
      hstable k v t hk htm hkt hmx⟩

end VG.Proof.Dsa.X86_64
