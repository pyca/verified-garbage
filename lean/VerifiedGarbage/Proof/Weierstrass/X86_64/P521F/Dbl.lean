module
-- separate module: the P-521 fast window's proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Weierstrass.X86_64.P521F.Steps
public import VerifiedGarbage.Proof.Framework.X86_64.KeepReg
public import VerifiedGarbage.Proof.Weierstrass.Jac
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# P-521 on x86-64: the doubling's steps

`dblCmsSteps` by the fast steps (`stepProg`): `dblSteps_ok`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.P521F

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64.P521F
open VG.Impl.Weierstrass.X86_64.Mont (fnTmp)
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Proof.Weierstrass
  VG.Proof.Weierstrass.X86_64 Spec.Weierstrass

theorem progs_inline_cons (a b : Prog isa) (l : List (Prog isa)) :
    (progs (a :: b :: l)).inline = .seq a.inline (progs (b :: l)).inline := rfl

theorem progs_inline_one (a : Prog isa) : (progs [a]).inline = a.inline := rfl

variable {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}

/-- Steps 1 to 4 of the doubling. -/
theorem dblSeg1_ok (H : StepCtx M size m Sl) {S : RcbSlots} {p : Pt} (hnd : (rcbW S p).Nodup)
    (hSl : ∀ x ∈ rcbW S p, Sl x) (hlow : ∀ x ∈ rcbW S p, x + 72 ≤ 3520) {V0 : List Nat}
    (_hV0 : ∀ x ∈ V0, x ∉ rcbW S p) {E : Nat → Fin m} {s : State}
    (hI : InvW M base size m Sl ([p.x, p.y, p.z] ++ V0) [] E s) :
    WP isa (progs [stepProg S (.op (.mul S.t0 p.z p.z)), stepProg S (.op (.mul S.t1 p.y p.y)), stepProg S (.op (.add S.t2 p.x S.t0)), stepProg S (.op (.sub S.t3 p.x S.t0))]).inline s fun t =>
      KeepW base (rcbW S p) s t ∧ InvW M base size m Sl ([S.t3, S.t2, S.t1, S.t0, p.x, p.y, p.z] ++ V0) [] (runSteps [(.op (.mul S.t0 p.z p.z) : DStep), (.op (.mul S.t1 p.y p.y) : DStep), (.op (.add S.t2 p.x S.t0) : DStep), (.op (.sub S.t3 p.x S.t0) : DStep)] E) t := by
  simp only [rcbW, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  rcases hnd with ⟨⟨h01, h02, h03, h04, h05, h06, h07, h08⟩, ⟨h12, h13, h14, h15, h16, h17, h18⟩,
    ⟨h23, h24, h25, h26, h27, h28⟩, ⟨h34, h35, h36, h37, h38⟩, ⟨h45, h46, h47, h48⟩, ⟨h56, h57, h58⟩,
    ⟨h67, h68⟩, h78, _⟩
  rw [progs_inline_cons]
  refine stepThen (o := S.t0) (by simp [rcbW]) (mulStepS_ok H hI (weakOp_false h05 h04) (hSl _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (by mem_tac) (by mem_tac)) fun s₁ I₁' => ?_
  have I₁ := I₁'.sub (V' := [S.t0, p.x, p.y, p.z] ++ V0) (W' := []) (fun q hq => by simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at hq ⊢; rcases hq with rfl | rfl | rfl | rfl | hq <;> first | simp | simp [hq]) (fun q hq => by simp at hq)
  rw [progs_inline_cons]
  refine stepThen (o := S.t1) (by simp [rcbW]) (mulStepS_ok H I₁ (weakOp_false h15 h14) (hSl _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (by mem_tac) (by mem_tac)) fun s₂ I₂' => ?_
  have I₂ := I₂'.sub (V' := [S.t1, S.t0, p.x, p.y, p.z] ++ V0) (W' := []) (fun q hq => by simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at hq ⊢; rcases hq with rfl | rfl | rfl | rfl | rfl | hq <;> first | simp | simp [hq]) (fun q hq => by simp at hq)
  rw [progs_inline_cons]
  refine stepThen (o := S.t2) (by simp [rcbW]) (addStep_ok H I₂ (hSl _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (by mem_tac) (by mem_tac)) fun s₃ I₃' => ?_
  have I₃ := I₃'.sub (V' := [S.t2, S.t1, S.t0, p.x, p.y, p.z] ++ V0) (W' := []) (fun q hq => by simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at hq ⊢; rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | hq <;> first | simp | simp [hq]) (fun q hq => by simp at hq)
  rw [progs_inline_one]
  refine stepLast' (o := S.t3) (by simp [rcbW]) (WP.mono (subStep_ok H I₃ (hSl _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (by mem_tac) (by mem_tac)) fun s' ⟨k', I₄'⟩ => ⟨k', ?_⟩)
  exact I₄'.sub (V' := [S.t3, S.t2, S.t1, S.t0, p.x, p.y, p.z] ++ V0) (W' := []) (fun q hq => by simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at hq ⊢; rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hq <;> first | simp | simp [hq]) (fun q hq => by simp at hq)

/-- Steps 5 to 8 of the doubling. -/
theorem dblSeg2_ok (H : StepCtx M size m Sl) {S : RcbSlots} {p : Pt} (hnd : (rcbW S p).Nodup)
    (hSl : ∀ x ∈ rcbW S p, Sl x) (hlow : ∀ x ∈ rcbW S p, x + 72 ≤ 3520) {V0 : List Nat}
    (hV0 : ∀ x ∈ V0, x ∉ rcbW S p) {E : Nat → Fin m} {s : State}
    (hI : InvW M base size m Sl ([S.t3, S.t2, S.t1, S.t0, p.x, p.y, p.z] ++ V0) [] E s) :
    WP isa (progs [stepProg S (.op (.mul S.t4 S.t2 S.t3)), stepProg S (.op (.add S.t2 p.y p.z)), stepProg S (.op (.mul S.t3 S.t4 S.t4)), stepProg S (.op (.mul S.t5 p.x S.t1))]).inline s fun t =>
      KeepW base (rcbW S p) s t ∧ InvW M base size m Sl ([S.t3, S.t2, S.t4, S.t1, S.t0, p.x, p.y, p.z] ++ V0) [S.t5] (runSteps [(.op (.mul S.t4 S.t2 S.t3) : DStep), (.op (.add S.t2 p.y p.z) : DStep), (.op (.mul S.t3 S.t4 S.t4) : DStep), (.op (.mul S.t5 p.x S.t1) : DStep)] E) t := by
  simp only [rcbW, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  rcases hnd with ⟨⟨h01, h02, h03, h04, h05, h06, h07, h08⟩, ⟨h12, h13, h14, h15, h16, h17, h18⟩,
    ⟨h23, h24, h25, h26, h27, h28⟩, ⟨h34, h35, h36, h37, h38⟩, ⟨h45, h46, h47, h48⟩, ⟨h56, h57, h58⟩,
    ⟨h67, h68⟩, h78, _⟩
  rw [progs_inline_cons]
  refine stepThen (o := S.t4) (by simp [rcbW]) (mulStepS_ok H hI (weakOp_false' h45 h23) (hSl _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (by mem_tac) (by mem_tac)) fun s₅ I₅' => ?_
  have I₅ := I₅'.sub (V' := [S.t4, S.t3, S.t2, S.t1, S.t0, p.x, p.y, p.z] ++ V0) (W' := []) (fun q hq => by simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at hq ⊢; rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hq <;> first | simp | simp [hq]) (fun q hq => by simp at hq)
  rw [progs_inline_cons]
  refine stepThen (o := S.t2) (by simp [rcbW]) (addStep_ok H I₅ (hSl _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (by mem_tac) (by mem_tac)) fun s₆ I₆' => ?_
  have I₆ := I₆'.sub (V' := [S.t2, S.t4, S.t3, S.t1, S.t0, p.x, p.y, p.z] ++ V0) (W' := []) (fun q hq => by simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at hq ⊢; rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hq <;> first | simp | simp [hq]) (fun q hq => by simp at hq)
  rw [progs_inline_cons]
  refine stepThen (o := S.t3) (by simp [rcbW]) (mulStepS_ok H I₆ (weakOp_false h35 h34) (hSl _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (by mem_tac) (by mem_tac)) fun s₇ I₇' => ?_
  have I₇ := I₇'.sub (V' := [S.t3, S.t2, S.t4, S.t1, S.t0, p.x, p.y, p.z] ++ V0) (W' := []) (fun q hq => by simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at hq ⊢; rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hq <;> first | simp | simp [hq]) (fun q hq => by simp at hq)
  rw [progs_inline_one]
  refine stepLast' (o := S.t5) (by simp [rcbW]) (WP.mono (mulStepW_ok H I₇ (by simp [weakOp]) (hSl _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (by mem_tac) (by mem_tac)) fun s' ⟨k', I₈'⟩ => ⟨k', ?_⟩)
  exact I₈'.sub (V' := [S.t3, S.t2, S.t4, S.t1, S.t0, p.x, p.y, p.z] ++ V0) (W' := [S.t5]) (fun q hq => by simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at hq; rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hq; exacts [mem_filter_ne (by mem_tac) h35, mem_filter_ne (by mem_tac) h25, mem_filter_ne (by mem_tac) h45, mem_filter_ne (by mem_tac) h15, mem_filter_ne (by mem_tac) h05, mem_filter_ne (by mem_tac) (Ne.symm h56), mem_filter_ne (by mem_tac) (Ne.symm h57), mem_filter_ne (by mem_tac) (Ne.symm h58), mem_filter_ne (by simp only [List.mem_cons, List.mem_append, or_true, hq]) (fun e => hV0 _ hq (e ▸ by simp [rcbW]))]) (fun q hq => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl; exacts [List.mem_cons_self ..])

/-- Steps 9 to 12 of the doubling. -/
theorem dblSeg3_ok (H : StepCtx M size m Sl) {S : RcbSlots} {p : Pt} (hnd : (rcbW S p).Nodup)
    (hSl : ∀ x ∈ rcbW S p, Sl x) (hlow : ∀ x ∈ rcbW S p, x + 72 ≤ 3520) {V0 : List Nat}
    (_hV0 : ∀ x ∈ V0, x ∉ rcbW S p) {E : Nat → Fin m} {s : State}
    (hI : InvW M base size m Sl ([S.t3, S.t2, S.t4, S.t1, S.t0, p.x, p.y, p.z] ++ V0) [S.t5] E s) :
    WP isa (progs [stepProg S (.op (.mul S.t2 S.t2 S.t2)), stepProg S (.cms S.t3 12 S.t5 9 S.t3), stepProg S (.op (.sub S.t2 S.t2 S.t0)), stepProg S (.op (.sub p.z S.t2 S.t1))]).inline s fun t =>
      KeepW base (rcbW S p) s t ∧ InvW M base size m Sl ([p.z, S.t2, S.t3, S.t4, S.t1, S.t0, p.x, p.y] ++ V0) [S.t5] (runSteps [(.op (.mul S.t2 S.t2 S.t2) : DStep), (.cms S.t3 12 S.t5 9 S.t3 : DStep), (.op (.sub S.t2 S.t2 S.t0) : DStep), (.op (.sub p.z S.t2 S.t1) : DStep)] E) t := by
  simp only [rcbW, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  rcases hnd with ⟨⟨h01, h02, h03, h04, h05, h06, h07, h08⟩, ⟨h12, h13, h14, h15, h16, h17, h18⟩,
    ⟨h23, h24, h25, h26, h27, h28⟩, ⟨h34, h35, h36, h37, h38⟩, ⟨h45, h46, h47, h48⟩, ⟨h56, h57, h58⟩,
    ⟨h67, h68⟩, h78, _⟩
  rw [progs_inline_cons]
  refine stepThen (o := S.t2) (by simp [rcbW]) (mulStepS_ok H hI (weakOp_false h25 h24) (hSl _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (by mem_tac) (by mem_tac)) fun s₉ I₉' => ?_
  have I₉ := I₉'.sub (V' := [S.t2, S.t3, S.t4, S.t1, S.t0, p.x, p.y, p.z] ++ V0) (W' := [S.t5]) (fun q hq => by simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at hq ⊢; rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hq <;> first | simp | simp [hq]) (fun q hq => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl; exacts [mem_filter_ne (by simp) (Ne.symm h25)])
  rw [progs_inline_cons]
  refine stepThen (o := S.t3) (by simp [rcbW]) (cmsStep_ok H I₉ (hSl _ (by simp [rcbW])) (Or.inr (Or.inl ⟨rfl, rfl⟩)) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (Or.inr (by mem_tac)) (by mem_tac)) fun s₁₀ I₁₀' => ?_
  have I₁₀ := I₁₀'.sub (V' := [S.t3, S.t2, S.t4, S.t1, S.t0, p.x, p.y, p.z] ++ V0) (W' := [S.t5]) (fun q hq => by simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at hq ⊢; rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hq <;> first | simp | simp [hq]) (fun q hq => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl; exacts [mem_filter_ne (by simp) (Ne.symm h35)])
  rw [progs_inline_cons]
  refine stepThen (o := S.t2) (by simp [rcbW]) (subStep_ok H I₁₀ (hSl _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (by mem_tac) (by mem_tac)) fun s₁₁ I₁₁' => ?_
  have I₁₁ := I₁₁'.sub (V' := [S.t2, S.t3, S.t4, S.t1, S.t0, p.x, p.y, p.z] ++ V0) (W' := [S.t5]) (fun q hq => by simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at hq ⊢; rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hq <;> first | simp | simp [hq]) (fun q hq => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl; exacts [mem_filter_ne (by simp) (Ne.symm h25)])
  rw [progs_inline_one]
  refine stepLast' (o := p.z) (by simp [rcbW]) (WP.mono (subStep_ok H I₁₁ (hSl _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (by mem_tac) (by mem_tac)) fun s' ⟨k', I₁₂'⟩ => ⟨k', ?_⟩)
  exact I₁₂'.sub (V' := [p.z, S.t2, S.t3, S.t4, S.t1, S.t0, p.x, p.y] ++ V0) (W' := [S.t5]) (fun q hq => by simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at hq ⊢; rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hq <;> first | simp | simp [hq]) (fun q hq => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl; exacts [mem_filter_ne (by simp) h58])

/-- Steps 13 to 16 of the doubling. -/
theorem dblSeg4_ok (H : StepCtx M size m Sl) {S : RcbSlots} {p : Pt} (hnd : (rcbW S p).Nodup)
    (hSl : ∀ x ∈ rcbW S p, Sl x) (hlow : ∀ x ∈ rcbW S p, x + 72 ≤ 3520) {V0 : List Nat}
    (hV0 : ∀ x ∈ V0, x ∉ rcbW S p) {E : Nat → Fin m} {s : State}
    (hI : InvW M base size m Sl ([p.z, S.t2, S.t3, S.t4, S.t1, S.t0, p.x, p.y] ++ V0) [S.t5] E s) :
    WP isa (progs [stepProg S (.op (.mul S.t0 S.t1 S.t1)), stepProg S (.op (.mul S.t4 S.t3 S.t4)), stepProg S (.cms p.x 4 S.t5 1 S.t3), stepProg S (.cms p.y 3 S.t4 8 S.t0)]).inline s fun t =>
      KeepW base (rcbW S p) s t ∧ InvW M base size m Sl ([p.y, p.x, S.t0, p.z, S.t2, S.t3, S.t1] ++ V0) [S.t4, S.t5] (runSteps [(.op (.mul S.t0 S.t1 S.t1) : DStep), (.op (.mul S.t4 S.t3 S.t4) : DStep), (.cms p.x 4 S.t5 1 S.t3 : DStep), (.cms p.y 3 S.t4 8 S.t0 : DStep)] E) t := by
  simp only [rcbW, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  rcases hnd with ⟨⟨h01, h02, h03, h04, h05, h06, h07, h08⟩, ⟨h12, h13, h14, h15, h16, h17, h18⟩,
    ⟨h23, h24, h25, h26, h27, h28⟩, ⟨h34, h35, h36, h37, h38⟩, ⟨h45, h46, h47, h48⟩, ⟨h56, h57, h58⟩,
    ⟨h67, h68⟩, h78, _⟩
  rw [progs_inline_cons]
  refine stepThen (o := S.t0) (by simp [rcbW]) (mulStepS_ok H hI (weakOp_false h05 h04) (hSl _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (by mem_tac) (by mem_tac)) fun s₁₃ I₁₃' => ?_
  have I₁₃ := I₁₃'.sub (V' := [S.t0, p.z, S.t2, S.t3, S.t4, S.t1, p.x, p.y] ++ V0) (W' := [S.t5]) (fun q hq => by simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at hq ⊢; rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hq <;> first | simp | simp [hq]) (fun q hq => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl; exacts [mem_filter_ne (by simp) (Ne.symm h05)])
  rw [progs_inline_cons]
  refine stepThen (o := S.t4) (by simp [rcbW]) (mulStepW_ok H I₁₃ (by simp [weakOp]) (hSl _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (by mem_tac) (by mem_tac)) fun s₁₄ I₁₄' => ?_
  have I₁₄ := I₁₄'.sub (V' := [S.t0, p.z, S.t2, S.t3, S.t1, p.x, p.y] ++ V0) (W' := [S.t4, S.t5]) (fun q hq => by simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at hq; rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hq; exacts [mem_filter_ne (by mem_tac) h04, mem_filter_ne (by mem_tac) (Ne.symm h48), mem_filter_ne (by mem_tac) h24, mem_filter_ne (by mem_tac) h34, mem_filter_ne (by mem_tac) h14, mem_filter_ne (by mem_tac) (Ne.symm h46), mem_filter_ne (by mem_tac) (Ne.symm h47), mem_filter_ne (by simp only [List.mem_cons, List.mem_append, or_true, hq]) (fun e => hV0 _ hq (e ▸ by simp [rcbW]))]) (fun q hq => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl; exacts [List.mem_cons_self .., List.mem_cons_of_mem _ (by simp)])
  rw [progs_inline_cons]
  refine stepThen (o := p.x) (by simp [rcbW]) (cmsStep_ok H I₁₄ (hSl _ (by simp [rcbW])) (Or.inl ⟨rfl, rfl⟩) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (Or.inr (by mem_tac)) (by mem_tac)) fun s₁₅ I₁₅' => ?_
  have I₁₅ := I₁₅'.sub (V' := [p.x, S.t0, p.z, S.t2, S.t3, S.t1, p.y] ++ V0) (W' := [S.t4, S.t5]) (fun q hq => by simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at hq ⊢; rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hq <;> first | simp | simp [hq]) (fun q hq => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl; exacts [mem_filter_ne (by simp) h46, mem_filter_ne (by simp) h56])
  rw [progs_inline_one]
  refine stepLast' (o := p.y) (by simp [rcbW]) (WP.mono (cmsStep_ok H I₁₅ (hSl _ (by simp [rcbW])) (Or.inr (Or.inr ⟨rfl, rfl⟩)) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (hlow _ (by simp [rcbW])) (Or.inr (by mem_tac)) (by mem_tac)) fun s' ⟨k', I₁₆'⟩ => ⟨k', ?_⟩)
  exact I₁₆'.sub (V' := [p.y, p.x, S.t0, p.z, S.t2, S.t3, S.t1] ++ V0) (W' := [S.t4, S.t5]) (fun q hq => by simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at hq ⊢; rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hq <;> first | simp | simp [hq]) (fun q hq => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl; exacts [mem_filter_ne (by simp) h47, mem_filter_ne (by simp) h57])

/-- The doubling's steps, from `p`'s coordinates (and the slots `V0`, which it does not write). -/
theorem dblSteps_ok (H : StepCtx M size m Sl) {S : RcbSlots} {p : Pt} (hnd : (rcbW S p).Nodup)
    (hSl : ∀ x ∈ rcbW S p, Sl x) (hlow : ∀ x ∈ rcbW S p, x + 72 ≤ 3520) {V0 : List Nat}
    (hV0 : ∀ x ∈ V0, x ∉ rcbW S p) {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl ([p.x, p.y, p.z] ++ V0) E s) :
    WP isa (progs ((dblCmsSteps S p).map (stepProg S))).inline s fun t => KeepW base (rcbW S p) s t ∧
      InvW M base size m Sl ([p.y, p.x, S.t0, p.z, S.t2, S.t3, S.t1] ++ V0) [S.t4, S.t5]
        (runSteps (dblCmsSteps S p) E) t := by
  have I₀ : InvW M base size m Sl ([p.x, p.y, p.z] ++ V0) [] E s :=
    ⟨hI, fun _ h => absurd h (List.not_mem_nil), fun _ h => absurd h (List.not_mem_nil),
      fun _ h => absurd h (List.not_mem_nil)⟩
  simp only [dblCmsSteps, List.map]
  refine progs_append_inline [_, _, _, _] [_, _, _, _, _, _, _, _, _, _, _, _] (by simp) (by simp)
    (WP.mono (dblSeg1_ok H hnd hSl hlow hV0 I₀) fun s₁ ⟨k₁, I₁⟩ => ?_)
  refine progs_append_inline [_, _, _, _] [_, _, _, _, _, _, _, _] (by simp) (by simp)
    (WP.mono (dblSeg2_ok H hnd hSl hlow hV0 I₁) fun s₂ ⟨k₂, I₂⟩ => ?_)
  refine progs_append_inline [_, _, _, _] [_, _, _, _] (by simp) (by simp)
    (WP.mono (dblSeg3_ok H hnd hSl hlow hV0 I₂) fun s₃ ⟨k₃, I₃⟩ => ?_)
  exact WP.mono (dblSeg4_ok H hnd hSl hlow hV0 I₃) fun _ ⟨k₄, I₄⟩ =>
    ⟨k₁.trans (k₂.trans (k₃.trans k₄)), I₄⟩

/-! ## The doubling, `rbx` and `rsi` kept in `xmm15` and `xmm14` -/

theorem save_ok (s : State) :
    WP isa (.block save) s fun s' => s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [save, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, Option.some.injEq,
    exists_eq_left', RegUpd.gpr_setXmm, RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm]
  exact ⟨trivial, trivial, trivial, trivial⟩

theorem restore_ok (s : State) :
    WP isa (.block restore) s fun s' => (∀ r, r ≠ .rbx → r ≠ .rsi → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [restore, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  refine ⟨fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  rw [RegUpd.gpr_setReg_of_ne _ _ h2, RegUpd.gpr_setReg_of_ne _ _ h1]

theorem dblCms_out (S : RcbSlots) (p : Pt) {F : Type _} [Lean.Grind.CommRing F] (E : Nat → F) {x : Nat}
    (hx : x ∉ rcbW S p) : runSteps (dblCmsSteps S p) E x = E x := by
  simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hx
  simp only [dblCmsSteps, runSteps, List.foldl, DStep.run, FOp.run, Function.update_apply, h0, h1, h2, h3, h4,
    h5, h6, h7, h8, ite_false]

/-- The registers but `clob 9` that a step may change are `rbx` and `rsi`. -/
theorem fclob_sub {r : Reg} (hr : r ∉ clob 9) (hb : r ≠ .rbx) (hs : r ≠ .rsi) : r ∉ fclob := by
  revert hr hb hs; cases r <;> decide

/-- `p = 2p` in place by `dbl`, for `p` and the slots `V0` (which it keeps) valid: as `DblOk`. -/
theorem dblF_ok {M : Mod} {C : Curve} {base : Addr} {size : Nat} {Sl : Nat → Prop}
    (H : StepCtx M size C.p Sl) (hC : Law C) (ha : AM3 C) {S : RcbSlots} {p : Pt} (hnd : (rcbW S p).Nodup)
    (hSl : ∀ x ∈ rcbW S p, Sl x) (hlow : ∀ x ∈ rcbW S p, x + 72 ≤ 3520) {V0 : List Nat}
    (hV0 : ∀ x ∈ V0, x ∉ rcbW S p) (hkb : KeepReg.keeps .rbx (dbl S p).inline = true)
    (hks : KeepReg.keeps .rsi (dbl S p).inline = true) {E : Nat → Fe C} {s : State}
    (hI : Inv M base size C.p Sl ([p.x, p.y, p.z] ++ V0) E s) {Q : Spec.Weierstrass.Point C}
    (hQ : Spec.Weierstrass.onCurve C Q = true) (hJ : InvJ C (E p.x) (E p.y) (E p.z) Q) :
    WP isa (dbl S p).inline s fun t => KeepRegs (clob 9) s t ∧ KeepW base (rcbW S p) s t ∧
      ∃ E' : Nat → Fe C, Inv M base size C.p Sl ([p.x, p.y, p.z] ++ V0) E' t ∧ (∀ x ∉ rcbW S p, E' x = E x) ∧
      InvJ C (E' p.x) (E' p.y) (E' p.z) (Spec.Weierstrass.add Q Q) := by
  have hw : WP isa (dbl S p).inline s fun t => (∀ r, r ≠ .rbx → r ≠ .rsi → r ∉ fclob → t.gpr r = s.gpr r) ∧
      KeepW base (rcbW S p) s t ∧ ∃ E' : Nat → Fe C, Inv M base size C.p Sl ([p.x, p.y, p.z] ++ V0) E' t ∧
        (∀ x ∉ rcbW S p, E' x = E x) ∧ InvJ C (E' p.x) (E' p.y) (E' p.z) (Spec.Weierstrass.add Q Q) := by
    show WP isa (.seq (.block save) (.seq (progs ((dblCmsSteps S p).map (stepProg S))).inline (.block restore))) s _
    refine WP.seq (WP.mono (save_ok s) fun s₁ ⟨g₁, m₁, rd₁, wr₁⟩ => ?_)
    have hs₁ : Scr s₁ base size := ⟨by rw [g₁]; exact hI.scr.rdi, by rw [wr₁]; exact hI.scr.wr, hI.scr.nowrap⟩
    have hI₁ : Inv M base size C.p Sl ([p.x, p.y, p.z] ++ V0) E s₁ :=
      ⟨hs₁, m₁ ▸ hI.mod, hI.sl, fun x hx => m₁ ▸ hI.lt x hx, fun x hx => m₁ ▸ hI.val x hx⟩
    refine WP.seq (WP.mono (dblSteps_ok H hnd hSl hlow hV0 hI₁) fun s₂ ⟨k₂, I₂⟩ => ?_)
    refine WP.mono (restore_ok s₂) fun s₃ ⟨g₃, m₃, rd₃, wr₃⟩ => ⟨fun r hb hs hr => ?_, ?_, ?_⟩
    · rw [g₃ r hb hs, k₂.gpr r hr, g₁]
    · exact ⟨fun r hr => by
          rw [g₃ r (fun h => hr (h ▸ by decide)) (fun h => hr (h ▸ by decide)), k₂.gpr r hr, g₁],
        by rw [rd₃, k₂.rd, rd₁], by rw [wr₃, k₂.wr, wr₁],
        fun x hx ht => by rw [m₃, k₂.mem x hx ht, m₁]⟩
    · have I₂' := I₂.inv.sub (V' := [p.x, p.y, p.z] ++ V0) (by
        intro q hq
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at hq ⊢
        rcases hq with rfl | rfl | rfl | hq <;> first | simp | simp [hq])
      refine ⟨runSteps (dblCmsSteps S p) E, ⟨⟨by rw [g₃ _ (by decide) (by decide)]; exact I₂'.scr.rdi,
        by rw [wr₃]; exact I₂'.scr.wr, I₂'.scr.nowrap⟩, m₃ ▸ I₂'.mod, I₂'.sl,
        fun x hx => m₃ ▸ I₂'.lt x hx, fun x hx => m₃ ▸ I₂'.val x hx⟩,
        fun x hx => dblCms_out S p E hx, InvJ.dbl' hC ha hQ hJ (dblCms_run S p E hnd)⟩
  obtain ⟨tr, t, he, hq⟩ := hw
  refine ⟨tr, t, he, ⟨fun r hr => ?_, hq.2.1.rd, hq.2.1.wr⟩, hq.2⟩
  by_cases hb : r = .rbx
  · subst hb; exact Exec.gpr_keeps hkb he
  by_cases hs : r = .rsi
  · subst hs; exact Exec.gpr_keeps hks he
  exact hq.1 r hb hs (fclob_sub hr hb hs)

end VG.Proof.Weierstrass.X86_64.P521F
