module

public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.Entry
public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.Timing
meta import VerifiedGarbage.TCB.Code
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-! # Timing of the register-save frames around preparation -/

-- separate module: isolates permission-aware frame timing from polynomial preparation invariants.

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa

def PushRel (r : Reg) (P : State → State → Prop) (a b : State) : Prop :=
  ∃ x y, P x y ∧ a = pushed r x ∧ b = pushed r y

theorem frame_tr {r : Reg} {body : Prog isa} {P R : State → State → Prop}
    (hsp : ∀ x y, P x y → x.sp = y.sp) (hbody : RelCT isa (PushRel r P) body R) :
    RelCT isa P (.frame (.push r) body (.pop r)) fun _ _ => True := by
  intro x y tx ty x' y' hp ex ey
  have push_eq : ∀ {s a : State}, isa.push (.push r) s = some a → a = pushed r s := by
    intro s a h
    change push (.push r) s = some a at h
    simp only [push] at h
    split at h
    · exact (Option.some.inj h).symm
    · cases h
  cases ex with
  | frame px bx qx =>
    cases ey with
    | frame py by' qy =>
      have ea := push_eq px
      have eb := push_eq py
      subst ea eb
      obtain ⟨ht, _⟩ := hbody _ _ _ _ _ _ ⟨x, y, hp, rfl, rfl⟩ bx by'
      have sx := (Exec.rdwr bx).2.2
      have sy := (Exec.rdwr by').2.2
      refine ⟨?_, trivial⟩
      simp only [addrs, sx, sy, pushed, hsp x y hp, ht]

theorem pushRel_sp {r : Reg} {P : State → State → Prop}
    (hsp : ∀ x y, P x y → x.sp = y.sp) : ∀ x y, PushRel r P x y → x.sp = y.sp := by
  rintro _ _ ⟨x, y, h, rfl, rfl⟩
  exact congrArg (· - 16) (hsp x y h)

def EntryRel (bytes count : Nat) (x y : State) : Prop :=
  EntryPre bytes count x ∧ EntryPre bytes count y ∧
    x.gpr .x0 = y.gpr .x0 ∧ x.gpr .x1 = y.gpr .x1 ∧
    x.gpr .x2 = y.gpr .x2 ∧ x.sp = y.sp

def fourPushed (s : State) : State :=
  pushed .x30 (pushed .x28 (pushed .x26 (pushed .x25 s)))

def FourPushRel (P : State → State → Prop) : State → State → Prop :=
  PushRel .x30 (PushRel .x28 (PushRel .x26 (PushRel .x25 P)))

theorem four_origin {P : State → State → Prop} {a b : State} (h : FourPushRel P a b) :
    ∃ x y, P x y ∧ a = fourPushed x ∧ b = fourPushed y := by
  rcases h with ⟨x3, y3, h3, rfl, rfl⟩
  rcases h3 with ⟨x2, y2, h2, rfl, rfl⟩
  rcases h2 with ⟨x1, y1, h1, rfl, rfl⟩
  rcases h1 with ⟨x, y, h0, rfl, rfl⟩
  exact ⟨x, y, h0, rfl, rfl⟩

theorem four_sp (s : State) : (fourPushed s).sp = s.sp - 64 := by
  simp only [fourPushed, pushed, BitVec.sub_sub]
  rfl

theorem push_wr_cover (r : Reg) (s : State) : Covers s.wr (pushed r s).wr :=
  Covers.of_mem fun _ hr => List.mem_cons_of_mem _ hr

theorem four_wr_cover (s : State) : Covers s.wr (fourPushed s).wr :=
  (push_wr_cover .x25 s).trans ((push_wr_cover .x26 (pushed .x25 s)).trans
    ((push_wr_cover .x28 (pushed .x26 (pushed .x25 s))).trans
      (push_wr_cover .x30 (pushed .x28 (pushed .x26 (pushed .x25 s))))))

theorem setup_layout {bytes count : Nat} {σ s : State} (h : EntryPre bytes count σ)
    (hb : bytes < 2 ^ 32) (ho : bytes + 1024 * count < 2 ^ 32)
    (hk : VG.Proof.MlKem.AArch64.Only [.x25, .x26, .x28] (fourPushed σ) s)
    (h25 : s.gpr .x25 = σ.gpr .x0) (h26 : s.gpr .x26 = σ.gpr .x1)
    (h28 : s.gpr .x28 = σ.gpr .x2) :
    Lay 16 (input bytes) (output bytes count) s := by
  exact entry_layout_covers h hb ho
    (by rw [hk.rd, hk.wr]; exact Covers.append (Covers.refl _) (four_wr_cover σ))
    (by rw [hk.wr]; exact four_wr_cover σ)
    (hk.sp.trans (four_sp σ)) h25 h26 h28

theorem prepareFrame_tr {bytes count : Nat} {body : Prog isa}
    (hb : bytes < 2 ^ 32) (ho : bytes + 1024 * count < 2 ^ 32)
    (hbody : RelCT isa (PrepRel 16 (input bytes) (output bytes count)) body
      (PrepRel 16 (input bytes) (output bytes count))) :
    RelCT isa (EntryRel bytes count) (Impl.MlDsa.AArch64.PreparedKey.prepareFrame body)
      fun _ _ => True := by
  have hs0 : ∀ x y, EntryRel bytes count x y → x.sp = y.sp := fun _ _ h => h.2.2.2.2.2
  have hs1 := pushRel_sp (r := .x25) hs0
  have hs2 := pushRel_sp (r := .x26) hs1
  have hs3 := pushRel_sp (r := .x28) hs2
  unfold Impl.MlDsa.AArch64.PreparedKey.prepareFrame
  simp only [List.foldr_cons, List.foldr_nil]
  refine frame_tr hs0 (frame_tr hs1 (frame_tr hs2 (frame_tr (R := fun _ _ => True) hs3 ?_)))
  refine RelCT.seq (R := PrepRel 16 (input bytes) (output bytes count)) (RelCT.postDep
    (taintRel [.x0, .x1, .x2] (fun x y h => ?_) (by taint_decide))
    (fun x y _ => ⟨setup_ok x, setup_ok y⟩)
    (fun x y x' y' h hx hy => ?_))
    (RelCT.mono hbody (fun _ _ h => h) (fun _ _ _ => trivial))
  · rcases four_origin h with ⟨a, b, hp, rfl, rfl⟩
    refine ⟨by rw [four_sp, four_sp, hp.2.2.2.2.2], ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1]
  · rcases four_origin h with ⟨a, b, hp, rfl, rfl⟩
    refine ⟨setup_layout hp.1 hb ho hx.1 hx.2.1 hx.2.2.1 hx.2.2.2,
      setup_layout hp.2.1 hb ho hy.1 hy.2.1 hy.2.2.1 hy.2.2.2, ?_⟩
    refine ⟨?_, ?_⟩
    · intro r hr
      simp only [prepBases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hx.2.1.trans (hp.2.2.1.trans hy.2.1.symm)
      · exact hx.2.2.1.trans (hp.2.2.2.1.trans hy.2.2.1.symm)
      · exact hx.2.2.2.trans (hp.2.2.2.2.1.trans hy.2.2.2.symm)
    · rw [hx.1.sp, hy.1.sp, four_sp, four_sp, hp.2.2.2.2.2]

end VG.Proof.MlDsa.AArch64.PreparedKey
