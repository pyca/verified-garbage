module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Teardown
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Stack
import VerifiedGarbage.Proof.Framework.Offset

/-! # Compose the round's two saved frames -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Impl.MillerRabin.X86_64

/-- The round's two frames, of which the postcondition may rely on nothing
their bytes hold once released, nor on the unknowns: it holds whatever
memory `m` that differs from the body's only in the 112 bytes below `rsp`
the frames take, and whatever unknowns `u`, the state then has. -/
theorem round_frames {s : State} {body : Prog isa} {Q : State → Prop}
    (hs : 120 ≤ (s.gpr .rsp).toNat)
    (hb : WP isa body (entered s) fun t =>
      t.gpr .rsp = (entered s).gpr .rsp ∧ t.wr = (entered s).wr ∧ ∀ m u,
        Frame [⟨(entered s).gpr .rsp, 112⟩] t.mem m → Q { exited t with mem := m, unknowns := u }) :
    WP isa (.frame (.push saved) (.frame (.push [.rbp]) body (.pop .rbp 1))
      (.pop .r11 13)) s Q := by
  have hn : saved.length = 13 := by decide +kernel
  have h104 : 8 * saved.length ≤ (s.gpr .rsp).toNat := by rw [hn]; omega_arith
  have hi : 8 * ([Reg.rbp] : List Reg).length ≤ ((pushed saved s).gpr .rsp).toNat := by
    rw [pushed_rsp, hn, toNat_sub_ofNat (by omega_arith : 8 * 13 ≤ (s.gpr .rsp).toNat)]
    simp only [List.length_cons, List.length_nil]
    omega_arith
  have hE : (pushed saved s).gpr .rsp - BitVec.ofNat 64 (8 * ([Reg.rbp] : List Reg).length) =
      (entered s).gpr .rsp := (pushed_rsp _ _).symm
  have hES : (entered s).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 112 := entered_rsp s
  apply WP.frame (by decide +kernel) (by decide +kernel) (by decide) h104
  apply WP.frame (by decide) (by decide) (by decide) hi
  refine WP.mono hb ?_
  rintro t ⟨hsp, hw, hq⟩
  refine ⟨hsp, hw, fun m₁ u₁ f₁ => ⟨?_, ?_, fun m u f => ?_⟩⟩
  · dsimp only
    rw [popped_rsp, hsp, entered_rsp, pushed_rsp, hn]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul]
    bv_omega
  · dsimp only
    rw [popped_wr, hw]
    rfl
  · -- The outer pop reads its own frame, which the inner frame's loss leaves
    -- alone, and both frames are in the 112 bytes below `rsp`.
    rw [hE] at f₁
    have hP : (popped .rbp ([Reg.rbp] : List Reg).length t).gpr .rsp = (entered s).gpr .rsp + 8 := by
      rw [popped_rsp, hsp]; rfl
    have hr : ∀ i < saved.length,
        m₁.readW ((popped .rbp ([Reg.rbp] : List Reg).length t).gpr .rsp + BitVec.ofNat 64 (8 * i)) 64 =
          (popped .rbp ([Reg.rbp] : List Reg).length t).mem.readW
            ((popped .rbp ([Reg.rbp] : List Reg).length t).gpr .rsp + BitVec.ofNat 64 (8 * i)) 64 := by
      intro i hi'
      rw [hn] at hi'
      rw [popped_mem, hP, show (entered s).gpr .rsp + 8 + BitVec.ofNat 64 (8 * i) =
        (entered s).gpr .rsp + BitVec.ofNat 64 (8 + 8 * i) by
          rw [BitVec.add_assoc]; congr 1; bv_omega_arith]
      exact f₁.readW (Region.contains_self _ _) (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by simp only [List.length_singleton]; omega_arith)
          (by omega_arith)) (by decide)
    rw [popped_withMem hr]
    have fm : Frame [⟨(entered s).gpr .rsp, 112⟩] t.mem m := by
      refine (f₁.sub fun r hr => ?_).trans (f.sub fun r hr => ?_)
      · rw [List.mem_singleton.mp hr]
        refine ⟨_, List.mem_singleton_self _, ?_⟩
        rw [hES]; exact Offset.sub_below _ (Nat.le_refl _) (by simp only [List.length_singleton]; omega_arith)
      · rw [List.mem_singleton.mp hr]
        refine ⟨_, List.mem_singleton_self _, ?_⟩
        rw [hES, hn]; exact Offset.sub_below _ (by omega_arith) (by omega_arith)
    simpa only [hn, exited, List.length_cons, List.length_nil, Nat.reduceAdd] using hq m u fm

end VG.Proof.MillerRabin.X86_64
