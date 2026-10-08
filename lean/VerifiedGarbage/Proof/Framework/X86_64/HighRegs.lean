import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.X86_64.ZFrame

/-! # AVX-512 high registers: lanes and preservation -/

namespace VG.X86_64

/-- The high registers are unchanged. Low vector writes do not imply this
through `ZFrame`, whose statement intentionally concerns only low registers. -/
structure HKeep (s s' : State) : Prop where
  ymm : s'.ymmH = s.ymmH
  hi : s'.zmmHiH = s.zmmHiH

theorem HKeep.refl (s : State) : HKeep s s := ⟨rfl, rfl⟩

theorem HKeep.trans {s t u : State} (h : HKeep s t) (h' : HKeep t u) : HKeep s u :=
  ⟨h'.ymm.trans h.ymm, h'.hi.trans h.hi⟩

theorem HKeep.lane {s t : State} (h : HKeep s t) (r : HReg) (i : Nat) :
    t.zlaneH r i = s.zlaneH r i := by
  simp only [State.zlaneH, h.ymm, h.hi]

theorem HKeep.zop (o : ZOp) (s : State) : HKeep s (o.exec s) := by
  cases o <;> exact ⟨rfl, rfl⟩

@[simp] theorem zlane_zbinH (op : ZKeyOp) (d a : XReg) (b : HReg) (s : State) (r : XReg)
    {i : Nat} (hi : i < 4) :
    ((ZOp.zbinH op d a b).exec s).zlane r i =
      if r = d then op.sse.eval (s.zlane a i) (s.zlaneH b i) else s.zlane r i := by
  simp only [ZOp.exec]
  rw [State.zlane_setZ _ _ _ _ _ _ _ hi,
    pick4_lanes (fun i => op.sse.eval (s.zlane a i) (s.zlaneH b i)) hi]

theorem State.zlaneH_setZH (s : State) (d r : HReg) (a b c e : BitVec 128)
    {i : Nat} (hi : i < 4) :
    (s.setZH d a b c e).zlaneH r i = if r = d then pick4 a b c e i else s.zlaneH r i := by
  by_cases h : r = d
  · subst h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    all_goals simp [State.zlaneH, State.setZH, pick4]
    all_goals
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
      simp [hj]
  · simp [State.zlaneH, State.setZH, h]

theorem State.setZH_zframe (s : State) (r : HReg) (a b c d : BitVec 128) :
    ZFrame [] s (s.setZH r a b c d) := ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩

end VG.X86_64
