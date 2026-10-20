module

public import VerifiedGarbage.Impl.MillerRabin.X86_64.Round
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # The shared round's two fixed frames -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Impl.MillerRabin.X86_64

def entered (s : State) : State := pushed [.rbp] (pushed saved s)

private theorem saved_length : saved.length = 13 := rfl

private theorem pushed_mem (rs : List Reg) (s : State) : (pushed rs s).mem = (pushRegs s rs).mem := rfl

private theorem entered_mem (s : State) : (entered s).mem = (pushRegs (pushed saved s) [.rbp]).mem := rfl

theorem entered_rsp (s : State) : (entered s).gpr .rsp = s.gpr .rsp - 112#64 := by
  simp only [entered, pushed_rsp, saved_length, List.length_cons, List.length_nil]
  bv_omega

theorem entered_gpr (s : State) {r : Reg} (hr : r ≠ .rsp) :
    (entered s).gpr r = s.gpr r :=
  (pushed_gpr _ _ hr).trans (pushed_gpr _ _ hr)

theorem entered_wr (s : State) :
    (entered s).wr = [⟨s.gpr .rsp - 112#64, 8⟩, ⟨s.gpr .rsp - 104#64, 104⟩] ++ s.wr := by
  have he : (pushed saved s).gpr .rsp - 8#64 = s.gpr .rsp - 112#64 := by
    have h := entered_rsp s
    simpa only [entered, pushed_rsp, List.length_cons, List.length_nil, Nat.reduceMul, Nat.reduceAdd] using h
  simp only [entered, pushed_wr, he, saved_length, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, Nat.reduceMul, Nat.reduceAdd]


theorem entered_frame (s : State) (hn : 120 ≤ (s.gpr .rsp).toNat) :
    Frame [⟨s.gpr .rsp - 112#64, 112⟩] s.mem (entered s).mem := by
  have h104 : 8 * saved.length ≤ (s.gpr .rsp).toNat := by rw [saved_length]; omega_arith
  have ho : Frame [⟨s.gpr .rsp - 104#64, 104⟩] s.mem (pushed saved s).mem := by
    simpa only [saved_length, Nat.reduceMul, pushed_mem] using (pushRegs_mem s saved (by decide +kernel) h104).1
  have hs : (pushed saved s).gpr .rsp = s.gpr .rsp - 104#64 := by simp only [pushed_rsp, saved_length, Nat.reduceMul]
  have h8 : 8 * ([Reg.rbp] : List Reg).length ≤ ((pushed saved s).gpr .rsp).toNat := by
    rw [hs, toNat_sub_ofNat (by omega_arith : 104 ≤ (s.gpr .rsp).toNat)]
    simp only [List.length_cons, List.length_nil]
    omega_arith
  have hi : Frame [⟨s.gpr .rsp - 112#64, 8⟩] (pushed saved s).mem (entered s).mem := by
    have hp := (pushRegs_mem (pushed saved s) [.rbp] (by decide) h8).1
    have he : (pushed saved s).gpr .rsp - 8#64 = s.gpr .rsp - 112#64 := by
      rw [hs]
      bv_omega
    change Frame [⟨(pushed saved s).gpr .rsp - 8#64, 8⟩] (pushed saved s).mem
      (pushRegs (pushed saved s) [.rbp]).mem at hp
    rw [entered_mem, ← he]
    exact hp
  refine (ho.sub (fun r hr => ?_)).trans (hi.sub (fun r hr => ?_))
  · simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub_below _ (by decide : 104 ≤ 112) (by decide)⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide : 8 ≤ 112)⟩

private theorem inner_frame (s : State) (hn : 120 ≤ (s.gpr .rsp).toNat) :
    Frame [⟨s.gpr .rsp - 112#64, 8⟩] (pushed saved s).mem (entered s).mem := by
  have hs : (pushed saved s).gpr .rsp = s.gpr .rsp - 104#64 := by simp only [pushed_rsp, saved_length, Nat.reduceMul]
  have h8 : 8 * ([Reg.rbp] : List Reg).length ≤ ((pushed saved s).gpr .rsp).toNat := by
    rw [hs, toNat_sub_ofNat (by omega_arith : 104 ≤ (s.gpr .rsp).toNat)]
    simp only [List.length_cons, List.length_nil]
    omega_arith
  have hp := (pushRegs_mem (pushed saved s) [.rbp] (by decide) h8).1
  change Frame [⟨(pushed saved s).gpr .rsp - 8#64, 8⟩] (pushed saved s).mem
    (pushRegs (pushed saved s) [.rbp]).mem at hp
  have he : (pushed saved s).gpr .rsp - 8#64 = s.gpr .rsp - 112#64 := by rw [hs]; bv_omega
  rw [entered_mem, ← he]
  exact hp

theorem entered_saved (s : State) (hn : 120 ≤ (s.gpr .rsp).toNat) {j : Nat} (hj : j < saved.length) :
    (entered s).mem.readW (s.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64 = s.gpr saved[j] := by
  have hj13 : j < 13 := by simpa only [saved_length] using hj
  have h104 : 8 * saved.length ≤ (s.gpr .rsp).toNat := by rw [saved_length]; omega_arith
  have ho := (pushRegs_mem s saved (by decide +kernel) h104).2 j hj
  change (pushed saved s).mem.readW (s.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64 = s.gpr saved[j] at ho
  refine Eq.trans (b := (pushed saved s).mem.readW (s.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64) ?_ ho
  apply (inner_frame s hn).readW (r := ⟨s.gpr .rsp - 104#64, 104⟩)
  · exact Offset.contains_below _ (by omega_arith) (by omega_arith) (by decide)
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    rw [Offset.sub_ofNat_eq (s.gpr .rsp) (by decide : 104 ≤ 112)]
    exact Offset.disjoint_base _ (by decide) (by decide)
  · decide

theorem entered_rbp (s : State) (hn : 120 ≤ (s.gpr .rsp).toNat) :
    (entered s).mem.readW (s.gpr .rsp - 112#64) 64 = s.gpr .rbp := by
  have hs : (pushed saved s).gpr .rsp = s.gpr .rsp - 104#64 := by simp only [pushed_rsp, saved_length, Nat.reduceMul]
  have h8 : 8 * ([Reg.rbp] : List Reg).length ≤ ((pushed saved s).gpr .rsp).toNat := by
    rw [hs, toNat_sub_ofNat (by omega_arith : 104 ≤ (s.gpr .rsp).toNat)]
    simp only [List.length_cons, List.length_nil]
    omega_arith
  have hp := (pushRegs_mem (pushed saved s) [.rbp] (by decide) h8).2 0 (by decide)
  have he : (pushed saved s).gpr .rsp - 8#64 = s.gpr .rsp - 112#64 := by rw [hs]; bv_omega
  simpa only [entered_mem, Nat.zero_add, Nat.reduceMul, he, List.getElem_cons_zero,
    pushed_gpr _ _ (by decide : Reg.rbp ≠ Reg.rsp)] using hp

theorem entered_load (s : State) {d : Nat} (hlo : 8 ≤ d) (hhi : d + 8 ≤ 112) :
    InRegions ((entered s).rd ++ (entered s).wr) ((entered s).gpr .rsp + BitVec.ofNat 64 d) 8 := by
  refine ⟨⟨s.gpr .rsp - 104#64, 104⟩, List.mem_append_right _ ?_, ?_⟩
  · rw [entered_wr]
    simp
  · have he : (entered s).gpr .rsp + BitVec.ofNat 64 d =
        s.gpr .rsp - 104#64 + BitVec.ofNat 64 (d - 8) := by
      rw [entered_rsp]
      bv_omega
    rw [he]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)

theorem popped_rbp (s : State) : (popped .rbp 1 s).gpr .rbp = s.mem.readW (s.gpr .rsp) 64 := by
  simp [popped, popReg, State.setReg]

theorem entered_saved_at (s : State) (hn : 120 ≤ (s.gpr .rsp).toNat) {j : Nat} (hj : j < saved.length) :
    (entered s).mem.readW ((entered s).gpr .rsp + BitVec.ofNat 64 (104 - 8 * j)) 64 = s.gpr saved[j] := by
  have hj13 : j < 13 := by simpa only [saved_length] using hj
  have ha : (entered s).gpr .rsp + BitVec.ofNat 64 (104 - 8 * j) =
      s.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1)) := by
    rw [entered_rsp]
    bv_omega
  rw [ha]
  exact entered_saved s hn hj

end VG.Proof.MillerRabin.X86_64
