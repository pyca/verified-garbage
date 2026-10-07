import VerifiedGarbage.Proof.Weierstrass.WinLay
import VerifiedGarbage.Impl.Weierstrass.AArch64.Jacobian

/-! The sixteen-entry public Jacobian table and its disjoint scratch slots. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Proof.Mont

def jacTblSlots (K : WinCfg) : List Nat := (List.range 48).map fun i => K.tbl+32*i

def jacWinSlots (K : WinCfg) : List Nat := winRo K ++ winOther K ++ jacTblSlots K

def jacWinWrites (K : WinCfg) : List Nat := winOther K ++ jacTblSlots K

/-- The five-bit loop has sixteen Jacobian entries and 260 scalar bits. -/
structure JacWinLay (K : WinCfg) (size : Nat) : Prop where
  n : K.M.n = 4
  lay : Lay K.M size (· ∈ jacWinSlots K)
  ro : ∀ x ∈ winRo K, x ∉ winOther K
  nodup : (winOther K).Nodup
  tbl : ∀ x ∈ winRo K ++ winOther K, x+32 ≤ K.tbl ∨ K.tbl+1536 ≤ x
  bits : K.bits+260 ≤ size
  bits_w : ∀ w ∈ jacWinWrites K, K.bits+260 ≤ w ∨ w+32 ≤ K.bits
  bits_tmp : K.bits+260 ≤ K.M.tmp ∨ K.M.tmp+32 ≤ K.bits
  exy : K.E.y = K.E.x+32
  exz : K.E.z = K.E.x+64
  rxy : K.R.y = K.R.x+32
  rxz : K.R.z = K.R.x+64

/-- A coordinate of an entry from 1 through 16 is one of the table slots. -/
theorem jacTbl_mem (K : WinCfg) {a c : Nat} (ha : 1 ≤ a) (h16 : a ≤ 16) (hc : c < 3) :
    K.tbl+96*(a-1)+32*c ∈ jacTblSlots K := by
  apply List.mem_map.mpr
  refine ⟨3*(a-1)+c,List.mem_range.mpr (by omega),?_⟩
  omega

/-- Every coordinate of a table point belongs to the complete environment. -/
theorem jacTblPt_mem (K : WinCfg) {a : Nat} (ha : 1 ≤ a) (h16 : a ≤ 16) :
    ∀ x ∈ [(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z],
      x ∈ jacWinSlots K := by
  intro x hx
  apply List.mem_append_right
  simp only [Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact jacTbl_mem K ha h16 (c := 0) (by decide)
  · exact jacTbl_mem K ha h16 (c := 1) (by decide)
  · exact jacTbl_mem K ha h16 (c := 2) (by decide)

/-- The complete 1536-byte table fits in the scratch allocation. -/
theorem JacWinLay.table_le {K : WinCfg} {size : Nat} (hL : JacWinLay K size) :
    K.tbl+1536 ≤ size := by
  have h := hL.lay.le (K.tbl+32*47) (List.mem_append_right _
    (List.mem_map.mpr ⟨47,by decide,rfl⟩))
  rw [hL.n] at h
  omega

/-- The previous eight-entry layout is a sub-layout of this allocation. -/
theorem JacWinLay.old_slots {K : WinCfg} {size : Nat} (hL : JacWinLay K size) :
    ∀ x ∈ winSlots K, x ∈ jacWinSlots K := by
  intro x hx
  simp only [winSlots,jacWinSlots,List.mem_append] at hx ⊢
  rcases hx with hx | hx
  · exact Or.inl hx
  · apply Or.inr
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    apply List.mem_map.mpr
    refine ⟨i,List.mem_range.mpr (by have := List.mem_range.mp hi; omega),?_⟩
    simp only [hL.n]

/-- Existing coordinate and scratch-separation lemmas remain available for
the working points, while the new table is twice as large. -/
theorem JacWinLay.toWinLay {K : WinCfg} {size : Nat} (hL : JacWinLay K size)
    (hJ : K.J=52) : WinLay K size := by
  refine ⟨?_,hL.ro,hL.nodup,?_,by rw [hL.n]; decide,by rw [hJ]; decide,?_,?_⟩
  · exact { le := fun x hx => hL.lay.le x (hL.old_slots x hx)
            mo := fun x hx => hL.lay.mo x (hL.old_slots x hx)
            tmp := fun x hx => hL.lay.tmp x (hL.old_slots x hx)
            apart := fun x y hx hy hxy => hL.lay.apart x y (hL.old_slots x hx) (hL.old_slots y hy) hxy }
  · intro x hx
    have := hL.tbl x hx
    rw [hL.n]; omega
  · have := hL.bits; rw [hJ]; omega
  · intro w hw
    simp only [winW,List.mem_append,List.mem_map,List.mem_singleton] at hw
    rcases hw with ⟨x,hx,rfl⟩ | rfl
    · have hnew : x ∈ jacWinWrites K := by
        simp only [winWs,jacWinWrites,List.mem_append] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl hx
        · apply Or.inr
          obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
          apply List.mem_map.mpr
          refine ⟨i,List.mem_range.mpr (by have := List.mem_range.mp hi; omega),?_⟩
          simp only [hL.n]
      have := hL.bits_w x hnew
      dsimp only
      rw [hL.n,hJ]; omega
    · have := hL.bits_tmp
      dsimp only
      rw [hL.n,hJ]; omega

/-- Reversing the two work points also separates all doubling operands. -/
theorem JacWinLay.rcbApart_DR {K : WinCfg} {size : Nat} (hL : JacWinLay K size) :
    RcbApart K.S K.D K.D K.R := by
  have hnd := hL.nodup
  have ha := hL.ro K.S.a (by simp [winRo])
  have hb := hL.ro K.S.b3 (by simp [winRo])
  simp only [winOther,rcbW,List.cons_append,List.nil_append,List.nodup_cons,
    List.mem_cons,List.not_mem_nil,or_false,not_or] at hnd ha hb
  refine ⟨?_,?_⟩ <;>
    simp only [rcbW,rcbR,List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,
      List.nodup_nil,and_true,forall_eq_or_imp,forall_eq] <;> grind

end VG.Proof.Weierstrass.AArch64
