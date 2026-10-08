import VerifiedGarbage.Proof.Weierstrass.WinLay
import VerifiedGarbage.Impl.Weierstrass.X86.Naf

/-! The eight-entry odd-multiple table and cached double and its disjoint scratch slots. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Proof.Mont

def nafTblSlots (K : WinCfg) : List Nat := (List.range 27).map fun i => K.tbl+32*i

def nafSlots (K : WinCfg) : List Nat := winRo K ++ winOther K ++ nafTblSlots K

def nafWrites (K : WinCfg) : List Nat := winOther K ++ nafTblSlots K

/-- The five-bit loop has eight odd multiples, one cached double, and 260 scalar bytes. -/
structure NafLay (K : WinCfg) (size : Nat) : Prop where
  size_le : size ≤ 8192
  n : K.M.n = 4
  lay : Lay K.M size (· ∈ nafSlots K)
  ro : ∀ x ∈ winRo K, x ∉ winOther K
  nodup : (winOther K).Nodup
  tbl : ∀ x ∈ winRo K ++ winOther K, x+32 ≤ K.tbl ∨ K.tbl+864 ≤ x
  bits : K.bits+260 ≤ size
  bits_w : ∀ w ∈ nafWrites K, K.bits+260 ≤ w ∨ w+32 ≤ K.bits
  bits_tmp : K.bits+260 ≤ K.M.tmp ∨ K.M.tmp+32 ≤ K.bits
  exy : K.E.y = K.E.x+32
  exz : K.E.z = K.E.x+64
  rxy : K.R.y = K.R.x+32
  rxz : K.R.z = K.R.x+64

/-- A coordinate of an entry from 1 through 9 is one of the table slots. -/
theorem nafTbl_mem (K : WinCfg) {a c : Nat} (ha : 1 ≤ a) (h9 : a ≤ 9) (hc : c < 3) :
    K.tbl+96*(a-1)+32*c ∈ nafTblSlots K := by
  apply List.mem_map.mpr
  refine ⟨3*(a-1)+c,List.mem_range.mpr (by omega),?_⟩
  omega

/-- Every coordinate of a table point belongs to the complete environment. -/
theorem nafTblPt_mem (K : WinCfg) (hn : K.M.n=4) {a : Nat} (ha : 1 ≤ a) (h9 : a ≤ 9) :
    ∀ x ∈ [(K.tblPt a).x,(K.tblPt a).y,(K.tblPt a).z],
      x ∈ nafSlots K := by
  intro x hx
  apply List.mem_append_right
  simp only [WinCfg.tblPt,hn,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact nafTbl_mem K ha h9 (c := 0) (by decide)
  · exact nafTbl_mem K ha h9 (c := 1) (by decide)
  · exact nafTbl_mem K ha h9 (c := 2) (by decide)

/-- The complete 864-byte table fits in the scratch allocation. -/
theorem NafLay.table_le {K : WinCfg} {size : Nat} (hL : NafLay K size) :
    K.tbl+864 ≤ size := by
  have h := hL.lay.le (K.tbl+32*26) (List.mem_append_right _
    (List.mem_map.mpr ⟨26,by decide,rfl⟩))
  rw [hL.n] at h
  omega

/-- The previous eight-entry layout is a sub-layout of this allocation. -/
theorem NafLay.old_slots {K : WinCfg} {size : Nat} (hL : NafLay K size) :
    ∀ x ∈ winSlots K, x ∈ nafSlots K := by
  intro x hx
  simp only [winSlots,nafSlots,List.mem_append] at hx ⊢
  rcases hx with hx | hx
  · exact Or.inl hx
  · apply Or.inr
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    apply List.mem_map.mpr
    refine ⟨i,List.mem_range.mpr (by have := List.mem_range.mp hi; omega),?_⟩
    simp only [hL.n]

/-- Existing coordinate and scratch-separation lemmas remain available for
the working points, while the new table includes the cached double. -/
theorem NafLay.toWinLay {K : WinCfg} {size : Nat} (hL : NafLay K size)
    (hJ : K.J=65) : WinLay K size := by
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
    · have hnew : x ∈ nafWrites K := by
        simp only [winWs,nafWrites,List.mem_append] at hx ⊢
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
theorem NafLay.rcbApart_DR {K : WinCfg} {size : Nat} (hL : NafLay K size) :
    RcbApart K.S K.D K.D K.R := by
  have hnd := hL.nodup
  have ha := hL.ro K.S.a (by simp [winRo])
  have hb := hL.ro K.S.b3 (by simp [winRo])
  simp only [winOther,rcbW,List.cons_append,List.nil_append,List.nodup_cons,
    List.mem_cons,List.not_mem_nil,or_false,not_or] at hnd ha hb
  refine ⟨?_,?_⟩ <;>
    simp only [rcbW,rcbR,List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,
      List.nodup_nil,and_true,forall_eq_or_imp,forall_eq] <;> grind

/-- The running odd multiple and cached double can be added into `D`. -/
theorem NafLay.rcbApart_twice {K : WinCfg} {size : Nat} (hL : NafLay K size) (hJ : K.J=65) :
    RcbApart K.S K.R (Naf.twice K) K.D := by
  have h := (hL.toWinLay hJ).rcbApart_D (Or.inl rfl)
  refine ⟨h.nodup,fun x hx hw => ?_⟩
  have he : x∈rcbR K.S K.R K.R ∨ x∈[(Naf.twice K).x,(Naf.twice K).y,(Naf.twice K).z] := by
    simp only [rcbR,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  rcases he with he | he
  · exact h.apart x he hw
  · have sep := hL.tbl x (List.mem_append_right _ (List.mem_append_right _ hw))
    simp only [Naf.twice,WinCfg.tblPt,hL.n,List.mem_cons,List.not_mem_nil,or_false] at he
    omega

/-- The initial double goes into the ninth point, outside the eight-entry odd table. -/
theorem NafLay.rcbApart_init {K : WinCfg} {size : Nat} (hL : NafLay K size) (hJ : K.J=65) :
    RcbApart K.S K.P K.P (Naf.twice K) := by
  let ts := [K.S.t0,K.S.t1,K.S.t2,K.S.t3,K.S.t4,K.S.t5]
  have ets (o : Pt) : rcbW K.S o=ts++[o.x,o.y,o.z] := rfl
  have hn := (hL.toWinLay hJ).other_ne.2.2.2.2.2.2.2.2.2
  rw [ets,List.nodup_append] at hn
  have hts : ∀ x∈ts, x∈winRo K++winOther K := rcbW_mem_other
  have ht : ∀ x∈winRo K++winOther K,
      x∉[(Naf.twice K).x,(Naf.twice K).y,(Naf.twice K).z] := by
    intro x hx he
    have sep := hL.tbl x hx
    simp only [Naf.twice,WinCfg.tblPt,hL.n,List.mem_cons,List.not_mem_nil,or_false] at he
    omega
  refine ⟨?_,?_⟩
  · rw [ets,List.nodup_append]
    refine ⟨hn.1,?_,fun x hx y hy he => ht x (hts x hx) (he ▸ hy)⟩
    simp only [Naf.twice,WinCfg.tblPt,hL.n,List.nodup_cons,List.mem_cons,List.not_mem_nil,
      or_false,not_or,List.nodup_nil,not_false_eq_true,and_true]
    and_intros <;> omega
  · intro x hx hw
    have hr : x∈winRo K := by
      simp only [rcbR,winRo,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
      grind
    rw [ets,List.mem_append] at hw
    rcases hw with hw | hw
    · exact hL.ro x hr (List.mem_append_right _ (List.mem_append_left _ hw))
    · exact ht x (List.mem_append_left _ hr) hw

end VG.Proof.Weierstrass.X86
