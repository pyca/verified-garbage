import VerifiedGarbage.Proof.Weierstrass.WinLay
import VerifiedGarbage.Impl.Weierstrass.X86_64.Naf

/-! The eight-entry odd-multiple table and cached double and its disjoint scratch slots. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Proof.Mont

def nafTblSlots (K : WinCfg) : List Nat := (List.range 27).map fun i => K.tbl+8*K.M.n*i

def nafSlots (K : WinCfg) : List Nat := winRo K ++ winOther K ++ nafTblSlots K

def nafWrites (K : WinCfg) : List Nat := winOther K ++ nafTblSlots K

/-- The five-bit loop has eight odd multiples, one cached double, and
`64 n + 4` scalar bytes. -/
structure NafLay (K : WinCfg) (size : Nat) : Prop where
  n : K.M.n = 4 ∨ K.M.n = 6
  lay : Lay K.M size (· ∈ nafSlots K)
  ro : ∀ x ∈ winRo K, x ∉ winOther K
  nodup : (winOther K).Nodup
  tbl : ∀ x ∈ winRo K ++ winOther K, x+8*K.M.n ≤ K.tbl ∨ K.tbl+216*K.M.n ≤ x
  bits : K.bits+64*K.M.n+4 ≤ size
  bits_w : ∀ w ∈ nafWrites K, K.bits+64*K.M.n+4 ≤ w ∨ w+8*K.M.n ≤ K.bits
  bits_tmp : K.bits+64*K.M.n+4 ≤ K.M.tmp ∨ K.M.tmp+8*K.M.n ≤ K.bits
  exy : K.E.y = K.E.x+8*K.M.n
  exz : K.E.z = K.E.x+16*K.M.n
  rxy : K.R.y = K.R.x+8*K.M.n
  rxz : K.R.z = K.R.x+16*K.M.n

theorem nafTbl_slot (K : WinCfg) {i : Nat} (hi : i<27) : K.tbl+8*K.M.n*i ∈ nafTblSlots K :=
  List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩

/-- Every coordinate of a table point belongs to the complete environment. -/
theorem nafTblPt_mem (K : WinCfg) {a : Nat} (ha : 1 ≤ a) (h9 : a ≤ 9) :
    ∀ x ∈ [(K.tblPt a).x,(K.tblPt a).y,(K.tblPt a).z],
      x ∈ nafSlots K := by
  intro x hx
  apply List.mem_append_right
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl
  · rw [tblPt_x]; exact nafTbl_slot K (by omega)
  · rw [tblPt_y]; exact nafTbl_slot K (by omega)
  · rw [tblPt_z]; exact nafTbl_slot K (by omega)

/-- The complete table of nine points fits in the scratch allocation. -/
theorem NafLay.table_le {K : WinCfg} {size : Nat} (hL : NafLay K size) :
    K.tbl+216*K.M.n ≤ size := by
  have h := hL.lay.le (K.tbl+8*K.M.n*26) (List.mem_append_right _ (nafTbl_slot K (by decide)))
  omega

/-- The previous eight-entry layout is a sub-layout of this allocation. -/
theorem nafOld_slots (K : WinCfg) : ∀ x ∈ winSlots K, x ∈ nafSlots K := by
  intro x hx
  simp only [winSlots,nafSlots,List.mem_append] at hx ⊢
  rcases hx with hx | hx
  · exact Or.inl hx
  · apply Or.inr
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    exact nafTbl_slot K (by have := List.mem_range.mp hi; omega)

/-- Existing coordinate and scratch-separation lemmas remain available for
the working points, while the new table includes the cached double. -/
theorem NafLay.toWinLay {K : WinCfg} {size : Nat} (hL : NafLay K size)
    (hJ : 1≤K.J ∧ 4*K.J≤64*K.M.n+4) : WinLay K size := by
  have hn := hL.n
  refine ⟨?_,hL.ro,hL.nodup,?_,by omega,by omega,?_,?_⟩
  · exact { le := fun x hx => hL.lay.le x (nafOld_slots K x hx)
            mo := fun x hx => hL.lay.mo x (nafOld_slots K x hx)
            tmp := fun x hx => hL.lay.tmp x (nafOld_slots K x hx)
            apart := fun x y hx hy hxy =>
              hL.lay.apart x y (nafOld_slots K x hx) (nafOld_slots K y hy) hxy }
  · intro x hx
    have := hL.tbl x hx
    omega
  · have := hL.bits; omega
  · intro w hw
    simp only [winW,List.mem_append,List.mem_map,List.mem_singleton] at hw
    rcases hw with ⟨x,hx,rfl⟩ | rfl
    · have hnew : x ∈ nafWrites K := by
        simp only [winWs,nafWrites,List.mem_append] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl hx
        · apply Or.inr
          obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
          exact nafTbl_slot K (by have := List.mem_range.mp hi; omega)
      have := hL.bits_w x hnew
      dsimp only
      omega
    · have := hL.bits_tmp
      dsimp only
      omega

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
theorem NafLay.rcbApart_twice {K : WinCfg} {size : Nat} (hL : NafLay K size) (hJ : 1≤K.J ∧ 4*K.J≤64*K.M.n+4) :
    RcbApart K.S K.R (Naf.twice K) K.D := by
  have h := (hL.toWinLay hJ).rcbApart_D (Or.inl rfl)
  refine ⟨h.nodup,fun x hx hw => ?_⟩
  have he : x∈rcbR K.S K.R K.R ∨ x∈[(Naf.twice K).x,(Naf.twice K).y,(Naf.twice K).z] := by
    simp only [rcbR,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  rcases he with he | he
  · exact h.apart x he hw
  · have sep := hL.tbl x (List.mem_append_right _ (List.mem_append_right _ hw))
    simp only [Naf.twice,WinCfg.tblPt,List.mem_cons,List.not_mem_nil,or_false] at he
    have := hL.n
    omega

/-- The initial double goes into the ninth point, outside the eight-entry odd table. -/
theorem NafLay.rcbApart_init {K : WinCfg} {size : Nat} (hL : NafLay K size) (hJ : 1≤K.J ∧ 4*K.J≤64*K.M.n+4) :
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
    simp only [Naf.twice,WinCfg.tblPt,List.mem_cons,List.not_mem_nil,or_false] at he
    have := hL.n
    omega
  refine ⟨?_,?_⟩
  · rw [ets,List.nodup_append]
    refine ⟨hn.1,?_,fun x hx y hy he => ht x (hts x hx) (he ▸ hy)⟩
    simp only [Naf.twice,WinCfg.tblPt,List.nodup_cons,List.mem_cons,List.not_mem_nil,
      or_false,not_or,List.nodup_nil,not_false_eq_true,and_true]
    have := hL.n
    and_intros <;> omega
  · intro x hx hw
    have hr : x∈winRo K := by
      simp only [rcbR,winRo,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
      grind
    rw [ets,List.mem_append] at hw
    rcases hw with hw | hw
    · exact hL.ro x hr (List.mem_append_right _ (List.mem_append_left _ hw))
    · exact ht x (List.mem_append_left _ hr) hw

end VG.Proof.Weierstrass.X86_64
