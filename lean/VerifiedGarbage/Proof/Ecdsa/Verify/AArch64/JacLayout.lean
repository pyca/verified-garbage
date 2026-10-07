import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Points
import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Jacobian
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindow

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64.Cfg (jacWinCfg)

/-- The sixteen Jacobian entries occupy forty-eight field slots. -/
def jacTblI : List Nat := (List.range 48).map (WT + ·)

theorem jacTblSlots_eq (c : Cfg) (hn : c.n=4) :
    jacTblSlots (jacWinCfg c) = jacTblI.map c.sl := by
  simp only [jacTblSlots,jacTblI,List.map_map]
  apply List.map_congr_left
  intro i _
  change c.sl WT + 32*i = c.sl (WT+i)
  rw [sl_eq4 c (Nat.le_of_eq hn), sl_eq4 c (Nat.le_of_eq hn), hn]
  omega

theorem jacSlots_eq (c : Cfg) (hn : c.n=4) :
    jacWinSlots (jacWinCfg c) = (roI++otherI++jacTblI).map c.sl := by
  rw [jacWinSlots,jacTblSlots_eq c hn,List.map_append,List.map_append]; rfl

theorem jacWrites_eq (c : Cfg) (hn : c.n=4) :
    jacTreeWrites (jacWinCfg c) = slW c (otherI++jacTblI++[TMP]) := by
  rw [jacTreeWrites,jacWinWrites,jacTblSlots_eq c hn]
  simp only [slW,List.map_append,List.map_map]; rfl

theorem jacLay {c : Cfg} (hc : CfgOk c) (hn : c.n=4) : JacWinLay (jacWinCfg c) size := by
  have hSl : Lay c.MP' size (·∈(roI++otherI++jacTblI).map c.sl) := by
    refine ⟨?_,?_,?_,?_⟩
    · intro x hx
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
      have hb : i<136 := (show ∀ i∈roI++otherI++jacTblI,i<136 by decide) i hi
      change c.sl i + 8*c.n ≤ size
      rw [sl_eq4 c (Nat.le_of_eq hn), hn]; change 64+32*i+32≤8192; omega
    · intro x y hx hy hxy
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hy
      exact sl_apart4 c (Nat.le_of_eq hn) (fun e => hxy (e ▸ rfl))
    · intro x hx
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
      exact sl_apart4 c (Nat.le_of_eq hn) ((show ∀ i∈roI++otherI++jacTblI,i≠MP by decide) i hi)
    · intro x hx
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
      exact sl_apart4 c (Nat.le_of_eq hn) ((show ∀ i∈roI++otherI++jacTblI,i≠TMP by decide) i hi)
  refine ⟨hn,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [jacSlots_eq c hn]; exact hSl
  · exact map_sl_disj hc.n0 (l₁:=roI) (l₂:=otherI) (by decide)
  · exact map_sl_nodup hc.n0 (l:=otherI) (by decide)
  · intro x hx
    have hx' : x∈(roI++otherI).map c.sl := by rw [List.map_append]; exact hx
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx'
    have h := (show ∀ i∈roI++otherI,i<WT by decide) i hi
    change c.sl i+32≤c.sl WT ∨ c.sl WT+1536≤c.sl i
    rw [sl_eq4 c (Nat.le_of_eq hn), sl_eq4 c (Nat.le_of_eq hn), hn]
    simp only [WT] at h ⊢
    omega
  · change c.sl WB+260≤8192
    rw [sl_eq4 c (Nat.le_of_eq hn), hn]; decide
  · intro w hw
    have he : jacWinWrites (jacWinCfg c)=(otherI++jacTblI).map c.sl := by
      rw [jacWinWrites,jacTblSlots_eq c hn,List.map_append]; rfl
    rw [he] at hw
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
    have hb := (show ∀ i∈otherI++jacTblI,i<WB ∨ WT≤i by decide) i hi
    change c.sl WB+260≤c.sl i ∨ c.sl i+32≤c.sl WB
    rw [sl_eq4 c (Nat.le_of_eq hn), sl_eq4 c (Nat.le_of_eq hn), hn]
    simp only [WB,WT] at hb ⊢
    omega
  · change c.sl WB+260≤c.sl TMP ∨ c.sl TMP+32≤c.sl WB
    rw [sl_eq4 c (Nat.le_of_eq hn), sl_eq4 c (Nat.le_of_eq hn), hn]; decide
  · change c.sl TY=c.sl TX+32; rw [sl_eq4 c (Nat.le_of_eq hn), sl_eq4 c (Nat.le_of_eq hn), hn]; rfl
  · change c.sl TZ=c.sl TX+64; rw [sl_eq4 c (Nat.le_of_eq hn), sl_eq4 c (Nat.le_of_eq hn), hn]; rfl
  · change c.sl RY=c.sl RX+32; rw [sl_eq4 c (Nat.le_of_eq hn), sl_eq4 c (Nat.le_of_eq hn), hn]; rfl
  · change c.sl RZ=c.sl RX+64; rw [sl_eq4 c (Nat.le_of_eq hn), sl_eq4 c (Nat.le_of_eq hn), hn]; rfl

theorem jacAligned (c : Cfg) (hn : c.n=4) : Aligned (jacWinCfg c).M (·∈jacWinSlots (jacWinCfg c)) := by
  refine ⟨?_,MP'_A c,fun _ _ h => nomatch (callOf_small (M := c.MP') (Nat.le_of_eq hn)).symm.trans h⟩
  intro x hx
  rw [jacSlots_eq c hn] at hx
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
  exact sl_mod8 c i

end VG.Proof.Ecdsa.Verify.AArch64
