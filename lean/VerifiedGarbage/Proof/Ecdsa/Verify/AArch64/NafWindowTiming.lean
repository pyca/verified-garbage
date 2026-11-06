module

public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Jacobian
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafWindowTiming
public import VerifiedGarbage.Proof.Ecdh.AArch64.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafWindow
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits

/-! ## `JacLayout` -/

@[expose] public section

section

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
  omega_arith

theorem jacSlots_eq (c : Cfg) (hn : c.n=4) :
    jacWinSlots (jacWinCfg c) = (roI++otherI++jacTblI).map c.sl := by
  rw [jacWinSlots,jacTblSlots_eq c hn,List.map_append,List.map_append]; rfl

theorem jacLay {c : Cfg} (hc : CfgOk c) (hn : c.n=4) : JacWinLay (jacWinCfg c) size := by
  have hSl : Lay c.MP' size (·∈(roI++otherI++jacTblI).map c.sl) := by
    refine ⟨?_,?_,?_,?_⟩
    · intro x hx
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
      have hb : i<136 := (show ∀ i∈roI++otherI++jacTblI,i<136 by decide) i hi
      change c.sl i + 8*c.n ≤ size
      rw [sl_eq4 c (Nat.le_of_eq hn), hn]; change 64+32*i+32≤8192; omega_arith
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
    omega_arith
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
    omega_arith
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

end

/-! ## `JacWinPrep` -/

/-! ## `JacWindow` -/

/-! ## `NafWinPrep` -/

/-! ## `NafWindow` -/

/-! ## `JacWindowTiming` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (V)
open VG.Impl.Ecdsa.Verify.AArch64.Cfg (jacWinCfg jacWinPrep)

structure JacWinState (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s : State) : Prop where
  scr : Scr s base size
  fixed : ∃ g, Fixed c base g s.mem
  px : sv c base s PX<c.C.p
  py : sv c base s PY<c.C.p
  rep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
    (tmv c.C c.n base s (c.sl ONEP)) P
  scalar : sv c base s V=k

structure JacWinPublic (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s t : State) : Prop where
  left : JacWinState c base P k s
  right : JacWinState c base P k t
  sp : s.sp=t.sp
  px : tmv c.C c.n base s (c.sl PX)=tmv c.C c.n base t (c.sl PX)
  py : tmv c.C c.n base s (c.sl PY)=tmv c.C c.n base t (c.sl PY)

theorem JacWinPublic.fields {c : Cfg} {base : Addr} {P : Point c.C} {k : Nat} {s t : State}
    (h : JacWinPublic c base P k s t) :
    ∀ x∈winRo (jacWinCfg c),tmv c.C c.n base s x=tmv c.C c.n base t x := by
  obtain ⟨_,fs⟩ := h.left.fixed
  obtain ⟨_,ft⟩ := h.right.fixed
  intro x hx
  simp only [winRo,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · change toM _ _ (wordsVal s.mem base (c.sl AP) c.n)=toM _ _ (wordsVal t.mem base (c.sl AP) c.n)
    rw [fs.ap,ft.ap]
  · change toM _ _ (wordsVal s.mem base (c.sl BM) c.n)=toM _ _ (wordsVal t.mem base (c.sl BM) c.n)
    rw [fs.bm,ft.bm]
  · change toM _ _ (wordsVal s.mem base (c.sl ZERO) c.n)=toM _ _ (wordsVal t.mem base (c.sl ZERO) c.n)
    rw [fs.zero,ft.zero]
  · exact h.px
  · exact h.py
  · change toM _ _ (wordsVal s.mem base (c.sl ONEP) c.n)=toM _ _ (wordsVal t.mem base (c.sl ONEP) c.n)
    rw [fs.onep,ft.onep]

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `NafWindowTiming` -/

