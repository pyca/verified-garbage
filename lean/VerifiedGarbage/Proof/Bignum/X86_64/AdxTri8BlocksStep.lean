import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8BlocksFrame

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.Bignum.X86_64.AdxRect8 (rawBase)

theorem blockStep_ok {s₀ s : State} {B : Addr} {Z w a k n : Nat} {mi : BitVec 64}
    (hZ : slot w 8≤Z) (hw : w<2^31) (hwN : w=8*n) (hk : k<n)
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    (hz : ∀ j<2*w, word s₀.mem B (rawBase w+8*j)=0)
    (h : BlocksInv s₀ B Z w a k mi s) :
    WP isa (.seq (AdxTri8.block a) (.block AdxTri8.nextBlock)) s fun t =>
      t.zf=some (decide (k+1=n)) ∧ BlocksInv s₀ B Z w a (k+1) mi t := by
  have nowrap := h.scr.nowrap
  have Z64 : slot w 8≤(2 : Nat)^64 := by omega
  have ar := AdxRect8.tile_ranges (by omega : 8*k+8≤w) (by omega : 8*k+8≤w) ha ha1 ha2
  have zero : ∀ q<16, word s.mem B (rawBase w+128*k+8*q)=0 := by
    intro q hq
    rw [h.frame.word_eq (by
      intro r hr
      simp only [diagonalRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> simp only [] <;> simp only [rawBase,slot,hdrBytes,sFn] <;> omega)
      (by unfold rawBase at *; omega)]
    rw [show rawBase w+128*k+8*q=rawBase w+8*(16*k+q) by omega]
    exact hz (16*k+q) (by omega)
  refine WP.seq (WP.mono (fullBlock_ok h.scr h.rdi h.hdr hZ ha ha1 ha2 (by omega) h.indexI
    (by simpa only [rawBase,Nat.mul_zero,Nat.add_zero,show 16*(8*k)=128*k by omega] using zero 0 (by decide))
    (by simpa only [rawBase,show 16*(8*k)=128*k by omega,show 8*15=120 from rfl] using zero 15 (by decide)))
    fun u ⟨vu,ou,ku⟩ => ?_)
  have indexU : word u.mem B (8*sFn 12)=BitVec.ofNat 64 (8*k) := by
    rw [ou.word (by unfold slot hdrBytes sFn; omega) (by decide)]; exact h.indexI
  have headerU := h.hdr.of_outside ou (by unfold slot; omega)
  refine WP.mono (AdxTiledProduct.nextRow_ok (h.scr.congr ku.2.2) ((ku.gpr (by decide)).trans h.rdi)
    headerU hZ (by omega) (by omega) indexU) fun t ⟨mt,zt,kt⟩ => ?_
  have ot : Outside B (8*sFn 12) 8 u.mem t.mem := by rw [mt]; exact writeW_outside _ _ _ (by decide)
  have fu : Frm B (diagonalRanges w (k+1)) s.mem u.mem := by
    intro x hx
    apply ou x
    have := hx (rawBase w,128*(k+1)) (by simp [diagonalRanges])
    unfold rawBase at *; omega
  have ft : Frm B (diagonalRanges w (k+1)) u.mem t.mem := Frm.of_outside ot (by simp [diagonalRanges])
  have old : Frm B (diagonalRanges w (k+1)) s₀.mem s.mem := by
    intro x hx
    apply h.frame x
    intro r hr
    simp only [diagonalRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · have := hx (rawBase w,128*(k+1)) (by simp [diagonalRanges]); simp only []; omega
    · exact hx _ (by simp [diagonalRanges])
  have finalFrame := (old.trans fu).trans ft
  have low : wv u.mem B (rawBase w) (16*k)=wv s.mem B (rawBase w) (16*k) :=
    ou.wv (by unfold rawBase; omega) (by unfold rawBase at *; omega)
  have resultU : wv u.mem B (rawBase w+8*(16*k)) 16=
      AdxSquare.crossValue s₀.mem B (slot w a+64*k) 8 := by
    rw [show rawBase w+8*(16*k)=slot w aAcc+16+16*(8*k) by unfold rawBase; omega,vu,
      diagonal_input ha ha1 ha2 (by omega) (by omega) Z64 h.frame,
      show slot w a+8*(8*k)=slot w a+64*k by omega]
  refine ⟨?_,⟨h.scr.congr (ku.trans kt).2.2,diagonal_hdr h.hdr (fu.trans ft),
    ((ku.trans kt).gpr (by decide)).trans h.rdi,?_,(h.keep.trans (ku.trans kt)).mono (by decide),finalFrame,?_⟩⟩
  · rw [zt]; exact congrArg some (decide_eq_decide.mpr (by omega))
  · rw [mt,word_writeW_self,show 8*(k+1)=8*k+8 by omega]
  · rw [ot.wv (by unfold rawBase slot hdrBytes sFn; omega) (by unfold rawBase at *; omega),
      show 16*(k+1)=16*k+16 by omega,wv_add,low,h.val,resultU,blockCross]
    rw [show 64*(16*k)=1024*k by omega]

end VG.Proof.Bignum.X86_64.AdxTri8
