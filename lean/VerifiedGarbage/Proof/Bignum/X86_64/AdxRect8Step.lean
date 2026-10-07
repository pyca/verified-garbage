import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8At

/-! One complete rectangular row step advances the public column counter. -/
namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)

theorem rowStep_ok {s : State} {B : Addr} {Z w i j : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hw : w < 2^31) (hi : i+8 ≤ w) (hj : j+8 ≤ w)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (hidx : word s.mem B (8*sFn 12) = BitVec.ofNat 64 i)
    (hjdx : word s.mem B (8*sFn 13) = BitVec.ofNat 64 j) :
    let e := slot w aAcc+16+8*(i+j)
    WP isa (AdxRect8.rowStep ca cb) s fun t =>
      t.zf = some (decide (j+8=w)) ∧
      word t.mem B (8*sFn 13) = BitVec.ofNat 64 (j+8) ∧
      wv t.mem B e 16 + 2^1024 * (word t.mem B carryOffset).toNat =
        wv s.mem B e 16 + wv s.mem B (slot w a+8*i) 8 * wv s.mem B (slot w b+8*j) 8 +
          2^512 * (word s.mem B carryOffset).toNat ∧
      (word t.mem B carryOffset).toNat ≤ 2 ∧
      ((word s.mem B carryOffset).toNat ≤ 1 → (word t.mem B carryOffset).toNat ≤ 1) ∧
      Hdr t.mem B w mi ∧ Frm B [(e,128),(carryOffset,8),(8*sFn 13,8)] s.mem t.mem ∧ t.gpr .rsi = off B (e+64) ∧ Keep mmRegs s t := by
  dsimp only
  unfold AdxRect8.rowStep
  have hn := hs.nowrap
  let e := slot w aAcc+16+8*(i+j)
  have eZ : e+128 ≤ Z := by have := tile_ranges hi hj ha ha1 ha2; omega
  have cZ : carryOffset+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sFn 14 < 32 by decide)
    unfold carryOffset; omega
  have idxZ : 8*sFn 13+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sFn 13 < 32 by decide); omega
  have eH : hdrBytes ≤ e := by unfold e slot; omega
  refine WP.seq (WP.mono (tileAt_ok hs hd hh hZ hi hj hv pa pb ha hb ha1 ha2 hb1 hb2 hidx hjdx)
    fun u ⟨eq,bd,one,hu,fr,ptr,ku⟩ => ?_)
  have ju : word u.mem B (8*sFn 13) = BitVec.ofNat 64 j := by
    rw [fr.word_eq (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> simp only [] <;>
        unfold carryOffset sFn e slot hdrBytes aAcc at * <;> omega) (by omega)]
    exact hjdx
  refine WP.mono (nextColumn_ok (hs.congr ku.2.2) ((ku.gpr (by decide)).trans hd)
    hu hZ (by omega) (by omega) ju) fun t ⟨mt,zt,kt⟩ => ?_
  have ot : Outside B (8*sFn 13) 8 u.mem t.mem := by
    rw [mt]; exact writeW_outside _ _ _ (by omega)
  have vt : wv t.mem B e 16 = wv u.mem B e 16 :=
    ot.wv (by unfold sFn hdrBytes at *; omega) (by omega)
  have ct : word t.mem B carryOffset = word u.mem B carryOffset :=
    ot.word (by unfold carryOffset sFn; omega) (by omega)
  have fr' : Frm B [(e,128),(carryOffset,8),(8*sFn 13,8)] s.mem t.mem :=
    (fr.mono (by simp [e])).trans (Frm.of_outside ot (by simp))
  refine ⟨zt,?_,?_,?_,?_,frame_hdr hh eH fr',fr',(kt.gpr (by decide)).trans ptr,(ku.trans kt).mono (by decide)⟩
  · rw [mt,word_writeW_self]
  · dsimp only [e] at vt
    rw [vt,ct]; exact eq
  · rw [ct]; exact bd
  · rw [ct]; exact one

end VG.Proof.Bignum.X86_64.AdxRect8
