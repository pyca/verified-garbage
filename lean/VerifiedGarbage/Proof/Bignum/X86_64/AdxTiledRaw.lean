import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRows
import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderFrame
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFinish8

/-! Full raw product with every borrowed header byte restored. -/
namespace VG.Proof.Bignum.X86_64.AdxTiledProduct
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.Bignum.X86_64.AdxRect8 (rawBase)
open VG.Proof.Bignum.X86_64.AdxHeader (highPad)

theorem scratch_input {m m' : Mem} {B : Addr} {w a : Nat}
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hZ : slot w 8 ≤ 2^64)
    (hf : Outside B (slot w aAcc) (16*w+32) m m') :
    wv m' B (slot w a) w=wv m B (slot w a) w := by
  have sa := slot_le (w := w) ha
  have s1 := slot_sep (w := w) ha1
  have s2 := slot_sep (w := w) ha2
  exact hf.wv (by unfold slot aAcc aTmp at *; omega) (by omega)

theorem rawProduct_ok {s : State} {B : Addr} {Z w a b n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    {ps : List (Nat × Nat)} (hvs : Ops s.mem B w ps) {ca cb : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (hZ : slot w 8 ≤ Z) (hw : w < 2^31) (hwN : w=8*n) (hn : 0<n)
    (ha : a < 8) (hb : b < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) :
    WP isa (AdxTiledProduct.rawProduct ca cb) s fun t =>
      wv t.mem B (rawBase w) (2*w+2)=wv s.mem B (slot w a) w*wv s.mem B (slot w b) w ∧
      wv t.mem B (rawBase w) (2*w)=wv s.mem B (slot w a) w*wv s.mem B (slot w b) w ∧
      Outside B (slot w aAcc) (16*w+32) s.mem t.mem ∧ Keep mmRegs s t := by
  have nowrap := hs.nowrap
  have pads := AdxHeader.pads_bound hZ
  have rawZ : rawBase w+8*(2*w+2) ≤ Z := by unfold rawBase highPad at *; omega
  have Z64 : slot w 8 ≤ (2 : Nat)^64 := by omega
  unfold AdxTiledProduct.rawProduct
  refine WP.seq (WP.mono (adxSetupV_ok hs hd hh hZ (hvs.at pb) (hvs.lt pb)) fun u ⟨_,_,pu,wu,mu,ku⟩ => ?_)
  refine WP.seq (WP.mono (zeroWin8_ok (hs.congr ku.2.2) pu wu hwN hn (by omega) rawZ)
    fun v ⟨zv,ov,kv⟩ => ?_)
  rw [mu] at ov
  have ov' : Outside B (slot w aAcc) (16*w+32) s.mem v.mem := ov.mono (by omega) (by omega)
  have hv : Hdr v.mem B w mi := hh.of_outside ov (by unfold slot; omega)
  have kuv := ku.trans kv
  refine WP.seq (WP.mono (AdxHeader.save_ok (hs.congr kuv.2.2) ((kuv.gpr (by decide)).trans hd) hv hZ)
    fun x ⟨lo,hi,fx,kx⟩ => ?_)
  have ox : Outside B (slot w aAcc) (16*w+32) v.mem x.mem := by
    intro p hp
    apply fx p
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> simp only [] <;> unfold highPad at * <;> omega
  have hx : Hdr x.mem B w mi := hv.of_outside ox (by unfold slot; omega)
  have zx : wv x.mem B (rawBase w) (2*w)=0 := by
    rw [fx.wv_eq (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> simp only [] <;> simp only [rawBase,highPad] <;> omega) (by omega)]
    exact wv_zero fun k hk => zv k (by omega)
  have kuvx := kuv.trans kx
  refine WP.seq (WP.mono (rows_ok (hs.congr kuvx.2.2) ((kuvx.gpr (by decide)).trans hd)
    hx (hvs.of_outside (ov'.trans ox) (by unfold slot sFn hdrBytes; omega)) pa pb hZ hw hwN hn ha hb ha1 ha2 hb1 hb2 zx) fun y ⟨vy,hy,fy,ky⟩ => ?_)
  have kuvxy := kuvx.trans ky
  refine WP.mono (AdxHeader.restore_ok (hs.congr kuvxy.2.2) ((kuvxy.gpr (by decide)).trans hd) hy hZ)
    fun t ⟨lot,hit,zt,ft,kt⟩ => ?_
  have bodyFrame : Frm B [(slot w aAcc+16,16*w),(8*sFn 12,32)] x.mem y.mem := fy
  have restored := AdxHeader.restored_frame (by omega : highPad w+16 ≤ 2^64) lo hi fx bodyFrame lot hit ft
  have low : wv t.mem B (rawBase w) (2*w)=wv s.mem B (slot w a) w*wv s.mem B (slot w b) w := by
    rw [ft.wv_eq (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> simp only [] <;>
        simp only [rawBase,highPad,slot,hdrBytes,sFn] <;> omega) (by omega),vy,
      scratch_input ha ha1 ha2 Z64 (ov'.trans ox),scratch_input hb hb1 hb2 Z64 (ov'.trans ox)]
  refine ⟨?_,low,ov'.trans restored,(kuvxy.trans kt).mono (by decide)⟩
  have high : wv t.mem B (rawBase w+8*(2*w)) 2=0 := wv_zero fun k hk => by
    rw [show rawBase w+8*(2*w)+8*k=highPad w+8*k by unfold rawBase highPad; omega]
    exact zt k hk
  rw [wv_add,high,Nat.mul_zero,Nat.add_zero]; exact low

end VG.Proof.Bignum.X86_64.AdxTiledProduct
