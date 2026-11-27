module

public import VerifiedGarbage.Impl.Bignum.X86_64.AdxTiledProduct
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Row
import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderFrame
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFinish8
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTail
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRow
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! ### `Bignum.X86_64.AdxTiledRows`, which this module and modules that import it used -/

section

/-! The outer loop accumulates the exact product, one eight-word row at a time. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxTiledProduct
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Proof.Bignum.X86_64.AdxRect8 (rawBase)

structure Inv (s₀ : State) (B : Addr) (Z w a b k : Nat) (mi : BitVec 64) (s : State) : Prop where
  scr : Scr s B Z
  hdr : Hdr s.mem B w mi
  rdi : s.gpr .rdi = B
  indexI : word s.mem B (8*sFn 12) = BitVec.ofNat 64 (8*k)
  keep : Keep mmRegs s₀ s
  frame : Frm B (ranges w) s₀.mem s.mem
  val : wv s.mem B (rawBase w) (2*w) = wv s₀.mem B (slot w a) (8*k)*wv s₀.mem B (slot w b) w

private theorem product_step {L Q C A P X Y : Nat}
    (h : L+Q*C=A*Y+P*X*Y) : L+Q*C=(A+P*X)*Y := by grind

private theorem drop_carry {L Q C V : Nat} (h : L+Q*C=V) (hb : V<Q) : L=V := by
  have hc : C=0 := by
    by_contra ne
    have : Q ≤ Q*C := Nat.le_mul_of_pos_right _ (by omega_using [ne])
    omega_using [h, hb, this]
  simpa only [hc,Nat.mul_zero,Nat.add_zero] using h

theorem row_inv {s₀ s : State} {B : Addr} {Z w a b k n : Nat} {mi : BitVec 64}
    {ps : List (Nat × Nat)} (hv : Ops s₀.mem B w ps) {ca cb : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (hZ : slot w 8 ≤ Z) (hw : w < 2^31) (hwN : w=8*n) (hk : k<n)
    (ha : a < 8) (hb : b < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) (h : Inv s₀ B Z w a b k mi s) :
    WP isa (AdxTiledProduct.row ca cb) s fun t =>
      t.zf = some (decide (k+1=n)) ∧ Inv s₀ B Z w a b (k+1) mi t := by
  have nowrap := h.scr.nowrap
  have Z64 : slot w 8 ≤ (2 : Nat)^64 := by omega_using [hZ, nowrap]
  refine WP.mono (row_ok h.scr h.rdi h.hdr (frame_ops hv h.frame) pa pb hZ hw hwN (by omega_using [hk])
    (by omega_using [hwN, hk] : w=8*k+8+8*(n-k-1)) ha hb ha1 ha2 hb1 hb2 h.indexI)
    fun t ⟨zt,it,⟨c,eq⟩,ht,ft,kt⟩ => ?_
  have va := input_preserved ha ha1 ha2 (by omega_using [hwN, hk] : 8*k+8 ≤ w) Z64 h.frame
  have vb := input_preserved hb hb1 hb2 (by omega_using [] : 0+w ≤ w) Z64 h.frame
  simp only [Nat.mul_zero,Nat.add_zero] at vb
  rw [h.val,va,vb] at eq
  have val := product_step eq
  have append : wv s₀.mem B (slot w a) (8*(k+1)) =
      wv s₀.mem B (slot w a) (8*k)+2^(64*(8*k))*wv s₀.mem B (slot w a+8*(8*k)) 8 := by
    rw [show 8*(k+1)=8*k+8 by omega_using [],wv_add]
  rw [← append] at val
  have boundA : wv s₀.mem B (slot w a) (8*(k+1)) < (2 : Nat)^(64*w) :=
    Nat.lt_of_lt_of_le (wv_lt _ _ _ _) (Nat.pow_le_pow_right (by decide) (by omega_using [hwN, hk]))
  have bound := Nat.mul_lt_mul'' boundA (wv_lt s₀.mem B (slot w b) w)
  rw [← Nat.pow_add,show 64*w+64*w=128*w by omega_using []] at bound
  refine ⟨?_,⟨h.scr.congr kt.2.2,ht,(kt.gpr (by decide)).trans h.rdi,?_,
    (h.keep.trans kt).mono (by decide),h.frame.trans ft,drop_carry val bound⟩⟩
  · rw [zt]; exact congrArg some (decide_eq_decide.mpr (by omega_using [hwN]))
  · simpa only [show 8*(k+1)=8*k+8 by omega_using []] using it

theorem rows_ok {s : State} {B : Addr} {Z w a b n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca cb : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (hZ : slot w 8 ≤ Z) (hw : w < 2^31) (hwN : w=8*n) (hn : 0<n)
    (ha : a < 8) (hb : b < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (hz : wv s.mem B (rawBase w) (2*w)=0) :
    WP isa (AdxTiledProduct.rows ca cb) s fun t =>
      wv t.mem B (rawBase w) (2*w)=wv s.mem B (slot w a) w*wv s.mem B (slot w b) w ∧
      Hdr t.mem B w mi ∧ Frm B (ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have nowrap := hs.nowrap
  have iZ : 8*sFn 12+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sFn 12 < 32 by decide); omega_using [hZ, this]
  have init : WP isa (.block [.mov32 .rax (.imm 0),.store (hdr (sFn 12)) .rax]) s fun t =>
      t.mem=s.mem.writeW (off B (8*sFn 12)) (0 : BitVec 64) ∧ Keep [.rax] s t := by
    apply WP.keep [.rax] (Q := fun t => t.mem=s.mem.writeW (off B (8*sFn 12)) (0 : BitVec 64)) _ rfl
    xrun [State.ea,hdr,hd,hdrOff,hs.st iZ]
    rfl
  unfold AdxTiledProduct.rows
  refine WP.seq (WP.mono init fun u ⟨mu,ku⟩ => ?_)
  have ou : Outside B (8*sFn 12) 8 s.mem u.mem := by rw [mu]; exact writeW_outside _ _ _ (by decide)
  have fu : Frm B (ranges w) s.mem u.mem := by
    intro x hx
    apply ou x
    have := hx (8*sFn 12,32) (by simp [ranges]); omega_using [this]
  have h0 : Inv s B Z w a b 0 mi u :=
    ⟨hs.congr ku.2.2,frame_hdr hh fu,(ku.gpr (by decide)).trans hd,by rw [mu,word_writeW_self]; rfl,
      ku.mono (by decide),fu,by
        rw [ou.wv (by unfold rawBase slot hdrBytes sFn; omega_using []) (by unfold rawBase slot aAcc at *; omega_using [hZ, nowrap])]
        simpa only [Nat.mul_zero,wv,Nat.zero_mul] using hz⟩
  exact wp_upto (a := 0) (N := n) hn (Inv s B Z w a b · mi)
    (fun _ _ hk _ h => row_inv hv pa pb hZ hw hwN hk ha hb ha1 ha2 hb1 hb2 h)
    (fun _ h => ⟨by simpa only [← hwN] using h.val,h.hdr,h.frame,h.keep⟩) h0

end VG.Proof.Bignum.X86_64.AdxTiledProduct

end

end

/-! Full raw product with every borrowed header byte restored. -/

@[expose] public section

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
  exact hf.wv (by unfold slot aAcc aTmp at *; omega_using [s1, s2]) (by omega_using [hZ, sa])

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
  have rawZ : rawBase w+8*(2*w+2) ≤ Z := by unfold rawBase highPad at *; omega_using [pads]
  have Z64 : slot w 8 ≤ (2 : Nat)^64 := by omega_using [hZ, nowrap]
  unfold AdxTiledProduct.rawProduct
  refine WP.seq (WP.mono (adxSetupV_ok hs hd hh hZ (hvs.at pb) (hvs.lt pb)) fun u ⟨_,_,pu,wu,mu,ku⟩ => ?_)
  refine WP.seq (WP.mono (zeroWin8_ok (hs.congr ku.2.2) pu wu hwN hn (by omega_using [hw]) rawZ)
    fun v ⟨zv,ov,kv⟩ => ?_)
  rw [mu] at ov
  have ov' : Outside B (slot w aAcc) (16*w+32) s.mem v.mem := ov.mono (by omega_using []) (by omega_using [])
  have hv : Hdr v.mem B w mi := hh.of_outside ov (by unfold slot; omega_using [])
  have kuv := ku.trans kv
  refine WP.seq (WP.mono (AdxHeader.save_ok (hs.congr kuv.2.2) ((kuv.gpr (by decide)).trans hd) hv hZ)
    fun x ⟨lo,hi,fx,kx⟩ => ?_)
  have ox : Outside B (slot w aAcc) (16*w+32) v.mem x.mem := by
    intro p hp
    apply fx p
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> simp only [] <;> unfold highPad at * <;> omega_using [hp]
  have hx : Hdr x.mem B w mi := hv.of_outside ox (by unfold slot; omega_using [])
  have zx : wv x.mem B (rawBase w) (2*w)=0 := by
    rw [fx.wv_eq (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> simp only [] <;> simp only [rawBase,highPad] <;> omega_using []) (by omega_using [nowrap, rawZ])]
    exact wv_zero fun k hk => zv k (by omega_using [hk])
  have kuvx := kuv.trans kx
  refine WP.seq (WP.mono (rows_ok (hs.congr kuvx.2.2) ((kuvx.gpr (by decide)).trans hd)
    hx (hvs.of_outside (ov'.trans ox) (by unfold slot sFn hdrBytes; omega_using [])) pa pb hZ hw hwN hn ha hb ha1 ha2 hb1 hb2 zx) fun y ⟨vy,hy,fy,ky⟩ => ?_)
  have kuvxy := kuvx.trans ky
  refine WP.mono (AdxHeader.restore_ok (hs.congr kuvxy.2.2) ((kuvxy.gpr (by decide)).trans hd) hy hZ)
    fun t ⟨lot,hit,zt,ft,kt⟩ => ?_
  have bodyFrame : Frm B [(slot w aAcc+16,16*w),(8*sFn 12,32)] x.mem y.mem := fy
  have restored := AdxHeader.restored_frame (by omega_using [nowrap, pads] : highPad w+16 ≤ 2^64) lo hi fx bodyFrame lot hit ft
  have low : wv t.mem B (rawBase w) (2*w)=wv s.mem B (slot w a) w*wv s.mem B (slot w b) w := by
    rw [ft.wv_eq (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> simp only [] <;>
        simp only [rawBase,highPad,slot,hdrBytes,sFn] <;> omega_using []) (by omega_using [nowrap, rawZ]),vy,
      scratch_input ha ha1 ha2 Z64 (ov'.trans ox),scratch_input hb hb1 hb2 Z64 (ov'.trans ox)]
  refine ⟨?_,low,ov'.trans restored,(kuvxy.trans kt).mono (by decide)⟩
  have high : wv t.mem B (rawBase w+8*(2*w)) 2=0 := wv_zero fun k hk => by
    rw [show rawBase w+8*(2*w)+8*k=highPad w+8*k by unfold rawBase highPad; omega_using []]
    exact zt k hk
  rw [wv_add,high,Nat.mul_zero,Nat.add_zero]; exact low

/-- `rawProduct` without the header's save: the borrowed words change too,
as from `s` to a memory `m`, which the rest changes only in the accumulator. -/
theorem rawProductBare_ok {s : State} {B : Addr} {Z w a b n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    {ps : List (Nat × Nat)} (hvs : Ops s.mem B w ps) {ca cb : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (hZ : slot w 8 ≤ Z) (hw : w < 2^31) (hwN : w=8*n) (hn : 0<n)
    (ha : a < 8) (hb : b < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) :
    WP isa (AdxTiledProduct.rawProductBare ca cb) s fun t => ∃ m,
      Outside B (8*sFn 12) 32 s.mem m ∧
      wv t.mem B (rawBase w) (2*w)=wv s.mem B (slot w a) w*wv s.mem B (slot w b) w ∧
      Outside B (slot w aAcc) (16*w+32) m t.mem ∧ Keep mmRegs s t := by
  have nowrap := hs.nowrap
  have pads := AdxHeader.pads_bound hZ
  have rawZ : rawBase w+8*(2*w+2) ≤ Z := by unfold rawBase highPad at *; omega_using [pads]
  have Z64 : slot w 8 ≤ (2 : Nat)^64 := by omega_using [hZ, nowrap]
  unfold AdxTiledProduct.rawProductBare
  refine WP.seq (WP.mono (adxSetupV_ok hs hd hh hZ (hvs.at pb) (hvs.lt pb)) fun u ⟨_,_,pu,wu,mu,ku⟩ => ?_)
  refine WP.seq (WP.mono (zeroWin8_ok (hs.congr ku.2.2) pu wu hwN hn (by omega_using [hw]) rawZ)
    fun v ⟨zv,ov,kv⟩ => ?_)
  rw [mu] at ov
  have ov' : Outside B (slot w aAcc) (16*w+32) s.mem v.mem := ov.mono (by omega_using []) (by omega_using [])
  have hv : Hdr v.mem B w mi := hh.of_outside ov (by unfold slot; omega_using [])
  have kuv := ku.trans kv
  have zv' : wv v.mem B (rawBase w) (2*w)=0 := wv_zero fun k hk => zv k (by omega_using [hk])
  refine WP.seq (WP.mono (rows_ok (hs.congr kuv.2.2) ((kuv.gpr (by decide)).trans hd)
    hv (hvs.of_outside ov' (by unfold slot sFn hdrBytes; omega_using [])) pa pb hZ hw hwN hn ha hb ha1 ha2 hb1 hb2 zv')
    fun y ⟨vy,hy,fy,ky⟩ => ?_)
  have kuvy := kuv.trans ky
  refine WP.mono (AdxHeader.clear_ok (hs.congr kuvy.2.2) ((kuvy.gpr (by decide)).trans hd) hy hZ)
    fun t ⟨_,ot,kt⟩ => ?_
  have bodyFrame : Frm B [(slot w aAcc+16,16*w),(8*sFn 12,32)] v.mem y.mem := fy
  have fr : Frm B [(slot w aAcc,16*w+32),(8*sFn 12,32)] s.mem t.mem := fun x hx => by
    have h1 := hx _ (List.mem_cons_self ..)
    have h2 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    simp only [] at h1 h2
    rw [ot x (by unfold highPad; omega_using [h1]),bodyFrame x fun r hr => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> simp only [] <;> omega_arith]
    exact ov' x h1
  obtain ⟨m₁,o₁,o₂⟩ := AdxHeader.frm_split fr
  refine ⟨m₁,o₁,?_,o₂,(kuvy.trans kt).mono (by decide)⟩
  rw [ot.wv (by unfold rawBase highPad; omega_using []) (by unfold rawBase highPad at *; omega_using [nowrap, pads]),vy,
    scratch_input ha ha1 ha2 Z64 ov',scratch_input hb hb1 hb2 Z64 ov']

end VG.Proof.Bignum.X86_64.AdxTiledProduct
