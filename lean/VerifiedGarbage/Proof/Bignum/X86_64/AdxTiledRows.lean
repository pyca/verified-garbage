import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRow

/-! The outer loop accumulates the exact product, one eight-word row at a time. -/
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
    have : Q ≤ Q*C := Nat.le_mul_of_pos_right _ (by omega)
    omega
  simpa only [hc,Nat.mul_zero,Nat.add_zero] using h

theorem row_inv {s₀ s : State} {B : Addr} {Z w a b k n : Nat} {mi : BitVec 64}
    (hZ : slot w 8 ≤ Z) (hw : w < 2^31) (hwN : w=8*n) (hk : k<n)
    (ha : a < 8) (hb : b < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) (h : Inv s₀ B Z w a b k mi s) :
    WP isa (AdxTiledProduct.row a b) s fun t =>
      t.zf = some (decide (k+1=n)) ∧ Inv s₀ B Z w a b (k+1) mi t := by
  have nowrap := h.scr.nowrap
  have Z64 : slot w 8 ≤ (2 : Nat)^64 := by omega
  refine WP.mono (row_ok h.scr h.rdi h.hdr hZ hw hwN (by omega)
    (by omega : w=8*k+8+8*(n-k-1)) ha hb ha1 ha2 hb1 hb2 h.indexI)
    fun t ⟨zt,it,⟨c,eq⟩,ht,ft,kt⟩ => ?_
  have va := input_preserved ha ha1 ha2 (by omega : 8*k+8 ≤ w) Z64 h.frame
  have vb := input_preserved hb hb1 hb2 (by omega : 0+w ≤ w) Z64 h.frame
  simp only [Nat.mul_zero,Nat.add_zero] at vb
  rw [h.val,va,vb] at eq
  have val := product_step eq
  have append : wv s₀.mem B (slot w a) (8*(k+1)) =
      wv s₀.mem B (slot w a) (8*k)+2^(64*(8*k))*wv s₀.mem B (slot w a+8*(8*k)) 8 := by
    rw [show 8*(k+1)=8*k+8 by omega,wv_add]
  rw [← append] at val
  have boundA : wv s₀.mem B (slot w a) (8*(k+1)) < (2 : Nat)^(64*w) :=
    Nat.lt_of_lt_of_le (wv_lt _ _ _ _) (Nat.pow_le_pow_right (by decide) (by omega))
  have bound := Nat.mul_lt_mul'' boundA (wv_lt s₀.mem B (slot w b) w)
  rw [← Nat.pow_add,show 64*w+64*w=128*w by omega] at bound
  refine ⟨?_,⟨h.scr.congr kt.2.2,ht,(kt.gpr (by decide)).trans h.rdi,?_,
    (h.keep.trans kt).mono (by decide),h.frame.trans ft,drop_carry val bound⟩⟩
  · rw [zt]; exact congrArg some (decide_eq_decide.mpr (by omega))
  · simpa only [show 8*(k+1)=8*k+8 by omega] using it

theorem rows_ok {s : State} {B : Addr} {Z w a b n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hw : w < 2^31) (hwN : w=8*n) (hn : 0<n)
    (ha : a < 8) (hb : b < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (hz : wv s.mem B (rawBase w) (2*w)=0) :
    WP isa (AdxTiledProduct.rows a b) s fun t =>
      wv t.mem B (rawBase w) (2*w)=wv s.mem B (slot w a) w*wv s.mem B (slot w b) w ∧
      Hdr t.mem B w mi ∧ Frm B (ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have nowrap := hs.nowrap
  have iZ : 8*sFn 12+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sFn 12 < 32 by decide); omega
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
    have := hx (8*sFn 12,32) (by simp [ranges]); omega
  have h0 : Inv s B Z w a b 0 mi u :=
    ⟨hs.congr ku.2.2,frame_hdr hh fu,(ku.gpr (by decide)).trans hd,by rw [mu,word_writeW_self]; rfl,
      ku.mono (by decide),fu,by
        rw [ou.wv (by unfold rawBase slot hdrBytes sFn; omega) (by unfold rawBase slot aAcc at *; omega)]
        simpa only [Nat.mul_zero,wv,Nat.zero_mul] using hz⟩
  exact wp_upto (a := 0) (N := n) hn (Inv s B Z w a b · mi)
    (fun _ _ hk _ h => row_inv hZ hw hwN hk ha hb ha1 ha2 hb1 hb2 h)
    (fun _ h => ⟨by simpa only [← hwN] using h.val,h.hdr,h.frame,h.keep⟩) h0

end VG.Proof.Bignum.X86_64.AdxTiledProduct
