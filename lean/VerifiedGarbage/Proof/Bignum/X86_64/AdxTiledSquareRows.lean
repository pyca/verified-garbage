import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareMath

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxTiledProduct (ranges frame_hdr input_preserved)
open VG.Proof.Bignum.X86_64.AdxTri8 (chunks)
open VG.Proof.Bignum.X86_64.AdxRect8 (rawBase)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

structure Inv (s₀ : State) (B : Addr) (Z w a n k : Nat) (mi : BitVec 64) (s : State) : Prop where
  scr : Scr s B Z
  hdr : Hdr s.mem B w mi
  rdi : s.gpr .rdi=B
  indexI : word s.mem B (8*sFn 12)=BitVec.ofNat 64 (8*k)
  keep : Keep mmRegs s₀ s
  frame : Frm B (ranges w) s₀.mem s.mem
  val : ∃ c, wv s.mem B (rawBase w) (2*w)+2^(128*w)*c+remaining s₀.mem B (slot w a) n k=
    wv s₀.mem B (rawBase w) (2*w)+remaining s₀.mem B (slot w a) n 0

private theorem advance {W W' R C D S S' T A : Nat}
    (prev : W+R*C+S=T) (step : W'+R*D=W+A) (rest : S=A+S') : W'+R*(C+D)+S'=T := by grind

theorem step_inv {s₀ s : State} {B : Addr} {Z w a n k : Nat} {mi : BitVec 64}
    (hZ : slot w 8≤Z) (hw : w<2^31) (hwN : w=8*n) (hk : k<n-1)
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp) (h : Inv s₀ B Z w a n k mi s) :
    WP isa (AdxTiledSquare.row a) s fun t => t.zf=some (decide (k+1=n-1)) ∧ Inv s₀ B Z w a n (k+1) mi t := by
  have nowrap := h.scr.nowrap
  have Z64 : slot w 8≤(2 : Nat)^64 := by omega
  refine WP.mono (row_ok h.scr h.rdi h.hdr hZ hw (by omega : w=8*k+8+8*(n-k-1))
    (by omega) ha ha1 ha2 h.indexI) fun t ⟨zt,it,⟨d,eq⟩,ht,ft,kt⟩ => ?_
  rw [input_preserved ha ha1 ha2 (by omega : 8*k+8≤w) Z64 h.frame,
    input_preserved ha ha1 ha2 (by omega : (8*k+8)+8*(n-k-1)≤w) Z64 h.frame] at eq
  rw [show 64*(8*k+(8*k+8))=512*(2*k+1) by omega,
    show slot w a+8*(8*k)=slot w a+64*k by omega,
    show slot w a+8*(8*k+8)=slot w a+64*(k+1) by omega] at eq
  obtain ⟨c,prev⟩ := h.val
  refine ⟨?_,⟨h.scr.congr kt.2.2,ht,(kt.gpr (by decide)).trans h.rdi,?_,
    (h.keep.trans kt).mono (by decide),h.frame.trans ft,c+d,?_⟩⟩
  · rw [zt]; exact congrArg some (decide_eq_decide.mpr (by omega))
  · simpa only [show 8*(k+1)=8*k+8 by omega] using it
  · exact advance prev eq (remaining_step s₀.mem B (slot w a) n k (by omega))

theorem rows_ok {s : State} {B : Addr} {Z w a n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    (hw : w<2^31) (hwN : w=8*n) (hn : 1<n)
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp) :
    WP isa (AdxTiledSquare.rows a) s fun t =>
      (∃ c, wv t.mem B (rawBase w) (2*w)+2^(128*w)*c=
        wv s.mem B (rawBase w) (2*w)+Square.cross (2^512) (chunks s.mem B (slot w a)) n) ∧
      Hdr t.mem B w mi ∧ Frm B (ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have nowrap := hs.nowrap
  have iZ : 8*sFn 12+8≤Z := by have := hdr_lt_slot w 8 (show sFn 12<32 by decide); omega
  have init : WP isa (.block [.mov32 .rax (.imm 0),.store (hdr (sFn 12)) .rax]) s fun t =>
      t.mem=s.mem.writeW (off B (8*sFn 12)) (0 : BitVec 64) ∧ Keep [.rax] s t := by
    apply WP.keep [.rax] (Q := fun t => t.mem=s.mem.writeW (off B (8*sFn 12)) (0 : BitVec 64)) _ rfl
    xrun [State.ea,hdr,hd,hdrOff,hs.st iZ]; rfl
  unfold AdxTiledSquare.rows
  refine WP.seq (WP.mono init fun u ⟨mu,ku⟩ => ?_)
  have ou : Outside B (8*sFn 12) 8 s.mem u.mem := by rw [mu]; exact writeW_outside _ _ _ (by decide)
  have fu : Frm B (ranges w) s.mem u.mem := by
    intro x hx
    apply ou x
    have := hx (8*sFn 12,32) (by simp [ranges]); omega
  have h0 : Inv s B Z w a n 0 mi u :=
    ⟨hs.congr ku.2.2,frame_hdr hh fu,(ku.gpr (by decide)).trans hd,by rw [mu,word_writeW_self]; rfl,
      ku.mono (by decide),fu,0,by
        rw [ou.wv (by unfold rawBase slot hdrBytes sFn; omega) (by unfold rawBase slot aAcc at *; omega),Nat.mul_zero,Nat.add_zero]⟩
  apply wp_upto (a := 0) (N := n-1) (by omega) (Inv s B Z w a n · mi)
    (fun _ _ hk _ h => step_inv hZ hw hwN hk ha ha1 ha2 h) ?_ h0
  intro t h
  obtain ⟨c,eq⟩ := h.val
  rw [remaining_end s.mem B (slot w a) n (by omega),Nat.add_zero] at eq
  simp only [remaining,Nat.mul_zero,Nat.pow_zero,Nat.one_mul,Nat.zero_add,Nat.sub_zero] at eq
  exact ⟨⟨c,eq⟩,h.hdr,h.frame,h.keep⟩

end VG.Proof.Bignum.X86_64.AdxTiledSquare
