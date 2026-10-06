import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTailSetup

/-! Complete a rectangular row by propagating its pending carry to the end. -/
namespace VG.Proof.Bignum.X86_64.AdxTiledProduct
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.Bignum.X86_64.AdxHeader (highPad)
open VG.Proof.Bignum.X86_64.AdxRect8 (rawBase)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)

private theorem suffix_arith {L P X Y Q C D : Nat} (h : X+Q*D=Y+C) :
    L+P*X+(P*Q)*D=L+P*Y+P*C := by grind

theorem suffix_value {m m' : Mem} {B : Addr} {e d n cin cout : Nat}
    (hZ : e+8*(d+n) ≤ (2 : Nat)^64) (hf : Outside B (e+8*d) (8*n) m m')
    (hv : wv m' B (e+8*d) n + (2 : Nat)^(64*n)*cout = wv m B (e+8*d) n+cin) :
    wv m' B e (d+n)+(2 : Nat)^(64*(d+n))*cout =
      wv m B e (d+n)+(2 : Nat)^(64*d)*cin := by
  have lo := hf.wv (show e+8*d ≤ e+8*d ∨ e+8*d+8*n ≤ e by omega) (by omega)
  rw [wv_add,wv_add,lo,Nat.mul_add,Nat.pow_add]
  exact suffix_arith hv

theorem tail_ok {s : State} {B : Addr} {Z w i n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hw : w < 2^31) (hn : w=i+8+8*n)
    (hidx : word s.mem B (8*sFn 12) = BitVec.ofNat 64 i)
    (hp : s.gpr .rsi = off B (rawBase w+8*(i+w))) :
    WP isa AdxTiledProduct.tail s fun t =>
      (∃ c, wv t.mem B (rawBase w) (2*w)+(2 : Nat)^(128*w)*c =
        wv s.mem B (rawBase w) (2*w)+(2 : Nat)^(64*(i+w+8))*(word s.mem B carryOffset).toNat) ∧
      Outside B (rawBase w) (16*w) s.mem t.mem ∧ Keep mmRegs s t := by
  have nowrap := hs.nowrap
  have rawEnd : rawBase w+16*w=highPad w := by unfold rawBase highPad; omega
  have padBound : highPad w+16 ≤ slot w 8 := by unfold highPad slot aAcc; omega
  unfold AdxTiledProduct.tail
  refine WP.seq (WP.mono (tailTest_ok hs hd hh hZ hw (by omega) hidx) fun a ⟨za,ma,ka⟩ => ?_)
  by_cases he : i+8=w
  · refine WP.ite true (by simp [eval,za,he]) (fun _ => WP.block_nil ?_) (by simp)
    refine ⟨⟨(word s.mem B carryOffset).toNat,?_⟩,?_,ka.mono (by decide)⟩
    · rw [ma,show 64*(i+w+8)=128*w by omega]
    · rw [ma]; exact Outside.refl _ _ _ _
  · refine WP.ite false (by simp [eval,za,he]) (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono (tailSetup_ok (hs.congr ka.2.2) ((ka.gpr (by decide)).trans hd)
      (ma ▸ hh) hZ ((ka.gpr (by decide)).trans hp)) fun b ⟨cb,pb,eb,zb,mb,kb⟩ => ?_)
    have hend : rawBase w+8*(i+w+8)+64*n=highPad w := by rw [← rawEnd]; omega
    refine WP.mono (AdxCarry8.propagate_ok (hs.congr (ka.trans kb).2.2) pb
      (by rw [hend]; exact eb) zb (by rw [hend]; omega) (by rw [hend]; omega) (by omega : 0<n))
      fun t ⟨_,ht⟩ => ?_
    have val := ht.val
    rw [cb,ma,show 512*n=64*(8*n) by omega] at val
    have lifted := suffix_value (e := rawBase w) (d := i+w+8) (n := 8*n)
      (by omega : rawBase w+8*(i+w+8+8*n) ≤ (2 : Nat)^64)
      (by rw [show 8*(8*n)=64*n by omega]; exact ht.frame) val
    rw [mb,ma,show i+w+8+8*n=2*w by omega,show 64*(2*w)=128*w by omega] at lifted
    refine ⟨⟨(t.gpr .rbp).toNat,lifted⟩,?_,((ka.trans kb).trans ht.keep).mono (by decide)⟩
    have frame := ht.frame.mono (o' := rawBase w) (n' := 16*w) (by omega) (by omega)
    rw [mb,ma] at frame
    exact frame

end VG.Proof.Bignum.X86_64.AdxTiledProduct
