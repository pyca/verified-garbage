import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRows

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxTiledProduct (ranges)
open VG.Proof.Bignum.X86_64.AdxTri8 (chunks)
open VG.Proof.Bignum.X86_64.AdxRect8 (rawBase)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

private theorem cross_one (r : Nat) (f : Nat → Nat) : Square.cross r f 1=0 := by
  simp only [Square.cross,Square.value,Nat.zero_mul,Nat.add_zero]

theorem rowsTest_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    (hw : w<2^31) :
    WP isa (.block [.mov .rax (.mem (hdr sW)),.alu .cmp .rax (.imm 8)]) s fun t =>
      t.zf=some (decide (w=8)) ∧ t.mem=s.mem ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf=some (decide (w=8)) ∧ t.mem=s.mem) ?_ rfl)
    fun t ⟨⟨z,m⟩,k⟩ => ⟨z,m,k⟩
  xrun [State.ea,hdr,hd,hdrOff,hs.ld (show 8*sW+8≤Z by have := hdr_lt_slot w 8 (show sW<32 by decide); omega),
    hh.hw,show (8 : BitVec 32).signExtend 64=BitVec.ofNat 64 8 from rfl,ofNat_sub_beq (by omega : w<2^64) (by decide : 8<2^64)]

theorem rowsChoice_ok {s : State} {B : Addr} {Z w a n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    (hw : w<2^31) (hwN : w=8*n) (hn : 0<n)
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp) :
    WP isa (AdxTiledSquare.rowsChoice a) s fun t =>
      (∃ c, wv t.mem B (rawBase w) (2*w)+2^(128*w)*c=
        wv s.mem B (rawBase w) (2*w)+Square.cross (2^512) (chunks s.mem B (slot w a)) n) ∧
      Hdr t.mem B w mi ∧ Frm B (ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold AdxTiledSquare.rowsChoice
  have test := rowsTest_ok hs hd hh hZ hw
  refine WP.seq (WP.mono test fun u ⟨zu,mu,ku⟩ => ?_)
  by_cases h8 : w=8
  · refine WP.ite true (by simp [eval,zu,h8]) (fun _ => WP.block_nil ?_) (by intro h; cases h)
    have km : Keep mmRegs s u := ku.mono (by decide)
    refine ⟨⟨0,?_⟩,mu ▸ hh,?_,km⟩
    swap
    · rw [mu]; exact Frm.refl _ _ _
    have n1 : n=1 := by omega
    rw [mu,n1]
    simp only [cross_one,Nat.mul_zero,Nat.add_zero]
  · refine WP.ite false (by simp [eval,zu,h8]) (by intro h; cases h) (fun _ => ?_)
    refine WP.mono (rows_ok (hs.congr ku.2.2) ((ku.gpr (by decide)).trans hd) (mu ▸ hh) hZ hw hwN
      (by omega) ha ha1 ha2) fun t ⟨vt,ht,ft,kt⟩ => ?_
    rw [mu] at vt ft
    exact ⟨vt,ht,ft,(ku.trans kt).mono (by decide)⟩

end VG.Proof.Bignum.X86_64.AdxTiledSquare
