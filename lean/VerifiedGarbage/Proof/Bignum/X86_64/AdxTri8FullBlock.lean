import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Block

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem zero_ends {m : Mem} {B : Addr} {e n : Nat}
    (lo : word m B e=0) (hi : word m B (e+8*(n+1))=0) :
    wv m B e (n+2)=2^64*wv m B (e+8) n := by
  rw [show n+2=1+(n+1) by omega,wv_add,wv_add]
  simp only [wv,lo,Nat.mul_zero,Nat.mul_one,Nat.add_zero,Nat.pow_zero,Nat.one_mul,Nat.zero_add]
  rw [show e+8+8*n=e+8*(n+1) by omega,hi]
  simp only [show (0 : BitVec 64).toNat=0 from rfl,Nat.mul_zero,Nat.add_zero,Nat.zero_add]

theorem fullBlock_ok {s : State} {B : Addr} {Z w a I : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hIndex : I+8≤w)
    (hI : word s.mem B (8*sFn 12)=BitVec.ofNat 64 I)
    (lo : word s.mem B (slot w aAcc+16+16*I)=0)
    (hi : word s.mem B (slot w aAcc+16+16*I+120)=0) :
    WP isa (AdxTri8.block a) s fun t =>
      wv t.mem B (slot w aAcc+16+16*I) 16=AdxSquare.crossValue s.mem B (slot w a+8*I) 8 ∧
      Outside B (slot w aAcc+16+16*I) 128 s.mem t.mem ∧ Keep mmRegs s t := by
  have nowrap := hs.nowrap
  have ar := AdxRect8.tile_ranges hIndex hIndex ha ha1 ha2
  have endBound : slot w aAcc+16+16*I+128≤Z := by omega
  refine WP.mono (block_ok hs hd hh hZ ha ha1 ha2 hIndex hI) fun t ⟨vt,ot,kt⟩ => ?_
  have low : word t.mem B (slot w aAcc+16+16*I)=0 := by
    rw [ot.word (by unfold output; omega) (by omega)]; exact lo
  have high : word t.mem B (slot w aAcc+16+16*I+8*(14+1))=0 := by
    rw [ot.word (by unfold output; omega) (by omega)]; exact hi
  refine ⟨?_,ot.mono (by unfold output; omega) (by unfold output; omega),kt⟩
  rw [show 16=14+2 from rfl,zero_ends low high]
  rw [show slot w aAcc+16+16*I+8=output w I 0 by unfold output; omega]
  exact vt

end VG.Proof.Bignum.X86_64.AdxTri8
