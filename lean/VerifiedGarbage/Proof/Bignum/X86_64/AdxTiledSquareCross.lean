import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareChoice
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRaw

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxTiledProduct (ranges)
open VG.Proof.Bignum.X86_64.AdxRect8 (rawBase)
open VG.Proof.MlKem.X86_64 (Keep)

private theorem cross_congr {r n : Nat} {f g : Nat → Nat}
    (h : ∀ j<n, f j=g j) : Square.cross r f n=Square.cross r g n := by
  have val (k : Nat) (hk : k≤n) : Square.value r f k=Square.value r g k := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Square.value,Square.value,ih (by omega),h k (by omega)]
  induction n with
  | zero => rfl
  | succ n ih => rw [Square.cross,Square.cross,ih (fun j hj => h j (by omega)) (fun k hk => val k (by omega)),val n (by omega),h n (by omega)]

theorem crossBody_ok {s : State} {B : Addr} {Z w a n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (hw : w<2^31) (hwN : w=8*n) (hn : 0<n)
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    (hz : ∀ j<2*w, word s.mem B (rawBase w+8*j)=0) :
    WP isa (.seq (AdxTri8.blocks ca) (AdxTiledSquare.rowsChoice ca)) s fun t =>
      wv t.mem B (rawBase w) (2*w)=AdxSquare.crossValue s.mem B (slot w a) w ∧
      Hdr t.mem B w mi ∧ Frm B (ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have nowrap := hs.nowrap
  refine WP.seq (WP.mono (AdxTri8.blocks_ok hs hd hh hZ hv pa hw hwN hn ha ha1 ha2 hz) fun u hu => ?_)
  have fu : Frm B (ranges w) s.mem u.mem := by
    intro p hp
    apply hu.frame p
    intro r hr
    simp only [AdxTri8.diagonalRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · have h := hp (rawBase w,16*w) (by simp [ranges])
      simp only [] at *; omega
    · have h := hp (8*sFn 12,32) (by simp [ranges])
      simp only [] at *; omega
  refine WP.mono (rowsChoice_ok hu.scr hu.rdi hu.hdr hZ (AdxTri8.diagonal_ops hv hu.frame) pa hw hwN hn ha ha1 ha2) fun t ⟨⟨c,vc⟩,ht,ft,kt⟩ => ?_
  have chunksEq : ∀ j<n, AdxTri8.chunks u.mem B (slot w a) j=AdxTri8.chunks s.mem B (slot w a) j := by
    intro j hj
    unfold AdxTri8.chunks
    rw [show 64*j=8*(8*j) by omega]
    exact AdxTiledProduct.input_preserved ha ha1 ha2 (by omega) (by omega) fu
  have crossEq : Square.cross (2^512) (AdxTri8.chunks u.mem B (slot w a)) n=
      Square.cross (2^512) (AdxTri8.chunks s.mem B (slot w a)) n := by
    apply cross_congr
    exact chunksEq
  have vu := hu.val
  rw [show 16*n=2*w by omega] at vu
  rw [vu,crossEq,← AdxTri8.chunks_cross,← hwN] at vc
  have dec := AdxSquare.square_decomposition s.mem B (slot w a) w
  have bound : wv s.mem B (slot w a) w*wv s.mem B (slot w a) w<2^(128*w) := by
    have h := Nat.mul_lt_mul'' (wv_lt s.mem B (slot w a) w) (wv_lt s.mem B (slot w a) w)
    rw [← Nat.pow_add,show 64*w+64*w=128*w by omega] at h
    exact h
  have cz : c=0 := by
    by_contra hc
    have h := Nat.mul_le_mul_left (2^(128*w)) (show 1≤c by omega)
    simp only [Nat.mul_one] at h
    omega
  rw [cz,Nat.mul_zero,Nat.add_zero] at vc
  exact ⟨vc,ht,fu.trans ft,(hu.keep.trans kt).mono (by decide)⟩

end VG.Proof.Bignum.X86_64.AdxTiledSquare
