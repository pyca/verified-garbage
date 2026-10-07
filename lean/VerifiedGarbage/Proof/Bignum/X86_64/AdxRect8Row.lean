import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8RowInv

/-! Correctness and termination of a complete rectangular row. -/
namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)

theorem row_ok {s : State} {B : Addr} {Z w a b i j₀ n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca cb : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (hZ : slot w 8 ≤ Z) (hw : w < 2^31) (hi : i+8 ≤ w)
    (ha : a < 8) (hb : b < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) (hwN : w = j₀+8*n) (hn : 0 < n)
    (hidx : word s.mem B (8*sFn 12) = BitVec.ofNat 64 i)
    (hjdx : word s.mem B (8*sFn 13) = BitVec.ofNat 64 j₀)
    (hc : (word s.mem B carryOffset).toNat = 0) :
    WP isa (AdxRect8.row ca cb) s (RowInv s B Z w a b i j₀ n mi) := by
  have h0 : RowInv s B Z w a b i j₀ 0 mi s :=
    ⟨hs,hh,hd,hidx,by simpa only [Nat.mul_zero,Nat.add_zero] using hjdx,
      by omega,Keep.refl _ _,Frm.refl _ _ _,Or.inl rfl,by
        simp only [hc,Nat.mul_zero,Nat.add_zero,wv]⟩
  unfold AdxRect8.row
  exact wp_upto (a := 0) (N := n) hn (RowInv s B Z w a b i j₀ · mi)
    (fun _ _ hk _ h => rowStep_inv hv pa pb hZ hw hi ha hb ha1 ha2 hb1 hb2 hwN hk h)
    (fun _ h => h) h0

end VG.Proof.Bignum.X86_64.AdxRect8
