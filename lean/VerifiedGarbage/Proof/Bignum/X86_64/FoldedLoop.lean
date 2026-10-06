import VerifiedGarbage.Proof.Bignum.X86_64.FoldedStep

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

structure SquareInv (s₀ : State) (B : Addr) (Z w N X x : Nat) (mi : BitVec 64)
    (i : Nat) (s : State) : Prop where
  ctx : ExpCtx s B Z w mi N X
  reduced : wv s.mem B (slot w aY) w < N
  value : wv s.mem B (slot w aY) w % N = x^(2^i) * 2^(64*w) % N
  count : word s.mem B (8*sI) = BitVec.ofNat 64 (16-i)
  frame : Frm B (expRanges w) s₀.mem s.mem
  keep : Keep mmRegs s₀ s

theorem loopStep_ok (M : Mont) {s₀ s : State} {B : Addr} {Z w N X x i : Nat} {mi : BitVec 64}
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2^31)
    (hR : Nat.Coprime (2^(64*w)) N) (hi : i < 16)
    (h : SquareInv s₀ B Z w N X x mi i s) :
    WP isa (Folded.squareStep M.mm) s fun t =>
      t.zf = some (decide (i+1 = 16)) ∧ SquareInv s₀ B Z w N X x mi (i+1) t := by
  refine WP.mono (squareStep_ok M h.ctx hZ hw hw' hR h.reduced h.value
    (by omega) (by omega) h.count) fun t ⟨ctx,lt,val,count,zf,frame,keep⟩ => ?_
  have hp : 2 * 2^i = 2^(i+1) := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [hp] at val
  refine ⟨?_,ctx,lt,val,?_,h.frame.trans frame,(h.keep.trans keep).mono (by decide)⟩
  · rw [zf]; congr 1; exact decide_eq_decide.mpr (by omega)
  · simpa only [Nat.sub_sub] using count

theorem squares_ok (M : Mont) {s : State} {B : Addr} {Z w N X x : Nat} {mi : BitVec 64}
    (hc : ExpCtx s B Z w mi N X) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2^31)
    (hR : Nat.Coprime (2^(64*w)) N)
    (hY : wv s.mem B (slot w aY) w < N)
    (hy : wv s.mem B (slot w aY) w % N = x * 2^(64*w) % N)
    (hcount : word s.mem B (8*sI) = 16) :
    WP isa (.loop (Folded.squareStep M.mm) .ne) s
      (SquareInv s B Z w N X x mi 16) := by
  apply wp_upto (a := 0) (N := 16) (by decide)
    (SquareInv s B Z w N X x mi)
    (fun _ _ hi _ h => loopStep_ok M hZ hw hw' hR hi h) (fun _ h => h)
  exact ⟨hc,hY,by simpa only [Nat.pow_zero,Nat.pow_one] using hy,
    hcount,Frm.refl _ _ _,Keep.refl _ _⟩

end VG.Proof.Bignum.X86_64.FoldedPublic
