module
import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Arguments
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ProbablePrime

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeArguments
import VerifiedGarbage.Proof.Framework.Omega

/-! # A complete native candidate test using retained generation arguments -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.MillerRabin.X86_64 VG.Impl.Bignum.X86_64

/-- Candidate setup, padded loading, trial division and the shared RSA
Miller–Rabin loop implement the exact DSA probable-prime operation. -/
theorem primeFromFrame_ok (M : Mont) (K : Kernel) {P : PrimeParams} {s : State} {mi : BitVec 64}
    {used candidate : Nat} {W : Nat → BitVec 64} {bs : List Byte}
    (hg : Good s P.B P.Z P.w mi) (hc : candidate < 2 ^ 31) (hk : P.checks < 2 ^ 31)
    (hsp : s.gpr .rsp = P.sp)
    (hr : ∀ k < 37, InRegions (s.rd ++ s.wr) (off P.sp (8 * k)) 8)
    (hwords : ∀ k < 37, word s.mem P.sp (8 * k) = W k)
    (hsep : ∀ k < 37, ∀ j < 32, Mem.Sep (off P.sp (8 * k)) 8 (off P.B (8 * j)) 8)
    (hwp : W 5 + BitVec.ofNat 64 VG.Impl.Dsa.Generation.Layout.witness = P.p)
    (hwr : W 13 = P.rp) (hwl : W 15 = BitVec.ofNat 64 P.rand.length)
    (hwu : W 16 = BitVec.ofNat 64 used)
    (htape : Src s P.B P.Z P.rp P.rand) (hout : ∀ i < P.len, InRegions s.wr (off P.p i) 1)
    (hlen : bs.length = P.len) (hvalue : Spec.Rsa.os2ip bs = P.N)
    (hsrc : Src s P.B P.Z (W 5 + BitVec.ofNat 64 candidate) bs)
    (hu : used ≤ P.rand.length) (hw : P.w ≤ 48) (hz : slot P.w aTab + 2048 ≤ P.Z)
    (hn : 8161 < P.N) (hpolicy : 1024 < Spec.Dsa.bitLength P.N ↔ 16 < P.w)
    (hchecks : P.checks = Spec.Dsa.primeChecks (Spec.Dsa.bitLength P.N)) :
    WP isa (primeFromFrame M.mm K.run candidate P.len P.drawBytes P.checks) s fun t =>
      let res := Spec.Dsa.probablePrime P.N (P.rand.drop used)
      ∃ mi' used', PrimeInput P mi' used' t ∧ used' ≤ P.rand.length ∧
        (res = none → word t.mem P.B (8 * kStat) = BitVec.ofNat 64 0) ∧
        (∀ b rest, res = some (b, rest) →
          word t.mem P.B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 3) ∧
          used' = P.rand.length - rest.length) ∧
        WorkFrame P.B ((128, 128) :: (slot P.w 0, 8 * (P.w + 2)) :: primeRanges P.w)
          (primeExtras P) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold primeFromFrame
  refine WP.seq (WP.mono (primeArguments_ok hg hc hk hsp hr hwords hsep hwp hwr hwl hwu htape hout)
    fun u ⟨hi, hptr, hf, ku⟩ => ?_)
  have src : Src u P.B P.Z (W 5 + BitVec.ofNat 64 candidate) bs :=
    hsrc.congrK (fun a ha => hf a (Or.inr (Nat.le_trans P.z256 ha))) ku
  refine WP.mono (primeBytes_ok M K hi hptr hlen hvalue src hu hw hz hn hpolicy hchecks)
    fun t ⟨mi', used', ht, hut, he, hb, ft, kt⟩ => ?_
  have ff : Frm P.B [(128, 128)] s.mem u.mem := Frm.of_outside hf (by simp)
  exact ⟨mi', used', ht, hut, he, hb,
    (ff.work.mono (by simp)).trans (ft.mono (fun _ hr => List.mem_cons_of_mem _ hr)),
    (ku.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64.Generation
