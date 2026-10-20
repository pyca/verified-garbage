module
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Arguments
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ProbablePrime
public import Mathlib.Data.Int.ModEq

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFromFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Workspace
import VerifiedGarbage.Proof.Framework.Omega

/-! # The native primality operation starts with arbitrary scratch contents -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.MillerRabin.X86_64 VG.Impl.Bignum.X86_64

/-- A frame word outside the arithmetic workspace survives bounded writes. -/
theorem frame_word_of_workspace {B F : Addr} {Z k : Nat} {rs : List (Nat × Nat)} {m m' : Mem}
    (hf : Frm B rs m m') (hr : ∀ r ∈ rs, r.1 + r.2 ≤ Z)
    (ho : ∀ i < 8, Z ≤ ofs B (off (off F (8 * k)) i)) :
    word m' F (8 * k) = word m F (8 * k) := by
  apply Mem.readW_congr
  intro i hi
  exact hf _ (fun r h => Or.inr (Nat.le_trans (hr r h) (ho i hi)))

theorem checkPrime_ok (M : Mont) (K : Kernel) {P : PrimeParams} {s : State}
    {used candidate : Nat} {W : Nat → BitVec 64} {bs : List Byte}
    (hS : Scr s P.B P.Z) (hdi : s.gpr .rdi = P.B)
    (hc : candidate < 2 ^ 31) (hk : P.checks < 2 ^ 31) (hsp : s.gpr .rsp = P.sp)
    (hr : ∀ k < 37, InRegions (s.rd ++ s.wr) (off P.sp (8 * k)) 8)
    (hwords : ∀ k < 37, word s.mem P.sp (8 * k) = W k)
    (hsep : ∀ k < 37, ∀ j < 32, Mem.Sep (off P.sp (8 * k)) 8 (off P.B (8 * j)) 8)
    (hframe : ∀ k < 37, ∀ i < 8, P.Z ≤ ofs P.B (off (off P.sp (8 * k)) i))
    (hwp : W 5 + BitVec.ofNat 64 VG.Impl.Dsa.Generation.Layout.witness = P.p)
    (hwr : W 13 = P.rp) (hwl : W 15 = BitVec.ofNat 64 P.rand.length)
    (hwu : W 16 = BitVec.ofNat 64 used)
    (htape : Src s P.B P.Z P.rp P.rand) (hout : ∀ i < P.len, InRegions s.wr (off P.p i) 1)
    (hlen : bs.length = P.len) (hvalue : Spec.Rsa.os2ip bs = P.N)
    (hsrc : Src s P.B P.Z (W 5 + BitVec.ofNat 64 candidate) bs)
    (hu : used ≤ P.rand.length) (hw : P.w ≤ 48) (hz : slot P.w aTab + 2048 ≤ P.Z)
    (hn : 8161 < P.N) (hpolicy : 1024 < Spec.Dsa.bitLength P.N ↔ 16 < P.w)
    (hchecks : P.checks = Spec.Dsa.primeChecks (Spec.Dsa.bitLength P.N)) :
    WP isa (checkPrime M.mm K.run P.w candidate P.len P.drawBytes P.checks) s fun t =>
      let res := Spec.Dsa.probablePrime P.N (P.rand.drop used)
      ∃ mi' used', PrimeInput P mi' used' t ∧ used' ≤ P.rand.length ∧
        (res = none → word t.mem P.B (8 * kStat) = BitVec.ofNat 64 0) ∧
        (∀ b rest, res = some (b, rest) →
          word t.mem P.B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 3) ∧
          used' = P.rand.length - rest.length) ∧
        WorkFrame P.B ((48, 80) :: (224, 8) :: (128, 128) ::
          (slot P.w 0, 8 * (P.w + 2)) :: primeRanges P.w) (primeExtras P) s.mem t.mem ∧
        Keep mmRegs s t := by
  unfold checkPrime
  have hz16 : slot P.w 16 ≤ P.Z := Nat.le_trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right (8 * (P.w + 2)) (by decide : 16 ≤ 28)) 256) P.room
  refine WP.seq (WP.mono (workspace_ok hS hdi hz16 (by have := P.dims.w4; omega) (by omega))
    fun u ⟨_, hg, hf, ku⟩ => ?_)
  have hb : ∀ r ∈ [(48, 80), (224, 8)], r.1 + r.2 ≤ P.Z := by
    have := P.z256
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only <;> omega
  have hwu' : ∀ k < 37, word u.mem P.sp (8 * k) = W k := by
    intro k h
    rw [frame_word_of_workspace hf hb (hframe k h), hwords k h]
  have tape := htape.congrK (InScr.of_frm hf hb) ku
  have src := hsrc.congrK (InScr.of_frm hf hb) ku
  refine WP.mono (primeFromFrame_ok M K hg hc hk ((ku.gpr (by decide)).trans hsp)
    (fun k h => by rw [ku.2.1, ku.2.2]; exact hr k h) hwu' hsep hwp hwr hwl hwu tape
    (fun i h => by rw [ku.2.2]; exact hout i h) hlen hvalue src hu hw hz hn hpolicy hchecks)
    fun t ⟨mi', used', ht, hut, he, hs, ft, kt⟩ => ?_
  exact ⟨mi', used', ht, hut, he, hs,
    (hf.work.mono (by simp)).trans (ft.mono (fun _ h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))),
    (ku.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64.Generation
