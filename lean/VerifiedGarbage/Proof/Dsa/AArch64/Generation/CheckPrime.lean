module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFromFrame
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Workspace
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.FrameWord
import VerifiedGarbage.Proof.Framework.Omega

/-! # The native primality operation starts with arbitrary scratch contents -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.Generation VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.MillerRabin.AArch64 VG.Impl.Bignum.AArch64

theorem checkPrime_ok (M : Mont) (K : Kernel) {P : PrimeParams} {s : State}
    {used candidate : Nat} {W : Nat → BitVec 64} {bs : List Byte}
    (hS : Scr s P.B P.Z) (hdi : s.gpr .x0 = P.B)
    (hc : candidate < 2 ^ 16) (hk : P.checks < 2 ^ 16) {F : Addr} (hsp : s.sp = F)
    (hr : ∀ k < 34, InRegions (s.rd ++ s.wr) (off F (8 * k)) 8)
    (hwords : ∀ k < 34, word s.mem F (8 * k) = W k)
    (hsep : ∀ k < 34, ∀ j < 32, Mem.Sep (off F (8 * k)) 8 (off P.B (8 * j)) 8)
    (hframe : ∀ k < 34, ∀ i < 8, P.Z ≤ ofs P.B (off (off F (8 * k)) i))
    (hwp : W 5 + BitVec.ofNat 64 VG.Impl.Dsa.Generation.Layout.witness = P.p)
    (hwr : W 14 = P.rp) (hwl : W 15 = BitVec.ofNat 64 P.rand.length)
    (hwu : W 16 = BitVec.ofNat 64 used)
    (htape : Src s P.B P.Z P.rp P.rand) (hout : ∀ i < P.len, InRegions s.wr (off P.p i) 1)
    (hlen : bs.length = P.len) (hvalue : Spec.Rsa.os2ip bs = P.N)
    (hsrc : Src s P.B P.Z (W 5 + BitVec.ofNat 64 candidate) bs)
    (hu : used ≤ P.rand.length) (hw : P.w ≤ 48) (hz : slot P.w aTab + 2048 ≤ P.Z)
    (hn : 8161 < P.N) (hpolicy : 1024 < Spec.Dsa.bitLength P.N ↔ 16 < P.w)
    (hchecks : P.checks = Spec.Dsa.primeChecks (Spec.Dsa.bitLength P.N)) :
    WP isa (checkPrime M.mm K.run P.w candidate P.len P.drawBytes P.checks) s fun t =>
      let res := Spec.Dsa.probablePrime P.N (P.rand.drop used)
      ∃ used', PrimeInput P used' t ∧ used' ≤ P.rand.length ∧
        (res = none → word t.mem P.B (8 * kStat) = BitVec.ofNat 64 0) ∧
        (∀ b rest, res = some (b, rest) →
          word t.mem P.B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 3) ∧
          used' = P.rand.length - rest.length) ∧
        WorkFrame P.B (workspaceRanges ++ (128, 128) ::
          (slot P.w 0, 8 * (P.w + 2)) :: primeRanges P.w) (primeExtras P) s.mem t.mem ∧
        Keep mmRegs s t := by
  unfold checkPrime
  have hz16 : slot P.w 16 ≤ P.Z := Nat.le_trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right (8 * (P.w + 2)) (by decide : 16 ≤ 28)) 256) P.room
  refine WP.seq (WP.mono (workspace_ok hS hdi hz16 (by have := P.w4; omega) hw)
    fun u ⟨hg, _, hf, ku⟩ => ?_)
  have hb : ∀ r ∈ workspaceRanges, r.1 + r.2 ≤ P.Z := by
    have := hg.h256
    simp only [workspaceRanges, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only <;> omega
  have hwu' : ∀ k < 34, word u.mem F (8 * k) = W k := by
    intro k h
    rw [frame_word_of_workspace hf hb (hframe k h), hwords k h]
  have tape := htape.congrK (InScr.of_frm hf hb) ku
  have src := hsrc.congrK (InScr.of_frm hf hb) ku
  refine WP.mono (primeFromFrame_ok M K hg hc hk (ku.sp.trans hsp)
    (fun k h => by rw [ku.rd, ku.wr]; exact hr k h) hwu' hsep hwp hwr hwl hwu tape
    (fun i h => by rw [ku.wr]; exact hout i h) hlen hvalue src hu hw hz hn hpolicy hchecks)
    fun t ⟨used', ht, hut, he, hs, ft, kt⟩ => ?_
  exact ⟨used', ht, hut, he, hs,
    (hf.work.mono (fun _ h => List.mem_append_left _ h)).trans (ft.mono (fun _ h => List.mem_append_right _ h)),
    (ku.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64.Generation
