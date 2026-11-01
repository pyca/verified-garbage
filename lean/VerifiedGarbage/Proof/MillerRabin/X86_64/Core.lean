module

public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrTab
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrLoop
import VerifiedGarbage.Proof.Ffdh.MillerRabin
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrExp
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # Shared Miller–Rabin core: correctness on x86-64

The existing table and window proofs compose to a single round against
the merged shared specification. This does not assume primality or pick
the caller's witness policy. -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.MlKem.X86_64

/-- The table and exponentiation change only their combined ranges. -/
def coreRanges (w : Nat) : List (Nat × Nat) :=
  tabRanges w ++ VG.Proof.RsaKeyGen.X86_64.expRanges w

/-- One prepared round, including construction of all sixteen powers. -/
theorem core_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm b : Nat}
    (hd : MrDims B Z w) (hc : MrCtx s B Z w mi c bm) (hE : ECtx s.mem B w c)
    (hodd : c % 2 = 1) (hc3 : 3 ≤ c) (hfit : mrE c < 16 ^ (16 * w))
    (hX : wv s.mem B (slot w VG.Impl.Bignum.Public.aXm) w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * w) % c) :
    WP isa (seqs (preparedRound M.mm)) s fun t =>
      MrCtx t B Z w mi c (Spec.Rsa.powMod b 1 c * 2 ^ (64 * w) % c) ∧ ECtx t.mem B w c ∧
      word t.mem B (8 * kFlag) = mask (Proof.MillerRabin.Round.round c b) ∧
      Frm B (coreRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hc1 : 1 < c := by omega_arith
  have hEn : B.toNat + slot w aE + 8 * (w + 1) ≤ 2 ^ 64 := by
    have := hc.good.scr.nowrap
    have := aE_fits hd
    omega_arith
  unfold preparedRound
  refine wp_seqs_append (by simp [tabBuild]) (by simp [mrExpLoop])
    (WP.mono (tabBuild_ok M hd hc hodd hc1 hX) fun u ⟨hu, ht, hy, hf, hk⟩ => ?_)
  have hEu : ECtx u.mem B w c := hE.of_frm hf
    (fun r hr => Or.inr (tabRanges_lt w r hr)) hEn
  refine WP.mono (mrExpLoop_ok M hd hu ht hEu hodd hc1 hy) fun t ⟨hc', hE', hp, hf', hk'⟩ =>
    ⟨hc', hE', ?_, ?_, (hk.trans hk').mono (by decide)⟩
  · rw [hp, VG.Proof.Ffdh.window_round_eq b hc3 hodd hfit, ← VG.Proof.Ffdh.rsa_round_eq b hc3 hodd]
    rfl
  · exact (hf.mono (fun r hr => List.mem_append_left _ hr)).trans
      (hf'.mono (fun r hr => List.mem_append_right _ hr))

end VG.Proof.MillerRabin.X86_64
