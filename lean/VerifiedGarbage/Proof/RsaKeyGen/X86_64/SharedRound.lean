module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedMid
public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.SharedCandidate
import VerifiedGarbage.Proof.Framework.Omega

/-! # RSA's witness policy around the callable shared round -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.MillerRabin.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

def sharedRoundRanges (w : Nat) : List (Nat × Nat) :=
  sharedMidRanges w ++ [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)]

/-- `mrRound`. -/
theorem sharedRound_ok (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) (R : Kernel) {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm : Nat} {sp : Addr}
    (hd : MrDims B Z w) (hZ : slot w 28 ≤ Z) (henv : SharedEnv B Z sp s) (hc : MrCtx s B Z w mi c bm) (hE : ECtx s.mem B w c)
    (hR2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c) (hc1 : 1 < c)
    (hsh : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c)
    {rp : Addr} {used : Nat} {r : List Byte} (hR : word s.mem B (8 * kRand) = rp)
    (hU : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hsrc : Src s B Z rp r) (hlen : used + 8 * w ≤ r.length)
    {i uni ch : Nat} (hI : word s.mem B (8 * kI) = BitVec.ofNat 64 i)
    (hN : word s.mem B (8 * kUni) = BitVec.ofNat 64 uni) (hC : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch)
    (hi : i < 2 ^ 61) (huni : uni < 2 ^ 61) (hch : ch < 2 ^ 62) :
    WP isa (seqs (mrRoundWith mm R.run)) s fun t =>
      (∃ bm', MrCtx t B Z w mi c bm') ∧ ECtx t.mem B w c ∧
      wv t.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 (used + 8 * w) ∧
      word t.mem B (8 * kStat) = BitVec.ofNat 64
        (if Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2
            (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).1 then
          (if i + 1 < 17 ∨ uni + (Spec.RsaKeyGen.witness (c - 1)
              (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).2.toNat < ch then 4 else 1)
        else 3) ∧
      (Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2
          (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).1 = true →
        word t.mem B (8 * kI) = BitVec.ofNat 64 (i + 1) ∧
        word t.mem B (8 * kUni) = BitVec.ofNat 64 (uni + (Spec.RsaKeyGen.witness (c - 1)
          (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).2.toNat)) ∧
      SharedFrame B sp (sharedRoundRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.good.scr.nowrap
  rw [mrRoundWith]
  refine wp_seqs_append (by simp [mrWitness]) (by simp) ?_
  refine WP.mono (sharedMid_ok M hmc R hd hZ henv hc hE hR2 hc1 hsh hR hU hK hsrc hlen hI hN hC)
    fun s₂ ⟨⟨bm₂, hc₂⟩, he₂, hfl₂, hI₂, hN₂, hC₂, hU₂, hUs₂, hR2₂, hf02, k₁₂⟩ => ?_
  simp only [wtOf, passOf] at hU₂ hfl₂
  generalize hwt : Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w))) = wt
    at hU₂ hfl₂ ⊢
  generalize hfv : Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1
    (Spec.Rsa.splitTwos (c - 1)).2 wt.1 = f at hfl₂ ⊢
  have hg₂ := hc₂.good
  refine WP.mono (roundTail_ok hg₂ hd.z hfl₂ hI₂ hU₂ hN₂ hC₂ (by omega_arith) (by omega_arith) hch) fun t ⟨hm, k⟩ => ?_
  have hft : Frm B [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)] s₂.mem t.mem := by
    rw [hm]
    have wI := Frm.of_outside (rs := [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)])
      (writeW_outside s₂.mem B (BitVec.ofNat 64 (i + 1)) (d := 8 * kI) (by unfold kI kElen sFn; omega_arith)) (by simp)
    cases f
    · exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kStat) (by unfold kStat sFn; omega_arith)) (by simp)
    · exact (wI.trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kUni) (by unfold kUni kP sFn; omega_arith))
        (by simp))).trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kStat) (by unfold kStat sFn; omega_arith))
        (by simp))
  have hgt : Good t B Z w mi := ⟨hg₂.scr.congr k.2.2, (k.gpr (by decide)).trans hg₂.rdi,
    Hdr.of_frm hg₂.hdr hft (by rng_disj)⟩
  refine ⟨⟨bm₂, hc₂.of_frm hd hft hgt.scr hgt.rdi (by rng_disj) (by rng_disj) (by rng_disj) (by rng_disj) (by rng_disj)⟩,
    he₂.of_frm hft (by rng_disj) (by have := aE_fits hd; omega_arith),
    ?_, ?_, ?_, ?_, ?_, ((k₁₂.trans k).mono (by decide))⟩
  · rw [hft.wv_eq (d := slot w aR2) (k := w) (by rng_disj)
      (by have := slot_le (w := w) (show aR2 < 8 by decide); have := hd.z; omega_arith)]; exact hR2₂
  · rw [hft.word_eq (d := 8 * kUsed) (by rng_disj) (by unfold kUsed sFn; omega_arith)]; exact hUs₂
  · rw [hm]; cases f <;> simp only [↓reduceIte, Bool.false_eq_true, word_writeW_self]
  · intro hf
    rw [hm, hf]
    simp only [↓reduceIte]
    refine ⟨?_, ?_⟩
    · rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        word_writeW_self]
    · rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · exact (hf02.mono (fun r hr => List.mem_append_left _ hr)).trans
      (hft.work.mono (fun r hr => List.mem_append_right _ hr))

end VG.Proof.RsaKeyGen.X86_64
