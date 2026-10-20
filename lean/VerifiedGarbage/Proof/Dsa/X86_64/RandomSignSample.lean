module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignRunning
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSample

/-! A nonce sample advances consumption while preserving the signing-loop state. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64
open VG.Proof.Dsa.Random

theorem random_sign_sample {extra : Nat} {s t : State} {h : RandomSignABI extra s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {used fuel : Nat}
    (hr : RandomSignRunning h hq used fuel t) :
    WP isa Random.sample t fun u =>
      u.gpr .rax = BitVec.ofNat 64 (sampleStatus (VG.Proof.Dsa.randomSignDraw (randomInput s) used)) ∧
      word u.mem (randomBase s) Random.oStatus =
        BitVec.ofNat 64 (sampleStatus (VG.Proof.Dsa.randomSignDraw (randomInput s) used)) ∧
      RandomSignRunning h hq (used + (VG.Proof.Dsa.randomSignDraw (randomInput s) used).used) fuel u ∧
      (∀ k, (VG.Proof.Dsa.randomSignDraw (randomInput s) used).scalar = some k →
        Spec.Rsa.bytesAt u.mem (off (randomBase s) Random.oNonce) (stackArg s 0).toNat =
          Spec.Dsa.encodeBE (stackArg s 0).toNat k) := by
  obtain ⟨m, draws, hready⟩ := hr.ready
  let C := randomContextOf h m hq
  have he : randomRemaining C used 128 = VG.Proof.Dsa.randomSignDraw (randomInput s) used := by
    unfold randomRemaining VG.Proof.Dsa.randomSignDraw
    change VG.Spec.Dsa.Random.sample (Spec.Dsa.decodeBE (randomQBytes s)) 128 _ = _
    rw [random_q_decode]
    rfl
  refine WP.mono_mx (by decide) (random_sample_encoded (C := C) hq hready)
    fun u ⟨hstatus, hstatusWord, _, hnonce, hf, ⟨draws', hready'⟩, hk⟩ hmx => ?_
  rw [he] at hstatus hstatusWord hnonce hready'
  have fits : ∀ r ∈ randomWriteRanges, r.1 + r.2 ≤ Random.frameBytes := by decide
  have hf0 := InScr.of_frm hready.frame fits
  have hf1 := InScr.of_frm hf fits
  have hmem : InScr (randomBase s) Random.frameBytes t.mem u.mem :=
    fun x hx => (hf1 x hx).trans (hf0 x hx).symm
  have hw (d : Nat) (hd : d + 8 ≤ 144 ∨ d = 152) : word u.mem (randomBase s) d = word t.mem (randomBase s) d := by
    have sep : ∀ r ∈ randomWriteRanges, d + 8 ≤ r.1 ∨ r.1 + r.2 ≤ d := by
      intro r hmem
      simp only [randomWriteRanges, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl <;> dsimp only <;> omega
    exact (hf.word_eq sep (by omega)).trans (hready.frame.word_eq sep (by omega)).symm
  have hkv : Keep randomVolatile t u := hk.mono (by decide)
  refine ⟨hstatus, hstatusWord, ⟨⟨m, draws', hready'⟩, hr.saved.congr (fun d _ hd => hw d (Or.inl hd)),
    (hw _ (Or.inr rfl)).trans hr.attempts, hk.2.1.trans hr.rd, hk.2.2.trans hr.wr,
    hr.key.congrK hmem hk, hr.digest.congrK hmem hk,
    fun r hc hn => (hkv.gpr (random_saved_not_volatile hc)).trans (hr.callee r hc hn),
    by rw [hmx]; exact hr.mxcsr⟩, ?_⟩
  intro k hk
  have hn := hnonce k hk
  simpa only [C, randomContextOf, random_q_length h, Random.oNonce] using hn

end VG.Proof.Dsa.X86_64
