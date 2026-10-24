module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Top
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sign.Inst
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.ExpandMask
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.BallCT
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Round.HighLow
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Round.MakeHint
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.BitPack
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.HintPackCT
public import VerifiedGarbage.Proof.MlDsa.Sample.RejNtt
public import VerifiedGarbage.Proof.MlDsa.Sample.Ball
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.Ball
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlDsa.Sign.Leak
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA signing on PPC64LE, with this library's primitives

The PPC64LE implementations of the primitives (`prims`) are verified with at
most 96 bytes of stack, and their frames use no more; with the 48 bytes they
are verified with, the two samplers whose results signing branches on return
what depends only on their public data, and succeed only if their algorithm
finishes within `maxBounds` (`rn_ret`, `sb_ret`, from what their own proofs
say they return). So signing with them is verified with 96
(`sign44_verified`, …).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sign

open VG VG.PPC64LE
open VG.Impl.MlDsa.PPC64LE.Sign
open VG.Proof.MlDsa.Sign (ifn rejNTTPoly_mono sampleInBall_mono)
open VG.Proof.MlDsa.Sample (rnFold ballFold rejNTT_some sampleInBall_some)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The samplers' results -/

theorem rn_ret {s s' : State} {tr : List Leak} (h : (rejNTTContract PPC64LE.abi 48).pre s)
    (e : Exec isa Impl.MlDsa.PPC64LE.Sample.rejNTT s tr s') :
    s'.gpr .r3 = if (rnFold [] (G (bytesAt s.mem (s.gpr .r3) 34) 1008)).length = 256 then 1 else 0 := by
  obtain ⟨_, _, e', h0, _⟩ := Sample.RejNtt.correct (Sample.RejNtt.spOk_of h)
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact h0

theorem rn_pub (s₁ s₂ : State) (h : (rejNTTContract PPC64LE.abi 48).pub s₁ s₂) :
    bytesAt s₁.mem (s₁.gpr .r3) 34 = bytesAt s₂.mem (s₂.gpr .r3) 34 := by
  sig_pub [rejNTTContract, rejNTTSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨_, hb, _⟩ := h
  exact Proof.MlDsa.Sign.leakBytes_inj hb

theorem sb_ret {s s' : State} {tr : List Leak} (h : (sampleInBallContract PPC64LE.abi 48).pre s)
    (e : Exec isa Impl.MlDsa.PPC64LE.Sample.sampleInBall s tr s') :
    s'.gpr .r3 = if (ballFold ((s.gpr .r5).setWidth 32).toNat
      (H (bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) 272)).2 = 256 then 1 else 0 := by
  obtain ⟨_, _, e', h0, _⟩ := Sample.Ball.correct (Sample.Ball.pre_of h)
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact h0

theorem sb_pub (s₁ s₂ : State) (h : (sampleInBallContract PPC64LE.abi 48).pub s₁ s₂) :
    (s₁.gpr .r5).setWidth 32 = (s₂.gpr .r5).setWidth 32 ∧
      bytesAt s₁.mem (s₁.gpr .r3) (s₁.gpr .r4).toNat = bytesAt s₂.mem (s₂.gpr .r3) (s₂.gpr .r4).toNat := by
  sig_pub [sampleInBallContract, sampleInBallSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨_, hb, _, _, h5, _⟩ := h
  exact ⟨h5, Proof.MlDsa.Sign.leakBytes_inj hb⟩

theorem zero_ne_one32 : (BitVec.setWidth 32 (0 : BitVec 64)) ≠ 1 := by decide

/-- The primitives satisfy what the proofs of signing need of them. -/
theorem prims_ok : SPrimsOk prims 96 where
  ntt := ⟨⟨96, by decide, Arith.Ntt.verified⟩, by decide +kernel⟩
  invNtt := ⟨⟨96, by decide, Arith.NttInv.verified⟩, by decide +kernel⟩
  mul := ⟨⟨0, by decide, Arith.Mul.mul_verified⟩, by decide +kernel⟩
  mulAdd := ⟨⟨0, by decide, Arith.Mul.mulAdd_verified⟩, by decide +kernel⟩
  add := ⟨⟨0, by decide, Arith.AddSub.add_verified⟩, by decide +kernel⟩
  sub := ⟨⟨0, by decide, Arith.AddSub.sub_verified⟩, by decide +kernel⟩
  rejNTT := ⟨⟨48, by decide, Sample.rejNTT_verified⟩, by decide +kernel⟩
  expandMask := ⟨⟨48, by decide, Sample.expandMask_verified⟩, by decide +kernel⟩
  ball := ⟨⟨48, by decide, Sample.sampleInBall_verified⟩, by decide +kernel⟩
  highBits := ⟨⟨0, by decide, Round.HighLow.high_verified⟩, by decide +kernel⟩
  lowBits := ⟨⟨0, by decide, Round.HighLow.low_verified⟩, by decide +kernel⟩
  normLt := ⟨⟨0, by decide, Round.NormLt.verified⟩, by decide +kernel⟩
  makeHint := ⟨⟨0, by decide, Round.MakeHint.verified⟩, by decide +kernel⟩
  simpleBitPack := ⟨⟨0, by decide, Pack.simpleBitPack_verified⟩, by decide +kernel⟩
  bitPack := ⟨⟨0, by decide, Pack.bitPack_verified⟩, by decide +kernel⟩
  bitUnpack := ⟨⟨0, by decide, Pack.bitUnpack_verified⟩, by decide +kernel⟩
  hintBitPack := ⟨⟨0, by decide, Pack.hintBitPack_verified⟩, by decide +kernel⟩
  rejX := ⟨48, by decide, Sample.rejNTT_verified,
    fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ =>
      ⟨Sample.rejNTT_verified.2.1 s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂,
        show _ = _ by rw [rn_ret h₁ e₁, rn_ret h₂ e₂, rn_pub s₁ s₂ hp]⟩,
    fun s t s' h e h1 => by
      rw [rn_ret h e] at h1
      by_cases hf : (rnFold [] (G (bytesAt s.mem (s.gpr .r3) 34) 1008)).length = 256
      · rw [rejNTTPoly_mono (show 1008 ≤ maxBounds.rejNTT by decide) (rejNTT_some hf)]; rfl
      · rw [ifn hf] at h1; exact absurd h1 zero_ne_one32⟩
  ballX := ⟨48, by decide, Sample.sampleInBall_verified,
    fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ =>
      ⟨Sample.sampleInBall_verified.2.1 s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂,
        show _ = _ by rw [sb_ret h₁ e₁, sb_ret h₂ e₂, (sb_pub s₁ s₂ hp).1, (sb_pub s₁ s₂ hp).2]⟩,
    fun s t s' h e h1 => by
      rw [sb_ret h e] at h1
      by_cases hf : (ballFold ((s.gpr .r5).setWidth 32).toNat
        (H (bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) 272)).2 = 256
      · rw [sampleInBall_mono (show 272 ≤ maxBounds.ball by decide) (sampleInBall_some _ (by decide) hf)]; rfl
      · rw [ifn hf] at h1; exact absurd h1 zero_ne_one32⟩

theorem sign44_sat : (signContract mlDsa44 PPC64LE.abi 96).pre (signSat mlDsa44) := by
  sig_sat_check [signContract, signSig, PPC64LE.abi, PPC64LE.argRegs, signSat]

theorem sign44_verified : Verified PPC64LE.target sign44 (signContract mlDsa44 PPC64LE.abi 96) :=
  sign_verified prims_ok (by decide) _ (.inl rfl) sign44_sat

theorem sign65_sat : (signContract mlDsa65 PPC64LE.abi 96).pre (signSat mlDsa65) := by
  sig_sat_check [signContract, signSig, PPC64LE.abi, PPC64LE.argRegs, signSat]

theorem sign65_verified : Verified PPC64LE.target sign65 (signContract mlDsa65 PPC64LE.abi 96) :=
  sign_verified prims_ok (by decide) _ (.inr (.inl rfl)) sign65_sat

theorem sign87_sat : (signContract mlDsa87 PPC64LE.abi 96).pre (signSat mlDsa87) := by
  sig_sat_check [signContract, signSig, PPC64LE.abi, PPC64LE.argRegs, signSat]

theorem sign87_verified : Verified PPC64LE.target sign87 (signContract mlDsa87 PPC64LE.abi 96) :=
  sign_verified prims_ok (by decide) _ (.inr (.inr rfl)) sign87_sat

end VG.Proof.MlDsa.PPC64LE.Sign
