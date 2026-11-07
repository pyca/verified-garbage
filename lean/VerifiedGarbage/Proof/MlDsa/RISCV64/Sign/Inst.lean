module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Sign.Top
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Sign.Inst
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.RISCV64.Sample.RejNtt
import VerifiedGarbage.Proof.MlDsa.RISCV64.Sample.ExpandMask
import VerifiedGarbage.Proof.MlDsa.RISCV64.Round.HighLow
import VerifiedGarbage.Proof.MlDsa.RISCV64.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.RISCV64.Round.MakeHint
import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.BitPack
import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.HintPackCT
public import VerifiedGarbage.Proof.MlDsa.Sample.RejNtt
public import VerifiedGarbage.Proof.MlDsa.Sample.Ball
import VerifiedGarbage.Proof.MlDsa.RISCV64.Sample.Ball
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlDsa.Sign.Leak
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA signing on RISC-V, with this library's primitives

The RISC-V implementations of the primitives (`prims`) are verified with at
most 1168 bytes of stack (the samplers' Keccak frames; the others use none),
and their frames use no more; with the 1168 bytes they are verified with, the
two samplers whose results signing branches on return
what depends only on their public data, and succeed only if their algorithm
finishes within `maxBounds` (`rn_ret`, `sb_ret`, from what their own proofs
say they return). So signing with them is verified with 1168
(`sign44_verified`, …).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Sign

open VG VG.RISCV64
open VG.Impl.MlDsa.RISCV64.Sign
open VG.Proof.MlDsa.Sign (ifn rejNTTPoly_mono sampleInBall_mono)
open VG.Proof.MlDsa.Sample (rnFold ballFold rejNTT_some sampleInBall_some)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The samplers' results -/

theorem rn_ret {s s' : State} {tr : List Leak} (h : (rejNTTContract RISCV64.abi 1168).pre s)
    (e : Exec isa Impl.MlDsa.RISCV64.Sample.rejNTT s tr s') :
    s'.gpr .a0 = if (rnFold [] (G (bytesAt s.mem (s.gpr .a0) 34) 1008)).length = 256 then 1 else 0 := by
  obtain ⟨_, _, e', h0, _⟩ := Sample.RejNtt.correct (Sample.RejNtt.spOk_of h)
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact h0

theorem rn_pub (s₁ s₂ : State) (h : (rejNTTContract RISCV64.abi 1168).pub s₁ s₂) :
    bytesAt s₁.mem (s₁.gpr .a0) 34 = bytesAt s₂.mem (s₂.gpr .a0) 34 := by
  sig_pub [rejNTTContract, rejNTTSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨_, hb, _⟩ := h
  exact Proof.MlDsa.Sign.leakBytes_inj hb

theorem sb_ret {s s' : State} {tr : List Leak} (h : (sampleInBallContract RISCV64.abi 1168).pre s)
    (e : Exec isa Impl.MlDsa.RISCV64.Sample.sampleInBall s tr s') :
    s'.gpr .a0 = if (ballFold ((s.gpr .a2).setWidth 32).toNat
      (H (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) 272)).2 = 256 then 1 else 0 := by
  obtain ⟨_, _, e', h0, _⟩ := Sample.Ball.correct (Sample.Ball.pre_of h)
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact h0

theorem sb_pub (s₁ s₂ : State) (h : (sampleInBallContract RISCV64.abi 1168).pub s₁ s₂) :
    (s₁.gpr .a2).setWidth 32 = (s₂.gpr .a2).setWidth 32 ∧
      bytesAt s₁.mem (s₁.gpr .a0) (s₁.gpr .a1).toNat = bytesAt s₂.mem (s₂.gpr .a0) (s₂.gpr .a1).toNat := by
  sig_pub [sampleInBallContract, sampleInBallSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨_, hb, _, _, h5, _⟩ := h
  exact ⟨h5, Proof.MlDsa.Sign.leakBytes_inj hb⟩

theorem zero_ne_one32 : (BitVec.setWidth 32 (0 : BitVec 64)) ≠ 1 := by decide

/-- The primitives satisfy what the proofs of signing need of them. -/
theorem prims_ok : SPrimsOk prims 1168 where
  ntt := ⟨⟨0, by decide, Arith.Ntt.verified⟩, by decide +kernel⟩
  invNtt := ⟨⟨0, by decide, Arith.NttInv.verified⟩, by decide +kernel⟩
  mul := ⟨⟨0, by decide, Arith.Mul.mul_verified⟩, by decide +kernel⟩
  mulAdd := ⟨⟨0, by decide, Arith.Mul.mulAdd_verified⟩, by decide +kernel⟩
  add := ⟨⟨0, by decide, Arith.AddSub.add_verified⟩, by decide +kernel⟩
  sub := ⟨⟨0, by decide, Arith.AddSub.sub_verified⟩, by decide +kernel⟩
  rejNTT := ⟨⟨1168, by decide, Sample.rejNTT_verified⟩, by decide +kernel⟩
  expandMask := ⟨⟨1168, by decide, Sample.expandMask_verified⟩, by decide +kernel⟩
  ball := ⟨⟨1168, by decide, Sample.sampleInBall_verified⟩, by decide +kernel⟩
  highBits := ⟨⟨0, by decide, Round.HighLow.high_verified⟩, by decide +kernel⟩
  lowBits := ⟨⟨0, by decide, Round.HighLow.low_verified⟩, by decide +kernel⟩
  normLt := ⟨⟨0, by decide, Round.NormLt.verified⟩, by decide +kernel⟩
  makeHint := ⟨⟨0, by decide, Round.MakeHint.verified⟩, by decide +kernel⟩
  simpleBitPack := ⟨⟨0, by decide, Pack.simpleBitPack_verified⟩, by decide +kernel⟩
  bitPack := ⟨⟨0, by decide, Pack.bitPack_verified⟩, by decide +kernel⟩
  bitUnpack := ⟨⟨0, by decide, Pack.bitUnpack_verified⟩, by decide +kernel⟩
  hintBitPack := ⟨⟨0, by decide, Pack.hintBitPack_verified⟩, by decide +kernel⟩
  rejX := ⟨1168, by decide, Sample.rejNTT_verified,
    fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ =>
      ⟨Sample.rejNTT_verified.2.1 s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂,
        show _ = _ by rw [rn_ret h₁ e₁, rn_ret h₂ e₂, rn_pub s₁ s₂ hp]⟩,
    fun s t s' h e h1 => by
      rw [rn_ret h e] at h1
      by_cases hf : (rnFold [] (G (bytesAt s.mem (s.gpr .a0) 34) 1008)).length = 256
      · rw [rejNTTPoly_mono (show 1008 ≤ maxBounds.rejNTT by decide) (rejNTT_some hf)]; rfl
      · rw [ifn hf] at h1; exact absurd h1 zero_ne_one32⟩
  ballX := ⟨1168, by decide, Sample.sampleInBall_verified,
    fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ =>
      ⟨Sample.sampleInBall_verified.2.1 s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂,
        show _ = _ by rw [sb_ret h₁ e₁, sb_ret h₂ e₂, (sb_pub s₁ s₂ hp).1, (sb_pub s₁ s₂ hp).2]⟩,
    fun s t s' h e h1 => by
      rw [sb_ret h e] at h1
      by_cases hf : (ballFold ((s.gpr .a2).setWidth 32).toNat
        (H (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) 272)).2 = 256
      · rw [sampleInBall_mono (show 272 ≤ maxBounds.ball by decide) (sampleInBall_some _ (by decide) hf)]; rfl
      · rw [ifn hf] at h1; exact absurd h1 zero_ne_one32⟩

theorem withCache44_sat : (Proof.MlDsa.signWithCacheContract mlDsa44 RISCV64.abi 1168).pre (signSat mlDsa44) := by
  sig_pre [Proof.MlDsa.signWithCacheContract, Proof.MlDsa.signWithCacheSig, signSig, RISCV64.abi,
    RISCV64.argRegs, signSat]
  sig_and_intros
  all_goals first
    | exact .inl rfl
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem withCache44_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Sign.withCache44
      (Proof.MlDsa.signWithCacheContract mlDsa44 RISCV64.abi 1168) :=
  sign_verified prims_ok (by decide) _ (.inl rfl) withCache44_sat

theorem withCache65_sat : (Proof.MlDsa.signWithCacheContract mlDsa65 RISCV64.abi 1168).pre (signSat mlDsa65) := by
  sig_pre [Proof.MlDsa.signWithCacheContract, Proof.MlDsa.signWithCacheSig, signSig, RISCV64.abi,
    RISCV64.argRegs, signSat]
  sig_and_intros
  all_goals first
    | exact .inl rfl
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem withCache65_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Sign.withCache65
      (Proof.MlDsa.signWithCacheContract mlDsa65 RISCV64.abi 1168) :=
  sign_verified prims_ok (by decide) _ (.inr (.inl rfl)) withCache65_sat

theorem withCache87_sat : (Proof.MlDsa.signWithCacheContract mlDsa87 RISCV64.abi 1168).pre (signSat mlDsa87) := by
  sig_pre [Proof.MlDsa.signWithCacheContract, Proof.MlDsa.signWithCacheSig, signSig, RISCV64.abi,
    RISCV64.argRegs, signSat]
  sig_and_intros
  all_goals first
    | exact .inl rfl
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem withCache87_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Sign.withCache87
      (Proof.MlDsa.signWithCacheContract mlDsa87 RISCV64.abi 1168) :=
  sign_verified prims_ok (by decide) _ (.inr (.inr rfl)) withCache87_sat

end VG.Proof.MlDsa.RISCV64.Sign
