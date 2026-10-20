module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeBytesCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeConstantsCT
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Arguments

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeArguments
import VerifiedGarbage.Proof.Framework.Omega

/-! # Only the argument-bearing frame words are public at a primality call -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 VG.Impl.Dsa.Generation.Layout

structure PrimeFramePublic where
  bytes : PrimeBytesPublic
  F : Addr
  candidate : Nat
  candidateBound : candidate < 2 ^ 16
  checksBound : bytes.call.draw.prime.checks < 2 ^ 16
  checks : bytes.call.draw.prime.checks = Spec.Dsa.primeChecks (Spec.Dsa.bitLength bytes.call.draw.prime.N)
  source : bytes.source = VG.Proof.Bignum.off bytes.call.arena candidate
  witness : bytes.call.draw.prime.p = VG.Proof.Bignum.off bytes.call.arena witness
  separate : ∀ k < 34, ∀ j < 32,
    Mem.Sep (VG.Proof.Bignum.off F (8 * k)) 8 (VG.Proof.Bignum.off bytes.call.draw.prime.B (8 * j)) 8

  outside : ∀ k < 34, ∀ i < 8, bytes.call.draw.prime.Z ≤
    ofs bytes.call.draw.prime.B (VG.Proof.Bignum.off (VG.Proof.Bignum.off F (8 * k)) i)

structure PrimeFrameInputs (p : PrimeFramePublic) (s : State) : Prop where
  stack : s.sp = p.F
  read : ∀ k < 34, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.off p.F (8 * k)) 8
  arena : VG.Proof.Bignum.word s.mem p.F 40 = p.bytes.call.arena
  tapePtr : VG.Proof.Bignum.word s.mem p.F 112 = p.bytes.call.draw.prime.rp
  tapeLength : VG.Proof.Bignum.word s.mem p.F 120 = BitVec.ofNat 64 p.bytes.call.draw.prime.rand.length
  used : VG.Proof.Bignum.word s.mem p.F 128 = BitVec.ofNat 64 p.bytes.call.draw.used
  tape : Src s p.bytes.call.draw.prime.B p.bytes.call.draw.prime.Z
    p.bytes.call.draw.prime.rp p.bytes.call.draw.prime.rand
  source : Src s p.bytes.call.draw.prime.B p.bytes.call.draw.prime.Z p.bytes.source p.bytes.bytes
  writable : ∀ i < p.bytes.call.draw.prime.len, InRegions s.wr (VG.Proof.Bignum.off p.bytes.call.draw.prime.p i) 1
  usedBound : p.bytes.call.draw.used ≤ p.bytes.call.draw.prime.rand.length

structure PrimeFrameState (p : PrimeFramePublic) (s : State) : Prop extends PrimeFrameInputs p s where
  good : PrimeGood p.bytes.call.draw.prime s

def PrimeFrameBefore (candidate len draw checks : Nat) (p : PrimeFramePublic) (s : State) : Prop :=
  PrimeFrameState p s ∧ p.candidate = candidate ∧ p.bytes.call.draw.prime.len = len ∧
    p.bytes.call.draw.prime.drawBytes = draw ∧ p.bytes.call.draw.prime.checks = checks

theorem primeFrame_arguments {candidate len draw checks : Nat} {p : PrimeFramePublic} {s : State}
    (h : PrimeFrameBefore candidate len draw checks p s) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.headerArguments
      (Impl.Dsa.AArch64.Generation.primeArguments candidate len draw checks))) s
      (PrimeBytesBefore len draw p.bytes) := by
  have hg := h.1.good
  have hw := primeArguments_ok hg p.candidateBound p.checksBound h.1.stack h.1.read
    (W := fun k => VG.Proof.Bignum.word s.mem p.F (8 * k)) (fun _ _ => rfl) p.separate
    (by change VG.Proof.Bignum.word s.mem p.F 40 + BitVec.ofNat 64 witness = _
        rw [h.1.arena, p.witness])
    h.1.tapePtr h.1.tapeLength h.1.used h.1.tape h.1.writable
  rw [h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2] at hw
  refine WP.mono hw fun t ⟨ht, hp, hf, hk⟩ => ?_
  refine ⟨ht, ?_, ?_, h.1.usedBound, h.2.2.1, h.2.2.2.1⟩
  · rw [p.source, h.2.1]
    simpa only [VG.Proof.Bignum.off, h.1.arena] using hp
  · apply h.1.source.congrK _ hk
    intro a ha
    exact hf a (Or.inr (Nat.le_trans p.bytes.call.draw.prime.z256 ha))

end VG.Proof.Dsa.AArch64.Generation
