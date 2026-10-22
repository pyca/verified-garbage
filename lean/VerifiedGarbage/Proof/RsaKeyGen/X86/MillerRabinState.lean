module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
import VerifiedGarbage.Proof.RsaKeyGen.MrCounts
public import VerifiedGarbage.Proof.RsaKeyGen.MrLoopAt
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessChecks
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedDataGap
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory

/-! # Exact entropy and counter invariants of the blinded witness loop -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Proof.RsaKeyGen

structure Parameters where
  g : Geometry
  capacity : Nat
  p : BitVec 32
  rand : BitVec 32
  randLen : Nat
  candidate : Nat
  entropy : Spec.RsaKeyGen.Rand
  /-- The uniform witnesses required (`checksForSize` for RSA, `primeChecks` for DSA). -/
  checks : Nat
  /-- The offset of the first witness in the tape: after the candidate's own
  octets for RSA, 0 for DSA. -/
  start : Nat

def Parameters.bytes (P : Parameters) : Nat := 8 * P.g.w
def Parameters.twos (P : Parameters) : Nat × Nat := Spec.Rsa.splitTwos (P.candidate - 1)

/-- The result of the blinded loop on the witnesses from `start` on. -/
def Parameters.test (P : Parameters) : Option (Bool × Spec.RsaKeyGen.Rand) :=
  Spec.RsaKeyGen.loop (Spec.RsaKeyGen.mrStep P.candidate P.checks P.twos.1 P.twos.2) (1, 0) (P.entropy.drop P.start)

structure Parameters.Valid (P : Parameters) : Prop where
  geometry : P.g.Valid
  length : P.g.L = 8 * P.capacity
  randFit : P.rand.toNat + P.randLen ≤ 2 ^ 32
  randLenFit : P.randLen < 2 ^ 32
  entropyLength : P.entropy.length = P.randLen
  randSeparate : (⟨P.rand.setWidth 64, P.randLen⟩ : Region).Disjoint ⟨P.g.W, P.g.L⟩
  randStackFar : (⟨P.rand.setWidth 64, P.randLen⟩ : Region).Disjoint (below P.p 68)
  low : 68 ≤ P.p.toNat
  stackFar : (⟨P.g.W, P.g.L⟩ : Region).Disjoint (below P.p 68)
  lengthFar : (lengthRegion P.p).Disjoint (below P.p 68)
  odd : P.candidate % 2 = 1
  large : 3 < P.candidate
  shape : Spec.RsaKeyGen.bitLength (P.candidate - 1) = 64 * P.g.w
  witnessBytes : Spec.RsaKeyGen.witnessBytes P.candidate = P.bytes
  checksFit : P.checks < 2 ^ 32

structure StateAt (P : Parameters) (k n : Nat) (s : State) : Prop where
  prepared : Prepare.Data P.g P.candidate P.capacity P.p s
  readable : InRegions (s.rd ++ s.wr) (P.rand.setWidth 64) P.randLen
  entropy : Spec.Rsa.bytesAt s.mem (P.rand.setWidth 64) P.randLen = P.entropy
  randPtr : s.mem.readW (off P.g.W 28) 32 = P.rand
  randLength : w32 s.mem P.g.W 32 = P.randLen
  used : w32 s.mem P.g.W 152 = P.start + P.bytes * k
  rounds : w32 s.mem P.g.W 176 = k
  uniform : w32 s.mem P.g.W 192 = (mrSB P.candidate P.bytes P.start P.entropy k).2
  checks : w32 s.mem P.g.W 200 = P.checks
  atLoop : MrLoopAt P.candidate P.checks P.twos.1 P.twos.2 P.bytes P.start P.entropy k n

theorem StateAt.keepMem {P : Parameters} (v : P.Valid) {s t : State} {k n : Nat}
    (S : StateAt P k n s) (mem : t.mem = s.mem) {regs : List Reg} (K : Keeps regs s t)
    (base : .edi ∉ regs) (sp : .esp ∉ regs) : StateAt P k n t := by
  refine ⟨S.prepared.keepHeader v.geometry (d := 128) (bytes := 0) (by decide) (by decide)
    (by rw [mem]; exact Outside.refl _ _ _ _) K base sp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, S.atLoop⟩
  · rw [K.2.1, K.2.2]; exact S.readable
  · rw [mem]; exact S.entropy
  · rw [mem]; exact S.randPtr
  · rw [mem]; exact S.randLength
  · rw [mem]; exact S.used
  · rw [mem]; exact S.rounds
  · rw [mem]; exact S.uniform
  · rw [mem]; exact S.checks

theorem StateAt.countFit {P : Parameters} (v : P.Valid) {s : State} {k n : Nat} (S : StateAt P k n s) :
    w32 s.mem P.g.W 176 + 1 < 2 ^ 32 ∧ w32 s.mem P.g.W 192 + 1 < 2 ^ 32 := by
  have used := S.atLoop.used
  have positive : 2 ≤ P.bytes := by have := v.geometry.minWidth; unfold Parameters.bytes; omega
  have count := Nat.mul_le_mul_right k positive
  rw [v.entropyLength] at used
  rw [S.rounds, S.uniform]
  have uniform := mrSB_uniform_le P.candidate P.bytes P.start P.entropy k
  have bound := v.randLenFit
  constructor <;> omega

theorem StateAt.sample {P : Parameters} {s : State} {k n : Nat} (S : StateAt P k n s)
    (enough : P.start + P.bytes * k + P.bytes ≤ P.randLen) :
    Spec.RsaKeyGen.witness (P.candidate - 1)
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off (P.rand.setWidth 64) (P.start + P.bytes * k)) P.bytes)) =
      wit P.candidate P.bytes P.entropy (P.start + P.bytes * k) := by
  unfold wit
  rw [← S.entropy, seg_bytesAt _ _ enough]

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop
