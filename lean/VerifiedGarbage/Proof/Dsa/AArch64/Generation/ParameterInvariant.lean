module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TapeIteration

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Generation.Chunks
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory

/-! # The outer seed loop retains the exact remaining parameter search -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def GenerationContext.remaining (p : GenerationContext) (seedUsed randUsed : Nat) : Option Spec.Dsa.Params :=
  Spec.Dsa.generateParameters.attempt (8 * p.geo.pLen)
    ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE) (8 * p.geo.qLen)
    (Spec.Dsa.generationChunks p.geo.qLen (p.seeds.bytes.drop seedUsed)) (p.rand.bytes.drop randUsed)

def ParameterInvariant (p : GenerationContext) (expected : Option Spec.Dsa.Params) (initial : State)
    (seedUsed : Nat) (s : State) : Prop :=
  ∃ W randUsed, GenerationMemory p W s ∧ randUsed ≤ p.rand.bytes.length ∧
    W 10 = BitVec.ofNat 64 seedUsed ∧ W 16 = BitVec.ofNat 64 randUsed ∧
    expected = p.remaining seedUsed randUsed ∧ Frame p.changed initial.mem s.mem ∧
    s.rd = initial.rd ∧ s.wr = initial.wr

theorem GenerationContext.status_frame {p : GenerationContext} {m m' : Mem}
    (h : Outside p.geo.F 152 8 m m') : Frame p.changed m m' := by
  apply GenerationContext.frame_single
  intro a ha
  apply h a
  right
  have hn := ha ⟨p.geo.F, frameBytes⟩ (by simp)
  change ¬ ofs p.geo.F a < frameBytes at hn
  unfold frameBytes at hn
  omega

end VG.Proof.Dsa.AArch64.Generation
