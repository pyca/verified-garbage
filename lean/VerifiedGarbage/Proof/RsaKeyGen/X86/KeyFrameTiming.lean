module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyBodyTiming
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # The outer native key frame preserves trace equivalence -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86

def FramedPair (E : Environment) (sp : BitVec 32) (e p q p' q' : Nat) (s t : State) : Prop :=
  BodyPair E sp e p q p' q' (Compact.entered s) (Compact.entered t) ∧ s.gpr .esp = t.gpr .esp

end VG.Proof.RsaKeyGen.X86.Key
