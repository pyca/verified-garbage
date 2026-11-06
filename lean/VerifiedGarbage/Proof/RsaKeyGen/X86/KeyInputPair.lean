module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInput
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Retained public key arguments determine the register state used by imports and exports -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86

structure InputPair (E : Environment) (s t : State) : Prop where
  left : Input E s
  right : Input E t
  stack : s.gpr .esp = t.gpr .esp

end VG.Proof.RsaKeyGen.X86.Key
