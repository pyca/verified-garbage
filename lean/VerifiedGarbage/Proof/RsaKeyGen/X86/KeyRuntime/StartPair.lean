module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.CoreReadonlyTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyArgContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyImportedPair
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWritePortTiming
import VerifiedGarbage.Proof.MillerRabin.X86.MontFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateParameters

/-! # The two runs' starting states: inputs, workspaces and argument records -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Dsa.X86
open VG.Proof.RsaKeyGen.X86.Key (Environment SizedStart OutputPair)
open VG.Proof.RsaKeyGen.X86.KeyArgs (Context)

structure RuntimeStart (E : Environment) (sp : BitVec 32) (e p q p' q' : Nat) (s t : State) : Prop where
  start : SizedStart E e p q p' q' s t
  left : Ws s E.base E.size E.n 32
  right : Ws t E.base E.size E.n 32
  leftArgs : Context E.base E.size sp E.argument s
  rightArgs : Context E.base E.size sp E.argument t

end VG.Proof.RsaKeyGen.X86.KeyRuntime
