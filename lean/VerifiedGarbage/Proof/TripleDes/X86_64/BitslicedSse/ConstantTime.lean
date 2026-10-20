module

public import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.ConstantTime
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Lit
public import VerifiedGarbage.Impl.TripleDes.X86_64.BitslicedSse
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Lit
import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.SboxLit
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.SboxLit
meta import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.ConstantTime
meta import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Lit
meta import VerifiedGarbage.Impl.TripleDes.X86_64.BitslicedSse
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Lit
meta import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.SboxLit
meta import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.SboxLit

/-!
# Constant time

As for the 64-block code: the pointers, the count of blocks and the stack
pointer are public, and so is everything the function computes from them
(the batches, the counts of passes and rounds, the addresses of the round
keys), which the batches of 128 blocks keep in registers.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.BitslicedSse

open VG VG.X86_64
open VG.Proof.TripleDes.X86_64.Bitsliced (ecbTaint)

/-! The analyses, with the summaries of the 64-block code they end with. -/

taint_summary encSum : taintS ecbTaint Impl.TripleDes.X86_64.BitsliceSse.encrypt
  using Bitsliced.encSum
taint_summary decSum : taintS ecbTaint Impl.TripleDes.X86_64.BitsliceSse.decrypt
  using Bitsliced.decSum

theorem encrypt_constantTime (pre : State → Prop) (pub : State → State → Prop)
    (hagree : ∀ s t, pre s → pre t → pub s t → X86_64.Taint.Agree ecbTaint s t) :
    ConstantTime isa pre pub Impl.TripleDes.X86_64.BitsliceSse.encrypt :=
  let ⟨_, h⟩ := VG.Taint.exists_check_of_sumOk encSum (by decide +kernel)
  VG.Taint.constantTime (A := taintS) ecbTaint hagree h

theorem decrypt_constantTime (pre : State → Prop) (pub : State → State → Prop)
    (hagree : ∀ s t, pre s → pre t → pub s t → X86_64.Taint.Agree ecbTaint s t) :
    ConstantTime isa pre pub Impl.TripleDes.X86_64.BitsliceSse.decrypt :=
  let ⟨_, h⟩ := VG.Taint.exists_check_of_sumOk decSum (by decide +kernel)
  VG.Taint.constantTime (A := taintS) ecbTaint hagree h

end VG.Proof.TripleDes.X86_64.BitslicedSse
