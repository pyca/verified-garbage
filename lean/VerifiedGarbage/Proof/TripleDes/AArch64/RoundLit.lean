module

import VerifiedGarbage.Proof.TripleDes.AArch64.SboxTable
meta import VerifiedGarbage.Proof.TripleDes.AArch64.SboxTable
public import VerifiedGarbage.Impl.TripleDes.AArch64.Block
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.TripleDes.AArch64.Block
import VerifiedGarbage.Impl.Aes.AArch64.Alloc
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Impl.Aes.AArch64.Alloc
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.AArch64.Target

@[expose] public section

namespace VG.Impl.TripleDes.AArch64

open VG.AArch64

materialize_code sboxInputs0 := (.block (sboxInputs 0) : Prog isa)
materialize_code sboxInputs1 := (.block (sboxInputs 1) : Prog isa)
materialize_code sboxInputs2 := (.block (sboxInputs 2) : Prog isa)
materialize_code sboxInputs3 := (.block (sboxInputs 3) : Prog isa)
materialize_code sboxInputs4 := (.block (sboxInputs 4) : Prog isa)
materialize_code sboxInputs5 := (.block (sboxInputs 5) : Prog isa)
materialize_code sboxInputs6 := (.block (sboxInputs 6) : Prog isa)
materialize_code sboxInputs7 := (.block (sboxInputs 7) : Prog isa)
materialize_code sboxOutputs0 := (.block (sboxOutputs 0) : Prog isa)
materialize_code sboxOutputs1 := (.block (sboxOutputs 1) : Prog isa)
materialize_code sboxOutputs2 := (.block (sboxOutputs 2) : Prog isa)
materialize_code sboxOutputs3 := (.block (sboxOutputs 3) : Prog isa)
materialize_code sboxOutputs4 := (.block (sboxOutputs 4) : Prog isa)
materialize_code sboxOutputs5 := (.block (sboxOutputs 5) : Prog isa)
materialize_code sboxOutputs6 := (.block (sboxOutputs 6) : Prog isa)
materialize_code sboxOutputs7 := (.block (sboxOutputs 7) : Prog isa)

end VG.Impl.TripleDes.AArch64
