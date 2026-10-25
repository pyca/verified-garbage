module

public import VerifiedGarbage.Impl.TripleDes.RISCV64.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.TripleDes.RISCV64.SboxTable
meta import VerifiedGarbage.Impl.TripleDes.RISCV64.Block
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.TripleDes.RISCV64.SboxTable
import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-! The S-boxes' inputs and outputs in a round, as literals. -/

@[expose] public section

namespace VG.Impl.TripleDes.RISCV64

open VG.RISCV64

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

end VG.Impl.TripleDes.RISCV64
