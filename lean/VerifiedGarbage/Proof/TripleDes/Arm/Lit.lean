import VerifiedGarbage.Impl.TripleDes.Arm.Sbox
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.TripleDes.Arm.Block
import VerifiedGarbage.Impl.TripleDes.Arm.Permutation

/-! ## `SboxTable` -/

section

/-!
The code of the eight S-boxes (written out in `Impl`) as one table
(`materialize_table`), which the literals of the code that runs them read.
-/

namespace VG

materialize_table Impl.TripleDes.Arm.sboxCode 8

end VG

end

/-! ## `RoundLit` -/

section

namespace VG.Impl.TripleDes.Arm

open VG.Arm

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

end VG.Impl.TripleDes.Arm

end

/-! ## `Lit` -/

section

namespace VG.Impl.TripleDes.Arm

materialize_code sbox0
materialize_code sbox1
materialize_code sbox2
materialize_code sbox3
materialize_code sbox4
materialize_code sbox5
materialize_code sbox6
materialize_code sbox7


materialize_code initialPermutation
materialize_code finalPermutation
materialize_code keyPermutation1
materialize_code keyPermutation2

end VG.Impl.TripleDes.Arm

end
