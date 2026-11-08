module

import VerifiedGarbage.Proof.TripleDes.Bitslice.LayoutLit
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Bitsliced
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.TripleDes.Bitslice.LayoutLit
meta import VerifiedGarbage.Impl.TripleDes.PPC64LE.Bitsliced
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit

/-! # The bitsliced S-box circuits' code, as literals -/

@[expose] public section

namespace VG.Impl.TripleDes.PPC64LE.Bitslice

open VG.PPC64LE

-- The circuits' code and their outputs' registers (written out in `Impl`), as
-- tables, which the literals below and the functions' literals (`Lit`) read.
materialize_table sboxCode 8
materialize_table outReg 8 4

-- The transposition, once.
materialize_value transposeBody

-- The exchange of the halves, once.
materialize_value swapHalves

def sbox0 : Prog isa := .block (sboxCode 0)
def sbox1 : Prog isa := .block (sboxCode 1)
def sbox2 : Prog isa := .block (sboxCode 2)
def sbox3 : Prog isa := .block (sboxCode 3)
def sbox4 : Prog isa := .block (sboxCode 4)
def sbox5 : Prog isa := .block (sboxCode 5)
def sbox6 : Prog isa := .block (sboxCode 6)
def sbox7 : Prog isa := .block (sboxCode 7)

materialize_code sbox0
materialize_code sbox1
materialize_code sbox2
materialize_code sbox3
materialize_code sbox4
materialize_code sbox5
materialize_code sbox6
materialize_code sbox7

def transposeProg : Prog isa := .block transposeBody

materialize_code transposeProg

end VG.Impl.TripleDes.PPC64LE.Bitslice
