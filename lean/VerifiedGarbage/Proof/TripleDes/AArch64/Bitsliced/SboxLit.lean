module

import VerifiedGarbage.Proof.TripleDes.Bitslice.LayoutLit
meta import VerifiedGarbage.Proof.TripleDes.Bitslice.LayoutLit
public import VerifiedGarbage.Impl.TripleDes.AArch64.Bitsliced
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.TripleDes.AArch64.Bitsliced
import VerifiedGarbage.Impl.TripleDes.AArch64.BitsliceAlloc
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Impl.TripleDes.AArch64.BitsliceAlloc
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target

/-! # The AdvSIMD S-box circuits' and transposition's code, and the circuits' output registers, as literals -/

@[expose] public section

namespace VG.Impl.TripleDes.AArch64.BitsliceNeon

open VG.AArch64

-- The circuits' code and output registers (written out in `Impl`), as one
-- table, which the literals below, `outRegsTable` and the functions' literals
-- (`Lit`) read.
materialize_table sboxCompiled 8

-- Pairs of rounds and the exchange of the halves, once.
materialize_value roundPairEncrypt := roundPair .encrypt
materialize_value roundPairDecrypt := roundPair .decrypt
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

-- The transposition, once.
materialize_code transpose

end VG.Impl.TripleDes.AArch64.BitsliceNeon

namespace VG

materialize_value Impl.TripleDes.AArch64.BitsliceNeon.outRegsTable

end VG
