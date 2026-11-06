module

public import VerifiedGarbage.Proof.RsaOaep.AArch64.CtBase
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Mgf
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.RsaOaep.AArch64.TaintImm
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.CtBase
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Mgf
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.TaintImm
meta import VerifiedGarbage.Proof.Mgf1.Bytes
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# RSAES-OAEP on AArch64: MGF1 in constant time

MGF1's slots and the counter in theirs (`MX`), which two runs of MGF1 in
the same frame and working space share at each round, and the lemmas
their proofs use.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.RsaOaep.AArch64.Mgf1 (seqs round xorOut xorHead xorBody nextCtr initArgs updSrcArgs updCtrArgs finArgs
  mgfXor)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK)

/-- MGF1's slots, and the counter `c` and `done` in theirs. -/
def MX (S : Addr) (src srcLen dst dstLen D c : Nat) (W : Nat → BitVec 64) (_ : State) : Prop :=
  MArgs W S src srcLen dst dstLen ∧ W 17 = BitVec.ofNat 64 c ∧ W 18 = BitVec.ofNat 64 (c * D)

theorem lt_ceil {a D j : Nat} (hD : 0 < D) : j < (a + D - 1) / D ↔ j * D < a := by
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hD, Nat.succ_mul]; omega

theorem updCtrArgs_eq : updCtrArgs lay = Mgf1.scr lay .x2 lay.oCtr ++ (([.ldrSp .x10 lay.sCtr, .strb .x10 .x2 3,
    .lsr .x .x10 .x10 8, .strb .x10 .x2 2, .lsr .x .x10 .x10 8, .strb .x10 .x2 1, .lsr .x .x10 .x10 8,
    .strb .x10 .x2 0] : List Instr) ++ Mgf1.scr lay .x0 lay.oSt ++ ([.ldrSp .x1 lay.sSrcLen, .movz .x .x3 4 0] :
    List Instr) ++ Mgf1.scr lay .x4 lay.oW) := by
  simp only [updCtrArgs, List.append_assoc]

variable {G : Hash} (hG : StreamOK G.stream)

end VG.Proof.RsaOaep.AArch64
