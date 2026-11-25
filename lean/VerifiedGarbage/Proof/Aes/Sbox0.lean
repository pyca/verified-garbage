module

public import VerifiedGarbage.Proof.Aes.Bitsliced
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.Aes.InvSboxSpec

/-!
# Truth tables of the S-boxes that bitsliced code computes

Tables of 256 rows, as `Framework/Bitslice/Table.lean`'s: the eight inputs
(`sbIns`), the S-box (`sboxOfT`), and the S-box and inverse S-box without the
constant (`sbox0T`, `invSbox0T`), with the bit of each row.
-/

@[expose] public section

namespace VG.Proof.Aes

open VG VG.Bitslice

def sbIn (j : Nat) : Nat := tableOf (fun c => c.testBit j) 256
def sbIns : List Nat := (List.range 8).map sbIn

theorem row_sbIns {c : Nat} (hc : c < 256) : row sbIns c = BitVec.ofNat 8 c := by
  refine row_ext fun j hj => ?_
  simp only [sbIns, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, sbIn, testBit_tableOf, hc, decide_true, Bool.true_and,
    BitVec.getLsbD_ofNat, hj]

/-- `{63}` in every row. -/
def k63 : List Nat := (List.range 8).map fun j => if (0x63).testBit j then ONES else 0

theorem row_k63 {c : Nat} (hc : c < 256) : row k63 c = 0x63 := by
  refine row_ext fun j hj => ?_
  simp only [k63, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some,
    Option.getD_some, testBit_ite_ONES, hc, decide_true, Bool.and_true]
  exact (by decide : ∀ j < 8, (0x63 : Nat).testBit j = (0x63 : Byte).getLsbD j) j hj

def sboxOfT : List Nat := sboxT sbIns
def sbox0T : List Nat := xorT (sboxT sbIns) k63
def invSbox0T : List Nat := invSboxT (xorT sbIns k63)

theorem length_affT (A : List Nat) : (affT A).length = 8 := by simp [affT]

theorem sboxOfT_bit {c j : Nat} (hc : c < 256) (hj : j < 8) :
    (sboxOfT.getD j 0).testBit c = (Spec.Aes.sbox (BitVec.ofNat 8 c)).getLsbD j := by
  rw [← row_sbIns hc, ← row_sboxT (by decide) hc, getLsbD_row _ _ hj, sboxOfT]

theorem sbox0T_bit {c j : Nat} (hc : c < 256) (hj : j < 8) :
    (sbox0T.getD j 0).testBit c = (sbox0 (BitVec.ofNat 8 c)).getLsbD j := by
  rw [← getLsbD_row _ _ hj, sbox0T, row_xorT (A := sboxT sbIns) (length_affT _) (by decide), row_sboxT (by decide) hc,
    row_sbIns hc, row_k63 hc, sbox0]

theorem invSbox0T_bit {c j : Nat} (hc : c < 256) (hj : j < 8) :
    (invSbox0T.getD j 0).testBit c = (invSbox0 (BitVec.ofNat 8 c)).getLsbD j := by
  rw [← getLsbD_row _ _ hj, invSbox0T, row_invSboxT _ hc, row_xorT (by decide) (by decide), row_sbIns hc,
    row_k63 hc, invSbox0]

end VG.Proof.Aes
