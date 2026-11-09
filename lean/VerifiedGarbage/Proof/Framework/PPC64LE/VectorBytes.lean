module

public import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector

/-!
# Bytes of PPC64LE's general-purpose and vector registers

The bytes of a doubleword (`gbyte`, from the least significant) and of a
vector register (`vbyte`, from the most significant), through the moves
between the two (`mtvsrd`, `mfvsrd`), and the vector instructions that act
on each byte (`vperm`, `vxor`, `vsbox`): what the single-block cores' S-box
layers (SM4's, Camellia's) compute. `TabOk`: a table of sixteen bytes in a
vector register, which `vperm` looks up (`vperm_byte`, `vperm_byte2`).
-/

@[expose] public section

namespace VG.PPC64LE.Bytes

open VG.PPC64LE

/-! ## Bytes -/

/-- Byte `k` of a doubleword, from the least significant. -/
abbrev gbyte (x : BitVec 64) (k : Nat) : BitVec 8 := x.extractLsb' (8 * k) 8

theorem gbyte_and (x y : BitVec 64) (k : Nat) : gbyte (x &&& y) k = gbyte x k &&& gbyte y k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, hi, decide_true, Bool.true_and]

theorem gbyte_xor (x y : BitVec 64) (k : Nat) : gbyte (x ^^^ y) k = gbyte x k ^^^ gbyte y k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, hi, decide_true, Bool.true_and]

/-- The register's doubleword `x`, moved to the high doubleword of a vector
register: its byte `k` is the vector's byte `7 - k`. -/
theorem vbyte_append (x u : BitVec 64) {k : Nat} (hk : k < 8) : vbyte (x ++ u) (7 - k) = gbyte x k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
  split
  · omega
  · congr 1; omega

theorem gbyte_vdword (v : BitVec 128) {k : Nat} (hk : k < 8) : gbyte (vdword v 0) k = vbyte v (7 - k) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vdword, vbyte, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  rw [show 64 * (1 - 0) + (8 * k + i) = 8 * (15 - (7 - k)) + i by omega]
  simp only [show 8 * k + i < 64 by omega, decide_true, Bool.true_and]

theorem toNat_and_0f (b : BitVec 8) : (b &&& 0x0f).toNat < 16 := by
  rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem toNat_shr4 (b : BitVec 8) : (b >>> 4).toNat < 16 := by
  rw [BitVec.toNat_ushiftRight]; have := b.isLt
  rw [Nat.shiftRight_eq_div_pow]; omega

/-! ## Vector instructions -/

theorem vbyte_xor' (a b : BitVec 128) (i : Nat) : vbyte (a ^^^ b) i = vbyte a i ^^^ vbyte b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, hj, decide_true, Bool.true_and]

theorem exec_mtvsrd {s : State} {d : VReg} {n : Reg} :
    exec (.mtvsrd d n) s = some { s.writeV d (s.gpr n ++ s.unknowns 0) with
      unknowns := fun i => s.unknowns (i + 1) } := rfl

theorem exec_mfvsrd {s : State} {d : Reg} {n : VReg} :
    exec (.mfvsrd d n) s = some (s.write d (vdword (s.vpr n) 0)) := rfl

theorem exec_vperm {s : State} {d n m c : VReg} :
    exec (.vop (.perm d n m c)) s = some (s.writeV d (ofVBytes fun i =>
      let j := (vbyte (s.vpr c) i).toNat % 32
      if j < 16 then vbyte (s.vpr n) j else vbyte (s.vpr m) (j - 16))) := rfl

theorem exec_vxor {s : State} {d n m : VReg} :
    exec (.vop (.logic .xor d n m)) s = some (s.writeV d (s.vpr n ^^^ s.vpr m)) := rfl

theorem exec_vsbox {s : State} {d n : VReg} :
    exec (.vop (.sbox d n)) s =
      some (s.writeV d (ofVBytes fun i => VectorCrypto.aesSbox (vbyte (s.vpr n) i))) := rfl

/-- A table of sixteen bytes, in a vector register. -/
def TabOk (v : BitVec 128) (t : Vector Byte 16) : Prop := ∀ j < 16, vbyte v j = t.getD j 0

/-- A table lookup by `vperm` of a byte below 16. -/
theorem vperm_byte {T c : BitVec 128} {t : Vector Byte 16} (hT : TabOk T t) {i : Nat} (hi : i < 16)
    (hc : (vbyte c i).toNat < 16) :
    vbyte (ofVBytes fun i =>
      let j := (vbyte c i).toNat % 32
      if j < 16 then vbyte T j else vbyte T (j - 16)) i = t.getD (vbyte c i).toNat 0 := by
  rw [vbyte_packed _ hi]
  have hm : (vbyte c i).toNat % 32 = (vbyte c i).toNat := Nat.mod_eq_of_lt (by omega)
  simp only [hm, hc, ite_true]
  exact hT _ hc


/-- A lookup by `vperm` in two tables: an index below 32 picks the first's
byte below 16, the second's above. -/
theorem vperm_byte2 {T U c : BitVec 128} {t u : Vector (BitVec 8) 16} (hT : TabOk T t) (hU : TabOk U u)
    {i : Nat} (hi : i < 16) (hc : (vbyte c i).toNat < 32) :
    vbyte (ofVBytes fun i =>
      let j := (vbyte c i).toNat % 32
      if j < 16 then vbyte T j else vbyte U (j - 16)) i =
      if (vbyte c i).toNat < 16 then t.getD (vbyte c i).toNat 0 else u.getD ((vbyte c i).toNat - 16) 0 := by
  rw [vbyte_packed _ hi]
  have hm : (vbyte c i).toNat % 32 = (vbyte c i).toNat := Nat.mod_eq_of_lt hc
  simp only [hm]
  split
  · exact hT _ (by omega)
  · exact hU _ (by omega)


theorem exec_vor {s : State} {d n m : VReg} :
    exec (.vop (.logic .or d n m)) s = some (s.writeV d (s.vpr n ||| s.vpr m)) := rfl

theorem exec_vsel {s : State} {d n m mask : VReg} :
    exec (.vop (.sel d n m mask)) s =
      some (s.writeV d ((s.vpr n &&& ~~~s.vpr mask) ||| (s.vpr m &&& s.vpr mask))) := rfl

theorem vbyte_or' (a b : BitVec 128) (i : Nat) : vbyte (a ||| b) i = vbyte a i ||| vbyte b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, hj, decide_true, Bool.true_and]

/-- `vsel`'s byte, of a mask whose byte is all zeros or all ones. -/
theorem vbyte_sel (a b c : BitVec 128) {i : Nat} (hi : i < 16) (hc : vbyte c i = 0 ∨ vbyte c i = 0xff) :
    vbyte ((a &&& ~~~c) ||| (b &&& c)) i = if vbyte c i = 0xff then vbyte b i else vbyte a i := by
  have e : vbyte ((a &&& ~~~c) ||| (b &&& c)) i = (vbyte a i &&& ~~~vbyte c i) ||| (vbyte b i &&& vbyte c i) := by
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_not, hj, decide_true, Bool.true_and, show 8 * (15 - i) + j < 128 by omega]
  rw [e]
  have h1 : ∀ x : BitVec 8, x &&& 255#8 = x := fun x => BitVec.and_allOnes
  have h0 : ∀ x : BitVec 8, x &&& 0#8 = 0#8 := fun x => BitVec.and_zero
  rcases hc with h | h <;> rw [h] <;> simp [h1, h0]

/-- A nibble with bit 4 set. -/
theorem toNat_or_16 {y : BitVec 8} (hy : y.toNat < 16) : (y ||| 0x10).toNat = y.toNat + 16 := by
  rw [BitVec.toNat_or]
  have : ∀ n < 16, n ||| 16 = n + 16 := by decide
  exact this _ hy

theorem vpr_writeV_self (s : State) (d : VReg) (x : BitVec 128) : (s.writeV d x).vpr d = x := by
  simp [State.writeV]

theorem vpr_writeV_of_ne (s : State) {d r : VReg} (x : BitVec 128) (h : r ≠ d) : (s.writeV d x).vpr r = s.vpr r := by
  simp [State.writeV, h]

end VG.PPC64LE.Bytes
