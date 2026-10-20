module

public import VerifiedGarbage.Impl.Rc2.Table
public import VerifiedGarbage.Proof.Rc2.PiLit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# RC2: PITABLE's bytes in the table of constants

Memory holding the quadwords of `VG_RC2_PITABLE` (`Impl/Rc2/Table.lean`) at
`T` (`PiHeld`, as `Abi.constsHeld` states it) holds PITABLE's byte `i` at
`T + i` (`PiHeld.byte`).
-/

@[expose] public section

namespace VG.Proof.Rc2

open VG VG.Impl.Rc2

theorem piQuads_length : piQuads.length = 32 := by
  simp only [piQuads, List.length_map, List.length_range]

theorem piQuads_getD {q : Nat} (hq : q < 32) : piQuads.getD q 0 = piQuad q := by
  simp only [piQuads, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hq,
    Option.map_some, Option.getD_some]

/-- `piQuad`, reading PITABLE from its packed table (`Rc2.piTable_getD`). -/
def piQuadNat (q : Nat) : BitVec 64 :=
  (List.range 8).foldr (fun j acc => acc ||| (BitVec.ofNat 8 (VG.Rc2.piNat (8 * q + j))).setWidth 64 <<< (8 * j)) 0

theorem piQuad_eq : piQuad = piQuadNat := by
  funext q; simp only [piQuad, piQuadNat, VG.Rc2.piTable_getD]

theorem piQuadNat_byte : ∀ i < 256,
    (piQuadNat (i / 8)).extractLsb' (8 * (i % 8)) 8 = BitVec.ofNat 8 (VG.Rc2.piNat i) := by
  lit_decide

/-- Byte `i % 8` of quadword `i / 8` is PITABLE's byte `i`. -/
theorem piQuad_byte {i : Nat} (hi : i < 256) :
    (piQuad (i / 8)).extractLsb' (8 * (i % 8)) 8 = Spec.Rc2.piTable.getD i 0 := by
  rw [piQuad_eq, VG.Rc2.piTable_getD]
  exact piQuadNat_byte i hi

/-- Memory holding the table at `T`. -/
def PiHeld (m : Mem) (T : Addr) : Prop :=
  ∀ i < piQuads.length, m.readW (T + BitVec.ofNat 64 (8 * i)) 64 = piQuads.getD i 0

/-- PITABLE's byte `i`, at `T + i`. -/
theorem PiHeld.byte {m : Mem} {T : Addr} (h : PiHeld m T) {i : Nat} (hi : i < 256) :
    m (T + BitVec.ofNat 64 i) = Spec.Rc2.piTable.getD i 0 := by
  have hq : i / 8 < 32 := by omega
  have hw := h (i / 8) (by rw [piQuads_length]; exact hq)
  rw [piQuads_getD hq] at hw
  have e : T + BitVec.ofNat 64 i = (T + BitVec.ofNat 64 (8 * (i / 8))) + BitVec.ofNat 64 (i % 8) := by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.div_add_mod]
  rw [e, ← Mem.extractLsb'_read m _ (n := 8) (by omega), ← piQuad_byte hi, ← hw]
  rfl

end VG.Proof.Rc2
