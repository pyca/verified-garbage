module

public import VerifiedGarbage.Proof.MlKem.Kpke16Contract
import VerifiedGarbage.Proof.MlKem.Arith

/-!
# ML-KEM: polynomials stored with 16-bit coefficients, byte by byte

A 16-bit coefficient from its two bytes (`coeffAtW16_toNat`), the
coefficients of a stored polynomial (`polyIsW16_toNat`), the bytes of
coefficients `F` stored with 16 bits (`bytesW16`), and the polynomial they
store (`polyIsW16_of_bytes`), on every target.
-/

@[expose] public section

namespace VG.Proof.MlKem

open VG VG.Spec.MlKem

/-- A 16-bit coefficient from its two bytes. -/
theorem coeffAtW16_toNat (m : Mem) (p : Addr) (i : Nat) :
    (coeffAtW 16 m p i).toNat =
      (m (p + BitVec.ofNat 64 (2 * i))).toNat + 256 * (m (p + BitVec.ofNat 64 (2 * i + 1))).toNat := by
  have e : coeffAtW 16 m p i = (m (p + BitVec.ofNat 64 (2 * i) + 1) ++ m (p + BitVec.ofNat 64 (2 * i)) : BitVec 16) := by
    rw [coeffAtW, Mem.readW, show 16 / 8 * i = 2 * i by omega]
    apply BitVec.eq_of_toNat_eq
    simp only [Mem.read, BitVec.toNat_setWidth, BitVec.toNat_append]
    rw [show (0#0).toNat = 0 from rfl, Nat.zero_shiftLeft, Nat.zero_or]
    exact Nat.mod_eq_of_lt (by
      rw [← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt _), Nat.shiftLeft_eq]
      have := (m (p + BitVec.ofNat 64 (2 * i) + 1)).isLt
      have := (m (p + BitVec.ofNat 64 (2 * i))).isLt
      omega)
  rw [e, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt _), Nat.shiftLeft_eq,
    show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add]
  omega

/-- The coefficients of a polynomial stored with 16 bits. -/
theorem polyIsW16_toNat {m : Mem} {p : Addr} {f : Poly} (h : PolyIsW 16 m p f) {i : Nat} (hi : i < 256) :
    (coeffAtW 16 m p i).toNat = (f[i]!).val := by
  have hr := h.1 i hi
  rw [← h.2, getElem!_eq _ hi]
  simp only [polyAtW, Vector.getElem_ofFn]
  exact (Nat.mod_eq_of_lt hr).symm

/-- Byte `j` of the coefficients `F` stored with 16 bits: byte `j % 2` of coefficient `j / 2`. -/
def bytesW16 (F : Nat → Nat) (j : Nat) : Byte := BitVec.ofNat 8 (F (j / 2) / 256 ^ (j % 2))

/-- All 512 bytes of a polynomial stored with 16 bits. -/
theorem polyIsW16_of_bytes {m : Mem} {p : Addr} {f : Poly}
    (h : ∀ j < 512, m (p + BitVec.ofNat 64 j) = bytesW16 (fun i => (f[i]!).val) j) : PolyIsW 16 m p f := by
  have hc : ∀ i < n, (coeffAtW 16 m p i).toNat = (f[i]!).val := fun i hi => by
    have hi' : i < 256 := hi
    have hq : (f[i]!).val < 3329 := Fin.isLt _
    rw [coeffAtW16_toNat, h _ (by omega), h _ (by omega),
      bytesW16, bytesW16, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (2 * i) / 2 = i by omega,
      show (2 * i + 1) / 2 = i by omega, show 2 * i % 2 = 0 by omega, show (2 * i + 1) % 2 = 1 by omega,
      Nat.pow_zero, Nat.pow_one, Nat.div_one]
    omega
  refine ⟨fun i hi => by rw [hc i hi]; exact Fin.isLt _, ext_getElem! fun i hi => ?_⟩
  rw [getElem!_eq _ hi]
  simp only [polyAtW, Vector.getElem_ofFn]
  rw [hc i hi, ofNat_val]

end VG.Proof.MlKem
