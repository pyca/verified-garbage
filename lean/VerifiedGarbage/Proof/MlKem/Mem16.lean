module

public import VerifiedGarbage.Proof.MlKem.Kpke16Contract
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# ML-KEM: polynomials stored with `w`-bit coefficients

The coefficients of `polyAtW` (`polyAtW_get`), and a stored polynomial from
its coefficients (`polyIsW_of_toNat`), as `Mem.lean` has them for `[u32; 256]`.

Code that stores either width, 16-bit coefficients if `h` (`cw h`), stores
coefficient `i` at `cAddr h p i`, within `cRegion h p`; `coeffAtW_writeW`
reads a coefficient after a write of one.
-/

@[expose] public section

namespace VG.Proof.MlKem

open VG.Spec.MlKem

theorem polyAtW_get (w : Nat) (m : Mem) (p : Addr) {i : Nat} (hi : i < n) :
    (polyAtW w m p)[i]! = ofNat (coeffAtW w m p i).toNat := by
  rw [getElem!_eq _ hi]
  simp only [polyAtW, Vector.getElem_ofFn]

/-- `f` is stored at `p` with `w`-bit coefficients if each of its
coefficients is. -/
theorem polyIsW_of_toNat {w : Nat} {m : Mem} {p : Addr} {f : Poly}
    (h : ∀ i < n, (coeffAtW w m p i).toNat = (f[i]!).val) : PolyIsW w m p f := by
  refine ⟨fun i hi => by rw [h i hi]; exact (f[i]!).isLt, ext_getElem! fun i hi => ?_⟩
  rw [polyAtW_get _ _ _ hi, h i hi, ofNat_val]

/-! ## Coefficients of either width -/

/-- The width of a coefficient: 16 bits if `h`, else 32. -/
abbrev cw (h : Bool) : Nat := if h then 16 else 32

/-- The address of coefficient `i` at `p`. -/
abbrev cAddr (h : Bool) (p : Addr) (i : Nat) : Addr := p + BitVec.ofNat 64 (cw h / 8 * i)

/-- The 256 coefficients at `p`. -/
abbrev cRegion (h : Bool) (p : Addr) : Region := ⟨p, 256 * (cw h / 8)⟩

theorem cw_bytes (h : Bool) : cw h / 8 = if h then 2 else 4 := by cases h <;> rfl

theorem cw_bytes_le (h : Bool) : cw h / 8 ≤ 4 := by cases h <;> decide

theorem coeffAtW_eq (h : Bool) (m : Mem) (p : Addr) (i : Nat) :
    coeffAtW (cw h) m p i = m.readW (cAddr h p i) (cw h) := rfl

theorem cAddr_contains (h : Bool) (p : Addr) {i : Nat} (hi : i < 256) :
    (cRegion h p).Contains (cAddr h p i) (cw h / 8) :=
  Offset.contains_base p (by cases h <;> simp only [cw, Bool.false_eq_true, ↓reduceIte] <;> omega)
    (by cases h <;> simp only [cw, Bool.false_eq_true, ↓reduceIte] <;> omega)

theorem cAddr_sep (h : Bool) (p : Addr) {i j : Nat} (hi : i < 256) (hj : j < 256) (hij : i ≠ j) :
    Mem.Sep (cAddr h p i) (cw h / 8) (cAddr h p j) (cw h / 8) := by
  cases h <;> exact Offset.sep p (by simp only [cw, Bool.false_eq_true, ↓reduceIte]; omega)
    (by simp only [cw, Bool.false_eq_true, ↓reduceIte]; omega) (by simp only [cw, Bool.false_eq_true, ↓reduceIte]; omega)

theorem readW_writeW_cw (h : Bool) (m : Mem) (a : Addr) (v : BitVec (cw h)) : (m.writeW a v).readW a (cw h) = v := by
  cases h
  · exact Mem.readW_writeW_self m a 4 v (by decide)
  · exact Mem.readW_writeW_self m a 2 v (by decide)

/-- Writing coefficient `j` of the polynomial at `p`. -/
theorem coeffAtW_writeW (h : Bool) (m : Mem) (p : Addr) {i j : Nat} (hi : i < 256) (hj : j < 256)
    (v : BitVec (cw h)) :
    coeffAtW (cw h) (m.writeW (cAddr h p j) v) p i = if j = i then v else coeffAtW (cw h) m p i := by
  rw [coeffAtW_eq, coeffAtW_eq]
  split
  · subst j; exact readW_writeW_cw h m _ v
  · exact Mem.readW_writeW_sep (cAddr_sep h p hi hj (Ne.symm ‹_›)) (by have := cw_bytes_le h; omega)

/-- A polynomial stored apart from the regions of a frame. -/
theorem polyIsW_frame (h : Bool) {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {f : Poly}
    (hd : ∀ r ∈ rs, (cRegion h p).Disjoint r) (hp : PolyIsW (cw h) m p f) : PolyIsW (cw h) m' p f := by
  have e : ∀ i < n, coeffAtW (cw h) m' p i = coeffAtW (cw h) m p i := fun i hi => by
    rw [coeffAtW_eq, coeffAtW_eq]
    exact hf.readW (cAddr_contains h p (by rw [n_eq] at hi; exact hi)) hd (by have := cw_bytes_le h; omega)
  refine ⟨fun i hi => by rw [e i hi]; exact hp.1 i hi, ?_⟩
  rw [← hp.2]
  simp only [polyAtW]
  congr 1
  funext i
  rw [e i.val i.isLt]

end VG.Proof.MlKem
