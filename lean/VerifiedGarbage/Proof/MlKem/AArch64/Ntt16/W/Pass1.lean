module

public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Pass1
public import VerifiedGarbage.Spec.MlKem.Kpke16
import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rc4.AArch64.Vec

/-!
# ML-KEM's 16-bit NTT on AArch64, of a polynomial stored with 16 bits: pass 1

The polynomial at `f`, stored with 16 bits, and the working space
(`Pre`, `inF`, `inS`), a polynomial a frame keeps (`polyIsW16_frame`), and
eight coefficients loaded at once (`rep_loadW`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16.W

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Ntt16
open Impl.MlKem.AArch64.Ntt16

section
variable (s₀ : State)

/-- The polynomial, 512 bytes. -/
abbrev fR : Region := ⟨fP s₀, 512⟩
/-- The working space of pass 1, 512 bytes. -/
abbrev sR : Region := ⟨sP s₀, 512⟩
/-- The polynomial to transform. -/
abbrev P₀ : Poly := polyAtW 16 s₀.mem (fP s₀)

end

/-- The precondition. -/
structure Pre (s₀ : State) : Prop where
  wr : s₀.wr = [fR s₀, sR s₀]
  disj : (fR s₀).Disjoint (sR s₀)
  red : ReducedW 16 s₀.mem (fP s₀)

theorem inF {s₀ s : State} (hp : Pre s₀) (h : St s₀ s) {o : Nat} (ho : o + 16 ≤ 512) :
    InRegions s.wr (fP s₀ + BitVec.ofNat 64 o) 16 := by
  rw [h.wr, hp.wr]
  exact in_regions (List.mem_cons_self ..) (contains_off ho (by decide))

theorem inS {s₀ s : State} (hp : Pre s₀) (h : St s₀ s) {o : Nat} (ho : o + 16 ≤ 512) :
    InRegions s.wr (sP s₀ + BitVec.ofNat 64 o) 16 := by
  rw [h.wr, hp.wr]
  exact in_regions (R := sR s₀) (by simp) (contains_off ho (by decide))

/-- A polynomial stored with 16 bits in a region a frame does not write. -/
theorem polyIsW16_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 512⟩ : Region).Disjoint r) (hr : ReducedW 16 m p) :
    PolyIsW 16 m' p (polyAtW 16 m p) := by
  have hc : ∀ i < 256, coeffAtW 16 m' p i = coeffAtW 16 m p i := fun i hi =>
    hf.readW (r := ⟨p, 512⟩) (contains_off (show 2 * i + 16 / 8 ≤ 512 by omega) (by decide)) hd (by decide)
  refine ⟨fun i hi => by rw [hc i hi]; exact hr i hi, Vector.ext fun i hi => ?_⟩
  simp only [polyAtW, Vector.getElem_ofFn]
  rw [hc i hi]

/-- Eight coefficients from `j` of a polynomial stored with 16 bits, in one vector. -/
theorem rep_loadW {m : Mem} {p : Addr} {P : Poly} (h : PolyIsW 16 m p P) {j : Nat} (hj : j + 8 ≤ 256) :
    Rep (m.read (p + BitVec.ofNat 64 (2 * j)) 16) (fun e => P[j + e]!) 3329 := fun e he => by
  have hv := vhalf_read_coeff m p j he
  rw [polyIsW16_toNat h (by omega)] at hv
  have hl : (P[j + e]!).val < 3329 := Fin.isLt _
  rw [LRep, BitVec.toInt_eq_toNat_of_lt (by omega), hv]
  exact ⟨by omega, by omega, by simp⟩

end VG.Proof.MlKem.AArch64.Ntt16.W
