import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyLay21
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyButterfly
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Ntt

/-! Each layer increases the nonnegative coefficient bound by 2q, while
preserving the residues of the specification's canonical NTT. -/
namespace VG.Proof.MlDsa.X86_64.Arith.Lazy
open VG.Spec.MlDsa (q Zq n)
open VG.Proof.MlDsa.Arith hiding bfly blockN layF
open VG.Proof.MlDsa.Arith.Lazy

def layer (F : Poly) (len : Nat) : Poly :=
  layF (fun f len k st t => blockN (bfly op) f len (VG.Spec.MlDsa.zetas k) st t)
    F len (fun c => 128 / len + c) (128 / len)

def Rel (b : Nat) (F : Poly) (f : VG.Spec.MlDsa.Poly) : Prop :=
  ∀ i < 256, F[i]!.val < b * q ∧ residue F[i]! = f[i]!

def lift (f : VG.Spec.MlDsa.Poly) : Poly := f.map fun x => ⟨x.val, Nat.lt_trans x.isLt (by decide)⟩

theorem lift_rel (f : VG.Spec.MlDsa.Poly) : Rel 1 (lift f) f := by
  intro i hi
  have he : (lift f)[i]! = ⟨f[i]!.val, Nat.lt_trans f[i]!.isLt (by decide)⟩ := by
    rw [getElem!_pos (lift f) i hi, lift, Vector.getElem_map, getElem!_pos f i hi]
  rw [he]
  exact ⟨by simpa only [Nat.one_mul] using f[i]!.isLt, Fin.ext (Nat.mod_eq_of_lt f[i]!.isLt)⟩

theorem layer_rel {b : Nat} (hb : b ≤ 15) {F : Poly} {f : VG.Spec.MlDsa.Poly} (hF : Rel b F f)
    {len : Nat} (hlen : len ∈ [1, 2, 4, 8, 16, 32, 64, 128]) :
    Rel (b + 2) (layer F len) (nttLayer f len) := by
  have hl : 0 < len ∧ 2 * len * (128 / len) = 256 ∧
      ∀ i < 256, (i % (2 * len) < len → i + len < 256) ∧ (¬ i % (2 * len) < len → len ≤ i) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
    rcases hlen with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> refine ⟨by decide, by decide, ?_⟩
    all_goals intro i hi; omega
  intro i hi
  rw [layer, layF_get (block_ok op) F hl.1 _ (by omega) hi,
    nttLayer_eq, Arith.layF_get nttBlk_ok f hl.1 _ (by omega) hi]
  simp only [ite_eq_left (show i < 2 * len * (128 / len) by omega)]
  by_cases h : i % (2 * len) < len
  · simp only [ite_eq_left h]
    have h0 := hF i hi
    have h1 := hF (i + len) ((hl.2.2 i hi).1 h)
    exact ⟨(op_bound _ _ _ hb h0.1).1, by
      rw [(op_residue _ _ _ (Nat.lt_of_lt_of_le h0.1 (Nat.mul_le_mul_right q hb))).1, h0.2, h1.2]⟩
  · simp only [ite_eq_right h]
    have h0 := hF (i - len) (by omega)
    have h1 := hF i hi
    exact ⟨(op_bound _ _ _ hb h0.1).2, by
      rw [(op_residue _ _ _ (Nat.lt_of_lt_of_le h0.1 (Nat.mul_le_mul_right q hb))).2, h0.2, h1.2]⟩

end VG.Proof.MlDsa.X86_64.Arith.Lazy
