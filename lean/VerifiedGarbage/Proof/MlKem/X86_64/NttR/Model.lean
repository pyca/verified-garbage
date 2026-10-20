module

public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Sound
public import VerifiedGarbage.Proof.MlKem.X86_64.Lazy
import VerifiedGarbage.Proof.MlKem.X86_64.NttLazy
import VerifiedGarbage.Proof.MlKem.X86_64.YNtt
import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.MlKem.X86_64.Ntt

/-!
# ML-KEM on x86-64: the NTT on registers, the words of its layers

The polynomial's words after `st` lazy layers (`LW`), as the existing AVX2
code computes them (`fwdW`, `layF`), obey the butterflies `Sym.run` collapses
(`model`), and their reduction (`Of`) is the coefficient of `NTT`
(`Of_ntt`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.NttR
open VG.Spec.MlKem
open VG.Proof.MlKem.X86_64 (WPoly fwdW wBlockN wBlk_ok zw PolyRep fwd_hop layF_rep layF_get nttBlk_ok red_rep cadd_rep rW)

/-- The distance of the butterflies of layer `st` of `NTT`. -/
def lenOf (st : Nat) : Nat := 128 >>> st

/-- The words after the first `st` layers. -/
def LW (W : WPoly) (st : Nat) : WPoly :=
  (nttLens.take st).foldl (fun W len => layF (wBlockN fwdW) W len (fun c => 128 / len + c) (128 / len)) W

def Lf (W : WPoly) (st p : Nat) : BitVec 16 := (LW W st)[p]!

/-- The reduced word `p` after the seven layers. -/
def Of (W : WPoly) (p : Nat) : BitVec 16 := caddQ (mtW (Lf W 7 p) (zmTab 0) (zmTab 0 * qinvN % 65536))

theorem lenOf_cases {st : Nat} (h : st < 7) :
    nttLens[st]? = some (lenOf st) := by
  rcases (by omega : st = 0 ∨ st = 1 ∨ st = 2 ∨ st = 3 ∨ st = 4 ∨ st = 5 ∨ st = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem fwd_ops {st : Nat} (h : st < 7) : fwdRules.ops[st]? = some (.ct (lenOf st)) := by
  rcases (by omega : st = 0 ∨ st = 1 ∨ st = 2 ∨ st = 3 ∨ st = 4 ∨ st = 5 ∨ st = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem fwd_ops_none {st : Nat} (h : 7 ≤ st) : fwdRules.ops[st]? = none :=
  List.getElem?_eq_none (by simp only [fwdRules, List.length_cons, List.length_nil]; omega)

theorem LW_succ (W : WPoly) {st : Nat} (h : st < 7) :
    LW W (st + 1) = layF (wBlockN fwdW) (LW W st) (lenOf st) (fun c => 128 / lenOf st + c) (128 / lenOf st) := by
  unfold LW
  rw [List.take_add_one, List.foldl_append, lenOf_cases h]
  rfl

theorem setWidth_signExtend16 (a : BitVec 16) : (a.signExtend 32).setWidth 16 = a := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_signExtend, BitVec.toNat_setWidth]
  have := a.isLt
  split <;> omega

theorem lo_mul (a b : BitVec 16) : (mulWordsSigned a b).extractLsb' 0 16 = a * b := by
  rw [mulWordsSigned, ← BitVec.setWidth_eq_extractLsb' (by decide), BitVec.setWidth_mul _ _ (by decide),
    setWidth_signExtend16, setWidth_signExtend16]

/-- `vmont` with the precomputed `ζ q⁻¹` is `montW`. -/
theorem mtW_eq (b : BitVec 16) (k : Nat) :
    W.montW b (zw (zeta k)) = mtW b (zmTab k) (zmTab k * qinvN % 65536) := by
  have hz : zw (zeta k) = BitVec.ofNat 16 (zmTab k) := by rw [zw, zmTab_eq]
  have hq : W.qW = BitVec.ofNat 16 qN := rfl
  have hk : zmTab k < 3329 := by rw [zmTab_eq]; exact Nat.mod_lt _ (by decide)
  have hm : BitVec.ofNat 16 (zmTab k) * W.qinvW = BitVec.ofNat 16 (zmTab k * qinvN % 65536) := by
    apply BitVec.eq_of_toNat_eq
    have hq' : W.qinvW.toNat = 62209 := by decide
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hq', Nat.mod_eq_of_lt (show zmTab k < 2 ^ 16 by omega)]
    simp only [qinvN]
    omega
  rw [W.montW, mtW, hz, hq, lo_mul, lo_mul, lo_mul, BitVec.mul_assoc, hm]

theorem model (W : WPoly) (hW : ∀ p < 256, (W[p]!).toNat < 32768) : Model fwdRules (Lf W) (Of W) := by
  refine ⟨fun p hp => hW p hp, fun st p p' z z' hb => ?_, fun st p p' h => ?_, fun st p p' z z' h => ?_,
    fun st p h => ?_, fun _ _ => rfl⟩
  rotate_left
  · rcases Nat.lt_or_ge st 7 with hs | hs
    · simp [gsPairOk, fwd_ops hs] at h
    · simp [gsPairOk, fwd_ops_none hs] at h
  · rcases Nat.lt_or_ge st 7 with hs | hs
    · simp [gsOk, fwd_ops hs] at h
    · simp [gsOk, fwd_ops_none hs] at h
  · rcases Nat.lt_or_ge st 7 with hs | hs
    · simp [redOk, fwd_ops hs] at h
    · simp [redOk, fwd_ops_none hs] at h
  have hst : st < 7 := by
    by_contra hs
    simp [bflyOk, fwd_ops_none (Nat.le_of_not_lt hs)] at hb
  rw [bflyOk, fwd_ops hst] at hb
  have hb' := hb
  simp only [pairOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb'
  obtain ⟨⟨⟨⟨rfl, hm⟩, hp'⟩, rfl⟩, rfl⟩ := hb'
  have hlen : 0 < lenOf st ∧ 2 * lenOf st * (128 / lenOf st) = 256 := by
    rcases (by omega : st = 0 ∨ st = 1 ∨ st = 2 ∨ st = 3 ∨ st = 4 ∨ st = 5 ∨ st = 6) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hd : (p + lenOf st) / (2 * lenOf st) = p / (2 * lenOf st) ∧
      (p + lenOf st) % (2 * lenOf st) = p % (2 * lenOf st) + lenOf st ∧ p + lenOf st - lenOf st = p := by
    rcases (by omega : st = 0 ∨ st = 1 ∨ st = 2 ∨ st = 3 ∨ st = 4 ∨ st = 5 ∨ st = 6) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [lenOf, Nat.reduceShiftRight] at hm ⊢ <;> omega
  simp only [Lf]
  rw [LW_succ W hst, layF_get (wBlk_ok fwdW) _ hlen.1 _ (by rw [hlen.2]) (by omega),
    layF_get (wBlk_ok fwdW) _ hlen.1 _ (by rw [hlen.2]) hp']
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show p < _ by rw [hlen.2]; omega)),
    ite_eq_left_of_eq_true _ _ (eq_true (show p + lenOf st < _ by rw [hlen.2]; omega)),
    ite_eq_left_of_eq_true _ _ (eq_true hm),
    ite_eq_right_of_eq_false _ _ (eq_false (show ¬ (p + lenOf st) % (2 * lenOf st) < lenOf st by omega)),
    hd.2.2, hd.1]
  simp only [fwdW, mtW_eq]
  exact ⟨trivial, trivial⟩

theorem lenOf_mem {st : Nat} (h : st < 7) : lenOf st ∈ [2, 4, 8, 16, 32, 64, 128] := by
  rcases (by omega : st = 0 ∨ st = 1 ∨ st = 2 ∨ st = 3 ∨ st = 4 ∨ st = 5 ∨ st = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The words after `st` layers represent the specification's, within `(st + 1) q`. -/
theorem LW_rep (W : WPoly) (F : Poly) (h : PolyRep 1 W F) :
    ∀ st, st ≤ 7 → PolyRep (st + 1) (LW W st) ((nttLens.take st).foldl nttLayer F)
  | 0, _ => h
  | st + 1, hs => by
    have ih := LW_rep W F h st (by omega)
    rw [LW_succ W (by omega), List.take_add_one, List.foldl_append, lenOf_cases (by omega)]
    simp only [Option.toList, List.foldl_cons, List.foldl_nil]
    rw [VG.Proof.MlKem.X86_64.nttLayer_eq]
    exact layF_rep (wBlk_ok fwdW) nttBlk_ok (fwd_hop (k := st + 1) (by omega)) (lenOf_mem (by omega)) _ ih

/-- The reduced words after the seven layers are the coefficients of `NTT`. -/
theorem Of_ntt (W : WPoly) (F : Poly) (h : PolyRep 1 W F) {p : Nat} (hp : p < 256) :
    (Of W p).toNat = ((ntt F)[p]!).val := by
  have h7 := LW_rep W F h 7 (by decide)
  have hz : zw (zeta 0) = rW := by rw [zw, ← zmTab_eq]; decide
  have e : Of W p = VG.Proof.MlKem.X86_64.W.caddW (VG.Proof.MlKem.X86_64.W.montW (Lf W 7 p) rW) := by
    rw [Of, ← mtW_eq _ 0, hz]; rfl
  rw [e, ntt_eq_layers]
  exact cadd_rep (red_rep (h7 p hp).2.2)

end VG.Proof.MlKem.X86_64.NttR
