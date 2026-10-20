module
public import VerifiedGarbage.Proof.MlKem.X86_64.Lazy
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Sound

import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Model
import VerifiedGarbage.Proof.MlKem.X86_64.NttInv
import VerifiedGarbage.Proof.MlKem.X86_64.NttLazy
import VerifiedGarbage.Proof.MlKem.X86_64.YNtt
import VerifiedGarbage.Proof.MlKem.X86_64.VPack

/-!
# ML-KEM on x86-64: `NTT⁻¹` on registers, the words of its layers

The polynomial's words after the first `st` layers of `invRules` (`LIW`):
the lazy Gentleman–Sande layers (`invW`, as `vibflyL` computes them) and the
reductions by Montgomery multiplication with `2¹⁶ mod q`. They obey the
layers `Sym.run` collapses (`modelI`), and their scaled and reduced values
(`OfI`) are the coefficients of `NTT⁻¹` (`OfI_nttInv`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.NttR
open VG.Spec.MlKem
open VG.Proof.MlKem.X86_64 (WPoly invW wBlockN wBlk_ok zw PolyRep Rep inv_hop layF_rep layF_get nttInvBlk_ok
  nttInvLayer_eq red_rep cadd_rep mont_rep rW getElem!_map)

/-- A layer of the words. -/
def stepI (W : WPoly) : Op → WPoly
  | .gs len => layF (wBlockN invW) W len (fun c => 256 / len - 1 - c) (128 / len)
  | .red => W.map fun w => VG.Proof.MlKem.X86_64.W.montW w rW
  | .ct _ => W

/-- The words after the first `st` layers. -/
def LIW (W : WPoly) (st : Nat) : WPoly := (invRules.ops.take st).foldl stepI W

def LfI (W : WPoly) (st p : Nat) : BitVec 16 := (LIW W st)[p]!

/-- The output word `p`: scaled by `3303` and reduced. -/
def OfI (W : WPoly) (p : Nat) : BitVec 16 := caddQ (mtW (LfI W 9 p) 512 (512 * qinvN % 65536))

theorem LIW_succ (W : WPoly) {st : Nat} {o : Op} (h : invRules.ops[st]? = some o) :
    LIW W (st + 1) = stepI (LIW W st) o := by
  unfold LIW
  rw [List.take_add_one, List.foldl_append, h]
  rfl

theorem inv_ops_none {st : Nat} (h : 9 ≤ st) : invRules.ops[st]? = none :=
  List.getElem?_eq_none (by simp only [invRules, List.length_cons, List.length_nil]; omega)

/-- `vmont` with the precomputed `z q⁻¹` is `montW`, for any constant `z < q`. -/
theorem mtW_eqN (b : BitVec 16) {z : Nat} (hz : z < 3329) :
    VG.Proof.MlKem.X86_64.W.montW b (BitVec.ofNat 16 z) = mtW b z (z * qinvN % 65536) := by
  have hq : VG.Proof.MlKem.X86_64.W.qW = BitVec.ofNat 16 qN := rfl
  have hm : BitVec.ofNat 16 z * VG.Proof.MlKem.X86_64.W.qinvW = BitVec.ofNat 16 (z * qinvN % 65536) := by
    apply BitVec.eq_of_toNat_eq
    have hq' : VG.Proof.MlKem.X86_64.W.qinvW.toNat = 62209 := by decide
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hq', Nat.mod_eq_of_lt (show z < 2 ^ 16 by omega)]
    simp only [qinvN]
    omega
  rw [VG.Proof.MlKem.X86_64.W.montW, mtW, hq, lo_mul, lo_mul, lo_mul, BitVec.mul_assoc, hm]

theorem zw_zeta (k : Nat) : zw (zeta k) = BitVec.ofNat 16 (zmTab k) := by rw [zw, zmTab_eq]

theorem zmTab_lt (k : Nat) : zmTab k < 3329 := by rw [zmTab_eq]; exact Nat.mod_lt _ (by decide)

theorem invLen_pos {st len : Nat} (h : invRules.ops[st]? = some (.gs len)) :
    0 < len ∧ 2 * len * (128 / len) = 256 ∧ len ∈ [2, 4, 8, 16, 32, 64, 128] := by
  rcases Nat.lt_or_ge st 9 with hs | hs
  · rcases (by omega : st = 0 ∨ st = 1 ∨ st = 2 ∨ st = 3 ∨ st = 4 ∨ st = 5 ∨ st = 6 ∨ st = 7 ∨ st = 8) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [invRules] at h <;> cases h <;> decide
  · rw [inv_ops_none hs] at h; cases h

theorem modelI (W : WPoly) (hW : ∀ p < 256, (W[p]!).toNat < 32768) : Model invRules (LfI W) (OfI W) := by
  refine ⟨fun p hp => hW p hp, fun st p p' z z' hb => ?_, fun st p p' h => ?_, fun st p p' z z' h => ?_,
    fun st p h hp => ?_, fun _ _ => rfl⟩
  · exfalso
    rcases Nat.lt_or_ge st 9 with hs | hs
    · rcases (by omega : st = 0 ∨ st = 1 ∨ st = 2 ∨ st = 3 ∨ st = 4 ∨ st = 5 ∨ st = 6 ∨ st = 7 ∨ st = 8) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [bflyOk, invRules] at hb
    · simp [bflyOk, inv_ops_none hs] at hb
  · unfold gsPairOk at h
    split at h
    · rename_i len hop
      obtain ⟨hl, hb, _⟩ := invLen_pos hop
      simp only [pairOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨⟨rfl, hm⟩, hp'⟩ := h
      simp only [LfI]
      rw [LIW_succ W hop, stepI, layF_get (wBlk_ok invW) _ hl _ (by rw [hb]) (by omega),
        ite_eq_left_of_eq_true _ _ (eq_true (show p < _ by rw [hb]; omega)), ite_eq_left_of_eq_true _ _ (eq_true hm)]
      rfl
    · cases h
  · unfold gsOk at h
    split at h
    · rename_i len hop
      obtain ⟨hl, hb, _⟩ := invLen_pos hop
      simp only [pairOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨rfl, hm⟩, hp'⟩, rfl⟩, rfl⟩ := h
      have hd : (p + len) / (2 * len) = p / (2 * len) ∧ (p + len) % (2 * len) = p % (2 * len) + len ∧
          p + len - len = p := by
        have hm' := (invLen_pos hop).2.2
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm'
        rcases hm' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      simp only [LfI]
      rw [LIW_succ W hop, stepI, layF_get (wBlk_ok invW) _ hl _ (by rw [hb]) hp',
        ite_eq_left_of_eq_true _ _ (eq_true (show p + len < _ by rw [hb]; omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ (p + len) % (2 * len) < len by omega)), hd.2.2, hd.1]
      simp only [invW, zw_zeta]
      exact mtW_eqN _ (zmTab_lt _)
    · cases h
  · unfold redOk at h
    have hop : invRules.ops[st]? = some .red := by simpa using h
    simp only [LfI]
    rw [LIW_succ W hop, stepI, getElem!_map _ _ hp, ← mtW_eqN _ (zmTab_lt 0), ← zw_zeta]
    have hz : zw (zeta 0) = rW := by rw [zw, ← zmTab_eq]; decide
    rw [hz]

/-- The spec's polynomial after the first `st` layers (the reductions keep it). -/
def stepS (F : Poly) : Op → Poly
  | .gs len => nttInvLayer F len
  | .red => F
  | .ct _ => F

def GI (F : Poly) (st : Nat) : Poly := (invRules.ops.take st).foldl stepS F

theorem GI_succ (F : Poly) {st : Nat} {o : Op} (h : invRules.ops[st]? = some o) :
    GI F (st + 1) = stepS (GI F st) o := by
  unfold GI
  rw [List.take_add_one, List.foldl_append, h]
  rfl

theorem rep_gs {k : Nat} (hk : 2 * k * 3329 ≤ 32768) (hk1 : 1 ≤ 2 * k) {st len : Nat}
    (hop : invRules.ops[st]? = some (.gs len)) {W : WPoly} {F : Poly}
    (h : PolyRep k (LIW W st) (GI F st)) : PolyRep (2 * k) (LIW W (st + 1)) (GI F (st + 1)) := by
  rw [LIW_succ W hop, GI_succ F hop, stepI, stepS, nttInvLayer_eq]
  exact layF_rep (wBlk_ok invW) nttInvBlk_ok (inv_hop hk hk1) (invLen_pos hop).2.2 _ h

theorem rep_red {k st : Nat} (hop : invRules.ops[st]? = some .red) {W : WPoly} {F : Poly}
    (h : PolyRep k (LIW W st) (GI F st)) : PolyRep 1 (LIW W (st + 1)) (GI F (st + 1)) := by
  rw [LIW_succ W hop, GI_succ F hop, stepI, stepS]
  intro i hi
  rw [getElem!_map _ _ hi]
  exact red_rep (h i hi).2.2

/-- The words after the nine layers represent `NTT⁻¹`'s before the scaling, within `4 q`. -/
theorem LIW_rep (W : WPoly) (F : Poly) (h : PolyRep 1 W F) : PolyRep 4 (LIW W 9) (GI F 9) := by
  have h1 := rep_gs (k := 1) (by decide) (by decide) (st := 0) rfl h
  have h2 := rep_gs (k := 2) (by decide) (by decide) (st := 1) rfl h1
  have h3 := rep_gs (k := 4) (by decide) (by decide) (st := 2) rfl h2
  have h4 := rep_red (st := 3) rfl h3
  have h5 := rep_gs (k := 1) (by decide) (by decide) (st := 4) rfl h4
  have h6 := rep_gs (k := 2) (by decide) (by decide) (st := 5) rfl h5
  have h7 := rep_red (st := 6) rfl h6
  have h8 := rep_gs (k := 1) (by decide) (by decide) (st := 7) rfl h7
  exact rep_gs (k := 2) (by decide) (by decide) (st := 8) rfl h8

theorem GI_nine (F : Poly) : GI F 9 = nttInvLens.foldl nttInvLayer F := by
  simp only [GI, invRules, List.take_succ_cons, List.take_zero, List.foldl_cons, List.foldl_nil, stepS,
    nttInvLens]

/-- The output words are the coefficients of `NTT⁻¹`. -/
theorem OfI_nttInv (W : WPoly) (F : Poly) (h : PolyRep 1 W F) {p : Nat} (hp : p < 256) :
    (OfI W p).toNat = ((nttInv F)[p]!).val := by
  have h9 := LIW_rep W F h p hp
  have hz : zw (3303 : Zq) = BitVec.ofNat 16 512 := by decide
  have e : OfI W p = VG.Proof.MlKem.X86_64.W.caddW
      (VG.Proof.MlKem.X86_64.W.montW (LfI W 9 p) (zw (3303 : Zq))) := by
    rw [OfI, hz, mtW_eqN _ (by decide)]; rfl
  rw [e, nttInv_eq_layers, getElem!_map _ _ hp, ← GI_nine, Fin.mul_comm]
  exact cadd_rep (mont_rep 3303 h9.2.2)

end VG.Proof.MlKem.X86_64.NttR
