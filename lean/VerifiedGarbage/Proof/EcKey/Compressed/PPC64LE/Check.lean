module

public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.Poly
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontCall
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.Select
import VerifiedGarbage.Proof.Ecdh.PPC64LE.Peer
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Flags
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Keep
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# SEC 1 point decompression on PPC64LE: the checks of the root

`checkRoot_ok`: `checkRoot` computes `y² - rhs` (`checkPoly_ok`) and ands
into the flag the masks of it being zero and of `y`'s parity being the
tag's.
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Spec.Weierstrass VG.Proof.Ecdh.PPC64LE
open VG.Impl.Ecdh.PPC64LE (QY QYM R2P W1 W2 W3)

variable {c : Cfg}

theorem invert_mask (P : Prop) [Decidable P] :
    BitVec.ofNat 64 0 - (mask64 P + BitVec.ofNat 64 1) = mask64 ¬P := by
  by_cases h : P <;> simp only [mask64, h, not_true, not_false_eq_true, ite_true, ite_false] <;> decide

/-- The mask `r5` of `r10`'s mask being clear. -/
theorem invertMask_ok {s : State} {P : Prop} [Decidable P] (h : s.gpr .r10 = mask64 P) :
    WP isa (.block Impl.EcKey.Compressed.PPC64LE.invertMask) s fun s' =>
      s'.gpr .r5 = mask64 ¬P ∧ Kp [.r4, .r5] s s' ∧ s'.mem = s.mem := by
  simp only [Impl.EcKey.Compressed.PPC64LE.invertMask]
  refine wp_step (exec_addi (by decide) (by decide)) ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_sub (WP.block_nil ⟨?_, ?_, ?_⟩)
  · simp only [write_gpr, ite_true, reduceCtorEq, ite_false, h]; exact invert_mask P
  · exact ((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))
  · simp only [write_mem]

/-- What `checkRoot` writes. -/
abbrev checkRootW (c : Cfg) : List (Nat × Nat) := checkW c ++ [(c.sl FLAG, 8)]

/-- The checks of `QY`: `y² = rhs` and `y`'s parity the tag's, anded into
the flag. -/
theorem checkRoot_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base)
    (hy : sv c base s QY < c.C.p) (hr : sv c base s W2 < c.C.p) (hr2 : sv c base s R2P = c.R * c.R % c.C.p)
    {P : Prop} [Decidable P] (hf : flagW c base s = mask64 P) :
    WP isa (Impl.EcKey.Compressed.PPC64LE.checkRoot c) s fun s' =>
      WsReg s' base ∧ Rk fnClob s s' ∧ Unch base (checkRootW c) s.mem s'.mem ∧
      flagW c base s' = mask64
        ((P ∧ Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) =
          toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2)) ∧
          sv c base s QY % 2 = (word s.mem base (c.sl D)).toNat % 2) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hw.nowrap
  have hsz : size = 8192 := rfl
  have hF := sl_le c h7 (i := FLAG) (by decide)
  have hW := sl_le c h7 (i := W3) (by decide)
  have hY := sl_le c h7 (i := QY) (by decide)
  have hD := sl_le c h7 (i := D) (by decide)
  change WP isa (.seq (fprog c.SP (Impl.EcKey.Compressed.PPC64LE.checkRootOps c))
    (.block (Impl.Ecdh.PPC64LE.Cfg.checkZero c (c.sl W3) ++ (Impl.EcKey.Compressed.PPC64LE.parityMask c ++
      (Impl.EcKey.Compressed.PPC64LE.invertMask ++ c.andFlag))))) s _
  refine WP.seq (WP.mono (checkPoly_ok hc hw hy hr hr2) fun s₁ ⟨hw₁, k₁, U₁, lt₁, v₁⟩ => ?_)
  have ap₁ : ∀ {i}, i < 45 → i ∉ [QYM, W1, W3] →
      ∀ w ∈ checkW c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := fun hi hl =>
    apart_append (apart_slW hl) (apart_own h7 hi)
  have flag₁ : flagW c base s₁ = mask64 P := by
    rw [flagW, U₁.word (fun w hw' => (ap₁ (i := FLAG) (by decide) (by decide) w hw').imp (fun h => by omega) id)
      (by omega), ← flagW, hf]
  have hz : sv c base s₁ W3 = 0 ↔
      Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) := by
    rw [← toM_eq_zero_iff (unitMod_pow_two hc.p_odd (64 * c.n)) lt₁, v₁]
    constructor <;> intro h <;> grind
  have y₁ : sv c base s₁ QY = sv c base s QY := sv_unch U₁ h7 hn (by decide) (ap₁ (by decide) (by decide))
  have d₁ : word s₁.mem base (c.sl D) = word s.mem base (c.sl D) :=
    U₁.word (fun w hw' => (ap₁ (i := D) (by decide) (by decide) w hw').imp (fun h => by omega) id) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (checkZero_ok c hw₁.ws hw₁.at3 (sl_al c W3) h0 (by omega) (by omega)) fun s₂ ⟨f₂, k₂, O₂⟩ => ?_
  have y₂ : sv c base s₂ QY = sv c base s QY :=
    (sv_unch O₂.unch h7 hn (by decide) (apart_flag h0 (by decide))).trans y₁
  have d₂ : word s₂.mem base (c.sl D) = word s.mem base (c.sl D) :=
    (O₂.unch.word (fun w hw' => by
      rw [List.mem_singleton.mp hw']; have := sl_lt c (i := D) (j := FLAG) (by decide); dsimp only; omega)
      (by omega)).trans d₁
  have hw₂ := hw₁.of_kp k₂
  rw [WP.block_append_iff]
  refine WP.mono (parityMask_ok c hw₂.ws hw₂.at3 h0 (by omega) (by omega)) fun s₃ ⟨mask₃, k₃, m₃⟩ => ?_
  rw [y₂, d₂] at mask₃
  rw [WP.block_append_iff]
  refine WP.mono (invertMask_ok mask₃) fun s₄ ⟨mask₄, k₄, m₄⟩ => ?_
  have hw₄ := (hw₂.of_kp k₃).of_kp k₄
  refine WP.mono (andFlag_ok c hw₄.ws hw₄.at3 (by omega)) fun s₅ ⟨flag₅, k₅, m₅⟩ => ?_
  have fl₄ : flagW c base s₄ = flagW c base s₂ := by simp only [flagW, m₄, m₃]
  refine ⟨hw₄.of_kp k₅, k₁.trans ((((k₂.rk (rs' := fnClob)).trans (k₃.rk (rs' := fnClob))).trans
    (k₄.rk (rs' := fnClob))).trans (k₅.rk (rs' := fnClob))), ?_, ?_⟩
  · have O₅ : Outside base (c.sl FLAG) 8 s₄.mem s₅.mem := by rw [m₅]; exact writeW_outside _ _ _ (by omega)
    have U₂₅ : Unch base [(c.sl FLAG, 8)] s₂.mem s₅.mem := by
      have := O₅.unch; rw [m₄, m₃] at this; exact this
    exact (U₁.trans (O₂.unch.trans U₂₅ |>.mono fun w hw' => by
      simp only [List.mem_append, List.mem_singleton, or_self] at hw'; exact List.mem_singleton.mpr hw'))
  · have key : ((P ∧ wordsVal s₁.mem base (c.sl W3) c.n = 0) ∧
        ¬((word s.mem base (c.sl D)).toNat % 2 ≠ sv c base s QY % 2)) ↔
        ((P ∧ Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) =
          toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2)) ∧
          sv c base s QY % 2 = (word s.mem base (c.sl D)).toNat % 2) := by
      rw [show wordsVal s₁.mem base (c.sl W3) c.n = sv c base s₁ W3 from rfl, hz]
      constructor
      · rintro ⟨⟨a, b⟩, h⟩; exact ⟨⟨a, b⟩, by omega⟩
      · rintro ⟨⟨a, b⟩, h⟩; exact ⟨⟨a, b⟩, by omega⟩
    rw [flag₅, fl₄, f₂, flag₁, mask₄, mask64_and, mask64_and]
    simp only [mask64, key]

end VG.Proof.EcKey.Compressed.PPC64LE
