module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout
public import VerifiedGarbage.Impl.EcKey.Compressed.PPC64LE.Decompress
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontCall
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.SlotOps
import VerifiedGarbage.Proof.EcKey.Compressed.Parity
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Copy
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Keep
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# SEC 1 point decompression on PPC64LE: the root of the tag's parity

`parityMask_ok`: the mask `r10` of `QY`'s parity differing from the tag's;
`selectRoot_ok`: the candidate out of Montgomery form, and it or `p` minus
it by that mask, to `QY`.
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Spec.Weierstrass VG.Proof.EcKey.Compressed
open VG.Impl.Ecdh.PPC64LE (QY W0)

variable {c : Cfg}

/-- The mask `r10` of `QY`'s parity differing from the tag's (`D`'s first
word). -/
theorem parityMask_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Ws s base size)
    (h3 : At s base .r3 0) (hn0 : 0 < c.n) (hQ : c.sl QY + 8 ≤ size) (hD : c.sl D + 8 ≤ size) :
    WP isa (.block (Impl.EcKey.Compressed.PPC64LE.parityMask c)) s fun s' =>
      s'.gpr .r10 = mask64 ((word s.mem base (c.sl D)).toNat % 2 ≠ sv c base s QY % 2) ∧
      Kp [.r4, .r5, .r10] s s' ∧ s'.mem = s.mem := by
  simp only [Impl.EcKey.Compressed.PPC64LE.parityMask]
  refine wp_step (ld0_ok hs h3 (by decide) (sl_al c QY) hQ) ?_
  refine wp_step (ld0_ok (hs.write _ _) (h3.write _) (by decide) (sl_al c D) hD) ?_
  refine wp_step exec_logic ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_logic ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_sub (WP.block_nil ⟨?_, ?_, ?_⟩)
  · simp only [write_gpr, ite_true, reduceCtorEq, ite_false, write_mem]
    rw [show BitVec.ofNat 64 1 = 1 from rfl, show BitVec.ofNat 64 0 = 0 from rfl, xor_low_mask,
      slot_parity s.mem base (c.sl QY) c.n hn0]
  · exact (((((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans
      (Kp.write _ _ (by decide))).trans ((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide)))).trans
      (Kp.write _ _ (by decide))
  · simp only [write_mem]

/-- What `selectRoot` writes. -/
abbrev selectW (c : Cfg) : List (Nat × Nat) := slW c [QY, W0] ++ [(own c.n, 64 * c.n)]

/-- The candidate in `ACC`, out of Montgomery form, or `p` minus it, by the
tag's parity, to `QY`. -/
theorem selectRoot_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base)
    (hOne : sv c base s ONE = 1) (hZero : sv c base s ZERO = 0) :
    WP isa (Impl.EcKey.Compressed.PPC64LE.selectRoot c) s fun s' =>
      WsReg s' base ∧ Rk fnClob s s' ∧ Unch base (selectW c) s.mem s'.mem ∧ sv c base s' QY < c.C.p ∧
      Fin.ofNat c.C.p (sv c base s' QY) =
        (let y := toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)
         if y.val % 2 = (word s.mem base (c.sl D)).toNat % 2 then y else -y) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hw.nowrap
  have hp3 := hc.p_ge
  have hsz : size = 8192 := rfl
  have hY := sl_le c h7 (i := QY) (by decide)
  have hW := sl_le c h7 (i := W0) (by decide)
  have hD := sl_le c h7 (i := D) (by decide)
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  change WP isa (.seq (mulCall c.SP (c.sl QY) (c.sl ACC) (c.sl ONE))
    (.seq (subCall c.SP (c.sl W0) (c.sl ZERO) (c.sl QY))
      (.block (Impl.EcKey.Compressed.PPC64LE.parityMask c ++ sel c.n (c.sl QY) (c.sl QY) (c.sl W0))))) s _
  -- `QY = ACC · 1`, out of Montgomery form.
  refine WP.seq (WP.mono (slMul_ok hc.fp hc.fpk hc.fpm h7 hw (o := QY) (a := ACC) (b := ONE)
    (by decide) (by decide) (by decide) (by rw [hOne]; omega)) fun s₁ ⟨k₁, U₁, lt₁, e₁⟩ => ?_)
  have hw₁ := hw.of_rk k₁
  have v₁ : ∀ {i}, i < 45 → i ≠ QY → sv c base s₁ i = sv c base s i := fun hi h₁ =>
    sv_unch U₁ h7 hn hi (apart_callW h7 hi h₁)
  have normal : Fin.ofNat c.C.p (sv c base s₁ QY) = toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) :=
    toM_one_mul hpR (by rw [e₁, hOne])
  have normalVal : sv c base s₁ QY = (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)).val := by
    simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt lt₁] using congrArg Fin.val normal
  -- `W0 = 0 - QY`.
  refine WP.seq (WP.mono (slSub_ok hc.fp hc.fpk hc.fpm h7 hw₁ (o := W0) (a := ZERO) (b := QY)
    (by decide) (by decide) (by decide) (by rw [v₁ (by decide) (by decide), hZero]; omega) lt₁)
    fun s₂ ⟨k₂, U₂, e₂⟩ => ?_)
  have hw₂ := hw₁.of_rk k₂
  have v₂ : ∀ {i}, i < 45 → i ≠ W0 → sv c base s₂ i = sv c base s₁ i := fun hi h₁ =>
    sv_unch U₂ h7 hn hi (apart_callW h7 hi h₁)
  have y₂ : sv c base s₂ QY = sv c base s₁ QY := v₂ (by decide) (by decide)
  have zero₁ : sv c base s₁ ZERO = 0 := (v₁ (by decide) (by decide)).trans hZero
  have negLt : sv c base s₂ W0 < c.C.p := by rw [e₂]; exact Nat.mod_lt _ (by omega)
  have negVal : Fin.ofNat c.C.p (sv c base s₂ W0) = -(Fin.ofNat c.C.p (sv c base s₁ QY)) := by
    apply Fin.ext
    simp only [Fin.val_ofNat, Fin.neg_def]
    rw [e₂, zero₁, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt lt₁]
  have hDw : ∀ w ∈ callW c QY ++ callW c W0, c.sl D + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl D := fun w hw' =>
    (apart_append (apart_callW h7 (i := D) (o := QY) (by decide) (by decide))
      (apart_callW h7 (i := D) (o := W0) (by decide) (by decide)) w hw').imp (fun h => by omega) id
  have tag₂ : word s₂.mem base (c.sl D) = word s.mem base (c.sl D) := (U₁.trans U₂).word hDw (by omega)
  -- The parity's mask, and the selection.
  rw [WP.block_append_iff]
  refine WP.mono (parityMask_ok c hw₂.ws hw₂.at3 h0 (by omega) (by omega)) fun s₃ ⟨mask₃, k₃, m₃⟩ => ?_
  refine WP.mono (sel_ok (decide ((word s₂.mem base (c.sl D)).toNat % 2 ≠ sv c base s₂ QY % 2)) c.n
    (k₃.ws hw₂.ws) (k₃.at hw₂.at3) (by rw [mask₃]; simp only [mask64, decide_eq_true_eq])
    (sl_al c _) (sl_al c _) (sl_al c _) (by omega) (by omega) (by omega) (Or.inl (Nat.le_refl _))
    (by have := sl_apart c (i := QY) (j := W0) (by decide); omega)) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  rw [m₃] at e₄
  have K : Rk fnClob s s₄ := (k₁.trans k₂).trans ((k₃.rk (rs' := fnClob)).trans (k₄.rk (rs' := fnClob)))
  refine ⟨hw.of_rk K, K, ?_, ?_, ?_⟩
  · have U := (U₁.trans U₂).trans (show Unch base [(c.sl QY, 8 * c.n)] s₂.mem s₄.mem by rw [← m₃]; exact O₄.unch)
    refine U.mono fun w hw' => ?_
    simp only [callW, slW, List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hw' ⊢
    grind
  · show wordsVal s₄.mem base (c.sl QY) c.n < c.C.p
    rw [e₄]
    split
    · exact negLt
    · rw [show wordsVal s₂.mem base (c.sl QY) c.n = sv c base s₂ QY from rfl, y₂]; exact lt₁
  · show Fin.ofNat c.C.p (wordsVal s₄.mem base (c.sl QY) c.n) = _
    rw [e₄, tag₂, show wordsVal s₂.mem base (c.sl QY) c.n = sv c base s₂ QY from rfl, y₂, normalVal]
    by_cases hm : (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)).val % 2 = (word s.mem base (c.sl D)).toNat % 2
    · simp only [hm.symm, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false, ite_true]
      exact Fin.ext (Nat.mod_eq_of_lt (toM _ _ _).isLt)
    · have hm' : ¬ (word s.mem base (c.sl D)).toNat % 2 =
          (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)).val % 2 := fun h => hm h.symm
      simp only [hm, hm', ne_eq, not_false_eq_true, decide_true, ite_true, ite_false]
      rw [show wordsVal s₂.mem base (c.sl W0) c.n = sv c base s₂ W0 from rfl, negVal, normal]

end VG.Proof.EcKey.Compressed.PPC64LE
