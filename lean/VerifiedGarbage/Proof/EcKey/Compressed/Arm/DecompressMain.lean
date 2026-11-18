module

public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.DecompressFront
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.EcKey.Compressed.Decode
public import VerifiedGarbage.Impl.EcKey.Compressed.Arm.Decompress
import VerifiedGarbage.Proof.EcKey.Arm.Finish
public import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Frame
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Candidate
import VerifiedGarbage.Proof.Ecdsa.Arm.SlotOps
import VerifiedGarbage.Proof.Ecdsa.Arm.Middle
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Proof.Weierstrass.Arm.Copy
public import VerifiedGarbage.Proof.Ecdsa.Arm.Main
import VerifiedGarbage.Proof.Ecdsa.Arm.Fixed
import VerifiedGarbage.Proof.Ecdsa.Arm.Lays
import VerifiedGarbage.Proof.Weierstrass.Arm.Bits
import VerifiedGarbage.Proof.Ecdh.Arm.Peer
import VerifiedGarbage.Proof.Ecdsa.Arm.Scalar
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Weierstrass.Arm.Ladder
public import VerifiedGarbage.Impl.EcKey.Compressed.Root
public import VerifiedGarbage.Spec.EcKey.Compressed
import VerifiedGarbage.Proof.EcKey.Compressed.Parity
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.TCB.Code

/-! ### `EcKey.Compressed.Arm.DecompressMiddle`, which this module and modules that import it used -/

section

/-! ### `EcKey.Compressed.Arm.Parity`, which only this module used -/

section

/-! # Choose the canonical root matching the SEC 1 parity bit -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_mov op2_imm op2_reg dpVal)

theorem xor_low_mask32 (x y : BitVec 32) :
    0 - ((x ^^^ y) &&& 1) = mask32 (x.toNat % 2 ≠ y.toNat % 2) := by
  have hlow : (x ^^^ y) &&& 1 = if x.toNat % 2 = y.toNat % 2 then 0 else 1 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_xor, show (1 : BitVec 32).toNat = 1 from rfl,
      Nat.and_one_is_mod, show 2 = 2 ^ 1 from rfl, Nat.xor_mod_two_pow]
    rcases Nat.mod_two_eq_zero_or_one x.toNat with hx | hx <;>
      rcases Nat.mod_two_eq_zero_or_one y.toNat with hy | hy <;> simp [hx, hy]
  rw [hlow]
  by_cases h : x.toNat % 2 = y.toNat % 2 <;> simp [h, mask32]

theorem parityMask_ok {c : Cfg} {s : State} {base : Addr}
    (hs : Scr s base size) (hn : 0 < c.n)
    (hy : c.sl Impl.Ecdh.Arm.QY + 4 ≤ size) (ht : c.sl D + 4 ≤ size) :
    WP isa (.block (Impl.EcKey.Compressed.Arm.parityMask c)) s fun t =>
      t.gpr .r10 = mask32 (sv c base s Impl.Ecdh.Arm.QY % 2 ≠
        (s.mem.readW (off base (c.sl D)) 32).toNat % 2) ∧
      Rest [.r4, .r5, .r10] s t ∧ t.mem = s.mem := by
  unfold Impl.EcKey.Compressed.Arm.parityMask
  refine wp_ldr (hs.off_lt (by omega_using [hy])) (hs.ea (by omega_using [hy])) (hs.read hy) fun s₁ u₁ => ?_
  have hs₁ := hs.of_rest (u₁.rest (ws := [.r4]) (by simp)) (by decide)
  refine wp_ldr (hs₁.off_lt (by omega_using [ht])) (hs₁.ea (by omega_using [ht])) (hs₁.read ht) fun s₂ u₂ => ?_
  refine wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_dp (op2_imm (by decide)) fun s₄ u₄ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₅ u₅ => ?_
  refine wp_dp (op2_reg _ _) fun t u₆ => WP.block_nil ?_
  refine ⟨?_, (u₁.rest (by simp)).trans ((u₂.rest (by simp)).trans ((u₃.rest (by simp)).trans
      ((u₄.rest (by simp)).trans ((u₅.rest (by simp)).trans (u₆.rest (by simp)))))), ?_⟩
  · rw [u₆.gpr, dpVal, u₅.gpr, u₅.other .r5 (by decide), u₄.gpr, dpVal, u₃.gpr, dpVal,
      u₂.gpr, u₂.other .r4 (by decide), u₁.gpr, u₁.mem, BitVec.xor_comm, xor_low_mask32]
    rw [slot32_parity _ _ _ _ hn]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

theorem invertMask_ok (s : State) (P : Prop) [Decidable P] (h : s.gpr .r10 = mask32 P) :
    WP isa (.block Impl.EcKey.Compressed.Arm.invertMask) s fun t =>
      t.gpr .r5 = mask32 (¬ P) ∧ Rest [.r4, .r5] s t ∧ t.mem = s.mem := by
  unfold Impl.EcKey.Compressed.Arm.invertMask
  refine wp_dp (op2_imm (by decide)) fun s₁ u₁ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  refine wp_dp (op2_reg _ _) fun t u₃ => WP.block_nil ?_
  refine ⟨?_, (u₁.rest (by simp)).trans ((u₂.rest (by simp)).trans (u₃.rest (by simp))), ?_⟩
  · rw [u₃.gpr, dpVal, u₂.gpr, u₂.other .r5 (by decide), u₁.gpr, dpVal, h]
    by_cases hp : P <;> simp [mask32, hp]
  · rw [u₃.mem, u₂.mem, u₁.mem]

end VG.Proof.EcKey.Compressed.Arm

end

end

/-! ### `EcKey.Compressed.Arm.Select`, which only this module used -/

section

/-! # Leave Montgomery form and choose between the two canonical roots -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG.Proof.X25519.Arm (Rest)
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Impl.Ecdh.Arm (QY W0)
open VG.Proof.Ecdsa.Arm VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm

structure SelectPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  mod : ModOkW c.MP' size c.C.p s'.mem base
  keep : Rest Mont.callClob s s'
  unch : Unch base (slWk c [QY, W0, TMP]) s.mem s'.mem
  lt : sv c base s' QY < c.C.p
  val : Fin.ofNat c.C.p (sv c base s' QY) =
    let y := toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)
    if y.val % 2 = (s.mem.readW (off base (c.sl D)) 32).toNat % 2 then y else -y

theorem selectRoot_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hf : Far s base 8192) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hOne : sv c base s ONE = 1) (hZero : sv c base s ZERO = 0) :
    WP isa (Impl.EcKey.Compressed.Arm.selectRoot c) s (SelectPost c base s) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hp3 := hc.p_ge
  obtain hY := sl_le c h7 (i := QY) (by decide)
  obtain hZ := sl_le c h7 (i := ZERO) (by decide)
  obtain hW := sl_le c h7 (i := W0) (by decide)
  obtain hD := sl_le c h7 (i := D) (by decide)
  obtain hMP := sl_le c h7 (i := MP) (by decide)
  change WP isa (.seq (Mont.mulCall c.SP (c.sl QY) (c.sl ACC) (c.sl ONE) c.umaal)
    (.seq (Mont.subCall c.SP (c.sl W0) (c.sl ZERO) (c.sl QY) c.umaal)
      (.block (Impl.EcKey.Compressed.Arm.parityMask c ++ sel (2 * c.n) (c.sl QY) (c.sl QY) (c.sl W0))))) s _
  refine WP.seq (WP.mono (slMul_ok hc.fp (MP'_n c) h7 hs hf (o := QY) (a := ACC) (b := ONE)
    (by decide) (by decide) (by decide) (by rw [hOne]; omega_using [hp3]))
    fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_)
  obtain hs₁ := k₁.scr hs
  obtain hM₁ := hM.keepArm (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  obtain normal : Fin.ofNat c.C.p (sv c base s₁ QY) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) :=
    toM_one_mul (unitMod_pow_two hc.p_odd (64 * c.n)) (by simpa only [hOne] using e₁)
  obtain normalVal : sv c base s₁ QY =
      (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)).val := by
    simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt lt₁] using congrArg Fin.val normal
  obtain zero₁ : sv c base s₁ ZERO = 0 :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hZero
  refine WP.seq (WP.mono (slSub_ok hc.fp (MP'_n c) h7 hs₁ (hf.of_rest k₁.rest)
    (o := W0) (a := ZERO) (b := QY) (by decide) (by decide) (by decide)
    (by rw [zero₁]; omega_using [hp3]) lt₁) fun s₂ ⟨k₂, e₂⟩ => ?_)
  change sv c base s₂ W0 = (sv c base s₁ ZERO + c.C.p - sv c base s₁ QY) % c.C.p at e₂
  obtain hs₂ := k₂.scr hs₁
  obtain hM₂ := hM₁.keepArm (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  obtain y₂ : sv c base s₂ QY = sv c base s₁ QY :=
    sv_keep (MP'_n c) rfl h7 hn k₂ (by decide) (by decide) (by decide)
  obtain negLt : sv c base s₂ W0 < c.C.p := by
    rw [e₂]
    exact Nat.mod_lt _ (by omega_using [hp3])
  obtain negVal : Fin.ofNat c.C.p (sv c base s₂ W0) = -(Fin.ofNat c.C.p (sv c base s₁ QY)) := by
    apply Fin.ext
    simp only [Fin.val_ofNat, Fin.neg_def]
    rw [show sv c base s₂ W0 = (sv c base s₁ ZERO + c.C.p - sv c base s₁ QY) % c.C.p from e₂,
      zero₁, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt lt₁]
  obtain U₁₂ : Unch base (slWk c [QY, W0, TMP]) s.mem s₂.mem :=
    unch_same (unch_slots (MP'_n c) rfl k₁.unch (by simp) (by simp))
      (unch_slots (MP'_n c) rfl k₂.unch (by simp) (by simp))
  obtain tag₂ : s₂.mem.readW (off base (c.sl D)) 32 = s.mem.readW (off base (c.sl D)) 32 :=
    Unch.readW32 U₁₂ (fun w hw => by
      have := apart_slWk h7 (i := D) (by decide) (by decide) w hw
      omega_using [h0, this]) (by omega_using [hn, hD])
  rw [WP.block_append_iff]
  refine WP.mono (parityMask_ok hs₂ h0 (by omega_using [h0, hY]) (by omega_using [h0, hD])) fun s₃ ⟨mask₃, k₃, m₃⟩ => ?_
  obtain hs₃ := hs₂.of_rest k₃ (by decide)
  refine WP.mono (sel_ok (decide (sv c base s₂ QY % 2 ≠ (s₂.mem.readW (off base (c.sl D)) 32).toNat % 2)) (2 * c.n) hs₃
    (by simpa only [mask32, decide_eq_true_eq] using mask₃)
    (by omega_using [hY]) (by omega_using [hY]) (by omega_using [hW]) (Or.inl (Nat.le_refl _))
    (by have := sl_apart c (i := QY) (j := W0) (by decide); omega_using [this])) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  rw [show 4 * (2 * c.n) = 8 * c.n by omega_using []] at O₄
  obtain hs₄ := hs₃.of_rest k₄ (by decide)
  obtain hM₄ : ModOkW c.MP' size c.C.p s₄.mem base := modP_of hc (by
    rw [O₄.wordsVal (d := c.sl MP) (k := c.n)
      (sl_apart c (i := MP) (j := QY) (by decide)) (by omega_using [hn, hMP]), m₃]
    exact hM₂.val)
  obtain e₄' : sv c base s₄ QY =
      if sv c base s₂ QY % 2 ≠ (s₂.mem.readW (off base (c.sl D)) 32).toNat % 2 then
        sv c base s₂ W0 else sv c base s₂ QY := by
    simpa only [sv, wordsVal_eq_val32, m₃, decide_eq_true_eq] using e₄
  refine ⟨hs₄, hM₄, ?_, ?_, ?_, ?_⟩
  · exact (k₁.rest.trans k₂.rest).trans ((k₃.mono (by decide)).trans (k₄.mono (by decide)))
  · apply unch_same U₁₂
    rw [← m₃]
    exact (slot_frame (slots := [QY, W0, TMP]) (by simp) (by omega_using []) O₄).mono
      (fun w hw => List.mem_append_left _ hw)
  · rw [e₄']
    split
    · exact negLt
    · rw [y₂]
      exact lt₁
  · change Fin.ofNat c.C.p (sv c base s₄ QY) =
      if (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)).val % 2 =
        (s.mem.readW (off base (c.sl D)) 32).toNat % 2 then _ else _
    rw [y₂, tag₂, normalVal] at e₄'
    by_cases hm : (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)).val % 2 =
        (s.mem.readW (off base (c.sl D)) 32).toNat % 2
    · rw [ite_eq_left hm]
      rw [ite_eq_right (not_not_intro hm)] at e₄'
      rw [e₄']
      exact Fin.ext (Nat.mod_eq_of_lt (toM _ _ _).isLt)
    · rw [ite_eq_right hm]
      rw [ite_eq_left hm] at e₄'
      rw [e₄', negVal, normal]

end VG.Proof.EcKey.Compressed.Arm

end

end

/-! ### `EcKey.Compressed.Arm.Check`, which only this module used -/

section

/-! # Check the recovered root's square and parity -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdh.Arm (QY QYM R2P W1 W2 W3)
open VG.Proof.Ecdsa.Arm VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
open VG.Proof.Ecdh.Arm
open VG.Proof.X25519.Arm (Rest)

def checkN : List FOp := [.mul QYM QY R2P, .mul W1 QYM QYM, .sub W3 W1 W2]
abbrev checkSlots : List Nat := [QY, R2P, W2, QYM, W1, W3]

theorem checkOps_eq (c : Cfg) : Impl.EcKey.Compressed.Arm.checkRootOps c =
    checkN.map (FOp.rename c.sl) := rfl

theorem checkN_run {F : Type} [Lean.Grind.CommRing F] (e : Nat → F) :
    runOps checkN e W3 = (e QY * e R2P) * (e QY * e R2P) - e W2 := by
  simp only [checkN, runOps_cons, runOps_nil, FOp.run, Function.update_apply]
  simp only [QYM, QY, R2P, W1, W2, X, RR, DM, TT, SM, Nat.reduceEqDiff, ↓reduceIte]

theorem checkN_reads : readsOk checkN [QY, R2P, W2] = true := by decide
theorem checkN_slots : ∀ op ∈ checkN, ∀ x ∈ op.out :: op.ins, x ∈ checkSlots := by decide
theorem checkN_out : ∀ op ∈ checkN, op.out ∈ [QYM, W1, W3, TMP] := by decide

theorem raw_r2_mul {c : Cfg} (hc : CfgOk c) (a : Nat) :
    toM c.C.p (2 ^ (64 * c.n)) a *
      toM c.C.p (2 ^ (64 * c.n)) (c.R * c.R % c.C.p) = Fin.ofNat c.C.p a := by
  change toM c.C.p (2 ^ (64 * c.n)) a * toM c.C.p (2 ^ (64 * c.n)) (c.mont c.R) = _
  rw [toM_cmont hc]
  unfold toM
  obtain hu := mul_rinv (unitMod_pow_two hc.p_odd (64 * c.n))
  change Fin.ofNat c.C.p c.R * rinv c.C.p (2 ^ (64 * c.n)) = 1 at hu
  grind

structure CheckPolyPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  keep : Rest Mont.callClob s s'
  unch : Unch base (slWk c [QYM, W1, W3, TMP]) s.mem s'.mem
  lt : sv c base s' W3 < c.C.p
  val : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' W3) =
    Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) -
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2)

theorem checkPoly_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hfar : Far s base 8192) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hy : sv c base s QY < c.C.p) (hr : sv c base s W2 < c.C.p)
    (hr2 : sv c base s R2P = c.R * c.R % c.C.p) :
    WP isa (Impl.Weierstrass.Arm.fprog c.SP
      (Impl.EcKey.Compressed.Arm.checkRootOps c) c.umaal) s (CheckPolyPost c base s) := by
  have h7 := hc.n10
  obtain hL : Lay c.MP' size (· ∈ checkSlots.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  obtain hW : WkOk c.MP' size c.wk (· ∈ checkSlots.map c.sl) := by
    refine ⟨wk_le c h7 rfl, ?_, sl_below_wk c h7 (by decide), sl_below_wk c h7 (by decide)⟩
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain H : ∀ i ∈ checkSlots, i < 45 := by decide
    exact sl_below_wk c h7 (H i hi)
  obtain I : Inv c.MP' base size c.C.p (· ∈ checkSlots.map c.sl) ([QY, R2P, W2].map c.sl)
      (fun o => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base o c.n)) s := by
    refine ⟨hs, hM, ?_, ?_, fun _ _ => rfl, hfar⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      obtain sub : ∀ i ∈ [QY, R2P, W2], i ∈ checkSlots := by decide
      exact List.mem_map_of_mem (sub i hi)
    · intro x hx
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact hy
      · show sv c base s R2P < _
        rw [hr2]
        exact Nat.mod_lt _ (by have := hc.p_ge; omega_using [hy])
      · exact hr
  rw [checkOps_eq]
  refine WP.mono (fprog_ok hL hW hc.fp (unitMod_pow_two hc.p_odd (64 * c.n)) _ I
    (fun op hop x hx => ?_)
    (readsOk_rename c.sl checkN_reads)) fun t ⟨PK, IT⟩ => ?_
  · obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
    obtain hx' : x ∈ (op₀.out :: op₀.ins).map c.sl := by
      cases op₀ <;> simpa [FOp.rename, FOp.out, FOp.ins] using hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    exact List.mem_map_of_mem (checkN_slots _ h₀ _ hi)
  obtain hw : c.sl W3 ∈ validAfter (checkN.map (FOp.rename c.sl)) ([QY, R2P, W2].map c.sl) :=
    (mem_validAfter _ _).mpr (Or.inr (by simp [checkN, FOp.rename, FOp.out]))
  obtain vt := IT.val _ hw
  rw [congrFun (runOps_rename c.sl checkN _ fun _ _ _ h => sl_inj c hc.n0 h) W3, checkN_run] at vt
  refine ⟨PK.scr hs, PK.rest, ?_, IT.lt _ hw, ?_⟩
  · apply PK.unch.mono
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hw
      obtain ⟨op, hop, rfl⟩ := List.mem_map.mp ho
      obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
      exact List.mem_append_left _ (List.mem_map.mpr ⟨op₀.out, checkN_out _ h₀, by rw [FOp.out_rename]; rfl⟩)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact List.mem_append_left _ (List.mem_map_of_mem (by decide))
      · exact List.mem_append_right _ (by simp [MP'_n])
  · change toM c.C.p (2 ^ (64 * c.n)) (sv c base t W3) =
      (toM c.C.p (2 ^ (64 * c.n)) (sv c base s QY) *
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s R2P)) *
      (toM c.C.p (2 ^ (64 * c.n)) (sv c base s QY) *
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s R2P)) -
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) at vt
    simpa only [hr2, raw_r2_mul hc] using vt

structure CheckRootPost (c : Cfg) (base : Addr) (P : Prop) [Decidable P] (s s' : State) : Prop where
  scr : Scr s' base size
  keep : Rest Mont.callClob s s'
  unch : Unch base (slWk c [QYM, W1, W3, TMP, FLAG]) s.mem s'.mem
  flag : flagW c base s' = mask32
    ((P ∧ Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2)) ∧
      sv c base s QY % 2 = (s.mem.readW (off base (c.sl D)) 32).toNat % 2)

theorem checkRoot_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hfar : Far s base 8192) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hy : sv c base s QY < c.C.p) (hr : sv c base s W2 < c.C.p)
    (hr2 : sv c base s R2P = c.R * c.R % c.C.p) {P : Prop} [Decidable P]
    (hf : flagW c base s = mask32 P) :
    WP isa (Impl.EcKey.Compressed.Arm.checkRoot c) s (CheckRootPost c base P s) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hsz : size = 4096 := rfl
  obtain hF := sl_le c h7 (i := FLAG) (by decide)
  obtain hW := sl_le c h7 (i := W3) (by decide)
  obtain hY := sl_le c h7 (i := QY) (by decide)
  obtain hD := sl_le c h7 (i := D) (by decide)
  change WP isa (.seq
    (Impl.Weierstrass.Arm.fprog c.SP (Impl.EcKey.Compressed.Arm.checkRootOps c) c.umaal)
    (.block (Impl.EcKey.Compressed.Arm.checkRootChecks c))) s _
  refine WP.seq (WP.mono (checkPoly_ok hc hs hfar hM hy hr hr2) fun s₁ I => ?_)
  obtain flag₁ : flagW c base s₁ = mask32 P := by
    rw [flagW, Unch.readW32 I.unch (fun w hw => by have := apart_slWk h7 (i := FLAG) (by decide) (by decide) w hw; omega_using [h0, this]) (by omega_using [hn, hF]), ← flagW, hf]
  obtain hz : sv c base s₁ W3 = 0 ↔
      Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) := by
    rw [← toM_eq_zero_iff (unitMod_pow_two hc.p_odd (64 * c.n)) I.lt, I.val]
    constructor <;> intro h <;> grind
  rw [Impl.EcKey.Compressed.Arm.checkRootChecks, WP.block_append_iff]
  refine WP.mono (checkZero_ok c I.scr h0 hW (by omega_using [h0, hF])) fun s₂ ⟨f₂, k₂, O₂⟩ => ?_
  obtain hs₂ := I.scr.of_rest k₂ (by decide)
  obtain flag₂ : flagW c base s₂ = mask32
      (P ∧ Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2)) := by
    rw [f₂, flag₁, show wordsVal s₁.mem base (c.sl W3) c.n = sv c base s₁ W3 from rfl, mask32_and]
    simp only [mask32, hz]
  obtain y₂ : sv c base s₂ QY = sv c base s QY := by
    rw [sv, sv_flag O₂ h0 h7 hn (by decide) (by decide)]
    exact sv_unch I.unch h7 hn (by decide) (apart_slWk h7 (by decide) (by decide))
  obtain tag₂ : s₂.mem.readW (off base (c.sl D)) 32 = s.mem.readW (off base (c.sl D)) 32 := by
    rw [BitVec.eq_of_toNat_eq (O₂.w32 (by have := sl_apart c (i := D) (j := FLAG) (by decide); omega_using [h0, this]) (by omega_using [hn, hD]))]
    exact Unch.readW32 I.unch (fun w hw => by
      have := apart_slWk h7 (i := D) (by decide) (by decide) w hw
      omega_using [h0, this]) (by omega_using [hn, hD])
  rw [WP.block_append_iff]
  refine WP.mono (parityMask_ok hs₂ h0 (by omega_using [h0, hY]) (by omega_using [h0, hD])) fun s₃ ⟨mask₃, k₃, m₃⟩ => ?_
  rw [y₂, tag₂] at mask₃
  rw [WP.block_append_iff]
  refine WP.mono (invertMask_ok s₃ _ mask₃) fun s₄ ⟨mask₄, k₄, m₄⟩ => ?_
  obtain hs₄ := (hs₂.of_rest k₃ (by decide)).of_rest k₄ (by decide)
  refine WP.mono (andFlag_ok c hs₄ (by omega_using [h0, hF])) fun s₅ ⟨flag₅, k₅, O₅⟩ => ?_
  refine ⟨hs₄.of_rest k₅ (by decide), ?_, ?_, ?_⟩
  · exact (((I.keep.trans (k₂.mono (by decide))).trans
      (k₃.mono (by decide))).trans (k₄.mono (by decide))).trans (k₅.mono (by decide))
  · have U₁ : Unch base (slWk c [QYM, W1, W3, TMP, FLAG]) s.mem s₁.mem := I.unch.mono (by
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
        exact List.mem_append_left _ (List.mem_map_of_mem (List.mem_append_left [FLAG] hi))
      · exact List.mem_append_right _ hw)
    obtain U₂ : Unch base (slWk c [QYM, W1, W3, TMP, FLAG]) s₁.mem s₄.mem := by
      rw [m₄, m₃]
      exact (slot_frame (slots := [QYM, W1, W3, TMP, FLAG]) (by simp) (by omega_using [h0]) O₂).mono
        (fun w hw => List.mem_append_left _ hw)
    exact unch_same (unch_same U₁ U₂) ((slot_frame (slots := [QYM, W1, W3, TMP, FLAG])
      (by simp) (by omega_using [h0]) O₅).mono (fun w hw => List.mem_append_left _ hw))
  · rw [flag₅, mask₄]
    change s₄.mem.readW (off base (c.sl FLAG)) 32 &&& _ = _
    rw [m₄, m₃, ← flagW, flag₂]
    simp only [not_not]
    exact mask32_and _ _

end VG.Proof.EcKey.Compressed.Arm

end

end


/-! # Coordinate recovery and final checks preserve the parsed encoding -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm VG.Impl.Ecdsa.Arm
open VG.Impl.Ecdh.Arm (QY QYM R2P W0 W1 W2 W3)
open VG.Proof.Ecdsa.Arm VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
open VG.Impl.EcKey.Compressed (chooseRoot)

def keyRhs (c : Cfg) (s : State) : Spec.Weierstrass.Fe c.C :=
  let x := Fin.ofNat c.C.p (keyX c s)
  x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b

def keyRoot (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C) (s : State) :=
  chooseRoot (root (keyRhs c s)) ((s.mem (ptr s .r1)).toNat % 2)

def CompressedAccept (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C)
    (s : State) : Prop := CompressedPrefix c s ∧
  (keyRoot c root s * keyRoot c root s = keyRhs c s ∧
    (keyRoot c root s).val % 2 = (s.mem (ptr s .r1)).toNat % 2)

instance (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C) (s : State) :
    Decidable (CompressedAccept c root s) := inferInstanceAs (Decidable (_ ∧ (_ ∧ _)))

structure DecompressChecked (c : Cfg)
    (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C)
    (s₀ : State) (s : State) : Prop where
  scr : Scr s (ptr s₀ .r2) size
  saved : ∀ rd ∈ Cfg.saved, s.mem.readW (off (ptr s₀ .r2) rd.2) 32 = s₀.gpr rd.1
  out : s.gpr .lr = s₀.gpr .r0
  x : sv c (ptr s₀ .r2) s E = keyX c s₀
  y : sv c (ptr s₀ .r2) s QY = (keyRoot c root s₀).val
  flag : flagW c (ptr s₀ .r2) s = mask32 (CompressedAccept c root s₀)
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem decompressMiddle_ok {c : Cfg} (hc : CfgOk c)
    {root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C} (hroot : CandidateCorrect c root)
    {s₀ s : State} (F : DecompressFront c s₀ s) :
    WP isa (.seq (Impl.EcKey.Compressed.Arm.rootCandidate c)
      (.seq (Impl.EcKey.Compressed.Arm.selectRoot c)
        (Impl.EcKey.Compressed.Arm.checkRoot c))) s (DecompressChecked c root s₀) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := F.scr.nowrap
  refine WP.seq (WP.mono (hroot _ s F.scr F.far (modP_of hc F.fixed.mp) F.rhs_lt F.fixed.onep)
    fun s₁ C => ?_)
  obtain F₁ := F.frame hc C.keep C.unch (candidate_fixed hc) (by
    intro i hi
    obtain h : ∀ i ∈ [E, D, R2P, W2, FLAG], i < 45 ∧ i ∉ candidateSlots := by decide
    exact candidate_apart hc (h i hi).1 (h i hi).2)
  obtain root₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c (ptr s₀ .r2) s₁ ACC) = root (keyRhs c s₀) := by
    rw [C.val, F.rhs]; rfl
  refine WP.seq (WP.mono (selectRoot_ok hc F₁.scr F₁.far (modP_of hc F₁.fixed.mp)
    F₁.fixed.one F₁.fixed.zero) fun s₂ S => ?_)
  obtain F₂ := F₁.frame hc (S.keep.mono (by decide)) S.unch
    (fixedOk_slWk h7 (l := [QY, W0, TMP]) (by decide)) (by
      intro i hi
      obtain h : ∀ i ∈ [E, D, R2P, W2, FLAG], i ∉ [QY, W0, TMP] := by decide
      exact apart_slWk h7 (by
        obtain H : ∀ i ∈ [E, D, R2P, W2, FLAG], i < 45 := by decide
        exact H i hi) (h i hi))
  obtain y₂ : Fin.ofNat c.C.p (sv c (ptr s₀ .r2) s₂ QY) = keyRoot c root s₀ := by
    rw [S.val, root₁, F₁.tag]
    simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show
      (s₀.mem (ptr s₀ .r1)).toNat < 2 ^ 32 from Nat.lt_trans (BitVec.isLt _) (by decide))]
    rfl
  obtain yval₂ : sv c (ptr s₀ .r2) s₂ QY = (keyRoot c root s₀).val := by
    simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt S.lt] using congrArg Fin.val y₂
  refine WP.mono (checkRoot_ok hc F₂.scr F₂.far (modP_of hc F₂.fixed.mp) S.lt
    F₂.rhs_lt F₂.r2 F₂.flag) fun s₃ K => ?_
  obtain F₃ := F₂.fixed.unch h7 hn
    (fixedOk_slWk h7 (l := [QYM, W1, W3, TMP, FLAG]) (by decide)) K.unch
  have e₃ {i : Nat} (hi : i < 45) (hw : i ∉ [QYM, W1, W3, TMP, FLAG]) :
      sv c (ptr s₀ .r2) s₃ i = sv c (ptr s₀ .r2) s₂ i :=
    sv_unch K.unch h7 hn hi (apart_slWk h7 hi hw)
  refine ⟨K.scr, F₃.saved, (K.keep.gpr _ (by decide)).trans F₂.out,
    (e₃ (by decide) (by decide)).trans F₂.x,
    (e₃ (by decide) (by decide)).trans yval₂, ?_, K.keep.sp.trans F₂.sp,
    K.keep.rd.trans F₂.rd, K.keep.wr.trans F₂.wr⟩
  rw [K.flag, y₂, yval₂, F₂.rhs, F₂.tag]
  simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show
    (s₀.mem (ptr s₀ .r1)).toNat < 2 ^ 32 from Nat.lt_trans (BitVec.isLt _) (by decide))]
  simp only [mask32, CompressedAccept, keyRhs, and_assoc]

end VG.Proof.EcKey.Compressed.Arm

end

end

/-! # Decompression meets the merged API contract -/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/Arm/DecompressFinish.lean`, which only this module imported.
section

section

namespace VG.Proof.EcKey.Compressed.Arm

open VG.Proof.Mont VG.Proof.Mont.Arm
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm Spec.Weierstrass
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.EcKey.Arm (pointFinish_ok)

variable {c : Cfg}

theorem decompressFinish_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size) {o32 : BitVec 32}
    (hlr : s.gpr .lr = o32) (hofit : o32.toNat + (1 + 2 * c.C.len) ≤ 2 ^ 32)
    (hw : (⟨State.addr o32, 1 + 2 * c.C.len⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨State.addr o32, 1 + 2 * c.C.len⟩ ⟨base, size⟩)
    {g : Reg → BitVec 32} (hsv : ∀ rd ∈ Cfg.saved, s.mem.readW (off base rd.2) 32 = g rd.1) (b : Bool)
    (hf : flagW c base s = mask32 (b = true)) :
    WP isa (.block (Impl.EcKey.Compressed.Arm.decompressFinish c)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem (State.addr o32) (1 + 2 * c.C.len) =
        (if b then 4 :: (toBytes c.C.len (sv c base s E) ++ toBytes c.C.len (sv c base s Impl.Ecdh.Arm.QY))
          else List.replicate (1 + 2 * c.C.len) 0) ∧
      s'.gpr .r0 = (if b then 1 else 0) ∧
      (∀ rd ∈ Cfg.saved, s'.gpr rd.1 = g rd.1) ∧
      Rest [.r0, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr] s s' ∧
      Outside (State.addr o32) 0 (1 + 2 * c.C.len) s.mem s'.mem :=
  pointFinish_ok hc (by decide) (by decide) hs hlr hofit hw hd hsv b hf

end VG.Proof.EcKey.Compressed.Arm
end

end

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm VG.Impl.Ecdsa.Arm
open VG.Proof.Ecdsa.Arm VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm Spec.Weierstrass

theorem decompress_key (c : Cfg) (root : Fe c.C → Fe c.C) (s : State) :
    Impl.EcKey.Compressed.decode c.C root
      (Spec.EcKey.bytesAt s.mem (ptr s .r1) (c.C.len + 1)) =
    if CompressedAccept c root s then
      some (.affine (Fin.ofNat c.C.p (keyX c s)) (keyRoot c root s)) else none := by
  have hb : Spec.Ecdsa.bytesAt s.mem (ptr s .r1) (c.C.len + 1) =
      s.mem (ptr s .r1) :: Spec.Ecdsa.bytesAt s.mem (ptr s .r1 + 1) c.C.len := by
    rw [Nat.add_comm c.C.len 1, bytesAt_add]
    simp only [Spec.Ecdsa.bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero,
      List.cons_append, List.nil_append]
    rfl
  apply decode_checked_eq root (length_bytesAt _ _ _)
    (by change (Spec.Ecdsa.bytesAt _ _ _).head? = _; rw [hb]; rfl)
    (by change ofBytes ((Spec.Ecdsa.bytesAt _ _ _).drop 1) = _; rw [hb]; rfl)

theorem decompress_correct (c : Cfg) (hc : CfgOk c)
    (root : Fe c.C → Fe c.C) (hroot : CandidateCorrect c root)
    (s : State) (hs : (decompressContract c.C root).pre s) :
    ∃ t s', Exec isa (Impl.EcKey.Compressed.Arm.decompress c) s t s' ∧
      abiPreserved s s' ∧ (decompressContract c.C root).post s s' := by
  obtain ⟨hrd, hwr, hpo, hpw, how, hfit, hpkfit, hwfit⟩ := hs
  have hp : InputPre c (1 + c.C.len) s :=
    ⟨by rw [hrd]; simp [Nat.add_comm], by rw [hwr]; simp,
      by simpa only [Nat.add_comm] using hpw, by omega_using [hpkfit], hwfit⟩
  have hrun : WP isa (Impl.EcKey.Compressed.Arm.decompress c) s fun s' =>
      (decompressContract c.C root).post s s' ∧
      (∀ rd ∈ Cfg.saved, s'.gpr rd.1 = s.gpr rd.1) ∧ s'.sp = s.sp := by
    apply decompressFront_ok hc hp
    intro t F
    refine WP.seq (WP.mono (decompressMiddle_ok hc hroot F) fun u U => ?_)
    refine WP.mono (decompressFinish_ok hc U.scr U.out (by omega_using [hfit])
      (by rw [U.wr, hwr, show 1 + 2 * c.C.len = 2 * c.C.len + 1 by omega_using []]; simp)
      (by simpa only [Nat.add_comm] using how.sub_right (Region.sub_prefix (by decide : size ≤ 8192)))
      U.saved (decide (CompressedAccept c root s)) (by simp only [U.flag, decide_eq_true_eq]))
      fun s' ⟨hout, hret, hsave, K, _⟩ => ?_
    refine ⟨?_, hsave, K.sp.trans U.sp⟩
    dsimp only [decompressContract]
    rw [decompress_key]
    rw [U.x, U.y] at hout
    change Spec.EcKey.bytesAt s'.mem (ptr s .r0) (1 + 2 * c.C.len) = _ at hout
    simp only [decide_eq_true_eq] at hret hout
    simp only [BitVec.setWidth_append_eq_right]
    by_cases hk : CompressedAccept c root s
    · rw [ite_eq_left hk] at hret hout ⊢
      refine ⟨hret, ?_⟩
      change Spec.EcKey.bytesAt s'.mem (ptr s .r0) (2 * c.C.len + 1) =
        4 :: (toBytes c.C.len (Fin.ofNat c.C.p (keyX c s)).val ++ toBytes c.C.len (keyRoot c root s).val)
      simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt hk.1.2, Nat.add_comm] using hout
    · rw [ite_eq_right hk] at hret hout ⊢
      exact ⟨hret, by simpa only [Nat.add_comm] using hout⟩
  obtain ⟨t, s', he, hpost, hsave, hsp⟩ := hrun
  refine ⟨t, s', he, ⟨?_, hsp⟩, hpost⟩
  intro r hr
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hsave (.r4, 0) (by decide)
  · exact hsave (.r5, 4) (by decide)
  · exact hsave (.r6, 8) (by decide)
  · exact hsave (.r7, 12) (by decide)
  · exact hsave (.r8, 16) (by decide)
  · exact hsave (.r9, 20) (by decide)
  · exact hsave (.r10, 24) (by decide)
  · exact hsave (.r11, 28) (by decide)
  · exact hsave (.lr, 32) (by decide)

end VG.Proof.EcKey.Compressed.Arm
