module

public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Candidate
public import VerifiedGarbage.Impl.EcKey.Compressed.Root
public import VerifiedGarbage.Spec.EcKey.Compressed
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Front
public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64.Decompress
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Fixed
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Frame
import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Parity
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.AArch64.Middle
import VerifiedGarbage.Proof.Mont.AArch64.Ops
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Ecdsa.AArch64.Scalar
public import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Weierstrass.AArch64.Pow
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Setup
import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! ### `EcKey.Compressed.AArch64.Select`, which only this module used -/

section

/-! # Leave Montgomery form and choose between the two canonical roots -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdh.AArch64 (QY W0)
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

structure SelectPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  mod : ModOkA c.MP' size c.C.p s'.mem base
  keep : KeepRegs (clob c.n) s s'
  unch : Unch base (slW c [QY, W0, TMP]) s.mem s'.mem
  lt : sv c base s' QY < c.C.p
  val : Fin.ofNat c.C.p (sv c base s' QY) =
    let y := toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)
    if y.val % 2 = (word s.mem base (c.sl D)).toNat % 2 then y else -y

theorem selectRoot_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkA c.MP' size c.C.p s.mem base)
    (hOne : sv c base s ONE = 1) (hZero : sv c base s ZERO = 0) :
    WP isa (Impl.EcKey.Compressed.AArch64.selectRoot c) s (SelectPost c base s) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hp3 := hc.p_ge
  have hY := sl_le c h7 (i := QY) (by decide)
  have hZ := sl_le c h7 (i := ZERO) (by decide)
  have hW := sl_le c h7 (i := W0) (by decide)
  have hD := sl_le c h7 (i := D) (by decide)
  have hMP := sl_le c h7 (i := MP) (by decide)
  change WP isa (.seq (opProg c.MP' (.mul (c.sl QY) (c.sl ACC) (c.sl ONE)))
    (.block (opCode c.MP' (.sub (c.sl W0) (c.sl ZERO) (c.sl QY)) ++
      Impl.EcKey.Compressed.AArch64.parityMask c ++ sel c.n (c.sl QY) (c.sl QY) (c.sl W0)))) s _
  rw [mulPP_eq_op _ _ _ (by
    intro h
    have := sl_inj c hc.n0 h
    contradiction)]
  refine WP.seq (WP.mono (slMulP_ok hc hs hM (o := QY) (a := ACC) (b := ONE)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [hOne]; omega_using [hp3]))
    fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_)
  have hs₁ := k₁.scr hs
  have hM₁ := hM.keepA64 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  have normal : Fin.ofNat c.C.p (sv c base s₁ QY) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) :=
    toM_one_mul (unitMod_pow_two hc.p_odd (64 * c.n)) (by simpa only [hOne] using e₁)
  have normalVal : sv c base s₁ QY =
      (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)).val := by
    simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt lt₁] using congrArg Fin.val normal
  have zero₁ : sv c base s₁ ZERO = 0 :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hZero
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (subOp_ok hs₁ hM₁ (MP'_A c) hW hZ hY (sl_mod8 c W0) (sl_mod8 c ZERO) (sl_mod8 c QY)
    (by change sv c base s₁ ZERO < c.C.p; rw [zero₁]; omega_using [hp3])
    lt₁) fun s₂ ⟨k₂, e₂⟩ => ?_
  change sv c base s₂ W0 = (sv c base s₁ ZERO + c.C.p - sv c base s₁ QY) % c.C.p at e₂
  have hs₂ := k₂.scr hs₁
  have hM₂ := hM₁.keepA64 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  have y₂ : sv c base s₂ QY = sv c base s₁ QY :=
    sv_keep (MP'_n c) rfl h7 hn k₂ (by decide) (by decide) (by decide)
  have negLt : sv c base s₂ W0 < c.C.p := by
    rw [e₂]
    exact Nat.mod_lt _ (by omega_using [hp3])
  have negVal : Fin.ofNat c.C.p (sv c base s₂ W0) = -(Fin.ofNat c.C.p (sv c base s₁ QY)) := by
    apply Fin.ext
    simp only [Fin.val_ofNat, Fin.neg_def]
    rw [show sv c base s₂ W0 = (sv c base s₁ ZERO + c.C.p - sv c base s₁ QY) % c.C.p from e₂,
      zero₁, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt lt₁]
  have U₁₂ : Unch base (slW c [QY, W0, TMP]) s.mem s₂.mem :=
    unch_same (unch_slots (MP'_n c) rfl k₁.unch (by simp) (by simp))
      (unch_slots (MP'_n c) rfl k₂.unch (by simp) (by simp))
  have tag₂ : word s₂.mem base (c.sl D) = word s.mem base (c.sl D) :=
    U₁₂.word (fun w hw => by
      have := (apart_slW (c := c) (by decide : D ∉ [QY, W0, TMP])) w hw
      omega_using [h0, this]) (by have := hs.nowrap; omega_using [h0, hn, hD])
  rw [WP.block_append_iff]
  refine WP.mono (parityMask_ok hs₂ h0 (by omega_using [h0, hY]) (by omega_using [h0, hD])) fun s₃ ⟨mask₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  refine WP.mono (sel_ok (decide (sv c base s₂ QY % 2 ≠ (word s₂.mem base (c.sl D)).toNat % 2)) c.n hs₃
    (by simpa only [mask, decide_eq_true_eq] using mask₃)
    hY hY hW (sl_mod8 c QY) (sl_mod8 c QY) (sl_mod8 c W0) (Or.inl (Nat.le_refl _))
    (by have := sl_apart c (i := QY) (j := W0) (by decide); omega_using [this])) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  have hM₄ : ModOkA c.MP' size c.C.p s₄.mem base := modP_of hc (by
    rw [O₄.wordsVal (d := c.sl MP) (k := c.n)
      (sl_apart c (i := MP) (j := QY) (by decide)) (by omega_using [hn, hMP]), k₃.mem]
    exact hM₂.val)
  have e₄' : sv c base s₄ QY =
      if sv c base s₂ QY % 2 ≠ (word s₂.mem base (c.sl D)).toNat % 2 then
        sv c base s₂ W0 else sv c base s₂ QY := by
    simpa only [sv, k₃.mem, decide_eq_true_eq] using e₄
  refine ⟨hs₄, hM₄, ?_, ?_, ?_, ?_⟩
  · have k₁' : KeepRegs (clob c.n) s s₁ := ⟨k₁.gpr, k₁.rd, k₁.wr, k₁.sp⟩
    have k₂' : KeepRegs (clob c.n) s₁ s₂ := ⟨k₂.gpr, k₂.rd, k₂.wr, k₂.sp⟩
    exact ((k₁'.trans k₂').trans ((Keeps.regs k₃).mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [clob]))).trans
        (k₄.mono (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                     rcases hr with rfl | rfl <;> simp [clob]))
  · apply unch_same U₁₂
    rw [← k₃.mem]
    exact slot_frame (by simp) (Nat.le_refl _) O₄
  · rw [e₄']
    split
    · exact negLt
    · rw [y₂]
      exact lt₁
  · change Fin.ofNat c.C.p (sv c base s₄ QY) =
      if (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)).val % 2 =
        (word s.mem base (c.sl D)).toNat % 2 then _ else _
    rw [y₂, tag₂, normalVal] at e₄'
    by_cases hm : (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)).val % 2 =
        (word s.mem base (c.sl D)).toNat % 2
    · rw [ite_eq_left hm]
      rw [ite_eq_right (not_not_intro hm)] at e₄'
      rw [e₄']
      exact Fin.ext (Nat.mod_eq_of_lt (toM _ _ _).isLt)
    · rw [ite_eq_right hm]
      rw [ite_eq_left hm] at e₄'
      rw [e₄', negVal, normal]

end VG.Proof.EcKey.Compressed.AArch64

end

end

/-! ### `EcKey.Compressed.AArch64.Check`, which only this module used -/

section

/-! # Check the recovered root's square and parity -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdh.AArch64 (QY QYM R2P W1 W2 W3)
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdh.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)

def checkN : List FOp := [.mul QYM QY R2P, .mul W1 QYM QYM, .sub W3 W1 W2]
abbrev checkSlots : List Nat := [QY, R2P, W2, QYM, W1, W3]

theorem checkOps_eq (c : Cfg) : Impl.EcKey.Compressed.AArch64.checkRootOps c =
    checkN.map (FOp.rename c.sl) := rfl

theorem checkN_run {F : Type} [Lean.Grind.CommRing F] (e : Nat → F) :
    runOps checkN e W3 = (e QY * e R2P) * (e QY * e R2P) - e W2 := by
  simp only [checkN, runOps_cons, runOps_nil, FOp.run, Function.update_apply]
  simp only [QYM, QY, R2P, W1, W2, X, RR, DM, TT, SM, Nat.reduceEqDiff, ↓reduceIte]

theorem checkN_reads : readsOk checkN [QY, R2P, W2] = true := by decide
theorem checkN_slots : ∀ op ∈ checkN, ∀ x ∈ op.out :: op.ins, x ∈ checkSlots := by decide
theorem checkN_out : ∀ op ∈ checkN, op.out ∈ [QYM, W1, W3, TMP] := by decide

theorem raw_r2_mul {c : Cfg} (hc : BaseCfgOk c) (a : Nat) :
    toM c.C.p (2 ^ (64 * c.n)) a *
      toM c.C.p (2 ^ (64 * c.n)) (c.R * c.R % c.C.p) = Fin.ofNat c.C.p a := by
  change toM c.C.p (2 ^ (64 * c.n)) a * toM c.C.p (2 ^ (64 * c.n)) (c.mont c.R) = _
  rw [toM_cmont hc]
  unfold toM
  have hu := mul_rinv (unitMod_pow_two hc.p_odd (64 * c.n))
  change Fin.ofNat c.C.p c.R * rinv c.C.p (2 ^ (64 * c.n)) = 1 at hu
  grind

structure CheckPolyPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (clob c.n) s s'
  unch : Unch base (slW c [QYM, W1, W3, TMP]) s.mem s'.mem
  lt : sv c base s' W3 < c.C.p
  val : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' W3) =
    Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) -
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2)

theorem checkPoly_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkA c.MP' size c.C.p s.mem base)
    (hy : sv c base s QY < c.C.p) (hr : sv c base s W2 < c.C.p)
    (hr2 : sv c base s R2P = c.R * c.R % c.C.p) :
    WP isa (Impl.Weierstrass.AArch64.fprogB c.MP'
      (Impl.EcKey.Compressed.AArch64.checkRootOps c)) s (CheckPolyPost c base s) := by
  have h7 := hc.n10
  have hL : Lay c.MP' size (· ∈ checkSlots.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  have hAl : Aligned c.MP' (· ∈ checkSlots.map c.sl) := ⟨fun x hx => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact sl_mod8 c i, MP'_A c, fun f m h => (hc.call_p f m h).2⟩
  have I : Inv c.MP' base size c.C.p (· ∈ checkSlots.map c.sl) ([QY, R2P, W2].map c.sl)
      (fun o => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base o c.n)) s := by
    refine ⟨hs, hM, ?_, ?_, fun _ _ => rfl⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have sub : ∀ i ∈ [QY, R2P, W2], i ∈ checkSlots := by decide
      exact List.mem_map_of_mem (sub i hi)
    · intro x hx
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact hy
      · show sv c base s R2P < _
        rw [hr2]
        exact Nat.mod_lt _ (by have := hc.p_ge; omega_arith)
      · exact hr
  rw [checkOps_eq]
  refine WP.mono (fprogB_ok hL hAl (unitMod_pow_two hc.p_odd (64 * c.n)) _ I
    (fun op hop x hx => ?_)
    (by
      intro op hop
      apply Low.of_call
      intro f m h x hx
      obtain ⟨op₀, hop₀, rfl⟩ := List.mem_map.mp hop
      have hx' : x ∈ (op₀.out :: op₀.ins).map c.sl := by
        cases op₀ <;> simpa [FOp.rename, FOp.out, FOp.ins] using hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
      have hi' := checkN_slots op₀ hop₀ i hi
      have H : ∀ i ∈ checkSlots, i < 45 ∧ i ≠ TMP := by decide
      exact sl_own_fn c h7 (H i hi').1 (H i hi').2)
    (readsOk_rename c.sl checkN_reads)) fun t ⟨PK, IT⟩ => ?_
  · obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
    have hx' : x ∈ (op₀.out :: op₀.ins).map c.sl := by
      cases op₀ <;> simpa [FOp.rename, FOp.out, FOp.ins] using hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    exact List.mem_map_of_mem (checkN_slots _ h₀ _ hi)
  have hw : c.sl W3 ∈ validAfter (checkN.map (FOp.rename c.sl)) ([QY, R2P, W2].map c.sl) :=
    (mem_validAfter _ _).mpr (Or.inr (by simp [checkN, FOp.rename, FOp.out]))
  have vt := IT.val _ hw
  have H : ∀ op ∈ checkN, op.out ≠ TMP ∧ op.out ≠ 54 ∧ op.out ≠ 61 ∧ op.out ≠ 82 := by decide
  rw [congrFun (runOps_rename c.sl checkN _ fun op hop y h =>
    sl_inj c hc.n0 h (.inr (H op hop).2) (.inl (H op hop).1)) W3, checkN_run] at vt
  refine ⟨PK.scr hs, ⟨PK.gpr, PK.rd, PK.wr, PK.sp⟩, ?_, IT.lt _ hw, ?_⟩
  · apply PK.unch.mono
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hw
      obtain ⟨op, hop, rfl⟩ := List.mem_map.mp ho
      obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
      exact List.mem_map.mpr ⟨op₀.out, checkN_out _ h₀, by rw [FOp.out_rename]; rfl⟩
    · obtain rfl := List.mem_singleton.mp hw
      exact List.mem_map_of_mem (by decide)
  · change toM c.C.p (2 ^ (64 * c.n)) (sv c base t W3) =
      (toM c.C.p (2 ^ (64 * c.n)) (sv c base s QY) *
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s R2P)) *
      (toM c.C.p (2 ^ (64 * c.n)) (sv c base s QY) *
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s R2P)) -
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) at vt
    simpa only [hr2, raw_r2_mul hc] using vt

structure CheckRootPost (c : Cfg) (base : Addr) (P : Prop) [Decidable P] (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (clob c.n) s s'
  unch : Unch base (slW c [QYM, W1, W3, TMP, FLAG]) s.mem s'.mem
  flag : word s'.mem base (c.sl FLAG) = mask
    ((P ∧ Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2)) ∧
      sv c base s QY % 2 = (word s.mem base (c.sl D)).toNat % 2)

theorem checkRoot_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkA c.MP' size c.C.p s.mem base)
    (hy : sv c base s QY < c.C.p) (hr : sv c base s W2 < c.C.p)
    (hr2 : sv c base s R2P = c.R * c.R % c.C.p) {P : Prop} [Decidable P]
    (hf : word s.mem base (c.sl FLAG) = mask P) :
    WP isa (Impl.EcKey.Compressed.AArch64.checkRoot c) s (CheckRootPost c base P s) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hsz : size = 8192 := rfl
  have hF := sl_le c h7 (i := FLAG) (by decide)
  have hW := sl_le c h7 (i := W3) (by decide)
  have hY := sl_le c h7 (i := QY) (by decide)
  have hD := sl_le c h7 (i := D) (by decide)
  change WP isa (.seq
    (Impl.Weierstrass.AArch64.fprogB c.MP' (Impl.EcKey.Compressed.AArch64.checkRootOps c))
    (.block (Impl.EcKey.Compressed.AArch64.checkRootChecks c))) s _
  refine WP.seq (WP.mono (checkPoly_ok hc hs hM hy hr hr2) fun s₁ I => ?_)
  have flag₁ : word s₁.mem base (c.sl FLAG) = mask P := by
    rw [flag_unch I.unch h7 h0 hn (by decide), hf]
  have hz : sv c base s₁ W3 = 0 ↔
      Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) := by
    rw [← toM_eq_zero_iff (unitMod_pow_two hc.p_odd (64 * c.n)) I.lt, I.val]
    constructor <;> intro h <;> grind
  rw [Impl.EcKey.Compressed.AArch64.checkRootChecks, WP.block_append_iff]
  refine WP.mono (checkZero_ok c I.scr h0 hW (by omega_arith) (sl_mod8 c W3) (sl_mod8 c FLAG)) fun s₂ ⟨f₂, k₂, O₂⟩ => ?_
  have hs₂ := I.scr.of_keepRegs k₂ (by decide)
  have flag₂ : word s₂.mem base (c.sl FLAG) = mask
      (P ∧ Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2)) := by
    rw [f₂, flag₁, show wordsVal s₁.mem base (c.sl W3) c.n = sv c base s₁ W3 from rfl, mask_and]
    simp only [mask, hz]
  have y₂ : sv c base s₂ QY = sv c base s QY := by
    rw [sv, sv_flag O₂ h0 h7 hn (by decide) (by decide)]
    exact sv_unch I.unch h7 hn (by decide) (apart_slW (by decide))
  have tag₂ : word s₂.mem base (c.sl D) = word s.mem base (c.sl D) := by
    rw [O₂.word (by have := sl_apart c (i := D) (j := FLAG) (by decide); omega_arith) (by omega_arith)]
    exact I.unch.word (fun w hw => by
      have := (apart_slW (c := c) (by decide : D ∉ [QYM, W1, W3, TMP])) w hw
      omega_arith) (by omega_arith)
  rw [WP.block_append_iff]
  refine WP.mono (parityMask_ok hs₂ h0 (by omega_arith) (by omega_arith)) fun s₃ ⟨mask₃, k₃⟩ => ?_
  rw [y₂, tag₂] at mask₃
  rw [WP.block_append_iff]
  refine WP.mono (invertMask_ok s₃ _ mask₃) fun s₄ ⟨mask₄, k₄⟩ => ?_
  have hs₄ := (hs₂.of_keeps k₃ (by decide)).of_keeps k₄ (by decide)
  refine WP.mono (andFlag_ok c hs₄ (by omega_arith) (sl_mod8 c FLAG)) fun s₅ ⟨flag₅, k₅, O₅⟩ => ?_
  refine ⟨hs₄.of_keepRegs k₅ (by decide), ?_, ?_, ?_⟩
  · exact (((I.keep.trans (k₂.mono (by simp [clob]))).trans
      ((Keeps.regs k₃).mono (by simp [clob]))).trans
      ((Keeps.regs k₄).mono (by simp [clob]))).trans (k₅.mono (by simp [clob]))
  · have U₁ : Unch base (slW c [QYM, W1, W3, TMP, FLAG]) s.mem s₁.mem := I.unch.mono (by
      intro w hw
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact List.mem_map_of_mem (List.mem_append_left [FLAG] hi))
    have U₂ : Unch base (slW c [QYM, W1, W3, TMP, FLAG]) s₁.mem s₄.mem := by
      rw [k₄.mem, k₃.mem]
      exact slot_frame (by simp) (by omega_arith) O₂
    exact unch_same (unch_same U₁ U₂) (slot_frame (by simp) (by omega_arith) O₅)
  · rw [flag₅, k₄.mem, k₃.mem, flag₂, mask₄]
    simp only [not_not]
    exact mask_and _ _

end VG.Proof.EcKey.Compressed.AArch64

end

end

/-! ### `EcKey.Compressed.AArch64.Peer`, which only this module used -/

section

/-! # Compressed tag, canonical x and curve constants -/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/AArch64/TagCheck.lean`, which only this module imported.
section

/-! # Accept precisely 02 and 03 and preserve their parity bit -/

section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Ecdh.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

 theorem tagRead_ok {s : State} {q : Addr} (hq : s.gpr .x6 = q)
    (hin : InRegions (s.rd ++ s.wr) q 1) :
    WP isa (.block [zero7, .ldrb .x1 .x6 0]) s fun t =>
      t.gpr .x1 = (s.mem q).setWidth 64 ∧ t.gpr .x7 = 0 ∧ Keeps [.x1, .x7] s t := by
  have ha : s.gpr .x6 + BitVec.ofNat 64 0 = q := by rw [hq, BitVec.add_zero]
  apply WP.of_runBlock
  simp only [zero7, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Nat.mod_one,
    show 0 < 4096 * 1 by decide, show 16 * 0 < Size.x.bits by decide, and_self, ite_true, Option.bind_some, State.load,
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq,
    reduceCtorEq, ite_false, ha, hin, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [read1_zext, RegUpd.mem_write], rfl, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

 theorem tagBits_ok (s : State) :
    WP isa (.block [.movz .x .x5 1 0, .logic .orr .x .x1 .x1 .x5,
      .movz .x .x5 3 0, .logic .eor .x .x1 .x1 .x5]) s fun t =>
      t.gpr .x1 = (s.gpr .x1 ||| 1) ^^^ 3 ∧ Keeps [.x1, .x5] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show 16 * 0 < Size.x.bits by decide, ite_true, RegUpd.gpr_write,
    BitVec.setWidth_eq, reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

 theorem decompressTag_ok {c : Cfg} {s : State} {base q : Addr}
    (hs : Scr s base size) (hq : s.gpr .x6 = q)
    (hin : InRegions (s.rd ++ s.wr) q 1) (hD : c.sl D + 8 ≤ size) :
    WP isa (.block (Impl.EcKey.Compressed.AArch64.decompressTag c)) s fun t =>
      t.gpr .x2 = mask (s.mem q = 2 ∨ s.mem q = 3) ∧
      word t.mem base (c.sl D) = (s.mem q).setWidth 64 ∧
      KeepRegs [.x1, .x2, .x5, .x7, .x16] s t ∧ Outside base (c.sl D) 8 s.mem t.mem := by
  change WP isa (.block ([zero7, .ldrb .x1 .x6 0] ++ ([st .x1 (c.sl D)] ++
    ([.movz .x .x5 1 0, .logic .orr .x .x1 .x1 .x5, .movz .x .x5 3 0,
      .logic .eor .x .x1 .x1 .x5] ++ Impl.Ecdh.AArch64.Cfg.isZero)))) s _
  rw [WP.block_append_iff]
  refine WP.mono (tagRead_ok hq hin) fun s₁ ⟨v₁, z₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (st_out (hs.of_keeps k₁ (by decide)) hD (sl_mod8 c D) .x1)
    fun s₂ ⟨m₂, k₂, g₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (tagBits_ok s₂) fun s₃ ⟨v₃, k₃⟩ => ?_
  refine WP.mono (isZero_ok s₃ (by rw [k₃.gpr _ (by decide), g₂, z₁]))
    fun s₄ ⟨v₄, k₄⟩ => ?_
  have m₄ : s₄.mem = s.mem.writeW (off base (c.sl D)) ((s.mem q).setWidth 64) := by
    rw [k₄.mem, k₃.mem, m₂, k₁.mem, v₁]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [v₄, v₃, g₂, v₁]
    have key : ∀ b : Byte, ((b.setWidth 64 ||| 1) ^^^ 3 = 0) = (b = 2 ∨ b = 3) := by decide
    simp only [mask, key]
  · rw [m₄, word_writeW_self]
  · exact (((Keeps.regs k₁).mono (by sub_regs)).trans (k₂.mono (by sub_regs))).trans
      (((Keeps.regs k₃).mono (by sub_regs)).trans ((Keeps.regs k₄).mono (by sub_regs)))
  · rw [m₄]
    exact writeW_outside _ _ _ (by have := hs.nowrap; omega)

end VG.Proof.EcKey.Compressed.AArch64
end

end

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdh.AArch64 (R2P BP)
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Ecdh.AArch64

theorem decompressPeer_eq (c : Cfg) : Impl.EcKey.Compressed.AArch64.decompressPeer c =
    setConst c.n (c.sl R2P) (c.R * c.R % c.C.p) ++
    (setConst c.n (c.sl BP) (c.mont c.C.b) ++
    (Impl.EcKey.Compressed.AArch64.decompressTag c ++
    (c.andFlag ++ Impl.Ecdh.AArch64.Cfg.checkLtP c (c.sl E)))) := by
  simp only [Impl.EcKey.Compressed.AArch64.decompressPeer, Impl.Ecdh.AArch64.Cfg.consts,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem decompressPeer_ok {c : Cfg} (hc : BaseCfgOk c) {base q : Addr} {s : State}
    (hs : Scr s base size) (hq : s.gpr .x6 = q)
    (hin : (⟨q, c.C.len + 1⟩ : Region) ∈ s.rd ++ s.wr)
    (hd : Region.Disjoint ⟨q, c.C.len + 1⟩ ⟨base, size⟩)
    (hmp : sv c base s MP = c.C.p) (hf : word s.mem base (c.sl FLAG) = BitVec.allOnes 64) :
    WP isa (.block (Impl.EcKey.Compressed.AArch64.decompressPeer c)) s fun s' =>
      Scr s' base size ∧ KeepRegs [.x1, .x2, .x5, .x7, .x16] s s' ∧
      Unch base (slW c [R2P, BP, D, FLAG]) s.mem s'.mem ∧
      sv c base s' R2P = c.R * c.R % c.C.p ∧ sv c base s' BP = c.mont c.C.b ∧
      word s'.mem base (c.sl D) = (s.mem q).setWidth 64 ∧
      word s'.mem base (c.sl FLAG) = mask ((s.mem q = 2 ∨ s.mem q = 3) ∧ sv c base s E < c.C.p) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hsz : size = 8192 := rfl
  have hR := sl_le c h7 (i := R2P) (by decide)
  have hB := sl_le c h7 (i := BP) (by decide)
  have hD := sl_le c h7 (i := D) (by decide)
  have hE := sl_le c h7 (i := E) (by decide)
  have hM := sl_le c h7 (i := MP) (by decide)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  rw [decompressPeer_eq, WP.block_append_iff]
  refine WP.mono (setConst_ok hs hR (sl_mod8 c R2P) (Nat.lt_trans (Nat.mod_lt _ (by have := hc.p_ge; omega_using [this])) hc.p_lt))
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (setConst_ok hs₁ hB (sl_mod8 c BP) (show c.mont c.C.b < 2 ^ (64 * c.n) from
    Nat.lt_trans (Nat.mod_lt _ (by have := hc.p_ge; omega_using [this])) hc.p_lt)) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have W₂ : Outside base 0 size s.mem s₂.mem :=
    (O₁.mono (Nat.zero_le _) hR).trans (O₂.mono (Nat.zero_le _) hB)
  have q₂ : s₂.mem q = s.mem q := by
    have h := keep_of_disjoint' W₂ hd (by omega_using [hn]) (i := 0) (by omega_using []) (by have := hc.len_hi; omega_using [h7, this])
    simpa only [BitVec.add_zero] using h
  rw [WP.block_append_iff]
  refine WP.mono (decompressTag_ok (c := c) (q := q) hs₂
    (by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), hq])
    (by
      exact ⟨_, by rw [k₂.rd, k₂.wr, k₁.rd, k₁.wr]; exact hin, by
        simpa using Offset.contains_base q (d := 0) (n := 1)
          (by omega_using [] : 0 + 1 ≤ c.C.len + 1) (by decide)⟩) (by omega_using [h0, hD])) fun s₃ ⟨mask₃, tag₃, k₃, O₃⟩ => ?_
  rw [q₂] at mask₃ tag₃
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have U₃ : Unch base (slW c [R2P, BP, D]) s.mem s₃.mem :=
    unch_same (unch_same (slot_frame (by simp) (Nat.le_refl _) O₁)
      (slot_frame (by simp) (Nat.le_refl _) O₂)) (slot_frame (by simp) (by omega_using [h0]) O₃)
  have flag₃ : word s₃.mem base (c.sl FLAG) = BitVec.allOnes 64 := by
    rw [U₃.word (fun w hw => by have := (apart_slW (c := c) (by decide : FLAG ∉ [R2P, BP, D])) w hw; omega_using [h0, this])
      (by omega_using [h0, hn, hF]), hf]
  rw [WP.block_append_iff]
  refine WP.mono (andFlag_ok c hs₃ (by omega_using [h0, hF]) (sl_mod8 c FLAG)) fun s₄ ⟨flag₄, k₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  have U₄ : Unch base (slW c [R2P, BP, D, FLAG]) s.mem s₄.mem :=
    unch_same (U₃.mono (by
      intro w hw
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact List.mem_map_of_mem (List.mem_append_left [FLAG] hi)))
      (slot_frame (by simp) (by omega_using [h0]) O₄)
  have keep₄ {i : Nat} (hi : i < 45) (hm : i ∉ [R2P, BP, D, FLAG]) :
      sv c base s₄ i = sv c base s i := sv_unch U₄ h7 hn hi (apart_slW hm)
  refine WP.mono (checkLtP_ok c hs₄ h0 hE hM (by omega_using [h0, hF]) (sl_mod8 c E) (sl_mod8 c MP) (sl_mod8 c FLAG)) fun s₅ ⟨flag₅, k₅, O₅⟩ => ?_
  refine ⟨hs₄.of_keepRegs k₅ (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((((k₁.mono (by simp)).trans (k₂.mono (by simp))).trans (k₃.mono (by simp))).trans
      (k₄.mono (by simp))).trans (k₅.mono (by sub_regs))
  · exact unch_same U₄ (slot_frame (by simp) (by omega_using [h0]) O₅)
  · rw [sv, sv_flag O₅ h0 h7 hn (by decide) (by decide), sv_flag O₄ h0 h7 hn (by decide) (by decide),
      sv_out (O₃.mono (Nat.le_refl _) (by omega_using [h0] : c.sl D + 8 ≤ c.sl D + 8 * c.n)) h7 hn (by decide) (by decide),
      sv_out O₂ h7 hn (by decide) (by decide)]
    exact e₁
  · rw [sv, sv_flag O₅ h0 h7 hn (by decide) (by decide), sv_flag O₄ h0 h7 hn (by decide) (by decide),
      sv_out (O₃.mono (Nat.le_refl _) (by omega_using [h0] : c.sl D + 8 ≤ c.sl D + 8 * c.n)) h7 hn (by decide) (by decide)]
    exact e₂
  · rw [O₅.word (by have := sl_apart c (i := D) (j := FLAG) (by decide); omega_using [h0, this]) (by omega_using [h0, hn, hD]),
      O₄.word (by have := sl_apart c (i := D) (j := FLAG) (by decide); omega_using [h0, this]) (by omega_using [h0, hn, hD])]
    exact tag₃
  · rw [flag₅, flag₄, flag₃, mask₃, BitVec.allOnes_and,
      show wordsVal s₄.mem base (c.sl E) c.n = sv c base s₄ E from rfl,
      show wordsVal s₄.mem base (c.sl MP) c.n = sv c base s₄ MP from rfl,
      keep₄ (by decide) (by decide), keep₄ (by decide) (by decide), hmp, mask_and]

end VG.Proof.EcKey.Compressed.AArch64

end

end

/-! # Coordinate recovery and final checks preserve the parsed encoding -/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/AArch64/Start.lean`, which only this module imported.
section

/-! # Decode the compressed x coordinate with the existing EC setup -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

structure DecompressPre (c : Cfg) (s : State) : Prop where
  pk : (⟨s.gpr .x1, c.C.len + 1⟩ : Region) ∈ s.rd ++ s.wr
  ws : (⟨s.gpr .x2, size⟩ : Region) ∈ s.wr
  disjoint : Region.Disjoint ⟨s.gpr .x1, c.C.len + 1⟩ ⟨s.gpr .x2, size⟩
  fit : (s.gpr .x2).toNat + size ≤ 2 ^ 64

structure DecompressStart (c : Cfg) (s₀ : State) (g : Reg → BitVec 64) (s : State) : Prop where
  scr : Scr s (s₀.gpr .x2) size
  fixed : Fixed c (s₀.gpr .x2) g s.mem
  original : ∀ r ∈ Cfg.saved.map Prod.fst, g r = s₀.gpr r
  out : s.gpr .x20 = s₀.gpr .x0
  pk : s.gpr .x6 = s₀.gpr .x1
  x : sv c (s₀.gpr .x2) s E = keyX c s₀
  flag : word s.mem (s₀.gpr .x2) (c.sl FLAG) = BitVec.allOnes 64
  outside : Outside (s₀.gpr .x2) 0 size s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem decompressStart_ok {c : Cfg} (hc : BaseCfgOk c) {s₀ : State} (hp : DecompressPre c s₀)
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ g s, DecompressStart c s₀ g s → WP isa rest s Q) :
    WP isa (.seq (.block Impl.EcKey.Compressed.AArch64.args)
      (.seq (.block (c.setupWith none)) rest)) s₀ Q := by
  have hsz : size = 8192 := rfl
  have := hc.len8
  have := hc.len_hi
  have := hc.n10
  refine WP.seq (WP.mono (args_ok s₀) fun s₁ ⟨r8, r9, rcx, rsi, rdx, k₁⟩ => ?_)
  have rw₁ : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [k₁.rd, k₁.wr]
  have hsp : SetupPre c s₁ := by
    have hin : ∀ e, e + 8 ≤ c.C.len →
        InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x1 + 1 + BitVec.ofNat 64 e) 8 := by
      intro e he
      rw [BitVec.add_assoc, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]
      exact ⟨_, hp.pk, Offset.contains_base _ (by omega_using [he]) (by omega_arith)⟩
    have hd : Region.Disjoint ⟨s₀.gpr .x1 + 1, c.C.len⟩ ⟨s₀.gpr .x2, size⟩ :=
      hp.disjoint.sub_left (Offset.sub_base _ (d := 1) (by omega_using []))
    exact ⟨by rw [k₁.wr, r8]; exact hp.ws,
      by rw [rcx, rw₁]; exact hin, by rw [rsi, rw₁]; exact hin,
      by rw [rdx, rw₁]; exact hin, by rw [rsi, r8]; exact hd,
      by rw [rdx, r8]; exact hd, by rw [rcx, r8]; exact hd, by rw [r8]; exact hp.fit⟩
  refine WP.seq (WP.mono (setup_ok hc (hs := none) (.inl rfl) hsp) fun s₂ S => ?_)
  rw [r8] at S
  apply h s₁.gpr s₂
  refine ⟨S.scr, setup_fixed S,
    fun r hr => k₁.gpr r (by revert r; decide), S.x20.trans (k₁.gpr _ (by decide)),
    (S.keep.gpr _ (by decide)).trans r9, ?_, S.flag, ?_, ?_, ?_⟩
  · rw [S.e, shAt_none, Nat.shiftRight_zero, rdx, k₁.mem]
  · rw [← k₁.mem]
    exact S.unch.outside (by simp)
  · rw [S.keep.rd, k₁.rd]
  · rw [S.keep.wr, k₁.wr]

end VG.Proof.EcKey.Compressed.AArch64
end

end

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/AArch64/Rhs.lean`, which only this module imported.
section

/-! # The curve polynomial used by coordinate recovery -/

section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdh.AArch64 (R2P BP QXM QYM QY W0 W1 W2 W3)
open VG.Impl.EcKey.Compressed.AArch64 (rhsOps)
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Ecdh.AArch64

abbrev rhsSlots : List Nat := [QXM, AP, BP, W1, W2, W3]

def rhsTail : List FOp :=
  [.mul W1 QXM QXM, .mul W2 W1 QXM, .mul W1 AP QXM,
    .add W3 W2 W1, .add W2 W3 BP]

theorem rhsTail_run {F : Type} [Lean.Grind.CommRing F] (e : Nat → F) :
    runOps rhsTail e W2 = e QXM * e QXM * e QXM + e AP * e QXM + e BP := by
  simp only [rhsTail, runOps_cons, runOps_nil, FOp.run, Function.update_apply]
  simp only [W1, W2, W3, QXM, AP, BP, TT, SM, RM, XM, EM, Nat.reduceEqDiff, ↓reduceIte]

theorem rhsTail_reads : readsOk rhsTail [QXM, AP, BP] = true := by decide
theorem rhsTail_slots : ∀ op ∈ rhsTail, ∀ x ∈ op.out :: op.ins, x ∈ rhsSlots := by decide
theorem rhsTail_out : ∀ op ∈ rhsTail, op.out ∈ [W1, W2, W3, TMP] := by decide

structure RhsPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  mod : ModOkA c.MP' size c.C.p s'.mem base
  gpr : ∀ r, r ∉ clob c.n → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unch : Unch base (slW c [QXM, W1, W2, W3, TMP]) s.mem s'.mem
  lt : sv c base s' W2 < c.C.p
  val : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' W2) =
    let x := Fin.ofNat c.C.p (sv c base s E)
    x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b

theorem rhs_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkA c.MP' size c.C.p s.mem base)
    (hr2 : sv c base s R2P = c.R * c.R % c.C.p)
    (hap : sv c base s AP = c.mont c.C.a) (hbp : sv c base s BP = c.mont c.C.b) :
    WP isa (Impl.Weierstrass.AArch64.fprogB c.MP' (rhsOps c)) s (RhsPost c base s) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  change WP isa (.seq (VG.Impl.Weierstrass.AArch64.opProg c.MP'
    (.mul (c.sl QXM) (c.sl E) (c.sl R2P)))
    (VG.Impl.Weierstrass.AArch64.fprogB c.MP' (rhsTail.map (FOp.rename c.sl)))) s _
  have hneq : c.sl E ≠ c.sl R2P := by
    intro he
    have := sl_inj c hc.n0 he
    contradiction
  have first : VG.Impl.Weierstrass.AArch64.opProg c.MP' (.mul (c.sl QXM) (c.sl E) (c.sl R2P)) =
      c.mulPP (c.sl QXM) (c.sl E) (c.sl R2P) := by
    unfold VG.Impl.Weierstrass.AArch64.opProg Cfg.mulPP
    cases hh : VG.Impl.Weierstrass.AArch64.Mont.callOf c.MP' with
    | none => simp [VG.Impl.Weierstrass.AArch64.opCode, hneq]
    | some fm => obtain ⟨f, m⟩ := fm; simp [hneq, MP'_n]
  rw [first]
  refine WP.seq (WP.mono (slMulP_ok hc hs hM (o := QXM) (a := E) (b := R2P)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hr2]; exact Nat.mod_lt _ (by have := hc.p_ge; omega_using [this])))
    fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_)
  have hs₁ := k₁.scr hs
  have hM₁ := hM.keepA64 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  have v₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ QXM) = Fin.ofNat c.C.p (sv c base s E) :=
    toM_r2 hpR (by simpa only [hr2, Cfg.R] using e₁)
  have a₁ : sv c base s₁ AP = c.mont c.C.a :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hap
  have b₁ : sv c base s₁ BP = c.mont c.C.b :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hbp
  have hL : Lay c.MP' size (· ∈ rhsSlots.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  have hAl : Aligned c.MP' (· ∈ rhsSlots.map c.sl) := ⟨fun x hx => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact sl_mod8 c i, MP'_A c, fun f m h => (hc.call_p f m h).2⟩
  have I : Inv c.MP' base size c.C.p (· ∈ rhsSlots.map c.sl) ([QXM, AP, BP].map c.sl)
      (fun o => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₁.mem base o c.n)) s₁ := by
    refine ⟨hs₁, hM₁, ?_, ?_, fun _ _ => rfl⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have sub : ∀ i ∈ [QXM, AP, BP], i ∈ rhsSlots := by decide
      exact List.mem_map_of_mem (sub i hi)
    · intro x hx
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact lt₁
      · show sv c base s₁ AP < _
        rw [a₁]
        exact Nat.mod_lt _ (by have := hc.p_ge; omega_using [lt₁])
      · show sv c base s₁ BP < _
        rw [b₁]
        exact Nat.mod_lt _ (by have := hc.p_ge; omega_using [lt₁])
  refine WP.mono (fprogB_ok hL hAl hpR _ I (fun op hop x hx => ?_)
    (by
      intro op hop
      apply Low.of_call
      intro f m h x hx
      obtain ⟨op₀, hop₀, rfl⟩ := List.mem_map.mp hop
      have hx' : x ∈ (op₀.out :: op₀.ins).map c.sl := by
        cases op₀ <;> simpa [FOp.rename, FOp.out, FOp.ins] using hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
      have hi' := rhsTail_slots op₀ hop₀ i hi
      have H : ∀ i ∈ rhsSlots, i < 45 ∧ i ≠ TMP := by decide
      exact sl_own_fn c h7 (H i hi').1 (H i hi').2)
    (readsOk_rename c.sl rhsTail_reads)) fun s₂ ⟨PK, I₂⟩ => ?_
  · obtain ⟨op₀, hop₀, rfl⟩ := List.mem_map.mp hop
    have hx' : x ∈ (op₀.out :: op₀.ins).map c.sl := by
      cases op₀ <;> simpa [FOp.rename, FOp.out, FOp.ins] using hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    exact List.mem_map_of_mem (rhsTail_slots _ hop₀ _ hi)
  have hw : c.sl W2 ∈ validAfter (rhsTail.map (FOp.rename c.sl)) ([QXM, AP, BP].map c.sl) :=
    (mem_validAfter _ _).mpr (Or.inr (by simp [rhsTail, FOp.rename, FOp.out]))
  have v₂ := I₂.val _ hw
  have H : ∀ op ∈ rhsTail, op.out ≠ TMP ∧ op.out ≠ 54 ∧ op.out ≠ 61 ∧ op.out ≠ 82 := by decide
  rw [congrFun (runOps_rename c.sl rhsTail _ fun op hop y h =>
    sl_inj c hc.n0 h (.inr (H op hop).2) (.inl (H op hop).1)) W2, rhsTail_run] at v₂
  have U₁ : Unch base (slW c [QXM, W1, W2, W3, TMP]) s.mem s₁.mem :=
    unch_slots (MP'_n c) rfl k₁.unch (by simp) (by simp)
  have U₂ : Unch base (slW c [QXM, W1, W2, W3, TMP]) s₁.mem s₂.mem := PK.unch.mono fun w hw => by
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hw
      obtain ⟨op, hop, rfl⟩ := List.mem_map.mp ho
      obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
      exact List.mem_map.mpr ⟨op₀.out, List.mem_cons_of_mem _ (rhsTail_out op₀ h₀), by
        rw [FOp.out_rename]; rfl⟩
    · obtain rfl := List.mem_singleton.mp hw
      exact List.mem_map_of_mem (by decide)
  refine ⟨PK.scr hs₁, I₂.mod, fun r hr => (PK.gpr r hr).trans (k₁.gpr r hr),
    PK.rd.trans k₁.rd, PK.wr.trans k₁.wr,
    (U₁.trans U₂).mono (by intro w hw; simpa only [List.mem_append, or_self] using hw), I₂.lt _ hw, ?_⟩
  simpa only [sv, MP'_n, a₁, b₁, toM_cmont hc, v₁] using v₂

end VG.Proof.EcKey.Compressed.AArch64
end

end

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/AArch64/DecompressFront.lean`, which only this module imported.
section

/-! # Prepare the polynomial and retain the compressed input's checks -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Impl.Ecdh.AArch64 (R2P BP QXM W1 W2 W3)
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Ecdh.AArch64

abbrev CompressedPrefix (c : Cfg) (s : State) : Prop :=
  (s.mem (s.gpr .x1) = 2 ∨ s.mem (s.gpr .x1) = 3) ∧ keyX c s < c.C.p

structure DecompressFront (c : Cfg) (s₀ : State) (g : Reg → BitVec 64) (s : State) : Prop where
  scr : Scr s (s₀.gpr .x2) size
  fixed : Fixed c (s₀.gpr .x2) g s.mem
  original : ∀ r ∈ Cfg.saved.map Prod.fst, g r = s₀.gpr r
  out : s.gpr .x20 = s₀.gpr .x0
  x : sv c (s₀.gpr .x2) s E = keyX c s₀
  tag : word s.mem (s₀.gpr .x2) (c.sl D) = (s₀.mem (s₀.gpr .x1)).setWidth 64
  r2 : sv c (s₀.gpr .x2) s R2P = c.R * c.R % c.C.p
  rhs_lt : sv c (s₀.gpr .x2) s W2 < c.C.p
  rhs : toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .x2) s W2) =
    let x := Fin.ofNat c.C.p (keyX c s₀)
    x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b
  flag : word s.mem (s₀.gpr .x2) (c.sl FLAG) = mask (CompressedPrefix c s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- Keep the input checks while a field-arithmetic phase writes other slots. -/
theorem DecompressFront.frame {c : Cfg} (hc : BaseCfgOk c) {s₀ s t : State}
    {g : Reg → BitVec 64} (F : DecompressFront c s₀ g s)
    (K : KeepRegs (powClob c.n) s t) {W : List (Nat × Nat)}
    (U : Unch (s₀.gpr .x2) W s.mem t.mem) (hW : FixedOk c W)
    (ha : ∀ i ∈ [E, D, R2P, W2, FLAG], ∀ w ∈ W,
      c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i) : DecompressFront c s₀ g t := by
  have hn := F.scr.nowrap
  have h0 := hc.n0
  have h7 := hc.n10
  have e {i : Nat} (hi : i < 45) (hm : i ∈ [E, D, R2P, W2, FLAG]) :
      sv c (s₀.gpr .x2) t i = sv c (s₀.gpr .x2) s i := sv_unch U h7 hn hi (ha i hm)
  have ew {i : Nat} (hi : i < 45) (hm : i ∈ [E, D, R2P, W2, FLAG]) :
      word t.mem (s₀.gpr .x2) (c.sl i) = word s.mem (s₀.gpr .x2) (c.sl i) :=
    U.word (fun w hw => by have := ha i hm w hw; omega_using [h0, this])
      (by have := sl_le c h7 hi; omega_using [hn, h0, this])
  refine ⟨F.scr.of_keepRegs K (x0_not_powClob _), F.fixed.unch h7 hn hW U, F.original,
    (K.gpr _ (x20_not_powClob _)).trans F.out,
    (e (by decide) (by simp)).trans F.x, (ew (by decide) (by simp)).trans F.tag,
    (e (by decide) (by simp)).trans F.r2, ?_, ?_, (ew (by decide) (by simp)).trans F.flag,
    K.rd.trans F.rd, K.wr.trans F.wr⟩
  · rw [e (by decide) (by simp)]; exact F.rhs_lt
  · rw [e (by decide) (by simp)]; exact F.rhs

theorem decompressFront_ok {c : Cfg} (hc : BaseCfgOk c) {s₀ : State} (hp : DecompressPre c s₀)
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ g s, DecompressFront c s₀ g s → WP isa rest s Q) :
    WP isa (.seq (.block Impl.EcKey.Compressed.AArch64.args)
      (.seq (.block (c.setupWith none))
      (.seq (.block (Impl.EcKey.Compressed.AArch64.decompressPeer c))
      (.seq (Impl.Weierstrass.AArch64.fprogB c.MP'
        (Impl.EcKey.Compressed.AArch64.rhsOps c)) rest)))) s₀ Q := by
  apply decompressStart_ok hc hp
  intro g s S
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := S.scr.nowrap
  refine WP.seq (WP.mono (decompressPeer_ok hc S.scr S.pk
    (by rw [S.rd, S.wr]; exact hp.pk) hp.disjoint S.fixed.mp S.flag)
    fun s₁ ⟨hs₁, k₁, U₁, r2₁, bp₁, tag₁, flag₁⟩ => ?_)
  have F₁ := S.fixed.unch h7 hn (fixedOk_slW (l := [R2P, BP, D, FLAG]) (by decide)) U₁
  have x₁ : sv c (s₀.gpr .x2) s₁ E = keyX c s₀ :=
    (sv_unch U₁ h7 hn (by decide) (apart_slW (by decide))).trans S.x
  have lead : s.mem (s₀.gpr .x1) = s₀.mem (s₀.gpr .x1) := by
    have e := keep_of_disjoint' S.outside hp.disjoint (by omega_using [hn]) (i := 0) (by omega_using [])
      (by have := hc.len_hi; omega_using [h7, this])
    simpa only [BitVec.add_zero] using e
  rw [lead, S.x] at flag₁
  rw [lead] at tag₁
  refine WP.seq (WP.mono (rhs_ok hc hs₁ (modP_of hc F₁.mp) r2₁ F₁.ap bp₁) fun s₂ R => ?_)
  have F₂ := F₁.unch h7 hn (fixedOk_slW (l := [QXM, W1, W2, W3, TMP]) (by decide)) R.unch
  have eq₂ {i : Nat} (hi : i < 45) (hw : i ∉ [QXM, W1, W2, W3, TMP]) :
      sv c (s₀.gpr .x2) s₂ i = sv c (s₀.gpr .x2) s₁ i :=
    sv_unch R.unch h7 hn hi (apart_slW hw)
  apply h g s₂
  refine ⟨R.scr, F₂, S.original, ?_, (eq₂ (by decide) (by decide)).trans x₁,
    ?_, (eq₂ (by decide) (by decide)).trans r2₁, R.lt, ?_, ?_, ?_, ?_⟩
  · rw [R.gpr _ (by intro h; exact (by decide : VG.AArch64.Reg.x20 ∉ VG.Proof.Mont.AArch64.clobAll) (VG.Proof.Mont.AArch64.mem_clobAll h)), k₁.gpr _ (by decide), S.out]
  · exact (R.unch.word (fun w hw => by
      have := (apart_slW (c := c) (by decide : D ∉ [QXM, W1, W2, W3, TMP])) w hw
      have := hc.n0
      omega_arith) (by have := sl_le c h7 (i := D) (by decide); omega_using [h0, hn, this])).trans tag₁
  · simpa only [x₁] using R.val
  · rw [flag_unch R.unch h7 hc.n0 hn (by decide), flag₁]
  · rw [R.rd, k₁.rd, S.rd]
  · rw [R.wr, k₁.wr, S.wr]

end VG.Proof.EcKey.Compressed.AArch64
end

end

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Impl.Ecdh.AArch64 (QY QYM R2P W0 W1 W2 W3)
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.EcKey.Compressed (chooseRoot)

def keyRhs (c : Cfg) (s : State) : Spec.Weierstrass.Fe c.C :=
  let x := Fin.ofNat c.C.p (keyX c s)
  x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b

def keyRoot (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C) (s : State) :=
  chooseRoot (root (keyRhs c s)) ((s.mem (s.gpr .x1)).toNat % 2)

def CompressedAccept (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C)
    (s : State) : Prop := CompressedPrefix c s ∧
  (keyRoot c root s * keyRoot c root s = keyRhs c s ∧
    (keyRoot c root s).val % 2 = (s.mem (s.gpr .x1)).toNat % 2)

instance (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C) (s : State) :
    Decidable (CompressedAccept c root s) := inferInstanceAs (Decidable (_ ∧ (_ ∧ _)))

structure DecompressChecked (c : Cfg)
    (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C)
    (s₀ : State) (g : Reg → BitVec 64) (s : State) : Prop where
  scr : Scr s (s₀.gpr .x2) size
  saved : Spill.Saved (s₀.gpr .x2) g Cfg.saved s.mem
  original : ∀ r ∈ Cfg.saved.map Prod.fst, g r = s₀.gpr r
  out : s.gpr .x20 = s₀.gpr .x0
  x : sv c (s₀.gpr .x2) s E = keyX c s₀
  y : sv c (s₀.gpr .x2) s QY = (keyRoot c root s₀).val
  flag : word s.mem (s₀.gpr .x2) (c.sl FLAG) = mask (CompressedAccept c root s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem decompressMiddle_ok {c : Cfg} (hc : BaseCfgOk c)
    {root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C} (hroot : CandidateCorrect c root)
    {s₀ s : State} {g : Reg → BitVec 64} (F : DecompressFront c s₀ g s) :
    WP isa (.seq (Impl.EcKey.Compressed.AArch64.rootCandidate c)
      (.seq (Impl.EcKey.Compressed.AArch64.selectRoot c)
        (Impl.EcKey.Compressed.AArch64.checkRoot c))) s (DecompressChecked c root s₀ g) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := F.scr.nowrap
  refine WP.seq (WP.mono (hroot _ s F.scr (modP_of hc F.fixed.mp) F.rhs_lt F.fixed.onep)
    fun s₁ C => ?_)
  have F₁ := F.frame hc C.keep C.unch (candidate_fixed hc) (by
    intro i hi
    have h : ∀ i ∈ [E, D, R2P, W2, FLAG], i < 45 ∧ i ∉ ACC :: candidateSlots := by decide
    exact candidate_apart hc (h i hi).1 (h i hi).2)
  have root₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .x2) s₁ ACC) = root (keyRhs c s₀) := by
    rw [C.val, F.rhs]; rfl
  refine WP.seq (WP.mono (selectRoot_ok hc F₁.scr (modP_of hc F₁.fixed.mp)
    F₁.fixed.one F₁.fixed.zero) fun s₂ S => ?_)
  have F₂ := F₁.frame hc (S.keep.mono (fun _ hr => List.mem_cons_of_mem _ hr)) S.unch
    (fixedOk_slW (l := [QY, W0, TMP]) (by decide)) (by
      intro i hi
      have h : ∀ i ∈ [E, D, R2P, W2, FLAG], i ∉ [QY, W0, TMP] := by decide
      exact apart_slW (h i hi) (by
        have H : ∀ i ∈ [E, D, R2P, W2, FLAG], i < 45 := by decide
        have := H i hi
        omega_using [this]) (by decide))
  have y₂ : Fin.ofNat c.C.p (sv c (s₀.gpr .x2) s₂ QY) = keyRoot c root s₀ := by
    rw [S.val, root₁, F₁.tag]
    simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show
      (s₀.mem (s₀.gpr .x1)).toNat < 2 ^ 64 from Nat.lt_trans (BitVec.isLt _) (by decide))]
    rfl
  have yval₂ : sv c (s₀.gpr .x2) s₂ QY = (keyRoot c root s₀).val := by
    simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt S.lt] using congrArg Fin.val y₂
  refine WP.mono (checkRoot_ok hc F₂.scr (modP_of hc F₂.fixed.mp) S.lt
    F₂.rhs_lt F₂.r2 F₂.flag) fun s₃ K => ?_
  have F₃ := F₂.fixed.unch h7 hn
    (fixedOk_slW (l := [QYM, W1, W3, TMP, FLAG]) (by decide)) K.unch
  have e₃ {i : Nat} (hi : i < 45) (hw : i ∉ [QYM, W1, W3, TMP, FLAG]) :
      sv c (s₀.gpr .x2) s₃ i = sv c (s₀.gpr .x2) s₂ i :=
    sv_unch K.unch h7 hn hi (apart_slW hw)
  refine ⟨K.scr, F₃.saved, F.original, (K.keep.gpr _ (by intro h; exact (by decide : VG.AArch64.Reg.x20 ∉ VG.Proof.Mont.AArch64.clobAll) (VG.Proof.Mont.AArch64.mem_clobAll h))).trans F₂.out,
    (e₃ (by decide) (by decide)).trans F₂.x,
    (e₃ (by decide) (by decide)).trans yval₂, ?_, K.keep.rd.trans F₂.rd, K.keep.wr.trans F₂.wr⟩
  rw [K.flag, y₂, yval₂, F₂.rhs, F₂.tag]
  simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show
    (s₀.mem (s₀.gpr .x1)).toNat < 2 ^ 64 from Nat.lt_trans (BitVec.isLt _) (by decide))]
  simp only [mask, CompressedAccept, keyRhs, and_assoc]

end VG.Proof.EcKey.Compressed.AArch64
