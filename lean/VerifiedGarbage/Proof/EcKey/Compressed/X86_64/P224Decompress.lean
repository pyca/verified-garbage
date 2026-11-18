module

public import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.EcKey.P224
public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.DecompressMain
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.InverseVerified
public import VerifiedGarbage.Spec.EcKey.P224
import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.InverseLit
import VerifiedGarbage.Proof.P224.Sqrt
public import VerifiedGarbage.Impl.EcKey.Compressed.Root
public import VerifiedGarbage.Impl.EcKey.Compressed.X86_64.Decompress
import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Fixed
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Layout
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Weierstrass.X86_64.Pow
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.Ecdsa.X86_64.SharedSlots
import VerifiedGarbage.Proof.Ecdsa.X86_64.Scalar
import VerifiedGarbage.Proof.Weierstrass.Sqrt
import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
import VerifiedGarbage.Proof.Mont.X86_64.Ops
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Weierstrass.X86_64.Fprog
import VerifiedGarbage.Proof.Weierstrass.RootTonelli
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.X86_64.Decompress
meta import VerifiedGarbage.Impl.Ecdsa.P224.X86_64
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.InverseVerified
public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.DecompressContract
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.DecompressContract
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-! ### `EcKey.Compressed.X86_64.DecompressCT`, which only this module used -/

section

/-! # Track the scratch counter through P-224's nested public loops -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64

def decompressT (len : Nat) : VG.X86_64.Taint.T where
  regs := .ofList [.rdi, .rsi, .rdx, .rsp]
  flags := false
  lens := [2 * len + 1, 8192]
  bases := [(.rdx, 1, 0)]

theorem decompress_agree {C : Spec.Weierstrass.Curve}
    {root : Spec.Weierstrass.Fe C → Spec.Weierstrass.Fe C} {s₁ s₂ : State}
    (h₁ : (decompressContract C root).pre s₁) (h₂ : (decompressContract C root).pre s₂)
    (hp : (decompressContract C root).pub s₁ s₂) :
    VG.X86_64.Taint.Agree (decompressT C.len) s₁ s₂ := by
  obtain ⟨hsp, hout, hpk, hws⟩ := hp
  have hr : VG.X86_64.Taint.Agree (Taint.ofRegs [.rdi, .rsi, .rdx, .rsp]) s₁ s₂ := by
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hout
    · exact hpk
    · exact hws
    · exact hsp
  have wf (s : State) (h : (decompressContract C root).pre s) : VG.X86_64.Taint.Wf (decompressT C.len) s := by
    obtain ⟨_, hwr, _, _, hd, _, _, hfit, _⟩ := h
    constructor
    · intro _
      rw [hwr]
      refine ⟨.cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil), ?_, ?_⟩
      · refine .cons ?_ (.cons (by simp) .nil)
        intro r hr
        obtain rfl := List.mem_singleton.mp hr
        exact hd
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · dsimp; omega_using [hfit]
        · change 8192 ≤ 2 ^ 64; decide
    · intro p hp
      obtain rfl := List.mem_singleton.mp hp
      simp only [VG.X86_64.Taint.region, hwr, List.getD_cons_succ, List.getD_cons_zero]
      exact (BitVec.add_zero _).symm

  refine ⟨hr.rf, ?_, wf s₁ h₁, wf s₂ h₂, ?_, ?_, hr.lo, hr.xr⟩
  · intro _
    rw [h₁.2.1, h₂.2.1, hout, hws]
  · intro sl h; cases h
  · intro sl h; cases h

end VG.Proof.EcKey.Compressed.X86_64

end

end

/-! ### `EcKey.Compressed.X86_64.Tonelli`, which only this module used -/

section

/-! ### `EcKey.Compressed.X86_64.TonelliSetup`, which only this module used -/

section

/-! # Initialize P-224's descent from its two computed powers -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Impl.EcKey.Compressed.X86_64 (rootQ)
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

theorem tonelliSetup_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hr : sv c base s T5 < c.C.p) (ht : sv c base s ACC < c.C.p) :
    WP isa (.block (Impl.EcKey.Compressed.X86_64.tonelliSetup c)) s fun t =>
      KeepRegs [.rax] s t ∧ Unch base (slW c [T0, ACC, T1, T2]) s.mem t.mem ∧
      (∀ i ∈ [ACC, T0, T1], sv c base t i < c.C.p) ∧
      word t.mem base (c.sl T2) = BitVec.ofNat 64 95 ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t ACC) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s T5) ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t T0) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t T1) =
        Spec.Weierstrass.pow (Fin.ofNat c.C.p 11) (rootQ c) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := hs.nowrap
  obtain hT0 := sl_le c h7 (i := T0) (by decide)
  obtain hACC := sl_le c h7 (i := ACC) (by decide)
  obtain hT5 := sl_le c h7 (i := T5) (by decide)
  obtain hT1 := sl_le c h7 (i := T1) (by decide)
  obtain hT2 := sl_le c h7 (i := T2) (by decide)
  rw [Impl.EcKey.Compressed.X86_64.tonelliSetup, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (copy_ok c.n hs hT0 hACC
    (by have := sl_apart c (i := T0) (j := ACC) (by decide); omega_using [this])) fun s₁ ⟨v₁, k₁, O₁⟩ => ?_
  obtain hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok c.n hs₁ hACC hT5
    (by have := sl_apart c (i := ACC) (j := T5) (by decide); omega_using [this])) fun s₂ ⟨v₂, k₂, O₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  obtain r₂ : sv c base s₂ ACC = sv c base s T5 := by
    rw [sv, v₂, O₁.wordsVal (sl_apart c (i := T5) (j := T0) (by decide)) (by omega_using [hn, hT5])]
  obtain t₂ : sv c base s₂ T0 = sv c base s ACC := by
    rw [sv, O₂.wordsVal (sl_apart c (i := T0) (j := ACC) (by decide)) (by omega_using [hn, hT0]), v₁]
  let z := Spec.Weierstrass.pow (Fin.ofNat c.C.p 11) (rootQ c)
  have zR : c.mont z.val < 2 ^ (64 * c.n) := Nat.lt_trans
    (Nat.mod_lt _ (by have := hc.p_ge; omega_using [hr])) hc.p_lt
  rw [WP.block_append_iff]
  refine WP.mono (setConst_ok hs₂ hT1 zR) fun s₃ ⟨v₃, k₃, O₃⟩ => ?_
  obtain hs₃ := hs₂.of_keepRegs k₃ (by decide)
  refine WP.mono (setConst_ok (n := 1) hs₃ (by omega_using [h0, hT2] : c.sl T2 + 8 * 1 ≤ size)
    (by decide : 95 < 2 ^ (64 * 1))) fun t ⟨v₄, k₄, O₄⟩ => ?_
  have e₃ {i : Nat} (hi : i < 45) (hw : i ≠ T1) : sv c base s₃ i = sv c base s₂ i :=
    O₃.wordsVal (sl_apart c hw) (by have := sl_le c h7 hi; omega_using [hn, this])
  have e₄ {i : Nat} (hi : i < 45) (hw : i ≠ T2) : sv c base t i = sv c base s₃ i :=
    O₄.wordsVal (by have := sl_apart c hw; omega_using [h0, this]) (by have := sl_le c h7 hi; omega_using [hn, this])
  obtain r₄ : sv c base t ACC = sv c base s T5 := by
    rw [e₄ (by decide) (by decide), e₃ (by decide) (by decide), r₂]
  obtain t₄ : sv c base t T0 = sv c base s ACC := by
    rw [e₄ (by decide) (by decide), e₃ (by decide) (by decide), t₂]
  obtain c₄ : sv c base t T1 = c.mont z.val := by
    rw [e₄ (by decide) (by decide)]; exact v₃
  refine ⟨((k₁.trans k₂).trans k₃).trans k₄, ?_, ?_, ?_, by rw [r₄], by rw [t₄], ?_⟩
  · exact unch_same (unch_same (unch_same (slot_frame (by simp) (Nat.le_refl _) O₁)
      (slot_frame (by simp) (Nat.le_refl _) O₂)) (slot_frame (by simp) (Nat.le_refl _) O₃))
      (slot_frame (by simp) (by omega_using [h0]) O₄)
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · rw [r₄]; exact hr
    · rw [t₄]; exact ht
    · rw [c₄]; exact Nat.mod_lt _ (by have := hc.p_ge; omega_using [hr])
  · apply BitVec.eq_of_toNat_eq
    simpa only [wordsVal, Nat.mul_zero, Nat.add_zero, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by decide : 95 < 2 ^ 64)] using v₄
  · rw [c₄, toM_cmont hc]
    exact Fin.ext (Nat.mod_eq_of_lt z.isLt)

end VG.Proof.EcKey.Compressed.X86_64

end

end

/-! ### `EcKey.Compressed.X86_64.DescentRound`, which only this module used -/

section

/-! ### `EcKey.Compressed.X86_64.Counter`, which only this module used -/

section

/-! # P-224's descent counter in the scratch buffer -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Ecdsa.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

theorem loadRbx_ok {s : State} {base : Addr} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) :
    WP isa (.block [.mov .rbx (.mem (sc d))]) s fun s' =>
      s'.gpr .rbx = word s.mem base d ∧ Keeps [.rbx] s s' := by
  exact WP.mono (movMem_ok hs .rbx hd) fun _ ⟨h, _, k⟩ => ⟨h, k⟩

theorem storeRbx_ok {s : State} {base : Addr} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) :
    WP isa (.block [.store (sc d) .rbx]) s fun s' =>
      word s'.mem base d = s.gpr .rbx ∧ KeepRegs [] s s' ∧
      Outside base d 8 s.mem s'.mem := by
  refine WP.mono (storeReg_ok hs .rbx hd) fun t ⟨hm, _, _, k⟩ => ?_
  refine ⟨?_, k, ?_⟩
  · rw [hm, word_writeW_self]
  · rw [hm]
    exact writeW_outside _ _ _ (by have := hs.nowrap; omega_using [hd, this])

theorem descentCounter_ok {c : Cfg} {base : Addr} {s : State} {j : Nat}
    (hs : Scr s base size) (hd : c.sl T2 + 8 ≤ size)
    (hj : 1 ≤ j) (hj' : j < 2 ^ 64)
    (hword : word s.mem base (c.sl T2) = BitVec.ofNat 64 j) :
    WP isa (.block (Impl.EcKey.Compressed.X86_64.descentCounter c)) s fun s' =>
      word s'.mem base (c.sl T2) = BitVec.ofNat 64 (j - 1) ∧
      s'.zf = some (decide (j - 1 = 0)) ∧
      KeepRegs [.rbx] s s' ∧ Outside base (c.sl T2) 8 s.mem s'.mem := by
  change WP isa (.block ([.mov .rbx (.mem (sc (c.sl T2)))] ++
    ([.alu .sub .rbx (.imm 1)] ++ ([.store (sc (c.sl T2)) .rbx] ++
    [.alu .test .rbx (.reg .rbx)])))) s _
  rw [WP.block_append_iff]
  refine WP.mono (loadRbx_ok hs hd) fun s₁ ⟨hb₁, k₁⟩ => ?_
  rw [hword] at hb₁
  rw [WP.block_append_iff]
  refine WP.mono (decRbx_ok s₁ hj hj' hb₁) fun s₂ ⟨hb₂, k₂⟩ => ?_
  obtain hs₂ := (hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (storeRbx_ok hs₂ hd) fun s₃ ⟨hw₃, k₃, O₃⟩ => ?_
  refine WP.mono (testRbx_ok s₃ (j := j - 1) (by omega_using [hj']) (by rw [k₃.gpr _ (by simp), hb₂])) fun s₄ ⟨hz₄, k₄⟩ => ?_
  refine ⟨by rw [k₄.2.1, hw₃, hb₂], hz₄,
    (((Keeps.regs k₁).trans (Keeps.regs k₂)).trans (k₃.mono (by simp))).trans
      ((Keeps.regs k₄).mono (by simp)), ?_⟩
  rw [k₄.2.1]
  simpa only [k₂.2.1, k₁.2.1] using O₃

end VG.Proof.EcKey.Compressed.X86_64

end

end

/-! # One machine round refines the functional P-224 root descent -/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86_64/Square.lean`, which only this module imported.
section

/-! # Repeated squaring for the P-224 root descent

The backwards invariant `current^(2^remaining) = original^(2^count)`
avoids any assumption about the input being a square or nonzero.
-/

section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont.X86_64 VG.Proof.Mont
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

structure SquareInv (c : Cfg) (base : Addr) (count : Nat) (s₀ s : State) (j : Nat) : Prop where
  scr : Scr s base size
  mod : ModOkW c.MP' size c.C.p s.mem base
  rbx : s.gpr .rbx = BitVec.ofNat 64 j
  keep : KeepRegs (powClob c.n) s₀ s
  unch : Unch base (slW c [T3, TMP]) s₀.mem s.mem
  lt : sv c base s T3 < c.C.p
  val : toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) ^ (2 ^ j) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s₀ T3) ^ (2 ^ count)

theorem squareStep_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {count j : Nat}
    (hj : 1 ≤ j) (hcount : count < 2 ^ 31) (hjc : j ≤ count) {s₀ s : State}
    (I : SquareInv c base count s₀ s j) :
    WP isa (Impl.EcKey.Compressed.X86_64.squareStep c T3) s fun s' =>
      SquareInv c base count s₀ s' (j - 1) ∧ s'.zf = some (decide (j - 1 = 0)) := by
  have h7 := hc.n10
  have hn := I.scr.nowrap
  rw [Impl.EcKey.Compressed.X86_64.squareStep, WP.block_append_iff]
  refine WP.mono (slMul_ok (MP'_n c) (MP'_tmp c) (MP'_mo c) h7 I.scr I.mod
    (o := T3) (a := T3) (b := T3) (by decide) (by decide) (by decide) (by decide) I.lt)
    fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_
  obtain hs₁ := k₁.scr I.scr
  obtain hm₁ := I.mod.keep (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  obtain hb₁ : s₁.gpr .rbx = BitVec.ofNat 64 j :=
    (k₁.gpr _ (rbx_not_clob c.n)).trans I.rbx
  obtain U₁ : Unch base (slW c [T3, TMP]) s.mem s₁.mem :=
    unch_slots (MP'_n c) rfl k₁.unch (by simp) (by simp)
  obtain v₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ T3) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) ^ 2 := by
    rw [toM_mul (unitMod_pow_two hc.p_odd (64 * c.n)) e₁, Lean.Grind.Semiring.pow_two]
  rw [show ([.alu .sub .rbx (.imm 1), .alu .test .rbx (.reg .rbx)] : List Instr) =
      [.alu .sub .rbx (.imm 1)] ++ [.alu .test .rbx (.reg .rbx)] from rfl,
    WP.block_append_iff]
  refine WP.mono (decRbx_ok s₁ hj (by omega) hb₁) fun s₂ ⟨hb₂, k₂⟩ => ?_
  refine WP.mono (testRbx_ok s₂ (by omega) hb₂) fun s₃ ⟨hz₃, k₃⟩ => ?_
  obtain m₃ : s₃.mem = s₁.mem := k₃.2.1.trans k₂.2.1
  refine ⟨⟨(hs₁.of_keeps k₂ (by decide)).of_keeps k₃ (by decide), by rw [m₃]; exact hm₁,
    by rw [k₃.1 _ (by decide), hb₂], ?_, ?_, by rw [sv, m₃]; exact lt₁, ?_⟩, hz₃⟩
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · have hr' : r ∉ clob c.n := fun h => hr (List.mem_cons_of_mem _ h)
      obtain hrb : r ≠ .rbx := fun h => hr (h ▸ List.mem_cons_self ..)
      rw [k₃.1 _ (by simp), k₂.1 _ (by simp [hrb]), k₁.gpr r hr', I.keep.gpr r hr]
    · rw [k₃.2.2.1, k₂.2.2.1, k₁.rd, I.keep.rd]
    · rw [k₃.2.2.2, k₂.2.2.2, k₁.wr, I.keep.wr]
  · rw [m₃]
    exact (I.unch.trans U₁).mono (by intro w hw; simpa only [List.mem_append, or_self] using hw)
  · rw [sv, m₃]
    change toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ T3) ^ (2 ^ (j - 1)) = _
    rw [v₁, pow_mul_exponents,
      show 2 * 2 ^ (j - 1) = 2 ^ j by
        calc
          2 * 2 ^ (j - 1) = 2 ^ (j - 1) * 2 := Nat.mul_comm _ _
          _ = 2 ^ (j - 1 + 1) := (Nat.pow_succ _ _).symm
          _ = 2 ^ j := by rw [Nat.sub_add_cancel hj]]
    exact I.val

theorem squareLoop_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {count : Nat} {s : State}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hlt : sv c base s T3 < c.C.p) (hb : s.gpr .rbx = BitVec.ofNat 64 count)
    (hcount : count < 2 ^ 31) (hpos : 1 ≤ count) :
    WP isa (.loop (Impl.EcKey.Compressed.X86_64.squareStep c T3) .ne) s fun s' =>
      KeepRegs (powClob c.n) s s' ∧ Unch base (slW c [T3, TMP]) s.mem s'.mem ∧
      sv c base s' T3 < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' T3) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) ^ (2 ^ count) := by
  apply countLoop_ok (Inv := fun j t => SquareInv c base count s t j)
    (fun j t hj hjc hi => squareStep_ok hc hj hcount hjc hi) (n := count)
  · intro t I
    refine ⟨I.keep, I.unch, I.lt, ?_⟩
    simpa only [Nat.pow_zero, Lean.Grind.Semiring.pow_one] using I.val
  · exact hpos
  · exact ⟨hs, hM, hb, ⟨fun _ _ => rfl, rfl, rfl⟩, Unch.refl _ _ _, hlt, rfl⟩

theorem squarePower_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {count : Nat} {s : State}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hlt : sv c base s T3 < c.C.p) (hb : s.gpr .rbx = BitVec.ofNat 64 count)
    (hcount : count < 2 ^ 31) :
    WP isa (Impl.EcKey.Compressed.X86_64.squarePower c) s fun s' =>
      KeepRegs (powClob c.n) s s' ∧ Unch base (slW c [T3, TMP]) s.mem s'.mem ∧
      sv c base s' T3 < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' T3) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) ^ (2 ^ count) := by
  rw [Impl.EcKey.Compressed.X86_64.squarePower]
  refine WP.seq (WP.mono (testRbx_ok s (by omega) hb) fun s₁ ⟨hz₁, k₁⟩ => ?_)
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.ite (decide (count = 0)) hz₁ (fun hz => ?_) (fun hn => ?_)
  · have hn : count = 0 := of_decide_eq_true hz
    apply WP.block_nil
    refine ⟨(Keeps.regs k₁).mono (by simp), ?_, ?_, ?_⟩
    · rw [k₁.2.1]
      exact Unch.refl _ _ _
    · rw [sv, k₁.2.1]
      exact hlt
    · rw [sv, k₁.2.1, hn, Nat.pow_zero, Lean.Grind.Semiring.pow_one]
  · have hn : count ≠ 0 := of_decide_eq_false hn
    refine WP.mono (squareLoop_ok hc hs₁ (k₁.2.1 ▸ hM) (by rw [sv, k₁.2.1]; exact hlt)
      (by rw [k₁.1 _ (by decide), hb]) hcount (by omega)) fun t ⟨kt, Ut, lt, vt⟩ => ?_
    refine ⟨((Keeps.regs k₁).mono (by simp)).trans kt, ?_, lt, ?_⟩
    · rw [← k₁.2.1]
      exact Ut
    · simpa only [sv, k₁.2.1] using vt

end VG.Proof.EcKey.Compressed.X86_64
end

end

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86_64/DescentPower.lean`, which only this module imported.
section

/-! # The tested power in one P-224 descent round -/

section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

theorem descentPower_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State} {j : Nat}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hlt : sv c base s T0 < c.C.p) (hj : 1 ≤ j) (hj' : j < 2 ^ 31)
    (hword : word s.mem base (c.sl T2) = BitVec.ofNat 64 j) :
    WP isa (Impl.EcKey.Compressed.X86_64.descentPower c).inline s fun s' =>
      KeepRegs (powClob c.n) s s' ∧ Unch base (slW c [T3, TMP]) s.mem s'.mem ∧
      sv c base s' T3 < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' T3) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s T0) ^ (2 ^ (j - 1)) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := hs.nowrap
  obtain h3 := sl_le c h7 (i := T3) (by decide)
  obtain h2 := sl_le c h7 (i := T2) (by decide)
  change WP isa (.seq (.block (copy c.n (c.sl T3) (c.sl T0) ++
    ([.mov .rbx (.mem (sc (c.sl T2)))] ++ [.alu .sub .rbx (.imm 1)])))
    (Impl.EcKey.Compressed.X86_64.squarePower c)) s _
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok c.n hs h3 (sl_le c h7 (by decide))
    (by have := sl_apart c (i := T3) (j := T0) (by decide); omega)) fun s₁ ⟨v₁, k₁, O₁⟩ => ?_
  obtain hs₁ := hs.of_keepRegs k₁ (by decide)
  obtain U₁ : Unch base (slW c [T3, TMP]) s.mem s₁.mem := slot_frame (by simp) (Nat.le_refl _) O₁
  obtain w₁ : word s₁.mem base (c.sl T2) = BitVec.ofNat 64 j := by
    rw [O₁.word (by have := sl_apart c (i := T2) (j := T3) (by decide); omega) (by omega), hword]
  rw [WP.block_append_iff]
  refine WP.mono (loadRbx_ok hs₁ (d := c.sl T2) (by omega)) fun s₂ ⟨hb₂, k₂⟩ => ?_
  rw [w₁] at hb₂
  refine WP.mono (decRbx_ok s₂ hj (by omega) hb₂) fun s₃ ⟨hb₃, k₃⟩ => ?_
  obtain hs₃ := (hs₁.of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
  obtain m₃ : s₃.mem = s₁.mem := k₃.2.1.trans k₂.2.1
  obtain M₃ : ModOkW c.MP' size c.C.p s₃.mem base := modP_of hc (by
    rw [m₃, O₁.wordsVal (sl_apart c (i := MP) (j := T3) (by decide)) (by
      have := sl_le c h7 (i := MP) (by decide); omega)]
    exact hM.val)
  refine WP.mono (squarePower_ok hc hs₃ M₃
    (by change wordsVal _ _ _ _ < _; rw [m₃, v₁]; exact hlt) hb₃ (by omega))
    fun t ⟨kt, Ut, lt, vt⟩ => ?_
  refine ⟨?_, ?_, lt, ?_⟩
  · have K₁ : KeepRegs (powClob c.n) s s₁ := k₁.mono (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      simp [powClob, clob])
    exact ((K₁.trans ((Keeps.regs k₂).mono (by simp [powClob]))).trans
      ((Keeps.regs k₃).mono (by simp [powClob]))).trans kt
  · rw [m₃] at Ut
    exact unch_same U₁ Ut
  · change toM c.C.p (2 ^ (64 * c.n)) (sv c base t T3) =
      toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl T0) c.n) ^ (2 ^ (j - 1))
    simpa only [sv, m₃, v₁] using vt

end VG.Proof.EcKey.Compressed.X86_64
end

end

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86_64/DescentChoose.lean`, which only this module imported.
section

/-! # Select the correction factor of the P-224 descent -/

section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Impl.Ecdh.X86_64 (W0)
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64 VG.Proof.Ecdh.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

theorem descentChoose_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (ht : sv c base s T3 < c.C.p) (hcval : sv c base s T1 < c.C.p)
    (hOne : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) :
    WP isa (.block (Impl.EcKey.Compressed.X86_64.descentChoose c)) s fun t =>
      KeepRegs (clob c.n) s t ∧ Unch base (slW c [W0, T4, TMP]) s.mem t.mem ∧
      sv c base t T4 < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t T4) =
        if toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) = 1 then 1
        else toM c.C.p (2 ^ (64 * c.n)) (sv c base s T1) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := hs.nowrap
  have hp := hc.p_ge
  obtain hW := sl_le c h7 (i := W0) (by decide)
  obtain hT := sl_le c h7 (i := T3) (by decide)
  obtain hC := sl_le c h7 (i := T1) (by decide)
  obtain hB := sl_le c h7 (i := T4) (by decide)
  obtain hO := sl_le c h7 (i := ONEP) (by decide)
  obtain hOlt : sv c base s ONEP < c.C.p := by rw [hOne]; exact Nat.mod_lt _ (by omega)
  obtain ha := slots_apart (MP'_n c) (MP'_tmp c) (MP'_mo c)
    (o := W0) (a := T3) (b := ONEP) (by decide)
  rw [Impl.EcKey.Compressed.X86_64.descentChoose, List.append_assoc, List.append_assoc,
    WP.block_append_iff]
  refine WP.mono (sub_ok hs hM hW hT hO ha.1 ha.2.1 ha.2.2.1 ha.2.2.2 ht hOlt)
    fun s₁ ⟨k₁, e₁⟩ => ?_
  change sv c base s₁ W0 = (sv c base s T3 + c.C.p - sv c base s ONEP) % c.C.p at e₁
  obtain hs₁ := k₁.scr hs
  obtain lt₁ : sv c base s₁ W0 < c.C.p := by
    rw [e₁]; exact Nat.mod_lt _ (by omega)
  obtain v₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ W0) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) - 1 := by
    rw [e₁, toM_sub (by omega), hOne, toM_one (unitMod_pow_two hc.p_odd (64 * c.n))]
  obtain z₁ : sv c base s₁ W0 = 0 ↔ toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) = 1 := by
    rw [← toM_eq_zero_iff (unitMod_pow_two hc.p_odd (64 * c.n)) lt₁, v₁]
    constructor <;> intro h <;> grind
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok c hs₁ h0 hW) fun s₂ ⟨mask₂, k₂⟩ => ?_
  simp only [mask, show wordsVal s₁.mem base (c.sl W0) c.n = sv c base s₁ W0 from rfl, z₁] at mask₂
  rw [WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov .rcx (.reg .rdx)]) s₂ (fun s₃ =>
      s₃.gpr .rcx = s₂.gpr .rdx ∧ Keeps [.rcx] s₂ s₃) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
      RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₃ ⟨m₃, k₃⟩ => ?_
  obtain hs₃ := (hs₁.of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
  refine WP.mono (sel_ok (decide (toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) = 1)) c.n hs₃
    (by rw [m₃, mask₂]; simp only [decide_eq_true_eq]) hB hC hO
    (by have := sl_apart c (i := T4) (j := T1) (by decide); omega)
    (by have := sl_apart c (i := T4) (j := ONEP) (by decide); omega))
    fun t ⟨v₄, k₄, O₄⟩ => ?_
  obtain mem₃ : s₃.mem = s₁.mem := k₃.2.1.trans k₂.2.1
  obtain C₃ : sv c base s₃ T1 = sv c base s T1 := by
    rw [sv, mem₃]; exact sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)
  obtain O₃ : sv c base s₃ ONEP = sv c base s ONEP := by
    rw [sv, mem₃]; exact sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)
  change sv c base t T4 = _ at v₄
  simp only [decide_eq_true_eq] at v₄
  change sv c base t T4 = if _ then sv c base s₃ ONEP else sv c base s₃ T1 at v₄
  rw [C₃, O₃] at v₄
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (((⟨k₁.gpr, k₁.rd, k₁.wr⟩ : KeepRegs (clob c.n) s s₁).trans
      ((Keeps.regs k₂).mono (by intro r hr; obtain rfl := List.mem_singleton.mp hr; simp [clob]))).trans
      ((Keeps.regs k₃).mono (by intro r hr; obtain rfl := List.mem_singleton.mp hr; simp [clob]))).trans (k₄.mono (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp [clob]))
  · have U₁ : Unch base (slW c [W0, T4, TMP]) s.mem s₁.mem :=
      unch_slots (MP'_n c) rfl k₁.unch (by simp) (by simp)
    apply unch_same U₁
    rw [← mem₃]
    exact slot_frame (by simp) (Nat.le_refl _) O₄
  · rw [v₄]; split
    · exact hOlt
    · exact hcval
  · rw [v₄]; split
    · rw [hOne, toM_one (unitMod_pow_two hc.p_odd (64 * c.n))]
    · rfl

end VG.Proof.EcKey.Compressed.X86_64
end

end

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86_64/DescentUpdate.lean`, which only this module imported.
section

/-! # The field updates in one P-224 descent round -/

section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Weierstrass
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

def descentN : List FOp :=
  [.mul ACC ACC T4, .mul T4 T4 T4, .mul T0 T0 T4, .mul T1 T1 T1]
abbrev descentFields : List Nat := [ACC, T0, T1, T4]
abbrev descentWritten : List Nat := [ACC, T0, T1, T4, TMP]

theorem descentOps_eq (c : Cfg) : Impl.EcKey.Compressed.X86_64.descentOps c =
    descentN.map (FOp.rename c.sl) := rfl

theorem descentN_run {F : Type} [Lean.Grind.CommRing F] (e : Nat → F) :
    runOps descentN e ACC = e ACC * e T4 ∧
    runOps descentN e T0 = e T0 * (e T4 * e T4) ∧
    runOps descentN e T1 = e T1 * e T1 := by
  simp only [descentN, runOps_cons, runOps_nil, FOp.run, Function.update_apply]
  simp only [ACC, T0, T1, T4, Nat.reduceEqDiff, ↓reduceIte, and_self]

theorem descentN_reads : readsOk descentN descentFields = true := by decide
theorem descentN_slots : ∀ op ∈ descentN, ∀ x ∈ op.out :: op.ins, x ∈ descentFields := by decide
theorem descentN_out : ∀ op ∈ descentN, op.out ∈ descentWritten := by decide

structure DescentUpdatePost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (clob c.n) s s'
  unch : Unch base (slW c descentWritten) s.mem s'.mem
  lt : ∀ i ∈ [ACC, T0, T1], sv c base s' i < c.C.p
  r : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s T4)
  t : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' T0) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s T0) *
      (toM c.C.p (2 ^ (64 * c.n)) (sv c base s T4) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s T4))
  c : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' T1) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s T1) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s T1)

theorem descentUpdate_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hlt : ∀ i ∈ descentFields, sv c base s i < c.C.p) :
    WP isa (Impl.Weierstrass.X86_64.fprogB c.MP'
      (Impl.EcKey.Compressed.X86_64.descentOps c)).inline s (DescentUpdatePost c base s) := by
  have h7 := hc.n10
  obtain hL : Lay c.MP' size (· ∈ descentFields.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  obtain I : Inv c.MP' base size c.C.p (· ∈ descentFields.map c.sl) (descentFields.map c.sl)
      (fun o => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base o c.n)) s := by
    refine ⟨hs, hM, fun _ h => h, ?_, fun _ _ => rfl⟩
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact hlt i hi
  rw [descentOps_eq]
  refine WP.mono (fprogB_ok hL (unitMod_pow_two hc.p_odd (64 * c.n)) _ I
    (fun op hop x hx => ?_) (readsOk_rename c.sl descentN_reads)) fun t ⟨PK, IT⟩ => ?_
  · obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
    obtain hx' : x ∈ (op₀.out :: op₀.ins).map c.sl := by
      cases op₀ <;> simpa [FOp.rename, FOp.out, FOp.ins] using hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    exact List.mem_map_of_mem (descentN_slots _ h₀ _ hi)
  have hw {i : Nat} (hi : i ∈ [ACC, T0, T1]) :
      c.sl i ∈ validAfter (descentN.map (FOp.rename c.sl)) (descentFields.map c.sl) := by
    apply (mem_validAfter _ _).mpr
    exact Or.inl (List.mem_map_of_mem (by
      obtain sub : ∀ i ∈ [ACC, T0, T1], i ∈ descentFields := by decide
      exact sub i hi))
  have val {i : Nat} (hi : i ∈ [ACC, T0, T1]) := IT.val _ (hw hi)
  obtain vr := val (i := ACC) (by simp)
  obtain vt := val (i := T0) (by simp)
  obtain vc := val (i := T1) (by simp)
  rw [congrFun (runOps_rename c.sl descentN _ fun _ _ y h => sl_inj c hc.n0 h) ACC,
    (descentN_run _).1] at vr
  rw [congrFun (runOps_rename c.sl descentN _ fun _ _ y h => sl_inj c hc.n0 h) T0,
    (descentN_run _).2.1] at vt
  rw [congrFun (runOps_rename c.sl descentN _ fun _ _ y h => sl_inj c hc.n0 h) T1,
    (descentN_run _).2.2] at vc
  refine ⟨PK.scr hs, ⟨PK.gpr, PK.rd, PK.wr⟩, ?_, fun i hi => IT.lt _ (hw hi), vr, vt, vc⟩
  apply PK.unch.mono
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hw
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp ho
    obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
    exact List.mem_map.mpr ⟨op₀.out, descentN_out _ h₀, by rw [FOp.out_rename]; rfl⟩
  · obtain rfl := List.mem_singleton.mp hw
    exact List.mem_map_of_mem (by decide)

end VG.Proof.EcKey.Compressed.X86_64
end

end

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Impl.Ecdh.X86_64 (W0)
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Impl.EcKey.Compressed (rootDescent)

def roundSlots : List Nat := [T3, W0, T4, TMP, ACC, T0, T1, T2]

abbrev fieldAt (c : Cfg) (base : Addr) (s : State) (i : Nat) :=
  toM c.C.p (2 ^ (64 * c.n)) (sv c base s i)

structure DescentRoundPost (c : Cfg) (base : Addr) (j : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (powClob c.n) s s'
  unch : Unch base (slW c roundSlots) s.mem s'.mem
  lt : ∀ i ∈ [ACC, T0, T1], sv c base s' i < c.C.p
  counter : word s'.mem base (c.sl T2) = BitVec.ofNat 64 (j - 1)
  zf : s'.zf = some (decide (j - 1 = 0))
  descent : rootDescent (j - 1) (fieldAt c base s' ACC) (fieldAt c base s' T0) (fieldAt c base s' T1) =
    rootDescent j (fieldAt c base s ACC) (fieldAt c base s T0) (fieldAt c base s T1)

theorem descentRound_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State} {j : Nat}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hlt : ∀ i ∈ [ACC, T0, T1], sv c base s i < c.C.p)
    (hOne : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p)
    (hj : 1 ≤ j) (hj' : j < 2 ^ 31)
    (hword : word s.mem base (c.sl T2) = BitVec.ofNat 64 j) :
    WP isa (Impl.EcKey.Compressed.X86_64.descentRound c).inline s (DescentRoundPost c base j s) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := hs.nowrap
  change WP isa (.seq (Impl.EcKey.Compressed.X86_64.descentPower c).inline
    (.seq (.block (Impl.EcKey.Compressed.X86_64.descentChoose c))
      (.seq (Impl.Weierstrass.X86_64.fprogB c.MP' (Impl.EcKey.Compressed.X86_64.descentOps c)).inline
        (.block (Impl.EcKey.Compressed.X86_64.descentCounter c))))) s _
  refine WP.seq (WP.mono (descentPower_ok hc hs hM (hlt _ (by simp)) hj hj' hword)
    fun s₁ ⟨k₁, U₁, lt₁, v₁⟩ => ?_)
  obtain hs₁ := hs.of_keepRegs k₁ (rdi_not_powClob _)
  have e₁ {i : Nat} (hi : i < 45) (hw : i ∉ [T3, TMP]) : sv c base s₁ i = sv c base s i :=
    sv_unch U₁ h7 hn hi (apart_slW hw)
  obtain M₁ : ModOkW c.MP' size c.C.p s₁.mem base := modP_of hc (by
    change sv c base s₁ MP = _
    rw [e₁ (by decide) (by decide)]; exact hM.val)
  refine WP.seq (WP.mono (descentChoose_ok hc hs₁ M₁ lt₁
    (by rw [e₁ (by decide) (by decide)]; exact hlt _ (by simp))
    (by rw [e₁ (by decide) (by decide)]; exact hOne)) fun s₂ ⟨k₂, U₂, lt₂, v₂⟩ => ?_)
  obtain hs₂ := hs₁.of_keepRegs k₂ (rdi_not_clob _)
  have e₂ {i : Nat} (hi : i < 45) (hw : i ∉ [W0, T4, TMP]) : sv c base s₂ i = sv c base s₁ i :=
    sv_unch U₂ h7 hn hi (apart_slW hw)
  obtain M₂ : ModOkW c.MP' size c.C.p s₂.mem base := modP_of hc (by
    change sv c base s₂ MP = _
    rw [e₂ (by decide) (by decide)]; exact M₁.val)
  obtain b₂ : fieldAt c base s₂ T4 =
      if fieldAt c base s T0 ^ (2 ^ (j - 1)) = 1 then 1 else fieldAt c base s T1 := by
    unfold fieldAt
    rw [v₂, v₁, e₁ (by decide) (by decide)]
  refine WP.seq (WP.mono (descentUpdate_ok hc hs₂ M₂ (by
    intro i hi
    obtain sub : ∀ i ∈ descentFields, i ∈ [ACC, T0, T1] ∨ i = T4 := by decide
    rcases sub i hi with h | rfl
    · have hi45 : i < 45 := (by decide : ∀ i ∈ [ACC, T0, T1], i < 45) i h
      obtain hn₁ : i ∉ [T3, TMP] := (by decide : ∀ i ∈ [ACC, T0, T1], i ∉ [T3, TMP]) i h
      obtain hn₂ : i ∉ [W0, T4, TMP] := (by decide : ∀ i ∈ [ACC, T0, T1], i ∉ [W0, T4, TMP]) i h
      rw [e₂ hi45 hn₂, e₁ hi45 hn₁]; exact hlt i h
    · exact lt₂)) fun s₃ V => ?_)
  obtain U₁₂ := unch_same (slots_widen U₁ (by decide : ∀ i ∈ [T3, TMP], i ∈ roundSlots))
    (slots_widen U₂ (by decide : ∀ i ∈ [W0, T4, TMP], i ∈ roundSlots))
  obtain U₁₂₃ := unch_same U₁₂ (slots_widen V.unch (by decide : ∀ i ∈ descentWritten, i ∈ roundSlots))
  obtain w₃ : word s₃.mem base (c.sl T2) = BitVec.ofNat 64 j := by
    obtain U : Unch base (slW c [T3, W0, T4, TMP, ACC, T0, T1]) s.mem s₃.mem :=
      unch_same (unch_same (slots_widen U₁ (by decide)) (slots_widen U₂ (by decide)))
        (slots_widen V.unch (by decide))
    rw [U.word (fun w hw => by
      have := apart_slW (c := c) (by decide : T2 ∉ [T3, W0, T4, TMP, ACC, T0, T1]) w hw
      omega_using [h0, this]) (by have := sl_le c h7 (i := T2) (by decide); omega_using [h0, hn, this]), hword]
  refine WP.mono (descentCounter_ok V.scr (by have := sl_le c h7 (i := T2) (by decide); omega_using [h0, this])
    hj (by omega_using [hj']) w₃) fun s₄ ⟨word₄, zf₄, k₄, O₄⟩ => ?_
  have e₄ {i : Nat} (hi : i < 45) (hw : i ≠ T2) : sv c base s₄ i = sv c base s₃ i :=
    O₄.wordsVal (by have := sl_apart c hw; omega_using [h0, this]) (by have := sl_le c h7 hi; omega_using [hn, this])
  refine ⟨V.scr.of_keepRegs k₄ (by decide), ?_,
    unch_same U₁₂₃ (slot_frame (by decide : T2 ∈ roundSlots) (by omega_using [h0]) O₄), ?_, word₄, zf₄, ?_⟩
  · exact ((k₁.trans (k₂.mono (fun _ h => List.mem_cons_of_mem _ h))).trans
      (V.keep.mono (fun _ h => List.mem_cons_of_mem _ h))).trans (k₄.mono (by simp [powClob]))
  · intro i hi
    obtain hi45 : i < 45 := (by decide : ∀ i ∈ [ACC, T0, T1], i < 45) i hi
    obtain hn₂ : i ≠ T2 := (by decide : ∀ i ∈ [ACC, T0, T1], i ≠ T2) i hi
    rw [e₄ hi45 hn₂]; exact V.lt i hi
  · have r₄ : fieldAt c base s₄ ACC = fieldAt c base s ACC * fieldAt c base s₂ T4 := by
      rw [fieldAt, e₄ (by decide) (by decide), V.r, e₂ (by decide) (by decide), e₁ (by decide) (by decide)]
    obtain t₄ : fieldAt c base s₄ T0 = fieldAt c base s T0 * (fieldAt c base s₂ T4 * fieldAt c base s₂ T4) := by
      rw [fieldAt, e₄ (by decide) (by decide), V.t, e₂ (by decide) (by decide), e₁ (by decide) (by decide)]
    obtain c₄ : fieldAt c base s₄ T1 = fieldAt c base s T1 * fieldAt c base s T1 := by
      rw [fieldAt, e₄ (by decide) (by decide), V.c, e₂ (by decide) (by decide), e₁ (by decide) (by decide)]
    conv_rhs => rw [show j = j - 1 + 1 by omega_using [hj], rootDescent]
    simp only [pow_eq_npow]
    rw [r₄, t₄, c₄, b₂]

end VG.Proof.EcKey.Compressed.X86_64

end

end

/-! # P-224's machine candidate refines its functional root algorithm -/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86_64/TonelliPowers.lean`, which only this module imported.
section

/-! # The two initial powers in P-224's root recovery -/

section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Impl.Ecdh.X86_64 (W2)
open VG.Impl.EcKey.Compressed.X86_64 (rootQ)
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

abbrev tonelliPowerWrites (c : Cfg) :=
  rootPowerWrites c 1 ++ slW c [T5] ++ rootPowerWrites c 2

theorem tonelliPowers_ok {c : Cfg} (hc : BaseCfgOk c) (hn9 : c.n ≠ 9)
    {base : Addr} {s : State} (hs : Scr s base size)
    (hM : ModOkW c.MP' size c.C.p s.mem base) (hB : sv c base s W2 < c.C.p)
    (hO : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) :
    WP isa (Impl.EcKey.Compressed.X86_64.tonelliPowers c).inline s fun t =>
      KeepRegs (powClob c.n) s t ∧ Unch base (tonelliPowerWrites c) s.mem t.mem ∧
      sv c base t ACC < c.C.p ∧ sv c base t T5 < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t ACC) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ rootQ c ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t T5) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ ((rootQ c + 1) / 2) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  obtain hq : rootQ c ≤ c.C.p - 1 := Nat.div_le_self _ _
  have hp := hc.p_ge
  obtain he : (rootQ c + 1) / 2 < 2 ^ (64 * c.n) := by have := hc.p_lt; omega
  obtain hqR : rootQ c < 2 ^ (64 * c.n) := by have := hc.p_lt; omega
  change WP isa (.seq (Impl.EcKey.Compressed.X86_64.rootPower c ((rootQ c + 1) / 2) 1).inline
    (.seq (.block (copy c.n (c.sl T5) (c.sl ACC)))
      (Impl.EcKey.Compressed.X86_64.rootPower c (rootQ c) 2).inline)) s _
  refine WP.seq (WP.mono (rootPower_ok hc (by decide) (.inr hn9) he hs hM hB hO)
    fun s₁ ⟨k₁, U₁, lt₁, v₁⟩ => ?_)
  obtain hs₁ := hs.of_keepRegs k₁ (rdi_not_powClob _)
  have e₁ {i : Nat} (hi : i < 45) (hw : i ∉ [EXPP, ACC, PT, TMP]) :
      sv c base s₁ i = sv c base s i := sv_unch U₁ h7 hn hi (rootPower_apart hi hw)
  refine WP.seq (WP.mono (copy_ok c.n hs₁ (sl_le c h7 (by decide)) (sl_le c h7 (by decide))
    (by have := sl_apart c (i := T5) (j := ACC) (by decide); omega)) fun s₂ ⟨v₂, k₂, O₂⟩ => ?_)
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have e₂ {i : Nat} (hi : i < 45) (hw : i ≠ T5) : sv c base s₂ i = sv c base s₁ i :=
    O₂.wordsVal (sl_apart c hw) (by have := sl_le c h7 hi; omega)
  obtain M₂ : ModOkW c.MP' size c.C.p s₂.mem base := modP_of hc (by
    change sv c base s₂ MP = _
    rw [e₂ (by decide) (by decide), e₁ (by decide) (by decide)]; exact hM.val)
  refine WP.mono (rootPower_ok hc (by decide) (.inl (by decide)) hqR hs₂ M₂
    (by rw [e₂ (by decide) (by decide), e₁ (by decide) (by decide)]; exact hB)
    (by rw [e₂ (by decide) (by decide), e₁ (by decide) (by decide)]; exact hO))
    fun t ⟨kt, Ut, ltt, vt⟩ => ?_
  obtain et : sv c base t T5 = sv c base s₂ T5 :=
    sv_unch Ut h7 hn (by decide) (rootPower_apart (by decide) (by decide))
  refine ⟨(k₁.trans (k₂.mono (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr; simp [powClob, clob]))).trans kt,
    (U₁.trans O₂.unch).trans Ut, ltt, ?_, ?_, ?_⟩
  · rw [et]
    change wordsVal s₂.mem base (c.sl T5) c.n < _
    rw [v₂]; exact lt₁
  · rw [vt, e₂ (by decide) (by decide), e₁ (by decide) (by decide)]
  · rw [et]
    change toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₂.mem base (c.sl T5) c.n) = _
    rw [v₂]; exact v₁

end VG.Proof.EcKey.Compressed.X86_64
end

end

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86_64/DescentLoop.lean`, which only this module imported.
section

/-! # The P-224 machine loop computes the functional root descent -/

section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Impl.EcKey.Compressed (rootDescent)

structure DescentInv (c : Cfg) (base : Addr) (count : Nat) (s₀ s : State) (j : Nat) : Prop where
  scr : Scr s base size
  mod : ModOkW c.MP' size c.C.p s.mem base
  one : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p
  counter : word s.mem base (c.sl T2) = BitVec.ofNat 64 j
  keep : KeepRegs (powClob c.n) s₀ s
  unch : Unch base (slW c roundSlots) s₀.mem s.mem
  lt : ∀ i ∈ [ACC, T0, T1], sv c base s i < c.C.p
  val : rootDescent j (fieldAt c base s ACC) (fieldAt c base s T0) (fieldAt c base s T1) =
    rootDescent count (fieldAt c base s₀ ACC) (fieldAt c base s₀ T0) (fieldAt c base s₀ T1)

theorem descentLoop_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State} {count : Nat}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hOne : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p)
    (hlt : ∀ i ∈ [ACC, T0, T1], sv c base s i < c.C.p)
    (hcount : 1 ≤ count) (hcount' : count < 2 ^ 31)
    (hword : word s.mem base (c.sl T2) = BitVec.ofNat 64 count) :
    WP isa (.loop (Impl.EcKey.Compressed.X86_64.descentRound c).inline .ne) s fun t =>
      KeepRegs (powClob c.n) s t ∧ Unch base (slW c roundSlots) s.mem t.mem ∧
      sv c base t ACC < c.C.p ∧ fieldAt c base t ACC =
        rootDescent count (fieldAt c base s ACC) (fieldAt c base s T0) (fieldAt c base s T1) := by
  have hn := hs.nowrap
  have h7 := hc.n10
  apply countLoop_ok (Inv := fun j t => DescentInv c base count s t j) (n := count)
  · intro j t hj hjc I
    refine WP.mono (descentRound_ok hc I.scr I.mod I.lt I.one hj (by omega) I.counter)
      fun u R => ?_
    obtain M : ModOkW c.MP' size c.C.p u.mem base := modP_of hc (by
      rw [sv_unch R.unch h7 hn (by decide) (apart_slW (by decide : MP ∉ roundSlots))]
      exact I.mod.val)
    obtain one : sv c base u ONEP = 2 ^ (64 * c.n) % c.C.p := by
      rw [sv]
      rw [sv_unch R.unch h7 hn (by decide) (apart_slW (by decide : ONEP ∉ roundSlots))]
      exact I.one
    exact ⟨⟨R.scr, M, one, R.counter, I.keep.trans R.keep, unch_same I.unch R.unch,
      R.lt, R.descent.trans I.val⟩, R.zf⟩
  · intro t I
    exact ⟨I.keep, I.unch, I.lt _ (by simp), I.val⟩
  · exact hcount
  · exact ⟨hs, hM, hOne, hword, ⟨fun _ _ => rfl, rfl, rfl⟩, Unch.refl _ _ _, hlt, rfl⟩

end VG.Proof.EcKey.Compressed.X86_64
end

end

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Impl.Ecdh.X86_64 (W2)
open VG.Impl.EcKey.Compressed.X86_64 (rootQ)
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

private theorem power_writes_subset (c : Cfg) {j : Nat} (hj : j = 1 ∨ j = 2) :
    ∀ w ∈ rootPowerWrites c j, w ∈ candidateWrites c := by
  intro w hw
  change w ∈ [(c.sl EXPP, 8 * c.n), (bitsAt c.n j, 64 * c.n)] ++ slW c [ACC, PT, TMP] at hw
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with (rfl | rfl) | hw
  · simp [candidateWrites, candidateSlots, slW]
  · rcases hj with rfl | rfl <;> simp [candidateWrites]
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    apply List.mem_append_left
    exact List.mem_map_of_mem ((by decide : ∀ i ∈ [ACC, PT, TMP], i ∈ candidateSlots) i hi)

theorem candidateTonelli_correct {c : Cfg} (hc : BaseCfgOk c) (hp : c.C.p % 4 ≠ 3)
    (hn9 : c.n ≠ 9) (hq : 0 < rootQ c) :
    CandidateCorrect c (fun a => Impl.EcKey.Compressed.rootTonelli a (rootQ c) 96 (Fin.ofNat c.C.p 11)) := by
  intro base s hs hM hB hO
  have h7 := hc.n10
  have hn := hs.nowrap
  simp only [Impl.EcKey.Compressed.X86_64.rootCandidate, hp, ↓reduceIte]
  change WP isa (.seq (Impl.EcKey.Compressed.X86_64.tonelliPowers c).inline
    (.seq (.block (Impl.EcKey.Compressed.X86_64.tonelliSetup c))
      (.loop (Impl.EcKey.Compressed.X86_64.descentRound c).inline .ne))) s _
  refine WP.seq (WP.mono (tonelliPowers_ok hc hn9 hs hM hB hO)
    fun s₁ ⟨k₁, U₁, lt₁, ltR₁, t₁, r₁⟩ => ?_)
  obtain hs₁ := hs.of_keepRegs k₁ (rdi_not_powClob _)
  refine WP.seq (WP.mono (tonelliSetup_ok hc hs₁ ltR₁ lt₁)
    fun s₂ ⟨k₂, U₂, lt₂, counter₂, r₂, t₂, c₂⟩ => ?_)
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  obtain U₁₂ : Unch base (candidateWrites c) s.mem s₂.mem :=
    unch_same (U₁.mono (by
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · rcases List.mem_append.mp hw with hw | hw
        · exact power_writes_subset c (.inl rfl) w hw
        · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
          exact List.mem_append_left _ (List.mem_map_of_mem
            ((by decide : ∀ i ∈ [T5], i ∈ candidateSlots) i hi))
      · exact power_writes_subset c (.inr rfl) w hw))
      (U₂.mono (by
        intro w hw
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
        exact List.mem_append_left _ (List.mem_map_of_mem
          ((by decide : ∀ i ∈ [T0, ACC, T1, T2], i ∈ candidateSlots) i hi))))
  obtain M₂ : ModOkW c.MP' size c.C.p s₂.mem base := modP_of hc (by
    rw [sv_unch U₁₂ h7 hn (by decide) (candidate_apart (by decide) (by decide))]
    exact hM.val)
  obtain one₂ : sv c base s₂ ONEP = 2 ^ (64 * c.n) % c.C.p := by
    rw [sv, sv_unch U₁₂ h7 hn (by decide) (candidate_apart (by decide) (by decide))]
    exact hO
  refine WP.mono (descentLoop_ok hc hs₂ M₂ one₂ lt₂ (by decide : 1 ≤ 95)
    (by decide : 95 < 2 ^ 31) counter₂) fun t ⟨kt, Ut, ltt, vt⟩ => ?_
  refine ⟨(k₁.trans (k₂.mono (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr; simp [powClob, clob]))).trans kt,
    unch_same U₁₂ (Ut.mono (by
      intro w hw
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact List.mem_append_left _ (List.mem_map_of_mem
        ((by decide : ∀ i ∈ roundSlots, i ∈ candidateSlots) i hi)))), ltt, ?_⟩
  change fieldAt c base t ACC = _
  rw [vt]
  change Impl.EcKey.Compressed.rootDescent 95
    (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₂ ACC))
    (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₂ T0))
    (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₂ T1)) = _
  rw [r₂, t₂, c₂, r₁, t₁, rootTonelli_eq_descent _ _ _ _ hq]
  simp only [pow_eq_npow]

end VG.Proof.EcKey.Compressed.X86_64

end

end


/-! # P224: instantiate the shared public-point decompression proof -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64.P224Decompress

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64.P224

abbrev root (a : Spec.Weierstrass.Fe Spec.P224.curve) :=
  Impl.EcKey.Compressed.rootTonelli a ((Spec.P224.curve.p - 1) / 2 ^ 96) 96 (Fin.ofNat Spec.P224.curve.p 11)

abbrev code (adx : Bool) : Prog isa := Impl.EcKey.Compressed.X86_64.decompress (Inverse.cfg adx)

materialize_shared baseline := code false

theorem inlineOk (adx : Bool) : (code adx).InlineOk = true := by
  rw [show code adx = code false from rfl]
  lit_decide

theorem hmx (adx : Bool) : (code adx).allInstrs (fun i => !loadsMxcsr i) = true := by
  rw [show code adx = code false from rfl]
  lit_decide

theorem ct (adx : Bool) : ConstantTime isa (decompressContract Spec.P224.curve root).pre
    (decompressContract Spec.P224.curve root).pub (code adx) := by
  rw [show code adx = code false from rfl]
  apply VG.Taint.constantTime (A := X86_64.taint) (decompressT Spec.P224.curve.len)
  all_goals first
    | exact fun _ _ h₁ h₂ hp => decompress_agree h₁ h₂ hp
    | taint_decide

theorem sat : ∃ s, (Spec.EcKey.P224.inst.decompressPublicKeyContract abi 8).pre s := by
  sig_implies_sat [Spec.EcKey.P224.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords,
    abi, argRegs, decompressSatState] [decompressSatState] using (decompressSatState Spec.P224.curve.len)

theorem verified (hL : Law Spec.P224.curve) (hI : InvSounds) (adx : Bool) :
    Verified target (code adx) (Spec.EcKey.P224.inst.decompressPublicKeyContract abi 8) := by
  obtain hc := Inverse.cfg_ok hI adx
  obtain hp : (Inverse.cfg adx).C.p % 4 ≠ 3 := by cases adx <;> decide +kernel
  obtain hn9 : (Inverse.cfg adx).n ≠ 9 := by cases adx <;> decide
  obtain hq : 0 < Impl.EcKey.Compressed.X86_64.rootQ (Inverse.cfg adx) := by
    cases adx <;> decide +kernel
  obtain hf := VG.Proof.P224.rootFacts hL
  obtain himp := decompress_implies Spec.EcKey.P224.inst _ hf sat
  refine Verified.of_inline_ct (inlineOk adx)
    (by
      cases adx
      · exact decompress_correct _ hc _ (candidateTonelli_correct hc hp hn9 hq) (inlineOk false) (hmx false)
      · exact decompress_correct _ hc _ (candidateTonelli_correct hc hp hn9 hq) (inlineOk true) (hmx true))
    (ct adx) himp (fun _ hs => Sig.clear_of_pre hs) ?_
  intro s b hv u hs hp
  exact decompress_post_patch _ _ s b hv u (himp.pre s hs) (Sig.clear_of_pre hs) hp

/-! ## Without secret residue -/

/-- The granules of its stack that `vg_ec_p224_decompress_public_key` must wipe on
return, from the residue analysis (`X86_64.RScrub.keepFor`). -/
def scrubKs : List Nat :=
  keep_for% Spec.EcKey.P224.inst.decompressPublicKeyApi.sig 8 (code false) []

theorem scrubOk : ∃ h : VG.Taint.Hint X86_64.RTaint.FT,
    (VG.Taint.check X86_64.RTaint.rtaint (X86_64.RScrub.init Spec.EcKey.P224.inst.decompressPublicKeyApi.sig 8 [])
      (code false) h).any (X86_64.RScrub.resOkB · 8 scrubKs (Impl.Scrub.X86_64.chunks 8)) = true :=
  X86_64.RScrub.Analysed.ok_of _ (by taint_decide)

/-- `vg_ec_p224_decompress_public_key`, followed by `Impl.Scrub.X86_64.scrubTail`
(`X86_64.RScrub.withScrub`): it returns without secret residue. -/
def scrubReg (hL : Law Spec.P224.curve) (hI : InvSounds) :
    Registration Spec.EcKey.P224.inst.decompressPublicKeyApi target :=
  X86_64.RScrub.withScrub {
    code := code false
    verified := verified hL hI false
    stack := 8 }
    (EcKey.X86_64.Scrub.decompressOut _ _) [] (X86_64.RScrub.pubOk_nil _) (some ⟨scrubKs, scrubOk⟩)

end VG.Proof.EcKey.Compressed.X86_64.P224Decompress
