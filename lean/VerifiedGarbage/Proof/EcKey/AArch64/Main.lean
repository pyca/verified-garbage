import VerifiedGarbage.Proof.Ecdsa.AArch64.Finish
import VerifiedGarbage.Impl.EcKey.AArch64
import VerifiedGarbage.Proof.Ecdsa.AArch64.Middle
import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Framework.AArch64.Inline

/-!
# Elliptic curve public keys on AArch64: the result, and the whole function

As on x86-64 (`Proof/EcKey/X86_64/Main.lean`).

## The result

`finish` writes `04 ‖ x ‖ y` big-endian to `out`, or zeros, by the flag's
mask, restores `x19`–`x25`, and returns the flag's low bit
(`pkFinish_ok`): the leading byte (`lead_ok`), then the two coordinates as
the signature's `finish` writes `r ‖ s`, from `out + 1` in `x6`.
-/

namespace VG.Proof.EcKey.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

theorem byte_outside (m : Mem) (a : Addr) (v : BitVec (8 * 1)) : Outside a 0 1 m (m.write a 1 v) := by
  intro x hx
  have : ¬ (x - a).toNat < 1 := by simp only [ofs] at hx; omega
  simp only [Mem.write, this, ite_false]

theorem byte_self (m : Mem) (a : Addr) (v : BitVec (8 * 1)) : m.write a 1 v a = v := by
  simp only [Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.mul_zero, Nat.zero_lt_one, ite_true]
  exact BitVec.extractLsb'_eq_self

theorem mask4 (b : Bool) :
    ((4 : BitVec 64) &&& (if b then BitVec.allOnes 64 else 0)).setWidth 8 = (if b then 4 else 0 : Byte) := by
  cases b <;> decide

/-- `04` (or `0`) to `out`, by the mask in `x3`. -/
theorem lead_ok {s : State} {out : Addr} (hx20 : s.gpr .x20 = out) (hw : InRegions s.wr out 1) (b : Bool)
    (hc : s.gpr .x3 = if b then BitVec.allOnes 64 else 0) :
    WP isa (.block ([.movz .x .x1 4 0, .logic .and .x .x1 .x1 .x3, .strb .x1 .x20 0] : List Instr)) s
      fun s' => s'.mem out = (if b then 4 else 0) ∧ Outside out 0 1 s.mem s'.mem ∧ KeepRegs [.x1] s s' := by
  have ha : s.gpr .x20 + BitVec.ofNat 64 0 = out := by rw [hx20]; exact BitVec.add_zero _
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, Nat.mod_one,
    show 0 < 4096 * 1 by decide, show 16 * 0 < Size.x.bits by decide, and_self, ite_true,
    Option.bind_some, State.store, State.read, RegUpd.gpr_write, RegUpd.wr_write, BitVec.setWidth_eq,
    reduceCtorEq, ite_false, ha, hw, hc, Option.some.injEq, exists_eq_left']
  refine ⟨?_, byte_outside _ _ _, ⟨fun r hr => ?_, rfl, rfl, rfl⟩⟩
  · rw [byte_self, ← mask4]; cases b <;> rfl
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]

/-- `x6 = out + 1`. -/
theorem outPlus_ok (s : State) :
    WP isa (.block [.addImm .x .x6 .x20 1]) s fun s' =>
      s'.gpr .x6 = s.gpr .x20 + BitVec.ofNat 64 1 ∧ Keeps [.x6] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, show (1 : Nat) < 4096 by decide,
    ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

theorem finish_eq (c : Cfg) : Impl.EcKey.AArch64.Cfg.finish c =
    ([ld .x3 (c.sl FLAG)] : List Instr) ++
    (([.movz .x .x1 4 0, .logic .and .x .x1 .x1 .x3, .strb .x1 .x20 0] : List Instr) ++
    (([.addImm .x .x6 .x20 1] : List Instr) ++
    (storeBytes c.C.len c.n .x6 0 (c.sl X) ++ (storeBytes c.C.len c.n .x6 c.C.len (c.sl Impl.EcKey.AArch64.Y) ++
    (Spill.restoreCode .x0 Cfg.saved ++
    ([.movz .x .x1 1 0, .logic .and .x .x0 .x3 .x1] : List Instr)))))) := by
  simp only [Impl.EcKey.AArch64.Cfg.finish, List.append_assoc]; rfl

/-- The result, the return value and the callee-saved registers. -/
theorem pkFinish_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size) {out : Addr}
    (hx20 : s.gpr .x20 = out) (hfit : out.toNat + (1 + 2 * c.C.len) ≤ 2 ^ 64)
    (hw : (⟨out, 1 + 2 * c.C.len⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨out, 1 + 2 * c.C.len⟩ ⟨base, size⟩)
    {g : Reg → BitVec 64} (hsv : Spill.Saved base g Cfg.saved s.mem) (b : Bool)
    (hf : word s.mem base (c.sl FLAG) = if b then BitVec.allOnes 64 else 0) :
    WP isa (.block (Impl.EcKey.AArch64.Cfg.finish c)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem out (1 + 2 * c.C.len) =
        (if b then 4 :: (toBytes c.C.len (sv c base s X) ++ toBytes c.C.len (sv c base s Impl.EcKey.AArch64.Y))
          else List.replicate (1 + 2 * c.C.len) 0) ∧
      (s'.gpr .x0).setWidth 32 = (if b then 1 else 0) ∧
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = g r) := by
  have h7 := hc.n10
  have hn0 := hc.n0
  have hn := hs.nowrap
  have hl8 := hc.len8
  have hlo := hc.len_lo
  have hhi := hc.len_hi
  have hX := sl_le c h7 (i := X) (by decide)
  have hY := sl_le c h7 (i := Impl.EcKey.AArch64.Y) (by decide)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  have h1 : ∀ e, out + BitVec.ofNat 64 1 + BitVec.ofNat 64 0 + BitVec.ofNat 64 e =
      out + BitVec.ofNat 64 (1 + e) := fun e => by
    rw [BitVec.add_zero, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have h8 : ∀ e, out + BitVec.ofNat 64 1 + BitVec.ofNat 64 c.C.len + BitVec.ofNat 64 e =
      out + BitVec.ofNat 64 (1 + c.C.len + e) := fun e => by
    rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat, Nat.add_assoc]
  have hdsc : ∀ {a d : Nat}, a + 8 * c.n ≤ size → d + c.C.len ≤ 1 + 2 * c.C.len →
      Region.Disjoint ⟨off base a, 8 * c.n⟩ ⟨out + BitVec.ofNat 64 d, c.C.len⟩ := fun ha hd' =>
    (hd.symm.sub_left (Offset.sub_base base ha)).sub_right (Offset.sub_base out hd')
  have hscd : ∀ {d k : Nat}, d + k ≤ 1 + 2 * c.C.len →
      Region.Disjoint ⟨base, size⟩ ⟨out + BitVec.ofNat 64 d, k⟩ := fun hd' =>
    hd.symm.sub_right (Offset.sub_base out hd')
  have hout : out + BitVec.ofNat 64 0 = out := BitVec.add_zero out
  have h10 : out + BitVec.ofNat 64 1 + BitVec.ofNat 64 0 = out + BitVec.ofNat 64 1 := BitVec.add_zero _
  have h18 : out + BitVec.ofNat 64 1 + BitVec.ofNat 64 c.C.len = out + BitVec.ofNat 64 (1 + c.C.len) := by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rw [finish_eq, WP.block_append_iff]
  refine WP.mono (ld_ok hs (d := c.sl FLAG) (by omega) (sl_mod8 c FLAG) .x3) fun s₁ ⟨e₁, k₁, _⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.mem
  have hx20₁ : s₁.gpr .x20 = out := by rw [k₁.gpr _ (by decide), hx20]
  rw [WP.block_append_iff]
  have hc0 : (⟨out, 1 + 2 * c.C.len⟩ : Region).Contains out 1 := by
    have := Offset.contains_base out (d := 0) (n := 1) (k := 1 + 2 * c.C.len) (by omega) (by omega)
    rwa [hout] at this
  refine WP.mono (lead_ok hx20₁ ⟨_, by rw [k₁.wr]; exact hw, hc0⟩ b (by rw [e₁, hf]))
    fun s₂ ⟨e₂, O₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have U₂ := O₂.unch_far (by have := hscd (d := 0) (k := 1) (by omega); rwa [hout] at this)
  rw [WP.block_append_iff]
  refine WP.mono (outPlus_ok s₂) fun s₂' ⟨e₂', k₂'⟩ => ?_
  have hs₂' := hs₂.of_keeps k₂' (by decide)
  have hx6 : s₂'.gpr .x6 = out + BitVec.ofNat 64 1 := by rw [e₂', k₂.gpr _ (by decide), hx20₁]
  have hx3₂ : s₂'.gpr .x3 = if b then BitVec.allOnes 64 else 0 := by
    rw [k₂'.gpr _ (by decide), k₂.gpr _ (by decide), e₁, hf]
  have x₂ : wordsVal s₂'.mem base (c.sl X) c.n = sv c base s X := by
    rw [k₂'.mem, U₂.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega),
      hm₁]
  rw [WP.block_append_iff]
  refine WP.mono (storeBytes_ok hs₂' (dst := .x6) (d := 0) (a := c.sl X) (by decide) (by decide) (by decide) b
    hx3₂ hX (sl_mod8 c X) (by omega) hlo hhi (by omega)
    (by rw [hx6, h10, Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (show 1 < 2 ^ 64 by decide),
      Nat.mod_eq_of_lt (by omega)]; omega)
    (fun e m he => ⟨_, by rw [k₂'.wr, k₂.wr, k₁.wr]; exact hw, by
      rw [hx6, h1]; exact Offset.contains_base out (by omega) (by omega)⟩)
    (by rw [hx6, h10]; exact hdsc hX (by omega))) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  rw [hx6, h10] at e₃ O₃
  have hs₃ := hs₂'.of_keepRegs k₃ (by decide)
  have U₃ := O₃.unch_far (hscd (d := 1) (by omega))
  have hx6₃ : s₃.gpr .x6 = out + BitVec.ofNat 64 1 := by rw [k₃.gpr _ (by decide), hx6]
  have hx3₃ : s₃.gpr .x3 = if b then BitVec.allOnes 64 else 0 := by
    rw [k₃.gpr _ (by decide), hx3₂]
  have y₃ : wordsVal s₃.mem base (c.sl Impl.EcKey.AArch64.Y) c.n = sv c base s Impl.EcKey.AArch64.Y := by
    rw [U₃.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega),
      k₂'.mem, U₂.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega), hm₁]
  rw [WP.block_append_iff]
  refine WP.mono (storeBytes_ok hs₃ (dst := .x6) (d := c.C.len) (a := c.sl Impl.EcKey.AArch64.Y) (by decide)
    (by decide) (by decide) b hx3₃ hY (sl_mod8 c _) (by omega) hlo hhi (by omega)
    (by rw [hx6₃, h18, Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (show 1 + c.C.len < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (by omega)]; omega)
    (fun e m he => ⟨_, by rw [k₃.wr, k₂'.wr, k₂.wr, k₁.wr]; exact hw, by
      rw [hx6₃, h8]; exact Offset.contains_base out (by omega) (by omega)⟩)
    (by rw [hx6₃, h18]; exact hdsc hY (by omega))) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  rw [hx6₃, h18] at e₄ O₄
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  have U₄ := O₄.unch_far (hscd (d := 1 + c.C.len) (by omega))
  have hx3₄ : s₄.gpr .x3 = if b then BitVec.allOnes 64 else 0 := by
    rw [k₄.gpr _ (by decide), hx3₃]
  have lead : Spec.Ecdsa.bytesAt s₄.mem out 1 = [if b then 4 else 0] := by
    rw [bytesAt_keep O₄ (Offset.base_disjoint out (by omega) (by omega)) (by omega) (by omega),
      bytesAt_keep O₃ (Offset.base_disjoint out (by omega) (by omega)) (by omega) (by omega)]
    simp only [Spec.Ecdsa.bytesAt, List.range_one, List.map_cons, List.map_nil, hout, k₂'.mem, e₂]
  have first : Spec.Ecdsa.bytesAt s₄.mem (out + BitVec.ofNat 64 1) c.C.len =
      if b then toBytes c.C.len (sv c base s X) else List.replicate c.C.len 0 := by
    rw [bytesAt_keep O₄ (Offset.disjoint out (by omega) (by omega) (by omega)) (by omega) (by omega), e₃, x₂]
  have hsv₄ : Spill.Saved base g Cfg.saved s₄.mem := by
    have h16 : ∀ w ∈ [(size, 2 ^ 64)], 64 ≤ w.1 := fun w hw => by
      simp only [List.mem_singleton] at hw; subst hw; decide
    have sv₂ : Spill.Saved base g Cfg.saved s₂'.mem := by
      rw [k₂'.mem]; exact Saved.unch (hm₁ ▸ hsv) h16 U₂
    exact Saved.unch (Saved.unch sv₂ h16 U₃) h16 U₄
  refine Spill.restore_ok hs₄.x0 (by decide) (by decide) (fun p hp => ?_) hsv₄ fun s₅ R₅ => ?_
  · have := saved_lt p hp
    exact ⟨_, List.mem_append_right _ hs₄.wr, hs₄.contains (by have : size = 8192 := rfl; omega) (by decide)⟩
  refine WP.mono (retBit_ok s₅) fun s₆ ⟨e₆, k₆⟩ => ?_
  refine ⟨?_, ?_, fun r hr => ?_⟩
  · rw [k₆.mem, R₅.mem, bytesAt_add, show 2 * c.C.len = c.C.len + c.C.len by omega, bytesAt_add, lead, first,
      BitVec.add_assoc, BitVec.ofNat_add_ofNat, e₄, y₃]
    cases b
    · simp only [Bool.false_eq_true, ite_false, ← List.replicate_append_replicate]; rfl
    · simp only [ite_true]; rfl
  · have hx3 : Reg.x3 ∉ Cfg.saved.map Prod.fst := by decide
    rw [e₆, R₅.other _ hx3, hx3₄, mask_bit]
  · have : r ∉ [Reg.x0, .x1] := by
      revert r; decide
    rw [k₆.gpr r this]
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    exact R₅.gpr p hp

end VG.Proof.EcKey.AArch64

/-!
## `x`, `y`, the checks and the result

`middle` computes `x = X Z^(p-2)` and `y = Y Z^(p-2)` from `X`, `Y` and the
power in `ACC`, each left Montgomery's form by a multiplication by 1
(`pkOps_ok`), then ands the masks of `d ∈ [1, n-1]` and `Z ≠ 0` into the
flag and writes the result (`middle_ok`).
-/

namespace VG.Proof.EcKey.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64
open VG.Impl.EcKey.AArch64 (YM Y)

variable {c : Cfg}

theorem middle_eq (c : Cfg) : Impl.EcKey.AArch64.Cfg.middle c =
    .seq (.block (mul c.MP' (c.sl XM) (c.sl RX) (c.sl ACC)))
    (.seq (.block (mul c.MP' (c.sl X) (c.sl XM) (c.sl ONE)))
    (.seq (.block (mul c.MP' (c.sl YM) (c.sl RY) (c.sl ACC)))
    (.seq (.block (mul c.MP' (c.sl Y) (c.sl YM) (c.sl ONE)))
    (.block (c.checkRange (c.sl D) ++ c.checkNonzero (c.sl RZ) ++ Impl.EcKey.AArch64.Cfg.finish c))))) := rfl

/-- What `middle`'s field operations leave. -/
structure OpsPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  gpr : ∀ r, r ∉ clob c.n → s'.gpr r = s.gpr r
  wr : s'.wr = s.wr
  unch : Unch base ([XM, X, YM, Y, TMP].map fun i => (c.sl i, 8 * c.n)) s.mem s'.mem
  x_lt : sv c base s' X < c.C.p
  x : Fin.ofNat c.C.p (sv c base s' X) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)
  y_lt : sv c base s' Y < c.C.p
  y : Fin.ofNat c.C.p (sv c base s' Y) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s RY) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)

/-- The four field operations of `middle`. -/
theorem pkOps_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hMP : ModOkA c.MP' size c.C.p s.mem base) (hacc : sv c base s ACC < c.C.p) (hone : sv c base s ONE = 1)
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', OpsPost c base s s' → WP isa rest s' Q) :
    WP isa (.seq (.block (mul c.MP' (c.sl XM) (c.sl RX) (c.sl ACC)))
      (.seq (.block (mul c.MP' (c.sl X) (c.sl XM) (c.sl ONE)))
      (.seq (.block (mul c.MP' (c.sl YM) (c.sl RY) (c.sl ACC)))
      (.seq (.block (mul c.MP' (c.sl Y) (c.sl YM) (c.sl ONE))) rest)))) s Q := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  -- `XM = X · ACC`.
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) h7 hs hMP (MP'_A c) (o := XM) (a := RX) (b := ACC) (by decide)
    (by decide) (by decide) hacc) fun s₁ ⟨k₁, _, e₁⟩ => ?_)
  have hs₁ := k₁.scr hs
  have kP₁ := hMP.keepA64 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  have v₁ : ∀ {i}, i < 45 → i ≠ XM → i ≠ TMP → sv c base s₁ i = sv c base s i := fun hi h₁ h₂ =>
    sv_keep (MP'_n c) rfl h7 hn k₁ hi h₁ h₂
  -- `X = XM · 1`.
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) h7 hs₁ kP₁ (MP'_A c) (o := X) (a := XM) (b := ONE) (by decide)
    (by decide) (by decide) (by rw [v₁ (by decide) (by decide) (by decide), hone]; omega))
    fun s₂ ⟨k₂, lt₂, e₂⟩ => ?_)
  have hs₂ := k₂.scr hs₁
  have kP₂ := kP₁.keepA64 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  have v₂ : ∀ {i}, i < 45 → i ≠ XM → i ≠ X → i ≠ TMP → sv c base s₂ i = sv c base s i := fun hi h₁ h₂ h₃ =>
    (sv_keep (MP'_n c) rfl h7 hn k₂ hi h₂ h₃).trans (v₁ hi h₁ h₃)
  have x₂ : Fin.ofNat c.C.p (sv c base s₂ X) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) := by
    rw [toM_one_mul hpR (by rw [e₂, v₁ (i := ONE) (by decide) (by decide) (by decide), hone]),
      toM_mul hpR e₁]
  -- `YM = Y · ACC`.
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) h7 hs₂ kP₂ (MP'_A c) (o := YM) (a := RY) (b := ACC) (by decide)
    (by decide) (by decide) (by rw [v₂ (by decide) (by decide) (by decide) (by decide)]; exact hacc))
    fun s₃ ⟨k₃, _, e₃⟩ => ?_)
  have hs₃ := k₃.scr hs₂
  have kP₃ := kP₂.keepA64 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₃ (by decide) (by decide)
  have v₃ : ∀ {i}, i < 45 → i ≠ XM → i ≠ X → i ≠ YM → i ≠ TMP → sv c base s₃ i = sv c base s i :=
    fun hi h₁ h₂ h₃ h₄ => (sv_keep (MP'_n c) rfl h7 hn k₃ hi h₃ h₄).trans (v₂ hi h₁ h₂ h₄)
  -- `Y = YM · 1`.
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) h7 hs₃ kP₃ (MP'_A c) (o := Y) (a := YM) (b := ONE) (by decide)
    (by decide) (by decide) (by rw [v₃ (by decide) (by decide) (by decide) (by decide) (by decide), hone]; omega))
    fun s₄ ⟨k₄, lt₄, e₄⟩ => h s₄ ?_)
  have X₄ : sv c base s₄ X = sv c base s₂ X := by
    rw [sv_keep (MP'_n c) rfl h7 hn k₄ (by decide) (by decide) (by decide),
      sv_keep (MP'_n c) rfl h7 hn k₃ (by decide) (by decide) (by decide)]
  have e₃' : sv c base s₃ YM * 2 ^ (64 * c.n) % c.C.p = sv c base s RY * sv c base s ACC % c.C.p := by
    rw [e₃, v₂ (i := RY) (by decide) (by decide) (by decide) (by decide),
      v₂ (i := ACC) (by decide) (by decide) (by decide) (by decide)]
  refine ⟨k₄.scr hs₃, fun r hr => ?_, by rw [k₄.wr, k₃.wr, k₂.wr, k₁.wr], ?_,
    by rw [X₄]; exact lt₂, by rw [X₄]; exact x₂, lt₄, ?_⟩
  · rw [k₄.gpr r hr, k₃.gpr r hr, k₂.gpr r hr, k₁.gpr r hr]
  · exact (((unch_slots (MP'_n c) rfl k₁.unch (l := [XM, X, YM, Y, TMP]) (by simp) (by simp)).trans
      (unch_slots (MP'_n c) rfl k₂.unch (l := [XM, X, YM, Y, TMP]) (by simp) (by simp))).trans
      ((unch_slots (MP'_n c) rfl k₃.unch (l := [XM, X, YM, Y, TMP]) (by simp) (by simp)).trans
      (unch_slots (MP'_n c) rfl k₄.unch (l := [XM, X, YM, Y, TMP]) (by simp) (by simp)))).mono
      fun w hw => by
        simp only [List.mem_append, or_self] at hw
        exact hw
  · rw [toM_one_mul hpR (by rw [e₄, v₃ (i := ONE) (by decide) (by decide) (by decide) (by decide) (by decide),
      hone]), toM_mul hpR e₃']

/-- Whether the public key is a point the result encodes: `d` in `[1, n-1]`
and `Z ≠ 0`. -/
abbrev ok (c : Cfg) (base : Addr) (s : State) : Bool :=
  decide ((0 < sv c base s D ∧ sv c base s D < c.C.n) ∧ sv c base s RZ ≠ 0)

/-- `x`, `y`, the checks and the result. -/
theorem middle_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (F : Fixed c base g s.mem) (hacc : sv c base s ACC < c.C.p)
    (hflag : word s.mem base (c.sl FLAG) = BitVec.allOnes 64) {out : Addr}
    (hx20 : s.gpr .x20 = out) (hfit : out.toNat + (1 + 2 * c.C.len) ≤ 2 ^ 64)
    (hw : (⟨out, 1 + 2 * c.C.len⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨out, 1 + 2 * c.C.len⟩ ⟨base, size⟩) :
    WP isa (Impl.EcKey.AArch64.Cfg.middle c) s fun s' => ∃ xv yv, xv < c.C.p ∧
      Fin.ofNat c.C.p xv =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) ∧
      yv < c.C.p ∧ Fin.ofNat c.C.p yv =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s RY) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) ∧
      Spec.Ecdsa.bytesAt s'.mem out (1 + 2 * c.C.len) =
        (if ok c base s then 4 :: (toBytes c.C.len xv ++ toBytes c.C.len yv)
          else List.replicate (1 + 2 * c.C.len) 0) ∧
      (s'.gpr .x0).setWidth 32 = (if ok c base s then 1 else 0) ∧
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = g r) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hf : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega
  rw [middle_eq]
  refine pkOps_ok hc hs (modP_of hc F.mp) hacc F.one fun s₄ Op => ?_
  have F₄ := F.unch h7 hn (fixedOk_slW (l := [XM, X, YM, Y, TMP]) (by decide)) Op.unch
  have e₄ : ∀ {i}, i < 45 → i ∉ [XM, X, YM, Y, TMP] → sv c base s₄ i = sv c base s i := fun hi hl =>
    sv_unch Op.unch h7 hn hi (apart_slW hl)
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (checkRange_ok c Op.scr h0 (sl_le c h7 (i := D) (by decide)) (sl_le c h7 (i := MN) (by decide))
    hf (sl_mod8 c D) (sl_mod8 c MN) (sl_mod8 c FLAG)) fun s₅ ⟨f₅, k₅, O₅⟩ => ?_
  have hs₅ := Op.scr.of_keepRegs k₅ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (checkNonzero_ok c hs₅ h0 (sl_le c h7 (i := RZ) (by decide)) hf
    (sl_mod8 c RZ) (sl_mod8 c FLAG)) fun s₆ ⟨f₆, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_keepRegs k₆ (by decide)
  have F₆ := (F₄.unch h7 hn fixedOk_flag O₅.unch).unch h7 hn fixedOk_flag O₆.unch
  have e₆ : ∀ {i}, i < 45 → i ≠ FLAG → sv c base s₆ i = sv c base s₄ i := fun hi hif =>
    (sv_flag O₆ h0 h7 hn hi hif).trans (sv_flag O₅ h0 h7 hn hi hif)
  have hflag₆ : word s₆.mem base (c.sl FLAG) = if ok c base s then BitVec.allOnes 64 else 0 := by
    have hMN : wordsVal s₄.mem base (c.sl MN) c.n = c.C.n := F₄.mn
    have z₄ : wordsVal s₄.mem base (c.sl RZ) c.n = sv c base s RZ := e₄ (by decide) (by decide)
    have d₄ : wordsVal s₄.mem base (c.sl D) c.n = sv c base s D := e₄ (by decide) (by decide)
    rw [f₆, f₅, flag_unch Op.unch h7 h0 hn (by decide), hflag, sv_flag O₅ h0 h7 hn (i := RZ) (by decide)
      (by decide), hMN, z₄, d₄, BitVec.allOnes_and, mask_and]
    simp only [mask, decide_eq_true_eq]
  have hx20₆ : s₆.gpr .x20 = out := by
    rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), Op.gpr _ (x20_not_clob h7), hx20]
  have hw₆ : (⟨out, 1 + 2 * c.C.len⟩ : Region) ∈ s₆.wr := by rw [k₆.wr, k₅.wr, Op.wr]; exact hw
  refine WP.mono (pkFinish_ok hc hs₆ hx20₆ hfit hw₆ hd F₆.saved _ hflag₆) fun s' ⟨bytes, ret, saved⟩ =>
    ⟨_, _, Op.x_lt, Op.x, Op.y_lt, Op.y, ?_, ret, saved⟩
  rw [bytes, e₆ (i := X) (by decide) (by decide), e₆ (i := Y) (by decide) (by decide)]

end VG.Proof.EcKey.AArch64

/-!
## The whole function

`publicKey_ok`: `Cfg.publicKey` computes the specification's public key of
`d`, for any curve the ECDSA proof supports (`CfgOk`), and restores the
callee-saved registers.

After `args`, the code up to `Z^(p-2)` is the signature's, with `k`, `d`
and the hash all `d`; its proof (`stage₁`, `stage₂`) is for the signature's
arguments, whose regions are within the public key's: so it runs on the
state with the signature's regions, and `Exec.widen` gives the same run
with the public key's. `middle_ok` and `publicKey_eq` do the rest.
-/

namespace VG.Proof.EcKey.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

variable {c : Cfg}

/-- The arguments: `out = x0` (`1 + 2 len` bytes), `d = x1` (`len` bytes)
and `scratch = x2`, and the comb's tables at the static `c.tsym`
(`Artifact.consts`), readable and writable as the contract says and apart
from each other as it says. -/
structure PkPre (c : Cfg) (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .x1, c.C.len⟩, ⟨s.syms c.tsym, 8 * c.combWords.length⟩]
  wr : s.wr = [⟨s.gpr .x0, 1 + 2 * c.C.len⟩, ⟨s.gpr .x2, size⟩]
  out_sc : Region.Disjoint ⟨s.gpr .x0, 1 + 2 * c.C.len⟩ ⟨s.gpr .x2, size⟩
  out_d : Region.Disjoint ⟨s.gpr .x0, 1 + 2 * c.C.len⟩ ⟨s.gpr .x1, c.C.len⟩
  d_sc : Region.Disjoint ⟨s.gpr .x1, c.C.len⟩ ⟨s.gpr .x2, size⟩
  out_fit : (s.gpr .x0).toNat + (1 + 2 * c.C.len) ≤ 2 ^ 64
  sc_fit : (s.gpr .x2).toNat + size ≤ 2 ^ 64
  tbl : TblPre c s (s.syms c.tsym) (s.gpr .x2)

/-- The private key. -/
abbrev dk (c : Cfg) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x1) c.C.len)

/-- The result the contract asks for: the specification's public key of `d`,
`04 ‖ x ‖ y`, and `1`, or zeros and `0`. -/
def PkPost (c : Cfg) (s₀ s' : State) : Prop :=
  match Spec.EcKey.publicKey c.C (dk c s₀) with
  | some (.affine x y) => (s'.gpr .x0).setWidth 32 = 1 ∧
      Spec.Ecdsa.bytesAt s'.mem (s₀.gpr .x0) (1 + 2 * c.C.len) = Spec.EcKey.encodePoint (.affine x y)
  | _ => (s'.gpr .x0).setWidth 32 = 0 ∧
      Spec.Ecdsa.bytesAt s'.mem (s₀.gpr .x0) (1 + 2 * c.C.len) = List.replicate (1 + 2 * c.C.len) 0

theorem args_ok (s : State) :
    WP isa (.block Impl.EcKey.AArch64.Cfg.args) s fun s' =>
      s'.gpr .x4 = s.gpr .x2 ∧ s'.gpr .x3 = s.gpr .x1 ∧ s'.gpr .x2 = s.gpr .x1 ∧
        Keeps [.x2, .x3, .x4] s s' := by
  apply WP.of_runBlock
  simp only [Impl.EcKey.AArch64.Cfg.args, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (0 : Nat) < 4096 by decide, ite_true, RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero,
    reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

/-- `vg_ec_<curve>_public_key` computes the specification's public key and
restores the callee-saved registers. -/
theorem publicKeyWith_ok (hc : CfgOk c) (hC : Law c.C) (comb : Prog isa)
    (hcomb : CombCorrect c comb) {s₀ : State} (hp : PkPre c s₀) :
    WP isa (Impl.EcKey.AArch64.Cfg.publicKeyWith c comb) s₀ fun s' =>
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s₀.gpr r) ∧ PkPost c s₀ s' := by
  have h0 := hc.n0
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  refine WP.seq (WP.mono_syms (args_ok s₀) fun s₁ ⟨x4₁, x3₁, x2₁, k₁⟩ sy₁ => ?_)
  have x1₁ : s₁.gpr .x1 = s₀.gpr .x1 := k₁.gpr _ (by decide)
  have x0₁ : s₁.gpr .x0 = s₀.gpr .x0 := k₁.gpr _ (by decide)
  -- The signature's regions, `k`, `d` and the hash all at `d`.
  obtain ⟨sN, hsN⟩ : ∃ sN, sN = s₁.withRegions
      [⟨s₀.gpr .x1, c.C.len⟩, ⟨s₀.gpr .x1, c.C.len⟩, ⟨s₀.gpr .x1, c.C.len⟩,
        ⟨s₀.syms c.tsym, 8 * c.combWords.length⟩]
      [⟨s₀.gpr .x0, 2 * c.C.len⟩, ⟨s₀.gpr .x2, size⟩] := ⟨_, rfl⟩
  have g : ∀ r, sN.gpr r = s₁.gpr r := fun r => by rw [hsN]; rfl
  have mN : sN.mem = s₀.mem := by rw [hsN]; exact k₁.mem
  have sN₁ : sN.syms = s₀.syms := by rw [hsN]; exact sy₁
  have hsub : Region.Sub ⟨s₀.gpr .x0, 2 * c.C.len⟩ ⟨s₀.gpr .x0, 1 + 2 * c.C.len⟩ := Region.sub_prefix (by omega)
  have od : Region.Disjoint ⟨s₀.gpr .x0, 2 * c.C.len⟩ ⟨s₀.gpr .x1, c.C.len⟩ := hp.out_d.sub_left hsub
  have dsc : Region.Disjoint ⟨s₀.gpr .x1, c.C.len⟩ ⟨s₀.gpr .x2, size⟩ := hp.d_sc
  have hpN : Pre c sN := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩ <;>
      simp only [g, x1₁, x0₁, x2₁, x3₁, x4₁, mN, sN₁]
    · rw [hsN]; rfl
    · rw [hsN]; rfl
    · exact hp.out_sc.sub_left hsub
    · exact od
    · exact od
    · exact od
    · exact dsc
    · exact dsc
    · exact dsc
    · have := hp.out_fit; omega
    · exact hp.sc_fit
    · rw [hsN]; simp
    · exact hp.tbl.held
    · exact hp.tbl.fit
    · exact hp.tbl.sc
  have hb : sN.gpr .x4 = s₀.gpr .x2 := by rw [g, x4₁]
  obtain ⟨t, s₂N, ex, S₂⟩ := stage₁ hc (.inl rfl) (hpN.setup hc)
    (rest := .seq comb (.seq c.pPow (.block [])))
    (Q := St₂ c none sN (sN.gpr .x4)) fun _ S₁ => stage₂_with hc comb hcomb hpN.tbl S₁ fun _ S₂ => WP.block_nil S₂
  rw [hb] at S₂
  -- The same run, with the public key's regions.
  have hrd₁ : s₁.rd = [⟨s₀.gpr .x1, c.C.len⟩, ⟨s₀.syms c.tsym, 8 * c.combWords.length⟩] := by rw [k₁.rd, hp.rd]
  have hwr₁ : s₁.wr = [⟨s₀.gpr .x0, 1 + 2 * c.C.len⟩, ⟨s₀.gpr .x2, size⟩] := by rw [k₁.wr, hp.wr]
  have ex' := Exec.widen ex (rd := s₁.rd) (wr := s₁.wr)
    (by
      rw [hsN, State.withRegions_rd, State.withRegions_wr, hrd₁, hwr₁]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., 0, (BitVec.add_zero _).symm, Nat.le_of_eq (Nat.zero_add _)⟩
      · exact ⟨_, List.mem_cons_self .., 0, (BitVec.add_zero _).symm, Nat.le_of_eq (Nat.zero_add _)⟩
      · exact ⟨_, List.mem_cons_self .., 0, (BitVec.add_zero _).symm, Nat.le_of_eq (Nat.zero_add _)⟩
      · exact ⟨⟨s₀.syms c.tsym, 8 * c.combWords.length⟩, by simp, 0, (BitVec.add_zero _).symm,
          Nat.le_of_eq (Nat.zero_add _)⟩
      · exact ⟨⟨s₀.gpr .x0, 1 + 2 * c.C.len⟩, by simp, 0, (BitVec.add_zero _).symm,
          by show 0 + 2 * c.C.len ≤ 1 + 2 * c.C.len; omega⟩
      · exact ⟨⟨s₀.gpr .x2, size⟩, by simp, 0, (BitVec.add_zero _).symm, Nat.le_of_eq (Nat.zero_add _)⟩)
    (by
      rw [hsN, State.withRegions_wr, hwr₁]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨s₀.gpr .x0, 1 + 2 * c.C.len⟩, List.mem_cons_self .., 0, (BitVec.add_zero _).symm,
          by show 0 + 2 * c.C.len ≤ 1 + 2 * c.C.len; omega⟩
      · exact ⟨⟨s₀.gpr .x2, size⟩, by simp, 0, (BitVec.add_zero _).symm, Nat.le_of_eq (Nat.zero_add _)⟩)
  rw [hsN, State.withRegions_withRegions, State.withRegions_self] at ex'
  obtain ⟨s₂, hs₂⟩ : ∃ s₂, s₂ = s₂N.withRegions s₁.rd s₁.wr := ⟨_, rfl⟩
  rw [← hs₂] at ex'
  have g₂ : s₂.gpr = s₂N.gpr := by rw [hs₂]; rfl
  have m₂ : s₂.mem = s₂N.mem := by rw [hs₂]; rfl
  have w₂ : s₂.wr = s₁.wr := by rw [hs₂]; rfl
  have sv₂ : ∀ i, sv c (s₀.gpr .x2) s₂ i = sv c (s₀.gpr .x2) s₂N i := fun i => by rw [sv, sv, m₂]
  have hs₂' : Scr s₂ (s₀.gpr .x2) size :=
    ⟨by rw [g₂]; exact S₂.scr.x0, by rw [w₂, hwr₁]; simp, S₂.scr.nowrap, S₂.scr.enc⟩
  have F₂ : Fixed c (s₀.gpr .x2) sN.gpr s₂.mem := m₂ ▸ S₂.fixed
  obtain ⟨t', s', exm, xv, yv, hxl, hx, hyl, hy, bytes, rax, saved⟩ :=
    middle_ok hc hs₂' F₂ (by rw [sv₂]; exact S₂.acc_lt) (by rw [m₂]; exact S₂.flag)
      (by rw [g₂, S₂.x20, g, x0₁]) hp.out_fit (by rw [w₂, hwr₁]; simp) hp.out_sc
  refine ⟨_, _, .seq ex' exm, fun r hr => ?_, ?_⟩
  · have hsv : ∀ r ∈ Cfg.saved.map Prod.fst, r ∉ [Reg.x2, .x3, .x4] := by decide
    rw [saved r hr, g, k₁.gpr r (hsv r hr)]
  -- The specification.
  have hk : kv c sN = dk c s₀ := by simp only [kv, dk, mN, g, x3₁]
  have hD : sv c (s₀.gpr .x2) s₂ D = dk c s₀ := by
    rw [sv₂, S₂.d, shAt_none, Nat.shiftRight_zero]; simp only [dv, dk, mN, g, x1₁]
  have hR := S₂.rep
  rw [hk] at hR
  have hZ : ∀ {i}, tmv c.C c.n (s₀.gpr .x2) s₂N (c.sl i) = toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .x2) s₂ i) :=
    fun {i} => by rw [sv₂]
  have acc := S₂.acc
  rw [← sv₂, hZ] at acc
  rw [hZ, hZ, hZ] at hR
  have hxX : Fin.ofNat c.C.p xv = toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .x2) s₂ RX) *
      toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .x2) s₂ RZ) ^ (c.C.p - 2) := by rw [hx, acc]
  have hyY : Fin.ofNat c.C.p yv = toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .x2) s₂ RY) *
      toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .x2) s₂ RZ) ^ (c.C.p - 2) := by rw [hy, acc]
  have hz := toM_eq_zero_iff hpR (x := sv c (s₀.gpr .x2) s₂ RZ) (by rw [sv₂]; exact S₂.rz_lt)
  unfold PkPost
  rw [publicKey_eq hC hR hxl hxX hyl hyY]
  by_cases hd : 1 ≤ dk c s₀ ∧ dk c s₀ < c.C.n
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hd)]
    by_cases h0 : sv c (s₀.gpr .x2) s₂ RZ = 0
    · have hok : ok c (s₀.gpr .x2) s₂ = false := decide_eq_false (by rw [hD]; omega)
      rw [ite_eq_left_of_eq_true _ _ (eq_true (hz.mpr h0))]
      exact ⟨by rw [rax, hok]; rfl, by rw [bytes, hok]; rfl⟩
    · have hok : ok c (s₀.gpr .x2) s₂ = true := decide_eq_true (by rw [hD]; omega)
      rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => h0 (hz.mp h)))]
      refine ⟨by rw [rax, hok]; rfl, ?_⟩
      rw [bytes, hok]
      rfl
  · have hok : ok c (s₀.gpr .x2) s₂ = false := decide_eq_false (by rw [hD]; omega)
    rw [ite_eq_right_of_eq_false _ _ (eq_false hd)]
    exact ⟨by rw [rax, hok]; rfl, by rw [bytes, hok]; rfl⟩

theorem publicKey_ok (hc : CfgOk c) (hC : Law c.C)
    (hT : CombOkW c.C Cfg.combW (Cfg.combJ c.n) c.tbl c.start) {s₀ : State} (hp : PkPre c s₀) :
    WP isa (Impl.EcKey.AArch64.Cfg.publicKey c) s₀ fun s' =>
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s₀.gpr r) ∧ PkPost c s₀ s' :=
  publicKeyWith_ok hc hC _ (combCorrect hc hC hT) hp

end VG.Proof.EcKey.AArch64
