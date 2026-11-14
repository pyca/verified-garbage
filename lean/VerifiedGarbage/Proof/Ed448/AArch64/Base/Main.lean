module

public import VerifiedGarbage.Proof.Ed448.AArch64.BaseContract
public import VerifiedGarbage.Proof.Ed448.AArch64.CombSum
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Lit
public import VerifiedGarbage.Proof.X448.AArch64.Mem
public import Mathlib.Tactic.NormNum.Prime
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Combine
import VerifiedGarbage.Proof.Ed448.AArch64.BaseEncode
import VerifiedGarbage.Proof.X448.AArch64.Base.Add
import VerifiedGarbage.Proof.X448.AArch64.Fast.Finish
public import VerifiedGarbage.Proof.X448.AArch64.Fast.Inv
public import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Impl.Ed448.AArch64.ScalarBase
public import VerifiedGarbage.Proof.Ed448.Formulas
import VerifiedGarbage.Proof.X448.AArch64.BitWrite
import VerifiedGarbage.Proof.X448.AArch64.Finish
import VerifiedGarbage.Proof.X448.AArch64.Weak.Main
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Impl.Curve448.AArch64.Neon
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.Impl.X448.AArch64.Field56
public import VerifiedGarbage.Proof.X448.AArch64.Fast.Env
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Spec.Ed448
public import VerifiedGarbage.TCB.Code
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.Proof.X448.AArch64.Fast.Setup
public import VerifiedGarbage.Proof.X448.AArch64.Env
public import VerifiedGarbage.Proof.X448.AArch64.Setup
public import VerifiedGarbage.Proof.X448.AArch64.Weak.Env
public import VerifiedGarbage.Spec.X448
import VerifiedGarbage.Proof.X448.AArch64.Iter
import VerifiedGarbage.Proof.Ed448.AArch64.CombBase
import Mathlib.FieldTheory.Finite.Basic
import VerifiedGarbage.Proof.X448.AArch64.Main
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.X448.AArch64.Base.Step
public import VerifiedGarbage.Proof.X448.AArch64.BitBody
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.X448.AArch64.Base.Setup
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-! ### `Ed448.AArch64.Base.Encode`, which only this module used -/

section

/-!
# Ed448 base-point multiplication on AArch64: the encoding

Untrusted: everything here is checked by Lean. `encode`, for `R = (X : Y : Z)`
in slots 0–2 (`encode_ok`): `Z` inverted into `T7` (slot 21, `invert_ok`);
`Y` kept in slot 3 and `x = X/Z` fully reduced in `X2` (slot 1), its low bit
stored as the top bit of the output's byte 56 (`signByte_ok`); then `Y` back
in `X2`, and X448's `finish` writes `Y/Z` fully reduced to the output's first
56 bytes and restores the registers. Together, the 57 bytes are
`encodePoint R` (`encodePoint_code`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Base

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (ld st slot X2 T7 ACC)
open VG.Impl.X448.AArch64.Fast (saved)
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 Saved ofs FieldMem writeW8_apply
  moveOutput_ok freeze_ok)
open VG.Proof.X448.AArch64.Weak (Index Env E_update E_outside)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd FKeep Same SavedX SavedV invert_ok invEnv invEnv_eval invEnv_x2
  invEnv_keep IKeep env_update block_codeOf
  mulOp)
open VG.Proof.X448.AArch64.Base (copyOp)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- The inversion's addition chain keeps slots 0 and 3. -/
theorem invEnv_0 (e : Env) : invEnv e 0 = e 0 := invEnv_keep e 0 (by decide)
/-- A fully reduced slot (sixteen limbs below `2^28`) is below `Ib`. -/
theorem bnd_of_bounded {m : Mem} {base : Addr} {o : Nat} (h : VG.Proof.X448.AArch64.Bounded m base o) :
    Bnd Ib m base o := fun i hi => Nat.lt_trans (h i (by omega_using [hi])) (by decide)

/-- `encode`: the 57 bytes at `p` are the encoding of `R` (slots 0–2), and the
registers are restored from the working space. -/
theorem encode_ok {s : State} {base p : Addr} (hs : Scr s base) (hb : BEnv s.mem base)
    (hp : s.gpr .x20 = p) (hw : ∀ j < 57, InRegions s.wr (off p j) 1)
    (hpd : ∀ j < 57, 8192 ≤ ofs base (off p j)) (hfar : ∀ j < 8192, 57 ≤ ofs p (off base j))
    {g : Reg → BitVec 64} (sv : Saved base g s.mem) (svx : SavedX base g s.mem)
    {gv : VReg → BitVec 128} (svV : SavedV base gv s.mem) :
    WP isa encode s fun t =>
      t.gpr .x19 = g .x19 ∧ t.gpr .x20 = g .x20 ∧ (∀ k < 8, t.gpr (saved k) = g (saved k)) ∧
      (∀ k < 8, (t.v (VG.Impl.Curve448.AArch64.Neon.V (8 + k))).extractLsb' 0 64 =
        (gv (VG.Impl.Curve448.AArch64.Neon.V (8 + k))).extractLsb' 0 64) ∧
      t.gpr .x30 = s.gpr .x30 ∧ Frame [⟨base, 8192⟩, ⟨p, 57⟩] s.mem t.mem ∧
      Spec.Ed448.bytesAt t.mem p 57 = Spec.Ed448.encodePoint (pt (EV s.mem base) 0 1 2) := by
  have far56 : 8192 ≤ ofs base (p + BitVec.ofNat 64 56) := hpd 56 (by decide)
  have fr : ∀ {m m' : Mem}, Outside base 0 8192 m m' → Frame [⟨base, 8192⟩, ⟨p, 57⟩] m m' :=
    fun h => (VG.Proof.X448.AArch64.Outside.frame h).mono (by simp)
  rw [encode]
  -- `1/Z` into `T7`.
  refine WP.seq (WP.mono (invert_ok hs hb) fun s1 ⟨k1, b1, e1⟩ => ?_)
  have hs1 : Scr s1 base := hs.of_keeps k1.regs (by decide)
  refine WP.seq ?_
  unfold sign
  rw [WP.seq_iff]
  -- The output pointer.
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (moveOutput_ok s1) fun s2 ⟨x2, m2, k2⟩ => ?_
  have hs2 : Scr s2 base := hs1.of_keeps k2 (by decide)
  have b2 : BEnv s2.mem base := by rw [m2]; exact b1
  -- `Y` to slot 3, and `X/Z` into `X2`.
  refine block_codeOf (copyOp hs2 b2 3 1 fun s3 k3 b3 _ _ e3 => WP.block_nil ?_)
  rw [WP.seq_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.Point56.mulCallKE (k3.scr hs2) b3 1 0 21 (by decide))
    fun s4 ⟨k4, b4, m4, _, e4⟩ => ?_
  replace e4 : EV s4.mem base = Function.update (EV s3.mem base) 1 (EV s3.mem base 0 * EV s3.mem base 21) := e4
  have hs4 : Scr s4 base := k4.scr (k3.scr hs2)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.toLegacy_ok' hs4 (o := X2) (by decide) (by decide)
    (fun i hi => Nat.lt_trans (m4 i hi) (by decide))) fun s5 ⟨c5, l5, v5⟩ => ?_
  have hs5 := hs4.of_keeps c5.1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok hs5 l5) fun s6 ⟨l6, v6, m6, k6⟩ => ?_
  have hs6 := hs5.of_keeps k6 (by decide)
  have x6 : s6.gpr .x1 = p := by
    rw [k6.1 _ (by decide), c5.1.1 _ (by decide), k4.regs.1 _ (by decide), k3.regs.1 _ (by decide), x2,
      k1.regs.1 _ (by decide), hp]
  have w6 : s6.wr = s.wr := by
    rw [k6.2.2, c5.1.2.2, k4.regs.2.2, k3.regs.2.2, k2.2.2, k1.regs.2.2]
  -- The sign byte.
  rw [WP.block_append_iff]
  refine WP.mono (signByte_ok hs6 x6 (by rw [w6]; exact hw 56 (by decide))) fun s7 ⟨m7, k7⟩ => ?_
  have hs7 := hs6.of_keeps k7 (by decide)
  have o67 : Outside base 8192 (2 ^ 64) s6.mem s7.mem := fun x hx => by
    rw [m7, writeW8_apply, ite_eq_right_iff.mpr]
    intro h; subst h
    have hlt := (p + BitVec.ofNat 64 56 - base).isLt
    simp only [ofs] at far56 hx
    omega
  have f46 : FieldMem base X2 s4.mem s6.mem := c5.2.trans m6
  have e6 : EV s6.mem base = Function.update (EV s4.mem base) 1
      (VG.Proof.X448.AArch64.Weak.F s6.mem base X2) := E_update f46
  have e76 : ∀ i : Index, EV s7.mem base i = EV s6.mem base i := fun i =>
    E_outside o67 i (Or.inl (by have := i.isLt; simp only [slot]; omega_using []))
  have b7 : BEnv s7.mem base := by
    intro i j hj
    rw [o67.limbs (Or.inl (by have := i.isLt; simp only [slot]; omega_using []))
      (by have := i.isLt; simp only [slot]; omega_using []) (by omega_using [hj])]
    by_cases hi : i = 1
    · subst hi; exact bnd_of_bounded l6 j hj
    · rw [f46.limbs (VG.Proof.X448.AArch64.Weak.slot_sep hi) (by have := i.isLt; simp only [slot, ACC]; omega_using [])
        (by omega_using [hj])]
      exact b4 i j hj
  -- `Y` back in `X2`.
  refine block_codeOf (copyOp hs7 b7 1 3 fun s8 k8 b8 _ _ e8 => WP.block_nil ?_)
  have hs8 : Scr s8 base := k8.scr hs7
  have x8 : s8.gpr .x1 = p := by rw [k8.regs.1 _ (by decide), k7.1 _ (by decide)]; exact x6
  have w8 : s8.wr = s.wr := by rw [k8.regs.2.2, k7.2.2]; exact w6
  -- The saved registers, through the operations since the entry.
  have o16 : Outside2 base 64 2816 ACC 1152 s.mem s6.mem :=
    (((k1.mem.trans (by rw [m2]; exact Outside2.refl _ _ _ _ _ _)).trans k3.mem).trans k4.mem).trans
      (VG.Proof.X448.AArch64.Fast.fieldMem_outside2 (o := 1) f46)
  have sv8 : Saved base g s8.mem :=
    ((sv.outside2 o16 (by decide) (by decide)).outside o67 (by decide)).outside2 k8.mem (by decide) (by decide)
  have svx8 : SavedX base g s8.mem :=
    ((svx.outside2 o16 (by decide) (by decide)).outside o67 (Or.inr (by decide))).outside2 k8.mem
      (by decide) (by decide)
  have svV8 : SavedV base gv s8.mem :=
    ((svV.outside2 o16 (by decide) (by decide)).outside o67 (Or.inr (by decide))).outside2 k8.mem
      (by decide) (by decide)
  refine WP.mono (VG.Proof.X448.AArch64.Fast.finish_ok hs8 b8 x8 (fun j hj => by rw [w8]; exact hw j (by omega_using [hj]))
    (fun j hj => Nat.le_trans (by decide) (hfar j hj)) sv8 svx8 svV8)
    fun t ⟨t19, t20, tx, tv, kt, ft, vt⟩ => ⟨t19, t20, tx, tv, ?_, ?_, ?_⟩
  · rw [kt.1 _ (by decide), k8.regs.1 _ (by decide), k7.1 _ (by decide), k6.1 _ (by decide),
      c5.1.1 _ (by decide), k4.regs.1 _ (by decide), k3.regs.1 _ (by decide), k2.1 _ (by decide),
      k1.regs.1 _ (by decide)]
  · -- Only the working space and the output change.
    have f67 : Frame [⟨base, 8192⟩, ⟨p, 57⟩] s6.mem s7.mem := by
      rw [m7]
      refine (Frame.refl _ _).writeW (r := ⟨p, 57⟩) (by simp) _ ?_
      simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
      omega_using []
    have ft' : Frame [⟨base, 8192⟩, ⟨p, 57⟩] s8.mem t.mem := fun x hx => ft x fun r hr hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hx _ (by simp) hc
      · exact hx ⟨p, 57⟩ (by simp) (by simp only [Region.Contains] at hc ⊢; omega_using [hc])
    exact (((fr (o16.whole (by decide) (by decide))).trans f67).trans
      (fr (k8.mem.whole (by decide) (by decide)))).trans ft'
  · -- The values.
    have v1 : EV s8.mem base 1 = EV s.mem base 1 := by
      simp only [e8, e76, e6, e4, e3, m2, e1, VG.Proof.X448.AArch64.opCopy, Function.update_apply, invEnv_x2, Fin.reduceEq,
        ↓reduceIte]
    have v21 : EV s8.mem base 21 = Proof.X448.invert (EV s.mem base 2) := by
      simp only [e8, e76, e6, e4, e3, m2, e1, VG.Proof.X448.AArch64.opCopy, Function.update_apply, invEnv_eval, Fin.reduceEq,
        ↓reduceIte]
    have vx : VG.Proof.X448.AArch64.F s5.mem base X2 = EV s.mem base 0 * Proof.X448.invert (EV s.mem base 2) := by
      rw [v5]
      change EV s4.mem base 1 = _
      simp only [e4, e3, m2, e1, VG.Proof.X448.AArch64.opCopy, Function.update_apply, invEnv_0, invEnv_eval, Fin.reduceEq,
        ↓reduceIte]
    -- The sign: the low bit of `x`, fully reduced.
    have sgn : (word s6.mem base X2).toNat % 2 =
        (EV s.mem base 0 * Proof.X448.invert (EV s.mem base 2)).val % 2 := by
      rw [← vx]
      have hv : (VG.Proof.X448.AArch64.F s5.mem base X2).val =
          VG.Proof.X448.AArch64.fe s5.mem base X2 % Spec.X448.P := rfl
      rw [hv, ← v6, show VG.Proof.X448.AArch64.fe s6.mem base X2 =
        VG.Proof.X448.valN (limbs s6.mem base X2) 16 from rfl, VG.Proof.Ed448.AArch64.valN_mod_two]
      rfl
    have byte : t.mem (p + BitVec.ofNat 64 56) = BitVec.ofNat 8 (128 * ((EV s.mem base 0 *
        Proof.X448.invert (EV s.mem base 2)).val % 2)) := by
      have hout : ∀ r ∈ ([⟨base, 8192⟩, ⟨p, 56⟩] : List Region), ¬ r.Contains (p + BitVec.ofNat 64 56) 1 := by
        intro r hr hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · simp only [Region.Contains] at hc
          simp only [ofs] at far56
          omega_using [far56, hc]
        · simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat] at hc
          omega_using [hc]
      rw [ft _ hout]
      rw [show s8.mem (p + BitVec.ofNat 64 56) = s7.mem (p + BitVec.ofNat 64 56) from
        k8.mem _ (by simp only [ofs] at far56 ⊢; omega_using [far56]) (by simp only [ofs, ACC] at far56 ⊢; omega_using [far56])]
      rw [m7, writeW8_apply]
      simp only [ite_true, sgn]
    rw [VG.Proof.Ed448.AArch64.bytesAt_57, vt, byte, VG.Proof.X448.encodeUCoordinate_eq, v1, v21]
    exact (VG.Proof.Ed448.encodePoint_code _ _ _).symm

end VG.Proof.Ed448.AArch64.Base

end

end

/-! ### `Ed448.AArch64.BaseBits`, which only this module used -/

section

/-!
# Ed448 base-point multiplication on AArch64: the scalar's bits

`bits`: the 57 bytes of the scalar, each expanded into its eight bits at
`BITS` (byte `t` is bit `t`, X448's `bitHead` and `bitJ`), counting `x19`
up to 57; then the output pointer into `x1`.
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keeps off Outside ofs bitHead bitJ bitHead_ok byteBits_ok bitRegs
  moveOutput_ok)
open VG.Impl.X448.AArch64 (BITS)
open VG.Spec.Ed448 (bytesAt decodeLE)

theorem bitTail_ok {s : State} {i : Nat} (hi : i < 57) (hb : s.gpr .x19 = BitVec.ofNat 64 i) :
    WP isa (.block ([.addImm .x .x19 .x19 1, .subImm .x .x11 .x19 57] : List Instr)) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (i + 1) ∧ (t.gpr .x11 == 0) = decide (i + 1 = 57) ∧
      t.mem = s.mem ∧ Keeps [.x19, .x11] s t := by
  have check : ∀ n < 57,
      ((BitVec.ofNat 64 n + BitVec.ofNat 64 1 - BitVec.ofNat 64 57) == 0) = decide (n + 1 = 57) :=
    by decide +kernel
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Nat.reduceLT, BitVec.setWidth_eq, RegUpd.gpr_write, hb, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨(BitVec.ofNat_add _ _).symm, check i hi, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem bitsBody_ok {s : State} {base k : Addr} (hs : Scr s base) (hk : s.gpr .x1 = k)
    {i : Nat} (hi : i < 57) (hb : s.gpr .x19 = BitVec.ofNat 64 i) (hc : s.gpr .x8 = 1)
    (hkr : InRegions (s.rd ++ s.wr) (off k i) 1) :
    WP isa (.block bitsBody) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (i + 1) ∧ (t.gpr .x11 == 0) = decide (i + 1 = 57) ∧
      t.gpr .x8 = 1 ∧ Keeps bitRegs s t ∧
      (∀ j < 8, t.mem (off base (BITS + (8 * i + j))) =
        BitVec.ofNat 8 (((s.mem (off k i)).toNat >>> j) &&& 1)) ∧
      Outside base (BITS + 8 * i) 8 s.mem t.mem := by
  change WP isa (.block (bitHead ++ (List.range 8).flatMap bitJ ++
    ([.addImm .x .x19 .x19 1, .subImm .x .x11 .x19 57] : List Instr))) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (bitHead_ok hs hk hb hkr) fun t ⟨ta, tp, tm, tk⟩ => ?_
  have tc : t.gpr .x8 = 1 := (tk.1 _ (by decide)).trans hc
  rw [WP.block_append_iff]
  refine WP.mono (byteBits_ok (hs.of_keeps tk (by decide)) hi tp tc ta) fun u ⟨uf, um, uk⟩ => ?_
  have ub : u.gpr .x19 = BitVec.ofNat 64 i := (uk.1 _ (by decide)).trans ((tk.1 _ (by decide)).trans hb)
  refine WP.mono (bitTail_ok hi ub) fun v ⟨vb, vz, vm, vk⟩ => ?_
  refine ⟨vb, vz, (vk.1 _ (by decide)).trans ((uk.1 _ (by decide)).trans tc), ?_, ?_, ?_⟩
  · refine (tk.mono ?_).trans ((uk.mono ?_).trans (vk.mono ?_))
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide
    · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide
  · rw [vm]; exact uf
  · rw [vm, ← tm]; exact um

/-- The loop's invariant, after `i` bytes. -/
structure BInv (base k : Addr) (s₀ s : State) (i : Nat) : Prop where
  scr : Scr s base
  x1 : s.gpr .x1 = k
  x19 : s.gpr .x19 = BitVec.ofNat 64 i
  one : s.gpr .x8 = 1
  gpr : ∀ r, r ∉ bitRegs → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base BITS 456 s₀.mem s.mem
  bits : ∀ t < 8 * i, s.mem (off base (BITS + t)) =
    BitVec.ofNat 8 (((s₀.mem (k + BitVec.ofNat 64 (t / 8))).toNat >>> (t % 8)) &&& 1)

theorem bitsLoop_ok {s₀ : State} {base k : Addr}
    (hkr : ∀ q < 57, InRegions (s₀.rd ++ s₀.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 57, 8192 ≤ ofs base (k + BitVec.ofNat 64 q)) :
    ∀ i, ∀ s, i < 57 → BInv base k s₀ s i →
      WP isa (.loop (.block bitsBody) (.nonzero .x .x11)) s fun s' => BInv base k s₀ s' 57 := by
  intro i s hi hb
  refine WP.loop (M := isa) (body := .block bitsBody) (c := .nonzero .x .x11)
    (Q := fun s' => BInv base k s₀ s' 57)
    (fun m (s : State) => ∃ i, m = 57 - i ∧ i < 57 ∧ BInv base k s₀ s i) ?_ (57 - i) s ⟨i, rfl, hi, hb⟩
  rintro m s ⟨i, rfl, hi, hb⟩
  refine WP.mono (bitsBody_ok hb.scr hb.x1 hi hb.x19 hb.one (by rw [hb.rd, hb.wr]; exact hkr i hi))
    fun s' ⟨b', z', one', keep', bits', o'⟩ => ?_
  obtain ⟨g', rd', wr'⟩ := keep'
  have hbyte : s.mem (k + BitVec.ofNat 64 i) = s₀.mem (k + BitVec.ofNat 64 i) :=
    hb.mem _ (by have := hkd i hi; simp only [BITS]; omega_using [this])
  have inv : BInv base k s₀ s' (i + 1) := by
    refine ⟨⟨(g' _ (by decide)).trans hb.scr.x3, (g' _ (by decide)).trans hb.scr.mask, wr' ▸ hb.scr.wr,
      hb.scr.nowrap⟩, (g' _ (by decide)).trans hb.x1, b', one', fun r hr => (g' r hr).trans (hb.gpr r hr),
      rd'.trans hb.rd, wr'.trans hb.wr, hb.mem.trans (o'.mono (by omega_using []) (by omega_using [hi])),
      fun t ht => ?_⟩
    rcases Nat.lt_or_ge t (8 * i) with h | h
    · have hofs : ofs base (off base (BITS + t)) = BITS + t :=
        Mem.sub_ofNat_toNat base (by simp only [BITS]; omega_using [hi, ht])
      rw [o' _ (by rw [hofs]; omega_using [h]), hb.bits t h]
    · have e := bits' (t - 8 * i) (by omega_using [ht])
      rw [show 8 * i + (t - 8 * i) = t by omega_using [h], hbyte] at e
      rw [e, show t / 8 = i by omega_using [ht, h], show t % 8 = t - 8 * i by omega_using [ht, h]]
  simp only [eval, State.read, BitVec.setWidth_eq, bne, z']
  rcases Nat.lt_or_ge (i + 1) 57 with h | h
  · exact .inr ⟨by simp only [decide_eq_false (by omega_using [h] : ¬i + 1 = 57), Bool.not_false],
      57 - (i + 1), by omega_using [hi], i + 1, rfl, h, inv⟩
  · obtain rfl : i = 56 := by omega_using [hi, h]
    exact .inl ⟨rfl, inv⟩

/-- `bits`: byte `t` of `BITS` is bit `t` of the scalar, for `t < 456`; then
`x1` is the output pointer, from `x20`. -/
theorem bits_ok {s : State} {base k : Addr} (hs : Scr s base) (hk : s.gpr .x1 = k)
    (hkr : ∀ q < 57, InRegions (s.rd ++ s.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 57, 8192 ≤ ofs base (k + BitVec.ofNat 64 q)) :
    WP isa bits s fun s' =>
      s'.gpr .x1 = s.gpr .x20 ∧ (∀ r, r ∉ .x1 :: bitRegs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ Outside base BITS 456 s.mem s'.mem ∧
      ∀ t < 456, s'.mem (off base (BITS + t)) =
        BitVec.ofNat 8 ((decodeLE (bytesAt s.mem k 57) >>> t) &&& 1) := by
  rw [bits]
  refine WP.seq (WP.mono (show WP isa (.block [.movz .x .x19 0 0, .movz .x .x8 1 0]) s
      (fun s' => BInv base k s s' 0) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
      Option.some.injEq, exists_eq_left']
    refine ⟨⟨?_, ?_, hs.wr, hs.nowrap⟩, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl,
      VG.Proof.X448.AArch64.Outside.refl _ _ _ _, fun t ht => absurd ht (by omega_using [])⟩
    · simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using hs.x3
    · simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using hs.mask
    · simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using hk
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true]; rfl
    · rw [RegUpd.gpr_write_self]; rfl
    · have h19 : r ≠ .x19 := fun h => hr (by subst r; decide)
      have h8 : r ≠ .x8 := fun h => hr (by subst r; decide)
      simp only [RegUpd.gpr_write, h19, h8, ite_false]) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (bitsLoop_ok hkr hkd 0 s₁ (by omega_using []) h₁) fun s₂ h₂ => ?_)
  refine WP.mono (moveOutput_ok s₂) fun s₃ ⟨x1₃, m₃, k₃⟩ => ?_
  refine ⟨x1₃.trans (h₂.gpr _ (by decide)), fun r hr => ?_, k₃.2.1.trans h₂.rd, k₃.2.2.trans h₂.wr,
    by rw [m₃]; exact h₂.mem, fun t ht => ?_⟩
  · simp only [List.mem_cons, not_or] at hr
    rw [k₃.1 r (by simp only [List.mem_singleton]; exact hr.1)]
    exact h₂.gpr r (by simp only [bitRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢; exact hr.2)
  · rw [m₃, h₂.bits t (by omega_using [ht]), scalar_bit s.mem k ht]

end VG.Proof.Ed448.AArch64

end

end

/-!
# Ed448 base-point multiplication on AArch64: the whole function

Untrusted: everything here is checked by Lean. The correctness of
`vg_ed448_scalar_base` against `scalarBaseLocal` (`BaseContract.lean`): the
comb of 57 tables, by a call of `vg_ed448_r56_comb_base` (`CombBase.call_ok`), and `16 A + C`
(`Point56.combineCall_frame`) leave `R` representing `[k]B`, whose
encoding is `encodePoint (pointMul k B)` since both represent the same affine
point (`encodePoint_rep`); every write but the result's is in the working
space, so the scalar is read unchanged, and the callee-saved registers are
restored from it.
-/

-- Formerly `VerifiedGarbage/Proof/Ed448/AArch64/Base/Setup.lean`, which only this module imported.
section

/-!
# Ed448 base-point multiplication on AArch64: the setup

Untrusted: everything here is checked by Lean. X448's comb's `entry` (the
registers saved, every slot zeroed), the bits of all 57 bytes of the scalar
(`bits_ok`), and both accumulators at `[G] B` for `G = 8 Σ_{j < 57} 256^j`
(`baseG57`): `StepInv` of the comb of 57 tables, for step 0.
-/

section

namespace VG.Proof.Ed448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Impl.X448.AArch64.Base
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 Saved bitRegs ofs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast
open VG.Proof.X448.AArch64.Base (CombPre block1_ok)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.Ed448 (Rep baseAff)
open VG.Spec.Ed448 (bytesAt decodeLE)

/-- What the setup leaves, from the function's entry state `sE`. -/
structure CombReady (sE : State) (base : Addr) (k : Nat) (t : State) : Prop where
  pre : CombPre 57 base k t
  saved : Saved base sE.gpr t.mem
  out : t.gpr .x20 = sE.gpr .x0
  savedX : SavedX base sE.gpr t.mem
  savedV : SavedV base sE.v t.mem
  lr : t.gpr .x30 = sE.gpr .x30
  rd : t.rd = sE.rd
  wr : t.wr = sE.wr
  mem : Outside base 0 8192 sE.mem t.mem

theorem bytesAt_outside {base p : Addr} {m m' : Mem} (h : Outside base 0 8192 m m')
    (hp : ∀ i < 57, 8192 ≤ ofs base (p + BitVec.ofNat 64 i)) :
    bytesAt m' p 57 = bytesAt m p 57 := by
  rw [VG.Proof.Ed448.bytesAt_eq, VG.Proof.Ed448.bytesAt_eq]
  refine List.map_congr_left fun i hi => h _ (Or.inr ?_)
  simp only [List.mem_range] at hi
  exact hp i hi

theorem setup_ok {s : State} {base kp : Addr} (hb : s.gpr .x2 = base) (hw : (⟨base, 8192⟩ : Region) ∈ s.wr)
    (hn : base.toNat + 8192 ≤ 2 ^ 64) (hk : s.gpr .x1 = kp)
    (hkr : ∀ q < 57, InRegions (s.rd ++ s.wr) (kp + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 57, 8192 ≤ ofs base (kp + BitVec.ofNat 64 q))
    (htb : VG.Proof.X448.AArch64.Base.TblAt s base (s.syms VG.Impl.X448.AArch64.Base.combSym)) :
    WP isa VG.Impl.Ed448.AArch64.baseSetup s (CombReady s base (decodeLE (bytesAt s.mem kp 57))) := by
  unfold VG.Impl.Ed448.AArch64.baseSetup
  refine WP.seq (WP.mono_syms (block1_ok hb hw hn) fun a ⟨ha, sa, oa, xa, va, ka, za, outa⟩ sya => ?_)
  refine WP.mono_syms (VG.Proof.Ed448.AArch64.bits_ok ha (by rw [ka.1 _ (by decide)]; exact hk)
    (by rw [ka.2.1, ka.2.2]; exact hkr) hkd) fun t ⟨_, gb, rdb, wrb, ob, bitsb⟩ syb => ?_
  have kb : Keeps (.x1 :: bitRegs) a t := ⟨gb, rdb, wrb⟩
  have hsb : Scr t base := ha.of_keeps kb (by decide)
  rw [bytesAt_outside outa hkd] at bitsb
  have mt : Outside base 0 8192 s.mem t.mem := outa.trans (ob.mono (by omega) (by simp only [BITS]; omega))
  have htt : VG.Proof.X448.AArch64.Base.TblAt t base (t.syms VG.Impl.X448.AArch64.Base.combSym) := by
    rw [syb, sya]
    exact htb.of_far (by rw [kb.2.1, ka.2.1, kb.2.2, ka.2.2]) fun x hx => mt x (Or.inr hx)
  -- Every word outside the bits is as `block1` left it.
  have wt : ∀ {d : Nat}, d + 8 ≤ BITS ∨ BITS + 456 ≤ d → d + 8 ≤ 8192 →
      word t.mem base d = word a.mem base d := fun h2 h3 => ob.word h2 h3
  -- The slots `block1` zeroed.
  have zs : ∀ i : Index, ∀ w < 8, word a.mem base (slot i.val + 8 * w) = 0 := fun i w hw => by
    have := i.isLt
    have hz := za (16 * i.val + w) (by omega)
    have e : slot 0 + 8 * (16 * i.val + w) = slot i.val + 8 * w := by simp only [slot]; omega
    rw [show VG.Proof.X448.AArch64.limbs a.mem base (slot 0) (16 * i.val + w) =
      (word a.mem base (slot i.val + 8 * w)).toNat by
        simp only [VG.Proof.X448.AArch64.limbs]; rw [e]] at hz
    exact BitVec.eq_of_toNat_eq hz
  have zt : ∀ i : Index, ∀ w < 8, word t.mem base (slot i.val + 8 * w) = 0 := fun i w hw => by
    have := i.isLt
    rw [wt (by simp only [slot, BITS]; omega) (by simp only [slot]; omega)]
    exact zs i w hw
  refine ⟨⟨hsb, fun i w hw => ?_, fun w hw => ?_, fun q hq => bitsb q hq, htt⟩,
    ⟨by rw [wt (by decide) (by decide)]; exact sa.1,
      by rw [wt (by decide) (by decide)]; exact sa.2⟩,
    by rw [kb.1 _ (by decide)]; exact oa,
    fun k hk => by
      rw [wt (by simp only [Impl.X448.AArch64.Fast.SAVE, BITS]; omega)
        (by simp only [Impl.X448.AArch64.Fast.SAVE]; omega)]
      exact xa k hk,
    va.outside ob (by simp only [BITS, Impl.X448.AArch64.Fast.VSAVE]; omega),
    by rw [kb.1 _ (by decide), ka.1 _ (by decide)],
    by rw [kb.2.1, ka.2.1], by rw [kb.2.2, ka.2.2], mt⟩
  · show (word t.mem base (slot i.val + 8 * w)).toNat < Ib
    rw [zt i w hw]; decide
  · show (word t.mem base (slot (19 : Index).val + 8 * w)).toNat = 0
    rw [zt 19 w hw]; rfl

end VG.Proof.Ed448.AArch64.Base
end

end

@[expose] public section

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keeps off word Outside Outside2 Saved ofs far)
open VG.Proof.Ed448.AArch64.Base (setup_ok encode_ok)
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Spec.Ed448 (bytesAt decodeLE)

/-- A byte of the working space is beyond the output. -/
theorem far_out {base p : Addr} (hd : (⟨p, 57⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < 8192) : 57 ≤ ofs p (off base i) := by
  refine Nat.le_of_not_lt fun h => hd _ ?_ (Offset.contains_base base (d := i) (n := 1) (k := 8192) (by omega_using [hi]) (by omega_using [hi]))
  simp only [Region.Contains]
  change ofs p (off base i) + 1 ≤ 57
  omega_using [h]

theorem decodeLE_57_lt (kb : List Byte) (hk : kb.length = 57) : decodeLE kb < 256 ^ 57 := by
  have h := VG.Proof.Ed448.decodeLE_lt' kb
  rwa [hk] at h

theorem scalarBase_correct {s : State} (hp : scalarBaseLocal.pre s) :
    WP isa scalarBase s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
      (∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) ∧
      scalarBaseLocal.post s t := by
  have htb := hp.2.2.2.2.2.tblAt (base := s.gpr .x2)
    (by rw [hp.1]; exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    (by simp)
  obtain ⟨hr, hw, hdo, hds, hn, -⟩ := hp
  obtain ⟨base, hbase⟩ : ∃ b, s.gpr .x2 = b := ⟨_, rfl⟩
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw, hbase]; simp
  rw [hbase] at hn hdo hds htb
  have hkr : ∀ q < 57, InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 q) 1 := fun q hq =>
    ⟨⟨s.gpr .x1, 57⟩, by rw [hr]; simp, Offset.contains_base _ (by omega_using [hq]) (by omega_using [hq])⟩
  have hkd : ∀ q < 57, 8192 ≤ ofs base (s.gpr .x1 + BitVec.ofNat 64 q) := fun q hq => far hds hq (by decide)
  have hod : ∀ q < 57, 8192 ≤ ofs base (s.gpr .x0 + BitVec.ofNat 64 q) := fun q hq => far hdo hq (by decide)
  set kb := bytesAt s.mem (s.gpr .x1) 57
  set k := decodeLE kb
  unfold scalarBase
  refine WP.seq (WP.mono (setup_ok hbase hws hn rfl hkr hkd htb) fun s1 R => ?_)
  have f1 : VG.Proof.X448.AArch64.Base.Frame s1 base s1 :=
    ⟨R.pre.scr, R.pre.env, R.pre.zero, rfl, rfl, rfl, rfl, Outside2.refl _ _ _ _ _ _⟩
  refine WP.seq (WP.mono (CombBase.call_ok (Or.inr rfl) f1 R.pre) fun s2 ⟨f2, a2, c2⟩ => ?_)
  refine WP.seq (WP.mono (Point56.combineCall_frame f2 a2 c2) fun s3 ⟨f3, r3⟩ => ?_)
  rw [VG.Proof.X448.comb_total (decodeLE_57_lt kb (by simp [kb, VG.Proof.Ed448.bytesAt_eq,
    Spec.X25519.bytesAt]))] at r3
  -- The encoding.
  have out3 : s3.gpr .x20 = s.gpr .x0 := by rw [f3.out, R.out]
  have wr3 : s3.wr = s.wr := by rw [f3.wr, R.wr]
  have o13 : Outside2 base 64 2816 ACC 1152 s1.mem s3.mem := f3.mem
  refine WP.mono (encode_ok f3.scr f3.env out3
    (fun j hj => ⟨⟨s.gpr .x0, 57⟩, by rw [wr3, hw]; simp, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩)
    (fun j hj => hod j hj) (fun j hj => far_out hdo hj)
    (R.saved.outside2 o13 (by decide) (by decide)) (R.savedX.outside2 o13 (by decide) (by decide))
    (R.savedV.outside2 o13 (by decide) (by decide)))
    fun t ⟨t19, t20, tx, tv, t30, _, vt⟩ => ⟨?_, ?_, ?_⟩
  · intro r hr
    have lr : t.gpr .x30 = s.gpr .x30 := by rw [t30, f3.lr, R.lr]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact t19
    · exact t20
    · exact tx 0 (by decide)
    · exact tx 1 (by decide)
    · exact tx 2 (by decide)
    · exact tx 3 (by decide)
    · exact tx 4 (by decide)
    · exact tx 5 (by decide)
    · exact tx 6 (by decide)
    · exact tx 7 (by decide)
    · exact lr
  · intro r hr
    simp only [preservedV, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tv 0 (by decide)
    · exact tv 1 (by decide)
    · exact tv 2 (by decide)
    · exact tv 3 (by decide)
    · exact tv 4 (by decide)
    · exact tv 5 (by decide)
    · exact tv 6 (by decide)
    · exact tv 7 (by decide)
  · show bytesAt t.mem (s.gpr .x0) 57 = Spec.Ed448.scalarBase kb
    rw [vt, Spec.Ed448.scalarBase]
    change Spec.Ed448.encodePoint (VG.Proof.X448.AArch64.Base.pt _ 0 1 2) = _
    rw [VG.Proof.Ed448.encodePoint_rep r3,
      VG.Proof.Ed448.encodePoint_rep (VG.Proof.Ed448.pointMul_rep k VG.Proof.Ed448.basePoint_rep),
      natCast_zsmul]

end VG.Proof.Ed448.AArch64
