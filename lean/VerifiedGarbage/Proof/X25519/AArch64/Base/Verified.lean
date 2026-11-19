module

public import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseVerified
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarMemory
public import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseEngine
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.X25519.AArch64.Ladder
meta import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseVerified
meta import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarMemory
meta import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseEngine
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.X25519.AArch64.Ladder
public import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseMain
public import VerifiedGarbage.Spec.X25519.Contract
public import VerifiedGarbage.Impl.X25519.AArch64.Base
import VerifiedGarbage.Proof.Ed25519.AArch64.Codec
import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddCodec
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Ed25519.AArch64.Divstep
import VerifiedGarbage.Proof.Ed25519.AArch64.Bits
import VerifiedGarbage.Proof.X25519.Edwards.Base
public import VerifiedGarbage.Proof.Ed25519.AArch64.PointEncode
public import VerifiedGarbage.Proof.Ed25519.AArch64.CombEntry
public import VerifiedGarbage.Proof.Ed25519.AArch64.PointPowers
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Spec.Weierstrass
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import VerifiedGarbage.Proof.X25519.Edwards.Ladder
import VerifiedGarbage.Proof.X25519.AArch64.Ops
meta import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseMain
meta import VerifiedGarbage.Spec.X25519.Contract
meta import VerifiedGarbage.Impl.X25519.AArch64.Base
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Codec
meta import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddCodec
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import Mathlib.Tactic.NormNum.Prime
meta import Mathlib.Data.Nat.Totient
meta import Mathlib.Tactic.Positivity.Finset
meta import Mathlib.Algebra.Order.Field.Basic
meta import Mathlib.Tactic.NormNum.GCD
meta import Mathlib.Data.Sym.Sym2.Init
meta import Mathlib.Tactic.ContinuousFunctionalCalculus
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Divstep
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Bits
meta import VerifiedGarbage.Proof.X25519.Edwards.Base
meta import VerifiedGarbage.Proof.Ed25519.AArch64.PointEncode
meta import VerifiedGarbage.Proof.Ed25519.AArch64.CombEntry
meta import VerifiedGarbage.Proof.Ed25519.AArch64.PointPowers
meta import VerifiedGarbage.Spec.Ed25519.Contract
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Spec.Weierstrass
meta import Mathlib.Tactic.Ring.RingNF
meta import Mathlib.Tactic.FieldSimp
meta import Mathlib.Tactic.Ring
meta import VerifiedGarbage.Proof.X25519.Edwards.Ladder
meta import VerifiedGarbage.Proof.X25519.AArch64.Ops

/-! ### `X25519.AArch64.Base.Main`, which only this module used -/

section

/-! ### `X25519.AArch64.Base.Engine`, which this module and modules that import it used -/

section

/-! ### `Ed25519.AArch64.CombClamped`, which only this module used -/

section

/-!
# The comb of a scalar whose bits 0–2 are clear

Digit 0 of such a scalar is `8 b₃ - 8`. `combInitClamped` starts the accumulator at
`[17 G]B` (`combStart`) and replaces its `X`, `Y` and `T` by `[17 G - 8]B`'s (`combStart8`,
whose `Z` is also `1`) where the mask of bit 3 being clear is set (`constSel`, as
`combNeg` chooses by `csel`): `[17 G + d₀]B`. The loop from digit 1 then ends at the
scalar's multiple (`combMultiplyClamped_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards
open Word64

/-- Slot `c` replaced by `v` where the mask in `x1` is set. -/
theorem constSel_ok {s : State} {base : Addr} (hs : Scr s base) (c : Slot) (v : Spec.X25519.Fe)
    {sg : Bool} (h1 : s.gpr .x1 = mask sg) :
    WP isa (.block (constSel c v)) s fun t => Op base (offset c) s t ∧
      F t.mem base (offset c) = (if sg then v else F s.mem base (offset c)) ∧
      fe t.mem base (offset c) = if sg then v.val else fe s.mem base (offset c) := by
  rw [constSel, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (constWords_ok s v) fun u ⟨eu, ku⟩ => ?_
  obtain hsu := hs.of_keeps ku (by decide)
  refine WP.mono (loads_ok hsu (slot_range c) (a := .x12) (b := .x13) (c := .x14) (d := .x15) (by decide))
    fun w ⟨w12, w13, w14, w15, kw⟩ => ?_
  obtain hsw := hsu.of_keeps kw (by decide)
  refine WP.mono (negSel_ok w (sg := sg) (by rw [kw.gpr _ (by decide), ku.gpr _ (by decide), h1]))
    fun x ⟨x4, x5, x6, x7, kx⟩ => ?_
  refine WP.mono (store4_ok (hsw.of_keeps kx (by decide)) (slot_range c)) fun t ht => ?_
  subst t
  obtain kux : Keeps clob s x := (ku.mono (by decide)).trans ((kw.mono (by decide)).trans (kx.mono (by decide)))
  refine ⟨Op.of_store (slot_range c) kux _ _ _ _, ?_, ?_⟩
  · simp only [F]
    rw [fe_st4 _ _ (by simp only [offset]; omega_using []), x4, x5, x6, x7]
    cases sg
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [w12, w13, w14, w15, ku.mem]
    · simp only [↓reduceIte]
      rw [kw.gpr _ (by decide), kw.gpr _ (by decide), kw.gpr _ (by decide), kw.gpr _ (by decide), eu,
        VG.Proof.X25519.toFe_self]
  · rw [fe_st4 _ _ (by simp only [offset]; omega_using []), x4, x5, x6, x7]
    cases sg
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [w12, w13, w14, w15, ku.mem]
    · simp only [↓reduceIte]
      rw [kw.gpr _ (by decide), kw.gpr _ (by decide), kw.gpr _ (by decide), kw.gpr _ (by decide), eu]

private theorem byte_ext : ∀ b < 2, ((BitVec.ofNat 8 b).setWidth 32).setWidth 64 = BitVec.ofNat 64 b := by
  decide

private theorem bit_mask : ∀ b < 2, BitVec.ofNat 64 b - BitVec.ofNat 64 1 = mask (decide (b = 0)) := by
  decide

/-- `x1` = the mask of the bit `b` at `x0 + 771` being clear. -/
theorem clampMask_ok {s : State} {base : Addr} (hs : Scr s base) {b : Nat} (hb2 : b < 2)
    (hm : s.mem (off base 771) = BitVec.ofNat 8 b) :
    WP isa (.block clampMask) s fun t => t.gpr .x1 = mask (decide (b = 0)) ∧ Keeps [.x1, .x2] s t := by
  have _hcap : workSize true = 8192 := rfl
  obtain hr : InRegions (s.rd ++ s.wr) (off base 771) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by omega_using [_hcap]) (by omega_using [])⟩
  obtain e : s.gpr .x0 + BitVec.ofNat 64 771 = off base 771 := by rw [hs.x0]
  apply WP.of_runBlock
  simp only [clampMask, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    State.load, addr, Size.bits, RegUpd.gpr_write, BitVec.setWidth_eq, Nat.mod_one,
    show 771 < 4096 * 1 by omega_using [], show (1 : Nat) < 4096 from by decide, Nat.reduceMul, and_self, e, hr,
    read_byte, hm, byte_ext b hb2, bit_mask b hb2,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ⟨fun r hr => ?_, by simp only [RegUpd.mem_write],
      by simp only [RegUpd.rd_write],
      by simp only [RegUpd.wr_write],
      by simp only [RegUpd.sp_write]⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- The accumulator at `[17 G - 8]B` for the bit `b` at `x0 + 771` clear, else `[17 G]B`, and
zero in slot 21. -/
theorem combInitClamped_ok {s : State} {base : Addr} (hs : Scr s base) {b : Nat} (hb2 : b < 2)
    (hm : s.mem (off base 771) = BitVec.ofNat 8 b) :
    WP isa (.block combInitClamped) s fun t => CombKeep base s t ∧ env t.mem base 21 = 0 ∧
      point (env t.mem base) 0 1 2 3 = (if b = 0 then combStart8 else combStart) ∧
      AccBel t.mem base := by
  simp only [combInitClamped, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (combInit_ok hs) fun a ⟨ka, az, ap, ab⟩ => ?_
  obtain hsa := ka.scr hs
  rw [WP.block_append_iff]
  refine WP.mono (clampMask_ok hsa hb2 (by
      rw [show off base 771 = off base (768 + 3) from rfl, ka.bit (by decide)]; exact hm))
    fun c ⟨c1, kc⟩ => ?_
  obtain hsc := hsa.of_keeps kc (by decide)
  obtain kac : CombKeep base a c := CombKeep.of_keeps kc (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constSel_ok hsc 0 combStart8.X c1) fun d ⟨od, vd, fd⟩ => ?_
  obtain kd := op_keep od
  obtain hsd := kd.scr hsc
  rw [WP.block_append_iff]
  refine WP.mono (constSel_ok hsd 1 combStart8.Y ((kd.gpr _ (by decide)).trans c1)) fun e ⟨oe, ve, fe1⟩ => ?_
  obtain ke := op_keep oe
  obtain hse := ke.scr hsd
  refine WP.mono (constSel_ok hse 3 combStart8.T
    ((ke.gpr _ (by decide)).trans ((kd.gpr _ (by decide)).trans c1))) fun t ⟨ot, vt, ft⟩ => ?_
  obtain kt := op_keep ot
  obtain ec : env c.mem base = env a.mem base := by rw [kc.mem]
  obtain et : ∀ i : Slot, i ≠ 0 → i ≠ 1 → i ≠ 3 → env t.mem base i = env a.mem base i := fun i h0 h1 h3 => by
    rw [env_update 3 ot.mem, Function.update_of_ne h3, env_update 1 oe.mem, Function.update_of_ne h1,
      env_update 0 od.mem, Function.update_of_ne h0, ec]
  obtain q0 : F c.mem base (offset 0) = combStart.X := by rw [kc.mem]; exact congrArg Spec.Ed25519.Point.X ap
  obtain q1 : F d.mem base (offset 1) = combStart.Y := by
    show env d.mem base 1 = _
    rw [env_update 0 od.mem, Function.update_of_ne (by decide), ec]
    exact congrArg Spec.Ed25519.Point.Y ap
  obtain q3 : F e.mem base (offset 3) = combStart.T := by
    show env e.mem base 3 = _
    rw [env_update 1 oe.mem, Function.update_of_ne (by decide), env_update 0 od.mem,
      Function.update_of_ne (by decide), ec]
    exact congrArg Spec.Ed25519.Point.T ap
  obtain t0 : env t.mem base 0 = if decide (b = 0) then combStart8.X else combStart.X := by
    rw [env_update 3 ot.mem, Function.update_of_ne (by decide), env_update 1 oe.mem,
      Function.update_of_ne (by decide), env_update 0 od.mem, Function.update_self, vd, q0]
  obtain t1 : env t.mem base 1 = if decide (b = 0) then combStart8.Y else combStart.Y := by
    rw [env_update 3 ot.mem, Function.update_of_ne (by decide), env_update 1 oe.mem,
      Function.update_self, ve, q1]
  obtain t3 : env t.mem base 3 = if decide (b = 0) then combStart8.T else combStart.T := by
    rw [env_update 3 ot.mem, Function.update_self, vt, q3]
  obtain t2 : env t.mem base 2 = combStart.Z :=
    (et 2 (by decide) (by decide) (by decide)).trans (congrArg Spec.Ed25519.Point.Z ap)
  obtain lt : ∀ v : Spec.X25519.Fe, v.val < VG.Proof.X25519.AArch64.AltLadder.P2 := fun v => by
    have := v.isLt; simp only [Spec.X25519.P, VG.Proof.X25519.AArch64.AltLadder.P2] at this ⊢; omega_using []
  obtain fc : ∀ i : Slot, fe c.mem base (offset i) = fe a.mem base (offset i) := fun i => by rw [kc.mem]
  obtain sel : ∀ (sg : Bool) (v : Spec.X25519.Fe) (x : Nat), x < VG.Proof.X25519.AArch64.AltLadder.P2 →
      (if sg then v.val else x) < VG.Proof.X25519.AArch64.AltLadder.P2 := fun sg v x hx => by
    cases sg
    · exact hx
    · exact lt v
  obtain bel : AccBel t.mem base := fun i hi => by
    obtain hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 :=
      (by decide : ∀ i : Slot, i.val < 4 → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) i hi
    rcases hc with rfl | rfl | rfl | rfl
    · rw [ot.mem.fe (by simp only [offset]; omega_using []) (by simp only [offset]; omega_using []),
        oe.mem.fe (by simp only [offset]; omega_using []) (by simp only [offset]; omega_using []), fd, fc]
      exact sel _ _ _ (ab 0 (by decide))
    · rw [ot.mem.fe (by simp only [offset]; omega_using []) (by simp only [offset]; omega_using []), fe1,
        od.mem.fe (by simp only [offset]; omega_using []) (by simp only [offset]; omega_using []), fc]
      exact sel _ _ _ (ab 1 (by decide))
    · rw [ot.mem.fe (by simp only [offset]; omega_using []) (by simp only [offset]; omega_using []),
        oe.mem.fe (by simp only [offset]; omega_using []) (by simp only [offset]; omega_using []),
        od.mem.fe (by simp only [offset]; omega_using []) (by simp only [offset]; omega_using []), fc]
      exact ab 2 (by decide)
    · rw [ft, oe.mem.fe (by simp only [offset]; omega_using []) (by simp only [offset]; omega_using []),
        od.mem.fe (by simp only [offset]; omega_using []) (by simp only [offset]; omega_using []), fc]
      exact sel _ _ _ (ab 3 (by decide))
  refine ⟨ka.trans (kac.trans ((CombKeep.of_keep kd).trans ((CombKeep.of_keep ke).trans
    (CombKeep.of_keep kt)))), (et 21 (by decide) (by decide) (by decide)).trans az, ?_, bel⟩
  simp only [point]
  rw [t0, t1, t2, t3]
  by_cases hb : b = 0
  · simp only [hb, decide_true, ↓reduceIte]; rfl
  · simp only [hb, decide_false, Bool.false_eq_true, ↓reduceIte]

/-- `[s]B` into slots 0–3, for a scalar whose bits 0–2 are clear. -/
theorem combMultiplyClamped_ok {s : State} {base T : Addr} (hs : Scr s base) (htb : TblAt s base T)
    (hT : s.syms combSym = T) {S : Nat} (hS : S < 2 ^ 256) (hc : ∀ q < 3, (S / 2 ^ q) % 2 = 0)
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) :
    WP isa combMultiplyClamped s fun t =>
      Rep (point (env t.mem base) 0 1 2 3) (S • baseAff) ∧ CombKeep base s t := by
  rw [combMultiplyClamped]
  refine WP.seq (WP.mono_syms (combInitClamped_ok hs (b := (S / 2 ^ 3) % 2) (Nat.mod_lt _ (by decide))
    (hb 3 (by decide))) fun a ⟨ka, az, ap, ab⟩ sya => ?_)
  obtain hsa := ka.scr hs
  obtain hta : TblAt a base T := htb.of_far (by rw [ka.rd, ka.wr])
    (fun x hx => ka.mem x (Or.inr (by omega_using [hx])))
  obtain hn0 : nib S 0 = 8 * ((S / 2 ^ 3) % 2) := by
    obtain h0 := hc 0 (by decide)
    obtain h1 := hc 1 (by decide)
    obtain h2 := hc 2 (by decide)
    rw [nib_bits]
    simp only [Nat.mul_zero, Nat.zero_add] at h0 h1 h2 ⊢
    omega_using [h0, h1, h2]
  obtain hd : digitSum64 S 1 = (nib S 0 : ℤ) - 8 := by simp [digitSum64, sdig]
  obtain h8 : 8 ≤ 17 * combGVal := by decide
  obtain hv : Rep (point (env a.mem base) 0 1 2 3) ((((17 * combGVal : Nat) : ℤ) + digitSum64 S 1) • baseAff) := by
    rw [ap, hd, hn0]
    split
    · rename_i h
      rw [h, show ((17 * combGVal : Nat) : ℤ) + (((8 * 0 : Nat) : ℤ) - 8) =
        ((17 * combGVal - 8 : Nat) : ℤ) by push_cast [Nat.cast_sub h8]; ring, natCast_zsmul]
      exact combStart8_ok
    · rename_i h
      rw [show (S / 2 ^ 3) % 2 = 1 by omega_using [h], show ((17 * combGVal : Nat) : ℤ) + (((8 * 1 : Nat) : ℤ) - 8) =
        ((17 * combGVal : Nat) : ℤ) by push_cast; ring, natCast_zsmul]
      exact combStart_ok
  refine WP.mono (combLoopFrom_ok hsa hta (by rw [sya]; exact hT) (by decide) az
    (fun q hq => by rw [ka.bit hq]; exact hb q hq) hv ab) fun t ht => ⟨?_, ka.trans ht.keep⟩
  have hu := ht.acc
  rw [comb64_total hS, natCast_zsmul] at hu
  exact hu

end VG.Proof.Ed25519.AArch64

end

end


/-!
# X25519 of the base point on AArch64: the engine

The expanded bits of the scalar, clamped (`clampBits_ok`), are those of
`decodeScalar25519` (`clamped_bit`); the comb computes `[k] B` from them
(`combMultiplyClamped_ok`, which absorbs digit 0 into its start), and `uEncode` its u-coordinate `(Z + Y) / (Z - Y)`, which
`Proof/X25519/Edwards/Ladder.lean` shows is `X25519(k, 9)` (`engine_ok`).
-/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Base

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Impl.X25519.AArch64.Base
open VG.Proof.Ed25519.AArch64
open VG.Proof.Ed25519 (Rep dZ baseAff toZ_add toZ_sub toZ_mul toZ_pow)
open VG.Spec.X25519 (Fe P decodeScalar25519)
open VG.Proof.X25519.Edwards (clamped_bit u_rep)
open VG.Proof.Ed25519.Word64 (val4)

/-! ## The clamped bits -/

/-- A byte store at `base + d`, read at `base + e`. -/
theorem write1_off (m : Mem) (base : Addr) {d e : Nat} (hd : d < 2 ^ 64) (he : e < 2 ^ 64)
    (v : BitVec (8 * 1)) :
    (m.write (off base d) 1 v) (off base e) = if e = d then v.extractLsb' 0 8 else m (off base e) := by
  by_cases h : e = d
  · subst h; simp [Mem.write]
  · have hne : off base e ≠ off base d := fun h' => h ((off_eq_iff base he hd).mp h')
    simp only [Mem.write, sub_toNat_lt_one, hne, h, ite_false]

/-- A byte store at `base + d` leaves the other bytes. -/
theorem write1_outside (m : Mem) (base : Addr) {d : Nat} (hd : d < 2 ^ 64) {x : Addr}
    (hx : ofs base x ≠ d) (v : BitVec (8 * 1)) : (m.write (off base d) 1 v) x = m x := by
  obtain hne : x ≠ off base d := fun h => hx (by rw [h]; exact ofs_off' base hd)
  simp only [Mem.write, sub_toNat_lt_one, hne, ite_false]

/-- Clamping the expanded bits: five byte stores at `768 + q`. -/
theorem clampBits_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block clampBits) s fun t => PowersKeep base 56 968 s t ∧
      ∀ q < 256, t.mem (off base (768 + q)) =
        if q < 3 ∨ q = 255 then 0 else if q = 254 then 1 else s.mem (off base (768 + q)) := by
  have _hcap : workSize true = 8192 := rfl
  obtain hw : ∀ d, 768 ≤ d → d < 1024 → InRegions s.wr (off base d) 1 := fun d h1 h2 =>
    ⟨_, hs.wr, Offset.contains_base _ (by omega_using [_hcap, h2]) (by omega_using [h2])⟩
  have hx0 := hs.x0
  have e768 : base + 768#64 = off base 768 := rfl
  have e769 : base + 769#64 = off base 769 := rfl
  have e770 : base + 770#64 = off base 770 := rfl
  have e1022 : base + 1022#64 = off base 1022 := rfl
  have e1023 : base + 1023#64 = off base 1023 := rfl
  apply WP.of_runBlock
  simp only [clampBits, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    addr, State.store, RegUpd.gpr_write, RegUpd.wr_write, RegUpd.mem_write,
    hx0, hw 768 (by decide) (by decide), hw 769 (by decide) (by decide),
    hw 770 (by decide) (by decide), hw 1022 (by decide) (by decide), hw 1023 (by decide) (by decide),
    show 16 * 0 < Size.w.bits from by decide, Nat.mod_one, and_self,
    show 768 < 4096 * 1 from by decide, show 769 < 4096 * 1 from by decide,
    show 770 < 4096 * 1 from by decide, show 1022 < 4096 * 1 from by decide,
    show 1023 < 4096 * 1 from by decide,
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.some.injEq, exists_eq_left']
  simp only [e768, e769, e770, e1022, e1023]
  dsimp only [RegUpd.mem_write, RegUpd.wr_write, RegUpd.rd_write, RegUpd.sp_write]
  refine ⟨⟨fun r _ _ hc => ?_, rfl, rfl, rfl, fun p _ hp => ?_⟩, fun q hq => ?_⟩
  · have : r ≠ .x9 := fun h => hc (by subst h; decide)
    simp only [RegUpd.gpr_write, this, ite_false]
  · dsimp only [RegUpd.mem_write]
    rw [write1_outside _ _ (by decide) (by omega_using [hp]), write1_outside _ _ (by decide) (by omega_using [hp]),
      write1_outside _ _ (by decide) (by omega_using [hp]), write1_outside _ _ (by decide) (by omega_using [hp]),
      write1_outside _ _ (by decide) (by omega_using [hp])]
  · have he : 768 + q < 2 ^ 64 := by omega_using [hq]
    rw [write1_off _ _ (by decide) he, write1_off _ _ (by decide) he, write1_off _ _ (by decide) he,
      write1_off _ _ (by decide) he, write1_off _ _ (by decide) he]
    split_ifs <;> first | rfl | decide | (exfalso; omega_arith)

/-! ## The u-coordinate -/

theorem uOps_eval (e : Env) :
    evalOps uOps e 0 = e 2 + e 1 ∧ evalOps uOps e 2 = e 2 - e 1 := by
  simp [uOps, evalOps, evalOp, Function.update]

theorem uEncode_ok [VG.Proof.Ed25519.AArch64.Divstep.Sound] {s : State} {base : Addr} (hs : Scr s base) :
    WP isa uEncode s fun t => CounterKeep base s t ∧
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) =
        ((env s.mem base 2 + env s.mem base 1) *
          Spec.X25519.pow (env s.mem base 2 - env s.mem base 1) (P - 2)).val := by
  rw [uEncode]
  refine WP.seq (WP.mono (fieldCode_ok uOps hs) fun a ⟨ka, va⟩ => ?_)
  obtain kac : CounterKeep base s a := ⟨fun r hr _ => ka.gpr r hr, ka.rd, ka.wr, ka.sp, ka.mem⟩
  refine WP.seq (WP.mono (pointAffine_ok (kac.scr hs)) fun b ⟨kb, bx, _⟩ => ?_)
  refine WP.mono (freezeField_ok ((kb.scr (kac.scr hs))) 0) fun t ⟨tv, kt⟩ => ?_
  refine ⟨(kac.trans kb).trans (CounterKeep.of_keeps kt (by decide)), ?_⟩
  rw [tv, bx, va, (uOps_eval _).1, (uOps_eval _).2]

/-! ## The engine -/

theorem engine_ok [VG.Proof.Ed25519.AArch64.Divstep.Sound] {s : State} {base k T : Addr} (hs : Scr s base) (hp : s.gpr .x1 = k)
    (hr : ∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1)
    (hd : ∀ q < 32, 8192 ≤ ofs base (off k q)) (htb : TblAt s base T) (hT : s.syms combSym = T) :
    WP isa engine s fun t => PowersKeep base 56 968 s t ∧ ∃ w : Fe,
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) = w.val ∧
      Spec.X25519.x25519 (Spec.Ed25519.bytesAt s.mem k 32) Spec.X25519.basePoint =
        Spec.X25519.encodeUCoordinate w := by
  obtain hk : (Spec.Ed25519.bytesAt s.mem k 32).length = 32 := by simp [Spec.Ed25519.bytesAt]
  set kb := Spec.Ed25519.bytesAt s.mem k 32
  rw [engine]
  refine WP.seq (WP.mono_syms (scalarBasePrepare_ok hs hp hr hd) fun b ⟨kab, bbits, _⟩ syb => ?_)
  obtain hsb := kab.scratch hs
  refine WP.seq (WP.mono_syms (clampBits_ok hsb) fun c ⟨kbc, cbits⟩ syc => ?_)
  obtain hsc := kbc.scratch hsb
  obtain hS : decodeScalar25519 kb < 2 ^ 256 := by
    obtain h := Edwards.decodeScalar25519_shift hk
    rw [Nat.shiftRight_eq_div_pow] at h
    have := (Nat.div_eq_zero_iff_lt (by positivity)).mp h
    omega_using [h]
  obtain cb : ∀ q < 256, c.mem (off base (768 + q)) = BitVec.ofNat 8 ((decodeScalar25519 kb / 2 ^ q) % 2) := by
    intro q hq
    rw [cbits q hq, clamped_bit hk hq]
    split_ifs
    · rfl
    · rfl
    · exact bbits q (by simpa using hq)
  obtain htc : TblAt c base T := htb.of_far (by rw [kbc.rd, kbc.wr, kab.rd, kab.wr])
    (fun x hx => (powersKeep_outside (kab.trans kbc)) x (Or.inr (by omega_using [hx])))
  obtain hc : ∀ q < 3, (decodeScalar25519 kb / 2 ^ q) % 2 = 0 := fun q hq => by
    rw [clamped_bit hk (by omega_using [hq])]
    simp only [hq, true_or, ↓reduceIte]
  refine WP.seq (WP.mono (combMultiplyClamped_ok hsc htc (by rw [syc, syb]; exact hT) hS hc cb)
    fun d ⟨dp, kd⟩ => ?_)
  refine WP.mono (uEncode_ok (kd.scr hsc)) fun t ⟨kt, tv⟩ => ?_
  refine ⟨((kab.trans kbc).trans kd.powers).trans
    ⟨fun r hb _ hr => kt.gpr r hr hb, kt.rd, kt.wr, kt.sp, TableFrame.workspace kt.mem⟩, _, tv, ?_⟩
  exact VG.Proof.X25519.Edwards.x25519_basePoint hk _ (u_rep dp)

end VG.Proof.X25519.AArch64.Base

end

end

/-!
# X25519 of the base point on AArch64: memory and ABI obligations

As Ed25519's `scalarBase` (`Proof/Ed25519/AArch64/ScalarBaseMain.lean`), with
the engine of `Engine.lean` and its result read as a u-coordinate.
-/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Base

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Impl.X25519.AArch64.Base
open VG.Proof.Ed25519.AArch64
open VG.Proof.Ed25519.Word64 (val4)
open VG.Spec.Ed25519 (bytesAt)

/-- `vg_x25519_base(out = x0, scalar = x1, scratch = x2)`, with the comb's tables at the
static's address. -/
def baseLocal : Contract isa where
  pre s := s.rd = [⟨s.gpr .x1, 32⟩, tblRegion s] ∧ s.wr = [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x2, 8192⟩] ∧
    (⟨s.gpr .x1, 32⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩ ∧
    (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64 ∧ CombHeld s [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x2, 8192⟩]
  post s t := Spec.X25519.bytesAt t.mem (s.gpr .x0) 32 =
    Spec.X25519.x25519 (Spec.X25519.bytesAt s.mem (s.gpr .x1) 32) Spec.X25519.basePoint
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧
    s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2 ∧ s.syms combSym = t.syms combSym

/-- The bytes of `scratch` (at `base`) from 1024 on keep their values: the function writes only
its first 1024 bytes. -/
def ScratchTail (base : Addr) (m m' : Mem) : Prop :=
  ∀ i, 1024 ≤ i → i < 8192 → m' (base + BitVec.ofNat 64 i) = m (base + BitVec.ofNat 64 i)

/-- A byte of `scratch` beyond 1024 is outside the bytes a step changes. -/
theorem outside_tail {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m')
    (hon : o + n ≤ 1024) {i : Nat} (hi : 1024 ≤ i) (hi' : i < 8192) :
    m' (base + BitVec.ofNat 64 i) = m (base + BitVec.ofNat 64 i) :=
  h _ (Or.inr (by rw [show base + BitVec.ofNat 64 i = off base i from rfl, ofs_off' base (by omega_using [hi'])]; omega_using [hon, hi]))

theorem x25519Base_correct [VG.Proof.Ed25519.AArch64.Divstep.Sound] {s : State} (hs : baseLocal.pre s) :
    WP isa x25519Base s fun t => abiPreserved s t ∧ baseLocal.post s t ∧
      (Region.Disjoint ⟨s.gpr .x0, 32⟩ ⟨s.gpr .x2, 8192⟩ → ScratchTail (s.gpr .x2) s.mem t.mem) := by
  apply WP.withPreservedV (hc := by lit_decide)
  obtain ⟨hr, hw, hd, hn, hct⟩ := hs
  have hws : (⟨s.gpr .x2, 8192⟩ : Region) ∈ s.wr := by rw [hw]; simp
  rw [x25519Base]
  apply WP.seq
  rw [WP.block_append_iff]
  have htb : TblAt s (s.gpr .x2) (s.syms combSym) := hct.tblAt (by rw [hr]; simp) (by simp)
  refine WP.mono_syms (scalarSave_ok rfl hws) fun a ⟨ga, ra, wa, spa, ma, sva⟩ sya => ?_
  have hwa : (⟨a.gpr .x2, 8192⟩ : Region) ∈ a.wr := by rw [ga, wa]; exact hws
  refine WP.mono_syms (scalarBaseSetup_ok a hwa) fun b ⟨pb, gb, rb, wb, spb, ob, mb⟩ syb => ?_
  rw [ga] at pb ob mb
  have hb : Scr b (s.gpr .x2) := ⟨pb, by rw [wb, wa]; exact hws, hn⟩
  have fm : Frame [⟨s.gpr .x2, 8192⟩] s.mem b.mem :=
    (scratchFrame ma (by decide)).trans (scratchFrame mb (by decide))
  have svb : Saved (s.gpr .x2) s.gpr b.mem := sva.outside mb (by decide)
  have input : bytesAt b.mem (s.gpr .x1) 32 = bytesAt s.mem (s.gpr .x1) 32 := bytesAt32_frame fm hd
  apply WP.seq
  refine WP.mono (engine_ok hb ((gb _ (by decide)).trans (congrFun ga _))
    (fun q hq => ⟨⟨s.gpr .x1, 32⟩, by rw [rb, ra, hr]; simp,
      Offset.contains_base _ (by omega_using [hq]) (by omega_using [hq])⟩)
    (fun q hq => farScr hd hq (by decide))
    (htb.of_far (by rw [rb, ra, wb, wa]) fun x hx => by
      rw [mb x (Or.inr (by omega_using [hx])), ma x (Or.inr (by omega_using [hx]))])
    (by rw [syb, sya])) fun c ⟨kc, w, vc, xc⟩ => ?_
  have mc := powersKeep_outside kc
  have svc : Saved (s.gpr .x2) s.gpr c.mem := svb.outside mc (by decide)
  have oc : c.mem.readW (off (s.gpr .x2) 48) 64 = s.gpr .x0 :=
    (mc.word (d := 48) (Or.inl (by decide)) (by decide)).trans ob
  have wc : c.wr = s.wr := kc.wr.trans (wb.trans wa)
  rw [scalarBaseFinish]
  apply WP.seq
  refine WP.mono (scalarBaseFinishArgs_ok (kc.scratch hb)) fun d ⟨pd, od, kd⟩ => ?_
  have x2d : d.gpr .x2 = s.gpr .x2 := pd
  have x0d : d.gpr .x0 = s.gpr .x0 := od.trans oc
  have wd : d.wr = s.wr := kd.wr.trans wc
  rw [scalarFinish, WP.block_append_iff]
  refine WP.mono (scalarRestore_ok (g := s.gpr) x2d (wd ▸ hws) (by rw [kd.mem]; exact svc))
    fun e ⟨re, ke⟩ => ?_
  have x0e : e.gpr .x0 = s.gpr .x0 := (ke.gpr _ (by decide)).trans x0d
  have hwo : (⟨s.gpr .x0, 32⟩ : Region) ∈ e.wr := by rw [ke.wr, wd, hw]; simp
  refine WP.mono (scalarOut_ok x0e hwo) fun t ht => ?_
  subst t
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, fun hD i hi hi' => ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact re (.x19, 0) (by decide)
    · exact re (.x20, 8) (by decide)
    · exact re (.x21, 16) (by decide)
    · exact re (.x22, 24) (by decide)
    · exact re (.x23, 32) (by decide)
    · exact re (.x24, 40) (by decide)
    all_goals
      rw [ke.gpr _ (by decide), kd.gpr _ (by decide), kc.gpr _ (by decide) (by decide) (by decide),
        gb _ (by decide), ga]
  · exact ke.sp.trans (kd.sp.trans (kc.sp.trans (spb.trans spa)))
  · change Spec.X25519.bytesAt (st4 _ _ _ _ _ _ _) _ 32 = _
    change _ = Spec.X25519.x25519 (bytesAt s.mem (s.gpr .x1) 32) Spec.X25519.basePoint
    rw [bytesAt_st4, ← input, xc, Proof.X25519.encodeUCoordinate_eq]
    apply congrArg (Proof.X25519.leBytes 32)
    rw [ke.gpr .x4 (by decide), ke.gpr .x5 (by decide), ke.gpr .x6 (by decide), ke.gpr .x7 (by decide),
      kd.gpr .x4 (by decide), kd.gpr .x5 (by decide), kd.gpr .x6 (by decide), kd.gpr .x7 (by decide)]
    exact vc

  · -- `out` is outside `scratch`, and every step before it wrote below byte 1024
    have hx : ¬ (⟨s.gpr .x0, 32⟩ : Region).Contains (s.gpr .x2 + BitVec.ofNat 64 i) 1 :=
      fun hc => hD _ hc (by
        have e := ofs_off' (s.gpr .x2) (d := i) (by omega_using [hi'])
        simp only [ofs, off] at e
        simp only [Region.Contains, e]; omega_using [hi'])
    simp only [Region.Contains] at hx
    have ho := st4_outside e.mem (s.gpr .x0) (o := 0) (by decide) (e.gpr .x4) (e.gpr .x5) (e.gpr .x6)
      (e.gpr .x7) (s.gpr .x2 + BitVec.ofNat 64 i) (Or.inr (by simp only [ofs]; omega_using [hx]))
    change st4 e.mem (s.gpr .x0) 0 _ _ _ _ _ = _
    rw [ho, ke.mem, kd.mem, outside_tail mc (by decide) hi hi', outside_tail mb (by decide) hi hi',
      outside_tail ma (by decide) hi hi']

end VG.Proof.X25519.AArch64.Base

end

end

/-!
# X25519 of the base point on AArch64: constant time and the contract

As for Ed25519's `scalarBase`: the scalar's bits, the comb and the encoding
have a public trace (one taint check of the engine, whose addresses are the
working space `x0` plus constants or public counters), and so do the setup and
the finish.
-/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Base

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Impl.X25519.AArch64.Base
open VG.Proof.Ed25519.AArch64

/-- The engine: Ed25519's preparation and comb (`scalarBasePrepare_ct`, `combMultiplyClamped_ct`), with
the clamping and the encoding of `u` between and after them. -/
theorem engine_ct (base k T : Addr) :
    CT (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y) engine (fun _ _ => True) := by
  have hw : ∀ s, (Scr s base ∧ s.syms combSym = T) →
      WP isa (.block clampBits) s (fun t => Scr t base ∧ t.syms combSym = T) := fun s h =>
    WP.mono_syms (clampBits_ok h.1) fun _ ⟨kt, _⟩ syt => ⟨kt.scratch h.1, by rw [syt]; exact h.2⟩
  have hc : CT (fun x y => (Scr x base ∧ x.syms combSym = T) ∧ (Scr y base ∧ y.syms combSym = T))
      (.block clampBits) (fun _ _ => True) :=
    CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact h.1.1.x0.trans h.2.1.x0.symm) (by taint_decide)
  rw [engine]
  refine CT.seq (scalarBasePrepare_ct base k T) (CT.seq ((hc.wp fun x y h => ⟨hw x h.1, hw y h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2) (CT.seq (combMultiplyClamped_ct base T) ?_))
  exact CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_ofRegs h) (by taint_decide)

private def BaseStart (base k out T : Addr) (s : State) : Prop :=
  baseLocal.pre s ∧ s.gpr .x0 = out ∧ s.gpr .x1 = k ∧ s.gpr .x2 = base ∧ s.syms combSym = T

private def BasePrepared (base k out T : Addr) (s : State) : Prop :=
  BaseEnginePre base k T s ∧ s.mem.readW (off base 48) 64 = out

private def BaseReady (base out : Addr) (s : State) : Prop :=
  Scr s base ∧ s.mem.readW (off base 48) 64 = out

private theorem start_ok {base k out T : Addr} {s : State} (hs : BaseStart base k out T s) :
    WP isa (.block (scalarSave ++ scalarBaseSetup)) s (BasePrepared base k out T) := by
  obtain ⟨⟨hr, hw, hd, hn, hct⟩, ho, hk, hb, hT⟩ := hs
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw, hb]; simp
  have htb : TblAt s base T := by
    rw [← hb, ← hT]; exact hct.tblAt (by rw [hr]; simp) (by simp)
  rw [WP.block_append_iff]
  refine WP.mono_syms (scalarSave_ok hb hws) fun a ⟨ga, ra, wa, _, ma, _⟩ sya => ?_
  have hwa : (⟨a.gpr .x2, 8192⟩ : Region) ∈ a.wr := by rw [ga, hb, wa]; exact hws
  refine WP.mono_syms (scalarBaseSetup_ok a hwa) fun b ⟨pb, gb, rb, wb, _, ob, mb⟩ syb => ?_
  rw [ga, hb] at pb ob mb
  refine ⟨⟨⟨pb, by rw [wb, wa]; exact hws, by rw [← hb]; exact hn⟩,
    (gb _ (by decide)).trans ((congrFun ga _).trans hk), ?_, ?_, ?_, by rw [syb, sya]; exact hT⟩,
    ob.trans ho⟩
  · intro q hq
    exact ⟨⟨k, 32⟩, by rw [rb, ra, hr, hk]; simp, Offset.contains_base _ (by omega_using [hq]) (by omega_using [hq])⟩
  · intro q hq
    rw [hk, hb] at hd
    exact farScr hd hq (by decide)
  · exact htb.of_far (by rw [rb, ra, wb, wa]) fun x hx => by
      rw [mb x (Or.inr (by omega_using [hx])), ma x (Or.inr (by omega_using [hx]))]

private theorem start_ct (base k out T : Addr) :
    CT (fun x y => BaseStart base k out T x ∧ BaseStart base k out T y)
      (.block (scalarSave ++ scalarBaseSetup))
      (fun x y => BasePrepared base k out T x ∧ BasePrepared base k out T y) := by
  have hc : CT (fun x y => BaseStart base k out T x ∧ BaseStart base k out T y)
      (.block (scalarSave ++ scalarBaseSetup)) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0, .x1, .x2]) _ (by taint_decide)
    intro x y h
    apply agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1.2.1.trans h.2.2.1.symm
    · exact h.1.2.2.1.trans h.2.2.2.1.symm
    · exact h.1.2.2.2.1.trans h.2.2.2.2.1.symm
  exact (hc.wp (fun _ _ h => ⟨start_ok h.1, start_ok h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

private theorem engine_ready [VG.Proof.Ed25519.AArch64.Divstep.Sound] {base k out T : Addr} {s : State} (hs : BasePrepared base k out T s) :
    WP isa engine s (BaseReady base out) := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, ho⟩ := hs
  refine WP.mono (engine_ok h1 h2 h3 h4 h5 h6) fun t ⟨kt, _⟩ => ?_
  exact ⟨kt.scratch h1, ((powersKeep_outside kt).word
    (d := 48) (Or.inl (by decide)) (by decide)).trans ho⟩

private theorem engine_ct' [VG.Proof.Ed25519.AArch64.Divstep.Sound] (base k out T : Addr) :
    CT (fun x y => BasePrepared base k out T x ∧ BasePrepared base k out T y)
      engine (fun x y => BaseReady base out x ∧ BaseReady base out y) := by
  have hc := (engine_ct base k T).mono
    (fun _ _ (h : BasePrepared base k out T _ ∧ BasePrepared base k out T _) => ⟨h.1.1, h.2.1⟩)
    (fun _ _ h => h)
  exact (hc.wp (fun _ _ h => ⟨engine_ready h.1, engine_ready h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

private theorem finish_ct (base out : Addr) :
    CT (fun x y => BaseReady base out x ∧ BaseReady base out y)
      scalarBaseFinish (fun _ _ => True) := by
  have hc : CT (fun x y => BaseReady base out x ∧ BaseReady base out y)
      (.block scalarBaseFinishArgs) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    intro x y h
    exact agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r; exact h.1.1.x0.trans h.2.1.x0.symm)
  have hw : ∀ s, BaseReady base out s → WP isa (.block scalarBaseFinishArgs) s
      (fun t => t.gpr .x2 = base ∧ t.gpr .x0 = out) := by
    intro s h
    exact WP.mono (scalarBaseFinishArgs_ok h.1) fun _ ht => ⟨ht.1, ht.2.1.trans h.2⟩
  have hc' := (hc.wp (fun _ _ h => ⟨hw _ h.1, hw _ h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)
  rw [scalarBaseFinish]
  refine CT.seq hc' ?_
  apply CT.taint (Taint.ofRegs [.x2, .x0]) _ (by taint_decide)
  intro x y h
  apply agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.1.trans h.2.1.symm
  · exact h.1.2.trans h.2.2.symm

theorem x25519Base_ct [VG.Proof.Ed25519.AArch64.Divstep.Sound] : ConstantTime isa baseLocal.pre baseLocal.pub x25519Base := by
  intro x y tx ty x' y' hx hy ⟨hsp, ho, hk, hb, hsy⟩ ex ey
  have hc := CT.seq (start_ct (x.gpr .x2) (x.gpr .x1) (x.gpr .x0) (x.syms combSym))
    (CT.seq (engine_ct' (x.gpr .x2) (x.gpr .x1) (x.gpr .x0) (x.syms combSym))
      (finish_ct (x.gpr .x2) (x.gpr .x0)))
  exact (hc _ _ _ _ _ _ ⟨hsp, ⟨hx, rfl, rfl, rfl, rfl⟩, ⟨hy, ho.symm, hk.symm, hb.symm, hsy.symm⟩⟩
    ex ey).1

theorem x25519Base_ok [VG.Proof.Ed25519.AArch64.Divstep.Sound] (s : State) (hs : baseLocal.pre s) :
    ∃ t s', Exec isa x25519Base s t s' ∧ abiPreserved s s' ∧ baseLocal.post s s' :=
  let ⟨t, s', he, ha, hp, _⟩ := x25519Base_correct hs
  ⟨t, s', he, ha, hp⟩

/-- The shared contract's precondition, from its facts. -/
theorem x25519Base_spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .x1, 32⟩, ⟨s.syms combSym, 8 * combWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x2, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .x0, 32⟩ ⟨s.gpr .x1, 32⟩)
    (h2 : Region.Disjoint ⟨s.gpr .x0, 32⟩ ⟨s.gpr .x2, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .x1, 32⟩ ⟨s.gpr .x2, 8192⟩)
    (f0 : (s.gpr .x0).toNat + 32 ≤ 2 ^ 64) (f1 : (s.gpr .x1).toNat + 32 ≤ 2 ^ 64)
    (f2 : (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64)
    (ht : CombHeld s [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x2, 8192⟩])
    (hal : (s.syms combSym).toNat % 64 = 0) :
    (Spec.X25519.x25519BaseContract (AArch64.abi.withConsts combConsts)).pre s := by
  sig_pre [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
    AArch64.abi, AArch64.argRegs, combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact hdw, hal, by rw [hrd]; rfl, hw, h1, h2, h3, f0, f1, f2⟩

theorem x25519Base_sat :
    (Spec.X25519.x25519BaseContract (AArch64.abi.withConsts combConsts)).pre baseSatState := by
  have hl := combWords_length
  have held : ∀ i < combWords.length, baseSatState.mem.readW (baseSatState.syms combSym +
      BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := satMem_held
  refine x25519Base_spec_pre (by rw [hl]; rfl) rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide)) (by decide) (by decide)
    (by decide) ⟨held, ?_, ?_⟩ (by decide)
  all_goals rw [hl]
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

theorem x25519Base_implies : baseLocal.Implies
    (Spec.X25519.x25519BaseContract (AArch64.abi.withConsts combConsts)) where
  pre s h := by
    sig_pre [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
      AArch64.abi, AArch64.argRegs, combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
      stackBelow] at h
    obtain ⟨hd, hheld, hfit, hdw, -, ht, hw, -, -, h3, -, -, h5⟩ := h
    refine ⟨?_, hw, h3, h5, hheld, hfit, by rw [hw] at hdw; exact hdw⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
  post := by
    intro s s' _ h
    sig_post [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
      AArch64.abi, AArch64.argRegs, combConsts_eq, Abi.withConsts]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
      AArch64.abi, AArch64.argRegs, combConsts_eq, Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1, h2⟩ := h
    exact ⟨hsp, h0, h1, h2, hsy⟩
  sat := ⟨baseSatState, x25519Base_sat⟩

/-- The function writes only the first 1024 bytes of `scratch`. -/
theorem x25519Base_written [VG.Proof.Ed25519.AArch64.Divstep.Sound] (s : State) (t : List Leak)
    (s' : State) (hs : (Spec.X25519.x25519BaseContract (AArch64.abi.withConsts combConsts)).pre s)
    (he : Exec isa x25519Base s t s') :
    Sig.writtenWithin (AArch64.abi.withConsts combConsts) Spec.X25519.x25519BaseSig
      [("scratch", 1024)] s s' := by
  have hl := x25519Base_implies.pre s hs
  have hd : Region.Disjoint ⟨s.gpr .x0, 32⟩ ⟨s.gpr .x2, 8192⟩ := by
    sig_pre [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
      AArch64.abi, AArch64.argRegs, combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
      stackBelow] at hs
    exact hs.2.2.2.2.2.2.2.2.1
  obtain ⟨t', s'', he', -, -, htail⟩ := x25519Base_correct hl
  obtain ⟨-, rfl⟩ := Exec.det he he'
  simp [Sig.writtenWithin, AArch64.abi, AArch64.argRegs, Abi.withConsts, combConsts_eq,
    Spec.X25519.x25519BaseSig, Sig.words, Sig.arrays, Param.words, ArgWord.bits]
  all_goals exact fun i h1 h2 => htail hd i h1 (by simpa [Elem.size] using h2)

theorem x25519Base_verified [VG.Proof.Ed25519.AArch64.Divstep.Sound] :
    Verified AArch64.target x25519Base (Spec.X25519.x25519BaseContract (AArch64.abi.withConsts combConsts)) :=
  Verified.of_correct x25519Base_ok x25519Base_ct x25519Base_implies

end VG.Proof.X25519.AArch64.Base
