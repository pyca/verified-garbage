module

public import VerifiedGarbage.Proof.Ed25519.AArch64.Divstep
public import VerifiedGarbage.Impl.X25519.AArch64.Base
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseEngine
import VerifiedGarbage.Proof.Ed25519.AArch64.BitByte
import VerifiedGarbage.Proof.X25519.Edwards.Base
public import VerifiedGarbage.Proof.Ed25519.AArch64.CounterKeep
public import VerifiedGarbage.Proof.Ed25519.AArch64.CombSelect
public import VerifiedGarbage.Proof.Ed25519.AArch64.PointPowers
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.AArch64.PointEncode
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.Ed25519.AArch64.CombLoop
import VerifiedGarbage.Proof.Ed25519.AArch64.CombStart
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.Weierstrass
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import VerifiedGarbage.Proof.X25519.Edwards.Ladder
import VerifiedGarbage.Proof.X25519.AArch64.Ops

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
