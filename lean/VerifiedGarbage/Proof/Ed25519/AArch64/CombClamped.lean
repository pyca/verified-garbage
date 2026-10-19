module

public import VerifiedGarbage.Proof.Ed25519.AArch64.CombLoop
import VerifiedGarbage.Proof.Ed25519.AArch64.CombStart
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed25519.AArch64.CombEntry

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
  have hsu := hs.of_keeps ku (by decide)
  refine WP.mono (loads_ok hsu (slot_range c) (a := .x12) (b := .x13) (c := .x14) (d := .x15) (by decide))
    fun w ⟨w12, w13, w14, w15, kw⟩ => ?_
  have hsw := hsu.of_keeps kw (by decide)
  refine WP.mono (negSel_ok w (sg := sg) (by rw [kw.gpr _ (by decide), ku.gpr _ (by decide), h1]))
    fun x ⟨x4, x5, x6, x7, kx⟩ => ?_
  refine WP.mono (store4_ok (hsw.of_keeps kx (by decide)) (slot_range c)) fun t ht => ?_
  subst t
  have kux : Keeps clob s x := (ku.mono (by decide)).trans ((kw.mono (by decide)).trans (kx.mono (by decide)))
  refine ⟨Op.of_store (slot_range c) kux _ _ _ _, ?_, ?_⟩
  · simp only [F]
    rw [fe_st4 _ _ (by simp only [offset]; omega), x4, x5, x6, x7]
    cases sg
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [w12, w13, w14, w15, ku.mem]
    · simp only [↓reduceIte]
      rw [kw.gpr _ (by decide), kw.gpr _ (by decide), kw.gpr _ (by decide), kw.gpr _ (by decide), eu,
        VG.Proof.X25519.toFe_self]
  · rw [fe_st4 _ _ (by simp only [offset]; omega), x4, x5, x6, x7]
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
  have hr : InRegions (s.rd ++ s.wr) (off base 771) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by omega) (by omega)⟩
  have e : s.gpr .x0 + BitVec.ofNat 64 771 = off base 771 := by rw [hs.x0]
  apply WP.of_runBlock
  simp only [clampMask, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    State.load, addr, Size.bits, RegUpd.gpr_write, BitVec.setWidth_eq, Nat.mod_one,
    show 771 < 4096 * 1 by omega, show (1 : Nat) < 4096 from by decide, Nat.reduceMul, and_self, e, hr,
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
  have hsa := ka.scr hs
  rw [WP.block_append_iff]
  refine WP.mono (clampMask_ok hsa hb2 (by
      rw [show off base 771 = off base (768 + 3) from rfl, ka.bit (by decide)]; exact hm))
    fun c ⟨c1, kc⟩ => ?_
  have hsc := hsa.of_keeps kc (by decide)
  have kac : CombKeep base a c := CombKeep.of_keeps kc (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constSel_ok hsc 0 combStart8.X c1) fun d ⟨od, vd, fd⟩ => ?_
  have kd := op_keep od
  have hsd := kd.scr hsc
  rw [WP.block_append_iff]
  refine WP.mono (constSel_ok hsd 1 combStart8.Y ((kd.gpr _ (by decide)).trans c1)) fun e ⟨oe, ve, fe1⟩ => ?_
  have ke := op_keep oe
  have hse := ke.scr hsd
  refine WP.mono (constSel_ok hse 3 combStart8.T
    ((ke.gpr _ (by decide)).trans ((kd.gpr _ (by decide)).trans c1))) fun t ⟨ot, vt, ft⟩ => ?_
  have kt := op_keep ot
  have ec : env c.mem base = env a.mem base := by rw [kc.mem]
  have et : ∀ i : Slot, i ≠ 0 → i ≠ 1 → i ≠ 3 → env t.mem base i = env a.mem base i := fun i h0 h1 h3 => by
    rw [env_update 3 ot.mem, Function.update_of_ne h3, env_update 1 oe.mem, Function.update_of_ne h1,
      env_update 0 od.mem, Function.update_of_ne h0, ec]
  have q0 : F c.mem base (offset 0) = combStart.X := by rw [kc.mem]; exact congrArg Spec.Ed25519.Point.X ap
  have q1 : F d.mem base (offset 1) = combStart.Y := by
    show env d.mem base 1 = _
    rw [env_update 0 od.mem, Function.update_of_ne (by decide), ec]
    exact congrArg Spec.Ed25519.Point.Y ap
  have q3 : F e.mem base (offset 3) = combStart.T := by
    show env e.mem base 3 = _
    rw [env_update 1 oe.mem, Function.update_of_ne (by decide), env_update 0 od.mem,
      Function.update_of_ne (by decide), ec]
    exact congrArg Spec.Ed25519.Point.T ap
  have t0 : env t.mem base 0 = if decide (b = 0) then combStart8.X else combStart.X := by
    rw [env_update 3 ot.mem, Function.update_of_ne (by decide), env_update 1 oe.mem,
      Function.update_of_ne (by decide), env_update 0 od.mem, Function.update_self, vd, q0]
  have t1 : env t.mem base 1 = if decide (b = 0) then combStart8.Y else combStart.Y := by
    rw [env_update 3 ot.mem, Function.update_of_ne (by decide), env_update 1 oe.mem,
      Function.update_self, ve, q1]
  have t3 : env t.mem base 3 = if decide (b = 0) then combStart8.T else combStart.T := by
    rw [env_update 3 ot.mem, Function.update_self, vt, q3]
  have t2 : env t.mem base 2 = combStart.Z :=
    (et 2 (by decide) (by decide) (by decide)).trans (congrArg Spec.Ed25519.Point.Z ap)
  have lt : ∀ v : Spec.X25519.Fe, v.val < VG.Proof.X25519.AArch64.AltLadder.P2 := fun v => by
    have := v.isLt; simp only [Spec.X25519.P, VG.Proof.X25519.AArch64.AltLadder.P2] at this ⊢; omega
  have fc : ∀ i : Slot, fe c.mem base (offset i) = fe a.mem base (offset i) := fun i => by rw [kc.mem]
  have sel : ∀ (sg : Bool) (v : Spec.X25519.Fe) (x : Nat), x < VG.Proof.X25519.AArch64.AltLadder.P2 →
      (if sg then v.val else x) < VG.Proof.X25519.AArch64.AltLadder.P2 := fun sg v x hx => by
    cases sg
    · exact hx
    · exact lt v
  have bel : AccBel t.mem base := fun i hi => by
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 :=
      (by decide : ∀ i : Slot, i.val < 4 → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) i hi
    rcases hc with rfl | rfl | rfl | rfl
    · rw [ot.mem.fe (by simp only [offset]; omega) (by simp only [offset]; omega),
        oe.mem.fe (by simp only [offset]; omega) (by simp only [offset]; omega), fd, fc]
      exact sel _ _ _ (ab 0 (by decide))
    · rw [ot.mem.fe (by simp only [offset]; omega) (by simp only [offset]; omega), fe1,
        od.mem.fe (by simp only [offset]; omega) (by simp only [offset]; omega), fc]
      exact sel _ _ _ (ab 1 (by decide))
    · rw [ot.mem.fe (by simp only [offset]; omega) (by simp only [offset]; omega),
        oe.mem.fe (by simp only [offset]; omega) (by simp only [offset]; omega),
        od.mem.fe (by simp only [offset]; omega) (by simp only [offset]; omega), fc]
      exact ab 2 (by decide)
    · rw [ft, oe.mem.fe (by simp only [offset]; omega) (by simp only [offset]; omega),
        od.mem.fe (by simp only [offset]; omega) (by simp only [offset]; omega), fc]
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
  have hsa := ka.scr hs
  have hta : TblAt a base T := htb.of_far (by rw [ka.rd, ka.wr])
    (fun x hx => ka.mem x (Or.inr (by omega)))
  have hn0 : nib S 0 = 8 * ((S / 2 ^ 3) % 2) := by
    have h0 := hc 0 (by decide)
    have h1 := hc 1 (by decide)
    have h2 := hc 2 (by decide)
    rw [nib_bits]
    simp only [Nat.mul_zero, Nat.zero_add] at h0 h1 h2 ⊢
    omega
  have hd : digitSum64 S 1 = (nib S 0 : ℤ) - 8 := by simp [digitSum64, sdig]
  have h8 : 8 ≤ 17 * combGVal := by decide
  have hv : Rep (point (env a.mem base) 0 1 2 3) ((((17 * combGVal : Nat) : ℤ) + digitSum64 S 1) • baseAff) := by
    rw [ap, hd, hn0]
    split
    · rename_i h
      rw [h, show ((17 * combGVal : Nat) : ℤ) + (((8 * 0 : Nat) : ℤ) - 8) =
        ((17 * combGVal - 8 : Nat) : ℤ) by push_cast [Nat.cast_sub h8]; ring, natCast_zsmul]
      exact combStart8_ok
    · rename_i h
      rw [show (S / 2 ^ 3) % 2 = 1 by omega, show ((17 * combGVal : Nat) : ℤ) + (((8 * 1 : Nat) : ℤ) - 8) =
        ((17 * combGVal : Nat) : ℤ) by push_cast; ring, natCast_zsmul]
      exact combStart_ok
  refine WP.mono (combLoopFrom_ok hsa hta (by rw [sya]; exact hT) (by decide) az
    (fun q hq => by rw [ka.bit hq]; exact hb q hq) hv ab) fun t ht => ⟨?_, ka.trans ht.keep⟩
  have hu := ht.acc
  rw [comb64_total hS, natCast_zsmul] at hu
  exact hu

end VG.Proof.Ed25519.AArch64
