module

public import VerifiedGarbage.Proof.Ed448.AArch64.DecodeSteps
public import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Lit
public import VerifiedGarbage.Proof.Ed448.Ref
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Call
import VerifiedGarbage.Proof.Ed448.Recover
import VerifiedGarbage.Proof.Ed448.AArch64.Window.Checks
import VerifiedGarbage.Proof.Ed448.AArch64.VerifySign
public import VerifiedGarbage.Proof.Ed448.Formulas
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.MulSlots
import VerifiedGarbage.Proof.X448.AArch64.Base.Const
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Ed448.AArch64.Window.CopyK
public import VerifiedGarbage.Proof.Ed448.AArch64.Window.TableInit
public import VerifiedGarbage.Proof.X448.AArch64.Base.Digit
public import VerifiedGarbage.Proof.X448.AArch64.Fast.VSave
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyBits
public import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyBytes
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.X448.AArch64.Finish
import VerifiedGarbage.Proof.X448.AArch64.Weak.Main
public import VerifiedGarbage.Impl.X448.AArch64.Fast
public import VerifiedGarbage.Spec.Ed448
public import VerifiedGarbage.Impl.Curve448.AArch64.Neon
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.AArch64.Mem
public import VerifiedGarbage.Spec.Ed448.Contract
import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Impl.Ed448.AArch64.VerifyEquation
public import VerifiedGarbage.Proof.X448.AArch64.Fast.Env
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.X448.AArch64.Weak.Env
public import VerifiedGarbage.Impl.Ed448.AArch64.VerifyWindow
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.Proof.X448.AArch64.Setup
public import VerifiedGarbage.Spec.X448
public import VerifiedGarbage.TCB.Code
import VerifiedGarbage.Proof.X448.AArch64.Iter

/-! ### `Ed448.AArch64.VerifyStages`, which only this module used -/

section

/-! ### `Ed448.AArch64.VerifyDecode`, which only this module used -/

section

/-!
# Ed448 verification's equation on AArch64: decoding a point

Untrusted: everything here is checked by Lean. `decode rp xo yo`: the 57
bytes at `rp` decoded into slots `xo` and `yo` (`decode_ok`), with the
register-resident arithmetic: `x20 |= c`, `c = 0` exactly when they decode,
given that `recoverX` is `recoverRef` (`RecoverOk`), and then the slots hold
the point; every slot stays below the products' operand bound.
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 ofs workRegs FieldMem)
open VG.Proof.X448.AArch64.Weak (E opSwap)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd FKeep Same fclob cswapE subOp)
open VG.Proof.Curve448.AArch64 (mask)
open VG.Proof.Curve448.AArch64.Fast (Mb)
open VG.Impl.X448.AArch64 (ld st slot X2 ACC)

/-- The registers decoding may change. -/
def decClob : List Reg := .x30 :: .x17 :: .x20 :: (workRegs ++ fclob)

theorem bytesAt57_take (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 57).take 56 = Spec.Ed448.bytesAt m p 56 := by
  simp only [Spec.Ed448.bytesAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]
  rw [List.take_left' (by simp)]

theorem bytesAt57_getD (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 57).getD 56 0 = m (p + BitVec.ofNat 64 56) := by
  simp [Spec.Ed448.bytesAt, List.getD_eq_getElem?_getD]

theorem bytesAt57_len (m : Mem) (p : Addr) : (Spec.Ed448.bytesAt m p 57).length = 57 := by
  simp [Spec.Ed448.bytesAt]

theorem decode_ok (hR : RecoverOk) {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base)
    {rp : Reg} {p : Addr} (hp : s.gpr rp = p) (hrp : rp = .x0 ∨ rp = .x1) (xo yo : Fin 22)
    (hxy : (xo = 6 ∧ yo = 7) ∨ (xo = 8 ∧ yo = 9)) (h11 : E s.mem base 11 = Spec.Ed448.d)
    (hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 j) 1)
    (hfar : ∀ j < 57, 8192 ≤ ofs base (p + BitVec.ofNat 64 j)) :
    WP isa (decode rp xo.val yo.val) s fun t =>
      (∃ c : BitVec 64, (c = 0 ↔ (Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem p 57)).isSome) ∧
        t.gpr .x20 = s.gpr .x20 ||| c) ∧
      (∀ pt, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem p 57) = some pt →
        E t.mem base xo = pt.X ∧ E t.mem base yo = pt.Y ∧ pt.Z = 1) ∧
      (∀ i : Fin 22, i.val < 12 → i ≠ 1 → i ≠ 3 → i ≠ 4 → i ≠ 5 → i ≠ 10 → i ≠ xo → i ≠ yo →
        E t.mem base i = E s.mem base i) ∧ E t.mem base 10 = 1 ∧
      BEnv t.mem base ∧ Keeps decClob s t ∧ DFrame base s.mem t.mem := by
  obtain hxo1 : xo ≠ 1 := by rcases hxy with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  obtain hxo12 : xo ≠ 12 := by rcases hxy with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  obtain hxo13 : xo ≠ 13 := by rcases hxy with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  obtain hyx : yo ≠ xo := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  obtain hy10 : yo ≠ 10 := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  obtain hxlt : xo.val < 14 := by rcases hxy with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  obtain hylt : yo.val < 14 := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  obtain hxo : xo = 6 ∨ xo = 8 := by rcases hxy with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  rw [decode]
  -- `y`, its checks, the sign bit, and 1 in slot 10.
  refine WP.seq (WP.mono (head_ok hs hb hp hrp yo hy10 hr hfar)
    fun s1 ⟨y1, sg1, ⟨c1, hc1, b1⟩, e1, one1, bd1, m10, k1, d1⟩ => ?_)
  obtain hs1 : Scr s1 base := hs.of_keeps k1 (by decide)
  -- `u`, `v`, `u³v` and `u⁵v³`.
  refine WP.seq (WP.mono (uvOps_ok hs1 bd1 m10 xo yo hxy) fun s2 ⟨k2, bd2, e2⟩ => ?_)
  obtain hs2 := k2.scr hs1
  -- The root.
  refine WP.seq (WP.mono (Point56.powCall_ok hs2 bd2) fun s3 ⟨k3, bd3, e3, _⟩ => ?_)
  obtain hs3 := k3.scr hs2
  -- `x` and `v x²`.
  refine WP.seq (WP.mono (xOps_ok hs3 bd3 xo hxo) fun s4 ⟨k4, bd4, mx4, sm4, e4⟩ => ?_)
  obtain hs4 := k4.scr hs3
  -- The comparison of `v x²` with `u`, and zero in slot 13.
  refine WP.seq (WP.mono (eqSlotsF_ok hs4 12 13 (lt118 bd4 12) (lt118 bd4 13) (by decide) (by decide))
    fun s5 ⟨⟨c2, hc2, b5⟩, k5, x25⟩ => ?_)
  obtain hs5 := k5.scr hs4
  obtain bd5 : BEnv s5.mem base := bnd_check bd4 k5.mem x25
  refine WP.seq (WP.mono (VG.Proof.X448.AArch64.Base.constSlot_ok hs5 (o := slot 13) (by decide) (by decide) 0)
    fun s6 ⟨w6, o6, k6⟩ => ?_)
  obtain hs6 : Scr s6 base := hs5.of_keeps k6 (by decide)
  obtain z13 : ∀ j < 8, limbs s6.mem base (slot (13 : Fin 22).val) j < 2 ^ 56 := fun j hj => by
    change (word s6.mem base (slot 13 + 8 * j)).toNat < _
    rw [w6 j hj]; exact VG.Proof.X448.AArch64.Base.limb_lt _ _
  obtain l56 : ∀ i : Fin 22, i ≠ 13 → ∀ j < 8, limbs s6.mem base (slot i.val) j = limbs s5.mem base (slot i.val) j := by
    intro i hi j hj
    obtain h1 := VG.Proof.X448.AArch64.Weak.slot_sep hi
    have h2 := i.isLt
    exact o6.limbs (by simp only [slot] at *; omega_arith) (by simp only [slot]; omega_arith) (by omega_arith)
  obtain E56 : ∀ i : Fin 22, i ≠ 13 → E s6.mem base i = E s5.mem base i := fun i hi =>
    congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr (l56 i hi))
  obtain bd6 : BEnv s6.mem base := fun i j hj => by
    by_cases h : i = 13
    · subst h; exact Nat.lt_trans (z13 j hj) (by decide)
    · rw [l56 i h j hj]; exact bd5 i j hj
  obtain mx6 : Bnd Mb s6.mem base (slot xo.val) := fun j hj => by
    rw [l56 xo hxo13 j hj, k5.mem.limbs hxo1 (by omega_arith)]; exact mx4 j hj
  -- `0 - x` into slot 12.
  refine WP.seq (subOp (o := 12) (a := 13) (b := xo) hs6 bd6 (fun j hj => Nat.lt_trans (z13 j hj) (by decide)) mx6
    (by decide) (Ne.symm hxo12) fun s7 k7 bd7 sm7 e7 => WP.block_nil ?_)
  obtain hs7 := k7.scr hs6
  -- The sign bit, the check of `x = 0`, the mask, and the swap.
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (signLoad_ok hs7) fun s8 ⟨x8, m8, k8⟩ => ?_
  obtain hs8 : Scr s8 base := hs7.of_keeps k8 (by decide)
  obtain hsb : (s.mem (p + BitVec.ofNat 64 56)).toNat / 128 < 2 := by
    have := (s.mem (p + BitVec.ofNat 64 56)).isLt; omega_arith
  obtain sgn : s8.gpr .x17 = BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat / 128) := by
    rw [x8, ← sg1,
      k7.mem.word (Or.inl (by simp only [SIGN]; omega_arith)) (Or.inl (by simp only [SIGN, ACC]; omega_arith)) (by decide),
      o6.word (Or.inl (by simp only [SIGN, slot]; omega_arith)) (by decide),
      k5.mem.word (Or.inl (by simp only [SIGN, X2, slot]; omega_arith)) (Or.inl (by simp only [SIGN, CAN]; omega_arith))
        (Or.inl (by simp only [SIGN, ACC]; omega_arith)) (by decide),
      k4.mem.word (Or.inl (by simp only [SIGN]; omega_arith)) (Or.inl (by simp only [SIGN, ACC]; omega_arith)) (by decide),
      k3.mem.word (Or.inl (by simp only [SIGN]; omega_arith)) (Or.inl (by simp only [SIGN, ACC]; omega_arith)) (by decide),
      k2.mem.word (Or.inl (by simp only [SIGN]; omega_arith)) (Or.inl (by simp only [SIGN, ACC]; omega_arith)) (by decide)]
  obtain bd8 : BEnv s8.mem base := m8 ▸ bd7
  rw [WP.block_append_iff]
  refine WP.mono (zeroSignF_ok hs8 bd8 xo hxo1 hsb sgn) fun s9 ⟨⟨c3, hc3, b9⟩, lo9, k9, bd9⟩ => ?_
  obtain hs9 := k9.scr hs8
  obtain sgn9 : s9.gpr .x17 = BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat / 128) := by
    rw [k9.regs.1 _ (by decide)]; exact sgn
  rw [WP.block_append_iff]
  refine WP.mono (negMask_ok hs9 hsb sgn9) fun s10 ⟨m10', mm10, k10⟩ => ?_
  obtain hs10 : Scr s10 base := hs9.of_keeps k10 (by decide)
  rw [negSwap, WP.block_append_iff]
  refine WP.mono (mov6_ok s10) fun s11 ⟨x6, mm11, k11⟩ => ?_
  obtain hs11 : Scr s11 base := hs10.of_keeps k11 (by decide)
  obtain bd11 : BEnv s11.mem base := by rw [mm11, mm10]; exact bd9
  refine WP.mono (cswapE hs11 bd11 xo 12 hxo12 (sw := decide (VG.Proof.X448.AArch64.limbs s9.mem base X2 0 % 2 ^^^
    (s.mem (p + BitVec.ofNat 64 56)).toNat / 128 = 1)) (by rw [x6, m10']; rfl)) fun t ⟨kt, bdt, _, _, _, _, et⟩ => ?_
  -- The values.
  have e1' : ∀ i : Fin 22, i ≠ yo → i ≠ 10 → E s1.mem base i = E s.mem base i := e1
  obtain h11' : E s1.mem base 11 = Spec.Ed448.d := by
    rw [e1' 11 (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide) (by decide), h11]
  obtain ⟨u2, vv2, t2, w2, k2'⟩ := uvEnv_eval xo yo hxy (E s1.mem base)
  simp only [one1, h11', y1] at u2 vv2 t2 w2
  simp only [← e2] at u2 vv2 t2 w2 k2'
  generalize hY : VG.Proof.X448.toFe (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56)) = Y at *
  obtain r21 : E s3.mem base 21 = rootPow (E s2.mem base 12) := by rw [e3, rootEnv_eval]
  obtain r3k : ∀ i : Fin 22, i.val < 14 → E s3.mem base i = E s2.mem base i := fun i hi => by
    rw [e3, rootEnv_keep _ _ hi]
  obtain ⟨x4, x12, x13, k4'⟩ := xEnv_eval xo hxo (E s3.mem base)
  rw [← e4] at x4 x12 x13 k4'
  rw [r3k xo hxlt, t2, r21, w2] at x4 x12
  rw [r3k 3 (by decide), vv2] at x12
  rw [x13, r3k 13 (by decide), u2] at hc2
  rw [x12] at hc2
  generalize hu : Y * Y - 1 = u at *
  generalize hv : Spec.Ed448.d * (Y * Y) - 1 = v at *
  generalize ht : u * u * u * v = tt at *
  generalize hx : tt * rootPow (tt * ((u * v) * (u * v))) = x at *
  -- From `s4` to `s9`, the slots but 12, 13 and `X2` keep their values.
  obtain E79 : ∀ i : Fin 22, i ≠ 1 → i ≠ 12 → i ≠ 13 → E s9.mem base i = E s4.mem base i := fun i h1 h12 h13 => by
    rw [k9.mem.E h1, m8, sm7.env (by simp [h12]), E56 i h13, k5.mem.E h1]
  obtain x8 : E s8.mem base xo = x := by
    rw [m8, sm7.env (by simp [hxo12]), E56 xo hxo13, k5.mem.E hxo1, x4]
  rw [x8] at hc3 lo9
  obtain n12 : E s9.mem base 12 = 0 - x := by
    obtain h0 : E s6.mem base 13 = 0 := VG.Proof.X448.AArch64.Base.F_of_words w6
    rw [k9.mem.E (by decide), m8, e7, Function.update_self, h0, E56 xo hxo13, k5.mem.E hxo1, x4]
  obtain hD := Proof.Ed448.decodePoint_impl hR (Spec.Ed448.bytesAt s.mem p 57) (bytesAt57_len _ _)
    (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56)) ((s.mem (p + BitVec.ofNat 64 56)).toNat)
    (by rw [bytesAt57_take]) (by rw [bytesAt57_getD]) Y u v tt x hY hu hv ht hx
  obtain s11x : E s11.mem base = E s9.mem base := by rw [mm11, mm10]
  -- The final `x`.
  obtain xt : E t.mem base xo =
      if (x.val % 2 == 1) == ((s.mem (p + BitVec.ofNat 64 56)).toNat / 128 == 1) then x else (x - x) - x := by
    rw [et, VG.Proof.X448.AArch64.opSwap, Function.update_of_ne hxo12, Function.update_self, s11x, n12,
      E79 xo hxo1 hxo12 hxo13, x4, sub_self]
    have hlo : VG.Proof.X448.AArch64.limbs s9.mem base X2 0 % 2 = x.val % 2 := lo9
    rw [hlo]
    obtain hx2 : x.val % 2 < 2 := Nat.mod_lt _ (by decide)
    generalize x.val % 2 = a at hx2 ⊢
    generalize (s.mem (p + BitVec.ofNat 64 56)).toNat / 128 = sb at hsb ⊢
    rcases (by omega_arith : a = 0 ∨ a = 1) with rfl | rfl <;> rcases (by omega_arith : sb = 0 ∨ sb = 1) with rfl | rfl <;>
      rfl
  -- What the rest keeps.
  obtain keepE : ∀ i : Fin 22, i ≠ 1 → i ≠ xo → i ≠ 12 → i ≠ 13 → E t.mem base i = E s4.mem base i := by
    intro i h1 hx h12 h13
    rw [et, VG.Proof.X448.AArch64.opSwap, Function.update_of_ne h12, Function.update_of_ne hx, s11x, E79 i h1 h12 h13]
  obtain kY : E t.mem base yo = Y := by
    obtain hy1 : yo ≠ 1 := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
    obtain hy12 : yo ≠ 12 := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
    obtain hy13 : yo ≠ 13 := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
    rw [keepE yo hy1 hyx hy12 hy13, k4' yo hyx hy12, r3k yo hylt,
      k2' yo (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
        (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) hy12 hy13 hyx, y1]
  obtain kk : ∀ i : Fin 22, i.val < 12 → i ≠ 1 → i ≠ 3 → i ≠ 4 → i ≠ 5 → i ≠ xo → E t.mem base i = E s1.mem base i := by
    intro i hi h1 h3 h4 h5 hix
    obtain h12 : i ≠ 12 := fun h => by rw [h] at hi; exact absurd hi (by decide)
    obtain h13 : i ≠ 13 := fun h => by rw [h] at hi; exact absurd hi (by decide)
    rw [keepE i h1 hix h12 h13, k4' i hix h12, r3k i (by omega_arith), k2' i h3 h4 h5 h12 h13 hix]
  refine ⟨⟨c1 ||| c2 ||| c3, ?_, ?_⟩, fun pt hpt => ?_, fun i hi h1 h3 h4 h5 h10 hix hiy => ?_, ?_, bdt, ?_, ?_⟩
  · rw [or_eq_zero64, or_eq_zero64, hc1, hc2, hc3, hD]
    by_cases hall : ((s.mem (p + BitVec.ofNat 64 56)).toNat % 128 = 0 ∧
        Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) < Spec.X448.P) ∧ v * (x * x) = u ∧
        ¬ (x = 0 ∧ (s.mem (p + BitVec.ofNat 64 56)).toNat / 128 = 1)
    · rw [ite_eq_left hall]
      exact ⟨fun _ => rfl, fun _ => ⟨⟨hall.1, hall.2.1⟩, hall.2.2⟩⟩
    · rw [ite_eq_right hall]
      exact ⟨fun h => absurd ⟨h.1.1, h.1.2, h.2⟩ hall, fun h => absurd h (by simp)⟩
  · rw [kt.regs.1 _ (by decide), k11.1 _ (by decide), k10.1 _ (by decide), b9, k8.1 _ (by decide),
      k7.regs.1 _ (by decide), k6.1 _ (by decide), b5, k4.regs.1 _ (by decide), k3.regs.1 _ (by decide),
      k2.regs.1 _ (by decide), b1]
    simp only [BitVec.or_assoc]
  · rw [hD] at hpt
    by_cases hall : ((s.mem (p + BitVec.ofNat 64 56)).toNat % 128 = 0 ∧
        Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) < Spec.X448.P) ∧ v * (x * x) = u ∧
        ¬ (x = 0 ∧ (s.mem (p + BitVec.ofNat 64 56)).toNat / 128 = 1)
    · rw [ite_eq_left hall] at hpt
      cases hpt
      exact ⟨xt, kY, rfl⟩
    · rw [ite_eq_right hall] at hpt
      cases hpt
  · rw [kk i hi h1 h3 h4 h5 hix, e1' i hiy h10]
  · rw [kk 10 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rcases hxy with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide), one1]
  · exact ((((((((((k1.mono (by decide)).trans (k2.regs.mono (by decide))).trans (k3.regs.mono (by decide))).trans
      (k4.regs.mono (by decide))).trans (k5.regs.mono (by decide))).trans (k6.mono (by decide))).trans
      (k7.regs.mono (by decide))).trans (k8.mono (by decide))).trans (k9.regs.mono (by decide))).trans
      ((k10.mono (by decide)).trans (k11.mono (by decide)))).trans (kt.regs.mono (by decide))
  · have d6 : DFrame base s5.mem s6.mem := DFrame.of_outside o6 (by simp only [slot]; omega_arith)
    obtain d8 : DFrame base s7.mem s8.mem := by rw [m8]; exact fun _ _ _ _ => rfl
    obtain d11 : DFrame base s9.mem s11.mem := by rw [mm11, mm10]; exact fun _ _ _ _ => rfl
    exact ((((((((d1.trans (fkeep_dframe k2)).trans (DFrame.of_outside2 (Nat.le_refl _) k3.mem)).trans (fkeep_dframe k4)).trans
      (cframe_dframe k5.mem)).trans d6).trans (fkeep_dframe k7)).trans d8).trans
      ((cframe_dframe k9.mem).trans d11)).trans (fkeep_dframe kt)

end VG.Proof.Ed448.AArch64

end

end


/-!
# Ed448 verification's equation on AArch64: decoding `A`

Untrusted: everything here is checked by Lean. `negA_ok`: after `A` is
decoded into slots 8 and 9, `-A` into slots 6 and 7. `decodes_ok`: `A` and `R`
decoded by one copy of `decode`, its loop's two passes, `-A` into slots 6, 7
and 10 and `R` into 8, 9 and 10. Each check ORs into `x20` a word that is 0
exactly when it passes.
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keep Keeps off word limbs Outside Outside2 ofs workRegs)
open VG.Proof.X448.AArch64.Weak (E opCopy)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd FKeep mulOp subOp copyE)
open VG.Proof.Curve448.AArch64.Fast (Mb)
open VG.Impl.X448.AArch64 (slot BITS ACC)

/-- Bytes far from the working space, after writes only to it. -/
theorem far_bytes {base p : Addr} {n : Nat} {m m' : Mem} (h : Outside base 0 8192 m m')
    (hf : ∀ i < n, 8192 ≤ ofs base (p + BitVec.ofNat 64 i)) :
    Spec.Ed448.bytesAt m' p n = Spec.Ed448.bytesAt m p n := by
  simp only [Spec.Ed448.bytesAt]
  exact List.map_congr_left fun i hi => h _ (Or.inr (hf i (List.mem_range.mp hi)))

/-- `x0 := x1`. -/
theorem mov01_ok (s : State) :
    WP isa (.block [.addImm .x .x0 .x1 0]) s fun t => t.gpr .x0 = s.gpr .x1 ∧ t.mem = s.mem ∧ Keeps [.x0] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (0 : Nat) < 4096 from by decide, ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq,
    BitVec.add_zero, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, rfl, fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl⟩

/-- `x0 := x1`, `x1 := x3`. -/
theorem mov013_ok (s : State) :
    WP isa (.block [.addImm .x .x0 .x1 0, .addImm .x .x1 .x3 0, .sub .x .x19 .x0 .x3]) s fun t =>
      t.gpr .x0 = s.gpr .x1 ∧ t.gpr .x1 = s.gpr .x3 ∧ t.gpr .x19 = s.gpr .x1 - s.gpr .x3 ∧
      t.mem = s.mem ∧ Keeps [.x0, .x1, .x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (0 : Nat) < 4096 from by decide, ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq,
    BitVec.add_zero, Option.some.injEq, exists_eq_left', RegUpd.gpr_write_of_ne _ _ _ (by decide : Reg.x3 ≠ .x0),
    RegUpd.gpr_write_of_ne _ _ _ (by decide : Reg.x0 ≠ .x1), RegUpd.gpr_write_of_ne _ _ _ (by decide : Reg.x0 ≠ .x19),
    RegUpd.gpr_write_of_ne _ _ _ (by decide : Reg.x1 ≠ .x19),
    RegUpd.gpr_write_of_ne _ _ _ (by decide : Reg.x3 ≠ .x1)]
  refine ⟨trivial, trivial, trivial, rfl, fun r hr => ?_, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [RegUpd.gpr_write_of_ne _ _ _ hr.2.2, RegUpd.gpr_write_of_ne _ _ _ hr.2.1,
    RegUpd.gpr_write_of_ne _ _ _ hr.1]

/-- After `A` is decoded into slots 8–9 (with 1 in slot 10): `-A` into slots 6 and 7, `x` (a
product by 1, below the products' bound) subtracted from zero in slot 13, `x0 := x1` and
`x1 := x3`. -/
theorem negA_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) (h10 : E s.mem base 10 = 1)
    (h19 : s.gpr .x19 = s.gpr .x1 - s.gpr .x3) :
    WP isa negA s fun t =>
      E t.mem base 6 = 0 - E s.mem base 8 ∧ E t.mem base 7 = E s.mem base 9 ∧
      (∀ i : Fin 22, i ≠ 6 → i ≠ 7 → i ≠ 12 → i ≠ 13 → E t.mem base i = E s.mem base i) ∧
      t.gpr .x0 = s.gpr .x1 ∧ t.gpr .x1 = s.gpr .x3 ∧ Scr t base ∧ BEnv t.mem base ∧
      Keeps (.x1 :: VG.Proof.X448.AArch64.Fast.fclob) s t ∧ DFrame base s.mem t.mem := by
  unfold negA
  refine WP.seq (VG.Proof.Ed448.AArch64.Point56.mulOpK (rest := [.copy (slot 7) (slot 9)]) hs hb 6 8 10
    (Or.inr (by decide))
    fun s2 k2 b2 m2 sm2 e2 => ?_)
  obtain hs2 := k2.scr hs
  refine WP.seq (WP.mono (copyE hs2 b2 7 9) fun s2b ⟨k2b, b2b, _, sm2b, e2b⟩ => WP.block_nil ?_)
  obtain hs2b := k2b.scr hs2
  refine WP.seq (WP.mono (VG.Proof.X448.AArch64.Base.constSlot_ok hs2b (o := slot 13) (by decide) (by decide) 0)
    fun s3 ⟨w3, o3, k3⟩ => ?_)
  obtain hs3 : Scr s3 base := hs2b.of_keeps k3 (by decide)
  obtain l23 : ∀ i : Fin 22, i ≠ 13 → ∀ j < 8, limbs s3.mem base (slot i.val) j = limbs s2b.mem base (slot i.val) j := by
    intro i hi j hj
    obtain h1 := VG.Proof.X448.AArch64.Weak.slot_sep hi
    have h2 := i.isLt
    exact o3.limbs (by simp only [slot] at *; omega_using [h1]) (by simp only [slot]; omega_using []) (by omega_using [hj])
  obtain E23 : ∀ i : Fin 22, i ≠ 13 → E s3.mem base i = E s2b.mem base i := fun i hi =>
    congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr (l23 i hi))
  obtain z13 : ∀ j < 8, limbs s3.mem base (slot (13 : Fin 22).val) j < 2 ^ 56 := fun j hj => by
    change (word s3.mem base (slot 13 + 8 * j)).toNat < _
    rw [w3 j hj]; exact VG.Proof.X448.AArch64.Base.limb_lt _ _
  obtain b3 : BEnv s3.mem base := fun i j hj => by
    by_cases h : i = 13
    · subst h; exact Nat.lt_trans (z13 j hj) (by decide)
    · rw [l23 i h j hj]; exact b2b i j hj
  obtain m3 : Bnd Mb s3.mem base (slot (6 : Fin 22).val) := fun j hj => by
    rw [l23 6 (by decide) j hj, sm2b 6 (by decide) j hj]; exact m2 j hj
  refine WP.seq (subOp (o := 12) (a := 13) (b := 6) (rest := [.copy (slot 6) (slot 12)]) hs3 b3
    (fun j hj => Nat.lt_trans (z13 j hj) (by decide)) m3 (by decide) (by decide) fun s4 k4 b4 _ e4 => ?_)
  obtain hs4 := k4.scr hs3
  refine WP.seq (WP.mono (copyE hs4 b4 6 12) fun s5 ⟨k5, b5, _, _, e5⟩ => WP.block_nil ?_)
  obtain hs5 := k5.scr hs4
  refine WP.mono (mov013_ok s5) fun t ⟨x0t, x1t, x19t, mt, kt'⟩ => ?_
  obtain kt : Keeps [.x0, .x1] s5 t := by
    refine ⟨fun r hr => ?_, kt'.2.1, kt'.2.2⟩
    by_cases e : r = .x19
    · subst e
      obtain k1 : s5.gpr .x1 = s.gpr .x1 := by
        rw [k5.regs.1 _ (by decide), k4.regs.1 _ (by decide), k3.1 _ (by decide), k2b.regs.1 _ (by decide),
          k2.regs.1 _ (by decide)]
      obtain k3' : s5.gpr .x3 = s.gpr .x3 := by rw [hs5.x3, hs.x3]
      obtain k19 : s5.gpr .x19 = s.gpr .x19 := by
        rw [k5.regs.1 _ (by decide), k4.regs.1 _ (by decide), k3.1 _ (by decide), k2b.regs.1 _ (by decide),
          k2.regs.1 _ (by decide)]
      rw [x19t, k1, k3', k19, h19]
    · exact kt'.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢; exact ⟨hr.1, hr.2, e⟩)
  obtain h0 : E s3.mem base 13 = 0 := VG.Proof.X448.AArch64.Base.F_of_words w3
  obtain Et : ∀ i, E t.mem base i = E s5.mem base i := fun i => by rw [mt]
  obtain keep : ∀ i : Fin 22, i ≠ 6 → i ≠ 7 → i ≠ 12 → i ≠ 13 → E t.mem base i = E s.mem base i :=
    fun i h6 h7 h12 h13 => by
      rw [Et, e5, VG.Proof.X448.AArch64.opCopy, Function.update_of_ne h6, e4, Function.update_of_ne h12, E23 i h13, e2b, VG.Proof.X448.AArch64.opCopy,
        Function.update_of_ne h7, e2, Function.update_of_ne h6]
  refine ⟨?_, ?_, keep, ?_, ?_, hs5.of_keeps kt (by decide), by rw [mt]; exact b5, ?_, ?_⟩
  · rw [Et, e5, VG.Proof.X448.AArch64.opCopy, Function.update_self, e4, Function.update_self, h0, E23 6 (by decide), e2b, VG.Proof.X448.AArch64.opCopy,
      Function.update_of_ne (by decide), e2, Function.update_self, h10, Fin.mul_one]
  · rw [Et, e5, VG.Proof.X448.AArch64.opCopy, Function.update_of_ne (by decide), e4, Function.update_of_ne (by decide),
      E23 7 (by decide), e2b, VG.Proof.X448.AArch64.opCopy, Function.update_self, e2, Function.update_of_ne (by decide)]
  · rw [x0t, k5.regs.1 _ (by decide), k4.regs.1 _ (by decide), k3.1 _ (by decide), k2b.regs.1 _ (by decide),
      k2.regs.1 _ (by decide)]
  · rw [x1t, k5.regs.1 _ (by decide), k4.regs.1 _ (by decide), k3.1 _ (by decide), k2b.regs.1 _ (by decide),
      k2.regs.1 _ (by decide)]
  · exact ((((k2.regs.mono (by decide)).trans (k2b.regs.mono (by decide))).trans (k3.mono (by decide))).trans
      (k4.regs.mono (by decide))).trans ((k5.regs.mono (by decide)).trans (kt.mono (by decide)))
  · rw [mt]
    exact (((fkeep_dframe k2).trans (fkeep_dframe k2b)).trans (DFrame.of_outside o3 (by simp only [slot]; omega_using []))).trans
      ((fkeep_dframe k4).trans (fkeep_dframe k5))

/-- `x19 := x1 - x3`. -/
theorem sub19_ok (s : State) :
    WP isa (.block [.sub .x .x19 .x1 .x3]) s fun t =>
      t.gpr .x19 = s.gpr .x1 - s.gpr .x3 ∧ Keeps [.x19] s t ∧ t.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl⟩, rfl⟩

/-- A loop whose body runs twice. -/
theorem WP.loop2 {b : Prog isa} {c : isa.Cond} {s : State} {Q : State → Prop}
    (h : WP isa b s fun t => isa.eval c t = some true ∧
      WP isa b t fun u => isa.eval c u = some false ∧ Q u) : WP isa (.loop b c) s Q := by
  obtain ⟨t₁, s₁, e₁, hc₁, t₂, s₂, e₂, hc₂, q⟩ := h
  exact ⟨_, _, Exec.loopNext e₁ hc₁ (Exec.loopExit e₂ hc₂), q⟩

theorem WP.ite_of {c : isa.Cond} {th el : Prog isa} {s : State} {Q : State → Prop} {b : Bool}
    (hc : isa.eval c s = some b) (ht : b = true → WP isa th s Q) (he : b = false → WP isa el s Q) :
    WP isa (.ite c th el) s Q := by
  cases b
  · obtain ⟨t, s', e, q⟩ := he rfl; exact ⟨_, _, Exec.iteF hc e, q⟩
  · obtain ⟨t, s', e, q⟩ := ht rfl; exact ⟨_, _, Exec.iteT hc e, q⟩

theorem eval19 {s : State} {b : Bool} (h : (s.gpr .x19 != 0) = b) :
    isa.eval (.nonzero .x .x19) s = some b := by
  simp only [eval, State.read, BitVec.setWidth_eq, h]

/-- An address at least 8192 bytes past the working space differs from its base. -/
theorem ne_of_far {base p : Addr} (h : 8192 ≤ ofs base (p + BitVec.ofNat 64 0)) : (p - base != 0) = true := by
  rw [BitVec.add_zero] at h
  have : p - base ≠ 0 := fun e => by rw [ofs, e] at h; exact absurd h (by decide)
  simpa using this

/-- **`A` and `R` decoded by one copy of `decode`**: the loop's first pass decodes `A` (from `x0`)
into slots 8–9 and negates it into 6–7 (`negA_ok`), the second decodes `R` (from `x1`, which
`negA` moved into `x0`) into 8–9. `x1 - x3`, after each, is nonzero after `A`, since `R` lies outside the
working space, and 0 after `R`, since `negA` moved `x3` into `x1`. -/
theorem decodes_ok (hR : RecoverOk) {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base)
    (h11 : E s.mem base 11 = Spec.Ed448.d)
    (hrA : ∀ j < 57, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 j) 1)
    (hfA : ∀ j < 57, 8192 ≤ ofs base (s.gpr .x0 + BitVec.ofNat 64 j))
    (hrR : ∀ j < 57, InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 j) 1)
    (hfR : ∀ j < 57, 8192 ≤ ofs base (s.gpr .x1 + BitVec.ofNat 64 j)) :
    WP isa decodes s fun t =>
      (∃ cA cR : BitVec 64,
        (cA = 0 ↔ (Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (s.gpr .x0) 57)).isSome) ∧
        (cR = 0 ↔ (Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (s.gpr .x1) 57)).isSome) ∧
        t.gpr .x20 = s.gpr .x20 ||| cA ||| cR) ∧
      (∀ a, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (s.gpr .x0) 57) = some a →
        (⟨E t.mem base 6, E t.mem base 7, 1⟩ : Spec.Ed448.Point) = negPoint a) ∧
      (∀ r, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (s.gpr .x1) 57) = some r →
        E t.mem base 8 = r.X ∧ E t.mem base 9 = r.Y ∧ r.Z = 1) ∧
      E t.mem base 11 = Spec.Ed448.d ∧ Scr t base ∧ BEnv t.mem base ∧ Keeps (.x0 :: .x1 :: .x19 :: decClob) s t ∧
      DFrame base s.mem t.mem := by
  unfold decodes
  refine WP.loop2 ?_
  -- The first pass: `A`.
  refine WP.seq (WP.mono (decode_ok hR hs hb (p := s.gpr .x0) rfl (Or.inl rfl) 8 9 (Or.inr ⟨rfl, rfl⟩) h11 hrA hfA)
    fun s1 ⟨⟨cA, hcA, x1'⟩, v1, kp1, one1, b1, g1, f1⟩ => ?_)
  obtain hs1 : Scr s1 base := hs.of_keeps g1 (by decide)
  refine WP.seq (WP.mono (sub19_ok s1) fun s2 ⟨c2, k2, m2⟩ => ?_)
  obtain hs2 := hs1.of_keeps k2 (by decide)
  obtain z2 : (s2.gpr .x19 != 0) = true := by
    rw [c2, g1.1 _ (by decide), hs1.x3]; exact ne_of_far (hfR 0 (by decide))
  refine WP.ite_of (eval19 z2) (fun _ => ?_) (fun h => absurd h (by decide))
  refine WP.mono (negA_ok hs2 (by rw [m2]; exact b1) (by rw [m2]; exact one1)
    (by rw [c2, k2.1 .x1 (by decide), k2.1 .x3 (by decide)]))
    fun s3 ⟨n6, n7, nk, x03, x13', hs3, b3, k3, f3⟩ => ⟨eval19 (by rw [k3.1 _ (by decide)]; exact z2), ?_⟩
  obtain O3 : Outside base 0 8192 s.mem s3.mem := (f1.trans (by rw [← m2]; exact f3)).whole
  obtain rr3 : s3.rd ++ s3.wr = s.rd ++ s.wr := by
    rw [k3.2.1, k3.2.2, k2.2.1, k2.2.2, g1.2.1, g1.2.2]
  obtain x13 : s3.gpr .x0 = s.gpr .x1 := by
    rw [x03, k2.1 _ (by decide), g1.1 _ (by decide)]
  obtain e11 : E s3.mem base 11 = Spec.Ed448.d := by
    rw [nk 11 (by decide) (by decide) (by decide) (by decide), m2,
      kp1 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h11]
  -- The second pass: `R`.
  refine WP.seq (WP.mono (decode_ok hR hs3 b3 (p := s.gpr .x1) x13 (Or.inl rfl) 8 9 (Or.inr ⟨rfl, rfl⟩) e11
    (by rw [rr3]; exact hrR) hfR) fun s4 ⟨⟨cR, hcR, x4'⟩, v4, kp4, one4, b4, g4, f4⟩ => ?_)
  rw [far_bytes O3 hfR] at hcR v4
  obtain hs4 : Scr s4 base := hs3.of_keeps g4 (by decide)
  refine WP.seq (WP.mono (sub19_ok s4) fun s5 ⟨c5, k5, m5⟩ => ?_)
  obtain z5 : (s5.gpr .x19 != 0) = false := by
    rw [c5, g4.1 _ (by decide), x13', hs4.x3, hs2.x3, BitVec.sub_self]; rfl
  refine WP.ite_of (eval19 z5) (fun h => absurd h (by decide)) (fun _ => ?_)
  refine WP.mono (mov01_ok s5) fun s6 ⟨_, m6, k6⟩ => ⟨eval19 (by rw [k6.1 _ (by decide)]; exact z5), ?_⟩
  obtain k46 : ∀ i : Fin 22, i = 6 ∨ i = 7 → E s4.mem base i = E s3.mem base i := by
    rintro i (rfl | rfl) <;>
      exact kp4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨⟨cA, cR, hcA, hcR, ?_⟩, fun a ha => ?_, fun r hr => ?_, ?_, (hs4.of_keeps k5 (by decide)).of_keeps k6 (by decide),
    by rw [m6, m5]; exact b4, ?_, ?_⟩
  · rw [k6.1 _ (by decide), k5.1 _ (by decide), x4', k3.1 _ (by decide), k2.1 _ (by decide), x1']
  · obtain ⟨vx, vy, hz⟩ := v1 a ha
    rw [m6, m5, k46 6 (.inl rfl), k46 7 (.inr rfl), n6, n7, m2, vx, vy, VG.Proof.Ed448.negPoint, hz]
  · rw [m6, m5]; exact v4 r hr
  · rw [m6, m5, kp4 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), e11]
  · exact ((((g1.mono (by decide)).trans (k2.mono (by decide))).trans
      (k3.mono (by decide))).trans (g4.mono (by decide))).trans (k5.mono (by decide)) |>.trans (k6.mono (by decide))
  · rw [m6, m5]
    exact ((f1.trans (by rw [← m2]; exact f3)).trans f4)

end VG.Proof.Ed448.AArch64

end

end


/-!
# Ed448 verification on AArch64: the entry and the decodings

Untrusted: everything here is checked by Lean. `wfront`: the entry
(`ventry_ok`), the challenge copied to `KB` and the callee-saved registers
saved, the bits of `S` at `BITS`, the check of `S`, and the decodings of `A`
(negated, slots 6–7) and `R` (slots 8–9), each check ORed into `x20`
(`wfront_ok`, `FrontOut`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Window

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (ld st slot ACC BITS)
open VG.Impl.X448.AArch64.Fast (saved SAVE VSAVE)
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 ofs Saved)
open VG.Proof.X448.AArch64.Weak (E BoundedEnv)
open VG.Proof.X448.AArch64.Fast (SavedX SavedV save_ok vsave_ok)
open VG.Proof.X448.AArch64.Base (Bits)
open VG.Proof.Ed448.AArch64 (DFrame ventry_ok sCheck_ok decodes_ok bitsAt_ok far_bytes)
open VG.Spec.Ed448 (bytesAt decodeLE decodePoint Point)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-! ## What frames keep -/

theorem Saved.dframe {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : DFrame base m m') (hs : Saved base g m) :
    Saved base g m' :=
  ⟨(h.word (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide)) (by decide)).trans hs.1,
    (h.word (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide)) (by decide)).trans hs.2⟩

theorem LrSaved.dframe {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : DFrame base m m')
    (hs : LrSaved base g m) : LrSaved base g m' :=
  (h.word (Or.inr (by simp only [LRS]; omega_arith)) (Or.inl (by simp only [ACC, LRS]; omega_arith))
    (Or.inl (by simp only [CAN, LRS]; omega_arith)) (by simp only [LRS]; omega_arith)).trans hs

theorem SavedX.dframe {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : DFrame base m m') (hs : SavedX base g m) :
    SavedX base g m' := fun k hk =>
  (h.word (Or.inr (by simp only [SAVE]; omega_arith)) (Or.inl (by simp only [ACC, SAVE]; omega_arith))
    (Or.inl (by simp only [CAN, SAVE]; omega_arith)) (by simp only [SAVE]; omega_arith)).trans (hs k hk)

theorem SavedV.dframe {base : Addr} {v : VReg → BitVec 128} {m m' : Mem} (h : DFrame base m m') (hs : SavedV base v m) :
    SavedV base v m' := by
  have hV : VSAVE = 4736 := rfl
  refine hs.frame fun d h1 h2 => ?_
  obtain ho : ofs base (off base d) = d := ofs_off0' base (by omega_arith)
  exact h _ (by rw [ho]; omega_arith) (by rw [ho]; simp only [ACC]; omega_arith) (by rw [ho]; simp only [CAN]; omega_arith)

/-- The challenge's copy at `KB`. -/
def KBytes (base : Addr) (m : Mem) (b : Nat → BitVec 8) : Prop := ∀ i < 57, m (off base (KB + i)) = b i

theorem KBytes.of_frame {base : Addr} {m m' : Mem} {b : Nat → BitVec 8} (h : KBytes base m b)
    (hf : ∀ i < 57, m' (off base (KB + i)) = m (off base (KB + i))) : KBytes base m' b := fun i hi => by
  rw [hf i hi]; exact h i hi

theorem kb_ofs (base : Addr) {i : Nat} (hi : i < 57) : ofs base (off base (KB + i)) = KB + i :=
  ofs_off0' base (by simp only [KB]; omega_arith)

theorem bits_ofs (base : Addr) {t : Nat} (ht : t < 456) : ofs base (off base (BITS + t)) = BITS + t :=
  ofs_off0' base (by simp only [BITS]; omega_arith)

/-! ## The front -/

/-- What `wfront` leaves, from the entry state `s`. -/
structure FrontOut (s : State) (base : Addr) (t : State) : Prop where
  scr : Scr t base
  bnd : VG.Proof.X448.AArch64.Fast.BEnv t.mem base
  chk : ∃ c0 cA cR : BitVec 64, t.gpr .x20 = 0 ||| c0 ||| cA ||| cR ∧
    (c0 = 0 ↔ decodeLE (bytesAt s.mem (s.gpr .x1 + BitVec.ofNat 64 57) 57) < Spec.Ed448.L) ∧
    (cA = 0 ↔ (decodePoint (bytesAt s.mem (s.gpr .x0) 57)).isSome) ∧
    (cR = 0 ↔ (decodePoint (bytesAt s.mem (s.gpr .x1) 57)).isSome)
  na : ∀ a, decodePoint (bytesAt s.mem (s.gpr .x0) 57) = some a → slotPt t.mem base = VG.Proof.Ed448.negPoint a
  rr : ∀ r, decodePoint (bytesAt s.mem (s.gpr .x1) 57) = some r → EV t.mem base 8 = r.X ∧ EV t.mem base 9 = r.Y ∧
    r.Z = 1
  bits : Bits 57 base (decodeLE (bytesAt s.mem (s.gpr .x1 + BitVec.ofNat 64 57) 57)) t.mem
  kb : KBytes base t.mem fun i => s.mem (s.gpr .x2 + BitVec.ofNat 64 i)
  saved : Saved base s.gpr t.mem
  savedX : SavedX base s.gpr t.mem
  savedV : SavedV base s.v t.mem
  lrs : LrSaved base s.gpr t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base 0 8192 s.mem t.mem

theorem wsave_eq : wsave = (((List.range 57).flatMap fun i => [.ldrb .x4 .x2 i, .strb .x4 .x3 (KB + i)]) ++
    Impl.X448.AArch64.Fast.save) ++ Impl.X448.AArch64.Fast.vsave := by
  simp only [wsave, List.append_assoc]

/-- What the entry block leaves. -/
structure EntryOut (s : State) (base : Addr) (t : State) : Prop where
  scr : Scr t base
  bnd : BoundedEnv t.mem base
  saved : Saved base s.gpr t.mem
  savedX : SavedX base s.gpr t.mem
  lrs : LrSaved base s.gpr t.mem
  x20 : t.gpr .x20 = 0
  kb : KBytes base t.mem fun i => s.mem (s.gpr .x2 + BitVec.ofNat 64 i)
  regs : Keeps [.x12, .x20, .x4] s t
  mem : Outside base 0 8192 s.mem t.mem
  e0 : E t.mem base 0 = 0
  pB : VG.Proof.Ed448.pt (E t.mem base) 8 9 10 = Spec.Ed448.basePoint
  d : E t.mem base 11 = Spec.Ed448.d

/-- After the entry (`ventry_ok`), the challenge's copy and the save of `x21`–`x28`. -/
theorem prefix_ok {s s1 : State} {base : Addr}
    (V : Scr s1 base ∧ BoundedEnv s1.mem base ∧ Saved base s.gpr s1.mem ∧ LrSaved base s.gpr s1.mem ∧
      s1.gpr .x20 = 0 ∧ Keeps [.x12, .x20, .x4] s s1 ∧ Outside base 0 8192 s.mem s1.mem ∧
      E s1.mem base 0 = 0 ∧ VG.Proof.Ed448.pt (E s1.mem base) 8 9 10 = Spec.Ed448.basePoint ∧
      E s1.mem base 11 = Spec.Ed448.d)
    (rch : ∀ i < 57, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 i) 1)
    (fch : ∀ i < 57, 8192 ≤ ofs base (s.gpr .x2 + BitVec.ofNat 64 i)) :
    WP isa (.block (((List.range 57).flatMap fun i => [.ldrb .x4 .x2 i, .strb .x4 .x3 (KB + i)]) ++
      Impl.X448.AArch64.Fast.save)) s1 (EntryOut s base) := by
  obtain ⟨hs1, b1, sv1, lr1, x20₁, k1, o1, z1, pB1, d1⟩ := V
  rw [WP.block_append_iff]
  refine WP.mono (copyK_ok hs1 (k1.1 _ (by decide)) (fun i hi => by rw [k1.2.1, k1.2.2]; exact rch i hi) fch)
    fun s2 ⟨kb2, o2, k2⟩ => ?_
  obtain hs2 := hs1.of_keeps k2 (by decide)
  refine WP.mono (save_ok hs2) fun t ⟨svx, o3, g3, rd3, wr3⟩ => ?_
  obtain o13 : Outside base SAVE 128 s1.mem t.mem :=
    (o2.mono (by simp only [SAVE, KB]; omega_arith) (by simp only [SAVE, KB]; omega_arith)).trans
      (o3.mono (Nat.le_refl _) (by omega_arith))
  obtain keepSlot : ∀ i : Fin 22, E t.mem base i = E s1.mem base i := fun i =>
    VG.Proof.X448.AArch64.Weak.E_outside o13 i (Or.inl (by have := i.isLt; simp only [slot, SAVE]; omega_arith))
  refine ⟨hs2.of_keeps (rs := []) ⟨fun r _ => congrFun g3 r, rd3, wr3⟩ (by decide), fun i j hj => ?_, ?_, ?_,
    lr1.outside o13 (Or.inr (by decide)), ?_, fun i hi => ?_, ?_, ?_, by rw [keepSlot]; exact z1, ?_,
    by rw [keepSlot]; exact d1⟩
  · rw [o13.limbs (Or.inl (by have := i.isLt; simp only [slot, SAVE]; omega_arith)) (by have := i.isLt; simp only [slot]; omega_arith)
      (by omega_arith)]
    exact b1 i j hj
  · exact (sv1.outside o13 (by decide))
  · intro k hk
    rw [svx k hk, congrFun (show s2.gpr = s2.gpr from rfl) _, k2.1 _ (by
      have : saved k ≠ .x4 := by revert k; decide
      simpa using this), k1.1 _ (by
      have : saved k ∉ [Reg.x12, .x20, .x4] := by revert k; decide
      exact this)]
  · rw [congrFun g3 .x20, k2.1 _ (by decide)]; exact x20₁
  · rw [o3 _ (Or.inr (by rw [kb_ofs base hi]; simp only [SAVE, KB]; omega_arith))]
    rw [kb2 i hi, o1 _ (Or.inr (fch i hi))]
  · exact (k1.trans (k2.mono (by decide))).trans ⟨fun r _ => congrFun g3 r, rd3, wr3⟩ |>.mono (by decide)
  · exact o1.trans ((o13.mono (by decide) (by decide)) : Outside base 0 8192 s1.mem t.mem) |>.trans (Outside.refl _ _ _ _)
  · simp only [VG.Proof.Ed448.pt]; rw [keepSlot 8, keepSlot 9, keepSlot 10]; exact pB1

theorem V_preserved : ∀ k < 8, VG.Impl.Curve448.AArch64.Neon.V (8 + k) ∈ preservedV := by decide

/-- The entry block: `EntryOut`, and `v8`–`v15` saved. -/
theorem entry_ok {s : State} {base : Addr} (hb3 : s.gpr .x3 = base) (hw : (⟨base, 8192⟩ : Region) ∈ s.wr)
    (hn : base.toNat + 8192 ≤ 2 ^ 64) (rch : ∀ i < 57, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 i) 1)
    (fch : ∀ i < 57, 8192 ≤ ofs base (s.gpr .x2 + BitVec.ofNat 64 i)) :
    WP isa (.seq ventry (.block wsave)) s fun t => EntryOut s base t ∧ SavedV base s.v t.mem := by
  refine WP.seq (WP.mono (WP.preservedV (ventry_ok hb3 hw hn) (by lit_decide)) fun s1 ⟨V1, v1⟩ => ?_)
  rw [wsave_eq]
  refine WP.block_append_iff.mpr (WP.mono (WP.preservedV (prefix_ok V1 rch fch) (by lit_decide))
    fun s3 ⟨E3, v3⟩ => WP.mono (vsave_ok E3.scr) fun s4 ⟨svv, o4, g4, rd4, wr4⟩ => ?_)
  have hV : VSAVE = 4736 := rfl
  obtain k4 : Keeps [] s3 s4 := ⟨fun r _ => congrFun g4 r, rd4, wr4⟩
  refine ⟨⟨E3.scr.of_keeps k4 (by decide), fun i j hj => ?_, E3.saved.outside o4 (by decide),
    E3.savedX.outside o4 (Or.inr (by decide)), E3.lrs.outside o4 (Or.inl (by decide)),
    by rw [congrFun g4]; exact E3.x20,
    E3.kb.of_frame fun i hi => o4 _ (Or.inl (by rw [kb_ofs base hi]; simp only [KB]; omega_arith)),
    E3.regs.trans (k4.mono (by decide)), E3.mem.trans (o4.mono (by decide) (by decide)), ?_, ?_, ?_⟩,
    fun k hk => by rw [svv k hk, v3 _ (V_preserved k hk), v1 _ (V_preserved k hk)]⟩
  · rw [o4.limbs (Or.inl (by have := i.isLt; simp only [slot]; omega_arith)) (by have := i.isLt; simp only [slot]; omega_arith)
      (by omega_arith)]
    exact E3.bnd i j hj
  · rw [VG.Proof.X448.AArch64.Weak.E_outside o4 0 (Or.inl (by simp only [slot]; omega_arith))]; exact E3.e0
  · simp only [VG.Proof.Ed448.pt]
    rw [VG.Proof.X448.AArch64.Weak.E_outside o4 8 (Or.inl (by simp only [slot]; omega_arith)),
      VG.Proof.X448.AArch64.Weak.E_outside o4 9 (Or.inl (by simp only [slot]; omega_arith)),
      VG.Proof.X448.AArch64.Weak.E_outside o4 10 (Or.inl (by simp only [slot]; omega_arith))]
    exact E3.pB
  · rw [VG.Proof.X448.AArch64.Weak.E_outside o4 11 (Or.inl (by simp only [slot]; omega_arith))]; exact E3.d

theorem wfront_ok (hR : VG.Proof.Ed448.RecoverOk) {s : State} {base : Addr} (hb3 : s.gpr .x3 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : base.toNat + 8192 ≤ 2 ^ 64)
    (rpk : ∀ i < 57, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 i) 1)
    (rsg : ∀ i < 114, InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 i) 1)
    (rch : ∀ i < 57, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 i) 1)
    (fpk : ∀ i < 57, 8192 ≤ ofs base (s.gpr .x0 + BitVec.ofNat 64 i))
    (fsg : ∀ i < 114, 8192 ≤ ofs base (s.gpr .x1 + BitVec.ofNat 64 i))
    (fch : ∀ i < 57, 8192 ≤ ofs base (s.gpr .x2 + BitVec.ofNat 64 i)) :
    WP isa wfront s (FrontOut s base) := by
  unfold wfront
  refine WP.seq (WP.mono (entry_ok hb3 hw hn rch fch) fun s4 ⟨E4, sv4⟩ => ?_)
  have hs4 := E4.scr
  obtain rr4 : s4.rd ++ s4.wr = s.rd ++ s.wr := by rw [E4.regs.2.1, E4.regs.2.2]
  obtain x1₄ : s4.gpr .x1 = s.gpr .x1 := E4.regs.1 _ (by decide)
  obtain x0₄ : s4.gpr .x0 = s.gpr .x0 := E4.regs.1 _ (by decide)
  -- The bits of `S`.
  refine WP.seq (WP.mono (bitsAt_ok (so := 57) (d1 := 0) (d2 := BITS) hs4 x1₄ (by decide) (by decide) (by decide)
    (by decide) (by decide) (fun q hq => by rw [rr4]; exact rsg _ (by omega_arith))
    (fun q hq => fsg _ (by omega_arith))) fun s5 ⟨g5, rd5, wr5, o5, bits5⟩ => ?_)
  obtain hs5 : Scr s5 base := ⟨(g5 _ (by decide)).trans hs4.x3, (g5 _ (by decide)).trans hs4.mask, wr5 ▸ hs4.wr, hn⟩
  obtain rr5 : s5.rd ++ s5.wr = s.rd ++ s.wr := by rw [rd5, wr5, rr4]
  obtain O5 : Outside base 0 8192 s.mem s5.mem := E4.mem.trans (o5.mono (by decide) (by decide))
  -- The check of `S`.
  refine WP.seq (WP.mono (sCheck_ok (p := s.gpr .x1) ((g5 _ (by decide)).trans x1₄)
    (fun j hj => by rw [rr5]; exact rsg _ (by omega_arith))) fun s6 ⟨⟨c0, hc0, x6'⟩, m6, k6⟩ => ?_)
  rw [far_bytes O5 (fun i hi => by rw [Offset.add_add]; exact fsg _ (by omega_arith))] at hc0
  obtain hs6 : Scr s6 base := hs5.of_keeps k6 (by decide)
  obtain rr6 : s6.rd ++ s6.wr = s.rd ++ s.wr := by rw [k6.2.1, k6.2.2, rr5]
  obtain O6 : Outside base 0 8192 s.mem s6.mem := by rw [m6]; exact O5
  obtain b6 : VG.Proof.X448.AArch64.Fast.BEnv s6.mem base := VG.Proof.Ed448.AArch64.benv_of_weak fun i j hj => by
    rw [m6, o5.limbs (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega_arith)) (by have := i.isLt; simp only [slot]; omega_arith)
      (by omega_arith)]
    exact E4.bnd i j hj
  obtain e6 : ∀ i : Fin 22, E s6.mem base i = E s4.mem base i := fun i => by
    rw [m6]; exact VG.Proof.X448.AArch64.Weak.E_outside o5 i (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega_arith))
  -- `A` and `R`, decoded by one copy of `decode`.
  obtain x0₆ : s6.gpr .x0 = s.gpr .x0 := (k6.1 _ (by decide)).trans ((g5 _ (by decide)).trans x0₄)
  obtain x1₆ : s6.gpr .x1 = s.gpr .x1 := (k6.1 _ (by decide)).trans ((g5 _ (by decide)).trans x1₄)
  refine WP.mono (decodes_ok hR hs6 b6 (by rw [e6]; exact E4.d)
    (fun j hj => by rw [rr6, x0₆]; exact rpk _ hj) (fun j hj => by rw [x0₆]; exact fpk _ hj)
    (fun j hj => by rw [rr6, x1₆]; exact rsg _ (by omega_arith)) (fun j hj => by rw [x1₆]; exact fsg _ (by omega_arith)))
    fun t ⟨⟨cA, cR, hcA, hcR, xt⟩, nat, vt, _, hst, bt, gt, ft⟩ => ?_
  simp only [x0₆, x1₆, far_bytes O6 fpk, far_bytes O6 (fun i (hi : i < 57) => fsg _ (by omega_arith))] at hcA hcR nat vt
  obtain s4b : bytesAt s4.mem (s.gpr .x1 + BitVec.ofNat 64 57) 57 = bytesAt s.mem (s.gpr .x1 + BitVec.ofNat 64 57) 57 :=
    far_bytes E4.mem (fun i hi => by rw [Offset.add_add]; exact fsg _ (by omega_arith))
  have o45 : Outside base BITS 456 s4.mem s5.mem := o5
  refine ⟨hst, bt, ⟨c0, cA, cR, ?_, hc0, hcA, hcR⟩, fun a ha => nat a ha, vt, fun q hq => ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [xt, x6', g5 _ (by decide), E4.x20]
  · have hq' : q < 456 := hq
    rw [ft _ (by rw [bits_ofs base hq']; simp only [BITS]; omega_arith) (by rw [bits_ofs base hq']; simp only [BITS, ACC]; omega_arith)
      (by rw [bits_ofs base hq']; simp only [BITS, CAN]; omega_arith), m6]
    have := bits5 q hq'
    rw [Nat.zero_add, s4b] at this
    exact this
  · refine E4.kb.of_frame fun i hi => ?_
    obtain ho := kb_ofs base hi
    rw [ft _ (by rw [ho]; simp only [KB]; omega_arith) (by rw [ho]; simp only [KB, ACC]; omega_arith)
      (by rw [ho]; simp only [KB, CAN]; omega_arith), m6, o45 _ (Or.inl (by rw [ho]; simp only [KB, BITS]; omega_arith))]
  · exact Saved.dframe ft (by rw [m6]; exact E4.saved.outside o45 (by decide))
  · exact SavedX.dframe ft (by rw [m6]; exact E4.savedX.outside o45 (Or.inr (by decide)))
  · exact SavedV.dframe ft (by rw [m6]; exact sv4.outside o45 (Or.inl (by decide)))
  · exact LrSaved.dframe ft (by rw [m6]; exact E4.lrs.outside o45 (Or.inl (by decide)))
  · rw [gt.2.1, k6.2.1, rd5, E4.regs.2.1]
  · rw [gt.2.2, k6.2.2, wr5, E4.regs.2.2]
  · exact O6.trans ft.whole

end VG.Proof.Ed448.AArch64.Window
