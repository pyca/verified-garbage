module
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.AArch64.Isa

import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
public import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Impl.Bignum.Layout
import VerifiedGarbage.TCB.AArch64.Simd
import VerifiedGarbage.Impl.Bignum.AArch64.Core

/-! A table row's SIMD comparison and masked insertion. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

abbrev dup2 (x : BitVec 64) : BitVec 128 := ofVDwords x x

theorem cmeq_dup2 (x y : BitVec 64) :
    VArr.d2.map2 (fun w x y => if x = y then BitVec.allOnes w else 0) (dup2 x) (dup2 y) =
      if x = y then BitVec.allOnes 128 else 0 := by
  simp only [VArr.map2, dup2, vdword_ofVDwords_0, vdword_ofVDwords_1]
  by_cases h : x = y
  · simp only [h, ite_true]; decide
  · simp only [h, ite_false]; decide

theorem bit_mask (d n : BitVec 128) (c : Prop) [Decidable c] :
    VSelOp.bit.eval d n (if c then BitVec.allOnes 128 else 0) = if c then n else d := by
  by_cases hc : c
  · simp only [hc, ite_true, VSelOp.eval, BitVec.and_allOnes, ← BitVec.xor_assoc,
      BitVec.xor_self, BitVec.zero_xor]
  · simp [hc, VSelOp.eval]

/-- A fixed-address load and BIT either replace the entire accumulator or
leave it unchanged. Memory, scalar registers and all other vectors are intact. -/
theorem loadBit_ok {s : State} {r : VReg} {i : Nat} {choose : Prop} [Decidable choose]
    (hr' : r ≠ .v21) (hi : i < 4)
    (hm : s.v .v20 = if choose then BitVec.allOnes 128 else 0)
    (hld : InRegions (s.rd ++ s.wr) (s.gpr .x16 + BitVec.ofNat 64 (16 * i)) 16) :
    WP isa (.block [.ldrq .v21 .x16 (16 * i), .vop (.bsel .bit r .v21 .v20)]) s fun t =>
      t = (s.setV .v21 (s.mem.read (s.gpr .x16 + BitVec.ofNat 64 (16 * i)) 16)).setV r
        (if choose then s.mem.read (s.gpr .x16 + BitVec.ofNat 64 (16 * i)) 16 else s.v r) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec, addr, show 16 * i % 16 = 0 by omega,
    show 16 * i < 4096 * 16 by omega, and_self, ite_true, Option.bind_some,
    State.load, hld, Option.map_some, runStep_some, VOp.eval,
    RegUpd.v_setV_self, RegUpd.v_setV_of_ne _ _ (show VReg.v20 ≠ .v21 by decide),
    RegUpd.v_setV_of_ne _ _ hr', hm, bit_mask, runBlock_nil,
    Option.some.injEq, exists_eq_left']

/-- Memory and all registers outside the listed SIMD destinations are unchanged. -/
structure VKeep (vs : List VReg) (s t : State) : Prop where
  gpr : t.gpr = s.gpr
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  v : ∀ r, r ∉ vs → t.v r = s.v r

theorem VKeep.setV (s : State) (r : VReg) (x : BitVec 128) : VKeep [r] s (s.setV r x) :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun q hq =>
    RegUpd.v_setV_of_ne s x (by simpa only [List.mem_singleton] using hq)⟩

theorem VKeep.trans {xs ys : List VReg} {s t u : State}
    (h : VKeep xs s t) (k : VKeep ys t u) : VKeep (xs ++ ys) s u :=
  ⟨k.gpr.trans h.gpr, k.mem.trans h.mem, k.rd.trans h.rd, k.wr.trans h.wr,
    k.sp.trans h.sp, fun r hr => (k.v r (fun hy => hr (List.mem_append_right _ hy))).trans
      (h.v r (fun hx => hr (List.mem_append_left _ hx)))⟩

theorem VKeep.mono {xs ys : List VReg} {s t : State}
    (h : VKeep xs s t) (hs : ∀ r ∈ xs, r ∈ ys) : VKeep ys s t :=
  ⟨h.gpr, h.mem, h.rd, h.wr, h.sp, fun r hr => h.v r (fun hx => hr (hs r hx))⟩

theorem loadBit_value {s : State} {r : VReg} {i : Nat} {choose : Prop} [Decidable choose]
    (hr : r ≠ .v21) (hi : i < 4)
    (hm : s.v .v20 = if choose then BitVec.allOnes 128 else 0)
    (hld : InRegions (s.rd ++ s.wr) (s.gpr .x16 + BitVec.ofNat 64 (16 * i)) 16) :
    WP isa (.block [.ldrq .v21 .x16 (16 * i), .vop (.bsel .bit r .v21 .v20)]) s fun t =>
      t.v r = (if choose then s.mem.read (s.gpr .x16 + BitVec.ofNat 64 (16 * i)) 16 else s.v r) ∧
      VKeep [.v21, r] s t := by
  refine WP.mono (loadBit_ok hr hi hm hld) fun t ht => ?_
  subst t
  exact ⟨RegUpd.v_setV_self _ _ _,
    (VKeep.setV _ _ _).trans (VKeep.setV _ _ _)⟩

end VG.Proof.Bignum.AArch64.WindowVector
