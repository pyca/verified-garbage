module

import VerifiedGarbage.Proof.Gcm.X86_64.Rev
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemQuad
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemQuadK
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemMask
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemLoopOne
import VerifiedGarbage.Proof.Framework.X86_64.Lane0Zero
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.SpecP

/-!
# The loops over the blocks after the last group

`remLoops_ok`: the loops of `StitchZH.remLoops`, over the `r` blocks at `S`
(read through `src`), their keystream at `P + 768` and their powers at `W`,
write their encryption to `A` and leave in `Y` their products with their
powers (`Y` added to the first), reduced and added. The first `r mod 4`
blocks go each to its own lane: one alone to lane 0 (`remStep1_ok`, `RInv1`),
two or three through a mask (`remStepK_ok`); the rest four at a time, one to
each lane (`remStep4_ok`, `RInv4`): block `j` to lane `laneOf r j`, whose
products are `laneAcc`. `StitchZ.fin` reduces the four
lanes and adds them (`RPost`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.StitchZ (fin)
open VG.Proof.Gcm.X86_64.StitchZ (fin_ok)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq pshufb_rev_xor)
open VG.Proof.Gcm.X86_64.Stitch (blockAt_writeW_sep')
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame)
open VG.Spec.Gcm (Block blockAt)

/-- The lane block `j` of the last `r` goes to: each of the first `r mod 4`
to its own, the others four at a time, one to each lane. -/
def laneOf (r j : Nat) : Nat := if j < r % 4 then j else (j - r % 4) % 4

/-- The products in lane `l` of the first `n` of the last `r` blocks `X`
with their powers `T`, `y` added to the first. -/
def laneAcc (X : Nat → Block) (T : Nat → BitVec 128) (y : Block) (r l : Nat) : Nat → Prod
  | 0 => Prod.zero
  | n + 1 => if laneOf r n = l then (laneAcc X T y r l n).acc ((if n = 0 then y else 0) ^^^ X n) (T n)
      else laneAcc X T y r l n

theorem laneAcc_congr {X X' : Nat → Block} {T T' : Nat → BitVec 128} (y : Block) (r l : Nat) :
    ∀ n, (∀ j < n, X j = X' j) → (∀ j < n, T j = T' j) → laneAcc X T y r l n = laneAcc X' T' y r l n
  | 0, _, _ => rfl
  | n + 1, hX, hT => by
    simp only [laneAcc]
    rw [laneAcc_congr y r l n (fun j hj => hX j (by omega)) (fun j hj => hT j (by omega)), hX n (by omega),
      hT n (by omega)]

/-- The first `r mod 4` blocks, each in its own lane. -/
theorem laneAcc_first {X : Nat → Block} {T : Nat → BitVec 128} {y : Block} {r l : Nat} :
    ∀ n, n ≤ r % 4 → laneAcc X T y r l n =
      if l < n then Prod.zero.acc ((if l = 0 then y else 0) ^^^ X l) (T l) else Prod.zero
  | 0, _ => by simp [laneAcc]
  | n + 1, hn => by
    have h0 : laneOf r n = n := by unfold laneOf; rw [ite_eq_left (show n < r % 4 by omega)]
    simp only [laneAcc, h0]
    rw [laneAcc_first n (by omega)]
    by_cases hnl : n = l
    · subst hnl
      rw [ite_eq_left rfl, ite_eq_right (Nat.lt_irrefl n), ite_eq_left (Nat.lt_succ_self n)]
    · rw [ite_eq_right hnl]
      by_cases hl : l < n
      · rw [ite_eq_left hl, ite_eq_left (show l < n + 1 by omega)]
      · rw [ite_eq_right hl, ite_eq_right (show ¬ l < n + 1 by omega)]

/-- The block alone of the first `r mod 4 = 1`, to lane 0. -/
theorem laneAcc_lo {X : Nat → Block} {T : Nat → BitVec 128} {y : Block} {r i : Nat} (hi : i < r % 4)
    (h1 : r % 4 = 1) :
    laneAcc X T y r 0 (i + 1) = (laneAcc X T y r 0 i).acc ((if i = 0 then y else 0) ^^^ X i) (T i) := by
  have h0 : laneOf r i = 0 := by unfold laneOf; split <;> omega
  simp only [laneAcc, h0, ite_true]

/-- Four blocks, one to each lane. -/
theorem laneAcc_quad {X : Nat → Block} {T : Nat → BitVec 128} {y : Block} {r i : Nat} (hk : r % 4 ≤ i)
    (hmd : (i - r % 4) % 4 = 0) {l : Nat} (hl : l < 4) :
    laneAcc X T y r l (i + 4) =
      (laneAcc X T y r l i).acc ((if i + l = 0 then y else 0) ^^^ X (i + l)) (T (i + l)) := by
  have h0 : laneOf r i = 0 := by unfold laneOf; split <;> omega
  have h1 : laneOf r (i + 1) = 1 := by unfold laneOf; split <;> omega
  have h2 : laneOf r (i + 2) = 2 := by unfold laneOf; split <;> omega
  have h3 : laneOf r (i + 3) = 3 := by unfold laneOf; split <;> omega
  rw [show i + 4 = i + 3 + 1 from rfl]
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;>
  simp only [laneAcc, h0, h1, h2, h3, Nat.add_zero, reduceCtorEq, ite_true, ite_false,
    show ¬ ((3 : Nat) = 0) by decide, show ¬ ((2 : Nat) = 0) by decide,
    show ¬ ((1 : Nat) = 0) by decide, show ¬ ((3 : Nat) = 1) by decide, show ¬ ((2 : Nat) = 1) by decide,
    show ¬ ((0 : Nat) = 1) by decide, show ¬ ((3 : Nat) = 2) by decide, show ¬ ((1 : Nat) = 2) by decide,
    show ¬ ((0 : Nat) = 2) by decide, show ¬ ((2 : Nat) = 3) by decide, show ¬ ((1 : Nat) = 3) by decide,
    show ¬ ((0 : Nat) = 3) by decide]

namespace REnv
variable (E : REnv)

/-- What the loop over four blocks at a time needs of its regions, besides
`Ok`. -/
structure Ok4 : Prop where
  inS4 : ∀ j, j + 4 ≤ E.r → InRegions (E.rd ++ E.wr) (E.aS j) 64
  inK4 : ∀ j, j + 4 ≤ E.r → InRegions (E.rd ++ E.wr) (E.aK j) 64
  inD4 : ∀ j, j + 4 ≤ E.r → InRegions E.wr (E.aD j) 64
  inW4 : ∀ j, j + 4 ≤ E.r → InRegions (E.rd ++ E.wr) (E.aW j) 64
  dW4 : ∀ j, j + 4 ≤ E.r → Region.Disjoint ⟨E.aW j, 64⟩ ⟨E.A, 16 * E.r⟩

end REnv

theorem addrL (p : Addr) (i l : Nat) :
    p + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 (16 * l) = p + BitVec.ofNat 64 (16 * (i + l)) := by
  rw [Offset.add_add, Nat.mul_add]

theorem addrLK (p : Addr) (i l : Nat) :
    p + BitVec.ofNat 64 (768 + 16 * i) + BitVec.ofNat 64 (16 * l) = p + BitVec.ofNat 64 (768 + 16 * (i + l)) := by
  rw [Offset.add_add, Nat.mul_add, Nat.add_assoc]

namespace REnv
variable (E : REnv)

/-- What the first `r mod 4` blocks, through a mask, need of their regions. -/
structure OkK : Prop where
  inSK : InRegions (E.rd ++ E.wr) (E.aS 0) (16 * (E.r % 4))
  inKK : InRegions (E.rd ++ E.wr) (E.aK 0) (16 * (E.r % 4))
  inDK : InRegions E.wr (E.aD 0) (16 * (E.r % 4))
  inWK : InRegions (E.rd ++ E.wr) (E.aW 0) (16 * (E.r % 4))

end REnv

theorem addrK0 (p : Addr) : p + BitVec.ofInt 64 ((0 : Nat) : Int) = p + BitVec.ofNat 64 (16 * 0) := by
  rw [BitVec.ofInt_natCast]

theorem addrK768 (p : Addr) : p + BitVec.ofInt 64 ((768 : Nat) : Int) = p + BitVec.ofNat 64 (768 + 16 * 0) := by
  rw [BitVec.ofInt_natCast]

theorem addrK0' (p : Addr) : p + BitVec.ofInt 64 ((0 : Nat) : Int) = p := by
  rw [BitVec.ofInt_natCast]; exact BitVec.add_zero _

theorem frame_nil {A : Addr} {m m' : Mem} (h : Frame [⟨A, 16 * 0⟩] m m') : m' = m := by
  funext x
  exact h x fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    simp [Region.Contains]

/-- `test r9, 3`: whether the blocks after the last group are a multiple of four. -/
theorem test9_ok (s : State) {r : Nat} (hr : r < 16) (h9 : s.gpr .r9 = BitVec.ofNat 64 (16 + r)) :
    WP isa (.block [.alu .test .r9 (.imm 3)]) s fun s' =>
      s'.zf = some (decide (r % 4 = 0)) ∧ s'.gpr = s.gpr ∧ (∀ x l, s'.zlane x l = s.zlane x l) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    h9, test3 r hr, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun _ _ => rfl, trivial, trivial, trivial⟩

/-- `cmp r9, 16`: whether blocks are left after the last group. -/
theorem cmp16_ok (s : State) :
    WP isa (.block [.alu .cmp .r9 (.imm 16)]) s fun s' =>
      s'.zf = some (s.gpr .r9 - 16 == 0) ∧ s'.gpr = s.gpr ∧
        (∀ r l, s'.zlane r l = s.zlane r l) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    e16, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun _ _ => rfl, trivial, trivial, trivial⟩

theorem sub16 : ∀ m < 16, (BitVec.ofNat 64 (16 + m) - 16 == 0) = decide (m = 0) := by decide

/-- `StitchAvx.zero` (`VEX.128`) clears every lane of `xmm8` … `xmm10`. -/
theorem zeroZ_ok (s : State) :
    WP isa (.block Impl.Gcm.X86_64.StitchAvx.zero) s fun s' =>
      (∀ l < 4, s'.zlane .xmm8 l = 0 ∧ s'.zlane .xmm9 l = 0 ∧ s'.zlane .xmm10 l = 0) ∧
      (∀ x, x ≠ .xmm8 → x ≠ .xmm9 → x ≠ .xmm10 → ∀ l < 4, s'.zlane x l = s.zlane x l) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86_64.StitchAvx.zero, runBlock_cons, runStep_some, runBlock_nil, exec, isa,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl => ?_, fun x h8 h9 h10 l hl => ?_, rfl, rfl, rfl, rfl⟩
  · have z : ((if l = 0 then 0#128 else 0) : BitVec 128) = 0 := ite_self _
    simp only [VOp.exec, State.zlane_setV128 _ _ _ _ _ hl, VBinOp.sse, Pclmul.eval_pxor, BitVec.xor_self,
      reduceCtorEq, ite_true, ite_false, z]
    exact ⟨trivial, trivial, trivial⟩
  · simp only [VOp.exec, State.zlane_setV128 _ _ _ _ _ hl, h8, h9, h10, ite_false]

end VG.Proof.Gcm.X86_64.StitchZH
