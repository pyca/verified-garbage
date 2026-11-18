module

import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.Mem
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowSelectVector
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import Mathlib.Tactic.ToAdditive
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorWord
meta import VerifiedGarbage.Proof.MlKem.AArch64.Wp
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd64
meta import VerifiedGarbage.Proof.Framework.Contract
meta import Mathlib.Tactic.Push
meta import Mathlib.Tactic.Attr.Core
meta import Mathlib.Tactic.ToAdditive
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorWord
meta import VerifiedGarbage.Impl.Rsa.AArch64.WindowSelectVector
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Lit

/-! ### `Bignum.AArch64.CrtWindowVectorStart`, which this module and modules that import it used -/

section

/-! ### `Bignum.AArch64.CrtWindowVectorScan`, which this module and modules that import it used -/

section

/-! ### `Bignum.AArch64.CrtWindowVectorInner`, which this module and modules that import it used -/

section

/-! ### `Bignum.AArch64.CrtWindowVectorLoad`, which this module and modules that import it used -/

section

/-! Four independent load/BIT pairs, sharing one row-comparison mask. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Rsa.AArch64.WindowSelectVector (accs)

def acc (i : Nat) : VReg := accs[i]!
def loadBits (n : Nat) : List Instr := (List.range n).flatMap fun i =>
  [.ldrq .v21 .x16 (16 * i), .vop (.bsel .bit (acc i) .v21 .v20)]
def written : List VReg := [.v21, .v16, .v17, .v18, .v19]

theorem acc_facts : ∀ i < 4, acc i ≠ .v20 ∧ acc i ≠ .v21 ∧ acc i ∈ written := by decide

theorem acc_ne : ∀ i < 4, ∀ j < 4, i ≠ j → acc i ≠ acc j := by decide

theorem loadBits_ok (n : Nat) {s : State} {choose : Prop} [Decidable choose]
    (hn : n ≤ 4) (hm : s.v .v20 = if choose then BitVec.allOnes 128 else 0)
    (hld : ∀ i < n, InRegions (s.rd ++ s.wr) (s.gpr .x16 + BitVec.ofNat 64 (16 * i)) 16) :
    WP isa (.block (loadBits n)) s fun t =>
      (∀ i < 4, t.v (acc i) = if i < n ∧ choose then
        s.mem.read (s.gpr .x16 + BitVec.ofNat 64 (16 * i)) 16 else s.v (acc i)) ∧
      VKeep written s t := by
  induction n with
  | zero =>
    apply WP.block_nil
    exact ⟨fun _ _ => by simp, ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩⟩
  | succ n ih =>
    rw [show loadBits (n + 1) = loadBits n ++
      [.ldrq .v21 .x16 (16 * n), .vop (.bsel .bit (acc n) .v21 .v20)] by
        simp [loadBits, List.range_succ], WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hn]) (fun i hi => hld i (by omega_using [hi]))) fun t ⟨hv, kt⟩ => ?_
    refine WP.mono (loadBit_value (choose := choose) (acc_facts n (by omega_using [hn])).2.1 (by omega_using [hn])
      (by rw [kt.v .v20 (by decide)]; exact hm)
      (by rw [kt.rd, kt.wr, kt.gpr]; exact hld n (by omega_using []))) fun u ⟨hu, ku⟩ => ?_
    refine ⟨?_, (kt.trans ku).mono ?_⟩
    · intro i hi
      by_cases he : i = n
      · subst i
        rw [hu, kt.mem, kt.gpr, hv n (by omega_using [hn])]
        simp only [Nat.lt_irrefl, false_and, ite_false, Nat.lt_succ_self, true_and]
      · rw [ku.v (acc i) (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨(acc_facts i hi).2.1, acc_ne i hi n (by omega_using [hn]) he⟩), hv i hi]
        have heq : i < n + 1 ↔ i < n := by omega_using [he]
        simp only [heq]
    · intro r hr
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with hr | rfl | rfl
      · exact hr
      · decide
      · exact (acc_facts n (by omega_using [hn])).2.2

end VG.Proof.Bignum.AArch64.WindowVector

end

end

/-! ### `Bignum.AArch64.CrtWindowVectorRow`, which this module and modules that import it used -/

section

/-! A complete table-row selection, with fixed-address loads and SIMD masks. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Rsa.AArch64.WindowSelectVector (inner)

theorem compare_ok {s : State} {j v : Nat} (hj : j < 2 ^ 64) (hv : v < 2 ^ 64)
    (h23 : s.v .v23 = dup2 (BitVec.ofNat 64 j))
    (h22 : s.v .v22 = dup2 (BitVec.ofNat 64 v)) :
    WP isa (.block [.vop (.cmeq .d2 .v20 .v23 .v22)]) s fun t =>
      t.v .v20 = (if j = v then BitVec.allOnes 128 else 0) ∧ VKeep [.v20] s t := by
  have he : (BitVec.ofNat 64 j = BitVec.ofNat 64 v) ↔ j = v := by
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hv] using this
    · intro h; rw [h]
  apply WP.of_runBlock
  simp only [runBlock_cons, exec, VOp.eval, h23, h22, cmeq_dup2, he,
    Option.map_some, runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  exact ⟨RegUpd.v_setV_self _ _ _, VKeep.setV _ _ _⟩

theorem selectRow_ok {s : State} {j v : Nat} (hj : j < 32) (hv : v < 32)
    (h23 : s.v .v23 = dup2 (BitVec.ofNat 64 j))
    (h22 : s.v .v22 = dup2 (BitVec.ofNat 64 v))
    (hld : ∀ i < 4, InRegions (s.rd ++ s.wr) (s.gpr .x16 + BitVec.ofNat 64 (16 * i)) 16) :
    WP isa (.block (([.vop (.cmeq .d2 .v20 .v23 .v22)] : List Instr) ++ loadBits 4)) s fun t =>
      (∀ i < 4, t.v (acc i) = if j = v then
        s.mem.read (s.gpr .x16 + BitVec.ofNat 64 (16 * i)) 16 else s.v (acc i)) ∧
      VKeep (.v20 :: written) s t := by
  rw [WP.block_append_iff]
  refine WP.mono (compare_ok (by omega_using [hj]) (by omega_using [hv]) h23 h22) fun a ⟨ha, ka⟩ => ?_
  refine WP.mono (loadBits_ok (choose := j = v) 4 (by decide) ha
    (fun i hi => by rw [ka.rd, ka.wr, ka.gpr]; exact hld i hi)) fun t ⟨ht, kt⟩ => ?_
  refine ⟨?_, ka.trans kt⟩
  intro i hi
  rw [ht i hi, ka.mem, ka.gpr, ka.v (acc i) (by
    simpa only [List.mem_singleton] using (acc_facts i hi).1)]
  simp only [hi, true_and]

end VG.Proof.Bignum.AArch64.WindowVector

end

end

/-! Advance the full-scan row pointer and public SIMD row index. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowSelectVector (inner)

def advance : List Instr :=
  [.add .x .x16 .x16 .x6, .vop (.add .d2 .v23 .v23 .v24)]

theorem add_dup2 (x y : BitVec 64) :
    VArr.d2.map2 (fun _ a b => a + b) (dup2 x) (dup2 y) = dup2 (x + y) := by
  simp only [VArr.map2, dup2, vdword_ofVDwords_0, vdword_ofVDwords_1]

theorem advance_ok {s : State} {j : Nat}
    (h23 : s.v .v23 = dup2 (BitVec.ofNat 64 j)) (h24 : s.v .v24 = dup2 1) :
    WP isa (.block advance) s fun t =>
      t = (s.write .x .x16 (s.gpr .x16 + s.gpr .x6)).setV .v23 (dup2 (BitVec.ofNat 64 (j + 1))) := by
  apply WP.of_runBlock
  simp only [advance, runBlock_cons, State.read, BitVec.setWidth_eq,
    runStep_some, exec, VOp.eval, RegUpd.v_write, h23, h24, add_dup2,
    Option.map_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  apply congrArg (fun x => (s.write .x .x16 (s.gpr .x16 + s.gpr .x6)).setV .v23 (dup2 x))
  rw [BitVec.ofNat_add]
  exact congrArg (fun x : BitVec 64 => BitVec.ofNat 64 j + x) (by decide)

theorem inner_eq : inner =
    ([.vop (.cmeq .d2 .v20 .v23 .v22)] : List Instr) ++ loadBits 4 ++ advance := rfl

theorem inner_ok {s : State} {j v : Nat} (hj : j < 32) (hv : v < 32)
    (h23 : s.v .v23 = dup2 (BitVec.ofNat 64 j))
    (h22 : s.v .v22 = dup2 (BitVec.ofNat 64 v)) (h24 : s.v .v24 = dup2 1)
    (hld : ∀ i < 4, InRegions (s.rd ++ s.wr) (s.gpr .x16 + BitVec.ofNat 64 (16 * i)) 16) :
    WP isa (.block inner) s fun t =>
      ((∀ i < 4, t.v (acc i) = if j = v then
        s.mem.read (s.gpr .x16 + BitVec.ofNat 64 (16 * i)) 16 else s.v (acc i)) ∧
      t.gpr .x16 = s.gpr .x16 + s.gpr .x6 ∧ t.mem = s.mem ∧
      t.v .v23 = dup2 (BitVec.ofNat 64 (j + 1)) ∧ t.v .v22 = s.v .v22 ∧ t.v .v24 = s.v .v24) ∧
      Keep [.x16] s t := by
  refine WP.keep [.x16] ?_ (by decide) (by decide) (by decide +kernel)
  rw [inner_eq, WP.block_append_iff]
  refine WP.mono (selectRow_ok hj hv h23 h22 hld) fun a ⟨ha, ka⟩ => ?_
  refine WP.mono (advance_ok (by rw [ka.v .v23 (by decide)]; exact h23)
    (by rw [ka.v .v24 (by decide)]; exact h24)) fun t ht => ?_
  subst t
  refine ⟨?_, ?_, ka.mem, RegUpd.v_setV_self _ _ _, ?_, ?_⟩
  · intro i hi
    have hn : acc i ≠ .v23 := by
      have h : ∀ i < 4, acc i ≠ .v23 := by decide
      exact h i hi
    rw [RegUpd.v_setV_of_ne _ _ hn, RegUpd.v_write, ha i hi]
  · simp only [RegUpd.gpr_setV, RegUpd.gpr_write_self, BitVec.setWidth_eq, ka.gpr]
  · rw [RegUpd.v_setV_of_ne _ _ (by decide), RegUpd.v_write, ka.v .v22 (by decide)]
  · rw [RegUpd.v_setV_of_ne _ _ (by decide), RegUpd.v_write, ka.v .v24 (by decide)]

end VG.Proof.Bignum.AArch64.WindowVector

end

end

/-! The scan of a table's entries (16 or 32) consumes every row and leaves the selected 64-byte block. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowSelectVector (inner)

structure ScanInv (s : State) (base : Addr) (stride v j : Nat) (t : State) : Prop where
  mem : t.mem = s.mem
  keep : Keep [.x14, .x16] s t
  ptr : t.gpr .x16 = base + BitVec.ofNat 64 (stride * j)
  index : t.v .v23 = dup2 (BitVec.ofNat 64 j)
  digit : t.v .v22 = dup2 (BitVec.ofNat 64 v)
  one : t.v .v24 = dup2 1
  value : ∀ i < 4, t.v (acc i) = if v < j then
    s.mem.read (base + BitVec.ofNat 64 (stride * v + 16 * i)) 16 else 0

theorem decVector_ok (s : State) :
    WP isa (.block [.subImm .x .x14 .x14 1]) s fun t =>
      (t.gpr .x14 = s.gpr .x14 - BitVec.ofNat 64 1 ∧ t.mem = s.mem ∧ t.v = s.v) ∧
      Keep [.x14] s t := by
  refine WP.keep [.x14] ?_ rfl rfl rfl
  brun
  exact RegUpd.v_write _ _ _ _

theorem scanStep_ok {s t : State} {base : Addr} {stride v j n : Nat} (hn : n ≤ 32)
    (hj : j < n) (hv : v < 32) (hs : s.gpr .x6 = BitVec.ofNat 64 stride)
    (hI : ScanInv s base stride v j t)
    (hld : ∀ j < n, ∀ i < 4,
      InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 (stride * j + 16 * i)) 16) :
    WP isa (.block (inner ++ ([.subImm .x .x14 .x14 1] : List Instr))) t fun u =>
      ScanInv s base stride v (j + 1) u ∧ u.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  rw [WP.block_append_iff]
  refine WP.mono (inner_ok (Nat.lt_of_lt_of_le hj hn) hv hI.index hI.digit hI.one (fun i hi => by
    rw [hI.keep.rd, hI.keep.wr, hI.ptr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hld j hj i hi)) fun a ⟨⟨ha, hp, hm, h23, h22, h24⟩, ka⟩ => ?_
  refine WP.mono (decVector_ok a) fun u ⟨⟨hu, hum, huv⟩, ku⟩ => ?_
  refine ⟨⟨hum.trans (hm.trans hI.mem), ((hI.keep.trans ka).trans ku).mono (by decide),
    ?_, ?_, ?_, ?_, ?_⟩, hu.trans (congrArg (· - BitVec.ofNat 64 1) (ka.gpr .x14 (by decide)))⟩
  · rw [ku.gpr .x16 (by decide), hp, hI.ptr, hI.keep.gpr .x6 (by decide), hs,
      BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add, Nat.mul_one]
  · rw [huv, h23]
  · rw [huv, h22, hI.digit]
  · rw [huv, h24, hI.one]
  · intro i hi
    rw [huv, ha i hi, hI.mem, hI.ptr, BitVec.add_assoc, ← BitVec.ofNat_add, hI.value i hi]
    by_cases he : j = v
    · subst j
      simp only [ite_true, Nat.lt_irrefl, ite_false, Nat.lt_succ_self]
    · have heq : v < j + 1 ↔ v < j := by omega_using [he]
      simp only [he, ite_false, heq]

/-- Exact scan of `n` rows. Its final value does not depend on the prior contents
of the accumulator registers, which the caller clears before entering. -/
theorem scan_ok {s : State} {base : Addr} {stride v n : Nat} (hn : n ≤ 32) (hn0 : 0 < n)
    (hv : v < 32) (hs : s.gpr .x6 = BitVec.ofNat 64 stride)
    (hc : s.gpr .x14 = BitVec.ofNat 64 n) (h0 : ScanInv s base stride v 0 s)
    (hld : ∀ j < n, ∀ i < 4,
      InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 (stride * j + 16 * i)) 16) :
    WP isa (countLoop .x14 inner) s (ScanInv s base stride v n) := by
  unfold countLoop
  exact wp_countdown (by omega_using [hn]) hn0 (fun j => ScanInv s base stride v j)
    (fun j hj t hI _ => scanStep_ok hn hj hv hs hI hld) h0 hc

end VG.Proof.Bignum.AArch64.WindowVector

end

end

/-! ### `Bignum.AArch64.CrtWindowVectorClear`, which this module and modules that import it used -/

section

/-! Clear the four selection accumulators without disturbing scalar state. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Rsa.AArch64.WindowSelectVector (accs)

theorem zeroVector_ok (s : State) (r : VReg) :
    WP isa (.block [.vop (.movi0 r)]) s fun t =>
      t.v r = 0 ∧ VKeep [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec, VOp.eval, Option.map_some, runStep_some,
    runBlock_nil, Option.some.injEq, exists_eq_left']
  exact ⟨RegUpd.v_setV_self _ _ _, VKeep.setV _ _ _⟩

theorem clearVectors_ok (rs : List VReg) (s : State) :
    WP isa (.block (rs.map fun r => .vop (.movi0 r))) s fun t =>
      (∀ r ∈ rs, t.v r = 0) ∧ VKeep rs s t := by
  induction rs generalizing s with
  | nil => exact WP.block_nil ⟨by simp, ⟨rfl,rfl,rfl,rfl,rfl,fun _ _ => rfl⟩⟩
  | cons r rs ih =>
    rw [List.map_cons, show .vop (.movi0 r) :: rs.map (fun r => Instr.vop (.movi0 r)) =
      [.vop (.movi0 r)] ++ rs.map (fun r => Instr.vop (.movi0 r)) from rfl,
      WP.block_append_iff]
    refine WP.mono (zeroVector_ok s r) fun u ⟨hu, ku⟩ => ?_
    refine WP.mono (ih u) fun t ⟨ht, kt⟩ => ⟨?_, ku.trans kt⟩
    intro q hq
    by_cases h : q ∈ rs
    · exact ht q h
    · have he : q = r := (List.mem_cons.mp hq).resolve_right h
      subst q
      exact (kt.v r h).trans hu

theorem clearAccs_ok (s : State) :
    WP isa (.block (accs.map fun r => .vop (.movi0 r))) s fun t =>
      (∀ i < 4, t.v (acc i) = 0) ∧ VKeep accs s t := by
  refine WP.mono (clearVectors_ok accs s) fun t ⟨ht, kt⟩ => ⟨?_, kt⟩
  intro i hi
  exact ht (acc i) ((by decide : ∀ i < 4, acc i ∈ accs) i hi)

end VG.Proof.Bignum.AArch64.WindowVector

end

end

/-! ### `Bignum.AArch64.CrtWindowVectorHead`, which this module and modules that import it used -/

section

/-! Start each SIMD block at the same public offset in every table entry. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowSelectVector (accs)

def blockHead (n : Nat) : List Instr :=
  [ldh .x16 (sArr Crt.aT), .sub .x .x16 .x17 .x16,
   ldh .x3 Crt.sTab, .add .x .x16 .x16 .x3,
   .vop (.movi0 .v23), movi .x14 n]

theorem exec_zeroVector (s : State) (r : VReg) :
    exec (.vop (.movi0 r)) s = some (s.setV r 0) := rfl

theorem blockHead_ok {s : State} {P : Addr} {w b n : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hN : n = 16 ∨ n = 32) (hc : CExpCtx s P w mi X Xc n)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot w 8))
    (hp : s.gpr .x17 = off P (slot w Crt.aT + 64 * b)) :
    WP isa (.block (blockHead n)) s fun t =>
      (t.gpr .x16 = off P (slot w 8 + 64 * b) ∧ t.gpr .x14 = BitVec.ofNat 64 n ∧
       t.v = (s.setV .v23 0).v ∧ t.mem = s.mem) ∧ Keep [.x16,.x3,.x14] s t := by
  have hp' : off P (slot w Crt.aT + 64 * b) - off P (slot w Crt.aT) =
      BitVec.ofNat 64 (64 * b) := by
    rw [off, BitVec.ofNat_add, ← BitVec.add_assoc]
    exact Offset.add_sub_cancel_left _ _
  rcases hN with rfl | rfl <;>
  · refine WP.keep _ ?_ rfl rfl rfl
    brun [blockHead, hc.good.x0, hdr_enc (sArr_lt (show Crt.aT < 8 by decide)),
      hdr_enc (show Crt.sTab < 32 by decide), hc.ld (i := sArr Crt.aT) (by decide),
      hc.ld (i := Crt.sTab) (by decide), hc.good.hdr.harr Crt.aT (by decide), ht, hp, hp',
      exec_zeroVector, RegUpd.v_write, RegUpd.gpr_setV, RegUpd.mem_setV]
    refine ⟨BitVec.add_comm _ _ |>.trans (off_add P (slot w 8) (64 * b)), ?_⟩
    simp only [State.setV, RegUpd.v_write]

end VG.Proof.Bignum.AArch64.WindowVector

end

end

/-! Initialize the complete invariant for a vector scan of 16 or 32 rows. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowSelectVector (accs)

theorem startScan_ok {s : State} {P : Addr} {w b v n : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hN : n = 16 ∨ n = 32) (hc : CExpCtx s P w mi X Xc n)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot w 8))
    (hp : s.gpr .x17 = off P (slot w Crt.aT + 64 * b))
    (h22 : s.v .v22 = dup2 (BitVec.ofNat 64 v)) (h24 : s.v .v24 = dup2 1) :
    WP isa (.block (blockHead n ++ accs.map fun r => .vop (.movi0 r))) s fun t =>
      t.gpr .x14 = BitVec.ofNat 64 n ∧
      ScanInv t (off P (slot w 8 + 64 * b)) (8 * (w + 2)) v 0 t ∧
      t.mem = s.mem ∧ Keep [.x16,.x3,.x14] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (blockHead_ok hN hc ht hp) fun u ⟨⟨h16,h14,hv,hm⟩, ku⟩ => ?_
  refine WP.mono (clearAccs_ok u) fun t ⟨hz, kt⟩ => ?_
  have keep : Keep [] u t := ⟨fun r _ => congrFun kt.gpr r, kt.rd, kt.wr, kt.sp,
    fun r hr => congrArg (fun x : BitVec 128 => x.extractLsb' 0 64)
      (kt.v r ((by decide : ∀ r ∈ preservedV, r ∉ accs) r hr))⟩
  refine ⟨by rw [kt.gpr, h14], ⟨rfl, Keep.refl _ _, ?_, ?_, ?_, ?_, ?_⟩,
    kt.mem.trans hm, (ku.trans keep).mono (by decide)⟩
  · simpa only [Nat.mul_zero, BitVec.add_zero, kt.gpr] using h16
  · rw [kt.v .v23 (by decide), hv, RegUpd.v_setV_self]
    rfl
  · rw [kt.v .v22 (by decide), hv, RegUpd.v_setV_of_ne _ _ (by decide)]
    exact h22
  · rw [kt.v .v24 (by decide), hv, RegUpd.v_setV_of_ne _ _ (by decide)]
    exact h24
  · intro i hi
    simpa only [Nat.not_lt_zero, ite_false] using hz i hi

end VG.Proof.Bignum.AArch64.WindowVector

end

end

/-! ### `Bignum.AArch64.CrtWindowVectorCopy`, which this module and modules that import it used -/

section

/-! Join adjacent selected blocks without losing previously copied bytes. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.Proof.Bignum

theorem copy_append {m₀ m₁ m₂ : Mem} {B : Addr} {dst src n k : Nat}
    (hn : dst + n + k ≤ 2 ^ 64)
    (h₁ : Outside B dst n m₀ m₁) (h₂ : Outside B (dst + n) k m₁ m₂)
    (b₁ : ∀ j < n, m₁ (off B (dst + j)) = m₀ (off B (src + j)))
    (b₂ : ∀ j < k, m₂ (off B (dst + n + j)) = m₀ (off B (src + n + j))) :
    Outside B dst (n + k) m₀ m₂ ∧
      ∀ j < n + k, m₂ (off B (dst + j)) = m₀ (off B (src + j)) := by
  refine ⟨(h₁.mono (by omega_using []) (by omega_using [])).trans (h₂.mono (by omega_using []) (by omega_using [])), ?_⟩
  intro j hj
  by_cases h : j < n
  · rw [h₂ _ (by
      simp only [ofs, off, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show dst + j < 2 ^ 64 by omega_using [hn, hj])]
      omega_using [h])]
    exact b₁ j h
  · have he₁ : dst + j = dst + n + (j - n) := by omega_using [h]
    have he₂ : src + j = src + n + (j - n) := by omega_using [h]
    rw [he₁,he₂]
    exact b₂ (j - n) (by omega_using [hj, h])

theorem wv_copy {m m' : Mem} {P : Addr} {dst src w : Nat}
    (h : ∀ j < 8 * w, m' (off P (dst + j)) = m (off P (src + j))) :
    wv m' P dst w = wv m P src w := by
  apply wv_congr2
  intro i hi
  change m'.read (off P (dst + 8 * i)) 8 = m.read (off P (src + 8 * i)) 8
  apply Mem.read_eq_of_bytes
  intro j hj
  rw [Mem.extractLsb'_read m _ hj]
  simpa only [off, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc] using h (8 * i + j) (by omega_using [hi, hj])

end VG.Proof.Bignum.AArch64.WindowVector

end

end

/-! ### `Bignum.AArch64.CrtWindowVectorBlock`, which this module and modules that import it used -/

section

/-! ### `Bignum.AArch64.CrtWindowVectorStore`, which this module and modules that import it used -/

section

/-! Store a selected 64-byte block while preserving its source snapshot. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

theorem write16_outside (m : Mem) (B : Addr) {d : Nat} (v : BitVec 128)
    (h : d + 16 ≤ 2 ^ 64) : Outside B d 16 m (m.write (off B d) 16 v) := by
  intro x hx
  apply Mem.write_apply
  simp only [ofs] at hx
  have he : (x - off B d).toNat = (2 ^ 64 - d + (x - B).toNat) % 2 ^ 64 :=
    Offset.toNat_sub_add x B (by omega_using [h])
  rw [he]
  have := (x - B).isLt
  rcases hx with hx | hx
  · rw [Nat.mod_eq_of_lt (by omega_using [hx])]; omega_using [h]
  · rw [show 2 ^ 64 - d + (x - B).toNat = (x - B).toNat - d + 2 ^ 64 by omega_using [hx],
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_using [])]
    omega_using [hx]

theorem write16_byte (m source : Mem) (dst src : Addr) {j : Nat} (hj : j < 16) :
    (m.write dst 16 (source.read src 16)) (dst + BitVec.ofNat 64 j) =
      source (src + BitVec.ofNat 64 j) := by
  simp only [Mem.write, Mem.sub_ofNat_toNat dst (show j < 2 ^ 64 by omega_using [hj]), hj, ite_true,
    Mem.extractLsb'_read source src hj]

theorem storePair_ok {s : State} {r : VReg} {i : Nat} (hi : i < 4)
    (hw : InRegions s.wr (s.gpr .x17 + BitVec.ofNat 64 (16 * i)) 16) :
    WP isa (.block [.strq r .x17 (16 * i)]) s fun t =>
      (t.mem = s.mem.write (s.gpr .x17 + BitVec.ofNat 64 (16 * i)) 16 (s.v r) ∧
        t.v = s.v) ∧ Keep [] s t := by
  refine WP.keep [] ?_ rfl rfl rfl
  apply WP.of_runBlock
  simp only [runBlock_cons, exec, addr, show 16 * i % 16 = 0 by omega_using [],
    show 16 * i < 4096 * 16 by omega_using [hi], and_self, ite_true, Option.bind_some,
    State.store, hw, runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']

def stores (n : Nat) : List Instr := (List.range n).map fun i => .strq (acc i) .x17 (16 * i)

structure StoreInv (s : State) (B : Addr) (dst src n : Nat) (t : State) : Prop where
  keep : Keep [] s t
  vectors : t.v = s.v
  frame : Outside B dst (16 * n) s.mem t.mem
  bytes : ∀ j < 16 * n, t.mem (off B (dst + j)) = s.mem (off B (src + j))

theorem stores_ok (n : Nat) {s : State} {B : Addr} {dst src : Nat}
    (hn : n ≤ 4) (hptr : s.gpr .x17 = off B dst) (hd : dst + 16 * n ≤ 2 ^ 64)
    (hv : ∀ i < n, s.v (acc i) = s.mem.read (off B (src + 16 * i)) 16)
    (hw : ∀ i < n, InRegions s.wr (off B (dst + 16 * i)) 16) :
    WP isa (.block (stores n)) s (StoreInv s B dst src n) := by
  induction n with
  | zero =>
    exact WP.block_nil ⟨Keep.refl _ _, rfl, Outside.refl _ _ _ _, fun _ h => by omega⟩
  | succ n ih =>
    rw [show stores (n + 1) = stores n ++ [.strq (acc n) .x17 (16 * n)] by
      simp [stores, List.range_succ], WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hn]) (by omega_using [hd]) (fun i hi => hv i (by omega_using [hi]))
      (fun i hi => hw i (by omega_using [hi]))) fun t ht => ?_
    have ptr : t.gpr .x17 + BitVec.ofNat 64 (16 * n) = off B (dst + 16 * n) := by
      rw [ht.keep.gpr .x17 (by simp), hptr, off, BitVec.add_assoc, ← BitVec.ofNat_add]
    refine WP.mono (storePair_ok (r := acc n) (by omega_using [hn])
      (by rw [ht.keep.wr, ptr]; exact hw n (by omega_using []))) fun u ⟨⟨hm, huv⟩, ku⟩ => ?_
    rw [ptr, ht.vectors, hv n (by omega_using [])] at hm
    have ho := write16_outside t.mem B (d := dst + 16 * n)
      (s.mem.read (off B (src + 16 * n)) 16) (by omega_using [hd])
    rw [← hm] at ho
    refine ⟨(ht.keep.trans ku).mono (by decide), huv.trans ht.vectors,
      (ht.frame.mono (by omega_using []) (by omega_using [])).trans (ho.mono (by omega_using []) (by omega_using [])), ?_⟩
    intro j hj
    by_cases hjn : j < 16 * n
    · rw [ho _ (by
      simp only [ofs, off, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show dst + j < 2 ^ 64 by omega_using [hd, hj])]
      omega_using [hjn])]
      exact ht.bytes j hjn
    · have hp : off B (dst + j) = off B (dst + 16 * n) + BitVec.ofNat 64 (j - 16 * n) := by
        rw [off, off, BitVec.add_assoc, ← BitVec.ofNat_add]
        exact congrArg (fun z => B + BitVec.ofNat 64 z) (by omega_using [hjn])
      rw [hm, hp, write16_byte t.mem s.mem _ _ (by omega_using [hj]), off,
        BitVec.add_assoc, ← BitVec.ofNat_add]
      exact congrArg (fun z => s.mem (B + BitVec.ofNat 64 z)) (by omega_using [hjn])

end VG.Proof.Bignum.AArch64.WindowVector

end

end

/-! A full table scan followed by the four stores of one selected block. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowSelectVector (inner)

theorem scan_store_ok {s : State} {B : Addr} {base stride dst v n : Nat} (hn : n ≤ 32)
    (hv : v < n) (hs : s.gpr .x6 = BitVec.ofNat 64 stride)
    (hc : s.gpr .x14 = BitVec.ofNat 64 n)
    (h0 : ScanInv s (off B base) stride v 0 s)
    (hp : s.gpr .x17 = off B dst) (hd : dst + 64 ≤ 2 ^ 64)
    (hld : ∀ j < n, ∀ i < 4,
      InRegions (s.rd ++ s.wr) (off B (base + stride * j + 16 * i)) 16)
    (hw : ∀ i < 4, InRegions s.wr (off B (dst + 16 * i)) 16) :
    WP isa (.seq (countLoop .x14 inner) (.block (stores 4))) s fun t =>
      Keep [.x14, .x16] s t ∧ Outside B dst 64 s.mem t.mem ∧
      t.v .v22 = dup2 (BitVec.ofNat 64 v) ∧ t.v .v24 = dup2 1 ∧
      ∀ j < 64, t.mem (off B (dst + j)) =
        s.mem (off B (base + stride * v + j)) := by
  apply WP.seq
  refine WP.mono (scan_ok hn (Nat.zero_lt_of_lt hv) (Nat.lt_of_lt_of_le hv hn) hs hc h0 (fun j hj i hi => by
    simpa only [off, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc] using hld j hj i hi))
    fun u hu => ?_
  refine WP.mono (stores_ok 4 (src := base + stride * v) (by decide)
    (by rw [hu.keep.gpr .x17 (by decide)]; exact hp) hd
    (fun i hi => by
      simp only [hu.value i hi, hv, ite_true, hu.mem]
      simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc])
    (fun i hi => by rw [hu.keep.wr]; exact hw i hi)) fun t ht => ?_
  refine ⟨(hu.keep.trans ht.keep).mono (by decide), ?_, ?_, ?_, ?_⟩
  · simpa only [hu.mem] using ht.frame
  · rw [ht.vectors]; exact hu.digit
  · rw [ht.vectors]; exact hu.one
  · simpa only [hu.mem] using ht.bytes

end VG.Proof.Bignum.AArch64.WindowVector

end

end

/-! ### `Bignum.AArch64.CrtWindowVectorTile`, which only this module used -/

section

/-! One complete SIMD selection tile, including initialization, all rows and stores. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowSelectVector (accs inner)

def tile (n : Nat) : Prog isa := .seq (.block (blockHead n ++ accs.map fun r => .vop (.movi0 r)))
  (.seq (countLoop .x14 inner) (.block (stores 4)))

theorem tableTile_ld {s : State} {P : Addr} {w b j i n : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx s P w mi X Xc n) (hb : 8 * b + 8 ≤ w) (hj : j < n) (hi : i < 4) :
    InRegions (s.rd ++ s.wr)
      (off P (slot w 8 + 64 * b + 8 * (w + 2) * j + 16 * i)) 16 := by
  have he : slot w 8 + 8 * (w + 2) * j = slot w (8 + j) := by
    simp only [slot, Nat.add_mul, Nat.mul_comm j, Nat.add_assoc]
  have hE := ent_le w hj
  obtain ⟨r, hr, hR⟩ := hc.scrT.region
    (d := slot w 8 + 64 * b + 8 * (w + 2) * j + 16 * i) (n := 16)
    (by omega_using [hb, hi, he, hE]) (by decide)
  exact ⟨r, List.mem_append_right _ hr, hR⟩

theorem tableTile_st {s : State} {P : Addr} {w b i n : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx s P w mi X Xc n) (hb : 8 * b + 8 ≤ w) (hi : i < 4) :
    InRegions s.wr (off P (slot w Crt.aT + 64 * b + 16 * i)) 16 := by
  have hT := slot_le (w := w) (show Crt.aT < 8 by decide)
  exact hc.good.scr.region (by omega_using [hb, hi, hT]) (by decide)

theorem tile_ok {s : State} {P : Addr} {w b v n : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hN : n = 16 ∨ n = 32) (hc : CExpCtx s P w mi X Xc n) (hv : v < n)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot w 8))
    (hp : s.gpr .x17 = off P (slot w Crt.aT + 64 * b))
    (hs : s.gpr .x6 = BitVec.ofNat 64 (8 * (w + 2)))
    (h22 : s.v .v22 = dup2 (BitVec.ofNat 64 v)) (h24 : s.v .v24 = dup2 1)
    (hd : slot w Crt.aT + 64 * b + 64 ≤ 2 ^ 64)
    (hld : ∀ j < n, ∀ i < 4, InRegions (s.rd ++ s.wr)
      (off P (slot w 8 + 64 * b + 8 * (w + 2) * j + 16 * i)) 16)
    (hw : ∀ i < 4, InRegions s.wr (off P (slot w Crt.aT + 64 * b + 16 * i)) 16) :
    WP isa (tile n) s fun t =>
      Keep [.x16,.x3,.x14] s t ∧ Outside P (slot w Crt.aT + 64 * b) 64 s.mem t.mem ∧
      t.v .v22 = dup2 (BitVec.ofNat 64 v) ∧ t.v .v24 = dup2 1 ∧
      ∀ j < 64, t.mem (off P (slot w Crt.aT + 64 * b + j)) =
        s.mem (off P (slot w 8 + 64 * b + 8 * (w + 2) * v + j)) := by
  unfold tile
  apply WP.seq
  refine WP.mono (startScan_ok hN hc ht hp h22 h24) fun u ⟨hu,h0,hm,ku⟩ => ?_
  refine WP.mono (scan_store_ok (by rcases hN with rfl | rfl <;> decide) hv
    (by rw [ku.gpr .x6 (by decide)]; exact hs) hu h0
    (by rw [ku.gpr .x17 (by decide)]; exact hp) hd
    (fun j hj i hi => by rw [ku.rd,ku.wr]; exact hld j hj i hi)
    (fun i hi => by rw [ku.wr]; exact hw i hi)) fun t ⟨kt,ho,h22',h24',hb⟩ => ?_
  exact ⟨(ku.trans kt).mono (by decide), hm ▸ ho, h22', h24', hm ▸ hb⟩

theorem tileAdvance_ok (s : State) :
    WP isa (.block [.addImm .x .x17 .x17 64, .subImm .x .x13 .x13 1]) s fun t =>
      (t.gpr .x17 = s.gpr .x17 + BitVec.ofNat 64 64 ∧
       t.gpr .x13 = s.gpr .x13 - BitVec.ofNat 64 1 ∧ t.mem = s.mem ∧ t.v = s.v) ∧
      Keep [.x17,.x13] s t := by
  refine WP.keep _ ?_ rfl rfl rfl
  brun [RegUpd.v_write]

end VG.Proof.Bignum.AArch64.WindowVector

end

end


/-! Preserve the selected prefix and table context across SIMD tiles. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.MlKem.AArch64 (Keep)

structure LoopInv (n : Nat) (s : State) (P : Addr) (w : Nat) (mi : BitVec 64) (X Xc v j : Nat)
    (t : State) : Prop where
  ctx : CExpCtx t P w mi X Xc n
  tab : word t.mem P (8 * Crt.sTab) = off P (slot w 8)
  stride : t.gpr .x6 = BitVec.ofNat 64 (8 * (w + 2))
  ptr : t.gpr .x17 = off P (slot w Crt.aT + 64 * j)
  digit : t.v .v22 = dup2 (BitVec.ofNat 64 v)
  one : t.v .v24 = dup2 1
  frame : Outside P (slot w Crt.aT) (64 * j) s.mem t.mem
  bytes : ∀ k < 64 * j, t.mem (off P (slot w Crt.aT + k)) =
    s.mem (off P (slot w 8 + 8 * (w + 2) * v + k))
  keep : Keep mmRegs s t

def tileStep (n : Nat) : Prog isa := .seq (tile n)
  (.block [.addImm .x .x17 .x17 64, .subImm .x .x13 .x13 1])

def rawStep (n : Nat) : Prog isa :=
  .seq (.block (blockHead n ++ VG.Impl.Rsa.AArch64.WindowSelectVector.accs.map fun r => .vop (.movi0 r)))
    (.seq (countLoop .x14 VG.Impl.Rsa.AArch64.WindowSelectVector.inner)
      (.block (stores 4 ++ [.addImm .x .x17 .x17 64, .subImm .x .x13 .x13 1])))

theorem rawStep_wp (n : Nat) (s : State) (Q : State → Prop) :
    WP isa (rawStep n) s Q ↔ WP isa (tileStep n) s Q := by
  unfold rawStep tileStep tile
  simp only [WP.seq_iff (M := isa), WP.block_append_iff (M := isa)]

theorem loopStep_ok {s t : State} {P : Addr} {w v j n : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hN : n = 16 ∨ n = 32) (hv : v < n) (hj : 8 * j + 8 ≤ w) (hI : LoopInv n s P w mi X Xc v j t) :
    WP isa (tileStep n) t fun u => LoopInv n s P w mi X Xc v (j + 1) u ∧
      u.gpr .x13 = t.gpr .x13 - BitVec.ofNat 64 1 := by
  have hn := hI.ctx.scrT.nowrap
  have hT := slot_le (w := w) (show Crt.aT < 8 by decide)
  have hE := ent_le w hv
  have he : slot w 8 + 8 * (w + 2) * v = slot w (8 + v) := by
    simp only [slot, Nat.add_mul, Nat.mul_comm v, Nat.add_assoc]
  unfold tileStep
  apply WP.seq
  refine WP.mono (tile_ok hN hI.ctx hv hI.tab hI.ptr hI.stride hI.digit hI.one (by omega_using [hj, hn, hT])
    (fun r hr i hi => tableTile_ld hI.ctx hj hr hi)
    (fun i hi => tableTile_st hI.ctx hj hi)) fun a ⟨ka,ho,h22,h24,hb⟩ => ?_
  have hcopy : ∀ k < 64, a.mem (off P (slot w Crt.aT + 64 * j + k)) =
      s.mem (off P (slot w 8 + 8 * (w + 2) * v + 64 * j + k)) := by
    intro k hk
    rw [hb k hk]
    have hs := hI.frame (off P (slot w 8 + 64 * j + 8 * (w + 2) * v + k)) (by
      simp only [ofs, off, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show slot w 8 + 64 * j + 8 * (w + 2) * v + k < 2 ^ 64 by omega_using [hj, hn, hE, he, hk])]
      omega_using [hT])
    rw [hs]
    congr 2
    omega_using []
  have copied := copy_append (by omega_using [hj, hn, hT]) hI.frame ho hI.bytes hcopy
  refine WP.mono (tileAdvance_ok a) fun u ⟨⟨hp,hc,hm,hvec⟩,ku⟩ => ?_
  have frame : Outside P (slot w Crt.aT) (64 * (j + 1)) s.mem u.mem := by
    rw [hm, Nat.mul_add, Nat.mul_one]
    exact copied.1
  have localFrame : Frm P (crtWinRanges w) t.mem u.mem := by
    rw [hm]
    exact (Frm.of_outside (ho.mono (o' := slot w Crt.aT) (n' := 8 * (w + 2))
      (by omega_using []) (by omega_using [hj])) (by simp [crtWinRanges]))
  have keep := (ka.trans ku).mono (rs' := mmRegs) (by decide)
  refine ⟨⟨hI.ctx.of_win localFrame keep.wr (keep.gpr .x0 (by decide)), ?_, ?_, ?_, ?_, ?_,
    frame, ?_, (hI.keep.trans keep).mono (by decide)⟩, ?_⟩
  · rw [hm, ho.word (by have := hdr_lt_slot w Crt.aT (show Crt.sTab < 32 by decide); omega_using [this])
      (by decide)]
    exact hI.tab
  · rw [ku.gpr .x6 (by decide), ka.gpr .x6 (by decide)]
    exact hI.stride
  · rw [hp, ka.gpr .x17 (by decide), hI.ptr, off_add, Nat.mul_add, Nat.mul_one, Nat.add_assoc]
  · rw [hvec]; exact h22
  · rw [hvec]; exact h24
  · simpa only [hm, Nat.mul_add, Nat.mul_one] using copied.2
  · rw [hc, ka.gpr .x13 (by decide)]

theorem blocks_ok {s : State} {P : Addr} {w v n : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hN : n = 16 ∨ n = 32) (hw : 8 ≤ w) (hw' : w < 2 ^ 30) (hv : v < n)
    (h0 : LoopInv n s P w mi X Xc v 0 s)
    (hc : s.gpr .x13 = BitVec.ofNat 64 (w / 8)) :
    WP isa (.loop (rawStep n) (.nonzero .x .x13)) s (LoopInv n s P w mi X Xc v (w / 8)) := by
  apply wp_countdown (by omega_using [hw']) (by omega_using [hw]) (fun j => LoopInv n s P w mi X Xc v j)
    (fun j hj t hI _ => (rawStep_wp _ _ _).mpr (loopStep_ok hN hv (by omega_using [hj]) hI)) h0 hc

end VG.Proof.Bignum.AArch64.WindowVector
