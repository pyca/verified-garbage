module

public import VerifiedGarbage.Proof.Sm3.StateMem
meta import VerifiedGarbage.Proof.Sm3.StateMem
public import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.PPC64LE.TaintMono
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public meta import VerifiedGarbage.Proof.Framework.PPC64LE.TaintMono
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Range
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
public import VerifiedGarbage.Proof.Sm3.Spec
public import VerifiedGarbage.Impl.Sm3.PPC64LE
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.TCB.PPC64LE.Isa
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Sm3.Spec
meta import VerifiedGarbage.Impl.Sm3.PPC64LE
meta import Mathlib.Data.List.Nodup
meta import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Spec.Sm3
public import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.Spec.Sm3
meta import VerifiedGarbage.TCB.Artifact

/-! ### `Sm3.PPC64LE.Contract`, which only this module used -/

section

/-!
# SM3: the PPC64LE contracts

The contracts the proofs are written against; the artifacts are emitted with the
shared contracts of `Spec/`, which imply these (`Contract.Implies`). The
contracts of the PPC64LE implementations of the compression function and the
streaming interface, in terms of `Spec/Sm3.lean`.

The return address is in the link register, which the target's calling
convention requires to be preserved (`VG.PPC64LE.abiPreserved`), not on the
stack, so unlike on x86-64 no region needs to be kept disjoint from it.
-/

@[expose] public section

namespace VG.Proof.Sm3

open Spec.Sm3

open PPC64LE in
/-- PPC64LE contract for
`vg_sm3_compress(state: *mut [u32; 8], blocks: *const [u8; 64], n: usize, scratch: *mut [u64; 14])`:
updates the hash value at `state` with the `n` 64-byte blocks at `blocks`.

The code may read `blocks` (`64 * n` bytes) and read and write `state`
(32 bytes) and `scratch` (112 bytes, whose contents on exit are unspecified).
These may not overlap each other. The pointers and `n` are public; the hash
value and the blocks are secret. -/
def compressPPC64LE : Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 32⟩
    let blocks : Region := ⟨s.gpr .r4, 64 * (s.gpr .r5).toNat⟩
    let scratch : Region := ⟨s.gpr .r6, 112⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch
  post s s' :=
    stateAt s'.mem (s.gpr .r3) =
      compressBlocks (stateAt s.mem (s.gpr .r3)) s.mem (s.gpr .r4) (s.gpr .r5).toNat
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

open PPC64LE in
/-- PPC64LE contract for `vg_sm3_init(state: *mut [u8; 96])`: makes the
streaming state at `state` represent the empty message.

The code may write `state` (96 bytes). The pointer is public. -/
def initPPC64LE : Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 96⟩
    s.rd = [] ∧ s.wr = [state]
  post s s' := Repr s'.mem (s.gpr .r3) []
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.sp = s₂.sp

open PPC64LE in
/-- PPC64LE contract for `update(state = r3, count = r4, data = r5, len =
r6, scratch = r7)`, `vg_sm3_update` with its working space (160 bytes)
passed in `scratch`: if the streaming state at `state` represents a message
`m` of `count` bytes (modulo 2⁶⁴), then afterwards it represents `m` followed
by the `len` bytes at `data`.

The code may read `data` (`len` bytes) and read and write `state` (96
bytes) and `scratch` (whose contents on exit are unspecified). These may not
overlap each other, nor the 48 bytes below the stack pointer (the frame
saving the link register), which do not wrap around. The pointers, `count` and `len` are
public; the state and the data are secret. -/
def updatePPC64LE : Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 96⟩
    let data : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let scratch : Region := ⟨s.gpr .r7, 160⟩
    let stack : Region := ⟨s.sp - 48, 48⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    48 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch
  post s s' := ∀ m, Repr s.mem (s.gpr .r3) m → s.gpr .r4 = BitVec.ofNat 64 m.length →
    Repr s'.mem (s.gpr .r3) (m ++ bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp

open PPC64LE in
/-- PPC64LE contract for `finalize(state = r3, count = r4, out = r5, scratch
= r6)`, `vg_sm3_finalize` with its working space (160 bytes) passed in
`scratch`: if the streaming state at `state` represents a message `m` of
`count` bytes (modulo 2⁶⁴), writes the SM3 hash value of `m` to `out`.

The code may read and write `state` (96 bytes, whose contents on exit are
unspecified), `out` (32 bytes) and `scratch` (whose contents on exit are
unspecified). These may not overlap each other, nor the 48 bytes below the
stack pointer (the frame saving the link register), which do not wrap around. The
pointers and `count` are public; the state is secret. -/
def finalizePPC64LE : Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 96⟩
    let out : Region := ⟨s.gpr .r5, 32⟩
    let scratch : Region := ⟨s.gpr .r6, 160⟩
    let stack : Region := ⟨s.sp - 48, 48⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    48 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' := ∀ m, Repr s.mem (s.gpr .r3) m → s.gpr .r4 = BitVec.ofNat 64 m.length →
    bytesAt s'.mem (s.gpr .r5) 32 = Spec.Sm3.hash m
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

end VG.Proof.Sm3

end

end

/-! ### `Sm3.PPC64LE.Rounds`, which only this module used -/

section

/-!
# SM3 compression function on PPC64LE: the message expansion and the iterations

The words are the low 32 bits of the registers (`Vars`), as in the SHA-256
proofs (`Proof/Sha256/PPC64LE/Rounds.lean`).
-/

@[expose] public section

namespace VG.Proof.Sm3.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm3.PPC64LE
open VG.Spec.Sm3 (HashValue Word Block W p0 p1 ff gg)

/-- The registers `v` are in the low words of the registers of iteration `t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  (s.gpr (var t 0)).setWidth 32 = v[0] ∧ (s.gpr (var t 1)).setWidth 32 = v[1] ∧
  (s.gpr (var t 2)).setWidth 32 = v[2] ∧ (s.gpr (var t 3)).setWidth 32 = v[3] ∧
  (s.gpr (var t 4)).setWidth 32 = v[4] ∧ (s.gpr (var t 5)).setWidth 32 = v[5] ∧
  (s.gpr (var t 6)).setWidth 32 = v[6] ∧ (s.gpr (var t 7)).setWidth 32 = v[7]

/-- The pointers, the count and the nonvolatile registers the iterations do
not use: never written by the iterations. -/
def pubRegs : List Reg := [.r3, .r4, .r5, .r6, .r2, .r20, .r21, .r22, .r23, .r24, .r25, .r26,
  .r27, .r28, .r29, .r30, .r31]

/-- `A … D` move one register along each iteration, and so do `E … H`:
the new `A` and `E` are written over `D` and `H`. -/
theorem var_succ (t : Nat) :
    var (t + 1) 0 = var t 3 ∧ var (t + 1) 1 = var t 0 ∧ var (t + 1) 2 = var t 1 ∧
    var (t + 1) 3 = var t 2 ∧ var (t + 1) 4 = var t 7 ∧ var (t + 1) 5 = var t 4 ∧
    var (t + 1) 6 = var t 5 ∧ var (t + 1) 7 = var t 6 := by
  simp only [var]
  rw [show (t + 1) % 4 = (t % 4 + 1) % 4 by omega_using []]
  have := Nat.mod_lt t (show 4 > 0 by decide)
  generalize t % 4 = c at *
  revert this; revert c; decide

/-- The registers of an iteration are all different. -/
theorem round_nodup (t : Nat) :
    ([var t 0, var t 1, var t 2, var t 3, var t 4, var t 5, var t 6, var t 7, T0, T1, T2, T3] ++
      pubRegs).Nodup := by
  simp only [var]
  have := Nat.mod_lt t (show 4 > 0 by decide)
  generalize t % 4 = c at *
  revert this; revert c; decide

theorem slot_ok (j : Nat) : slot j < 2 ^ 15 := by
  simp only [slot]; omega_using []

/-- The address of `W[j mod 16]`. -/
abbrev slotAddr (scr : Addr) (j : Nat) : Addr := scr + BitVec.ofNat 64 (slot j)

/-- `TT1`, in the order the iteration adds its terms (`D + W'_j + FF_j`
first, then `SS2`, with `E + (T_j <<< j)` added first in `SS1`). -/
theorem tt1_eqR (d x f r t e : Word) :
    d + x + f + (r ^^^ (r + (t + e)).rotateRight 25) = f + d + ((r + e + t).rotateRight 25 ^^^ r) + x := by
  rw [show r + (t + e) = r + e + t by simp only [ac]]
  simp only [ac]

/-- `P_0(TT2)`, in the order the iteration adds its terms (`H + W_j + GG_j`
first, then `SS1`). -/
theorem tt2_eqR (h w g r t e : Word) :
    (h + w + g + (r + (t + e)).rotateRight 25 ^^^ (h + w + g + (r + (t + e)).rotateRight 25).rotateRight 23) ^^^
      (h + w + g + (r + (t + e)).rotateRight 25).rotateRight 15 =
      p0 (g + h + (r + e + t).rotateRight 25 + w) := by
  rw [show r + (t + e) = r + e + t by simp only [ac]]
  generalize (r + e + t).rotateRight 25 = s
  rw [show h + w + g + s = h + s + w + g by simp only [ac]]
  exact tt2_eq h s w g

/-- The symbolic execution of an iteration, of either shape (`t < 16` or
not), for any registers `A … H` (which `round_nodup` says are different
from each other and the others). -/
theorem round_ok (t : Nat) (s : State) (v : HashValue) (w w₄ : Word) (scr : Addr)
    (hv : Vars t s v) (hr6 : s.gpr .r6 = scr)
    (hin : InRegions (s.rd ++ s.wr) (slotAddr scr t) 4)
    (hin₄ : InRegions (s.rd ++ s.wr) (slotAddr scr (t + 4)) 4)
    (hw : s.mem.readW (slotAddr scr t) 32 = w) (hw₄ : s.mem.readW (slotAddr scr (t + 4)) 32 = w₄) :
    WP isa (.block (round t)) s fun s' =>
      Vars (t + 1) s' (roundW v t w w₄) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := by
  have hs := (List.nodup_append.mp (round_nodup t)).1
  have hs' := List.nodup_reverse.mpr hs
  have hdj := (List.nodup_append.mp (round_nodup t)).2.2
  -- The registers the iteration writes are not in `pubRegs`.
  have hpw : ∀ r ∈ pubRegs, r ≠ var t 1 ∧ r ≠ var t 3 ∧ r ≠ var t 5 ∧ r ≠ var t 7 ∧
      r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 := fun r hr =>
    ⟨fun e => hdj _ (by simp) r hr e.symm, fun e => hdj _ (by simp) r hr e.symm,
      fun e => hdj _ (by simp) r hr e.symm, fun e => hdj _ (by simp) r hr e.symm,
      fun e => hdj _ (by simp) r hr e.symm, fun e => hdj _ (by simp) r hr e.symm,
      fun e => hdj _ (by simp) r hr e.symm, fun e => hdj _ (by simp) r hr e.symm⟩
  clear hdj
  have hr6w := hpw .r6 (by simp [pubRegs])
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := var_succ t
  simp only [Vars, e0, e1, e2, e3, e4, e5, e6, e7] at hv ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hv
  simp only [slotAddr] at hin hin₄ hw hw₄
  apply WP.of_runBlock
  by_cases ht : t < 16 <;> (
    simp only [Impl.Sm3.PPC64LE.round, ht, ite_true, ite_false, List.cons_append, List.nil_append]
    generalize var t 0 = a at *
    generalize var t 1 = b at *
    generalize var t 2 = c at *
    generalize var t 3 = d at *
    generalize var t 4 = e at *
    generalize var t 5 = f at *
    generalize var t 6 = g at *
    generalize var t 7 = h at *
    simp only [T0, T1, T2, T3] at hpw hr6w ⊢
    simp only [T0, T1, T2, T3, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, or_false, not_or,
      List.nodup_nil, and_true] at hs hs'
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_rotr_w, exec_add, exec_lis,
      exec_ori, exec_logic, exec_load_w, slot_ok, isa, RegUpd.gpr_write, RegUpd.mem_write,
      RegUpd.rd_write, RegUpd.wr_write, hs, hs', hr6w, hr6, hin, hin₄,
      Option.some.injEq, exists_eq_left', Nat.reduceLT, ↓reduceIte, reduceCtorEq, ne_eq,
      not_false_eq_true, true_and]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun r hr => ?_⟩
    rotate_right
    · obtain ⟨n1, n3, n5, n7, n16, n17, n18, n19⟩ := hpw r hr
      simp only [n1, n3, n5, n7, n16, n17, n18, n19, ↓reduceIte]
    all_goals
      simp only [lo32_add, BitVec.setWidth_xor, BitVec.setWidth_and, BitVec.setWidth_or,
        BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, lis_ori', h0, h1, h2, h3, h4, h5, h6, h7,
        hw, hw₄, Nat.reduceLeDiff]
    all_goals
      simp only [roundW_0, roundW_1, roundW_2, roundW_3, roundW_4, roundW_5, roundW_6, roundW_7,
        Spec.Sm3.ff, Spec.Sm3.gg, ht, ite_true, ite_false, maj_eq, ch_eq, tj, rotl9,
        rotl12, rotl7, rotl19] <;>
      first | exact tt1_eqR _ _ _ _ _ _ | exact tt2_eqR _ _ _ _ _ _)

theorem expand_ok (i : Nat) (s : State) (M : Block) (bp scr : Addr)
    (hr4 : s.gpr .r4 = bp) (hr6 : s.gpr .r6 = scr)
    (hin : ∀ j, InRegions (s.rd ++ s.wr) (slotAddr scr j) 4)
    (hout : ∀ j, InRegions s.wr (slotAddr scr j) 4)
    (hbin : i < 16 → InRegions (s.rd ++ s.wr) (bp + BitVec.ofNat 64 (4 * i)) 4)
    (hblk : i < 16 → rev32 (s.mem.readW (bp + BitVec.ofNat 64 (4 * i)) 32) = W M i)
    (hwin : 16 ≤ i → ∀ j, j < i → i ≤ j + 16 → s.mem.readW (slotAddr scr j) 32 = W M j) :
    WP isa (.block (expand i)) s fun s' =>
      s'.mem = s.mem.writeW (slotAddr scr i) (W M i) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ r, r ≠ T0 → r ≠ T1 → r ≠ T2 → r ≠ T3 → r ≠ .r0 → s'.gpr r = s.gpr r := by
  simp only [slotAddr] at hin hout hwin ⊢
  apply WP.of_runBlock
  by_cases hi : i < 16
  · have hi' := hbin hi
    have hb := hblk hi
    simp only [Impl.Sm3.PPC64LE.expand, hi, ite_true, T0, T1, T2, T3]
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_li (show 4 * i < 2 ^ 15 by omega_using [hi]),
      exec_loadRev_w, exec_store_w, slot_ok, isa, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, hr4, hr6, hi', hout,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, hb, Option.some.injEq,
      exists_eq_left', Nat.reduceLeDiff, reduceCtorEq, ↓reduceIte, ne_eq,
      not_false_eq_true, true_and]
    refine fun r h0 _ _ _ h4 => ?_
    simp [h0, h4]
  · have hw := hwin (by omega_using [hi])
    have e16 := hw (i - 16) (by omega_using [hi]) (by omega_using [])
    have e9 := hw (i - 9) (by omega_using [hi]) (by omega_using [])
    have e3 := hw (i - 3) (by omega_using [hi]) (by omega_using [])
    have e13 := hw (i - 13) (by omega_using [hi]) (by omega_using [])
    have e6 := hw (i - 6) (by omega_using [hi]) (by omega_using [])
    rw [show slot (i - 16) = slot i by simp only [slot]; omega_using [hi]] at e16
    rw [show slot (i - 9) = slot (i + 7) by simp only [slot]; omega_using [hi]] at e9
    rw [show slot (i - 3) = slot (i + 13) by simp only [slot]; omega_using [hi]] at e3
    rw [show slot (i - 13) = slot (i + 3) by simp only [slot]; omega_using [hi]] at e13
    rw [show slot (i - 6) = slot (i + 10) by simp only [slot]; omega_using [hi]] at e6
    simp only [Impl.Sm3.PPC64LE.expand, hi, ite_false, T0, T1, T2, T3]
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_load_w, exec_store_w, slot_ok,
      exec_logic, exec_rotr_w, isa, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, hr6, hin, hout, Option.some.injEq,
      exists_eq_left', Nat.reduceLT, reduceCtorEq, ↓reduceIte, ne_eq, not_false_eq_true, true_and]
    simp only [BitVec.setWidth_xor, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
      e16, e9, e3, e13, e6, Nat.reduceLeDiff]
    have hW := W_ge M (j := i) (by omega_using [hi])
    rw [Spec.Sm3.p1, rotl15 (W M (i - 3)), rotl7, rotl15, rotl23] at hW
    refine ⟨by rw [hW], fun r h0 h1 h2 _ _ => ?_⟩
    simp [h0, h1, h2]

/-! ## The 64 iterations -/

theorem var_mem (t k : Nat) : var t k ∈ group₁ ++ group₂ := by
  unfold var
  split
  · refine List.mem_append_left _ ?_
    unfold List.getD
    cases hn : group₁[(k + 4 - t % 4) % 4]?
    · simp [group₁]
    · exact List.mem_of_getElem? hn
  · refine List.mem_append_right _ ?_
    unfold List.getD
    cases hn : group₂[(k + 4 - t % 4) % 4]?
    · have := Nat.mod_lt (k + 4 - t % 4) (show 4 > 0 by decide)
      simp [group₂] at hn; omega
    · exact List.mem_of_getElem? hn

theorem work_ne' : ∀ r ∈ group₁ ++ group₂, r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 ∧ r ≠ .r0 := by
  decide

theorem work_ne {r : Reg} (h : r ∈ group₁ ++ group₂) : r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 ∧ r ≠ .r0 :=
  work_ne' r h

theorem pubRegs_ne' : ∀ r ∈ pubRegs, r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 ∧ r ≠ .r0 := by decide

theorem pubRegs_ne {r : Reg} (h : r ∈ pubRegs) : r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 ∧ r ≠ .r0 :=
  pubRegs_ne' r h

/-- The window `⟨scr, 64⟩`. -/
abbrev winRegion (scr : Addr) : Region := ⟨scr, 64⟩

theorem win_contains (scr : Addr) (j : Nat) : (winRegion scr).Contains (slotAddr scr j) 4 := by
  simp only [Region.Contains, slotAddr, slot]
  have : j % 16 < 16 := Nat.mod_lt _ (by omega_using [])
  generalize j % 16 = p at *
  rw [Offset.add_sub_cancel_left]
  simp only [BitVec.toNat_ofNat]
  omega_using [this]

theorem slot_sep (scr : Addr) {i j : Nat} (h : i % 16 ≠ j % 16) :
    Mem.Sep (slotAddr scr i) 4 (slotAddr scr j) 4 := by
  simp only [slotAddr, slot]
  exact Offset.sep _ (by omega_using [h]) (by omega_using []) (by omega_using [])

/-- What holds during the iterations, relative to the state `sB` at their
start: the registers `V` are those of iteration `t`, and the window holds
`W_j` for the 16 words `j` before `i`. -/
structure Inv (V : HashValue) (M : Block) (scr : Addr) (sB : State) (t i : Nat) (s : State) : Prop where
  vars : Vars t s V
  pub : ∀ r ∈ pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  frame : Frame [winRegion scr] sB.mem s.mem
  win : ∀ j < i, i ≤ j + 16 → s.mem.readW (slotAddr scr j) 32 = W M j

/-- After iteration `t`, the window holds `W_{t-12} … W_{t+3}`. -/
abbrev RInv (H : HashValue) (M : Block) (scr : Addr) (sB : State) (t : Nat) : State → Prop :=
  Inv (Spec.Sm3.rounds H M t) M scr sB t (t + 4)

section
variable {H : HashValue} {M : Block} {bp scr : Addr} {sB : State}
  (hr4 : sB.gpr .r4 = bp) (hr6 : sB.gpr .r6 = scr)
  (hin : ∀ j, InRegions (sB.rd ++ sB.wr) (slotAddr scr j) 4)
  (hout : ∀ j, InRegions sB.wr (slotAddr scr j) 4)
  (hbin : ∀ t : Nat, t < 16 → InRegions (sB.rd ++ sB.wr) (bp + BitVec.ofNat 64 (4 * t)) 4)
  (hblk : ∀ m, Frame [winRegion scr] sB.mem m →
    ∀ t : Nat, t < 16 → rev32 (m.readW (bp + BitVec.ofNat 64 (4 * t)) 32) = W M t)
include hr4 hr6 hin hout hbin hblk

theorem expand_inv {V : HashValue} {t i : Nat} {s : State} (hs : Inv V M scr sB t i s) :
    WP isa (.block (expand i)) s (Inv V M scr sB t (i + 1)) := by
  refine WP.mono (expand_ok i s M bp scr ((hs.pub .r4 (by decide)).trans hr4)
    ((hs.pub .r6 (by decide)).trans hr6)
    (by rw [hs.rd, hs.wr]; exact hin) (by rw [hs.wr]; exact hout)
    (fun h => by rw [hs.rd, hs.wr]; exact hbin i h) (hblk _ hs.frame i)
    (fun _ => hs.win)) fun s₁ ⟨hm₁, hrd₁, hwr₁, hr₁⟩ => ?_
  refine ⟨?_, fun r hr => ?_, by rw [hrd₁, hs.rd], by rw [hwr₁, hs.wr], ?_, ?_⟩
  · have hv := hs.vars
    have e : ∀ k, s₁.gpr (var t k) = s.gpr (var t k) := fun k =>
      have := work_ne (var_mem t k); hr₁ _ this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2
    simp only [Vars, e] at hv ⊢
    exact hv
  · have := pubRegs_ne hr
    rw [hr₁ r this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2, hs.pub r hr]
  · rw [hm₁]
    exact hs.frame.writeW (List.mem_singleton_self _) _ (win_contains scr i)
  · intro j hj hj'
    rw [hm₁]
    by_cases hji : j = i
    · subst hji; exact Mem.readW_writeW_self32 _ _ _
    · rw [Mem.readW_writeW_sep (slot_sep scr (by omega_using [hj, hj', hji])) (by decide)]
      exact hs.win j (by omega_using [hj, hji]) (by omega_using [hj'])

theorem rounds_ok (h0 : Vars 0 sB H) : ∀ t ≤ 64, WP isa (rounds t) sB (RInv H M scr sB t) := by
  intro t ht
  induction t with
  | zero =>
    have i₀ : Inv H M scr sB 0 0 sB :=
      ⟨h0, fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (by omega_using [])⟩
    show WP isa (.block (expand 0 ++ expand 1 ++ expand 2 ++ expand 3)) sB _
    rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (expand_inv hr4 hr6 hin hout hbin hblk i₀) fun s₁ h₁ => ?_
    refine WP.mono (expand_inv hr4 hr6 hin hout hbin hblk h₁) fun s₂ h₂ => ?_
    refine WP.mono (expand_inv hr4 hr6 hin hout hbin hblk h₂) fun s₃ h₃ => ?_
    exact expand_inv hr4 hr6 hin hout hbin hblk h₃
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by omega_using [ht])) fun s hs => ?_)
    rw [WP.block_append_iff]
    refine WP.mono (expand_inv hr4 hr6 hin hout hbin hblk hs) fun s₁ h₁ => ?_
    have hr6₁ : s₁.gpr .r6 = scr := (h₁.pub .r6 (by decide)).trans hr6
    refine WP.mono (round_ok t s₁ _ (W M t) (W M (t + 4)) scr h₁.vars hr6₁
      (by rw [h₁.rd, h₁.wr]; exact hin t) (by rw [h₁.rd, h₁.wr]; exact hin (t + 4))
      (h₁.win t (by omega_using []) (by omega_using [])) (h₁.win (t + 4) (by omega_using []) (by omega_using [])))
      fun s₂ ⟨hv₂, hm₂, hrd₂, hwr₂, hr₂⟩ => ?_
    refine ⟨?_, fun r hr => by rw [hr₂ r hr, h₁.pub r hr], by rw [hrd₂, h₁.rd],
      by rw [hwr₂, h₁.wr], by rw [hm₂]; exact h₁.frame, fun j hj hj' => ?_⟩
    · rw [rounds_succ, round_eq]; exact hv₂
    · rw [hm₂]; exact h₁.win j (by omega_using [hj]) (by omega_using [hj'])

end

end VG.Proof.Sm3.PPC64LE

end

end

/-!
# SM3 compression function on PPC64LE: the whole function

Untrusted: everything here is checked by Lean.
-/

@[expose] public section

namespace VG.Proof.Sm3.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm3.PPC64LE
open VG.Spec.Sm3 (HashValue Word Block W stateAt blockAt compressBlocks compress parseBlock)

/-! The hash value in memory and offsets into regions (`Proof/Sm3/StateMem.lean`). -/
export VG.Proof.Sm3.StateMem (toNat_ofNat_lt contains_offset sub_offset word_sep
  readW_writeW_word stateAt_eq stateAt_get writeState stateAt_writeState)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .r3
abbrev bp : Addr := s₀.gpr .r4
abbrev nb : Nat := (s₀.gpr .r5).toNat
abbrev scr : Addr := s₀.gpr .r6
abbrev stR : Region := ⟨st s₀, 32⟩
abbrev blR : Region := ⟨bp s₀, 64 * nb s₀⟩
abbrev scrR : Region := ⟨scr s₀, 112⟩
abbrev H₀ : HashValue := stateAt s₀.mem (st s₀)
/-- Where the nonvolatile registers are saved. -/
abbrev savR : Region := ⟨scr s₀ + BitVec.ofNat 64 64, 48⟩
/-- Where nonvolatile register `i` is saved. -/
abbrev savAddr (i : Nat) : Addr := scr s₀ + BitVec.ofNat 64 (64 + 8 * i)

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : Addr := bp s₀ + BitVec.ofNat 64 (64 * i)
abbrev blk (i : Nat) : Block := blockAt s₀.mem (blkAddr s₀ i)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  blk_st : (blR s₀).Disjoint (stR s₀)
  blk_scr : (blR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : Proof.Sm3.compressPPC64LE.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem nb_lt : 64 * nb s₀ < 2 ^ 64 := by
  by_contra hn
  refine h.blk_st (st s₀) ?_ (by simp [Region.Contains])
  simp only [Region.Contains]
  have := (st s₀ - bp s₀).isLt
  omega_using [hn]

theorem in_state {k : Nat} (hk : k < 8) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_offset (by omega_using [hk]) (by omega_using [hk])⟩

theorem out_state {k : Nat} (hk : k < 8) :
    InRegions s₀.wr (st s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_offset (by omega_using [hk]) (by omega_using [hk])⟩

theorem in_slot (j : Nat) : InRegions (s₀.rd ++ s₀.wr) (slotAddr (scr s₀) j) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset (by simp only [slot]; omega_using []) (by simp only [slot]; omega_using [])⟩

theorem out_slot (j : Nat) : InRegions s₀.wr (slotAddr (scr s₀) j) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset (by simp only [slot]; omega_using []) (by simp only [slot]; omega_using [])⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 4 := by
  have := h.nb_lt
  rw [show blkAddr s₀ i + BitVec.ofNat 64 (4 * t) =
    bp s₀ + BitVec.ofNat 64 (64 * i + 4 * t) from Offset.add_add _ _ _]
  exact contains_offset (by omega_using [hi, ht]) (by omega_using [hi, ht, this])

theorem in_sav {i : Nat} (hi : i < 6) (rs : List Region) :
    InRegions (rs ++ s₀.wr) (scr s₀ + BitVec.ofNat 64 (64 + 8 * i)) 8 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset (by omega_using [hi]) (by omega_using [hi])⟩

theorem out_sav {i : Nat} (hi : i < 6) : InRegions s₀.wr (scr s₀ + BitVec.ofNat 64 (64 + 8 * i)) 8 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset (by omega_using [hi]) (by omega_using [hi])⟩

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 4 :=
  ⟨blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

/-! ## Saving and restoring the nonvolatile registers -/

/-- The nonvolatile registers the code does not use: never written. -/
def keepRegs : List Reg := [.r2, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30,
  .r31]

theorem keepRegs_pub : ∀ r ∈ keepRegs, r ∈ pubRegs := by decide

/-- A preserved register is saved, or kept. -/
theorem preserved_cases : ∀ r ∈ preserved, (∃ i < 6, r = saved i) ∨ r ∈ keepRegs := by decide

theorem saved_inj {i j : Nat} (hi : i < 6) (hj : j < 6) (h : saved i = saved j) : i = j := by
  have key : ∀ i < 6, ∀ j < 6, saved i = saved j → i = j := by decide
  exact key i hi j hj h

theorem saved_ne {i : Nat} (hi : i < 6) : saved i ≠ .r3 ∧ saved i ≠ .r6 ∧ saved i ∉ keepRegs := by
  have key : ∀ i < 6, saved i ≠ .r3 ∧ saved i ≠ .r6 ∧ saved i ∉ keepRegs := by decide
  exact key i hi

theorem sav_sep (p : Addr) {i j : Nat} (hi : i < 6) (hj : j < 6) (h : i ≠ j) :
    Mem.Sep (p + BitVec.ofNat 64 (64 + 8 * i)) 8 (p + BitVec.ofNat 64 (64 + 8 * j)) 8 := by
  intro x hx hy
  bv_omega

theorem savR_sub (s₀ : State) : Region.Sub (savR s₀) (scrR s₀) := sub_offset (by omega_using []) (by omega_using [])

theorem win_sav (s₀ : State) : (winRegion (scr s₀)).Disjoint (savR s₀) := by
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  bv_omega

theorem sav_contains (s₀ : State) {i : Nat} (hi : i < 6) : (savR s₀).Contains (savAddr s₀ i) 8 := by
  simp only [Region.Contains]; bv_omega

/-- The first `n` registers are saved. -/
structure SI (s₀ : State) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [savR s₀] s₀.mem s.mem
  saved : ∀ i < n, s.mem.readW (savAddr s₀ i) 64 = s₀.gpr (saved i)

theorem save_step {s₀ : State} (hp : Pre s₀) {n : Nat} (hn : n < 6) {s : State} (h : SI s₀ n s) :
    WP isa (.block [.store .d (saved n) .r6 (64 + 8 * n)]) s (SI s₀ (n + 1)) := by
  have hr6 : s.gpr .r6 = scr s₀ := by rw [h.gpr]
  have hout : InRegions s.wr (s.gpr .r6 + BitVec.ofNat 64 (64 + 8 * n)) 8 := by
    rw [h.wr, hr6]; exact hp.out_sav hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_store_d (by decide) (show 64 + 8 * n < 2 ^ 15 ∧ (64 + 8 * n) % 4 = 0 by omega_using [hn]) hout,
    Option.some.injEq, exists_eq_left', hr6]
  refine ⟨h.gpr, h.rd, h.wr, h.frame.writeW (List.mem_singleton_self _) _ (sav_contains s₀ hn),
    fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · rw [Mem.readW_writeW_sep (sav_sep _ (by omega_arith) hn (by omega_using [hi])) (by decide)]
    exact h.saved i hi
  · rw [Mem.readW_writeW_self64, h.gpr]

/-- The first `n` registers are restored, from the state `sB` the restoring
starts in. -/
structure RI (s₀ sB : State) (n : Nat) (s : State) : Prop where
  restored : ∀ i < n, s.gpr (saved i) = s₀.gpr (saved i)
  others : ∀ r, (∀ i < 6, r ≠ saved i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem restore_step {s₀ sB : State} (hp : Pre s₀) (hr6 : sB.gpr .r6 = scr s₀)
    (hsav : ∀ i < 6, sB.mem.readW (savAddr s₀ i) 64 = s₀.gpr (saved i))
    {n : Nat} (hn : n < 6) {s : State} (h : RI s₀ sB n s) :
    WP isa (.block [.load .d (saved n) .r6 (64 + 8 * n)]) s (RI s₀ sB (n + 1)) := by
  have hr6' : s.gpr .r6 = scr s₀ := by
    rw [h.others _ fun i hi e => (saved_ne hi).2.1 e.symm, hr6]
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r6 + BitVec.ofNat 64 (64 + 8 * n)) 8 := by
    rw [h.rd, h.wr, hr6']; exact hp.in_sav hn _
  have hv : s.mem.readW (scr s₀ + BitVec.ofNat 64 (64 + 8 * n)) 64 = s₀.gpr (saved n) := by
    rw [h.mem]; exact hsav n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (by decide) (show 64 + 8 * n < 2 ^ 15 ∧ (64 + 8 * n) % 4 = 0 by omega_using [hn]) hin,
    Option.some.injEq, exists_eq_left', hr6', hv]
  refine ⟨fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr⟩
  · simp only [State.write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have e : saved i ≠ saved n := fun e => absurd (saved_inj (by omega_arith) hn e) (by omega_using [hi])
      simp only [e, ite_false]; exact h.restored i hi
    · simp
  · simp only [State.write, hr n hn, ite_false]; exact h.others r hr

/-! ## The loop invariant -/

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = st s₀
  r6 : s.gpr .r6 = scr s₀
  kept : ∀ r ∈ keepRegs, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  sav : ∀ i < 6, s.mem.readW (savAddr s₀ i) 64 = s₀.gpr (saved i)
  state : stateAt s.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) i

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  r4 : s.gpr .r4 = blkAddr s₀ i
  r5 : s.gpr .r5 = BitVec.ofNat 64 (nb s₀ - i)

/-! ## One block -/

theorem load_eq : load = [
    .load .w .r7 .r3 (4 * 0), .load .w .r8 .r3 (4 * 1), .load .w .r9 .r3 (4 * 2),
    .load .w .r10 .r3 (4 * 3), .load .w .r11 .r3 (4 * 4), .load .w .r12 .r3 (4 * 5),
    .load .w .r14 .r3 (4 * 6), .load .w .r15 .r3 (4 * 7)] := by
  decide

theorem update_eq : update ++ advance = [
    .load .w .r16 .r3 (4 * 0), .load .w .r17 .r3 (4 * 1), .load .w .r18 .r3 (4 * 2),
    .load .w .r19 .r3 (4 * 3),
    .logic .xor .r7 .r7 .r16, .logic .xor .r8 .r8 .r17, .logic .xor .r9 .r9 .r18,
    .logic .xor .r10 .r10 .r19,
    .load .w .r16 .r3 (4 * (0 + 4)), .load .w .r17 .r3 (4 * (1 + 4)),
    .load .w .r18 .r3 (4 * (2 + 4)), .load .w .r19 .r3 (4 * (3 + 4)),
    .logic .xor .r11 .r11 .r16, .logic .xor .r12 .r12 .r17, .logic .xor .r14 .r14 .r18,
    .logic .xor .r15 .r15 .r19,
    .store .w .r7 .r3 (4 * 0), .store .w .r8 .r3 (4 * 1), .store .w .r9 .r3 (4 * 2),
    .store .w .r10 .r3 (4 * 3), .store .w .r11 .r3 (4 * 4), .store .w .r12 .r3 (4 * 5),
    .store .w .r14 .r3 (4 * 6), .store .w .r15 .r3 (4 * 7),
    .addi .r4 .r4 64, .subi .r5 .r5 1] := by
  decide

theorem vars0 (s : State) (v : HashValue) : Vars 0 s v ↔
    (s.gpr .r7).setWidth 32 = v[0] ∧ (s.gpr .r8).setWidth 32 = v[1] ∧
    (s.gpr .r9).setWidth 32 = v[2] ∧ (s.gpr .r10).setWidth 32 = v[3] ∧
    (s.gpr .r11).setWidth 32 = v[4] ∧ (s.gpr .r12).setWidth 32 = v[5] ∧
    (s.gpr .r14).setWidth 32 = v[6] ∧ (s.gpr .r15).setWidth 32 = v[7] := Iff.rfl

theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hr3 : s.gpr .r3 = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block load) s fun s₁ =>
      Vars 0 s₁ (stateAt s.mem (st s₀)) ∧ (∀ r ∈ pubRegs, s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
  have hin : ∀ k : Nat, k < 8 → InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
  have h3 := hin 3 (by decide); have h4 := hin 4 (by decide); have h5 := hin 5 (by decide)
  have h6 := hin 6 (by decide); have h7 := hin 7 (by decide)
  simp only [Nat.reduceMul] at h0 h1 h2 h3 h4 h5 h6 h7
  apply WP.of_runBlock
  rw [load_eq]
  simp only [vars0, runBlock_cons, runStep_some, runBlock_nil, exec_load_w, isa, State.write, hr3,
    h0, h1, h2, h3, h4, h5, h6, h7, Option.some.injEq, exists_eq_left', Nat.reduceMul,
    Nat.reducePow, Nat.reduceLT, reduceCtorEq, ↓reduceIte, ne_eq, not_false_eq_true, and_self,
    and_true]
  simp only [stateAt_get _ _ (show 0 < 8 by decide), stateAt_get _ _ (show 1 < 8 by decide),
    stateAt_get _ _ (show 2 < 8 by decide), stateAt_get _ _ (show 3 < 8 by decide),
    stateAt_get _ _ (show 4 < 8 by decide), stateAt_get _ _ (show 5 < 8 by decide),
    stateAt_get _ _ (show 6 < 8 by decide), stateAt_get _ _ (show 7 < 8 by decide)]
  simp [pubRegs]

theorem frame_writeState {s₀ : State} {m m' : Mem} (h : Frame [stR s₀] m m') (v : HashValue) :
    Frame [stR s₀] m (writeState m' (st s₀) v) := by
  have c : ∀ k, k < 8 → (stR s₀).Contains (st s₀ + BitVec.ofNat 64 (4 * k)) (32 / 8) :=
    fun k hk => contains_offset (by omega_using [hk]) (by omega_using [hk])
  simp only [writeState]
  refine (((((((h.writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 1 ?_)).writeW ?_ _ (c 2 ?_)).writeW ?_ _
    (c 3 ?_)).writeW ?_ _ (c 4 ?_)).writeW ?_ _ (c 5 ?_)).writeW ?_ _ (c 6 ?_)).writeW ?_ _ (c 7 ?_) <;>
  simp

theorem update_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue) (hv : Vars 0 s V)
    (hr3 : s.gpr .r3 = st s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hH : ∀ k : Nat, (hk : k < 8) → s.mem.readW (st s₀ + BitVec.ofNat 64 (4 * k)) 32 = H[k]) :
    WP isa (.block (update ++ advance)) s fun s' =>
      s'.mem = writeState s.mem (st s₀) (Vector.zipWith (· ^^^ ·) V H) ∧
      s'.gpr .r4 = s.gpr .r4 + 64 ∧ s'.gpr .r5 = s.gpr .r5 - 1 ∧
      s'.gpr .r3 = s.gpr .r3 ∧ s'.gpr .r6 = s.gpr .r6 ∧
      (∀ r ∈ keepRegs, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : ∀ k : Nat, k < 8 → InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have hout : ∀ k : Nat, k < 8 → InRegions s.wr (st s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [hwr]; exact fun k hk => hp.out_state hk
  have i0 := hin 0 (by decide); have i1 := hin 1 (by decide); have i2 := hin 2 (by decide)
  have i3 := hin 3 (by decide); have i4 := hin (0 + 4) (by decide); have i5 := hin (1 + 4) (by decide)
  have i6 := hin (2 + 4) (by decide); have i7 := hin (3 + 4) (by decide)
  have o0 := hout 0 (by decide); have o1 := hout 1 (by decide); have o2 := hout 2 (by decide)
  have o3 := hout 3 (by decide); have o4 := hout 4 (by decide); have o5 := hout 5 (by decide)
  have o6 := hout 6 (by decide); have o7 := hout 7 (by decide)
  have m0 := hH 0 (by decide); have m1 := hH 1 (by decide); have m2 := hH 2 (by decide)
  have m3 := hH 3 (by decide); have m4 := hH (0 + 4) (by decide); have m5 := hH (1 + 4) (by decide)
  have m6 := hH (2 + 4) (by decide); have m7 := hH (3 + 4) (by decide)
  rw [vars0] at hv
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := hv
  apply WP.of_runBlock
  rw [update_eq]
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_load_w, exec_store_w, exec_logic,
    exec_addi, exec_subi, State.write, hr3, i0, i1, i2, i3, i4, i5, i6, i7, o0, o1, o2, o3, o4, o5,
    o6, o7, Option.some.injEq, exists_eq_left', Nat.reduceAdd, Nat.reduceMul, Nat.reducePow,
    Nat.reduceLeDiff, Nat.reduceLT, reduceCtorEq, ↓reduceIte, ne_eq, not_false_eq_true, and_self,
    true_and, and_true]
  simp only [BitVec.setWidth_xor, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, m0, m1, m2, m3, m4, m5,
    m6, m7, v0, v1, v2, v3, v4, v5, v6, v7, Nat.reduceAdd, Nat.reduceLeDiff]
  refine ⟨?_, ?_⟩
  · simp only [writeState, Vector.getElem_zipWith]
  and_intros
  all_goals first
    | trivial
    | rfl
    | (intro r hr
       simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
       simp)

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (64 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (i t : Nat) (ht : t < 16) :
    rev32 (s₀.mem.readW (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 32) = W (blk s₀ i) t := by
  rw [W_lt _ ht, rev32_readW]
  simp only [blk, blockAt, parseBlock]
  rw [show blkAddr s₀ i + BitVec.ofNat 64 (4 * t) + 1 = blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 1) from
      Offset.add_add _ _ 1,
    show blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 1) + 1 = blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 2) from
      Offset.add_add _ _ 1,
    show blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 2) + 1 = blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 3) from
      Offset.add_add _ _ 1]

theorem win_sub (p : Addr) : Region.Sub (winRegion p) ⟨p, 112⟩ := Region.sub_prefix (by omega_using [])

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval (.nonzero .d .r5) s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval (.nonzero .d .r5) s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  refine WP.seq (WP.mono (load_ok hp hL.r3 hL.rd hL.wr) fun s₁ ⟨hv₁, hpub₁, hrd₁, hwr₁, hm₁⟩ => ?_)
  have hwin : ∀ r' ∈ [winRegion (scr s₀)], (blR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.blk_scr (win_sub _)
  have hblk : ∀ m, Frame [winRegion (scr s₀)] s₁.mem m → ∀ t : Nat, t < 16 →
      rev32 (m.readW (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 32) = W (blk s₀ i) t := by
    intro m hm t ht
    rw [hm.readW (hp.blk_contains hi ht) hwin (by decide), hm₁,
      hL.frame.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
    exact blk_word i t ht
  have hr4₁ : s₁.gpr .r4 = blkAddr s₀ i := (hpub₁ .r4 (by decide)).trans hL.r4
  have hr6₁ : s₁.gpr .r6 = scr s₀ := (hpub₁ .r6 (by decide)).trans hL.r6
  refine WP.seq (WP.mono (rounds_ok (M := blk s₀ i) (scr := scr s₀) (sB := s₁) hr4₁ hr6₁
    (by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_slot)
    (by rw [hwr₁, hL.wr]; exact hp.out_slot)
    (fun t ht => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_blk hi ht) hblk hv₁ 64 (Nat.le_refl _))
    fun s₂ hR => ?_)
  have hst : ∀ r' ∈ [winRegion (scr s₀)], (stR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.st_scr (win_sub _)
  have pub₂ : ∀ r ∈ pubRegs, s₂.gpr r = s.gpr r := fun r hr => by
    rw [hR.pub r hr, hpub₁ r hr]
  have hr3₂ : s₂.gpr .r3 = st s₀ := by rw [pub₂ .r3 (by decide), hL.r3]
  refine WP.mono (update_ok hp _ (stateAt s.mem (st s₀)) hR.vars hr3₂
    (by rw [hR.rd, hrd₁, hL.rd]) (by rw [hR.wr, hwr₁, hL.wr]) fun k hk => ?_) fun s₃ h₃ => ?_
  · rw [hR.frame.readW (contains_offset (by omega_using [hk]) (by omega_using [hk])) hst (by decide), hm₁,
      stateAt_get _ _ hk]
  obtain ⟨hm₃, hr4₃, hr5₃, hr3₃, hr6₃, hkept₃, hrd₃, hwr₃⟩ := h₃
  have hr5 : s₂.gpr .r5 - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [pub₂ .r5 (by decide), hL.r5]
    have := (s₀.gpr .r5).isLt
    bv_omega
  have hframe : Frame [stR s₀, scrR s₀] s₀.mem s₃.mem := by
    refine hL.frame.trans ?_
    rw [← hm₁]
    refine Frame.trans (hR.frame.sub fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact win_sub _⟩) ?_
    rw [hm₃]
    exact (frame_writeState (Frame.refl _ _) _).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have hsav : ∀ j < 6, s₃.mem.readW (savAddr s₀ j) 64 = s₀.gpr (saved j) := by
    intro j hj
    have hd : (savR s₀).Disjoint (stR s₀) :=
      Region.Disjoint.sub_left hp.st_scr.symm (savR_sub s₀)
    rw [hm₃, writeState]
    simp only [savAddr]
    iterate 8 rw [Mem.readW_writeW_sep (hd.sep (sav_contains s₀ hj) (contains_offset (by omega_using [])
      (by omega_using []))) (by decide)]
    rw [hR.frame.readW (r := savR s₀) (sav_contains s₀ hj) (by simpa using (win_sav s₀).symm)
      (by decide), hm₁]
    exact hL.sav j hj
  have hcommon : ∀ j, j = i + 1 → Common s₀ j s₃ := by
    rintro j rfl
    refine ⟨by rw [hr3₃, hr3₂], by rw [hr6₃, pub₂ .r6 (by decide), hL.r6],
      fun r hr => by rw [hkept₃ r hr, pub₂ r (keepRegs_pub r hr), hL.kept r hr],
      by rw [hrd₃, hR.rd, hrd₁, hL.rd], by rw [hwr₃, hR.wr, hwr₁, hL.wr], hframe, hsav, ?_⟩
    rw [hm₃, stateAt_writeState, compressBlocks_succ, ← hL.state]
    rfl
  have hev : eval (.nonzero .d .r5) s₃ = some (BitVec.ofNat 64 (nb s₀ - (i + 1)) != 0) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hr5₃, hr5]
  have := hp.nb_lt
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon _ rfl⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega_using [hi, hlast]
    have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [this])] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by omega_using [hi, hlast], { hcommon _ rfl with r4 := ?_, r5 := ?_ }⟩
    · rw [hr4₃, pub₂ .r4 (by decide), hL.r4]
      simp only [blkAddr]
      bv_omega
    · rw [hr5₃, hr5]

/-! ## The whole function -/

theorem blocks_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (hc₀ : Common s₀ 0 s₁)
    (hr4 : s₁.gpr .r4 = bp s₀) (hr5 : s₁.gpr .r5 = s₀.gpr .r5) :
    WP isa blocks s₁ (Common s₀ (nb s₀)) := by
  refine WP.ite (s₁.gpr .r5 == 0) (by simp [eval, State.read]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp [hr5] at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [beq_eq_false_iff_ne, ne_eq, hr5] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval (.nonzero .d .r5) s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval (.nonzero .d .r5) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega_using [hi], i + 1, rfl, hi', hL'⟩
    have hL₀ : LInv s₀ 0 s₁ :=
      { hc₀ with
        r4 := by simp [blkAddr, hr4]
        r5 := by simp [nb, hr5] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sm3.compressPPC64LE.post s₀ s' := by
  have hs₀ : SI s₀ 0 s₀ := ⟨rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega_using [])⟩
  have hsave : WP isa (.block save) s₀ (SI s₀ 6) := by
    unfold save
    exact wp_range_flatMap (M := isa) (SI s₀) (fun k s hk h => save_step hp hk h) 6 (Nat.le_refl _) s₀ hs₀
  refine WP.seq (WP.mono hsave fun s₁ h₁ => ?_)
  have hc₀ : Common s₀ 0 s₁ := by
    refine ⟨by rw [h₁.gpr], by rw [h₁.gpr], fun r _ => by rw [h₁.gpr], h₁.rd, h₁.wr,
      h₁.frame.sub fun r hr => ?_, h₁.saved, ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, savR_sub s₀⟩
    · show stateAt s₁.mem (st s₀) = H₀ s₀
      apply stateAt_eq
      intro k hk
      rw [h₁.frame.readW (r := stR s₀) (contains_offset (by omega_using [hk]) (by omega_using [hk]))
        (by simpa using Region.Disjoint.sub_right hp.st_scr (savR_sub s₀)) (by decide),
        ← stateAt_get _ _ hk]
  refine WP.seq (WP.mono (blocks_ok hp hc₀ (by rw [h₁.gpr]) (by rw [h₁.gpr])) fun s₂ h₂ => ?_)
  have hr₀ : RI s₀ s₂ 0 s₂ := ⟨fun _ h => absurd h (by omega_using []), fun _ _ => rfl, rfl, h₂.rd, h₂.wr⟩
  unfold restore
  refine WP.mono (wp_range_flatMap (M := isa) (RI s₀ s₂)
    (fun k s hk h => restore_step hp h₂.r6 h₂.sav hk h) 6 (Nat.le_refl _) s₂ hr₀) fun s' h => ⟨?_, ?_⟩
  · intro r hr
    rcases preserved_cases r hr with ⟨i, hi, rfl⟩ | hk
    · exact h.restored i hi
    · rw [h.others r fun i hi e => (saved_ne hi).2.2 (e ▸ hk), h₂.kept r hk]
  · show stateAt s'.mem (s₀.gpr .r3) = _
    rw [h.mem]
    exact h₂.state

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r6 => 0x3000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x3000, 112⟩]

/-! The constant-time analysis of the compression function from its arguments, done once for
every check of code that calls it (`taint_decide_sum [compressSum]`), which keeps what is public
of `r20`–`r31`: it writes none of them. -/
taint_summary compressSum : taint (Taint.ofRegs [.r3, .r4, .r5, .r6]) Impl.Sm3.PPC64LE.compress
  keeping (Taint.ofRegs [.r20, .r21, .r22, .r23, .r24, .r25,
    .r26, .r27, .r28, .r29, .r30, .r31])

theorem compress_verified :
    Verified PPC64LE.target Impl.Sm3.PPC64LE.compress Proof.Sm3.compressPPC64LE := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.lr he (by decide +kernel)
      (by rw [← Code.allInstrs_eq]; decide +kernel)⟩, h₂⟩
  · refine VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6]) ?_
      (VG.Taint.exists_check_of_sumOk compressSum (RegSet.subset_refl _))
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, hsp⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · refine ⟨satState, rfl, rfl, ?_, ?_, ?_⟩ <;>
    exact Region.disjoint_of_sep (by decide)

end VG.Proof.Sm3.PPC64LE
