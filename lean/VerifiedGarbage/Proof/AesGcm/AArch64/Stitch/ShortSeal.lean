module

import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Run
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Run
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Tables
import VerifiedGarbage.Proof.Gcm.Short
import VerifiedGarbage.Proof.AesGcm.AArch64.Cmp
public import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Mul
import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Seal
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Entry
public import VerifiedGarbage.Proof.AesGcm.AArch64.Seal
public import VerifiedGarbage.Proof.Gcm.Ctr
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Ctr32
public import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
public import VerifiedGarbage.Proof.Aes.KeyExp
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Steps
import VerifiedGarbage.Proof.AesGcm.AArch64.Flush
import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ops
public import VerifiedGarbage.Impl.AesGcm.AArch64.Stitch
public import VerifiedGarbage.Proof.Gcm.Compose
public import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Copy
import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Groups
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Spec.Aes
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem

/-! ### `AesGcm.AArch64.Stitch.ShortBytes`, which this module and modules that import it used -/

section

/-! ### `AesGcm.AArch64.Stitch.ShortAes`, which this module and modules that import it used -/

section

/-! ### `AesGcm.AArch64.Stitch.ShortCopy`, which this module and modules that import it used -/

section

/-!
# AES-GCM on AArch64, short records: copying through `v0`

Untrusted: everything here is checked by Lean. `copyQ`
(`Impl.AesGcm.AArch64.Stitch`) copies the `n` bytes at `x12` to `x11`:
fewer than 16 with `copy` (`copy_ok`), otherwise the whole blocks with
`SealGather.copyBlocks` (`copyBlocks_wp`) and then the last 16 bytes, which
overlap them (`writeBytes_overlap`) (`copyQ_ok`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64.Stitch

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.AArch64 (LoopPre copy_ok eval_zero loopRegs covers_prefix length_bytesAt
  write_read_bytes)
open VG.Proof.AesGcm.AArch64.Gather (BlocksPre copyBlocks_wp Keeps ofNat_lsr4 copyRegs)

/-- A byte after writing the `n` bytes at `S` of `m'` at `D`. -/
theorem writeBytes_bytesAt_apply (m m' : Mem) (D S : Addr) (n : Nat) (a : Addr) :
    writeBytes m D (bytesAt m' S n) a =
      if (a - D).toNat < n then m' (S + BitVec.ofNat 64 (a - D).toNat) else m a := by
  simp only [writeBytes, length_bytesAt]
  split
  · rename_i h
    simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h,
      Option.map_some, Option.getD_some]
  · rfl

/-- `(a − (D + c))` from `(a − D)`, for `c < 2⁶³`. -/
theorem toNat_sub_add (a D : Addr) {c : Nat} (hc : c < 2 ^ 63) :
    (a - (D + BitVec.ofNat 64 c)).toNat =
      if c ≤ (a - D).toNat then (a - D).toNat - c else 2 ^ 64 - c + (a - D).toNat := by
  obtain e : a - (D + BitVec.ofNat 64 c) = (a - D) - BitVec.ofNat 64 c := by
    rw [Offset.sub_add_eq]
  rw [e, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega_arith)]
  have := (a - D).isLt
  split <;> omega_arith

/-- The `16 k` first bytes, then the 16 last (`n − 16 ≤ 16 k ≤ n`), written
over them: all `n`. -/
theorem writeBytes_overlap (m : Mem) (D S : Addr) {n k : Nat} (hk1 : n - 16 ≤ 16 * k) (hk2 : 16 * k ≤ n)
    (h16 : 16 ≤ n) (hn : n < 2 ^ 63) :
    writeBytes (writeBytes m D (bytesAt m S (16 * k))) (D + BitVec.ofNat 64 (n - 16))
        (bytesAt m (S + BitVec.ofNat 64 (n - 16)) 16) =
      writeBytes m D (bytesAt m S n) := by
  funext a
  rw [writeBytes_bytesAt_apply, writeBytes_bytesAt_apply, writeBytes_bytesAt_apply,
    toNat_sub_add a D (show n - 16 < 2 ^ 63 by omega_arith)]
  generalize ht : (a - D).toNat = t
  obtain htl : t < 2 ^ 64 := ht ▸ (a - D).isLt
  by_cases h1 : n - 16 ≤ t
  · simp only [h1, ite_true]
    by_cases h2 : t - (n - 16) < 16
    · simp only [h2, ite_true, show t < n by omega_arith]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' h1]
    · simp only [h2, ite_false, show ¬t < n by omega_arith, show ¬t < 16 * k by omega_arith]
  · simp only [h1, ite_false, show ¬2 ^ 64 - (n - 16) + t < 16 by omega_arith, show t < n by omega_arith,
      show t < 16 * k by omega_arith, ite_true]

/-- What `copyQ` needs. -/
structure QPre (s : State) (S D : Addr) (n : Nat) : Prop where
  x12 : s.gpr .x12 = S
  x11 : s.gpr .x11 = D
  x13 : s.gpr .x13 = BitVec.ofNat 64 n
  lt : n < 2 ^ 63
  rd : Covers [⟨S, n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨D, n⟩] s.wr
  disj : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩

/-- The registers `copyQ` writes. -/
abbrev qRegs : List Reg := [.x9, .x10, .x11, .x12, .x13, .x14, .x15]

/-- What `copyQ` leaves: the bytes copied, and only `qRegs` (and `v0`) written. -/
def QPost (s : State) (S D : Addr) (n : Nat) (s' : State) : Prop :=
  s'.mem = writeBytes s.mem D (bytesAt s.mem S n) ∧ (∀ r, r ∉ qRegs → s'.gpr r = s.gpr r) ∧
    s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem copyQ_ok (s : State) {S D : Addr} {n : Nat} (h : QPre s S D n) :
    WP isa Impl.AesGcm.AArch64.Stitch.copyQ s (QPost s S D n) := by
  have hn := h.lt
  unfold Impl.AesGcm.AArch64.Stitch.copyQ
  -- `x14 = n / 16`.
  refine WP.seq (WP.of_runBlock ⟨s.write .x .x14 (s.read .x .x13 >>> 4), by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceLT, ite_true, Size.bits], ?_⟩)
  obtain x14₁ : (s.write .x .x14 (s.read .x .x13 >>> 4)).gpr .x14 = BitVec.ofNat 64 (n / 16) := by
    simp only [gpr_write_self, State.read, h.x13, BitVec.setWidth_eq, ofNat_lsr4 (show n < 2 ^ 64 by omega_arith)]
  generalize hs₁ : s.write .x .x14 (s.read .x .x13 >>> 4) = s₁ at x14₁
  obtain g₁ : ∀ r, r ≠ .x14 → s₁.gpr r = s.gpr r := fun r hr => by rw [← hs₁]; simp [gpr_write, hr]
  obtain m₁ : s₁.mem = s.mem := by rw [← hs₁, mem_write]
  obtain sp₁ : s₁.sp = s.sp := by rw [← hs₁, sp_write]
  obtain rd₁ : s₁.rd = s.rd := by rw [← hs₁, rd_write]
  obtain wr₁ : s₁.wr = s.wr := by rw [← hs₁, wr_write]
  refine WP.ite (decide (n / 16 = 0)) (eval_zero x14₁ (by omega_arith)) (fun hz => ?_) (fun hz => ?_)
  · -- Fewer than 16 bytes.
    obtain lp : LoopPre s₁ S D n := ⟨by omega_arith, by rw [rd₁, wr₁]; exact h.rd, by rw [wr₁]; exact h.wr, h.disj⟩
    refine WP.mono (copy_ok s₁ (by rw [g₁ _ (by decide), h.x12]) (by rw [g₁ _ (by decide), h.x11])
      (by rw [g₁ _ (by decide), h.x13]) lp) fun s' ⟨m', g', sp', rd', wr'⟩ => ⟨by rw [m', m₁], fun r hr => ?_,
        by rw [sp', sp₁], by rw [rd', rd₁], by rw [wr', wr₁]⟩
    rw [g' r (fun hm => hr (by
        simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl <;> decide)),
      g₁ r (by intro e; subst e; simp at hr)]
  · have h16 : 16 ≤ n := by have := of_decide_eq_false hz; omega_arith
    obtain hk1 : 1 ≤ n / 16 := by omega_arith
    -- The last 16 bytes' addresses, in `x9` and `x10`.
    obtain ⟨s₂, run₂, x9₂, x10₂, g₂, m₂, sp₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
        [.add .x .x9 .x12 .x13, .subImm .x .x9 .x9 16, .add .x .x10 .x11 .x13, .subImm .x .x10 .x10 16] s₁ =
          some s₂ ∧ s₂.gpr .x9 = S + BitVec.ofNat 64 (n - 16) ∧ s₂.gpr .x10 = D + BitVec.ofNat 64 (n - 16) ∧
          (∀ r, r ≠ .x9 → r ≠ .x10 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.sp = s₁.sp ∧
          s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
      refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceLT, ite_true, Size.bits]; rfl,
        ?_, ?_, fun r h₁ h₂ => by simp [gpr_write, State.read, h₁, h₂], by simp [mem_write],
        by simp [sp_write], by simp [rd_write], by simp [wr_write]⟩
      · simp only [gpr_write, State.read, ite_true, BitVec.setWidth_eq, reduceCtorEq, ite_false]
        rw [g₁ _ (by decide), g₁ _ (by decide), h.x12, h.x13, Offset.add_ofNat_sub S h16]
      · simp only [gpr_write, State.read, ite_true, BitVec.setWidth_eq, reduceCtorEq, ite_false]
        rw [g₁ _ (by decide), g₁ _ (by decide), h.x11, h.x13, Offset.add_ofNat_sub D h16]
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    -- The whole blocks.
    obtain hb : BlocksPre s₂ S D (n / 16) :=
      ⟨by rw [g₂ _ (by decide) (by decide), g₁ _ (by decide), h.x12],
        by rw [g₂ _ (by decide) (by decide), g₁ _ (by decide), h.x11],
        by rw [g₂ _ (by decide) (by decide), x14₁], hk1, by omega_arith,
        by rw [rd₂, wr₂, rd₁, wr₁]; exact covers_prefix h.rd (by omega_arith),
        by rw [wr₂, wr₁]; exact covers_prefix h.wr (by omega_arith),
        (h.disj.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Region.sub_prefix (by omega_arith))⟩
    refine WP.seq (WP.mono (copyBlocks_wp s₂ hb) fun s₃ ⟨m₃, _, _, _, kp₃⟩ => ?_)
    -- The last 16 bytes.
    obtain ha : s₃.gpr .x9 + BitVec.ofNat 64 0 = S + BitVec.ofNat 64 (n - 16) := by
      rw [kp₃.gpr _ (by decide), x9₂, BitVec.add_zero]
    obtain hb : s₃.gpr .x10 + BitVec.ofNat 64 0 = D + BitVec.ofNat 64 (n - 16) := by
      rw [kp₃.gpr _ (by decide), x10₂, BitVec.add_zero]
    obtain hrd : InRegions (s₃.rd ++ s₃.wr) (S + BitVec.ofNat 64 (n - 16)) 16 := by
      rw [kp₃.rd, kp₃.wr, rd₂, wr₂, rd₁, wr₁]
      exact Proof.AesGcm.AArch64.in_off h.rd (by omega_arith) (by omega_arith)
    obtain hwr : InRegions s₃.wr (D + BitVec.ofNat 64 (n - 16)) 16 := by
      rw [kp₃.wr, wr₂, wr₁]
      exact Proof.AesGcm.AArch64.in_off h.wr (by omega_arith) (by omega_arith)
    refine WP.of_runBlock ⟨_, by
      simp only [↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, runBlock_cons,
        runStep_some, runBlock_nil, exec, addr, State.load, State.store, gpr_setV, mem_setV, rd_setV, wr_setV,
        v_setV_self, Option.bind_some, Option.map_some, ha, hb, hrd, hwr]
      rfl, ?_⟩
    have kept : bytesAt (writeBytes s.mem D (bytesAt s.mem S (16 * (n / 16)))) (S + BitVec.ofNat 64 (n - 16)) 16 =
        bytesAt s.mem (S + BitVec.ofNat 64 (n - 16)) 16 :=
      Proof.AesGcm.AArch64.bytesAt_frame
        (writeBytes_frame s.mem D _ (R := ⟨D, 16 * (n / 16)⟩) (by rw [length_bytesAt]; exact Region.contains_self _ _))
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (h.disj.sub_left (Offset.sub_base S (by omega_arith))).sub_right (Region.sub_prefix (by omega_arith)))
        (by omega_arith)
    refine ⟨?_, fun r hr => ?_, ?_, ?_, ?_⟩
    · dsimp only
      rw [write_read_bytes, m₃, m₂, m₁, kept, writeBytes_overlap s.mem D S (by omega_arith) (by omega_arith) h16 hn]
    · dsimp only
      rw [kp₃.gpr r (fun hm => hr (by
          simp only [copyRegs, List.mem_cons, List.not_mem_nil, or_false] at hm
          rcases hm with rfl | rfl | rfl | rfl | rfl <;> decide)),
        g₂ r (by intro e; subst e; simp at hr) (by intro e; subst e; simp at hr),
        g₁ r (by intro e; subst e; simp at hr)]
    · dsimp only; rw [sp_setV, kp₃.sp, sp₂, sp₁]
    · dsimp only; rw [kp₃.rd, rd₂, rd₁]
    · dsimp only; rw [kp₃.wr, wr₂, wr₁]

/-! ## Zero stores -/

/-- A zero 16-byte store, as bytes. -/
theorem write_zero16 (m : Mem) (a : Addr) :
    m.write a 16 (0 : BitVec 128) = writeBytes m a (List.replicate 16 0) := by
  rw [write_eq_writeBytes]
  congr 1

/-- The first `k` stores of `v0 = 0` to `B₂`: its first `16 k` bytes zeroed. -/
theorem zstores_ok {W : Addr} (k : Nat) (hk : k ≤ 8) (s : State) (hv : s.v .v0 = 0) (h19 : s.gpr .x19 = W)
    (hw : Covers [⟨W, 2560⟩] s.wr) :
    WP isa (.block ((List.range k).map fun i => .strq .v0 .x19 (Impl.AesGcm.AArch64.Stitch.b2O + 16 * i))) s
      fun s' => s'.mem = writeBytes s.mem (W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.b2O)
          (List.replicate (16 * k) 0) ∧
        s'.gpr = s.gpr ∧ s'.v = s.v ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  induction k with
  | zero => exact WP.block_nil ⟨by simp [writeBytes_nil], rfl, rfl, rfl, rfl, rfl⟩
  | succ k ih =>
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ih (by omega_arith)) fun t ⟨mt, gt, vt, spt, rdt, wrt⟩ => ?_
    obtain hout : InRegions t.wr (t.gpr .x19 + BitVec.ofNat 64 (Impl.AesGcm.AArch64.Stitch.b2O + 16 * k)) 16 := by
      rw [wrt, gt, h19]
      exact Proof.AesGcm.AArch64.in_off hw (by unfold Impl.AesGcm.AArch64.Stitch.b2O; omega_arith) (by decide)
    refine WP.of_runBlock ⟨_, by
      simp only [List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil,
        VG.Proof.Gcm.AArch64.Pmull.exec_strq (by unfold Impl.AesGcm.AArch64.Stitch.b2O; omega_arith)
          (by unfold Impl.AesGcm.AArch64.Stitch.b2O; omega_arith) hout]
      rfl, ?_⟩
    refine ⟨?_, gt, vt, spt, rdt, wrt⟩
    dsimp only
    rw [vt, hv, write_zero16, mt, gt, h19, ← Offset.add_add,
      show 16 * (k + 1) = 16 * k + 16 by omega_arith, ← List.replicate_append_replicate,
      show BitVec.ofNat 64 (16 * k) = BitVec.ofNat 64 (List.replicate (16 * k) (0 : Byte)).length by
        rw [List.length_replicate]]
    exact writeBytes_append s.mem _ _ _ (by simp only [List.length_replicate]; omega_arith)

/-! ## The lengths -/

theorem ceil16_bv {n : Nat} (hn : n < 2 ^ 60) :
    ((BitVec.ofNat 64 n + BitVec.ofNat 64 15) >>> 4) <<< 4 = BitVec.ofNat 64 (16 * ((n + 15) / 16)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (show n + 15 < 2 ^ 64 by omega_arith),
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show 16 * ((n + 15) / 16) < 2 ^ 64 by omega_arith)]
  rw [Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

/-- `shortLen`: the lengths and the text's address, from `x5`–`x7`. -/
theorem shortLen_ok {D : Addr} {n al : Nat} (s : State) (h7 : s.gpr .x7 = BitVec.ofNat 64 n)
    (h6 : s.gpr .x6 = D) (h5 : s.gpr .x5 = BitVec.ofNat 64 al) (hn : n < 2 ^ 60) :
    WP isa (.block Impl.AesGcm.AArch64.Stitch.shortLen) s fun s' =>
      s'.gpr .x26 = BitVec.ofNat 64 n ∧ s'.gpr .x27 = D ∧ s'.gpr .x24 = BitVec.ofNat 64 al ∧
        s'.gpr .x25 = BitVec.ofNat 64 (16 * ((n + 15) / 16)) ∧
        (∀ r, r ≠ .x24 → r ≠ .x25 → r ≠ .x26 → r ≠ .x27 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.v = s.v ∧
        s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.of_runBlock ⟨_, by arun [Impl.AesGcm.AArch64.Stitch.shortLen], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, h7]
  · simp [gpr_write, h6]
  · simp [gpr_write, h5]
  · simp only [gpr_write, h7, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, Size.bits]
    exact ceil16_bv hn
  · simp [gpr_write, h₁, h₂, h₃, h₄]
  all_goals simp [mem_write, sp_write, rd_write, wr_write, v_write]

/-- `zeroBufs`: `B₂` zeroed, then block `p − 1` of `B₁`, with `x25 = 16 c`. -/
theorem zeroBufs_ok {W : Addr} {c : Nat} (hc6 : c ≤ 6) (s : State) (h19 : s.gpr .x19 = W)
    (h25 : s.gpr .x25 = BitVec.ofNat 64 (16 * c)) (hw : Covers [⟨W, 2560⟩] s.wr) :
    WP isa (.block Impl.AesGcm.AArch64.Stitch.zeroBufs) s fun s' =>
      s'.mem = writeBytes (writeBytes s.mem (W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.b2O)
          (List.replicate 128 0)) (W + BitVec.ofNat 64 (864 - 16 * c)) (List.replicate 16 0) ∧
        (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold Impl.AesGcm.AArch64.Stitch.zeroBufs
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_cons_iff]
  refine ⟨_, VG.Proof.Gcm.AArch64.Pmull.exec_movi0 .v0 s, ?_⟩
  refine WP.mono (zstores_ok (W := W) 8 (by decide) _ (by simp [v_setV_self]) (by rw [gpr_setV, h19])
    (by rw [wr_setV]; exact hw)) fun t ⟨mt, gt, vt, spt, rdt, wrt⟩ => ?_
  -- `x9` at block `p − 1` of `B₁`.
  obtain ⟨t₁, run₁, x9₁, g₁, m₁, v₁, sp₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa (Impl.AesGcm.AArch64.Stitch.atP .x9
      Impl.AesGcm.AArch64.Stitch.b1O 0) t = some t₁ ∧ t₁.gpr .x9 = W + BitVec.ofNat 64 (864 - 16 * c) ∧
      (∀ r, r ≠ .x9 → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.v = t.v ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧
      t₁.wr = t.wr := by
    refine ⟨_, by
      simp only [Impl.AesGcm.AArch64.Stitch.atP, runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceLT,
        ite_true, Size.bits, Impl.AesGcm.AArch64.Stitch.b1O, Nat.reduceAdd, Nat.reduceMul]
      rfl, ?_, fun r hr => by simp [gpr_write, hr], by simp [mem_write], by simp [v_write], by simp [sp_write],
      by simp [rd_write], by simp [wr_write]⟩
    simp only [gpr_write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq]
    simp only [gt, gpr_setV, h19, h25]
    exact Offset.add_ofNat_sub W (by omega_arith)
  obtain hout : InRegions t₁.wr (t₁.gpr .x9 + BitVec.ofNat 64 0) 16 := by
    rw [wr₁, wrt, wr_setV, x9₁, BitVec.add_zero]
    exact Proof.AesGcm.AArch64.in_off hw (by omega_arith) (by decide)
  refine WP.of_runBlock ⟨t₁, run₁, ?_⟩
  refine WP.of_runBlock ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil,
      VG.Proof.Gcm.AArch64.Pmull.exec_strq (by decide) (by decide) hout]
    rfl, ?_⟩
  refine ⟨?_, fun r hr => ?_, by rw [sp₁, spt, sp_setV], by rw [rd₁, rdt, rd_setV], by rw [wr₁, wrt, wr_setV]⟩
  · dsimp only
    rw [v₁, vt, v_setV_self, write_zero16, x9₁, BitVec.add_zero, m₁, mt, mem_setV]
  · dsimp only
    rw [g₁ r hr, gt, gpr_setV]

/-- `x` at block `p + d − 1` of the buffer at `W + b`, with `x25 = 16 c`. -/
theorem atP_ok {W : Addr} {c : Nat} (r : Reg) (b d : Nat) (hb : b + 96 + 16 * d < 4096) (hc : 16 * c ≤ b + 96 + 16 * d)
    (s : State) (h19 : s.gpr .x19 = W) (h25 : s.gpr .x25 = BitVec.ofNat 64 (16 * c)) (hr' : r ≠ .x25) :
    ∃ t, runBlock isa (Impl.AesGcm.AArch64.Stitch.atP r b d) s = some t ∧
      t.gpr r = W + BitVec.ofNat 64 (b + 96 + 16 * d - 16 * c) ∧ (∀ q, q ≠ r → t.gpr q = s.gpr q) ∧
      t.mem = s.mem ∧ t.v = s.v ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  refine ⟨_, by
    simp only [Impl.AesGcm.AArch64.Stitch.atP, runBlock_cons, runStep_some, runBlock_nil, exec, hb, ite_true,
      Size.bits]
    rfl, ?_, fun q hq => by simp [gpr_write, hq], by simp [mem_write], by simp [v_write], by simp [sp_write],
    by simp [rd_write], by simp [wr_write]⟩
  simp only [gpr_write, State.read, ite_true, BitVec.setWidth_eq]
  rw [ite_eq_right (Ne.symm hr'), h25, h19]
  exact Offset.add_ofNat_sub W hc

/-- `aadIn`: the `al ≤ 16` bytes of additional data at `x4` copied to block
`p − 1` of `B₂`. -/
theorem aadIn_ok {W A : Addr} {c al : Nat} (hc6 : c ≤ 6) (s : State) (h19 : s.gpr .x19 = W)
    (h25 : s.gpr .x25 = BitVec.ofNat 64 (16 * c)) (hw : Covers [⟨W, 2560⟩] s.wr)
    (h4 : s.gpr .x4 = A) (h24 : s.gpr .x24 = BitVec.ofNat 64 al) (hal16 : al ≤ 16)
    (hAr : Covers [⟨A, al⟩] (s.rd ++ s.wr)) (hd : (⟨A, al⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 (992 - 16 * c), al⟩) :
    WP isa Impl.AesGcm.AArch64.Stitch.aadIn s fun s' =>
      s'.mem = writeBytes s.mem (W + BitVec.ofNat 64 (992 - 16 * c)) (bytesAt s.mem A al) ∧
        (∀ r, r ∉ [.x11, .x12, .x13, .x14, .x15] → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧
        s'.wr = s.wr := by
  unfold Impl.AesGcm.AArch64.Stitch.aadIn
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  obtain ⟨t₁, run₁, x12₁, g₁, m₁, sp₁, rd₁, wr₁⟩ : ∃ t, runBlock isa [mov .x12 .x4] s = some t ∧ t.gpr .x12 = A ∧
      (∀ r, r ≠ .x12 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
    refine ⟨_, by arun [], ?_⟩
    exact ⟨by simp [gpr_write, h4], fun r hr => by simp [gpr_write, hr], rfl, rfl, rfl, rfl⟩
  refine WP.of_runBlock ⟨t₁, run₁, ?_⟩
  obtain ⟨t₂, run₂, x11₂, g₂, m₂, -, sp₂, rd₂, wr₂⟩ := atP_ok (c := c) .x11 Impl.AesGcm.AArch64.Stitch.b2O 0
    (by decide) (by unfold Impl.AesGcm.AArch64.Stitch.b2O; omega_arith) t₁ (by rw [g₁ _ (by decide), h19])
    (by rw [g₁ _ (by decide), h25]) (by decide)
  refine WP.of_runBlock ⟨t₂, run₂, ?_⟩
  obtain ⟨t₃, run₃, x13₃, g₃, m₃', sp₃', rd₃', wr₃'⟩ : ∃ t, runBlock isa [mov .x13 .x24] t₂ = some t ∧
      t.gpr .x13 = BitVec.ofNat 64 al ∧ (∀ r, r ≠ .x13 → t.gpr r = t₂.gpr r) ∧ t.mem = t₂.mem ∧ t.sp = t₂.sp ∧
      t.rd = t₂.rd ∧ t.wr = t₂.wr := by
    refine ⟨_, by arun [], ?_⟩
    exact ⟨by simp [gpr_write, g₂ .x24 (by decide), g₁ .x24 (by decide), h24], fun r hr => by simp [gpr_write, hr],
      rfl, rfl, rfl, rfl⟩
  refine WP.of_runBlock ⟨t₃, run₃, ?_⟩
  obtain m₃ : t₃.mem = s.mem := by rw [m₃', m₂, m₁]
  obtain rd₃ : t₃.rd = s.rd := by rw [rd₃', rd₂, rd₁]
  obtain wr₃ : t₃.wr = s.wr := by rw [wr₃', wr₂, wr₁]
  obtain sp₃ : t₃.sp = s.sp := by rw [sp₃', sp₂, sp₁]
  refine WP.mono (copy_ok t₃ (S := A) (D := W + BitVec.ofNat 64 (992 - 16 * c)) (n := al)
    (by rw [g₃ _ (by decide), g₂ _ (by decide), x12₁])
    (by rw [g₃ _ (by decide), x11₂]; rfl) x13₃
    ⟨by omega_arith, by rw [rd₃, wr₃]; exact hAr, by
      rw [wr₃]; exact Proof.AesGcm.AArch64.covers_off hw (by omega_arith) (by decide), hd⟩)
    fun s' ⟨hm, hg, hsp, hrd, hwr⟩ => ⟨by rw [hm, m₃], fun r hr => ?_, by rw [hsp, sp₃], by rw [hrd, rd₃],
      by rw [hwr, wr₃]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [hg r (by simp [loopRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2]), g₃ r hr.2.2.1, g₂ r hr.1,
    g₁ r hr.2.1]

/-- `ctToB2`: the `c` blocks at block `p` of `B₁` copied to block `p` of `B₂`, then
16 zero bytes from `n` bytes on. -/
theorem ctToB2_ok {W : Addr} {c n : Nat} (hc1 : 1 ≤ c) (hc6 : c ≤ 6) (hn : n ≤ 16 * c) (s : State)
    (h19 : s.gpr .x19 = W) (h25 : s.gpr .x25 = BitVec.ofNat 64 (16 * c)) (h26 : s.gpr .x26 = BitVec.ofNat 64 n)
    (hw : Covers [⟨W, 2560⟩] s.wr) :
    WP isa Impl.AesGcm.AArch64.Stitch.ctToB2 s fun s' =>
      s'.mem = writeBytes (writeBytes s.mem (W + BitVec.ofNat 64 (1008 - 16 * c))
          (bytesAt s.mem (W + BitVec.ofNat 64 (880 - 16 * c)) (16 * c)))
          (W + BitVec.ofNat 64 (1008 - 16 * c + n)) (List.replicate 16 0) ∧
        (∀ r, r ∉ [.x9, .x11, .x12, .x13, .x14, .x15] → s'.gpr r = s.gpr r) ∧
        s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold Impl.AesGcm.AArch64.Stitch.ctToB2
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  obtain ⟨t₁, run₁, x12₁, g₁, m₁, v₁, sp₁, rd₁, wr₁⟩ := atP_ok (c := c) .x12 Impl.AesGcm.AArch64.Stitch.b1O 1
    (by unfold Impl.AesGcm.AArch64.Stitch.b1O; omega_arith) (by unfold Impl.AesGcm.AArch64.Stitch.b1O; omega_arith) s h19 h25
    (by decide)
  refine WP.of_runBlock ⟨t₁, run₁, ?_⟩
  obtain ⟨t₂, run₂, x11₂, g₂, m₂, v₂, sp₂, rd₂, wr₂⟩ := atP_ok (c := c) .x11 Impl.AesGcm.AArch64.Stitch.b2O 1
    (by unfold Impl.AesGcm.AArch64.Stitch.b2O; omega_arith) (by unfold Impl.AesGcm.AArch64.Stitch.b2O; omega_arith) t₁
    (by rw [g₁ _ (by decide), h19]) (by rw [g₁ _ (by decide), h25]) (by decide)
  refine WP.of_runBlock ⟨t₂, run₂, ?_⟩
  refine WP.of_runBlock ⟨t₂.write .x .x14 (t₂.read .x .x25 >>> 4), by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceLT, ite_true, Size.bits], ?_⟩
  generalize ht₃ : t₂.write .x .x14 (t₂.read .x .x25 >>> 4) = t₃
  obtain x14₃ : t₃.gpr .x14 = BitVec.ofNat 64 c := by
    rw [← ht₃, gpr_write_self, State.read]
    simp only [Size.bits, BitVec.setWidth_eq]
    rw [g₂ _ (by decide), g₁ _ (by decide), h25, ofNat_lsr4 (show 16 * c < 2 ^ 64 by omega_arith),
      show 16 * c / 16 = c by omega_arith]
  obtain g₃ : ∀ r, r ≠ .x14 → t₃.gpr r = t₂.gpr r := fun r hr => by rw [← ht₃]; simp [gpr_write, hr]
  obtain m₃ : t₃.mem = s.mem := by rw [← ht₃, mem_write, m₂, m₁]
  obtain sp₃ : t₃.sp = s.sp := by rw [← ht₃, sp_write, sp₂, sp₁]
  obtain rd₃ : t₃.rd = s.rd := by rw [← ht₃, rd_write, rd₂, rd₁]
  obtain wr₃ : t₃.wr = s.wr := by rw [← ht₃, wr_write, wr₂, wr₁]
  -- The `c` blocks.
  refine WP.seq (WP.ite false (by rw [eval_zero x14₃ (by omega_arith)]; simp; omega_arith) (fun h => by cases h) fun _ => ?_)
  obtain hb : BlocksPre t₃ (W + BitVec.ofNat 64 (880 - 16 * c)) (W + BitVec.ofNat 64 (1008 - 16 * c)) c :=
    ⟨by rw [g₃ _ (by decide), g₂ _ (by decide), x12₁]; rfl, by rw [g₃ _ (by decide), x11₂]; rfl, x14₃, hc1,
      by omega_arith, by rw [rd₃, wr₃]; exact Proof.AesGcm.AArch64.covers_left (Proof.AesGcm.AArch64.covers_off hw
        (by omega_arith) (by decide)),
      by rw [wr₃]; exact Proof.AesGcm.AArch64.covers_off hw (by omega_arith) (by decide),
      Offset.disjoint W (.inl (by omega_arith)) (by omega_arith) (by omega_arith)⟩
  refine WP.mono (copyBlocks_wp t₃ hb) fun t₄ ⟨m₄, _, _, _, kp₄⟩ => ?_
  rw [WP.block_append_iff]
  obtain kg : ∀ r ∈ [Reg.x19, .x25, .x26], t₄.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [kp₄.gpr _ (by decide), g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide)]
  obtain ⟨t₅, run₅, x9₅, g₅, m₅, v₅, sp₅, rd₅, wr₅⟩ := atP_ok (c := c) .x9 Impl.AesGcm.AArch64.Stitch.b2O 1
    (by unfold Impl.AesGcm.AArch64.Stitch.b2O; omega_arith) (by unfold Impl.AesGcm.AArch64.Stitch.b2O; omega_arith) t₄
    (by rw [kg _ (by simp), h19]) (by rw [kg _ (by simp), h25]) (by decide)
  refine WP.of_runBlock ⟨t₅, run₅, ?_⟩
  obtain x26₅ : t₅.gpr .x26 = BitVec.ofNat 64 n := by rw [g₅ _ (by decide), kg _ (by simp), h26]
  generalize ht₆ : (t₅.write .x .x9 (t₅.read .x .x9 + t₅.read .x .x26)).setV .v0 0 = t₆
  obtain x9₆ : t₆.gpr .x9 = W + BitVec.ofNat 64 (1008 - 16 * c + n) := by
    rw [← ht₆, gpr_setV, gpr_write_self, State.read, State.read]
    simp only [Size.bits, BitVec.setWidth_eq]
    rw [x9₅, x26₅, BitVec.add_assoc, ← BitVec.ofNat_add]
    unfold Impl.AesGcm.AArch64.Stitch.b2O
    rfl
  obtain hout : InRegions t₆.wr (t₆.gpr .x9 + BitVec.ofNat 64 0) 16 := by
    rw [x9₆, BitVec.add_zero, ← ht₆, wr_setV, wr_write, wr₅, kp₄.wr, wr₃]
    exact Proof.AesGcm.AArch64.in_off hw (by omega_arith) (by decide)
  refine WP.of_runBlock ⟨_, by
    rw [runBlock_cons]
    simp only [exec, Size.bits]
    rw [runStep_some, runBlock_cons, VG.Proof.Gcm.AArch64.Pmull.exec_movi0, runStep_some, runBlock_cons, ht₆,
      VG.Proof.Gcm.AArch64.Pmull.exec_strq (by decide) (by decide) hout, runStep_some, runBlock_nil], ?_⟩
  refine ⟨?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · dsimp only
    rw [x9₆, BitVec.add_zero, ← ht₆, v_setV_self, write_zero16, mem_setV, mem_write, m₅, m₄, m₃]
  · dsimp only
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h9, h11, h12, h13, h14, h15⟩ := hr
    rw [← ht₆, gpr_setV]
    simp only [gpr_write, h9, ite_false]
    rw [g₅ r h9, kp₄.gpr r (by simp [Proof.AesGcm.AArch64.Gather.copyRegs, h11, h12, h13, h14, h15]),
      g₃ r h14, g₂ r h11, g₁ r h12]
  · dsimp only; rw [← ht₆, sp_setV, sp_write, sp₅, kp₄.sp, sp₃]
  · dsimp only; rw [← ht₆, rd_setV, rd_write, rd₅, kp₄.rd, rd₃]
  · dsimp only; rw [← ht₆, wr_setV, wr_write, wr₅, kp₄.wr, wr₃]

/-- `ctToB2_ok` for no blocks. -/
theorem ctToB2_ok0 {W : Addr} {c n : Nat} (hc1 : c = 0) (_hc6 : c ≤ 6) (hn : n ≤ 16 * c) (s : State)
    (h19 : s.gpr .x19 = W) (h25 : s.gpr .x25 = BitVec.ofNat 64 (16 * c)) (h26 : s.gpr .x26 = BitVec.ofNat 64 n)
    (hw : Covers [⟨W, 2560⟩] s.wr) :
    WP isa Impl.AesGcm.AArch64.Stitch.ctToB2 s fun s' =>
      s'.mem = writeBytes (writeBytes s.mem (W + BitVec.ofNat 64 (1008 - 16 * c))
          (bytesAt s.mem (W + BitVec.ofNat 64 (880 - 16 * c)) (16 * c)))
          (W + BitVec.ofNat 64 (1008 - 16 * c + n)) (List.replicate 16 0) ∧
        (∀ r, r ∉ [.x9, .x11, .x12, .x13, .x14, .x15] → s'.gpr r = s.gpr r) ∧
        s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold Impl.AesGcm.AArch64.Stitch.ctToB2
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  obtain ⟨t₁, run₁, x12₁, g₁, m₁, v₁, sp₁, rd₁, wr₁⟩ := atP_ok (c := c) .x12 Impl.AesGcm.AArch64.Stitch.b1O 1
    (by unfold Impl.AesGcm.AArch64.Stitch.b1O; omega_arith) (by unfold Impl.AesGcm.AArch64.Stitch.b1O; omega_arith) s h19 h25
    (by decide)
  refine WP.of_runBlock ⟨t₁, run₁, ?_⟩
  obtain ⟨t₂, run₂, x11₂, g₂, m₂, v₂, sp₂, rd₂, wr₂⟩ := atP_ok (c := c) .x11 Impl.AesGcm.AArch64.Stitch.b2O 1
    (by unfold Impl.AesGcm.AArch64.Stitch.b2O; omega_arith) (by unfold Impl.AesGcm.AArch64.Stitch.b2O; omega_arith) t₁
    (by rw [g₁ _ (by decide), h19]) (by rw [g₁ _ (by decide), h25]) (by decide)
  refine WP.of_runBlock ⟨t₂, run₂, ?_⟩
  refine WP.of_runBlock ⟨t₂.write .x .x14 (t₂.read .x .x25 >>> 4), by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceLT, ite_true, Size.bits], ?_⟩
  generalize ht₃ : t₂.write .x .x14 (t₂.read .x .x25 >>> 4) = t₃
  obtain x14₃ : t₃.gpr .x14 = BitVec.ofNat 64 c := by
    rw [← ht₃, gpr_write_self, State.read]
    simp only [Size.bits, BitVec.setWidth_eq]
    rw [g₂ _ (by decide), g₁ _ (by decide), h25, ofNat_lsr4 (show 16 * c < 2 ^ 64 by omega_arith),
      show 16 * c / 16 = c by omega_arith]
  obtain g₃ : ∀ r, r ≠ .x14 → t₃.gpr r = t₂.gpr r := fun r hr => by rw [← ht₃]; simp [gpr_write, hr]
  obtain m₃ : t₃.mem = s.mem := by rw [← ht₃, mem_write, m₂, m₁]
  obtain sp₃ : t₃.sp = s.sp := by rw [← ht₃, sp_write, sp₂, sp₁]
  obtain rd₃ : t₃.rd = s.rd := by rw [← ht₃, rd_write, rd₂, rd₁]
  obtain wr₃ : t₃.wr = s.wr := by rw [← ht₃, wr_write, wr₂, wr₁]
  -- No blocks.
  refine WP.seq (WP.ite true (by rw [eval_zero x14₃ (by omega_arith)]; simp [hc1]) (fun _ => WP.block_nil ?_)
    fun h => by cases h)
  obtain m₄ : t₃.mem = writeBytes s.mem (W + BitVec.ofNat 64 (1008 - 16 * c))
      (bytesAt s.mem (W + BitVec.ofNat 64 (880 - 16 * c)) (16 * c)) := by
    rw [m₃, hc1, show 16 * 0 = 0 from rfl, show bytesAt s.mem (W + BitVec.ofNat 64 (880 - 0)) 0 = [] from rfl,
      writeBytes_nil]
  generalize t₃ = t₄ at m₄ g₃ sp₃ rd₃ wr₃
  rw [WP.block_append_iff]
  obtain kg : ∀ r ∈ [Reg.x19, .x25, .x26], t₄.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide)]
  obtain ⟨t₅, run₅, x9₅, g₅, m₅, v₅, sp₅, rd₅, wr₅⟩ := atP_ok (c := c) .x9 Impl.AesGcm.AArch64.Stitch.b2O 1
    (by unfold Impl.AesGcm.AArch64.Stitch.b2O; omega_arith) (by unfold Impl.AesGcm.AArch64.Stitch.b2O; omega_arith) t₄
    (by rw [kg _ (by simp), h19]) (by rw [kg _ (by simp), h25]) (by decide)
  refine WP.of_runBlock ⟨t₅, run₅, ?_⟩
  obtain x26₅ : t₅.gpr .x26 = BitVec.ofNat 64 n := by rw [g₅ _ (by decide), kg _ (by simp), h26]
  generalize ht₆ : (t₅.write .x .x9 (t₅.read .x .x9 + t₅.read .x .x26)).setV .v0 0 = t₆
  obtain x9₆ : t₆.gpr .x9 = W + BitVec.ofNat 64 (1008 - 16 * c + n) := by
    rw [← ht₆, gpr_setV, gpr_write_self, State.read, State.read]
    simp only [Size.bits, BitVec.setWidth_eq]
    rw [x9₅, x26₅, BitVec.add_assoc, ← BitVec.ofNat_add]
    unfold Impl.AesGcm.AArch64.Stitch.b2O
    rfl
  obtain hout : InRegions t₆.wr (t₆.gpr .x9 + BitVec.ofNat 64 0) 16 := by
    rw [x9₆, BitVec.add_zero, ← ht₆, wr_setV, wr_write, wr₅, wr₃]
    exact Proof.AesGcm.AArch64.in_off hw (by omega_arith) (by decide)
  refine WP.of_runBlock ⟨_, by
    rw [runBlock_cons]
    simp only [exec, Size.bits]
    rw [runStep_some, runBlock_cons, VG.Proof.Gcm.AArch64.Pmull.exec_movi0, runStep_some, runBlock_cons, ht₆,
      VG.Proof.Gcm.AArch64.Pmull.exec_strq (by decide) (by decide) hout, runStep_some, runBlock_nil], ?_⟩
  refine ⟨?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · dsimp only
    rw [x9₆, BitVec.add_zero, ← ht₆, v_setV_self, write_zero16, mem_setV, mem_write, m₅, m₄]
  · dsimp only
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h9, h11, h12, h13, h14, h15⟩ := hr
    rw [← ht₆, gpr_setV]
    simp only [gpr_write, h9, ite_false]
    rw [g₅ r h9, g₃ r h14, g₂ r h11, g₁ r h12]
  · dsimp only; rw [← ht₆, sp_setV, sp_write, sp₅, sp₃]
  · dsimp only; rw [← ht₆, rd_setV, rd_write, rd₅, rd₃]
  · dsimp only; rw [← ht₆, wr_setV, wr_write, wr₅, wr₃]

/-- `ctToB2_ok`, for any number of blocks. -/
theorem ctToB2_ok' {W : Addr} {c n : Nat} (hc6 : c ≤ 6) (hn : n ≤ 16 * c) (s : State)
    (h19 : s.gpr .x19 = W) (h25 : s.gpr .x25 = BitVec.ofNat 64 (16 * c)) (h26 : s.gpr .x26 = BitVec.ofNat 64 n)
    (hw : Covers [⟨W, 2560⟩] s.wr) :
    WP isa Impl.AesGcm.AArch64.Stitch.ctToB2 s fun s' =>
      s'.mem = writeBytes (writeBytes s.mem (W + BitVec.ofNat 64 (1008 - 16 * c))
          (bytesAt s.mem (W + BitVec.ofNat 64 (880 - 16 * c)) (16 * c)))
          (W + BitVec.ofNat 64 (1008 - 16 * c + n)) (List.replicate 16 0) ∧
        (∀ r, r ∉ [.x9, .x11, .x12, .x13, .x14, .x15] → s'.gpr r = s.gpr r) ∧
        s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rcases Nat.eq_zero_or_pos c with hc | hc
  · exact ctToB2_ok0 hc hc6 hn s h19 h25 h26 hw
  · exact ctToB2_ok hc hc6 hn s h19 h25 h26 hw

/-! ## The eight AES states stored -/

/-- Byte `t < 16` of a 16-byte write at `b`, at `b + t`. -/
theorem write16_at (m : Mem) (b : Addr) (v : BitVec 128) {t : Nat} (ht : t < 16) :
    m.write b 16 v (b + BitVec.ofNat 64 t) = vbyte v t := by
  simp only [Mem.write, Mem.sub_ofNat_toNat b (show t < 2 ^ 64 by omega_arith), ht, ite_true, vbyte]

/-- `stores 0` with `x9 = B`: byte `t` of block `j` of `B`, byte `t` of `breg j`. -/
theorem storesB_ok {B : Addr} (u : State) (hx9 : u.gpr .x9 = B) (hw : Covers [⟨B, 128⟩] u.wr) :
    WP isa (.block (Impl.Gcm.AArch64.Stitch.stores 0)) u fun u' =>
      (∀ j < 8, ∀ t < 16, u'.mem (B + BitVec.ofNat 64 (16 * j + t)) =
        vbyte (u.v (Impl.Gcm.AArch64.Stitch.breg j)) t) ∧
      Frame [⟨B, 128⟩] u.mem u'.mem ∧ u'.gpr = u.gpr ∧ u'.v = u.v ∧ u'.sp = u.sp ∧ u'.rd = u.rd ∧
        u'.wr = u.wr := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun k u' =>
      (∀ j < k, ∀ t < 16, u'.mem (B + BitVec.ofNat 64 (16 * j + t)) =
        vbyte (u.v (Impl.Gcm.AArch64.Stitch.breg j)) t) ∧
      Frame [⟨B, 128⟩] u.mem u'.mem ∧ u'.gpr = u.gpr ∧ u'.v = u.v ∧ u'.sp = u.sp ∧ u'.rd = u.rd ∧
        u'.wr = u.wr)
    (fun k u₁ hk ⟨d₁, f₁, g₁, v₁, sp₁, rd₁, wr₁⟩ => ?_) 8 (Nat.le_refl _) u
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, rfl, rfl, rfl, rfl, rfl⟩) fun u' h => h
  obtain ha : u₁.gpr .x9 + BitVec.ofNat 64 (0 + 16 * k) = B + BitVec.ofNat 64 (16 * k) := by
    rw [g₁, hx9, Nat.zero_add]
  obtain hout : InRegions u₁.wr (u₁.gpr .x9 + BitVec.ofNat 64 (0 + 16 * k)) 16 := by
    rw [ha, wr₁]; exact Proof.AesGcm.AArch64.in_off hw (by omega_arith) (by decide)
  rw [WP.block_cons_iff]
  refine ⟨_, VG.Proof.Gcm.AArch64.Pmull.exec_strq (by omega_arith) (by omega_arith) hout, WP.block_nil ?_⟩
  refine ⟨fun j hj t ht => ?_, ?_, g₁, v₁, sp₁, rd₁, wr₁⟩
  · dsimp only
    rw [ha]
    by_cases hjk : j = k
    · subst hjk
      rw [← Offset.add_add B (16 * j) t, write16_at _ _ _ ht, v₁]
    · rw [Mem.write_apply, d₁ j (by omega_arith) t ht]
      rw [Offset.add_sub_add_left, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show 16 * j + t < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (show 16 * k < 2 ^ 64 by omega_arith)]
      omega_arith
  · dsimp only
    rw [ha]
    exact f₁.trans ((Frame.refl [⟨B, 128⟩] u₁.mem).write (List.mem_singleton_self _) _
      (Offset.contains_base B (by omega_arith) (by omega_arith)))

/-! ## The number of rounds -/

/-- `byRounds f` runs `f R`, from a state that differs only in `x13` and `x14`. -/
theorem byRoundsG_ok {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) {f : Nat → Prog isa} {Q : State → Prop} {s : State}
    (hx22 : s.gpr .x22 = BitVec.ofNat 64 R)
    (hf : ∀ t : State, (∀ r, r ≠ .x13 → r ≠ .x14 → t.gpr r = s.gpr r) → t.mem = s.mem → t.v = s.v →
      t.sp = s.sp → t.rd = s.rd → t.wr = s.wr → WP isa (f R) t Q) :
    WP isa (Impl.Gcm.AArch64.Stitch.byRounds f) s Q := by
  rw [Impl.Gcm.AArch64.Stitch.byRounds, WP.seq_iff, WP.block_cons_iff]
  refine ⟨_, exec_subImm_x (imm := 10) (by decide), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_subImm_x (imm := 12) (by decide), WP.block_nil ?_⟩
  generalize ht : (s.write .x .x13 (s.read .x .x22 - BitVec.ofNat 64 10)).write .x .x14
      ((s.write .x .x13 (s.read .x .x22 - BitVec.ofNat 64 10)).read .x .x22 - BitVec.ofNat 64 12) = t
  obtain gt : ∀ r, r ≠ .x13 → r ≠ .x14 → t.gpr r = s.gpr r := fun r h13 h14 => by
    rw [← ht, gpr_write_of_ne _ _ _ h14, gpr_write_of_ne _ _ _ h13]
  obtain mt : t.mem = s.mem := by rw [← ht, mem_write, mem_write]
  obtain vt : t.v = s.v := by rw [← ht, v_write, v_write]
  obtain spt : t.sp = s.sp := by rw [← ht, sp_write, sp_write]
  obtain rdt : t.rd = s.rd := by rw [← ht, rd_write, rd_write]
  obtain wrt : t.wr = s.wr := by rw [← ht, wr_write, wr_write]
  obtain e13 : t.gpr .x13 = BitVec.ofNat 64 (R - 10) := by
    rw [← ht]
    simp only [gpr_write_of_ne _ _ _ (show Reg.x13 ≠ Reg.x14 by decide), gpr_write_self, State.read,
      BitVec.setWidth_eq, hx22, Size.bits]
    rw [Offset.ofNat_sub_ofNat (by omega_arith)]
  obtain hft := hf t gt mt vt spt rdt wrt
  refine WP.ite _ (eval_zero e13 (by omega_arith)) (fun h => ?_) (fun h => ?_)
  · have h10 : R = 10 := by simp only [decide_eq_true_eq] at h; omega_arith
    rw [h10] at hft; exact hft
  · have hge : 12 ≤ R := by simp only [decide_eq_false_iff_not] at h; omega_arith
    obtain e14 : t.gpr .x14 = BitVec.ofNat 64 (R - 12) := by
      rw [← ht]
      simp only [gpr_write_self, State.read, BitVec.setWidth_eq,
        gpr_write_of_ne _ _ _ (show Reg.x22 ≠ Reg.x13 by decide), hx22, Size.bits]
      rw [Offset.ofNat_sub_ofNat (by omega_arith)]
    refine WP.ite _ (eval_zero e14 (by omega_arith)) (fun h' => ?_) (fun h' => ?_)
    · have h12 : R = 12 := by simp only [decide_eq_true_eq] at h'; omega_arith
      rw [h12] at hft; exact hft
    · have h14 : R = 14 := by simp only [decide_eq_false_iff_not] at h'; omega_arith
      rw [h14] at hft; exact hft

end VG.Proof.AesGcm.AArch64.Stitch

end

end

/-!
# AES-GCM on AArch64, short records: one pass of the counter mode

Untrusted: everything here is checked by Lean. `byRounds shortAes`
(`Impl.AesGcm.AArch64.Stitch`), from `x9 = B` and the counter in `w10`
(`APre`), leaves at `B` the eight blocks there XORed with the keystream of
the counter blocks `k … k + 7` (`shortAesB_ok`): `aesPart_ok`, then
`storesB_ok`, for the number of rounds (`byRoundsG_ok`).
-/

@[expose] public section

local notation "ofVDwords" => VG.Proof.Gcm.Clmul.ofVDwords

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Stitch

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Proof.Gcm.AArch64.Stitch (APre APost aesPart_ok sch cbk kp cbA c0)
open VG.Proof.Aes.AArch64 (keyStream)

/-- `APre` from a state that differs in `x13` and `x14` only. -/
theorem APre.of_x1314 {R o k : Nat} {s t : State} (h : APre R o k s)
    (hg : ∀ r, r ≠ .x13 → r ≠ .x14 → t.gpr r = s.gpr r) (hm : t.mem = s.mem) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) : APre R o k t where
  rounds := h.rounds
  o_le := h.o_le
  keys := fun r hr => by
    rw [hrd, hwr, kp, hg _ (by decide) (by decide)]; exact h.keys r hr
  ctr := by rw [hrd, hwr, cbA, hg _ (by decide) (by decide)]; exact h.ctr
  data := fun j hj => by rw [hrd, hwr, hg _ (by decide) (by decide)]; exact h.data j hj
  x10 := by
    simp only [State.read, hg _ (by decide : Reg.x10 ≠ .x13) (by decide)]
    have := h.x10
    simp only [State.read, c0, cbk, cbA] at this ⊢
    rw [hm, hg _ (by decide : Reg.x20 ≠ .x13) (by decide)]
    exact this

/-- `byRounds shortAes` from `x9 = B`: the blocks at `B` XORed with the keystream. -/
theorem shortAesB_ok {R k : Nat} {B : Addr} (s : State) (hp : APre R 0 k s)
    (hx22 : s.gpr .x22 = BitVec.ofNat 64 R) (hx9 : s.gpr .x9 = B) (hw : Covers [⟨B, 128⟩] s.wr) :
    WP isa (Impl.Gcm.AArch64.Stitch.byRounds Impl.AesGcm.AArch64.Stitch.shortAes) s fun s' =>
      (∀ j < 8, ∀ t < 16, s'.mem (B + BitVec.ofNat 64 (16 * j + t)) =
        keyStream R (sch R s) (cbk s) (16 * (k + j) + t) ^^^ s.mem (B + BitVec.ofNat 64 (16 * j + t))) ∧
      Frame [⟨B, 128⟩] s.mem s'.mem ∧ (∀ r, r ∉ [Reg.x10, .x12, .x13, .x14] → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.v Impl.Gcm.AArch64.Stitch.Y = s.v Impl.Gcm.AArch64.Stitch.Y := by
  refine byRoundsG_ok hp.rounds hx22 fun t gt mt vt spt rdt wrt => ?_
  have hpt := APre.of_x1314 hp gt mt rdt wrt
  unfold Impl.AesGcm.AArch64.Stitch.shortAes
  rw [WP.block_append_iff]
  refine WP.mono (aesPart_ok hpt (by decide)) fun u hu => ?_
  have x9u : u.gpr .x9 = B := by rw [hu.fr.gpr _ (by decide), gt _ (by decide) (by decide), hx9]
  refine WP.mono (storesB_ok u x9u (by rw [hu.fr.wr, wrt]; exact hw)) fun u' ⟨e, f, g, vv, sp, rd, wr⟩ => ?_
  have hsch : sch R t = sch R s := by simp only [sch, kp, mt, gt _ (by decide : Reg.x21 ≠ .x13) (by decide)]
  have hcbk : cbk t = cbk s := by simp only [cbk, cbA, mt, gt _ (by decide : Reg.x20 ≠ .x13) (by decide)]
  refine ⟨fun j hj tt htt => ?_, ?_, fun r hr => ?_, by rw [sp, hu.fr.sp, spt], by rw [rd, hu.fr.rd, rdt],
    by rw [wr, hu.fr.wr, wrt], by rw [vv, hu.fr.v _ (by decide), vt]⟩
  · rw [e j hj tt htt, hu.out j hj tt htt, hsch, hcbk, mt, gt _ (by decide) (by decide), hx9, Nat.zero_add,
      Offset.add_add]
  · rw [← mt, ← hu.fr.mem]; exact f
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g, hu.fr.gpr r (by simp [hr.1, hr.2.1]), gt r hr.2.2.1 hr.2.2.2]

/-! ## One pass of GHASH -/

open VG.Proof.Gcm.AArch64.Stitch (TblOk Gh8Ok GhIn ghPart_ok gh8V blkV tblV ghV gh8V_congr kpack) in
open VG.Proof.Gcm.AArch64.Pmull (ext8 rev64b_read) in
/-- `shortGh`: GHASH from zero of the eight blocks of `B₂`, with the table of `H`, in `v16` as loaded. -/
theorem shortGh_ok {W : Addr} {H : Spec.Gcm.Block} (gh : Gh8Ok) (s : State) (h19 : s.gpr .x19 = W)
    (ht : TblOk s.mem W H) (hr : Covers [⟨W, 2560⟩] (s.rd ++ s.wr)) :
    WP isa (.block Impl.AesGcm.AArch64.Stitch.shortGh) s fun s' =>
      s'.v Impl.Gcm.AArch64.Stitch.Y =
        ext8 (Spec.Gcm.ghashFrom H 0 ((List.range 8).map fun j =>
          Spec.Gcm.blockAt s.mem (W + BitVec.ofNat 64 (Impl.AesGcm.AArch64.Stitch.b2O + 16 * j))))
          (Spec.Gcm.ghashFrom H 0 ((List.range 8).map fun j =>
          Spec.Gcm.blockAt s.mem (W + BitVec.ofNat 64 (Impl.AesGcm.AArch64.Stitch.b2O + 16 * j)))) ∧
      (∀ r, r ≠ .x9 → r ≠ .x12 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧
        s'.wr = s.wr := by
  unfold Impl.AesGcm.AArch64.Stitch.shortGh
  rw [WP.block_append_iff, WP.block_cons_iff]
  refine ⟨_, VG.Proof.Gcm.AArch64.Pmull.exec_movz_x (imm := 0xc200) (hw := 3) (by decide) _, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, VG.Proof.Gcm.AArch64.Pmull.exec_dup_d2 _ .x12 _, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, VG.Proof.Gcm.AArch64.Pmull.exec_movi0 _ _, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := Impl.AesGcm.AArch64.Stitch.b2O) (by decide), WP.block_nil ?_⟩
  have hx9 : ∀ j, ((((s.write .x .x12 ((0xc200 : BitVec 16).setWidth 64 <<< (16 * 3))).setV
      Impl.Gcm.AArch64.Stitch.C (ofVDwords ((s.write .x .x12 ((0xc200 : BitVec 16).setWidth 64 <<< (16 * 3))).gpr .x12)
        ((s.write .x .x12 ((0xc200 : BitVec 16).setWidth 64 <<< (16 * 3))).gpr .x12))).setV
      Impl.Gcm.AArch64.Stitch.Y 0).write .x .x9
      ((((s.write .x .x12 ((0xc200 : BitVec 16).setWidth 64 <<< (16 * 3))).setV
      Impl.Gcm.AArch64.Stitch.C (ofVDwords ((s.write .x .x12 ((0xc200 : BitVec 16).setWidth 64 <<< (16 * 3))).gpr .x12)
        ((s.write .x .x12 ((0xc200 : BitVec 16).setWidth 64 <<< (16 * 3))).gpr .x12))).setV
      Impl.Gcm.AArch64.Stitch.Y 0).read .x .x19 + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.b2O)).gpr .x9 +
        BitVec.ofNat 64 (16 * j) = W + BitVec.ofNat 64 (Impl.AesGcm.AArch64.Stitch.b2O + 16 * j) := fun j => by
    simp only [gpr_write_self, State.read, gpr_setV, gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x12 by decide),
      BitVec.setWidth_eq, Size.bits, h19, Offset.add_add]
  refine WP.mono (ghPart_ok _ ⟨fun j hj => ?_, fun k hk1 hk8 => ?_, fun p hp => ?_⟩ ?_) fun s' ⟨e, o⟩ => ?_
  · simp only [rd_write, wr_write, rd_setV, wr_setV] at *
    rw [hx9 j]
    exact Proof.AesGcm.AArch64.in_off hr (by unfold Impl.AesGcm.AArch64.Stitch.b2O; omega_using [hj]) (by decide)
  · simp only [rd_write, wr_write, rd_setV, wr_setV, gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x9 by decide),
      gpr_setV, gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x12 by decide), h19]
    exact Proof.AesGcm.AArch64.in_off hr (by unfold Impl.Gcm.AArch64.Stitch.sOff Impl.Gcm.AArch64.Stitch.tbl; omega_using [hk8])
      (by decide)
  · simp only [rd_write, wr_write, rd_setV, wr_setV, gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x9 by decide),
      gpr_setV, gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x12 by decide), h19]
    exact Proof.AesGcm.AArch64.in_off hr (by unfold Impl.Gcm.AArch64.Stitch.kOff Impl.Gcm.AArch64.Stitch.tbl; omega_using [hp])
      (by decide)
  · simp only [v_write, v_setV_of_ne _ _ (show Impl.Gcm.AArch64.Stitch.C ≠ Impl.Gcm.AArch64.Stitch.Y by decide),
      v_setV_self, gpr_write_self]
    rfl
  have hm₁ : ∀ x : Addr, ((((s.write .x .x12 ((0xc200 : BitVec 16).setWidth 64 <<< (16 * 3))).setV
      Impl.Gcm.AArch64.Stitch.C (ofVDwords ((s.write .x .x12 ((0xc200 : BitVec 16).setWidth 64 <<< (16 * 3))).gpr .x12)
        ((s.write .x .x12 ((0xc200 : BitVec 16).setWidth 64 <<< (16 * 3))).gpr .x12))).setV
      Impl.Gcm.AArch64.Stitch.Y 0).write .x .x9 x).mem = s.mem := fun _ => by
    simp only [mem_write, mem_setV]
  refine ⟨?_, fun r h9 h12 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [e, gh8V_congr (y' := ext8 0 0)
      (b' := fun j => ext8 (Spec.Gcm.blockAt s.mem (W + BitVec.ofNat 64 (Impl.AesGcm.AArch64.Stitch.b2O + 16 * j)))
        (Spec.Gcm.blockAt s.mem (W + BitVec.ofNat 64 (Impl.AesGcm.AArch64.Stitch.b2O + 16 * j))))
      (S' := fun k => ext8 (VG.Proof.Gcm.AArch64.Pmull.pp H k) (VG.Proof.Gcm.AArch64.Pmull.pp H k))
      (KP' := fun p => kpack H (Impl.Gcm.AArch64.Stitch.pk p) (Impl.Gcm.AArch64.Stitch.pl p))
      (by simp only [v_write, v_setV_self]; rfl)
      (fun j _ => by rw [blkV, hx9 j, hm₁, rev64b_read])
      (fun k hk1 hk8 => by
        rw [tblV, hm₁]
        simp only [gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x9 by decide), gpr_setV,
          gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x12 by decide), h19]
        rw [VG.Proof.Gcm.AArch64.Stitch.read_eq_readW]
        exact ht.sw k hk1 hk8)
      (fun p hp => by
        rw [tblV, hm₁]
        simp only [gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x9 by decide), gpr_setV,
          gpr_write_of_ne _ _ _ (show Reg.x19 ≠ Reg.x12 by decide), h19]
        rw [VG.Proof.Gcm.AArch64.Stitch.read_eq_readW]
        exact ht.key p hp), gh]
  · rw [o.gpr]
    simp only [gpr_write_of_ne _ _ _ h9, gpr_setV, gpr_write_of_ne _ _ _ h12]
  · rw [o.mem]; simp only [mem_write, mem_setV]
  · rw [o.sp]; simp only [sp_write, sp_setV]
  · rw [o.rd]; simp only [rd_write, rd_setV]
  · rw [o.wr]; simp only [wr_write, wr_setV]

/-! ## The lengths block -/

/-- `lensB`: the lengths block of `al` and `n` bytes, at block 7 of `B₂`. -/
theorem lensB_ok {W : Addr} {al n : Nat} (s : State) (h19 : s.gpr .x19 = W) (hr : Covers [⟨W, 2560⟩] s.wr)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 al) (h26 : s.gpr .x26 = BitVec.ofNat 64 n)
    (hal' : al < 2 ^ 64) (hn : n < 2 ^ 64) :
    WP isa (.block Impl.AesGcm.AArch64.Stitch.lensB) s fun s' =>
      Spec.Aes.bytesAt s'.mem (W + BitVec.ofNat 64 1008) 16 = Proof.Gcm.lensBlock al n ∧
      Frame [⟨W + BitVec.ofNat 64 1008, 16⟩] s.mem s'.mem ∧
      Others [.x9, .x10] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.v = s.v := by
  have w₁ : InRegions s.wr (W + BitVec.ofNat 64 1008) 8 := Proof.AesGcm.AArch64.in_off hr (by decide) (by decide)
  have w₂ : InRegions s.wr (W + BitVec.ofNat 64 1016) 8 := Proof.AesGcm.AArch64.in_off hr (by decide) (by decide)
  obtain ⟨s', run, m', og, sp', rd', wr', v'⟩ : ∃ s', runBlock isa Impl.AesGcm.AArch64.Stitch.lensB s = some s' ∧
      s'.mem = (s.mem.writeW (W + BitVec.ofNat 64 1008) (AArch64.rev64 (BitVec.ofNat 64 al <<< 3))).writeW
        (W + BitVec.ofNat 64 1008 + BitVec.ofNat 64 8) (AArch64.rev64 (BitVec.ofNat 64 n <<< 3)) ∧
      Others [.x9, .x10] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.v = s.v := by
    refine ⟨_, by arun [Impl.AesGcm.AArch64.Stitch.lensB, Impl.AesGcm.AArch64.Stitch.b2O, h19, w₁, w₂], ?_⟩
    refine ⟨?_, by others_tac, rfl, rfl, rfl, rfl⟩
    simp only [RegUpd.mem_write, Mem.writeW, BitVec.setWidth_eq, Proof.AesGcm.AArch64.add_ofNat_assoc, gpr_write,
      ite_true, ite_false, reduceCtorEq, h24, h26]
  refine WP.of_runBlock ⟨s', run, ?_, ?_, og, sp', rd', wr', v'⟩
  · rw [m', Proof.Cmac.bytesAt_store2, Proof.AesGcm.AArch64.le8_lens, Proof.AesGcm.AArch64.le8_lens,
      Proof.AesGcm.AArch64.toNat_ofNat_of_lt hal', Proof.AesGcm.AArch64.toNat_ofNat_of_lt hn]
    rfl
  · rw [m']; exact Proof.Cmac.frame_store2 _ _ _

/-! ## The tag -/

theorem byteRev64_xor (a b : BitVec 64) : byteRev64 (a ^^^ b) = byteRev64 a ^^^ byteRev64 b := by
  -- byte by byte; the outer `^^^` is of `BitVec 64`, whose two widths `simp` does not find
  simp only [byteRev64, BitVec.extractLsb'_xor, BitVec.xor_append (w := 8 + 8 + 8 + 8 + 8 + 8 + 8) (v := 8),
    BitVec.xor_append]

open VG.Proof.Gcm.AArch64.Pmull (vdwords vdword_xor vdword_rev64b) in
theorem rev64b_xor (a b : BitVec 128) :
    VRevOp.eval .rev64b (a ^^^ b) = VRevOp.eval .rev64b a ^^^ VRevOp.eval .rev64b b := by
  rw [vdwords (VRevOp.eval .rev64b (a ^^^ b)), vdword_rev64b _ (by decide), vdword_rev64b _ (by decide),
    vdwords (VRevOp.eval .rev64b a ^^^ VRevOp.eval .rev64b b), vdword_xor, vdword_xor, vdword_xor, vdword_xor,
    vdword_rev64b _ (by decide), vdword_rev64b _ (by decide), vdword_rev64b _ (by decide),
    vdword_rev64b _ (by decide)]
  rw [show AArch64.rev64 = byteRev64 from rfl, byteRev64_xor, byteRev64_xor]

open VG.Proof.Gcm.AArch64.Pmull (ext8 ext8_eq vdword_xor) in
theorem ext8_xor (a b : BitVec 128) : ext8 (a ^^^ b) (a ^^^ b) = ext8 a a ^^^ ext8 b b := by
  rw [ext8_eq, ext8_eq, ext8_eq, vdword_xor, vdword_xor, BitVec.xor_append]

open VG.Proof.Gcm.AArch64.Pmull (ext8 ext8_ext8 rev64b_rev64b rev64b_read blockAt_store exec_rev64b exec_ldrq
  exec_eor exec_strq) in
/-- `shortTagAt o`: GHASH (in `v16`, as loaded) XORed with block `p − 1` of `B₁`, at `W + o`. -/
theorem shortTagAt_ok {W : Addr} {c : Nat} {g : Spec.Gcm.Block} {o : Nat} (ho : o = 0 ∨ o = 112)
    (hc6 : c ≤ 6) (s : State) (h19 : s.gpr .x19 = W) (h25 : s.gpr .x25 = BitVec.ofNat 64 (16 * c))
    (hY : s.v Impl.Gcm.AArch64.Stitch.Y = ext8 g g) (hr : Covers [⟨W, 2560⟩] s.wr) :
    WP isa (.block (Impl.AesGcm.AArch64.Stitch.shortTagAt o)) s fun s' =>
      Spec.Gcm.blockAt s'.mem (W + BitVec.ofNat 64 o) =
        g ^^^ Spec.Gcm.blockAt s.mem (W + BitVec.ofNat 64 (864 - 16 * c)) ∧
      Frame [⟨W + BitVec.ofNat 64 o, 16⟩] s.mem s'.mem ∧ (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold Impl.AesGcm.AArch64.Stitch.shortTagAt
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_cons_iff]
  refine ⟨_, exec_rev64b _ _ _, WP.block_nil ?_⟩
  obtain ⟨t₁, run₁, x9₁, g₁, m₁, v₁, sp₁, rd₁, wr₁⟩ := atP_ok (c := c) .x9 Impl.AesGcm.AArch64.Stitch.b1O 0
    (by unfold Impl.AesGcm.AArch64.Stitch.b1O; omega_using []) (by unfold Impl.AesGcm.AArch64.Stitch.b1O; omega_using [hc6])
    (s.setV Impl.Gcm.AArch64.Stitch.Y (VRevOp.eval .rev64b (s.v Impl.Gcm.AArch64.Stitch.Y)))
    (by rw [gpr_setV, h19]) (by rw [gpr_setV, h25]) (by decide)
  refine WP.of_runBlock ⟨t₁, run₁, ?_⟩
  have hin : InRegions (t₁.rd ++ t₁.wr) (t₁.gpr .x9 + BitVec.ofNat 64 0) 16 := by
    rw [rd₁, wr₁, x9₁, BitVec.add_zero, rd_setV, wr_setV]
    exact Proof.AesGcm.AArch64.in_left (Proof.AesGcm.AArch64.in_off hr
      (by unfold Impl.AesGcm.AArch64.Stitch.b1O; omega_using []) (by decide))
  rw [WP.block_cons_iff]
  refine ⟨_, exec_ldrq (by decide) (by decide) hin, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_eor _ _ _ _, ?_⟩
  have hx19 : t₁.gpr .x19 = W := by rw [g₁ _ (by decide), gpr_setV, h19]
  have hout : InRegions ((t₁.setV .v0 (t₁.mem.read (t₁.gpr .x9 + BitVec.ofNat 64 0) 16)).setV
      Impl.Gcm.AArch64.Stitch.Y ((t₁.setV .v0 (t₁.mem.read (t₁.gpr .x9 + BitVec.ofNat 64 0) 16)).v
        Impl.Gcm.AArch64.Stitch.Y ^^^ (t₁.setV .v0 (t₁.mem.read (t₁.gpr .x9 + BitVec.ofNat 64 0) 16)).v .v0)).wr
      (((t₁.setV .v0 (t₁.mem.read (t₁.gpr .x9 + BitVec.ofNat 64 0) 16)).setV
      Impl.Gcm.AArch64.Stitch.Y ((t₁.setV .v0 (t₁.mem.read (t₁.gpr .x9 + BitVec.ofNat 64 0) 16)).v
        Impl.Gcm.AArch64.Stitch.Y ^^^ (t₁.setV .v0 (t₁.mem.read (t₁.gpr .x9 + BitVec.ofNat 64 0) 16)).v .v0)).gpr .x19 +
        BitVec.ofNat 64 o) 16 := by
    rw [wr_setV, wr_setV, gpr_setV, gpr_setV, hx19, wr₁, wr_setV]
    exact Proof.AesGcm.AArch64.in_off hr (by rcases ho with rfl | rfl <;> decide) (by decide)
  rw [WP.block_cons_iff]
  refine ⟨_, exec_strq (by rcases ho with rfl | rfl <;> decide) (by rcases ho with rfl | rfl <;> decide) hout,
    WP.block_nil ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · dsimp only
    rw [gpr_setV, gpr_setV, hx19, v_setV_self, v_setV_of_ne _ _ (by decide), v_setV_self, v₁, v_setV_self,
      mem_setV, mem_setV, m₁, mem_setV, x9₁, BitVec.add_zero, hY,
      show Impl.AesGcm.AArch64.Stitch.b1O + 96 + 16 * 0 - 16 * c = 864 - 16 * c by
        unfold Impl.AesGcm.AArch64.Stitch.b1O; omega_using [],
      ← rev64b_rev64b (s.mem.read (W + BitVec.ofNat 64 (864 - 16 * c)) 16), ← rev64b_xor, blockAt_store,
      ext8_xor, ext8_ext8, rev64b_read, ext8_ext8]
  · dsimp only
    rw [gpr_setV, gpr_setV, hx19, mem_setV, mem_setV, m₁, mem_setV]
    exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · dsimp only
    rw [gpr_setV, gpr_setV, g₁ r hr, gpr_setV]
  · dsimp only; rw [sp_setV, sp_setV, sp₁, sp_setV]
  · dsimp only; rw [rd_setV, rd_setV, rd₁, rd_setV]
  · dsimp only; rw [wr_setV, wr_setV, wr₁, wr_setV]

/-! ## The counter -/

/-- `shortCtr`: `w10 = c₀ + c − 7` (the counter block at `St + 48`'s counter), and `x9 = B₁`. -/
theorem shortCtr_ok {W St : Addr} {c : Nat} (hc6 : c ≤ 6) (s : State) (h19 : s.gpr .x19 = W)
    (h20 : s.gpr .x20 = St) (h25 : s.gpr .x25 = BitVec.ofNat 64 (16 * c))
    (hq : InRegions (s.rd ++ s.wr) (St + BitVec.ofNat 64 60) 4) :
    WP isa (.block Impl.AesGcm.AArch64.Stitch.shortCtr) s fun s' =>
      s'.read .w .x10 = (Spec.Gcm.blockAt s.mem (St + BitVec.ofNat 64 48)).extractLsb' 0 32 +
        BitVec.ofNat 32 (2 ^ 32 + c - 7) ∧
      s'.gpr .x9 = W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.b1O ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.v = s.v ∧ s'.sp = s.sp ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hq' : InRegions (s.rd ++ s.wr) (s.gpr .x20 + BitVec.ofNat 64 60) 4 := by rw [h20]; exact hq
  refine WP.of_runBlock ⟨_, by
    simp only [Impl.AesGcm.AArch64.Stitch.shortCtr, runBlock_cons]
    rw [exec_ldr_w (by decide) hq', runStep_some]
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceLT, ite_true, Size.bits]
    rfl, ?_⟩
  refine ⟨?_, ?_, fun r h9 h10 => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [State.read, gpr_write, ite_true, reduceCtorEq, ite_false, Size.bits, h25, mem_write,
      Proof.Aes.AArch64.Aese.sw32, BitVec.setWidth_eq]
    rw [h20, show St + BitVec.ofNat 64 60 = St + BitVec.ofNat 64 48 + BitVec.ofNat 64 12 by rw [Offset.add_add],
      Proof.Aes.AArch64.icb_lo, Proof.AesGcm.AArch64.Gather.ofNat_lsr4 (show 16 * c < 2 ^ 64 by omega_using [hc6]),
      show 16 * c / 16 = c by omega_using []]
    generalize (Spec.Gcm.blockAt s.mem (St + BitVec.ofNat 64 48)).extractLsb' 0 32 = x
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_using []
  · simp [gpr_write, State.read, h19]
  · simp [gpr_write, h9, h10]
  all_goals simp [mem_write, v_write, sp_write, rd_write, wr_write]

end VG.Proof.AesGcm.AArch64.Stitch

end

end

/-!
# AES-GCM on AArch64, short records: what the buffers hold

Untrusted: everything here is checked by Lean. After one `aesPart` over
`B₁` from the counter `c₀ + n − 7`, its blocks from `p = 7 − n` on are the
text XORed with counter mode from `inc₃₂(J₀)` (`b1_gctr`, the counter
having wrapped around: `ksByte_wrap`), and block `p − 1`, zero before, is
`CIPH_K(J₀)` (`b1_j0`). `B₂` holds zero blocks, the additional data and the
text each padded, and the lengths block (`b2_layout`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Stitch

open VG VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros ofBytes toBytes inc32 aesWith gctr)
open VG.Proof.Gcm (xorKs ksByte)
open VG.Proof.Aes.AArch64 (keyStream)

/-- The keystream of `keyStream` is counter mode's. -/
theorem keyStream_ks (R : Nat) (w : List Byte) (icb : Block) (i : Nat) :
    keyStream R w icb i = ksByte (aesWith R w) icb i := by
  have ht : i % 16 < 16 := Nat.mod_lt _ (by decide)
  rw [keyStream, ksByte, aesWith, Proof.Aes.toBytes_ofBytes (by simp) ht, Proof.Aes.getD_eq _ ht,
    List.getD_eq_getElem?_getD, Vector.getElem?_toList, Vector.getElem?_eq_getElem ht, Option.getD_some]
  rfl

/-- `B₁`'s blocks from `7 − c` on, `n` bytes of `P` XORed with the keystream
of `aesPart` from `2³² + c − 7` blocks on: counter mode from `icb`. -/
theorem b1_gctr {m₀ m : Mem} {B : Addr} {R c n : Nat} {w : List Byte} {icb : Block} {P : List Byte}
    (hn : n ≤ 16 * c) (hc6 : c ≤ 6)
    (hks : ∀ j < 8, ∀ t < 16, m (B + BitVec.ofNat 64 (16 * j + t)) =
      keyStream R w icb (16 * (2 ^ 32 + c - 7 + j) + t) ^^^ m₀ (B + BitVec.ofNat 64 (16 * j + t)))
    (hP : bytesAt m₀ (B + BitVec.ofNat 64 (16 * (7 - c))) n = P) :
    bytesAt m (B + BitVec.ofNat 64 (16 * (7 - c))) n = gctr (aesWith R w) icb P := by
  have hPl : P.length = n := by rw [← hP, Proof.AesCcm.length_bytesAt]
  rw [Proof.Gcm.gctr_eq]
  refine Proof.Gcm.list_ext (by rw [Proof.AesCcm.length_bytesAt, Proof.Gcm.length_xorKs, hPl]) fun k hk => ?_
  rw [Proof.AesCcm.length_bytesAt] at hk
  rw [Proof.Gcm.getD_xorKs _ _ _ _ (by rw [hPl]; exact hk), Nat.zero_add, ← hP, Proof.Gcm.getD_bytesAt' _ _ hk,
    Proof.Gcm.getD_bytesAt' _ _ hk, Offset.add_add,
    show 16 * (7 - c) + k = 16 * (7 - c + k / 16) + k % 16 by omega_using [],
    hks _ (by omega_using [hn, hc6, hk]) _ (Nat.mod_lt _ (by decide)), keyStream_ks,
    show 16 * (2 ^ 32 + c - 7 + (7 - c + k / 16)) + k % 16 = 16 * 2 ^ 32 + k by omega_using [hc6], Proof.Gcm.ksByte_wrap,
    BitVec.xor_comm]

/-- Block `6 − c` of `B₁`, zero before: `CIPH(J)`, for the keystream from `inc₃₂(J)`. -/
theorem b1_j0 {m₀ m : Mem} {B : Addr} {R c : Nat} {w : List Byte} {J : Block} (hc6 : c ≤ 6)
    (hks : ∀ j < 8, ∀ t < 16, m (B + BitVec.ofNat 64 (16 * j + t)) =
      keyStream R w (inc32 J) (16 * (2 ^ 32 + c - 7 + j) + t) ^^^ m₀ (B + BitVec.ofNat 64 (16 * j + t)))
    (hz : bytesAt m₀ (B + BitVec.ofNat 64 (16 * (6 - c))) 16 = zeros 16) :
    blockAt m (B + BitVec.ofNat 64 (16 * (6 - c))) = aesWith R w J := by
  refine Proof.Aes.block_ext fun t ht => ?_
  have h0 : m₀ (B + BitVec.ofNat 64 (16 * (6 - c) + t)) = 0 := by
    have := congrArg (·.getD t 0) hz
    simp only [Proof.Gcm.getD_bytesAt' _ _ ht, Offset.add_add] at this
    rw [this]
    simp only [zeros, List.getD_eq_getElem?_getD, List.getElem?_replicate, ht, ite_true, Option.getD_some]
  rw [Proof.Aes.toBytes_blockAt _ _ ht, Offset.add_add, hks _ (by omega_using []) _ ht, h0,
    show ∀ x : Byte, x ^^^ 0 = x from fun _ => BitVec.xor_zero,
    keyStream_ks, show 2 ^ 32 + c - 7 + (6 - c) = 2 ^ 32 - 1 by omega_using [hc6], Proof.Gcm.ksByte_pred _ _ ht]

/-- What `B₂` (at `G`) holds: zeroed, then, after writes elsewhere, the `16 c`
bytes `Q` at block `7 − c`, 16 zeros after their first `n`, the additional
data `A` at block `6 − c` and the lengths block at block 7. -/
theorem b2_layout {G : Addr} {c n : Nat} {Q A lens : List Byte} {mZ mY mL : Mem} {rs : List Region}
    (hc6 : c ≤ 6) (hn : n ≤ 16 * c) (hn' : 16 * c ≤ n + 16) (hQ : Q.length = 16 * c)
    (hA : A.length ≤ 16)
    (hZ : bytesAt mZ G 128 = zeros 128) (fY : Frame rs mZ mY) (hrs : ∀ r ∈ rs, (⟨G, 128⟩ : Region).Disjoint r)
    (fL : Frame [⟨G + BitVec.ofNat 64 112, 16⟩]
      (writeBytes (writeBytes (writeBytes mY (G + BitVec.ofNat 64 (112 - 16 * c)) Q)
        (G + BitVec.ofNat 64 (112 - 16 * c + n)) (List.replicate 16 0)) (G + BitVec.ofNat 64 (96 - 16 * c)) A) mL)
    (hL : bytesAt mL (G + BitVec.ofNat 64 112) 16 = lens) :
    bytesAt mL G 128 =
      zeros (16 * (6 - c)) ++ A ++ zeros (16 - A.length) ++ Q.take n ++ zeros (16 * c - n) ++ lens := by
  have Z : ∀ a b, zeros a ++ zeros b = zeros (a + b) := fun a b => List.replicate_append_replicate
  have lz : ∀ a, (zeros a).length = a := fun a => List.length_replicate
  -- The first `k` bytes, and those after the first `k`, of a list split there.
  have tk : ∀ (l₁ l₂ : List Byte) (k : Nat), l₁.length = k → (l₁ ++ l₂).take k = l₁ :=
    fun _ _ _ h => List.take_left' h
  have dk : ∀ (l₁ l₂ : List Byte) (k : Nat), l₁.length = k → (l₁ ++ l₂).drop k = l₂ :=
    fun _ _ _ h => List.drop_left' h
  have wr : ∀ (m : Mem) (o : Nat) (xs : List Byte), o + xs.length ≤ 128 → ∀ (l₁ l₂ l₃ : List Byte),
      bytesAt m G 128 = l₁ ++ l₂ ++ l₃ → l₁.length = o → l₂.length = xs.length →
      bytesAt (writeBytes m (G + BitVec.ofNat 64 o) xs) G 128 = l₁ ++ xs ++ l₃ := by
    intro m o xs h l₁ l₂ l₃ e h₁ h₂
    rw [Proof.AesCcm.bytesAt_writeBytes_at _ _ _ h (by decide), e,
      show l₁ ++ l₂ ++ l₃ = l₁ ++ (l₂ ++ l₃) from List.append_assoc .., tk _ _ _ h₁,
      show o + xs.length = (l₁ ++ l₂).length by simp [h₁, h₂], ← List.append_assoc l₁ l₂ l₃, dk _ _ _ rfl]
  -- `B₂` before the writes.
  have L0 : bytesAt mY G 128 = zeros (112 - 16 * c) ++ zeros (16 * c) ++ zeros 16 := by
    rw [bytesAt_frame fY hrs (by decide), hZ, Z, Z]; congr 1; omega_using [hc6]
  have L1 := wr _ (112 - 16 * c) Q (by rw [hQ]; omega_using [hc6]) _ _ _ L0 (lz _) (by rw [lz, hQ])
  rw [← List.take_append_drop n Q,
    show zeros 16 = zeros (16 - (16 * c - n)) ++ zeros (16 * c - n) by rw [Z]; congr 1; omega_using [hn']] at L1
  have L2 := wr _ (112 - 16 * c + n) (List.replicate 16 0) (by simp; omega_using [hc6, hn])
    (zeros (112 - 16 * c) ++ Q.take n) (Q.drop n ++ zeros (16 - (16 * c - n))) (zeros (16 * c - n))
    (by rw [L1]; simp only [List.append_assoc]) (by simp [lz]; omega_using [hn, hQ]) (by simp [lz]; omega_using [hn', hQ])
  have L2' : bytesAt (writeBytes (writeBytes mY (G + BitVec.ofNat 64 (112 - 16 * c)) (List.take n Q ++ List.drop n Q))
      (G + BitVec.ofNat 64 (112 - 16 * c + n)) (List.replicate 16 0)) G 128 =
      zeros (96 - 16 * c) ++ zeros A.length ++
        (zeros (16 - A.length) ++ Q.take n ++ zeros 16 ++ zeros (16 * c - n)) := by
    rw [L2, show zeros (112 - 16 * c) = zeros (96 - 16 * c) ++ zeros A.length ++ zeros (16 - A.length) by
      rw [Z, Z]; congr 1; omega_using [hc6, hA]]
    simp only [List.append_assoc]; rfl
  have L3 := wr _ (96 - 16 * c) A (by omega_using [hA]) _ _ _ L2' (lz _) (lz _)
  rw [List.take_append_drop] at L3
  have e128 : (128 : Nat) = 112 + 16 := rfl
  rw [e128, bytesAt_add, hL, bytesAt_frame fL (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.base_disjoint G (Nat.le_refl _) (by decide))
      (by decide), Proof.AesCcm.bytesAt_prefix _ _ (show 112 ≤ 128 by decide), L3]
  simp only [List.append_assoc]
  rw [show zeros 16 ++ zeros (16 * c - n) = zeros (16 * c - n) ++ zeros 16 by rw [Z, Z, Nat.add_comm],
    show 16 * (6 - c) = 96 - 16 * c by omega_using []]
  simp only [← List.append_assoc]
  rw [tk _ _ _ (by simp only [List.length_append, lz, List.length_take, hQ]; omega_using [hc6, hA])]

end VG.Proof.AesGcm.AArch64.Stitch

end

end

/-!
# AES-GCM on AArch64, short records: `sealShort`

Untrusted: everything here is checked by Lean. `sealShort`
(`Impl/AesGcm/AArch64/Stitch.lean`) seals a record of 17 to 96 bytes as
`seal` does (`sealShort_ok`): `J₀` and the first counter block as `front`
leaves them (`j012_ok`, `initState_ok`), the table of keys (`TbFor`), one
`aesPart` over `B₁` and one `ghPart` over `B₂` (`Gh8Ok`), whose zero first
blocks leave GHASH from zero as it is (`ghashFrom_zeros`), and the counter
block `2³² − 1` steps after `inc₃₂(J₀)`, `J₀` (`repeat_inc32_pred`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.WriteBytes
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks zeros padLen ofBytes inc32 ctxH ctxCiph gctr)
open VG.Proof.Gcm.AArch64.Stitch (TblOk Gh8Ok)

/-- What `tb` must do, from a state of the path for TLS records: write the
table of keys of the context's hash subkey (`Stitch.TblPost`). -/
def TbFor (tb : List Instr) (w : Nat) (s : State) : Prop :=
  ∀ u : State, Env (s.gpr .x0) (stackArg s w + BitVec.ofNat 64 16) (stackArg s w) s.sp u →
    u.rd = s.rd → u.wr = s.wr →
    Frame [workR (stackArg s w), ⟨s.gpr .x6, (s.gpr .x7).toNat⟩] s.mem u.mem →
    KeyAt (Spec.Gcm.ctxH s.mem (s.gpr .x0)) u.mem (stackArg s w) →
    WP isa (.block tb) u (Stitch.TblPost (stackArg s w) (Spec.Gcm.ctxH s.mem (s.gpr .x0)) u)

/-- `TbFor` without the key `H'` at `W + hO`, which `pwTbl` does not read:
what the paths that never compute `H'` (`sealShort`) need of `tb`. -/
def TbForP (tb : List Instr) (w : Nat) (s : State) : Prop :=
  ∀ u : State, Env (s.gpr .x0) (stackArg s w + BitVec.ofNat 64 16) (stackArg s w) s.sp u →
    u.rd = s.rd → u.wr = s.wr →
    Frame [workR (stackArg s w), ⟨s.gpr .x6, (s.gpr .x7).toNat⟩] s.mem u.mem →
    WP isa (.block tb) u (Stitch.TblPost (stackArg s w) (Spec.Gcm.ctxH s.mem (s.gpr .x0)) u)

theorem TbForP.tbFor {tb : List Instr} {w : Nat} {s : State} (h : TbForP tb w s) : TbFor tb w s :=
  fun u he hrd hwr hf _ => h u he hrd hwr hf

theorem ofNat_lsr {n k : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> k = BitVec.ofNat 64 (n / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn)]

/-- `shortThr`: `x9 = ⌊(n + 31) / 128⌋`, zero exactly when `n ≤ shortMax`. -/
theorem shortThr_ok {n : Nat} (s : State) (h7 : s.gpr .x7 = BitVec.ofNat 64 n) (hn : n + 31 < 2 ^ 64) :
    WP isa (.block Impl.AesGcm.AArch64.Stitch.shortThr) s fun s' =>
      s'.gpr .x9 = BitVec.ofNat 64 ((n + 31) / 128) ∧ Regs [.x9, .x10] s s' := by
  refine WP.of_runBlock ⟨_, by arun [Impl.AesGcm.AArch64.Stitch.shortThr, Impl.AesGcm.AArch64.Stitch.shortMax], ?_⟩
  refine ⟨?_, by others_tac, rfl, rfl, rfl, rfl⟩
  simp only [gpr_write, ite_true, h7, State.read, BitVec.setWidth_eq, Size.bits]
  rw [BitVec.ofNat_add_ofNat, ofNat_lsr hn]

/-- `shortMin`: `x9 = ⌊(n + 15) / 32⌋`, zero exactly when `n ≤ 16`. -/
theorem shortMin_ok {n : Nat} (s : State) (h7 : s.gpr .x7 = BitVec.ofNat 64 n) (hn : n + 15 < 2 ^ 64) :
    WP isa (.block Impl.AesGcm.AArch64.Stitch.shortMin) s fun s' =>
      s'.gpr .x9 = BitVec.ofNat 64 ((n + 15) / 32) ∧ Regs [.x9, .x10] s s' := by
  refine WP.of_runBlock ⟨_, by arun [Impl.AesGcm.AArch64.Stitch.shortMin], ?_⟩
  refine ⟨?_, by others_tac, rfl, rfl, rfl, rfl⟩
  simp only [gpr_write, ite_true, h7, State.read, BitVec.setWidth_eq, Size.bits]
  rw [BitVec.ofNat_add_ofNat, ofNat_lsr hn]

/-- A region apart from the 2560 bytes of the working space, neither wrapping
around, is at most `2⁶⁴ − 2560` bytes long. -/
theorem len_of_disjoint {D W : Addr} {n : Nat} (hd : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hD : D.toNat + n ≤ 2 ^ 64) (hW : W.toNat + 2560 ≤ 2 ^ 64) : n + 2560 ≤ 2 ^ 64 := by
  refine Classical.byContradiction fun h => ?_
  by_cases hDW : D.toNat ≤ W.toNat
  · refine hd W ?_ ?_
    · simp only [Region.Contains, BitVec.toNat_sub]; omega_using [hW, h, hDW]
    · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using []
  · refine hd D ?_ ?_
    · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [h]
    · simp only [Region.Contains, BitVec.toNat_sub]; omega_using [hD, h, hDW]

open VG.Proof.Gcm.AArch64.Stitch (TblOk) in
/-- The table, outside a frame apart from it. -/
theorem tblOk_frame {m m' : Mem} {W : Addr} {H : Block} {rs : List Region} (h : TblOk m W H) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (Stitch.tblR W).Disjoint r) : TblOk m' W H where
  sw k h₁ h₂ := by
    rw [hf.readW (r := ⟨W + BitVec.ofNat 64 (Impl.Gcm.AArch64.Stitch.sOff k), 16⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Offset.sub W (by unfold Impl.Gcm.AArch64.Stitch.sOff Impl.Gcm.AArch64.Stitch.tbl; omega_using [])
        (by unfold Impl.Gcm.AArch64.Stitch.sOff Impl.Gcm.AArch64.Stitch.tbl; omega_using [h₂]))) (by decide)]
    exact h.sw k h₁ h₂
  key p hp := by
    rw [hf.readW (r := ⟨W + BitVec.ofNat 64 (Impl.Gcm.AArch64.Stitch.kOff p), 16⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Offset.sub W (by unfold Impl.Gcm.AArch64.Stitch.kOff Impl.Gcm.AArch64.Stitch.tbl; omega_using [])
        (by unfold Impl.Gcm.AArch64.Stitch.kOff Impl.Gcm.AArch64.Stitch.tbl; omega_using [hp]))) (by decide)]
    exact h.key p hp

/-- `sealShort`, from the entry of `seal`, for a record of 17 to 96 bytes. -/
theorem sealShort_ok (gh : Gh8Ok) {tb : List Instr} {w : Nat} {extra extraW : List Region} {s s₁ : State}
    (hs : sealPreXW w extra s extraW) (htb : TbForP tb w s)
    (h₁ : SealEntry w s s₁) (hx : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₁.gpr r = s.gpr r)
    (h12 : (s.gpr .x3).toNat = 12) (h16 : (s.gpr .x5).toNat ≤ 16)
    (hlo : 17 ≤ (s.gpr .x7).toNat) (hhi : (s.gpr .x7).toNat ≤ 96) :
    WP isa (Impl.AesGcm.AArch64.Stitch.sealShort tb) s₁ fun s' => GprAbi s s' ∧ sealAArch64.post s s' := by
  obtain ⟨he₁, x22₁, x23₁, x24₁, x26₁, x27₁, x28₁, sl₁, sl₂, sl₃, sl₄, sl₅, f₁, sv₁, rd₁, wr₁⟩ := h₁
  obtain hx4 := hx .x4 (by simp)
  obtain hx5 := hx .x5 (by simp)
  obtain hx6 := hx .x6 (by simp)
  obtain hx7 := hx .x7 (by simp)
  obtain ⟨ol, tW, dtw, ddt⟩ := sealLay hs
  simp only [sealAArch64]
  obtain ⟨L, perm, hsp, dnW, daW, ddW, dcW, daA, dnd, dad, dcd, wn, wa, wd, hR, nR, aR, dW⟩ := ol
  obtain h3 := ofNat_toNat' (s.gpr .x3)
  obtain h5 := ofNat_toNat' (s.gpr .x5)
  obtain h7 := ofNat_toNat' (s.gpr .x7)
  have htb' := htb
  unfold TbForP at htb'
  generalize hW : stackArg s w = W at *
  generalize hTg : stackArg s 0 = Tg at *
  generalize hCtx : s.gpr .x0 = Ctx at *
  generalize hRR : (s.gpr .x1).toNat = R at *
  generalize hNp : s.gpr .x2 = Np at *
  generalize hnl : (s.gpr .x3).toNat = nl at *
  generalize hA : s.gpr .x4 = A at *
  generalize hal : (s.gpr .x5).toNat = al at *
  generalize hD : s.gpr .x6 = D at *
  generalize hn : (s.gpr .x7).toNat = n at *
  subst h12
  obtain hRb : R = 10 ∨ R = 12 ∨ R = 14 := by rw [← hRR]; exact hR
  unfold Impl.AesGcm.AArch64.Stitch.sealShort Impl.AesGcm.AArch64.Stitch.shortPre
  obtain sub16 : Region.Sub ⟨W + BitVec.ofNat 64 16, 80⟩ (workR W) := Lay.wSub (by decide)
  obtain kc := keep_of_sub (entryR_work W) (dcW.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide)))
  obtain hH₁ : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := blockAt_frame f₁ kc
  obtain hnon : DataOk (W + BitVec.ofNat 64 16) W s₁ Np 12 :=
    ⟨by rw [rd₁, wr₁]; exact nR, hnl ▸ (s.gpr .x3).isLt, wn, dnW.sub_right sub16, dnW⟩
  obtain iv₁ : bytesAt s₁.mem Np 12 = bytesAt s.mem Np 12 :=
    bytesAt_frame f₁ (keep_of_sub (entryR_work W) dnW) (by omega_arith)
  obtain hJ : J0In Ctx (W + BitVec.ofNat 64 16) W s.sp s₁.gpr (ctxH s.mem Ctx) Np 12 s₁ :=
    ⟨he₁, fun _ _ => rfl, x23₁, by rw [x24₁, ← h3], by rw [x26₁, ← h3], x27₁, hnon, hH₁⟩
  generalize hc : (n + 15) / 16 = c
  obtain hc1 : 2 ≤ c := by omega_arith
  obtain hc6 : c ≤ 6 := by omega_arith
  obtain hcn : n ≤ 16 * c := by omega_arith
  obtain hcn' : 16 * c ≤ n + 15 := by omega_arith
  -- `J₀`, the first counter block, and the lengths.
  refine WP.seq (WP.seq (WP.block_append_iff.mpr (WP.block_append_iff.mpr
    (WP.mono (WP.with_rdwr (WP.block_and (j012_ok L hJ) (j012_others hJ))) fun s₂ ⟨⟨h₂, o₂⟩, rd₂, wr₂⟩ =>
      WP.mono (WP.with_rdwr (WP.block_and (initState_ok L h₂) (initState_others h₂.env)))
        fun s₃ ⟨⟨h₃, o₃⟩, rd₃, wr₃⟩ => ?_))))
  rw [iv₁] at h₃
  obtain o₁₃ : ∀ r ∉ [Reg.x9, .x10, .x11, .x12], s₃.gpr r = s₁.gpr r := fun r hr => by rw [o₃ r hr, o₂ r hr]
  obtain F₃ : Frame [workR W, ⟨D, n⟩] s.mem s₃.mem := by
    obtain wE : ∀ {r : Region}, Region.Sub r (workR W) → ∃ r' ∈ [workR W, (⟨D, n⟩ : Region)], Region.Sub r r' :=
      fun h => ⟨_, List.mem_cons_self .., h⟩
    obtain j0W : ∀ r ∈ j0Frame (W + BitVec.ofNat 64 16) W, Region.Sub r (workR W) := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub16
      · exact Lay.wSub (by decide)
      · exact Lay.wSub (by decide)
    exact (f₁.sub fun r hr => wE (entryR_work W r hr)).trans (h₃.frame.sub fun r hr => wE (j0W r hr))
  refine WP.mono (Stitch.shortLen_ok (n := n) (D := D) (al := al) s₃ (by rw [o₁₃ _ (by decide), hx7, ← h7])
    (by rw [o₁₃ _ (by decide), hx6]) (by rw [o₁₃ _ (by decide), hx5, ← h5]) (by omega_arith))
    fun t₀ ⟨x26₅, x27₅, x24₅, x25₅, g₅, m₅, v₅, sp₅, rd₅, wr₅⟩ => ?_
  rw [hc] at x25₅
  obtain he₅ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp t₀ := h₃.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₅ _ (by decide) (by decide) (by decide) (by decide)) sp₅ rd₅ wr₅
  -- The table.
  refine WP.seq (WP.mono (htb' t₀ he₅ (by rw [rd₅, rd₃, rd₂, rd₁]) (by rw [wr₅, wr₃, wr₂, wr₁])
    (by rw [m₅]; exact F₃)) fun s₄ ⟨tbl₄, ft₄, g₄, sp₄, rd₄, wr₄⟩ => ?_)
  rw [m₅] at ft₄
  obtain he₄ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp s₄ := he₅.keep (fun r hr => g₄ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₄ rd₄ wr₄
  -- The buffers zeroed.
  refine WP.mono (Stitch.zeroBufs_ok (c := c) hc6 s₄ he₄.x19 (by rw [g₄ _ (by decide), x25₅])
    he₄.perm.w) fun s₆ ⟨m₆, g₆, sp₆, rd₆, wr₆⟩ => ?_
  obtain he₆ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp s₆ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₆ _ (by decide)) sp₆ rd₆ wr₆
  obtain x25₆ : s₆.gpr .x25 = BitVec.ofNat 64 (16 * c) := by rw [g₆ _ (by decide), g₄ _ (by decide), x25₅]
  obtain x26₆ : s₆.gpr .x26 = BitVec.ofNat 64 n := by rw [g₆ _ (by decide), g₄ _ (by decide), x26₅]
  obtain x27₆ : s₆.gpr .x27 = D := by rw [g₆ _ (by decide), g₄ _ (by decide), x27₅]
  obtain x24₆ : s₆.gpr .x24 = BitVec.ofNat 64 al := by rw [g₆ _ (by decide), g₄ _ (by decide), x24₅]
  obtain x4₆ : s₆.gpr .x4 = A := by
    rw [g₆ _ (by decide), g₄ _ (by decide), g₅ _ (by decide) (by decide) (by decide) (by decide),
      o₁₃ _ (by decide), hx4]
  obtain rd₆' : s₆.rd = s.rd := by rw [rd₆, rd₄, rd₅, rd₃, rd₂, rd₁]
  obtain wr₆' : s₆.wr = s.wr := by rw [wr₆, wr₄, wr₅, wr₃, wr₂, wr₁]
  -- The text, to block `p` of `B₁`.
  unfold Impl.AesGcm.AArch64.Stitch.textIn
  refine WP.seq (WP.seq ?_)
  rw [WP.block_append_iff]
  obtain ⟨t₁, run₁, x11₁, g₁', m₁', v₁', sp₁', rd₁', wr₁'⟩ := Stitch.atP_ok (c := c) .x11
    Impl.AesGcm.AArch64.Stitch.b1O 1 (by decide) (by unfold Impl.AesGcm.AArch64.Stitch.b1O; omega_arith) s₆ he₆.x19
    x25₆ (by decide)
  refine WP.of_runBlock ⟨t₁, run₁, ?_⟩
  obtain ⟨s₇, run₇, x12₇, x13₇, r₇⟩ : ∃ s₇, runBlock isa [mov .x12 .x27, mov .x13 .x26] t₁ = some s₇ ∧
      s₇.gpr .x12 = D ∧ s₇.gpr .x13 = BitVec.ofNat 64 n ∧ Regs [.x12, .x13] t₁ s₇ := by
    refine ⟨_, by arun [], ?_⟩
    exact ⟨by simp [gpr_write, g₁' .x27 (by decide), x27₆], by simp [gpr_write, g₁' .x26 (by decide), x26₆],
      ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  refine WP.of_runBlock ⟨s₇, run₇, ?_⟩
  obtain x11₇ : s₇.gpr .x11 = W + BitVec.ofNat 64 (880 - 16 * c) := by
    rw [r₇.others _ (by decide), x11₁]; rfl
  obtain rd₇ : s₇.rd = s.rd := by rw [r₇.rd, rd₁', rd₆']
  obtain wr₇ : s₇.wr = s.wr := by rw [r₇.wr, wr₁', wr₆']
  obtain m₇ : s₇.mem = s₆.mem := by rw [r₇.mem, m₁']
  refine WP.mono (Stitch.copyQ_ok s₇ ⟨x12₇, x11₇, x13₇, by omega_arith, by rw [rd₇, wr₇]; exact covers_left dW,
    by rw [wr₇]; exact covers_off perm.w (by omega_arith) (by decide),
    ddW.sub_right (Lay.wSub (by omega_arith))⟩) fun s₈ ⟨m₈, g₈, sp₈, rd₈, wr₈⟩ => ?_
  obtain he₈ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp s₈ := he₆.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> rw [g₈ _ (by decide), r₇.others _ (by decide), g₁' _ (by decide)])
    (by rw [sp₈, r₇.sp, sp₁']) (by rw [rd₈, r₇.rd, rd₁']) (by rw [wr₈, r₇.wr, wr₁'])
  obtain x25₈ : s₈.gpr .x25 = BitVec.ofNat 64 (16 * c) := by
    rw [g₈ _ (by decide), r₇.others _ (by decide), g₁' _ (by decide), x25₆]
  -- The counter, and one pass of AES over `B₁`.
  refine WP.seq (WP.mono (Stitch.shortCtr_ok (W := W) (St := W + BitVec.ofNat 64 16) hc6 s₈ he₈.x19
    he₈.x20 x25₈ (he₈.perm.stR (by decide))) fun s₉ ⟨x10₉, x9₉, g₉, m₉, v₉, sp₉, rd₉, wr₉⟩ => ?_)
  obtain he₉ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp s₉ := he₈.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₉ _ (by decide) (by decide)) sp₉ rd₉ wr₉
  obtain x22₉ : s₉.gpr .x22 = BitVec.ofNat 64 R := by
    rw [g₉ _ (by decide) (by decide), g₈ _ (by decide), r₇.others _ (by decide), g₁' _ (by decide),
      g₆ _ (by decide), g₄ _ (by decide), g₅ _ (by decide) (by decide) (by decide) (by decide),
      h₃.kept .x22 (by decide),
      x22₁, ← hRR, ofNat_toNat']
  obtain hp₉ : Proof.Gcm.AArch64.Stitch.APre R 0 (2 ^ 32 + c - 7) s₉ := {
    rounds := hRb
    o_le := by decide
    keys := fun r hr => by
      rw [Proof.Gcm.AArch64.Stitch.kp, he₉.x21]
      exact in_off he₉.perm.ctx (by omega_arith) (by decide)
    ctr := by
      rw [Proof.Gcm.AArch64.Stitch.cbA, he₉.x20, add_ofNat_zero]
      exact he₉.perm.stR (by decide)
    data := fun j hj => by
      rw [x9₉, Offset.add_add]
      exact he₉.perm.wR (by unfold Impl.AesGcm.AArch64.Stitch.b1O; omega_arith)
    x10 := by
      rw [x10₉]
      simp only [Proof.Gcm.AArch64.Stitch.c0, Proof.Gcm.AArch64.Stitch.cbk, Proof.Gcm.AArch64.Stitch.cbA, m₉,
        he₉.x20] }
  refine WP.seq (WP.mono (Stitch.shortAesB_ok s₉ hp₉ x22₉ x9₉ (covers_off he₉.perm.w (by decide) (by decide)))
    fun s₁₀ ⟨ks₁₀, f₁₀, g₁₀, sp₁₀, rd₁₀, wr₁₀, _⟩ => ?_)
  obtain he₁₀ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp s₁₀ := he₉.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁₀ _ (by decide)) sp₁₀ rd₁₀ wr₁₀
  obtain x25₁₀ : s₁₀.gpr .x25 = BitVec.ofNat 64 (16 * c) := by
    rw [g₁₀ _ (by decide), g₉ _ (by decide) (by decide), x25₈]
  obtain k₁₀ : ∀ r ∈ [Reg.x4, .x24, .x26, .x27, .x28], s₁₀.gpr r = s₆.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rw [g₁₀ _ (by decide), g₉ _ (by decide) (by decide), g₈ _ (by decide), r₇.others _ (by decide),
        g₁' _ (by decide)]
  obtain rd₁₀' : s₁₀.rd = s.rd := by rw [rd₁₀, rd₉, rd₈, rd₇]
  obtain wr₁₀' : s₁₀.wr = s.wr := by rw [wr₁₀, wr₉, wr₈, wr₇]
  -- The ciphertext, to the text and to `B₂`.
  unfold Impl.AesGcm.AArch64.Stitch.textOut
  refine WP.seq (WP.seq ?_)
  rw [WP.block_append_iff]
  obtain ⟨t₂, run₂, x12t₂, g₂', m₂', -, sp₂', rd₂', wr₂'⟩ := Stitch.atP_ok (c := c) .x12
    Impl.AesGcm.AArch64.Stitch.b1O 1 (by decide) (by unfold Impl.AesGcm.AArch64.Stitch.b1O; omega_arith) s₁₀ he₁₀.x19
    x25₁₀ (by decide)
  refine WP.of_runBlock ⟨t₂, run₂, ?_⟩
  obtain ⟨s₁₁, run₁₁, x11₁₁, x13₁₁, r₁₁⟩ : ∃ s₁₁, runBlock isa [mov .x11 .x27, mov .x13 .x26] t₂ = some s₁₁ ∧
      s₁₁.gpr .x11 = D ∧ s₁₁.gpr .x13 = BitVec.ofNat 64 n ∧ Regs [.x11, .x13] t₂ s₁₁ := by
    refine ⟨_, by arun [], ?_⟩
    exact ⟨by simp [gpr_write, g₂' .x27 (by decide), k₁₀ .x27 (by simp), x27₆],
      by simp [gpr_write, g₂' .x26 (by decide), k₁₀ .x26 (by simp), x26₆], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  refine WP.of_runBlock ⟨s₁₁, run₁₁, ?_⟩
  obtain x12₁₁ : s₁₁.gpr .x12 = W + BitVec.ofNat 64 (880 - 16 * c) := by
    rw [r₁₁.others _ (by decide), x12t₂]; rfl
  obtain rd₁₁ : s₁₁.rd = s.rd := by rw [r₁₁.rd, rd₂', rd₁₀']
  obtain wr₁₁ : s₁₁.wr = s.wr := by rw [r₁₁.wr, wr₂', wr₁₀']
  obtain m₁₁ : s₁₁.mem = s₁₀.mem := by rw [r₁₁.mem, m₂']
  refine WP.seq (WP.mono (Stitch.copyQ_ok s₁₁ ⟨x12₁₁, x11₁₁, x13₁₁, by omega_arith,
    by rw [rd₁₁, wr₁₁]; exact covers_left (covers_off perm.w (by omega_arith) (by decide)),
    by rw [wr₁₁]; exact dW, (ddW.sub_right (Lay.wSub (by omega_arith))).symm⟩) fun s₁₂ ⟨m₁₂, g₁₂, sp₁₂, rd₁₂, wr₁₂⟩ => ?_)
  obtain k₁₂ : ∀ r ∈ [Reg.x4, .x19, .x20, .x21, .x24, .x25, .x26, .x27, .x28], s₁₂.gpr r = s₁₀.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [g₁₂ _ (by decide), r₁₁.others _ (by decide), g₂' _ (by decide)]
  obtain he₁₂ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp s₁₂ := he₁₀.keep (fun r hr => k₁₂ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp))
    (by rw [sp₁₂, r₁₁.sp, sp₂']) (by rw [rd₁₂, rd₁₁, rd₁₀']) (by rw [wr₁₂, wr₁₁, wr₁₀'])
  refine WP.mono (Stitch.ctToB2_ok (by omega_arith) hc6 hcn s₁₂ he₁₂.x19 (by rw [k₁₂ .x25 (by simp), x25₁₀])
    (by rw [k₁₂ .x26 (by simp), k₁₀ .x26 (by simp), x26₆]) he₁₂.perm.w) fun s₁₃ ⟨m₁₃, g₁₃, sp₁₃, rd₁₃, wr₁₃⟩ => ?_
  obtain k₁₃ : ∀ r ∈ [Reg.x4, .x19, .x20, .x21, .x24, .x25, .x26, .x27, .x28], s₁₃.gpr r = s₁₀.gpr r := fun r hr => by
    obtain hr' : r ∉ [Reg.x9, .x11, .x12, .x13, .x14, .x15] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [g₁₃ r hr', k₁₂ r hr]
  obtain he₁₃ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp s₁₃ := he₁₂.keep (fun r hr => g₁₃ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp₁₃ rd₁₃ wr₁₃
  -- The additional data, to `B₂`.
  refine WP.seq (WP.mono (Stitch.aadIn_ok (A := A) (al := al) hc6 s₁₃ he₁₃.x19
    (by rw [k₁₃ .x25 (by simp), x25₁₀]) he₁₃.perm.w (by rw [k₁₃ .x4 (by simp), k₁₀ .x4 (by simp), x4₆])
    (by rw [k₁₃ .x24 (by simp), k₁₀ .x24 (by simp), x24₆]) h16
    (by rw [rd₁₃, wr₁₃, rd₁₂, wr₁₂, rd₁₁, wr₁₁]; exact aR) (daW.sub_right (Lay.wSub (by omega_arith))))
    fun s₁₄ ⟨m₁₄, g₁₄, sp₁₄, rd₁₄, wr₁₄⟩ => ?_)
  obtain k₁₄ : ∀ r ∈ [Reg.x4, .x19, .x20, .x21, .x24, .x25, .x26, .x27, .x28], s₁₄.gpr r = s₁₀.gpr r := fun r hr => by
    obtain hr' : r ∉ [Reg.x11, .x12, .x13, .x14, .x15] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [g₁₄ r hr', k₁₃ r hr]
  obtain he₁₄ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp s₁₄ := he₁₃.keep (fun r hr => g₁₄ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp₁₄ rd₁₄ wr₁₄
  obtain x26₁₄ : s₁₄.gpr .x26 = BitVec.ofNat 64 n := by rw [k₁₄ .x26 (by simp), k₁₀ .x26 (by simp), x26₆]
  obtain x24₁₄ : s₁₄.gpr .x24 = BitVec.ofNat 64 al := by rw [k₁₄ .x24 (by simp), k₁₀ .x24 (by simp), x24₆]
  -- The lengths block, GHASH, the tag, and the exit.
  simp only [Impl.AesGcm.AArch64.Stitch.shortTag, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Stitch.lensB_ok s₁₄ he₁₄.x19 he₁₄.perm.w x24₁₄ x26₁₄ (by omega_arith) (by omega_arith))
    fun s₁₅ ⟨lens₁₅, fL₁₅, og₁₅, sp₁₅, rd₁₅, wr₁₅, _⟩ => ?_
  obtain he₁₅ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp s₁₅ := he₁₄.keep (fun r hr => og₁₅ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp₁₅ rd₁₅ wr₁₅
  -- What the writes since the table keep.
  let BR : Region := ⟨W + BitVec.ofNat 64 768, 256⟩
  obtain one : ∀ {m m' : Mem} {q : Addr} {k : Nat}, Frame [⟨q, k⟩] m m' →
      (∃ r' ∈ [BR, ⟨D, n⟩], Region.Sub ⟨q, k⟩ r') → Frame [BR, ⟨D, n⟩] m m' := fun h hs =>
    h.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs
  obtain wB : ∀ {e k : Nat}, 768 ≤ e → e + k ≤ 1024 → ∃ r' ∈ [BR, ⟨D, n⟩],
      Region.Sub ⟨W + BitVec.ofNat 64 e, k⟩ r' := fun h₁ h₂ => ⟨_, List.mem_cons_self .., Offset.sub W h₁ (by omega_arith)⟩
  obtain wD : ∃ r' ∈ [BR, ⟨D, n⟩], Region.Sub ⟨D, n⟩ r' := ⟨_, by simp, fun _ h => h⟩
  obtain F₄₉ : Frame [BR, ⟨D, n⟩] s₄.mem s₉.mem := by
    rw [m₉, m₈, m₇, m₆]
    exact ((one (writeBytes_frame' _ List.length_replicate) (wB (by decide) (by decide))).trans
      (one (writeBytes_frame' _ List.length_replicate) (wB (by omega_arith) (by omega_arith)))).trans
      (one (writeBytes_frame' _ (Proof.AesCcm.length_bytesAt _ _ _)) (wB (by omega_arith) (by omega_arith)))
  obtain F₉₁₅ : Frame [BR, ⟨D, n⟩] s₉.mem s₁₅.mem := by
    obtain a₁ : Frame [BR, ⟨D, n⟩] s₉.mem s₁₀.mem := one f₁₀ (wB (by decide) (by decide))
    obtain a₂ : Frame [BR, ⟨D, n⟩] s₁₀.mem s₁₂.mem := by
      rw [m₁₂, m₁₁]; exact one (writeBytes_frame' _ (Proof.AesCcm.length_bytesAt _ _ _)) wD
    obtain a₃ : Frame [BR, ⟨D, n⟩] s₁₂.mem s₁₃.mem := by
      rw [m₁₃]
      exact (one (writeBytes_frame' _ (Proof.AesCcm.length_bytesAt _ _ _)) (wB (by omega_arith) (by omega_arith))).trans
        (one (writeBytes_frame' _ List.length_replicate) (wB (by omega_arith) (by omega_arith)))
    obtain a₄ : Frame [BR, ⟨D, n⟩] s₁₃.mem s₁₄.mem := by
      rw [m₁₄]; exact one (writeBytes_frame' _ (Proof.AesCcm.length_bytesAt _ _ _)) (wB (by omega_arith) (by omega_arith))
    exact (((a₁.trans a₂).trans a₃).trans a₄).trans (one fL₁₅ (wB (by decide) (by decide)))
  obtain dBR : ∀ {X : Region}, X.Disjoint (workR W) → X.Disjoint ⟨D, n⟩ → ∀ r ∈ [BR, ⟨D, n⟩], X.Disjoint r :=
    fun h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h₁.sub_right (Lay.wSub (by decide))
      · exact h₂
  obtain dWBR : ∀ {e k : Nat}, e + k ≤ 768 → ∀ r ∈ [BR, ⟨D, n⟩], (⟨W + BitVec.ofNat 64 e, k⟩ : Region).Disjoint r :=
    fun h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint W (.inl h) (by omega_arith) (by decide)
      · exact (ddW.sub_right (Lay.wSub (by omega_arith))).symm
  obtain tbl₁₅ : TblOk s₁₅.mem W (ctxH s.mem Ctx) :=
    tblOk_frame (tblOk_frame tbl₄ F₄₉ (dWBR (by decide))) F₉₁₅ (dWBR (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (Stitch.shortGh_ok gh s₁₅ he₁₅.x19 tbl₁₅ (covers_left he₁₅.perm.w))
    fun s₁₆ ⟨y₁₆, g₁₆, m₁₆, sp₁₆, rd₁₆, wr₁₆⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Stitch.shortTagAt_ok (W := W) (o := 0) (.inl rfl) hc6 s₁₆ (by rw [g₁₆ _ (by decide) (by decide),
      he₁₅.x19]) (by rw [g₁₆ _ (by decide) (by decide), og₁₅ _ (by decide), k₁₄ .x25 (by simp), x25₁₀]) y₁₆
      (by rw [wr₁₆, wr₁₅]; exact he₁₄.perm.w))
    fun s₁₇ ⟨tag₁₇, fT₁₇, g₁₇, sp₁₇, rd₁₇, wr₁₇⟩ => ?_
  obtain k₁₇ : ∀ r ∈ [Reg.x19, .x20, .x21, .x28], s₁₇.gpr r = s₁₄.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [g₁₇ _ (by decide), g₁₆ _ (by decide) (by decide), og₁₅ _ (by decide)]
  obtain x28₁₇ : s₁₇.gpr .x28 = Tg := by
    rw [k₁₇ .x28 (by simp), k₁₄ .x28 (by simp), k₁₀ .x28 (by simp), g₆ _ (by decide), g₄ _ (by decide),
      g₅ _ (by decide) (by decide) (by decide) (by decide), h₃.kept .x28 (by decide), x28₁]
  obtain he₁₇ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp s₁₇ := he₁₄.keep (fun r hr => k₁₇ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl <;> simp)) (by rw [sp₁₇, sp₁₆, sp₁₅]) (by rw [rd₁₇, rd₁₆, rd₁₅])
    (by rw [wr₁₇, wr₁₆, wr₁₅])
  obtain rd₁₇' : s₁₇.rd = s.rd := by rw [rd₁₇, rd₁₆, rd₁₅, rd₁₄, rd₁₃, rd₁₂, rd₁₁]
  obtain wr₁₇' : s₁₇.wr = s.wr := by rw [wr₁₇, wr₁₆, wr₁₅, wr₁₄, wr₁₃, wr₁₂, wr₁₁]
  rw [WP.block_append_iff]
  refine WP.mono (tagOut_ok he₁₇.x19 x28₁₇ (covers_left he₁₇.perm.w) (by rw [wr₁₇']; exact tW)
    (dtw.sub_right (Region.sub_prefix (by decide)))) fun s₁₈ ⟨out₁₈, f₁₈, og₁₈, sp₁₈, rd₁₈, wr₁₈⟩ => ?_
  obtain he₁₈ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp s₁₈ := he₁₇.keep (fun r hr => og₁₈ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₁₈ rd₁₈ wr₁₈
  obtain sv₁₈ : SavedAt s₁₈.mem W s := by
    refine ((((sv₁.frame h₃.frame (saved_j0Frame L)).frame ft₄ fun r hr => ?_).frame (F₄₉.trans F₉₁₅)
      fun r hr => ?_).frame (by rw [← m₁₆, ← add_ofNat_zero W]; exact fT₁₇) (saved_tag16 L)).frame f₁₈ fun r hr => ?_
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
      · exact (ddW.sub_right (Lay.wSub (by decide))).symm
    · simp only [List.mem_singleton] at hr; subst hr
      exact (dtw.sub_right (Lay.wSub (by decide))).symm
  refine WP.mono (exit_ok he₁₈.x19 he₁₈.sp (covers_left he₁₈.perm.w) sv₁₈) fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  rw [hm]
  simp only [Impl.AesGcm.AArch64.Stitch.b2O, Impl.AesGcm.AArch64.Stitch.b1O] at m₆ ks₁₀ y₁₆ f₁₀ tag₁₇
  have lb := Proof.AesCcm.length_bytesAt
  obtain selfB : ∀ (m : Mem) (q : Addr) (xs : List Byte) {k : Nat}, xs.length = k → k < 2 ^ 64 →
      bytesAt (writeBytes m q xs) q k = xs := fun m q xs _ hk hk' => by
    subst hk; exact bytesAt_writeBytes_self m q xs hk'
  obtain wf : ∀ (m : Mem) (q : Addr) (xs : List Byte) {k : Nat}, xs.length = k →
      Frame [⟨q, k⟩] m (writeBytes m q xs) := fun m _ _ _ hk => writeBytes_frame' m hk
  obtain one1 : ∀ {X r : Region}, X.Disjoint r → ∀ r' ∈ [r], X.Disjoint r' := fun h r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact h
  obtain dWW : ∀ {d k e j : Nat}, d + k ≤ e ∨ e + j ≤ d → d + k ≤ 2560 → e + j ≤ 2560 →
      (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, j⟩ :=
    fun h h₁ h₂ => Offset.disjoint W h (by omega_arith) (by omega_arith)
  obtain dDW : ∀ {e j : Nat}, e + j ≤ 2560 → (⟨D, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, j⟩ :=
    fun h => ddW.sub_right (Lay.wSub h)
  obtain F₀₄ : Frame [workR W] s.mem s₄.mem := by
    obtain w' : ∀ {r : Region}, Region.Sub r (workR W) → ∃ r' ∈ [workR W], Region.Sub r r' :=
      fun h => ⟨_, List.mem_singleton_self _, h⟩
    refine ((f₁.sub fun r hr => w' (entryR_work W r hr)).trans (h₃.frame.sub fun r hr => w' ?_)).trans
      (ft₄.sub fun r hr => w' ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub16
      · exact Lay.wSub (by decide)
      · exact Lay.wSub (by decide)
    · simp only [List.mem_singleton] at hr; subst hr; exact Lay.wSub (by decide)
  generalize hJ : Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np 12) = J
  have cb₃ := h₃.cb
  rw [hJ] at cb₃
  simp only [Offset.add_add] at cb₃
  -- The text, until it is encrypted.
  obtain hD₇ : bytesAt s₇.mem D n = bytesAt s.mem D n := by
    rw [m₇, m₆, bytesAt_frame (wf _ _ _ List.length_replicate) (one1 (dDW (by omega_arith))) (by omega_arith),
      bytesAt_frame (wf _ _ _ List.length_replicate) (one1 (dDW (by decide))) (by omega_arith),
      bytesAt_frame F₀₄ (one1 ddW) (by omega_arith)]
  obtain hP : bytesAt s₉.mem (W + BitVec.ofNat 64 768 + BitVec.ofNat 64 (16 * (7 - c))) n = bytesAt s.mem D n := by
    rw [Offset.add_add, show 768 + 16 * (7 - c) = 880 - 16 * c by omega_arith, m₉, m₈,
      selfB _ _ _ (lb _ _ _) (by omega_arith), hD₇]
  -- The key schedule and the counter block.
  obtain hsch : Proof.Gcm.AArch64.Stitch.sch R s₉ = bytesAt s.mem Ctx (16 * (R + 1)) := by
    obtain dC : (⟨Ctx, 16 * (R + 1)⟩ : Region).Disjoint (workR W) := dcW.sub_left (Region.sub_prefix (by omega_arith))
    simp only [Proof.Gcm.AArch64.Stitch.sch, Proof.Gcm.AArch64.Stitch.kp, he₉.x21]
    rw [bytesAt_frame F₄₉ (dBR dC (dcd.sub_left (Region.sub_prefix (by omega_arith)))) (by omega_arith),
      bytesAt_frame F₀₄ (one1 dC) (by omega_arith)]
  obtain hcb : Proof.Gcm.AArch64.Stitch.cbk s₉ = inc32 J := by
    simp only [Proof.Gcm.AArch64.Stitch.cbk, Proof.Gcm.AArch64.Stitch.cbA, he₉.x20, Offset.add_add]
    rw [blockAt_frame F₄₉ (dWBR (by decide)),
      blockAt_frame ft₄ (one1 (dWW (.inl (by decide)) (by decide) (by decide))), cb₃]
  -- The ciphertext, and `CIPH_K(J₀)`, in `B₁`.
  obtain hC₁₀ : bytesAt s₁₀.mem (W + BitVec.ofNat 64 (880 - 16 * c)) n =
      gctr (ctxCiph s.mem Ctx R) (inc32 J) (bytesAt s.mem D n) := by
    have := Stitch.b1_gctr hcn hc6 ks₁₀ hP
    rw [Offset.add_add, show 768 + 16 * (7 - c) = 880 - 16 * c by omega_arith, hsch, hcb] at this
    exact this
  obtain hz₉ : bytesAt s₉.mem (W + BitVec.ofNat 64 768 + BitVec.ofNat 64 (16 * (6 - c))) 16 = zeros 16 := by
    rw [Offset.add_add, show 768 + 16 * (6 - c) = 864 - 16 * c by omega_arith, m₉, m₈,
      bytesAt_frame (wf _ _ _ (lb _ _ _)) (one1 (dWW (.inl (by omega_arith)) (by omega_arith) (by omega_arith))) (by decide), m₇, m₆,
      selfB _ _ _ List.length_replicate (by decide)]
    rfl
  obtain hE : blockAt s₁₀.mem (W + BitVec.ofNat 64 (864 - 16 * c)) = ctxCiph s.mem Ctx R J := by
    rw [hcb] at ks₁₀
    have := Stitch.b1_j0 hc6 ks₁₀ hz₉
    rw [Offset.add_add, show 768 + 16 * (6 - c) = 864 - 16 * c by omega_arith, hsch] at this
    exact this
  obtain hE₁₆ : blockAt s₁₆.mem (W + BitVec.ofNat 64 (864 - 16 * c)) = ctxCiph s.mem Ctx R J := by
    rw [m₁₆, blockAt_frame fL₁₅ (one1 (dWW (.inl (by omega_arith)) (by omega_arith) (by decide))), m₁₄,
      blockAt_frame (wf _ _ _ (lb _ _ _)) (one1 (dWW (.inl (by omega_arith)) (by omega_arith) (by omega_arith))), m₁₃,
      blockAt_frame (wf _ _ _ List.length_replicate) (one1 (dWW (.inl (by omega_arith)) (by omega_arith) (by omega_arith))),
      blockAt_frame (wf _ _ _ (lb _ _ _)) (one1 (dWW (.inl (by omega_arith)) (by omega_arith) (by omega_arith))), m₁₂,
      blockAt_frame (wf _ _ _ (lb _ _ _)) (one1 (dDW (by omega_arith)).symm), m₁₁, hE]
  -- The text, at the end.
  obtain hC₁₂ : bytesAt s₁₂.mem (W + BitVec.ofNat 64 (880 - 16 * c)) n =
      gctr (ctxCiph s.mem Ctx R) (inc32 J) (bytesAt s.mem D n) := by
    rw [m₁₂, bytesAt_frame (wf _ _ _ (lb _ _ _)) (one1 (dDW (by omega_arith)).symm) (by omega_arith), m₁₁, hC₁₀]
  obtain hdata : bytesAt s₁₈.mem D n = gctr (ctxCiph s.mem Ctx R) (inc32 J) (bytesAt s.mem D n) := by
    rw [bytesAt_frame f₁₈ (one1 ddt) (by omega_arith), bytesAt_frame fT₁₇ (one1 (dDW (by decide))) (by omega_arith), m₁₆,
      bytesAt_frame fL₁₅ (one1 (dDW (by decide))) (by omega_arith), m₁₄,
      bytesAt_frame (wf _ _ _ (lb _ _ _)) (one1 (dDW (by omega_arith))) (by omega_arith), m₁₃,
      bytesAt_frame (wf _ _ _ List.length_replicate) (one1 (dDW (by omega_arith))) (by omega_arith),
      bytesAt_frame (wf _ _ _ (lb _ _ _)) (one1 (dDW (by omega_arith))) (by omega_arith), m₁₂,
      selfB _ _ _ (lb _ _ _) (by omega_arith), m₁₁, hC₁₀]
  -- What `B₂` holds, and its GHASH.
  generalize hCg : gctr (ctxCiph s.mem Ctx R) (inc32 J) (bytesAt s.mem D n) = Cg at hC₁₂ hdata
  obtain hCl : Cg.length = n := by rw [← hCg, Proof.Gcm.length_gctr, lb]
  obtain hA₁₃ : bytesAt s₁₃.mem A al = bytesAt s.mem A al := by
    obtain dA : ∀ {e j : Nat}, e + j ≤ 2560 → (⟨A, al⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, j⟩ :=
      fun h => daW.sub_right (Lay.wSub h)
    rw [m₁₃, bytesAt_frame (wf _ _ _ List.length_replicate) (one1 (dA (by omega_arith))) (by omega_arith),
      bytesAt_frame (wf _ _ _ (lb _ _ _)) (one1 (dA (by omega_arith))) (by omega_arith), m₁₂,
      bytesAt_frame (wf _ _ _ (lb _ _ _)) (one1 dad) (by omega_arith), m₁₁,
      bytesAt_frame f₁₀ (one1 (dA (by decide))) (by omega_arith), bytesAt_frame F₄₉ (dBR daW dad) (by omega_arith),
      bytesAt_frame F₀₄ (one1 daW) (by omega_arith)]
  obtain hZ₆ : bytesAt s₆.mem (W + BitVec.ofNat 64 896) 128 = zeros 128 := by
    rw [m₆, bytesAt_frame (wf _ _ _ List.length_replicate) (one1 (dWW (.inr (by omega_arith)) (by decide) (by omega_arith)))
      (by decide), selfB _ _ _ List.length_replicate (by decide)]
    rfl
  obtain fY : Frame [⟨W + BitVec.ofNat 64 768, 128⟩, ⟨D, n⟩] s₆.mem s₁₂.mem := by
    obtain oneG : ∀ {m m' : Mem} {q : Addr} {k : Nat}, Frame [⟨q, k⟩] m m' →
        (∃ r' ∈ [(⟨W + BitVec.ofNat 64 768, 128⟩ : Region), ⟨D, n⟩], Region.Sub ⟨q, k⟩ r') →
        Frame [⟨W + BitVec.ofNat 64 768, 128⟩, ⟨D, n⟩] m m' := fun h hs =>
      h.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs
    obtain a₁ : Frame [⟨W + BitVec.ofNat 64 768, 128⟩, ⟨D, n⟩] s₆.mem s₉.mem := by
      rw [m₉, m₈, m₇]
      exact oneG (wf _ _ _ (lb _ _ _)) ⟨_, List.mem_cons_self .., Offset.sub W (by omega_arith) (by omega_arith)⟩
    obtain a₂ : Frame [⟨W + BitVec.ofNat 64 768, 128⟩, ⟨D, n⟩] s₁₀.mem s₁₂.mem := by
      rw [m₁₂, m₁₁]; exact oneG (wf _ _ _ (lb _ _ _)) ⟨_, by simp, fun _ h => h⟩
    exact (a₁.trans (oneG f₁₀ ⟨_, List.mem_cons_self .., fun _ h => h⟩)).trans a₂
  obtain L := Stitch.b2_layout (G := W + BitVec.ofNat 64 896) (c := c) (n := n)
    (Q := bytesAt s₁₂.mem (W + BitVec.ofNat 64 (880 - 16 * c)) (16 * c)) (A := bytesAt s₁₃.mem A al)
    (lens := Proof.Gcm.lensBlock al n) (mZ := s₆.mem) (mY := s₁₂.mem) (mL := s₁₅.mem) hc6 hcn
    (by omega_arith) (lb _ _ _) (by rw [lb]; exact h16) hZ₆ fY (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dWW (.inr (by decide)) (by decide) (by decide)
      · exact (dDW (by decide)).symm)
    (by
      simp only [Offset.add_add]
      rw [show 896 + (112 - 16 * c) = 1008 - 16 * c by omega_arith, show 896 + (112 - 16 * c + n) = 1008 - 16 * c + n by omega_arith,
        show 896 + (96 - 16 * c) = 992 - 16 * c by omega_arith, ← m₁₃, ← m₁₄]
      exact fL₁₅)
    (by rw [Offset.add_add]; exact lens₁₅)
  rw [← Proof.AesCcm.bytesAt_prefix _ _ (show n ≤ 16 * c from hcn), hC₁₂, hA₁₃,
    show 16 * c - n = Spec.Gcm.padLen Cg.length by rw [hCl]; simp only [Spec.Gcm.padLen]; omega_arith,
    show Proof.Gcm.lensBlock al n = Proof.Gcm.lensBlock (bytesAt s.mem A al).length Cg.length by rw [lb, hCl]] at L
  obtain hg : Spec.Gcm.ghashFrom (ctxH s.mem Ctx) 0 ((List.range 8).map fun j =>
      blockAt s₁₅.mem (W + BitVec.ofNat 64 (896 + 16 * j))) =
      Spec.Gcm.ghashFrom (ctxH s.mem Ctx) (ghash (ctxH s.mem Ctx) (blocks (Proof.Gcm.padded (bytesAt s.mem A al) Cg)))
        [ofBytes (Proof.Gcm.lensBlock (bytesAt s.mem A al).length Cg.length)] := by
    rw [show ((List.range 8).map fun j => blockAt s₁₅.mem (W + BitVec.ofNat 64 (896 + 16 * j))) =
        Spec.Gcm.blocksAt s₁₅.mem (W + BitVec.ofNat 64 896) 8 by simp only [Spec.Gcm.blocksAt, Offset.add_add],
      Proof.Gcm.blocksAt_eq, L]
    exact Proof.Gcm.ghash_lead _ _ (by rw [lb]; exact h16)
  -- The tag.
  obtain bt : ∀ (m : Mem) (p : Addr), bytesAt m p 16 = Spec.Gcm.toBytes (blockAt m p) := fun m p => by
    rw [blockAt, Proof.Cmac.toBytes_ofBytes (lb _ _ _)]
  obtain htag : bytesAt s₁₈.mem Tg 16 = Spec.Gcm.toBytes (Spec.Gcm.ghashFrom (ctxH s.mem Ctx)
      (ghash (ctxH s.mem Ctx) (blocks (Proof.Gcm.padded (bytesAt s.mem A al) Cg)))
        [ofBytes (Proof.Gcm.lensBlock (bytesAt s.mem A al).length Cg.length)] ^^^ ctxCiph s.mem Ctx R J) := by
    rw [out₁₈, bt, ← add_ofNat_zero W, tag₁₇, hE₁₆, hg]
  rw [hdata, htag, Spec.Gcm.encryptWith, Proof.Gcm.fullTag_eq,
    List.take_of_length_le (by rw [Proof.Cmac.toBytes_length]), hJ, hCg]

end VG.Proof.AesGcm.AArch64.Fast
