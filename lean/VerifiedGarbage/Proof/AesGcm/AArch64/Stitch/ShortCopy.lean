module

import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Copy
public import VerifiedGarbage.Impl.AesGcm.AArch64.Stitch
import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Groups
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
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
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Spec.Aes
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem

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
  have e : a - (D + BitVec.ofNat 64 c) = (a - D) - BitVec.ofNat 64 c := by
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
  have htl : t < 2 ^ 64 := ht ▸ (a - D).isLt
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
  have x14₁ : (s.write .x .x14 (s.read .x .x13 >>> 4)).gpr .x14 = BitVec.ofNat 64 (n / 16) := by
    simp only [gpr_write_self, State.read, h.x13, BitVec.setWidth_eq, ofNat_lsr4 (show n < 2 ^ 64 by omega_arith)]
  generalize hs₁ : s.write .x .x14 (s.read .x .x13 >>> 4) = s₁ at x14₁
  have g₁ : ∀ r, r ≠ .x14 → s₁.gpr r = s.gpr r := fun r hr => by rw [← hs₁]; simp [gpr_write, hr]
  have m₁ : s₁.mem = s.mem := by rw [← hs₁, mem_write]
  have sp₁ : s₁.sp = s.sp := by rw [← hs₁, sp_write]
  have rd₁ : s₁.rd = s.rd := by rw [← hs₁, rd_write]
  have wr₁ : s₁.wr = s.wr := by rw [← hs₁, wr_write]
  refine WP.ite (decide (n / 16 = 0)) (eval_zero x14₁ (by omega_arith)) (fun hz => ?_) (fun hz => ?_)
  · -- Fewer than 16 bytes.
    have lp : LoopPre s₁ S D n := ⟨by omega_arith, by rw [rd₁, wr₁]; exact h.rd, by rw [wr₁]; exact h.wr, h.disj⟩
    refine WP.mono (copy_ok s₁ (by rw [g₁ _ (by decide), h.x12]) (by rw [g₁ _ (by decide), h.x11])
      (by rw [g₁ _ (by decide), h.x13]) lp) fun s' ⟨m', g', sp', rd', wr'⟩ => ⟨by rw [m', m₁], fun r hr => ?_,
        by rw [sp', sp₁], by rw [rd', rd₁], by rw [wr', wr₁]⟩
    rw [g' r (fun hm => hr (by
        simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl <;> decide)),
      g₁ r (by intro e; subst e; simp at hr)]
  · have h16 : 16 ≤ n := by have := of_decide_eq_false hz; omega_arith
    have hk1 : 1 ≤ n / 16 := by omega_arith
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
    have hb : BlocksPre s₂ S D (n / 16) :=
      ⟨by rw [g₂ _ (by decide) (by decide), g₁ _ (by decide), h.x12],
        by rw [g₂ _ (by decide) (by decide), g₁ _ (by decide), h.x11],
        by rw [g₂ _ (by decide) (by decide), x14₁], hk1, by omega_arith,
        by rw [rd₂, wr₂, rd₁, wr₁]; exact covers_prefix h.rd (by omega_arith),
        by rw [wr₂, wr₁]; exact covers_prefix h.wr (by omega_arith),
        (h.disj.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Region.sub_prefix (by omega_arith))⟩
    refine WP.seq (WP.mono (copyBlocks_wp s₂ hb) fun s₃ ⟨m₃, _, _, _, kp₃⟩ => ?_)
    -- The last 16 bytes.
    have ha : s₃.gpr .x9 + BitVec.ofNat 64 0 = S + BitVec.ofNat 64 (n - 16) := by
      rw [kp₃.gpr _ (by decide), x9₂, BitVec.add_zero]
    have hb : s₃.gpr .x10 + BitVec.ofNat 64 0 = D + BitVec.ofNat 64 (n - 16) := by
      rw [kp₃.gpr _ (by decide), x10₂, BitVec.add_zero]
    have hrd : InRegions (s₃.rd ++ s₃.wr) (S + BitVec.ofNat 64 (n - 16)) 16 := by
      rw [kp₃.rd, kp₃.wr, rd₂, wr₂, rd₁, wr₁]
      exact Proof.AesGcm.AArch64.in_off h.rd (by omega_arith) (by omega_arith)
    have hwr : InRegions s₃.wr (D + BitVec.ofNat 64 (n - 16)) 16 := by
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
    have hout : InRegions t.wr (t.gpr .x19 + BitVec.ofNat 64 (Impl.AesGcm.AArch64.Stitch.b2O + 16 * k)) 16 := by
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
  have hout : InRegions t₁.wr (t₁.gpr .x9 + BitVec.ofNat 64 0) 16 := by
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
  have m₃ : t₃.mem = s.mem := by rw [m₃', m₂, m₁]
  have rd₃ : t₃.rd = s.rd := by rw [rd₃', rd₂, rd₁]
  have wr₃ : t₃.wr = s.wr := by rw [wr₃', wr₂, wr₁]
  have sp₃ : t₃.sp = s.sp := by rw [sp₃', sp₂, sp₁]
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
  have x14₃ : t₃.gpr .x14 = BitVec.ofNat 64 c := by
    rw [← ht₃, gpr_write_self, State.read]
    simp only [Size.bits, BitVec.setWidth_eq]
    rw [g₂ _ (by decide), g₁ _ (by decide), h25, ofNat_lsr4 (show 16 * c < 2 ^ 64 by omega_arith),
      show 16 * c / 16 = c by omega_arith]
  have g₃ : ∀ r, r ≠ .x14 → t₃.gpr r = t₂.gpr r := fun r hr => by rw [← ht₃]; simp [gpr_write, hr]
  have m₃ : t₃.mem = s.mem := by rw [← ht₃, mem_write, m₂, m₁]
  have sp₃ : t₃.sp = s.sp := by rw [← ht₃, sp_write, sp₂, sp₁]
  have rd₃ : t₃.rd = s.rd := by rw [← ht₃, rd_write, rd₂, rd₁]
  have wr₃ : t₃.wr = s.wr := by rw [← ht₃, wr_write, wr₂, wr₁]
  -- The `c` blocks.
  refine WP.seq (WP.ite false (by rw [eval_zero x14₃ (by omega_arith)]; simp; omega_arith) (fun h => by cases h) fun _ => ?_)
  have hb : BlocksPre t₃ (W + BitVec.ofNat 64 (880 - 16 * c)) (W + BitVec.ofNat 64 (1008 - 16 * c)) c :=
    ⟨by rw [g₃ _ (by decide), g₂ _ (by decide), x12₁]; rfl, by rw [g₃ _ (by decide), x11₂]; rfl, x14₃, hc1,
      by omega_arith, by rw [rd₃, wr₃]; exact Proof.AesGcm.AArch64.covers_left (Proof.AesGcm.AArch64.covers_off hw
        (by omega_arith) (by decide)),
      by rw [wr₃]; exact Proof.AesGcm.AArch64.covers_off hw (by omega_arith) (by decide),
      Offset.disjoint W (.inl (by omega_arith)) (by omega_arith) (by omega_arith)⟩
  refine WP.mono (copyBlocks_wp t₃ hb) fun t₄ ⟨m₄, _, _, _, kp₄⟩ => ?_
  rw [WP.block_append_iff]
  have kg : ∀ r ∈ [Reg.x19, .x25, .x26], t₄.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [kp₄.gpr _ (by decide), g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide)]
  obtain ⟨t₅, run₅, x9₅, g₅, m₅, v₅, sp₅, rd₅, wr₅⟩ := atP_ok (c := c) .x9 Impl.AesGcm.AArch64.Stitch.b2O 1
    (by unfold Impl.AesGcm.AArch64.Stitch.b2O; omega_arith) (by unfold Impl.AesGcm.AArch64.Stitch.b2O; omega_arith) t₄
    (by rw [kg _ (by simp), h19]) (by rw [kg _ (by simp), h25]) (by decide)
  refine WP.of_runBlock ⟨t₅, run₅, ?_⟩
  have x26₅ : t₅.gpr .x26 = BitVec.ofNat 64 n := by rw [g₅ _ (by decide), kg _ (by simp), h26]
  generalize ht₆ : (t₅.write .x .x9 (t₅.read .x .x9 + t₅.read .x .x26)).setV .v0 0 = t₆
  have x9₆ : t₆.gpr .x9 = W + BitVec.ofNat 64 (1008 - 16 * c + n) := by
    rw [← ht₆, gpr_setV, gpr_write_self, State.read, State.read]
    simp only [Size.bits, BitVec.setWidth_eq]
    rw [x9₅, x26₅, BitVec.add_assoc, ← BitVec.ofNat_add]
    unfold Impl.AesGcm.AArch64.Stitch.b2O
    rfl
  have hout : InRegions t₆.wr (t₆.gpr .x9 + BitVec.ofNat 64 0) 16 := by
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
  have x14₃ : t₃.gpr .x14 = BitVec.ofNat 64 c := by
    rw [← ht₃, gpr_write_self, State.read]
    simp only [Size.bits, BitVec.setWidth_eq]
    rw [g₂ _ (by decide), g₁ _ (by decide), h25, ofNat_lsr4 (show 16 * c < 2 ^ 64 by omega_arith),
      show 16 * c / 16 = c by omega_arith]
  have g₃ : ∀ r, r ≠ .x14 → t₃.gpr r = t₂.gpr r := fun r hr => by rw [← ht₃]; simp [gpr_write, hr]
  have m₃ : t₃.mem = s.mem := by rw [← ht₃, mem_write, m₂, m₁]
  have sp₃ : t₃.sp = s.sp := by rw [← ht₃, sp_write, sp₂, sp₁]
  have rd₃ : t₃.rd = s.rd := by rw [← ht₃, rd_write, rd₂, rd₁]
  have wr₃ : t₃.wr = s.wr := by rw [← ht₃, wr_write, wr₂, wr₁]
  -- No blocks.
  refine WP.seq (WP.ite true (by rw [eval_zero x14₃ (by omega_arith)]; simp [hc1]) (fun _ => WP.block_nil ?_)
    fun h => by cases h)
  have m₄ : t₃.mem = writeBytes s.mem (W + BitVec.ofNat 64 (1008 - 16 * c))
      (bytesAt s.mem (W + BitVec.ofNat 64 (880 - 16 * c)) (16 * c)) := by
    rw [m₃, hc1, show 16 * 0 = 0 from rfl, show bytesAt s.mem (W + BitVec.ofNat 64 (880 - 0)) 0 = [] from rfl,
      writeBytes_nil]
  generalize t₃ = t₄ at m₄ g₃ sp₃ rd₃ wr₃
  rw [WP.block_append_iff]
  have kg : ∀ r ∈ [Reg.x19, .x25, .x26], t₄.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide)]
  obtain ⟨t₅, run₅, x9₅, g₅, m₅, v₅, sp₅, rd₅, wr₅⟩ := atP_ok (c := c) .x9 Impl.AesGcm.AArch64.Stitch.b2O 1
    (by unfold Impl.AesGcm.AArch64.Stitch.b2O; omega_arith) (by unfold Impl.AesGcm.AArch64.Stitch.b2O; omega_arith) t₄
    (by rw [kg _ (by simp), h19]) (by rw [kg _ (by simp), h25]) (by decide)
  refine WP.of_runBlock ⟨t₅, run₅, ?_⟩
  have x26₅ : t₅.gpr .x26 = BitVec.ofNat 64 n := by rw [g₅ _ (by decide), kg _ (by simp), h26]
  generalize ht₆ : (t₅.write .x .x9 (t₅.read .x .x9 + t₅.read .x .x26)).setV .v0 0 = t₆
  have x9₆ : t₆.gpr .x9 = W + BitVec.ofNat 64 (1008 - 16 * c + n) := by
    rw [← ht₆, gpr_setV, gpr_write_self, State.read, State.read]
    simp only [Size.bits, BitVec.setWidth_eq]
    rw [x9₅, x26₅, BitVec.add_assoc, ← BitVec.ofNat_add]
    unfold Impl.AesGcm.AArch64.Stitch.b2O
    rfl
  have hout : InRegions t₆.wr (t₆.gpr .x9 + BitVec.ofNat 64 0) 16 := by
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
  have ha : u₁.gpr .x9 + BitVec.ofNat 64 (0 + 16 * k) = B + BitVec.ofNat 64 (16 * k) := by
    rw [g₁, hx9, Nat.zero_add]
  have hout : InRegions u₁.wr (u₁.gpr .x9 + BitVec.ofNat 64 (0 + 16 * k)) 16 := by
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
  have gt : ∀ r, r ≠ .x13 → r ≠ .x14 → t.gpr r = s.gpr r := fun r h13 h14 => by
    rw [← ht, gpr_write_of_ne _ _ _ h14, gpr_write_of_ne _ _ _ h13]
  have mt : t.mem = s.mem := by rw [← ht, mem_write, mem_write]
  have vt : t.v = s.v := by rw [← ht, v_write, v_write]
  have spt : t.sp = s.sp := by rw [← ht, sp_write, sp_write]
  have rdt : t.rd = s.rd := by rw [← ht, rd_write, rd_write]
  have wrt : t.wr = s.wr := by rw [← ht, wr_write, wr_write]
  have e13 : t.gpr .x13 = BitVec.ofNat 64 (R - 10) := by
    rw [← ht]
    simp only [gpr_write_of_ne _ _ _ (show Reg.x13 ≠ Reg.x14 by decide), gpr_write_self, State.read,
      BitVec.setWidth_eq, hx22, Size.bits]
    rw [Offset.ofNat_sub_ofNat (by omega_arith)]
  have hft := hf t gt mt vt spt rdt wrt
  refine WP.ite _ (eval_zero e13 (by omega_arith)) (fun h => ?_) (fun h => ?_)
  · have h10 : R = 10 := by simp only [decide_eq_true_eq] at h; omega_arith
    rw [h10] at hft; exact hft
  · have hge : 12 ≤ R := by simp only [decide_eq_false_iff_not] at h; omega_arith
    have e14 : t.gpr .x14 = BitVec.ofNat 64 (R - 12) := by
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
