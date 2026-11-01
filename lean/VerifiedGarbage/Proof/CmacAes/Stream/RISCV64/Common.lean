module

public import VerifiedGarbage.Impl.CmacAes.Stream.RISCV64
public import VerifiedGarbage.Proof.CmacAes.RISCV64.Contract
public import VerifiedGarbage.Proof.Aes.RISCV64.ExpandKey
public import VerifiedGarbage.Proof.Cmac.Stream
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.CmacAes.RISCV64.Verified
import VerifiedGarbage.Proof.CmacAes.RISCV64.CT
import VerifiedGarbage.Proof.AesCbc.RISCV64.Body
import VerifiedGarbage.Proof.AesCbc.RISCV64.Call
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
import VerifiedGarbage.Proof.Aes.RISCV64.ExpandKeyVerified
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Align
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# Streaming AES-CMAC on RISC-V: the contracts, the calls and the copies

As on PPC64LE (`Proof/CmacAes/Stream/PPC64LE/Common.lean`). The artifacts'
contracts are the shared ones of `Spec/Cmac/Contract.lean`, with the working
space appended (`Proof/CmacAes/Stream/Scratch.lean`), which imply these
(`Verified.lean`). A call (`jal`) stores nothing in memory, so no stack is
used.

A call of each function the streaming functions call
(`vg_aes_expand_key_scratch`, `vg_cmac_aes_subkeys`, `vg_cmac_aes_update` and
`vg_cmac_aes_finalize`), from its contract (with `WP.call`): what it needs
(`…Args`), what it leaves (`…Post`, in terms of the memory before the call),
and that two calls with the same arguments leak the same (`…_rel`). The
callees change only the buffers they are given, and keep every callee-saved
register. Then the number of bytes held back, as the code computes it from
`count` (`held_bv`), and `copy`, which copies the `t2` bytes at `t6` to
`t5`, a byte at a time (none if `t2` is 0), changing only `t2`, `t3`, `t5`
and `t6`.
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.RISCV64

open VG VG.RISCV64
open VG.Proof.CmacAes.RISCV64 (subkeysRISCV64 updateRISCV64 finalizeRISCV64)
open VG.Proof.AesCbc.RISCV64 (toNat_rounds)

/-! ## The contracts -/

/-- `vg_cmac_aes_init(state = a0, key = a1, key_len = a2, scratch = a3)`. -/
def initRISCV64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 304⟩
    let key : Region := ⟨s.gpr .a1, (s.gpr .a2).toNat⟩
    let scr : Region := ⟨s.gpr .a3, 2304⟩
    s.rd = [key] ∧ s.wr = [state, scr] ∧
      state.Disjoint key ∧ state.Disjoint scr ∧ key.Disjoint scr ∧
      (s.gpr .a0).toNat + 304 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + (s.gpr .a2).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a3).toNat + 2304 ≤ 2 ^ 64 ∧
      ((s.gpr .a2).toNat = 16 ∨ (s.gpr .a2).toNat = 24 ∨ (s.gpr .a2).toNat = 32)
  post s s' :=
    Spec.Cmac.Repr s'.mem (s.gpr .a0) (Spec.Aes.bytesAt s.mem (s.gpr .a1) (s.gpr .a2).toNat) []
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

/-- `vg_cmac_aes_absorb(state = a0, rounds = a1, count = a2, data = a3, len = a4, scratch = a5)`. -/
def absorbRISCV64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 304⟩
    let data : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
    let scr : Region := ⟨s.gpr .a5, 2304⟩
    s.rd = [data] ∧ s.wr = [state, scr] ∧
      state.Disjoint data ∧ state.Disjoint scr ∧ data.Disjoint scr ∧
      (s.gpr .a0).toNat + 304 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a5).toNat + 2304 ≤ 2 ^ 64 ∧
      ((s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14)
  post s s' :=
    ∀ key msg, Spec.Cmac.Repr s.mem (s.gpr .a0) key msg →
      (s.gpr .a1).toNat = Spec.Aes.rounds (key.length / 4) →
      s.gpr .a2 = BitVec.ofNat 64 msg.length → msg.length + (s.gpr .a4).toNat < 2 ^ 64 →
      Spec.Cmac.Repr s'.mem (s.gpr .a0) key
        (msg ++ Spec.Aes.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat)
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.sp = s₂.sp

/-- `vg_cmac_aes_finish(state = a0, rounds = a1, count = a2, out = a3, scratch = a4)`. -/
def finishRISCV64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 304⟩
    let out : Region := ⟨s.gpr .a3, 16⟩
    let scr : Region := ⟨s.gpr .a4, 2304⟩
    s.rd = [] ∧ s.wr = [state, out, scr] ∧
      state.Disjoint out ∧ state.Disjoint scr ∧ out.Disjoint scr ∧
      (s.gpr .a0).toNat + 304 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .a4).toNat + 2304 ≤ 2 ^ 64 ∧
      ((s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14)
  post s s' :=
    ∀ key msg, Spec.Cmac.Repr s.mem (s.gpr .a0) key msg →
      (s.gpr .a1).toNat = Spec.Aes.rounds (key.length / 4) →
      s.gpr .a2 = BitVec.ofNat 64 msg.length → msg.length < 2 ^ 64 →
      Spec.Aes.bytesAt s'.mem (s.gpr .a3) 16 = Spec.Cmac.aesCmac key 16 msg
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.sp = s₂.sp

/-! ## Arithmetic -/

theorem toNat_ofNat {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem ofNat_toNat_eq {x : BitVec 64} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 64 n :=
  BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (h ▸ x.isLt)])

theorem toNat_add_lt (p : Addr) {d k : Nat} (h : p.toNat + k ≤ 2 ^ 64) (hd : d < k) :
    (p + BitVec.ofNat 64 d).toNat = p.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 64)]
  exact Nat.mod_eq_of_lt (by omega)

theorem and15 (x : BitVec 64) : (x &&& BitVec.ofInt 64 15).toNat = x.toNat % 16 := by
  rw [BitVec.toNat_and, show (BitVec.ofInt 64 15).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

open VG.Proof.Cmac.Stream (held held_pos) in
/-- The number of bytes held back for a nonzero `count`, as `addi -1; andi 15; addi 1` computes it. -/
theorem held_bv (c : BitVec 64) (h : c ≠ 0) :
    ((c - BitVec.ofNat 64 1) &&& BitVec.ofInt 64 15) + BitVec.ofNat 64 1 = BitVec.ofNat 64 (held c.toNat) := by
  have hc : c.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
  rw [held_pos (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, and15, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  have := c.isLt
  omega

/-- The rounds, as `srli 2; addi 6` computes them from the key length. -/
theorem rounds_bv {KL : Nat} (h : KL = 16 ∨ KL = 24 ∨ KL = 32) :
    BitVec.ofNat 64 KL >>> 2 + BitVec.ofNat 64 6 = BitVec.ofNat 64 (KL / 4 + 6) := by
  rcases h with rfl | rfl | rfl <;> decide

theorem shr_ofNat {n k : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> k = BitVec.ofNat 64 (n / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by have := Nat.div_le_self n (2 ^ k); omega)]

theorem preserved_ne (r : Reg) (hr : r ∈ preserved) :
    r ≠ .t0 ∧ r ≠ .t1 ∧ r ≠ .t2 ∧ r ≠ .t3 ∧ r ≠ .t4 ∧ r ≠ .t5 ∧ r ≠ .t6 ∧ r ≠ .ra ∧ r ≠ .a0 ∧
      r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .a3 ∧ r ≠ .a4 ∧ r ≠ .a5 ∧ r ≠ .a6 ∧ r ≠ .a7 := by
  revert hr; cases r <;> decide

theorem in_wr {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

/-! ## Saving registers -/

/-- `addi 2047`, `addi 136` then `andi -8`: `x + 2176` rounded up. -/
theorem sv2_arith (x : Addr) :
    (x + BitVec.ofInt 64 2047 + BitVec.ofInt 64 136) &&& BitVec.ofInt 64 (-8) =
      x + BitVec.ofNat 64 2176 + BitVec.ofNat 64 (Align.pad (x + BitVec.ofNat 64 2176)) := by
  rw [← Align.align_eq, BitVec.add_assoc, BitVec.add_assoc,
    show BitVec.ofInt 64 2047 + BitVec.ofInt 64 136 = BitVec.ofNat 64 2176 + BitVec.ofInt 64 7 by decide]

/-- Where the streaming functions save the registers, from the scratch
buffer `S`: `S + 2176` rounded up to a multiple of 8. -/
abbrev sv2 (S : Addr) : Addr :=
  S + BitVec.ofNat 64 2176 + BitVec.ofNat 64 (Align.pad (S + BitVec.ofNat 64 2176))

/-- `t0 :=` the register `n`'s value plus 2176, rounded up. -/
theorem savePtr2_ok {s : State} (n : Reg) :
    WP isa (.block (Impl.CmacAes.Stream.RISCV64.savePtr2 n)) s (· = s.write .t0 (sv2 (s.gpr n))) := by
  apply WP.of_runBlock
  simp only [Impl.CmacAes.Stream.RISCV64.savePtr2, runBlock_cons, runStep_some, runBlock_nil,
    exec_addi (show imm12 2047 by decide), exec_addi (show imm12 136 by decide),
    exec_logicImm (show imm12 (-8) by decide), RegUpd.gpr_write_self, RegUpd.write_write, Option.some.injEq,
    exists_eq_left']
  rw [sv2_arith]

theorem sv2_add (S : Addr) (d : Nat) :
    sv2 S + BitVec.ofNat 64 d = S + BitVec.ofNat 64 (2176 + Align.pad (S + BitVec.ofNat 64 2176) + d) :=
  Align.align_add _ _ _

/-- A slot at `sv2 S + d`, within the scratch buffer. -/
theorem sv2_sub (S : Addr) {d n : Nat} (h : d + n ≤ 121) : Region.Sub ⟨sv2 S + BitVec.ofNat 64 d, n⟩ ⟨S, 2304⟩ := by
  have := Align.pad_lt (S + BitVec.ofNat 64 2176)
  rw [sv2_add]; exact Offset.sub_base _ (by omega)

theorem sv2_contains (S : Addr) {d n : Nat} (h : d + n ≤ 121) :
    (⟨S, 2304⟩ : Region).Contains (sv2 S + BitVec.ofNat 64 d) n := by
  have := Align.pad_lt (S + BitVec.ofNat 64 2176)
  rw [sv2_add]; exact Offset.contains_base _ (by omega) (by omega)

/-- A slot at `sv2 S + d`, above the callees' working space. -/
theorem sv2_ws (S : Addr) {d n : Nat} (h : d + n ≤ 121) :
    Region.Disjoint ⟨sv2 S + BitVec.ofNat 64 d, n⟩ ⟨S, 2176⟩ := by
  have := Align.pad_lt (S + BitVec.ofNat 64 2176)
  rw [sv2_add]; exact Offset.disjoint_base _ (by omega) (by omega)

/-- Slots holding registers whose values agree hold either's. -/
theorem saved_congr {B : Addr} {g g' : Reg → BitVec 64} {l : List (Reg × Nat)} {m : Mem}
    (h : Spill.Saved B g l m) (hg : ∀ p ∈ l, g p.1 = g' p.1) : Spill.Saved B g' l m :=
  fun p hp => (h p hp).trans (hg p hp)

/-! ## No frames -/

theorem expandKey_noFrames : Impl.Aes.RISCV64.expandKey.noFrames = true := by lit_decide

theorem subkeys_noFrames : Impl.CmacAes.RISCV64.subkeys.noFrames = true := by
  simp [Impl.CmacAes.RISCV64.subkeys, Impl.AesCbc.RISCV64.encCall, Code.noFrames]
  exact Proof.AesCbc.RISCV64.encryptBlocks_noFrames

theorem update_noFrames : Impl.CmacAes.RISCV64.update.noFrames = true := by
  simp only [Impl.CmacAes.RISCV64.update, Impl.Aes.RISCV64.macChainCall, Code.noFrames, Bool.and_true,
    Bool.true_and]
  exact (Proof.AesCbc.RISCV64.chain_k false).noFrames

theorem finalize_noFrames : Impl.CmacAes.RISCV64.finalize.noFrames = true := by
  simp [Impl.CmacAes.RISCV64.finalize, Impl.CmacAes.RISCV64.finPre, Impl.CmacAes.RISCV64.partialBlock,
    Impl.CmacAes.RISCV64.xorLoop, Impl.AesCbc.RISCV64.encCall, Code.noFrames]
  exact Proof.AesCbc.RISCV64.encryptBlocks_noFrames

/-! ## `vg_cmac_aes_update` -/

/-- What a call of `vg_cmac_aes_update` needs: the key schedule `W`, the
chaining value `C`, `n` blocks at `D`, the working space `S` and the rounds
`R`. -/
structure UArgs (s : State) (W C D S : Addr) (R n : Nat) : Prop where
  a0 : s.gpr .a0 = W
  a1 : s.gpr .a1 = BitVec.ofNat 64 R
  a2 : s.gpr .a2 = C
  a3 : s.gpr .a3 = D
  a4 : s.gpr .a4 = BitVec.ofNat 64 n
  a5 : s.gpr .a5 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  hn : 16 * n < 2 ^ 64
  wc : (⟨W, 240⟩ : Region).Disjoint ⟨C, 16⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2176⟩
  dc : (⟨D, 16 * n⟩ : Region).Disjoint ⟨C, 16⟩
  ds : (⟨D, 16 * n⟩ : Region).Disjoint ⟨S, 2176⟩
  cs : (⟨C, 16⟩ : Region).Disjoint ⟨S, 2176⟩
  wrapC : C.toNat + 16 ≤ 2 ^ 64
  wrapD : D.toNat + 16 * n ≤ 2 ^ 64
  wrapS : S.toNat + 2176 ≤ 2 ^ 64
  reads : Covers ([⟨W, 240⟩, ⟨D, 16 * n⟩] ++ [⟨C, 16⟩, ⟨S, 2176⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 16⟩, ⟨S, 2176⟩] s.wr

/-- What a call of `vg_cmac_aes_update` leaves. -/
structure UPost (s : State) (W C D S : Addr) (R n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨C, 16⟩, ⟨S, 2176⟩] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem C 16 =
    Spec.Cmac.chain (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem W (16 * (R + 1))))
      (Spec.Aes.bytesAt s.mem C 16) (Spec.Cmac.blocksAt s.mem D 16 n)

theorem UArgs.pre {s : State} {W C D S : Addr} {R n : Nat} (h : UArgs s W C D S R n) :
    updateRISCV64.pre (s.callEntry.withRegions [⟨W, 240⟩, ⟨D, 16 * n⟩] [⟨C, 16⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  have hN := toNat_ofNat (n := n) (by have := h.hn; omega)
  simp only [updateRISCV64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a4 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a5 ∉ linkRegs),
    h.a0, h.a1, h.a2, h.a3, h.a4, h.a5, hR, hN]
  exact ⟨trivial, trivial, h.wc, h.ws, h.dc, h.ds, h.cs, h.wrapC, h.wrapD, h.wrapS, h.rounds⟩

theorem upd_call {s : State} {W C D S : Addr} {R n : Nat} (h : UArgs s W C D S R n) :
    WP isa Impl.CmacAes.Stream.RISCV64.updCall s (UPost s W C D S R n) := by
  have hR := toNat_rounds h.rounds
  have hN := toNat_ofNat (n := n) (by have := h.hn; omega)
  refine WP.call (k := updateRISCV64) Proof.CmacAes.RISCV64.update_correct h.pre h.reads h.writes ?_
    update_noFrames
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [updateRISCV64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a4 ∉ linkRegs), h.a0, h.a1, h.a2, h.a3, h.a4, hR, hN] at hpost
  exact hpost

theorem upd_rel {W C D S : Addr} {R n : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → UArgs s₁ W C D S R n ∧ UArgs s₂ W C D S R n ∧ s₁.sp = s₂.sp) :
    RelCT isa P Impl.CmacAes.Stream.RISCV64.updCall fun _ _ => True := by
  refine RelCT.call Proof.CmacAes.RISCV64.update_correct Proof.CmacAes.RISCV64.update_ct
    [⟨W, 240⟩, ⟨D, 16 * n⟩] [⟨C, 16⟩, ⟨S, 2176⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [updateRISCV64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.a4 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a5 ∉ linkRegs),
    h₁.a0, h₁.a1, h₁.a2, h₁.a3, h₁.a4, h₁.a5, h₂.a0, h₂.a1, h₂.a2, h₂.a3, h₂.a4, h₂.a5, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_cmac_aes_subkeys` -/

/-- What a call of `vg_cmac_aes_subkeys` needs: the key schedule `W`, the
subkeys `K`, the working space `S` and the rounds `R`. -/
structure SArgs (s : State) (W K S : Addr) (R : Nat) : Prop where
  a0 : s.gpr .a0 = W
  a1 : s.gpr .a1 = BitVec.ofNat 64 R
  a2 : s.gpr .a2 = K
  a3 : s.gpr .a3 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wk : (⟨W, 240⟩ : Region).Disjoint ⟨K, 32⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2176⟩
  ks : (⟨K, 32⟩ : Region).Disjoint ⟨S, 2176⟩
  wrapK : K.toNat + 32 ≤ 2 ^ 64
  wrapS : S.toNat + 2176 ≤ 2 ^ 64
  reads : Covers ([⟨W, 240⟩] ++ [⟨K, 32⟩, ⟨S, 2176⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨K, 32⟩, ⟨S, 2176⟩] s.wr

/-- What a call of `vg_cmac_aes_subkeys` leaves. -/
structure SPost (s : State) (W K S : Addr) (R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨K, 32⟩, ⟨S, 2176⟩] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem K 32 =
    (Spec.Cmac.subkeys (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem W (16 * (R + 1)))) 16).1 ++
      (Spec.Cmac.subkeys (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem W (16 * (R + 1)))) 16).2

theorem SArgs.pre {s : State} {W K S : Addr} {R : Nat} (h : SArgs s W K S R) :
    subkeysRISCV64.pre (s.callEntry.withRegions [⟨W, 240⟩] [⟨K, 32⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  simp only [subkeysRISCV64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
    h.a0, h.a1, h.a2, h.a3, hR]
  exact ⟨trivial, trivial, h.wk, h.ws, h.ks, h.wrapK, h.wrapS, h.rounds⟩

theorem sub_call {s : State} {W K S : Addr} {R : Nat} (h : SArgs s W K S R) :
    WP isa Impl.CmacAes.Stream.RISCV64.skCall s (SPost s W K S R) := by
  have hR := toNat_rounds h.rounds
  refine WP.call (k := subkeysRISCV64) Proof.CmacAes.RISCV64.subkeys_correct h.pre h.reads h.writes ?_
    subkeys_noFrames
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [subkeysRISCV64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), h.a0, h.a1, h.a2, hR] at hpost
  exact hpost

theorem sub_rel {W K S : Addr} {R : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → SArgs s₁ W K S R ∧ SArgs s₂ W K S R ∧ s₁.sp = s₂.sp) :
    RelCT isa P Impl.CmacAes.Stream.RISCV64.skCall fun _ _ => True := by
  refine RelCT.call Proof.CmacAes.RISCV64.subkeys_correct Proof.CmacAes.RISCV64.subkeys_ct
    [⟨W, 240⟩] [⟨K, 32⟩, ⟨S, 2176⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [subkeysRISCV64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a3 ∉ linkRegs),
    h₁.a0, h₁.a1, h₁.a2, h₁.a3, h₂.a0, h₂.a1, h₂.a2, h₂.a3, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_cmac_aes_finalize` -/

/-- What a call of `vg_cmac_aes_finalize` needs: the key schedule and
subkeys `K`, the state `St`, the `L` last bytes at `P`, the working space
`S` and the rounds `R`. -/
structure FArgs (s : State) (K St P S : Addr) (L R : Nat) : Prop where
  a0 : s.gpr .a0 = K
  a1 : s.gpr .a1 = BitVec.ofNat 64 R
  a2 : s.gpr .a2 = St
  a3 : s.gpr .a3 = P
  a4 : s.gpr .a4 = BitVec.ofNat 64 L
  a5 : s.gpr .a5 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  len : L ≤ 16
  kst : (⟨K, 272⟩ : Region).Disjoint ⟨St, 16⟩
  ks : (⟨K, 272⟩ : Region).Disjoint ⟨S, 2176⟩
  pst : (⟨P, L⟩ : Region).Disjoint ⟨St, 16⟩
  ps : (⟨P, L⟩ : Region).Disjoint ⟨S, 2176⟩
  sts : (⟨St, 16⟩ : Region).Disjoint ⟨S, 2176⟩
  wrapK : K.toNat + 272 ≤ 2 ^ 64
  wrapSt : St.toNat + 16 ≤ 2 ^ 64
  wrapP : P.toNat + L ≤ 2 ^ 64
  wrapS : S.toNat + 2176 ≤ 2 ^ 64
  reads : Covers ([⟨K, 272⟩, ⟨P, L⟩] ++ [⟨St, 16⟩, ⟨S, 2176⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨St, 16⟩, ⟨S, 2176⟩] s.wr

/-- What a call of `vg_cmac_aes_finalize` leaves. -/
structure FPost (s : State) (K St P S : Addr) (L R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨St, 16⟩, ⟨S, 2176⟩] s.mem s'.mem
  out : let ciph := Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem K (16 * (R + 1)))
    let ks := Spec.Cmac.subkeys ciph 16
    Spec.Aes.bytesAt s.mem (K + 240) 32 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 16 = 0 → (msg = [] ∨ 0 < L) →
      Spec.Aes.bytesAt s.mem St 16 = Spec.Cmac.chain ciph (Spec.Cmac.zeros 16) (Spec.Cmac.blocks 16 msg) →
      Spec.Aes.bytesAt s'.mem St 16 = Spec.Cmac.macFull ciph 16 (msg ++ Spec.Aes.bytesAt s.mem P L)

theorem FArgs.pre {s : State} {K St P S : Addr} {L R : Nat} (h : FArgs s K St P S L R) :
    finalizeRISCV64.pre (s.callEntry.withRegions [⟨K, 272⟩, ⟨P, L⟩] [⟨St, 16⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  have hL := toNat_ofNat (n := L) (by have := h.len; omega)
  simp only [finalizeRISCV64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a4 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a5 ∉ linkRegs),
    h.a0, h.a1, h.a2, h.a3, h.a4, h.a5, hR, hL]
  exact ⟨trivial, trivial, h.kst, h.ks, h.pst, h.ps, h.sts, h.wrapK, h.wrapSt, h.wrapP, h.wrapS,
    h.rounds, h.len⟩

theorem fin_call {s : State} {K St P S : Addr} {L R : Nat} (h : FArgs s K St P S L R) :
    WP isa Impl.CmacAes.Stream.RISCV64.finCall s (FPost s K St P S L R) := by
  have hR := toNat_rounds h.rounds
  have hL := toNat_ofNat (n := L) (by have := h.len; omega)
  refine WP.call (k := finalizeRISCV64) Proof.CmacAes.RISCV64.finalize_correct h.pre h.reads h.writes ?_
    finalize_noFrames
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [finalizeRISCV64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a4 ∉ linkRegs), h.a0, h.a1, h.a2, h.a3, h.a4, hR, hL] at hpost
  exact hpost

theorem fin_rel {K St Q S : Addr} {L R : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → FArgs s₁ K St Q S L R ∧ FArgs s₂ K St Q S L R ∧ s₁.sp = s₂.sp) :
    RelCT isa P Impl.CmacAes.Stream.RISCV64.finCall fun _ _ => True := by
  refine RelCT.call Proof.CmacAes.RISCV64.finalize_correct Proof.CmacAes.RISCV64.finalize_ct
    [⟨K, 272⟩, ⟨Q, L⟩] [⟨St, 16⟩, ⟨S, 2176⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [finalizeRISCV64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.a4 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a5 ∉ linkRegs),
    h₁.a0, h₁.a1, h₁.a2, h₁.a3, h₁.a4, h₁.a5, h₂.a0, h₂.a1, h₂.a2, h₂.a3, h₂.a4, h₂.a5, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_aes_expand_key_scratch` -/

/-- What a call of `vg_aes_expand_key_scratch` needs: the key `Kp` of `KL`
bytes, the schedule `W` and the working space `S`. -/
structure EArgs (s : State) (Kp W S : Addr) (KL : Nat) : Prop where
  a0 : s.gpr .a0 = Kp
  a1 : s.gpr .a1 = BitVec.ofNat 64 KL
  a2 : s.gpr .a2 = W
  a3 : s.gpr .a3 = S
  klen : KL = 16 ∨ KL = 24 ∨ KL = 32
  kw : (⟨Kp, KL⟩ : Region).Disjoint ⟨W, 240⟩
  ks : (⟨Kp, KL⟩ : Region).Disjoint ⟨S, 512⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 512⟩
  reads : Covers ([⟨Kp, KL⟩] ++ [⟨W, 240⟩, ⟨S, 512⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨W, 240⟩, ⟨S, 512⟩] s.wr

/-- What a call of `vg_aes_expand_key_scratch` leaves. -/
structure EPost (s : State) (Kp W S : Addr) (KL : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨W, 240⟩, ⟨S, 512⟩] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem W (16 * (Spec.Aes.rounds (KL / 4) + 1)) =
    Spec.Aes.expandKey (Spec.Aes.bytesAt s.mem Kp KL)

theorem EArgs.pre {s : State} {Kp W S : Addr} {KL : Nat} (h : EArgs s Kp W S KL) :
    Proof.Aes.expandKeyRISCV64.pre (s.callEntry.withRegions [⟨Kp, KL⟩] [⟨W, 240⟩, ⟨S, 512⟩]) := by
  have hK := toNat_ofNat (n := KL) (by rcases h.klen with h | h | h <;> omega)
  simp only [Proof.Aes.expandKeyRISCV64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
    h.a0, h.a1, h.a2, h.a3, hK]
  exact ⟨trivial, trivial, h.kw, h.ks, h.ws, h.klen⟩

theorem ek_call {s : State} {Kp W S : Addr} {KL : Nat} (h : EArgs s Kp W S KL) :
    WP isa Impl.CmacAes.Stream.RISCV64.ekCall s (EPost s Kp W S KL) := by
  have hK := toNat_ofNat (n := KL) (by rcases h.klen with h | h | h <;> omega)
  refine WP.call (k := Proof.Aes.expandKeyRISCV64) Proof.Aes.RISCV64.expandKey_correct h.pre h.reads
    h.writes ?_ expandKey_noFrames
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [Proof.Aes.expandKeyRISCV64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), h.a0, h.a1, h.a2, hK] at hpost
  exact hpost

theorem ek_rel {Kp W S : Addr} {KL : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → EArgs s₁ Kp W S KL ∧ EArgs s₂ Kp W S KL ∧ s₁.sp = s₂.sp) :
    RelCT isa P Impl.CmacAes.Stream.RISCV64.ekCall fun _ _ => True := by
  refine RelCT.call Proof.Aes.RISCV64.expandKey_correct Proof.Aes.RISCV64.expandKey_ct
    [⟨Kp, KL⟩] [⟨W, 240⟩, ⟨S, 512⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [Proof.Aes.expandKeyRISCV64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a3 ∉ linkRegs),
    h₁.a0, h₁.a1, h₁.a2, h₁.a3, h₂.a0, h₂.a1, h₂.a2, h₂.a3, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-! ## Bytes written -/

open VG.WriteBytes

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < 2 ^ 64) :
    writeBytes m q xs (q + BitVec.ofNat 64 i) =
      if i < xs.length then xs.getD i 0 else m (q + BitVec.ofNat 64 i) := by
  simp only [writeBytes, Mem.sub_ofNat_toNat q hi]

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) {xs : List Byte} (h : xs.length < 2 ^ 64) :
    Spec.Aes.bytesAt (writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt])
  intro i h1 _
  simp only [Spec.Aes.bytesAt, List.length_map, List.length_range] at h1
  simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range, writeBytes_at m q xs (by omega : i < 2 ^ 64),
    h1, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    Spec.Aes.bytesAt (writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) =
      Spec.Aes.bytesAt m p r ++ xs := by
  rw [Proof.Cmac.Stream.bytesAt_append, bytesAt_writeBytes_self _ _ (by omega)]
  refine congrArg (· ++ xs) ?_
  simp only [Spec.Aes.bytesAt]
  apply List.map_congr_left
  intro i hi
  exact writeBytes_before m p xs (List.mem_range.mp hi) (by omega)

/-! ## Copying bytes -/

/-- Memory after writing the bytes copied, pointwise, as `writeBytes`. -/
theorem writeBytes_of {m m' : Mem} {C : Addr} {xs : List Byte}
    (hc : ∀ i < xs.length, m' (C + BitVec.ofNat 64 i) = xs.getD i 0) (hf : Frame [⟨C, xs.length⟩] m m') :
    m' = writeBytes m C xs := by
  funext a
  simp only [writeBytes]
  split
  · rename_i h
    have := hc _ h
    rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel] at this
  · rename_i h
    exact hf a fun r hr hc' => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains] at hc'; omega

/-- What `copy` leaves. -/
structure Copied (s : State) (C : Addr) (xs : List Byte) (s' : State) : Prop where
  mem : s'.mem = writeBytes s.mem C xs
  other : ∀ r, r ≠ .t2 → r ≠ .t3 → r ≠ .t5 → r ≠ .t6 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem copy_ok (s : State) {P C : Addr} {L : Nat} (hL : L < 2 ^ 64) (h6 : s.gpr .t6 = P)
    (h5 : s.gpr .t5 = C) (h2 : s.gpr .t2 = BitVec.ofNat 64 L)
    (hr : ∀ i < L, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < L, InRegions s.wr (C + BitVec.ofNat 64 i) 1)
    (hdis : (⟨P, L⟩ : Region).Disjoint ⟨C, L⟩) :
    WP isa Impl.CmacAes.Stream.RISCV64.copy s (Copied s C (Spec.Aes.bytesAt s.mem P L)) := by
  have ev := Steps.eval_zero_ofNat s .t2 hL h2
  by_cases hL0 : L = 0
  · subst hL0
    refine WP.ite true (by rw [ev]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    exact ⟨by simp [Spec.Aes.bytesAt, writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl⟩
  refine WP.ite false (by rw [ev]; simp [hL0]) (fun h => by cases h) fun _ => ?_
  refine WP.mono (copyLoop_ok (tmp := .t3) (src := .t6) (dst := .t5) (cnt := .t2) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) s (N := L) (by omega) hL h2 (by rw [h6]; exact hr)
    (by rw [h5]; exact hw) (fun x h₁ h₂ => ?_)) ?_
  · rw [h5] at h₁; rw [h6] at h₂
    exact hdis x (by simp only [Region.Contains]; omega) (by simp only [Region.Contains]; omega)
  rintro t ⟨hc, hf, hk⟩
  rw [h5, h6] at hc
  rw [h5] at hf
  refine ⟨writeBytes_of (fun i hi => ?_)
    (by rw [Proof.Cmac.bytesAt_length]; exact hf), fun r a b c d => hk.gpr (by simp [a, b, c, d]), hk.2.1, hk.2.2⟩
  rw [Proof.Cmac.bytesAt_length] at hi
  rw [hc i hi, Proof.Cmac.getD_bytesAt _ _ hi]

end VG.Proof.CmacAes.Stream.RISCV64
