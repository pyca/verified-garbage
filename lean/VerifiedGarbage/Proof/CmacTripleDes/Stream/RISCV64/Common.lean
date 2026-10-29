module

import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Calls
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.RISCV64.Align
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.CmacTripleDes.Stream
public import VerifiedGarbage.Spec.Cmac.TripleDesContract
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.RISCV64
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Straight
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Modes.RISCV64.Seq
public import VerifiedGarbage.Proof.TripleDes.RISCV64.Lit
public import VerifiedGarbage.Proof.TripleDes.RISCV64.FeistelLit
public import VerifiedGarbage.Proof.TripleDes.SboxTables
public import VerifiedGarbage.Spec.Cmac
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# Streaming TDEA-CMAC on RISC-V: the contracts and what the functions share

The contracts the code is proved against (`initRISCV64`, `absorbRISCV64`,
`finishRISCV64`), which the shared contracts with the working space
appended (`Proof/CmacTripleDes/StreamScratch.lean`, with the 944 bytes of
stack ECB uses) imply (`Verified.lean`). Then where the registers are saved
(`sv S`, the scratch buffer rounded up to a multiple of 8), the number of
bytes held back as `heldCode` computes it from `count` (`heldCode_wp`), and
`copy`, which copies `cnt` bytes from `src` to `dst`, a byte at a time
(none if `cnt` is 0), changing only `tmp`, `src`, `dst` and `cnt`
(`copy_ok`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.CmacTripleDes.Stream.RISCV64

/-! ## The contracts -/

/-- `vg_cmac_triple_des_stream_init(state = a0, key = a1, key_len = a2, scratch = a3)`. -/
def initRISCV64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 416⟩
    let key : Region := ⟨s.gpr .a1, (s.gpr .a2).toNat⟩
    let scr : Region := ⟨s.gpr .a3, 640⟩
    let stk : Region := ⟨s.sp - 944, 944⟩
    s.rd = [key] ∧ s.wr = [state, scr] ∧
      state.Disjoint key ∧ state.Disjoint scr ∧ key.Disjoint scr ∧
      stk.Disjoint state ∧ stk.Disjoint key ∧ stk.Disjoint scr ∧
      (s.gpr .a0).toNat + 416 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + (s.gpr .a2).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a3).toNat + 640 ≤ 2 ^ 64 ∧ s.sp.toNat % 16 = 0 ∧ 944 ≤ s.sp.toNat ∧
      Spec.TripleDes.validKey (s.gpr .a2).toNat
  post s s' :=
    Spec.Cmac.tdesRepr s'.mem (s.gpr .a0) (Spec.TripleDes.bytesAt s.mem (s.gpr .a1) (s.gpr .a2).toNat) []
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

/-- `vg_cmac_triple_des_absorb(state = a0, count = a1, data = a2, len = a3, scratch = a4)`. -/
def absorbRISCV64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 416⟩
    let data : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let scr : Region := ⟨s.gpr .a4, 688⟩
    let stk : Region := ⟨s.sp - 944, 944⟩
    s.rd = [data] ∧ s.wr = [state, scr] ∧
      state.Disjoint data ∧ state.Disjoint scr ∧ data.Disjoint scr ∧
      stk.Disjoint state ∧ stk.Disjoint data ∧ stk.Disjoint scr ∧
      (s.gpr .a0).toNat + 416 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a4).toNat + 688 ≤ 2 ^ 64 ∧ s.sp.toNat % 16 = 0 ∧ 944 ≤ s.sp.toNat
  post s s' :=
    ∀ key msg, Spec.Cmac.tdesRepr s.mem (s.gpr .a0) key msg →
      s.gpr .a1 = BitVec.ofNat 64 msg.length → msg.length + (s.gpr .a3).toNat < 2 ^ 64 →
      Spec.Cmac.tdesRepr s'.mem (s.gpr .a0) key
        (msg ++ Spec.Aes.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.sp = s₂.sp

/-- `vg_cmac_triple_des_finish(state = a0, count = a1, out = a2, scratch = a3)`. -/
def finishRISCV64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 416⟩
    let out : Region := ⟨s.gpr .a2, 8⟩
    let scr : Region := ⟨s.gpr .a3, 640⟩
    let stk : Region := ⟨s.sp - 944, 944⟩
    s.rd = [] ∧ s.wr = [state, out, scr] ∧
      state.Disjoint out ∧ state.Disjoint scr ∧ out.Disjoint scr ∧
      stk.Disjoint state ∧ stk.Disjoint out ∧ stk.Disjoint scr ∧
      (s.gpr .a0).toNat + 416 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8 ≤ 2 ^ 64 ∧
      (s.gpr .a3).toNat + 640 ≤ 2 ^ 64 ∧ s.sp.toNat % 16 = 0 ∧ 944 ≤ s.sp.toNat
  post s s' :=
    ∀ key msg, Spec.Cmac.tdesRepr s.mem (s.gpr .a0) key msg →
      s.gpr .a1 = BitVec.ofNat 64 msg.length → msg.length < 2 ^ 64 →
      Spec.Aes.bytesAt s'.mem (s.gpr .a2) 8 = Spec.Cmac.tdesCmac key 8 msg
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

/-! ## Arithmetic -/

theorem toNat_ofNat {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem ofNat_toNat_eq {x : BitVec 64} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 64 n :=
  BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (h ▸ x.isLt)])

theorem and7 (x : BitVec 64) : (x &&& BitVec.ofInt 64 7).toNat = x.toNat % 8 := by
  rw [BitVec.toNat_and, show (BitVec.ofInt 64 7).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

open VG.Proof.CmacTripleDes.Stream (held held_pos) in
/-- The number of bytes held back for a nonzero `count`, as `addi -1; andi 7; addi 1` computes it. -/
theorem held_bv (c : BitVec 64) (h : c ≠ 0) :
    ((c - BitVec.ofNat 64 1) &&& BitVec.ofInt 64 7) + BitVec.ofNat 64 1 = BitVec.ofNat 64 (held c.toNat) := by
  have hc : c.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
  rw [held_pos (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, and7, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  have := c.isLt
  omega

theorem preserved_ne (r : Reg) (hr : r ∈ preserved) :
    r ≠ .t0 ∧ r ≠ .t1 ∧ r ≠ .t2 ∧ r ≠ .t3 ∧ r ≠ .t4 ∧ r ≠ .t5 ∧ r ≠ .t6 ∧ r ≠ .ra ∧ r ≠ .a0 ∧
      r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .a3 ∧ r ≠ .a4 ∧ r ≠ .a5 ∧ r ≠ .a6 ∧ r ≠ .a7 := by
  revert hr; cases r <;> decide

/-- Code keeps the stack pointer. -/
theorem wp_sp {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.sp = s.sp := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.sp he⟩

theorem in_wr {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

/-! ## The number of bytes held back -/

open VG.Proof.CmacTripleDes.Stream (held) in
/-- `heldCode` computes, from `count = n` in `a1`, the number of bytes held
back for a message of `n` bytes, to `t0`. -/
theorem heldCode_wp {s : State} {n : Nat} (hn : n < 2 ^ 64) (h1 : s.gpr .a1 = BitVec.ofNat 64 n) :
    WP isa heldCode s fun t => t.gpr .t0 = BitVec.ofNat 64 (held n) ∧
      (∀ r, r ≠ .t0 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have ev := Steps.eval_zero_ofNat s .a1 hn h1
  by_cases h0 : n = 0
  · subst h0
    refine WP.ite true (by rw [ev]; rfl) (fun _ => ?_) (fun h => by cases h)
    refine wp_li (imm := 0) (by decide) fun t u => WP.block_nil ?_
    exact ⟨by rw [u.gpr]; rfl, fun r h => u.other r h, u.mem, u.rd, u.wr, u.sp⟩
  refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => ?_
  refine wp_subi (imm := 1) (by decide) fun t₁ u₁ => wp_andi (by decide) fun t₂ u₂ =>
    wp_addi (imm := 1) (by decide) fun t₃ u₃ => WP.block_nil ?_
  refine ⟨?_, fun r h => by rw [u₃.other r h, u₂.other r h, u₁.other r h], by rw [u₃.mem, u₂.mem, u₁.mem],
    by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr], by rw [u₃.sp, u₂.sp, u₁.sp]⟩
  have hc : s.gpr .a1 ≠ 0 := by
    rw [h1]; intro e; apply h0; have := congrArg BitVec.toNat e; rwa [toNat_ofNat hn] at this
  rw [u₃.gpr, u₂.gpr, u₁.gpr, held_bv _ hc, h1, toNat_ofNat hn]

/-! ## Saving registers -/

/-- Where the functions save the registers, from the scratch buffer `S`: `S`
rounded up to a multiple of 8. -/
abbrev sv (S : Addr) : Addr := S + BitVec.ofNat 64 (Align.pad S)

/-- `t0 :=` the register `n`'s value rounded up. -/
theorem savePtr_ok {s : State} (n : Reg) :
    WP isa (.block (savePtr n)) s (· = s.write .t0 (sv (s.gpr n))) := by
  apply WP.of_runBlock
  simp only [savePtr, runBlock_cons, runStep_some, runBlock_nil, exec_addi (show imm12 7 by decide),
    exec_logicImm (show imm12 (-8) by decide), RegUpd.gpr_write_self, RegUpd.write_write, Option.some.injEq,
    exists_eq_left']
  rw [Align.align_eq]

theorem sv_add (S : Addr) (d : Nat) : sv S + BitVec.ofNat 64 d = S + BitVec.ofNat 64 (Align.pad S + d) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

/-- A slot at `sv S + d`, within the scratch buffer's first 56 bytes. -/
theorem sv_sub (S : Addr) {d n : Nat} (h : d + n ≤ 49) : Region.Sub ⟨sv S + BitVec.ofNat 64 d, n⟩ ⟨S, 56⟩ := by
  have := Align.pad_lt S
  rw [sv_add]; exact Offset.sub_base _ (by omega)

theorem sv_contains (S : Addr) {d n L : Nat} (h : d + n ≤ 49) (hL : 56 ≤ L) :
    (⟨S, L⟩ : Region).Contains (sv S + BitVec.ofNat 64 d) n := by
  have := Align.pad_lt S
  rw [sv_add]; exact Offset.contains_base _ (by omega) (by omega)

/-- Slots holding registers whose values agree hold either's. -/
theorem saved_congr {B : Addr} {g g' : Reg → BitVec 64} {l : List (Reg × Nat)} {m : Mem}
    (h : Spill.Saved B g l m) (hg : ∀ p ∈ l, g p.1 = g' p.1) : Spill.Saved B g' l m :=
  fun p hp => (h p hp).trans (hg p hp)

/-! ## Copying bytes -/

open VG.WriteBytes

/-- What `copy` leaves: the bytes copied, and every register but the
copy's. -/
structure Copied (tmp src dst cnt : Reg) (s : State) (C : Addr) (xs : List Byte) (s' : State) : Prop where
  mem : s'.mem = writeBytes s.mem C xs
  other : ∀ r, r ≠ tmp → r ≠ src → r ≠ dst → r ≠ cnt → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

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

theorem copy_ok {tmp src dst cnt : Reg} (h1 : tmp ≠ src) (h2 : tmp ≠ dst) (h3 : tmp ≠ cnt)
    (h4 : src ≠ dst) (h5 : src ≠ cnt) (h6 : dst ≠ cnt) (s : State) {P C : Addr} {L : Nat} (hL : L < 2 ^ 64)
    (hs : s.gpr src = P) (hd : s.gpr dst = C) (hc : s.gpr cnt = BitVec.ofNat 64 L)
    (hr : ∀ i < L, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < L, InRegions s.wr (C + BitVec.ofNat 64 i) 1)
    (hdis : (⟨P, L⟩ : Region).Disjoint ⟨C, L⟩) :
    WP isa (copy tmp src dst cnt) s (Copied tmp src dst cnt s C (Spec.Aes.bytesAt s.mem P L)) := by
  have ev := Steps.eval_zero_ofNat s cnt hL hc
  by_cases hL0 : L = 0
  · subst hL0
    refine WP.ite true (by rw [ev]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    exact ⟨by simp [Spec.Aes.bytesAt, writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl⟩
  refine WP.ite false (by rw [ev]; simp [hL0]) (fun h => by cases h) fun _ => ?_
  refine WP.mono (copyLoop_ok h1 h2 h3 h4 h5 h6 s (N := L) (by omega) hL hc (by rw [hs]; exact hr)
    (by rw [hd]; exact hw) (fun x hx₁ hx₂ => ?_)) ?_
  · rw [hd] at hx₁; rw [hs] at hx₂
    exact hdis x (by simp only [Region.Contains]; omega) (by simp only [Region.Contains]; omega)
  rintro t ⟨hcp, hf, hk⟩
  rw [hd, hs] at hcp
  rw [hd] at hf
  refine ⟨writeBytes_of (fun i hi => ?_) (by rw [Proof.Cmac.bytesAt_length]; exact hf),
    fun r a b c d => hk.gpr (by simp [a, b, c, d]), hk.2.1, hk.2.2⟩
  rw [Proof.Cmac.bytesAt_length] at hi
  rw [hcp i hi, Proof.Cmac.getD_bytesAt _ _ hi]

/-! ## Zeroing a block -/

/-- The 8 bytes `storeBytes` stores of zeros, at `C`. -/
theorem zeros_stored {s s' : State} {tmp dst : Reg} {doff : Nat} {C : Addr} (hC : s.gpr dst + BitVec.ofNat 64 doff = C)
    (h : Bytes.StoreI tmp dst doff (List.replicate 8 0) s 8 s') :
    Spec.Aes.bytesAt s'.mem C 8 = Spec.Cmac.zeros 8 ∧ Frame [⟨C, 8⟩] s.mem s'.mem := by
  refine ⟨?_, by have := h.frame; rwa [hC, List.length_replicate] at this⟩
  simp only [Spec.Aes.bytesAt, Spec.Cmac.zeros]
  apply List.ext_getElem (by simp)
  intro j h₁ _
  simp only [List.length_map, List.length_range] at h₁
  have := h.stored j h₁
  simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
  rw [← hC, Offset.add_add, this]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, show j < 8 from h₁, ↓reduceIte,
    Option.getD_some]
  rfl


/-! ## Bytes written and read -/

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

/-- The bytes past the first `a`. -/
theorem bytesAt_drop (m : Mem) (p : Addr) {a n : Nat} (h : a ≤ n) :
    (Spec.Aes.bytesAt m p n).drop a = Spec.Aes.bytesAt m (p + BitVec.ofNat 64 a) (n - a) := by
  conv => lhs; rw [show n = a + (n - a) by omega, Proof.Cmac.Stream.bytesAt_append]
  rw [List.drop_append_of_le_length (by simp [Spec.Aes.bytesAt]), List.drop_of_length_le (by simp [Spec.Aes.bytesAt]),
    List.nil_append]

/-- The first `b` bytes past the first `a`. -/
theorem bytesAt_drop_take (m : Mem) (p : Addr) {a b n : Nat} (h : a + b ≤ n) :
    ((Spec.Aes.bytesAt m p n).drop a).take b = Spec.Aes.bytesAt m (p + BitVec.ofNat 64 a) b := by
  rw [bytesAt_drop m p (by omega), show n - a = b + (n - a - b) by omega, Proof.Cmac.Stream.bytesAt_append,
    List.take_append_of_le_length (by simp [Spec.Aes.bytesAt]), List.take_of_length_le (by simp [Spec.Aes.bytesAt])]

/-- The first `a` bytes. -/
theorem bytesAt_take (m : Mem) (p : Addr) {a n : Nat} (h : a ≤ n) :
    (Spec.Aes.bytesAt m p n).take a = Spec.Aes.bytesAt m p a := by
  have := bytesAt_drop_take m p (a := 0) (b := a) (n := n) (by omega)
  rwa [List.drop_zero, BitVec.add_zero] at this

theorem blocksAt_succ (m : Mem) (p : Addr) (k : Nat) :
    Spec.Cmac.blocksAt m p 8 (k + 1) =
      Spec.Cmac.blocksAt m p 8 k ++ [Spec.Aes.bytesAt m (p + BitVec.ofNat 64 (8 * k)) 8] := by
  simp only [Spec.Cmac.blocksAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]

end VG.Proof.CmacTripleDes.Stream.RISCV64
