module

public import VerifiedGarbage.Proof.Sha3.Arm.Permute
public import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Sha3.Arith
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha3.Arm.Permute
meta import VerifiedGarbage.Proof.Sha3.Stream
meta import VerifiedGarbage.Proof.Sha3.Arith
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# The SHA-3 sponge on ARMv7: `absorb`

The same structure as the AArch64 proof
(`VG.Proof.Sha3.AArch64.Stream.Absorb`), with the return address saved in the
scratch space instead of a frame, and the callee-saved registers the code does
not save (`r8`–`r11`) kept by the permutation. An iteration of the loop
absorbs bytes that fit in the block, one byte (`body_block`) or the whole
words left of the data and of the block (`words_ok`, `word_step`), and then
permutes the state if they complete the block (`finish_ok`); or, at the
start of a block with two or more blocks left (`bulkTest_ok`), all the
whole blocks that are left (`bulk_ok`): the state is interleaved in the
scratch space (`enter_call`), each block's lanes are XORed into it
(`xor_step`, by evaluation: `xorSeg_ok`) and the rounds permute it
(`rounds_call`), and it is brought back (`leave_call`).
-/

@[expose] public section

namespace VG.Proof.Sha3.Arm.Stream.Absorb

open VG VG.Arm VG.Impl.Sha3.Arm.Stream
open VG.Proof.Sha3.Arm (saveA_ok restoreA_ok saveMemA saveMemA_frame SSaved ssaved_ok saveMemA_ssaved
  restore_eq call_ok covers_of preserved_cases ofNat32_succ sub_ofNat32 ofNat32_beq_zero sub_beq_zero32
  beq_zero32 xor_setWidth32 ofNat_toNat32 arg_in argByte_eq addr_toNat words_ok shl2_ofNat32 writeW32_apply
  regR sub_imm0 Stored RCs Masks segs segs_ok segs_rate segs_imm xorSeg_ok cfgX ok_offs stw stw_xor
  lane_words wordAddr_eq Hi storeVars storeVars_keep storeVars_frame saveL bulkSave_eq saveL_ok saveMemA_hi
  savedHi_regs readW_above bulkLoad_ok bulkStore_ok bulkRestore_ok wp_geq geq_beq ladder_ok enter_call
  rounds_call leave_call rd64_add rd64_eq)
open VG.Proof.Sha512.Arm (A contains_A rd64 rd64_frame mem_rd)
open VG.Arm.Straight (wordAddr Ok)
open VG.Impl.Sha3.Arm (enterCall roundsCall leaveCall xorSeg)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsl wp_mov wp_add wp_sub wp_subs wp_cmp
  wp_ldr wp_str wp_ldrb wp_strb wp_ldrSp wp_orr eval_eq eval_ne add_ofNat)
open VG.Proof.Sha512.Arm (wp_eor)
open VG.Proof.Sha3 (Rep rep_append xorByte xorAt xorAt_snoc xorAt_single snoc_induction byteOf_xorAt
  byteOf_stateAt ext_bytes stateAt_xorByte stateAt_congr writeW8_apply bytesAt_succ bytesAt_length
  contains_offset ne_of_lt200)
open VG.Spec.Sha3 (stateAt keccakF bytesAt rates)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : BitVec 32 := s₀.gpr .r0
abbrev rt : Nat := (s₀.gpr .r1).toNat
abbrev pos : Nat := (s₀.gpr .r2).toNat
abbrev dp : BitVec 32 := s₀.gpr .r3
abbrev len : Nat := (stackArg s₀ 0).toNat
abbrev scr : BitVec 32 := stackArg s₀ 1
abbrev stA : Addr := State.addr (st s₀)
abbrev dA : Addr := State.addr (dp s₀)
abbrev stR : Region := ⟨stA s₀, 200⟩
abbrev dR : Region := ⟨dA s₀, len s₀⟩
abbrev scR : Region := ⟨State.addr (scr s₀), 640⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 8⟩
/-- The first `c` bytes of data. -/
abbrev D (c : Nat) : List Byte := bytesAt s₀.mem (dA s₀) c

/-- The messages the initial state and position represent. -/
def Msg (msg : List Byte) : Prop :=
  stateAt s₀.mem (stA s₀) = Rep (rt s₀) msg ∧ pos s₀ = msg.length % rt s₀

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀, argR s₀]
  wr : s₀.wr = [stR s₀, scR s₀]
  st_scr : (stR s₀).Disjoint (scR s₀)
  d_st : (dR s₀).Disjoint (stR s₀)
  d_scr : (dR s₀).Disjoint (scR s₀)
  a_st : (argR s₀).Disjoint (stR s₀)
  a_scr : (argR s₀).Disjoint (scR s₀)
  st_fit : (st s₀).toNat + 200 ≤ 2 ^ 32
  d_fit : (dp s₀).toNat + len s₀ ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 640 ≤ 2 ^ 32
  sp_fit : s₀.sp.toNat + 8 ≤ 2 ^ 32
  rate : rt s₀ ∈ rates
  pos_lt : pos s₀ < rt s₀

theorem pre_of {s₀ : State} (h : Proof.Sha3.absorbArm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem Pre.rt_pos {s₀ : State} (hp : Pre s₀) : 0 < rt s₀ ∧ rt s₀ ≤ 168 := by
  obtain h := Proof.Sha3.rate_bounds hp.rate
  omega_using [h]

theorem Pre.arg {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 2) :
    InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 :=
  ⟨argR s₀, by simp [hp.rd], arg_in (n := 2) hp.sp_fit hk⟩

theorem len_lt (s₀ : State) : len s₀ < 2 ^ 32 := (stackArg s₀ 0).isLt

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r0 : s.gpr .r0 = st s₀
  r1 : s.gpr .r1 = scr s₀
  r4 : s.gpr .r4 = s₀.gpr .r1
  r6 : s.gpr .r6 = dp s₀ + BitVec.ofNat 32 c
  r7 : s.gpr .r7 = BitVec.ofNat 32 (len s₀ - c)
  hi : ∀ r ∈ [Reg.r8, .r9, .r10, .r11], s.gpr r = s₀.gpr r
  frame : Frame [stR s₀, scR s₀] s₀.mem s.mem
  saved : SSaved (scr s₀) s₀.gpr s.mem

/-- The loop invariant: the state represents the message followed by the
first `c` bytes of data. -/
structure Inv (s₀ : State) (c : Nat) (s : State) : Prop extends Common s₀ c s where
  r5 : s.gpr .r5 = BitVec.ofNat 32 ((pos s₀ + c) % rt s₀)
  repr : ∀ msg, Msg s₀ msg → stateAt s.mem (stA s₀) = Rep (rt s₀) (msg ++ D s₀ c)

/-- The registers `Common` is about. -/
abbrev kept : List Reg := [.r0, .r1, .r4, .r6, .r7, .r8, .r9, .r10, .r11]

theorem hi_kept : ∀ r ∈ [Reg.r8, .r9, .r10, .r11], r ∈ kept := by decide

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Common s₀ c s)
    (hg : ∀ r ∈ kept, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Common s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  sp := hsp.trans h.sp
  r0 := by rw [hg _ (by simp)]; exact h.r0
  r1 := by rw [hg _ (by simp)]; exact h.r1
  r4 := by rw [hg _ (by simp)]; exact h.r4
  r6 := by rw [hg _ (by simp)]; exact h.r6
  r7 := by rw [hg _ (by simp)]; exact h.r7
  hi := fun r hr => by
    rw [hg r (hi_kept r hr)]
    exact h.hi r hr
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Inv.of_flags {s₀ : State} {c : Nat} {s s' : State} (h : Inv s₀ c s) (u : Fupd s s') :
    Inv s₀ c s' :=
  { h.toCommon.of_gpr (fun r _ => by rw [u.gpr]) u.mem u.rd u.wr u.sp with
    r5 := by rw [u.gpr]; exact h.r5
    repr := by rw [u.mem]; exact h.repr }

theorem hi_ok : ∀ r ∈ [Reg.r8, .r9, .r10, .r11], r ∈ preserved ∧ r ≠ .lr := by decide

/-- A call of the permutation keeps what holds throughout. -/
theorem Common.after_call {s₀ : State} (hp : Pre s₀) {c : Nat} {s s' : State} (h : Common s₀ c s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hcs : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) (h0 : s'.gpr .r0 = st s₀)
    (h1 : s'.gpr .r1 = scr s₀) (hf : Frame [regR (st s₀) 200, regR (scr s₀) 512] s.mem s'.mem) :
    Common s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  sp := hsp.trans h.sp
  r0 := h0
  r1 := h1
  r4 := by rw [hcs _ (by decide) (by decide)]; exact h.r4
  r6 := by rw [hcs _ (by decide) (by decide)]; exact h.r6
  r7 := by rw [hcs _ (by decide) (by decide)]; exact h.r7
  hi := fun r hr => by rw [hcs r (hi_ok r hr).1 (hi_ok r hr).2]; exact h.hi r hr
  frame := h.frame.trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀, by simp, fun _ h => h⟩
    · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega_using [])⟩)
  saved := h.saved.frame hp.scr_fit hp.st_scr hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact hr

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (h : Common s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dA s₀ + BitVec.ofNat 64 i) = s₀.mem (dA s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr⟩) (by have := len_lt s₀; simp; omega_using [this]) hi

/-! ## The prologue -/

theorem setup_eq : setup = .ldrSp .r12 4 :: (saved.map (fun p => Instr.str p.1 .r12 p.2) ++
    ([.mov .r4 (.reg .r1), .mov .r1 (.reg .r12), .mov .r5 (.reg .r2), .mov .r6 (.reg .r3),
      .ldrSp .r7 0, .cmp .r7 (.imm 0)] : List Instr)) := rfl

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block setup) s₀ fun s => Inv s₀ 0 s ∧ s.z = decide (len s₀ = 0) := by
  have fC := hp.scr_fit
  rw [setup_eq]
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) rfl (hp.arg (by omega_using [])) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = scr s₀ := u₁.gpr
  refine saveA_ok saved s₁ _ (fun p hp' => ⟨(ssaved_ok p hp').2.2.1, ?_⟩)
    fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  · rw [u₁.wr, h12, hp.wr]
    exact ⟨scR s₀, by simp, contains_A fC (by have := ssaved_ok p hp'; omega)⟩
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ =>
    wp_mov (op2_reg _ _) fun s₅ u₅ => wp_mov (op2_reg _ _) fun s₆ u₆ => ?_
  obtain hm : s₆.mem = saveMemA s₀.mem (scr s₀) s₁.gpr saved := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂, u₁.mem, h12]
  obtain hf : Frame [regR (scr s₀) 640] s₀.mem s₆.mem := by
    rw [hm]; exact saveMemA_frame fC _ _ _ fun p hp' => by have := ssaved_ok p hp'; omega
  obtain ha : s₆.mem.readW (stackArgAddr s₀ 0) 32 = stackArg s₀ 0 :=
    hf.readW (r := ⟨stackArgAddr s₀ 0, 4⟩) (Region.contains_self _ _)
      (by simpa using hp.a_scr.sub_left (Region.sub_prefix (by omega_using []))) (by decide)
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide)
    (by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]
        exact hp.arg (by omega_using [])) fun s₇ u₇ => ?_
  refine wp_cmp (op2_imm (by decide)) fun s₈ u₈ hz => WP.block_nil ?_
  obtain g : ∀ r, r ≠ .r12 → r ≠ .r4 → r ≠ .r1 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → s₈.gpr r = s₀.gpr r :=
    fun r h12 h4 h1 h5 h6 h7 => by
      rw [u₈.gpr, u₇.other r h7, u₆.other r h6, u₅.other r h5, u₄.other r h1, u₃.other r h4, g₂,
        u₁.other r h12]
  obtain h7 : s₈.gpr .r7 = stackArg s₀ 0 := by rw [u₈.gpr, u₇.gpr, ha]
  refine ⟨⟨⟨Nat.zero_le _, ?_, ?_, ?_, g .r0 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide), ?_, ?_, ?_, by rw [h7, Nat.sub_zero]; exact (ofNat_toNat32 _).symm, fun r hr => ?_,
    ?_, ?_⟩, ?_, fun msg ⟨hs, _⟩ => ?_⟩, ?_⟩
  · rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  · rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]
  · rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]
  · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), g₂, h12]
  · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, g₂, u₁.other _ (by decide)]
  · rw [u₈.gpr, u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
    rw [BitVec.add_zero]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [u₈.mem, u₇.mem]; exact hf.mono (by simp)
  · rw [u₈.mem, u₇.mem, hm]
    exact (saveMemA_ssaved _ fC _).of_gpr fun r hr => u₁.other r hr
  · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), g₂, u₁.other _ (by decide), Nat.add_zero, Nat.mod_eq_of_lt hp.pos_lt]
    exact (ofNat_toNat32 _).symm
  · rw [u₈.mem, u₇.mem, show D s₀ 0 = [] by simp [bytesAt], List.append_nil, ← hs]
    exact stateAt_congr fun i hi =>
      hf.bytes (R := stR s₀) (by simpa using hp.st_scr.sub_right (Region.sub_prefix (Nat.le_refl _)))
        (by simp) hi
  · rw [hz, u₇.gpr, ha]; simp only [sub_imm0]; rw [beq_zero32]

/-! ## Bytes XORed into the state -/

/-- The bytes `c … c + n - 1` follow the first `c`. -/
theorem bytesAt_add (m : Mem) (p : Addr) (c : Nat) :
    ∀ n, bytesAt m p (c + n) = bytesAt m p c ++ bytesAt m (p + BitVec.ofNat 64 c) n
  | 0 => by simp [bytesAt]
  | n + 1 => by
    rw [← Nat.add_assoc, bytesAt_succ, bytesAt_add m p c n, bytesAt_succ, List.append_assoc, add_ofNat]

theorem bytesAt_one (m : Mem) (p : Addr) : bytesAt m p 1 = [m p] := by
  simp [bytesAt]

theorem bytesAt_getD (m : Mem) (p : Addr) {n d : Nat} (hd : d < n) :
    (bytesAt m p n).getD d 0 = m (p + BitVec.ofNat 64 d) := by
  simp [bytesAt, hd]

theorem xorAt_nil (A : Spec.Sha3.State) (j : Nat) : xorAt A j [] = A := by
  simp [xorAt]

/-- Bytes XORed in after others. -/
theorem xorAt_append (A : Spec.Sha3.State) (j : Nat) (bs : List Byte) :
    ∀ cs : List Byte, xorAt (xorAt A j bs) (j + bs.length) cs = xorAt A j (bs ++ cs) := by
  intro cs
  induction cs using snoc_induction with
  | h0 => rw [xorAt_nil, List.append_nil]
  | hs cs b ih =>
    rw [xorAt_snoc, ih, ← List.append_assoc, xorAt_snoc, List.length_append, Nat.add_assoc]

/-- A word of a state in memory XORed with the word at `q`: its four bytes
XORed with the bytes at `q`. -/
theorem stateAt_xor_word (m : Mem) (p q : Addr) {j : Nat} (hj : j + 4 ≤ 200) :
    stateAt (m.writeW (p + BitVec.ofNat 64 j) (m.readW q 32 ^^^ m.readW (p + BitVec.ofNat 64 j) 32)) p =
      xorAt (stateAt m p) j (bytesAt m q 4) :=
  ext_bytes fun i hi => by
    rw [byteOf_xorAt _ _ _ hi, byteOf_stateAt _ _ hi, byteOf_stateAt _ _ hi, bytesAt_length,
      writeW32_apply, Offset.sub_toNat' p (by omega_using [hj]) (by omega_using [hi])]
    by_cases c : j ≤ i ∧ i < j + 4
    · have hd : i - j < 4 := by omega_using [c]
      rw [ite_eq_left c, ite_eq_left c.1, ite_eq_left hd, BitVec.extractLsb'_xor,
        ← Mem.readW_byte _ _ hd, ← Mem.readW_byte _ _ hd, bytesAt_getD _ _ hd, add_ofNat,
        Nat.add_sub_cancel' c.1, BitVec.xor_comm]
    · rw [ite_eq_right c]
      by_cases c' : j ≤ i
      · rw [ite_eq_left c', ite_eq_right (by omega_using [c, c'])]
      · rw [ite_eq_right c', ite_eq_right (by omega_using [hi, hj, c'])]

/-! ## One iteration -/

theorem kept_tmp : ∀ r ∈ kept, r ∉ [Reg.r2, .r3, .r12, .lr] := by decide

/-- The invariant does not depend on the temporaries or the flags. -/
theorem Inv.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Inv s₀ c s)
    (hg : ∀ r, r ∉ [Reg.r2, .r3, .r12, .lr] → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) : Inv s₀ c s' :=
  { h.toCommon.of_gpr (fun r hr => hg r (kept_tmp r hr)) hm hrd hwr hsp with
    r5 := by rw [hg _ (by decide)]; exact h.r5
    repr := by rw [hm]; exact h.repr }

theorem body_regs : ∀ r ∈ [Reg.r8, .r9, .r10, .r11], r ∉ [Reg.r2, .r3, .r12, .r6, .r5, .r7] := by decide

/-- One byte: the byte at position `j` XORed in. -/
theorem body_block {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < len s₀) {s : State}
    (hI : Inv s₀ c s) :
    WP isa (.block absorbByte) s fun s' =>
      Common s₀ (c + 1) s' ∧ s'.gpr .r5 = BitVec.ofNat 32 ((pos s₀ + c) % rt s₀ + 1) ∧
      s'.z = decide ((pos s₀ + c) % rt s₀ + 1 = rt s₀) ∧
      stateAt s'.mem (stA s₀) = xorByte (stateAt s.mem (stA s₀)) ((pos s₀ + c) % rt s₀)
        (s₀.mem (dA s₀ + BitVec.ofNat 64 c)) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  obtain hl := len_lt s₀
  have fS := hp.st_fit
  have fD := hp.d_fit
  obtain hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  generalize hjd : (pos s₀ + c) % rt s₀ = j at hj ⊢
  obtain hr5 : s.gpr .r5 = BitVec.ofNat 32 j := by rw [hI.r5, hjd]
  unfold absorbByte
  refine wp_ldrb (a := dA s₀ + BitVec.ofNat 64 c) (by decide)
    (by rw [hI.r6]; rw [BitVec.add_zero]; exact addr_add (by omega_using [hc, fD]))
    ⟨dR s₀, by simp [hI.rd, hp.rd], contains_offset (by omega_using [hc]) (by omega_using [hc, hl])⟩ fun s₁ u₁ => ?_
  refine wp_add (op2_reg _ _) fun s₂ u₂ => ?_
  obtain ea : State.addr (s₂.gpr .r3 + BitVec.ofNat 32 0) = stA s₀ + BitVec.ofNat 64 j := by
    rw [u₂.gpr, u₁.other .r0 (by decide), u₁.other .r5 (by decide), hI.r0, hr5]
    rw [BitVec.add_zero]
    exact addr_add (by omega_using [hr₁, fS, hj])
  obtain hsin : ∀ rs : List Region, stR s₀ ∈ rs → InRegions rs (stA s₀ + BitVec.ofNat 64 j) 1 :=
    fun rs h => ⟨stR s₀, h, contains_offset (by omega_using [hr₁, hj]) (by omega_using [hr₁, hj])⟩
  refine wp_ldrb (a := stA s₀ + BitVec.ofNat 64 j) (by decide) ea
    (hsin _ (by simp [u₂.rd, u₂.wr, u₁.rd, u₁.wr, hI.rd, hI.wr, hp.wr])) fun s₃ u₃ => ?_
  refine wp_eor (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_strb (a := stA s₀ + BitVec.ofNat 64 j) (by decide)
    (by rw [u₄.other .r3 (by decide), u₃.other .r3 (by decide)]; exact ea)
    (hsin _ (by simp [u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr, hp.wr])) fun s₅ g₅ => ?_
  refine wp_add (op2_imm (by decide)) fun s₆ u₆ => wp_add (op2_imm (by decide)) fun s₇ u₇ =>
    wp_sub (op2_imm (by decide)) fun s₈ u₈ => wp_cmp (op2_reg _ _) fun s₉ u₉ hz => WP.block_nil ?_
  -- The byte stored.
  obtain hv : (s₄.gpr .r2).setWidth 8 =
      s₀.mem (dA s₀ + BitVec.ofNat 64 c) ^^^ s.mem (stA s₀ + BitVec.ofNat 64 j) := by
    rw [u₄.gpr, u₃.other .r2 (by decide), u₂.other .r2 (by decide), u₁.gpr, u₃.gpr, u₂.mem, u₁.mem,
      xor_setWidth32, hI.data hp hc]
  obtain hm₉ : s₉.mem = s.mem.writeW (stA s₀ + BitVec.ofNat 64 j)
      (s₀.mem (dA s₀ + BitVec.ofNat 64 c) ^^^ s.mem (stA s₀ + BitVec.ofNat 64 j)) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, g₅.mem, hv, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain hf : Frame [stR s₀] s.mem s₉.mem := by
    rw [hm₉]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (by omega_using [hr₁, hj]) (by omega_using [hr₁, hj]))
  obtain g : ∀ r, r ∉ [Reg.r2, .r3, .r12, .r6, .r5, .r7] → s₉.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h2, h3, h12, h6, h5, h7⟩ := hr
    rw [u₉.gpr, u₈.other r h7, u₇.other r h5, u₆.other r h6, g₅.gpr, u₄.other r h2, u₃.other r h12,
      u₂.other r h3, u₁.other r h2]
  obtain h5 : s₈.gpr .r5 = BitVec.ofNat 32 (j + 1) := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), g₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hr5, ofNat32_succ]
  obtain h4 : s₈.gpr .r4 = s₀.gpr .r1 := by
    rw [← u₉.gpr, g .r4 (by decide), hI.r4]
  refine ⟨⟨by omega_using [hc], ?_, ?_, ?_, by rw [g .r0 (by decide), hI.r0], by rw [g .r1 (by decide), hI.r1],
    by rw [u₉.gpr, h4], ?_, ?_, fun r hr => by rw [g r (body_regs r hr)]; exact hI.hi r hr,
    hI.frame.trans (hf.mono (by simp)),
    hI.saved.frame hp.scr_fit hp.st_scr hf fun r hr => .inl (List.mem_singleton.mp hr)⟩,
    by rw [u₉.gpr, h5], by rw [hz, h5, h4, sub_beq_zero32 (by omega_using [hr₁, hj])], ?_⟩
  · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, g₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, g₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  · rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, g₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, hI.sp]
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r6, BitVec.add_assoc, ofNat32_succ]
  · rw [u₉.gpr, u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r7, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      sub_ofNat32 (by omega_using [hc]), Nat.sub_sub]
  · refine stateAt_xorByte (by omega_using [hr₁, hj]) ?_ fun i hi hij => ?_
    · rw [hm₉, writeW8_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl), BitVec.xor_comm]
    · rw [hm₉, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (ne_of_lt200 hi (by omega_using [hr₁, hj]) hij))]

/-! ## Whole words -/

/-- In the words of an iteration that began with `c` bytes consumed, at the
position `j` and with the state `S`: after `w` of its `nw` words. The bytes
left and the position are already those after the words. -/
structure WInv (s₀ : State) (c j nw : Nat) (S : Spec.Sha3.State) (w : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r0 : s.gpr .r0 = st s₀
  r1 : s.gpr .r1 = scr s₀
  r3 : s.gpr .r3 = st s₀ + BitVec.ofNat 32 (j + 4 * w)
  r4 : s.gpr .r4 = s₀.gpr .r1
  r5 : s.gpr .r5 = BitVec.ofNat 32 (j + 4 * nw)
  r6 : s.gpr .r6 = dp s₀ + BitVec.ofNat 32 (c + 4 * w)
  r7 : s.gpr .r7 = BitVec.ofNat 32 (len s₀ - (c + 4 * nw))
  lr : s.gpr .lr = BitVec.ofNat 32 (nw - w)
  hi : ∀ r ∈ [Reg.r8, .r9, .r10, .r11], s.gpr r = s₀.gpr r
  frame : Frame [stR s₀, scR s₀] s₀.mem s.mem
  saved : SSaved (scr s₀) s₀.gpr s.mem
  state : stateAt s.mem (stA s₀) =
    xorAt S (j) (bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 c) (4 * w))

/-- Before the words. -/
theorem wordsPre_ok {s₀ : State} {c nw : Nat} (h4 : c + 4 * nw ≤ len s₀) {s : State} (hI : Inv s₀ c s)
    (hlr : s.gpr .lr = BitVec.ofNat 32 nw) :
    WP isa (.block wordsPre) s (WInv s₀ c ((pos s₀ + c) % rt s₀) nw (stateAt s.mem (stA s₀)) 0) := by
  unfold wordsPre
  refine wp_sub (op2_lsl (by decide)) fun s₁ u₁ => wp_add (op2_reg _ _) fun s₂ u₂ =>
    wp_add (op2_lsl (by decide)) fun s₃ u₃ => WP.block_nil ?_
  obtain g : ∀ r, r ≠ .r7 → r ≠ .r3 → r ≠ .r5 → s₃.gpr r = s.gpr r := fun r a b c => by
    rw [u₃.other r c, u₂.other r b, u₁.other r a]
  obtain gm : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine ⟨by rw [u₃.rd, u₂.rd, u₁.rd, hI.rd], by rw [u₃.wr, u₂.wr, u₁.wr, hI.wr],
    by rw [u₃.sp, u₂.sp, u₁.sp, hI.sp], by rw [g _ (by decide) (by decide) (by decide), hI.r0],
    by rw [g _ (by decide) (by decide) (by decide), hI.r1], ?_,
    by rw [g _ (by decide) (by decide) (by decide), hI.r4], ?_,
    by rw [g _ (by decide) (by decide) (by decide), hI.r6, Nat.mul_zero, Nat.add_zero], ?_,
    by rw [g _ (by decide) (by decide) (by decide), hlr, Nat.sub_zero], fun r hr => ?_,
    by rw [gm]; exact hI.frame, by rw [gm]; exact hI.saved, ?_⟩
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), hI.r0, hI.r5,
      Nat.mul_zero, Nat.add_zero]
  · rw [u₃.gpr, u₂.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      u₁.other _ (by decide), hI.r5, hlr, shl2_ofNat32, ← BitVec.ofNat_add]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hI.r7, hlr, shl2_ofNat32,
      sub_ofNat32 (by omega_using [h4]), Nat.sub_sub]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      (rw [g _ (by decide) (by decide) (by decide)]; exact hI.hi _ (by simp))
  · rw [gm, Nat.mul_zero, show bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 c) 0 = [] by simp [bytesAt],
      xorAt_nil]

/-- The data is unchanged. -/
theorem WInv.data {s₀ : State} (hp : Pre s₀) {c j nw w : Nat} {S : Spec.Sha3.State} {s : State}
    (h : WInv s₀ c j nw S w s) {i : Nat} (hi : i < len s₀) :
    s.mem (dA s₀ + BitVec.ofNat 64 i) = s₀.mem (dA s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr⟩) (by have := len_lt s₀; simp; omega_using [this]) hi

theorem word_regs : ∀ r ∈ [Reg.r8, .r9, .r10, .r11], r ≠ .r2 ∧ r ≠ .r12 ∧ r ≠ .r6 ∧ r ≠ .r3 ∧ r ≠ .lr := by
  decide

/-- One word: the four bytes at position `j + 4 w` XORed in. -/
theorem word_step {s₀ : State} (hp : Pre s₀) {c j nw w : Nat} {S : Spec.Sha3.State} (hw : w < nw)
    (h4 : c + 4 * nw ≤ len s₀) (hj4 : j + 4 * nw ≤ rt s₀) {s : State}
    (hW : WInv s₀ c j nw S w s) :
    WP isa (.block absorbWord) s fun s' =>
      WInv s₀ c j nw S (w + 1) s' ∧ s'.z = decide (nw - (w + 1) = 0) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  obtain hl := len_lt s₀
  have fS := hp.st_fit
  have fD := hp.d_fit
  obtain cd : (dR s₀).Contains (dA s₀ + BitVec.ofNat 64 (c + 4 * w)) 4 :=
    contains_offset (by omega_using [hw, h4]) (by omega_using [hw, h4, hl])
  obtain cs : (stR s₀).Contains (stA s₀ + BitVec.ofNat 64 (j + 4 * w)) 4 :=
    contains_offset (by omega_using [hw, hj4, hr₁]) (by omega_using [hw, hj4, hr₁])
  unfold absorbWord
  refine wp_ldr (a := dA s₀ + BitVec.ofNat 64 (c + 4 * w)) (by decide)
    (by rw [hW.r6, BitVec.add_zero]; exact addr_add (by omega_using [hw, h4, fD]))
    ⟨dR s₀, by simp [hW.rd, hp.rd], cd⟩ fun s₁ u₁ => ?_
  refine wp_ldr (a := stA s₀ + BitVec.ofNat 64 (j + 4 * w)) (by decide)
    (by rw [u₁.other _ (by decide), hW.r3, BitVec.add_zero]; exact addr_add (by omega_using [hw, hj4, hr₁, fS]))
    ⟨stR s₀, by simp [u₁.rd, u₁.wr, hW.wr, hp.wr], cs⟩ fun s₂ u₂ => ?_
  refine wp_eor (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_str (a := stA s₀ + BitVec.ofNat 64 (j + 4 * w)) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hW.r3, BitVec.add_zero]
        exact addr_add (by omega_using [hw, hj4, hr₁, fS]))
    ⟨stR s₀, by simp [u₃.wr, u₂.wr, u₁.wr, hW.wr, hp.wr], cs⟩ fun s₄ g₄ => ?_
  refine wp_add (op2_imm (by decide)) fun s₅ u₅ => wp_add (op2_imm (by decide)) fun s₆ u₆ =>
    wp_subs (op2_imm (by decide)) fun s₇ u₇ hz => WP.block_nil ?_
  obtain hm : s₇.mem = s.mem.writeW (stA s₀ + BitVec.ofNat 64 (j + 4 * w))
      (s.mem.readW (dA s₀ + BitVec.ofNat 64 (c + 4 * w)) 32 ^^^
        s.mem.readW (stA s₀ + BitVec.ofNat 64 (j + 4 * w)) 32) := by
    rw [u₇.mem, u₆.mem, u₅.mem, g₄.mem, u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem, u₃.mem,
      u₂.mem, u₁.mem]
  obtain hf : Frame [stR s₀] s.mem s₇.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ cs
  obtain g : ∀ r, r ≠ .r2 → r ≠ .r12 → r ≠ .r6 → r ≠ .r3 → r ≠ .lr → s₇.gpr r = s.gpr r :=
    fun r a b c d e => by
      rw [u₇.other r e, u₆.other r d, u₅.other r c, g₄.gpr, u₃.other r a, u₂.other r b, u₁.other r a]
  obtain hlr : s₆.gpr .lr = BitVec.ofNat 32 (nw - w) := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), g₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hW.lr]
  obtain e1 : BitVec.ofNat 32 (nw - w) - 1 = BitVec.ofNat 32 (nw - (w + 1)) := by
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat32 (by omega_using [hw]), Nat.sub_sub]
  obtain hd : bytesAt s.mem (dA s₀ + BitVec.ofNat 64 (c + 4 * w)) 4 =
      bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 c + BitVec.ofNat 64 (4 * w)) 4 := by
    simp only [bytesAt, add_ofNat]
    exact List.map_congr_left fun d hd' =>
      hW.data hp (by have := List.mem_range.mp hd'; omega_using [hw, h4, this])
  refine ⟨⟨by rw [u₇.rd, u₆.rd, u₅.rd, g₄.rd, u₃.rd, u₂.rd, u₁.rd, hW.rd],
    by rw [u₇.wr, u₆.wr, u₅.wr, g₄.wr, u₃.wr, u₂.wr, u₁.wr, hW.wr],
    by rw [u₇.sp, u₆.sp, u₅.sp, g₄.sp, u₃.sp, u₂.sp, u₁.sp, hW.sp],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), hW.r0],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), hW.r1], ?_,
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), hW.r4],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), hW.r5], ?_,
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), hW.r7],
    by rw [u₇.gpr, hlr, e1], fun r hr => ?_, hW.frame.trans (hf.mono (by simp)),
    hW.saved.frame hp.scr_fit hp.st_scr hf fun r hr => .inl (List.mem_singleton.mp hr), ?_⟩,
    by rw [hz, hlr, e1, ofNat32_beq_zero (by omega_using [hw, h4, hl])]⟩
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), g₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hW.r3, BitVec.add_assoc,
      show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ← BitVec.ofNat_add,
      show j + 4 * w + 4 = j + 4 * (w + 1) by omega_using []]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, g₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hW.r6, BitVec.add_assoc,
      show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ← BitVec.ofNat_add,
      show c + 4 * w + 4 = c + 4 * (w + 1) by omega_using []]
  · obtain ⟨a, b, c', d, e⟩ := word_regs r hr
    rw [g r a b c' d e]; exact hW.hi r hr
  · rw [hm, stateAt_xor_word _ _ _ (by omega_using [hw, hj4, hr₁]), hW.state, hd,
      show j + 4 * w = j + (bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 c) (4 * w)).length by
        rw [bytesAt_length],
      xorAt_append, ← bytesAt_add, show 4 * w + 4 = 4 * (w + 1) by omega_using []]

/-- After the words: Z is set if they complete the block. -/
theorem wordsPost_ok {s₀ : State} (hp : Pre s₀) {c j nw : Nat} {S : Spec.Sha3.State}
    (h4 : c + 4 * nw ≤ len s₀) (hj4 : j + 4 * nw ≤ rt s₀) {s : State}
    (hW : WInv s₀ c j nw S nw s) :
    WP isa (.block [.cmp .r5 (.reg .r4)]) s fun s' =>
      Common s₀ (c + 4 * nw) s' ∧ s'.gpr .r5 = BitVec.ofNat 32 (j + 4 * nw) ∧
      s'.z = decide (j + 4 * nw = rt s₀) ∧
      stateAt s'.mem (stA s₀) =
        xorAt S (j) (bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 c) (4 * nw)) := by
  have ⟨_, hr₁⟩ := hp.rt_pos
  refine wp_cmp (op2_reg _ _) fun s₁ u₁ hz => WP.block_nil ⟨⟨h4, u₁.rd.trans hW.rd, u₁.wr.trans hW.wr,
    u₁.sp.trans hW.sp, by rw [u₁.gpr, hW.r0], by rw [u₁.gpr, hW.r1], by rw [u₁.gpr, hW.r4],
    by rw [u₁.gpr, hW.r6], by rw [u₁.gpr, hW.r7], fun r hr => by rw [u₁.gpr]; exact hW.hi r hr,
    by rw [u₁.mem]; exact hW.frame, by rw [u₁.mem]; exact hW.saved⟩, by rw [u₁.gpr, hW.r5], ?_,
    by rw [u₁.mem]; exact hW.state⟩
  rw [hz, hW.r5, hW.r4, sub_beq_zero32 (by omega_using [hj4, hr₁])]

/-! ## The end of an iteration -/

/-- The test at the end of the body. -/
theorem cmp_ok {s₀ : State} {c : Nat} {s : State} (hI : Inv s₀ c s) :
    WP isa (.block [.cmp .r7 (.imm 0)]) s fun s' => Inv s₀ c s' ∧ s'.z = decide (len s₀ - c = 0) :=
  wp_cmp (op2_imm (by decide)) fun s' u hz => WP.block_nil ⟨hI.of_flags u, by
    rw [hz, hI.r7]; simp only [sub_imm0]; rw [ofNat32_beq_zero (by have := len_lt s₀; omega_using [this])]⟩

theorem kept_r5 : ∀ r ∈ kept, r ≠ .r5 := by decide

/-- After `k` bytes that fit in the block are XORed in: the permutation, if
they complete the block. -/
theorem finish_ok {s₀ : State} (hp : Pre s₀) {c k : Nat} (hk : 0 < k)
    (hjk : (pos s₀ + c) % rt s₀ + k ≤ rt s₀) {s s₁ : State} (hI : Inv s₀ c s)
    (hC : Common s₀ (c + k) s₁) (h5 : s₁.gpr .r5 = BitVec.ofNat 32 ((pos s₀ + c) % rt s₀ + k))
    (hz : s₁.z = decide ((pos s₀ + c) % rt s₀ + k = rt s₀))
    (hst : stateAt s₁.mem (stA s₀) = xorAt (stateAt s.mem (stA s₀)) ((pos s₀ + c) % rt s₀)
      (bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 c) k)) :
    WP isa (.ite .eq (.seq (.block [.mov .r5 (.imm 0)]) permuteCall) (.block [])) s₁
      (Inv s₀ (c + k)) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  -- The representation after absorbing the bytes.
  obtain hlen : ∀ msg, Msg s₀ msg → (msg ++ D s₀ c).length % rt s₀ = (pos s₀ + c) % rt s₀ :=
    fun msg ⟨_, hpm⟩ => by rw [List.length_append, bytesAt_length, hpm, Nat.mod_add_mod]
  obtain hrep : ∀ msg, Msg s₀ msg → Rep (rt s₀) (msg ++ D s₀ (c + k)) =
      if (pos s₀ + c) % rt s₀ + k = rt s₀ then keccakF (stateAt s₁.mem (stA s₀))
      else stateAt s₁.mem (stA s₀) := fun msg hm => by
    rw [D, bytesAt_add, ← List.append_assoc,
      rep_append hr₀ (by omega_using [hr₁]) _ _ (by rw [bytesAt_length]; exact hk)
        (by rw [hlen msg hm, bytesAt_length]; exact hjk),
      hlen msg hm, bytesAt_length, hst, hI.repr msg hm]
  obtain hpc : (pos s₀ + (c + k)) % rt s₀ = if (pos s₀ + c) % rt s₀ + k = rt s₀ then 0
      else (pos s₀ + c) % rt s₀ + k := by
    obtain e := Nat.div_add_mod (pos s₀ + c) (rt s₀)
    rw [show pos s₀ + (c + k) = (pos s₀ + c) + k by omega_using []]
    generalize (pos s₀ + c) % rt s₀ = j at e hjk ⊢
    generalize (pos s₀ + c) / rt s₀ = q at e
    rw [← e]
    split
    · rw [Nat.add_assoc, ‹j + k = rt s₀›, ← Nat.mul_succ, Nat.mul_mod_right]
    · rw [Nat.add_assoc, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega_arith)]
  refine WP.ite (decide ((pos s₀ + c) % rt s₀ + k = rt s₀))
    (by show VG.Arm.eval .eq s₁ = _; rw [eval_eq, hz]) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine WP.seq (wp_mov (op2_imm (by decide)) fun s₂ u₂ => WP.block_nil ?_)
    obtain hC₂ := hC.of_gpr (fun r hr => u₂.other r (kept_r5 r hr)) u₂.mem u₂.rd u₂.wr u₂.sp
    refine call_ok (st := st s₀) (scr := scr s₀) hC₂.r0 hC₂.r1 hp.st_fit
      (by have := hp.scr_fit; omega_using [this]) (hp.st_scr.sub_right (Region.sub_prefix (by omega_using [])))
      (by rw [hC₂.wr, hp.wr]; exact covers_of (N := 640) (by omega_using []) (by simp) (by simp))
      fun s₃ rd₃ wr₃ sp₃ cs₃ r0₃ r1₃ f₃ e₃ => ?_
    refine { hC₂.after_call hp rd₃ wr₃ sp₃ cs₃ r0₃ r1₃ f₃ with r5 := ?_, repr := fun msg hm => ?_ }
    · rw [cs₃ _ (by decide) (by decide), u₂.gpr, hpc, ite_eq_left_of_eq_true _ _ (eq_true hb)]; rfl
    · rw [e₃, u₂.mem, hrep msg hm, ite_eq_left_of_eq_true _ _ (eq_true hb)]
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.block_nil { hC with r5 := ?_, repr := fun msg hm => ?_ }
    · rw [h5, hpc, ite_eq_right_of_eq_false _ _ (eq_false hb)]
    · rw [hrep msg hm, ite_eq_right_of_eq_false _ _ (eq_false hb)]

/-! ## Several blocks between one `enter` and one `leave` -/

theorem shl1_toNat32 (x : BitVec 32) : x <<< 1 = BitVec.ofNat 32 (2 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_using []

/-- Whether a register that is zero or all ones, ORed with a position, is zero. -/
theorem bulk_beq {c : Prop} [Decidable c] {j : Nat} (hj : j < 2 ^ 32) :
    (((if c then 0#32 else BitVec.allOnes 32) ||| BitVec.ofNat 32 j) - 0 == 0) = decide (c ∧ j = 0) := by
  by_cases h : c
  · rw [ite_eq_left h, BitVec.zero_or, sub_imm0, ofNat32_beq_zero hj]; simp [h]
  · rw [ite_eq_right h, BitVec.allOnes_or, sub_imm0, decide_eq_false (fun hc => h hc.1)]; decide

/-- The test at the start of the body: Z is set at the start of a block, if
two blocks of data are left. -/
theorem bulkTest_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (hI : Inv s₀ c s) :
    WP isa (.block absorbBulkTest) s fun s' => Inv s₀ c s' ∧
      s'.z = decide (2 * rt s₀ ≤ len s₀ - c ∧ (pos s₀ + c) % rt s₀ = 0) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  obtain hl := len_lt s₀
  obtain hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  unfold absorbBulkTest
  refine wp_geq (x := BitVec.ofNat 32 (len s₀ - c)) (y := BitVec.ofNat 32 (2 * rt s₀)) (by decide)
    (by decide) hI.r7 (fun s' h => by rw [op2_lsl (by decide), h _ (by decide), hI.r4, shl1_toNat32])
    fun s₁ g₁ o₁ m₁ rd₁ wr₁ sp₁ => ?_
  refine wp_orr (op2_reg _ _) fun s₂ u₂ => wp_cmp (op2_imm (by decide)) fun s₃ u₃ hz =>
    WP.block_nil ⟨?_, ?_⟩
  · refine hI.of_gpr (fun r hr => ?_) (by rw [u₃.mem, u₂.mem, m₁]) (by rw [u₃.rd, u₂.rd, rd₁])
      (by rw [u₃.wr, u₂.wr, wr₁]) (by rw [u₃.sp, u₂.sp, sp₁])
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₃.gpr, u₂.other r hr.2.1, o₁ r hr.2.1 hr.1]
  · rw [hz, u₂.gpr, g₁, o₁ .r5 (by decide) (by decide), hI.r5, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_using [hr₁]), Nat.mod_eq_of_lt (by omega_using [hl]),
      bulk_beq (by omega_using [hj, hr₁])]

/-- A lane, from its bytes. -/
theorem lane_ext {x y : BitVec 64} (h : ∀ k < 8, x.extractLsb' (8 * k) 8 = y.extractLsb' (8 * k) 8) :
    x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  have := congrArg (fun z : Byte => z.getLsbD (b % 8)) (h (b / 8) (by omega_using [hb]))
  simp only [BitVec.getLsbD_extractLsb', show b % 8 < 8 by omega_using [], decide_true, Bool.true_and,
    show 8 * (b / 8) + b % 8 = b by omega_using []] at this
  exact this

/-- The lanes of a state after `n` lanes of memory are XORed into it from
its start. -/
theorem xorAt_lane (K : Spec.Sha3.State) (m : Mem) (q : Addr) (n : Nat) {j : Nat} (hj : j < 25) :
    (xorAt K 0 (bytesAt m q (8 * n)))[j]! =
      if j < n then K[j]! ^^^ m.readW (q + BitVec.ofNat 64 (8 * j)) 64 else K[j]! := by
  rw [getElem!_pos _ j hj, getElem!_pos K j hj]
  by_cases h : j < n
  · rw [ite_eq_left h]
    refine lane_ext fun k hk => ?_
    rw [← Proof.Sha3.byteOf_eq _ hj hk, byteOf_xorAt _ _ _ (by omega_using [hj, hk]), bytesAt_length,
      ite_eq_left (by omega_using [h, hk]), BitVec.extractLsb'_xor, Proof.Sha3.byteOf_eq _ hj hk,
      Nat.sub_zero, bytesAt_getD _ _ (by omega_using [h, hk])]
    refine congrArg (_ ^^^ ·) ?_
    simp only [Mem.readW]
    rw [show (m.read (q + BitVec.ofNat 64 (8 * j)) (64 / 8)).setWidth 64 =
        m.read (q + BitVec.ofNat 64 (8 * j)) 8 from BitVec.setWidth_eq _,
      Mem.extractLsb'_read m _ hk, add_ofNat]
  · rw [ite_eq_right h]
    refine lane_ext fun k hk => ?_
    rw [← Proof.Sha3.byteOf_eq _ hj hk, byteOf_xorAt _ _ _ (by omega_using [hj, hk]), bytesAt_length,
      ite_eq_right (by omega_using [h, hk]), Proof.Sha3.byteOf_eq _ hj hk]

theorem Pre.scr_in {s₀ : State} (hp : Pre s₀) {s : State} (hwr : s.wr = s₀.wr) {d : Nat}
    (hd : d + 4 ≤ 640) : InRegions s.wr (A (scr s₀) d) 4 := by
  rw [hwr, hp.wr]; exact ⟨scR s₀, by simp, contains_A hp.scr_fit hd⟩

theorem Pre.covers {s₀ : State} (hp : Pre s₀) {s : State} (hwr : s.wr = s₀.wr) :
    Covers [regR (st s₀) 200, regR (scr s₀) 512] s.wr := by
  rw [hwr, hp.wr]; exact covers_of (N := 640) (by omega_using []) (by simp) (by simp)

/-- Between `enter` and `leave`, at the start of a block, after `c` bytes of
data: the interleaved state represents the message followed by them. -/
structure BInv (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  pos0 : (pos s₀ + c) % rt s₀ = 0
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r0 : s.gpr .r0 = st s₀
  r1 : s.gpr .r1 = scr s₀
  frame : Frame [stR s₀, scR s₀] s₀.mem s.mem
  hi : Hi (scr s₀) s₀.gpr (s₀.gpr .r1) (dp s₀ + BitVec.ofNat 32 c) (BitVec.ofNat 32 (len s₀ - c)) s.mem
  rcs : RCs (scr s₀) s.mem
  state : ∃ K, Stored s.mem (scr s₀) K ∧ ∀ msg, Msg s₀ msg → K = Rep (rt s₀) (msg ++ D s₀ c)

/-- While the lanes of the block at `c` are XORed into the interleaved
state `K`, from the state `s₁`: after `n` lanes. -/
structure XInv (s₀ : State) (c : Nat) (K : Spec.Sha3.State) (s₁ : State) (n : Nat) (s : State) :
    Prop where
  le : 8 * n ≤ rt s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r0 : s.gpr .r0 = st s₀
  r1 : s.gpr .r1 = scr s₀
  r9 : s.gpr .r9 = dp s₀ + BitVec.ofNat 32 (c + 8 * n)
  r10 : s.gpr .r10 = s₀.gpr .r1
  r11 : s.gpr .r11 = BitVec.ofNat 32 (len s₀ - c)
  masks : Masks s
  words : ∀ j < 21, ∀ h < 2, s.mem.readW (wordAddr (scr s₀) (2 * j + h)) 32 =
    stw (if j < n then K[j]! ^^^ rd64 s₀.mem (dp s₀) (c + 8 * j) else K[j]!) j h
  frame : Frame [regR (scr s₀) 168] s₁.mem s.mem

theorem XInv.of_flags {s₀ : State} {c : Nat} {K : Spec.Sha3.State} {s₁ : State} {n : Nat} {s s' : State}
    (h : XInv s₀ c K s₁ n s) (u : Fupd s s') : XInv s₀ c K s₁ n s' where
  le := h.le
  rd := u.rd.trans h.rd
  wr := u.wr.trans h.wr
  sp := u.sp.trans h.sp
  r0 := by rw [u.gpr]; exact h.r0
  r1 := by rw [u.gpr]; exact h.r1
  r9 := by rw [u.gpr]; exact h.r9
  r10 := by rw [u.gpr]; exact h.r10
  r11 := by rw [u.gpr]; exact h.r11
  masks := by have := h.masks; unfold Masks at this ⊢; rw [u.gpr]; exact this
  words := by rw [u.mem]; exact h.words
  frame := by rw [u.mem]; exact h.frame

/-- A run of lanes of the block, and `r9` after them. -/
theorem xor_step {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c + rt s₀ ≤ len s₀) {K : Spec.Sha3.State}
    {s₁ : State} (hf₁ : Frame [stR s₀, scR s₀] s₀.mem s₁.mem) (p : Nat × Nat) (hpm : p ∈ segs)
    (ha : p.1 = 0 ∨ rt s₀ ≠ 8 * p.1) (s : State) (hX : XInv s₀ c K s₁ p.1 s) (rest : List Instr)
    (Q : State → Prop) (k : ∀ s', XInv s₀ c K s₁ p.2 s' → WP isa (.block rest) s' Q) :
    WP isa (.block (xorSeg p.1 p.2 ++
      .dp .add .r9 .r9 (.imm (BitVec.ofNat 32 (8 * (p.2 - p.1)))) :: rest)) s Q := by
  have hb : 8 * p.2 ≤ rt s₀ := segs_rate hp.rate _ hpm ha hX.le
  obtain ⟨hab, hb21, hn⟩ := segs_ok _ hpm
  have himm := (segs_imm _ hpm).1
  obtain ⟨a, b⟩ := p
  have fD := hp.d_fit
  have fC := hp.scr_fit
  have hok : Ok (cfgX (b - a)) s :=
    ok_offs (lb := 640) (le := len s₀) (ob := 0) (oe := c + 8 * a)
      (show s.gpr .r1 = scr s₀ + BitVec.ofNat 32 0 by rw [hX.r1]; simp) hX.r9
      (by rw [hX.wr, hp.wr]; simp) (by rw [hX.rd, hp.rd]; simp) fC fD
      (show 0 + 4 * 42 ≤ 640 by decide)
      (show c + 8 * a + 4 * (2 * (b - a)) ≤ len s₀ by
        have h₁ : a ≤ b := hab
        have h₂ : 8 * b ≤ rt s₀ := hb
        omega_using [hc, h₁, h₂])
      hp.d_scr.symm
  obtain ⟨s', hs', hw, rd', wr', sp', g1, g9, go, f⟩ := xorSeg_ok hpm hok hX.masks
  rw [hX.r1, hX.r9] at hw
  rw [hX.r1] at f
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s', hs', ?_⟩
  refine wp_add (op2_imm himm) fun s₂ u₂ => k s₂ ?_
  have dataF : ∀ o, o + 8 ≤ len s₀ → rd64 s.mem (dp s₀) o = rd64 s₀.mem (dp s₀) o := fun o ho => by
    rw [rd64_frame hX.frame (N := len s₀) (fun r hr => ?_) fD ho,
      rd64_frame hf₁ (N := len s₀) (fun r hr => ?_) fD ho]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.d_st
      · exact hp.d_scr
    · rw [List.mem_singleton.mp hr]
      exact hp.d_scr.sub_right (Region.sub_prefix (by decide))
  obtain ⟨m4, m5, m6, m7, m8⟩ := hX.masks
  refine {
    le := hb, rd := by rw [u₂.rd, rd', hX.rd], wr := by rw [u₂.wr, wr', hX.wr],
    sp := by rw [u₂.sp, sp', hX.sp], r0 := by rw [u₂.other _ (by decide), go _ (by decide), hX.r0],
    r1 := by rw [u₂.other _ (by decide), g1, hX.r1], r9 := ?_,
    r10 := by rw [u₂.other _ (by decide), go _ (by decide), hX.r10],
    r11 := by rw [u₂.other _ (by decide), go _ (by decide), hX.r11],
    masks := ⟨by rw [u₂.other _ (by decide), go _ (by decide), m4],
      by rw [u₂.other _ (by decide), go _ (by decide), m5],
      by rw [u₂.other _ (by decide), go _ (by decide), m6],
      by rw [u₂.other _ (by decide), go _ (by decide), m7],
      by rw [u₂.other _ (by decide), go _ (by decide), m8]⟩,
    words := fun j hj h hh => ?_, frame := by rw [u₂.mem]; exact hX.frame.trans f }
  · have h₁ : a ≤ b := hab
    rw [u₂.gpr, g9, hX.r9, Straight.add_ofNat_ofNat, show c + 8 * a + 8 * (b - a) = c + 8 * b by omega_using [h₁]]
  · have h₂ : 8 * b ≤ rt s₀ := hb
    rw [u₂.mem, hw j hj h hh, hX.words j hj h hh]
    by_cases hr : a ≤ j ∧ j < b
    · rw [ite_eq_left hr, ite_eq_right (show ¬ j < a by omega_using [hr]), ite_eq_left hr.2, stw_xor,
        lane_words, rd64_add, show c + 8 * a + 8 * (j - a) = c + 8 * j by omega_using [hr],
        dataF _ (by omega_using [hr, h₂, hc])]
    · rw [ite_eq_right hr]
      by_cases hja : j < a
      · rw [ite_eq_left hja, ite_eq_left (show j < b by have h₁ : a ≤ b := hab; omega_using [hja, h₁])]
      · rw [ite_eq_right hja, ite_eq_right (show ¬ j < b by omega_using [hr, hja])]

/-- A block: its lanes XORed into the interleaved state, which the rounds
then permute; and Z is set if another block of data is left. -/
theorem block_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (hB : BInv s₀ c s)
    (hc : c + rt s₀ ≤ len s₀) :
    WP isa (.seq (.block bulkLoad) (.seq (ladder xorSeg) (.seq (.block bulkStore)
      (.seq roundsCall (.block absorbBlockTest))))) s fun s' =>
      BInv s₀ (c + rt s₀) s' ∧ s'.z = decide (rt s₀ ≤ len s₀ - (c + rt s₀)) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  obtain hl := len_lt s₀
  have fC := hp.scr_fit
  have fD := hp.d_fit
  obtain ⟨n, hn, hn21⟩ : ∃ n, rt s₀ = 8 * n ∧ n ≤ 21 := by
    have := hp.rate
    simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at this
    exact ⟨rt s₀ / 8, by omega_using [this], by omega_using [this]⟩
  obtain ⟨K, hK, hrep⟩ := hB.state
  refine WP.seq ?_
  rw [← List.append_nil bulkLoad]
  refine bulkLoad_ok hB.r1 (fun d hd => hp.scr_in hB.wr hd)
    fun s₁ hm h9 h10 h11 g0 g1 m₁ rd₁ wr₁ sp₁ => WP.block_nil ?_
  rw [hB.hi.ptr] at h9
  rw [hB.hi.rate] at h10
  rw [hB.hi.left] at h11
  have hf₁ : Frame [stR s₀, scR s₀] s₀.mem s₁.mem := by rw [m₁]; exact hB.frame
  have hX₀ : XInv s₀ c K s₁ 0 s₁ := {
    le := Nat.zero_le _, rd := rd₁.trans hB.rd, wr := wr₁.trans hB.wr, sp := sp₁.trans hB.sp,
    r0 := g0.trans hB.r0, r1 := g1, r9 := by rw [h9, Nat.mul_zero, Nat.add_zero], r10 := h10,
    r11 := h11, masks := hm,
    words := fun j hj h hh => by
      rw [m₁, ite_eq_right (Nat.not_lt_zero _)]; exact hK j (by omega_using [hj]) h hh,
    frame := Frame.refl _ _ }
  refine WP.seq (WP.mono (ladder_ok (P := XInv s₀ c K s₁) (rt := rt s₀)
    (fun a s h => by rw [h.r10]; exact (ofNat_toNat32 _).symm) (fun a s s' h u => h.of_flags u)
    (fun p hpm ha s hX rest Q k => xor_step hp hc hf₁ p hpm ha s hX rest Q k) hp.rate hX₀)
    fun s₂ hX => ?_)
  rw [show rt s₀ / 8 = n by omega_using [hn]] at hX
  -- The interleaved state after the block.
  have hK₂ : Stored s₂.mem (scr s₀) (xorAt K 0 (bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 c) (8 * n))) := by
    intro j hj h hh
    rw [xorAt_lane _ _ _ _ hj]
    by_cases hj21 : j < 21
    · rw [hX.words j hj21 h hh]
      by_cases hjn : j < n
      · rw [ite_eq_left hjn, ite_eq_left hjn, rd64_eq _ (by omega_using [hjn, hn, hc, fD]), add_ofNat]
      · rw [ite_eq_right hjn, ite_eq_right hjn]
    · rw [ite_eq_right (by omega_using [hj21, hn21]), wordAddr_eq,
        readW_above fC hX.frame (by omega_using [hj21]) (by omega_using [hj, hh]), m₁, ← wordAddr_eq]
      exact hK j hj h hh
  have keep₂ : ∀ d, 168 ≤ d → d + 4 ≤ 640 → s₂.mem.readW (A (scr s₀) d) 32 = s.mem.readW (A (scr s₀) d) 32 :=
    fun d h₁ h₂ => by rw [readW_above fC hX.frame h₁ h₂, m₁]
  refine WP.seq ?_
  rw [← List.append_nil bulkStore]
  refine bulkStore_ok hX.r1 (fun d hd => hp.scr_in hX.wr hd)
    fun s₃ e11 o₃ m₃ rd₃ wr₃ sp₃ => WP.block_nil ?_
  have e9 : s₂.gpr .r9 = dp s₀ + BitVec.ofNat 32 (c + rt s₀) := by rw [hX.r9, hn]
  have el : s₂.gpr .r11 - s₂.gpr .r10 = BitVec.ofNat 32 (len s₀ - (c + rt s₀)) := by
    rw [hX.r11, hX.r10, ← ofNat_toNat32 (s₀.gpr .r1),
      sub_ofNat32 (show rt s₀ ≤ len s₀ - c by omega_using [hc]), Nat.sub_sub]
  rw [el, hX.r10, e9] at m₃
  have hH₃ : Hi (scr s₀) s₀.gpr (s₀.gpr .r1) (dp s₀ + BitVec.ofNat 32 (c + rt s₀))
      (BitVec.ofNat 32 (len s₀ - (c + rt s₀))) s₃.mem := by
    rw [m₃]
    exact (hB.hi.keep fun d h₁ h₂ => keep₂ d (by omega_using [h₁]) h₂).store fC _ _ _
  have hK₃ : Stored s₃.mem (scr s₀) (xorAt K 0 (bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 c) (8 * n))) :=
    hK₂.keep fun d hd => by rw [m₃]; exact storeVars_keep _ fC _ _ _ (by omega_using [hd]) (.inl (by omega_using [hd]))
  have hrc₃ : RCs (scr s₀) s₃.mem :=
    (hB.rcs.keep fun d h₁ h₂ => keep₂ d (by omega_using [h₁]) (by omega_using [h₂])).keep fun d h₁ h₂ => by
      rw [m₃]; exact storeVars_keep _ fC _ _ _ (by omega_using [h₂]) (.inl (by omega_using [h₂]))
  have hf₃ : Frame [stR s₀, scR s₀] s₀.mem s₃.mem := by
    refine (hf₁.trans (hX.frame.sub fun r hr => ⟨scR s₀, by simp, ?_⟩)).trans ?_
    · rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)
    · rw [m₃]; exact (storeVars_frame _ fC _ _ _).mono fun r hr => by rw [List.mem_singleton.mp hr]; simp
  have r0₃ : s₃.gpr .r0 = st s₀ := by rw [o₃ _ (by decide), hX.r0]
  have r1₃ : s₃.gpr .r1 = scr s₀ := by rw [o₃ _ (by decide), hX.r1]
  refine WP.seq (rounds_call r0₃ r1₃ hp.st_fit (by omega_using [fC])
    (hp.st_scr.sub_right (Region.sub_prefix (by decide))) (hp.covers (wr₃.trans hX.wr)) hK₃ hrc₃
    fun s₄ rd₄ wr₄ sp₄ r0₄ r1₄ f₄ hK₄ hrc₄ _ => ?_)
  have hH₄ := hH₃.frame fC hp.st_scr f₄ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact hr
  have rw₄ : s₄.rd = s₀.rd ∧ s₄.wr = s₀.wr :=
    ⟨by rw [rd₄, rd₃, hX.rd], by rw [wr₄, wr₃, hX.wr]⟩
  unfold absorbBlockTest
  refine wp_ldr (a := A (scr s₀) vLeft) (by decide) (by rw [r1₄])
    (by rw [rw₄.1, rw₄.2, ← hX.rd, ← hX.wr]; exact mem_rd (hp.scr_in hX.wr (by decide))) fun s₅ u₅ => ?_
  refine wp_ldr (a := A (scr s₀) vRate) (by decide) (by rw [u₅.other .r1 (by decide), r1₄])
    (by rw [u₅.rd, u₅.wr, rw₄.1, rw₄.2, ← hX.rd, ← hX.wr]; exact mem_rd (hp.scr_in hX.wr (by decide)))
    fun s₆ u₆ => ?_
  refine wp_geq (d := .r12) (n := .r2) (x := BitVec.ofNat 32 (len s₀ - (c + rt s₀)))
    (y := BitVec.ofNat 32 (rt s₀)) (by decide) (by decide)
    (by rw [u₆.other .r2 (by decide), u₅.gpr, hH₄.left])
    (fun s' h => by rw [op2_reg, h .r3 (by decide), u₆.gpr, u₅.mem, hH₄.rate, ofNat_toNat32])
    fun s₇ g₇ o₇ m₇ rd₇ wr₇ sp₇ => ?_
  refine wp_cmp (op2_imm (by decide)) fun s₈ u₈ hz => WP.block_nil ⟨?_, ?_⟩
  · have em : s₈.mem = s₄.mem := by rw [u₈.mem, m₇, u₆.mem, u₅.mem]
    have eg : ∀ r, r ≠ .r12 → r ≠ .r2 → r ≠ .r3 → s₈.gpr r = s₄.gpr r := fun r a b c' => by
      rw [u₈.gpr, o₇ r a b, u₆.other r c', u₅.other r b]
    refine {
      c_le := hc, pos0 := by rw [← Nat.add_assoc, Nat.add_mod_right]; exact hB.pos0,
      rd := by rw [u₈.rd, rd₇, u₆.rd, u₅.rd, rw₄.1], wr := by rw [u₈.wr, wr₇, u₆.wr, u₅.wr, rw₄.2],
      sp := by rw [u₈.sp, sp₇, u₆.sp, u₅.sp, sp₄, sp₃, hX.sp],
      r0 := by rw [eg _ (by decide) (by decide) (by decide), r0₄],
      r1 := by rw [eg _ (by decide) (by decide) (by decide), r1₄],
      frame := by
        rw [em]
        exact hf₃.trans (f₄.sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact ⟨stR s₀, by simp, fun _ h => h⟩
          · exact ⟨scR s₀, by simp, Region.sub_prefix (by decide)⟩),
      hi := by rw [em]; exact hH₄, rcs := by rw [em]; exact hrc₄,
      state := ⟨_, by rw [em]; exact hK₄, fun msg hm => ?_⟩ }
    obtain hlen : (msg ++ D s₀ c).length % rt s₀ = 0 := by
      rw [List.length_append, bytesAt_length, ← Nat.mod_add_mod, ← hm.2]; exact hB.pos0
    rw [D, bytesAt_add, ← List.append_assoc,
      rep_append hr₀ (by omega_using [hr₁]) _ _ (by rw [bytesAt_length]; exact hr₀)
        (by rw [hlen, bytesAt_length]; omega_using []),
      hlen, bytesAt_length, ite_eq_left (Nat.zero_add _), ← hrep msg hm, hn]
  · rw [hz, g₇, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hr₁]),
      Nat.mod_eq_of_lt (by omega_using [hl]), geq_beq]

/-- The whole blocks of the data, from the start of a block with two or
more left: they absorb `k > 0` more bytes. -/
theorem bulk_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (hI : Inv s₀ c s)
    (h2 : 2 * rt s₀ ≤ len s₀ - c) (h0 : (pos s₀ + c) % rt s₀ = 0) :
    WP isa absorbBulk s fun s' => ∃ k, 0 < k ∧ c + k ≤ len s₀ ∧ Inv s₀ (c + k) s' := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have fC := hp.scr_fit
  have fC' : (scr s₀).toNat + 512 ≤ 2 ^ 32 := by omega_using [fC]
  have hd' := hp.st_scr.sub_right (Region.sub_prefix (show 512 ≤ 640 by decide))
  unfold absorbBulk
  refine WP.seq ?_
  rw [bulkSave_eq]
  refine saveA_ok saveL s _ (fun p hp' => ⟨(saveL_ok p hp').1, by
    rw [hI.r1]; exact hp.scr_in hI.wr (by have := saveL_ok p hp'; omega)⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => WP.block_nil ?_
  rw [hI.r1] at m₁
  have hH₁ : Hi (scr s₀) s₀.gpr (s₀.gpr .r1) (dp s₀ + BitVec.ofNat 32 c) (BitVec.ofNat 32 (len s₀ - c))
      s₁.mem := by
    have h := saveMemA_hi fC hI.saved s.gpr (fun p hp' => hI.hi p.1 (savedHi_regs p hp'))
    rw [hI.r4, hI.r6, hI.r7, ← m₁] at h
    exact h
  have f₁ : Frame [regR (scr s₀) 640] s.mem s₁.mem := by
    rw [m₁]; exact saveMemA_frame fC _ _ _ fun p hp' => by have := saveL_ok p hp'; omega
  have hst₁ : stateAt s₁.mem (stA s₀) = stateAt s.mem (stA s₀) :=
    stateAt_congr fun i hi =>
      f₁.bytes (R := stR s₀) (by simpa using hp.st_scr) (by simp) hi
  refine WP.seq (enter_call (st := st s₀) (scr := scr s₀) (by rw [g₁]; exact hI.r0)
    (by rw [g₁]; exact hI.r1) hp.st_fit fC' hd' (hp.covers (wr₁.trans hI.wr))
    fun s₂ rd₂ wr₂ sp₂ r0₂ r1₂ f₂ hK₂ hrc₂ => ?_)
  rw [hst₁] at hK₂
  have hB₂ : BInv s₀ c s₂ := {
    c_le := hI.c_le, pos0 := h0, rd := by rw [rd₂, rd₁, hI.rd], wr := by rw [wr₂, wr₁, hI.wr],
    sp := by rw [sp₂, sp₁, hI.sp], r0 := r0₂, r1 := r1₂,
    frame := hI.frame.trans ((f₁.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp).trans
      (f₂.sub fun r hr => ⟨scR s₀, by simp, by
        rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩)),
    hi := hH₁.frame fC hp.st_scr (rs := [regR (scr s₀) 512])
      (f₂.sub fun r hr => ⟨regR (scr s₀) 512, by simp, by
        rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩)
      (fun r hr => .inr (List.mem_singleton.mp hr)),
    rcs := hrc₂, state := ⟨_, hK₂, fun msg hm => hI.repr msg hm⟩ }
  refine WP.seq (WP.mono (Q := fun s' => ∃ k, 0 < k ∧ BInv s₀ (c + k) s') ?_ fun s₃ ⟨k, hk, hB₃⟩ => ?_)
  · refine WP.loop (M := isa)
      (fun n s => ∃ c', n = len s₀ - c' ∧ c ≤ c' ∧ c' + rt s₀ ≤ len s₀ ∧ BInv s₀ c' s) ?_ (len s₀ - c) s₂
      ⟨c, rfl, Nat.le_refl _, by omega_using [h2, hr₀], hB₂⟩
    rintro n s ⟨c', rfl, hcc, hcl, hB⟩
    refine WP.mono (block_ok hp hB hcl) fun s' ⟨hB', hz'⟩ => ?_
    by_cases he : rt s₀ ≤ len s₀ - (c' + rt s₀)
    · exact .inr ⟨by show VG.Arm.eval .eq s' = _; rw [eval_eq, hz', decide_eq_true he],
        len s₀ - (c' + rt s₀), by omega_using [hcl, hr₀], c' + rt s₀, rfl, by omega_using [hcc],
        by omega_using [he, hcl], hB'⟩
    · refine .inl ⟨by show VG.Arm.eval .eq s' = _; rw [eval_eq, hz', decide_eq_false he],
        c' + rt s₀ - c, by omega_using [hcc, hr₀], ?_⟩
      rw [show c + (c' + rt s₀ - c) = c' + rt s₀ by omega_using [hcc]]; exact hB'
  obtain ⟨K, hK, hrep⟩ := hB₃.state
  refine WP.seq (leave_call (st := st s₀) (scr := scr s₀) hB₃.r0 hB₃.r1 hp.st_fit fC' hd'
    (hp.covers hB₃.wr) hK fun s₄ rd₄ wr₄ sp₄ r0₄ r1₄ f₄ hst₄ => ?_)
  have hH₄ := hB₃.hi.frame fC hp.st_scr f₄ (fun r hr => .inl (List.mem_singleton.mp hr))
  refine bulkRestore_ok r1₄ (fun d hd => hp.scr_in (wr₄.trans hB₃.wr) hd) hH₄
    fun s' e4 e5 e6 e7 e8 e0 e1 em erd ewr esp => ⟨k, hk, hB₃.c_le, ?_⟩
  exact {
    c_le := hB₃.c_le, rd := by rw [erd, rd₄, hB₃.rd], wr := by rw [ewr, wr₄, hB₃.wr],
    sp := by rw [esp, sp₄, hB₃.sp], r0 := e0.trans r0₄, r1 := e1, r4 := e4, r6 := e6, r7 := e7,
    hi := e8,
    frame := by
      rw [em]; exact hB₃.frame.trans (f₄.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp),
    saved := by rw [em]; exact hH₄.saved, r5 := by rw [e5, hB₃.pos0]; rfl,
    repr := fun msg hm => by rw [em, hst₄, hrep msg hm] }

/-- The bytes that are left of the block, or of the data: `k > 0` more bytes. -/
theorem step_ok {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < len s₀) {s : State} (hI : Inv s₀ c s) :
    WP isa absorbStep s fun s' => ∃ k, 0 < k ∧ c + k ≤ len s₀ ∧ Inv s₀ (c + k) s' := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  obtain hl := len_lt s₀
  obtain hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  unfold absorbStep
  refine WP.seq (WP.mono (words_ok (l := len s₀ - c) (j := (pos s₀ + c) % rt s₀) (rt := rt s₀) hI.r7
    hI.r5 (by rw [hI.r4]; exact (ofNat_toNat32 _).symm) (by omega_using [hl]) (by omega_using [hj])
    (by omega_using [hr₁])) fun s₁ ⟨g₁, m₁, rd₁, wr₁, sp₁, hlr, hz₁⟩ => ?_)
  obtain hI₁ := hI.of_gpr g₁ m₁ rd₁ wr₁ sp₁
  generalize hnw : min (len s₀ - c) (rt s₀ - (pos s₀ + c) % rt s₀) / 4 = nw at hlr hz₁
  obtain h4 : c + 4 * nw ≤ len s₀ := by omega_using [hnw, hc]
  obtain hj4 : (pos s₀ + c) % rt s₀ + 4 * nw ≤ rt s₀ := by omega_using [hnw, hj]
  refine WP.seq (WP.ite (decide (nw = 0)) (by show VG.Arm.eval .eq s₁ = _; rw [eval_eq, hz₁])
    (fun _ => ?_) (fun hb => ?_))
  · refine WP.mono (body_block hp hc hI₁) fun s₂ ⟨hC, h5, hz, hst⟩ => ?_
    refine WP.mono (finish_ok hp (k := 1) (by decide) (by omega_using [hj]) hI₁ hC h5 hz
      (by rw [hst, bytesAt_one, xorAt_single])) fun s' h => ⟨1, by decide, by omega_using [hc], h⟩
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.seq (WP.mono (wordsPre_ok h4 hI₁ hlr) fun s₂ hW => ?_)
    refine WP.seq (WP.mono (Q := WInv s₀ c ((pos s₀ + c) % rt s₀) nw (stateAt s₁.mem (stA s₀)) nw) ?_
      fun s₃ hW₃ =>
      WP.mono (wordsPost_ok hp h4 hj4 hW₃) fun s₄ ⟨hC, h5, hz, hst⟩ =>
        WP.mono (finish_ok hp (k := 4 * nw) (by omega_using [hb]) hj4 hI₁ hC h5 hz hst) fun s' h =>
          ⟨4 * nw, by omega_using [hb], h4, h⟩)
    refine WP.loop (M := isa)
      (fun n s => ∃ w, n = nw - w ∧ w < nw ∧
        WInv s₀ c ((pos s₀ + c) % rt s₀) nw (stateAt s₁.mem (stA s₀)) w s) ?_ nw s₂
      ⟨0, rfl, by omega_using [hb], hW⟩
    rintro n s ⟨w, rfl, hw, hWs⟩
    refine WP.mono (word_step hp hw h4 hj4 hWs) fun s' ⟨hW', hz'⟩ => ?_
    by_cases he : nw - (w + 1) = 0
    · refine .inl ⟨by show VG.Arm.eval .ne s' = _; rw [eval_ne, hz', decide_eq_true he]; rfl, ?_⟩
      rwa [show w + 1 = nw by omega_using [hw, he]] at hW'
    · exact .inr ⟨by show VG.Arm.eval .ne s' = _; rw [eval_ne, hz', decide_eq_false he]; rfl,
        nw - (w + 1), by omega_using [hw], w + 1, rfl, by omega_using [he], hW'⟩

/-- The whole body: it absorbs `k > 0` more bytes. -/
theorem body_ok {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < len s₀) {s : State} (hI : Inv s₀ c s) :
    WP isa absorbBody s fun s' => ∃ k, 0 < k ∧ c + k ≤ len s₀ ∧ Inv s₀ (c + k) s' ∧
      s'.z = decide (len s₀ - (c + k) = 0) := by
  unfold absorbBody
  refine WP.seq (WP.mono (bulkTest_ok hp hI) fun s₁ ⟨hI₁, hz₁⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s' => ∃ k, 0 < k ∧ c + k ≤ len s₀ ∧ Inv s₀ (c + k) s') ?_
    fun s₂ ⟨k, hk, hck, hI₂⟩ => WP.mono (cmp_ok hI₂) fun s' h => ⟨k, hk, hck, h⟩)
  refine WP.ite (decide (2 * rt s₀ ≤ len s₀ - c ∧ (pos s₀ + c) % rt s₀ = 0))
    (by show VG.Arm.eval .eq s₁ = _; rw [eval_eq, hz₁]) (fun hb => ?_) (fun _ => step_ok hp hc hI₁)
  simp only [decide_eq_true_eq] at hb
  exact bulk_ok hp hI₁ hb.1 hb.2

/-! ## The epilogue -/

/-- The epilogue's postcondition. -/
def Post (s₀ s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha3.absorbArm.post s₀ s'

theorem hi_not_saved : ∀ r ∈ [Reg.r8, .r9, .r10, .r11], r ∉ saved.map Prod.fst ∧ r ≠ .r0 := by decide

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (hI : Inv s₀ (len s₀) s) :
    WP isa (.block epilogue) s (Post s₀) := by
  have ⟨hr₀, _⟩ := hp.rt_pos
  have fC := hp.scr_fit
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => ?_
  rw [restore_eq, ← List.append_nil (saved.map _)]
  refine restoreA_ok saved s₁ _ (by decide) (fun p hp' => ⟨(ssaved_ok p hp').1, (ssaved_ok p hp').2.2.1,
    ?_⟩) fun s' ho hr hm => WP.block_nil ⟨fun r hr' => ?_, fun msg hm' hpm => ?_, ?_⟩
  · rw [u₁.rd, u₁.wr, u₁.other .r1 (by decide), hI.rd, hI.wr, hI.r1, hp.wr]
    exact ⟨scR s₀, by simp, contains_A fC (by have := ssaved_ok p hp'; omega)⟩
  · rcases preserved_cases r hr' with ⟨p, hp', rfl⟩ | hr''
    · rw [ho p hp', u₁.other .r1 (by decide), hI.r1, u₁.mem]; exact hI.saved p hp'
    · rw [hr r (hi_not_saved r hr'').1, u₁.other r (hi_not_saved r hr'').2]; exact hI.hi r hr''
  · rw [Proof.Sha3.repr_iff, hm, u₁.mem]
    exact hI.repr msg ⟨hm', hpm⟩
  · rw [hr .r0 (by decide), u₁.gpr, hI.r5, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := Nat.mod_lt (pos s₀ + len s₀) hr₀; omega_arith)]

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) : WP isa absorb s₀ (Post s₀) := by
  obtain hl := len_lt s₀
  unfold absorb
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨hI, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := Inv s₀ (len s₀)) ?_ fun s₂ hI₂ => epilogue_ok hp hI₂)
  refine WP.ite (decide (len s₀ = 0)) (by show VG.Arm.eval .eq s₁ = _; rw [eval_eq, hz])
    (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (M := isa) (hb ▸ hI)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun n s => ∃ c, n = len s₀ - c ∧ c < len s₀ ∧ Inv s₀ c s) ?_ (len s₀) s₁
      ⟨0, rfl, by omega_using [hb], hI⟩
    rintro n s ⟨c, rfl, hcl, hI⟩
    refine WP.mono (body_ok hp hcl hI) fun s' ⟨k, hk, hck, hI', hz'⟩ => ?_
    by_cases he : len s₀ - (c + k) = 0
    · refine .inl ⟨by show VG.Arm.eval .ne s' = _; rw [eval_ne, hz', decide_eq_true he]; rfl, ?_⟩
      rwa [show c + k = len s₀ by omega_using [hck, he]] at hI'
    · exact .inr ⟨by show VG.Arm.eval .ne s' = _; rw [eval_ne, hz', decide_eq_false he]; rfl,
        len s₀ - (c + k), by omega_using [hcl, hk], c + k, rfl, by omega_using [he], hI'⟩

/-! ## Constant time -/

/-- The initial taint: the register arguments are public, `r0` points at the
state, and the 8 bytes of stack arguments are public, the second one
pointing at the scratch space. -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [200, 640], bases := [(.r0, 0)],
    argLen := 8, argBases := [(4, 1)] }

theorem wf₀ {s : State} (h : Proof.Sha3.absorbArm.pre s) : VG.Arm.Taint.Wf τ₀ s := by
  obtain hp := pre_of h
  obtain hst := hp.st_fit; have hsc := hp.scr_fit
  refine ⟨fun _ => ⟨by simp [hp.wr, τ₀], by simpa [hp.wr] using hp.st_scr, ?_⟩, ?_,
    fun _ => ⟨hp.sp_fit, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr_toNat] <;> omega_arith
  · intro p hp'; simp only [τ₀, List.mem_singleton] at hp'; subst hp'
    simp [VG.Arm.Taint.region, hp.wr]
  · have e : (⟨State.addr s.sp, 8⟩ : Region) = argR s := by simp [stackArgAddr]
    simp only [τ₀, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.a_st
    · exact hp.a_scr
  · intro p hp'; simp only [τ₀, List.mem_singleton] at hp'; subst hp'
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha3.absorbArm.pre s₁) (h₂ : Proof.Sha3.absorbArm.pre s₂)
    (hpub : Proof.Sha3.absorbArm.pub s₁ s₂) : VG.Arm.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨psp, p0, p1, p2, p3, a0, a1⟩ := hpub
  obtain hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp,
    fun k hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [stR, scR, stA, scr, st, p0, a1]
  · simp only [τ₀] at hk
    rw [argByte_eq hp₁.sp_fit hk, argByte_eq hp₂.sp_fit hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega_using [])), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega_using []))]
    have : k / 4 = 0 ∨ k / 4 = 1 := by omega_using [hk]
    rcases this with h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1

/-- A state satisfying the precondition (with no data, and the scratch space at 0). -/
def sat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 72 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0, 0⟩, ⟨0x4000, 8⟩]
  wr := [⟨0x1000, 200⟩, ⟨0, 640⟩]

theorem absorb_verified : Verified Arm.target absorb Proof.Sha3.absorbArm := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩
  · exact VG.Taint.constantTime (A := VG.Arm.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp)
      (by taint_decide_weak VG.Proof.Sha3.Arm.dropRC)
  · have e : ∀ k, stackArg sat k = 0 := fun k => by
      simp [stackArg, sat, Mem.readW, Mem.read]
    refine ⟨sat, ?_⟩
    simp only [Proof.Sha3.absorbArm, e]
    refine ⟨by simp [sat, stackArgAddr]; decide, rfl, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide,
      by decide, by decide, by decide⟩ <;>
    · exact Region.disjoint_of_sep (by decide)

end VG.Proof.Sha3.Arm.Stream.Absorb
