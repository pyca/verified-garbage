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
permutes the state if they complete the block (`finish_ok`).
-/

@[expose] public section

namespace VG.Proof.Sha3.Arm.Stream.Absorb

open VG VG.Arm VG.Impl.Sha3.Arm.Stream
open VG.Proof.Sha3.Arm (saveA_ok restoreA_ok saveMemA saveMemA_frame SSaved ssaved_ok saveMemA_ssaved
  restore_eq call_ok covers_of preserved_cases ofNat32_succ sub_ofNat32 ofNat32_beq_zero sub_beq_zero32
  beq_zero32 xor_setWidth32 ofNat_toNat32 arg_in argByte_eq addr_toNat words_ok shl2_ofNat32 writeW32_apply)
open VG.Proof.Sha512.Arm (contains_A)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsl wp_mov wp_add wp_sub wp_subs wp_cmp
  wp_ldr wp_str wp_ldrb wp_strb wp_ldrSp eval_eq eval_ne add_ofNat)
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
they complete the block, and the test. -/
theorem finish_ok {s₀ : State} (hp : Pre s₀) {c k : Nat} (hk : 0 < k)
    (hjk : (pos s₀ + c) % rt s₀ + k ≤ rt s₀) {s s₁ : State} (hI : Inv s₀ c s)
    (hC : Common s₀ (c + k) s₁) (h5 : s₁.gpr .r5 = BitVec.ofNat 32 ((pos s₀ + c) % rt s₀ + k))
    (hz : s₁.z = decide ((pos s₀ + c) % rt s₀ + k = rt s₀))
    (hst : stateAt s₁.mem (stA s₀) = xorAt (stateAt s.mem (stA s₀)) ((pos s₀ + c) % rt s₀)
      (bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 c) k)) :
    WP isa (.seq (.ite .eq (.seq (.block [.mov .r5 (.imm 0)]) permuteCall) (.block []))
      (.block [.cmp .r7 (.imm 0)])) s₁ fun s' =>
        Inv s₀ (c + k) s' ∧ s'.z = decide (len s₀ - (c + k) = 0) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  refine WP.seq (WP.mono (Q := Inv s₀ (c + k)) ?_ fun s₂ hI₂ => cmp_ok hI₂)
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

/-- The whole body: it absorbs `k > 0` more bytes. -/
theorem body_ok {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < len s₀) {s : State} (hI : Inv s₀ c s) :
    WP isa absorbBody s fun s' => ∃ k, 0 < k ∧ c + k ≤ len s₀ ∧ Inv s₀ (c + k) s' ∧
      s'.z = decide (len s₀ - (c + k) = 0) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  obtain hl := len_lt s₀
  obtain hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  unfold absorbBody
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
