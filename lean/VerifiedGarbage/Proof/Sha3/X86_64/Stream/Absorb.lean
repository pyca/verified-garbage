import VerifiedGarbage.Proof.Sha3.X86_64.Permute
import VerifiedGarbage.Impl.Sha3.X86_64.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Sha3.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Spill

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.X86_64.Stream.Word`. -/
section

/-!
# The SHA-3 sponge on x86-64: the test for a lane at a time

`wordTest` sets ZF only if the position is at a lane and at least 8 bytes are
left (`wordTest_ok`), so that `absorb` and `squeeze` can then move a lane at
once.
-/

namespace VG.Proof.Sha3.X86_64

open VG VG.X86_64
open VG.Impl.Sha3.X86_64.Stream (wordTest)
open VG.Spec.Sha3 (rates stateAt bytesAt)
open VG.Proof.Sha3 (xorAt byteOf_xorAt byteOf_stateAt writeW64_byte bytesAt_succ)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_or {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr d ||| s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .or d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_shr {d : Reg} {n : Nat} (h₁ : 1 ≤ n) (h₂ : n ≤ 63)
    (k : ∀ s', Upd s s' d (s.gpr d >>> n) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q := by
  have e : exec (.shift .shr d n) s = some ((s.setFlags (some ((s.gpr d).getLsbD (n - 1)))
      (if n = 1 then some (s.gpr d).msb else none) (some (s.gpr d >>> n == 0))
      (some (s.gpr d >>> n).msb)).setReg d (s.gpr d >>> n)) := by
    simp only [exec, execShift, h₁, h₂, and_self, ite_true]
  exact WP.cons e (k _ (Upd.withFlags _ _ _ _ _ _ _))

end

theorem sx8 : BitVec.signExtend 64 (8 : BitVec 32) = BitVec.ofNat 64 8 := by decide

/-- Every rate is a whole number of lanes. -/
theorem rate_mod8 {r : Nat} (h : r ∈ rates) : r % 8 = 0 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `wordTest`, from `r12` = `pos` and `r14` = `n`: it changes only `r10`,
`r11` and the flags, and sets ZF only if `pos` is a multiple of 8 and
`n ≥ 8`. -/
theorem wordTest_ok {s : State} {pos n : Nat} (h12 : s.gpr .r12 = BitVec.ofNat 64 pos)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    WP isa (.block wordTest) s fun s' => (∀ r, r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∃ b, s'.zf = some b ∧ (b = true → pos % 8 = 0 ∧ 8 ≤ n) := by
  unfold wordTest
  refine wp_mov fun s₁ u₁ => wp_mov32i fun s₂ u₂ => wp_and fun s₃ u₃ => wp_mov fun s₄ u₄ =>
    wp_subi fun s₅ u₅ _ => VG.Proof.Sha3.X86_64.wp_shr (by decide) (by decide) fun s₆ u₆ => VG.Proof.Sha3.X86_64.wp_or fun s₇ u₇ =>
      wp_test fun s₈ g₈ m₈ rd₈ wr₈ z₈ => wp_nil ?_
  refine ⟨fun r h1 h2 => by
      rw [g₈, u₇.other r h1, u₆.other r h2, u₅.other r h2, u₄.other r h2, u₃.other r h1, u₂.other r h2,
        u₁.other r h1],
    by rw [m₈, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem],
    by rw [rd₈, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd],
    by rw [wr₈, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr], _, z₈, fun hb => ?_⟩
  have h0 : s₇.gpr .r10 = 0 := by simpa using hb
  rw [u₇.gpr, u₆.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
    u₂.other _ (by decide), u₂.gpr, u₁.gpr, u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
    u₁.other _ (by decide), h12, h14, VG.Proof.Sha3.X86_64.sx8] at h0
  have h0' := congrArg BitVec.toNat h0
  simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_sub,
    BitVec.toNat_ofNat, BitVec.toNat_setWidth] at h0'
  simp only [show BitVec.toNat (7 : BitVec 32) = 2 ^ 3 - 1 from rfl,
    show (2 ^ 3 - 1) % 2 ^ 64 = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow, show BitVec.toNat (0 : BitVec 64) = 0 from rfl,
    Nat.or_eq_zero_iff] at h0'
  omega

/-- The bytes `c … c + n - 1` follow the first `c`. -/
theorem bytesAt_add (m : Mem) (p : Addr) (c : Nat) :
    ∀ n, bytesAt m p (c + n) = bytesAt m p c ++ bytesAt m (p + BitVec.ofNat 64 c) n
  | 0 => by simp [bytesAt]
  | n + 1 => by
    rw [← Nat.add_assoc, bytesAt_succ, VG.Proof.Sha3.X86_64.bytesAt_add m p c n, bytesAt_succ, List.append_assoc,
      BitVec.add_assoc, ← BitVec.ofNat_add]

/-- A lane of a state in memory written: its 8 bytes XORed with `bs`. -/
theorem stateAt_write_lane {m : Mem} {p : Addr} {j : Nat} (hj : j + 8 ≤ 200) {v : BitVec 64}
    {bs : List Byte} (hbs : bs.length = 8)
    (hv : ∀ d < 8, v.extractLsb' (8 * d) 8 = m (p + BitVec.ofNat 64 (j + d)) ^^^ bs.getD d 0) :
    stateAt (m.writeW (p + BitVec.ofNat 64 j) v) p = xorAt (stateAt m p) j bs :=
  Proof.Sha3.ext_bytes fun i hi => by
    rw [byteOf_xorAt _ _ _ hi, byteOf_stateAt _ _ hi, byteOf_stateAt _ _ hi, hbs]
    by_cases c : j ≤ i ∧ i < j + 8
    · rw [ite_eq_left c, show p + BitVec.ofNat 64 i = p + BitVec.ofNat 64 j + BitVec.ofNat 64 (i - j) by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' c.1],
        writeW64_byte _ _ _ (by omega), hv _ (by omega), Nat.add_sub_cancel' c.1,
        show p + BitVec.ofNat 64 j + BitVec.ofNat 64 (i - j) = p + BitVec.ofNat 64 i by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' c.1]]
    · rw [ite_eq_right c, Mem.writeW, Mem.write_apply]
      rw [Offset.sub_toNat' _ (by omega) (by omega)]
      split <;> omega

end VG.Proof.Sha3.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.X86_64.Stream.Absorb`. -/
section

/-!
# The SHA-3 sponge on x86-64: `absorb`
-/

namespace VG.Proof.Sha3.X86_64.Stream.Absorb

open VG VG.X86_64 VG.Impl.Sha3.X86_64.Stream
open VG.Impl.Sha3.X86_64 (at_)
open VG.Proof.Sha3.X86_64 (Upd wp_mov wp_movm wp_movzx8 wp_store8 wp_store wp_xor wp_xorm wp_addi wp_subi
  wp_cmp wp_test wp_mov32i wp_nil ea_at
  permuteAt_ok wordTest_ok rate_mod8 sx8 bytesAt_add stateAt_write_lane)
open VG.Proof.Sha3 (Rep rep_snoc rep_append xorByte xorAt xorAt_single stateAt_xorByte)
open VG.Spec.Sha3 (stateAt keccakF bytesAt rates)

/-! ## Arithmetic -/

theorem sx1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .rdi
abbrev rt : Nat := (s₀.gpr .rsi).toNat
abbrev pos : Nat := (s₀.gpr .rdx).toNat
abbrev dp : Addr := s₀.gpr .rcx
abbrev len : Nat := (s₀.gpr .r8).toNat
abbrev scr : Addr := s₀.gpr .r9
abbrev stR : Region := ⟨VG.Proof.Sha3.X86_64.Stream.Absorb.st s₀, 200⟩
abbrev dR : Region := ⟨VG.Proof.Sha3.X86_64.Stream.Absorb.dp s₀, VG.Proof.Sha3.X86_64.Stream.Absorb.len s₀⟩
abbrev scR : Region := ⟨VG.Proof.Sha3.X86_64.Stream.Absorb.scr s₀, 640⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
/-- Where the call of `vg_keccak_f1600` stores its return address. -/
abbrev stkR : Region := below (s₀.gpr .rsp) 8
/-- The first `c` bytes of data. -/
abbrev D (c : Nat) : List Byte := bytesAt s₀.mem (VG.Proof.Sha3.X86_64.Stream.Absorb.dp s₀) c

/-- The caller's callee-saved registers are saved in the scratch space. -/
abbrev Saved (m : Mem) : Prop := Spill.Saved m (VG.Proof.Sha3.X86_64.Stream.Absorb.scr s₀) s₀.gpr saved

/-- The messages the initial state and position represent. -/
def Msg (msg : List Byte) : Prop :=
  stateAt s₀.mem (VG.Proof.Sha3.X86_64.Stream.Absorb.st s₀) = Rep (VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀) msg ∧ VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ = msg.length % VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Sha3.X86_64.Stream.Absorb.dR s₀]
  wr : s₀.wr = [VG.Proof.Sha3.X86_64.Stream.Absorb.stR s₀, VG.Proof.Sha3.X86_64.Stream.Absorb.scR s₀]
  st_scr : (VG.Proof.Sha3.X86_64.Stream.Absorb.stR s₀).Disjoint (VG.Proof.Sha3.X86_64.Stream.Absorb.scR s₀)
  d_st : (VG.Proof.Sha3.X86_64.Stream.Absorb.dR s₀).Disjoint (VG.Proof.Sha3.X86_64.Stream.Absorb.stR s₀)
  d_scr : (VG.Proof.Sha3.X86_64.Stream.Absorb.dR s₀).Disjoint (VG.Proof.Sha3.X86_64.Stream.Absorb.scR s₀)
  ret_st : (VG.Proof.Sha3.X86_64.Stream.Absorb.retR s₀).Disjoint (VG.Proof.Sha3.X86_64.Stream.Absorb.stR s₀)
  ret_scr : (VG.Proof.Sha3.X86_64.Stream.Absorb.retR s₀).Disjoint (VG.Proof.Sha3.X86_64.Stream.Absorb.scR s₀)
  stk_st : (VG.Proof.Sha3.X86_64.Stream.Absorb.stkR s₀).Disjoint (VG.Proof.Sha3.X86_64.Stream.Absorb.stR s₀)
  stk_d : (VG.Proof.Sha3.X86_64.Stream.Absorb.stkR s₀).Disjoint (VG.Proof.Sha3.X86_64.Stream.Absorb.dR s₀)
  stk_scr : (VG.Proof.Sha3.X86_64.Stream.Absorb.stkR s₀).Disjoint (VG.Proof.Sha3.X86_64.Stream.Absorb.scR s₀)
  rate : VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ ∈ rates
  pos_lt : VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ < VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀

theorem pre_of {s₀ : State} (h : Proof.Sha3.absorbX86_64.pre s₀) : VG.Proof.Sha3.X86_64.Stream.Absorb.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem Pre.rt_pos {s₀ : State} (hp : VG.Proof.Sha3.X86_64.Stream.Absorb.Pre s₀) : 0 < VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ ∧ VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ ≤ 168 := by
  have h := hp.rate
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h
  omega

theorem ret_stk (s₀ : State) : (VG.Proof.Sha3.X86_64.Stream.Absorb.retR s₀).Disjoint (VG.Proof.Sha3.X86_64.Stream.Absorb.stkR s₀) := by
  intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega

theorem len_lt (s₀ : State) : VG.Proof.Sha3.X86_64.Stream.Absorb.len s₀ < 2 ^ 64 := (s₀.gpr .r8).isLt

theorem rsi_eq (s₀ : State) : s₀.gpr .rsi = BitVec.ofNat 64 (VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀) := by simp [VG.Proof.Sha3.X86_64.Stream.Absorb.rt]

theorem saved_bound : ∀ p ∈ saved, 512 ≤ p.2 ∧ p.2 + 8 ≤ 560 := by decide

/-- Writes to the state, the first 512 bytes of scratch and below the stack
keep the saved registers. -/
theorem Saved.frame {s₀ : State} (hp : VG.Proof.Sha3.X86_64.Stream.Absorb.Pre s₀) {m m' : Mem} (h : VG.Proof.Sha3.X86_64.Stream.Absorb.Saved s₀ m)
    (hf : Frame [VG.Proof.Sha3.X86_64.Stream.Absorb.stR s₀, ⟨VG.Proof.Sha3.X86_64.Stream.Absorb.scr s₀, 512⟩, VG.Proof.Sha3.X86_64.Stream.Absorb.stkR s₀] m m') : VG.Proof.Sha3.X86_64.Stream.Absorb.Saved s₀ m' :=
  Spill.Saved.frame h hf fun p hp' r hr => by
    have := VG.Proof.Sha3.X86_64.Stream.Absorb.saved_bound p hp'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.st_scr.symm.sub_left (sub_offset (by omega) (by omega))
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact hp.stk_scr.symm.sub_left (sub_offset (by omega) (by omega))

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ VG.Proof.Sha3.X86_64.Stream.Absorb.len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rbx : s.gpr .rbx = VG.Proof.Sha3.X86_64.Stream.Absorb.st s₀
  r15 : s.gpr .r15 = VG.Proof.Sha3.X86_64.Stream.Absorb.scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbp : s.gpr .rbp = s₀.gpr .rsi
  r13 : s.gpr .r13 = VG.Proof.Sha3.X86_64.Stream.Absorb.dp s₀ + BitVec.ofNat 64 c
  r14 : s.gpr .r14 = BitVec.ofNat 64 (VG.Proof.Sha3.X86_64.Stream.Absorb.len s₀ - c)
  frame : Frame [VG.Proof.Sha3.X86_64.Stream.Absorb.stR s₀, VG.Proof.Sha3.X86_64.Stream.Absorb.scR s₀, VG.Proof.Sha3.X86_64.Stream.Absorb.stkR s₀] s₀.mem s.mem
  saved : VG.Proof.Sha3.X86_64.Stream.Absorb.Saved s₀ s.mem

/-- The loop invariant: the state represents the message followed by the
first `c` bytes of data. -/
structure Inv (s₀ : State) (c : Nat) (s : State) : Prop extends VG.Proof.Sha3.X86_64.Stream.Absorb.Common s₀ c s where
  r12 : s.gpr .r12 = BitVec.ofNat 64 ((VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ + c) % VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀)
  repr : ∀ msg, VG.Proof.Sha3.X86_64.Stream.Absorb.Msg s₀ msg → stateAt s.mem (VG.Proof.Sha3.X86_64.Stream.Absorb.st s₀) = Rep (VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀) (msg ++ VG.Proof.Sha3.X86_64.Stream.Absorb.D s₀ c)

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : VG.Proof.Sha3.X86_64.Stream.Absorb.Common s₀ c s)
    (hg : ∀ r ∈ [Reg.rbx, .r15, .rsp, .rbp, .r13, .r14], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.Sha3.X86_64.Stream.Absorb.Common s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  rbx := by rw [hg _ (by simp)]; exact h.rbx
  r15 := by rw [hg _ (by simp)]; exact h.r15
  rsp := by rw [hg _ (by simp)]; exact h.rsp
  rbp := by rw [hg _ (by simp)]; exact h.rbp
  r13 := by rw [hg _ (by simp)]; exact h.r13
  r14 := by rw [hg _ (by simp)]; exact h.r14
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

/-- A call of the permutation keeps what holds throughout. -/
theorem Common.after_call {s₀ : State} (hp : VG.Proof.Sha3.X86_64.Stream.Absorb.Pre s₀) {c : Nat} {s s' : State} (h : VG.Proof.Sha3.X86_64.Stream.Absorb.Common s₀ c s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r)
    (hf : Frame [VG.Proof.Sha3.X86_64.Stream.Absorb.stR s₀, ⟨VG.Proof.Sha3.X86_64.Stream.Absorb.scr s₀, 512⟩, VG.Proof.Sha3.X86_64.Stream.Absorb.stkR s₀] s.mem s'.mem) : VG.Proof.Sha3.X86_64.Stream.Absorb.Common s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  rbx := by rw [hcs _ (by decide)]; exact h.rbx
  r15 := by rw [hcs _ (by decide)]; exact h.r15
  rsp := by rw [hcs _ (by decide)]; exact h.rsp
  rbp := by rw [hcs _ (by decide)]; exact h.rbp
  r13 := by rw [hcs _ (by decide)]; exact h.r13
  r14 := by rw [hcs _ (by decide)]; exact h.r14
  frame := h.frame.trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.Sha3.X86_64.Stream.Absorb.stR s₀, by simp, fun _ h => h⟩
    · exact ⟨VG.Proof.Sha3.X86_64.Stream.Absorb.scR s₀, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨VG.Proof.Sha3.X86_64.Stream.Absorb.stkR s₀, by simp, fun _ h => h⟩)
  saved := h.saved.frame hp hf

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : VG.Proof.Sha3.X86_64.Stream.Absorb.Pre s₀) {c : Nat} {s : State} (h : VG.Proof.Sha3.X86_64.Stream.Absorb.Common s₀ c s) {i : Nat}
    (hi : i < VG.Proof.Sha3.X86_64.Stream.Absorb.len s₀) : s.mem (VG.Proof.Sha3.X86_64.Stream.Absorb.dp s₀ + BitVec.ofNat 64 i) = s₀.mem (VG.Proof.Sha3.X86_64.Stream.Absorb.dp s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := VG.Proof.Sha3.X86_64.Stream.Absorb.dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr, hp.stk_d.symm⟩) (Nat.le_of_lt (VG.Proof.Sha3.X86_64.Stream.Absorb.len_lt s₀)) hi

/-! ## The prologue -/

theorem prologue_ok {s₀ : State} (hp : VG.Proof.Sha3.X86_64.Stream.Absorb.Pre s₀) :
    WP isa (.block (save .r9 ++ ([.mov .rbx (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx),
      .mov .r13 (.reg .rcx), .mov .r14 (.reg .r8), .mov .r15 (.reg .r9), .alu .test .r14 (.reg .r14)] : List Instr)))
      s₀ fun s => VG.Proof.Sha3.X86_64.Stream.Absorb.Inv s₀ 0 s ∧ s.zf = some (decide (VG.Proof.Sha3.X86_64.Stream.Absorb.len s₀ = 0)) := by
  rw [WP.block_append_iff]
  refine WP.mono (Spill.save_ok .r9 saved s₀ fun p hp' => ?_) fun s₁ ⟨g₁, rd₁, wr₁, m₁⟩ => ?_
  · have := VG.Proof.Sha3.X86_64.Stream.Absorb.saved_bound p hp'
    exact ⟨VG.Proof.Sha3.X86_64.Stream.Absorb.scR s₀, by simp [hp.wr], contains_offset (by omega) (by omega)⟩
  have f₁ : Frame [VG.Proof.Sha3.X86_64.Stream.Absorb.scR s₀] s₀.mem s₁.mem := m₁ ▸ Spill.saveMem_frame_base _ _ _ _
    (fun p hp => by have := VG.Proof.Sha3.X86_64.Stream.Absorb.saved_bound p hp; omega) (by decide)
  have v₁ : VG.Proof.Sha3.X86_64.Stream.Absorb.Saved s₀ s₁.mem := m₁ ▸ Spill.saveMem_saved _ _ _ _ (by decide)
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    wp_mov fun s₆ u₆ => wp_mov fun s₇ u₇ => wp_test fun s₈ g₈ m₈ rd₈ wr₈ z₈ => wp_nil ?_
  have hm : s₈.mem = s₁.mem := by rw [m₈, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have hrd : s₈.rd = s₀.rd := by rw [rd₈, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  have hwr : s₈.wr = s₀.wr := by rw [wr₈, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  have hf : Frame [VG.Proof.Sha3.X86_64.Stream.Absorb.stR s₀, VG.Proof.Sha3.X86_64.Stream.Absorb.scR s₀, VG.Proof.Sha3.X86_64.Stream.Absorb.stkR s₀] s₀.mem s₁.mem := f₁.mono (by simp)
  have h14 : s₈.gpr .r14 = s₀.gpr .r8 := by
    rw [g₈, u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  have hl := VG.Proof.Sha3.X86_64.Stream.Absorb.len_lt s₀
  refine ⟨⟨⟨Nat.zero_le _, hrd, hwr, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hm]; exact hf,
    by rw [hm]; exact v₁⟩, ?_, fun msg ⟨hs, _⟩ => ?_⟩, ?_⟩
  · rw [g₈, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, g₁]
  · rw [g₈, u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  · rw [g₈, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  · rw [g₈, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), g₁]
  · rw [g₈, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), g₁]
    simp
  · rw [h14, Nat.sub_zero]; simp [VG.Proof.Sha3.X86_64.Stream.Absorb.len]
  · rw [g₈, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), g₁, Nat.add_zero, Nat.mod_eq_of_lt hp.pos_lt]
    simp [VG.Proof.Sha3.X86_64.Stream.Absorb.pos]
  · rw [hm, show VG.Proof.Sha3.X86_64.Stream.Absorb.D s₀ 0 = [] by simp [bytesAt], List.append_nil, ← hs]
    exact Proof.Sha3.stateAt_congr fun i hi =>
      f₁.bytes (R := VG.Proof.Sha3.X86_64.Stream.Absorb.stR s₀) (by simpa using hp.st_scr)
        (by simp) hi
  · rw [z₈, ← congrFun g₈ .r14, h14, BitVec.and_self]
    rw [show s₀.gpr .r8 = BitVec.ofNat 64 (VG.Proof.Sha3.X86_64.Stream.Absorb.len s₀) by simp [VG.Proof.Sha3.X86_64.Stream.Absorb.len], ofNat_beq_zero hl]

/-! ## One iteration -/

/-- The state after absorbing `c` bytes, then the byte at the position `j`
XORed in. -/
theorem body_block {s₀ : State} (hp : VG.Proof.Sha3.X86_64.Stream.Absorb.Pre s₀) {c : Nat} (hc : c < VG.Proof.Sha3.X86_64.Stream.Absorb.len s₀) {s : State}
    (hI : VG.Proof.Sha3.X86_64.Stream.Absorb.Inv s₀ c s) :
    WP isa (.block absorbByte) s fun s' =>
      VG.Proof.Sha3.X86_64.Stream.Absorb.Common s₀ (c + 1) s' ∧ s'.gpr .r12 = BitVec.ofNat 64 ((VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ + c) % VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ + 1) ∧
      s'.zf = some (decide ((VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ + c) % VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ + 1 = VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀)) ∧
      stateAt s'.mem (VG.Proof.Sha3.X86_64.Stream.Absorb.st s₀) = xorByte (stateAt s.mem (VG.Proof.Sha3.X86_64.Stream.Absorb.st s₀)) ((VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ + c) % VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀)
        (s₀.mem (VG.Proof.Sha3.X86_64.Stream.Absorb.dp s₀ + BitVec.ofNat 64 c)) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hl := VG.Proof.Sha3.X86_64.Stream.Absorb.len_lt s₀
  have hj : (VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ + c) % VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ < VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ := Nat.mod_lt _ hr₀
  generalize hjd : (VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ + c) % VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ = j at hj ⊢
  have hr12 : s.gpr .r12 = BitVec.ofNat 64 j := by rw [hI.r12, hjd]
  have hrbx := hI.rbx
  have hin : InRegions (s.rd ++ s.wr) (VG.Proof.Sha3.X86_64.Stream.Absorb.dp s₀ + BitVec.ofNat 64 c) 1 :=
    ⟨VG.Proof.Sha3.X86_64.Stream.Absorb.dR s₀, by simp [hI.rd, hp.rd], contains_offset (by omega) (by omega)⟩
  have hst : ∀ t : State, t.gpr .rbx = VG.Proof.Sha3.X86_64.Stream.Absorb.st s₀ → t.gpr .r12 = BitVec.ofNat 64 j →
      t.ea stByte = VG.Proof.Sha3.X86_64.Stream.Absorb.st s₀ + BitVec.ofNat 64 j := fun t h1 h2 => by
    simp [State.ea, stByte, h1, h2]
  have hsin : ∀ rs : List Region, VG.Proof.Sha3.X86_64.Stream.Absorb.stR s₀ ∈ rs → InRegions rs (VG.Proof.Sha3.X86_64.Stream.Absorb.st s₀ + BitVec.ofNat 64 j) 1 :=
    fun rs h => ⟨VG.Proof.Sha3.X86_64.Stream.Absorb.stR s₀, h, contains_offset (by omega) (by omega)⟩
  unfold absorbByte
  refine wp_movzx8 (d := .rax) (a := VG.Proof.Sha3.X86_64.Stream.Absorb.dp s₀ + BitVec.ofNat 64 c) (by simp [State.ea, hI.r13]) hin
    fun s₁ u₁ => ?_
  refine wp_movzx8 (d := .rcx) (a := VG.Proof.Sha3.X86_64.Stream.Absorb.st s₀ + BitVec.ofNat 64 j)
    (hst _ (by rw [u₁.other _ (by decide), hrbx]) (by rw [u₁.other _ (by decide), hr12]))
    (hsin _ (by simp [u₁.rd, u₁.wr, hI.rd, hI.wr, hp.wr])) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  refine wp_store8 (r := .rax) (a := VG.Proof.Sha3.X86_64.Stream.Absorb.st s₀ + BitVec.ofNat 64 j)
    (hst _ (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hrbx])
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hr12]))
    (hsin _ (by simp [u₃.wr, u₂.wr, u₁.wr, hI.wr, hp.wr])) fun s₄ g₄ m₄ rd₄ wr₄ => ?_
  refine wp_addi fun s₅ u₅ => wp_addi fun s₆ u₆ => wp_subi fun s₇ u₇ _ =>
    wp_cmp fun s₈ g₈ m₈ rd₈ wr₈ _ z₈ => wp_nil ?_
  -- The byte stored.
  have hv : (s₃.gpr .rax).setWidth 8 =
      s₀.mem (VG.Proof.Sha3.X86_64.Stream.Absorb.dp s₀ + BitVec.ofNat 64 c) ^^^ s.mem (VG.Proof.Sha3.X86_64.Stream.Absorb.st s₀ + BitVec.ofNat 64 j) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₂.gpr, u₁.gpr, u₁.mem, xor_setWidth, hI.data hp hc]
  have hm₈ : s₈.mem = s.mem.writeW (VG.Proof.Sha3.X86_64.Stream.Absorb.st s₀ + BitVec.ofNat 64 j)
      (s₀.mem (VG.Proof.Sha3.X86_64.Stream.Absorb.dp s₀ + BitVec.ofNat 64 c) ^^^ s.mem (VG.Proof.Sha3.X86_64.Stream.Absorb.st s₀ + BitVec.ofNat 64 j)) := by
    rw [m₈, u₇.mem, u₆.mem, u₅.mem, m₄, hv, u₃.mem, u₂.mem, u₁.mem]
  have hf : Frame [VG.Proof.Sha3.X86_64.Stream.Absorb.stR s₀] s.mem s₈.mem := by
    rw [hm₈]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (by omega) (by omega))
  have g : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r13 → r ≠ .r12 → r ≠ .r14 → s₈.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [g₈, u₇.other r h5, u₆.other r h4, u₅.other r h3, g₄, u₃.other r h1, u₂.other r h2,
        u₁.other r h1]
  have h12 : s₈.gpr .r12 = BitVec.ofNat 64 (j + 1) := by
    rw [g₈, u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), g₄, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hr12, VG.Proof.Sha3.X86_64.Stream.Absorb.sx1, ofNat_succ]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, h12, ?_, ?_⟩
  · rw [rd₈, u₇.rd, u₆.rd, u₅.rd, rd₄, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [wr₈, u₇.wr, u₆.wr, u₅.wr, wr₄, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  · rw [g .rbx (by decide) (by decide) (by decide) (by decide) (by decide), hrbx]
  · rw [g .r15 (by decide) (by decide) (by decide) (by decide) (by decide), hI.r15]
  · rw [g .rsp (by decide) (by decide) (by decide) (by decide) (by decide), hI.rsp]
  · rw [g .rbp (by decide) (by decide) (by decide) (by decide) (by decide), hI.rbp]
  · rw [g₈, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, g₄, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hI.r13, VG.Proof.Sha3.X86_64.Stream.Absorb.sx1, ofNat_succ, BitVec.add_assoc]
  · rw [g₈, u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), g₄, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hI.r14, VG.Proof.Sha3.X86_64.Stream.Absorb.sx1, ofNat_pred (by omega), Nat.sub_sub]
  · exact hI.frame.trans (hf.mono (by simp))
  · exact hI.saved.frame hp (hf.mono (by simp))
  · rw [z₈, ← congrFun g₈ .r12, ← congrFun g₈ .rbp, h12, g .rbp (by decide) (by decide) (by decide) (by decide) (by decide), hI.rbp, VG.Proof.Sha3.X86_64.Stream.Absorb.rsi_eq,
      sub_beq (by omega) (by omega)]
  · refine stateAt_xorByte (by omega) ?_ fun i hi hij => ?_
    · rw [hm₈, VG.Proof.Sha3.writeW8_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl), BitVec.xor_comm]
    · rw [hm₈, VG.Proof.Sha3.writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (VG.Proof.Sha3.ne_of_lt200 hi (by omega) hij))]

/-- The block of the body: the lane of data at `c` XORed into the lane at
position `j`. -/
theorem body_word {s₀ : State} (hp : VG.Proof.Sha3.X86_64.Stream.Absorb.Pre s₀) {c : Nat} (hc : c + 8 ≤ VG.Proof.Sha3.X86_64.Stream.Absorb.len s₀) {s : State}
    (hI : VG.Proof.Sha3.X86_64.Stream.Absorb.Inv s₀ c s) (hj8 : (VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ + c) % VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ % 8 = 0) :
    WP isa (.block absorbWord) s fun s' =>
      VG.Proof.Sha3.X86_64.Stream.Absorb.Common s₀ (c + 8) s' ∧ s'.gpr .r12 = BitVec.ofNat 64 ((VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ + c) % VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ + 8) ∧
      s'.zf = some (decide ((VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ + c) % VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ + 8 = VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀)) ∧
      stateAt s'.mem (VG.Proof.Sha3.X86_64.Stream.Absorb.st s₀) = xorAt (stateAt s.mem (VG.Proof.Sha3.X86_64.Stream.Absorb.st s₀)) ((VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ + c) % VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀)
        (bytesAt s₀.mem (VG.Proof.Sha3.X86_64.Stream.Absorb.dp s₀ + BitVec.ofNat 64 c) 8) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hl := VG.Proof.Sha3.X86_64.Stream.Absorb.len_lt s₀
  have h8 := VG.Proof.Sha3.X86_64.rate_mod8 hp.rate
  have hj : (VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ + c) % VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ < VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ := Nat.mod_lt _ hr₀
  generalize hjd : (VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ + c) % VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ = j at hj hj8 ⊢
  have hj' : j + 8 ≤ VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ := by omega
  have hr12 : s.gpr .r12 = BitVec.ofNat 64 j := by rw [hI.r12, hjd]
  have hrbx := hI.rbx
  have hst : ∀ t : State, t.gpr .rbx = VG.Proof.Sha3.X86_64.Stream.Absorb.st s₀ → t.gpr .r12 = BitVec.ofNat 64 j →
      t.ea stByte = VG.Proof.Sha3.X86_64.Stream.Absorb.st s₀ + BitVec.ofNat 64 j := fun t h1 h2 => by
    simp [State.ea, stByte, h1, h2]
  have hsin : ∀ rs : List Region, VG.Proof.Sha3.X86_64.Stream.Absorb.stR s₀ ∈ rs → InRegions rs (VG.Proof.Sha3.X86_64.Stream.Absorb.st s₀ + BitVec.ofNat 64 j) 8 :=
    fun rs h => ⟨VG.Proof.Sha3.X86_64.Stream.Absorb.stR s₀, h, contains_offset (by omega) (by omega)⟩
  unfold absorbWord
  refine wp_movm (d := .rax) (a := VG.Proof.Sha3.X86_64.Stream.Absorb.dp s₀ + BitVec.ofNat 64 c) (by simp [State.ea, hI.r13])
    ⟨VG.Proof.Sha3.X86_64.Stream.Absorb.dR s₀, by simp [hI.rd, hp.rd], contains_offset (by omega) (by omega)⟩ fun s₁ u₁ => ?_
  refine wp_xorm (a := VG.Proof.Sha3.X86_64.Stream.Absorb.st s₀ + BitVec.ofNat 64 j)
    (hst _ (by rw [u₁.other _ (by decide), hrbx]) (by rw [u₁.other _ (by decide), hr12]))
    (hsin _ (by simp [u₁.rd, u₁.wr, hI.rd, hI.wr, hp.wr])) fun s₂ u₂ => ?_
  refine wp_store (r := .rax) (a := VG.Proof.Sha3.X86_64.Stream.Absorb.st s₀ + BitVec.ofNat 64 j)
    (hst _ (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hrbx])
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hr12]))
    (hsin _ (by simp [u₂.wr, u₁.wr, hI.wr, hp.wr])) fun s₃ g₃ m₃ rd₃ wr₃ => ?_
  refine wp_addi fun s₄ u₄ => wp_addi fun s₅ u₅ => wp_subi fun s₆ u₆ _ =>
    wp_cmp fun s₇ g₇ m₇ rd₇ wr₇ _ z₇ => wp_nil ?_
  have hv : s₂.gpr .rax = s.mem.readW (VG.Proof.Sha3.X86_64.Stream.Absorb.dp s₀ + BitVec.ofNat 64 c) 64 ^^^
      s.mem.readW (VG.Proof.Sha3.X86_64.Stream.Absorb.st s₀ + BitVec.ofNat 64 j) 64 := by
    rw [u₂.gpr, u₁.gpr, u₁.mem]
  have hm₇ : s₇.mem = s.mem.writeW (VG.Proof.Sha3.X86_64.Stream.Absorb.st s₀ + BitVec.ofNat 64 j) (s₂.gpr .rax) := by
    rw [m₇, u₆.mem, u₅.mem, u₄.mem, m₃, u₂.mem, u₁.mem]
  have hf : Frame [VG.Proof.Sha3.X86_64.Stream.Absorb.stR s₀] s.mem s₇.mem := by
    rw [hm₇]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (by omega) (by omega))
  have g : ∀ r, r ≠ .rax → r ≠ .r13 → r ≠ .r12 → r ≠ .r14 → s₇.gpr r = s.gpr r :=
    fun r h1 h3 h4 h5 => by
      rw [g₇, u₆.other r h5, u₅.other r h4, u₄.other r h3, g₃, u₂.other r h1, u₁.other r h1]
  have h12 : s₇.gpr .r12 = BitVec.ofNat 64 (j + 8) := by
    rw [g₇, u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃, u₂.other _ (by decide),
      u₁.other _ (by decide), hr12, VG.Proof.Sha3.X86_64.sx8, ← BitVec.ofNat_add]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, h12, ?_, ?_⟩
  · rw [rd₇, u₆.rd, u₅.rd, u₄.rd, rd₃, u₂.rd, u₁.rd, hI.rd]
  · rw [wr₇, u₆.wr, u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr, hI.wr]
  · rw [g .rbx (by decide) (by decide) (by decide) (by decide), hrbx]
  · rw [g .r15 (by decide) (by decide) (by decide) (by decide), hI.r15]
  · rw [g .rsp (by decide) (by decide) (by decide) (by decide), hI.rsp]
  · rw [g .rbp (by decide) (by decide) (by decide) (by decide), hI.rbp]
  · rw [g₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃, u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r13, VG.Proof.Sha3.X86_64.sx8, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [g₇, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃, u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r14, VG.Proof.Sha3.X86_64.sx8, sub_ofNat (by omega), Nat.sub_sub]
  · exact hI.frame.trans (hf.mono (by simp))
  · exact hI.saved.frame hp (hf.mono (by simp))
  · rw [z₇, ← congrFun g₇ .r12, ← congrFun g₇ .rbp, h12, g .rbp (by decide) (by decide) (by decide) (by decide),
      hI.rbp, VG.Proof.Sha3.X86_64.Stream.Absorb.rsi_eq, sub_beq (by omega) (by omega)]
  · rw [hm₇]
    refine VG.Proof.Sha3.X86_64.stateAt_write_lane (by omega) (VG.Proof.Sha3.bytesAt_length _ _ _) fun d hd => ?_
    rw [hv, BitVec.extractLsb'_xor, Mem.readW, Mem.readW, BitVec.setWidth_eq, BitVec.setWidth_eq,
      Mem.extractLsb'_read _ _ (show d < 64 / 8 by omega), Mem.extractLsb'_read _ _ (show d < 64 / 8 by omega),
      BitVec.xor_comm, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 1
    simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hd,
      Option.map_some, Option.getD_some]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, hI.data hp (by omega)]

/-- After a lane or a byte of data: what the permutation, if the block is
complete, turns into the invariant. -/
structure After (s₀ : State) (s : State) (c n : Nat) (s' : State) : Prop where
  common : VG.Proof.Sha3.X86_64.Stream.Absorb.Common s₀ (c + n) s'
  r12 : s'.gpr .r12 = BitVec.ofNat 64 ((VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ + c) % VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ + n)
  z : s'.zf = some (decide ((VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ + c) % VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ + n = VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀))
  st : stateAt s'.mem (VG.Proof.Sha3.X86_64.Stream.Absorb.st s₀) = xorAt (stateAt s.mem (VG.Proof.Sha3.X86_64.Stream.Absorb.st s₀)) ((VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ + c) % VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀)
    (bytesAt s₀.mem (VG.Proof.Sha3.X86_64.Stream.Absorb.dp s₀ + BitVec.ofNat 64 c) n)

/-- The permutation if the block is complete. -/
theorem after_ok {s₀ : State} (hp : VG.Proof.Sha3.X86_64.Stream.Absorb.Pre s₀) {c n : Nat} (hn : 0 < n)
    (hfit : (VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ + c) % VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ + n ≤ VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀) {s s₁ : State} (hI : VG.Proof.Sha3.X86_64.Stream.Absorb.Inv s₀ c s) (h : VG.Proof.Sha3.X86_64.Stream.Absorb.After s₀ s c n s₁) :
    WP isa (.ite .e (.seq (.block [.mov32 .r12 (.imm 0)]) permuteAt) (.block [])) s₁
      (VG.Proof.Sha3.X86_64.Stream.Absorb.Inv s₀ (c + n)) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hC := h.common
  have hlen : ∀ msg, VG.Proof.Sha3.X86_64.Stream.Absorb.Msg s₀ msg → (msg ++ VG.Proof.Sha3.X86_64.Stream.Absorb.D s₀ c).length % VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ = (VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ + c) % VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ :=
    fun msg ⟨_, hpm⟩ => by rw [List.length_append, VG.Proof.Sha3.bytesAt_length, hpm, Nat.mod_add_mod]
  have hrep : ∀ msg, VG.Proof.Sha3.X86_64.Stream.Absorb.Msg s₀ msg → Rep (VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀) (msg ++ VG.Proof.Sha3.X86_64.Stream.Absorb.D s₀ (c + n)) =
      if (VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ + c) % VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ + n = VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ then keccakF (stateAt s₁.mem (VG.Proof.Sha3.X86_64.Stream.Absorb.st s₀))
      else stateAt s₁.mem (VG.Proof.Sha3.X86_64.Stream.Absorb.st s₀) := fun msg hm => by
    rw [VG.Proof.Sha3.X86_64.Stream.Absorb.D, VG.Proof.Sha3.X86_64.bytesAt_add, ← List.append_assoc, rep_append hr₀ (by omega) _ _
      (by rw [VG.Proof.Sha3.bytesAt_length]; exact hn) (by rw [VG.Proof.Sha3.bytesAt_length, hlen msg hm]; exact hfit),
      hlen msg hm, VG.Proof.Sha3.bytesAt_length, h.st, hI.repr msg hm]
  have hpc : (VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ + (c + n)) % VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ = if (VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ + c) % VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ + n = VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ then 0
      else (VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ + c) % VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ + n := by
    have e := Nat.div_add_mod (VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ + c) (VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀)
    rw [show VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ + (c + n) = (VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ + c) + n by omega]
    generalize (VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ + c) % VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ = j at e hfit ⊢
    generalize (VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ + c) / VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ = q at e
    rw [← e]
    split
    · rw [Nat.add_assoc, ‹j + n = rt s₀›, ← Nat.mul_succ, Nat.mul_mod_right]
    · rw [Nat.add_assoc, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  refine WP.ite (decide ((VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ + c) % VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ + n = VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀)) h.z (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine WP.seq (wp_mov32i fun s₂ u₂ => wp_nil ?_)
    have hC₂ := hC.of_gpr (fun r hr => u₂.other r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u₂.mem u₂.rd u₂.wr
    have hsp := hC₂.rsp
    refine permuteAt_ok hC₂.rbx hC₂.r15 (hp.st_scr.sub_right (Region.sub_prefix (by omega)))
      (by rw [hsp]; exact hp.stk_st) (by rw [hsp]; exact hp.stk_scr.sub_right (Region.sub_prefix (by omega)))
      ?_ fun s₃ rd₃ wr₃ cs₃ f₃ e₃ => ?_
    · rw [hC₂.wr, hp.wr]
      intro a n ⟨r, hr, hcn⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.Sha3.X86_64.Stream.Absorb.stR s₀, by simp, hcn⟩
      · exact ⟨VG.Proof.Sha3.X86_64.Stream.Absorb.scR s₀, by simp, by simp only [Region.Contains] at hcn ⊢; omega⟩
    · have f₃' : Frame [VG.Proof.Sha3.X86_64.Stream.Absorb.stR s₀, ⟨VG.Proof.Sha3.X86_64.Stream.Absorb.scr s₀, 512⟩, VG.Proof.Sha3.X86_64.Stream.Absorb.stkR s₀] s₂.mem s₃.mem := by
        have := f₃; rw [hsp] at this; exact this
      refine { hC₂.after_call hp rd₃ wr₃ cs₃ f₃' with r12 := ?_, repr := fun msg hm => ?_ }
      · rw [cs₃ _ (by decide), u₂.gpr, hpc, ite_eq_left_of_eq_true _ _ (eq_true hb)]; rfl
      · rw [e₃, u₂.mem, hrep msg hm, ite_eq_left_of_eq_true _ _ (eq_true hb)]
  · simp only [decide_eq_false_iff_not] at hb
    refine wp_nil { hC with r12 := ?_, repr := fun msg hm => ?_ }
    · rw [h.r12, hpc, ite_eq_right_of_eq_false _ _ (eq_false hb)]
    · rw [hrep msg hm, ite_eq_right_of_eq_false _ _ (eq_false hb)]

/-- The whole body: a lane or a byte of data, and the test of the bytes left. -/
theorem body_ok {s₀ : State} (hp : VG.Proof.Sha3.X86_64.Stream.Absorb.Pre s₀) {c : Nat} (hc : c < VG.Proof.Sha3.X86_64.Stream.Absorb.len s₀) {s : State} (hI : VG.Proof.Sha3.X86_64.Stream.Absorb.Inv s₀ c s) :
    WP isa absorbBody s fun s' => ∃ c', c < c' ∧ c' ≤ VG.Proof.Sha3.X86_64.Stream.Absorb.len s₀ ∧
      ((isa.eval .ne s' = some false ∧ c' = VG.Proof.Sha3.X86_64.Stream.Absorb.len s₀ ∧ VG.Proof.Sha3.X86_64.Stream.Absorb.Inv s₀ (VG.Proof.Sha3.X86_64.Stream.Absorb.len s₀) s') ∨
        (isa.eval .ne s' = some true ∧ c' < VG.Proof.Sha3.X86_64.Stream.Absorb.len s₀ ∧ VG.Proof.Sha3.X86_64.Stream.Absorb.Inv s₀ c' s')) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have h8 := VG.Proof.Sha3.X86_64.rate_mod8 hp.rate
  have hj : (VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ + c) % VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ < VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ := Nat.mod_lt _ hr₀
  have hl := VG.Proof.Sha3.X86_64.Stream.Absorb.len_lt s₀
  unfold absorbBody
  refine WP.seq (WP.mono (VG.Proof.Sha3.X86_64.wordTest_ok hI.r12 hI.r14 (by omega)) fun s₇ ⟨oth, m₇, rd₇, wr₇, b, z₇, hb₇⟩ => ?_)
  have hI₇ : VG.Proof.Sha3.X86_64.Stream.Absorb.Inv s₀ c s₇ :=
    { hI.toCommon.of_gpr (fun r hr => oth r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) m₇ rd₇ wr₇ with
      r12 := by rw [oth _ (by decide) (by decide)]; exact hI.r12
      repr := fun msg hm => by rw [m₇]; exact hI.repr msg hm }
  -- The final test.
  have tail : ∀ c', c < c' → c' ≤ VG.Proof.Sha3.X86_64.Stream.Absorb.len s₀ → ∀ t : State, VG.Proof.Sha3.X86_64.Stream.Absorb.Inv s₀ c' t →
      WP isa (.block [.alu .test .r14 (.reg .r14)]) t fun s' => ∃ c', c < c' ∧ c' ≤ VG.Proof.Sha3.X86_64.Stream.Absorb.len s₀ ∧
        ((isa.eval .ne s' = some false ∧ c' = VG.Proof.Sha3.X86_64.Stream.Absorb.len s₀ ∧ VG.Proof.Sha3.X86_64.Stream.Absorb.Inv s₀ (VG.Proof.Sha3.X86_64.Stream.Absorb.len s₀) s') ∨
          (isa.eval .ne s' = some true ∧ c' < VG.Proof.Sha3.X86_64.Stream.Absorb.len s₀ ∧ VG.Proof.Sha3.X86_64.Stream.Absorb.Inv s₀ c' s')) := by
    intro c' hcc hcl t ht
    refine wp_test fun s' g' m' rd' wr' z' => wp_nil ?_
    have ht' : VG.Proof.Sha3.X86_64.Stream.Absorb.Inv s₀ c' s' :=
      { ht.toCommon.of_gpr (fun r _ => by rw [g']) m' rd' wr' with
        r12 := by rw [g']; exact ht.r12
        repr := by rw [m']; exact ht.repr }
    have hz : isa.eval .ne s' = some (!decide (VG.Proof.Sha3.X86_64.Stream.Absorb.len s₀ - c' = 0)) := by
      simp only [eval, z', ht.r14, BitVec.and_self, ofNat_beq_zero (show VG.Proof.Sha3.X86_64.Stream.Absorb.len s₀ - c' < 2 ^ 64 by omega),
        Option.map_some]
    by_cases he : c' = VG.Proof.Sha3.X86_64.Stream.Absorb.len s₀
    · exact ⟨c', hcc, hcl, .inl ⟨by rw [hz]; simp [he], he, he ▸ ht'⟩⟩
    · exact ⟨c', hcc, hcl, .inr ⟨by rw [hz]; simp; omega, by omega, ht'⟩⟩
  refine WP.seq (WP.mono (Q := fun s₁ => ∃ n, 0 < n ∧ (VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ + c) % VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ + n ≤ VG.Proof.Sha3.X86_64.Stream.Absorb.rt s₀ ∧
      c + n ≤ VG.Proof.Sha3.X86_64.Stream.Absorb.len s₀ ∧ VG.Proof.Sha3.X86_64.Stream.Absorb.After s₀ s₇ c n s₁) ?_
    fun s₁ ⟨n, hn, hfit, hcn, hA⟩ => WP.seq (WP.mono (VG.Proof.Sha3.X86_64.Stream.Absorb.after_ok hp hn hfit hI₇ hA)
      fun s' h => tail (c + n) (by omega) hcn s' h))
  refine WP.ite b (by rw [show isa.eval .e s₇ = s₇.zf from rfl, z₇]) (fun hb => ?_) (fun _ => ?_)
  · obtain ⟨m8, l8⟩ := hb₇ hb
    exact WP.mono (VG.Proof.Sha3.X86_64.Stream.Absorb.body_word hp (by omega) hI₇ m8) fun s₁ ⟨hC, h12, hz, hst⟩ =>
      ⟨8, by decide, by omega, by omega, hC, h12, hz, hst⟩
  · refine WP.mono (VG.Proof.Sha3.X86_64.Stream.Absorb.body_block hp hc hI₇) fun s₁ ⟨hC, h12, hz, hst⟩ =>
      ⟨1, by decide, by omega, by omega, hC, h12, hz, ?_⟩
    rw [hst]
    simp [bytesAt, xorAt_single]

/-! ## The epilogue -/

theorem epilogue_ok {s₀ : State} (hp : VG.Proof.Sha3.X86_64.Stream.Absorb.Pre s₀) {s : State} (hI : VG.Proof.Sha3.X86_64.Stream.Absorb.Inv s₀ (VG.Proof.Sha3.X86_64.Stream.Absorb.len s₀) s) :
    WP isa (.block (.mov .rax (.reg .r12) :: restore)) s fun s' =>
      gprPreserved s₀ s' ∧ Proof.Sha3.absorbX86_64.post s₀ s' := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  refine wp_mov fun s₁ u₁ => ?_
  have r15 : s₁.gpr .r15 = VG.Proof.Sha3.X86_64.Stream.Absorb.scr s₀ := by rw [u₁.other _ (by decide), hI.r15]
  refine WP.mono (Spill.restore_ok .r15 saved s₀.gpr s₁ (by decide) (fun p hp' => ?_)
    (by rw [r15, u₁.mem]; exact hI.saved)) fun s' ⟨h₁, h₂, m, _⟩ => ?_
  · have := VG.Proof.Sha3.X86_64.Stream.Absorb.saved_bound p hp'
    rw [r15]
    exact ⟨VG.Proof.Sha3.X86_64.Stream.Absorb.scR s₀, by simp [u₁.rd, u₁.wr, hI.wr, hp.wr], contains_offset (by omega) (by omega)⟩
  · have ax : s'.gpr .rax = s₁.gpr .rax := h₂ _ (by decide)
    refine ⟨⟨Spill.calleeSaved_ok h₁ h₂ (by decide) (by rw [u₁.other _ (by decide), hI.rsp]), ?_⟩,
      fun msg hm hpm => ?_, ?_⟩
    · rw [m, u₁.mem]
      exact hI.frame.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_st, hp.ret_scr, VG.Proof.Sha3.X86_64.Stream.Absorb.ret_stk s₀⟩)
        (by decide)
    · rw [Proof.Sha3.repr_iff, m, u₁.mem]
      exact hI.repr msg ⟨hm, hpm⟩
    · rw [ax, u₁.gpr, hI.r12, toNat_ofNat_lt (by have := Nat.mod_lt (VG.Proof.Sha3.X86_64.Stream.Absorb.pos s₀ + VG.Proof.Sha3.X86_64.Stream.Absorb.len s₀) hr₀; omega)]

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : VG.Proof.Sha3.X86_64.Stream.Absorb.Pre s₀) :
    WP isa absorb s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Sha3.absorbX86_64.post s₀ s' := by
  unfold absorb
  refine WP.seq (WP.mono (VG.Proof.Sha3.X86_64.Stream.Absorb.prologue_ok hp) fun s₁ ⟨hI, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := VG.Proof.Sha3.X86_64.Stream.Absorb.Inv s₀ (VG.Proof.Sha3.X86_64.Stream.Absorb.len s₀)) ?_ fun s₂ hI₂ => VG.Proof.Sha3.X86_64.Stream.Absorb.epilogue_ok hp hI₂)
  refine WP.ite (decide (VG.Proof.Sha3.X86_64.Stream.Absorb.len s₀ = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact wp_nil (by rw [hb]; exact hI)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun n s => ∃ c, n = VG.Proof.Sha3.X86_64.Stream.Absorb.len s₀ - c ∧ c < VG.Proof.Sha3.X86_64.Stream.Absorb.len s₀ ∧ VG.Proof.Sha3.X86_64.Stream.Absorb.Inv s₀ c s) ?_ (VG.Proof.Sha3.X86_64.Stream.Absorb.len s₀) s₁
      ⟨0, rfl, by omega, hI⟩
    rintro n s ⟨c, rfl, hc, hI⟩
    refine WP.mono (VG.Proof.Sha3.X86_64.Stream.Absorb.body_ok hp hc hI) fun s' ⟨c', hcc, hcl, h⟩ => ?_
    rcases h with ⟨he, _, hI'⟩ | ⟨he, hc', hI'⟩
    · exact .inl ⟨he, hI'⟩
    · exact .inr ⟨he, VG.Proof.Sha3.X86_64.Stream.Absorb.len s₀ - c', by omega, c', rfl, hc', hI'⟩

/-! ## Constant time -/

/-- The initial taint: the arguments and `rsp` are public, and `rdi` and `r9`
point at the writable regions. -/
def τ₀ : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], flags := false, lens := [200, 640],
    bases := [(.rdi, 0, 0), (.r9, 1, 0)] }

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha3.absorbX86_64.pre s₁)
    (h₂ : Proof.Sha3.absorbX86_64.pre s₂) (hpub : Proof.Sha3.absorbX86_64.pub s₁ s₂) :
    X86_64.Taint.Agree VG.Proof.Sha3.X86_64.Stream.Absorb.τ₀ s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hpub
  have wf : ∀ s, Proof.Sha3.absorbX86_64.pre s → X86_64.Taint.Wf VG.Proof.Sha3.X86_64.Stream.Absorb.τ₀ s := by
    intro s hs
    obtain ⟨-, hw, hd, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, VG.Proof.Sha3.X86_64.Stream.Absorb.τ₀], by simp [hw, hd], by simp [hw]⟩, fun p hp => ?_⟩
    simp only [VG.Proof.Sha3.X86_64.Stream.Absorb.τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo⟩
  · simp only [VG.Proof.Sha3.X86_64.Stream.Absorb.τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [h₁.2.1, h₂.2.1, p1, p6]
  · intro sl h; simp [VG.Proof.Sha3.X86_64.Stream.Absorb.τ₀] at h
  · intro sl h; simp [VG.Proof.Sha3.X86_64.Stream.Absorb.τ₀] at h

/-- A state satisfying the precondition (with no data). -/
def sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 72 | .rcx => 0x2000 | .r9 => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 200⟩, ⟨0x3000, 640⟩]

theorem absorb_correct (s : State) (hs : Proof.Sha3.absorbX86_64.pre s) :
    ∃ t s', Exec isa absorb s t s' ∧ abiPreserved s s' ∧ Proof.Sha3.absorbX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := VG.Proof.Sha3.X86_64.Stream.Absorb.correct (VG.Proof.Sha3.X86_64.Stream.Absorb.pre_of hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem absorb_ct : ConstantTime isa Proof.Sha3.absorbX86_64.pre Proof.Sha3.absorbX86_64.pub absorb
    := by
  exact VG.Taint.constantTime (A := taint) VG.Proof.Sha3.X86_64.Stream.Absorb.τ₀ (fun _ _ h₁ h₂ hp => VG.Proof.Sha3.X86_64.Stream.Absorb.agree₀ h₁ h₂ hp)
    (by taint_decide_weak VG.Proof.Sha3.X86_64.dropRC)

theorem absorb_verified :
    Verified X86_64.target Impl.Sha3.X86_64.Stream.absorb (Spec.Sha3.absorbScratchContract X86_64.abi 8) :=
  Verified.of_correct VG.Proof.Sha3.X86_64.Stream.Absorb.absorb_correct VG.Proof.Sha3.X86_64.Stream.Absorb.absorb_ct (by
    sig_implies [Spec.Sha3.absorbScratchContract, Spec.Sha3.absorbScratchSig, Spec.Sha3.absorbPre, Spec.Sha3.absorbPost, Proof.Sha3.absorbX86_64, X86_64.abi,
      X86_64.argRegs] [Proof.Sha3.X86_64.Stream.Absorb.sat] using
      Proof.Sha3.X86_64.Stream.Absorb.sat)

end VG.Proof.Sha3.X86_64.Stream.Absorb

end
