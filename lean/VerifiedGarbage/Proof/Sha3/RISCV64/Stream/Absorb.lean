module

public import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Common
public import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Sha3.Lanes
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Wp
import VerifiedGarbage.Proof.Sha3.RISCV64.Call
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Sha3.RISCV64.Contract
public import VerifiedGarbage.Spec.Sha3.Contract

/-!
# The SHA-3 sponge on RISC-V: `absorb`

The structure of the PPC64LE proof (`Proof/Sha3/PPC64LE/Stream/Absorb.lean`),
a lane (`body_word`) or a byte (`body_byte`) at a time, in the frame of
`Stream/Common.lean`.
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64.Stream.Absorb

open VG VG.RISCV64 VG.RISCV64.Wp VG.Impl.Sha3.RISCV64.Stream
open VG.Proof.Sha3.RISCV64 VG.Proof.Sha3.RISCV64.Stream
open VG.Proof.Sha3 (Rep rep_append xorByte stateAt_xorByte ofNat_beq_zero sub_beq_zero sub_ofNat
  xor_setWidth writeW8_apply bytesAt_succ bytesAt_length toNat_ofNat_lt xorAt xorAt_single byteOf_xorAt
  byteOf_stateAt writeW64_byte)
open VG.Spec.Sha3 (stateAt keccakF bytesAt rates)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .a0
abbrev rt : Nat := (s₀.gpr .a1).toNat
abbrev pos : Nat := (s₀.gpr .a2).toNat
abbrev dp : Addr := s₀.gpr .a3
abbrev len : Nat := (s₀.gpr .a4).toNat
abbrev stR : Region := ⟨st s₀, 200⟩
abbrev dR : Region := ⟨dp s₀, len s₀⟩
/-- The first `c` bytes of data. -/
abbrev D (c : Nat) : List Byte := bytesAt s₀.mem (dp s₀) c

/-- The messages the initial state and position represent. -/
def Msg (msg : List Byte) : Prop :=
  stateAt s₀.mem (st s₀) = Rep (rt s₀) msg ∧ pos s₀ = msg.length % rt s₀

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀]
  wr : s₀.wr = [stR s₀]
  d_st : (dR s₀).Disjoint (stR s₀)
  stk : Stk s₀
  k_st : (KR s₀).Disjoint (stR s₀)
  k_d : (KR s₀).Disjoint (dR s₀)
  rate : rt s₀ ∈ rates
  pos_lt : pos s₀ < rt s₀

theorem pre_of {s₀ : State} (h : Proof.Sha3.absorbRISCV64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, ⟨h4, h5⟩, h6, h7, h8, h9⟩

theorem Pre.rt_pos {s₀ : State} (hp : Pre s₀) : 0 < rt s₀ ∧ rt s₀ ≤ 168 := by
  have h := Proof.Sha3.rate_bounds hp.rate
  omega

theorem len_lt (s₀ : State) : len s₀ < 2 ^ 64 := (s₀.gpr .a4).isLt

/-- The callee-saved registers our code never writes. -/
abbrev untouched : List Reg := [.s0, .s1, .s7, .s8, .s9, .s10, .s11]

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = [dR s₀]
  wr : s.wr = [BR s₀, stR s₀]
  sp : s.sp = B s₀
  s2 : s.gpr .s2 = st s₀
  s3 : s.gpr .s3 = s₀.gpr .a1
  s5 : s.gpr .s5 = dp s₀ + BitVec.ofNat 64 c
  s6 : s.gpr .s6 = BitVec.ofNat 64 (len s₀ - c)
  frame : Frame [stR s₀, KR s₀] s₀.mem s.mem
  saved : Saved (B s₀) s₀.gpr s.mem
  untouched : ∀ r ∈ untouched, s.gpr r = s₀.gpr r

/-- The loop invariant: the state represents the message followed by the
first `c` bytes of data. -/
structure Inv (s₀ : State) (c : Nat) (s : State) : Prop extends Common s₀ c s where
  s4 : s.gpr .s4 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀)
  repr : ∀ msg, Msg s₀ msg → stateAt s.mem (st s₀) = Rep (rt s₀) (msg ++ D s₀ c)

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (h : Common s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dp s₀ + BitVec.ofNat 64 i) = s₀.mem (dp s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := dR s₀) (by simpa using ⟨hp.d_st, hp.k_d.symm⟩) (Nat.le_of_lt (len_lt s₀)) hi

theorem slots_disjoint {s₀ : State} (hp : Pre s₀) :
    ∀ d, 512 ≤ d → d + 8 ≤ 560 → ∀ r ∈ [stR s₀, KR s₀], r ≠ KR s₀ →
      Region.Disjoint ⟨B s₀ + BitVec.ofNat 64 d, 8⟩ r := by
  intro d h₁ h₂ r hr hne
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.k_st.sub_left (hp.stk.slot_sub h₁ h₂)
  · exact absurd rfl hne

/-! ## The prologue -/

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block setup) (allocd 560 s₀) (Inv s₀ 0) := by
  have hk := hp.stk
  unfold setup
  refine save_ok (s := allocd 560 s₀) hk.B_al (fun d hd₁ hd₂ => ⟨BR s₀, List.mem_cons_self ..,
      Offset.contains_base _ (by omega) (by omega)⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ sv₁ f₁ => ?_
  refine wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ =>
    wp_mv fun s₆ u₆ => WP.block_nil ?_
  have hm : s₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have f₁' : Frame [stR s₀, KR s₀] s₀.mem s₁.mem :=
    f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨KR s₀, by simp, by
        rw [show (allocd 560 s₀).sp = B s₀ from rfl, hk.B_off]; exact sub_K s₀ (by omega)⟩
  have g : ∀ r, r ≠ .t0 → s₁.gpr r = s₀.gpr r := fun r h => g₁ r h
  refine ⟨⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hm]; exact f₁', by rw [hm]; exact sv₁,
      fun r hr => ?_⟩, ?_, fun msg ⟨hs, _⟩ => ?_⟩
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]; exact hp.rd
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]; simp only [allocd, hp.wr]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]; rfl
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, g _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), g _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g _ (by decide)]; simp
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g _ (by decide), Nat.sub_zero]; simp [len]
  · have : r ≠ .s2 ∧ r ≠ .s3 ∧ r ≠ .s4 ∧ r ≠ .s5 ∧ r ≠ .s6 ∧ r ≠ .t0 := by revert r; decide
    rw [u₆.other _ this.2.2.2.2.1, u₅.other _ this.2.2.2.1, u₄.other _ this.2.2.1,
      u₃.other _ this.2.1, u₂.other _ this.1, g _ this.2.2.2.2.2]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), g _ (by decide), Nat.add_zero,
      Nat.mod_eq_of_lt hp.pos_lt]
    simp [pos]
  · rw [hm, show D s₀ 0 = [] by simp [bytesAt], List.append_nil, ← hs]
    exact Proof.Sha3.stateAt_congr fun i hi =>
      f₁.bytes (R := stR s₀) (by
        simpa using (hp.k_st.sub_left (by
          rw [show (allocd 560 s₀).sp = B s₀ from rfl, hk.B_off]; exact sub_K s₀ (by omega))).symm)
        (by show 200 ≤ 2 ^ 64; decide) hi

/-! ## One iteration -/

/-- The byte at position `j` XORed in. -/
theorem body_byte {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < len s₀) {s : State}
    (hI : Inv s₀ c s) :
    WP isa (.block absorbByte) s fun s' =>
      Common s₀ (c + 1) s' ∧ s'.gpr .s4 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + 1) ∧
      stateAt s'.mem (st s₀) = xorByte (stateAt s.mem (st s₀)) ((pos s₀ + c) % rt s₀)
        (s₀.mem (dp s₀ + BitVec.ofNat 64 c)) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hl := len_lt s₀
  have hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  generalize hjd : (pos s₀ + c) % rt s₀ = j at hj ⊢
  have hr3 : s.gpr .s4 = BitVec.ofNat 64 j := by rw [hI.s4, hjd]
  have hsin : ∀ rs : List Region, stR s₀ ∈ rs → InRegions rs (st s₀ + BitVec.ofNat 64 j) 1 :=
    fun rs h => ⟨stR s₀, h, Offset.contains_base _ (by omega) (by omega)⟩
  refine wp_lbu (t := .t1) (a := dp s₀ + BitVec.ofNat 64 c) (by decide) (by rw [hI.s5]; simp)
    ⟨dR s₀, by simp [hI.rd], Offset.contains_base _ (by omega) (by omega)⟩ fun s₁ u₁ => ?_
  refine wp_add fun s₂ u₂ => ?_
  have ea : s₂.gpr .t2 + BitVec.ofNat 64 0 = st s₀ + BitVec.ofNat 64 j := by
    rw [u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), hI.s2, hr3]; simp
  refine wp_lbu (t := .t3) (a := st s₀ + BitVec.ofNat 64 j) (by decide) ea
    (hsin _ (by simp [u₂.rd, u₂.wr, u₁.rd, u₁.wr, hI.rd, hI.wr])) fun s₃ u₃ => ?_
  refine wp_xor fun s₄ u₄ => ?_
  refine wp_sb (a := st s₀ + BitVec.ofNat 64 j) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide)]; exact ea)
    (hsin _ (by simp [u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr])) fun s₅ g₅ => ?_
  refine wp_addi (by decide) fun s₆ u₆ => wp_addi (by decide) fun s₇ u₇ =>
    wp_subi (imm := 1) (by decide) fun s₈ u₈ => WP.block_nil ?_
  have hv : (s₄.gpr .t1).setWidth 8 =
      s₀.mem (dp s₀ + BitVec.ofNat 64 c) ^^^ s.mem (st s₀ + BitVec.ofNat 64 j) := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, u₃.gpr, u₂.mem, u₁.mem,
      xor_setWidth, hI.data hp hc]
  have hm₈ : s₈.mem = s.mem.writeW (st s₀ + BitVec.ofNat 64 j)
      (s₀.mem (dp s₀ + BitVec.ofNat 64 c) ^^^ s.mem (st s₀ + BitVec.ofNat 64 j)) := by
    rw [u₈.mem, u₇.mem, u₆.mem, g₅.mem, hv, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hf : Frame [stR s₀] s.mem s₈.mem := by
    rw [hm₈]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by omega))
  have g : ∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .s5 → r ≠ .s4 → r ≠ .s6 →
      s₈.gpr r = s.gpr r := fun r h1 h2 h3 h4 h33 h5 => by
    rw [u₈.other r h5, u₇.other r h33, u₆.other r h4, g₅.gpr, u₄.other r h1, u₃.other r h3,
      u₂.other r h2, u₁.other r h1]
  have h3 : s₈.gpr .s4 = BitVec.ofNat 64 (j + 1) := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hr3, ← BitVec.ofNat_add]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩, h3, ?_⟩
  · rw [u₈.rd, u₇.rd, u₆.rd, g₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [u₈.wr, u₇.wr, u₆.wr, g₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  · rw [u₈.sp, u₇.sp, u₆.sp, g₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, hI.sp]
  · rw [g .s2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.s2]
  · rw [g .s3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.s3]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.s5, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.s6, sub_ofNat (by omega), Nat.sub_sub]
  · exact hI.frame.trans (hf.mono (by simp))
  · exact hI.saved.frame (fun d h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.k_st.sub_left (hp.stk.slot_sub h₁ h₂)) hf
  · have hne : r ≠ .t1 ∧ r ≠ .t2 ∧ r ≠ .t3 ∧ r ≠ .s5 ∧ r ≠ .s4 ∧ r ≠ .s6 := by revert r; decide
    rw [g r hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2]
    exact hI.untouched r hr
  · refine stateAt_xorByte (by omega) ?_ fun i hi hij => ?_
    · rw [hm₈, writeW8_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl), BitVec.xor_comm]
    · rw [hm₈, writeW8_apply, ite_eq_right_of_eq_false _ _
        (eq_false (VG.Proof.Sha3.ne_of_lt200 hi (by omega) hij))]

/-- The bytes `c … c + n - 1` of the data follow the first `c`. -/
theorem bytesAt_add (m : Mem) (p : Addr) (c : Nat) :
    ∀ n, bytesAt m p (c + n) = bytesAt m p c ++ bytesAt m (p + BitVec.ofNat 64 c) n
  | 0 => by simp [bytesAt]
  | n + 1 => by
    rw [← Nat.add_assoc, bytesAt_succ, bytesAt_add m p c n, bytesAt_succ, List.append_assoc,
      BitVec.add_assoc, ← BitVec.ofNat_add]

theorem rate_mod8 {r : Nat} (h : r ∈ rates) : r % 8 = 0 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl

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

/-- The lane of data at `c` XORed into the lane at position `j`, both
aligned. -/
theorem body_word {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c + 8 ≤ len s₀) {s : State}
    (hI : Inv s₀ c s) (hj8 : (pos s₀ + c) % rt s₀ % 8 = 0)
    (ht2 : s.gpr .t2 = st s₀ + BitVec.ofNat 64 ((pos s₀ + c) % rt s₀))
    (hal : (st s₀ + BitVec.ofNat 64 ((pos s₀ + c) % rt s₀)).toNat % 8 = 0)
    {al : Bool} (hdal : al = true → (dp s₀ + BitVec.ofNat 64 c).toNat % 8 = 0) :
    WP isa (.block (absorbLane al)) s fun s' =>
      Common s₀ (c + 8) s' ∧ s'.gpr .s4 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + 8) ∧
      stateAt s'.mem (st s₀) = xorAt (stateAt s.mem (st s₀)) ((pos s₀ + c) % rt s₀)
        (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) 8) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hl := len_lt s₀
  have h8 := rate_mod8 hp.rate
  have hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  generalize hjd : (pos s₀ + c) % rt s₀ = j at hj hj8 ht2 hal ⊢
  have hj' : j + 8 ≤ rt s₀ := by omega
  have hr3 : s.gpr .s4 = BitVec.ofNat 64 j := by rw [hI.s4, hjd]
  have hsin : ∀ rs : List Region, stR s₀ ∈ rs → InRegions rs (st s₀ + BitVec.ofNat 64 j) 8 :=
    fun rs h => ⟨stR s₀, h, Offset.contains_base _ (by omega) (by omega)⟩
  unfold absorbLane
  refine loadData_ok (a := dp s₀ + BitVec.ofNat 64 c) (by rw [hI.s5]) hdal
    ⟨dR s₀, by simp [hI.rd], Offset.contains_base _ (by omega) (by omega)⟩ fun s₁ u₁ => ?_
  refine wp_ld (t := .t3) (a := st s₀ + BitVec.ofNat 64 j) (by decide)
    (by rw [u₁.other _ (by decide) (by decide) (by decide), ht2]; simp) hal
    (hsin _ (by simp [u₁.rd, u₁.wr, hI.rd, hI.wr])) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  refine wp_sd (a := st s₀ + BitVec.ofNat 64 j) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide) (by decide) (by decide), ht2]; simp) hal
    (hsin _ (by simp [u₃.wr, u₂.wr, u₁.wr, hI.wr])) fun s₄ g₄ => ?_
  refine wp_addi (by decide) fun s₅ u₅ => wp_addi (by decide) fun s₆ u₆ =>
    wp_subi (imm := 8) (by decide) fun s₇ u₇ => WP.block_nil ?_
  have hv : s₃.gpr .t1 = s.mem.readW (dp s₀ + BitVec.ofNat 64 c) 64 ^^^
      s.mem.readW (st s₀ + BitVec.ofNat 64 j) 64 := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem]
  have hm₇ : s₇.mem = s.mem.writeW (st s₀ + BitVec.ofNat 64 j) (s₃.gpr .t1) := by
    rw [u₇.mem, u₆.mem, u₅.mem, g₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hf : Frame [stR s₀] s.mem s₇.mem := by
    rw [hm₇]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by omega))
  have g : ∀ r, r ≠ .t1 → r ≠ .t3 → r ≠ .s5 → r ≠ .s4 → r ≠ .s6 → r ≠ .t4 →
      s₇.gpr r = s.gpr r := fun r h1 h3 h4 h33 h5 h6 => by
    rw [u₇.other r h5, u₆.other r h33, u₅.other r h4, g₄.gpr, u₃.other r h1, u₂.other r h3,
      u₁.other r h1 h3 h6]
  have h3 : s₇.gpr .s4 = BitVec.ofNat 64 (j + 8) := by
    rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), g₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide) (by decide) (by decide), hr3,
      ← BitVec.ofNat_add]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩, h3, ?_⟩
  · rw [u₇.rd, u₆.rd, u₅.rd, g₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, g₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  · rw [u₇.sp, u₆.sp, u₅.sp, g₄.sp, u₃.sp, u₂.sp, u₁.sp, hI.sp]
  · rw [g .s2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.s2]
  · rw [g .s3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.s3]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, g₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide) (by decide) (by decide), hI.s5,
      BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), g₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide) (by decide) (by decide), hI.s6,
      sub_ofNat (by omega), Nat.sub_sub]
  · exact hI.frame.trans (hf.mono (by simp))
  · exact hI.saved.frame (fun d h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.k_st.sub_left (hp.stk.slot_sub h₁ h₂)) hf
  · have hne : r ≠ .t1 ∧ r ≠ .t3 ∧ r ≠ .s5 ∧ r ≠ .s4 ∧ r ≠ .s6 ∧ r ≠ .t4 := by revert r; decide
    rw [g r hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2]
    exact hI.untouched r hr
  · rw [hm₇]
    refine stateAt_write_lane (by omega) (bytesAt_length _ _ _) fun d hd => ?_
    rw [hv, BitVec.extractLsb'_xor, Mem.readW, Mem.readW, BitVec.setWidth_eq, BitVec.setWidth_eq,
      Mem.extractLsb'_read _ _ (show d < 64 / 8 by omega),
      Mem.extractLsb'_read _ _ (show d < 64 / 8 by omega),
      BitVec.xor_comm, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 1
    simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hd,
      Option.map_some, Option.getD_some]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, hI.data hp (by omega)]

theorem keep_preserved : ∀ r ∈ untouched, r ∈ preserved := by decide

/-- The permutation if the block is complete, after `n` bytes of data that
fit in it. -/
theorem full_ok {s₀ : State} (hp : Pre s₀) {c n : Nat} (hn : 0 < n)
    (hfit : (pos s₀ + c) % rt s₀ + n ≤ rt s₀) {s s₁ : State}
    (hI : Inv s₀ c s) (hC : Common s₀ (c + n) s₁)
    (h3 : s₁.gpr .s4 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + n))
    (hst : stateAt s₁.mem (st s₀) = xorAt (stateAt s.mem (st s₀)) ((pos s₀ + c) % rt s₀)
        (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) n)) :
    WP isa permuteIfFull s₁ (Inv s₀ (c + n)) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hk := hp.stk
  have hlen : ∀ msg, Msg s₀ msg → (msg ++ D s₀ c).length % rt s₀ = (pos s₀ + c) % rt s₀ :=
    fun msg ⟨_, hpm⟩ => by rw [List.length_append, bytesAt_length, hpm, Nat.mod_add_mod]
  have hrep : ∀ msg, Msg s₀ msg → Rep (rt s₀) (msg ++ D s₀ (c + n)) =
      if (pos s₀ + c) % rt s₀ + n = rt s₀ then keccakF (stateAt s₁.mem (st s₀))
      else stateAt s₁.mem (st s₀) := fun msg hm => by
    rw [D, bytesAt_add, ← List.append_assoc, rep_append hr₀ (by omega) _ _
      (by rw [bytesAt_length]; exact hn) (by rw [bytesAt_length, hlen msg hm]; exact hfit),
      hlen msg hm, bytesAt_length, hst, hI.repr msg hm]
  have hpc : (pos s₀ + (c + n)) % rt s₀ = if (pos s₀ + c) % rt s₀ + n = rt s₀ then 0
      else (pos s₀ + c) % rt s₀ + n := by
    have e := Nat.div_add_mod (pos s₀ + c) (rt s₀)
    rw [show pos s₀ + (c + n) = (pos s₀ + c) + n by omega]
    generalize (pos s₀ + c) % rt s₀ = j at e hfit ⊢
    generalize (pos s₀ + c) / rt s₀ = q at e
    rw [← e]
    split
    · rw [Nat.add_assoc, ‹j + n = rt s₀›, ← Nat.mul_succ, Nat.mul_mod_right]
    · rw [Nat.add_assoc, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  unfold permuteIfFull
  refine WP.seq (wp_sub fun s₂ u₂ => WP.block_nil ?_)
  have hC₂ : Common s₀ (c + n) s₂ :=
    { hC with rd := u₂.rd.trans hC.rd, wr := u₂.wr.trans hC.wr, sp := u₂.sp.trans hC.sp
              s2 := (u₂.other _ (by decide)).trans hC.s2, s3 := (u₂.other _ (by decide)).trans hC.s3
              s5 := (u₂.other _ (by decide)).trans hC.s5, s6 := (u₂.other _ (by decide)).trans hC.s6
              frame := u₂.mem ▸ hC.frame, saved := u₂.mem ▸ hC.saved
              untouched := fun r hr => (u₂.other r (by revert r; decide)).trans (hC.untouched r hr) }
  have hz : isa.eval (.zero .t1) s₂ = some (decide ((pos s₀ + c) % rt s₀ + n = rt s₀)) := by
    show eval (.zero .t1) s₂ = _
    rw [eval_zero, u₂.gpr, h3, hC.s3, sub_beq_zero (by have := (s₀.gpr .a1).isLt; omega)]
  refine WP.ite (decide ((pos s₀ + c) % rt s₀ + n = rt s₀)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine WP.seq (wp_li (by decide) fun s₃ u₃ => WP.block_nil ?_)
    have sp₃ : s₃.sp = B s₀ := by rw [u₃.sp, hC₂.sp]
    refine permuteAt_ok (st := st s₀) (by rw [u₃.other _ (by decide), hC₂.s2])
      (by rw [sp₃]; exact hk.B_al) (by rw [sp₃]; exact hk.B_608)
      (by rw [sp₃]; exact (hp.k_st.sub_left hk.scr_sub).symm)
      (by rw [sp₃]; exact hp.k_st.sub_left hk.below_sub)
      (by
        rw [u₃.wr, hC₂.wr, sp₃]
        apply Covers.of_sub
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
        · exact ⟨BR s₀, by simp, 0, by simp, by simp⟩)
      fun s₄ rd₄ wr₄ sp₄ cs₄ f₄ e₄ => ?_
    rw [sp₃] at f₄
    have hm₃ : s₃.mem = s₂.mem := u₃.mem
    refine ⟨⟨hC₂.c_le, by rw [rd₄, u₃.rd, hC₂.rd], by rw [wr₄, u₃.wr, hC₂.wr], by rw [sp₄, sp₃],
      by rw [cs₄ _ (by decide), u₃.other _ (by decide), hC₂.s2],
      by rw [cs₄ _ (by decide), u₃.other _ (by decide), hC₂.s3],
      by rw [cs₄ _ (by decide), u₃.other _ (by decide), hC₂.s5],
      by rw [cs₄ _ (by decide), u₃.other _ (by decide), hC₂.s6], ?_, ?_,
      fun r hr => by rw [cs₄ _ (keep_preserved r hr), u₃.other _ (by revert r; decide),
        hC₂.untouched r hr]⟩, ?_, fun msg hm => ?_⟩
    · rw [hm₃] at f₄
      exact hC₂.frame.trans (f₄.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨stR s₀, by simp, fun _ h => h⟩
        · exact ⟨KR s₀, by simp, hk.scr_sub⟩
        · exact ⟨KR s₀, by simp, hk.below_sub⟩)
    · rw [hm₃] at f₄
      refine hC₂.saved.frame (fun d h₁ h₂ r hr => ?_) f₄
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.k_st.sub_left (hk.slot_sub h₁ h₂)
      · exact slot_scr s₀ h₁ h₂
      · exact hk.slot_below h₁ h₂
    · rw [cs₄ _ (by decide), u₃.gpr, hpc, ite_eq_left_of_eq_true _ _ (eq_true hb)]
    · rw [e₄, hm₃, u₂.mem, hrep msg hm, ite_eq_left_of_eq_true _ _ (eq_true hb)]
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.block_nil { hC₂ with s4 := ?_, repr := fun msg hm => ?_ }
    · rw [u₂.other _ (by decide), h3, hpc, ite_eq_right_of_eq_false _ _ (eq_false hb)]
    · rw [u₂.mem, hrep msg hm, ite_eq_right_of_eq_false _ _ (eq_false hb)]

theorem body_ok {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < len s₀) {s : State}
    (hI : Inv s₀ c s) :
    WP isa absorbBody s fun s' => ∃ c', c < c' ∧ c' ≤ len s₀ ∧ Inv s₀ c' s' := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have h8 := rate_mod8 hp.rate
  have hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  have hl := len_lt s₀
  unfold absorbBody
  refine WP.seq (WP.mono (laneCheck_ok hI.s2 hI.s4 hI.s6 (by omega) (by omega))
    fun s₇ ⟨oth, ht2, m₇, rd₇, wr₇, sp₇, hz, hd⟩ => ?_)
  have o : ∀ r, r ≠ .t1 ∧ r ≠ .t2 ∧ r ≠ .t3 ∧ r ≠ .t4 → s₇.gpr r = s.gpr r :=
    fun r h => oth r h.1 h.2.1 h.2.2.1 h.2.2.2
  have hI₇ : Inv s₀ c s₇ :=
    { c_le := hI.c_le, rd := rd₇.trans hI.rd, wr := wr₇.trans hI.wr, sp := sp₇.trans hI.sp
      s2 := (o _ (by decide)).trans hI.s2, s3 := (o _ (by decide)).trans hI.s3
      s5 := (o _ (by decide)).trans hI.s5, s6 := (o _ (by decide)).trans hI.s6
      frame := m₇ ▸ hI.frame, saved := m₇ ▸ hI.saved
      untouched := fun r hr => (o r (by revert r; decide)).trans (hI.untouched r hr)
      s4 := (o _ (by decide)).trans hI.s4
      repr := fun msg hm => by rw [m₇]; exact hI.repr msg hm }
  refine WP.seq (WP.mono (Q := fun (s₁ : State) => ∃ n, 0 < n ∧ (pos s₀ + c) % rt s₀ + n ≤ rt s₀ ∧
      c + n ≤ len s₀ ∧ Common s₀ (c + n) s₁ ∧
      s₁.gpr .s4 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + n) ∧
      stateAt s₁.mem (st s₀) = xorAt (stateAt s₇.mem (st s₀)) ((pos s₀ + c) % rt s₀)
        (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) n)) ?_
    fun s₁ ⟨n, hn, hfit, hcn, hC, h3, hst⟩ => WP.mono (full_ok hp hn hfit hI₇ hC h3 hst)
      fun s' h => ⟨c + n, by omega, hcn, h⟩)
  unfold step
  refine WP.ite (s₇.gpr .t1 == 0) (by show eval (.zero .t1) s₇ = _; rw [eval_zero])
    (fun hb => ?_) (fun _ => ?_)
  · obtain ⟨m8, al, l8⟩ := hz (by simpa using hb)
    have lane : ∀ b : Bool, (b = true → (dp s₀ + BitVec.ofNat 64 c).toNat % 8 = 0) →
        WP isa (.block (absorbLane b)) s₇ fun s₁ => ∃ n, 0 < n ∧ (pos s₀ + c) % rt s₀ + n ≤ rt s₀ ∧
          c + n ≤ len s₀ ∧ Common s₀ (c + n) s₁ ∧
          s₁.gpr .s4 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + n) ∧
          stateAt s₁.mem (st s₀) = xorAt (stateAt s₇.mem (st s₀)) ((pos s₀ + c) % rt s₀)
            (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) n) := fun b hb =>
      WP.mono (body_word hp (by omega) hI₇ m8 ht2 al hb)
        fun s₁ ⟨hC, h3, hst⟩ => ⟨8, by decide, by omega, by omega, hC, h3, hst⟩
    refine WP.ite (s₇.gpr .t4 == 0) (by show eval (.zero .t4) s₇ = _; rw [eval_zero])
      (fun hb4 => lane true fun _ => ?_) (fun _ => lane false fun h => absurd h (by decide))
    rw [← hI.s5]; exact hd (by simpa using hb4)
  · refine WP.mono (body_byte hp hc hI₇) fun s₁ ⟨hC, h3, hst⟩ =>
      ⟨1, by decide, by omega, by omega, hC, h3, ?_⟩
    rw [hst]
    simp [bytesAt, xorAt_single]

/-! ## The whole function -/

theorem preserved_split : ∀ r ∈ preserved, r ∈ saved.map Prod.fst ∨ r ∈ untouched := by decide

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa absorb s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha3.absorbRISCV64.post s₀ s' := by
  have hk := hp.stk
  have hl := len_lt s₀
  have ⟨hr₀, _⟩ := hp.rt_pos
  unfold absorb withLoop frameBytes
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by have := hk.sp; omega) ?_
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ hI => ?_)
  refine WP.seq (WP.mono (Q := Inv s₀ (len s₀)) ?_ fun s₂ hI₂ => ?_)
  · refine WP.ite (decide (len s₀ = 0))
      (by show eval (.zero .s6) s₁ = _
          rw [eval_zero, hI.s6, Nat.sub_zero, ofNat_beq_zero (by omega)])
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      exact WP.block_nil (hb ▸ hI)
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.loop (M := isa) (fun n s => ∃ c, n = len s₀ - c ∧ c < len s₀ ∧ Inv s₀ c s) ?_
        (len s₀) s₁ ⟨0, rfl, by omega, hI⟩
      rintro n s ⟨c, rfl, hcl, hI⟩
      refine WP.mono (body_ok hp hcl hI) fun s' ⟨c', hcc, hcl', hI'⟩ => ?_
      have hz : isa.eval (.nonzero .s6) s' = some (decide (len s₀ - c' ≠ 0)) := by
        show eval (.nonzero .s6) s' = _
        rw [eval_nonzero, hI'.s6, bne, ofNat_beq_zero (by omega)]
        simp
      by_cases he : len s₀ - c' = 0
      · refine .inl ⟨by rw [hz]; simp [he], ?_⟩
        rwa [show c' = len s₀ by omega] at hI'
      · exact .inr ⟨by rw [hz]; simp [he], len s₀ - c', by omega, c', rfl, by omega, hI'⟩
  · refine epilogue_ok (g := s₀.gpr) (by rw [hI₂.sp]; exact hk.B_al)
      (fun d hd₁ hd₂ => by
        rw [hI₂.rd, hI₂.wr, hI₂.sp]
        exact ⟨BR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩)
      (by rw [hI₂.sp]; exact hI₂.saved) fun s' h0 hsv hother hm hrd hwr hsp => ?_
    refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun msg hR hpm => ?_, ?_⟩
    · show s'.gpr r = _
      rcases preserved_split r hr with h | h
      · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp h
        exact hsv p hp'
      · rw [hother r (by revert r; decide) (by revert r; decide) (by revert r; decide)]
        exact hI₂.untouched r h
    · show s'.sp + BitVec.ofNat 64 560 = s₀.sp
      rw [hsp, hI₂.sp, BitVec.sub_add_cancel]
    · exact hsv (.ra, 512) (by decide)
    · simp only [freed]
      rw [Proof.Sha3.repr_iff, hm]
      exact hI₂.repr msg ⟨hR, hpm⟩
    · simp only [freed]
      rw [h0, hI₂.s4, toNat_ofNat_lt (by have := Nat.mod_lt (pos s₀ + len s₀) hr₀; omega)]

end VG.Proof.Sha3.RISCV64.Stream.Absorb
