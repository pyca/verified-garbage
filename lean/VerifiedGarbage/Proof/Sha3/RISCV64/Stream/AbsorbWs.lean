module

public import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Absorb
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Sha3.Lanes
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Wp
import VerifiedGarbage.Proof.Sha3.RISCV64.Call
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
public import VerifiedGarbage.Proof.Sha3.RISCV64.Contract

/-!
# The SHA-3 sponge on RISC-V: `absorbWs`

`absorb` (`Absorb.lean`) with its working space passed in `scratch` (`a5`)
rather than in a frame on the stack: the same loop, a lane (`body_word`) or
a byte (`body_byte`) at a time, with the registers saved in `scratch`
(`Spill`) and the permutation's scratch space at its start (`permuteAtWs`).
The stack it uses is the permutation's frame, the 608 bytes below the stack
pointer.
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64.Stream.AbsorbWs

open VG VG.RISCV64 VG.RISCV64.Wp VG.Impl.Sha3.RISCV64.Stream
open VG.Proof.Sha3.RISCV64 VG.Proof.Sha3.RISCV64.Stream
open VG.Proof.Sha3.RISCV64.Stream.Absorb (st rt pos dp len stR dR D Msg len_lt bytesAt_add rate_mod8
  stateAt_write_lane)
open VG.Proof.Sha3 (Rep rep_append xorByte stateAt_xorByte ofNat_beq_zero sub_beq_zero sub_ofNat
  xor_setWidth writeW8_apply bytesAt_succ bytesAt_length toNat_ofNat_lt xorAt xorAt_single byteOf_xorAt
  byteOf_stateAt writeW64_byte)
open VG.Spec.Sha3 (stateAt keccakF bytesAt rates)

/-! ## The precondition -/

section
variable (s₀ : State)

/-- The working space. -/
abbrev ws : Addr := s₀.gpr .a5
abbrev wsR : Region := ⟨ws s₀, 640⟩
/-- Its first 512 bytes, the permutation's scratch space. -/
abbrev scrR : Region := ⟨ws s₀, 512⟩
/-- The slots of the saved registers in it. -/
abbrev slotR : Region := ⟨ws s₀ + BitVec.ofNat 64 512, 56⟩
/-- The permutation's frame, below the stack pointer. -/
abbrev PR : Region := ⟨s₀.sp - 608, 608⟩

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀]
  wr : s₀.wr = [stR s₀, wsR s₀]
  st_ws : (stR s₀).Disjoint (wsR s₀)
  d_st : (dR s₀).Disjoint (stR s₀)
  d_ws : (dR s₀).Disjoint (wsR s₀)
  ws_al : (ws s₀).toNat % 8 = 0
  ws_fit : (ws s₀).toNat + 640 ≤ 2 ^ 64
  sp_al : s₀.sp.toNat % 16 = 0
  sp : 608 ≤ s₀.sp.toNat
  p_st : (PR s₀).Disjoint (stR s₀)
  p_d : (PR s₀).Disjoint (dR s₀)
  p_ws : (PR s₀).Disjoint (wsR s₀)
  rate : rt s₀ ∈ rates
  pos_lt : pos s₀ < rt s₀

theorem pre_of {s₀ : State} (h : Proof.Sha3.absorbWsRISCV64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

theorem Pre.rt_pos {s₀ : State} (hp : Pre s₀) : 0 < rt s₀ ∧ rt s₀ ≤ 168 := by
  have h := Proof.Sha3.rate_bounds hp.rate
  omega

theorem savedWs_fits : Spill.Fits savedWs := by decide

theorem savedWs_bound : ∀ p ∈ savedWs, 512 ≤ p.2 ∧ p.2 + 8 ≤ 512 + 56 := by decide

theorem slot_ws (s₀ : State) : Region.Sub (slotR s₀) (wsR s₀) := Offset.sub_base _ (by omega)

theorem scr_ws (s₀ : State) : Region.Sub (scrR s₀) (wsR s₀) := Region.sub_prefix (by omega)

theorem slot_scr (s₀ : State) : (slotR s₀).Disjoint (scrR s₀) :=
  Offset.disjoint_base _ (by omega) (by omega)

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem slot_st : (slotR s₀).Disjoint (stR s₀) := hp.st_ws.symm.sub_left (slot_ws s₀)

theorem slot_p : (slotR s₀).Disjoint (PR s₀) := hp.p_ws.symm.sub_left (slot_ws s₀)

theorem st_scr : (stR s₀).Disjoint (scrR s₀) := (hp.st_ws.symm.sub_left (scr_ws s₀)).symm

theorem p_scr : (PR s₀).Disjoint (scrR s₀) := (hp.p_ws.symm.sub_left (scr_ws s₀)).symm

end Pre

/-- The callee-saved registers our code never writes. -/
abbrev untouched : List Reg := [.s0, .s1, .s8, .s9, .s10, .s11]

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = [dR s₀]
  wr : s.wr = [stR s₀, wsR s₀]
  sp : s.sp = s₀.sp
  s2 : s.gpr .s2 = st s₀
  s3 : s.gpr .s3 = s₀.gpr .a1
  s5 : s.gpr .s5 = dp s₀ + BitVec.ofNat 64 c
  s6 : s.gpr .s6 = BitVec.ofNat 64 (len s₀ - c)
  s7 : s.gpr .s7 = ws s₀
  frame : Frame [stR s₀, wsR s₀, PR s₀] s₀.mem s.mem
  saved : Spill.Saved (ws s₀) s₀.gpr savedWs s.mem
  untouched : ∀ r ∈ untouched, s.gpr r = s₀.gpr r

/-- The loop invariant: the state represents the message followed by the
first `c` bytes of data. -/
structure Inv (s₀ : State) (c : Nat) (s : State) : Prop extends Common s₀ c s where
  s4 : s.gpr .s4 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀)
  repr : ∀ msg, Msg s₀ msg → stateAt s.mem (st s₀) = Rep (rt s₀) (msg ++ Absorb.D s₀ c)

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (h : Common s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dp s₀ + BitVec.ofNat 64 i) = s₀.mem (dp s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_ws, hp.p_d.symm⟩)
    (Nat.le_of_lt (len_lt s₀)) hi

/-- A write within the state keeps the saved registers. -/
theorem Common.saved_st {s₀ : State} (hp : Pre s₀) {m m' : Mem}
    (h : Spill.Saved (ws s₀) s₀.gpr savedWs m) (hf : Frame [stR s₀] m m') :
    Spill.Saved (ws s₀) s₀.gpr savedWs m' :=
  h.frame_in savedWs_bound hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.slot_st

/-! ## The prologue -/

theorem setupWs_eq : setupWs = mov .t0 .a5 :: (Spill.saveCode .t0 savedWs ++
    [mov .s2 .a0, mov .s3 .a1, mov .s4 .a2, mov .s5 .a3, mov .s6 .a4, mov .s7 .a5]) := rfl

theorem savedWs_ne_t0 : ∀ p ∈ savedWs, p.1 ≠ .t0 := by decide

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block setupWs) s₀ (Inv s₀ 0) := by
  rw [setupWs_eq]
  refine wp_mv fun s₁ u₁ => ?_
  have g1 : s₁.gpr .t0 = ws s₀ := u₁.gpr
  refine Spill.save_ok (b := .t0) (by rw [g1]; exact hp.ws_al) (fun p hp' => savedWs_fits.1 p hp')
    (fun p hp' => ?_) ?_
  · have := savedWs_bound p hp'
    rw [u₁.wr, hp.wr, g1]
    exact ⟨wsR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ =>
    wp_mv fun s₆ u₆ => wp_mv fun s₇ u₇ => WP.block_nil ?_
  have hm : s₇.mem = Spill.saveMem s₀.mem (ws s₀) s₁.gpr savedWs := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, g1, u₁.mem]
  have hf : Frame [slotR s₀] s₀.mem s₇.mem := by
    rw [hm]; exact Spill.saveMem_frame savedWs_bound (by omega_using [hp.ws_fit]) _ _ _
  have hs : Spill.Saved (ws s₀) s₀.gpr savedWs s₇.mem := fun p hp' => by
    rw [hm, Spill.saveMem_saved savedWs_fits _ _ _ p hp', u₁.other _ (savedWs_ne_t0 p hp')]
  have o : ∀ r, r ≠ .t0 →
      ({ s₁ with mem := Spill.saveMem s₁.mem (s₁.gpr .t0) s₁.gpr savedWs } : State).gpr r = s₀.gpr r :=
    u₁.other
  refine ⟨⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hf.sub fun r hr => ⟨wsR s₀, by simp, by simp only [List.mem_singleton] at hr; subst hr; exact slot_ws s₀⟩,
      hs, fun r hr => ?_⟩, ?_, fun msg ⟨hst, _⟩ => ?_⟩
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]; exact hp.rd
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hp.wr
  · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, o _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), o _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), o _ (by decide)]; simp
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), o _ (by decide), Nat.sub_zero]; simp [len]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), o _ (by decide)]
  · have : r ≠ .s2 ∧ r ≠ .s3 ∧ r ≠ .s4 ∧ r ≠ .s5 ∧ r ≠ .s6 ∧ r ≠ .s7 ∧ r ≠ .t0 := by
      revert r; decide
    rw [u₇.other _ this.2.2.2.2.2.1, u₆.other _ this.2.2.2.2.1, u₅.other _ this.2.2.2.1,
      u₄.other _ this.2.2.1, u₃.other _ this.2.1, u₂.other _ this.1, o _ this.2.2.2.2.2.2]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), o _ (by decide), Nat.add_zero,
      Nat.mod_eq_of_lt hp.pos_lt]
    simp [pos]
  · rw [show Absorb.D s₀ 0 = [] by simp [Absorb.D, bytesAt], List.append_nil, ← hst]
    exact Proof.Sha3.stateAt_congr fun i hi =>
      hf.bytes (R := stR s₀) (by simpa using hp.slot_st.symm) (by show 200 ≤ 2 ^ 64; decide) hi

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
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩, h3, ?_⟩
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
  · rw [g .s7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.s7]
  · exact hI.frame.trans (hf.mono (by simp))
  · exact Common.saved_st hp hI.saved hf
  · have hne : r ≠ .t1 ∧ r ≠ .t2 ∧ r ≠ .t3 ∧ r ≠ .s5 ∧ r ≠ .s4 ∧ r ≠ .s6 := by revert r; decide
    rw [g r hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2]
    exact hI.untouched r hr
  · refine stateAt_xorByte (by omega) ?_ fun i hi hij => ?_
    · rw [hm₈, writeW8_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl), BitVec.xor_comm]
    · rw [hm₈, writeW8_apply, ite_eq_right_of_eq_false _ _
        (eq_false (VG.Proof.Sha3.ne_of_lt200 hi (by omega) hij))]

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
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩, h3, ?_⟩
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
  · rw [g .s7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.s7]
  · exact hI.frame.trans (hf.mono (by simp))
  · exact Common.saved_st hp hI.saved hf
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

theorem s7_preserved : Reg.s7 ∈ preserved := by decide

/-- The permutation if the block is complete, after `n` bytes of data that
fit in it. -/
theorem full_ok {s₀ : State} (hp : Pre s₀) {c n : Nat} (hn : 0 < n)
    (hfit : (pos s₀ + c) % rt s₀ + n ≤ rt s₀) {s s₁ : State}
    (hI : Inv s₀ c s) (hC : Common s₀ (c + n) s₁)
    (h3 : s₁.gpr .s4 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + n))
    (hst : stateAt s₁.mem (st s₀) = xorAt (stateAt s.mem (st s₀)) ((pos s₀ + c) % rt s₀)
        (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) n)) :
    WP isa permuteIfFullWs s₁ (Inv s₀ (c + n)) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hlen : ∀ msg, Msg s₀ msg → (msg ++ Absorb.D s₀ c).length % rt s₀ = (pos s₀ + c) % rt s₀ :=
    fun msg ⟨_, hpm⟩ => by rw [List.length_append, bytesAt_length, hpm, Nat.mod_add_mod]
  have hrep : ∀ msg, Msg s₀ msg → Rep (rt s₀) (msg ++ Absorb.D s₀ (c + n)) =
      if (pos s₀ + c) % rt s₀ + n = rt s₀ then keccakF (stateAt s₁.mem (st s₀))
      else stateAt s₁.mem (st s₀) := fun msg hm => by
    rw [Absorb.D, bytesAt_add, ← List.append_assoc, rep_append hr₀ (by omega) _ _
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
  unfold permuteIfFullWs
  refine WP.seq (wp_sub fun s₂ u₂ => WP.block_nil ?_)
  have hC₂ : Common s₀ (c + n) s₂ :=
    { hC with rd := u₂.rd.trans hC.rd, wr := u₂.wr.trans hC.wr, sp := u₂.sp.trans hC.sp
              s2 := (u₂.other _ (by decide)).trans hC.s2, s3 := (u₂.other _ (by decide)).trans hC.s3
              s5 := (u₂.other _ (by decide)).trans hC.s5, s6 := (u₂.other _ (by decide)).trans hC.s6
              s7 := (u₂.other _ (by decide)).trans hC.s7
              frame := u₂.mem ▸ hC.frame, saved := u₂.mem ▸ hC.saved
              untouched := fun r hr => (u₂.other r (by revert r; decide)).trans (hC.untouched r hr) }
  have hz : isa.eval (.zero .t1) s₂ = some (decide ((pos s₀ + c) % rt s₀ + n = rt s₀)) := by
    show eval (.zero .t1) s₂ = _
    rw [eval_zero, u₂.gpr, h3, hC.s3, sub_beq_zero (by have := (s₀.gpr .a1).isLt; omega)]
  refine WP.ite (decide ((pos s₀ + c) % rt s₀ + n = rt s₀)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine WP.seq (wp_li (by decide) fun s₃ u₃ => WP.block_nil ?_)
    have sp₃ : s₃.sp = s₀.sp := by rw [u₃.sp, hC₂.sp]
    refine permuteAtWs_ok (st := st s₀) (w := ws s₀) (by rw [u₃.other _ (by decide), hC₂.s2])
      (by rw [u₃.other _ (by decide), hC₂.s7])
      (by rw [sp₃]; exact hp.sp_al) (by rw [sp₃]; exact hp.sp) hp.st_scr
      (by rw [sp₃]; exact hp.p_st) (by rw [sp₃]; exact hp.p_scr)
      (by
        rw [u₃.wr, hC₂.wr]
        apply Covers.of_sub
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
        · exact ⟨wsR s₀, by simp, 0, by simp, by simp⟩)
      fun s₄ rd₄ wr₄ sp₄ cs₄ f₄ e₄ => ?_
    rw [sp₃] at f₄
    have hm₃ : s₃.mem = s₂.mem := u₃.mem
    rw [hm₃] at f₄
    refine ⟨⟨hC₂.c_le, by rw [rd₄, u₃.rd, hC₂.rd], by rw [wr₄, u₃.wr, hC₂.wr], by rw [sp₄, sp₃],
      by rw [cs₄ _ (by decide), u₃.other _ (by decide), hC₂.s2],
      by rw [cs₄ _ (by decide), u₃.other _ (by decide), hC₂.s3],
      by rw [cs₄ _ (by decide), u₃.other _ (by decide), hC₂.s5],
      by rw [cs₄ _ (by decide), u₃.other _ (by decide), hC₂.s6],
      by rw [cs₄ _ s7_preserved, u₃.other _ (by decide), hC₂.s7], ?_, ?_,
      fun r hr => by rw [cs₄ _ (keep_preserved r hr), u₃.other _ (by revert r; decide),
        hC₂.untouched r hr]⟩, ?_, fun msg hm => ?_⟩
    · exact hC₂.frame.trans (f₄.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨stR s₀, by simp, fun _ h => h⟩
        · exact ⟨wsR s₀, by simp, scr_ws s₀⟩
        · exact ⟨PR s₀, by simp, fun _ h => h⟩)
    · refine hC₂.saved.frame_in savedWs_bound f₄ fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.slot_st
      · exact slot_scr s₀
      · exact hp.slot_p
    · rw [cs₄ _ (by decide), u₃.gpr, hpc, ite_eq_left_of_eq_true _ _ (eq_true hb)]
    · rw [e₄, hm₃, u₂.mem, hrep msg hm, ite_eq_left_of_eq_true _ _ (eq_true hb)]
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.block_nil { hC₂ with s4 := ?_, repr := fun msg hm => ?_ }
    · rw [u₂.other _ (by decide), h3, hpc, ite_eq_right_of_eq_false _ _ (eq_false hb)]
    · rw [u₂.mem, hrep msg hm, ite_eq_right_of_eq_false _ _ (eq_false hb)]

theorem body_ok {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < len s₀) {s : State}
    (hI : Inv s₀ c s) :
    WP isa absorbWsBody s fun s' => ∃ c', c < c' ∧ c' ≤ len s₀ ∧ Inv s₀ c' s' := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have h8 := rate_mod8 hp.rate
  have hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  have hl := len_lt s₀
  unfold absorbWsBody
  refine WP.seq (WP.mono (laneCheck_ok hI.s2 hI.s4 hI.s6 (by omega) (by omega))
    fun s₇ ⟨oth, ht2, m₇, rd₇, wr₇, sp₇, hz, hd⟩ => ?_)
  have o : ∀ r, r ≠ .t1 ∧ r ≠ .t2 ∧ r ≠ .t3 ∧ r ≠ .t4 → s₇.gpr r = s.gpr r :=
    fun r h => oth r h.1 h.2.1 h.2.2.1 h.2.2.2
  have hI₇ : Inv s₀ c s₇ :=
    { c_le := hI.c_le, rd := rd₇.trans hI.rd, wr := wr₇.trans hI.wr, sp := sp₇.trans hI.sp
      s2 := (o _ (by decide)).trans hI.s2, s3 := (o _ (by decide)).trans hI.s3
      s5 := (o _ (by decide)).trans hI.s5, s6 := (o _ (by decide)).trans hI.s6
      s7 := (o _ (by decide)).trans hI.s7
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

theorem preserved_split : ∀ r ∈ preserved, r ∈ savedWs.map Prod.fst ∨ r ∈ untouched := by decide

theorem restoreWs_eq : restoreWs = mov .t0 .s7 :: Spill.restoreCode .t0 savedWs := rfl

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa absorbWs s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha3.absorbWsRISCV64.post s₀ s' := by
  have hl := len_lt s₀
  have ⟨hr₀, _⟩ := hp.rt_pos
  unfold absorbWs
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
  · rw [restoreWs_eq]
    refine wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => ?_
    have g4 : s₄.gpr .t0 = ws s₀ := by rw [u₄.gpr, u₃.other _ (by decide), hI₂.s7]
    have m₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
    refine WP.mono (Spill.restore_wp (B := ws s₀) hp.ws_al g4
      (fun p hp' => savedWs_fits.1 p hp') (by decide) (fun p hp' => ?_)
      (by rw [m₄]; exact hI₂.saved)) fun s' hR => ?_
    · have := savedWs_bound p hp'
      rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, hI₂.rd, hI₂.wr]
      exact ⟨wsR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
    have a0 : s'.gpr .a0 = s₂.gpr .s4 := by
      rw [hR.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
    refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun msg hRp hpm => ?_, ?_⟩
    · rcases preserved_split r hr with h | h
      · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp h
        exact hR.gpr p hp'
      · have hne : r ∉ savedWs.map Prod.fst ∧ r ≠ .t0 ∧ r ≠ .a0 := by revert r; decide
        rw [hR.other r hne.1, u₄.other _ hne.2.1, u₃.other _ hne.2.2]
        exact hI₂.untouched r h
    · rw [hR.sp, u₄.sp, u₃.sp, hI₂.sp]
    · exact hR.gpr (.ra, 512) (by decide)
    · rw [Proof.Sha3.repr_iff, hR.mem, m₄]
      exact hI₂.repr msg ⟨hRp, hpm⟩
    · rw [a0, hI₂.s4, toNat_ofNat_lt (by have := Nat.mod_lt (pos s₀ + len s₀) hr₀; omega)]

end VG.Proof.Sha3.RISCV64.Stream.AbsorbWs
