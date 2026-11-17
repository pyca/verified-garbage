module

public import VerifiedGarbage.Proof.Sha3.RISCV64.Contract
public import VerifiedGarbage.Impl.Sha3.RISCV64.Stream
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.AbsorbWs
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sha3.Lanes
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RISCV64.Wp
public import VerifiedGarbage.Spec.Sha3.Contract
import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sha3.RISCV64.Contract
meta import VerifiedGarbage.Impl.Sha3.RISCV64.Stream
meta import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Sha3.Contract
meta import VerifiedGarbage.Proof.Sha3.Contract

/-! ### `Sha3.RISCV64.Stream.Pad`, which only this module used -/

section

/-!
# The SHA-3 sponge on RISC-V: `pad`

As on PPC64LE (`Proof/Sha3/PPC64LE/Stream/Pad.lean`), in a frame on the
stack (`WP.allocKept`) that holds the permutation's scratch space and the saved
return address.
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64.Stream.Pad

open VG VG.RISCV64 VG.RISCV64.Wp VG.Impl.Sha3.RISCV64.Stream
open VG.Spec.Sha3 (stateAt keccakF absorb rates Repr)
open VG.Proof.Sha3 (xorByte Rep stateAt_xorByte absorb_pad)

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .a0
abbrev stR : Region := ⟨st s₀, 200⟩
/-- The stack below the stack pointer that the function and the permutation use. -/
abbrev K : Addr := s₀.sp - BitVec.ofNat 64 1136
/-- The frame's base. -/
abbrev B : Addr := s₀.sp - BitVec.ofNat 64 528

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀]
  al : s₀.sp.toNat % 16 = 0
  sp : 1136 ≤ s₀.sp.toNat
  stk : Region.Disjoint ⟨K s₀, 1136⟩ (stR s₀)
  rate : (s₀.gpr .a1).toNat ∈ rates
  pos_lt : (s₀.gpr .a2).toNat < (s₀.gpr .a1).toNat

theorem pre_of {s₀ : State} (h : Proof.Sha3.padRISCV64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem B_eq : B s₀ = K s₀ + BitVec.ofNat 64 608 := by
  have := hp.sp
  simp only [B, K]; bv_omega

theorem B_al : (B s₀).toNat % 16 = 0 := by
  have := hp.sp; have := hp.al
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_arith), BitVec.toNat_ofNat]
  omega_using [this]

theorem B_toNat : 608 ≤ (B s₀).toNat := by
  have := hp.sp
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [this]), BitVec.toNat_ofNat]
  omega_using [this]

/-- A part of the stack the function and the permutation use is disjoint from the state. -/
theorem stk_sub {d n : Nat} (h : d + n ≤ 1136) :
    Region.Disjoint ⟨K s₀ + BitVec.ofNat 64 d, n⟩ (stR s₀) :=
  hp.stk.sub_left (Offset.sub_base _ h)

theorem below_eq : B s₀ - 608 = K s₀ := by
  rw [hp.B_eq]; exact BitVec.add_sub_cancel _ _

end Pre

theorem x80 : (BitVec.ofNat 64 0x80).setWidth 8 = (0x80 : BitVec 8) := by decide

theorem xor_lo (x y : BitVec 64) : (x ^^^ y).setWidth 8 = x.setWidth 8 ^^^ y.setWidth 8 := by
  ext i _; simp

theorem lbu_lo (b : Byte) : (b.setWidth 64).setWidth 8 = b := by
  ext i hi; simp

theorem keep_ne : ∀ r ∈ preserved, r ≠ .t0 ∧ r ≠ .t1 ∧ r ≠ .t2 ∧ r ≠ .a1 := by decide

/-- `pad`: the callee-saved registers, the stack pointer and the return
address are kept. -/
theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa Impl.Sha3.RISCV64.Stream.pad s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha3.padRISCV64.post s₀ s' := by
  obtain hr : 72 ≤ (s₀.gpr .a1).toNat ∧ (s₀.gpr .a1).toNat ≤ 168 := Proof.Sha3.rate_bounds hp.rate
  have hpl := hp.pos_lt
  have hB := hp.B_eq
  unfold Impl.Sha3.RISCV64.Stream.pad padBytes
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by have := hp.sp; omega_using [this]) ?_
  -- In the frame.
  let s := allocd 528 s₀
  have hsp : s.sp = B s₀ := rfl
  obtain hwr : s.wr = [⟨B s₀, 528⟩, stR s₀] := by simp only [s, allocd, hp.wr]
  obtain hin : ∀ j < 200, InRegions s.wr (st s₀ + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hwr]; exact ⟨stR s₀, by simp, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩
  obtain hin' : ∀ j < 200, InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [show s.rd = [] from hp.rd]; exact hin j hj
  obtain hra : InRegions s.wr (B s₀ + BitVec.ofNat 64 512) 8 := by
    rw [hwr]; exact ⟨_, List.mem_cons_self .., Offset.contains_base _ (by omega_using []) (by omega_using [])⟩
  refine WP.seq ?_
  unfold padMain
  refine wp_addSp (by decide) fun s₁ u₁ => ?_
  obtain h₁ : s₁.gpr .t0 = B s₀ := by rw [u₁.gpr, hsp]; exact BitVec.add_zero _
  refine wp_sd (by decide) (a := B s₀ + BitVec.ofNat 64 512) (by rw [h₁])
    (al8 hp.B_al (by decide) (by decide)) (by rw [u₁.wr]; exact hra) fun s₂ g₂ => ?_
  obtain k₂ : ∀ r, r ≠ .t0 → s₂.gpr r = s₀.gpr r := fun r h => by rw [g₂.gpr, u₁.other _ h]; rfl
  refine wp_add fun s₃ u₃ => ?_
  obtain e₃ : s₃.gpr .t1 + BitVec.ofNat 64 0 = st s₀ + BitVec.ofNat 64 ((s₀.gpr .a2).toNat) := by
    rw [u₃.gpr, k₂ _ (by decide), k₂ _ (by decide)]; simp
  refine wp_lbu (a := st s₀ + BitVec.ofNat 64 ((s₀.gpr .a2).toNat)) (by decide) e₃
    (by rw [u₃.rd, u₃.wr, g₂.rd, g₂.wr, u₁.rd, u₁.wr]; exact hin' _ (by omega_using [hr, hpl])) fun s₄ u₄ =>
    wp_xor fun s₅ u₅ => wp_sb (a := st s₀ + BitVec.ofNat 64 ((s₀.gpr .a2).toNat)) (by decide)
      (by rw [u₅.other _ (by decide), u₄.other _ (by decide)]; exact e₃)
      (by rw [u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr]; exact hin _ (by omega_using [hr, hpl])) fun s₆ g₆ => ?_
  obtain k₆ : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → s₆.gpr r = s₀.gpr r := fun r h0 h1 h2 => by
    rw [g₆.gpr, u₅.other _ h2, u₄.other _ h2, u₃.other _ h1, k₂ _ h0]
  refine wp_add fun s₇ u₇ => wp_subi (imm := 1) (by decide) fun s₈ u₈ => ?_
  obtain e₈ : s₈.gpr .t1 + BitVec.ofNat 64 0 =
      st s₀ + BitVec.ofNat 64 ((s₀.gpr .a1).toNat - 1) := by
    rw [u₈.gpr, u₇.gpr, k₆ _ (by decide) (by decide) (by decide),
      k₆ _ (by decide) (by decide) (by decide), BitVec.add_zero]
    exact Offset.add_sub_one64 _ _ (by omega_using [hr])
  refine wp_lbu (a := st s₀ + BitVec.ofNat 64 ((s₀.gpr .a1).toNat - 1)) (by decide) e₈
    (by rw [u₈.rd, u₈.wr, u₇.rd, u₇.wr, g₆.rd, g₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr,
          g₂.rd, g₂.wr, u₁.rd, u₁.wr]
        exact hin' _ (by omega_using [hr]))
    fun s₉ u₉ => wp_xori (imm := 0x80) (by decide) fun s₁₀ u₁₀ =>
    wp_sb (a := st s₀ + BitVec.ofNat 64 ((s₀.gpr .a1).toNat - 1)) (by decide)
      (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide)]; exact e₈)
      (by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, g₆.wr, u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr]
          exact hin _ (by omega_using [hr]))
    fun s₁₁ g₁₁ => wp_addSp (by decide) fun s₁₂ u₁₂ => WP.block_nil ?_
  -- The two bytes written.
  obtain hb₁ : s₆.mem = s₂.mem.writeW (st s₀ + BitVec.ofNat 64 ((s₀.gpr .a2).toNat))
      (s₂.mem (st s₀ + BitVec.ofNat 64 ((s₀.gpr .a2).toNat)) ^^^ (s₀.gpr .a3).setWidth 8) := by
    rw [g₆.mem, u₅.gpr, u₄.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      k₂ _ (by decide), u₅.mem, u₄.mem, u₃.mem, xor_lo, lbu_lo]
  obtain hb₂ : s₁₁.mem = s₆.mem.writeW (st s₀ + BitVec.ofNat 64 ((s₀.gpr .a1).toNat - 1))
      (s₆.mem (st s₀ + BitVec.ofNat 64 ((s₀.gpr .a1).toNat - 1)) ^^^ 0x80) := by
    rw [g₁₁.mem, u₁₀.gpr, u₉.gpr, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, xor_lo, lbu_lo, x80]
  obtain hraR : Region.Disjoint ⟨B s₀ + BitVec.ofNat 64 512, 8⟩ (stR s₀) := by
    have := hp.stk_sub (d := 1120) (n := 8) (by omega_using [])
    rwa [show K s₀ + BitVec.ofNat 64 1120 = B s₀ + BitVec.ofNat 64 512 by
      rw [hB, BitVec.add_assoc, BitVec.ofNat_add_ofNat]] at this
  obtain f₂ : Frame [⟨B s₀ + BitVec.ofNat 64 512, 8⟩] s₀.mem s₂.mem := by
    rw [g₂.mem, u₁.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain hst₂ : ∀ i < 200, s₂.mem (st s₀ + BitVec.ofNat 64 i) = s₀.mem (st s₀ + BitVec.ofNat 64 i) :=
    fun i hi => f₂.bytes (R := stR s₀) (by simpa using hraR.symm) (by show 200 ≤ 2 ^ 64; decide) hi
  obtain k₁₂ : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → r ≠ .a1 → s₁₂.gpr r = s₀.gpr r :=
    fun r h0 h1 h2 ha => by
      rw [u₁₂.other _ ha, g₁₁.gpr, u₁₀.other _ h2, u₉.other _ h2, u₈.other _ h1, u₇.other _ h1,
        k₆ _ h0 h1 h2]
  obtain sp₁₂ : s₁₂.sp = B s₀ := by
    rw [u₁₂.sp, g₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, g₆.sp, u₅.sp, u₄.sp, u₃.sp, g₂.sp, u₁.sp, hsp]
  obtain wr₁₂ : s₁₂.wr = [⟨B s₀, 528⟩, stR s₀] := by
    rw [u₁₂.wr, g₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, g₆.wr, u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr, hwr]
  obtain rd₁₂ : s₁₂.rd = [] := by
    rw [u₁₂.rd, g₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, g₆.rd, u₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd]
    exact hp.rd
  obtain hS : stateAt s₁₂.mem (st s₀) =
      xorByte (xorByte (stateAt s₀.mem (st s₀)) ((s₀.gpr .a2).toNat) ((s₀.gpr .a3).setWidth 8))
        ((s₀.gpr .a1).toNat - 1) 0x80 := by
    obtain e₀ : stateAt s₂.mem (st s₀) = stateAt s₀.mem (st s₀) :=
      Proof.Sha3.stateAt_congr fun i hi => hst₂ i hi
    rw [← e₀, ← stateAt_xorByte (m := s₂.mem) (m' := s₆.mem) (by omega_using [hr, hpl])
      (by simp only [hb₁, Proof.Sha3.writeW8_apply, ↓reduceIte])
      (fun i hi hne => by
        simp only [hb₁, Proof.Sha3.writeW8_apply, Proof.Sha3.ne_of_lt200 hi (by omega_using [hr, hpl]) hne, ite_false])]
    rw [show s₁₂.mem = s₁₁.mem from u₁₂.mem]
    exact stateAt_xorByte (by omega_using [hr]) (by simp only [hb₂, Proof.Sha3.writeW8_apply, ↓reduceIte])
      (fun i hi hne => by
        simp only [hb₂, Proof.Sha3.writeW8_apply, Proof.Sha3.ne_of_lt200 hi (by omega_using [hr]) hne, ite_false])
  -- The slot of the return address, which the bytes of the state do not touch.
  obtain hraS : s₁₂.mem.readW (B s₀ + BitVec.ofNat 64 512) 64 = s₀.gpr .ra := by
    obtain f : Frame [stR s₀] s₂.mem s₁₂.mem := by
      rw [u₁₂.mem, hb₂, hb₁]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (by omega_using [hr, hpl]) (by omega_using []))).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (by omega_using [hr]) (by omega_using []))
    rw [f.readW (Region.contains_self _ _) (by simpa using hraR) (by decide), g₂.mem,
      Mem.readW_writeW_self64, u₁.other _ (by decide)]
    rfl
  obtain hstk : Region.Disjoint ⟨B s₀ - 608, 608⟩ (stR s₀) := by
    rw [hp.below_eq]; simpa using hp.stk_sub (d := 0) (n := 608) (by omega_using [])
  obtain hscr : Region.Disjoint (stR s₀) ⟨B s₀, 512⟩ := by
    have := hp.stk_sub (d := 608) (n := 512) (by omega_using [])
    rw [← hB] at this; exact this.symm
  refine WP.seq (call_ok (st := st s₀)
    (by rw [k₁₂ _ (by decide) (by decide) (by decide) (by decide)])
    (by rw [u₁₂.gpr, sp₁₂, g₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, g₆.sp, u₅.sp, u₄.sp, u₃.sp, g₂.sp,
      u₁.sp, hsp]; exact BitVec.add_zero _)
    (by rw [sp₁₂]; exact hp.B_al) (by rw [sp₁₂]; exact hp.B_toNat) (by rw [sp₁₂]; exact hscr)
    (by rw [sp₁₂]; exact hstk)
    (by
      rw [wr₁₂, sp₁₂]
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨B s₀, 528⟩, by simp, 0, by simp, by simp⟩)
    fun s' rd' wr' sp' cs' f' e' => ?_)
  -- Restore the return address.
  refine wp_addSp (by decide) fun s₁₃ u₁₃ => ?_
  obtain hf' : s'.mem.readW (B s₀ + BitVec.ofNat 64 512) 64 = s₀.gpr .ra := by
    rw [sp₁₂] at f'
    rw [f'.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide), hraS]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hraR
    · exact Offset.disjoint_base _ (by omega_using []) (by omega_using [])
    · rw [hp.below_eq, hB, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact Offset.disjoint_base _ (by omega_using []) (by omega_using [])
  refine wp_ld (by decide) (a := B s₀ + BitVec.ofNat 64 512)
    (by rw [u₁₃.gpr, sp', sp₁₂, show B s₀ + BitVec.ofNat 64 0 = B s₀ from BitVec.add_zero _])
    (al8 hp.B_al (by decide) (by decide))
    (by rw [u₁₃.rd, u₁₃.wr, rd', wr', rd₁₂, wr₁₂]
        exact ⟨_, List.mem_cons_self .., Offset.contains_base _ (by omega_using []) (by omega_using [])⟩)
    fun s₁₄ u₁₄ => WP.block_nil ?_
  intro mL _ fl
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun msg hR hm => ?_⟩
  · have ne := keep_ne r hr
    obtain hra : r ≠ .ra := by revert r; decide
    show s₁₄.gpr r = _
    rw [u₁₄.other _ hra, u₁₃.other _ ne.1, cs' r hr, k₁₂ r ne.1 ne.2.1 ne.2.2.1 ne.2.2.2]
  · show s₁₄.sp + BitVec.ofNat 64 528 = s₀.sp
    rw [u₁₄.sp, u₁₃.sp, sp', sp₁₂, BitVec.sub_add_cancel]
  · show s₁₄.gpr .ra = _
    rw [u₁₄.gpr, u₁₃.mem, hf']
  · -- The `free` loses the frame's bytes, which lie apart from the state.
    show stateAt mL (st s₀) = _
    rw [Proof.Sha3.stateAt_congr (m := s₁₄.mem) fun i hi =>
        lost_byte fl (R := stR s₀) (hp.stk.symm.sub_right (Offset.sub_below _ (by decide) (by decide))) hi,
      u₁₄.mem, u₁₃.mem, e', hS, absorb_pad (by omega_using [hr]) (by omega_using [hr]), ← hm,
      show Rep ((s₀.gpr .a1).toNat) msg = stateAt s₀.mem (st s₀) from hR.symm]

end VG.Proof.Sha3.RISCV64.Stream.Pad

end

end

/-! ### `Sha3.RISCV64.Stream.Squeeze`, which only this module used -/

section

/-!
# The SHA-3 sponge on RISC-V: `squeeze`

The structure of the PPC64LE proof (`Proof/Sha3/PPC64LE/Stream/Squeeze.lean`),
a lane (`store_lane`) or a byte (`store_ok`) at a time, in the frame of
`Stream/Common.lean`.
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64.Stream.Squeeze

open VG VG.RISCV64 VG.RISCV64.Wp VG.Impl.Sha3.RISCV64.Stream
open VG.Proof.Sha3.RISCV64 VG.Proof.Sha3.RISCV64.Stream
open VG.Spec.Sha3 (stateAt keccakF bytesAt rates)
open VG.Proof.Sha3 (byteOf byteOf_stateAt iterF iterF_succ length_squeezeFrom squeezeFrom_getElem
  squeezeFrom_iterF ofNat_beq_zero sub_beq_zero sub_ofNat writeW8_self writeW8_other div_mod_eq
  toNat_ofNat_lt writeW64_byte)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev stp : Addr := s₀.gpr .a0
abbrev rate : Nat := (s₀.gpr .a1).toNat
abbrev pos₀ : Nat := (s₀.gpr .a2).toNat
abbrev outp : Addr := s₀.gpr .a3
abbrev outn : Nat := (s₀.gpr .a4).toNat
abbrev SR : Region := ⟨stp s₀, 200⟩
abbrev OR : Region := ⟨outp s₀, outn s₀⟩
/-- The initial state. -/
abbrev S₀ : Spec.Sha3.State := stateAt s₀.mem (stp s₀)

end

structure SPre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [SR s₀, OR s₀]
  st_o : (SR s₀).Disjoint (OR s₀)
  stk : Stk s₀
  k_st : (KR s₀).Disjoint (SR s₀)
  k_o : (KR s₀).Disjoint (OR s₀)
  rate_mem : rate s₀ ∈ rates
  pos_le : pos₀ s₀ ≤ rate s₀

theorem pre_of {s₀ : State} (h : Proof.Sha3.squeezeRISCV64.pre s₀) : SPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, ⟨h4, h5⟩, h6, h7, h8, h9⟩

theorem SPre.rate_pos {s₀ : State} (hp : SPre s₀) : 0 < rate s₀ ∧ rate s₀ ≤ 200 := by
  have := Proof.Sha3.rate_bounds hp.rate_mem
  omega_using [this]

theorem outn_lt (s₀ : State) : outn s₀ < 2 ^ 64 := (s₀.gpr .a4).isLt

/-- The callee-saved registers our code never writes. -/
abbrev untouched : List Reg := [.s0, .s1, .s7, .s8, .s9, .s10, .s11]

/-! ## The loop invariant -/

/-- After `i` bytes of output, `k` permutations and `pos` bytes of the
current block: `pos₀ + i = rate * k + pos`. -/
structure Inv (s₀ : State) (i k pos : Nat) (s : State) : Prop where
  i_le : i ≤ outn s₀
  hi : pos₀ s₀ + i = rate s₀ * k + pos
  pos_le : pos ≤ rate s₀
  rd : s.rd = []
  wr : s.wr = [BR s₀, SR s₀, OR s₀]
  s2 : s.gpr .s2 = stp s₀
  s3 : s.gpr .s3 = s₀.gpr .a1
  s4 : s.gpr .s4 = BitVec.ofNat 64 pos
  s5 : s.gpr .s5 = outp s₀ + BitVec.ofNat 64 i
  s6 : s.gpr .s6 = BitVec.ofNat 64 (outn s₀ - i)
  sp : s.sp = B s₀
  frame : Frame [SR s₀, OR s₀, KR s₀] s₀.mem s.mem
  saved : Saved (B s₀) s₀.gpr s.mem
  untouched : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  state : stateAt s.mem (stp s₀) = iterF k (S₀ s₀)
  out : ∀ j < i, s.mem (outp s₀ + BitVec.ofNat 64 j) =
    byteOf (iterF ((pos₀ s₀ + j) / rate s₀) (S₀ s₀)) ((pos₀ s₀ + j) % rate s₀)

/-- The registers of the invariant, besides `untouched`. -/
abbrev keep : List Reg := [.s2, .s3, .s4, .s5, .s6] ++ untouched

theorem Inv.congr {s₀ : State} {i k pos : Nat} {s s' : State} (h : Inv s₀ i k pos s)
    (hg : ∀ r ∈ keep, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Inv s₀ i k pos s' where
  i_le := h.i_le
  hi := h.hi
  pos_le := h.pos_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  s2 := by rw [hg _ (by decide)]; exact h.s2
  s3 := by rw [hg _ (by decide)]; exact h.s3
  s4 := by rw [hg _ (by decide)]; exact h.s4
  s5 := by rw [hg _ (by decide)]; exact h.s5
  s6 := by rw [hg _ (by decide)]; exact h.s6
  sp := hsp.trans h.sp
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved
  untouched := fun r hr => (hg r (List.mem_append_right _ hr)).trans (h.untouched r hr)
  state := by rw [hm]; exact h.state
  out := by rw [hm]; exact h.out

theorem prologue_ok {s₀ : State} (hp : SPre s₀) :
    WP isa (.block setup) (allocd 560 s₀) (Inv s₀ 0 0 (pos₀ s₀)) := by
  have hk := hp.stk
  unfold setup
  refine save_ok (s := allocd 560 s₀) hk.B_al (fun d hd₁ hd₂ => ⟨BR s₀, List.mem_cons_self ..,
      Offset.contains_base _ (by omega_using [hd₂]) (by omega_using [hd₂])⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ sv₁ f₁ => ?_
  refine wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ =>
    wp_mv fun s₆ u₆ => WP.block_nil ?_
  obtain hm : s₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  obtain hsub : Region.Sub ⟨(allocd 560 s₀).sp + BitVec.ofNat 64 512, 48⟩ (KR s₀) := by
    rw [show (allocd 560 s₀).sp = B s₀ from rfl, hk.B_off]; exact sub_K s₀ (by omega_using [])
  obtain g : ∀ r, r ≠ .t0 → s₁.gpr r = s₀.gpr r := fun r h => g₁ r h
  obtain hf : Frame [SR s₀, OR s₀, KR s₀] s₀.mem s₁.mem := f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨KR s₀, by simp, hsub⟩
  refine ⟨Nat.zero_le _, by simp, hp.pos_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [hm]; exact hf, by rw [hm]; exact sv₁, fun r hr => ?_, ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]; exact hp.rd
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]; simp only [allocd, hp.wr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, g _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), g _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), g _ (by decide)]; simp
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g _ (by decide)]; simp
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g _ (by decide)]; simp
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]; rfl
  · have : r ≠ .s2 ∧ r ≠ .s3 ∧ r ≠ .s4 ∧ r ≠ .s5 ∧ r ≠ .s6 ∧ r ≠ .t0 := by revert r; decide
    rw [u₆.other _ this.2.2.2.2.1, u₅.other _ this.2.2.2.1, u₄.other _ this.2.2.1,
      u₃.other _ this.2.1, u₂.other _ this.1, g _ this.2.2.2.2.2]
  · rw [hm]
    exact Proof.Sha3.stateAt_congr fun j hj => f₁.bytes (R := SR s₀)
      (by simpa using (hp.k_st.sub_left hsub).symm) (by show 200 ≤ 2 ^ 64; decide) hj

/-! ## One iteration -/

theorem keep_preserved : ∀ r ∈ untouched, r ∈ preserved := by decide

theorem permute_ok {s₀ : State} (hp : SPre s₀) {i k : Nat} {s : State} (hI : Inv s₀ i k (rate s₀) s) :
    WP isa (.seq (.block [.li .s4 0]) permuteAt) s (Inv s₀ i (k + 1) 0) := by
  have hk := hp.stk
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => WP.block_nil ?_)
  obtain sp₁ : s₁.sp = B s₀ := by rw [u₁.sp, hI.sp]
  refine permuteAt_ok (st := stp s₀) (by rw [u₁.other _ (by decide), hI.s2])
    (by rw [sp₁]; exact hk.B_al) (by rw [sp₁]; exact hk.B_608)
    (by rw [sp₁]; exact (hp.k_st.sub_left hk.scr_sub).symm)
    (by rw [sp₁]; exact hp.k_st.sub_left hk.below_sub) ?_
    fun s' rd' wr' sp' cs' hf hst => ?_
  · rw [u₁.wr, hI.wr, sp₁]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨SR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨BR s₀, by simp, 0, by simp, by simp⟩
  rw [sp₁, u₁.mem] at hf
  obtain hd : ∀ r ∈ [(⟨stp s₀, 200⟩ : Region), ⟨B s₀, 512⟩, ⟨B s₀ - 608, 608⟩], (OR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.st_o.symm
    · exact (hp.k_o.sub_left hk.scr_sub).symm
    · exact (hp.k_o.sub_left hk.below_sub).symm
  refine ⟨hI.i_le, by rw [hI.hi, Nat.mul_succ]; rfl, Nat.zero_le _, rd'.trans (u₁.rd.trans hI.rd),
    wr'.trans (u₁.wr.trans hI.wr), ?_, ?_, ?_, ?_, ?_, by rw [sp', sp₁], ?_, ?_, (fun r hr => by
      rw [cs' r (keep_preserved r hr), u₁.other r (by revert r; decide)]
      exact hI.untouched r hr), ?_, fun j hj => ?_⟩
  · rw [cs' _ (by decide), u₁.other _ (by decide), hI.s2]
  · rw [cs' _ (by decide), u₁.other _ (by decide), hI.s3]
  · rw [cs' _ (by decide), u₁.gpr]
  · rw [cs' _ (by decide), u₁.other _ (by decide), hI.s5]
  · rw [cs' _ (by decide), u₁.other _ (by decide), hI.s6]
  · exact hI.frame.trans (hf.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨SR s₀, by simp, fun _ h => h⟩
      · exact ⟨KR s₀, by simp, hk.scr_sub⟩
      · exact ⟨KR s₀, by simp, hk.below_sub⟩)
  · refine hI.saved.frame (fun d h₁ h₂ r hr => ?_) hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.k_st.sub_left (hk.slot_sub h₁ h₂)
    · exact slot_scr s₀ h₁ h₂
    · exact hk.slot_below h₁ h₂
  · rw [hst, u₁.mem, hI.state, iterF_succ]
  · refine Eq.trans (hf.bytes (R := OR s₀) hd (Nat.le_of_lt (outn_lt s₀))
      (by have := hI.i_le; omega_using [hj, this] : j < outn s₀)) ?_
    exact hI.out j hj

theorem store_ok {s₀ : State} (hp : SPre s₀) {i k pos : Nat} {s : State} (hI : Inv s₀ i k pos s)
    (hlt : pos < rate s₀) (hi : i < outn s₀) :
    WP isa (.block squeezeByte) s (Inv s₀ (i + 1) k (pos + 1)) := by
  have ⟨hr0, hr200⟩ := hp.rate_pos
  obtain hn := outn_lt s₀
  refine wp_add fun s₁ u₁ => ?_
  refine wp_lbu (a := stp s₀ + BitVec.ofNat 64 pos) (by decide) (by rw [u₁.gpr, hI.s2, hI.s4]; simp)
    ⟨SR s₀, by simp [u₁.rd, u₁.wr, hI.rd, hI.wr], Offset.contains_base _ (by omega_using [hlt, hr200]) (by omega_using [hlt, hr200])⟩
    fun s₂ u₂ => ?_
  refine wp_sb (a := outp s₀ + BitVec.ofNat 64 i) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hI.s5]; simp)
    (by rw [u₂.wr, u₁.wr, hI.wr]; exact ⟨OR s₀, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hn])⟩)
    fun s₃ g₃ => ?_
  refine wp_addi (by decide) fun s₄ u₄ => wp_addi (by decide) fun s₅ u₅ =>
    wp_subi (imm := 1) (by decide) fun s₆ u₆ => WP.block_nil ?_
  obtain g : ∀ r, r ≠ .t2 → r ≠ .t1 → r ≠ .s5 → r ≠ .s4 → r ≠ .s6 → s₆.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₆.other r h5, u₅.other r h4, u₄.other r h3, g₃.gpr, u₂.other r h2, u₁.other r h1]
  obtain hb : s.mem (stp s₀ + BitVec.ofNat 64 pos) = byteOf (iterF k (S₀ s₀)) pos := by
    rw [← hI.state, byteOf_stateAt _ _ (by omega_using [hlt, hr200])]
  obtain hm : s₆.mem = s.mem.writeW (outp s₀ + BitVec.ofNat 64 i) (byteOf (iterF k (S₀ s₀)) pos) := by
    rw [u₆.mem, u₅.mem, u₄.mem, g₃.mem, u₂.gpr, u₂.mem, u₁.mem,
      BitVec.setWidth_setWidth_of_le _ (by omega_using []), BitVec.setWidth_eq, hb]
  obtain hfw : Frame [OR s₀] s.mem s₆.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hn]))
  refine ⟨by omega_using [hi], by have := hI.hi; omega_using [this], by omega_using [hlt], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hI.frame.trans (hfw.mono (by simp)), ?_, (fun r hr => by
      have : r ≠ .t2 ∧ r ≠ .t1 ∧ r ≠ .s5 ∧ r ≠ .s4 ∧ r ≠ .s6 := by revert r; decide
      rw [g r this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2]
      exact hI.untouched r hr), ?_, fun j hj => ?_⟩
  · rw [u₆.rd, u₅.rd, u₄.rd, g₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, g₃.wr, u₂.wr, u₁.wr, hI.wr]
  · rw [g .s2 (by decide) (by decide) (by decide) (by decide) (by decide), hI.s2]
  · rw [g .s3 (by decide) (by decide) (by decide) (by decide) (by decide), hI.s3]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hI.s4, ← BitVec.ofNat_add]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hI.s5, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hI.s6, sub_ofNat (by omega_using [hi]), Nat.sub_sub]
  · rw [u₆.sp, u₅.sp, u₄.sp, g₃.sp, u₂.sp, u₁.sp, hI.sp]
  · exact hI.saved.frame (fun d h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.k_o.sub_left (hp.stk.slot_sub h₁ h₂)) hfw
  · rw [Proof.Sha3.stateAt_congr fun j hj => hfw.bytes (R := SR s₀) (by simpa using hp.st_o)
      (by show 200 ≤ 2 ^ 64; decide) hj]
    exact hI.state
  · rw [hm]
    by_cases e : j = i
    · subst e
      obtain ⟨d, m⟩ := div_mod_eq (k := k) hr0 hlt
      rw [writeW8_self, hI.hi, d, m]
    · rw [writeW8_other _ _ (Offset.add_ofNat_ne _ (by omega_using [hi, hn, hj]) (by omega_using [hi, hn]) e)]
      exact hI.out j (by omega_using [hj, e])

theorem rate_mod8 {r : Nat} (h : r ∈ rates) : r % 8 = 0 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- A lane of the state, at an aligned position, to aligned output. -/
theorem store_lane {s₀ : State} (hp : SPre s₀) {i k pos : Nat} {s : State} (hI : Inv s₀ i k pos s)
    (h8 : pos % 8 = 0) (hlt : pos < rate s₀) (hi : i + 8 ≤ outn s₀)
    (ht2 : s.gpr .t2 = stp s₀ + BitVec.ofNat 64 pos)
    (hal : (stp s₀ + BitVec.ofNat 64 pos).toNat % 8 = 0)
    {al : Bool} (hoal : al = true → (outp s₀ + BitVec.ofNat 64 i).toNat % 8 = 0) :
    WP isa (.block (squeezeLane al)) s (Inv s₀ (i + 8) k (pos + 8)) := by
  have ⟨hr0, hr200⟩ := hp.rate_pos
  obtain hn := outn_lt s₀
  obtain hr8 := rate_mod8 hp.rate_mem
  obtain hfit : pos + 8 ≤ rate s₀ := by omega_using [h8, hlt, hr8]
  unfold squeezeLane
  rw [List.singleton_append]
  refine wp_ld (t := .t1) (a := stp s₀ + BitVec.ofNat 64 pos) (by decide) (by rw [ht2]; simp) hal
    ⟨SR s₀, by simp [hI.rd, hI.wr], Offset.contains_base _ (by omega_using [h8, hlt, hr200]) (by omega_using [hlt, hr200])⟩ fun s₁ u₁ => ?_
  refine storeData_ok (a := outp s₀ + BitVec.ofNat 64 i)
    (by rw [u₁.other _ (by decide), hI.s5]) hoal
    (by rw [u₁.wr, hI.wr]; exact ⟨OR s₀, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hn])⟩)
    fun s₂ g₂ m₂ rd₂ wr₂ sp₂ => ?_
  refine wp_addi (by decide) fun s₃ u₃ => wp_addi (by decide) fun s₄ u₄ =>
    wp_subi (imm := 8) (by decide) fun s₅ u₅ => WP.block_nil ?_
  obtain g : ∀ r, r ≠ .t1 → r ≠ .s5 → r ≠ .s4 → r ≠ .s6 → r ≠ .t3 → r ≠ .t4 → s₅.gpr r = s.gpr r :=
    fun r h1 h3 h4 h5 h6 h7 => by
      rw [u₅.other r h5, u₄.other r h4, u₃.other r h3, g₂ r h6 h7, u₁.other r h1]
  obtain hm : s₅.mem = s.mem.writeW (outp s₀ + BitVec.ofNat 64 i)
      (s.mem.readW (stp s₀ + BitVec.ofNat 64 pos) 64) := by
    rw [u₅.mem, u₄.mem, u₃.mem, m₂, u₁.gpr, u₁.mem]
  obtain hfw : Frame [OR s₀] s.mem s₅.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hn]))
  refine ⟨by omega_using [hi], by have := hI.hi; omega_using [this], by omega_using [h8, hlt, hr8], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hI.frame.trans (hfw.mono (by simp)), ?_, (fun r hr => by
      have : r ≠ .t1 ∧ r ≠ .s5 ∧ r ≠ .s4 ∧ r ≠ .s6 ∧ r ≠ .t3 ∧ r ≠ .t4 := by revert r; decide
      rw [g r this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2.1 this.2.2.2.2.2]
      exact hI.untouched r hr), ?_, fun j hj => ?_⟩
  · rw [u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd, hI.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr, hI.wr]
  · rw [g .s2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.s2]
  · rw [g .s3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.s3]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂ _ (by decide) (by decide), u₁.other _ (by decide),
      hI.s4, ← BitVec.ofNat_add]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂ _ (by decide) (by decide), u₁.other _ (by decide),
      hI.s5, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂ _ (by decide) (by decide), u₁.other _ (by decide),
      hI.s6, sub_ofNat (by omega_using [hi]), Nat.sub_sub]
  · rw [u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp, hI.sp]
  · exact hI.saved.frame (fun d h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.k_o.sub_left (hp.stk.slot_sub h₁ h₂)) hfw
  · rw [Proof.Sha3.stateAt_congr fun j hj => hfw.bytes (R := SR s₀) (by simpa using hp.st_o)
      (by show 200 ≤ 2 ^ 64; decide) hj]
    exact hI.state
  · rw [hm]
    by_cases e : j < i
    · rw [Mem.writeW, Mem.write_apply]
      · exact hI.out j e
      · rw [Offset.sub_toNat' _ (by omega_using [hi, hn]) (by omega_using [hi, hn, hj])]; split <;> omega_arith
    · obtain ⟨d, m⟩ := div_mod_eq (k := k) hr0 (show pos + (j - i) < rate s₀ by omega_using [h8, hlt, hr8, hj])
      rw [show outp s₀ + BitVec.ofNat 64 j = outp s₀ + BitVec.ofNat 64 i + BitVec.ofNat 64 (j - i) by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' (by omega_using [e])],
        writeW64_byte _ _ _ (by omega_using [hj]), Mem.readW, BitVec.setWidth_eq,
        Mem.extractLsb'_read _ _ (show j - i < 64 / 8 by omega_using [hj]), BitVec.add_assoc,
        ← BitVec.ofNat_add, show pos₀ s₀ + j = rate s₀ * k + (pos + (j - i)) by
          have := hI.hi; omega_using [h8, hlt, hi, hal, hr0, hr200, hr8, hfit, hj, e, d, m, this], d, m, ← hI.state, byteOf_stateAt _ _ (by omega_using [h8, hlt, hi, hal, hr0, hr200, hn, hr8, hfit, hj, e, d, m])]

/-- After the permutation if one is due: a lane or a byte. -/
theorem tail_ok {s₀ : State} (hp : SPre s₀) {i k pos : Nat} {s : State} (hI : Inv s₀ i k pos s)
    (hlt : pos < rate s₀) (hi : i < outn s₀) :
    WP isa (.seq (.block laneCheck) (step squeezeLane squeezeByte)) s
      fun s' => ∃ i' k' pos', i < i' ∧ Inv s₀ i' k' pos' s' := by
  obtain hn := outn_lt s₀
  have ⟨hr0, hr200⟩ := hp.rate_pos
  refine WP.seq (WP.mono (laneCheck_ok hI.s2 hI.s4 hI.s6 (by omega_using [hlt, hr200]) (by omega_using [hn]))
    fun s₇ ⟨oth, ht2, m₇, rd₇, wr₇, sp₇, hz, hd⟩ => ?_)
  obtain hI₇ := hI.congr (fun r hr => oth r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) m₇ rd₇ wr₇ sp₇
  unfold step
  refine WP.ite (s₇.gpr .t1 == 0) (by show eval (.zero .t1) s₇ = _; rw [eval_zero])
    (fun hb => ?_) (fun _ => ?_)
  · obtain ⟨m8, al, l8⟩ := hz (by simpa using hb)
    obtain lane : ∀ b : Bool, (b = true → (outp s₀ + BitVec.ofNat 64 i).toNat % 8 = 0) →
        WP isa (.block (squeezeLane b)) s₇ fun s' => ∃ i' k' pos', i < i' ∧ Inv s₀ i' k' pos' s' :=
      fun b hb => WP.mono (store_lane hp hI₇ m8 hlt (by omega_using [l8]) ht2 al hb)
        fun s' h => ⟨i + 8, k, pos + 8, by omega_using [], h⟩
    refine WP.ite (s₇.gpr .t4 == 0) (by show eval (.zero .t4) s₇ = _; rw [eval_zero])
      (fun hb4 => lane true fun _ => ?_) (fun _ => lane false fun h => absurd h (by decide))
    rw [← hI.s5]; exact hd (by simpa using hb4)
  · exact WP.mono (store_ok hp hI₇ hlt hi) fun s' h => ⟨i + 1, k, pos + 1, by omega_using [], h⟩

theorem body_ok {s₀ : State} (hp : SPre s₀) {i k pos : Nat} {s : State} (hI : Inv s₀ i k pos s)
    (hi : i < outn s₀) :
    WP isa squeezeBody s fun s' => ∃ i' k' pos', i < i' ∧ Inv s₀ i' k' pos' s' := by
  have ⟨hr0, _⟩ := hp.rate_pos
  unfold squeezeBody permuteIfFull
  refine WP.seq (WP.seq (wp_sub fun s₁ u₁ => WP.block_nil ?_))
  obtain hI₁ := hI.congr (fun r hr => u₁.other r (by revert r; decide)) u₁.mem u₁.rd u₁.wr u₁.sp
  obtain hz : isa.eval (.zero .t1) s₁ = some (decide (pos = rate s₀)) := by
    show eval (.zero .t1) s₁ = _
    rw [eval_zero, u₁.gpr, hI.s4, hI.s3,
      sub_beq_zero (by have := hI.pos_le; have := (s₀.gpr .a1).isLt; omega_arith)]
  refine WP.mono (Q := fun s => ∃ k' pos', Inv s₀ i k' pos' s ∧ pos' < rate s₀) ?_
    fun s₂ ⟨k', pos', hI₂, hlt⟩ => tail_ok hp hI₂ hlt hi
  refine WP.ite (decide (pos = rate s₀)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    exact WP.mono (permute_ok hp hI₁) fun s' h => ⟨k + 1, 0, h, hr0⟩
  · simp only [decide_eq_false_iff_not] at hb
    exact WP.block_nil ⟨k, pos, hI₁, by have := hI.pos_le; omega_using [hb, this]⟩

/-! ## The whole function -/

theorem preserved_split : ∀ r ∈ preserved, r ∈ saved.map Prod.fst ∨ r ∈ untouched := by decide

theorem correct {s₀ : State} (hp : SPre s₀) :
    WP isa squeeze s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha3.squeezeRISCV64.post s₀ s' := by
  have hk := hp.stk
  obtain hn := outn_lt s₀
  have ⟨hr0, hr200⟩ := hp.rate_pos
  unfold squeeze withLoop frameBytes
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by have := hk.sp; omega_using [this]) ?_
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ hI => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ k pos, Inv s₀ (outn s₀) k pos s) ?_
    fun s₂ ⟨k, pos, hI₂⟩ => ?_)
  · refine WP.ite (decide (outn s₀ = 0))
      (by show eval (.zero .s6) s₁ = _
          rw [eval_zero, hI.s6, Nat.sub_zero, ofNat_beq_zero (by omega_using [hn])])
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      exact WP.block_nil ⟨0, pos₀ s₀, by rw [hb]; exact hI⟩
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.loop (M := isa) (fun n s => ∃ i k pos, n = outn s₀ - i ∧ i < outn s₀ ∧ Inv s₀ i k pos s)
        ?_ (outn s₀) s₁ ⟨0, 0, pos₀ s₀, by omega_using [], by omega_using [hb], hI⟩
      rintro n s ⟨i, k, pos, rfl, hi, hI⟩
      refine WP.mono (body_ok hp hI hi) fun s' ⟨i', k', pos', hii, hI'⟩ => ?_
      have hil := hI'.i_le
      obtain hz : isa.eval (.nonzero .s6) s' = some (decide (outn s₀ - i' ≠ 0)) := by
        show eval (.nonzero .s6) s' = _
        rw [eval_nonzero, hI'.s6, bne, ofNat_beq_zero (by omega_using [hn])]
        simp
      by_cases hl : outn s₀ - i' = 0
      · exact .inl ⟨by rw [hz]; simp [hl], k', pos', by rwa [show i' = outn s₀ by omega_using [hil, hl]] at hI'⟩
      · exact .inr ⟨by rw [hz]; simp [hl], _, by omega_using [hi, hii], i', k', pos', rfl, by omega_using [hl], hI'⟩
  · have hpl := hI₂.pos_le
    refine epilogue_ok (g := s₀.gpr) (by rw [hI₂.sp]; exact hk.B_al)
      (fun d hd₁ hd₂ => by
        rw [hI₂.rd, hI₂.wr, hI₂.sp]
        exact ⟨BR s₀, by simp, Offset.contains_base _ (by omega_using [hd₂]) (by omega_using [hd₂])⟩)
      (by rw [hI₂.sp]; exact hI₂.saved) fun s' h0 hsv hother hm hrd hwr hsp mL _ fl => ?_
    obtain hx0 : s'.gpr .a0 = BitVec.ofNat 64 pos := by rw [h0, hI₂.s4]
    -- The `free` loses the frame's bytes, which lie apart from the state and the output.
    obtain dS : (SR s₀).Disjoint ⟨s₀.sp - BitVec.ofNat 64 560, 560⟩ :=
      hp.k_st.symm.sub_right (Offset.sub_below _ (by decide) (by decide))
    obtain dO : (OR s₀).Disjoint ⟨s₀.sp - BitVec.ofNat 64 560, 560⟩ :=
      hp.k_o.symm.sub_right (Offset.sub_below _ (by decide) (by decide))
    refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, fun d => ?_⟩
    · show s'.gpr r = _
      rcases preserved_split r hr with h | h
      · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp h
        exact hsv p hp'
      · rw [hother r (by revert r; decide) (by revert r; decide) (by revert r; decide)]
        exact hI₂.untouched r h
    · show s'.sp + BitVec.ofNat 64 560 = s₀.sp
      rw [hsp, hI₂.sp, BitVec.sub_add_cancel]
    · exact hsv (.ra, 512) (by decide)
    · show bytesAt mL (outp s₀) (outn s₀) = Spec.Sha3.squeezeFrom (rate s₀) (S₀ s₀) (pos₀ s₀) (outn s₀)
      rw [show bytesAt mL (outp s₀) (outn s₀) = bytesAt s'.mem (outp s₀) (outn s₀) from
        List.map_congr_left fun i hi => lost_byte fl (R := OR s₀) dO (List.mem_range.mp hi), hm]
      refine List.ext_getElem (by rw [length_squeezeFrom hr0 hr200]; simp [bytesAt]) fun j h₁ _ => ?_
      obtain hj : j < outn s₀ := by simpa [bytesAt] using h₁
      rw [squeezeFrom_getElem hr0 hr200 _ hj]
      simp only [bytesAt, List.getElem_map, List.getElem_range]
      exact hI₂.out j hj
    · simp only [freed]
      rw [hx0, toNat_ofNat_lt (by omega_using [hr200, hpl])]; exact hpl
    · show Spec.Sha3.squeezeFrom (rate s₀) (stateAt mL (stp s₀)) (s'.gpr .a0).toNat d =
        Spec.Sha3.squeezeFrom (rate s₀) (S₀ s₀) (pos₀ s₀ + outn s₀) d
      rw [Proof.Sha3.stateAt_congr (m := s'.mem) fun i hi => lost_byte fl (R := SR s₀) dS hi, hm, hI₂.state, hx0, toNat_ofNat_lt (by omega_using [hr200, hpl]), squeezeFrom_iterF hr0 hr200, ← hI₂.hi]

end VG.Proof.Sha3.RISCV64.Stream.Squeeze

end

end


/-!
# The SHA-3 sponge on RISC-V: `Verified`

`absorb`, `absorbWs`, `pad` and `squeeze` (`Stream/`): correctness,
constant time (by taint tracking, `taint_decide`), and a state satisfying
each precondition, against the per-target contracts, then moved to the
shared ones of `Spec/Sha3/Contract.lean` with the stack they use: their
frame and the permutation's (608 bytes), or for `absorbWs`, which has no
frame, the permutation's alone. `absorb` has no shared contract: it is an internal
function, which RISC-V's verified code (ML-KEM, ML-DSA, Ed448, the SHA-3
pieces) calls by its per-target contract (`Calls.lean`).
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64.Stream

open VG VG.RISCV64

/-! ## `absorb` -/

theorem absorb_ct : ConstantTime isa Proof.Sha3.absorbRISCV64.pre Proof.Sha3.absorbRISCV64.pub
    Impl.Sha3.RISCV64.Stream.absorb := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, h2, h3, h4, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4]

/-- A state satisfying `absorb`'s precondition, with no data. -/
def absorbSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 72 | .a3 => 0x2000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 200⟩]

theorem absorb_verified' :
    Verified RISCV64.target Impl.Sha3.RISCV64.Stream.absorb Proof.Sha3.absorbRISCV64 := by
  refine ⟨fun s hs => ?_, absorb_ct, absorbSat, rfl, rfl, ?_, by decide, by decide, ?_, ?_,
    by decide, by decide⟩
  · obtain ⟨t, s', he, h⟩ := Absorb.correct (Absorb.pre_of hs)
    exact ⟨t, s', he, h⟩
  all_goals exact Region.disjoint_of_sep (by decide)

/-! ## `absorbWs` -/

theorem absorbWs_ct : ConstantTime isa Proof.Sha3.absorbWsRISCV64.pre Proof.Sha3.absorbWsRISCV64.pub
    Impl.Sha3.RISCV64.Stream.absorbWs := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4, h5]

/-- A state satisfying `absorbWs`'s precondition, with no data. -/
def absorbWsSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 72 | .a3 => 0x2000 | .a5 => 0x3000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 200⟩, ⟨0x3000, 640⟩]

theorem absorbWs_verified' :
    Verified RISCV64.target Impl.Sha3.RISCV64.Stream.absorbWs Proof.Sha3.absorbWsRISCV64 := by
  refine ⟨fun s hs => ?_, absorbWs_ct, absorbWsSat, rfl, rfl, ?_, ?_, ?_, by decide, by decide,
    by decide, by decide, ?_, ?_, ?_, by decide, by decide⟩
  · obtain ⟨t, s', he, h⟩ := AbsorbWs.correct (AbsorbWs.pre_of hs)
    exact ⟨t, s', he, h⟩
  all_goals exact Region.disjoint_of_sep (by decide)

/-! ## `pad` -/

theorem pad_ct : ConstantTime isa Proof.Sha3.padRISCV64.pre Proof.Sha3.padRISCV64.pub
    Impl.Sha3.RISCV64.Stream.pad := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, h2, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [h0, h1, h2]

/-- A state satisfying `pad`'s precondition. -/
def padSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 136 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 200⟩]

theorem pad_verified' :
    Verified RISCV64.target Impl.Sha3.RISCV64.Stream.pad Proof.Sha3.padRISCV64 := by
  refine ⟨fun s hs => ?_, pad_ct, padSat, rfl, rfl, by decide, by decide, ?_, by decide, by decide⟩
  · obtain ⟨t, s', he, h⟩ := Pad.correct (Pad.pre_of hs)
    exact ⟨t, s', he, h⟩
  · exact Region.disjoint_of_sep (by decide)

/-! ## `squeeze` -/

theorem squeeze_ct : ConstantTime isa Proof.Sha3.squeezeRISCV64.pre Proof.Sha3.squeezeRISCV64.pub
    Impl.Sha3.RISCV64.Stream.squeeze := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, h2, h3, h4, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4]

/-- A state satisfying `squeeze`'s precondition, with no output. -/
def squeezeSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 72 | .a3 => 0x2000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x2000, 0⟩]

theorem squeeze_verified' :
    Verified RISCV64.target Impl.Sha3.RISCV64.Stream.squeeze Proof.Sha3.squeezeRISCV64 := by
  refine ⟨fun s hs => ?_, squeeze_ct, squeezeSat, rfl, rfl, ?_, by decide, by decide, ?_, ?_,
    by decide, by decide⟩
  · obtain ⟨t, s', he, h⟩ := Squeeze.correct (Squeeze.pre_of hs)
    exact ⟨t, s', he, h⟩
  all_goals exact Region.disjoint_of_sep (by decide)

end VG.Proof.Sha3.RISCV64.Stream
