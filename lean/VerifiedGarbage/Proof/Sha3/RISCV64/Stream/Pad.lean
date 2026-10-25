module

public import VerifiedGarbage.Proof.Sha3.RISCV64.Call
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The SHA-3 sponge on RISC-V: `pad`

As on PPC64LE (`Proof/Sha3/PPC64LE/Stream/Pad.lean`), in a frame on the
stack (`WP.alloc`) that holds the permutation's scratch space and the saved
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
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]
  omega

theorem B_toNat : 608 ≤ (B s₀).toNat := by
  have := hp.sp
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]
  omega

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
  have hr : 72 ≤ (s₀.gpr .a1).toNat ∧ (s₀.gpr .a1).toNat ≤ 168 := Proof.Sha3.rate_bounds hp.rate
  have hpl := hp.pos_lt
  have hB := hp.B_eq
  unfold Impl.Sha3.RISCV64.Stream.pad padBytes
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by have := hp.sp; omega) ?_
  -- In the frame.
  let s := allocd 528 s₀
  have hsp : s.sp = B s₀ := rfl
  have hwr : s.wr = [⟨B s₀, 528⟩, stR s₀] := by simp only [s, allocd, hp.wr]
  have hin : ∀ j < 200, InRegions s.wr (st s₀ + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hwr]; exact ⟨stR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hin' : ∀ j < 200, InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [show s.rd = [] from hp.rd]; exact hin j hj
  have hra : InRegions s.wr (B s₀ + BitVec.ofNat 64 512) 8 := by
    rw [hwr]; exact ⟨_, List.mem_cons_self .., Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.seq ?_
  unfold padMain
  refine wp_addSp (by decide) fun s₁ u₁ => ?_
  have h₁ : s₁.gpr .t0 = B s₀ := by rw [u₁.gpr, hsp]; exact BitVec.add_zero _
  refine wp_sd (by decide) (a := B s₀ + BitVec.ofNat 64 512) (by rw [h₁])
    (al8 hp.B_al (by decide) (by decide)) (by rw [u₁.wr]; exact hra) fun s₂ g₂ => ?_
  have k₂ : ∀ r, r ≠ .t0 → s₂.gpr r = s₀.gpr r := fun r h => by rw [g₂.gpr, u₁.other _ h]; rfl
  refine wp_add fun s₃ u₃ => ?_
  have e₃ : s₃.gpr .t1 + BitVec.ofNat 64 0 = st s₀ + BitVec.ofNat 64 ((s₀.gpr .a2).toNat) := by
    rw [u₃.gpr, k₂ _ (by decide), k₂ _ (by decide)]; simp
  refine wp_lbu (a := st s₀ + BitVec.ofNat 64 ((s₀.gpr .a2).toNat)) (by decide) e₃
    (by rw [u₃.rd, u₃.wr, g₂.rd, g₂.wr, u₁.rd, u₁.wr]; exact hin' _ (by omega)) fun s₄ u₄ =>
    wp_xor fun s₅ u₅ => wp_sb (a := st s₀ + BitVec.ofNat 64 ((s₀.gpr .a2).toNat)) (by decide)
      (by rw [u₅.other _ (by decide), u₄.other _ (by decide)]; exact e₃)
      (by rw [u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr]; exact hin _ (by omega)) fun s₆ g₆ => ?_
  have k₆ : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → s₆.gpr r = s₀.gpr r := fun r h0 h1 h2 => by
    rw [g₆.gpr, u₅.other _ h2, u₄.other _ h2, u₃.other _ h1, k₂ _ h0]
  refine wp_add fun s₇ u₇ => wp_subi (imm := 1) (by decide) fun s₈ u₈ => ?_
  have e₈ : s₈.gpr .t1 + BitVec.ofNat 64 0 =
      st s₀ + BitVec.ofNat 64 ((s₀.gpr .a1).toNat - 1) := by
    rw [u₈.gpr, u₇.gpr, k₆ _ (by decide) (by decide) (by decide),
      k₆ _ (by decide) (by decide) (by decide), BitVec.add_zero]
    exact Offset.add_sub_one64 _ _ (by omega)
  refine wp_lbu (a := st s₀ + BitVec.ofNat 64 ((s₀.gpr .a1).toNat - 1)) (by decide) e₈
    (by rw [u₈.rd, u₈.wr, u₇.rd, u₇.wr, g₆.rd, g₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr,
          g₂.rd, g₂.wr, u₁.rd, u₁.wr]
        exact hin' _ (by omega))
    fun s₉ u₉ => wp_xori (imm := 0x80) (by decide) fun s₁₀ u₁₀ =>
    wp_sb (a := st s₀ + BitVec.ofNat 64 ((s₀.gpr .a1).toNat - 1)) (by decide)
      (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide)]; exact e₈)
      (by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, g₆.wr, u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr]
          exact hin _ (by omega))
    fun s₁₁ g₁₁ => wp_addSp (by decide) fun s₁₂ u₁₂ => WP.block_nil ?_
  -- The two bytes written.
  have hb₁ : s₆.mem = s₂.mem.writeW (st s₀ + BitVec.ofNat 64 ((s₀.gpr .a2).toNat))
      (s₂.mem (st s₀ + BitVec.ofNat 64 ((s₀.gpr .a2).toNat)) ^^^ (s₀.gpr .a3).setWidth 8) := by
    rw [g₆.mem, u₅.gpr, u₄.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      k₂ _ (by decide), u₅.mem, u₄.mem, u₃.mem, xor_lo, lbu_lo]
  have hb₂ : s₁₁.mem = s₆.mem.writeW (st s₀ + BitVec.ofNat 64 ((s₀.gpr .a1).toNat - 1))
      (s₆.mem (st s₀ + BitVec.ofNat 64 ((s₀.gpr .a1).toNat - 1)) ^^^ 0x80) := by
    rw [g₁₁.mem, u₁₀.gpr, u₉.gpr, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, xor_lo, lbu_lo, x80]
  have hraR : Region.Disjoint ⟨B s₀ + BitVec.ofNat 64 512, 8⟩ (stR s₀) := by
    have := hp.stk_sub (d := 1120) (n := 8) (by omega)
    rwa [show K s₀ + BitVec.ofNat 64 1120 = B s₀ + BitVec.ofNat 64 512 by
      rw [hB, BitVec.add_assoc, BitVec.ofNat_add_ofNat]] at this
  have f₂ : Frame [⟨B s₀ + BitVec.ofNat 64 512, 8⟩] s₀.mem s₂.mem := by
    rw [g₂.mem, u₁.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hst₂ : ∀ i < 200, s₂.mem (st s₀ + BitVec.ofNat 64 i) = s₀.mem (st s₀ + BitVec.ofNat 64 i) :=
    fun i hi => f₂.bytes (R := stR s₀) (by simpa using hraR.symm) (by show 200 ≤ 2 ^ 64; decide) hi
  have k₁₂ : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → r ≠ .a1 → s₁₂.gpr r = s₀.gpr r :=
    fun r h0 h1 h2 ha => by
      rw [u₁₂.other _ ha, g₁₁.gpr, u₁₀.other _ h2, u₉.other _ h2, u₈.other _ h1, u₇.other _ h1,
        k₆ _ h0 h1 h2]
  have sp₁₂ : s₁₂.sp = B s₀ := by
    rw [u₁₂.sp, g₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, g₆.sp, u₅.sp, u₄.sp, u₃.sp, g₂.sp, u₁.sp, hsp]
  have wr₁₂ : s₁₂.wr = [⟨B s₀, 528⟩, stR s₀] := by
    rw [u₁₂.wr, g₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, g₆.wr, u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr, hwr]
  have rd₁₂ : s₁₂.rd = [] := by
    rw [u₁₂.rd, g₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, g₆.rd, u₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd]
    exact hp.rd
  have hS : stateAt s₁₂.mem (st s₀) =
      xorByte (xorByte (stateAt s₀.mem (st s₀)) ((s₀.gpr .a2).toNat) ((s₀.gpr .a3).setWidth 8))
        ((s₀.gpr .a1).toNat - 1) 0x80 := by
    have e₀ : stateAt s₂.mem (st s₀) = stateAt s₀.mem (st s₀) :=
      Proof.Sha3.stateAt_congr fun i hi => hst₂ i hi
    rw [← e₀, ← stateAt_xorByte (m := s₂.mem) (m' := s₆.mem) (by omega)
      (by simp only [hb₁, Proof.Sha3.writeW8_apply, ↓reduceIte])
      (fun i hi hne => by
        simp only [hb₁, Proof.Sha3.writeW8_apply, Proof.Sha3.ne_of_lt200 hi (by omega) hne, ite_false])]
    rw [show s₁₂.mem = s₁₁.mem from u₁₂.mem]
    exact stateAt_xorByte (by omega) (by simp only [hb₂, Proof.Sha3.writeW8_apply, ↓reduceIte])
      (fun i hi hne => by
        simp only [hb₂, Proof.Sha3.writeW8_apply, Proof.Sha3.ne_of_lt200 hi (by omega) hne, ite_false])
  -- The slot of the return address, which the bytes of the state do not touch.
  have hraS : s₁₂.mem.readW (B s₀ + BitVec.ofNat 64 512) 64 = s₀.gpr .ra := by
    have f : Frame [stR s₀] s₂.mem s₁₂.mem := by
      rw [u₁₂.mem, hb₂, hb₁]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (by omega) (by omega))).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (by omega) (by omega))
    rw [f.readW (Region.contains_self _ _) (by simpa using hraR) (by decide), g₂.mem,
      Mem.readW_writeW_self64, u₁.other _ (by decide)]
    rfl
  have hstk : Region.Disjoint ⟨B s₀ - 608, 608⟩ (stR s₀) := by
    rw [hp.below_eq]; simpa using hp.stk_sub (d := 0) (n := 608) (by omega)
  have hscr : Region.Disjoint (stR s₀) ⟨B s₀, 512⟩ := by
    have := hp.stk_sub (d := 608) (n := 512) (by omega)
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
  have hf' : s'.mem.readW (B s₀ + BitVec.ofNat 64 512) 64 = s₀.gpr .ra := by
    rw [sp₁₂] at f'
    rw [f'.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide), hraS]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hraR
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · rw [hp.below_eq, hB, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact Offset.disjoint_base _ (by omega) (by omega)
  refine wp_ld (by decide) (a := B s₀ + BitVec.ofNat 64 512)
    (by rw [u₁₃.gpr, sp', sp₁₂, show B s₀ + BitVec.ofNat 64 0 = B s₀ from BitVec.add_zero _])
    (al8 hp.B_al (by decide) (by decide))
    (by rw [u₁₃.rd, u₁₃.wr, rd', wr', rd₁₂, wr₁₂]
        exact ⟨_, List.mem_cons_self .., Offset.contains_base _ (by omega) (by omega)⟩)
    fun s₁₄ u₁₄ => WP.block_nil ?_
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun msg hR hm => ?_⟩
  · have ne := keep_ne r hr
    have hra : r ≠ .ra := by revert r; decide
    show s₁₄.gpr r = _
    rw [u₁₄.other _ hra, u₁₃.other _ ne.1, cs' r hr, k₁₂ r ne.1 ne.2.1 ne.2.2.1 ne.2.2.2]
  · show s₁₄.sp + BitVec.ofNat 64 528 = s₀.sp
    rw [u₁₄.sp, u₁₃.sp, sp', sp₁₂, BitVec.sub_add_cancel]
  · show s₁₄.gpr .ra = _
    rw [u₁₄.gpr, u₁₃.mem, hf']
  · simp only [freed]
    rw [u₁₄.mem, u₁₃.mem, e', hS, absorb_pad (by omega) (by omega), ← hm,
      show Rep ((s₀.gpr .a1).toNat) msg = stateAt s₀.mem (st s₀) from hR.symm]

end VG.Proof.Sha3.RISCV64.Stream.Pad
