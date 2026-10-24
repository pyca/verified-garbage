module

import VerifiedGarbage.Proof.Sha3.PPC64LE.Call
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Wp
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Sha3.PPC64LE.Stream
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Sha3.PPC64LE.Contract
public import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# The SHA-3 sponge on PPC64LE: `pad`

The same structure as the AArch64 proof (`VG.Proof.Sha3.AArch64.Stream.Pad`):
`padMain`, whose frame saving the link register `correct` adds
(`WP.frameReg`).
-/

@[expose] public section

namespace VG.Proof.Sha3.PPC64LE.Stream.Pad

open VG VG.PPC64LE VG.Impl.Sha3.PPC64LE.Stream
open VG.Proof.Sha3.PPC64LE VG.Proof.Sha3.PPC64LE.Stream
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_mov wp_subi wp_li wp_add wp_lbz wp_stb contains_offset)
open VG.Spec.Sha3 (stateAt keccakF absorb pad rates Repr)
open VG.Proof.Sha3 (xorByte Rep stateAt_xorByte absorb_pad)

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .r3
abbrev rt : Nat := (s₀.gpr .r4).toNat
abbrev pos : Nat := (s₀.gpr .r5).toNat
abbrev scr : Addr := s₀.gpr .r7
abbrev stR : Region := ⟨st s₀, 200⟩
abbrev scR : Region := ⟨scr s₀, 640⟩
/-- The frame saving the link register, below the stack pointer. -/
abbrev stkR : Region := ⟨s₀.sp - 48, 48⟩

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, scR s₀]
  st_scr : (stR s₀).Disjoint (scR s₀)
  rate : rt s₀ ∈ rates
  pos_lt : pos s₀ < rt s₀

/-- The frame is below the stack pointer, and disjoint from the buffers. -/
structure Stack (s₀ : State) : Prop where
  sp48 : 48 ≤ s₀.sp.toNat
  st : (stkR s₀).Disjoint (stR s₀)
  scr : (stkR s₀).Disjoint (scR s₀)

theorem pre_of {s₀ : State} (h : Proof.Sha3.padPPC64LE.pre s₀) : Pre s₀ ∧ Stack s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨⟨h1, h2, h3, h7, h8⟩, ⟨h4, h5, h6⟩⟩

theorem x80 : (BitVec.ofNat 64 0x80).setWidth 8 = (0x80 : BitVec 8) := by decide

theorem keep_ne : ∀ r ∈ preserved, r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r4 := by decide

/-- `pad` without its frame: the callee-saved registers are kept. -/
theorem correctMain {s₀ : State} (hp : Pre s₀) :
    WP isa padMain s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ Proof.Sha3.padPPC64LE.post s₀ s' := by
  have hr : 72 ≤ (s₀.gpr .r4).toNat ∧ (s₀.gpr .r4).toNat ≤ 168 := Proof.Sha3.rate_bounds hp.rate
  have hpl : (s₀.gpr .r5).toNat < (s₀.gpr .r4).toNat := hp.pos_lt
  have hin : ∀ j < 200, (stR s₀).Contains (st s₀ + BitVec.ofNat 64 j) 1 := fun j hj =>
    contains_offset (by omega) (by omega)
  have hw : ∀ j < 200, InRegions s₀.wr (st s₀ + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hp.wr]; exact ⟨_, List.mem_cons_self .., hin j hj⟩
  have hw' : ∀ j < 200, InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hp.rd]; exact hw j hj
  unfold padMain
  refine WP.seq (wp_add fun s₁ u₁ => ?_)
  have e₁ : s₁.gpr .r9 + BitVec.ofNat 64 0 = st s₀ + BitVec.ofNat 64 ((s₀.gpr .r5).toNat) := by
    rw [u₁.gpr]; simp
  refine wp_lbz (a := st s₀ + BitVec.ofNat 64 ((s₀.gpr .r5).toNat)) (by omega) e₁
    (by rw [u₁.rd, u₁.wr]; exact hw' _ (by omega)) fun s₂ u₂ => wp_xor fun s₃ u₃ =>
    wp_stb (a := st s₀ + BitVec.ofNat 64 ((s₀.gpr .r5).toNat)) (by omega)
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide)]; exact e₁)
      (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hw _ (by omega)) fun s₄ g₄ => ?_
  have k₄ : ∀ r, r ≠ .r9 → r ≠ .r10 → s₄.gpr r = s₀.gpr r := fun r h h' => by
    rw [g₄.gpr, u₃.other _ h', u₂.other _ h', u₁.other _ h]
  refine wp_add fun s₅ u₅ => wp_subi (by decide) fun s₆ u₆ => ?_
  have e₆ : s₆.gpr .r9 + BitVec.ofNat 64 0 = st s₀ + BitVec.ofNat 64 ((s₀.gpr .r4).toNat - 1) := by
    rw [u₆.gpr, u₅.gpr, k₄ _ (by decide) (by decide), k₄ _ (by decide) (by decide)]
    simp only [st]
    rw [BitVec.add_zero]; exact Offset.add_sub_one64 _ _ (by omega)
  refine wp_lbz (a := st s₀ + BitVec.ofNat 64 ((s₀.gpr .r4).toNat - 1)) (by omega) e₆
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, g₄.rd, g₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
        exact hw' _ (by omega))
    fun s₇ u₇ => wp_li (by decide) fun s₈ u₈ => wp_xor fun s₉ u₉ =>
    wp_stb (a := st s₀ + BitVec.ofNat 64 ((s₀.gpr .r4).toNat - 1)) (by omega)
      (by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide)]; exact e₆)
      (by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, g₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hw _ (by omega))
    fun s₁₀ g₁₀ => wp_mov fun s₁₁ u₁₁ => WP.block_nil ?_
  -- The two bytes written.
  have hb₁ : s₄.mem = s₀.mem.writeW (st s₀ + BitVec.ofNat 64 ((s₀.gpr .r5).toNat))
      (s₀.mem (st s₀ + BitVec.ofNat 64 ((s₀.gpr .r5).toNat)) ^^^ (s₀.gpr .r6).setWidth 8) := by
    rw [g₄.mem, u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.other _ (by decide), u₃.mem, u₂.mem,
      u₁.mem, Proof.Sha3.xor_byte]
  have hb₂ : s₁₀.mem = s₄.mem.writeW (st s₀ + BitVec.ofNat 64 ((s₀.gpr .r4).toNat - 1))
      (s₄.mem (st s₀ + BitVec.ofNat 64 ((s₀.gpr .r4).toNat - 1)) ^^^ 0x80) := by
    rw [g₁₀.mem, u₉.gpr, u₈.gpr, u₈.other _ (by decide), u₇.gpr, u₉.mem, u₈.mem, u₇.mem, u₆.mem,
      u₅.mem, Proof.Sha3.xor_byte, x80]
  have hS : stateAt s₁₀.mem (st s₀) =
      xorByte (xorByte (stateAt s₀.mem (st s₀)) ((s₀.gpr .r5).toNat) ((s₀.gpr .r6).setWidth 8)) ((s₀.gpr .r4).toNat - 1) 0x80 := by
    rw [← stateAt_xorByte (m := s₀.mem) (m' := s₄.mem) (by omega)
      (by simp only [hb₁, Proof.Sha3.writeW8_apply, ↓reduceIte])
      (fun i hi hne => by
        simp only [hb₁, Proof.Sha3.writeW8_apply, Proof.Sha3.ne_of_lt200 hi (by omega) hne, ite_false])]
    exact stateAt_xorByte (by omega) (by simp only [hb₂, Proof.Sha3.writeW8_apply, ↓reduceIte])
      (fun i hi hne => by
        simp only [hb₂, Proof.Sha3.writeW8_apply, Proof.Sha3.ne_of_lt200 hi (by omega) hne, ite_false])
  have k₁₁ : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r4 → s₁₁.gpr r = s₀.gpr r :=
    fun r h9 h10 h11 h1 => by
      rw [u₁₁.other _ h1, g₁₀.gpr, u₉.other _ h10, u₈.other _ h11, u₇.other _ h10, u₆.other _ h9,
        u₅.other _ h9, k₄ _ h9 h10]
  have sp₁₁ : s₁₁.sp = s₀.sp := by
    rw [u₁₁.sp, g₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, g₄.sp, u₃.sp, u₂.sp, u₁.sp]
  have e512 : Region.Sub ⟨scr s₀, 512⟩ (scR s₀) := Region.sub_prefix (by omega)
  refine call_ok (st := st s₀) (scr := scr s₀)
    (by rw [k₁₁ _ (by decide) (by decide) (by decide) (by decide)])
    (by rw [u₁₁.gpr, g₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), k₄ _ (by decide) (by decide)])
    (hp.st_scr.sub_right e512)
    (by
      rw [u₁₁.wr, g₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, g₄.wr, u₃.wr, u₂.wr, u₁.wr, hp.wr]
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩)
    fun s' _ _ sp' cs' _ e' => ?_
  refine ⟨fun r hr => ?_, by rw [sp', sp₁₁], fun msg hR hm => ?_⟩
  · have ne := keep_ne r hr
    rw [cs' r hr, k₁₁ r ne.1 ne.2.1 ne.2.2.1 ne.2.2.2]
  · rw [e', u₁₁.mem, hS, absorb_pad (by omega) (by omega), ← hm,
      show Rep ((s₀.gpr .r4).toNat) msg = stateAt s₀.mem (st s₀) from hR.symm]

end VG.Proof.Sha3.PPC64LE.Stream.Pad
