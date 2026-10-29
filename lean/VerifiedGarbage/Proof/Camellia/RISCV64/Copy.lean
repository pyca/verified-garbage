module
public import VerifiedGarbage.Impl.Camellia.RISCV64.Ecb
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem

import VerifiedGarbage.Proof.Camellia.RISCV64.Keys
import VerifiedGarbage.Proof.Camellia.RISCV64.Prologue
import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Copying blocks on RISC-V

As on PPC64LE (`Proof/Camellia/PPC64LE/Copy.lean`): the loops `copyInBlocks`
and `copyOutBlocks` copy `c ≥ 1` blocks of 16 bytes from `t3` to `t4`
(areas that do not overlap), through `t0`–`t2`, counting down `t5`, and
change nothing else in memory. `copyLoop_wp` proves the loop once for any
copy of a word (`CopiesWord`): `copyIn_word` reads the data a byte at a
time and writes the aligned tail buffer, `copyOut_word` the reverse.
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64

open VG VG.RISCV64 VG.Impl.Camellia.RISCV64
open VG.Impl.Aes.RISCV64 (t0 t1 t2)

/-- What copying a word at offset `d` does: `[t4 + d] := [t3 + d]`,
through `t0`–`t2`, for the pointers at block `j < c` from `A` and `B`. -/
def CopiesWord (W : Nat → List Instr) (A B : Addr) (c : Nat) : Prop :=
  ∀ (s : State) (j d : Nat), j < c → (d = 0 ∨ d = 8) →
    s.gpr .t3 = A + BitVec.ofNat 64 (16 * j) → s.gpr .t4 = B + BitVec.ofNat 64 (16 * j) →
    InRegions (s.rd ++ s.wr) (s.gpr .t3 + BitVec.ofNat 64 d) 8 →
    InRegions s.wr (s.gpr .t4 + BitVec.ofNat 64 d) 8 →
    ∃ s', runBlock isa (W d) s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .t4 + BitVec.ofNat 64 d) (s.mem.readW (s.gpr .t3 + BitVec.ofNat 64 d) 64) ∧
      (∀ r, r ≠ t0 → r ≠ t1 → r ≠ t2 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr

/-- A word of the data to the tail buffer. -/
def wordIn (d : Nat) : List Instr :=
  Impl.Words64.RISCV64.loadLE64 t0 t1 t2 .t3 d ++ [.store .d t0 .t4 d]

/-- A word of the tail buffer to the data. -/
def wordOut (d : Nat) : List Instr :=
  [.load .d t0 .t3 d] ++ Impl.Words64.RISCV64.storeLE64 t0 t1 t2 .t4 d

theorem copyInBlocks_eq : copyInBlocks = .loop (.block (wordIn 0 ++ (wordIn 8 ++ copyStep))) (.nonzero .t5) := by
  simp only [copyInBlocks, wordIn, List.append_assoc]

theorem copyOutBlocks_eq :
    copyOutBlocks = .loop (.block (wordOut 0 ++ (wordOut 8 ++ copyStep))) (.nonzero .t5) := by
  simp only [copyOutBlocks, wordOut, List.append_assoc]

theorem copyIn_word {A B : Addr} {c : Nat} (hB : B.toNat % 8 = 0) : CopiesWord wordIn A B c := by
  intro s j d _ hd _ hdst hr hw
  obtain ⟨s₁, e₁, u₁⟩ := WP.runBlock_of (Words64.loadLE64_ok (s := s) (d := t0) (tmp := t1) (tmp2 := t2)
    (n := .t3) (off := d) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rcases hd with rfl | rfl <;> decide) hr)
  have h4 : s₁.gpr .t4 = s.gpr .t4 := u₁.other _ (by decide) (by decide) (by decide)
  refine ⟨{ s₁ with mem := s₁.mem.writeW (s₁.gpr .t4 + BitVec.ofNat 64 d) (s₁.gpr t0) }, ?_, ?_,
    fun r h0 h1 h2 => u₁.other r h0 h1 h2, u₁.rd, u₁.wr⟩
  · rw [wordIn, runBlock_append', e₁, Option.bind_some]
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_store_d (show d < 2048 by omega)
      (by rw [h4, hdst, addr_add]; exact Spill.al8 hB (by omega))
      (by rw [u₁.wr, h4]; exact hw)]
  · show s₁.mem.writeW _ _ = _
    rw [u₁.mem, h4, u₁.gpr]

theorem copyOut_word {A B : Addr} {c : Nat} (hA : A.toNat % 8 = 0) : CopiesWord wordOut A B c := by
  intro s j d _ hd hsrc _ hr hw
  let s₁ := s.write t0 (s.mem.readW (s.gpr .t3 + BitVec.ofNat 64 d) 64)
  have e₁ : runBlock isa [.load .d t0 .t3 d] s = some s₁ := by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_load_d (show d < 2048 by omega)
      (by rw [hsrc, addr_add]; exact Spill.al8 hA (by omega)) hr]
    rfl
  have h4 : s₁.gpr .t4 = s.gpr .t4 := RegUpd.gpr_write_of_ne _ _ (by decide)
  obtain ⟨s₂, e₂, g₂, m₂, rd₂, wr₂, -⟩ := WP.runBlock_of (Words64.storeLE64_ok (s := s₁) (v := t0)
    (tmp := t1) (tmp2 := t2) (n := .t4) (off := d) (by decide) (by decide) (by decide) (by decide)
    (by rcases hd with rfl | rfl <;> decide) (by rw [h4]; exact hw))
  refine ⟨s₂, ?_, ?_, fun r h0 h1 h2 => by rw [g₂ r h1 h2]; exact RegUpd.gpr_write_of_ne _ _ h0, rd₂, wr₂⟩
  · rw [wordOut, runBlock_append', e₁, Option.bind_some]; exact e₂
  · rw [m₂, h4, RegUpd.gpr_write_self]; rfl

/-- Copying, after `j` of `c` blocks. -/
structure CopyInv (A B : Addr) (c : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  src : s.gpr .t3 = A + BitVec.ofNat 64 (16 * j)
  dst : s.gpr .t4 = B + BitVec.ofNat 64 (16 * j)
  cnt : s.gpr .t5 = BitVec.ofNat 64 (c - j)
  copied : ∀ t < 16 * j, s.mem (B + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t)
  frame : Frame [⟨B, 16 * c⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → r ≠ t0 → r ≠ t1 → r ≠ t2 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem copyLoop_wp {W : Nat → List Instr} {A B : Addr} {c : Nat} {s₀ : State} (hW : CopiesWord W A B c) (hc : 0 < c) (hcBound : c ≤ 17)
    (hA : ∀ t < 2 * c, InRegions (s₀.rd ++ s₀.wr) (A + BitVec.ofNat 64 (8 * t)) 8)
    (hB : ∀ t < 2 * c, InRegions s₀.wr (B + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨A, 16 * c⟩ ⟨B, 16 * c⟩) (hs : CopyInv A B c s₀ 0 s₀) :
    WP isa (.loop (.block (W 0 ++ (W 8 ++ copyStep))) (.nonzero .t5)) s₀ (CopyInv A B c s₀ c) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = c - j ∧ j < c ∧ CopyInv A B c s₀ j s)
    (fun n s hs => ?_) c s₀ ⟨0, by omega_arith, hc, hs⟩
  obtain ⟨j, rfl, hj, hi⟩ := hs
  have hA0 := hA (2 * j) (by omega_arith)
  have hA1 := hA (2 * j + 1) (by omega_arith)
  have hB0 := hB (2 * j) (by omega_arith)
  have hB1 := hB (2 * j + 1) (by omega_arith)
  have hfA : Frame [⟨B, 16 * c⟩] s₀.mem s.mem := hi.frame
  have hAs : ∀ t < 16 * c, s.mem (A + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t) := fun t ht =>
    hfA.bytes (R := ⟨A, 16 * c⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep)
      (by simp only; omega_arith) ht
  obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := hW s j 0 hj (Or.inl rfl) hi.src hi.dst
    (by rw [hi.rd, hi.wr, hi.src, addr_add, show 16 * j + 0 = 8 * (2 * j) by omega_arith]; exact hA0)
    (by rw [hi.wr, hi.dst, addr_add, show 16 * j + 0 = 8 * (2 * j) by omega_arith]; exact hB0)
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := hW s₁ j 8 hj (Or.inr rfl)
    (by rw [g₁ _ (by decide) (by decide) (by decide), hi.src])
    (by rw [g₁ _ (by decide) (by decide) (by decide), hi.dst])
    (by rw [rd₁, wr₁, hi.rd, hi.wr, g₁ _ (by decide) (by decide) (by decide), hi.src, addr_add,
      show 16 * j + 8 = 8 * (2 * j + 1) by omega_arith]; exact hA1)
    (by rw [wr₁, hi.wr, g₁ _ (by decide) (by decide) (by decide), hi.dst, addr_add, show 16 * j + 8 = 8 * (2 * j + 1) by omega_arith]; exact hB1)
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := addI_ok s₂ .t3 .t3 16 (by decide)
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := addI_ok s₃ .t4 .t4 16 (by decide)
  obtain ⟨s₅, e₅, c₅, o₅, m₅, rd₅, wr₅⟩ := subI_ok s₄ .t5 .t5 1 (by decide)
  refine WP.of_runBlock ⟨s₅, by
    rw [show copyStep = [.addi .t3 .t3 16] ++ ([.addi .t4 .t4 16] ++ [.addi .t5 .t5 (-1)]) from rfl,
      runBlock_append', e₁, Option.bind_some, runBlock_append', e₂, Option.bind_some, runBlock_append', e₃,
      Option.bind_some, runBlock_append', e₄, Option.bind_some]
    exact e₅, ?_⟩
  have hn : 16 * c < 2 ^ 64 := by omega_arith
  have r1 : s₁.gpr .t4 = B + BitVec.ofNat 64 (16 * j) := by rw [g₁ _ (by decide) (by decide) (by decide), hi.dst]
  have a1 : s₁.gpr .t3 = A + BitVec.ofNat 64 (16 * j) := by rw [g₁ _ (by decide) (by decide) (by decide), hi.src]
  have hm : s₅.mem = (s₁.mem.writeW (B + BitVec.ofNat 64 (16 * j + 8))
      (s₁.mem.readW (A + BitVec.ofNat 64 (16 * j + 8)) 64)) := by
    rw [m₅, m₄, m₃, m₂, r1, a1, addr_add, addr_add]
  have hm₁ : s₁.mem = s.mem.writeW (B + BitVec.ofNat 64 (16 * j))
      (s.mem.readW (A + BitVec.ofNat 64 (16 * j)) 64) := by
    rw [m₁, hi.dst, hi.src, addr_add, addr_add, Nat.add_zero]
  -- `s₁` and `s` agree on `A`'s area.
  have hA₁ : ∀ t < 16 * c, s₁.mem (A + BitVec.ofNat 64 t) = s.mem (A + BitVec.ofNat 64 t) := fun t ht => by
    rw [hm₁, writeW_readW_apply, ite_eq_right (not_in_of_disjoint hsep ht (by omega_arith) hn)]
  have hc₅ : s₅.gpr .t5 = BitVec.ofNat 64 (c - (j + 1)) := by
    rw [c₅, o₄ _ (by decide), o₃ _ (by decide), g₂ _ (by decide) (by decide) (by decide),
      g₁ _ (by decide) (by decide) (by decide), hi.cnt,
      VG.Offset.ofNat_sub_ofNat (by omega_arith), show c - j - 1 = c - (j + 1) by omega_arith]
  have hinv : CopyInv A B c s₀ (j + 1) s₅ := by
    refine ⟨?_, ?_, hc₅, fun t ht => ?_, hi.frame.trans fun x hx => ?_, fun r h1 h2 h3 h4 h5 h6 => ?_,
      by rw [rd₅, rd₄, rd₃, rd₂, rd₁, hi.rd], by rw [wr₅, wr₄, wr₃, wr₂, wr₁, hi.wr]⟩
    · rw [o₅ _ (by decide), o₄ _ (by decide), a₃, g₂ _ (by decide) (by decide) (by decide), a1, addr_add,
        show 16 * j + 16 = 16 * (j + 1) by omega_arith]
    · rw [o₅ _ (by decide), a₄, o₃ _ (by decide), g₂ _ (by decide) (by decide) (by decide), r1, addr_add,
        show 16 * j + 16 = 16 * (j + 1) by omega_arith]
    · rw [hm, writeW_readW_apply]
      by_cases h8 : 16 * j + 8 ≤ t
      · rw [ite_eq_left (by rw [off_sub_toNat B h8 (by omega_arith)]; omega_arith), off_sub_toNat B h8 (by omega_arith), addr_add,
          show 16 * j + 8 + (t - (16 * j + 8)) = t by omega_arith, hA₁ t (by omega_arith), hAs t (by omega_arith)]
      · rw [ite_eq_right (off_sub_not B (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith)), hm₁,
          writeW_readW_apply]
        by_cases h0 : 16 * j ≤ t
        · rw [ite_eq_left (by rw [off_sub_toNat B h0 (by omega_arith)]; omega_arith), off_sub_toNat B h0 (by omega_arith), addr_add,
            show 16 * j + (t - 16 * j) = t by omega_arith, hAs t (by omega_arith)]
        · rw [ite_eq_right (off_sub_not B (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith))]
          exact hi.copied t (by omega_arith)
    · have hout : ∀ e, e + 8 ≤ 16 * c → ¬ (x - (B + BitVec.ofNat 64 e)).toNat < 8 := fun e he h =>
        hx _ (List.mem_singleton_self _) (VG.Offset.sub_base B he _ (by simp only [Region.Contains]; omega_arith))
      rw [hm, writeW_readW_apply, ite_eq_right (hout _ (by omega_arith)), hm₁, writeW_readW_apply,
        ite_eq_right (hout _ (by omega_arith))]
    · rw [o₅ r h3, o₄ r h2, o₃ r h1, g₂ r h4 h5 h6, g₁ r h4 h5 h6, hi.regs r h1 h2 h3 h4 h5 h6]
  have hz : (s₅.gpr .t5 == 0) = decide (c - (j + 1) = 0) := by
    rw [hc₅, show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, Bool.eq_iff_iff, beq_iff_eq,
      decide_eq_true_iff]
    constructor
    · intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega_arith
    · intro h; rw [h]
  by_cases hl : j + 1 = c
  · refine .inl ⟨(eval_nonzero s₅ .t5).trans (by rw [hz]; simp; omega_arith),
      by rw [show j + 1 = c from hl] at hinv; exact hinv⟩
  · exact .inr ⟨(eval_nonzero s₅ .t5).trans (by rw [hz]; simp; omega_arith), c - (j + 1), by omega_arith, j + 1, rfl,
      by omega_arith, hinv⟩

theorem copyInBlocks_wp {A B : Addr} {c : Nat} {s₀ : State} (hB8 : B.toNat % 8 = 0) (hc : 0 < c) (hc8 : c ≤ 8)
    (hA : ∀ t < 2 * c, InRegions (s₀.rd ++ s₀.wr) (A + BitVec.ofNat 64 (8 * t)) 8)
    (hB : ∀ t < 2 * c, InRegions s₀.wr (B + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨A, 16 * c⟩ ⟨B, 16 * c⟩) (hs : CopyInv A B c s₀ 0 s₀) :
    WP isa copyInBlocks s₀ (CopyInv A B c s₀ c) := by
  rw [copyInBlocks_eq]; exact copyLoop_wp (copyIn_word hB8) hc (by omega) hA hB hsep hs

theorem copyOutBlocks_wp {A B : Addr} {c : Nat} {s₀ : State} (hA8 : A.toNat % 8 = 0) (hc : 0 < c) (hc8 : c ≤ 8)
    (hA : ∀ t < 2 * c, InRegions (s₀.rd ++ s₀.wr) (A + BitVec.ofNat 64 (8 * t)) 8)
    (hB : ∀ t < 2 * c, InRegions s₀.wr (B + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨A, 16 * c⟩ ⟨B, 16 * c⟩) (hs : CopyInv A B c s₀ 0 s₀) :
    WP isa copyOutBlocks s₀ (CopyInv A B c s₀ c) := by
  rw [copyOutBlocks_eq]; exact copyLoop_wp (copyOut_word hA8) hc (by omega) hA hB hsep hs

end VG.Proof.Camellia.RISCV64
