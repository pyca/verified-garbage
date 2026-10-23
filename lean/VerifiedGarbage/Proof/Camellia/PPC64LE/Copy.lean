module
public import VerifiedGarbage.Impl.Camellia.PPC64LE.Ecb
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem

import VerifiedGarbage.Proof.Camellia.PPC64LE.Keys
import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Copying blocks on PPC64LE

As on x86-64: `copyBlocks_wp`: the loop `copyBlocks` copies `c ≥ 1` blocks
of 16 bytes from `r9` to `r10` (areas that do not overlap), through `t0`,
counting down `r11`, and changes nothing else in memory.
-/

@[expose] public section

namespace VG.Proof.Camellia.PPC64LE

open VG VG.PPC64LE VG.Impl.Camellia.PPC64LE
open VG.Impl.Aes.PPC64LE (t0)

/-- `ldr t0, [r9, #d]; str t0, [r10, #d]`. -/
theorem copyWord_ok (s : State) {d : Nat} (hd : d % 8 = 0 ∧ d < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r9 + BitVec.ofNat 64 d) 8)
    (hw : InRegions s.wr (s.gpr .r10 + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa [.load .d t0 .r9 d, .store .d t0 .r10 d] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .r10 + BitVec.ofNat 64 d) (s.mem.readW (s.gpr .r9 + BitVec.ofNat 64 d) 64) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let v := s.mem.readW (s.gpr .r9 + BitVec.ofNat 64 d) 64
  let s₁ := s.write t0 v
  have h15 : s₁.gpr .r10 = s.gpr .r10 := RegUpd.gpr_write_of_ne _ _ (by decide)
  have ht : s₁.gpr t0 = v := RegUpd.gpr_write_self _ _ _
  refine ⟨{ s₁ with mem := s₁.mem.writeW (s₁.gpr .r10 + BitVec.ofNat 64 d) (s₁.gpr t0) }, ?_, ?_,
    fun r hr => RegUpd.gpr_write_of_ne _ _ hr, rfl, rfl⟩
  · have e1 : runBlock isa [.load .d t0 .r9 d] s = some s₁ := by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec_ld hd hr]; rfl
    have e2 : runBlock isa [.store .d t0 .r10 d] s₁ =
        some { s₁ with mem := s₁.mem.writeW (s₁.gpr .r10 + BitVec.ofNat 64 d) (s₁.gpr t0) } := by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec_std hd (by rw [h15]; exact hw)]
    rw [show ([.load .d t0 .r9 d, .store .d t0 .r10 d] : List Instr) =
      [.load .d t0 .r9 d] ++ [.store .d t0 .r10 d] from rfl, runBlock_append', e1, Option.bind_some, e2]
  · show s.mem.writeW (s₁.gpr .r10 + BitVec.ofNat 64 d) (s₁.gpr t0) = _
    rw [h15, ht]

/-- Copying, after `j` of `c` blocks. -/
structure CopyInv (A B : Addr) (c : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  src : s.gpr .r9 = A + BitVec.ofNat 64 (16 * j)
  dst : s.gpr .r10 = B + BitVec.ofNat 64 (16 * j)
  cnt : s.gpr .r11 = BitVec.ofNat 64 (c - j)
  copied : ∀ t < 16 * j, s.mem (B + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t)
  frame : Frame [⟨B, 16 * c⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ t0 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem copyBlocks_bounded_wp {A B : Addr} {c : Nat} {s₀ : State} (hc : 0 < c) (hcBound : c ≤ 17)
    (hA : ∀ t < 2 * c, InRegions (s₀.rd ++ s₀.wr) (A + BitVec.ofNat 64 (8 * t)) 8)
    (hB : ∀ t < 2 * c, InRegions s₀.wr (B + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨A, 16 * c⟩ ⟨B, 16 * c⟩) (hs : CopyInv A B c s₀ 0 s₀) :
    WP isa copyBlocks s₀ (CopyInv A B c s₀ c) := by
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
  obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := copyWord_ok s (d := 0) (by decide)
    (by rw [hi.rd, hi.wr, hi.src, addr_add, show 16 * j + 0 = 8 * (2 * j) by omega_arith]; exact hA0)
    (by rw [hi.wr, hi.dst, addr_add, show 16 * j + 0 = 8 * (2 * j) by omega_arith]; exact hB0)
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := copyWord_ok s₁ (d := 8) (by decide)
    (by rw [rd₁, wr₁, hi.rd, hi.wr, g₁ _ (by decide), hi.src, addr_add,
      show 16 * j + 8 = 8 * (2 * j + 1) by omega_arith]; exact hA1)
    (by rw [wr₁, hi.wr, g₁ _ (by decide), hi.dst, addr_add, show 16 * j + 8 = 8 * (2 * j + 1) by omega_arith]; exact hB1)
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := addI_ok s₂ .r9 .r9 (imm := 16) (by decide)
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := addI_ok s₃ .r10 .r10 (imm := 16) (by decide)
  obtain ⟨s₅, e₅, c₅, o₅, m₅, rd₅, wr₅⟩ := subI_ok s₄ .r11 .r11 (imm := 1) (by decide)
  refine WP.of_runBlock ⟨s₅, by
    rw [show ([Instr.load .d t0 .r9 0, .store .d t0 .r10 0, .load .d t0 .r9 8, .store .d t0 .r10 8,
      .addi .r9 .r9 16, .addi .r10 .r10 16, .subi .r11 .r11 1] : List Instr) =
      [.load .d t0 .r9 0, .store .d t0 .r10 0] ++ ([.load .d t0 .r9 8, .store .d t0 .r10 8] ++
      ([.addi .r9 .r9 16] ++ ([.addi .r10 .r10 16] ++ [.subi .r11 .r11 1]))) from rfl,
      runBlock_append', e₁, Option.bind_some, runBlock_append', e₂, Option.bind_some, runBlock_append', e₃,
      Option.bind_some, runBlock_append', e₄, Option.bind_some, e₅], ?_⟩
  have hn : 16 * c < 2 ^ 64 := by omega_arith
  have r1 : s₁.gpr .r10 = B + BitVec.ofNat 64 (16 * j) := by rw [g₁ _ (by decide), hi.dst]
  have a1 : s₁.gpr .r9 = A + BitVec.ofNat 64 (16 * j) := by rw [g₁ _ (by decide), hi.src]
  have hm : s₅.mem = (s₁.mem.writeW (B + BitVec.ofNat 64 (16 * j + 8))
      (s₁.mem.readW (A + BitVec.ofNat 64 (16 * j + 8)) 64)) := by
    rw [m₅, m₄, m₃, m₂, r1, a1, addr_add, addr_add]
  have hm₁ : s₁.mem = s.mem.writeW (B + BitVec.ofNat 64 (16 * j))
      (s.mem.readW (A + BitVec.ofNat 64 (16 * j)) 64) := by
    rw [m₁, hi.dst, hi.src, addr_add, addr_add, Nat.add_zero]
  -- `s₁` and `s` agree on `A`'s area.
  have hA₁ : ∀ t < 16 * c, s₁.mem (A + BitVec.ofNat 64 t) = s.mem (A + BitVec.ofNat 64 t) := fun t ht => by
    rw [hm₁, writeW_readW_apply, ite_eq_right (not_in_of_disjoint hsep ht (by omega_arith) hn)]
  have hc₅ : s₅.gpr .r11 = BitVec.ofNat 64 (c - (j + 1)) := by
    rw [c₅, o₄ _ (by decide), o₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hi.cnt,
      VG.Offset.ofNat_sub_ofNat (by omega_arith), show c - j - 1 = c - (j + 1) by omega_arith]
  have hinv : CopyInv A B c s₀ (j + 1) s₅ := by
    refine ⟨?_, ?_, hc₅, fun t ht => ?_, hi.frame.trans fun x hx => ?_, fun r h1 h2 h3 h4 => ?_,
      by rw [rd₅, rd₄, rd₃, rd₂, rd₁, hi.rd], by rw [wr₅, wr₄, wr₃, wr₂, wr₁, hi.wr]⟩
    · rw [o₅ _ (by decide), o₄ _ (by decide), a₃, g₂ _ (by decide), a1, addr_add,
        show 16 * j + 16 = 16 * (j + 1) by omega_arith]
    · rw [o₅ _ (by decide), a₄, o₃ _ (by decide), g₂ _ (by decide), r1, addr_add,
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
    · rw [o₅ r h3, o₄ r h2, o₃ r h1, g₂ r h4, g₁ r h4, hi.regs r h1 h2 h3 h4]
  have hz : (s₅.gpr .r11 == 0) = decide (c - (j + 1) = 0) := by
    rw [hc₅, show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, Bool.eq_iff_iff, beq_iff_eq,
      decide_eq_true_iff]
    constructor
    · intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega_arith
    · intro h; rw [h]
  by_cases hl : j + 1 = c
  · refine .inl ⟨(eval_nonzero s₅ .r11).trans (by rw [hz]; simp; omega_arith),
      by rw [show j + 1 = c from hl] at hinv; exact hinv⟩
  · exact .inr ⟨(eval_nonzero s₅ .r11).trans (by rw [hz]; simp; omega_arith), c - (j + 1), by omega_arith, j + 1, rfl,
      by omega_arith, hinv⟩

/-- The original eight-block interface used by the parallel block modes. -/
theorem copyBlocks_wp {A B : Addr} {c : Nat} {s₀ : State} (hc : 0 < c) (hc8 : c ≤ 8)
    (hA : ∀ t < 2*c, InRegions (s₀.rd ++ s₀.wr) (A+BitVec.ofNat 64 (8*t)) 8)
    (hB : ∀ t < 2*c, InRegions s₀.wr (B+BitVec.ofNat 64 (8*t)) 8)
    (hsep : Region.Disjoint ⟨A,16*c⟩ ⟨B,16*c⟩) (hs : CopyInv A B c s₀ 0 s₀) :
    WP isa copyBlocks s₀ (CopyInv A B c s₀ c) :=
  copyBlocks_bounded_wp hc (by omega) hA hB hsep hs

end VG.Proof.Camellia.PPC64LE
