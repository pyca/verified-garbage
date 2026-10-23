module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Key.Load
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Word
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Write
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Key.Permutation
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Key

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

def pack : List Instr := [.lsl .r8 .r0 28, .logic .xor .r8 .r8 .r7]

def tail : List Instr := [.store .d .r9 .r6 0, .addi .r6 .r6 8, .addi .r12 .r12 1, .subi .r8 .r12 16]

theorem pack_ok (s : State) (c d : BitVec 28)
    (hc : s.gpr .r0 = c.setWidth 64) (hd : s.gpr .r7 = d.setWidth 64) :
    ∃ s', runBlock isa pack s = some s' ∧
      (s'.gpr .r8).setWidth 56 = c ++ d ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r8 → s'.gpr r = s.gpr r) := by
  let s₁ := s.write .r8 (s.gpr .r0 <<< 28)
  let s₂ := s₁.write .r8 (s₁.gpr .r8 ^^^ s₁.gpr .r7)
  refine ⟨s₂, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · rw [pack, runBlock_cons, exec_lsl (by decide), runStep_some, runBlock_cons, exec_logic,
      runStep_some, runBlock_nil]
  · simp only [s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false]
    rw [hc, hd]; exact pack28_shift c d
  · intro r hr; simp only [s₂, s₁, gpr_write, hr, ite_false]

theorem nextRound_values : ∀ j < 16,
    BitVec.ofNat 64 j + BitVec.ofNat 64 1 = BitVec.ofNat 64 (j + 1) ∧
    ((BitVec.ofNat 64 j + BitVec.ofNat 64 1 - BitVec.ofNat 64 16) != 0) = decide (j ≠ 15) := by
  decide

theorem tail_ok (s : State) (j : Nat) (hj : j < 16)
    (hc : s.gpr .r12 = BitVec.ofNat 64 j)
    (hw : InRegions s.wr (s.gpr .r6) 8) :
    ∃ s', runBlock isa tail s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .r6) (s.gpr .r9) ∧
      s'.gpr .r6 = s.gpr .r6 + 8 ∧ s'.gpr .r12 = BitVec.ofNat 64 (j + 1) ∧
      isa.eval (.nonzero .d .r8) s' = some (decide (j ≠ 15)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r8 → r ≠ .r12 → r ≠ .r6 → s'.gpr r = s.gpr r) := by
  have hstore := exec_store_d (s := s) (t := .r9) (n := .r6) (off := 0) (by decide) (by decide)
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hw)
  let s₁ : State := { s with mem := s.mem.writeW (s.gpr .r6 + BitVec.ofNat 64 0) (s.gpr .r9) }
  let s₂ := s₁.write .r6 (s₁.gpr .r6 + BitVec.ofNat 64 8)
  let s₃ := s₂.write .r12 (s₂.gpr .r12 + BitVec.ofNat 64 1)
  let s₄ := s₃.write .r8 (s₃.gpr .r12 - BitVec.ofNat 64 16)
  have h12 : s₃.gpr .r12 = BitVec.ofNat 64 (j + 1) := by
    simp only [s₃, s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false]
    rw [hc]; exact (nextRound_values j hj).1
  refine ⟨s₄, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
  · rw [tail, runBlock_cons, hstore, runStep_some, runBlock_cons, exec_addi (by decide) (by decide),
      runStep_some, runBlock_cons, exec_addi (by decide) (by decide), runStep_some, runBlock_cons,
      exec_subi (by decide) (by decide), runStep_some, runBlock_nil]
  · change s.mem.writeW (s.gpr .r6 + BitVec.ofNat 64 0) (s.gpr .r9) = _
    rw [BitVec.add_zero]
  · simp only [s₄, s₃, s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false]; rfl
  · simp only [s₄, gpr_write, reduceCtorEq, ite_false]; exact h12
  · change VG.PPC64LE.eval (.nonzero .d .r8) s₄ = _
    simp only [VG.PPC64LE.eval, State.read, Size.bits, BitVec.setWidth_eq, s₄, gpr_write_self]
    rw [h12, ← (nextRound_values j hj).1]
    exact congrArg some (nextRound_values j hj).2
  · intro r h8 h12 h6
    simp only [s₄, s₃, s₂, s₁, gpr_write, h8, h12, h6, ite_false]

structure StorePost (c d : BitVec 28) (j : Nat) (s s' : State) : Prop where
  mem : s'.mem = s.mem.writeW (s.gpr .r6) ((Spec.TripleDes.permute Spec.TripleDes.pc2 (c ++ d)).setWidth 64)
  ptr : s'.gpr .r6 = s.gpr .r6 + 8
  counter : s'.gpr .r12 = BitVec.ofNat 64 (j + 1)
  flag : isa.eval (.nonzero .d .r8) s' = some (decide (j ≠ 15))
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r ∈ (keyKept ++ [.r0, .r7]), s'.gpr r = s.gpr r

theorem storeRound_ok (s : State) (c d : BitVec 28) (j : Nat) (hj : j < 16)
    (hc : s.gpr .r0 = c.setWidth 64) (hd : s.gpr .r7 = d.setWidth 64)
    (hjreg : s.gpr .r12 = BitVec.ofNat 64 j) (hw : InRegions s.wr (s.gpr .r6) 8) :
    WP isa (.block Impl.TripleDes.PPC64LE.Key.storeRound) s (StorePost c d j s) := by
  have code : Impl.TripleDes.PPC64LE.Key.storeRound =
      (pack ++ permuteCode Spec.TripleDes.pc2 56 .r9 .r8 .r10 .r11) ++ tail := rfl
  rw [code, WP.block_append_iff, WP.block_append_iff]
  obtain ⟨s₁, run₁, word₁, mem₁, rd₁, wr₁, reg₁⟩ := pack_ok s c d hc hd
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, word₂, rd₂, wr₂, mem₂, reg₂⟩ := pc2_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [word₁] at word₂
  have checks : ∀ r ∈ (keyKept ++ [.r0, .r7, .r12, .r6]),
      ((instrs keyPermutation2.lit).all fun op => dstOf op != some r) = true := by decide +kernel
  have keep₂ : ∀ r ∈ (keyKept ++ [.r0, .r7, .r12, .r6]), s₂.gpr r = s.gpr r := by
    intro r hr
    have unused : ∀ r ∈ (keyKept ++ [.r0, .r7, .r12, .r6]), r ≠ .r8 := by decide
    exact (reg₂ r (checks r hr)).trans (reg₁ r (unused r hr))
  have counter₂ := (keep₂ .r12 (by decide)).trans hjreg
  have write₂ : InRegions s₂.wr (s₂.gpr .r6) 8 := by
    rw [wr₂, wr₁, keep₂ .r6 (by decide)]; exact hw
  obtain ⟨s₃, run₃, mem₃, ptr₃, counter₃, flag₃, rd₃, wr₃, reg₃⟩ := tail_ok s₂ j hj counter₂ write₂
  refine WP.of_runBlock ⟨s₃, run₃, ⟨?_, ?_, counter₃, flag₃, rd₃.trans (rd₂.trans rd₁),
    wr₃.trans (wr₂.trans wr₁), ?_⟩⟩
  · rw [mem₃, mem₂, mem₁, keep₂ .r6 (by decide), word₂]
  · rw [ptr₃, keep₂ .r6 (by decide)]
  · intro r hr
    have incl : ∀ r ∈ (keyKept ++ [.r0, .r7]),
        r ≠ .r8 ∧ r ≠ .r12 ∧ r ≠ .r6 ∧ r ∈ (keyKept ++ [.r0, .r7, .r12, .r6]) := by decide
    exact (reg₃ r (incl r hr).1 (incl r hr).2.1 (incl r hr).2.2.1).trans (keep₂ r (incl r hr).2.2.2)

end VG.Proof.TripleDes.PPC64LE.Key
