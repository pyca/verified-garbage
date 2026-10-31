module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Groups
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: loading a batch is independent of the cipher's direction and its stores.
/-! # POWER8 AES batch inputs -/

@[expose] public section
namespace VG.Proof.Aes.PPC64LE.Crypto
open VG VG.PPC64LE
open VG.Impl.Aes.PPC64LE.Crypto (breg batchRegs mask byteMask counterBase counterWord counterMask counterControl key data)

theorem batchRegs_succ (n : Nat) : batchRegs (n+1) = batchRegs n ++ [breg n] := by
  rw [batchRegs, List.range_succ, List.map_append, List.map_singleton]
  rfl

theorem batchFacts : ∀ n : Fin 9,
    (batchRegs n).Nodup ∧ key ∉ batchRegs n ∧ mask ∉ batchRegs n ∧ counterBase ∉ batchRegs n ∧
      counterMask ∉ batchRegs n ∧ counterWord ∉ batchRegs n ∧ data ∉ batchRegs n := by decide

theorem breg_injective {i j : Nat} (hi : i < 8) (hj : j < 8) (he : breg i = breg j) : i = j := by
  have h : ∀ i j : Fin 8, breg i = breg j → i.val = j.val := by decide
  exact h ⟨i, hi⟩ ⟨j, hj⟩ he

theorem breg_mem {i n : Nat} (hi : i < n) : breg i ∈ batchRegs n :=
  List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

theorem breg_ne {i j : Nat} (hi : i < 8) (hj : j < 8) (hn : i ≠ j) : breg i ≠ breg j :=
  fun he => hn (breg_injective hi hj he)

def readValue (ctr : Bool) (s : State) (i : Nat) : BitVec 128 :=
  if ctr then (s.vpr counterBase).extractLsb' 32 96 ++ (s.gpr .r8 + BitVec.ofNat 64 i).extractLsb' 0 32
  else rev128 (s.mem.read (s.gpr .r6 + BitVec.ofNat 64 (16*i)) 16)

structure ReadInv (ctr : Bool) (s₀ : State) (k : Nat) (s : State) : Prop where
  effects : Local [.r6, .r8] (counterWord :: batchRegs k) s₀ s
  ptr : s.gpr .r6 = if ctr then s₀.gpr .r6 else s₀.gpr .r6 + BitVec.ofNat 64 (16*k)
  counter : s.gpr .r8 = if ctr then s₀.gpr .r8 + BitVec.ofNat 64 k else s₀.gpr .r8
  val : ∀ i < k, s.vpr (breg i) = readValue ctr s₀ i

theorem read_step (ctr : Bool) {N k : Nat} (hN : N ≤ 8) (hk : k < N) {s₀ s : State}
    (h0 : s₀.gpr .r0 = 0) (hm : s₀.vpr mask = byteMask)
    (hc : ctr = true → s₀.vpr counterMask = counterControl)
    (hr : ∀ i < N, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .r6 + BitVec.ofNat 64 (16*i)) 16)
    (h : ReadInv ctr s₀ k s) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.readBlock ctr (breg k))) s (ReadInv ctr s₀ (k+1)) := by
  have hkn : k < 8 := by omega
  have facts := batchFacts ⟨k, by omega⟩
  have all := batchFacts ⟨8, by decide⟩
  have hbm : breg k ≠ mask := fun he => all.2.2.1 (he ▸ breg_mem hkn)
  have hzm : s.gpr .r0 = 0 := (h.effects.keep.gpr (by decide)).trans h0
  have hmm : s.vpr mask = byteMask := (h.effects.v mask (by simp [facts.2.2.1])).trans hm
  have hcc : ctr = true → s.vpr counterMask = counterControl := by
    intro he
    rw [h.effects.v counterMask (by simp [facts.2.2.2.2.1])]
    exact hc he
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r6) 16 := by
    rw [h.effects.keep.2.1, h.effects.keep.2.2, h.ptr]
    cases ctr
    · simpa only [Bool.false_eq_true, ite_false] using hr k hk
    · simpa only [ite_true, Nat.mul_zero, BitVec.add_zero] using hr 0 (by omega)
  refine WP.mono (readBlock_ok ctr (breg k) s hbm hzm hmm hcc hin) fun t ⟨hv, hg6, hg8, hf⟩ => ?_
  have hnval : t.vpr (breg k) = readValue ctr s₀ k := by
    rw [hv]
    cases ctr
    · simp only [inputVector, readValue, Bool.false_eq_true, ite_false, h.effects.mem, h.ptr]
    · simp only [inputVector, readValue, ite_true, h.counter]
      rw [h.effects.v counterBase (by simp [facts.2.2.2.1])]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (h.effects.trans hf).weaken (by simp)
      (by simp [batchRegs_succ, or_left_comm, or_comm])
  · rw [hg6, h.ptr]
    cases ctr
    · simp only [Bool.false_eq_true, ite_false]
      change s₀.gpr .r6 + BitVec.ofNat 64 (16*k) + BitVec.ofNat 64 16 = _
      rw [Offset.add_add]
      exact congrArg (fun n => s₀.gpr .r6 + BitVec.ofNat 64 n) (by omega)
    · simp only [ite_true]
  · rw [hg8, h.counter]
    cases ctr
    · simp only [Bool.false_eq_true, ite_false]
    · simp only [ite_true]
      exact Offset.add_ofNat_add_one (s₀.gpr .r8) k
  · intro i hi
    by_cases he : i = k
    · subst i
      exact hnval
    · have hik : i < k := by omega
      have hi8 : i < 8 := by omega
      have hbiw : breg i ≠ counterWord := fun he => all.2.2.2.2.2.1 (he ▸ breg_mem hi8)
      rw [hf.v (breg i) (by simp [breg_ne hi8 hkn he, hbiw])]
      exact h.val i hik

theorem read_ok (ctr : Bool) {N : Nat} (hN : N ≤ 8) (s : State)
    (h0 : s.gpr .r0 = 0) (hm : s.vpr mask = byteMask)
    (hc : ctr = true → s.vpr counterMask = counterControl)
    (hr : ∀ i < N, InRegions (s.rd ++ s.wr) (s.gpr .r6 + BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block ((batchRegs N).flatMap (Impl.Aes.PPC64LE.Crypto.readBlock ctr))) s (ReadInv ctr s N) := by
  rw [batchRegs, List.flatMap_map]
  refine wp_range_flatMap (M := isa) (ReadInv ctr s)
    (fun k t hk ht => read_step ctr hN hk h0 hm hc hr ht) N (Nat.le_refl _) s ?_
  refine ⟨Local.refl _ _ _, ?_, ?_, fun i hi => by omega⟩ <;> cases ctr <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, Nat.mul_zero, BitVec.add_zero]

end VG.Proof.Aes.PPC64LE.Crypto
