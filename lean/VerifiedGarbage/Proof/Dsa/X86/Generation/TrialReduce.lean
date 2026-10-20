module
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Trial
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialChunk
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialPrefix
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Trial reduction reads each two-byte chunk once and leaves memory unchanged -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86.Generation

structure TrialInv (s : State) (input : BitVec 32) (count p i : Nat) (t : State) : Prop where
  pointer : t.gpr .ebp = input + BitVec.ofNat 32 (2 * i)
  counter : t.gpr .ecx = BitVec.ofNat 32 (count - i)
  remainder : t.gpr .ebx = BitVec.ofNat 32 (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (input.setWidth 64) (2 * i)) % p)
  mem : t.mem = s.mem
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t

theorem trialReduce_ok {s : State} {input : BitVec 32} {count p : Nat}
    (hp : 1 < p) (pfit : p < 65536) (hc : 1 ≤ count) (hcount : 2 * count < 2 ^ 32)
    (bp : s.gpr .ebp = input) (cx : s.gpr .ecx = BitVec.ofNat 32 count)
    (ps : s.gpr .esi = BitVec.ofNat 32 p) (vi : s.gpr .edi = BitVec.ofNat 32 (2 ^ 32 / p))
    (fit : input.toNat + 2 * count ≤ 2 ^ 32)
    (rd : ∀ i < 2 * count, InRegions (s.rd ++ s.wr) (off (input.setWidth 64) i) 1) :
    WP isa trialReduce s fun t =>
      t.gpr .ebx = BitVec.ofNat 32 (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (input.setWidth 64) (2 * count)) % p) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  unfold trialReduce
  refine WP.seq (wp_movS rfl fun a sa _ => WP.block_nil ?_)
  have I0 : TrialInv s input count p 0 a := by
    refine ⟨?_, ?_, ?_, sa.mem, sa.keeps.mono (by decide)⟩
    · rw [sa.other _ (by decide), bp]; simp only [Nat.mul_zero, BitVec.add_zero]
    · rw [sa.other _ (by decide), cx, Nat.sub_zero]
    · rw [sa.gpr]; rfl
  refine WP.mono (WP.loop (M := isa) (fun k t => ∃ i, k = count - i ∧ i < count ∧ TrialInv s input count p i t)
    ?_ count a ⟨0, rfl, by omega, I0⟩) fun t (I : TrialInv s input count p count t) => ⟨I.remainder, I.mem, I.keeps⟩
  rintro k t ⟨i, rfl, hi, I⟩
  let ptr := input + BitVec.ofNat 32 (2 * i)
  have ptrNat : ptr.toNat = input.toNat + 2 * i := by
    simp only [ptr, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : 2 * i < 2 ^ 32), Nat.mod_eq_of_lt (by omega)]
  have ptrAddr : ptr.setWidth 64 = off (input.setWidth 64) (2 * i) := addr_eq (by omega)
  have step := trialChunk_ok hp pfit (Nat.mod_lt _ (by omega)) (by omega : 1 ≤ count - i) (by omega)
    I.pointer I.remainder I.counter ((I.keeps.1 _ (by decide)).trans ps) ((I.keeps.1 _ (by decide)).trans vi)
    (by change ptr.toNat + 2 ≤ 2 ^ 32; rw [ptrNat]; omega)
    (fun j hj => by
      rw [I.keeps.2.1, I.keeps.2.2]
      change InRegions _ (off (ptr.setWidth 64) j) 1
      rw [ptrAddr, off, off, Offset.add_add]
      exact rd _ (by omega))
  refine WP.mono step fun u ⟨bx, bp', cx', zf, mu, ku⟩ => ?_
  have next : TrialInv s input count p (i + 1) u := by
    refine ⟨?_, ?_, ?_, mu.trans I.mem, I.keeps.trans ku⟩
    · rw [bp', BitVec.add_assoc, ← BitVec.ofNat_add, show 2 * i + 2 = 2 * (i + 1) by omega]
    · rw [cx', Nat.sub_sub]
    · rw [bx, I.mem]
      change BitVec.ofNat 32 ((_ * 65536 + (s.mem (ptr.setWidth 64)).toNat * 256 +
        (s.mem (off (ptr.setWidth 64) 1)).toNat) % p) = _
      rw [ptrAddr, off, off, Offset.add_add]
      rw [trial_prefix_pair, show 2 * i + 2 = 2 * (i + 1) by omega]
  by_cases done : i + 1 = count
  · refine .inl ⟨?_, done ▸ next⟩
    simp only [eval, zf, show count - i = 1 by omega, decide_true, Option.map_some, Bool.not_true]
  · refine .inr ⟨?_, count - (i + 1), by omega, i + 1, rfl, by omega, next⟩
    simp only [eval, zf, show count - i ≠ 1 by omega, decide_false, Option.map_some, Bool.not_false]
end VG.Proof.Dsa.X86.Generation
