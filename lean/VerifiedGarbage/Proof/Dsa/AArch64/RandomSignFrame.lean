module

public import VerifiedGarbage.Impl.Dsa.AArch64.RandomSign
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Dsa.RandomSign
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Dsa.SignContractWith
import VerifiedGarbage.Proof.Framework.Sig

/-! ### `Dsa.AArch64.RandomSignABI`, which this module and modules that import it used -/

section

/-! The randomized-signing ABI, including the wrapper and callee stack allowance. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64

theorem randomSignStackArgs (s : State) : List.map (stackArg s) (List.range 5) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4] := rfl

structure RandomSignABI (extra : Nat) (s : State) : Prop where
  stackLower : extra + 256 ≤ (s.sp).toNat
  stackUpper : s.sp.toNat + 40 ≤ 2 ^ 64
  rd : s.rd = [⟨s.gpr .x3, (s.gpr .x4).toNat⟩, ⟨s.gpr .x7, (stackArg s 0).toNat⟩, ⟨stackArg s 1, (stackArg s 2).toNat⟩, ⟨stackArgAddr s 0, 40⟩]
  wr : s.wr = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩, ⟨s.gpr .x2, 8⟩, ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩]
  outUsed : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨s.gpr .x2, 8⟩
  outKey : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  outDigest : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨s.gpr .x7, (stackArg s 0).toNat⟩
  outRand : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩
  outScratch : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  outArgs : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨stackArgAddr s 0, 40⟩
  usedKey : (⟨s.gpr .x2, 8⟩ : Region).Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  usedDigest : (⟨s.gpr .x2, 8⟩ : Region).Disjoint ⟨s.gpr .x7, (stackArg s 0).toNat⟩
  usedRand : (⟨s.gpr .x2, 8⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩
  usedScratch : (⟨s.gpr .x2, 8⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  usedArgs : (⟨s.gpr .x2, 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 40⟩
  keyScratch : (⟨s.gpr .x3, (s.gpr .x4).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  digestScratch : (⟨s.gpr .x7, (stackArg s 0).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  randScratch : (⟨stackArg s 1, (stackArg s 2).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  scratchArgs : (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 40⟩
  stackOut : (below (s.sp) (extra + 256)).Disjoint ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
  stackUsed : (below (s.sp) (extra + 256)).Disjoint ⟨s.gpr .x2, 8⟩
  stackKey : (below (s.sp) (extra + 256)).Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  stackDigest : (below (s.sp) (extra + 256)).Disjoint ⟨s.gpr .x7, (stackArg s 0).toNat⟩
  stackRand : (below (s.sp) (extra + 256)).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩
  stackScratch : (below (s.sp) (extra + 256)).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  stackArgs : (below (s.sp) (extra + 256)).Disjoint ⟨stackArgAddr s 0, 40⟩
  outBound : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).base.toNat + (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).len ≤ 2 ^ 64
  usedBound : (⟨s.gpr .x2, 8⟩ : Region).base.toNat + (⟨s.gpr .x2, 8⟩ : Region).len ≤ 2 ^ 64
  keyBound : (⟨s.gpr .x3, (s.gpr .x4).toNat⟩ : Region).base.toNat + (⟨s.gpr .x3, (s.gpr .x4).toNat⟩ : Region).len ≤ 2 ^ 64
  digestBound : (⟨s.gpr .x7, (stackArg s 0).toNat⟩ : Region).base.toNat + (⟨s.gpr .x7, (stackArg s 0).toNat⟩ : Region).len ≤ 2 ^ 64
  randBound : (⟨stackArg s 1, (stackArg s 2).toNat⟩ : Region).base.toNat + (⟨stackArg s 1, (stackArg s 2).toNat⟩ : Region).len ≤ 2 ^ 64
  scratchBound : (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region).base.toNat + (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region).len ≤ 2 ^ 64
  lengths : Spec.Dsa.lengthsValid (s.gpr .x5).toNat (s.gpr .x6).toNat
  outLength : (s.gpr .x1).toNat = 2 * (s.gpr .x6).toNat
  keyLength : (s.gpr .x4).toNat = 3 * (s.gpr .x5).toNat + 2 * (s.gpr .x6).toNat
  scratchLength : Spec.Dsa.randomSignScratchWords (s.gpr .x5).toNat ≤ (stackArg s 4).toNat

theorem randomSignABI_of {extra : Nat} {s : State}
    (h : (randomSignCheckedContract abi (extra + 256)).pre s) : RandomSignABI extra s := by
  sig_pre [randomSignCheckedContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs,
    show extra + 256 = (extra + 255) + 1 from rfl] at h
  sig_pre [randomSignCheckedContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs] at h
  sig_split h
  constructor <;> with_reducible assumption

end VG.Proof.Dsa.AArch64

end

end

/-! Allocate the wrapper frame and locate the incoming stack arguments. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

def randomBase (s : State) : Addr := s.sp - BitVec.ofNat 64 Random.frameBytes

def randomFreed (s : State) : State :=
  { s with sp := s.sp + BitVec.ofNat 64 Random.frameBytes, wr := s.wr.tail }

theorem randomBase_toNat {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    (randomBase s).toNat = (s.sp).toNat - Random.frameBytes := by
  have hl := h.stackLower
  simp only [randomBase, BitVec.toNat_sub, BitVec.toNat_ofNat, Random.frameBytes]
  have hb := (s.sp).isLt
  omega_using [hl]

theorem random_frame_sub {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    Region.Sub ⟨randomBase s, Random.frameBytes⟩ (below (s.sp) (extra + 256)) := by
  apply below_sub (by unfold Random.frameBytes; omega_using [])
  have hl := h.stackLower
  have hb := (s.sp).isLt
  omega_using [hl]

theorem random_alloc_scr {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    Scr (allocated Random.frameBytes s) (randomBase s) Random.frameBytes := by
  apply Scr.of_mem (List.mem_cons_self ..)
  rw [randomBase_toNat h]
  have hb := (s.sp).isLt
  unfold Random.frameBytes
  omega_using []

theorem random_incoming_address (s : State) (j : Nat) :
    off (randomBase s) (256 + 8 * j) = stackArgAddr s j := by
  change s.sp - BitVec.ofNat 64 256 + BitVec.ofNat 64 (256 + 8 * j) = _
  rw [← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rfl

theorem random_incoming_read {extra : Nat} {s : State} (h : RandomSignABI extra s)
    (p : Nat × Nat) (hp : p ∈ RandomSign.incomingSlots) :
    InRegions ((allocated Random.frameBytes s).rd ++ (allocated Random.frameBytes s).wr)
      (off (randomBase s) p.1) 8 := by
  have hj (j : Nat) (hj : j < 5) :
      InRegions ((allocated Random.frameBytes s).rd ++ (allocated Random.frameBytes s).wr)
        (off (randomBase s) (256 + 8 * j)) 8 := by
    rw [random_incoming_address]
    refine ⟨⟨stackArgAddr s 0, 40⟩, List.mem_append_left _ ?_, ?_⟩
    · change _ ∈ s.rd
      rw [h.rd]
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_true]
    · simp only [stackArgAddr]
      exact Offset.contains _ (d := 8 * j) (n := 8) (e := 0) (k := 40)
        (by omega_using []) (by omega_using [hj]) (by decide)
  simp only [RandomSign.incomingSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact hj 0 (by decide)
  · exact hj 1 (by decide)
  · exact hj 2 (by decide)
  · exact hj 3 (by decide)
  · exact hj 4 (by decide)

theorem random_frame_ok {extra : Nat} {s : State} (h : RandomSignABI extra s)
    {body : Prog isa} {Q : State → Prop}
    (hb : WP isa body (allocated Random.frameBytes s) fun t =>
      t.sp = randomBase s ∧ t.wr = (allocated Random.frameBytes s).wr ∧ Q (randomFreed t)) :
    WP isa (.frame (.alloc Random.frameBytes) body (.free Random.frameBytes)) s Q := by
  obtain ⟨trace, t, he, htsp, htwr, hq⟩ := hb
  have hl := h.stackLower
  have ha : isa.push (.alloc Random.frameBytes) s = some (allocated Random.frameBytes s) := by
    simp only [isa, push, allocated]
    exact ite_eq_left ⟨by decide, by decide, by decide, by unfold Random.frameBytes; omega_using [hl]⟩
  have hf : isa.pop (.free Random.frameBytes) (allocated Random.frameBytes s) t = some (randomFreed t) := by
    simp only [isa, pop]
    exact ite_eq_left ⟨by decide, by decide, by decide, htsp, htwr, rfl⟩
  exact ⟨_, _, Exec.frame ha he hf, hq⟩

end VG.Proof.Dsa.AArch64
