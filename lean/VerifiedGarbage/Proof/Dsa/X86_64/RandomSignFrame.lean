module

public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Impl.Dsa.X86_64.RandomSign
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
import Mathlib.Tactic.Push
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Spec.Dsa.RandomSign
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.Dsa.SignContractWith
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlKem.X86_64.Wp

/-! ### `Dsa.X86_64.RandomSignABI`, which this module and modules that import it used -/

section

/-! The randomized-signing ABI, including the wrapper and callee stack allowance. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64

theorem stackArgs_seven (s : State) : List.map (stackArg s) (List.range 7) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6] := rfl

structure RandomSignABI (extra : Nat) (s : State) : Prop where
  stackLower : extra + 256 ≤ (s.gpr .rsp).toNat
  stackUpper : (s.gpr .rsp).toNat + 64 ≤ 2 ^ 64
  rd : s.rd = [⟨s.gpr .rcx, (s.gpr .r8).toNat⟩, ⟨stackArg s 1, (stackArg s 2).toNat⟩, ⟨stackArg s 3, (stackArg s 4).toNat⟩, ⟨stackArgAddr s 0, 56⟩]
  wr : s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.gpr .rdx, 8⟩, ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩]
  outUsed : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rdx, 8⟩
  outKey : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  outDigest : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩
  outRand : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat⟩
  outScratch : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩
  outArgs : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArgAddr s 0, 56⟩
  usedKey : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  usedDigest : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩
  usedRand : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat⟩
  usedScratch : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩
  usedArgs : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 56⟩
  keyScratch : (⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩
  digestScratch : (⟨stackArg s 1, (stackArg s 2).toNat⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩
  randScratch : (⟨stackArg s 3, (stackArg s 4).toNat⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩
  scratchArgs : (⟨stackArg s 5, (stackArg s 6).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 56⟩
  retOut : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  stackOut : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  retUsed : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, 8⟩
  stackUsed : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨s.gpr .rdx, 8⟩
  retKey : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  stackKey : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  retDigest : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩
  stackDigest : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩
  retRand : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat⟩
  stackRand : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat⟩
  retScratch : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩
  stackScratch : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩
  retArgs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 56⟩
  stackArgs : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨stackArgAddr s 0, 56⟩
  outBound : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).base.toNat + (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).len ≤ 2 ^ 64
  usedBound : (⟨s.gpr .rdx, 8⟩ : Region).base.toNat + (⟨s.gpr .rdx, 8⟩ : Region).len ≤ 2 ^ 64
  keyBound : (⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ : Region).base.toNat + (⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ : Region).len ≤ 2 ^ 64
  digestBound : (⟨stackArg s 1, (stackArg s 2).toNat⟩ : Region).base.toNat + (⟨stackArg s 1, (stackArg s 2).toNat⟩ : Region).len ≤ 2 ^ 64
  randBound : (⟨stackArg s 3, (stackArg s 4).toNat⟩ : Region).base.toNat + (⟨stackArg s 3, (stackArg s 4).toNat⟩ : Region).len ≤ 2 ^ 64
  scratchBound : (⟨stackArg s 5, (stackArg s 6).toNat * 8⟩ : Region).base.toNat + (⟨stackArg s 5, (stackArg s 6).toNat * 8⟩ : Region).len ≤ 2 ^ 64
  lengths : Spec.Dsa.lengthsValid (s.gpr .r9).toNat (stackArg s 0).toNat
  outLength : (s.gpr .rsi).toNat = 2 * (stackArg s 0).toNat
  keyLength : (s.gpr .r8).toNat = 3 * (s.gpr .r9).toNat + 2 * (stackArg s 0).toNat
  scratchLength : Spec.Dsa.randomSignScratchWords (s.gpr .r9).toNat ≤ (stackArg s 6).toNat

theorem randomSignABI_of {extra : Nat} {s : State}
    (h : (randomSignCheckedContract abi (extra + 256)).pre s) : RandomSignABI extra s := by
  sig_pre [randomSignCheckedContract, Spec.Dsa.randomSignSig, abi, argRegs, stackArgs_seven,
    show extra + 256 = (extra + 255) + 1 from rfl, List.range, List.range.loop] at h
  sig_pre [randomSignCheckedContract, Spec.Dsa.randomSignSig, abi, argRegs, stackArgs_seven, List.range, List.range.loop] at h
  sig_split h
  constructor <;> with_reducible assumption

end VG.Proof.Dsa.X86_64

end

end

/-! Allocate the wrapper frame and locate the incoming stack arguments. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

def randomBase (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 Random.frameBytes

def randomFreed (s : State) : State :=
  { s.setReg .rsp (s.gpr .rsp + BitVec.ofNat 64 Random.frameBytes) with wr := s.wr.tail }

theorem randomBase_toNat {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    (randomBase s).toNat = (s.gpr .rsp).toNat - Random.frameBytes := by
  have hl := h.stackLower
  simp only [randomBase, BitVec.toNat_sub, BitVec.toNat_ofNat, Random.frameBytes]
  have hb := (s.gpr .rsp).isLt
  omega_using [hl]

theorem random_frame_sub {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    Region.Sub ⟨randomBase s, Random.frameBytes⟩ (below (s.gpr .rsp) (extra + 256)) := by
  apply below_sub (by unfold Random.frameBytes; omega_using [])
  have hl := h.stackLower
  have hb := (s.gpr .rsp).isLt
  omega_using [hl]

theorem random_alloc_scr {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    Scr (allocState Random.frameBytes s) (randomBase s) Random.frameBytes := by
  apply Scr.of_mem (List.mem_cons_self ..)
  rw [randomBase_toNat h]
  have hb := (s.gpr .rsp).isLt
  unfold Random.frameBytes
  omega_using []

theorem random_incoming_address (s : State) (j : Nat) :
    off (randomBase s) (256 + 8 * j) = stackArgAddr s j := by
  change s.gpr .rsp - BitVec.ofNat 64 248 + BitVec.ofNat 64 (256 + 8 * j) = _
  rw [show 256 + 8 * j = 248 + 8 * (j + 1) by omega_using [], BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rfl

theorem random_incoming_read {extra : Nat} {s : State} (h : RandomSignABI extra s)
    (p : Nat × Nat) (hp : p ∈ RandomSign.incomingSlots) :
    InRegions ((allocState Random.frameBytes s).rd ++ (allocState Random.frameBytes s).wr)
      (off (randomBase s) p.1) 8 := by
  have hj (j : Nat) (hj : j < 7) :
      InRegions ((allocState Random.frameBytes s).rd ++ (allocState Random.frameBytes s).wr)
        (off (randomBase s) (256 + 8 * j)) 8 := by
    rw [random_incoming_address]
    refine ⟨⟨stackArgAddr s 0, 56⟩, List.mem_append_left _ ?_, ?_⟩
    · change _ ∈ s.rd
      rw [h.rd]
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_true]
    · simp only [stackArgAddr]
      exact Offset.contains _ (d := 8 * (j + 1)) (n := 8) (e := 8) (k := 56)
        (by omega_using []) (by omega_using [hj]) (by decide)
  simp only [RandomSign.incomingSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hj 0 (by decide)
  · exact hj 1 (by decide)
  · exact hj 2 (by decide)
  · exact hj 3 (by decide)
  · exact hj 4 (by decide)
  · exact hj 5 (by decide)
  · exact hj 6 (by decide)

theorem random_frame_ok {extra : Nat} {s : State} (h : RandomSignABI extra s)
    {body : Prog isa} {Q : State → Prop}
    (hb : WP isa body (allocState Random.frameBytes s) fun t =>
      t.gpr .rsp = randomBase s ∧ t.wr = (allocState Random.frameBytes s).wr ∧ Q (randomFreed t)) :
    WP isa (.frame (.alloc Random.frameBytes) body (.free Random.frameBytes)) s Q := by
  obtain ⟨trace, t, he, htsp, htwr, hq⟩ := hb
  have hl := h.stackLower
  have ha : isa.push (.alloc Random.frameBytes) s = some (allocState Random.frameBytes s) := by
    simp only [isa, push, allocState]
    exact ite_eq_left ⟨by decide, by decide, by decide, by unfold Random.frameBytes; omega_using [hl]⟩
  have hf : isa.pop (.free Random.frameBytes) (allocState Random.frameBytes s) t = some (randomFreed t) := by
    simp only [isa, pop]
    exact ite_eq_left ⟨by decide, by decide, by decide, htsp, htwr, rfl⟩
  exact ⟨_, _, Exec.frame ha he hf, hq⟩

end VG.Proof.Dsa.X86_64
