module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.X86.KcInputs
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
public import VerifiedGarbage.Proof.Weierstrass.PointContract

/-! # cdecl resources for the two shared key-validation contracts -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.KeyCheck

def contract (full : Bool) : Contract isa :=
  if full then Spec.Rsa.checkKeyContract abi 20 else Spec.Rsa.checkCrtKeyContract abi 20

def caller (full : Bool) (s : State) : CallGeometry :=
  ⟨full, argumentPointer s (scratchArg full), (arg s (scratchArg full + 1)).toNat * 8,
    Spec.Rsa.modulusWords (arg s 1).toNat, arg s⟩

def inputCount (full : Bool) : Nat := if full then 8 else 7

def inputRegions (full : Bool) (s : State) : List Region :=
  (List.range (inputCount full)).map fun i => (caller full s).buffer (2 * i)

structure Layout (full : Bool) (s : State) : Prop where
  stackLow : 20 ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 4 + 4 * (scratchArg full + 2) ≤ 2 ^ 32
  rd : s.rd = inputRegions full s
  wr : s.wr = [⟨(caller full s).base, (caller full s).size⟩,
    ⟨argAddr s 0, 4 * (scratchArg full + 2)⟩]
  scratchBound : (arg s (scratchArg full)).toNat + (caller full s).size ≤ 2 ^ 32
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - 20#64, 20⟩ : Region).Disjoint
    ⟨(caller full s).base, (caller full s).size⟩
  argsApart : (⟨argAddr s 0, 4 * (scratchArg full + 2)⟩ : Region).Disjoint
    ⟨(caller full s).base, (caller full s).size⟩
  retApart : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint
    ⟨(caller full s).base, (caller full s).size⟩
  inApart : ∀ r ∈ s.rd, r.Disjoint ⟨(caller full s).base, (caller full s).size⟩

structure Sizes (full : Bool) (s : State) : Prop where
  inputBounds : ∀ i, i < inputCount full → (arg s (2 * i)).toNat + (arg s (2 * i + 1)).toNat ≤ 2 ^ 32
  ePositive : 1 ≤ (arg s 3).toNat
  eBound : (arg s 3).toNat ≤ (arg s 1).toNat
  dPositive : 1 ≤ (arg s (if full then 5 else 3)).toNat
  dBound : (arg s (if full then 5 else 3)).toNat ≤ (arg s 1).toNat
  pPositive : 1 ≤ (arg s (if full then 7 else 5)).toNat
  qPositive : 1 ≤ (arg s (if full then 9 else 7)).toNat
  lengths : Spec.Rsa.lenValid (arg s 1).toNat
  pSmall : (arg s (if full then 7 else 5)).toNat < (arg s 1).toNat
  qSmall : (arg s (if full then 9 else 7)).toNat < (arg s 1).toNat
  dpLen : (arg s (if full then 11 else 9)).toNat = (arg s (if full then 7 else 5)).toNat
  dqLen : (arg s (if full then 13 else 11)).toNat = (arg s (if full then 9 else 7)).toNat
  qiLen : (arg s (if full then 15 else 13)).toNat = (arg s (if full then 7 else 5)).toNat
  scratchLength : Spec.Rsa.scratchWords (arg s 1).toNat ≤ (arg s (scratchArg full + 1)).toNat

structure ABI (full : Bool) (s : State) : Prop extends Layout full s, Sizes full s

private theorem all_seven {P : Nat → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3)
    (h4 : P 4) (h5 : P 5) (h6 : P 6) : ∀ i, i < 7 → P i := by
  intro i hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

private theorem all_eight {P : Nat → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3)
    (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) : ∀ i, i < 8 → P i := by
  intro i hi
  by_cases e : i = 7
  · subst i; exact h7
  · exact all_seven h0 h1 h2 h3 h4 h5 h6 i (by omega)

theorem abi_crt_layout {s : State} (h : (contract false).pre s) : Layout false s := by
  simp only [contract, Bool.false_eq_true, ite_false] at h
  sig_pre [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, Spec.Rsa.checkCrtKeyContract,
    Spec.Rsa.checkCrtKeySig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  have rd : s.rd = inputRegions false s := by
    dsimp [inputRegions, inputCount, caller, CallGeometry.buffer, byteAddr]
    simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul]
    with_reducible assumption
  have len : Spec.Rsa.lenValid (arg s 1).toNat := by with_reducible assumption
  have lo := len.1
  have hi := len.2
  constructor
  all_goals try rw [rd]
  all_goals try dsimp only [caller, CallGeometry.buffer, byteAddr, scratchArg, inputCount,
    inputRegions]
  all_goals try simp only [Bool.false_eq_true, ite_false, List.range, List.range.loop, List.map,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  all_goals try simp only [Nat.reduceAdd, Nat.reduceMul]
  all_goals repeat' apply And.intro
  all_goals first | with_reducible assumption | rfl | omega |
    exact Region.Disjoint.symm (by with_reducible assumption)


theorem abi_crt_sizes {s : State} (h : (contract false).pre s) : Sizes false s := by
  simp only [contract, Bool.false_eq_true, ite_false] at h
  sig_pre [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, Spec.Rsa.checkCrtKeyContract,
    Spec.Rsa.checkCrtKeySig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  have len : Spec.Rsa.lenValid (arg s 1).toNat := by with_reducible assumption
  have lo := len.1
  have hi := len.2
  constructor
  all_goals try dsimp only [caller, CallGeometry.buffer, byteAddr, scratchArg, inputCount,
    inputRegions]
  all_goals try simp only [Bool.false_eq_true, ite_false]
  all_goals try first
    | refine all_seven ?_ ?_ ?_ ?_ ?_ ?_ ?_
    | refine all_eight ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals try simp only [Nat.reduceAdd, Nat.reduceMul]
  all_goals repeat' apply And.intro
  all_goals first | with_reducible assumption | rfl | omega |
    exact Region.Disjoint.symm (by with_reducible assumption)


theorem abi_crt_of {s : State} (h : (contract false).pre s) : ABI false s :=
  ⟨abi_crt_layout h, abi_crt_sizes h⟩

theorem abi_key_layout {s : State} (h : (contract true).pre s) : Layout true s := by
  simp only [contract, ite_true] at h
  sig_pre [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, Spec.Rsa.checkCrtKeyContract,
    Spec.Rsa.checkCrtKeySig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  have rd : s.rd = inputRegions true s := by
    dsimp [inputRegions, inputCount, caller, CallGeometry.buffer, byteAddr]
    simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul]
    with_reducible assumption
  have len : Spec.Rsa.lenValid (arg s 1).toNat := by with_reducible assumption
  have lo := len.1
  have hi := len.2
  constructor
  all_goals try rw [rd]
  all_goals try dsimp only [caller, CallGeometry.buffer, byteAddr, scratchArg, inputCount,
    inputRegions]
  all_goals try simp only [ite_true, List.range, List.range.loop, List.map,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  all_goals try simp only [Nat.reduceAdd, Nat.reduceMul]
  all_goals repeat' apply And.intro
  all_goals first | with_reducible assumption | rfl | omega |
    exact Region.Disjoint.symm (by with_reducible assumption)


theorem abi_key_sizes {s : State} (h : (contract true).pre s) : Sizes true s := by
  simp only [contract, ite_true] at h
  sig_pre [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, Spec.Rsa.checkCrtKeyContract,
    Spec.Rsa.checkCrtKeySig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  have len : Spec.Rsa.lenValid (arg s 1).toNat := by with_reducible assumption
  have lo := len.1
  have hi := len.2
  constructor
  all_goals try dsimp only [caller, CallGeometry.buffer, byteAddr, scratchArg, inputCount,
    inputRegions]
  all_goals try simp only [ite_true]
  all_goals try first
    | refine all_seven ?_ ?_ ?_ ?_ ?_ ?_ ?_
    | refine all_eight ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals try simp only [Nat.reduceAdd, Nat.reduceMul]
  all_goals repeat' apply And.intro
  all_goals first | with_reducible assumption | rfl | omega |
    exact Region.Disjoint.symm (by with_reducible assumption)


theorem abi_key_of {s : State} (h : (contract true).pre s) : ABI true s :=
  ⟨abi_key_layout h, abi_key_sizes h⟩

theorem abi_of {full : Bool} {s : State} (h : (contract full).pre s) : ABI full s := by
  cases full
  · exact abi_crt_of h
  · exact abi_key_of h
theorem ABI.inputLengths {full : Bool} {s : State} (a : ABI full s) :
    ∀ i, i < inputCount full → 1 ≤ (arg s (2 * i + 1)).toNat ∧
      (arg s (2 * i + 1)).toNat ≤ (arg s 1).toNat := by
  have hn := a.lengths.1
  have he := a.ePositive
  have he' := a.eBound
  have hd := a.dPositive
  have hd' := a.dBound
  have hp := a.pPositive
  have hq := a.qPositive
  have hp' := a.pSmall
  have hq' := a.qSmall
  have hdp := a.dpLen
  have hdq := a.dqLen
  have hqi := a.qiLen
  cases full
  · apply all_seven
    all_goals simp only [Bool.false_eq_true, ite_false] at hp hq hp' hq' hdp hdq hqi
    all_goals simp only [Nat.reduceAdd, Nat.reduceMul]
    all_goals constructor <;> omega
  · apply all_eight
    all_goals simp only [ite_true] at hd hd' hp hq hp' hq' hdp hdq hqi
    all_goals simp only [Nat.reduceAdd, Nat.reduceMul]
    all_goals constructor <;> omega

end VG.Proof.Rsa.X86.KeyCheck
