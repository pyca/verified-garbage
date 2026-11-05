module

public import VerifiedGarbage.Impl.Dsa.X86_64.ParameterSearch
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillContract
public import VerifiedGarbage.Proof.Framework.X86_64.ForwardCall
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.EntryBranch
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Sig

/-! # The refillable-tape search by the public modulus width, on x86-64

`ParameterSearch.widths` (`Impl/Dsa/X86_64/ParameterSearch.lean`) loads
`state[1]`, the modulus's width, and calls the function for that width,
forwarding its arguments (`Verified.forward`, two of them on the stack): it is
verified against the search's contract from its width functions'
(`Refill.contract`, the search's contract with the width fixed), by choosing
on entry (`Verified.entryBranch`), as `Generation.Widths` does for
`vg_dsa_generate_parameters`. The width functions' stack `S` grows by the
forwarding frame's 56 octets and the call's return address: the search's
contract has `S + 64`.
-/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation.RefillWidths
open VG VG.X86_64
open VG.Spec.Rsa (bytesAt wordsAt)

/-! ## Memory a buffer holds -/

theorem bytesAt_congr {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) : bytesAt m₁ p n = bytesAt m₂ p n := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => h _ ?_
  have hi := List.mem_range.mp hi
  by_cases hw : i < 2 ^ 64
  · exact Offset.contains_base _ (by omega_arith) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega_arith

theorem readW_congr {m₁ m₂ : Mem} {p : Addr} {k : Nat} (hk : k + 8 ≤ 32)
    (h : ∀ a, Region.Contains ⟨p, 32⟩ a 1 → m₁ a = m₂ a) :
    m₁.readW (p + BitVec.ofNat 64 k) 64 = m₂.readW (p + BitVec.ofNat 64 k) 64 :=
  Mem.readW_congr fun i hi => h _ (by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith))

theorem readW_congr0 {m₁ m₂ : Mem} {p : Addr}
    (h : ∀ a, Region.Contains ⟨p, 32⟩ a 1 → m₁ a = m₂ a) : m₁.readW p 64 = m₂.readW p 64 := by
  have := readW_congr (k := 0) (by omega_arith) h
  rwa [show p + BitVec.ofNat 64 0 = p from BitVec.add_zero p] at this

theorem readW_congr8 {m₁ m₂ : Mem} {p : Addr}
    (h : ∀ a, Region.Contains ⟨p, 32⟩ a 1 → m₁ a = m₂ a) : m₁.readW (p + 8) 64 = m₂.readW (p + 8) 64 :=
  readW_congr (k := 8) (by omega_arith) h

theorem readW_congr16 {m₁ m₂ : Mem} {p : Addr}
    (h : ∀ a, Region.Contains ⟨p, 32⟩ a 1 → m₁ a = m₂ a) : m₁.readW (p + 16) 64 = m₂.readW (p + 16) 64 :=
  readW_congr (k := 16) (by omega_arith) h

theorem wordsAt_congr {m₁ m₂ : Mem} {p : Addr}
    (h : ∀ a, Region.Contains ⟨p, 32⟩ a 1 → m₁ a = m₂ a) : wordsAt m₁ p 4 = wordsAt m₂ p 4 := by
  simp only [wordsAt]
  exact List.map_congr_left fun i hi => readW_congr (by have := List.mem_range.mp hi; omega_arith) h

theorem setWidth_ptr (x : BitVec 64) : (BitVec.setWidth abi.ptrBits x).toNat = x.toNat :=
  congrArg BitVec.toNat (BitVec.setWidth_eq x)

/-! ## Forwarding to a width's function -/

theorem forward_refill (p S : Nat) (hS : S + 72 ≤ 2 ^ 64) {name : String} {body : Prog isa}
    (h : Verified target body (Refill.contract p abi S))
    (hsp : body.all (fun i => !isa.writesSp i) = true) (hd : body.x86_64Depth ≤ S)
    (hsat : ∃ s, (Refill.contract p abi (S + 64)).pre s) :
    Verified target (Impl.Dsa.X86_64.ParameterSearch.width name body) (Refill.contract p abi (S + 64)) := by
  refine Verified.forward (sig := Spec.Dsa.parameterSearchSig) (bytes := 56) h (by decide) (by decide)
    (by decide) (by omega_arith) hsp hd ?_ ?_ hsat ?_
  · intro vs m₁ m₂ hl hb _ hpr
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 7) hl
    replace hl := Nat.succ.inj hl
    iterate 6
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
      replace hl := Nat.succ.inj hl
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    replace hl := Nat.succ.inj hl
    obtain rfl := List.eq_nil_of_length_eq_zero hl
    simp only [Spec.Dsa.parameterSearchSig, Sig.bufs_nil, Sig.bufs_slice, Sig.bufs_array,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size,
      Nat.mul_one, Nat.reduceMul] at hb
    obtain ⟨-, -, -, -, b5⟩ := hb
    change Curry.apply (α := Mem → Prop) [ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.addr,
      ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr] _ _ m₁ at hpr
    change Curry.apply (α := Mem → Prop) [ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.addr,
      ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr] _ _ m₂
    dsimp only [Curry.apply, ArgWord.ofRaw] at hpr ⊢
    rwa [← readW_congr0 b5, ← readW_congr8 b5, ← readW_congr16 b5]
  · intro vs m₁ m₂ m' r hl hb _ hq
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 7) hl
    replace hl := Nat.succ.inj hl
    iterate 2
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
      replace hl := Nat.succ.inj hl
    obtain ⟨rand, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    replace hl := Nat.succ.inj hl
    obtain ⟨randLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    replace hl := Nat.succ.inj hl
    iterate 2
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
      replace hl := Nat.succ.inj hl
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    replace hl := Nat.succ.inj hl
    obtain rfl := List.eq_nil_of_length_eq_zero hl
    simp only [Spec.Dsa.parameterSearchSig, Sig.bufs_nil, Sig.bufs_slice, Sig.bufs_array,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size,
      Nat.mul_one, Nat.reduceMul] at hb
    obtain ⟨-, -, b3, -, b5⟩ := hb
    rw [← setWidth_ptr randLen] at b3
    change Curry.apply (α := Mem → Mem → BitVec (Spec.Dsa.parameterSearchSig.retBits abi.ptrBits) → Prop)
      [ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.addr,
      ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr] _ _ m₁ m' r at hq
    change Curry.apply (α := Mem → Mem → BitVec (Spec.Dsa.parameterSearchSig.retBits abi.ptrBits) → Prop)
      [ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.addr,
      ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr] _ _ m₂ m' r
    dsimp only [Curry.apply, ArgWord.ofRaw] at hq ⊢
    rwa [← readW_congr0 b5, ← readW_congr8 b5, ← bytesAt_congr b3]
  · intro vs m₁ m₂ hl hb _
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 7) hl
    replace hl := Nat.succ.inj hl
    iterate 2
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
      replace hl := Nat.succ.inj hl
    obtain ⟨rand, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    replace hl := Nat.succ.inj hl
    obtain ⟨randLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    replace hl := Nat.succ.inj hl
    iterate 2
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
      replace hl := Nat.succ.inj hl
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    replace hl := Nat.succ.inj hl
    obtain rfl := List.eq_nil_of_length_eq_zero hl
    simp only [Spec.Dsa.parameterSearchSig, Sig.bufs_nil, Sig.bufs_slice, Sig.bufs_array,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size,
      Nat.mul_one, Nat.reduceMul] at hb
    obtain ⟨-, -, b3, -, b5⟩ := hb
    rw [← setWidth_ptr randLen] at b3
    change Curry.apply (α := Mem → List Nat) [ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.addr,
      ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr] _ _ m₁ =
      Curry.apply (α := Mem → List Nat) [ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.addr,
      ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr] _ _ m₂
    dsimp only [Curry.apply, ArgWord.ofRaw]
    rw [wordsAt_congr b5, bytesAt_congr b3]

end VG.Proof.Dsa.X86_64.Generation.RefillWidths
