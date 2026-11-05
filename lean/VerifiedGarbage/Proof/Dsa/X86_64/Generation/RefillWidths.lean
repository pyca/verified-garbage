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

theorem stackArgs_two (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

/-! ## Code that changes only `rax` and the flags -/

/-- `u` is `s` but for `rax` and the flags: every contract built with
`Sig.contract` under `abi` holds of one as of the other. -/
structure Agree (u s : State) : Prop where
  gpr : ∀ r, r ≠ .rax → u.gpr r = s.gpr r
  mem : u.mem = s.mem
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  mxcsr : u.mxcsr = s.mxcsr

theorem argRegs_ne : ∀ r ∈ argRegs, r ≠ .rax := by decide

theorem Agree.rsp {u s : State} (h : Agree u s) : u.gpr .rsp = s.gpr .rsp := h.gpr _ (by decide)

theorem Agree.stackArg {u s : State} (h : Agree u s) (i : Nat) : stackArg u i = stackArg s i := by
  simp only [VG.X86_64.stackArg, stackArgAddr, h.rsp, h.mem]

theorem Agree.args {u s : State} (h : Agree u s) {ws : List Nat} {f : State → List (BitVec 64)}
    (e : abi.args ws = some f) : f u = f s := by
  simp only [abi] at e
  split at e
  · cases e
    exact List.map_congr_left fun r hr => h.gpr r (argRegs_ne r (List.mem_of_mem_take hr))
  · cases e
    rw [List.map_congr_left fun r hr => h.gpr r (argRegs_ne r hr),
      List.map_congr_left fun i _ => h.stackArg i]

theorem Agree.pre {u s : State} (h : Agree u s) {sig : Sig}
    {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
    {st : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} :
    (sig.contract abi pre post wa st leak).pre u ↔ (sig.contract abi pre post wa st leak).pre s := by
  simp only [Sig.contract]
  split
  · exact Iff.rfl
  · rename_i vals e
    rw [h.args e]
    simp only [abi, stackArgAddr, h.rsp, h.mem, h.rd, h.wr]

theorem Agree.post {u s s' : State} (h : Agree u s) {sig : Sig}
    {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
    {st : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} :
    (sig.contract abi pre post wa st leak).post u s' ↔ (sig.contract abi pre post wa st leak).post s s' := by
  simp only [Sig.contract]
  split
  · exact Iff.rfl
  · rename_i vals e
    rw [h.args e]
    simp only [abi, h.mem]

theorem Agree.pub {u u' s s' : State} (h : Agree u s) (h' : Agree u' s') {sig : Sig}
    {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
    {st : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} :
    (sig.contract abi pre post wa st leak).pub u u' ↔ (sig.contract abi pre post wa st leak).pub s s' := by
  simp only [Sig.contract]
  split
  · exact Iff.rfl
  · rename_i vals e
    rw [h.args e, h'.args e]
    simp only [abi, h.mem, h'.mem, h.rsp, h'.rsp]

theorem Agree.abiPreserved {u s s' : State} (h : Agree u s) (a : target.abiPreserved u s') :
    target.abiPreserved s s' := by
  obtain ⟨a₁, a₂, a₃⟩ := a
  refine ⟨fun r hr => ?_, ?_, ?_⟩
  · rw [a₁ r hr, h.gpr r (by revert r; decide)]
  · rw [← h.rsp, a₂, h.mem]
  · rw [a₃, h.mxcsr]

theorem agree_flags (s : State) (c o z n : Option Bool) : Agree (s.setFlags c o z n) s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

/-! ## The width -/

/-- `state[1]`, the modulus's width. -/
abbrev widthWord (s : State) : BitVec 64 := s.mem.readW (stackArg s 1 + 8) 64

theorem sub_beq_zero (a b : BitVec 64) : (a - b == 0) = (a == b) :=
  Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq, BitVec.sub_eq_zero_iff_eq])

theorem widthOf_run (n : Nat) (hn : BitVec.signExtend 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n)
    (s : State) (h₁ : InRegions (s.rd ++ s.wr) (stackArgAddr s 1) 8)
    (h₂ : InRegions (s.rd ++ s.wr) (stackArg s 1 + 8) 8) :
    ∃ u, execBlock isa (Impl.Dsa.X86_64.ParameterSearch.widthOf n) s =
        some (u, [.addr (stackArgAddr s 1), .addr (stackArg s 1 + 8)]) ∧
      Agree u s ∧ u.gpr .rax = widthWord s ∧ isa.eval .e u = some (widthWord s == BitVec.ofNat 64 n) := by
  have ea₁ : s.ea { base := .rsp, disp := 16 } = stackArgAddr s 1 := rfl
  have e₁ : exec (.mov .rax (.mem { base := .rsp, disp := 16 })) s = some (s.setReg .rax (stackArg s 1)) := by
    simp only [exec, readSrc, State.load64, ea₁, h₁, ite_true, Option.map_some]; rfl
  have ea₂ : (s.setReg .rax (stackArg s 1)).ea { base := .rax, disp := 8 } = stackArg s 1 + 8 := rfl
  have e₂ : exec (.mov .rax (.mem { base := .rax, disp := 8 })) (s.setReg .rax (stackArg s 1)) =
      some ((s.setReg .rax (stackArg s 1)).setReg .rax (widthWord s)) := by
    simp only [exec, readSrc, State.load64, ea₂]
    rw [if_pos h₂]; rfl
  obtain ⟨u, e₃⟩ : ∃ u, exec (.alu .cmp .rax (.imm (BitVec.ofNat 32 n)))
      ((s.setReg .rax (stackArg s 1)).setReg .rax (widthWord s)) = some u := ⟨_, rfl⟩
  have hu : u = ((s.setReg .rax (stackArg s 1)).setReg .rax (widthWord s)).setFlags _ _
      (some ((widthWord s - BitVec.signExtend 64 (BitVec.ofNat 32 n)) == 0)) _ :=
    (Option.some.inj e₃).symm
  refine ⟨u, ?_, ⟨fun r hr => ?_, by rw [hu]; rfl, by rw [hu]; rfl, by rw [hu]; rfl, by rw [hu]; rfl⟩,
    by rw [hu]; rfl, ?_⟩
  · simp only [Impl.Dsa.X86_64.ParameterSearch.widthOf, execBlock, isa, e₁, e₂, e₃]
    rfl
  · rw [hu]
    show (if r = .rax then _ else if r = .rax then _ else s.gpr r) = s.gpr r
    simp only [hr, ite_false]
  · rw [hu]
    show some ((widthWord s - BitVec.signExtend 64 (BitVec.ofNat 32 n)) == 0) = _
    rw [hn, sub_beq_zero]

end VG.Proof.Dsa.X86_64.Generation.RefillWidths
