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
    dsimp only
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
  Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq]; bv_omega)

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
    have h₂' : InRegions ((s.setReg .rax (stackArg s 1)).rd ++ (s.setReg .rax (stackArg s 1)).wr)
        (stackArg s 1 + 8) 8 := h₂
    simp only [exec, readSrc, State.load64, ea₂, h₂', ite_true, Option.map_some]; rfl
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

theorem cmp_run (v : BitVec 32) (s : State) :
    ∃ u, execBlock isa [.alu .cmp .rax (.imm v)] s = some (u, []) ∧ Agree u s ∧
      isa.eval .e u = some ((s.gpr .rax - BitVec.signExtend 64 v) == 0) :=
  ⟨_, rfl, agree_flags s _ _ _ _, rfl⟩

/-! ## The contracts the choice passes through -/

/-- The search's contract for the two larger widths, with the width in `rax`. -/
def largeContract (S : Nat) : Contract isa where
  pre s := (Spec.Dsa.parameterSearchContract abi S).pre s ∧ s.gpr .rax = widthWord s ∧
    (widthWord s).toNat ≠ 128
  post := (Spec.Dsa.parameterSearchContract abi S).post
  pub := (Spec.Dsa.parameterSearchContract abi S).pub

theorem refill_of_search {p S : Nat} {s : State} (h : (Spec.Dsa.parameterSearchContract abi S).pre s)
    (hw : (widthWord s).toNat = p) : (Refill.contract p abi S).pre s := by
  sig_pre [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackArgs_two] at h
  sig_pre [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackArgs_two] at h
  sig_split h
  sig_pre [Refill.contract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackArgs_two]
  sig_pre [Refill.contract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackArgs_two]
  sig_and_intros
  all_goals with_reducible assumption

theorem valid_of_search {S : Nat} {s : State} (h : (Spec.Dsa.parameterSearchContract abi S).pre s) :
    Spec.Dsa.generationPLenValid (widthWord s).toNat = true := by
  sig_pre [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackArgs_two] at h
  sig_pre [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackArgs_two] at h
  sig_split h
  with_reducible assumption

theorem search_in {S : Nat} {s : State} (h : (Spec.Dsa.parameterSearchContract abi S).pre s) :
    InRegions (s.rd ++ s.wr) (stackArgAddr s 1) 8 ∧ InRegions (s.rd ++ s.wr) (stackArg s 1 + 8) 8 := by
  sig_pre [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackArgs_two] at h
  sig_pre [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackArgs_two] at h
  sig_split h
  refine ⟨⟨⟨stackArgAddr s 0, 16⟩, ?_, ?_⟩, ⟨⟨stackArg s 1, 32⟩, ?_, ?_⟩⟩
  · rw [‹s.rd = _›]
    exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · have e : stackArgAddr s 1 = stackArgAddr s 0 + BitVec.ofNat 64 8 := by
      simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    rw [e]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  · rw [‹s.wr = _›]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))
  · exact Offset.contains_base (stackArg s 1) (d := 8) (n := 8) (k := 32) (by omega_arith) (by omega_arith)

theorem wordsAt_four (m : Mem) (p : Addr) : (wordsAt m p 4).map (·.toNat) =
    [(m.readW (p + BitVec.ofNat 64 0) 64).toNat, (m.readW (p + 8) 64).toNat, (m.readW (p + 16) 64).toNat,
      (m.readW (p + 24) 64).toNat] := rfl

theorem search_pub {S : Nat} {s s' : State} (h : (Spec.Dsa.parameterSearchContract abi S).pub s s') :
    s.gpr .rsp = s'.gpr .rsp ∧ stackArg s 1 = stackArg s' 1 ∧ widthWord s = widthWord s' := by
  sig_pub [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackArgs_two] at h
  obtain ⟨hsp, hl, -, -, -, -, -, -, -, h₇⟩ := h
  have hst : stackArg s 1 = stackArg s' 1 := h₇
  refine ⟨hsp, hst, ?_⟩
  rw [wordsAt_four, wordsAt_four] at hl
  have hw := (List.append_inj hl rfl).1
  simp only [List.cons.injEq] at hw
  exact BitVec.eq_of_toNat_eq hw.2.1

/-! ## The choice -/

theorem large_verified (S : Nat) {n₂₅₆ n₃₈₄ : String} {c₂₅₆ c₃₈₄ : Prog isa}
    (h₂₅₆ : Verified target (Impl.Dsa.X86_64.ParameterSearch.width n₂₅₆ c₂₅₆) (Refill.contract 256 abi S))
    (h₃₈₄ : Verified target (Impl.Dsa.X86_64.ParameterSearch.width n₃₈₄ c₃₈₄) (Refill.contract 384 abi S))
    (hsat : ∃ s, (largeContract S).pre s) :
    Verified target (.seq (.block [.alu .cmp .rax (.imm 256)])
      (Code.iteCold .e (Impl.Dsa.X86_64.ParameterSearch.width n₂₅₆ c₂₅₆)
        (Impl.Dsa.X86_64.ParameterSearch.width n₃₈₄ c₃₈₄))) (largeContract S) := by
  refine Verified.entryBranch (p := fun s => s.gpr .rax == 256) (fun _ => []) h₂₅₆ h₃₈₄
    (fun s hs => ?_) ?_ hsat
  · obtain ⟨u, e, ag, ev⟩ := cmp_run 256 s
    obtain ⟨hk, hrax, h128⟩ := hs
    refine ⟨u, e, ?_, fun hp => ⟨ag.pre.mpr (refill_of_search hk ?_), fun s' a q => ⟨ag.abiPreserved a, ag.post.mp q⟩⟩,
      fun hp => ⟨ag.pre.mpr (refill_of_search hk ?_), fun s' a q => ⟨ag.abiPreserved a, ag.post.mp q⟩⟩⟩
    · rw [ev, show BitVec.signExtend 64 (256 : BitVec 32) = 256 from by decide, sub_beq_zero]
    · rw [← hrax, beq_iff_eq.mp hp]; rfl
    · have hv := valid_of_search hk
      simp only [Spec.Dsa.generationPLenValid, Bool.or_eq_true, beq_iff_eq] at hv
      have h256 : (widthWord s).toNat ≠ 256 := fun h => by
        rw [← hrax] at h
        have : s.gpr .rax = 256 := BitVec.eq_of_toNat_eq h
        simp [this] at hp
      omega_arith
  · intro s s' u u' hs hs' hq e e'
    obtain ⟨u₀, e₀, ag, -⟩ := cmp_run 256 s
    obtain ⟨u₀', e₀', ag', -⟩ := cmp_run 256 s'
    rw [e₀] at e; rw [e₀'] at e'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e')
    have pu : (Spec.Dsa.parameterSearchContract abi S).pub u₀ u₀' := (ag.pub ag').mpr hq
    obtain ⟨-, -, hw⟩ := search_pub (S := S) hq
    exact ⟨rfl, by simp only [hs.2.1, hs'.2.1, hw], fun _ => pu, fun _ => pu⟩

theorem widths_verified (S : Nat) {n₁₂₈ n₂₅₆ n₃₈₄ : String} {c₁₂₈ c₂₅₆ c₃₈₄ : Prog isa}
    (h₁₂₈ : Verified target (Impl.Dsa.X86_64.ParameterSearch.width n₁₂₈ c₁₂₈) (Refill.contract 128 abi S))
    (h₂₅₆ : Verified target (Impl.Dsa.X86_64.ParameterSearch.width n₂₅₆ c₂₅₆) (Refill.contract 256 abi S))
    (h₃₈₄ : Verified target (Impl.Dsa.X86_64.ParameterSearch.width n₃₈₄ c₃₈₄) (Refill.contract 384 abi S))
    (hsatL : ∃ s, (largeContract S).pre s)
    (hsat : ∃ s, (Spec.Dsa.parameterSearchContract abi S).pre s) :
    Verified target (Impl.Dsa.X86_64.ParameterSearch.widths n₁₂₈ n₂₅₆ n₃₈₄ c₁₂₈ c₂₅₆ c₃₈₄)
      (Spec.Dsa.parameterSearchContract abi S) := by
  refine Verified.entryBranch (p := fun s => widthWord s == 128)
    (fun s => [.addr (stackArgAddr s 1), .addr (stackArg s 1 + 8)]) h₁₂₈
    (large_verified S h₂₅₆ h₃₈₄ hsatL) (fun s hs => ?_) ?_ hsat
  · obtain ⟨i₁, i₂⟩ := search_in hs
    obtain ⟨u, e, ag, hrax, ev⟩ := widthOf_run 128 (by decide) s i₁ i₂
    have hw : widthWord u = widthWord s := by simp only [widthWord, ag.mem, ag.stackArg]
    refine ⟨u, e, ev, fun hp => ⟨ag.pre.mpr (refill_of_search hs ?_), fun s' a q => ⟨ag.abiPreserved a, ag.post.mp q⟩⟩,
      fun hp => ⟨⟨ag.pre.mpr hs, by rw [hrax, hw], ?_⟩, fun s' a q => ⟨ag.abiPreserved a, ag.post.mp q⟩⟩⟩
    · rw [beq_iff_eq.mp hp]; rfl
    · rw [hw]
      intro h
      have : widthWord s = 128 := BitVec.eq_of_toNat_eq h
      simp [this] at hp
  · intro s s' u u' hs hs' hq e e'
    obtain ⟨i₁, i₂⟩ := search_in hs
    obtain ⟨i₁', i₂'⟩ := search_in hs'
    obtain ⟨u₀, e₀, ag, -, -⟩ := widthOf_run 128 (by decide) s i₁ i₂
    obtain ⟨u₀', e₀', ag', -, -⟩ := widthOf_run 128 (by decide) s' i₁' i₂'
    rw [e₀] at e; rw [e₀'] at e'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e')
    have pu : (Spec.Dsa.parameterSearchContract abi S).pub u₀ u₀' := (ag.pub ag').mpr hq
    obtain ⟨hsp, hst, hw⟩ := search_pub hq
    exact ⟨by simp only [stackArgAddr, hsp, hst], by simp only [hw], fun _ => pu, fun _ => pu⟩

/-! ## Satisfiable with the forwarding frame's stack -/

/-- The memory of `satState`: `scratch_len` and `state` on the stack, and
`state`'s words `[0, p, 32769 p, 0]`. -/
def satMem (p : Nat) : Mem :=
  Mem.writeW (Mem.writeW (Mem.writeW (Mem.writeW (fun _ => 0) (0x1000000000008 : Addr) (25600 : BitVec 64))
    (0x1000000000010 : Addr) (0x4000 : BitVec 64)) (0x4008 : Addr) (BitVec.ofNat 64 p))
    (0x4010 : Addr) (BitVec.ofNat 64 (Spec.Dsa.parameterEntropy p))

/-- A search for width `p`, with the width in `rax` too. -/
def satState (p : Nat) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => BitVec.ofNat 64 (2 * p + Spec.Dsa.generationQLen p) | .rdx => 0x2000
    | .rcx => 0x3000 | .r9 => 0x10000 | .rsp => 0x1000000000000 | .rax => BitVec.ofNat 64 p | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem p
  rd := [⟨0x3000, 0⟩, ⟨0x1000000000008, 16⟩]
  wr := [⟨0x1000, 2 * p + Spec.Dsa.generationQLen p⟩, ⟨0x2000, 8⟩, ⟨0x10000, 204800⟩, ⟨0x4000, 32⟩]

/-- The stack below `satState`'s return address is apart from every region
below `2 ^ 47` or above the return address. -/
theorem below_disjoint {S : Nat} (hS : S ≤ 2 ^ 40) {r : Region}
    (hr : decide (r.base.toNat + r.len ≤ 2 ^ 47 ∨
      (2 ^ 48 ≤ r.base.toNat ∧ r.base.toNat + r.len ≤ 2 ^ 64)) = true) :
    Region.Disjoint ⟨(0x1000000000000 : Addr) - BitVec.ofNat 64 (S + 63 + 1), S + 63 + 1⟩ r := by
  have hr := of_decide_eq_true hr
  have ht : ((0x1000000000000 : Addr) - BitVec.ofNat 64 (S + 63 + 1)).toNat = 2 ^ 48 - (S + 64) := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, show (0x1000000000000 : Addr).toNat = 2 ^ 48 from rfl]
    omega_arith
  refine Region.disjoint_of_le ?_ ?_ ?_
  · simp only [ht]
    omega_arith
  · simp only [ht]
    omega_arith
  · omega_arith

theorem search_sat {p S : Nat} (hp : p = 128 ∨ p = 256 ∨ p = 384) (hS : S ≤ 2 ^ 40) :
    (Spec.Dsa.parameterSearchContract abi (S + 64)).pre (satState p) := by
  rcases hp with rfl | rfl | rfl
  all_goals sig_pre [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackArgs_two]
  all_goals sig_and_intros
  all_goals first
    | decide +kernel
    | exact Region.disjoint_of_sep (by decide +kernel)
    | exact below_disjoint hS (by decide +kernel)
    | exact Nat.le_trans (Nat.add_le_add_right hS 64) (by decide +kernel)

theorem refill_sat {p S : Nat} (hp : p = 128 ∨ p = 256 ∨ p = 384) (hS : S ≤ 2 ^ 40) :
    ∃ s, (Refill.contract p abi (S + 64)).pre s :=
  ⟨satState p, refill_of_search (search_sat hp hS) (by rcases hp with rfl | rfl | rfl <;> decide +kernel)⟩

theorem large_sat {S : Nat} (hS : S ≤ 2 ^ 40) : ∃ s, (largeContract (S + 64)).pre s :=
  ⟨satState 256, search_sat (.inr (.inl rfl)) hS, by decide +kernel, by decide +kernel⟩

theorem full_sat {S : Nat} (hS : S ≤ 2 ^ 40) : ∃ s, (Spec.Dsa.parameterSearchContract abi (S + 64)).pre s :=
  ⟨satState 128, search_sat (.inl rfl) hS⟩

/-! ## The search -/

/-- `vg_dsa_parameter_search` by the functions for each width, each verified
against the search's contract with its width fixed and `S` octets of stack:
the choice and the forwarding frame (56 octets and the return address) need
64 more. -/
theorem refillWidths_verified (S : Nat) (hS : S ≤ 2 ^ 40) {n₁₂₈ n₂₅₆ n₃₈₄ : String}
    {c₁₂₈ c₂₅₆ c₃₈₄ : Prog isa}
    (h₁₂₈ : Verified target c₁₂₈ (Refill.contract 128 abi S))
    (h₂₅₆ : Verified target c₂₅₆ (Refill.contract 256 abi S))
    (h₃₈₄ : Verified target c₃₈₄ (Refill.contract 384 abi S))
    (s₁₂₈ : c₁₂₈.all (fun i => !isa.writesSp i) = true) (s₂₅₆ : c₂₅₆.all (fun i => !isa.writesSp i) = true)
    (s₃₈₄ : c₃₈₄.all (fun i => !isa.writesSp i) = true)
    (d₁₂₈ : c₁₂₈.x86_64Depth ≤ S) (d₂₅₆ : c₂₅₆.x86_64Depth ≤ S) (d₃₈₄ : c₃₈₄.x86_64Depth ≤ S) :
    Verified target (Impl.Dsa.X86_64.ParameterSearch.widths n₁₂₈ n₂₅₆ n₃₈₄ c₁₂₈ c₂₅₆ c₃₈₄)
      (Spec.Dsa.parameterSearchContract abi (S + 64)) :=
  have hS' : S + 72 ≤ 2 ^ 64 := by omega_arith
  widths_verified (S + 64)
    (forward_refill 128 S hS' h₁₂₈ s₁₂₈ d₁₂₈ (refill_sat (.inl rfl) hS))
    (forward_refill 256 S hS' h₂₅₆ s₂₅₆ d₂₅₆ (refill_sat (.inr (.inl rfl)) hS))
    (forward_refill 384 S hS' h₃₈₄ s₃₈₄ d₃₈₄ (refill_sat (.inr (.inr rfl)) hS))
    (large_sat hS) (full_sat hS)

/-- The choice writes `rsp` only in frames and calls, if its bodies do. -/
theorem refillWidths_spSafe {n₁₂₈ n₂₅₆ n₃₈₄ : String} {c₁₂₈ c₂₅₆ c₃₈₄ : Prog isa}
    (s₁₂₈ : c₁₂₈.all (fun i => !isa.writesSp i) = true) (s₂₅₆ : c₂₅₆.all (fun i => !isa.writesSp i) = true)
    (s₃₈₄ : c₃₈₄.all (fun i => !isa.writesSp i) = true) :
    (Impl.Dsa.X86_64.ParameterSearch.widths n₁₂₈ n₂₅₆ n₃₈₄ c₁₂₈ c₂₅₆ c₃₈₄).all
      (fun i => !isa.writesSp i) = true := by
  simp only [Impl.Dsa.X86_64.ParameterSearch.widths, Impl.Dsa.X86_64.ParameterSearch.width, Code.iteCold,
    Code.all, forward_spSafe s₁₂₈, forward_spSafe s₂₅₆, forward_spSafe s₃₈₄, Bool.and_true]
  rfl

end VG.Proof.Dsa.X86_64.Generation.RefillWidths
