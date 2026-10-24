module

public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# DSA key generation on PPC64LE: the contract on the registers and the stack

`gkContract`: `vg_dsa_generate_key(out = r3, out_len = r4, used = r5,
params = r6, params_len = r7, p_len = r8, q_len = r9, rand = r10, rand_len,
scratch, scratch_len)`, the last three on the stack, with the 304 bytes of
stack below the stack pointer that its frame uses (the functions it calls
use none). `generate_implies`: it implies the shared contract.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE

/-- The bytes of stack below the stack pointer the function uses. -/
abbrev gkStack : Nat := 304

/-- The arguments on the stack. -/
abbrev gkStackArgs (s : State) : Region := ⟨stackArgAddr s 0, 24⟩

/-- The result `generateKeyBytes` gives, on entry. -/
def gkRes (s : State) : Spec.Dsa.GenerateKeyResult :=
  Spec.Dsa.generateKeyBytes (s.gpr .r8).toNat (s.gpr .r9).toNat
    (Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat)

/-- `vg_dsa_generate_key`, on the registers and the stack. -/
def gkContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let used : Region := ⟨s.gpr .r5, 8⟩
    let ps : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
    let rnd : Region := ⟨s.gpr .r10, (stackArg s 0).toNat⟩
    let scr : Region := ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
    let stk : Region := ⟨s.sp - BitVec.ofNat 64 gkStack, gkStack⟩
    gkStack ≤ s.sp.toNat ∧ s.sp.toNat + 32 + 8 * 11 ≤ 2 ^ 64 ∧
      s.rd = [ps, rnd, gkStackArgs s] ∧ s.wr = [out, used, scr] ∧
      out.Disjoint used ∧ out.Disjoint ps ∧ out.Disjoint rnd ∧ out.Disjoint scr ∧
      out.Disjoint (gkStackArgs s) ∧ used.Disjoint ps ∧ used.Disjoint rnd ∧
      used.Disjoint scr ∧ used.Disjoint (gkStackArgs s) ∧ ps.Disjoint scr ∧
      rnd.Disjoint scr ∧ scr.Disjoint (gkStackArgs s) ∧
      stk.Disjoint out ∧ stk.Disjoint used ∧ stk.Disjoint ps ∧ stk.Disjoint rnd ∧
      stk.Disjoint scr ∧ stk.Disjoint (gkStackArgs s) ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 8 ≤ 2 ^ 64 ∧
      (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64 ∧ (s.gpr .r10).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧
      (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Dsa.lengthsValid (s.gpr .r8).toNat (s.gpr .r9).toNat ∧
      (s.gpr .r4).toNat = 3 * (s.gpr .r8).toNat + 2 * (s.gpr .r9).toNat ∧
      (s.gpr .r7).toNat = 2 * (s.gpr .r8).toNat + (s.gpr .r9).toNat ∧
      Spec.Dsa.generationScratchWords (s.gpr .r8).toNat ≤ (stackArg s 2).toNat
  post s t :=
    ((t.gpr .r3).setWidth 32).toNat = (gkRes s).status ∧
      Spec.Rsa.bytesAt t.mem (s.gpr .r3) (s.gpr .r4).toNat =
        (gkRes s).key.getD (List.replicate (s.gpr .r4).toNat 0) ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .r5) 1 = [BitVec.ofNat 64 (gkRes s).used]
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
      s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
      stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧
      (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r6) (s₁.gpr .r7).toNat).map (·.toNat) ++
          [(gkRes s₁).status, (gkRes s₁).used] ++ (gkRes s₁).trace =
      (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r6) (s₂.gpr .r7).toNat).map (·.toNat) ++
          [(gkRes s₂).status, (gkRes s₂).used] ++ (gkRes s₂).trace

theorem gkStackArgs_three (s : State) :
    List.map (stackArg s) (List.range 3) = [stackArg s 0, stackArg s 1, stackArg s 2] :=
  rfl

/-- A state meeting `gkContract.pre`: 1024-bit p and 160-bit q, `out` at
`0x4000`, `used` at `0x5000`, the domain at `0x1000`, the tape at `0x6000`
and the working space at `0x10000`; the stack's arguments at `0x9060`. -/
def gkSatState : State where
  gpr r := match r with
    | .r3 => 0x4000 | .r4 => 424 | .r5 => 0x5000 | .r6 => 0x1000 | .r7 => 276 | .r8 => 128 | .r9 => 20
    | .r10 => 0x6000 | _ => 0
  lr := 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x906A then 0x01 else bif Nat.beq a.toNat 0x9071 then 0x24 else 0
  rd := [⟨0x1000, 276⟩, ⟨0x6000, 0⟩, ⟨0x9060, 24⟩]
  wr := [⟨0x4000, 424⟩, ⟨0x5000, 8⟩, ⟨0x10000, 73728⟩]

theorem generate_implies : gkContract.Implies (Spec.Dsa.generateKeyContract abi gkStack) := by
  exact
    { pre := by
        intro s h
        sig_pre [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, gkContract, gkRes,
      gkStackArgs_three, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow] at h
        sig_split h
        have hx : Sig.conj (Sig.pairFacts [(⟨s.gpr .r10, (stackArg s 0).toNat⟩, false),
            (⟨stackArg s 1, (stackArg s 2).toNat * 8⟩, true), (⟨stackArgAddr s 0, 24⟩, false)]) := by
          with_reducible assumption
        simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false,
          Bool.or_false, Bool.false_or, List.nil_append, List.cons_append, Sig.conj_cons,
          Sig.conj] at hx
        obtain ⟨_, _⟩ := hx
        sig_reduce [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, gkContract, gkRes,
      gkStackArgs_three, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow]
        sig_simp [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, gkContract, gkRes,
      gkStackArgs_three, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow] []
        sig_and_intros
        sig_close
        all_goals first
          | with_reducible assumption
          | sig_disjoint_symm
          | omega
          | skip
        all_goals done
      post := by sig_implies_post [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, gkContract,
      gkRes, gkStackArgs_three, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow]
      pub := by sig_implies_pub [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, gkContract,
      gkRes, gkStackArgs_three, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow]
      sat := by sig_implies_sat [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, gkContract,
      gkRes, gkStackArgs_three, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow]
          [gkSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using gkSatState }

end VG.Proof.Dsa.PPC64LE
