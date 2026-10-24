module

public import VerifiedGarbage.Spec.Dsa.RandomSign
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# Randomized DSA signing on PPC64LE: the contract on the registers and the stack

`rsContract`: `vg_dsa_sign_random(out = r3, out_len = r4, used = r5,
key = r6, key_len = r7, p_len = r8, q_len = r9, digest = r10, digest_len,
rand, rand_len, scratch, scratch_len)`, the last five on the stack, with the
304 bytes of stack below the stack pointer that its frame uses (`vg_dsa_sign`
uses none). `randomSign_implies`: it implies the shared contract.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE

/-- The bytes of stack below the stack pointer the function uses. -/
abbrev rsStack : Nat := 304

/-- The arguments on the stack. -/
abbrev rsStackArgs (s : State) : Region := ⟨stackArgAddr s 0, 40⟩

/-- The result `randomSignBytes` gives, on entry. -/
def rsRes (s : State) : Spec.Dsa.RandomSignResult :=
  Spec.Dsa.randomSignBytes (s.gpr .r8).toNat (s.gpr .r9).toNat
    (Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)

/-- `vg_dsa_sign_random`, on the registers and the stack. -/
def rsContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let used : Region := ⟨s.gpr .r5, 8⟩
    let key : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
    let dg : Region := ⟨s.gpr .r10, (stackArg s 0).toNat⟩
    let rnd : Region := ⟨stackArg s 1, (stackArg s 2).toNat⟩
    let scr : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
    let stk : Region := ⟨s.sp - BitVec.ofNat 64 rsStack, rsStack⟩
    rsStack ≤ s.sp.toNat ∧ s.sp.toNat + 32 + 8 * 13 ≤ 2 ^ 64 ∧
      s.rd = [key, dg, rnd, rsStackArgs s] ∧ s.wr = [out, used, scr] ∧
      out.Disjoint used ∧ out.Disjoint key ∧ out.Disjoint dg ∧ out.Disjoint rnd ∧ out.Disjoint scr ∧
      out.Disjoint (rsStackArgs s) ∧ used.Disjoint key ∧ used.Disjoint dg ∧ used.Disjoint rnd ∧
      used.Disjoint scr ∧ used.Disjoint (rsStackArgs s) ∧ key.Disjoint scr ∧ dg.Disjoint scr ∧
      rnd.Disjoint scr ∧ scr.Disjoint (rsStackArgs s) ∧
      stk.Disjoint out ∧ stk.Disjoint used ∧ stk.Disjoint key ∧ stk.Disjoint dg ∧ stk.Disjoint rnd ∧
      stk.Disjoint scr ∧ stk.Disjoint (rsStackArgs s) ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 8 ≤ 2 ^ 64 ∧
      (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64 ∧ (s.gpr .r10).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧
      (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64 ∧
      (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Dsa.lengthsValid (s.gpr .r8).toNat (s.gpr .r9).toNat ∧
      (s.gpr .r4).toNat = 2 * (s.gpr .r9).toNat ∧
      (s.gpr .r7).toNat = 3 * (s.gpr .r8).toNat + 2 * (s.gpr .r9).toNat ∧
      Spec.Dsa.randomSignScratchWords (s.gpr .r8).toNat ≤ (stackArg s 4).toNat
  post s t :=
    ((t.gpr .r3).setWidth 32).toNat = (rsRes s).status ∧
      Spec.Rsa.bytesAt t.mem (s.gpr .r3) (s.gpr .r4).toNat =
        (rsRes s).signature.getD (List.replicate (s.gpr .r4).toNat 0) ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .r5) 1 = [BitVec.ofNat 64 (rsRes s).used]
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
      s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
      stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧ stackArg s₁ 3 = stackArg s₂ 3 ∧
      stackArg s₁ 4 = stackArg s₂ 4 ∧
      Spec.Dsa.publicBytesLeak (s₁.gpr .r8).toNat (s₁.gpr .r9).toNat
          (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r6) (s₁.gpr .r7).toNat) ++ [(rsRes s₁).status, (rsRes s₁).used] ++
          (rsRes s₁).trace =
      Spec.Dsa.publicBytesLeak (s₂.gpr .r8).toNat (s₂.gpr .r9).toNat
          (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r6) (s₂.gpr .r7).toNat) ++ [(rsRes s₂).status, (rsRes s₂).used] ++
          (rsRes s₂).trace

theorem rsStackArgs_five (s : State) :
    List.map (stackArg s) (List.range 5) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4] :=
  rfl

/-- A state meeting `rsContract.pre`: 1024-bit p and 160-bit q, `out` at
`0x4000`, `used` at `0x5000`, the key at `0x1000`, the digest at `0x3000`,
the tape at `0x6000` and the working space at `0x10000`; the stack's
arguments at `0x9060`. -/
def rsSatState : State where
  gpr r := match r with
    | .r3 => 0x4000 | .r4 => 40 | .r5 => 0x5000 | .r6 => 0x1000 | .r7 => 424 | .r8 => 128 | .r9 => 20
    | .r10 => 0x3000 | _ => 0
  lr := 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9068 then 0x00 else bif Nat.beq a.toNat 0x9069 then 0x60 else
    bif Nat.beq a.toNat 0x907A then 0x01 else bif Nat.beq a.toNat 0x9080 then 0x40 else
    bif Nat.beq a.toNat 0x9081 then 0x08 else 0
  rd := [⟨0x1000, 424⟩, ⟨0x3000, 0⟩, ⟨0x6000, 0⟩, ⟨0x9060, 40⟩]
  wr := [⟨0x4000, 40⟩, ⟨0x5000, 8⟩, ⟨0x10000, 16896⟩]

theorem randomSign_implies : rsContract.Implies (Spec.Dsa.randomSignContract abi rsStack) := by
  exact
    { pre := by
        intro s h
        sig_pre [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, abi, argRegs, rsContract, rsRes,
      rsStackArgs_five, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow] at h
        sig_split h
        have hx : Sig.conj (Sig.pairFacts [(⟨s.gpr .r10, (stackArg s 0).toNat⟩, false),
            (⟨stackArg s 1, (stackArg s 2).toNat⟩, false), (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩, true),
            (⟨stackArgAddr s 0, 40⟩, false)]) := by with_reducible assumption
        simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false,
          Bool.or_false, Bool.false_or, List.nil_append, List.cons_append, Sig.conj_cons,
          Sig.conj] at hx
        obtain ⟨_, _, _⟩ := hx
        sig_reduce [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, abi, argRegs, rsContract, rsRes,
      rsStackArgs_five, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow]
        sig_simp [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, abi, argRegs, rsContract, rsRes,
      rsStackArgs_five, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
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
      post := by sig_implies_post [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, abi, argRegs, rsContract, rsRes,
      rsStackArgs_five, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow]
      pub := by sig_implies_pub [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, abi, argRegs, rsContract, rsRes,
      rsStackArgs_five, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow]
      sat := by sig_implies_sat [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, abi, argRegs, rsContract, rsRes,
      rsStackArgs_five, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow]
          [rsSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using rsSatState }

end VG.Proof.Dsa.PPC64LE
