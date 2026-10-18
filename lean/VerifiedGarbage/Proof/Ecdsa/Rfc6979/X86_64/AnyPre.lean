module

public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.AnyHash
public import VerifiedGarbage.Proof.Framework.X86_64.CallMeetsC
public import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.SigEval

/-!
# Deterministic ECDSA on x86-64, for any hash function: the precondition by name

`APre I cs s` is the precondition of `I.signAnyContract` under
`abi.withConsts cs` (`apre_of`), for tables `cs` (the comb's, never none):
`vg_ecdsa_<curve>_rfc6979_sign(out = rdi, d = rsi, digest = rdx,
digest_len = rcx, scratch = r8, hash = r9, hash_fns = [rsp + 8])`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64

theorem stackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

/-- The table of streaming functions and the stack argument pointing to it. -/
abbrev tabR (s : State) : Region := ⟨stackArg s 0, 24⟩
abbrev argR (s : State) : Region := ⟨stackArgAddr s 0, 8⟩

/-- The caller's buffers: `out`, `d`, the digest and `scratch`. -/
abbrev outR (I : Spec.Ecdsa.Rfc6979.Instance) (s : State) : Region := ⟨s.gpr .rdi, 2 * I.ecdsa.curve.len⟩
abbrev dR (I : Spec.Ecdsa.Rfc6979.Instance) (s : State) : Region := ⟨s.gpr .rsi, I.ecdsa.curve.len⟩
abbrev dgR (s : State) : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
abbrev scrR (I : Spec.Ecdsa.Rfc6979.Instance) (s : State) : Region := ⟨s.gpr .r8, I.scratchWords * 8⟩
abbrev retR (s : State) : Region := ⟨s.gpr .rsp, 8⟩
abbrev stkR (s : State) : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 408, 408⟩

/-- The precondition of `vg_ecdsa_<curve>_rfc6979_sign`, by name. -/
structure APre (I : Spec.Ecdsa.Rfc6979.Instance) (cs : List (String × List (BitVec 64))) (s : State) : Prop where
  sp : 408 ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 16 ≤ 2 ^ 64
  rd : s.rd = [dR I s, dgR s, tabR s, argR s] ++ Abi.constRegions s.syms cs
  held : Abi.constsHeld s.mem s.syms cs
  tbl : ∀ t ∈ Abi.constRegions s.syms cs, t.base.toNat + t.len ≤ 2 ^ 64 ∧ (∀ r ∈ s.wr, t.Disjoint r) ∧
    t.Disjoint (retR s) ∧ t.Disjoint (stkR s)
  wr : s.wr = [outR I s, scrR I s]
  oD : (outR I s).Disjoint (dR I s)
  oG : (outR I s).Disjoint (dgR s)
  oS : (outR I s).Disjoint (scrR I s)
  oT : (outR I s).Disjoint (tabR s)
  oA : (outR I s).Disjoint (argR s)
  dS : (dR I s).Disjoint (scrR I s)
  gS : (dgR s).Disjoint (scrR I s)
  sT : (scrR I s).Disjoint (tabR s)
  sA : (scrR I s).Disjoint (argR s)
  rO : (retR s).Disjoint (outR I s)
  rD : (retR s).Disjoint (dR I s)
  rG : (retR s).Disjoint (dgR s)
  rS : (retR s).Disjoint (scrR I s)
  rT : (retR s).Disjoint (tabR s)
  rA : (retR s).Disjoint (argR s)
  kO : (stkR s).Disjoint (outR I s)
  kD : (stkR s).Disjoint (dR I s)
  kG : (stkR s).Disjoint (dgR s)
  kS : (stkR s).Disjoint (scrR I s)
  kT : (stkR s).Disjoint (tabR s)
  kA : (stkR s).Disjoint (argR s)
  bO : (s.gpr .rdi).toNat + 2 * I.ecdsa.curve.len ≤ 2 ^ 64
  bD : (s.gpr .rsi).toNat + I.ecdsa.curve.len ≤ 2 ^ 64
  bG : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  bS : (s.gpr .r8).toNat + I.scratchWords * 8 ≤ 2 ^ 64
  bT : (stackArg s 0).toNat + 24 ≤ 2 ^ 64
  hk : (s.gpr .r9).toNat ∈ Spec.Ecdsa.Rfc6979.hashIds
  dl : ∀ H, Spec.HashId.mgf1 (s.gpr .r9).toNat = some H → (s.gpr .rcx).toNat = H.len
  fns : Spec.HashFns.tableOf (s.gpr .r9).toNat s.mem (stackArg s 0)
    fun a K n => FnMeets (abi.withConsts cs) K n 408 s a

/-- What a contract with `fns` requires of the functions its arguments point to. -/
theorem contract_fns {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    {f : Curry (sig.words A.ptrBits) (Mem → (Addr → (Abi isa → Nat → Contract isa) → Nat → Prop) → Prop)}
    {vals : State → List (BitVec 64)} (hv : A.args ((sig.words A.ptrBits).map (·.bits A.ptrBits)) = some vals)
    {s : State} (h : (sig.contract A pre post wa stack leak (some f)).pre s) :
    Curry.apply (sig.words A.ptrBits) f (vals s) (A.mem s) (fun a K n => FnMeets A K n stack s a) := by
  unfold Sig.contract at h
  simp only [hv] at h
  exact h.2.2.2.2.2.2.2

/-- A contract with `fns` holds of an entry if the contract without them does
and the functions its arguments point to meet what it requires of them. -/
theorem contract_of_fns {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    {f : Curry (sig.words A.ptrBits) (Mem → (Addr → (Abi isa → Nat → Contract isa) → Nat → Prop) → Prop)}
    {vals : State → List (BitVec 64)} (hv : A.args ((sig.words A.ptrBits).map (·.bits A.ptrBits)) = some vals)
    {s : State} (h₁ : (sig.contract A pre post wa stack leak none).pre s)
    (h₂ : Curry.apply (sig.words A.ptrBits) f (vals s) (A.mem s) (fun a K n => FnMeets A K n stack s a)) :
    (sig.contract A pre post wa stack leak (some f)).pre s := by
  unfold Sig.contract at h₁ ⊢
  simp only [hv] at h₁ ⊢
  obtain ⟨a, b, c, d, e, g, i⟩ := h₁
  exact ⟨a, b, c, d, e, g, i, h₂⟩

theorem apre_cons {I : Spec.Ecdsa.Rfc6979.Instance} {cs : List (String × List (BitVec 64))}
    {c : String × List (BitVec 64)} {cs' : List (String × List (BitVec 64))} (hcs : cs = c :: cs') {s : State}
    (h : (I.signAnyContract (abi.withConsts cs) 408).pre s) : APre I cs s := by
  subst hcs
  have hf := contract_fns (vals := fun s => argRegs.map s.gpr ++ [stackArg s 0]) rfl h
  sig_pre [Spec.Ecdsa.Rfc6979.Instance.signAnyContract, Spec.Ecdsa.Rfc6979.Instance.signAnySig, abi, argRegs,
    Abi.withConsts, stackBelow, stackArgs_one] at h
  sig_pre [Spec.Ecdsa.Rfc6979.Instance.signAnyContract, Spec.Ecdsa.Rfc6979.Instance.signAnySig, abi, argRegs,
    Abi.withConsts, stackBelow, stackArgs_one] at h
  obtain ⟨sp, sp2, hdrop, held, tbl, htake, wr, oD, oG, oS, oT, oA, dS, gS, sT, sA, rO, rD, rG, rS, rT, rA,
    kO, kD, kG, kS, kT, kA, bO, bD, bG, bS, bT, hk, dl, -⟩ := h
  refine ⟨sp, sp2, ?_, held, tbl, wr, oD, oG, oS, oT, oA, dS, gS, sT, sA, rO, rD, rG, rS, rT, rA,
    kO, kD, kG, kS, kT, kA, bO, bD, bG, bS, bT, hk, dl, hf⟩
  rw [← List.take_append_drop (s.rd.length - (cs'.length + 1)) s.rd, htake, hdrop]

/-- The reverse of `apre_cons`. -/
theorem pre_of_apre_cons {I : Spec.Ecdsa.Rfc6979.Instance} {cs : List (String × List (BitVec 64))}
    {c : String × List (BitVec 64)} {cs' : List (String × List (BitVec 64))} (hcs : cs = c :: cs') {s : State}
    (h : APre I cs s) : (I.signAnyContract (abi.withConsts cs) 408).pre s := by
  subst hcs
  unfold Spec.Ecdsa.Rfc6979.Instance.signAnyContract
  refine contract_of_fns (vals := fun s => argRegs.map s.gpr ++ [stackArg s 0]) rfl ?_ h.fns
  sig_pre [Spec.Ecdsa.Rfc6979.Instance.signAnySig, abi, argRegs, Abi.withConsts, stackBelow, stackArgs_one]
  sig_pre [Spec.Ecdsa.Rfc6979.Instance.signAnySig, abi, argRegs, Abi.withConsts, stackBelow, stackArgs_one]
  have hl : s.rd.length - (cs'.length + 1) = 4 := by
    rw [h.rd, List.length_append, WithConsts.constRegions_length]; simp
  refine ⟨h.sp, h.sp2, ?_, h.held, h.tbl, ?_, h.wr, h.oD, h.oG, h.oS, h.oT, h.oA, h.dS, h.gS, h.sT, h.sA, h.rO,
    h.rD, h.rG, h.rS, h.rT, h.rA, h.kO, h.kD, h.kG, h.kS, h.kT, h.kA, h.bO, h.bD, h.bG, h.bS, h.bT, h.hk, h.dl⟩
  · rw [hl, h.rd]; rfl
  · rw [hl, h.rd]; rfl

theorem apre_nil {I : Spec.Ecdsa.Rfc6979.Instance} {s : State}
    (h : (I.signAnyContract (abi.withConsts []) 408).pre s) : APre I [] s := by
  have hf := contract_fns (vals := fun s => argRegs.map s.gpr ++ [stackArg s 0]) rfl h
  sig_pre [Spec.Ecdsa.Rfc6979.Instance.signAnyContract, Spec.Ecdsa.Rfc6979.Instance.signAnySig, abi, argRegs,
    Abi.withConsts, stackBelow, stackArgs_one] at h
  sig_pre [Spec.Ecdsa.Rfc6979.Instance.signAnyContract, Spec.Ecdsa.Rfc6979.Instance.signAnySig, abi, argRegs,
    Abi.withConsts, stackBelow, stackArgs_one] at h
  obtain ⟨sp, sp2, hrd, wr, oD, oG, oS, oT, oA, dS, gS, sT, sA, rO, rD, rG, rS, rT, rA,
    kO, kD, kG, kS, kT, kA, bO, bD, bG, bS, bT, hk, dl, -⟩ := h
  exact ⟨sp, sp2, by rw [hrd]; rfl, (fun _ h => by cases h),
    (fun _ h => by rw [show Abi.constRegions _ [] = [] from rfl] at h; cases h), wr, oD, oG,
    oS, oT, oA, dS, gS, sT, sA, rO, rD, rG, rS, rT, rA, kO, kD, kG, kS, kT, kA, bO, bD, bG, bS, bT, hk, dl, hf⟩

/-- The precondition of the shared contract, by name. -/
theorem apre_of {I : Spec.Ecdsa.Rfc6979.Instance} {cs : List (String × List (BitVec 64))} {s : State}
    (h : (I.signAnyContract (abi.withConsts cs) 408).pre s) : APre I cs s := by
  cases cs with
  | nil => exact apre_nil h
  | cons c cs => exact apre_cons rfl h

theorem pre_of_apre_nil {I : Spec.Ecdsa.Rfc6979.Instance} {s : State} (h : APre I [] s) :
    (I.signAnyContract (abi.withConsts []) 408).pre s := by
  unfold Spec.Ecdsa.Rfc6979.Instance.signAnyContract
  refine contract_of_fns (vals := fun s => argRegs.map s.gpr ++ [stackArg s 0]) rfl ?_ h.fns
  sig_pre [Spec.Ecdsa.Rfc6979.Instance.signAnySig, abi, argRegs, Abi.withConsts, stackBelow, stackArgs_one]
  sig_pre [Spec.Ecdsa.Rfc6979.Instance.signAnySig, abi, argRegs, Abi.withConsts, stackBelow, stackArgs_one]
  exact ⟨h.sp, h.sp2, by rw [h.rd]; rfl, h.wr, h.oD, h.oG, h.oS, h.oT, h.oA, h.dS, h.gS, h.sT, h.sA, h.rO,
    h.rD, h.rG, h.rS, h.rT, h.rA, h.kO, h.kD, h.kG, h.kS, h.kT, h.kA, h.bO, h.bD, h.bG, h.bS, h.bT, h.hk, h.dl⟩

/-- The reverse of `apre_of`. -/
theorem pre_of_apre {I : Spec.Ecdsa.Rfc6979.Instance} {cs : List (String × List (BitVec 64))} {s : State}
    (h : APre I cs s) : (I.signAnyContract (abi.withConsts cs) 408).pre s := by
  cases cs with
  | nil => exact pre_of_apre_nil h
  | cons c cs => exact pre_of_apre_cons rfl h

/-- The public data of `vg_ecdsa_<curve>_rfc6979_sign`, by name. -/
structure APub (I : Spec.Ecdsa.Rfc6979.Instance) (cs : List (String × List (BitVec 64))) (s₁ s₂ : State) :
    Prop where
  rsp : s₁.gpr .rsp = s₂.gpr .rsp
  rdi : s₁.gpr .rdi = s₂.gpr .rdi
  rsi : s₁.gpr .rsi = s₂.gpr .rsi
  rdx : s₁.gpr .rdx = s₂.gpr .rdx
  rcx : s₁.gpr .rcx = s₂.gpr .rcx
  r8 : s₁.gpr .r8 = s₂.gpr .r8
  r9 : s₁.gpr .r9 = s₂.gpr .r9
  arg : stackArg s₁ 0 = stackArg s₂ 0
  syms : ∀ x ∈ cs, s₁.syms x.1 = s₂.syms x.1
  same : abi.sameWorld s₁ s₂
  leak : ((I.anyResult s₁.mem (s₁.gpr .rsi) (s₁.gpr .rdx) (s₁.gpr .rcx).toNat (s₁.gpr .r9).toNat).map
      (·.2)).getD 0 :: Spec.HashFns.tableWords s₁.mem (stackArg s₁ 0) =
    ((I.anyResult s₂.mem (s₂.gpr .rsi) (s₂.gpr .rdx) (s₂.gpr .rcx).toNat (s₂.gpr .r9).toNat).map
      (·.2)).getD 0 :: Spec.HashFns.tableWords s₂.mem (stackArg s₂ 0)

theorem apub_cons {I : Spec.Ecdsa.Rfc6979.Instance} {cs : List (String × List (BitVec 64))}
    {c : String × List (BitVec 64)} {cs' : List (String × List (BitVec 64))} (hcs : cs = c :: cs') {s₁ s₂ : State}
    (h : (I.signAnyContract (abi.withConsts cs) 408).pub s₁ s₂) : APub I cs s₁ s₂ := by
  subst hcs
  sig_pub [Spec.Ecdsa.Rfc6979.Instance.signAnyContract, Spec.Ecdsa.Rfc6979.Instance.signAnySig, abi, argRegs,
    Abi.withConsts, stackBelow, stackArgs_one] at h
  obtain ⟨rsp, hc, hcs, same, leak, rdi, rsi, rdx, rcx, r8, r9, arg⟩ := h
  exact ⟨rsp, rdi, rsi, rdx, rcx, r8, r9, arg, List.forall_mem_cons.mpr ⟨hc, hcs⟩, same, leak⟩

theorem apub_nil {I : Spec.Ecdsa.Rfc6979.Instance} {s₁ s₂ : State}
    (h : (I.signAnyContract (abi.withConsts []) 408).pub s₁ s₂) : APub I [] s₁ s₂ := by
  sig_pub [Spec.Ecdsa.Rfc6979.Instance.signAnyContract, Spec.Ecdsa.Rfc6979.Instance.signAnySig, abi, argRegs,
    Abi.withConsts, stackBelow, stackArgs_one] at h
  obtain ⟨rsp, same, leak, rdi, rsi, rdx, rcx, r8, r9, arg⟩ := h
  exact ⟨rsp, rdi, rsi, rdx, rcx, r8, r9, arg, (fun _ h => by cases h), same, leak⟩

/-- The public data of the shared contract, by name. -/
theorem apub_of {I : Spec.Ecdsa.Rfc6979.Instance} {cs : List (String × List (BitVec 64))} {s₁ s₂ : State}
    (h : (I.signAnyContract (abi.withConsts cs) 408).pub s₁ s₂) : APub I cs s₁ s₂ := by
  cases cs with
  | nil => exact apub_nil h
  | cons c cs => exact apub_cons rfl h

end VG.Proof.Ecdsa.Rfc6979.X86_64
