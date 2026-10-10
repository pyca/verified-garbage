import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Callee

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: `vg_aes_gcm_seal` called

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_gather`
copies a short text to the output and encrypts it there by a call of
`vg_aes_gcm_seal` (or of its instance for the key context of
`vg_aes_gcm_init_precomputed`), an artifact with its working space in a
frame of its own, so what the proof needs of it is its shared contract
(`Spec/Gcm/Contract.lean`, `Spec/Gcm/Precomputed.lean`), in the terms of this
target: a contract whose precondition is the layout the call gives it
(`sealK`), which implies the shared one's, and whose postcondition is the
shared one's (`CallFn.ofSpec`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64
open VG.Impl.AesGcm.X86_64 (Fn)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args ret rounds)

/-! ## `vg_aes_gcm_seal(ctx = rdi, rounds = rsi, nonce = rdx, nonce_len = rcx, aad = r8,
aad_len = r9, data = [rsp + 8], len = [rsp + 16], tag = [rsp + 24])` -/

/-- What a call of `vg_aes_gcm_seal` needs, for a key context of kind `M`:
the layout of its shared contract with 2624 bytes of stack. -/
def sealPreK (M : CtxMode) (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, M.len⟩
  let nonce : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let aad : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let data : Region := ⟨arg s 0, (arg s 1).toNat⟩
  let tag : Region := ⟨arg s 2, 16⟩
  let stk : Region := below (s.gpr .rsp) 2624
  s.rd = [ctx, nonce, aad, args s 3] ∧ s.wr = [data, tag] ∧
    ctx.Disjoint data ∧ ctx.Disjoint tag ∧ nonce.Disjoint data ∧ nonce.Disjoint tag ∧
    aad.Disjoint data ∧ aad.Disjoint tag ∧ data.Disjoint tag ∧
    data.Disjoint (args s 3) ∧ tag.Disjoint (args s 3) ∧
    (ret s).Disjoint ctx ∧ (ret s).Disjoint nonce ∧ (ret s).Disjoint aad ∧ (ret s).Disjoint data ∧
    (ret s).Disjoint tag ∧ (ret s).Disjoint (args s 3) ∧
    stk.Disjoint ctx ∧ stk.Disjoint nonce ∧ stk.Disjoint aad ∧ stk.Disjoint data ∧ stk.Disjoint tag ∧
    stk.Disjoint (args s 3) ∧
    (s.gpr .rdi).toNat + M.len ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 64 ∧
    (arg s 2).toNat + 16 ≤ 2 ^ 64 ∧
    2624 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 32 ≤ 2 ^ 64 ∧ rounds s ∧ M.ok s.mem (s.gpr .rdi)

def sealPubK (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧ arg s₁ 2 = arg s₂ 2

def sealK (M : CtxMode) : Contract isa where
  pre := sealPreK M
  post := Proof.AesGcm.sealX86_64.post
  pub := sealPubK

theorem sealSpec_pre {s : State} (h : sealPreK CtxMode.base s) :
    (Spec.Gcm.sealContract X86_64.abi 2624).pre s := by
  sig_split h
  rename_i a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁ a₂₂ a₂₃ a₂₄ a₂₅ a₂₆ a₂₇
    a₂₈ a₂₉ a₃₀ a₃₁
  clear h
  sig_pre [Spec.Gcm.sealContract, Spec.Gcm.sealSig, Spec.Gcm.sealPre, X86_64.abi, X86_64.argRegs]
  sig_reduce [Spec.Gcm.sealContract, Spec.Gcm.sealSig, Spec.Gcm.sealPre, X86_64.abi, X86_64.argRegs,
    Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
    List.range, List.range.loop, VG.X86_64.below]
  sig_and_intros
  all_goals simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg,
    X86_64.stackArgAddr, VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.base] at *
  all_goals first
    | with_reducible assumption
    | omega

theorem sealSpecP_pre {s : State} (h : sealPreK CtxMode.powers s) :
    (Spec.Gcm.sealPrecomputedContract X86_64.abi 2624).pre s := by
  sig_split h
  rename_i a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁ a₂₂ a₂₃ a₂₄ a₂₅ a₂₆ a₂₇
    a₂₈ a₂₉ a₃₀ a₃₁
  have a₃₂ := h
  clear h
  sig_pre [Spec.Gcm.sealPrecomputedContract, Spec.Gcm.sealPrecomputedSig, Spec.Gcm.sealPrecomputedPre,
    X86_64.abi, X86_64.argRegs]
  sig_reduce [Spec.Gcm.sealPrecomputedContract, Spec.Gcm.sealPrecomputedSig, Spec.Gcm.sealPrecomputedPre,
    X86_64.abi, X86_64.argRegs, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg,
    X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below]
  sig_and_intros
  all_goals simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg,
    X86_64.stackArgAddr, VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.powers] at *
  all_goals first
    | with_reducible assumption
    | omega

theorem sealSpec_post {s s' : State} (hR : rounds s) (h : (Spec.Gcm.sealContract X86_64.abi 2624).post s s') :
    Proof.AesGcm.sealX86_64.post s s' := by
  sig_post [Spec.Gcm.sealContract, Spec.Gcm.sealSig, Spec.Gcm.sealPre, X86_64.abi, X86_64.argRegs,
    Spec.Gcm.sealPost] at h
  sig_reduce [Spec.Gcm.sealContract, Spec.Gcm.sealSig, X86_64.abi, X86_64.argRegs, X86_64.stackArg,
    X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem sealSpecP_post {s s' : State} (hR : rounds s)
    (h : (Spec.Gcm.sealPrecomputedContract X86_64.abi 2624).post s s') :
    Proof.AesGcm.sealX86_64.post s s' := by
  sig_post [Spec.Gcm.sealPrecomputedContract, Spec.Gcm.sealPrecomputedSig, Spec.Gcm.sealPrecomputedPre,
    X86_64.abi, X86_64.argRegs, Spec.Gcm.sealPost] at h
  sig_reduce [Spec.Gcm.sealPrecomputedContract, Spec.Gcm.sealPrecomputedSig, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem sealSpec_pub {s₁ s₂ : State} (h : sealPubK s₁ s₂) :
    (Spec.Gcm.sealContract X86_64.abi 2624).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀⟩ := h
  sig_pub [Spec.Gcm.sealContract, Spec.Gcm.sealSig, X86_64.abi, X86_64.argRegs]
  sig_reduce [Spec.Gcm.sealContract, Spec.Gcm.sealSig, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop, Proof.AesGcm.arg]
  simp only [Proof.AesGcm.arg, X86_64.stackArg, X86_64.stackArgAddr] at a₈ a₉ a₁₀
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

theorem sealSpecP_pub {s₁ s₂ : State} (h : sealPubK s₁ s₂) :
    (Spec.Gcm.sealPrecomputedContract X86_64.abi 2624).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀⟩ := h
  sig_pub [Spec.Gcm.sealPrecomputedContract, Spec.Gcm.sealPrecomputedSig, X86_64.abi, X86_64.argRegs]
  sig_reduce [Spec.Gcm.sealPrecomputedContract, Spec.Gcm.sealPrecomputedSig, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop, Proof.AesGcm.arg]
  simp only [Proof.AesGcm.arg, X86_64.stackArg, X86_64.stackArgAddr] at a₈ a₉ a₁₀
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

/-! ## The function called -/

abbrev SealFn (M : CtxMode) := CallFn (sealK M) 2624

/-- `vg_aes_gcm_seal` from its shared contract. -/
def SealFn.ofBase (f : Fn) (hv : Verified X86_64.target f.code (Spec.Gcm.sealContract X86_64.abi 2624))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 2624)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : SealFn CtxMode.base :=
  CallFn.ofSpec f hv (fun _ h => sealSpec_pre h)
    (fun _ _ h h' => sealSpec_post h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h')
    (fun _ _ h => sealSpec_pub h) sp xd mx

/-- `vg_aes_gcm_seal_precomputed` from its shared contract. -/
def SealFn.ofPowers (f : Fn)
    (hv : Verified X86_64.target f.code (Spec.Gcm.sealPrecomputedContract X86_64.abi 2624))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 2624)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : SealFn CtxMode.powers :=
  CallFn.ofSpec f hv (fun _ h => sealSpecP_pre h)
    (fun _ _ h h' => sealSpecP_post h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h')
    (fun _ _ h => sealSpecP_pub h) sp xd mx

end VG.Proof.AesGcm.X86_64.Gather
