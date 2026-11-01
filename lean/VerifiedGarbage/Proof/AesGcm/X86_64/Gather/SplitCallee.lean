module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Callee
public import VerifiedGarbage.Proof.Gcm.OutOfPlaceContract
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Impl.Aes.X86_64.Alloc

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: `vg_aes_gcm_seal_split` called

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_gather`
copies the slices after the first of a short text to the output and
encrypts the text by a call of `vg_aes_gcm_seal_split` (or of its instance
for the key context of `vg_aes_gcm_init_precomputed`) from the first slice
where it is and the rest at the output, an artifact with its working space
in a frame of its own; so what the proof needs of it is its shared contract
(`Spec/Gcm/OutOfPlace.lean`), in the terms of this target, as
`SealCallee.lean` does for `vg_aes_gcm_seal` (`splitK`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64
open VG.Impl.AesGcm.X86_64 (Fn)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args ret rounds)

/-! ## `vg_aes_gcm_seal_split(ctx = rdi, rounds = rsi, nonce = rdx, nonce_len = rcx, aad = r8,
aad_len = r9, src = [rsp + 8], src_len = [rsp + 16], dst = [rsp + 24], len = [rsp + 32],
tag = [rsp + 40])` -/

/-- What a call of `vg_aes_gcm_seal_split` needs, for a key context of kind
`M`: the layout of its shared contract with 2672 bytes of stack. -/
def splitPreK (M : CtxMode) (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, M.len⟩
  let nonce : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let aad : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let src : Region := ⟨arg s 0, (arg s 1).toNat⟩
  let data : Region := ⟨arg s 2, (arg s 3).toNat⟩
  let tag : Region := ⟨arg s 4, 16⟩
  let stk : Region := below (s.gpr .rsp) 2672
  s.rd = [ctx, nonce, aad, src, args s 5] ∧ s.wr = [data, tag] ∧
    ctx.Disjoint data ∧ ctx.Disjoint tag ∧ nonce.Disjoint data ∧ nonce.Disjoint tag ∧
    aad.Disjoint data ∧ aad.Disjoint tag ∧ src.Disjoint data ∧ src.Disjoint tag ∧ data.Disjoint tag ∧
    data.Disjoint (args s 5) ∧ tag.Disjoint (args s 5) ∧
    (ret s).Disjoint ctx ∧ (ret s).Disjoint nonce ∧ (ret s).Disjoint aad ∧ (ret s).Disjoint src ∧
    (ret s).Disjoint data ∧ (ret s).Disjoint tag ∧ (ret s).Disjoint (args s 5) ∧
    stk.Disjoint ctx ∧ stk.Disjoint nonce ∧ stk.Disjoint aad ∧ stk.Disjoint src ∧ stk.Disjoint data ∧
    stk.Disjoint tag ∧ stk.Disjoint (args s 5) ∧
    (s.gpr .rdi).toNat + M.len ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 64 ∧
    (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 64 ∧ (arg s 4).toNat + 16 ≤ 2 ^ 64 ∧
    2672 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 48 ≤ 2 ^ 64 ∧ rounds s ∧
    (arg s 1).toNat ≤ (arg s 3).toNat ∧ M.ok s.mem (s.gpr .rdi)

def splitPubK (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧ arg s₁ 2 = arg s₂ 2 ∧
    arg s₁ 3 = arg s₂ 3 ∧ arg s₁ 4 = arg s₂ 4

def splitK (M : CtxMode) : Contract isa where
  pre := splitPreK M
  post := (Proof.AesGcm.sealSplitX86_64M M).post
  pub := splitPubK

theorem splitSpec_pre {s : State} (h : splitPreK CtxMode.base s) :
    (Proof.Gcm.sealSplitContract X86_64.abi 2672).pre s := by
  sig_split h
  clear h
  sig_pre [Proof.Gcm.sealSplitContract, Proof.Gcm.sealSplitSig, Proof.Gcm.sealSplitPre, X86_64.abi, X86_64.argRegs]
  sig_reduce [Proof.Gcm.sealSplitContract, Proof.Gcm.sealSplitSig, Proof.Gcm.sealSplitPre, X86_64.abi, X86_64.argRegs,
    Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
    List.range, List.range.loop, VG.X86_64.below]
  sig_and_intros
  all_goals simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg,
    X86_64.stackArgAddr, VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.base, BitVec.setWidth_eq] at *
  all_goals first
    | with_reducible assumption
    | omega

theorem splitSpecP_pre {s : State} (h : splitPreK CtxMode.powers s) :
    (Proof.Gcm.sealSplitPrecomputedContract X86_64.abi 2672).pre s := by
  sig_split h
  have a₀ := h
  clear h
  sig_pre [Proof.Gcm.sealSplitPrecomputedContract, Proof.Gcm.sealSplitPrecomputedSig,
    Proof.Gcm.sealSplitPrecomputedPre, X86_64.abi, X86_64.argRegs]
  sig_reduce [Proof.Gcm.sealSplitPrecomputedContract, Proof.Gcm.sealSplitPrecomputedSig,
    Proof.Gcm.sealSplitPrecomputedPre, X86_64.abi, X86_64.argRegs, Proof.AesGcm.arg, Proof.AesGcm.args,
    Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
    VG.X86_64.below]
  sig_and_intros
  all_goals simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg,
    X86_64.stackArgAddr, VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.powers, BitVec.setWidth_eq] at *
  all_goals first
    | with_reducible assumption
    | omega

theorem splitSpec_post {M : CtxMode} {s s' : State} (h : (Proof.Gcm.sealSplitContract X86_64.abi 2672).post s s')
    (hR : rounds s) : (Proof.AesGcm.sealSplitX86_64M M).post s s' := by
  sig_post [Proof.Gcm.sealSplitContract, Proof.Gcm.sealSplitSig, Proof.Gcm.sealSplitPre, X86_64.abi, X86_64.argRegs,
    Proof.Gcm.sealSplitPost] at h
  sig_reduce [Proof.Gcm.sealSplitContract, Proof.Gcm.sealSplitSig, X86_64.abi, X86_64.argRegs, X86_64.stackArg,
    X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem splitSpecP_post {M : CtxMode} {s s' : State} (h : (Proof.Gcm.sealSplitPrecomputedContract X86_64.abi 2672).post s s')
    (hR : rounds s) : (Proof.AesGcm.sealSplitX86_64M M).post s s' := by
  sig_post [Proof.Gcm.sealSplitPrecomputedContract, Proof.Gcm.sealSplitPrecomputedSig,
    Proof.Gcm.sealSplitPrecomputedPre, X86_64.abi, X86_64.argRegs, Proof.Gcm.sealSplitPost] at h
  sig_reduce [Proof.Gcm.sealSplitPrecomputedContract, Proof.Gcm.sealSplitPrecomputedSig, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem splitSpec_pub {s₁ s₂ : State} (h : splitPubK s₁ s₂) :
    (Proof.Gcm.sealSplitContract X86_64.abi 2672).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂⟩ := h
  sig_pub [Proof.Gcm.sealSplitContract, Proof.Gcm.sealSplitSig, X86_64.abi, X86_64.argRegs]
  sig_reduce [Proof.Gcm.sealSplitContract, Proof.Gcm.sealSplitSig, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop, Proof.AesGcm.arg]
  simp only [Proof.AesGcm.arg, X86_64.stackArg, X86_64.stackArgAddr] at a₈ a₉ a₁₀ a₁₁ a₁₂
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

theorem splitSpecP_pub {s₁ s₂ : State} (h : splitPubK s₁ s₂) :
    (Proof.Gcm.sealSplitPrecomputedContract X86_64.abi 2672).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂⟩ := h
  sig_pub [Proof.Gcm.sealSplitPrecomputedContract, Proof.Gcm.sealSplitPrecomputedSig, X86_64.abi, X86_64.argRegs]
  sig_reduce [Proof.Gcm.sealSplitPrecomputedContract, Proof.Gcm.sealSplitPrecomputedSig, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop, Proof.AesGcm.arg]
  simp only [Proof.AesGcm.arg, X86_64.stackArg, X86_64.stackArgAddr] at a₈ a₉ a₁₀ a₁₁ a₁₂
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

/-! ## The function called -/

abbrev SplitFn (M : CtxMode) := CallFn (splitK M) 2672

/-- `vg_aes_gcm_seal_split` from its shared contract. -/
def SplitFn.ofBase (f : Fn) (hv : Verified X86_64.target f.code (Proof.Gcm.sealSplitContract X86_64.abi 2672))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 2672)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : SplitFn CtxMode.base :=
  CallFn.ofSpec f hv (fun _ h => splitSpec_pre h)
    (fun _ _ h h' => splitSpec_post (M := CtxMode.base) h' h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ _ h => splitSpec_pub h) sp xd mx

/-- `vg_aes_gcm_seal_split_precomputed` from its shared contract. -/
def SplitFn.ofPowers (f : Fn)
    (hv : Verified X86_64.target f.code (Proof.Gcm.sealSplitPrecomputedContract X86_64.abi 2672))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 2672)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : SplitFn CtxMode.powers :=
  CallFn.ofSpec f hv (fun _ h => splitSpecP_pre h)
    (fun _ _ h h' => splitSpecP_post (M := CtxMode.powers) h' h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ _ h => splitSpecP_pub h) sp xd mx

end VG.Proof.AesGcm.X86_64.Gather
