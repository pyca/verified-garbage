module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Callee
import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Verified
public import VerifiedGarbage.Spec.Gcm.Powers8
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/-!
# AES-GCM out of place from a list of slices, with the powers, AArch64: the function called

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_gather_with_powers`
calls an implementation of `vg_aes_gcm_seal_with_powers` as an artifact
(`SealPwFn`), with its working space in a frame of its own, so what the proof
needs of it is its contract: its precondition from the layout the call gives
it (`callPre`) and the powers, its postcondition and its public data. For the
shared contract (`Spec.Gcm.sealWithPowersContract`, with 2592 bytes of
stack, `SealPwFn.ofSpec`), they are `sealPwSpec_pre`, `sealPwSpec_post` and
`sealPwSpec_pub`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.GatherPw

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH encryptWith Powers8Repr)

/-- What a call of `vg_aes_gcm_seal_with_powers(ctx = x0, rounds = x1,
nonce = x2, nonce_len = x3, aad = x4, aad_len = x5, data = x6, len = x7,
tag = [sp], pw = [sp + 8])` needs, but the powers. -/
def callPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let nonce : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let aad : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let data : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  let tag : Region := ⟨stackArg s 0, 16⟩
  let pw : Region := ⟨stackArg s 1, 128⟩
  let arg : Region := ⟨stackArgAddr s 0, 16⟩
  let stk : Region := ⟨s.sp - BitVec.ofNat 64 2592, 2592⟩
  s.rd = [ctx, nonce, aad, pw, arg] ∧ s.wr = [data, tag] ∧
    ctx.Disjoint data ∧ ctx.Disjoint tag ∧ nonce.Disjoint data ∧ nonce.Disjoint tag ∧
    aad.Disjoint data ∧ aad.Disjoint tag ∧ pw.Disjoint data ∧ pw.Disjoint tag ∧ data.Disjoint tag ∧
    data.Disjoint arg ∧ tag.Disjoint arg ∧
    stk.Disjoint ctx ∧ stk.Disjoint nonce ∧ stk.Disjoint aad ∧ stk.Disjoint pw ∧ stk.Disjoint data ∧
    stk.Disjoint tag ∧ stk.Disjoint arg ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + 16 ≤ 2 ^ 64 ∧ (stackArg s 1).toNat + 128 ≤ 2 ^ 64 ∧
    2592 ≤ s.sp.toNat ∧ s.sp.toNat + 16 ≤ 2 ^ 64 ∧
    ((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14)

/-- An implementation of `vg_aes_gcm_seal_with_powers`, by its contract `k`,
whose frames use at most the 2592 bytes below the stack pointer that the
contract reserves: `k` holds of a call as `callPre` lays it out with the
powers of the key context's hash subkey at `pw`, and gives `seal`'s result. -/
structure SealPwFn where
  fn : Impl.AesGcm.AArch64.Fn
  k : Contract isa
  verified : Verified AArch64.target fn.code k
  depth : 16 * fn.code.aarch64Depth ≤ 2592
  pre : ∀ s, callPre s → Powers8Repr s.mem (stackArg s 1) (ctxH s.mem (s.gpr .x0)) → k.pre s
  post : ∀ s s', k.post s s' → ((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14) →
    encryptWith (ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat) (ctxH s.mem (s.gpr .x0)) 16
        (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
        (bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) =
      (bytesAt s'.mem (s.gpr .x6) (s.gpr .x7).toNat, bytesAt s'.mem (stackArg s 0) 16)
  pub : ∀ s₁ s₂, s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧
    s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ s₁.sp = s₂.sp ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 → k.pub s₁ s₂

theorem stackArgs_two (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

theorem sealPwSpec_pre {s : State} (h : callPre s) (hp : Powers8Repr s.mem (stackArg s 1) (ctxH s.mem (s.gpr .x0))) :
    (Spec.Gcm.sealWithPowersContract AArch64.abi 2592).pre s := by
  obtain ⟨rd, wr, cd, ct, nd, nt, ad, at_, pd, pt, dt, darg, targ, sk, sn, sa, sp_, sd, st, sarg, o0, o2, o4, o6,
    otg, opw, w₁, w₂, hR⟩ := h
  sig_pre [Spec.Gcm.sealWithPowersContract, Spec.Gcm.sealWithPowersSig, Spec.Gcm.sealWithPowersPre,
    Spec.Gcm.sealPre, Spec.Gcm.sealSig, Spec.Gcm.withPowersParam, AArch64.abi, AArch64.argRegs,
    stackArgs_two, List.append_eq]
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, Gather.pairFacts_ro _ (by simp)]
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, Gather.filter_true', Gather.filter_false',
    Gather.filterMap_some', Gather.filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map,
    Bool.cond_false, Bool.cond_true, List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append,
    Sig.conj, Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false, List.cons_append, List.singleton_append]
  exact ⟨w₁, w₂, rd, wr, ⟨cd, ct, nd, nt, ad, at_, dt, pd.symm, darg, pt.symm, targ⟩, sk, sn, sa, sd, st, sp_,
    sarg, o0, o2, o4, o6, otg, opw, hR, hp⟩

theorem sealPwSpec_post {s s' : State} (h : (Spec.Gcm.sealWithPowersContract AArch64.abi 2592).post s s')
    (hR : (s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14) :
    encryptWith (ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat) (ctxH s.mem (s.gpr .x0)) 16
        (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
        (bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) =
      (bytesAt s'.mem (s.gpr .x6) (s.gpr .x7).toNat, bytesAt s'.mem (stackArg s 0) 16) := by
  sig_post [Spec.Gcm.sealWithPowersContract, Spec.Gcm.sealWithPowersSig, Spec.Gcm.sealWithPowersPost,
    Spec.Gcm.sealPost, Spec.Gcm.sealSig, Spec.Gcm.withPowersParam, AArch64.abi, AArch64.argRegs,
    stackArgs_two, List.append_eq] at h
  exact h hR

theorem sealPwSpec_pub {s₁ s₂ : State} (h : s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧
    s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ s₁.sp = s₂.sp ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1) :
    (Spec.Gcm.sealWithPowersContract AArch64.abi 2592).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁⟩ := h
  sig_pub [Spec.Gcm.sealWithPowersContract, Spec.Gcm.sealWithPowersSig, Spec.Gcm.sealSig,
    Spec.Gcm.withPowersParam, AArch64.abi, AArch64.argRegs, stackArgs_two, List.append_eq]
  sig_reduce [Spec.Gcm.sealWithPowersContract, Spec.Gcm.sealWithPowersSig, Spec.Gcm.sealSig,
    Spec.Gcm.withPowersParam, AArch64.abi, AArch64.argRegs]
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

/-- An implementation of `vg_aes_gcm_seal_with_powers`, by its shared
contract (`Spec.Gcm.sealWithPowersContract`, with 2592 bytes of stack). -/
def SealPwFn.ofSpec (fn : Impl.AesGcm.AArch64.Fn)
    (verified : Verified AArch64.target fn.code (Spec.Gcm.sealWithPowersContract AArch64.abi 2592))
    (depth : 16 * fn.code.aarch64Depth ≤ 2592) : SealPwFn where
  fn := fn
  k := Spec.Gcm.sealWithPowersContract AArch64.abi 2592
  verified := verified
  depth := depth
  pre _ h hp := sealPwSpec_pre h hp
  post _ _ h hR := sealPwSpec_post h hR
  pub _ _ h := sealPwSpec_pub h

end VG.Proof.AesGcm.AArch64.GatherPw
