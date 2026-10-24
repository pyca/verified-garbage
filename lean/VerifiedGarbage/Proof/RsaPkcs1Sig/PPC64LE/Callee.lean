module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.Frame
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubVerified
import VerifiedGarbage.Proof.Framework.Mem

/-!
# The RSA operation the signatures call, on PPC64LE

Untrusted: everything here is checked by Lean. `vg_rsa_pkcs1_verify_precomputed`
and `vg_rsa_pkcs1_recover_precomputed` call `vg_rsa_public_precomputed_checked`
(`out = r3, out_len = r4, pre = r5, pre_len = r6, e = r7, e_len = r8,
input = r9, input_len = r10, scratch, scratch_len`, the last two on the
stack) by its shared contract (`Spec.Rsa.publicPrecomputedCheckedContract`,
with no stack: it has no frames), which its artifact proves
(`Proof.Bignum.PPC64LE.Pub.publicChecked_verified`). As on AArch64
(`Proof/RsaPkcs1Sig/AArch64/Callee.lean`), the call lemmas evaluate that
contract (`sig_pre`, `sig_post`) into facts about the registers at the call
(`PdOk`, `pdCall`, `pdCallCT`), so the callers' proofs never see
`Sig.contract`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE

open VG VG.PPC64LE

theorem stackArgs_two (s : State) :
    List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

/-- The regions a call of `vg_rsa_public_precomputed_checked` reads and
writes: `pre`, `e`, the input and its two stack arguments; `out` and the
working space. -/
abbrev pdRd (t : State) : List Region :=
  [⟨t.gpr .r5, (t.gpr .r6).toNat * 8⟩, ⟨t.gpr .r7, (t.gpr .r8).toNat⟩, ⟨t.gpr .r9, (t.gpr .r10).toNat⟩,
    ⟨stackArgAddr t 0, 16⟩]

abbrev pdWr (t : State) : List Region :=
  [⟨t.gpr .r3, (t.gpr .r4).toNat⟩, ⟨stackArg t 0, (stackArg t 1).toNat * 8⟩]

/-- What the buffers of a call of `vg_rsa_public_precomputed_checked` need:
they are apart where one is written, from the arguments on the stack, and do
not wrap around. `o`, `n`, `e`, `i`, `sc`, `a`: `out`, `pre`, `e`, the input,
the working space and the stack arguments. -/
structure PdLay (o n e i sc a : Region) : Prop where
  on : o.Disjoint n
  oe : o.Disjoint e
  oi : o.Disjoint i
  os : o.Disjoint sc
  oa : o.Disjoint a
  ns : n.Disjoint sc
  es : e.Disjoint sc
  is : i.Disjoint sc
  sa : sc.Disjoint a
  wo : o.base.toNat + o.len ≤ 2 ^ 64
  wn : n.base.toNat + n.len ≤ 2 ^ 64
  we : e.base.toNat + e.len ≤ 2 ^ 64
  wi : i.base.toNat + i.len ≤ 2 ^ 64
  ws : sc.base.toNat + sc.len ≤ 2 ^ 64

/-- What a call of `vg_rsa_public_precomputed_checked` needs at the call:
the precomputed values of a modulus of `k` bytes (`r6` words at `r5`), `e`
(`r8` bytes) at `r7`, the input at `r9`, `out` at `r3` (`k = r4` bytes); the
working space and its length in words are the two doublewords at `sp + 96`. -/
structure PdOk (t : State) : Prop where
  hl : PdLay ⟨t.gpr .r3, (t.gpr .r4).toNat⟩ ⟨t.gpr .r5, (t.gpr .r6).toNat * 8⟩ ⟨t.gpr .r7, (t.gpr .r8).toNat⟩
    ⟨t.gpr .r9, (t.gpr .r10).toNat⟩ ⟨stackArg t 0, (stackArg t 1).toNat * 8⟩ ⟨stackArgAddr t 0, 16⟩
  sp : t.sp.toNat + 112 ≤ 2 ^ 64
  hrd : Covers (pdRd t) (t.rd ++ t.wr)
  hwr : Covers (pdWr t) t.wr
  hk : Spec.Rsa.lenValid (t.gpr .r4).toNat
  h6 : (t.gpr .r6).toNat = Spec.Rsa.precomputedWords (t.gpr .r4).toNat
  h10 : (t.gpr .r10).toNat = (t.gpr .r4).toNat
  he1 : 1 ≤ (t.gpr .r8).toNat
  he2 : (t.gpr .r8).toNat ≤ (t.gpr .r4).toNat
  hs : Spec.Rsa.publicScratchWords (t.gpr .r4).toNat ≤ (stackArg t 1).toNat

theorem PdOk.pre {t : State} (h : PdOk t) :
    (Spec.Rsa.publicPrecomputedCheckedContract abi).pre (t.callEntry.withRegions (pdRd t) (pdWr t)) := by
  have hl := h.hl
  sig_pre [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs,
    stackArgs_two, List.append_eq]
  simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false,
    Bool.true_or, Bool.false_or, List.cons_append, List.nil_append, Sig.conj, List.append_nil]
  exact ⟨by have := h.sp; omega, rfl, rfl, hl.on, hl.oe, ⟨hl.oi, hl.os, hl.oa, hl.ns, hl.es, hl.is, hl.sa⟩,
    hl.wo, hl.wn, hl.we, hl.wi, hl.ws, h.hk, h.h6, h.h10, h.he1, h.he2, h.hs⟩

/-- The correctness of `vg_rsa_public_precomputed_checked`, from its artifact. -/
theorem pd_correct : ∀ s, (Spec.Rsa.publicPrecomputedCheckedContract abi).pre s →
    ∃ t s', Exec isa Impl.Bignum.PPC64LE.PublicChecked.publicChecked s t s' ∧ abiPreserved s s' ∧
      (Spec.Rsa.publicPrecomputedCheckedContract abi).post s s' :=
  Proof.Bignum.PPC64LE.Pub.publicChecked_verified.1

/-- `vg_rsa_public_precomputed_checked` has no frames. -/
theorem pd_noFrames : Impl.Bignum.PPC64LE.PublicChecked.publicChecked.noFrames = true := by decide +kernel

/-- A call of `vg_rsa_public_precomputed_checked`. Its result is that of any
modulus whose values `pre` holds. -/
theorem pdCall {t : State} {Q : State → Prop} (h : PdOk t)
    (hQ : ∀ s', s'.rd = t.rd → s'.wr = t.wr → s'.sp = t.sp → Frame (pdWr t) t.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = t.gpr r) →
      (∀ nB : List Byte, nB.length = (t.gpr .r4).toNat →
        Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt t.mem (t.gpr .r5) (t.gpr .r6).toNat) →
        Spec.Rsa.written s'.mem (t.gpr .r3) (t.gpr .r4).toNat ((s'.gpr .r3).setWidth 32)
          (Spec.Rsa.publicOpChecked nB (Spec.Rsa.bytesAt t.mem (t.gpr .r7) (t.gpr .r8).toNat)
            (Spec.Rsa.bytesAt t.mem (t.gpr .r9) (t.gpr .r4).toNat))) → Q s') :
    WP isa Impl.RsaPkcs1Sig.PPC64LE.pubCall t Q := by
  refine WP.call (k := Spec.Rsa.publicPrecomputedCheckedContract abi) pd_correct h.pre
    (Covers.append_left (Covers.trans h.hrd (Covers.refl _)) (Covers.right h.hwr)) h.hwr ?_ pd_noFrames
  intro s' hrd' hwr' hsp' hf hpres _ hpost
  sig_post [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs,
    stackArgs_two, List.append_eq] at hpost
  exact hQ s' hrd' hwr' hsp' hf hpres hpost

/-- What two runs agree on at a call of `vg_rsa_public_precomputed_checked`:
the stack pointer, the argument registers and its two stack arguments. -/
structure ArgsEq (t₁ t₂ : State) : Prop where
  sp : t₁.sp = t₂.sp
  gpr : ∀ r ∈ argRegs, t₁.gpr r = t₂.gpr r
  a0 : stackArg t₁ 0 = stackArg t₂ 0
  a1 : stackArg t₁ 1 = stackArg t₂ 1

/-- Two calls of `vg_rsa_public_precomputed_checked` leak alike if their
arguments, the precomputed values and the bytes of `e` agree. -/
theorem pdCallCT {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → PdOk t₁ ∧ PdOk t₂ ∧ ArgsEq t₁ t₂ ∧
      Spec.Rsa.wordsAt t₁.mem (t₁.gpr .r5) (t₁.gpr .r6).toNat =
        Spec.Rsa.wordsAt t₂.mem (t₂.gpr .r5) (t₂.gpr .r6).toNat ∧
      Spec.Rsa.bytesAt t₁.mem (t₁.gpr .r7) (t₁.gpr .r8).toNat =
        Spec.Rsa.bytesAt t₂.mem (t₂.gpr .r7) (t₂.gpr .r8).toNat) :
    RelCT isa P Impl.RsaPkcs1Sig.PPC64LE.pubCall fun _ _ => True := by
  refine RelCT.callEx pd_correct Proof.Bignum.PPC64LE.Pub.publicChecked_verified.2.1 fun t₁ t₂ hp => ?_
  obtain ⟨h₁, h₂, he, hn, hE⟩ := hP t₁ t₂ hp
  refine ⟨_, _, _, _, h₁.pre, h₂.pre, ?_,
    Covers.append_left (Covers.trans h₁.hrd (Covers.refl _)) (Covers.right h₁.hwr), h₁.hwr,
    Covers.append_left (Covers.trans h₂.hrd (Covers.refl _)) (Covers.right h₂.hwr), h₂.hwr⟩
  sig_pub [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs,
    stackArgs_two, List.append_eq]
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  exact ⟨he.sp, by rw [hn, hE], he.gpr _ (by decide), he.gpr _ (by decide), he.gpr _ (by decide),
    he.gpr _ (by decide), he.gpr _ (by decide), he.gpr _ (by decide), he.gpr _ (by decide),
    he.gpr _ (by decide), he.a0, he.a1⟩

end VG.Proof.RsaPkcs1Sig.PPC64LE
