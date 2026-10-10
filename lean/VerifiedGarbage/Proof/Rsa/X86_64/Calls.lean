import VerifiedGarbage.Proof.Rsa.X86_64.Implies8
import VerifiedGarbage.Proof.Rsa.X86_64.CallPatch
import VerifiedGarbage.Proof.Bignum.X86_64.CrtVerified
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedBackend
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Verified
import VerifiedGarbage.Proof.Bignum.X86_64.PcFn
import VerifiedGarbage.Proof.Rsa.X86_64.CallMont

/-!
# The x86-64 RSA functions, with Montgomery multiplication by calls

Each of `vg_rsa_public_precompute`, `vg_rsa_private_crt` and
`vg_rsa_recover_primes` (and their variants) calls
`vg_rsa_mont_mul` or `vg_rsa_mont_mul_adx` where it used to run their code
inlined. Its code `c` has the inlined code proven before as `c.inline`
(`hin`, which the registration evaluates); `Verified.of_inline` gives it
the contract with 8 bytes of stack, and `ok_of_inline`, `ct_of_inline` the
shared contract with the return address's slot clear (`Contract.clear`),
for its callers. (`vg_rsa_public_precomputed_checked` keeps its
multiplication inline: with a small public exponent it makes few
multiplications, and the calls' cost showed in its benchmarks.)
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.Rsa.X86_64

/-! ## `vg_rsa_public_precompute` -/

theorem pc_call_verified (M : Mont) (r : R2Impl M) {c : Prog isa} (hc : c.InlineOk = true)
    (hin : c.inline = Precompute.code M.mm r.code)
    (hmx : (Precompute.code M.mm r.code).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target c (Spec.Rsa.publicPrecomputeContract abi 8) :=
  Verified.of_inline_sig hc (hin ▸ pcCode_correct M r hmx) (hin ▸ pcCode_constantTime M r) precompute_implies8
    (fun _ h => Sig.clear_of_pre h) (fun _ _ _ _ h => Sig.rsp_of_pub h) pc_patch

theorem pc_call_ok (M : Mont) (r : R2Impl M) {c : Prog isa} (hc : c.InlineOk = true)
    (hin : c.inline = Precompute.code M.mm r.code)
    (hmx : (Precompute.code M.mm r.code).allInstrs (fun i => !loadsMxcsr i) = true) :
    ∀ s, pcContract.clear.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ pcContract.post s s' :=
  ok_of_inline hc (hin ▸ pcCode_correct M r hmx) pc_patch

theorem pc_call_ct (M : Mont) (r : R2Impl M) {c : Prog isa} (hc : c.InlineOk = true)
    (hin : c.inline = Precompute.code M.mm r.code)
    (hmx : (Precompute.code M.mm r.code).allInstrs (fun i => !loadsMxcsr i) = true) :
    ConstantTime isa pcContract.clear.pre pcContract.pub c :=
  ct_of_inline hc (fun s h => let ⟨t, s', e, _⟩ := (hin ▸ pcCode_correct M r hmx) s h; ⟨t, s', e⟩)
    (fun _ _ h => h.1 .rsp (by simp)) (hin ▸ pcCode_constantTime M r)

/-! ## `vg_rsa_private_crt` -/

theorem crt_call_verified {c : Prog isa} (hc : c.InlineOk = true)
    (hcor : ∀ s, crtContract.pre s → ∃ t s', Exec isa c.inline s t s' ∧ abiPreserved s s' ∧ crtContract.post s s')
    (hct : ConstantTime isa crtContract.pre crtContract.pub c.inline) :
    Verified target c (Spec.Rsa.privateCrtContract abi 8) :=
  Verified.of_inline_sig hc hcor hct crt_implies8 (fun _ h => Sig.clear_of_pre h)
    (fun _ _ _ _ h => Sig.rsp_of_pub h) crt_patch

theorem crt_call_ok {c : Prog isa} (hc : c.InlineOk = true)
    (hcor : ∀ s, crtContract.pre s → ∃ t s', Exec isa c.inline s t s' ∧ abiPreserved s s' ∧ crtContract.post s s') :
    ∀ s, crtContract.clear.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ crtContract.post s s' :=
  ok_of_inline hc hcor crt_patch

theorem crt_call_ct {c : Prog isa} (hc : c.InlineOk = true)
    (hcor : ∀ s, crtContract.pre s → ∃ t s', Exec isa c.inline s t s' ∧ abiPreserved s s' ∧ crtContract.post s s')
    (hct : ConstantTime isa crtContract.pre crtContract.pub c.inline) :
    ConstantTime isa crtContract.clear.pre crtContract.pub c :=
  ct_of_inline hc (fun s h => let ⟨t, s', e, _⟩ := hcor s h; ⟨t, s', e⟩) (fun _ _ h => h.1 .rsp (by simp)) hct

/-! ## `vg_rsa_recover_primes` -/

theorem rp_call_verified (M : Mont) {c : Prog isa} (hc : c.InlineOk = true)
    (hin : c.inline = Keys.Recover.code M.mm)
    (hmx : (Keys.Recover.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target c (Spec.Rsa.recoverPrimesContract abi 8) :=
  Verified.of_inline_sig hc (hin ▸ rpCode_correct M hmx) (hin ▸ rpCode_constantTime M) rp_implies8
    (fun _ h => Sig.clear_of_pre h) (fun _ _ _ _ h => Sig.rsp_of_pub h) rp_patch

end VG.Proof.Rsa.X86_64
