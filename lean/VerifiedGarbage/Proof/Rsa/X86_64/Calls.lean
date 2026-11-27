module

public import VerifiedGarbage.Proof.Rsa.X86_64.InvLaw
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtContract
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
public import VerifiedGarbage.Proof.Bignum.X86_64.PcCode
import VerifiedGarbage.Proof.Rsa.X86_64.CallMont
import VerifiedGarbage.Proof.Bignum.Amm52
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
public import VerifiedGarbage.Proof.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Impl.Bignum.X86_64.MontFn

/-! ### `Bignum.X86_64.PcFn`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86_64.PcVerified`, which this module and modules that import it used -/

section

/-!
# `vg_rsa_public_precompute` on x86-64: verified against the shared contract

`pcContract` states the shared contract on the registers;
`pcSatState`, a state it allows.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Rsa.X86_64

/-- A state meeting `pcContract.pre`: a 512-bit modulus, `pre` at `0x1000`
and the working space at `0x4000`. -/
def pcSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 64 | .r8 => 0x4000 | .r9 => 1056
    | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 64⟩]
  wr := [⟨0x1000, 128⟩, ⟨0x4000, 8448⟩]

end VG.Proof.Bignum.X86_64

end

end

/-!
# `vg_rsa_public_precompute` on x86-64: its shared contract, with 8 bytes of stack

`pcContract` implies `Spec.Rsa.publicPrecomputeContract` with the stack its
calls of Montgomery multiplication use, a return address
(`precompute_implies8`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Bignum.X86_64.MontFn

theorem precompute_implies8 : pcContract.Implies (Spec.Rsa.publicPrecomputeContract abi 8) where
  pre := by
    intro s h
    sig_pre [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, pcContract, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, pcContract, List.append_eq]
    sig_and_intros
    sig_close
  post := by sig_implies_post [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, pcContract, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, pcContract, List.append_eq] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9⟩ := h
    refine ⟨?_, (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, pcContract, List.append_eq] [pcSatState] using pcSatState

end VG.Proof.Bignum.X86_64

end

end

/-! ### `Rsa.X86_64.CallPatch`, which this module and modules that import it used -/

section

/-!
# The RSA functions' postconditions do not read the return address

What `ok_of_inline` and `Verified.of_inline` need of the contracts of the
x86-64 RSA functions that call `vg_rsa_mont_mul`: their postconditions read
memory only in their writable buffers, which a precondition with `Clear`
keeps off the 8 bytes below `rsp`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64

theorem pc_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64) (hs : pcContract.pre s)
    (hc : Clear (hole (s.gpr .rsp)) s) (hp : pcContract.post s b) :
    pcContract.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -, -, -, -, -, -, hn, -⟩ := hs
  have hm := Clear.miss_wr hc (by rw [hwr]; simp) hn (Nat.le_refl _)
  simp only [pcContract, State.patch_gpr] at hp ⊢
  rw [patch_mem, wordsAt_overlay fun i hi => hm i (by omega_using [hi])]
  exact hp

theorem crtP_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64) (hs : crtContractP.pre s)
    (hc : Clear (hole (s.gpr .rsp)) s) (hp : crtContractP.post s b) :
    crtContractP.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  have hn : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hl, -⟩ := hs
  have hm := Clear.miss_wr hc (by rw [hwr]; simp) hn (Nat.le_of_eq hl.symm)
  simp only [crtContractP, crtContract, State.patch_gpr] at hp ⊢
  rw [patch_mem, written_overlay hm]
  exact hp

end VG.Proof.Bignum.X86_64

end

end

/-!
# The x86-64 RSA functions, with Montgomery multiplication by calls

Each of `vg_rsa_public_precompute` and `vg_rsa_private_crt` (and their
variants) calls
`vg_rsa_mont_mul` or `vg_rsa_mont_mul_adx` where it used to run their code
inlined. Its code `c` has the inlined code proven before as `c.inline`
(`hin`, which the registration evaluates); `Verified.of_inline` gives it
the contract with 8 bytes of stack, and `ok_of_inline`, `ct_of_inline` the
shared contract with the return address's slot clear (`Contract.clear`),
for its callers. (`vg_rsa_public_precomputed_checked` keeps its
multiplication inline: with a small public exponent it makes few
multiplications, and the calls' cost showed in its benchmarks.)
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.Rsa.X86_64

/-! ## `vg_rsa_public_precompute` -/

theorem pc_call_verified (M : Mont) (r : R2Impl M) {c : Prog isa} (hc : c.InlineOk = true)
    (hin : c.inline = Precompute.code M.mm r.code)
    (hmx : (Precompute.code M.mm r.code).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target c (Spec.Rsa.publicPrecomputeContract abi 8) :=
  Verified.of_inline_sig hc (hin ▸ pcCode_correct M r hmx) (hin ▸ pcCode_constantTime M r) precompute_implies8
    (fun _ h => Sig.clear_of_pre h) (fun _ _ _ _ h => Sig.rsp_of_pub h) pc_patch

/-! ## `vg_rsa_private_crt` -/

/-! ## `vg_rsa_private_crt_precomputed` -/

theorem crtP_call_ok {c : Prog isa} (hc : c.InlineOk = true)
    (hcor : ∀ s, crtContractP.pre s → ∃ t s', Exec isa c.inline s t s' ∧ abiPreserved s s' ∧ crtContractP.post s s') :
    ∀ s, crtContractP.clear.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ crtContractP.post s s' :=
  ok_of_inline hc hcor crtP_patch

theorem crtP_call_ct {c : Prog isa} (hc : c.InlineOk = true)
    (hcor : ∀ s, crtContractP.pre s → ∃ t s', Exec isa c.inline s t s' ∧ abiPreserved s s' ∧ crtContractP.post s s')
    (hct : ConstantTime isa crtContractP.pre crtContractP.pub c.inline) :
    ConstantTime isa crtContractP.clear.pre crtContractP.pub c :=
  ct_of_inline hc (fun s h => let ⟨t, s', e, _⟩ := hcor s h; ⟨t, s', e⟩) (fun _ _ h => h.1.1 .rsp (by simp)) hct

end VG.Proof.Rsa.X86_64
