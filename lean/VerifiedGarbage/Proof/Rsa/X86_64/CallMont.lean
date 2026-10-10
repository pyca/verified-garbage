import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdxMont

/-!
# Montgomery multiplication by calls, on x86-64

What the x86-64 functions that call `vg_rsa_mont_mul` or
`vg_rsa_mont_mul_adx` share (`Calls.lean`, and RSA key generation's
`vg_rsa_keygen_candidate`): the calls, and `Verified.of_inline` for a
contract `Sig.contract` builds.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- Montgomery multiplication by calls of `name`, whose code is `body`;
`mont` is what the calls run as, inlined. -/
structure CallMont where
  name : String
  body : Prog isa
  mont : Mont

/-- The call of `[o] = [a] [b] R⁻¹ mod m`. -/
def CallMont.mm (M : CallMont) : Nat → Nat → Nat → Prog isa := Impl.Bignum.X86_64.MontFn.call M.name M.body

/-- By calls of `vg_rsa_mont_mul`. -/
def CallMont.base : CallMont := ⟨"vg_rsa_mont_mul", Impl.Bignum.X86_64.MontFn.mulBase, Mont.fnBase⟩

/-- By calls of `vg_rsa_mont_mul_adx`. -/
def CallMont.adx : CallMont := ⟨"vg_rsa_mont_mul_adx", Impl.Bignum.X86_64.MontFn.mulAdx, Mont.fnAdx⟩

/-- `Verified.of_inline` for a contract `Sig.contract` builds with 8 bytes
of stack, from the shared contract `k₀` it implies. -/
theorem Verified.of_inline_sig {c : Prog isa} (hc : c.InlineOk = true) {k₀ k : Contract isa}
    (hcor : ∀ s, k₀.pre s → ∃ t s', Exec isa c.inline s t s' ∧ abiPreserved s s' ∧ k₀.post s s')
    (hct : ConstantTime isa k₀.pre k₀.pub c.inline) (himp : k₀.Implies k)
    (hclear : ∀ s, k.pre s → Clear (hole (s.gpr .rsp)) s)
    (hrsp : ∀ s₁ s₂, k.pre s₁ → k.pre s₂ → k.pub s₁ s₂ → s₁.gpr .rsp = s₂.gpr .rsp)
    (hpatch : ∀ s b hv u, k₀.pre s → Clear (hole (s.gpr .rsp)) s → k₀.post s b →
      k₀.post s (b.patch (hole (s.gpr .rsp)) hv u)) : Verified target c k :=
  Verified.of_inline hc hcor hct himp hclear (fun s b hv u hs hp => hpatch s b hv u (himp.pre s hs) (hclear s hs) hp)
    hrsp

end VG.Proof.Rsa.X86_64
