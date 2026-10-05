import VerifiedGarbage.Proof.Rsa.X86_64.PrivFrame
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCode

/-!
# Implementations of `vg_rsa_private_crt` on x86-64

A `CrtImpl` is what `vg_rsa_private_checked` needs of the implementation of
`vg_rsa_private_crt` it calls, so that its proof holds for each of them:
each is a variant of the interface `RsaPrivateCrt` on x86-64
(`Variants/RsaPrivateCrt/X86_64/`), and `vg_rsa_private_checked`
(`Generic/RsaPrivateCrt/X86_64/Rsa.lean`) is emitted once for each. Every
implementation is proven against `crtContract`, and makes no calls. It
comes with the Montgomery multiplication of the implementations of
`vg_rsa_public_precompute` and `vg_rsa_public_precomputed_checked` that
check its result, which need no more CPU features.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.Rsa.X86_64

/-- An implementation of `vg_rsa_private_crt` on x86-64. -/
structure CrtImpl where
  /-- Its symbol and code. -/
  name : String
  code : Prog isa
  /-- It makes no calls. -/
  depth : code.depth = 0
  ok : ∀ s, crtContract.pre s → ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ crtContract.post s s'
  ct : ConstantTime isa crtContract.pre crtContract.pub code
  /-- It never writes the stack pointer. -/
  nosp : NoSp code
  /-- The Montgomery multiplication of `vg_rsa_public_precompute` and
  `vg_rsa_public_precomputed_checked`, and the suffix of their names. -/
  mont : Mont
  montSuffix : String
  pcMx : (Precompute.code mont.mm).allInstrs (fun i => !loadsMxcsr i) = true
  pdMx : (Precomputed.code mont.mm).allInstrs (fun i => !loadsMxcsr i) = true
  pcNosp : NoSp (Precompute.code mont.mm)
  pdNosp : NoSp (Checked.precomputedChecked mont.mm)
  pcDepth : (Precompute.code mont.mm).depth = 0
  pdDepth : (Checked.precomputedChecked mont.mm).depth = 0
  /-- What the names of `vg_rsa_private_checked`'s instances end with (e.g.
  `_adx`; nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code and that of the public operation require,
  which `vg_rsa_private_checked` requires too. -/
  features : List String

/-- `NoSp` by evaluating the code. -/
theorem noSp_of {c : Prog isa} (h : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true) : NoSp c := by
  rw [Code.allInstrs_eq] at h
  exact fun i hi => by simpa using List.all_eq_true.mp h i hi

end VG.Proof.Rsa.X86_64
