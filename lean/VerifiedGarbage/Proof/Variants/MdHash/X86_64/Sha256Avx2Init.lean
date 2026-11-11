module

public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256Avx2
import VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
public meta import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256Avx2
public meta import VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Lit
public meta import VerifiedGarbage.Proof.Framework.Lit
public meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

-- separate module: it would double the time and the memory of `Sha256Avx2.lean`

/-!
# HMAC's `init` over SHA-224 and SHA-256 on x86-64 with AVX2 and BMI, without secret residue

The residue analysis of HMAC's `init` for a key of any length (`initCode`)
over SHA-224 and SHA-256 with this compression function, a branch at a time
(`Proof.Pbkdf2.Md.X86_64.initRes_ok`): the variants of
`Proof/Variants/MdHash/X86_64.lean` with it take theirs from here
(`MdHash.hmacInitRes`), and the rest from `Sha256Avx2.lean`.
-/

@[expose] public section

namespace VG.Proof.Variants.MdHash.X86_64.Sha256Avx2Init

open Proof.Pbkdf2.Md.X86_64

def ks : List Nat := keep_for% Sha256Avx2.variant.I.initAnyKeyApi.sig (24 + anyFrame Sha256Avx2.variant.I)
  (initCode Sha256Avx2.variant.H Sha256Avx2.variant.I) []

/-- The analysis of the branch for long keys stops between its two parts here. -/
def longMid : VG.X86_64.RTaint.FT := init_long_mid% Sha256Avx2.variant.H Sha256Avx2.variant.I

theorem longPre : InitLongPre Sha256Avx2.variant.H Sha256Avx2.variant.I longMid :=
  ⟨_, by taint_decide_weak (initHintWeak Sha256Avx2.variant.I)⟩

theorem longPost : InitLongPost Sha256Avx2.variant.H Sha256Avx2.variant.I ks longMid :=
  ⟨_, by taint_decide_weak (initHintWeak Sha256Avx2.variant.I)⟩

theorem long : InitLongOk Sha256Avx2.variant.H Sha256Avx2.variant.I ks := initLong_of (by decide) longPre longPost

theorem short : InitShortOk Sha256Avx2.variant.H Sha256Avx2.variant.I ks :=
  ⟨by decide, _, by taint_decide⟩

/-- The residue analysis of HMAC's `init` over SHA-256: `MdHash.hmacInitReg`
follows it with `Impl.Scrub.X86_64.scrubTail`, which wipes the registers and
the granules `ks` of its stack. -/
def init : VG.X86_64.RScrub.Analysed Sha256Avx2.variant.I.initAnyKeyApi.sig (24 + anyFrame Sha256Avx2.variant.I) []
    (initCode Sha256Avx2.variant.H Sha256Avx2.variant.I) :=
  ⟨ks, initRes_ok long short⟩

def ks224 : List Nat := keep_for% Sha256Avx2.variant224.I.initAnyKeyApi.sig (24 + anyFrame Sha256Avx2.variant224.I)
  (initCode Sha256Avx2.variant224.H Sha256Avx2.variant224.I) []

/-- The analysis of the branch for long keys stops between its two parts here. -/
def longMid224 : VG.X86_64.RTaint.FT := init_long_mid% Sha256Avx2.variant224.H Sha256Avx2.variant224.I

theorem longPre224 : InitLongPre Sha256Avx2.variant224.H Sha256Avx2.variant224.I longMid224 :=
  ⟨_, by taint_decide_weak (initHintWeak Sha256Avx2.variant224.I)⟩

theorem longPost224 : InitLongPost Sha256Avx2.variant224.H Sha256Avx2.variant224.I ks224 longMid224 :=
  ⟨_, by taint_decide_weak (initHintWeak Sha256Avx2.variant224.I)⟩

theorem long224 : InitLongOk Sha256Avx2.variant224.H Sha256Avx2.variant224.I ks224 := initLong_of (by decide) longPre224 longPost224

theorem short224 : InitShortOk Sha256Avx2.variant224.H Sha256Avx2.variant224.I ks224 :=
  ⟨by decide, _, by taint_decide⟩

/-- The residue analysis of HMAC's `init` over SHA-224: `MdHash.hmacInitReg`
follows it with `Impl.Scrub.X86_64.scrubTail`, which wipes the registers and
the granules `ks224` of its stack. -/
def init224 : VG.X86_64.RScrub.Analysed Sha256Avx2.variant224.I.initAnyKeyApi.sig (24 + anyFrame Sha256Avx2.variant224.I) []
    (initCode Sha256Avx2.variant224.H Sha256Avx2.variant224.I) :=
  ⟨ks224, initRes_ok long224 short224⟩

end VG.Proof.Variants.MdHash.X86_64.Sha256Avx2Init
