module

public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256
import VerifiedGarbage.Proof.Framework.X86_64.ResidueTaintSum
import VerifiedGarbage.Proof.Sha256.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
public meta import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256
public meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueTaintSum
public meta import VerifiedGarbage.Proof.Sha256.X86_64.Lit
public meta import VerifiedGarbage.Proof.Framework.Lit
public meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# HMAC's `init` over SHA-224 and SHA-256 on x86-64 with the scalar compression function, without secret residue

The residue analysis of HMAC's `init` for a key of any length (`initCode`)
over SHA-224 and SHA-256 with this compression function: the variants of
`Proof/Variants/MdHash/X86_64.lean` with it take theirs from here
(`MdHash.hmacInitRes`), and the rest from `Sha256.lean`.

Their code differs only in the hash's `init` and `finalize` that it calls
and in their constants, so most of their analyses are the same: the calls of
`update`, the code after the two calls of `init` in HMAC's `init`, at the
two depths it runs at, and the clearing of the frame of the branch for long
keys are analysed once, as summaries (`rtaint_summary`), from the same taint
in each (`rtaint_site%`, from SHA-256's analysis), which the analysis of each hash
uses (`rtaint_decide_sum_weak`).
-/

@[expose] public section

namespace VG.Proof.Variants.MdHash.X86_64.Sha256Init

open Proof.Pbkdf2.Md.X86_64

/-! ## The summaries -/

/-- The weakening of the hints (the frame of the branch for long keys is the
same size in each). -/
abbrev weak : VG.X86_64.RTaint.FT → VG.X86_64.RTaint.FT := initHintWeak Sha256.variant.I

def updPre : VG.X86_64.RTaint.FT := rtaint_site% weak (initStart Sha256.variant.I) (initCode Sha256.variant.H Sha256.variant.I)
  (initUpd Sha256.variant.H) 0

rtaint_summary upd : weak updPre (initUpd Sha256.variant.H)

def tail0Pre : VG.X86_64.RTaint.FT := rtaint_site% weak (initStart Sha256.variant.I) (initCode Sha256.variant.H Sha256.variant.I)
  (initTail Sha256.variant.H) 0 using upd

rtaint_summary tail0 : weak tail0Pre (initTail Sha256.variant.H)

def tail1Pre : VG.X86_64.RTaint.FT := rtaint_site% weak (initStart Sha256.variant.I) (initCode Sha256.variant.H Sha256.variant.I)
  (initTail Sha256.variant.H) 1 using upd tail0

rtaint_summary tail1 : weak tail1Pre (initTail Sha256.variant.H)

def wipePre : VG.X86_64.RTaint.FT := rtaint_site% weak (initStart Sha256.variant.I) (initCode Sha256.variant.H Sha256.variant.I)
  (initWipe Sha256.variant.I) 0 using upd tail0 tail1

rtaint_summary wiped : weak wipePre (initWipe Sha256.variant.I)

/-! ## The analyses -/

def ks : List Nat := keep_for% Sha256.variant.I.initAnyKeyApi.sig (24 + anyFrame Sha256.variant.I)
  (initCode Sha256.variant.H Sha256.variant.I) []

/-- The residue analysis of HMAC's `init` over SHA-256: `MdHash.hmacInitReg`
follows it with `Impl.Scrub.X86_64.scrubTail`, which wipes the registers and
the granules `ks` of its stack. -/
def init : VG.X86_64.RScrub.Analysed Sha256.variant.I.initAnyKeyApi.sig (24 + anyFrame Sha256.variant.I) []
    (initCode Sha256.variant.H Sha256.variant.I) :=
  ⟨ks, VG.X86_64.RTaint.ok_of_resOkF
    (by rtaint_decide_sum_weak (initHintWeak Sha256.variant.I) [upd, tail0, tail1, wiped])⟩

def ks224 : List Nat := keep_for% Sha256.variant224.I.initAnyKeyApi.sig (24 + anyFrame Sha256.variant224.I)
  (initCode Sha256.variant224.H Sha256.variant224.I) []

/-- The residue analysis of HMAC's `init` over SHA-224: `MdHash.hmacInitReg`
follows it with `Impl.Scrub.X86_64.scrubTail`, which wipes the registers and
the granules `ks224` of its stack. -/
def init224 : VG.X86_64.RScrub.Analysed Sha256.variant224.I.initAnyKeyApi.sig (24 + anyFrame Sha256.variant224.I) []
    (initCode Sha256.variant224.H Sha256.variant224.I) :=
  ⟨ks224, VG.X86_64.RTaint.ok_of_resOkF
    (by rtaint_decide_sum_weak (initHintWeak Sha256.variant224.I) [upd, tail0, tail1, wiped])⟩

end VG.Proof.Variants.MdHash.X86_64.Sha256Init
