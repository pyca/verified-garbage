module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512
import VerifiedGarbage.Proof.Framework.X86_64.ResidueTaintSum
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
public meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512
public meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueTaintSum
public meta import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
public meta import VerifiedGarbage.Proof.Framework.Lit
public meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# HMAC's `init` over the SHA-512 family on x86-64 with the scalar compression function, without secret residue

The residue analysis of HMAC's `init` for a key of any length (`initCode`)
over SHA-384, SHA-512, SHA-512/224 and SHA-512/256 with this compression function: the variants of
`Proof/Variants/MdHash/X86_64.lean` with it take theirs from here
(`MdHash.hmacInitRes`), and the rest from `Sha512.lean`.

Their code differs only in the hash's `init` and `finalize` that it calls
and in their constants, so most of their analyses are the same: the calls of
`update`, the code after the two calls of `init` in HMAC's `init`, at the
two depths it runs at, and the clearing of the frame of the branch for long
keys are analysed once, as summaries (`rtaint_summary`), from the same taint
in each (`rtaint_site%`, from SHA-384's analysis), which the analysis of each hash
uses (`rtaint_decide_sum_weak`).
-/

@[expose] public section

namespace VG.Proof.Variants.MdHash.X86_64.Sha512Init

open Proof.Pbkdf2.Md.X86_64

abbrev compress : Proof.Sha512.X86_64.Compress := Proof.Sha512.X86_64.Compress.scalar

/-- SHA-384 with this compression function, whose HMAC's `init` is the variant's. -/
abbrev base384 : MdHash := Proof.Pbkdf2.Md.X86_64.Sha512.sha384 compress

/-- SHA-512 with this compression function, whose HMAC's `init` is the variant's. -/
abbrev base512 : MdHash := Proof.Pbkdf2.Md.X86_64.Sha512.sha512 compress

/-- SHA-512/224 with this compression function, whose HMAC's `init` is the variant's. -/
abbrev base512_224 : MdHash := Proof.Pbkdf2.Md.X86_64.Sha512.sha512_224 compress

/-- SHA-512/256 with this compression function, whose HMAC's `init` is the variant's. -/
abbrev base512_256 : MdHash := Proof.Pbkdf2.Md.X86_64.Sha512.sha512_256 compress

/-! ## The summaries -/

/-- The weakening of the hints (the frame of the branch for long keys is the
same size in each). -/
abbrev weak : VG.X86_64.RTaint.FT → VG.X86_64.RTaint.FT := initHintWeak base384.I

def updPre : VG.X86_64.RTaint.FT := rtaint_site% weak (initStart base384.I) (initCode base384.H base384.I)
  (initUpd base384.H) 0

rtaint_summary upd : weak updPre (initUpd base384.H)

def tail0Pre : VG.X86_64.RTaint.FT := rtaint_site% weak (initStart base384.I) (initCode base384.H base384.I)
  (initTail base384.H) 0 using upd

rtaint_summary tail0 : weak tail0Pre (initTail base384.H)

def tail1Pre : VG.X86_64.RTaint.FT := rtaint_site% weak (initStart base384.I) (initCode base384.H base384.I)
  (initTail base384.H) 1 using upd tail0

rtaint_summary tail1 : weak tail1Pre (initTail base384.H)

def wipePre : VG.X86_64.RTaint.FT := rtaint_site% weak (initStart base384.I) (initCode base384.H base384.I)
  (initWipe base384.I) 0 using upd tail0 tail1

rtaint_summary wiped : weak wipePre (initWipe base384.I)

/-! ## The analyses -/

def ks384 : List Nat := keep_for% base384.I.initAnyKeyApi.sig (24 + anyFrame base384.I)
  (initCode base384.H base384.I) []

/-- The residue analysis of HMAC's `init` over SHA-384: `MdHash.hmacInitReg`
follows it with `Impl.Scrub.X86_64.scrubTail`, which wipes the registers and
the granules `ks384` of its stack. -/
def init384 : VG.X86_64.RScrub.Analysed base384.I.initAnyKeyApi.sig (24 + anyFrame base384.I) []
    (initCode base384.H base384.I) :=
  ⟨ks384, VG.X86_64.RTaint.ok_of_resOkF
    (by rtaint_decide_sum_weak (initHintWeak base384.I) [upd, tail0, tail1, wiped])⟩

def ks512 : List Nat := keep_for% base512.I.initAnyKeyApi.sig (24 + anyFrame base512.I)
  (initCode base512.H base512.I) []

/-- The residue analysis of HMAC's `init` over SHA-512: `MdHash.hmacInitReg`
follows it with `Impl.Scrub.X86_64.scrubTail`, which wipes the registers and
the granules `ks512` of its stack. -/
def init512 : VG.X86_64.RScrub.Analysed base512.I.initAnyKeyApi.sig (24 + anyFrame base512.I) []
    (initCode base512.H base512.I) :=
  ⟨ks512, VG.X86_64.RTaint.ok_of_resOkF
    (by rtaint_decide_sum_weak (initHintWeak base512.I) [upd, tail0, tail1, wiped])⟩

def ks512_224 : List Nat := keep_for% base512_224.I.initAnyKeyApi.sig (24 + anyFrame base512_224.I)
  (initCode base512_224.H base512_224.I) []

/-- The residue analysis of HMAC's `init` over SHA-512/224: `MdHash.hmacInitReg`
follows it with `Impl.Scrub.X86_64.scrubTail`, which wipes the registers and
the granules `ks512_224` of its stack. -/
def init512_224 : VG.X86_64.RScrub.Analysed base512_224.I.initAnyKeyApi.sig (24 + anyFrame base512_224.I) []
    (initCode base512_224.H base512_224.I) :=
  ⟨ks512_224, VG.X86_64.RTaint.ok_of_resOkF
    (by rtaint_decide_sum_weak (initHintWeak base512_224.I) [upd, tail0, tail1, wiped])⟩

def ks512_256 : List Nat := keep_for% base512_256.I.initAnyKeyApi.sig (24 + anyFrame base512_256.I)
  (initCode base512_256.H base512_256.I) []

/-- The residue analysis of HMAC's `init` over SHA-512/256: `MdHash.hmacInitReg`
follows it with `Impl.Scrub.X86_64.scrubTail`, which wipes the registers and
the granules `ks512_256` of its stack. -/
def init512_256 : VG.X86_64.RScrub.Analysed base512_256.I.initAnyKeyApi.sig (24 + anyFrame base512_256.I) []
    (initCode base512_256.H base512_256.I) :=
  ⟨ks512_256, VG.X86_64.RTaint.ok_of_resOkF
    (by rtaint_decide_sum_weak (initHintWeak base512_256.I) [upd, tail0, tail1, wiped])⟩

end VG.Proof.Variants.MdHash.X86_64.Sha512Init
