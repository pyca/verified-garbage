module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
public meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512
public meta import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
public meta import VerifiedGarbage.Proof.Framework.Lit
public meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

-- separate module: the kernel checks it alongside `Sha512ShaNi.lean`, each about as long, with less memory than both

/-!
# HMAC's `init` over the SHA-512 family on x86-64 with the SHA-512 extensions, without secret residue

The residue analysis of HMAC's `init` for a key of any length (`initCode`)
over SHA-384, SHA-512, SHA-512/224 and SHA-512/256 with this compression
function, a branch at a time (`Proof.Pbkdf2.Md.X86_64.initRes_ok`): the variants
of `Proof/Variants/MdHash/X86_64.lean` with it take theirs from here
(`MdHash.hmacInitRes`), and the rest from `Sha512ShaNi.lean`.
-/

@[expose] public section

namespace VG.Proof.Variants.MdHash.X86_64.Sha512ShaNiInit

open Proof.Pbkdf2.Md.X86_64

abbrev compress : Proof.Sha512.X86_64.Compress := Proof.Sha512.X86_64.Compress.shani

/-- SHA-384 with this compression function, whose HMAC's `init` is the variant's. -/
abbrev base384 : MdHash := Proof.Pbkdf2.Md.X86_64.Sha512.sha384 compress

def ks384 : List Nat := keep_for% base384.I.initAnyKeyApi.sig (24 + anyFrame base384.I)
  (initCode base384.H base384.I) []

/-- The analysis of the branch for long keys stops between its two parts here. -/
def longMid384 : VG.X86_64.RTaint.FT := init_long_mid% base384.H base384.I

theorem longPre384 : InitLongPre base384.H base384.I longMid384 :=
  ⟨_, by taint_decide_weak (initHintWeak base384.I)⟩

theorem longPost384 : InitLongPost base384.H base384.I ks384 longMid384 :=
  ⟨_, by taint_decide_weak (initHintWeak base384.I)⟩

theorem long384 : InitLongOk base384.H base384.I ks384 := initLong_of (by decide) longPre384 longPost384

theorem short384 : InitShortOk base384.H base384.I ks384 :=
  ⟨by decide, _, by taint_decide⟩

/-- The residue analysis of HMAC's `init` over SHA-384: `MdHash.hmacInitReg`
follows it with `Impl.Scrub.X86_64.scrubTail`, which wipes the registers and
the granules `ks384` of its stack. -/
def init384 : VG.X86_64.RScrub.Analysed base384.I.initAnyKeyApi.sig (24 + anyFrame base384.I) []
    (initCode base384.H base384.I) :=
  ⟨ks384, initRes_ok long384 short384⟩

/-- SHA-512 with this compression function, whose HMAC's `init` is the variant's. -/
abbrev base512 : MdHash := Proof.Pbkdf2.Md.X86_64.Sha512.sha512 compress

def ks512 : List Nat := keep_for% base512.I.initAnyKeyApi.sig (24 + anyFrame base512.I)
  (initCode base512.H base512.I) []

/-- The analysis of the branch for long keys stops between its two parts here. -/
def longMid512 : VG.X86_64.RTaint.FT := init_long_mid% base512.H base512.I

theorem longPre512 : InitLongPre base512.H base512.I longMid512 :=
  ⟨_, by taint_decide_weak (initHintWeak base512.I)⟩

theorem longPost512 : InitLongPost base512.H base512.I ks512 longMid512 :=
  ⟨_, by taint_decide_weak (initHintWeak base512.I)⟩

theorem long512 : InitLongOk base512.H base512.I ks512 := initLong_of (by decide) longPre512 longPost512

theorem short512 : InitShortOk base512.H base512.I ks512 :=
  ⟨by decide, _, by taint_decide⟩

/-- The residue analysis of HMAC's `init` over SHA-512: `MdHash.hmacInitReg`
follows it with `Impl.Scrub.X86_64.scrubTail`, which wipes the registers and
the granules `ks512` of its stack. -/
def init512 : VG.X86_64.RScrub.Analysed base512.I.initAnyKeyApi.sig (24 + anyFrame base512.I) []
    (initCode base512.H base512.I) :=
  ⟨ks512, initRes_ok long512 short512⟩

/-- SHA-512/224 with this compression function, whose HMAC's `init` is the variant's. -/
abbrev base512_224 : MdHash := Proof.Pbkdf2.Md.X86_64.Sha512.sha512_224 compress

def ks512_224 : List Nat := keep_for% base512_224.I.initAnyKeyApi.sig (24 + anyFrame base512_224.I)
  (initCode base512_224.H base512_224.I) []

/-- The analysis of the branch for long keys stops between its two parts here. -/
def longMid512_224 : VG.X86_64.RTaint.FT := init_long_mid% base512_224.H base512_224.I

theorem longPre512_224 : InitLongPre base512_224.H base512_224.I longMid512_224 :=
  ⟨_, by taint_decide_weak (initHintWeak base512_224.I)⟩

theorem longPost512_224 : InitLongPost base512_224.H base512_224.I ks512_224 longMid512_224 :=
  ⟨_, by taint_decide_weak (initHintWeak base512_224.I)⟩

theorem long512_224 : InitLongOk base512_224.H base512_224.I ks512_224 := initLong_of (by decide) longPre512_224 longPost512_224

theorem short512_224 : InitShortOk base512_224.H base512_224.I ks512_224 :=
  ⟨by decide, _, by taint_decide⟩

/-- The residue analysis of HMAC's `init` over SHA-512/224: `MdHash.hmacInitReg`
follows it with `Impl.Scrub.X86_64.scrubTail`, which wipes the registers and
the granules `ks512_224` of its stack. -/
def init512_224 : VG.X86_64.RScrub.Analysed base512_224.I.initAnyKeyApi.sig (24 + anyFrame base512_224.I) []
    (initCode base512_224.H base512_224.I) :=
  ⟨ks512_224, initRes_ok long512_224 short512_224⟩

/-- SHA-512/256 with this compression function, whose HMAC's `init` is the variant's. -/
abbrev base512_256 : MdHash := Proof.Pbkdf2.Md.X86_64.Sha512.sha512_256 compress

def ks512_256 : List Nat := keep_for% base512_256.I.initAnyKeyApi.sig (24 + anyFrame base512_256.I)
  (initCode base512_256.H base512_256.I) []

/-- The analysis of the branch for long keys stops between its two parts here. -/
def longMid512_256 : VG.X86_64.RTaint.FT := init_long_mid% base512_256.H base512_256.I

theorem longPre512_256 : InitLongPre base512_256.H base512_256.I longMid512_256 :=
  ⟨_, by taint_decide_weak (initHintWeak base512_256.I)⟩

theorem longPost512_256 : InitLongPost base512_256.H base512_256.I ks512_256 longMid512_256 :=
  ⟨_, by taint_decide_weak (initHintWeak base512_256.I)⟩

theorem long512_256 : InitLongOk base512_256.H base512_256.I ks512_256 := initLong_of (by decide) longPre512_256 longPost512_256

theorem short512_256 : InitShortOk base512_256.H base512_256.I ks512_256 :=
  ⟨by decide, _, by taint_decide⟩

/-- The residue analysis of HMAC's `init` over SHA-512/256: `MdHash.hmacInitReg`
follows it with `Impl.Scrub.X86_64.scrubTail`, which wipes the registers and
the granules `ks512_256` of its stack. -/
def init512_256 : VG.X86_64.RScrub.Analysed base512_256.I.initAnyKeyApi.sig (24 + anyFrame base512_256.I) []
    (initCode base512_256.H base512_256.I) :=
  ⟨ks512_256, initRes_ok long512_256 short512_256⟩

end VG.Proof.Variants.MdHash.X86_64.Sha512ShaNiInit
