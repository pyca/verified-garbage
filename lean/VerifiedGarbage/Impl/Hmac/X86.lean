module

public import VerifiedGarbage.Impl.Pbkdf2.Md.X86
public import VerifiedGarbage.Impl.Pbkdf2.Md.AnyKey.X86
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Impl.Scrub.X86.Sel

/-!
# HMAC on x86 (32-bit): `init` and `finalize` as emitted

HMAC's functions are those PBKDF2 calls (`Impl/Pbkdf2/Md/X86.lean`,
`Impl/Pbkdf2/Md/AnyKey/X86.lean`) of a hash function `M` and the functions
`F` of its streaming hash, each followed by its cleanup
(`Impl.Scrub.X86.scrubAll`): the zeroing of the stack it reserves below `esp`,
and the clearing of the registers a callee may change. Neither returns a
value. SHA-224's and SHA-256's `init` zeroes its frames itself and is
followed by the zeroing of only the doublewords that leaves
(`Impl.Scrub.X86.scrubSel`, `sha256Init`).

* `vg_hmac_<hash>_init`, for a key of any length, chooses on entry
  (`initEntry`): for a key of at most a block, `M.hmacInit` in a frame
  holding its working space; for a longer key (cold), `F.hmacInitAny` in a
  frame holding its larger working space, which it wipes.
* `vg_hmac_<hash>_finalize` runs `M.hmacFin` in a frame holding its working
  space.

Every number is the literal its proof states (`Proof/Hmac/X86/Scrub.lean`):
the frames' bytes and the stack the cleanup zeroes, from the instance's
working space (`Proof.Pbkdf2.Md.X86.initFrame`, `finFrame`,
`Proof.Pbkdf2.Whole.X86.Any.anyFrame`), but SHA-224's and SHA-256's
`finalize`, whose frame holds only the 208 bytes of working space its code
uses (`Proof.Pbkdf2.Md.X86.finFramedW`): the whole frame is zeroed on every
call. SHA-224 and SHA-256 share them, as do the hashes of the SHA-512
family.
-/

@[expose] public section

namespace VG.Impl.Hmac.X86.Fn

open VG.X86
open VG.Impl.StackScratch.X86 (withStackScratch withStackScratchWiped)
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Impl.Pbkdf2.Whole.X86 (Fns initEntry)

/-! ## MD5 -/

/-- `vg_hmac_md5_init`, as emitted. -/
def md5Init (M : Hash) (F : Fns) : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 1124
    (initEntry 64 (withStackScratch 408 4 M.hmacInit) (withStackScratchWiped 1048 4 256 F.hmacInitAny))

/-- `vg_hmac_md5_finalize`, as emitted. -/
def md5Finalize (M : Hash) : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 460 (withStackScratch 412 5 M.hmacFin)

/-! ## SHA-1 -/

/-- `vg_hmac_sha1_init`, as emitted. -/
def sha1Init (M : Hash) (F : Fns) : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 1220
    (initEntry 64 (withStackScratch 472 4 M.hmacInit) (withStackScratchWiped 1144 4 280 F.hmacInitAny))

/-- `vg_hmac_sha1_finalize`, as emitted. -/
def sha1Finalize (M : Hash) : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 524 (withStackScratch 476 5 M.hmacFin)

/-! ## SHA-224 and SHA-256 -/

/-- `vg_hmac_sha224_init` and `vg_hmac_sha256_init` before their cleanup: for
a key of at most a block, `M.hmacInit` in a frame of the 176 bytes of working
space its code uses (the compression function's and our caller's registers;
200 bytes with the return address, the arguments and the buffer's address),
which it zeroes; for a longer key (cold), `F.hmacInitAny` in its larger
frame, which it zeroes. -/
def sha256InitBody (M : Hash) (F : Fns) : Prog isa :=
  initEntry 64 (withStackScratchWiped 200 4 44 M.hmacInit) (withStackScratchWiped 1624 4 400 F.hmacInitAny)

/-- The doublewords of the 1700 bytes below `esp` on entry that
`sha256InitBody` may leave different in two runs, as the residue analysis
finds (`X86.rtaint`): what neither frame zeroes of itself, its header (the
word for the return address, the copies of the arguments, the buffer's
address), and the stack below it that the functions it calls use. The short
key's frame is the 200 bytes at the top (doublewords 375 to 424: its header
is 375 to 380, and its callees use 370 to 374), the long key's the 1624
(19 to 424: header 19 to 24, callees 7 to 18). -/
def sha256InitWords : List Nat :=
  [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
    370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380]

/-- `vg_hmac_sha224_init` and `vg_hmac_sha256_init`, as emitted:
`sha256InitBody`, then the zeroing of the doublewords it leaves
(`Impl.Scrub.X86.scrubSel`), so that a key of at most a block zeroes its 200
bytes and those, not the 1700 the long key's frame takes. -/
def sha256Init (M : Hash) (F : Fns) : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1700 sha256InitWords (sha256InitBody M F)

/-- `vg_hmac_sha224_finalize` and `vg_hmac_sha256_finalize`, as emitted. -/
def sha256Finalize (M : Hash) : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 284 (withStackScratch 236 5 M.hmacFin)

/-! ## The SHA-512 family -/

/-- `vg_hmac_sha384_init`, `vg_hmac_sha512_init`, `vg_hmac_sha512_224_init`
and `vg_hmac_sha512_256_init`, as emitted. -/
def sha512Init (M : Hash) (F : Fns) : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 3508
    (initEntry 128 (withStackScratch 1896 4 M.hmacInit) (withStackScratchWiped 3432 4 852 F.hmacInitAny))

/-- `vg_hmac_sha384_finalize`, `vg_hmac_sha512_finalize`,
`vg_hmac_sha512_224_finalize` and `vg_hmac_sha512_256_finalize`, as
emitted. -/
def sha512Finalize (M : Hash) : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 1948 (withStackScratch 1900 5 M.hmacFin)

end VG.Impl.Hmac.X86.Fn
