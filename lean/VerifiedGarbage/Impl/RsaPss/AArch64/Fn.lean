module

public import VerifiedGarbage.Impl.RsaPss.AArch64.Encoding
public import VerifiedGarbage.Impl.RsaOaep.AArch64.Fn

/-! # RSASSA-PSS with a precomputed key on AArch64: the functions as emitted

Each function's code, calling the hash functions through its tables, then
its cleanup: the registers the code may write cleared, and its stack zeroed
(`scrubOf`). -/

@[expose] public section

namespace VG.Impl.RsaPss.AArch64.Fn

open VG VG.AArch64
open VG.Impl.Residue.AArch64 (scrubOf)
open VG.Impl.Rsa.AArch64.PrivChecked (Crt)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)

/-- `vg_rsa_pss_sign_precomputed` with the tables' functions `f` (their
`init`, compression function and digest), those of the hash functions `hs`
MGF1 calls, and the implementation `c` of the private-key operation: its
frame of 336 bytes over the 3248 of `vg_rsa_private_checked_precomputed`. -/
def signCP (f : MdFns) (hs : List Hash) (c : Crt) : Prog isa :=
  scrubOf 3584 32 (AArch64.signCP f (Impl.RsaOaep.AArch64.Fn.fnsOf hs) c.privPName c.privP)

/-- `vg_rsa_pss_verify_precomputed`, calling the public-key operation `pub`:
its frame of 336 bytes over the 624 its callees use. -/
def verifyC (f : MdFns) (hs : List Hash) (pubName : String) (pub : Prog isa) : Prog isa :=
  scrubOf 960 32 (AArch64.verifyC f (Impl.RsaOaep.AArch64.Fn.fnsOf hs) pubName pub)

end VG.Impl.RsaPss.AArch64.Fn
