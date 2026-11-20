module

public import VerifiedGarbage.Impl.MdHashTable.AArch64
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

/-- The name of the digest of the hash functions with the parameters `P`,
`Impl.MdHashTable.AArch64.digest P`: one for each size of hash value, which
the hash functions of a family share. -/
def digestName (P : Impl.Pbkdf2.AArch64.Params) : String :=
  match P.N with
  | 16 => "vg_md5_state_digest"
  | 20 => "vg_sha1_state_digest"
  | 32 => "vg_sha256_state_digest"
  | _ => "vg_sha512_state_digest"

/-- For each of the functions the code calls through the table of the hash
function of the message (its `init`, compression function and digest), that
function of each of `hs`: what an indirect call may reach. -/
def mdFns (hs : List Hash) : MdFns :=
  ⟨hs.map fun h => (h.initN, h.initC), hs.map fun h => (h.compN, h.compC),
    hs.map fun h => (digestName h.P, Impl.MdHashTable.AArch64.digest h.P)⟩

/-- `vg_rsa_pss_sign_precomputed` with the tables of the hash functions `hs`
(the message's, and those MGF1 calls) and the implementation `c` of the
private-key operation: its frame of 336 bytes over the 3248 of
`vg_rsa_private_checked_precomputed`. -/
def signCP (hs : List Hash) (c : Crt) : Prog isa :=
  scrubOf 3584 32 (AArch64.signCP (mdFns hs) (Impl.RsaOaep.AArch64.Fn.fnsOf hs) c.privPName c.privP)

/-- `vg_rsa_pss_verify_precomputed`, calling the public-key operation `pub`:
its frame of 336 bytes over the 624 its callees use. -/
def verifyC (hs : List Hash) (pubName : String) (pub : Prog isa) : Prog isa :=
  scrubOf 960 32 (AArch64.verifyC (mdFns hs) (Impl.RsaOaep.AArch64.Fn.fnsOf hs) pubName pub)

end VG.Impl.RsaPss.AArch64.Fn
