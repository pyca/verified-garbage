module

public import VerifiedGarbage.Impl.RsaOaep.AArch64.Precomputed
public import VerifiedGarbage.Impl.Rsa.AArch64.PrivChecked
public import VerifiedGarbage.Impl.Scrub.AArch64.Writes

/-! # RSAES-OAEP with a precomputed key on AArch64: the functions as emitted

Each function's code, calling the hash functions through its tables, then
its cleanup: the registers the code may write cleared, and its stack zeroed
(`scrubOf`). -/

@[expose] public section

namespace VG.Impl.RsaOaep.AArch64.Fn

open VG VG.AArch64
open VG.Impl.Scrub.AArch64 (scrubOf)
open VG.Impl.Rsa.AArch64.PrivChecked (Crt)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns)

/-- For each of the streaming functions RSAES-OAEP and MGF1 call through a
table, that function of each of the hash functions `hs`: what an indirect
call may reach. -/
def fnsOf (hs : List Hash) : Fns :=
  ⟨hs.map fun h => (h.initN, h.initC), hs.map fun h => (h.updN, h.updC), hs.map fun h => (h.finN, h.finC)⟩

/-- `vg_rsa_oaep_decrypt_precomputed` with the tables of `hs` and the
implementation `c` of the private-key operation: its frames of 288 bytes
over the 3248 of `vg_rsa_private_checked_precomputed`. -/
def decryptP (hs : List Hash) (c : Crt) : Prog isa :=
  scrubOf 3536 32 (AArch64.decryptP (fnsOf hs) c.privPName c.privP)

/-- `vg_rsa_oaep_encrypt_precomputed` with the tables of `hs`, calling the
public-key operation `pub`: its frames of 288 bytes, and the two words of
arguments it passes on the stack. -/
def encrypt (hs : List Hash) (pubName : String) (pub : Prog isa) : Prog isa :=
  scrubOf 304 32 (Precomputed.encrypt (fnsOf hs) pubName pub)

end VG.Impl.RsaOaep.AArch64.Fn
