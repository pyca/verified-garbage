import VerifiedGarbage.Proof.RsaOaep.X86_64.DecCT
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant

/-!
# RSAES-OAEP on x86-64: `rsp` written only by the frames

`Artifact.spSafe` of both functions: every piece but the RSA operation's
call is `Good`, which never writes `rsp`; the RSA operation's
implementation writes it only in its frames; and so do the frames.
-/

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (seqs)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees)
open VG.Proof.RsaPkcs1Sig.X86_64 (pubChecked)
open VG.Proof.RsaPkcs1Enc.X86_64 (PrivImpl)

theorem Good.all {c : Prog isa} (h : Good c) : c.all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (by
    rw [Code.allInstrs_eq]
    exact List.all_eq_true.mpr fun i hi => by rw [SpSafe.of_noSp h.noSp i hi]; rfl)

variable {Hl Gm : Hash} (hH : HashOK Hl) (KH : Callees Hl) (hG : HashOK Gm) (KG : Callees Gm)

include hH KH hG KG in
theorem enc_spSafe :
    (encrypt Hl.stream Gm.stream pubChecked.name pubChecked.code).all (fun i => !isa.writesSp i) = true := by
  have g := HGood.of hH KH
  have g' := HGood.of hG KG
  simp only [encrypt, encBody, encMain, encEm, encFail, seqs, Code.all,
    zeroOut_good.all, clearEm_good.all, (copySeed_good _).all, (hashLabel_good g oDig).all, (copyLh_good _).all,
    putMsg_good.all, (mgfXor_good g').all, pubChecked.spSafe, Bool.and_true]
  rfl

include hH KH hG KG in
theorem dec_spSafe (v : PrivImpl) :
    (decrypt Hl.stream Gm.stream v.name v.code).all (fun i => !isa.writesSp i) = true := by
  have g := HGood.of hH KH
  have g' := HGood.of hG KG
  simp only [decrypt, decBody, decMain, seqs, Code.all,
    decFail_good.all, (hashLabel_good g oLh).all, (mgfXor_good g').all,
    (accLh_good _).all, (scan_good _).all, (clearBuf_good _).all, copyT_good.all, shift_good.all,
    outLoop_good.all, v.spSafe]
  rfl

/-! ## The instances emitted -/

namespace Inst

open VG.Proof.Pbkdf2.Md.X86_64 (MdHash)

/-- Whether `vg_rsa_oaep_<H>_mgf1_<G>_*` is emitted for `H`'s variant `v` and
`G`'s variant `v2`: for `G = H`, with the same variant for both (`v2 = v`);
and for MGF1 with SHA-1 and `H` another hash function, for every pair. MD5
is not used. These are the pairs that are used in practice (and that
Wycheproof tests). -/
def emitted (v v2 : MdHash) : Bool :=
  v.mgf.G.rust != "md5" &&
    if v.mgf.G.rust == v2.mgf.G.rust then v.suffix == v2.suffix else v2.mgf.G.rust == "sha1"

/-- The tags and suffixes of an instance's name (`Emit.qualifiedName`): `H`'s
variant tagged with `H`, then, if `G` is another hash function, `G`'s tagged
with `mgf1` (`vg_rsa_oaep_sha256_mgf1_sha1_encrypt_sha256_shani_mgf1_shani`). -/
def parts (v v2 : MdHash) : List (String × String) :=
  (v.mgf.G.rust, v.suffix) ::
    if v.mgf.G.rust == v2.mgf.G.rust then [] else [("mgf1", v2.suffix)]

/-- The CPU features of both variants, each once. -/
def features (v v2 : MdHash) : List String := v.features ++ v2.features.filter (!v.features.contains ·)

end Inst

end VG.Proof.RsaOaep.X86_64
