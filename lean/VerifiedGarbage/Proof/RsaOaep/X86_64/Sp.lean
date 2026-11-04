module

public import VerifiedGarbage.Proof.HashTable.X86_64
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Impl.RsaOaep.X86_64
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Stack
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecContract
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaOaep.X86_64.DecMain
import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelT
import VerifiedGarbage.Proof.RsaOaep.X86_64.Good
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Pub
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-!
# RSAES-OAEP on x86-64: `rsp` written only by the frames

`Artifact.spSafe` of both functions: every piece but the RSA operation's
call is `Good`, which never writes `rsp`; the RSA operation's
implementation writes it only in its frames; and so do the frames.
-/

@[expose] public section

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

theorem dec_spSafe (vs : List Proof.Pbkdf2.Md.X86_64.MdHash) (v : PrivImpl) :
    (decrypt (Proof.HashTable.X86_64.fnsOf vs) v.name v.code).all (fun i => !isa.writesSp i) = true := by
  obtain ⟨hgi, hgu, hgf⟩ := Proof.HashTable.X86_64.fnsGood_of vs
  simp only [decrypt, decBody, byLen, lens, decTail, decMain, mgfT, seqs, Code.all,
    decFail_good.all, (hashLabelT_good hgi hgu hgf oLh).all, (Table.mgfT_good hgi hgu hgf _).all,
    (accLh_good _).all, (scan_good _).all, (clearBuf_good _).all, copyT_good.all, shift_good.all,
    outLoop_good.all, v.spSafe]
  rfl

/-! ## The instances emitted -/

namespace Inst

open VG.Proof.Pbkdf2.Md.X86_64 (MdHash)

/-- Whether `vg_rsa_oaep_<H>_mgf1_*` is emitted for `H`'s variant `v`: for every
hash function but MD5, which is not used. MGF1's hash function is any of
the tables'. -/
def emitted (v : MdHash) : Bool := v.mgf.G.rust != "md5"

/-- The tags and suffixes of an instance's name (`Emit.qualifiedName`): `H`'s
variant tagged with `H` (`vg_rsa_oaep_sha256_mgf1_decrypt_sha256_shani_…`). -/
def parts (v : MdHash) : List (String × String) := [(v.mgf.G.rust, v.suffix)]

end Inst

end VG.Proof.RsaOaep.X86_64
