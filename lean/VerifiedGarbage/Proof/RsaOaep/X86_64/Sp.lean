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

theorem Good.all {c : Prog isa} (h : Good c) : c.all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (by
    rw [Code.allInstrs_eq]
    exact List.all_eq_true.mpr fun i hi => by rw [SpSafe.of_noSp h.noSp i hi]; rfl)

end VG.Proof.RsaOaep.X86_64
