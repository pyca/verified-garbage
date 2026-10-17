module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.DecCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExpL
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Pub

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
open VG.Proof.Pbkdf2.Md.X86_64 (Tier)
open VG.Proof.RsaPkcs1Enc.X86_64 (PrivImpl)

theorem dec_spSafe (t : Tier) (v : PrivImpl) :
    (decrypt (oaepHs t) v.name v.code).all (fun i => !isa.writesSp i) = true := by
  have g := oaepHs_good t
  simp only [decrypt, decBody, decMain, seqs, Code.all,
    decFail_good.all, (hashLabel_good g oLh).all, (mgfXor_good g).all, (selPrologue_good _ _).all,
    accLh_good.all, scan_good.all, clearBuf_good.all, copyT_good.all, shift_good.all,
    outLoop_good.all, v.spSafe]
  rfl

end VG.Proof.RsaOaep.X86_64
