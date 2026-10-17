module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.PcCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExpL
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCall

/-! # RSAES-OAEP encryption with a precomputed public key on x86-64: the stack pointer -/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64.Pc

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (seqs)
open VG.Proof.Pbkdf2.Md.X86_64 (Tier)
open VG.Proof.Rsa.X86_64 (PublicImpl)

/-- It writes `rsp` only in its frame's push and pop. -/
theorem code_spSafe (t : Tier) (v : PublicImpl) :
    (Impl.RsaOaep.X86_64.Precomputed.encrypt (oaepHs t) v.name v.code).all
      (fun i => !isa.writesSp i) = true := by
  have g := oaepHs_good t
  simp only [Impl.RsaOaep.X86_64.Precomputed.encrypt, encBodyWith, Impl.RsaOaep.X86_64.Precomputed.encMain, encEm,
    encFail, seqs, Code.all, zeroOut_good.all, clearEm_good.all, copySeed_good.all, (hashLabel_good g oDig).all,
    copyLh_good.all, putMsg_good.all, (mgfXor_good g).all, (selPrologue_good _ _).all, v.spSafe, Bool.and_true]
  rfl

end VG.Proof.RsaOaep.X86_64.Pc
