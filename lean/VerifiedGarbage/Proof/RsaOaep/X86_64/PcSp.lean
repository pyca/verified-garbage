module
public import VerifiedGarbage.Impl.RsaOaep.X86_64.Precomputed
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Core
public import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl

import VerifiedGarbage.Proof.RsaOaep.X86_64.Sp
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaOaep.X86_64.Good
import VerifiedGarbage.Proof.Rsa.X86_64.PrivCT
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-! # RSAES-OAEP encryption with a precomputed public key on x86-64: the stack pointer -/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64.Pc

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (seqs)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees)
open VG.Proof.Rsa.X86_64 (PublicImpl)

variable {Hl : Hash} (hH : HashOK Hl) (KH : Callees Hl)

include hH KH in
/-- It writes `rsp` only in its frame's push and pop. -/
theorem code_spSafe (vs : List Proof.Pbkdf2.Md.X86_64.MdHash) (v : PublicImpl) :
    (Impl.RsaOaep.X86_64.Precomputed.encrypt Hl.stream (Proof.HashTable.X86_64.fnsOf vs) v.name v.code).all
      (fun i => !isa.writesSp i) = true := by
  have g := HGood.of hH KH
  obtain ⟨hgi, hgu, hgf⟩ := Proof.HashTable.X86_64.fnsGood_of vs
  simp only [Impl.RsaOaep.X86_64.Precomputed.encrypt, encBodyWith, Impl.RsaOaep.X86_64.Precomputed.encMain, encEm,
    encFail, mgfT, seqs, Code.all, zeroOut_good.all, clearEm_good.all, (copySeed_good _).all,
    (hashLabel_good g oDig).all, (copyLh_good _).all, putMsg_good.all, (Table.mgfT_good hgi hgu hgf _).all, v.spSafe,
    Bool.and_true]
  rfl

end VG.Proof.RsaOaep.X86_64.Pc
