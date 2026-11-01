module

import VerifiedGarbage.Proof.AesXts.X86.Unit.CT
import VerifiedGarbage.Proof.AesXts.X86.Verified
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesXts.X86.Unit.Run
import VerifiedGarbage.Proof.AesXts.X86.CT
public import VerifiedGarbage.Proof.Aes.X86.BlocksVariant

/-!
# XTS-AES of data units on x86: `Verified`

Correctness (`encrypt_wp`, `decrypt_wp`) and constant time (`encrypt_ct`,
`decrypt_ct`) for the whole-block functions calling any implementation `v`
of the block functions (`xtsE v`, `xtsD v`), a state satisfying the
precondition (`unitSat`), and the shared contracts of
`Spec/Xts/Contract.lean`, with 52 bytes of stack: the frame of a call's six
arguments, its return address, and the whole-block function's 24.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86.Unit

open VG VG.X86 VG.Impl.AesXts.X86Unit
open VG.Proof.AesCbc (aesWith_state aesInvWith_state)
open VG.Proof.Aes.X86 (BlocksImpl)

/-- `vg_aes_xts_encrypt` calling the block functions of `v`, with `v`'s suffix. -/
abbrev xtsE (v : BlocksImpl) : Impl.Aes.X86.Blocks :=
  ⟨"vg_aes_xts_encrypt" ++ v.suffix, Impl.AesXts.X86.encrypt v.enc⟩

/-- `vg_aes_xts_decrypt` calling the block functions of `v`, with `v`'s suffix. -/
abbrev xtsD (v : BlocksImpl) : Impl.Aes.X86.Blocks :=
  ⟨"vg_aes_xts_decrypt" ++ v.suffix, Impl.AesXts.X86.decrypt v.dec⟩

theorem callee_nosp_all {c : Prog isa} (h : NoSp c) : c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq]
  exact List.all_eq_true.mpr fun i hi => by simp only [h i hi, Bool.not_false]

theorem xtsE_nosp (v : BlocksImpl) : NoSp (xtsE v).code := by
  apply NoSp.of_all
  simp only [Impl.AesXts.X86.encrypt, Impl.AesXts.X86.crypt, Impl.AesXts.X86.batch, Impl.AesXts.X86.pass,
    Impl.AesOcb.X86.blocksFrame, Code.allInstrs, callee_nosp_all v.encNosp]
  decide +kernel

theorem xtsD_nosp (v : BlocksImpl) : NoSp (xtsD v).code := by
  apply NoSp.of_all
  simp only [Impl.AesXts.X86.decrypt, Impl.AesXts.X86.crypt, Impl.AesXts.X86.batch, Impl.AesXts.X86.pass,
    Impl.AesOcb.X86.blocksFrame, Code.allInstrs, callee_nosp_all v.decNosp]
  decide +kernel

theorem xtsE_stack (v : BlocksImpl) : stackUse (xtsE v).code ≤ 24 := by
  simp only [Impl.AesXts.X86.encrypt, Impl.AesXts.X86.crypt, Impl.AesXts.X86.batch, Impl.AesXts.X86.pass,
    Impl.AesOcb.X86.blocksFrame, stackUse, v.encStack]
  decide +kernel

theorem xtsD_stack (v : BlocksImpl) : stackUse (xtsD v).code ≤ 24 := by
  simp only [Impl.AesXts.X86.decrypt, Impl.AesXts.X86.crypt, Impl.AesXts.X86.batch, Impl.AesXts.X86.pass,
    Impl.AesOcb.X86.blocksFrame, stackUse, v.decStack]
  decide +kernel

theorem xfnE (v : BlocksImpl) : XFn true (xtsE v) where
  ok _ hs := crypt_wp true v.encOk v.encNosp v.encStack (fun R w m p => (aesWith_state R w m p).symm) hs
  ct := crypt_ct true v.encOk v.encCt v.encNosp v.encStack fun R w m p => (aesWith_state R w m p).symm
  nosp := xtsE_nosp v
  stack := xtsE_stack v

theorem xfnD (v : BlocksImpl) : XFn false (xtsD v) where
  ok _ hs := crypt_wp false v.decOk v.decNosp v.decStack (fun R w m p => (aesInvWith_state R w m p).symm) hs
  ct := crypt_ct false v.decOk v.decCt v.decNosp v.decStack fun R w m p => (aesInvWith_state R w m p).symm
  nosp := xtsD_nosp v
  stack := xtsD_stack v

theorem encrypt_spSafe (v : BlocksImpl) : (encrypt (xtsE v)).all (fun i => !isa.writesSp i) = true := by
  simp only [encrypt, tweak, encSteal, swap, xcall, Code.all, Proof.AesXts.X86.encrypt_spSafe v]
  decide +kernel

theorem decrypt_spSafe (v : BlocksImpl) : (decrypt (xtsE v) (xtsD v)).all (fun i => !isa.writesSp i) = true := by
  simp only [decrypt, tweak, decSteal, swap, xcall, Code.all, Proof.AesXts.X86.encrypt_spSafe v,
    Proof.AesXts.X86.decrypt_spSafe v]
  decide +kernel

/-- A state satisfying the precondition: AES-128, a data unit of one block
at `0x4000`, and the scratch buffer at `0x5000`, as stack arguments at
`0x8004`. -/
def unitSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800c then 10
    else if a = 0x8011 then 0x30 else if a = 0x8015 then 0x40 else if a = 0x8018 then 16
    else if a = 0x801d then 0x50 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 240⟩, ⟨0x3000, 16⟩, ⟨0x8004, 28⟩]
  wr := [⟨0x4000, 16⟩, ⟨0x5000, 2432⟩]

theorem encrypt_verified (v : BlocksImpl) :
    Verified X86.target (encrypt (xtsE v)) (Spec.Xts.aesEncryptUnitContract X86.abi 52) :=
  Verified.of_correct (fun _ hs => encrypt_wp (UPre.of hs) (xfnE v)) (encrypt_ct (xfnE v)) (by
    have a0 : arg unitSat 0 = 0x1000 := by decide
    have a1 : arg unitSat 1 = 0x2000 := by decide
    have a2 : arg unitSat 2 = 10 := by decide
    have a3 : arg unitSat 3 = 0x3000 := by decide
    have a4 : arg unitSat 4 = 0x4000 := by decide
    have a5 : arg unitSat 5 = 16 := by decide
    have a6 : arg unitSat 6 = 0x5000 := by decide
    have e : argAddr unitSat 0 = 0x8004 := by decide
    have esp : unitSat.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Xts.aesEncryptUnitContract, Spec.Xts.aesUnitSig, Spec.Xts.aesUnitPre,
      Spec.Xts.aesEncryptUnitPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, unitX86, unitPre, unitPub,
      xtsOf, E, W, K, R, I, D, Len, S, Sa, Da, schR, tschR, iR, dataR, scrR, argsR, retR, stkR]
      [a0, a1, a2, a3, a4, a5, a6, e, esp] using unitSat)

theorem decrypt_verified (v : BlocksImpl) :
    Verified X86.target (decrypt (xtsE v) (xtsD v)) (Spec.Xts.aesDecryptUnitContract X86.abi 52) :=
  Verified.of_correct (fun _ hs => decrypt_wp (UPre.of hs) (xfnE v) (xfnD v)) (decrypt_ct (xfnE v) (xfnD v)) (by
    have a0 : arg unitSat 0 = 0x1000 := by decide
    have a1 : arg unitSat 1 = 0x2000 := by decide
    have a2 : arg unitSat 2 = 10 := by decide
    have a3 : arg unitSat 3 = 0x3000 := by decide
    have a4 : arg unitSat 4 = 0x4000 := by decide
    have a5 : arg unitSat 5 = 16 := by decide
    have a6 : arg unitSat 6 = 0x5000 := by decide
    have e : argAddr unitSat 0 = 0x8004 := by decide
    have esp : unitSat.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Xts.aesDecryptUnitContract, Spec.Xts.aesUnitSig, Spec.Xts.aesUnitPre,
      Spec.Xts.aesDecryptUnitPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, unitX86, unitPre, unitPub,
      xtsOf, E, W, K, R, I, D, Len, S, Sa, Da, schR, tschR, iR, dataR, scrR, argsR, retR, stkR]
      [a0, a1, a2, a3, a4, a5, a6, e, esp] using unitSat)

end VG.Proof.AesXts.X86.Unit
