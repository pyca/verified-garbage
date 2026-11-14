module

public import VerifiedGarbage.Spec.Xts.Contract
public import VerifiedGarbage.Spec.Xts.OutOfPlace
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubOr
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.AesXts.X86_64.Unit.CT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Contract
public import VerifiedGarbage.Proof.AesXts.X86_64.Variant
import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Dec
public import VerifiedGarbage.Proof.AesXts.X86_64.UnitTo.Verified
import VerifiedGarbage.Proof.Aes.X86_64.ModesScrub

/-! ### `AesXts.X86_64.Unit.Verified`, which only this module used -/

section

/-!
# XTS-AES of data units on x86-64: `Verified`

Correctness (`encrypt_wp`, `decrypt_wp`) and constant time (`encrypt_ct`,
`decrypt_ct`) for any implementation `v` of the whole-block functions, a
state satisfying the precondition (`unitSat`), and the shared contracts of
`Spec/Xts/Contract.lean`, with 16 bytes of stack: the return addresses of the
call of the whole-block function and of its call of a block function.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Unit

open VG VG.X86_64 VG.Impl.AesXts.X86_64Unit

theorem encrypt_mx (v : XtsImpl) : (encrypt v.xts).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [encrypt, tweak, encSteal, swap, Code.allInstrs, v.encMxcsr]; decide +kernel

theorem decrypt_mx (v : XtsImpl) : (decrypt v.xts).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [decrypt, tweak, decSteal, swap, Code.allInstrs, v.encMxcsr, v.decMxcsr]; decide +kernel

theorem encrypt_spSafe (v : XtsImpl) : (encrypt v.xts).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [encrypt, tweak, encSteal, swap, Code.all, v.encSpSafe]; decide +kernel

theorem decrypt_spSafe (v : XtsImpl) : (decrypt v.xts).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [decrypt, tweak, decSteal, swap, Code.all, v.encSpSafe, v.decSpSafe]; decide +kernel

theorem encrypt_correct (v : XtsImpl) (s : State) (hs : (unitX86_64 true).pre s) :
    ∃ t s', Exec isa (encrypt v.xts) s t s' ∧ abiPreserved s s' ∧ (unitX86_64 true).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := encrypt_wp (UPre.of hs) v
  exact ⟨t, s', he, abiPreserved_of_exec (encrypt_mx v) he hg, hp⟩

theorem decrypt_correct (v : XtsImpl) (s : State) (hs : (unitX86_64 false).pre s) :
    ∃ t s', Exec isa (decrypt v.xts) s t s' ∧ abiPreserved s s' ∧ (unitX86_64 false).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := decrypt_wp (UPre.of hs) v
  exact ⟨t, s', he, abiPreserved_of_exec (decrypt_mx v) he hg, hp⟩

/-- A state satisfying the precondition: AES-128, a data unit of one block
at `0x4000`, and the scratch buffer at 0 (the stack argument, zero). -/
def unitSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 10 | .rcx => 0x3000 | .r8 => 0x4000 | .r9 => 16
    | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 240⟩, ⟨0x3000, 16⟩, ⟨0x8008, 8⟩]
  wr := [⟨0x4000, 16⟩, ⟨0, 2432⟩]

theorem encrypt_verified (v : XtsImpl) :
    Verified X86_64.target (encrypt v.xts) (Spec.Xts.aesEncryptUnitContract X86_64.abi 16) :=
  Verified.of_correct (encrypt_correct v) (encrypt_ct v) (by
    sig_implies [Spec.Xts.aesEncryptUnitContract, Spec.Xts.aesUnitSig, Spec.Xts.aesUnitPre,
      Spec.Xts.aesEncryptUnitPost, unitX86_64, unitPre, unitPub, xtsOf, W, K, R, I, D, Len, S, schR, tschR, iR,
      dataR, scrR, argR, retR, stk, X86_64.abi, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range,
      List.range.loop, VG.X86_64.below, X86_64.argRegs] [unitSat] using unitSat)

theorem decrypt_verified (v : XtsImpl) :
    Verified X86_64.target (decrypt v.xts) (Spec.Xts.aesDecryptUnitContract X86_64.abi 16) :=
  Verified.of_correct (decrypt_correct v) (decrypt_ct v) (by
    sig_implies [Spec.Xts.aesDecryptUnitContract, Spec.Xts.aesUnitSig, Spec.Xts.aesUnitPre,
      Spec.Xts.aesDecryptUnitPost, unitX86_64, unitPre, unitPub, xtsOf, W, K, R, I, D, Len, S, schR, tschR, iR,
      dataR, scrR, argR, retR, stk, X86_64.abi, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range,
      List.range.loop, VG.X86_64.below, X86_64.argRegs] [unitSat] using unitSat)

end VG.Proof.AesXts.X86_64.Unit

end

end


/-!
# XTS-AES of data units on x86-64, without secret residue

`vg_aes_xts_encrypt_unit`, `vg_aes_xts_decrypt_unit` and their out-of-place
counterparts over an implementation of the whole-block functions
(`AesXts.X86_64.XtsImpl`), each followed by `Impl.Scrub.X86_64.scrubTail`
(`X86_64.Scrub.withScrub`) where the implementation gives the residue
analysis of the instance (`XtsImpl.encUnitRes`, …), and otherwise with its
16 or 24 bytes of stack wiped (`X86_64.RScrub.withScrubOrAll`). Their postconditions
read the memory on return only within the buffers (`X86_64.Scrub.PostOut`):
the data, or the output as long as the input, which the out-of-place
functions' precondition requires.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub VG.Proof.Aes.X86_64.ModesScrub

/-! ## Postconditions -/

theorem encryptUnitOut (stack : Nat) :
    PostOut (Spec.Xts.aesEncryptUnitContract X86_64.abi stack) (Spec.Xts.aesUnitSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, tsch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Xts.aesUnitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, Spec.Xts.KeySchedules m sch tsch _ key → _ = some (Spec.Aes.bytesAt m₂ dt _)
      intro key hk
      rw [bytesAt_of0 hb.2.2.2.1 (len_le1 ln)]
      exact h key hk

theorem decryptUnitOut (stack : Nat) :
    PostOut (Spec.Xts.aesDecryptUnitContract X86_64.abi stack) (Spec.Xts.aesUnitSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, tsch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Xts.aesUnitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, Spec.Xts.KeySchedules m sch tsch _ key → _ = some (Spec.Aes.bytesAt m₂ dt _)
      intro key hk
      rw [bytesAt_of0 hb.2.2.2.1 (len_le1 ln)]
      exact h key hk

theorem encryptUnitToOut (stack : Nat) :
    PostOut (Spec.Xts.aesEncryptUnitToContract X86_64.abi stack) (Spec.Xts.aesUnitToSig.retBits 64) :=
  postOut_of_local_pre (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hpre hb h => by
    match vs, hlen with
    | [sch, tsch, rd, iv, sr, ln, dt, dl, sc], _ =>
      simp only [Spec.Xts.aesUnitToSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      have hdl : ((ArgWord.int X86_64.abi.ptrBits).ofRaw dl).toNat = ((ArgWord.int X86_64.abi.ptrBits).ofRaw ln).toNat :=
        hpre.2.2.2
      show ∀ key, Spec.Xts.KeySchedules m sch tsch _ key → _ = some (Spec.Aes.bytesAt m₂ dt _)
      intro key hk
      rw [bytesAt_of0 hb.2.2.2.2.1 (by rw [← hdl]; exact len_le1 dl)]
      exact h key hk

theorem decryptUnitToOut (stack : Nat) :
    PostOut (Spec.Xts.aesDecryptUnitToContract X86_64.abi stack) (Spec.Xts.aesUnitToSig.retBits 64) :=
  postOut_of_local_pre (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hpre hb h => by
    match vs, hlen with
    | [sch, tsch, rd, iv, sr, ln, dt, dl, sc], _ =>
      simp only [Spec.Xts.aesUnitToSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      have hdl : ((ArgWord.int X86_64.abi.ptrBits).ofRaw dl).toNat = ((ArgWord.int X86_64.abi.ptrBits).ofRaw ln).toNat :=
        hpre.2.2.2
      show ∀ key, Spec.Xts.KeySchedules m sch tsch _ key → _ = some (Spec.Aes.bytesAt m₂ dt _)
      intro key hk
      rw [bytesAt_of0 hb.2.2.2.2.1 (by rw [← hdl]; exact len_le1 dl)]
      exact h key hk

/-! ## The registrations -/

open VG.X86_64.RScrub VG.Proof.AesXts.X86_64

/-- `vg_aes_xts_encrypt_unit` over `v`. -/
def encryptUnitReg (v : XtsImpl) : Registration Spec.Xts.aesEncryptUnitApi X86_64.target :=
  withScrubOrAll {
    suffix := v.suffix
    code := Impl.AesXts.X86_64Unit.encrypt v.xts
    stack := 16
    verified := Unit.encrypt_verified v
    spSafe := Unit.encrypt_spSafe v } (encryptUnitOut _) [] (pubOk_nil _) v.encUnitRes

/-- `vg_aes_xts_decrypt_unit` over `v`. -/
def decryptUnitReg (v : XtsImpl) : Registration Spec.Xts.aesDecryptUnitApi X86_64.target :=
  withScrubOrAll {
    suffix := v.suffix
    code := Impl.AesXts.X86_64Unit.decrypt v.xts
    stack := 16
    verified := Unit.decrypt_verified v
    spSafe := Unit.decrypt_spSafe v } (decryptUnitOut _) [] (pubOk_nil _) v.decUnitRes

/-- `vg_aes_xts_encrypt_unit_to` over `v`. -/
def encryptUnitToReg (v : XtsImpl) : Registration Spec.Xts.aesEncryptUnitToApi X86_64.target :=
  withScrubOrAll {
    suffix := v.suffix
    code := Impl.AesXts.X86_64UnitTo.encrypt v.xts (UnitTo.UnitImpl.of v).xt
    stack := 24
    verified := UnitTo.encrypt_verified (.of v)
    spSafe := UnitTo.encrypt_spSafe (.of v) } (encryptUnitToOut _) [] (pubOk_nil _) v.encUnitToRes

/-- `vg_aes_xts_decrypt_unit_to` over `v`. -/
def decryptUnitToReg (v : XtsImpl) : Registration Spec.Xts.aesDecryptUnitToApi X86_64.target :=
  withScrubOrAll {
    suffix := v.suffix
    code := Impl.AesXts.X86_64UnitTo.decrypt v.xts (UnitTo.UnitImpl.of v).xt
    stack := 24
    verified := UnitTo.decrypt_verified (.of v)
    spSafe := UnitTo.decrypt_spSafe (.of v) } (decryptUnitToOut _) [] (pubOk_nil _) v.decUnitToRes

end VG.Proof.AesXts.X86_64.Scrub
