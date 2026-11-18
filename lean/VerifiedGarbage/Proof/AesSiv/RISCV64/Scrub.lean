module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesSiv.RISCV64.Init
public import VerifiedGarbage.Proof.AesSiv.RISCV64.Verified
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.AesSiv.Scratch

/-!
# AES-SIV on RISC-V, without secret residue

`vg_aes_siv_init`, `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt`, each followed by `Impl.Scrub.RISCV64.scrubTail`
(`RISCV64.Scrub.withScrub`), which clears the caller-saved registers and the
stack its frames used, the working space of its callees with it. Their
postconditions read the memory on return only within the key context, or the data and the synthetic IV
(`RISCV64.Scrub.PostOut`), as on x86-64 (`Proof/AesSiv/X86_64/Frame.lean`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub VG.Proof.Aes.ScrubLocal VG.Proof.AesSiv.RISCV64

/-! ## Postconditions -/

theorem initOut (stack : Nat) :
    PostOut (Spec.Siv.initContract RISCV64.abi stack) (Spec.Siv.initSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [key, kl, ctx], _ =>
      simp only [Spec.Siv.initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      exact keyRepr_local hb.2 h

theorem encryptOut (stack : Nat) :
    PostOut (Spec.Siv.encryptContract RISCV64.abi stack) (Spec.Siv.encryptSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rd, ads, cnt, data, len, siv], _ =>
      simp only [Spec.Siv.encryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr] (Spec.Siv.encryptPost 64) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr] (Spec.Siv.encryptPost 64) _ m m₂ r
      dsimp only [Curry.apply, Spec.Siv.encryptPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      rw [h key hk, Proof.AesSiv.bytesAt_congr fun i hi => Proof.AesSiv.agree_of hb.2.2 i (by omega),
        Proof.AesSiv.bytesAt_congr fun i hi => Proof.AesSiv.agree_of hb.2.1 i (by simpa using hi)]

theorem decryptOut (stack : Nat) :
    PostOut (Spec.Siv.decryptContract RISCV64.abi stack) (Spec.Siv.decryptSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rd, ads, cnt, data, len, siv], _ =>
      simp only [Spec.Siv.decryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr] (Spec.Siv.decryptPost 64) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr] (Spec.Siv.decryptPost 64) _ m m₂ r
      dsimp only [Curry.apply, Spec.Siv.decryptPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      have e := Proof.AesSiv.bytesAt_congr (n := (BitVec.setWidth 64 len).toNat) fun i hi =>
        Proof.AesSiv.agree_of hb.2.1 i (by simpa using hi)
      rw [e]
      exact h key hk

/-! ## The registrations -/

/-- `Spec.Siv.initApi`. -/
def initReg : Registration Spec.Siv.initApi RISCV64.target :=
  withScrub {
      code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a3 Impl.AesSiv.RISCV64.init
      verified := init_framed }
    (initOut _)

/-- `Spec.Siv.encryptApi`. -/
def encryptReg : Registration Spec.Siv.encryptApi RISCV64.target :=
  withScrub {
      code := Impl.StackScratch.RISCV64.withStackScratch 2576 .a7 Impl.AesSiv.RISCV64.encrypt
      verified := Proof.AesSiv.encrypt_keyed encrypt_framed }
    (encryptOut _)

/-- `Spec.Siv.decryptApi`. -/
def decryptReg : Registration Spec.Siv.decryptApi RISCV64.target :=
  withScrub {
      code := Impl.StackScratch.RISCV64.withStackScratch 2576 .a7 Impl.AesSiv.RISCV64.decrypt
      verified := Proof.AesSiv.decrypt_keyed decrypt_framed }
    (decryptOut _)

end VG.Proof.AesSiv.RISCV64.Scrub
