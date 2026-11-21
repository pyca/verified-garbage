module

public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesSiv.X86.Verified
public import VerifiedGarbage.Proof.CmacAes.Stream.X86.Frame
public import VerifiedGarbage.Spec.Siv.Contract
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Impl.AesSiv.X86
import VerifiedGarbage.Proof.AesSiv.Scratch
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubCall
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.AesSiv.X86.Verified
meta import VerifiedGarbage.Proof.CmacAes.Stream.X86.Frame
meta import VerifiedGarbage.Spec.Siv.Contract
meta import VerifiedGarbage.Proof.AesSiv.Scratch
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Impl.AesSiv.X86

/-!
# AES-SIV on x86 (32-bit), without secret residue

`vg_aes_siv_init`, `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt` read the
memory on return only within the context, the data and `siv` (`initOut`,
`encryptOut`, `decryptOut`), as on PPC64LE (`Proof/AesSiv/PPC64LE/Scrub.lean`):
what the scrub of their frames and calls needs (`X86.Scrub.PostOut`).

Each as emitted (`Impl.AesSiv.X86.Fn`) zeroes the stack of its contract
below `esp` (its frame of working space, `withStackScratch`, and its
callees') and clears the registers, and returns without secret residue
(`X86.Scrub.verifiedScrubbedAll`: `init_scrubbed`, `encrypt_scrubbed`,
`decrypt_scrubbed`). What that needs of the code (`scrubFSide`) holds whatever the
implementation of AES (`init_scrub`, …): from SIV's code with stub
implementations, whose code is `.block []`, which the kernel evaluates once
(`init_side`, …), the implementation's own facts (`Ctr32Impl.scrub`,
`expandScrub`, their stacks), and `Fill`, which `fill_calls` proves by
walking only SIV's code. `vg_cmac_aes_update` chains in a register with
AES-NI and by calls otherwise (`Impl.CmacAes.X86.hardware`), so `encrypt`
and `decrypt` have a stub of each.
-/

@[expose] public section

namespace VG.Proof.AesSiv.X86.Scrub

open VG.X86 VG.X86.Scrub

/-- An index below a length argument, which the contract reads as its low
32 bits, is below the length of the buffer `Sig.bufs` gives it. -/
private theorem lt_len {x : BitVec 64} {i : Nat} (h : i < (x.setWidth abi.ptrBits).toNat) : i < x.toNat := by
  rw [BitVec.toNat_setWidth] at h
  exact Nat.lt_of_lt_of_le h (Nat.mod_le _ _)

theorem initOut (stack : Nat) :
    PostOut (Spec.Siv.initContract abi stack) (Spec.Siv.initSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.AesSiv.initPostOut_local _)

theorem encryptOut (stack : Nat) :
    PostOut (Spec.Siv.encryptContract abi stack) (Spec.Siv.encryptSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rd, ads, cnt, data, len, siv], _ =>
      simp only [Spec.Siv.encryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr,
        ArgWord.int abi.ptrBits, ArgWord.addr] (Spec.Siv.encryptPost abi.ptrBits) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr,
        ArgWord.int abi.ptrBits, ArgWord.addr] (Spec.Siv.encryptPost abi.ptrBits) _ m m₂ r
      dsimp only [Curry.apply, Spec.Siv.encryptPost, ArgWord.ofRaw] at h ⊢
      intro key hk
      rw [h key hk, Proof.AesSiv.bytesAt_congr fun i hi => Proof.AesSiv.agree_of hb.2.2 i (by omega),
        Proof.AesSiv.bytesAt_congr fun i hi => Proof.AesSiv.agree_of hb.2.1 i (lt_len hi)]

theorem decryptOut (stack : Nat) :
    PostOut (Spec.Siv.decryptContract abi stack) (Spec.Siv.decryptSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rd, ads, cnt, data, len, siv], _ =>
      simp only [Spec.Siv.decryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr,
        ArgWord.int abi.ptrBits, ArgWord.addr] (Spec.Siv.decryptPost abi.ptrBits) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr,
        ArgWord.int abi.ptrBits, ArgWord.addr] (Spec.Siv.decryptPost abi.ptrBits) _ m m₂ r
      dsimp only [Curry.apply, Spec.Siv.decryptPost, ArgWord.ofRaw] at h ⊢
      intro key hk
      have e := Proof.AesSiv.bytesAt_congr (n := (BitVec.setWidth abi.ptrBits len).toNat) fun i hi =>
        Proof.AesSiv.agree_of hb.2.1 i (lt_len hi)
      rw [e]
      exact h key hk

/-! ## What the scrub needs of the code -/

open Impl.StackScratch.X86 (withStackScratch)
open Proof.Aes.X86 (Ctr32Impl)

/-- AES in counter mode with no code, by the name that chooses the
chaining by calls (`Impl.CmacAes.X86.hardware`). -/
def stubCtr : Impl.Aes.X86.Ctr32 := ⟨"", .block []⟩

/-- `stubCtr` by the name that chooses the chaining with AES-NI. -/
def stubCtrNi : Impl.Aes.X86.Ctr32 := ⟨"vg_aes_ctr32_to_aesni", .block []⟩

/-- AES's key expansion with no code. -/
def stubExpand : Impl.Aes.X86.ExpandKey := ⟨"", .block []⟩

-- SIV's own code, with the stubs, as literals for the kernel's evaluation.
materialize_code initStub := withStackScratch 2580 3 (Impl.AesSiv.X86.initCore stubExpand stubCtr "")
materialize_code encryptStub := withStackScratch 2612 7 (Impl.AesSiv.X86.encrypt stubCtr "")
materialize_code encryptStubNi := withStackScratch 2612 7 (Impl.AesSiv.X86.encrypt stubCtrNi "")
materialize_code decryptStub := withStackScratch 2612 7 (Impl.AesSiv.X86.decrypt stubCtr "")
materialize_code decryptStubNi := withStackScratch 2612 7 (Impl.AesSiv.X86.decrypt stubCtrNi "")

theorem init_side :
    scrubFSide (withStackScratch 2580 3 (Impl.AesSiv.X86.initCore stubExpand stubCtr "")) [] 2632 = true := by
  lit_decide

theorem encrypt_side : scrubFSide (withStackScratch 2612 7 (Impl.AesSiv.X86.encrypt stubCtr "")) [] 2672 = true := by
  lit_decide

theorem encryptNi_side :
    scrubFSide (withStackScratch 2612 7 (Impl.AesSiv.X86.encrypt stubCtrNi "")) [] 2672 = true := by
  lit_decide

theorem decrypt_side : scrubFSide (withStackScratch 2612 7 (Impl.AesSiv.X86.decrypt stubCtr "")) [] 2672 = true := by
  lit_decide

theorem decryptNi_side :
    scrubFSide (withStackScratch 2612 7 (Impl.AesSiv.X86.decrypt stubCtrNi "")) [] 2672 = true := by
  lit_decide

theorem init_fill (e : Impl.Aes.X86.ExpandKey) (c : Impl.Aes.X86.Ctr32) (sfx : String)
    (he : calleeSide e.code 0 = true) (hc : calleeSide c.code 0 = true) :
    Fill 0 (withStackScratch 2580 3 (Impl.AesSiv.X86.initCore stubExpand stubCtr ""))
      (withStackScratch 2580 3 (Impl.AesSiv.X86.initCore e c sfx)) := by
  fill_calls

theorem encrypt_fill (c : Impl.Aes.X86.Ctr32) (sfx : String) (hc : calleeSide c.code 0 = true)
    (h : ¬Impl.CmacAes.X86.hardware c = true) :
    Fill 0 (withStackScratch 2612 7 (Impl.AesSiv.X86.encrypt stubCtr ""))
      (withStackScratch 2612 7 (Impl.AesSiv.X86.encrypt c sfx)) := by
  fill_calls

theorem encryptNi_fill (c : Impl.Aes.X86.Ctr32) (sfx : String) (hc : calleeSide c.code 0 = true)
    (h : Impl.CmacAes.X86.hardware c = true) :
    Fill 0 (withStackScratch 2612 7 (Impl.AesSiv.X86.encrypt stubCtrNi ""))
      (withStackScratch 2612 7 (Impl.AesSiv.X86.encrypt c sfx)) := by
  fill_calls

theorem decrypt_fill (c : Impl.Aes.X86.Ctr32) (sfx : String) (hc : calleeSide c.code 0 = true)
    (h : ¬Impl.CmacAes.X86.hardware c = true) :
    Fill 0 (withStackScratch 2612 7 (Impl.AesSiv.X86.decrypt stubCtr ""))
      (withStackScratch 2612 7 (Impl.AesSiv.X86.decrypt c sfx)) := by
  fill_calls

theorem decryptNi_fill (c : Impl.Aes.X86.Ctr32) (sfx : String) (hc : calleeSide c.code 0 = true)
    (h : Impl.CmacAes.X86.hardware c = true) :
    Fill 0 (withStackScratch 2612 7 (Impl.AesSiv.X86.decrypt stubCtrNi ""))
      (withStackScratch 2612 7 (Impl.AesSiv.X86.decrypt c sfx)) := by
  fill_calls

/-- `scrubFSide` of `vg_aes_siv_init`, whatever the implementation. -/
theorem init_scrub (v : Ctr32Impl) :
    scrubFSide (withStackScratch 2580 3 (Impl.AesSiv.X86.initCore v.expand v.callee v.suffix)) [] 2632 = true :=
  scrubFSide_of_fill (init_fill _ _ _ (calleeSide_of_eq v.expandStack v.expandScrub)
    (calleeSide_of_eq v.stack v.scrub)) init_side

/-- `scrubFSide` of `vg_aes_siv_encrypt`, whatever the implementation. -/
theorem encrypt_scrub (v : Ctr32Impl) :
    scrubFSide (withStackScratch 2612 7 (Impl.AesSiv.X86.encrypt v.callee v.suffix)) [] 2672 = true := by
  by_cases h : Impl.CmacAes.X86.hardware v.callee = true
  · exact scrubFSide_of_fill (encryptNi_fill _ _ (calleeSide_of_eq v.stack v.scrub) h) encryptNi_side
  · exact scrubFSide_of_fill (encrypt_fill _ _ (calleeSide_of_eq v.stack v.scrub) h) encrypt_side

/-- `scrubFSide` of `vg_aes_siv_decrypt`, whatever the implementation. -/
theorem decrypt_scrub (v : Ctr32Impl) :
    scrubFSide (withStackScratch 2612 7 (Impl.AesSiv.X86.decrypt v.callee v.suffix)) [] 2672 = true := by
  by_cases h : Impl.CmacAes.X86.hardware v.callee = true
  · exact scrubFSide_of_fill (decryptNi_fill _ _ (calleeSide_of_eq v.stack v.scrub) h) decryptNi_side
  · exact scrubFSide_of_fill (decrypt_fill _ _ (calleeSide_of_eq v.stack v.scrub) h) decrypt_side

/-! ## The functions as emitted -/

/-- `vg_aes_siv_init` over `v` as emitted (`Impl.AesSiv.X86.Fn.init`)
meets its contract in constant time and returns without secret residue. -/
theorem init_scrubbed (v : Ctr32Impl) :
    VerifiedScrubbed X86.target (Impl.AesSiv.X86.Fn.init v.expand v.callee v.suffix)
      (Spec.Siv.initContract X86.abi 2632) 0 :=
  verifiedScrubbedAll (api := Spec.Siv.initApi) {
      suffix := v.suffix
      code := withStackScratch 2580 3 (Impl.AesSiv.X86.initCore v.expand v.callee v.suffix)
      verified := init_framed v
      spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe (init_spSafe v) }
    (initOut _) (W := 2632) (hs := init_scrub v)

/-- `vg_aes_siv_encrypt` over `v` as emitted (`Impl.AesSiv.X86.Fn.encrypt`)
meets its contract in constant time and returns without secret residue. -/
theorem encrypt_scrubbed (v : Ctr32Impl) :
    VerifiedScrubbed X86.target (Impl.AesSiv.X86.Fn.encrypt v.callee v.suffix)
      (Spec.Siv.encryptContract X86.abi 2672) 0 :=
  verifiedScrubbedAll (api := Spec.Siv.encryptApi) {
      suffix := v.suffix
      code := withStackScratch 2612 7 (Impl.AesSiv.X86.encrypt v.callee v.suffix)
      verified := Proof.AesSiv.encrypt_keyed (encrypt_framed v)
      spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe (encrypt_spSafe v) }
    (encryptOut _) (W := 2672) (hs := encrypt_scrub v)

/-- `vg_aes_siv_decrypt` over `v` as emitted (`Impl.AesSiv.X86.Fn.decrypt`)
meets its contract in constant time and returns without secret residue. -/
theorem decrypt_scrubbed (v : Ctr32Impl) :
    VerifiedScrubbed X86.target (Impl.AesSiv.X86.Fn.decrypt v.callee v.suffix)
      (Spec.Siv.decryptContract X86.abi 2672) 32 :=
  verifiedScrubbedAll (api := Spec.Siv.decryptApi) {
      suffix := v.suffix
      code := withStackScratch 2612 7 (Impl.AesSiv.X86.decrypt v.callee v.suffix)
      verified := Proof.AesSiv.decrypt_keyed (decrypt_framed v)
      spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe (decrypt_spSafe v) }
    (decryptOut _) (W := 2672) (hs := decrypt_scrub v)

/-- `Impl.AesSiv.X86.Fn.init` writes `esp` only in its frames and calls. -/
theorem init_fnSpSafe (v : Ctr32Impl) :
    (Impl.AesSiv.X86.Fn.init v.expand v.callee v.suffix).all (fun i => !X86.isa.writesSp i) = true :=
  scrubAll_spSafe (Proof.CmacAes.Stream.X86.withStackScratch_spSafe (init_spSafe v))

/-- `Impl.AesSiv.X86.Fn.encrypt` writes `esp` only in its frames and calls. -/
theorem encrypt_fnSpSafe (v : Ctr32Impl) :
    (Impl.AesSiv.X86.Fn.encrypt v.callee v.suffix).all (fun i => !X86.isa.writesSp i) = true :=
  scrubAll_spSafe (Proof.CmacAes.Stream.X86.withStackScratch_spSafe (encrypt_spSafe v))

/-- `Impl.AesSiv.X86.Fn.decrypt` writes `esp` only in its frames and calls. -/
theorem decrypt_fnSpSafe (v : Ctr32Impl) :
    (Impl.AesSiv.X86.Fn.decrypt v.callee v.suffix).all (fun i => !X86.isa.writesSp i) = true :=
  scrubAll_spSafe (Proof.CmacAes.Stream.X86.withStackScratch_spSafe (decrypt_spSafe v))

end VG.Proof.AesSiv.X86.Scrub
