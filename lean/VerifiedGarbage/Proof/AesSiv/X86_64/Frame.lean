module

public import VerifiedGarbage.Proof.AesSiv.Rounds
public import VerifiedGarbage.Proof.AesSiv.X86_64.Verified
public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-SIV on x86-64, with its working space on the stack

`vg_aes_siv_init` runs its code, proved with the working space as an argument
(`Verified.lean`), in a frame of 2568 bytes that allocates it
(`Verified.stackScratch`): the 2560 bytes of working space, and 8 more to
keep `rsp` aligned. Its own calls use 16 bytes below it: two return
addresses, as `vg_aes_ctr32` and `vg_aes_expand_key_scratch` use no stack.
Over implementations of AES that need no working space (`initF`), it needs
only 72 bytes of it, in a frame of 88 (`initF_framed`), which
`X86_64.Scrub.withScrubAll` wipes whole on return (`initReg`).

`encrypt` and `decrypt` run their code, proved with the working space as
their last argument, in a frame that allocates it
(`Verified.stackArgScratchL`): their working space is passed on the stack
after `siv`, so the frame of 2600 bytes holds the 2576 bytes of working
space, a copy of `siv`, the word that stands for the return address and the
address of the working space. The code's own calls use 16 bytes below it.
The frame copies `siv`, so the postconditions and `decrypt`'s leak must read
the memory on entry only within the buffers and the list of slices
(`encryptPost_local`, `decryptPost_local`, `decryptLeak_local`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.Impl.AesSiv.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (UpdateImpl)
open VG.Proof.CmacAes.Stream.X86_64 (ekF)

theorem init_xdepth (v : Ctr32Impl) : (init v.expand v.callee v.suffix).x86_64Depth ≤ 16 := by
  simp only [init, initAt, Impl.CmacAes.X86_64.subkeys, Code.x86_64Depth, v.noStack, v.expandNoStack]
  decide +kernel

theorem initF_xdepth (v : Ctr32Impl) : (initF ekF v.callee v.suffix).x86_64Depth ≤ 16 := by
  have h : ekF.code.x86_64Depth = 0 := Ctr32Impl.aesni.expandNoStack
  simp only [initF, initAt, Impl.CmacAes.X86_64.subkeys, Code.x86_64Depth, v.noStack, h]
  decide +kernel

/-- A state satisfying `vg_aes_siv_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 512⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Siv.initContract X86_64.abi 2584).pre s := by
  implies_sat [Spec.Siv.initContract, Spec.Siv.initSig, Spec.Siv.initPre, Spec.Siv.initPost,
    X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed (v : Ctr32Impl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (init v.expand v.callee v.suffix))
      (Spec.Siv.initContract X86_64.abi 2584) :=
  X86_64.Verified.stackScratch (sig := Spec.Siv.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Siv.initPre X86_64.abi.ptrBits) (post := Spec.Siv.initPost X86_64.abi.ptrBits)
    (wa := true) (stack := 16) (bytes := 2568) (init_verified v) (by decide) (by decide) (by decide)
    (init_spSafe v) (init_xdepth v) initFrameSat_pre

theorem initFrameSatF_pre : ∃ s, (Spec.Siv.initContract X86_64.abi 104).pre s := by
  implies_sat [Spec.Siv.initContract, Spec.Siv.initSig, Spec.Siv.initPre, Spec.Siv.initPost,
    X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using initFrameSat

/-- `init_framed`, over implementations of AES that need no working space
(`initF`): a frame of the 72 bytes of the registers saved, and 16 more to
keep `rsp` aligned. -/
theorem initF_framed (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 88 .rcx (initF ekF v.callee v.suffix))
      (Spec.Siv.initContract X86_64.abi 104) :=
  X86_64.Verified.stackScratch (sig := Spec.Siv.initSig) (nm := "scratch") (e := .u64) (n := 9)
    (pre := Spec.Siv.initPre X86_64.abi.ptrBits) (post := Spec.Siv.initPost X86_64.abi.ptrBits)
    (wa := true) (stack := 16) (bytes := 88) (initF_verified v f) (by decide) (by decide) (by decide)
    (initF_spSafe v) (initF_xdepth v) initFrameSatF_pre

theorem encrypt_xdepth (v : UpdateImpl) : (encrypt v.callee v.ctr.callee v.ctr.suffix).x86_64Depth ≤ 16 := by
  have := v.xdepth
  simp only [encrypt, encryptCore, encS2v, s2vAds, cmacOf, cmacPre, finish, shortTail, longTail, shortMac, longMac,
    copy, ctr, ctrWhole, ctrBody, ctrMin, xorBytes, callUpdate, callFinalize,
    Impl.CmacAes.X86_64.finalize, Impl.CmacAes.X86_64.finPre,
    Impl.CmacAes.Stream.X86_64.copy, Code.x86_64Depth, v.ctr.noStack]
  generalize v.callee.code.x86_64Depth = d at this ⊢
  revert d
  decide +kernel

theorem decrypt_xdepth (v : UpdateImpl) : (decrypt v.callee v.ctr.callee v.ctr.suffix).x86_64Depth ≤ 16 := by
  have := v.xdepth
  simp only [decrypt, openTail, encS2v, s2vAds, cmacOf, cmacPre, finish, shortTail, longTail, shortMac, longMac,
    copy, ctr, ctrWhole, ctrBody, ctrMin, xorBytes, maskData, callUpdate, callFinalize,
    Impl.CmacAes.X86_64.finalize, Impl.CmacAes.X86_64.finPre,
    Impl.CmacAes.Stream.X86_64.copy, Code.x86_64Depth, v.ctr.noStack]
  generalize v.callee.code.x86_64Depth = d at this ⊢
  revert d
  decide +kernel

/-- A state satisfying `vg_aes_siv_encrypt`'s precondition, without the
working space. -/
def encFrameSat : State :=
  { encSat with rd := [⟨0x1000, 512⟩, ⟨0x2000, 0⟩, ⟨0x8008, 8⟩], wr := [⟨0x3000, 0⟩, ⟨0x5000, 16⟩] }

theorem encFrameSat_pre : ∃ s, (Proof.AesSiv.encryptRoundsContract X86_64.abi 2616).pre s := by
  implies_sat [Proof.AesSiv.encryptRoundsContract, Spec.Siv.encryptSig, Spec.Siv.encryptPre, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop]
    [encFrameSat, encSat, Mem.readW, Mem.read] using encFrameSat

theorem encrypt_framed (v : UpdateImpl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 1 (encrypt v.callee v.ctr.callee v.ctr.suffix))
      (Proof.AesSiv.encryptRoundsContract X86_64.abi 2616) :=
  X86_64.Verified.stackArgScratchL (sig := Spec.Siv.encryptSig) (nm := "work") (e := .u64) (n := 322)
    (pre := Spec.Siv.encryptPre X86_64.abi.ptrBits) (post := Proof.AesSiv.encryptRoundsPost X86_64.abi.ptrBits)
    (wa := true) (stack := 16) (bytes := 2600) (encrypt_verified v) (by decide) (by decide) (by decide)
    (encrypt_spSafe v) (encrypt_xdepth v) (Proof.AesSiv.encryptPre_local _) (Proof.AesSiv.encryptPost_local _)
    encFrameSat_pre

/-- A state satisfying `vg_aes_siv_decrypt`'s precondition, without the
working space. -/
def decFrameSat : State :=
  { encSat with rd := [⟨0x1000, 512⟩, ⟨0x5000, 16⟩, ⟨0x2000, 0⟩, ⟨0x8008, 8⟩], wr := [⟨0x3000, 0⟩] }

theorem decFrameSat_pre : ∃ s, (Proof.AesSiv.decryptRoundsContract X86_64.abi 2616).pre s := by
  implies_sat [Proof.AesSiv.decryptRoundsContract, Spec.Siv.decryptSig, Spec.Siv.decryptPre, Proof.AesSiv.decryptRoundsPost,
    Spec.Siv.decryptLeak, X86_64.abi, X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range,
    List.range.loop] [decFrameSat, encSat, Mem.readW, Mem.read] using decFrameSat

theorem decrypt_framed (v : UpdateImpl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 1 (decrypt v.callee v.ctr.callee v.ctr.suffix))
      (Proof.AesSiv.decryptRoundsContract X86_64.abi 2616) :=
  X86_64.Verified.stackArgScratchL (sig := Spec.Siv.decryptSig) (nm := "work") (e := .u64) (n := 322)
    (pre := Spec.Siv.decryptPre X86_64.abi.ptrBits) (post := Proof.AesSiv.decryptRoundsPost X86_64.abi.ptrBits)
    (wa := true) (stack := 16) (bytes := 2600) (leak := some (Spec.Siv.decryptLeak X86_64.abi.ptrBits))
    (decrypt_verified v) (by decide) (by decide) (by decide) (decrypt_spSafe v) (decrypt_xdepth v)
    (Proof.AesSiv.decryptPre_local _) (Proof.AesSiv.decryptPost_local _) decFrameSat_pre
    (hleak := Proof.AesSiv.decryptLeak_local _)

/-! ## Without secret residue -/

section
open VG.X86_64.Scrub

theorem keyRepr_local {m₁ m₂ : Mem} {p : Addr} {key : List Byte}
    (h : ∀ a, Region.Contains ⟨p, 512⟩ a 1 → m₁ a = m₂ a) (hr : Spec.Siv.KeyRepr m₁ p key) :
    Spec.Siv.KeyRepr m₂ p key := by
  have e {d n : Nat} (hn : d + n ≤ 512) :
      Spec.Aes.bytesAt m₂ (p + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt m₁ (p + BitVec.ofNat 64 d) n := by
    simp only [Spec.Aes.bytesAt]
    refine List.map_congr_left fun i hi => (h _ ?_).symm
    have := List.mem_range.mp hi
    rw [VG.Offset.add_add]; exact VG.Offset.contains_base _ (by omega) (by omega)
  obtain ⟨hl, h1, h2, h3, h4⟩ := hr
  have hn : 16 * (Spec.Aes.rounds (key.length / 8) + 1) ≤ 240 := by
    simp only [Spec.Aes.rounds]; rcases hl with h | h | h <;> rw [h] <;> decide
  refine ⟨hl, ?_, ?_, ?_, ?_⟩
  · have := e (d := 0) (n := 16 * (Spec.Aes.rounds (key.length / 8) + 1)) (by omega)
    rw [show p + BitVec.ofNat 64 0 = p from BitVec.add_zero p] at this
    rw [this]; exact h1
  · rw [show p + 240 = p + BitVec.ofNat 64 240 from rfl, e (by decide)]; exact h2
  · rw [show p + 256 = p + BitVec.ofNat 64 256 from rfl, e (by decide)]; exact h3
  · rw [show p + 272 = p + BitVec.ofNat 64 272 from rfl, e (by omega)]; exact h4

theorem initOut (stack : Nat) :
    PostOut (Spec.Siv.initContract X86_64.abi stack) (Spec.Siv.initSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [key, kl, ctx], _ =>
      simp only [Spec.Siv.initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      exact keyRepr_local hb.2 h

/-- `vg_aes_siv_init` over `v`: with no working space for an implementation
that needs none, then without secret residue, its frame of 104 bytes wiped
whole (`withScrubAll`); over the others, as before. -/
def initReg (v : Ctr32Impl) : Registration Spec.Siv.initApi X86_64.target :=
  match v.free with
  | some f =>
    withScrubAll {
      suffix := v.suffix
      code := Impl.StackScratch.X86_64.withStackScratch 88 .rcx (initF ekF v.callee v.suffix)
      stack := 104
      verified := initF_framed v f
      spSafe := VG.X86_64.withStackScratch_spSafe_of (initF_spSafe v) }
      (initOut _)
  | none => {
      suffix := v.suffix
      code := Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (init v.expand v.callee v.suffix)
      stack := 2584
      verified := init_framed v
      spSafe := VG.X86_64.withStackScratch_spSafe_of (init_spSafe v) }

end

end VG.Proof.AesSiv.X86_64
