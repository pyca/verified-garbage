module

public import VerifiedGarbage.Proof.AesSiv.Scratch
public import VerifiedGarbage.Proof.AesSiv.X86_64.Verified
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubChunks
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-SIV on x86-64, with its working space on the stack

`vg_aes_siv_init` runs its code, proved with the working space as an argument
(`Verified.lean`), in a frame of 2568 bytes that allocates it
(`Verified.stackScratchKept`): the 2560 bytes of working space, and 8 more to
keep `rsp` aligned. Its own calls use 16 bytes below it: two return
addresses, as `vg_aes_ctr32` and `vg_aes_expand_key_scratch` use no stack.
Over the bitsliced AES given its working space 512 bytes into
`vg_cmac_aes_subkeys`'s scratch buffer (`initS`), it needs only 1920 bytes,
in a frame of 1928 (`initS_framed`).
Over implementations of AES that need no working space (`initF`), it needs
only 72 bytes of it, in a frame of 88 (`initF_framed`), which
`X86_64.Scrub.withScrubAll` wipes whole on return (`initReg`).

`encrypt` and `decrypt` run their code, proved with the working space as
their last argument, in a frame that allocates it
(`Verified.stackArgScratchLKept`): their working space is passed on the stack
after `siv`, so the frame of 2600 bytes holds the 2576 bytes of working
space, a copy of `siv`, the word that stands for the return address and the
address of the working space. The code's own calls use 16 bytes below it.
The frame copies `siv`, so the postconditions and `decrypt`'s leak must read
the memory on entry only within the buffers and the list of slices
(`encryptPost_local`, `decryptPost_local`, `decryptLeak_local`).
Over implementations of `vg_cmac_aes_update` and `vg_aes_ctr32` that never
touch their scratch buffers (`UpdateImpl.free` and `Ctr32Impl.free`), the
working space is 288 bytes (`Lay.free`: the code's own 256, the counter block
of `vg_cmac_aes_finalize` and S2V's state), in a frame of 312
(`encryptF_framed`, `decryptF_framed`). Over implementations that give the
bitsliced AES its working space 512 bytes into their scratch buffers
(`UpdateImpl.small` and `Ctr32Impl.small`), the working space is 1936 bytes
(`Lay.small`), in a frame of 1960 (`encryptS_framed`, `decryptS_framed`).

Over the bitsliced AES (`Ctr32Impl.free` is `none`), the frames of `init`,
`encrypt` and `decrypt` are mostly the working space of the functions they
call, which AES writes, and are wiped whole on return
(`X86_64.Scrub.withScrubAll`: `initReg`, `encryptReg`, `decryptReg`); the
frames of 312 bytes (`encryptRegF`, `decryptRegF`) are wiped whole too, in
the chunks `[8, 320]`, whose 16-byte stores are aligned
(`X86_64.RScrub.withScrubAllC`); their
postconditions read the memory on return only within the key context, or
the data and the synthetic IV (`initOut`, `encryptOut`, `decryptOut`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.Impl.AesSiv.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (UpdateImpl)
open VG.Proof.CmacAes.Stream.X86_64 (ekF)

theorem init_xdepth (v : Ctr32Impl) : (init v.expand v.callee v.suffix).x86_64Depth ≤ 16 := by
  simp only [init, initAt, Impl.CmacAes.X86_64.subkeys, Code.x86_64Depth,
    Proof.CmacAes.X86_64.ctrCall_xdepth, v.noStack, v.expandNoStack]
  decide +kernel

theorem initF_xdepth (v : Ctr32Impl) : (initF ekF v.callee v.suffix).x86_64Depth ≤ 16 := by
  have h : ekF.code.x86_64Depth = 0 := Ctr32Impl.aesni.expandNoStack
  simp only [initF, initAt, Impl.CmacAes.X86_64.subkeys, Code.x86_64Depth,
    Proof.CmacAes.X86_64.ctrCall_xdepth, v.noStack, h]
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
  X86_64.Verified.stackScratchKept (sig := Spec.Siv.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Siv.initPre X86_64.abi.ptrBits) (post := Spec.Siv.initPost X86_64.abi.ptrBits)
    (wa := true) (stack := 16) (bytes := 2568) (init_verified v) (by decide) (by decide) (by decide)
    (init_spSafe v) (init_xdepth v) initFrameSat_pre

theorem initS_xdepth (v : Ctr32Impl) : (initS v.expand v.callee v.suffix).x86_64Depth ≤ 16 := by
  have := init_xdepth v
  simp only [initS, init, initAt, Code.x86_64Depth] at this ⊢
  exact this

theorem initFrameSatS_pre : ∃ s, (Spec.Siv.initContract X86_64.abi 1944).pre s := by
  implies_sat [Spec.Siv.initContract, Spec.Siv.initSig, Spec.Siv.initPre, Spec.Siv.initPost,
    X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using initFrameSat

/-- `init_framed`, over an implementation of `vg_aes_ctr32` given its working
space 512 bytes in (`initS`): a frame of the 1920 bytes of working space,
and 8 more to keep `rsp` aligned. -/
theorem initS_framed (v : Ctr32Impl) (g : Proof.Aes.X86_64.Ctr32Small v.callee) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 1928 .rcx (initS v.expand v.callee v.suffix))
      (Spec.Siv.initContract X86_64.abi 1944) :=
  X86_64.Verified.stackScratchKept (sig := Spec.Siv.initSig) (nm := "scratch") (e := .u64) (n := 240)
    (pre := Spec.Siv.initPre X86_64.abi.ptrBits) (post := Spec.Siv.initPost X86_64.abi.ptrBits)
    (wa := true) (stack := 16) (bytes := 1928) (initS_verified v g) (by decide) (by decide) (by decide)
    (initS_spSafe v) (initS_xdepth v) initFrameSatS_pre

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
  X86_64.Verified.stackScratchKept (sig := Spec.Siv.initSig) (nm := "scratch") (e := .u64) (n := 9)
    (pre := Spec.Siv.initPre X86_64.abi.ptrBits) (post := Spec.Siv.initPost X86_64.abi.ptrBits)
    (wa := true) (stack := 16) (bytes := 88) (initF_verified v f) (by decide) (by decide) (by decide)
    (initF_spSafe v) (initF_xdepth v) initFrameSatF_pre

theorem encrypt_xdepth {g : Lay} (hg : g.Ok) (v : UpdateImpl) :
    (encrypt g.x g.n v.callee v.ctr.callee v.ctr.suffix).x86_64Depth ≤ 16 := by
  have := v.xdepth
  rcases hg with rfl | rfl | rfl
  all_goals
  simp only [encrypt, encryptCore, encS2v, s2vAds, cmacOf, cmacPre, finish, shortTail, longTail, shortMac, longMac,
    copy, ctr, ctrWhole, ctrBody, ctrMin, xorBytes, callUpdate, callFinalize,
    Impl.CmacAes.X86_64.finalize, Impl.CmacAes.X86_64.finPre,
    Impl.CmacAes.Stream.X86_64.copy, Code.x86_64Depth, Proof.CmacAes.X86_64.ctrCall_xdepth, v.ctr.noStack]
  generalize v.callee.code.x86_64Depth = d at this ⊢
  revert d
  decide +kernel

theorem decrypt_xdepth {g : Lay} (hg : g.Ok) (v : UpdateImpl) :
    (decrypt g.x g.n v.callee v.ctr.callee v.ctr.suffix).x86_64Depth ≤ 16 := by
  have := v.xdepth
  rcases hg with rfl | rfl | rfl
  all_goals
  simp only [decrypt, openTail, encS2v, s2vAds, cmacOf, cmacPre, finish, shortTail, longTail, shortMac, longMac,
    copy, ctr, ctrWhole, ctrBody, ctrMin, xorBytes, maskData, callUpdate, callFinalize,
    Impl.CmacAes.X86_64.finalize, Impl.CmacAes.X86_64.finPre,
    Impl.CmacAes.Stream.X86_64.copy, Code.x86_64Depth, Proof.CmacAes.X86_64.ctrCall_xdepth, v.ctr.noStack]
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
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 1 (encrypt csImm dOff v.callee v.ctr.callee v.ctr.suffix))
      (Proof.AesSiv.encryptRoundsContract X86_64.abi 2616) :=
  X86_64.Verified.stackArgScratchLKept (sig := Spec.Siv.encryptSig) (nm := "work") (e := .u64) (n := 322)
    (pre := Spec.Siv.encryptPre X86_64.abi.ptrBits) (post := Proof.AesSiv.encryptRoundsPost X86_64.abi.ptrBits)
    (wa := true) (stack := 16) (bytes := 2600) (encrypt_verified v) (by decide) (by decide) (by decide)
    (encrypt_spSafe (.inl rfl) v) (encrypt_xdepth (.inl rfl) v) (Proof.AesSiv.encryptPre_local _)
    (Proof.AesSiv.encryptPost_local _) encFrameSat_pre

theorem encFrameSatF_pre : ∃ s, (Proof.AesSiv.encryptRoundsContract X86_64.abi 328).pre s := by
  implies_sat [Proof.AesSiv.encryptRoundsContract, Spec.Siv.encryptSig, Spec.Siv.encryptPre, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop]
    [encFrameSat, encSat, Mem.readW, Mem.read] using encFrameSat

/-- `encrypt_framed`, over implementations of `vg_cmac_aes_update` and
`vg_aes_ctr32` that never touch their scratch buffers: a frame of 312 bytes,
the 288 of working space, a copy of `siv`, the word that stands for the
return address and the address of the working space. -/
theorem encryptF_framed (v : UpdateImpl) (f : Proof.CmacAes.X86_64.UpdateFree v.callee)
    (fc : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 312 1 (encrypt csImmF dOffF v.callee v.ctr.callee v.ctr.suffix))
      (Proof.AesSiv.encryptRoundsContract X86_64.abi 328) :=
  X86_64.Verified.stackArgScratchLKept (sig := Spec.Siv.encryptSig) (nm := "work") (e := .u64) (n := 36)
    (pre := Spec.Siv.encryptPre X86_64.abi.ptrBits) (post := Proof.AesSiv.encryptRoundsPost X86_64.abi.ptrBits)
    (wa := true) (stack := 16) (bytes := 312) (encryptF_verified v f fc) (by decide) (by decide) (by decide)
    (encrypt_spSafe (.inr (.inl rfl)) v) (encrypt_xdepth (.inr (.inl rfl)) v) (Proof.AesSiv.encryptPre_local _)
    (Proof.AesSiv.encryptPost_local _) encFrameSatF_pre

theorem encFrameSatS_pre : ∃ s, (Proof.AesSiv.encryptRoundsContract X86_64.abi 1976).pre s := by
  implies_sat [Proof.AesSiv.encryptRoundsContract, Spec.Siv.encryptSig, Spec.Siv.encryptPre, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop]
    [encFrameSat, encSat, Mem.readW, Mem.read] using encFrameSat

/-- `encrypt_framed`, over implementations of `vg_cmac_aes_update` and
`vg_aes_ctr32` that give the bitsliced AES its working space 512 bytes into
their scratch buffers: a frame of 1960 bytes, the 1936 of working space of
`Lay.small`, a copy of `siv`, the word that stands for the return address and
the address of the working space. -/
theorem encryptS_framed (v : UpdateImpl) (f : Proof.CmacAes.X86_64.UpdateSmall v.callee)
    (fc : Proof.Aes.X86_64.Ctr32Small v.ctr.callee) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 1960 1 (encrypt csImmS dOffS v.callee v.ctr.callee v.ctr.suffix))
      (Proof.AesSiv.encryptRoundsContract X86_64.abi 1976) :=
  X86_64.Verified.stackArgScratchLKept (sig := Spec.Siv.encryptSig) (nm := "work") (e := .u64) (n := 242)
    (pre := Spec.Siv.encryptPre X86_64.abi.ptrBits) (post := Proof.AesSiv.encryptRoundsPost X86_64.abi.ptrBits)
    (wa := true) (stack := 16) (bytes := 1960) (encryptS_verified v f fc) (by decide) (by decide) (by decide)
    (encrypt_spSafe (.inr (.inr rfl)) v) (encrypt_xdepth (.inr (.inr rfl)) v) (Proof.AesSiv.encryptPre_local _)
    (Proof.AesSiv.encryptPost_local _) encFrameSatS_pre

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
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 1 (decrypt csImm dOff v.callee v.ctr.callee v.ctr.suffix))
      (Proof.AesSiv.decryptRoundsContract X86_64.abi 2616) :=
  X86_64.Verified.stackArgScratchLKept (sig := Spec.Siv.decryptSig) (nm := "work") (e := .u64) (n := 322)
    (pre := Spec.Siv.decryptPre X86_64.abi.ptrBits) (post := Proof.AesSiv.decryptRoundsPost X86_64.abi.ptrBits)
    (wa := true) (stack := 16) (bytes := 2600) (leak := some (Spec.Siv.decryptLeak X86_64.abi.ptrBits))
    (decrypt_verified v) (by decide) (by decide) (by decide) (decrypt_spSafe (.inl rfl) v)
    (decrypt_xdepth (.inl rfl) v) (Proof.AesSiv.decryptPre_local _) (Proof.AesSiv.decryptPost_local _)
    decFrameSat_pre (hleak := Proof.AesSiv.decryptLeak_local _)

theorem decFrameSatF_pre : ∃ s, (Proof.AesSiv.decryptRoundsContract X86_64.abi 328).pre s := by
  implies_sat [Proof.AesSiv.decryptRoundsContract, Spec.Siv.decryptSig, Spec.Siv.decryptPre, Proof.AesSiv.decryptRoundsPost,
    Spec.Siv.decryptLeak, X86_64.abi, X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range,
    List.range.loop] [decFrameSat, encSat, Mem.readW, Mem.read] using decFrameSat

/-- `decrypt_framed`, in a frame of 312 bytes, as `encryptF_framed`. -/
theorem decryptF_framed (v : UpdateImpl) (f : Proof.CmacAes.X86_64.UpdateFree v.callee)
    (fc : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 312 1 (decrypt csImmF dOffF v.callee v.ctr.callee v.ctr.suffix))
      (Proof.AesSiv.decryptRoundsContract X86_64.abi 328) :=
  X86_64.Verified.stackArgScratchLKept (sig := Spec.Siv.decryptSig) (nm := "work") (e := .u64) (n := 36)
    (pre := Spec.Siv.decryptPre X86_64.abi.ptrBits) (post := Proof.AesSiv.decryptRoundsPost X86_64.abi.ptrBits)
    (wa := true) (stack := 16) (bytes := 312) (leak := some (Spec.Siv.decryptLeak X86_64.abi.ptrBits))
    (decryptF_verified v f fc) (by decide) (by decide) (by decide) (decrypt_spSafe (.inr (.inl rfl)) v)
    (decrypt_xdepth (.inr (.inl rfl)) v) (Proof.AesSiv.decryptPre_local _) (Proof.AesSiv.decryptPost_local _)
    decFrameSatF_pre (hleak := Proof.AesSiv.decryptLeak_local _)

theorem decFrameSatS_pre : ∃ s, (Proof.AesSiv.decryptRoundsContract X86_64.abi 1976).pre s := by
  implies_sat [Proof.AesSiv.decryptRoundsContract, Spec.Siv.decryptSig, Spec.Siv.decryptPre, Proof.AesSiv.decryptRoundsPost,
    Spec.Siv.decryptLeak, X86_64.abi, X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range,
    List.range.loop] [decFrameSat, encSat, Mem.readW, Mem.read] using decFrameSat

/-- `decrypt_framed`, in a frame of 1960 bytes, as `encryptS_framed`. -/
theorem decryptS_framed (v : UpdateImpl) (f : Proof.CmacAes.X86_64.UpdateSmall v.callee)
    (fc : Proof.Aes.X86_64.Ctr32Small v.ctr.callee) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 1960 1 (decrypt csImmS dOffS v.callee v.ctr.callee v.ctr.suffix))
      (Proof.AesSiv.decryptRoundsContract X86_64.abi 1976) :=
  X86_64.Verified.stackArgScratchLKept (sig := Spec.Siv.decryptSig) (nm := "work") (e := .u64) (n := 242)
    (pre := Spec.Siv.decryptPre X86_64.abi.ptrBits) (post := Proof.AesSiv.decryptRoundsPost X86_64.abi.ptrBits)
    (wa := true) (stack := 16) (bytes := 1960) (leak := some (Spec.Siv.decryptLeak X86_64.abi.ptrBits))
    (decryptS_verified v f fc) (by decide) (by decide) (by decide) (decrypt_spSafe (.inr (.inr rfl)) v)
    (decrypt_xdepth (.inr (.inr rfl)) v) (Proof.AesSiv.decryptPre_local _) (Proof.AesSiv.decryptPost_local _)
    decFrameSatS_pre (hleak := Proof.AesSiv.decryptLeak_local _)

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
    rw [VG.Offset.add_add]; exact VG.Offset.contains_base _ (by omega_using [hn, this]) (by omega_using [hn, this])
  obtain ⟨hl, h1, h2, h3, h4⟩ := hr
  have hn : 16 * (Spec.Aes.rounds (key.length / 8) + 1) ≤ 240 := by
    simp only [Spec.Aes.rounds]; rcases hl with h | h | h <;> rw [h] <;> decide
  refine ⟨hl, ?_, ?_, ?_, ?_⟩
  · have := e (d := 0) (n := 16 * (Spec.Aes.rounds (key.length / 8) + 1)) (by omega_using [hn])
    rw [show p + BitVec.ofNat 64 0 = p from BitVec.add_zero p] at this
    rw [this]; exact h1
  · rw [show p + 240 = p + BitVec.ofNat 64 240 from rfl, e (by decide)]; exact h2
  · rw [show p + 256 = p + BitVec.ofNat 64 256 from rfl, e (by decide)]; exact h3
  · rw [show p + 272 = p + BitVec.ofNat 64 272 from rfl, e (by omega_using [hn])]; exact h4

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
whole (`withScrubAll`); over the others, its frame, the working space AES
writes, wiped whole: 1944 bytes over an implementation of `vg_aes_ctr32` that
leaves the first 512 bytes of its scratch buffer untouched (`v.small`), else
2584. -/
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
  | none =>
    match v.small with
    | some g =>
      withScrubAll {
        suffix := v.suffix
        code := Impl.StackScratch.X86_64.withStackScratch 1928 .rcx (initS v.expand v.callee v.suffix)
        stack := 1944
        verified := initS_framed v g
        spSafe := VG.X86_64.withStackScratch_spSafe_of (initS_spSafe v) }
        (initOut _)
    | none =>
      withScrubAll {
        suffix := v.suffix
        code := Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (init v.expand v.callee v.suffix)
        stack := 2584
        verified := init_framed v
        spSafe := VG.X86_64.withStackScratch_spSafe_of (init_spSafe v) }
        (initOut _)

theorem encryptOut (stack : Nat) :
    PostOut (Spec.Siv.encryptContract X86_64.abi stack) (Spec.Siv.encryptSig.retBits 64) :=
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
    PostOut (Spec.Siv.decryptContract X86_64.abi stack) (Spec.Siv.decryptSig.retBits 64) :=
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

/-- `vg_aes_siv_encrypt` over implementations of `vg_cmac_aes_update` and
`vg_aes_ctr32` that never touch their scratch buffers: in a frame of 312
bytes, its working space the 288 of `Lay.free`, its 328 bytes of stack wiped
whole on return (`withScrubAllC`). -/
def encryptRegF (v : UpdateImpl) (f : Proof.CmacAes.X86_64.UpdateFree v.callee)
    (fc : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) : Registration Spec.Siv.encryptApi X86_64.target :=
  let r : Registration Spec.Siv.encryptApi X86_64.target := {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 312 1
      (encrypt csImmF dOffF v.callee v.ctr.callee v.ctr.suffix)
    stack := 328
    verified := Proof.AesSiv.encrypt_keyed (encryptF_framed v f fc)
    spSafe := X86_64.withStackArgScratch_spSafe (encrypt_spSafe (.inr (.inl rfl)) v) }
  VG.X86_64.RScrub.withScrubAllC r (encryptOut _) [8, 320]

/-- `vg_aes_siv_encrypt` over `v`. Over implementations that need no working
space (`v.free` and `v.ctr.free`), in the frame of 312 bytes of `encryptRegF`.
Otherwise in a frame mostly the working space of the functions it calls: over
an implementation of AES that needs it (`v.ctr.free` is `none`), wiped whole
on return (`withScrubAll`), of 1960 bytes over implementations that leave the
first 512 bytes of their scratch buffers untouched (`v.small` and
`v.ctr.small`), else 2600; over the others, of 2600 bytes, as before. -/
def encryptReg (v : UpdateImpl) : Registration Spec.Siv.encryptApi X86_64.target :=
  let r : Registration Spec.Siv.encryptApi X86_64.target := {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2600 1
      (encrypt csImm dOff v.callee v.ctr.callee v.ctr.suffix)
    stack := 2616
    verified := Proof.AesSiv.encrypt_keyed (encrypt_framed v)
    spSafe := X86_64.withStackArgScratch_spSafe (encrypt_spSafe (.inl rfl) v) }
  match v.free, v.ctr.free with
  | some f, some fc => encryptRegF v f fc
  | none, some _ => r
  | _, none =>
    match v.small, v.ctr.small with
    | some f, some fc => withScrubAll {
        suffix := v.suffix
        code := Impl.StackScratch.X86_64.withStackArgScratch 1960 1
          (encrypt csImmS dOffS v.callee v.ctr.callee v.ctr.suffix)
        stack := 1976
        verified := Proof.AesSiv.encrypt_keyed (encryptS_framed v f fc)
        spSafe := X86_64.withStackArgScratch_spSafe (encrypt_spSafe (.inr (.inr rfl)) v) }
        (encryptOut _)
    | _, _ => withScrubAll r (encryptOut _)

/-- `vg_aes_siv_decrypt` in a frame of 312 bytes, as `encryptRegF`. -/
def decryptRegF (v : UpdateImpl) (f : Proof.CmacAes.X86_64.UpdateFree v.callee)
    (fc : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) : Registration Spec.Siv.decryptApi X86_64.target :=
  let r : Registration Spec.Siv.decryptApi X86_64.target := {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 312 1
      (decrypt csImmF dOffF v.callee v.ctr.callee v.ctr.suffix)
    stack := 328
    verified := Proof.AesSiv.decrypt_keyed (decryptF_framed v f fc)
    spSafe := X86_64.withStackArgScratch_spSafe (decrypt_spSafe (.inr (.inl rfl)) v) }
  VG.X86_64.RScrub.withScrubAllC r (decryptOut _) [8, 320]

/-- `vg_aes_siv_decrypt` over `v`, as `encryptReg`. -/
def decryptReg (v : UpdateImpl) : Registration Spec.Siv.decryptApi X86_64.target :=
  let r : Registration Spec.Siv.decryptApi X86_64.target := {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2600 1
      (decrypt csImm dOff v.callee v.ctr.callee v.ctr.suffix)
    stack := 2616
    verified := Proof.AesSiv.decrypt_keyed (decrypt_framed v)
    spSafe := X86_64.withStackArgScratch_spSafe (decrypt_spSafe (.inl rfl) v) }
  match v.free, v.ctr.free with
  | some f, some fc => decryptRegF v f fc
  | none, some _ => r
  | _, none =>
    match v.small, v.ctr.small with
    | some f, some fc => withScrubAll {
        suffix := v.suffix
        code := Impl.StackScratch.X86_64.withStackArgScratch 1960 1
          (decrypt csImmS dOffS v.callee v.ctr.callee v.ctr.suffix)
        stack := 1976
        verified := Proof.AesSiv.decrypt_keyed (decryptS_framed v f fc)
        spSafe := X86_64.withStackArgScratch_spSafe (decrypt_spSafe (.inr (.inr rfl)) v) }
        (decryptOut _)
    | _, _ => withScrubAll r (decryptOut _)

end

end VG.Proof.AesSiv.X86_64
