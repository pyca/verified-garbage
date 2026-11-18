module

public import VerifiedGarbage.Proof.AesOcb.Scratch
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Seal
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.AesOcb.RISCV64
import VerifiedGarbage.Proof.AesOcb.RISCV64.Open
import VerifiedGarbage.Proof.AesOcb.RISCV64.FnCT
import VerifiedGarbage.Proof.Framework.SigEval
public import VerifiedGarbage.Impl.StackScratch.RISCV64.Args
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratchArgs
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Init
import VerifiedGarbage.Proof.Aes.ScrubLocal
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubPre

/-!
# AES-OCB on RISC-V: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time,
a state satisfying each precondition, and the shared contracts of
`Spec/Ocb/Contract.lean` with the working space as a last argument
(`Proof/AesOcb/Scratch.lean`; with no stack: a call keeps the return address
in `ra`, which each function saves in the working space).
The working space is then allocated on the stack (`seal_framed`,
`open_framed`); `init` is AES-GCM's (`Init.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.Impl.AesOcb.RISCV64

theorem seal_correct (s : State) (hs : sealRISCV64.pre s) :
    ∃ t s', Exec isa «seal» s t s' ∧ abiPreserved s s' ∧ sealRISCV64.post s s' :=
  seal_wp hs

theorem open_correct (s : State) (hs : openRISCV64.pre s) :
    ∃ t s', Exec isa «open» s t s' ∧ abiPreserved s s' ∧ openRISCV64.post s s' :=
  open_wp hs

/-! ## States satisfying the preconditions -/

/-- A state satisfying the precondition of `vg_aes_ocb_seal`: a 1-byte nonce,
no associated data, no data, a 4-byte tag at `0x5000` and `work` at
`0x6000`, with the stack arguments at `0x9000`. -/
def sealSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x2000 | .a3 => 1 | .a4 => 0x3000 | .a6 => 0x4000 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9001 then 0x50 else bif Nat.beq a.toNat 0x9008 then 4 else
    bif Nat.beq a.toNat 0x9011 then 0x60 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x9000, 24⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 4⟩, ⟨0x6000, 2560⟩]

/-- A state satisfying the precondition of `vg_aes_ocb_open`: as `sealSat`,
with the tag read only. -/
def openSat : State := { sealSat with
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x5000, 4⟩, ⟨0x9000, 24⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x6000, 2560⟩] }

/-! ## The shared contracts -/

theorem seal_verified :
    Verified RISCV64.target «seal» (Proof.AesOcb.sealScratchContract RISCV64.abi) :=
  Verified.of_correct seal_correct seal_ct
    { pre := by sig_implies_pre [Proof.AesOcb.sealScratchContract, Proof.AesOcb.sealScratchSig, Spec.Ocb.sealPre,
      Proof.AesOcb.sealRoundsPost, sealRISCV64, sealPreA, oneFacts, aCtx, aNonce, aAad, aData, aTag, aWork, onePub, args,
      rounds, RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range,
      List.range.loop, BitVec.add_zero]
      post := by sig_implies_post [Proof.AesOcb.sealScratchContract, Proof.AesOcb.sealScratchSig, Spec.Ocb.sealPre,
      Proof.AesOcb.sealRoundsPost, sealRISCV64, sealPreA, oneFacts, aCtx, aNonce, aAad, aData, aTag, aWork, onePub, args,
      rounds, RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range,
      List.range.loop]
      pub := by sig_implies_pub [Proof.AesOcb.sealScratchContract, Proof.AesOcb.sealScratchSig, Spec.Ocb.sealPre,
      Proof.AesOcb.sealRoundsPost, sealRISCV64, sealPreA, oneFacts, aCtx, aNonce, aAad, aData, aTag, aWork, onePub, args,
      rounds, RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range,
      List.range.loop]
      sat := by sig_implies_sat [Proof.AesOcb.sealScratchContract, Proof.AesOcb.sealScratchSig, Spec.Ocb.sealPre,
      Proof.AesOcb.sealRoundsPost, sealRISCV64, sealPreA, oneFacts, aCtx, aNonce, aAad, aData, aTag, aWork, onePub, args,
      rounds, RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range,
      List.range.loop] [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat }

/-- `open`'s public data include its leak, from which `pub` has whether it
succeeds. -/
theorem open_verified :
    Verified RISCV64.target «open» (Proof.AesOcb.openScratchContract RISCV64.abi) :=
  Verified.of_correct open_correct open_ct
    { pre := by sig_implies_pre [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openRISCV64, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
        aTag, aWork, onePub, openOut, args, rounds, RISCV64.abi, RISCV64.argRegs, stackArg,
        stackArgAddr, List.getD, List.range, List.range.loop, BitVec.add_zero]
      post := by sig_implies_post [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openRISCV64, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
        aTag, aWork, onePub, openOut, args, rounds, RISCV64.abi, RISCV64.argRegs, stackArg,
        stackArgAddr, List.getD, List.range, List.range.loop]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
          Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openRISCV64, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
          aTag, aWork, onePub, openOut, args, rounds, RISCV64.abi, RISCV64.argRegs, stackArg,
          stackArgAddr, List.getD, List.range, List.range.loop] at h
        sig_split h
        sig_reduce [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
          Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openRISCV64, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
          aTag, aWork, onePub, openOut, args, rounds, RISCV64.abi, RISCV64.argRegs, stackArg,
          stackArgAddr, List.getD, List.range, List.range.loop]
        sig_simp [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
          Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openRISCV64, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
          aTag, aWork, onePub, openOut, args, rounds, RISCV64.abi, RISCV64.argRegs, stackArg,
          stackArgAddr, List.getD, List.range, List.range.loop]
          [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := by sig_implies_sat [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openRISCV64, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
        aTag, aWork, onePub, openOut, args, rounds, RISCV64.abi, RISCV64.argRegs, stackArg,
        stackArgAddr, List.getD, List.range, List.range.loop] [openSat, sealSat, stackArg, stackArgAddr, Mem.readW,
        Mem.read] using openSat }

/-! ## With the working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (above), in a frame that allocates it
(`Verified.stackScratchArgs`): `tag` and `tag_len` arrive on the stack, so
the frame of 2592 bytes copies them, then the working space's address, above
its stack pointer. The copies are read only where the pre- and
postconditions read the buffers, and `open`'s leak, whether it succeeds,
reads only its buffers (`Proof/AesOcb/Scratch.lean`). As AES-GCM's `open`
(`Proof/AesGcm/RISCV64/Verified.lean`).
-/

/-- A state satisfying `vg_aes_ocb_seal`'s precondition, without the working
space: `tag` and `tag_len` alone on the stack. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x9000, 16⟩],
                 wr := [⟨0x4000, 0⟩, ⟨0x5000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Proof.AesOcb.sealRoundsContract RISCV64.abi 2592).pre s := by
  implies_sat [Proof.AesOcb.sealRoundsContract, Spec.Ocb.sealSig, Spec.Ocb.sealPre, Proof.AesOcb.sealRoundsPost, RISCV64.abi,
    RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealFrameSat

theorem seal_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchArgs 2592 2 «seal»)
      (Proof.AesOcb.sealRoundsContract RISCV64.abi 2592) :=
  RISCV64.Verified.stackScratchArgs (sig := Spec.Ocb.sealSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Ocb.sealPre RISCV64.abi.ptrBits) (post := Proof.AesOcb.sealRoundsPost RISCV64.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2592) (m := 2) seal_verified (by decide) (by decide)
    (Proof.AesOcb.sealPre_local _) (Proof.AesOcb.sealPost_local _) (Proof.AesOcb.sealPostOut_local _)
    sealFrameSat_pre

/-- A state satisfying `vg_aes_ocb_open`'s precondition, without the working
space: `tag` and `tag_len` alone on the stack. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x5000, 4⟩, ⟨0x9000, 16⟩],
                 wr := [⟨0x4000, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Proof.AesOcb.openRoundsContract RISCV64.abi 2592).pre s := by
  implies_sat [Proof.AesOcb.openRoundsContract, Spec.Ocb.openSig, Spec.Ocb.openPre, Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak,
    RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [openFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openFrameSat

theorem open_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchArgs 2592 2 «open»)
      (Proof.AesOcb.openRoundsContract RISCV64.abi 2592) :=
  RISCV64.Verified.stackScratchArgs (sig := Spec.Ocb.openSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Ocb.openPre RISCV64.abi.ptrBits) (post := Proof.AesOcb.openRoundsPost RISCV64.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2592) (m := 2) (leak := some (Spec.Ocb.openLeak RISCV64.abi.ptrBits))
    open_verified (by decide) (by decide) (Proof.AesOcb.openPre_local _) (Proof.AesOcb.openPost_local _)
    (Proof.AesOcb.openPostOut_local _) openFrameSat_pre (hleak := Proof.AesOcb.openLeak_local _)

end VG.Proof.AesOcb.RISCV64

/-! ## AES-OCB on RISC-V, without secret residue

`vg_aes_ocb_init`, `vg_aes_ocb_seal` and `vg_aes_ocb_open`, each followed by `Impl.Scrub.RISCV64.scrubTail`
(`RISCV64.Scrub.withScrub`), which clears the caller-saved registers and the
stack its frames used, the working space of its callees with it. Their
postconditions read the memory on return only within the key context, or the data and the tag
(`RISCV64.Scrub.PostOut`), as on x86-64 (`Proof/AesOcb/X86_64/Scrub.lean`).
-/

namespace VG.Proof.AesOcb.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub VG.Proof.Aes.ScrubLocal VG.Proof.AesOcb.RISCV64

/-! ## Postconditions -/

theorem ocbInitOut (stack : Nat) :
    PostOut (Spec.Ocb.initContract RISCV64.abi stack) (Spec.Ocb.initSig.retBits 64) :=
  postOut_of_local_pre fun vs m m₁ m₂ r hlen hpre hb h => by
    match vs, hlen with
    | [k, ln, ctx], _ =>
      simp only [Spec.Ocb.initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      change Spec.Ocb.KeyRepr m₁ ctx _ at h
      change Spec.Ocb.KeyRepr m₂ ctx _
      change _ ∨ _ at hpre
      obtain ⟨h1, h2⟩ := h
      refine ⟨?_, ?_⟩
      · rw [Proof.Aes.ScrubLocal.bytesAt_of0 hb.2 ?_]
        · exact h1
        · simp only [Spec.Aes.bytesAt, List.length_map, List.length_range, Spec.Aes.rounds, Elem.size]
          rcases hpre with h | h | h <;> rw [h] <;> decide
      · simp only [Spec.Ocb.ctxLstar, Spec.Ocb.blockAtMem] at h2 ⊢
        rw [show (240 : BitVec 64) = BitVec.ofNat 64 240 from rfl] at h2 ⊢
        rw [Proof.Aes.ScrubLocal.bytesAt_of hb.2 (by decide)]
        exact h2

theorem sealOut (stack : Nat) :
    PostOut (Spec.Ocb.sealContract RISCV64.abi stack) (Spec.Ocb.sealSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [cp, rd, np, nl, ap, al, dp, dl, tp, tl], _ =>
      simp only [Spec.Ocb.sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ocb.sealPost 64) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ocb.sealPost 64) _ m m₂ r
      dsimp only [Curry.apply, Spec.Ocb.sealPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      rw [h key hk, Proof.Aes.ScrubLocal.bytesAt_of0 hb.2.2.2.1 (by simp),
        Proof.Aes.ScrubLocal.bytesAt_of0 hb.2.2.2.2 (by simp)]

theorem openOut (stack : Nat) :
    PostOut (Spec.Ocb.openContract RISCV64.abi stack) (Spec.Ocb.openSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [cp, rd, np, nl, ap, al, dp, dl, tp, tl], _ =>
      simp only [Spec.Ocb.openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ocb.openPost 64) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ocb.openPost 64) _ m m₂ r
      dsimp only [Curry.apply, Spec.Ocb.openPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      rw [Proof.Aes.ScrubLocal.bytesAt_of0 hb.2.2.2.1 (by simp)]
      exact h key hk

/-! ## The registrations -/

/-- `Spec.Ocb.initApi`. -/
def initReg : Registration Spec.Ocb.initApi RISCV64.target :=
  withScrub {
      code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a3 Impl.AesGcm.RISCV64.init
      verified := init_framed }
    (ocbInitOut _)

/-- `Spec.Ocb.sealApi`. -/
def sealReg : Registration Spec.Ocb.sealApi RISCV64.target :=
  withScrub {
      code := Impl.StackScratch.RISCV64.withStackScratchArgs 2592 2 Impl.AesOcb.RISCV64.«seal»
      verified := Proof.AesOcb.seal_keyed seal_framed }
    (sealOut _)

/-- `Spec.Ocb.openApi`. -/
def openReg : Registration Spec.Ocb.openApi RISCV64.target :=
  withScrub {
      code := Impl.StackScratch.RISCV64.withStackScratchArgs 2592 2 Impl.AesOcb.RISCV64.«open»
      verified := Proof.AesOcb.open_keyed open_framed }
    (openOut _)

end VG.Proof.AesOcb.RISCV64.Scrub
