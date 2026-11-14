module

public import VerifiedGarbage.Proof.AesCcm.Rounds
public import VerifiedGarbage.Proof.AesCcm.X86_64.Verified
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration

/-!
# AES-CCM on x86-64, with its working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (`Verified.lean`), in a frame that allocates it
(`Verified.stackArgScratch`): their working space is passed on the stack
after the six argument registers and four other stack arguments (`data`,
`len`, `tag` and `tag_len`), so the frame of 2608 bytes holds the 2560 bytes
of working space, a copy of those four arguments, the word that stands for
the return address and the address of the working space. The code's own
calls use 16 bytes below it: the return addresses of the call of
`vg_cmac_aes_update` (or of `vg_aes_ctr32`) and of its call of
`vg_aes_ctr32`, if it makes one (`UpdateImpl.xdepth`), which uses no stack
(`Ctr32Impl.noStack`). `open`'s leak,
whether it succeeds, reads only its buffers (`openLeak_local`).

Over an implementation of AES that needs working space (`Ctr32Impl.free` is
`none`), that frame is the working space of the functions called, wiped
whole on return (`X86_64.Scrub.withScrubAll`, `sealReg`, `openReg`): their
postconditions read the memory on return only within the data and the tag
(`sealOut`, `openOut`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.Impl.AesCcm.X86_64
open VG.Proof.CmacAes.X86_64 (UpdateImpl)

variable (v : UpdateImpl)

theorem seal_xdepth : («seal» v.callee v.ctr.callee).x86_64Depth ≤ 16 := by
  have := v.xdepth
  simp only [«seal», sealFront, tagOut, mac, b0, aad, aadHead, absorbPad, updBlock, tag, ctr, ctrChunk, callUpdate,
    callCtr, Code.x86_64Depth, v.ctr.noStack]
  generalize v.callee.code.x86_64Depth = d at this ⊢
  revert d
  decide +kernel

theorem open_xdepth : («open» v.callee v.ctr.callee).x86_64Depth ≤ 16 := by
  have := v.xdepth
  simp only [«open», openFront, mac, b0, aad, aadHead, absorbPad, updBlock, tag, ctr, ctrChunk, callUpdate, callCtr,
    Code.x86_64Depth, v.ctr.noStack]
  generalize v.callee.code.x86_64Depth = d at this ⊢
  revert d
  decide +kernel

/-- A state satisfying `vg_aes_ccm_seal`'s precondition, without the working
space. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩, ⟨0x8008, 32⟩], wr := [⟨0, 0⟩, ⟨0x3000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Proof.AesCcm.sealRoundsContract X86_64.abi 2624).pre s := by
  implies_sat [Proof.AesCcm.sealRoundsContract, Spec.Ccm.sealSig, Spec.Ccm.sealPre, Proof.AesCcm.sealRoundsPost,
    X86_64.abi, X86_64.argRegs] [sealFrameSat, sealSat] using sealFrameSat

theorem seal_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 («seal» v.callee v.ctr.callee))
      (Proof.AesCcm.sealRoundsContract X86_64.abi 2624) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Ccm.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ccm.sealPre X86_64.abi.ptrBits)
    (post := Proof.AesCcm.sealRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 2608) (seal_verified v) (by decide) (by decide) (by decide)
    (seal_spSafe v) (seal_xdepth v) (sealPre_local _) (sealPost_local _) sealFrameSat_pre

/-- A state satisfying `vg_aes_ccm_open`'s precondition, without the working
space. -/
def openFrameSat : State :=
  { openSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩, ⟨0x3000, 4⟩, ⟨0x8008, 32⟩], wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Proof.AesCcm.openRoundsContract X86_64.abi 2624).pre s := by
  implies_sat [Proof.AesCcm.openRoundsContract, Spec.Ccm.openSig, Spec.Ccm.openPre, Proof.AesCcm.openRoundsPost,
    Spec.Ccm.openLeak, X86_64.abi, X86_64.argRegs] [openFrameSat, openSat, sealSat] using openFrameSat

theorem open_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 («open» v.callee v.ctr.callee))
      (Proof.AesCcm.openRoundsContract X86_64.abi 2624) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Ccm.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ccm.openPre X86_64.abi.ptrBits)
    (post := Proof.AesCcm.openRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 16)
    (leak := some (Spec.Ccm.openLeak X86_64.abi.ptrBits)) (bytes := 2608) (open_verified v)
    (by decide) (by decide) (by decide) (open_spSafe v) (open_xdepth v) (openPre_local _)
    (openPost_local _) openFrameSat_pre (hleak := openLeak_local _)

/-! ## Without secret residue -/

section
open VG.X86_64.Scrub

omit v

/-- The bytes of a buffer on which two memories agree. -/
theorem bytesAt_of {m₁ m₂ : Mem} {p : Addr} {L : Nat} (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a)
    {n : Nat} (hn : n ≤ L) : Spec.Aes.bytesAt m₂ p n = Spec.Aes.bytesAt m₁ p n := by
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi => (h _ (Region.contains_ofNat p (by have := List.mem_range.mp hi; omega))).symm

theorem sealOut (stack : Nat) :
    PostOut (Spec.Ccm.sealContract X86_64.abi stack) (Spec.Ccm.sealSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, np, nl, ap, al, dp, dl, tp, tl], _ =>
      simp only [Spec.Ccm.sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ccm.sealPost 64) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ccm.sealPost 64) _ m m₂ r
      dsimp only [Curry.apply, Spec.Ccm.sealPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      rw [h key hk, bytesAt_of hb.2.2.2.1 (by simp), bytesAt_of hb.2.2.2.2 (by simp)]

theorem openOut (stack : Nat) :
    PostOut (Spec.Ccm.openContract X86_64.abi stack) (Spec.Ccm.openSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, np, nl, ap, al, dp, dl, tp, tl], _ =>
      simp only [Spec.Ccm.openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ccm.openPost 64) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ccm.openPost 64) _ m m₂ r
      dsimp only [Curry.apply, Spec.Ccm.openPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      rw [bytesAt_of hb.2.2.2.1 (by simp)]
      exact h key hk

/-- `vg_aes_ccm_seal` over `v`. Over an implementation of AES that needs
working space (`v.ctr.free` is `none`), its frame of 2.6 KB is mostly that
working space, wiped whole on return (`withScrubAll`); over the others, as
before. -/
def sealReg (v : UpdateImpl) : Registration Spec.Ccm.sealApi X86_64.target :=
  let r : Registration Spec.Ccm.sealApi X86_64.target := {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2608 4 («seal» v.callee v.ctr.callee)
    stack := 2624
    verified := Proof.AesCcm.seal_keyed (seal_framed v)
    spSafe := X86_64.withStackArgScratch_spSafe (seal_spSafe v) }
  match v.ctr.free with
  | some _ => r
  | none => withScrubAll r (sealOut _)

/-- `vg_aes_ccm_open` over `v`, as `sealReg`. -/
def openReg (v : UpdateImpl) : Registration Spec.Ccm.openApi X86_64.target :=
  let r : Registration Spec.Ccm.openApi X86_64.target := {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2608 4 («open» v.callee v.ctr.callee)
    stack := 2624
    verified := Proof.AesCcm.open_keyed (open_framed v)
    spSafe := X86_64.withStackArgScratch_spSafe (open_spSafe v) }
  match v.ctr.free with
  | some _ => r
  | none => withScrubAll r (openOut _)

end

end VG.Proof.AesCcm.X86_64
