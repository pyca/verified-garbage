import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.CT
import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchWipe
import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract

/-!
# ChaCha20-Poly1305 on x86-64: `Verified`

Correctness and constant time (both from `CT.lean`), and a state satisfying
the precondition, for any implementation `v` of `vg_chacha20_xor`: of the
code with its working space as its last argument
(`sealScratchContract`, `openScratchContract`), and then of the functions,
which allocate it in a frame on the stack and wipe it after the code
(`Verified.stackArgScratchWipedX`): `work` is passed on the stack after `tag`,
so the frame holds a copy of `tag` and the address of `work`, and the 1696
bytes of `work`, 1720 bytes in all. The wrapper zeroes the first 672 bytes of
`work`; the code itself zeroes the keystream it keeps after them. The code's
calls use 24 bytes below the frame.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64

/-- A state satisfying `seal`'s precondition (with no additional data and no
data, `tag` at `0x3000` and `work` at 0). -/
def sealSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x1100 | .rdx => 0x2000 | .r8 => 0x2100 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := bif Nat.beq a.toNat 0x8009 then 0x30 else 0
  rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x8008, 16⟩]
  wr := [⟨0x2100, 0⟩, ⟨0x3000, 16⟩, ⟨0, 1696⟩]

/-- A state satisfying `open`'s precondition (as `sealSat`, with `tag` read). -/
def openSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x1100 | .rdx => 0x2000 | .r8 => 0x2100 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := bif Nat.beq a.toNat 0x8009 then 0x30 else 0
  rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x3000, 16⟩, ⟨0x8008, 16⟩]
  wr := [⟨0x2100, 0⟩, ⟨0, 1696⟩]

/-- `seal` and `open` never write the stack pointer. -/
theorem seal_spSafe (v : Proof.ChaCha20.X86_64.XorImpl) :
    («seal» v.callee v.poly).all (fun i => !X86_64.isa.writesSp i) = true := by
  rcases v.fold_poly with ⟨hf, hb⟩ | ⟨hf, hb⟩ | ⟨hf, hb⟩ <;>
    (simp only [«seal», prologue, crypt, Code.all, v.spSafe, hf, hb]; lit_decide)

theorem open_spSafe (v : Proof.ChaCha20.X86_64.XorImpl) :
    («open» v.callee v.poly).all (fun i => !X86_64.isa.writesSp i) = true := by
  rcases v.fold_poly with ⟨hf, hb⟩ | ⟨hf, hb⟩ | ⟨hf, hb⟩ <;>
    (simp only [«open», prologue, crypt, Code.all, v.spSafe, hf, hb]; lit_decide)

theorem seal_ok (v : Proof.ChaCha20.X86_64.XorImpl) (s : State) (hs : sealX86_64.pre s) :
    ∃ t s', Exec isa («seal» v.callee v.poly) s t s' ∧ abiPreserved s s' ∧ sealX86_64.post s s' :=
  seal_correct v (APre.of s hs)

theorem seal_ct (v : Proof.ChaCha20.X86_64.XorImpl) :
    ConstantTime isa sealX86_64.pre sealX86_64.pub («seal» v.callee v.poly) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (seal_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem open_ok (v : Proof.ChaCha20.X86_64.XorImpl) (s : State) (hs : openX86_64.pre s) :
    ∃ t s', Exec isa («open» v.callee v.poly) s t s' ∧ abiPreserved s s' ∧ openX86_64.post s s' :=
  open_correct v (APre.of s hs)

theorem open_ct (v : Proof.ChaCha20.X86_64.XorImpl) :
    ConstantTime isa openX86_64.pre openX86_64.pub («open» v.callee v.poly) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (open_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem seal_verified (v : Proof.ChaCha20.X86_64.XorImpl) :
    Verified X86_64.target («seal» v.callee v.poly) (sealScratchContract X86_64.abi 212 24) :=
  Verified.of_correct (seal_ok v) (seal_ct v) (by
    sig_implies [Proof.ChaCha20Poly1305.sealScratchContract, Proof.ChaCha20Poly1305.sealScratchSig,
      Spec.ChaCha20Poly1305.sealPost, Proof.ChaCha20Poly1305.sealX86_64,
      Proof.ChaCha20Poly1305.preX86_64, Proof.ChaCha20Poly1305.pubX86_64, X86_64.abi, X86_64.stackArg,
      X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
      [sealSat] using sealSat)

/-- The postconditions match on `decrypt` through different auxiliary
functions, so the implication splits on it. -/
theorem open_verified (v : Proof.ChaCha20.X86_64.XorImpl) :
    Verified X86_64.target («open» v.callee v.poly) (openScratchContract X86_64.abi 212 24) :=
  Verified.of_correct (open_ok v) (open_ct v)
    { pre := by
        sig_implies_pre [Proof.ChaCha20Poly1305.openScratchContract,
          Proof.ChaCha20Poly1305.openScratchSig, Spec.ChaCha20Poly1305.openPost,
          Proof.ChaCha20Poly1305.openX86_64, Proof.ChaCha20Poly1305.preX86_64,
          Proof.ChaCha20Poly1305.pubX86_64, X86_64.abi, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
          List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_eval [Proof.ChaCha20Poly1305.openScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openPost, X86_64.abi, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
          List.range, List.range.loop, X86_64.argRegs]
        simp only [Proof.ChaCha20Poly1305.openX86_64] at h
        -- The two `decrypt` terms are equal only up to unfolding numerals.
        split at h
        next _ pt e₁ =>
          split
          next _ pt' e₂ =>
            obtain rfl := Option.some.inj (e₁.symm.trans e₂)
            exact h
          next _ e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
        next _ e₁ =>
          split
          next _ pt' e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
          next _ e₂ => exact h
      pub := by
        sig_implies_pub [Proof.ChaCha20Poly1305.openScratchContract,
          Proof.ChaCha20Poly1305.openScratchSig, Spec.ChaCha20Poly1305.openPost,
          Proof.ChaCha20Poly1305.openX86_64, Proof.ChaCha20Poly1305.preX86_64,
          Proof.ChaCha20Poly1305.pubX86_64, X86_64.abi, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
          List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
      sat := by
        sig_implies_sat [Proof.ChaCha20Poly1305.openScratchContract,
          Proof.ChaCha20Poly1305.openScratchSig, Spec.ChaCha20Poly1305.openPost,
          Proof.ChaCha20Poly1305.openX86_64, Proof.ChaCha20Poly1305.preX86_64,
          Proof.ChaCha20Poly1305.pubX86_64, X86_64.abi, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
          List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
          [openSat] using openSat }

/-! ## The frame -/

theorem xorBuf_xdepth : (xorBufX .r14).x86_64Depth = 0 := by decide
theorem init_xdepth : Impl.Poly1305.X86_64.init.x86_64Depth = 0 := by lit_decide
theorem finalize_xdepth : Impl.Poly1305.X86_64.finalize.x86_64Depth = 0 := by lit_decide

theorem blocks_xdepth (b : Impl.Poly1305.X86_64.Blocks) : b.code.x86_64Depth ≤ 16 := by
  cases b <;> lit_decide

theorem seal_xdepth (v : Proof.ChaCha20.X86_64.XorImpl) : («seal» v.callee v.poly).x86_64Depth ≤ 24 := by
  have hx := v.xdepth
  have hb := blocks_xdepth v.poly
  simp only [«seal», prologue, prologueA, prologueB, foldM, zeroKs, macPad, macPadLengths, wholeBlocks, padTail, crypt, absorbLengths, finalizeTag, finalizeWith,
    Code.x86_64Depth, xorBuf_xdepth, init_xdepth, finalize_xdepth, Nat.max_le]
  omega

theorem open_xdepth (v : Proof.ChaCha20.X86_64.XorImpl) : («open» v.callee v.poly).x86_64Depth ≤ 24 := by
  have hx := v.xdepth
  have hb := blocks_xdepth v.poly
  simp only [«open», prologue, prologueA, prologueB, foldM, zeroKs, macPad, macPadLengths, wholeBlocks, padTail, crypt, absorbLengths, finalizeTo, finalizeWith,
    Code.x86_64Depth, xorBuf_xdepth, init_xdepth, finalize_xdepth, Nat.max_le]
  omega

/-- A state satisfying `seal`'s precondition, without the working space. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x8008, 8⟩],
                 wr := [⟨0x2100, 0⟩, ⟨0x3000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.sealContract X86_64.abi 1744).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig,
    Spec.ChaCha20Poly1305.sealPost, X86_64.abi, X86_64.argRegs] [sealFrameSat, sealSat] using sealFrameSat

theorem seal_framed (v : Proof.ChaCha20.X86_64.XorImpl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratchWipedX 1720 1 42 («seal» v.callee v.poly))
      (Spec.ChaCha20Poly1305.sealContract X86_64.abi 1744) :=
  X86_64.Verified.stackArgScratchWipedX (sig := Spec.ChaCha20Poly1305.sealSig) (nm := "work") (e := .u64)
    (n := 212) (post := Spec.ChaCha20Poly1305.sealPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 1720) (k := 42) (seal_verified v) (by decide) (by decide) (by decide)
    (seal_spSafe v) (seal_xdepth v) (by decide) (pre_local _ _) (sealPost_local _) (sealPost_out _)
    sealFrameSat_pre

/-- A state satisfying `open`'s precondition, without the working space. -/
def openFrameSat : State :=
  { openSat with rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x3000, 16⟩, ⟨0x8008, 8⟩],
                 wr := [⟨0x2100, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.openContract X86_64.abi 1744).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig,
    Spec.ChaCha20Poly1305.openPost, X86_64.abi, X86_64.argRegs] [openFrameSat, openSat] using openFrameSat

theorem open_framed (v : Proof.ChaCha20.X86_64.XorImpl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratchWipedX 1720 1 42 («open» v.callee v.poly))
      (Spec.ChaCha20Poly1305.openContract X86_64.abi 1744) :=
  X86_64.Verified.stackArgScratchWipedX (sig := Spec.ChaCha20Poly1305.openSig) (nm := "work") (e := .u64)
    (n := 212) (post := Spec.ChaCha20Poly1305.openPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 1720) (k := 42) (open_verified v) (by decide) (by decide) (by decide)
    (open_spSafe v) (open_xdepth v) (by decide) (pre_local _ _) (openPost_local _) (openPost_out _)
    openFrameSat_pre

end VG.Proof.ChaCha20Poly1305.X86_64
