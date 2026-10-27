module

import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.ByRegister
import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.SignCT
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Ed25519.WholeLocal
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Whole
import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.TCB.Artifact

/-!
# `vg_ed25519_sign_cached` on RISC-V, verified

The code meets `signCachedContract` with the frame (36 doublewords, so
aligned as the contract's `u64` buffers are) as one more argument
(`Sig.scratchContract`) and 208 bytes of stack for the callees' frames: the
proof against the contract's facts by register (`signC`), which it implies,
and a state satisfying it. In a frame of 288 bytes on the stack whose first
224 it zeroes before returning (`Verified.stackScratchWiped`), it meets the
contract itself.
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.Impl.Ed25519.RISCV64.Whole
open VG.Spec.Ed25519 (bytesAt)

/-- A state satisfying the precondition, with memory `m`. -/
def signSat (m : Mem) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x2100 | .a3 => 0x3000 | .a5 => 0x4000 | .a6 => 0x8000 | _ => 0
  sp := 0x10000
  mem := m
  rd := [⟨0x2000, 32⟩, ⟨0x2100, 32⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x4000, 8192⟩, ⟨0x8000, 288⟩]

theorem signCached_verified :
    Verified RISCV64.target signCached (Sig.scratchContract RISCV64.abi Spec.Ed25519.signCachedSig "frame" .u64 36
      (Proof.Ed25519.WholeLocal.signCachedPre RISCV64.abi.ptrBits)
      (Proof.Ed25519.WholeLocal.signCachedPost RISCV64.abi.ptrBits) true 208) :=
  Verified.of_correct sign_ok (signCached_ct fun _ _ _ _ ⟨h0, h1, h2, h3, h4, h5, h6, hsp⟩ => ⟨hsp, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption⟩)
    { pre := by
        sig_implies_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Ed25519.signCachedSig, Spec.Ed25519.scratchWords, Proof.Ed25519.WholeLocal.signCachedPre,
          Proof.Ed25519.WholeLocal.signCachedPost, signC, RISCV64.abi, RISCV64.argRegs]
      post := by
        sig_implies_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Ed25519.signCachedSig, Spec.Ed25519.scratchWords, Proof.Ed25519.WholeLocal.signCachedPre,
          Proof.Ed25519.WholeLocal.signCachedPost, signC, RISCV64.abi, RISCV64.argRegs]
      pub := by
        sig_implies_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Ed25519.signCachedSig, Spec.Ed25519.scratchWords, Proof.Ed25519.WholeLocal.signCachedPre,
          Proof.Ed25519.WholeLocal.signCachedPost, signC, RISCV64.abi, RISCV64.argRegs]
      sat := by
        obtain ⟨m, hm⟩ : ∃ m : Mem, bytesAt m 0x2100 32 = Spec.Ed25519.publicKey (bytesAt m 0x2000 32) :=
          ⟨_, Proof.Ed25519.WholeLocal.sat_pk⟩
        refine ⟨signSat m, ?_⟩
        sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Ed25519.signCachedSig, Spec.Ed25519.scratchWords, Proof.Ed25519.WholeLocal.signCachedPre,
          RISCV64.abi, RISCV64.argRegs, signSat]
        sig_and_intros
        all_goals first
          | exact hm
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide) }

/-- A state satisfying `vg_ed25519_sign_cached`'s precondition, without the frame. -/
def signFrameSat (m : Mem) : State := { signSat m with wr := [⟨0x1000, 64⟩, ⟨0x4000, 8192⟩] }

theorem signFrameSat_pre : ∃ s, (Spec.Ed25519.signCachedContract RISCV64.abi (208 + 288)).pre s := by
  obtain ⟨m, hm⟩ : ∃ m : Mem, bytesAt m 0x2100 32 = Spec.Ed25519.publicKey (bytesAt m 0x2000 32) :=
    ⟨_, Proof.Ed25519.WholeLocal.sat_pk⟩
  refine ⟨signFrameSat m, ?_⟩
  sig_pre [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig, Spec.Ed25519.scratchWords, RISCV64.abi,
    RISCV64.argRegs, signFrameSat, signSat]
  sig_and_intros
  all_goals first
    | exact hm
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

/-- In its frame of 288 bytes, whose first 224 it zeroes before returning. -/
theorem signCached_framed :
    Verified RISCV64.target signCachedCode (Spec.Ed25519.signCachedContract RISCV64.abi (208 + 288)) :=
  Verified.stackScratchWiped (sig := Spec.Ed25519.signCachedSig) (nm := "frame") (e := .u64) (n := 36)
    (pre := Proof.Ed25519.WholeLocal.signCachedPre RISCV64.abi.ptrBits)
    (post := Proof.Ed25519.WholeLocal.signCachedPost RISCV64.abi.ptrBits) (wa := true) (stack := 208) (bytes := 288)
    (words := 28) signCached_verified (by decide) (by decide) (by decide)
    (Proof.Ed25519.WholeLocal.signCachedPostOut_local _) signFrameSat_pre

end VG.Proof.Ed25519.RISCV64.Whole
