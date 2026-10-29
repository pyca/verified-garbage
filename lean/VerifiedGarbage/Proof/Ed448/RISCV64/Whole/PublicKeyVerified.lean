module

import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.PublicKey
import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Lit
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Ed448.WholeLocal
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.PublicKey
meta import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Ed448.WholeLocal
meta import VerifiedGarbage.Impl.StackScratch.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Ed448.RISCV64.Whole
public import VerifiedGarbage.Proof.Ed448.Ref
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# `vg_ed448_public_key` on RISC-V, verified

The code meets `publicKeyContract` with the frame (20 doublewords, so
aligned as the contract's `u64` buffers are) as one more argument
(`Sig.scratchContract`), and 1168 bytes of stack for the callees' frames:
the proof against the contract's facts by register (`pkC`), which it
implies, and a state satisfying it; and, in a frame of 160 bytes whose first
120 it zeroes before returning (`Verified.stackScratchWiped`), the contract
itself. Only the pointers are public: they stay in `s7`–`s10`, which no
function called writes, so the taint analysis (`taint_decide`) sees them
public throughout, callees included.
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64.Whole

open VG VG.RISCV64 VG.Impl.Ed448.RISCV64.Whole
open VG.Spec.Ed448 (bytesAt)

/-- The contract by register: `out` in `a0`, `seed` in `a1`, `scratch` in `a2`, the frame in `a3`. -/
def pkC : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 57⟩
    let seed : Region := ⟨s.gpr .a1, 57⟩
    let sc : Region := ⟨s.gpr .a2, 8192⟩
    let fr : Region := ⟨s.gpr .a3, 160⟩
    s.rd = [seed] ∧ s.wr = [out, sc, fr] ∧ out.Disjoint seed ∧ out.Disjoint sc ∧ out.Disjoint fr ∧
      seed.Disjoint sc ∧ seed.Disjoint fr ∧ sc.Disjoint fr ∧ (s.gpr .a2).toNat % 8 = 0 ∧
      (s.gpr .a3).toNat % 8 = 0 ∧ s.sp.toNat % 16 = 0 ∧ 1168 ≤ s.sp.toNat ∧
      (below s.sp 1168).Disjoint out ∧ (below s.sp 1168).Disjoint seed ∧ (below s.sp 1168).Disjoint sc ∧
      (below s.sp 1168).Disjoint fr
  post s s' := bytesAt s'.mem (s.gpr .a0) 57 = Spec.Ed448.publicKey (bytesAt s.mem (s.gpr .a1) 57)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

theorem pk_ok (hl : Proof.Ed448.BaseLadder2Ok) (s : State) (hs : pkC.pre s) :
    ∃ t s', Exec isa publicKey s t s' ∧ abiPreserved s s' ∧ pkC.post s s' := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩ := hs
  obtain ⟨t, s', he, hg, hsp, hra, hq⟩ := publicKey_wp hl ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hq⟩

theorem pk_ct : ConstantTime isa pkC.pre pkC.pub publicKey :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun s₁ s₂ _ _ ⟨p0, p1, p2, p3, psp⟩ => ⟨psp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption⟩) (by taint_decide)

/-- A state satisfying the precondition. -/
def pkSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x4000 | .a3 => 0x8000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 57⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x4000, 8192⟩, ⟨0x8000, 160⟩]

theorem publicKey_verified (hl : Proof.Ed448.BaseLadder2Ok) :
    Verified RISCV64.target publicKey (Sig.scratchContract RISCV64.abi Spec.Ed448.publicKeySig "frame" .u64 20
      (Curry.const (fun _ => True) _) (Proof.Ed448.WholeLocal.publicKeyPost RISCV64.abi.ptrBits) true 1168) :=
  Verified.of_correct (pk_ok hl) pk_ct (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Ed448.publicKeySig,
      Spec.Ed448.scratchWords, Proof.Ed448.WholeLocal.publicKeyPost, pkC, RISCV64.abi, RISCV64.argRegs]
      [pkSat] using pkSat)

/-- A state satisfying `vg_ed448_public_key`'s precondition, without the frame. -/
def pkFrameSat : State := { pkSat with wr := [⟨0x1000, 57⟩, ⟨0x4000, 8192⟩] }

theorem pkFrameSat_pre : ∃ s, (Spec.Ed448.publicKeyContract RISCV64.abi (1168 + 160)).pre s := by
  implies_sat [Spec.Ed448.publicKeyContract, Spec.Ed448.publicKeySig, Spec.Ed448.scratchWords, RISCV64.abi,
    RISCV64.argRegs] [pkFrameSat, pkSat] using pkFrameSat

/-- In its frame of 160 bytes, whose first 120 it zeroes before returning. -/
theorem publicKey_framed (hl : Proof.Ed448.BaseLadder2Ok) :
    Verified RISCV64.target publicKeyCode (Spec.Ed448.publicKeyContract RISCV64.abi (1168 + 160)) :=
  Verified.stackScratchWiped (sig := Spec.Ed448.publicKeySig) (nm := "frame") (e := .u64) (n := 20)
    (post := Proof.Ed448.WholeLocal.publicKeyPost RISCV64.abi.ptrBits) (wa := true) (stack := 1168) (bytes := 160)
    (words := 15) (publicKey_verified hl) (by decide) (by decide) (by decide)
    (Proof.Ed448.WholeLocal.publicKeyPostOut_local _) pkFrameSat_pre

end VG.Proof.Ed448.RISCV64.Whole
