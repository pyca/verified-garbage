module

import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.PublicKey
import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Lit
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Ed448.WholeLocal
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.PublicKey
meta import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Ed448.WholeLocal
meta import VerifiedGarbage.Impl.StackScratch.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Ed448.PPC64LE.Whole
public import VerifiedGarbage.Proof.Ed448.Ref
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# `vg_ed448_public_key` on PPC64LE, verified

The code meets `publicKeyContract` with the frame as one more argument
(`Sig.scratchContract`), and 48 bytes of stack for the callees' frames: the
proof against the contract's facts by register (`pkC`), which it implies, and
a state satisfying it; and, in a frame of 192 bytes whose first 120 it zeroes
before returning (`Verified.stackScratchWiped`), the contract itself. Only
the pointers are public: they stay in `r20`–`r23`, which no function called
writes, so the taint analysis (`taint_decide`) sees them public throughout,
callees included.
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE.Whole
open VG.Spec.Ed448 (bytesAt)

/-- The contract by register: `out` in `r3`, `seed` in `r4`, `scratch` in `r5`, the frame in `r6`. -/
def pkC : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 57⟩
    let seed : Region := ⟨s.gpr .r4, 57⟩
    let sc : Region := ⟨s.gpr .r5, 8192⟩
    let fr : Region := ⟨s.gpr .r6, 160⟩
    s.rd = [seed] ∧ s.wr = [out, sc, fr] ∧ out.Disjoint seed ∧ out.Disjoint sc ∧ out.Disjoint fr ∧
      seed.Disjoint sc ∧ seed.Disjoint fr ∧ sc.Disjoint fr ∧ 48 ≤ s.sp.toNat ∧
      (below s.sp 48).Disjoint out ∧ (below s.sp 48).Disjoint seed ∧ (below s.sp 48).Disjoint sc ∧
      (below s.sp 48).Disjoint fr
  post s s' := bytesAt s'.mem (s.gpr .r3) 57 = Spec.Ed448.publicKey (bytesAt s.mem (s.gpr .r4) 57)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

theorem pk_ok (hl : Proof.Ed448.BaseLadder2Ok) (s : State) (hs : pkC.pre s) :
    ∃ t s', Exec isa publicKey s t s' ∧ abiPreserved s s' ∧ pkC.post s s' := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩ := hs
  obtain ⟨t, s', he, hg, hsp, hlr, hq⟩ := publicKey_wp hl ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩
  exact ⟨t, s', he, ⟨hg, hsp, hlr⟩, hq⟩

theorem pk_ct : ConstantTime isa pkC.pre pkC.pub publicKey :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun s₁ s₂ _ _ ⟨p3, p4, p5, p6, psp⟩ => ⟨psp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption⟩) (by taint_decide)

/-- A state satisfying the precondition. -/
def pkSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x4000 | .r6 => 0x8000 | _ => 0
  lr := 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 57⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x4000, 8192⟩, ⟨0x8000, 160⟩]

theorem publicKey_verified (hl : Proof.Ed448.BaseLadder2Ok) :
    Verified PPC64LE.target publicKey (Sig.scratchContract PPC64LE.abi Spec.Ed448.publicKeySig "frame" .u8 160
      (Curry.const (fun _ => True) _) (Proof.Ed448.WholeLocal.publicKeyPost PPC64LE.abi.ptrBits) true 48) :=
  Verified.of_correct (pk_ok hl) pk_ct (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Ed448.publicKeySig,
      Spec.Ed448.scratchWords, Proof.Ed448.WholeLocal.publicKeyPost, pkC, PPC64LE.abi, PPC64LE.argRegs]
      [pkSat] using pkSat)

/-- A state satisfying `vg_ed448_public_key`'s precondition, without the frame. -/
def pkFrameSat : State := { pkSat with wr := [⟨0x1000, 57⟩, ⟨0x4000, 8192⟩] }

theorem pkFrameSat_pre : ∃ s, (Spec.Ed448.publicKeyContract PPC64LE.abi (48 + 192)).pre s := by
  implies_sat [Spec.Ed448.publicKeyContract, Spec.Ed448.publicKeySig, Spec.Ed448.scratchWords, PPC64LE.abi,
    PPC64LE.argRegs] [pkFrameSat, pkSat] using pkFrameSat

/-- In its frame of 192 bytes, whose first 120 it zeroes before returning. -/
theorem publicKey_framed (hl : Proof.Ed448.BaseLadder2Ok) :
    Verified PPC64LE.target publicKeyCode (Spec.Ed448.publicKeyContract PPC64LE.abi (48 + 192)) :=
  Verified.stackScratchWiped (sig := Spec.Ed448.publicKeySig) (nm := "frame") (e := .u8) (n := 160)
    (post := Proof.Ed448.WholeLocal.publicKeyPost PPC64LE.abi.ptrBits) (wa := true) (stack := 48) (bytes := 192)
    (words := 15) (publicKey_verified hl) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Ed448.WholeLocal.publicKeyPost_local _)
    (Proof.Ed448.WholeLocal.publicKeyPostOut_local _) pkFrameSat_pre

end VG.Proof.Ed448.PPC64LE.Whole
