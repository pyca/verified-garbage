module

import VerifiedGarbage.Proof.Sha512.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Sha512.PPC64LE.Lit

import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.PublicKey
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Sha512OK
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Ed25519.WholeLocal
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.PublicKey
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Ed25519.WholeLocal
meta import VerifiedGarbage.Impl.StackScratch.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Whole
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Common
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector

/-!
# `vg_ed25519_public_key` on PPC64LE, with its frame as an argument, verified

The code meets `publicKeyContract` with the frame as one more argument
(`Sig.scratchContract`), and 48 bytes of stack for the callees' frames: the
proof against the contract's facts by register (`pkC`), which it implies, and
a state satisfying it. Only the pointers are public: the pointers stay in
`r20`–`r23`, which no function called writes, so the taint analysis
(`taint_decide`) sees them public throughout, callees included.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE.Whole
open VG.Spec.Ed25519 (bytesAt)

/-- The contract by register: `out` in `r3`, `seed` in `r4`, `scratch` in `r5`, the frame in `r6`. -/
def pkC : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 32⟩
    let seed : Region := ⟨s.gpr .r4, 32⟩
    let sc : Region := ⟨s.gpr .r5, 8192⟩
    let fr : Region := ⟨s.gpr .r6, 144⟩
    s.rd = [seed] ∧ s.wr = [out, sc, fr] ∧ out.Disjoint seed ∧ out.Disjoint sc ∧ out.Disjoint fr ∧
      seed.Disjoint sc ∧ seed.Disjoint fr ∧ sc.Disjoint fr ∧ 48 ≤ s.sp.toNat ∧
      (below s.sp 48).Disjoint out ∧ (below s.sp 48).Disjoint seed ∧ (below s.sp 48).Disjoint sc ∧
      (below s.sp 48).Disjoint fr
  post s s' := bytesAt s'.mem (s.gpr .r3) 32 = Spec.Ed25519.publicKey (bytesAt s.mem (s.gpr .r4) 32)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

theorem pk_ok (s : State) (hs : pkC.pre s) :
    ∃ t s', Exec isa publicKey s t s' ∧ abiPreserved s s' ∧ pkC.post s s' := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩ := hs
  obtain ⟨t, s', he, hg, hsp, hlr, hq⟩ := publicKey_wp sha512OK ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩
  exact ⟨t, s', he, ⟨hg, hsp, hlr⟩, hq⟩

theorem pk_ct : ConstantTime isa pkC.pre pkC.pub publicKey :=
  VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
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
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩, ⟨0x8000, 144⟩]

theorem publicKey_verified :
    Verified PPC64LE.target publicKey (Sig.scratchContract PPC64LE.abi Spec.Ed25519.publicKeySig "frame" .u8 144
      (Curry.const (fun _ => True) _) (Proof.Ed25519.WholeLocal.publicKeyPost PPC64LE.abi.ptrBits) true 48) :=
  Verified.of_correct pk_ok pk_ct (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Ed25519.publicKeySig,
      Spec.Ed25519.scratchWords, Proof.Ed25519.WholeLocal.publicKeyPost, pkC, PPC64LE.abi, PPC64LE.argRegs] [pkSat] using pkSat)

/-- A state satisfying `vg_ed25519_public_key`'s precondition, without the frame. -/
def pkFrameSat : State := { pkSat with wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩] }

theorem pkFrameSat_pre : ∃ s, (Spec.Ed25519.publicKeyContract PPC64LE.abi (48 + 176)).pre s := by
  implies_sat [Spec.Ed25519.publicKeyContract, Spec.Ed25519.publicKeySig, Spec.Ed25519.scratchWords, PPC64LE.abi,
    PPC64LE.argRegs] [pkFrameSat, pkSat] using pkFrameSat

/-- In its frame of 176 bytes, whose first 136 it zeroes before returning. -/
theorem publicKey_framed :
    Verified PPC64LE.target publicKeyCode (Spec.Ed25519.publicKeyContract PPC64LE.abi (48 + 176)) :=
  Verified.stackScratchWiped (sig := Spec.Ed25519.publicKeySig) (nm := "frame") (e := .u8) (n := 144)
    (post := Proof.Ed25519.WholeLocal.publicKeyPost PPC64LE.abi.ptrBits) (wa := true) (stack := 48) (bytes := 176)
    (words := 17) publicKey_verified (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Ed25519.WholeLocal.publicKeyPost_local _)
    (Proof.Ed25519.WholeLocal.publicKeyPostOut_local _) pkFrameSat_pre

end VG.Proof.Ed25519.PPC64LE.Whole
