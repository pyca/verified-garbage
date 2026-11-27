module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Front
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP384r1.Config
import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Lit
public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP384r1.AArch64
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Front
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP384r1.Config
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Lit
meta import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP384r1.AArch64
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP384r1
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ecdsa.BrainpoolP384r1
meta import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
meta import VerifiedGarbage.Proof.Framework.GetElem

/-! ### `Ecdsa.Verify.AArch64.BrainpoolP384r1.Contract`, which this module and modules that import it used -/

section

/-!
# ECDSA verification over brainpoolP384r1 on AArch64: the contract the proof is written against

The facts of `Proof.Ecdsa.verifyContract Spec.Ecdsa.BrainpoolP384r1.inst` for AArch64, by name:
`vg_ecdsa_brainpoolp384r1_verify(public = x0, digest = x1, sig = x2, scratch = x3)`,
the result in `w0`. Only the pointers are public here: the proof shows that
nothing else affects timing, although the contract would let the contents of
the three buffers.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1

open VG VG.AArch64 Spec.Weierstrass Spec.Ecdsa

/-- Whether the signature at `sig` of the hash at `digest` is valid for the
public key at `pk`, as the specification says. -/
abbrev vf (m : Mem) (pk digest sig : Addr) : Bool :=
  verify Spec.BrainpoolP384r1.curve (bytesAt m pk 97) (hashToInt Spec.BrainpoolP384r1.curve (bytesAt m digest 48)) (bytesAt m sig 96)

def verifyAArch64 : Contract AArch64.isa where
  pre s :=
    let pk : Region := ⟨s.gpr .x0, 97⟩
    let digest : Region := ⟨s.gpr .x1, 48⟩
    let sig : Region := ⟨s.gpr .x2, 96⟩
    let scratch : Region := ⟨s.gpr .x3, 8192⟩
    s.rd = [pk, digest, sig] ∧ s.wr = [scratch] ∧ pk.Disjoint scratch ∧ digest.Disjoint scratch ∧
      sig.Disjoint scratch ∧ (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64
  post s s' := (s'.gpr .x0).setWidth 32 = if vf s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) then 1 else 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x8000 | _ => 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x1000, 97⟩, ⟨0x2000, 48⟩, ⟨0x3000, 96⟩]
  wr := [⟨0x8000, 8192⟩]

theorem implies : verifyAArch64.Implies (Proof.Ecdsa.verifyContract Spec.Ecdsa.BrainpoolP384r1.inst AArch64.abi) := by
  sig_implies [Spec.Ecdsa.BrainpoolP384r1.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig,
    Spec.BrainpoolP384r1.curve, Spec.Ecdsa.scratchWords, AArch64.abi, AArch64.argRegs, verifyAArch64, vf]
    [satState] using satState

end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1

end

end

/-!
# ECDSA verification over brainpoolP384r1 on AArch64: `Verified`

brainpoolp384r1 is a curve the proof supports (`brainpoolp384r1_ok`, and `Law` for its group law,
which the registration file supplies: `Proof.BrainpoolP384r1.law`), so `verify_ok` gives
the contract's postcondition; `x19` and `x20` are restored, and no instruction
writes the other callee-saved registers, `sp` or a SIMD register
(`abiPreserved_of`). Constant time by taint tracking: the only branches are on
loop counters, and every address is an argument plus a constant or a counter,
so only the pointers affect timing (the contract would let the key, the hash
and the signature affect it too).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.BrainpoolP384r1

theorem pre_of {s : State} (h : verifyAArch64.pre s) : FrontPre brainpoolp384r1 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨⟨[], h1⟩, h2, h3, h4, h5, h6⟩

end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1
