module

public import VerifiedGarbage.Spec.Sha3.Contract
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.TCB.Artifact

/-!
# SHA-3 on PPC64LE: the contracts

The contracts the proofs are written against; the artifacts are emitted with
the shared contracts of `Spec/Sha3/Contract.lean`, which imply these, with
the arguments where the ELFv2 ABI passes them. The streaming functions save
the link register in a frame of 48 bytes below the stack pointer.
-/

@[expose] public section

namespace VG.Proof.Sha3

open Spec.Sha3

open VG.PPC64LE in
/-- PPC64LE contract for `vg_keccak_f1600(state: *mut [u64; 25], scratch: *mut
[u64; 64])`: applies Keccak-f[1600] to the state at `state`.

The code may read and write `state` (200 bytes) and `scratch` (512 bytes,
whose contents on exit are unspecified), which may not overlap. The pointers
are public; the state is secret. -/
def permutePPC64LE : Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 200⟩
    let scratch : Region := ⟨s.gpr .r4, 512⟩
    s.rd = [] ∧ s.wr = [state, scratch] ∧ state.Disjoint scratch
  post s s' := stateAt s'.mem (s.gpr .r3) = keccakF (stateAt s.mem (s.gpr .r3))
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.sp = s₂.sp

open VG.PPC64LE in
/-- PPC64LE contract for `vg_keccak_absorb(state = r3, rate = r4, pos = r5,
data = r6, len = r7, scratch = r8) -> r3`: absorbs `data` into the streaming
state (`Repr`) and returns the new position in the block.

The code may read `data`, and read and write `state` (200 bytes) and
`scratch` (640 bytes), none of which overlap each other or the 48 bytes
below the stack pointer (the frame saving the link register), which do not
wrap around. `rate` is one of `rates`, and `pos < rate`. -/
def absorbPPC64LE : Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 200⟩
    let data : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 640⟩
    let stack : Region := ⟨s.sp - 48, 48⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    48 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch ∧
    (s.gpr .r4).toNat ∈ rates ∧ (s.gpr .r5).toNat < (s.gpr .r4).toNat
  post s s' :=
    (∀ msg, Repr s.mem (s.gpr .r3) (s.gpr .r4).toNat msg →
      (s.gpr .r5).toNat = msg.length % (s.gpr .r4).toNat →
      Repr s'.mem (s.gpr .r3) (s.gpr .r4).toNat
        (msg ++ bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat)) ∧
    (s'.gpr .r3).toNat = ((s.gpr .r5).toNat + (s.gpr .r7).toNat) % (s.gpr .r4).toNat
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.sp = s₂.sp

open VG.PPC64LE in
/-- PPC64LE contract for `vg_keccak_pad(state = r3, rate = r4, pos = r5,
suffix = r6, scratch = r7)`: absorbs the padding (with the low byte of
`suffix`) into the streaming state.

The code may read and write `state` (200 bytes) and `scratch` (640 bytes),
none of which overlap each other or the 48 bytes below the stack pointer
(the frame saving the link register), which do not wrap around. `rate` is
one of `rates`, and `pos < rate`. -/
def padPPC64LE : Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 200⟩
    let scratch : Region := ⟨s.gpr .r7, 640⟩
    let stack : Region := ⟨s.sp - 48, 48⟩
    s.rd = [] ∧ s.wr = [state, scratch] ∧ state.Disjoint scratch ∧
    48 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint scratch ∧
    (s.gpr .r4).toNat ∈ rates ∧ (s.gpr .r5).toNat < (s.gpr .r4).toNat
  post s s' := ∀ msg, Repr s.mem (s.gpr .r3) (s.gpr .r4).toNat msg →
    (s.gpr .r5).toNat = msg.length % (s.gpr .r4).toNat →
    stateAt s'.mem (s.gpr .r3) =
      absorb (s.gpr .r4).toNat (pad (s.gpr .r4).toNat ((s.gpr .r6).setWidth 8) msg)
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp

open VG.PPC64LE in
/-- PPC64LE contract for `vg_keccak_squeeze(state = r3, rate = r4, pos = r5,
out = r6, outlen = r7, scratch = r8) -> r3`: writes `outlen` bytes of output
from byte `pos` on to `out`, and returns the position after them, leaving a
state from which the output continues.

The code may read and write `state` (200 bytes), `out` (`outlen` bytes) and
`scratch` (640 bytes), none of which overlap each other or the 48 bytes
below the stack pointer (the frame saving the link register), which do not
wrap around. `rate` is one of `rates`, and `pos ≤ rate`. -/
def squeezePPC64LE : Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 200⟩
    let out : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 640⟩
    let stack : Region := ⟨s.sp - 48, 48⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    48 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (s.gpr .r4).toNat ∈ rates ∧ (s.gpr .r5).toNat ≤ (s.gpr .r4).toNat
  post s s' :=
    bytesAt s'.mem (s.gpr .r6) (s.gpr .r7).toNat =
      squeezeFrom (s.gpr .r4).toNat (stateAt s.mem (s.gpr .r3)) (s.gpr .r5).toNat (s.gpr .r7).toNat ∧
    (s'.gpr .r3).toNat ≤ (s.gpr .r4).toNat ∧
    ∀ d, squeezeFrom (s.gpr .r4).toNat (stateAt s'.mem (s.gpr .r3)) (s'.gpr .r3).toNat d =
      squeezeFrom (s.gpr .r4).toNat (stateAt s.mem (s.gpr .r3))
        ((s.gpr .r5).toNat + (s.gpr .r7).toNat) d
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.sp = s₂.sp

end VG.Proof.Sha3
