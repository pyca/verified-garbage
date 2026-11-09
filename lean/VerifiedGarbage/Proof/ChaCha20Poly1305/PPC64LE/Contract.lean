module

public import VerifiedGarbage.Spec.ChaCha20Poly1305
public import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# ChaCha20-Poly1305: the PPC64LE contracts

The contracts the proofs are written against; the artifacts are emitted with
the shared contracts with the working space as an argument
(`Proof/ChaCha20Poly1305/Scratch.lean`), which imply these.

`seal` and `open` take `(key = r3, nonce = r4, aad = r5, aad_len = r6,
data = r7, len = r8, tag = r9, work = r10)`: `work` (656 bytes) and `data`
may be read and written, `key`, `nonce` and `aad` read, and `tag` written
(`seal`) or read (`open`). The regions written overlap none of the others,
nor the 160 bytes below the stack pointer (the frame of
`vg_poly1305_blocks`), which nothing else overlaps either; nothing wraps
around the end of the address space.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305

open Spec.ChaCha20Poly1305
open Spec.Poly1305 (bytesAt)

open VG.PPC64LE in
/-- The precondition of both functions; `enc` for `seal`. -/
def prePPC64LE (enc : Bool) (s : PPC64LE.State) : Prop :=
  let key : Region := ⟨s.gpr .r3, 32⟩
  let nonce : Region := ⟨s.gpr .r4, 12⟩
  let aad : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
  let data : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
  let tag : Region := ⟨s.gpr .r9, 16⟩
  let work : Region := ⟨s.gpr .r10, 656⟩
  let below : Region := ⟨s.sp - 160, 160⟩
  160 ≤ s.sp.toNat ∧
  s.rd = (if enc then [key, nonce, aad] else [key, nonce, aad, tag]) ∧
  s.wr = (if enc then [data, tag, work] else [data, work]) ∧
  key.Disjoint data ∧ key.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
  aad.Disjoint data ∧ aad.Disjoint work ∧ data.Disjoint tag ∧ data.Disjoint work ∧
  tag.Disjoint work ∧
  (if enc then key.Disjoint tag ∧ nonce.Disjoint tag ∧ aad.Disjoint tag else True) ∧
  below.Disjoint key ∧ below.Disjoint nonce ∧ below.Disjoint aad ∧ below.Disjoint data ∧
  below.Disjoint tag ∧ below.Disjoint work ∧
  (s.gpr .r3).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + 12 ≤ 2 ^ 64 ∧
  (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧ (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
  (s.gpr .r9).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .r10).toNat + 656 ≤ 2 ^ 64

open VG.PPC64LE in
def pubPPC64LE (s₁ s₂ : PPC64LE.State) : Prop :=
  s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
  s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
  s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧ s₁.sp = s₂.sp

open VG.PPC64LE in
/-- `seal(key, nonce, aad, aad_len, data, len, tag, work)`. -/
def sealPPC64LE : Contract PPC64LE.isa where
  pre := prePPC64LE true
  post s s' :=
    encrypt (bytesAt s.mem (s.gpr .r3) 32) (bytesAt s.mem (s.gpr .r4) 12)
        (bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) (bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) =
      (bytesAt s'.mem (s.gpr .r7) (s.gpr .r8).toNat, bytesAt s'.mem (s.gpr .r9) 16)
  pub := pubPPC64LE

open VG.PPC64LE in
/-- Whether the message is authenticated, in `open`'s state on entry. -/
def okPPC64LE (s : PPC64LE.State) : Bool :=
  (decrypt (bytesAt s.mem (s.gpr .r3) 32) (bytesAt s.mem (s.gpr .r4) 12)
    (bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) (bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat)
    (bytesAt s.mem (s.gpr .r9) 16)).isSome

open VG.PPC64LE in
/-- What `open` may leak (`Spec.ChaCha20Poly1305.openLeak`): whether the
message is authenticated. -/
def openLeakPPC64LE (s : PPC64LE.State) : List Nat :=
  [if (decrypt (bytesAt s.mem (s.gpr .r3) 32) (bytesAt s.mem (s.gpr .r4) 12)
    (bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) (bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat)
    (bytesAt s.mem (s.gpr .r9) 16)).isSome then 1 else 0]

open VG.PPC64LE in
/-- `open(key, nonce, aad, aad_len, data, len, tag, work) -> u32`: zeros at
`data` if the tag is wrong; it may leak whether it is (`openLeakPPC64LE`). -/
def openPPC64LE : Contract PPC64LE.isa where
  pre := prePPC64LE false
  post s s' :=
    match decrypt (bytesAt s.mem (s.gpr .r3) 32) (bytesAt s.mem (s.gpr .r4) 12)
        (bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) (bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat)
        (bytesAt s.mem (s.gpr .r9) 16) with
    | some pt => s'.gpr .r3 = 1 ∧ bytesAt s'.mem (s.gpr .r7) (s.gpr .r8).toNat = pt
    | none => s'.gpr .r3 = 0 ∧
        bytesAt s'.mem (s.gpr .r7) (s.gpr .r8).toNat = List.replicate (s.gpr .r8).toNat 0
  pub s₁ s₂ := pubPPC64LE s₁ s₂ ∧ openLeakPPC64LE s₁ = openLeakPPC64LE s₂

/-! ## Out of place

`open_to(key = r3, nonce = r4, aad = r5, aad_len = r6, src = r7, len = r8,
dst = r9, dst_len = r10, tag = [sp + 96], work = [sp + 104]) -> u32`, its
last two arguments on the stack (ELFv2 ABI §2.2.3.3, the Parameter Save
Area), which it may only read. -/

open VG.PPC64LE in
/-- The two arguments on the stack. -/
abbrev toArgs (s : PPC64LE.State) : Region := ⟨stackArgAddr s 0, 16⟩

open VG.PPC64LE in
/-- `open_to`'s precondition: the regions, apart but for those read, apart
from the 160 bytes below the stack pointer, the output as long as the
input, at most `P_MAX`. -/
def openToPrePPC64LE (s : PPC64LE.State) : Prop :=
  let key : Region := ⟨s.gpr .r3, 32⟩
  let nonce : Region := ⟨s.gpr .r4, 12⟩
  let aad : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
  let src : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
  let dst : Region := ⟨s.gpr .r9, (s.gpr .r10).toNat⟩
  let tag : Region := ⟨stackArg s 0, 16⟩
  let work : Region := ⟨stackArg s 1, 656⟩
  let below : Region := ⟨s.sp - 160, 160⟩
  160 ≤ s.sp.toNat ∧
  s.rd = [key, nonce, aad, src, tag, toArgs s] ∧ s.wr = [dst, work] ∧
  dst.Disjoint key ∧ dst.Disjoint nonce ∧ dst.Disjoint aad ∧ dst.Disjoint src ∧ dst.Disjoint tag ∧
  dst.Disjoint work ∧ dst.Disjoint (toArgs s) ∧
  work.Disjoint key ∧ work.Disjoint nonce ∧ work.Disjoint aad ∧ work.Disjoint src ∧ work.Disjoint tag ∧
  work.Disjoint (toArgs s) ∧
  below.Disjoint key ∧ below.Disjoint nonce ∧ below.Disjoint aad ∧ below.Disjoint src ∧
  below.Disjoint dst ∧ below.Disjoint tag ∧ below.Disjoint work ∧
  (s.gpr .r3).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + 12 ≤ 2 ^ 64 ∧
  (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧ (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
  (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + 16 ≤ 2 ^ 64 ∧
  (stackArg s 1).toNat + 656 ≤ 2 ^ 64 ∧ (stackArgAddr s 0).toNat + 16 ≤ 2 ^ 64 ∧
  (s.gpr .r10).toNat = (s.gpr .r8).toNat ∧ (s.gpr .r8).toNat ≤ pMax

open VG.PPC64LE in
/-- `open_to`'s result: `decrypt` of the source, with the tag at `[sp + 96]`. -/
def openToRes (s : PPC64LE.State) : Option (List Byte) :=
  decrypt (bytesAt s.mem (s.gpr .r3) 32) (bytesAt s.mem (s.gpr .r4) 12)
    (bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) (bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat)
    (bytesAt s.mem (stackArg s 0) 16)

open VG.PPC64LE in
/-- What `open_to` may leak (`Spec.ChaCha20Poly1305.openToLeak`): whether the
tag is right. -/
def openToLeakPPC64LE (s : PPC64LE.State) : List Nat :=
  [if (openToRes s).isSome then 1 else 0]

open VG.PPC64LE in
/-- `open_to`: the plaintext or zeros at `dst`. -/
def openToPPC64LE : Contract PPC64LE.isa where
  pre := openToPrePPC64LE
  post s s' :=
    match openToRes s with
    | some pt => s'.gpr .r3 = 1 ∧ bytesAt s'.mem (s.gpr .r9) (s.gpr .r8).toNat = pt
    | none => s'.gpr .r3 = 0 ∧
        bytesAt s'.mem (s.gpr .r9) (s.gpr .r8).toNat = List.replicate (s.gpr .r8).toNat 0
  pub s₁ s₂ := pubPPC64LE s₁ s₂ ∧ (∀ i < 2, stackArg s₁ i = stackArg s₂ i) ∧
    openToLeakPPC64LE s₁ = openToLeakPPC64LE s₂

end VG.Proof.ChaCha20Poly1305
