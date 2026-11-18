module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Impl.ChaCha20Poly1305.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Poly1305.RISCV64.Lit
meta import VerifiedGarbage.Proof.Poly1305.RISCV64.Lit
public import VerifiedGarbage.Spec.ChaCha20Poly1305
public import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Spec.ChaCha20Poly1305
meta import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace
meta import VerifiedGarbage.TCB.RISCV64.Isa
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `ChaCha20Poly1305.RISCV64.Contract`, which this module and modules that import it used -/

section

/-!
# ChaCha20-Poly1305: the RISC-V contracts

The contracts the proofs are written against; the artifacts are emitted with
the shared contracts with the working space as an argument
(`Proof/ChaCha20Poly1305/Scratch.lean`), which imply these.

`seal` and `open` take `(key = a0, nonce = a1, aad = a2, aad_len = a3,
data = a4, len = a5, tag = a6, work = a7)`: `work` (624 bytes) and `data`
may be read and written, `key`, `nonce` and `aad` read, and `tag` written
(`seal`) or read (`open`). The regions written overlap none of the others;
nothing wraps around the end of the address space. No stack is used.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305

open Spec.ChaCha20Poly1305
open Spec.Poly1305 (bytesAt)

open VG.RISCV64 in
/-- The precondition of both functions; `enc` for `seal`. -/
def preRISCV64 (enc : Bool) (s : RISCV64.State) : Prop :=
  let key : Region := ⟨s.gpr .a0, 32⟩
  let nonce : Region := ⟨s.gpr .a1, 12⟩
  let aad : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
  let data : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
  let tag : Region := ⟨s.gpr .a6, 16⟩
  let work : Region := ⟨s.gpr .a7, 624⟩
  s.rd = (if enc then [key, nonce, aad] else [key, nonce, aad, tag]) ∧
  s.wr = (if enc then [data, tag, work] else [data, work]) ∧
  key.Disjoint data ∧ key.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
  aad.Disjoint data ∧ aad.Disjoint work ∧ data.Disjoint tag ∧ data.Disjoint work ∧
  tag.Disjoint work ∧
  (if enc then key.Disjoint tag ∧ nonce.Disjoint tag ∧ aad.Disjoint tag else True) ∧
  (s.gpr .a0).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 12 ≤ 2 ^ 64 ∧
  (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧ (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64 ∧
  (s.gpr .a6).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .a7).toNat + 624 ≤ 2 ^ 64

open VG.RISCV64 in
def pubRISCV64 (s₁ s₂ : RISCV64.State) : Prop :=
  s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
  s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
  s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧ s₁.sp = s₂.sp

open VG.RISCV64 in
/-- `seal(key, nonce, aad, aad_len, data, len, tag, work)`. -/
def sealRISCV64 : Contract RISCV64.isa where
  pre := preRISCV64 true
  post s s' :=
    encrypt (bytesAt s.mem (s.gpr .a0) 32) (bytesAt s.mem (s.gpr .a1) 12)
        (bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) =
      (bytesAt s'.mem (s.gpr .a4) (s.gpr .a5).toNat, bytesAt s'.mem (s.gpr .a6) 16)
  pub := pubRISCV64

open VG.RISCV64 in
/-- Whether the message is authenticated, in `open`'s state on entry. -/
def okRISCV64 (s : RISCV64.State) : Bool :=
  (decrypt (bytesAt s.mem (s.gpr .a0) 32) (bytesAt s.mem (s.gpr .a1) 12)
    (bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)
    (bytesAt s.mem (s.gpr .a6) 16)).isSome

open VG.RISCV64 in
/-- What `open` may leak (`Spec.ChaCha20Poly1305.openLeak`): whether the
message is authenticated. -/
def openLeakRISCV64 (s : RISCV64.State) : List Nat :=
  [if (decrypt (bytesAt s.mem (s.gpr .a0) 32) (bytesAt s.mem (s.gpr .a1) 12)
    (bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)
    (bytesAt s.mem (s.gpr .a6) 16)).isSome then 1 else 0]

open VG.RISCV64 in
/-- `open(key, nonce, aad, aad_len, data, len, tag, work) -> u32`: zeros at
`data` if the tag is wrong; it may leak whether it is (`openLeakRISCV64`). -/
def openRISCV64 : Contract RISCV64.isa where
  pre := preRISCV64 false
  post s s' :=
    match decrypt (bytesAt s.mem (s.gpr .a0) 32) (bytesAt s.mem (s.gpr .a1) 12)
        (bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)
        (bytesAt s.mem (s.gpr .a6) 16) with
    | some pt => s'.gpr .a0 = 1 ∧ bytesAt s'.mem (s.gpr .a4) (s.gpr .a5).toNat = pt
    | none => s'.gpr .a0 = 0 ∧
        bytesAt s'.mem (s.gpr .a4) (s.gpr .a5).toNat = List.replicate (s.gpr .a5).toNat 0
  pub s₁ s₂ := pubRISCV64 s₁ s₂ ∧ openLeakRISCV64 s₁ = openLeakRISCV64 s₂

/-! ## Out of place

`open_to(key = a0, nonce = a1, aad = a2, aad_len = a3, src = a4, len = a5,
dst = a6, dst_len = a7, tag = [sp], work = [sp + 8]) -> u32`, its last two
arguments on the stack, which it may only read, at the stack pointer, which
is aligned. -/

open VG.RISCV64 in
/-- The two arguments on the stack. -/
abbrev toArgsRISCV64 (s : RISCV64.State) : Region := ⟨stackArgAddr s 0, 16⟩

open VG.RISCV64 in
/-- `open_to`'s precondition: the regions, apart but for those read, the
output as long as the input, at most `P_MAX`. -/
def openToPreRISCV64 (s : RISCV64.State) : Prop :=
  let key : Region := ⟨s.gpr .a0, 32⟩
  let nonce : Region := ⟨s.gpr .a1, 12⟩
  let aad : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
  let src : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
  let dst : Region := ⟨s.gpr .a6, (s.gpr .a7).toNat⟩
  let tag : Region := ⟨stackArg s 0, 16⟩
  let work : Region := ⟨stackArg s 1, 624⟩
  s.rd = [key, nonce, aad, src, tag, toArgsRISCV64 s] ∧ s.wr = [dst, work] ∧
  dst.Disjoint key ∧ dst.Disjoint nonce ∧ dst.Disjoint aad ∧ dst.Disjoint src ∧ dst.Disjoint tag ∧
  dst.Disjoint work ∧ dst.Disjoint (toArgsRISCV64 s) ∧
  work.Disjoint key ∧ work.Disjoint nonce ∧ work.Disjoint aad ∧ work.Disjoint src ∧ work.Disjoint tag ∧
  work.Disjoint (toArgsRISCV64 s) ∧
  (s.gpr .a0).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 12 ≤ 2 ^ 64 ∧
  (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧ (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64 ∧
  (s.gpr .a6).toNat + (s.gpr .a7).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + 16 ≤ 2 ^ 64 ∧
  (stackArg s 1).toNat + 624 ≤ 2 ^ 64 ∧ (stackArgAddr s 0).toNat + 16 ≤ 2 ^ 64 ∧
  s.sp.toNat % 16 = 0 ∧ (s.gpr .a7).toNat = (s.gpr .a5).toNat ∧ (s.gpr .a5).toNat ≤ pMax

open VG.RISCV64 in
/-- `open_to`'s result: `decrypt` of the source, with the tag at `[sp]`. -/
def openToResRISCV64 (s : RISCV64.State) : Option (List Byte) :=
  decrypt (bytesAt s.mem (s.gpr .a0) 32) (bytesAt s.mem (s.gpr .a1) 12)
    (bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)
    (bytesAt s.mem (stackArg s 0) 16)

open VG.RISCV64 in
/-- What `open_to` may leak (`Spec.ChaCha20Poly1305.openToLeak`): whether the
tag is right. -/
def openToLeakRISCV64 (s : RISCV64.State) : List Nat :=
  [if (openToResRISCV64 s).isSome then 1 else 0]

open VG.RISCV64 in
/-- `open_to`: the plaintext or zeros at `dst`. -/
def openToRISCV64 : Contract RISCV64.isa where
  pre := openToPreRISCV64
  post s s' :=
    match openToResRISCV64 s with
    | some pt => s'.gpr .a0 = 1 ∧ bytesAt s'.mem (s.gpr .a6) (s.gpr .a5).toNat = pt
    | none => s'.gpr .a0 = 0 ∧
        bytesAt s'.mem (s.gpr .a6) (s.gpr .a5).toNat = List.replicate (s.gpr .a5).toNat 0
  pub s₁ s₂ := pubRISCV64 s₁ s₂ ∧ (∀ i < 2, stackArg s₁ i = stackArg s₂ i) ∧
    openToLeakRISCV64 s₁ = openToLeakRISCV64 s₂

end VG.Proof.ChaCha20Poly1305

end

end

/-!
# ChaCha20-Poly1305 on RISC-V: constant time

The taint analysis of the whole of `seal`, and of `open` but for its branch
on the result, through their callees: the values they keep in `s7`–`s11`,
which no callee writes, and the context in `a0`, which no callee writes
either, stay public across the calls.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.RISCV64

open VG VG.RISCV64

theorem agree₀ {s₁ s₂ : State} (hpub : pubRISCV64 s₁ s₂) :
    VG.RISCV64.Taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7]) s₁ s₂ := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem seal_ct :
    ConstantTime isa sealRISCV64.pre sealRISCV64.pub
      (Impl.ChaCha20Poly1305.RISCV64.inPlace Impl.ChaCha20Poly1305.RISCV64.«seal») :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7])
    (fun _ _ _ _ hp => agree₀ hp) (by taint_decide)

/-! `open` branches on whether the tag is right, which its contract lets it
leak: the taint analysis checks the parts around the branch, which
`open_ct` (`Verified.lean`) composes. -/

theorem openBody_taint : ∃ h, (VG.Taint.check taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t6])
    Impl.ChaCha20Poly1305.RISCV64.openBody h).isSome = true := ⟨_, by taint_decide⟩

theorem inPlace_taint : ∃ h, (VG.Taint.check taint (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7])
    (.block [Impl.ChaCha20.RISCV64.Xor.mov .t6 .a4]) h).isSome = true := ⟨_, by taint_decide⟩

theorem toEntry_taint : ∃ h, (VG.Taint.check taint (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7])
    (.block Impl.ChaCha20Poly1305.RISCV64.toEntry) h).isSome = true := ⟨_, by taint_decide⟩

theorem zeroData_taint : ∃ h, (VG.Taint.check taint (Taint.ofRegs [.s6, .s10])
    Impl.ChaCha20Poly1305.RISCV64.zeroData h).isSome = true := ⟨_, by taint_decide⟩

theorem tail_taint : ∃ h, (VG.Taint.check taint (Taint.ofRegs [.t0])
    (.block (Impl.ChaCha20Poly1305.RISCV64.restore ++ [Impl.ChaCha20.RISCV64.Xor.mov .a0 .t1])) h).isSome =
      true := ⟨_, by taint_decide⟩

end VG.Proof.ChaCha20Poly1305.RISCV64
