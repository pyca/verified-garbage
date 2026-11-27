module

import VerifiedGarbage.Proof.Poly1305.Spec
import VerifiedGarbage.Proof.Poly1305.Stream
import VerifiedGarbage.Proof.ChaCha20.Keystream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
public import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Wp
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Impl.ChaCha20Poly1305.PPC64LE
public import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Xor
public import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Vmx4.Xor
public import VerifiedGarbage.Proof.Poly1305.PPC64LE.Shared
public import VerifiedGarbage.Proof.Poly1305.PPC64LE.Init
public import VerifiedGarbage.Proof.Poly1305.PPC64LE.Finalize
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.ChaCha20
public import VerifiedGarbage.Spec.Poly1305
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Block
public import VerifiedGarbage.Proof.Poly1305.Contract
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.ChaCha20Poly1305
public import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace
public import VerifiedGarbage.TCB.PPC64LE.Target

/-! ### `ChaCha20Poly1305.PPC64LE.Prologue`, which this module and modules that import it used -/

section

/-! ### `ChaCha20Poly1305.PPC64LE.Contract`, which this module and modules that import it used -/

section

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
abbrev toArgsPPC64LE (s : PPC64LE.State) : Region := ⟨stackArgAddr s 0, 16⟩

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
  s.rd = [key, nonce, aad, src, tag, toArgsPPC64LE s] ∧ s.wr = [dst, work] ∧
  dst.Disjoint key ∧ dst.Disjoint nonce ∧ dst.Disjoint aad ∧ dst.Disjoint src ∧ dst.Disjoint tag ∧
  dst.Disjoint work ∧ dst.Disjoint (toArgsPPC64LE s) ∧
  work.Disjoint key ∧ work.Disjoint nonce ∧ work.Disjoint aad ∧ work.Disjoint src ∧ work.Disjoint tag ∧
  work.Disjoint (toArgsPPC64LE s) ∧
  below.Disjoint key ∧ below.Disjoint nonce ∧ below.Disjoint aad ∧ below.Disjoint src ∧
  below.Disjoint dst ∧ below.Disjoint tag ∧ below.Disjoint work ∧
  (s.gpr .r3).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + 12 ≤ 2 ^ 64 ∧
  (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧ (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
  (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + 16 ≤ 2 ^ 64 ∧
  (stackArg s 1).toNat + 656 ≤ 2 ^ 64 ∧ (stackArgAddr s 0).toNat + 16 ≤ 2 ^ 64 ∧
  (s.gpr .r10).toNat = (s.gpr .r8).toNat ∧ (s.gpr .r8).toNat ≤ pMax

open VG.PPC64LE in
/-- `open_to`'s result: `decrypt` of the source, with the tag at `[sp + 96]`. -/
def openToResPPC64LE (s : PPC64LE.State) : Option (List Byte) :=
  decrypt (bytesAt s.mem (s.gpr .r3) 32) (bytesAt s.mem (s.gpr .r4) 12)
    (bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) (bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat)
    (bytesAt s.mem (stackArg s 0) 16)

open VG.PPC64LE in
/-- What `open_to` may leak (`Spec.ChaCha20Poly1305.openToLeak`): whether the
tag is right. -/
def openToLeakPPC64LE (s : PPC64LE.State) : List Nat :=
  [if (openToResPPC64LE s).isSome then 1 else 0]

open VG.PPC64LE in
/-- `open_to`: the plaintext or zeros at `dst`. -/
def openToPPC64LE : Contract PPC64LE.isa where
  pre := openToPrePPC64LE
  post s s' :=
    match openToResPPC64LE s with
    | some pt => s'.gpr .r3 = 1 ∧ bytesAt s'.mem (s.gpr .r9) (s.gpr .r8).toNat = pt
    | none => s'.gpr .r3 = 0 ∧
        bytesAt s'.mem (s.gpr .r9) (s.gpr .r8).toNat = List.replicate (s.gpr .r8).toNat 0
  pub s₁ s₂ := pubPPC64LE s₁ s₂ ∧ (∀ i < 2, stackArg s₁ i = stackArg s₂ i) ∧
    openToLeakPPC64LE s₁ = openToLeakPPC64LE s₂

end VG.Proof.ChaCha20Poly1305

end

end

/-! ### `ChaCha20Poly1305.PPC64LE.Entry`, which this module and modules that import it used -/

section

/-! ### `ChaCha20Poly1305.PPC64LE.Calls`, which only this module used -/

section

/-!
# ChaCha20-Poly1305 on PPC64LE: the calls

Each call of a verified function, from its proof (`WP.call`, or
`WP.callAny` for `vg_poly1305_blocks`, which allocates a frame): what it
needs of the state it is called from, and what holds when it returns. A
call (`bl`) stores nothing in memory, so the callee changes memory only
within the regions it may write (and its frame below the stack pointer).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.PPC64LE

open VG VG.PPC64LE
open VG.Spec.Poly1305 (Repr Buffered bytesAt mac)
open VG.Spec.ChaCha20 (stateAt keystream)

/-- `s'` differs from `s` only in memory within `rs` and in registers that
are not callee-saved. -/
structure Kept (rs : List Region) (s s' : State) : Prop where
  cs : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame rs s.mem s'.mem

theorem Kept.trans {rs : List Region} {s₁ s₂ s₃ : State} (h₁ : Kept rs s₁ s₂) (h₂ : Kept rs s₂ s₃) :
    Kept rs s₁ s₃ :=
  ⟨fun r hr => by rw [h₂.cs r hr, h₁.cs r hr], by rw [h₂.sp, h₁.sp], by rw [h₂.rd, h₁.rd],
    by rw [h₂.wr, h₁.wr], h₁.frame.trans h₂.frame⟩

theorem Kept.sub {rs rs' : List Region} {s s' : State} (h : Kept rs s s')
    (hs : ∀ r ∈ rs, ∃ r' ∈ rs', Region.Sub r r') : Kept rs' s s' :=
  ⟨h.cs, h.sp, h.rd, h.wr, h.frame.sub hs⟩

/-! ## `vg_chacha20_block` -/

theorem block_call {s : State} {S B : Addr} (h3 : s.gpr .r3 = S) (h4 : s.gpr .r4 = B)
    (hdj : (⟨B, 256⟩ : Region).Disjoint ⟨S, 64⟩)
    (hc : Covers ([⟨S, 64⟩] ++ [⟨B, 256⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨B, 256⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨B, 256⟩] s s' →
      stateAt s'.mem B = Spec.ChaCha20.block (stateAt s.mem S) → Q s') :
    WP isa (.call "vg_chacha20_block" Impl.ChaCha20.PPC64LE.block) s Q := by
  refine WP.call (k := Proof.ChaCha20.blockPPC64LE) Proof.ChaCha20.PPC64LE.block_verified.1
    (rd := [⟨S, 64⟩]) (wr := [⟨B, 256⟩]) ?_ hc hw ?_
  · simp only [Proof.ChaCha20.blockPPC64LE, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r4 ∉ linkRegs), h3, h4]
    exact ⟨trivial, trivial, hdj⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    refine hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ ?_
    simpa only [Proof.ChaCha20.blockPPC64LE, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r4 ∉ linkRegs), h3, h4] using hpost

/-! ## `vg_chacha20_xor` -/

/-- `vg_chacha20_xor` from `X` to `D` (`Proof.ChaCha20.PPC64LE.Vmx4.xor_call_to`). -/
theorem xor_call_to {s : State} {S X D B : Addr} {n : Nat} (h3 : s.gpr .r3 = S) (h4 : s.gpr .r4 = X)
    (h5 : s.gpr .r5 = BitVec.ofNat 64 n) (h6 : s.gpr .r6 = B) (h7 : s.gpr .r7 = D) (hn : n < 2 ^ 64)
    (hSX : (⟨S, 64⟩ : Region).Disjoint ⟨X, n⟩) (hSD : (⟨S, 64⟩ : Region).Disjoint ⟨D, n⟩)
    (hSB : (⟨S, 64⟩ : Region).Disjoint ⟨B, 320⟩) (hXB : (⟨X, n⟩ : Region).Disjoint ⟨B, 320⟩)
    (hDB : (⟨D, n⟩ : Region).Disjoint ⟨B, 320⟩) (hXD : D = X ∨ (⟨X, n⟩ : Region).Disjoint ⟨D, n⟩)
    (hX : X.toNat + n ≤ 2 ^ 64) (hD : D.toNat + n ≤ 2 ^ 64)
    (hc : Covers ([⟨X, n⟩] ++ [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s s' →
      Spec.ChaCha20.bytesAt s'.mem D n =
        List.zipWith (· ^^^ ·) (Spec.ChaCha20.bytesAt s.mem X n)
          (keystream (stateAt s.mem S) n) → Q s') :
    WP isa (.call "vg_chacha20_xor" Impl.ChaCha20.PPC64LE.Vmx4.xor) s Q :=
  Proof.ChaCha20.PPC64LE.Vmx4.xor_call_to h3 h4 h5 h6 h7 hn hSX hSD hSB hXB hDB hXD hX hD hc hw
    fun s' hrd hwr hsp hf hcs _ hpost => hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ hpost

/-! ## `vg_poly1305_init` -/

theorem init_call {s : State} {P K : Addr} (h3 : s.gpr .r3 = P) (h4 : s.gpr .r4 = K)
    (hdj : (⟨P, 128⟩ : Region).Disjoint ⟨K, 32⟩)
    (hc : Covers ([⟨K, 32⟩] ++ [⟨P, 128⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨P, 128⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨P, 128⟩] s s' → Repr s'.mem P (bytesAt s.mem K 32) [] → Q s') :
    WP isa (.call "vg_poly1305_init_core" Impl.Poly1305.PPC64LE.init) s Q := by
  refine WP.call (k := Proof.Poly1305.initPPC64LE) Proof.Poly1305.PPC64LE.init_verified.1
    (rd := [⟨K, 32⟩]) (wr := [⟨P, 128⟩]) ?_ hc hw ?_
  · simp only [Proof.Poly1305.initPPC64LE, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r4 ∉ linkRegs), h3, h4]
    exact ⟨trivial, trivial, hdj⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    refine hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ ?_
    simpa only [Proof.Poly1305.initPPC64LE, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r4 ∉ linkRegs), h3, h4] using hpost

/-! ## `vg_poly1305_blocks`, in its frame -/

theorem blocks_call {s : State} {P p : Addr} {n : Nat} (h3 : s.gpr .r3 = P) (h4 : s.gpr .r4 = p)
    (h5 : s.gpr .r5 = BitVec.ofNat 64 n) (hn : 16 * n < 2 ^ 64) (hsp : 160 ≤ s.sp.toNat)
    (hdj : (⟨P, 128⟩ : Region).Disjoint ⟨p, 16 * n⟩)
    (hbP : (⟨s.sp - 160, 160⟩ : Region).Disjoint ⟨P, 128⟩)
    (hbp : (⟨s.sp - 160, 160⟩ : Region).Disjoint ⟨p, 16 * n⟩)
    (hP : P.toNat + 128 ≤ 2 ^ 64) (hp : p.toNat + 16 * n ≤ 2 ^ 64)
    (hc : Covers ([⟨p, 16 * n⟩] ++ [⟨P, 128⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨P, 128⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨P, 128⟩, ⟨s.sp - 160, 160⟩] s s' →
      (∀ key msg, Repr s.mem P key msg → Repr s'.mem P key (msg ++ bytesAt s.mem p (16 * n))) →
      Q s') :
    WP isa (.call "vg_poly1305_blocks" Impl.ChaCha20Poly1305.PPC64LE.blocksCode) s Q := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hn])
  refine WP.callAny (k := Proof.Poly1305.blocksContract PPC64LE.abi 160)
    Proof.Poly1305.PPC64LE.Shared.blocks.1
    (rd := [⟨p, 16 * n⟩]) (wr := [⟨P, 128⟩]) ?_ hc hw ?_
  · sig_pre [Proof.Poly1305.blocksContract, Proof.Poly1305.blocksSig, PPC64LE.abi, PPC64LE.argRegs]
    simp only [h3, h4, h5, hn', Nat.mul_comm n 16]
    exact ⟨hsp, trivial, trivial, hdj, hbP, hbp, hP, hp⟩
  · intro s' hrd hwr hsp' hf hcs hpost
    refine hQ s' ⟨hcs, hsp', hrd, hwr, ?_⟩ fun key msg hr => ?_
    · refine hf.sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
    · sig_post [Proof.Poly1305.blocksContract, Proof.Poly1305.blocksSig, Proof.Poly1305.blocksPost,
        PPC64LE.abi, PPC64LE.argRegs] at hpost
      simp only [h3, h4, h5, hn'] at hpost
      exact hpost key msg hr

/-! ## `vg_poly1305_finalize_scratch` -/

theorem finalize_call {s : State} {P O Sc : Addr} {c : BitVec 64} (h3 : s.gpr .r3 = P)
    (h4 : s.gpr .r4 = c) (h5 : s.gpr .r5 = O) (h6 : s.gpr .r6 = Sc)
    (hPO : (⟨P, 128⟩ : Region).Disjoint ⟨O, 16⟩) (hPS : (⟨P, 128⟩ : Region).Disjoint ⟨Sc, 128⟩)
    (hOS : (⟨O, 16⟩ : Region).Disjoint ⟨Sc, 128⟩)
    (hc : Covers ([] ++ [⟨P, 128⟩, ⟨O, 16⟩, ⟨Sc, 128⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨P, 128⟩, ⟨O, 16⟩, ⟨Sc, 128⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨P, 128⟩, ⟨O, 16⟩, ⟨Sc, 128⟩] s s' →
      (∀ key msg, Buffered s.mem P key msg → c.toNat % 16 = msg.length % 16 →
        bytesAt s'.mem O 16 = mac key msg) → Q s') :
    WP isa (.call "vg_poly1305_finalize_scratch" Impl.Poly1305.PPC64LE.finalize) s Q := by
  refine WP.call (k := Proof.Poly1305.finalizePPC64LE) Proof.Poly1305.PPC64LE.finalize_verified.1
    (rd := []) (wr := [⟨P, 128⟩, ⟨O, 16⟩, ⟨Sc, 128⟩]) ?_ hc hw ?_
  · simp only [Proof.Poly1305.finalizePPC64LE, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r5 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r6 ∉ linkRegs), h3, h5, h6]
    exact ⟨trivial, trivial, hPO, hPS, hOS⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    refine hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ ?_
    simpa only [Proof.Poly1305.finalizePPC64LE, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r4 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r5 ∉ linkRegs), h3, h4, h5] using hpost

end VG.Proof.ChaCha20Poly1305.PPC64LE

end

end


/-!
# ChaCha20-Poly1305 on PPC64LE: the entry state, the invariant and the prologue

What the proofs use of the precondition (`APre`), the values kept in
`r24`–`r29` and our caller's registers saved in the context, and the
invariant that holds between the parts of the code (`Inv`); then the
prologue, which saves the registers, moves the arguments and stores the
ChaCha20 state for counter 0 in the context.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.PPC64LE

open VG VG.PPC64LE VG.Impl.ChaCha20Poly1305.PPC64LE
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20 (stateAt)

/-- `p + d`, as the code computes it. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d

section
variable (s₀ : State)
abbrev cx : Addr := s₀.gpr .r10
abbrev kp : Addr := s₀.gpr .r3
abbrev np : Addr := s₀.gpr .r4
abbrev ad : Addr := s₀.gpr .r5
abbrev AL : Nat := (s₀.gpr .r6).toNat
abbrev dp : Addr := s₀.gpr .r7
abbrev L : Nat := (s₀.gpr .r8).toNat
abbrev tp : Addr := s₀.gpr .r9
/-- The destination: `src` in place, or apart from it. -/
abbrev op : Addr := s₀.gpr .r11

abbrev K : List Byte := bytesAt s₀.mem (kp s₀) 32
abbrev N : List Byte := bytesAt s₀.mem (np s₀) 12
abbrev A : List Byte := bytesAt s₀.mem (ad s₀) (AL s₀)
abbrev D : List Byte := bytesAt s₀.mem (dp s₀) (L s₀)
abbrev T0 : List Byte := bytesAt s₀.mem (tp s₀) 16
abbrev otk : List Byte := Spec.ChaCha20Poly1305.polyKeyGen (K s₀) (N s₀)

abbrev ctxR : Region := ⟨cx s₀, 656⟩
abbrev kR : Region := ⟨kp s₀, 32⟩
abbrev nR : Region := ⟨np s₀, 12⟩
abbrev aR : Region := ⟨ad s₀, AL s₀⟩
abbrev dR : Region := ⟨dp s₀, L s₀⟩
abbrev tR : Region := ⟨tp s₀, 16⟩
abbrev oR : Region := ⟨op s₀, L s₀⟩
/-- The frame of `vg_poly1305_blocks`, below the stack pointer. -/
abbrev belR : Region := ⟨s₀.sp - 160, 160⟩
/-- `ctx[k, k + n)`. -/
abbrev sub (k n : Nat) : Region := ⟨off (cx s₀) k, n⟩
end

/-- What the proof uses of the precondition; `enc` for `seal`, which runs
in place. -/
structure APre (enc : Bool) (s₀ : State) : Prop where
  sp160 : 160 ≤ s₀.sp.toNat
  k_rd : kR s₀ ∈ s₀.rd
  n_rd : nR s₀ ∈ s₀.rd
  a_rd : aR s₀ ∈ s₀.rd
  /-- The source is readable. -/
  d_in : dR s₀ ∈ s₀.rd ++ s₀.wr
  /-- The destination is writable. -/
  o_wr : oR s₀ ∈ s₀.wr
  ctx_wr : ctxR s₀ ∈ s₀.wr
  t_in : if enc then tR s₀ ∈ s₀.wr else tR s₀ ∈ s₀.rd
  k_c : (kR s₀).Disjoint (ctxR s₀)
  n_c : (nR s₀).Disjoint (ctxR s₀)
  a_c : (aR s₀).Disjoint (ctxR s₀)
  d_c : (dR s₀).Disjoint (ctxR s₀)
  t_c : (tR s₀).Disjoint (ctxR s₀)
  k_o : (kR s₀).Disjoint (oR s₀)
  n_o : (nR s₀).Disjoint (oR s₀)
  a_o : (aR s₀).Disjoint (oR s₀)
  o_t : (oR s₀).Disjoint (tR s₀)
  o_c : (oR s₀).Disjoint (ctxR s₀)
  /-- In place, or (`open` only) apart. -/
  alias : op s₀ = dp s₀ ∨ (enc = false ∧ (dR s₀).Disjoint (oR s₀))
  enc_t : if enc then (kR s₀).Disjoint (tR s₀) ∧ (nR s₀).Disjoint (tR s₀) ∧
    (aR s₀).Disjoint (tR s₀) else True
  b_k : (belR s₀).Disjoint (kR s₀)
  b_n : (belR s₀).Disjoint (nR s₀)
  b_a : (belR s₀).Disjoint (aR s₀)
  b_d : (belR s₀).Disjoint (dR s₀)
  b_o : (belR s₀).Disjoint (oR s₀)
  b_t : (belR s₀).Disjoint (tR s₀)
  b_c : (belR s₀).Disjoint (ctxR s₀)
  fit_k : (kp s₀).toNat + 32 ≤ 2 ^ 64
  fit_n : (np s₀).toNat + 12 ≤ 2 ^ 64
  fit_a : (ad s₀).toNat + AL s₀ ≤ 2 ^ 64
  fit_d : (dp s₀).toNat + L s₀ ≤ 2 ^ 64
  fit_o : (op s₀).toNat + L s₀ ≤ 2 ^ 64
  fit_t : (tp s₀).toNat + 16 ≤ 2 ^ 64
  fit_c : (cx s₀).toNat + 656 ≤ 2 ^ 64

variable {e : Bool}

theorem APre.t_wr {s₀ : State} (hp : APre true s₀) : tR s₀ ∈ s₀.wr := hp.t_in

theorem APre.t_rd {s₀ : State} (hp : APre false s₀) : tR s₀ ∈ s₀.rd := hp.t_in

/-- `seal` runs in place. -/
theorem APre.inPlace {s₀ : State} (hp : APre true s₀) : op s₀ = dp s₀ := by
  rcases hp.alias with h | ⟨h, -⟩
  · exact h
  · exact absurd h (by decide)

/-! ## Regions -/

theorem sub_ctx (s₀ : State) {k n : Nat} (h : k + n ≤ 656) : Region.Sub (sub s₀ k n) (ctxR s₀) :=
  Offset.sub_base _ h

theorem sub_disj (s₀ : State) {a n b m : Nat} (h : a + n ≤ b ∨ b + m ≤ a) (ha : a + n ≤ 656)
    (hb : b + m ≤ 656) : (sub s₀ a n).Disjoint (sub s₀ b m) :=
  Offset.disjoint (cx s₀) h (by omega_using [ha]) (by omega_using [hb])

theorem contains_sub (s₀ : State) {k n a w : Nat} (h₁ : k ≤ a) (h₂ : a + w ≤ k + n) (h₃ : k + n ≤ 656) :
    (sub s₀ k n).Contains (off (cx s₀) a) w := Offset.contains (cx s₀) h₁ h₂ (by omega_using [h₃])

theorem contains_ctx (s₀ : State) {a w : Nat} (h : a + w ≤ 656) : (ctxR s₀).Contains (off (cx s₀) a) w :=
  Offset.contains_base (cx s₀) h (by omega_using [h])

theorem off_off (p : Addr) (a b : Nat) : off (off p a) b = off p (a + b) := by
  show p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem off_zero (p : Addr) : off p 0 = p := BitVec.add_zero p

theorem sub_zero (s₀ : State) (n : Nat) : sub s₀ 0 n = ⟨cx s₀, n⟩ := by simp [sub, off]

namespace APre
variable {s₀ : State} (hp : APre e s₀)
include hp

theorem in_ctx {a w : Nat} (h : a + w ≤ 656) : InRegions s₀.wr (off (cx s₀) a) w :=
  ⟨ctxR s₀, hp.ctx_wr, contains_ctx s₀ h⟩

theorem in_ctx' {a w : Nat} (h : a + w ≤ 656) : InRegions (s₀.rd ++ s₀.wr) (off (cx s₀) a) w :=
  ⟨ctxR s₀, List.mem_append_right _ hp.ctx_wr, contains_ctx s₀ h⟩

theorem k_in {d : Nat} (h : d + 4 ≤ 32) {s : State} (hrd : s.rd = s₀.rd) :
    InRegions (s.rd ++ s.wr) (off (kp s₀) d) 4 :=
  ⟨kR s₀, by rw [hrd]; exact List.mem_append_left _ hp.k_rd, Offset.contains_base _ h (by omega_using [h])⟩

theorem n_in {d : Nat} (h : d + 4 ≤ 12) {s : State} (hrd : s.rd = s₀.rd) :
    InRegions (s.rd ++ s.wr) (off (np s₀) d) 4 :=
  ⟨nR s₀, by rw [hrd]; exact List.mem_append_left _ hp.n_rd, Offset.contains_base _ h (by omega_using [h])⟩

end APre

/-! ## The saved registers and the invariant -/

/-- Our caller's `r24`–`r29` and `r31`, and our return address, saved in
`ctx[464, 528)`. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  (∀ i < 7, m.readW (off (cx s₀) (savOff + 8 * i)) 64 = s₀.gpr (saved i)) ∧
    m.readW (off (cx s₀) (savOff + 56)) 64 = s₀.lr

/-- The saved registers survive a frame that does not touch them. -/
theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (sub s₀ savOff 64).Disjoint r) : Saved s₀ m' := by
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [hf.readW (contains_sub s₀ (w := 64 / 8) (by simp only [savOff]; omega_using [])
      (by simp only [savOff]; omega_using [hi]) (by decide)) hd (by decide), h.1 i hi]
  · rw [hf.readW (contains_sub s₀ (w := 64 / 8) (by simp only [savOff]; omega_using [])
      (by simp only [savOff]; omega_using []) (by decide)) hd (by decide), h.2]

/-- The values we keep in `r24`–`r29` and `r31`. -/
structure Regs (s₀ s : State) : Prop where
  r24 : s.gpr .r24 = cx s₀
  r25 : s.gpr .r25 = s₀.gpr .r5
  r26 : s.gpr .r26 = s₀.gpr .r6
  r27 : s.gpr .r27 = s₀.gpr .r7
  r28 : s.gpr .r28 = s₀.gpr .r8
  r29 : s.gpr .r29 = s₀.gpr .r9
  r31 : s.gpr .r31 = s₀.gpr .r11

theorem Regs.kept {s₀ s s' : State} (h : Regs s₀ s) (hk : ∀ r ∈ preserved, s'.gpr r = s.gpr r) :
    Regs s₀ s' :=
  ⟨by rw [hk _ (by decide), h.r24], by rw [hk _ (by decide), h.r25],
    by rw [hk _ (by decide), h.r26], by rw [hk _ (by decide), h.r27],
    by rw [hk _ (by decide), h.r28], by rw [hk _ (by decide), h.r29], by rw [hk _ (by decide), h.r31]⟩

/-- What holds between the parts of the code: the registers, the stack
pointer and the regions, the saved registers, and the memory changed only
in the context, the destination and the stack below the stack pointer. -/
structure Inv (s₀ : State) (s : State) : Prop where
  regs : Regs s₀ s
  pres : ∀ r ∈ preserved, (∀ i < 7, r ≠ saved i) → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : Saved s₀ s.mem
  frame : Frame [ctxR s₀, oR s₀, belR s₀] s₀.mem s.mem

/-- The invariant survives a part that keeps the callee-saved registers and
writes only the context outside the saved registers, the destination and the stack
below the stack pointer. -/
theorem Inv.step {s₀ s s' : State} {rs : List Region} (h : Inv s₀ s) (hk : Kept rs s s')
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [ctxR s₀, oR s₀, belR s₀], Region.Sub r r')
    (hsv : ∀ r ∈ rs, (sub s₀ savOff 64).Disjoint r) : Inv s₀ s' where
  regs := h.regs.kept hk.cs
  pres r hr hne := by rw [hk.cs r hr, h.pres r hr hne]
  sp := by rw [hk.sp, h.sp]
  rd := by rw [hk.rd, h.rd]
  wr := by rw [hk.wr, h.wr]
  saved := h.saved.frame hk.frame hsv
  frame := h.frame.trans (hk.frame.sub hsub)

/-- A part that writes `ctx[k, k + n)` keeps the invariant. -/
theorem Inv.step1 {s₀ s s' : State} (h : Inv s₀ s) {k n : Nat} (hk : Kept [sub s₀ k n] s s')
    (h₂ : k + n ≤ 656) (h₃ : k + n ≤ savOff ∨ savOff + 64 ≤ k) : Inv s₀ s' :=
  h.step hk (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨ctxR s₀, by simp, sub_ctx s₀ h₂⟩)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by simp only [savOff] at h₃ ⊢; omega_using [h₃]) (by decide) h₂)

/-- A part that writes no memory keeps the invariant. -/
theorem Inv.step0 {s₀ s s' : State} (h : Inv s₀ s) (hk : Kept [] s s') : Inv s₀ s' :=
  h.step hk (fun _ hr => absurd hr List.not_mem_nil) (fun _ hr => absurd hr List.not_mem_nil)

/-- The context may be read and written. -/
def CtxOk (s₀ s : State) : Prop :=
  ∀ a w, a + w ≤ 656 → InRegions (s.rd ++ s.wr) (off (cx s₀) a) w ∧ InRegions s.wr (off (cx s₀) a) w

theorem Inv.ctxOk {s₀ s : State} (hp : APre e s₀) (h : s.rd = s₀.rd) (h' : s.wr = s₀.wr) : CtxOk s₀ s :=
  fun _ _ hw => by rw [h, h']; exact ⟨hp.in_ctx' hw, hp.in_ctx hw⟩

theorem Kept.mem_eq {s s' : State} (hk : Kept [] s s') : s'.mem = s.mem :=
  funext fun x => hk.frame x fun _ h => absurd h List.not_mem_nil

end VG.Proof.ChaCha20Poly1305.PPC64LE

end

end

/-!
# ChaCha20-Poly1305 on PPC64LE: the prologue

Saving the registers, moving the arguments, the ChaCha20 state for counter
0, the one-time key and the Poly1305 state for it; and what the later parts
use of memory and of the callees' regions.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.PPC64LE

open VG VG.PPC64LE VG.Impl.ChaCha20Poly1305.PPC64LE
open VG.Impl.ChaCha20.PPC64LE.Xor (mov)
open VG.Spec.Poly1305 (Repr bytesAt)
open VG.Spec.ChaCha20 (stateAt)

variable {e : Bool}

theorem savOff_eq : savOff = 464 := rfl
theorem stOff_eq : stOff = 320 := rfl
/-- A register not callee-saved is not a callee-saved one. -/
theorem ne_of_pres {r d : Reg} (hr : r ∈ preserved) (hd : d ∉ preserved := by decide) : r ≠ d := by
  rintro rfl; exact hd hr

/-! ## Memory -/

theorem off_add (p : Addr) (a b : Nat) : off p a + BitVec.ofNat 64 b = off p (a + b) := off_off p a b

/-- A read at `p + d` after a write at `p + e`, elsewhere. -/
theorem readW_writeW_off (m : Mem) (p : Addr) {w w' : Nat} (v : BitVec w') {d e : Nat}
    (hd : d + w / 8 ≤ 2 ^ 64) (he : e + w' / 8 ≤ 2 ^ 64) (h : d + w / 8 ≤ e ∨ e + w' / 8 ≤ d)
    (hw : w / 8 < 2 ^ 64 := by decide) :
    (m.writeW (off p e) v).readW (off p d) w = m.readW (off p d) w :=
  Mem.readW_writeW_sep (Offset.sep p h hd he) hw

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- A Poly1305 state outside a frame is unchanged. -/
theorem Repr.frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr}
    (hd : ∀ r ∈ rs, (⟨P, 128⟩ : Region).Disjoint r) {key msg : List Byte} (h : Repr m P key msg) :
    Repr m' P key msg := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, ?_⟩
  · rw [show (P + 24 : Addr) = P + BitVec.ofNat 64 24 from rfl,
      bytesAt_frame hf (n := 32) (fun r hr => (hd r hr).sub_left (Offset.sub_base P (d := 24) (by decide)))
      (by decide)]
    exact h2
  · rw [bytesAt_frame hf (n := 24) (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by decide)))
      (by decide)]
    exact h3

/-- A ChaCha20 state outside a frame is unchanged. -/
theorem stateAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 64⟩ : Region).Disjoint r) : stateAt m' p = stateAt m p := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn]
  exact hf.readW (Offset.contains_base p (by omega_using [hi]) (by omega_using [hi])) hd (by decide)

/-- Byte `i` of a little-endian doubleword. -/
theorem readW64_byte (m : Mem) (a : Addr) {i : Nat} (hi : i < 8) :
    m (a + BitVec.ofNat 64 i) = (m.readW a 64).extractLsb' (8 * i) 8 := by
  rw [← Mem.extractLsb'_read m a (n := 8) hi]
  simp only [Mem.readW]
  rfl

/-- Bytes equal byte by byte. -/
theorem bytesAt_eq_of {m m' : Mem} {p q : Addr} {n : Nat}
    (h : ∀ i < n, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    bytesAt m' q n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.ext_getElem (by simp)
  intro i h₁ _
  simp only [List.getElem_map, List.getElem_range]
  exact h i (by simpa using h₁)

/-- Doublewords copied are bytes copied. -/
theorem bytes_of_dwords {m m' : Mem} {p q : Addr} {n : Nat}
    (h : ∀ k < n, m'.readW (q + BitVec.ofNat 64 (8 * k)) 64 = m.readW (p + BitVec.ofNat 64 (8 * k)) 64) :
    bytesAt m' q (8 * n) = bytesAt m p (8 * n) := by
  refine bytesAt_eq_of fun i hi => ?_
  have e : ∀ a : Addr, a + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (8 * (i / 8)) + BitVec.ofNat 64 (i % 8) := by
    intro a
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.div_add_mod]
  rw [e, e, readW64_byte m' _ (Nat.mod_lt _ (by decide)), readW64_byte m _ (Nat.mod_lt _ (by decide)),
    h _ (by omega_using [hi])]

/-- The first `n ≤ 64` bytes of a ChaCha20 state in memory. -/
theorem bytesAt_serialize (m : Mem) (p : Addr) {n : Nat} (hn : n ≤ 64) :
    bytesAt m p n = (Spec.ChaCha20.serialize (stateAt m p)).take n := by
  apply List.ext_getElem
  · simp [bytesAt, VG.Proof.ChaCha20.length_serialize]; omega_using [hn]
  · intro i h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    have e := VG.Proof.ChaCha20.serialize_stateAt m p (i := i) (by omega_using [hn, h₁])
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
      rw [VG.Proof.ChaCha20.length_serialize]; omega_using [hn, h₁]), Option.getD_some] at e
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_take, e]

/-! ## Covering the callees' regions -/

theorem covers_right {rs rd wr : List Region} (h : Covers rs wr) : Covers rs (rd ++ wr) := fun a n hi =>
  let ⟨r, hr, hc⟩ := h a n hi; ⟨r, List.mem_append_right _ hr, hc⟩

theorem covers_sub {s₀ s : State} (hp : APre e s₀) (hwr : s.wr = s₀.wr) (rs : List Region)
    (h : ∀ r ∈ rs, ∃ k, r = sub s₀ k r.len ∧ k + r.len ≤ 656) : Covers rs s.wr := by
  refine Covers.of_sub fun r hr => ?_
  obtain ⟨k, hrk, hk⟩ := h r hr
  exact ⟨ctxR s₀, by rw [hwr]; exact hp.ctx_wr, k, by rw [hrk], hk⟩

/-- A callee's working space (at `ctx + a`, `n` bytes) and argument (at
`ctx + b`, `m` bytes) in the context. -/
theorem covers2 {s₀ s : State} (hp : APre e s₀) (hwr : s.wr = s₀.wr) {a n b m : Nat}
    (ha : a + n ≤ 656) (hb : b + m ≤ 656) :
    Covers ([sub s₀ b m] ++ [sub s₀ a n]) (s.rd ++ s.wr) :=
  covers_right (covers_sub hp hwr _ fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨b, rfl, hb⟩
    · exact ⟨a, rfl, ha⟩)

theorem covers1 {s₀ s : State} (hp : APre e s₀) (hwr : s.wr = s₀.wr) {a n : Nat} (ha : a + n ≤ 656) :
    Covers [sub s₀ a n] s.wr :=
  covers_sub hp hwr _ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨a, rfl, ha⟩

/-! ## Saving the registers -/

/-- The first `n` registers saved. -/
structure SI (s₀ : State) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [sub s₀ savOff 64] s₀.mem s.mem
  saved : ∀ i < n, s.mem.readW (off (cx s₀) (savOff + 8 * i)) 64 = s₀.gpr (saved i)

theorem save_step {s₀ : State} (hp : APre e s₀) {n : Nat} (hn : n < 7) {s : State} (h : SI s₀ n s) :
    WP isa (.block [.store .d (saved n) .r10 (savOff + 8 * n)]) s (SI s₀ (n + 1)) := by
  refine wp_std (a := off (cx s₀) (savOff + 8 * n)) (by decide) (by rw [savOff_eq]; omega_using [hn])
    (by rw [h.gpr]) (by rw [h.wr]; exact hp.in_ctx (by rw [savOff_eq]; omega_using [hn])) fun s' u => WP.block_nil ?_
  refine ⟨by rw [u.gpr, h.gpr], by rw [u.sp, h.sp], by rw [u.lr, h.lr], by rw [u.rd, h.rd],
    by rw [u.wr, h.wr], ?_, fun i hi => ?_⟩
  · rw [u.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _
      (contains_sub s₀ (w := 64 / 8) (by omega_using []) (by omega_using [hn]) (by decide))
  · rw [u.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [readW_writeW_off _ _ _ (by rw [savOff_eq]; omega_arith) (by rw [savOff_eq]; omega_using [hn]) (by omega_using [hi])]
      exact h.saved i hi
    · rw [Mem.readW_writeW_self64, h.gpr]

/-- Saving the registers and the return address. -/
theorem save_ok {s₀ : State} (hp : APre e s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s, (∀ r, r ≠ .r0 → s.gpr r = s₀.gpr r) → s.sp = s₀.sp → s.rd = s₀.rd → s.wr = s₀.wr →
      Saved s₀ s.mem → Frame [sub s₀ savOff 64] s₀.mem s.mem → WP isa (.block rest) s Q) :
    WP isa (.block (save ++ rest)) s₀ Q := by
  rw [save, List.append_assoc]
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (SI s₀)
    (fun k s hk h => save_step hp hk h) 7 (Nat.le_refl _) s₀
    ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s h => ?_)
  refine wp_mflr fun s₁ u₁ => ?_
  refine wp_std (a := off (cx s₀) (savOff + 56)) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), h.gpr]) (by rw [u₁.wr, h.wr]; exact hp.in_ctx (by decide))
    fun s₂ u₂ => ?_
  refine k s₂ (fun r hr => by rw [u₂.gpr, u₁.other r hr, h.gpr]) (by rw [u₂.sp, u₁.sp, h.sp])
    (by rw [u₂.rd, u₁.rd, h.rd]) (by rw [u₂.wr, u₁.wr, h.wr]) ⟨fun i hi => ?_, ?_⟩ ?_
  · rw [u₂.mem, readW_writeW_off _ _ _ (by rw [savOff_eq]; omega_using [hi]) (by decide) (by omega_using [hi]), u₁.mem]
    exact h.saved i hi
  · rw [u₂.mem, Mem.readW_writeW_self64, u₁.gpr, h.lr]
  · rw [u₂.mem, u₁.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _
      (contains_sub s₀ (w := 64 / 8) (by omega_using []) (by omega_using []) (by decide))

/-! ## Moving the arguments -/

theorem moves_ok {s₀ s : State} (hg : ∀ r, r ≠ .r0 → s.gpr r = s₀.gpr r) :
    WP isa (.block moves) s fun s' => Regs s₀ s' ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ ∀ r, (∀ i < 7, r ≠ saved i) → s'.gpr r = s.gpr r := by
  unfold moves
  refine wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ =>
    wp_mov fun s₅ u₅ => wp_mov fun s₆ u₆ => wp_mov fun s₇ u₇ =>
    WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hg _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hg _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hg _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hg _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hg _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hg _ (by decide)]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hg _ (by decide)]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · intro r hr
    rw [u₇.other r (hr 6 (by decide)), u₆.other r (hr 5 (by decide)), u₅.other r (hr 4 (by decide)),
      u₄.other r (hr 3 (by decide)), u₃.other r (hr 2 (by decide)), u₂.other r (hr 1 (by decide)),
      u₁.other r (hr 0 (by decide))]

/-- Saving the registers and moving the arguments. -/
theorem saveMoves_ok {s₀ : State} (hp : APre e s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s, Regs s₀ s → (∀ r, (∀ i < 7, r ≠ saved i) → r ≠ .r0 → s.gpr r = s₀.gpr r) →
      s.gpr .r3 = kp s₀ → s.gpr .r4 = np s₀ → s.sp = s₀.sp → s.rd = s₀.rd →
      s.wr = s₀.wr → Saved s₀ s.mem → Frame [sub s₀ savOff 64] s₀.mem s.mem → WP isa (.block rest) s Q) :
    WP isa (.block (save ++ moves ++ rest)) s₀ Q := by
  rw [List.append_assoc]
  refine save_ok hp fun s₁ g₁ sp₁ rd₁ wr₁ sv₁ f₁ => ?_
  refine WP.block_append (WP.mono (moves_ok g₁) fun s₂ ⟨rg, m₂, rd₂, wr₂, sp₂, o₂⟩ => ?_)
  refine k s₂ rg (fun r hr h0 => by rw [o₂ r hr, g₁ r h0]) ?_ ?_ (by rw [sp₂, sp₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) (by rw [m₂]; exact sv₁)
    (by rw [m₂]; exact f₁)
  · rw [o₂ _ (by decide), g₁ _ (by decide)]
  · rw [o₂ _ (by decide), g₁ _ (by decide)]

/-! ## Copying doublewords of the context -/

theorem copyWords_step (a b n : Nat) : copyWords a b (n + 1) =
    copyWords a b n ++ ([.load .d .r12 .r24 (a + 8 * n), .store .d .r12 .r24 (b + 8 * n)] : List Instr) := by
  simp [copyWords, List.range_succ, List.flatMap_append]

/-- `n` doublewords from `ctx + a` to `ctx + b`. -/
theorem copyWords_ok {s₀ : State} {a b n : Nat} (hab : a + 8 * n ≤ b ∨ b + 8 * n ≤ a)
    (ha : a + 8 * n ≤ 656) (hb : b + 8 * n ≤ 656) (ha4 : a % 4 = 0) (hb4 : b % 4 = 0) {s : State}
    (h14 : s.gpr .r24 = cx s₀) (hc : CtxOk s₀ s) :
    WP isa (.block (copyWords a b n)) s fun s' =>
      (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [sub s₀ b (8 * n)] s.mem s'.mem ∧
      ∀ i < n, s'.mem.readW (off (cx s₀) (b + 8 * i)) 64 = s.mem.readW (off (cx s₀) (a + 8 * i)) 64 := by
  induction n with
  | zero =>
    exact WP.block_nil (M := isa) ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun i hi => absurd hi (by omega_using [])⟩
  | succ n ih =>
    rw [copyWords_step]
    refine WP.block_append (WP.mono (ih (by omega_using [hab]) (by omega_using [ha]) (by omega_using [hb]))
      fun s₁ ⟨g₁, rd₁, wr₁, sp₁, f₁, w₁⟩ => ?_)
    have hc₁ : CtxOk s₀ s₁ := by rw [CtxOk, rd₁, wr₁]; exact hc
    have h14₁ : s₁.gpr .r24 = cx s₀ := by rw [g₁ _ (by decide), h14]
    refine wp_ld (a := off (cx s₀) (a + 8 * n)) (by decide) (by omega_using [ha4, ha]) (by rw [h14₁])
      (hc₁ _ 8 (by omega_using [ha])).1 fun s₂ u₂ => ?_
    refine wp_std (a := off (cx s₀) (b + 8 * n)) (by decide) (by omega_using [hb4, hb])
      (by rw [u₂.other _ (by decide), h14₁]) (by rw [u₂.wr]; exact (hc₁ _ 8 (by omega_using [hb])).2)
      fun s₃ u₃ => WP.block_nil ?_
    refine ⟨fun r hr => by rw [u₃.gpr, u₂.other r hr, g₁ r hr], by rw [u₃.rd, u₂.rd, rd₁],
      by rw [u₃.wr, u₂.wr, wr₁], by rw [u₃.sp, u₂.sp, sp₁], ?_, fun i hi => ?_⟩
    · rw [u₃.mem, u₂.mem]
      refine (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _ ?_
      · simp only [List.mem_singleton] at hr; subst hr
        exact Region.sub_prefix (by omega_using [])
      · exact contains_sub s₀ (w := 64 / 8) (by omega_using []) (by omega_using []) (by omega_using [hb])
    · rw [u₃.mem, u₂.gpr, u₂.mem]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [readW_writeW_off _ _ _ (by omega_arith) (by omega_using [hb]) (by omega_using [hi]), w₁ i hi]
      · rw [Mem.readW_writeW_self64]
        exact f₁.readW (contains_sub s₀ (k := a + 8 * i) (n := 8) (w := 64 / 8) (Nat.le_refl _) (by omega_using [])
            (by omega_using [ha]))
          (by simp only [List.mem_singleton, forall_eq]; exact sub_disj s₀ (by omega_using [hab]) (by omega_using [ha]) (by omega_using [hb]))
          (by decide)

/-! ## The ChaCha20 state -/

/-- The word `stW k` stores, from memory `m`, the key at `kp` and the nonce at `np`. -/
def wordOf (m : Mem) (kp np : Addr) (k : Nat) : BitVec 32 :=
  if k < 4 then consts.getD k 0
  else if k < 12 then m.readW (off kp (4 * (k - 4))) 32
  else if k = 12 then 0
  else m.readW (off np (4 * (k - 13))) 32

theorem sw32 (v : BitVec 32) : (v.setWidth 64).setWidth 32 = v :=
  BitVec.setWidth_setWidth_of_le _ (by decide)

theorem stW_ok {s₀ : State} (hp : APre e s₀) {k : Nat} (hk : k < 16) {s : State}
    (h14 : s.gpr .r24 = cx s₀) (h3 : s.gpr .r3 = kp s₀) (h4 : s.gpr .r4 = np s₀) (hrd : s.rd = s₀.rd)
    (hc : CtxOk s₀ s) :
    WP isa (.block (stW k)) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) (stOff + 4 * k)) (wordOf s.mem (kp s₀) (np s₀) k) ∧
      (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have o := (hc (stOff + 4 * k) 4 (by rw [stOff_eq]; omega_using [hk])).2
  have ho : stOff + 4 * k < 2 ^ 15 := by rw [stOff_eq]; omega_using [hk]
  unfold stW stSrc wordOf
  by_cases h₁ : k < 4
  · simp only [h₁, ite_true, List.cons_append, List.nil_append]
    refine wp_lis fun s₁ u₁ => wp_ori fun s₂ u₂ => ?_
    refine wp_stw (a := off (cx s₀) (stOff + 4 * k)) (by decide) ho
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h14]) (by rw [u₂.wr, u₁.wr]; exact o)
      fun s₃ g₃ => WP.block_nil ?_
    refine ⟨by rw [g₃.mem, u₂.gpr, u₂.mem, u₁.gpr, u₁.mem, lis_ori], fun r hr => by
      rw [g₃.gpr, u₂.other r hr, u₁.other r hr], by rw [g₃.rd, u₂.rd, u₁.rd], by rw [g₃.wr, u₂.wr, u₁.wr],
      by rw [g₃.sp, u₂.sp, u₁.sp]⟩
  by_cases h₂ : k < 12
  · simp only [h₁, h₂, ite_true, ite_false, List.cons_append, List.nil_append]
    refine wp_lwz (a := off (kp s₀) (4 * (k - 4))) (by decide) (by omega_using [hk]) (by rw [h3])
      (hp.k_in (by omega_using [h₂]) hrd) fun s₁ u₁ => ?_
    refine wp_stw (a := off (cx s₀) (stOff + 4 * k)) (by decide) ho
      (by rw [u₁.other _ (by decide), h14]) (by rw [u₁.wr]; exact o) fun s₃ g₃ => WP.block_nil ?_
    refine ⟨by rw [g₃.mem, u₁.gpr, u₁.mem, sw32], fun r hr => by rw [g₃.gpr, u₁.other r hr],
      by rw [g₃.rd, u₁.rd], by rw [g₃.wr, u₁.wr], by rw [g₃.sp, u₁.sp]⟩
  by_cases h₃ : k = 12
  · subst h₃
    simp only [ite_true]
    refine wp_li (by decide) fun s₁ u₁ => ?_
    refine wp_stw (a := off (cx s₀) (stOff + 4 * 12)) (by decide) ho
      (by rw [u₁.other _ (by decide), h14]) (by rw [u₁.wr]; exact o) fun s₃ g₃ => WP.block_nil ?_
    refine ⟨by rw [g₃.mem, u₁.gpr, u₁.mem]; rfl, fun r hr => by rw [g₃.gpr, u₁.other r hr],
      by rw [g₃.rd, u₁.rd], by rw [g₃.wr, u₁.wr], by rw [g₃.sp, u₁.sp]⟩
  · simp only [h₁, h₂, h₃, ite_false, List.cons_append, List.nil_append]
    refine wp_lwz (a := off (np s₀) (4 * (k - 13))) (by decide) (by omega_using [hk]) (by rw [h4])
      (hp.n_in (by omega_using [hk]) hrd) fun s₁ u₁ => ?_
    refine wp_stw (a := off (cx s₀) (stOff + 4 * k)) (by decide) ho
      (by rw [u₁.other _ (by decide), h14]) (by rw [u₁.wr]; exact o) fun s₃ g₃ => WP.block_nil ?_
    refine ⟨by rw [g₃.mem, u₁.gpr, u₁.mem, sw32], fun r hr => by rw [g₃.gpr, u₁.other r hr],
      by rw [g₃.rd, u₁.rd], by rw [g₃.wr, u₁.wr], by rw [g₃.sp, u₁.sp]⟩

/-- A frame of `ctx[k, k + n)` is one of the context. -/
theorem frame_ctx {s₀ : State} {m m' : Mem} {k n : Nat} (hf : Frame [sub s₀ k n] m m') (h : k + n ≤ 656) :
    Frame [ctxR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨ctxR s₀, List.mem_singleton_self _, sub_ctx s₀ h⟩

/-- Words outside the context are unchanged by a frame of the context. -/
theorem readW_out {s₀ : State} {m m' : Mem} (hf : Frame [ctxR s₀] m m') {p : Addr} {n : Nat}
    (hd : (ctxR s₀).Disjoint ⟨p, n⟩) {a : Nat} (ha : a + 4 ≤ n) :
    m'.readW (off p a) 32 = m.readW (off p a) 32 :=
  hf.readW (r := ⟨off p a, 4⟩) (Region.contains_self _ _)
    (by simp only [List.mem_singleton, forall_eq]; exact (hd.sub_right (Offset.sub_base p (d := a) (n := 4) ha)).symm)
    (by decide)

theorem wordOf_frame {s₀ : State} (hp : APre e s₀) {m m' : Mem} (hf : Frame [ctxR s₀] m m') {k : Nat}
    (hk : k < 16) :
    wordOf m' (kp s₀) (np s₀) k = wordOf m (kp s₀) (np s₀) k := by
  unfold wordOf
  by_cases h₁ : k < 4
  · simp only [h₁, ite_true]
  by_cases h₂ : k < 12
  · simp only [h₁, h₂, ite_true, ite_false]; exact readW_out hf hp.k_c.symm (by omega_using [h₂])
  by_cases h₃ : k = 12
  · subst h₃; simp only [h₁, h₂, ite_true, ite_false]
  · simp only [h₁, h₂, h₃, ite_false]; exact readW_out hf hp.n_c.symm (by omega_using [hk])

theorem initState_step (j : Nat) : (List.range (j + 1)).flatMap stW = (List.range j).flatMap stW ++ stW j := by
  simp [List.range_succ, List.flatMap_append]

/-- The first `j` words of the ChaCha20 state. -/
theorem initState_ok {s₀ : State} (hp : APre e s₀) {j : Nat} (hj : j ≤ 16) {s : State}
    (h14 : s.gpr .r24 = cx s₀) (h3 : s.gpr .r3 = kp s₀) (h4 : s.gpr .r4 = np s₀) (hrd : s.rd = s₀.rd)
    (hc : CtxOk s₀ s) :
    WP isa (.block ((List.range j).flatMap stW)) s fun s' =>
      (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [sub s₀ stOff (4 * j)] s.mem s'.mem ∧
      ∀ i < j, s'.mem.readW (off (cx s₀) (stOff + 4 * i)) 32 = wordOf s.mem (kp s₀) (np s₀) i := by
  induction j with
  | zero =>
    exact WP.block_nil (M := isa) ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun i hi => absurd hi (by omega_using [])⟩
  | succ j ih =>
    rw [initState_step]
    refine WP.block_append (WP.mono (ih (by omega_using [hj])) fun s₁ ⟨g₁, rd₁, wr₁, sp₁, f₁, w₁⟩ => ?_)
    have hc₁ : CtxOk s₀ s₁ := by rw [CtxOk, rd₁, wr₁]; exact hc
    refine WP.mono (stW_ok hp (by omega_using [hj]) (by rw [g₁ _ (by decide), h14]) (by rw [g₁ _ (by decide), h3])
      (by rw [g₁ _ (by decide), h4]) (by rw [rd₁, hrd]) hc₁)
      fun s₂ ⟨m₂, g₂, rd₂, wr₂, sp₂⟩ => ?_
    refine ⟨fun r hr => by rw [g₂ r hr, g₁ r hr], by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [sp₂, sp₁],
      ?_, fun i hi => ?_⟩
    · rw [m₂]
      refine (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _ ?_
      · simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_using [])
      · exact contains_sub s₀ (w := 32 / 8) (by omega_using []) (by omega_using []) (by rw [stOff_eq]; omega_using [hj])
    · rw [m₂, wordOf_frame hp (frame_ctx f₁ (by rw [stOff_eq]; omega_using [hj])) (k := j) (by omega_using [hj])]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [readW_writeW_off _ _ _ (by rw [stOff_eq]; omega_arith) (by rw [stOff_eq]; omega_using [hj]) (by omega_using [hi])]
        exact w₁ i hi
      · exact Mem.readW_writeW_self32 _ _ _

theorem consts_eq : ∀ i < 4, consts.getD i 0 = Spec.ChaCha20.constants.getD i 0 := by decide +kernel

/-- The words stored are the initial ChaCha20 state for the key, counter 0
and the nonce, if the key and the nonce are as on entry. -/
theorem stateAt_initState {s₀ : State} (hp : APre e s₀) {m₁ m' : Mem} (hf₁ : Frame [ctxR s₀] s₀.mem m₁)
    (hw : ∀ i < 16, m'.readW (off (cx s₀) (stOff + 4 * i)) 32 = wordOf m₁ (kp s₀) (np s₀) i) :
    stateAt m' (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Spec.ChaCha20.initState, Vector.getElem_ofFn]
  rw [off_add, hw i hi, wordOf_frame hp hf₁ hi]
  unfold wordOf
  by_cases h₁ : i < 4
  · simp only [h₁, ite_true]; exact consts_eq i h₁
  by_cases h₂ : i < 12
  · simp only [h₁, h₂, ite_true, ite_false]
    rw [show (K s₀) = Spec.ChaCha20.bytesAt s₀.mem (kp s₀) 32 from rfl,
      wordLE_bytesAt s₀.mem (kp s₀) (n := 32) (j := i - 4) (by omega_using [h₂])]
  by_cases h₃ : i = 12
  · subst h₃; simp only [h₁, h₂, ite_true, ite_false]
  · simp only [h₁, h₂, h₃, ite_false]
    rw [show (N s₀) = Spec.ChaCha20.bytesAt s₀.mem (np s₀) 12 from rfl,
      wordLE_bytesAt s₀.mem (np s₀) (n := 12) (j := i - 13) (by omega_using [hi])]

/-! ## The first block -/

/-- After the first block: the registers saved and moved, and the ChaCha20
state. -/
structure Post1 (s₀ : State) (s : State) : Prop where
  inv : Inv s₀ s
  st : stateAt s.mem (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)
  fctx : Frame [ctxR s₀] s₀.mem s.mem

/-- The first block of both functions. -/
theorem block1_ok {s₀ : State} (hp : APre e s₀) :
    WP isa (.block (save ++ moves ++ initState)) s₀ (Post1 s₀) := by
  refine saveMoves_ok hp fun s₁ rg og h3 h4 sp rd wr sv f₁ => ?_
  have i₁ : Inv s₀ s₁ := ⟨rg, fun r hr hne => og r hne (ne_of_pres hr), sp, rd, wr, sv, f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨ctxR s₀, List.mem_cons_self, sub_ctx s₀ (by decide)⟩⟩
  have hf₁ := frame_ctx f₁ (by decide)
  refine WP.mono (initState_ok hp (j := 16) (Nat.le_refl _) rg.r24 h3 h4 rd (Inv.ctxOk hp rd wr))
    fun s₂ ⟨g₂, rd₂, wr₂, sp₂, f₂, w₂⟩ => ⟨?_, ?_, hf₁.trans (frame_ctx f₂ (by decide))⟩
  · exact i₁.step1 ⟨fun r hr => g₂ r (ne_of_pres hr), sp₂, rd₂, wr₂, f₂⟩ (by decide) (by decide)
  · exact stateAt_initState hp hf₁ w₂

/-! ## The one-time key -/

/-- `r3 = ctx + stOff`, `r4 = ctx`. -/
theorem kgA_ok {s₀ s : State} (h : Inv s₀ s) :
    WP isa (.block [.addi .r3 .r24 stOff, mov .r4 .r24]) s fun s' =>
      s'.gpr .r3 = off (cx s₀) stOff ∧ s'.gpr .r4 = cx s₀ ∧ Kept [] s s' :=
  wp_addi (by decide) (by decide) fun s₁ u₁ => wp_mov fun s₂ u₂ => WP.block_nil
    ⟨by rw [u₂.other _ (by decide), u₁.gpr, h.regs.r24], by rw [u₂.gpr, u₁.other _ (by decide), h.regs.r24],
      ⟨fun r hr => by rw [u₂.other r (ne_of_pres hr), u₁.other r (ne_of_pres hr)], by rw [u₂.sp, u₁.sp],
        by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.mem, u₁.mem]; exact Frame.refl _ _⟩⟩

/-- After the one-time key is computed. -/
structure PostK (s₀ : State) (s : State) : Prop where
  inv : Inv s₀ s
  st : stateAt s.mem (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)
  key : bytesAt s.mem (off (cx s₀) keyOff) 32 = otk s₀

theorem keyGen_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Post1 s₀ s) :
    WP isa keyGen s fun s' => PostK s₀ s' ∧ Frame [sub s₀ 0 256, sub s₀ keyOff 32] s.mem s'.mem := by
  unfold keyGen
  refine WP.seq (WP.mono (kgA_ok h.inv) fun s₁ ⟨h3, h4, k₁⟩ => ?_)
  have i₁ := h.inv.step0 k₁
  have m₁ := k₁.mem_eq
  have dj : (⟨cx s₀, 256⟩ : Region).Disjoint ⟨off (cx s₀) stOff, 64⟩ := by
    rw [← sub_zero s₀ 256]; exact sub_disj s₀ (by decide) (by decide) (by decide)
  have cv : Covers ([(⟨off (cx s₀) stOff, 64⟩ : Region)] ++ [⟨cx s₀, 256⟩]) (s₁.rd ++ s₁.wr) := by
    rw [← sub_zero s₀ 256]; exact covers2 hp i₁.wr (by decide) (by decide)
  have cw : Covers [(⟨cx s₀, 256⟩ : Region)] s₁.wr := by
    rw [← sub_zero s₀ 256]; exact covers1 hp i₁.wr (by decide)
  refine WP.seq (block_call h3 h4 dj cv cw fun s₂ k₂ blk₂ => ?_)
  rw [← sub_zero s₀ 256] at k₂
  have i₂ := i₁.step1 k₂ (by decide) (by decide)
  refine WP.mono (copyWords_ok (a := 0) (b := keyOff) (n := 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) i₂.regs.r24 (Inv.ctxOk hp i₂.rd i₂.wr))
    fun s₃ ⟨g₃, rd₃, wr₃, sp₃, f₃, w₃⟩ => ?_
  have hk₃ : Kept [sub s₀ keyOff (8 * 4)] s₂ s₃ := ⟨fun r hr => g₃ r (ne_of_pres hr), sp₃, rd₃, wr₃, f₃⟩
  refine ⟨⟨i₂.step1 hk₃ (by decide) (by decide), ?_, ?_⟩, ?_⟩
  · -- The ChaCha20 state is outside both writes.
    rw [stateAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact sub_disj s₀ (by decide) (by decide) (by decide)),
      stateAt_frame k₂.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact sub_disj s₀ (a := stOff) (n := 64) (b := 0) (m := 256) (by decide) (by decide)
          (by decide)), m₁, h.st]
  · have e : bytesAt s₃.mem (off (cx s₀) keyOff) (8 * 4) = bytesAt s₂.mem (off (cx s₀) 0) (8 * 4) :=
      bytes_of_dwords fun k hk => by rw [off_add, off_add]; exact w₃ k hk
    rw [show (32 : Nat) = 8 * 4 from rfl, e, off_zero, bytesAt_serialize _ _ (by decide), blk₂, m₁, h.st]
    rfl
  · refine (k₁.frame.sub fun _ hr => absurd hr List.not_mem_nil).trans ((k₂.frame.sub fun r hr => ?_).trans ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact f₃.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩

/-! ## The Poly1305 state -/

/-- `r3 = ctx`, `r4 = ctx + keyOff`. -/
theorem piA_ok {s₀ s : State} (h : Inv s₀ s) :
    WP isa (.block [mov .r3 .r24, .addi .r4 .r24 keyOff]) s fun s' =>
      s'.gpr .r3 = cx s₀ ∧ s'.gpr .r4 = off (cx s₀) keyOff ∧ Kept [] s s' :=
  wp_mov fun s₁ u₁ => wp_addi (by decide) (by decide) fun s₂ u₂ => WP.block_nil
    ⟨by rw [u₂.other _ (by decide), u₁.gpr, h.regs.r24], by rw [u₂.gpr, u₁.other _ (by decide), h.regs.r24],
      ⟨fun r hr => by rw [u₂.other r (ne_of_pres hr), u₁.other r (ne_of_pres hr)], by rw [u₂.sp, u₁.sp],
        by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.mem, u₁.mem]; exact Frame.refl _ _⟩⟩

theorem polyInit_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s)
    (hkey : bytesAt s.mem (off (cx s₀) keyOff) 32 = otk s₀) :
    WP isa polyInit s fun s' => Inv s₀ s' ∧ Kept [sub s₀ 0 128] s s' ∧ Repr s'.mem (cx s₀) (otk s₀) [] := by
  unfold polyInit
  refine WP.seq (WP.mono (piA_ok h) fun s₁ ⟨h3, h4, k₁⟩ => ?_)
  have i₁ := h.step0 k₁
  have dj : (⟨cx s₀, 128⟩ : Region).Disjoint ⟨off (cx s₀) keyOff, 32⟩ := by
    rw [← sub_zero s₀ 128]; exact sub_disj s₀ (by decide) (by decide) (by decide)
  have cv : Covers ([(⟨off (cx s₀) keyOff, 32⟩ : Region)] ++ [⟨cx s₀, 128⟩]) (s₁.rd ++ s₁.wr) := by
    rw [← sub_zero s₀ 128]; exact covers2 hp i₁.wr (by decide) (by decide)
  have cw : Covers [(⟨cx s₀, 128⟩ : Region)] s₁.wr := by
    rw [← sub_zero s₀ 128]; exact covers1 hp i₁.wr (by decide)
  refine init_call h3 h4 dj cv cw fun s₂ k₂ repr₂ => ?_
  rw [← sub_zero s₀ 128] at k₂
  refine ⟨i₁.step1 k₂ (by decide) (by decide), (k₁.sub fun _ hr => absurd hr List.not_mem_nil).trans k₂, ?_⟩
  rw [k₁.mem_eq, hkey] at repr₂
  exact repr₂

end VG.Proof.ChaCha20Poly1305.PPC64LE

end

end

/-! ### `ChaCha20Poly1305.PPC64LE.Mac`, which this module and modules that import it used -/

section

/-!
# ChaCha20-Poly1305 on PPC64LE: absorbing padded data

`macPad p n` absorbs the `n` bytes at `p` into the Poly1305 state (at `ctx`),
and zeros to a multiple of 16: `msg ++ x ++ pad16 x`.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.PPC64LE

open VG VG.PPC64LE VG.Impl.ChaCha20Poly1305.PPC64LE
open VG.Impl.ChaCha20.PPC64LE.Xor (mov)
open VG.Spec.Poly1305 (Repr bytesAt)
open VG.Spec.ChaCha20Poly1305 (pad16)

variable {e : Bool}

theorem padOff_eq : padOff = 416 := rfl

/-! ## Numbers -/

theorem toNat64 {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem ofNat_beq_zero {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x == 0) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h0; rw [← toNat64 h, h0]; rfl
  · intro hx; subst hx; rfl

theorem ofNat_bne_zero {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x != 0) = decide (x ≠ 0) := by
  rw [bne, ofNat_beq_zero h]; by_cases hx : x = 0 <;> simp [hx]

theorem ofNat_shr {x : Nat} (h : x < 2 ^ 64) : BitVec.ofNat 64 x >>> 4 = BitVec.ofNat 64 (x / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat64 h, toNat64 (by omega_arith), Nat.shiftRight_eq_div_pow]

theorem off_toNat (p : Addr) {d : Nat} (h : p.toNat + d < 2 ^ 64) : (off p d).toNat = p.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith

/-! ## What `macPad` keeps -/

/-- The Poly1305 state, the padded block, and `vg_poly1305_blocks`'s frame. -/
abbrev macR (s₀ : State) : List Region := [sub s₀ 0 128, sub s₀ padOff 16, belR s₀]

theorem kept_mac0 {s₀ s s' : State} (hk : Kept [] s s') : Kept (macR s₀) s s' :=
  hk.sub fun _ hr => absurd hr List.not_mem_nil

theorem kept_macP {s₀ s s' : State} (hk : Kept [sub s₀ padOff 16] s s') : Kept (macR s₀) s s' :=
  hk.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩

theorem kept_macB {s₀ s s' : State} (hk : Kept [sub s₀ 0 128, belR s₀] s s') : Kept (macR s₀) s s' :=
  hk.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩

theorem mac_inv {s₀ s s' : State} (hp : APre e s₀) (h : Inv s₀ s) (hk : Kept (macR s₀) s s') : Inv s₀ s' :=
  h.step hk (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨ctxR s₀, List.mem_cons_self, sub_ctx s₀ (by decide)⟩
      · exact ⟨ctxR s₀, List.mem_cons_self, sub_ctx s₀ (by decide)⟩
      · exact ⟨belR s₀, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_disj s₀ (by decide) (by decide) (by decide)
      · exact sub_disj s₀ (by decide) (by decide) (by decide)
      · exact (hp.b_c.sub_right (sub_ctx s₀ (by decide))).symm)

/-! ## Absorbing whole blocks -/

/-- `n` blocks at `p` absorbed, from `r4 = p` and `r5 = n`. -/
theorem absorb_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) {p : Addr} {n : Nat}
    (h4 : s.gpr .r4 = p) (h5 : s.gpr .r5 = BitVec.ofNat 64 n) (hn : 16 * n < 2 ^ 64)
    (hdj : (sub s₀ 0 128).Disjoint ⟨p, 16 * n⟩) (hbp : (belR s₀).Disjoint ⟨p, 16 * n⟩)
    (hfit : p.toNat + 16 * n ≤ 2 ^ 64) (hc : Covers [⟨p, 16 * n⟩] (s₀.rd ++ s₀.wr)) :
    WP isa absorb s fun s' => Inv s₀ s' ∧ Kept (macR s₀) s s' ∧
      ∀ key msg, Repr s.mem (cx s₀) key msg → Repr s'.mem (cx s₀) key (msg ++ bytesAt s.mem p (16 * n)) := by
  unfold absorb
  refine WP.seq (wp_mov fun s₁ u₁ => WP.block_nil ?_)
  obtain k₁ : Kept [] s s₁ :=
    ⟨fun r hr => u₁.other r (ne_of_pres hr), u₁.sp, u₁.rd, u₁.wr, by rw [u₁.mem]; exact Frame.refl _ _⟩
  obtain i₁ := h.step0 k₁
  have hsp : s₁.sp = s₀.sp := i₁.sp
  obtain hbP : (⟨s₁.sp - 160, 160⟩ : Region).Disjoint ⟨cx s₀, 128⟩ := by
    rw [hsp, ← sub_zero s₀ 128]; exact hp.b_c.sub_right (sub_ctx s₀ (by decide))
  obtain hP : (cx s₀).toNat + 128 ≤ 2 ^ 64 := by have := hp.fit_c; omega_arith
  obtain cv : Covers ([(⟨p, 16 * n⟩ : Region)] ++ [⟨cx s₀, 128⟩]) (s₁.rd ++ s₁.wr) := by
    intro a w ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [i₁.rd, i₁.wr]; exact hc a w ⟨_, List.mem_singleton_self _, hcn⟩
    · rw [← sub_zero s₀ 128] at hcn
      exact covers_right (covers1 hp i₁.wr (a := 0) (n := 128) (by decide)) a w
        ⟨_, List.mem_singleton_self _, hcn⟩
  obtain cw : Covers [(⟨cx s₀, 128⟩ : Region)] s₁.wr := by
    rw [← sub_zero s₀ 128]; exact covers1 hp i₁.wr (by decide)
  refine blocks_call (P := cx s₀) (p := p) (n := n) (by rw [u₁.gpr, h.regs.r24])
    (by rw [u₁.other _ (by decide), h4]) (by rw [u₁.other _ (by decide), h5]) hn
    (by rw [hsp]; exact hp.sp160) (by rw [← sub_zero s₀ 128]; exact hdj) hbP (by rw [hsp]; exact hbp)
    hP hfit cv cw fun s₂ k₂ repr₂ => ?_
  rw [← sub_zero s₀ 128, hsp] at k₂
  obtain k₁₂ : Kept (macR s₀) s s₂ := (kept_mac0 k₁).trans (kept_macB k₂)
  exact ⟨mac_inv hp h k₁₂, k₁₂, fun key msg hr => by
    rw [← k₁.mem_eq]; exact repr₂ key msg (by rw [k₁.mem_eq]; exact hr)⟩

/-! ## Zeroing the padded block -/

theorem writeW64_zero_apply (m : Mem) (a x : Addr) :
    (m.writeW a (0 : BitVec 64)) x = if (x - a).toNat < 8 then 0 else m x := by
  simp only [Mem.writeW, Mem.write]
  split
  · simp
  · rfl

theorem padZ_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block [.li .r11 0, .store .d .r11 .r24 padOff, .store .d .r11 .r24 (padOff + 8),
      .addi .r6 .r24 padOff]) s fun s' =>
      s'.gpr .r6 = off (cx s₀) padOff ∧ (∀ r, r ≠ .r11 → r ≠ .r6 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [sub s₀ padOff 16] s.mem s'.mem ∧ ∀ j < 16, s'.mem (off (cx s₀) (padOff + j)) = 0 := by
  have h14 := h.regs.r24
  refine wp_li (by decide) fun s₁ u₁ => ?_
  refine wp_std (a := off (cx s₀) padOff) (by decide) (by decide) (by rw [u₁.other _ (by decide), h14])
    (by rw [u₁.wr, h.wr]; exact hp.in_ctx (by decide)) fun s₂ g₂ => ?_
  refine wp_std (a := off (cx s₀) (padOff + 8)) (by decide) (by decide)
    (by rw [g₂.gpr, u₁.other _ (by decide), h14]) (by rw [g₂.wr, u₁.wr, h.wr]; exact hp.in_ctx (by decide))
    fun s₃ g₃ => ?_
  refine wp_addi (by decide) (by decide) fun s₄ u₄ => WP.block_nil ?_
  have x11 : s₁.gpr .r11 = 0 := u₁.gpr
  obtain hm : s₄.mem = (s.mem.writeW (off (cx s₀) padOff) (0 : BitVec 64)).writeW
      (off (cx s₀) (padOff + 8)) (0 : BitVec 64) := by
    rw [u₄.mem, g₃.mem, g₂.gpr, g₂.mem, u₁.mem, x11]
  refine ⟨by rw [u₄.gpr, g₃.gpr, g₂.gpr, u₁.other _ (by decide), h14], fun r h₁ h₂ => by
      rw [u₄.other _ h₂, g₃.gpr, g₂.gpr, u₁.other _ h₁],
    by rw [u₄.rd, g₃.rd, g₂.rd, u₁.rd], by rw [u₄.wr, g₃.wr, g₂.wr, u₁.wr],
    by rw [u₄.sp, g₃.sp, g₂.sp, u₁.sp], ?_, fun j hj => ?_⟩
  · rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (contains_sub s₀ (w := 64 / 8) (by omega_arith) (by omega_arith) (by decide))).writeW
      (List.mem_singleton_self _) _ (contains_sub s₀ (w := 64 / 8) (by omega_arith) (by omega_arith) (by decide))
  · rw [hm, writeW64_zero_apply]
    by_cases hj8 : 8 ≤ j
    · rw [ite_eq_left (by rw [Offset.sub_toNat _ (by omega_arith) (by rw [padOff_eq]; omega_arith)]; omega_arith)]
    · rw [ite_eq_right (by rw [Offset.sub_toNat' _ (by rw [padOff_eq]; omega_arith) (by rw [padOff_eq]; omega_arith)]; split <;> omega_arith),
        writeW64_zero_apply,
        ite_eq_left (by rw [Offset.sub_toNat _ (by omega_arith) (by rw [padOff_eq]; omega_arith)]; omega_arith)]

/-! ## Copying the last bytes -/

/-- Before byte `i` of the last `t` bytes at `Q` is copied into the padded
block, from the state `s₂` after the block was zeroed. -/
structure CpInv (s₀ s₂ : State) (Q : Addr) (t i : Nat) (s : State) : Prop where
  r4 : s.gpr .r4 = Q + BitVec.ofNat 64 i
  r6 : s.gpr .r6 = off (cx s₀) (padOff + i)
  r12 : s.gpr .r12 = BitVec.ofNat 64 (t - i)
  keep : ∀ r ∈ preserved, s.gpr r = s₂.gpr r
  sp : s.sp = s₂.sp
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  frame : Frame [sub s₀ padOff 16] s₂.mem s.mem
  buf : ∀ j < 16, s.mem (off (cx s₀) (padOff + j)) = if j < i then s₂.mem (Q + BitVec.ofNat 64 j) else 0

def copyBody : List Instr :=
  [.lbz .r11 .r4 0, .stb .r11 .r6 0, .addi .r4 .r4 1, .addi .r6 .r6 1, .subi .r12 .r12 1]

theorem copyLoop_eq : copyLoop = .loop (.block copyBody) (.nonzero .d .r12) := rfl

theorem byte_rt (b : Byte) : ((b.setWidth 64).setWidth 8 : Byte) = b := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

theorem sub_toNat_lt_one (x a : Addr) : (x - a).toNat < 1 ↔ x = a := by
  constructor
  · intro h
    obtain h0 : x - a = 0 := BitVec.eq_of_toNat_eq (by rw [show (0 : Addr).toNat = 0 from rfl]; omega_arith)
    calc x = x - a + a := (BitVec.sub_add_cancel x a).symm
      _ = a := by rw [h0]; exact BitVec.zero_add a
  · rintro rfl; simp

theorem writeW8_apply (m : Mem) (a x : Addr) (v : BitVec 8) :
    (m.writeW a v) x = if x = a then v else m x := by
  by_cases h : x = a
  · subst h; simp [Mem.writeW, Mem.write]
  · simp only [Mem.writeW, Mem.write, Nat.reduceDiv, sub_toNat_lt_one, h, ite_false]

theorem sub_one {a : Nat} (h : 0 < a) : BitVec.ofNat 64 a - BitVec.ofNat 64 1 = BitVec.ofNat 64 (a - 1) :=
  Offset.ofNat_sub_ofNat h

theorem copy_step {s₀ : State} (hp : APre e s₀) {s₂ : State} {Q : Addr} {t : Nat} (ht : t < 16)
    (hwr : s₂.wr = s₀.wr)
    (hsrc : ∀ j < t, InRegions (s₂.rd ++ s₂.wr) (Q + BitVec.ofNat 64 j) 1)
    (hdisj : ∀ j < t, (⟨Q + BitVec.ofNat 64 j, 1⟩ : Region).Disjoint (sub s₀ padOff 16))
    {i : Nat} (hi : i < t) {s : State} (h : CpInv s₀ s₂ Q t i s) :
    WP isa (.block copyBody) s fun s' => CpInv s₀ s₂ Q t (i + 1) s' := by
  obtain hin : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 i) 1 := by
    rw [h.rd, h.wr]; exact hsrc i hi
  obtain hout : InRegions s.wr (off (cx s₀) (padOff + i)) 1 := by
    rw [h.wr, hwr]; exact hp.in_ctx (by rw [padOff_eq]; omega_arith)
  unfold copyBody
  refine wp_lbz (a := Q + BitVec.ofNat 64 i) (by decide) (by decide)
    (by rw [h.r4]; exact BitVec.add_zero _) hin fun s₁ u₁ => ?_
  refine wp_stb (a := off (cx s₀) (padOff + i)) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), h.r6]; exact BitVec.add_zero _) (by rw [u₁.wr]; exact hout)
    fun s₂' g₂ => ?_
  refine wp_addi (by decide) (by decide) fun s₃ u₃ => wp_addi (by decide) (by decide) fun s₄ u₄ =>
    wp_subi (by decide) (by decide) fun s₅ u₅ => WP.block_nil ?_
  obtain hm : s₅.mem = s.mem.writeW (off (cx s₀) (padOff + i)) (s.mem (Q + BitVec.ofNat 64 i)) := by
    rw [u₅.mem, u₄.mem, u₃.mem, g₂.mem, u₁.gpr, u₁.mem, byte_rt]
  refine ⟨?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, fun k hk => ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.r4,
      BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r6,
      off_add, Nat.add_assoc]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r12,
      sub_one (by omega_arith), Nat.sub_sub]
  · rw [u₅.other _ (ne_of_pres hr), u₄.other _ (ne_of_pres hr), u₃.other _ (ne_of_pres hr), g₂.gpr,
      u₁.other _ (ne_of_pres hr), h.keep r hr]
  · rw [u₅.sp, u₄.sp, u₃.sp, g₂.sp, u₁.sp, h.sp]
  · rw [u₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd, h.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr, h.wr]
  · rw [hm]
    exact h.frame.writeW (List.mem_singleton_self _) _
      (contains_sub s₀ (w := 8 / 8) (by omega_arith) (by omega_arith) (by decide))
  · have hbyte : s.mem (Q + BitVec.ofNat 64 i) = s₂.mem (Q + BitVec.ofNat 64 i) :=
      h.frame _ fun r hr hc => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hdisj i hi _ (by simp only [Region.Contains]; rw [BitVec.sub_self]; simp) hc
    rw [hm, writeW8_apply]
    by_cases hki : k = i
    · subst hki
      simp only [ite_true, show k < k + 1 by omega_arith, hbyte]
    · rw [ite_eq_right (Offset.add_ofNat_ne (cx s₀) (by rw [padOff_eq]; omega_arith) (by rw [padOff_eq]; omega_arith)
        (by omega_arith)), h.buf k hk]
      by_cases hk' : k < i
      · simp [hk', show k < i + 1 by omega_arith]
      · simp [hk', show ¬ k < i + 1 by omega_arith]

/-- The padded block's bytes. -/
theorem padded_bytes {s₀ : State} {m mz : Mem} {Q : Addr} {t : Nat} (ht : t < 16)
    (h : ∀ j < 16, m (off (cx s₀) (padOff + j)) = if j < t then mz (Q + BitVec.ofNat 64 j) else 0) :
    bytesAt m (off (cx s₀) padOff) 16 = bytesAt mz Q t ++ List.replicate (16 - t) 0 := by
  apply List.ext_getElem
  · simp [bytesAt]; omega_arith
  · intro k h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [off_add, h k h₁]
    by_cases hk : k < t
    · rw [List.getElem_append_left (by simp [hk])]
      simp [hk]
    · rw [List.getElem_append_right (by simp; omega_arith)]
      simp [hk]

theorem padTail_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) {Q : Addr} {t : Nat}
    (ht0 : 0 < t) (ht : t < 16) (h4 : s.gpr .r4 = Q) (h12 : s.gpr .r12 = BitVec.ofNat 64 t)
    (hsrc : ∀ j < t, InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 j) 1)
    (hdisj : ∀ j < t, (⟨Q + BitVec.ofNat 64 j, 1⟩ : Region).Disjoint (sub s₀ padOff 16)) :
    WP isa padTail s fun s' => Inv s₀ s' ∧ Kept (macR s₀) s s' ∧
      ∀ key msg, Repr s.mem (cx s₀) key msg →
        Repr s'.mem (cx s₀) key (msg ++ (bytesAt s.mem Q t ++ List.replicate (16 - t) 0)) := by
  unfold padTail
  refine WP.seq (WP.mono (padZ_ok hp h) fun s₂ ⟨r6₂, g₂, rd₂, wr₂, sp₂, f₂, z₂⟩ => ?_)
  obtain src₂ : ∀ j < t, s₂.mem (Q + BitVec.ofNat 64 j) = s.mem (Q + BitVec.ofNat 64 j) :=
    fun j hj => f₂ _ fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hdisj j hj _ (by simp only [Region.Contains]; rw [BitVec.sub_self]; simp) hc
  obtain hk₂ : Kept [sub s₀ padOff 16] s s₂ :=
    ⟨fun r hr => g₂ r (ne_of_pres hr) (ne_of_pres hr), sp₂, rd₂, wr₂, f₂⟩
  obtain i₂ := h.step1 hk₂ (by decide) (by decide)
  refine WP.seq (WP.mono (Q := CpInv s₀ s₂ Q t t) ?_ fun s₃ h₃ => ?_)
  · rw [copyLoop_eq]
    let I : Nat → State → Prop := fun n s => ∃ i, n = t - i ∧ i < t ∧ CpInv s₀ s₂ Q t i s
    obtain hstep : ∀ n s, I n s → WP isa (.block copyBody) s (fun s' =>
        (isa.eval (.nonzero .d .r12) s' = some false ∧ CpInv s₀ s₂ Q t t s') ∨
        (isa.eval (.nonzero .d .r12) s' = some true ∧ ∃ n' < n, I n' s')) := by
      rintro n s ⟨i, rfl, hi, hI⟩
      refine WP.mono (copy_step hp ht (by rw [i₂.wr]) (by rw [rd₂, wr₂]; exact hsrc) hdisj hi hI)
        fun s' h' => ?_
      obtain hz : isa.eval (.nonzero .d .r12) s' = some (decide (t - (i + 1) ≠ 0)) := by
        rw [VG.Proof.Poly1305.PPC64LE.eval_nonzero, h'.r12, ofNat_bne_zero (by omega_arith)]
      by_cases hl : i + 1 = t
      · exact .inl ⟨by rw [hz]; simp [hl], hl ▸ h'⟩
      · exact .inr ⟨by rw [hz]; simp; omega_arith, t - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, h'⟩
    exact WP.loop (M := isa) I hstep t s₂ ⟨0, by simp, ht0, ⟨by rw [g₂ _ (by decide) (by decide), h4]; exact (BitVec.add_zero _).symm,
      by rw [r6₂]; rfl, by rw [g₂ _ (by decide) (by decide), h12]; rfl, fun _ _ => rfl, rfl, rfl, rfl,
      Frame.refl _ _, fun j hj => by simp [z₂ j hj]⟩⟩
  obtain hk₃ : Kept [sub s₀ padOff 16] s₂ s₃ := ⟨h₃.keep, h₃.sp, h₃.rd, h₃.wr, h₃.frame⟩
  obtain i₃ := i₂.step1 hk₃ (by decide) (by decide)
  refine WP.seq (wp_addi (by decide) (by decide) fun s₄ u₄ => wp_li (by decide) fun s₅ u₅ => WP.block_nil ?_)
  obtain k₅ : Kept [] s₃ s₅ := ⟨fun r hr => by rw [u₅.other _ (ne_of_pres hr), u₄.other _ (ne_of_pres hr)],
    by rw [u₅.sp, u₄.sp], by rw [u₅.rd, u₄.rd], by rw [u₅.wr, u₄.wr], by rw [u₅.mem, u₄.mem]; exact Frame.refl _ _⟩
  obtain i₅ := i₃.step0 k₅
  obtain hdj : (sub s₀ 0 128).Disjoint ⟨off (cx s₀) padOff, 16 * 1⟩ :=
    sub_disj s₀ (by decide) (by decide) (by decide)
  obtain hbp : (belR s₀).Disjoint ⟨off (cx s₀) padOff, 16 * 1⟩ :=
    hp.b_c.sub_right (sub_ctx s₀ (by decide))
  obtain hfit : (off (cx s₀) padOff).toNat + 16 * 1 ≤ 2 ^ 64 := by
    have := hp.fit_c; rw [off_toNat _ (by rw [padOff_eq]; omega_arith), padOff_eq]; omega_arith
  obtain hc : Covers [(⟨off (cx s₀) padOff, 16 * 1⟩ : Region)] (s₀.rd ++ s₀.wr) :=
    covers_right (covers1 hp rfl (a := padOff) (n := 16 * 1) (by decide))
  refine WP.mono (absorb_ok hp i₅ (n := 1) (by rw [u₅.other _ (by decide), u₄.gpr, i₃.regs.r24])
    (by rw [u₅.gpr]) (by decide) hdj hbp hfit hc)
    fun s₆ ⟨i₆, k₆, repr₆⟩ => ⟨i₆, (kept_macP hk₂).trans ((kept_macP hk₃).trans
      ((kept_mac0 k₅).trans k₆)), fun key msg hr => ?_⟩
  have m₅ := k₅.mem_eq
  obtain hr₅ : Repr s₅.mem (cx s₀) key msg := by
    rw [m₅]
    refine Repr.frame (f₂.trans h₃.frame) (fun r hr => ?_) hr
    simp only [List.mem_singleton] at hr; subst hr
    rw [← sub_zero s₀ 128]; exact sub_disj s₀ (by decide) (by decide) (by decide)
  obtain hb : bytesAt s₅.mem (off (cx s₀) padOff) (16 * 1) =
      bytesAt s.mem Q t ++ List.replicate (16 - t) 0 := by
    rw [m₅, show 16 * 1 = 16 from rfl, padded_bytes ht h₃.buf]
    exact congrArg (· ++ _) (bytesAt_eq_of fun j hj => src₂ j hj)
  have := repr₆ key msg hr₅
  rwa [hb] at this

/-! ## The whole of `macPad` -/

/-- The registers `macPad` may take its arguments in. -/
def MacRegs (p n : Reg) : Prop := (p = .r25 ∧ n = .r26) ∨ (p = .r27 ∧ n = .r28)

/-- Neither is written by `macPad`'s own instructions, and both are callee-saved. -/
structure RegOk (r : Reg) : Prop where
  pres : r ∈ preserved
  r0 : r ≠ .r0
  r4 : r ≠ .r4
  r5 : r ≠ .r5
  r12 : r ≠ .r12

theorem MacRegs.p_ok {p n : Reg} (hr : MacRegs p n) : RegOk p := by
  rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem MacRegs.n_ok {p n : Reg} (hr : MacRegs p n) : RegOk n := by
  rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- What `macPad` needs of the bytes it absorbs. -/
structure Src (s₀ : State) (P : Addr) (len : Nat) : Prop where
  lt : len < 2 ^ 64
  fit : P.toNat + len ≤ 2 ^ 64
  ctx : (ctxR s₀).Disjoint ⟨P, len⟩
  bel : (belR s₀).Disjoint ⟨P, len⟩
  cov : Covers [⟨P, len⟩] (s₀.rd ++ s₀.wr)

/-- The `len` bytes at `P` (in `p` and `n`), padded with zeros, absorbed. -/
theorem macPad_ok {s₀ : State} (hp : APre e s₀) {p n : Reg} (hr : MacRegs p n) {P : Addr} {len : Nat}
    (hs : Src s₀ P len) {s : State} (h : Inv s₀ s) (hP : s.gpr p = P) (hn : s.gpr n = BitVec.ofNat 64 len) :
    WP isa (macPad p n) s fun s' => Inv s₀ s' ∧ Kept (macR s₀) s s' ∧
      ∀ key msg, Repr s.mem (cx s₀) key msg →
        Repr s'.mem (cx s₀) key (msg ++ (bytesAt s.mem P len ++ pad16 (bytesAt s.mem P len))) := by
  have hpn := hr.p_ok
  have hnn := hr.n_ok
  have hlt := hs.lt
  obtain hk : 16 * (len / 16) ≤ len := Nat.mul_div_le _ _
  unfold macPad
  refine WP.seq (wp_mov (hn := hpn.r0) fun s₁ u₁ => wp_lsr (by decide) fun s₂ u₂ => WP.block_nil ?_)
  obtain k₂ : Kept [] s s₂ := ⟨fun r hr => by rw [u₂.other _ (ne_of_pres hr), u₁.other _ (ne_of_pres hr)],
    by rw [u₂.sp, u₁.sp], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.mem, u₁.mem]; exact Frame.refl _ _⟩
  obtain i₂ := h.step0 k₂
  obtain hdj : (sub s₀ 0 128).Disjoint ⟨P, 16 * (len / 16)⟩ :=
    (hs.ctx.sub_left (sub_ctx s₀ (by decide))).sub_right (Region.sub_prefix hk)
  refine WP.seq (WP.mono (absorb_ok hp i₂ (p := P) (n := len / 16) (by rw [u₂.other _ (by decide), u₁.gpr, hP])
    (by rw [u₂.gpr, u₁.other _ hnn.r4, hn, ofNat_shr hlt]) (by omega_arith) hdj
    (hs.bel.sub_right (Region.sub_prefix hk)) (by have := hs.fit; omega_arith)
    (fun a w ⟨r, hr', hc⟩ => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact hs.cov a w ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega_arith⟩))
    fun s₃ ⟨i₃, k₃, repr₃⟩ => ?_)
  have m₂ := k₂.mem_eq
  rw [m₂] at repr₃
  obtain n₃ : s₃.gpr n = BitVec.ofNat 64 len := by rw [k₃.cs n hnn.pres, k₂.cs n hnn.pres, hn]
  obtain p₃ : s₃.gpr p = P := by rw [k₃.cs p hpn.pres, k₂.cs p hpn.pres, hP]
  refine WP.seq (wp_li (by decide) fun s₄ u₄ => wp_and fun s₅ u₅ => WP.block_nil ?_)
  obtain r12₅ : s₅.gpr .r12 = BitVec.ofNat 64 (len % 16) := by
    rw [u₅.gpr, u₄.other _ hnn.r12, u₄.gpr, n₃, VG.Proof.Poly1305.PPC64LE.and15, toNat64 hlt]
  obtain k₅ : Kept [] s₃ s₅ := ⟨fun r hr => by rw [u₅.other _ (ne_of_pres hr), u₄.other _ (ne_of_pres hr)],
    by rw [u₅.sp, u₄.sp], by rw [u₅.rd, u₄.rd], by rw [u₅.wr, u₄.wr], by rw [u₅.mem, u₄.mem]; exact Frame.refl _ _⟩
  obtain i₅ := i₃.step0 k₅
  obtain k₁₅ : Kept (macR s₀) s s₅ := (kept_mac0 k₂).trans (k₃.trans (kept_mac0 k₅))
  obtain x_eq : bytesAt s.mem P len = bytesAt s.mem P (16 * (len / 16)) ++
      bytesAt s.mem (P + BitVec.ofNat 64 (16 * (len / 16))) (len % 16) := by
    rw [← VG.Proof.Poly1305.bytesAt_add, Nat.div_add_mod]
  obtain hlen : (bytesAt s.mem P len).length = len := VG.Proof.Poly1305.length_bytesAt _ _ _
  have m₅ := k₅.mem_eq
  refine WP.ite (decide (len % 16 = 0)) (by
      rw [VG.Proof.Poly1305.PPC64LE.eval_zero, r12₅, ofNat_beq_zero (by omega_arith)]) (fun hb => ?_) (fun hb => ?_)
  · -- A multiple of 16: nothing to pad.
    obtain h0 : len % 16 = 0 := by simpa using hb
    refine WP.block_nil ⟨i₅, k₁₅, fun key msg hr => ?_⟩
    rw [m₅]
    have := repr₃ key msg hr
    rwa [show pad16 (bytesAt s.mem P len) = [] by simp [pad16, hlen, h0], List.append_nil,
      ← show 16 * (len / 16) = len by omega_arith]
  · have h0 : len % 16 ≠ 0 := by simpa using hb
    refine WP.seq (wp_sub fun s₆ u₆ => wp_add fun s₇ u₇ => WP.block_nil ?_)
    obtain k₇ : Kept [] s₅ s₇ := ⟨fun r hr => by rw [u₇.other _ (ne_of_pres hr), u₆.other _ (ne_of_pres hr)],
      by rw [u₇.sp, u₆.sp], by rw [u₇.rd, u₆.rd], by rw [u₇.wr, u₆.wr], by rw [u₇.mem, u₆.mem]; exact Frame.refl _ _⟩
    obtain i₇ := i₅.step0 k₇
    obtain hQ : s₇.gpr .r4 = P + BitVec.ofNat 64 (16 * (len / 16)) := by
      rw [u₇.gpr, u₆.other _ hpn.r4, u₆.gpr, u₅.other _ hpn.r12, u₄.other _ hpn.r12, p₃,
        u₅.other _ hnn.r12, u₄.other _ hnn.r12, n₃, r12₅, Offset.ofNat_sub_ofNat (Nat.mod_le _ _),
        show len - len % 16 = 16 * (len / 16) by omega_arith]
    obtain hsrc : ∀ j < len % 16, InRegions (s₇.rd ++ s₇.wr)
        (P + BitVec.ofNat 64 (16 * (len / 16)) + BitVec.ofNat 64 j) 1 := fun j hj => by
      rw [i₇.rd, i₇.wr, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact hs.cov _ _ ⟨_, List.mem_singleton_self _,
        Offset.contains_base P (d := 16 * (len / 16) + j) (n := 1) (by omega_arith) (by omega_arith)⟩
    obtain hdj' : ∀ j < len % 16, (⟨P + BitVec.ofNat 64 (16 * (len / 16)) + BitVec.ofNat 64 j, 1⟩ :
        Region).Disjoint (sub s₀ padOff 16) := fun j hj => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact ((hs.ctx.sub_left (sub_ctx s₀ (by decide))).sub_right
        (Offset.sub_base P (d := 16 * (len / 16) + j) (n := 1) (by omega_arith))).symm
    refine WP.mono (padTail_ok hp i₇ (Q := P + BitVec.ofNat 64 (16 * (len / 16))) (t := len % 16)
      (by omega_arith) (by omega_arith) hQ (by rw [u₇.other _ (by decide), u₆.other _ (by decide), r12₅]) hsrc hdj')
      fun s₈ ⟨i₈, k₈, repr₈⟩ => ?_
    refine ⟨i₈, k₁₅.trans ((kept_mac0 k₇).trans k₈), fun key msg hr => ?_⟩
    have m₇ := k₇.mem_eq
    have := repr₈ key _ (by rw [m₇, m₅]; exact repr₃ key msg hr)
    rw [m₇, m₅, bytesAt_frame k₃.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ((hs.ctx.sub_left (sub_ctx s₀ (by decide))).sub_right
            (Offset.sub_base P (d := 16 * (len / 16)) (by omega_arith))).symm
        · exact ((hs.ctx.sub_left (sub_ctx s₀ (by decide))).sub_right
            (Offset.sub_base P (d := 16 * (len / 16)) (by omega_arith))).symm
        · exact (hs.bel.sub_right (Offset.sub_base P (d := 16 * (len / 16)) (by omega_arith))).symm) (by omega_arith),
      m₂] at this
    rw [show pad16 (bytesAt s.mem P len) = List.replicate (16 - len % 16) 0 by
      simp [pad16, hlen, h0], x_eq]
    simpa only [List.append_assoc] using this

end VG.Proof.ChaCha20Poly1305.PPC64LE

end

end

/-!
# ChaCha20-Poly1305 on PPC64LE: the other parts

The encryption, the lengths block, the arguments of
`vg_poly1305_finalize_scratch` and the tag, restoring the registers, and
comparing tags.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.PPC64LE

open VG VG.PPC64LE VG.Impl.ChaCha20Poly1305.PPC64LE
open VG.Impl.ChaCha20.PPC64LE.Xor (mov)
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt keystream)

variable {e : Bool}

theorem lenOff_eq : lenOff = 432 := rfl
/-! ## Encrypting -/

theorem set12_initState (key nonce : List Byte) :
    (Spec.ChaCha20.initState key 0 nonce).set 12 1 = Spec.ChaCha20.initState key 1 nonce := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_set, Spec.ChaCha20.initState, Vector.getElem_ofFn]
  by_cases h : 12 = i
  · subst h; simp
  · simp only [h, ite_false, show ¬ i = 12 from fun h' => h h'.symm]

theorem stateAt_writeW_counter (m : Mem) (p : Addr) (v : BitVec 32) :
    stateAt (m.writeW (off p 48) v) p = (stateAt m p).set 12 v := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases h : 12 = i
  · subst h
    simp only [ite_true]
    exact Mem.readW_writeW_self32 _ _ _
  · simp only [h, ite_false]
    exact readW_writeW_off m p v (d := 4 * i) (by omega_using [hi]) (by decide) (by omega_using [h])

theorem cryptA_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block [.li .r12 1, .store .w .r12 .r24 (stOff + 48), .addi .r3 .r24 stOff, mov .r4 .r27,
      mov .r5 .r28, mov .r6 .r24, mov .r7 .r31]) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) (stOff + 48)) (1 : BitVec 32) ∧ s'.gpr .r3 = off (cx s₀) stOff ∧
      s'.gpr .r4 = dp s₀ ∧ s'.gpr .r5 = s₀.gpr .r8 ∧ s'.gpr .r6 = cx s₀ ∧ s'.gpr .r7 = op s₀ ∧
      Kept [sub s₀ (stOff + 48) 4] s s' := by
  have h14 := h.regs.r24
  refine wp_li (by decide) fun s₁ u₁ => ?_
  refine wp_stw (a := off (cx s₀) (stOff + 48)) (by decide) (by decide) (by rw [u₁.other _ (by decide), h14])
    (by rw [u₁.wr, h.wr]; exact hp.in_ctx (by decide)) fun s₂ u₂ => ?_
  refine wp_addi (by decide) (by decide) fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    wp_mov fun s₆ u₆ => wp_mov fun s₇ u₇ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, u₁.mem]; rfl
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.gpr, u₁.other _ (by decide), h14]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.regs.r27]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.regs.r28]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h14]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.regs.r31]
  · refine ⟨fun r hr => ?_, by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp],
      by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd],
      by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr], ?_⟩
    · rw [u₇.other _ (ne_of_pres hr), u₆.other _ (ne_of_pres hr), u₅.other _ (ne_of_pres hr),
        u₄.other _ (ne_of_pres hr), u₃.other _ (ne_of_pres hr), u₂.gpr, u₁.other _ (ne_of_pres hr)]
    · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (contains_sub s₀ (w := 32 / 8) (by omega_using []) (by omega_using []) (by decide))

theorem length_encrypt (key nonce m : List Byte) : (Spec.ChaCha20.encrypt key 1 nonce m).length = m.length := by
  rw [encrypt_eq, List.length_zipWith, VG.Proof.ChaCha20.length_keystream, Nat.min_self]

/-- The source encrypted (or decrypted) to the destination from block
counter 1, with the ChaCha20 state for counter 0 at `ctx + stOff`. -/
theorem crypt_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s)
    (hst : stateAt s.mem (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)) :
    WP isa crypt s fun s' => Inv s₀ s' ∧ Kept [sub s₀ 0 (stOff + 64), oR s₀] s s' ∧
      bytesAt s'.mem (op s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) := by
  unfold crypt
  refine WP.seq (WP.mono (cryptA_ok hp h) fun s₁ ⟨m₁, h3, h4, h5, h6, h7, k₁⟩ => ?_)
  have i₁ := h.step1 k₁ (by decide) (by decide)
  have hw : Covers [⟨off (cx s₀) stOff, 64⟩, ⟨op s₀, L s₀⟩, ⟨cx s₀, 320⟩] s₁.wr := by
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ctxR s₀, by rw [i₁.wr]; exact hp.ctx_wr, stOff, rfl, by exact (by decide : stOff + 64 ≤ 656)⟩
    · exact ⟨oR s₀, by rw [i₁.wr]; exact hp.o_wr, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨ctxR s₀, by rw [i₁.wr]; exact hp.ctx_wr, 0, (BitVec.add_zero _).symm,
        by exact (by decide : 0 + 320 ≤ 656)⟩
  have hL : s₀.gpr .r8 = BitVec.ofNat 64 (L s₀) := by simp [L]
  have hcv : Covers ([⟨dp s₀, L s₀⟩] ++ [⟨off (cx s₀) stOff, 64⟩, ⟨op s₀, L s₀⟩, ⟨cx s₀, 320⟩])
      (s₁.rd ++ s₁.wr) := by
    intro a m ⟨r, hr, hcr⟩
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨dR s₀, by rw [i₁.rd, i₁.wr]; exact hp.d_in, hcr⟩
    · exact covers_right hw a m ⟨r, hr, hcr⟩
  have hSX : (⟨off (cx s₀) stOff, 64⟩ : Region).Disjoint ⟨dp s₀, L s₀⟩ :=
    hp.d_c.symm.sub_left (sub_ctx s₀ (by decide))
  have hSD : (⟨off (cx s₀) stOff, 64⟩ : Region).Disjoint ⟨op s₀, L s₀⟩ :=
    hp.o_c.symm.sub_left (sub_ctx s₀ (by decide))
  have hSB : (⟨off (cx s₀) stOff, 64⟩ : Region).Disjoint ⟨cx s₀, 320⟩ := by
    rw [← sub_zero s₀ 320]; exact sub_disj s₀ (by decide) (by decide) (by decide)
  have hXB : (⟨dp s₀, L s₀⟩ : Region).Disjoint ⟨cx s₀, 320⟩ := by
    rw [← sub_zero s₀ 320]; exact hp.d_c.sub_right (sub_ctx s₀ (by decide))
  have hDB : (⟨op s₀, L s₀⟩ : Region).Disjoint ⟨cx s₀, 320⟩ := by
    rw [← sub_zero s₀ 320]; exact hp.o_c.sub_right (sub_ctx s₀ (by decide))
  have hXD : op s₀ = dp s₀ ∨ (⟨dp s₀, L s₀⟩ : Region).Disjoint ⟨op s₀, L s₀⟩ := by
    rcases hp.alias with h' | ⟨-, h'⟩
    · exact .inl h'
    · exact .inr h'
  have h5' : s₁.gpr .r5 = BitVec.ofNat 64 (L s₀) := by rw [h5, hL]
  refine xor_call_to h3 h4 h5' h6 h7 (s₀.gpr .r8).isLt hSX hSD hSB hXB hDB hXD hp.fit_d hp.fit_o hcv hw
    fun s₂ k₂ data₂ => ?_
  have hsub : ∀ r ∈ [(⟨off (cx s₀) stOff, 64⟩ : Region), ⟨op s₀, L s₀⟩, ⟨cx s₀, 320⟩],
      ∃ r' ∈ [sub s₀ 0 (stOff + 64), oR s₀], Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, Offset.sub (cx s₀) (by decide) (by decide)⟩
    · exact ⟨oR s₀, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
    · refine ⟨_, List.mem_cons_self, ?_⟩
      rw [← sub_zero s₀ 320]; exact Offset.sub (cx s₀) (by decide) (by decide)
  have k₁₂ : Kept [sub s₀ 0 (stOff + 64), oR s₀] s s₂ :=
    (k₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub (cx s₀) (by decide) (by decide)⟩).trans (k₂.sub hsub)
  have i₂ := h.step k₁₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨ctxR s₀, List.mem_cons_self, sub_ctx s₀ (by decide)⟩
      · exact ⟨oR s₀, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_disj s₀ (by decide) (by decide) (by decide)
      · exact (hp.o_c.sub_right (sub_ctx s₀ (by decide))).symm)
  refine ⟨i₂, k₁₂, ?_⟩
  have d₁ : bytesAt s₁.mem (dp s₀) (L s₀) = bytesAt s.mem (dp s₀) (L s₀) :=
    bytesAt_frame k₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.d_c.sub_right (sub_ctx s₀ (by decide)))
      (Nat.le_of_lt (s₀.gpr .r8).isLt)
  have st₁ : stateAt s₁.mem (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 1 (N s₀) := by
    rw [m₁, show off (cx s₀) (stOff + 48) = off (off (cx s₀) stOff) 48 from (off_off _ _ _).symm,
      stateAt_writeW_counter, hst, set12_initState]
  rw [show Spec.ChaCha20.bytesAt = bytesAt from rfl] at data₂
  rw [data₂, st₁, d₁, encrypt_eq, VG.Proof.Poly1305.length_bytesAt]

/-! ## The lengths block -/

theorem lengthsA_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block [.store .d .r26 .r24 lenOff, .store .d .r28 .r24 (lenOff + 8), .addi .r4 .r24 lenOff,
      .li .r5 1]) s fun s' =>
      s'.gpr .r4 = off (cx s₀) lenOff ∧ s'.gpr .r5 = BitVec.ofNat 64 1 ∧ Kept [sub s₀ lenOff 16] s s' ∧
      bytesAt s'.mem (off (cx s₀) lenOff) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
  have h14 := h.regs.r24
  refine wp_std (a := off (cx s₀) lenOff) (by decide) (by decide) (by rw [h14])
    (by rw [h.wr]; exact hp.in_ctx (by decide)) fun s₁ g₁ => ?_
  refine wp_std (a := off (cx s₀) (lenOff + 8)) (by decide) (by decide) (by rw [g₁.gpr, h14])
    (by rw [g₁.wr, h.wr]; exact hp.in_ctx (by decide)) fun s₂ g₂ => ?_
  refine wp_addi (by decide) (by decide) fun s₃ u₃ => wp_li (by decide) fun s₄ u₄ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · rw [u₄.other _ (by decide), u₃.gpr, g₂.gpr, g₁.gpr, h14]
  · rw [u₄.gpr]
  · refine ⟨fun r hr => by rw [u₄.other _ (ne_of_pres hr), u₃.other _ (ne_of_pres hr), g₂.gpr, g₁.gpr],
      by rw [u₄.sp, u₃.sp, g₂.sp, g₁.sp], by rw [u₄.rd, u₃.rd, g₂.rd, g₁.rd], by rw [u₄.wr, u₃.wr, g₂.wr, g₁.wr], ?_⟩
    rw [u₄.mem, u₃.mem, g₂.mem, g₁.mem]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (contains_sub s₀ (w := 64 / 8) (by omega_using []) (by omega_using []) (by decide))).writeW (List.mem_singleton_self _) _
      (contains_sub s₀ (w := 64 / 8) (by omega_using []) (by omega_using []) (by decide))
  · rw [u₄.mem, u₃.mem, g₂.mem, g₁.mem, g₁.gpr, show (16 : Nat) = 8 + 8 from rfl, VG.Proof.Poly1305.bytesAt_add,
      VG.Proof.Poly1305.bytesAt_leBytes_64, VG.Proof.Poly1305.bytesAt_leBytes_64, off_add,
      readW_writeW_off _ _ _ (d := lenOff) (e := lenOff + 8) (by decide) (by decide) (by decide),
      Mem.readW_writeW_self64, Mem.readW_writeW_self64, h.regs.r26, h.regs.r28]

theorem lengths_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) :
    WP isa lengths s fun s' => Inv s₀ s' ∧ Kept (macR s₀ ++ [sub s₀ lenOff 16]) s s' ∧
      ∀ key msg, Repr s.mem (cx s₀) key msg →
        Repr s'.mem (cx s₀) key (msg ++ (leBytes 8 (AL s₀) ++ leBytes 8 (L s₀))) := by
  unfold lengths
  refine WP.seq (WP.mono (lengthsA_ok hp h) fun s₁ ⟨h4, h5, k₁, len₁⟩ => ?_)
  have i₁ := h.step1 k₁ (by decide) (by decide)
  have hdj : (sub s₀ 0 128).Disjoint ⟨off (cx s₀) lenOff, 16 * 1⟩ := sub_disj s₀ (by decide) (by decide) (by decide)
  have hbp : (belR s₀).Disjoint ⟨off (cx s₀) lenOff, 16 * 1⟩ := hp.b_c.sub_right (sub_ctx s₀ (by decide))
  have hfit : (off (cx s₀) lenOff).toNat + 16 * 1 ≤ 2 ^ 64 := by
    have := hp.fit_c; rw [off_toNat _ (by rw [lenOff_eq]; omega_using [this]), lenOff_eq]; omega_using [this]
  have hc : Covers [(⟨off (cx s₀) lenOff, 16 * 1⟩ : Region)] (s₀.rd ++ s₀.wr) :=
    covers_right (covers1 hp rfl (a := lenOff) (n := 16 * 1) (by decide))
  refine WP.mono (absorb_ok hp i₁ (n := 1) h4 h5 (by decide) hdj hbp hfit hc)
    fun s₂ ⟨i₂, k₂, repr₂⟩ => ⟨i₂, ?_, fun key msg hr => ?_⟩
  · exact (k₁.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩).trans
      (k₂.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩)
  have hr₁ : Repr s₁.mem (cx s₀) key msg := Repr.frame k₁.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [← sub_zero s₀ 128]; exact sub_disj s₀ (by decide) (by decide) (by decide)) hr
  have := repr₂ key msg hr₁
  rwa [show 16 * 1 = 16 from rfl, len₁] at this

/-! ## The arguments of `vg_poly1305_finalize_scratch` -/

/-- `⌈n / 16⌉` into `d`, through `t`: only `d` and `t` change. -/
theorem ceil16_ok {d t n : Reg} {rest : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ d → r ≠ t → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → WP isa (.block rest) s' Q) (ht : t ≠ .r0 := by decide) :
    WP isa (.block (ceil16 d t n ++ rest)) s Q := by
  unfold ceil16
  simp only [List.cons_append, List.nil_append]
  refine wp_lsr (by decide) fun s₁ u₁ => wp_li (by decide) fun s₂ u₂ => wp_and fun s₃ u₃ =>
    wp_addi ht (by decide) fun s₄ u₄ => wp_lsr (by decide) fun s₅ u₅ => wp_add fun s₆ u₆ =>
    k s₆ (fun r h₁ h₂ => ?_) ?_ ?_ ?_ ?_
  · rw [u₆.other r h₁, u₅.other r h₂, u₄.other r h₂, u₃.other r h₂, u₂.other r h₂, u₁.other r h₁]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

theorem shl4_mod (x : BitVec 64) : (x <<< 4).toNat % 16 = 0 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega_using []

/-- The arguments of `vg_poly1305_finalize_scratch`, with `out` set to `O`
by the instruction `out`. -/
theorem finArgs_ok {s₀ : State} {s : State} (h : Inv s₀ s) {out : Instr} {O : Addr}
    (hout : ∀ (t : State) (rest : List Instr) (Q : State → Prop), t.gpr .r24 = cx s₀ →
      t.gpr .r29 = s.gpr .r29 → (∀ t', Upd t t' .r5 O → WP isa (.block rest) t' Q) →
      WP isa (.block (out :: rest)) t Q) :
    WP isa (.block (finalizeArgs out)) s fun s' => Inv s₀ s' ∧ Kept [] s s' ∧ s'.gpr .r3 = cx s₀ ∧
      s'.gpr .r5 = O ∧ s'.gpr .r6 = off (cx s₀) scrOff ∧ (s'.gpr .r4).toNat % 16 = 0 := by
  unfold finalizeArgs
  rw [List.append_assoc]
  refine ceil16_ok fun s₁ g₁ m₁ rd₁ wr₁ sp₁ => ceil16_ok fun s₂ g₂ m₂ rd₂ wr₂ sp₂ => ?_
  have e₂ : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r12 → s₂.gpr r = s.gpr r := fun r a b c => by
    rw [g₂ r b c, g₁ r a c]
  refine wp_add fun s₃ u₃ => wp_addi (by decide) (by decide) fun s₄ u₄ => wp_lsl (by decide) fun s₅ u₅ =>
    wp_mov fun s₆ u₆ => ?_
  have g14 : s₅.gpr .r24 = cx s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      e₂ _ (by decide) (by decide) (by decide), h.regs.r24]
  refine hout s₆ _ _ (by rw [u₆.other _ (by decide), g14])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      e₂ _ (by decide) (by decide) (by decide)])
    fun s₇ u₇ => wp_addi (by decide) (by decide) fun s₈ u₈ => WP.block_nil ?_
  have hk : Kept [] s s₈ := ⟨fun r hr => by
      rw [u₈.other _ (ne_of_pres hr), u₇.other _ (ne_of_pres hr), u₆.other _ (ne_of_pres hr), u₅.other _ (ne_of_pres hr), u₄.other _ (ne_of_pres hr), u₃.other _ (ne_of_pres hr), e₂ r (ne_of_pres hr) (ne_of_pres hr) (ne_of_pres hr)],
    by rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, sp₁], by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, rd₁], by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, wr₁],
    by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂, m₁]; exact Frame.refl _ _⟩
  refine ⟨h.step0 hk, hk, ?_, ?_, ?_, ?_⟩
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g14]
  · rw [u₈.other _ (by decide), u₇.gpr]
  · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), g14]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
    exact shl4_mod _

/-- `seal`'s `out`: `tag`. -/
theorem out_seal {s₀ s : State} (h : Inv s₀ s) :
    ∀ (t : State) (rest : List Instr) (Q : State → Prop), t.gpr .r24 = cx s₀ →
      t.gpr .r29 = s.gpr .r29 → (∀ t', Upd t t' .r5 (tp s₀) → WP isa (.block rest) t' Q) →
      WP isa (.block (mov .r5 .r29 :: rest)) t Q := fun _ _ _ _ t19 k =>
  wp_mov fun t' u => k t' ⟨by rw [u.gpr, t19, h.regs.r29], u.other, u.mem, u.rd, u.wr, u.sp, u.lr⟩

/-- `open`'s `out`: the tag computed, in the context. -/
theorem out_open {s₀ s : State} :
    ∀ (t : State) (rest : List Instr) (Q : State → Prop), t.gpr .r24 = cx s₀ →
      t.gpr .r29 = s.gpr .r29 → (∀ t', Upd t t' .r5 (off (cx s₀) tagOff) → WP isa (.block rest) t' Q) →
      WP isa (.block (.addi .r5 .r24 tagOff :: rest)) t Q := fun _ _ _ t14 _ k =>
  wp_addi (by decide) (by decide) fun t' u => k t' ⟨by rw [u.gpr, t14], u.other, u.mem, u.rd, u.wr, u.sp, u.lr⟩

/-! ## The tag -/

/-- Where `out` may be: 16 writable bytes disjoint from the Poly1305 state,
the working space of `vg_poly1305_finalize_scratch` and the saved registers. -/
structure OutOk (s₀ : State) (O : Addr) : Prop where
  dP : (sub s₀ 0 128).Disjoint ⟨O, 16⟩
  dS : (⟨O, 16⟩ : Region).Disjoint (sub s₀ scrOff 128)
  dSv : (sub s₀ savOff 64).Disjoint ⟨O, 16⟩
  w : ∃ r ∈ s₀.wr, ∃ k, O = r.base + BitVec.ofNat 64 k ∧ k + 16 ≤ r.len

/-- `open`'s tag computed. -/
theorem outOk_tag {s₀ : State} (hp : APre e s₀) : OutOk s₀ (off (cx s₀) tagOff) :=
  ⟨sub_disj s₀ (by decide) (by decide) (by decide), sub_disj s₀ (by decide) (by decide) (by decide),
    sub_disj s₀ (by decide) (by decide) (by decide), ⟨ctxR s₀, hp.ctx_wr, tagOff, rfl, by exact (by decide : tagOff + 16 ≤ 656)⟩⟩

/-- `seal`'s `tag`. -/
theorem outOk_tP {s₀ : State} (hp : APre true s₀) : OutOk s₀ (tp s₀) :=
  ⟨hp.t_c.symm.sub_left (sub_ctx s₀ (by decide)), hp.t_c.sub_right (sub_ctx s₀ (by decide)),
    hp.t_c.symm.sub_left (sub_ctx s₀ (by decide)), ⟨tR s₀, hp.t_wr, 0, (BitVec.add_zero _).symm, by exact (by decide : 0 + 16 ≤ 16)⟩⟩

theorem fin_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) {O : Addr} (ho : OutOk s₀ O)
    (h3 : s.gpr .r3 = cx s₀) (h4 : (s.gpr .r4).toNat % 16 = 0) (h5 : s.gpr .r5 = O)
    (h6 : s.gpr .r6 = off (cx s₀) scrOff) :
    WP isa finalize s fun s' =>
      Kept [sub s₀ 0 128, ⟨O, 16⟩, sub s₀ scrOff 128] s s' ∧
      ∀ key msg, Repr s.mem (cx s₀) key msg → bytesAt s'.mem O 16 = mac key msg := by
  have hPO : (⟨cx s₀, 128⟩ : Region).Disjoint ⟨O, 16⟩ := by rw [← sub_zero s₀ 128]; exact ho.dP
  have hPS : (⟨cx s₀, 128⟩ : Region).Disjoint ⟨off (cx s₀) scrOff, 128⟩ := by
    rw [← sub_zero s₀ 128]; exact sub_disj s₀ (by decide) (by decide) (by decide)
  have hw : Covers [⟨cx s₀, 128⟩, ⟨O, 16⟩, ⟨off (cx s₀) scrOff, 128⟩] s.wr := by
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ctxR s₀, by rw [h.wr]; exact hp.ctx_wr, 0, (BitVec.add_zero _).symm,
        by exact (by decide : 0 + 128 ≤ 656)⟩
    · obtain ⟨r', hr', k, hk, hl⟩ := ho.w
      exact ⟨r', by rw [h.wr]; exact hr', k, hk, hl⟩
    · exact ⟨ctxR s₀, by rw [h.wr]; exact hp.ctx_wr, scrOff, rfl, by exact (by decide : scrOff + 128 ≤ 656)⟩
  have hc : Covers ([] ++ [⟨cx s₀, 128⟩, ⟨O, 16⟩, ⟨off (cx s₀) scrOff, 128⟩]) (s.rd ++ s.wr) := by
    rw [List.nil_append]; exact covers_right hw
  refine finalize_call h3 rfl h5 h6 hPO hPS ho.dS hc hw fun s' hk htag => ?_
  rw [← sub_zero s₀ 128] at hk
  refine ⟨hk, fun key msg hr => htag key msg (VG.Proof.Poly1305.Repr.buffered hr) ?_⟩
  obtain ⟨hl, _, _⟩ := hr
  rw [h4, hl]

/-! ## Restoring the registers -/

theorem restore_eq : restore = ([mov .r12 .r24, .load .d .r0 .r12 (savOff + 56), .mtlr .r0] : List Instr) ++
    (List.range 7).flatMap fun i => [.load .d (saved i) .r12 (savOff + 8 * i)] := rfl

theorem saved_inj : ∀ i < 7, ∀ j < 7, saved i = saved j → i = j := by decide

theorem r12_ne_saved : ∀ i < 7, Reg.r12 ≠ saved i := by decide

/-- The first `n` registers restored, from the state `sB` the loads start in. -/
structure RI (s₀ sB : State) (n : Nat) (s : State) : Prop where
  r12 : s.gpr .r12 = cx s₀
  restored : ∀ i < n, s.gpr (saved i) = s₀.gpr (saved i)
  others : ∀ r, (∀ i < 7, r ≠ saved i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  sp : s.sp = sB.sp
  lr : s.lr = sB.lr

theorem restore_step {s₀ sB : State} (hp : APre e s₀) (hrd : sB.rd = s₀.rd) (hwr : sB.wr = s₀.wr)
    (hsv : Saved s₀ sB.mem) {n : Nat} (hn : n < 7) {s : State} (h : RI s₀ sB n s) :
    WP isa (.block [.load .d (saved n) .r12 (savOff + 8 * n)]) s (RI s₀ sB (n + 1)) := by
  refine wp_ld (a := off (cx s₀) (savOff + 8 * n)) (by decide) (by rw [savOff_eq]; omega_using [hn]) (by rw [h.r12])
    (by rw [h.rd, h.wr, hrd, hwr]; exact hp.in_ctx' (by rw [savOff_eq]; omega_using [hn])) fun s' u => WP.block_nil ?_
  refine ⟨by rw [u.other _ (r12_ne_saved n hn), h.r12], fun i hi => ?_, fun r hr => ?_, by rw [u.mem, h.mem],
    by rw [u.rd, h.rd], by rw [u.wr, h.wr], by rw [u.sp, h.sp], by rw [u.lr, h.lr]⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [u.other _ (fun e => absurd (saved_inj i (by omega_arith) n hn e) (by omega_using [hi])), h.restored i hi]
    · rw [u.gpr, h.mem, hsv.1 i hn]
  · rw [u.other r (hr n hn), h.others r hr]

/-- Restoring `r24`–`r29`, `r31` and the return address from `ctx[464, 528)`, through `r12`. -/
theorem restore_ok {s₀ : State} (hp : APre e s₀) {s : State} (h14 : s.gpr .r24 = cx s₀) (hsv : Saved s₀ s.mem)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block restore) s fun s' => (∀ i < 7, s'.gpr (saved i) = s₀.gpr (saved i)) ∧ s'.lr = s₀.lr ∧
      (∀ r, (∀ i < 7, r ≠ saved i) → r ≠ .r0 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [restore_eq]
  refine wp_mov fun s₁ u₁ => wp_ld (a := off (cx s₀) (savOff + 56)) (by decide) (by decide)
    (by rw [u₁.gpr, h14]) (by rw [u₁.rd, u₁.wr, hrd, hwr]; exact hp.in_ctx' (by decide)) fun s₂ u₂ =>
    wp_mtlr fun s₃ l₃ => ?_
  have m₃ : s₃.mem = s.mem := by rw [l₃.mem, u₂.mem, u₁.mem]
  refine WP.mono (wp_range_flatMap (M := isa) (RI s₀ s₃)
    (fun k t hk ht => restore_step hp (by rw [l₃.rd, u₂.rd, u₁.rd, hrd]) (by rw [l₃.wr, u₂.wr, u₁.wr, hwr])
      (by rw [m₃]; exact hsv) hk ht) 7 (Nat.le_refl _) s₃
    ⟨by rw [l₃.gpr, u₂.other _ (by decide), u₁.gpr, h14], fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩)
    fun s' h' => ⟨h'.restored, ?_, fun r hr h0 h12 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [h'.lr, l₃.lr, u₂.gpr, u₁.mem]; exact hsv.2
  · rw [h'.others r hr, l₃.gpr, u₂.other r h0, u₁.other r h12]
  · rw [h'.mem, m₃]
  · rw [h'.sp, l₃.sp, u₂.sp, u₁.sp]
  · rw [h'.rd, l₃.rd, u₂.rd, u₁.rd]
  · rw [h'.wr, l₃.wr, u₂.wr, u₁.wr]

/-! ## Comparing the tags -/

/-- `(x | -x) >> 63` is 0 if `x = 0` and 1 otherwise. -/
theorem nz_bit (x : BitVec 64) : (x ||| (BitVec.ofNat 64 0 - x)) >>> 63 = if x = 0 then 0 else 1 := by
  by_cases h : x = 0
  · subst h; rfl
  · simp only [h, ↓reduceIte]
    have hx : x.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq h')
    have hlt := x.isLt
    have hneg : (BitVec.ofNat 64 0 - x).toNat = 2 ^ 64 - x.toNat := by
      rw [BitVec.toNat_sub, show (BitVec.ofNat 64 0).toNat = 0 from rfl]; omega_using [hx]
    have h1 : 2 ^ 63 ≤ (x ||| (BitVec.ofNat 64 0 - x)).toNat := by
      rw [BitVec.toNat_or]
      rcases Nat.lt_or_ge x.toNat (2 ^ 63) with h2 | h2
      · exact Nat.le_trans (by omega_using [hneg, h2]) (Nat.right_le_or (n := x.toNat))
      · exact Nat.le_trans h2 Nat.left_le_or
    have h2 := (x ||| (BitVec.ofNat 64 0 - x)).isLt
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, show (1 : BitVec 64).toNat = 1 from rfl]
    omega_using [h1]

theorem sel_eq {x : BitVec 64} {p : Prop} [Decidable p] (h : x = 0 ↔ p) :
    (BitVec.ofNat 64 1 - if x = 0 then 0 else 1) = if p then 1 else 0 := by
  by_cases hp : p
  · have hx : x = 0 := h.mpr hp
    simp only [hx, hp, ↓reduceIte]
    decide
  · have hx : ¬ x = 0 := fun e => hp (h.mp e)
    simp only [hx, hp, ↓reduceIte]
    decide

/-- Doublewords with the same bytes are equal. -/
theorem readW64_eq_of_bytes {m : Mem} {p q : Addr}
    (h : ∀ i < 8, m (p + BitVec.ofNat 64 i) = m (q + BitVec.ofNat 64 i)) : m.readW p 64 = m.readW q 64 := by
  have e : m.read p 8 = m.read q 8 :=
    Mem.read_eq_of_bytes fun i hi => by rw [Mem.extractLsb'_read m q hi]; exact h i hi
  simp only [Mem.readW]
  rw [e]

/-- The tags differ in no bit if and only if they are equal. -/
theorem tag_eq (m : Mem) (c t : Addr) :
    ((m.readW (off c tagOff) 64 ^^^ m.readW (off t 0) 64) |||
      (m.readW (off c (tagOff + 8)) 64 ^^^ m.readW (off t 8) 64)) = 0#64 ↔
      bytesAt m (off c tagOff) 16 = bytesAt m t 16 := by
  rw [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff, BitVec.xor_eq_zero_iff]
  constructor
  · rintro ⟨h0, h1⟩
    refine bytes_of_dwords (n := 2) fun k hk => ?_
    match k, hk with
    | 0, _ => exact (congrArg (m.readW · 64) (BitVec.add_zero _)).trans h0
    | 1, _ => rw [off_add]; exact h1
  · intro h
    have hb : ∀ i < 16, m (off c (tagOff + i)) = m (off t i) := fun i hi => by
      have := congrArg (fun l => l.getD i 0) h
      simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
        Option.map_some, Option.getD_some] at this
      rwa [off_add] at this
    refine ⟨readW64_eq_of_bytes fun i hi => ?_, readW64_eq_of_bytes fun i hi => ?_⟩
    · rw [off_add, off_add, Nat.zero_add]; exact hb i (by omega_using [hi])
    · rw [off_add, off_add, Nat.add_assoc]; exact hb (8 + i) (by omega_using [hi])

/-- The tags compared: the one computed, at `ctx + tagOff`, and `tag`. -/
theorem compare_ok {s₀ : State} (hp : APre false s₀) {s : State} (h : Inv s₀ s) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ s', s'.gpr .r3 = (if bytesAt s.mem (off (cx s₀) tagOff) 16 = bytesAt s.mem (tp s₀) 16 then 1 else 0) →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) → s'.sp = s.sp → s'.lr = s.lr → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block rest) s' Q) :
    WP isa (.block (Impl.ChaCha20Poly1305.PPC64LE.compare ++ rest)) s Q := by
  unfold Impl.ChaCha20Poly1305.PPC64LE.compare
  simp only [List.cons_append, List.nil_append]
  have h14 := h.regs.r24
  have h19 : s.gpr .r29 = tp s₀ := h.regs.r29
  have ic : ∀ d, d + 8 ≤ 656 → InRegions (s.rd ++ s.wr) (off (cx s₀) d) 8 := fun d hd => by
    rw [h.rd, h.wr]; exact hp.in_ctx' hd
  have it : ∀ d, d + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (off (tp s₀) d) 8 := fun d hd =>
    ⟨tR s₀, by rw [h.rd]; exact List.mem_append_left _ hp.t_rd, Offset.contains_base _ hd (by omega_using [hd])⟩
  refine wp_ld (a := off (cx s₀) tagOff) (by decide) (by decide) (by rw [h14]) (ic _ (by decide))
    fun s₁ u₁ => ?_
  refine wp_ld (a := off (tp s₀) 0) (by decide) (by decide) (by rw [u₁.other _ (by decide), h19])
    (by rw [u₁.rd, u₁.wr]; exact it 0 (by decide)) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  refine wp_ld (a := off (cx s₀) (tagOff + 8)) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h14])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact ic _ (by decide)) fun s₄ u₄ => ?_
  refine wp_ld (a := off (tp s₀) 8) (by decide) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h19])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact it 8 (by decide)) fun s₅ u₅ => ?_
  refine wp_xor fun s₆ u₆ => wp_or fun s₇ u₇ => wp_li (by decide) fun s₈ u₈ => wp_sub fun s₉ u₉ =>
    wp_or fun s₁₀ u₁₀ => wp_lsr (by decide) fun s₁₁ u₁₁ => wp_li (by decide) fun s₁₂ u₁₂ =>
    wp_sub fun s₁₃ u₁₃ => k s₁₃ ?_ (fun r hr => ?_) ?_ ?_ ?_ ?_ ?_
  · have x₃ : s₃.gpr .r3 = s.mem.readW (off (cx s₀) tagOff) 64 ^^^ s.mem.readW (off (tp s₀) 0) 64 := by
      rw [u₃.gpr, u₂.other _ (by decide), u₂.gpr, u₁.gpr, u₁.mem]
    have x₆ : s₆.gpr .r4 = s.mem.readW (off (cx s₀) (tagOff + 8)) 64 ^^^ s.mem.readW (off (tp s₀) 8) 64 := by
      rw [u₆.gpr, u₅.other _ (by decide), u₅.gpr, u₄.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    have x₇ := u₇.gpr
    rw [u₆.other _ (by decide), x₆, u₅.other _ (by decide), u₄.other _ (by decide), x₃] at x₇
    rw [u₁₃.gpr, u₁₂.gpr, u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.gpr, u₉.other _ (by decide), u₉.gpr, u₈.gpr,
      u₈.other _ (by decide), x₇, nz_bit]
    exact sel_eq (tag_eq s.mem (cx s₀) (tp s₀))
  · rw [u₁₃.other _ (ne_of_pres hr), u₁₂.other _ (ne_of_pres hr), u₁₁.other _ (ne_of_pres hr), u₁₀.other _ (ne_of_pres hr), u₉.other _ (ne_of_pres hr), u₈.other _ (ne_of_pres hr), u₇.other _ (ne_of_pres hr), u₆.other _ (ne_of_pres hr), u₅.other _ (ne_of_pres hr), u₄.other _ (ne_of_pres hr), u₃.other _ (ne_of_pres hr), u₂.other _ (ne_of_pres hr), u₁.other _ (ne_of_pres hr)]
  · rw [u₁₃.sp, u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [u₁₃.lr, u₁₂.lr, u₁₁.lr, u₁₀.lr, u₉.lr, u₈.lr, u₇.lr, u₆.lr, u₅.lr, u₄.lr, u₃.lr, u₂.lr, u₁.lr]
  · rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

end VG.Proof.ChaCha20Poly1305.PPC64LE
