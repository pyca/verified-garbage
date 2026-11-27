module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.SealGather
import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.LoopCT
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.SealGather
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.LoopCT
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
meta import VerifiedGarbage.Proof.Aes.KeyExp
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Loop
import VerifiedGarbage.Proof.ChaCha20Poly1305.Gathered
import VerifiedGarbage.Proof.AesGcm.ScratchGather
public import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.AArch64.Depth
public import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Loop
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.Gathered
meta import VerifiedGarbage.Proof.AesGcm.ScratchGather
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Gcm.SealGather
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Env
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AArch64.Depth
meta import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract
meta import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace

/-! ### `ChaCha20Poly1305.AArch64.Gather.Fn`, which this module and modules that import it used -/

section

/-! ### `ChaCha20Poly1305.AArch64.Gather.Contract`, which this module and modules that import it used -/

section

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, AArch64: the contract

Untrusted: everything here is checked by Lean. The contract the proof of
`vg_chacha20_poly1305_seal_gather` is written against, which the shared one
(`Spec.ChaCha20Poly1305.sealGatherContract`, with the 1296 bytes of stack
below the stack pointer that its frame and its call use) implies
(`Gather/Verified.lean`): `(key = x0, nonce = x1, aad = x2, aad_len = x3,
src = x4, src_count = x5, dst = x6, len = x7, tag = [sp])`.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.Gather

open VG VG.AArch64
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20Poly1305 (encrypt gathered gatheredLen pMax)

section
variable (s : State)

/-- The arguments. -/
abbrev K : Addr := s.gpr .x0
abbrev Nn : Addr := s.gpr .x1
abbrev Ad : Addr := s.gpr .x2
abbrev AL : Nat := (s.gpr .x3).toNat
abbrev Src : Addr := s.gpr .x4
abbrev Cnt : Nat := (s.gpr .x5).toNat
abbrev Dst : Addr := s.gpr .x6
abbrev L : Nat := (s.gpr .x7).toNat
abbrev Tg : Addr := stackArg s 0

/-- The regions: the key, the nonce, the additional data, the descriptors,
the slices they list, the output, the tag, the stack argument and the stack
below the stack pointer. -/
abbrev kR : Region := ⟨K s, 32⟩
abbrev nR : Region := ⟨Nn s, 12⟩
abbrev aR : Region := ⟨Ad s, AL s⟩
abbrev dsR : Region := ⟨Src s, Cnt s * 16⟩
abbrev lsR : List Region := Sig.listed 64 s.mem .u8 (Src s) (Cnt s)
abbrev dR : Region := ⟨Dst s, L s⟩
abbrev tgR : Region := ⟨Tg s, 16⟩
abbrev argR : Region := ⟨stackArgAddr s 0, 8⟩
abbrev stkR : Region := ⟨s.sp - BitVec.ofNat 64 1296, 1296⟩

/-- The total length of the first `i` slices, and their bytes. -/
abbrev gl (i : Nat) : Nat := gatheredLen 64 s.mem (Src s) i
abbrev pt (i : Nat) : List Byte := gathered 64 s.mem (Src s) i

end

/-- What the code of `vg_chacha20_poly1305_seal_gather` needs. -/
def gatherPre (s : State) : Prop :=
  s.rd = [kR s, nR s, aR s, dsR s] ++ lsR s ++ [argR s] ∧ s.wr = [dR s, tgR s] ∧
    (kR s).Disjoint (dR s) ∧ (kR s).Disjoint (tgR s) ∧ (nR s).Disjoint (dR s) ∧
    (nR s).Disjoint (tgR s) ∧ (aR s).Disjoint (dR s) ∧ (aR s).Disjoint (tgR s) ∧
    (dsR s).Disjoint (dR s) ∧ (dsR s).Disjoint (tgR s) ∧
    (∀ r ∈ lsR s, r.Disjoint (dR s) ∧ r.Disjoint (tgR s)) ∧
    (dR s).Disjoint (tgR s) ∧ (dR s).Disjoint (argR s) ∧ (tgR s).Disjoint (argR s) ∧
    (stkR s).Disjoint (kR s) ∧ (stkR s).Disjoint (nR s) ∧ (stkR s).Disjoint (aR s) ∧
    (stkR s).Disjoint (dsR s) ∧ (∀ r ∈ lsR s, (stkR s).Disjoint r) ∧ (stkR s).Disjoint (argR s) ∧
    (stkR s).Disjoint (dR s) ∧ (stkR s).Disjoint (tgR s) ∧
    (K s).toNat + 32 ≤ 2 ^ 64 ∧ (Nn s).toNat + 12 ≤ 2 ^ 64 ∧ (Ad s).toNat + AL s ≤ 2 ^ 64 ∧
    (Src s).toNat + Cnt s * 16 ≤ 2 ^ 64 ∧ (∀ r ∈ lsR s, r.base.toNat + r.len ≤ 2 ^ 64) ∧
    (Dst s).toNat + L s ≤ 2 ^ 64 ∧ (Tg s).toNat + 16 ≤ 2 ^ 64 ∧
    1296 ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 64 ∧ gl s (Cnt s) = L s ∧ L s ≤ pMax

/-- What two runs agree on: the arguments and the descriptors. -/
def gatherPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ s₁.sp = s₂.sp ∧ s₁.dit = s₂.dit ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ ∀ i < Cnt s₁ * 16, s₁.mem (Src s₁ + BitVec.ofNat 64 i) = s₂.mem (Src s₁ + BitVec.ofNat 64 i)

/-- What `vg_chacha20_poly1305_seal_gather` leaves: `sealGatherPost`. -/
def gatherPost (s s' : State) : Prop :=
  encrypt (bytesAt s.mem (K s) 32) (bytesAt s.mem (Nn s) 12) (bytesAt s.mem (Ad s) (AL s)) (pt s (Cnt s)) =
    (bytesAt s'.mem (Dst s) (L s), bytesAt s'.mem (Tg s) 16)

/-- `vg_chacha20_poly1305_seal_gather`. -/
def gatherAArch64 : Contract isa where
  pre := gatherPre
  post := gatherPost
  pub := gatherPub

end VG.Proof.ChaCha20Poly1305.AArch64.Gather

end

end

/-! ### `ChaCha20Poly1305.AArch64.Gather.Callee`, which this module and modules that import it used -/

section

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, AArch64: the function called

Untrusted: everything here is checked by Lean. `vg_chacha20_poly1305_seal_gather`
calls an implementation of `vg_chacha20_poly1305_seal` as an artifact
(`SealFn`), with its working space in a frame of its own, so what the proof
needs of it is its shared contract (`Spec.ChaCha20Poly1305.sealContract`,
with 1280 bytes of stack): its precondition from the layout the call gives it
(`callPre`, `sealSpec_pre`), its postcondition (`sealSpec_post`) and its
public data (`sealSpec_pub`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.Gather

open VG VG.AArch64
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20Poly1305 (encrypt)

/-- An implementation of `vg_chacha20_poly1305_seal`, by its shared
contract, whose frames use at most the 1280 bytes below the stack pointer that
the contract reserves. -/
structure SealFn where
  name : String
  code : Prog isa
  verified : Verified AArch64.target code (Spec.ChaCha20Poly1305.sealContract AArch64.abi 1280)
  depth : 16 * code.aarch64Depth ≤ 1280

/-- What a call of `vg_chacha20_poly1305_seal(key = x0, nonce = x1, aad = x2,
aad_len = x3, data = x4, len = x5, tag = x6)` needs. -/
def callPre (s : State) : Prop :=
  let key : Region := ⟨s.gpr .x0, 32⟩
  let nonce : Region := ⟨s.gpr .x1, 12⟩
  let aad : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let data : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let tag : Region := ⟨s.gpr .x6, 16⟩
  let stk : Region := ⟨s.sp - BitVec.ofNat 64 1280, 1280⟩
  s.rd = [key, nonce, aad] ∧ s.wr = [data, tag] ∧
    key.Disjoint data ∧ key.Disjoint tag ∧ nonce.Disjoint data ∧ nonce.Disjoint tag ∧
    aad.Disjoint data ∧ aad.Disjoint tag ∧ data.Disjoint tag ∧
    stk.Disjoint key ∧ stk.Disjoint nonce ∧ stk.Disjoint aad ∧ stk.Disjoint data ∧ stk.Disjoint tag ∧
    (s.gpr .x0).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 12 ≤ 2 ^ 64 ∧
    (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x6).toNat + 16 ≤ 2 ^ 64 ∧ 1280 ≤ s.sp.toNat

theorem sealSpec_pre {s : State} (h : callPre s) :
    (Spec.ChaCha20Poly1305.sealContract AArch64.abi 1280).pre s := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀⟩ := h
  sig_pre [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, AArch64.abi, AArch64.argRegs]
  sig_reduce [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, AArch64.abi,
    AArch64.argRegs, List.getD]
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | trivial
    | omega
    | exact Region.Disjoint.symm ‹_›

theorem sealSpec_post {s s' : State} (h : (Spec.ChaCha20Poly1305.sealContract AArch64.abi 1280).post s s') :
    encrypt (bytesAt s.mem (s.gpr .x0) 32) (bytesAt s.mem (s.gpr .x1) 12)
        (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) =
      (bytesAt s'.mem (s.gpr .x4) (s.gpr .x5).toNat, bytesAt s'.mem (s.gpr .x6) 16) := by
  sig_post [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig,
    Spec.ChaCha20Poly1305.sealPost, AArch64.abi, AArch64.argRegs] at h
  exact h

theorem sealSpec_pub {s₁ s₂ : State} (h : s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧
    s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.sp = s₂.sp ∧ s₁.dit = s₂.dit) :
    (Spec.ChaCha20Poly1305.sealContract AArch64.abi 1280).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, aMd⟩ := h
  sig_pub [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, AArch64.abi, AArch64.argRegs]
  sig_reduce [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, AArch64.abi, AArch64.argRegs]
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

end VG.Proof.ChaCha20Poly1305.AArch64.Gather

end

end

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, AArch64: the function

Untrusted: everything here is checked by Lean. `vg_chacha20_poly1305_seal_gather`
allocates its frame of 16 bytes, at `B + 1280` with `B` the base of the 1296
bytes of stack below the stack pointer (`sp = B + 1296`), keeps our return
address at `B + 1288` and `dst`, `len` and `tag` in `x8`, `x9` and `x10`
(`entered_wp`), gathers the slices to `dst` (`gather_wp`), and calls
`vg_chacha20_poly1305_seal` on them in place (`sealSpec_pre`,
`sealSpec_post`); the call keeps our frame, so the return address comes back
from it (`sealGather_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.AArch64.Gather

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.ChaCha20Poly1305.AArch64.SealGather VG.WriteBytes
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20Poly1305 (encrypt gathered gatheredLen pMax)
open VG.Proof.ChaCha20Poly1305 (bytesAt_frame bytesAt_writeBytes_self gathered_eq_gcm)
open VG.Proof.AesGcm.AArch64 (covers_of_mem covers_cons covers_append covers_prefix covers_nil)
open VG.Proof.AesGcm.AArch64.Gather (GatherPre gather_wp gatherRegs contains_off add_ofNat_sub_ofNat ldrSp_ok)

/-- The entry, in the frame at `P`: our return address at `P + 8`, the
stack argument at `P + 16` (`tag`) in `x10`, `dst` and `len` in `x8` and
`x9`, and the gathering's arguments `src`, `src_count` and `dst` in `x6`,
`x7` and `x11`. -/
theorem entry_ok (a : State) {P : Addr} (hsp : a.sp = P) (w₈ : InRegions a.wr (P + BitVec.ofNat 64 8) 8)
    (r₁₆ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 16) 8) :
    WP isa (.block entry) a fun e =>
      e.mem = a.mem.write (P + BitVec.ofNat 64 8) 8 (a.gpr .x30) ∧
      e.gpr .x10 = (a.mem.write (P + BitVec.ofNat 64 8) 8 (a.gpr .x30)).read (P + BitVec.ofNat 64 16) 8 ∧
      e.gpr .x8 = a.gpr .x6 ∧ e.gpr .x9 = a.gpr .x7 ∧ e.gpr .x11 = a.gpr .x6 ∧ e.gpr .x6 = a.gpr .x4 ∧
      e.gpr .x7 = a.gpr .x5 ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x16 → e.gpr r = a.gpr r) ∧
      e.sp = a.sp ∧ e.rd = a.rd ∧ e.wr = a.wr := by
  subst hsp
  have e₀ : a.sp + BitVec.ofNat 64 0 = a.sp := BitVec.add_zero _
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by
    simp only [entry, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store,
      Size.bytes, Size.bits, State.read, gpr_write, mem_write, rd_write, wr_write, sp_write, Option.bind_some,
      Option.map_some, BitVec.setWidth_eq, e₀, reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul,
      Nat.reduceMod, and_self, w₈, r₁₆]; rfl, rfl⟩ fun e he => ?_
  subst he
  refine ⟨rfl, by simp [State.write], by simp [State.write], by simp [State.write], by simp [State.write],
    by simp [State.write], by simp [State.write], fun r h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₆ => ?_, rfl, rfl, rfl⟩
  simp [State.write, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₆]

/-- `callArgs`: `x8`, `x9` and `x10` into `x4`, `x5` and `x6`. -/
theorem callArgs_ok (a : State) :
    WP isa (.block callArgs) a fun e => e.gpr .x4 = a.gpr .x8 ∧ e.gpr .x5 = a.gpr .x9 ∧
      e.gpr .x6 = a.gpr .x10 ∧ (∀ r, r ≠ .x4 → r ≠ .x5 → r ≠ .x6 → e.gpr r = a.gpr r) ∧ e.mem = a.mem ∧
      e.sp = a.sp ∧ e.rd = a.rd ∧ e.wr = a.wr ∧ e.v = a.v := by
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by
    simp only [callArgs, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
      BitVec.setWidth_eq, Nat.reduceLT, ↓reduceIte]; rfl, rfl⟩ fun e he => ?_
  subst he
  refine ⟨by simp [State.write], by simp [State.write], by simp [State.write], fun r h₄ h₅ h₆ => ?_, rfl, rfl,
    rfl, rfl, rfl⟩
  simp [State.write, h₄, h₅, h₆]

theorem stackArgAddr_eq (s : State) {B : Addr} (hB : s.sp = B + BitVec.ofNat 64 1296) (i : Nat) :
    stackArgAddr s i = B + BitVec.ofNat 64 (1296 + 8 * i) := by
  rw [stackArgAddr, hB, Offset.add_ofNat_add_ofNat]

/-! ## The layout -/

section
variable (s : State)

/-- The base of the 1296 bytes of stack below the stack pointer. -/
abbrev Bs : Addr := s.sp - BitVec.ofNat 64 1296

/-- The frame. -/
abbrev FR : Region := ⟨Bs s + BitVec.ofNat 64 1280, 16⟩

/-- The memory after the entry: the return address at `Bs + 1288`. -/
abbrev eMem : Mem := s.mem.write (Bs s + BitVec.ofNat 64 1288) 8 (s.gpr .x30)

/-- The memory once the slices are gathered at `dst`. -/
abbrev gMem : Mem := writeBytes (eMem s) (Dst s) (pt s (Cnt s))

/-- The regions the call of `vg_chacha20_poly1305_seal` reads and writes. -/
abbrev rdC : List Region := [kR s, nR s, aR s]
abbrev wrC : List Region := [dR s, tgR s]

end

/-- What `gatherPre` gives, with the stack below the stack pointer at `Bs s`. -/
structure Lay (s : State) : Prop where
  pre : gatherPre s
  hB : s.sp = Bs s + BitVec.ofNat 64 1296
  hBn : (Bs s).toNat + 1304 ≤ 2 ^ 64
  bk : (⟨Bs s, 1296⟩ : Region).Disjoint (kR s)
  bn : (⟨Bs s, 1296⟩ : Region).Disjoint (nR s)
  ba : (⟨Bs s, 1296⟩ : Region).Disjoint (aR s)
  bds : (⟨Bs s, 1296⟩ : Region).Disjoint (dsR s)
  bl : ∀ r ∈ lsR s, (⟨Bs s, 1296⟩ : Region).Disjoint r
  bd : (⟨Bs s, 1296⟩ : Region).Disjoint (dR s)
  bt : (⟨Bs s, 1296⟩ : Region).Disjoint (tgR s)
  hargR : argR s = ⟨Bs s + BitVec.ofNat 64 1296, 8⟩
  w₁ : 1296 ≤ s.sp.toNat
  hgl : gl s (Cnt s) = L s
  ods : (Src s).toNat + Cnt s * 16 ≤ 2 ^ 64

theorem lay {s : State} (hs : gatherPre s) : Lay s := by
  obtain ⟨rd, wr, kd, kt, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, bk, bn, ba, bds, bl, barg, bd, bt,
    ok, on, oa, ods, ol, od, ot, w₁, w₂, hgl, hpm⟩ := hs
  have hB : s.sp = Bs s + BitVec.ofNat 64 1296 := (BitVec.sub_add_cancel s.sp _).symm
  have hBn : (Bs s).toNat + 1304 ≤ 2 ^ 64 := by
    have e := congrArg BitVec.toNat hB
    rw [BitVec.toNat_add, BitVec.toNat_ofNat] at e
    have := (Bs s).isLt
    omega_arith
  exact ⟨⟨rd, wr, kd, kt, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, bk, bn, ba, bds, bl, barg, bd, bt,
    ok, on, oa, ods, ol, od, ot, w₁, w₂, hgl, hpm⟩, hB, hBn, bk, bn, ba, bds, bl, bd, bt,
    by simp only [argR, stackArgAddr_eq s hB, Nat.mul_zero, Nat.add_zero], w₁, hgl, ods⟩

/-- Parts of the stack below the stack pointer. -/
theorem stk_sub (s : State) (d n : Nat) (h' : d + n ≤ 1296) :
    (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Sub ⟨Bs s, 1296⟩ :=
  Offset.sub_base _ h'

theorem frame_eMem (s : State) : Frame [FR s] s.mem (eMem s) :=
  (Frame.refl _ _).write (List.mem_singleton_self _) _ (contains_off _ (by decide) (by decide) (by decide))

namespace Lay

variable {s : State} (h : Lay s)
include h

theorem argIn : argR s ∈ s.rd := by rw [h.pre.1]; simp

theorem inArg (rs : List Region) : InRegions (s.rd ++ rs) (Bs s + BitVec.ofNat 64 1296) 8 :=
  ⟨_, List.mem_append_left _ h.argIn, by rw [h.hargR]; exact Region.contains_self _ _⟩

theorem sep (d e : Nat) (h₁ : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d + 8 ≤ 1304) (he : e + 8 ≤ 1304) :
    Mem.Sep (Bs s + BitVec.ofNat 64 d) 8 (Bs s + BitVec.ofNat 64 e) 8 :=
  Offset.sep _ h₁ (by have := h.hBn; omega_arith) (by have := h.hBn; omega_arith)

omit h in
/-- The memory the entry left outside the frame. -/
theorem keepE {r : Region} (hr : r.Disjoint ⟨Bs s, 1296⟩) {x : Addr} (hx : r.Contains x 1) :
    eMem s x = s.mem x :=
  frame_eMem s x fun r' hr' hc => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hr x hx (stk_sub s 1280 16 (by decide) x hc)

/-- `tag`, after the entry. -/
theorem eTag : (eMem s).read (Bs s + BitVec.ofNat 64 1296) 8 = Tg s := by
  rw [Mem.read_write_sep (h.sep 1296 1288 (by decide) (by decide) (by decide)) (by decide), ← stackArgAddr_eq s h.hB 0]
  rfl

/-- The descriptors and the slices, after the entry. -/
theorem hag : ∀ r ∈ Sig.descRegion 64 (Src s) (Cnt s) :: lsR s, ∀ x, r.Contains x 1 → s.mem x = eMem s x := by
  intro r hr x hx
  refine (keepE ?_ hx).symm
  rcases List.mem_cons.mp hr with rfl | hr
  · exact h.bds.symm
  · exact (h.bl r hr).symm

theorem hpt : Spec.Gcm.gathered 64 (eMem s) (Src s) (Cnt s) = pt s (Cnt s) :=
  Proof.AesGcm.gathered_congr_le (Nat.le_refl _) h.hag

theorem hlen : (pt s (Cnt s)).length = L s := (Proof.Gcm.length_gathered _ _ _ _).trans h.hgl

theorem frame_gMem : Frame [dR s] (eMem s) (gMem s) := by
  refine writeBytes_frame _ _ _ ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, h.hlen, Nat.le_refl]

/-- A doubleword of the frame, once the slices are gathered. -/
theorem gFrame (d : Nat) (hd' : d + 8 ≤ 1296) :
    (gMem s).read (Bs s + BitVec.ofNat 64 d) 8 = (eMem s).read (Bs s + BitVec.ofNat 64 d) 8 :=
  Frame.read h.frame_gMem (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.bd.symm.sub_right (stk_sub s d 8 hd') |>.symm) (by decide)

end Lay

/-! ## The phases -/

/-- After the entry. -/
structure Entered (s e : State) : Prop where
  mem : e.mem = eMem s
  x6 : e.gpr .x6 = Src s
  x7 : e.gpr .x7 = s.gpr .x5
  x8 : e.gpr .x8 = Dst s
  x9 : e.gpr .x9 = s.gpr .x7
  x10 : e.gpr .x10 = Tg s
  x11 : e.gpr .x11 = Dst s
  gpr : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x16 → e.gpr r = s.gpr r
  sp : e.sp = Bs s + BitVec.ofNat 64 1280
  rd : e.rd = s.rd
  wr : e.wr = FR s :: s.wr
  v : ∀ r ∈ preservedV, (e.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem allocated_sp {s : State} (h : Lay s) : (allocated 16 s).sp = Bs s + BitVec.ofNat 64 1280 := by
  show s.sp - BitVec.ofNat 64 16 = _
  rw [h.hB, add_ofNat_sub_ofNat _ (by decide)]

theorem entered_wp {s : State} (h : Lay s) : WP isa (.block entry) (allocated 16 s) (Entered s) := by
  have asp := allocated_sp h
  have awr : (allocated 16 s).wr = FR s :: s.wr := by
    show (⟨s.sp - BitVec.ofNat 64 16, 16⟩ :: s.wr : List Region) = _
    rw [show s.sp - BitVec.ofNat 64 16 = _ from asp]
  refine WP.mono (WP.preservedV (entry_ok (allocated 16 s) asp
      ⟨_, by rw [awr]; exact List.mem_cons_self .., Offset.contains_base _ (by decide) (by decide)⟩
      (by rw [Offset.add_ofNat_add_ofNat]; exact h.inArg _)) (by lit_decide))
    fun e ⟨⟨me, x10e, x8e, x9e, x11e, x6e, x7e, ge, spe, rde, wre⟩, ve⟩ => ?_
  simp only [Offset.add_ofNat_add_ofNat, Nat.reduceAdd] at me x10e
  exact ⟨me, x6e, x7e, x8e, x9e, x10e.trans h.eTag, x11e, ge, by rw [spe, asp], rde, by rw [wre, awr], ve⟩

/-- `gather`'s precondition after the entry. -/
theorem gatherPre_of {s e : State} (h : Lay s) (he : Entered s e) : GatherPre e (Src s) (Dst s) (Cnt s) (L s) := by
  obtain ⟨rd, wr, kd, kt, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, bk, bn, ba, bds, bl, barg, bd, bt,
    ok, on, oa, ods, ol, od, ot, w₁, w₂, hgl, hpm⟩ := h.pre
  obtain ⟨hls, -⟩ := Proof.AesGcm.listed_congr_le (Nat.le_refl _) h.hag
  rw [← he.mem] at hls
  exact { x6 := he.x6
          x7 := by rw [he.x7, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          x11 := he.x11
          hcnt := (s.gpr .x5).isLt
          dw := ods
          lt := (s.gpr .x7).isLt
          len := by rw [he.mem, Proof.AesGcm.gatheredLen_congr_le (Nat.le_refl _) h.hag]; exact hgl
          dsr := covers_of_mem (List.mem_append_left _ (by rw [he.rd]; show dsR s ∈ s.rd; rw [rd]; simp))
          lsr := fun r hr => covers_of_mem (List.mem_append_left _ (by
            rw [hls] at hr; rw [he.rd]; show r ∈ s.rd; rw [rd]; simp [hr]))
          dw' := covers_of_mem (by rw [he.wr, wr]; simp)
          dsd := dsd
          lsd := fun r hr => (lsdt r (by rw [hls] at hr; exact hr)).1 }

/-- After the gathering. -/
structure Gathered (s g : State) : Prop where
  mem : g.mem = gMem s
  x8 : g.gpr .x8 = Dst s
  x9 : g.gpr .x9 = s.gpr .x7
  x10 : g.gpr .x10 = Tg s
  gpr : ∀ r, r ∉ gatherRegs → r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → r ≠ .x16 → g.gpr r = s.gpr r
  sp : g.sp = Bs s + BitVec.ofNat 64 1280
  rd : g.rd = s.rd
  wr : g.wr = FR s :: s.wr
  v : ∀ r ∈ preservedV, (g.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem gathered_wp {s e : State} (h : Lay s) (he : Entered s e) :
    WP isa Impl.AesGcm.AArch64.SealGather.gather e (Gathered s) := by
  refine WP.mono (WP.preservedV (gather_wp e (gatherPre_of h he)) (by lit_decide)) fun g ⟨⟨mg, kg⟩, vg⟩ => ?_
  rw [he.mem, h.hpt] at mg
  have hn : ∀ r, r ∉ gatherRegs → g.gpr r = e.gpr r := kg.gpr
  exact ⟨mg, (hn _ (by decide)).trans he.x8, (hn _ (by decide)).trans he.x9, (hn _ (by decide)).trans he.x10,
    fun r hg h₈ h₉ h₁₀ h₁₆ => (hn r hg).trans (he.gpr r (fun e => hg (by simp [e]))
      (fun e => hg (by simp [e])) h₈ h₉ h₁₀ (fun e => hg (by simp [e])) h₁₆),
    kg.sp.trans he.sp, kg.rd.trans he.rd, kg.wr.trans he.wr, fun r hr => (vg r hr).trans (he.v r hr)⟩

/-- Ready for the call. -/
structure Ready (s c : State) : Prop where
  mem : c.mem = gMem s
  x4 : c.gpr .x4 = Dst s
  x5 : c.gpr .x5 = s.gpr .x7
  x6 : c.gpr .x6 = Tg s
  gpr : ∀ r, r ≠ .x4 → r ≠ .x5 → r ∉ gatherRegs → r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → r ≠ .x16 → c.gpr r = s.gpr r
  sp : c.sp = Bs s + BitVec.ofNat 64 1280
  rd : c.rd = s.rd
  wr : c.wr = FR s :: s.wr
  v : ∀ r ∈ preservedV, (c.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem ready_wp {s g : State} (hg : Gathered s g) : WP isa (.block callArgs) g (Ready s) := by
  refine WP.mono (callArgs_ok g) fun c ⟨x4c, x5c, x6c, gc, mc, spc, rdc, wrc, vc⟩ => ?_
  exact ⟨mc.trans hg.mem, x4c.trans hg.x8, x5c.trans hg.x9, x6c.trans hg.x10,
    fun r h₄ h₅ hr h₈ h₉ h₁₀ h₁₆ => (gc r h₄ h₅ (fun e => hr (by simp [e]))).trans (hg.gpr r hr h₈ h₉ h₁₀ h₁₆),
    spc.trans hg.sp, rdc.trans hg.rd, wrc.trans hg.wr, fun r hr => by rw [vc]; exact hg.v r hr⟩

/-- The registers at the call. -/
theorem Ready.callGpr {s c : State} (hc : Ready s c) :
    c.callEntry.gpr .x0 = s.gpr .x0 ∧ c.callEntry.gpr .x1 = s.gpr .x1 ∧ c.callEntry.gpr .x2 = s.gpr .x2 ∧
      c.callEntry.gpr .x3 = s.gpr .x3 ∧ c.callEntry.gpr .x4 = Dst s ∧ c.callEntry.gpr .x5 = s.gpr .x7 ∧
      c.callEntry.gpr .x6 = Tg s := by
  have cg (r : Reg) (h₀ : r ∉ linkRegs) (h₄ : r ≠ .x4) (h₅ : r ≠ .x5) (hg : r ∉ gatherRegs) (h₈ : r ≠ .x8)
      (h₉ : r ≠ .x9) (h₁₀ : r ≠ .x10) (h₁₆ : r ≠ .x16) : c.callEntry.gpr r = s.gpr r := by
    rw [c.callEntry_gpr h₀, hc.gpr r h₄ h₅ hg h₈ h₉ h₁₀ h₁₆]
  exact ⟨cg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    cg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    cg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    cg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    by rw [c.callEntry_gpr (by decide), hc.x4], by rw [c.callEntry_gpr (by decide), hc.x5],
    by rw [c.callEntry_gpr (by decide), hc.x6]⟩

/-- What the call needs. -/
theorem Ready.call {s c : State} (h : Lay s) (hc : Ready s c) :
    callPre ((c.callEntry).withRegions (rdC s) (wrC s)) ∧ Covers (rdC s ++ wrC s) (c.rd ++ c.wr) ∧
      Covers (wrC s) c.wr := by
  obtain ⟨rd, wr, kd, kt, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, -, -, -, -, -, -, -, -,
    ok, on, oa, ods, ol, od, ot, w₁, w₂, hgl, hpm⟩ := h.pre
  obtain ⟨c0, c1, c2, c3, c4, c5, c6⟩ := hc.callGpr
  have hPn : (Bs s + BitVec.ofNat 64 1280).toNat = (Bs s).toNat + 1280 := by
    have := h.hBn
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith
  refine ⟨?_, ?_, ?_⟩
  · simp only [callPre, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, State.withRegions_sp,
      State.callEntry_sp, c0, c1, c2, c3, c4, c5, c6, hc.sp, BitVec.add_sub_cancel]
    refine ⟨trivial, trivial, kd, kt, nd, nt, ad, at_, dt, h.bk.sub_left (Region.sub_prefix (by decide)),
      h.bn.sub_left (Region.sub_prefix (by decide)), h.ba.sub_left (Region.sub_prefix (by decide)),
      h.bd.sub_left (Region.sub_prefix (by decide)), h.bt.sub_left (Region.sub_prefix (by decide)),
      ok, on, oa, od, ot, by omega_arith⟩
  · have inRd {r : Region} (h' : r ∈ [kR s, nR s, aR s]) : Covers [r] (c.rd ++ c.wr) := by
      refine covers_of_mem (List.mem_append_left _ ?_)
      rw [hc.rd, rd]; simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
      rcases h' with rfl | rfl | rfl <;> simp
    have hw' {r : Region} (h' : r ∈ [dR s, tgR s]) : Covers [r] (c.rd ++ c.wr) :=
      covers_of_mem (List.mem_append_right _ (by rw [hc.wr, wr]; exact List.mem_cons_of_mem _ h'))
    exact covers_append (covers_cons (inRd (r := kR s) (by simp)) (covers_cons (inRd (r := nR s) (by simp))
      (covers_cons (inRd (r := aR s) (by simp)) covers_nil)))
      (covers_cons (hw' (by simp)) (covers_cons (hw' (by simp)) covers_nil))
  · rw [hc.wr, wr]
    exact covers_cons (covers_of_mem (by simp)) (covers_cons (covers_of_mem (by simp)) covers_nil)

/-- After the call. -/
structure Called (s s' : State) : Prop where
  ra : s'.mem.read (Bs s + BitVec.ofNat 64 1288) 8 = s.gpr .x30
  out : encrypt (bytesAt (gMem s) (K s) 32) (bytesAt (gMem s) (Nn s) 12) (bytesAt (gMem s) (Ad s) (AL s))
      (bytesAt (gMem s) (Dst s) (L s)) = (bytesAt s'.mem (Dst s) (L s), bytesAt s'.mem (Tg s) 16)
  gpr : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  sp : s'.sp = Bs s + BitVec.ofNat 64 1280
  rd : s'.rd = s.rd
  wr : s'.wr = FR s :: s.wr
  v : ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem called_wp (F : SealFn) {s c : State} (h : Lay s) (hc : Ready s c) :
    WP isa (.call F.name F.code) c (Called s) := by
  obtain ⟨hcp, hcov, hw⟩ := hc.call h
  obtain ⟨c0, c1, c2, c3, c4, c5, c6⟩ := hc.callGpr
  have hdep := F.depth
  refine WP.callFV (name := F.name) F.verified.1 (sealSpec_pre hcp) hcov hw
    (fun s' rd' wr' sp' fr' pres' presV' post' => ?_) (by omega_arith)
  have hpost := sealSpec_post post'
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1, c2, c3, c4, c5, c6,
    hc.mem] at hpost
  have hpres : ∀ r ∈ preserved, r ≠ .x30 → r ≠ .x4 ∧ r ≠ .x5 ∧ r ∉ gatherRegs ∧ r ≠ .x8 ∧ r ≠ .x9 ∧
      r ≠ .x10 ∧ r ≠ .x16 := by decide
  -- The return address, from the frame, which the call kept.
  have ra : s'.mem.read (Bs s + BitVec.ofNat 64 1288) 8 = s.gpr .x30 := by
    have e : c.mem.read (Bs s + BitVec.ofNat 64 1288) 8 = s.gpr .x30 := by
      rw [hc.mem, h.gFrame 1288 (by decide)]
      exact read_write_self _ _ _
    rw [← e]
    refine Frame.read fr' (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact h.bd.symm.sub_right (stk_sub s 1288 8 (by decide)) |>.symm
    · exact h.bt.symm.sub_right (stk_sub s 1288 8 (by decide)) |>.symm
    · simp only [below, hc.sp, add_ofNat_sub_ofNat _ (show 16 * F.code.aarch64Depth ≤ 1280 by omega_arith)]
      exact Offset.disjoint _ (.inr (by omega_arith)) (by decide) (by have := h.hBn; omega_arith)
  exact ⟨ra, hpost, fun r hr h30 => by
      obtain ⟨h₄, h₅, hg, h₈, h₉, h₁₀, h₁₆⟩ := hpres r hr h30
      rw [pres' r hr h30, hc.gpr r h₄ h₅ hg h₈ h₉ h₁₀ h₁₆],
    sp'.trans hc.sp, rd'.trans hc.rd, wr'.trans hc.wr, fun r hr => (presV' r hr).trans (hc.v r hr)⟩

/-- The return address back in `x30`, and the frame freed. -/
theorem ret_wp {s s' : State} (h : Lay s) (hc : Called s s') :
    WP isa (.block [.ldrSp .x30 8]) s' fun z => ∀ m u, Frame [⟨s.sp - BitVec.ofNat 64 16, 16⟩] z.mem m →
      abiPreserved s { freed 16 z with mem := m, unknowns := u } ∧
        gatherPost s { freed 16 z with mem := m, unknowns := u } := by
  obtain ⟨rd, wr, kd, kt, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, -, -, -, -, -, -, -, -,
    ok, on, oa, ods, ol, od, ot, w₁, w₂, hgl, hpm⟩ := h.pre
  refine WP.mono (ldrSp_ok (t := .x30) (k := 8) s' (by decide) ?_) fun z ⟨x30z, gz, mz, spz, rdz, wrz, vz⟩ => ?_
  · rw [hc.sp, hc.rd, hc.wr, Offset.add_ofNat_add_ofNat]
    exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), contains_off _ (by decide) (by decide) (by decide)⟩
  rw [hc.sp, Offset.add_ofNat_add_ofNat, hc.ra] at x30z
  intro m u fl
  refine ⟨⟨fun r hr => ?_, ?_, fun r hr => ?_⟩, ?_⟩
  · -- The callee-saved registers.
    show z.gpr r = s.gpr r
    by_cases h30 : r = .x30
    · subst h30; exact x30z
    · rw [gz r h30, hc.gpr r hr h30]
  · -- The stack pointer.
    show z.sp + BitVec.ofNat 64 16 = s.sp
    rw [spz, hc.sp, Offset.add_ofNat_add_ofNat, h.hB]
  · -- The callee-saved vector registers.
    show (z.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
    rw [vz]; exact hc.v r hr
  · -- The ciphertext and the tag.
    show encrypt _ _ _ _ = (bytesAt m (Dst s) (L s), bytesAt m (Tg s) 16)
    -- The `free` loses the frame's bytes, which lie apart from the data and the tag.
    have e : s.sp - BitVec.ofNat 64 16 = Bs s + BitVec.ofNat 64 1280 := by
      rw [h.hB]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega_using []
    rw [e] at fl
    have hD : bytesAt m (Dst s) (L s) = bytesAt z.mem (Dst s) (L s) :=
      List.map_congr_left fun i hi =>
        lost_byte fl (R := dR s) (h.bd.symm.sub_right (stk_sub s 1280 16 (by decide))) (List.mem_range.mp hi)
    have hT : bytesAt m (Tg s) 16 = bytesAt z.mem (Tg s) 16 :=
      List.map_congr_left fun i hi =>
        lost_byte fl (R := tgR s) (h.bt.symm.sub_right (stk_sub s 1280 16 (by decide))) (List.mem_range.mp hi)
    rw [hD, hT, mz]
    have hfc : Frame [FR s, dR s] s.mem (gMem s) :=
      ((frame_eMem s).mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)).trans
        (h.frame_gMem.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp))
    have apart {r : Region} (h₁ : (⟨Bs s, 1296⟩ : Region).Disjoint r) (h₂ : r.Disjoint (dR s)) :
        ∀ r' ∈ [FR s, dR s], r.Disjoint r' := by
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact h₁.symm.sub_right (stk_sub s 1280 16 (by decide))
      · exact h₂
    have hk : bytesAt (gMem s) (K s) 32 = bytesAt s.mem (K s) 32 := bytesAt_frame hfc (apart h.bk kd) (by omega_arith)
    have hn : bytesAt (gMem s) (Nn s) 12 = bytesAt s.mem (Nn s) 12 := bytesAt_frame hfc (apart h.bn nd) (by omega_arith)
    have ha : bytesAt (gMem s) (Ad s) (AL s) = bytesAt s.mem (Ad s) (AL s) :=
      bytesAt_frame hfc (apart h.ba ad) (by omega_arith)
    have hd : bytesAt (gMem s) (Dst s) (L s) = pt s (Cnt s) := by
      rw [← h.hlen]
      exact bytesAt_writeBytes_self _ _ _ (by rw [h.hlen]; exact (s.gpr .x7).isLt)
    have := hc.out
    rw [hk, hn, ha, hd] at this
    exact this

theorem sealGather_wp (F : SealFn) {s : State} (hs : gatherPre s) :
    WP isa (sealGather F.name F.code) s fun z => abiPreserved s z ∧ gatherPost s z := by
  have h := lay hs
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by have := h.w₁; omega_arith) ?_
  refine WP.seq (WP.mono (entered_wp h) fun e he => ?_)
  refine WP.seq (WP.mono (gathered_wp h he) fun g hg => ?_)
  refine WP.seq (WP.mono (ready_wp hg) fun c hc => ?_)
  refine WP.seq (WP.mono (called_wp F h hc) fun s' hs' => ?_)
  exact ret_wp h hs'

end VG.Proof.ChaCha20Poly1305.AArch64.Gather

end

end

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, AArch64: constant time

Untrusted: everything here is checked by Lean. Two runs whose arguments and
descriptors agree (`gatherPub`) leak the same trace: the entry, the moves of
the call's arguments and the load of the return address are at the stack
pointer or between registers; the gathering is constant time by
`gather_rel` (`Proof/AesGcm/AArch64/Gather/LoopCT.lean`); and the call is
constant time by its callee's contract, whose public arguments agree
(`sealGather_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.AArch64.Gather

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.SealGather
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_taint ct_of)
open VG.Proof.AesGcm.AArch64.Gather (gather_rel)

theorem sealGather_ct (F : SealFn) : ConstantTime isa gatherPre gatherPub (sealGather F.name F.code) := by
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  have h₁ := lay p₁
  have h₂ := lay p₂
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qdit, a0, hdesc⟩ := hq
  have hB : Bs σ₁ = Bs σ₂ := by simp only [Bs, qsp]
  refine (RelCT.alloc (P := Eq2 σ₁ σ₂) (R := TT)
    ((?_ : RelCT isa (Eq2 (allocated 16 σ₁) (allocated 16 σ₂)) _ TT).mono
      (fun a b ⟨s, t, ⟨hs, ht⟩, ha, hb⟩ => by subst hs ht; exact ⟨ha, hb⟩) fun _ _ h => h)).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  -- The entry.
  refine rel_seq (rel_taint [] (by rw [allocated_sp h₁, allocated_sp h₂, hB]) (by agree_tac [])
    ⟨_, by taint_decide⟩) (WP.dit (by decide) (entered_wp h₁)) (WP.dit (by decide) (entered_wp h₂))
    fun e₁ e₂ ⟨he₁, ed₁⟩ ⟨he₂, ed₂⟩ => ?_
  -- The gathering.
  have g₁ := gatherPre_of h₁ he₁
  have g₂ := gatherPre_of h₂ he₂
  simp only [Src, Dst, Cnt, L, ← q4, ← q5, ← q6, ← q7] at g₂
  have hd : ∀ j < Cnt σ₁ * 16, e₁.mem (Src σ₁ + BitVec.ofNat 64 j) = e₂.mem (Src σ₁ + BitVec.ofNat 64 j) := by
    intro j hj
    have hx : (dsR σ₁).Contains (Src σ₁ + BitVec.ofNat 64 j) 1 :=
      Offset.contains_base _ hj (by have := h₁.ods; omega_using [hj, this])
    have hx₂ : (dsR σ₂).Contains (Src σ₁ + BitVec.ofNat 64 j) 1 := by
      simp only [dsR, Src, Cnt, ← q4, ← q5]; exact hx
    rw [he₁.mem, he₂.mem, Lay.keepE h₁.bds.symm hx, Lay.keepE h₂.bds.symm hx₂]
    exact hdesc j hj
  refine rel_seq (gather_rel hd g₁ g₂ (by rw [he₁.sp, he₂.sp, hB])) (WP.dit (by lit_decide) (gathered_wp h₁ he₁))
    (WP.dit (by lit_decide) (gathered_wp h₂ he₂)) fun u₁ u₂ ⟨hg₁, gd₁⟩ ⟨hg₂, gd₂⟩ => ?_
  -- The call's arguments.
  refine rel_seq (rel_taint [] (by rw [hg₁.sp, hg₂.sp, hB]) (by agree_tac []) ⟨_, by taint_decide⟩)
    (WP.dit (by decide) (ready_wp hg₁)) (WP.dit (by decide) (ready_wp hg₂))
    fun c₁ c₂ ⟨hc₁, cd₁⟩ ⟨hc₂, cd₂⟩ => ?_
  -- The call, by its callee's contract.
  have hrd : rdC σ₂ = rdC σ₁ := by simp only [rdC, kR, nR, aR, K, Nn, Ad, AL, q0, q1, q2, q3]
  have hwr : wrC σ₂ = wrC σ₁ := by simp only [wrC, dR, tgR, Dst, L, Tg, q6, q7, a0]
  obtain ⟨cp₁, cv₁, cw₁⟩ := hc₁.call h₁
  obtain ⟨cp₂, cv₂, cw₂⟩ := hc₂.call h₂
  rw [hrd, hwr] at cp₂ cv₂
  rw [hwr] at cw₂
  obtain ⟨r0₁, r1₁, r2₁, r3₁, r4₁, r5₁, r6₁⟩ := hc₁.callGpr
  obtain ⟨r0₂, r1₂, r2₂, r3₂, r4₂, r5₂, r6₂⟩ := hc₂.callGpr
  refine rel_seq (RelCT.call F.verified.1 F.verified.2.1 (rdC σ₁) (wrC σ₁) fun a b ⟨ha, hb⟩ => by
      subst ha hb
      refine ⟨sealSpec_pre cp₁, sealSpec_pre cp₂, sealSpec_pub ?_, cv₁, cw₁, cv₂, cw₂⟩
      simp only [State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp, r0₁, r1₁, r2₁, r3₁, r4₁, r5₁,
        r6₁, r0₂, r1₂, r2₂, r3₂, r4₂, r5₂, r6₂, hc₁.sp, hc₂.sp, hB, q0, q1, q2, q3, Dst, Tg, q6, q7, a0,
        State.withRegions_dit, State.callEntry_dit, cd₁, cd₂, gd₁, gd₂, ed₁, ed₂, allocated_dit, qdit, and_self])
    (called_wp F h₁ hc₁) (called_wp F h₂ hc₂) fun z₁ z₂ hz₁ hz₂ => ?_
  -- The return address.
  exact rel_taint [] (by rw [hz₁.sp, hz₂.sp, hB]) (by agree_tac []) ⟨_, by taint_decide⟩

end VG.Proof.ChaCha20Poly1305.AArch64.Gather
