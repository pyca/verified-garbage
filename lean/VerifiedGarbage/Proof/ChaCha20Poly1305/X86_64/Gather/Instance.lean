module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Split.FnCT
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.CT
import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Gcm.OutOfPlaceContract
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Shared
public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Verified
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchWipe
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Lit
public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.SealGather
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.LoopCT
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Algebra.Group.Nat.Defs
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.CT
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.LoopCT
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.CT
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Shared
meta import Mathlib.Tactic.NormNum.Pow
meta import Mathlib.Tactic.NormNum.Inv
meta import Mathlib.Algebra.Group.Nat.Defs
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Impl.Gcm.X86_64
meta import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Env
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Run
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Verified
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.RoundsVL
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Last
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Xor
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.XorBuf
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Gcm.Ctr
meta import VerifiedGarbage.Proof.Gcm.Spec
meta import VerifiedGarbage.Proof.Gcm.Stream
meta import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.ChaCha20Poly1305.Gathered
import VerifiedGarbage.Proof.AesGcm.ScratchGather
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.Aes.KeyExp
public import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace
public import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.Gathered
meta import VerifiedGarbage.Proof.AesGcm.ScratchGather
meta import VerifiedGarbage.Proof.Framework.X86_64.Frame
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Gcm.SealGather
meta import VerifiedGarbage.Proof.Framework.X86_64.CallSp
meta import VerifiedGarbage.Proof.Aes.KeyExp
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.Depth
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
meta import VerifiedGarbage.Proof.Aes.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace
meta import VerifiedGarbage.Proof.Framework.X86_64.Call

/-! ### `ChaCha20Poly1305.X86_64.Gather.By`, which this module and modules that import it used -/

section

/-! ### `ChaCha20Poly1305.X86_64.Gather.Whole.CT`, which this module and modules that import it used -/

section

/-! ### `ChaCha20Poly1305.X86_64.Gather.Whole.Fn`, which this module and modules that import it used -/

section

/-! ### `ChaCha20Poly1305.X86_64.Gather.Whole.Contract`, which this module and modules that import it used -/

section

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86-64: the contract

Untrusted: everything here is checked by Lean. The contract the proof of
`vg_chacha20_poly1305_seal_gather` is written against, which the shared one
(`Spec.ChaCha20Poly1305.sealGatherContract`, with the 1832 bytes of stack
below the stack pointer that its frames and its call use) implies
(`Gather/Verified.lean`): `(key = rdi, nonce = rsi, aad = rdx,
aad_len = rcx, src = r8, src_count = r9, dst = [rsp + 8], len = [rsp + 16],
tag = [rsp + 24])`.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Gather.Whole

open VG VG.X86_64
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20Poly1305 (encrypt gathered gatheredLen pMax)

section
variable (s : State)

/-- The arguments. -/
abbrev K : Addr := s.gpr .rdi
abbrev Nn : Addr := s.gpr .rsi
abbrev Ad : Addr := s.gpr .rdx
abbrev AL : Nat := (s.gpr .rcx).toNat
abbrev Src : Addr := s.gpr .r8
abbrev Cnt : Nat := (s.gpr .r9).toNat
abbrev Dst : Addr := stackArg s 0
abbrev L : Nat := (stackArg s 1).toNat
abbrev Tg : Addr := stackArg s 2
abbrev SP : Addr := s.gpr .rsp

/-- The regions: the key, the nonce, the additional data, the descriptors,
the slices they list, the output, the tag, the stack arguments, the return
address and the stack below it. -/
abbrev kR : Region := ⟨K s, 32⟩
abbrev nR : Region := ⟨Nn s, 12⟩
abbrev aR : Region := ⟨Ad s, AL s⟩
abbrev dsR : Region := ⟨Src s, Cnt s * 16⟩
abbrev lsR : List Region := Sig.listed 64 s.mem .u8 (Src s) (Cnt s)
abbrev dR : Region := ⟨Dst s, L s⟩
abbrev tgR : Region := ⟨Tg s, 16⟩
abbrev argR : Region := ⟨stackArgAddr s 0, 24⟩
abbrev retR : Region := ⟨SP s, 8⟩
abbrev stkR : Region := below (SP s) 1832

/-- The total length of the first `i` slices, and their bytes. -/
abbrev gl (i : Nat) : Nat := gatheredLen 64 s.mem (Src s) i
abbrev pt (i : Nat) : List Byte := gathered 64 s.mem (Src s) i

end

/-- What the code of `vg_chacha20_poly1305_seal_gather` needs. -/
def gatherPre (s : State) : Prop :=
  s.rd = [kR s, nR s, aR s, dsR s] ++ lsR s ++ [argR s] ∧ s.wr = [dR s, tgR s] ∧
    (kR s).Disjoint (dR s) ∧ (kR s).Disjoint (tgR s) ∧ (nR s).Disjoint (dR s) ∧ (nR s).Disjoint (tgR s) ∧
    (aR s).Disjoint (dR s) ∧ (aR s).Disjoint (tgR s) ∧ (dR s).Disjoint (tgR s) ∧
    (dR s).Disjoint (dsR s) ∧ (∀ r ∈ lsR s, (dR s).Disjoint r) ∧ (dR s).Disjoint (argR s) ∧
    (retR s).Disjoint (dR s) ∧ (retR s).Disjoint (tgR s) ∧
    (stkR s).Disjoint (kR s) ∧ (stkR s).Disjoint (nR s) ∧ (stkR s).Disjoint (aR s) ∧
    (stkR s).Disjoint (dR s) ∧ (stkR s).Disjoint (tgR s) ∧ (stkR s).Disjoint (dsR s) ∧
    (∀ r ∈ lsR s, (stkR s).Disjoint r) ∧
    (K s).toNat + 32 ≤ 2 ^ 64 ∧ (Nn s).toNat + 12 ≤ 2 ^ 64 ∧ (Ad s).toNat + AL s ≤ 2 ^ 64 ∧
    (Dst s).toNat + L s ≤ 2 ^ 64 ∧ (Tg s).toNat + 16 ≤ 2 ^ 64 ∧
    (Src s).toNat + Cnt s * 16 ≤ 2 ^ 64 ∧ (∀ r ∈ lsR s, r.base.toNat + r.len ≤ 2 ^ 64) ∧
    1832 ≤ (SP s).toNat ∧ (SP s).toNat + 32 ≤ 2 ^ 64 ∧ gl s (Cnt s) = L s ∧ L s ≤ pMax

/-- What two runs agree on: the arguments and the descriptors. -/
def gatherPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.mxcsr = s₂.mxcsr ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
    stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧
    ∀ i < Cnt s₁ * 16, s₁.mem (Src s₁ + BitVec.ofNat 64 i) = s₂.mem (Src s₁ + BitVec.ofNat 64 i)

/-- What `vg_chacha20_poly1305_seal_gather` leaves: `sealGatherPost`. -/
def gatherPost (s s' : State) : Prop :=
  encrypt (bytesAt s.mem (K s) 32) (bytesAt s.mem (Nn s) 12) (bytesAt s.mem (Ad s) (AL s)) (pt s (Cnt s)) =
    (bytesAt s'.mem (Dst s) (L s), bytesAt s'.mem (Tg s) 16)

end VG.Proof.ChaCha20Poly1305.X86_64.Gather.Whole

end

end

/-! ### `ChaCha20Poly1305.X86_64.Gather.Whole.Callee`, which this module and modules that import it used -/

section

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86-64: the function called

Untrusted: everything here is checked by Lean. `vg_chacha20_poly1305_seal_gather`
calls an instance of `vg_chacha20_poly1305_seal` as an artifact (`SealFn`),
with its working space in a frame of its own, so what the proof needs of it
is its shared contract (`Spec.ChaCha20Poly1305.sealContract`, with 1768
bytes of stack): its precondition from the layout the call gives it
(`callPre`, `sealSpec_pre`), its postcondition (`sealSpec_post`) and its
public data (`sealSpec_pub`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Gather.Whole

open VG VG.X86_64
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20Poly1305 (encrypt)

/-- An instance of `vg_chacha20_poly1305_seal`, by its shared contract, which
writes `rsp` only in its frames, whose frames and calls use at most the 1768
bytes below the stack pointer that the contract reserves. -/
structure SealFn where
  name : String
  code : Prog isa
  verified : Verified X86_64.target code (Spec.ChaCha20Poly1305.sealContract X86_64.abi 1768)
  sp : SpSafe code
  depth : code.x86_64Depth ≤ 1768
  /-- What else its runs leave, from the state it is called in to the memory
  it returns with: nothing to say (`True`), but where its caller's clearing
  needs what it leaves on the stack. -/
  E : State → Mem → Prop
  exec : ∀ s, (Spec.ChaCha20Poly1305.sealContract X86_64.abi 1768).pre s → ∃ t s', Exec isa code s t s' ∧
      abiPreserved s s' ∧ (Spec.ChaCha20Poly1305.sealContract X86_64.abi 1768).post s s' ∧ E s s'.mem

/-- The contract `SealFn.exec` states, `seal`'s with `E`. -/
def SealFn.contractE (F : SealFn) : Contract isa where
  pre := (Spec.ChaCha20Poly1305.sealContract X86_64.abi 1768).pre
  post s s' := (Spec.ChaCha20Poly1305.sealContract X86_64.abi 1768).post s s' ∧ F.E s s'.mem
  pub := (Spec.ChaCha20Poly1305.sealContract X86_64.abi 1768).pub

/-- What a call of `vg_chacha20_poly1305_seal(key = rdi, nonce = rsi,
aad = rdx, aad_len = rcx, data = r8, len = r9, tag = [rsp + 8])` needs. -/
def callPre (s : State) : Prop :=
  let key : Region := ⟨s.gpr .rdi, 32⟩
  let nonce : Region := ⟨s.gpr .rsi, 12⟩
  let aad : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let data : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let tag : Region := ⟨stackArg s 0, 16⟩
  let args : Region := ⟨stackArgAddr s 0, 8⟩
  let ret : Region := ⟨s.gpr .rsp, 8⟩
  let stk : Region := below (s.gpr .rsp) 1768
  1768 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 16 ≤ 2 ^ 64 ∧
    s.rd = [key, nonce, aad, args] ∧ s.wr = [data, tag] ∧
    key.Disjoint data ∧ key.Disjoint tag ∧ nonce.Disjoint data ∧ nonce.Disjoint tag ∧
    aad.Disjoint data ∧ aad.Disjoint tag ∧ data.Disjoint tag ∧ data.Disjoint args ∧ tag.Disjoint args ∧
    ret.Disjoint key ∧ ret.Disjoint nonce ∧ ret.Disjoint aad ∧ ret.Disjoint data ∧ ret.Disjoint tag ∧
    ret.Disjoint args ∧
    stk.Disjoint key ∧ stk.Disjoint nonce ∧ stk.Disjoint aad ∧ stk.Disjoint data ∧ stk.Disjoint tag ∧
    stk.Disjoint args ∧
    (s.gpr .rdi).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 12 ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + 16 ≤ 2 ^ 64

theorem sealSpec_pre {s : State} (h : callPre s) :
    (Spec.ChaCha20Poly1305.sealContract X86_64.abi 1768).pre s := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁,
    a₂₂, a₂₃, a₂₄, a₂₅, a₂₆, a₂₇, a₂₈, a₂₉, a₃₀⟩ := h
  sig_pre [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, X86_64.abi, X86_64.argRegs]
  sig_reduce [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below]
  sig_and_intros
  all_goals simp only [X86_64.stackArg, X86_64.stackArgAddr, VG.X86_64.below, Nat.mul_one] at *
  all_goals first
    | with_reducible assumption
    | trivial
    | omega
    | exact Region.Disjoint.symm ‹_›

theorem sealSpec_post {s s' : State} (h : (Spec.ChaCha20Poly1305.sealContract X86_64.abi 1768).post s s') :
    encrypt (bytesAt s.mem (s.gpr .rdi) 32) (bytesAt s.mem (s.gpr .rsi) 12)
        (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) =
      (bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat, bytesAt s'.mem (stackArg s 0) 16) := by
  sig_post [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig,
    Spec.ChaCha20Poly1305.sealPost, X86_64.abi, X86_64.argRegs] at h
  sig_reduce [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h

theorem sealSpec_pub {s₁ s₂ : State} (h : s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ s₁.mxcsr = s₂.mxcsr) :
    (Spec.ChaCha20Poly1305.sealContract X86_64.abi 1768).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, aMd⟩ := h
  sig_pub [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, X86_64.abi, X86_64.argRegs]
  sig_reduce [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop]
  simp only [X86_64.stackArg, X86_64.stackArgAddr] at a₈
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

end VG.Proof.ChaCha20Poly1305.X86_64.Gather.Whole

end

end

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86-64: the function

Untrusted: everything here is checked by Lean. With `B` the base of the
1832 bytes of stack below the stack pointer (`rsp = B + 1832`),
`vg_chacha20_poly1305_seal_gather` pushes the six argument registers in its
frame at `B + 1784` (`pushed`), puts `src` in `r11` and `dst` in `rdi`
(`entered_wp`), gathers the slices to `dst` (`gathered_wp`, `gather_wp`),
loads the call's arguments from the frame and the stack arguments
(`ready_wp`), and calls `vg_chacha20_poly1305_seal` on them in place with
`tag` pushed at `B + 1776` (`called_wp`, by its shared contract); the call
keeps our frame and the return address above it.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Gather.Whole

open VG VG.X86_64 VG.X86_64.RegUpd VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm)
open VG.Impl.ChaCha20Poly1305.X86_64.SealGather (Width entry gather callArgsWhole sealGatherWhole)
open VG.Proof.AesGcm.X86_64 (offset_nat)
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20Poly1305 (encrypt gathered gatheredLen pMax)
open VG.Proof.ChaCha20Poly1305 (bytesAt_frame bytesAt_writeBytes_self)

/-- The argument registers our frame keeps. -/
abbrev saved : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r9]

/-! ## The blocks -/

/-- `entry`: `src` into `r11`, and `dst` (`[rsp + 56]`) into `rdi`. -/
theorem entry_ok (a : State) {P : Addr} (hsp : a.gpr .rsp = P)
    (r₅₆ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 56) 8) :
    WP isa (.block entry) a fun e => e.gpr .r11 = a.gpr .r8 ∧
      e.gpr .rdi = a.mem.readW (P + BitVec.ofNat 64 56) 64 ∧
      (∀ r, r ≠ .r11 → r ≠ .rdi → e.gpr r = a.gpr r) ∧ e.mem = a.mem ∧ e.rd = a.rd ∧ e.wr = a.wr := by
  apply WP.of_runBlock
  refine ⟨_, by xrun [entry, hsp, r₅₆], ?_⟩
  exact ⟨by simp [gpr_setReg], by simp [gpr_setReg], fun r h₁ h₂ => by simp [gpr_setReg, h₁, h₂], rfl, rfl, rfl⟩

/-- `callArgsWhole`: the call's arguments, from the frame and our stack arguments. -/
theorem callArgs_ok (a : State) {P : Addr} (hsp : a.gpr .rsp = P)
    (r₁₆ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 16) 8)
    (r₂₄ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 24) 8)
    (r₃₂ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 32) 8)
    (r₄₀ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 40) 8)
    (r₅₆ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 56) 8)
    (r₆₄ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 64) 8)
    (r₇₂ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 72) 8) :
    WP isa (.block callArgsWhole) a fun e => e.gpr .rdi = a.mem.readW (P + BitVec.ofNat 64 40) 64 ∧
      e.gpr .rsi = a.mem.readW (P + BitVec.ofNat 64 32) 64 ∧
      e.gpr .rdx = a.mem.readW (P + BitVec.ofNat 64 24) 64 ∧
      e.gpr .rcx = a.mem.readW (P + BitVec.ofNat 64 16) 64 ∧
      e.gpr .r8 = a.mem.readW (P + BitVec.ofNat 64 56) 64 ∧
      e.gpr .r9 = a.mem.readW (P + BitVec.ofNat 64 64) 64 ∧
      e.gpr .rax = a.mem.readW (P + BitVec.ofNat 64 72) 64 ∧
      (∀ r ∈ calleeSaved, e.gpr r = a.gpr r) ∧ e.mem = a.mem ∧ e.rd = a.rd ∧ e.wr = a.wr := by
  apply WP.of_runBlock
  refine ⟨_, by xrun [callArgsWhole, hsp, r₁₆, r₂₄, r₃₂, r₄₀, r₅₆, r₆₄, r₇₂], ?_⟩
  refine ⟨by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg],
    by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg], fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]

/-! ## The layout -/

section
variable (s : State)

/-- The base of the 1832 bytes of stack below the stack pointer. -/
abbrev Bs : Addr := s.gpr .rsp - BitVec.ofNat 64 1832

/-- Our frame. -/
abbrev FR : Region := ⟨Bs s + BitVec.ofNat 64 1784, 48⟩

/-- The memory after the push of our frame. -/
abbrev eM : Mem := (pushed saved s).mem

/-- The memory once the slices are gathered at `dst`. -/
abbrev gM : Mem := writeBytes (eM s) (Dst s) (pt s (Cnt s))

/-- The regions the call of `vg_chacha20_poly1305_seal` reads (with `tag`
pushed for it) and writes. -/
abbrev rdC : List Region := [kR s, nR s, aR s, ⟨Bs s + BitVec.ofNat 64 1776, 8⟩]
abbrev wrC : List Region := [dR s, tgR s]

end

theorem add_ofNat_sub_ofNat (B : Addr) {a b : Nat} (h : b ≤ a) :
    B + BitVec.ofNat 64 a - BitVec.ofNat 64 b = B + BitVec.ofNat 64 (a - b) := by
  rw [← Offset.ofNat_sub_ofNat h, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]

/-- What `gatherPre` gives, with the stack below the stack pointer at `Bs s`. -/
structure Lay (s : State) : Prop where
  pre : gatherPre s
  hB : s.gpr .rsp = Bs s + BitVec.ofNat 64 1832
  hBn : (Bs s).toNat + 1864 ≤ 2 ^ 64
  hBv : (Bs s).toNat = (s.gpr .rsp).toNat - 1832

theorem lay {s : State} (hs : gatherPre s) : Lay s := by
  have w₁ : 1832 ≤ (s.gpr .rsp).toNat := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have w₂ : (s.gpr .rsp).toNat + 32 ≤ 2 ^ 64 := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hBv : (Bs s).toNat = (s.gpr .rsp).toNat - 1832 := toNat_sub_ofNat w₁
  exact ⟨hs, (BitVec.sub_add_cancel _ _).symm, by omega_arith, hBv⟩

/-- Parts of the stack below the stack pointer. -/
theorem stk_sub (s : State) (d n : Nat) (h' : d + n ≤ 1832) :
    (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Sub (stkR s) :=
  Offset.sub_base _ h'

theorem covers_of_mem' {r : Region} {ts : List Region} (h : r ∈ ts) : Covers [r] ts := by
  intro a n ⟨x, hx, hc⟩
  simp only [List.mem_singleton] at hx; subst hx; exact ⟨x, h, hc⟩

theorem hP (s : State) : (pushed saved s).gpr .rsp = Bs s + BitVec.ofNat 64 1784 := by
  rw [pushed_rsp, Offset.sub_ofNat_eq _ (show 8 * saved.length ≤ 1832 by decide)]; rfl

theorem hPwr (s : State) : (pushed saved s).wr = FR s :: s.wr := by
  rw [pushed_wr, Offset.sub_ofNat_eq _ (show 8 * saved.length ≤ 1832 by decide)]; rfl

theorem fr_sub (s : State) : (FR s).Sub (stkR s) := stk_sub s 1784 48 (by decide)

namespace Lay

variable {s : State} (h : Lay s)
include h

theorem w₁ : 1832 ≤ (s.gpr .rsp).toNat := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The stack arguments. -/
theorem argAddr (i : Nat) : stackArgAddr s i = Bs s + BitVec.ofNat 64 (1840 + 8 * i) := by
  show s.gpr .rsp + BitVec.ofNat 64 (8 * (i + 1)) = _
  rw [h.hB, Offset.add_ofNat_add_ofNat]; congr 2; omega_arith

theorem hargR : argR s = ⟨Bs s + BitVec.ofNat 64 1840, 24⟩ := by
  show (⟨stackArgAddr s 0, 24⟩ : Region) = _
  rw [h.argAddr]

theorem pushes : Frame [FR s] s.mem (eM s) ∧
    ∀ j (hj : j < saved.length), (eM s).readW (s.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64 = s.gpr saved[j] := by
  have := pushRegs_mem s saved (by decide) (by have := h.w₁; simp only [List.length_cons, List.length_nil]; omega_arith)
  rw [Offset.sub_ofNat_eq _ (show 8 * saved.length ≤ 1832 by decide)] at this
  exact this

theorem frame_eM : Frame [FR s] s.mem (eM s) := h.pushes.1

/-- The words of our frame: the argument registers. -/
theorem pushedW (j : Nat) (hj : j < 6) (d : Nat) (hd : d + 8 * (j + 1) = 1832) :
    (eM s).readW (Bs s + BitVec.ofNat 64 d) 64 = s.gpr (saved[j]'hj) := by
  have := h.pushes.2 j hj
  rw [Offset.sub_ofNat_eq _ (show 8 * (j + 1) ≤ 1832 by omega_arith), show 1832 - 8 * (j + 1) = d by omega_arith] at this
  exact this

/-- The memory the push left outside the frame. -/
theorem keepE {r : Region} (hr : r.Disjoint (stkR s)) {x : Addr} (hx : r.Contains x 1) : eM s x = s.mem x :=
  h.frame_eM x fun r' hr' hc => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hr x hx (fr_sub s x hc)

/-- The descriptors and the slices, after the push. -/
theorem hag : ∀ r ∈ Sig.descRegion 64 (Src s) (Cnt s) :: lsR s, ∀ x, r.Contains x 1 → s.mem x = eM s x := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, bds, bls, -⟩ := h.pre
  intro r hr x hx
  refine (h.keepE ?_ hx).symm
  rcases List.mem_cons.mp hr with rfl | hr
  · exact bds.symm
  · exact (bls r hr).symm

theorem hpt : Spec.Gcm.gathered 64 (eM s) (Src s) (Cnt s) = pt s (Cnt s) :=
  Proof.AesGcm.gathered_congr_le (Nat.le_refl _) h.hag

theorem hlen : (pt s (Cnt s)).length = L s :=
  (Proof.Gcm.length_gathered _ _ _ _).trans h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem frame_gM : Frame [dR s] (eM s) (gM s) := by
  refine writeBytes_frame _ _ _ ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, h.hlen, Nat.le_refl]

/-- A word of the stack, once the slices are gathered. -/
theorem gFrame (d : Nat) (hd : d + 8 ≤ 1832) :
    (gM s).readW (Bs s + BitVec.ofNat 64 d) 64 = (eM s).readW (Bs s + BitVec.ofNat 64 d) 64 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, bd, -⟩ := h.pre
  refine Frame.readW h.frame_gM (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact bd.sub_left (stk_sub s d 8 hd)

/-- A stack argument, once the slices are gathered. -/
theorem gArg (i : Nat) (hi : i < 3) :
    (gM s).readW (Bs s + BitVec.ofNat 64 (1840 + 8 * i)) 64 = stackArg s i := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, darg, -⟩ := h.pre
  have hBn := h.hBn
  have hs : Region.Sub ⟨Bs s + BitVec.ofNat 64 (1840 + 8 * i), 8⟩ (argR s) := by
    rw [h.hargR]; exact Offset.sub _ (by omega_arith) (by omega_arith)
  rw [Frame.readW h.frame_gM (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact darg.symm.sub_left hs) (by decide)]
  rw [Frame.readW h.frame_eM (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide)]
  rw [← h.argAddr]; rfl

end Lay

/-! ## The phases -/

/-- After the push and the entry. -/
structure Entered (s e : State) : Prop where
  mem : e.mem = eM s
  r11 : e.gpr .r11 = Src s
  rdi : e.gpr .rdi = Dst s
  gpr : ∀ r, r ≠ .r11 → r ≠ .rdi → r ≠ .rsp → e.gpr r = s.gpr r
  rsp : e.gpr .rsp = Bs s + BitVec.ofNat 64 1784
  rd : e.rd = s.rd
  wr : e.wr = FR s :: s.wr
  mx : e.mxcsr = s.mxcsr

theorem entered_wp {s : State} (h : Lay s) : WP isa (.block entry) (pushed saved s) (Entered s) := by
  have hBn := h.hBn
  have r₅₆ : InRegions ((pushed saved s).rd ++ (pushed saved s).wr)
      (Bs s + BitVec.ofNat 64 1784 + BitVec.ofNat 64 56) 8 := by
    rw [pushed_rd, Offset.add_ofNat_add_ofNat]
    refine ⟨argR s, List.mem_append_left _ (by rw [h.pre.1]; simp), ?_⟩
    rw [h.hargR]; exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)
  refine WP.mono_mx (by decide +kernel) (entry_ok (pushed saved s) (hP s) r₅₆)
    fun e ⟨r11e, rdie, ge, me, rde, wre⟩ mxe => ?_
  refine ⟨me, by rw [r11e, pushed_gpr _ _ (by decide)], ?_, fun r h₁ h₂ h₃ => ?_, ?_, by rw [rde, pushed_rd],
    by rw [wre, hPwr s], by rw [mxe, pushed_mxcsr]⟩
  · rw [rdie, Offset.add_ofNat_add_ofNat, Frame.readW h.frame_eM (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide)]
    show _ = s.mem.readW (stackArgAddr s 0) 64
    rw [h.argAddr]
  · rw [ge r h₁ h₂, pushed_gpr _ _ h₃]
  · rw [ge _ (by decide) (by decide), hP s]

/-- `gather`'s precondition after the entry. -/
theorem gatherPre_of {s e : State} (h : Lay s) (he : Entered s e) : GatherPre e (Src s) (Dst s) (Cnt s) (L s) := by
  obtain ⟨rd, wr, -, -, -, -, -, -, -, dds, dls, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ods, -, -, -, hgl,
    hpm⟩ := h.pre
  obtain ⟨hls, -⟩ := Proof.AesGcm.listed_congr_le (Nat.le_refl _) h.hag
  rw [← he.mem] at hls
  have hpm' : L s ≤ 64 * (2 ^ 32 - 1) := hpm
  exact { r11 := he.r11
          r9 := by rw [he.gpr _ (by decide) (by decide) (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
          rdi := he.rdi
          hcnt := (s.gpr .r9).isLt
          dw := ods
          lt := by omega_arith
          len := by rw [he.mem, Proof.AesGcm.gatheredLen_congr_le (Nat.le_refl _) h.hag]; exact hgl
          dsr := covers_of_mem' (List.mem_append_left _ (by rw [he.rd, rd]; simp))
          lsr := fun r hr => covers_of_mem' (List.mem_append_left _ (by
            rw [hls] at hr; rw [he.rd, rd]; simp [hr]))
          dw' := covers_of_mem' (by rw [he.wr, wr]; simp)
          dsd := dds.symm
          lsd := fun r hr => (dls r (by rw [hls] at hr; exact hr)).symm }

/-- After the gathering. -/
structure Gathered (s g : State) : Prop where
  mem : g.mem = gM s
  gpr : ∀ r, r ∉ gatherRegs → r ≠ .rsp → g.gpr r = s.gpr r
  rsp : g.gpr .rsp = Bs s + BitVec.ofNat 64 1784
  rd : g.rd = s.rd
  wr : g.wr = FR s :: s.wr
  mx : g.mxcsr = s.mxcsr

theorem gathered_wp (w : Width) {s e : State} (h : Lay s) (he : Entered s e) : WP isa (gather w) e (Gathered s) := by
  refine WP.mono_mx (by cases w <;> decide +kernel) (gather_wp w e (gatherPre_of h he)) fun g ⟨mg, kg⟩ mxg => ?_
  rw [he.mem, h.hpt] at mg
  exact ⟨mg, fun r hr hsp => (kg.gpr r hr).trans (he.gpr r (fun e => hr (by simp [e]))
      (fun e => hr (by simp [e])) hsp),
    (kg.gpr _ (by decide)).trans he.rsp, kg.rd.trans he.rd, kg.wr.trans he.wr, mxg.trans he.mx⟩

/-- Ready for the call. -/
structure Ready (s c : State) : Prop where
  mem : c.mem = gM s
  rdi : c.gpr .rdi = K s
  rsi : c.gpr .rsi = Nn s
  rdx : c.gpr .rdx = Ad s
  rcx : c.gpr .rcx = s.gpr .rcx
  r8 : c.gpr .r8 = Dst s
  r9 : c.gpr .r9 = stackArg s 1
  rax : c.gpr .rax = Tg s
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → c.gpr r = s.gpr r
  rsp : c.gpr .rsp = Bs s + BitVec.ofNat 64 1784
  rd : c.rd = s.rd
  wr : c.wr = FR s :: s.wr
  mx : c.mxcsr = s.mxcsr

theorem ready_wp {s g : State} (h : Lay s) (hg : Gathered s g) : WP isa (.block callArgsWhole) g (Ready s) := by
  have hBn := h.hBn
  have inFr (d : Nat) (hd : d + 8 ≤ 48) :
      InRegions (g.rd ++ g.wr) (Bs s + BitVec.ofNat 64 1784 + BitVec.ofNat 64 d) 8 := by
    rw [hg.wr, Offset.add_ofNat_add_ofNat]
    exact ⟨FR s, List.mem_append_right _ (List.mem_cons_self ..), Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)⟩
  have inArg (d : Nat) (h₁ : 56 ≤ d) (hd : d + 8 ≤ 80) :
      InRegions (g.rd ++ g.wr) (Bs s + BitVec.ofNat 64 1784 + BitVec.ofNat 64 d) 8 := by
    rw [hg.rd, Offset.add_ofNat_add_ofNat]
    refine ⟨argR s, List.mem_append_left _ (by rw [h.pre.1]; simp), ?_⟩
    rw [h.hargR]; exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)
  refine WP.mono_mx (by decide +kernel) (callArgs_ok g hg.rsp (inFr 16 (by decide)) (inFr 24 (by decide))
      (inFr 32 (by decide)) (inFr 40 (by decide)) (inArg 56 (by decide) (by decide))
      (inArg 64 (by decide) (by decide)) (inArg 72 (by decide) (by decide)))
    fun c ⟨rdic, rsic, rdxc, rcxc, r8c, r9c, raxc, csc, mc, rdc, wrc⟩ mxc => ?_
  simp only [Offset.add_ofNat_add_ofNat, Nat.reduceAdd, hg.mem] at rdic rsic rdxc rcxc r8c r9c raxc
  have g56 := h.gArg 0 (by decide)
  have g64 := h.gArg 1 (by decide)
  have g72 := h.gArg 2 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at g56 g64 g72
  refine ⟨mc.trans hg.mem, ?_, ?_, ?_, ?_, r8c.trans g56, r9c.trans g64, raxc.trans g72, fun r hr hsp => ?_,
    (csc _ (by decide)).trans hg.rsp, rdc.trans hg.rd, wrc.trans hg.wr, mxc.trans hg.mx⟩
  · rw [rdic, h.gFrame 1824 (by decide)]; exact h.pushedW 0 (by decide) 1824 rfl
  · rw [rsic, h.gFrame 1816 (by decide)]; exact h.pushedW 1 (by decide) 1816 rfl
  · rw [rdxc, h.gFrame 1808 (by decide)]; exact h.pushedW 2 (by decide) 1808 rfl
  · rw [rcxc, h.gFrame 1800 (by decide)]; exact h.pushedW 3 (by decide) 1800 rfl
  · rw [csc r hr]
    refine hg.gpr r (fun hm => ?_) hsp
    simp only [calleeSaved, gatherRegs, List.mem_cons, List.not_mem_nil, or_false] at hr hm
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hm

/-! ## The call -/

section
variable (c : State)

/-- The state the body of the call's frame starts in: `tag` pushed. -/
abbrev qS : State := pushed [.rax] c

end

/-- The state the callee starts in, given the regions it reads and writes. -/
abbrev xS (s c : State) : State := (qS c).callEntry.withRegions (rdC s) (wrC s)

theorem xgpr_eq {s c : State} {r : Reg} (hr : r ≠ .rsp) : (xS s c).gpr r = c.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr _ _ hr]

section
variable {s c : State} (h : Lay s) (hc : Ready s c)
include h hc

omit h in
theorem Ready.qsp : (qS c).gpr .rsp = Bs s + BitVec.ofNat 64 1776 := by
  rw [pushed_rsp, hc.rsp, show 8 * [Reg.rax].length = 8 from rfl, add_ofNat_sub_ofNat _ (by decide)]

omit h in
theorem Ready.qwr : (qS c).wr = ⟨Bs s + BitVec.ofNat 64 1776, 8⟩ :: FR s :: s.wr := by
  rw [pushed_wr, hc.rsp, hc.wr, show 8 * [Reg.rax].length = 8 from rfl, add_ofNat_sub_ofNat _ (by decide)]

omit h in
theorem Ready.qrd : (qS c).rd = s.rd := by rw [pushed_rd, hc.rd]

theorem Ready.hn : 8 * [Reg.rax].length ≤ (c.gpr .rsp).toNat := by
  have := h.hBn
  rw [hc.rsp, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 1784) (by decide),
    Nat.mod_eq_of_lt (by omega_arith)]
  simp only [List.length_cons, List.length_nil]; omega_arith

/-- The push of `tag`. -/
theorem Ready.qmem : Frame [⟨Bs s + BitVec.ofNat 64 1776, 8⟩] c.mem (qS c).mem ∧
    (qS c).mem.readW (Bs s + BitVec.ofNat 64 1776) 64 = Tg s := by
  have := pushRegs_mem c [.rax] (by decide) (hc.hn h)
  have h₁ := this.1
  have h₂ := this.2 0 (by decide)
  rw [hc.rsp, show 8 * [Reg.rax].length = 8 from rfl, add_ofNat_sub_ofNat _ (by decide)] at h₁
  rw [hc.rsp, show 8 * (0 + 1) = 8 from rfl, add_ofNat_sub_ofNat _ (by decide)] at h₂
  exact ⟨h₁, h₂.trans hc.rax⟩

omit h in
theorem Ready.xsp : (xS s c).gpr .rsp = Bs s + BitVec.ofNat 64 1768 := by
  rw [State.withRegions_gpr, State.callEntry_rsp, hc.qsp, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
    add_ofNat_sub_ofNat _ (by decide)]


omit h in
/-- The return address of the call. -/
theorem Ready.xmem : Frame [⟨Bs s + BitVec.ofNat 64 1768, 8⟩] (qS c).mem (xS s c).mem := by
  rw [State.withRegions_mem, State.callEntry_mem, hc.qsp, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
    add_ofNat_sub_ofNat _ (by decide)]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

omit h in
theorem Ready.xarg : stackArgAddr (xS s c) 0 = Bs s + BitVec.ofNat 64 1776 := by
  show (xS s c).gpr .rsp + BitVec.ofNat 64 (8 * (0 + 1)) = _
  rw [hc.xsp, Offset.add_ofNat_add_ofNat]

theorem Ready.xtag : stackArg (xS s c) 0 = Tg s := by
  have hBn := h.hBn
  show (xS s c).mem.readW (stackArgAddr (xS s c) 0) 64 = _
  rw [hc.xarg, Frame.readW (hc.xmem) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide)]
  exact (hc.qmem h).2

/-- What the call needs. -/
theorem Ready.call : callPre (xS s c) ∧ Covers (rdC s ++ wrC s) ((qS c).rd ++ (qS c).wr) ∧
    Covers (wrC s) (qS c).wr := by
  obtain ⟨rd, wr, kd, kt, nd, nt, ad, at_, dt, -, -, -, -, -, bk, bn, ba, bd, bt, -, -, ok, on, oa, od, ot,
    -⟩ := h.pre
  have hBn := h.hBn
  have hx (r : Reg) (hr : r ≠ .rsp) : (xS s c).gpr r = c.gpr r := xgpr_eq hr
  have hstk : below (Bs s + BitVec.ofNat 64 1768) 1768 = ⟨Bs s, 1768⟩ := by
    simp only [below, add_ofNat_sub_ofNat _ (show 1768 ≤ 1768 by decide), Nat.sub_self, BitVec.add_zero]
  have hxsp : (Bs s + BitVec.ofNat 64 1768).toNat = (Bs s).toNat + 1768 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 1768) (by decide),
      Nat.mod_eq_of_lt (by omega_arith)]
  have sb (d n : Nat) (hd : d + n ≤ 1832) {r : Region} (hr : (stkR s).Disjoint r) :
      (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := hr.sub_left (stk_sub s d n hd)
  have s0 (n : Nat) (hd : n ≤ 1832) {r : Region} (hr : (stkR s).Disjoint r) :
      (⟨Bs s, n⟩ : Region).Disjoint r := hr.sub_left (Region.sub_prefix hd)
  refine ⟨?_, ?_, ?_⟩
  · simp only [callPre, State.withRegions_rd, State.withRegions_wr, hx .rdi (by decide), hx .rsi (by decide),
      hx .rdx (by decide), hx .rcx (by decide), hx .r8 (by decide), hx .r9 (by decide), hc.rdi, hc.rsi, hc.rdx,
      hc.rcx, hc.r8, hc.r9, hc.xtag h, hc.xarg, hc.xsp, hstk]
    exact ⟨by omega_arith, by omega_arith, trivial, trivial, kd, kt, nd, nt, ad, at_, dt, (sb 1776 8 (by decide) bd).symm,
      (sb 1776 8 (by decide) bt).symm, sb 1768 8 (by decide) bk, sb 1768 8 (by decide) bn,
      sb 1768 8 (by decide) ba, sb 1768 8 (by decide) bd, sb 1768 8 (by decide) bt,
      Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith), s0 1768 (by decide) bk, s0 1768 (by decide) bn,
      s0 1768 (by decide) ba, s0 1768 (by decide) bd, s0 1768 (by decide) bt,
      Offset.base_disjoint _ (by decide) (by omega_arith), ok, on, oa, od, ot⟩
  · rw [hc.qrd, hc.qwr, rd, wr]
    intro a n ⟨r, hr, hcn⟩
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl) | (rfl | rfl)
    · exact ⟨_, by simp, hcn⟩
    · exact ⟨_, by simp, hcn⟩
    · exact ⟨_, by simp, hcn⟩
    · exact ⟨_, by simp, hcn⟩
    · exact ⟨_, by simp, hcn⟩
    · exact ⟨_, by simp, hcn⟩
  · rw [hc.qwr, wr]
    intro a n ⟨r, hr, hcn⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, hcn⟩
    · exact ⟨_, by simp, hcn⟩

end

/-- `gatherPost` reads the memory on return only within `dst` and the tag,
apart from the stack below `rsp`: a frame there loses its bytes harmlessly. -/
theorem gatherPost_frame {s z z' : State} (hs : gatherPre s) {R : Region} (hR : R.Sub (stkR s))
    (hz : Frame [R] z.mem z'.mem) (hp : gatherPost s z) : gatherPost s z' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, bd, bt, -, -, -, -, -, od, -⟩ := hs
  unfold gatherPost at hp ⊢
  rw [bytesAt_frame hz (fun r hr => by rw [List.mem_singleton.mp hr]; exact bd.symm.sub_right hR)
      (by omega_arith),
    bytesAt_frame hz (fun r hr => by rw [List.mem_singleton.mp hr]; exact bt.symm.sub_right hR) (by decide)]
  exact hp

/-- After the call, and the pop of `tag`. -/
structure Called (F : SealFn) (s z : State) : Prop where
  out : gatherPost s z
  ret : z.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → z.gpr r = s.gpr r
  rsp : z.gpr .rsp = Bs s + BitVec.ofNat 64 1784
  rd : z.rd = s.rd
  wr : z.wr = FR s :: s.wr
  mx : z.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10

theorem called_wp (F : SealFn) {s c : State} (h : Lay s) (hc : Ready s c) :
    WP isa (.frame (.push [.rax]) (.call F.name F.code) (.pop .rax 1)) c (Called F s) := by
  obtain ⟨-, -, kd, -, nd, -, ad, -, -, -, -, -, rdd, rt, bk, bn, ba, bd, -, -, -, ok, on, oa, od, -⟩ := h.pre
  obtain ⟨hcp, hcov, hw⟩ := hc.call h
  have hBn := h.hBn
  have hdep := F.depth
  have hx (r : Reg) (hr : r ≠ .rsp) : (xS s c).gpr r = c.gpr r := xgpr_eq hr
  refine WP.frame (by simp) (by decide) (by decide) (hc.hn h) (WP.call_sp_mx (k := F.contractE) F.exec F.sp
    (by omega_arith) (sealSpec_pre hcp) hcov hw fun s' rd' wr' cs' fr' _ ⟨s₂, m₂, _, post', _⟩ mx' => ?_)
  have rsp' : s'.gpr .rsp = (qS c).gpr .rsp := cs' .rsp (by decide)
  refine ⟨rsp', wr', fun m u fm => ?_⟩
  -- The pop of `tag` loses the 8 bytes it was in.
  rw [show c.gpr .rsp - BitVec.ofNat 64 (8 * [Reg.rax].length) = Bs s + BitVec.ofNat 64 1776 from
    (pushed_rsp _ _).symm.trans hc.qsp] at fm
  replace fm : Frame [⟨Bs s + BitVec.ofNat 64 1776, 8⟩] s'.mem m := fm
  have hpost := sealSpec_post post'
  simp only [hx .rdi (by decide), hx .rsi (by decide), hx .rdx (by decide), hx .rcx (by decide),
    hx .r8 (by decide), hx .r9 (by decide), hc.rdi, hc.rsi, hc.rdx, hc.rcx, hc.r8, hc.r9, hc.xtag h, m₂] at hpost
  -- The callee's memory on entry: ours, with `tag` and its return address pushed below our frame.
  have fx : Frame [⟨Bs s + BitVec.ofNat 64 1776, 8⟩, ⟨Bs s + BitVec.ofNat 64 1768, 8⟩] (gM s) (xS s c).mem := by
    rw [← hc.mem]
    exact ((hc.qmem h).1.mono (fun r hr => by simp at hr ⊢; exact Or.inl hr)).trans
      ((hc.xmem).mono (fun r hr => by simp at hr ⊢; exact Or.inr hr))
  have apart {r : Region} (hr : (stkR s).Disjoint r) :
      ∀ r' ∈ [(⟨Bs s + BitVec.ofNat 64 1776, 8⟩ : Region), ⟨Bs s + BitVec.ofNat 64 1768, 8⟩], r.Disjoint r' := by
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact (hr.sub_left (stk_sub s 1776 8 (by decide))).symm
    · exact (hr.sub_left (stk_sub s 1768 8 (by decide))).symm
  rw [bytesAt_frame fx (apart bk) (by omega_arith), bytesAt_frame fx (apart bn) (by omega_arith),
    bytesAt_frame fx (apart ba) (by omega_arith), bytesAt_frame fx (apart bd) (by omega_arith)] at hpost
  -- The key, the nonce and the additional data are what they were; the data is the slices gathered.
  have hfc : Frame [FR s, dR s] s.mem (gM s) :=
    (h.frame_eM.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)).trans
      (h.frame_gM.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp))
  have apart' {r : Region} (h₁ : (stkR s).Disjoint r) (h₂ : r.Disjoint (dR s)) :
      ∀ r' ∈ [FR s, dR s], r.Disjoint r' := by
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact h₁.symm.sub_right (fr_sub s)
    · exact h₂
  rw [bytesAt_frame hfc (apart' bk kd) (by omega_arith), bytesAt_frame hfc (apart' bn nd) (by omega_arith),
    bytesAt_frame hfc (apart' ba ad) (by omega_arith)] at hpost
  have hd : bytesAt (gM s) (Dst s) (L s) = pt s (Cnt s) := by
    rw [← h.hlen]
    exact bytesAt_writeBytes_self _ _ _ (by rw [h.hlen]; exact (stackArg s 1).isLt)
  rw [hd] at hpost
  dsimp only
  refine ⟨gatherPost_frame h.pre (stk_sub s 1776 8 (by decide)) (z := popped .rax 1 s') fm
    (by simp only [gatherPost, popped_mem]; exact hpost), ?_, fun r hr hsp => ?_, ?_, ?_, ?_, ?_⟩
  · -- The return address: neither the push, nor the copy, nor the call wrote it.
    have hsp' : (qS c).gpr .rsp = Bs s + BitVec.ofNat 64 1776 := hc.qsp
    have hbelow : below ((qS c).gpr .rsp) (F.code.x86_64Depth + 8) =
        ⟨Bs s + BitVec.ofNat 64 (1768 - F.code.x86_64Depth), F.code.x86_64Depth + 8⟩ := by
      rw [hsp']; simp only [below]
      rw [add_ofNat_sub_ofNat _ (by omega_arith), show 1776 - (F.code.x86_64Depth + 8) = 1768 - F.code.x86_64Depth by omega_arith]
    have e : s.gpr .rsp = Bs s + BitVec.ofNat 64 1832 := h.hB
    rw [e, Frame.readW fm (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide)]
    have r₁ : s'.mem.readW (Bs s + BitVec.ofNat 64 1832) 64 = (qS c).mem.readW (Bs s + BitVec.ofNat 64 1832) 64 := by
      refine Frame.readW fr' (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, hbelow] at hr
      rcases hr with (rfl | rfl) | rfl
      · rw [← e]; exact rdd
      · rw [← e]; exact rt
      · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
    have r₂ : (qS c).mem.readW (Bs s + BitVec.ofNat 64 1832) 64 = c.mem.readW (Bs s + BitVec.ofNat 64 1832) 64 :=
      Frame.readW (hc.qmem h).1 (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide)
    have r₃ : (gM s).readW (Bs s + BitVec.ofNat 64 1832) 64 = (eM s).readW (Bs s + BitVec.ofNat 64 1832) 64 :=
      Frame.readW h.frame_gM (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [← e]; exact rdd) (by decide)
    have r₄ : (eM s).readW (Bs s + BitVec.ofNat 64 1832) 64 = s.mem.readW (Bs s + BitVec.ofNat 64 1832) 64 :=
      Frame.readW h.frame_eM (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide)
    rw [r₁, r₂, hc.mem, r₃, r₄]
  · have hra : r ≠ .rax := fun e => by subst e; simp [calleeSaved] at hr
    rw [popped_gpr _ _ _ hsp hra, cs' r hr, pushed_gpr _ _ hsp, hc.cs r hr hsp]
  · rw [popped_rsp, rsp', hc.qsp, Offset.add_ofNat_add_ofNat]; rfl
  · rw [popped_rd, rd', hc.qrd]
  · rw [popped_wr, wr', hc.qwr]; rfl
  · rw [popped_mxcsr, mx', pushed_mxcsr, hc.mx]

/-- What else the callee leaves (`SealFn.E`), from the state it was called
in, in the memory the pop of `tag` leaves: a memory that differs from
it only in that frame, whose bytes the pop loses. What the residue proof
(`Scrub.lean`) asks of each run. -/
theorem called_wpE (F : SealFn) {s c : State} (h : Lay s) (hc : Ready s c) (hu : c.unknowns = s.unknowns)
    (hy : c.syms = s.syms) :
    WP isa (.frame (.push [.rax]) (.call F.name F.code) (.pop .rax 1)) c
      fun z => z.gpr .rsp = Bs s + BitVec.ofNat 64 1784 ∧ z.wr = FR s :: s.wr ∧
        ∃ c m, Ready s c ∧ c.unknowns = s.unknowns ∧ c.syms = s.syms ∧ F.E (xS s c) m ∧ Frame [(⟨Bs s + BitVec.ofNat 64 1776, 8⟩ : Region)] m z.mem := by
  obtain ⟨hcp, hcov, hw⟩ := hc.call h
  have hdep := F.depth
  refine WP.frame (by simp) (by decide) (by decide) (hc.hn h) (WP.call_sp_mx (k := F.contractE) F.exec F.sp
    (by omega_arith) (sealSpec_pre hcp) hcov hw fun s' _ wr' cs' _ _ ⟨s₂, m₂, _, _, hE⟩ _ => ?_)
  obtain rsp' : s'.gpr .rsp = (qS c).gpr .rsp := cs' .rsp (by decide)
  refine ⟨rsp', wr', fun m _ fm => ⟨?_, ?_, c, s'.mem, hc, hu, hy, by rw [← m₂]; exact hE, ?_⟩⟩
  · show (popped .rax 1 s').gpr .rsp = _
    rw [popped_rsp, rsp', hc.qsp, Offset.add_ofNat_add_ofNat]
  · show (popped .rax 1 s').wr = _
    rw [popped_wr, wr', hc.qwr]; rfl
  · rw [show c.gpr .rsp - BitVec.ofNat 64 (8 * ([.rax] : List Reg).length) = Bs s + BitVec.ofNat 64 1776 from
      (pushed_rsp _ _).symm.trans hc.qsp] at fm
    exact fm

/-- The body of our frame, as `called_wpE` sees its call. -/
theorem frameBody_wpE (w : Width) (F : SealFn) {s : State} (h : Lay s) :
    WP isa (.seq (.block entry) (.seq (gather w) (.seq (.block callArgsWhole)
      (.frame (.push [.rax]) (.call F.name F.code) (.pop .rax 1))))) (pushed saved s)
      fun z => z.gpr .rsp = Bs s + BitVec.ofNat 64 1784 ∧ z.wr = FR s :: s.wr ∧
        ∃ c m, Ready s c ∧ c.unknowns = s.unknowns ∧ c.syms = s.syms ∧ F.E (xS s c) m ∧ Frame [(⟨Bs s + BitVec.ofNat 64 1776, 8⟩ : Region)] m z.mem := by
  refine WP.seq (WP.mono_flat (entered_wp h) rfl fun e he ue ye => ?_)
  refine WP.seq (WP.mono_flat (gathered_wp w h he) (gather_flat w) fun g hg ug yg => ?_)
  refine WP.seq (WP.mono_flat (ready_wp h hg) rfl fun c hc uc yc => ?_)
  exact called_wpE F h hc (by rw [uc, ug, ue, pushed_unknowns]) (by rw [yc, yg, ye, pushed_syms])

/-- The body of our frame. -/
theorem frameBody_wp (w : Width) (F : SealFn) {s : State} (h : Lay s) :
    WP isa (.seq (.block entry) (.seq (gather w) (.seq (.block callArgsWhole)
      (.frame (.push [.rax]) (.call F.name F.code) (.pop .rax 1))))) (pushed saved s) (Called F s) := by
  refine WP.seq (WP.mono (entered_wp h) fun e he => ?_)
  refine WP.seq (WP.mono (gathered_wp w h he) fun g hg => ?_)
  refine WP.seq (WP.mono (ready_wp h hg) fun c hc => ?_)
  exact called_wp F h hc

theorem sealGather_wp (w : Width) (F : SealFn) {s : State} (hs : gatherPre s) :
    WP isa (sealGatherWhole w F.name F.code) s fun z => abiPreserved s z ∧ gatherPost s z := by
  have h := lay hs
  have hn : 8 * saved.length ≤ (s.gpr .rsp).toNat := by have := h.w₁; simp only [List.length_cons, List.length_nil]; omega_arith
  refine WP.frame (by simp) (by decide) (by decide) hn (WP.mono (frameBody_wp w F h) fun z hz => ?_)
  refine ⟨by rw [hz.rsp, hP s], by rw [hz.wr, hPwr s], fun m u fm => ?_⟩
  -- The pop of the saved registers loses their 48 bytes, `FR s`.
  rw [show s.gpr .rsp - BitVec.ofNat 64 (8 * saved.length) = Bs s + BitVec.ofNat 64 1784 from
    (pushed_rsp _ _).symm.trans (hP s)] at fm
  replace fm : Frame [FR s] z.mem m := fm
  dsimp only
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · by_cases hsp : r = .rsp
    · subst hsp
      rw [popped_rsp, hz.rsp, Offset.add_ofNat_add_ofNat, h.hB]; rfl
    · have hra : r ≠ .rax := fun e => by subst e; simp [calleeSaved] at hr
      rw [popped_gpr _ _ _ hsp hra, hz.cs r hr hsp]
  · rw [Frame.readW fm (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr, h.hB]
      exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide)]
    exact hz.ret
  · rw [popped_mxcsr]; exact hz.mx
  · exact gatherPost_frame hs (fr_sub s) (z := popped .rax saved.length z) fm
      (by simp only [gatherPost, popped_mem]; exact hz.out)

/-- What else the callee leaves (`SealFn.E`), from the state it was called
in, in a memory that differs from the one `seal_gather` returns with only in the
frames it releases: the call's and its own, whose bytes are lost. -/
theorem sealGather_wpE (w : Width) (F : SealFn) {s : State} (hs : gatherPre s) :
    WP isa (sealGatherWhole w F.name F.code) s fun z => ∃ c m, Ready s c ∧ c.unknowns = s.unknowns ∧ c.syms = s.syms ∧ F.E (xS s c) m ∧
      Frame [(⟨Bs s + BitVec.ofNat 64 1776, 8⟩ : Region), FR s] m z.mem := by
  have h := lay hs
  have hn : 8 * saved.length ≤ (s.gpr .rsp).toNat := by have := h.w₁; simp only [List.length_cons, List.length_nil]; omega_arith
  refine WP.frame (by simp) (by decide) (by decide) hn (WP.mono (frameBody_wpE w F h) fun z hz =>
    ⟨by rw [hz.1, hP s], by rw [hz.2.1, hPwr s], fun m _ fm => ?_⟩)
  rw [show s.gpr .rsp - BitVec.ofNat 64 (8 * saved.length) = Bs s + BitVec.ofNat 64 1784 from
    (pushed_rsp _ _).symm.trans (hP s)] at fm
  replace fm : Frame [FR s] z.mem m := fm
  obtain ⟨c, m', hc, hu, hy, hE, hf⟩ := hz.2.2
  exact ⟨c, m', hc, hu, hy, hE, (hf.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]).trans
    (fm.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])⟩

end VG.Proof.ChaCha20Poly1305.X86_64.Gather.Whole

end

end

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86-64: constant time

Untrusted: everything here is checked by Lean. Two runs whose arguments,
stack pointer and descriptors agree (`gatherPub`) leak the same trace,
related piece by piece from given states (`Eq2`, `Gather/LoopCT.lean`): the
frames are pushed and popped at `rsp`, the same in both runs
(`RelCT.frame`); the entry and the call's arguments are read at `rsp`
(the taint analysis from `rsp` and `r8`); the gathering is constant time by
`gather_rel`; and the call is constant time by its callee's contract, whose
public arguments agree (`sealGather_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Gather.Whole

open VG VG.X86_64
open VG.Impl.ChaCha20Poly1305.X86_64.SealGather (Width entry gather callArgsWhole sealGatherWhole)

/-- A frame, from two runs of its body from the states its push leaves. -/
theorem rel_frame {rs : List Reg} {r : Reg} {k : Nat} {body : Prog isa} {σ₁ σ₂ : State}
    (hsp : σ₁.gpr .rsp = σ₂.gpr .rsp) (hb : RelCT isa (Eq2 (pushed rs σ₁) (pushed rs σ₂)) body TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.frame (.push rs) body (.pop r k)) TT :=
  RelCT.frame (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact hsp)
    (hb.mono (fun _ _ ⟨s₁, s₂, ⟨e₁, e₂⟩, hx, hy⟩ => by subst e₁ e₂; exact ⟨hx, hy⟩) fun _ _ h => h)

/-- The callee's public data, in two runs ready for the call with the same
public arguments: what its contract relates them by. -/
theorem callee_pub {σ₁ σ₂ c₁ c₂ : State} (h₁ : Lay σ₁) (h₂ : Lay σ₂) (hc₁ : Ready σ₁ c₁)
    (hc₂ : Ready σ₂ c₂) (hrd : rdC σ₂ = rdC σ₁) (hwr : wrC σ₂ = wrC σ₁) (hB : Bs σ₁ = Bs σ₂)
    (hk : K σ₁ = K σ₂) (hn : Nn σ₁ = Nn σ₂) (ha : Ad σ₁ = Ad σ₂) (hal : σ₁.gpr .rcx = σ₂.gpr .rcx)
    (hd : Dst σ₁ = Dst σ₂) (hl : stackArg σ₁ 1 = stackArg σ₂ 1) (ht : Tg σ₁ = Tg σ₂)
    (hm : c₁.mxcsr = c₂.mxcsr) :
    (Spec.ChaCha20Poly1305.sealContract X86_64.abi 1768).pub (xS σ₁ c₁) (xS σ₂ c₂) := by
  have hx₂ : xS σ₂ c₂ = (qS c₂).callEntry.withRegions (rdC σ₁) (wrC σ₁) := by rw [← hrd, ← hwr]
  have g₁ (r : Reg) (hr : r ≠ .rsp) : (xS σ₁ c₁).gpr r = c₁.gpr r := xgpr_eq hr
  have g₂ (r : Reg) (hr : r ≠ .rsp) : ((qS c₂).callEntry.withRegions (rdC σ₁) (wrC σ₁)).gpr r = c₂.gpr r :=
    xgpr_eq (s := σ₁) hr
  have t₂ : stackArg ((qS c₂).callEntry.withRegions (rdC σ₁) (wrC σ₁)) 0 = Tg σ₂ := by
    rw [← hx₂]; exact hc₂.xtag h₂
  rw [hx₂]
  refine sealSpec_pub ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g₁ _ (by decide), g₂ _ (by decide), hc₁.rdi, hc₂.rdi, hk]
  · rw [g₁ _ (by decide), g₂ _ (by decide), hc₁.rsi, hc₂.rsi, hn]
  · rw [g₁ _ (by decide), g₂ _ (by decide), hc₁.rdx, hc₂.rdx, ha]
  · rw [g₁ _ (by decide), g₂ _ (by decide), hc₁.rcx, hc₂.rcx, hal]
  · rw [g₁ _ (by decide), g₂ _ (by decide), hc₁.r8, hc₂.r8, hd]
  · rw [g₁ _ (by decide), g₂ _ (by decide), hc₁.r9, hc₂.r9, hl]
  · rw [State.withRegions_gpr, State.withRegions_gpr, State.callEntry_rsp, State.callEntry_rsp, hc₁.qsp,
      hc₂.qsp, hB]
  · rw [hc₁.xtag h₁, t₂, ht]
  · simp only [State.withRegions_mxcsr, State.callEntry_mxcsr, pushed_mxcsr, hm]

/-- The call, in two runs ready for it with the same public arguments. -/
theorem call_rel (F : SealFn) {σ₁ σ₂ c₁ c₂ : State} (h₁ : Lay σ₁) (h₂ : Lay σ₂) (hc₁ : Ready σ₁ c₁)
    (hc₂ : Ready σ₂ c₂) (hrd : rdC σ₂ = rdC σ₁) (hwr : wrC σ₂ = wrC σ₁) (hB : Bs σ₁ = Bs σ₂)
    (hk : K σ₁ = K σ₂) (hn : Nn σ₁ = Nn σ₂) (ha : Ad σ₁ = Ad σ₂) (hal : σ₁.gpr .rcx = σ₂.gpr .rcx)
    (hd : Dst σ₁ = Dst σ₂) (hl : stackArg σ₁ 1 = stackArg σ₂ 1) (ht : Tg σ₁ = Tg σ₂)
    (hm : c₁.mxcsr = c₂.mxcsr) :
    RelCT isa (Eq2 c₁ c₂) (.frame (.push [.rax]) (.call F.name F.code) (.pop .rax 1)) TT := by
  refine rel_frame (by rw [hc₁.rsp, hc₂.rsp, hB]) ?_
  obtain ⟨cp₁, cv₁, cw₁⟩ := hc₁.call h₁
  obtain ⟨cp₂, cv₂, cw₂⟩ := hc₂.call h₂
  have hx₂ : xS σ₂ c₂ = (qS c₂).callEntry.withRegions (rdC σ₁) (wrC σ₁) := by rw [← hrd, ← hwr]
  rw [hx₂] at cp₂
  rw [hrd, hwr] at cv₂
  rw [hwr] at cw₂
  refine (RelCT.call F.verified.1 F.verified.2.1 (rdC σ₁) (wrC σ₁) fun x y ⟨e₁, e₂⟩ => ?_).mono
    (fun a b h => h) fun _ _ h => h
  subst e₁ e₂
  refine ⟨sealSpec_pre cp₁, sealSpec_pre cp₂, by
      rw [← hx₂]; exact callee_pub h₁ h₂ hc₁ hc₂ hrd hwr hB hk hn ha hal hd hl ht hm,
    cv₁, cw₁, cv₂, cw₂, by rw [hc₁.qsp, hc₂.qsp, hB]⟩

/-- What two runs from states `seal_gather`'s contract relates agree on, of
what the call's public arguments are made of. -/
theorem pub_facts {σ₁ σ₂ : State} (hq : gatherPub σ₁ σ₂) :
    rdC σ₂ = rdC σ₁ ∧ wrC σ₂ = wrC σ₁ ∧ Bs σ₁ = Bs σ₂ ∧ K σ₁ = K σ₂ ∧ Nn σ₁ = Nn σ₂ ∧ Ad σ₁ = Ad σ₂ ∧
      σ₁.gpr .rcx = σ₂.gpr .rcx ∧ Dst σ₁ = Dst σ₂ ∧ stackArg σ₁ 1 = stackArg σ₂ 1 ∧ Tg σ₁ = Tg σ₂ ∧
      σ₁.mxcsr = σ₂.mxcsr := by
  obtain ⟨qdi, qsi, qdx, qcx, -, -, qsp, qmx, a0, a1, a2, -⟩ := hq
  have hB : Bs σ₁ = Bs σ₂ := by simp only [Bs, qsp]
  have hrd : rdC σ₂ = rdC σ₁ := by
    simp only [rdC, kR, nR, aR, K, Nn, Ad, AL, Bs, qdi, qsi, qdx, qcx, qsp]
  have hwr : wrC σ₂ = wrC σ₁ := by
    simp only [wrC, dR, tgR, Dst, L, Tg, a0, a1, a2]
  exact ⟨hrd, hwr, hB, qdi, qsi, qdx, qcx, a0, a1, a2, qmx⟩

/-- The callee's public data, in two runs from states `seal_gather`'s contract
relates. -/
theorem callee_pub_of {σ₁ σ₂ c₁ c₂ : State} (p₁ : gatherPre σ₁) (p₂ : gatherPre σ₂) (hq : gatherPub σ₁ σ₂)
    (hc₁ : Ready σ₁ c₁) (hc₂ : Ready σ₂ c₂) :
    (Spec.ChaCha20Poly1305.sealContract X86_64.abi 1768).pub (xS σ₁ c₁) (xS σ₂ c₂) := by
  obtain ⟨hrd, hwr, hB, hk, hn, ha, hal, hd, hl, ht, hm⟩ := pub_facts hq
  exact callee_pub (lay p₁) (lay p₂) hc₁ hc₂ hrd hwr hB hk hn ha hal hd hl ht
    (hc₁.mx.trans (hm.trans hc₂.mx.symm))

theorem sealGather_ct (w : Width) (F : SealFn) :
    ConstantTime isa gatherPre gatherPub (sealGatherWhole w F.name F.code) := by
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  have h₁ := lay p₁
  have h₂ := lay p₂
  obtain ⟨qdi, qsi, qdx, qcx, q8, q9, qsp, qmx, a0, a1, a2, hdesc⟩ := hq
  have hB : Bs σ₁ = Bs σ₂ := by simp only [Bs, qsp]
  refine rel_frame qsp ?_
  -- The entry.
  refine rel_seq (rel_regs [.rsp, .r8] (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨by rw [hP, hP, hB], by rw [pushed_gpr _ _ (by decide), pushed_gpr _ _ (by decide), q8]⟩)
      ⟨_, by taint_decide⟩) (entered_wp h₁) (entered_wp h₂) fun e₁ e₂ he₁ he₂ => ?_
  -- The gathering.
  have gp₁ := gatherPre_of h₁ he₁
  have gp₂ : GatherPre e₂ (Src σ₁) (Dst σ₁) (Cnt σ₁) (L σ₁) := by
    have := gatherPre_of h₂ he₂
    rwa [show Src σ₂ = Src σ₁ from q8.symm, show Dst σ₂ = Dst σ₁ from a0.symm,
      show Cnt σ₂ = Cnt σ₁ from congrArg BitVec.toNat q9.symm, show L σ₂ = L σ₁ from congrArg BitVec.toNat a1.symm]
      at this
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, bds₁, -, -, -, -, -, -, ods₁, -⟩ := p₁
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, bds₂, -⟩ := p₂
  have hd : ∀ j < Cnt σ₁ * 16,
      e₁.mem (Src σ₁ + BitVec.ofNat 64 j) = e₂.mem (Src σ₁ + BitVec.ofNat 64 j) := by
    intro j hj
    have hx : (dsR σ₁).Contains (Src σ₁ + BitVec.ofNat 64 j) 1 :=
      Offset.contains_base _ hj (by omega_using [ods₁, hj])
    have hx₂ : (dsR σ₂).Contains (Src σ₁ + BitVec.ofNat 64 j) 1 := by
      simp only [dsR, Src, Cnt, ← q8, ← q9]; exact hx
    rw [he₁.mem, he₂.mem, h₁.keepE bds₁.symm hx, h₂.keepE bds₂.symm hx₂]
    exact hdesc j hj
  refine rel_seq (gather_rel w hd gp₁ gp₂) (gathered_wp w h₁ he₁) (gathered_wp w h₂ he₂)
    fun g₁ g₂ hg₁ hg₂ => ?_
  -- The call's arguments.
  refine rel_seq (rel_regs [.rsp] (by simp [hg₁.rsp, hg₂.rsp, hB]) ⟨_, by taint_decide⟩)
    (ready_wp h₁ hg₁) (ready_wp h₂ hg₂) fun c₁ c₂ hc₁ hc₂ => ?_
  -- The call, by its callee's contract.
  have hrd : rdC σ₂ = rdC σ₁ := by
    simp only [rdC, kR, nR, aR, K, Nn, Ad, AL, Bs, qdi, qsi, qdx, qcx, qsp]
  have hwr : wrC σ₂ = wrC σ₁ := by
    simp only [wrC, dR, tgR, Dst, L, Tg, a0, a1, a2]
  exact call_rel F h₁ h₂ hc₁ hc₂ hrd hwr hB qdi qsi qdx qcx a0 a1 a2 (hc₁.mx.trans (qmx.trans hc₂.mx.symm))

end VG.Proof.ChaCha20Poly1305.X86_64.Gather.Whole

end

end

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86-64: by length

Untrusted: everything here is checked by Lean. `sealGatherBy` compares
`len` with `lim`, 961 or 1025 (`lenCmp_ok`, through `rax`) and runs, for less, the code that
gathers every slice and calls `seal` (`Whole`), else the code that calls
`seal_split` (`Gather/Fn.lean`). Each is proven from its own precondition,
which `gatherPre` (with the 1880 bytes of stack the second needs) gives in
the state after the comparison, which differs only in `rax` and the flags
(`CmpSame`, `whole_pre`, `pre_same`); their postconditions and public data
are the same functions of the arguments (`post_same`, `pub_same`). Both
runs of the constant-time proof take the same branch, `len` being public
(`sealGatherBy_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Impl.AesGcm.X86_64 (at_ imm)
open VG.Proof.AesGcm.X86_64 (imm_eq)
open VG.Impl.ChaCha20Poly1305.X86_64.SealGather (Width sealGather sealGatherWhole sealGatherBy)

/-- The comparison of `len` with `lim`. -/
abbrev lenCmp (lim : Nat) : List Instr := [.mov .rax (.mem (at_ .rsp 16)), .alu .cmp .rax (imm lim)]

/-- A state that differs from `s` at most in `rax` and the flags. -/
structure CmpSame (s e : State) : Prop where
  gpr : ∀ r, r ≠ .rax → e.gpr r = s.gpr r
  mem : e.mem = s.mem
  rd : e.rd = s.rd
  wr : e.wr = s.wr
  mx : e.mxcsr = s.mxcsr

theorem lenCmp_ok {lim : Nat} (hlim : lim < 2 ^ 31) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 16) 8) :
    WP isa (.block (lenCmp lim)) s fun e => isa.eval .b e = some (decide (L s < lim)) ∧ CmpSame s e := by
  have il := imm_eq hlim
  apply WP.of_runBlock
  refine ⟨_, by xrun [lenCmp, hin, il], ?_⟩
  refine ⟨?_, ⟨fun r hr => by simp [gpr_setReg, gpr_arithFlags, hr], rfl, rfl, rfl, rfl⟩⟩
  show (State.cf _) = _
  simp only [cf_arithFlags, gpr_setReg, ↓reduceIte, BitVec.toNat_ofNat]
  show some (decide ((s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 16) 64).toNat < lim % 2 ^ 64)) = _
  rw [Nat.mod_eq_of_lt (by omega_using [hlim])]
  rfl

section
variable {s e : State} (h : CmpSame s e)
include h

theorem CmpSame.arg (i : Nat) : stackArg e i = stackArg s i := by
  show e.mem.readW (e.gpr .rsp + _) 64 = s.mem.readW (s.gpr .rsp + _) 64
  rw [h.mem, h.gpr .rsp (by decide)]

theorem CmpSame.argAddr (i : Nat) : stackArgAddr e i = stackArgAddr s i := by
  show e.gpr .rsp + _ = s.gpr .rsp + _
  rw [h.gpr .rsp (by decide)]

/-- The arguments, the regions and the slices' length, after the comparison. -/
theorem CmpSame.eqs : kR e = kR s ∧ nR e = nR s ∧ aR e = aR s ∧ dsR e = dsR s ∧ lsR e = lsR s ∧
    dR e = dR s ∧ tgR e = tgR s ∧ argR e = argR s ∧ retR e = retR s ∧ stkR e = stkR s ∧
    K e = K s ∧ Nn e = Nn s ∧ Ad e = Ad s ∧ AL e = AL s ∧ Dst e = Dst s ∧ L e = L s ∧ Tg e = Tg s ∧
    Src e = Src s ∧ Cnt e = Cnt s ∧ SP e = SP s ∧ gl e (Cnt e) = gl s (Cnt s) := by
  have hK : K e = K s := h.gpr .rdi (by decide)
  have hN : Nn e = Nn s := h.gpr .rsi (by decide)
  have hA : Ad e = Ad s := h.gpr .rdx (by decide)
  have hAL : AL e = AL s := congrArg BitVec.toNat (h.gpr .rcx (by decide))
  have hS : Src e = Src s := h.gpr .r8 (by decide)
  have hC : Cnt e = Cnt s := congrArg BitVec.toNat (h.gpr .r9 (by decide))
  have hSP : SP e = SP s := h.gpr .rsp (by decide)
  have hD : Dst e = Dst s := h.arg 0
  have hL : L e = L s := congrArg BitVec.toNat (h.arg 1)
  have hT : Tg e = Tg s := h.arg 2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hK, hN, hA, hAL, hD, hL, hT, hS, hC, hSP, ?_⟩
  · show (⟨K e, 32⟩ : Region) = ⟨K s, 32⟩; rw [hK]
  · show (⟨Nn e, 12⟩ : Region) = ⟨Nn s, 12⟩; rw [hN]
  · show (⟨Ad e, AL e⟩ : Region) = ⟨Ad s, AL s⟩; rw [hA, hAL]
  · show (⟨Src e, Cnt e * 16⟩ : Region) = ⟨Src s, Cnt s * 16⟩; rw [hS, hC]
  · show Sig.listed 64 e.mem .u8 (Src e) (Cnt e) = Sig.listed 64 s.mem .u8 (Src s) (Cnt s); rw [h.mem, hS, hC]
  · show (⟨Dst e, L e⟩ : Region) = ⟨Dst s, L s⟩; rw [hD, hL]
  · show (⟨Tg e, 16⟩ : Region) = ⟨Tg s, 16⟩; rw [hT]
  · show (⟨stackArgAddr e 0, 24⟩ : Region) = ⟨stackArgAddr s 0, 24⟩; rw [h.argAddr]
  · show (⟨SP e, 8⟩ : Region) = ⟨SP s, 8⟩; rw [hSP]
  · show below (SP e) 1880 = below (SP s) 1880; rw [hSP]
  · show Spec.ChaCha20Poly1305.gatheredLen 64 e.mem (Src e) (Cnt e) = Spec.ChaCha20Poly1305.gatheredLen 64 s.mem (Src s) (Cnt s); rw [h.mem, hS, hC]

/-- `gatherPre`, after the comparison. -/
theorem pre_same (hs : gatherPre s) : gatherPre e := by
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉, e₁₀, e₁₁, e₁₂, e₁₃, e₁₄, e₁₅, e₁₆, e₁₇, e₁₈, e₁₉, e₂₀, e₂₁⟩ := h.eqs
  unfold gatherPre
  rw [h.rd, h.wr, e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉, e₁₀, e₁₁, e₁₂, e₁₃, e₁₄, e₁₅, e₁₆, e₁₇, e₁₈, e₂₁, e₁₉, e₂₀]
  exact hs

/-- `Whole`'s precondition, after the comparison. -/
theorem whole_pre (hs : gatherPre s) : Whole.gatherPre e := by
  have he := pre_same h hs
  have g (r : Reg) (hr : r ≠ .rax) := h.gpr r hr
  obtain ⟨rd, wr, kd, kt, nd, nt, ad, at_, dt, dds, dls, darg, rdd, rt, bk, bn, ba, bd, bt, bds, bls, ok, on, oa,
    od, ot, ods, ol, w₁, w₂, hgl, hpm, -, -⟩ := he
  have sub : (Whole.stkR e).Sub (stkR e) :=
    below_sub (a := 1832) (b := 1880) (by decide) (by decide)
  exact ⟨rd, wr, kd, kt, nd, nt, ad, at_, dt, dds, dls, darg, rdd, rt, bk.sub_left sub, bn.sub_left sub,
    ba.sub_left sub, bd.sub_left sub, bt.sub_left sub, bds.sub_left sub, fun r hr => (bls r hr).sub_left sub,
    ok, on, oa, od, ot, ods, ol, by have : 1880 ≤ (e.gpr .rsp).toNat := w₁; show 1832 ≤ (e.gpr .rsp).toNat; omega_using [this], w₂, hgl, hpm⟩

/-- What the code leaves, from `s` or from the state after the comparison. -/
theorem post_same {z : State} : gatherPost e z ↔ gatherPost s z := by
  have g (r : Reg) (hr : r ≠ .rax) := h.gpr r hr
  simp only [gatherPost, pt, K, Nn, Ad, AL, Src, Cnt, Dst, L, Tg, g .rdi (by decide), g .rsi (by decide),
    g .rdx (by decide), g .rcx (by decide), g .r8 (by decide), g .r9 (by decide), h.mem, h.arg]

theorem whole_post {z : State} : Whole.gatherPost e z ↔ gatherPost s z := by
  have g (r : Reg) (hr : r ≠ .rax) := h.gpr r hr
  simp only [Whole.gatherPost, gatherPost, Whole.pt, pt, Whole.K, K, Whole.Nn, Nn, Whole.Ad, Ad, Whole.AL, AL,
    Whole.Src, Src, Whole.Cnt, Cnt, Whole.Dst, Dst, Whole.L, L, Whole.Tg, Tg, g .rdi (by decide),
    g .rsi (by decide), g .rdx (by decide), g .rcx (by decide), g .r8 (by decide), g .r9 (by decide), h.mem,
    h.arg]

theorem abi_same {z : State} (hz : abiPreserved e z) : abiPreserved s z := by
  obtain ⟨h₁, h₂, h₃⟩ := hz
  refine ⟨fun r hr => (h₁ r hr).trans (h.gpr r fun e => by subst e; simp [calleeSaved] at hr), ?_, ?_⟩
  · rw [← h.mem, ← h.gpr .rsp (by decide)]; exact h₂
  · rw [← h.mx]; exact h₃

end

/-- Public data, after the comparison in both runs. -/
theorem pub_same {s₁ s₂ e₁ e₂ : State} (h₁ : CmpSame s₁ e₁) (h₂ : CmpSame s₂ e₂) (hp : gatherPub s₁ s₂) :
    gatherPub e₁ e₂ := by
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, qm, a₀, a₁, a₂, hd⟩ := hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [h₁.mx, h₂.mx]; exact qm, by rw [h₁.arg, h₂.arg]; exact a₀, by rw [h₁.arg, h₂.arg]; exact a₁,
    by rw [h₁.arg, h₂.arg]; exact a₂, fun i hi => ?_⟩
  · rw [h₁.gpr _ (by decide), h₂.gpr _ (by decide)]; exact q₁
  · rw [h₁.gpr _ (by decide), h₂.gpr _ (by decide)]; exact q₂
  · rw [h₁.gpr _ (by decide), h₂.gpr _ (by decide)]; exact q₃
  · rw [h₁.gpr _ (by decide), h₂.gpr _ (by decide)]; exact q₄
  · rw [h₁.gpr _ (by decide), h₂.gpr _ (by decide)]; exact q₅
  · rw [h₁.gpr _ (by decide), h₂.gpr _ (by decide)]; exact q₆
  · rw [h₁.gpr _ (by decide), h₂.gpr _ (by decide)]; exact q₇
  · simp only [Src, Cnt, h₁.gpr .r8 (by decide), h₁.gpr .r9 (by decide), h₁.mem, h₂.mem] at hi ⊢
    exact hd i hi

theorem whole_pub {s₁ s₂ e₁ e₂ : State} (h₁ : CmpSame s₁ e₁) (h₂ : CmpSame s₂ e₂) (hp : gatherPub s₁ s₂) :
    Whole.gatherPub e₁ e₂ :=
  pub_same h₁ h₂ hp

/-- `len`'s word is a stack argument. -/
theorem len_in {s : State} (hs : gatherPre s) :
    InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 16) 8 := by
  obtain ⟨rd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, w₁, w₂, -⟩ := hs
  have w₂' : (s.gpr .rsp).toNat + 32 ≤ 2 ^ 64 := w₂
  refine ⟨argR s, List.mem_append_left _ (by rw [rd]; simp), ?_⟩
  show (⟨s.gpr .rsp + BitVec.ofNat 64 8, 24⟩ : Region).Contains _ 8
  rw [show s.gpr .rsp + BitVec.ofNat 64 16 = s.gpr .rsp + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 by
    rw [Offset.add_ofNat_add_ofNat]]
  exact Offset.contains_base _ (by decide) (by decide)

theorem sealGatherBy_correct {lim : Nat} (hlim : lim < 2 ^ 31) (w : Width) (F : Whole.SealFn) (G : SealSplitFn)
    (s : State) (hs : gatherPre s) :
    ∃ t s', Exec isa (sealGatherBy lim w F.name F.code G.name G.code) s t s' ∧ abiPreserved s s' ∧
      gatherPost s s' := by
  have hw : WP isa (sealGatherBy lim w F.name F.code G.name G.code) s fun z =>
      abiPreserved s z ∧ gatherPost s z := by
    refine WP.seq (WP.mono (lenCmp_ok hlim s (len_in hs)) fun e ⟨hb, he⟩ => ?_)
    refine WP.ite (decide (L s < lim)) hb (fun _ => ?_) (fun _ => ?_)
    · exact WP.mono (Whole.sealGather_wp w F (whole_pre he hs)) fun z ⟨ha, hp⟩ =>
        ⟨abi_same he ha, (whole_post he).mp hp⟩
    · exact WP.mono (sealGather_wp w G (pre_same he hs)) fun z ⟨ha, hp⟩ =>
        ⟨abi_same he ha, (post_same he).mp hp⟩
  obtain ⟨t, s', he, hq⟩ := hw
  exact ⟨t, s', he, hq⟩

/-- Two runs of constant-time code from states it allows, with the same
public data. -/
theorem rel_of_ct {pre : State → Prop} {pub : State → State → Prop} {c : Prog isa}
    (hc : ConstantTime isa pre pub c) {σ₁ σ₂ : State} (h₁ : pre σ₁) (h₂ : pre σ₂) (hp : pub σ₁ σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) c TT := by
  intro a b t₁ t₂ a' b' ⟨ea, eb⟩ e₁ e₂
  subst ea eb
  exact ⟨hc _ _ _ _ _ _ h₁ h₂ hp e₁ e₂, trivial⟩

theorem sealGatherBy_ct {lim : Nat} (hlim : lim = 961 ∨ lim = 1025) (w : Width) (F : Whole.SealFn)
    (G : SealSplitFn) :
    ConstantTime isa gatherPre gatherPub (sealGatherBy lim w F.name F.code G.name G.code) := by
  have hl : lim < 2 ^ 31 := by omega_using [hlim]
  have ht : ∃ h, (taint.check (Taint.ofRegs [.rsp]) (.block (lenCmp lim)) h).isSome = true := by
    rcases hlim with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  have hsp : σ₁.gpr .rsp = σ₂.gpr .rsp := hq.2.2.2.2.2.2.1
  have hL : L σ₂ = L σ₁ := congrArg BitVec.toNat hq.2.2.2.2.2.2.2.2.2.1.symm
  refine rel_seq (rel_regs [.rsp] (by simp [hsp]) ht)
    (lenCmp_ok hl σ₁ (len_in p₁)) (lenCmp_ok hl σ₂ (len_in p₂)) fun e₁ e₂ ⟨b₁, h₁⟩ ⟨b₂, h₂⟩ => ?_
  rw [hL] at b₂
  refine rel_ite b₁ b₂ (fun _ => ?_) (fun _ => ?_)
  · exact rel_of_ct (Whole.sealGather_ct w F) (whole_pre h₁ p₁) (whole_pre h₂ p₂) (whole_pub h₁ h₂ hq)
  · exact rel_of_ct (sealGather_ct w G) (pre_same h₁ p₁) (pre_same h₂ p₂) (pub_same h₁ h₂ hq)

theorem sealGatherBy_verified {lim : Nat} (hlim : lim = 961 ∨ lim = 1025) (w : Width) (F : Whole.SealFn)
    (G : SealSplitFn) :
    Verified X86_64.target (sealGatherBy lim w F.name F.code G.name G.code)
      (Spec.ChaCha20Poly1305.sealGatherContract X86_64.abi 1880) :=
  Verified.of_correct (k := gatherX86_64) (sealGatherBy_correct (by omega_using [hlim]) w F G) (sealGatherBy_ct hlim w F G)
    gather_implies

/-- `Whole` alone, from `gatherPre` (with 1880 bytes of stack). -/
theorem sealGatherWhole_verified (w : Width) (F : Whole.SealFn) :
    Verified X86_64.target (sealGatherWhole w F.name F.code)
      (Spec.ChaCha20Poly1305.sealGatherContract X86_64.abi 1880) := by
  have same (s : State) : CmpSame s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  refine Verified.of_correct (k := gatherX86_64) (fun s hs => ?_) (fun s₁ s₂ t₁ t₂ s₁' s₂' p₁ p₂ hp e₁ e₂ =>
    Whole.sealGather_ct w F s₁ s₂ t₁ t₂ s₁' s₂' (whole_pre (same _) p₁) (whole_pre (same _) p₂)
      (whole_pub (same _) (same _) hp) e₁ e₂) gather_implies
  obtain ⟨t, s', he, ha, hp⟩ := Whole.sealGather_wp w F (whole_pre (same s) hs)
  exact ⟨t, s', he, ha, (whole_post (same s)).mp hp⟩

end VG.Proof.ChaCha20Poly1305.X86_64.Gather

end

end

/-! ### `ChaCha20Poly1305.X86_64.Split.Verified`, which only this module used -/

section

/-! ### `ChaCha20Poly1305.SplitScratch`, which only this module used -/

section

/-!
# `vg_chacha20_poly1305_seal_split` with its working space as an argument

As `seal` (`Scratch.lean`), `vg_chacha20_poly1305_seal_split` keeps its
working space in a frame of its own, around code proved with the working
space as a last argument (`sealSplitScratchContract n`). Its precondition
and postcondition read the memory only within its buffers
(`sealSplitPre_local`, `sealSplitPost_local`, `sealSplitPost_out`): the
precondition reads none, the postcondition the key, the nonce, the
additional data, `src`, the data and the tag.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305

open VG.Spec.ChaCha20Poly1305

/-- `sealSplitContract`, with `work: *mut [u64; n]` after its arguments,
whatever it holds. -/
def sealSplitScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  Sig.scratchContract A sealSplitSig "work" .u64 n (sealSplitPre A.ptrBits) (sealSplitPost A.ptrBits) true stack

variable (pb : Nat)

theorem sealSplitPre_local : ∀ vs (m₁ m₂ : Mem), vs.length = (sealSplitSig.words pb).length →
    (∀ b ∈ Sig.bufs sealSplitSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealSplitSig.words pb) (sealSplitPre pb) vs m₁ →
      Curry.apply (sealSplitSig.words pb) (sealSplitPre pb) vs m₂ := by
  intro vs _ _ hlen _ h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 8) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 8
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact h

theorem sealSplitPost_local : ∀ vs m₁ m₂ m' r, vs.length = (sealSplitSig.words pb).length →
    (∀ b ∈ Sig.bufs sealSplitSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealSplitSig.words pb) (sealSplitPost pb) vs m₁ m' r →
      Curry.apply (sealSplitSig.words pb) (sealSplitPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨key, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 8) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nonce, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨aad, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨al, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨src, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨sl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dst, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [sealSplitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (sealSplitPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (sealSplitPost pb) _ m₂ m' r
  dsimp only [Curry.apply, sealSplitPost, ArgWord.ofRaw] at h ⊢
  rw [bytesAt_congr (agree_of hb.1), bytesAt_congr (agree_of hb.2.1),
    bytesAt_congr_len (agree_of hb.2.2.1), bytesAt_congr_len (p := src) (agree_of hb.2.2.2.1),
    bytesAt_congr_len (p := dst) (agree_of hb.2.2.2.2.1)]
  exact h

theorem sealSplitPost_out : ∀ vs m m₁ m₂ r, vs.length = (sealSplitSig.words pb).length →
    (∀ b ∈ Sig.bufs sealSplitSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealSplitSig.words pb) (sealSplitPost pb) vs m m₁ r →
      Curry.apply (sealSplitSig.words pb) (sealSplitPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 8) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 5
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain ⟨dst, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [sealSplitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (sealSplitPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (sealSplitPost pb) _ m m₂ r
  dsimp only [Curry.apply, sealSplitPost, ArgWord.ofRaw] at h ⊢
  rw [bytesAt_congr_len (p := dst) (agree_of hb.2.2.2.2.1), bytesAt_congr (p := tag) (agree_of hb.2.2.2.2.2)]
  exact h

end VG.Proof.ChaCha20Poly1305

end

end


/-!
# ChaCha20-Poly1305 with the data's first bytes from `src`, x86-64: `Verified`

The contract of `vg_chacha20_poly1305_seal_split` with its working space as
a last argument and the 64 bytes of stack below the stack pointer that its
frame (40) and `seal`'s calls (24) use (`sealSplitScratchContract`) implies
the one the proofs are written against (`splitX86_64`: `FPre`, `splitPost`,
`splitPub`), so the code of the instance calling the implementation `v` of
`vg_chacha20_xor` is `Verified` against it (`sealSplit_verified`), and then,
with its working space in a frame of its own of 1736 bytes (the copies of
`dst`, `len` and `tag` and the address of `work`, and `work`'s 1696 bytes),
against the shared contract with 1800 bytes of stack
(`Verified.stackArgScratchWipedX`, `sealSplit_framed`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Split

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.SealSplit
open VG.Impl.ChaCha20Poly1305.X86_64.SealGather (Width)
open VG.Proof.ChaCha20Poly1305.X86_64.Gather (filter_true' filter_false' filterMap_some' filterMap_none' pairFacts_ro)

/-- `vg_chacha20_poly1305_seal_split(key, nonce, aad, aad_len, src, src_len,
dst, len, tag, work)`, as the proofs state it. -/
def splitX86_64 : Contract isa where
  pre := FPre
  post := splitPost
  pub := splitPub

theorem stackArgs_four (s : State) : List.map (stackArg s) (List.range 4) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3] := rfl

theorem fpre_of_spec {s : State} (h : (sealSplitScratchContract X86_64.abi 212 64).pre s) : FPre s := by
  sig_pre [sealSplitScratchContract, Sig.scratchContract, Sig.withScratch, Proof.ChaCha20Poly1305.sealSplitSig,
    Proof.ChaCha20Poly1305.sealSplitPre, X86_64.abi, X86_64.argRegs, stackArgs_four, List.append_eq] at h
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or, Bool.or_true,
    Bool.false_or, Bool.or_false, List.cons_append, List.singleton_append] at h
  obtain ⟨w₁, w₂, rd, wr, ⟨kd, kt, kw, nd, nt, nw, ad, at_, aw, sd, st, sw, dt, dw, dg, tw, tg, wg⟩,
    -, -, ra, rs, rdd, rt, rw, -, bk, bn, ba, bs, bd, bt, bw, -, ok, on, oa, os, od, ot, ow, hle⟩ := h
  exact ⟨rd, wr, kd, kt, kw, nd, nt, nw, ad, at_, aw, sd, st, sw, dt, dw, tw, dg, tg, wg, ra, rs, rdd, rt, rw, bk,
    bn, ba, bs, bd, bt, bw, ok, on, oa, os, od, ot, ow, w₁, w₂, hle⟩

theorem post_of {s s' : State} (h : splitPost s s') : (sealSplitScratchContract X86_64.abi 212 64).post s s' := by
  sig_post [sealSplitScratchContract, Sig.scratchContract, Sig.withScratch, Proof.ChaCha20Poly1305.sealSplitSig,
    Proof.ChaCha20Poly1305.sealSplitPost, X86_64.abi, X86_64.argRegs, stackArgs_four, List.append_eq]
  exact fun _ => h

theorem pub_of {s₁ s₂ : State} (hp : (sealSplitScratchContract X86_64.abi 212 64).pub s₁ s₂) : splitPub s₁ s₂ := by
  sig_pub_keep [sealSplitScratchContract, Sig.scratchContract, Sig.withScratch, Proof.ChaCha20Poly1305.sealSplitSig,
    Proof.ChaCha20Poly1305.sealSplitPre, X86_64.abi, X86_64.argRegs, stackArgs_four, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hp
  obtain ⟨qsp, qm, q₁, q₂, q₃, q₄, q₅, q₆, a₀, a₁, a₂, a₃⟩ := hp
  exact ⟨q₁, q₂, q₃, q₄, q₅, q₆, qsp, a₀, a₁, a₂, a₃, qm⟩

/-- A state satisfying the precondition, with its working space: no
additional data or data, `dst` at `0x3000`, `tag` at `0x4000` and `work`
at 0, on the stack at `0x8008`. -/
def splitSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x1100 | .rdx => 0x2000 | .r8 => 0x2100 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := bif Nat.beq a.toNat 0x8009 then 0x30 else bif Nat.beq a.toNat 0x8019 then 0x40 else 0
  rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x8008, 32⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 16⟩, ⟨0, 1696⟩]

theorem splitSat_pre : ∃ s, (sealSplitScratchContract X86_64.abi 212 64).pre s := by
  refine ⟨splitSat, ?_⟩
  sig_pre [sealSplitScratchContract, Sig.scratchContract, Sig.withScratch,
    Proof.ChaCha20Poly1305.sealSplitSig, Proof.ChaCha20Poly1305.sealSplitPre, X86_64.abi, X86_64.argRegs,
    stackArgs_four, List.append_eq]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Nat.zero_le _

theorem split_implies : splitX86_64.Implies (sealSplitScratchContract X86_64.abi 212 64) :=
  ⟨fun _ h => fpre_of_spec h, fun _ _ _ h => post_of h, fun _ _ _ _ h => pub_of h, splitSat_pre⟩

theorem sealSplit_verified (v : Proof.ChaCha20.X86_64.XorImpl) :
    Verified X86_64.target (sealSplitFor v.callee v.poly) (sealSplitScratchContract X86_64.abi 212 64) :=
  Verified.of_correct (k := splitX86_64) (fun _ hs => let ⟨t, s', e, a, p⟩ := sealSplit_wp v hs; ⟨t, s', e, a, p⟩)
    (sealSplit_ct v) split_implies

/-! ## The frame -/

theorem head_spSafe (whole : Bool) (w : Width) :
    (head whole w).all (fun i => !X86_64.isa.writesSp i) = true := by
  cases whole <;> cases w <;> decide +kernel

theorem head_xdepth (whole : Bool) (w : Width) : (head whole w).x86_64Depth = 0 := by
  cases whole <;> cases w <;> decide +kernel

theorem framed_spSafe {c : Prog isa} (h : c.all (fun i => !X86_64.isa.writesSp i) = true) :
    (framed c).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [framed, Code.all, h, Bool.and_true]; decide

theorem framed_xdepth (c : Prog isa) : (framed c).x86_64Depth = c.x86_64Depth + 40 := by
  simp only [framed, Code.x86_64Depth, X86_64.Instr.frameBytes, Nat.zero_max]; rfl

theorem sealSplitFor_spSafe (v : Proof.ChaCha20.X86_64.XorImpl) :
    (sealSplitFor v.callee v.poly).all (fun i => !X86_64.isa.writesSp i) = true := by
  have h₁ := Proof.ChaCha20Poly1305.X86_64.Stitch.sealFor_spSafe v
  cases hb : v.poly with
  | avx512 => exact (Bool.and_eq_true _ _).mpr ⟨head_spSafe _ _, framed_spSafe (sealSplitBody_spSafe v _ (.inl rfl))⟩
  | ifma => exact (Bool.and_eq_true _ _).mpr ⟨head_spSafe _ _, framed_spSafe (sealSplitBody_spSafe v _ (.inr rfl))⟩
  | scalar => rw [hb] at h₁; exact (Bool.and_eq_true _ _).mpr ⟨head_spSafe _ _, framed_spSafe h₁⟩
  | avx2 => rw [hb] at h₁; exact (Bool.and_eq_true _ _).mpr ⟨head_spSafe _ _, framed_spSafe h₁⟩

theorem sealSplitFor_xdepth (v : Proof.ChaCha20.X86_64.XorImpl) : (sealSplitFor v.callee v.poly).x86_64Depth ≤ 64 := by
  have h₁ := Proof.ChaCha20Poly1305.X86_64.Stitch.sealFor_xdepth v
  cases hb : v.poly with
  | avx512 => have := sealSplitBody_xdepth v .avx512
              simp only [sealSplitFor, Code.x86_64Depth, head_xdepth, framed_xdepth, Nat.max_le]; omega_using [this]
  | ifma => have := sealSplitBody_xdepth v .ifma
            simp only [sealSplitFor, Code.x86_64Depth, head_xdepth, framed_xdepth, Nat.max_le]; omega_using [this]
  | scalar => rw [hb] at h₁; simp only [sealSplitFor, Code.x86_64Depth, head_xdepth, framed_xdepth, Nat.max_le]; omega_using [h₁]
  | avx2 => rw [hb] at h₁; simp only [sealSplitFor, Code.x86_64Depth, head_xdepth, framed_xdepth, Nat.max_le]; omega_using [h₁]

/-- A state satisfying the shared contract's precondition, without the
working space. -/
def splitFrameSat : State :=
  { splitSat with rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x8008, 24⟩],
                  wr := [⟨0x3000, 0⟩, ⟨0x4000, 16⟩] }

theorem stackArgs_three (s : State) : List.map (stackArg s) (List.range 3) =
    [stackArg s 0, stackArg s 1, stackArg s 2] := rfl

theorem splitFrameSat_pre : ∃ s, (Proof.ChaCha20Poly1305.sealSplitContract X86_64.abi 1800).pre s := by
  refine ⟨splitFrameSat, ?_⟩
  sig_pre [Proof.ChaCha20Poly1305.sealSplitContract, Proof.ChaCha20Poly1305.sealSplitSig,
    Proof.ChaCha20Poly1305.sealSplitPre, X86_64.abi, X86_64.argRegs, stackArgs_three, List.append_eq]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Nat.zero_le _

/-- `vg_chacha20_poly1305_seal_split` of the instance calling the
implementation `v` of `vg_chacha20_xor`, with its working space in a frame
of its own. -/
theorem sealSplit_framed (v : Proof.ChaCha20.X86_64.XorImpl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratchWipedX 1736 3 42 (sealSplitFor v.callee v.poly))
      (Proof.ChaCha20Poly1305.sealSplitContract X86_64.abi 1800) :=
  X86_64.Verified.stackArgScratchWipedX (sig := Proof.ChaCha20Poly1305.sealSplitSig) (nm := "work") (e := .u64)
    (n := 212) (pre := Proof.ChaCha20Poly1305.sealSplitPre X86_64.abi.ptrBits)
    (post := Proof.ChaCha20Poly1305.sealSplitPost X86_64.abi.ptrBits) (wa := true) (stack := 64)
    (bytes := 1736) (k := 42) (sealSplit_verified v) (by decide) (by decide) (by decide)
    (sealSplitFor_spSafe v) (sealSplitFor_xdepth v) (by decide) (sealSplitPre_local _) (sealSplitPost_local _)
    (sealSplitPost_out _) splitFrameSat_pre

end VG.Proof.ChaCha20Poly1305.X86_64.Split

end

end

/-! ### `ChaCha20Poly1305.X86_64.Gather.Whole.Verified`, which only this module used -/

section

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86-64: the instance it calls

Untrusted: everything here is checked by Lean. For the code of
`vg_chacha20_poly1305_seal_gather` that calls an instance of
`vg_chacha20_poly1305_seal` (`sealGatherWhole`): that instance (`sealFn`),
how many bytes at a time the code copies (`width`), and that only its
frames' pushes and pops write `rsp` (`sealGather_spSafe`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Gather.Whole

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.SealGather

open VG.Proof.ChaCha20.X86_64 VG.Impl.StackScratch.X86_64 in
/-- The instance of `vg_chacha20_poly1305_seal` calling the implementation
`v` of `vg_chacha20_xor`, with its working space in a frame of its own: its
code as it is without the clearing after it (`Scrub.sealReg`), `…_core`, as
`seal_gather` clears its own stack. -/
def sealFn (v : XorImpl) : SealFn where
  name := Spec.ChaCha20Poly1305.sealApi.name ++ v.suffix ++ "_core"
  code := Impl.ChaCha20Poly1305.X86_64.Shared.sealCode v.callee v.poly
  verified := Shared.seal_verified v
  sp := SpSafe.of_all (Shared.seal_sp v)
  depth := Shared.seal_depth v
  E _ _ := True
  exec s h := let ⟨t, s', e, a, p⟩ := (Shared.seal_verified v).1 s h; ⟨t, s', e, a, p, trivial⟩

open VG.Proof.ChaCha20.X86_64 in
/-- How many bytes at a time the instance for `v` copies: as many as the
CPUs of the instance of `vg_chacha20_poly1305_seal` it calls can. -/
def width (v : XorImpl) : Width := .ofBlocks v.poly

open VG.Proof.ChaCha20.X86_64 in
/-- No instruction of the code, or of the instance it calls, writes `rsp`
but its frames' pushes and pops. -/
theorem sealGather_spSafe (v : XorImpl) :
    (sealGatherWhole (width v) (sealFn v).name (sealFn v).code).all (fun i => !X86_64.isa.writesSp i) = true := by
  have hc : (sealFn v).code.all (fun i => !X86_64.isa.writesSp i) = true :=
    Shared.seal_sp v
  simp only [sealGatherWhole, Code.all, hc, Bool.and_true, Bool.true_and]
  cases width v <;> decide +kernel

end VG.Proof.ChaCha20Poly1305.X86_64.Gather.Whole

end

end


/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86-64: the instances

Untrusted: everything here is checked by Lean. The instance of
`vg_chacha20_poly1305_seal_gather` for an implementation of
`vg_chacha20_xor` copies as many bytes at a time as its CPUs can (`width`).
With the AVX-512 implementations of `vg_poly1305_blocks`, it calls that
implementation's `vg_chacha20_poly1305_seal` (`Whole.sealFn`) for at most
960 bytes of data (1024 without IFMA, `byLim`), and its `vg_chacha20_poly1305_seal_split` (`sealSplitFn`)
for more (`sealGatherBy`). The others always gather every slice and call
`seal` (`sealGatherWhole`): their `seal_split` would copy the first slice
too (`gatherCode`, `gather_verified`). The code writes `rsp` only in frames
(`gather_spSafe`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Gather

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.SealGather

open VG.Proof.ChaCha20.X86_64 VG.Impl.StackScratch.X86_64 in
/-- The instance of `vg_chacha20_poly1305_seal_split` calling the
implementation `v` of `vg_chacha20_xor`, with its working space in a frame
of its own. -/
def sealSplitFn (v : XorImpl) : SealSplitFn where
  name := "vg_chacha20_poly1305_seal_split" ++ v.suffix
  code := withStackArgScratchWipedX 1736 3 42
    (Impl.ChaCha20Poly1305.X86_64.SealSplit.sealSplitFor v.callee v.poly)
  verified := Split.sealSplit_framed v
  E _ _ := True
  exec s h := let ⟨t, s', e, a, p⟩ := (Split.sealSplit_framed v).1 s h; ⟨t, s', e, a, p, trivial⟩
  sp := SpSafe.of_all (X86_64.withStackArgScratchWipedX_spSafe (Split.sealSplitFor_spSafe v))
  depth := by
    have := Split.sealSplitFor_xdepth v
    simp only [withStackArgScratchWipedX, withStackArgScratch, Code.x86_64Depth, X86_64.Instr.frameBytes,
      Nat.zero_max, Nat.max_zero, Nat.max_le]
    omega_using [this]

open VG.Proof.ChaCha20.X86_64 in
/-- How many bytes at a time the instance for `v` copies: as many as the
CPUs of the instance of `vg_chacha20_poly1305_seal_split` it calls can. -/
def width (v : XorImpl) : Width := .ofBlocks v.poly

open VG.Proof.ChaCha20.X86_64 in
/-- No instruction of the code, or of the instance it calls, writes `rsp`
but its frames' pushes and pops. -/
theorem sealGather_spSafe (v : XorImpl) :
    (sealGather (width v) (sealSplitFn v).name (sealSplitFn v).code).all
      (fun i => !X86_64.isa.writesSp i) = true := by
  have hc : (sealSplitFn v).code.all (fun i => !X86_64.isa.writesSp i) = true :=
    X86_64.withStackArgScratchWipedX_spSafe (Split.sealSplitFor_spSafe v)
  simp only [sealGather, Code.all, hc, Bool.and_true]
  cases width v <;> decide +kernel

open VG.Proof.ChaCha20.X86_64 in
/-- The code of the instance for `v`. -/
def gatherCode (v : XorImpl) : Prog isa :=
  match v.poly with
  | .avx512 | .ifma => sealGatherBy (byLim v.poly) (width v) (Whole.sealFn v).name (Whole.sealFn v).code (sealSplitFn v).name
      (sealSplitFn v).code
  | _ => sealGatherWhole (width v) (Whole.sealFn v).name (Whole.sealFn v).code

open VG.Proof.ChaCha20.X86_64 in
theorem byLim_cases (v : XorImpl) : byLim v.poly = 961 ∨ byLim v.poly = 1025 := by
  generalize v.poly = b
  cases b <;> decide

open VG.Proof.ChaCha20.X86_64 in
theorem gather_verified (v : XorImpl) :
    Verified X86_64.target (gatherCode v) (Spec.ChaCha20Poly1305.sealGatherContract X86_64.abi 1880) := by
  unfold gatherCode
  split
  all_goals first
    | exact sealGatherBy_verified (byLim_cases v) _ _ _
    | exact sealGatherWhole_verified _ _

open VG.Proof.ChaCha20.X86_64 in
theorem gather_spSafe (v : XorImpl) : (gatherCode v).all (fun i => !X86_64.isa.writesSp i) = true := by
  have hw := Whole.sealGather_spSafe v
  have hs := sealGather_spSafe v
  unfold gatherCode
  split
  all_goals first
    | exact hw
    | (simp only [sealGatherBy, Code.all, Bool.and_eq_true]
       exact ⟨by rcases byLim_cases v with h | h <;> rw [h] <;> decide, hw, hs⟩)

end VG.Proof.ChaCha20Poly1305.X86_64.Gather
