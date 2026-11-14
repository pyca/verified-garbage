module
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivCrt
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivPd

import VerifiedGarbage.Proof.Rsa.X86_64.PrivCorrect
import VerifiedGarbage.Proof.Rsa.X86_64.PrivCheck
import VerifiedGarbage.Proof.Rsa.X86_64.PrivTail
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rsa.X86_64.PrivCrt
meta import VerifiedGarbage.Proof.Rsa.X86_64.PrivPd
meta import VerifiedGarbage.Proof.Rsa.X86_64.PrivCorrect
meta import VerifiedGarbage.Proof.Rsa.X86_64.PrivCheck
meta import VerifiedGarbage.Proof.Rsa.X86_64.PrivTail
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Rsa.Contract
meta import VerifiedGarbage.Proof.Rsa.Contract

/-!
# `vg_rsa_private_checked` on x86-64: constant time

Two runs from entry states that agree on the public data (`chkContract.pub`:
the pointers and lengths, `n` and `e`) leak the same trace. Each point of
the code is described, in each run, by what correctness says of it from that
run's entry state, which agrees with an anchor `a` on the public data
(`At`): the blocks between the calls are checked by the taint analysis
from the registers this fixes, and each call is constant time for its
callee's contract, whose public data it fixes too (`body_ct`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.PrivChecked
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-! ## Entry states and the anchor -/

theorem pub_refl (s : State) : chkContract.pub s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

/-- A caller's buffer, read by a callee: the same as at the entry. -/
theorem Env.entryBytes {s t : State} (he : Env s t) (rd wr : List Region) {p : Addr} {len : Nat}
    (hk : (stkR s).Disjoint ⟨p, len⟩) (ho : (outR s).Disjoint ⟨p, len⟩) (hs : (scrR s).Disjoint ⟨p, len⟩)
    (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt (t.callEntry.withRegions rd wr).mem p len = Spec.Rsa.bytesAt s.mem p len := by
  rw [State.withRegions_mem]
  exact bytes_of_frame (frame_call he.mem (callEntry_frame he.rsp) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inl (below_sub s)) hk ho hs hl

/-! ## The points of the code -/

def J0 (s t : State) : Prop := t = allocState frameBytes s

def J1 (s t : State) : Prop :=
  Env s t ∧ (∀ i < 12, word t.mem (fb s) (8 * i) = stackArg s (i + 2)) ∧ t.gpr .rdi = off (fb s) oM ∧
    t.gpr .rsi = s.gpr .rcx ∧ t.gpr .rdx = s.gpr .rdx ∧ t.gpr .rcx = s.gpr .rcx ∧ t.gpr .r8 = stackArg s 0 ∧
    t.gpr .r9 = s.gpr .rcx

def J2 (s t : State) : Prop := Env s t

def J7 (s t : State) : Prop :=
  t.gpr .rsp = fb s ∧ t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = stackArg s 0 ∧ t.gpr .rcx = s.gpr .rcx ∧
    t.gpr .r10 = BitVec.ofNat 64 0

/-! ## The calls -/

/-- The registers a callee sees, from the caller's. -/
theorem entry_regs (t : State) (rd wr : List Region) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions rd wr).gpr =
      [t.gpr .rdi, t.gpr .rsi, t.gpr .rdx, t.gpr .rcx, t.gpr .r8, t.gpr .r9, t.gpr .rsp - 8] := by
  simp only [List.map_cons, List.map_nil, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide)]

theorem regs_eq {s₁ s₂ : State}
    (h : [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map s₁.gpr = [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map s₂.gpr) :
    ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r :=
  List.map_inj_left.mp h

/-! ## The pieces -/

theorem tail_eq : seqs PrivChecked.tail =
    .seq (.block cmpArgs) (.seq cmpLoop (.seq (.block masks) (.seq releaseLoop (.block [.mov .rax (.reg .r11)])))) :=
  rfl

/-! ## The frame -/

theorem alloc_push {s s₁ : State} (h : isa.push (.alloc frameBytes) s = some s₁) : s₁ = allocState frameBytes s := by
  simp only [isa, push] at h
  split at h
  · cases h; rfl
  · cases h

/-- A frame of `frameBytes` bytes leaks what its body does. -/
theorem relCT_alloc {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = allocState frameBytes s₁ ∧ b = allocState frameBytes s₂)
      body R) :
    RelCT isa P (.frame (.alloc frameBytes) body (.free frameBytes)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      obtain rfl := alloc_push p₁
      obtain rfl := alloc_push p₂
      obtain ⟨rfl, -⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ b₁ b₂
      exact ⟨rfl, trivial⟩

/-! ## `Verified` -/

end VG.Proof.Rsa.X86_64
