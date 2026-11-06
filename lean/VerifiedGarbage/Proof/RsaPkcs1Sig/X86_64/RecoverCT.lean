module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverCorrect
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverCall
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCorrect
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Compare
import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverCorrect
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverCall
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCT
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCorrect
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Compare
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# `vg_rsa_pkcs1_recover` on x86-64: constant time

As for `vg_rsa_pkcs1_verify` (`VerifyCT.lean`): each point of the code is
described, in each run, by what correctness says of it from that run's entry
state, which agrees with an anchor on the public data (`At`). The blocks
between the call and the branches are checked by the taint analysis from the
registers this fixes, each branch's condition is fixed by it too, and the
call is constant time for its callee's contract. The zeros and the copy to
`out` take its address and length from the frame's slots, which the taint
analysis does not know public: their loads are a piece of their own, and the
loops after them are checked from the registers correctness fixes.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.Rec

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Recover
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (frameBytes oEM1 oEM2 sp arg arg0 lea test0 ret0 cmpArgs)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64
open VG.Proof.RsaPkcs1Sig.X86_64.Ver (fb kb stkR scrR frame_sub test0_ok relCT_alloc entry_regs regs_eq
  written_r stackArg_entry callEntry_frame below_sub)

/-! ## The taint checks -/

theorem zeroOut_taint {Φ : State → State → Prop} (h : Pins Φ [.rdi, .rsi]) :
    RelCT isa (Two Φ) zeroOut fun _ _ => True := two_taint [.rdi, .rsi] h (by taint_decide)

theorem copyRest_taint {Φ : State → State → Prop} (h : Pins Φ [.rsi, .rdi, .r9]) :
    RelCT isa (Two Φ) (.seq copyLoop (.block [.mov32 .rax (.imm 1)])) fun _ _ => True :=
  two_taint [.rsi, .rdi, .r9] h (by taint_decide)

/-! ## Entry states and the anchor -/

/-- An entry state meeting the precondition (by name) with the anchor's
public data. A variant with more public data (`RecoverPrecomputed`) uses the
pieces after the call too. -/
def Sib (a s : State) : Prop := PreR s ∧ recContract.pub a s

theorem pub_refl (s : State) : recContract.pub s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Sib.gpr {a s : State} (h : Sib a s) {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) :
    s.gpr r = a.gpr r := (h.2.1 r hr).symm

theorem Sib.h {a s : State} (h : Sib a s) : (stackArg s 0).setWidth 32 = (stackArg a 0).setWidth 32 :=
  h.2.2.1.symm

theorem Sib.arg {a s : State} (h : Sib a s) {i : Nat} (hi : 1 ≤ i) (hi' : i < 5) : stackArg s i = stackArg a i := by
  have := h.2.2.2.1
  simp only [List.cons.injEq] at this
  obtain ⟨h1, h2, h3, h4, -⟩ := this
  rcases (show i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl
  · exact h1.symm
  · exact h2.symm
  · exact h3.symm
  · exact h4.symm

theorem Sib.e {a s : State} (h : Sib a s) :
    Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat :=
  h.2.2.2.2.2.1.symm

theorem Sib.fb {a s : State} (h : Sib a s) : fb s = fb a := by
  show s.gpr .rsp - _ = a.gpr .rsp - _
  rw [h.gpr (r := .rsp) (by decide)]

theorem Sib.valA {a s : State} (h : Sib a s) : valA s = valA a := by
  show off (Ver.fb s) _ = off (Ver.fb a) _
  rw [h.fb, h.gpr (r := .rcx) (by decide), h.gpr (r := .rsi) (by decide)]

def At (J : State → State → Prop) (a t : State) : Prop := ∃ s, Sib a s ∧ J s t

theorem pin {J : State → State → Prop} {r : Reg} (f : State → BitVec 64) (hf : ∀ s t, J s t → t.gpr r = f s)
    (hs : ∀ a s, Sib a s → f s = f a) {a t₁ t₂ : State} (h₁ : At J a t₁) (h₂ : At J a t₂) :
    t₁.gpr r = t₂.gpr r := by
  obtain ⟨s₁, S₁, j₁⟩ := h₁
  obtain ⟨s₂, S₂, j₂⟩ := h₂
  rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]

theorem pinEval {J : State → State → Prop} {c : Cond} (f : State → Option Bool)
    (hf : ∀ s t, J s t → isa.eval c t = f s) (hs : ∀ a s, Sib a s → f s = f a) :
    ∀ a t₁ t₂, At J a t₁ → At J a t₂ → isa.eval c t₁ = isa.eval c t₂ := by
  rintro a t₁ t₂ ⟨s₁, S₁, j₁⟩ ⟨s₂, S₂, j₂⟩
  rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]

theorem pins_rsp {J : State → State → Prop} (hJ : ∀ s t, J s t → t.gpr .rsp = fb s) : Pins (At J) [.rsp] :=
  fun _ _ _ h₁ h₂ r hr => by
    rw [List.mem_singleton.mp hr]
    exact pin fb hJ (fun _ _ h => h.fb) h₁ h₂

/-- `At` with a condition on the state. -/
theorem at_and {J : State → State → Prop} {P : State → Prop} {a t : State} (h : At J a t ∧ P t) :
    At (fun s t => J s t ∧ P t) a t :=
  let ⟨⟨s, S, j⟩, p⟩ := h; ⟨s, S, j, p⟩

theorem two_and {J : State → State → Prop} {P : State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : RelCT isa (Two (At fun s t => J s t ∧ P t)) c Q) :
    RelCT isa (Two fun a t => At J a t ∧ P t) c Q :=
  h.mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, at_and h₁, at_and h₂⟩) fun _ _ h => h

/-! ## The points of the code -/

def J0 (s t : State) : Prop := t = s

def JL (s t : State) : Prop := Keep [.rax] s t ∧ t.mem = s.mem ∧ t.zf = some (stackArg s 2 == s.gpr .rcx)

def JA (s t : State) : Prop :=
  ∃ t₀, JL s t₀ ∧ stackArg s 2 = s.gpr .rcx ∧ t = allocState frameBytes t₀

theorem encodeId_length {x : BitVec 32} {H : List Byte} {k : Nat} {em' : List Byte}
    (h : encodeId x H k = some em') : em'.length = k := by
  unfold encodeId at h
  split at h
  · exact VG.Proof.RsaPkcs1Sig.encode_length h
  · cases h

/-! ## The call -/

theorem entryBytes {s t : State} (he : Env s t) (rd wr : List Region) {p : Addr} {len : Nat}
    (hk : (stkR s).Disjoint ⟨p, len⟩) (ho : (outR s).Disjoint ⟨p, len⟩) (hs : (scrR s).Disjoint ⟨p, len⟩)
    (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt (t.callEntry.withRegions rd wr).mem p len = Spec.Rsa.bytesAt s.mem p len := by
  rw [State.withRegions_mem]
  exact bytes_of_frame (frame_call he.mem (callEntry_frame he.rsp) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inl (below_sub s)) hk ho hs hl

/-! ## Zeros and the copy to `out` -/

def JZ (s t : State) : Prop := t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = s.gpr .rsi

def JC (s t : State) : Prop := t.gpr .rsi = valA s ∧ t.gpr .rdi = s.gpr .rdi ∧ t.gpr .r9 = s.gpr .rsi

theorem zeroSlots_ct {J : State → State → Prop} (hJ : ∀ s t, J s t → Env s t) :
    RelCT isa (Two (At J)) zeroSlots fun _ _ => True := by
  unfold zeroSlots
  refine RelCT.seq (two_piece [.rsp] (pins_rsp fun s t h => (hJ s t h).rsp) (by taint_decide)
    (Ψ := At JZ) fun _ t ⟨s, S, h⟩ => WP.mono (zeroHead_ok S.1 (hJ s t h))
      fun _ ⟨_, _, hdi, hsi⟩ => ⟨s, S, hdi, hsi⟩) (zeroOut_taint fun _ _ _ h₁ h₂ r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact pin (fun s => s.gpr .rdi) (fun _ _ h => h.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
  · exact pin (fun s => s.gpr .rsi) (fun _ _ h => h.2) (fun _ _ S => S.gpr (by decide)) h₁ h₂

theorem copyOut_ct {J : State → State → Prop} (hJ : ∀ s t, J s t → Env s t ∧ t.gpr .rcx = s.gpr .rcx) :
    RelCT isa (Two (At J)) copyOut fun _ _ => True := by
  unfold copyOut
  refine RelCT.seq (two_piece [.rsp] (pins_rsp fun s t h => (hJ s t h).1.rsp) (by taint_decide)
    (Ψ := At JC) fun _ t ⟨s, S, h⟩ => WP.mono (copyHead_ok S.1 (hJ s t h).1 (hJ s t h).2)
      fun _ ⟨_, _, _, hdi, h9, hsi⟩ => ⟨s, S, hsi, hdi, h9⟩) (copyRest_taint fun _ _ _ h₁ h₂ r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact pin valA (fun _ _ h => h.1) (fun _ _ S => S.valA) h₁ h₂
  · exact pin (fun s => s.gpr .rdi) (fun _ _ h => h.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
  · exact pin (fun s => s.gpr .rsi) (fun _ _ h => h.2.2) (fun _ _ S => S.gpr (by decide)) h₁ h₂

end VG.Proof.RsaPkcs1Sig.X86_64.Rec
