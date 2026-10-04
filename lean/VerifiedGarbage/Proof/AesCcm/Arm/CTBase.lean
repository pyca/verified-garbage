import VerifiedGarbage.Proof.AesCcm.Arm.Open
import VerifiedGarbage.Proof.AesGcm.Arm.CTBase
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# AES-CCM on ARMv7: constant time, the invariants

Untrusted: everything here is checked by Lean. Two runs of `seal` or `open`
with the same public arguments (`onePub`) are related piece by piece by
invariants `CT I` (`Proof.AesGcm.Arm.CT`), whose parameters are the public
values: the pointers, the lengths, the rounds and `W` (`One`, the
arguments, as `Args`, with their values on the stack; `PubArgs`, which the
taint analysis of blocks reading them needs, `CT.args`). Each piece's
correctness lemma, in each run, gives the invariant of the next
(`One.next`).
-/

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (CT ArgsKeep arg_frame)

/-- The stack arguments `a`, which the code may not write, as public. -/
structure PubArgs (sp : BitVec 32) (a : Nat → BitVec 32) (s : State) : Prop where
  hsp : s.sp = sp
  fit : sp.toNat + 4 * 7 ≤ 2 ^ 32
  wr : ∀ r ∈ s.wr, (args s 7).Disjoint r
  arg : ∀ i < 7, stackArg s i = a i

/-- A block the taint analysis checks from the registers `rs` and the stack
arguments, the same in both runs. -/
theorem CT.args {I : State → Prop} {c : Prog isa} {sp : BitVec 32} {a : Nat → BitVec 32} (rs : List Reg)
    (hI : ∀ s, I s → PubArgs sp a s) (hp : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint rs (4 * 7)) c h).isSome = true) : CT I c := by
  obtain ⟨_, hc⟩ := hc
  refine Proof.AesGcm.Arm.CT.argTaint rs (4 * 7) hp (fun s₁ s₂ h₁ h₂ => (hI _ h₁).hsp.trans (hI _ h₂).hsp.symm)
    (fun s h => ⟨by rw [(hI s h).hsp]; exact (hI s h).fit, fun r hr => ?_⟩)
    (fun s₁ s₂ h₁ h₂ => argMem_of ((hI _ h₁).hsp.trans (hI _ h₂).hsp.symm) (by rw [(hI _ h₁).hsp]; exact (hI _ h₁).fit)
      fun i hi => by rw [(hI _ h₁).arg i hi, (hI _ h₂).arg i hi]) hc
  have := (hI s h).wr r hr
  rwa [show Proof.AesCcm.Arm.args s 7 = ⟨State.addr s.sp, 4 * 7⟩ by
    simp only [Proof.AesCcm.Arm.args, Proof.AesGcm.Arm.argAddr_zero]] at this

/-- `a; (b; c)`, from `(a; b); c`. -/
theorem CT.assoc {I : State → Prop} {a b c : Prog isa} (h : CT I (.seq (.seq a b) c)) : CT I (.seq a (.seq b c)) :=
  RelCT.assoc h

/-- `a; (b; (c; (d; e)))`, from `(a; (b; (c; d))); e`. -/
theorem CT.assoc4 {I : State → Prop} {a b c d e : Prog isa} (h : CT I (.seq (.seq a (.seq b (.seq c d))) e)) :
    CT I (.seq a (.seq b (.seq c (.seq d e)))) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq a₁ e₁ => cases e₁ with | seq b₁ e₁ => cases e₁ with | seq c₁ e₁ => cases e₁ with
    | seq d₁ f₁ =>
  cases e₂ with | seq a₂ e₂ => cases e₂ with | seq b₂ e₂ => cases e₂ with | seq c₂ e₂ => cases e₂ with
    | seq d₂ f₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ (.seq b₁ (.seq c₁ d₁))) f₁)
    (.seq (.seq a₂ (.seq b₂ (.seq c₂ d₂))) f₂)
  simp only [List.append_assoc] at ht
  exact ⟨ht, hq⟩

/-- The values of the stack arguments. -/
abbrev argVals (A D T w : BitVec 32) (al n tl : Nat) (i : Nat) : BitVec 32 :=
  [A, BitVec.ofNat 32 al, D, BitVec.ofNat 32 n, T, BitVec.ofNat 32 tl, w].getD i 0

/-- One run between the pieces, with its public values: the arguments, the
stack pointer and what the code may write. -/
structure One (k w sp N A D T : BitVec 32) (R nl al n tl : Nat) (s : State) : Prop where
  ar : Args s k w N A D R nl al n tl
  sp : s.sp = sp
  wr : ∀ r ∈ s.wr, (args s 7).Disjoint r
  eA : stackArg s 0 = A
  eal : stackArg s 1 = BitVec.ofNat 32 al
  eD : stackArg s 2 = D
  en : stackArg s 3 = BitVec.ofNat 32 n
  eT : stackArg s 4 = T
  etl : stackArg s 5 = BitVec.ofNat 32 tl
  eW : stackArg s 6 = w

namespace One

variable {k w sp N A D T : BitVec 32} {R nl al n tl : Nat} {s : State} (h : One k w sp N A D T R nl al n tl s)
include h

theorem pubArgs : PubArgs sp (argVals A D T w al n tl) s where
  hsp := h.sp
  fit := by rw [← h.sp]; exact h.ar.stk.fit
  wr := h.wr
  arg i hi := by
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h.eA
    · exact h.eal
    · exact h.eD
    · exact h.en
    · exact h.eT
    · exact h.etl
    · exact h.eW

/-- After code that writes regions apart from the stack arguments. -/
theorem next' {s' : State} {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, (args s 7).Disjoint r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : One k w sp N A D T R nl al n tl s' := by
  have Ar := h.ar
  have hk : Stk w s s' := Ar.stk.frame hf hd hsp hrd hwr
  have ea : args s' 7 = args s 7 := Proof.AesGcm.Arm.args_sp hsp 7
  have ka : ∀ i < 7, stackArg s' i = stackArg s i := hk.keep.arg
  have sb : blw s'.sp = blw s.sp := by rw [hsp]
  refine ⟨?_, by rw [hsp, h.sp], by rw [hwr, ea]; exact h.wr, by rw [ka 0 (by decide), h.eA],
    by rw [ka 1 (by decide), h.eal], by rw [ka 2 (by decide), h.eD], by rw [ka 3 (by decide), h.en],
    by rw [ka 4 (by decide), h.eT], by rw [ka 5 (by decide), h.etl], by rw [ka 6 (by decide), h.eW]⟩
  have L := Ar.lay
  exact {
    lay := ⟨L.kw, L.ww, by rw [hsp]; exact L.sp16, L.k_w, by rw [sb]; exact L.stk_k, by rw [sb]; exact L.stk_w⟩
    perm := Ar.perm.of_eq hrd hwr
    stk := ⟨ArgsKeep.refl 7 s', by rw [hsp]; exact Ar.stk.fit, by rw [ea, hrd]; exact Ar.stk.rd,
      by rw [ea]; exact Ar.stk.aw⟩
    rounds := Ar.rounds
    nonce := { Ar.nonce.of_eq hrd hwr with stk := by rw [sb]; exact Ar.nonce.stk }
    aad := { Ar.aad.of_eq hrd hwr with stk := by rw [sb]; exact Ar.aad.stk }
    data := ⟨{ Ar.data.buf.of_eq hrd hwr with stk := by rw [sb]; exact Ar.data.buf.stk }, by rw [hwr]; exact Ar.data.wr,
      Ar.data.k⟩
    nd := Ar.nd
    ad := Ar.ad
    da := by rw [ea]; exact Ar.da
    h7 := Ar.h7
    h13 := Ar.h13
    t4 := Ar.t4
    t16 := Ar.t16
    te := Ar.te
    hn := Ar.hn
    n32 := Ar.n32
    al32 := Ar.al32 }

/-- After code that writes regions within `mutR`. -/
theorem next {s' : State} {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ mutR w sp D n, Region.Sub r r') (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : One k w sp N A D T R nl al n tl s' := by
  rw [← h.sp] at hsub
  exact h.next' (hf.sub hsub) (args_mut h.ar) hsp hrd hwr

end One

end VG.Proof.AesCcm.Arm
