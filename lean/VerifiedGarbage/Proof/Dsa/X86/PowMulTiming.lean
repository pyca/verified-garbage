module

import VerifiedGarbage.Proof.Dsa.X86.PowOuts
public import VerifiedGarbage.Impl.Dsa.X86.Pow
import VerifiedGarbage.Proof.Dsa.X86.PowMul
import VerifiedGarbage.Proof.Bignum.X86.RtCall
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Mont.X86.Sse2.AtVerified
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Callee
import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
public import VerifiedGarbage.Proof.Mont.X86.OutsZ
public import VerifiedGarbage.Proof.Rsa.MontMulContract

/-! # The trace of a multiplication of DSA's exponentiation, by a call

Two runs of `mul n o a b` leak the same trace when both are ready for it
(`MulIn`: a context with its modulus, slot `b` below it, and the call's stack
apart from the working space) from the same stack pointer: the frame's
arguments are written from public values (the taint analysis), after which
each run's call meets the callee's precondition (`CallOk`, `mulArgs_call`),
and their arguments agree (`mul_relCT`).
-/

@[expose] public section

namespace VG.Proof.Dsa.X86.Pow

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Dynamic VG.Proof.Mont.X86.Rt VG.Impl.Dsa.X86.Pow
open VG.Proof.Bignum.X86.PublicRt (calleeOf)
open VG.Proof.Bignum.X86.RtCall (callArg)

/-- Two runs, each meeting `F`. -/
abbrev Both (F : State → Prop) (s t : State) : Prop := F s ∧ F t

theorem relCT_both {P F : State → Prop} {c : Prog isa} (hct : RelCT isa (Both P) c fun _ _ => True)
    (hw : ∀ s, P s → WP isa c s F) : RelCT isa (Both P) c (Both F) :=
  (hct.wp (F₁ := F) (F₂ := F) fun s t h => ⟨hw s h.1, hw t h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- What a multiplication needs of a run: a context, slot `b` below its
modulus, and the call's stack at `sp`, apart from the working space. -/
def MulIn (n : Nat) (base : Addr) (sp : BitVec 32) (b : Nat) (s : State) : Prop :=
  ∃ size m, Context n m base size s ∧ CallRoom sp base size ∧ s.gpr .esp = sp ∧
    VG.Proof.Mont.wordsVal s.mem base (slot n b) n < m

/-- The state of the call: the callee's precondition, its arguments and the regions it is given. -/
private def CallOk (n : Nat) (base : Addr) (sp : BitVec 32) (o a b : Nat) (g : State) : Prop :=
  (Proof.Rsa.MontMul.mulContract abi 56).pre (calleeOf g base (contextBytes n)) ∧
    g.gpr .esp = sp - BitVec.ofNat 32 36 ∧
    (∀ i < 9, arg (calleeOf g base (contextBytes n)) i =
      callArg (BitVec.ofNat 32 base.toNat) (BitVec.ofNat 32 (contextBytes n / 8)) n (slot n 0) 0
        (calleeScratch n) (slot n o) (slot n a) (slot n b) i) ∧
    (⟨(g.gpr .esp).setWidth 64, 36⟩ : Region) ∈ g.wr ∧ Covers [⟨base, contextBytes n⟩] g.wr

/-- The context's bytes, within the working space. -/
private theorem covers_context {n size : Nat} {base : Addr} {g : State} (h : (⟨base, size⟩ : Region) ∈ g.wr)
    (cb : contextBytes n ≤ size) : Covers [⟨base, contextBytes n⟩] g.wr :=
  Covers.of_sub fun r hr => ⟨⟨base, size⟩, h, 0, by rw [List.mem_singleton.mp hr]; simp,
    by rw [List.mem_singleton.mp hr]; simpa using cb⟩

private theorem mulArgs_call {n : Nat} {base : Addr} {sp : BitVec 32} {o a b : Nat} (hn : 2 ≤ n)
    (ho : 4 ≤ o) (ho7 : o ≤ 7) (ha : 4 ≤ a) (ha7 : a ≤ 7) (hb : 4 ≤ b) (hb7 : b ≤ 7)
    {s : State} (I : MulIn n base sp b s) :
    WP isa (.block (mulArgs n o a b)) (allocFrame 36 s) (CallOk n base sp o a b) := by
  obtain ⟨size, m, h, R, hsp, hB⟩ := I
  have cb := h.size_le
  have nw := h.scr.nowrap
  have low := R.low
  rw [← hsp] at R low
  have fEsp : (allocFrame 36 s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 36 := allocFrame_esp _ _
  refine WP.mono (mulArgs_ok (o := o) (a := a) (b := b)
    (by rw [fEsp, VG.X86.sub_toNat (by omega)]; have := (s.gpr .esp).isLt; omega)
    (by rw [allocFrame_wr]; exact List.mem_cons_self ..)) fun g ⟨Kg, Fg, Rg⟩ => ?_
  have gEsp : g.gpr .esp = s.gpr .esp - BitVec.ofNat 32 36 := by rw [Kg.1 _ (by decide), fEsp]
  have hFg : Frame [below (s.gpr .esp) 36] s.mem g.mem := by
    have := Fg; rwa [fEsp, allocFrame_mem] at this
  have edi : s.gpr .edi = BitVec.ofNat 32 base.toNat := by
    apply BitVec.eq_of_toNat_eq
    have : 0 < contextBytes n := by simp only [contextBytes, slot, stride]; omega
    rw [h.scr.edi_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hread : ∀ i < 9, g.mem.readW ((g.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 =
      callArg (s.gpr .edi) (BitVec.ofNat 32 (contextBytes n / 8)) n (slot n 0) 0 (calleeScratch n)
        (slot n o) (slot n a) (slot n b) i := by
    intro i hi; rw [gEsp, ← fEsp, Rg i hi, allocFrame_gpr _ _ (by decide)]
  -- The callee's view: the working space narrowed to the context.
  let s' := s.withRegions s.rd [⟨base, contextBytes n⟩]
  have hscr : Scr s' base (contextBytes n) :=
    ⟨h.scr.edi, List.mem_singleton_self _, by omega, stkOk_mono h.scr.stk cb⟩
  have R' : CallRoom (s'.gpr .esp) base (contextBytes n) :=
    ⟨low, fun x h₁ h₂ => R.apart x h₁ (by simp only [Region.Contains] at h₂ ⊢; omega)⟩
  have hv : VG.Proof.Mont.wordsVal s.mem base (slot n 0) n = m := h.modulus.val
  have hinv : (VG.Proof.Mont.val32 s'.mem base (slot n 0) (2 * n) * w32 s'.mem base 0 + 1) % 2 ^ 32 = 0 := by
    show (VG.Proof.Mont.val32 s.mem base (slot n 0) (2 * n) * w32 s.mem base 0 + 1) % 2 ^ 32 = 0
    rw [← wordsVal_eq_val32, hv]; exact h.inverse
  have hB' : VG.Proof.Mont.val32 s'.mem base (slot n b) (2 * n) < VG.Proof.Mont.val32 s'.mem base (slot n 0) (2 * n) := by
    show VG.Proof.Mont.val32 s.mem base (slot n b) (2 * n) < VG.Proof.Mont.val32 s.mem base (slot n 0) (2 * n)
    rw [← wordsVal_eq_val32, ← wordsVal_eq_val32, hv]; exact hB
  have hlen : contextBytes n = (BitVec.ofNat 32 (contextBytes n / 8)).toNat * 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), contextBytes_div]
  have A := VG.Proof.Bignum.X86.RtCall.callee_abi (s := s') hscr hlen R' (offs hn ho ho7 ha ha7 hb hb7)
    gEsp hFg hread hinv hB'
  refine ⟨VG.Proof.Bignum.X86.PublicRt.callee_pre A R' gEsp, by rw [gEsp, hsp], fun i hi => ?_, ?_, ?_⟩
  · rw [VG.Proof.Bignum.X86.RtCall.callee_arg (base := base) (bytes := contextBytes n) (by simpa using low)
      gEsp hread hi, edi]
  · rw [Kg.2.2, allocFrame_wr, gEsp, ← fEsp]; exact List.mem_cons_self ..
  · refine covers_context (g := g) ?_ cb
    rw [Kg.2.2, allocFrame_wr]; exact List.mem_cons_of_mem _ h.scr.wr

/-- The callee's public data from its stack pointer and its arguments. -/
private theorem rtPub_of {s t : State} (sp : s.gpr .esp = t.gpr .esp) (args : ∀ i < 9, arg s i = arg t i) :
    (Proof.Rsa.MontMul.mulContract abi 56).pub s t := by
  have a0 := args 0 (by decide); have a1 := args 1 (by decide); have a2 := args 2 (by decide)
  have a3 := args 3 (by decide); have a4 := args 4 (by decide); have a5 := args 5 (by decide)
  have a6 := args 6 (by decide); have a7 := args 7 (by decide); have a8 := args 8 (by decide)
  sig_pub [Proof.Rsa.MontMul.mulContract, Proof.Rsa.MontMul.sig, abi, argSlots, argVal, argBytes]
  sig_and_intros
  all_goals with_reducible assumption

private theorem calleeOf_eq {g : State} {base : Addr} {bytes : Nat} {sp : BitVec 32}
    (hsp : g.gpr .esp = sp - BitVec.ofNat 32 36) :
    calleeOf g base bytes =
      g.callEntry.withRegions [⟨(sp - BitVec.ofNat 32 36).setWidth 64, 36⟩] [⟨base, bytes⟩] := by
  simp only [calleeOf, argAddr_callEntry, hsp, Nat.mul_zero, BitVec.add_zero]

theorem mul_relCT {n : Nat} {base : Addr} (sp : BitVec 32) {o a b : Nat} (hn : 2 ≤ n)
    (ho : 4 ≤ o) (ho7 : o ≤ 7) (ha : 4 ≤ a) (ha7 : a ≤ 7) (hb : 4 ≤ b) (hb7 : b ≤ 7) :
    RelCT isa (Both (MulIn n base sp b)) (VG.Impl.Dsa.X86.Pow.mul n o a b) (fun _ _ => True) := by
  unfold VG.Impl.Dsa.X86.Pow.mul
  refine RelCT.frameAlloc (R := fun _ _ => True) ?_
  have blk := (RelCT.taint (A := taint) (P := fun f₁ f₂ => ∃ s₁ s₂, Both (MulIn n base sp b) s₁ s₂ ∧
      f₁ = allocFrame 36 s₁ ∧ f₂ = allocFrame 36 s₂) (c := (.block (mulArgs n o a b) : Prog isa))
      (τr [.edi, .esp]) (hc := .block [])
      (fun _ _ ⟨s₁, s₂, ⟨⟨_, _, h₁, _, e₁, _⟩, ⟨_, _, h₂, _, e₂, _⟩⟩, q₁, q₂⟩ => by
        subst q₁ q₂
        refine agree_regs fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [allocFrame_gpr _ _ (by decide), allocFrame_gpr _ _ (by decide)]
          exact BitVec.eq_of_toNat_eq (h₁.scr.edi_toNat.trans h₂.scr.edi_toNat.symm)
        · simp only [allocFrame_esp, e₁, e₂])
      (by
        have e : VG.X86.Code.erase (.block (mulArgs n o a b) : Prog isa) = VG.X86.Code.erase (.block (mulArgs 2 4 4 4)) := rfl
        exact (congrArg Option.isSome
          (VG.Proof.Mont.X86.Dynamic.check_of_erase_eq _ _ (τr [.edi, .esp]) (.block []) e rfl rfl)).trans rfl)).wp
    (F₁ := CallOk n base sp o a b) (F₂ := CallOk n base sp o a b)
    (fun _ _ ⟨s₁, s₂, ⟨I₁, I₂⟩, q₁, q₂⟩ => by
      subst q₁ q₂
      exact ⟨mulArgs_call hn ho ho7 ha ha7 hb hb7 I₁, mulArgs_call hn ho ho7 ha ha7 hb hb7 I₂⟩)
  refine VG.RelCT.seq blk ?_
  refine RelCT.call (k := Proof.Rsa.MontMul.mulContract abi 56) VG.Proof.Mont.X86.Sse2.at_correct
    VG.Proof.Mont.X86.Sse2.at_constantTime
    [⟨(sp - BitVec.ofNat 32 36).setWidth 64, 36⟩] [⟨base, contextBytes n⟩] ?_
  rintro g₁ g₂ ⟨-, ⟨A₁, sp₁, arg₁, fr₁, sc₁⟩, ⟨A₂, sp₂, arg₂, fr₂, sc₂⟩⟩
  have c₁ := calleeOf_eq (base := base) (bytes := contextBytes n) sp₁
  have c₂ := calleeOf_eq (base := base) (bytes := contextBytes n) sp₂
  rw [sp₁] at fr₁
  rw [sp₂] at fr₂
  refine ⟨c₁ ▸ A₁, c₂ ▸ A₂, ?_, ?_, sc₁, ?_, sc₂, by rw [sp₁, sp₂]⟩
  · rw [← c₁, ← c₂]
    refine rtPub_of ?_ fun i hi => (arg₁ i hi).trans (arg₂ i hi).symm
    simp only [calleeOf, State.withRegions_gpr, State.callEntry_esp, sp₁, sp₂]
  · exact Covers.append_left (Covers.of_mem fun r hr => by
      rw [List.mem_singleton.mp hr]; exact List.mem_append_right _ fr₁) sc₁.right
  · exact Covers.append_left (Covers.of_mem fun r hr => by
      rw [List.mem_singleton.mp hr]; exact List.mem_append_right _ fr₂) sc₂.right

end VG.Proof.Dsa.X86.Pow
