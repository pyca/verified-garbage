module

public import VerifiedGarbage.Proof.Dsa.X86.PowABI
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.ModPowContract
public import VerifiedGarbage.Proof.Dsa.X86.PowCore
public import VerifiedGarbage.Impl.Dsa.X86.Pow
import VerifiedGarbage.Proof.Bignum.X86.RtCall
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Mont.X86.Sse2.AtVerified
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Callee
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
public import VerifiedGarbage.Proof.Mont.X86.OutsZ
public import VerifiedGarbage.Proof.Mont.X86.ArgWs
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
public import VerifiedGarbage.Proof.Mont.X86.ContextInit
public import VerifiedGarbage.Proof.Mont.X86.ExponentTiming
public import VerifiedGarbage.Proof.Mont.X86.PowerTiming
import VerifiedGarbage.Proof.Mont.X86.ExponentTimingBlocks
import VerifiedGarbage.Proof.Mont.X86.PowerInit
public import VerifiedGarbage.Proof.Dsa.X86.PowEntry
import VerifiedGarbage.Proof.Dsa.X86.EntryTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Impl.Mont.X86.Context
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32

/-! ### `Dsa.X86.PowBody`, which this module and modules that import it used -/

section

/-! # IA-32 DSA exponentiation with its callee-saved registers restored -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Pow
open VG VG.X86 VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Pow

theorem core_saved {s t : State} {base : Addr} {sp : BitVec 32} {size n : Nat} {g : Reg → BitVec 32}
    (O : OutsS base sp (coreRanges n) s.mem t.mem) (R : CallRoom sp base size) (nw : base.toNat + size ≤ 2 ^ 32)
    (hz : 24 ≤ size) (H : Saved s.mem (off base) g slots) : Saved t.mem (off base) g slots := by
  intro p hp
  have hp' : 8 ≤ p.2 ∧ p.2 + 4 ≤ 24 := by
    simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  rw [O.readW32 R nw (fun r hr => by
      simp only [coreRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [slot_lin] <;> omega_using [hp']) (by omega_using [hz, hp'])]
  exact H p hp

theorem body_ok {s : State} {base : Addr} {size n e m : Nat}
    (E : Entry s base size) (R : CallRoom (s.gpr .esp) base size) (hz : contextBytes n ≤ size)
    (hn : 2 ≤ n) (hn48 : n ≤ 48) (he : 1 < e) (hen : e ≤ 2 * n)
    (hv : wordsVal s.mem base (slot n 0) n = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (body n e) s fun t =>
      wordsVal t.mem base (slot n 6) n =
        wordsVal s.mem base (slot n 5) n ^ val32 s.mem base (slot n 8) e % m ∧
      OutsS base (s.gpr .esp) (scratch n) s.mem t.mem ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have nw := E.nowrap
  have hz24 : 24 ≤ size := by simp only [contextBytes, slot, stride] at hz; omega_using [hz]
  unfold body
  refine WP.seq (WP.mono (save_ok E hz24) fun u ⟨Su, Saved, Ou, Ku⟩ => ?_)
  have uesp : u.gpr .esp = s.gpr .esp := Ku.1 _ (by decide)
  have vals : ∀ {d k : Nat}, 24 ≤ d → d + 4 * k ≤ 2 ^ 64 →
      val32 u.mem base d k = val32 s.mem base d k :=
    fun hd hk => Ou.val32 (by omega_using [hd]) hk
  have V : wordsVal u.mem base (slot n 0) n = m := by
    rw [wordsVal_eq_val32, vals (by simp only [slot]; omega_using []) (by simp only [slot, stride]; omega_using [hn48]),
      ← wordsVal_eq_val32, hv]
  refine WP.seq (WP.mono (core_ok Su (by rw [uesp]; exact R) hz hn hn48 he hen V hm1 hodd)
    fun v ⟨Vv, Ov, Kv⟩ => ?_)
  rw [uesp] at Ov
  refine WP.mono (restore_ok (Su.of_keeps Kv (by decide)) hz24 (core_saved Ov R nw hz24 Saved))
    fun t R' => ⟨?_, ?_, R'.abi (by decide) (by decide) ?_, ?_, ?_⟩
  · rw [R'.mem, Vv, wordsVal_eq_val32, vals (by simp only [slot]; omega_using [])
      (by simp only [slot, stride]; omega_using [hn48]), vals (by simp only [slot]; omega_using [])
      (by simp only [slot, stride]; omega_using [hn48, hen]), ← wordsVal_eq_val32]
  · rw [R'.mem]
    refine (OutsS.of_outs (Outs.of_outside (Ou.mono (by decide) (by decide)) (List.mem_cons_self ..))).trans ?_
    refine Ov.widen fun y hy r hr => ?_
    simp only [coreRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    have h0 := hy (0, 64) (List.mem_cons_self ..)
    have h1 := hy _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    rcases hr with rfl | rfl <;> dsimp only at * <;> omega_arith
  · exact (Kv.1 _ (by decide)).trans (Ku.1 _ (by decide))
  · rw [R'.rd, Kv.2.1, Ku.2.1]
  · rw [R'.wr, Kv.2.2, Ku.2.2]

end VG.Proof.Dsa.X86.Pow

end

end

/-! ### `Dsa.X86.PowTiming`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86.PowCoreTiming`, which only this module used -/

section

/-! ### `Dsa.X86.PowMulTiming`, which only this module used -/

section

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
    (by rw [fEsp, VG.X86.sub_toNat (by omega_using [low])]; have := (s.gpr .esp).isLt; omega_using [])
    (by rw [allocFrame_wr]; exact List.mem_cons_self ..)) fun g ⟨Kg, Fg, Rg⟩ => ?_
  have gEsp : g.gpr .esp = s.gpr .esp - BitVec.ofNat 32 36 := by rw [Kg.1 _ (by decide), fEsp]
  have hFg : Frame [below (s.gpr .esp) 36] s.mem g.mem := by
    have := Fg; rwa [fEsp, allocFrame_mem] at this
  have edi : s.gpr .edi = BitVec.ofNat 32 base.toNat := by
    apply BitVec.eq_of_toNat_eq
    have : 0 < contextBytes n := by simp only [contextBytes, slot, stride]; omega_using []
    rw [h.scr.edi_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [cb, nw, this])]
  have hread : ∀ i < 9, g.mem.readW ((g.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 =
      callArg (s.gpr .edi) (BitVec.ofNat 32 (contextBytes n / 8)) n (slot n 0) 0 (calleeScratch n)
        (slot n o) (slot n a) (slot n b) i := by
    intro i hi; rw [gEsp, ← fEsp, Rg i hi, allocFrame_gpr _ _ (by decide)]
  -- The callee's view: the working space narrowed to the context.
  let s' := s.withRegions s.rd [⟨base, contextBytes n⟩]
  have hscr : Scr s' base (contextBytes n) :=
    ⟨h.scr.edi, List.mem_singleton_self _, by omega_using [cb, nw], stkOk_mono h.scr.stk cb⟩
  have R' : CallRoom (s'.gpr .esp) base (contextBytes n) :=
    ⟨low, fun x h₁ h₂ => R.apart x h₁ (by simp only [Region.Contains] at h₂ ⊢; omega_using [cb, h₂])⟩
  have hv : VG.Proof.Mont.wordsVal s.mem base (slot n 0) n = m := h.modulus.val
  have hinv : (VG.Proof.Mont.val32 s'.mem base (slot n 0) (2 * n) * w32 s'.mem base 0 + 1) % 2 ^ 32 = 0 := by
    show (VG.Proof.Mont.val32 s.mem base (slot n 0) (2 * n) * w32 s.mem base 0 + 1) % 2 ^ 32 = 0
    rw [← wordsVal_eq_val32, hv]; exact h.inverse
  have hB' : VG.Proof.Mont.val32 s'.mem base (slot n b) (2 * n) < VG.Proof.Mont.val32 s'.mem base (slot n 0) (2 * n) := by
    show VG.Proof.Mont.val32 s.mem base (slot n b) (2 * n) < VG.Proof.Mont.val32 s.mem base (slot n 0) (2 * n)
    rw [← wordsVal_eq_val32, ← wordsVal_eq_val32, hv]; exact hB
  have hlen : contextBytes n = (BitVec.ofNat 32 (contextBytes n / 8)).toNat * 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [cb, nw]), contextBytes_div]
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

end

end


/-! # The trace of DSA's exponentiation core

Two runs of the core leak the same trace from the same stack pointer. What
each piece needs of a run (`Wk`: the core's state `St`, the counter where the
code uses it, and the slots that a later call takes as its second operand
below the modulus) each piece keeps: the pieces between calls are checked by
the taint analysis, which needs `edi` (and `esi`, the counter) to agree, and
the calls are related by `mul_relCT`.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86.Pow

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Dynamic VG.Impl.Dsa.X86.Pow

section
variable {n : Nat} {base : Addr} {sp : BitVec 32}

/-- A run of the core: its state `St` from a start at `sp`, the counter
`cnt` in `esi` where known, and the slots `bs` below the modulus. -/
def Wk (n : Nat) (base : Addr) (sp : BitVec 32) (cnt : Option Nat) (bs : List Nat) (u : State) : Prop :=
  ∃ size m s₀, St n m size base s₀ u ∧ s₀.gpr .esp = sp ∧
    (∀ c, cnt = some c → u.gpr .esi = BitVec.ofNat 32 c) ∧
    ∀ b ∈ bs, VG.Proof.Mont.wordsVal u.mem base (slot n b) n < m

theorem Wk.agree {cnt : Option Nat} {bs : List Nat} {s t : State} (W₁ : Wk n base sp cnt bs s)
    (W₂ : Wk n base sp cnt bs t) : VG.X86.Taint.Agree (workspaceTaint cnt.isSome) s t := by
  obtain ⟨_, _, _, S₁, _, c₁, _⟩ := W₁
  obtain ⟨_, _, _, S₂, _, c₂, _⟩ := W₂
  have edi : s.gpr .edi = t.gpr .edi :=
    BitVec.eq_of_toNat_eq (S₁.ctx.scr.edi_toNat.trans S₂.ctx.scr.edi_toNat.symm)
  cases cnt with
  | none => exact agree_regs (rs := [.edi]) fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact edi
  | some c =>
    refine agree_regs (rs := [.edi, .esi]) fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact edi
    · rw [c₁ c rfl, c₂ c rfl]

/-- A piece the taint analysis checks, which keeps what `F` says of a run. -/
theorem wk_taint {cnt : Option Nat} {bs : List Nat} {c : Prog isa} {F : State → Prop}
    {hc : VG.Taint.Hint VG.X86.Taint.T}
    (hT : (VG.Taint.check taint (workspaceTaint cnt.isSome) c hc).isSome = true)
    (hw : ∀ u, Wk n base sp cnt bs u → WP isa c u F) : RelCT isa (Both (Wk n base sp cnt bs)) c (Both F) :=
  relCT_both (RelCT.taint _ (fun _ _ h => Wk.agree h.1 h.2) hT) hw

/-- `wk_taint` for a run that also meets `X`. -/
theorem wk_taintX {cnt : Option Nat} {bs : List Nat} {c : Prog isa} {X F : State → Prop}
    {hc : VG.Taint.Hint VG.X86.Taint.T}
    (hT : (VG.Taint.check taint (workspaceTaint cnt.isSome) c hc).isSome = true)
    (hw : ∀ u, Wk n base sp cnt bs u → X u → WP isa c u F) :
    RelCT isa (Both fun u => Wk n base sp cnt bs u ∧ X u) c (Both F) :=
  relCT_both (RelCT.taint _ (fun _ _ h => Wk.agree h.1.1 h.2.1) hT) fun u h => hw u h.1 h.2

theorem wk_mul {cnt : Option Nat} {bs bs' : List Nat} (hn : 2 ≤ n) {o a b : Nat}
    (ho : 4 ≤ o) (ho7 : o ≤ 7) (ha : 4 ≤ a) (ha7 : a ≤ 7) (hb4 : 4 ≤ b) (hb7 : b ≤ 7) (hb : b ∈ bs)
    (hbs : ∀ x ∈ bs, 4 ≤ x ∧ x < 9) (hbs' : ∀ x ∈ bs', x = o ∨ (x ∈ bs ∧ x ≠ o)) :
    RelCT isa (Both (Wk n base sp cnt bs)) (VG.Impl.Dsa.X86.Pow.mul n o a b) (Both (Wk n base sp cnt bs')) := by
  refine relCT_both ((mul_relCT (base := base) sp hn ho ho7 ha ha7 hb4 hb7).mono (fun _ _ h => ⟨?_, ?_⟩) fun _ _ h => h) ?_
  · obtain ⟨size, m, s₀, S, e, _, B⟩ := h.1
    exact ⟨size, m, S.ctx, e ▸ S.room, S.esp.trans e, B b hb⟩
  · obtain ⟨size, m, s₀, S, e, _, B⟩ := h.2
    exact ⟨size, m, S.ctx, e ▸ S.room, S.esp.trans e, B b hb⟩
  intro u ⟨size, m, s₀, S, e, c, B⟩
  refine WP.mono (mulSt_ok S hn ho ho7 ha ha7 hb4 hb7 (B b hb)) fun v ⟨Sv, iv, L, _, V, _⟩ =>
    ⟨size, m, s₀, Sv, e, fun c' h => by rw [iv]; exact c c' h, fun x hx => ?_⟩
  rcases hbs' x hx with rfl | ⟨hx', hxo⟩
  · exact L
  · have := hbs x hx'
    rw [wordsVal_eq_val32, V x this.1 this.2 hxo _ (Nat.le_refl _), ← wordsVal_eq_val32]
    exact B x hx'

theorem wk_one {cnt : Option Nat} {bs : List Nat} {i : Nat} (hi1 : 1 ≤ i) (hi : i < 9)
    (hbs : ∀ x ∈ bs, x < 9 ∧ x ≠ i) :
    RelCT isa (Both (Wk n base sp cnt bs)) (one n (slot n i)) (Both (Wk n base sp cnt (i :: bs))) :=
  wk_taint (hc := oneHint cnt.isSome) (by rw [one_check]; rfl) fun u ⟨size, m, s₀, S, e, c, B⟩ =>
    WP.mono (oneSt_ok S hi1 hi) fun v ⟨Sv, iv, O, V⟩ =>
      ⟨size, m, s₀, Sv, e, fun c' h => by rw [iv]; exact c c' h, fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · rw [O]; exact S.ctx.gt_one
        · have := hbs x hx
          rw [wordsVal_eq_val32, V x this.1 this.2 _ (Nat.le_refl _), ← wordsVal_eq_val32]
          exact B x hx⟩

/-- `k` squarings of slot 4. -/
theorem wk_squarings (hn : 2 ≤ n) :
    ∀ k, RelCT isa (Both (Wk n base sp none [4])) (squarings n k) (Both (Wk n base sp none [4]))
  | 0 => RelCT.nil fun _ _ h => h
  | k + 1 => VG.RelCT.seq (wk_squarings hn k)
      (wk_mul hn (o := 4) (a := 4) (b := 4) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (List.mem_singleton_self _) (fun x hx => by rw [List.mem_singleton.mp hx]; decide)
        (fun x hx => .inl (List.mem_singleton.mp hx)))

/-- What the core needs of a run on entry. -/
def CoreIn (n : Nat) (base : Addr) (sp : BitVec 32) (u : State) : Prop :=
  ∃ size m, Scr u base size ∧ CallRoom sp base size ∧ u.gpr .esp = sp ∧ contextBytes n ≤ size ∧
    VG.Proof.Mont.wordsVal u.mem base (slot n 0) n = m ∧ 1 < m ∧ m % 2 = 1

theorem setupRanges_core (n : Nat) :
    ∀ r ∈ setupRanges n, ∃ c ∈ coreRanges n, c.1 ≤ r.1 ∧ r.1 + r.2 ≤ c.1 + c.2 := by
  have b8 := slot_bound (n := n) (i := 8) (by decide)
  simp only [stride] at b8
  intro r hr
  simp only [setupRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨(0, 8), List.mem_cons_self .., by decide, by decide⟩
  all_goals exact in_core (by decide) (by simp only [contextBytes, slot_lin] at b8 ⊢; omega_arith)

theorem contextSeed_check (n bits : Nat) :
    VG.Taint.check taint (workspaceTaint false) (contextSeed n bits) contextSetupHint = some counterEndTaint :=
  exponent_check_seq taint
    (exponent_check_seq taint (setupInverse_taint false (slot n 0) 0) (by rfl)
      (one_check false n (slot n 3))) (by rfl)
    (powerTwo_check (contextMod n) (slot n 2) (slot n 4) bits)

theorem wk_seed (hn : 2 ≤ n) (hn48 : n ≤ 48) :
    RelCT isa (Both (CoreIn n base sp)) (contextSeed n (65 * n)) (Both (Wk n base sp none [4])) := by
  refine relCT_both (RelCT.taint (A := taint) (hc := contextSetupHint) (workspaceTaint false) (fun s t h => ?_)
    (by rw [contextSeed_check]; rfl)) ?_
  · obtain ⟨_, _, h₁, -⟩ := h.1
    obtain ⟨_, _, h₂, -⟩ := h.2
    exact agree_regs (rs := [.edi]) fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact BitVec.eq_of_toNat_eq (h₁.edi_toNat.trans h₂.edi_toNat.symm)
  · intro u ⟨size, m, hs, R, e, hz, hv, hm1, hodd⟩
    refine WP.mono (contextSeed_ok (bits := 65 * n) hs (by omega_arith) (by omega_arith) (by omega_arith) hz hv hm1 hodd)
      fun v ⟨Cv, _, Xv, Ov, Kv⟩ => ?_
    rw [← e] at R
    refine ⟨size, m, u, ⟨Cv, R, Kv, (OutsS.of_outs Ov).core (setupRanges_core n)⟩, e, ?_, fun b hb => ?_⟩
    · intro c h; cases h
    · rw [List.mem_singleton.mp hb, Xv]
      exact Nat.mod_lt _ (by omega_arith)

theorem wk_encode (hn : 2 ≤ n) :
    RelCT isa (Both (Wk n base sp none [4])) (encode n) (Both (Wk n base sp none [5])) := by
  unfold encode
  refine VG.RelCT.seq (wk_one (bs := [4]) (i := 7) (by decide) (by decide)
    (fun x hx => by rw [List.mem_singleton.mp hx]; decide)) ?_
  refine VG.RelCT.seq (wk_mul (bs' := [4]) hn (o := 6) (a := 4) (b := 7) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp)) ?_
  exact wk_mul hn (o := 5) (a := 5) (b := 4) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by simp) (by simp) (by simp)

theorem wk_start (e : Nat) :
    RelCT isa (Both (Wk n base sp none [5])) (.block [.mov .esi (.imm (BitVec.ofNat 32 (32 * e)))])
      (Both (Wk n base sp (some (32 * e)) [5])) :=
  wk_taint (hc := .block []) rfl fun u W => wp_movS rfl fun v U _ => WP.block_nil (by
    obtain ⟨size, m, s₀, S, e', _, B⟩ := W
    have K : Keeps powerClob u v := U.keeps.mono (by decide)
    refine ⟨size, m, s₀, ⟨⟨S.ctx.scr.of_keeps K (by decide), S.ctx.size_le, U.mem ▸ S.ctx.modulus, S.ctx.gt_one,
      U.mem ▸ S.ctx.inverse⟩, S.room, S.keeps.trans K, U.mem ▸ S.mem⟩, e', fun c h => ?_, fun b hb => ?_⟩
    · cases h; exact U.gpr
    · rw [U.mem]; exact B b hb)

/-- The header's mask word is a mask. -/
def MaskOk (base : Addr) (u : State) : Prop :=
  ∃ bit : Bool, u.mem.readW (off base 4) 32 = if bit then BitVec.allOnes 32 else 0

theorem wk_mulMask {cnt : Option Nat} (hn : 2 ≤ n) :
    RelCT isa (Both fun u => Wk n base sp cnt [5] u ∧ MaskOk base u) (VG.Impl.Dsa.X86.Pow.mul n 7 6 5)
      (Both fun u => Wk n base sp cnt [5] u ∧ MaskOk base u) := by
  refine relCT_both ((mul_relCT (base := base) sp hn (o := 7) (a := 6) (b := 5) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)).mono (fun _ _ h => ⟨?_, ?_⟩) fun _ _ h => h) ?_
  · obtain ⟨⟨size, m, s₀, S, e, _, B⟩, _⟩ := h.1
    exact ⟨size, m, S.ctx, e ▸ S.room, S.esp.trans e, B 5 (by simp)⟩
  · obtain ⟨⟨size, m, s₀, S, e, _, B⟩, _⟩ := h.2
    exact ⟨size, m, S.ctx, e ▸ S.room, S.esp.trans e, B 5 (by simp)⟩
  intro u ⟨⟨size, m, s₀, S, e, c, B⟩, bit, hm⟩
  refine WP.mono (mulSt_ok S hn (o := 7) (a := 6) (b := 5) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (B 5 (by simp))) fun v ⟨Sv, iv, _, _, V, M⟩ =>
    ⟨⟨size, m, s₀, Sv, e, fun c' h => by rw [iv]; exact c c' h, fun x hx => ?_⟩, bit, by rw [M, hm]⟩
  rw [List.mem_singleton.mp hx, wordsVal_eq_val32, V 5 (by decide) (by decide) (by decide) _ (Nat.le_refl _),
    ← wordsVal_eq_val32]
  exact B 5 (by simp)

theorem wk_step {e j : Nat} (hn : 2 ≤ n) (he : 2 ≤ e) (hen : e ≤ 2 * n) (hj : 0 < j) (hj32 : j < 2 ^ 32) :
    RelCT isa (Both (Wk n base sp (some j) [5])) (step n e)
      (Both fun u => Wk n base sp (some (j - 1)) [5] u ∧ u.zf = some (decide (j = 1))) := by
  have keep5 : ∀ {u v : State} {size m : Nat} {s₀ : State}, St n m size base s₀ v →
      v.gpr .esi = u.gpr .esi → (∀ k ≤ 2 * n, val32 v.mem base (slot n 5) k = val32 u.mem base (slot n 5) k) →
      Wk n base sp (some j) [5] u → (∀ b ∈ [5], VG.Proof.Mont.wordsVal u.mem base (slot n b) n < m) →
      s₀.gpr .esp = sp → (∀ c, some j = some c → u.gpr .esi = BitVec.ofNat 32 c) →
      Wk n base sp (some j) [5] v := by
    intro u v size m s₀ Sv iv V _ B e c
    refine ⟨size, m, s₀, Sv, e, fun c' h => by rw [iv]; exact c c' h, fun x hx => ?_⟩
    rw [List.mem_singleton.mp hx, wordsVal_eq_val32, V _ (Nat.le_refl _), ← wordsVal_eq_val32]
    exact B 5 (by simp)
  unfold step
  refine VG.RelCT.seq (wk_taint (hc := .block []) (F := fun u => Wk n base sp (some j) [5] u ∧ MaskOk base u)
    ((congrArg Option.isSome (exponentMask_taint (slot n 8) 4)).trans rfl)
    fun u W => ?_) ?_
  · obtain ⟨size, m, s₀, S, e', c, B⟩ := W
    exact WP.mono (maskSt_ok S) fun v ⟨Sv, iv, M, V⟩ =>
      ⟨keep5 Sv iv (V 5 (by decide)) ⟨size, m, s₀, S, e', c, B⟩ B e' c,
        decide (w32 u.mem base (slot n 8) % 2 = 1), by rw [M]; simp only [decide_eq_true_eq]⟩
  refine VG.RelCT.seq (wk_mulMask hn) ?_
  refine VG.RelCT.seq (wk_taintX (cnt := some j) (hc := selectHint) (F := Wk n base sp (some j) [5])
    ((congrArg Option.isSome (selectProduct_check (contextMod n) (slot n 6) (slot n 7) 4)).trans rfl)
    fun u W ⟨bit, M⟩ => ?_) ?_
  · obtain ⟨size, m, s₀, S, e', c, B⟩ := W
    exact WP.mono (selectSt_ok S M) fun v ⟨Sv, iv, _, V⟩ =>
      keep5 Sv iv (V 5 (by decide) (by decide)) ⟨size, m, s₀, S, e', c, B⟩ B e' c
  refine VG.RelCT.seq (wk_mul (bs' := [5]) hn (o := 5) (a := 5) (b := 5) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp)) ?_
  refine VG.RelCT.seq (wk_taint (cnt := some j) (hc := shiftDownHint) (F := Wk n base sp (some j) [5])
    ((congrArg Option.isSome (shiftDown_check e (slot n 8))).trans rfl) fun u W => ?_) ?_
  · obtain ⟨size, m, s₀, S, e', c, B⟩ := W
    exact WP.mono (shiftSt_ok S he hen) fun v ⟨Sv, iv, _, V⟩ =>
      keep5 Sv iv (V 5 (by decide) (by decide)) ⟨size, m, s₀, S, e', c, B⟩ B e' c
  refine wk_taint (cnt := some j) (hc := .block [])
    (show (VG.Taint.check taint (workspaceTaint true) _ _).isSome = true from rfl) fun u W => ?_
  obtain ⟨size, m, s₀, S, e', c, B⟩ := W
  have hc := c j rfl
  refine wp_subS rfl fun v uv _ => ?_
  refine wp_cmpS rfl fun w fw zw => WP.block_nil ?_
  have mw : w.mem = u.mem := fw.mem.trans uv.mem
  have kw : Keeps powerClob u w := (uv.keeps.mono (by decide)).trans (fw.keeps _)
  refine ⟨⟨size, m, s₀, ⟨⟨S.ctx.scr.of_keeps kw (by decide), S.ctx.size_le, mw ▸ S.ctx.modulus, S.ctx.gt_one,
    mw ▸ S.ctx.inverse⟩, S.room, S.keeps.trans kw, mw ▸ S.mem⟩, e', fun c' h => ?_, fun b hb => ?_⟩, ?_⟩
  · cases h; rw [fw.gpr, uv.gpr, hc, counter_sub hj32 hj]
  · rw [mw]; exact B b hb
  · rw [zw, uv.gpr, hc, counter_sub hj32 hj, counter_zero hj32 hj]

theorem wk_loop {e : Nat} (hn : 2 ≤ n) (he : 2 ≤ e) (hen : e ≤ 2 * n) (j : Nat) :
    RelCT isa (fun s t => 0 < j ∧ j < 2 ^ 32 ∧ Both (Wk n base sp (some j) [5]) s t) (.loop (step n e) .ne)
      (Both (Wk n base sp (some 0) [5])) := by
  refine VG.RelCT.loop (M := isa) (I := fun j s t => 0 < j ∧ j < 2 ^ 32 ∧ Both (Wk n base sp (some j) [5]) s t)
    (fun j => ?_) j
  by_cases hj : 0 < j ∧ j < 2 ^ 32
  · refine (wk_step hn he hen hj.1 hj.2).mono (fun _ _ h => h.2.2) ?_
    rintro s t ⟨⟨W₁, z₁⟩, ⟨W₂, z₂⟩⟩
    have e₁ : isa.eval .ne s = some (!decide (j = 1)) := by show s.zf.map (!·) = _; rw [z₁]; rfl
    have e₂ : isa.eval .ne t = some (!decide (j = 1)) := by show t.zf.map (!·) = _; rw [z₂]; rfl
    refine ⟨e₁.trans e₂.symm, fun h => ?_, fun h => ?_⟩
    · rw [e₁] at h
      have d : j = 1 := by simpa using h
      rw [d] at W₁ W₂
      exact ⟨W₁, W₂⟩
    · rw [e₁] at h
      have : j ≠ 1 := by simpa using h
      exact ⟨j - 1, by omega_arith, by omega_arith, by omega_arith, W₁, W₂⟩
  · exact VG.RelCT.of_false fun _ _ h => hj ⟨h.1, h.2.1⟩

theorem wk_finish {cnt : Option Nat} (hn : 2 ≤ n) :
    RelCT isa (Both (Wk n base sp cnt [])) (finish n) (fun _ _ => True) := by
  unfold finish
  refine VG.RelCT.seq (wk_one (bs := []) (i := 7) (by decide) (by decide) (by simp)) ?_
  refine (mul_relCT (base := base) sp hn (o := 6) (a := 6) (b := 7) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).mono (fun _ _ h => ⟨?_, ?_⟩) fun _ _ h => h
  · obtain ⟨size, m, s₀, S, e, _, B⟩ := h.1
    exact ⟨size, m, S.ctx, e ▸ S.room, S.esp.trans e, B 7 (by simp)⟩
  · obtain ⟨size, m, s₀, S, e, _, B⟩ := h.2
    exact ⟨size, m, S.ctx, e ▸ S.room, S.esp.trans e, B 7 (by simp)⟩

theorem core_relCT {e : Nat} (hn : 2 ≤ n) (hn48 : n ≤ 48) (he : 1 < e) (hen : e ≤ 2 * n) :
    RelCT isa (Both (CoreIn n base sp)) (core n e) (fun _ _ => True) := by
  unfold core setup
  refine VG.RelCT.seq (VG.RelCT.seq (wk_seed hn hn48) (wk_squarings hn 6)) ?_
  refine VG.RelCT.seq (wk_encode hn) ?_
  refine VG.RelCT.seq (wk_start e) ?_
  refine VG.RelCT.seq ((wk_loop hn he hen (32 * e)).mono (fun _ _ h => ⟨by omega_arith, by omega_arith, h⟩) fun _ _ h => h) ?_
  refine (wk_finish (base := base) (sp := sp) (cnt := some 0) hn).mono (fun _ _ h => ⟨?_, ?_⟩) fun _ _ h => h
  · obtain ⟨size, m, s₀, S, e', c, _⟩ := h.1
    exact ⟨size, m, s₀, S, e', c, fun _ h => nomatch h⟩
  · obtain ⟨size, m, s₀, S, e', c, _⟩ := h.2
    exact ⟨size, m, s₀, S, e', c, fun _ h => nomatch h⟩

end

end VG.Proof.Dsa.X86.Pow

end

end


/-! # Constant-time traces of the shared IA-32 exponentiation body

Two runs from the same stack pointer and working space, each ready for the
body (`BodyIn`), leak the same trace: the saves read the argument and store
through public pointers, the core's traces agree (`core_relCT`), and it
leaves `edi` as it found it, through which the restores read. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Pow
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic VG.Impl.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Pow

/-- What the body needs of a run on entry: the working space at its first argument, the 96 bytes
of stack below `esp` apart from it, and the modulus odd and above 1. -/
def BodyIn (n : Nat) (s : State) : Prop :=
  ∃ size, Entry s ((arg s 0).setWidth 64) size ∧ CallRoom (s.gpr .esp) ((arg s 0).setWidth 64) size ∧
    contextBytes n ≤ size ∧ 1 < wordsVal s.mem ((arg s 0).setWidth 64) (slot n 0) n ∧
    wordsVal s.mem ((arg s 0).setWidth 64) (slot n 0) n % 2 = 1

theorem edi_of_scr {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) :
    s.gpr .edi = BitVec.ofNat 32 base.toNat := by
  apply BitVec.eq_of_toNat_eq
  have := hs.edi_toNat
  have := (s.gpr .edi).isLt
  rw [hs.edi_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]

theorem body_relCT (n e : Nat) (hn : 2 ≤ n) (hn48 : n ≤ 48) (he : 1 < e) (hen : e ≤ 2 * n) :
    RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧
      readSrc s (.mem (VG.Impl.Mont.X86.at_ .esp 4)) = some (arg s 0) ∧
      readSrc t (.mem (VG.Impl.Mont.X86.at_ .esp 4)) = some (arg t 0) ∧ BodyIn n s ∧ BodyIn n t)
      (body n e) (fun _ _ => True) := by
  unfold body
  have saveCT : RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧
      readSrc s (.mem (VG.Impl.Mont.X86.at_ .esp 4)) = some (arg s 0) ∧
      readSrc t (.mem (VG.Impl.Mont.X86.at_ .esp 4)) = some (arg t 0))
      (.block save) (VG.X86.Taint.Agree (workspaceTaint false)) := by
    unfold save
    rw [List.append_assoc]
    exact RelCT.block_append (RelCT.seq (scratchArgument_relCT 0)
      (checkedProgramChange (σ := workspaceTaint false) (hint := .block []) rfl rfl))
  have saved := (saveCT.mono (P' := fun (s t : State) => s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧
      readSrc s (.mem (VG.Impl.Mont.X86.at_ .esp 4)) = some (arg s 0) ∧
      readSrc t (.mem (VG.Impl.Mont.X86.at_ .esp 4)) = some (arg t 0) ∧ BodyIn n s ∧ BodyIn n t)
      (fun _ _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩) fun _ _ h => h).wpDep
    (F := fun (σ u : State) => CoreIn n ((arg σ 0).setWidth 64) (σ.gpr .esp) u ∧
      (∀ r ∈ calleeSaved, r ≠ .edi → u.gpr r = σ.gpr r))
    fun s t ⟨_, _, _, _, B₁, B₂⟩ => by
      have go : ∀ σ, BodyIn n σ → WP isa (.block save) σ fun u =>
          CoreIn n ((arg σ 0).setWidth 64) (σ.gpr .esp) u ∧ (∀ r ∈ calleeSaved, r ≠ .edi → u.gpr r = σ.gpr r) := by
        intro σ ⟨size, E, R, hz, hm1, hodd⟩
        have hz24 : 24 ≤ size := by simp only [contextBytes, slot, stride] at hz; omega_using [hz]
        refine WP.mono (save_ok E hz24) fun u ⟨Su, _, Ou, Ku⟩ => ?_
        have hv : wordsVal u.mem ((arg σ 0).setWidth 64) (slot n 0) n =
            wordsVal σ.mem ((arg σ 0).setWidth 64) (slot n 0) n := by
          rw [wordsVal_eq_val32, wordsVal_eq_val32]
          exact Ou.val32 (by simp only [slot]; omega_using []) (by have := E.nowrap; simp only [slot, stride] at hz ⊢; omega_using [hn48])
        exact ⟨⟨size, _, Su, R, Ku.1 _ (by decide), hz, hv, hm1, hodd⟩,
          fun r hr hne => Ku.1 r (by revert hr hne; cases r <;> simp [calleeSaved])⟩
      exact ⟨go s B₁, go t B₂⟩
  refine VG.RelCT.seq (R := fun u v => ∃ p : Addr × BitVec 32, Both (CoreIn n p.1 p.2) u v)
    (saved.mono (fun _ _ h => h) fun u v ⟨_, σ₁, σ₂, ⟨SP, A0, _⟩, ⟨C₁, _⟩, ⟨C₂, _⟩⟩ =>
      ⟨((arg σ₁ 0).setWidth 64, σ₁.gpr .esp), C₁, by rw [A0, SP]; exact C₂⟩) ?_
  refine VG.RelCT.seq (R := VG.X86.Taint.Agree (workspaceTaint false)) ?_
    ((checkedProgramChange (σ := { regs := .ofList [], flags := false }) (hint := .block []) (by rfl) rfl).mono
      (fun _ _ h => h) (fun _ _ _ => trivial))
  refine VG.RelCT.exists_ fun p => ?_
  have go : ∀ u, CoreIn n p.1 p.2 u → WP isa (core n e) u fun w => w.gpr .edi = BitVec.ofNat 32 p.1.toNat := by
    intro u ⟨size, m, hs, R, esp, hz, hv, hm1, hodd⟩
    rw [← esp] at R
    exact WP.mono (core_ok hs R hz hn hn48 he hen hv hm1 hodd) fun w ⟨_, _, K⟩ => by
      rw [K.1 _ (by decide)]; exact edi_of_scr hs
  refine ((core_relCT (base := p.1) (sp := p.2) hn hn48 he hen).wp (F₁ := fun (w : State) => w.gpr .edi = BitVec.ofNat 32 p.1.toNat)
    (F₂ := fun (w : State) => w.gpr .edi = BitVec.ofNat 32 p.1.toNat) fun u v h => ⟨go u h.1, go v h.2⟩).mono
    (fun _ _ h => h) fun w₁ w₂ ⟨_, e₁, e₂⟩ => agree_regs (rs := [.edi]) fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      rw [e₁, e₂]

end VG.Proof.Dsa.X86.Pow

end

end

/-! # Correctness and secrecy of callable IA-32 exponentiation -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Pow
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Pow

theorem scratch_fits {n size : Nat} (h : contextBytes n ≤ size) :
    ∀ r ∈ scratch n, r.1 + r.2 ≤ size := by
  intro r hr
  simp only [scratch, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp only [contextBytes, slot, stride] at * <;> omega_using [h]

end VG.Proof.Dsa.X86.Pow
