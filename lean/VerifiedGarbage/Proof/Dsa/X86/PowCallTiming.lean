module
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Dsa.X86.Pow
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Weierstrass
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.TCB.X86.Target

import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Dsa.X86.PowTiming
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame
import VerifiedGarbage.Proof.Dsa.X86.PowCallFrame
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Traces of calls to shared IA-32 exponentiation -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Pow
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Pow

theorem body_readArg {n e : Nat} {s t : State} {tr : List Leak}
    (E : Exec isa (body n e) s tr t) :
    readSrc s (.mem (at_ .esp 4)) = some (arg s 0) := by
  change s.load32 (argAddr s 0) = some (arg s 0)
  unfold State.load32
  split
  · rfl
  · rename_i h
    cases E with
    | seq E _ =>
      cases E with
      | block H =>
        simp only [save, slots, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
          execBlock, isa, exec, readSrc, State.load32] at H
        simp only [show s.ea (at_ .esp 4) = argAddr s 0 from rfl, h, ↓reduceIte, Option.map_none] at H
        cases H

/-- What a call of the exponentiation needs of a run: the working space at `edi`, the stack its
call uses apart from it, and the modulus odd and above 1. -/
def CallIn (n : Nat) (s : State) : Prop :=
  ∃ base size, Scr s base size ∧ Room (s.gpr .esp) base size ∧ contextBytes n ≤ size ∧
    1 < wordsVal s.mem base (slot n 0) n ∧ wordsVal s.mem base (slot n 0) n % 2 = 1

theorem bodyIn_of {n : Nat} {s : State} (h : CallIn n s) : BodyIn n (pushed [.eax, .edi] s).callEntry := by
  obtain ⟨base, size, hs, ⟨h108, sep⟩, hz, h1, hodd⟩ := h
  have nw := hs.nowrap
  have spBound := (s.gpr .esp).isLt
  have fit : 4 * [Reg.eax, .edi].length + 4 ≤ (s.gpr .esp).toNat := by simp; omega
  have a0 : arg (pushed [.eax, .edi] s).callEntry 0 = s.gpr .edi := callEntry_arg fit (by decide) (by decide)
  have ws : (arg (pushed [.eax, .edi] s).callEntry 0).setWidth 64 = base := by rw [a0]; exact hs.edi
  have tsp : ((pushed [.eax, .edi] s).callEntry.gpr .esp).toNat = (s.gpr .esp).toNat - 12 := by
    rw [callEntry_espNat fit]; rfl
  have tEsp : (pushed [.eax, .edi] s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 12 := by
    rw [callEntry_esp']; rfl
  have fr := callEntry_frame (rs := [.eax, .edi]) fit (by decide)
  rw [show 4 * [Reg.eax, .edi].length + 4 = 12 from rfl] at fr
  have mv : wordsVal (pushed [.eax, .edi] s).callEntry.mem base (slot n 0) n = wordsVal s.mem base (slot n 0) n := by
    rw [wordsVal_eq_val32, wordsVal_eq_val32, frame_val32 ⟨h108, sep⟩ nw fr
      (by simp only [contextBytes, slot, stride] at hz ⊢; omega)]
  unfold BodyIn
  rw [ws, mv]
  refine ⟨size, ⟨?_, ws, ?_, nw, ?_⟩, ⟨by omega, fun x h₁ h₂ => ?_⟩, hz, h1, hodd⟩
  · refine ⟨below (s.gpr .esp) 8, ?_, ?_⟩
    · simp only [State.callEntry_rd, State.callEntry_wr, pushed_rd, pushed_wr]
      exact List.mem_append_right _ (List.mem_cons_self ..)
    · rw [callEntry_argAddr0, show 4 * [Reg.eax, .edi].length = 8 from rfl]
      simpa only [BitVec.add_zero] using Offset.contains_base ((s.gpr .esp - BitVec.ofNat 32 8).setWidth 64)
        (d := 0) (n := 4) (k := 8) (by decide) (by decide)
  · simp only [State.callEntry_wr, pushed_wr]; exact List.mem_cons_of_mem _ hs.wr
  · unfold StkOk; rw [tsp]; constructor <;> omega
  · rw [tEsp] at h₁
    have h₁' := below_inner (sp := s.gpr .esp) (a := 96) (k := 12) (b := 108) (by decide) h108 x h₁
    have := zone_ofs' ⟨h108, sep⟩ nw (k := 108) (by decide) h₁'
    simp only [Region.Contains, ofs] at h₂ this
    omega

theorem framed_relCT (n e : Nat) (hn : 2 ≤ n) (hn48 : n ≤ 48) (he : 1 < e) (hen : e ≤ 2 * n) :
    RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ s.gpr .edi = t.gpr .edi ∧ CallIn n s ∧ CallIn n t)
      (.frame (.push [.eax, .edi]) (.call (name n e) (body n e)) (.pop .eax 2))
      (fun _ _ => True) := by
  refine RelCT.frame (R := fun _ _ => True) (fun _ _ H => H.1) ?_
  rintro _ _ tr ur sf tf ⟨s, t, ⟨SP, DI, C₁, C₂⟩, rfl, rfl⟩ E F
  have fit : 12 ≤ (s.gpr .esp).toNat := by obtain ⟨_, _, _, ⟨h, _⟩, _⟩ := C₁; omega
  cases E with
  | call C E R =>
    cases F with
    | call D F S =>
      rw [call_callEntry, Option.some.injEq] at C D
      subst C D
      have sp : (pushed [Reg.eax, .edi] s).callEntry.gpr .esp =
          (pushed [Reg.eax, .edi] t).callEntry.gpr .esp := by
        rw [callEntry_esp', callEntry_esp', SP]
      have args : arg (pushed [Reg.eax, .edi] s).callEntry 0 =
          arg (pushed [Reg.eax, .edi] t).callEntry 0 := by
        rw [callEntry_arg (rs := [.eax, .edi]) (s := s) fit (by decide) (by decide),
          callEntry_arg (rs := [.eax, .edi]) (s := t) (by rw [← SP]; exact fit) (by decide) (by decide)]
        exact DI
      have traces := (body_relCT n e hn hn48 he hen) _ _ _ _ _ _
        ⟨sp, args, body_readArg E, body_readArg F, bodyIn_of C₁, bodyIn_of C₂⟩ E F
      have r := (ret_gpr R .esp).1
      have q := (ret_gpr S .esp).1
      refine ⟨?_, trivial⟩
      simp only [r, q, State.callEntry_esp, pushed_esp, SP, traces.1]

theorem call_relCT (n e : Nat) (hn : 2 ≤ n) (hn48 : n ≤ 48) (he : 1 < e) (hen : e ≤ 2 * n) :
    RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ s.gpr .edi = t.gpr .edi ∧ CallIn n s ∧ CallIn n t)
      (Impl.Dsa.X86.Pow.call n e) (fun _ _ => True) := by
  unfold Impl.Dsa.X86.Pow.call
  refine RelCT.seq ?_ (framed_relCT n e hn hn48 he hen)
  intro s t tr ur sf tf H E F
  have W (s : State) : WP isa (.block [.mov .eax (.imm (BitVec.ofNat 32 (VG.Impl.Mont.X86.Dynamic.contextBytes n / 8)))]) s
      (fun t => VG.Proof.Mont.X86.Keeps [.eax] s t ∧ t.mem = s.mem) :=
    wp_movS rfl fun _ U _ => WP.block_nil ⟨U.keeps, U.mem⟩
  have K := wp_result (W s) E
  have L := wp_result (W t) F
  have keep : ∀ {u v : State}, VG.Proof.Mont.X86.Keeps [.eax] u v → v.mem = u.mem → CallIn n u → CallIn n v :=
    fun K M ⟨base, size, hs, R, hz, h1, hodd⟩ =>
      ⟨base, size, hs.of_keeps K (by decide), by rw [K.1 _ (by decide)]; exact R, hz, M ▸ h1, M ▸ hodd⟩
  refine ⟨?_, ?_⟩
  · cases E with
    | block E => cases F with
      | block F =>
        simp only [execBlock, isa, exec, readSrc, Option.map_some, addrs, srcAddrs, List.map_nil,
          List.nil_append, Option.some.injEq, Prod.mk.injEq] at E F
        exact E.2.symm.trans F.2
  · dsimp only
    rw [K.1.1 .esp (by decide), L.1.1 .esp (by decide), K.1.1 .edi (by decide), L.1.1 .edi (by decide)]
    exact ⟨H.1, H.2.1, keep K.1 K.2 H.2.2.1, keep L.1 L.2 H.2.2.2⟩

end VG.Proof.Dsa.X86.Pow
