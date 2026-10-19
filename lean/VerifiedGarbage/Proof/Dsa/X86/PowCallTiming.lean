module

public import VerifiedGarbage.Proof.Dsa.X86.PowCall
public import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! # Traces of calls to shared IA-32 exponentiation -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Pow
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Impl.Dsa.X86.Pow

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

theorem framed_relCT (n e : Nat) :
    RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ s.gpr .edi = t.gpr .edi ∧ 12 ≤ (s.gpr .esp).toNat)
      (.frame (.push [.eax, .edi]) (.call (name n e) (body n e)) (.pop .eax 2))
      (fun _ _ => True) := by
  refine RelCT.frame (R := fun _ _ => True) (fun _ _ H => H.1) ?_
  rintro _ _ tr ur sf tf ⟨s, t, ⟨SP, DI, fit⟩, rfl, rfl⟩ E F
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
      have traces := (body_relCT n e) _ _ _ _ _ _ ⟨sp, args, body_readArg E, body_readArg F⟩ E F
      have r := (ret_gpr R .esp).1
      have q := (ret_gpr S .esp).1
      refine ⟨?_, trivial⟩
      simp only [r, q, State.callEntry_esp, pushed_esp, SP, traces.1]

theorem call_relCT (n e : Nat) :
    RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ s.gpr .edi = t.gpr .edi ∧ 12 ≤ (s.gpr .esp).toNat)
      (Impl.Dsa.X86.Pow.call n e) (fun _ _ => True) := by
  unfold Impl.Dsa.X86.Pow.call
  refine RelCT.seq ?_ (framed_relCT n e)
  intro s t tr ur sf tf H E F
  have W (s : State) : WP isa (.block [.mov .eax (.imm (BitVec.ofNat 32 (VG.Impl.Mont.X86.Dynamic.contextBytes n / 8)))]) s
      (fun t => VG.Proof.Mont.X86.Keeps [.eax] s t) :=
    wp_movS rfl fun _ U _ => WP.block_nil U.keeps
  have K := wp_result (W s) E
  have L := wp_result (W t) F
  refine ⟨?_, ?_⟩
  · cases E with
    | block E => cases F with
      | block F =>
        simp only [execBlock, isa, exec, readSrc, Option.map_some, addrs, srcAddrs, List.map_nil,
          List.nil_append, Option.some.injEq, Prod.mk.injEq] at E F
        exact E.2.symm.trans F.2
  · dsimp only
    rw [K.1 .esp (by decide), L.1 .esp (by decide), K.1 .edi (by decide), L.1 .edi (by decide)]
    exact H

end VG.Proof.Dsa.X86.Pow
