module

import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.DispatchHead
import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.BodyTiming
import VerifiedGarbage.Proof.Mont.X86.Compact.ConstantTime
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import Init.Prelude
public import VerifiedGarbage.Impl.Mont.X86.PreparedSquare
public import VerifiedGarbage.Spec.Rsa.Mont
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.EntryTransport

/-! # Public operand equality selects between two constant-time Montgomery paths -/

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Spec.Rsa.Mont hiding Keeps
open VG.Proof.Dsa.X86

theorem constantTime : ConstantTime isa (mulContract abi 16).pre (mulContract abi 16).pub
    VG.Impl.Mont.X86.PreparedSquare.dispatch := by
  intro s t ls lt u v hs ht pub ES ET
  obtain ⟨sp, args, _⟩ := Compact.publicInputs pub
  have A := Compact.entry_of hs
  have B := Compact.entry_of ht
  have agree : VG.X86.Taint.Agree (argTaint [] 24) s t :=
    agree_argTaint (k := 5) (by intro r hr; cases hr) sp (entry_args_out A) (entry_args_out B) args
  cases ES with
  | seq HS BS =>
    cases ET with
    | seq HT BT =>
      obtain ⟨headTrace, _⟩ := dispatchHead_trace _ _ _ _ _ _ agree HS HT
      obtain ⟨zs, ms, KS⟩ := wp_result (dispatchHead_ok A) HS
      obtain ⟨zt, mt, KT⟩ := wp_result (dispatchHead_ok B) HT
      have ss := KS.1 .esp (by decide)
      have ts := KT.1 .esp (by decide)
      have preS := pre_transport hs ms ss KS.2.1 KS.2.2
      have preT := pre_transport ht mt ts KT.2.1 KT.2.2
      have pub' := pub_transport pub ms ss mt ts
      have decisions : decide (arg s 3 = arg s 4) = decide (arg t 3 = arg t 4) := by
        rw [args 3 (by decide), args 4 (by decide)]
      have zeq := zs.trans ((congrArg some decisions).trans zt.symm)
      cases BS with
      | iteT cs RS =>
        cases BT with
        | iteT ct RT =>
          change VG.X86.eval .e _ = some true at cs
          simp only [VG.X86.eval] at cs
          have same : arg s 3 = arg s 4 := of_decide_eq_true (Option.some.inj (zs.symm.trans cs))
          have same' := same
          rw [← argument_transport ms ss 3, ← argument_transport ms ss 4] at same'
          have trace := (body_trace _ _ _ _ _ _ ⟨Compact.entry_of preS, Compact.entry_of preT, same', pub'⟩ RS RT).1
          rw [headTrace, trace]
        | iteF ct _ =>
          change VG.X86.eval .e _ = some true at cs
          simp only [VG.X86.eval] at cs
          change VG.X86.eval .e _ = some false at ct
          simp only [VG.X86.eval] at ct
          rw [zeq, ct] at cs
          cases cs
      | iteF cs RS =>
        cases BT with
        | iteT ct _ =>
          change VG.X86.eval .e _ = some false at cs
          simp only [VG.X86.eval] at cs
          change VG.X86.eval .e _ = some true at ct
          simp only [VG.X86.eval] at ct
          rw [zeq, ct] at cs
          cases cs
        | iteF ct RT =>
          have trace := Compact.constantTime _ _ _ _ _ _ preS preT pub' RS RT
          rw [headTrace, trace]

end VG.Proof.Mont.X86.PreparedSquare
