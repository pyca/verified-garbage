import VerifiedGarbage.Proof.X25519.X86.Base.Main
import VerifiedGarbage.Proof.X25519.X86.Base.Lit
import VerifiedGarbage.Proof.Ed25519.X86.CombCT
import VerifiedGarbage.Proof.Ed25519.X86.PointCTBlocks
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Inline

/-!
# X25519 of the base point on x86: constant time, and the shared contract

Every piece's trace depends only on the pointers: the expansion and clamping
of the scalar store to fixed offsets of the workspace, the comb and the
inversion use only the workspace pointer (`combMultiply_ct`, the summaries of
`PointCTBlocks.lean`), and the output reloads its pointer from the stack.
-/

namespace VG.Proof.X25519.X86.Base

open VG VG.X86 VG.Impl.Ed25519.X86 VG.Impl.X25519.X86.Base
open VG.Proof.Ed25519.X86

theorem uEncode_ct : RelCT isa (fun s t => s.gpr .edi = t.gpr .edi) uEncode (fun _ _ => True) := by
  obtain ⟨_, hc⟩ : ∃ h, (taint.check (regsTaint [.edi]) uEncode h).isSome = true := by
    taint_decide_sum [power250Sum, sqT1]
  apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ hc
  intro s t h
  exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸ h)

theorem start_ct : RelCT isa
    (fun s t => x25519BaseLocal.pre s ∧ x25519BaseLocal.pre t ∧ x25519BaseLocal.pub s t)
    (.block x25519BaseStart) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (scalarTaint 2 3) _ (by taint_decide)
  intro s t ⟨hs, ht, hp⟩
  obtain ⟨sp, a0, a1, a2⟩ := hp
  obtain ⟨ps, _, os⟩ := scalarBase_pre hs
  obtain ⟨pt, _, ot⟩ := scalarBase_pre ht
  refine scalarTaint_agree (scalarTaint_wf ps os hs.2.1 hs.2.2.2.2.1)
    (scalarTaint_wf pt ot ht.2.1 ht.2.2.2.2.1) sp ?_ (by decide) hs.2.1 ht.2.1 ps.sp_fit pt.sp_fit
  intro i hi
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  exacts [a0, a1, a2]

theorem finish_ct (s₀ t₀ : State) (hs : x25519BaseLocal.pre s₀) (ht : x25519BaseLocal.pre t₀)
    (hp : x25519BaseLocal.pub s₀ t₀) :
    RelCT isa (BaseSaved s₀ t₀) (.block (finishWords 64)) (fun _ _ => True) := by
  obtain ⟨ps, _, _⟩ := scalarBase_pre hs
  obtain ⟨pt, _, _⟩ := scalarBase_pre ht
  have loadct : RelCT isa (BaseSaved s₀ t₀)
      (.block [.mov .esi (.mem (Impl.X25519.X86.at_ .esp 4))]) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.esp]) _ (by taint_decide)
    intro s t h
    exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸
      (h.1.esp.trans (hp.1.trans h.2.esp.symm)))
  have hh := ctWithRuns loadct (fun _ _ h => ⟨loadArg_ok (i := 0) ps h.1 (by decide),
    loadArg_ok (i := 0) pt h.2 (by decide)⟩)
  have tailct : RelCT isa (fun s t => s.gpr .edi = t.gpr .edi ∧ s.gpr .esi = t.gpr .esi)
      (.block (outputWords 64 8 ++ Impl.X25519.X86.restore)) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi, .esi]) _ (by taint_decide)
    intro s t h
    apply regsTaint_agree
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h.1, h.2]
  simp only [finishWords, List.append_assoc]
  refine ctBlockAppend (hh.mono (fun _ _ h => h) ?_) tailct
  intro s t ⟨_, a, b, _, ha, hb⟩
  exact ⟨ha.1.edi.trans (hp.2.2.2.trans hb.1.edi.symm), ha.2.1.trans (hp.2.1.trans hb.2.1.symm)⟩

theorem tail_ct (s₀ t₀ : State) (hs : x25519BaseLocal.pre s₀) (ht : x25519BaseLocal.pre t₀)
    (hp : x25519BaseLocal.pub s₀ t₀) :
    RelCT isa (fun s t => Ready s₀ s ∧ Ready t₀ t)
      (.seq combMultiply (.seq uEncode (.block (finishWords 64)))) (fun _ _ => True) := by
  have mulct := combMultiply_ct.mono
    (P' := fun (s t : State) => Ready s₀ s ∧ Ready t₀ t)
    (fun _ _ h => h.1.saved.edi.trans (hp.2.2.2.trans h.2.saved.edi.symm)) (fun _ _ h => h)
  have mw (u s : State) (hu : x25519BaseLocal.pre u) (h : Ready u s) :
      WP isa combMultiply s (Saved u (arg u 2)) :=
    WP.mono (comb_ok hu h) fun _ ⟨_, kt⟩ => kt
  have mul := ctWithRuns mulct (fun s t h => ⟨mw s₀ s hs h.1, mw t₀ t ht h.2⟩)
  have encct := uEncode_ct.mono (P' := BaseSaved s₀ t₀)
    (fun _ _ h => h.1.edi.trans (hp.2.2.2.trans h.2.edi.symm)) (fun _ _ h => h)
  have ew (u s : State) (hu : x25519BaseLocal.pre u) (h : Saved u (arg u 2) s) :
      WP isa uEncode s (Saved u (arg u 2)) := by
    have pu := (scalarBase_pre hu).1
    refine WP.mono (uEncode_ok (h.ctx pu.fit pu.wr)) fun t ⟨kt, _⟩ => ?_
    exact h.ikeep pu.fit kt
  have enc := ctWithRuns encct (fun s t h => ⟨ew s₀ s hs h.1, ew t₀ t ht h.2⟩)
  refine VG.RelCT.seq (mul.mono (fun _ _ h => h) (fun _ _ ⟨_, _, _, _, ha, hb⟩ => ⟨ha, hb⟩))
    (VG.RelCT.seq (enc.mono (fun _ _ h => h) (fun _ _ ⟨_, _, _, _, ha, hb⟩ => ⟨ha, hb⟩))
      (finish_ct s₀ t₀ hs ht hp))

theorem x25519Base_ct :
    ConstantTime isa x25519BaseLocal.pre x25519BaseLocal.pub x25519Base := by
  apply VG.RelCT.constantTime (Q := fun _ _ => True)
  have start := ctWithRuns start_ct (fun _ _ h => ⟨start_ok h.1, start_ok h.2.1⟩)
  rw [x25519Base]
  refine VG.RelCT.seq start ?_
  intro s t ts tt s' t' ⟨_, u, v, hp, hu, hv⟩ es et
  exact tail_ct u v hp.1 hp.2.1 hp.2.2 _ _ _ _ _ _ ⟨hu, hv⟩ es et

theorem x25519Base_ok (s : State) (h : x25519BaseLocal.pre s) :
    ∃ tr t, Exec isa x25519Base s tr t ∧ abiPreserved s t ∧ x25519BaseLocal.post s t :=
  x25519Base_correct h

/-- Memory holding the arguments `0x1000, 0x2000, 0x4000` at `0x8004`. -/
def satMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x40 else 0

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 32⟩, ⟨0x8004, 12⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩]

theorem x25519Base_verified :
    Verified X86.target x25519Base (Spec.X25519.x25519BaseContract X86.abi) :=
  Verified.of_correct x25519Base_ok x25519Base_ct (by
    have a0 : arg satState 0 = 0x1000 := by decide
    have a1 : arg satState 1 = 0x2000 := by decide
    have a2 : arg satState 2 = 0x4000 := by decide
    have e : argAddr satState 0 = 0x8004 := by decide
    have esp : satState.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig, x25519BaseLocal,
      scalarBaseLocal, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, e, esp] using satState)

end VG.Proof.X25519.X86.Base
