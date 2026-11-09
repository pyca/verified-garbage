module

public import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseCTSetup
import VerifiedGarbage.Proof.Ed25519.X86.CombCT
import VerifiedGarbage.Proof.Ed25519.X86.CombLoop
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseCTLit
import VerifiedGarbage.Proof.Ed25519.X86.CommonMemory
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseLit
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseCTSetup
meta import VerifiedGarbage.Proof.Ed25519.X86.CombCT
meta import VerifiedGarbage.Proof.Ed25519.X86.CombLoop
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseCTLit
meta import VerifiedGarbage.Proof.Ed25519.X86.CommonMemory
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseLit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Spec.Ed25519.Contract

/-! Merged from `Proof.Ed25519.X86.ScalarBaseCT`. -/

@[expose] public section

section
/-! Merged from `Proof.Ed25519.X86.ScalarBaseCTFinish`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def BaseSaved (s₀ t₀ s t : State) : Prop := Saved s₀ (arg s₀ 2) s ∧ Saved t₀ (arg t₀ 2) t

theorem scalarBaseFinish_ct (s₀ t₀ : State) (hs : BaseRegions s₀) (ht : BaseRegions t₀)
    (hp : scalarBaseLocal.pub s₀ t₀) : RelCT isa (BaseSaved s₀ t₀) (.block (finishWords 96)) (fun _ _ => True) := by
  obtain ⟨ps, _, _⟩ := scalarBase_pre hs
  obtain ⟨pt, _, _⟩ := scalarBase_pre ht
  have loadct : RelCT isa (BaseSaved s₀ t₀)
      (.block [.mov .esi (.mem (Impl.X25519.X86.at_ .esp 4))]) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.esp]) _ (by native_taint_decide)
    intro s t h
    exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸
      (h.1.esp.trans (hp.1.trans h.2.esp.symm)))
  have hh := ctWithRuns loadct (fun _ _ h => ⟨loadArg_ok (i := 0) ps h.1 (by decide),
    loadArg_ok (i := 0) pt h.2 (by decide)⟩)
  have tailct : RelCT isa (fun s t => s.gpr .edi = t.gpr .edi ∧ s.gpr .esi = t.gpr .esi)
      (.block (outputWords 96 8 ++ Impl.X25519.X86.restore)) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi, .esi]) _ (by native_taint_decide)
    intro s t h
    apply regsTaint_agree
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h.1, h.2]
  simp only [finishWords, List.append_assoc]
  refine ctBlockAppend (hh.mono (fun _ _ h => h) ?_) tailct
  intro s t ⟨_, a, b, _, ha, hb⟩
  exact ⟨ha.1.edi.trans (hp.2.2.2.1.trans hb.1.edi.symm), ha.2.1.trans (hp.2.1.trans hb.2.1.symm)⟩

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem scalarBaseTail_ct (s₀ t₀ : State) (hs : BaseRegions s₀) (ht : BaseRegions t₀)
    (hp : scalarBaseLocal.pub s₀ t₀) :
    RelCT isa (fun s t => BaseCTReady s₀ s ∧ BaseCTReady t₀ t)
      (.seq combMultiply (.seq pointEncode (.block (finishWords 96)))) (fun _ _ => True) := by
  have mulct := (combMultiply_ct (x := arg s₀ 2)).mono
    (P' := fun (s t : State) => BaseCTReady s₀ s ∧ BaseCTReady t₀ t)
    (fun s t h => by
      have ht' := h.2.2.1.ctx
      rw [← hp.2.2.2.1] at ht'
      refine ⟨h.1.2.1.ctx, ht', ?_, ?_, ?_⟩
      · rw [h.1.1.wr, h.2.1.wr, hs.2.1, ht.2.1, hp.2.1, hp.2.2.2.1]
      · rw [h.1.1.esp, h.2.1.esp, hp.1]
      · rw [h.1.2.2.1, hp.2.2.2.1, h.2.2.2.1, hp.2.2.2.2]) (fun _ _ h => h)
  have mw (u s : State) (h : BaseCTReady u s) : WP isa combMultiply s (Saved u (arg u 2)) := by
    refine WP.mono (combMultiply_ok (S := baseScalar u) h.2.1.ctx.ctx (by simpa using h.2.1.bound)
      (fun q hq => by rw [h.2.1.bits q (by omega), scalarBit_nat]) h.2.1.d h.2.2.1 h.2.2.2.1 h.2.2.2.2)
      fun t ⟨_, kt⟩ => ?_
    exact h.1.mulkeep h.2.1.ctx.ctx.fit kt
  have mul := ctWithRuns mulct (fun s t h => ⟨mw s₀ s h.1, mw t₀ t h.2⟩)
  have encct := (pointEncode_ct (x := arg s₀ 2)).mono (P' := BaseSaved s₀ t₀)
    (fun _ _ h => by
      have ct := pointCTCtx_saved ht h.2
      rw [← hp.2.2.2.1] at ct
      exact ⟨pointCTCtx_saved hs h.1, ct, by rw [h.1.wr, h.2.wr, hs.2.1, ht.2.1, hp.2.1, hp.2.2.2.1],
        by rw [h.1.esp, h.2.esp, hp.1]⟩) (fun _ _ h => h)
  have ew (u s : State) (hu : BaseRegions u) (h : Saved u (arg u 2) s) :
      WP isa pointEncode s (Saved u (arg u 2)) := by
    have pu := (scalarBase_pre hu).1
    refine WP.mono (pointEncode_ok (h.ctx pu.fit pu.wr pu.stk)) fun t ⟨kt, _⟩ => ?_
    exact h.ikeep pu.fit kt
  have enc := ctWithRuns encct (fun s t h => ⟨ew s₀ s hs h.1, ew t₀ t ht h.2⟩)
  refine VG.RelCT.seq (mul.mono (fun _ _ h => h) (fun _ _ ⟨_, _, _, _, ha, hb⟩ => ⟨ha, hb⟩))
    (VG.RelCT.seq (enc.mono (fun _ _ h => h) (fun _ _ ⟨_, _, _, _, ha, hb⟩ => ⟨ha, hb⟩))
      (scalarBaseFinish_ct s₀ t₀ hs ht hp))

theorem scalarBaseBody_ct : RelCT isa (fun s t => BodyPre s ∧ BodyPre t ∧ scalarBaseLocal.pub s t)
    scalarBaseBody (fun _ _ => True) := by
  have start := ctWithRuns scalarBaseStart_ct
    (fun _ _ h => ⟨scalarBaseStart_ok h.1, scalarBaseStart_ok h.2.1⟩)
  rw [scalarBaseBody]
  refine VG.RelCT.seq start ?_
  intro s t ts tt s' t' ⟨_, u, v, hp, hu, hv⟩ es et
  exact scalarBaseTail_ct u v hp.1.1 hp.2.1.1 hp.2.2 _ _ _ _ _ _ ⟨hu, hv⟩ es et

theorem scalarBase_ct : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBase := by
  apply VG.RelCT.constantTime (Q := fun _ _ => True)
  have pro := ctWithRuns combAddr_ct (fun _ _ h => ⟨combAddr_ok h.1, combAddr_ok h.2.1⟩)
  rw [scalarBase]
  refine VG.RelCT.seq pro ?_
  intro s t ts tt s' t' ⟨_, u, v, ⟨_, _, hp⟩, Pu, Pv⟩ es et
  exact scalarBaseBody_ct _ _ _ _ _ _ ⟨Pu.pre, Pv.pre, Prologue.pub Pu Pv hp⟩ es et

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem scalarBaseBody_correct {s : State} (h : BodyPre s) :
    WP isa scalarBaseBody s fun t => abiPreserved s t ∧ scalarBaseLocal.post s t := by
  obtain ⟨hp, _, ho⟩ := scalarBase_pre h.1
  rw [scalarBaseBody]
  refine WP.seq (WP.mono (scalarBaseStart_ok h) fun c ⟨hc, mc, pc, tc⟩ => ?_)
  refine WP.seq (WP.mono (combMultiply_ok (S := baseScalar s) mc.ctx.ctx (by simpa using mc.bound)
    (fun q hq => by rw [mc.bits q (by omega), scalarBit_nat]) mc.d pc tc.1 tc.2) fun d ⟨pd, kd⟩ => ?_)
  have hd := hc.mulkeep hp.fit kd
  refine WP.seq (WP.mono (pointEncode_value (hd.ctx hp.fit hp.wr hp.stk)) fun e ⟨ke, ve⟩ => ?_)
  have he := hd.ikeep hp.fit ke
  refine WP.mono (finishWords_ok hp ho he (src := 96) (by decide)) fun t ⟨abi_t, et⟩ => ⟨abi_t, ?_⟩
  change Spec.Ed25519.bytesAt t.mem ((arg s 0).setWidth 64) 32 = _
  rw [et, ve, encodePoint_rep pd, Spec.Ed25519.scalarBase,
    encodePoint_rep (pointMul_rep _ basePoint_rep)]
  rfl

theorem scalarBase_correct {s : State} (h : scalarBaseLocal.pre s) :
    WP isa scalarBase s fun t => abiPreserved s t ∧ scalarBaseLocal.post s t := by
  rw [scalarBase]
  refine WP.seq (WP.mono (combAddr_ok h) fun s₁ P => ?_)
  refine WP.mono (scalarBaseBody_correct P.pre) fun t ⟨ha, hq⟩ => ⟨P.abi ha, ?_⟩
  change Spec.Ed25519.bytesAt t.mem ((arg s₁ 0).setWidth 64) 32 =
    Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s₁.mem ((arg s₁ 1).setWidth 64) 32) at hq
  change Spec.Ed25519.bytesAt t.mem ((arg s 0).setWidth 64) 32 =
    Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32)
  rw [P.args 0 (by decide), P.args 1 (by decide), P.input] at hq
  exact hq

theorem scalarBase_ok (s : State) (h : scalarBaseLocal.pre s) :
    ∃ tr t, Exec isa scalarBase s tr t ∧ abiPreserved s t ∧ scalarBaseLocal.post s t :=
  scalarBase_correct h

/-- The `n` bytes below `sp`, as the contract states them. -/
theorem below_eq {sp : BitVec 32} {n : Nat} (h : n ≤ sp.toNat) :
    below sp n = ⟨sp.setWidth 64 - BitVec.ofNat 64 n, n⟩ := by
  simp only [below, Taint.sub_setWidth h]

end VG.Proof.Ed25519.X86
