module

import VerifiedGarbage.Proof.Ed25519.X86.CombLoop
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseCTLit
import VerifiedGarbage.Proof.Ed25519.X86.CommonMemory
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseLit
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
public import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseEntry
import VerifiedGarbage.Proof.Ed25519.X86.CommonCT
import VerifiedGarbage.Proof.Ed25519.Bytes
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseEntry
meta import VerifiedGarbage.Proof.Ed25519.X86.CommonCT
meta import VerifiedGarbage.Proof.Ed25519.Bytes
public import VerifiedGarbage.Proof.Ed25519.X86.PointCTBlocks
public import VerifiedGarbage.Proof.Ed25519.X86.AccumulateStep
import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ed25519.X86.PointCTBlocks
meta import VerifiedGarbage.Proof.Ed25519.X86.AccumulateStep
meta import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Ed25519.X86.PointBatch
public import VerifiedGarbage.Impl.Ed25519.X86.PointAccumulate
import VerifiedGarbage.Proof.Ed25519.X86.PrepareAdd
import VerifiedGarbage.Proof.Ed25519.X86.PointMultiplyFrame
meta import VerifiedGarbage.Impl.Ed25519.X86.PointBatch
meta import VerifiedGarbage.Impl.Ed25519.X86.PointAccumulate
meta import VerifiedGarbage.Proof.Ed25519.X86.PrepareAdd
meta import VerifiedGarbage.Proof.Ed25519.X86.PointMultiplyFrame
public import VerifiedGarbage.Impl.Ed25519.X86.Comb
import VerifiedGarbage.Proof.Ed25519.X86.CombLit
public import VerifiedGarbage.Proof.Ed25519.X86.PointCTSupport
import VerifiedGarbage.Proof.Ed25519.X86.Point32.AddSum
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Impl.Ed25519.X86.Comb
meta import VerifiedGarbage.Proof.Ed25519.X86.CombLit
meta import VerifiedGarbage.Proof.Ed25519.X86.PointCTSupport
meta import VerifiedGarbage.Proof.Ed25519.X86.Point32.AddSum
meta import VerifiedGarbage.Proof.Framework.TacticTemplate

/-! ### `Ed25519.X86.CombCT`, which this module and modules that import it used -/

section

/-! The comb has a public trace: its loops' counters (`esi`) are public, and every address is
the workspace pointer `edi` plus a constant or `8 esi`, or the tables' address plus
`768 esi` and a constant. The tables' address is the word at byte `combTbl` of the workspace,
which the comb never writes, public (`callTaint combTbl`): the digits only reach masks. The
calls of `vg_ed25519_r32_add_affine` and of `_point_add` are analysed by their summaries, and
those of `_double`, after the loop, as part of the comb. -/

@[expose] public section

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86

theorem combMultiply_ct {x : BitVec 32} : RelCT isa
    (fun s t => PointCTCtx x s ∧ PointCTCtx x t ∧ s.wr = t.wr ∧ s.gpr .esp = t.gpr .esp ∧
      wd s.mem x combTbl = wd t.mem x combTbl) combMultiply (fun _ _ => True) := by
  obtain ⟨_, hc⟩ : ∃ h, (taint.check (callTaint combTbl) combMultiply h).isSome = true := by
    native_taint_decide_sum [affSum, addSum]
  apply VG.RelCT.taint (A := taint) (callTaint combTbl) _ hc
  intro s t ⟨hs, ht, hw, hsp, hv⟩
  exact callTaint_agree hs ht hw hsp (by decide) hv

end VG.Proof.Ed25519.X86

end

end

/-! ### `Ed25519.X86.ScalarBaseCTSetup`, which only this module used -/

section

/-! ### `Ed25519.X86.PointCTMul`, which only this module used -/

section

/-! Merged from `Proof.Ed25519.X86.PointCTBatch`. -/

@[expose] public section

/-! Merged from `Proof.Ed25519.X86.PointCTMulLoop`. -/

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

structure MulCTInput (x : BitVec 32) (scalar count : Nat) (s : State) : Prop where
  ctx : PointCTCtx x s
  bound : scalar < 2 ^ (16 * count)
  bits : ∀ i < 16 * count, s.mem (addr x (7168 + i)) = BitVec.ofNat 8 (scalarBit scalar i).toNat
  d : env s.mem x 16 = Spec.Ed25519.d

end VG.Proof.Ed25519.X86

end

end

@[expose] public section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def baseScalar (s : State) : Nat := Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32)

theorem pointCTCtx_saved {s₀ s : State} (h : BaseRegions s₀) (hs : Saved s₀ (arg s₀ 2) s) :
    PointCTCtx (arg s₀ 2) s := by
  obtain ⟨hp, _, ho⟩ := scalarBase_pre h
  refine ⟨hs.ctx hp.fit hp.wr hp.stk, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs.wr, h.2.1]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
  · rw [hs.wr, h.2.1]
    exact List.pairwise_cons.mpr ⟨by simpa using ho.sep, by simp⟩
  · intro r hr
    rw [hs.wr, h.2.1] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [BitVec.toNat_setWidth]
    · omega_using [ho.fit]
    · omega_using [hp.fit]
  · change s.wr.getD 1 ⟨0, 0⟩ = _
    rw [hs.wr, h.2.1]; rfl
  · intro r hr
    rw [hs.wr, h.2.1] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [callStk, hs.esp]
    rcases hr with rfl | rfl
    · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- After the body's start: the callee-saved registers saved, the scalar's bits, `d`, and the
tables' address and the tables, apart from the stack a call uses. -/
def BaseCTReady (s₀ s : State) : Prop :=
  Saved s₀ (arg s₀ 2) s ∧ MulCTInput (arg s₀ 2) (baseScalar s₀) 16 s ∧
    wd s.mem (arg s₀ 2) combTbl = s₀.syms combSym ∧ TblAt (arg s₀ 2) (s₀.syms combSym) s ∧
    (TBL ((s₀.syms combSym).setWidth 64)).Disjoint (callStk s)

theorem scalarBaseStart_ok {s : State} (h : BodyPre s) :
    WP isa scalarBaseStart s (BaseCTReady s) := by
  obtain ⟨hr, hptr, htbl, hts⟩ := h
  obtain ⟨hp, hi, _⟩ := scalarBase_pre hr
  have scalar_bound : baseScalar s < 2 ^ (16 * 16) := by
    have hb := decodeLE_lt (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32)
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] at hb
    change baseScalar s < 256 ^ 32 at hb
    rw [show 2 ^ (16 * 16) = 256 ^ 32 by decide]
    exact hb
  rw [scalarBaseStart]
  refine WP.seq (WP.mono (abiSave_frame hp) fun a ⟨ha, fa⟩ => ?_)
  refine WP.seq (WP.mono (inputBits_frame hp hi ha (by decide) (by decide) (by decide))
    fun b ⟨hb, fb, bits⟩ => ?_)
  have cb := hb.ctx hp.fit hp.wr hp.stk
  refine WP.mono (fieldCode_ok baseSetupOps cb) fun c ⟨kc, ec⟩ => ?_
  have hc := hb.ikeep hp.fit (IKeep.of_field kc)
  have toScr : ∀ {m m' : Mem} {o n : Nat}, Frame [sub (arg s 2) o n] m m' → o + n ≤ 8192 → o < 8192 →
      Frame [scR 8192 (arg s 2)] m m' := fun f h1 h2 => f.sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_singleton_self _, by rw [scR_eq]; exact sub_sub hp.fit (Nat.zero_le _) h1 h2⟩
  refine ⟨hc, ⟨pointCTCtx_saved hr hc, scalar_bound, ?_, ?_⟩, ?_,
    htbl.of_frame hc.rd (((toScr fa (by decide) (by decide)).trans (toScr fb (by decide) (by decide))).trans
      (toScr kc.frame (by decide) (by decide))) fun r hr => by
        rw [List.mem_singleton.mp hr]; exact fun _ h => h, by rw [callStk, hc.esp]; exact hts⟩
  · intro i ii
    rw [IKeep.bit (IKeep.of_field kc) cb i (by omega_using [ii]), bits i (by omega_using [ii]), scalarBit_nat]
    rfl
  · rw [ec, baseSetup_d]
  · rw [wd_frame1 kc.frame hp.fit (by decide) (by decide) (Or.inr (by decide)),
      wd_frame1 fb hp.fit (by decide) (by decide) (Or.inl (by decide)),
      wd_frame1 fa hp.fit (by decide) (by decide) (Or.inr (by decide))]
    exact hptr


theorem scalarBaseStart_ct : RelCT isa
    (fun s t => BodyPre s ∧ BodyPre t ∧ scalarBaseLocal.pub s t)
    scalarBaseStart (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (scalarTaint 2 3) _ (by native_taint_decide)
  intro s t ⟨hs, ht, hp⟩
  obtain ⟨sp, a0, a1, a2, _⟩ := hp
  obtain ⟨ps, _, os⟩ := scalarBase_pre hs.1
  obtain ⟨pt, _, ot⟩ := scalarBase_pre ht.1
  refine scalarTaint_agree (scalarTaint_wf ps os hs.1.2.1 hs.1.2.2.2.2.1)
    (scalarTaint_wf pt ot ht.1.2.1 ht.1.2.2.2.2.1) sp ?_ (by decide) hs.1.2.1 ht.1.2.1 ps.sp_fit pt.sp_fit
  intro i hi
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  exacts [a0, a1, a2]

/-- The prologue's trace: the frame's word below `esp`, the argument and the store, all at
public addresses. -/
theorem combAddr_ct : RelCT isa
    (fun s t => scalarBaseLocal.pre s ∧ scalarBaseLocal.pre t ∧ scalarBaseLocal.pub s t)
    (combAddr 2) (fun _ _ => True) := by
  unfold combAddr
  have fr : RelCT isa
      (fun s t => scalarBaseLocal.pre s ∧ scalarBaseLocal.pre t ∧ scalarBaseLocal.pub s t)
      (.frame (.symPush .eax combSym) (.block []) (.pop .ecx 1)) (fun _ _ => True) := by
    intro s t tr₁ tr₂ s' t' h e₁ e₂
    exact ⟨by rw [symFrame_trace h.1.1.sp4 e₁, symFrame_trace h.2.1.1.sp4 e₂, h.2.2.1], trivial⟩
  have pre := fr.wpDep (F := fun s t => SymAddrPost combSym s t) (fun s t h =>
    ⟨symFrame_ok combSym s h.1.1.sp4, symFrame_ok combSym t h.2.1.1.sp4⟩)
  refine pre.seq ?_
  apply VG.RelCT.taint (A := taint) (scalarTaint 2 3) _ (by native_taint_decide)
  intro s t ⟨_, a, b, ⟨ha, hb, hp⟩, P, Q⟩
  have hs := ha.1.symAddr P ha.1.sp4
  have ht := hb.1.symAddr Q hb.1.sp4
  obtain ⟨ps, _, os⟩ := scalarBase_pre hs
  obtain ⟨pt, _, ot⟩ := scalarBase_pre ht
  have fa : (a.gpr .esp).toNat + 16 ≤ 2 ^ 32 := ha.1.spfit
  have fb : (b.gpr .esp).toNat + 16 ≤ 2 ^ 32 := hb.1.spfit
  refine scalarTaint_agree (scalarTaint_wf ps os hs.2.1 hs.2.2.2.2.1)
    (scalarTaint_wf pt ot ht.2.1 ht.2.2.2.2.1) ?_ ?_ (by decide) hs.2.1 ht.2.1 ps.sp_fit pt.sp_fit
  · rw [P.gpr .esp (by decide), Q.gpr .esp (by decide), hp.1]
  · intro i hi
    rw [P.arg ha.1.sp4 (by omega_using [fa, hi]), Q.arg hb.1.sp4 (by omega_using [fb, hi])]
    obtain ⟨_, a0, a1, a2, _⟩ := hp
    rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    exacts [a0, a1, a2]

end VG.Proof.Ed25519.X86

end

end

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
      (fun q hq => by rw [h.2.1.bits q (by omega_using [hq]), scalarBit_nat]) h.2.1.d h.2.2.1 h.2.2.2.1 h.2.2.2.2)
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
    (fun q hq => by rw [mc.bits q (by omega_using [hq]), scalarBit_nat]) mc.d pc tc.1 tc.2) fun d ⟨pd, kd⟩ => ?_)
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
