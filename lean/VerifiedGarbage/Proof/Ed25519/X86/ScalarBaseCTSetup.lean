import VerifiedGarbage.Proof.Ed25519.X86.PointCTMul
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseCTLit
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseMain
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseEntry

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
    WP isa (.block (abiSave 2 ++ inputBits 1 32 ++ fieldCode baseSetupOps)) s (BaseCTReady s) := by
  obtain ⟨hr, hptr, htbl, hts⟩ := h
  obtain ⟨hp, hi, _⟩ := scalarBase_pre hr
  have scalar_bound : baseScalar s < 2 ^ (16 * 16) := by
    have hb := decodeLE_lt (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32)
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] at hb
    change baseScalar s < 256 ^ 32 at hb
    rw [show 2 ^ (16 * 16) = 256 ^ 32 by decide]
    exact hb
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (abiSave_frame hp) fun a ⟨ha, fa⟩ => ?_)
  refine WP.block_append (WP.mono (inputBits_frame hp hi ha (by decide) (by decide))
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
    (.block (abiSave 2 ++ inputBits 1 32 ++ fieldCode baseSetupOps)) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (scalarTaint 2 3) _ (by taint_decide)
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
  apply VG.RelCT.taint (A := taint) (scalarTaint 2 3) _ (by taint_decide)
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
    rw [P.arg ha.1.sp4 (by omega), Q.arg hb.1.sp4 (by omega)]
    obtain ⟨_, a0, a1, a2, _⟩ := hp
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    exacts [a0, a1, a2]

end VG.Proof.Ed25519.X86
