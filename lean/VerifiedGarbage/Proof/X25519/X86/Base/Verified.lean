import VerifiedGarbage.Proof.X25519.X86.Base.Main
import VerifiedGarbage.Proof.X25519.X86.Base.Lit
import VerifiedGarbage.Proof.Ed25519.X86.CombCT
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseCTSetup
import VerifiedGarbage.Proof.Ed25519.X86.PointCTBlocks
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Inline

/-!
# X25519 of the base point on x86: constant time, and the shared contract

Every piece's trace depends only on the pointers: the static's address, its
frame below `esp` and its store to the workspace (`combAddr_ct`), the expansion
and clamping of the scalar store to fixed offsets of the workspace, the comb and
the inversion use only the workspace pointer and the static's address
(`combMultiply_ct`, `uEncode_ct`), and the output
reloads its pointer from the stack.
-/

namespace VG.Proof.X25519.X86.Base

open VG VG.X86 VG.Impl.Ed25519.X86 VG.Impl.X25519.X86.Base
open VG.Proof.Ed25519.X86

theorem uEncode_ct {x : BitVec 32} : RelCT isa (CallCTPre x) uEncode (fun _ _ => True) := by
  obtain ⟨_, hc⟩ : ∃ h, (taint.check callTaint₀ uEncode h).isSome = true := by
    taint_decide_sum [VG.Proof.X25519.X86.pow250Sum]
  exact VG.RelCT.taint (A := taint) callTaint₀ (fun _ _ h => callTaint₀_agree h) hc

theorem start_ct : RelCT isa
    (fun s t => BodyPre s ∧ BodyPre t ∧ x25519BaseLocal.pub s t)
    (.block x25519BaseStart) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (scalarTaint 2 3) _ (by taint_decide)
  intro s t ⟨hs, ht, hp⟩
  obtain ⟨sp, a0, a1, a2, _⟩ := hp
  obtain ⟨ps, _, os⟩ := scalarBase_pre hs.1
  obtain ⟨pt, _, ot⟩ := scalarBase_pre ht.1
  refine scalarTaint_agree (scalarTaint_wf ps os hs.1.2.1 hs.1.2.2.2.2.1)
    (scalarTaint_wf pt ot ht.1.2.1 ht.1.2.2.2.2.1) sp ?_ (by decide) hs.1.2.1 ht.1.2.1 ps.sp_fit
    pt.sp_fit
  intro i hi
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  exacts [a0, a1, a2]

theorem finish_ct (s₀ t₀ : State) (hs : BaseRegions s₀) (ht : BaseRegions t₀)
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
  exact ⟨ha.1.edi.trans (hp.2.2.2.1.trans hb.1.edi.symm), ha.2.1.trans (hp.2.1.trans hb.2.1.symm)⟩

theorem tail_ct (s₀ t₀ : State) (hs : BaseRegions s₀) (ht : BaseRegions t₀)
    (hp : x25519BaseLocal.pub s₀ t₀) :
    RelCT isa (fun s t => Ready s₀ s ∧ Ready t₀ t)
      (.seq combMultiply (.seq uEncode (.block (finishWords 64)))) (fun _ _ => True) := by
  have mulct := (combMultiply_ct (x := arg s₀ 2)).mono
    (P' := fun (s t : State) => Ready s₀ s ∧ Ready t₀ t)
    (fun s t h => by
      have ht' := pointCTCtx_saved ht h.2.saved
      rw [← hp.2.2.2.1] at ht'
      refine ⟨pointCTCtx_saved hs h.1.saved, ht', ?_, ?_, ?_⟩
      · rw [h.1.saved.wr, h.2.saved.wr, hs.2.1, ht.2.1, hp.2.1, hp.2.2.2.1]
      · rw [h.1.saved.esp, h.2.saved.esp, hp.1]
      · rw [h.1.ptr, hp.2.2.2.1, h.2.ptr, hp.2.2.2.2]) (fun _ _ h => h)
  have mw (u s : State) (hu : BaseRegions u) (h : Ready u s) :
      WP isa combMultiply s (Saved u (arg u 2)) :=
    WP.mono (comb_ok hu h) fun _ ⟨_, kt⟩ => kt
  have mul := ctWithRuns mulct (fun s t h => ⟨mw s₀ s hs h.1, mw t₀ t ht h.2⟩)
  have encct := (uEncode_ct (x := arg s₀ 2)).mono (P' := BaseSaved s₀ t₀)
    (fun _ _ h => by
      have ct := pointCTCtx_saved ht h.2
      rw [← hp.2.2.2.1] at ct
      exact ⟨pointCTCtx_saved hs h.1, ct, by rw [h.1.wr, h.2.wr, hs.2.1, ht.2.1, hp.2.1, hp.2.2.2.1],
        by rw [h.1.esp, h.2.esp, hp.1]⟩) (fun _ _ h => h)
  have ew (u s : State) (hu : BaseRegions u) (h : Saved u (arg u 2) s) :
      WP isa uEncode s (Saved u (arg u 2)) := by
    have pu := (scalarBase_pre hu).1
    refine WP.mono (uEncode_ok (h.ctx pu.fit pu.wr pu.stk)) fun t ⟨kt, _⟩ => ?_
    exact h.ikeep pu.fit kt
  have enc := ctWithRuns encct (fun s t h => ⟨ew s₀ s hs h.1, ew t₀ t ht h.2⟩)
  refine VG.RelCT.seq (mul.mono (fun _ _ h => h) (fun _ _ ⟨_, _, _, _, ha, hb⟩ => ⟨ha, hb⟩))
    (VG.RelCT.seq (enc.mono (fun _ _ h => h) (fun _ _ ⟨_, _, _, _, ha, hb⟩ => ⟨ha, hb⟩))
      (finish_ct s₀ t₀ hs ht hp))

theorem x25519BaseBody_ct : RelCT isa
    (fun s t => BodyPre s ∧ BodyPre t ∧ x25519BaseLocal.pub s t) x25519BaseBody (fun _ _ => True) := by
  have start := ctWithRuns start_ct (fun _ _ h => ⟨start_ok h.1, start_ok h.2.1⟩)
  rw [x25519BaseBody]
  refine VG.RelCT.seq start ?_
  intro s t ts tt s' t' ⟨_, u, v, hp, hu, hv⟩ es et
  exact tail_ct u v hp.1.1 hp.2.1.1 hp.2.2 _ _ _ _ _ _ ⟨hu, hv⟩ es et

theorem x25519Base_ct :
    ConstantTime isa x25519BaseLocal.pre x25519BaseLocal.pub x25519Base := by
  apply VG.RelCT.constantTime (Q := fun _ _ => True)
  have pro := ctWithRuns combAddr_ct (fun _ _ h => ⟨combAddr_ok h.1, combAddr_ok h.2.1⟩)
  rw [x25519Base]
  refine VG.RelCT.seq pro ?_
  intro s t ts tt s' t' ⟨_, u, v, ⟨_, _, hp⟩, Pu, Pv⟩ es et
  exact x25519BaseBody_ct _ _ _ _ _ _ ⟨Pu.pre, Pv.pre, Prologue.pub Pu Pv hp⟩ es et

theorem x25519Base_ok (s : State) (h : x25519BaseLocal.pre s) :
    ∃ tr t, Exec isa x25519Base s tr t ∧ abiPreserved s t ∧ x25519BaseLocal.post s t :=
  x25519Base_correct h

/-- Memory holding the arguments `0x1000, 0x2000, 0x4000` at `0x8004`. -/
def satArgs : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x40 else 0

/-- A state satisfying the precondition: the tables at `0x100000`. -/
def satState : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMemWith satArgs
  rd := [⟨0x2000, 32⟩, ⟨0x8004, 12⟩, ⟨0x100000, 24576⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩]
  syms _ := 0x100000

theorem sat_arg (j : Nat) (hj : j < 3) : arg satState j = satArgs.readW (argAddr satState j) 32 := by
  unfold arg
  apply Mem.readW_congr
  intro b hb
  change satMemWith satArgs _ = _
  rw [satMemWith_out]
  have : ∀ j < 3, ∀ b < 4, 8 * 32 * 96 ≤ (argAddr satState j + BitVec.ofNat 64 b - 0x100000).toNat := by
    decide
  exact this j hj b (by omega)

theorem x25519Base_sat :
    (Spec.X25519.x25519BaseContract (X86.abi.withConsts combConsts) 8).pre satState := by
  have hl := combWords_length
  have a0 : arg satState 0 = 0x1000 := (sat_arg 0 (by decide)).trans (by decide)
  have a1 : arg satState 1 = 0x2000 := (sat_arg 1 (by decide)).trans (by decide)
  have a2 : arg satState 2 = 0x4000 := (sat_arg 2 (by decide)).trans (by decide)
  have held : TblWords ((satState.syms combSym).setWidth 64) satState.mem := satMemWith_held satArgs
  generalize e : satState = s
  sig_pre [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst s
  refine ⟨by decide, by decide, by rw [hl]; rfl, held, by rw [hl]; decide, ?_, ?_, ?_, ?_⟩
  · rw [hl]
    intro r hr
    change r ∈ [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · rw [hl]; exact Region.disjoint_of_sep (by decide)
  · rw [hl]; exact Region.disjoint_of_sep (by decide)
  · rw [a0, a1, a2]
    refine ⟨rfl, rfl, ?_⟩
    repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide

theorem x25519Base_implies :
    x25519BaseLocal.Implies (Spec.X25519.x25519BaseContract (X86.abi.withConsts combConsts) 8) where
  pre s h := by
    sig_pre [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq,
      Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨h4, hsp, hd, held, hfit, hdw, -, hstk, ht, hw, -, o2, o3, i2, s3, r0, -, r2, -,
      b0, b1, b2, -, f0, f1, f2⟩ := h
    have be : callStk s = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 8, 8⟩ := below_eq (sp := s.gpr .esp) h4
    refine ⟨⟨?_, hw, o2, i2, o3.symm, s3.symm, r0, r2, f0, f1, f2, by omega, h4, by rw [be]; exact b1,
      by rw [be]; exact b2, by rw [be]; exact b0⟩, by rw [be]; exact b0, held, hfit, ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hdw _ (by rw [hw]; simp)
      · rw [be]; exact hstk
  post := by
    intro s t _ h
    sig_post [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq, Abi.withConsts]
    exact h
  pub s t _ _ h := by
    sig_pub [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq, Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1, h2⟩ := h
    exact ⟨hsp, h0, h1, h2, hsy⟩
  sat := ⟨satState, x25519Base_sat⟩

theorem x25519Base_verified :
    Verified X86.target x25519Base (Spec.X25519.x25519BaseContract (X86.abi.withConsts combConsts) 8) :=
  Verified.of_correct x25519Base_ok x25519Base_ct x25519Base_implies

end VG.Proof.X25519.X86.Base
