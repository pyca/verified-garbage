import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseCTSetup
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseLit
import VerifiedGarbage.Proof.Ed25519.X86.CombCT
import VerifiedGarbage.Proof.Ed25519.X86.CombLoop
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Inline

/-! Merged from `Proof.Ed25519.X86.ScalarBaseCT`. -/
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
    apply VG.RelCT.taint (A := taint) (regsTaint [.esp]) _ (by taint_decide)
    intro s t h
    exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸
      (h.1.esp.trans (hp.1.trans h.2.esp.symm)))
  have hh := ctWithRuns loadct (fun _ _ h => ⟨loadArg_ok (i := 0) ps h.1 (by decide),
    loadArg_ok (i := 0) pt h.2 (by decide)⟩)
  have tailct : RelCT isa (fun s t => s.gpr .edi = t.gpr .edi ∧ s.gpr .esi = t.gpr .esi)
      (.block (outputWords 96 8 ++ Impl.X25519.X86.restore)) (fun _ _ => True) := by
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

def baseSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x40 else 0

def baseSatState : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMemWith baseSatMem
  rd := [⟨0x2000, 32⟩, ⟨0x100000, 24576⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩, ⟨0x8004, 12⟩]
  syms _ := 0x100000

theorem baseSat_arg (j : Nat) (hj : j < 3) :
    arg baseSatState j = baseSatMem.readW (argAddr baseSatState j) 32 := by
  unfold arg
  apply Mem.readW_congr
  intro b hb
  change satMemWith baseSatMem _ = _
  rw [satMemWith_out]
  have : ∀ j < 3, ∀ b < 4, 8 * 32 * 96 ≤ (argAddr baseSatState j + BitVec.ofNat 64 b - 0x100000).toNat := by
    decide
  exact this j hj b (by omega)

theorem scalarBase_ok (s : State) (h : scalarBaseLocal.pre s) :
    ∃ tr t, Exec isa scalarBase s tr t ∧ abiPreserved s t ∧ scalarBaseLocal.post s t :=
  scalarBase_correct h

/-- The shared contract's precondition, with the arguments' area writable (as the calling
convention gives it): the proof narrows it to `scalarBaseLocal`'s. -/
def scalarBaseWide : Contract isa :=
  { scalarBaseLocal with
  pre := fun s =>
    let out : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let input : Region := ⟨(arg s 1).setWidth 64, 32⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := callStk s
    s.rd = [input, TBL ((s.syms combSym).setWidth 64)] ∧ s.wr = [out, scratch, args] ∧
      out.Disjoint scratch ∧ input.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 1).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 ∧ 8 ≤ (s.gpr .esp).toNat ∧ stk.Disjoint input ∧
      stk.Disjoint scratch ∧ stk.Disjoint out ∧ CombHeld s [out, scratch, stk] }

def scalarBaseRd (s : State) : List Region :=
  [⟨(arg s 1).setWidth 64, 32⟩, ⟨argAddr s 0, 12⟩, TBL ((s.syms combSym).setWidth 64)]
def scalarBaseWr (s : State) : List Region := [⟨(arg s 0).setWidth 64, 32⟩, ⟨(arg s 2).setWidth 64, 8192⟩]

theorem scalarBaseWide_pre (s : State) (h : scalarBaseWide.pre s) :
    scalarBaseLocal.pre (s.withRegions (scalarBaseRd s) (scalarBaseWr s)) := by
  obtain ⟨-, -, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  simp only [scalarBaseLocal, BaseRegions, scalarBaseRd, scalarBaseWr, arg_withRegions,
    argAddr_withRegions, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_syms, callStk]
  exact ⟨⟨True.intro, True.intro, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩, h16, h17⟩

/-- The `n` bytes below `sp`, as the contract states them. -/
theorem below_eq {sp : BitVec 32} {n : Nat} (h : n ≤ sp.toNat) :
    below sp n = ⟨sp.setWidth 64 - BitVec.ofNat 64 n, n⟩ := by
  simp only [below, Taint.sub_setWidth h]

theorem scalarBase_sat :
    (Spec.Ed25519.scalarBaseContract (X86.abi.withConsts combConsts) 8).pre baseSatState := by
  have hl := combWords_length
  have a0 : arg baseSatState 0 = 0x1000 := (baseSat_arg 0 (by decide)).trans (by decide)
  have a1 : arg baseSatState 1 = 0x2000 := (baseSat_arg 1 (by decide)).trans (by decide)
  have a2 : arg baseSatState 2 = 0x4000 := (baseSat_arg 2 (by decide)).trans (by decide)
  have held : TblWords ((baseSatState.syms combSym).setWidth 64) baseSatState.mem :=
    satMemWith_held baseSatMem
  generalize e : baseSatState = s
  sig_pre [Spec.Ed25519.scalarBaseContract, Spec.Ed25519.scalarBaseSig,
    Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst s
  refine ⟨by decide, by decide, by rw [hl]; rfl, held, by rw [hl]; decide, ?_, ?_, ?_, ?_⟩
  · rw [hl]
    intro r hr
    change r ∈ [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩, ⟨0x8004, 12⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · rw [hl]; exact Region.disjoint_of_sep (by decide)
  · rw [hl]; exact Region.disjoint_of_sep (by decide)
  · rw [a0, a1, a2]
    refine ⟨rfl, rfl, ?_⟩
    repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide

theorem scalarBaseWide_implies :
    scalarBaseWide.Implies (Spec.Ed25519.scalarBaseContract (X86.abi.withConsts combConsts) 8) where
  pre s h := by
    sig_pre [Spec.Ed25519.scalarBaseContract, Spec.Ed25519.scalarBaseSig,
      Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq,
      Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨h4, hsp, hd, held, hfit, hdw, -, hstk, ht, hw, -, o2, o3, i2, -, s3, r0, -, r2, -,
      b0, b1, b2, -, f0, f1, f2⟩ := h
    have be : callStk s = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 8, 8⟩ := below_eq (sp := s.gpr .esp) h4
    refine ⟨?_, hw, o2, i2, o3.symm, s3.symm, r0, r2, f0, f1, f2, by omega, h4, by rw [be]; exact b1,
      by rw [be]; exact b2, by rw [be]; exact b0, held, hfit, ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hdw _ (by rw [hw]; simp)
      · rw [be]; exact hstk
  post := by
    intro s t _ h
    sig_post [Spec.Ed25519.scalarBaseContract, Spec.Ed25519.scalarBaseSig,
      Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq,
      Abi.withConsts]
    exact h
  pub s t _ _ h := by
    sig_pub [Spec.Ed25519.scalarBaseContract, Spec.Ed25519.scalarBaseSig,
      Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq,
      Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1, h2⟩ := h
    exact ⟨hsp, h0, h1, h2, hsy⟩
  sat := ⟨baseSatState, scalarBase_sat⟩

theorem scalarBase_verified :
    Verified X86.target scalarBase (Spec.Ed25519.scalarBaseContract (X86.abi.withConsts combConsts) 8) := by
  have hsat := scalarBaseWide_implies.sat_left
  have satLocal : ∃ s, scalarBaseLocal.pre s := hsat.elim fun s h => ⟨_, scalarBaseWide_pre s h⟩
  have verifiedLocal : Verified X86.target scalarBase scalarBaseLocal :=
    Verified.of_correct scalarBase_ok scalarBase_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal scalarBaseRd scalarBaseWr scalarBaseWide_pre
    ?_ ?_ ?_ ?_ hsat) scalarBaseWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [scalarBaseRd, scalarBaseWr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rcases hr with (rfl | rfl | rfl) | rfl | rfl <;> simp only [true_or, or_true]
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [scalarBaseWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [scalarBaseWide, scalarBaseLocal, arg_withRegions, State.withRegions_mem] using h
  · intro s t _ _ h
    simpa only [scalarBaseWide, scalarBaseLocal, arg_withRegions, State.withRegions_gpr,
      State.withRegions_syms] using h

end VG.Proof.Ed25519.X86
