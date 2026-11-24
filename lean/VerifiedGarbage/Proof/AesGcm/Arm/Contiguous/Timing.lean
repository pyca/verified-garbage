module

public import VerifiedGarbage.Proof.AesGcm.Arm.Contiguous.Body
public import VerifiedGarbage.Proof.AesGcm.Arm.CTOpen
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.AesGcm.Arm.Contiguous
import VerifiedGarbage.Proof.Framework.Block

/-! Both address layouts run the same public AES-GCM control flow. -/
@[expose] public section
namespace VG.Proof.AesGcm.Arm.Contiguous
open VG VG.Arm VG.Impl.AesGcm.Arm VG.Impl.AesGcm.Arm.Contiguous

variable {t₀ : State} {c st w sp : BitVec 32} {R : Nat}

theorem load_wp (hf : t₀.sp.toNat + 4 * 7 ≤ 2 ^ 32) (hin : args t₀ 7 ∈ t₀.rd) {s : State}
    (hs : FT 7 t₀ c st w sp R s) :
    WP isa (.block cryptArgs) s fun s' => FT 7 t₀ c st w sp R s' ∧
      s'.gpr .r4 = arg t₀ 5 ∧ s'.gpr .r5 = arg t₀ 3 ∧ s'.gpr .r6 = arg t₀ 2 := by
  obtain ⟨k7, he, hk⟩ := hs
  obtain ⟨s', run, h4, h5, h6, g, k⟩ := cryptArgs_run hk hf hin
  exact WP.of_runBlock ⟨s', run, ⟨k7, he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g _ (by decide) (by decide) (by decide)) k.sp k.rd k.wr,
    hk.of_eq k.mem k.sp k.rd k.wr⟩, h4, h5, h6⟩


theorem payload_rel {s₀ s₀' : State} (ho : Layout s₀) (ho' : Layout s₀')
    (hq : onePub 7 s₀ s₀') :
    RelCT isa (fun a b => OF 7 6 s₀ s₀ a ∧ OF 7 6 s₀ s₀' b) (.seq (.block cryptArgs) cryptTo)
      fun a b => OF 7 6 s₀ s₀ a ∧ OF 7 6 s₀ s₀' b := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := id hq
  have h0 := ho.basic
  have h0' := ho'.basic
  have L := oneLay h0
  have spf := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf' := h0'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : args s₀ 7 ∈ s₀.rd := h0.1.2.2.2
  have hin' : args s₀' 7 ∈ s₀'.rd := h0'.1.2.2.2
  have e4 : arg s₀' 6 = arg s₀ 6 := (qa 6 (by decide)).symm
  have est : oSt s₀' 6 = oSt s₀ 6 := by show arg s₀' _ + _ = arg s₀ _ + _; rw [e4]
  let D1 : State → State → Prop := fun t₀ s => OF 7 6 s₀ t₀ s ∧ s.gpr .r4 = arg s₀ 5 ∧
    s.gpr .r5 = arg s₀ 3 ∧ s.gpr .r6 = arg s₀ 2
  have x1 := rel_agree (F := OF 7 6 s₀ s₀) (F' := OF 7 6 s₀ s₀')
    (G := D1 s₀) (G' := D1 s₀')
    (argTaint [] 28) (c := .block cryptArgs)
    (fun _ _ ⟨_, _, a⟩ ⟨_, _, b⟩ => a.agree b q₀ spf qa (one_hw h0) (one_hw h0') (by simp))
    ⟨_, by taint_decide⟩
    (fun s h => load_wp spf hin h)
    (fun s h => WP.mono (load_wp spf' hin' h) fun s' ⟨y₁, y₂, y₃, y₄⟩ =>
      ⟨y₁, by rw [y₂, qa 5 (by decide)], by rw [y₃, qa 3 (by decide)], by rw [y₄, qa 2 (by decide)]⟩)
  have eR : (s₀'.gpr .r1).toNat = (s₀.gpr .r1).toNat := by rw [q₂]
  have ek : ∀ t : State, (t.gpr .r1).toNat = (s₀.gpr .r1).toNat →
      t.gpr .r1 = BitVec.ofNat 32 (s₀.gpr .r1).toNat := fun t e => by rw [← e]; simp
  have run : ∀ {t : State} (hot : Layout t) (ec : t.gpr .r0 = s₀.gpr .r0)
      (ew : arg t 6 = arg s₀ 6) (esp : t.sp = s₀.sp) (eR : (t.gpr .r1).toNat = (s₀.gpr .r1).toNat)
      (eS : arg t 5 = arg s₀ 5) (eT : arg t 2 = arg s₀ 2) (en : arg t 3 = arg s₀ 3) {s : State} (h : D1 t s),
      CrMG true (s₀.gpr .r0) (oSt s₀ 6) (arg s₀ 6) s₀.sp (BitVec.ofNat 32 (s₀.gpr .r1).toNat)
        (s₀.gpr .r1).toNat (arg s₀ 5) (arg s₀ 2) (arg s₀ 3).toNat 0 0 s ∧
      WP isa cryptTo s (OF 7 6 s₀ t) := fun {t} hot ec ew esp eR eS eT en s h => by
    have est : oSt t 6 = oSt s₀ 6 := congrArg (· + 16#32) ew
    obtain ⟨⟨k7, env, argsKept⟩, rs, rn, rt⟩ := h
    have ownEnv : Env (t.gpr .r0) (oSt t 6) (arg t 6) t.sp k7 (t.gpr .r1) s := by
      rw [ec, est, ew, esp, ek t eR]; exact env
    have mid := initial (Spec.Gcm.blockAt s.mem 0) ownEnv
      hot.basic.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      (rs.trans eS.symm) (by rw [rn, en]; simp) (rt.trans eT.symm)
      (hot.readable.of_eq argsKept.rd argsKept.wr) (one_dataW hot.basic hot.writable argsKept k7 _) hot.mode
    have safe : ∀ r ∈ crFrameG true (oSt t 6) (arg t 6) t.sp (arg t 2) (arg t 3).toNat,
        (args t 7).Disjoint r := by
      intro r hr
      rcases List.mem_append.mp hr with old | stack
      · exact one_argsCr hot.basic hot.writable r old
      · exact List.mem_singleton.mp stack ▸ (below12_args t
          hot.basic.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hot.mode.2.1).symm
    constructor
    · refine ⟨k7, Spec.Gcm.blockAt s.mem 0, 0, s.mem, rfl, ?_⟩
      rw [← ec, ← est, ← ew, ← esp, ← ek t eR, ← eS, ← eT, ← en, ← eR]
      exact mid
    · exact (WP.with_rdwr (cryptTo_ok (oneLay hot.basic) mid)).mono fun z ⟨out, rd, wr, sp⟩ =>
        ⟨k7, by rw [← ec, ← est, ← ew, ← esp, ← ek t eR]; exact out.env,
          argsKept.frame hot.basic.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 out.frame safe sp rd wr⟩
  have r₀ := @run s₀ ho rfl rfl rfl rfl rfl rfl rfl
  have r₁ := @run s₀' ho' q₁.symm e4 q₀.symm eR (qa 5 (by decide)).symm (qa 2 (by decide)).symm
    (qa 3 (by decide)).symm
  have x2 := rel_wp (F := D1 s₀) (F' := D1 s₀') (G := OF 7 6 s₀ s₀)
    (G' := OF 7 6 s₀ s₀')
    (rel_of_ct (cryptTo_ct L) (fun s h => (r₀ h).1) (fun s h => (r₁ h).1))
    (fun s h => (r₀ h).2) (fun s h => (r₁ h).2)
  exact x1.seq x2

theorem body_rel [VG.Proof.Gcm.Arm.GhashLaw] {s₀ s₀' : State} (h0 : Layout s₀) (h0' : Layout s₀') (hq : onePub 7 s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') body fun _ _ => True := by
  obtain h6 : onePre 7 6 s₀ := h0.basic
  obtain h6' : onePre 7 6 s₀' := h0'.basic
  have hq6 : onePub 7 s₀ s₀' := hq
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := id hq6
  obtain L := oneLay h6
  have spf := h6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf' := h6'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := SO1 7 6 s₀) (G' := SO1 7 6 s₀')
    (argTaint [.r0, .r1, .r2, .r3] (4 * 7)) (c := .block (oneEntry 24))
    (one_entry_agree (by simp) h6 h6' hq6) ⟨_, by taint_decide⟩
    (fun s e => by rw [e]; exact one1_wp h6 (by decide) (by decide) fun _ h => h)
    (fun s e => by rw [e]; exact one1_wp h6' (by decide) (by decide) fun _ h => h)
  -- the tag copied out
  let W : State → Prop := fun s => s.gpr .r11 = arg s₀ 6
  obtain c := rel_agree (F := OF 7 6 s₀ s₀) (F' := OF 7 6 s₀ s₀') (G := W) (G' := W) (argTaint [.r11] (4 * 7))
    (c := .block tagOut)
    (fun s s' ⟨_, he, hk⟩ ⟨_, he', hk'⟩ => hk.agree hk' q₀ spf qa (one_hw h6) (one_hw h6') fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [he.r11, he'.r11]) ⟨_, by taint_decide⟩
    (fun s ⟨_, he, hk⟩ => tagOut_wp L (by decide) he hk spf h6.1.2.2.2 h0.tagW h0.tagFit
      (h0.tagWork.sub_right (Region.sub_prefix (by decide))))
    (fun s ⟨_, he, hk⟩ => tagOut_wp L (by decide) he hk spf' h6'.1.2.2.2 h0'.tagW h0'.tagFit
      (by rw [qa 6 (by decide)]; exact h0'.tagWork.sub_right (Region.sub_prefix (by decide))))
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  obtain d := RelCT.taint (A := taint) (P := fun s₁ s₂ => W s₁ ∧ W s₂) (c := .block restore)
    (Taint.ofRegs [.r11]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.1, h.2]) hB
  have p := payload_rel h0 h0' hq6
  have tail := (oneTag_rel h6 h6' hq6 (by decide) (by decide) (o:=0) (.inl rfl)).seq (c.seq d)
  have joined := p.seq tail
  exact a.seq ((oneAad_rel h6 h6' hq6 (by decide) (by decide)).seq (by
    intro x y z z' t t' pre ex ex'
    cases ex with | seq l r =>
      cases r with | seq m n =>
        cases ex' with | seq l' r' =>
          cases r' with | seq m' n' =>
            simpa [List.append_assoc] using joined _ _ _ _ _ _ pre (.seq (.seq l m) n) (.seq (.seq l' m') n')))

end VG.Proof.AesGcm.Arm.Contiguous
