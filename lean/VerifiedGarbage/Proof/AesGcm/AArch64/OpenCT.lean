import VerifiedGarbage.Proof.AesGcm.AArch64.SealCT

/-!
# AES-GCM on AArch64: `vg_aes_gcm_open` leaks only whether the tag is right

Untrusted: everything here is checked by Lean. As for `seal` (`SealCT.lean`),
with the received tag copied in and compared, and the text decrypted, by
`decAbs_rel` and the taint analysis. The branches on the tag length and on the comparison are public:
the tag length is an argument, and whether the tag is right is what
`openAArch64.pub` leaks.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph)

/-- The bit `openMain` computes, after `tagIn`, is whether `open` succeeds. -/
theorem tagBit {Ctx W SP Np A D Tg : Addr} {R nl al n tl : Nat} {s₀ t : State}
    (o : OpenIn Ctx W SP Np A D Tg R nl al n tl s₀ t) (rt : bytesAt t.mem W tl = bytesAt s₀.mem Tg tl)
    (hok : Spec.Gcm.tagLenOk tl = true) :
    decide ((Spec.Gcm.fullTag (ciphOf t.mem Ctx R) (blockAt t.mem (Ctx + BitVec.ofNat 64 240))
      (bytesAt t.mem Np nl) (bytesAt t.mem A al) (bytesAt t.mem D n)).take tl = bytesAt t.mem W tl) =
    (Spec.Gcm.openResult (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) tl (bytesAt s₀.mem Np nl)
      (bytesAt s₀.mem D n) (bytesAt s₀.mem A al) (bytesAt s₀.mem Tg tl)).isSome := by
  obtain ⟨hc₃, hH₃, hN₃, hA₃, hD₃⟩ := o.vals
  rw [hc₃, hH₃, hN₃, hA₃, hD₃, rt, Spec.Gcm.openResult, ite_eq_left hok, Spec.Gcm.decryptWith]
  by_cases hc : (Spec.Gcm.fullTag (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl)
      (bytesAt s₀.mem A al) (bytesAt s₀.mem D n)).take tl = bytesAt s₀.mem Tg tl
  · rw [ite_eq_left hc]; simp [hc]
  · rw [ite_eq_right hc]; simp [hc]

/-- `FrontIn` from `OpenIn`. -/
theorem OpenIn.front {Ctx W SP Np A D Tg : Addr} {R nl al n tl : Nat} {s₀ t : State}
    (o : OpenIn Ctx W SP Np A D Tg R nl al n tl s₀ t) :
    FrontIn Ctx (W + BitVec.ofNat 64 16) W SP t.gpr Np A D nl al n t :=
  ⟨o.env, fun _ _ => rfl, o.x23, o.x24, o.x26, o.x27, o.non, o.aad, o.sA, o.sL, o.sD, o.sN⟩

/-- `openMain` up to the branch on the tag, in two runs. -/
theorem omA_rel (v : GcmImpl) {Ctx W SP Np A D Tg : Addr} {R nl al n tl : Nat} {s₁ s₂ t₁ t₂ : State}
    (o₁ : OpenIn Ctx W SP Np A D Tg R nl al n tl s₁ t₁) (o₂ : OpenIn Ctx W SP Np A D Tg R nl al n tl s₂ t₂) :
    RelCT isa (Eq2 t₁ t₂) (omA v.callees) TT := by
  have L := o₁.lay
  have hal := o₁.aad.lt
  have hn := o₁.dat.ok.lt
  have sl := slots_omFrame L o₁.ddW
  have mF : ∀ {rs : List Region}, (∀ r ∈ rs, r ∈ omFrame W) → ∀ {m m' : Mem}, Frame rs m m' →
      Frame (omFrame W) m m' := fun hs _ _ hf => hf.mono hs
  unfold omA
  refine front_rel L v o₁.front o₂.front fun u₁ u₂ p₁ p₂ => ?_
  have mkB : ∀ {s t u : State}, OpenIn Ctx W SP Np A D Tg R nl al n tl s t →
      FrontOut Ctx (W + BitVec.ofNat 64 16) W SP t.gpr D al n t u →
      BodyIn Ctx (W + BitVec.ofNat 64 16) W SP u.gpr R n 0 D (Spec.Gcm.zeros al) []
        (blockAt u.mem (Ctx + BitVec.ofNat 64 240)) u := fun o p =>
    ⟨p.env, fun _ _ => rfl, by rw [p.x22, o.x22], o.rounds, by rw [p.x25, Proof.Gcm.length_zeros],
      p.x26, p.x27, p.x28, rfl, by decide, o.dat.of_eq (by rw [p.rd]) (by rw [p.wr]), rfl⟩
  have B₁ := mkB o₁ p₁
  have B₂ := mkB o₂ p₂
  refine rel_seq (decAbs_rel L v B₁ B₂ rfl) (decAbs_ok L v B₁) (decAbs_ok L v B₂)
    fun w₁ w₂ ⟨e₁, kk₁, _, fr₁, _, _, _⟩ ⟨e₂, kk₂, _, fr₂, _, _, _⟩ => ?_
  have F₁ : Frame (omFrame W) t₁.mem w₁.mem :=
    (mF (fun r hr => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hr))) p₁.frame).trans
      (mF (fun r hr => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hr))) fr₁)
  have F₂ : Frame (omFrame W) t₂.mem w₂.mem :=
    (mF (fun r hr => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hr))) p₂.frame).trans
      (mF (fun r hr => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hr))) fr₂)
  refine rel_seq (rel_taint [.x19] (by rw [e₁.sp, e₂.sp]) (by agree_tac [e₁.x19, e₂.x19]) ⟨_, by taint_decide⟩)
    (finPrep_ok (al := al) (n := n) e₁.x19 (covers_left e₁.perm.w)
      (by rw [slot_kept F₁ sl (by decide) (by decide), o₁.sL]) (by rw [slot_kept F₁ sl (by decide) (by decide), o₁.sN]))
    (finPrep_ok (al := al) (n := n) e₂.x19 (covers_left e₂.perm.w)
      (by rw [slot_kept F₂ sl (by decide) (by decide), o₂.sL]) (by rw [slot_kept F₂ sl (by decide) (by decide), o₂.sN]))
    fun z₁ z₂ ⟨x26₁, x27₁, r₁⟩ ⟨x26₂, x27₂, r₂⟩ => ?_
  have y22₁ : z₁.gpr .x22 = BitVec.ofNat 64 R := by
    rw [r₁.others _ (by decide), kk₁ .x22 (by decide), p₁.x22, o₁.x22]
  have y22₂ : z₂.gpr .x22 = BitVec.ofNat 64 R := by
    rw [r₂.others _ (by decide), kk₂ .x22 (by decide), p₂.x22, o₂.x22]
  refine rel_seq (finBody_rel L v (.inr rfl) (e₁.of_regs r₁) (e₂.of_regs r₂) (fun _ _ => rfl)
      (fun _ _ => rfl) y22₁ y22₂ o₁.rounds x26₁ x26₂ x27₁ x27₂ hal hn)
    (finBody_env v L (.inr rfl) (e₁.of_regs r₁) (fun _ _ => rfl) y22₁ o₁.rounds x26₁ x27₁ hn)
    (finBody_env v L (.inr rfl) (e₂.of_regs r₂) (fun _ _ => rfl) y22₂ o₂.rounds x26₂ x27₂ hn)
    fun g₁ g₂ ⟨ge₁, _, gf₁⟩ ⟨ge₂, _, gf₂⟩ => ?_
  have G₁ : Frame (omFrame W) t₁.mem g₁.mem :=
    F₁.trans (by rw [r₁.mem] at gf₁; exact mF (fun r hr => List.mem_append_left _ (List.mem_append_right _ hr)) gf₁)
  have G₂ : Frame (omFrame W) t₂.mem g₂.mem :=
    F₂.trans (by rw [r₂.mem] at gf₂; exact mF (fun r hr => List.mem_append_left _ (List.mem_append_right _ hr)) gf₂)
  refine rel_seq (rel_taint [.x19] (by rw [ge₁.sp, ge₂.sp]) (by agree_tac [ge₁.x19, ge₂.x19]) ⟨_, by taint_decide⟩)
    (ldr28_ok (V := BitVec.ofNat 64 tl) ge₁ (by rw [slot_kept G₁ sl (by decide) (by decide), o₁.sT]))
    (ldr28_ok (V := BitVec.ofNat 64 tl) ge₂ (by rw [slot_kept G₂ sl (by decide) (by decide), o₂.sT]))
    fun h₁ h₂ ⟨x28₁, q₁⟩ ⟨x28₂, q₂⟩ => ?_
  exact rel_taint [.x19, .x28] (by rw [q₁.sp, q₂.sp, ge₁.sp, ge₂.sp])
    (by agree_tac [x28₁, x28₂, q₁.others .x19 (by decide), q₂.others .x19 (by decide), ge₁.x19, ge₂.x19])
    ⟨_, by taint_decide⟩

/-- The rest of `openMain`, in two runs that agree on the tag. -/
theorem omB_rel (v : GcmImpl) {Ctx W SP D Np A : Addr} {R nl al n tl : Nat}
    (L : Lay Ctx (W + BitVec.ofNat 64 16) W) {s s' m₁ m₂ : State} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (ddW : (⟨D, n⟩ : Region).Disjoint (workR W)) (dcW : (⟨Ctx, 256⟩ : Region).Disjoint (workR W))
    (mo₁ : MidO Ctx W SP D Np A R nl al n tl s m₁) (mo₂ : MidO Ctx W SP D Np A R nl al n tl s' m₂)
    (hx : m₁.gpr .x27 = m₂.gpr .x27) :
    RelCT isa (Eq2 m₁ m₂) (omB v.callees) TT := by
  unfold omB
  have tm : ∃ h, (taint.check (Taint.ofRegs [.x27]) (.block [mov .x0 .x27]) h).isSome = true :=
    ⟨_, by taint_decide⟩
  refine rel_seq ?_ (omIte_ok v L hR ddW dcW mo₁) (omIte_ok v L hR ddW dcW mo₂)
    fun a b ⟨ea, xa, _, _⟩ ⟨eb, xb, _, _⟩ =>
      rel_taint [.x27] (by rw [ea.sp, eb.sp]) (by agree_tac [xa, xb, hx]) tm
  have x27₁ := mo₁.x27
  have x27₂ : m₂.gpr .x27 = _ := hx ▸ x27₁
  have hlt : ∀ B : Bool, (if B then 1 else 0 : Nat) < 2 ^ 64 := fun B => by cases B <;> decide
  refine rel_ite (eval_zero x27₁ (hlt _)) (eval_zero x27₂ (hlt _)) (fun _ => ?_) (fun _ => ?_)
  · exact rel_taint [] (by rw [mo₁.env.sp, mo₂.env.sp]) (by agree_tac []) ⟨_, by taint_decide⟩
  · refine rel_seq (rel_taint [.x19] (by rw [mo₁.env.sp, mo₂.env.sp]) (by agree_tac [mo₁.env.x19, mo₂.env.x19])
      ⟨_, by taint_decide⟩) (ocLdr_ok mo₁.env mo₁.sD mo₁.sN) (ocLdr_ok mo₂.env mo₂.sD mo₂.sN)
      fun c₁ c₂ h₁ h₂ => ?_
    exact crypt_rel L v (oc_in hR mo₁ h₁) (oc_in hR mo₂ h₂)

theorem open_ct (v : GcmImpl) : ConstantTime isa openAArch64.pre openAArch64.pub («open» v.callees) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨hq, hres⟩ := hq
  have hR₁ : rounds (σ₁.gpr .x1) := (openLay h₁).1.rounds
  have hR₂ : rounds (σ₂.gpr .x1) := (openLay h₂).1.rounds
  obtain ⟨f₁, f₂⟩ := oneFacts (by decide : 2 < 3) (openCore h₁) (openCore h₂) hq
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  have qt : stackArg σ₁ 1 = stackArg σ₂ 1 := qa 1 (by decide)
  have qg : stackArg σ₁ 0 = stackArg σ₂ 0 := qa 0 (by decide)
  have hW₁ : σ₁.mem.readW (σ₁.sp + BitVec.ofNat 64 16) 64 = stackArg σ₁ 2 := rfl
  have hW₂ : σ₂.mem.readW (σ₂.sp + BitVec.ofNat 64 16) 64 = stackArg σ₁ 2 := f₂.hW
  have hT₁ : σ₁.mem.readW (σ₁.sp + BitVec.ofNat 64 8) 64 = stackArg σ₁ 1 := rfl
  have hT₂ : σ₂.mem.readW (σ₂.sp + BitVec.ofNat 64 8) 64 = stackArg σ₁ 1 := qt.symm
  have t₁ : ∃ h, (taint.check (Taint.ofRegs []) (.block [.ldrSp .x12 0]) h).isSome = true := ⟨_, by taint_decide⟩
  refine rel_seq (RelCT.block_split (rel_seq (entryStash_rel (k := 16) (j := 8) (.inr rfl) rfl (.inr rfl) f₁ f₂
      (by decide) qsp (by agree_tac [q0, q1, q2, q3, q4, q5, q6, q7]))
      (entryStash_ok (V := stackArg σ₁ 1) (by decide) (by decide) hW₁ (f₁.hsp 2 (by decide)) (f₁.hsp 1 (by decide))
        hT₁ (f₁.argW (by decide)) rfl f₁.perm)
      (entryStash_ok (V := stackArg σ₁ 1) (by decide) (by decide) hW₂ (f₂.hsp 2 (by decide)) (f₂.hsp 1 (by decide))
        hT₂ (f₂.argW (by decide)) q0.symm f₂.perm)
      fun τ₁ τ₂ a₁ a₂ => rel_taint [] (by rw [a₁.1.sp, a₂.1.sp, qsp]) (by agree_tac []) t₁))
    (openEntry_ok h₁) (openEntry_ok h₂) fun s₁ s₂ ⟨o₁, x12₁⟩ ⟨o₂, x12₂⟩ => ?_
  rw [f₂.hW, ← q0, ← q1, ← q2, ← q3, ← q4, ← q5, ← q6, ← q7, ← qsp, ← qt, ← qg] at o₂
  rw [← qg] at x12₂
  have hb : (openRes σ₁).isSome = (openRes σ₂).isSome := by
    rw [openLeakOf, openLeakOf, ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro hR₁)),
      ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro hR₂))] at hres
    revert hres; cases (openRes σ₁).isSome <;> cases (openRes σ₂).isSome <;> simp
  have hr₂ : openRes σ₂ = Spec.Gcm.openResult (ctxCiph σ₂.mem (σ₁.gpr .x0) (σ₁.gpr .x1).toNat)
      (ctxH σ₂.mem (σ₁.gpr .x0)) (stackArg σ₁ 1).toNat
      (bytesAt σ₂.mem (σ₁.gpr .x2) (σ₁.gpr .x3).toNat) (bytesAt σ₂.mem (σ₁.gpr .x6) (σ₁.gpr .x7).toNat)
      (bytesAt σ₂.mem (σ₁.gpr .x4) (σ₁.gpr .x5).toNat) (bytesAt σ₂.mem (stackArg σ₁ 0) (stackArg σ₁ 1).toNat) := by
    unfold openRes; rw [← q0, ← q1, ← q2, ← q3, ← q4, ← q5, ← q6, ← q7, ← qt, ← qg]
  rw [hr₂] at hb
  refine rel_seq (rel_taint [.x28] (by rw [o₁.env.sp, o₂.env.sp]) (by agree_tac [o₁.x28, o₂.x28])
      ⟨_, by taint_decide⟩)
    (tagLenOk_ok s₁ o₁.x28 o₁.tlt) (tagLenOk_ok s₂ o₂.x28 o₂.tlt) fun u₁ u₂ ⟨x9₁, r₁⟩ ⟨x9₂, r₂⟩ => ?_
  have tr : ∃ h, (taint.check (Taint.ofRegs [.x19]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  have p₁ := o₁.of_regs r₁
  have p₂ := o₂.of_regs r₂
  have y12₁ : u₁.gpr .x12 = stackArg σ₁ 0 := by rw [r₁.others _ (by decide), x12₁]
  have y12₂ : u₂.gpr .x12 = stackArg σ₁ 0 := by rw [r₂.others _ (by decide), x12₂]
  have hlt : ((if Spec.Gcm.tagLenOk (stackArg σ₁ 1).toNat then 1 else 0 : Nat)) < 2 ^ 64 := by split <;> decide
  refine rel_seq (rel_ite (eval_zero x9₁ hlt) (eval_zero x9₂ hlt) (fun _ => ?_) (fun hf => ?_))
    (oite_ok v p₁ y12₁ x9₁) (oite_ok v p₂ y12₂ x9₂) fun w₁ w₂ e₁ e₂ =>
      rel_taint [.x19] (by rw [e₁.1.sp, e₂.1.sp]) (by agree_tac [e₁.1.x19, e₂.1.x19]) tr
  · exact rel_taint [] (by rw [p₁.env.sp, p₂.env.sp]) (by agree_tac []) ⟨_, by taint_decide⟩
  have hok : Spec.Gcm.tagLenOk (stackArg σ₁ 1).toNat = true := by
    revert hf; cases Spec.Gcm.tagLenOk (stackArg σ₁ 1).toNat <;> simp
  have hle := tagLenOk_le hok
  have L := p₁.lay
  refine rel_seq (rel_taint [.x19, .x28, .x12] (by rw [p₁.env.sp, p₂.env.sp])
      (by agree_tac [p₁.env.x19, p₂.env.x19, p₁.x28, p₂.x28, y12₁, y12₂]) ⟨_, by taint_decide⟩)
    (tagIn_ok p₁.env.x19 y12₁ p₁.x28 hle p₁.tagR p₁.env.perm.w (p₁.dtW.sub_right (Region.sub_prefix (by decide))))
    (tagIn_ok p₂.env.x19 y12₂ p₂.x28 hle p₂.tagR p₂.env.perm.w (p₂.dtW.sub_right (Region.sub_prefix (by decide))))
    fun t₁ t₂ ⟨rt₁, g₁, og₁, sp₁, rd₁, wr₁⟩ ⟨rt₂, g₂, og₂, sp₂, rd₂, wr₂⟩ => ?_
  have p₁' := p₁.tagIn g₁ og₁ sp₁ rd₁ wr₁
  have p₂' := p₂.tagIn g₂ og₂ sp₂ rd₂ wr₂
  have rt₁' : bytesAt t₁.mem (stackArg σ₁ 2) (stackArg σ₁ 1).toNat =
      bytesAt σ₁.mem (stackArg σ₁ 0) (stackArg σ₁ 1).toNat := by rw [rt₁, p₁.tag]
  have rt₂' : bytesAt t₂.mem (stackArg σ₁ 2) (stackArg σ₁ 1).toNat =
      bytesAt σ₂.mem (stackArg σ₁ 0) (stackArg σ₁ 1).toNat := by rw [rt₂, p₂.tag]
  refine (openMain_split v.callees).symm.rel (rel_seq (omA_rel v p₁' p₂')
    (openMainA_ok v L p₁'.env p₁'.x22 p₁'.rounds p₁'.x23 p₁'.x24 p₁'.x26 p₁'.x27 p₁'.non p₁'.aad p₁'.dat p₁'.ddW
      p₁'.dcW p₁'.sA p₁'.sL p₁'.sD p₁'.sN p₁'.sT hok)
    (openMainA_ok v L p₂'.env p₂'.x22 p₂'.rounds p₂'.x23 p₂'.x24 p₂'.x26 p₂'.x27 p₂'.non p₂'.aad p₂'.dat p₂'.ddW
      p₂'.dcW p₂'.sA p₂'.sL p₂'.sD p₂'.sN p₂'.sT hok) fun m₁ m₂ mo₁ mo₂ => ?_)
  refine omB_rel v L p₁'.rounds p₁'.ddW p₁'.dcW mo₁ mo₂ ?_
  rw [mo₁.x27, mo₂.x27, tagBit p₁' rt₁' hok, tagBit p₂' rt₂' hok]
  simp only [openRes] at hb
  rw [hb]

end VG.Proof.AesGcm.AArch64
