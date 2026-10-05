import VerifiedGarbage.Proof.AesOcb.Arm.CTBody

/-!
# AES-OCB on ARMv7: `vg_aes_ocb_seal` and `vg_aes_ocb_open` are constant time

Untrusted: everything here is checked by Lean. Two runs with the same
public arguments (`onePub`) have the same `prmOf`; each piece of `seal` and
`open` is related in the two runs by the lemmas of `CTPre.lean` and
`CTBody.lean`, the entry, the copy of the tag, the comparison, the mask and
the restore by the taint analysis (`seal_ct`, `open_ct`). `open` compares
the tags and masks the data without a branch: whether the tag is right, in
`r0`, is never branched on nor used as an address.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (blockAtMem)
open VG.Proof.Ocb (blockAtMem_frame)
open VG.Impl.AesGcm.Arm (imm addI restore)

/-- `(a; (b; (c; (d; e)))); f`, from `a; (b; (c; (d; (e; f))))`. -/
theorem rel_assoc5 {P Q : State → State → Prop} {a b c d e f : Prog isa}
    (h : RelCT isa P (.seq a (.seq b (.seq c (.seq d (.seq e f))))) Q) :
    RelCT isa P (.seq (.seq a (.seq b (.seq c (.seq d e)))) f) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq a₁ f₁ => cases a₁ with | seq a₁ b₁ => cases b₁ with | seq b₁ c₁ => cases c₁ with
    | seq c₁ d₁ => cases d₁ with | seq d₁ e₁ =>
  cases e₂ with | seq a₂ f₂ => cases a₂ with | seq a₂ b₂ => cases b₂ with | seq b₂ c₂ => cases c₂ with
    | seq c₂ d₂ => cases d₂ with | seq d₂ e₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ (.seq c₁ (.seq d₁ (.seq e₁ f₁)))))
    (.seq a₂ (.seq b₂ (.seq c₂ (.seq d₂ (.seq e₂ f₂)))))
  simp only [List.append_assoc] at ht ⊢
  exact ⟨ht, hq⟩

/-- Two runs with the same public arguments have the same `prmOf`. -/
theorem prm_eq {s₁ s₂ : State} (h : onePub s₁ s₂) : prmOf s₂ = prmOf s₁ := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := h
  simp only [prmOf, ← q₀, ← q₁, ← q₂, ← q₃, ← q₄, ← qa 0 (by decide), ← qa 1 (by decide), ← qa 2 (by decide),
    ← qa 3 (by decide), ← qa 4 (by decide), ← qa 5 (by decide), ← qa 6 (by decide)]

theorem entry_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint [.r0, .r1, .r2, .r3] 28) (.block entry) h).isSome =
    true := ⟨_, by taint_decide⟩

/-- The entry, in two runs with the same public arguments. -/
theorem entry_rel {p : Prm} (L : Lay p) {σ₁ σ₂ : State} (P₁ : Perm p σ₁) (P₂ : Perm p σ₂) (h₁ : σ₁.sp = p.SP)
    (h₂ : σ₂.sp = p.SP) (hq : onePub σ₁ σ₂) : RelCT isa (Eq2 σ₁ σ₂) (.block entry) TT := by
  obtain ⟨-, q₀, q₁, q₂, q₃, qa⟩ := hq
  have spf := L.spf
  have hw : ∀ {σ : State}, σ.sp = p.SP → Perm p σ →
      σ.sp.toNat + 28 ≤ 2 ^ 32 ∧ ∀ r ∈ σ.wr, Region.Disjoint ⟨State.addr σ.sp, 28⟩ r := fun h P =>
    ⟨by rw [h]; omega, fun r hr => by rw [h]; exact P.argw r hr⟩
  refine rel_arg [.r0, .r1, .r2, .r3] 28 (fun r hr => ?_) (by rw [h₁, h₂]) (hw h₁ P₁) (hw h₂ P₂)
    (fun k hk => argMem_of (j := 7) (by rw [h₁, h₂]) (by rw [h₁]; omega) qa k (by omega)) entry_check
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [q₀, q₁, q₂, q₃]

/-- What the entry and `Offset_0` leave. -/
abbrev EN (p : Prm) (σ : State) (c : State) : Prop := ∃ a, EntryPost p σ a ∧ NonceOut p a c

/-- The entry and `Offset_0`. -/
theorem en_wp {p : Prm} (L : Lay p) {s₀ : State} (P : Perm p s₀) (A : Args p s₀.mem) (hsp : s₀.sp = p.SP)
    (h0 : s₀.gpr .r0 = p.K) (h1 : s₀.gpr .r1 = BitVec.ofNat 32 p.R) (h2 : s₀.gpr .r2 = p.N)
    (h3 : s₀.gpr .r3 = BitVec.ofNat 32 p.nl) (hW : s₀.mem.readW (State.addr (s₀.sp + BitVec.ofNat 32 24)) 32 = p.W) :
    WP isa (.seq (.block entry) nonce) s₀ (EN p s₀) :=
  WP.seq (WP.mono (entry_wp L P hsp h0 h1 h2 h3 hW) fun a Ea =>
    WP.mono (nonce_ok L Ea.env (args_W L Ea.frame A) Ea.r4 Ea.r5) fun _ Nc => ⟨a, Ea, Nc⟩)

/-- The entry, `Offset_0` and `HASH`, in two runs with the same public
arguments. -/
theorem pre_rel {p : Prm} (L : Lay p) {σ₁ σ₂ : State} (P₁ : Perm p σ₁) (P₂ : Perm p σ₂) (A₁ : Args p σ₁.mem)
    (A₂ : Args p σ₂.mem) (hs₁ : σ₁.sp = p.SP) (hs₂ : σ₂.sp = p.SP)
    (h0₁ : σ₁.gpr .r0 = p.K) (h1₁ : σ₁.gpr .r1 = BitVec.ofNat 32 p.R) (h2₁ : σ₁.gpr .r2 = p.N)
    (h3₁ : σ₁.gpr .r3 = BitVec.ofNat 32 p.nl)
    (hW₁ : σ₁.mem.readW (State.addr (σ₁.sp + BitVec.ofNat 32 24)) 32 = p.W)
    (h0₂ : σ₂.gpr .r0 = p.K) (h1₂ : σ₂.gpr .r1 = BitVec.ofNat 32 p.R) (h2₂ : σ₂.gpr .r2 = p.N)
    (h3₂ : σ₂.gpr .r3 = BitVec.ofNat 32 p.nl)
    (hW₂ : σ₂.mem.readW (State.addr (σ₂.sp + BitVec.ofNat 32 24)) 32 = p.W) (hq : onePub σ₁ σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (.seq (.block entry) nonce) Impl.AesOcb.Arm.hash) TT := by
  refine rel_seq (rel_seq (entry_rel L P₁ P₂ hs₁ hs₂ hq) (entry_wp L P₁ hs₁ h0₁ h1₁ h2₁ h3₁ hW₁)
    (entry_wp L P₂ hs₂ h0₂ h1₂ h2₂ h3₂ hW₂) fun a₁ a₂ E₁ E₂ => nonce_rel L E₁.env E₂.env (args_W L E₁.frame A₁)
      (args_W L E₂.frame A₂) (by rw [E₁.r4, E₂.r4]) (by rw [E₁.r5, E₂.r5]))
    (en_wp L P₁ A₁ hs₁ h0₁ h1₁ h2₁ h3₁ hW₁) (en_wp L P₂ A₂ hs₂ h0₂ h1₂ h2₂ h3₂ hW₂)
    fun _ _ ⟨a₁, E₁, N₁⟩ ⟨a₂, E₂, N₂⟩ => ?_
  have l0 : ∀ {σ a c : State}, EntryPost p σ a → NonceOut p a c →
      blockAtMem c.mem (State.addr p.W + BitVec.ofNat 64 l0O) = Spec.Ocb.lAt (lstarOf p c.mem) 0 := fun E N => by
    rw [blockAtMem_frame N.frame (by wdisj L), E.l0]
    exact congrArg (Spec.Ocb.lAt · 0) ((lstar_mut L (nonceR_mut L N.frame)).trans (lstar_W L E.frame)).symm
  exact hash_rel L N₁.env N₂.env ((args_W L E₁.frame A₁).mut L (nonceR_mut L N₁.frame))
    ((args_W L E₂.frame A₂).mut L (nonceR_mut L N₂.frame)) (l0 E₁ N₁) (l0 E₂ N₂)

theorem tagOut_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs []) 24) tagOut h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem restore_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [])) (.block restore)
    h).isSome = true := ⟨_, by taint_decide⟩

/-- What `seal` and `open` know of a run at the entry. -/
structure Run (p : Prm) (σ : State) : Prop where
  perm : Perm p σ
  args : Args p σ.mem
  sp : σ.sp = p.SP
  r0 : σ.gpr .r0 = p.K
  r1 : σ.gpr .r1 = BitVec.ofNat 32 p.R
  r2 : σ.gpr .r2 = p.N
  r3 : σ.gpr .r3 = BitVec.ofNat 32 p.nl
  w : σ.mem.readW (State.addr (σ.sp + BitVec.ofNat 32 24)) 32 = p.W

theorem run_of {σ : State} (P : Perm (prmOf σ) σ) : Run (prmOf σ) σ :=
  ⟨P, args_of σ, rfl, rfl, (ofNat_toNat32' _).symm, rfl, (ofNat_toNat32' _).symm, rfl⟩

/-- `vg_aes_ocb_seal`, in two runs with the same public arguments. -/
theorem seal_rel {p : Prm} (L : Lay p) {σ₁ σ₂ : State} (R₁ : Run p σ₁) (R₂ : Run p σ₂) (hq : onePub σ₁ σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) «seal» TT := by
  unfold «seal» front
  refine rel_assoc5 (RelCT.assoc (RelCT.assoc (rel_seq (pre_rel L R₁.perm R₂.perm R₁.args R₂.args R₁.sp R₂.sp
    R₁.r0 R₁.r1 R₁.r2 R₁.r3 R₁.w R₂.r0 R₂.r1 R₂.r2 R₂.r3 R₂.w hq)
    (WP.assoc' (pre_wp' L R₁.perm R₁.args R₁.sp R₁.r0 R₁.r1 R₁.r2 R₁.r3 R₁.w))
    (WP.assoc' (pre_wp' L R₂.perm R₂.args R₂.sp R₂.r0 R₂.r1 R₂.r2 R₂.r3 R₂.w)) fun e₁ e₂ P₁ P₂ => ?_)))
  refine rel_seq (bodySeal_rel L P₁.env P₂.env P₁.args P₂.args P₁.ofs P₁.o0 P₁.ck (by rw [P₁.l0, P₁.lstar])
    P₂.ofs P₂.o0 P₂.ck (by rw [P₂.l0, P₂.lstar]))
    (bodySeal_ok L P₁.env P₁.args P₁.ofs P₁.o0 P₁.ck (by rw [P₁.l0, P₁.lstar]))
    (bodySeal_ok L P₂.env P₂.args P₂.ofs P₂.o0 P₂.ck (by rw [P₂.l0, P₂.lstar])) fun f₁ f₂ B₁ B₂ => ?_
  refine rel_seq (tag_rel L B₁.env B₂.env (.inl rfl)) (tag_ok L B₁.env (.inl rfl)) (tag_ok L B₂.env (.inl rfl))
    fun g₁ g₂ T₁ T₂ => ?_
  have A₁ : Args p g₁.mem := (P₁.args.mut L (bodyR_mut L B₁.frame)).mut L (tagR_mut L (.inl (by decide)) T₁.frame)
  have A₂ : Args p g₂.mem := (P₂.args.mut L (bodyR_mut L B₂.frame)).mut L (tagR_mut L (.inl (by decide)) T₂.frame)
  exact rel_seqX (rel_envArg L T₁.env T₂.env A₁ A₂ [] (by simp) tagOut_check)
    (kept_of L T₁.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (kept_of L T₂.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    fun _ _ K₁ K₂ => rel_env K₁.env K₂.env [] (by simp) restore_check

theorem recv_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs []) 24) recv h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cmp_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs []) 24) cmp h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mask_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs []) 24) mask h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `vg_aes_ocb_open`, in two runs with the same public arguments. -/
theorem open_rel {p : Prm} (L : Lay p) {σ₁ σ₂ : State} (R₁ : Run p σ₁) (R₂ : Run p σ₂) (hq : onePub σ₁ σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) «open» TT := by
  unfold «open» front
  refine rel_assoc5 (RelCT.assoc (RelCT.assoc (rel_seq (pre_rel L R₁.perm R₂.perm R₁.args R₂.args R₁.sp R₂.sp
    R₁.r0 R₁.r1 R₁.r2 R₁.r3 R₁.w R₂.r0 R₂.r1 R₂.r2 R₂.r3 R₂.w hq)
    (WP.assoc' (pre_wp' L R₁.perm R₁.args R₁.sp R₁.r0 R₁.r1 R₁.r2 R₁.r3 R₁.w))
    (WP.assoc' (pre_wp' L R₂.perm R₂.args R₂.sp R₂.r0 R₂.r1 R₂.r2 R₂.r3 R₂.w)) fun e₁ e₂ P₁ P₂ => ?_)))
  refine rel_seq (bodyOpen_rel L P₁.env P₂.env P₁.args P₂.args P₁.ofs P₁.o0 P₁.ck (by rw [P₁.l0, P₁.lstar])
    P₂.ofs P₂.o0 P₂.ck (by rw [P₂.l0, P₂.lstar]))
    (bodyOpen_ok L P₁.env P₁.args P₁.ofs P₁.o0 P₁.ck (by rw [P₁.l0, P₁.lstar]))
    (bodyOpen_ok L P₂.env P₂.args P₂.ofs P₂.o0 P₂.ck (by rw [P₂.l0, P₂.lstar])) fun f₁ f₂ B₁ B₂ => ?_
  refine rel_seq (tag_rel L B₁.env B₂.env (.inr rfl)) (tag_ok L B₁.env (.inr rfl)) (tag_ok L B₂.env (.inr rfl))
    fun g₁ g₂ T₁ T₂ => ?_
  have A₁ : Args p g₁.mem :=
    (P₁.args.mut L (bodyR_mut L B₁.frame)).mut L (tagR_mut L (.inr ⟨by decide, by decide⟩) T₁.frame)
  have A₂ : Args p g₂.mem :=
    (P₂.args.mut L (bodyR_mut L B₂.frame)).mut L (tagR_mut L (.inr ⟨by decide, by decide⟩) T₂.frame)
  refine rel_seqX (rel_envArg L T₁.env T₂.env A₁ A₂ [] (by simp) recv_check)
    (kept_of L T₁.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (kept_of L T₂.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel)) fun h₁ h₂ K₁ K₂ => ?_
  refine rel_seqX (rel_envArg L K₁.env K₂.env (K₁.args A₁) (K₂.args A₂) [] (by simp) cmp_check)
    (kept_of L K₁.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (kept_of L K₂.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel)) fun i₁ i₂ M₁ M₂ => ?_
  exact rel_seqX (rel_envArg L M₁.env M₂.env (M₁.args (K₁.args A₁)) (M₂.args (K₂.args A₂)) [] (by simp) mask_check)
    (kept_of L M₁.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (kept_of L M₂.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    fun _ _ N₁ N₂ => rel_env N₁.env N₂.env [] (by simp) restore_check

theorem seal_ct : ConstantTime isa sealArm.pre sealArm.pub «seal» := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  have e := prm_eq hq
  have R₂ := run_of (sealPerm h₂)
  rw [e] at R₂
  exact seal_rel (lay_of h₁.2.2.1) (run_of (sealPerm h₁)) R₂ hq

theorem open_ct : ConstantTime isa openArm.pre openArm.pub «open» := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  have e := prm_eq hq.1
  have R₂ := run_of (openPerm h₂)
  rw [e] at R₂
  exact open_rel (lay_of h₁.2.2) (run_of (openPerm h₁)) R₂ hq.1

end VG.Proof.AesOcb.Arm
