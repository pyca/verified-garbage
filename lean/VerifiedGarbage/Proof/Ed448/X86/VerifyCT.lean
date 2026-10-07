import VerifiedGarbage.Proof.Ed448.X86.VerifyMain
import VerifiedGarbage.Proof.Ed448.X86.VerifyLit
import VerifiedGarbage.Proof.X448.X86.Runs

/-!
# Ed448 verification's equation on x86 (32-bit): constant time

The calls of the field functions are related run by run (`RelCT`,
`Proof/X448/X86/Runs.lean`), and so is the whole function: the blocks
between them by the taint analysis, from what each run's correctness says of
its own state (`FS`: the field arithmetic's invariant and `esp`; `FE`, with
the memory but the working space and the stack below the return address,
where code reads the arguments), and the loops by `RelCT.loop`, with the
correctness proofs' invariants. `VP₀` relates the entry states.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Proof.Ed448 (RecoverOk VerifyEqOk fopValid)
open VG.Impl.Ed448.X86 (verifyEquation ventry vdecodeInit vdecodeBody vbodyA vnext decode field root RX RY)
open VG.Impl.X448.X86 (slot)

/-- Two entry states the constant-time statement relates. -/
def VP₀ (σ₁ σ₂ : State) : Prop :=
  verifyEquationLocal.pre σ₁ ∧ verifyEquationLocal.pre σ₂ ∧ verifyEquationLocal.pub σ₁ σ₂

/-- The working space, from the entry state. -/
abbrev bsV (σ : State) : Addr := (arg σ 3).setWidth 64

theorem VP₀.hp {σ₁ σ₂ : State} (h : VP₀ σ₁ σ₂) : bsV σ₁ = bsV σ₂ ∧ σ₁.gpr .esp = σ₂.gpr .esp :=
  ⟨by simp only [bsV, h.2.2.2.2.2.2.1], h.2.2.1⟩

theorem VP₀.arg {σ₁ σ₂ : State} (h : VP₀ σ₁ σ₂) {i : Nat} (hi : i < 4) : arg σ₁ i = arg σ₂ i := by
  obtain ⟨_, _, _, a0, a1, a2, a3, _⟩ := h
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  exacts [a0, a1, a2, a3]

/-- What the blocks between the calls need public: `esp` and `edi`. -/
theorem FS.agree {σ₁ σ₂ s₁ s₂ : State} (hP : VP₀ σ₁ σ₂) (h₁ : FS bsV σ₁ s₁) (h₂ : FS bsV σ₂ s₂) :
    VG.X86.Taint.Agree (τr [.esp, .edi]) s₁ s₂ := RF.agree (FS.rf hP.hp.1 hP.hp.2 h₁ h₂)

/-! ## Field programs and the square root -/

theorem root_rel (base : Addr) : RelCT isa (RF base) root (RF base) := by
  have h : RelCT isa (RF base) _ (RF base) :=
    (ops_rel [.copy 14 12]).seq <|
    (sqn_rel base 14 (n := 1) (by decide) (by decide)).seq <|
    (ops_rel [.mul 14 14 12, .copy 15 14]).seq <|
    (sqn_rel base 15 (n := 2) (by decide) (by decide)).seq <|
    (ops_rel [.mul 15 15 14, .copy 16 15]).seq <|
    (sqn_rel base 16 (n := 4) (by decide) (by decide)).seq <|
    (ops_rel [.mul 16 16 15, .copy 17 16]).seq <|
    (sqn_rel base 17 (n := 8) (by decide) (by decide)).seq <|
    (ops_rel [.mul 17 17 16, .copy 18 17]).seq <|
    (sqn_rel base 18 (n := 16) (by decide) (by decide)).seq <|
    (ops_rel [.mul 18 18 17, .copy 19 18]).seq <|
    (sqn_rel base 19 (n := 32) (by decide) (by decide)).seq <|
    (ops_rel [.mul 19 19 18, .copy 20 19]).seq <|
    (sqn_rel base 20 (n := 64) (by decide) (by decide)).seq <|
    (ops_rel [.mul 20 20 19]).seq <|
    (sqn_rel base 20 (n := 64) (by decide) (by decide)).seq <|
    (ops_rel [.mul 20 20 19]).seq <|
    (sqn_rel base 20 (n := 16) (by decide) (by decide)).seq <|
    (ops_rel [.mul 20 20 17]).seq <|
    (sqn_rel base 20 (n := 8) (by decide) (by decide)).seq <|
    (ops_rel [.mul 20 20 16]).seq <|
    (sqn_rel base 20 (n := 4) (by decide) (by decide)).seq <|
    (ops_rel [.mul 20 20 15]).seq <|
    (sqn_rel base 20 (n := 2) (by decide) (by decide)).seq <|
    (ops_rel [.mul 20 20 14, .copy 21 20]).seq <|
    (sqn_rel base 21 (n := 1) (by decide) (by decide)).seq <|
    (ops_rel [.mul 21 21 12]).seq <|
    (sqn_rel base 21 (n := 223) (by decide) (by decide)).seq <|
    (ops_rel [.mul 21 21 20])
  exact h

/-- A field program, keeping a predicate field programs keep. -/
theorem field_gen {P : State → State → Prop} (hF : ∀ σ s, P σ s → FS bsV σ s)
    (hK : ∀ σ s t, P σ s → Keep (bsV σ) s t → BoundedEnv t.mem (bsV σ) → P σ t)
    (l : List Impl.Ed448.FOp) (hv : ∀ op ∈ l, fopValid op) :
    RelCT isa (Runs VP₀ P) (field l) (Runs VP₀ P) := by
  refine Runs.step (R := fun _ _ => True) ?_ fun σ s h =>
    WP.mono (field_ok l hv (hF _ _ h).1.scr (hF _ _ h).1.ctx (hF _ _ h).1.bounded) fun t ⟨k, b, _⟩ =>
      hK σ s t h k b
  rw [field_ops l hv]
  exact ops_tr (fun _ _ h => h.hp) hF _

theorem FS.keep {σ s t : State} (h : FS bsV σ s) (k : Keep (bsV σ) s t) (b : BoundedEnv t.mem (bsV σ)) :
    FS bsV σ t := ⟨⟨k.scr h.1.scr, k.ctx h.1.ctx, b⟩, (k.regs.1 _ (by decide)).trans h.2⟩

/-- A field program, from `FS` to `FS`. -/
theorem field_FS (l : List Impl.Ed448.FOp) (hv : ∀ op ∈ l, fopValid op) :
    RelCT isa (Runs VP₀ (FS bsV)) (field l) (Runs VP₀ (FS bsV)) :=
  field_gen (fun _ _ h => h) (fun _ _ _ h k b => FS.keep h k b) l hv

theorem root_FS : RelCT isa (Runs VP₀ (FS bsV)) root (Runs VP₀ (FS bsV)) :=
  Runs.step (rf_tr (fun _ _ h => h.hp) (fun _ _ h => h) root_rel) fun σ s h =>
    WP.mono (root_ok h.1.scr h.1.ctx h.1.bounded) fun t ⟨k, b, _⟩ =>
      ⟨⟨k.scr h.1.scr, k.ctx h.1.ctx, b⟩, (k.regs.1 _ (by decide)).trans h.2⟩

/-- The comparison of slots 12 and 13, from `FS` to `FS`. -/
theorem eqSlots_FS :
    RelCT isa (Runs VP₀ (FS bsV)) (.block (Impl.Ed448.X86.eqSlots (slot 12) (slot 13)))
      (Runs VP₀ (FS bsV)) :=
  Runs.step (RelCT.taint (A := taint) (τr [.esp, .edi])
    (fun _ _ ⟨_, _, hP, f₁, f₂⟩ => FS.agree hP f₁ f₂) (by taint_decide)) fun σ s h =>
    WP.mono (eqSlots_ok h.1.scr h.1.bounded 12 13 (by decide) (by decide) (by decide)) fun t ⟨k, bt, _⟩ =>
      ⟨⟨k.scr h.1.scr, k.ctx h.1.ctx, bt⟩, (k.regs.1 _ (by decide)).trans h.2⟩

/-! ## The entry -/

/-- The taint analysis starts with the stack arguments public, and the word
holding `scratch` known to be the base address of the writable region. -/
def verifyTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [8192], argLen := 20, argBases := [(16, 0)] }

theorem verifyTaint_wf {s : State} (h : verifyEquationLocal.pre s) : VG.X86.Taint.Wf verifyTaint s := by
  have hp := VerifyPre.of h
  have hf := hp.f3; have spfit := hp.sp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, verifyTaint], by simp [hp.wr], ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [verifyTaint]; omega, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl; simp only [BitVec.toNat_setWidth]; omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl
    exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_sc hp.args_sc
  · intro p hp'
    simp only [verifyTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    subst hp'
    exact ⟨by simp [verifyTaint], by simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]⟩

theorem verifyTaint_agree {s t : State} (hs : verifyEquationLocal.pre s) (ht : verifyEquationLocal.pre t)
    (hp : verifyEquationLocal.pub s t) : VG.X86.Taint.Agree verifyTaint s t := by
  obtain ⟨hsp, a0, a1, a2, a3, _⟩ := hp
  have ps := VerifyPre.of hs
  have pt := VerifyPre.of ht
  have ha : ∀ i < 4, arg s i = arg t i := fun i hi => by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    exacts [a0, a1, a2, a3]
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, verifyTaint_wf hs, verifyTaint_wf ht,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hsp,
    fun k h4 hk => ?_⟩
  · simp only [verifyTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hsp
  · rw [ps.wr, pt.wr, a3]
  · simp only [verifyTaint] at hk
    have fs := ps.sp_fit
    have ft := pt.sp_fit
    rw [show VG.X86.Taint.depth verifyTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by omega) h4 hk, VG.X86.Taint.argByte_eq (by omega) h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (ha ((k - 4) / 4) (by omega))

/-- `S` and `k`, from the entry state. -/
abbrev SV (σ : State) : Nat :=
  Spec.Ed448.decodeLE (Spec.Ed448.bytesAt σ.mem ((arg σ 1).setWidth 64 + BitVec.ofNat 64 57) 57)
abbrev KV (σ : State) : Nat := Spec.Ed448.decodeLE (Spec.Ed448.bytesAt σ.mem ((arg σ 2).setWidth 64) 57)

/-- The bits of `S` and `k` in the working space. -/
def BitsAt (σ s : State) : Prop :=
  ∀ j < 456, s.mem (off (bsV σ) (Impl.X448.X86.BITS + j)) = BitVec.ofNat 8 (pair2 (SV σ) (KV σ) j)

/-- After the entry block. -/
structure VE (σ s₁ : State) : Prop where
  pre : VerifyPre σ
  lp : LoopPre σ s₁
  sp : s₁.gpr .esp = σ.gpr .esp
  out : Outside (bsV σ) 0 8192 σ.mem s₁.mem
  bits : BitsAt σ s₁
  e : ∀ i : Index, E s₁.mem (bsV σ) i = Proof.X448.toFe (Impl.Ed448.X86.initVal i.val)

theorem ventry_VE {σ : State} (h : VerifyPre σ) : WP isa (.block ventry) σ (VE σ) :=
  WP.mono (WP.and (ventry_loopPre h) (ventry_ok h rfl)) fun _ ⟨lp, _, _, o, k, _, bits, _, e⟩ =>
    ⟨h, lp, k.1 _ (by decide), o, bits, e⟩

/-- `FE` from the entry, for a state the decoding has reached. -/
theorem VE.fe {σ s₁ t : State} (h : VE σ s₁) (ht : Scr t (bsV σ)) (hb : BoundedEnv t.mem (bsV σ))
    {rs : List Reg} (hk : Keeps rs s₁ t) (hesp : .esp ∉ rs) (hx : XF (bsV σ) s₁ s₁.mem t.mem) :
    FE bsV σ t := by
  have sp : t.gpr .esp = σ.gpr .esp := (hk.1 _ hesp).trans h.sp
  have hw : σ.wr = [⟨bsV σ, 8192⟩] := h.pre.wr
  refine ⟨⟨ht, h.lp.ctx.keep (hk.1 _ hesp), hb⟩, sp, hk.2.2.trans (h.lp.wr.trans hw.symm), ?_⟩
  have st : callStk s₁ = below (σ.gpr .esp) 20 := by simp only [callStk, h.sp]
  have f1 : Frame (σ.wr ++ [below (σ.gpr .esp) 20]) σ.mem s₁.mem :=
    (Outside.frame h.out).mono fun r hr => by rw [List.mem_singleton.mp hr, hw]; exact List.mem_cons_self
  refine f1.trans (hx.mono fun r hr => ?_)
  rw [hw, ← st]
  simpa using hr

theorem VE.fe₁ {σ s₁ : State} (h : VE σ s₁) : FE bsV σ s₁ :=
  h.fe h.lp.scr h.lp.bounded (Keeps.refl [] _) (by decide) (Frame.refl _ _)

/-! ## The decoding loop -/

/-- Before the decoding `2 - n` of the loop, from the entry state. -/
def LoopAt (σ : State) (n : Nat) (x : State) : Prop :=
  ∃ s₁, VE σ s₁ ∧ DecInv (bsV σ) s₁ (arg σ 1) (arg σ 0) n x

theorem LoopAt.fe {σ x : State} {n : Nat} (h : LoopAt σ n x) : FE bsV σ x :=
  let ⟨_, e, d⟩ := h; e.fe (d.scr e.lp.scr) d.bounded d.keeps (by decide) d.ext

/-- After an iteration's first block. -/
def MidAt (σ : State) (n : Nat) (u : State) : Prop :=
  1 ≤ n ∧ ∃ s₁ t, VE σ s₁ ∧ DecInv (bsV σ) s₁ (arg σ 1) (arg σ 0) n t ∧ AFacts (bsV σ) t u

theorem MidAt.fe {σ u : State} {n : Nat} (h : MidAt σ n u) : FE bsV σ u := by
  obtain ⟨_, s₁, t, e, d, a⟩ := h
  have kt := d.keeps.trans a.2.1
  exact e.fe ((d.scr e.lp.scr).of_keeps a.2.1 (by decide)) (BoundedEnv.out a.2.2.1 (by decide) d.bounded)
    kt (by decide) (d.ext.trans (XF.of_out a.2.2.1 (by decide)))

/-- The pointer to the point an iteration decodes. -/
theorem MidAt.esi {σ u : State} {n : Nat} (h : MidAt σ n u) :
    u.gpr .esi = if n = 2 then arg σ 1 else arg σ 0 :=
  let ⟨hn, _, _, _, d, a⟩ := h; a.1.trans (d.ptr hn)

/-- The decoding of the point at `esi`, keeping `FE`. -/
theorem decode_FE (hR : RecoverOk) {σ u : State} {n : Nat} (h : MidAt σ n u) :
    WP isa (decode 6 7) u (FE bsV σ) := by
  have fe := h.fe
  obtain ⟨hn, s₁, t, e, ht, ⟨ae, ak, ao, _, _⟩⟩ := h
  have kt := ht.keeps.trans ak
  have Eu : ∀ i : Index, E u.mem (bsV σ) i = E t.mem (bsV σ) i := fun i =>
    E_out ao i (Or.inl (by have := slot_range i; simp only [RX]; omega))
  have h10u : E u.mem (bsV σ) 10 = 1 := by rw [Eu, ht.other 10 (by decide) (by decide) (by decide), e.lp.e10]
  have h11u : E u.mem (bsV σ) 11 = Spec.Ed448.d := by
    rw [Eu, ht.other 11 (by decide) (by decide) (by decide), e.lp.e11]
  have hp : u.gpr .esi = (if n = 2 then arg σ 1 else arg σ 0) := ae.trans (ht.ptr hn)
  have hin : Input u (bsV σ) (if n = 2 then arg σ 1 else arg σ 0) 57 := by
    split
    · exact e.lp.isig.of_keeps kt
    · exact e.lp.ipk.of_keeps kt
  refine WP.mono (fe.wp (NoSp.of_all (by decide +kernel)) (by decide +kernel) (Q := fun _ => True)
    (WP.mono (decode_ok hR fe.fin.scr fe.fin.ctx fe.fin.bounded hp hin.fit hin.read hin.far 6 7
      (Or.inl ⟨rfl, rfl⟩) h10u h11u) fun w ⟨k, b, _⟩ =>
      ⟨⟨k.scr fe.fin.scr, k.ctx fe.fin.ctx, b⟩, k.regs.1 _ (by decide), k.regs.2.2, trivial⟩))
    fun w ⟨f, _⟩ => f

/-- The decoding's trace. -/
theorem decode_tr (n : Nat) : RelCT isa (Runs VP₀ (MidAt · n ·)) (decode 6 7) fun _ _ => True := by
  unfold decode
  refine RelCT.seq (Runs.step (G := FS bsV) (RelCT.taint (A := taint) (τr [.esp, .esi, .edi]) ?_
    (by taint_decide)) ?_) ?_
  · rintro s₁ s₂ ⟨σ₁, σ₂, hP, m₁, m₂⟩
    refine agree_regs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact m₁.fe.sp.trans (hP.hp.2.trans m₂.fe.sp.symm)
    · rw [m₁.esi, m₂.esi, hP.arg (by decide : 1 < 4), hP.arg (by decide : 0 < 4)]
    · exact edi_eq m₁.fe.fin.scr (hP.hp.1 ▸ m₂.fe.fin.scr)
  · intro σ u h
    have fe := h.fe
    obtain ⟨hn, s₁, t, e, ht, ⟨ae, ak, _, _, _⟩⟩ := h
    have kt := ht.keeps.trans ak
    have hp : u.gpr .esi = (if n = 2 then arg σ 1 else arg σ 0) := ae.trans (ht.ptr hn)
    have hin : Input u (bsV σ) (if n = 2 then arg σ 1 else arg σ 0) 57 := by
      split
      · exact e.lp.isig.of_keeps kt
      · exact e.lp.ipk.of_keeps kt
    exact WP.mono (decodeY_ok fe.fin.scr fe.fin.bounded hp hin.fit hin.read hin.far 7 (by decide))
      fun w ⟨k, b, _⟩ => ⟨⟨k.scr fe.fin.scr, k.ctx fe.fin.ctx, b⟩, (k.regs.1 _ (by decide)).trans fe.sp⟩
  refine (field_FS _ (by decide)).seq (root_FS.seq ((field_FS _ (by decide)).seq
    (eqSlots_FS.seq ((field_FS _ (by decide)).seq ?_))))
  exact RelCT.taint (A := taint) (τr [.esp, .edi]) (fun _ _ ⟨_, _, hP, f₁, f₂⟩ => FS.agree hP f₁ f₂)
    (by taint_decide)

/-- What the blocks reading the arguments need public. -/
theorem FE.agreeV {σ₁ σ₂ s₁ s₂ : State} (hP : VP₀ σ₁ σ₂) (f₁ : FE bsV σ₁ s₁) (f₂ : FE bsV σ₂ s₂) :
    VG.X86.Taint.Agree (τa 20) s₁ s₂ := by
  have p₁ := VerifyPre.of hP.1
  have p₂ := VerifyPre.of hP.2.1
  have a := verifyTaint_agree hP.1 hP.2.1 hP.2.2
  have wr : ∀ {σ : State}, VerifyPre σ → ∀ r ∈ σ.wr, Region.Disjoint ⟨(σ.gpr .esp).setWidth 64, 20⟩ r := by
    intro σ p r hr
    have := p.sp_fit
    rw [p.wr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) p.ret_sc p.args_sc
  have ad : ∀ {σ : State}, VerifyPre σ → ∀ r ∈ σ.wr ++ [below (σ.gpr .esp) 20],
      (⟨argAddr σ 0, 20 - 4⟩ : Region).Disjoint r := by
    intro σ p r hr
    rw [p.wr, ← stkR_below p.sp_room] at hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact p.args_sc
    · exact p.stk_args.symm
  exact f₁.agreeA f₂ hP.hp.1 hP.hp.2 p₁.sp_fit p₂.sp_fit (wr p₁) (wr p₂) (ad p₁) (ad p₂)
    fun k h4 hk => by
      have := a.argMem k h4 hk
      simpa only [verifyTaint, VG.X86.Taint.depth, Nat.zero_add] using this

/-- An iteration of the decoding loop. -/
theorem vdecodeBody_rel (hR : RecoverOk) (n : Nat) :
    RelCT isa (Runs VP₀ fun σ x => 1 ≤ n ∧ LoopAt σ n x) vdecodeBody fun x y =>
      isa.eval .ne x = isa.eval .ne y ∧ (isa.eval .ne x = some false → Runs VP₀ (LoopAt · 0 ·) x y) ∧
        (isa.eval .ne x = some true → ∃ m < n, Runs VP₀ (fun σ x => 1 ≤ m ∧ LoopAt σ m x) x y) := by
  have tr : RelCT isa (Runs VP₀ fun σ x => 1 ≤ n ∧ LoopAt σ n x) vdecodeBody fun _ _ => True := by
    unfold vdecodeBody
    refine RelCT.seq (Runs.step (G := (MidAt · n ·)) (RelCT.taint (A := taint) (τr [.esp, .edi])
      (fun _ _ ⟨_, _, hP, ⟨_, f₁⟩, ⟨_, f₂⟩⟩ => FS.agree hP f₁.fe.fs f₂.fe.fs) (by taint_decide)) ?_)
      (RelCT.seq (Runs.step (G := FE bsV) (decode_tr n) fun σ u h => decode_FE hR h) ?_)
    · rintro σ x ⟨hn, s₁, e, d⟩
      exact WP.mono (vbodyA_ok (d.scr e.lp.scr)) fun u hu => ⟨hn, s₁, x, e, d, hu⟩
    · exact RelCT.taint (A := taint) (τa 20) (fun _ _ ⟨_, _, hP, f₁, f₂⟩ => FE.agreeV hP f₁ f₂)
        (by taint_decide)
  refine Runs.then (G := fun σ v => LoopAt σ (n - 1) v ∧ v.zf = some (decide (n - 1 = 0)))
    (fun _ _ h => h) tr ?_ ?_
  · rintro σ x ⟨hn, s₁, e, d⟩
    exact WP.mono (vdecodeStep_ok hR e.lp.scr e.lp.ctx e.lp.wr e.lp.pk e.lp.isig e.lp.ipk e.lp.dsig
      e.lp.dpk e.lp.e10 e.lp.e11 hn d) fun v ⟨dv, zv⟩ => ⟨⟨s₁, e, dv⟩, zv⟩
  · rintro σ₁ σ₂ t₁ t₂ hP - ⟨l₁, z₁⟩ ⟨l₂, z₂⟩
    rw [eval_ne z₁, eval_ne z₂]
    refine ⟨rfl, fun hz => ?_, fun hz => ?_⟩
    · have h0 : n - 1 = 0 := by simpa using hz
      rw [h0] at l₁ l₂
      exact ⟨σ₁, σ₂, hP, l₁, l₂⟩
    · have h0 : n - 1 ≠ 0 := by simpa using hz
      exact ⟨n - 1, by omega, σ₁, σ₂, hP, ⟨by omega, l₁⟩, ⟨by omega, l₂⟩⟩


/-! ## After the decodings -/

/-- `-A` computed, and `Q`'s `Y` set to 1. -/
def V4 (σ s₄ : State) : Prop :=
  ∃ s₂ s₃, LoopAt σ 0 s₂ ∧ Keep (bsV σ) s₂ s₃ ∧ E s₃.mem (bsV σ) = evalOps [.sub 6 0 6] (E s₂.mem (bsV σ)) ∧
    Keep (bsV σ) s₃ s₄ ∧ BoundedEnv s₄.mem (bsV σ) ∧
    E s₄.mem (bsV σ) = applyOps [.copy 1 10] (E s₃.mem (bsV σ)) ∧ FE bsV σ s₄

/-- The point `-A`. -/
abbrev AV (s₄ : State) (σ : State) : Spec.Ed448.Point := pt (E s₄.mem (bsV σ)) 6 7 10

/-- In the loop over the bits, `n + 1` iterations left. -/
def VI (n : Nat) (σ s : State) : Prop :=
  n < 456 ∧ ∃ s₄, V4 σ s₄ ∧ VInv (bsV σ) (SV σ) (KV σ) (AV s₄ σ) s₄ s (n + 1) ∧ FE bsV σ s

theorem V4.bits {σ s₄ : State} (h : V4 σ s₄) : BitsAt σ s₄ := by
  obtain ⟨s₂, s₃, ⟨s₁, e, d⟩, k₃, -, k₄, -⟩ := h
  intro j hj
  rw [bits_kept (WsOut2.widen k₄.2) j hj, bits_kept (WsOut2.widen k₃.2) j hj, bits_keptD d.frame j hj]
  exact e.bits j hj

theorem V4.start {σ s₄ : State} (h : V4 σ s₄) :
    ∀ s', s'.gpr .esi = BitVec.ofNat 32 456 → (∀ r, r ≠ .esi → s'.gpr r = s₄.gpr r) →
      s'.mem = s₄.mem → s'.rd = s₄.rd → s'.wr = s₄.wr →
      VInv (bsV σ) (SV σ) (KV σ) (AV s₄ σ) s₄ s' 456 := by
  obtain ⟨s₂, s₃, ⟨s₁, e, d⟩, k₃, e₃, k₄, b₄, e₄, fe⟩ := h
  obtain ⟨er, eq, ed⟩ := initE _ e.e
  have e₂ := d.other
  obtain ⟨_, k₃e⟩ := sub6_E (E s₂.mem (bsV σ))
  rw [← e₃] at k₃e
  have e₄1 : E s₄.mem (bsV σ) 1 = E s₃.mem (bsV σ) 10 := by
    rw [e₄]; simp only [applyOps, FieldOp.apply, opCopy, Function.update_self]
  have e₄k : ∀ i : Index, i ≠ 1 → E s₄.mem (bsV σ) i = E s₃.mem (bsV σ) i := fun i hi => by
    rw [e₄]; exact Function.update_of_ne hi _ _
  have k41 : ∀ i : Index, i.val = 0 ∨ i.val = 2 ∨ (8 ≤ i.val ∧ i.val ≤ 11) →
      E s₄.mem (bsV σ) i = E s₁.mem (bsV σ) i := fun i hi => by
    rw [e₄k i (fun h => by subst h; omega), k₃e i (fun h => by subst h; omega),
      e₂ i (fun h => by subst h; omega) (fun h => by subst h; omega) (by omega)]
  intro s' h1 h2 h3 h4 h5
  have k' : Keeps (.esi :: workRegs) s₄ s' :=
    ⟨fun r hr => h2 r (fun e => hr (by subst r; exact List.mem_cons_self)), h4, h5⟩
  refine ⟨fe.fin.scr.of_keeps k' (by decide), fe.fin.ctx.keep (h2 _ (by decide)), h3 ▸ b₄, k', h1,
    h3 ▸ WsOut2.refl _ _ _ _ _ _, ?_, ?_, ?_, ?_⟩
  · rw [h3, Nat.sub_self]
    show (⟨E s₄.mem (bsV σ) 0, E s₄.mem (bsV σ) 1, E s₄.mem (bsV σ) 2⟩ : Spec.Ed448.Point) =
      Spec.Ed448.identity
    rw [k41 0 (Or.inl rfl), k41 2 (Or.inr (Or.inl rfl)), e₄1, k₃e 10 (by decide),
      e₂ 10 (by decide) (by decide) (by decide), e.lp.e10]
    rw [show E s₁.mem (bsV σ) 0 = Spec.Ed448.identity.X from congrArg Spec.Ed448.Point.X er,
      show E s₁.mem (bsV σ) 2 = Spec.Ed448.identity.Z from congrArg Spec.Ed448.Point.Z er]
    rfl
  · rw [h3, pt_congr' (k41 8 (by decide)) (k41 9 (by decide)) (k41 10 (by decide))]; exact eq
  · rw [h3]
  · rw [h3, k41 11 (by decide)]; exact ed

/-- Within an iteration: `FS`, the counter, and the bits. -/
def StepV (n : Nat) (σ t : State) : Prop :=
  FS bsV σ t ∧ t.gpr .esi = BitVec.ofNat 32 n ∧ BitsAt σ t ∧ n < 456

theorem StepV.keep {n : Nat} {σ s t : State} (h : StepV n σ s) (k : Keep (bsV σ) s t)
    (b : BoundedEnv t.mem (bsV σ)) : StepV n σ t :=
  ⟨FS.keep h.1 k b, (k.regs.1 _ (by decide)).trans h.2.1, fun j hj => by
    rw [bits_kept (WsOut2.widen k.2) j hj]; exact h.2.2.1 j hj, h.2.2.2⟩

theorem StepV.agree {n : Nat} {s₁ s₂ : State} (h : Runs VP₀ (StepV n) s₁ s₂) :
    VG.X86.Taint.Agree (τr [.esp, .esi, .edi]) s₁ s₂ := by
  obtain ⟨σ₁, σ₂, hP, f₁, f₂⟩ := h
  refine agree_regs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact f₁.1.2.trans (hP.hp.2.trans f₂.1.2.symm)
  · exact f₁.2.1.trans f₂.2.1.symm
  · exact edi_eq f₁.1.1.scr (hP.hp.1 ▸ f₂.1.1.scr)

theorem vmaskSwap_rel (n : Nat) (hi : Bool) :
    RelCT isa (Runs VP₀ (StepV n)) (.block (Impl.Ed448.X86.vmask hi ++ Impl.Ed448.X86.swapT))
      (Runs VP₀ (StepV n)) := by
  have ag : ∀ s₁ s₂, Runs VP₀ (StepV n) s₁ s₂ → VG.X86.Taint.Agree (τr [.esp, .esi, .edi]) s₁ s₂ := by
    rintro s₁ s₂ ⟨σ₁, σ₂, hP, f₁, f₂⟩
    refine agree_regs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact f₁.1.2.trans (hP.hp.2.trans f₂.1.2.symm)
    · exact f₁.2.1.trans f₂.2.1.symm
    · exact edi_eq f₁.1.1.scr (hP.hp.1 ▸ f₂.1.1.scr)
  refine Runs.step (R := fun _ _ => True) ?_ fun σ s h => ?_
  · cases hi
    · exact RelCT.taint (A := taint) (τr [.esp, .esi, .edi]) ag (by taint_decide)
    · exact RelCT.taint (A := taint) (τr [.esp, .esi, .edi]) ag (by taint_decide)
  · exact WP.mono (vmaskSwap_ok h.1.1.scr h.1.1.bounded h.2.2.2 h.2.1 (bit_lt' (SV σ) n) (bit_lt' (KV σ) n)
      (h.2.2.1 n h.2.2.2) hi) fun t ⟨k, b, _⟩ => h.keep k b


theorem fieldV (n : Nat) (l : List Impl.Ed448.FOp) (hv : ∀ op ∈ l, fopValid op) :
    RelCT isa (Runs VP₀ (StepV n)) (field l) (Runs VP₀ (StepV n)) :=
  field_gen (fun _ _ h => h.1) (fun _ _ _ h k b => h.keep k b) l hv

theorem vstep_tr (n : Nat) : RelCT isa (Runs VP₀ (VI n)) Impl.Ed448.X86.vstep fun _ _ => True := by
  unfold Impl.Ed448.X86.vstep
  refine RelCT.seq (Runs.step (G := StepV n) (RelCT.taint (A := taint) (τr [])
      (fun _ _ _ => agree_regs fun _ h => (List.not_mem_nil h).elim) (by taint_decide)) ?_)
    ((fieldV n _ (by decide)).seq ((fieldV n _ (by decide)).seq ((vmaskSwap_rel n false).seq
      ((fieldV n _ (by decide)).seq ?_))))
  · rintro σ s ⟨hn, s₄, v, L, fe⟩
    refine WP.mono (decCounter_ok (by omega) L.esi) fun t ⟨c, g, m, r, w, _⟩ =>
      ⟨⟨FInv.of_counter fe.fin g m r w, (g _ (by decide)).trans fe.sp⟩, c, fun j hj => ?_, hn⟩
    rw [m, L.mem _ (by rw [ofs_off' _ (by simp only [Impl.X448.X86.BITS]; omega)]; simp only [Impl.X448.X86.BITS]; omega)
      (by rw [ofs_off' _ (by simp only [Impl.X448.X86.BITS]; omega)]; simp only [Impl.X448.X86.BITS]; omega)
      (by rw [ofs_off' _ (by simp only [Impl.X448.X86.BITS]; omega)]; simp only [Impl.X448.X86.BITS, Impl.X448.X86.ACC]; omega)]
    exact v.bits j hj
  · exact RelCT.taint (A := taint) (τr [.esp, .esi, .edi]) (fun _ _ h => StepV.agree h) (by taint_decide)


/-- After the loop over the bits. -/
def V5 (σ s : State) : Prop :=
  ∃ s₄, V4 σ s₄ ∧ VInv (bsV σ) (SV σ) (KV σ) (AV s₄ σ) s₄ s 0 ∧ FE bsV σ s

theorem VInv.fs {σ s₄ s t : State} {n m : Nat} {A : Spec.Ed448.Point}
    (hs : VInv (bsV σ) (SV σ) (KV σ) A s₄ s n) (ht : VInv (bsV σ) (SV σ) (KV σ) A s₄ t m) :
    FInv (bsV σ) t ∧ t.gpr .esp = s.gpr .esp ∧ t.wr = s.wr :=
  ⟨⟨ht.scr, ht.ctx, ht.bounded⟩, (ht.regs.1 _ (by decide)).trans (hs.regs.1 _ (by decide)).symm,
    ht.regs.2.2.trans hs.regs.2.2.symm⟩

theorem vloop_rel : RelCT isa (Runs VP₀ V4) Impl.Ed448.X86.vloop (Runs VP₀ V5) := by
  unfold Impl.Ed448.X86.vloop
  refine RelCT.seq (Runs.step (G := VI 455) (RelCT.taint (A := taint) (τr [])
    (fun _ _ _ => agree_regs fun _ h => (List.not_mem_nil h).elim) (by taint_decide)) ?_) ?_
  · intro σ s v
    have fe : FE bsV σ s := by obtain ⟨_, _, _, _, _, _, _, _, fe⟩ := v; exact fe
    refine WP.mono (setCounter_ok s 456 (by decide)) fun t ⟨h1, h2, h3, h4, h5⟩ =>
      ⟨by decide, s, v, v.start t h1 h2 h3 h4 h5, ?_⟩
    exact ⟨FInv.of_counter fe.fin h2 h3 h4 h5, (h2 _ (by decide)).trans fe.sp, h5.trans fe.wr,
      by rw [h3]; exact fe.frame⟩
  refine RelCT.loop (M := isa) (fun n => Runs VP₀ (VI n)) (fun n => ?_) 455
  refine Runs.then (G := fun σ t => (n < 456 ∧ ∃ s₄, V4 σ s₄ ∧
      VInv (bsV σ) (SV σ) (KV σ) (AV s₄ σ) s₄ t n ∧ FE bsV σ t) ∧ t.zf = some (decide (n = 0)))
    (fun _ _ h => h) (vstep_tr n) ?_ ?_
  · rintro σ s ⟨hn, s₄, v, L, fe⟩
    exact WP.mono (fe.wp (NoSp.of_all (by decide +kernel)) (by decide +kernel)
      (Q := fun t => VInv (bsV σ) (SV σ) (KV σ) (AV s₄ σ) s₄ t n ∧ t.zf = some (decide (n = 0)))
      (WP.mono (vstep_ok hn v.bits L) fun t ⟨l, z⟩ =>
        ⟨(VInv.fs L l).1, (VInv.fs L l).2.1, (VInv.fs L l).2.2, l, z⟩))
      fun t ⟨f, l, z⟩ => ⟨⟨hn, s₄, v, l, f⟩, z⟩
  · rintro σ₁ σ₂ t₁ t₂ hP - ⟨l₁, z₁⟩ ⟨l₂, z₂⟩
    rw [eval_ne z₁, eval_ne z₂]
    refine ⟨rfl, fun hz => ⟨σ₁, σ₂, hP, ?_, ?_⟩, fun hz => ?_⟩
    · have : n = 0 := by simpa using hz
      subst this; exact l₁.2
    · have : n = 0 := by simpa using hz
      subst this; exact l₂.2
    · have hn0 : n ≠ 0 := fun h0 => by simp [h0] at hz
      obtain ⟨hn, a₁, v₁, L₁, f₁⟩ := l₁
      obtain ⟨-, a₂, v₂, L₂, f₂⟩ := l₂
      have e : n - 1 + 1 = n := by omega
      exact ⟨n - 1, by omega, σ₁, σ₂, hP, ⟨by omega, a₁, v₁, e ▸ L₁, f₁⟩, ⟨by omega, a₂, v₂, e ▸ L₂, f₂⟩⟩


/-! ## The whole function -/

theorem field_tr {F : State → State → Prop} (hF : ∀ σ s, F σ s → FS bsV σ s) (l : List Impl.Ed448.FOp)
    (hv : ∀ op ∈ l, fopValid op) : RelCT isa (Runs VP₀ F) (field l) fun _ _ => True := by
  rw [field_ops l hv]
  exact ops_tr (fun _ _ h => h.hp) hF _

/-- After `-A`. -/
def V3 (σ s₃ : State) : Prop := ∃ s₂, LoopAt σ 0 s₂ ∧ Keep (bsV σ) s₂ s₃ ∧
  E s₃.mem (bsV σ) = evalOps [.sub 6 0 6] (E s₂.mem (bsV σ)) ∧ FE bsV σ s₃

theorem V3.fe {σ s : State} (h : V3 σ s) : FE bsV σ s := by obtain ⟨_, _, _, _, fe⟩ := h; exact fe

theorem negA_rel : RelCT isa (Runs VP₀ (LoopAt · 0 ·)) (field [.sub 6 0 6]) (Runs VP₀ V3) := by
  refine Runs.step (field_tr (fun _ _ h => h.fe.fs) _ (by decide)) ?_
  intro σ s h
  have fe := h.fe
  exact WP.mono (fe.wp (NoSp.of_all (by decide +kernel)) (by decide +kernel)
    (Q := fun t => Keep (bsV σ) s t ∧ E t.mem (bsV σ) = evalOps [.sub 6 0 6] (E s.mem (bsV σ)))
    (WP.mono (field_ok _ (by decide) fe.fin.scr fe.fin.ctx fe.fin.bounded) fun t ⟨k, b, e⟩ =>
      ⟨⟨k.scr fe.fin.scr, k.ctx fe.fin.ctx, b⟩, k.regs.1 _ (by decide), k.regs.2.2, k, e⟩))
    fun t ⟨f, k, e⟩ => ⟨s, h, k, e, f⟩

theorem copy1_rel : RelCT isa (Runs VP₀ V3) (Impl.X448.X86.ops [.copy Impl.X448.X86.X2 (slot 10)])
    (Runs VP₀ V4) := by
  rw [show Impl.X448.X86.ops [.copy Impl.X448.X86.X2 (slot 10)] =
    Impl.X448.X86.ops (([.copy 1 10] : List FieldOp).map FieldOp.impl) from rfl]
  refine Runs.step (ops_tr (fun _ _ h => h.hp) (fun _ _ h => h.fe.fs) _) ?_
  rintro σ s ⟨s₂, l, k₃, e₃, fe⟩
  exact WP.mono (ops_FE fe [.copy 1 10]) fun t ⟨f, k, e⟩ => ⟨s₂, s, l, k₃, e₃, k, f.fin.bounded, e, f⟩

/-- Before `R` is copied back. -/
def V6 (σ s₆ : State) : Prop := ∃ s₅, V5 σ s₅ ∧ Keep (bsV σ) s₅ s₆ ∧ FE bsV σ s₆

theorem V6.r {σ s₆ : State} (h : V6 σ s₆) :
    Bounded s₆.mem (bsV σ) RX ∧ Bounded s₆.mem (bsV σ) RY := by
  obtain ⟨s₅, ⟨s₄, ⟨s₂, s₃, ⟨s₁, e, d⟩, k₃, -, k₄, -⟩, L, -⟩, k₆, -⟩ := h
  obtain ⟨bx, by'⟩ := d.rBnd rfl
  have g : ∀ o, o = RX ∨ o = RY → Bounded s₂.mem (bsV σ) o → Bounded s₆.mem (bsV σ) o := fun o ho b =>
    (F_high k₆.2 (by decide) ho).2 ((F_high L.mem (by decide) ho).2
      ((F_high k₄.2 (by decide) ho).2 ((F_high k₃.2 (by decide) ho).2 b)))
  exact ⟨g _ (Or.inl rfl) bx, g _ (Or.inr rfl) by'⟩

theorem copy6_rel : RelCT isa (Runs VP₀ V5) (Impl.X448.X86.ops [.copy (slot 6) Impl.X448.X86.X2])
    (Runs VP₀ V6) := by
  rw [show Impl.X448.X86.ops [.copy (slot 6) Impl.X448.X86.X2] =
    Impl.X448.X86.ops (([.copy 6 1] : List FieldOp).map FieldOp.impl) from rfl]
  refine Runs.step (ops_tr (fun _ _ h => h.hp)
    (fun _ _ h => by obtain ⟨_, _, _, fe⟩ := h; exact fe.fs) _) ?_
  intro σ s h
  have fe : FE bsV σ s := by obtain ⟨_, _, _, fe⟩ := h; exact fe
  exact WP.mono (ops_FE fe [.copy 6 1]) fun t ⟨f, k, _⟩ => ⟨s, h, k, f⟩

theorem vR_rel : RelCT isa (Runs VP₀ V6) (.block Impl.Ed448.X86.vR) (Runs VP₀ (FS bsV)) := by
  refine Runs.step (RelCT.taint (A := taint) (τr [.esp, .edi])
    (fun _ _ ⟨_, _, hP, ⟨_, _, _, f₁⟩, ⟨_, _, _, f₂⟩⟩ => FS.agree hP f₁.fs f₂.fs) (by taint_decide)) ?_
  intro σ s h
  have fe : FE bsV σ s := by obtain ⟨_, _, _, fe⟩ := h; exact fe
  exact WP.mono (vR_ok fe.fin.scr fe.fin.bounded h.r.1 h.r.2) fun t ⟨k, b, _⟩ => FS.keep fe.fs k b

/-- In `vdouble`, `k + 1` iterations left. -/
def DI (k : Nat) (σ s : State) : Prop := FS bsV σ s ∧ s.gpr .esi = BitVec.ofNat 32 (k + 1) ∧ k + 1 < 2 ^ 16

theorem vdouble_rel : RelCT isa (Runs VP₀ (FS bsV)) Impl.Ed448.X86.vdouble (Runs VP₀ (FS bsV)) := by
  unfold Impl.Ed448.X86.vdouble
  refine RelCT.seq (Runs.step (G := DI 1) (RelCT.taint (A := taint) (τr [])
    (fun _ _ _ => agree_regs fun _ h => (List.not_mem_nil h).elim) (by taint_decide)) ?_)
    (RelCT.loop (M := isa) (fun k => Runs VP₀ (DI k)) (fun k => ?_) 1)
  · intro σ s h
    exact WP.mono (setCounter_ok s 2 (by decide)) fun t ⟨h1, h2, h3, h4, h5⟩ =>
      ⟨⟨FInv.of_counter h.1 h2 h3 h4 h5, (h2 _ (by decide)).trans h.2⟩, h1, by decide⟩
  refine Runs.then (G := fun σ t => FS bsV σ t ∧ t.gpr .esi = BitVec.ofNat 32 k ∧ t.zf = some (decide (k = 0)) ∧
      k < 2 ^ 16) (fun _ _ h => h)
    ((field_tr (fun _ _ h => h.1) _ (by decide)).seq (RelCT.taint (A := taint) (τr [])
      (fun _ _ _ => agree_regs fun _ h => (List.not_mem_nil h).elim) (by taint_decide))) ?_ ?_
  · rintro σ s ⟨f, e, hk⟩
    exact WP.mono (vdoubleStep_ok f.1.scr f.1.ctx f.1.bounded (k := k) (by omega) e)
      fun t ⟨et, zt, kt, _, bt, _⟩ => ⟨⟨⟨f.1.scr.of_keeps kt (by decide), f.1.ctx.keep (kt.1 _ (by decide)), bt⟩,
        (kt.1 _ (by decide)).trans f.2⟩, et, zt, by omega⟩
  · rintro σ₁ σ₂ t₁ t₂ hP - ⟨f₁, e₁, z₁, b₁⟩ ⟨f₂, e₂, z₂, b₂⟩
    rw [eval_ne z₁, eval_ne z₂]
    refine ⟨rfl, fun _ => ⟨σ₁, σ₂, hP, f₁, f₂⟩, fun hz => ?_⟩
    have hk0 : k ≠ 0 := fun h0 => by simp [h0] at hz
    have e : k - 1 + 1 = k := by omega
    exact ⟨k - 1, by omega, σ₁, σ₂, hP, ⟨f₁, e ▸ e₁, by omega⟩, ⟨f₂, e ▸ e₂, by omega⟩⟩

theorem vfinish_tr : RelCT isa (Runs VP₀ (FS bsV)) Impl.Ed448.X86.vfinish fun _ _ => True := by
  unfold Impl.Ed448.X86.vfinish
  exact vdouble_rel.seq ((field_FS _ (by decide)).seq (eqSlots_FS.seq ((field_FS _ (by decide)).seq
    (RelCT.taint (A := taint) (τr [.esp, .edi]) (fun _ _ ⟨_, _, hP, f₁, f₂⟩ => FS.agree hP f₁ f₂)
      (by taint_decide)))))

theorem vafter_tr : RelCT isa (Runs VP₀ (LoopAt · 0 ·)) Impl.Ed448.X86.vafter fun _ _ => True := by
  unfold Impl.Ed448.X86.vafter
  exact negA_rel.seq (copy1_rel.seq (vloop_rel.seq (copy6_rel.seq (vR_rel.seq vfinish_tr))))

theorem verifyEquation_ct (hR : RecoverOk) :
    ConstantTime isa verifyEquationLocal.pre verifyEquationLocal.pub verifyEquation := by
  refine RelCT.constantTime (Q := fun _ _ => True)
    ((?_ : RelCT isa (Runs VP₀ fun σ s => s = σ ∧ VerifyPre σ) verifyEquation fun _ _ => True).mono
      (fun s₁ s₂ h => ⟨s₁, s₂, h, ⟨rfl, VerifyPre.of h.1⟩, ⟨rfl, VerifyPre.of h.2.1⟩⟩) fun _ _ h => h)
  unfold verifyEquation Impl.Ed448.X86.vdecode
  refine RelCT.seq (Runs.step (G := VE) (RelCT.taint (A := taint) verifyTaint ?_ (by taint_decide))
    fun σ s ⟨e, h⟩ => by subst e; exact ventry_VE h)
    (RelCT.seq (RelCT.seq (R := Runs VP₀ fun σ x => 1 ≤ 2 ∧ LoopAt σ 2 x) ?_ ?_) vafter_tr)
  · rintro s₁ s₂ ⟨σ₁, σ₂, hP, ⟨rfl, -⟩, ⟨rfl, -⟩⟩
    exact verifyTaint_agree hP.1 hP.2.1 hP.2.2
  · refine Runs.step (G := fun σ x => 1 ≤ 2 ∧ LoopAt σ 2 x) (RelCT.taint (A := taint) (τa 20)
      (fun _ _ ⟨_, _, hP, e₁, e₂⟩ => FE.agreeV hP e₁.fe₁ e₂.fe₁) (by taint_decide)) ?_
    intro σ s e
    exact WP.mono (vdecodeInit_ok e.lp.scr e.lp.bounded e.lp.sig) fun t ht => ⟨by decide, s, e, ht⟩
  · exact RelCT.loop (M := isa) (fun n => Runs VP₀ fun σ x => 1 ≤ n ∧ LoopAt σ n x)
      (vdecodeBody_rel hR) 2

end VG.Proof.Ed448.X86
