module

public import VerifiedGarbage.Proof.Ed448.X86.VerifyMain
public import VerifiedGarbage.Proof.X448.X86.Runs
import VerifiedGarbage.Proof.Ed448.X86.VerifyDecode
import VerifiedGarbage.Proof.Ed448.X86.BaseMain
import VerifiedGarbage.Proof.Ed448.X86.VerifyFinish
import VerifiedGarbage.Proof.Ed448.X86.VerifyDecodeY
import VerifiedGarbage.Proof.X448.X86.Frame
import VerifiedGarbage.Proof.X448.X86.Counters
import VerifiedGarbage.Proof.X448.X86.Iter
import VerifiedGarbage.Proof.X448.X86.FnLit
import VerifiedGarbage.Proof.Ed448.X86.VerifyLit
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Ed448.X86.VerifyMain
meta import VerifiedGarbage.Proof.X448.X86.Runs
meta import VerifiedGarbage.Proof.Ed448.X86.VerifyDecode
meta import VerifiedGarbage.Proof.Ed448.X86.BaseMain
meta import VerifiedGarbage.Proof.Ed448.X86.VerifyFinish
meta import VerifiedGarbage.Proof.Ed448.X86.VerifyDecodeY
meta import VerifiedGarbage.Proof.X448.X86.Frame
meta import VerifiedGarbage.Proof.X448.X86.Counters
meta import VerifiedGarbage.Proof.X448.X86.Iter
meta import VerifiedGarbage.Proof.X448.X86.FnLit
meta import VerifiedGarbage.Proof.Ed448.X86.VerifyLit
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# Ed448 verification's equation on x86 (32-bit): constant time

The calls of the field functions are related run by run (`RelCT`,
`Proof/X448/X86/Runs.lean`), and so is the whole function: the blocks
between them by the taint analysis, from what each run's correctness says of
its own state (`FS`: the field arithmetic's invariant and `esp`; `FE`, with
the memory but the working space and the stack below the return address,
where code reads the arguments), and the loops by `RelCT.loop`, with the
correctness proofs' invariants. `VP₀` relates the entry states. The recoding
of `k`'s digits, and the loop's addition of the entry of a digit, branch on
`k` and address the working space by it: `k` is public (`VP₀.kv`), so two
runs are in the same state of the recoding after each bit, and load the same
digit.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Proof.Ed448 (RecoverOk fopValid evalOps)
open VG.Impl.Ed448.X86 (verifyEquation ventry vdecodeInit vdecodeBody vbodyA vnext decode field root RX RY KBITS VTAB
  vtable vtableInit vtableStep ventryStore ventryLoad vcombIf vaddIf addTake addAtZ)
open VG.Impl.X448.X86 (slot BITS)

/-- Two entry states the constant-time statement relates. -/
def VP₀ (σ₁ σ₂ : State) : Prop :=
  verifyEquationLocal.pre σ₁ ∧ verifyEquationLocal.pre σ₂ ∧ verifyEquationLocal.pub σ₁ σ₂

/-- The working space, from the entry state. -/
abbrev bsV (σ : State) : Addr := (arg σ 3).setWidth 64

theorem VP₀.hp {σ₁ σ₂ : State} (h : VP₀ σ₁ σ₂) : bsV σ₁ = bsV σ₂ ∧ σ₁.gpr .esp = σ₂.gpr .esp :=
  ⟨by simp only [bsV, h.2.2.2.2.2.2.1], h.2.2.1⟩

theorem VP₀.arg {σ₁ σ₂ : State} (h : VP₀ σ₁ σ₂) {i : Nat} (hi : i < 4) : arg σ₁ i = arg σ₂ i := by
  obtain ⟨_, _, _, a0, a1, a2, a3, _⟩ := h
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
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
    fun _ => ⟨by simp only [verifyTaint]; omega_using [spfit], ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl; simp only [BitVec.toNat_setWidth]; omega_using [hf]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl
    exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [spfit]) hp.ret_sc hp.args_sc
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
    rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    exacts [a0, a1, a2, a3]
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, verifyTaint_wf hs, verifyTaint_wf ht,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hsp,
    fun k h4 hk => ?_⟩
  · simp only [verifyTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hsp
  · rw [ps.wr, pt.wr, a3]
  · simp only [verifyTaint] at hk
    have fs := ps.sp_fit
    have ft := pt.sp_fit
    rw [show VG.X86.Taint.depth verifyTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by omega_using [fs]) h4 hk, VG.X86.Taint.argByte_eq (by omega_using [ft]) h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (ha ((k - 4) / 4) (by omega_using [hk]))

/-- `S` and `k`, from the entry state. -/
abbrev SV (σ : State) : Nat :=
  Spec.Ed448.decodeLE (Spec.Ed448.bytesAt σ.mem ((arg σ 1).setWidth 64 + BitVec.ofNat 64 57) 57)
abbrev KV (σ : State) : Nat := Spec.Ed448.decodeLE (Spec.Ed448.bytesAt σ.mem ((arg σ 2).setWidth 64) 57)

/-- The bits of `S` and `k` in the working space. -/
abbrev BitsAt (σ s : State) : Prop := VBits (bsV σ) (SV σ) (KV σ) s.mem

/-- After the entry block. -/
structure VE (σ s₁ : State) : Prop where
  pre : VerifyPre σ
  lp : LoopPre σ s₁
  sp : s₁.gpr .esp = σ.gpr .esp
  out : Outside (bsV σ) 0 8192 σ.mem s₁.mem
  bits : BitsAt σ s₁
  e : ∀ i : Index, E s₁.mem (bsV σ) i = Proof.X448.toFe (Impl.Ed448.X86.initVal i.val)

theorem ventry_VE {σ : State} (h : VerifyPre σ) : WP isa ventry σ (VE σ) :=
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
    E_out ao i (Or.inl (by have := slot_range i; simp only [RX]; omega_using [this]))
  have h10u : E u.mem (bsV σ) 10 = 1 := by rw [Eu, ht.other 10 (by decide) (by decide) (by decide), e.lp.e10]
  have h11u : E u.mem (bsV σ) 11 = Spec.Ed448.d := by
    rw [Eu, ht.other 11 (by decide) (by decide) (by decide), e.lp.e11]
  have hp : u.gpr .esi = (if n = 2 then arg σ 1 else arg σ 0) := ae.trans (ht.ptr hn)
  have hin : Input u (bsV σ) (if n = 2 then arg σ 1 else arg σ 0) 57 := by
    split
    · exact e.lp.isig.of_keeps kt
    · exact e.lp.ipk.of_keeps kt
  refine WP.mono (fe.wp (NoSp.of_all (by lit_decide)) (by lit_decide) (Q := fun _ => True)
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
    exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [this]) p.ret_sc p.args_sc
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
      exact ⟨n - 1, by omega_using [h0], σ₁, σ₂, hP, ⟨by omega_using [h0], l₁⟩, ⟨by omega_using [h0], l₂⟩⟩


/-! ## After the decodings -/

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
  exact WP.mono (fe.wp (NoSp.of_all (by lit_decide)) (by lit_decide)
    (Q := fun t => Keep (bsV σ) s t ∧ E t.mem (bsV σ) = evalOps [.sub 6 0 6] (E s.mem (bsV σ)))
    (WP.mono (field_ok _ (by decide) fe.fin.scr fe.fin.ctx fe.fin.bounded) fun t ⟨k, b, e⟩ =>
      ⟨⟨k.scr fe.fin.scr, k.ctx fe.fin.ctx, b⟩, k.regs.1 _ (by decide), k.regs.2.2, k, e⟩))
    fun t ⟨f, k, e⟩ => ⟨s, h, k, e, f⟩

/-- What the recoding, the table and the loop start from: the bits, 1 and `d` in their slots,
and `R`'s coordinates bounded. -/
theorem V3.facts {σ s₃ : State} (h : V3 σ s₃) :
    BitsAt σ s₃ ∧ E s₃.mem (bsV σ) 10 = 1 ∧ E s₃.mem (bsV σ) 11 = Spec.Ed448.d ∧
      Bounded s₃.mem (bsV σ) RX ∧ Bounded s₃.mem (bsV σ) RY := by
  obtain ⟨s₂, ⟨s₁, e, d⟩, k₃, e₃, -⟩ := h
  obtain ⟨_, k₃e⟩ := sub6_E (E s₂.mem (bsV σ))
  rw [← e₃] at k₃e
  obtain ⟨bx, by'⟩ := d.rBnd rfl
  exact ⟨VBits.kept (WsOut2.widen k₃.2) (VBits.keptD d.frame e.bits),
    by rw [k₃e 10 (by decide), d.other 10 (by decide) (by decide) (by decide), e.lp.e10],
    by rw [k₃e 11 (by decide), d.other 11 (by decide) (by decide) (by decide), e.lp.e11],
    (F_high k₃.2 (by decide) (Or.inl rfl)).2 bx, (F_high k₃.2 (by decide) (Or.inr rfl)).2 by'⟩

/-- `k`, the same in two runs: the challenge is public. -/
theorem VP₀.kv {σ₁ σ₂ : State} (h : VP₀ σ₁ σ₂) : KV σ₁ = KV σ₂ :=
  congrArg Spec.Ed448.decodeLE h.2.2.2.2.2.2.2.2.2

/-- From the recoding of `k`'s digits on: the field arithmetic's invariant, the bits of `S` and
the digits of `k`, 1 and `d` in their slots, and `R`'s coordinates bounded. -/
structure VW (σ s : State) : Prop where
  fe : FE bsV σ s
  dig : VDig (bsV σ) (SV σ) (KV σ) s.mem
  one : E s.mem (bsV σ) 10 = 1
  d : E s.mem (bsV σ) 11 = Spec.Ed448.d
  rx : Bounded s.mem (bsV σ) RX
  ry : Bounded s.mem (bsV σ) RY

/-- After field operations that keep slots 10 and 11. -/
theorem VW.keep {σ s t : State} (h : VW σ s) (fe : FE bsV σ t) (k : Keep (bsV σ) s t)
    (e10 : E t.mem (bsV σ) 10 = E s.mem (bsV σ) 10) (e11 : E t.mem (bsV σ) 11 = E s.mem (bsV σ) 11) :
    VW σ t :=
  ⟨fe, h.dig.keep k.mem, e10.trans h.one, e11.trans h.d, (F_high k.mem (by decide) (Or.inl rfl)).2 h.rx,
    (F_high k.mem (by decide) (Or.inr rfl)).2 h.ry⟩

/-- `FE`, after code that writes no memory and keeps `esp` and `edi`. -/
theorem feMem {σ s t : State} (fe : FE bsV σ s) {rs : List Reg} (k : Keeps rs s t) (hesp : .esp ∉ rs)
    (hedi : .edi ∉ rs) (m : t.mem = s.mem) : FE bsV σ t :=
  ⟨⟨fe.fin.scr.of_keeps k hedi, fe.fin.ctx.keep (k.1 _ hesp), m ▸ fe.fin.bounded⟩, (k.1 _ hesp).trans fe.sp,
    k.2.2.trans fe.wr, by rw [m]; exact fe.frame⟩

theorem VW.of_mem {σ s t : State} (h : VW σ s) {rs : List Reg} (k : Keeps rs s t) (hesp : .esp ∉ rs)
    (hedi : .edi ∉ rs) (m : t.mem = s.mem) : VW σ t :=
  ⟨feMem h.fe k hesp hedi m, by rw [m]; exact h.dig, by rw [m]; exact h.one, by rw [m]; exact h.d,
    by rw [m]; exact h.rx, by rw [m]; exact h.ry⟩

/-- A list of field operations that keeps slots 10 and 11. -/
theorem opsVW (xs : List FieldOp) (h10 : (10 : Index) ∉ xs.map fdest) (h11 : (11 : Index) ∉ xs.map fdest) :
    RelCT isa (Runs VP₀ VW) (Impl.X448.X86.ops (xs.map FieldOp.impl)) (Runs VP₀ VW) :=
  Runs.step (ops_tr (fun _ _ h => h.hp) (fun _ _ h => h.fe.fs) xs) fun σ s h =>
    WP.mono (ops_FE h.fe xs) fun t ⟨fe, k, e⟩ =>
      h.keep fe k (by rw [e, applyOps_keep _ _ h10]) (by rw [e, applyOps_keep _ _ h11])

/-! ## `k`'s digits

Two runs on the same `k` are in the same state of the recoding after each bit (`RecSt`, from
each run's correctness), so the test of a window in hand and the addresses of the bytes they
store agree. -/

/-- What a bit's first block needs public: the working space, the counter, the weight and the
window's address. -/
theorem RecSt.agree {i e : Nat} {σ₁ σ₂ s₁ s₂ : State} (hP : VP₀ σ₁ σ₂)
    (h₁ : RecSt (bsV σ₁) (KV σ₁) i e s₁) (h₂ : RecSt (bsV σ₂) (KV σ₂) i e s₂) :
    VG.X86.Taint.Agree (τr [.edi, .esi, .ebx, .eax]) s₁ s₂ := by
  have hedi : s₁.gpr .edi = s₂.gpr .edi := edi_eq h₁.scr (hP.hp.1 ▸ h₂.scr)
  refine agree_regs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hedi
  · exact h₁.esi.trans h₂.esi.symm
  · rw [h₁.ebx, h₂.ebx, hP.kv]
  · rw [h₁.eax, h₂.eax, hedi, hP.kv]

/-- One bit's trace. -/
theorem recBit_tr (i : Nat) (hi : i < 456) :
    RelCT isa (Runs VP₀ fun σ s => RecSt (bsV σ) (KV σ) i i s) Impl.Ed448.X86.recBit fun _ _ => True := by
  unfold Impl.Ed448.X86.recBit
  refine RelCT.seq (Runs.step (G := fun σ s => RecH (bsV σ) (KV σ) i s)
      (RelCT.taint (A := taint) (τr [.edi, .esi, .ebx, .eax])
        (fun _ _ ⟨_, _, hP, h₁, h₂⟩ => RecSt.agree hP h₁ h₂) (by taint_decide))
      fun σ s h => WP.mono (recHead_ok h hi) fun t ht => ht.1)
    (RelCT.seq (R := fun _ _ => True) (VG.X86.RelCT.ite ?_ ?_ ?_)
      (RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs fun _ h => (List.not_mem_nil h).elim)
        (by taint_decide)))
  · rintro s₁ s₂ ⟨σ₁, σ₂, hP, h₁, h₂⟩
    change s₁.zf = s₂.zf
    rw [h₁.zf, h₂.zf, hP.kv]
  · exact RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs fun _ h => (List.not_mem_nil h).elim)
      (by taint_decide)
  · refine RelCT.taint (A := taint) (τr [.ebp, .eax]) ?_ (by taint_decide)
    rintro s₁ s₂ ⟨⟨σ₁, σ₂, hP, h₁, h₂⟩, -⟩
    have hedi : s₁.gpr .edi = s₂.gpr .edi := edi_eq h₁.st.scr (hP.hp.1 ▸ h₂.st.scr)
    refine agree_regs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.ebp, h₂.ebp, hedi]
    · rw [h₁.st.eax, h₂.st.eax, hedi, hP.kv]

/-- In the recoding, `n + 1` bits left. -/
def RecI (n : Nat) (σ s : State) : Prop := n < 456 ∧ RecSt (bsV σ) (KV σ) (455 - n) (455 - n) s

theorem vrecode_tr : RelCT isa (Runs VP₀ V3) Impl.Ed448.X86.vrecode fun _ _ => True := by
  unfold Impl.Ed448.X86.vrecode
  refine RelCT.seq (Runs.step (G := RecI 455) (RelCT.taint (A := taint) (τr [])
      (fun _ _ _ => agree_regs fun _ h => (List.not_mem_nil h).elim) (by taint_decide)) ?_)
    (RelCT.loop (M := isa) (fun n => Runs VP₀ (RecI n)) (fun n => ?_) 455)
  · intro σ s h
    exact WP.mono (recInit_ok (K := KV σ) h.fe.fin.scr fun q hq => (h.facts.1 q hq).2) fun t ⟨_, _, r⟩ =>
      ⟨by decide, r⟩
  · refine Runs.then (G := fun σ t => n < 456 ∧ RecSt (bsV σ) (KV σ) (455 - n + 1) (455 - n + 1) t ∧
        t.zf = some (decide (455 - n + 1 = 456))) (fun _ _ h => h)
      ((recBit_tr (455 - n) (by omega_arith)).mono
        (fun _ _ ⟨σ₁, σ₂, hP, h₁, h₂⟩ => ⟨σ₁, σ₂, hP, h₁.2, h₂.2⟩) fun _ _ h => h) ?_ ?_
    · rintro σ s ⟨hn, h⟩
      exact WP.mono (recBit_ok h (by omega_arith)) fun t ⟨_, _, r, z⟩ => ⟨hn, r, z⟩
    · rintro σ₁ σ₂ t₁ t₂ hP - ⟨hn, r₁, z₁⟩ ⟨-, r₂, z₂⟩
      rw [eval_ne z₁, eval_ne z₂]
      refine ⟨rfl, fun _ => trivial, fun hz => ?_⟩
      have h0 : ¬(455 - n + 1 = 456) := by simpa using hz
      have e : 455 - (n - 1) = 455 - n + 1 := by omega_using [h0, hn]
      exact ⟨n - 1, by omega_using [h0, hn], σ₁, σ₂, hP, ⟨by omega_using [hn], by rw [e]; exact r₁⟩,
        ⟨by omega_using [hn], by rw [e]; exact r₂⟩⟩

theorem vrecode_rel : RelCT isa (Runs VP₀ V3) Impl.Ed448.X86.vrecode (Runs VP₀ VW) :=
  Runs.step vrecode_tr fun σ s h => by
    obtain ⟨bits, h10, h11, rx, ry⟩ := h.facts
    have fe := h.fe
    refine WP.mono (fe.wp (NoSp.of_all (by lit_decide)) (by lit_decide)
      (Q := fun t => Outside (bsV σ) KBITS 456 s.mem t.mem ∧
        ∀ q < 456, t.mem (off (bsV σ) (KBITS + q)) = BitVec.ofNat 8 (Proof.Ed448.vdigits (KV σ) q))
      (WP.mono (vrecode_ok fe.fin.scr fun q hq => (bits q hq).2) fun t ⟨k, o, dig⟩ =>
        ⟨⟨fe.fin.scr.of_keeps k (by decide), fe.fin.ctx.keep (k.1 _ (by decide)),
          (slots_out o (by decide)).2 fe.fin.bounded⟩, k.1 _ (by decide), k.2.2, o, dig⟩))
      fun t ⟨fe', o, dig⟩ => ?_
    obtain ⟨eE, -⟩ := slots_out o (by decide)
    exact ⟨fe', fun q hq => ⟨by
        rw [o _ (Or.inl (by rw [ofs_off' _ (by simp only [BITS]; omega_using [hq])]; simp only [BITS, KBITS]; omega_using [hq]))]
        exact (bits q hq).1, dig q hq⟩,
      by rw [eE]; exact h10, by rw [eE]; exact h11,
      (F_below (WsBelow.of_out o (Nat.le_refl _)) (Nat.le_refl _) (by decide) (Or.inl rfl)).2 rx,
      (F_below (WsBelow.of_out o (Nat.le_refl _)) (Nat.le_refl _) (by decide) (Or.inr rfl)).2 ry⟩

/-! ## The table of `-A`'s odd multiples -/

/-- In the table's code: the entry to store. -/
def TI (j : Nat) (σ s : State) : Prop := FE bsV σ s ∧ s.gpr .esi = BitVec.ofNat 32 (VTAB + 384 * j) ∧ j < 8

theorem TI.agree {j : Nat} {s₁ s₂ : State} (h : Runs VP₀ (TI j) s₁ s₂) :
    VG.X86.Taint.Agree (τr [.esp, .esi, .edi]) s₁ s₂ := by
  obtain ⟨σ₁, σ₂, hP, f₁, f₂⟩ := h
  refine agree_regs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact f₁.1.sp.trans (hP.hp.2.trans f₂.1.sp.symm)
  · exact f₁.2.1.trans f₂.2.1.symm
  · exact edi_eq f₁.1.fin.scr (hP.hp.1 ▸ f₂.1.fin.scr)

/-- An entry's store keeps `FE`. -/
theorem ventryStoreT_ok {j : Nat} {σ s : State} (h : TI j σ s) :
    WP isa (.block ventryStore) s fun t => FE bsV σ t ∧
      t.gpr .esi = BitVec.ofNat 32 (VTAB + 384 * (j + 1)) ∧ t.zf = some (decide (j + 1 = 8)) := by
  obtain ⟨fe, he, hj⟩ := h
  exact fe.wp (NoSp.of_all (by lit_decide)) (by lit_decide)
    (WP.mono (ventryStore_ok fe.fin.scr fe.fin.bounded hj he) fun t ⟨k, o, _, g, z⟩ =>
      ⟨⟨fe.fin.scr.of_keeps k (by decide), fe.fin.ctx.keep (k.1 _ (by decide)),
        (slots_out o (by simp only [VTAB]; omega_arith)).2 fe.fin.bounded⟩, k.1 _ (by decide), k.2.2, g, z⟩)

theorem vtableInit_rel : RelCT isa (Runs VP₀ VW) vtableInit (Runs VP₀ (TI 1)) := by
  unfold Impl.Ed448.X86.vtableInit
  rw [tableQF_impl, field, doubleF6_impl]
  refine RelCT.seq (Runs.step (G := FE bsV) (ops_tr (fun _ _ h => h.hp) (fun _ _ h => h.fe.fs) _)
      fun σ s h => WP.mono (ops_FE h.fe _) fun t ⟨fe, _⟩ => fe)
    (RelCT.seq (Runs.step (G := TI 1) (RelCT.taint (A := taint) (τr [.esp, .edi])
        (fun _ _ ⟨_, _, hP, f₁, f₂⟩ => FS.agree hP f₁.fs f₂.fs) (by taint_decide)) ?_)
      (Runs.step (ops_tr (fun _ _ h => h.hp) (fun _ _ h => h.1.fs) _) fun σ s h =>
        WP.mono (ops_FE h.1 _) fun t ⟨fe, k, _⟩ => ⟨fe, (k.regs.1 _ (by decide)).trans h.2.1, h.2.2⟩))
  intro σ s fe
  refine wp_mov rfl fun u hu => ?_
  have feu : FE bsV σ u := feMem fe (hu.rest (rs := [.esi]) (by decide)) (by decide) (by decide) hu.mem
  exact WP.mono (ventryStoreT_ok (j := 0) ⟨feu, by rw [hu.gpr]; rfl, by decide⟩) fun t ⟨f, g, _⟩ =>
    ⟨f, g, by decide⟩

theorem vtableStep_rel (n : Nat) :
    RelCT isa (Runs VP₀ fun σ s => n ≤ 6 ∧ TI (7 - n) σ s) vtableStep fun x y =>
      isa.eval .ne x = isa.eval .ne y ∧ (isa.eval .ne x = some false → Runs VP₀ (FE bsV) x y) ∧
        (isa.eval .ne x = some true → ∃ m < n, Runs VP₀ (fun σ s => m ≤ 6 ∧ TI (7 - m) σ s) x y) := by
  unfold Impl.Ed448.X86.vtableStep
  rw [addTake6_impl]
  refine Runs.then (G := fun σ t => n ≤ 6 ∧ FE bsV σ t ∧
      t.gpr .esi = BitVec.ofNat 32 (VTAB + 384 * (7 - n + 1)) ∧ t.zf = some (decide (7 - n + 1 = 8)))
    (fun _ _ h => h)
    (RelCT.seq (Runs.step (G := TI (7 - n)) (ops_tr (fun _ _ h => h.hp) (fun _ _ h => h.2.1.fs) _)
        fun σ s h => WP.mono (ops_FE h.2.1 _) fun t ⟨fe, k, _⟩ =>
          ⟨fe, (k.regs.1 _ (by decide)).trans h.2.2.1, h.2.2.2⟩)
      (RelCT.taint (A := taint) (τr [.esp, .esi, .edi]) (fun _ _ h => TI.agree h) (by taint_decide))) ?_ ?_
  · rintro σ s ⟨hn, h⟩
    exact WP.seq (WP.mono (ops_FE h.1 _) fun t ⟨fe, k, _⟩ =>
      WP.mono (ventryStoreT_ok ⟨fe, (k.regs.1 _ (by decide)).trans h.2.1, h.2.2⟩) fun u ⟨f, g, z⟩ => ⟨hn, f, g, z⟩)
  · rintro σ₁ σ₂ t₁ t₂ hP - ⟨hn, f₁, g₁, z₁⟩ ⟨-, f₂, g₂, z₂⟩
    rw [eval_ne z₁, eval_ne z₂]
    refine ⟨rfl, fun _ => ⟨σ₁, σ₂, hP, f₁, f₂⟩, fun hz => ?_⟩
    have h0 : ¬(7 - n + 1 = 8) := by simpa using hz
    have e : 7 - (n - 1) = 7 - n + 1 := by omega_using [h0, hn]
    exact ⟨n - 1, by omega_using [h0, hn], σ₁, σ₂, hP,
      ⟨by omega_using [hn], f₁, by rw [e]; exact g₁, by omega_using [hn]⟩,
      ⟨by omega_using [hn], f₂, by rw [e]; exact g₂, by omega_using [hn]⟩⟩

theorem vtable_tr : RelCT isa (Runs VP₀ VW) vtable fun _ _ => True := by
  unfold Impl.Ed448.X86.vtable
  rw [neutralF_impl]
  exact RelCT.seq (vtableInit_rel.mono (fun _ _ h => h)
      fun _ _ ⟨σ₁, σ₂, hP, f₁, f₂⟩ => ⟨σ₁, σ₂, hP, ⟨by decide, f₁⟩, ⟨by decide, f₂⟩⟩)
    (RelCT.seq (RelCT.loop (M := isa) (fun n => Runs VP₀ fun σ s => n ≤ 6 ∧ TI (7 - n) σ s) vtableStep_rel 6)
      (ops_tr (fun _ _ h => h.hp) (fun _ _ h => h.fs) _))

/-- With the table of the odd multiples of a point. -/
def VT (σ s : State) : Prop := VW σ s ∧ ∃ A, TabOk (bsV σ) A s.mem

theorem vtable_rel : RelCT isa (Runs VP₀ VW) vtable (Runs VP₀ VT) :=
  Runs.step vtable_tr fun σ s h => by
    have fe := h.fe
    refine WP.mono (fe.wp (NoSp.of_all (by lit_decide)) (by lit_decide) (Q := Tabled (bsV σ) s)
      (WP.mono (vtable_ok fe.fin.scr fe.fin.ctx fe.fin.bounded h.one h.d) fun t T =>
        ⟨⟨T.scr, T.ctx, T.bounded⟩, T.regs.1 _ (by decide), T.regs.2.2, T⟩)) fun t ⟨fe', T⟩ => ?_
    exact ⟨⟨fe', h.dig.below T.mem (by decide) (by decide), T.one, T.d,
      (F_below T.mem (by decide) (by decide) (Or.inl rfl)).2 h.rx,
      (F_below T.mem (by decide) (by decide) (Or.inr rfl)).2 h.ry⟩, _, T.tab⟩

/-! ## The loop over the bits -/

theorem VT.keep {σ s t : State} (h : VT σ s) (fe : FE bsV σ t) (k : Keep (bsV σ) s t)
    (e10 : E t.mem (bsV σ) 10 = E s.mem (bsV σ) 10) (e11 : E t.mem (bsV σ) 11 = E s.mem (bsV σ) 11) :
    VT σ t :=
  ⟨h.1.keep fe k e10 e11, let ⟨A, ht⟩ := h.2; ⟨A, fun j hj => (ht j hj).keep hj k.mem⟩⟩

theorem VT.of_mem {σ s t : State} (h : VT σ s) {rs : List Reg} (k : Keeps rs s t) (hesp : .esp ∉ rs)
    (hedi : .edi ∉ rs) (m : t.mem = s.mem) : VT σ t :=
  ⟨h.1.of_mem k hesp hedi m, by rw [m]; exact h.2⟩

/-- Code that keeps the field arithmetic's frame and slots 10 and 11 keeps `VT`. -/
theorem VT.wp {σ s : State} (h : VT σ s) {c : Prog isa} (hc : NoSp c) (hu : stackUse c ≤ 20)
    (hw : WP isa c s fun t => Keep (bsV σ) s t ∧ BoundedEnv t.mem (bsV σ) ∧
      E t.mem (bsV σ) 10 = E s.mem (bsV σ) 10 ∧ E t.mem (bsV σ) 11 = E s.mem (bsV σ) 11) :
    WP isa c s fun t => VT σ t ∧ Keep (bsV σ) s t :=
  WP.mono (h.1.fe.wp hc hu (Q := fun t => Keep (bsV σ) s t ∧
      E t.mem (bsV σ) 10 = E s.mem (bsV σ) 10 ∧ E t.mem (bsV σ) 11 = E s.mem (bsV σ) 11)
    (WP.mono hw fun t ⟨k, b, e10, e11⟩ =>
      ⟨⟨k.scr h.1.fe.fin.scr, k.ctx h.1.fe.fin.ctx, b⟩, k.regs.1 _ (by decide), k.regs.2.2, k, e10, e11⟩))
    fun t ⟨fe, k, e10, e11⟩ => ⟨h.keep fe k e10 e11, k⟩

/-- Within the iteration of bit `n`. -/
def StepW (n : Nat) (σ t : State) : Prop := VT σ t ∧ t.gpr .esi = BitVec.ofNat 32 n ∧ n < 456

theorem StepW.agree {n : Nat} {s₁ s₂ : State} (h : Runs VP₀ (StepW n) s₁ s₂) :
    VG.X86.Taint.Agree (τr [.esp, .esi, .edi]) s₁ s₂ := by
  obtain ⟨σ₁, σ₂, hP, f₁, f₂⟩ := h
  refine agree_regs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact f₁.1.1.fe.sp.trans (hP.hp.2.trans f₂.1.1.fe.sp.symm)
  · exact f₁.2.1.trans f₂.2.1.symm
  · exact edi_eq f₁.1.1.fe.fin.scr (hP.hp.1 ▸ f₂.1.1.fe.fin.scr)

/-- A list of field operations that keeps slots 10 and 11, in an iteration. -/
theorem opsW (n : Nat) (xs : List FieldOp) (h10 : (10 : Index) ∉ xs.map fdest)
    (h11 : (11 : Index) ∉ xs.map fdest) :
    RelCT isa (Runs VP₀ (StepW n)) (Impl.X448.X86.ops (xs.map FieldOp.impl)) (Runs VP₀ (StepW n)) :=
  Runs.step (ops_tr (fun _ _ h => h.hp) (fun _ _ h => h.1.1.fe.fs) xs) fun σ s h =>
    WP.mono (ops_FE h.1.1.fe xs) fun t ⟨fe, k, e⟩ =>
      ⟨h.1.keep fe k (by rw [e, applyOps_keep _ _ h10]) (by rw [e, applyOps_keep _ _ h11]),
        (k.regs.1 _ (by decide)).trans h.2.1, h.2.2⟩

theorem doubleW (n : Nat) :
    RelCT isa (Runs VP₀ (StepW n)) (field Impl.Ed448.doubleOps) (Runs VP₀ (StepW n)) := by
  rw [field, doubleF0_impl]
  exact opsW n _ (by decide) (by decide)

theorem addTake8W (n : Nat) :
    RelCT isa (Runs VP₀ (StepW n)) (addTake Impl.Ed448.addOps) (Runs VP₀ (StepW n)) := by
  rw [addTake8_impl]
  exact opsW n _ (by decide) (by decide)

theorem addTake6W (n : Nat) :
    RelCT isa (Runs VP₀ (StepW n)) (addTake (addAtZ 6 7 21)) (Runs VP₀ (StepW n)) := by
  rw [addTake6_impl]
  exact opsW n _ (by decide) (by decide)

/-- The selection of the comb's entry, in a row. -/
theorem selectW_ok {n : Nat} {σ s : State} (h : StepW n σ s) (hn : n < 114) :
    WP isa (.block (Impl.Ed448.X86.combDigit Impl.X448.X86.BITS ++ Impl.Ed448.X86.combSelect)) s (StepW n σ) := by
  obtain ⟨vt, he, hn'⟩ := h
  have fe := vt.1.fe
  refine WP.mono (vt.wp (NoSp.of_all (by lit_decide)) (by lit_decide) ?_) fun t ⟨vt', k⟩ =>
    ⟨vt', (k.regs.1 _ (by decide)).trans he, hn'⟩
  rw [WP.block_append_iff]
  refine WP.mono (combDigit_ok (k := SV σ) fe.fin.scr (by decide) hn he fun i hi => (vt.1.dig i hi).1)
    fun u ⟨d, ku, mu⟩ => ?_
  obtain hsu := fe.fin.scr.of_keeps ku (by decide)
  obtain K : Keep (bsV σ) s u := ⟨ku.mono (by decide), by rw [mu]; exact WsOut2.refl _ _ _ _ _ _⟩
  refine WP.mono (combSelect_ok hsu (mu ▸ fe.fin.bounded) (Proof.Ed448.combDigit_lt (SV σ) n) d)
    fun t ⟨kt, bt, et⟩ => ⟨K.trans kt, bt, ?_, ?_⟩
  · rw [et, mu]; rfl
  · rw [et, mu]; rfl

/-- After the test of a row. -/
def StepC (n : Nat) (σ t : State) : Prop := StepW n σ t ∧ isa.eval .b t = some (decide (n < 114))

theorem vcombIf_rel (n : Nat) : RelCT isa (Runs VP₀ (StepW n)) vcombIf (Runs VP₀ (StepW n)) := by
  unfold Impl.Ed448.X86.vcombIf
  refine RelCT.seq (Runs.step (G := StepC n) (RelCT.taint (A := taint) (τr [.esp, .esi, .edi])
      (fun _ _ h => StepW.agree h) (by taint_decide)) ?_) (VG.X86.RelCT.ite ?_ ?_ ?_)
  · rintro σ s ⟨vt, he, hn⟩
    exact WP.mono (vrowTest_ok s hn he) fun t ⟨c, f⟩ =>
      ⟨⟨vt.of_mem (f.rest []) (by decide) (by decide) f.mem, (congrFun f.gpr _).trans he, hn⟩, c⟩
  · rintro s₁ s₂ ⟨σ₁, σ₂, hP, ⟨-, c₁⟩, ⟨-, c₂⟩⟩
    rw [c₁, c₂]
  · refine (RelCT.seq (Runs.step (P₀ := VP₀) (F := fun σ t => StepW n σ t ∧ n < 114) (G := StepW n)
        (RelCT.taint (A := taint) (τr [.esp, .esi, .edi])
          (fun _ _ ⟨σ₁, σ₂, hP, f₁, f₂⟩ => StepW.agree ⟨σ₁, σ₂, hP, f₁.1, f₂.1⟩) (by taint_decide))
        fun σ s h => selectW_ok h.1 h.2) (addTake8W n)).mono ?_ fun _ _ h => h
    rintro s₁ s₂ ⟨⟨σ₁, σ₂, hP, ⟨w₁, c₁⟩, ⟨w₂, c₂⟩⟩, hc⟩
    have hn : n < 114 := by rw [c₁] at hc; exact of_decide_eq_true (Option.some.inj hc)
    exact ⟨σ₁, σ₂, hP, ⟨w₁, hn⟩, ⟨w₂, hn⟩⟩
  · exact VG.X86.RelCT.nil fun s₁ s₂ ⟨⟨σ₁, σ₂, hP, ⟨w₁, _⟩, ⟨w₂, _⟩⟩, _⟩ => ⟨σ₁, σ₂, hP, w₁, w₂⟩

/-- After digit `n` of `k` is loaded. -/
def StepD (n : Nat) (σ t : State) : Prop :=
  StepW n σ t ∧ t.gpr .ecx = BitVec.ofNat 32 (Proof.Ed448.vdigits (KV σ) n) ∧
    t.zf = some (decide (Proof.Ed448.vdigits (KV σ) n = 0))

/-- The load of the entry of a digit that is not zero. -/
theorem entryW_ok {n : Nat} {σ s : State} (h : StepD n σ s) (h0 : Proof.Ed448.vdigits (KV σ) n ≠ 0) :
    WP isa (.block ventryLoad) s (StepW n σ) := by
  obtain ⟨⟨vt, he, hn⟩, hc, -⟩ := h
  obtain ⟨A, ht⟩ := vt.2
  have fe := vt.1.fe
  obtain hodd : Proof.Ed448.vdigits (KV σ) n % 2 = 1 ∧ Proof.Ed448.vdigits (KV σ) n < 16 :=
    (Proof.Ed25519.Slide.digits_odd 456 (KV σ) n).resolve_left h0
  obtain hj8 : (Proof.Ed448.vdigits (KV σ) n - 1) / 2 < 8 := by have := hodd.2; omega_using [this]
  refine WP.mono (vt.wp (NoSp.of_all (by lit_decide)) (by lit_decide)
    (WP.mono (ventryLoad_ok fe.fin.scr fe.fin.bounded hodd.2 hodd.1 hc (ht _ hj8)) fun t ⟨k, b, e⟩ =>
      ⟨k, b, by rw [e]; rfl, by rw [e]; rfl⟩)) fun t ⟨vt', k⟩ => ⟨vt', (k.regs.1 _ (by decide)).trans he, hn⟩

theorem vaddIf_rel (n : Nat) : RelCT isa (Runs VP₀ (StepW n)) vaddIf (Runs VP₀ (StepW n)) := by
  unfold Impl.Ed448.X86.vaddIf
  refine RelCT.seq (Runs.step (G := StepD n) (RelCT.taint (A := taint) (τr [.esp, .esi, .edi])
      (fun _ _ h => StepW.agree h) (by taint_decide)) ?_) (VG.X86.RelCT.ite ?_ ?_ ?_)
  · rintro σ s ⟨vt, he, hn⟩
    exact WP.mono (vdigit_ok vt.1.fe.fin.scr hn (vdigits_lt _ _) he (vt.1.dig n hn).2) fun t ⟨z, c, k, m⟩ =>
      ⟨⟨vt.of_mem k (by decide) (by decide) m, (k.1 _ (by decide)).trans he, hn⟩, c, z⟩
  · rintro s₁ s₂ ⟨σ₁, σ₂, hP, ⟨-, -, z₁⟩, ⟨-, -, z₂⟩⟩
    rw [eval_ne z₁, eval_ne z₂, hP.kv]
  · refine (RelCT.seq (Runs.step (P₀ := VP₀)
        (F := fun σ t => StepD n σ t ∧ Proof.Ed448.vdigits (KV σ) n ≠ 0) (G := StepW n)
        (RelCT.taint (A := taint) (τr [.esp, .edi, .ecx]) ?_ (by taint_decide))
        fun σ s h => entryW_ok h.1 h.2) (addTake6W n)).mono ?_ fun _ _ h => h
    · rintro s₁ s₂ ⟨σ₁, σ₂, hP, ⟨d₁, -⟩, ⟨d₂, -⟩⟩
      refine agree_regs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact d₁.1.1.1.fe.sp.trans (hP.hp.2.trans d₂.1.1.1.fe.sp.symm)
      · exact edi_eq d₁.1.1.1.fe.fin.scr (hP.hp.1 ▸ d₂.1.1.1.fe.fin.scr)
      · rw [d₁.2.1, d₂.2.1, hP.kv]
    · rintro s₁ s₂ ⟨⟨σ₁, σ₂, hP, d₁, d₂⟩, hc⟩
      have h1 : Proof.Ed448.vdigits (KV σ₁) n ≠ 0 := by rw [eval_ne d₁.2.2] at hc; simpa using hc
      exact ⟨σ₁, σ₂, hP, ⟨d₁, h1⟩, ⟨d₂, hP.kv ▸ h1⟩⟩
  · exact VG.X86.RelCT.nil fun s₁ s₂ ⟨⟨σ₁, σ₂, hP, d₁, d₂⟩, _⟩ => ⟨σ₁, σ₂, hP, d₁.1, d₂.1⟩

/-- In the loop over the bits, `n + 1` iterations left. -/
def LI (n : Nat) (σ s : State) : Prop := n < 456 ∧ VT σ s ∧ s.gpr .esi = BitVec.ofNat 32 (n + 1)

theorem vstep_rel (n : Nat) : RelCT isa (Runs VP₀ (LI n)) Impl.Ed448.X86.vstep
    (Runs VP₀ fun σ t => StepW n σ t ∧ t.zf = some (decide (n = 0))) := by
  unfold Impl.Ed448.X86.vstep
  refine RelCT.seq (Runs.step (G := StepW n) (RelCT.taint (A := taint) (τr [])
      (fun _ _ _ => agree_regs fun _ h => (List.not_mem_nil h).elim) (by taint_decide)) ?_)
    ((doubleW n).seq ((vcombIf_rel n).seq ((vaddIf_rel n).seq
      (Runs.step (RelCT.taint (A := taint) (τr [])
        (fun _ _ _ => agree_regs fun _ h => (List.not_mem_nil h).elim) (by taint_decide)) ?_))))
  · rintro σ s ⟨hn, vt, he⟩
    exact WP.mono (decCounter_ok (by omega_using [hn]) he) fun t ⟨c, g, m, r, w, _⟩ =>
      ⟨vt.of_mem (rs := [.esi]) ⟨fun r hr => g r (fun e => hr (by simp [e])), r, w⟩ (by decide) (by decide) m,
        c, hn⟩
  · rintro σ s ⟨vt, he, hn⟩
    refine wp_cmp rfl fun t f hz => WP.block_nil
      ⟨⟨vt.of_mem (f.rest []) (by decide) (by decide) f.mem, (congrFun f.gpr _).trans he, hn⟩, ?_⟩
    rw [hz, he, show BitVec.ofNat 32 n - (0 : BitVec 32) = BitVec.ofNat 32 n from BitVec.sub_zero _,
      ofNat_beq_zero (by omega_using [hn])]

theorem vloop_rel : RelCT isa (Runs VP₀ VT) Impl.Ed448.X86.vloop (Runs VP₀ VW) := by
  unfold Impl.Ed448.X86.vloop
  refine RelCT.seq (Runs.step (G := LI 455) (RelCT.taint (A := taint) (τr [])
    (fun _ _ _ => agree_regs fun _ h => (List.not_mem_nil h).elim) (by taint_decide)) ?_) ?_
  · intro σ s vt
    exact WP.mono (setCounter_ok s 456 (by decide)) fun t ⟨h1, h2, h3, h4, h5⟩ =>
      ⟨by decide, vt.of_mem (rs := [.esi]) ⟨fun r hr => h2 r (fun e => hr (by simp [e])), h4, h5⟩ (by decide)
        (by decide) h3, h1⟩
  refine RelCT.loop (M := isa) (fun n => Runs VP₀ (LI n)) (fun n => ?_) 455
  refine (vstep_rel n).mono (fun _ _ h => h) ?_
  rintro t₁ t₂ ⟨σ₁, σ₂, hP, ⟨w₁, z₁⟩, ⟨w₂, z₂⟩⟩
  rw [eval_ne z₁, eval_ne z₂]
  refine ⟨rfl, fun _ => ⟨σ₁, σ₂, hP, w₁.1.1, w₂.1.1⟩, fun hz => ?_⟩
  have hn0 : n ≠ 0 := fun h0 => by simp [h0] at hz
  have e : n - 1 + 1 = n := by omega_using [hn0]
  have hn := w₁.2.2
  exact ⟨n - 1, by omega_using [hn0], σ₁, σ₂, hP, ⟨by omega_using [hn], w₁.1, by rw [e]; exact w₁.2.1⟩,
    ⟨by omega_using [hn], w₂.1, by rw [e]; exact w₂.2.1⟩⟩

/-! ## The whole function -/

theorem copy6_rel : RelCT isa (Runs VP₀ VW) (Impl.X448.X86.ops [.copy (slot 6) Impl.X448.X86.X2])
    (Runs VP₀ VW) := by
  rw [show Impl.X448.X86.ops [.copy (slot 6) Impl.X448.X86.X2] =
    Impl.X448.X86.ops (([.copy 6 1] : List FieldOp).map FieldOp.impl) from rfl]
  exact opsVW _ (by decide) (by decide)

theorem vR_rel : RelCT isa (Runs VP₀ VW) (.block Impl.Ed448.X86.vR) (Runs VP₀ (FS bsV)) := by
  refine Runs.step (RelCT.taint (A := taint) (τr [.esp, .edi])
    (fun _ _ ⟨_, _, hP, f₁, f₂⟩ => FS.agree hP f₁.fe.fs f₂.fe.fs) (by taint_decide)) ?_
  intro σ s h
  exact WP.mono (vR_ok h.fe.fin.scr h.fe.fin.bounded h.rx h.ry) fun t ⟨k, b, _⟩ => FS.keep h.fe.fs k b

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
    exact WP.mono (vdoubleStep_ok f.1.scr f.1.ctx f.1.bounded (k := k) (by omega_using [hk]) e)
      fun t ⟨et, zt, kt, _, bt, _⟩ => ⟨⟨⟨f.1.scr.of_keeps kt (by decide), f.1.ctx.keep (kt.1 _ (by decide)), bt⟩,
        (kt.1 _ (by decide)).trans f.2⟩, et, zt, by omega_using [hk]⟩
  · rintro σ₁ σ₂ t₁ t₂ hP - ⟨f₁, e₁, z₁, b₁⟩ ⟨f₂, e₂, z₂, b₂⟩
    rw [eval_ne z₁, eval_ne z₂]
    refine ⟨rfl, fun _ => ⟨σ₁, σ₂, hP, f₁, f₂⟩, fun hz => ?_⟩
    have hk0 : k ≠ 0 := fun h0 => by simp [h0] at hz
    have e : k - 1 + 1 = k := by omega_using [hk0]
    exact ⟨k - 1, by omega_using [hk0], σ₁, σ₂, hP, ⟨f₁, e ▸ e₁, by omega_using [b₁]⟩, ⟨f₂, e ▸ e₂, by omega_using [b₁]⟩⟩

/-- In the comparison, `k + 1` passes left. -/
def CI (k : Nat) (σ s : State) : Prop := FS bsV σ s ∧ s.gpr .esi = BitVec.ofNat 32 (k + 1) ∧ k < 2

theorem CI.keep {k : Nat} {σ s t : State} (h : CI k σ s) (kt : Keeps workRegs s t) (ht : FS bsV σ t) :
    CI k σ t :=
  ⟨ht, (kt.1 _ (by decide)).trans h.2.1, h.2.2⟩

theorem vcmp_tr (k : Nat) : RelCT isa (Runs VP₀ (CI k)) Impl.Ed448.X86.vcmp fun _ _ => True := by
  unfold Impl.Ed448.X86.vcmp
  refine RelCT.seq (Runs.step (G := CI k) (field_tr (fun _ _ h => h.1) _ (by decide)) ?_) ?_
  · intro σ s h
    exact WP.mono (field_ok _ (by decide) h.1.1.scr h.1.1.ctx h.1.1.bounded) fun t ⟨kt, bt, _⟩ =>
      h.keep kt.regs (FS.keep h.1 kt bt)
  refine RelCT.seq (Runs.step (G := CI k) (RelCT.taint (A := taint) (τr [.esp, .edi])
    (fun _ _ ⟨_, _, hP, f₁, f₂⟩ => FS.agree hP f₁.1 f₂.1) (by taint_decide)) ?_) ?_
  · intro σ s h
    exact WP.mono (eqSlots_ok h.1.1.scr h.1.1.bounded 12 13 (by decide) (by decide) (by decide))
      fun t ⟨k', bt, _, _, kw⟩ =>
        h.keep kw ⟨⟨k'.scr h.1.1.scr, k'.ctx h.1.1.ctx, bt⟩, (k'.regs.1 _ (by decide)).trans h.1.2⟩
  rw [show Impl.X448.X86.ops [.copy (slot 0) (slot 6), .copy (slot 8) (slot 9)] =
    Impl.X448.X86.ops (([.copy 0 6, .copy 8 9] : List FieldOp).map FieldOp.impl) from rfl]
  refine RelCT.seq (Runs.step (G := CI k) (ops_tr (fun _ _ h => h.hp) (fun _ _ h => h.1) _) ?_)
    (RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs fun _ h => (List.not_mem_nil h).elim)
      (by taint_decide))
  intro σ s h
  exact WP.mono (ops_ok h.1.1.scr h.1.1.ctx h.1.1.bounded _) fun t ⟨kt, bt, _⟩ =>
    h.keep kt.regs (FS.keep h.1 kt bt)

theorem vfinish_tr : RelCT isa (Runs VP₀ (FS bsV)) Impl.Ed448.X86.vfinish fun _ _ => True := by
  unfold Impl.Ed448.X86.vfinish
  refine vdouble_rel.seq (RelCT.seq (Runs.step (G := CI 1) (RelCT.taint (A := taint) (τr [])
    (fun _ _ _ => agree_regs fun _ h => (List.not_mem_nil h).elim) (by taint_decide)) ?_)
    (RelCT.seq (R := Runs VP₀ (FS bsV)) (RelCT.loop (M := isa) (fun k => Runs VP₀ (CI k)) (fun k => ?_) 1)
      (RelCT.taint (A := taint) (τr [.esp, .edi]) (fun _ _ ⟨_, _, hP, f₁, f₂⟩ => FS.agree hP f₁ f₂)
        (by taint_decide))))
  · intro σ s h
    exact WP.mono (setCounter_ok s 2 (by decide)) fun t ⟨h1, h2, h3, h4, h5⟩ =>
      ⟨⟨FInv.of_counter h.1 h2 h3 h4 h5, (h2 _ (by decide)).trans h.2⟩, h1, by decide⟩
  refine Runs.then (G := fun σ t => FS bsV σ t ∧ t.gpr .esi = BitVec.ofNat 32 k ∧ t.zf = some (decide (k = 0)) ∧
      k < 2) (fun _ _ h => h) (vcmp_tr k) ?_ ?_
  · rintro σ s ⟨f, e, hk⟩
    exact WP.mono (vcmp_ok f.1.scr f.1.ctx f.1.bounded hk e)
      fun t ⟨et, zt, kt, _, bt, _⟩ => ⟨⟨⟨f.1.scr.of_keeps kt (by decide), f.1.ctx.keep (kt.1 _ (by decide)), bt⟩,
        (kt.1 _ (by decide)).trans f.2⟩, et, zt, hk⟩
  · rintro σ₁ σ₂ t₁ t₂ hP - ⟨f₁, e₁, z₁, b₁⟩ ⟨f₂, e₂, z₂, b₂⟩
    rw [eval_ne z₁, eval_ne z₂]
    refine ⟨rfl, fun _ => ⟨σ₁, σ₂, hP, f₁, f₂⟩, fun hz => ?_⟩
    have hk0 : k ≠ 0 := fun h0 => by simp [h0] at hz
    have e : k - 1 + 1 = k := by omega_using [hk0]
    exact ⟨k - 1, by omega_using [hk0], σ₁, σ₂, hP, ⟨f₁, e ▸ e₁, by omega_using [b₁]⟩, ⟨f₂, e ▸ e₂, by omega_using [b₁]⟩⟩

theorem vafter_tr : RelCT isa (Runs VP₀ (LoopAt · 0 ·)) Impl.Ed448.X86.vafter fun _ _ => True := by
  unfold Impl.Ed448.X86.vafter
  exact negA_rel.seq (vrecode_rel.seq (vtable_rel.seq (vloop_rel.seq (copy6_rel.seq (vR_rel.seq vfinish_tr)))))

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
