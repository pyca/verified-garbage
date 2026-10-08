import VerifiedGarbage.Proof.AesCbc.Arm.Body
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint

/-!
# AES-CBC on ARMv7: constant time

Two runs from states that agree on the public arguments are related piece by
piece (`RelCT`): the taint analysis covers the code between the calls, from
the public arguments for the prologue and from the registers the correctness
proof pins to them (`LInv`) afterwards, and each call of a block function, in
its frame, is constant time by its own proof (`Proof.AesOcb.Arm.blk_rel`).
`whole_ct`: if one run of `body` is (`BodyCt`), `whole body` is.
-/

namespace VG.Proof.AesCbc.Arm

open VG VG.Arm VG.Impl.AesCbc.Arm
open VG.Impl.CmacAes.Arm (save setup restore advance)
open VG.Proof.CmacAes.Arm (W R Dp N S argsR)
open VG.Proof.AesOcb.Arm (BlkFn BlkCall BlkPost blkFrame blk_call blk_rel encF decF)
open VG.Proof.MdStream.Arm (eval_eq eval_ne)

/-- The registers holding our variables in the loop. -/
abbrev vars : List Reg := [.r4, .r5, .r6, .r7, .r8, .r10]

/-- Those the code after a call uses. -/
abbrev postVars : List Reg := [.r6, .r7, .r8, .r10]

section
variable {M : Mode} {s₀ s₀' : State} (hq : (modeArm M).pub s₀ s₀')
include hq

theorem pub_sp : s₀.sp = s₀'.sp := hq.1
theorem pub_W : W s₀ = W s₀' := hq.2.1
theorem pub_r1 : s₀.gpr .r1 = s₀'.gpr .r1 := hq.2.2.1
theorem pub_R : R s₀ = R s₀' := by rw [R, R, pub_r1 hq]
theorem pub_Iv : Iv s₀ = Iv s₀' := hq.2.2.2.1
theorem pub_Dp : Dp s₀ = Dp s₀' := hq.2.2.2.2.1
theorem pub_N : N s₀ = N s₀' := by rw [N, N, hq.2.2.2.2.2.1]
theorem pub_S : S s₀ = S s₀' := hq.2.2.2.2.2.2
theorem pub_D32 (k : Nat) : D32 s₀ k = D32 s₀' k := by rw [D32, D32, pub_Dp hq]

/-- The registers the invariant pins agree in both runs. -/
theorem LInv.agree {k : Nat} {s₁ s₂ : State} (h₁ : LInv M s₀ k s₁) (h₂ : LInv M s₀' k s₂) :
    ∀ r ∈ vars, s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [vars, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.r4, h₂.r4, pub_W hq]
  · rw [h₁.r5, h₂.r5, pub_r1 hq]
  · rw [h₁.r6, h₂.r6, pub_Iv hq]
  · rw [h₁.r7, h₂.r7, pub_Dp hq]
  · rw [h₁.r8, h₂.r8, pub_N hq]
  · rw [h₁.r10, h₂.r10, pub_S hq]

end

/-- The relation before a block, in two runs. -/
def BRel (M : Mode) (s₀ s₀' : State) (k : Nat) (s₁ s₂ : State) : Prop :=
  (k < N s₀ ∧ LInv M s₀ k s₁) ∧ (k < N s₀' ∧ LInv M s₀' k s₂)

/-- One run of `body` from `k` blocks is constant time. -/
def BodyCt (M : Mode) (body : Prog isa) : Prop :=
  ∀ {s₀ s₀' : State}, UPre s₀ → UPre s₀' → (modeArm M).pub s₀ s₀' → ∀ k : Nat,
    RelCT isa (BRel M s₀ s₀' k) body fun _ _ => True

/-! ## One block -/

/-- What is known after the code before the call, and after the call. -/
structure After (s₀ : State) (k : Nat) (s : State) : Prop where
  r6 : s.gpr .r6 = Iv s₀
  r7 : s.gpr .r7 = D32 s₀ k
  r8 : s.gpr .r8 = BitVec.ofNat 32 (N s₀ - k)
  r10 : s.gpr .r10 = S s₀
  sp : s.sp = s₀.sp

/-- What is known between the code before the call and the call, on the
block at `D`. -/
structure Mid (s₀ : State) (k : Nat) (D : BitVec 32) (s : State) : Prop where
  pre : BlkCall s (W s₀) D (S s₀) (R s₀) 1
  after : After s₀ k s

theorem Mid.of {M : Mode} {s₀ : State} {k : Nat} {s s₁ : State} {m : Mem} (h : LInv M s₀ k s)
    (a : PreA s₀ k s m s₁) : Mid s₀ k (D32 s₀ k) s₁ :=
  ⟨a.pre, ⟨by rw [a.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r6],
    by rw [a.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r7],
    by rw [a.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r8],
    by rw [a.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r10],
    by rw [a.sp, h.sp]⟩⟩

theorem After.of {F : BlkFn} {s₀ : State} {k : Nat} {D : BitVec 32} {s s' : State} (h : Mid s₀ k D s)
    (c : BlkPost F s (W s₀) D (S s₀) (R s₀) 1 s') : After s₀ k s' :=
  ⟨by rw [c.saved .r6 (by simp [preserved]) (by decide), h.after.r6],
    by rw [c.saved .r7 (by simp [preserved]) (by decide), h.after.r7],
    by rw [c.saved .r8 (by simp [preserved]) (by decide), h.after.r8],
    by rw [c.saved .r10 (by simp [preserved]) (by decide), h.after.r10], by rw [c.sp, h.after.sp]⟩

/-- A body: code before the call (`pre`), the call of `F` in its frame on the
block at `D s₀ k` (public), and code after it (`post`), constant time when
`pre`'s addresses and branches depend only on the registers the invariant
pins and `post`'s on `r6`, `r7`, `r8` and `r10`. -/
theorem body_ct {M : Mode} (F : BlkFn) {pre post : List Instr} {D : State → Nat → BitVec 32}
    (pubD : ∀ {s₀ s₀' : State}, (modeArm M).pub s₀ s₀' → ∀ k, D s₀ k = D s₀' k)
    (hA : ∃ h, (taint.check (Taint.ofRegs vars) (.block pre) h).isSome = true)
    (hB : ∃ h, (taint.check (Taint.ofRegs postVars) (.block post) h).isSome = true)
    (wpA : ∀ {s₀ : State}, UPre s₀ → ∀ {k : Nat}, k < N s₀ → ∀ {s : State}, LInv M s₀ k s →
      WP isa (.block pre) s (Mid s₀ k (D s₀ k)))
    {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : (modeArm M).pub s₀ s₀') (k : Nat) :
    RelCT isa (BRel M s₀ s₀' k) (.seq (.block pre) (.seq (blkFrame F) (.block post))) fun _ _ => True := by
  obtain ⟨_, hB⟩ := hB
  have a := rel_agree (F := fun s => k < N s₀ ∧ LInv M s₀ k s) (F' := fun s => k < N s₀' ∧ LInv M s₀' k s)
    (G := Mid s₀ k (D s₀ k)) (G' := Mid s₀' k (D s₀' k)) (Taint.ofRegs vars)
    (fun _ _ h h' => Taint.agree_ofRegs (LInv.agree hq h.2 h'.2)) hA
    (fun _ h => wpA hp h.1 h.2) (fun _ h => wpA hp' h.1 h.2)
  have c := rel_wp (F := Mid s₀ k (D s₀ k)) (F' := Mid s₀' k (D s₀' k)) (G := After s₀ k) (G' := After s₀' k)
    (blk_rel F fun s₁ s₂ h => ⟨W s₀, D s₀ k, S s₀, R s₀, 1, h.1.pre,
      by rw [pub_W hq, pubD hq k, pub_S hq, pub_R hq]; exact h.2.pre,
      by rw [h.1.after.sp, h.2.after.sp, pub_sp hq]⟩)
    (fun _ h => WP.mono (blk_call F h.pre) fun _ hc => After.of h hc)
    (fun _ h => WP.mono (blk_call F h.pre) fun _ hc => After.of h hc)
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => After s₀ k s₁ ∧ After s₀' k s₂) (Taint.ofRegs postVars)
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [postVars, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.1.r6, h.2.r6, pub_Iv hq]
      · rw [h.1.r7, h.2.r7, pub_D32 hq]
      · rw [h.1.r8, h.2.r8, pub_N hq]
      · rw [h.1.r10, h.2.r10, pub_S hq]) hB
  exact a.seq ((c.mono (fun _ _ h => ⟨h.1, h.2⟩) fun _ _ h => ⟨h.1, h.2⟩).seq
    (b.mono (fun _ _ h => h) fun _ _ h => h))

theorem encPre_taint : ∃ h, (taint.check (Taint.ofRegs vars) (.block encPre) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem encPost_taint : ∃ h, (taint.check (Taint.ofRegs postVars) (.block encPost) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem decPre_taint : ∃ h, (taint.check (Taint.ofRegs vars) (.block decPre) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem decPost_taint : ∃ h, (taint.check (Taint.ofRegs postVars) (.block decPost) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem encBody_ct : BodyCt (cbcMode true) encBody := fun hp hp' hq k => by
  rw [encBody, encFrame_eq]
  exact body_ct encF (fun hq k => pub_D32 hq k) encPre_taint encPost_taint
    (@fun _ hp _ hk _ h => WP.mono (encA_wp hp hk h) fun _ a => Mid.of h a) hp hp' hq k

theorem decBody_ct : BodyCt (cbcMode false) decBody := fun hp hp' hq k => by
  rw [decBody, decFrame_eq]
  exact body_ct decF (fun hq k => pub_D32 hq k) decPre_taint decPost_taint
    (@fun _ hp _ hk _ h => WP.mono (decA_wp hp hk h) fun _ a => Mid.of h a) hp hp' hq k

/-! ## The loop -/

/-- The loop's relation, with the number of iterations left. -/
def LRel (M : Mode) (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ BRel M s₀ s₀' k s₁ s₂

theorem loop_ct {M : Mode} {body : Prog isa} (hb : BodyOk M body) (hc : BodyCt M body)
    {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : (modeArm M).pub s₀ s₀') (n : Nat) :
    RelCT isa (LRel M s₀ s₀' n) (.loop body .ne)
      fun s₁ s₂ => LInv M s₀ (N s₀) s₁ ∧ LInv M s₀' (N s₀') s₂ := by
  refine RelCT.loop (M := isa) (LRel M s₀ s₀') (fun n => ?_) n
  have hN := pub_N hq
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : LRel M s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  have ct := (hc hp hp' hq k).wp
    (F₁ := fun (s : State) => (LInv M s₀ (k + 1) s ∧ s.z = decide (N s₀ - (k + 1) = 0)) ∧ k < N s₀)
    (F₂ := fun (s : State) => LInv M s₀' (k + 1) s ∧ s.z = decide (N s₀' - (k + 1) = 0))
    fun _ _ h => ⟨WP.mono (hb hp h.1.1 h.1.2) fun _ r => ⟨r, h.1.1⟩, hb hp' h.2.1 h.2.2⟩
  refine ct.mono (fun _ _ h => h.2) fun s₁ s₂ ⟨_, ⟨⟨l₁, z₁⟩, hk⟩, ⟨l₂, z₂⟩⟩ => ?_
  have e₁ : isa.eval .ne s₁ = some !decide (N s₀ - (k + 1) = 0) := by
    show VG.Arm.eval .ne s₁ = _; rw [eval_ne, z₁]
  have e₂ : isa.eval .ne s₂ = some !decide (N s₀ - (k + 1) = 0) := by
    show VG.Arm.eval .ne s₂ = _; rw [eval_ne, z₂, ← hN]
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : N s₀ = k + 1 := by
      have : N s₀ - (k + 1) = 0 := by simpa using hf
      omega
    exact ⟨h0 ▸ l₁, by rw [← hN, h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : N s₀ - (k + 1) ≠ 0 := by simpa using ht
    exact ⟨N s₀ - (k + 1), by omega, k + 1, rfl, ⟨by omega, l₁⟩, ⟨by omega, l₂⟩⟩

/-! ## The whole function -/

theorem prologue_taint : ∃ h, (taint.check (argTaint [.r0, .r1, .r2, .r3] 8) (.block (save ++ setup)) h).isSome =
    true := ⟨_, by taint_decide⟩

theorem epilogue_taint : ∃ h, (taint.check (Taint.ofRegs [.r10]) (.block restore) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem nil_taint : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true := ⟨_, by taint_decide⟩

theorem whole_rel {M : Mode} {body : Prog isa} (hb : BodyOk M body) (hc : BodyCt M body)
    {s₀ s₀' : State} (h0 : (modeArm M).pre s₀) (h0' : (modeArm M).pre s₀')
    (hq : (modeArm M).pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (whole body) fun _ _ => True := by
  have hp := UPre.of h0
  have hp' := UPre.of h0'
  obtain ⟨_, hepi⟩ := epilogue_taint
  obtain ⟨_, hnil⟩ := nil_taint
  have hN := pub_N hq
  have hsp := pub_sp hq
  have wfA : ∀ {s : State}, UPre s →
      s.sp.toNat + 8 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 8⟩ r := fun {s} h => by
    have e : (⟨State.addr s.sp, 8⟩ : Region) = argsR s := by simp [stackArgAddr]
    refine ⟨h.sp_fit, ?_⟩
    rw [e, h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact h.iv_args.symm
    · exact h.data_args.symm
    · exact h.scr_args.symm
  have pro := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀')
    (G := fun s => LInv M s₀ 0 s ∧ s.z = decide (N s₀ = 0))
    (G' := fun s => LInv M s₀' 0 s ∧ s.z = decide (N s₀' = 0))
    (argTaint [.r0, .r1, .r2, .r3] 8)
    (fun s s' e e' => by
      subst e e'
      refine agree_argTaint (fun r hr => ?_) hsp (wfA hp) (wfA hp')
        (argMem_of (j := 2) hsp hp.sp_fit fun i hi => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hq.2.1
        · exact hq.2.2.1
        · exact hq.2.2.2.1
        · exact hq.2.2.2.2.1
      · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · exact hq.2.2.2.2.2.1
        · exact hq.2.2.2.2.2.2) prologue_taint
    (fun s e => by rw [e]; exact prologue_wp hp) (fun s e => by rw [e]; exact prologue_wp hp')
  have ev {s : State} (h : s.z = decide (N s₀ = 0)) : isa.eval .eq s = some (decide (N s₀ = 0)) := by
    show VG.Arm.eval .eq s = _; rw [eval_eq, h]
  have ev' {s : State} (h : s.z = decide (N s₀' = 0)) : isa.eval .eq s = some (decide (N s₀ = 0)) := by
    show VG.Arm.eval .eq s = _; rw [eval_eq, h, hN]
  have nil := RelCT.taint (A := taint)
    (P := fun a b => ((LInv M s₀ 0 a ∧ a.z = decide (N s₀ = 0)) ∧
      (LInv M s₀' 0 b ∧ b.z = decide (N s₀' = 0))) ∧ isa.eval .eq a = some true)
    (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs fun r hr => by simp at hr) hnil
  have mid : RelCT isa (fun a b => (LInv M s₀ 0 a ∧ a.z = decide (N s₀ = 0)) ∧
      (LInv M s₀' 0 b ∧ b.z = decide (N s₀' = 0)))
      (.ite .eq (.block []) (.loop body .ne)) (fun a b => LInv M s₀ (N s₀) a ∧ LInv M s₀' (N s₀') b) := by
    refine RelCT.ite (fun a b h => by rw [ev h.1.2, ev' h.2.2]) ?_ ?_
    · refine (nil.wp (F₁ := LInv M s₀ (N s₀)) (F₂ := LInv M s₀' (N s₀')) fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : N s₀ = 0 := by
        have := h.2; rw [ev h.1.1.2] at this; simpa using this
      exact ⟨WP.block_nil (h0 ▸ h.1.1.1), WP.block_nil (by rw [← hN, h0]; exact h.1.2.1)⟩
    · refine (loop_ct hb hc hp hp' hq (N s₀ - 0)).mono (fun a b h => ⟨0, rfl, ⟨?_, h.1.1.1⟩, ⟨?_, h.1.2.1⟩⟩)
        fun _ _ h => h
      all_goals
        have := h.2; rw [ev h.1.1.2] at this
        have : N s₀ ≠ 0 := by simpa using this
        omega
  have epi := RelCT.taint (A := taint) (P := fun a b => LInv M s₀ (N s₀) a ∧ LInv M s₀' (N s₀') b)
    (Taint.ofRegs [.r10]) (fun a b h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.r10, h.2.r10, pub_S hq]) hepi
  exact (pro.mono (fun _ _ h => h) fun _ _ h => h).seq (mid.seq epi)

theorem whole_ct {M : Mode} {body : Prog isa} (hb : BodyOk M body) (hc : BodyCt M body) :
    ConstantTime isa (modeArm M).pre (modeArm M).pub (whole body) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (whole_rel hb hc h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesCbc.Arm
