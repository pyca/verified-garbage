module

public import VerifiedGarbage.Impl.Ed25519.Arm.PointEncode
public import VerifiedGarbage.Impl.Ed25519.Arm.Power
public import VerifiedGarbage.Proof.Ed25519.Arm.FnCall
public import VerifiedGarbage.Proof.Ed25519.RootPower
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Ed25519.Arm.Power`, which this module and modules that import it used -/

section

/-! Merged from `Proof.Ed25519.Arm.PowerEnv`. -/

@[expose] public section

section
/-! Compositional field exponentiation and fixed-count squaring loops. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm
open VG.Proof.X25519 (sqn)

variable {umaal : Bool}

def opMul (o a b : Slot) (e : Env) : Env := Function.update e o (e a * e b)

/-- Field work and its fixed-count squaring counter. -/
structure IKeep (b : BitVec 32) (s t : State) : Prop where
  rest : Rest (.r10 :: fclob) s t
  frame : Frame [FA b] s.mem t.mem

theorem IKeep.trans {b : BitVec 32} {s t u : State} (h : IKeep b s t) (k : IKeep b t u) :
    IKeep b s u := ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

theorem IKeep.ctx {b : BitVec 32} {s t : State} (h : IKeep b s t) (hc : Ctx b s) : Ctx b t :=
  hc.of_rest h.rest (by decide)

theorem IKeep.of_counter {b : BitVec 32} {s t : State} (hr : Rest [.r10] s t)
    (hm : t.mem = s.mem) : IKeep b s t :=
  ⟨hr.mono (by decide), by rw [hm]; exact Frame.refl _ _⟩

def ISpec (b : BitVec 32) (c : Prog isa) (f : Env → Env) : Prop :=
  ∀ s, Ctx b s → AllLim s.mem b → WP isa c s fun t =>
    IKeep b s t ∧ AllLim t.mem b ∧ env t.mem b = f (env s.mem b)

theorem ISpec.seq {b : BitVec 32} {c₁ c₂ : Prog isa} {f g : Env → Env}
    (h₁ : ISpec b c₁ f) (h₂ : ISpec b c₂ g) : ISpec b (.seq c₁ c₂) fun e => g (f e) :=
  fun s hc hl => WP.seq (WP.mono (h₁ s hc hl) fun _ ⟨k₁, l₁, e₁⟩ =>
    WP.mono (h₂ _ (k₁.ctx hc) l₁) fun _ ⟨k₂, l₂, e₂⟩ =>
      ⟨k₁.trans k₂, l₂, by rw [e₂, e₁]⟩)

theorem mulcI_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (o a b : Slot) :
    WP isa (mulPc umaal o a b) s fun t => IKeep base s t ∧ AllLim t.mem base ∧
      t.gpr .r10 = s.gpr .r10 ∧ env t.mem base = opMul o a b (env s.mem base) :=
  WP.mono (fieldOp_ok hc hl (.mulc o a b)) fun _ ⟨hk, hlt, he⟩ =>
    ⟨⟨hk.rest.mono (by decide), hk.frame⟩, hlt, hk.rest.gpr _ (by decide), he⟩

theorem decR10_ok {s : State} {k : Nat} (hk : k < 2 ^ 32)
    (hb : s.gpr .r10 = BitVec.ofNat 32 (k + 1)) :
    WP isa (.block [.subs .r10 .r10 (.imm 1)]) s fun t =>
      t.gpr .r10 = BitVec.ofNat 32 k ∧ t.z = decide (k = 0) ∧
      Rest [.r10] s t ∧ t.mem = s.mem := by
  refine wp_subs (op2_imm (by decide)) fun t ht hz => WP.block_nil ?_
  have he : s.gpr .r10 - 1 = BitVec.ofNat 32 k := by
    rw [hb, BitVec.ofNat_add]
    change BitVec.ofNat 32 k + (1 : BitVec 32) - 1 = _
    exact BitVec.add_sub_cancel _ _
  exact ⟨ht.gpr.trans he, by rw [hz, he, ofNat_beq_zero hk], ht.rest (by decide), ht.mem⟩

def opSqn (o a : Slot) (n : Nat) (e : Env) : Env := Function.update e o (sqn (e a) n)

theorem opMul_update (o : Slot) (e : Env) (v : Spec.X25519.Fe) :
    opMul o o o (Function.update e o v) = Function.update e o (v * v) := by
  simp only [opMul, Function.update_self, Function.update_idem]

theorem mulcI (base : BitVec 32) (o a b : Slot) : ISpec base (mulPc umaal o a b) (opMul o a b) :=
  fun _ hc hl => WP.mono (fieldOp_ok hc hl (.mulc o a b)) fun _ ⟨hk, hlt, he⟩ =>
    ⟨⟨hk.rest.mono (by decide), hk.frame⟩, hlt, he⟩

open VG.Proof.X25519.Arm (Rest clob wp_movw)

theorem mulO_ok {b : BitVec 32} {s : State} (hc : Ctx b s) {S W : List Slot} (hl : LimOn s.mem b S)
    (o x y : Slot) (hx : x ∈ S) (hy : y ∈ S) (hw : o ∈ W) :
    WP isa (mulP umaal o x y) s fun t => Rest clob s t ∧ Frame (wRegions b W) s.mem t.mem ∧ LimOn t.mem b (o :: S) ∧
      env t.mem b = opMul o x y (env s.mem b) :=
  fieldOpOn_ok hc hl (.mul o x y) rfl (fun i hi => by
    rcases List.mem_cons.mp hi with rfl | hi
    · exact hx
    · rw [List.mem_singleton.mp hi]; exact hy) hw

theorem sqLoopO_ok {s₀ : State} {base : BitVec 32} (hc : Ctx base s₀) (o : Slot) (S : List Slot) {W : List Slot} (hw : o ∈ W)
    (x : Spec.X25519.Fe) (n : Nat) (hn : n < 65536) :
    ∀ m s, 1 ≤ m → m ≤ n → Rest (.r10 :: clob) s₀ s → Frame (wRegions base W) s₀.mem s.mem →
      LimOn s.mem base (o :: S) → s.gpr .r10 = BitVec.ofNat 32 m →
      env s.mem base = Function.update (env s₀.mem base) o (VG.Proof.X25519.sqn x (n - m)) →
      WP isa (.loop (.seq (mulP umaal o o o) (.block [.subs .r10 .r10 (.imm 1)])) .ne) s fun t =>
        Rest (.r10 :: clob) s₀ t ∧ Frame (wRegions base W) s₀.mem t.mem ∧ LimOn t.mem base (o :: S) ∧
        env t.mem base = Function.update (env s₀.mem base) o (VG.Proof.X25519.sqn x n) := by
  intro m s h1 h2 hr hf hl hb he
  refine WP.loop (M := isa) (Inv := fun m (s : State) =>
    1 ≤ m ∧ m ≤ n ∧ Rest (.r10 :: clob) s₀ s ∧ Frame (wRegions base W) s₀.mem s.mem ∧ LimOn s.mem base (o :: S) ∧
    s.gpr .r10 = BitVec.ofNat 32 m ∧
    env s.mem base = Function.update (env s₀.mem base) o (VG.Proof.X25519.sqn x (n - m))) ?_
    m s ⟨h1, h2, hr, hf, hl, hb, he⟩
  intro m s ⟨h1, h2, hr, hf, hl, hb, he⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega_using [h1]⟩
  have hcs : Ctx base s := hc.of_rest hr (by decide)
  refine WP.seq (WP.mono (mulO_ok hcs hl o o o List.mem_cons_self List.mem_cons_self hw)
    fun s1 ⟨r1, f1, l1, e1⟩ => ?_)
  refine WP.mono (decR10_ok (by omega_using [hn, h2]) ((r1.gpr _ (by decide)).trans hb)) fun s2 ⟨b2, z2, r2, mem2⟩ => ?_
  have k2 : Rest (.r10 :: clob) s₀ s2 := hr.trans ((r1.mono (by decide)).trans (r2.mono (by decide)))
  have f2 : Frame (wRegions base W) s₀.mem s2.mem := by rw [mem2]; exact hf.trans f1
  have l2 : LimOn s2.mem base (o :: S) := by
    rw [mem2]; exact l1.mono fun i hi => List.mem_cons_of_mem _ hi
  have e2 : env s2.mem base = Function.update (env s₀.mem base) o (VG.Proof.X25519.sqn x (n - m)) := by
    rw [mem2, e1, he, opMul_update]
    apply congrArg (Function.update (env s₀.mem base) o)
    rw [show n - m = (n - (m + 1)) + 1 by omega_using [h2]]
    rfl
  simp only [VG.Arm.eval, z2]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, k2, f2, l2, by rw [e2, Nat.sub_zero]⟩
  · exact .inr ⟨by simp only [decide_eq_false (by omega_using [hm] : m ≠ 0), Bool.not_false],
      m, by omega_using [], by omega_using [hm], by omega_using [h2], k2, f2, l2, b2, e2⟩

theorem sqn_sq (x : Spec.X25519.Fe) : ∀ m, VG.Proof.X25519.sqn (x * x) m = VG.Proof.X25519.sqn x (m + 1)
  | 0 => rfl
  | m + 1 => by
    show VG.Proof.X25519.sqn (x * x) m * VG.Proof.X25519.sqn (x * x) m = _
    rw [sqn_sq x m]; rfl

theorem sqrFn_noCalls (umaal : Bool) (o : Slot) : (sqrFn umaal o).noCalls = true := by
  cases umaal <;> simp [sqrFn, asFn, sqLoop, mulP, Impl.Ed25519.Arm.mulIn, mulBodyU, Impl.X25519.Arm.mulAt,
    Impl.Ed25519.Arm.mul, Code.noCalls]

/-- `vg_gf25519_r16_sqr{o}`, entered with `n` in `r10`: slot `o` squared `n`
times. -/
theorem sqrFn_ok {b : BitVec 32} (o : Slot) {n : Nat} (hn : 1 ≤ n) (hn' : n < 65536) {s : State}
    (hc : Ctx b s) (hl : AllLim s.mem b) (h10 : s.gpr .r10 = BitVec.ofNat 32 n) :
    WP isa (sqrFn umaal o) s fun t => Rest fnClob s t ∧ Frame [FA b] s.mem t.mem ∧ AllLim t.mem b ∧
      env t.mem b = opSqn o o n (env s.mem b) :=
  WP.mono (asFnG_ok (c := true) (R := .r10 :: clob) (S := o :: allSlots) (W := [o]) (f := opSqn o o n)
      (fun r hr => by revert r; decide)
      (fun s₁ hc₁ hl₁ hg => sqLoopO_ok (umaal := umaal) hc₁ o allSlots (List.mem_singleton_self o) (env s₁.mem b o) n hn' n s₁
        hn (Nat.le_refl _) (Rest.refl _ _) (Frame.refl _ _) hl₁ (by rw [hg]; exact h10)
        (by rw [Nat.sub_self]; exact (Function.update_eq_self _ _).symm)) hc (LimOn.of_all hl _))
    fun _ ⟨hr, hf, hl', he⟩ => ⟨hr, frameS_FA hf, hl'.all fun i => List.mem_cons_of_mem _ (mem_allSlots i), he⟩

/-- `sqrCall o n`: slot `o` squared `n` times. -/
theorem sqrCallI (base : BitVec 32) (o : Slot) (n : Nat) (hn : 1 ≤ n) (hn' : n < 65536) :
    ISpec base (sqrCall umaal o n) (opSqn o o n) := by
  intro s hc hl
  refine WP.seq (wp_movw fun s1 h1 => WP.block_nil ?_)
  have b1 : s1.gpr .r10 = BitVec.ofNat 32 n := by
    rw [h1.gpr]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega_using [hn'] : n < 2 ^ 16)]
  have k1 : IKeep base s s1 := IKeep.of_counter (h1.rest (by decide)) h1.mem
  have hc1 : Ctx base s1 := k1.ctx hc
  have hl1 : AllLim s1.mem base := by rw [h1.mem]; exact hl
  refine WP.mono (fnCallG_ok (fun t ht hlt h10 => sqrFn_ok o hn hn' ht hlt (h10.trans b1))
    (sqrFn_noCalls umaal o) hc1 hl1) fun t ⟨kt, lt, et⟩ => ⟨k1.trans ⟨kt.rest.mono (by decide), kt.frame⟩, lt, ?_⟩
  rw [et, h1.mem]

/-- `sqnLoop o n`: slot `o` squared `n` times. -/
theorem sqnLoopI (base : BitVec 32) (o : Slot) (n : Nat) (hn : 1 ≤ n) (hn' : n < 65536) :
    ISpec base (sqnLoop umaal o n) (opSqn o o n) := sqrCallI base o n hn hn'

/-- `sqn o a n`: slot `o` = slot `a` squared `n` times. -/
theorem sqnI (base : BitVec 32) (o a : Slot) (n : Nat) (hn : 2 ≤ n) (hn' : n < 65536) :
    ISpec base (Impl.Ed25519.Arm.sqn umaal o a n) (opSqn o a n) := by
  have h := (mulcI (umaal := umaal) base o a a).seq
    (sqrCallI (umaal := umaal) base o (n - 1) (by omega_using [hn]) (by omega_using [hn']))
  refine fun s hc hl => WP.mono (h s hc hl) fun t ⟨k, l, e⟩ => ⟨k, l, ?_⟩
  rw [e]
  simp only [opSqn, opMul, Function.update_self, Function.update_idem, sqn_sq]
  rw [show n - 1 + 1 = n by omega_using [hn]]

end VG.Proof.Ed25519.Arm
end

/-! The shared addition chain computes inversion and square-root powers. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

variable {umaal : Bool}

def power250Env (e : Env) : Env :=
  opMul 15 16 15 (opSqn 16 16 50 (opMul 16 17 16 (opSqn 17 16 100
    (opMul 16 16 15 (opSqn 16 15 50 (opMul 15 16 15 (opSqn 16 16 10 (opMul 16 17 16 (opSqn 17 16 20
    (opMul 16 16 15 (opSqn 16 15 10 (opMul 15 16 15 (opSqn 16 15 5 (opMul 15 15 16
    (opMul 16 14 14 (opMul 14 14 15 (opMul 15 2 15 (opMul 15 15 15 (opMul 15 14 14
    (opMul 14 2 2 e))))))))))))))))))))

/-! ## The chain

`chain250I`: the chain, each product a call of `vg_gf25519_r16_mul`
(`mulcI`, `sqnI`), computes `power250Env`. -/

theorem chain250I (base : BitVec 32) : ISpec base (chain250 umaal) power250Env := by
  have h : ISpec base (chain250 umaal) _ :=
    (mulcI base 14 2 2).seq <|
    (mulcI base 15 14 14).seq <|
    (mulcI base 15 15 15).seq <|
    (mulcI base 15 2 15).seq <|
    (mulcI base 14 14 15).seq <|
    (mulcI base 16 14 14).seq <|
    (mulcI base 15 15 16).seq <|
    (sqnI base 16 15 5 (by decide) (by decide)).seq <|
    (mulcI base 15 16 15).seq <|
    (sqnI base 16 15 10 (by decide) (by decide)).seq <|
    (mulcI base 16 16 15).seq <|
    (sqnI base 17 16 20 (by decide) (by decide)).seq <|
    (mulcI base 16 17 16).seq <|
    (sqnI base 16 16 10 (by decide) (by decide)).seq <|
    (mulcI base 15 16 15).seq <|
    (sqnI base 16 15 50 (by decide) (by decide)).seq <|
    (mulcI base 16 16 15).seq <|
    (sqnI base 17 16 100 (by decide) (by decide)).seq <|
    (mulcI base 16 17 16).seq <|
    (sqnI base 16 16 50 (by decide) (by decide)).seq <|
    (mulcI base 15 16 15)
  exact h

def invEnv (e : Env) : Env := opMul 15 15 14 (opSqn 15 15 5 (power250Env e))
def rootEnv (e : Env) : Env := opMul 15 15 2 (opSqn 15 15 2 (power250Env e))

theorem invert_spec (base : BitVec 32) : ISpec base (invert umaal) invEnv := by
  have h : ISpec base _ _ := (chain250I (umaal := umaal) base).seq
    ((sqnLoopI (umaal := umaal) base 15 5 (by decide) (by decide)).seq (mulcI (umaal := umaal) base 15 15 14))
  exact h

theorem rootPower_spec (base : BitVec 32) : ISpec base (Impl.Ed25519.Arm.rootPower umaal) rootEnv := by
  have h : ISpec base _ _ := (chain250I (umaal := umaal) base).seq
    ((sqnLoopI (umaal := umaal) base 15 2 (by decide) (by decide)).seq (mulcI (umaal := umaal) base 15 15 2))
  exact h

theorem invEnv_eval (e : Env) : invEnv e 15 = VG.Proof.X25519.invert (e 2) := by
  simp only [↓reduceIte, invEnv, power250Env, opMul, opSqn, Function.update_apply]
  rfl

theorem rootEnv_eval (e : Env) : rootEnv e 15 = VG.Proof.Ed25519.rootPower (e 2) := by
  simp only [↓reduceIte, rootEnv, power250Env, opMul, opSqn, Function.update_apply]
  rfl

end VG.Proof.Ed25519.Arm

end

end

/-! Affine conversion using the verified inversion chain. -/

@[expose] public section

namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

variable {umaal : Bool}

theorem IKeep.of_keep {b : BitVec 32} {s t : State} (h : Keep b s t) : IKeep b s t :=
  ⟨h.rest.mono (by decide), h.frame⟩

theorem affine_eval (e : Env) :
    evalOps affineOps e 0 = e 0 * e 15 ∧ evalOps affineOps e 1 = e 1 * e 15 := ⟨rfl, rfl⟩

theorem invEnv_xy (e : Env) : invEnv e 0 = e 0 ∧ invEnv e 1 = e 1 := by
  simp only [↓reduceIte, invEnv, power250Env, opMul, opSqn, Function.update_apply]
  exact ⟨rfl, rfl⟩

theorem pointAffine_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base) :
    WP isa (pointAffine umaal) s fun t => IKeep base s t ∧ AllLim t.mem base ∧
      env t.mem base 0 = env s.mem base 0 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2) ∧
      env t.mem base 1 = env s.mem base 1 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2) := by
  refine WP.seq (WP.mono (invert_spec base s hc hl) fun t ⟨hk, hlt, hv⟩ => ?_)
  refine WP.mono (fieldCode_ok affineOps (hk.ctx hc) hlt) fun u ⟨ku, hlu, vu⟩ => ?_
  refine ⟨hk.trans (IKeep.of_keep ku), hlu, ?_, ?_⟩
  · rw [vu, (affine_eval _).1, hv, (invEnv_xy _).1, invEnv_eval, Proof.X25519.invert_eq]
  · rw [vu, (affine_eval _).2, hv, (invEnv_xy _).2, invEnv_eval, Proof.X25519.invert_eq]

end VG.Proof.Ed25519.Arm
