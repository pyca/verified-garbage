import VerifiedGarbage.Impl.Ed25519.Arm.Power
import VerifiedGarbage.Proof.Ed25519.Arm.FnCall
import VerifiedGarbage.Proof.X25519.Invert
import VerifiedGarbage.Proof.Ed25519.RootPower

/-! Merged from `Proof.Ed25519.Arm.PowerEnv`. -/
section
/-! Compositional field exponentiation and fixed-count squaring loops. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm
open VG.Proof.X25519 (sqn)

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

theorem mulI_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (o a b : Slot) :
    WP isa (mulP o a b) s fun t => IKeep base s t ∧ AllLim t.mem base ∧
      t.gpr .r10 = s.gpr .r10 ∧ env t.mem base = opMul o a b (env s.mem base) :=
  WP.mono (fieldOp_ok hc hl (.mul o a b)) fun _ ⟨hk, hlt, he⟩ =>
    ⟨⟨hk.rest.mono (by decide), hk.frame⟩, hlt, hk.rest.gpr _ (by decide), he⟩

theorem mulI (base : BitVec 32) (o a b : Slot) : ISpec base (mulP o a b) (opMul o a b) :=
  fun _ hc hl => WP.mono (mulI_ok hc hl o a b) fun _ ⟨hk, hlt, _, he⟩ => ⟨hk, hlt, he⟩

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

theorem sqLoop_ok {s₀ : State} {base : BitVec 32} (hc : Ctx base s₀)
    (o : Slot) (x : Spec.X25519.Fe) (n : Nat) (hn : n < 65536) :
    ∀ m s, 1 ≤ m → m < n → IKeep base s₀ s → AllLim s.mem base →
      s.gpr .r10 = BitVec.ofNat 32 m →
      env s.mem base = Function.update (env s₀.mem base) o (sqn x (n - m)) →
      WP isa (.loop (.seq (mulP o o o) (.block [.subs .r10 .r10 (.imm 1)])) .ne) s fun t =>
        IKeep base s₀ t ∧ AllLim t.mem base ∧
        env t.mem base = Function.update (env s₀.mem base) o (sqn x n) := by
  intro m s h1 h2 hk hl hb he
  refine WP.loop (M := isa) (Inv := fun m (s : State) =>
    1 ≤ m ∧ m < n ∧ IKeep base s₀ s ∧ AllLim s.mem base ∧
    s.gpr .r10 = BitVec.ofNat 32 m ∧
    env s.mem base = Function.update (env s₀.mem base) o (sqn x (n - m))) ?_
    m s ⟨h1, h2, hk, hl, hb, he⟩
  intro m s ⟨h1, h2, hk, hl, hb, he⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine WP.seq (WP.mono (mulI_ok (hk.ctx hc) hl o o o) fun s1 ⟨k1, l1, b1, e1⟩ => ?_)
  refine WP.mono (decR10_ok (by omega) (b1.trans hb)) fun s2 ⟨b2, z2, r2, mem2⟩ => ?_
  have k2 : IKeep base s₀ s2 := hk.trans (k1.trans (IKeep.of_counter r2 mem2))
  have l2 : AllLim s2.mem base := by rw [mem2]; exact l1
  have e2 : env s2.mem base = Function.update (env s₀.mem base) o (sqn x (n - m)) := by
    rw [mem2, e1, he, opMul_update]
    apply congrArg (Function.update (env s₀.mem base) o)
    rw [show n - m = (n - (m + 1)) + 1 by omega]
    rfl
  simp only [VG.Arm.eval, z2]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, k2, l2, by rw [e2, Nat.sub_zero]⟩
  · exact .inr ⟨by simp only [decide_eq_false (by omega : m ≠ 0), Bool.not_false],
      m, by omega, by omega, by omega, k2, l2, b2, e2⟩

theorem sqnI (base : BitVec 32) (o a : Slot) (n : Nat) (hn : 2 ≤ n) (hn' : n < 65536) :
    ISpec base (Impl.Ed25519.Arm.sqn o a n) (opSqn o a n) := by
  intro s hc hl
  refine WP.seq (WP.mono (mulI_ok hc hl o a a) fun s1 ⟨k1, l1, _, e1⟩ => ?_)
  refine WP.seq (wp_movw fun s2 h2 => WP.block_nil ?_)
  have b2 : s2.gpr .r10 = BitVec.ofNat 32 (n - 1) := by
    rw [h2.gpr]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : n - 1 < 2 ^ 16)]
  have k2 : IKeep base s s2 := k1.trans (IKeep.of_counter (h2.rest (by decide)) h2.mem)
  refine sqLoop_ok hc o (env s.mem base a) n hn' (n - 1) s2 (by omega) (by omega) k2
    (by rw [h2.mem]; exact l1) b2 ?_
  rw [h2.mem, e1, show n - (n - 1) = 1 by omega]
  rfl

end VG.Proof.Ed25519.Arm
end

/-! The shared addition chain computes inversion and square-root powers. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

def power250Env (e : Env) : Env :=
  opMul 15 16 15 (opSqn 16 16 50 (opMul 16 17 16 (opSqn 17 16 100
    (opMul 16 16 15 (opSqn 16 15 50 (opMul 15 16 15 (opSqn 16 16 10 (opMul 16 17 16 (opSqn 17 16 20
    (opMul 16 16 15 (opSqn 16 15 10 (opMul 15 16 15 (opSqn 16 15 5 (opMul 15 15 16
    (opMul 16 14 14 (opMul 14 14 15 (opMul 15 2 15 (opMul 15 15 15 (opMul 15 14 14
    (opMul 14 2 2 e))))))))))))))))))))

/-! ## The chain as a function

`chain250O`: the chain on the slots with limbs below `2^16` (`LimOn`), from
slot 2's, changing no memory but `FA0` (`OSpec`); then `pow250Fn_ok`, the
chain as a function (`asFn_ok`), and `power250_spec`, its call, as the
inlined chain was. -/

open VG.Proof.X25519.Arm (Rest clob wp_movw)

/-- `c` maps the elements by `f`, from the slots `S` with limbs below `2^16`
to the slots `S'`, changing no register but the counter and X25519's `clob`
and no memory but the slots `W` and `ACC`. -/
def OSpec (b : BitVec 32) (W : List Slot) (c : Prog isa) (S S' : List Slot) (f : Env → Env) : Prop :=
  ∀ s, Ctx b s → LimOn s.mem b S → WP isa c s fun t =>
    Rest (.r10 :: clob) s t ∧ Frame (wRegions b W) s.mem t.mem ∧ LimOn t.mem b S' ∧
      env t.mem b = f (env s.mem b)

theorem OSpec.seq {b : BitVec 32} {W : List Slot} {c₁ c₂ : Prog isa} {S S₁ S₂ : List Slot} {f g : Env → Env}
    (h₁ : OSpec b W c₁ S S₁ f) (h₂ : OSpec b W c₂ S₁ S₂ g) : OSpec b W (.seq c₁ c₂) S S₂ fun e => g (f e) :=
  fun s hc hl => WP.seq (WP.mono (h₁ s hc hl) fun _ ⟨r₁, f₁, l₁, e₁⟩ =>
    WP.mono (h₂ _ (hc.of_rest r₁ (by decide)) l₁) fun _ ⟨r₂, f₂, l₂, e₂⟩ =>
      ⟨r₁.trans r₂, f₁.trans f₂, l₂, by rw [e₂, e₁]⟩)

theorem OSpec.weaken {b : BitVec 32} {W : List Slot} {c : Prog isa} {S S' S'' : List Slot} {f : Env → Env}
    (h : OSpec b W c S S' f) (hs : ∀ i ∈ S'', i ∈ S') : OSpec b W c S S'' f :=
  fun s hc hl => WP.mono (h s hc hl) fun _ ⟨r, fr, l, e⟩ => ⟨r, fr, l.mono hs, e⟩

theorem mulO_ok {b : BitVec 32} {s : State} (hc : Ctx b s) {S W : List Slot} (hl : LimOn s.mem b S)
    (o x y : Slot) (hx : x ∈ S) (hy : y ∈ S) (hw : o ∈ W) :
    WP isa (mulP o x y) s fun t => Rest clob s t ∧ Frame (wRegions b W) s.mem t.mem ∧ LimOn t.mem b (o :: S) ∧
      env t.mem b = opMul o x y (env s.mem b) :=
  fieldOpOn_ok hc hl (.mul o x y) (fun i hi => by
    rcases List.mem_cons.mp hi with rfl | hi
    · exact hx
    · rw [List.mem_singleton.mp hi]; exact hy) hw

theorem mulO (b : BitVec 32) {W : List Slot} (o x y : Slot) {S : List Slot} (hx : x ∈ S) (hy : y ∈ S)
    (hw : o ∈ W) : OSpec b W (mulP o x y) S (o :: S) (opMul o x y) :=
  fun _ hc hl => WP.mono (mulO_ok hc hl o x y hx hy hw) fun _ ⟨r, fr, l, e⟩ => ⟨r.mono (by decide), fr, l, e⟩

theorem sqLoopO_ok {s₀ : State} {base : BitVec 32} (hc : Ctx base s₀) (o : Slot) (S : List Slot) {W : List Slot} (hw : o ∈ W)
    (x : Spec.X25519.Fe) (n : Nat) (hn : n < 65536) :
    ∀ m s, 1 ≤ m → m < n → Rest (.r10 :: clob) s₀ s → Frame (wRegions base W) s₀.mem s.mem →
      LimOn s.mem base (o :: S) → s.gpr .r10 = BitVec.ofNat 32 m →
      env s.mem base = Function.update (env s₀.mem base) o (VG.Proof.X25519.sqn x (n - m)) →
      WP isa (.loop (.seq (mulP o o o) (.block [.subs .r10 .r10 (.imm 1)])) .ne) s fun t =>
        Rest (.r10 :: clob) s₀ t ∧ Frame (wRegions base W) s₀.mem t.mem ∧ LimOn t.mem base (o :: S) ∧
        env t.mem base = Function.update (env s₀.mem base) o (VG.Proof.X25519.sqn x n) := by
  intro m s h1 h2 hr hf hl hb he
  refine WP.loop (M := isa) (Inv := fun m (s : State) =>
    1 ≤ m ∧ m < n ∧ Rest (.r10 :: clob) s₀ s ∧ Frame (wRegions base W) s₀.mem s.mem ∧ LimOn s.mem base (o :: S) ∧
    s.gpr .r10 = BitVec.ofNat 32 m ∧
    env s.mem base = Function.update (env s₀.mem base) o (VG.Proof.X25519.sqn x (n - m))) ?_
    m s ⟨h1, h2, hr, hf, hl, hb, he⟩
  intro m s ⟨h1, h2, hr, hf, hl, hb, he⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hcs : Ctx base s := hc.of_rest hr (by decide)
  refine WP.seq (WP.mono (mulO_ok hcs hl o o o List.mem_cons_self List.mem_cons_self hw)
    fun s1 ⟨r1, f1, l1, e1⟩ => ?_)
  refine WP.mono (decR10_ok (by omega) ((r1.gpr _ (by decide)).trans hb)) fun s2 ⟨b2, z2, r2, mem2⟩ => ?_
  have k2 : Rest (.r10 :: clob) s₀ s2 := hr.trans ((r1.mono (by decide)).trans (r2.mono (by decide)))
  have f2 : Frame (wRegions base W) s₀.mem s2.mem := by rw [mem2]; exact hf.trans f1
  have l2 : LimOn s2.mem base (o :: S) := by
    rw [mem2]; exact l1.mono fun i hi => List.mem_cons_of_mem _ hi
  have e2 : env s2.mem base = Function.update (env s₀.mem base) o (VG.Proof.X25519.sqn x (n - m)) := by
    rw [mem2, e1, he, opMul_update]
    apply congrArg (Function.update (env s₀.mem base) o)
    rw [show n - m = (n - (m + 1)) + 1 by omega]
    rfl
  simp only [VG.Arm.eval, z2]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, k2, f2, l2, by rw [e2, Nat.sub_zero]⟩
  · exact .inr ⟨by simp only [decide_eq_false (by omega : m ≠ 0), Bool.not_false],
      m, by omega, by omega, by omega, k2, f2, l2, b2, e2⟩

theorem sqnO (base : BitVec 32) {W : List Slot} (o a : Slot) (n : Nat) (hn : 2 ≤ n) (hn' : n < 65536)
    {S : List Slot} (ha : a ∈ S) (hw : o ∈ W) :
    OSpec base W (Impl.Ed25519.Arm.sqn o a n) S (o :: S) (opSqn o a n) := by
  intro s hc hl
  refine WP.seq (WP.mono (mulO_ok hc hl o a a ha ha hw) fun s1 ⟨r1, f1, l1, e1⟩ => ?_)
  refine WP.seq (wp_movw fun s2 h2 => WP.block_nil ?_)
  have b2 : s2.gpr .r10 = BitVec.ofNat 32 (n - 1) := by
    rw [h2.gpr]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : n - 1 < 2 ^ 16)]
  have k2 : Rest (.r10 :: clob) s s2 := (r1.mono (by decide)).trans (h2.rest (by decide))
  refine sqLoopO_ok hc o S hw (env s.mem base a) n hn' (n - 1) s2 (by omega) (by omega) k2
    (by rw [h2.mem]; exact f1) (by rw [h2.mem]; exact l1) b2 ?_
  rw [h2.mem, e1, show n - (n - 1) = 1 by omega]
  rfl

/-- The chain, from slot 2's limbs below `2^16`, with the other slots `T`'s
kept so. -/
theorem chain250O (base : BitVec 32) (T : List Slot) :
    OSpec base [14, 15, 16, 17] chain250 (2 :: T) (15 :: 14 :: T) power250Env := by
  have h : OSpec base [14, 15, 16, 17] chain250 (2 :: T) _ power250Env :=
    (mulO base 14 2 2 (by simp) (by simp) (by decide)).seq <|
    (mulO base 15 14 14 (by simp) (by simp) (by decide)).seq <|
    (mulO base 15 15 15 (by simp) (by simp) (by decide)).seq <|
    (mulO base 15 2 15 (by simp) (by simp) (by decide)).seq <|
    (mulO base 14 14 15 (by simp) (by simp) (by decide)).seq <|
    (mulO base 16 14 14 (by simp) (by simp) (by decide)).seq <|
    (mulO base 15 15 16 (by simp) (by simp) (by decide)).seq <|
    (sqnO base 16 15 5 (by decide) (by decide) (by simp) (by decide)).seq <|
    (mulO base 15 16 15 (by simp) (by simp) (by decide)).seq <|
    (sqnO base 16 15 10 (by decide) (by decide) (by simp) (by decide)).seq <|
    (mulO base 16 16 15 (by simp) (by simp) (by decide)).seq <|
    (sqnO base 17 16 20 (by decide) (by decide) (by simp) (by decide)).seq <|
    (mulO base 16 17 16 (by simp) (by simp) (by decide)).seq <|
    (sqnO base 16 16 10 (by decide) (by decide) (by simp) (by decide)).seq <|
    (mulO base 15 16 15 (by simp) (by simp) (by decide)).seq <|
    (sqnO base 16 15 50 (by decide) (by decide) (by simp) (by decide)).seq <|
    (mulO base 16 16 15 (by simp) (by simp) (by decide)).seq <|
    (sqnO base 17 16 100 (by decide) (by decide) (by simp) (by decide)).seq <|
    (mulO base 16 17 16 (by simp) (by simp) (by decide)).seq <|
    (sqnO base 16 16 50 (by decide) (by decide) (by simp) (by decide)).seq <|
    (mulO base 15 16 15 (by simp) (by simp) (by decide))
  refine h.weaken fun i hi => ?_
  rcases List.mem_cons.mp hi with rfl | hi
  · simp
  rcases List.mem_cons.mp hi with rfl | hi
  · simp
  · simp [hi]

/-- `vg_gf25519_r16_pow250`, from slot 2's limbs below `2^16`. -/
theorem pow250Fn_ok {b : BitVec 32} (T : List Slot) {s : State} (hc : Ctx b s) (hl : LimOn s.mem b (2 :: T)) :
    WP isa pow250Fn s fun t => Rest fnClob s t ∧ Frame (wRegions b [14, 15, 16, 17] ++ [saveR b]) s.mem t.mem ∧
      LimOn t.mem b (15 :: 14 :: T) ∧
      env t.mem b = power250Env (env s.mem b) :=
  asFn_ok (R := .r10 :: clob) (by decide) (chain250O b T) hc hl

/-- A call of `vg_gf25519_r16_pow250`, as the inlined chain. -/
theorem power250_spec (base : BitVec 32) : ISpec base power250 power250Env := fun s hc hl =>
  WP.mono (fnCall_ok (fun _ hc hl => WP.mono (pow250Fn_ok allSlots hc (LimOn.of_all hl _))
      fun _ ⟨r, f, l, e⟩ => ⟨r, frameS_FA f, l.all fun i => List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (mem_allSlots i)), e⟩) (by decide +kernel) hc hl)
    fun _ ⟨k, l, e⟩ => ⟨⟨k.rest.mono (by decide), k.frame⟩, l, e⟩

def invEnv (e : Env) : Env := opMul 15 15 14 (opSqn 15 15 5 (power250Env e))
def rootEnv (e : Env) : Env := opMul 15 15 2 (opSqn 15 15 2 (power250Env e))

theorem invert_spec (base : BitVec 32) : ISpec base invert invEnv := by
  have h : ISpec base _ _ := (power250_spec base).seq ((sqnI base 15 15 5 (by decide) (by decide)).seq
    (mulI base 15 15 14))
  exact h

theorem rootPower_spec (base : BitVec 32) : ISpec base Impl.Ed25519.Arm.rootPower rootEnv := by
  have h : ISpec base _ _ := (power250_spec base).seq ((sqnI base 15 15 2 (by decide) (by decide)).seq
    (mulI base 15 15 2))
  exact h

theorem invEnv_eval (e : Env) : invEnv e 15 = VG.Proof.X25519.invert (e 2) := by
  simp only [↓reduceIte, invEnv, power250Env, opMul, opSqn, Function.update_apply]
  rfl

theorem rootEnv_eval (e : Env) : rootEnv e 15 = VG.Proof.Ed25519.rootPower (e 2) := by
  simp only [↓reduceIte, rootEnv, power250Env, opMul, opSqn, Function.update_apply]
  rfl

theorem invert_ok {s : State} {base : BitVec 32} (hs : Ctx base s) (hl : AllLim s.mem base) :
    WP isa invert s fun t => IKeep base s t ∧ AllLim t.mem base ∧
      env t.mem base 15 = VG.Proof.X25519.invert (env s.mem base 2) :=
  WP.mono (invert_spec base s hs hl) fun _ ⟨hk, hlt, hv⟩ => ⟨hk, hlt, by rw [hv, invEnv_eval]⟩

theorem rootPower_ok {s : State} {base : BitVec 32} (hs : Ctx base s) (hl : AllLim s.mem base) :
    WP isa Impl.Ed25519.Arm.rootPower s fun t => IKeep base s t ∧ AllLim t.mem base ∧
      env t.mem base 15 = VG.Proof.Ed25519.rootPower (env s.mem base 2) :=
  WP.mono (rootPower_spec base s hs hl) fun _ ⟨hk, hlt, hv⟩ => ⟨hk, hlt, by rw [hv, rootEnv_eval]⟩

end VG.Proof.Ed25519.Arm
