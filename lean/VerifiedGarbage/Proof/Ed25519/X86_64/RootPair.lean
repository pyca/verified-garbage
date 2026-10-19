module

public import VerifiedGarbage.Impl.Ed25519.X86_64.Recover
public import VerifiedGarbage.Proof.Ed25519.RootPower
public import VerifiedGarbage.Proof.Ed25519.X86_64.FieldWide
import VerifiedGarbage.Proof.X25519.X86_64.Inv
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# Ed25519 on x86-64: two square roots' powers at once

`rootPower2` is `rootPower`'s addition chain for slot 2 (into slot 15) and for slot 3 (into
slot 19), each step beside its copy. Its parts that change the slots by a function of them
(`RSpec`) keep everything else but `rbx` and `clob`. Past `2^5 - 1`, its steps
`W = W^(2^n) T` run in a loop (`rootStep_ok`), reading `n` and where `T` comes from out of
`rsi` (`stepsFrom`), whose value slot 14 keeps meanwhile; `ChainInv` is what the loop keeps,
and `chainVals` the values of `W` and of the value saved, `S`, after `j` steps.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519 (sqn)
open VG.Proof.X25519.X86_64 (Outside setRbx_ok decRbx_ok)

variable {fld : Arith} [EdArith fld]

/-- `c` changes the slots by `f`, and keeps everything else but `rbx` and `clob`. -/
def RSpec (base : Addr) (c : Prog isa) (f : Env → Env) : Prop :=
  ∀ s, Scratch s base → WP isa c s fun t => RbxKeep base s t ∧ env t.mem base = f (env s.mem base)

theorem RSpec.seq {base : Addr} {c₁ c₂ : Prog isa} {f g : Env → Env} (h₁ : RSpec base c₁ f)
    (h₂ : RSpec base c₂ g) : RSpec base (.seq c₁ c₂) fun e => g (f e) := fun s hs =>
  WP.seq (WP.mono (h₁ s hs) fun _ ⟨k₁, e₁⟩ =>
    WP.mono (h₂ _ (k₁.scratch hs)) fun _ ⟨k₂, e₂⟩ => ⟨k₁.trans k₂, by rw [e₂, e₁]⟩)

theorem RSpec.ops (base : Addr) (ops : List FieldOp) :
    RSpec base (.block (fieldCode fld ops)) (evalOps ops) := fun _ hs =>
  WP.mono (fieldCodeWide_ok hs ops) fun _ ⟨k, e⟩ => ⟨RbxKeep.of_keep k, e⟩

/-- Slots `o` and `o'` set to `v` and `v'`. -/
abbrev upd2 (e : Env) (o o' : Slot) (v v' : Spec.X25519.Fe) : Env :=
  Function.update (Function.update e o v) o' v'

theorem sq2_eval (e : Env) {o o' : Slot} (ho : o ≠ o') (v v' : Spec.X25519.Fe) :
    evalOps [.sqr o o, .sqr o' o'] (upd2 e o o' v v') = upd2 e o o' (v * v) (v' * v') := by
  funext i
  simp only [evalOps, List.foldl_cons, List.foldl_nil, evalOp, Function.update_apply, ↓reduceIte,
    ho, Ne.symm ho]
  by_cases h₁ : i = o' <;> simp only [h₁, ↓reduceIte]
  by_cases h₂ : i = o <;> simp only [h₂, ↓reduceIte]

theorem sq2_first (e : Env) {o a o' a' : Slot} (ha : o ≠ a') :
    evalOps [.sqr o a, .sqr o' a'] e = upd2 e o o' (sqn (e a) 1) (sqn (e a') 1) := by
  funext i
  simp only [evalOps, List.foldl_cons, List.foldl_nil, evalOp, Function.update_apply, ↓reduceIte,
    Ne.symm ha]
  rfl

/-- The loop of `sqn2`, with the counter `rbx = m` and slots `o` and `o'` squared `n - m`
times since `s₀`. -/
theorem sq2Loop_ok {s₀ : State} {base : Addr} (hs₀ : Scratch s₀ base) {o o' : Slot} (ho : o ≠ o')
    (x x' : Spec.X25519.Fe) (n : Nat) (hn : n < 2 ^ 32) :
    ∀ m s, 1 ≤ m → m < n → RbxKeep base s₀ s → s.gpr .rbx = BitVec.ofNat 64 m →
      env s.mem base = upd2 (env s₀.mem base) o o' (sqn x (n - m)) (sqn x' (n - m)) →
      WP isa (.loop (.block (fieldCode fld ([.sqr o o, .sqr o' o'] : List FieldOp) ++
          ([.alu .sub .rbx (.imm 1)] : List Instr))) .ne) s fun t =>
        RbxKeep base s₀ t ∧ env t.mem base = upd2 (env s₀.mem base) o o' (sqn x n) (sqn x' n) := by
  intro m s h1 h2 hk hb he
  refine WP.loop (M := isa) (Inv := fun m (s : State) => 1 ≤ m ∧ m < n ∧ RbxKeep base s₀ s ∧
    s.gpr .rbx = BitVec.ofNat 64 m ∧
    env s.mem base = upd2 (env s₀.mem base) o o' (sqn x (n - m)) (sqn x' (n - m))) ?_ m s
    ⟨h1, h2, hk, hb, he⟩
  intro m s ⟨h1, h2, hk, hb, he⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok (hk.scratch hs₀) [.sqr o o, .sqr o' o']) fun s1 ⟨k1, e1⟩ => ?_
  refine WP.mono (decRbx_ok (by omega) ((k1.gpr _ (by decide)).trans hb))
    fun s2 ⟨b2, g2, m2, rd2, wr2, z2⟩ => ?_
  have k2 : RbxKeep base s₀ s2 := hk.trans ((RbxKeep.of_keep k1).trans
    ⟨fun r _ hr => g2 r hr, rd2, wr2, by rw [m2]; exact Outside.refl _ _ _ _⟩)
  have e2 : env s2.mem base = upd2 (env s₀.mem base) o o' (sqn x (n - m)) (sqn x' (n - m)) := by
    rw [m2, e1, he, sq2_eval _ ho, show n - m = (n - (m + 1)) + 1 by omega]
    rfl
  simp only [eval, z2, Option.map_some]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, k2, by rw [e2, Nat.sub_zero]⟩
  · exact .inr ⟨by simp only [decide_eq_false (by omega : ¬m = 0), Bool.not_false], m, by omega,
      by omega, by omega, k2, b2, e2⟩

/-- `sqn2 o a o' a' n`: slots `o` and `o'` become slots `a` and `a'` squared `n` times. -/
theorem sqn2_spec (base : Addr) {o a o' a' : Slot} (ho : o ≠ o') (ha : o ≠ a') (n : Nat)
    (hn : 2 ≤ n) (hn' : n < 2 ^ 32) :
    RSpec base (sqn2 fld o a o' a' n) fun e => upd2 e o o' (sqn (e a) n) (sqn (e a') n) := by
  intro s hs
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok hs [.sqr o a, .sqr o' a']) fun s1 ⟨k1, e1⟩ => ?_
  refine WP.mono (setRbx_ok s1 (n - 1) (by omega)) fun s2 ⟨b2, g2, m2, rd2, wr2⟩ => ?_
  have k2 : RbxKeep base s s2 := (RbxKeep.of_keep k1).trans
    ⟨fun r _ hr => g2 r hr, rd2, wr2, by rw [m2]; exact Outside.refl _ _ _ _⟩
  refine sq2Loop_ok hs ho (env s.mem base a) (env s.mem base a') n hn' (n - 1) s2 (by omega)
    (by omega) k2 b2 ?_
  rw [m2, e1, show n - (n - 1) = 1 by omega, sq2_first _ ha]

/-! ## The chain's steps in a loop -/

/-- The squaring loop from `rbx = m`, slots `o` and `o'` squared `n - m` times since `s₀`,
changing no byte but theirs. -/
theorem sqLoop_ok {s₀ : State} {base : Addr} (hs₀ : Scratch s₀ base) {o o' : Slot} (ho : o ≠ o')
    (x x' : Spec.X25519.Fe) (n : Nat) (hn : n < 2 ^ 32) :
    ∀ m s, 1 ≤ m → m ≤ n → RbxKeep base s₀ s → s.gpr .rbx = BitVec.ofNat 64 m →
      (∀ y, Outs [.sqr o o, .sqr o' o'] base y → s.mem y = s₀.mem y) →
      env s.mem base = upd2 (env s₀.mem base) o o' (sqn x (n - m)) (sqn x' (n - m)) →
      WP isa (.loop (.block (fieldCode fld ([.sqr o o, .sqr o' o'] : List FieldOp) ++
          ([.alu .sub .rbx (.imm 1)] : List Instr))) .ne) s fun t =>
        RbxKeep base s₀ t ∧ (∀ y, Outs [.sqr o o, .sqr o' o'] base y → t.mem y = s₀.mem y) ∧
        env t.mem base = upd2 (env s₀.mem base) o o' (sqn x n) (sqn x' n) := by
  intro m s h1 h2 hk hb hf he
  refine WP.loop (M := isa) (Inv := fun m (s : State) => 1 ≤ m ∧ m ≤ n ∧ RbxKeep base s₀ s ∧
    s.gpr .rbx = BitVec.ofNat 64 m ∧ (∀ y, Outs [.sqr o o, .sqr o' o'] base y → s.mem y = s₀.mem y) ∧
    env s.mem base = upd2 (env s₀.mem base) o o' (sqn x (n - m)) (sqn x' (n - m))) ?_ m s
    ⟨h1, h2, hk, hb, hf, he⟩
  intro m s ⟨h1, h2, hk, hb, hf, he⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [WP.block_append_iff]
  refine WP.mono (fieldCodeWide_frame (hk.scratch hs₀) [.sqr o o, .sqr o' o']) fun s1 ⟨k1, e1, f1⟩ => ?_
  refine WP.mono (decRbx_ok (by omega) ((k1.gpr _ (by decide)).trans hb))
    fun s2 ⟨b2, g2, m2, rd2, wr2, z2⟩ => ?_
  have k2 : RbxKeep base s₀ s2 := hk.trans ((RbxKeep.of_keep k1).trans
    ⟨fun r _ hr => g2 r hr, rd2, wr2, by rw [m2]; exact Outside.refl _ _ _ _⟩)
  have f2 : ∀ y, Outs [.sqr o o, .sqr o' o'] base y → s2.mem y = s₀.mem y := fun y hy => by
    rw [m2, f1 y hy, hf y hy]
  have e2 : env s2.mem base = upd2 (env s₀.mem base) o o' (sqn x (n - m)) (sqn x' (n - m)) := by
    rw [m2, e1, he, sq2_eval _ ho, show n - m = (n - (m + 1)) + 1 by omega]
    rfl
  simp only [eval, z2, Option.map_some]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, k2, f2, by rw [e2, Nat.sub_zero]⟩
  · exact .inr ⟨by simp only [decide_eq_false (by omega : ¬m = 0), Bool.not_false], m, by omega,
      by omega, by omega, k2, b2, f2, e2⟩

/-- A step of `rootSteps` on one lane's `W` and `S`. -/
def stepVals (st : Nat × Bool × Bool) (p : Spec.X25519.Fe × Spec.X25519.Fe) :
    Spec.X25519.Fe × Spec.X25519.Fe :=
  let w := sqn p.1 st.1 * (if st.2.1 then p.2 else p.1)
  (w, if st.2.2 then w else p.2)

/-- The first `j` steps. -/
def chainVals (p : Spec.X25519.Fe × Spec.X25519.Fe) (j : Nat) : Spec.X25519.Fe × Spec.X25519.Fe :=
  (rootSteps.take j).foldl (fun q st => stepVals st q) p

/-- `rootSteps`' words, from step `j`. -/
def stepsFrom (j : Nat) : Nat :=
  (rootSteps.drop j).foldr (fun st acc => st.1 + 128 * st.2.1.toNat + 256 * st.2.2.toNat + 512 * acc) 0

/-- What `rootStep` reads of `rsi`, for each step. -/
theorem stepsFrom_facts : ∀ j < 7,
    (BitVec.ofNat 64 (stepsFrom j) &&& 128 == 0) = !(rootSteps.getD j (0, false, false)).2.1 ∧
    (BitVec.ofNat 64 (stepsFrom j) &&& 256 == 0) = !(rootSteps.getD j (0, false, false)).2.2 ∧
    BitVec.ofNat 64 (stepsFrom j) &&& 127 = BitVec.ofNat 64 (rootSteps.getD j (0, false, false)).1 ∧
    1 ≤ (rootSteps.getD j (0, false, false)).1 ∧ (rootSteps.getD j (0, false, false)).1 < 2 ^ 32 ∧
    BitVec.ofNat 64 (stepsFrom j) >>> 9 = BitVec.ofNat 64 (stepsFrom (j + 1)) ∧
    (BitVec.ofNat 64 (stepsFrom (j + 1)) == 0) = decide (j + 1 = 7) := by
  decide

/-- The chain's values after a step, from those before. -/
theorem step_env (e : Env) (n : Nat) (u v : Bool) :
    let e₁ := evalOps (if u then [.copy 16 17, .copy 20 21] else [.copy 16 15, .copy 20 19]) e
    let e₂ := upd2 e₁ 15 19 (sqn (e₁ 15) n) (sqn (e₁ 19) n)
    let e₃ := evalOps [.mul 15 15 16, .mul 19 19 20] e₂
    let e₄ := if v then evalOps [.copy 17 15, .copy 21 19] e₃ else e₃
    (e₄ 15, e₄ 17) = stepVals (n, u, v) (e 15, e 17) ∧
      (e₄ 19, e₄ 21) = stepVals (n, u, v) (e 19, e 21) ∧ e₄ 2 = e 2 ∧ e₄ 3 = e 3 := by
  cases u <;> cases v <;>
    simp only [Fin.isValue, Fin.reduceEq, evalOps, List.foldl_cons, List.foldl_nil, evalOp, upd2,
      Function.update_apply, stepVals, Bool.false_eq_true, ↓reduceIte, and_self]

theorem chainVals_succ (p : Spec.X25519.Fe × Spec.X25519.Fe) {j : Nat} (hj : j < 7) :
    chainVals p (j + 1) = stepVals (rootSteps.getD j (0, false, false)) (chainVals p j) := by
  have : rootSteps.take (j + 1) = rootSteps.take j ++ [rootSteps.getD j (0, false, false)] := by
    have h : ∀ j < 7, rootSteps.take (j + 1) = rootSteps.take j ++ [rootSteps.getD j (0, false, false)] := by
      decide
    exact h j hj
  rw [chainVals, this, List.foldl_append]
  rfl

/-- The two-lane field program `A` or `B`, as the flag `ne` says. -/
theorem iteOps_ok {s : State} {base : Addr} (hs : Scratch s base) (b : Bool)
    (hc : isa.eval .ne s = some b) (A B : List FieldOp) :
    WP isa (.ite .ne (.block (fieldCode fld A)) (.block (fieldCode fld B))) s fun t => Keep base s t ∧
      env t.mem base = evalOps (if b then A else B) (env s.mem base) ∧
      ∀ x, Outs (if b then A else B) base x → t.mem x = s.mem x := by
  refine WP.ite b hc (fun h => ?_) (fun h => ?_) <;> subst h <;> exact fieldCodeWide_frame hs _

/-- The word at byte 512 (slot 14's first) of a program writing only slots past it. -/
theorem word14_of_outs {ops : List FieldOp} (hops : ∀ op ∈ ops, 520 ≤ offset op.out) {base : Addr}
    {m m' : Mem} (hf : ∀ x, Outs ops base x → m' x = m x) :
    X25519.X86_64.word m' base 512 = X25519.X86_64.word m base 512 :=
  Mem.readW_congr (w := 64) fun i hi => hf _ fun op hop => by
    have := hops op hop
    rw [X25519.X86_64.ofs_off base (by omega)]; omega

/-- What the loop keeps of the state before it (`s₁`), and the chain after `j` of its steps. -/
structure ChainInv (base : Addr) (s₁ s : State) (r₀ : BitVec 64) (a b a' b' : Spec.X25519.Fe)
    (j : Nat) : Prop where
  gpr : ∀ r, r ∉ X25519.X86_64.clob → r ≠ .rbx → r ≠ .rsi → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  mem : Outside base 64 704 s₁.mem s.mem
  saved : X25519.X86_64.word s.mem base 512 = r₀
  rsi : s.gpr .rsi = BitVec.ofNat 64 (stepsFrom j)
  lane : (env s.mem base 15, env s.mem base 17) = chainVals (a, b) j
  lane' : (env s.mem base 19, env s.mem base 21) = chainVals (a', b') j
  x2 : env s.mem base 2 = env s₁.mem base 2
  x3 : env s.mem base 3 = env s₁.mem base 3

theorem ChainInv.scratch {base : Addr} {s₁ s : State} {r₀ : BitVec 64} {a b a' b' : Spec.X25519.Fe}
    {j : Nat} (h : ChainInv base s₁ s r₀ a b a' b' j) (hs : Scratch s₁ base) : Scratch s base :=
  ⟨(h.gpr _ (by decide) (by decide) (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

/-- `rootStep` runs step `j` of `rootSteps`, and sets ZF past the last. -/
theorem rootStep_ok {s₁ s : State} {base : Addr} (hs₁ : Scratch s₁ base) {r₀ : BitVec 64}
    {a b a' b' : Spec.X25519.Fe} {j : Nat} (hj : j < 7) (h : ChainInv base s₁ s r₀ a b a' b' j) :
    WP isa (rootStep fld) s fun t => ChainInv base s₁ t r₀ a b a' b' (j + 1) ∧
      t.zf = some (decide (j + 1 = 7)) := by
  have hs := h.scratch hs₁
  have hn := hs.nowrap
  obtain ⟨fu, fv, fn, fn1, fn2, fsh, fz⟩ := stepsFrom_facts j hj
  generalize hst : rootSteps.getD j (0, false, false) = st at fu fv fn fn1 fn2
  obtain ⟨n, u, v⟩ := st
  dsimp only at fu fv fn fn1 fn2
  unfold rootStep
  -- `test rsi, 128`.
  refine WP.seq (WP.mono (show WP isa (.block [.alu .test .rsi (.imm 128)]) s fun t =>
      t.zf = some !u ∧ t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, h.rsi,
      Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_arithFlags,
      RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.zf_arithFlags,
      show BitVec.signExtend 64 (128 : BitVec 32) = 128 by decide, fu]
    exact ⟨trivial, trivial, trivial, trivial, trivial⟩) fun s₂ ⟨z₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  have hs₂ : Scratch s₂ base := ⟨by rw [g₂]; exact hs.rdi, wr₂ ▸ hs.wr, hn⟩
  -- `T`.
  refine WP.seq (WP.mono (iteOps_ok hs₂ u (by simp only [eval, z₂, Option.map_some, Bool.not_not])
    [.copy 16 17, .copy 20 21] [.copy 16 15, .copy 20 19]) fun s₃ ⟨k₃, e₃, f₃⟩ => ?_)
  have hs₃ := hs₂.of_keep k₃
  -- `rbx = n`.
  refine WP.seq (WP.mono (show WP isa (.block [.mov .rbx (.reg .rsi), .alu .and .rbx (.imm 127)]) s₃
      fun t => t.gpr .rbx = BitVec.ofNat 64 n ∧ (∀ r, r ≠ .rbx → t.gpr r = s₃.gpr r) ∧ t.mem = s₃.mem ∧
        t.rd = s₃.rd ∧ t.wr = s₃.wr by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
      Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self,
      RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.rd_setReg,
      RegUpd.rd_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags,
      show BitVec.signExtend 64 (127 : BitVec 32) = 127 by decide]
    refine ⟨?_, fun r hr => ?_, trivial, trivial, trivial⟩
    · rw [k₃.gpr _ (by decide), g₂, h.rsi, fn]
    · simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₄ ⟨b₄, g₄, m₄, rd₄, wr₄⟩ => ?_)
  have hs₄ : Scratch s₄ base := ⟨by rw [g₄ _ (by decide)]; exact hs₃.rdi, wr₄ ▸ hs₃.wr, hn⟩
  -- The squarings.
  have k₄ : RbxKeep base s₄ s₄ := ⟨fun _ _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩
  refine WP.seq (WP.mono (sqLoop_ok (fld := fld) hs₄ (o := 15) (o' := 19) (by decide)
    (env s₄.mem base 15) (env s₄.mem base 19) n fn2 n s₄ fn1 (Nat.le_refl _) k₄ b₄ (fun _ _ => rfl)
    (by rw [Nat.sub_self]; simp only [upd2, sqn, Function.update_eq_self]))
    fun s₅ ⟨k₅, f₅, e₅⟩ => ?_)
  have hs₅ := k₅.scratch hs₄
  -- The products, and `test rsi, 256`.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (fieldCodeWide_frame hs₅ [.mul 15 15 16, .mul 19 19 20])
    fun s₆ ⟨k₆, e₆, f₆⟩ => ?_
  have rsi₆ : s₆.gpr .rsi = BitVec.ofNat 64 (stepsFrom j) := by
    rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide) (by decide), g₄ _ (by decide),
      k₃.gpr _ (by decide), g₂, h.rsi]
  refine WP.mono (show WP isa (.block [.alu .test .rsi (.imm 256)]) s₆ fun t =>
      t.zf = some !v ∧ t.gpr = s₆.gpr ∧ t.mem = s₆.mem ∧ t.rd = s₆.rd ∧ t.wr = s₆.wr by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, rsi₆,
      Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_arithFlags,
      RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.zf_arithFlags,
      show BitVec.signExtend 64 (256 : BitVec 32) = 256 by decide, fv]
    exact ⟨trivial, trivial, trivial, trivial, trivial⟩) fun s₇ ⟨z₇, g₇, m₇, rd₇, wr₇⟩ => ?_
  have hs₇ : Scratch s₇ base := ⟨by rw [g₇]; exact (hs₅.of_keep k₆).rdi, wr₇ ▸ (hs₅.of_keep k₆).wr, hn⟩
  -- `S`.
  refine WP.seq (WP.mono (iteOps_ok hs₇ v (by simp only [eval, z₇, Option.map_some, Bool.not_not])
    [.copy 17 15, .copy 21 19] []) fun s₈ ⟨k₈, e₈, f₈⟩ => ?_)
  have rsi₈ : s₈.gpr .rsi = BitVec.ofNat 64 (stepsFrom j) := by rw [k₈.gpr _ (by decide), g₇, rsi₆]
  -- `rsi` to the next step.
  refine WP.mono (show WP isa (.block [.shift .shr .rsi 9, .alu .test .rsi (.reg .rsi)]) s₈ fun t =>
      t.gpr .rsi = BitVec.ofNat 64 (stepsFrom (j + 1)) ∧ t.zf = some (decide (j + 1 = 7)) ∧
        (∀ r, r ≠ .rsi → t.gpr r = s₈.gpr r) ∧ t.mem = s₈.mem ∧ t.rd = s₈.rd ∧ t.wr = s₈.wr by
    apply WP.of_runBlock
    simp only [runBlock_cons, runBlock_nil, exec, readSrc, execAlu, execShift, rsi₈,
      show (1 ≤ 9 ∧ 9 ≤ 63) = True from by decide, ite_true, runStep_some, Option.some.injEq,
      exists_eq_left', RegUpd.gpr_setReg_self, RegUpd.gpr_arithFlags, RegUpd.mem_setReg,
      RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags, RegUpd.wr_setReg,
      RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags,
      RegUpd.wr_setFlags, BitVec.and_self, fsh, fz, Option.bind_some]
    refine ⟨trivial, trivial, fun r hr => ?_, trivial, trivial, trivial⟩
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun t ⟨rsiT, zT, gT, mT, rdT, wrT⟩ => ?_
  have eT : env t.mem base = (let e₁ := evalOps (if u then [.copy 16 17, .copy 20 21] else
        [.copy 16 15, .copy 20 19]) (env s.mem base)
      let e₂ := upd2 e₁ 15 19 (sqn (e₁ 15) n) (sqn (e₁ 19) n)
      let e₃ := evalOps [.mul 15 15 16, .mul 19 19 20] e₂
      if v then evalOps [.copy 17 15, .copy 21 19] e₃ else e₃) := by
    have hv4 : ∀ e, evalOps (if v then [.copy 17 15, .copy 21 19] else []) e =
        if v then evalOps [.copy 17 15, .copy 21 19] e else e := fun e => by cases v <;> rfl
    rw [mT, e₈, hv4, m₇, e₆, e₅, m₄, e₃, m₂]
  obtain ⟨l₁, l₂, l₃, l₄⟩ := step_env (env s.mem base) n u v
  rw [← eT] at l₁ l₂ l₃ l₄
  have hu : ∀ op ∈ (if u then [FieldOp.copy 16 17, .copy 20 21] else [.copy 16 15, .copy 20 19]),
      520 ≤ offset op.out := by cases u <;> decide
  have hv : ∀ op ∈ (if v then [FieldOp.copy 17 15, .copy 21 19] else []), 520 ≤ offset op.out := by
    cases v <;> decide
  refine ⟨⟨fun r hr hb hs' => ?_, ?_, ?_, ?_, ?_, rsiT, ?_, ?_, ?_, ?_⟩, zT⟩
  · rw [gT r hs', k₈.gpr r hr, g₇, k₆.gpr r hr, k₅.gpr r hr hb, g₄ r hb, k₃.gpr r hr, g₂,
      h.gpr r hr hb hs']
  · rw [rdT, k₈.rd, rd₇, k₆.rd, k₅.rd, rd₄, k₃.rd, rd₂, h.rd]
  · rw [wrT, k₈.wr, wr₇, k₆.wr, k₅.wr, wr₄, k₃.wr, wr₂, h.wr]
  · refine h.mem.trans (fun x _ => by rw [m₂]) |>.trans k₃.mem |>.trans (fun x _ => by rw [m₄])
      |>.trans k₅.mem |>.trans k₆.mem |>.trans (fun x _ => by rw [m₇]) |>.trans k₈.mem
      |>.trans (fun x _ => by rw [mT])
  · rw [mT, word14_of_outs hv f₈, m₇, word14_of_outs (by decide) f₆, word14_of_outs (by decide) f₅,
      m₄, word14_of_outs hu f₃, m₂, h.saved]
  · rw [chainVals_succ _ hj, hst, ← h.lane]; exact l₁
  · rw [chainVals_succ _ hj, hst, ← h.lane']; exact l₂
  · rw [l₃, h.x2]
  · rw [l₄, h.x3]

/-- `2^5 - 1`, then the steps, the last two squarings and the product: `rootPower`, for each
lane. -/
theorem chain_rootPower (e : Env) (b b' : Spec.X25519.Fe) :
    let e₃ := evalOps [.mul 15 2 15, .mul 19 3 19, .mul 14 14 15, .mul 18 18 19, .sqr 16 14, .sqr 20 18,
      .mul 15 15 16, .mul 19 19 20] (evalOps [.sqr 15 14, .sqr 19 18, .sqr 15 15, .sqr 19 19]
        (evalOps [.sqr 14 2, .sqr 18 3] e))
    sqn (chainVals (e₃ 15, b) 7).1 2 * e₃ 2 = VG.Proof.Ed25519.rootPower (e 2) ∧
      sqn (chainVals (e₃ 19, b') 7).1 2 * e₃ 3 = VG.Proof.Ed25519.rootPower (e 3) := by
  simp only [Fin.isValue, Fin.reduceEq, evalOps, List.foldl_cons, evalOp,
    Function.update_apply, ↓reduceIte, chainVals, rootSteps, List.take, List.foldl, stepVals]
  exact ⟨rfl, rfl⟩

/-- `rootPowerLoop2` in the scratch: A's power (of slot 2) into slot 15 and R's (of slot 3)
into slot 19. -/
theorem rootPowerLoop2_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (rootPowerLoop2 fld) s fun t => RbxKeep base s t ∧
      env t.mem base 15 = Spec.X25519.pow (env s.mem base 2) ((Spec.X25519.P - 5) / 8) ∧
      env t.mem base 19 = Spec.X25519.pow (env s.mem base 3) ((Spec.X25519.P - 5) / 8) := by
  have hn := hs.nowrap
  unfold rootPowerLoop2
  -- `2^5 - 1`.
  refine WP.seq (WP.mono (fieldCodeWide_ok hs _) fun s₁ ⟨k₁, e₁⟩ => ?_)
  have hs₁ := hs.of_keep k₁
  refine WP.seq (WP.mono (fieldCodeWide_ok hs₁ _) fun s₂ ⟨k₂, e₂⟩ => ?_)
  have hs₂ := hs₁.of_keep k₂
  refine WP.seq (WP.mono (fieldCodeWide_ok hs₂ _) fun s₃ ⟨k₃, e₃⟩ => ?_)
  have hs₃ := hs₂.of_keep k₃
  -- `rsi` into slot 14, the steps into `rsi`.
  have hw : InRegions s₃.wr (X25519.X86_64.off base 512) 8 :=
    ⟨_, hs₃.wr, Offset.contains_base base (show 512 + 8 ≤ 8192 by decide) (by omega)⟩
  refine WP.seq (WP.mono (show WP isa (.block [.store (Impl.X25519.X86_64.sc (offset 14)) .rsi,
      .movImm64 .rsi (BitVec.ofNat 64 rootStepsWord)]) s₃ fun t =>
      t.mem = s₃.mem.writeW (X25519.X86_64.off base 512) (s₃.gpr .rsi) ∧
      t.gpr .rsi = BitVec.ofNat 64 rootStepsWord ∧ (∀ r, r ≠ .rsi → t.gpr r = s₃.gpr r) ∧
      t.rd = s₃.rd ∧ t.wr = s₃.wr by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, X25519.X86_64.ea_sc, hs₃.rdi,
      State.store64, show offset 14 = 512 from rfl, hw, ite_true, Option.some.injEq,
      exists_eq_left', RegUpd.gpr_setReg_self, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg]
    refine ⟨trivial, trivial, fun r hr => ?_, trivial, trivial⟩
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₄ ⟨m₄, rsi₄, g₄, rd₄, wr₄⟩ => ?_)
  have O₄ : Outside base 512 8 s₃.mem s₄.mem := by
    rw [m₄]; exact X25519.X86_64.writeW_outside _ _ _ (by omega)
  have v₄ : ∀ i : Slot, i ≠ 14 → env s₄.mem base i = env s₃.mem base i := fun i hi => by
    have : i.val ≠ 14 := fun h => hi (Fin.ext h)
    simp only [env, X25519.X86_64.F]
    rw [O₄.fe (by simp only [offset]; omega) (by simp only [offset]; omega)]
  have I₀ : ChainInv base s₃ s₄ (s₃.gpr .rsi) (env s₃.mem base 15) (env s₃.mem base 17)
      (env s₃.mem base 19) (env s₃.mem base 21) 0 :=
    ⟨fun r _ _ hr => g₄ r hr, rd₄, wr₄, O₄.mono (by decide) (by decide),
      by rw [m₄]; exact Mem.readW_writeW_self64 _ _ _, rsi₄,
      by rw [v₄ 15 (by decide), v₄ 17 (by decide)]; rfl,
      by rw [v₄ 19 (by decide), v₄ 21 (by decide)]; rfl, v₄ 2 (by decide), v₄ 3 (by decide)⟩
  -- The steps.
  refine WP.seq (WP.mono (WP.loop (M := isa) (Q := fun t => ChainInv base s₃ t (s₃.gpr .rsi)
      (env s₃.mem base 15) (env s₃.mem base 17) (env s₃.mem base 19) (env s₃.mem base 21) 7)
    (fun m t => ∃ j, j < 7 ∧ m = 7 - j ∧ ChainInv base s₃ t (s₃.gpr .rsi) (env s₃.mem base 15)
      (env s₃.mem base 17) (env s₃.mem base 19) (env s₃.mem base 21) j)
    (fun m t ⟨j, hj, hm, hI⟩ => WP.mono (rootStep_ok hs₃ hj hI) fun t' ⟨hI', z'⟩ => by
      simp only [eval, z', Option.map_some]
      by_cases h7 : j + 1 = 7
      · exact .inl ⟨by simp [h7], h7 ▸ hI'⟩
      · exact .inr ⟨by simp [h7], 7 - (j + 1), by omega, j + 1, by omega, rfl, hI'⟩)
    7 s₄ ⟨0, by decide, rfl, I₀⟩) fun s₅ I₅ => ?_)
  have hs₅ := I₅.scratch hs₃
  -- `rsi` back.
  refine WP.seq (WP.mono (show WP isa (.block [.mov .rsi (.mem (Impl.X25519.X86_64.sc (offset 14)))]) s₅
      fun t => t.gpr .rsi = s₃.gpr .rsi ∧ (∀ r, r ≠ .rsi → t.gpr r = s₅.gpr r) ∧ t.mem = s₅.mem ∧
        t.rd = s₅.rd ∧ t.wr = s₅.wr by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
      X25519.X86_64.readSrc_sc (show X25519.X86_64.Scr s₅ base 8192 from ⟨hs₅.rdi, hs₅.wr, hn⟩)
        (show offset 14 + 8 ≤ 8192 by decide), Option.map_some, Option.some.injEq,
      exists_eq_left', RegUpd.gpr_setReg_self, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg]
    refine ⟨I₅.saved, fun r hr => ?_, trivial, trivial, trivial⟩
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₆ ⟨rsi₆, g₆, m₆, rd₆, wr₆⟩ => ?_)
  have hs₆ : Scratch s₆ base := ⟨by rw [g₆ _ (by decide)]; exact hs₅.rdi, wr₆ ▸ hs₅.wr, hn⟩
  -- The last squarings and the product.
  refine WP.seq (WP.mono (sqn2_spec (fld := fld) base (o := 15) (a := 15) (o' := 19) (a' := 19)
    (by decide) (by decide) 2 (by decide) (by decide) s₆ hs₆) fun s₇ ⟨k₇, e₇⟩ => ?_)
  refine WP.mono (fieldCodeWide_ok (k₇.scratch hs₆) _) fun t ⟨k₈, e₈⟩ => ?_
  refine ⟨⟨fun r hr hb => ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [k₈.gpr r hr, k₇.gpr r hr hb]
    by_cases hsi : r = .rsi
    · subst hsi; rw [rsi₆, k₃.gpr _ hr, k₂.gpr _ hr, k₁.gpr _ hr]
    · rw [g₆ r hsi, I₅.gpr r hr hb hsi, k₃.gpr _ hr, k₂.gpr _ hr, k₁.gpr _ hr]
  · rw [k₈.rd, k₇.rd, rd₆, I₅.rd, k₃.rd, k₂.rd, k₁.rd]
  · rw [k₈.wr, k₇.wr, wr₆, I₅.wr, k₃.wr, k₂.wr, k₁.wr]
  · exact k₁.mem.trans k₂.mem |>.trans k₃.mem |>.trans I₅.mem |>.trans (fun x _ => by rw [m₆])
      |>.trans k₇.mem |>.trans k₈.mem
  · have hl : env s₅.mem base 15 = (chainVals (env s₃.mem base 15, env s₃.mem base 17) 7).1 :=
      congrArg Prod.fst I₅.lane
    rw [← VG.Proof.Ed25519.rootPower_eq, ← (chain_rootPower (env s.mem base) (env s₃.mem base 17)
      (env s₃.mem base 21)).1, ← e₁, ← e₂, ← e₃, ← hl, ← I₅.x2, ← m₆, e₈, e₇]
    simp only [Fin.isValue, Fin.reduceEq, evalOps, List.foldl_cons, List.foldl_nil, evalOp, upd2,
      Function.update_apply, ↓reduceIte]
  · have hl : env s₅.mem base 19 = (chainVals (env s₃.mem base 19, env s₃.mem base 21) 7).1 :=
      congrArg Prod.fst I₅.lane'
    rw [← VG.Proof.Ed25519.rootPower_eq, ← (chain_rootPower (env s.mem base) (env s₃.mem base 17)
      (env s₃.mem base 21)).2, ← e₁, ← e₂, ← e₃, ← hl, ← I₅.x3, ← m₆, e₈, e₇]
    simp only [Fin.isValue, Fin.reduceEq, evalOps, List.foldl_cons, List.foldl_nil, evalOp, upd2,
      Function.update_apply, ↓reduceIte]

theorem rootPowerUnrolled2_spec (base : Addr) :
    ∃ f, RSpec base (rootPowerUnrolled2 fld) f ∧ ∀ e, f e 15 = VG.Proof.Ed25519.rootPower (e 2) ∧
      f e 19 = VG.Proof.Ed25519.rootPower (e 3) := by
  refine ⟨_, (RSpec.ops base _).seq <| (RSpec.ops base _).seq <| (RSpec.ops base _).seq <|
    (sqn2_spec base (by decide) (by decide) 5 (by decide) (by decide)).seq <| (RSpec.ops base _).seq <|
    (sqn2_spec base (by decide) (by decide) 10 (by decide) (by decide)).seq <| (RSpec.ops base _).seq <|
    (sqn2_spec base (by decide) (by decide) 20 (by decide) (by decide)).seq <| (RSpec.ops base _).seq <|
    (sqn2_spec base (by decide) (by decide) 10 (by decide) (by decide)).seq <| (RSpec.ops base _).seq <|
    (sqn2_spec base (by decide) (by decide) 50 (by decide) (by decide)).seq <| (RSpec.ops base _).seq <|
    (sqn2_spec base (by decide) (by decide) 100 (by decide) (by decide)).seq <| (RSpec.ops base _).seq <|
    (sqn2_spec base (by decide) (by decide) 50 (by decide) (by decide)).seq <| (RSpec.ops base _).seq <|
    (sqn2_spec base (by decide) (by decide) 2 (by decide) (by decide)).seq (RSpec.ops base _),
    fun e => ⟨?_, ?_⟩⟩
  all_goals
    dsimp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, upd2, evalOps, List.foldl_cons, List.foldl_nil,
      evalOp, Function.update_apply]
    rfl

/-- `rootPowerUnrolled2` in the scratch: A's power (of slot 2) into slot 15 and R's (of slot 3) into
slot 19. -/
theorem rootPowerUnrolled2_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (rootPowerUnrolled2 fld) s fun t => RbxKeep base s t ∧
      env t.mem base 15 = Spec.X25519.pow (env s.mem base 2) ((Spec.X25519.P - 5) / 8) ∧
      env t.mem base 19 = Spec.X25519.pow (env s.mem base 3) ((Spec.X25519.P - 5) / 8) := by
  obtain ⟨f, hf, hv⟩ := rootPowerUnrolled2_spec (fld := fld) base
  refine WP.mono (hf s hs) fun t ⟨k, e⟩ => ⟨k, ?_, ?_⟩
  · rw [e, (hv _).1, VG.Proof.Ed25519.rootPower_eq]
  · rw [e, (hv _).2, VG.Proof.Ed25519.rootPower_eq]

/-- `rootPower2` in the scratch: A's power (of slot 2) into slot 15 and R's (of slot 3) into
slot 19. -/
theorem rootPower2_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (rootPower2 fld) s fun t => RbxKeep base s t ∧
      env t.mem base 15 = Spec.X25519.pow (env s.mem base 2) ((Spec.X25519.P - 5) / 8) ∧
      env t.mem base 19 = Spec.X25519.pow (env s.mem base 3) ((Spec.X25519.P - 5) / 8) := by
  unfold rootPower2
  split
  · exact rootPowerLoop2_ok hs
  · exact rootPowerUnrolled2_ok hs

end VG.Proof.Ed25519.X86_64
