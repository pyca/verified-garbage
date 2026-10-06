import VerifiedGarbage.Impl.Ed25519.X86_64.Recover
import VerifiedGarbage.Proof.Ed25519.RootPower
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldWide
import VerifiedGarbage.Proof.X25519.X86_64.Inv

/-!
# Ed25519 on x86-64: two square roots' powers at once

`rootPower2` is `rootPower`'s addition chain for slot 2 (into slot 15) and for slot 3 (into
slot 19), each step beside its copy. Each of its parts changes the slots by a function of them
(`RSpec`), keeping everything else but `rbx` and `clob`.
-/

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

theorem rootPower2_spec (base : Addr) :
    ∃ f, RSpec base (rootPower2 fld) f ∧ ∀ e, f e 15 = VG.Proof.Ed25519.rootPower (e 2) ∧
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
    simp only [↓reduceIte, upd2, evalOps, List.foldl_cons, List.foldl_nil, evalOp,
      Function.update_apply]
    rfl

/-- `rootPower2` in the scratch: A's power (of slot 2) into slot 15 and R's (of slot 3) into
slot 19. -/
theorem rootPower2_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (rootPower2 fld) s fun t => RbxKeep base s t ∧
      env t.mem base 15 = Spec.X25519.pow (env s.mem base 2) ((Spec.X25519.P - 5) / 8) ∧
      env t.mem base 19 = Spec.X25519.pow (env s.mem base 3) ((Spec.X25519.P - 5) / 8) := by
  obtain ⟨f, hf, hv⟩ := rootPower2_spec (fld := fld) base
  refine WP.mono (hf s hs) fun t ⟨k, e⟩ => ⟨k, ?_, ?_⟩
  · rw [e, (hv _).1, VG.Proof.Ed25519.rootPower_eq]
  · rw [e, (hv _).2, VG.Proof.Ed25519.rootPower_eq]

end VG.Proof.Ed25519.X86_64
