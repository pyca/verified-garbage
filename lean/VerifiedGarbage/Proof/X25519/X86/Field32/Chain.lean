import VerifiedGarbage.Proof.X25519.X86.Ops
import VerifiedGarbage.Proof.X25519.Invert
import VerifiedGarbage.Impl.X25519.X86.Field32

/-!
# `vg_gf25519_r32_pow250` on x86 (32-bit): the addition chain

The chain runs on five slots of the working space from byte 512 (`coff`):
`E0`, `E1`, `E2`, `E3` and `AC`, the copy of `a`. Each multiplication and
run of squarings changes one of them (`mulC`, `sqnC`), and memory only in
bytes 512 to 927, the slots and X25519's product (`CKeep`), so the chain
takes the slots' values `e` to `chainEnv e` (`chain_spec`), in which `E1`
holds `a^(2^250 - 1)` and `E0` holds `a^11` (`chainEnv_eval`).
-/

namespace VG.Proof.X25519.X86.Field32

open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.X25519.X86.Field32 VG.Proof.X25519.X86 VG.Spec.X25519
open VG.Proof.X25519 (sqn pw)

/-- The chain's slots: `E0`, `E1`, `E2`, `E3` and `AC`. -/
abbrev Cs := Fin 5

/-- Slot `i`'s offset. -/
def coff (i : Cs) : Nat := 512 + 32 * i.val

theorem coff_slot (i : Cs) : isSlot 512 (coff i) = true :=
  (by decide : ∀ i : Cs, isSlot 512 (coff i) = true) i

theorem coff_inj {i j : Cs} (h : coff i = coff j) : i = j := by
  apply Fin.ext
  simp only [coff] at h
  omega

/-- The slots' values. -/
abbrev CEnv := Cs → Fe

def cenv (m : Mem) (x : BitVec 32) : CEnv := fun i => F m x (coff i)

/-- What the chain keeps: `edi`, `esp`, the regions, and memory outside bytes
512 to 927. -/
structure CKeep (x : BitVec 32) (s t : State) : Prop where
  edi : t.gpr .edi = s.gpr .edi
  esp : t.gpr .esp = s.gpr .esp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [sub x 512 416] s.mem t.mem

theorem CKeep.refl (x : BitVec 32) (s : State) : CKeep x s s :=
  ⟨rfl, rfl, rfl, rfl, Frame.refl _ _⟩

theorem CKeep.trans {x : BitVec 32} {s t u : State} (h : CKeep x s t) (k : CKeep x t u) : CKeep x s u :=
  ⟨k.edi.trans h.edi, k.esp.trans h.esp, k.rd.trans h.rd, k.wr.trans h.wr, h.frame.trans k.frame⟩

theorem CKeep.ctx {x : BitVec 32} {s t : State} (h : CKeep x s t) (hc : Ctx 4096 x s) : Ctx 4096 x t :=
  hc.keep h.edi h.wr h.esp

theorem CKeep.of_counter {x : BitVec 32} {s t : State} {v : BitVec 32} (h : Wp.Upd s t .esi v) :
    CKeep x s t :=
  ⟨h.other _ (by decide), h.other _ (by decide), h.rd, h.wr, by rw [h.mem]; exact Frame.refl _ _⟩

/-- `c` takes the slots' values `e` to `f e`, keeping what `CKeep` keeps. -/
def CSpec (x : BitVec 32) (c : Prog isa) (f : CEnv → CEnv) : Prop :=
  ∀ s, Ctx 4096 x s → WP isa c s fun t => CKeep x s t ∧ cenv t.mem x = f (cenv s.mem x)

theorem CSpec.seq {x : BitVec 32} {c d : Prog isa} {f g : CEnv → CEnv}
    (h : CSpec x c f) (k : CSpec x d g) : CSpec x (.seq c d) (fun e => g (f e)) :=
  fun s hc => WP.seq (WP.mono (h s hc) fun t ⟨ht, et⟩ =>
    WP.mono (k t (ht.ctx hc)) fun u ⟨hu, eu⟩ => ⟨ht.trans hu, by rw [eu, et]⟩)

theorem CSpec.append {x : BitVec 32} {c d : List Instr} {f g : CEnv → CEnv}
    (h : CSpec x (.block c) f) (k : CSpec x (.block d) g) :
    CSpec x (.block (c ++ d)) (fun e => g (f e)) := fun s hc => by
  rw [WP.block_append_iff]
  exact WP.mono (h s hc) fun t ⟨ht, et⟩ =>
    WP.mono (k t (ht.ctx hc)) fun u ⟨hu, eu⟩ => ⟨ht.trans hu, by rw [eu, et]⟩

def opMul (o a b : Cs) (e : CEnv) : CEnv := Function.update e o (e a * e b)
def opSqn (o a : Cs) (n : Nat) (e : CEnv) : CEnv := Function.update e o (sqn (e a) n)

/-- A multiplication of slots, with what it keeps. -/
theorem mul_keep {x : BitVec 32} {s : State} (hc : Ctx 4096 x s) (o a b : Cs) :
    WP isa (.block (mul (coff o) (coff a) (coff b))) s fun t =>
      Keep s t ∧ CKeep x s t ∧ cenv t.mem x = opMul o a b (cenv s.mem x) := by
  have hv : opValid 512 (.mul (coff o) (coff a) (coff b)) = true := by
    simp only [opValid, opOut, opIns, coff_slot, List.all_cons, List.all_nil, Bool.and_self]
  refine WP.mono (op_ok hc (.mul (coff o) (coff a) (coff b)) hv) fun t ⟨k, f, e⟩ =>
    ⟨k, ⟨k.edi, k.esp, k.rd, k.wr, f⟩, funext fun i => ?_⟩
  rw [cenv, e (coff i) (coff_slot i)]
  simp only [opOut, opVal, opMul]
  by_cases hi : i = o
  · subst hi; rw [Function.update_self, Function.update_self]; rfl
  · rw [Function.update_of_ne (fun h => hi (coff_inj h)), Function.update_of_ne hi]; rfl

theorem mulC (x : BitVec 32) (o a b : Cs) :
    CSpec x (.block (mul (coff o) (coff a) (coff b))) (opMul o a b) := fun _ hc =>
  WP.mono (mul_keep hc o a b) fun _ ⟨_, k, e⟩ => ⟨k, e⟩

theorem opMul_update (o : Cs) (e : CEnv) (v : Fe) :
    opMul o o o (Function.update e o v) = Function.update e o (v * v) := by
  simp only [opMul, Function.update_self, Function.update_idem]

theorem sqLoop_ok {x : BitVec 32} {s₀ : State} (hc₀ : Ctx 4096 x s₀) (o : Cs) (v : Fe) (n : Nat)
    (hn : n < 2 ^ 32) :
    ∀ m s, 1 ≤ m → m < n → CKeep x s₀ s → s.gpr .esi = BitVec.ofNat 32 m →
      cenv s.mem x = Function.update (cenv s₀.mem x) o (sqn v (n - m)) →
      WP isa (.loop (.block (mul (coff o) (coff o) (coff o) ++
        ([.alu .sub .esi (.imm 1)] : List Instr))) .ne) s fun t =>
        CKeep x s₀ t ∧ cenv t.mem x = Function.update (cenv s₀.mem x) o (sqn v n) := by
  intro m s h1 h2 hk hb he
  refine WP.loop (M := isa) (Inv := fun m (s : State) => 1 ≤ m ∧ m < n ∧ CKeep x s₀ s ∧
    s.gpr .esi = BitVec.ofNat 32 m ∧
    cenv s.mem x = Function.update (cenv s₀.mem x) o (sqn v (n - m))) ?_ m s ⟨h1, h2, hk, hb, he⟩
  intro m s ⟨h1, h2, hk, hb, he⟩
  rw [WP.block_append_iff]
  refine WP.mono (mul_keep (hk.ctx hc₀) o o o) fun t ⟨kt, ht, et⟩ => ?_
  refine Wp.wp_subi fun u hu _ hz => WP.block_nil ?_
  have ku := hk.trans (ht.trans (CKeep.of_counter hu))
  have bu : u.gpr .esi = BitVec.ofNat 32 (m - 1) := by
    rw [hu.gpr, kt.esi, hb]; exact Wp.ofNat_pred h1
  have eu : cenv u.mem x = Function.update (cenv s₀.mem x) o (sqn v (n - (m - 1))) := by
    rw [hu.mem, et, he, opMul_update, show n - (m - 1) = (n - m) + 1 by omega]
    rfl
  have ev : isa.eval .ne u = some (!decide (m - 1 = 0)) := by
    show u.zf.map (!·) = _
    rw [hz, kt.esi, hb, Wp.ofNat_pred h1, Wp.ofNat_beq_zero (by omega_using [h2, hn])]
    rfl
  by_cases hm : m = 1
  · subst m
    exact .inl ⟨by rw [ev]; rfl, ku, by simpa only [Nat.sub_self, Nat.sub_zero] using eu⟩
  · exact .inr ⟨by rw [ev]; simp only [show m - 1 ≠ 0 by omega, decide_false]; rfl,
      m - 1, by omega, by omega, by omega, ku, bu, eu⟩

theorem sqnC (x : BitVec 32) (o a : Cs) (n : Nat) (hn : 2 ≤ n) (hn' : n < 2 ^ 32) :
    CSpec x (Impl.X25519.X86.Field32.sqn (coff o) (coff a) n) (opSqn o a n) := by
  intro s hc
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (mul_keep hc o a a) fun t ⟨_, ht, et⟩ => ?_
  refine Wp.wp_movi fun u hu => WP.block_nil ?_
  refine sqLoop_ok hc o (cenv s.mem x a) n hn' (n - 1) u (by omega) (by omega)
    (ht.trans (CKeep.of_counter hu)) hu.gpr ?_
  rw [hu.mem, et, show n - (n - 1) = 1 by omega]
  rfl

/-- The slots after the chain. -/
def chainEnv (e : CEnv) : CEnv :=
  opMul 1 2 1 (opSqn 2 2 50 (opMul 2 3 2 (opSqn 3 2 100
    (opMul 2 2 1 (opSqn 2 1 50 (opMul 1 2 1 (opSqn 2 2 10 (opMul 2 3 2 (opSqn 3 2 20
    (opMul 2 2 1 (opSqn 2 1 10 (opMul 1 2 1 (opSqn 2 1 5 (opMul 1 1 2
    (opMul 2 0 0 (opMul 0 0 1 (opMul 1 4 1 (opMul 1 1 1 (opMul 1 0 0
    (opMul 0 4 4 e))))))))))))))))))))

theorem chain_eq : chain =
    .seq (.block (mul (coff 0) (coff 4) (coff 4))) (
    .seq (.block (mul (coff 1) (coff 0) (coff 0) ++ mul (coff 1) (coff 1) (coff 1))) (
    .seq (.block (mul (coff 1) (coff 4) (coff 1) ++ mul (coff 0) (coff 0) (coff 1) ++
      mul (coff 2) (coff 0) (coff 0) ++ mul (coff 1) (coff 1) (coff 2))) (
    .seq (Impl.X25519.X86.Field32.sqn (coff 2) (coff 1) 5) (.seq (.block (mul (coff 1) (coff 2) (coff 1))) (
    .seq (Impl.X25519.X86.Field32.sqn (coff 2) (coff 1) 10) (.seq (.block (mul (coff 2) (coff 2) (coff 1))) (
    .seq (Impl.X25519.X86.Field32.sqn (coff 3) (coff 2) 20) (.seq (.block (mul (coff 2) (coff 3) (coff 2))) (
    .seq (Impl.X25519.X86.Field32.sqn (coff 2) (coff 2) 10) (.seq (.block (mul (coff 1) (coff 2) (coff 1))) (
    .seq (Impl.X25519.X86.Field32.sqn (coff 2) (coff 1) 50) (.seq (.block (mul (coff 2) (coff 2) (coff 1))) (
    .seq (Impl.X25519.X86.Field32.sqn (coff 3) (coff 2) 100) (.seq (.block (mul (coff 2) (coff 3) (coff 2))) (
    .seq (Impl.X25519.X86.Field32.sqn (coff 2) (coff 2) 50) (.block (mul (coff 1) (coff 2) (coff 1)))))))))))))))))) :=
  rfl

theorem chain_spec (x : BitVec 32) : CSpec x chain chainEnv := by
  rw [chain_eq]
  have h : CSpec x _ _ :=
    (mulC x 0 4 4).seq <|
    ((mulC x 1 0 0).append (mulC x 1 1 1)).seq <|
    ((((mulC x 1 4 1).append (mulC x 0 0 1)).append (mulC x 2 0 0)).append (mulC x 1 1 2)).seq <|
    (sqnC x 2 1 5 (by decide) (by decide)).seq <| (mulC x 1 2 1).seq <|
    (sqnC x 2 1 10 (by decide) (by decide)).seq <| (mulC x 2 2 1).seq <|
    (sqnC x 3 2 20 (by decide) (by decide)).seq <| (mulC x 2 3 2).seq <|
    (sqnC x 2 2 10 (by decide) (by decide)).seq <| (mulC x 1 2 1).seq <|
    (sqnC x 2 1 50 (by decide) (by decide)).seq <| (mulC x 2 2 1).seq <|
    (sqnC x 3 2 100 (by decide) (by decide)).seq <| (mulC x 2 3 2).seq <|
    (sqnC x 2 2 50 (by decide) (by decide)).seq <| (mulC x 1 2 1)
  exact h

/-- The chain on `z`: `z^(2^250 - 1)` and `z^11`. -/
def chainF (z : Fe) : Fe × Fe :=
  let t0 := z * z                 -- 2
  let t1 := t0 * t0
  let t1 := t1 * t1               -- 8
  let t1 := z * t1                -- 9
  let t0 := t0 * t1               -- 11
  let t2 := t0 * t0               -- 22
  let t1 := t1 * t2               -- 31 = 2^5 - 1
  let t2 := sqn t1 5
  let t1 := t2 * t1               -- 2^10 - 1
  let t2 := sqn t1 10
  let t2 := t2 * t1               -- 2^20 - 1
  let t3 := sqn t2 20
  let t2 := t3 * t2               -- 2^40 - 1
  let t2 := sqn t2 10
  let t1 := t2 * t1               -- 2^50 - 1
  let t2 := sqn t1 50
  let t2 := t2 * t1               -- 2^100 - 1
  let t3 := sqn t2 100
  let t2 := t3 * t2               -- 2^200 - 1
  let t2 := sqn t2 50
  (t2 * t1, t0)                   -- 2^250 - 1, 11

theorem chainF_eq (z : Fe) : chainF z = (pw z (2 ^ 250 - 1), pw z 11) := by
  rw [← congrArg chainF (VG.Proof.X25519.pw_one z)]
  simp only [chainF, VG.Proof.X25519.pw_mul, VG.Proof.X25519.sqn_pw]

theorem chainEnv_eval (e : CEnv) : chainEnv e 1 = (chainF (e 4)).1 ∧ chainEnv e 0 = (chainF (e 4)).2 := by
  simp only [chainEnv, opMul, opSqn, Function.update_apply]
  simp only [↓reduceIte, Fin.isValue, Fin.reduceEq]
  exact ⟨rfl, rfl⟩

end VG.Proof.X25519.X86.Field32
