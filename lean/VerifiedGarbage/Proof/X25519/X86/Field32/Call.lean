module

public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.X25519.Invert
public import VerifiedGarbage.Proof.X25519.X86.Ops
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Impl.X25519.X86.Field32
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.X25519.X86.Field32.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.X25519.Chain250

/-! ### `X25519.X86.Field32.Chain`, which this module and modules that import it used -/

section

/-!
# `vg_gf25519_r32_pow250` on x86 (32-bit): the addition chain

The chain runs on five slots of the working space from byte 512 (`coff`):
`E0`, `E1`, `E2`, `E3` and `AC`, the copy of `a`. Each multiplication and
run of squarings changes one of them (`mulC`, `sqnC`), and memory only in
bytes 512 to 927, the slots and X25519's product (`CKeep`), so the chain
takes the slots' values `e` to `chainEnv e` (`chain_spec`), in which `E1`
holds `a^(2^250 - 1)` and `E0` holds `a^11` (`chainEnv_eval`).
-/

@[expose] public section

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
  omega_using [h]

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
    ∀ m s, 1 ≤ m → m ≤ n → CKeep x s₀ s → s.gpr .esi = BitVec.ofNat 32 m →
      cenv s.mem x = Function.update (cenv s₀.mem x) o (sqn v (n - m)) →
      WP isa (.loop (.block (mul (coff o) (coff o) (coff o) ++
        ([.alu .sub .esi (.imm 1)] : List Instr))) .ne) s fun t =>
        CKeep x s₀ t ∧ cenv t.mem x = Function.update (cenv s₀.mem x) o (sqn v n) := by
  intro m s h1 h2 hk hb he
  refine WP.loop (M := isa) (Inv := fun m (s : State) => 1 ≤ m ∧ m ≤ n ∧ CKeep x s₀ s ∧
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
    rw [hu.mem, et, he, opMul_update, show n - (m - 1) = (n - m) + 1 by omega_using [h1, h2]]
    rfl
  have ev : isa.eval .ne u = some (!decide (m - 1 = 0)) := by
    show u.zf.map (!·) = _
    rw [hz, kt.esi, hb, Wp.ofNat_pred h1, Wp.ofNat_beq_zero (by omega_using [h2, hn])]
    rfl
  by_cases hm : m = 1
  · subst m
    exact .inl ⟨by rw [ev]; rfl, ku, by simpa only [Nat.sub_self, Nat.sub_zero] using eu⟩
  · exact .inr ⟨by rw [ev]; simp only [show m - 1 ≠ 0 by omega_using [h1, hm], decide_false]; rfl,
      m - 1, by omega_using [h1], by omega_using [h1, hm], by omega_using [h2], ku, bu, eu⟩

/-- `a` copied to `o`, unless they are the same slot. -/
theorem copyC {x : BitVec 32} {s : State} (hc : Ctx 4096 x s) (o a : Cs) :
    WP isa (.block (if coff o = coff a then [] else copy (coff o) (coff a))) s fun t =>
      CKeep x s t ∧ cenv t.mem x = Function.update (cenv s.mem x) o (cenv s.mem x a) := by
  by_cases h : o = a
  · subst h
    simp only [↓reduceIte]
    exact WP.block_nil ⟨CKeep.refl x s, (Function.update_eq_self o _).symm⟩
  · have hfit := hc.fit
    have ho := coff_slot o
    have hb : 512 ≤ coff o ∧ coff o + 32 ≤ 928 := (by decide : ∀ i : Cs, 512 ≤ coff i ∧ coff i + 32 ≤ 928) o
    simp only [show (coff o = coff a) = False from eq_false fun e => h (coff_inj e), ↓reduceIte]
    refine WP.mono (copy_ok hc (slot_below ho) (slot_below (coff_slot a))
      (slot_apart ho (coff_slot a))) fun t ⟨k, f, e⟩ =>
      ⟨⟨k.edi, k.esp, k.rd, k.wr, frameWiden f hfit hb.1 (by omega_using [hb]) (by omega_using [hb])⟩,
        funext fun i => ?_⟩
    by_cases hi : i = o
    · subst hi; rw [Function.update_self]; exact congrArg toFe e
    · rw [Function.update_of_ne hi]
      have hib : coff i + 32 ≤ 928 := (by decide : ∀ i : Cs, coff i + 32 ≤ 928) i
      exact congrArg toFe (fe_frame1 f hfit (by omega_using [hb]) (by omega_using [hib])
        (slot_ne ho (coff_slot i) fun e => hi (coff_inj e)))

theorem sqnC (x : BitVec 32) (o a : Cs) (n : Nat) (hn : 1 ≤ n) (hn' : n < 2 ^ 32) :
    CSpec x (Impl.X25519.X86.Field32.sqn (coff o) (coff a) n) (opSqn o a n) := by
  intro s hc
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (copyC hc o a) fun t ⟨ht, et⟩ => ?_
  refine Wp.wp_movi fun u hu => WP.block_nil ?_
  refine sqLoop_ok hc o (cenv s.mem x a) n hn' n u hn (Nat.le_refl _)
    (ht.trans (CKeep.of_counter hu)) hu.gpr ?_
  rw [hu.mem, et, Nat.sub_self]
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

theorem chainEnv_eval (e : CEnv) : chainEnv e 1 = (chainF (e 4)).1 ∧ chainEnv e 0 = (chainF (e 4)).2 := by
  simp only [chainEnv, opMul, opSqn, Function.update_apply]
  simp only [↓reduceIte, Fin.isValue, Fin.reduceEq]
  exact ⟨rfl, rfl⟩

end VG.Proof.X25519.X86.Field32

end

end

/-! ### `X25519.X86.Field32.Fn`, which only this module used -/

section

/-!
# `vg_gf25519_r32_pow250` on x86 (32-bit): what it computes

From its entry (`Entry`: the working space `ws` at `x`, its argument on the
stack), `entry` saves `ebx`, `esi`, `edi` and `ebp` at `SAVE`, points `edi`
at the working space and copies `a` to `AC` (`entry_ok`); the chain leaves
`a^(2^250 - 1)` in `E1` and `a^11` in `E0` (`chain_spec`); `exit` restores
the registers (`exit_ok`). `pow250Fn_ok`: the function keeps the
callee-saved registers, changes memory only in bytes 512 to 1023, and
leaves the two powers at bytes 544 and 512.
-/

@[expose] public section

namespace VG.Proof.X25519.X86.Field32

open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.X25519.X86.Field32 VG.Proof.X25519.X86 VG.Spec.X25519
open VG.Proof.X25519 (pw)

/-- The function's entry: the working space `ws = x` (its argument), writable
for 4096 bytes and within the 32-bit address space, and the argument
readable. -/
structure Entry (s : State) (x : BitVec 32) : Prop where
  ws : arg s 0 = x
  fit : x.toNat + 4096 ≤ 2 ^ 32
  wr : scR 4096 x ∈ s.wr
  read : InRegions (s.rd ++ s.wr) (argAddr s 0) 4

/-- The registers saved at `SAVE`. -/
structure Saved (x : BitVec 32) (g : Reg → BitVec 32) (m : Mem) : Prop where
  ebx : wd m x SAVE = g .ebx
  esi : wd m x (SAVE + 4) = g .esi
  edi : wd m x (SAVE + 8) = g .edi
  ebp : wd m x (SAVE + 12) = g .ebp

theorem below_AC : Below AC := by decide
theorem below_aAt : Below Impl.X25519.X86.Field32.aAt := by decide

theorem save_ok {s : State} {x : BitVec 32} (h : Entry s x) :
    WP isa (.block [.mov .eax (.mem (at_ .esp 4)), .store (at_ .eax SAVE) .ebx,
      .store (at_ .eax (SAVE + 4)) .esi, .store (at_ .eax (SAVE + 8)) .edi,
      .store (at_ .eax (SAVE + 12)) .ebp, .mov .edi (.reg .eax)]) s fun t =>
      Ctx 4096 x t ∧ t.gpr .esp = s.gpr .esp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [sub x SAVE 16] s.mem t.mem ∧ Saved x s.gpr t.mem := by
  have hfit := h.fit
  refine Wp.wp_ldm (b := .esp) (o := 4 + 4 * 0) rfl h.read fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = x := by rw [u₁.gpr]; exact h.ws
  refine Wp.wp_stm e₁ ⟨_, by rw [u₁.wr]; exact h.wr, scR_contains hfit (by decide) (by decide)⟩ fun s₂ u₂ => ?_
  refine Wp.wp_stm (by rw [u₂.gpr]; exact e₁)
    ⟨_, by rw [u₂.wr, u₁.wr]; exact h.wr, scR_contains hfit (by decide) (by decide)⟩ fun s₃ u₃ => ?_
  refine Wp.wp_stm (by rw [u₃.gpr, u₂.gpr]; exact e₁)
    ⟨_, by rw [u₃.wr, u₂.wr, u₁.wr]; exact h.wr, scR_contains hfit (by decide) (by decide)⟩ fun s₄ u₄ => ?_
  refine Wp.wp_stm (by rw [u₄.gpr, u₃.gpr, u₂.gpr]; exact e₁)
    ⟨_, by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact h.wr, scR_contains hfit (by decide) (by decide)⟩
    fun s₅ u₅ => ?_
  refine Wp.wp_mov fun s₆ u₆ => WP.block_nil ?_
  have m₆ : s₆.mem = (((s.mem.writeW (addr x SAVE) (s.gpr .ebx)).writeW (addr x (SAVE + 4)) (s.gpr .esi)).writeW
      (addr x (SAVE + 8)) (s.gpr .edi)).writeW (addr x (SAVE + 12)) (s.gpr .ebp) := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₄.gpr, u₃.gpr, u₂.gpr, u₁.other .edi (by decide),
      u₁.other .ebp (by decide), u₁.other .esi (by decide), u₁.other .ebx (by decide)]
  have hS : ∀ d, SAVE ≤ d → d + 4 ≤ SAVE + 16 → (sub x SAVE 16).Contains (addr x d) 4 := fun d h₁ h₂ =>
    sub_contains (by simp only [SAVE]; omega_using [hfit]) h₁ h₂ (by decide)
  refine ⟨⟨by rw [u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]; exact e₁, hfit,
      by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact h.wr, by decide, fun _ hW => absurd hW (by decide)⟩,
    by rw [u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ (by decide)],
    by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr], ?_, ?_⟩
  · rw [m₆]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hS _ (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (hS _ (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (hS _ (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (hS _ (by decide) (by decide))
  · rw [m₆]
    have w : ∀ {m : Mem} {d e : Nat} {v : BitVec 32}, SAVE ≤ d → d + 4 ≤ SAVE + 16 → SAVE ≤ e →
        e + 4 ≤ SAVE + 16 → d + 4 ≤ e ∨ e + 4 ≤ d → wd (m.writeW (addr x e) v) x d = wd m x d := fun h₁ h₂ h₃ h₄ hne =>
      wd_write_ne _ _ (by simp only [SAVE] at *; omega_using [hfit, h₂]) (by simp only [SAVE] at *; omega_using [hfit, h₄])
        hne
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [w (by decide) (by decide) (by decide) (by decide) (by decide),
        w (by decide) (by decide) (by decide) (by decide) (by decide),
        w (by decide) (by decide) (by decide) (by decide) (by decide), wd_write_self]
    · rw [w (by decide) (by decide) (by decide) (by decide) (by decide),
        w (by decide) (by decide) (by decide) (by decide) (by decide), wd_write_self]
    · rw [w (by decide) (by decide) (by decide) (by decide) (by decide), wd_write_self]
    · rw [wd_write_self]

theorem entry_ok {s : State} {x : BitVec 32} (h : Entry s x) :
    WP isa (.block entry) s fun t =>
      Ctx 4096 x t ∧ t.gpr .esp = s.gpr .esp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [sub x SAVE 16, sub x AC 32] s.mem t.mem ∧ Saved x s.gpr t.mem ∧
      F t.mem x AC = F s.mem x Impl.X25519.X86.Field32.aAt := by
  have hfit := h.fit
  rw [entry, WP.block_append_iff]
  refine WP.mono (save_ok h) fun t ⟨hc, esp, rd, wr, hf, hsv⟩ => ?_
  refine WP.mono (copy_ok hc below_AC below_aAt (.inr (.inl (by decide)))) fun u ⟨k, fu, eu⟩ => ?_
  have k₁ : ∀ d, SAVE ≤ d → d + 4 ≤ SAVE + 16 → wd u.mem x d = wd t.mem x d := fun d h₁ h₂ =>
    wd_frame1 fu hfit (by decide) (by simp only [SAVE] at h₂; omega_using [h₂]) (.inr (by simp only [SAVE, AC] at *; omega_using [h₁]))
  refine ⟨k.ctx hc, by rw [k.esp, esp], by rw [k.rd, rd], by rw [k.wr, wr],
    (hf.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..).trans
      (fu.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp),
    ⟨(k₁ _ (by decide) (by decide)).trans hsv.ebx, (k₁ _ (by decide) (by decide)).trans hsv.esi,
      (k₁ _ (by decide) (by decide)).trans hsv.edi, (k₁ _ (by decide) (by decide)).trans hsv.ebp⟩, ?_⟩
  simp only [F]
  rw [eu]
  exact congrArg VG.Proof.X25519.toFe (fe_frame1 hf hfit (by decide) (by decide) (.inl (by decide)))

theorem exit_ok {u : State} {x : BitVec 32} {g : Reg → BitVec 32} (hc : Ctx 4096 x u) (hsv : Saved x g u.mem) :
    WP isa (.block exit) u fun v => v.gpr .ebx = g .ebx ∧ v.gpr .esi = g .esi ∧ v.gpr .edi = g .edi ∧
      v.gpr .ebp = g .ebp ∧ v.gpr .esp = u.gpr .esp ∧ v.rd = u.rd ∧ v.wr = u.wr ∧ v.mem = u.mem := by
  have hfit := hc.fit
  refine Wp.wp_mov fun u₁ v₁ => ?_
  have edx₁ : u₁.gpr .edx = x := by rw [v₁.gpr, hc.edi]
  have rin : ∀ d, d + 4 ≤ 4096 → InRegions (u₁.rd ++ u₁.wr) (addr x d) 4 := fun d hd =>
    ⟨_, List.mem_append_right _ (by rw [v₁.wr]; exact hc.wr), scR_contains hfit hd (by decide)⟩
  refine Wp.wp_ldm (B := x) (o := SAVE) edx₁ (rin _ (by decide)) fun u₂ v₂ => ?_
  refine Wp.wp_ldm (B := x) (o := SAVE + 4) (by rw [v₂.other _ (by decide)]; exact edx₁)
    (by rw [v₂.rd, v₂.wr]; exact rin _ (by decide)) fun u₃ v₃ => ?_
  refine Wp.wp_ldm (B := x) (o := SAVE + 12) (by rw [v₃.other _ (by decide), v₂.other _ (by decide)]; exact edx₁)
    (by rw [v₃.rd, v₃.wr, v₂.rd, v₂.wr]; exact rin _ (by decide)) fun u₄ v₄ => ?_
  refine Wp.wp_ldm (B := x) (o := SAVE + 8)
    (by rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide)]; exact edx₁)
    (by rw [v₄.rd, v₄.wr, v₃.rd, v₃.wr, v₂.rd, v₂.wr]; exact rin _ (by decide)) fun u₅ v₅ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, by rw [v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd],
    by rw [v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr], by rw [v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]⟩
  · rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.mem]; exact hsv.ebx
  · rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr, v₂.mem, v₁.mem]; exact hsv.esi
  · rw [v₅.gpr, v₄.mem, v₃.mem, v₂.mem, v₁.mem]; exact hsv.edi
  · rw [v₅.other _ (by decide), v₄.gpr, v₃.mem, v₂.mem, v₁.mem]; exact hsv.ebp
  · rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide),
      v₁.other _ (by decide)]

/-- The regions the function writes: bytes 512 to 1023. -/
abbrev powW (x : BitVec 32) : List Region := [sub x 512 512]

theorem pow250Fn_ok {s : State} {x : BitVec 32} (h : Entry s x) :
    WP isa pow250Fn s fun t => (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame (powW x) s.mem t.mem ∧
      F t.mem x E1 = pw (F s.mem x Impl.X25519.X86.Field32.aAt) (2 ^ 250 - 1) ∧
      F t.mem x E0 = pw (F s.mem x Impl.X25519.X86.Field32.aAt) 11 := by
  have hfit := h.fit
  refine WP.seq (WP.mono (entry_ok h) fun t ⟨hc, esp, rd, wr, hf, hsv, ha⟩ => ?_)
  refine WP.seq (WP.mono (chain_spec x t hc) fun u ⟨ku, eu⟩ => ?_)
  have hsv' : Saved x s.gpr u.mem := by
    have k : ∀ d, SAVE ≤ d → d + 4 ≤ SAVE + 16 → wd u.mem x d = wd t.mem x d := fun d h₁ h₂ =>
      wd_frame1 ku.frame hfit (by decide) (by simp only [SAVE] at h₂; omega_using [h₂]) (.inr (by simp only [SAVE] at h₁; omega_using [h₁]))
    exact ⟨(k _ (by decide) (by decide)).trans hsv.ebx, (k _ (by decide) (by decide)).trans hsv.esi,
      (k _ (by decide) (by decide)).trans hsv.edi, (k _ (by decide) (by decide)).trans hsv.ebp⟩
  refine WP.mono (exit_ok (ku.ctx hc) hsv') fun v ⟨rb, rs, ri, rp, re, rr, rw', rm⟩ => ?_
  obtain ⟨v1, v0⟩ := chainEnv_eval (cenv t.mem x)
  have e1 := congrFun eu 1
  have e0 := congrFun eu 0
  have hz : cenv t.mem x 4 = F s.mem x Impl.X25519.X86.Field32.aAt := ha
  refine ⟨fun r hr => ?_, by rw [rr, ku.rd, rd], by rw [rw', ku.wr, wr], ?_, ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact rb
    · exact rs
    · exact ri
    · exact rp
    · rw [re, ku.esp, esp]
  · rw [rm]
    have sub512 : ∀ r ∈ [sub x SAVE 16, sub x AC 32], ∃ r' ∈ powW x, Region.Sub r r' := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;>
        exact ⟨_, List.mem_singleton_self _, sub_sub hfit (by decide) (by decide) (by decide)⟩
    refine (hf.sub sub512).trans (ku.frame.sub fun r hr => ?_)
    rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_singleton_self _, sub_sub hfit (Nat.le_refl _) (by decide) (by decide)⟩
  · rw [rm]
    change cenv u.mem x 1 = _
    rw [e1, v1, hz, chainF_eq]
  · rw [rm]
    change cenv u.mem x 0 = _
    rw [e0, v0, hz, chainF_eq]

end VG.Proof.X25519.X86.Field32

end

end


/-!
# Calls of `vg_gf25519_r32_pow250` on x86 (32-bit)

`pow250Call` (`Impl/X25519/X86/Field32.lean`) pushes the working space at
`edi` as the argument of `vg_gf25519_r32_pow250` and calls it
(`pow250Call_ok`): from a working space of 8192 bytes apart from the 8
bytes of stack the call uses (`Ctx`'s `stk`), it keeps what the field
arithmetic keeps (`Keep`), changes memory only in bytes 512 to 1023 of the
working space and that stack, and leaves `a^(2^250 - 1)` at byte 544 and
`a^11` at byte 512, for `a` the element at byte 128. The call's correctness
is the function's own (`pow250Fn_ok`, through `WP.callWith`).
-/

@[expose] public section

namespace VG.Proof.X25519.X86.Field32

open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.X25519.X86.Field32 VG.Proof.X25519.X86 VG.Spec.X25519
open VG.Proof.X25519 (pw)

theorem pow250Fn_noSp : NoSp pow250Fn := NoSp.of_all (by lit_decide)

theorem pow250Fn_stack : stackUse pow250Fn = 0 := rfl

/-- A call from a working space of `W` bytes, the 4096 the function uses apart
from the 8 bytes of stack below `esp`. -/
theorem pow250Call_ok' {W : Nat} {x : BitVec 32} {s : State} (hc : Ctx W x s) (hE : 8 ≤ (s.gpr .esp).toNat)
    (dis4 : (scR 4096 x).Disjoint (callStk s)) :
    WP isa pow250Call s fun t => Keep s t ∧ Frame [sub x 512 512, callStk s] s.mem t.mem ∧
      F t.mem x E1 = pw (F s.mem x Impl.X25519.X86.Field32.aAt) (2 ^ 250 - 1) ∧
      F t.mem x E0 = pw (F s.mem x Impl.X25519.X86.Field32.aAt) 11 := by
  have hfit : x.toNat + 4096 ≤ 2 ^ 32 := hc.fit4
  have fit : 4 * [Reg.edi].length + 4 ≤ (s.gpr .esp).toNat := hE
  let rd : List Region := [below (s.gpr .esp) 4]
  let wr : List Region := [scR 4096 x]
  obtain ⟨e, he⟩ : ∃ e, e = (pushed [.edi] s).callEntry.withRegions rd wr := ⟨_, rfl⟩
  have esp_e : e.gpr .esp = s.gpr .esp - BitVec.ofNat 32 8 := by
    rw [he, State.withRegions_gpr]; exact callEntry_esp' [.edi] s
  have entry : Entry e x := by
    refine ⟨?_, hfit, by rw [he]; exact List.mem_singleton_self _, ?_⟩
    · rw [he, arg_withRegions, callEntry_arg fit (by decide) (by decide)]; exact hc.edi
    · rw [he, argAddr_withRegions, callEntry_argAddr0]
      exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), Region.contains_self _ _⟩
  let K : Contract isa :=
    { pre := fun t => t = e
      post := fun t t' => Frame (powW x) t.mem t'.mem ∧
        F t'.mem x E1 = pw (F t.mem x Impl.X25519.X86.Field32.aAt) (2 ^ 250 - 1) ∧
        F t'.mem x E0 = pw (F t.mem x Impl.X25519.X86.Field32.aAt) 11
      pub := fun _ _ => True }
  have hret : (⟨(e.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (scR 4096 x) := by
    rw [esp_e]
    exact (dis4.sub_right (Region.sub_prefix (len := 4) (len' := 8) (by decide))).symm
  have hK : ∀ t, K.pre t → ∃ tr t', Exec isa pow250Fn t tr t' ∧ abiPreserved t t' ∧ K.post t t' := by
    intro t ht
    change t = e at ht
    subst ht
    obtain ⟨tr, t', ex, hcs, -, -, hf, h1, h0⟩ := pow250Fn_ok entry
    refine ⟨tr, t', ex, ⟨hcs, ?_⟩, hf, h1, h0⟩
    refine hf.readW (Region.contains_self _ _) (fun r hr => hret.sub_right ?_) (by decide)
    rw [List.mem_singleton.mp hr, scR_eq]
    exact sub_sub hfit (Nat.zero_le _) (by decide) (by decide)
  have cov4 : ∀ ts : List Region, scR W x ∈ ts → Covers wr ts := fun ts h =>
    Covers.of_sub fun r hr => ⟨scR W x, h, 0, by
      rw [List.mem_singleton.mp hr]; exact (BitVec.add_zero _).symm, by
      rw [List.mem_singleton.mp hr]; show 0 + 4096 ≤ W; omega_using [hc.room]⟩
  refine WP.callWith (k := K) (rd := rd) (wr := wr) hK pow250Fn_noSp (by decide) (by decide)
    (by rw [pow250Fn_stack]; exact hE)
    ⟨he.symm, Covers.append_left (Covers.of_mem fun r hr => by
        rw [List.mem_singleton.mp hr]; exact List.mem_append_right _ List.mem_cons_self)
        (cov4 _ (List.mem_append_right _ (List.mem_cons_of_mem _ hc.wr))),
      cov4 _ (List.mem_cons_of_mem _ hc.wr)⟩
    fun s' hrd hwr hcs _ ⟨s₂, hm2, hf2, h1, h0⟩ => ?_
  rw [← he] at hf2 h1 h0
  -- Memory: the call's stack, then the function's writes.
  have fs : Frame [callStk s] s.mem e.mem := by
    rw [he, State.withRegions_mem]; exact callEntry_frame (rs := [.edi]) fit (by decide)
  have fstk : ∀ q, q + 32 ≤ 4096 → F e.mem x q = F s.mem x q := fun q hq =>
    congrArg VG.Proof.X25519.toFe (fe_frame fun k hk => wd_frame fs fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact dis4.sub_left (by rw [scR_eq]; exact sub_sub hfit (Nat.zero_le _) (by omega_using [hq, hk]) (by omega_using [hq, hk])))
  -- The pop loses the argument's frame, below `esp`, apart from the slots.
  have fP : Frame [callStk s] s₂.mem s'.mem := hm2.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨callStk s, List.mem_singleton_self _, below_sub (by decide) hE⟩
  have flost : ∀ q, q + 32 ≤ 4096 → F s'.mem x q = F s₂.mem x q := fun q hq =>
    congrArg VG.Proof.X25519.toFe (fe_frame fun k hk => wd_frame fP fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact dis4.sub_left (by rw [scR_eq]; exact sub_sub hfit (Nat.zero_le _) (by omega_using [hq, hk]) (by omega_using [hq, hk])))
  refine ⟨⟨hcs .esi (by decide), hcs .edi (by decide), hcs .esp (by decide), hrd, hwr⟩, ?_, ?_, ?_⟩
  · exact ((fs.mono fun r hr => by
      rw [List.mem_singleton.mp hr]; simp) |>.trans (hf2.mono fun r hr => by
      rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..)).trans
      (fP.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · rw [flost _ (by decide), h1, fstk _ (by decide)]
  · rw [flost _ (by decide), h0, fstk _ (by decide)]

theorem pow250Call_ok {x : BitVec 32} {s : State} (hc : Ctx 8192 x s) :
    WP isa pow250Call s fun t => Keep s t ∧ Frame [sub x 512 512, callStk s] s.mem t.mem ∧
      F t.mem x E1 = pw (F s.mem x Impl.X25519.X86.Field32.aAt) (2 ^ 250 - 1) ∧
      F t.mem x E0 = pw (F s.mem x Impl.X25519.X86.Field32.aAt) 11 :=
  have h := hc.stk rfl (Nat.le_refl _)
  pow250Call_ok' hc h.1 (h.2.sub_left (Region.sub_prefix (by decide)))

end VG.Proof.X25519.X86.Field32
