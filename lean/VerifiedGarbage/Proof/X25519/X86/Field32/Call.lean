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

/-! ### The chain's slots -/

section

/-!
# Curve25519's field on x86 (32-bit): the addition chain's slots

The chain runs on five slots of the working space from byte 512 (`coff`):
`E0`, `E1`, `E2`, `E3` and `AC`, the copy of `a`. Inline, a multiplication
and a run of squarings change one of them (`mulC`, `sqnC`), and memory only
in bytes 512 to 927, the slots and X25519's product (`CKeep`). The chain
takes the slots' values `e` to `chainEnv e` (`Field32/Call`'s `chain_spec`),
in which `E1` holds `a^(2^250 - 1)` and `E0` holds `a^11`
(`chainEnv_eval`).
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

theorem chainEnv_eval (e : CEnv) : chainEnv e 1 = (chainF (e 4)).1 ∧ chainEnv e 0 = (chainF (e 4)).2 := by
  simp only [chainEnv, opMul, opSqn, Function.update_apply]
  simp only [↓reduceIte, Fin.isValue, Fin.reduceEq]
  exact ⟨rfl, rfl⟩

end VG.Proof.X25519.X86.Field32

end

end


/-! ### The functions -/

section

/-!
# `vg_gf25519_r32_mul` and `vg_gf25519_r32_sqn` on x86 (32-bit)

From the working space `ws = edi` (`Ctx 4096`), each saves `ebx`, `esi`,
`edi` and `ebp` at `SAVE` (`saveRegs_ok`), changes the element at `OpA` and
no other slot (`Upd1`): to `P · OpB` (`mulFn_ok`), or to `OpA^(2^n)` for the
count `n ≥ 1` in `eax` (`sqnFn_ok`, squaring in place counted by `esi`,
`sqLoopP`), and restores the registers (`exit_ok`). Memory changes only in
bytes 512 to 1023.
-/

@[expose] public section

namespace VG.Proof.X25519.X86.Field32

open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.X25519.X86.Field32 VG.Proof.X25519.X86 VG.Spec.X25519
open VG.Proof.X25519 (sqn)

/-- The slots from byte 512 keep their elements, but `o`, which gets `v`. -/
def Upd1 (m m' : Mem) (x : BitVec 32) (o : Nat) (v : Fe) : Prop :=
  ∀ q, isSlot 512 q = true → F m' x q = Function.update (F m x) o v q

theorem OpA_slot : isSlot 512 OpA = true := by decide
theorem OpB_slot : isSlot 512 OpB = true := by decide

/-- The registers saved at `SAVE`. -/
structure Saved (x : BitVec 32) (g : Reg → BitVec 32) (m : Mem) : Prop where
  ebx : wd m x SAVE = g .ebx
  esi : wd m x (SAVE + 4) = g .esi
  edi : wd m x (SAVE + 8) = g .edi
  ebp : wd m x (SAVE + 12) = g .ebp

theorem saveRegs_ok {W : Nat} {x : BitVec 32} {s : State} {c : Bool} (hc : Ctx W x s c) :
    WP isa (.block saveRegs) s fun t => t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [sub x SAVE 16] s.mem t.mem ∧ Saved x s.gpr t.mem := by
  have hfit := hc.fit4
  refine Wp.wp_stm (B := x) hc.edi (hc.inW4 (d := SAVE) (n := 4) (by decide) (by decide)) fun s₁ u₁ => ?_
  refine Wp.wp_stm (B := x) (by rw [u₁.gpr]; exact hc.edi)
    (by rw [u₁.wr]; exact hc.inW4 (d := SAVE + 4) (n := 4) (by decide) (by decide)) fun s₂ u₂ => ?_
  refine Wp.wp_stm (B := x) (by rw [u₂.gpr, u₁.gpr]; exact hc.edi)
    (by rw [u₂.wr, u₁.wr]; exact hc.inW4 (d := SAVE + 8) (n := 4) (by decide) (by decide)) fun s₃ u₃ => ?_
  refine Wp.wp_stm (B := x) (by rw [u₃.gpr, u₂.gpr, u₁.gpr]; exact hc.edi)
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hc.inW4 (d := SAVE + 12) (n := 4) (by decide) (by decide))
    fun s₄ u₄ => WP.block_nil ?_
  have m₄ : s₄.mem = (((s.mem.writeW (addr x SAVE) (s.gpr .ebx)).writeW (addr x (SAVE + 4)) (s.gpr .esi)).writeW
      (addr x (SAVE + 8)) (s.gpr .edi)).writeW (addr x (SAVE + 12)) (s.gpr .ebp) := by
    rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.gpr, u₁.gpr]
  have hS : ∀ d, SAVE ≤ d → d + 4 ≤ SAVE + 16 → (sub x SAVE 16).Contains (addr x d) 4 := fun d h₁ h₂ =>
    sub_contains (by simp only [SAVE]; omega_using [hfit]) h₁ h₂ (by decide)
  refine ⟨by rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
    by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr], ?_, ?_⟩
  · rw [m₄]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hS _ (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (hS _ (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (hS _ (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (hS _ (by decide) (by decide))
  · rw [m₄]
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

/-- The registers saved at `SAVE` survive a change of bytes 512 to 927. -/
theorem Saved.frame {x : BitVec 32} {g : Reg → BitVec 32} {m m' : Mem} (h : Saved x g m)
    (hf : Frame [sub x 512 416] m m') (hfit : x.toNat + 4096 ≤ 2 ^ 32) : Saved x g m' :=
  have k : ∀ d, SAVE ≤ d → d + 4 ≤ SAVE + 16 → wd m' x d = wd m x d := fun d h₁ h₂ =>
    wd_frame1 hf hfit (by decide) (by simp only [SAVE] at h₂; omega_using [h₂])
      (.inr (by simp only [SAVE] at h₁; omega_using [h₁]))
  ⟨(k _ (by decide) (by decide)).trans h.ebx, (k _ (by decide) (by decide)).trans h.esi,
    (k _ (by decide) (by decide)).trans h.edi, (k _ (by decide) (by decide)).trans h.ebp⟩

/-- The slots keep their elements across a change of the saved registers. -/
theorem F_save {x : BitVec 32} {m m' : Mem} (hf : Frame [sub x SAVE 16] m m') (hfit : x.toNat + 4096 ≤ 2 ^ 32)
    {q : Nat} (hq : isSlot 512 q = true) : F m' x q = F m x q := by
  obtain hb := slot_below hq
  simp only [Below, T] at hb
  exact congrArg VG.Proof.X25519.toFe (fe_frame1 hf hfit (by decide) (by omega_using [hb]) (.inl (by
    simp only [SAVE]; omega_using [hb])))

/-- The end of both functions: the registers restored; what holds of the
state then. -/
theorem exit_end {x : BitVec 32} {s t u : State} (hfit : x.toNat + 4096 ≤ 2 ^ 32) (hc : Ctx 4096 x u)
    (g : t.gpr = s.gpr) (hsv : Saved x s.gpr t.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (esp : u.gpr .esp = t.gpr .esp) (urd : u.rd = t.rd) (uwr : u.wr = t.wr)
    (hf : Frame [sub x SAVE 16] s.mem t.mem) (fu : Frame [sub x 512 416] t.mem u.mem) {v : Fe}
    (eu : Upd1 t.mem u.mem x OpA v) :
    WP isa (.block exit) u fun w => (∀ r ∈ calleeSaved, w.gpr r = s.gpr r) ∧ w.rd = s.rd ∧ w.wr = s.wr ∧
      Frame [sub x 512 512] s.mem w.mem ∧ Upd1 s.mem w.mem x OpA v := by
  refine WP.mono (exit_ok hc (hsv.frame fu hfit)) fun w ⟨rb, rs, ri, rp, re, rr, rw', rm⟩ => ?_
  refine ⟨fun r hr => ?_, by rw [rr, urd, rd], by rw [rw', uwr, wr], ?_, fun q hq => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact rb
    · exact rs
    · exact ri
    · exact rp
    · rw [re, esp, g]
  · rw [rm]
    exact (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact sub_sub hfit (by decide) (by decide) (by decide)⟩).trans
      (fu.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact sub_sub hfit (Nat.le_refl _) (by decide) (by decide)⟩)
  · rw [rm, eu q hq]
    by_cases e : q = OpA
    · subst e; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne e, Function.update_of_ne e, F_save hf hfit hq]

theorem mulFn_ok {x : BitVec 32} {s : State} (hc : Ctx 4096 x s) :
    WP isa mulFn s fun t => (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [sub x 512 512] s.mem t.mem ∧ Upd1 s.mem t.mem x OpA (F s.mem x OpA * F s.mem x OpB) := by
  have hfit := hc.fit
  rw [mulFn, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (saveRegs_ok hc) fun t ⟨g, rd, wr, hf, hsv⟩ => ?_
  have ct : Ctx 4096 x t := hc.keep (by rw [g]) wr (by rw [g])
  refine WP.mono (op_ok (lo := 512) ct (.mul OpA OpA OpB) (by decide)) fun u ⟨k, fu, eu⟩ => ?_
  refine exit_end hfit (k.ctx ct) g hsv rd wr k.esp k.rd k.wr hf fu fun q hq => ?_
  rw [eu q hq]
  show Function.update (F t.mem x) OpA (F t.mem x OpA * F t.mem x OpB) q = _
  rw [F_save hf hfit OpA_slot, F_save hf hfit OpB_slot]

/-- `sqnFn`'s loop: `[OpA]` squared in place, `esi` times. -/
theorem sqLoopP {x : BitVec 32} {s₀ : State} (hc₀ : Ctx 4096 x s₀) (v : Fe) (n : Nat) (hn : n < 2 ^ 32) :
    ∀ m s, 1 ≤ m → m ≤ n → CKeep x s₀ s → s.gpr .esi = BitVec.ofNat 32 m →
      Upd1 s₀.mem s.mem x OpA (sqn v (n - m)) →
      WP isa (.loop (.block (mul OpA OpA OpA ++ ([.alu .sub .esi (.imm 1)] : List Instr))) .ne) s fun t =>
        CKeep x s₀ t ∧ Upd1 s₀.mem t.mem x OpA (sqn v n) := by
  intro m s h1 h2 hk hb he
  refine WP.loop (M := isa) (Inv := fun m (s : State) => 1 ≤ m ∧ m ≤ n ∧ CKeep x s₀ s ∧
    s.gpr .esi = BitVec.ofNat 32 m ∧ Upd1 s₀.mem s.mem x OpA (sqn v (n - m))) ?_ m s ⟨h1, h2, hk, hb, he⟩
  intro m s ⟨h1, h2, hk, hb, he⟩
  rw [WP.block_append_iff]
  refine WP.mono (op_ok (lo := 512) (hk.ctx hc₀) (.mul OpA OpA OpA) (by decide)) fun t ⟨kt, ft, et⟩ => ?_
  refine Wp.wp_subi fun u hu _ hz => WP.block_nil ?_
  have ht : CKeep x s t := ⟨kt.edi, kt.esp, kt.rd, kt.wr, ft⟩
  have ku := hk.trans (ht.trans (CKeep.of_counter hu))
  have bu : u.gpr .esi = BitVec.ofNat 32 (m - 1) := by
    rw [hu.gpr, kt.esi, hb]; exact Wp.ofNat_pred h1
  have eu : Upd1 s₀.mem u.mem x OpA (sqn v (n - (m - 1))) := fun q hq => by
    rw [hu.mem, et q hq]
    show Function.update (F s.mem x) OpA (F s.mem x OpA * F s.mem x OpA) q = _
    rw [he OpA OpA_slot, Function.update_self, show n - (m - 1) = (n - m) + 1 by omega_using [h1, h2]]
    by_cases e : q = OpA
    · subst e; rw [Function.update_self, Function.update_self]; rfl
    · rw [Function.update_of_ne e, Function.update_of_ne e, he q hq, Function.update_of_ne e]
  have ev : isa.eval .ne u = some (!decide (m - 1 = 0)) := by
    show u.zf.map (!·) = _
    rw [hz, kt.esi, hb, Wp.ofNat_pred h1, Wp.ofNat_beq_zero (by omega_using [h2, hn])]
    rfl
  by_cases hm : m = 1
  · subst m
    exact .inl ⟨by rw [ev]; rfl, ku, by simpa only [Nat.sub_self, Nat.sub_zero] using eu⟩
  · exact .inr ⟨by rw [ev]; simp only [show m - 1 ≠ 0 by omega_using [h1, hm], decide_false]; rfl,
      m - 1, by omega_using [h1], by omega_using [h1, hm], by omega_using [h2], ku, bu, eu⟩

theorem sqnFn_ok {x : BitVec 32} {s : State} (hc : Ctx 4096 x s) {n : Nat}
    (hn : s.gpr .eax = BitVec.ofNat 32 n) (h1 : 1 ≤ n) (h2 : n < 2 ^ 32) :
    WP isa sqnFn s fun t => (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [sub x 512 512] s.mem t.mem ∧ Upd1 s.mem t.mem x OpA (sqn (F s.mem x OpA) n) := by
  have hfit := hc.fit
  rw [sqnFn]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (saveRegs_ok hc) fun t ⟨g, rd, wr, hf, hsv⟩ => ?_
  refine Wp.wp_mov fun t₁ u₁ => WP.block_nil ?_
  have g₁ : ∀ r, r ≠ .esi → t₁.gpr r = s.gpr r := fun r h => by rw [u₁.other r h, g]
  have ct : Ctx 4096 x t₁ := hc.keep (g₁ _ (by decide)) (by rw [u₁.wr, wr]) (g₁ _ (by decide))
  have e₁ : t₁.gpr .esi = BitVec.ofNat 32 n := by rw [u₁.gpr, g, hn]
  refine WP.seq (WP.mono (sqLoopP ct (F t₁.mem x OpA) n h2 n t₁ h1 (Nat.le_refl _) (CKeep.refl x t₁) e₁
    fun q _ => by
      rw [Nat.sub_self]
      show F t₁.mem x q = Function.update (F t₁.mem x) OpA (F t₁.mem x OpA) q
      rw [Function.update_eq_self]) fun u ⟨ku, eu⟩ => ?_)
  have fu : Frame [sub x 512 416] t.mem u.mem := by rw [← u₁.mem]; exact ku.frame
  refine exit_end hfit (ku.ctx ct) g hsv rd wr (by rw [ku.esp, g₁ _ (by decide), g]) (by rw [ku.rd, u₁.rd])
    (by rw [ku.wr, u₁.wr]) hf fu fun q hq => ?_
  rw [eu q hq, u₁.mem, F_save hf hfit OpA_slot]

end VG.Proof.X25519.X86.Field32

end

end

/-! ### The calls and the chain -/

section

/-!
# The addition chain of `pow250Call` on x86 (32-bit), by calls

A call of `vg_gf25519_r32_mul` or `vg_gf25519_r32_sqn` (`fieldCall_ok`,
through `WP.call`) keeps what the field arithmetic keeps (`Keep`), changes
memory only in bytes 512 to 1023 and the 4 bytes below `esp` of its return
address, and sets `OpA` as the function does (`mulCall_ok`, `sqnCall_ok`).
With their copies, `cmul` and `csqn` are a product and a run of squarings of
the chain's slots (`cmulS`, `csqnS`, as `SSpec`s), so the chain takes the
slots' values `e` to `chainEnv e` (`chain_spec`). `pow250Call_ok'`: `a`
copied to `AC` and the chain, from a working space of `W` bytes apart from
the 8 bytes of stack below `esp`.
-/

@[expose] public section

namespace VG.Proof.X25519.X86.Field32

open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.X25519.X86.Field32 VG.Proof.X25519.X86 VG.Spec.X25519
open VG.Proof.X25519 (pw sqn)

theorem mulFn_noSp : NoSp mulFn := NoSp.of_all (by lit_decide)
theorem sqnFn_noSp : NoSp sqnFn := NoSp.of_all (by lit_decide)
theorem mulFn_stack : stackUse mulFn = 0 := rfl
theorem sqnFn_stack : stackUse sqnFn = 0 := rfl

theorem below_AC : Below AC := by decide
theorem below_aAt : Below Impl.X25519.X86.Field32.aAt := by decide

/-- The callee's state: `s` once the call has stored its return address,
with the working space's 4096 bytes its only region. -/
abbrev callee (x : BitVec 32) (s : State) : State := s.callEntry.withRegions [] [scR 4096 x]

theorem callee_ctx {W : Nat} {x : BitVec 32} {s : State} {c : Bool} (hc : Ctx W x s c) :
    Ctx 4096 x (callee x s) :=
  ⟨by rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide)]; exact hc.edi, hc.fit4,
    List.mem_singleton_self _, Nat.le_refl _, fun _ hW => absurd hW (by decide)⟩

/-- The return address stored below `esp`. -/
theorem callee_frame {s : State} (hE : 4 ≤ (s.gpr .esp).toNat) :
    Frame [below (s.gpr .esp) 4] s.mem s.callEntry.mem :=
  Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_top (k := 4) (Nat.le_refl _) hE (by decide))

/-- The working space's elements are the callee's. -/
theorem F_callee {W : Nat} {x : BitVec 32} {s : State} {c : Bool} (hc : Ctx W x s c) (hE : 4 ≤ (s.gpr .esp).toNat)
    (dis : (scR 4096 x).Disjoint (below (s.gpr .esp) 4)) {q : Nat} (hq : q + 32 ≤ 4096) :
    F (callee x s).mem x q = F s.mem x q := by
  have hfit := hc.fit4
  exact congrArg VG.Proof.X25519.toFe (fe_frame fun k hk => wd_frame (callee_frame hE) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact dis.sub_left (by
      rw [scR_eq]; exact sub_sub hfit (Nat.zero_le _) (by omega_using [hq, hk]) (by omega_using [hq, hk])))

/-- A call of a function of the field, `n` with the code `body`, which
from the callee's state keeps the callee-saved registers and the regions,
changes memory only in bytes 512 to 1023 and sets `OpA` to `v`; from a
working space of `W` bytes apart from the 4 bytes of stack below `esp`. -/
theorem fieldCall_ok {W : Nat} {x : BitVec 32} {s : State} {c : Bool} (hc : Ctx W x s c)
    (hE : 4 ≤ (s.gpr .esp).toNat) (dis : (scR 4096 x).Disjoint (below (s.gpr .esp) 4)) {n : String}
    {body : Prog isa} (hsp : NoSp body) (hst : stackUse body = 0) {v : Fe}
    (hb : WP isa body (callee x s) fun t => (∀ r ∈ calleeSaved, t.gpr r = (callee x s).gpr r) ∧
      t.rd = (callee x s).rd ∧ t.wr = (callee x s).wr ∧ Frame [sub x 512 512] (callee x s).mem t.mem ∧
      Upd1 (callee x s).mem t.mem x OpA v) :
    WP isa (.call n body) s fun t => Keep s t ∧ Frame [sub x 512 512, below (s.gpr .esp) 4] s.mem t.mem ∧
      Upd1 s.mem t.mem x OpA v := by
  have hfit : x.toNat + 4096 ≤ 2 ^ 32 := hc.fit4
  let K : Contract isa :=
    { pre := fun t => t = callee x s
      post := fun t t' => Frame [sub x 512 512] t.mem t'.mem ∧ Upd1 t.mem t'.mem x OpA v
      pub := fun _ _ => True }
  have hK : ∀ t, K.pre t → ∃ tr t', Exec isa body t tr t' ∧ abiPreserved t t' ∧ K.post t t' := by
    intro t ht
    change t = callee x s at ht
    subst ht
    obtain ⟨tr, t', ex, hcs, -, -, hf, hu⟩ := hb
    refine ⟨tr, t', ex, ⟨hcs, ?_⟩, hf, hu⟩
    refine hf.readW (Region.contains_self _ _) (fun r hr => dis.symm.sub_right ?_) (by decide)
    rw [List.mem_singleton.mp hr, scR_eq]
    exact sub_sub hfit (by decide) (by decide) (by decide)
  have cov : ∀ ts : List Region, scR W x ∈ ts → Covers [scR 4096 x] ts := fun ts h =>
    Covers.of_sub fun r hr => ⟨scR W x, h, 0, by
      rw [List.mem_singleton.mp hr]; exact (BitVec.add_zero _).symm, by
      rw [List.mem_singleton.mp hr]; show 0 + 4096 ≤ W; omega_using [hc.room]⟩
  refine WP.call (k := K) (rd := []) (wr := [scR 4096 x]) hK hsp (by rw [hst]; exact hE) rfl
    (cov _ (List.mem_append_right _ hc.wr)) (cov _ hc.wr)
    fun s' hrd hwr hcs _ _ ⟨s₂, hm2, _, hf2, hu2⟩ => ?_
  rw [← hm2]
  refine ⟨⟨hcs .esi (by decide), hcs .edi (by decide), hcs .esp (by decide), hrd, hwr⟩, ?_, fun q hq => ?_⟩
  · exact ((callee_frame hE).mono fun r hr => by
      rw [List.mem_singleton.mp hr]; simp).trans (hf2.mono fun r hr => by
      rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..)
  · obtain hb := slot_below hq
    simp only [Below, T] at hb
    rw [hu2 q hq]
    by_cases e : q = OpA
    · subst e; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne e, Function.update_of_ne e]
      exact F_callee hc hE dis (by omega_using [hb])

theorem mulCall_ok {W : Nat} {x : BitVec 32} {s : State} {c : Bool} (hc : Ctx W x s c)
    (hE : 4 ≤ (s.gpr .esp).toNat) (dis : (scR 4096 x).Disjoint (below (s.gpr .esp) 4)) :
    WP isa mulCall s fun t => Keep s t ∧ Frame [sub x 512 512, below (s.gpr .esp) 4] s.mem t.mem ∧
      Upd1 s.mem t.mem x OpA (F s.mem x OpA * F s.mem x OpB) := by
  have h := fieldCall_ok (n := "vg_gf25519_r32_mul") hc hE dis mulFn_noSp mulFn_stack (mulFn_ok (callee_ctx hc))
  rwa [F_callee hc hE dis (by decide), F_callee hc hE dis (q := OpB) (by decide)] at h

theorem sqnCall_ok {W : Nat} {x : BitVec 32} {s : State} {c : Bool} (hc : Ctx W x s c)
    (hE : 4 ≤ (s.gpr .esp).toNat) (dis : (scR 4096 x).Disjoint (below (s.gpr .esp) 4)) {n : Nat}
    (hn : s.gpr .eax = BitVec.ofNat 32 n) (h1 : 1 ≤ n) (h2 : n < 2 ^ 32) :
    WP isa sqnCall s fun t => Keep s t ∧ Frame [sub x 512 512, below (s.gpr .esp) 4] s.mem t.mem ∧
      Upd1 s.mem t.mem x OpA (sqn (F s.mem x OpA) n) := by
  have hn' : (callee x s).gpr .eax = BitVec.ofNat 32 n := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide)]; exact hn
  have h := fieldCall_ok (n := "vg_gf25519_r32_sqn") hc hE dis sqnFn_noSp sqnFn_stack
    (sqnFn_ok (callee_ctx hc) hn' h1 h2)
  rwa [F_callee hc hE dis (by decide)] at h

/-- What a product or a run of squarings of the chain keeps: what the field
arithmetic keeps, and memory outside bytes 512 to 1023 and the 4 bytes of
stack below `esp`. -/
structure SKeep (x : BitVec 32) (s t : State) : Prop where
  keep : Keep s t
  frame : Frame [sub x 512 512, below (s.gpr .esp) 4] s.mem t.mem

theorem SKeep.trans {x : BitVec 32} {s t u : State} (h : SKeep x s t) (k : SKeep x t u) : SKeep x s u :=
  ⟨h.keep.trans k.keep, h.frame.trans (by rw [← h.keep.esp]; exact k.frame)⟩

theorem SKeep.of_keep {x : BitVec 32} {s t : State} (k : Keep s t) (f : Frame [sub x 512 416] s.mem t.mem)
    (hfit : x.toNat + 4096 ≤ 2 ^ 32) : SKeep x s t :=
  ⟨k, f.sub fun r hr => ⟨_, List.mem_cons_self .., by
    rw [List.mem_singleton.mp hr]; exact sub_sub hfit (Nat.le_refl _) (by decide) (by decide)⟩⟩

/-- `c` takes the slots' values `e` to `f e`, keeping what `SKeep` keeps,
from a working space of `W` bytes apart from the 4 bytes of stack below
`esp`. -/
def SSpec (W : Nat) (x : BitVec 32) (c : Prog isa) (f : CEnv → CEnv) : Prop :=
  ∀ s, Ctx W x s → 4 ≤ (s.gpr .esp).toNat → (scR 4096 x).Disjoint (below (s.gpr .esp) 4) →
    WP isa c s fun t => SKeep x s t ∧ cenv t.mem x = f (cenv s.mem x)

theorem SSpec.seq {W : Nat} {x : BitVec 32} {c d : Prog isa} {f g : CEnv → CEnv}
    (h : SSpec W x c f) (k : SSpec W x d g) : SSpec W x (.seq c d) (fun e => g (f e)) :=
  fun s hc hE hd => WP.seq (WP.mono (h s hc hE hd) fun t ⟨ht, et⟩ => by
    have sp := ht.keep.esp
    exact WP.mono (k t (ht.keep.ctx hc) (by rw [sp]; exact hE) (by rw [sp]; exact hd))
      fun u ⟨hu, eu⟩ => ⟨ht.trans hu, by rw [eu, et]⟩)

theorem coff_ne_OpA (i : Cs) : coff i ≠ OpA := (by decide : ∀ i : Cs, coff i ≠ OpA) i
theorem coff_ne_OpB (i : Cs) : coff i ≠ OpB := (by decide : ∀ i : Cs, coff i ≠ OpB) i
theorem OpA_ne_OpB : OpA ≠ OpB := by decide

/-- A copy of slots from byte 512, with what it keeps. -/
theorem copyS {W : Nat} {x : BitVec 32} {s : State} (hc : Ctx W x s) {o a : Nat} (ho : isSlot 512 o = true)
    (ha : isSlot 512 a = true) :
    WP isa (.block (copy o a)) s fun t => Keep s t ∧ Frame [sub x 512 416] s.mem t.mem ∧
      F t.mem x o = F s.mem x a ∧ ∀ q, isSlot 512 q = true → q ≠ o → F t.mem x q = F s.mem x q := by
  have hv : opValid 512 (.copy o a) = true := by
    simp only [opValid, opOut, opIns, ho, ha, List.all_cons, List.all_nil, Bool.and_self]
  refine WP.mono (op_ok (lo := 512) hc (.copy o a) hv) fun t ⟨k, f, e⟩ => ⟨k, f, ?_, fun q hq h => ?_⟩
  · rw [e o ho]; exact Function.update_self ..
  · rw [e q hq]; exact Function.update_of_ne h ..

theorem cmulS {W : Nat} (x : BitVec 32) (o a b : Cs) :
    SSpec W x (cmul (coff o) (coff a) (coff b)) (opMul o a b) := by
  intro s hc hE hd
  have hfit := hc.fit4
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (copyS hc OpA_slot (coff_slot a)) fun t₁ ⟨k₁, f₁, p₁, a₁⟩ => ?_
  obtain c₁ := k₁.ctx hc
  refine WP.mono (copyS c₁ OpB_slot (coff_slot b)) fun t₂ ⟨k₂, f₂, q₂, a₂⟩ => ?_
  obtain c₂ := k₂.ctx c₁
  obtain sp₂ : t₂.gpr .esp = s.gpr .esp := k₂.esp.trans k₁.esp
  refine WP.seq (WP.mono (mulCall_ok c₂ (by rw [sp₂]; exact hE) (by rw [sp₂]; exact hd)) fun t₃ ⟨k₃, f₃, e₃⟩ => ?_)
  obtain c₃ := k₃.ctx c₂
  refine WP.mono (copyS c₃ (coff_slot o) OpA_slot) fun t₄ ⟨k₄, f₄, o₄, a₄⟩ => ?_
  obtain p₃ : F t₃.mem x OpA = F t₂.mem x OpA * F t₂.mem x OpB := by rw [e₃ OpA OpA_slot]; exact Function.update_self ..
  obtain a₃ : ∀ q, isSlot 512 q = true → q ≠ OpA → F t₃.mem x q = F t₂.mem x q := fun q hq h => by
    rw [e₃ q hq]; exact Function.update_of_ne h ..
  refine ⟨((SKeep.of_keep k₁ f₁ hfit).trans (SKeep.of_keep k₂ f₂ hfit)).trans
    ((⟨k₃, f₃⟩ : SKeep x t₂ t₃).trans (SKeep.of_keep k₄ f₄ hfit)), funext fun i => ?_⟩
  show F t₄.mem x (coff i) = opMul o a b (cenv s.mem x) i
  by_cases h : i = o
  · subst h
    rw [o₄, p₃, a₂ OpA OpA_slot OpA_ne_OpB, p₁, q₂, a₁ (coff b) (coff_slot b) (coff_ne_OpA b)]
    simp only [opMul, Function.update_self]
    rfl
  · rw [a₄ (coff i) (coff_slot i) (fun e => h (coff_inj e)), a₃ _ (coff_slot i) (coff_ne_OpA i),
      a₂ _ (coff_slot i) (coff_ne_OpB i), a₁ _ (coff_slot i) (coff_ne_OpA i)]
    simp only [opMul, Function.update_of_ne h]
    rfl

theorem csqnS {W : Nat} (x : BitVec 32) (o a : Cs) (n : Nat) (h1 : 1 ≤ n) (h2 : n < 2 ^ 32) :
    SSpec W x (csqn (coff o) (coff a) n) (opSqn o a n) := by
  intro s hc hE hd
  have hfit := hc.fit4
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (copyS hc OpA_slot (coff_slot a)) fun t₁ ⟨k₁, f₁, p₁, a₁⟩ => ?_
  refine Wp.wp_movi fun t₂ u₂ => WP.block_nil ?_
  obtain k₂ : Keep t₁ t₂ := ⟨u₂.other _ (by decide), u₂.other _ (by decide), u₂.other _ (by decide), u₂.rd, u₂.wr⟩
  obtain c₂ := k₂.ctx (k₁.ctx hc)
  obtain sp₂ : t₂.gpr .esp = s.gpr .esp := k₂.esp.trans k₁.esp
  refine WP.seq (WP.mono (sqnCall_ok c₂ (by rw [sp₂]; exact hE) (by rw [sp₂]; exact hd) u₂.gpr h1 h2)
    fun t₃ ⟨k₃, f₃, e₃⟩ => ?_)
  obtain c₃ := k₃.ctx c₂
  refine WP.mono (copyS c₃ (coff_slot o) OpA_slot) fun t₄ ⟨k₄, f₄, o₄, a₄⟩ => ?_
  obtain p₃ : F t₃.mem x OpA = sqn (F t₂.mem x OpA) n := by rw [e₃ OpA OpA_slot]; exact Function.update_self ..
  obtain a₃ : ∀ q, isSlot 512 q = true → q ≠ OpA → F t₃.mem x q = F t₂.mem x q := fun q hq h => by
    rw [e₃ q hq]; exact Function.update_of_ne h ..
  obtain f₂ : Frame [sub x 512 416] t₁.mem t₂.mem := by rw [u₂.mem]; exact Frame.refl _ _
  refine ⟨((SKeep.of_keep k₁ f₁ hfit).trans (SKeep.of_keep k₂ f₂ hfit)).trans
    ((⟨k₃, f₃⟩ : SKeep x t₂ t₃).trans (SKeep.of_keep k₄ f₄ hfit)), funext fun i => ?_⟩
  show F t₄.mem x (coff i) = opSqn o a n (cenv s.mem x) i
  by_cases h : i = o
  · subst h
    rw [o₄, p₃, u₂.mem, p₁]
    simp only [opSqn, Function.update_self]
    rfl
  · rw [a₄ (coff i) (coff_slot i) (fun e => h (coff_inj e)), a₃ _ (coff_slot i) (coff_ne_OpA i), u₂.mem,
      a₁ _ (coff_slot i) (coff_ne_OpA i)]
    simp only [opSqn, Function.update_of_ne h]
    rfl

/-- A square, as a run of one squaring. -/
theorem sq1S {W : Nat} (x : BitVec 32) (o a : Cs) :
    SSpec W x (csqn (coff o) (coff a) 1) (opMul o a a) := fun s hc hE hd =>
  WP.mono (csqnS x o a 1 (by decide) (by decide) s hc hE hd) fun _ ⟨k, e⟩ => ⟨k, by rw [e]; rfl⟩

theorem chain_eq : chain =
    .seq (csqn (coff 0) (coff 4) 1) (.seq (csqn (coff 1) (coff 0) 1) (.seq (csqn (coff 1) (coff 1) 1) (
    .seq (cmul (coff 1) (coff 4) (coff 1)) (.seq (cmul (coff 0) (coff 0) (coff 1)) (
    .seq (csqn (coff 2) (coff 0) 1) (.seq (cmul (coff 1) (coff 1) (coff 2)) (
    .seq (csqn (coff 2) (coff 1) 5) (.seq (cmul (coff 1) (coff 2) (coff 1)) (
    .seq (csqn (coff 2) (coff 1) 10) (.seq (cmul (coff 2) (coff 2) (coff 1)) (
    .seq (csqn (coff 3) (coff 2) 20) (.seq (cmul (coff 2) (coff 3) (coff 2)) (
    .seq (csqn (coff 2) (coff 2) 10) (.seq (cmul (coff 1) (coff 2) (coff 1)) (
    .seq (csqn (coff 2) (coff 1) 50) (.seq (cmul (coff 2) (coff 2) (coff 1)) (
    .seq (csqn (coff 3) (coff 2) 100) (.seq (cmul (coff 2) (coff 3) (coff 2)) (
    .seq (csqn (coff 2) (coff 2) 50) (cmul (coff 1) (coff 2) (coff 1))))))))))))))))))))) :=
  rfl

theorem chain_spec {W : Nat} (x : BitVec 32) : SSpec W x chain chainEnv := by
  rw [chain_eq]
  have h : SSpec W x _ _ :=
    (sq1S x 0 4).seq <| (sq1S x 1 0).seq <| (sq1S x 1 1).seq <|
    (cmulS x 1 4 1).seq <| (cmulS x 0 0 1).seq <| (sq1S x 2 0).seq <| (cmulS x 1 1 2).seq <|
    (csqnS x 2 1 5 (by decide) (by decide)).seq <| (cmulS x 1 2 1).seq <|
    (csqnS x 2 1 10 (by decide) (by decide)).seq <| (cmulS x 2 2 1).seq <|
    (csqnS x 3 2 20 (by decide) (by decide)).seq <| (cmulS x 2 3 2).seq <|
    (csqnS x 2 2 10 (by decide) (by decide)).seq <| (cmulS x 1 2 1).seq <|
    (csqnS x 2 1 50 (by decide) (by decide)).seq <| (cmulS x 2 2 1).seq <|
    (csqnS x 3 2 100 (by decide) (by decide)).seq <| (cmulS x 2 3 2).seq <|
    (csqnS x 2 2 50 (by decide) (by decide)).seq <| (cmulS x 1 2 1)
  exact h

/-- The chain from a working space of `W` bytes, the 4096 it uses apart
from the 8 bytes of stack below `esp`. -/
theorem pow250Call_ok' {W : Nat} {x : BitVec 32} {s : State} (hc : Ctx W x s) (hE : 8 ≤ (s.gpr .esp).toNat)
    (dis4 : (scR 4096 x).Disjoint (callStk s)) :
    WP isa pow250Call s fun t => Keep s t ∧ Frame [sub x 512 512, callStk s] s.mem t.mem ∧
      F t.mem x E1 = pw (F s.mem x Impl.X25519.X86.Field32.aAt) (2 ^ 250 - 1) ∧
      F t.mem x E0 = pw (F s.mem x Impl.X25519.X86.Field32.aAt) 11 := by
  have hfit := hc.fit4
  have b48 : Region.Sub (below (s.gpr .esp) 4) (callStk s) := below_sub (by decide) hE
  refine WP.seq (WP.mono (copy_ok hc below_AC below_aAt (.inr (.inl (by decide)))) fun t ⟨k, ft, et⟩ => ?_)
  have sp : t.gpr .esp = s.gpr .esp := k.esp
  refine WP.mono (chain_spec x t (k.ctx hc) (by rw [sp]; omega_using [hE]) (by rw [sp]; exact dis4.sub_right b48))
    fun u ⟨ku, eu⟩ => ?_
  obtain ⟨v1, v0⟩ := chainEnv_eval (cenv t.mem x)
  have hz : cenv t.mem x 4 = F s.mem x Impl.X25519.X86.Field32.aAt := by
    show VG.Proof.X25519.toFe (fe t.mem x AC) = _
    rw [et]; rfl
  have fu := ku.frame
  rw [sp] at fu
  refine ⟨k.trans ku.keep, ?_, ?_, ?_⟩
  · exact (ft.sub fun r hr => ⟨_, List.mem_cons_self .., by
      rw [List.mem_singleton.mp hr]; exact sub_sub hfit (by decide) (by decide) (by decide)⟩).trans
      (fu.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, b48⟩)
  · change cenv u.mem x 1 = _
    rw [eu, v1, hz, chainF_eq]
  · change cenv u.mem x 0 = _
    rw [eu, v0, hz, chainF_eq]

theorem pow250Call_ok {x : BitVec 32} {s : State} (hc : Ctx 8192 x s) :
    WP isa pow250Call s fun t => Keep s t ∧ Frame [sub x 512 512, callStk s] s.mem t.mem ∧
      F t.mem x E1 = pw (F s.mem x Impl.X25519.X86.Field32.aAt) (2 ^ 250 - 1) ∧
      F t.mem x E0 = pw (F s.mem x Impl.X25519.X86.Field32.aAt) 11 :=
  have h := hc.stk rfl (Nat.le_refl _)
  pow250Call_ok' hc h.1 (h.2.sub_left (Region.sub_prefix (by decide)))

end VG.Proof.X25519.X86.Field32

end

end
