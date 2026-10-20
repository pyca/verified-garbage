module
public import VerifiedGarbage.Proof.Camellia.Arm.KeyPair
public import VerifiedGarbage.Proof.Camellia.Arm.Prologue
public import VerifiedGarbage.Proof.Camellia.Common

import VerifiedGarbage.Proof.Camellia.Arm.Copy
import VerifiedGarbage.Proof.Camellia.Arm.Fl
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Camellia's key schedule on ARMv7: `KA` and `KB`

`kaKb_wp`: from `KL` and `KR` in their slots and the constants' table, the
loop of three pairs of rounds on the running value (`pairPlain_step`), with
the XORs and copies between them (`wordsOp_ok`), leaves `KA` and `KB`
(`kaD2`, `kaD3`) in their slots.
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Camellia.Arm
open VG.Impl.Aes.Arm (q sb t0 t1 u7 kp movR ldS stS eorR lsrOp)
open VG.Proof.Camellia (byteOf byteOf_xor pair sigE kaD1 kaD2 kaD3 kaW)

/-! ## Operations on four words -/

/-- An operation on word `k` of the values at `w` and `x`: slot `w + k`
becomes `F` of slots `x + k` and `w + k`. -/
def OpOk (op : Nat → List Instr) (F : BitVec 32 → BitVec 32 → BitVec 32) (w x : Nat) : Prop :=
  ∀ k < 4, ∀ (s : State) (b : BitVec 32), s.gpr sb = b → ScrIn s.wr b →
    ∃ s', runBlock isa (op k) s = some s' ∧
      s'.mem = s.mem.writeW (wordAddr b (w + k))
        (F (s.mem.readW (wordAddr b (x + k)) 32) (s.mem.readW (wordAddr b (w + k)) 32)) ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

theorem copy_op (w x : Nat) (hw : w + 4 ≤ slots) (hx : x + 4 ≤ slots) :
    OpOk (fun k => [ldS t0 (x + k), stS (w + k) t0]) (fun a _ => a) w x := by
  intro k hk s b hb hs
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := ldSlot_ok s t0 sb (k := x + k) hb (by omega) hs
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂, sp₂, -, -⟩ := stSlot_ok s₁ t0 sb (k := w + k) (by rw [o₁ _ (by decide), hb])
    (by omega) (by rw [wr₁]; exact hs)
  refine ⟨s₂, ?_, by rw [m₂, v₁, m₁], fun r h0 _ => by rw [g₂, o₁ r h0], by rw [rd₂, rd₁], by rw [wr₂, wr₁],
    by rw [sp₂, sp₁]⟩
  show runBlock isa [ldS t0 (x + k), stS (w + k) t0] s = _
  rw [show ([ldS t0 (x + k), stS (w + k) t0] : List Instr) = [.ldr t0 sb (4 * (x + k))] ++
    [.str t0 sb (4 * (w + k))] from rfl, runBlock_app, e₁, Option.bind_some, e₂]

theorem xor_op (w x : Nat) (hw : w + 4 ≤ slots) (hx : x + 4 ≤ slots) :
    OpOk (fun k => [ldS t0 (x + k), ldS t1 (w + k), eorR t0 t0 t1, stS (w + k) t0]) (fun a c => a ^^^ c) w x := by
  intro k hk s b hb hs
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := ldSlot_ok s t0 sb (k := x + k) hb (by omega) hs
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := ldSlot_ok s₁ t1 sb (k := w + k) (by rw [o₁ _ (by decide), hb])
    (by omega) (by rw [wr₁]; exact hs)
  let s₃ := s₂.setReg t0 (s₂.gpr t0 ^^^ s₂.gpr t1)
  have e₃ : runBlock isa [eorR t0 t0 t1] s₂ = some s₃ := by
    rw [runBlock_cons, show exec (eorR t0 t0 t1) s₂ = some s₃ by simp only [eorR, exec, Op2.eval, Option.map_some]; rfl,
      runStep_some, runBlock_nil]
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄, sp₄, -, -⟩ := stSlot_ok s₃ t0 sb (k := w + k)
    (by rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), o₂ _ (by decide), o₁ _ (by decide), hb])
    (by omega) (by rw [RegUpd.wr_setReg, wr₂, wr₁]; exact hs)
  refine ⟨s₄, ?_, ?_, fun r h0 h1 => by rw [g₄, RegUpd.gpr_setReg_of_ne _ _ h0, o₂ r h1, o₁ r h0],
    by rw [rd₄, RegUpd.rd_setReg, rd₂, rd₁], by rw [wr₄, RegUpd.wr_setReg, wr₂, wr₁],
    by rw [sp₄, RegUpd.sp_setReg, sp₂, sp₁]⟩
  · show runBlock isa [ldS t0 (x + k), ldS t1 (w + k), eorR t0 t0 t1, stS (w + k) t0] s = _
    rw [show ([ldS t0 (x + k), ldS t1 (w + k), eorR t0 t0 t1, stS (w + k) t0] : List Instr) =
      [.ldr t0 sb (4 * (x + k))] ++ ([.ldr t1 sb (4 * (w + k))] ++ ([eorR t0 t0 t1] ++
        [.str t0 sb (4 * (w + k))])) from rfl, runBlock_app, e₁, Option.bind_some, runBlock_app, e₂,
      Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄]
  · rw [m₄, RegUpd.gpr_setReg_self, RegUpd.mem_setReg, m₂, m₁, o₂ _ (by decide), v₁, v₂, m₁]

/-- Four words of an operation. -/
theorem wordsOp_ok {op : Nat → List Instr} {F : BitVec 32 → BitVec 32 → BitVec 32} {w x : Nat}
    (hop : OpOk op F w x) (hsep : x + 4 ≤ w ∨ w + 4 ≤ x) (hw : w + 4 ≤ slots) (hx : x + 4 ≤ slots)
    {b : BitVec 32} :
    ∀ n ≤ 4, ∀ s : State, s.gpr sb = b → ScrIn s.wr b →
      ∃ s', runBlock isa ((List.range n).flatMap op) s = some s' ∧
        (∀ k < n, s'.mem.readW (wordAddr b (w + k)) 32 =
          F (s.mem.readW (wordAddr b (x + k)) 32) (s.mem.readW (wordAddr b (w + k)) 32)) ∧
        (∀ j < slots, j < w ∨ w + n ≤ j → s'.mem.readW (wordAddr b j) 32 = s.mem.readW (wordAddr b j) 32) ∧
        (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
        Frame [⟨wordAddr b w, 4 * n⟩] s.mem s'.mem
  | 0, _, s, _, _ => ⟨s, rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl,
      rfl, Frame.refl _ _⟩
  | n + 1, hn, s, hb, hs => by
    have hfit := hs.fit
    obtain ⟨s₁, e₁, v₁, o₁, g₁, rd₁, wr₁, sp₁, f₁⟩ := wordsOp_ok hop hsep hw hx n (by omega) s hb hs
    obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂, sp₂⟩ := hop n (by omega) s₁ b (by rw [g₁ _ (by decide) (by decide), hb])
      (by rw [wr₁]; exact hs)
    have hfw : (s.gpr sb).toNat + 4 * slots ≤ 2 ^ 32 := by rw [hb]; exact hfit
    refine ⟨s₂, by rw [List.range_succ, List.flatMap_append, runBlock_app, e₁, Option.bind_some,
        List.flatMap_singleton]; exact e₂, fun k hk => ?_, fun j hj h => ?_,
      fun r h0 h1 => by rw [g₂ r h0 h1, g₁ r h0 h1], by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [sp₂, sp₁], ?_⟩
    · rw [m₂, readW_slot_write hfit _ (by omega) (by omega)]
      by_cases hkn : k = n
      · subst hkn
        rw [ite_eq_left rfl, o₁ _ (by omega) (by omega), o₁ _ (by omega) (by omega)]
      · rw [ite_eq_right (by omega), v₁ k (by omega)]
    · rw [m₂, readW_slot_write hfit _ hj (by omega), ite_eq_right (by omega), o₁ j hj (by omega)]
    · have hf2 := hfit
      rw [slots_eq] at hf2 hw
      have hsub1 : Region.Sub ⟨wordAddr b w, 4 * n⟩ ⟨wordAddr b w, 4 * (n + 1)⟩ := Region.sub_prefix (by omega)
      have hsub2 : Region.Sub ⟨wordAddr b (w + n), 4⟩ ⟨wordAddr b w, 4 * (n + 1)⟩ := by
        simp only [wordAddr]
        rw [VG.Arm.addr_add (by omega), VG.Arm.addr_add (by omega)]
        exact VG.Offset.sub _ (by omega) (by omega)
      rw [m₂]
      exact (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
          simp only [List.mem_singleton] at hr; subst hr; exact hsub1⟩).trans
        (((Frame.refl _ _).writeW (r := ⟨wordAddr b (w + n), 4⟩) (List.mem_singleton_self _) _
          (Region.contains_self _ _)).sub fun r hr => ⟨_, List.mem_singleton_self _, by
            simp only [List.mem_singleton] at hr; subst hr; exact hsub2⟩)

/-! ## On the values -/

theorem VW_copy {s s' : State} {w x : Nat} {v : BitVec 64 × BitVec 64} (hv : VW s x v)
    (h : ∀ k < 4, slotW s' (w + k) = slotW s (x + k)) : VW s' w v := fun c hc j hj => by
  rw [h _ (by omega)]; exact hv c hc j hj

theorem VW_xor {s s' : State} {w x : Nat} {v u : BitVec 64 × BitVec 64} (hv : VW s x v) (hu : VW s w u)
    (h : ∀ k < 4, slotW s' (w + k) = slotW s (x + k) ^^^ slotW s (w + k)) :
    VW s' w (v.1 ^^^ u.1, v.2 ^^^ u.2) := fun c hc j hj => by
  rw [h _ (by omega), BitVec.getLsbD_xor, hv c hc j hj, hu c hc j hj]
  by_cases h8 : c < 8
  · simp only [itePos h8, byteOf_xor, BitVec.getLsbD_xor]
  · simp only [iteNeg h8, byteOf_xor, BitVec.getLsbD_xor]

theorem kaSlot_eq : kaSlot = 644 := rfl
theorem kbSlot_eq : kbSlot = 648 := rfl
theorem cntSlot_eq : cntSlot = 616 := rfl

/-! ## Under the rounds' context -/

/-- Four words of an operation in the tail buffer, under `Ctx`. -/
theorem words_ctx {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {op : Nat → List Instr} {F : BitVec 32 → BitVec 32 → BitVec 32} {w x : Nat} (hop : OpOk op F w x)
    (hsep : x + 4 ≤ w ∨ w + 4 ≤ x) (hw1 : tailSlot ≤ w) (hw2 : w + 4 ≤ tailSlot + 32) (hx : x + 4 ≤ slots) :
    ∃ s', runBlock isa ((List.range 4).flatMap op) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      (∀ k < 4, slotW s' (w + k) = F (slotW s (x + k)) (slotW s (w + k))) ∧
      (∀ j < slots, j < w ∨ w + 4 ≤ j → slotW s' j = slotW s j) := by
  have hs := hc.scr hp
  have hfit := hs.fit
  rw [tailSlot_eq] at hw1 hw2
  have hw : w + 4 ≤ slots := by rw [slots_eq]; omega
  obtain ⟨s', e', v', o', g', rd', wr', -, f'⟩ := wordsOp_ok hop hsep hw hx 4 (Nat.le_refl _) s rfl ⟨hs.wr, hfit⟩
  have hb : s'.gpr sb = s.gpr sb := g' _ (by decide) (by decide)
  refine ⟨s', e', hc.step rd' wr' (fun r h1 _ => g' r (fun h => h1 (h ▸ by decide)) (fun h => h1 (h ▸ by decide)))
    ?_, g' _ (by decide) (by decide), fun k hk => by simp only [slotW, hb]; exact v' k hk,
    fun j hj h => by simp only [slotW, hb]; exact o' j hj h⟩
  refine f'.sub fun r hr => ⟨_, by simp only [ctxRegions, List.mem_cons]; exact .inr (.inr (.inl rfl)), ?_⟩
  simp only [List.mem_singleton] at hr; subst hr
  rw [slots_eq] at hfit
  simp only [wordAddr, hc.base]
  rw [← hc.base, VG.Arm.addr_add (by omega), VG.Arm.addr_add (by rw [tailSlot_eq]; omega)]
  exact VG.Offset.sub _ (by rw [tailSlot_eq]; omega) (by rw [tailSlot_eq]; omega)

/-- `KA` and `KB`, from `KL` and `KR`. -/
structure KaPost (s₀ : State) (KL KR : BitVec 64 × BitVec 64) (s : State) : Prop where
  ctx : Ctx s₀ s
  kl : VW s klSlot KL
  kr : VW s krSlot KR
  ka : VW s kaSlot (kaD2 KL KR)
  kb : VW s kbSlot (kaD3 KL KR)

/-- Before pair `i`. -/
structure KaInv (s₀ : State) (KL KR : BitVec 64 × BitVec 64) (i : Nat) (s : State) : Prop where
  lt : i < 3
  ctx : Ctx s₀ s
  kp : AtEntry s (s₀.gpr sb) (2 * i)
  w : VW s wSlot (kaW KL KR i)
  kl : VW s klSlot KL
  kr : VW s krSlot KR
  ka : 2 ≤ i → VW s kaSlot (kaD2 KL KR)
  cnt : slotW s cntSlot = BitVec.ofNat 32 (3 - i)

/-- The pair's result. -/
theorem pair_kaW (KL KR : BitVec 64 × BitVec 64) {i : Nat} (hi : i < 3) :
    pair (sigE (2 * i)) (sigE (2 * i + 1)) (kaW KL KR i) =
      (if i = 0 then kaD1 KL KR else if i = 1 then kaD2 KL KR else kaD3 KL KR) := by
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl <;> rfl

/-- After pair `i` and the operations, before the count's step. -/
structure KaMid (s₀ : State) (KL KR : BitVec 64 × BitVec 64) (i : Nat) (s : State) : Prop where
  ctx : Ctx s₀ s
  kp : AtEntry s (s₀.gpr sb) (2 * i + 2)
  w : VW s wSlot (kaW KL KR (i + 1))
  kl : VW s klSlot KL
  kr : VW s krSlot KR
  ka : 1 ≤ i → VW s kaSlot (kaD2 KL KR)
  kb : i = 2 → VW s kbSlot (kaD3 KL KR)
  cnt : slotW s cntSlot = BitVec.ofNat 32 (3 - i)

theorem VW.keep {s s' : State} {a : Nat} {v : BitVec 64 × BitVec 64} (h : VW s a v)
    (hk : ∀ j < slots, j < wSlot ∨ wSlot + 4 ≤ j → slotW s' j = slotW s j)
    (ha : a + 4 ≤ wSlot ∨ wSlot + 4 ≤ a) (has : a + 4 ≤ slots) : VW s' a v :=
  h.congr fun i hi => hk _ (by omega) (by omega)

/-- `cmp r, #v`. -/
theorem cmpImm_ok (s : State) (r : Reg) {v : BitVec 32} (hv : encodable v = true) :
    runBlock isa [.cmp r (.imm v)] s = some (subFlags s (s.gpr r) v) := by
  rw [runBlock_cons, show exec (.cmp r (.imm v)) s = some (subFlags s (s.gpr r) v) by
    simp only [exec, Op2.eval, hv, ↓reduceIte, Option.map_some], runStep_some, runBlock_nil]

/-- `mov t1, t0, lsr #1; cmp t1, #0`. -/
theorem cntTest_ok (s : State) :
    ∃ s', runBlock isa [.mov t1 (lsrOp t0 1), .cmp t1 (.imm 0)] s = some s' ∧
      s'.z = (s.gpr t0 >>> 1 - 0 == 0) ∧ (∀ r, r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  let s₁ := s.setReg t1 (s.gpr t0 >>> 1)
  refine ⟨subFlags s₁ (s₁.gpr t1) 0, ?_, by rw [subFlags_z, RegUpd.gpr_setReg_self],
    fun r h => by rw [subFlags_gpr, RegUpd.gpr_setReg_of_ne _ _ h], rfl, rfl, rfl, rfl⟩
  rw [runBlock_cons, show exec (.mov t1 (lsrOp t0 1)) s = some s₁ by simp [exec, lsrOp, Op2.eval, s₁],
    runStep_some, cmpImm_ok s₁ t1 (by decide)]

theorem kaStep_wp {s₀ : State} {KL KR : BitVec 64 × BitVec 64} (hp : KeyCtx s₀ 6 sigE) {i : Nat} {s : State}
    (h : KaInv s₀ KL KR i s) {c : Prog isa} {Q : State → Prop} (hcont : ∀ s', KaMid s₀ KL KR i s' → WP isa c s' Q) :
    WP isa (.seq (.block (pairPlain ++ [ldS t0 cntSlot, .mov t1 (lsrOp t0 1), .cmp t1 (.imm 0)]))
      (.seq (.ite .ne
          (.seq (.block [.cmp t0 (.imm 3)])
            (.ite .eq (.block (xorWords wSlot klSlot))
              (.block (copyWords kaSlot wSlot ++ xorWords wSlot krSlot))))
          (.block (copyWords kbSlot wSlot))) c)) s Q := by
  have hi := h.lt
  obtain ⟨s₁, e₁, c₁, k₁, w₁, o₁⟩ := pairPlain_step hp h.ctx h.kp (by omega) (by omega) h.w
  rw [pair_kaW KL KR hi] at w₁
  have hs₁ := c₁.scr hp
  have hb₁ := c₁.base
  have keep₁ : ∀ a, keySlot ≤ a → a + 4 ≤ wSlot ∨ wSlot + 4 ≤ a → a + 4 ≤ slots →
      ∀ v, VW s a v → VW s₁ a v := fun a h1 ha has v hv =>
    hv.congr fun j hj => o₁ _ (by omega) (by omega) (by omega)
  have kl₁ := keep₁ klSlot (by decide) (by decide) (by decide) _ h.kl
  have kr₁ := keep₁ krSlot (by decide) (by decide) (by decide) _ h.kr
  have cnt₁ : slotW s₁ cntSlot = BitVec.ofNat 32 (3 - i) := by
    rw [o₁ _ (by decide) (by decide) (by decide), h.cnt]
  -- The count's tests.
  obtain ⟨s₂, e₂, v₂, g₂, m₂, rd₂, wr₂, sp₂⟩ := ldSlot_ok s₁ t0 sb (k := cntSlot) rfl (by decide)
    ⟨hs₁.wr, hs₁.fit⟩
  obtain ⟨s₄, e₃, z₄, g₄, m₄, rd₄, wr₄, sp₄⟩ := cntTest_ok s₂
  have ht0 : s₄.gpr t0 = BitVec.ofNat 32 (3 - i) := by
    rw [g₄ _ (by decide), v₂]; exact cnt₁
  have hz₄ : s₄.z = decide (i = 2) := by
    rw [z₄, v₂]
    change (slotW s₁ cntSlot >>> 1 - 0 == 0) = _
    rw [cnt₁]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl <;> decide
  have c₄ : Ctx s₀ s₄ := c₁.step (by rw [rd₄, rd₂]) (by rw [wr₄, wr₂])
    (fun r h1 _ => by rw [g₄ r (fun e => h1 (by rw [e]; decide)), g₂ r (fun e => h1 (by rw [e]; decide))])
    (by rw [m₄, m₂]; exact Frame.refl _ _)
  have hs₄ : ∀ j, slotW s₄ j = slotW s₁ j := fun j => by
    simp only [slotW, m₄, m₂, g₄ sb (by decide), g₂ sb (by decide)]
  have k₄ : s₄.gpr kp = s₁.gpr kp := by rw [g₄ _ (by decide), g₂ _ (by decide)]
  have hk₄ : AtEntry s₄ (s₀.gpr sb) (2 * i + 2) := by rw [AtEntry, k₄]; exact k₁
  have w₄ := w₁.congr fun j _ => hs₄ _
  have kl₄ := kl₁.congr fun j _ => hs₄ _
  have kr₄ := kr₁.congr fun j _ => hs₄ _
  have cnt₄ : slotW s₄ cntSlot = BitVec.ofNat 32 (3 - i) := by rw [hs₄, cnt₁]
  refine WP.seq (WP.of_runBlock ⟨s₄, by
    rw [runBlock_app, e₁, Option.bind_some, show ([ldS t0 cntSlot, .mov t1 (lsrOp t0 1), .cmp t1 (.imm 0)] :
      List Instr) = [.ldr t0 sb (4 * cntSlot)] ++ [.mov t1 (lsrOp t0 1), .cmp t1 (.imm 0)] from rfl,
      runBlock_app, e₂, Option.bind_some, e₃], ?_⟩)
  refine WP.seq (WP.mono (Q := KaMid s₀ KL KR i) ?_ hcont)
  have hka : 2 ≤ i → VW s₄ kaSlot (kaD2 KL KR) := fun h2 =>
    ((keep₁ kaSlot (by decide) (by decide) (by decide) _ (h.ka h2)).congr fun j _ => hs₄ _)
  refine WP.ite (!(decide (i = 2))) ((eval_ne s₄).trans (by rw [hz₄])) (fun hne => ?_) (fun heq => ?_)
  · have hi2 : i ≠ 2 := by simpa using hne
    let s₅ := subFlags s₄ (s₄.gpr t0) 3
    have e₅ : runBlock isa [.cmp t0 (.imm 3)] s₄ = some s₅ := cmpImm_ok s₄ t0 (by decide)
    have hz₅ : s₅.z = decide (i = 0) := by
      rw [subFlags_z, ht0]
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> decide
    have c₅ : Ctx s₀ s₅ := c₄.step rfl rfl (fun _ _ _ => rfl) (Frame.refl _ _)
    have hs₅ : ∀ j, slotW s₅ j = slotW s₄ j := fun _ => rfl
    have w₅ := w₄.congr fun j _ => hs₅ _
    have kl₅ := kl₄.congr fun j _ => hs₅ _
    have kr₅ := kr₄.congr fun j _ => hs₅ _
    refine WP.seq (WP.of_runBlock ⟨s₅, e₅, ?_⟩)
    refine WP.ite (decide (i = 0)) ((eval_eq s₅).trans (by rw [hz₅])) (fun h0 => ?_) (fun h0 => ?_)
    · -- After the first pair: `KL` is XORed in.
      have hi0 : i = 0 := by simpa using h0
      subst hi0
      obtain ⟨s₆, e₆, c₆, k₆, v₆, o₆⟩ := words_ctx hp c₅ (xor_op wSlot klSlot (by decide) (by decide))
        (by decide) (by decide) (by decide) (by decide)
      refine WP.of_runBlock ⟨s₆, e₆, ⟨c₆, by rw [AtEntry, k₆]; exact hk₄, ?_, ?_, ?_, fun h => by omega,
        fun h => by omega, by rw [o₆ _ (by decide) (by decide), hs₅, cnt₄]⟩⟩
      · have := VW_xor (s := s₅) (s' := s₆) (x := klSlot) (w := wSlot) kl₅ w₅ fun k hk => by
          rw [v₆ k hk]
        simpa [kaW, BitVec.xor_comm] using this
      · exact kl₅.congr fun j hj => o₆ _ (by decide +revert) (by decide +revert)
      · exact kr₅.congr fun j hj => o₆ _ (by decide +revert) (by decide +revert)
    · -- After the second: it is `KA`, and `KR` is XORed in.
      have hi1 : i = 1 := by simp at h0; omega
      subst hi1
      obtain ⟨s₆, e₆, c₆, k₆, v₆, o₆⟩ := words_ctx hp c₅ (copy_op kaSlot wSlot (by decide) (by decide))
        (by decide) (by decide) (by decide) (by decide)
      obtain ⟨s₇, e₇, c₇, k₇, v₇, o₇⟩ := words_ctx hp c₆ (xor_op wSlot krSlot (by decide) (by decide))
        (by decide) (by decide) (by decide) (by decide)
      have w₆ : VW s₆ wSlot (kaD2 KL KR) := w₅.congr fun j hj => o₆ _ (by decide +revert) (by decide +revert)
      have kr₆ : VW s₆ krSlot KR := kr₅.congr fun j hj => o₆ _ (by decide +revert) (by decide +revert)
      have ka₆ : VW s₆ kaSlot (kaD2 KL KR) := VW_copy w₅ fun k hk => by rw [v₆ k hk]
      refine WP.of_runBlock ⟨s₇, by
        rw [runBlock_app, show runBlock isa (copyWords kaSlot wSlot) s₅ = some s₆ from e₆, Option.bind_some]
        exact e₇,
        ⟨c₇, by rw [AtEntry, k₇, k₆]; exact hk₄, ?_, ?_, ?_, fun _ => ?_, fun h => by omega, ?_⟩⟩
      · have := VW_xor (s := s₆) (s' := s₇) (x := krSlot) (w := wSlot) kr₆ w₆ fun k hk => by rw [v₇ k hk]
        simpa [kaW, BitVec.xor_comm] using this
      · exact (kl₅.congr fun j hj => o₆ _ (by decide +revert) (by decide +revert)).congr fun j hj =>
          o₇ _ (by decide +revert) (by decide +revert)
      · exact kr₆.congr fun j hj => o₇ _ (by decide +revert) (by decide +revert)
      · exact ka₆.congr fun j hj => o₇ _ (by decide +revert) (by decide +revert)
      · rw [o₇ _ (by decide) (by decide), o₆ _ (by decide) (by decide), hs₅, cnt₄]
  · -- After the third: it is `KB`.
    have hi2 : i = 2 := by simpa using heq
    subst hi2
    obtain ⟨s₆, e₆, c₆, k₆, v₆, o₆⟩ := words_ctx hp c₄ (copy_op kbSlot wSlot (by decide) (by decide))
      (by decide) (by decide) (by decide) (by decide)
    refine WP.of_runBlock ⟨s₆, e₆, ⟨c₆, by rw [AtEntry, k₆]; exact hk₄, ?_, ?_, ?_, fun _ => ?_, fun _ => ?_, ?_⟩⟩
    · exact w₄.congr fun j hj => o₆ _ (by decide +revert) (by decide +revert)
    · exact kl₄.congr fun j hj => o₆ _ (by decide +revert) (by decide +revert)
    · exact kr₄.congr fun j hj => o₆ _ (by decide +revert) (by decide +revert)
    · exact (hka (by decide)).congr fun j hj => o₆ _ (by decide +revert) (by decide +revert)
    · exact VW_copy w₄ fun k hk => by rw [v₆ k hk]
    · rw [o₆ _ (by decide) (by decide), cnt₄]

/-- The count's step: `ldr t0, [sb, #4 cntSlot]; subs t0, t0, #1; str t0, [sb, #4 cntSlot]`. -/
theorem cntStep_ok {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {c : Nat} (hc3 : 1 ≤ c ∧ c ≤ 3) (hcnt : slotW s cntSlot = BitVec.ofNat 32 c) :
    ∃ s', runBlock isa [ldS t0 cntSlot, .subs t0 t0 (.imm 1), stS cntSlot t0] s = some s' ∧ Ctx s₀ s' ∧
      s'.z = decide (c = 1) ∧ s'.gpr kp = s.gpr kp ∧ slotW s' cntSlot = BitVec.ofNat 32 (c - 1) ∧
      (∀ j < slots, j ≠ cntSlot → slotW s' j = slotW s j) := by
  have hs := hc.scr hp
  have hfit := hs.fit
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := ldSlot_ok s t0 sb (k := cntSlot) rfl (by decide) ⟨hs.wr, hfit⟩
  let s₂ := (subFlags s₁ (s₁.gpr t0) 1).setReg t0 (s₁.gpr t0 - 1)
  have e₂ : runBlock isa [.subs t0 t0 (.imm 1)] s₁ = some s₂ := by
    simp only [runBlock_cons, exec, Op2.eval, show encodable 1 = true by decide, ↓reduceIte, Option.map_some,
      runStep_some, runBlock_nil]
    rfl
  have hb₂ : s₂.gpr sb = s.gpr sb := by
    rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), subFlags_gpr, o₁ _ (by decide)]
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃, sp₃, z₃, f₃⟩ := stSlot_ok s₂ t0 sb (k := cntSlot) hb₂ (by decide)
    ⟨by rw [RegUpd.wr_setReg, subFlags_wr, wr₁]; exact hs.wr, hfit⟩
  have ht : s₂.gpr t0 = BitVec.ofNat 32 (c - 1) := by
    rw [RegUpd.gpr_setReg_self, v₁]
    change slotW s cntSlot - 1 = _
    rw [hcnt, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, VG.Offset.ofNat_sub_ofNat (by omega)]
  have hb₃ : s₃.gpr sb = s.gpr sb := by rw [g₃, hb₂]
  have hfit' := hfit
  rw [slots_eq] at hfit'
  refine ⟨s₃, ?_, hc.step (by rw [rd₃, RegUpd.rd_setReg, subFlags_rd, rd₁]) (by rw [wr₃, RegUpd.wr_setReg,
      subFlags_wr, wr₁]) (fun r h1 _ => by
        rw [g₃, RegUpd.gpr_setReg_of_ne _ _ (fun e => h1 (by rw [e]; decide)), subFlags_gpr,
          o₁ r (fun e => h1 (by rw [e]; decide))]) ?_, ?_, by rw [g₃, RegUpd.gpr_setReg_of_ne _ _ (by decide),
      subFlags_gpr, o₁ _ (by decide)], ?_, fun j hj hne => ?_⟩
  · rw [show ([ldS t0 cntSlot, .subs t0 t0 (.imm 1), stS cntSlot t0] : List Instr) =
      [.ldr t0 sb (4 * cntSlot)] ++ ([.subs t0 t0 (.imm 1)] ++ [.str t0 sb (4 * cntSlot)]) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, e₃]
  · have f₃' : Frame [⟨wordAddr (s.gpr sb) cntSlot, 4⟩] s.mem s₃.mem := by rw [← m₁]; exact f₃
    refine f₃'.sub fun r hr => ⟨_, by simp only [ctxRegions, List.mem_cons]; exact .inr (.inl rfl), ?_⟩
    simp only [List.mem_singleton] at hr; subst hr
    rw [hc.base]
    exact fun _ h => h
  · rw [z₃, RegUpd.z_setReg, subFlags_z, v₁]
    change (slotW s cntSlot - 1 == 0) = _
    rw [hcnt, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ofNat32_sub_beq (by omega) (by omega)]
  · rw [slotW, hb₃, m₃, ← hb₂, Mem.readW_writeW_self32, ht]
  · rw [slotW, hb₃, m₃, readW_slot_write hfit _ hj (by decide), ite_eq_right hne,
      RegUpd.mem_setReg, subFlags_mem, m₁]

/-- The loop's start: the running value `KL ⊕ KR`, the count 3. -/
theorem kaStart_ok {s₀ : State} {KL KR : BitVec 64 × BitVec 64} (hp : KeyCtx s₀ 6 sigE)
    (hk : AtEntry s₀ (s₀.gpr sb) 0) (hl : VW s₀ klSlot KL) (hr : VW s₀ krSlot KR) :
    ∃ s, runBlock isa (copyWords wSlot klSlot ++ xorWords wSlot krSlot ++
        ([.mov t0 (.imm 3), stS cntSlot t0] : List Instr)) s₀ =
      some s ∧ KaInv s₀ KL KR 0 s := by
  obtain ⟨s₁, e₁, c₁, k₁, v₁, o₁⟩ := words_ctx hp (Ctx.refl s₀) (copy_op wSlot klSlot (by decide) (by decide))
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨s₂, e₂, c₂, k₂, v₂, o₂⟩ := words_ctx hp c₁ (xor_op wSlot krSlot (by decide) (by decide))
    (by decide) (by decide) (by decide) (by decide)
  have hs₂ := c₂.scr hp
  let s₃ := s₂.setReg t0 (BitVec.ofNat 32 3)
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄, sp₄, -, f₄⟩ := stSlot_ok s₃ t0 sb (b := s₂.gpr sb) (k := cntSlot)
    (RegUpd.gpr_setReg_of_ne _ _ (by decide)) (by decide)
    ⟨by rw [RegUpd.wr_setReg]; exact hs₂.wr, hs₂.fit⟩
  have hfit := hs₂.fit
  have hb₄ : s₄.gpr sb = s₂.gpr sb := by rw [g₄, RegUpd.gpr_setReg_of_ne _ _ (by decide)]
  have hs₄ : ∀ j < slots, j ≠ cntSlot → slotW s₄ j = slotW s₂ j := fun j hj hne => by
    rw [slotW, hb₄, m₄, readW_slot_write hfit _ hj (by decide), ite_eq_right hne]
    rfl
  have kl₁ := hl.congr fun j hj => o₁ _ (by decide +revert) (by decide +revert)
  have kr₁ := hr.congr fun j hj => o₁ _ (by decide +revert) (by decide +revert)
  have w₂ : VW s₂ wSlot (kaW KL KR 0) := by
    have := VW_xor (s := s₁) (s' := s₂) (x := krSlot) (w := wSlot) kr₁ (VW_copy hl fun k hk => by rw [v₁ k hk])
      fun k hk => by rw [v₂ k hk]
    simpa [kaW, BitVec.xor_comm] using this
  refine ⟨s₄, ?_, ⟨by decide, ?_, by rw [AtEntry, g₄, RegUpd.gpr_setReg_of_ne _ _ (by decide), k₂, k₁]; exact hk,
    w₂.congr fun j hj => hs₄ _ (by decide +revert) (by decide +revert),
    (kl₁.congr fun j hj => o₂ _ (by decide +revert) (by decide +revert)).congr fun j hj =>
      hs₄ _ (by decide +revert) (by decide +revert),
    (kr₁.congr fun j hj => o₂ _ (by decide +revert) (by decide +revert)).congr fun j hj =>
      hs₄ _ (by decide +revert) (by decide +revert),
    fun h => by omega, ?_⟩⟩
  · rw [runBlock_app, runBlock_app, show runBlock isa (copyWords wSlot klSlot) s₀ = some s₁ from e₁,
      Option.bind_some, show runBlock isa (xorWords wSlot krSlot) s₁ = some s₂ from e₂, Option.bind_some,
      runBlock_cons, show exec (.mov t0 (.imm 3)) s₂ = some s₃ by
        simp only [exec, Op2.eval, show encodable (3 : BitVec 32) = true by decide, ↓reduceIte, Option.map_some]
        rfl, runStep_some, show ([stS cntSlot t0] : List Instr) = [.str t0 sb (4 * cntSlot)] from rfl, e₄]
  · refine c₂.step (by rw [rd₄]; rfl) (by rw [wr₄]; rfl) (fun r h1 _ => by
      rw [g₄, RegUpd.gpr_setReg_of_ne _ _ (fun e => h1 (by rw [e]; decide))]) ?_
    refine f₄.sub fun r hr => ⟨_, by simp only [ctxRegions, List.mem_cons]; exact .inr (.inl rfl), ?_⟩
    simp only [List.mem_singleton] at hr; subst hr
    rw [c₂.base]
    exact fun _ h => h
  · rw [slotW, hb₄, m₄, Mem.readW_writeW_self32, RegUpd.gpr_setReg_self]

theorem kaKb_wp {s₀ : State} {KL KR : BitVec 64 × BitVec 64} (hp : KeyCtx s₀ 6 sigE)
    (hk : AtEntry s₀ (s₀.gpr sb) 0) (hl : VW s₀ klSlot KL) (hr : VW s₀ krSlot KR) :
    WP isa kaKb s₀ (KaPost s₀ KL KR) := by
  obtain ⟨s₁, e₁, h₁⟩ := kaStart_ok hp hk hl hr
  unfold kaKb
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.loop (M := isa) (fun n s => ∃ i, n = 3 - i ∧ KaInv s₀ KL KR i s) (fun n s hs => ?_) 3 s₁
    ⟨0, rfl, h₁⟩
  obtain ⟨i, rfl, hi⟩ := hs
  refine kaStep_wp hp hi fun s₂ h₂ => ?_
  obtain ⟨s₃, e₃, c₃, z₃, k₃, n₃, o₃⟩ := cntStep_ok hp h₂.ctx (c := 3 - i) (by have := hi.lt; omega) h₂.cnt
  refine WP.of_runBlock ⟨s₃, e₃, ?_⟩
  have keep : ∀ a, a + 4 ≤ cntSlot ∨ cntSlot + 1 ≤ a → a + 4 ≤ slots → ∀ v, VW s₂ a v → VW s₃ a v :=
    fun a ha has v h => h.congr fun j hj => o₃ _ (by omega) (by omega)
  by_cases h2 : i = 2
  · subst h2
    refine .inl ⟨(eval_ne s₃).trans (by rw [z₃]; rfl), ⟨c₃, keep _ (by decide) (by decide) _ h₂.kl,
      keep _ (by decide) (by decide) _ h₂.kr, keep _ (by decide) (by decide) _ (h₂.ka (by decide)),
      keep _ (by decide) (by decide) _ (h₂.kb rfl)⟩⟩
  · have hi3 := hi.lt
    refine .inr ⟨(eval_ne s₃).trans (by rw [z₃]; simp; omega), 3 - (i + 1), by omega, i + 1, rfl,
      ⟨by omega, c₃, by rw [AtEntry, k₃]; exact h₂.kp, keep _ (by decide) (by decide) _ h₂.w,
        keep _ (by decide) (by decide) _ h₂.kl, keep _ (by decide) (by decide) _ h₂.kr,
        fun h => keep _ (by decide) (by decide) _ (h₂.ka (by omega)), by rw [n₃]; congr 1⟩⟩

end VG.Proof.Camellia.Arm
