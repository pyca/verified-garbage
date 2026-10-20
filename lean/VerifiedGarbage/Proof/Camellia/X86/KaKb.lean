module
public import VerifiedGarbage.Proof.Camellia.Common
public import VerifiedGarbage.Proof.Camellia.X86.KeyPair

import VerifiedGarbage.Proof.Camellia.X86.Prologue
import VerifiedGarbage.Proof.Camellia.X86.Fl
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Camellia's key schedule on x86 (32-bit): `KA` and `KB`

As on ARMv7 (`Proof/Camellia/Arm/KaKb.lean`): `kaKb_wp`, from `KL` and `KR`
in their slots and the constants' table, the loop of three pairs of rounds
on the running value (`pairPlain_step`), with the XORs and copies between
them (`wordsOp_ok`), leaves `KA` and `KB` (`kaD2`, `kaD3`) in their slots.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Camellia.X86
open VG.Impl.Aes.X86 (sb tmpRegs slotAt st movS xorS movR movI shrI subI)
open VG.Proof.Camellia (byteOf byteOf_xor pair sigE kaD1 kaD2 kaD3 kaW)

/-! ## Operations on four words -/

/-- An operation on word `k` of the values at `w` and `x`: slot `w + k`
becomes `F` of slots `x + k` and `w + k`. -/
def OpOk (op : Nat → List Instr) (F : BitVec 32 → BitVec 32 → BitVec 32) (w x : Nat) : Prop :=
  ∀ k < 4, ∀ (s : State) (b : BitVec 32), s.gpr sb = b → ScrIn s.wr b →
    ∃ s', runBlock isa (op k) s = some s' ∧
      s'.mem = s.mem.writeW (wordAddr b (w + k))
        (F (s.mem.readW (wordAddr b (x + k)) 32) (s.mem.readW (wordAddr b (w + k)) 32)) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem copy_op (w x : Nat) (hw : w + 4 ≤ slots) (hx : x + 4 ≤ slots) :
    OpOk (fun k => [movS .eax (x + k), st (w + k) .eax]) (fun a _ => a) w x := by
  intro k hk s b hb hs
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, -, -⟩ := ldSlot_ok s .eax .edi (k := x + k) hb (by omega) hs
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂, -, -, -⟩ := stSlot_ok s₁ .eax .edi (b := b) (k := w + k)
    (by rw [o₁ _ (by decide)]; exact hb) (by omega) (by rw [wr₁]; exact hs)
  refine ⟨s₂, ?_, by rw [m₂, v₁, m₁], fun r h0 => by rw [g₂, o₁ r h0], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  show runBlock isa [movS .eax (x + k), st (w + k) .eax] s = _
  rw [show ([movS .eax (x + k), st (w + k) .eax] : List Instr) = [.mov .eax (.mem (slotAt .edi (x + k)))] ++
    [.store (slotAt .edi (w + k)) .eax] from rfl, runBlock_app, e₁, Option.bind_some, e₂]

theorem xor_op (w x : Nat) (hw : w + 4 ≤ slots) (hx : x + 4 ≤ slots) :
    OpOk (fun k => [movS .eax (x + k), xorS .eax (w + k), st (w + k) .eax]) (fun a c => a ^^^ c) w x := by
  intro k hk s b hb hs
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, -, -⟩ := ldSlot_ok s .eax .edi (k := x + k) hb (by omega) hs
  have hb₁ : s₁.gpr sb = b := by rw [o₁ _ (by decide), hb]
  have hin : InRegions (s₁.rd ++ s₁.wr) (wordAddr (s₁.gpr sb) (w + k)) 4 := by
    rw [hb₁, rd₁, wr₁]; exact inRd (hs.slot (by omega))
  let y := s₁.gpr .eax ^^^ slotW s₁ (w + k)
  let s₂ := (arithFlags s₁ y false false).setReg .eax y
  have e₂ : runBlock isa [xorS .eax (w + k)] s₁ = some s₂ := by
    rw [runBlock_cons, show exec (xorS .eax (w + k)) s₁ = some s₂ by
      show (s₁.load32 (wordAddr (s₁.gpr sb) (w + k))).bind _ = _
      simp only [State.load32, hin, ↓reduceIte, Option.bind_some]; rfl, runStep_some, runBlock_nil]
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃, -, -, -⟩ := stSlot_ok s₂ .eax .edi (b := b) (k := w + k)
    (by rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_arithFlags]; exact hb₁) (by omega)
    (by show ScrIn s₁.wr b; rw [wr₁]; exact hs)
  refine ⟨s₃, ?_, ?_, fun r h0 => by
      rw [g₃, RegUpd.gpr_setReg_of_ne _ _ h0, RegUpd.gpr_arithFlags, o₁ r h0],
    by rw [rd₃]; exact rd₁, by rw [wr₃]; exact wr₁⟩
  · show runBlock isa [movS .eax (x + k), xorS .eax (w + k), st (w + k) .eax] s = _
    rw [show ([movS .eax (x + k), xorS .eax (w + k), st (w + k) .eax] : List Instr) =
      [.mov .eax (.mem (slotAt .edi (x + k)))] ++ ([xorS .eax (w + k)] ++ [.store (slotAt .edi (w + k)) .eax])
      from rfl, runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, e₃]
  · rw [m₃, RegUpd.gpr_setReg_self]
    show s₁.mem.writeW _ (s₁.gpr .eax ^^^ s₁.mem.readW (wordAddr (s₁.gpr sb) (w + k)) 32) = _
    rw [m₁, v₁, hb₁]

/-- Four words of an operation. -/
theorem wordsOp_ok {op : Nat → List Instr} {F : BitVec 32 → BitVec 32 → BitVec 32} {w x : Nat}
    (hop : OpOk op F w x) (hsep : x + 4 ≤ w ∨ w + 4 ≤ x) (hw : w + 4 ≤ slots) (hx : x + 4 ≤ slots)
    {b : BitVec 32} :
    ∀ n ≤ 4, ∀ s : State, s.gpr sb = b → ScrIn s.wr b →
      ∃ s', runBlock isa ((List.range n).flatMap op) s = some s' ∧
        (∀ k < n, s'.mem.readW (wordAddr b (w + k)) 32 =
          F (s.mem.readW (wordAddr b (x + k)) 32) (s.mem.readW (wordAddr b (w + k)) 32)) ∧
        (∀ j < slots, j < w ∨ w + n ≤ j → s'.mem.readW (wordAddr b j) 32 = s.mem.readW (wordAddr b j) 32) ∧
        (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        Frame [⟨wordAddr b w, 4 * n⟩] s.mem s'.mem
  | 0, _, s, _, _ => ⟨s, rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ => rfl, fun _ _ => rfl, rfl, rfl,
      Frame.refl _ _⟩
  | n + 1, hn, s, hb, hs => by
    have hfit := hs.fit
    obtain ⟨s₁, e₁, v₁, o₁, g₁, rd₁, wr₁, f₁⟩ := wordsOp_ok hop hsep hw hx n (by omega) s hb hs
    obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := hop n (by omega) s₁ b (by rw [g₁ _ (by decide), hb])
      (by rw [wr₁]; exact hs)
    refine ⟨s₂, by rw [List.range_succ, List.flatMap_append, runBlock_app, e₁, Option.bind_some,
        List.flatMap_singleton]; exact e₂, fun k hk => ?_, fun j hj h => ?_,
      fun r h0 => by rw [g₂ r h0, g₁ r h0], by rw [rd₂, rd₁], by rw [wr₂, wr₁], ?_⟩
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
        rw [slot_addr (by omega), slot_addr (by omega)]
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

theorem kaSlot_eq : kaSlot = 84 := rfl
theorem kbSlot_eq : kbSlot = 88 := rfl
theorem cntSlot_eq : cntSlot = 654 := rfl

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
  obtain ⟨s', e', v', o', g', rd', wr', f'⟩ := wordsOp_ok hop hsep hw hx 4 (Nat.le_refl _) s rfl hs
  have hb : s'.gpr sb = s.gpr sb := g' _ (by decide)
  refine ⟨s', e', hc.step rd' wr' (fun r h1 _ => g' r (fun h => h1 (h ▸ by decide)))
    ?_, g' _ (by decide), fun k hk => by simp only [slotW, hb]; exact v' k hk,
    fun j hj h => by simp only [slotW, hb]; exact o' j hj h⟩
  refine f'.sub fun r hr => ⟨_, by simp only [ctxRegions, List.mem_cons]; exact .inl rfl, ?_⟩
  simp only [List.mem_singleton] at hr; subst hr
  rw [slots_eq] at hfit
  rw [hc.base, slot_addr (by rw [← hc.base]; omega)]
  exact VG.Offset.sub_base _ (by rw [keySlot_eq]; omega)

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

/-- `mov eax, [edi + 4 cntSlot]; mov ebx, eax; shr ebx, 1; cmp ebx, 0`. -/
theorem cntTest_ok {s : State} (hs : ScrIn s.wr (s.gpr sb)) :
    ∃ s', runBlock isa [movS .eax cntSlot, movR .ebx .eax, shrI .ebx 1, .alu .cmp .ebx (.imm 0)] s = some s' ∧
      s'.zf = some (slotW s cntSlot >>> 1 - 0 == 0) ∧ s'.gpr .eax = slotW s cntSlot ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, -, -⟩ := ldSlot_ok s .eax .edi (k := cntSlot) rfl (by decide) hs
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂, -, -⟩ := movR_ok s₁ .ebx .eax
  let a := s₂.gpr .ebx
  let r := a >>> 1
  let s₃ := (s₂.setFlags (some (a.getLsbD (1 - 1))) (if 1 = 1 then some a.msb else none) (some (r == 0))
    (some r.msb)).setReg .ebx r
  have e₃ : runBlock isa [shrI .ebx 1] s₂ = some s₃ := rfl
  let s₄ := arithFlags s₃ (s₃.gpr .ebx - 0) ((s₃.gpr .ebx).toNat < (0 : BitVec 32).toNat)
    (subOverflow (s₃.gpr .ebx) 0 (s₃.gpr .ebx - 0))
  have e₄ : runBlock isa [.alu .cmp .ebx (.imm 0)] s₃ = some s₄ := rfl
  have hr : s₃.gpr .ebx = slotW s cntSlot >>> 1 := by
    rw [RegUpd.gpr_setReg_self]; show s₂.gpr .ebx >>> 1 = _; rw [r₂, v₁]; rfl
  have hm : s₄.mem = s.mem := by rw [RegUpd.mem_arithFlags]; show s₂.mem = _; rw [m₂, m₁]
  have hrd : s₄.rd = s.rd := by rw [RegUpd.rd_arithFlags]; show s₂.rd = _; rw [rd₂, rd₁]
  have hwr : s₄.wr = s.wr := by rw [RegUpd.wr_arithFlags]; show s₂.wr = _; rw [wr₂, wr₁]
  refine ⟨s₄, ?_, by rw [RegUpd.zf_arithFlags, hr], ?_, fun r h1 h2 => ?_, hm, hrd, hwr⟩
  · rw [show ([movS .eax cntSlot, movR .ebx .eax, shrI .ebx 1, .alu .cmp .ebx (.imm 0)] : List Instr) =
      [.mov .eax (.mem (slotAt .edi cntSlot))] ++ ([movR .ebx .eax] ++ ([shrI .ebx 1] ++
        [.alu .cmp .ebx (.imm 0)])) from rfl, runBlock_app, e₁, Option.bind_some, runBlock_app, e₂,
      Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄]
  · rw [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ (by decide)]
    show s₂.gpr .eax = _; rw [o₂ _ (by decide), v₁]; rfl
  · rw [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ h2]
    show s₂.gpr r = _; rw [o₂ r h2, o₁ r h1]

/-- `cmp eax, v`. -/
theorem cmpEax_ok (s : State) (v : BitVec 32) :
    ∃ s', runBlock isa [.alu .cmp .eax (.imm v)] s = some s' ∧ s'.zf = some (s.gpr .eax - v == 0) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem kaStep_wp {s₀ : State} {KL KR : BitVec 64 × BitVec 64} (hp : KeyCtx s₀ 6 sigE) {i : Nat} {s : State}
    (h : KaInv s₀ KL KR i s) {c : Prog isa} {Q : State → Prop} (hcont : ∀ s', KaMid s₀ KL KR i s' → WP isa c s' Q) :
    WP isa (.seq (.block (pairPlain ++ [movS .eax cntSlot, movR .ebx .eax, shrI .ebx 1, .alu .cmp .ebx (.imm 0)]))
      (.seq (.ite .ne
          (.seq (.block [.alu .cmp .eax (.imm 3)])
            (.ite .e (.block (xorWords wSlot klSlot))
              (.block (copyWords kaSlot wSlot ++ xorWords wSlot krSlot))))
          (.block (copyWords kbSlot wSlot))) c)) s Q := by
  have hi := h.lt
  obtain ⟨s₁, e₁, c₁, k₁, w₁, o₁⟩ := pairPlain_step hp h.ctx h.kp (by omega) (by omega) h.w
  rw [pair_kaW KL KR hi] at w₁
  have hs₁ := c₁.scr hp
  have keep₁ : ∀ a, tailSlot ≤ a → a + 4 ≤ wSlot ∨ wSlot + 4 ≤ a → a + 4 ≤ slots →
      ∀ v, VW s a v → VW s₁ a v := fun a h1 ha has v hv =>
    hv.congr fun j hj => o₁ _ (by omega) (by omega) (by omega)
  have kl₁ := keep₁ klSlot (by decide) (by decide) (by decide) _ h.kl
  have kr₁ := keep₁ krSlot (by decide) (by decide) (by decide) _ h.kr
  have cnt₁ : slotW s₁ cntSlot = BitVec.ofNat 32 (3 - i) := by
    rw [o₁ _ (by decide) (by decide) (by decide), h.cnt]
  -- The count's tests.
  obtain ⟨s₄, e₄, z₄, a₄, g₄, m₄, rd₄, wr₄⟩ := cntTest_ok hs₁
  have ht0 : s₄.gpr .eax = BitVec.ofNat 32 (3 - i) := by rw [a₄, cnt₁]
  have hz₄ : s₄.zf = some (decide (i = 2)) := by
    rw [z₄, cnt₁]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl <;> decide
  have c₄ : Ctx s₀ s₄ := c₁.step rd₄ wr₄
    (fun r h1 _ => g₄ r (fun e => h1 (by rw [e]; decide)) (fun e => h1 (by rw [e]; decide)))
    (by rw [m₄]; exact Frame.refl _ _)
  have hs₄ : ∀ j, slotW s₄ j = slotW s₁ j := fun j => by
    simp only [slotW, m₄, g₄ sb (by decide) (by decide)]
  have k₄ : s₄.gpr kp = s₁.gpr kp := g₄ _ (by decide) (by decide)
  have hk₄ : AtEntry s₄ (s₀.gpr sb) (2 * i + 2) := by rw [AtEntry, k₄]; exact k₁
  have w₄ := w₁.congr fun j _ => hs₄ _
  have kl₄ := kl₁.congr fun j _ => hs₄ _
  have kr₄ := kr₁.congr fun j _ => hs₄ _
  have cnt₄ : slotW s₄ cntSlot = BitVec.ofNat 32 (3 - i) := by rw [hs₄, cnt₁]
  refine WP.seq (WP.of_runBlock ⟨s₄, by rw [runBlock_app, e₁, Option.bind_some, e₄], ?_⟩)
  refine WP.seq (WP.mono (Q := KaMid s₀ KL KR i) ?_ hcont)
  have hka : 2 ≤ i → VW s₄ kaSlot (kaD2 KL KR) := fun h2 =>
    ((keep₁ kaSlot (by decide) (by decide) (by decide) _ (h.ka h2)).congr fun j _ => hs₄ _)
  refine WP.ite (!(decide (i = 2))) ((eval_ne s₄).trans (by rw [hz₄]; rfl)) (fun hne => ?_) (fun heq => ?_)
  · have hi2 : i ≠ 2 := by simpa using hne
    obtain ⟨s₅, e₅, z₅, g₅, m₅, rd₅, wr₅⟩ := cmpEax_ok s₄ 3
    have hz₅ : s₅.zf = some (decide (i = 0)) := by
      rw [z₅, ht0]
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> decide
    have c₅ : Ctx s₀ s₅ := c₄.step rd₅ wr₅ (fun r _ _ => by rw [g₅]) (by rw [m₅]; exact Frame.refl _ _)
    have hs₅ : ∀ j, slotW s₅ j = slotW s₄ j := fun j => by simp only [slotW, m₅, g₅]
    have hk₅ : AtEntry s₅ (s₀.gpr sb) (2 * i + 2) := by rw [AtEntry, g₅]; exact hk₄
    have w₅ := w₄.congr fun j _ => hs₅ _
    have kl₅ := kl₄.congr fun j _ => hs₅ _
    have kr₅ := kr₄.congr fun j _ => hs₅ _
    have cnt₅ : slotW s₅ cntSlot = BitVec.ofNat 32 (3 - i) := by rw [hs₅, cnt₄]
    refine WP.seq (WP.of_runBlock ⟨s₅, e₅, ?_⟩)
    refine WP.ite (decide (i = 0)) ((eval_e s₅).trans hz₅) (fun h0 => ?_) (fun h0 => ?_)
    · -- After the first pair: `KL` is XORed in.
      have hi0 : i = 0 := by simpa using h0
      subst hi0
      obtain ⟨s₆, e₆, c₆, k₆, v₆, o₆⟩ := words_ctx hp c₅ (xor_op wSlot klSlot (by decide) (by decide))
        (by decide) (by decide) (by decide) (by decide)
      refine WP.of_runBlock ⟨s₆, e₆, ⟨c₆, by rw [AtEntry, k₆]; exact hk₅, ?_, ?_, ?_, fun h => by omega,
        fun h => by omega, by rw [o₆ _ (by decide) (by decide), cnt₅]⟩⟩
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
        ⟨c₇, by rw [AtEntry, k₇, k₆]; exact hk₅, ?_, ?_, ?_, fun _ => ?_, fun h => by omega, ?_⟩⟩
      · have := VW_xor (s := s₆) (s' := s₇) (x := krSlot) (w := wSlot) kr₆ w₆ fun k hk => by rw [v₇ k hk]
        simpa [kaW, BitVec.xor_comm] using this
      · exact (kl₅.congr fun j hj => o₆ _ (by decide +revert) (by decide +revert)).congr fun j hj =>
          o₇ _ (by decide +revert) (by decide +revert)
      · exact kr₆.congr fun j hj => o₇ _ (by decide +revert) (by decide +revert)
      · exact ka₆.congr fun j hj => o₇ _ (by decide +revert) (by decide +revert)
      · rw [o₇ _ (by decide) (by decide), o₆ _ (by decide) (by decide), cnt₅]
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

/-- The count's step: `mov eax, [edi + 4 cntSlot]; sub eax, 1; mov [edi + 4 cntSlot], eax`. -/
theorem cntStep_ok {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {c : Nat} (hc3 : 1 ≤ c ∧ c ≤ 3) (hcnt : slotW s cntSlot = BitVec.ofNat 32 c) :
    ∃ s', runBlock isa [movS .eax cntSlot, subI .eax 1, st cntSlot .eax] s = some s' ∧ Ctx s₀ s' ∧
      s'.zf = some (decide (c = 1)) ∧ s'.gpr kp = s.gpr kp ∧ slotW s' cntSlot = BitVec.ofNat 32 (c - 1) ∧
      (∀ j < slots, j ≠ cntSlot → slotW s' j = slotW s j) := by
  have hs := hc.scr hp
  have hfit := hs.fit
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, -, -⟩ := ldSlot_ok s .eax .edi (k := cntSlot) rfl (by decide) hs
  obtain ⟨s₂, e₂, r₂, z₂, o₂, m₂, rd₂, wr₂⟩ := subI_ok s₁ .eax 1
  have hb₂ : s₂.gpr sb = s.gpr sb := by rw [o₂ _ (by decide), o₁ _ (by decide)]
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃, z₃, -, f₃⟩ := stSlot_ok s₂ .eax .edi (b := s.gpr sb) (k := cntSlot) hb₂
    (by decide) (by rw [wr₂, wr₁]; exact hs)
  have ht : s₂.gpr .eax = BitVec.ofNat 32 (c - 1) := by
    rw [r₂, v₁]
    change slotW s cntSlot - 1 = _
    rw [hcnt, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, VG.Offset.ofNat_sub_ofNat (by omega)]
  have hb₃ : s₃.gpr sb = s.gpr sb := by rw [g₃, hb₂]
  refine ⟨s₃, ?_, hc.step (by rw [rd₃, rd₂, rd₁]) (by rw [wr₃, wr₂, wr₁]) (fun r h1 _ => by
        rw [g₃, o₂ r (fun e => h1 (by rw [e]; decide)), o₁ r (fun e => h1 (by rw [e]; decide))]) ?_, ?_,
    by rw [g₃, o₂ _ (by decide), o₁ _ (by decide)], ?_, fun j hj hne => ?_⟩
  · rw [show ([movS .eax cntSlot, subI .eax 1, st cntSlot .eax] : List Instr) =
      [.mov .eax (.mem (slotAt .edi cntSlot))] ++ ([subI .eax 1] ++ [.store (slotAt .edi cntSlot) .eax]) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, e₃]
  · have f₃' : Frame [⟨wordAddr (s.gpr sb) cntSlot, 4⟩] s.mem s₃.mem := by rw [← m₁, ← m₂]; exact f₃
    refine f₃'.sub fun r hr => ⟨_, by simp only [ctxRegions, List.mem_cons]; exact .inr (.inl rfl), ?_⟩
    simp only [List.mem_singleton] at hr; subst hr
    rw [hc.base]
    exact fun _ h => h
  · rw [z₃, z₂, v₁]
    change some (slotW s cntSlot - 1 == 0) = _
    rw [hcnt, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ofNat32_sub_beq (by omega) (by omega)]
  · rw [slotW, hb₃, m₃, Mem.readW_writeW_self32, ht]
  · rw [slotW, hb₃, m₃, readW_slot_write hfit _ hj (by decide), ite_eq_right hne, m₂, m₁]

/-- The loop's start: the running value `KL ⊕ KR`, the count 3. -/
theorem kaStart_ok {s₀ : State} {KL KR : BitVec 64 × BitVec 64} (hp : KeyCtx s₀ 6 sigE)
    (hk : AtEntry s₀ (s₀.gpr sb) 0) (hl : VW s₀ klSlot KL) (hr : VW s₀ krSlot KR) :
    ∃ s, runBlock isa (copyWords wSlot klSlot ++ xorWords wSlot krSlot ++
        ([movI .eax 3, st cntSlot .eax] : List Instr)) s₀ = some s ∧ KaInv s₀ KL KR 0 s := by
  obtain ⟨s₁, e₁, c₁, k₁, v₁, o₁⟩ := words_ctx hp (Ctx.refl s₀) (copy_op wSlot klSlot (by decide) (by decide))
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨s₂, e₂, c₂, k₂, v₂, o₂⟩ := words_ctx hp c₁ (xor_op wSlot krSlot (by decide) (by decide))
    (by decide) (by decide) (by decide) (by decide)
  have hs₂ := c₂.scr hp
  obtain ⟨s₃, e₃, v₃, o₃, m₃, rd₃, wr₃⟩ := movI_ok s₂ .eax 3
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄, -, -, f₄⟩ := stSlot_ok s₃ .eax .edi (b := s₂.gpr sb) (k := cntSlot)
    (o₃ _ (by decide)) (by decide) (by rw [wr₃]; exact hs₂)
  have hfit := hs₂.fit
  have hb₄ : s₄.gpr sb = s₂.gpr sb := by rw [g₄, o₃ _ (by decide)]
  have hs₄ : ∀ j < slots, j ≠ cntSlot → slotW s₄ j = slotW s₂ j := fun j hj hne => by
    rw [slotW, hb₄, m₄, readW_slot_write hfit _ hj (by decide), ite_eq_right hne, m₃]
  have kl₁ := hl.congr fun j hj => o₁ _ (by decide +revert) (by decide +revert)
  have kr₁ := hr.congr fun j hj => o₁ _ (by decide +revert) (by decide +revert)
  have w₂ : VW s₂ wSlot (kaW KL KR 0) := by
    have := VW_xor (s := s₁) (s' := s₂) (x := krSlot) (w := wSlot) kr₁ (VW_copy hl fun k hk => by rw [v₁ k hk])
      fun k hk => by rw [v₂ k hk]
    simpa [kaW, BitVec.xor_comm] using this
  have kp₄ : AtEntry s₄ (s₀.gpr sb) 0 := by
    show s₄.gpr kp = _
    rw [g₄, o₃ _ (by decide), k₂, k₁]; exact hk
  refine ⟨s₄, ?_, ⟨by decide, ?_, kp₄,
    w₂.congr fun j hj => hs₄ _ (by decide +revert) (by decide +revert),
    (kl₁.congr fun j hj => o₂ _ (by decide +revert) (by decide +revert)).congr fun j hj =>
      hs₄ _ (by decide +revert) (by decide +revert),
    (kr₁.congr fun j hj => o₂ _ (by decide +revert) (by decide +revert)).congr fun j hj =>
      hs₄ _ (by decide +revert) (by decide +revert),
    fun h => by omega, ?_⟩⟩
  · rw [runBlock_app, runBlock_app, show runBlock isa (copyWords wSlot klSlot) s₀ = some s₁ from e₁,
      Option.bind_some, show runBlock isa (xorWords wSlot krSlot) s₁ = some s₂ from e₂, Option.bind_some,
      show ([movI .eax 3, st cntSlot .eax] : List Instr) = [movI .eax 3] ++ [.store (slotAt .edi cntSlot) .eax]
        from rfl, runBlock_app, e₃, Option.bind_some, e₄]
  · refine c₂.step (by rw [rd₄, rd₃]) (by rw [wr₄, wr₃]) (fun r h1 _ => by
      rw [g₄, o₃ r (fun e => h1 (by rw [e]; decide))]) ?_
    rw [← m₃]
    refine f₄.sub fun r hr => ⟨_, by simp only [ctxRegions, List.mem_cons]; exact .inr (.inl rfl), ?_⟩
    simp only [List.mem_singleton] at hr; subst hr
    rw [c₂.base]
    exact fun _ h => h
  · rw [slotW, hb₄, m₄, Mem.readW_writeW_self32, v₃]; rfl

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

end VG.Proof.Camellia.X86
