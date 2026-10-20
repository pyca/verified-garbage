module

public import VerifiedGarbage.Proof.Camellia.X86.Core
public import VerifiedGarbage.Proof.Camellia.Layout32
import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# The head and tail of eight blocks of bitsliced Camellia on x86 (32-bit)

As on ARMv7 (`Proof/Camellia/Arm/Crypt8.lean`): `head` bitslices both
halves of the eight blocks in the tail buffer and whitens them, and `tail`
whitens, transposes and stores them back; between them the groups of
rounds (`group_wp`) run in a loop. `crypt8_ok` composes them: each block
becomes `cryptWords g E` of it.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Camellia.X86
open VG.Bitslice (lanes bitOf xorBits bitOf_word xorBits_cons xorBits_nil)
open VG.Impl.Aes.X86 (sb tmpRegs movR addI)
open VG.Proof.Camellia (pair group groups cryptWords groupsN groupsN_succ)

/-! ## The tail buffer -/

/-- Word `t` of the tail buffer. -/
abbrev dataW (s : State) (t : Nat) : BitVec 32 := slotW s (tailSlot + t)

/-- Block `b` in the tail buffer. -/
abbrev blk (s : State) (b : Nat) : Spec.Camellia.Block :=
  Spec.Camellia.blockAt s.mem ((s.gpr sb).setWidth 64 + BitVec.ofNat 64 (4 * tailSlot + 16 * b))

theorem dataW_byte (s : State) (hfit : (s.gpr sb).toNat + 4 * slots ≤ 2 ^ 32) {b c j : Nat} (hb : b < 8)
    (hc : c < 16) (hj : j < 8) :
    (dataW s (4 * b + c / 4)).getLsbD (8 * (c % 4) + j) =
      (s.mem ((s.gpr sb).setWidth 64 + BitVec.ofNat 64 (4 * tailSlot + 16 * b) + BitVec.ofNat 64 c)).getLsbD j := by
  rw [slots_eq] at hfit
  rw [dataW, slotW, slot_addr (by rw [tailSlot_eq]; omega), W32.readW32_bit _ _ (by omega) hj,
    VG.Offset.add_add, VG.Offset.add_add,
    show 4 * (tailSlot + (4 * b + c / 4)) + c % 4 = 4 * tailSlot + 16 * b + c by omega]

theorem data_words (s : State) (hfit : (s.gpr sb).toNat + 4 * slots ≤ 2 ^ 32) :
    W32.BlockWords (dataW s) (blk s) := fun b hb c hc j hj => by
  rw [dataW_byte s hfit hb hc hj]
  simp [Spec.Camellia.blockAt]

theorem blk_of_words {s : State} (hfit : (s.gpr sb).toNat + 4 * slots ≤ 2 ^ 32) {B : Nat → Spec.Camellia.Block}
    (h : W32.BlockWords (dataW s) B) {b : Nat} (hb : b < 8) : blk s b = B b := by
  apply Vector.ext
  intro c hc
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [← h b hb c hc j hj, dataW_byte s hfit hb hc hj]
  simp [Spec.Camellia.blockAt]

/-! ## The transposes -/

theorem ok_bs {s : State} (hs : ScrIn s.wr (s.gpr sb)) : Ok bsCfg s where
  slotIn k hk := hs.slot (by simp only [bsCfg, keySlot_eq] at hk; rw [slots_eq]; omega)
  extIn j hj := by simp [bsCfg] at hj
  fit := by have := hs.fit; simp only [bsCfg]; rw [slots_eq] at this; rw [keySlot_eq]; omega
  sep k _ j hj := by simp [bsCfg] at hj

/-- A step that writes only the slots below the table. -/
theorem Ctx.stepB {s₀ s s' : State} (hc : Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hk : ∀ r, r ∉ tmpRegs → r ≠ kp → s'.gpr r = s.gpr r)
    (hf : Frame [slotRegion bsCfg s] s.mem s'.mem) : Ctx s₀ s' :=
  hc.step hrd hwr hk (hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self .., by simp only [slotRegion, bsCfg, hc.base]; exact Region.sub_prefix (by omega)⟩)

/-- A frame of the slots below the table keeps the slots from the table on. -/
theorem slot_above_bs {s s' : State} (hfit : (s.gpr sb).toNat + 4 * slots ≤ 2 ^ 32)
    (hb : s'.gpr sb = s.gpr sb) (hf : Frame [slotRegion bsCfg s] s.mem s'.mem) {k : Nat}
    (h1 : keySlot ≤ k) (h2 : k < slots) : slotW s' k = slotW s k := by
  simp only [slotW, hb]
  exact slot_above (n := keySlot) (by simpa [slotRegion, bsCfg] using hf) h1
    (by rw [slots_eq] at hfit h2; omega)

theorem toBs_all : ([Reg.esp, .esi, .edi].all fun r =>
    ((List.range 4).flatMap toBsWord).all fun i => i.dst != some r) = true := by decide +kernel

theorem fromBs_all : ([Reg.esp, .esi, .edi].all fun r =>
    ((List.range 4).flatMap fromBsWord).all fun i => i.dst != some r) = true := by decide +kernel

theorem keep_of_all {is : List Instr} (h : ([Reg.esp, .esi, .edi].all fun r => is.all fun i => i.dst != some r) = true)
    {r : Reg} (hr : r ∉ tmpRegs) : (is.all fun i => i.dst != some r) = true :=
  List.all_eq_true.mp h r (not_tmp r hr)

/-- `toBs`: the planes of the halves, from the words of the blocks. -/
theorem toBs_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s) :
    ∃ s', runBlock isa ((List.range 4).flatMap toBsWord) s = some s' ∧ Ctx s₀ s' ∧
      s'.gpr kp = s.gpr kp ∧
      (∀ w < 4, ∀ j < 8, ∀ p < 32, (slotW s' (d1Slot + (8 * w + j))).getLsbD p =
        (dataW s (4 * (p % 8) + w)).getLsbD (8 * (p / 8) + j)) ∧
      (∀ k, keySlot ≤ k → k < slots → slotW s' k = slotW s k) := by
  have hs := hc.scr hp
  obtain ⟨s', h', so', rd', wr', o', f'⟩ := linear_ok toBs_check (ok_bs hs) (dataW s)
    (fun j i hji hj => by
      simp only [tailIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      obtain ⟨k, hk, rfl, rfl⟩ := hji
      exact ⟨by omega, rfl⟩)
    (fun j hj => by simp [bsCfg] at hj)
  have hkeep : ∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r := fun r hr => o' r (keep_of_all toBs_all hr)
  refine ⟨s', h', hc.stepB rd' wr' (fun r h1 _ => hkeep r h1) f', hkeep _ (by decide),
    fun w hw j hj p hp => ?_, fun k h1 h2 => slot_above_bs hs.fit (hkeep _ (by decide)) f' h1 h2⟩
  have := so' (d1Slot + (8 * w + j)) (toBsG w j)
    (by
      simp only [toBsOuts, List.mem_map, List.mem_range, Prod.mk.injEq]
      exact ⟨8 * w + j, by omega, rfl, by rw [show (8 * w + j) / 8 = w by omega, show (8 * w + j) % 8 = j by omega]⟩)
    p hp
  simp only [bsCfg] at this
  rw [slotW, hkeep _ (by decide), this, toBsG, xorBits_cons, xorBits_nil, Bool.xor_false, Nat.add_assoc,
    bitOf_word _ _ _ (by omega)]

/-- `fromBs`: the words of the blocks, from the planes of the halves. -/
theorem fromBs_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s) :
    ∃ s', runBlock isa ((List.range 4).flatMap fromBsWord) s = some s' ∧ Ctx s₀ s' ∧
      (∀ b < 8, ∀ w < 4, ∀ i < 4, ∀ j < 8, (dataW s' (4 * b + w)).getLsbD (8 * i + j) =
        (slotW s (d1Slot + (8 * ((w + 2) % 4) + j))).getLsbD (8 * i + b)) := by
  have hs := hc.scr hp
  obtain ⟨s', h', so', rd', wr', o', f'⟩ := linear_ok fromBs_check (ok_bs hs) (fun i => slotW s (d1Slot + i))
    (fun j i hji hj => by
      obtain ⟨k, hk, rfl, rfl⟩ := halvesIns_mem hji
      exact ⟨by omega, by rw [Nat.zero_add]; rfl⟩)
    (fun j hj => by simp [bsCfg] at hj)
  have hkeep : ∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r := fun r hr => o' r (keep_of_all fromBs_all hr)
  refine ⟨s', h', hc.stepB rd' wr' (fun r h1 _ => hkeep r h1) f', fun b hb w hw i hi j hj => ?_⟩
  have := so' (tailSlot + (4 * b + w)) (fromBsG (4 * b + w))
    (by simp only [fromBsOuts, List.mem_map, List.mem_range]; exact ⟨4 * b + w, by omega, rfl⟩)
    (8 * i + j) (by omega)
  simp only [bsCfg] at this
  rw [dataW, slotW, hkeep _ (by decide), this, fromBsG, xorBits_cons, xorBits_nil, Bool.xor_false,
    show (4 * b + w) % 4 = w by omega, show (8 * i + j) % 8 = j by omega, show (8 * i + j) / 8 = i by omega,
    show (4 * b + w) / 4 = b by omega, Nat.add_assoc, bitOf_word _ _ _ (by omega)]

/-! ## The whitening -/

theorem whiten_all (swap : Bool) :
    ([Reg.esp, .esi, .edi].all fun r => (whiten swap).all fun i => i.dst != some r) = true := by
  cases swap <;> decide +kernel

/-- The whitening, with the two entries at `kp`. -/
theorem whiten_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm34 : m + 2 ≤ 34) (swap : Bool)
    (hchk : check (lanes 32 11) layerCfg (linExt 32) (whiten swap) (linEnv (halvesIns 0))
      (linPost tailSlot 11 (whitenOuts swap)) = true) :
    ∃ s', runBlock isa (whiten swap) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      (∀ i < 32, ∀ p < 32, (slotW s' (d1Slot + i)).getLsbD p =
        ((slotW s (d1Slot + i)).getLsbD p ^^ (keyW s (if swap then (i + 16) % 32 else i)).getLsbD p)) ∧
      (∀ k, tailSlot ≤ k → k < slots → slotW s' k = slotW s k) := by
  have hok := hc.ok hp hk hm34
  let W : Nat → BitVec 32 := fun i => if i < 32 then slotW s (d1Slot + i) else keyW s (i - 32)
  obtain ⟨s', h', so', rd', wr', o', f'⟩ := linear_ok hchk hok W
    (fun j i hji hj => by
      obtain ⟨k, hk', rfl, rfl⟩ := halvesIns_mem hji
      exact ⟨by omega, by simp [W, hk']; rfl⟩)
    (fun j hj => by
      simp only [layerCfg] at hj
      exact ⟨by omega, by simp [W, show ¬ 32 + j < 32 by omega]; rfl⟩)
  have hkeep : ∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r := fun r hr => o' r (keep_of_all (whiten_all swap) hr)
  have hfit : (s.gpr sb).toNat + 4 * slots ≤ 2 ^ 32 := by rw [hc.base]; exact hp.scr.fit
  refine ⟨s', h', hc.stepL rd' wr' (fun r h1 _ => hkeep r h1) f', hkeep _ (by decide),
    fun i hi p hp => ?_, fun k h1 h2 => slot_above_frame hfit (hkeep _ (by decide)) f' h1 h2⟩
  have := so' (d1Slot + i) (whitenG swap i)
    (by simp only [whitenOuts, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩) p hp
  simp only [layerCfg] at this
  have hki : (if swap then (i + 16) % 32 else i) < 32 := by split <;> omega
  rw [slotW, hkeep _ (by decide), this, whitenG, xorBits_cons, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ hp, bitOf_word _ _ _ hp]
  simp only [W, hi, ↓reduceIte, show ¬ 32 + (if swap then (i + 16) % 32 else i) < 32 by omega,
    show 32 + (if swap then (i + 16) % 32 else i) - 32 = (if swap then (i + 16) % 32 else i) by omega]

/-! ## The head -/

/-- The halves of the eight blocks after the prewhitening. -/
def headHalves (s : State) (E : Nat → BitVec 64) (b : Nat) : BitVec 64 × BitVec 64 :=
  (W32.hiOf (blk s b) ^^^ E 0, W32.loOf (blk s b) ^^^ E 1)

/-- `kp := ` the address of slot `k`. -/
theorem kpAt_ok (s : State) (k : Nat) :
    ∃ s', runBlock isa (kpAt k) s = some s' ∧ s'.gpr kp = s.gpr sb + BitVec.ofNat 32 (4 * k) ∧
      (∀ r, r ≠ kp → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁, -, -⟩ := movR_ok s kp .edi
  obtain ⟨s₂, e₂, r₂, -, o₂, m₂, rd₂, wr₂⟩ := addI_ok s₁ kp (BitVec.ofNat 32 (4 * k))
  refine ⟨s₂, ?_, by rw [r₂, r₁]; rfl, fun r h => by rw [o₂ r h, o₁ r h], m₂.trans m₁, rd₂.trans rd₁,
    wr₂.trans wr₁⟩
  rw [kpAt, show ([movR kp .edi, addI kp (BitVec.ofNat 32 (4 * k))] : List Instr) =
    [movR kp .edi] ++ [addI kp (BitVec.ofNat 32 (4 * k))] from rfl, runBlock_app, e₁, Option.bind_some, e₂]

theorem head_ok {s₀ : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) :
    ∃ s', runBlock isa head s₀ = some s' ∧ Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) 2 ∧
      Halves s' (headHalves s₀ E) := by
  have hg : 8 * g + 2 ≤ 34 := hp.nk34
  have hfit := hp.scr.fit
  let b := s₀.gpr sb
  -- The transposes.
  obtain ⟨s₂, e₂, c₂, -, x₂, a₂⟩ := toBs_step hp.toKeyCtx (Ctx.refl s₀)
  obtain ⟨hD1, hD2⟩ := W32.halves_of_words (Q := fun k => slotW s₂ (d1Slot + k))
    (fun w hw j hj p hp => x₂ w hw j hj p hp) (data_words s₀ hfit)
  -- `kp := ` the table, and the whitening.
  obtain ⟨s₃, e₃, kp₃, o₃, m₃, rd₃, wr₃⟩ := kpAt_ok s₂ keySlot
  have c₃ : Ctx s₀ s₃ := c₂.regs (fun r h _ => o₃ r h) m₃ rd₃ wr₃
  have k₃ : AtEntry s₃ b 0 := by
    rw [AtEntry, kp₃, c₂.base, Nat.mul_zero, Nat.add_zero]
  have hs₃ : ∀ k, slotW s₃ k = slotW s₂ k := fun k => by simp only [slotW, m₃, o₃ sb (by decide)]
  obtain ⟨s₄, e₄, c₄, kp₄, w₄, -⟩ := whiten_step hp.toKeyCtx c₃ k₃ (by omega) false whiten0_check
  have hK0 := c₃.keyRel hp.toKeyCtx k₃ (e := 0) (by omega)
  have hK1 := c₃.keyRel hp.toKeyCtx k₃ (e := 1) (by omega)
  simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one] at hK0 hK1
  -- `kp += 128`.
  obtain ⟨s₅, e₅, kp₅, -, o₅, m₅, rd₅, wr₅⟩ := addI_ok s₄ kp 128
  have hs₅ : ∀ k, slotW s₅ k = slotW s₄ k := fun k => by simp only [slotW, m₅, o₅ sb (by decide)]
  refine ⟨s₅, ?_, c₄.regs (fun r h _ => o₅ r h) m₅ rd₅ wr₅, k₃.add (n := 2) (by rw [kp₅, kp₄]; rfl), ⟨?_, ?_⟩⟩
  · rw [head, runBlock_app, runBlock_app, runBlock_app, e₂, Option.bind_some, e₃, Option.bind_some,
      e₄, Option.bind_some, e₅]
  · refine (W32.HalfRel.xor hD1 hK0 fun i hi p hp => ?_).congr_right fun _ _ => rfl
    show (slotW s₅ (d1Slot + i)).getLsbD p = _
    rw [hs₅, w₄ i (by omega) p hp, hs₃]
    simp
  · refine (W32.HalfRel.xor hD2 hK1 fun i hi p hp => ?_).congr_right fun _ _ => rfl
    show (slotW s₅ (d2Slot + i)).getLsbD p = _
    rw [hs₅, show d2Slot + i = d1Slot + (16 + i) by rw [d1Slot_eq, d2Slot_eq]; omega,
      w₄ (16 + i) (by omega) p hp, hs₃]
    simp

/-! ## The tail -/

theorem tail_ok {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    (hk : AtEntry s (s₀.gpr sb) (8 * g)) {S : Nat → BitVec 64 × BitVec 64} (hS : Halves s S) :
    ∃ s', runBlock isa tail s = some s' ∧ Ctx s₀ s' ∧
      W32.BlockWords (dataW s')
        (fun b => Spec.Camellia.encodeBlock (((S b).2 ^^^ E (8 * g)) ++ ((S b).1 ^^^ E (8 * g + 1)))) := by
  have hg : 8 * g + 2 ≤ 34 := hp.nk34
  obtain ⟨h1, h2⟩ := hS
  have hK0 := hc.keyRel hp.toKeyCtx hk (e := 0) (by omega)
  have hK1 := hc.keyRel hp.toKeyCtx hk (e := 1) (by omega)
  simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one, Nat.add_zero] at hK0 hK1
  obtain ⟨s₁, e₁, c₁, -, w₁, -⟩ := whiten_step hp.toKeyCtx hc hk (by omega) true whiten1_check
  obtain ⟨s₃, e₃, c₃, x₃⟩ := fromBs_step hp.toKeyCtx c₁
  refine ⟨s₃, ?_, c₃, W32.block_of_planes (Q := fun k => slotW s₁ (d1Slot + (k + 16) % 32))
    (fun b hb w hw i hi j hj => ?_) ?_ ?_⟩
  · rw [tail, runBlock_app, e₁, Option.bind_some, e₃]
  · rw [x₃ b hb w hw i hi j hj]
    congr 3; omega
  · refine (W32.HalfRel.xor h2 hK0 fun i hi p hp => ?_).congr_right fun _ _ => rfl
    show (slotW s₁ _).getLsbD p = _
    rw [show d1Slot + (i + 16) % 32 = d1Slot + (16 + i) by omega, w₁ (16 + i) (by omega) p hp,
      show d1Slot + (16 + i) = d2Slot + i by rw [d1Slot_eq, d2Slot_eq]; omega]
    simp only [↓reduceIte, show (16 + i + 16) % 32 = i by omega, half]
  · refine (W32.HalfRel.xor h1 hK1 fun i hi p hp => ?_).congr_right fun _ _ => rfl
    show (slotW s₁ _).getLsbD p = _
    rw [show (16 + i + 16) % 32 = i by omega, w₁ i (by omega) p hp]
    simp only [↓reduceIte, show (i + 16) % 32 = 16 + i by omega, half]

/-! ## The groups -/

theorem groups_wp {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    (hk : AtEntry s (s₀.gpr sb) 2) {S : Nat → BitVec 64 × BitVec 64} (hS : Halves s S) :
    WP isa (.loop (groupBody g) .ne) s fun s' => Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) (8 * g) ∧
      Halves s' (fun b => groups g E (S b)) := by
  have hg0 : 0 < g := by rcases hp.hg with h | h <;> omega
  let Inv : Nat → State → Prop := fun n s' => ∃ i, n = g - i ∧ i < g ∧ Ctx s₀ s' ∧
    AtEntry s' (s₀.gpr sb) (2 + 8 * i) ∧ Halves s' (fun b => groupsN g E i (S b))
  refine WP.loop (M := isa) Inv (fun n s' hs' => ?_) g s ⟨0, by omega, hg0, hc, hk, by simpa [groupsN] using hS⟩
  obtain ⟨i, rfl, hi, hc', hk', hS'⟩ := hs'
  refine WP.mono (group_wp hp hc' hi hk' hS') fun s'' ⟨c'', S'', k'', z''⟩ => ?_
  simp only [← groupsN_succ] at S''
  by_cases he : i + 1 = g
  · refine .inl ⟨(eval_ne s'').trans (by rw [z'']; simp [he]), c'', ?_, ?_⟩
    · simpa only [show ¬ i + 1 < g by omega, ↓reduceIte] using k''
    · have hG : ∀ d, groupsN g E (i + 1) d = groups g E d := fun d => by rw [he]; rfl
      simpa only [hG] using S''
  · refine .inr ⟨(eval_ne s'').trans (by rw [z'']; simp [he]), g - (i + 1), by omega, i + 1, rfl,
      by omega, c'', ?_, S''⟩
    simpa only [show i + 1 < g by omega, ↓reduceIte] using k''

/-! ## Eight blocks -/

/-- `crypt8`: each of the eight blocks in the tail buffer becomes `cryptWords g E` of it. -/
theorem crypt8_ok {s₀ : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) :
    WP isa (crypt8 g) s₀ fun s' => Ctx s₀ s' ∧
      ∀ b < 8, blk s' b = Spec.Camellia.encodeBlock (cryptWords g E (Spec.Camellia.decodeBlock (blk s₀ b))) := by
  obtain ⟨s₁, e₁, c₁, k₁, S₁⟩ := head_ok hp
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.seq (WP.mono (groups_wp hp c₁ k₁ S₁) fun s₂ ⟨c₂, k₂, S₂⟩ => ?_)
  obtain ⟨s₃, e₃, c₃, w₃⟩ := tail_ok hp c₂ k₂ S₂
  refine WP.of_runBlock ⟨s₃, e₃, c₃, fun b hb => ?_⟩
  rw [blk_of_words (by rw [c₃.base]; exact hp.scr.fit) w₃ hb, cryptWords]
  rfl

end VG.Proof.Camellia.X86
