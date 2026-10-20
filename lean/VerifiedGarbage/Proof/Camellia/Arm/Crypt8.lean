module

public import VerifiedGarbage.Proof.Camellia.Arm.Core
public import VerifiedGarbage.Proof.Camellia.Arm.StoreFrame
public import VerifiedGarbage.Proof.Camellia.Layout32
import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Camellia.Arm.Fl
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# The head and tail of eight blocks of bitsliced Camellia on ARMv7

`head` bitslices both halves of the eight blocks in the tail buffer (at
`r12`) and whitens them, and `tail` whitens, transposes and stores them
back; between them the groups of rounds (`group_wp`) run in a loop.
`crypt8_ok` composes them: each block becomes `cryptWords g E` of it.
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Camellia.Arm
open VG.Bitslice (lanes)
open VG.Impl.Aes.Arm (q sb t0 t1 u7 kp ldS stS)
open VG.Proof.Camellia (pair group groups cryptWords groupsN groupsN_succ)
open VG.Proof.Sm4.Arm (linPostG linG_ok)

/-! ## The tail buffer -/

/-- Word `t` of the tail buffer. -/
abbrev dataW (s : State) (t : Nat) : BitVec 32 := slotW s (tailSlot + t)

/-- Block `b` in the tail buffer. -/
abbrev blk (s : State) (b : Nat) : Spec.Camellia.Block :=
  Spec.Camellia.blockAt s.mem (State.addr (s.gpr sb) + BitVec.ofNat 64 (4 * tailSlot + 16 * b))

theorem dataW_byte (s : State) (hfit : (s.gpr sb).toNat + 4 * slots ≤ 2 ^ 32) {b c j : Nat} (hb : b < 8)
    (hc : c < 16) (hj : j < 8) :
    (dataW s (4 * b + c / 4)).getLsbD (8 * (c % 4) + j) =
      (s.mem (State.addr (s.gpr sb) + BitVec.ofNat 64 (4 * tailSlot + 16 * b) + BitVec.ofNat 64 c)).getLsbD j := by
  rw [slots_eq] at hfit
  rw [dataW, slotW, wordAddr, VG.Arm.addr_add (by rw [tailSlot_eq]; omega), W32.readW32_bit _ _ (by omega) hj,
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

/-- `r12` points to the tail buffer. -/
def AtTail (s : State) : Prop := s.gpr u7 = s.gpr sb + BitVec.ofNat 32 (4 * tailSlot)

theorem wordAddr_tail {s : State} (h : AtTail s) (j : Nat) :
    wordAddr (s.gpr u7) j = wordAddr (s.gpr sb) (tailSlot + j) := by
  rw [wordAddr, wordAddr, h, add_ofNat_ofNat, show 4 * tailSlot + 4 * j = 4 * (tailSlot + j) by omega]

theorem ok_toBs {s : State} (hs : Scr s (s.gpr sb)) (ht : AtTail s) : Ok toBsCfg s where
  slotIn k hk := hs.slot_in (by simp only [toBsCfg, keySlot_eq] at hk; rw [slots_eq]; omega)
  extIn j hj := by
    simp only [toBsCfg] at hj ⊢
    rw [wordAddr_tail ht]
    obtain ⟨r, hr, hc⟩ := hs.slot_in (k := tailSlot + j) (by rw [slots_eq, tailSlot_eq]; omega)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  slots := by have := hs.fit; simp only [toBsCfg]; rw [slots_eq] at this; rw [keySlot_eq]; omega
  sep k hk j hj := by
    have := hs.fit
    simp only [toBsCfg, keySlot_eq] at hk hj ⊢
    rw [wordAddr_tail ht]
    rw [slots_eq] at this
    exact slot_sep _ (by omega) (by rw [tailSlot_eq]; omega) (by rw [tailSlot_eq]; omega)

theorem toBs_all : (layerKeep.all fun r => ((List.range 4).flatMap toBsWord).all fun i => !clobbers i r) =
    true ∧ (((List.range 4).flatMap toBsWord).all fun i => !clobbers i u7) = true := by
  constructor <;> decide +kernel

/-- `toBs`: the planes of the halves, from the words of the blocks. -/
theorem toBs_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    (ht : AtTail s) :
    ∃ s', runBlock isa ((List.range 4).flatMap toBsWord) s = some s' ∧ Ctx s₀ s' ∧
      s'.gpr kp = s.gpr kp ∧ s'.gpr u7 = s.gpr u7 ∧
      (∀ w < 4, ∀ j < 8, ∀ p < 32, (slotW s' (d1Slot + (8 * w + j))).getLsbD p =
        (dataW s (4 * (p % 8) + w)).getLsbD (8 * (p / 8) + j)) ∧
      (∀ k, keySlot ≤ k → k < slots → slotW s' k = slotW s k) := by
  have hs := hc.scr hp
  obtain ⟨s', h', -, so', -, rd', wr', -, o', f', -, -⟩ := linG_ok toBs_check (ok_toBs hs ht) (dataW s)
    (fun r i hri => by simp at hri) (fun j i hji => by simp at hji) (fun kv hkv => by simp at hkv)
    (fun j hj => ⟨by simp only [toBsCfg] at hj; omega, by rw [Nat.zero_add]; simp only [toBsCfg, wordAddr_tail ht]⟩)
  have hkeep : ∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp toBs_all.1 r (not_layerWrites r hr))
  have hfit : (s.gpr sb).toNat + 4 * slots ≤ 2 ^ 32 := hs.fit
  refine ⟨s', h', hc.stepL rd' wr' (fun r h1 _ => hkeep r h1) f', hkeep _ (by decide), o' _ toBs_all.2,
    fun w hw j hj p hp => ?_, fun k h1 h2 => slot_above_frame hfit (hkeep _ (by decide)) f' h1 h2⟩
  have := so' (d1Slot + (8 * w + j)) (toBsG w j)
    (by
      simp only [toBsOuts, List.mem_map, List.mem_range, Prod.mk.injEq]
      exact ⟨8 * w + j, by omega, rfl, by rw [show (8 * w + j) / 8 = w by omega, show (8 * w + j) % 8 = j by omega]⟩)
    (by simp only [toBsCfg, d1Slot_eq, keySlot_eq]; omega) p hp
  simp only [toBsCfg] at this
  rw [slotW, hkeep _ (by decide), this, toBsG, xorBits_cons, xorBits_nil, Bool.xor_false, Nat.add_assoc,
    bitOf_word _ _ _ (by omega)]

theorem ok_fromBs {s : State} (hs : Scr s (s.gpr sb)) : Ok fromBsCfg s where
  slotIn k hk := by
    simp only [fromBsCfg] at hk ⊢
    exact hs.slot_in (by rw [slots_eq]; rw [tailSlot_eq] at hk; omega)
  extIn j hj := by simp [fromBsCfg] at hj
  slots := by
    have := hs.fit
    simp only [fromBsCfg, tailSlot_eq]
    rw [slots_eq] at this; omega
  sep k _ j hj := by simp [fromBsCfg] at hj

theorem fromBs_all : (layerKeep.all fun r => ((List.range 4).flatMap fromBsWord).all fun i => !clobbers i r) =
    true ∧ (((List.range 4).flatMap fromBsWord).all (storesIn (4 * tailSlot) (4 * tailSlot + 128))) = true := by
  constructor <;> decide +kernel

/-- `fromBs`: the words of the blocks, from the planes of the halves. -/
theorem fromBs_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s) :
    ∃ s', runBlock isa ((List.range 4).flatMap fromBsWord) s = some s' ∧ Ctx s₀ s' ∧
      (∀ b < 8, ∀ w < 4, ∀ i < 4, ∀ j < 8, (dataW s' (4 * b + w)).getLsbD (8 * i + j) =
        (slotW s (d1Slot + (8 * ((w + 2) % 4) + j))).getLsbD (8 * i + b)) := by
  have hs := hc.scr hp
  obtain ⟨s', h', -, so', -, rd', wr', -, o', -, -, -⟩ := linG_ok fromBs_check (ok_fromBs hs) (slotW s)
    (fun r i hri => by simp at hri)
    (fun j i hji => by
      simp only [fromBsIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      obtain ⟨k, hk, rfl, rfl⟩ := hji
      exact ⟨by simp only [fromBsCfg, d1Slot_eq, tailSlot_eq]; omega, by rw [d1Slot_eq]; omega, rfl⟩)
    (fun kv hkv => by simp at hkv) (fun j hj => by simp [fromBsCfg] at hj)
  have hkeep : ∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp fromBs_all.1 r (not_layerWrites r hr))
  have hfit := hs.fit
  rw [slots_eq] at hfit
  obtain ⟨-, f'⟩ := runBlock_storesIn _ fromBs_all.2 (by rw [tailSlot_eq]; omega) h'
  refine ⟨s', h', hc.step rd' wr' (fun r h1 _ => hkeep r h1) ?_, fun b hb w hw i hi j hj => ?_⟩
  · refine f'.sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    have hb := hc.base
    refine ⟨_, by simp only [ctxRegions, List.mem_cons]; exact .inr (.inr (.inl rfl)), ?_⟩
    simp only [storeRegion, hb]
    rw [VG.Arm.addr_add (by rw [← hb, tailSlot_eq]; omega), show 4 * tailSlot + 128 - 4 * tailSlot = 128 by omega]
    exact fun _ h => h
  · have := so' (tailSlot + (4 * b + w)) (fromBsG (4 * b + w))
      (by simp only [fromBsOuts, List.mem_map, List.mem_range]; exact ⟨4 * b + w, by omega, rfl⟩)
      (by simp only [fromBsCfg]; omega) (8 * i + j) (by omega)
    simp only [fromBsCfg] at this
    rw [dataW, slotW, hkeep _ (by decide), this, fromBsG, xorBits_cons, xorBits_nil, Bool.xor_false,
      show (4 * b + w) % 4 = w by omega, show (8 * i + j) % 8 = j by omega, show (8 * i + j) / 8 = i by omega,
      show (4 * b + w) / 4 = b by omega, Nat.add_assoc, bitOf_word _ _ _ (by omega),
      show d1Slot + 8 * ((w + 2) % 4) + j = d1Slot + (8 * ((w + 2) % 4) + j) by omega]

/-! ## The whitening -/

theorem whiten_all (swap : Bool) :
    (layerKeep.all fun r => (whiten swap).all fun i => !clobbers i r) = true ∧
      ((whiten swap).all fun i => !clobbers i u7) = true := by
  cases swap <;> (constructor <;> decide +kernel)

/-- The whitening, with the two entries at `kp`. -/
theorem whiten_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm34 : m + 2 ≤ 34) (swap : Bool)
    (hchk : check (lanes 32 11) layerCfg (linExt 32) (whiten swap) whitenEnv
      (linPostG 11 [] (whitenOuts swap) [] whitenEnv) = true) :
    ∃ s', runBlock isa (whiten swap) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧ s'.gpr u7 = s.gpr u7 ∧
      (∀ i < 32, ∀ p < 32, (slotW s' (d1Slot + i)).getLsbD p =
        ((slotW s (d1Slot + i)).getLsbD p ^^ (keyW s (if swap then (i + 16) % 32 else i)).getLsbD p)) ∧
      (∀ k, keySlot ≤ k → k < slots → slotW s' k = slotW s k) := by
  have hok := hc.ok hp hk hm34
  let W : Nat → BitVec 32 := fun i => if i < 32 then slotW s (d1Slot + i) else keyW s (i - 32)
  obtain ⟨s', h', -, so', -, rd', wr', -, o', f', -, -⟩ := linG_ok hchk hok W
    (fun r i hri => by simp at hri)
    (fun j i hji => by
      obtain ⟨k, hk', rfl, rfl⟩ := halvesIns_mem hji
      exact ⟨by simp only [layerCfg, keySlot_eq, d1Slot_eq]; omega, by omega, by simp [W, hk']; rfl⟩)
    (fun kv hkv => by simp at hkv)
    (fun j hj => by
      simp only [layerCfg] at hj
      exact ⟨by omega, by simp [W, show ¬ 32 + j < 32 by omega]; rfl⟩)
  have hkeep : ∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp (whiten_all swap).1 r (not_layerWrites r hr))
  have hfit : (s.gpr sb).toNat + 4 * slots ≤ 2 ^ 32 := by rw [hc.base]; exact hp.scr.fit
  refine ⟨s', h', hc.stepL rd' wr' (fun r h1 _ => hkeep r h1) f', hkeep _ (by decide), o' _ (whiten_all swap).2,
    fun i hi p hp => ?_, fun k h1 h2 => slot_above_frame hfit (hkeep _ (by decide)) f' h1 h2⟩
  have := so' (d1Slot + i) (whitenG swap i)
    (by simp only [whitenOuts, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩)
    (by simp only [layerCfg, d1Slot_eq, keySlot_eq]; omega) p hp
  simp only [layerCfg] at this
  have hki : (if swap then (i + 16) % 32 else i) < 32 := by split <;> omega
  rw [slotW, hkeep _ (by decide), this, whitenG, Straight.xorBits_cons, Straight.xorBits_cons,
    Straight.xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp, bitOf_word _ _ _ hp]
  simp only [W, hi, ↓reduceIte, show ¬ 32 + (if swap then (i + 16) % 32 else i) < 32 by omega,
    show 32 + (if swap then (i + 16) % 32 else i) - 32 = (if swap then (i + 16) % 32 else i) by omega]

/-! ## The head -/

theorem exec_addImm {s : State} {d n : Reg} {v : BitVec 32} (he : encodable v = true) :
    exec (.dp .add d n (.imm v)) s = some (s.setReg d (s.gpr n + v)) := by
  simp only [exec, Op2.eval, he, ↓reduceIte, Option.map_some]

/-- The halves of the eight blocks after the prewhitening. -/
def headHalves (s : State) (E : Nat → BitVec 64) (b : Nat) : BitVec 64 × BitVec 64 :=
  (W32.hiOf (blk s b) ^^^ E 0, W32.loOf (blk s b) ^^^ E 1)

theorem head_ok {s₀ : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) :
    ∃ s', runBlock isa head s₀ = some s' ∧ Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) 2 ∧
      Halves s' (headHalves s₀ E) := by
  have hg : 8 * g + 2 ≤ 34 := hp.nk34
  have hfit := hp.scr.fit
  let b := s₀.gpr sb
  -- `r12 := ` the tail buffer.
  have e₁ : exec (slotAddr u7 tailSlot) s₀ =
      some (s₀.setReg u7 (s₀.gpr sb + BitVec.ofNat 32 (4 * tailSlot))) := exec_addImm (by decide)
  have c₁ := (Ctx.refl s₀).step (s' := s₀.setReg u7 (s₀.gpr sb + BitVec.ofNat 32 (4 * tailSlot))) rfl rfl
    (fun r h1 _ => RegUpd.gpr_setReg_of_ne _ _ (fun h => h1 (by rw [h]; decide))) (Frame.refl _ _)
  have t₁ : AtTail (s₀.setReg u7 (s₀.gpr sb + BitVec.ofNat 32 (4 * tailSlot))) := by
    rw [AtTail, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ (by decide)]
  -- The transposes.
  obtain ⟨s₂, e₂, c₂, -, -, x₂, a₂⟩ := toBs_step hp.toKeyCtx c₁ t₁
  have hd₁ : ∀ t, dataW (s₀.setReg u7 (s₀.gpr sb + BitVec.ofNat 32 (4 * tailSlot))) t = dataW s₀ t :=
    fun t => slotW_setReg _ _ (by decide) _
  obtain ⟨hD1, hD2⟩ := W32.halves_of_words (Q := fun k => slotW s₂ (d1Slot + k))
    (fun w hw j hj p hp => by rw [x₂ w hw j hj p hp, hd₁]) (data_words s₀ hfit)
  -- `kp := ` the table, and the whitening.
  have e₃ : exec (slotAddr kp keySlot) s₂ = some (s₂.setReg kp (s₂.gpr sb + BitVec.ofNat 32 (4 * keySlot))) :=
    exec_addImm (by decide)
  have c₃ := c₂.step (s' := s₂.setReg kp (s₂.gpr sb + BitVec.ofNat 32 (4 * keySlot))) rfl rfl
    (fun r _ h2 => RegUpd.gpr_setReg_of_ne _ _ h2) (Frame.refl _ _)
  have k₃ : AtEntry (s₂.setReg kp (s₂.gpr sb + BitVec.ofNat 32 (4 * keySlot))) b 0 := by
    rw [AtEntry, RegUpd.gpr_setReg_self, c₂.base, Nat.mul_zero, Nat.add_zero]
  obtain ⟨s₄, e₄, c₄, kp₄, -, w₄, -⟩ := whiten_step hp.toKeyCtx c₃ k₃ (by omega) false whiten0_check
  have hK0 := c₃.keyRel hp.toKeyCtx k₃ (e := 0) (by omega)
  have hK1 := c₃.keyRel hp.toKeyCtx k₃ (e := 1) (by omega)
  simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one] at hK0 hK1
  have hs₃ : ∀ k, slotW (s₂.setReg kp (s₂.gpr sb + BitVec.ofNat 32 (4 * keySlot))) k = slotW s₂ k :=
    fun k => slotW_setReg _ _ (by decide) _
  -- `kp += 128`.
  refine ⟨s₄.setReg kp (s₄.gpr kp + BitVec.ofNat 32 128), ?_, ?_, ?_, ⟨?_, ?_⟩⟩
  · rw [show head = [slotAddr u7 tailSlot] ++ (List.range 4).flatMap toBsWord ++ [slotAddr kp keySlot] ++
        whiten false ++ [.dp .add kp kp (.imm (BitVec.ofNat 32 128))] from rfl,
      runBlock_app, runBlock_app, runBlock_app, runBlock_app, runBlock_cons, e₁, runStep_some, runBlock_nil,
      Option.bind_some, e₂, Option.bind_some, runBlock_cons, e₃, runStep_some, runBlock_nil, Option.bind_some,
      e₄, Option.bind_some, addKp_ok _ _ encodable_128]
  · exact c₄.step rfl rfl (fun r _ h2 => RegUpd.gpr_setReg_of_ne _ _ h2) (Frame.refl _ _)
  · exact k₃.add (n := 2) (by rw [RegUpd.gpr_setReg_self, kp₄])
  · refine (W32.HalfRel.xor hD1 hK0 fun i hi p hp => ?_).congr_right fun _ _ => rfl
    show (slotW (s₄.setReg kp _) (d1Slot + i)).getLsbD p = _
    rw [slotW_setReg _ _ (by decide), w₄ i (by omega) p hp, hs₃]
    simp
  · refine (W32.HalfRel.xor hD2 hK1 fun i hi p hp => ?_).congr_right fun _ _ => rfl
    show (slotW (s₄.setReg kp _) (d2Slot + i)).getLsbD p = _
    rw [slotW_setReg _ _ (by decide), show d2Slot + i = d1Slot + (16 + i) by rw [d1Slot_eq, d2Slot_eq]; omega,
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
  obtain ⟨s₁, e₁, c₁, -, -, w₁, -⟩ := whiten_step hp.toKeyCtx hc hk (by omega) true whiten1_check
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
    WP isa (.loop groupBody .ne) s fun s' => Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) (8 * g) ∧
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
    WP isa crypt8 s₀ fun s' => Ctx s₀ s' ∧
      ∀ b < 8, blk s' b = Spec.Camellia.encodeBlock (cryptWords g E (Spec.Camellia.decodeBlock (blk s₀ b))) := by
  obtain ⟨s₁, e₁, c₁, k₁, S₁⟩ := head_ok hp
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.seq (WP.mono (groups_wp hp c₁ k₁ S₁) fun s₂ ⟨c₂, k₂, S₂⟩ => ?_)
  obtain ⟨s₃, e₃, c₃, w₃⟩ := tail_ok hp c₂ k₂ S₂
  refine WP.of_runBlock ⟨s₃, e₃, c₃, fun b hb => ?_⟩
  rw [blk_of_words (by rw [c₃.base]; exact hp.scr.fit) w₃ hb, cryptWords]
  rfl

end VG.Proof.Camellia.Arm
