module

public import VerifiedGarbage.Impl.Sm4.X86.ExpandKey
public import VerifiedGarbage.Proof.Sm4.X86.Prologue
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Sm4.X86.Crypt8
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Sm4.X86.Ecb
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Sm4.X86.LayersLit
import VerifiedGarbage.Proof.Sm4.Planes
import VerifiedGarbage.Proof.Sm4.Layout
import VerifiedGarbage.Proof.Framework.X86.Taint

/-! ### `Sm4.X86.KeyInit`, which only this module used -/

section

/-!
# The start of the SM4 key schedule on x86 (32-bit)

As on ARMv7 (`Proof/Sm4/Arm/KeyVerified.lean`): the planes of `CK` stored as
constants (`constStores_ok`), and `MK ⊕ FK` stored to the eight blocks of
the tail buffer (`loadKeyWord_ok`), whose words, bitsliced, are the key
schedule's initial state `keyInit` (`keyInit_rel`).
-/

@[expose] public section

namespace VG.Proof.Sm4.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Sm4.X86
open VG.Impl.Aes.X86 (sb slotAt st movI at_)
open VG.Proof.Sm4 (keyInit getLsbD_wordAt fkLE_bit)
open VG.Impl.Sm4 (fkLE)

/-! ## Constants and stores -/

/-- `mov eax, v; mov [edi + 4 k], eax` for each `(k, v)` of `L`. -/
theorem constStores_ok {b : BitVec 32} : ∀ (L : List (Nat × BitVec 32)) {s : State}, s.gpr sb = b →
    ScrIn s.wr b → (L.map (·.1)).Nodup → (∀ x ∈ L, x.1 < slots) →
    ∃ s', runBlock isa (L.flatMap fun (k, v) => [movI .eax v, st k .eax]) s = some s' ∧
      (∀ x ∈ L, s'.mem.readW (wordAddr b x.1) 32 = x.2) ∧
      (∀ k < slots, k ∉ L.map (·.1) → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b.setWidth 64, 4 * slots⟩] s.mem s'.mem
  | [], s, _, _, _, _ => ⟨s, rfl, by simp, fun _ _ _ => rfl, fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | (k, v) :: L, s, hb, hw, hnd, hin => by
    have hx : k < slots := hin (k, v) List.mem_cons_self
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := movI_ok s .eax v
    obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂, -, -, f₂⟩ := stSlot_ok s₁ .eax .edi (b := b) (k := k)
      ((o₁ _ (by decide)).trans hb) hx (by rw [wr₁]; exact hw)
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', v', k', g', rd', wr', f'⟩ := constStores_ok (b := b) L (s := s₂)
      (by rw [g₂]; exact (o₁ _ (by decide)).trans hb) (by rw [wr₂, wr₁]; exact hw) hnd.2
      fun y hy => hin y (List.mem_cons_of_mem _ hy)
    have hfit := hw.fit
    have hslot : ∀ j < slots, s₂.mem.readW (wordAddr b j) 32 = if j = k then v else
        s.mem.readW (wordAddr b j) 32 := fun j hj => by
      rw [m₂, readW_slot_write hfit _ hj hx, v₁, m₁]
    refine ⟨s', ?_, fun y hy => ?_, fun j hj hn => ?_, fun r hr => by rw [g' r hr, g₂, o₁ r hr],
      by rw [rd', rd₂, rd₁], by rw [wr', wr₂, wr₁], ?_⟩
    · show runBlock isa ([movI .eax v] ++ ([.store (slotAt .edi k) .eax] ++
        L.flatMap fun (k, v) => [movI .eax v, st k .eax])) s = some s'
      rw [runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some]
      exact e'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · by_cases hin' : k ∈ L.map (·.1)
        · exact absurd hin' hnd.1
        · rw [k' _ hx hin', hslot _ hx, ite_eq_left rfl]
      · exact v' y hy'
    · simp only [List.map_cons, List.mem_cons, not_or] at hn
      rw [k' j hj hn.2, hslot j hj, ite_eq_right hn.1]
    · rw [← m₁]
      exact (f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact slot_sub hfit hx⟩).trans f'

/-- `mov [edi + 4 k], r` for each `k` of `ks`. -/
theorem storeAll_ok (r : Reg) {b : BitVec 32} : ∀ (ks : List Nat) {s : State}, s.gpr sb = b →
    ScrIn s.wr b → (∀ k ∈ ks, k < slots) →
    ∃ s', runBlock isa (ks.map fun k => st k r) s = some s' ∧
      (∀ k ∈ ks, s'.mem.readW (wordAddr b k) 32 = s.gpr r) ∧
      (∀ k < slots, k ∉ ks → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨b.setWidth 64, 4 * slots⟩] s.mem s'.mem
  | [], s, _, _, _ => ⟨s, rfl, by simp, fun _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | k :: ks, s, hb, hw, hk => by
    have hk0 : k < slots := hk k List.mem_cons_self
    obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁, -, -, f₁⟩ := stSlot_ok s r .edi (b := b) (k := k) hb hk0 hw
    obtain ⟨s', e', v', o', g', rd', wr', f'⟩ := storeAll_ok r (b := b) ks (s := s₁) (by rw [g₁]; exact hb)
      (by rw [wr₁]; exact hw) fun k h => hk k (List.mem_cons_of_mem _ h)
    have hfit := hw.fit
    have hslot : ∀ j < slots, s₁.mem.readW (wordAddr b j) 32 = if j = k then s.gpr r else
        s.mem.readW (wordAddr b j) 32 := fun j hj => by rw [m₁, readW_slot_write hfit _ hj hk0]
    refine ⟨s', by rw [List.map_cons, ← List.singleton_append, runBlock_app,
        show ([st k r] : List Instr) = [.store (slotAt .edi k) r] from rfl, e₁, Option.bind_some]; exact e',
      fun j hj => ?_, fun j hj hn => ?_, by rw [g', g₁], by rw [rd', rd₁], by rw [wr', wr₁], ?_⟩
    · rcases List.mem_cons.mp hj with rfl | hj'
      · by_cases hin : j ∈ ks
        · rw [v' j hin, g₁]
        · rw [o' j hk0 hin, hslot j hk0, ite_eq_left rfl]
      · rw [v' j hj', g₁]
    · simp only [List.mem_cons, not_or] at hn
      rw [o' j hj hn.2, hslot j hj, ite_eq_right hn.1]
    · exact (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact slot_sub hfit hk0⟩).trans f'

/-! ## `MK ⊕ FK` -/

theorem tailAt_lt {c w : Nat} (hc : c < 8) (hw : w < 4) : tailAt c w < slots := by
  simp only [tailAt, tailSlot_eq, slots_eq]; omega_using [hc, hw]

/-- `mov eax, [ecx + 4 w]`, `ecx` holding `K`. -/
theorem ldWord_ok (s : State) {K : BitVec 32} {w : Nat} (hK : s.gpr .ecx = K)
    (hr : InRegions (s.rd ++ s.wr) (wordAddr K w) 4) :
    ∃ s', runBlock isa [.mov .eax (.mem (at_ .ecx (4 * w)))] s = some s' ∧
      s'.gpr .eax = s.mem.readW (wordAddr K w) 32 ∧ (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have he : s.ea (at_ .ecx (4 * w)) = wordAddr K w := by
    show (s.gpr .ecx + BitVec.ofNat 32 (4 * w)).setWidth 64 = _
    rw [hK]; rfl
  refine ⟨s.setReg .eax (s.mem.readW (wordAddr K w) 32), ?_, RegUpd.gpr_setReg_self _ _ _,
    fun _ hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl⟩
  rw [runBlock_cons, show exec (.mov .eax (.mem (at_ .ecx (4 * w)))) s =
      some (s.setReg .eax (s.mem.readW (wordAddr K w) 32)) by
    simp [exec, readSrc, State.load32, he, hr], runStep_some, runBlock_nil]

/-- `xor d, v`. -/
theorem xorI_ok (s : State) (d : Reg) (v : BitVec 32) :
    ∃ s', runBlock isa [.alu .xor d (.imm v)] s = some s' ∧ s'.gpr d = s.gpr d ^^^ v ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨(arithFlags s (s.gpr d ^^^ v) false false).setReg d (s.gpr d ^^^ v), rfl, RegUpd.gpr_setReg_self _ _ _,
    fun _ hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr]; rfl, rfl, rfl, rfl⟩

/-- Word `w` of the key at `K`, XOR `FK`, to the eight blocks. -/
theorem loadKeyWord_ok {s : State} {b K : BitVec 32} (w : Nat) (hw4 : w < 4) (hb : s.gpr sb = b)
    (hw : ScrIn s.wr b) (hK : s.gpr .ecx = K) (hr : InRegions (s.rd ++ s.wr) (wordAddr K w) 4) :
    ∃ s', runBlock isa (loadKeyWord w) s = some s' ∧
      (∀ c < 8, s'.mem.readW (wordAddr b (tailAt c w)) 32 = s.mem.readW (wordAddr K w) 32 ^^^ fkLE w) ∧
      (∀ k < slots, (∀ c < 8, k ≠ tailAt c w) →
        s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b.setWidth 64, 4 * slots⟩] s.mem s'.mem := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldWord_ok s hK hr
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂⟩ := xorI_ok s₁ .eax (fkLE w)
  have o₂' : ∀ r, r ≠ .eax → s₂.gpr r = s.gpr r := fun r hr => by rw [o₂ r hr, o₁ r hr]
  obtain ⟨s', e', v', k', g', rd', wr', f'⟩ := storeAll_ok .eax ((List.range 8).map fun c => tailAt c w)
    (s := s₂) ((o₂' _ (by decide)).trans hb) (by rw [wr₂, wr₁]; exact hw)
    (fun k hk => by simp only [List.mem_map, List.mem_range] at hk; obtain ⟨c, hc, rfl⟩ := hk
                    exact tailAt_lt hc hw4)
  have mem₂ : s₂.mem = s.mem := by rw [m₂, m₁]
  refine ⟨s', ?_, fun c hc => ?_, fun k hk hne => ?_, fun r h0 => by rw [g', o₂' r h0],
    by rw [rd', rd₂, rd₁], by rw [wr', wr₂, wr₁], by rw [← mem₂]; exact f'⟩
  · rw [loadKeyWord, show ([.mov .eax (.mem (at_ .ecx (4 * w))), .alu .xor .eax (.imm (fkLE w))] : List Instr) =
      [.mov .eax (.mem (at_ .ecx (4 * w)))] ++ [.alu .xor .eax (.imm (fkLE w))] from rfl,
      runBlock_app, runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some]
    simpa only [List.map_map, Function.comp_def] using e'
  · rw [v' _ (by simp only [List.mem_map, List.mem_range]; exact ⟨c, hc, rfl⟩), v₂, v₁]
  · rw [k' k hk (by simp only [List.mem_map, List.mem_range, not_exists, not_and]; exact fun c hc h' => hne c hc h'.symm),
      mem₂]

/-- Byte `i` of block `c` of the tail buffer, from its words. -/
theorem tailBlock_bit (s : State) {b : BitVec 32} (hb : s.gpr sb = b) (hfit : b.toNat + 4 * slots ≤ 2 ^ 32)
    {c i j : Nat} (hc : c < 8) (hi : i < 16) (hj : j < 8) :
    ((tailBlock s c).getD i 0).getLsbD j =
      (s.mem.readW (wordAddr b (tailAt c (i / 4))) 32).getLsbD (8 * (i % 4) + j) := by
  rw [readW32_bit _ _ (by omega_using []) hj, VG.Proof.Sm4.blockAt_getD _ _ hi, hb,
    byte_addr b (k := tailAt c (i / 4)) rfl (by simp only [tailAt, tailSlot_eq]; rw [slots_eq] at hfit; omega_using [hfit, hc, hi]),
    VG.Offset.add_add, tailAt]
  rw [show 4 * tailSlot + 16 * c + i = 4 * (tailSlot + 4 * c + i / 4) + i % 4 by omega_using []]

/-- The tail buffer's blocks are `MK ⊕ FK`, from the key's words `K w`. -/
theorem keyInit_rel {s : State} {b : BitVec 32} (hb : s.gpr sb = b) (hfit : b.toNat + 4 * slots ≤ 2 ^ 32)
    {key : Spec.Sm4.Block} {K : Nat → BitVec 32}
    (hK : ∀ w < 4, ∀ t < 4, ∀ j < 8, (K w).getLsbD (8 * t + j) = (key.getD (4 * w + t) 0).getLsbD j)
    (hT : ∀ c < 8, ∀ w < 4, s.mem.readW (wordAddr b (tailAt c w)) 32 = K w ^^^ fkLE w) :
    ∀ c < 8, ∀ w < 4, VG.Proof.Sm4.ofBlock (tailBlock s c) w = keyInit key w := by
  intro c hc w hw
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hi : 3 - k / 8 < 4 := by omega_using []
  rw [show k = 8 * (3 - (3 - k / 8)) + k % 8 by omega_using [hk]]
  simp only [VG.Proof.Sm4.ofBlock, keyInit]
  rw [BitVec.getLsbD_xor, getLsbD_wordAt _ _ hi (by omega_using []), getLsbD_wordAt _ _ hi (by omega_using []),
    tailBlock_bit s hb hfit hc (by omega_using [hw]) (by omega_using []), show (4 * w + (3 - k / 8)) / 4 = w by omega_using [],
    hT c hc w hw, BitVec.getLsbD_xor, fkLE_bit (by omega_using []), show (4 * w + (3 - k / 8)) % 4 = 3 - k / 8 by omega_using [],
    hK w hw _ hi _ (by omega_using [])]
  congr 2
  omega_using []

end VG.Proof.Sm4.X86

end

end

/-! ### `Sm4.X86.KeyLoop`, which only this module used -/

section

/-!
# The loop of the SM4 key schedule on x86 (32-bit)

As on ARMv7 (`Proof/Sm4/Arm/KeyLoop.lean`): each iteration runs four rounds
of the key schedule, puts the state's words in the tail buffer as a block
(`fromBs_step`), and stores them to the schedule as little-endian words
(`extract_ok`): the first block's words, last first, byte-reversed
(`bswap`). The schedule's pointer waits in slot `nSlot` (the rounds use
every register).
-/

@[expose] public section

namespace VG.Proof.Sm4.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Sm4.X86
open VG.Impl.Aes.X86 (sb slotAt st movS addI at_)
open VG.Proof.Sm4 (writeW32_byte writeW32_other)

theorem out_of_disj {r₁ r₂ : Region} (hd : r₁.Disjoint r₂) {x a : Addr} {n : Nat} (hx : r₁.Contains x 1)
    (ha : r₂.Contains a n) : ¬ (x - a).toNat < n := fun h => hd x hx (ha.byte h)

/-! ## The extraction -/

/-- The extraction, after its first `k` words: the schedule's bytes at `P`
before `4 k` hold the tail buffer's first block, last byte first. -/
structure ExtInv (s₀ : State) (b P : BitVec 32) (k : Nat) (s : State) : Prop where
  base : s.gpr sb = b
  ptr : s.gpr .ecx = P
  bytes : ∀ t < 4 * k, ∀ j < 8, (s.mem (P.setWidth 64 + BitVec.ofNat 64 t)).getLsbD j =
    ((tailBlock s₀ 0).getD (15 - t) 0).getLsbD j
  frame : Frame [⟨P.setWidth 64, 4 * k⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .eax → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The extraction's word `k`. -/
theorem extStep_ok {s₀ s : State} {b P : BitVec 32} {k : Nat} (hk : k < 4)
    (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) (hP : P.toNat + 16 ≤ 2 ^ 32)
    (hw : ScrIn s₀.wr b) (hS : ∀ t < 4, InRegions s₀.wr (P.setWidth 64 + BitVec.ofNat 64 (4 * t)) 4)
    (hsep : Region.Disjoint ⟨P.setWidth 64, 16⟩ ⟨b.setWidth 64, 4 * slots⟩) (hb₀ : s₀.gpr sb = b)
    (hi : ExtInv s₀ b P k s) :
    ∃ s', runBlock isa [movS .eax (tailAt 0 (3 - k)), .bswap .eax, .store (at_ .ecx (4 * k)) .eax] s = some s' ∧
      ExtInv s₀ b P (k + 1) s' := by
  obtain hb := setWidth_toNat b
  obtain hPn := setWidth_toNat P
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, -, -⟩ := ldSlot_ok s .eax .edi (k := tailAt 0 (3 - k)) hi.base
    (tailAt_lt (by decide) (by omega_using [])) (by rw [hi.wr]; exact hw)
  let s₂ := s₁.setReg .eax (bswap (s₁.gpr .eax))
  obtain e₂ : runBlock isa [.bswap .eax] s₁ = some s₂ := by
    rw [runBlock_cons, show exec (.bswap .eax) s₁ = some s₂ from rfl, runStep_some, runBlock_nil]
  obtain ecx₂ : s₂.gpr .ecx = P := by rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), o₁ _ (by decide), hi.ptr]
  obtain eA : s₂.ea (at_ .ecx (4 * k)) = P.setWidth 64 + BitVec.ofNat 64 (4 * k) := by
    show (s₂.gpr .ecx + BitVec.ofNat 32 (4 * k)).setWidth 64 = _
    rw [ecx₂]; exact setWidth_add (by omega_using [hk, hP])
  obtain wr₂ : s₂.wr = s₀.wr := by show s₁.wr = _; rw [wr₁, hi.wr]
  obtain hin : InRegions s₂.wr (P.setWidth 64 + BitVec.ofNat 64 (4 * k)) 4 := by rw [wr₂]; exact hS k hk
  -- The slot read is the one on entry.
  obtain hslot : s.mem.readW (wordAddr b (tailAt 0 (3 - k))) 32 = s₀.mem.readW (wordAddr b (tailAt 0 (3 - k))) 32 := by
    obtain hk' := tailAt_lt (c := 0) (w := 3 - k) (by decide) (by omega_using [])
    rw [slot_addr (by omega_using [hfit, hk'])]
    refine hi.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact ((hsep.sub_left (Region.sub_prefix (by omega_using [hk]))).sub_right
      (VG.Offset.sub_base _ (by omega_using [hk']))).symm
  obtain v₂ : s₂.gpr .eax = bswap (s₀.mem.readW (wordAddr b (tailAt 0 (3 - k))) 32) := by
    rw [RegUpd.gpr_setReg_self, v₁, hslot]
  let s₃ : State := { s₂ with mem := s₂.mem.writeW (P.setWidth 64 + BitVec.ofNat 64 (4 * k)) (s₂.gpr .eax) }
  obtain e₃ : runBlock isa [.store (at_ .ecx (4 * k)) .eax] s₂ = some s₃ := by
    rw [runBlock_cons]
    simp only [exec, State.store32, eA, hin, ↓reduceIte, runStep_some, runBlock_nil, s₃]
  have mem₂ : s₂.mem = s.mem := m₁
  refine ⟨s₃, ?_, ⟨by show s₂.gpr sb = b; rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), o₁ _ (by decide), hi.base],
    ecx₂, fun t ht j hj => ?_, ?_, fun r hr => ?_, by show s₁.rd = _; rw [rd₁, hi.rd], wr₂⟩⟩
  · rw [show ([movS .eax (tailAt 0 (3 - k)), .bswap .eax, .store (at_ .ecx (4 * k)) .eax] : List Instr) =
      [.mov .eax (.mem (slotAt .edi (tailAt 0 (3 - k))))] ++ ([.bswap .eax] ++ [.store (at_ .ecx (4 * k)) .eax])
      from rfl, runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, e₃]
  · show (s₂.mem.writeW _ _ _).getLsbD j = _
    by_cases hlt : t < 4 * k
    · rw [writeW32_other _ _ _ _ (VG.Proof.Sm4.off_sub_not _ (Or.inl hlt) (by omega_using [hk, ht]) (by decide) (by omega_using [hk])),
        mem₂]
      exact hi.bytes t hlt j hj
    · have hc : t - 4 * k < 4 := by omega_using [ht]
      rw [show P.setWidth 64 + BitVec.ofNat 64 t =
          P.setWidth 64 + BitVec.ofNat 64 (4 * k) + BitVec.ofNat 64 (t - 4 * k) by
        rw [VG.Offset.add_add, show 4 * k + (t - 4 * k) = t by omega_using [hlt]],
        writeW32_byte _ _ _ hc hj, v₂, bswap_bit _ hc hj,
        tailBlock_bit s₀ (c := 0) (i := 15 - t) hb₀ hfit (by decide) (by omega_using []) hj,
        show (15 - t) / 4 = 3 - k by omega_using [ht, hlt], show (15 - t) % 4 = 3 - (t - 4 * k) by omega_using [hk, ht, hlt]]
  · refine (hi.frame.sub fun r hr => ⟨⟨P.setWidth 64, 4 * (k + 1)⟩, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_using [])⟩).trans ?_
    show Frame _ s.mem (s₂.mem.writeW _ _)
    rw [mem₂]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Offset.contains_base _ (by omega_using []) (by omega_using [hk]))
  · show (s₁.setReg .eax _).gpr r = _
    rw [RegUpd.gpr_setReg_of_ne _ _ hr, o₁ r hr, hi.regs r hr]

/-- The schedule's bytes `16 m … 16 m + 15`: the words of the tail buffer's
first block, the last first, each little-endian; the schedule's pointer
stepped. -/
theorem extract_ok {s : State} {b S : BitVec 32} {m : Nat} (hm : m < 8) (hb : s.gpr sb = b) (hw : ScrIn s.wr b)
    (hSfit : S.toNat + 128 ≤ 2 ^ 32) (hS : (⟨S.setWidth 64, 128⟩ : Region) ∈ s.wr)
    (hsep : Region.Disjoint ⟨S.setWidth 64, 128⟩ ⟨b.setWidth 64, 4 * slots⟩)
    (hn : s.mem.readW (wordAddr b nSlot) 32 = S + BitVec.ofNat 32 (16 * m)) :
    ∃ s', runBlock isa extract s = some s' ∧
      (∀ t < 16, ∀ j < 8, (s'.mem (S.setWidth 64 + BitVec.ofNat 64 (16 * m + t))).getLsbD j =
        ((tailBlock s 0).getD (15 - t) 0).getLsbD j) ∧
      s'.mem.readW (wordAddr b nSlot) 32 = S + BitVec.ofNat 32 (16 * (m + 1)) ∧
      Frame [⟨S.setWidth 64 + BitVec.ofNat 64 (16 * m), 16⟩, ⟨wordAddr b nSlot, 4⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfit := hw.fit
  obtain hSn := setWidth_toNat S
  let P := S + BitVec.ofNat 32 (16 * m)
  obtain hPa : P.setWidth 64 = S.setWidth 64 + BitVec.ofNat 64 (16 * m) := setWidth_add (by omega_using [hm, hSfit])
  obtain hPn : P.toNat + 16 ≤ 2 ^ 32 := by rw [toNat_add32 _ (by omega_using [hm, hSfit])]; omega_using [hm, hSfit]
  obtain subP : Region.Sub ⟨P.setWidth 64, 16⟩ ⟨S.setWidth 64, 128⟩ := by
    rw [hPa]; exact VG.Offset.sub_base _ (by omega_using [hm])
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, -, -⟩ := ldSlot_ok s .ecx .edi (k := nSlot) hb (by decide) hw
  rw [hn] at v₁
  obtain hb₁ : s₁.gpr sb = b := by rw [o₁ _ (by decide)]; exact hb
  obtain hw₁ : ScrIn s₁.wr b := by rw [wr₁]; exact hw
  obtain hS₁ : ∀ t < 4, InRegions s₁.wr (P.setWidth 64 + BitVec.ofNat 64 (4 * t)) 4 := fun t ht =>
    ⟨_, by rw [wr₁]; exact hS, by rw [hPa, VG.Offset.add_add]; exact VG.Offset.contains_base _ (by omega_using [hm, ht]) (by omega_using [hm, ht])⟩
  obtain hsepP : Region.Disjoint ⟨P.setWidth 64, 16⟩ ⟨b.setWidth 64, 4 * slots⟩ := hsep.sub_left subP
  obtain i0 : ExtInv s₁ b P 0 s₁ := ⟨hb₁, v₁, fun t ht => by omega, Frame.refl _ _, fun _ _ => rfl, rfl, rfl⟩
  obtain ⟨s₂, e₂, i₂⟩ := extStep_ok (k := 0) (by decide) hfit hPn hw₁ hS₁ hsepP hb₁ i0
  obtain ⟨s₃, e₃, i₃⟩ := extStep_ok (k := 1) (by decide) hfit hPn hw₁ hS₁ hsepP hb₁ i₂
  obtain ⟨s₄, e₄, i₄⟩ := extStep_ok (k := 2) (by decide) hfit hPn hw₁ hS₁ hsepP hb₁ i₃
  obtain ⟨s₅, e₅, i₅⟩ := extStep_ok (k := 3) (by decide) hfit hPn hw₁ hS₁ hsepP hb₁ i₄
  obtain ⟨s₆, e₆, r₆, -, o₆, m₆, rd₆, wr₆⟩ := addI_ok s₅ .ecx 16
  obtain ⟨s₇, e₇, m₇, g₇, rd₇, wr₇, -, -, f₇⟩ := stSlot_ok s₆ .ecx .edi (b := b) (k := nSlot)
    (by rw [o₆ _ (by decide)]; exact i₅.base) (by decide) (by rw [wr₆, i₅.wr, wr₁]; exact hw)
  obtain hmem₇ : s₇.mem = s₅.mem.writeW (wordAddr b nSlot) (P + BitVec.ofNat 32 16) := by
    rw [m₇, m₆, r₆, i₅.ptr]; rfl
  obtain hblk : tailBlock s₁ 0 = tailBlock s 0 := by simp only [tailBlock, m₁, hb₁, hb]
  obtain dN : Region.Disjoint ⟨P.setWidth 64, 16⟩ ⟨wordAddr b nSlot, 4⟩ :=
    hsepP.sub_right (slot_sub hfit (by decide))
  refine ⟨s₇, ?_, fun t ht j hj => ?_, ?_, ?_, fun r h0 h7 => ?_, by rw [rd₇, rd₆, i₅.rd, rd₁],
    by rw [wr₇, wr₆, i₅.wr, wr₁]⟩
  · rw [extract, show (List.range 4).flatMap (fun k => ([movS .eax (tailAt 0 (3 - k)), .bswap .eax,
        .store (at_ .ecx (4 * k)) .eax] : List Instr)) =
        [movS .eax (tailAt 0 (3 - 0)), .bswap .eax, .store (at_ .ecx (4 * 0)) .eax] ++
        ([movS .eax (tailAt 0 (3 - 1)), .bswap .eax, .store (at_ .ecx (4 * 1)) .eax] ++
        ([movS .eax (tailAt 0 (3 - 2)), .bswap .eax, .store (at_ .ecx (4 * 2)) .eax] ++
        [movS .eax (tailAt 0 (3 - 3)), .bswap .eax, .store (at_ .ecx (4 * 3)) .eax])) from rfl,
      show ([addI .ecx 16, st nSlot .ecx] : List Instr) =
        [addI .ecx 16] ++ [.store (slotAt .edi nSlot) .ecx] from rfl,
      runBlock_app, runBlock_app,
      show ([movS .ecx nSlot] : List Instr) = [.mov .ecx (.mem (slotAt .edi nSlot))] from rfl, e₁,
      Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some, runBlock_app, e₄,
      Option.bind_some, e₅, Option.bind_some, runBlock_app, e₆, Option.bind_some, e₇]
  · have hx : (⟨P.setWidth 64, 16⟩ : Region).Contains (P.setWidth 64 + BitVec.ofNat 64 t) 1 :=
      VG.Offset.contains_base _ (by omega_using [ht]) (by omega_using [ht])
    rw [show S.setWidth 64 + BitVec.ofNat 64 (16 * m + t) = P.setWidth 64 + BitVec.ofNat 64 t by
        rw [hPa, VG.Offset.add_add],
      hmem₇, writeW32_other _ _ _ _ (out_of_disj dN hx (Region.contains_self _ _)), i₅.bytes t (by omega_using [ht]) j hj,
      hblk]
  · rw [hmem₇, Mem.readW_writeW_self32]
    simp only [P]
    rw [VG.Offset.add_add, show 16 * m + 16 = 16 * (m + 1) by omega_using []]
  · rw [← m₁]
    refine (i₅.frame.sub fun r hr => ⟨_, List.mem_cons_self, by
      simp only [List.mem_singleton] at hr; subst hr; rw [hPa]; exact fun _ h => h⟩).trans ?_
    rw [← m₆]
    exact f₇.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  · rw [g₇, o₆ r h7, i₅.regs r h0, o₁ r h7]

end VG.Proof.Sm4.X86

end

end


/-!
# The SM4 key schedule on x86 (32-bit): the whole function

As on ARMv7 (`Proof/Sm4/Arm/KeyVerified.lean`): `expandKey_wp`, with the working
space as an argument (`expandKeyX86`): `expandKey` saves the callee-saved
registers, keeps the schedule's pointer in its slot, stores the table of
`CK`'s planes, bitslices eight copies of `MK ⊕ FK`, runs the loop
(`ekIter_ok`) and restores the registers; the schedule is the
specification's `expandKey`.
-/

@[expose] public section

namespace VG.Proof.Sm4

open VG VG.X86 VG.Impl.Sm4.X86

/-- The key schedule on x86 with its working space as the third argument. -/
def expandKeyX86 : Contract X86.isa where
  pre s :=
    let key : Region := ⟨(arg s 0).setWidth 64, 16⟩
    let sched : Region := ⟨(arg s 1).setWidth 64, 128⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 4 * slots⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [key, args] ∧ s.wr = [sched, scratch] ∧
    key.Disjoint sched ∧ key.Disjoint scratch ∧ sched.Disjoint scratch ∧
    args.Disjoint sched ∧ args.Disjoint scratch ∧ ret.Disjoint sched ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 16 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 128 ≤ 2 ^ 32 ∧
    (arg s 2).toNat + 4 * slots ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  post s s' :=
    Spec.Sm4.scheduleAt s'.mem ((arg s 1).setWidth 64) =
      Spec.Sm4.expandKey (Spec.Sm4.blockAt s.mem ((arg s 0).setWidth 64))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 3, arg s₁ i = arg s₂ i

end VG.Proof.Sm4

namespace VG.Proof.Sm4.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Sm4.X86
open VG.Impl.Aes.X86 (sb slotAt st movS movR addI at_ argOp)
open VG.Proof.Sm4 (quads ofBlock outBlock keyInit rkOf getLsbD_outBlock expandKeyX86 expandKey_eq)
open VG.Impl.Sm4 (planeOf32 fkLE)

/-! ## The loop -/

/-- What the loop keeps, after `m` of its eight iterations: the state holds
the key schedule's words after `4 m` rounds, and the schedule its first
`4 m` round keys. -/
structure EkInv (s₀ : State) (b S : BitVec 32) (key : Spec.Sm4.Block) (m : Nat) (s : State) : Prop where
  base : s.gpr sb = b
  esp : s.gpr .esp = s₀.gpr .esp
  ptr : s.mem.readW (wordAddr b nSlot) 32 = S + BitVec.ofNat 32 (16 * m)
  kp : AtEntry s b (4 * m)
  keys : KeyCtx s Spec.Sm4.ck
  st : StRel s (fun _ => quads .key Spec.Sm4.ck m (keyInit key))
  sched : ∀ i < 4 * m, ∀ c < 4, ∀ j < 8,
    (s.mem (S.setWidth 64 + BitVec.ofNat 64 (4 * i + c))).getLsbD j = (rkOf key i).getLsbD (8 * c + j)
  saved : Saved s₀ b s.mem
  frame : Frame [⟨b.setWidth 64, 4 * slots⟩, ⟨S.setWidth 64, 128⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The scratch buffer and the schedule, writable and apart. -/
structure EkPre (s₀ : State) (b S : BitVec 32) : Prop where
  scr : ScrIn s₀.wr b
  sch : (⟨S.setWidth 64, 128⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨S.setWidth 64, 128⟩ ⟨b.setWidth 64, 4 * slots⟩
  fitS : S.toNat + 128 ≤ 2 ^ 32

theorem ekIter_ok {s₀ : State} {b S : BitVec 32} {key : Spec.Sm4.Block} (hp : EkPre s₀ b S) {m : Nat} (hm : m < 8)
    {s : State} (hi : EkInv s₀ b S key m s) :
    ∃ s', runBlock isa keyBody s = some s' ∧ EkInv s₀ b S key (m + 1) s' ∧
      s'.zf = some (decide (m + 1 = 8)) := by
  have hfit' := hp.scr.fit
  have hfit : b.toNat + 4 * 358 ≤ 2 ^ 32 := hfit'
  have l₁ := tableSlot_eq
  have l₂ := dSlot_eq
  have l₃ := nSlot_eq
  have l₄ := slots_eq
  have l₅ := savedSlot_eq
  have l₆ := tableEnd_eq
  have hfitS := hp.fitS
  obtain hSn := setWidth_toNat S
  obtain hbn := setWidth_toNat b
  obtain hc0 : Ctx s s := Ctx.refl s
  obtain hwS : ScrIn s.wr b := by rw [hi.wr]; exact hp.scr
  -- Four rounds.
  obtain ⟨s₁, e₁, c₁, k₁, X₁⟩ := rounds4_ok .key hi.keys hc0 (by rw [hi.base]; exact hi.kp) hm hi.st
  obtain ⟨s₂, e₂, kp₂, -, o₂, m₂, rd₂, wr₂⟩ := addI_ok s₁ kp 128
  obtain c₂ : Ctx s s₂ := c₁.kp o₂ m₂ rd₂ wr₂
  obtain X₂ : StRel s₂ (fun _ => quads .key Spec.Sm4.ck (m + 1) (keyInit key)) :=
    X₁.congr fun k => by simp only [slotW, m₂, o₂ sb (by decide)]
  -- The words to the tail buffer.
  obtain ⟨s₃, e₃, c₃, kp₃, X₃, T₃⟩ := fromBs_step hi.keys c₂ X₂
  obtain base₃ : s₃.gpr sb = b := by rw [c₃.base, hi.base]
  obtain hwS₃ : ScrIn s₃.wr b := by rw [c₃.wr]; exact hwS
  -- To the schedule.
  obtain ⟨s₄, e₄, B₄, n₄, f₄, o₄, rd₄, wr₄⟩ := extract_ok hm base₃ hwS₃ hfitS
    (by rw [c₃.wr, hi.wr]; exact hp.sch) hp.sep
    (by rw [slot_keep (lo := tableSlot) (hi := slots) hfit' (Nat.le_refl _) c₃.frame (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [hi.base]
          exact VG.Offset.disjoint_base _ (Nat.le_refl _) (by omega_arith))
        (show tableSlot ≤ nSlot by decide) (by decide), hi.ptr])
  obtain ⟨s₅, e₅, z₅, g₅, m₅, rd₅, wr₅⟩ := endTest_ok s₄ (BitVec.ofNat 32 (4 * tableEnd))
  have mem₅ : s₅.mem = s₄.mem := m₅
  obtain g₅' : ∀ r, r ≠ .eax → r ≠ .ecx → s₅.gpr r = s₃.gpr r := fun r h0 h7 => by rw [g₅ r h0, o₄ r h0 h7]
  obtain base₅ : s₅.gpr sb = b := by rw [g₅' _ (by decide) (by decide), base₃]
  obtain kp₄ : s₄.gpr kp = b + BitVec.ofNat 32 (4 * tableSlot + 32 * (4 * (m + 1))) := by
    rw [o₄ _ (by decide) (by decide), kp₃, kp₂, k₁, show s.gpr kp = _ from hi.kp,
      show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, VG.Offset.add_add,
      show 4 * tableSlot + 32 * (4 * m) + 128 = 4 * tableSlot + 32 * (4 * (m + 1)) by omega_arith]
  obtain kp₅ : AtEntry s₅ b (4 * (m + 1)) := by
    rw [AtEntry, g₅ _ (by decide), kp₄]
  -- What the extraction keeps: everything outside the schedule's new bytes and the pointer's slot.
  obtain dHi : ∀ r ∈ [(⟨S.setWidth 64 + BitVec.ofNat 64 (16 * m), 16⟩ : Region), ⟨wordAddr b nSlot, 4⟩],
      (slotsRegion b 0 dSlot).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hp.sep.sub_left (VG.Offset.sub_base _ (by omega_arith))).sub_right
        (VG.Offset.sub_base _ (by omega_arith)) |>.symm
    · rw [slot_addr (by omega_arith)]
      exact VG.Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  obtain keep₄ : ∀ k < dSlot, s₄.mem.readW (wordAddr b k) 32 = s₃.mem.readW (wordAddr b k) 32 := fun k hk =>
    slot_keep (lo := 0) (hi := dSlot) hfit' (by decide) f₄ dHi (Nat.zero_le _) hk
  obtain keepT : ∀ k, tableSlot ≤ k → k < dSlot → s₃.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32 :=
    fun k h1 h2 => slot_keep (lo := tableSlot) (hi := dSlot) hfit' (by decide) c₃.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hi.base]
      exact VG.Offset.disjoint_base _ (Nat.le_refl _) (by omega_arith)) h1 h2
  obtain hent : ∀ e < 32, ∀ j < 8, entryW s₅.mem b e j = entryW s.mem b e j := fun e he j hj => by
    simp only [entryW]
    rw [mem₅, keep₄ _ (by rw [tableSlot_eq, dSlot_eq]; omega_arith), keepT _ (by omega_arith) (by rw [tableSlot_eq, dSlot_eq]; omega_arith)]
  refine ⟨s₅, ?_, ⟨base₅, ?_, by rw [mem₅]; exact n₄, kp₅,
    ⟨by rw [base₅, wr₅, wr₄, c₃.wr, hi.wr]; exact hp.scr,
      fun e he => by rw [base₅]; exact (hi.keys.keys e he).congr fun j hj => by rw [hi.base] at *; exact hent e he j hj⟩,
    fun w hw => (X₃ w hw).congr fun j hj => ?_, fun i hi' c hc j hj => ?_, fun i hi' => ?_, ?_,
    by rw [rd₅, rd₄, c₃.rd, hi.rd], by rw [wr₅, wr₄, c₃.wr, hi.wr]⟩, ?_⟩
  · rw [keyBody, runBlock_app, runBlock_app, runBlock_app, runBlock_app, e₁, Option.bind_some,
      e₂, Option.bind_some, e₃, Option.bind_some, e₄, Option.bind_some, e₅]
  · rw [g₅' _ (by decide) (by decide), c₃.keep _ (by decide) (by decide), hi.esp]
  · show slotW s₅ (stateSlot w j) = slotW s₃ (stateSlot w j)
    rw [slotW, slotW, base₅, base₃, mem₅, keep₄ _ (by simp only [stateSlot, dSlot_eq]; omega_arith)]
  · by_cases hnew : 4 * m ≤ i
    · have ht : 4 * (i - 4 * m) + c < 16 := by omega_arith
      obtain hB := B₄ _ ht j hj
      rw [show 16 * m + (4 * (i - 4 * m) + c) = 4 * i + c by omega_arith] at hB
      rw [mem₅, hB, T₃ 0 (by decide), getLsbD_outBlock _ (by omega_arith) hj]
      simp only [rkOf]
      rw [show i / 4 + 1 = m + 1 by omega_arith, show 3 - (15 - (4 * (i - 4 * m) + c)) / 4 = i % 4 by omega_arith,
        show 8 * (3 - (15 - (4 * (i - 4 * m) + c)) % 4) + j = 8 * c + j by omega_arith]
    · have hx : (⟨S.setWidth 64, 128⟩ : Region).Contains (S.setWidth 64 + BitVec.ofNat 64 (4 * i + c)) 1 :=
        VG.Offset.contains_base _ (by omega_arith) (by omega_arith)
      rw [mem₅, f₄ _ (fun r hr => ?_), c₃.frame _ (fun r hr => ?_)]
      · exact hi.sched i (by omega_arith) c hc j hj
      · simp only [List.mem_singleton] at hr; subst hr; rw [hi.base]
        exact fun h => hp.sep _ hx (Region.sub_prefix (show 4 * tableSlot ≤ 4 * slots by
          rw [tableSlot_eq, slots_eq]; omega_arith) _ h)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact VG.Proof.Sm4.not_contains_off _ (Or.inl (by omega_arith)) (by omega_arith) (by decide) (by omega_arith)
        · exact fun h => hp.sep _ hx (slot_sub hfit' (by decide) _ h)
  · have hk : savedSlot + i < dSlot := by rw [savedSlot_eq, dSlot_eq]; omega_arith
    show s₅.mem.readW _ 32 = _
    rw [mem₅, keep₄ _ hk, keepT _ (by rw [savedSlot_eq, tableSlot_eq]; omega_arith) hk]
    exact hi.saved i hi'
  · rw [mem₅]
    refine hi.frame.trans ((c₃.frame.sub fun r hr => ⟨⟨b.setWidth 64, 4 * slots⟩, List.mem_cons_self, ?_⟩).trans
      (f₄.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr; rw [hi.base]
      exact Region.sub_prefix (by rw [tableSlot_eq, slots_eq]; omega_arith)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨S.setWidth 64, 128⟩, List.mem_cons_of_mem _ List.mem_cons_self, VG.Offset.sub_base _ (by omega_arith)⟩
      · exact ⟨⟨b.setWidth 64, 4 * slots⟩, List.mem_cons_self, slot_sub hfit' (by decide)⟩
  · rw [z₅, kp₄, o₄ _ (by decide) (by decide), show s₃.gpr .edi = b from base₃, VG.Offset.add_sub_cancel_left,
      ofNat32_sub_beq (by rw [tableSlot_eq]; omega_arith) (by rw [tableEnd_eq]; omega_arith), tableSlot_eq, tableEnd_eq]
    simp only [Option.some.injEq, decide_eq_decide]; omega_arith

theorem ekLoop_wp {s₀ s : State} {b S : BitVec 32} {key : Spec.Sm4.Block} (hp : EkPre s₀ b S)
    (hi : EkInv s₀ b S key 0 s) :
    WP isa (.loop (.block keyBody) .ne) s (EkInv s₀ b S key 8) := by
  refine WP.loop (M := isa) (fun n s => ∃ m, n = 8 - m ∧ m < 8 ∧ EkInv s₀ b S key m s)
    (fun n s hs => ?_) 8 s ⟨0, rfl, by omega_arith, hi⟩
  obtain ⟨m, rfl, hm, hi⟩ := hs
  obtain ⟨s', e', hi', z'⟩ := ekIter_ok hp hm hi
  refine WP.of_runBlock ⟨s', e', ?_⟩
  by_cases h8 : m + 1 = 8
  · exact .inl ⟨by rw [eval_ne, z', h8]; rfl, by rw [h8] at hi'; exact hi'⟩
  · exact .inr ⟨by rw [eval_ne, z']; simp [h8], 8 - (m + 1), by omega_arith, m + 1, rfl, by omega_arith, hi'⟩

/-! ## The start -/

theorem ckEntries_mem {e j : Nat} (he : e < 32) (hj : j < 8) :
    (tableSlot + 8 * e + j, planeOf32 (Spec.Sm4.ck e) j) ∈ ckEntries := by
  simp only [ckEntries, List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨e, he, j, hj, rfl⟩

theorem ckEntries_lt : ∀ kv ∈ ckEntries, kv.1 < tableEnd := by decide +kernel

theorem ckEntries_nodup : (ckEntries.map (·.1)).Nodup := by
  -- The slots are consecutive: a linear check, not the quadratic `Nodup` search.
  rw [show ckEntries.map (·.1) = List.range' tableSlot 256 by decide +kernel]
  exact List.nodup_range'

/-- Argument `i` of three is in the arguments' region. -/
theorem arg3_contains (s : State) (hfit : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32) {i : Nat} (hi : i < 3) :
    (⟨argAddr s 0, 12⟩ : Region).Contains (argAddr s i) 4 := by
  obtain hs := setWidth_toNat (s.gpr .esp)
  rw [show argAddr s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) from addr_eq (by omega_arith),
    show argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 from addr_eq (by omega_arith)]
  exact VG.Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)

/-- The code before the loop. -/
def ekHead : List Instr :=
  saveRegs 2 ++ [.mov .eax (.mem (argOp 1)), st nSlot .eax] ++ ckTable ++ loadKey ++ toBs ++ kpAt tableSlot

theorem ekHead_ok {s₀ : State} (hp : expandKeyX86.pre s₀) :
    ∃ s, runBlock isa ekHead s₀ = some s ∧
      EkInv s₀ (arg s₀ 2) (arg s₀ 1) (Spec.Sm4.blockAt s₀.mem ((arg s₀ 0).setWidth 64)) 0 s := by
  obtain ⟨hrd, hwr, dKS, dKB, dSB, dAS, dAB, -, -, fitK, fitS, fitB, fitE⟩ := hp
  let b := arg s₀ 2
  let S := arg s₀ 1
  let Kp := arg s₀ 0
  obtain hwS : ScrIn s₀.wr b := .exact (by rw [hwr]; simp [b]) fitB
  have hfit : b.toNat + 4 * 358 ≤ 2 ^ 32 := fitB
  obtain hbn := setWidth_toNat b
  obtain hKn := setWidth_toNat Kp
  have hfK : Kp.toNat + 16 ≤ 2 ^ 32 := fitK
  have l₁ := tableSlot_eq
  have l₂ := dSlot_eq
  have l₃ := nSlot_eq
  have l₄ := slots_eq
  have l₅ := savedSlot_eq
  have l₆ := tableEnd_eq
  have l₇ := tailSlot_eq
  obtain hrA : (⟨argAddr s₀ 0, 12⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  -- The arguments, through writes of the scratch buffer.
  obtain argR : ∀ {m : Mem}, Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem m → ∀ i < 3,
      m.readW (argAddr s₀ i) 32 = arg s₀ i := fun hf i hi =>
    hf.readW (arg3_contains s₀ fitE hi) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dAB) (by decide)
  obtain argIn : ∀ {s : State}, s.rd = s₀.rd → s.wr = s₀.wr → s.gpr .esp = s₀.gpr .esp → ∀ i < 3,
      InRegions (s.rd ++ s.wr) (s.ea (argOp i)) 4 := fun h1 h2 h3 i hi => by
    rw [h1, h2, ea_arg h3]; exact ⟨_, List.mem_append_left _ hrA, arg3_contains s₀ fitE hi⟩
  -- Saving, the schedule's pointer, the table of `CK`.
  obtain ⟨s₁, e₁, b₁, g₁, sv₁, rd₁, wr₁, f₁, -⟩ := save_ok (k := 2) hwS (argIn rfl rfl rfl 2 (by decide))
    (by rw [ea_arg rfl]; rfl)
  obtain esp₁ : s₁.gpr .esp = s₀.gpr .esp := g₁ _ (by decide) (by decide)
  obtain ⟨s₂, e₂, a₂, o₂, m₂, rd₂, wr₂, f₂⟩ := argSlot_ok s₁ (i := 1) (k := nSlot) b₁ (by decide)
    (by rw [wr₁]; exact hwS) (argIn rd₁ wr₁ esp₁ 1 (by decide))
  obtain b₂ : s₂.gpr sb = b := (o₂ _ (by decide)).trans b₁
  obtain hw₂ : ScrIn s₂.wr b := by rw [wr₂, wr₁]; exact hwS
  obtain ⟨s₃, e₃, v₃, k₃, g₃, rd₃, wr₃, f₃⟩ := constStores_ok ckEntries b₂ hw₂ ckEntries_nodup
    (fun kv hkv => by have := ckEntries_lt kv hkv; omega_arith)
  obtain b₃ : s₃.gpr sb = b := (g₃ _ (by decide)).trans b₂
  obtain esp₃ : s₃.gpr .esp = s₀.gpr .esp := by rw [g₃ _ (by decide), o₂ _ (by decide), esp₁]
  obtain f₀₃ : Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s₃.mem :=
    f₁.trans ((f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact slot_sub fitB (by decide)⟩).trans f₃)
  obtain rd₃' : s₃.rd = s₀.rd := by rw [rd₃, rd₂, rd₁]
  obtain wr₃' : s₃.wr = s₀.wr := by rw [wr₃, wr₂, wr₁]
  -- The key's pointer.
  obtain ⟨s₄, e₄, c₄, o₄, m₄, rd₄, wr₄⟩ := ldArg_ok s₃ .ecx 0 (argIn rd₃' wr₃' esp₃ 0 (by decide))
  obtain ecx₄ : s₄.gpr .ecx = Kp := by rw [c₄, ea_arg esp₃]; exact argR f₀₃ 0 (by decide)
  obtain b₄ : s₄.gpr sb = b := (o₄ _ (by decide)).trans b₃
  obtain hw₄ : ScrIn s₄.wr b := by rw [wr₄, wr₃']; exact hwS
  obtain f₀₄ : Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s₄.mem := by rw [m₄]; exact f₀₃
  -- The key's words, as on entry.
  obtain inK : ∀ w < 4, InRegions (s₀.rd ++ s₀.wr) (wordAddr Kp w) 4 := fun w hw =>
    ⟨_, List.mem_append_left _ (by rw [hrd]; exact List.mem_cons_self), by
      rw [slot_addr (by omega_arith)]; exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain hKw : ∀ (m : Mem), Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem m → ∀ w < 4,
      m.readW (wordAddr Kp w) 32 = s₀.mem.readW (wordAddr Kp w) 32 := fun m hf w hw => by
    rw [slot_addr (by omega_arith)]
    exact hf.readW (r := ⟨Kp.setWidth 64, 16⟩) (VG.Offset.contains_base _ (by omega_arith) (by omega_arith))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dKB) (by decide)
  -- `MK ⊕ FK` to the tail buffer.
  obtain rdwr : ∀ (st : State), st.rd = s₀.rd → st.wr = s₀.wr → ∀ w < 4,
      InRegions (st.rd ++ st.wr) (wordAddr Kp w) 4 := fun st h1 h2 w hw => by rw [h1, h2]; exact inK w hw
  obtain ⟨s₅, e₅, v₅, k₅, g₅, rd₅, wr₅, f₅⟩ := loadKeyWord_ok (s := s₄) 0 (by decide) b₄ hw₄ ecx₄
    (rdwr s₄ (by rw [rd₄, rd₃']) (by rw [wr₄, wr₃']) 0 (by decide))
  obtain ⟨s₆, e₆, v₆, k₆, g₆, rd₆, wr₆, f₆⟩ := loadKeyWord_ok (s := s₅) 1 (by decide)
    (by rw [g₅ _ (by decide), b₄]) (by rw [wr₅]; exact hw₄) (by rw [g₅ _ (by decide), ecx₄])
    (rdwr s₅ (by rw [rd₅, rd₄, rd₃']) (by rw [wr₅, wr₄, wr₃']) 1 (by decide))
  obtain ⟨s₇, e₇, v₇, k₇, g₇, rd₇, wr₇, f₇⟩ := loadKeyWord_ok (s := s₆) 2 (by decide)
    (by rw [g₆ _ (by decide), g₅ _ (by decide), b₄]) (by rw [wr₆, wr₅]; exact hw₄)
    (by rw [g₆ _ (by decide), g₅ _ (by decide), ecx₄])
    (rdwr s₆ (by rw [rd₆, rd₅, rd₄, rd₃']) (by rw [wr₆, wr₅, wr₄, wr₃']) 2 (by decide))
  obtain ⟨s₈, e₈, v₈, k₈, g₈, rd₈, wr₈, f₈⟩ := loadKeyWord_ok (s := s₇) 3 (by decide)
    (by rw [g₇ _ (by decide), g₆ _ (by decide), g₅ _ (by decide), b₄]) (by rw [wr₇, wr₆, wr₅]; exact hw₄)
    (by rw [g₇ _ (by decide), g₆ _ (by decide), g₅ _ (by decide), ecx₄])
    (rdwr s₇ (by rw [rd₇, rd₆, rd₅, rd₄, rd₃']) (by rw [wr₇, wr₆, wr₅, wr₄, wr₃']) 3 (by decide))
  obtain g₈' : ∀ r, r ≠ .eax → s₈.gpr r = s₄.gpr r := fun r h0 => by
    rw [g₈ r h0, g₇ r h0, g₆ r h0, g₅ r h0]
  obtain b₈ : s₈.gpr sb = b := by rw [g₈' _ (by decide), b₄]
  obtain f₀₈ : Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s₈.mem := f₀₄.trans (f₅.trans (f₆.trans (f₇.trans f₈)))
  -- The slots outside the tail buffer after `s₃`.
  obtain notTail : ∀ k, tableSlot ≤ k → ∀ c < 8, ∀ w < 4, k ≠ tailAt c w := fun k hk c hc w hw => by
    simp only [tailAt]; omega_arith
  obtain kk₈ : ∀ k < slots, tableSlot ≤ k →
      s₈.mem.readW (wordAddr b k) 32 = s₃.mem.readW (wordAddr b k) 32 := fun k hk ht => by
    rw [k₈ k hk (fun c hc => notTail k ht c hc 3 (by decide)), k₇ k hk (fun c hc => notTail k ht c hc 2 (by decide)),
      k₆ k hk (fun c hc => notTail k ht c hc 1 (by decide)), k₅ k hk (fun c hc => notTail k ht c hc 0 (by decide)),
      m₄]
  obtain notCk : ∀ k, tableEnd ≤ k → k ∉ ckEntries.map (·.1) := fun k hk hm => by
    simp only [List.mem_map] at hm
    obtain ⟨kv, hkv, rfl⟩ := hm
    have := ckEntries_lt kv hkv; omega_arith
  -- The table of `CK`.
  obtain hkey₈ : KeyCtx s₈ Spec.Sm4.ck :=
    { scr := by rw [b₈, wr₈, wr₇, wr₆, wr₅, wr₄, wr₃']; exact hwS
      keys := fun e he => (planeOf32_rel (Spec.Sm4.ck e)).congr fun j hj => by
        rw [b₈, entryW, kk₈ _ (by omega_arith) (by omega_arith), v₃ _ (ckEntries_mem he hj)] }
  -- The key, bitsliced.
  obtain ⟨s₉, e₉, c₉, X₉⟩ := toBs_step hkey₈ (Ctx.refl s₈)
  obtain ⟨s₁₀a, e₁₀a, k₁₀a, o₁₀a, m₁₀a, rd₁₀a, wr₁₀a, -, -⟩ := movR_ok s₉ kp .edi
  obtain ⟨s₁₀, e₁₀, k₁₀, -, o₁₀, m₁₀, rd₁₀, wr₁₀⟩ := addI_ok s₁₀a kp (BitVec.ofNat 32 (4 * tableSlot))
  obtain b₉ : s₉.gpr sb = b := by rw [c₉.base, b₈]
  obtain b₁₀ : s₁₀.gpr sb = b := by rw [o₁₀ _ (by decide), o₁₀a _ (by decide), b₉]
  obtain mem₁₀ : s₁₀.mem = s₉.mem := by rw [m₁₀, m₁₀a]
  obtain keep₉ : ∀ k, tableSlot ≤ k → k < slots →
      s₁₀.mem.readW (wordAddr b k) 32 = s₈.mem.readW (wordAddr b k) 32 := fun k h1 h2 => by
    rw [mem₁₀]
    exact slot_keep (lo := tableSlot) (hi := slots) fitB (Nat.le_refl _) c₉.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [b₈]
      exact VG.Offset.disjoint_base _ (Nat.le_refl _) (by omega_arith)) h1 h2
  obtain hK : ∀ w < 4, ∀ t < 4, ∀ j < 8, (s₀.mem.readW (wordAddr Kp w) 32).getLsbD (8 * t + j) =
      ((Spec.Sm4.blockAt s₀.mem (Kp.setWidth 64)).getD (4 * w + t) 0).getLsbD j := fun w hw t ht j hj => by
    rw [readW32_bit _ _ ht hj, VG.Proof.Sm4.blockAt_getD _ _ (by omega_arith), byte_addr _ rfl (by omega_arith)]
  obtain hT : ∀ c < 8, ∀ w < 4, s₈.mem.readW (wordAddr b (tailAt c w)) 32 =
      s₀.mem.readW (wordAddr Kp w) 32 ^^^ fkLE w := by
    intro c hc w hw
    obtain hne : ∀ w', w' < 4 → w' ≠ w → ∀ c' < 8, tailAt c w ≠ tailAt c' w' := fun w' _ h c' _ h' => by
      simp only [tailAt] at h'; omega_arith
    obtain hl := tailAt_lt hc hw
    rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by omega_arith) with rfl | rfl | rfl | rfl
    · rw [k₈ _ hl (hne 3 (by decide) (by decide)), k₇ _ hl (hne 2 (by decide) (by decide)),
        k₆ _ hl (hne 1 (by decide) (by decide)), v₅ c hc, hKw _ f₀₄ 0 (by decide)]
    · rw [k₈ _ hl (hne 3 (by decide) (by decide)), k₇ _ hl (hne 2 (by decide) (by decide)), v₆ c hc,
        hKw _ (f₀₄.trans f₅) 1 (by decide)]
    · rw [k₈ _ hl (hne 3 (by decide) (by decide)), v₇ c hc, hKw _ (f₀₄.trans (f₅.trans f₆)) 2 (by decide)]
    · rw [v₈ c hc, hKw _ (f₀₄.trans (f₅.trans (f₆.trans f₇))) 3 (by decide)]
  obtain hst : StRel s₁₀ (fun _ => quads .key Spec.Sm4.ck 0
      (keyInit (Spec.Sm4.blockAt s₀.mem (Kp.setWidth 64)))) := fun w hw =>
    ((X₉ w hw).congr fun j _ => by simp only [planes, slotW, mem₁₀, b₁₀, b₉]).congr_right fun c hc =>
      (keyInit_rel b₈ fitB hK hT c hc w hw).symm
  obtain g₁₀ : ∀ r, r ≠ kp → s₁₀.gpr r = s₉.gpr r := fun r hr => by rw [o₁₀ r hr, o₁₀a r hr]
  refine ⟨s₁₀, ?_, ⟨b₁₀, ?_, ?_, ?_, ?_, hst, fun i hi => by omega_arith, fun i hi => ?_, ?_,
    by rw [rd₁₀, rd₁₀a, c₉.rd, rd₈, rd₇, rd₆, rd₅, rd₄, rd₃'],
    by rw [wr₁₀, wr₁₀a, c₉.wr, wr₈, wr₇, wr₆, wr₅, wr₄, wr₃']⟩⟩
  · rw [ekHead, runBlock_app, runBlock_app, runBlock_app, runBlock_app, runBlock_app, e₁,
      Option.bind_some,
      show ([.mov .eax (.mem (argOp 1)), st nSlot .eax] : List Instr) =
        [.mov .eax (.mem (argOp 1)), .store (slotAt .edi nSlot) .eax] from rfl,
      e₂, Option.bind_some, ckTable, e₃, Option.bind_some,
      show loadKey = [.mov .ecx (.mem (argOp 0))] ++
        (loadKeyWord 0 ++ (loadKeyWord 1 ++ (loadKeyWord 2 ++ loadKeyWord 3))) from rfl,
      runBlock_app, e₄, Option.bind_some,
      runBlock_app, e₅, Option.bind_some, runBlock_app, e₆, Option.bind_some, runBlock_app, e₇, Option.bind_some,
      e₈, Option.bind_some, e₉, Option.bind_some, kpAt,
      show ([movR kp .edi, addI kp (BitVec.ofNat 32 (4 * tableSlot))] : List Instr) =
        [movR kp .edi] ++ [addI kp (BitVec.ofNat 32 (4 * tableSlot))] from rfl, runBlock_app, e₁₀a,
      Option.bind_some, e₁₀]
  · rw [g₁₀ _ (by decide), c₉.keep _ (by decide) (by decide), g₈' _ (by decide), o₄ _ (by decide), esp₃]
  · rw [keep₉ _ (by decide) (by decide), kk₈ _ (by decide) (by decide), k₃ _ (by decide) (notCk _ (by decide)),
      m₂, readW_slot_write fitB _ (by decide) (by decide), ite_eq_left rfl, ea_arg esp₁]
    rw [argR f₁ 1 (by decide)]
    simp
  · rw [AtEntry, k₁₀, k₁₀a, c₉.keep _ (by decide) (by decide), g₈' _ (by decide), show s₄.gpr .edi = b from b₄]
    simp [b]
  · exact (hkey₈.of_ctx c₉) |> fun h => ⟨by rw [wr₁₀, wr₁₀a, b₁₀, ← b₉]; exact h.scr,
      fun e he => by rw [b₁₀, ← b₉, mem₁₀]; exact h.keys e he⟩
  · have hk : savedSlot + i < slots := by omega_arith
    show s₁₀.mem.readW _ 32 = _
    rw [keep₉ _ (by omega_arith) hk, kk₈ _ hk (by omega_arith), k₃ _ hk (notCk _ (by omega_arith)), m₂,
      readW_slot_write fitB _ hk (by decide), ite_eq_right (by omega_arith)]
    exact sv₁ i hi
  · rw [mem₁₀]
    refine (f₀₈.trans (c₉.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)).sub
      fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self, fun _ h => h⟩
    simp only [List.mem_singleton] at hr; subst hr
    rw [b₈]; exact Region.sub_prefix (by omega_arith)

theorem expandKey_wp {s₀ : State} (hp : expandKeyX86.pre s₀) :
    WP isa expandKey s₀ fun s' => abiPreserved s₀ s' ∧ expandKeyX86.post s₀ s' := by
  obtain ⟨s₁, e₁, h₁⟩ := ekHead_ok hp
  obtain ⟨hrd, hwr, dKS, dKB, dSB, dAS, dAB, dRS, dRB, fitK, fitS, fitB, fitE⟩ := hp
  let b := arg s₀ 2
  let S := arg s₀ 1
  obtain hwB : ScrIn s₀.wr b := .exact (by rw [hwr]; simp [b]) fitB
  obtain hwS : (⟨S.setWidth 64, 128⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [S]
  obtain pre : EkPre s₀ b S := ⟨hwB, hwS, dSB, fitS⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.seq (WP.mono (ekLoop_wp pre h₁) fun s₂ h₂ => ?_)
  obtain ⟨s₃, e₃, rg₃, o₃, m₃, -, -⟩ := restore_ok (s₀ := s₀) (b := b) (by rw [h₂.wr]; exact hwB) h₂.base
    h₂.saved
  refine WP.of_runBlock ⟨s₃, e₃, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact rg₃ 0 (by decide)
    · exact rg₃ 1 (by decide)
    · exact rg₃ 2 (by decide)
    · exact rg₃ 3 (by decide)
    · rw [o₃ _ (fun i hi => by revert i; decide), h₂.esp]
  · rw [m₃]
    exact h₂.frame.readW (r := ⟨(s₀.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dRB
      · exact dRS) (by decide)
  · show Spec.Sm4.scheduleAt s₃.mem (S.setWidth 64) = _
    rw [expandKey_eq]
    apply Vector.ext
    intro i hi
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [show k = 8 * (k / 8) + k % 8 by omega_arith, VG.Proof.Sm4.getLsbD_scheduleAt _ _ hi (by omega_arith) (by omega_arith),
      Vector.getElem_ofFn, m₃]
    exact h₂.sched i (by omega_arith) _ (by omega_arith) _ (by omega_arith)

end VG.Proof.Sm4.X86
