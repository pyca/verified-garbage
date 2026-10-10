import VerifiedGarbage.Proof.Sm4.X86.Ecb
import VerifiedGarbage.Proof.Sm4.Planes

/-!
# The start of the SM4 key schedule on x86 (32-bit)

As on ARMv7 (`Proof/Sm4/Arm/KeyInit.lean`): the planes of `CK` stored as
constants (`constStores_ok`), and `MK ⊕ FK` stored to the eight blocks of
the tail buffer (`loadKeyWord_ok`), whose words, bitsliced, are the key
schedule's initial state `keyInit` (`keyInit_rel`).
-/

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
  simp only [tailAt, tailSlot_eq, slots_eq]; omega

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
  rw [readW32_bit _ _ (by omega) hj, VG.Proof.Sm4.blockAt_getD _ _ hi, hb,
    byte_addr b (k := tailAt c (i / 4)) rfl (by simp only [tailAt, tailSlot_eq]; rw [slots_eq] at hfit; omega),
    VG.Offset.add_add, tailAt]
  rw [show 4 * tailSlot + 16 * c + i = 4 * (tailSlot + 4 * c + i / 4) + i % 4 by omega]

/-- The tail buffer's blocks are `MK ⊕ FK`, from the key's words `K w`. -/
theorem keyInit_rel {s : State} {b : BitVec 32} (hb : s.gpr sb = b) (hfit : b.toNat + 4 * slots ≤ 2 ^ 32)
    {key : Spec.Sm4.Block} {K : Nat → BitVec 32}
    (hK : ∀ w < 4, ∀ t < 4, ∀ j < 8, (K w).getLsbD (8 * t + j) = (key.getD (4 * w + t) 0).getLsbD j)
    (hT : ∀ c < 8, ∀ w < 4, s.mem.readW (wordAddr b (tailAt c w)) 32 = K w ^^^ fkLE w) :
    ∀ c < 8, ∀ w < 4, VG.Proof.Sm4.ofBlock (tailBlock s c) w = keyInit key w := by
  intro c hc w hw
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hi : 3 - k / 8 < 4 := by omega
  rw [show k = 8 * (3 - (3 - k / 8)) + k % 8 by omega]
  simp only [VG.Proof.Sm4.ofBlock, keyInit]
  rw [BitVec.getLsbD_xor, getLsbD_wordAt _ _ hi (by omega), getLsbD_wordAt _ _ hi (by omega),
    tailBlock_bit s hb hfit hc (by omega) (by omega), show (4 * w + (3 - k / 8)) / 4 = w by omega,
    hT c hc w hw, BitVec.getLsbD_xor, fkLE_bit (by omega), show (4 * w + (3 - k / 8)) % 4 = 3 - k / 8 by omega,
    hK w hw _ hi _ (by omega)]
  congr 2
  omega

end VG.Proof.Sm4.X86
