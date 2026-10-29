module
public import VerifiedGarbage.Impl.Sm4.RISCV64.ExpandKey
public import VerifiedGarbage.Proof.Sm4.RISCV64.Round

import VerifiedGarbage.Proof.Sm4.RISCV64.Prologue
import VerifiedGarbage.Proof.Sm4.RISCV64.Group
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sm4.RISCV64.LayersLit

/-!
# The start of the SM4 key schedule on RISCV64

As on PPC64LE (`Proof/Sm4/PPC64LE/KeyInit.lean`): the planes of `CK`
stored as constants (`ckTable_ok`, through a pointer to the table, beyond
an offset's reach from `a5`), and `MK ⊕ FK` stored to the sixteen blocks of
the tail buffer (`loadHalf_ok`, the key read a byte at a time), whose
words, bitsliced, are the key schedule's initial state `keyInit`.
-/

@[expose] public section

namespace VG.Proof.Sm4.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Impl.Sm4.RISCV64
open VG.Impl.Aes.RISCV64 (q m sb t0 t1 t2 movR ldS stS xorR)
open VG.Impl.Words.RISCV64 (li64 loadLE64)
open VG.Impl.Sm4 (planeOf fkWord)

/-! ## Stores of a register -/

/-- `sd r, 8 k(sb)` for each `k` of `ks`. -/
theorem storeAll_ok (r : Reg) : ∀ (ks : List Nat) {s : State} {b : Addr}, s.gpr sb = b →
    (⟨b, 8 * slots⟩ : Region) ∈ s.wr → b.toNat % 8 = 0 → (∀ k ∈ ks, k < tableSlot) →
    ∃ s', runBlock isa (ks.map fun k => stS k r) s = some s' ∧ (∀ k ∈ ks, slotW s' k = s.gpr r) ∧
      (∀ k < slots, k ∉ ks → slotW s' k = slotW s k) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b, 8 * slots⟩] s.mem s'.mem
  | [], s, _, _, _, _, _ => ⟨s, rfl, by simp, fun _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | k :: ks, s, b, hb, hw, hal, hk => by
    have hk0 : k < tableSlot := hk k List.mem_cons_self
    rw [tableSlot_eq] at hk0
    have e₁ := stS_ok s r (k := k) (by omega) (by rw [hb]; exact hal) ⟨_, hw, by
      rw [hb]; exact VG.Offset.contains_base b (by rw [slots_eq]; omega) (by omega)⟩
    let s₁ : State := { s with mem := s.mem.writeW (wordAddr (s.gpr sb) k) (s.gpr r) }
    obtain ⟨s', e', v', o', g', rd', wr', f'⟩ := storeAll_ok r ks (s := s₁) hb hw hal
      fun k h => hk k (List.mem_cons_of_mem _ h)
    have hslot : ∀ j < slots, slotW s₁ j = if j = k then s.gpr r else slotW s j := fun j hj => by
      simp only [slotW, s₁]
      exact readW_slot_write _ hj (by rw [slots_eq]; omega)
    refine ⟨s', by rw [List.map_cons, show (stS k r :: ks.map fun k => stS k r) = [stS k r] ++ ks.map fun k => stS k r
        from rfl, Interleave.runBlock_append, e₁, Option.bind_some]; exact e', fun j hj => ?_, fun j hj hn => ?_,
      by rw [g'], by rw [rd'], by rw [wr'], ?_⟩
    · rcases List.mem_cons.mp hj with rfl | hj'
      · by_cases hin : j ∈ ks
        · rw [v' j hin]
        · rw [o' j (by rw [slots_eq]; omega) hin, hslot j (by rw [slots_eq]; omega), ite_eq_left rfl]
      · rw [v' j hj']
    · simp only [List.mem_cons, not_or] at hn
      rw [o' j hj hn.2, hslot j hj, ite_eq_right hn.1]
    · refine Frame.trans (fun x hx => ?_) f'
      simp only [s₁, Mem.writeW, Mem.write, wordAddr, hb]
      exact ite_eq_right fun h => hx _ (List.mem_singleton_self _) (VG.Offset.sub_base b
        (show 8 * k + 8 ≤ 8 * slots by rw [slots_eq]; omega) _ (by simp only [Region.Contains]; omega))

/-! ## `MK ⊕ FK` -/

/-- `t0 := ` the key's 64-bit word `h` (little-endian, through `t2` and
`t3`) `⊕ FK`, through `t1`. -/
theorem keyWord_ok (s : State) (h : Nat) (hh : h < 2)
    (hr : ∀ i < 2, InRegions (s.rd ++ s.wr) (s.gpr .a0 + BitVec.ofNat 64 (8 * h + 4 * i)) 4) :
    ∃ s', runBlock isa (loadLE64 t0 t2 (m 1) .a0 (8 * h) ++ li64 t1 t2 (fkWord h) ++
        ([xorR t0 t0 t1] : List Instr)) s = some s' ∧
      s'.gpr t0 = s.mem.readW (s.gpr .a0 + BitVec.ofNat 64 (8 * h)) 64 ^^^ fkWord h ∧
      (∀ r, r ≠ t0 → r ≠ t1 → r ≠ t2 → r ≠ m 1 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, -⟩ := Interleave.runBlock_of_WP (Bytes.loadLE64_ok (s := s)
    (d := t0) (tmp := t2) (hi := m 1) (n := .a0) (off := 8 * h) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by omega)
    (by have := hr 0 (by decide); simpa using this) (by have := hr 1 (by decide); simpa using this))
  obtain ⟨s₂, e₂, h₂⟩ := Interleave.runBlock_of_WP (ByteLoad.li64_ok (s := s₁) (d := t1) (tmp := t2)
    (by decide) (fkWord h))
  subst h₂
  let s₂ := (s₁.write t2 (sext32 ((fkWord h).setWidth 32))).write t1 (fkWord h)
  let s₃ := s₂.write t0 (s₂.gpr t0 ^^^ s₂.gpr t1)
  have e₃ : runBlock isa [xorR t0 t0 t1] s₂ = some s₃ := by
    simp only [xorR, runBlock_cons, exec_logic, runStep_some, runBlock_nil, s₃]
  have g₂ : ∀ r, r ≠ t1 → r ≠ t2 → s₂.gpr r = s₁.gpr r := fun r h1 h2 => by
    rw [RegUpd.gpr_write_of_ne _ _ h1, RegUpd.gpr_write_of_ne _ _ h2]
  refine ⟨s₃, ?_, ?_, fun r h0 h1 h2 h3 => ?_, m₁, rd₁, wr₁⟩
  · rw [Interleave.runBlock_append, Interleave.runBlock_append, e₁, Option.bind_some, e₂, Option.bind_some, e₃]
  · rw [RegUpd.gpr_write_self, g₂ _ (by decide) (by decide), v₁, RegUpd.gpr_write_self]
  · rw [RegUpd.gpr_write_of_ne _ _ h0, g₂ r h1 h2, o₁ r h0 h2 h3]

theorem tailAt_lt {b h : Nat} (hb : b < 16) (hh : h < 2) : tailAt b h < tableSlot := by
  simp only [tailAt, tailSlot_eq, tableSlot_eq]; omega

/-- Half `h` of the key, XOR `FK`, to the sixteen blocks. -/
theorem loadHalf_ok {s : State} {b : Addr} (h : Nat) (hh : h < 2) (hb : s.gpr sb = b)
    (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hal : b.toNat % 8 = 0)
    (hr : ∀ i < 2, InRegions (s.rd ++ s.wr) (s.gpr .a0 + BitVec.ofNat 64 (8 * h + 4 * i)) 4) :
    ∃ s', runBlock isa (loadHalf h) s = some s' ∧
      (∀ c < 16, slotW s' (tailAt c h) = s.mem.readW (s.gpr .a0 + BitVec.ofNat 64 (8 * h)) 64 ^^^ fkWord h) ∧
      (∀ k < slots, (∀ c < 16, k ≠ tailAt c h) → slotW s' k = slotW s k) ∧
      (∀ r, r ≠ t0 → r ≠ t1 → r ≠ t2 → r ≠ m 1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b, 8 * slots⟩] s.mem s'.mem := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := keyWord_ok s h hh hr
  obtain ⟨s', e', v', k', g', rd', wr', f'⟩ := storeAll_ok t0 ((List.range 16).map fun c => tailAt c h)
    (s := s₁) (by rw [o₁ _ (by decide) (by decide) (by decide) (by decide), hb]) (by rw [wr₁]; exact hw) hal
    (fun k hk => by simp only [List.mem_map, List.mem_range] at hk; obtain ⟨c, hc, rfl⟩ := hk
                    exact tailAt_lt hc hh)
  refine ⟨s', ?_, fun c hc => ?_, fun k hk hne => ?_, fun r h0 h1 h2 h3 => by rw [g', o₁ r h0 h1 h2 h3],
    by rw [rd', rd₁], by rw [wr', wr₁], by rw [← m₁]; exact f'⟩
  · rw [loadHalf, Interleave.runBlock_append, e₁, Option.bind_some]
    simpa only [List.map_map, Function.comp_def] using e'
  · rw [v' _ (by simp only [List.mem_map, List.mem_range]; exact ⟨c, hc, rfl⟩), v₁]
  · rw [k' k hk (by simp only [List.mem_map, List.mem_range, not_exists, not_and]; exact fun c hc h' => hne c hc h'.symm)]
    simp only [slotW, m₁, o₁ sb (by decide) (by decide) (by decide) (by decide)]

/-! ## The table of `CK` -/

/-- `li64 t0, v` (through `t1`); `sd t0, d(a4)`. -/
theorem ckOne_ok {s : State} {A : Addr} {d : Nat} (v : BitVec 64) (ha : s.gpr .a4 = A) (hd : d < 2048)
    (hal : (A + BitVec.ofNat 64 d).toNat % 8 = 0) (hw : InRegions s.wr (A + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa (li64 t0 t1 v ++ ([.store .d t0 .a4 d] : List Instr)) s = some s' ∧
      s'.mem = s.mem.writeW (A + BitVec.ofNat 64 d) v ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, h₁⟩ := Interleave.runBlock_of_WP (ByteLoad.li64_ok (s := s) (d := t0) (tmp := t1) (by decide) v)
  subst h₁
  let s₁ := (s.write t1 (sext32 (v.setWidth 32))).write t0 v
  have ha₁ : s₁.gpr .a4 = A := by
    rw [RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide), ha]
  refine ⟨{ s₁ with mem := s₁.mem.writeW (s₁.gpr .a4 + BitVec.ofNat 64 d) (s₁.gpr t0) }, ?_, ?_,
    fun r h0 h1 => ?_, rfl, rfl⟩
  · rw [Interleave.runBlock_append, e₁, Option.bind_some]
    show runBlock isa [.store .d t0 .a4 d] s₁ = _
    simp only [runBlock_cons, exec_store_d (s := s₁) hd (by rw [ha₁]; exact hal) (by rw [ha₁]; exact hw),
      runStep_some, runBlock_nil]
  · show s₁.mem.writeW (s₁.gpr .a4 + BitVec.ofNat 64 d) (s₁.gpr t0) = _
    rw [ha₁, RegUpd.gpr_write_self]; rfl
  · show s₁.gpr r = _
    rw [RegUpd.gpr_write_of_ne _ _ h0, RegUpd.gpr_write_of_ne _ _ h1]

/-- Constants to the words at offsets `8 k` of `A`, through `a4`. -/
theorem ckStores_ok {A : Addr} (hal : A.toNat % 8 = 0) :
    ∀ (ms : List (Nat × BitVec 64)) {s : State}, s.gpr .a4 = A →
      (∀ k < 256, InRegions s.wr (wordAddr A k) 8) →
      (∀ kv ∈ ms, kv.1 < 256) → (ms.map (·.1)).Nodup →
      ∃ s', runBlock isa (ms.flatMap fun (k, v) => li64 t0 t1 v ++ ([.store .d t0 .a4 (8 * k)] : List Instr)) s = some s' ∧
        (∀ kv ∈ ms, s'.mem.readW (wordAddr A kv.1) 64 = kv.2) ∧
        (∀ k < 256, k ∉ ms.map (·.1) → s'.mem.readW (wordAddr A k) 64 = s.mem.readW (wordAddr A k) 64) ∧
        (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        Frame [⟨A, 2048⟩] s.mem s'.mem
  | [], s, _, _, _, _ => ⟨s, rfl, by simp, fun _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | (k, v) :: ms, s, ha, hw, hk, hnd => by
    have hk0 : k < 256 := hk _ List.mem_cons_self
    obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := ckOne_ok (d := 8 * k) v ha (by omega) (Spill.al8 hal (by omega))
      (hw k hk0)
    have ha₁ : s₁.gpr .a4 = A := by rw [g₁ _ (by decide) (by decide), ha]
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', v', o', g', rd', wr', f'⟩ := ckStores_ok hal ms (s := s₁) ha₁ (fun k hk => by rw [wr₁]; exact hw k hk)
      (fun kv h => hk kv (List.mem_cons_of_mem _ h)) hnd.2
    have hslot : ∀ j < 256, s₁.mem.readW (wordAddr A j) 64 = if j = k then v else s.mem.readW (wordAddr A j) 64 :=
      fun j hj => by
        rw [m₁, show A + BitVec.ofNat 64 (8 * k) = wordAddr A k from rfl]
        split
        · rename_i h; subst h; exact Mem.readW_writeW_self64 _ _ _
        · rename_i h; exact Mem.readW_writeW_sep (slot_sep A (by omega) (by omega) h) (by decide)
    refine ⟨s', by
      rw [List.flatMap_cons, Interleave.runBlock_append, e₁, Option.bind_some]; exact e', fun kv hkv => ?_,
      fun j hj hn => ?_, fun r h0 h1 => by rw [g' r h0 h1, g₁ r h0 h1], by rw [rd', rd₁], by rw [wr', wr₁], ?_⟩
    · rcases List.mem_cons.mp hkv with rfl | hkv'
      · rw [o' _ hk0 hnd.1, hslot _ hk0, ite_eq_left rfl]
      · exact v' kv hkv'
    · simp only [List.map_cons, List.mem_cons, not_or] at hn
      rw [o' j hj hn.2, hslot j hj, ite_eq_right hn.1]
    · refine Frame.trans ?_ f'
      rw [m₁]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Offset.contains_base A (by omega) (by omega))

end VG.Proof.Sm4.RISCV64
