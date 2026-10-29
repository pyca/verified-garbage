module
public import VerifiedGarbage.Proof.Sm4.RISCV64.Round
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill

import VerifiedGarbage.Proof.Sm4.RISCV64.Core
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sm4.RISCV64.LayersLit

/-!
# SM4's prologue and epilogue on RISCV64

Saving and restoring the callee-saved registers `s0`–`s11` in their slots
(`save_ok`, `restore_ok`), and storing constants to slots (`setSlots_ok`,
through `li64`): the masks of the round keys' planes and of the transposes.
As on PPC64LE (`Proof/Sm4/PPC64LE/Prologue.lean`), with the scratch buffer
aligned to 8 bytes, as `ld` and `sd` need.
-/

@[expose] public section

namespace VG.Proof.Sm4.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Impl.Sm4.RISCV64
open VG.Impl.Aes.RISCV64 (q sb t0 t1 movR ldS stS)
open VG.Impl.Words.RISCV64 (li64)

theorem savedSlot_eq : savedSlot = 384 := rfl
theorem sb_ne_t0 : sb ≠ t0 := by decide
theorem sb_ne_t1 : sb ≠ t1 := by decide

/-! ## Loads and stores of slots -/

/-- `ld r, 8 k(sb)`. -/
theorem ldMask_ok {s : State} {r : Reg} {k : Nat} {M : BitVec 64} (hk : 8 * k < 2048)
    (hal : (s.gpr sb).toNat % 8 = 0)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr sb + BitVec.ofNat 64 (8 * k)) 8)
    (hv : s.mem.readW (s.gpr sb + BitVec.ofNat 64 (8 * k)) 64 = M) :
    ∃ s', runBlock isa [ldS r k] s = some s' ∧ s'.gpr r = M ∧ (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨_, by simp only [ldS, runBlock_cons, exec_load_d hk (Spill.al8 hal (by omega)) hin, runStep_some,
    runBlock_nil], (RegUpd.gpr_write_self _ _ _).trans hv, fun _ h => RegUpd.gpr_write_of_ne _ _ h,
    rfl, rfl, rfl⟩

/-- Loads of slots into distinct registers other than `sb`. -/
theorem ldS_list_ok : ∀ (L : List (Reg × Nat)) (s : State), (s.gpr sb).toNat % 8 = 0 →
    (∀ x ∈ L, x.1 ≠ sb) → (L.map (·.1)).Nodup →
    (∀ x ∈ L, 8 * x.2 < 2048 ∧ InRegions (s.rd ++ s.wr) (s.gpr sb + BitVec.ofNat 64 (8 * x.2)) 8) →
    ∃ s', runBlock isa (L.map fun x => ldS x.1 x.2) s = some s' ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ (∀ r, r ∉ L.map (·.1) → s'.gpr r = s.gpr r) ∧ ∀ x ∈ L, s'.gpr x.1 = slotW s x.2
  | [], s, _, _, _, _ => ⟨s, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil⟩
  | x :: L, s, hal, hsb, hnd, hin => by
    have hx := hin x List.mem_cons_self
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldMask_ok (r := x.1) (k := x.2) hx.1 hal hx.2 rfl
    have hb₁ : s₁.gpr sb = s.gpr sb := o₁ _ (hsb x List.mem_cons_self).symm
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', m', rd', wr', o', v'⟩ := ldS_list_ok L s₁ (by rw [hb₁]; exact hal)
      (fun y hy => hsb y (List.mem_cons_of_mem _ hy))
      hnd.2 (fun y hy => by rw [rd₁, wr₁, hb₁]; exact hin y (List.mem_cons_of_mem _ hy))
    refine ⟨s', ?_, m'.trans m₁, rd'.trans rd₁, wr'.trans wr₁, fun r hr => ?_, fun y hy => ?_⟩
    · rw [List.map_cons, ← List.singleton_append, Interleave.runBlock_append, e₁, Option.bind_some]; exact e'
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [o' r hr.2, o₁ r hr.1]
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact (o' _ hnd.1).trans v₁
      · rw [v' y hy]; simp only [slotW, m₁, hb₁]

/-- `sd t, 8 k(sb)`. -/
theorem stS_ok (s : State) {k : Nat} (t : Reg) (hk : 8 * k < 2048) (hal : (s.gpr sb).toNat % 8 = 0)
    (hin : InRegions s.wr (s.gpr sb + BitVec.ofNat 64 (8 * k)) 8) :
    runBlock isa [stS k t] s = some { s with mem := s.mem.writeW (wordAddr (s.gpr sb) k) (s.gpr t) } := by
  simp only [stS, runBlock_cons, runStep_some, runBlock_nil, exec_store_d hk (Spill.al8 hal (by omega)) hin]

/-- Stores of registers to distinct slots in the region `R`. -/
theorem stS_list_ok (R : Region) : ∀ (L : List (Nat × Reg)) (s : State), (s.gpr sb).toNat % 8 = 0 →
    (L.map (·.1)).Nodup →
    (∀ x ∈ L, 8 * x.1 < 2048 ∧ InRegions s.wr (s.gpr sb + BitVec.ofNat 64 (8 * x.1)) 8 ∧
      R.Contains (wordAddr (s.gpr sb) x.1) 8) →
    ∃ s', runBlock isa (L.map fun x => stS x.1 x.2) s = some s' ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ Frame [R] s.mem s'.mem ∧
      (∀ k, k ∉ L.map (·.1) → k < 2 ^ 58 → slotW s' k = slotW s k) ∧ ∀ x ∈ L, slotW s' x.1 = s.gpr x.2
  | [], s, _, _, _ => ⟨s, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ _ _ => rfl,
      fun _ h => absurd h List.not_mem_nil⟩
  | x :: L, s, hal, hnd, hin => by
    have hx := hin x List.mem_cons_self
    let s₁ : State := { s with mem := s.mem.writeW (wordAddr (s.gpr sb) x.1) (s.gpr x.2) }
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', g', rd', wr', f', o', v'⟩ :=
      stS_list_ok R L s₁ hal hnd.2 fun y hy => hin y (List.mem_cons_of_mem _ hy)
    have hsep : ∀ k, k ≠ x.1 → k < 2 ^ 58 → slotW s₁ k = slotW s k := fun k hk hk58 =>
      Mem.readW_writeW_sep (slot_sep _ (by omega) (by omega) hk) (by decide)
    refine ⟨s', ?_, g', rd', wr', ?_, fun k hk hk58 => ?_, fun y hy => ?_⟩
    · rw [List.map_cons, ← List.singleton_append, Interleave.runBlock_append, stS_ok s x.2 hx.1 hal hx.2.1,
        Option.bind_some]
      exact e'
    · exact ((Frame.refl _ _).writeW (List.mem_singleton_self R) _ hx.2.2).trans f'
    · simp only [List.map_cons, List.mem_cons, not_or] at hk
      rw [o' k hk.2 hk58]; exact hsep k hk.1 hk58
    · rcases List.mem_cons.mp hy with rfl | hy
      · rw [o' _ hnd.1 (by omega)]; exact Mem.readW_writeW_self64 _ _ _
      · exact v' y hy

/-! ## Saving and restoring the callee-saved registers -/

/-- The callee-saved registers the code uses, in the order of `savedOffs`. -/
def sreg (i : Nat) : Reg := ((savedOffs.map (·.1))[i]?).getD .s0

theorem savedOffs_eq : savedOffs = (List.range 12).map fun i => (sreg i, 8 * i) := by decide

theorem saveRegs_eq : saveRegs = slotAddr t0 savedSlot ++ Spill.saveCode t0 savedOffs := rfl

theorem restoreRegs_eq : restoreRegs = slotAddr t0 savedSlot ++ Spill.restoreCode t0 savedOffs := rfl

theorem savedOffs_ho : ∀ p ∈ savedOffs, p.2 % 8 = 0 ∧ p.2 < 2048 := by decide

/-- The saved registers are in their slots. -/
def Saved (s₀ : State) (b : Addr) (m : Mem) : Prop :=
  ∀ i < 12, m.readW (wordAddr b (savedSlot + i)) 64 = s₀.gpr (sreg i)

theorem sreg_ne_sb : ∀ i < 12, sreg i ≠ sb := by decide
theorem sreg_ne_t0 : ∀ i < 12, sreg i ≠ t0 := by decide

theorem saved_addr (b : Addr) (i : Nat) :
    wordAddr b (savedSlot + i) = b + BitVec.ofNat 64 (8 * savedSlot) + BitVec.ofNat 64 (8 * i) := by
  rw [wordAddr, addr_add, show 8 * savedSlot + 8 * i = 8 * (savedSlot + i) by omega]

theorem save_ok {s : State} {b : Addr} (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b)
    (hal : b.toNat % 8 = 0) :
    ∃ s', runBlock isa saveRegs s = some s' ∧ Saved s b s'.mem ∧ (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨b, 8 * slots⟩] s.mem s'.mem ∧
      (∀ k, k < savedSlot → slotW s' k = slotW s k) ∧
      Frame [⟨b + BitVec.ofNat 64 (8 * savedSlot), 96⟩] s.mem s'.mem := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := slotAddr_ok s t0 savedSlot
  rw [hb] at r₁
  have hal₁ : (s₁.gpr t0).toNat % 8 = 0 := by rw [r₁]; exact Spill.al8 hal (by decide)
  obtain ⟨s', e', st⟩ := Interleave.runBlock_of_WP (Spill.save_wp (b := t0) (l := savedOffs) hal₁
    savedOffs_ho fun p hp => by
      rw [wr₁, r₁, addr_add]
      have := savedOffs_ho p hp
      have h2 : p.2 + 8 ≤ 96 := by revert p; decide
      exact ⟨_, hw, VG.Offset.contains_base b (by rw [slots_eq, savedSlot_eq]; omega)
        (by rw [savedSlot_eq]; omega)⟩)
  have g' : ∀ r, r ≠ t0 → s'.gpr r = s.gpr r := fun r hr => by rw [st.gpr, o₁ r hr]
  have hfr : Frame [⟨b + BitVec.ofNat 64 (8 * savedSlot), 96⟩] s.mem s'.mem := by
    rw [st.mem, ← r₁, m₁]
    exact Spill.saveMem_frame_base (by decide) (by decide) _ _ _
  refine ⟨s', by rw [saveRegs_eq, Interleave.runBlock_append, e₁, Option.bind_some]; exact e',
    fun i hi => ?_, g', by rw [st.rd, rd₁], by rw [st.wr, wr₁], hfr.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩,
    fun k hk => ?_, hfr⟩
  · have := Spill.saveMem_saved (l := savedOffs) (by decide) s₁.mem (s₁.gpr t0) s₁.gpr (sreg i, 8 * i)
      (by rw [savedOffs_eq]; exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    rw [← st.mem, r₁] at this
    rw [saved_addr, this, o₁ _ (sreg_ne_t0 i hi)]
  · simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.sub_base b (by rw [slots_eq, savedSlot_eq])
  · rw [savedSlot_eq] at hk
    rw [slotW, slotW, g' _ sb_ne_t0, hb]
    refine hfr.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    rw [wordAddr]
    exact VG.Offset.disjoint b (Or.inl (by rw [savedSlot_eq]; omega)) (by omega) (by rw [savedSlot_eq]; omega)

theorem restore_ok {s₀ s : State} {b : Addr} (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b)
    (hal : b.toNat % 8 = 0) (hs : Saved s₀ b s.mem) :
    ∃ s', runBlock isa restoreRegs s = some s' ∧ (∀ i < 12, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (∀ r, (∀ i < 12, r ≠ sreg i) → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := slotAddr_ok s t0 savedSlot
  rw [hb] at r₁
  obtain ⟨s', e', rs⟩ := Interleave.runBlock_of_WP (Spill.restore_wp (b := t0) (l := savedOffs)
    (g := s₀.gpr) (Spill.al8 hal (by decide)) r₁ savedOffs_ho (by decide)
    (fun p hp => by
      rw [rd₁, wr₁, addr_add]
      have := savedOffs_ho p hp
      have h2 : p.2 + 8 ≤ 96 := by revert p; decide
      exact ⟨_, List.mem_append_right _ hw, VG.Offset.contains_base b (by rw [slots_eq, savedSlot_eq]; omega)
        (by rw [savedSlot_eq]; omega)⟩)
    (fun p hp => by
      rw [savedOffs_eq] at hp
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
      have hi := List.mem_range.mp hi
      rw [m₁, ← saved_addr]; exact hs i hi))
  refine ⟨s', by rw [restoreRegs_eq, Interleave.runBlock_append, e₁, Option.bind_some]; exact e',
    fun i hi => rs.gpr (sreg i, 8 * i) (by rw [savedOffs_eq]; exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩),
    fun r hr h0 => ?_, by rw [rs.mem, m₁], by rw [rs.rd, rd₁], by rw [rs.wr, wr₁]⟩
  rw [rs.other r ?_, o₁ r h0]
  rw [savedOffs_eq, List.map_map]
  simp only [List.mem_map, List.mem_range, Function.comp_def, not_exists, not_and]
  exact fun i hi h => hr i hi h.symm

/-! ## Constants -/

/-- `li64 t0, v` (through `t1`); `sd t0, 8 k(sb)`. -/
theorem setOne_ok {s : State} {b : Addr} {k : Nat} (v : BitVec 64) (hb : s.gpr sb = b) (hk : 8 * k < 2048)
    (hal : b.toNat % 8 = 0) (hw : InRegions s.wr (wordAddr b k) 8) :
    ∃ s', runBlock isa (li64 t0 t1 v ++ [stS k t0]) s = some s' ∧ s'.mem = s.mem.writeW (wordAddr b k) v ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, h₁⟩ := Interleave.runBlock_of_WP (ByteLoad.li64_ok (s := s) (d := t0) (tmp := t1) (by decide) v)
  subst h₁
  let s₁ := (s.write t1 (sext32 (v.setWidth 32))).write t0 v
  have hb₁ : s₁.gpr sb = b := by
    rw [RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide), hb]
  refine ⟨{ s₁ with mem := s₁.mem.writeW (wordAddr (s₁.gpr sb) k) (s₁.gpr t0) }, ?_, ?_,
    fun r h0 h1 => ?_, rfl, rfl⟩
  · rw [Interleave.runBlock_append, e₁, Option.bind_some]
    exact stS_ok _ t0 hk (by rw [hb₁]; exact hal) (by rw [hb₁]; exact hw)
  · show s₁.mem.writeW (wordAddr (s₁.gpr sb) k) (s₁.gpr t0) = _
    rw [hb₁, RegUpd.gpr_write_self]; rfl
  · show s₁.gpr r = _
    rw [RegUpd.gpr_write_of_ne _ _ h0, RegUpd.gpr_write_of_ne _ _ h1]

theorem setSlots_ok (ms : List (Nat × BitVec 64)) {s : State} {b : Addr} (hb : s.gpr sb = b)
    (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hal : b.toNat % 8 = 0) (hk : ∀ kv ∈ ms, kv.1 < tableSlot)
    (hnd : (ms.map (·.1)).Nodup) :
    ∃ s', runBlock isa (setSlots ms) s = some s' ∧ (∀ kv ∈ ms, slotW s' kv.1 = kv.2) ∧
      (∀ k < slots, k ∉ ms.map (·.1) → slotW s' k = slotW s k) ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b, 8 * tableSlot⟩] s.mem s'.mem := by
  induction ms generalizing s with
  | nil => exact ⟨s, rfl, by simp, fun _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | cons kv ms ih =>
    have hk0 : kv.1 < tableSlot := hk kv List.mem_cons_self
    rw [tableSlot_eq] at hk0
    obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := setOne_ok (k := kv.1) kv.2 hb (by omega) hal ⟨_, hw, by
      rw [wordAddr]; exact VG.Offset.contains_base b (by rw [slots_eq]; omega) (by omega)⟩
    have hb₁ : s₁.gpr sb = b := by rw [g₁ _ sb_ne_t0 sb_ne_t1, hb]
    obtain ⟨s', e', v', k', g', rd', wr', f'⟩ := ih (s := s₁) hb₁ (by rw [wr₁]; exact hw)
      (fun kv h => hk kv (List.mem_cons_of_mem _ h)) (List.nodup_cons.mp hnd).2
    have hnot : kv.1 ∉ ms.map (·.1) := (List.nodup_cons.mp hnd).1
    have hslot : ∀ k < slots, slotW s₁ k = if k = kv.1 then kv.2 else slotW s k := fun k hk' => by
      simp only [slotW, hb₁, hb, m₁]
      split
      · rename_i h; subst h; exact Mem.readW_writeW_self64 _ _ _
      · rename_i h
        rw [slots_eq] at hk'
        exact Mem.readW_writeW_sep (slot_sep b (by omega) (by omega) h) (by decide)
    refine ⟨s', by
      rw [show setSlots (kv :: ms) = (li64 t0 t1 kv.2 ++ [stS kv.1 t0]) ++ setSlots ms from rfl,
        Interleave.runBlock_append, e₁, Option.bind_some, e'], fun x hx => ?_, fun k hk' hn => ?_,
      fun r h0 h1 => by rw [g' r h0 h1, g₁ r h0 h1], by rw [rd', rd₁], by rw [wr', wr₁], ?_⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · rw [k' _ (by rw [slots_eq]; omega) hnot, hslot _ (by rw [slots_eq]; omega), ite_eq_left rfl]
      · exact v' x hx
    · simp only [List.map_cons, List.mem_cons, not_or] at hn
      rw [k' k hk' hn.2, hslot k hk', ite_eq_right hn.1]
    · refine Frame.trans (fun x hx => ?_) f'
      rw [m₁]
      simp only [Mem.writeW, Mem.write, wordAddr]
      exact ite_eq_right fun h => hx _ (List.mem_singleton_self _) (VG.Offset.sub_base b
        (show 8 * kv.1 + 8 ≤ 8 * tableSlot by rw [tableSlot_eq]; omega) _ (by simp only [Region.Contains]; omega))

end VG.Proof.Sm4.RISCV64
