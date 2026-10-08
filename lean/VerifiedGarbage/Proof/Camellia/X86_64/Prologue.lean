import VerifiedGarbage.Proof.Camellia.X86_64.Copy
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.Bitslice.Sym

/-!
# Camellia ECB's prologue and epilogue on x86-64

Saving and restoring the callee-saved registers in their slots
(`save_ok`, `restore_ok`, by evaluation over names, as AES's), and setting
the masks of the layers (`setMasks_ok`).
-/

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR movS st imm setMasks)

/-! ## Saving and restoring the callee-saved registers -/

/-- The callee-saved registers the code uses, in the order of `savedRegs`. -/
def sreg : Nat → Reg
  | 0 => .rbx | 1 => .rbp | 2 => .r12 | 3 => .r13 | 4 => .r14 | _ => .r15

def saveCfg : Cfg := { base := sb, slots := tailSlot, ext := sb, exts := 0 }

def saveEnv : Env Nat :=
  { reg := fun r => (List.range 6).find? (fun i => sreg i == r), slot := fun _ => none }

def savePost (e : Env Nat) : Bool := (List.range 6).all fun i => e.slot (savedSlot + i) == some i

theorem save_check : check (names 64) saveCfg (fun _ => none) saveRegs saveEnv savePost = true := by
  decide +kernel

def restoreEnv : Env Nat :=
  { reg := fun _ => none,
    slot := fun k => if savedSlot ≤ k ∧ k < savedSlot + 6 then some (k - savedSlot) else none }

def restorePost (e : Env Nat) : Bool := (List.range 6).all fun i => e.reg (sreg i) == some i

theorem restore_check :
    check (names 64) saveCfg (fun _ => none) restoreRegs restoreEnv restorePost = true := by
  decide +kernel

theorem saveCfg_ok {s : State} {b : Addr} (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr)
    (hb : s.gpr sb = b) : Ok saveCfg s :=
  Ok.of_region hw hb.symm (by simp only [saveCfg, slots]; omega) (by simp [saveCfg, tailSlot_eq]) rfl

/-- The saved registers are in their slots. -/
def Saved (s₀ : State) (b : Addr) (m : Mem) : Prop :=
  ∀ i < 6, m.readW (wordAddr b (savedSlot + i)) 64 = s₀.gpr (sreg i)

theorem save_ok {s : State} {b : Addr} (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b) :
    ∃ s', runBlock isa saveRegs s = some s' ∧ Saved s b s'.mem ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨b, 8 * tailSlot⟩] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ save_check
  let V : Nat → BitVec 64 := fun i => s.gpr (sreg i)
  have hrel : Rel (NameRel V) saveCfg (fun _ => none) saveEnv s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), (fun _ _ hk _ => by simp [saveCfg] at hk)⟩
    simp only [saveEnv] at h
    have h1 := List.find?_some h
    simp only [beq_iff_eq] at h1; subst h1; rfl
  obtain ⟨s', hs', p⟩ := run (names_sound V) (saveCfg_ok hw hb) hrel he
  refine ⟨s', hs', fun i hi => ?_, funext fun r => p.other r ?_, p.rd, p.wr, ?_⟩
  · have := List.all_eq_true.mp hpost i (List.mem_range.mpr hi)
    simp only [beq_iff_eq] at this
    have h := p.rel.slot (savedSlot + i) i (by simp [saveCfg, savedSlot, tailSlot]; omega) this
    rw [p.base] at h
    simp only [saveCfg, hb] at h
    exact h
  · have : (saveRegs.all fun i => i.dst != some r) = true := by simp [saveRegs, savedRegs, st, Instr.dst]
    simp [this]
  · have := p.frame
    simpa [slotRegion, saveCfg, hb] using this

theorem restore_ok {s₀ s : State} {b : Addr} (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr)
    (hb : s.gpr sb = b) (hs : Saved s₀ b s.mem) :
    ∃ s', runBlock isa restoreRegs s = some s' ∧ (∀ i < 6, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (∀ r, (∀ i < 6, r ≠ sreg i) → s'.gpr r = s.gpr r) ∧ Frame [⟨b, 8 * tailSlot⟩] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ restore_check
  let V : Nat → BitVec 64 := fun i => s₀.gpr (sreg i)
  have hrel : Rel (NameRel V) saveCfg (fun _ => none) restoreEnv s := by
    refine ⟨(fun r a h => by cases h), fun k a hk h => ?_, (fun _ _ hk _ => by simp [saveCfg] at hk)⟩
    simp only [restoreEnv] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h
      rename_i hk'
      have := hs (k - savedSlot) (by omega)
      rw [show savedSlot + (k - savedSlot) = k by omega] at this
      simp only [NameRel, saveCfg, hb]
      exact this
    · cases h
  obtain ⟨s', hs', p⟩ := run (names_sound V) (saveCfg_ok hw hb) hrel he
  refine ⟨s', hs', fun i hi => ?_, fun r hr => p.other r ?_, ?_, p.rd, p.wr⟩
  · have := List.all_eq_true.mp hpost i (List.mem_range.mpr hi)
    simp only [beq_iff_eq] at this
    exact p.rel.reg _ i this
  · have : (restoreRegs.all fun i => i.dst != some r) = true := by
      have h0 := hr 0 (by omega); have h1 := hr 1 (by omega); have h2 := hr 2 (by omega)
      have h3 := hr 3 (by omega); have h4 := hr 4 (by omega); have h5 := hr 5 (by omega)
      simp only [sreg] at h0 h1 h2 h3 h4 h5
      simp [restoreRegs, savedRegs, movS, Instr.dst, Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3,
        Ne.symm h4, Ne.symm h5]
    simp [this]
  · have := p.frame
    simpa [slotRegion, saveCfg, hb] using this

/-! ## The masks -/

/-- `mov t0, v; mov [sb + 8 k], t0`. -/
theorem setOne_ok {s : State} {b : Addr} {k : Nat} (v : BitVec 64) (hb : s.gpr sb = b)
    (hw : InRegions s.wr (wordAddr b k) 8) :
    ∃ s', runBlock isa [imm t0 v, st k t0] s = some s' ∧ s'.mem = s.mem.writeW (wordAddr b k) v ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hw' : InRegions s.wr (b + BitVec.ofNat 64 (8 * k)) 8 := hw
  refine ⟨{ s.setReg t0 v with mem := s.mem.writeW (wordAddr b k) v }, ?_, rfl,
    fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl⟩
  simp only [imm, st, Impl.Aes.X86_64.slotAt, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.store64, State.ea, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ sb_ne_t0,
    RegUpd.wr_setReg, ofInt_nat, hb, hw', ite_true, RegUpd.mem_setReg]

theorem setMasks_ok (ms : List (Nat × BitVec 64)) {s : State} {b : Addr} (hb : s.gpr sb = b)
    (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hk : ∀ kv ∈ ms, kv.1 < keySlot)
    (hnd : (ms.map (·.1)).Nodup) :
    ∃ s', runBlock isa (setMasks ms) s = some s' ∧ (∀ kv ∈ ms, slotW s' kv.1 = kv.2) ∧
      (∀ k < slots, k ∉ ms.map (·.1) → slotW s' k = slotW s k) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b, 8 * keySlot⟩] s.mem s'.mem := by
  induction ms generalizing s with
  | nil => exact ⟨s, rfl, by simp, fun _ _ _ => rfl, fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | cons kv ms ih =>
    have hk0 : kv.1 < keySlot := hk kv List.mem_cons_self
    obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := setOne_ok (k := kv.1) kv.2 hb ⟨_, hw, by
      rw [wordAddr]; exact VG.Offset.contains_base b (by rw [slots_eq, keySlot_eq] at *; omega)
        (by rw [keySlot_eq] at hk0; omega)⟩
    obtain ⟨s', e', v', k', g', rd', wr', f'⟩ := ih (s := s₁) (by rw [g₁ _ sb_ne_t0, hb]) (by rw [wr₁]; exact hw)
      (fun kv h => hk kv (List.mem_cons_of_mem _ h)) (List.nodup_cons.mp hnd).2
    have hb₁ : s₁.gpr sb = b := by rw [g₁ _ sb_ne_t0, hb]
    have hnot : kv.1 ∉ ms.map (·.1) := (List.nodup_cons.mp hnd).1
    have hslot : ∀ k < slots, slotW s₁ k = if k = kv.1 then kv.2 else slotW s k := fun k hk' => by
      simp only [slotW, hb₁, hb, m₁]
      split
      · rename_i h; subst h; exact Mem.readW_writeW_self64 _ _ _
      · rename_i h
        rw [slots_eq] at hk'
        exact Mem.readW_writeW_sep (slot_sep b (by omega) (by rw [keySlot_eq] at hk0; omega) h) (by decide)
    refine ⟨s', by
      rw [show setMasks (kv :: ms) = [imm t0 kv.2, st kv.1 t0] ++ setMasks ms from rfl,
        runBlock_append', e₁, Option.bind_some, e'], fun x hx => ?_, fun k hk' hn => ?_,
      fun r hr => by rw [g' r hr, g₁ r hr], by rw [rd', rd₁], by rw [wr', wr₁], ?_⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · rw [k' _ (by rw [slots_eq, keySlot_eq] at *; omega) hnot, hslot _ (by rw [slots_eq, keySlot_eq] at *; omega),
          ite_eq_left rfl]
      · exact v' x hx
    · simp only [List.map_cons, List.mem_cons, not_or] at hn
      rw [k' k hk' hn.2, hslot k hk', ite_eq_right hn.1]
    · refine Frame.trans (fun x hx => ?_) f'
      rw [m₁]
      simp only [Mem.writeW, Mem.write, wordAddr]
      exact ite_eq_right fun h => hx _ (List.mem_singleton_self _) (VG.Offset.sub_base b
        (show 8 * kv.1 + 8 ≤ 8 * keySlot by omega) _ (by simp only [Region.Contains]; omega))

end VG.Proof.Camellia.X86_64
