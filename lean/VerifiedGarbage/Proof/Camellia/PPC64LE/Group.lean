module

public import VerifiedGarbage.Proof.Camellia.Common
public import VerifiedGarbage.Proof.Camellia.PPC64LE.Keys
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
public import VerifiedGarbage.Impl.Camellia.PPC64LE.Ecb
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Camellia.PPC64LE.Crypt8

/-! ### `Camellia.PPC64LE.Prologue`, which this module and modules that import it used -/

section

/-!
# Camellia's prologue and epilogue on PPC64LE

Saving and restoring the callee-saved registers `r14`–`r31` in their slots
(`save_ok`, `restore_ok`, by symbolic execution of the stores and loads),
and setting the masks of the layers (`setSlots_ok`, by evaluation: the
masks are constants of the lane domain).
-/

@[expose] public section

namespace VG.Proof.Camellia.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Bitslice VG.Impl.Camellia.PPC64LE
open VG.Impl.Aes.PPC64LE (q sb t0 t1 kp movR ldS stS)

theorem savedSlot_eq : savedSlot = 368 := rfl

/-! ## Saving and restoring the callee-saved registers -/

/-- The callee-saved registers the code uses, in the order of `savedRegs`. -/
def sreg (i : Nat) : Reg := ((savedRegs.map (·.1))[i]?).getD .r14

theorem savedRegs_eq : savedRegs = (List.range 18).map fun i => (sreg i, savedSlot + i) := by decide

/-- The saved registers are in their slots. -/
def Saved (s₀ : State) (b : Addr) (m : Mem) : Prop :=
  ∀ i < 18, m.readW (wordAddr b (savedSlot + i)) 64 = s₀.gpr (sreg i)

/-- The saved registers' slots. -/
def savedRegion (b : Addr) : Region := ⟨b + BitVec.ofNat 64 (8 * savedSlot), 144⟩

theorem sreg_ne_sb : ∀ i < 18, sreg i ≠ sb := by decide

theorem save_ok {s : State} {b : Addr} (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b) :
    ∃ s', runBlock isa saveRegs s = some s' ∧ Saved s b s'.mem ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [savedRegion b] s.mem s'.mem ∧
      ∀ k, (k < savedSlot ∨ savedSlot + 18 ≤ k) → k < 2 ^ 58 → slotW s' k = slotW s k := by
  let L : List (Nat × Reg) := (List.range 18).map fun i => (savedSlot + i, sreg i)
  have hL : saveRegs = L.map fun x => stS x.1 x.2 := by
    rw [saveRegs, savedRegs_eq]; simp only [L, List.map_map]; rfl
  have hslots : L.map (·.1) = (List.range 18).map fun i => savedSlot + i := by
    simp only [L, List.map_map]; rfl
  rw [slots_eq] at hw
  obtain ⟨s', e', g', rd', wr', f', o', v'⟩ := stS_list_ok (savedRegion b) L s (by rw [hslots]; decide)
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      refine ⟨by rw [savedSlot_eq]; omega, ⟨_, hw, ?_⟩, ?_⟩
      · rw [hb]; exact VG.Offset.contains_base b (by rw [savedSlot_eq]; omega) (by rw [savedSlot_eq]; omega)
      · rw [hb, savedRegion, wordAddr]
        exact VG.Offset.contains _ (by omega_using []) (by omega) (by rw [savedSlot_eq]; omega_using []))
  refine ⟨s', by rw [hL]; exact e', fun i hi => ?_, g', rd', wr', f', fun k hk hk' => o' k ?_ hk'⟩
  · have := v' (savedSlot + i, sreg i) (by simp only [L, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩)
    simp only [slotW, g', hb] at this
    exact this
  · rw [hslots]
    simp only [List.mem_map, List.mem_range, not_exists, not_and]
    intro i hi h; omega_using [hk, hi, h]

theorem restore_ok {s₀ s : State} {b : Addr} (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b)
    (hs : Saved s₀ b s.mem) :
    ∃ s', runBlock isa restoreRegs s = some s' ∧ (∀ i < 18, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (∀ r, (∀ i < 18, r ≠ sreg i) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  let L : List (Reg × Nat) := (List.range 18).map fun i => (sreg i, savedSlot + i)
  have hL : restoreRegs = L.map fun x => ldS x.1 x.2 := by
    rw [restoreRegs, savedRegs_eq]
  have hregs : L.map (·.1) = (List.range 18).map sreg := by simp only [L, List.map_map]; rfl
  rw [slots_eq] at hw
  obtain ⟨s', e', m', rd', wr', o', v'⟩ := ldS_list_ok L s
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx; exact sreg_ne_sb i hi)
    (by rw [hregs]; decide)
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      refine ⟨by rw [savedSlot_eq]; omega, ⟨_, List.mem_append_right _ hw, ?_⟩⟩
      rw [hb]; exact VG.Offset.contains_base b (by rw [savedSlot_eq]; omega) (by rw [savedSlot_eq]; omega))
  refine ⟨s', by rw [hL]; exact e', fun i hi => ?_, fun r hr => o' r ?_, m', rd', wr'⟩
  · rw [v' (sreg i, savedSlot + i) (by simp only [L, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩), slotW, hb]
    exact hs i hi
  · rw [hregs]
    simp only [List.mem_map, List.mem_range, not_exists, not_and]
    exact fun i hi h => hr i hi h.symm

/-! ## The masks -/

/-- The masks' slots, below the table. -/
def maskCfg : Cfg := { base := sb, slots := keySlot, ext := sb, exts := 0 }

def maskPost (e : Env (Nat × Nat)) : Bool := layerMasks.all fun kv => e.slot kv.1 == some (kv.2.toNat, 0)

theorem setSlots_check :
    check (lanes 64 1) maskCfg (fun _ => none) (setSlots layerMasks) (linEnvG [] [] []) maskPost = true := by
  decide +kernel

theorem setSlots_ok {s : State} {b : Addr} (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b) :
    ∃ s', runBlock isa (setSlots layerMasks) s = some s' ∧ MasksOk s' ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b, 8 * keySlot⟩] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ setSlots_check
  have hok : Ok maskCfg s :=
    Ok.of_region hw hb.symm (by show 8 * keySlot ≤ 8 * slots; rw [keySlot_eq, slots_eq]; omega_using [])
      (by show 8 * slots < 2 ^ 64; rw [slots_eq]; decide) rfl
  have hrel : Rel (LaneRel 1 0) maskCfg (fun _ => none) (linEnvG [] [] []) s := by
    refine ⟨fun r a h => ?_, fun k a _ h => ?_, fun _ _ _ h => ?_, fun _ _ h => ?_⟩ <;>
      simp [linEnvG] at h
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  have hall : ∀ r, r ≠ t0 → ((setSlots layerMasks).all fun i => dstOf i != some r) = true := by
    intro r hr
    have : ((setSlots layerMasks).all fun i => dstOf i == none || dstOf i == some t0) = true := by
      decide +kernel
    refine List.all_eq_true.mpr fun i hi => ?_
    have h := List.all_eq_true.mp this i hi
    rcases hd : dstOf i with _ | d
    · rfl
    · rw [hd] at h
      have hdt : d = t0 := by simpa using h
      subst hdt
      simpa using fun h' => hr h'.symm
  refine ⟨s', hs', fun kv hkv => ?_, fun r hr => p.other r (by simp [hall r hr]), p.rd, p.wr, ?_⟩
  · have h := List.all_eq_true.mp hpost kv hkv
    simp only [beq_iff_eq] at h
    have hr := p.rel.slot kv.1 _ (by simp only [maskCfg]; exact mask_lt hkv) h
    simp only [maskCfg] at hr
    apply BitVec.eq_of_getLsbD_eq
    intro q hq
    show (s'.mem.readW (wordAddr (s'.gpr sb) kv.1) 64).getLsbD q = _
    rw [hr.2 q hq, par_zero, Bool.xor_false]
    rfl
  · have := p.frame
    simpa [slotRegion, maskCfg, hb] using this

end VG.Proof.Camellia.PPC64LE

end

end

/-! ### `Camellia.PPC64LE.Copy`, which only this module used -/

section

/-!
# Copying blocks on PPC64LE

As on x86-64: `copyBlocks_wp`: the loop `copyBlocks` copies `c ≥ 1` blocks
of 16 bytes from `r9` to `r10` (areas that do not overlap), through `t0`,
counting down `r11`, and changes nothing else in memory.
-/

@[expose] public section

namespace VG.Proof.Camellia.PPC64LE

open VG VG.PPC64LE VG.Impl.Camellia.PPC64LE
open VG.Impl.Aes.PPC64LE (t0)

/-- `ldr t0, [r9, #d]; str t0, [r10, #d]`. -/
theorem copyWord_ok (s : State) {d : Nat} (hd : d % 8 = 0 ∧ d < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r9 + BitVec.ofNat 64 d) 8)
    (hw : InRegions s.wr (s.gpr .r10 + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa [.load .d t0 .r9 d, .store .d t0 .r10 d] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .r10 + BitVec.ofNat 64 d) (s.mem.readW (s.gpr .r9 + BitVec.ofNat 64 d) 64) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let v := s.mem.readW (s.gpr .r9 + BitVec.ofNat 64 d) 64
  let s₁ := s.write t0 v
  obtain h15 : s₁.gpr .r10 = s.gpr .r10 := RegUpd.gpr_write_of_ne _ _ (by decide)
  obtain ht : s₁.gpr t0 = v := RegUpd.gpr_write_self _ _ _
  refine ⟨{ s₁ with mem := s₁.mem.writeW (s₁.gpr .r10 + BitVec.ofNat 64 d) (s₁.gpr t0) }, ?_, ?_,
    fun r hr => RegUpd.gpr_write_of_ne _ _ hr, rfl, rfl⟩
  · have e1 : runBlock isa [.load .d t0 .r9 d] s = some s₁ := by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec_ld hd hr]; rfl
    obtain e2 : runBlock isa [.store .d t0 .r10 d] s₁ =
        some { s₁ with mem := s₁.mem.writeW (s₁.gpr .r10 + BitVec.ofNat 64 d) (s₁.gpr t0) } := by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec_std hd (by rw [h15]; exact hw)]
    rw [show ([.load .d t0 .r9 d, .store .d t0 .r10 d] : List Instr) =
      [.load .d t0 .r9 d] ++ [.store .d t0 .r10 d] from rfl, runBlock_append', e1, Option.bind_some, e2]
  · show s.mem.writeW (s₁.gpr .r10 + BitVec.ofNat 64 d) (s₁.gpr t0) = _
    rw [h15, ht]

/-- Copying, after `j` of `c` blocks. -/
structure CopyInv (A B : Addr) (c : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  src : s.gpr .r9 = A + BitVec.ofNat 64 (16 * j)
  dst : s.gpr .r10 = B + BitVec.ofNat 64 (16 * j)
  cnt : s.gpr .r11 = BitVec.ofNat 64 (c - j)
  copied : ∀ t < 16 * j, s.mem (B + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t)
  frame : Frame [⟨B, 16 * c⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ t0 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem copyBlocks_bounded_wp {A B : Addr} {c : Nat} {s₀ : State} (hc : 0 < c) (hcBound : c ≤ 17)
    (hA : ∀ t < 2 * c, InRegions (s₀.rd ++ s₀.wr) (A + BitVec.ofNat 64 (8 * t)) 8)
    (hB : ∀ t < 2 * c, InRegions s₀.wr (B + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨A, 16 * c⟩ ⟨B, 16 * c⟩) (hs : CopyInv A B c s₀ 0 s₀) :
    WP isa copyBlocks s₀ (CopyInv A B c s₀ c) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = c - j ∧ j < c ∧ CopyInv A B c s₀ j s)
    (fun n s hs => ?_) c s₀ ⟨0, by omega_arith, hc, hs⟩
  obtain ⟨j, rfl, hj, hi⟩ := hs
  obtain hA0 := hA (2 * j) (by omega_arith)
  obtain hA1 := hA (2 * j + 1) (by omega_arith)
  obtain hB0 := hB (2 * j) (by omega_arith)
  obtain hB1 := hB (2 * j + 1) (by omega_arith)
  have hfA : Frame [⟨B, 16 * c⟩] s₀.mem s.mem := hi.frame
  obtain hAs : ∀ t < 16 * c, s.mem (A + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t) := fun t ht =>
    hfA.bytes (R := ⟨A, 16 * c⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep)
      (by simp only; omega_arith) ht
  obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := copyWord_ok s (d := 0) (by decide)
    (by rw [hi.rd, hi.wr, hi.src, addr_add, show 16 * j + 0 = 8 * (2 * j) by omega_arith]; exact hA0)
    (by rw [hi.wr, hi.dst, addr_add, show 16 * j + 0 = 8 * (2 * j) by omega_arith]; exact hB0)
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := copyWord_ok s₁ (d := 8) (by decide)
    (by rw [rd₁, wr₁, hi.rd, hi.wr, g₁ _ (by decide), hi.src, addr_add,
      show 16 * j + 8 = 8 * (2 * j + 1) by omega_arith]; exact hA1)
    (by rw [wr₁, hi.wr, g₁ _ (by decide), hi.dst, addr_add, show 16 * j + 8 = 8 * (2 * j + 1) by omega_arith]; exact hB1)
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := addI_ok s₂ .r9 .r9 (imm := 16) (by decide)
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := addI_ok s₃ .r10 .r10 (imm := 16) (by decide)
  obtain ⟨s₅, e₅, c₅, o₅, m₅, rd₅, wr₅⟩ := subI_ok s₄ .r11 .r11 (imm := 1) (by decide)
  refine WP.of_runBlock ⟨s₅, by
    rw [show ([Instr.load .d t0 .r9 0, .store .d t0 .r10 0, .load .d t0 .r9 8, .store .d t0 .r10 8,
      .addi .r9 .r9 16, .addi .r10 .r10 16, .subi .r11 .r11 1] : List Instr) =
      [.load .d t0 .r9 0, .store .d t0 .r10 0] ++ ([.load .d t0 .r9 8, .store .d t0 .r10 8] ++
      ([.addi .r9 .r9 16] ++ ([.addi .r10 .r10 16] ++ [.subi .r11 .r11 1]))) from rfl,
      runBlock_append', e₁, Option.bind_some, runBlock_append', e₂, Option.bind_some, runBlock_append', e₃,
      Option.bind_some, runBlock_append', e₄, Option.bind_some, e₅], ?_⟩
  obtain hn : 16 * c < 2 ^ 64 := by omega_arith
  obtain r1 : s₁.gpr .r10 = B + BitVec.ofNat 64 (16 * j) := by rw [g₁ _ (by decide), hi.dst]
  obtain a1 : s₁.gpr .r9 = A + BitVec.ofNat 64 (16 * j) := by rw [g₁ _ (by decide), hi.src]
  obtain hm : s₅.mem = (s₁.mem.writeW (B + BitVec.ofNat 64 (16 * j + 8))
      (s₁.mem.readW (A + BitVec.ofNat 64 (16 * j + 8)) 64)) := by
    rw [m₅, m₄, m₃, m₂, r1, a1, addr_add, addr_add]
  obtain hm₁ : s₁.mem = s.mem.writeW (B + BitVec.ofNat 64 (16 * j))
      (s.mem.readW (A + BitVec.ofNat 64 (16 * j)) 64) := by
    rw [m₁, hi.dst, hi.src, addr_add, addr_add, Nat.add_zero]
  -- `s₁` and `s` agree on `A`'s area.
  obtain hA₁ : ∀ t < 16 * c, s₁.mem (A + BitVec.ofNat 64 t) = s.mem (A + BitVec.ofNat 64 t) := fun t ht => by
    rw [hm₁, writeW_readW_apply, ite_eq_right (not_in_of_disjoint hsep ht (by omega_arith) hn)]
  obtain hc₅ : s₅.gpr .r11 = BitVec.ofNat 64 (c - (j + 1)) := by
    rw [c₅, o₄ _ (by decide), o₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hi.cnt,
      VG.Offset.ofNat_sub_ofNat (by omega_arith), show c - j - 1 = c - (j + 1) by omega_arith]
  obtain hinv : CopyInv A B c s₀ (j + 1) s₅ := by
    refine ⟨?_, ?_, hc₅, fun t ht => ?_, hi.frame.trans fun x hx => ?_, fun r h1 h2 h3 h4 => ?_,
      by rw [rd₅, rd₄, rd₃, rd₂, rd₁, hi.rd], by rw [wr₅, wr₄, wr₃, wr₂, wr₁, hi.wr]⟩
    · rw [o₅ _ (by decide), o₄ _ (by decide), a₃, g₂ _ (by decide), a1, addr_add,
        show 16 * j + 16 = 16 * (j + 1) by omega_arith]
    · rw [o₅ _ (by decide), a₄, o₃ _ (by decide), g₂ _ (by decide), r1, addr_add,
        show 16 * j + 16 = 16 * (j + 1) by omega_arith]
    · rw [hm, writeW_readW_apply]
      by_cases h8 : 16 * j + 8 ≤ t
      · rw [ite_eq_left (by rw [off_sub_toNat B h8 (by omega_arith)]; omega_arith), off_sub_toNat B h8 (by omega_arith), addr_add,
          show 16 * j + 8 + (t - (16 * j + 8)) = t by omega_arith, hA₁ t (by omega_arith), hAs t (by omega_arith)]
      · rw [ite_eq_right (off_sub_not B (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith)), hm₁,
          writeW_readW_apply]
        by_cases h0 : 16 * j ≤ t
        · rw [ite_eq_left (by rw [off_sub_toNat B h0 (by omega_arith)]; omega_arith), off_sub_toNat B h0 (by omega_arith), addr_add,
            show 16 * j + (t - 16 * j) = t by omega_arith, hAs t (by omega_arith)]
        · rw [ite_eq_right (off_sub_not B (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith))]
          exact hi.copied t (by omega_arith)
    · have hout : ∀ e, e + 8 ≤ 16 * c → ¬ (x - (B + BitVec.ofNat 64 e)).toNat < 8 := fun e he h =>
        hx _ (List.mem_singleton_self _) (VG.Offset.sub_base B he _ (by simp only [Region.Contains]; omega_arith))
      rw [hm, writeW_readW_apply, ite_eq_right (hout _ (by omega_arith)), hm₁, writeW_readW_apply,
        ite_eq_right (hout _ (by omega_arith))]
    · rw [o₅ r h3, o₄ r h2, o₃ r h1, g₂ r h4, g₁ r h4, hi.regs r h1 h2 h3 h4]
  obtain hz : (s₅.gpr .r11 == 0) = decide (c - (j + 1) = 0) := by
    rw [hc₅, show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, Bool.eq_iff_iff, beq_iff_eq,
      decide_eq_true_iff]
    constructor
    · intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega_arith
    · intro h; rw [h]
  by_cases hl : j + 1 = c
  · refine .inl ⟨(eval_nonzero s₅ .r11).trans (by rw [hz]; simp; omega_arith),
      by rw [show j + 1 = c from hl] at hinv; exact hinv⟩
  · exact .inr ⟨(eval_nonzero s₅ .r11).trans (by rw [hz]; simp; omega_arith), c - (j + 1), by omega_arith, j + 1, rfl,
      by omega_arith, hinv⟩

/-- The original eight-block interface used by the parallel block modes. -/
theorem copyBlocks_wp {A B : Addr} {c : Nat} {s₀ : State} (hc : 0 < c) (hc8 : c ≤ 8)
    (hA : ∀ t < 2*c, InRegions (s₀.rd ++ s₀.wr) (A+BitVec.ofNat 64 (8*t)) 8)
    (hB : ∀ t < 2*c, InRegions s₀.wr (B+BitVec.ofNat 64 (8*t)) 8)
    (hsep : Region.Disjoint ⟨A,16*c⟩ ⟨B,16*c⟩) (hs : CopyInv A B c s₀ 0 s₀) :
    WP isa copyBlocks s₀ (CopyInv A B c s₀ c) :=
  copyBlocks_bounded_wp hc (by omega_using [hc8]) hA hB hsep hs

end VG.Proof.Camellia.PPC64LE

end

end


/-!
# A group of blocks of Camellia ECB on PPC64LE

`dataGroup_wp`: one iteration of the data loop copies the group's blocks
(eight, or the last one to seven) to the tail buffer, transforms it
(`crypt8_ok`, which keeps the data pointer, the blocks left and the
postwhitening's address in `r5`–`r7`), copies the blocks back and steps to
the next group.
-/

@[expose] public section

namespace VG.Proof.Camellia.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.Camellia.PPC64LE
open VG.Impl.Aes.PPC64LE (q sb t0 t1 kp movR ldS stS shrI)

/-! ## Small blocks -/

theorem lsr3_beq {v : Nat} (hv : v < 2 ^ 64) : (BitVec.ofNat 64 v >>> 3 == 0) = decide (v < 8) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.shiftRight_eq_div_pow] at this
    simp at this
    omega_arith
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.shiftRight_eq_div_pow]
    simp
    omega_arith

/-- `r12 := min(r6, 8)`. -/
theorem groupCount_wp {s : State} {v : Nat} (hr : s.gpr .r6 = BitVec.ofNat 64 v) (hv : v < 2 ^ 64) :
    WP isa groupCount s fun s' => s'.gpr .r12 = BitVec.ofNat 64 (min v 8) ∧
      (∀ r, r ≠ .r12 → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.write t0 (s.gpr .r6 >>> 3)
  obtain e₁ : runBlock isa [shrI t0 .r6 3] s = some s₁ := by
    simp only [shrI, runBlock_cons, runStep_some, runBlock_nil, exec_lsr_d (show 3 < 64 by decide)]; rfl
  obtain t₁ : s₁.gpr t0 = BitVec.ofNat 64 v >>> 3 := by
    rw [RegUpd.gpr_write_self, hr]
  obtain o₁ : ∀ r, r ≠ t0 → s₁.gpr r = s.gpr r := fun r hr => RegUpd.gpr_write_of_ne _ _ hr
  unfold groupCount
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.ite (decide (8 ≤ v)) ((eval_nonzero s₁ t0).trans (by rw [t₁, lsr3_beq hv]; by_cases h : v < 8 <;> simp [h] <;> omega_arith))
    (fun h => ?_) (fun h => ?_)
  · obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := li_ok s₁ .r12 (v := 8) (by decide)
    refine WP.of_runBlock ⟨s₂, e₂, ?_, fun r h1 h2 => by rw [o₂ r h1, o₁ r h2], m₂, rd₂, wr₂⟩
    rw [r₂, Nat.min_eq_right (by simp at h; omega_arith)]
  · obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok s₁ .r12 .r6
    refine WP.of_runBlock ⟨s₂, e₂, ?_, fun r h1 h2 => by rw [o₂ r h1, o₁ r h2], m₂, rd₂, wr₂⟩
    rw [r₂, o₁ _ (by decide), hr, Nat.min_eq_left (by simp at h; omega_arith)]

/-- `tailAddr r`. -/
theorem tailAddr_ok (s : State) (r : Reg) :
    ∃ s', runBlock isa (tailAddr r) s = some s' ∧ s'.gpr r = s.gpr sb + BitVec.ofNat 64 (8 * tailSlot) ∧
      (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  addI_ok s r sb (imm := 8 * tailSlot) (by decide)

/-! ## The scratch buffer's contents -/

/-- The masks, in the memory at `b`. -/
def MasksAt (m : Mem) (b : Addr) : Prop := ∀ kv ∈ layerMasks, m.readW (wordAddr b kv.1) 64 = kv.2

theorem MasksOk.at {s : State} {b : Addr} (h : MasksOk s) (hb : s.gpr sb = b) : MasksAt s.mem b :=
  fun kv hkv => by rw [← hb]; exact h kv hkv

theorem MasksAt.ok {s : State} {b : Addr} (h : MasksAt s.mem b) (hb : s.gpr sb = b) : MasksOk s :=
  fun kv hkv => by show s.mem.readW (wordAddr (s.gpr sb) kv.1) 64 = kv.2; rw [hb]; exact h kv hkv

/-- What the data loop keeps in the scratch buffer: the masks, the table and
the saved registers. -/
structure ScrOk (s₀ : State) (b : Addr) (g : Nat) (E : Nat → BitVec 64) (m : Mem) : Prop where
  masks : MasksAt m b
  keys : ∀ i < 8 * g + 2, EntryOk m b i (E i)
  saved : Saved s₀ b m

/-- The slots `ScrOk` reads: 48–52, 96–367 and 368–377. -/
abbrev scrRegions (b : Addr) : List Region :=
  [⟨b + BitVec.ofNat 64 (8 * 48), 40⟩, ⟨b + BitVec.ofNat 64 (8 * keySlot), 8 * 272⟩,
    ⟨b + BitVec.ofNat 64 (8 * savedSlot), 144⟩]

theorem ScrOk.frame {s₀ : State} {b : Addr} {g : Nat} {E : Nat → BitVec 64} {m m' : Mem}
    (h : ScrOk s₀ b g E m) (hg : g ≤ 4) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ t ∈ scrRegions b, ∀ r ∈ rs, Region.Disjoint t r) :
    ScrOk s₀ b g E m' := by
  obtain hR : ∀ t ∈ scrRegions b, ∀ d, Region.Sub ⟨b + BitVec.ofNat 64 d, 8⟩ t →
      m'.readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 := fun t ht d hs =>
    hf.readW (Region.contains_self _ _) (fun r hr => (hd _ ht r hr).sub_left hs) (by decide)
  refine ⟨fun kv hkv => ?_, fun i hi => (h.keys i hi).congr fun j hj => ?_, fun i hi => ?_⟩
  · have hk : 48 ≤ kv.1 ∧ kv.1 < 53 := by
      simp [layerMasks] at hkv; rcases hkv with h | h | h | h | h <;> subst h <;>
        simp [evenSlot, oddSlot, m4Slot, m2Slot, m3Slot]
    rw [← h.masks kv hkv]
    exact hR _ List.mem_cons_self (8 * kv.1) (VG.Offset.sub b (by omega_arith) (by omega_arith))
  · exact hR _ (List.mem_cons_of_mem _ List.mem_cons_self) (8 * keySlot + 64 * i + 8 * j)
      (VG.Offset.sub b (by omega_arith) (by rw [keySlot_eq]; omega_arith))
  · rw [← h.saved i hi]
    exact hR _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) (8 * (savedSlot + i))
      (VG.Offset.sub b (by omega_arith) (by omega_arith))

theorem ScrOk.frame2 {s₀ : State} {b : Addr} {g : Nat} {E : Nat → BitVec 64} {m m' : Mem}
    (h : ScrOk s₀ b g E m) (hg : g ≤ 4) {rs : List Region} (hf : Frame rs m m') (hm : MasksAt m' b)
    (hd : ∀ t ∈ (scrRegions b).tail, ∀ r ∈ rs, Region.Disjoint t r) : ScrOk s₀ b g E m' := by
  obtain hR : ∀ t ∈ (scrRegions b).tail, ∀ d, Region.Sub ⟨b + BitVec.ofNat 64 d, 8⟩ t →
      m'.readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 := fun t ht d hs =>
    hf.readW (Region.contains_self _ _) (fun r hr => (hd _ ht r hr).sub_left hs) (by decide)
  refine ⟨hm, fun i hi => (h.keys i hi).congr fun j hj => ?_, fun i hi => ?_⟩
  · exact hR _ List.mem_cons_self (8 * keySlot + 64 * i + 8 * j)
      (VG.Offset.sub b (by omega_arith) (by rw [keySlot_eq]; omega_arith))
  · rw [← h.saved i hi]
    exact hR _ (List.mem_cons_of_mem _ List.mem_cons_self) (8 * (savedSlot + i))
      (VG.Offset.sub b (by omega_arith) (by omega_arith))

/-! ## The data loop -/

/-- The scratch buffer at `b` and the `n` blocks at `D`. -/
structure GPre (s₀ : State) (b D : Addr) (n g : Nat) : Prop where
  scr : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr
  dat : (⟨D, 16 * n⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨D, 16 * n⟩ ⟨b, 8 * slots⟩
  fit : b.toNat + 8 * slots ≤ 2 ^ 64
  fitD : D.toNat + 16 * n ≤ 2 ^ 64
  hg : g = 3 ∨ g = 4

/-- `copyBlocks` from `r9` to `r10`, `r11` blocks, set up. -/
theorem copy_wp {s : State} {X Y : Addr} {c : Nat} (hc : 0 < c) (hc8 : c ≤ 8)
    (hx : s.gpr .r9 = X) (hy : s.gpr .r10 = Y) (hcx : s.gpr .r11 = BitVec.ofNat 64 c)
    (hX : ∀ t < 2 * c, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (8 * t)) 8)
    (hY : ∀ t < 2 * c, InRegions s.wr (Y + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨X, 16 * c⟩ ⟨Y, 16 * c⟩) :
    WP isa copyBlocks s fun s' => (∀ t < 16 * c, s'.mem (Y + BitVec.ofNat 64 t) = s.mem (X + BitVec.ofNat 64 t)) ∧
      Frame [⟨Y, 16 * c⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  WP.mono (copyBlocks_wp hc hc8 hX hY hsep ⟨by rw [hx]; simp, by rw [hy]; simp, by rw [hcx, Nat.sub_zero],
    fun t ht => by omega_arith, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl⟩)
    fun s' h => ⟨h.copied, h.frame, h.regs, h.rd, h.wr⟩

/-- The data loop, before group `k`. -/
structure GInv (s₀ : State) (b D : Addr) (n g : Nat) (E : Nat → BitVec 64) (k : Nat) (s : State) : Prop where
  base : s.gpr sb = b
  r5 : s.gpr .r5 = D + BitVec.ofNat 64 (128 * k)
  r6 : s.gpr .r6 = BitVec.ofNat 64 (n - 8 * k)
  lt : 8 * k < n
  r7 : s.gpr .r7 = b + BitVec.ofNat 64 (8 * keySlot + 512 * g)
  scr : ScrOk s₀ b g E s.mem
  data : DInv s₀.mem s.mem D n (8 * k) (outF s₀.mem D g E)
  frame : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The data loop, done. -/
structure GDone (s₀ : State) (b D : Addr) (n g : Nat) (E : Nat → BitVec 64) (s : State) : Prop where
  base : s.gpr sb = b
  scr : ScrOk s₀ b g E s.mem
  data : DInv s₀.mem s.mem D n n (outF s₀.mem D g E)
  frame : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem inRd {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

theorem dataGroup_wp {s₀ : State} {b D : Addr} {n g : Nat} {E : Nat → BitVec 64} (hp : GPre s₀ b D n g)
    {k : Nat} {s : State} (hi : GInv s₀ b D n g E k s) :
    WP isa Impl.Camellia.PPC64LE.group s fun s' => (s'.gpr .r6 = 0 ∧ GDone s₀ b D n g E s') ∨
      (s'.gpr .r6 ≠ 0 ∧ GInv s₀ b D n g E (k + 1) s') := by
  have hfit := hp.fit
  have hfitD := hp.fitD
  have hk := hi.lt
  obtain hg4 : g ≤ 4 := by rcases hp.hg with h | h <;> omega_arith
  rw [slots_eq] at hfit
  let v := n - 8 * k
  let c := min v 8
  obtain hv : v < 2 ^ 64 := by omega_arith
  obtain hc0 : 0 < c := by omega_arith
  obtain hc8 : c ≤ 8 := by omega_arith
  obtain hkc : 128 * k + 16 * c ≤ 16 * n := by omega_arith
  let A := D + BitVec.ofNat 64 (128 * k)
  let T := b + BitVec.ofNat 64 (8 * tailSlot)
  obtain hwS : (⟨b, 8 * slots⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr
  obtain hwD : (⟨D, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  obtain inT : ∀ t, t < 16 → InRegions s.wr (T + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwS, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base b (by rw [slots_eq, tailSlot_eq]; omega_arith) (by rw [tailSlot_eq]; omega_arith)
  obtain inA : ∀ t, t < 2 * c → InRegions s.wr (A + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwD, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base D (by omega_arith) (by omega_arith)
  obtain sepAT : Region.Disjoint ⟨A, 16 * c⟩ ⟨T, 16 * c⟩ :=
    (hp.sep.sub_left (VG.Offset.sub_base D (by omega_arith))).sub_right
      (VG.Offset.sub_base b (by rw [slots_eq, tailSlot_eq]; omega_arith))
  unfold Impl.Camellia.PPC64LE.group copyIn
  -- The group's blocks to the tail buffer.
  refine WP.seq (WP.seq (WP.mono (groupCount_wp hi.r6 hv) fun s₁ ⟨c₁, o₁, m₁, rd₁, wr₁⟩ => ?_))
  obtain ⟨s₂a, e₂a, r₂a, o₂a, m₂a, rd₂a, wr₂a⟩ := movR_ok s₁ .r9 .r5
  obtain ⟨s₂b, e₂b, r₂b, o₂b, m₂b, rd₂b, wr₂b⟩ := tailAddr_ok s₂a .r10
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok s₂b .r11 .r12
  obtain rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₂b, rd₂a, rd₁]
  obtain wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₂b, wr₂a, wr₁]
  obtain mem₂ : s₂.mem = s.mem := by rw [m₂, m₂b, m₂a, m₁]
  obtain g₂ : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → r ≠ t0 → s₂.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [o₂ r h3, o₂b r h2, o₂a r h1, o₁ r h4 h5]
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [runBlock_append', runBlock_append', e₂a, Option.bind_some, e₂b, Option.bind_some, e₂], ?_⟩)
  refine WP.mono (copy_wp (X := A) (Y := T) hc0 hc8
    (by rw [o₂ _ (by decide), o₂b _ (by decide), r₂a, o₁ _ (by decide) (by decide), hi.r5])
    (by rw [o₂ _ (by decide), r₂b, o₂a _ (by decide), o₁ _ (by decide) (by decide), hi.base])
    (by rw [r₂, o₂b _ (by decide), o₂a _ (by decide), c₁])
    (fun t ht => by rw [rd₂', wr₂']; exact inRd (inA t ht))
    (fun t ht => by rw [wr₂']; exact inT t (by omega_arith)) sepAT) fun s₃ ⟨cp₃, f₃, g₃, rd₃, wr₃⟩ => ?_
  obtain f₃' : Frame [⟨T, 16 * c⟩] s.mem s₃.mem := by rw [← mem₂]; exact f₃
  obtain wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂']
  obtain rd₃' : s₃.rd = s.rd := by rw [rd₃, rd₂']
  obtain g₃' : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → r ≠ t0 → s₃.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [g₃ r h1 h2 h3 h5, g₂ r h1 h2 h3 h4 h5]
  obtain base₃ : s₃.gpr sb = b := by rw [g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide), hi.base]
  obtain sc₃ : ScrOk s₀ b g E s₃.mem := by
    refine hi.scr.frame hg4 (mem₂ ▸ f₃) fun t ht r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    simp only [scrRegions, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> refine VG.Offset.disjoint b (Or.inl ?_) ?_ ?_ <;>
      (try simp only [tailSlot_eq, keySlot_eq, savedSlot_eq]) <;> omega_arith
  -- The eight blocks.
  obtain hcore : CorePre s₃ g E :=
    { scr := by rw [base₃, wr₃']; exact hwS
      fit := by rw [base₃, slots_eq]; exact hfit
      hg := hp.hg
      nk34 := by rcases hp.hg with h | h <;> omega_arith
      masks := sc₃.masks.ok base₃
      bound := by rw [g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide), hi.r7, base₃]
      keys := fun i hi' => by rw [base₃]; exact sc₃.keys i hi' }
  refine WP.seq (WP.mono (crypt8_ok hcore) fun s₅ ⟨c₅, b₅⟩ => ?_)
  obtain base₅ : s₅.gpr sb = b := by rw [c₅.base, base₃]
  obtain f₅ : Frame [⟨b, 8 * keySlot⟩, ⟨T, 128⟩] s₃.mem s₅.mem := by
    have := c₅.frame; rw [ctxRegions, base₃] at this; exact this
  have hT : T = b + BitVec.ofNat 64 (8 * tailSlot) := rfl
  obtain sc₅ : ScrOk s₀ b g E s₅.mem := by
    refine sc₃.frame2 hg4 f₅ (c₅.masks.at base₅) fun t ht r hr => ?_
    simp only [scrRegions, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at ht hr
    rcases ht with rfl | rfl <;> rcases hr with rfl | rfl
    · exact VG.Offset.disjoint_base b (by rw [keySlot_eq]) (by rw [keySlot_eq] <;> omega_arith)
    · rw [hT]; exact VG.Offset.disjoint b (Or.inl (by rw [keySlot_eq, tailSlot_eq] <;> omega_arith))
        (by rw [keySlot_eq] <;> omega_arith) (by rw [tailSlot_eq] <;> omega_arith)
    · exact VG.Offset.disjoint_base b (by rw [keySlot_eq, savedSlot_eq] <;> omega_arith) (by rw [savedSlot_eq] <;> omega_arith)
    · rw [hT]; exact VG.Offset.disjoint b (Or.inl (by rw [savedSlot_eq, tailSlot_eq]))
        (by rw [savedSlot_eq] <;> omega_arith) (by rw [tailSlot_eq] <;> omega_arith)
  obtain k₅ : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .r3 → s₅.gpr r = s₃.gpr r := fun r h1 h2 h3 => c₅.keep r h1 h2 h3
  obtain r5₅ : s₅.gpr .r5 = A := by
    rw [k₅ _ (by decide) (by decide) (by decide), g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide),
      hi.r5]
  obtain r6₅ : s₅.gpr .r6 = BitVec.ofNat 64 v := by
    rw [k₅ _ (by decide) (by decide) (by decide), g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide),
      hi.r6]
  obtain r7₅ : s₅.gpr .r7 = b + BitVec.ofNat 64 (8 * keySlot + 512 * g) := by
    rw [k₅ _ (by decide) (by decide) (by decide), g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide),
      hi.r7]
  obtain wr₅' : s₅.wr = s.wr := by rw [c₅.wr, wr₃']
  obtain rd₅' : s₅.rd = s.rd := by rw [c₅.rd, rd₃']
  -- The tail buffer back to the group's blocks.
  unfold copyOut
  refine WP.seq (WP.seq (WP.mono (groupCount_wp r6₅ hv) fun s₇ ⟨c₇, o₇, m₇, rd₇, wr₇⟩ => ?_))
  obtain ⟨s₈a, e₈a, r₈a, o₈a, m₈a, rd₈a, wr₈a⟩ := tailAddr_ok s₇ .r9
  obtain ⟨s₈b, e₈b, r₈b, o₈b, m₈b, rd₈b, wr₈b⟩ := movR_ok s₈a .r10 .r5
  obtain ⟨s₈, e₈, r₈, o₈, m₈, rd₈, wr₈⟩ := movR_ok s₈b .r11 .r12
  refine WP.seq (WP.of_runBlock ⟨s₈, by
    rw [runBlock_append', e₈a, Option.bind_some,
      show ([movR .r10 .r5, movR .r11 .r12] : List Instr) = [movR .r10 .r5] ++ [movR .r11 .r12] from rfl,
      runBlock_append', e₈b, Option.bind_some, e₈], ?_⟩)
  obtain mem₈ : s₈.mem = s₅.mem := by rw [m₈, m₈b, m₈a, m₇]
  obtain wr₈' : s₈.wr = s.wr := by rw [wr₈, wr₈b, wr₈a, wr₇, wr₅']
  obtain rd₈' : s₈.rd = s.rd := by rw [rd₈, rd₈b, rd₈a, rd₇, rd₅']
  obtain g₈ : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → r ≠ t0 → s₈.gpr r = s₅.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [o₈ r h3, o₈b r h2, o₈a r h1, o₇ r h4 h5]
  refine WP.mono (copy_wp (X := T) (Y := A) hc0 hc8
    (by rw [o₈ _ (by decide), o₈b _ (by decide), r₈a, o₇ _ (by decide) (by decide), base₅])
    (by rw [o₈ _ (by decide), r₈b, o₈a _ (by decide), o₇ _ (by decide) (by decide), r5₅])
    (by rw [r₈, o₈b _ (by decide), o₈a _ (by decide), c₇])
    (fun t ht => by rw [rd₈', wr₈']; exact inRd (inT t (by omega_arith)))
    (fun t ht => by rw [wr₈']; exact inA t ht) sepAT.symm) fun s₉ ⟨cp₉, f₉, g₉, rd₉, wr₉⟩ => ?_
  obtain g₉' : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → r ≠ t0 → s₉.gpr r = s₅.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [g₉ r h1 h2 h3 h5, g₈ r h1 h2 h3 h4 h5]
  obtain r12₉ : s₉.gpr .r12 = BitVec.ofNat 64 c := by
    rw [g₉ _ (by decide) (by decide) (by decide) (by decide), o₈ _ (by decide), o₈b _ (by decide),
      o₈a _ (by decide), c₇]
  obtain base₉ : s₉.gpr sb = b := by rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide), base₅]
  obtain r5₉ : s₉.gpr .r5 = A := by rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide), r5₅]
  obtain r6₉ : s₉.gpr .r6 = BitVec.ofNat 64 v := by
    rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide), r6₅]
  obtain r7₉ : s₉.gpr .r7 = b + BitVec.ofNat 64 (8 * keySlot + 512 * g) := by
    rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide), r7₅]
  obtain wr₉' : s₉.wr = s₀.wr := by rw [wr₉, wr₈', hi.wr]
  obtain rd₉' : s₉.rd = s₀.rd := by rw [rd₉, rd₈', hi.rd]
  -- The scratch buffer and the frame.
  obtain subS : ∀ {d l : Nat}, d + l ≤ 8 * slots → Region.Sub ⟨b + BitVec.ofNat 64 d, l⟩ ⟨b, 8 * slots⟩ :=
    fun h => VG.Offset.sub_base b h
  obtain sc₉ : ScrOk s₀ b g E s₉.mem := by
    refine (mem₈ ▸ sc₅).frame hg4 f₉ fun t ht r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    obtain hsub : Region.Sub t ⟨b, 8 * slots⟩ := by
      simp only [scrRegions, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl <;> refine subS ?_ <;> (try simp only [keySlot_eq, savedSlot_eq]) <;>
        rw [slots_eq] <;> omega_arith
    exact ((hp.sep.sub_left (VG.Offset.sub_base D (by omega_arith))).sub_right hsub).symm
  obtain fr₉ : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s.mem s₉.mem := by
    refine (((mem₂ ▸ f₃).sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((f₅.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((mem₈ ▸ f₉).sub fun r hr => ⟨⟨D, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩)))
    · simp only [List.mem_singleton] at hr; subst hr; exact subS (by rw [slots_eq, tailSlot_eq]; omega_arith)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Region.sub_prefix (by rw [slots_eq, keySlot_eq]; omega_arith)
      · exact subS (by rw [slots_eq, tailSlot_eq]; omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr; exact VG.Offset.sub_base D (by omega_arith)
  -- The blocks the eight-block code read are the group's, as on entry.
  obtain hblk : ∀ j < c, blk s₃ j = Spec.Camellia.blockAt s₀.mem (D + BitVec.ofNat 64 (16 * (8 * k + j))) := by
    intro j hj
    apply Vector.ext; intro u hu
    simp only [blk, Spec.Camellia.blockAt, Vector.getElem_ofFn]
    rw [base₃, addr_add]
    obtain ht : 16 * j + u < 16 * c := by omega_arith
    have := cp₃ (16 * j + u) ht
    rw [addr_add, show 8 * tailSlot + (16 * j + u) = 8 * tailSlot + 16 * j + u by omega_arith] at this
    rw [this, mem₂, addr_add, hi.data _ (by omega_arith), ite_eq_right (by omega_arith),
      show 128 * k + (16 * j + u) = 16 * (8 * k + j) + u by omega_arith, addr_add]
  obtain hdata : DInv s₀.mem s₉.mem D n (8 * k + c) (outF s₀.mem D g E) := by
    intro i hin
    by_cases hin1 : 128 * k ≤ i ∧ i < 128 * k + 16 * c
    · have e1 : D + BitVec.ofNat 64 i = A + BitVec.ofNat 64 (i - 128 * k) := by
        rw [addr_add, show 128 * k + (i - 128 * k) = i by omega_arith]
      rw [e1, cp₉ _ (by omega_arith), mem₈, ite_eq_left (show i < 16 * (8 * k + c) by omega_arith),
        show i / 16 = 8 * k + (i - 128 * k) / 16 by omega_arith, show i % 16 = (i - 128 * k) % 16 by omega_arith]
      obtain hj : (i - 128 * k) / 16 < c := by omega_arith
      obtain eT : T + BitVec.ofNat 64 (i - 128 * k) = s₅.gpr sb + BitVec.ofNat 64 (8 * tailSlot + 16 * ((i - 128 * k) / 16)) +
          BitVec.ofNat 64 ((i - 128 * k) % 16) := by
        rw [base₅, addr_add, addr_add, show 8 * tailSlot + 16 * ((i - 128 * k) / 16) + (i - 128 * k) % 16 =
          8 * tailSlot + (i - 128 * k) by omega_arith]
      rw [eT, ← blockAt_getD s₅.mem _ (Nat.mod_lt _ (by decide))]
      show (blk s₅ _).getD _ 0 = _
      rw [b₅ _ (by omega_arith), hblk _ hj]
      rfl
    · have hout : ∀ r ∈ [(⟨A, 16 * c⟩ : Region)], ¬ r.Contains (D + BitVec.ofNat 64 i) 1 := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact not_contains_off D (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      obtain hdS : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨b, 8 * slots⟩) →
          ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r := fun h r hr => hp.sep.sub_right (h r hr)
      rw [f₉ _ hout, mem₈,
        f₅.bytes (R := ⟨D, 16 * n⟩) (hdS fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Region.sub_prefix (by rw [slots_eq, keySlot_eq]; omega_arith)
          · exact subS (by rw [slots_eq, tailSlot_eq]; omega_arith)) (by simp only; omega_arith) hin,
        f₃'.bytes (R := ⟨D, 16 * n⟩) (hdS fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact subS (by rw [slots_eq, tailSlot_eq]; omega_arith))
          (by simp only; omega_arith) hin,
        hi.data i hin]
      by_cases h2 : i < 128 * k
      · rw [ite_eq_left (show i < 16 * (8 * k) by omega_arith), ite_eq_left (show i < 16 * (8 * k + c) by omega_arith)]
      · rw [ite_eq_right (show ¬ i < 16 * (8 * k) by omega_arith), ite_eq_right (show ¬ i < 16 * (8 * k + c) by omega_arith)]
  obtain fr : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s₉.mem := hi.frame.trans fr₉
  -- On to the next group.
  obtain ⟨s₁₀, e₁₀, r₁₀, o₁₀, m₁₀, rd₁₀, wr₁₀⟩ := subR_ok s₉ .r6 .r6 .r12
  obtain ⟨s₁₁, e₁₁, r₁₁, o₁₁, m₁₁, rd₁₁, wr₁₁⟩ := addI_ok s₁₀ .r5 .r5 (imm := 128) (by decide)
  refine WP.of_runBlock ⟨s₁₁, by
    rw [show ([Instr.sub .r6 .r6 .r12, .addi .r5 .r5 128] : List Instr) =
      [.sub .r6 .r6 .r12] ++ [.addi .r5 .r5 128] from rfl, runBlock_append', e₁₀,
      Option.bind_some, e₁₁], ?_⟩
  obtain hm : s₁₁.mem = s₉.mem := by rw [m₁₁, m₁₀]
  obtain r6₁₁ : s₁₁.gpr .r6 = BitVec.ofNat 64 (v - c) := by
    rw [o₁₁ _ (by decide), r₁₀, r6₉, r12₉, VG.Offset.ofNat_sub_ofNat (by omega_arith)]
  obtain base₁₁ : s₁₁.gpr sb = b := by rw [o₁₁ _ (by decide), o₁₀ _ (by decide), base₉]
  obtain rd₁₁' : s₁₁.rd = s₀.rd := by rw [rd₁₁, rd₁₀, rd₉']
  obtain wr₁₁' : s₁₁.wr = s₀.wr := by rw [wr₁₁, wr₁₀, wr₉']
  by_cases hlt : v ≤ 8
  · have hn : 8 * k + c = n := by omega_arith
    refine .inl ⟨by rw [r6₁₁, show v - c = 0 by omega_arith]; rfl, base₁₁, hm ▸ sc₉,
      fun i hi' => by rw [hm, hdata i hi', hn], hm ▸ fr, rd₁₁', wr₁₁'⟩
  · have hc : c = 8 := by omega_arith
    refine .inr ⟨fun h => ?_, base₁₁, ?_, ?_, by omega_arith, ?_, hm ▸ sc₉, ?_, hm ▸ fr, rd₁₁', wr₁₁'⟩
    · have hne : v - c ≠ 0 := by omega_arith
      rw [r6₁₁] at h
      apply hne
      have := congrArg BitVec.toNat h
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
    · rw [r₁₁, o₁₀ _ (by decide), r5₉, addr_add, show 128 * k + 128 = 128 * (k + 1) by omega_arith]
    · rw [r6₁₁, show v - c = n - 8 * (k + 1) by omega_arith]
    · rw [o₁₁ _ (by decide), o₁₀ _ (by decide), r7₉]
    · rw [hm, show 8 * (k + 1) = 8 * k + c by omega_arith]; exact hdata

end VG.Proof.Camellia.PPC64LE
