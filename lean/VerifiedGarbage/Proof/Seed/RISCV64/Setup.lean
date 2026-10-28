module

public import VerifiedGarbage.Proof.Seed.RISCV64.Round
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The functions' prologue

What ECB and the key expansion share before their work (`prologue_ok`):
the scratch buffer moved to `a5`, the callee-saved registers saved in its
slots 117–128 (`Spill.save_ok` on `savedOffs`), `g16`'s masks built in its
slots 104–116 (`storeKs_ok`), and `a3` pointed to them (`Masks`). The
epilogue restores the registers with `Spill.restore_wp`.
-/

@[expose] public section

namespace VG.Proof.Seed.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.RegUpd VG.Impl.Seed.RISCV64
open VG.Impl.Aes.RISCV64 (sb t0 t1 movR stS ldS)

/-! ## The callee-saved registers -/

/-- The registers and their byte offsets in the scratch buffer. -/
def savedOffs : List (Reg × Nat) := seedSaved.map fun p => (p.1, 8 * p.2)

theorem seedSave_eq : seedSave = Spill.saveCode sb savedOffs := by
  simp only [seedSave, Spill.saveCode, savedOffs, List.map_map]; rfl

theorem seedRestore_eq : seedRestore = Spill.restoreCode sb savedOffs := by
  simp only [seedRestore, Spill.restoreCode, savedOffs, List.map_map]; rfl

theorem savedOffs_fits : Spill.Fits savedOffs := by decide

theorem savedOffs_restorable : Spill.Restorable sb savedOffs := by decide

theorem savedOffs_ho : ∀ p ∈ savedOffs, p.2 % 8 = 0 ∧ p.2 < 2048 := by decide

theorem savedOffs_range : ∀ p ∈ savedOffs, 936 ≤ p.2 ∧ p.2 + 8 ≤ 936 + 96 := by decide

/-- The registers `savedOffs` saves are the preserved ones. -/
theorem savedOffs_regs : savedOffs.map Prod.fst = RISCV64.preserved := by decide

theorem not_saved : ∀ p ∈ savedOffs, p.1 ≠ sb ∧ p.1 ≠ kb ∧ p.1 ≠ .t0 ∧ p.1 ≠ .t1 := by decide

/-! ## The masks -/

/-- The masks' slots and values. -/
def kAbs : List (Nat × BitVec 64) := gKs.map fun p => (kSlot + p.1, p.2)

theorem buildMasks_eq :
    buildMasks = kAbs.flatMap fun p => Impl.Words64.RISCV64.movImm64 t0 t1 p.2 ++ [stS p.1 t0] := by
  simp only [buildMasks, kAbs, List.flatMap_map]

theorem kAbs_nodup : (kAbs.map Prod.fst).Nodup := by decide

theorem kAbs_range : ∀ p ∈ kAbs, kSlot ≤ p.1 ∧ p.1 < kSlot + 13 := by decide

theorem slot_al {B : Addr} (hB : B.toNat % 8 = 0) {k : Nat} (hk : k < 256) :
    (Straight.wordAddr B k).toNat % 8 = 0 :=
  Straight.wordAddr_al hB k (by omega)

/-- The slots of `ks`. -/
def ksRegions (b : Addr) (ks : List (Nat × BitVec 64)) : List Region :=
  ks.map fun p => ⟨Straight.wordAddr b p.1, 8⟩

/-- Build the masks `ks` (slots in `[kSlot, kSlot + 13)`) through `t0` and `t1`. -/
theorem storeKs_ok {ks : List (Nat × BitVec 64)} {s : State} (h : Room s)
    (hnd : (ks.map Prod.fst).Nodup) (hk : ∀ p ∈ ks, kSlot ≤ p.1 ∧ p.1 < kSlot + 13) :
    WP isa (.block (ks.flatMap fun p => Impl.Words64.RISCV64.movImm64 t0 t1 p.2 ++ [stS p.1 t0])) s
      fun s' => (∀ k v, (k, v) ∈ ks → s'.mem.readW (Straight.wordAddr (s.gpr sb) k) 64 = v) ∧
        Frame (ksRegions (s.gpr sb) ks) s.mem s'.mem ∧ (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  induction ks generalizing s with
  | nil =>
    exact WP.block_nil ⟨fun _ _ h => absurd h List.not_mem_nil, Frame.refl _ _, fun _ _ _ => rfl,
      rfl, rfl, rfl⟩
  | cons p ks ih =>
    obtain ⟨k, v⟩ := p
    have hk0 := hk _ (List.mem_cons_self ..)
    simp only [List.flatMap_cons] at ih ⊢
    rw [List.append_assoc, WP.block_append_iff (M := isa)]
    refine WP.mono (Words64.movImm64_ok (d := t0) (tmp := t1) (by decide) v)
      fun s₁ ⟨v₁, g₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
    have b₁ : s₁.gpr sb = s.gpr sb := g₁ _ (by decide) (by decide)
    have h₁ : Room s₁ := room_congr h b₁ wr₁
    simp only [List.singleton_append, stS]
    have hk' : k < scratchSlots := by unfold kSlot at hk0; unfold scratchSlots; omega
    refine wp_sd (a := Straight.wordAddr (s.gpr sb) k) (by unfold kSlot at hk0; omega) (by rw [b₁])
      (slot_al h.1 (by unfold kSlot at hk0; omega))
      (h₁.wr (by simp only [scratchR, b₁]; exact Straight.slot_contains _ hk' (by unfold scratchSlots; decide)))
      fun s₂ u₂ => ?_
    have b₂ : s₂.gpr sb = s.gpr sb := by rw [u₂.gpr, b₁]
    have h₂ : Room s₂ := room_congr h b₂ (by rw [u₂.wr, wr₁])
    obtain ⟨hnk, hnd'⟩ := List.nodup_cons.mp hnd
    refine WP.mono (ih (s := s₂) h₂ hnd' (fun p hp => hk p (List.mem_cons_of_mem _ hp)))
      fun s₃ ⟨mk₃, f₃, g₃, rd₃, wr₃, sp₃⟩ => ?_
    rw [b₂] at mk₃ f₃
    have m₂ : s₂.mem = s.mem.writeW (Straight.wordAddr (s.gpr sb) k) v := by rw [u₂.mem, m₁, v₁]
    refine ⟨fun j w hj => ?_, ?_, fun r h1 h2 => by rw [g₃ r h1 h2, u₂.gpr, g₁ r h1 h2],
      by rw [rd₃, u₂.rd, rd₁], by rw [wr₃, u₂.wr, wr₁], by rw [sp₃, u₂.sp, sp₁]⟩
    · rcases List.mem_cons.mp hj with e | hj
      · cases e
        rw [f₃.readW (r := ⟨Straight.wordAddr (s.gpr sb) k, 8⟩) (by simp [Region.Contains]) (fun r hr => ?_)
          (by decide), m₂, Mem.readW_writeW_self64]
        simp only [ksRegions, List.mem_map] at hr
        obtain ⟨⟨j', w'⟩, hj', rfl⟩ := hr
        have hne : k ≠ j' := fun e => hnk (by
          simp only [List.mem_map]; exact ⟨(j', w'), hj', e.symm⟩)
        have h1 := hk _ (List.mem_cons_of_mem _ hj')
        simp only at h1
        exact Offset.disjoint (s.gpr sb) (by omega) (by unfold kSlot at h1 hk0; omega)
          (by unfold kSlot at h1 hk0; omega)
      · exact mk₃ j w hj
    · simp only [ksRegions, List.map_cons]
      refine Frame.trans (m₂ ▸ ?_) (f₃.mono fun r hr => List.mem_cons_of_mem _ hr)
      exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _ (by simp [Region.Contains])

/-- The masks, built in their slots. -/
theorem buildMasks_ok {s : State} (h : Room s) :
    WP isa (.block buildMasks) s fun s' =>
      (∀ j v, (j, v) ∈ gKs → s'.mem.readW (Straight.wordAddr (s.gpr sb + BitVec.ofNat 64 (8 * kSlot)) j) 64 = v) ∧
        Frame [masksR s] s.mem s'.mem ∧ (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  rw [buildMasks_eq]
  refine WP.mono (storeKs_ok h kAbs_nodup kAbs_range) fun s' ⟨h1, h2, h3, h4, h5, h6⟩ =>
    ⟨fun j v hj => ?_, h2.sub fun r hr => ?_, h3, h4, h5, h6⟩
  · have := h1 (kSlot + j) v (List.mem_map.mpr ⟨(j, v), hj, rfl⟩)
    simp only [Straight.wordAddr] at this ⊢
    rw [Offset.add_add]
    rw [show 8 * (kSlot + j) = 8 * kSlot + 8 * j by omega] at this
    exact this
  · simp only [ksRegions, List.mem_map] at hr
    obtain ⟨⟨k, v⟩, hk, rfl⟩ := hr
    have := kAbs_range _ hk
    refine ⟨masksR s, List.mem_singleton_self _, ?_⟩
    simp only [masksR, Straight.wordAddr] at this ⊢
    exact Offset.sub (s.gpr sb) (d := 8 * k) (n := 8) (e := 8 * kSlot) (k := 8 * 13) (by omega) (by omega)

/-! ## The prologue -/

/-- What the prologue leaves: the scratch buffer in `a5`, the callee-saved
registers saved in it, the masks built and pointed to by `a3`. -/
structure Prologue (r : Reg) (s s' : State) : Prop where
  room : Room s'
  masks : Masks s'
  base : s'.gpr sb = s.gpr r
  regs : ∀ x, x ≠ sb → x ≠ kb → x ≠ t0 → x ≠ t1 → s'.gpr x = s.gpr x
  saved : Spill.Saved (s.gpr r) s.gpr savedOffs s'.mem
  frame : Frame [⟨s.gpr r, 8 * scratchSlots⟩] s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem prologue_ok {r : Reg} {s : State} (hal : (s.gpr r).toNat % 8 = 0)
    (hscr : InRegions s.wr (s.gpr r) (8 * scratchSlots)) :
    WP isa (.block (prologue r)) s (Prologue r s) := by
  rw [prologue, WP.block_append_iff (M := isa), WP.block_append_iff (M := isa),
    WP.block_append_iff (M := isa)]
  simp only [movR]
  refine wp_mv fun s₁ u₁ => WP.block_nil ?_
  have room₁ : Room s₁ := ⟨by rw [u₁.gpr]; exact hal, by rw [u₁.gpr, u₁.wr]; exact hscr⟩
  rw [seedSave_eq]
  refine Spill.save_ok (rest := []) room₁.1 savedOffs_ho (fun p hp => room₁.wr ?_) (WP.block_nil ?_)
  · have := savedOffs_range p hp
    have h8 : p.2 + 8 ≤ 8 * scratchSlots := by unfold scratchSlots; omega
    exact Offset.contains_base _ h8 (by omega)
  generalize hS : ({ s₁ with mem := Spill.saveMem s₁.mem (s₁.gpr sb) s₁.gpr savedOffs } : State) = s₂
  have g₂ : s₂.gpr = s₁.gpr := by rw [← hS]
  have mm₂ : s₂.mem = Spill.saveMem s₁.mem (s₁.gpr sb) s₁.gpr savedOffs := by rw [← hS]
  have rd₂ : s₂.rd = s₁.rd := by rw [← hS]
  have wr₂ : s₂.wr = s₁.wr := by rw [← hS]
  have sp₂ : s₂.sp = s₁.sp := by rw [← hS]
  have sb₂ : s₂.gpr sb = s.gpr r := by rw [g₂, u₁.gpr]
  have room₂ : Room s₂ := room_congr room₁ (by rw [g₂]) wr₂
  have sv₂ : Spill.Saved (s.gpr r) s.gpr savedOffs s₂.mem := by
    intro p hp
    rw [mm₂, u₁.gpr, Spill.saveMem_saved savedOffs_fits _ _ _ p hp]
    exact u₁.other _ (not_saved p hp).1
  have f₂ : Frame [⟨s.gpr r, 8 * scratchSlots⟩] s.mem s₂.mem := by
    rw [mm₂, u₁.mem, u₁.gpr]
    exact Spill.saveMem_frame_base (fun p hp => by have := savedOffs_range p hp; unfold scratchSlots; omega)
      (by unfold scratchSlots; omega) _ _ _
  refine WP.mono (buildMasks_ok room₂) fun s₃ ⟨mk₃, fm₃, g₃, rd₃, wr₃, sp₃⟩ => ?_
  refine wp_addi (by unfold kSlot; omega) fun s₄ u₄ => WP.block_nil ?_
  have sb₃ : s₃.gpr sb = s.gpr r := by rw [g₃ _ (by decide) (by decide), sb₂]
  have sb₄ : s₄.gpr sb = s.gpr r := by rw [u₄.other _ (by decide), sb₃]
  have mR : masksR s₂ = ⟨s.gpr r + BitVec.ofNat 64 (8 * kSlot), 8 * 13⟩ := by
    simp only [masksR, sb₂]
  rw [mR] at fm₃
  refine ⟨room_congr room₂ (by rw [sb₄, sb₂]) (by rw [u₄.wr, wr₃]), ⟨?_, fun j v hj => ?_⟩, sb₄,
    fun x h1 h2 h3 h4 => ?_, ?_, ?_, by rw [u₄.rd, rd₃, rd₂, u₁.rd], by rw [u₄.wr, wr₃, wr₂, u₁.wr],
    by rw [u₄.sp, sp₃, sp₂, u₁.sp]⟩
  · rw [u₄.gpr, sb₃, sb₄]
  · rw [u₄.gpr, sb₃, u₄.mem]
    have := mk₃ j v hj
    rw [sb₂] at this
    exact this
  · rw [u₄.other x h2, g₃ x h3 h4, g₂, u₁.other x h1]
  · rw [u₄.mem]
    refine sv₂.frame_in savedOffs_range fm₃ fun r' hr' => ?_
    simp only [List.mem_singleton] at hr'; subst hr'
    exact Offset.disjoint _ (by unfold kSlot; omega) (by omega) (by unfold kSlot; omega)
  · rw [u₄.mem]
    exact f₂.trans (fm₃.sub fun r' hr' => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact Offset.sub_base _ (by unfold kSlot scratchSlots; omega)⟩)

end VG.Proof.Seed.RISCV64
