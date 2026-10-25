module

public import VerifiedGarbage.Proof.Aes.RISCV64.Common
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.Aes.RISCV64.Ctr32
public import VerifiedGarbage.Impl.Words64.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Align

/-!
# The prologues and epilogues of the AES functions, on RISC-V

What `vg_aes_ctr32`, the block functions and the key expansion share
before and after their loops: rounding the scratch buffer up to a multiple
of 8 (`roundSb_wp`), saving and restoring the callee-saved registers in its
slots 40–51 (`Spill.save_ok`, `Spill.restore_ok` on `savedOffs`), building
the masks of the linear layers in its slots (`storeKs_ok`), and setting up
the key loop (`keySetup_wp`).
-/

@[expose] public section

namespace VG.Proof.Aes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.Align VG.RISCV64.Steps VG.Bitslice
  VG.Impl.Aes.RISCV64 VG.Proof.Aes

/-! ## Rounding the scratch buffer -/

theorem roundSb_wp {s : State} {P : State → Prop}
    (h : ∀ s', s'.gpr sb = s.gpr sb + BitVec.ofNat 64 (pad (s.gpr sb)) →
      (∀ r, r ≠ sb → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → P s') :
    WP isa (.block roundSb) s P := by
  unfold roundSb
  refine wp_addi (imm := 7) (by decide) fun s₁ u₁ => wp_andi (by decide) fun s₂ u₂ => WP.block_nil ?_
  refine h s₂ ?_ (fun r hr => by rw [u₂.other r hr, u₁.other r hr]) (by rw [u₂.mem, u₁.mem])
    (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) (by rw [u₂.sp, u₁.sp])
  rw [u₂.gpr, u₁.gpr, ← align_eq]
  rfl

/-! ## The callee-saved registers -/

/-- The registers and their byte offsets in the scratch buffer. -/
def savedOffs : List (Reg × Nat) := savedRegs.map fun p => (p.1, 8 * p.2)

theorem saveRegs_eq : saveRegs = Spill.saveCode sb savedOffs := by
  simp only [saveRegs, Spill.saveCode, savedOffs, List.map_map]; rfl

theorem restoreRegs_eq : restoreRegs = Spill.restoreCode sb savedOffs := by
  simp only [restoreRegs, Spill.restoreCode, savedOffs, List.map_map]; rfl

theorem savedOffs_fits : Spill.Fits savedOffs := by decide

theorem savedOffs_restorable : Spill.Restorable sb savedOffs := by decide

theorem savedOffs_ho : ∀ p ∈ savedOffs, p.2 % 8 = 0 ∧ p.2 < 2048 := by decide

theorem savedOffs_range : ∀ p ∈ savedOffs, 320 ≤ p.2 ∧ p.2 + 8 ≤ 320 + 96 := by decide

/-- The registers `savedOffs` saves are the preserved ones. -/
theorem savedOffs_regs : savedOffs.map Prod.fst = RISCV64.preserved := by decide

theorem not_saved_sb : sb ∉ savedOffs.map Prod.fst := by decide

theorem not_saved_ra : Reg.ra ∉ savedOffs.map Prod.fst := by decide

/-! ## The masks -/

/-- Build the masks `ks` in their slots, through `t0` and `t1`. -/
def storeKs (ks : List (Nat × BitVec 64)) : List Instr :=
  ks.flatMap fun p => Impl.Words64.RISCV64.movImm64 t0 t1 p.2 ++ [stS p.1 t0]

theorem storeMasks_eq (base : Nat) (ms : List (Nat × BitVec 64)) :
    storeMasks base ms = storeKs (ksOf base ms) := by
  simp only [storeMasks, storeKs, ksOf, List.flatMap_map]

theorem maskInit_eq : maskInit = storeKs allKs := by
  simp only [maskInit, storeMasks_eq, allKs, storeKs, List.flatMap_append, bsKs, srKs, invSrKs]

/-- The slots of `ks`. -/
def ksRegions (b : Addr) (ks : List (Nat × BitVec 64)) : List Region :=
  ks.map fun p => ⟨wordAddr b p.1, 8⟩

theorem storeKs_ok {ks : List (Nat × BitVec 64)} {s : State} {X : Addr} {N : Nat} (hs : Scr s X N)
    (hN : N ≤ 2048) (hnd : (ks.map Prod.fst).Nodup) (hk : ∀ p ∈ ks, 8 * p.1 + 15 ≤ N) :
    WP isa (.block (storeKs ks)) s fun s' =>
      MasksAt s'.mem (s.gpr sb) ks ∧ Frame (ksRegions (s.gpr sb) ks) s.mem s'.mem ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  induction ks generalizing s with
  | nil =>
    exact WP.block_nil ⟨fun _ _ h => absurd h List.not_mem_nil, Frame.refl _ _, fun _ _ _ => rfl,
      rfl, rfl, rfl⟩
  | cons p ks ih =>
    obtain ⟨k, v⟩ := p
    have hk0 : 8 * k + 15 ≤ N := hk _ (List.mem_cons_self ..)
    simp only [storeKs, List.flatMap_cons] at ih ⊢
    rw [List.append_assoc, WP.block_append_iff (M := isa)]
    refine WP.mono (Words64.movImm64_ok (d := t0) (tmp := t1) (by decide) v)
      fun s₁ ⟨v₁, g₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
    have b₁ : s₁.gpr sb = s.gpr sb := g₁ _ (by decide) (by decide)
    have hs₁ : Scr s₁ X N := hs.congr wr₁ b₁
    simp only [List.singleton_append, stS]
    refine wp_sd (a := wordAddr (s.gpr sb) k) (by omega) (by rw [b₁]) (wordAddr_al hs.al k (by omega))
      ⟨⟨X, N⟩, hs₁.wr, hs.contains (by omega) (by omega)⟩ fun s₂ u₂ => ?_
    have hs₂ : Scr s₂ X N := hs₁.congr u₂.wr (by rw [u₂.gpr])
    have b₂ : s₂.gpr sb = s.gpr sb := by rw [u₂.gpr, b₁]
    obtain ⟨hnk, hnd'⟩ := List.nodup_cons.mp hnd
    refine WP.mono (ih (s := s₂) hs₂ hnd' (fun p hp => hk p (List.mem_cons_of_mem _ hp)))
      fun s₃ ⟨mk₃, f₃, g₃, rd₃, wr₃, sp₃⟩ => ?_
    rw [b₂] at mk₃ f₃
    have m₂ : s₂.mem = s.mem.writeW (wordAddr (s.gpr sb) k) v := by rw [u₂.mem, m₁, v₁]
    refine ⟨fun j w hj => ?_, ?_, fun r h1 h2 => by rw [g₃ r h1 h2, u₂.gpr, g₁ r h1 h2],
      by rw [rd₃, u₂.rd, rd₁], by rw [wr₃, u₂.wr, wr₁], by rw [sp₃, u₂.sp, sp₁]⟩
    · rcases List.mem_cons.mp hj with e | hj
      · cases e
        rw [f₃.readW (r := ⟨wordAddr (s.gpr sb) k, 8⟩) (by simp [Region.Contains]) (fun r hr => ?_)
          (by decide), m₂, Mem.readW_writeW_self64]
        simp only [ksRegions, List.mem_map] at hr
        obtain ⟨⟨j', w'⟩, hj', rfl⟩ := hr
        have hne : k ≠ j' := fun e => hnk (by
          simp only [List.mem_map]; exact ⟨(j', w'), hj', e.symm⟩)
        have h1 := hk _ (List.mem_cons_of_mem _ hj')
        simp only at h1
        exact Offset.disjoint (s.gpr sb) (by omega) (by omega) (by omega)
      · exact mk₃ j w hj
    · simp only [ksRegions, List.map_cons]
      refine Frame.trans (m₂ ▸ ?_) (f₃.mono fun r hr => List.mem_cons_of_mem _ hr)
      exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _ (by simp [Region.Contains])

theorem allKs_nodup : (allKs.map Prod.fst).Nodup := by decide

theorem allKs_lt : ∀ p ∈ allKs, 8 * p.1 + 15 ≤ 2048 := by decide

/-- The masks of every layer. -/
theorem maskInit_ok {s : State} {X : Addr} (hs : Scr s X 2048) :
    WP isa (.block maskInit) s fun s' =>
      MasksAt s'.mem (s.gpr sb) allKs ∧
      Frame [⟨s.gpr sb + BitVec.ofNat 64 416, 48⟩, ⟨s.gpr sb + BitVec.ofNat 64 512, 96⟩]
        s.mem s'.mem ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  rw [maskInit_eq]
  refine WP.mono (storeKs_ok hs (by decide) allKs_nodup allKs_lt) fun s' ⟨h1, h2, h3, h4, h5, h6⟩ =>
    ⟨h1, h2.sub fun r hr => ?_, h3, h4, h5, h6⟩
  simp only [ksRegions, List.mem_map] at hr
  obtain ⟨⟨j, w⟩, hj, rfl⟩ := hr
  rcases allKs_in _ hj with hk | hk
  · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by simp only at hk ⊢; omega) (by simp only at hk ⊢; omega)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..),
      Offset.sub _ (by simp only at hk ⊢; omega) (by simp only at hk ⊢; omega)⟩

/-! ## The key loop's setup -/

theorem ofNat_shl4 {R : Nat} (h : R < 2 ^ 60) : BitVec.ofNat 64 R <<< 4 = BitVec.ofNat 64 (16 * R) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (a := R) (by omega)]
  congr 1; omega

/-- `a0 := schedule + 16 rounds`, `a2 := a5 + lastKey`, `a1 := rounds + 1`. -/
theorem keySetup_wp {s : State} {R : Nat} (hR : s.gpr .a1 = BitVec.ofNat 64 R) (hR' : R ≤ 14)
    {P : State → Prop}
    (h : ∀ s', s'.gpr .a0 = s.gpr .a0 + BitVec.ofNat 64 (16 * R) →
      s'.gpr .a2 = s.gpr sb + BitVec.ofNat 64 lastKey → s'.gpr .a1 = BitVec.ofNat 64 (R + 1) →
      (∀ r, r ≠ t0 → r ≠ .a0 → r ≠ .a2 → r ≠ .a1 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → P s') :
    WP isa (.block keySetup) s P := by
  unfold keySetup shlI
  refine wp_sll (by decide) fun s₁ u₁ => wp_add fun s₂ u₂ => wp_addi (imm := lastKey) (by decide)
    fun s₃ u₃ => wp_addi (imm := 1) (by decide) fun s₄ u₄ => WP.block_nil ?_
  refine h s₄ ?_ ?_ ?_ (fun r h1 h2 h3 h4 => ?_) (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem])
    (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp])
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), u₁.gpr, hR,
      ofNat_shl4 (by omega)]
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hR,
      BitVec.ofNat_add]
  · rw [u₄.other _ h4, u₃.other _ h3, u₂.other _ h2, u₁.other _ h1]

end VG.Proof.Aes.RISCV64
