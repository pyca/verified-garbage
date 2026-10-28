module

public import VerifiedGarbage.Proof.Seed.RISCV64.KeyBody
import VerifiedGarbage.Proof.Seed.RISCV64.Setup
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
import VerifiedGarbage.Proof.Seed.RISCV64.Ecb
import VerifiedGarbage.Proof.Seed.Memory
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Seed.RISCV64.Ecb
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# Key expansion on RISC-V

As on PPC64LE (`Proof/Seed/PPC64LE/Key.lean`): `expandKey_ok`: after the
prologue (`Setup.lean`), `expandKey` loads the key (`keyLoad_ok`: its two
big-endian doublewords are `Key0 || Key1` and `Key2 || Key3`), computes the
schedule (`keyPre_ok`, `keyHalves_wp`) and restores the registers.
-/

@[expose] public section

namespace VG.Proof.Seed.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.Seed.RISCV64 VG.Proof.Seed
open VG.Impl.Aes.RISCV64 (sb)

theorem be64_bytes (b0 b1 b2 b3 b4 b5 b6 b7 : Byte) :
    (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 : BitVec 64) =
      ((b0 ++ b1 ++ b2 ++ b3 : BitVec 32) ++ (b4 ++ b5 ++ b6 ++ b7 : BitVec 32)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append]
  split_ifs <;> first | rfl | omega | (congr 1; omega)

/-- The big-endian doubleword of a block's bytes `off … off + 7`: two of its words. -/
theorem be64_key (m : Mem) (p : Addr) {off : Nat} (ho : off ≤ 8) :
    ByteLoad.be64 m p off =
      Spec.Seed.wordAt (Spec.Seed.blockAt m p) off ++ Spec.Seed.wordAt (Spec.Seed.blockAt m p) (off + 4) := by
  have hg : ∀ i < 16, (Spec.Seed.blockAt m p).getD i 0 = m (p + BitVec.ofNat 64 i) := fun i hi => by
    rw [vector_getD _ _ hi]; simp only [Spec.Seed.blockAt, Vector.getElem_ofFn]
  simp only [ByteLoad.be64, Spec.Seed.wordAt, hg off (by omega), hg (off + 1) (by omega),
    hg (off + 2) (by omega), hg (off + 3) (by omega), hg (off + 4) (by omega),
    hg (off + 4 + 1) (by omega), hg (off + 4 + 2) (by omega), hg (off + 4 + 3) (by omega)]
  rw [be64_bytes]

/-- What key expansion needs: the scratch buffer and the schedule writable,
the key readable, apart from each other. -/
structure KeyPre (s : State) : Prop where
  scrAl : (s.gpr .a2).toNat % 8 = 0
  scratch : (⟨s.gpr .a2, 8 * scratchSlots⟩ : Region) ∈ s.wr
  schedIn : (⟨s.gpr .a1, 128⟩ : Region) ∈ s.wr
  keyIn : (⟨s.gpr .a0, 16⟩ : Region) ∈ s.rd
  keySched : (⟨s.gpr .a0, 16⟩ : Region).Disjoint ⟨s.gpr .a1, 128⟩
  keyBuf : (⟨s.gpr .a0, 16⟩ : Region).Disjoint ⟨s.gpr .a2, 8 * scratchSlots⟩
  schedBuf : (⟨s.gpr .a1, 128⟩ : Region).Disjoint ⟨s.gpr .a2, 8 * scratchSlots⟩

structure KeyPost (s s' : State) : Prop where
  saved : ∀ r ∈ RISCV64.preserved, s'.gpr r = s.gpr r
  ra : s'.gpr .ra = s.gpr .ra
  sched : Spec.Seed.scheduleAt s'.mem (s.gpr .a1) = Spec.Seed.expandKey (Spec.Seed.blockAt s.mem (s.gpr .a0))
  frame : Frame [⟨s.gpr .a2, 8 * scratchSlots⟩, ⟨s.gpr .a1, 128⟩] s.mem s'.mem

theorem expandKey_eq_code : expandKey = .seq (.block (prologue .a2 ++
    (Impl.Words.RISCV64.loadBE64 keyA .t0 .a0 0 ++ Impl.Words.RISCV64.loadBE64 keyB .t0 .a0 8) ++ keyPre))
    (.seq (.loop keyHalf (.nonzero .a4)) (.block seedRestore)) := by
  simp only [expandKey, keyPre, keyLoad, List.append_assoc]
  rfl

theorem expandKey_ok {s : State} (h : KeyPre s) : WP isa expandKey s (KeyPost s) := by
  let key := Spec.Seed.blockAt s.mem (s.gpr .a0)
  let X := s.gpr .a2
  rw [expandKey_eq_code]
  apply WP.seq
  rw [WP.block_append_iff (M := isa), WP.block_append_iff (M := isa)]
  refine WP.mono (prologue_ok h.scrAl ⟨_, Nat.le_refl _, h.scratch⟩) fun s₁ P => ?_
  -- the key
  have G₁ : ∀ r, r ≠ sb → r ≠ kb → r ≠ .t0 → r ≠ .t1 → s₁.gpr r = s.gpr r := P.regs
  have a0₁ : s₁.gpr .a0 = s.gpr .a0 := G₁ _ (by decide) (by decide) (by decide) (by decide)
  have hkey : ∀ k, k + 8 ≤ 16 → InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .a0 + BitVec.ofNat 64 k) 8 := fun k hk => by
    rw [P.rd, P.wr, a0₁]
    exact ⟨_, List.mem_append_left _ h.keyIn, Offset.contains_base _ (by omega) (by omega)⟩
  have key₁ : ∀ off, off ≤ 8 → ByteLoad.be64 s₁.mem (s₁.gpr .a0) off =
      Spec.Seed.wordAt key off ++ Spec.Seed.wordAt key (off + 4) := fun off ho => by
    rw [be64_key _ _ ho, a0₁]
    have : Spec.Seed.blockAt s₁.mem (s.gpr .a0) = key := blockAt_frame P.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.keyBuf
    rw [this]
  rw [WP.block_append_iff (M := isa)]
  refine WP.mono (ByteLoad.loadBE64_ok (s := s₁) (d := keyA) (tmp := .t0) (n := .a0) (off := 0)
    (by decide) (by decide) (by decide) (by decide) (hkey 0 (by decide))) fun s₂ e₂ => ?_
  have a0₂ : s₂.gpr .a0 = s.gpr .a0 := by
    rw [e₂, gpr_write_of_ne _ _ (show ¬ Reg.a0 = keyA by decide), gpr_write_of_ne _ _ (by decide), a0₁]
  have rw₂ : s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by rw [e₂]; exact ⟨rfl, rfl⟩
  refine WP.mono (ByteLoad.loadBE64_ok (s := s₂) (d := keyB) (tmp := .t0) (n := .a0) (off := 8)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [rw₂.1, rw₂.2, a0₂, ← a0₁]; exact hkey 8 (by decide))) fun s₃ e₃ => ?_
  have m₃ : s₃.mem = s₁.mem := by rw [e₃, e₂]; rfl
  have G₃ : ∀ r, r ≠ .t0 → r ≠ .t5 → r ≠ .t6 → s₃.gpr r = s₁.gpr r := fun r a b c => by
    rw [e₃, gpr_write_of_ne _ _ (show ¬ r = keyB from c), gpr_write_of_ne _ _ a, e₂,
      gpr_write_of_ne _ _ (show ¬ r = keyA from b), gpr_write_of_ne _ _ a]
  have h3 : s₃.gpr .t5 = kx (keyWords key 0) := by
    rw [e₃, gpr_write_of_ne _ _ (show ¬ Reg.t5 = keyB by decide), gpr_write_of_ne _ _ (by decide), e₂,
      show Reg.t5 = keyA from rfl, gpr_write_self, key₁ 0 (by decide)]
    rfl
  have h4 : s₃.gpr .t6 = ky (keyWords key 0) := by
    rw [e₃, show Reg.t6 = keyB from rfl, gpr_write_self, a0₂, ← a0₁,
      show s₂.mem = s₁.mem by rw [e₂]; rfl, key₁ 8 (by decide)]
    rfl
  have sb₃ : s₃.gpr sb = X := by rw [G₃ _ (by decide) (by decide) (by decide), P.base]
  have rd₃ : s₃.rd = s.rd := by rw [e₃, e₂]; exact P.rd
  have wr₃ : s₃.wr = s.wr := by rw [e₃, e₂]; exact P.wr
  have sp₃ : s₃.sp = s.sp := by rw [e₃, e₂]; exact P.sp
  have room₃ : Room s₃ := room_congr P.room (by rw [G₃ _ (by decide) (by decide) (by decide)])
    (by rw [wr₃, P.wr])
  have masks₃ : Masks s₃ := P.masks.frame (G₃ _ (by decide) (by decide) (by decide))
    (G₃ _ (by decide) (by decide) (by decide)) (by rw [m₃]; exact Frame.refl _ _)
  -- the rounds, and the count of halves
  refine WP.of_runBlock ?_
  obtain ⟨s₅, e₅, room₅, cur₅, next₅, a4₅, g₅, rd₅, wr₅, sp₅, f₅⟩ := keyPre_ok key room₃ h3 h4
  refine ⟨s₅, e₅, ?_⟩
  have G₅ : ∀ r ∈ [Reg.ra, .a0, .a1, .a2, .a3, .a5], s₅.gpr r = s₃.gpr r := fun r hr => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have sb₅ : s₅.gpr sb = X := (G₅ _ (by simp [sb])).trans sb₃
  have scr₅ : scratchR s₅ = ⟨X, 8 * scratchSlots⟩ := by simp only [scratchR, sb₅]
  have masks₅ : Masks s₅ := masks₃.frame (G₅ _ (by simp [sb])) (G₅ _ (by simp [kb]))
    (scratch_of_arrays f₅)
  have a1₅ : s₅.gpr .a1 = s.gpr .a1 := by
    rw [G₅ _ (by simp), G₃ _ (by decide) (by decide) (by decide), G₁ _ (by decide) (by decide) (by decide)
      (by decide)]
  have h0 : HalfInv key s₅ (s.gpr .a1) 0 s₅ :=
    ⟨room₅, masks₅, rfl, by rw [a1₅]; exact (BitVec.add_zero _).symm, a4₅, fun _ _ => rfl,
      fun w hw => by rw [cur₅ w hw, Nat.mul_zero, Nat.zero_add], fun _ => next₅, fun i hi => by omega,
      rfl, rfl, rfl, Frame.refl _ _⟩
  refine WP.seq (keyHalves_wp key (by rw [wr₅, wr₃]; exact h.schedIn) (by rw [scr₅]; exact h.schedBuf) h0
    fun s₆ v₆ regs₆ rd₆ wr₆ sp₆ f₆ => ?_)
  have sb₆ : s₆.gpr sb = X := (regs₆ _ (by simp [sb])).trans sb₅
  have room₆ : Room s₆ := room_congr room₅ (regs₆ _ (by simp [sb])) wr₆
  have workR₅ : workR s₅ = ⟨X, 8 * 104⟩ := by simp only [workR, sb₅]
  rw [workR₅] at f₆
  have arr₃ : Region.Sub (arraysR s₃) ⟨X, 8 * 104⟩ := by
    have := arraysR_sub_work s₃; simp only [workR, sb₃] at this; exact this
  have f₃₆ : Frame [⟨X, 8 * 104⟩, ⟨s.gpr .a1, 128⟩] s₃.mem s₆.mem :=
    (f₅.sub fun r hr => ⟨_, List.mem_cons_self, by simp at hr; subst hr; exact arr₃⟩).trans f₆
  have sv₆ : Spill.Saved X s.gpr savedOffs s₆.mem := by
    have sv₃ : Spill.Saved X s.gpr savedOffs s₃.mem := by rw [m₃]; exact P.saved
    refine sv₃.frame_in savedOffs_range f₃₆ fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact (h.schedBuf.sub_right (Offset.sub_base _ (by unfold scratchSlots; omega))).symm
  rw [seedRestore_eq]
  refine WP.mono (Spill.restore_wp (B := X) (by rw [← sb₆]; exact room₆.1) sb₆ savedOffs_ho
    savedOffs_restorable (fun q hq => room₆.rw ?_) sv₆) fun s' R => ?_
  · rw [← sb₆]
    have := savedOffs_range q hq
    exact Offset.contains_base _ (by unfold scratchSlots; omega) (by omega)
  have frame : Frame [⟨X, 8 * scratchSlots⟩, ⟨s.gpr .a1, 128⟩] s.mem s'.mem := by
    rw [R.mem]
    refine (P.frame.mono (by simp [X])).trans ?_
    rw [← m₃]
    refine f₃₆.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by unfold scratchSlots; omega)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  refine ⟨fun r hr => ?_, ?_, ?_, frame⟩
  · rw [← savedOffs_regs] at hr
    exact R.gpr_of (Or.inl hr)
  · rw [R.other _ (by decide), regs₆ _ (by simp), G₅ _ (by simp), G₃ _ (by decide) (by decide) (by decide),
      G₁ _ (by decide) (by decide) (by decide) (by decide)]
  · rw [Proof.Seed.expandKey_eq]
    apply Vector.ext
    intro i hi
    rw [scheduleAt_readW _ _ i hi, R.mem, v₆ i hi, Vector.getElem_ofFn]

end VG.Proof.Seed.RISCV64
