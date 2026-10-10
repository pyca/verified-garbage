import VerifiedGarbage.Proof.Sm4.AArch64.Group
import VerifiedGarbage.Proof.Sm4.Common

/-!
# SM4 ECB on AArch64: the whole function

`ecb_wp`: with the working space as an argument (`ecbAArch64`), `ecb dir`
saves the callee-saved registers, sets the masks, builds the table of round
keys in the order `dir` uses them, transforms the blocks a group at a time
(`dataGroup_wp`) and restores the registers.
-/

namespace VG.Proof.Sm4

open VG VG.AArch64 VG.Impl.Sm4.AArch64

/-- The specification's direction. -/
def specDirA : Dir → Spec.Sm4.Direction
  | .encrypt => .encrypt
  | .decrypt => .decrypt

/-- ECB on AArch64 with its working space at `x3`. -/
def ecbAArch64 (dir : Dir) : Contract AArch64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 128⟩
    let data : Region := ⟨s.gpr .x1, 16 * (s.gpr .x2).toNat⟩
    let scratch : Region := ⟨s.gpr .x3, 8 * slots⟩
    s.rd = [sched] ∧ s.wr = [data, scratch] ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
      data.Disjoint scratch ∧
      (s.gpr .x0).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 16 * (s.gpr .x2).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x3).toNat + 8 * slots ≤ 2 ^ 64
  post s s' :=
    Spec.Sm4.blocksAt s'.mem (s.gpr .x1) (s.gpr .x2).toNat =
      Spec.Sm4.ecb (Spec.Sm4.scheduleAt s.mem (s.gpr .x0)) (specDirA dir)
        (Spec.Sm4.blocksAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

end VG.Proof.Sm4

namespace VG.Proof.Sm4.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Sm4.AArch64
open VG.Impl.Aes.AArch64 (q sb t0 t1 movR ldS stS)
open VG.Proof.Sm4 (DInv blocksAt_of_dinv ecb_eq blockFn specDirA ecbAArch64 crypt_eq quads ofBlock outBlock)

theorem dataLoop_wp {s₀ : State} {b D : Addr} {n : Nat} {E : Nat → Spec.Sm4.Word} (hp : GPre s₀ b D n)
    {s : State} (hi : GInv s₀ b D n E 0 s) :
    WP isa (.loop Impl.Sm4.AArch64.group (.nonzero .x .x2)) s (GDone s₀ b D n E) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - 16 * k ∧ GInv s₀ b D n E k s) (fun m s hs => ?_) n s
    ⟨0, by omega, hi⟩
  obtain ⟨k, rfl, hk⟩ := hs
  refine WP.mono (dataGroup_wp hp hk) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨(eval_nonzero s' .x2).trans (by rw [z]; rfl), d⟩
  · exact .inr ⟨(eval_nonzero s' .x2).trans (by rw [beq_false_of_ne z]; rfl), n - 16 * (k + 1),
      by have := d.lt; have := hk.lt; omega, k + 1, rfl, d⟩

theorem sreg_ne (i : Nat) (hi : i < 10) : sreg i ≠ sb := by
  revert i; decide

theorem prologue_ok {s₀ : State} {b : Addr} (hb : s₀.gpr .x3 = b) (hw : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr) :
    ∃ s, runBlock isa (([movR sb .x3] : List Instr) ++ saveRegs ++ setSlots keyMasks) s₀ = some s ∧
      s.gpr sb = b ∧ (∀ r, r ≠ sb → r ≠ t0 → s.gpr r = s₀.gpr r) ∧
      Saved s₀ b s.mem ∧ MasksOk s ∧ Frame [⟨b, 8 * slots⟩] s₀.mem s.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s₀ sb .x3
  have hb₁ : s₁.gpr sb = b := by rw [r₁, hb]
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, f₂, -⟩ := save_ok (b := b) (by rw [wr₁]; exact hw) hb₁
  obtain ⟨s₃, e₃, v₃, -, g₃, rd₃, wr₃, f₃⟩ := setSlots_ok (b := b) keyMasks (by rw [g₂, hb₁])
    (by rw [wr₂, wr₁]; exact hw) (fun kv hkv => by have := mask_lt hkv; rw [tableSlot_eq]; omega)
    (by decide)
  refine ⟨s₃, by
    rw [runBlock_app, runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some, e₃],
    by rw [g₃ _ (by decide), g₂, hb₁],
    fun r h1 h2 => by rw [g₃ r h2, g₂, o₁ r h1], fun i hi => ?_, fun kv hkv => v₃ kv hkv, ?_,
    by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁]⟩
  · rw [← o₁ _ (sreg_ne i hi), ← sv₂ i hi]
    refine f₃.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by rw [tableSlot_eq, savedSlot_eq]; omega)
      (by rw [savedSlot_eq]; omega)
  · rw [← m₁]
    refine f₂.trans (f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    simp only [List.mem_singleton] at hr; subst hr
    exact Region.sub_prefix (by rw [tableSlot_eq, slots_eq]; omega)

theorem outF_spec (dir : Dir) (m : Mem) (sch : Spec.Sm4.Schedule) (D : Addr) (j : Nat) :
    outF m D (dirKeys dir sch) j = blockFn sch (specDirA dir) (Spec.Sm4.blockAt m (D + BitVec.ofNat 64 (16 * j))) := by
  cases dir
  · simp only [outF, blockFn, specDirA, Spec.Sm4.encryptBlock, crypt_eq]; rfl
  · simp only [outF, blockFn, specDirA, Spec.Sm4.decryptBlock, crypt_eq]; rfl

theorem ecb_wp (dir : Dir) {s₀ : State} (hp : (ecbAArch64 dir).pre s₀) :
    WP isa (ecb dir) s₀ fun s' => (∀ i < 10, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (ecbAArch64 dir).post s₀ s' := by
  obtain ⟨hrd, hwr, dSD, dSS, dDS, fitK, fitD, fitB⟩ := hp
  let b := s₀.gpr .x3
  let D := s₀.gpr .x1
  let n := (s₀.gpr .x2).toNat
  let sched := s₀.gpr .x0
  have hwS : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [b]
  have hwD : (⟨D, 16 * n⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [D, n]
  have hrK : (⟨sched, 128⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp [sched]
  unfold ecb
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, g₁, sv₁, m₁, f₁, rd₁, wr₁⟩ := prologue_ok (b := b) rfl hwS
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have hk₁ : SchedPre s₁ b sched :=
    ⟨b₁, by rw [wr₁]; exact hwS, fitB, List.mem_append_left _ (by rw [rd₁]; exact hrK), fitK, dSS⟩
  have x0₁ : s₁.gpr .x0 = sched := g₁ _ (by decide) (by decide)
  -- The table.
  refine WP.seq (WP.mono (keys_wp dir hk₁ x0₁ m₁) fun s₂ k₂ => ?_)
  let E : Nat → Spec.Sm4.Word := dirKeys dir (Spec.Sm4.scheduleAt s₀.mem sched)
  have hsch : Spec.Sm4.scheduleAt s₁.mem sched = Spec.Sm4.scheduleAt s₀.mem sched :=
    hk₁.sched_eq' (Nat.le_refl _) f₁
  have hfitB := fitB
  rw [slots_eq] at hfitB
  have f₀₂ : Frame [⟨b, 8 * slots⟩] s₀.mem s₂.mem :=
    f₁.trans (k₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by rw [tableEnd_eq, slots_eq]; omega)⟩)
  have base₂ : s₂.gpr sb = b := k₂.pre.base
  have sc₂ : ScrOk s₀ b E s₂.mem := by
    refine ⟨k₂.masks.at base₂, fun e he => ?_, fun i hi => ?_⟩
    · have := k₂.key.keys e he
      rw [base₂, hsch] at this
      exact this
    · rw [← sv₁ i hi]
      refine k₂.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by rw [tableEnd_eq, savedSlot_eq]; omega)
        (by rw [savedSlot_eq]; omega)
  have data₂ : ∀ i < 16 * n, s₂.mem (D + BitVec.ofNat 64 i) = s₀.mem (D + BitVec.ofNat 64 i) := fun i hi =>
    f₀₂.bytes (R := ⟨D, 16 * n⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dDS)
      (by simp only; omega) hi
  have fr₂ : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s₂.mem :=
    f₀₂.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have x2₂ : s₂.gpr .x2 = s₀.gpr .x2 := by
    rw [k₂.regs _ (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide)]
  have x1₂ : s₂.gpr .x1 = D := by
    rw [k₂.regs _ (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide)]
  have rd₂ : s₂.rd = s₀.rd := by rw [k₂.rd, rd₁]
  have wr₂ : s₂.wr = s₀.wr := by rw [k₂.wr, wr₁]
  -- Any blocks?
  have hz₃ : (s₂.gpr .x2 == 0) = decide (n = 0) := by
    rw [x2₂, show s₀.gpr .x2 = BitVec.ofNat 64 n by simp only [n, BitVec.ofNat_toNat, BitVec.setWidth_eq]]
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro h; have := congrArg BitVec.toNat h; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
    · intro h; rw [h]; rfl
  refine WP.seq (WP.mono (M := isa) (Q := GDone s₀ b D n E)
    (WP.ite (decide (n = 0)) ((eval_zero s₂ .x2).trans (by rw [hz₃])) (fun h0 => ?_) (fun h0 => ?_))
    fun s₄ d₄ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨base₂, sc₂, fun i hi => by omega, fr₂, rd₂, wr₂⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine dataLoop_wp ⟨hwS, hwD, dDS, fitB, fitD⟩ ⟨base₂, by rw [x1₂]; simp,
      by rw [x2₂, Nat.mul_zero, Nat.sub_zero]; simp [n], by omega, k₂.rdi, sc₂, fun i hi => ?_, fr₂, rd₂, wr₂⟩
    rw [data₂ i hi, ite_eq_right (by omega)]
  -- The epilogue.
  obtain ⟨s₅, e₅, rg₅, -, m₅, -, -⟩ := restore_ok (by rw [d₄.wr]; exact hwS) d₄.base d₄.scr.saved
  refine WP.of_runBlock ⟨s₅, e₅, rg₅, ?_⟩
  have hd₅ : DInv s₀.mem s₅.mem D n n (outF s₀.mem D E) := fun i hi => by
    rw [m₅]; exact d₄.data i hi
  show Spec.Sm4.blocksAt s₅.mem D n = _
  rw [blocksAt_of_dinv hd₅, ecb_eq]
  simp only [Spec.Sm4.blocksAt, List.map_map]
  refine List.map_congr_left fun j _ => ?_
  exact outF_spec dir s₀.mem _ D j

end VG.Proof.Sm4.AArch64
