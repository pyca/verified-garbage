import VerifiedGarbage.Proof.Sm4.Arm.Group
import VerifiedGarbage.Proof.Sm4.Common
import VerifiedGarbage.Proof.Framework.Contract

/-!
# SM4 ECB on ARMv7: the whole function

`ecb_wp`: with the working space as an argument (`ecbArm`), `ecb dir`
saves the callee-saved registers, keeps the data pointer and the count in
their slots, builds the table of round keys in the order `dir` uses them,
transforms the blocks a group at a time (`dataGroup_wp`) and restores the
registers.
-/

namespace VG.Proof.Sm4

open VG VG.Arm VG.Impl.Sm4.Arm

/-- The specification's direction. -/
def specDirArm : Dir → Spec.Sm4.Direction
  | .encrypt => .encrypt
  | .decrypt => .decrypt

/-- ECB on ARMv7 with its working space at `r3`. -/
def ecbArm (dir : Dir) : Contract Arm.isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 128⟩
    let data : Region := ⟨State.addr (s.gpr .r1), 16 * (s.gpr .r2).toNat⟩
    let scratch : Region := ⟨State.addr (s.gpr .r3), 4 * slots⟩
    s.rd = [sched] ∧ s.wr = [data, scratch] ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
      data.Disjoint scratch ∧
      (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 16 * (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 4 * slots ≤ 2 ^ 32
  post s s' :=
    Spec.Sm4.blocksAt s'.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat =
      Spec.Sm4.ecb (Spec.Sm4.scheduleAt s.mem (State.addr (s.gpr .r0))) (specDirArm dir)
        (Spec.Sm4.blocksAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
  pub s₁ s₂ :=
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.sp = s₂.sp

end VG.Proof.Sm4

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Sm4.Arm
open VG.Impl.Aes.Arm (q sb t0 t1 kp movR ldS stS)
open VG.Proof.Sm4 (DInv blocksAt_of_dinv ecb_eq blockFn specDirArm ecbArm crypt_eq quads ofBlock outBlock)

theorem dataLoop_wp {s₀ : State} {b D : BitVec 32} {n : Nat} {E : Nat → Spec.Sm4.Word} (hp : GPre s₀ b D n)
    {s : State} (hi : GInv s₀ b D n E 0 s) :
    WP isa (.loop group .ne) s (GDone s₀ b D n E) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - 8 * k ∧ GInv s₀ b D n E k s) (fun m s hs => ?_) n s
    ⟨0, by omega, hi⟩
  obtain ⟨k, rfl, hk⟩ := hs
  refine WP.mono (dataGroup_wp hp hk) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨(eval_ne s').trans (by rw [z]; rfl), d⟩
  · exact .inr ⟨(eval_ne s').trans (by rw [z]; rfl), n - 8 * (k + 1),
      by have := d.lt; have := hk.lt; omega, k + 1, rfl, d⟩

theorem outF_spec (dir : Dir) (m : Mem) (sch : Spec.Sm4.Schedule) (D : Addr) (j : Nat) :
    outF m D (dirKeys dir sch) j =
      blockFn sch (specDirArm dir) (Spec.Sm4.blockAt m (D + BitVec.ofNat 64 (16 * j))) := by
  cases dir
  · simp only [outF, blockFn, specDirArm, Spec.Sm4.encryptBlock, crypt_eq]; rfl
  · simp only [outF, blockFn, specDirArm, Spec.Sm4.decryptBlock, crypt_eq]; rfl

/-- The prologue: the registers saved, the scratch buffer in `sb`, the data
pointer and the count in their slots, the schedule's pointer in `r12`. -/
theorem prologue_ok {s₀ : State} {b : BitVec 32} (hb : s₀.gpr .r3 = b) (hw : ScrIn s₀.wr b) :
    ∃ s, runBlock isa (saveRegs .r3 ++ [movR sb .r3, stS dSlot .r1, stS nSlot .r2, movR .r12 .r0]) s₀ = some s ∧
      s.gpr sb = b ∧ s.gpr .r12 = s₀.gpr .r0 ∧ Saved s₀ b s.mem ∧
      s.mem.readW (wordAddr b dSlot) 32 = s₀.gpr .r1 ∧ s.mem.readW (wordAddr b nSlot) 32 = s₀.gpr .r2 ∧
      Frame [⟨State.addr b, 4 * slots⟩] s₀.mem s.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp := by
  obtain ⟨s₁, e₁, sv₁, g₁, rd₁, wr₁, sp₁, f₁, -⟩ := save_ok hw hb
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := movR_ok s₁ sb .r3
  have b₂ : s₂.gpr sb = b := by rw [r₂, g₁, hb]
  have hw₂ : ScrIn s₂.wr b := by rw [wr₂, wr₁]; exact hw
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃, sp₃, -, f₃⟩ := stSlot_ok s₂ .r1 sb (k := dSlot) b₂ (by decide) hw₂
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄, sp₄, -, f₄⟩ := stSlot_ok s₃ .r2 sb (k := nSlot) (by rw [g₃, b₂]) (by decide)
    (by rw [wr₃]; exact hw₂)
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅, sp₅⟩ := movR_ok s₄ .r12 .r0
  have hfit := hw.fit
  have hsub : ∀ k < slots, Region.Sub ⟨wordAddr b k, 4⟩ ⟨State.addr b, 4 * slots⟩ := fun k hk => slot_sub hfit hk
  refine ⟨s₅, ?_, by rw [o₅ _ (by decide), g₄, g₃, b₂], by rw [r₅, g₄, g₃, o₂ _ (by decide), g₁],
    fun i hi => ?_, ?_, ?_, ?_, by rw [rd₅, rd₄, rd₃, rd₂, rd₁], by rw [wr₅, wr₄, wr₃, wr₂, wr₁],
    by rw [sp₅, sp₄, sp₃, sp₂, sp₁]⟩
  · rw [runBlock_app, e₁, Option.bind_some,
      show ([movR sb .r3, stS dSlot .r1, stS nSlot .r2, movR .r12 .r0] : List Instr) =
        [movR sb .r3] ++ ([.str .r1 sb (4 * dSlot)] ++ ([.str .r2 sb (4 * nSlot)] ++ [movR .r12 .r0])) from rfl,
      runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some, runBlock_app, e₄,
      Option.bind_some, e₅]
  · rw [m₅, m₄, m₃, m₂, readW_slot_write hfit _ (by rw [savedSlot_eq, slots_eq]; omega) (by decide),
      ite_eq_right (by rw [savedSlot_eq, nSlot_eq]; omega),
      readW_slot_write hfit _ (by rw [savedSlot_eq, slots_eq]; omega) (by decide),
      ite_eq_right (by rw [savedSlot_eq, dSlot_eq]; omega)]
    exact sv₁ i hi
  · rw [m₅, m₄, m₃, readW_slot_write hfit _ (by decide) (by decide), ite_eq_right (by decide),
      readW_slot_write hfit _ (by decide) (by decide), ite_eq_left rfl, o₂ _ (by decide), g₁]
  · rw [m₅, m₄, readW_slot_write hfit _ (by decide) (by decide), ite_eq_left rfl, g₃, o₂ _ (by decide), g₁]
  · have f₂₄ : Frame [⟨State.addr b, 4 * slots⟩] s₂.mem s₄.mem :=
      (f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact hsub _ (by decide)⟩).trans
      (f₄.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact hsub _ (by decide)⟩)
    rw [m₅]; refine f₁.trans ?_; rw [← m₂]; exact f₂₄

theorem ecb_wp (dir : Dir) {s₀ : State} (hp : (ecbArm dir).pre s₀) :
    WP isa (ecb dir) s₀ fun s' => (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ (ecbArm dir).post s₀ s' := by
  obtain ⟨hrd, hwr, dSD, dSS, dDS, fitK, fitD, fitB⟩ := hp
  let b := s₀.gpr .r3
  let D := s₀.gpr .r1
  let n := (s₀.gpr .r2).toNat
  let sched := s₀.gpr .r0
  have hwS : ScrIn s₀.wr b := ⟨by rw [hwr]; simp [b], fitB⟩
  have hwD : (⟨State.addr D, 16 * n⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [D, n]
  have hrK : (⟨State.addr sched, 128⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp [sched]
  unfold ecb
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, r12₁, sv₁, dp₁, np₁, f₁, rd₁, wr₁, sp₁⟩ := prologue_ok (b := b) rfl hwS
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have hk₁ : SchedPre s₁ b sched :=
    ⟨b₁, by rw [wr₁]; exact hwS.mem, fitB, List.mem_append_left _ (by rw [rd₁]; exact hrK), fitK, dSS⟩
  -- The table.
  refine WP.seq (WP.mono (keys_wp dir hk₁ r12₁) fun s₂ k₂ => ?_)
  let E : Nat → Spec.Sm4.Word := dirKeys dir (Spec.Sm4.scheduleAt s₀.mem (State.addr sched))
  have hsch : Spec.Sm4.scheduleAt s₁.mem (State.addr sched) = Spec.Sm4.scheduleAt s₀.mem (State.addr sched) :=
    hk₁.sched_eq (Nat.le_refl _) f₁
  have hfitB : b.toNat + 4 * 364 ≤ 2 ^ 32 := fitB
  have f₀₂ : Frame [⟨State.addr b, 4 * slots⟩] s₀.mem s₂.mem :=
    f₁.trans (k₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by rw [tableEnd_eq, slots_eq]; omega)⟩)
  have base₂ : s₂.gpr sb = b := k₂.pre.base
  have hi₂ : ∀ j, tableEnd ≤ j → j < slots → s₂.mem.readW (wordAddr b j) 32 = s₁.mem.readW (wordAddr b j) 32 :=
    fun j h1 h2 => by
      rw [slot_addr (by rw [slots_eq] at h2; omega)]
      refine k₂.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.disjoint_base _ (by omega) (by rw [slots_eq] at h2; omega)
  have sc₂ : ScrOk s₀ b E s₂.mem := by
    refine ⟨fun e he => ?_, fun i hi => ?_⟩
    · have := k₂.key.keys e he
      rw [base₂, hsch] at this
      exact this
    · rw [hi₂ _ (by rw [savedSlot_eq, tableEnd_eq]; omega) (by rw [savedSlot_eq, slots_eq]; omega)]
      exact sv₁ i hi
  have data₂ : ∀ i < 16 * n, s₂.mem (State.addr D + BitVec.ofNat 64 i) = s₀.mem (State.addr D + BitVec.ofNat 64 i) :=
    fun i hi => f₀₂.bytes (R := ⟨State.addr D, 16 * n⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dDS) (by simp only; omega) hi
  have fr₂ : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s₀.mem s₂.mem :=
    f₀₂.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have rd₂ : s₂.rd = s₀.rd := by rw [k₂.rd, rd₁]
  have wr₂ : s₂.wr = s₀.wr := by rw [k₂.wr, wr₁]
  have sp₂ : s₂.sp = s₀.sp := by rw [k₂.sp, sp₁]
  have np₂ : s₂.mem.readW (wordAddr b nSlot) 32 = BitVec.ofNat 32 n := by
    rw [hi₂ _ (by decide) (by decide), np₁]; simp [n]
  -- Any blocks?
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃, sp₃⟩ := ldSlot_ok s₂ .r2 sb (k := nSlot) base₂ (by decide)
    (by rw [wr₂]; exact hwS)
  let s₄ := subFlags s₃ (s₃.gpr .r2) 0
  have e₄ : runBlock isa [.cmp .r2 (.imm 0)] s₃ = some s₄ := by
    rw [runBlock_cons, show exec (.cmp .r2 (.imm 0)) s₃ = some s₄ by simp [exec, Op2.eval, s₄]; decide,
      runStep_some, runBlock_nil]
  have hz₄ : s₄.z = decide (n = 0) := by
    show (s₃.gpr .r2 - 0 == 0) = _
    rw [r₃, np₂, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    have : n < 2 ^ 32 := (s₀.gpr .r2).isLt
    bv_omega
  refine WP.seq (WP.of_runBlock ⟨s₄, by
    rw [show ([ldS .r2 nSlot, .cmp .r2 (.imm 0)] : List Instr) = [.ldr .r2 sb (4 * nSlot)] ++ [.cmp .r2 (.imm 0)]
      from rfl, runBlock_app, e₃, Option.bind_some, e₄], ?_⟩)
  have base₄ : s₄.gpr sb = b := by show s₃.gpr sb = b; rw [o₃ _ (by decide), base₂]
  have mem₄ : s₄.mem = s₂.mem := m₃
  have rd₄ : s₄.rd = s₀.rd := by show s₃.rd = _; rw [rd₃, rd₂]
  have wr₄ : s₄.wr = s₀.wr := by show s₃.wr = _; rw [wr₃, wr₂]
  have sp₄ : s₄.sp = s₀.sp := by show s₃.sp = _; rw [sp₃, sp₂]
  refine WP.seq (WP.mono (M := isa) (Q := GDone s₀ b D n E)
    (WP.ite (decide (n = 0)) ((eval_eq s₄).trans (by rw [hz₄])) (fun h0 => ?_) (fun h0 => ?_))
    fun s₅ d₅ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨base₄, mem₄ ▸ sc₂, fun i hi => by omega, mem₄ ▸ fr₂, rd₄, wr₄, sp₄⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine dataLoop_wp ⟨hwS, hwD, dDS, fitD⟩ ⟨base₄, ?_, by rw [mem₄, np₂, Nat.mul_zero, Nat.sub_zero], by omega,
      mem₄ ▸ sc₂, fun i hi => ?_, mem₄ ▸ fr₂, rd₄, wr₄, sp₄⟩
    · rw [mem₄, hi₂ _ (by decide) (by decide), dp₁]; simp [D]
    · rw [mem₄, data₂ i hi, ite_eq_right (by omega)]
  -- The epilogue.
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆, sp₆⟩ := movR_ok s₅ .r12 sb
  obtain ⟨s₇, e₇, rg₇, -, m₇, -, -, -⟩ := restore_ok (s₀ := s₀) (b := b) (by rw [wr₆, d₅.wr]; exact hwS)
    (by rw [r₆, d₅.base]) (by rw [m₆]; exact d₅.scr.saved)
  refine WP.of_runBlock ⟨s₇, by rw [runBlock_app, e₆, Option.bind_some, e₇], rg₇, ?_⟩
  have hd₇ : DInv s₀.mem s₇.mem (State.addr D) n n (outF s₀.mem (State.addr D) E) := fun i hi => by
    rw [m₇, m₆]; exact d₅.data i hi
  show Spec.Sm4.blocksAt s₇.mem (State.addr D) n = _
  rw [blocksAt_of_dinv hd₇, ecb_eq]
  simp only [Spec.Sm4.blocksAt, List.map_map]
  refine List.map_congr_left fun j _ => ?_
  exact outF_spec dir s₀.mem _ _ j

end VG.Proof.Sm4.Arm
