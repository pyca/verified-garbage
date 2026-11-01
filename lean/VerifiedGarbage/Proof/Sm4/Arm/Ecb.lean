module

public import VerifiedGarbage.Proof.Sm4.Arm.Group
public import VerifiedGarbage.Spec.Sm4.Contract
public import VerifiedGarbage.Proof.Sm4.Contract
public import VerifiedGarbage.Proof.Sm4.Arm.Keys
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Sm4.Arm.LayersLit

/-!
# SM4 ECB on ARMv7: the whole function

`ecbWith_wp`: with the working space at `sr`, `ecbWith sr kt` saves the
callee-saved registers, runs `kt`, which builds the table of round keys in
the order `dir` uses them (`keys_wp`, `keysAny_wp`), transforms the blocks
a group at a time (`dataGroup_wp`) and restores the registers.
-/

@[expose] public section

namespace VG.Proof.Sm4

open VG VG.Arm VG.Impl.Sm4.Arm

/-- The specification's direction. -/
def specDirArm : Dir → Spec.Sm4.Direction
  | .encrypt => .encrypt
  | .decrypt => .decrypt

end VG.Proof.Sm4

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Sm4.Arm
open VG.Impl.Aes.Arm (q sb t0 t1 kp movR ldS stS)
open VG.Proof.Sm4 (DInv blocksAt_of_dinv ecb_eq blockFn specDirArm crypt_eq quads ofBlock outBlock)

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

/-- The prologue: the registers saved, the scratch buffer in `sb`, the
schedule's pointer in `r12`. -/
theorem prologue_ok {sr : Reg} {s₀ : State} {b : BitVec 32} (hb : s₀.gpr sr = b) (hw : ScrIn s₀.wr b) :
    ∃ s, runBlock isa (saveRegs sr ++ [movR sb sr, movR .r12 .r0]) s₀ = some s ∧
      s.gpr sb = b ∧ s.gpr .r12 = s₀.gpr .r0 ∧ (∀ r, r ≠ sb → r ≠ .r12 → s.gpr r = s₀.gpr r) ∧
      Saved s₀ b s.mem ∧ Frame [⟨State.addr b, 4 * slots⟩] s₀.mem s.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
      s.sp = s₀.sp := by
  obtain ⟨s₁, e₁, sv₁, g₁, rd₁, wr₁, sp₁, f₁, -⟩ := save_ok hw hb
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := movR_ok s₁ sb sr
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃, sp₃⟩ := movR_ok s₂ .r12 .r0
  refine ⟨s₃, ?_, by rw [o₃ _ (by decide), r₂, g₁, hb], by rw [r₃, o₂ _ (by decide), g₁],
    fun r h1 h2 => by rw [o₃ r h2, o₂ r h1, g₁], by rw [m₃, m₂]; exact sv₁, by rw [m₃, m₂]; exact f₁,
    by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁], by rw [sp₃, sp₂, sp₁]⟩
  rw [runBlock_app, e₁, Option.bind_some,
    show ([movR sb sr, movR .r12 .r0] : List Instr) = [movR sb sr] ++ [movR .r12 .r0] from rfl,
    runBlock_app, e₂, Option.bind_some, e₃]

/-- `ecbWith sr kt`, from the arguments' regions with the working space at
`sr`, for table code `kt` that builds the table of `dir`. -/
theorem ecbWith_wp (sr : Reg) (kt : Prog isa) (dir : Dir) {s₀ : State}
    (hrK : (⟨State.addr (s₀.gpr .r0), 128⟩ : Region) ∈ s₀.rd)
    (hwS : ScrIn s₀.wr (s₀.gpr sr))
    (hwD : (⟨State.addr (s₀.gpr .r1), 16 * (s₀.gpr .r2).toNat⟩ : Region) ∈ s₀.wr)
    (dSS : Region.Disjoint ⟨State.addr (s₀.gpr .r0), 128⟩ ⟨State.addr (s₀.gpr sr), 4 * slots⟩)
    (dDS : Region.Disjoint ⟨State.addr (s₀.gpr .r1), 16 * (s₀.gpr .r2).toNat⟩ ⟨State.addr (s₀.gpr sr), 4 * slots⟩)
    (fitK : (s₀.gpr .r0).toNat + 128 ≤ 2 ^ 32) (fitD : (s₀.gpr .r1).toNat + 16 * (s₀.gpr .r2).toNat ≤ 2 ^ 32)
    (hk : ∀ s₁, SchedPre s₁ (s₀.gpr sr) (s₀.gpr .r0) → s₁.gpr .r12 = s₀.gpr .r0 →
      (∀ r, r ≠ sb → r ≠ .r12 → s₁.gpr r = s₀.gpr r) →
      WP isa kt s₁ (KeysPost s₁ (s₀.gpr sr) (s₀.gpr .r0) dir)) :
    WP isa (ecbWith sr kt) s₀ fun s' => (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      Spec.Sm4.blocksAt s'.mem (State.addr (s₀.gpr .r1)) (s₀.gpr .r2).toNat =
        Spec.Sm4.ecb (Spec.Sm4.scheduleAt s₀.mem (State.addr (s₀.gpr .r0))) (specDirArm dir)
          (Spec.Sm4.blocksAt s₀.mem (State.addr (s₀.gpr .r1)) (s₀.gpr .r2).toNat) := by
  let b := s₀.gpr sr
  let D := s₀.gpr .r1
  let n := (s₀.gpr .r2).toNat
  let sched := s₀.gpr .r0
  have fitB : b.toNat + 4 * 364 ≤ 2 ^ 32 := by have := hwS.fit; rw [slots_eq] at this; exact this
  unfold ecbWith
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, r12₁, g₁, sv₁, f₁, rd₁, wr₁, sp₁⟩ := prologue_ok (b := b) rfl hwS
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have hk₁ : SchedPre s₁ b sched :=
    ⟨b₁, by rw [wr₁]; exact hwS.mem, hwS.fit, List.mem_append_left _ (by rw [rd₁]; exact hrK), fitK, dSS⟩
  -- The table.
  refine WP.seq (WP.mono (hk s₁ hk₁ r12₁ g₁) fun s₂ k₂ => ?_)
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
  have r1₂ : s₂.gpr .r1 = D := by
    rw [k₂.regs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₁ _ (by decide) (by decide)]
  have r2₂ : s₂.gpr .r2 = BitVec.ofNat 32 n := by
    rw [k₂.regs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₁ _ (by decide) (by decide)]; simp [n]
  -- Any blocks?
  let s₄ := subFlags s₂ (s₂.gpr .r2) 0
  have e₄ : runBlock isa [.cmp .r2 (.imm 0)] s₂ = some s₄ := by
    rw [runBlock_cons, show exec (.cmp .r2 (.imm 0)) s₂ = some s₄ by simp [exec, Op2.eval, s₄]; decide,
      runStep_some, runBlock_nil]
  have hz₄ : s₄.z = decide (n = 0) := by
    show (s₂.gpr .r2 - 0 == 0) = _
    rw [r2₂, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    have : n < 2 ^ 32 := (s₀.gpr .r2).isLt
    bv_omega_arith
  refine WP.seq (WP.of_runBlock ⟨s₄, e₄, ?_⟩)
  have base₄ : s₄.gpr sb = b := base₂
  have mem₄ : s₄.mem = s₂.mem := rfl
  have rd₄ : s₄.rd = s₀.rd := rd₂
  have wr₄ : s₄.wr = s₀.wr := wr₂
  have sp₄ : s₄.sp = s₀.sp := sp₂
  refine WP.seq (WP.mono (M := isa) (Q := GDone s₀ b D n E)
    (WP.ite (decide (n = 0)) ((eval_eq s₄).trans (by rw [hz₄])) (fun h0 => ?_) (fun h0 => ?_))
    fun s₅ d₅ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨base₄, mem₄ ▸ sc₂, fun i hi => by omega, mem₄ ▸ fr₂, rd₄, wr₄, sp₄⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine dataLoop_wp ⟨hwS, hwD, dDS, fitD⟩ ⟨base₄, by show s₂.gpr .r1 = _; rw [r1₂]; simp [D],
      by show s₂.gpr .r2 = _; rw [r2₂, Nat.mul_zero, Nat.sub_zero], by omega,
      mem₄ ▸ sc₂, fun i hi => ?_, mem₄ ▸ fr₂, rd₄, wr₄, sp₄⟩
    rw [mem₄, data₂ i hi, ite_eq_right (by omega)]
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

/-! ## Either direction -/

/-- The direction `vg_sm4_ecb`'s `decrypt` selects. -/
def dirOf (decrypt : BitVec 32) : Dir := if decrypt = 0 then .encrypt else .decrypt

theorem dirOf_eq (decrypt : BitVec 32) :
    specDirArm (dirOf decrypt) = Proof.Sm4.directionOf (decrypt.setWidth 64).toNat := by
  unfold dirOf Proof.Sm4.directionOf
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := decrypt.isLt; omega)]
  by_cases h : decrypt = 0
  · subst h; rfl
  · have h' : decrypt.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq h')
    simp only [h, h', ite_false]; rfl

/-- `keysAny`: the table of the direction `r3` selects, from a state whose
`r3` is `decrypt`. -/
theorem keysAny_wp {s : State} {b sched decrypt : BitVec 32} (hs : SchedPre s b sched)
    (hr : s.gpr .r12 = sched) (h3 : s.gpr .r3 = decrypt) :
    WP isa keysAny s (KeysPost s b sched (dirOf decrypt)) := by
  let s' := subFlags s (s.gpr .r3) 0
  have e' : runBlock isa [.cmp .r3 (.imm 0)] s = some s' := by
    rw [runBlock_cons, show exec (.cmp .r3 (.imm 0)) s = some s' by simp [exec, Op2.eval, s']; decide,
      runStep_some, runBlock_nil]
  have hz : s'.z = decide (decrypt = 0) := by
    show (s.gpr .r3 - 0 == 0) = _
    rw [h3, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]; simp
  have hs' : SchedPre s' b sched := ⟨hs.base, hs.scr, hs.fit, hs.sch, hs.schFit, hs.sep⟩
  unfold keysAny
  refine WP.seq (WP.of_runBlock ⟨s', e', ?_⟩)
  refine WP.ite (decide (decrypt = 0)) ((eval_eq s').trans (by rw [hz])) (fun h => ?_) (fun h => ?_)
  · have hd : dirOf decrypt = .encrypt := by simp only [dirOf, of_decide_eq_true h, ite_true]
    rw [hd]
    exact WP.mono (keys_wp .encrypt hs' hr) fun s₂ k => ⟨k.pre, k.key, k.frame, k.regs, k.rd, k.wr, k.sp⟩
  · have hd : dirOf decrypt = .decrypt := by simp only [dirOf, of_decide_eq_false h, ite_false]
    rw [hd]
    exact WP.mono (keys_wp .decrypt hs' hr) fun s₂ k => ⟨k.pre, k.key, k.frame, k.regs, k.rd, k.wr, k.sp⟩

end VG.Proof.Sm4.Arm
