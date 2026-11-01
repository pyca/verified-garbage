module

public import VerifiedGarbage.Proof.Sm4.RISCV64.Group
public import VerifiedGarbage.Spec.Sm4.Contract
public import VerifiedGarbage.Proof.Sm4.Contract
public import VerifiedGarbage.Proof.Sm4.RISCV64.Keys
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.Sm4.RISCV64.Prologue
import VerifiedGarbage.Proof.Sm4.RISCV64.LayersLit

/-!
# SM4 ECB on RISCV64: the whole function

`ecb_wp`: with the working space as an argument (`ecbRISCV64`), `ecb dir`
saves the callee-saved registers, sets the masks, builds the table of round
keys in the order `dir` uses them, transforms the blocks a group at a time
(`dataGroup_wp`) and restores the registers. As on PPC64LE
(`Proof/Sm4/PPC64LE/Ecb.lean`), with the working space aligned to 8 bytes.
-/

@[expose] public section

namespace VG.Proof.Sm4

open VG VG.RISCV64 VG.Impl.Sm4.RISCV64

/-- The specification's direction. -/
def specDirA : Dir → Spec.Sm4.Direction
  | .encrypt => .encrypt
  | .decrypt => .decrypt

/-- ECB on RISCV64 with its working space at `a3`. -/
def ecbRISCV64 (dir : Dir) : Contract RISCV64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .a0, 128⟩
    let data : Region := ⟨s.gpr .a1, 16 * (s.gpr .a2).toNat⟩
    let scratch : Region := ⟨s.gpr .a3, 8 * slots⟩
    s.rd = [sched] ∧ s.wr = [data, scratch] ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
      data.Disjoint scratch ∧
      (s.gpr .a0).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 16 * (s.gpr .a2).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a3).toNat + 8 * slots ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat % 8 = 0
  post s s' :=
    Spec.Sm4.blocksAt s'.mem (s.gpr .a1) (s.gpr .a2).toNat =
      Spec.Sm4.ecb (Spec.Sm4.scheduleAt s.mem (s.gpr .a0)) (specDirA dir)
        (Spec.Sm4.blocksAt s.mem (s.gpr .a1) (s.gpr .a2).toNat)
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

end VG.Proof.Sm4

namespace VG.Proof.Sm4.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Impl.Sm4.RISCV64
open VG.Impl.Aes.RISCV64 (q sb t0 t1 movR ldS stS)
open VG.Proof.Aes.RISCV64 (sboxWrites)
open VG.Proof.Sm4 (DInv blocksAt_of_dinv ecb_eq blockFn specDirA ecbRISCV64 crypt_eq quads ofBlock outBlock)

theorem dataLoop_wp {s₀ : State} {b D : Addr} {n : Nat} {E : Nat → Spec.Sm4.Word} (hp : GPre s₀ b D n)
    {s : State} (hi : GInv s₀ b D n E 0 s) :
    WP isa (.loop Impl.Sm4.RISCV64.group (.nonzero .a2)) s (GDone s₀ b D n E) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - 16 * k ∧ GInv s₀ b D n E k s) (fun m s hs => ?_) n s
    ⟨0, by omega, hi⟩
  obtain ⟨k, rfl, hk⟩ := hs
  refine WP.mono (dataGroup_wp hp hk) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨(eval_nonzero s' .a2).trans (by rw [z]; rfl), d⟩
  · exact .inr ⟨(eval_nonzero s' .a2).trans (by rw [beq_false_of_ne z]; rfl), n - 16 * (k + 1),
      by have := d.lt; have := hk.lt; omega, k + 1, rfl, d⟩

/-- The schedule, outside the scratch buffer's frame. -/
theorem sched_frame {m m' : Mem} {b sched : Addr} (hf : Frame [⟨b, 8 * slots⟩] m m')
    (hd : Region.Disjoint ⟨sched, 128⟩ ⟨b, 8 * slots⟩) :
    Spec.Sm4.scheduleAt m' sched = Spec.Sm4.scheduleAt m sched := by
  have hb : ∀ k < 128, m' (sched + BitVec.ofNat 64 k) = m (sched + BitVec.ofNat 64 k) := fun k hk =>
    hf.bytes (R := ⟨sched, 128⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd)
      (by show 128 ≤ 2 ^ 64; omega_arith) hk
  apply Vector.ext
  intro i hi
  simp only [Spec.Sm4.scheduleAt, Vector.getElem_ofFn, List.range, List.range.loop, List.foldl]
  rw [hb (4 * i + 0) (by omega_arith), hb (4 * i + 1) (by omega_arith), hb (4 * i + 2) (by omega_arith),
    hb (4 * i + 3) (by omega_arith)]

theorem prologue_ok (ms : List (Nat × BitVec 64)) (hms : ∀ kv ∈ ms, kv.1 < tableSlot)
    (hnd : (ms.map (·.1)).Nodup) {sr : Reg} {s₀ : State} {b : Addr} (hb : s₀.gpr sr = b)
    (hw : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr) (hal : b.toNat % 8 = 0) :
    ∃ s, runBlock isa (([movR sb sr] : List Instr) ++ saveRegs ++ setSlots ms) s₀ = some s ∧
      s.gpr sb = b ∧ (∀ r, r ≠ sb → r ≠ t0 → r ≠ t1 → s.gpr r = s₀.gpr r) ∧
      Saved s₀ b s.mem ∧ (∀ kv ∈ ms, slotW s kv.1 = kv.2) ∧ Frame [⟨b, 8 * slots⟩] s₀.mem s.mem ∧
      s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s₀ sb sr
  have hb₁ : s₁.gpr sb = b := by rw [r₁, hb]
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, f₂, -, -⟩ := save_ok (b := b) (by rw [wr₁]; exact hw) hb₁ hal
  obtain ⟨s₃, e₃, v₃, -, g₃, rd₃, wr₃, f₃⟩ := setSlots_ok (b := b) ms (by rw [g₂ _ sb_ne_t0, hb₁])
    (by rw [wr₂, wr₁]; exact hw) hal hms hnd
  refine ⟨s₃, by
    rw [Interleave.runBlock_append, Interleave.runBlock_append, e₁, Option.bind_some, e₂, Option.bind_some, e₃],
    by rw [g₃ _ sb_ne_t0 sb_ne_t1, g₂ _ sb_ne_t0, hb₁],
    fun r h1 h2 h3 => by rw [g₃ r h2 h3, g₂ r h2, o₁ r h1], fun i hi => ?_, v₃, ?_,
    by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁]⟩
  · rw [← o₁ _ (sreg_ne_sb i hi), ← sv₂ i hi]
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

/-- `ecbWith sr k`, from the arguments' regions with the working space at
`sr`, for code `k` that builds the table of `dir` from the prologue's state. -/
theorem ecbWith_wp (sr : Reg) (k : Prog isa) (dir : Dir) {s₀ : State}
    (hrd : s₀.rd = [⟨s₀.gpr .a0, 128⟩]) (hwr : s₀.wr = [⟨s₀.gpr .a1, 16 * (s₀.gpr .a2).toNat⟩, ⟨s₀.gpr sr, 8 * slots⟩])
    (dSS : Region.Disjoint ⟨s₀.gpr .a0, 128⟩ ⟨s₀.gpr sr, 8 * slots⟩)
    (dDS : Region.Disjoint ⟨s₀.gpr .a1, 16 * (s₀.gpr .a2).toNat⟩ ⟨s₀.gpr sr, 8 * slots⟩)
    (fitK : (s₀.gpr .a0).toNat + 128 ≤ 2 ^ 64) (fitD : (s₀.gpr .a1).toNat + 16 * (s₀.gpr .a2).toNat ≤ 2 ^ 64)
    (fitB : (s₀.gpr sr).toNat + 8 * slots ≤ 2 ^ 64) (hal : (s₀.gpr sr).toNat % 8 = 0)
    (hk : ∀ s₁, SchedPre s₁ (s₀.gpr sr) (s₀.gpr .a0) → s₁.gpr .a0 = s₀.gpr .a0 → MasksOk s₁ →
      (∀ r, r ≠ sb → r ≠ t0 → r ≠ t1 → s₁.gpr r = s₀.gpr r) →
      WP isa k s₁ (KeysPost s₁ (s₀.gpr sr) (s₀.gpr .a0) dir)) :
    WP isa (ecbWith sr k) s₀ fun s' => (∀ i < 12, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      Spec.Sm4.blocksAt s'.mem (s₀.gpr .a1) (s₀.gpr .a2).toNat =
        Spec.Sm4.ecb (Spec.Sm4.scheduleAt s₀.mem (s₀.gpr .a0)) (specDirA dir)
          (Spec.Sm4.blocksAt s₀.mem (s₀.gpr .a1) (s₀.gpr .a2).toNat) := by
  let b := s₀.gpr sr
  let D := s₀.gpr .a1
  let n := (s₀.gpr .a2).toNat
  let sched := s₀.gpr .a0
  have hwS : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [b]
  have hwD : (⟨D, 16 * n⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [D, n]
  have hrK : (⟨sched, 128⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp [sched]
  unfold ecbWith
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, g₁, sv₁, v₁, f₁, rd₁, wr₁⟩ := prologue_ok (keyMasks ++ bsKs)
    (fun kv hkv => by have := masks_lt kv hkv; rw [tableSlot_eq]; omega) (by decide) (b := b) rfl hwS hal
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have hk₁ : SchedPre s₁ b sched :=
    ⟨⟨b₁, by rw [wr₁]; exact hwS, fitB, hal⟩, List.mem_append_left _ (by rw [rd₁]; exact hrK), fitK, dSS⟩
  have a0₁ : s₁.gpr .a0 = sched := g₁ _ (by decide) (by decide) (by decide)
  -- The table.
  refine WP.seq (WP.mono (hk s₁ hk₁ a0₁ v₁ g₁) fun s₂ k₂ => ?_)
  let E : Nat → Spec.Sm4.Word := dirKeys dir (Spec.Sm4.scheduleAt s₀.mem sched)
  have hsch : Spec.Sm4.scheduleAt s₁.mem sched = Spec.Sm4.scheduleAt s₀.mem sched := sched_frame f₁ dSS
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
  have a2₂ : s₂.gpr .a2 = s₀.gpr .a2 := by
    rw [k₂.regs _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide)]
  have a1₂ : s₂.gpr .a1 = D := by
    rw [k₂.regs _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide)]
  have rd₂ : s₂.rd = s₀.rd := by rw [k₂.rd, rd₁]
  have wr₂ : s₂.wr = s₀.wr := by rw [k₂.wr, wr₁]
  -- Any blocks?
  have hz₃ : (s₂.gpr .a2 == 0) = decide (n = 0) := by
    rw [a2₂, show s₀.gpr .a2 = BitVec.ofNat 64 n by simp only [n, BitVec.ofNat_toNat, BitVec.setWidth_eq]]
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro h; have := congrArg BitVec.toNat h; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
    · intro h; rw [h]; rfl
  refine WP.seq (WP.mono (M := isa) (Q := GDone s₀ b D n E)
    (WP.ite (decide (n = 0)) ((eval_zero s₂ .a2).trans (by rw [hz₃])) (fun h0 => ?_) (fun h0 => ?_))
    fun s₄ d₄ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨base₂, sc₂, fun i hi => by omega, fr₂, rd₂, wr₂⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine dataLoop_wp ⟨hwS, hwD, dDS, fitB, fitD, hal⟩ ⟨base₂, by rw [a1₂]; simp,
      by rw [a2₂, Nat.mul_zero, Nat.sub_zero]; simp [n], by omega, k₂.rdi, sc₂, fun i hi => ?_, fr₂, rd₂, wr₂⟩
    rw [data₂ i hi, ite_eq_right (by omega)]
  -- The epilogue.
  obtain ⟨s₅, e₅, rg₅, -, m₅, -, -⟩ := restore_ok (by rw [d₄.wr]; exact hwS) d₄.base hal d₄.scr.saved
  refine WP.of_runBlock ⟨s₅, e₅, rg₅, ?_⟩
  have hd₅ : DInv s₀.mem s₅.mem D n n (outF s₀.mem D E) := fun i hi => by
    rw [m₅]; exact d₄.data i hi
  show Spec.Sm4.blocksAt s₅.mem D n = _
  rw [blocksAt_of_dinv hd₅, ecb_eq]
  simp only [Spec.Sm4.blocksAt, List.map_map]
  refine List.map_congr_left fun j _ => ?_
  exact outF_spec dir s₀.mem _ D j

theorem ecb_wp (dir : Dir) {s₀ : State} (hp : (ecbRISCV64 dir).pre s₀) :
    WP isa (ecb dir) s₀ fun s' => (∀ i < 12, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (ecbRISCV64 dir).post s₀ s' := by
  obtain ⟨hrd, hwr, -, dSS, dDS, fitK, fitD, fitB, hal⟩ := hp
  exact ecbWith_wp .a3 (keys dir) dir hrd hwr dSS dDS fitK fitD fitB hal
    fun _ hk₁ a0₁ m₁ _ => keys_wp dir hk₁ a0₁ m₁

/-- The direction `vg_sm4_prepare_keys`'s `decrypt` selects. -/
def dirOf (decrypt : BitVec 64) : Dir := if decrypt = 0 then .encrypt else .decrypt

theorem specDirA_dirOf (decrypt : BitVec 64) :
    specDirA (dirOf decrypt) = Proof.Sm4.directionOf decrypt.toNat := by
  unfold dirOf Proof.Sm4.directionOf
  by_cases h : decrypt = 0
  · subst h; rfl
  · have h' : decrypt.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq h')
    simp only [h, h', ite_false]; rfl

end VG.Proof.Sm4.RISCV64
