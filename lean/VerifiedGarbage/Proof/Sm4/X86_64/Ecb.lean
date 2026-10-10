import VerifiedGarbage.Proof.Sm4.X86_64.GroupStep
import VerifiedGarbage.Proof.Sm4.Common

/-!
# SM4 ECB on x86-64: the whole function

`ecb_wp`: with the working space as an argument (`ecbX86_64`), `ecb dir`
saves the callee-saved registers, sets the masks, builds the table of round
keys in the order `dir` uses them, transforms the blocks a group at a time
(`dataGroup_wp`) and restores the registers.
-/

namespace VG.Proof.Sm4

open VG VG.X86_64 VG.Impl.Sm4.X86_64

/-- The specification's direction. -/
def specDir : Dir → Spec.Sm4.Direction
  | .encrypt => .encrypt
  | .decrypt => .decrypt

/-- ECB on x86-64 with its working space at `rcx`. -/
def ecbX86_64 (dir : Dir) : Contract X86_64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 128⟩
    let data : Region := ⟨s.gpr .rsi, 16 * (s.gpr .rdx).toNat⟩
    let scratch : Region := ⟨s.gpr .rcx, 8 * slots⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [sched] ∧ s.wr = [data, scratch] ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
      data.Disjoint scratch ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
      (s.gpr .rdi).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 16 * (s.gpr .rdx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + 8 * slots ≤ 2 ^ 64
  post s s' :=
    Spec.Sm4.blocksAt s'.mem (s.gpr .rsi) (s.gpr .rdx).toNat =
      Spec.Sm4.ecb (Spec.Sm4.scheduleAt s.mem (s.gpr .rdi)) (specDir dir)
        (Spec.Sm4.blocksAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.Sm4

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Sm4.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR movS st setMasks)
open VG.Proof.Sm4 (DInv blocksAt_of_dinv ecb_eq blockFn specDir ecbX86_64 crypt_eq quads ofBlock outBlock)

theorem testSelf_ok (s : State) (r : Reg) :
    ∃ s', runBlock isa [.alu .test r (.reg r)] s = some s' ∧ s'.zf = some (s.gpr r == 0) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨arithFlags s (s.gpr r &&& s.gpr r) false false, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some]
  · simp only [RegUpd.zf_arithFlags, BitVec.and_self]

theorem dataLoop_wp {s₀ : State} {b D : Addr} {n : Nat} {E : Nat → Spec.Sm4.Word} (hp : GPre s₀ b D n)
    {s : State} (hi : GInv s₀ b D n E 0 s) :
    WP isa (.loop Impl.Sm4.X86_64.group .ne) s (GDone s₀ b D n E) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - 16 * k ∧ GInv s₀ b D n E k s) (fun m s hs => ?_) n s
    ⟨0, by omega, hi⟩
  obtain ⟨k, rfl, hk⟩ := hs
  refine WP.mono (dataGroup_wp hp hk) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨by simp [X86_64.eval, z], d⟩
  · exact .inr ⟨by simp [X86_64.eval, z], n - 16 * (k + 1), by have := d.lt; have := hk.lt; omega,
      k + 1, rfl, d⟩

theorem sreg_ne (i : Nat) : sreg i ≠ .r9 ∧ sreg i ≠ .r8 ∧ sreg i ≠ .rdx := by
  unfold sreg; split <;> decide

theorem prologue_ok {s₀ : State} {b : Addr} (hb : s₀.gpr .rcx = b) (hw : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr) :
    ∃ s, runBlock isa (([movR sb .rcx, movR .r8 .rdx, movR .rdx .rsi] : List Instr) ++ saveRegs ++
        setMasks keyMasks) s₀ = some s ∧
      s.gpr sb = b ∧ s.gpr .r8 = s₀.gpr .rdx ∧ s.gpr .rdx = s₀.gpr .rsi ∧
      (∀ r, r ≠ .r9 → r ≠ .r8 → r ≠ .rdx → r ≠ t0 → s.gpr r = s₀.gpr r) ∧
      Saved s₀ b s.mem ∧ MasksOk s ∧ Frame [⟨b, 8 * slots⟩] s₀.mem s.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  obtain ⟨s₁a, e₁a, r₁a, o₁a, m₁a, rd₁a, wr₁a⟩ := movR_ok s₀ sb .rcx
  obtain ⟨s₁b, e₁b, r₁b, o₁b, m₁b, rd₁b, wr₁b⟩ := movR_ok s₁a .r8 .rdx
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s₁b .rdx .rsi
  have hb₁ : s₁.gpr sb = b := by rw [o₁ _ (by decide), o₁b _ (by decide), r₁a, hb]
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, f₂⟩ := save_ok (b := b) (by rw [wr₁, wr₁b, wr₁a]; exact hw) hb₁
  obtain ⟨s₃, e₃, v₃, -, g₃, rd₃, wr₃, f₃⟩ := setMasks_ok (b := b) keyMasks (by rw [g₂, hb₁])
    (by rw [wr₂, wr₁, wr₁b, wr₁a]; exact hw) (fun kv hkv => by have := mask_lt hkv; rw [tableSlot_eq]; omega)
    (by decide)
  have g₁ : ∀ r, r ≠ .r9 → r ≠ .r8 → r ≠ .rdx → s₁.gpr r = s₀.gpr r := fun r h1 h2 h3 => by
    rw [o₁ r h3, o₁b r h2, o₁a r h1]
  refine ⟨s₃, by
    rw [runBlock_app, runBlock_app, show ([movR sb .rcx, movR .r8 .rdx, movR .rdx .rsi] : List Instr) =
      [movR sb .rcx] ++ ([movR .r8 .rdx] ++ [movR .rdx .rsi]) from rfl, runBlock_app, e₁a, Option.bind_some,
      runBlock_app, e₁b, Option.bind_some, e₁, Option.bind_some, e₂, Option.bind_some, e₃],
    by rw [g₃ _ (by decide), g₂, hb₁], by rw [g₃ _ (by decide), g₂, o₁ _ (by decide), r₁b, o₁a _ (by decide)],
    by rw [g₃ _ (by decide), g₂, r₁, o₁b _ (by decide), o₁a _ (by decide)],
    fun r h1 h2 h3 h4 => by rw [g₃ r h4, g₂, g₁ r h1 h2 h3], fun i hi => ?_, fun kv hkv => v₃ kv hkv, ?_,
    by rw [rd₃, rd₂, rd₁, rd₁b, rd₁a], by rw [wr₃, wr₂, wr₁, wr₁b, wr₁a]⟩
  · obtain ⟨n1, n2, n3⟩ := sreg_ne i
    rw [← g₁ _ n1 n2 n3, ← sv₂ i hi]
    refine f₃.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by rw [tableSlot_eq, savedSlot_eq]; omega)
      (by rw [savedSlot_eq]; omega)
  · have hm1 : s₁.mem = s₀.mem := by rw [m₁, m₁b, m₁a]
    rw [← hm1]
    refine f₂.trans (f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    simp only [List.mem_singleton] at hr; subst hr
    exact Region.sub_prefix (by rw [tableSlot_eq, slots_eq]; omega)

theorem outF_spec (dir : Dir) (m : Mem) (sch : Spec.Sm4.Schedule) (D : Addr) (j : Nat) :
    outF m D (dirKeys dir sch) j = blockFn sch (specDir dir) (Spec.Sm4.blockAt m (D + BitVec.ofNat 64 (16 * j))) := by
  cases dir
  · simp only [outF, blockFn, specDir, Spec.Sm4.encryptBlock, crypt_eq]; rfl
  · simp only [outF, blockFn, specDir, Spec.Sm4.decryptBlock, crypt_eq]; rfl

theorem ecb_wp (dir : Dir) {s₀ : State} (hp : (ecbX86_64 dir).pre s₀) :
    WP isa (ecb dir) s₀ fun s' => gprPreserved s₀ s' ∧ (ecbX86_64 dir).post s₀ s' := by
  obtain ⟨hrd, hwr, dSD, dSS, dDS, dRD, dRS, fitK, fitD, fitB⟩ := hp
  let b := s₀.gpr .rcx
  let D := s₀.gpr .rsi
  let n := (s₀.gpr .rdx).toNat
  let sched := s₀.gpr .rdi
  have hwS : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [b]
  have hwD : (⟨D, 16 * n⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [D, n]
  have hrK : (⟨sched, 128⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp [sched]
  unfold ecb
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, r8₁, rdx₁, g₁, sv₁, m₁, f₁, rd₁, wr₁⟩ := prologue_ok (b := b) rfl hwS
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have hk₁ : SchedPre s₁ b sched :=
    ⟨b₁, by rw [wr₁]; exact hwS, fitB, List.mem_append_left _ (by rw [rd₁]; exact hrK), fitK, dSS⟩
  have rdi₁ : s₁.gpr .rdi = sched := g₁ _ (by decide) (by decide) (by decide) (by decide)
  -- The table.
  refine WP.seq (WP.mono (keys_wp dir hk₁ rdi₁ m₁) fun s₂ k₂ => ?_)
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
  have rsp₂ : s₂.gpr .rsp = s₀.gpr .rsp := by
    rw [k₂.regs _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide) (by decide)]
  have r8₂ : s₂.gpr .r8 = s₀.gpr .rdx := by rw [k₂.regs _ (by decide) (by decide) (by decide), r8₁]
  have rdx₂ : s₂.gpr .rdx = D := by rw [k₂.regs _ (by decide) (by decide) (by decide), rdx₁]
  have rd₂ : s₂.rd = s₀.rd := by rw [k₂.rd, rd₁]
  have wr₂ : s₂.wr = s₀.wr := by rw [k₂.wr, wr₁]
  -- Any blocks?
  obtain ⟨s₃, e₃, z₃, g₃, m₃, rd₃, wr₃⟩ := testSelf_ok s₂ .r8
  refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
  have hz₃ : s₃.zf = some (decide (n = 0)) := by
    rw [z₃, r8₂]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by simp [n, h], fun h => BitVec.eq_of_toNat_eq (by simpa [n] using h)⟩
  refine WP.seq (WP.mono (M := isa) (Q := GDone s₀ b D n E)
    (WP.ite (decide (n = 0)) (by simp [X86_64.eval, hz₃]) (fun h0 => ?_) (fun h0 => ?_)) fun s₄ d₄ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨by rw [g₃, base₂], by rw [g₃, rsp₂], by rw [m₃]; exact sc₂, fun i hi => by omega,
      by rw [m₃]; exact fr₂, by rw [rd₃, rd₂], by rw [wr₃, wr₂]⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine dataLoop_wp ⟨hwS, hwD, dDS, fitB, fitD⟩ ⟨by rw [g₃, base₂], by rw [g₃, rsp₂],
      by rw [g₃, rdx₂]; simp, by rw [g₃, r8₂, Nat.mul_zero, Nat.sub_zero]; simp [n], by omega,
      by rw [g₃, k₂.rdi], by rw [m₃]; exact sc₂, fun i hi => ?_, by rw [m₃]; exact fr₂, by rw [rd₃, rd₂],
      by rw [wr₃, wr₂]⟩
    rw [m₃, data₂ i hi, ite_eq_right (by omega)]
  -- The epilogue.
  obtain ⟨s₅, e₅, rg₅, o₅, f₅, rd₅, wr₅⟩ := restore_ok (by rw [d₄.wr]; exact hwS) d₄.base d₄.scr.saved
  refine WP.of_runBlock ⟨s₅, e₅, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rg₅ 0 (by omega)
    · exact rg₅ 1 (by omega)
    · rw [o₅ _ (fun i hi => by unfold sreg; split <;> decide), d₄.rsp]
    · exact rg₅ 2 (by omega)
    · exact rg₅ 3 (by omega)
    · exact rg₅ 4 (by omega)
    · exact rg₅ 5 (by omega)
  · -- The return address is untouched.
    have fr : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s₅.mem :=
      d₄.frame.trans (f₅.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (Nat.le_refl _)⟩)
    refine fr.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dRS
    · exact dRD
  · have hd₅ : DInv s₀.mem s₅.mem D n n (outF s₀.mem D E) := fun i hi => by
      rw [f₅.bytes (R := ⟨D, 16 * n⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact dDS.sub_right (Region.sub_prefix (Nat.le_refl _)))
        (by simp only; omega) hi]
      exact d₄.data i hi
    show Spec.Sm4.blocksAt s₅.mem D n = _
    rw [blocksAt_of_dinv hd₅, ecb_eq]
    simp only [Spec.Sm4.blocksAt, List.map_map]
    refine List.map_congr_left fun j _ => ?_
    exact outF_spec dir s₀.mem _ D j

end VG.Proof.Sm4.X86_64
