module

public import VerifiedGarbage.Proof.Dsa.Arm.Env
public import VerifiedGarbage.Proof.Dsa.Arm.GenerateContract
public import VerifiedGarbage.Impl.Dsa.Arm.Generate
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# DSA domain checks and key derivation on 32-bit ARM: the entries

As signing's (`Install.lean`): `checkEntry_ok` and `deriveEntry_ok` leave
`r12` at `scratch`, the registers to restore at its offset 128, and the
arguments and the components' pointers at their fields (`Installed`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd)

/-- The fields of the domain check. -/
abbrev checkFields (s : State) : Fields :=
  [(64, s.gpr .r0), (100, s.gpr .r2), (104, s.gpr .r3), (108, s.gpr .r2),
    (68, s.gpr .r0 + s.gpr .r2), (72, s.gpr .r0 + s.gpr .r2 + s.gpr .r3),
    (76, s.gpr .r0 + s.gpr .r2 + s.gpr .r3 + s.gpr .r2), (80, s.gpr .r0 + s.gpr .r2 + s.gpr .r3 + s.gpr .r2 + s.gpr .r2)]

/-- The fields of derivation. -/
abbrev deriveFields (s : State) : Fields :=
  [(96, s.gpr .r0), (64, s.gpr .r2), (100, arg s 0), (88, arg s 1), (104, arg s 2), (108, arg s 0),
    (68, s.gpr .r2 + arg s 0), (72, s.gpr .r2 + arg s 0 + arg s 2), (76, s.gpr .r2 + arg s 0 + arg s 2 + arg s 0),
    (80, s.gpr .r2 + arg s 0 + arg s 2 + arg s 0 + arg s 0)]

theorem checkFields_ok (s : State) : FieldsOk (checkFields s) := by
  intro f hf
  simp only [checkFields, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem deriveFields_ok (s : State) : FieldsOk (deriveFields s) := by
  intro f hf
  simp only [deriveFields, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- The arguments of the domain check at their fields. -/
theorem checkArgs_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (hz : 164 ≤ size) :
    WP isa (.block (Generate.checkArguments.flatMap Entry.saveArgument)) s fun t =>
      t.mem.readW (off base 64) 32 = s.gpr .r0 ∧ t.mem.readW (off base 100) 32 = s.gpr .r2 ∧
      t.mem.readW (off base 104) 32 = s.gpr .r3 ∧ t.mem.readW (off base 108) 32 = s.gpr .r2 ∧
      Rest [] s t ∧ Outside base 64 48 s.mem t.mem ∧ t.sp = s.sp := by
  have nw := hs.nowrap
  show WP isa (.block [.str .r0 .r12 64, .str .r2 .r12 100, .str .r3 .r12 104, .str .r2 .r12 108]) s _
  refine wp_str12 hs (by decide) (by omega) fun s₁ m₁ => ?_
  refine wp_str12 (hs.of_mupd m₁) (by decide) (by omega) fun s₂ m₂ => ?_
  refine wp_str12 ((hs.of_mupd m₁).of_mupd m₂) (by decide) (by omega) fun s₃ m₃ => ?_
  refine wp_str12 (((hs.of_mupd m₁).of_mupd m₂).of_mupd m₃) (by decide) (by omega) fun t m₄ => WP.block_nil ?_
  have v₁ : s₁.mem.readW (off base 64) 32 = s.gpr .r0 := by rw [m₁.mem]; exact readW_off_self _ _ _ _
  have v₂ : s₂.mem.readW (off base 100) 32 = s.gpr .r2 := by rw [m₂.mem, m₁.gpr]; exact readW_off_self _ _ _ _
  have v₃ : s₃.mem.readW (off base 104) 32 = s.gpr .r3 := by
    rw [m₃.mem, m₂.gpr, m₁.gpr]; exact readW_off_self _ _ _ _
  have v₄ : t.mem.readW (off base 108) 32 = s.gpr .r2 := by
    rw [m₄.mem, m₃.gpr, m₂.gpr, m₁.gpr]; exact readW_off_self _ _ _ _
  have k₄ : ∀ {d v}, (d + 4 ≤ 108 ∨ 112 ≤ d) → d + 4 ≤ 164 → s₃.mem.readW (off base d) 32 = v →
      t.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₄.mem]; exact stored hd (by omega) (by omega) h _
  have k₃ : ∀ {d v}, (d + 4 ≤ 104 ∨ 108 ≤ d) → d + 4 ≤ 164 → s₂.mem.readW (off base d) 32 = v →
      s₃.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₃.mem]; exact stored hd (by omega) (by omega) h _
  have k₂ : ∀ {d v}, (d + 4 ≤ 100 ∨ 104 ≤ d) → d + 4 ≤ 164 → s₁.mem.readW (off base d) 32 = v →
      s₂.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₂.mem]; exact stored hd (by omega) (by omega) h _
  refine ⟨k₄ (by decide) (by decide) (k₃ (by decide) (by decide) (k₂ (by decide) (by decide) v₁)),
    k₄ (by decide) (by decide) (k₃ (by decide) (by decide) v₂), k₄ (by decide) (by decide) v₃, v₄, ?_, ?_, ?_⟩
  · exact (((m₁.rest _).trans (m₂.rest _)).trans (m₃.rest _)).trans (m₄.rest _)
  · rw [m₄.mem, m₃.mem, m₂.mem, m₁.mem]
    exact (((outside_word (by decide) (by decide) (by omega) _).trans
      (outside_word (by decide) (by decide) (by omega) _)).trans (outside_word (by decide) (by decide) (by omega) _)).trans
      (outside_word (by decide) (by decide) (by omega) _)
  · rw [m₄.sp, m₃.sp, m₂.sp, m₁.sp]

/-- The arguments of derivation at their fields. -/
theorem deriveArgs_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (hz : 164 ≤ size)
    (hr : ArgsRead s 5) (ha : ArgsApart s base 5) :
    WP isa (.block (Generate.deriveArguments.flatMap Entry.saveArgument)) s fun t =>
      t.mem.readW (off base 96) 32 = s.gpr .r0 ∧ t.mem.readW (off base 64) 32 = s.gpr .r2 ∧
      t.mem.readW (off base 100) 32 = stackArg s 0 ∧ t.mem.readW (off base 88) 32 = stackArg s 1 ∧
      t.mem.readW (off base 104) 32 = stackArg s 2 ∧ t.mem.readW (off base 108) 32 = stackArg s 0 ∧
      Rest [.r4] s t ∧ Outside base 64 48 s.mem t.mem ∧ ∀ i < 5, stackArg t i = stackArg s i := by
  have nw := hs.nowrap
  show WP isa (.block [.str .r0 .r12 96, .str .r2 .r12 64, .ldrSp .r4 (4 * 0), .str .r4 .r12 100,
    .ldrSp .r4 (4 * 1), .str .r4 .r12 88, .ldrSp .r4 (4 * 2), .str .r4 .r12 104,
    .ldrSp .r4 (4 * 0), .str .r4 .r12 108]) s _
  refine wp_str12 hs (by decide) (by omega) fun s₁ m₁ => ?_
  have a₁ := ha.mupd m₁
  refine wp_str12 (hs.of_mupd m₁) (by decide) (by omega) fun s₂ m₂ => ?_
  have a₂ := a₁.mupd m₂
  have w₂ := (hs.of_mupd m₁).of_mupd m₂
  have r₂ : ArgsRead s₂ 5 := (hr.keep m₁.rd m₁.wr m₁.sp).keep m₂.rd m₂.wr m₂.sp
  have A₂ : ∀ i < 5, stackArg s₂ i = stackArg s i := fun i hi => by
    rw [stackArg_mupd m₂ a₁ hi (by decide), stackArg_mupd m₁ ha hi (by decide)]
  refine wp_ldrSp (by decide) (r₂ 0 (by decide)) fun s₃ u₃ => wp_str12 (w₂.of_upd u₃ (by decide)) (by decide)
    (by omega) fun s₄ m₄ => ?_
  have a₄ := (a₂.upd u₃).mupd m₄
  have w₄ := (w₂.of_upd u₃ (by decide)).of_mupd m₄
  have r₄ : ArgsRead s₄ 5 := (r₂.keep u₃.rd u₃.wr u₃.sp).keep m₄.rd m₄.wr m₄.sp
  have A₄ : ∀ i < 5, stackArg s₄ i = stackArg s i := fun i hi => by
    rw [stackArg_mupd m₄ (a₂.upd u₃) hi (by decide), stackArg_upd u₃, A₂ i hi]
  refine wp_ldrSp (by decide) (r₄ 1 (by decide)) fun s₅ u₅ => wp_str12 (w₄.of_upd u₅ (by decide)) (by decide)
    (by omega) fun s₆ m₆ => ?_
  have a₆ := (a₄.upd u₅).mupd m₆
  have w₆ := (w₄.of_upd u₅ (by decide)).of_mupd m₆
  have r₆ : ArgsRead s₆ 5 := (r₄.keep u₅.rd u₅.wr u₅.sp).keep m₆.rd m₆.wr m₆.sp
  have A₆ : ∀ i < 5, stackArg s₆ i = stackArg s i := fun i hi => by
    rw [stackArg_mupd m₆ (a₄.upd u₅) hi (by decide), stackArg_upd u₅, A₄ i hi]
  refine wp_ldrSp (by decide) (r₆ 2 (by decide)) fun s₇ u₇ => wp_str12 (w₆.of_upd u₇ (by decide)) (by decide)
    (by omega) fun s₈ m₈ => ?_
  have a₈ := (a₆.upd u₇).mupd m₈
  have w₈ := (w₆.of_upd u₇ (by decide)).of_mupd m₈
  have r₈ : ArgsRead s₈ 5 := (r₆.keep u₇.rd u₇.wr u₇.sp).keep m₈.rd m₈.wr m₈.sp
  have A₈ : ∀ i < 5, stackArg s₈ i = stackArg s i := fun i hi => by
    rw [stackArg_mupd m₈ (a₆.upd u₇) hi (by decide), stackArg_upd u₇, A₆ i hi]
  refine wp_ldrSp (by decide) (r₈ 0 (by decide)) fun s₉ u₉ => wp_str12 (w₈.of_upd u₉ (by decide)) (by decide)
    (by omega) fun t m₁₀ => WP.block_nil ?_
  have A : ∀ i < 5, stackArg t i = stackArg s i := fun i hi => by
    rw [stackArg_mupd m₁₀ (a₈.upd u₉) hi (by decide), stackArg_upd u₉, A₈ i hi]
  have v₁ : s₁.mem.readW (off base 96) 32 = s.gpr .r0 := by rw [m₁.mem]; exact readW_off_self _ _ _ _
  have v₂ : s₂.mem.readW (off base 64) 32 = s.gpr .r2 := by rw [m₂.mem, m₁.gpr]; exact readW_off_self _ _ _ _
  have v₄ : s₄.mem.readW (off base 100) 32 = stackArg s 0 := by
    rw [m₄.mem, u₃.gpr, A₂ 0 (by decide)]; exact readW_off_self _ _ _ _
  have v₆ : s₆.mem.readW (off base 88) 32 = stackArg s 1 := by
    rw [m₆.mem, u₅.gpr, A₄ 1 (by decide)]; exact readW_off_self _ _ _ _
  have v₈ : s₈.mem.readW (off base 104) 32 = stackArg s 2 := by
    rw [m₈.mem, u₇.gpr, A₆ 2 (by decide)]; exact readW_off_self _ _ _ _
  have v₁₀ : t.mem.readW (off base 108) 32 = stackArg s 0 := by
    rw [m₁₀.mem, u₉.gpr, A₈ 0 (by decide)]; exact readW_off_self _ _ _ _
  have k₁₀ : ∀ {d v}, (d + 4 ≤ 108 ∨ 112 ≤ d) → d + 4 ≤ 164 → s₈.mem.readW (off base d) 32 = v →
      t.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₁₀.mem, u₉.mem]; exact stored hd (by omega) (by omega) h _
  have k₈ : ∀ {d v}, (d + 4 ≤ 104 ∨ 108 ≤ d) → d + 4 ≤ 164 → s₆.mem.readW (off base d) 32 = v →
      s₈.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₈.mem, u₇.mem]; exact stored hd (by omega) (by omega) h _
  have k₆ : ∀ {d v}, (d + 4 ≤ 88 ∨ 92 ≤ d) → d + 4 ≤ 164 → s₄.mem.readW (off base d) 32 = v →
      s₆.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₆.mem, u₅.mem]; exact stored hd (by omega) (by omega) h _
  have k₄ : ∀ {d v}, (d + 4 ≤ 100 ∨ 104 ≤ d) → d + 4 ≤ 164 → s₂.mem.readW (off base d) 32 = v →
      s₄.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₄.mem, u₃.mem]; exact stored hd (by omega) (by omega) h _
  have k₂ : ∀ {d v}, (d + 4 ≤ 64 ∨ 68 ≤ d) → d + 4 ≤ 164 → s₁.mem.readW (off base d) 32 = v →
      s₂.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₂.mem]; exact stored hd (by omega) (by omega) h _
  refine ⟨k₁₀ (by decide) (by decide) (k₈ (by decide) (by decide) (k₆ (by decide) (by decide)
      (k₄ (by decide) (by decide) (k₂ (by decide) (by decide) v₁)))),
    k₁₀ (by decide) (by decide) (k₈ (by decide) (by decide) (k₆ (by decide) (by decide) (k₄ (by decide) (by decide) v₂))),
    k₁₀ (by decide) (by decide) (k₈ (by decide) (by decide) (k₆ (by decide) (by decide) v₄)),
    k₁₀ (by decide) (by decide) (k₈ (by decide) (by decide) v₆),
    k₁₀ (by decide) (by decide) v₈, v₁₀, ?_, ?_, A⟩
  · exact (((((((((m₁.rest _).trans (m₂.rest _)).trans (u₃.rest (by decide))).trans (m₄.rest _)).trans
      (u₅.rest (by decide))).trans (m₆.rest _)).trans (u₇.rest (by decide))).trans (m₈.rest _)).trans
      (u₉.rest (by decide))).trans (m₁₀.rest _)
  · rw [m₁₀.mem, u₉.mem, m₈.mem, u₇.mem, m₆.mem, u₅.mem, m₄.mem, u₃.mem, m₂.mem, m₁.mem]
    exact (((((outside_word (by decide) (by decide) (by omega) _).trans
      (outside_word (by decide) (by decide) (by omega) _)).trans (outside_word (by decide) (by decide) (by omega) _)).trans
      (outside_word (by decide) (by decide) (by omega) _)).trans (outside_word (by decide) (by decide) (by omega) _)).trans
      (outside_word (by decide) (by decide) (by omega) _)

theorem checkEntry_ok {s : State} (h : checkPre s) :
    WP isa (.block Generate.checkEntry) s
      (Installed s (State.addr (arg s 0)) ((arg s 1).toNat * 8) (checkFields s)) := by
  obtain ⟨hsp, hrd, hwr, _, hsa, _, hsb, hv, _, hsw⟩ := h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hs16 : 16384 ≤ (arg s 1).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega
  show WP isa (.block (((Entry.openScratch 0) ++ Generate.checkArguments.flatMap Entry.saveArgument) ++
    Entry.keyPointers)) s _
  simp only [Entry.openScratch, List.append_assoc, List.singleton_append]
  refine wp_ldrSp (i := 0) (by decide) (args_read (n := 2) (by rw [hrd]; simp) hsp 0 (by decide)) fun u₁ v₁ => ?_
  have w₁ := openScratch_ws v₁ ((arg s 1).toNat * 8) (by rw [hwr]; simp) hsb
  have nw := w₁.nowrap
  refine VG.Proof.X25519.Arm.WP.append (save_ok w₁ (by omega)) fun u₂ ⟨S₂, R₂, O₂⟩ => ?_
  have w₂ := w₁.of_rest R₂ (by decide)
  rw [v₁.mem] at O₂
  refine VG.Proof.X25519.Arm.WP.append (checkArgs_ok w₂ (by omega))
    fun u₃ ⟨F₁, F₂, F₃, F₄, R₃, O₃, _⟩ => ?_
  have w₃ := w₂.of_rest R₃ (by decide)
  have g0 : u₂.gpr .r0 = s.gpr .r0 := by rw [R₂.gpr _ (by decide), v₁.other _ (by decide)]
  have g2 : u₂.gpr .r2 = s.gpr .r2 := by rw [R₂.gpr _ (by decide), v₁.other _ (by decide)]
  have g3 : u₂.gpr .r3 = s.gpr .r3 := by rw [R₂.gpr _ (by decide), v₁.other _ (by decide)]
  rw [g0] at F₁
  rw [g2] at F₂ F₄
  rw [g3] at F₃
  refine WP.mono (keyPointers_ok w₃ (by omega) F₁ F₂ F₃) fun u ⟨K₁, K₂, K₃, K₄, R₄, O₄⟩ =>
    ⟨w₃.of_rest R₄ (by decide), ?_, ?_, ?_, ?_⟩
  · intro f hf
    have k : ∀ {d} {x : BitVec 32}, (d + 4 ≤ 68 ∨ 84 ≤ d) → d + 4 ≤ 164 →
        u₃.mem.readW (off (State.addr (arg s 0)) d) 32 = x →
        u.mem.readW (off (State.addr (arg s 0)) d) 32 = x := fun hd' hd'' h => keep_word O₄ hd' (by omega) h
    simp only [checkFields, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact k (d := 64) (by decide) (by decide) F₁
    · exact k (d := 100) (by decide) (by decide) F₂
    · exact k (d := 104) (by decide) (by decide) F₃
    · exact k (d := 108) (by decide) (by decide) F₄
    · exact K₁
    · exact K₂
    · exact K₃
    · exact K₄
  · intro i hi
    have g : u₁.gpr (Entry.savedRegs.getD i .r0) = s.gpr (Entry.savedRegs.getD i .r0) :=
      v₁.other _ (saved_ne i hi)
    rw [← g]
    exact keep_word O₄ (.inr (by omega)) (by omega) (keep_word O₃ (.inr (by omega)) (by omega) (S₂ i hi))
  · exact ((O₂.mono (by decide) (by decide)).trans (O₃.mono (by decide) (by decide))).trans
      (O₄.mono (by decide) (by decide))
  · exact (((v₁.rest (by decide)).trans (R₂.mono (by decide))).trans (R₃.mono (by decide))).trans
      (R₄.mono (by decide))

theorem deriveEntry_ok {s : State} (h : derivePre s) :
    WP isa (.block Generate.deriveEntry) s
      (Installed s (State.addr (arg s 3)) ((arg s 4).toNat * 8) (deriveFields s)) := by
  obtain ⟨hsp, hrd, hwr, _, _, _, _, _, _, hsa, _, _, _, hsb, hv, _, _, hsw⟩ := h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hs16 : 16384 ≤ (arg s 4).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega
  have hd : Region.Disjoint ⟨State.addr s.sp, 4 * 5⟩ ⟨State.addr (arg s 3), (arg s 4).toNat * 8⟩ := hsa.symm
  show WP isa (.block (((Entry.openScratch 3) ++ Generate.deriveArguments.flatMap Entry.saveArgument) ++
    Entry.keyPointers)) s _
  simp only [Entry.openScratch, List.append_assoc, List.singleton_append]
  refine wp_ldrSp (i := 3) (by decide) (args_read (n := 5) (by rw [hrd]; simp) hsp 3 (by decide)) fun u₁ v₁ => ?_
  have w₁ := openScratch_ws v₁ ((arg s 4).toNat * 8) (by rw [hwr]; simp) hsb
  have nw := w₁.nowrap
  have aa : ArgsApart s (State.addr (arg s 3)) 5 := args_apart hd hsp (by omega)
  refine VG.Proof.X25519.Arm.WP.append (save_ok w₁ (by omega)) fun u₂ ⟨S₂, R₂, O₂⟩ => ?_
  have w₂ := w₁.of_rest R₂ (by decide)
  have hsp₂ : u₂.sp = s.sp := by rw [R₂.sp, v₁.sp]
  rw [v₁.mem] at O₂
  have A₂ : ∀ i < 5, stackArg u₂ i = stackArg s i := fun i hi =>
    stackArg_apart O₂ hsp₂ hd hi hsp (by omega) (by omega)
  have r₂ : ArgsRead u₂ 5 := (args_read (n := 5) (by rw [hrd]; simp) hsp).keep (by rw [R₂.rd, v₁.rd])
    (by rw [R₂.wr, v₁.wr]) hsp₂
  refine VG.Proof.X25519.Arm.WP.append (deriveArgs_ok w₂ (by omega) r₂ (aa.sp hsp₂))
    fun u₃ ⟨F₁, F₂, F₃, F₄, F₅, F₆, R₃, O₃, A₃⟩ => ?_
  have w₃ := w₂.of_rest R₃ (by decide)
  have g0 : u₂.gpr .r0 = s.gpr .r0 := by rw [R₂.gpr _ (by decide), v₁.other _ (by decide)]
  have g2 : u₂.gpr .r2 = s.gpr .r2 := by rw [R₂.gpr _ (by decide), v₁.other _ (by decide)]
  rw [g0] at F₁
  rw [g2] at F₂
  rw [A₂ 0 (by decide)] at F₃ F₆
  rw [A₂ 1 (by decide)] at F₄
  rw [A₂ 2 (by decide)] at F₅
  refine WP.mono (keyPointers_ok w₃ (by omega) F₂ F₃ F₅) fun u ⟨K₁, K₂, K₃, K₄, R₄, O₄⟩ =>
    ⟨w₃.of_rest R₄ (by decide), ?_, ?_, ?_, ?_⟩
  · intro f hf
    have k : ∀ {d} {x : BitVec 32}, (d + 4 ≤ 68 ∨ 84 ≤ d) → d + 4 ≤ 164 →
        u₃.mem.readW (off (State.addr (arg s 3)) d) 32 = x →
        u.mem.readW (off (State.addr (arg s 3)) d) 32 = x := fun hd' hd'' h => keep_word O₄ hd' (by omega) h
    simp only [deriveFields, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact k (d := 96) (by decide) (by decide) F₁
    · exact k (d := 64) (by decide) (by decide) F₂
    · exact k (d := 100) (by decide) (by decide) F₃
    · exact k (d := 88) (by decide) (by decide) F₄
    · exact k (d := 104) (by decide) (by decide) F₅
    · exact k (d := 108) (by decide) (by decide) F₆
    · exact K₁
    · exact K₂
    · exact K₃
    · exact K₄
  · intro i hi
    have g : u₁.gpr (Entry.savedRegs.getD i .r0) = s.gpr (Entry.savedRegs.getD i .r0) :=
      v₁.other _ (saved_ne i hi)
    rw [← g]
    exact keep_word O₄ (.inr (by omega)) (by omega) (keep_word O₃ (.inr (by omega)) (by omega) (S₂ i hi))
  · exact ((O₂.mono (by decide) (by decide)).trans (O₃.mono (by decide) (by decide))).trans
      (O₄.mono (by decide) (by decide))
  · exact (((v₁.rest (by decide)).trans (R₂.mono (by decide))).trans (R₃.mono (by decide))).trans
      (R₄.mono (by decide))

end VG.Proof.Dsa.Arm
