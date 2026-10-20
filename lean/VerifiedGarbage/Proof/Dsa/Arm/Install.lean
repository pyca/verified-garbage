module

public import VerifiedGarbage.Proof.Dsa.Arm.EntrySave
public import VerifiedGarbage.Proof.Dsa.Arm.Contract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Framework.Offset

/-!
# DSA on 32-bit ARM: the entries

From the precondition of the contract, the entry of signing (`signEntry_ok`)
and of verification (`verifyEntry_ok`) leaves `r12` at `scratch`, the
registers to restore at its offset 128 and the arguments and the key's
component pointers at their fields (`Installed`), and has changed nothing
else but its header.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd)

/-- The fields of the entry: `(offset, value)`. -/
abbrev Fields := List (Nat × BitVec 32)

/-- What the entry leaves, from `s₀`. -/
structure Installed (s₀ : State) (base : Addr) (size : Nat) (fields : Fields) (u : State) : Prop where
  ws : Ws u base size
  fields : ∀ f ∈ fields, u.mem.readW (off base f.1) 32 = f.2
  saved : ∀ i < 9, u.mem.readW (off base (128 + 4 * i)) 32 = s₀.gpr (Entry.savedRegs.getD i .r0)
  mem : Outside base 64 100 s₀.mem u.mem
  rest : Rest [.r4, .r5, .r12] s₀ u

/-- The scratch region, and `r12` set to it. -/
theorem openScratch_ws {s u : State} {i : Nat} (hu : Upd s u .r12 (stackArg s i)) (size : Nat)
    (hr : ⟨State.addr (stackArg s i), size⟩ ∈ s.wr) (hb : (stackArg s i).toNat + size ≤ 2 ^ 32) :
    Ws u (State.addr (stackArg s i)) size :=
  ⟨by rw [hu.gpr], ⟨size, Nat.le_refl _, by omega, by rw [hu.wr]; exact hr⟩,
    by rw [VG.Proof.X25519.Arm.addr_toNat]; exact hb⟩

theorem args_read {s : State} {n : Nat} (h : ⟨State.addr s.sp, 4 * n⟩ ∈ s.rd) (hb : s.sp.toNat + 4 * n ≤ 2 ^ 32) :
    ArgsRead s n := fun i hi =>
  ⟨_, List.mem_append_left _ h, by
    rw [stackArgAddr, VG.Arm.addr_add (by omega)]
    exact Offset.contains_base _ (by omega) (by omega)⟩

theorem args_apart {s : State} {base : Addr} {n size : Nat} (h : Region.Disjoint ⟨State.addr s.sp, 4 * n⟩ ⟨base, size⟩)
    (hb : s.sp.toNat + 4 * n ≤ 2 ^ 32) (hz : 164 ≤ size) :
    ArgsApart s base n := fun i hi d hd =>
  Region.Disjoint.sep h (by rw [stackArgAddr, VG.Arm.addr_add (by omega)]; exact Offset.contains_base _ (by omega) (by omega))
    (Offset.contains_base base (by omega) (by omega))

/-- The fields of signing. -/
abbrev signFields (s : State) : Fields :=
  [(96, s.gpr .r0), (64, s.gpr .r2), (100, arg s 0), (88, arg s 1), (104, arg s 2), (92, arg s 3), (108, arg s 4),
    (68, s.gpr .r2 + arg s 0), (72, s.gpr .r2 + arg s 0 + arg s 2), (76, s.gpr .r2 + arg s 0 + arg s 2 + arg s 0),
    (80, s.gpr .r2 + arg s 0 + arg s 2 + arg s 0 + arg s 0)]

/-- The fields of verification. -/
abbrev verifyFields (s : State) : Fields :=
  [(64, s.gpr .r0), (100, s.gpr .r2), (104, s.gpr .r3), (84, arg s 0), (92, arg s 2), (108, arg s 3),
    (68, s.gpr .r0 + s.gpr .r2), (72, s.gpr .r0 + s.gpr .r2 + s.gpr .r3),
    (76, s.gpr .r0 + s.gpr .r2 + s.gpr .r3 + s.gpr .r2), (80, s.gpr .r0 + s.gpr .r2 + s.gpr .r3 + s.gpr .r2 + s.gpr .r2)]

/-- A word stored by the entry and kept since. -/
theorem keep_word {m m' : Mem} {base : Addr} {o n d : Nat} {v : BitVec 32} (O : Outside base o n m m')
    (hd : d + 4 ≤ o ∨ o + n ≤ d) (hb : d + 4 ≤ 2 ^ 64) (h : m.readW (off base d) 32 = v) :
    m'.readW (off base d) 32 = v := by
  rw [← h]
  exact BitVec.eq_of_toNat_eq (O.w32 hd hb)

/-- A word apart from the working space, which only changed inside it. -/
theorem readW_apart {m m' : Mem} {base p : Addr} {o n size : Nat} (O : Outside base o n m m')
    (hd : Region.Disjoint ⟨p, 4⟩ ⟨base, size⟩) (ho : o + n ≤ size) (hs : size ≤ 2 ^ 64) :
    m'.readW p 32 = m.readW p 32 :=
  Mem.readW_congr fun i hi =>
    (VG.Proof.Weierstrass.keep_of_disjoint O (hd.sub_right (Offset.sub_base base ho)) (by omega) hi (by decide))

theorem stackArg_apart {s s' : State} {base : Addr} {o n size k i : Nat} (O : Outside base o n s.mem s'.mem)
    (hsp : s'.sp = s.sp) (hd : Region.Disjoint ⟨State.addr s.sp, 4 * k⟩ ⟨base, size⟩) (hi : i < k)
    (hb : s.sp.toNat + 4 * k ≤ 2 ^ 32) (ho : o + n ≤ size) (hs : size ≤ 2 ^ 64) :
    stackArg s' i = stackArg s i := by
  unfold stackArg
  rw [show stackArgAddr s' i = stackArgAddr s i by simp only [stackArgAddr, hsp]]
  refine readW_apart O (hd.sub_left ?_) ho hs
  rw [stackArgAddr, VG.Arm.addr_add (by omega)]
  exact Offset.sub_base _ (by omega)

theorem ArgsApart.sp {s s' : State} {base : Addr} {n : Nat} (h : ArgsApart s base n) (hsp : s'.sp = s.sp) :
    ArgsApart s' base n :=
  fun i hi d hd => by rw [show stackArgAddr s' i = stackArgAddr s i by simp only [stackArgAddr, hsp]]; exact h i hi d hd

theorem saved_ne : ∀ i < 9, Entry.savedRegs.getD i .r0 ≠ .r12 := by decide

theorem signEntry_ok {s : State} (h : signPre s) :
    WP isa (.block Entry.signEntry) s
      (Installed s (State.addr (arg s 5)) ((arg s 6).toNat * 8) (signFields s)) := by
  obtain ⟨hsp, hrd, hwr, _, _, _, _, _, _, _, _, hsa, _, _, _, _, hsb, hv, _, _, hsw⟩ := h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hs16 : 16384 ≤ (arg s 6).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega
  have hd : Region.Disjoint ⟨State.addr s.sp, 4 * 7⟩ ⟨State.addr (arg s 5), (arg s 6).toNat * 8⟩ := hsa.symm
  show WP isa (.block (((Entry.openScratch 5) ++ Entry.signArguments.flatMap Entry.saveArgument) ++
    Entry.keyPointers)) s _
  simp only [Entry.openScratch, List.append_assoc, List.singleton_append]
  refine wp_ldrSp (i := 5) (by decide) (args_read (n := 7) (by rw [hrd]; simp) hsp 5 (by decide)) fun u₁ v₁ => ?_
  have w₁ := openScratch_ws v₁ ((arg s 6).toNat * 8) (by rw [hwr]; simp) hsb
  have nw := w₁.nowrap
  have aa : ArgsApart s (State.addr (arg s 5)) 7 := args_apart hd hsp (by omega)
  refine VG.Proof.X25519.Arm.WP.append (save_ok w₁ (by omega)) fun u₂ ⟨S₂, R₂, O₂⟩ => ?_
  have w₂ := w₁.of_rest R₂ (by decide)
  have hsp₂ : u₂.sp = s.sp := by rw [R₂.sp, v₁.sp]
  rw [v₁.mem] at O₂
  have A₂ : ∀ i < 7, stackArg u₂ i = stackArg s i := fun i hi =>
    stackArg_apart O₂ hsp₂ hd hi hsp (by omega) (by omega)
  have r₂ : ArgsRead u₂ 7 := (args_read (n := 7) (by rw [hrd]; simp) hsp).keep (by rw [R₂.rd, v₁.rd])
    (by rw [R₂.wr, v₁.wr]) hsp₂
  refine VG.Proof.X25519.Arm.WP.append (signArgs_ok w₂ (by omega) r₂ (aa.sp hsp₂))
    fun u₃ ⟨F₁, F₂, F₃, F₄, F₅, F₆, F₇, R₃, O₃, A₃⟩ => ?_
  have w₃ := w₂.of_rest R₃ (by decide)
  have g0 : u₂.gpr .r0 = s.gpr .r0 := by rw [R₂.gpr _ (by decide), v₁.other _ (by decide)]
  have g2 : u₂.gpr .r2 = s.gpr .r2 := by rw [R₂.gpr _ (by decide), v₁.other _ (by decide)]
  rw [g0] at F₁
  rw [g2] at F₂
  rw [A₂ 0 (by decide)] at F₃
  rw [A₂ 1 (by decide)] at F₄
  rw [A₂ 2 (by decide)] at F₅
  rw [A₂ 3 (by decide)] at F₆
  rw [A₂ 4 (by decide)] at F₇
  refine WP.mono (keyPointers_ok w₃ (by omega) F₂ F₃ F₅) fun u ⟨K₁, K₂, K₃, K₄, R₄, O₄⟩ => ⟨w₃.of_rest R₄ (by decide), ?_, ?_, ?_, ?_⟩
  · intro f hf
    have k : ∀ {d} {x : BitVec 32}, (d + 4 ≤ 68 ∨ 84 ≤ d) → d + 4 ≤ 164 → u₃.mem.readW (off (State.addr (arg s 5)) d) 32 = x →
        u.mem.readW (off (State.addr (arg s 5)) d) 32 = x := fun hd' hd'' h => keep_word O₄ hd' (by omega) h
    simp only [signFields, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact k (d := 96) (by decide) (by decide) F₁
    · exact k (d := 64) (by decide) (by decide) F₂
    · exact k (d := 100) (by decide) (by decide) F₃
    · exact k (d := 88) (by decide) (by decide) F₄
    · exact k (d := 104) (by decide) (by decide) F₅
    · exact k (d := 92) (by decide) (by decide) F₆
    · exact k (d := 108) (by decide) (by decide) F₇
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
  · exact (((v₁.rest (by decide)).trans (R₂.mono (by decide))).trans (R₃.mono (by decide))).trans (R₄.mono (by decide))

theorem verifyEntry_ok {s : State} (h : verifyPre s) :
    WP isa (.block Entry.verifyEntry) s
      (Installed s (State.addr (arg s 4)) ((arg s 5).toNat * 8) (verifyFields s)) := by
  obtain ⟨hsp, hrd, hwr, _, _, _, hsa, _, _, _, hsb, hv, _, _, hsw⟩ := h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hs16 : 16384 ≤ (arg s 5).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega
  have hd : Region.Disjoint ⟨State.addr s.sp, 4 * 6⟩ ⟨State.addr (arg s 4), (arg s 5).toNat * 8⟩ := hsa.symm
  show WP isa (.block (((Entry.openScratch 4) ++ Entry.verifyArguments.flatMap Entry.saveArgument) ++
    Entry.keyPointers)) s _
  simp only [Entry.openScratch, List.append_assoc, List.singleton_append]
  refine wp_ldrSp (i := 4) (by decide) (args_read (n := 6) (by rw [hrd]; simp) hsp 4 (by decide)) fun u₁ v₁ => ?_
  have w₁ := openScratch_ws v₁ ((arg s 5).toNat * 8) (by rw [hwr]; simp) hsb
  have aa : ArgsApart s (State.addr (arg s 4)) 6 := args_apart hd hsp (by omega)
  refine VG.Proof.X25519.Arm.WP.append (save_ok w₁ (by omega)) fun u₂ ⟨S₂, R₂, O₂⟩ => ?_
  have w₂ := w₁.of_rest R₂ (by decide)
  have hsp₂ : u₂.sp = s.sp := by rw [R₂.sp, v₁.sp]
  rw [v₁.mem] at O₂
  have A₂ : ∀ i < 6, stackArg u₂ i = stackArg s i := fun i hi =>
    stackArg_apart O₂ hsp₂ hd hi hsp (by omega) (by omega)
  have r₂ : ArgsRead u₂ 6 := (args_read (n := 6) (by rw [hrd]; simp) hsp).keep (by rw [R₂.rd, v₁.rd])
    (by rw [R₂.wr, v₁.wr]) hsp₂
  refine VG.Proof.X25519.Arm.WP.append (verifyArgs_ok w₂ (by omega) r₂ (aa.sp hsp₂))
    fun u₃ ⟨F₁, F₂, F₃, F₄, F₅, F₆, R₃, O₃, A₃⟩ => ?_
  have w₃ := w₂.of_rest R₃ (by decide)
  have g0 : u₂.gpr .r0 = s.gpr .r0 := by rw [R₂.gpr _ (by decide), v₁.other _ (by decide)]
  have g2 : u₂.gpr .r2 = s.gpr .r2 := by rw [R₂.gpr _ (by decide), v₁.other _ (by decide)]
  have g3 : u₂.gpr .r3 = s.gpr .r3 := by rw [R₂.gpr _ (by decide), v₁.other _ (by decide)]
  rw [g0] at F₁
  rw [g2] at F₂
  rw [g3] at F₃
  rw [A₂ 0 (by decide)] at F₄
  rw [A₂ 2 (by decide)] at F₅
  rw [A₂ 3 (by decide)] at F₆
  refine WP.mono (keyPointers_ok w₃ (by omega) F₁ F₂ F₃) fun u ⟨K₁, K₂, K₃, K₄, R₄, O₄⟩ => ⟨w₃.of_rest R₄ (by decide), ?_, ?_, ?_, ?_⟩
  · intro f hf
    have k : ∀ {d} {x : BitVec 32}, (d + 4 ≤ 68 ∨ 84 ≤ d) → d + 4 ≤ 164 → u₃.mem.readW (off (State.addr (arg s 4)) d) 32 = x →
        u.mem.readW (off (State.addr (arg s 4)) d) 32 = x := fun hd' hd'' h => keep_word O₄ hd' (by omega) h
    simp only [verifyFields, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact k (d := 64) (by decide) (by decide) F₁
    · exact k (d := 100) (by decide) (by decide) F₂
    · exact k (d := 104) (by decide) (by decide) F₃
    · exact k (d := 84) (by decide) (by decide) F₄
    · exact k (d := 92) (by decide) (by decide) F₅
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
  · exact (((v₁.rest (by decide)).trans (R₂.mono (by decide))).trans (R₃.mono (by decide))).trans (R₄.mono (by decide))

end VG.Proof.Dsa.Arm
