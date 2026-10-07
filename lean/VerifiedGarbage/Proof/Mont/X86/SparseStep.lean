import VerifiedGarbage.Proof.Mont.X86.Chain
import VerifiedGarbage.Impl.Mont.X86.Sparse

namespace VG.Proof.Mont.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Proof.Mont

/-- A word of an addition, with the carry in `cin` (none for `add`). -/
theorem sparseStepAdd_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {op : AluOp} {cin : Bool}
    (hop : (op = .add ∧ cin = false) ∨ (op = .adc ∧ s.cf = some cin)) {acc i j : Nat} (first : Bool)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i))
    (hacc : 4 * i + (acc + 4 * j) + 4 ≤ size) :
    WP isa (.block (sparseStep acc j op first)) s fun u =>
      Outside base (4 * i + (acc + 4 * j)) 4 s.mem u.mem ∧
      (∃ c, u.cf = some c ∧ w32 u.mem base (4 * i + (acc + 4 * j)) + 2 ^ 32 * c.toNat =
        w32 s.mem base (4 * i + (acc + 4 * j)) + (if first then (s.gpr .ecx).toNat else 0) + cin.toNat) ∧
      Keeps [.eax] s u := by
  have hn := hs.nowrap
  simp only [sparseStep]
  refine wp_movS (readSrc_at hs hp hacc) fun s₁ u₁ cf₁ => ?_
  have hs₁ := hs.of_keeps u₁.keeps (by decide)
  have hx := (s.mem.readW (off base (4 * i + (acc + 4 * j))) 32).isLt
  have hv : readSrc s₁ (if first then .reg .ecx else .imm 0) = some (if first then s.gpr .ecx else 0) := by
    cases first <;> simp only [Bool.false_eq_true, ite_false, ite_true, readSrc]
    exact congrArg some (u₁.other _ (by decide))
  have hy := (s.gpr .ecx).isLt
  have hp₁ : s₁.gpr .ebp = s₁.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [u₁.other _ (by decide), u₁.other _ (by decide)]; exact hp
  rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, hc⟩
  · refine wp_addS hv fun s₂ u₂ c₂ => ?_
    have hs₂ := hs₁.of_keeps u₂.keeps (by decide)
    have hp₂ : s₂.gpr .ebp = s₂.gpr .edi + BitVec.ofNat 32 (4 * i) := by
      rw [u₂.other _ (by decide), u₂.other _ (by decide)]; exact hp₁
    refine wp_storeS (hs₂.ea_at hp₂ (d := acc + 4 * j) (by omega)) (hs₂.write (n := 4) (by omega))
      fun s₃ m₃ => WP.block_nil ⟨?_, ⟨_, by rw [m₃.cf, c₂], ?_⟩, (u₁.keeps.trans (u₂.keeps)).trans (m₃.keeps _)⟩
    · rw [m₃.mem, u₂.mem, u₁.mem]; exact writeW32_outside _ _ _ (by omega)
    · rw [m₃.mem, w32_write_self, u₂.gpr, BitVec.toNat_add, u₁.gpr]
      simp only [w32]
      have hvn : (if first then s.gpr .ecx else (0 : BitVec 32)).toNat = (if first then (s.gpr .ecx).toNat else 0) := by cases first <;> rfl
      rw [hvn]
      have hy' : (if first then (s.gpr .ecx).toNat else 0) < 2 ^ 32 := by cases first <;> simp_all
      by_cases h : 2 ^ 32 ≤ (s.mem.readW (off base (4 * i + (acc + 4 * j))) 32).toNat +
          (if first then (s.gpr .ecx).toNat else 0) <;>
        simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega
  · refine wp_adcS hv (by rw [cf₁]; exact hc) fun s₂ u₂ c₂ => ?_
    have hs₂ := hs₁.of_keeps u₂.keeps (by decide)
    have hp₂ : s₂.gpr .ebp = s₂.gpr .edi + BitVec.ofNat 32 (4 * i) := by
      rw [u₂.other _ (by decide), u₂.other _ (by decide)]; exact hp₁
    refine wp_storeS (hs₂.ea_at hp₂ (d := acc + 4 * j) (by omega)) (hs₂.write (n := 4) (by omega))
      fun s₃ m₃ => WP.block_nil ⟨?_, ⟨_, by rw [m₃.cf, c₂], ?_⟩, (u₁.keeps.trans (u₂.keeps)).trans (m₃.keeps _)⟩
    · rw [m₃.mem, u₂.mem, u₁.mem]; exact writeW32_outside _ _ _ (by omega)
    · rw [m₃.mem, w32_write_self, u₂.gpr, add3_toNat, u₁.gpr]
      simp only [w32]
      have := Bool.toNat_le cin
      have hvn : (if first then s.gpr .ecx else (0 : BitVec 32)).toNat = (if first then (s.gpr .ecx).toNat else 0) := by cases first <;> rfl
      rw [hvn]
      have hy' : (if first then (s.gpr .ecx).toNat else 0) < 2 ^ 32 := by cases first <;> simp_all
      by_cases h : 2 ^ 32 ≤ (s.mem.readW (off base (4 * i + (acc + 4 * j))) 32).toNat +
          (if first then (s.gpr .ecx).toNat else 0) + cin.toNat <;>
        simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

/-- A word of a subtraction, with the borrow in `cin` (none for `sub`). -/
theorem sparseStepSub_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {op : AluOp} {cin : Bool}
    (hop : (op = .sub ∧ cin = false) ∨ (op = .sbb ∧ s.cf = some cin)) {acc i j : Nat} (first : Bool)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i))
    (hacc : 4 * i + (acc + 4 * j) + 4 ≤ size) :
    WP isa (.block (sparseStep acc j op first)) s fun u =>
      Outside base (4 * i + (acc + 4 * j)) 4 s.mem u.mem ∧
      (∃ c, u.cf = some c ∧ w32 u.mem base (4 * i + (acc + 4 * j)) + (if first then (s.gpr .ecx).toNat else 0) + cin.toNat =
        w32 s.mem base (4 * i + (acc + 4 * j)) + 2 ^ 32 * c.toNat) ∧
      Keeps [.eax] s u := by
  have hn := hs.nowrap
  simp only [sparseStep]
  refine wp_movS (readSrc_at hs hp hacc) fun s₁ u₁ cf₁ => ?_
  have hs₁ := hs.of_keeps u₁.keeps (by decide)
  have hx := (s.mem.readW (off base (4 * i + (acc + 4 * j))) 32).isLt
  have hv : readSrc s₁ (if first then .reg .ecx else .imm 0) = some (if first then s.gpr .ecx else 0) := by
    cases first <;> simp only [Bool.false_eq_true, ite_false, ite_true, readSrc]
    exact congrArg some (u₁.other _ (by decide))
  have hy := (s.gpr .ecx).isLt
  have hp₁ : s₁.gpr .ebp = s₁.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [u₁.other _ (by decide), u₁.other _ (by decide)]; exact hp
  rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, hc⟩
  · refine wp_subS hv fun s₂ u₂ c₂ => ?_
    have hs₂ := hs₁.of_keeps u₂.keeps (by decide)
    have hp₂ : s₂.gpr .ebp = s₂.gpr .edi + BitVec.ofNat 32 (4 * i) := by
      rw [u₂.other _ (by decide), u₂.other _ (by decide)]; exact hp₁
    refine wp_storeS (hs₂.ea_at hp₂ (d := acc + 4 * j) (by omega)) (hs₂.write (n := 4) (by omega))
      fun s₃ m₃ => WP.block_nil ⟨?_, ⟨_, by rw [m₃.cf, c₂], ?_⟩, (u₁.keeps.trans (u₂.keeps)).trans (m₃.keeps _)⟩
    · rw [m₃.mem, u₂.mem, u₁.mem]; exact writeW32_outside _ _ _ (by omega)
    · rw [m₃.mem, w32_write_self, u₂.gpr, sub_toNat, u₁.gpr]
      simp only [w32]
      have hvn : (if first then s.gpr .ecx else (0 : BitVec 32)).toNat = (if first then (s.gpr .ecx).toNat else 0) := by cases first <;> rfl
      rw [hvn]
      have hy' : (if first then (s.gpr .ecx).toNat else 0) < 2 ^ 32 := by cases first <;> simp_all
      by_cases h : (s.mem.readW (off base (4 * i + (acc + 4 * j))) 32).toNat <
          (if first then (s.gpr .ecx).toNat else 0) <;>
        simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega
  · refine wp_sbbS hv (by rw [cf₁]; exact hc) fun s₂ u₂ c₂ => ?_
    have hs₂ := hs₁.of_keeps u₂.keeps (by decide)
    have hp₂ : s₂.gpr .ebp = s₂.gpr .edi + BitVec.ofNat 32 (4 * i) := by
      rw [u₂.other _ (by decide), u₂.other _ (by decide)]; exact hp₁
    refine wp_storeS (hs₂.ea_at hp₂ (d := acc + 4 * j) (by omega)) (hs₂.write (n := 4) (by omega))
      fun s₃ m₃ => WP.block_nil ⟨?_, ⟨_, by rw [m₃.cf, c₂], ?_⟩, (u₁.keeps.trans (u₂.keeps)).trans (m₃.keeps _)⟩
    · rw [m₃.mem, u₂.mem, u₁.mem]; exact writeW32_outside _ _ _ (by omega)
    · rw [m₃.mem, w32_write_self, u₂.gpr, sub3_toNat, u₁.gpr]
      simp only [w32]
      have := Bool.toNat_le cin
      have hvn : (if first then s.gpr .ecx else (0 : BitVec 32)).toNat = (if first then (s.gpr .ecx).toNat else 0) := by cases first <;> rfl
      rw [hvn]
      have hy' : (if first then (s.gpr .ecx).toNat else 0) < 2 ^ 32 := by cases first <;> simp_all
      by_cases h : (s.mem.readW (off base (4 * i + (acc + 4 * j))) 32).toNat <
          (if first then (s.gpr .ecx).toNat else 0) + cin.toNat <;>
        simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega


end VG.Proof.Mont.X86
