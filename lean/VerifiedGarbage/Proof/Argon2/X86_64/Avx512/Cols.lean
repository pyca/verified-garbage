import VerifiedGarbage.Proof.Argon2.X86_64.Avx512.Rows

/-!
# Argon2 on x86-64 with AVX-512: P on two columns

The registers of columns `2c` and `2c + 1` are four consecutive 64-byte
chunks of `cv` (`loadCols_ok`); P on both halves of them (`round_words`),
stored back (`storeCols_ok`), is P on both columns (`cols_ok`).
-/

namespace VG.Proof.Argon2.X86_64.Avx512

open VG VG.X86_64 VG.Spec.Argon2
open VG.Impl.Argon2.X86_64 (at_)
open VG.Impl.Argon2.X86_64.Avx512
open VG.Impl.Argon2.X86_64.Avx2 (vreg)
open VG.Proof.Argon2.X86_64 (off Scratch ea_at)
open VG.Proof.Argon2.X86_64.Avx2 (VKeep VKeep.refl cases_div4)
open VG.Proof.Poly1305.X86_64.Avx512 (qz)
open VG.Proof.Argon2 (gather gather_get)

/-- Where quadword `4h + j % 4` of register `j / 4` of columns `2c`, `2c + 1`
is: word `j` of column `2c + h`. -/
theorem colQ : ∀ c < 4, ∀ h < 2, ∀ j < 16,
    256 * c + 64 * (j / 4) + 8 * (4 * h + j % 4) = cvOff (16 * (j / 2) + 2 * (2 * c + h) + j % 2) := by
  decide

@[simp] theorem State.setMem_zmm (s : State) (m : Mem) (r : XReg) : (s.setMem m).zmm r = s.zmm r := by
  cases s; rfl

theorem loadCols_eq (c : Nat) : loadCols c =
    [.vmovdqu32Load .xmm0 (at_ .rcx (colOff c 0)), .vmovdqu32Load .xmm1 (at_ .rcx (colOff c 1)),
      .vmovdqu32Load .xmm2 (at_ .rcx (colOff c 2)), .vmovdqu32Load .xmm3 (at_ .rcx (colOff c 3))] := rfl

theorem storeCols_eq (c : Nat) : storeCols c =
    [.vmovdqu32Store (at_ .rcx (colOff c 0)) .xmm0, .vmovdqu32Store (at_ .rcx (colOff c 1)) .xmm1,
      .vmovdqu32Store (at_ .rcx (colOff c 2)) .xmm2, .vmovdqu32Store (at_ .rcx (colOff c 3)) .xmm3] := rfl

theorem colOff_read {s : State} {p : Addr} (hs : Scratch s p) {c k : Nat} (hc : c < 4) (hk : k < 4) :
    InRegions (s.rd ++ s.wr) (off p (colOff c k)) 64 :=
  hs.read (by unfold colOff; omega)

theorem loadCols_ok {c : Nat} (hc : c < 4) {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (.block (loadCols c)) s fun t =>
      (∀ h (hh : h < 2), words t h = gather (colIndex ⟨2 * c + h, by omega⟩) (cv s.mem p)) ∧
      t.mem = s.mem ∧ VKeep s t := by
  apply WP.of_runBlock
  simp only [loadCols_eq, runBlock_cons, runStep_some, runBlock_nil, exec, State.load512, ea_at,
    State.setZ_rd, State.setZ_wr, State.setZ_gpr, State.setZ_mem, hs.reg,
    colOff_read hs hc (show 0 < 4 by decide), colOff_read hs hc (show 1 < 4 by decide),
    colOff_read hs hc (show 2 < 4 by decide), colOff_read hs hc (show 3 < 4 by decide), ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun h hh => ?_, trivial, ?_⟩
  · apply Vector.ext
    intro j hj
    rw [words_get _ _ _ hj, show (gather (colIndex ⟨2 * c + h, by omega⟩) (cv s.mem p))[j] =
        (cv s.mem p)[colIndex ⟨2 * c + h, by omega⟩ ⟨j, hj⟩] from gather_get _ _ ⟨j, hj⟩,
      Fin.getElem_fin, cv_get _ _ _ (colIndex _ _).isLt]
    have hq := colQ c hc h hh j hj
    simp only [colIndex]
    rcases cases_div4 hj with e | e | e | e <;> rw [e] at hq ⊢ <;>
      simp (disch := omega) only [vreg, qz_load, ↓reduceIte, reduceCtorEq] <;>
      refine congrArg (Mem.readW _ · 64) (Offset.add_add_eq _ ?_) <;> unfold colOff <;> omega
  · exact (((setZ_vkeep _ _ _ _ _ _).trans (setZ_vkeep _ _ _ _ _ _)).trans
      (setZ_vkeep _ _ _ _ _ _)).trans (setZ_vkeep _ _ _ _ _ _)

theorem storeCols_ok {c : Nat} (hc : c < 4) {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (.block (storeCols c)) s fun t =>
      (∀ i (hi : i < 128), (cv t.mem p)[i] = if i % 16 / 4 = c then
        qz s (vreg (i / 32)) (cvQ i) else (cv s.mem p)[i]) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ VKeep s t := by
  apply WP.of_runBlock
  simp only [storeCols_eq, runBlock_cons, runStep_some, runBlock_nil, exec, State.store512_eq, ea_at,
    State.setMem_wr, State.setMem_gpr, State.setMem_mem, hs.reg,
    colOff_write hs hc (show 0 < 4 by decide), colOff_write hs hc (show 1 < 4 by decide),
    colOff_write hs hc (show 2 < 4 by decide), colOff_write hs hc (show 3 < 4 by decide), ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun i hi => ?_, ?_, ?_⟩
  · have hq := cvQ_lt i hi
    rw [cv_write512 _ _ hc (show 3 < 4 by decide) _ _ hi, cv_write512 _ _ hc (show 2 < 4 by decide) _ _ hi,
      cv_write512 _ _ hc (show 1 < 4 by decide) _ _ hi, cv_write512 _ _ hc (show 0 < 4 by decide) _ _ hi]
    simp only [State.setMem_zmm, zmm_qz _ _ hq]
    by_cases h : i % 16 / 4 = c
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
      have : i / 32 = 0 ∨ i / 32 = 1 ∨ i / 32 = 2 ∨ i / 32 = 3 := by omega
      rcases this with e | e | e | e <;> simp only [e, h, vreg, and_self, ite_true, ite_false,
        show (0 : Nat) ≠ 1 by decide, show (0 : Nat) ≠ 2 by decide, show (0 : Nat) ≠ 3 by decide,
        show (1 : Nat) ≠ 2 by decide, show (1 : Nat) ≠ 3 by decide, show (2 : Nat) ≠ 3 by decide,
        and_false]
    · simp only [h, false_and, ite_false]
  · repeat (first
      | refine Frame.writeW ?_ (List.mem_singleton_self _) _ (colOff_contains p hc (by decide))
      | exact Frame.refl _ _)
  · exact (((setMem_vkeep _ _).trans (setMem_vkeep _ _)).trans (setMem_vkeep _ _)).trans
      (setMem_vkeep _ _)

/-- P on columns `2c` and `2c + 1` of `cv`. -/
theorem cols_ok {c : Nat} (hc : c < 4) {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (cols c) s fun t =>
      cv t.mem p = permuteAt (colIndex ⟨(2 * c + 1) % 8, Nat.mod_lt _ (by decide)⟩)
        (permuteAt (colIndex ⟨2 * c % 8, Nat.mod_lt _ (by decide)⟩) (cv s.mem p)) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ VKeep s t := by
  unfold cols
  rw [WP.block_append_iff, WP.block_append_iff]
  refine (loadCols_ok hc hs).mono ?_
  rintro t1 ⟨hw1, hmem1, hk1⟩
  refine round_then ?_
  have hs2 : Scratch (zrun roundOps t1) p := (hs.of_vkeep hk1).of_vkeep (zrun_vkeep _ _)
  refine (storeCols_ok hc hs2).mono ?_
  rintro t ⟨hc', hf, hk⟩
  rw [zrun_mem, hmem1] at hc' hf
  refine ⟨?_, hf, hk1.trans ((zrun_vkeep _ _).trans hk)⟩
  apply Vector.ext
  intro i hi
  rw [hc' i hi, Proof.Argon2.colPair_get hc _ i hi]
  by_cases h : i % 16 / 4 = c
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h)]
    have hh : i % 16 / 2 % 2 < 2 := Nat.mod_lt _ (by decide)
    have e := congrArg (fun v : Vector Word 16 => v[2 * (i / 16) + i % 2]'(by omega))
      ((round_words t1 hh).trans (congrArg permute (hw1 _ hh)))
    simp only [words_get _ _ _ (show 2 * (i / 16) + i % 2 < 16 by omega),
      show (2 * (i / 16) + i % 2) / 4 = i / 32 by omega,
      show 4 * (i % 16 / 2 % 2) + (2 * (i / 16) + i % 2) % 4 = cvQ i by simp only [cvQ]; omega] at e
    rw [e]
    have er : (⟨2 * c + i % 16 / 2 % 2, by omega⟩ : Fin 8) = ⟨i % 16 / 2, by omega⟩ :=
      Fin.ext (by simp only; omega)
    rw [er]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false h)]

end VG.Proof.Argon2.X86_64.Avx512
