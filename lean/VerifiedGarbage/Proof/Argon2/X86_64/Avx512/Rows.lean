import VerifiedGarbage.Proof.Argon2.X86_64.Avx512.Mem
import VerifiedGarbage.Proof.Argon2.PermuteMany
import VerifiedGarbage.Proof.Argon2.X86_64.Compress

/-!
# Argon2 on x86-64 with AVX-512: P on two rows

Rows `2p` and `2p + 1` of R (`[0, 1024)` of scratch, `blockAt`) are loaded
into the halves of `zmm0`–`zmm3` (`loadRows_ok`), permuted (`round_words`)
and stored to their places in the block P permutes, as scratch holds it by
pairs of columns (`cv`, `storeRows_ok`): `rows_ok`.
-/

namespace VG.Proof.Argon2.X86_64.Avx512

open VG VG.X86_64 VG.Spec.Argon2
open VG.Impl.Argon2.X86_64 (at_)
open VG.Impl.Argon2.X86_64.Avx512
open VG.Impl.Argon2.X86_64.Avx2 (vreg)
open VG.Proof.Argon2.X86_64 (off Scratch ea_at blockAt_get)
open VG.Proof.Argon2.X86_64.Avx2 (VKeep VKeep.refl cases_div4)
open VG.Proof.Poly1305.X86_64.Avx512 (qz qz_vshufi32x4)
open VG.Proof.Poly1305.X86_64.Avx2 (sel4)
open VG.Proof.Argon2 (gather gather_get)

/-! ## Selectors of `vshufi32x4` -/

theorem sel4_44 {m : Nat} (hm : m < 4) : sel4 (0x44 : BitVec 8).toNat m = m % 2 := by
  rcases cases4 hm with rfl | rfl | rfl | rfl <;> rfl
theorem sel4_ee {m : Nat} (hm : m < 4) : sel4 (0xee : BitVec 8).toNat m = 2 + m % 2 := by
  rcases cases4 hm with rfl | rfl | rfl | rfl <;> rfl
theorem sel4_d8 {m : Nat} (hm : m < 4) : sel4 (0xd8 : BitVec 8).toNat m = 2 * (m % 2) + m / 2 := by
  rcases cases4 hm with rfl | rfl | rfl | rfl <;> rfl
theorem sel4_88 {m : Nat} (hm : m < 4) : sel4 (0x88 : BitVec 8).toNat m = 2 * (m % 2) := by
  rcases cases4 hm with rfl | rfl | rfl | rfl <;> rfl
theorem sel4_dd {m : Nat} (hm : m < 4) : sel4 (0xdd : BitVec 8).toNat m = 2 * (m % 2) + 1 := by
  rcases cases4 hm with rfl | rfl | rfl | rfl <;> rfl

theorem vreg_ne4 (i : Nat) : vreg i ≠ .xmm4 := by unfold vreg; split <;> decide

@[simp] theorem State.setMem_mxcsr' (s : State) (m : Mem) : (s.setMem m).mxcsr = s.mxcsr := by
  cases s; rfl

theorem setMem_vkeep (s : State) (m : Mem) : VKeep s (s.setMem m) := by
  cases s; exact ⟨rfl, rfl, rfl, rfl⟩

theorem zop_vkeep (o : ZOp) (s : State) : VKeep s (o.exec s) :=
  ⟨ZOp.exec_gpr o s, ZOp.exec_rd o s, ZOp.exec_wr o s, ZOp.exec_mxcsr o s⟩

theorem setZ_vkeep (s : State) (r : XReg) (a b c d : BitVec 128) : VKeep s (s.setZ r a b c d) :=
  ⟨State.setZ_gpr _ _ _ _ _ _, State.setZ_rd _ _ _ _ _ _, State.setZ_wr _ _ _ _ _ _,
    State.setZ_mxcsr _ _ _ _ _ _⟩

theorem zrun_vkeep (os : List ZOp) (s : State) : VKeep s (zrun os s) :=
  ⟨zrun_gpr os s, zrun_rd os s, zrun_wr os s, zrun_mxcsr os s⟩

/-- The round, as a block, from the state the loads leave. -/
theorem round_then {s : State} {Q : State → Prop} (h : Q (zrun roundOps s)) :
    WP isa (.block round) s Q := by
  rw [round_eq]
  exact WP.of_runBlock ⟨_, runBlock_zops _ _, h⟩

/-! ## Loading two rows -/

theorem loadRows_ok {pp : Nat} (hp : pp < 4) {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (.block (loadRows pp)) s fun t =>
      (∀ h (hh : h < 2), words t h = gather (rowIndex ⟨2 * pp + h, by omega⟩) (blockAt s.mem p)) ∧
      t.mem = s.mem ∧ VKeep s t := by
  have r0 := hs.read (d := 256 * pp) (n := 64) (by omega)
  have r1 := hs.read (d := 256 * pp + 64) (n := 64) (by omega)
  have r2 := hs.read (d := 256 * pp + 128) (n := 64) (by omega)
  have r3 := hs.read (d := 256 * pp + 192) (n := 64) (by omega)
  apply WP.of_runBlock
  simp only [loadRows, runBlock_cons, runStep_some, runBlock_nil, exec, State.load512, ea_at,
    State.setZ_rd, State.setZ_wr, State.setZ_gpr, State.setZ_mem, hs.reg, r0, r1, r2, r3, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun h hh => ?_, by simp only [ZOp.exec_mem, State.setZ_mem], ?_⟩
  · apply Vector.ext
    intro j hj
    have hk : j % 4 < 4 := Nat.mod_lt _ (by decide)
    rw [words_get _ _ _ hj, show (gather (rowIndex ⟨2 * pp + h, by omega⟩) (blockAt s.mem p))[j] =
        (blockAt s.mem p)[rowIndex ⟨2 * pp + h, by omega⟩ ⟨j, hj⟩] from gather_get _ _ ⟨j, hj⟩,
      blockAt_get]
    simp only [rowIndex]
    rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;>
      rcases cases_div4 hj with e | e | e | e <;> rw [e] <;>
      simp (disch := omega) only [vreg, qz_vshufi32x4, qz_load, sel4_44, sel4_ee, ↓reduceIte,
        reduceCtorEq, show (4 * 0 + j % 4) / 2 < 2 by omega, show ¬ (4 * 1 + j % 4) / 2 < 2 by omega] <;>
      refine congrArg (Mem.readW _ · 64) (Offset.add_add_eq _ ?_) <;> omega
  · exact (((((((setZ_vkeep _ _ _ _ _ _).trans (setZ_vkeep _ _ _ _ _ _)).trans
      (setZ_vkeep _ _ _ _ _ _)).trans (setZ_vkeep _ _ _ _ _ _)).trans (zop_vkeep _ _)).trans
      (zop_vkeep _ _)).trans (zop_vkeep _ _)).trans (zop_vkeep _ _)

/-! ## Storing two rows -/

/-- The working half of scratch contains the chunk at `colOff c k`. -/
theorem colOff_contains (p : Addr) {c k : Nat} (hc : c < 4) (hk : k < 4) :
    (⟨off p 1024, 1024⟩ : Region).Contains (off p (colOff c k)) 64 :=
  Offset.contains p (by unfold colOff; omega) (by unfold colOff; omega) (by omega)

theorem colOff_write {s : State} {p : Addr} (hs : Scratch s p) {c k : Nat} (hc : c < 4) (hk : k < 4) :
    InRegions s.wr (off p (colOff c k)) 64 :=
  hs.write (by unfold colOff; omega)

/-- The quadword `vshufi32x4` with `0xd8` moves to quadword `cvQ i`. -/
theorem rowQ : ∀ i < 128, 2 * sel4 (0xd8 : BitVec 8).toNat (cvQ i / 2) + cvQ i % 2 =
    4 * (i / 16 % 2) + i % 4 := by decide

def storeRow (pp k : Nat) : List Instr :=
  [.zop (.vshufi32x4 .xmm4 (vreg k) (vreg k) 0xd8), .vmovdqu32Store (at_ .rcx (colOff k pp)) .xmm4]

theorem storeRows_eq (pp : Nat) : storeRows pp = (List.range 4).flatMap (storeRow pp) := rfl

/-- What storing register `k` of rows `2p`, `2p + 1` leaves. -/
structure RowStored (p : Addr) (pp n : Nat) (s t : State) : Prop where
  cv : ∀ i (hi : i < 128), (cv t.mem p)[i] = if i % 16 / 4 < n ∧ i / 32 = pp then
    qz s (vreg (i % 16 / 4)) (4 * (i / 16 % 2) + i % 4) else (cv s.mem p)[i]
  frame : Frame [⟨off p 1024, 1024⟩] s.mem t.mem
  keep : VKeep s t
  regs : ∀ r, r ≠ .xmm4 → ∀ e < 8, qz t r e = qz s r e

theorem storeRow_ok {pp k : Nat} (hp : pp < 4) (hk : k < 4) {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (.block (storeRow pp k)) s fun t =>
      (∀ i (hi : i < 128), (cv t.mem p)[i] = if i % 16 / 4 = k ∧ i / 32 = pp then
        qz s (vreg k) (4 * (i / 16 % 2) + i % 4) else (cv s.mem p)[i]) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ VKeep s t ∧
      (∀ r, r ≠ .xmm4 → ∀ e < 8, qz t r e = qz s r e) := by
  apply WP.of_runBlock
  simp only [storeRow, runBlock_cons, runStep_some, runBlock_nil, exec, State.store512_eq, ea_at,
    ZOp.exec_wr, ZOp.exec_gpr, ZOp.exec_mem, hs.reg, colOff_write hs hk hp, ite_true,
    Option.some.injEq, exists_eq_left', State.setMem_mem]
  refine ⟨fun i hi => ?_, ?_, (zop_vkeep _ _).trans (setMem_vkeep _ _), fun r hr e he => ?_⟩
  · rw [cv_write512 _ _ hk hp _ _ hi]
    split
    · rw [zmm_qz _ _ (cvQ_lt i hi), qz_vshufi32x4 _ _ _ _ _ _ (cvQ_lt i hi),
        ite_eq_left_of_eq_true _ _ (eq_true rfl), ite_self]
      exact congrArg _ (rowQ i hi)
    · rfl
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (colOff_contains p hk hp)
  · rw [qz_setMem, qz_vshufi32x4 _ _ _ _ _ _ he, ite_eq_right_of_eq_false _ _ (eq_false hr)]

theorem storeRows_prefix {pp : Nat} (hp : pp < 4) (n : Nat) (hn : n ≤ 4) {s : State} {p : Addr}
    (hs : Scratch s p) :
    WP isa (.block ((List.range n).flatMap (storeRow pp))) s (RowStored p pp n s) := by
  induction n with
  | zero => exact WP.block_nil ⟨fun i hi => by simp, Frame.refl _ _, VKeep.refl s, fun _ _ _ _ => rfl⟩
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    apply WP.block_append
    refine (ih (by omega)).mono ?_
    rintro t ⟨hc, hf, hk, hr⟩
    refine (storeRow_ok hp (k := n) (by omega) (hs.of_vkeep hk)).mono ?_
    rintro u ⟨hc', hf', hk', hr'⟩
    refine ⟨fun i hi => ?_, hf.trans hf', hk.trans hk', fun r h e he => (hr' r h e he).trans (hr r h e he)⟩
    rw [hc' i hi, hr _ (vreg_ne4 n) _ (by omega), hc i hi]
    by_cases h1 : i % 16 / 4 = n ∧ i / 32 = pp
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true (by omega)), h1.1]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      by_cases h2 : i % 16 / 4 < n ∧ i / 32 = pp
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h2), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

/-! ## Two rows -/

/-- P on rows `2p` and `2p + 1` of R, stored to `cv`. -/
theorem rows_ok {pp : Nat} (hp : pp < 4) {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (rows pp) s fun t =>
      (∀ i (hi : i < 128), (cv t.mem p)[i] = if i / 32 = pp then
        (permute (gather (rowIndex ⟨i / 16, by omega⟩) (blockAt s.mem p)))[i % 16]'(by omega)
        else (cv s.mem p)[i]) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ VKeep s t := by
  unfold rows
  rw [WP.block_append_iff, WP.block_append_iff]
  refine (loadRows_ok hp hs).mono ?_
  rintro t1 ⟨hw1, hmem1, hk1⟩
  refine round_then ?_
  have hs2 : Scratch (zrun roundOps t1) p := (hs.of_vkeep hk1).of_vkeep (zrun_vkeep _ _)
  rw [storeRows_eq]
  refine (storeRows_prefix hp 4 (by decide) hs2).mono ?_
  rintro t ⟨hc, hf, hk, -⟩
  rw [zrun_mem, hmem1] at hc hf
  refine ⟨fun i hi => ?_, hf, hk1.trans ((zrun_vkeep _ _).trans hk)⟩
  rw [hc i hi]
  by_cases h : i / 32 = pp
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), ite_eq_left_of_eq_true _ _ (eq_true h)]
    have hh : i / 16 % 2 < 2 := Nat.mod_lt _ (by decide)
    have e := congrArg (fun v : Vector Word 16 => v[i % 16]'(by omega))
      ((round_words t1 hh).trans (congrArg permute (hw1 _ hh)))
    simp only [words_get _ _ _ (show i % 16 < 16 by omega), show i % 16 % 4 = i % 4 by omega] at e
    rw [e]
    have er : (⟨2 * pp + i / 16 % 2, by omega⟩ : Fin 8) = ⟨i / 16, by omega⟩ := Fin.ext (by simp only; omega)
    rw [er]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false h)]

end VG.Proof.Argon2.X86_64.Avx512
