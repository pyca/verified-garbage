import VerifiedGarbage.Proof.Argon2.X86_64.Avx2.Gb
import VerifiedGarbage.Proof.Argon2.X86_64.Words
import VerifiedGarbage.Proof.Argon2.Permutation

/-!
# Argon2 on x86-64 with AVX2: rows and columns in scratch

A row of the block P permutes (`working`, `[1024, 2048)` of scratch) is
loaded into `ymm0`–`ymm3` with four 32-byte loads, permuted (`round_words`)
and stored back; a column with two 16-byte loads per register, joined by
`vinserti128`, and two 16-byte stores. Either way the block becomes
`Spec.Argon2.permuteAt` of the row or column (`row_ok`, `col_ok`).
-/

namespace VG.Proof.Argon2.X86_64.Avx2

open VG VG.X86_64 VG.Spec.Argon2
open VG.Impl.Argon2.X86_64 (at_)
open VG.Impl.Argon2.X86_64.Avx2
open VG.Proof.Argon2.X86_64 (off word working working_get Scratch ea_at)
open VG.Proof.Argon2 (gather gather_get eq_scatter rowIndex_injective colIndex_injective)
open VG.Proof.Poly1305.X86_64.Avx2 (qw qword256_ymm qword256_eq qw_setV256 qw_setV128 qw_lane)

/-! ## What the vector code keeps -/

/-- The general-purpose registers, permissions and MXCSR are those of `s`. -/
structure VKeep (s t : State) : Prop where
  gpr : t.gpr = s.gpr
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr

theorem VKeep.refl (s : State) : VKeep s s := ⟨rfl, rfl, rfl, rfl⟩

theorem VKeep.trans {s t u : State} (h : VKeep s t) (h' : VKeep t u) : VKeep s u :=
  ⟨h'.gpr.trans h.gpr, h'.rd.trans h.rd, h'.wr.trans h.wr, h'.mxcsr.trans h.mxcsr⟩

theorem _root_.VG.Proof.Argon2.X86_64.Scratch.of_vkeep {s t : State} {p : Addr} (hs : Scratch s p) (h : VKeep s t) : Scratch t p :=
  ⟨by rw [h.gpr]; exact hs.reg, h.wr ▸ hs.wr⟩

theorem vrun_vkeep (os : List VOp) (s : State) : VKeep s (vrun os s) :=
  ⟨vrun_gpr os s, vrun_rd os s, vrun_wr os s, vrun_mxcsr os s⟩

/-! ## Loads and stores, quadword by quadword -/

theorem qword256_readW (m : Mem) (a : Addr) {k : Nat} (hk : k < 4) :
    qword256 (m.readW a 256) k = m.readW (a + BitVec.ofNat 64 (8 * k)) 64 := by
  rw [qword256, show 64 * k = 8 * (8 * k) by omega]
  exact readW_extract _ _ (k := 8 * k) (n := 8) (by omega)

theorem qword_readW128 (m : Mem) (a : Addr) {k : Nat} (hk : k < 2) :
    qword (m.readW a 128) k = m.readW (a + BitVec.ofNat 64 (8 * k)) 64 := by
  rw [qword, show 64 * k = 8 * (8 * k) by omega]
  exact readW_extract _ _ (k := 8 * k) (n := 8) (by omega)

theorem qw_set256 (s : State) (d r : XReg) (v : BitVec 256) {k : Nat} (hk : k < 4) :
    qw (s.setV .l256 d (v.extractLsb' 0 128) (v.extractLsb' 128 128)) r k =
      if r = d then qword256 v k else qw s r k := by
  rw [qw_setV256]
  split
  · rw [qword256_eq]
    rcases VG.X86_64.cases4 hk with rfl | rfl | rfl | rfl <;> rfl
  · rfl

/-- A word of `working` after a 32-byte write to it. -/
theorem working_write256 (m : Mem) (p : Addr) {c : Nat} (hc : c < 32) (v : BitVec 256) (i : Fin 128) :
    (working (m.writeW (off p (1024 + 32 * c)) v) p)[i] =
      if i.val / 4 = c then qword256 v (i.val % 4) else (working m p)[i] := by
  rw [working_get, working_get]
  split
  · rename_i h
    have e : off p (1024 + 8 * i.val) = off p (1024 + 32 * c) + BitVec.ofNat 64 (8 * (i.val % 4)) :=
      (Offset.add_add_eq p (by omega)).symm
    rw [word, e]
    refine (readW_writeW_inside _ _ v (k := 8 * (i.val % 4)) (n := 8) (by omega) (by decide)).trans ?_
    rw [qword256, show 8 * (8 * (i.val % 4)) = 64 * (i.val % 4) by omega]
  · exact readW_writeW_off m p v (n := 8) (by omega) (by omega) (by omega)

/-- A word of `working` after a 16-byte write to it. -/
theorem working_write128 (m : Mem) (p : Addr) {c : Nat} (hc : c < 64) (v : BitVec 128) (i : Fin 128) :
    (working (m.writeW (off p (1024 + 16 * c)) v) p)[i] =
      if i.val / 2 = c then qword v (i.val % 2) else (working m p)[i] := by
  rw [working_get, working_get]
  split
  · rename_i h
    have e : off p (1024 + 8 * i.val) = off p (1024 + 16 * c) + BitVec.ofNat 64 (8 * (i.val % 2)) :=
      (Offset.add_add_eq p (by omega)).symm
    rw [word, e]
    refine (readW_writeW_inside _ _ v (k := 8 * (i.val % 2)) (n := 8) (by omega) (by decide)).trans ?_
    rw [qword, show 8 * (8 * (i.val % 2)) = 64 * (i.val % 2) by omega]
  · exact readW_writeW_off m p v (n := 8) (by omega) (by omega) (by omega)

/-- A row or column is permuted if its words are P of what they were and the
others are unchanged. -/
theorem permuteAt_of (index : Fin 16 → Fin 128) (hi : Function.Injective index) (b t : Block)
    (hg : ∀ j : Fin 16, t[index j] = (permute (gather index b))[j])
    (ho : ∀ k : Fin 128, (∀ j, index j ≠ k) → t[k] = b[k]) :
    t = Spec.Argon2.permuteAt index b :=
  eq_scatter index hi b t _ (Vector.ext fun j hj => by
    rw [show (gather index t)[j] = (gather index t)[(⟨j, hj⟩ : Fin 16)] from rfl, gather_get, hg]
    rfl) ho


@[simp] theorem State.setV_mxcsr (s : State) (len : VLen) (r : XReg) (lo hi : BitVec 128) :
    (s.setV len r lo hi).mxcsr = s.mxcsr := by
  cases s; rfl

theorem Masks.setV {s : State} (h : Masks s) {len : VLen} {d : XReg} {lo hi : BitVec 128}
    (h14 : d ≠ .xmm14) (h15 : d ≠ .xmm15) : Masks (s.setV len d lo hi) := by
  intro l hl
  cases len
  · simp only [State.lane_setV128, h14.symm, h15.symm, ite_false]; exact h l hl
  · simp only [State.lane_setV256, h14.symm, h15.symm, ite_false]; exact h l hl

/-! ## Rows -/

theorem loadRow_eq (i : Nat) : loadRow i =
    [.vmovdquLoad .l256 x0 (at_ .rcx (rowOff i 0)), .vmovdquLoad .l256 x1 (at_ .rcx (rowOff i 1)),
      .vmovdquLoad .l256 x2 (at_ .rcx (rowOff i 2)), .vmovdquLoad .l256 x3 (at_ .rcx (rowOff i 3))] :=
  rfl

theorem storeRow_eq (i : Nat) : storeRow i =
    [.vmovdquStore .l256 (at_ .rcx (rowOff i 0)) x0, .vmovdquStore .l256 (at_ .rcx (rowOff i 1)) x1,
      .vmovdquStore .l256 (at_ .rcx (rowOff i 2)) x2, .vmovdquStore .l256 (at_ .rcx (rowOff i 3)) x3] :=
  rfl

theorem loadRow_ok {i : Nat} (hi : i < 8) {s : State} {p : Addr} (hs : Scratch s p) (hm : Masks s) :
    WP isa (.block (loadRow i)) s fun t =>
      words t = gather (rowIndex ⟨i, hi⟩) (working s.mem p) ∧ t.mem = s.mem ∧ VKeep s t ∧ Masks t := by
  have r (k : Nat) (hk : k < 4) := hs.read (d := rowOff i k) (n := 32) (by unfold rowOff; omega)
  apply WP.of_runBlock
  simp only [loadRow_eq, runBlock_cons, runStep_some, runBlock_nil, exec, State.load256, ea_at,
    State.setV_rd, State.setV_wr, State.setV_gpr, State.setV_mem, hs.reg, r 0 (by decide),
    r 1 (by decide), r 2 (by decide), r 3 (by decide), ite_true, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, ⟨by simp only [State.setV_gpr], by simp only [State.setV_rd],
      by simp only [State.setV_wr], by simp only [State.setV_mxcsr]⟩,
    (((hm.setV (by decide) (by decide)).setV (by decide) (by decide)).setV (by decide)
      (by decide)).setV (by decide) (by decide)⟩
  apply Vector.ext
  intro j hj
  have hk : j % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [words_get _ _ hj, show (gather (rowIndex ⟨i, hi⟩) (working s.mem p))[j] =
      (working s.mem p)[rowIndex ⟨i, hi⟩ ⟨j, hj⟩] from gather_get _ _ ⟨j, hj⟩, working_get]
  rcases cases_div4 hj with e | e | e | e <;> rw [e] <;>
    simp only [vreg, qw_set256 _ _ _ _ hk, ↓reduceIte, reduceCtorEq, qword256_readW _ _ hk] <;>
    exact congrArg (Mem.readW _ · 64) (Offset.add_add_eq _ (by simp only [rowIndex, rowOff]; omega))


theorem ymm_setMem (s : State) (m : Mem) (r : XReg) : (s.setMem m).ymm r = s.ymm r := by
  cases s; rfl

theorem setMem_vkeep (s : State) (m : Mem) : VKeep s (s.setMem m) := by
  cases s; exact ⟨rfl, rfl, rfl, rfl⟩

theorem Masks.setMem {s : State} (h : Masks s) (m : Mem) : Masks (s.setMem m) := by
  intro l hl; simp only [State.setMem_lane]; exact h l hl

theorem qw_setMem (s : State) (m : Mem) (r : XReg) (k : Nat) : qw (s.setMem m) r k = qw s r k := by
  simp only [qw, State.setMem_lane]

/-- The region of `working` contains a write at `1024 + d`. -/
theorem working_contains (p : Addr) {d n : Nat} (h : d + n ≤ 1024) :
    (⟨off p 1024, 1024⟩ : Region).Contains (off p (1024 + d)) n :=
  Offset.contains p (by omega) (by omega) (by omega)

theorem storeRow_ok {i : Nat} (hi : i < 8) {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (.block (storeRow i)) s fun t =>
      (∀ w : Fin 128, (working t.mem p)[w] =
        if w.val / 16 = i then qw s (vreg (w.val % 16 / 4)) (w.val % 4) else (working s.mem p)[w]) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ VKeep s t ∧ words t = words s ∧
      (Masks s → Masks t) := by
  have w (k : Nat) (hk : k < 4) := hs.write (d := rowOff i k) (n := 32) (by unfold rowOff; omega)
  have o (k : Nat) : rowOff i k = 1024 + 32 * (4 * i + k) := by unfold rowOff; omega
  apply WP.of_runBlock
  simp only [storeRow_eq, runBlock_cons, runStep_some, runBlock_nil, exec, State.store256_eq, ea_at,
    State.setMem_wr, State.setMem_gpr, State.setMem_mem, ymm_setMem, hs.reg, w 0 (by decide),
    w 1 (by decide), w 2 (by decide), w 3 (by decide), ite_true, Option.some.injEq, exists_eq_left']
  simp only [o]
  refine ⟨fun x => ?_, ?_, ?_, ?_, fun h => ((((h.setMem _).setMem _).setMem _).setMem _)⟩
  · have hx := x.isLt
    simp only [working_write256 _ p (show 4 * i + 3 < 32 by omega),
      working_write256 _ p (show 4 * i + 2 < 32 by omega),
      working_write256 _ p (show 4 * i + 1 < 32 by omega),
      working_write256 _ p (show 4 * i + 0 < 32 by omega)]
    have hq : x.val % 4 < 4 := Nat.mod_lt _ (by decide)
    by_cases h : x.val / 16 = i
    · have : x.val % 16 / 4 = 0 ∨ x.val % 16 / 4 = 1 ∨ x.val % 16 / 4 = 2 ∨ x.val % 16 / 4 = 3 := by
        omega
      rcases this with e | e | e | e <;>
        simp only [h, ite_true, e, vreg, show x.val / 4 = 4 * i + x.val % 16 / 4 by omega,
          qword256_ymm _ _ hq] <;> simp
    · simp only [h, ite_false, show x.val / 4 ≠ 4 * i + 3 by omega, show x.val / 4 ≠ 4 * i + 2 by omega,
        show x.val / 4 ≠ 4 * i + 1 by omega, show x.val / 4 ≠ 4 * i + 0 by omega]
  · exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (working_contains p (by omega))).writeW
      (List.mem_singleton_self _) _ (working_contains p (by omega))).writeW
      (List.mem_singleton_self _) _ (working_contains p (by omega))).writeW
      (List.mem_singleton_self _) _ (working_contains p (by omega))
  · exact ((((setMem_vkeep _ _).trans (setMem_vkeep _ _)).trans (setMem_vkeep _ _)).trans
      (setMem_vkeep _ _))
  · apply Vector.ext; intro j hj
    simp only [words_get, qw_setMem]


/-- What a row or column step leaves. -/
structure Permuted (index : Fin 16 → Fin 128) (p : Addr) (s t : State) : Prop where
  working : working t.mem p = Spec.Argon2.permuteAt index (working s.mem p)
  frame : Frame [⟨off p 1024, 1024⟩] s.mem t.mem
  keep : VKeep s t
  masks : Masks t

/-- The round, as a block, from the state the loads leave. -/
theorem round_then {s : State} {Q : State → Prop} (h : Q (vrun roundOps s)) :
    WP isa (.block round) s Q := by
  rw [round_eq]
  exact WP.of_runBlock ⟨_, runBlock_vops _ _, h⟩

/-- P on row `i`. -/
theorem row_ok {i : Nat} (hi : i < 8) {s : State} {p : Addr} (hs : Scratch s p) (hm : Masks s) :
    WP isa (row i) s (Permuted (rowIndex ⟨i, hi⟩) p s) := by
  unfold row
  rw [WP.block_append_iff, WP.block_append_iff]
  refine (loadRow_ok hi hs hm).mono ?_
  rintro t1 ⟨hw1, hmem1, hk1, hm1⟩
  refine round_then ?_
  have hs2 : Scratch (vrun roundOps t1) p := (hs.of_vkeep hk1).of_vkeep (vrun_vkeep _ _)
  refine (storeRow_ok hi hs2).mono ?_
  rintro t ⟨hw, hf, hk, -, hmt⟩
  have hr := round_words hm1
  rw [vrun_mem, hmem1] at hw hf
  refine ⟨?_, hf, hk1.trans ((vrun_vkeep _ _).trans hk), hmt (round_masks hm1)⟩
  apply permuteAt_of _ (rowIndex_injective _)
  · intro j
    have hj := j.isLt
    rw [hw, ite_eq_left_of_eq_true _ _ (eq_true (by simp only [rowIndex]; omega)), ← hw1]
    have e := congrArg (fun v : Vector Word 16 => v[j.val]) hr
    simp only [words_get _ _ hj] at e
    simp only [rowIndex, show (16 * i + j.val) % 16 = j.val by omega,
      show (16 * i + j.val) % 4 = j.val % 4 by omega, e]
    rfl
  · intro k hk
    rw [hw, ite_eq_right_of_eq_false _ _ (eq_false fun h =>
      hk ⟨k.val % 16, by omega⟩ (Fin.ext (by simp only [rowIndex]; omega)))]


/-! ## Columns -/

theorem xmm_eq_lane (s : State) (r : XReg) : s.xmm r = s.lane r 0 := rfl

theorem loadCol_eq (j : Nat) : loadCol j = [
    .vmovdquLoad .l128 x0 (at_ .rcx (colOff j 0 false)), .vmovdquLoad .l128 .xmm4 (at_ .rcx (colOff j 0 true)),
    .vop (.vinserti128 x0 x0 .xmm4 1),
    .vmovdquLoad .l128 x1 (at_ .rcx (colOff j 1 false)), .vmovdquLoad .l128 .xmm4 (at_ .rcx (colOff j 1 true)),
    .vop (.vinserti128 x1 x1 .xmm4 1),
    .vmovdquLoad .l128 x2 (at_ .rcx (colOff j 2 false)), .vmovdquLoad .l128 .xmm4 (at_ .rcx (colOff j 2 true)),
    .vop (.vinserti128 x2 x2 .xmm4 1),
    .vmovdquLoad .l128 x3 (at_ .rcx (colOff j 3 false)), .vmovdquLoad .l128 .xmm4 (at_ .rcx (colOff j 3 true)),
    .vop (.vinserti128 x3 x3 .xmm4 1)] := rfl

theorem storeCol_eq (j : Nat) : storeCol j = [
    .vmovdquStore .l128 (at_ .rcx (colOff j 0 false)) x0, .vop (.vextracti128 .xmm4 x0 1),
    .vmovdquStore .l128 (at_ .rcx (colOff j 0 true)) .xmm4,
    .vmovdquStore .l128 (at_ .rcx (colOff j 1 false)) x1, .vop (.vextracti128 .xmm4 x1 1),
    .vmovdquStore .l128 (at_ .rcx (colOff j 1 true)) .xmm4,
    .vmovdquStore .l128 (at_ .rcx (colOff j 2 false)) x2, .vop (.vextracti128 .xmm4 x2 1),
    .vmovdquStore .l128 (at_ .rcx (colOff j 2 true)) .xmm4,
    .vmovdquStore .l128 (at_ .rcx (colOff j 3 false)) x3, .vop (.vextracti128 .xmm4 x3 1),
    .vmovdquStore .l128 (at_ .rcx (colOff j 3 true)) .xmm4] := rfl

theorem vinserti128_1 (s : State) (d a b : XReg) :
    (VOp.vinserti128 d a b 1).exec s = s.setV .l256 d (s.lane a 0) (s.xmm b) := rfl

theorem vextracti128_1 (s : State) (d a : XReg) :
    (VOp.vextracti128 d a 1).exec s = s.setV .l128 d (s.lane a 1) 0 := rfl

theorem colOff_eq (j k : Nat) (hi : Bool) :
    colOff j k hi = 1024 + 16 * (16 * k + j + if hi then 8 else 0) := by
  unfold colOff; cases hi <;> simp <;> omega

theorem loadCol_ok {c : Nat} (hc : c < 8) {s : State} {p : Addr} (hs : Scratch s p) (hm : Masks s) :
    WP isa (.block (loadCol c)) s fun t =>
      words t = gather (colIndex ⟨c, hc⟩) (working s.mem p) ∧ t.mem = s.mem ∧ VKeep s t ∧ Masks t := by
  have r (k : Nat) (hk : k < 4) (hi : Bool) :=
    hs.read (d := colOff c k hi) (n := 16) (by rw [colOff_eq]; cases hi <;> simp <;> omega)
  apply WP.of_runBlock
  simp only [loadCol_eq, runBlock_cons, runStep_some, runBlock_nil, exec, State.load128, ea_at,
    State.setV_rd, State.setV_wr, State.setV_gpr, State.setV_mem, hs.reg, r 0 (by decide), r 1 (by decide), r 2 (by decide),
    r 3 (by decide), ite_true, Option.map_some, Option.some.injEq, exists_eq_left', vinserti128_1]
  refine ⟨?_, trivial, ⟨by simp only [State.setV_gpr], by simp only [State.setV_rd],
    by simp only [State.setV_wr], by simp only [State.setV_mxcsr]⟩, ?_⟩
  · apply Vector.ext
    intro j hj
    have hk : j % 4 < 4 := Nat.mod_lt _ (by decide)
    rw [words_get _ _ hj, show (gather (colIndex ⟨c, hc⟩) (working s.mem p))[j] =
        (working s.mem p)[colIndex ⟨c, hc⟩ ⟨j, hj⟩] from gather_get _ _ ⟨j, hj⟩, working_get]
    have h2 : j % 4 / 2 = 0 ∨ j % 4 / 2 = 1 := by omega
    rcases cases_div4 hj with e | e | e | e <;> rw [e] <;> rcases h2 with h | h <;>
      simp only [vreg, qw, State.lane_setV256, State.lane_setV128, xmm_eq_lane, h, ↓reduceIte,
        reduceCtorEq, qword_readW128 _ _ (Nat.mod_lt _ (by decide) : j % 4 % 2 < 2)]
    all_goals exact congrArg (Mem.readW _ · 64) (Offset.add_add_eq _ (by
      simp only [colIndex, colOff, Bool.false_eq_true, ite_true, ite_false]; omega))
  · exact (((((((((((hm.setV (by decide) (by decide)).setV (by decide) (by decide)).setV (by decide)
      (by decide)).setV (by decide) (by decide)).setV (by decide) (by decide)).setV (by decide)
      (by decide)).setV (by decide) (by decide)).setV (by decide) (by decide)).setV (by decide)
      (by decide)).setV (by decide) (by decide)).setV (by decide) (by decide)).setV (by decide) (by decide)


@[simp] theorem State.setMem_mxcsr (s : State) (m : Mem) : (s.setMem m).mxcsr = s.mxcsr := by
  cases s; rfl

theorem vreg_ne4 (i : Nat) : vreg i ≠ .xmm4 := by
  unfold vreg; split <;> decide

theorem qw_col (s : State) {k b x : Nat} (h1 : x / 32 = k) (h2 : x / 16 % 2 = b) :
    qword (s.lane (vreg k) b) (x % 2) = qw s (vreg (x / 32)) (2 * (x / 16 % 2) + x % 2) := by
  rw [h1, h2, qw, show (2 * b + x % 2) / 2 = b by omega, show (2 * b + x % 2) % 2 = x % 2 by omega]

/-- Whether word `8 q + r` of the block is in row `2 k` of column `c`. -/
theorem col_cond (q r k c : Nat) (hr : r < 8) (hc : c < 8) :
    (8 * q + r = 16 * k + c) = (q = 2 * k ∧ r = c) := by
  apply propext; omega

/-- Whether word `8 q + r` of the block is in row `2 k + 1` of column `c`. -/
theorem col_cond8 (q r k c : Nat) (hr : r < 8) (hc : c < 8) :
    (8 * q + r = 16 * k + c + 8) = (q = 2 * k + 1 ∧ r = c) := by
  apply propext; omega

theorem storeCol_ok {c : Nat} (hc : c < 8) {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (.block (storeCol c)) s fun t =>
      (∀ w : Fin 128, (working t.mem p)[w] =
        if w.val % 16 / 2 = c then qw s (vreg (w.val / 32)) (2 * (w.val / 16 % 2) + w.val % 2)
        else (working s.mem p)[w]) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ VKeep s t ∧ words t = words s ∧
      (Masks s → Masks t) := by
  have w (k : Nat) (hk : k < 4) (hi : Bool) :=
    hs.write (d := colOff c k hi) (n := 16) (by rw [colOff_eq]; cases hi <;> simp <;> omega)
  apply WP.of_runBlock
  simp only [storeCol_eq, runBlock_cons, runStep_some, runBlock_nil, exec, State.store128_eq, ea_at,
    State.setMem_wr, State.setMem_gpr, State.setMem_mem, State.setV_wr, State.setV_gpr,
    State.setV_mem, State.setMem_xmm, hs.reg, w 0 (by decide), w 1 (by decide), w 2 (by decide),
    w 3 (by decide), ite_true, Option.some.injEq, exists_eq_left', vextracti128_1]
  simp only [colOff_eq, Bool.false_eq_true, Nat.add_zero, xmm_eq_lane,
    State.setMem_lane, State.lane_setV128, ↓reduceIte, reduceCtorEq]
  refine ⟨fun x => ?_, ?_, ?_, ?_, fun h => ?_⟩
  · have hx := x.isLt
    rw [working_write128 _ p (show 16 * 3 + c + 8 < 64 by omega),
      working_write128 _ p (show 16 * 3 + c < 64 by omega),
      working_write128 _ p (show 16 * 2 + c + 8 < 64 by omega),
      working_write128 _ p (show 16 * 2 + c < 64 by omega),
      working_write128 _ p (show 16 * 1 + c + 8 < 64 by omega),
      working_write128 _ p (show 16 * 1 + c < 64 by omega),
      working_write128 _ p (show 16 * 0 + c + 8 < 64 by omega),
      working_write128 _ p (show 16 * 0 + c < 64 by omega)]
    obtain ⟨q, hq16⟩ : ∃ q, x.val / 16 = q := ⟨_, rfl⟩
    have hr : x.val % 16 / 2 < 8 := by omega
    rw [show x.val / 2 = 8 * q + x.val % 16 / 2 by omega]
    simp only [col_cond _ _ _ _ hr hc, col_cond8 _ _ _ _ hr hc]
    by_cases h : x.val % 16 / 2 = c
    · simp only [h, and_true, ↓reduceIte]
      rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      · exact qw_col s (k := 0) (b := 0) (by omega) (by omega)
      · exact qw_col s (k := 0) (b := 1) (by omega) (by omega)
      · exact qw_col s (k := 1) (b := 0) (by omega) (by omega)
      · exact qw_col s (k := 1) (b := 1) (by omega) (by omega)
      · exact qw_col s (k := 2) (b := 0) (by omega) (by omega)
      · exact qw_col s (k := 2) (b := 1) (by omega) (by omega)
      · exact qw_col s (k := 3) (b := 0) (by omega) (by omega)
      · exact qw_col s (k := 3) (b := 1) (by omega) (by omega)
    · simp only [h, and_false, ↓reduceIte]
  · repeat (first
      | refine Frame.writeW ?_ (List.mem_singleton_self _) _ (working_contains p (by omega))
      | exact Frame.refl _ _)
  · exact ⟨by simp only [State.setMem_gpr, State.setV_gpr], by simp only [State.setMem_rd, State.setV_rd],
      by simp only [State.setMem_wr, State.setV_wr], by simp only [State.setMem_mxcsr, State.setV_mxcsr]⟩
  · apply Vector.ext; intro j hj
    simp only [words_get, qw_setMem, qw_setV128, vreg_ne4, ite_false]
  · exact ((((((((((((h.setMem _).setV (by decide) (by decide)).setMem _).setMem _).setV (by decide) (by decide)).setMem _).setMem _).setV (by decide) (by decide)).setMem _).setMem _).setV (by decide) (by decide)).setMem _)


/-- P on column `c`. -/
theorem col_ok {c : Nat} (hc : c < 8) {s : State} {p : Addr} (hs : Scratch s p) (hm : Masks s) :
    WP isa (col c) s (Permuted (colIndex ⟨c, hc⟩) p s) := by
  unfold col
  rw [WP.block_append_iff, WP.block_append_iff]
  refine (loadCol_ok hc hs hm).mono ?_
  rintro t1 ⟨hw1, hmem1, hk1, hm1⟩
  refine round_then ?_
  have hs2 : Scratch (vrun roundOps t1) p := (hs.of_vkeep hk1).of_vkeep (vrun_vkeep _ _)
  refine (storeCol_ok hc hs2).mono ?_
  rintro t ⟨hw, hf, hk, -, hmt⟩
  have hr := round_words hm1
  rw [vrun_mem, hmem1] at hw hf
  refine ⟨?_, hf, hk1.trans ((vrun_vkeep _ _).trans hk), hmt (round_masks hm1)⟩
  apply permuteAt_of _ (colIndex_injective _)
  · intro j
    have hj := j.isLt
    rw [hw, ite_eq_left_of_eq_true _ _ (eq_true (by simp only [colIndex]; omega)), ← hw1]
    have e := congrArg (fun v : Vector Word 16 => v[j.val]) hr
    simp only [words_get _ _ hj] at e
    simp only [colIndex, show (16 * (j.val / 2) + 2 * c + j.val % 2) / 32 = j.val / 4 by omega,
      show 2 * ((16 * (j.val / 2) + 2 * c + j.val % 2) / 16 % 2) + (16 * (j.val / 2) + 2 * c +
        j.val % 2) % 2 = j.val % 4 by omega, e]
    rfl
  · intro k hk
    rw [hw, ite_eq_right_of_eq_false _ _ (eq_false fun h =>
      hk ⟨4 * (k.val / 32) + 2 * (k.val / 16 % 2) + k.val % 2, by omega⟩
        (Fin.ext (by simp only [colIndex]; omega)))]

end VG.Proof.Argon2.X86_64.Avx2
