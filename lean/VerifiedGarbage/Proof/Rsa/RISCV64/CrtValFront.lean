module

public import VerifiedGarbage.Impl.Rsa.RISCV64.CrtValues
public import VerifiedGarbage.Proof.Rsa.RISCV64.CrtValPre
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyBytes
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCheck
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Rsa.RISCV64.KeyInv
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_crt_values` on RISC-V: the entry, the modulus' check, the failure and the exit

`CB s0 M s`: the arguments are in the registers `entry` moves them to,
the header's first twelve words hold the caller's saved registers, and
memory outside the working space (`Z` bytes at `B`, the stack arguments 6
and 7) is `M`'s. `entry_ok` establishes it, every step of the body keeps
it (`CB.of_keep`, `CB.of_frame`), and `restore_ok'` ends it with the
caller's registers back.

`nCheck_ok`: `s0 = 0` exactly when `n` is a valid modulus; `fail_ok`: zeros
written and 0 returned.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.CrtValues

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (seqs saved mov save restore zeroBytes)
open VG.Impl.Rsa.RISCV64.CrtValues (entry nCheck fail)

/-- The working space: the stack arguments 6 and 7. -/
abbrev bOf (s : State) : Addr := stackArg s 6
abbrev zOf (s : State) : Nat := (stackArg s 7).toNat * 8

/-- The registers the body keeps. -/
abbrev cbRegs : List Reg := [.s1, .s2, .s3, .s4, .s5, .s6, .a0, .a1, .a2, .a3, .a6, .s11, .ra]

/-- After `entry`, the body's state: the arguments' registers, the saved
registers in the header, and memory outside the working space `M`'s. -/
structure CB (s0 : State) (M : Mem) (s : State) : Prop where
  s1 : s.gpr .s1 = s0.gpr .a6
  s2 : s.gpr .s2 = s0.gpr .a7
  s3 : s.gpr .s3 = stackArg s0 0
  s4 : s.gpr .s4 = stackArg s0 1
  s5 : s.gpr .s5 = stackArg s0 2
  s6 : s.gpr .s6 = stackArg s0 3
  a0 : s.gpr .a0 = stackArg s0 4
  a1 : s.gpr .a1 = stackArg s0 5
  a2 : s.gpr .a2 = s0.gpr .a0
  a3 : s.gpr .a3 = s0.gpr .a2
  a6 : s.gpr .a6 = s0.gpr .a4
  s11 : s.gpr .s11 = bOf s0
  ra : s.gpr .ra = s0.gpr .ra
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  hdr : ∀ i < 12, word s.mem (bOf s0) (8 * i) = s0.gpr (saved i)
  frame : ∀ x, zOf s0 ≤ ofs (bOf s0) x → s.mem x = M x

theorem CB.of_keep {s0 s t : State} {M : Mem} (h : CB s0 M s) {rs : List Reg} (k : Keep rs s t)
    (hm : t.mem = s.mem) (hr : ∀ r ∈ cbRegs, r ∉ rs := by decide) : CB s0 M t :=
  ⟨(k.gpr (hr _ (by decide))).trans h.s1, (k.gpr (hr _ (by decide))).trans h.s2,
    (k.gpr (hr _ (by decide))).trans h.s3, (k.gpr (hr _ (by decide))).trans h.s4,
    (k.gpr (hr _ (by decide))).trans h.s5, (k.gpr (hr _ (by decide))).trans h.s6,
    (k.gpr (hr _ (by decide))).trans h.a0, (k.gpr (hr _ (by decide))).trans h.a1,
    (k.gpr (hr _ (by decide))).trans h.a2, (k.gpr (hr _ (by decide))).trans h.a3,
    (k.gpr (hr _ (by decide))).trans h.a6, (k.gpr (hr _ (by decide))).trans h.s11,
    (k.gpr (hr _ (by decide))).trans h.ra, k.2.1.trans h.rd, k.2.2.trans h.wr,
    fun i hi => by rw [hm]; exact h.hdr i hi, fun x hx => by rw [hm]; exact h.frame x hx⟩

/-- A step that writes only arrays and slots from 96 on keeps `CB`. -/
theorem CB.of_frame {s0 s t : State} {M : Mem} (h : CB s0 M s) {w : Nat} {js ds : List Nat}
    (f : Keys.Frame (bOf s0) w js ds s.mem t.mem) (hjs : ∀ j ∈ js, arr w j + S w ≤ zOf s0)
    (hds : ∀ d ∈ ds, 96 ≤ d ∧ d + 8 ≤ Keys.hdr) (hZ : Keys.hdr ≤ zOf s0)
    {rs : List Reg} (k : Keep rs s t) (hr : ∀ r ∈ cbRegs, r ∉ rs := by decide) :
    CB s0 M t := by
  have h' := h.of_keep (t := { t with mem := s.mem }) (rs := rs) k rfl hr
  refine { h' with hdr := fun i hi => ?_, frame := fun x hx => ?_ }
  · rw [← h.hdr i hi]
    have e := f.words (d := 8 * i) (k := 1) (fun j _ => by have := hdr_le_arr w j; simp only [hdr_eq] at this; omega_arith)
      (fun d hd => by have := hds d hd; omega_arith) (by simp only [hdr_eq] at hZ; omega_arith)
    simp only [wordsVal, Nat.mul_zero, Nat.add_zero] at e
    exact BitVec.eq_of_toNat_eq e
  · rw [← h.frame x hx]
    exact f.out (Z := zOf s0) hjs (fun d hd => by have := hds d hd; simp only [hdr_eq] at hZ this; omega_arith) hx

/-! ## Addresses outside the working space -/

theorem past_of_disjoint {B : Addr} {Z : Nat} {r : Region} (hd : r.Disjoint ⟨B, Z⟩) {a : Addr}
    (ha : r.Contains a 1) : Z ≤ ofs B a := by
  have := hd a ha
  simp only [Region.Contains] at this
  simp only [ofs]; omega_arith

/-- Byte `i` of a region at `P`. -/
theorem bytes_contains {P : Addr} {L i : Nat} (hi : i < L) (hL : L ≤ 2 ^ 64) :
    (⟨P, L⟩ : Region).Contains (off P i) 1 :=
  Offset.contains_base P (by omega_arith) (by omega_arith)

/-- Byte `i` of a region apart from the working space is past it. -/
theorem bytes_past {B P : Addr} {Z L i : Nat} (hd : (⟨P, L⟩ : Region).Disjoint ⟨B, Z⟩) (hi : i < L)
    (hL : L ≤ 2 ^ 64) : Z ≤ ofs B (off P i) :=
  past_of_disjoint hd (bytes_contains hi hL)

theorem bytes_sep {B P : Addr} {Z L : Nat} (hd : (⟨P, L⟩ : Region).Disjoint ⟨B, Z⟩) (hL : L ≤ 2 ^ 64) :
    ∀ i < L, ∀ x, ofs B x < Z → off P i ≠ x := fun i hi x hx e => by
  have := bytes_past hd hi hL
  rw [e] at this
  omega_arith

theorem bytes_in {rs : List Region} {P : Addr} {L : Nat} (hr : (⟨P, L⟩ : Region) ∈ rs) (hL : L ≤ 2 ^ 64) :
    ∀ i < L, InRegions rs (off P i) 1 := fun _ hi => ⟨_, hr, bytes_contains hi hL⟩

theorem bytesAt_congr {m m' : Mem} {P : Addr} {L : Nat} (h : ∀ i < L, m (off P i) = m' (off P i)) :
    Spec.Rsa.bytesAt m P L = Spec.Rsa.bytesAt m' P L := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- The bytes of a region apart from the working space are `M`'s. -/
theorem CB.bytes {s0 s : State} {M : Mem} (h : CB s0 M s) {P : Addr} {L : Nat}
    (hd : (⟨P, L⟩ : Region).Disjoint (sR s0)) (hL : L ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt s.mem P L = Spec.Rsa.bytesAt M P L :=
  bytesAt_congr fun _ hi => h.frame _ (bytes_past hd hi hL)

/-! ## The entry -/

theorem PreC.sR_wr {s : State} (h : PreC s) : sR s ∈ s.wr := by rw [h.hwr]; simp

theorem PreC.zk {s : State} (h : PreC s) : 8 * (16 * (s.gpr .a7).toNat + 32) ≤ zOf s := by
  have := h.hs; simp only [Spec.Rsa.scratchWords] at this; simp only [zOf]; omega_arith

theorem PreC.scr {s : State} (h : PreC s) : Scr s (bOf s) (zOf s) :=
  Scr.of_mem h.sR_wr h.ws h.al

theorem arg_al {s : State} (h : PreC s) (j : Nat) : (stackArgAddr s j).toNat % 8 = 0 := by
  have := h.sp16; have := h.sp2
  simp only [stackArgAddr, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith

theorem arg_in {s : State} {rs : List Region} (hrs : aR s ∈ rs) {j : Nat} (hj : j < 8) :
    InRegions rs (stackArgAddr s j) 8 := by
  refine ⟨_, hrs, ?_⟩
  simp only [stackArgAddr]
  have e : s.sp + BitVec.ofNat 64 (8 * j) = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
    simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
  rw [e]
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

/-- A stack argument, read after the working space changed. -/
theorem arg_read {s : State} (h : PreC s) {m : Mem} (hm : ∀ x, zOf s ≤ ofs (bOf s) x → m x = s.mem x)
    {j : Nat} (hj : j < 8) : m.readW (stackArgAddr s j) 64 = stackArg s j := by
  refine Mem.readW_congr fun i hi => hm _ ?_
  have hc : (aR s).Contains (stackArgAddr s j + BitVec.ofNat 64 i) 1 := by
    have e : stackArgAddr s j + BitVec.ofNat 64 i = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j + i) := by
      simp only [stackArgAddr, Nat.mul_zero, BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_zero]
    rw [e]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  exact past_of_disjoint h.sa.symm hc

theorem arg_succ (s : State) (j : Nat) : stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) = stackArgAddr s j := by
  simp only [stackArgAddr, Nat.mul_zero, add_ofNat_zero']

/-- The moves of `entry`, after `save`. -/
def cvMoves : List Instr :=
  [mov .s1 .a6, mov .s2 .a7, mov .a6 .a4, mov .a3 .a2, mov .a2 .a0, .addSp .t0 0,
    .load .d .s3 .t0 0, .load .d .s4 .t0 8, .load .d .s5 .t0 16, .load .d .s6 .t0 24,
    .load .d .a0 .t0 32, .load .d .a1 .t0 40]

theorem entry_eq : entry = save 48 ++ cvMoves := rfl

/-- The moves, after `save`: the arguments are in the registers kept. -/
theorem moves_ok {s0 e : State} (h : PreC s0) (F : Saved s0 (bOf s0) e) :
    WP isa (.block cvMoves) e (CB s0 s0.mem) := by
  have hz := h.zk
  have hk := h.k1
  have fr : ∀ x, zOf s0 ≤ ofs (bOf s0) x → e.mem x = s0.mem x := fun x hx =>
    F.out x (.inr (Nat.le_trans (by omega_arith : 0 + 96 ≤ zOf s0) hx))
  have hrd : e.rd = s0.rd := F.keep.2.1
  have hin : ∀ j < 8, InRegions (e.rd ++ e.wr) (stackArgAddr s0 j) 8 := fun j hj =>
    arg_in (by rw [hrd, h.hrd]; simp) hj
  have l : ∀ j, (stackArgAddr s0 j).toNat % 8 = 0 := arg_al h
  have r : ∀ j < 8, e.mem.readW (stackArgAddr s0 j) 64 = stackArg s0 j := fun j hj => arg_read h fr hj
  have a0 : s0.sp + BitVec.ofNat 64 0 = stackArgAddr s0 0 := rfl
  have a1 : stackArgAddr s0 0 + BitVec.ofNat 64 8 = stackArgAddr s0 1 := arg_succ s0 1
  have a2 : stackArgAddr s0 0 + BitVec.ofNat 64 16 = stackArgAddr s0 2 := arg_succ s0 2
  have a3 : stackArgAddr s0 0 + BitVec.ofNat 64 24 = stackArgAddr s0 3 := arg_succ s0 3
  have a4 : stackArgAddr s0 0 + BitVec.ofNat 64 32 = stackArgAddr s0 4 := arg_succ s0 4
  have a5 : stackArgAddr s0 0 + BitVec.ofNat 64 40 = stackArgAddr s0 5 := arg_succ s0 5
  have hg : ∀ r, r ≠ .t0 → r ≠ .s11 → e.gpr r = s0.gpr r := fun r h0 h11 =>
    F.keep.gpr (by simp [h0, h11])
  have hb : WP isa (.block cvMoves) e fun u =>
      (u.gpr .s1 = s0.gpr .a6 ∧ u.gpr .s2 = s0.gpr .a7 ∧ u.gpr .a6 = s0.gpr .a4 ∧ u.gpr .a3 = s0.gpr .a2 ∧
        u.gpr .a2 = s0.gpr .a0 ∧ u.gpr .s3 = stackArg s0 0 ∧ u.gpr .s4 = stackArg s0 1 ∧
        u.gpr .s5 = stackArg s0 2 ∧ u.gpr .s6 = stackArg s0 3 ∧ u.gpr .a0 = stackArg s0 4 ∧
        u.gpr .a1 = stackArg s0 5 ∧ u.mem = e.mem ∧ u.sp = e.sp) ∧
      Keep [.s1, .s2, .a6, .a3, .a2, .t0, .s3, .s4, .s5, .s6, .a0, .a1] e u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [cvMoves, mov, exec_addSp (d := .t0) (imm := 0) (by decide), F.sp, hg .a6 (by decide) (by decide),
      hg .a7 (by decide) (by decide), hg .a4 (by decide) (by decide), hg .a2 (by decide) (by decide),
      hg .a0 (by decide) (by decide), add_ofNat_zero', a0, a1, a2, a3, a4, a5, l 0, l 1, l 2, l 3, l 4, l 5,
      hin 0 (by decide), hin 1 (by decide), hin 2 (by decide), hin 3 (by decide), hin 4 (by decide),
      hin 5 (by decide), r 0 (by decide), r 1 (by decide), r 2 (by decide), r 3 (by decide), r 4 (by decide),
      r 5 (by decide)]
  refine WP.mono hb fun u ⟨⟨u1, u2, u6, u3, u2', v3, v4, v5, v6, v0, v1, um, usp⟩, ku⟩ => ?_
  exact ⟨u1, u2, v3, v4, v5, v6, v0, v1, u2', u3, u6, (ku.gpr (by decide)).trans F.s11,
    (ku.gpr (by decide)).trans (hg .ra (by decide) (by decide)), ku.2.1.trans hrd,
    ku.2.2.trans F.keep.2.2, fun i hi => by rw [um]; exact F.saved i hi, fun x hx => by rw [um]; exact fr x hx⟩

/-- `entry`: the working space's header holds the saved registers, and the
arguments are in the registers kept. -/
theorem entry_ok {s0 : State} (h : PreC s0) : WP isa (.block entry) s0 (CB s0 s0.mem) := by
  have hz := h.zk
  rw [entry_eq, WP.block_append_iff]
  exact WP.mono (save_ok s0 (i := 6) (by decide) (arg_in (by rw [h.hrd]; simp) (by decide))
    (arg_al h 6) h.scr (by omega_arith)) fun e F => moves_ok h F

theorem inRegions_left {rs ws : List Region} {a : Addr} {n : Nat} (h : InRegions rs a n) :
    InRegions (rs ++ ws) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_left _ hr, hc⟩

theorem inRegions_right {rs ws : List Region} {a : Addr} {n : Nat} (h : InRegions ws a n) :
    InRegions (rs ++ ws) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

/-! ## The modulus' check -/

/-- `n`'s bytes, as the function reads them. -/
abbrev nB (s0 : State) : List Byte := Spec.Rsa.bytesAt s0.mem (s0.gpr .a6) (s0.gpr .a7).toNat

theorem nCheck_ok {s0 s : State} (h : PreC s0) (c : CB s0 s0.mem s) :
    WP isa nCheck s fun t =>
      (t.gpr .s0 = 0 ↔ Spec.Rsa.modulusValid (Spec.Rsa.os2ip (nB s0)) (s0.gpr .a7).toNat = true) ∧
        t.mem = s.mem ∧ Keep [.s7, .s8, .s0, .t4, .t5] s t := by
  have hk1 := h.k1
  have hk2 := h.k2
  have hL : (s0.gpr .a7).toNat ≤ 2 ^ 64 := by omega_arith
  rw [nCheck, WP.seq_iff]
  have hb : WP isa (.block [mov .s7 .s1, mov .s8 .s2]) s fun u =>
      (u.gpr .s7 = off (s0.gpr .a6) 0 ∧ u.gpr .s8 = BitVec.ofNat 64 (s0.gpr .a7).toNat ∧ u.mem = s.mem ∧
        u.sp = s.sp) ∧ Keep [.s7, .s8] s u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [mov, c.s1, c.s2, add_ofNat_zero', BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono hb fun u ⟨⟨u7, u8, um, usp⟩, ku⟩ => ?_
  have hrd : u.rd = s0.rd := ku.2.1.trans c.rd
  refine WP.mono (check_ok (nb := Spec.Rsa.bytesAt s.mem (s0.gpr .a6) (s0.gpr .a7).toNat) u7 u8 hk1 hk2
    (by simp [Spec.Rsa.bytesAt])
    (fun i hi => by
      rw [hrd]
      exact inRegions_left (bytes_in (rs := s0.rd) (by rw [h.hrd]; simp) hL i hi))
    (fun i hi => by simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, um]))
    fun t ⟨t0, tm, kt⟩ => ?_
  rw [c.bytes h.ns hL] at t0
  exact ⟨t0, tm.trans um, Keep.trans' (Keep.mono ku (by decide)) (Keep.mono kt (by decide))⟩

/-! ## An invalid modulus -/

/-- Bytes of `O` zeroed stay zeroed when memory changes only in a region apart. -/
theorem zeros_keep {O O' : Addr} {L L' : Nat} {m m' : Mem} (hd : (⟨O, L⟩ : Region).Disjoint ⟨O', L'⟩)
    (hL : L ≤ 2 ^ 64) (ho : Outside O' 0 L' m m') {c : Nat} (hc : c < L) : m' (off O c) = m (off O c) :=
  ho _ (.inr (by have := bytes_past hd hc hL; omega_arith))

theorem bytesAt_zero {m : Mem} {O : Addr} {L : Nat} (h : ∀ c < L, m (off O c) = 0) :
    Spec.Rsa.bytesAt m O L = List.replicate L 0 := by
  simp only [Spec.Rsa.bytesAt]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
  exact h i (by simpa using h1)

/-- The three outputs: `dp` (`p_len` bytes), `dq` (`q_len`) and `qinv` (`p_len`). -/
abbrev outs (s0 : State) : List (Addr × Nat) :=
  [(s0.gpr .a0, (stackArg s0 1).toNat), (s0.gpr .a2, (stackArg s0 3).toNat),
    (s0.gpr .a4, (stackArg s0 1).toNat)]

theorem PreC.dpR_eq {s : State} (h : PreC s) : dpR s = ⟨s.gpr .a0, (stackArg s 1).toNat⟩ := by
  simp only [dpR, h.h1]
theorem PreC.dqR_eq {s : State} (h : PreC s) : dqR s = ⟨s.gpr .a2, (stackArg s 3).toNat⟩ := by
  simp only [dqR, h.h3]
theorem PreC.qiR_eq {s : State} (h : PreC s) : qiR s = ⟨s.gpr .a4, (stackArg s 1).toNat⟩ := by
  simp only [qiR, h.h5]

theorem lt32 {s : State} (h : PreC s) : (stackArg s 1).toNat < 2 ^ 32 ∧ (stackArg s 3).toNat < 2 ^ 32 := by
  have := h.p2; have := h.q2; have := h.k2; constructor <;> omega_arith

/-- A byte of the working space is kept by a write apart from it. -/
theorem out_of_scr {O B : Addr} {L Z : Nat} {m m' : Mem} (hd : (⟨O, L⟩ : Region).Disjoint ⟨B, Z⟩)
    (ho : Outside O 0 L m m') {x : Addr} (hx : (⟨B, Z⟩ : Region).Contains x 1) : m' x = m x :=
  ho x (.inr (by
    have := hd x
    simp only [Region.Contains] at this hx
    simp only [ofs]
    omega_arith))

/-- A write to a region apart from the working space keeps `CB`, for its new memory. -/
theorem CB.of_out {s0 s t : State} {M : Mem} (c : CB s0 M s) {rs : List Reg} (k : Keep rs s t)
    {O : Addr} {L : Nat} (ho : Outside O 0 L s.mem t.mem) (hd : (⟨O, L⟩ : Region).Disjoint (sR s0))
    (hZ : 96 ≤ zOf s0) (hr : ∀ r ∈ cbRegs, r ∉ rs := by decide) : CB s0 t.mem t :=
  { c.of_keep (t := { t with mem := s.mem }) k rfl hr with
    hdr := fun i hi => by
      rw [← c.hdr i hi]
      refine Mem.readW_congr fun j hj => ?_
      refine out_of_scr hd ho ?_
      rw [off_add]
      exact Offset.contains_base _ (by simp only [zOf] at hZ ⊢; omega_arith) (by omega_arith)
    frame := fun _ _ => rfl }

/-- What the exit needs: the saved registers in the header, the base in
`s11`, and `ra`. -/
structure CE (s0 s : State) : Prop where
  s11 : s.gpr .s11 = bOf s0
  ra : s.gpr .ra = s0.gpr .ra
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  hdr : ∀ i < 12, word s.mem (bOf s0) (8 * i) = s0.gpr (saved i)

theorem CB.ce {s0 s : State} {M : Mem} (c : CB s0 M s) : CE s0 s := ⟨c.s11, c.ra, c.rd, c.wr, c.hdr⟩

theorem fail_ok {s0 s : State} (h : PreC s0) (c : CB s0 s0.mem s) :
    WP isa fail s fun t => CE s0 t ∧
      Spec.Rsa.writtenAll t.mem (outs s0) ((t.gpr .a0).setWidth 32) none := by
  have ⟨lp, lq⟩ := lt32 h
  have hp1 := h.p1
  have hq1 := h.q1
  have wdp : (s0.gpr .a0).toNat + (stackArg s0 1).toNat ≤ 2 ^ 64 := by have := h.wdp; rw [h.h1] at this; exact this
  have wdq : (s0.gpr .a2).toNat + (stackArg s0 3).toNat ≤ 2 ^ 64 := by have := h.wdq; rw [h.h3] at this; exact this
  have wqi : (s0.gpr .a4).toNat + (stackArg s0 1).toNat ≤ 2 ^ 64 := by have := h.wqi; rw [h.h5] at this; exact this
  have inW : ∀ {P : Addr} {L : Nat}, (⟨P, L⟩ : Region) ∈ s0.wr → L ≤ 2 ^ 64 → ∀ {u : State}, u.wr = s0.wr →
      ∀ i < L, InRegions u.wr (off P i) 1 := fun hr hL u hu i hi => by
    rw [hu]; exact bytes_in hr hL i hi
  have m1 : dpR s0 ∈ s0.wr := by rw [h.hwr]; simp
  have m2 : dqR s0 ∈ s0.wr := by rw [h.hwr]; simp
  have m3 : qiR s0 ∈ s0.wr := by rw [h.hwr]; simp
  rw [h.dpR_eq] at m1
  rw [h.dqR_eq] at m2
  rw [h.qiR_eq] at m3
  have l4 : s.gpr .s4 = BitVec.ofNat 64 (stackArg s0 1).toNat := by rw [c.s4, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have l6 : s.gpr .s6 = BitVec.ofNat 64 (stackArg s0 3).toNat := by rw [c.s6, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  unfold fail
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (WP.rdwr (zeroBytes_ok c.a2 l4 (by decide) hp1 lp (inW m1 (by omega_arith) c.wr) wdp))
    fun t1 ⟨⟨z1, o1, k1⟩, r1, w1, _⟩ => ?_
  have hz := h.zk
  have hZ : 96 ≤ zOf s0 := by omega_arith
  have c1 := c.of_out k1 o1 (by rw [← h.dpR_eq]; exact h.dps) hZ
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (WP.rdwr (zeroBytes_ok (c1.a3) (by rw [(k1.gpr (by decide))]; exact l6) (by decide) hq1 lq
    (inW m2 (by omega_arith) (w1.trans c.wr)) wdq)) fun t2 ⟨⟨z2, o2, k2⟩, r2, w2, _⟩ => ?_
  have c2 := c1.of_out k2 o2 (by rw [← h.dqR_eq]; exact h.dqs) hZ
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (WP.rdwr (zeroBytes_ok (c2.a6)
    (by rw [(k2.gpr (by decide)), (k1.gpr (by decide))]; exact l4) (by decide) hp1 lp
    (inW m3 (by omega_arith) (w2.trans (w1.trans c.wr))) wqi)) fun t3 ⟨⟨z3, o3, k3⟩, _, _, _⟩ => ?_
  have c3 := c2.of_out k3 o3 (by rw [← h.qiR_eq]; exact h.qis) hZ
  have hb : WP isa (.block [.li .a0 0]) t3 fun u => (u.gpr .a0 = 0 ∧ u.mem = t3.mem) ∧ Keep [.a0] t3 u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [fin64_exec_li_zero]
  refine WP.mono hb fun u ⟨⟨u0, um⟩, ku⟩ => ?_
  refine ⟨⟨(ku.gpr (by decide)).trans c3.s11, (ku.gpr (by decide)).trans c3.ra, ku.2.1.trans c3.rd,
    ku.2.2.trans c3.wr, fun i hi => by rw [um]; exact c3.hdr i hi⟩, ?_, ?_⟩
  · rw [u0]; rfl
  · have dq_qi : (⟨s0.gpr .a2, (stackArg s0 3).toNat⟩ : Region).Disjoint ⟨s0.gpr .a4, (stackArg s0 1).toNat⟩ := by
      rw [← h.dqR_eq, ← h.qiR_eq]; exact h.dqqi
    have dp_qi : (⟨s0.gpr .a0, (stackArg s0 1).toNat⟩ : Region).Disjoint ⟨s0.gpr .a4, (stackArg s0 1).toNat⟩ := by
      rw [← h.dpR_eq, ← h.qiR_eq]; exact h.dpqi
    have dp_dq : (⟨s0.gpr .a0, (stackArg s0 1).toNat⟩ : Region).Disjoint ⟨s0.gpr .a2, (stackArg s0 3).toNat⟩ := by
      rw [← h.dpR_eq, ← h.dqR_eq]; exact h.dpdq
    simp only [outs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, um]
    refine ⟨bytesAt_zero fun c hc => ?_, bytesAt_zero fun c hc => ?_, bytesAt_zero fun c hc => z3 c hc⟩
    · rw [zeros_keep dp_qi (by omega_arith) o3 hc, zeros_keep dp_dq (by omega_arith) o2 hc]; exact z1 c hc
    · rw [zeros_keep dq_qi (by omega_arith) o3 hc]; exact z2 c hc

/-! ## The exit -/

theorem preserved_saved : ∀ r ∈ preserved, ∃ i < 12, saved i = r := by decide

theorem restore_ok' {s0 t : State} (h : PreC s0) (c : CE s0 t) :
    WP isa (.block restore) t fun v =>
      (∀ r ∈ preserved, v.gpr r = s0.gpr r) ∧ v.gpr .ra = s0.gpr .ra ∧ v.mem = t.mem ∧
        v.gpr .a0 = t.gpr .a0 := by
  have hz := h.zk
  have hs : Scr t (bOf s0) (zOf s0) := Scr.of_mem (by rw [c.wr]; exact h.sR_wr) h.ws h.al
  refine WP.mono (restore_ok t hs (by omega_arith) c.s11 c.hdr) fun v ⟨hv, ho, hm, _⟩ => ?_
  refine ⟨fun r hr => ?_, (ho .ra (by decide)).trans c.ra, hm, ho .a0 (by decide)⟩
  obtain ⟨i, hi, rfl⟩ := preserved_saved r hr
  exact hv i hi

end VG.Proof.Rsa.RISCV64.CrtValues
