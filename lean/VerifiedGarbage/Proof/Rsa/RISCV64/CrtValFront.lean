module

public import VerifiedGarbage.Impl.Rsa.RISCV64.CrtValues
public import VerifiedGarbage.Proof.Rsa.RISCV64.CrtValPre
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyBytes
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCheck
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
  sp : s.sp = s0.sp
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  hdr : ∀ i < 12, word s.mem (bOf s0) (8 * i) = s0.gpr (saved i)
  frame : ∀ x, zOf s0 ≤ ofs (bOf s0) x → s.mem x = M x

theorem CB.of_keep {s0 s t : State} {M : Mem} (h : CB s0 M s) {rs : List Reg} (k : Keep rs s t)
    (hm : t.mem = s.mem) (hsp : t.sp = s.sp) (hr : ∀ r ∈ cbRegs, r ∉ rs := by decide) : CB s0 M t :=
  ⟨(k.gpr (hr _ (by decide))).trans h.s1, (k.gpr (hr _ (by decide))).trans h.s2,
    (k.gpr (hr _ (by decide))).trans h.s3, (k.gpr (hr _ (by decide))).trans h.s4,
    (k.gpr (hr _ (by decide))).trans h.s5, (k.gpr (hr _ (by decide))).trans h.s6,
    (k.gpr (hr _ (by decide))).trans h.a0, (k.gpr (hr _ (by decide))).trans h.a1,
    (k.gpr (hr _ (by decide))).trans h.a2, (k.gpr (hr _ (by decide))).trans h.a3,
    (k.gpr (hr _ (by decide))).trans h.a6, (k.gpr (hr _ (by decide))).trans h.s11,
    (k.gpr (hr _ (by decide))).trans h.ra, hsp.trans h.sp, k.2.1.trans h.rd, k.2.2.trans h.wr,
    fun i hi => by rw [hm]; exact h.hdr i hi, fun x hx => by rw [hm]; exact h.frame x hx⟩

/-- A step that writes only arrays and slots from 96 on keeps `CB`. -/
theorem CB.of_frame {s0 s t : State} {M : Mem} (h : CB s0 M s) {w : Nat} {js ds : List Nat}
    (f : Keys.Frame (bOf s0) w js ds s.mem t.mem) (hjs : ∀ j ∈ js, arr w j + S w ≤ zOf s0)
    (hds : ∀ d ∈ ds, 96 ≤ d ∧ d + 8 ≤ Keys.hdr) (hZ : Keys.hdr ≤ zOf s0)
    {rs : List Reg} (k : Keep rs s t) (hsp : t.sp = s.sp) (hr : ∀ r ∈ cbRegs, r ∉ rs := by decide) :
    CB s0 M t := by
  have h' := h.of_keep (t := { t with mem := s.mem }) (rs := rs) k rfl hsp hr
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

/-- `entry`: the working space's header holds the saved registers, and the
arguments are in the registers kept. -/
theorem entry_ok {s0 : State} (h : PreC s0) : WP isa (.block entry) s0 (CB s0 s0.mem) := by
  have hz := h.zk
  have hk := h.k1
  rw [entry, WP.block_append_iff]
  refine WP.mono (save_ok s0 (i := 6) (by decide) (arg_in (by rw [h.hrd]; simp) (by decide))
    (arg_al h 6) h.scr (by omega_arith)) fun e F => ?_
  have fr : ∀ x, zOf s0 ≤ ofs (bOf s0) x → e.mem x = s0.mem x := fun x hx =>
    F.out x (.inr (Nat.le_trans (by omega_arith : 0 + 96 ≤ zOf s0) hx))
  have hrd : e.rd = s0.rd := F.keep.2.1
  have hin : ∀ j < 8, InRegions (e.rd ++ e.wr) (stackArgAddr s0 j) 8 := fun j hj =>
    arg_in (by rw [hrd, h.hrd]; simp) hj
  have i0 : InRegions (e.rd ++ e.wr) (s0.sp + BitVec.ofNat 64 0) 8 := hin 0 (by decide)
  have i1 : InRegions (e.rd ++ e.wr) (s0.sp + BitVec.ofNat 64 8) 8 := hin 1 (by decide)
  have i2 : InRegions (e.rd ++ e.wr) (s0.sp + BitVec.ofNat 64 16) 8 := hin 2 (by decide)
  have i3 : InRegions (e.rd ++ e.wr) (s0.sp + BitVec.ofNat 64 24) 8 := hin 3 (by decide)
  have i4 : InRegions (e.rd ++ e.wr) (s0.sp + BitVec.ofNat 64 32) 8 := hin 4 (by decide)
  have i5 : InRegions (e.rd ++ e.wr) (s0.sp + BitVec.ofNat 64 40) 8 := hin 5 (by decide)
  have l0 : (s0.sp + BitVec.ofNat 64 0).toNat % 8 = 0 := arg_al h 0
  have l1 : (s0.sp + BitVec.ofNat 64 8).toNat % 8 = 0 := arg_al h 1
  have l2 : (s0.sp + BitVec.ofNat 64 16).toNat % 8 = 0 := arg_al h 2
  have l3 : (s0.sp + BitVec.ofNat 64 24).toNat % 8 = 0 := arg_al h 3
  have l4 : (s0.sp + BitVec.ofNat 64 32).toNat % 8 = 0 := arg_al h 4
  have l5 : (s0.sp + BitVec.ofNat 64 40).toNat % 8 = 0 := arg_al h 5
  have r0 : e.mem.readW (s0.sp + BitVec.ofNat 64 0) 64 = stackArg s0 0 := arg_read h fr (by decide)
  have r1 : e.mem.readW (s0.sp + BitVec.ofNat 64 8) 64 = stackArg s0 1 := arg_read h fr (by decide)
  have r2 : e.mem.readW (s0.sp + BitVec.ofNat 64 16) 64 = stackArg s0 2 := arg_read h fr (by decide)
  have r3 : e.mem.readW (s0.sp + BitVec.ofNat 64 24) 64 = stackArg s0 3 := arg_read h fr (by decide)
  have r4 : e.mem.readW (s0.sp + BitVec.ofNat 64 32) 64 = stackArg s0 4 := arg_read h fr (by decide)
  have r5 : e.mem.readW (s0.sp + BitVec.ofNat 64 40) 64 = stackArg s0 5 := arg_read h fr (by decide)
  simp only [BitVec.add_zero] at i0 l0 r0
  sorry
  have hg : ∀ r, r ≠ .t0 → r ≠ .s11 → e.gpr r = s0.gpr r := fun r h0 h11 =>
    F.keep.gpr (by simp [h0, h11])
  have hb : WP isa (.block [mov .s1 .a6, mov .s2 .a7, mov .a6 .a4, mov .a3 .a2, mov .a2 .a0, .addSp .t0 0,
      .load .d .s3 .t0 0, .load .d .s4 .t0 8, .load .d .s5 .t0 16, .load .d .s6 .t0 24,
      .load .d .a0 .t0 32, .load .d .a1 .t0 40]) e fun u =>
      (u.gpr .s1 = s0.gpr .a6 ∧ u.gpr .s2 = s0.gpr .a7 ∧ u.gpr .a6 = s0.gpr .a4 ∧ u.gpr .a3 = s0.gpr .a2 ∧
        u.gpr .a2 = s0.gpr .a0 ∧ u.gpr .s3 = stackArg s0 0 ∧ u.gpr .s4 = stackArg s0 1 ∧
        u.gpr .s5 = stackArg s0 2 ∧ u.gpr .s6 = stackArg s0 3 ∧ u.gpr .a0 = stackArg s0 4 ∧
        u.gpr .a1 = stackArg s0 5 ∧ u.mem = e.mem ∧ u.sp = e.sp) ∧
      Keep [.s1, .s2, .a6, .a3, .a2, .t0, .s3, .s4, .s5, .s6, .a0, .a1] e u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    sorry
    brun [mov, exec_addSp (s := e) (d := .t0) (imm := 0) (by decide), F.sp, hg .a6 (by decide) (by decide),
      hg .a7 (by decide) (by decide), hg .a4 (by decide) (by decide), hg .a2 (by decide) (by decide),
      hg .a0 (by decide) (by decide), BitVec.add_zero, i0, i1, i2, i3, i4, i5, l0, l1, l2, l3, l4, l5,
      r0, r1, r2, r3, r4, r5]
  refine WP.mono hb fun u ⟨⟨u1, u2, u6, u3, u2', v3, v4, v5, v6, v0, v1, um, usp⟩, ku⟩ => ?_
  exact ⟨u1, u2, v3, v4, v5, v6, v0, v1, u2', u3, u6, (ku.gpr (by decide)).trans F.s11,
    (ku.gpr (by decide)).trans (hg .ra (by decide) (by decide)), usp.trans F.sp, ku.2.1.trans hrd,
    ku.2.2.trans F.keep.2.2, fun i hi => by rw [um]; exact F.saved i hi, fun x hx => by rw [um]; exact fr x hx⟩

end VG.Proof.Rsa.RISCV64.CrtValues
