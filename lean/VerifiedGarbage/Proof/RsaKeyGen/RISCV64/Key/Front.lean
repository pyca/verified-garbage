module

public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.Key
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyBytes
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_rsa_keygen_key` on RISC-V: the contract by name, the entry and the exit

`PreC s`: `keyContract`'s precondition, by name (`preC_of`). `CB s0 M s`:
the arguments are in the registers `entry` moves them to, the header's first
twelve words hold the caller's saved registers, and memory outside the
working space (`zOf` bytes at `bOf`, the stack arguments 8 and 9) is `M`'s.
`entry_ok` establishes it, every step of the body keeps it (`CB.of_keep`,
`CB.of_frame`), and `restore_ok` ends it with the caller's registers back.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Key

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (saved mov save restore)

theorem stackArgs_ten (s : State) :
    List.map (stackArg s) (List.range 10) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9] := rfl

/-! ## The buffers

Argument registers `a0`–`a7`: `n`, `n_len`, `d`, `d_len`, `p`, `p_len`, `q`,
`q_len`; stack arguments 0–9: `dp`, `dp_len`, `dq`, `dq_len`, `qinv`,
`qinv_len`, `e`, `e_len`, `scratch`, `scratch_len`. -/

abbrev nR (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
abbrev dR (s : State) : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
abbrev pR (s : State) : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
abbrev qR (s : State) : Region := ⟨s.gpr .a6, (s.gpr .a7).toNat⟩
abbrev dpR (s : State) : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
abbrev dqR (s : State) : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
abbrev qiR (s : State) : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
abbrev eR (s : State) : Region := ⟨stackArg s 6, (stackArg s 7).toNat⟩
abbrev sR (s : State) : Region := ⟨stackArg s 8, (stackArg s 9).toNat * 8⟩
abbrev aR (s : State) : Region := ⟨stackArgAddr s 0, 80⟩

/-- `keyContract`'s precondition, by name: every pair of the buffers is disjoint but
`e` and the stack arguments' (both read-only). -/
structure PreC (s : State) : Prop where
  sp16 : s.sp.toNat % 16 = 0
  sp2 : s.sp.toNat + 80 ≤ 2 ^ 64
  hrd : s.rd = [eR s, aR s]
  hwr : s.wr = [nR s, dR s, pR s, qR s, dpR s, dqR s, qiR s, sR s]
  nd : (nR s).Disjoint (dR s)
  np : (nR s).Disjoint (pR s)
  nq : (nR s).Disjoint (qR s)
  ndp : (nR s).Disjoint (dpR s)
  ndq : (nR s).Disjoint (dqR s)
  nqi : (nR s).Disjoint (qiR s)
  ne : (nR s).Disjoint (eR s)
  ns : (nR s).Disjoint (sR s)
  na : (nR s).Disjoint (aR s)
  dp : (dR s).Disjoint (pR s)
  dq : (dR s).Disjoint (qR s)
  ddp : (dR s).Disjoint (dpR s)
  ddq : (dR s).Disjoint (dqR s)
  dqi : (dR s).Disjoint (qiR s)
  de : (dR s).Disjoint (eR s)
  ds : (dR s).Disjoint (sR s)
  da : (dR s).Disjoint (aR s)
  pq : (pR s).Disjoint (qR s)
  pdp : (pR s).Disjoint (dpR s)
  pdq : (pR s).Disjoint (dqR s)
  pqi : (pR s).Disjoint (qiR s)
  pe : (pR s).Disjoint (eR s)
  ps : (pR s).Disjoint (sR s)
  pa : (pR s).Disjoint (aR s)
  qdp : (qR s).Disjoint (dpR s)
  qdq : (qR s).Disjoint (dqR s)
  qqi : (qR s).Disjoint (qiR s)
  qe : (qR s).Disjoint (eR s)
  qs : (qR s).Disjoint (sR s)
  qa : (qR s).Disjoint (aR s)
  dpdq : (dpR s).Disjoint (dqR s)
  dpqi : (dpR s).Disjoint (qiR s)
  dpe : (dpR s).Disjoint (eR s)
  dps : (dpR s).Disjoint (sR s)
  dpa : (dpR s).Disjoint (aR s)
  dqqi : (dqR s).Disjoint (qiR s)
  dqe : (dqR s).Disjoint (eR s)
  dqs : (dqR s).Disjoint (sR s)
  dqa : (dqR s).Disjoint (aR s)
  qie : (qiR s).Disjoint (eR s)
  qis : (qiR s).Disjoint (sR s)
  qia : (qiR s).Disjoint (aR s)
  es : (eR s).Disjoint (sR s)
  sa : (sR s).Disjoint (aR s)
  wn : (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64
  wd : (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64
  wp : (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64
  wq : (s.gpr .a6).toNat + (s.gpr .a7).toNat ≤ 2 ^ 64
  wdp : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  wdq : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64
  wqi : (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64
  we : (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64
  ws : (stackArg s 8).toNat + (stackArg s 9).toNat * 8 ≤ 2 ^ 64
  p32 : 32 ≤ (s.gpr .a5).toNat
  p512 : (s.gpr .a5).toNat ≤ 512
  p8 : (s.gpr .a5).toNat % 8 = 0
  hn : (s.gpr .a1).toNat = 2 * (s.gpr .a5).toNat
  hd : (s.gpr .a3).toNat = (s.gpr .a1).toNat
  hq : (s.gpr .a7).toNat = (s.gpr .a5).toNat
  hdp : (stackArg s 1).toNat = (s.gpr .a5).toNat
  hdq : (stackArg s 3).toNat = (s.gpr .a5).toNat
  hqi : (stackArg s 5).toNat = (s.gpr .a5).toNat
  e1 : 1 ≤ (stackArg s 7).toNat
  e2 : (stackArg s 7).toNat ≤ 8
  hs : Spec.Rsa.scratchWords (s.gpr .a1).toNat ≤ (stackArg s 9).toNat
  al : (stackArg s 8).toNat % 8 = 0

theorem preC_of {s : State} (h : (Spec.RsaKeyGen.keyContract RISCV64.abi).pre s) : PreC s := by
  sig_pre [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, RISCV64.abi, RISCV64.argRegs,
    stackArgs_ten, List.append_eq, List.range, List.range.loop] at h
  obtain ⟨sp16, sp2, hrd, hwr, nd, np, nq, ndp, ndq, nqi, ne, ns, na, dp, dq, ddp, ddq, dqi, de, ds, da, pq, pdp, pdq, pqi, pe, ps, pa, qdp, qdq, qqi, qe, qs, qa, dpdq, dpqi, dpe, dps, dpa, dqqi, dqe, dqs, dqa, qie, qis, qia, es, sa, wn, wd, wp, wq, wdp, wdq, wqi, we, ws, ⟨p32, p512, p8⟩, hn, hd, hq, hdp, hdq, hqi, e1, e2, hs, al⟩ := h
  exact ⟨sp16, sp2, hrd, hwr, nd, np, nq, ndp, ndq, nqi, ne, ns, na, dp, dq, ddp, ddq, dqi, de, ds, da, pq, pdp, pdq, pqi, pe, ps, pa, qdp, qdq, qqi, qe, qs, qa, dpdq, dpqi, dpe, dps, dpa, dqqi, dqe, dqs, dqa, qie, qis, qia, es, sa, wn, wd, wp, wq, wdp, wdq, wqi, we, ws, p32, p512, p8, hn, hd, hq, hdp, hdq, hqi, e1, e2, hs, al⟩

/-! ## The working space -/

abbrev bOf (s : State) : Addr := stackArg s 8
abbrev zOf (s : State) : Nat := (stackArg s 9).toNat * 8
abbrev pLen (s : State) : Nat := (s.gpr .a5).toNat
/-- `w`, as `setup` computes it from `2 p_len`. -/
abbrev wOf (s : State) : Nat := (2 * pLen s + 7) / 8

theorem PreC.wOf_eq {s : State} (h : PreC s) : 4 * wOf s = pLen s := by
  have := h.p8; simp only [wOf, pLen] at this ⊢; omega

theorem PreC.zk {s : State} (h : PreC s) : 8 * (16 * (s.gpr .a1).toNat + 32) ≤ zOf s := by
  have := h.hs; simp only [Spec.Rsa.scratchWords] at this; simp only [zOf]; omega_arith

theorem PreC.fits {s : State} (h : PreC s) :
    arr (wOf s) VG.Impl.RsaKeyGen.RISCV64.Key.nArr ≤ zOf s ∧ 8 ≤ wOf s ∧ wOf s ≤ 128 := by
  have hz := h.zk
  have := h.hn; have := h.p32; have := h.p512; have := h.p8
  simp only [arr, hdr_eq, S, VG.Impl.RsaKeyGen.RISCV64.Key.nArr, wOf, pLen] at hz ⊢
  omega_arith

theorem PreC.sR_wr {s : State} (h : PreC s) : sR s ∈ s.wr := by rw [h.hwr]; simp

theorem PreC.scr {s : State} (h : PreC s) : Scr s (bOf s) (zOf s) :=
  Scr.of_mem h.sR_wr h.ws h.al

/-! ## The body's state -/

/-- The registers the body keeps. -/
abbrev cbRegs : List Reg := [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .a0, .a1, .a7, .s11, .ra]

/-- After `entry`: the arguments in the registers kept, the caller's registers in the
header's first twelve words, memory outside the working space `M`'s. -/
structure CB (s0 : State) (M : Mem) (s : State) : Prop where
  rs0 : s.gpr .s0 = s0.gpr .a0
  s1 : s.gpr .s1 = s0.gpr .a2
  s2 : s.gpr .s2 = s0.gpr .a4
  s3 : s.gpr .s3 = s0.gpr .a6
  a1 : s.gpr .a1 = s0.gpr .a5
  s4 : s.gpr .s4 = stackArg s0 0
  s5 : s.gpr .s5 = stackArg s0 2
  s6 : s.gpr .s6 = stackArg s0 4
  a0 : s.gpr .a0 = stackArg s0 6
  a7 : s.gpr .a7 = stackArg s0 7
  s11 : s.gpr .s11 = bOf s0
  ra : s.gpr .ra = s0.gpr .ra
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  hdr : ∀ i < 12, word s.mem (bOf s0) (8 * i) = s0.gpr (saved i)
  frame : ∀ x, zOf s0 ≤ ofs (bOf s0) x → s.mem x = M x

theorem CB.of_keep {s0 s t : State} {M : Mem} (h : CB s0 M s) {rs : List Reg} (k : Keep rs s t)
    (hm : t.mem = s.mem) (hr : ∀ r ∈ cbRegs, r ∉ rs := by decide) : CB s0 M t :=
  ⟨(k.gpr (hr _ (by decide))).trans h.rs0, (k.gpr (hr _ (by decide))).trans h.s1,
    (k.gpr (hr _ (by decide))).trans h.s2, (k.gpr (hr _ (by decide))).trans h.s3,
    (k.gpr (hr _ (by decide))).trans h.a1, (k.gpr (hr _ (by decide))).trans h.s4,
    (k.gpr (hr _ (by decide))).trans h.s5, (k.gpr (hr _ (by decide))).trans h.s6,
    (k.gpr (hr _ (by decide))).trans h.a0, (k.gpr (hr _ (by decide))).trans h.a7,
    (k.gpr (hr _ (by decide))).trans h.s11, (k.gpr (hr _ (by decide))).trans h.ra,
    k.2.1.trans h.rd, k.2.2.trans h.wr,
    fun i hi => by rw [hm]; exact h.hdr i hi, fun x hx => by rw [hm]; exact h.frame x hx⟩

/-- A step that writes only arrays and slots from 96 on keeps `CB`. -/
theorem CB.of_frame {s0 s t : State} {M : Mem} (h : CB s0 M s) {w : Nat} {js ds : List Nat}
    (f : VG.Proof.Rsa.RISCV64.Keys.Frame (bOf s0) w js ds s.mem t.mem) (hjs : ∀ j ∈ js, arr w j + S w ≤ zOf s0)
    (hds : ∀ d ∈ ds, 96 ≤ d ∧ d + 8 ≤ VG.Proof.Rsa.RISCV64.Keys.hdr) (hZ : VG.Proof.Rsa.RISCV64.Keys.hdr ≤ zOf s0)
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

theorem bytes_contains {P : Addr} {L i : Nat} (hi : i < L) (hL : L ≤ 2 ^ 64) :
    (⟨P, L⟩ : Region).Contains (off P i) 1 :=
  Offset.contains_base P (by omega_arith) (by omega_arith)

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

theorem arg_al {s : State} (h : PreC s) (j : Nat) : (stackArgAddr s j).toNat % 8 = 0 := by
  have := h.sp16; have := h.sp2
  simp only [stackArgAddr, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith

theorem arg_in {s : State} {rs : List Region} (hrs : aR s ∈ rs) {j : Nat} (hj : j < 10) :
    InRegions rs (stackArgAddr s j) 8 := by
  refine ⟨_, hrs, ?_⟩
  simp only [stackArgAddr]
  have e : s.sp + BitVec.ofNat 64 (8 * j) = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
    simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
  rw [e]
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

/-- A stack argument, read after the working space changed. -/
theorem arg_read {s : State} (h : PreC s) {m : Mem} (hm : ∀ x, zOf s ≤ ofs (bOf s) x → m x = s.mem x)
    {j : Nat} (hj : j < 10) : m.readW (stackArgAddr s j) 64 = stackArg s j := by
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
def kMoves : List Instr :=
  [mov .s0 .a0, mov .s1 .a2, mov .s2 .a4, mov .s3 .a6, mov .a1 .a5, .addSp .t0 0,
    .load .d .s4 .t0 0, .load .d .s5 .t0 16, .load .d .s6 .t0 32, .load .d .a0 .t0 48,
    .load .d .a7 .t0 56]

theorem entry_eq : VG.Impl.RsaKeyGen.RISCV64.Key.entry = save 64 ++ kMoves := rfl

/-- The moves, after `save`: the arguments are in the registers kept. -/
theorem moves_ok {s0 e : State} (h : PreC s0) (F : Saved s0 (bOf s0) e) :
    WP isa (.block kMoves) e (CB s0 s0.mem) := by
  have hz := h.zk
  have hk := h.hn
  have fr : ∀ x, zOf s0 ≤ ofs (bOf s0) x → e.mem x = s0.mem x := fun x hx =>
    F.out x (.inr (Nat.le_trans (by omega_arith : 0 + 96 ≤ zOf s0) hx))
  have hrd : e.rd = s0.rd := F.keep.2.1
  have hin : ∀ j < 10, InRegions (e.rd ++ e.wr) (stackArgAddr s0 j) 8 := fun j hj =>
    arg_in (by rw [hrd, h.hrd]; simp) hj
  have l : ∀ j, (stackArgAddr s0 j).toNat % 8 = 0 := arg_al h
  have r : ∀ j < 10, e.mem.readW (stackArgAddr s0 j) 64 = stackArg s0 j := fun j hj => arg_read h fr hj
  have a0 : s0.sp + BitVec.ofNat 64 0 = stackArgAddr s0 0 := rfl
  have a2 : stackArgAddr s0 0 + BitVec.ofNat 64 16 = stackArgAddr s0 2 := arg_succ s0 2
  have a4 : stackArgAddr s0 0 + BitVec.ofNat 64 32 = stackArgAddr s0 4 := arg_succ s0 4
  have a6 : stackArgAddr s0 0 + BitVec.ofNat 64 48 = stackArgAddr s0 6 := arg_succ s0 6
  have a7 : stackArgAddr s0 0 + BitVec.ofNat 64 56 = stackArgAddr s0 7 := arg_succ s0 7
  have hg : ∀ r, r ≠ .t0 → r ≠ .s11 → e.gpr r = s0.gpr r := fun r h0 h11 =>
    F.keep.gpr (by simp [h0, h11])
  have hb : WP isa (.block kMoves) e fun u =>
      (u.gpr .s0 = s0.gpr .a0 ∧ u.gpr .s1 = s0.gpr .a2 ∧ u.gpr .s2 = s0.gpr .a4 ∧ u.gpr .s3 = s0.gpr .a6 ∧
        u.gpr .a1 = s0.gpr .a5 ∧ u.gpr .s4 = stackArg s0 0 ∧ u.gpr .s5 = stackArg s0 2 ∧
        u.gpr .s6 = stackArg s0 4 ∧ u.gpr .a0 = stackArg s0 6 ∧ u.gpr .a7 = stackArg s0 7 ∧
        u.mem = e.mem ∧ u.sp = e.sp) ∧
      Keep [.s0, .s1, .s2, .s3, .a1, .t0, .s4, .s5, .s6, .a0, .a7] e u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [kMoves, mov, exec_addSp (d := .t0) (imm := 0) (by decide), F.sp, hg .a0 (by decide) (by decide),
      hg .a2 (by decide) (by decide), hg .a4 (by decide) (by decide), hg .a6 (by decide) (by decide),
      hg .a5 (by decide) (by decide), add_ofNat_zero', a0, a2, a4, a6, a7, l 0, l 2, l 4, l 6, l 7,
      hin 0 (by decide), hin 2 (by decide), hin 4 (by decide), hin 6 (by decide), hin 7 (by decide),
      r 0 (by decide), r 2 (by decide), r 4 (by decide), r 6 (by decide), r 7 (by decide)]
  refine WP.mono hb fun u ⟨⟨u0, u1, u2, u3, ua1, v4, v5, v6, v0, v7, um, usp⟩, ku⟩ => ?_
  exact ⟨u0, u1, u2, u3, ua1, v4, v5, v6, v0, v7, (ku.gpr (by decide)).trans F.s11,
    (ku.gpr (by decide)).trans (hg .ra (by decide) (by decide)), ku.2.1.trans hrd,
    ku.2.2.trans F.keep.2.2, fun i hi => by rw [um]; exact F.saved i hi, fun x hx => by rw [um]; exact fr x hx⟩

/-- `entry`: the working space's header holds the saved registers, and the
arguments are in the registers kept. -/
theorem entry_ok {s0 : State} (h : PreC s0) : WP isa (.block VG.Impl.RsaKeyGen.RISCV64.Key.entry) s0 (CB s0 s0.mem) := by
  have hz := h.zk
  rw [entry_eq, WP.block_append_iff]
  exact WP.mono (save_ok s0 (i := 8) (by decide) (arg_in (by rw [h.hrd]; simp) (by decide))
    (arg_al h 8) h.scr (by omega_arith)) fun e F => moves_ok h F

/-! ## The exit -/

/-- What `restore` needs. -/
structure CE (s0 s : State) : Prop where
  s11 : s.gpr .s11 = bOf s0
  ra : s.gpr .ra = s0.gpr .ra
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  hdr : ∀ i < 12, word s.mem (bOf s0) (8 * i) = s0.gpr (saved i)

theorem CB.ce {s0 s : State} {M : Mem} (c : CB s0 M s) : CE s0 s := ⟨c.s11, c.ra, c.rd, c.wr, c.hdr⟩

theorem preserved_saved : ∀ r ∈ preserved, ∃ i < 12, saved i = r := by decide

theorem restore_ok {s0 t : State} (h : PreC s0) (c : CE s0 t) :
    WP isa (.block restore) t fun v =>
      (∀ r ∈ preserved, v.gpr r = s0.gpr r) ∧ v.gpr .ra = s0.gpr .ra ∧ v.mem = t.mem ∧
        v.gpr .a0 = t.gpr .a0 := by
  have hz := h.zk
  have hs : Scr t (bOf s0) (zOf s0) := Scr.of_mem (by rw [c.wr]; exact h.sR_wr) h.ws h.al
  refine WP.mono (VG.Proof.Rsa.RISCV64.Keys.restore_ok t hs (by omega_arith) c.s11 c.hdr)
    fun v ⟨hv, ho, hm, _⟩ => ?_
  refine ⟨fun r hr => ?_, (ho .ra (by decide)).trans c.ra, hm, ho .a0 (by decide)⟩
  obtain ⟨i, hi, rfl⟩ := preserved_saved r hr
  exact hv i hi

end VG.Proof.RsaKeyGen.RISCV64.Key
