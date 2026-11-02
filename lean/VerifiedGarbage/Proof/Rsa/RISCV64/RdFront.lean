module

public import VerifiedGarbage.Spec.Rsa.RecoverDet
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Rsa.RISCV64.RecoverDet
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyBytes
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCheck
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Rsa.RISCV64.CrtValFront
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_rsa_recover_primes_det` on RISC-V: the contract, the entry, the modulus' check, the failure and the exit

`PreC s`: the shared contract's precondition (`recoverPrimesDetContract`),
by name (`preC_of`); `fnPost`: its postcondition on the registers and the
stack, which implies the shared contract's (`rd_implies`).

`CB s0 M s`: the arguments are in the registers `entry` moves them to,
the header's first twelve words hold the caller's saved registers, and
memory outside the working space (the stack arguments 2 and 3) is `M`'s.
`entry_ok` establishes it, every step of the body keeps it (`CB.of_keep`,
`CB.step`, in either view of the working space), and `restore_ok'` ends it
with the caller's registers back. `nCheck_ok`: `s0 = 0` exactly when `n` is
a valid modulus; `fail_ok`: zeros written and 0 returned.
-/

-- separate module: its proofs (the entry's and the exit's symbolic execution, `rd_implies`) are not
-- re-checked with every change to the body's proofs

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.RecDet

open VG VG.RISCV64

theorem stackArgs_four (s : State) :
    List.map (stackArg s) (List.range 4) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3] := rfl

/-! ## The buffers -/

abbrev pR (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
abbrev qR (s : State) : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
abbrev nR (s : State) : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .a6, (s.gpr .a7).toNat⟩
abbrev dR (s : State) : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
abbrev sR (s : State) : Region := ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
abbrev aR (s : State) : Region := ⟨stackArgAddr s 0, 32⟩

/-- What the code needs of `recoverPrimesDetContract.pre`, by name. -/
structure PreC (s : State) : Prop where
  sp16 : s.sp.toNat % 16 = 0
  sp2 : s.sp.toNat + 32 ≤ 2 ^ 64
  hrd : s.rd = [nR s, eR s, dR s, aR s]
  hwr : s.wr = [pR s, qR s, sR s]
  pq : (pR s).Disjoint (qR s)
  pn : (pR s).Disjoint (nR s)
  pe : (pR s).Disjoint (eR s)
  pd : (pR s).Disjoint (dR s)
  ps : (pR s).Disjoint (sR s)
  pa : (pR s).Disjoint (aR s)
  qn : (qR s).Disjoint (nR s)
  qe : (qR s).Disjoint (eR s)
  qd : (qR s).Disjoint (dR s)
  qs : (qR s).Disjoint (sR s)
  qa : (qR s).Disjoint (aR s)
  ns : (nR s).Disjoint (sR s)
  es : (eR s).Disjoint (sR s)
  ds : (dR s).Disjoint (sR s)
  sa : (sR s).Disjoint (aR s)
  wp : (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64
  wq : (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64
  wn : (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64
  we : (s.gpr .a6).toNat + (s.gpr .a7).toNat ≤ 2 ^ 64
  wd : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  ws : (stackArg s 2).toNat + (stackArg s 3).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .a5).toNat
  k2 : (s.gpr .a5).toNat ≤ 1024
  h1 : (s.gpr .a1).toNat = (s.gpr .a5).toNat
  h3 : (s.gpr .a3).toNat = (s.gpr .a5).toNat
  e1 : 1 ≤ (s.gpr .a7).toNat
  e2 : (s.gpr .a7).toNat ≤ 8
  d1 : 1 ≤ (stackArg s 1).toNat
  d2 : (stackArg s 1).toNat ≤ (s.gpr .a5).toNat
  hs : Spec.Rsa.scratchWords (s.gpr .a5).toNat ≤ (stackArg s 3).toNat
  al : (stackArg s 2).toNat % 8 = 0

theorem preC_of {s : State} (h : (Spec.Rsa.recoverPrimesDetContract RISCV64.abi).pre s) : PreC s := by
  sig_pre [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, RISCV64.abi, RISCV64.argRegs,
    stackArgs_four, List.append_eq, List.range, List.range.loop] at h
  obtain ⟨sp16, sp2, hrd, hwr, pq, pn, pe, pd, ps, pa, qn, qe, qd, qs, qa, ns, es, ds, sa, wp, wq, wn, we, wd,
    ws, ⟨k1, k2⟩, h1, h3, e1, e2, d1, d2, hs, al⟩ := h
  exact ⟨sp16, sp2, hrd, hwr, pq, pn, pe, pd, ps, pa, qn, qe, qd, qs, qa, ns, es, ds, sa, wp, wq, wn, we, wd,
    ws, k1, k2, h1, h3, e1, e2, d1, d2, hs, al⟩

/-! ## The values -/

/-- `n_len`, and the inputs' bytes and values, as the function reads them. -/
abbrev kOf (s0 : State) : Nat := (s0.gpr .a5).toNat
abbrev nB (s0 : State) : List Byte := Spec.Rsa.bytesAt s0.mem (s0.gpr .a4) (kOf s0)
abbrev eB (s0 : State) : List Byte := Spec.Rsa.bytesAt s0.mem (s0.gpr .a6) (s0.gpr .a7).toNat
abbrev dB (s0 : State) : List Byte := Spec.Rsa.bytesAt s0.mem (stackArg s0 0) (stackArg s0 1).toNat
abbrev Nv (s0 : State) : Nat := Spec.Rsa.os2ip (nB s0)
abbrev Ev (s0 : State) : Nat := Spec.Rsa.os2ip (eB s0)
abbrev Dv (s0 : State) : Nat := Spec.Rsa.os2ip (dB s0)

/-! ## The postcondition -/

/-- The shared contract's postcondition, on the registers and the stack. -/
def fnPost (s s' : State) : Prop :=
  Spec.Rsa.writtenAll s'.mem [(s.gpr .a0, kOf s), (s.gpr .a2, kOf s)] ((s'.gpr .a0).setWidth 32)
    ((Spec.Rsa.primesKeyDet (nB s) (eB s) (dB s)).map fun v => [v.1, v.2])

/-- The shared contract, its postcondition on the registers and the stack. -/
def fnContract : Contract isa where
  pre := (Spec.Rsa.recoverPrimesDetContract RISCV64.abi).pre
  post := fnPost
  pub := (Spec.Rsa.recoverPrimesDetContract RISCV64.abi).pub

/-- A state meeting the precondition: a 64-byte modulus and factors, one-byte
exponents, and the stack arguments at `0x10000`. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x1100 | .a3 => 64 | .a4 => 0x2000 | .a5 => 64
    | .a6 => 0x3100 | .a7 => 1 | _ => 0
  sp := 0x10000
  mem a :=
    bif Nat.beq a.toNat 0x10001 then 0x30 else bif Nat.beq a.toNat 0x10008 then 1
    else bif Nat.beq a.toNat 0x10012 then 0x02 else bif Nat.beq a.toNat 0x10018 then 0x20
    else bif Nat.beq a.toNat 0x10019 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3100, 1⟩, ⟨0x3000, 1⟩, ⟨0x10000, 32⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 64⟩, ⟨0x20000, 8448⟩]

theorem rd_implies : fnContract.Implies (Spec.Rsa.recoverPrimesDetContract RISCV64.abi) where
  pre := fun _ h => h
  post := by
    sig_implies_post [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, RISCV64.abi,
      RISCV64.argRegs, fnContract, fnPost, stackArgs_four, List.append_eq]
  pub := fun _ _ _ _ h => h
  sat := by
    sig_implies_sat [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, RISCV64.abi,
      RISCV64.argRegs, fnContract, stackArgs_four, List.append_eq] [satState, stackArg, stackArgAddr,
      Mem.readW, Mem.read] using satState

end VG.Proof.Rsa.RISCV64.RecDet


namespace VG.Proof.Rsa.RISCV64.RecDet

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Proof.Rsa.RISCV64.CrtValues (past_of_disjoint bytes_contains bytes_past bytes_sep bytes_in
  bytesAt_congr inRegions_left zeros_keep bytesAt_zero out_of_scr preserved_saved)
open VG.Impl.Rsa.RISCV64.Keys (seqs saved mov save restore zeroBytes)
open VG.Impl.Rsa.RISCV64.RecoverDet (entry nCheck fail)

/-- The working space: the stack arguments 2 and 3. -/
abbrev bOf (s : State) : Addr := stackArg s 2
abbrev zOf (s : State) : Nat := (stackArg s 3).toNat * 8

/-- The registers the body keeps. -/
abbrev cbRegs : List Reg := [.s1, .s2, .s3, .s4, .s5, .s6, .a0, .a1, .s11, .ra]

/-- After `entry`, the body's state: the arguments' registers, the saved
registers in the header, and memory outside the working space `M`'s. -/
structure CB (s0 : State) (M : Mem) (s : State) : Prop where
  s1 : s.gpr .s1 = s0.gpr .a4
  s2 : s.gpr .s2 = s0.gpr .a5
  s3 : s.gpr .s3 = s0.gpr .a0
  s4 : s.gpr .s4 = s0.gpr .a2
  s5 : s.gpr .s5 = s0.gpr .a6
  s6 : s.gpr .s6 = s0.gpr .a7
  a0 : s.gpr .a0 = stackArg s0 0
  a1 : s.gpr .a1 = stackArg s0 1
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
    (k.gpr (hr _ (by decide))).trans h.s11, (k.gpr (hr _ (by decide))).trans h.ra,
    k.2.1.trans h.rd, k.2.2.trans h.wr,
    fun i hi => by rw [hm]; exact h.hdr i hi, fun x hx => by rw [hm]; exact h.frame x hx⟩

/-- A step that writes only arrays and slots from 96 on keeps `CB`, in any view `w`. -/
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

/-- The bytes of a region apart from the working space are `M`'s. -/
theorem CB.bytes {s0 s : State} {M : Mem} (h : CB s0 M s) {P : Addr} {L : Nat}
    (hd : (⟨P, L⟩ : Region).Disjoint (sR s0)) (hL : L ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt s.mem P L = Spec.Rsa.bytesAt M P L :=
  bytesAt_congr fun _ hi => h.frame _ (bytes_past hd hi hL)

/-! ## The entry -/

theorem PreC.sR_wr {s : State} (h : PreC s) : sR s ∈ s.wr := by rw [h.hwr]; simp

theorem PreC.zk {s : State} (h : PreC s) : 8 * (16 * kOf s + 32) ≤ zOf s := by
  have := h.hs; simp only [Spec.Rsa.scratchWords] at this; simp only [zOf, kOf]; omega_arith

theorem PreC.scr {s : State} (h : PreC s) : Scr s (bOf s) (zOf s) :=
  Scr.of_mem h.sR_wr h.ws h.al

theorem arg_al {s : State} (h : PreC s) (j : Nat) : (stackArgAddr s j).toNat % 8 = 0 := by
  have := h.sp16; have := h.sp2
  simp only [stackArgAddr, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith

theorem arg_in {s : State} {rs : List Region} (hrs : aR s ∈ rs) {j : Nat} (hj : j < 4) :
    InRegions rs (stackArgAddr s j) 8 := by
  refine ⟨_, hrs, ?_⟩
  simp only [stackArgAddr]
  have e : s.sp + BitVec.ofNat 64 (8 * j) = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
    simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
  rw [e]
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

/-- A stack argument, read after the working space changed. -/
theorem arg_read {s : State} (h : PreC s) {m : Mem} (hm : ∀ x, zOf s ≤ ofs (bOf s) x → m x = s.mem x)
    {j : Nat} (hj : j < 4) : m.readW (stackArgAddr s j) 64 = stackArg s j := by
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
def rdMoves : List Instr :=
  [mov .s3 .a0, mov .s4 .a2, mov .s1 .a4, mov .s2 .a5, mov .s5 .a6, mov .s6 .a7, .addSp .t0 0,
    .load .d .a0 .t0 0, .load .d .a1 .t0 8]

theorem entry_eq : entry = save 16 ++ rdMoves := rfl

/-- The moves, after `save`: the arguments are in the registers kept. -/
theorem moves_ok {s0 e : State} (h : PreC s0) (F : Saved s0 (bOf s0) e) :
    WP isa (.block rdMoves) e (CB s0 s0.mem) := by
  have hz := h.zk
  have hk := h.k1
  have fr : ∀ x, zOf s0 ≤ ofs (bOf s0) x → e.mem x = s0.mem x := fun x hx =>
    F.out x (.inr (Nat.le_trans (by omega_arith : 0 + 96 ≤ zOf s0) hx))
  have hrd : e.rd = s0.rd := F.keep.2.1
  have hin : ∀ j < 4, InRegions (e.rd ++ e.wr) (stackArgAddr s0 j) 8 := fun j hj =>
    arg_in (by rw [hrd, h.hrd]; simp) hj
  have l : ∀ j, (stackArgAddr s0 j).toNat % 8 = 0 := arg_al h
  have r : ∀ j < 4, e.mem.readW (stackArgAddr s0 j) 64 = stackArg s0 j := fun j hj => arg_read h fr hj
  have a0 : s0.sp + BitVec.ofNat 64 0 = stackArgAddr s0 0 := rfl
  have a1 : stackArgAddr s0 0 + BitVec.ofNat 64 8 = stackArgAddr s0 1 := arg_succ s0 1
  have hg : ∀ r, r ≠ .t0 → r ≠ .s11 → e.gpr r = s0.gpr r := fun r h0 h11 =>
    F.keep.gpr (by simp [h0, h11])
  have hb : WP isa (.block rdMoves) e fun u =>
      (u.gpr .s3 = s0.gpr .a0 ∧ u.gpr .s4 = s0.gpr .a2 ∧ u.gpr .s1 = s0.gpr .a4 ∧ u.gpr .s2 = s0.gpr .a5 ∧
        u.gpr .s5 = s0.gpr .a6 ∧ u.gpr .s6 = s0.gpr .a7 ∧ u.gpr .a0 = stackArg s0 0 ∧
        u.gpr .a1 = stackArg s0 1 ∧ u.mem = e.mem ∧ u.sp = e.sp) ∧
      Keep [.s3, .s4, .s1, .s2, .s5, .s6, .t0, .a0, .a1] e u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [rdMoves, mov, exec_addSp (d := .t0) (imm := 0) (by decide), F.sp, hg .a0 (by decide) (by decide),
      hg .a2 (by decide) (by decide), hg .a4 (by decide) (by decide), hg .a5 (by decide) (by decide),
      hg .a6 (by decide) (by decide), hg .a7 (by decide) (by decide), add_ofNat_zero', a0, a1, l 0, l 1,
      hin 0 (by decide), hin 1 (by decide), r 0 (by decide), r 1 (by decide)]
  refine WP.mono hb fun u ⟨⟨u3, u4, u1, u2, u5, u6, v0, v1, um, usp⟩, ku⟩ => ?_
  exact ⟨u1, u2, u3, u4, u5, u6, v0, v1, (ku.gpr (by decide)).trans F.s11,
    (ku.gpr (by decide)).trans (hg .ra (by decide) (by decide)), ku.2.1.trans hrd,
    ku.2.2.trans F.keep.2.2, fun i hi => by rw [um]; exact F.saved i hi, fun x hx => by rw [um]; exact fr x hx⟩

/-- `entry`: the working space's header holds the saved registers, and the
arguments are in the registers kept. -/
theorem entry_ok {s0 : State} (h : PreC s0) : WP isa (.block entry) s0 (CB s0 s0.mem) := by
  have hz := h.zk
  rw [entry_eq, WP.block_append_iff]
  exact WP.mono (save_ok s0 (i := 2) (by decide) (arg_in (by rw [h.hrd]; simp) (by decide))
    (arg_al h 2) h.scr (by omega_arith)) fun e F => moves_ok h F

/-! ## The modulus' check -/

theorem nCheck_ok {s0 s : State} (h : PreC s0) (c : CB s0 s0.mem s) :
    WP isa nCheck s fun t =>
      (t.gpr .s0 = 0 ↔ Spec.Rsa.modulusValid (Nv s0) (kOf s0) = true) ∧
        t.mem = s.mem ∧ Keep [.s7, .s8, .s0, .t4, .t5] s t := by
  have hk1 : 64 ≤ kOf s0 := h.k1
  have hk2 : kOf s0 ≤ 1024 := h.k2
  have hL : kOf s0 ≤ 2 ^ 64 := by omega_arith
  rw [nCheck, WP.seq_iff]
  have hb : WP isa (.block [mov .s7 .s1, mov .s8 .s2]) s fun u =>
      (u.gpr .s7 = off (s0.gpr .a4) 0 ∧ u.gpr .s8 = BitVec.ofNat 64 (kOf s0) ∧ u.mem = s.mem ∧
        u.sp = s.sp) ∧ Keep [.s7, .s8] s u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [mov, c.s1, c.s2, add_ofNat_zero', BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono hb fun u ⟨⟨u7, u8, um, usp⟩, ku⟩ => ?_
  have hrd : u.rd = s0.rd := ku.2.1.trans c.rd
  refine WP.mono (check_ok (nb := Spec.Rsa.bytesAt s.mem (s0.gpr .a4) (kOf s0)) u7 u8 hk1 hk2
    (by simp [Spec.Rsa.bytesAt])
    (fun i hi => by
      rw [hrd]
      exact inRegions_left (bytes_in (rs := s0.rd) (by rw [h.hrd]; simp) hL i hi))
    (fun i hi => by simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, um]))
    fun t ⟨t0, tm, kt⟩ => ?_
  rw [c.bytes h.ns hL] at t0
  exact ⟨t0, tm.trans um, Keep.trans' (Keep.mono ku (by decide)) (Keep.mono kt (by decide))⟩

/-! ## An invalid modulus -/

/-- The two outputs, `p` and `q`, `n_len` bytes each. -/
abbrev outs (s0 : State) : List (Addr × Nat) := [(s0.gpr .a0, kOf s0), (s0.gpr .a2, kOf s0)]

theorem PreC.pR_eq {s : State} (h : PreC s) : pR s = ⟨s.gpr .a0, kOf s⟩ := by simp only [pR, h.h1]
theorem PreC.qR_eq {s : State} (h : PreC s) : qR s = ⟨s.gpr .a2, kOf s⟩ := by simp only [qR, h.h3]

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
  have hk1 : 64 ≤ kOf s0 := h.k1
  have hk2 : kOf s0 ≤ 1024 := h.k2
  have lk : kOf s0 < 2 ^ 32 := by omega_arith
  have hk : 1 ≤ kOf s0 := by omega_arith
  have wp : (s0.gpr .a0).toNat + kOf s0 ≤ 2 ^ 64 := by have := h.wp; rw [h.h1] at this; exact this
  have wq : (s0.gpr .a2).toNat + kOf s0 ≤ 2 ^ 64 := by have := h.wq; rw [h.h3] at this; exact this
  have inW : ∀ {P : Addr} {L : Nat}, (⟨P, L⟩ : Region) ∈ s0.wr → L ≤ 2 ^ 64 → ∀ {u : State}, u.wr = s0.wr →
      ∀ i < L, InRegions u.wr (off P i) 1 := fun hr hL u hu i hi => by
    rw [hu]; exact bytes_in hr hL i hi
  have m1 : pR s0 ∈ s0.wr := by rw [h.hwr]; simp
  have m2 : qR s0 ∈ s0.wr := by rw [h.hwr]; simp
  rw [h.pR_eq] at m1
  rw [h.qR_eq] at m2
  have l2 : s.gpr .s2 = BitVec.ofNat 64 (kOf s0) := by rw [c.s2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  unfold fail
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (WP.rdwr (zeroBytes_ok c.s3 l2 (by decide) hk lk (inW m1 (by omega_arith) c.wr) wp))
    fun t1 ⟨⟨z1, o1, k1⟩, r1, w1, _⟩ => ?_
  have hz := h.zk
  have hZ : 96 ≤ zOf s0 := by omega_arith
  have c1 := c.of_out k1 o1 (by rw [← h.pR_eq]; exact h.ps) hZ
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (WP.rdwr (zeroBytes_ok c1.s4 (by rw [(k1.gpr (by decide))]; exact l2) (by decide) hk lk
    (inW m2 (by omega_arith) (w1.trans c.wr)) wq)) fun t2 ⟨⟨z2, o2, k2⟩, _, _, _⟩ => ?_
  have c2 := c1.of_out k2 o2 (by rw [← h.qR_eq]; exact h.qs) hZ
  have hb : WP isa (.block [.li .a0 0]) t2 fun u => (u.gpr .a0 = 0 ∧ u.mem = t2.mem) ∧ Keep [.a0] t2 u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [fin64_exec_li_zero]
  refine WP.mono hb fun u ⟨⟨u0, um⟩, ku⟩ => ?_
  refine ⟨⟨(ku.gpr (by decide)).trans c2.s11, (ku.gpr (by decide)).trans c2.ra, ku.2.1.trans c2.rd,
    ku.2.2.trans c2.wr, fun i hi => by rw [um]; exact c2.hdr i hi⟩, ?_, ?_⟩
  · rw [u0]; rfl
  · have p_q : (⟨s0.gpr .a0, kOf s0⟩ : Region).Disjoint ⟨s0.gpr .a2, kOf s0⟩ := by
      rw [← h.pR_eq, ← h.qR_eq]; exact h.pq
    simp only [outs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, um]
    refine ⟨bytesAt_zero fun c hc => ?_, bytesAt_zero fun c hc => z2 c hc⟩
    rw [zeros_keep p_q (by omega_arith) o2 hc]; exact z1 c hc

/-! ## The exit -/

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

end VG.Proof.Rsa.RISCV64.RecDet
