module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Contract
public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Key
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBase
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs

/-!
# `vg_rsa_keygen_key` on PPC64LE: what every stage keeps, and the entry

As `vg_rsa_crt_values`'s (`Proof/Rsa/PPC64LE/CvBase.lean`), for `keyP`:
`KPre s0`, the precondition's facts by name; `Base s0 s`: from the initial
state `s0`, the stack pointer, the link register and the regions are `s0`'s,
memory outside the working space (`kZ s0` bytes at `kB s0`) is `s0`'s, the
working space's base is in `r31`, and the header's first fourteen words hold
the saved `r14`–`r24` and `r29`–`r31`. `Args s0 s`: the pointers and lengths
in `r14`–`r24`. `entry_ok`: the entry establishes both.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Key

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Key (entry)
open VG.Impl.Rsa.PPC64LE.CrtValues (stackOff)
open VG.Proof.Rsa.PPC64LE.CrtValues (savedReg hdrVal readW_sep exec_addSp stackArg_addr past_of_disjoint)

/-- The working space's base and size, `p_len`, and `w = p_len / 2`. -/
abbrev kB (s0 : State) : Addr := PPC64LE.stackArg s0 8
abbrev kZ (s0 : State) : Nat := (PPC64LE.stackArg s0 9).toNat * 8
abbrev kL (s0 : State) : Nat := (s0.gpr .r8).toNat
abbrev kW (s0 : State) : Nat := kL s0 / 2

/-- The regions of the arguments. -/
abbrev rN (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
abbrev rD (s : State) : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
abbrev rP (s : State) : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
abbrev rQ (s : State) : Region := ⟨s.gpr .r9, (s.gpr .r10).toNat⟩
abbrev rDp (s : State) : Region := ⟨PPC64LE.stackArg s 0, (PPC64LE.stackArg s 1).toNat⟩
abbrev rDq (s : State) : Region := ⟨PPC64LE.stackArg s 2, (PPC64LE.stackArg s 3).toNat⟩
abbrev rQi (s : State) : Region := ⟨PPC64LE.stackArg s 4, (PPC64LE.stackArg s 5).toNat⟩
abbrev rE (s : State) : Region := ⟨PPC64LE.stackArg s 6, (PPC64LE.stackArg s 7).toNat⟩
abbrev rS (s : State) : Region := ⟨kB s, kZ s⟩
abbrev rA (s : State) : Region := ⟨stackArgAddr s 0, 80⟩

/-- The precondition's facts, by name. -/
structure KPre (s : State) : Prop where
  sp : s.sp.toNat + 32 + 8 * 18 ≤ 2 ^ 64
  rd : s.rd = [rE s, rA s]
  wr : s.wr = [rN s, rD s, rP s, rQ s, rDp s, rDq s, rQi s, rS s]
  nS : (rN s).Disjoint (rS s)
  dS : (rD s).Disjoint (rS s)
  pS : (rP s).Disjoint (rS s)
  qS : (rQ s).Disjoint (rS s)
  dpS : (rDp s).Disjoint (rS s)
  dqS : (rDq s).Disjoint (rS s)
  qiS : (rQi s).Disjoint (rS s)
  eS : (rE s).Disjoint (rS s)
  sA : (rS s).Disjoint (rA s)
  nD : (rN s).Disjoint (rD s)
  nP : (rN s).Disjoint (rP s)
  nQ : (rN s).Disjoint (rQ s)
  nDp : (rN s).Disjoint (rDp s)
  nDq : (rN s).Disjoint (rDq s)
  nQi : (rN s).Disjoint (rQi s)
  dP : (rD s).Disjoint (rP s)
  dQ : (rD s).Disjoint (rQ s)
  dDp : (rD s).Disjoint (rDp s)
  dDq : (rD s).Disjoint (rDq s)
  dQi : (rD s).Disjoint (rQi s)
  pQ : (rP s).Disjoint (rQ s)
  pDp : (rP s).Disjoint (rDp s)
  pDq : (rP s).Disjoint (rDq s)
  pQi : (rP s).Disjoint (rQi s)
  qDp : (rQ s).Disjoint (rDp s)
  qDq : (rQ s).Disjoint (rDq s)
  qQi : (rQ s).Disjoint (rQi s)
  dpDq : (rDp s).Disjoint (rDq s)
  dpQi : (rDp s).Disjoint (rQi s)
  dqQi : (rDq s).Disjoint (rQi s)
  wN : (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64
  wD : (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64
  wP : (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  wQ : (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64
  wDp : (PPC64LE.stackArg s 0).toNat + (PPC64LE.stackArg s 1).toNat ≤ 2 ^ 64
  wDq : (PPC64LE.stackArg s 2).toNat + (PPC64LE.stackArg s 3).toNat ≤ 2 ^ 64
  wQi : (PPC64LE.stackArg s 4).toNat + (PPC64LE.stackArg s 5).toNat ≤ 2 ^ 64
  wE : (PPC64LE.stackArg s 6).toNat + (PPC64LE.stackArg s 7).toNat ≤ 2 ^ 64
  wS : (kB s).toNat + kZ s ≤ 2 ^ 64
  l1 : 32 ≤ kL s
  l2 : kL s ≤ 512
  l8 : kL s % 8 = 0
  nl : (s.gpr .r4).toNat = 2 * kL s
  dl : (s.gpr .r6).toNat = (s.gpr .r4).toNat
  ql : (s.gpr .r10).toNat = kL s
  dpl : (PPC64LE.stackArg s 1).toNat = kL s
  dql : (PPC64LE.stackArg s 3).toNat = kL s
  qil : (PPC64LE.stackArg s 5).toNat = kL s
  el1 : 1 ≤ (PPC64LE.stackArg s 7).toNat
  el8 : (PPC64LE.stackArg s 7).toNat ≤ 8
  sl : 8 * (32 * kL s + 32) ≤ kZ s

theorem kpre {s : State} (h : keyP.pre s) : KPre s := by
  obtain ⟨hsp, hrd, hwr, nD, nP, nQ, nDp, nDq, nQi, -, nS, -, dP, dQ, dDp, dDq, dQi, -, dS, -, pQ, pDp, pDq, pQi, -,
    pS, -, qDp, qDq, qQi, -, qS, -, dpDq, dpQi, -, dpS, -, dqQi, -, dqS, -, -, qiS, -, eS, sA, wN, wD, wP, wQ,
    wDp, wDq, wQi, wE, wS, ⟨l1, l2, l8⟩, nl, dl, ql, dpl, dql, qil, el1, el8, sl⟩ := h
  simp only [Spec.Rsa.scratchWords] at sl
  exact ⟨hsp, hrd, hwr, nS, dS, pS, qS, dpS, dqS, qiS, eS, sA, nD, nP, nQ, nDp, nDq, nQi, dP, dQ, dDp, dDq, dQi,
    pQ, pDp, pDq, pQi, qDp, qDq, qQi, dpDq, dpQi, dqQi, wN, wD, wP, wQ, wDp, wDq, wQi, wE, wS, l1, l2, l8, nl, dl,
    ql, dpl, dql, qil, el1, el8, by simp only [kZ, kL]; omega_arith⟩

/-- The pointers and lengths, in `r14`–`r24`. -/
structure Args (s0 s : State) : Prop where
  r14 : s.gpr .r14 = s0.gpr .r3
  r15 : s.gpr .r15 = s0.gpr .r5
  r16 : s.gpr .r16 = s0.gpr .r7
  r17 : s.gpr .r17 = s0.gpr .r9
  r18 : s.gpr .r18 = PPC64LE.stackArg s0 0
  r19 : s.gpr .r19 = PPC64LE.stackArg s0 2
  r20 : s.gpr .r20 = PPC64LE.stackArg s0 4
  r21 : s.gpr .r21 = PPC64LE.stackArg s0 6
  r22 : s.gpr .r22 = s0.gpr .r8
  r23 : s.gpr .r23 = PPC64LE.stackArg s0 7
  r24 : s.gpr .r24 = s0.gpr .r4

/-- The registers `Args` is about. -/
abbrev argsRegs : List Reg := [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24]

theorem Args.of_keep {s0 s t : State} (h : Args s0 s) {rs : List Reg} (k : Keep rs s t)
    (hr : ∀ r ∈ argsRegs, r ∉ rs := by decide) : Args s0 t := by
  have e : ∀ r ∈ argsRegs, t.gpr r = s.gpr r := fun r hr' => k.gpr r (hr r hr')
  exact ⟨(e _ (by decide)).trans h.r14, (e _ (by decide)).trans h.r15, (e _ (by decide)).trans h.r16,
    (e _ (by decide)).trans h.r17, (e _ (by decide)).trans h.r18, (e _ (by decide)).trans h.r19,
    (e _ (by decide)).trans h.r20, (e _ (by decide)).trans h.r21, (e _ (by decide)).trans h.r22,
    (e _ (by decide)).trans h.r23, (e _ (by decide)).trans h.r24⟩

structure Base (s0 s : State) : Prop where
  pre : keyP.pre s0
  sp : s.sp = s0.sp
  lr : s.lr = s0.lr
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  frame : ∀ x, kZ s0 ≤ ofs (kB s0) x → s.mem x = s0.mem x
  hdr : ∀ i < 14, s.mem.readW (off (kB s0) (8 * i)) 64 = hdrVal s0 i
  r31 : s.gpr .r31 = kB s0

/-- The stack argument `i < 10` is readable. -/
theorem arg_rd {s0 s : State} (h : keyP.pre s0) (hrd : s.rd = s0.rd) (hsp : s.sp = s0.sp) {i : Nat}
    (hi : i < 10) : InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8 := by
  have p := kpre h
  have hm : rA s0 ∈ s0.rd := by rw [p.rd]; simp
  refine ⟨_, List.mem_append_left _ (hrd ▸ hm), ?_⟩
  have hs := p.sp
  simp only [stackArgAddr, hsp]
  rw [show s0.sp + BitVec.ofNat 64 (32 + 8 * (8 + i)) = stackArgAddr s0 0 + BitVec.ofNat 64 (8 * i) by
    rw [stackArgAddr, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega_arith]
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

/-- `stackArg r i`: the stack argument `i` into `r`. -/
theorem stackArg_ok {s0 s : State} (h : keyP.pre s0) (hrd : s.rd = s0.rd) (hsp : s.sp = s0.sp)
    {r : Reg} (hr : r ≠ .r0) {i : Nat} (hi : i < 10) {rest : List Instr} {Q : State → Prop}
    (k : WP isa (.block rest) (s.write r (PPC64LE.stackArg s i)) Q) :
    WP isa (.block (VG.Impl.Rsa.PPC64LE.CrtValues.stackArg r i ++ rest)) s Q := by
  have rd := arg_rd h hrd hsp hi
  have ho : stackOff i < 2 ^ 15 := by simp only [stackOff]; omega_arith
  rw [WP.block_append_iff]
  have ea : (s.write r (s.sp + BitVec.ofNat 64 (stackOff i))).gpr r + BitVec.ofNat 64 0 = stackArgAddr s i := by
    simp only [State.write, ite_true, BitVec.add_zero, stackArg_addr]
  have hrd' : InRegions ((s.write r (s.sp + BitVec.ofNat 64 (stackOff i))).rd ++
      (s.write r (s.sp + BitVec.ofNat 64 (stackOff i))).wr)
      ((s.write r (s.sp + BitVec.ofNat 64 (stackOff i))).gpr r + BitVec.ofNat 64 0) 8 := by
    rw [ea]; exact rd
  refine WP.of_runBlock ⟨s.write r (PPC64LE.stackArg s i), ?_, k⟩
  simp only [VG.Impl.Rsa.PPC64LE.CrtValues.stackArg, runBlock_cons, runStep_some, runBlock_nil, exec_addSp ho,
    exec_load_d hr ⟨by decide, by decide⟩ hrd', Option.some.injEq]
  rw [ea, VG.Proof.Rsa.PPC64LE.Keys.write_write]
  rfl

/-- The stack arguments are `s0`'s. -/
theorem Base.stackArg {s0 s : State} (h : Base s0 s) {i : Nat} (hi : i < 10) :
    PPC64LE.stackArg s i = PPC64LE.stackArg s0 i := by
  have p := kpre h.pre
  have hs := p.sp
  simp only [PPC64LE.stackArg, stackArgAddr, h.sp]
  refine Mem.readW_congr fun b hb => h.frame _ (past_of_disjoint p.sA.symm ?_)
  rw [show s0.sp + BitVec.ofNat 64 (32 + 8 * (8 + i)) + BitVec.ofNat 64 b =
    stackArgAddr s0 0 + BitVec.ofNat 64 (8 * i + b) by
      rw [stackArgAddr, BitVec.add_assoc, BitVec.add_assoc, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
      congr 2; omega_arith]
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

/-- A step that keeps memory and `r31` keeps `Base`. -/
theorem Base.of_regs {s0 s t : State} (h : Base s0 s) {rs : List Reg} (k : Keep rs s t) (hm : t.mem = s.mem)
    (hr : .r31 ∉ rs := by decide) : Base s0 t :=
  ⟨h.pre, k.sp.trans h.sp, k.lr.trans h.lr, k.rd.trans h.rd, k.wr.trans h.wr,
    fun x hx => by rw [hm]; exact h.frame x hx, fun i hi => by rw [hm]; exact h.hdr i hi,
    (k.gpr _ hr).trans h.r31⟩

/-- `stackArg r i`, from a state with `Base`. -/
theorem argStep {s0 s : State} (h : Base s0 s) {r : Reg} (hr : r ≠ .r0) (hr31 : .r31 ∉ [r]) {i : Nat}
    (hi : i < 10) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Base s0 t → t.gpr r = PPC64LE.stackArg s0 i → Keep [r] s t → WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.Rsa.PPC64LE.CrtValues.stackArg r i ++ rest)) s Q :=
  stackArg_ok h.pre h.rd h.sp hr hi (k _ (h.of_regs (Keep.write _ _ _) rfl hr31)
    (by simp only [State.write, ↓reduceIte]; exact h.stackArg hi) (Keep.write _ _ _))

/-! ## The entry -/

/-- The header after the entry's stores. -/
def entryMem (s0 : State) : Mem :=
  (((((((((((((s0.mem.writeW (off (kB s0) 0) (s0.gpr .r14)).writeW (off (kB s0) 8) (s0.gpr .r15)).writeW
    (off (kB s0) 16) (s0.gpr .r16)).writeW (off (kB s0) 24) (s0.gpr .r17)).writeW (off (kB s0) 32)
      (s0.gpr .r18)).writeW (off (kB s0) 40) (s0.gpr .r19)).writeW (off (kB s0) 48) (s0.gpr .r20)).writeW
        (off (kB s0) 56) (s0.gpr .r21)).writeW (off (kB s0) 64) (s0.gpr .r22)).writeW (off (kB s0) 72)
          (s0.gpr .r23)).writeW (off (kB s0) 80) (s0.gpr .r24)).writeW (off (kB s0) 88) (s0.gpr .r29)).writeW
            (off (kB s0) 96) (s0.gpr .r30)).writeW (off (kB s0) 104) (s0.gpr .r31)

theorem entryMem_frame {s0 : State} (h : keyP.pre s0) :
    ∀ x, kZ s0 ≤ ofs (kB s0) x → entryMem s0 x = s0.mem x := by
  have p := kpre h
  have nw := p.wS
  have hz := p.sl
  intro x hx
  have o : ∀ (m : Mem) (d : Nat) (v : BitVec 64), d + 8 ≤ 112 → (m.writeW (off (kB s0) d) v) x = m x :=
    fun m d v hd => writeW_outside m (kB s0) (d := d) v (by omega_arith) x (Or.inr (by omega_arith))
  simp only [entryMem]
  rw [o _ 104 _ (by decide), o _ 96 _ (by decide), o _ 88 _ (by decide), o _ 80 _ (by decide),
    o _ 72 _ (by decide), o _ 64 _ (by decide), o _ 56 _ (by decide), o _ 48 _ (by decide),
    o _ 40 _ (by decide), o _ 32 _ (by decide), o _ 24 _ (by decide), o _ 16 _ (by decide),
    o _ 8 _ (by decide), o _ 0 _ (by decide)]

theorem entryMem_hdr (s0 : State) :
    ∀ i < 14, (entryMem s0).readW (off (kB s0) (8 * i)) 64 = hdrVal s0 i := by
  intro i hi
  simp only [entryMem]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11 ∨ i = 12 ∨ i = 13 by omega_arith) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := decide) only [hdrVal, savedReg, Nat.mul_zero, Nat.reduceMul, readW_sep, Mem.readW_writeW_self64]

theorem entry_eq : entry = VG.Impl.Rsa.PPC64LE.CrtValues.stackArg .r11 8 ++ (([.store .d .r14 .r11 0,
    .store .d .r15 .r11 8, .store .d .r16 .r11 16, .store .d .r17 .r11 24, .store .d .r18 .r11 32,
    .store .d .r19 .r11 40, .store .d .r20 .r11 48, .store .d .r21 .r11 56, .store .d .r22 .r11 64,
    .store .d .r23 .r11 72, .store .d .r24 .r11 80, .store .d .r29 .r11 88, .store .d .r30 .r11 96,
    .store .d .r31 .r11 104, .addi .r31 .r11 0, .addi .r14 .r3 0, .addi .r15 .r5 0, .addi .r16 .r7 0,
    .addi .r17 .r9 0, .addi .r22 .r8 0, .addi .r24 .r4 0] : List Instr) ++
    (VG.Impl.Rsa.PPC64LE.CrtValues.stackArg .r18 0 ++ (VG.Impl.Rsa.PPC64LE.CrtValues.stackArg .r19 2 ++
      (VG.Impl.Rsa.PPC64LE.CrtValues.stackArg .r20 4 ++ (VG.Impl.Rsa.PPC64LE.CrtValues.stackArg .r21 6 ++
        (VG.Impl.Rsa.PPC64LE.CrtValues.stackArg .r23 7 ++ ([] : List Instr))))))) := rfl

/-- The registers the entry changes. -/
abbrev entryRegs : List Reg := [.r11, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r31]

theorem entry_ok {s0 : State} (h : keyP.pre s0) :
    WP isa (.block entry) s0 fun s => Base s0 s ∧ Args s0 s ∧ Keep entryRegs s0 s := by
  have p := kpre h
  have nw := p.wS
  have hz := p.sl
  have hm : (⟨kB s0, kZ s0⟩ : Region) ∈ s0.wr := by rw [p.wr]; simp
  have hs : Scr s0 (kB s0) (kZ s0) := Scr.of_mem hm nw
  rw [entry_eq]
  refine stackArg_ok h rfl rfl (r := .r11) (by decide) (by decide) ?_
  have k1 : Keep [.r11] s0 (s0.write .r11 (PPC64LE.stackArg s0 8)) := Keep.write _ _ _
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r14, .r15, .r16, .r17, .r22, .r24, .r31] (Q := fun s => s.mem = entryMem s0 ∧
      s.gpr .r31 = kB s0 ∧ s.gpr .r14 = s0.gpr .r3 ∧ s.gpr .r15 = s0.gpr .r5 ∧ s.gpr .r16 = s0.gpr .r7 ∧
      s.gpr .r17 = s0.gpr .r9 ∧ s.gpr .r22 = s0.gpr .r8 ∧ s.gpr .r24 = s0.gpr .r4) ?_ (by decide))
    fun s ⟨⟨m, r31, a14, a15, a16, a17, a22, a24⟩, k⟩ => ?_
  · prun [hs.st (d := 0) (n := 8) (by omega_arith), hs.st (d := 8) (n := 8) (by omega_arith),
      hs.st (d := 16) (n := 8) (by omega_arith), hs.st (d := 24) (n := 8) (by omega_arith),
      hs.st (d := 32) (n := 8) (by omega_arith), hs.st (d := 40) (n := 8) (by omega_arith),
      hs.st (d := 48) (n := 8) (by omega_arith), hs.st (d := 56) (n := 8) (by omega_arith),
      hs.st (d := 64) (n := 8) (by omega_arith), hs.st (d := 72) (n := 8) (by omega_arith),
      hs.st (d := 80) (n := 8) (by omega_arith), hs.st (d := 88) (n := 8) (by omega_arith),
      hs.st (d := 96) (n := 8) (by omega_arith), hs.st (d := 104) (n := 8) (by omega_arith)]
    exact ⟨rfl, BitVec.add_zero _, BitVec.add_zero _, BitVec.add_zero _, BitVec.add_zero _, BitVec.add_zero _,
      BitVec.add_zero _, BitVec.add_zero _⟩
  · have kk : Keep [.r11, .r14, .r15, .r16, .r17, .r22, .r24, .r31] s0 s := (k1.trans k).mono
    have b : Base s0 s := ⟨h, kk.sp, kk.lr, kk.rd, kk.wr, fun x hx => by rw [m]; exact entryMem_frame h x hx,
      fun i hi => by rw [m]; exact entryMem_hdr s0 i hi, r31⟩
    refine argStep b (r := .r18) (by decide) (by decide) (by decide) fun t1 b1 e18 k18 => ?_
    refine argStep b1 (r := .r19) (by decide) (by decide) (by decide) fun t2 b2 e19 k19 => ?_
    refine argStep b2 (r := .r20) (by decide) (by decide) (by decide) fun t3 b3 e20 k20 => ?_
    refine argStep b3 (r := .r21) (by decide) (by decide) (by decide) fun t4 b4 e21 k21 => ?_
    refine argStep b4 (r := .r23) (by decide) (by decide) (by decide) fun t b5 e23 k23 => WP.block_nil ?_
    have K := (((((kk.trans k18).trans k19).trans k20).trans k21).trans k23)
    have K5 := ((((k18.trans k19).trans k20).trans k21).trans k23)
    refine ⟨b5, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, e23, ?_⟩, K.mono⟩
    · rw [K5.gpr _ (by decide)]; exact a14
    · rw [K5.gpr _ (by decide)]; exact a15
    · rw [K5.gpr _ (by decide)]; exact a16
    · rw [K5.gpr _ (by decide)]; exact a17
    · rw [(((k19.trans k20).trans k21).trans k23).gpr _ (by decide)]; exact e18
    · rw [((k20.trans k21).trans k23).gpr _ (by decide)]; exact e19
    · rw [(k21.trans k23).gpr _ (by decide)]; exact e20
    · rw [k23.gpr _ (by decide)]; exact e21
    · rw [K5.gpr _ (by decide)]; exact a22
    · rw [K5.gpr _ (by decide)]; exact a24

end VG.Proof.RsaKeyGen.PPC64LE.Key
