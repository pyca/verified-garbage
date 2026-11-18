module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Env3
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvLoads
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvMid
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyHalf
import VerifiedGarbage.Proof.Rsa.PPC64LE.Seqs
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Env2
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Contract
public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Key
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBase
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs

/-! ### `RsaKeyGen.PPC64LE.Key.Base`, which this module and modules that import it used -/

section

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
  sig_split h
  rename_i hsp hrd hwr nD nP nQ nDp nDq nQi _ nS _ dP dQ dDp dDq dQi _ dS _ pQ pDp pDq pQi _ pS _ qDp qDq qQi _
    qS _ dpDq dpQi _ dpS _ dqQi _ dqS _ _ qiS _ eS sA wN wD wP wQ wDp wDq wQi wE wS h_l1_l2_l8 nl dl ql dpl dql
    qil el1 el8
  have sl := h
  obtain ⟨l1, l2, l8⟩ := h_l1_l2_l8
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

end

end

/-!
# `vg_rsa_keygen_key` on PPC64LE: the working space, the inputs and the constants

`setup_ok`: `w = p_len / 2` and the stride, and every array zeroed.
`loads_ok`: `p`, `q` and `e` read. `consts_ok`: 1, 2, 3, `2^(32 w - 1)`,
`2^(8 p_len) + 1` and `2^33`. `init_ok`: the three, in the environment the
body's phases work in (`KS`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Key

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs half aZero)
open VG.Impl.RsaKeyGen.PPC64LE.Key (setup loads consts nArr aOne aTwo aThree aTop aC aC33 aE aP0 aQ0 aDv)
open VG.Impl.RsaKeyGen.PPC64LE.Key (setDigit)
open VG.Impl.Rsa.PPC64LE.CrtValues (load)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot ranges)
open VG.Proof.Rsa.PPC64LE.CrtValues (past_of_disjoint mv2_ok val32_of_zero ofNat_toNat64 ofNat_stride)

/-- The inputs, from the caller's memory. -/
abbrev pIn (s0 : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r7) (kL s0))
abbrev qIn (s0 : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r9) (kL s0))
abbrev eIn (s0 : State) : Nat :=
  Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 6) (PPC64LE.stackArg s0 7).toNat)

theorem pre_ws {s0 : State} (h : keyP.pre s0) :
    arr (kW s0) nArr ≤ kZ s0 ∧ 16 ≤ kW s0 ∧ kW s0 ≤ 256 ∧ kL s0 = 2 * kW s0 ∧ kL s0 % 4 = 0 := by
  obtain p := kpre h
  have := p.sl; have := p.l1; have := p.l2; have := p.l8
  simp only [arr, S, nArr, VG.Proof.Rsa.KeyWorkspace.hdr, kW] at *
  omega_arith

/-- A step that writes only the arrays and the slots keeps `Base`. -/
theorem Base.of_kk {s0 s t : State} (h : Base s0 s) (k : KK (kB s0) (kW s0) s.mem t.mem) (sp : t.sp = s.sp)
    (lr : t.lr = s.lr) (rd : t.rd = s.rd) (wr : t.wr = s.wr) (r31 : t.gpr .r31 = s.gpr .r31) : Base s0 t := by
  obtain p := kpre h.pre
  have nw := p.wS
  obtain ⟨fits, -, -, -⟩ := pre_ws h.pre
  obtain hjs : ∀ j ∈ allArrs, j < nArr := fun j hj => List.mem_range.mp hj
  obtain hds : ∀ d ∈ allSlots, 112 ≤ d ∧ d + 4 ≤ 160 := by decide
  refine ⟨h.pre, sp.trans h.sp, lr.trans h.lr, rd.trans h.rd, wr.trans h.wr, fun x hx => ?_,
    fun i hi => ?_, r31.trans h.r31⟩
  · rw [← h.frame x hx]
    exact k.out (Z := kZ s0) (fun j hj => Nat.le_trans (VG.Proof.Rsa.KeyWorkspace.arr_end (hjs j hj)) fits)
      (fun d hd => by have := hds d hd; have : 160 ≤ kZ s0 := Nat.le_trans (Nat.le_add_right _ _) fits; omega_arith) hx
  · rw [← h.hdr i hi]
    refine Mem.readW_congr fun b hb => ?_
    rw [off, Offset.add_add]
    refine k _ fun r hr => ?_
    obtain h160 : 160 ≤ kZ s0 := Nat.le_trans (Nat.le_add_right _ _) fits
    rw [ofs, Mem.sub_ofNat_toNat _ (by omega_arith)]
    simp only [ranges, List.mem_append, List.mem_map] at hr
    rcases hr with ⟨j, -, rfl⟩ | ⟨d, hd, rfl⟩
    · left; simp only [arr, VG.Proof.Rsa.KeyWorkspace.hdr]; omega_arith
    · left; have := hds d hd; dsimp only; omega_arith

/-- `Base` through a phase of the body. -/
theorem Base.of_phase {s0 s t : State} (h : Base s0 s) (k : KK (kB s0) (kW s0) s.mem t.mem) {rs : List Reg}
    (kr : Keep rs s t) (hr : .r31 ∉ rs := by decide) : Base s0 t :=
  h.of_kk k kr.sp kr.lr kr.rd kr.wr (kr.gpr _ hr)

/-- A step that writes only bytes from 160 on, within the working space, keeps `Base`. -/
theorem Base.of_outside {s0 s t : State} (h : Base s0 s) {n : Nat}
    (o : Outside (kB s0) 160 n s.mem t.mem) (hn : 160 + n ≤ kZ s0) (sp : t.sp = s.sp) (lr : t.lr = s.lr)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) (r31 : t.gpr .r31 = s.gpr .r31) : Base s0 t := by
  obtain nw := (kpre h.pre).wS
  refine ⟨h.pre, sp.trans h.sp, lr.trans h.lr, rd.trans h.rd, wr.trans h.wr, fun x hx => ?_,
    fun i hi => ?_, r31.trans h.r31⟩
  · rw [← h.frame x hx]; exact o x (Or.inr (by omega_arith))
  · rw [← h.hdr i hi]
    refine Mem.readW_congr fun b hb => ?_
    rw [off, Offset.add_add]
    refine o _ (Or.inl ?_)
    rw [ofs, Mem.sub_ofNat_toNat _ (by omega_arith)]
    omega_arith

theorem ofNat_shr1 (x : BitVec 64) : x >>> 1 = BitVec.ofNat 64 (x.toNat / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega_arith

theorem ofNat_digits60 (w : Nat) (hw : w ≤ 256) :
    (BitVec.ofNat 64 60 * BitVec.ofNat 64 (S w)) >>> 2 = BitVec.ofNat 64 (60 * (w + 2)) := by
  rw [← BitVec.ofNat_mul]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  simp only [S]
  rw [Nat.mod_eq_of_lt (show 60 * (4 * (w + 2)) < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (show 60 * (w + 2) < 2 ^ 64 by omega_arith)]
  omega_arith

theorem zero_bounds {w Z : Nat} (f : arr w nArr ≤ Z) (hw : w ≤ 256) :
    160 + 4 * (nArr * (w + 2)) ≤ Z ∧ 1 ≤ nArr * (w + 2) ∧ nArr * (w + 2) < 2 ^ 32 := by
  simp only [arr, S, nArr, VG.Proof.Rsa.KeyWorkspace.hdr] at f ⊢
  omega_arith

/-- `setup`: `w` and the stride, and every array 0: the environment of zeros. -/
theorem setup_ok {s0 s : State} (h : Base s0 s) (h22 : s.gpr .r22 = s0.gpr .r8) :
    WP isa setup s fun t => Base s0 t ∧ Ws t (kB s0) (kZ s0) (kW s0) nArr ∧
      KS t.mem (kB s0) (kW s0) (fun _ => 0) (fun d => slot t.mem (kB s0) d) ∧
      Keep (.r29 :: .r30 :: opRegs) s t := by
  obtain p := kpre h.pre
  have nw := p.wS
  obtain hm : (⟨kB s0, kZ s0⟩ : Region) ∈ s.wr := by rw [h.wr, p.wr]; simp
  obtain ⟨fits, hw16, hw, hlw, -⟩ := pre_ws h.pre
  obtain hs : Scr s (kB s0) (kZ s0) := Scr.of_mem hm nw
  rw [setup, WP.seq_iff]
  obtain hb : WP isa (.block ([.lsr .d .r29 .r22 1] ++ VG.Impl.Rsa.PPC64LE.Keys.stride ++
      [.li .r8 nArr, .mul .r8 .r8 .r30, .lsr .d .r8 .r8 2])) s fun u =>
        (u.gpr .r29 = BitVec.ofNat 64 (kW s0) ∧ u.gpr .r30 = BitVec.ofNat 64 (S (kW s0)) ∧
          u.gpr .r8 = BitVec.ofNat 64 (nArr * (kW s0 + 2)) ∧ u.mem = s.mem) ∧ Keep [.r8, .r29, .r30] s u := by
    refine WP.keep _ ?_ (by decide)
    prun [VG.Impl.Rsa.PPC64LE.Keys.stride, h22, ofNat_shr1, ofNat_stride, ofNat_digits60 _ hw, nArr]
  refine WP.mono hb fun u ⟨⟨u29, u30, u8, um⟩, ku⟩ => ?_
  obtain hu : Ws u (kB s0) (kZ s0) (kW s0) nArr :=
    ⟨hs.congr ku.wr, fits, by omega_arith, Nat.le_trans hw (by decide), u29, u30, (ku.gpr _ (by decide)).trans h.r31⟩
  obtain ⟨hn, hn1, hn2⟩ := zero_bounds fits hw
  refine WP.mono (zeroArrays_ok hu u8 hn1 hn2 hn)
    fun t ⟨ht, z, out, kt⟩ => ⟨?_, ht, ?_, (ku.trans kt).mono⟩
  · have kk := ku.trans kt
    exact Base.of_outside h (by rw [← um]; exact out) hn kk.sp kk.lr kk.rd kk.wr (kk.gpr _ (by decide))
  · have zz : ∀ j < nArr, ∀ i < kW s0 + 2, w32 t.mem (kB s0) (arr (kW s0) j + 4 * i) = 0 := by
      intro j hj i hi
      obtain hb : j * (kW s0 + 2) + i < nArr * (kW s0 + 2) := by
        have := Nat.mul_le_mul_right (kW s0 + 2) (show j + 1 ≤ nArr by omega_arith)
        rw [Nat.add_mul, Nat.one_mul] at this; omega_arith
      have := z (j * (kW s0 + 2) + i) hb
      rw [show 160 + 4 * (j * (kW s0 + 2) + i) = arr (kW s0) j + 4 * i by
        simp only [arr, S, VG.Proof.Rsa.KeyWorkspace.hdr]; grind] at this
      exact this
    exact ⟨fun j hj => val32_of_zero fun i hi => zz j hj i (by omega_arith), fun _ _ => rfl,
      zz aDv (by decide) _ (by omega_arith)⟩

/-- The bytes of a region apart from the working space are the caller's. -/
theorem Base.bytes {s0 s : State} (h : Base s0 s) {P : Addr} {L : Nat} (hd : (⟨P, L⟩ : Region).Disjoint (rS s0))
    (hw : P.toNat + L ≤ 2 ^ 64) : Spec.Rsa.bytesAt s.mem P L = Spec.Rsa.bytesAt s0.mem P L := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => h.frame _ (past_of_disjoint hd ?_)
  obtain hi' := List.mem_range.mp hi
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

/-- `load j` from a region apart from the working space. -/
theorem ldE {s0 s : State} (h : Base s0 s) (hw : Ws s (kB s0) (kZ s0) (kW s0) nArr) {V F : Nat → Nat}
    (ks : KS s.mem (kB s0) (kW s0) V F) {j : Nat} (hj : j < nArr := by decide) (hjdv : j ≠ aDv := by decide)
    {P : Addr} {L : Nat} (h6 : s.gpr .r6 = P) (h8 : s.gpr .r8 = BitVec.ofNat 64 L) (hL : 1 ≤ L)
    (hLw : L ≤ 4 * kW s0) (hm : (⟨P, L⟩ : Region) ∈ s0.rd ++ s0.wr) (hd : (⟨P, L⟩ : Region).Disjoint (rS s0))
    (hPw : P.toNat + L ≤ 2 ^ 64) (hz : V j = 0) :
    WP isa (load j) s fun t => Base s0 t ∧ Ws t (kB s0) (kZ s0) (kW s0) nArr ∧
      KS t.mem (kB s0) (kW s0) (upd V j (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem P L))) F ∧ Keep opsRegs s t := by
  obtain hc : ∀ i < L, (⟨P, L⟩ : Region).Contains (off P i) 1 := fun i hi =>
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  refine WP.mono (loadE hw ks hj hjdv h6 h8 hL hLw
    (fun i hi => ⟨_, by rw [h.rd, h.wr]; exact hm, hc i hi⟩)
    (fun i hi x hx e => by have := past_of_disjoint hd (hc i hi); rw [e] at this; omega_arith) hz)
    fun t ⟨ht, kt, kk, kr⟩ => ⟨h.of_phase kk kr, ht, ?_, kr⟩
  rw [h.bytes hd hPw] at kt
  exact kt

theorem loads_eq : loads = seqs [.block [.addi .r6 .r16 0, .addi .r8 .r22 0], load aP0,
    .block [.addi .r6 .r17 0, .addi .r8 .r22 0], load aQ0, .block [.addi .r6 .r21 0, .addi .r8 .r23 0],
    load aE] := rfl

/-- `loads`: `p`, `q` and `e` into their arrays. -/
theorem loads_ok {s0 s : State} (h : Base s0 s) (ha : Args s0 s) (hw : Ws s (kB s0) (kZ s0) (kW s0) nArr)
    {V F : Nat → Nat} (ks : KS s.mem (kB s0) (kW s0) V F) (z1 : V aP0 = 0) (z2 : V aQ0 = 0) (z3 : V aE = 0) :
    WP isa loads s fun t => Base s0 t ∧ Ws t (kB s0) (kZ s0) (kW s0) nArr ∧
      (∃ V', KS t.mem (kB s0) (kW s0) V' F ∧ (∀ j, j ≠ aP0 → j ≠ aQ0 → j ≠ aE → V' j = V j) ∧
        V' aP0 = pIn s0 ∧ V' aQ0 = qIn s0 ∧ V' aE = eIn s0) ∧ Keep opsRegs s t := by
  obtain p := kpre h.pre
  obtain ⟨-, hw16, -, hlw, -⟩ := pre_ws h.pre
  have l1 := p.l1
  have el1 := p.el1
  have el8 := p.el8
  have wq := p.wQ
  rw [p.ql] at wq
  rw [loads_eq, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (mv2_ok (s := s) (d₁ := .r6) (d₂ := .r8) (a := .r16) (b := .r22) (by decide) (by decide)
    (by decide) (by decide)) fun u0 ⟨⟨a6, a8, am⟩, ak⟩ => ?_
  rw [ha.r16] at a6
  rw [ha.r22] at a8
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ldE (h.of_regs ak am) (hw.of_keep ak) (am ▸ ks) (j := aP0) (h6 := a6)
    (h8 := by rw [a8]; exact ofNat_toNat64 _) (L := kL s0) (hL := by omega_arith) (hLw := by omega_arith)
    (hm := by rw [p.rd, p.wr]; simp) (hd := p.pS) (hPw := p.wP) (hz := z1)) fun t1 ⟨b1, w1, k1, r1⟩ => ?_
  obtain ⟨V1, k1, e1, o1⟩ := k1.vx
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (mv2_ok (s := t1) (d₁ := .r6) (d₂ := .r8) (a := .r17) (b := .r22) (by decide) (by decide)
    (by decide) (by decide)) fun u2 ⟨⟨c6, c8, m2⟩, k2⟩ => ?_
  obtain a1 := ha.of_keep (ak.trans r1)
  rw [a1.r17] at c6
  rw [a1.r22] at c8
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ldE (b1.of_regs k2 m2) (w1.of_keep k2) (m2 ▸ k1) (j := aQ0) (h6 := c6)
    (h8 := by rw [c8]; exact ofNat_toNat64 _) (L := kL s0) (hL := by omega_arith) (hLw := by omega_arith)
    (hm := by rw [p.rd, p.wr, ← p.ql]; simp) (hd := by rw [← p.ql]; exact p.qS) (hPw := by rw [← p.ql]; exact p.wQ)
    (hz := by rw [o1 _ (by decide), z2])) fun t3 ⟨b3, w3, k3, r3⟩ => ?_
  obtain ⟨V3, k3, e3, o3⟩ := k3.vx
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (mv2_ok (s := t3) (d₁ := .r6) (d₂ := .r8) (a := .r21) (b := .r23) (by decide) (by decide)
    (by decide) (by decide)) fun u4 ⟨⟨c6', c8', m4⟩, k4⟩ => ?_
  obtain a3 := a1.of_keep (k2.trans r3)
  rw [a3.r21] at c6'
  rw [a3.r23] at c8'
  rw [show seqs [load aE] = load aE from rfl]
  refine WP.mono (ldE (b3.of_regs k4 m4) (w3.of_keep k4) (m4 ▸ k3) (j := aE) (h6 := c6')
    (h8 := by rw [c8']; exact ofNat_toNat64 _) (hL := el1) (hLw := by omega_arith)
    (hm := by rw [p.rd, p.wr]; simp) (hd := p.eS) (hPw := p.wE)
    (hz := by rw [o3 _ (by decide), o1 _ (by decide), z3])) fun t ⟨b5, w5, k5, r5⟩ => ?_
  obtain ⟨V5, k5, e5, o5⟩ := k5.vx
  refine ⟨b5, w5, ⟨V5, k5, fun j a b c => by rw [o5 j c, o3 j b, o1 j a], by rw [o5 _ (by decide),
    o3 _ (by decide), e1], by rw [o5 _ (by decide), e3], e5⟩,
    (((((ak.trans r1).trans k2).trans r3).trans k4).trans r5).mono⟩

/-- One instruction that writes a register. -/
theorem reg_step {u : State} {i : Instr} {r : Reg} {v : BitVec 64} (he : exec i u = some (u.write r v))
    {rest : List Instr} {Q : State → Prop} (k : WP isa (.block rest) (u.write r v) Q) :
    WP isa (.block (i :: rest)) u Q := by
  rw [show i :: rest = [i] ++ rest from rfl, WP.block_append_iff]
  exact WP.of_runBlock ⟨u.write r v, by simp only [runBlock_cons, runStep_some, he, runBlock_nil], k⟩

theorem consts_eq : seqs consts = .seq (.block (.li .r6 0 :: (setDigit aOne 1 ++ (setDigit aTwo 2 ++
    (setDigit aThree 3 ++ (setDigit aC 1 ++ (.addi .r6 .r22 0 :: (setDigit aC 1 ++ (.li .r6 4 ::
      (setDigit aC33 2 ++ ([.li .r9 1] : List Instr))))))))))) (half aTop) := rfl

/-- The six constants, into zero arrays. -/
theorem consts_ok {s0 s : State} (h : Base s0 s) (ha : Args s0 s) (hw : Ws s (kB s0) (kZ s0) (kW s0) nArr)
    {V F : Nat → Nat} (ks : KS s.mem (kB s0) (kW s0) V F) (z1 : V aOne = 0) (z2 : V aTwo = 0)
    (z3 : V aThree = 0) (z4 : V aC = 0) (z5 : V aC33 = 0) (z6 : V aTop = 0) :
    WP isa (seqs consts) s fun t => Base s0 t ∧ Ws t (kB s0) (kZ s0) (kW s0) nArr ∧
      (∃ V', KS t.mem (kB s0) (kW s0) V' F ∧
        (∀ j, j ≠ aOne → j ≠ aTwo → j ≠ aThree → j ≠ aC → j ≠ aC33 → j ≠ aTop → V' j = V j) ∧
        V' aOne = 1 ∧ V' aTwo = 2 ∧ V' aThree = 3 ∧ V' aC = 2 ^ (8 * kL s0) + 1 ∧ V' aC33 = 2 ^ 33 ∧
        V' aTop = 2 ^ (32 * kW s0 - 1)) ∧ Keep opsRegs s t := by
  obtain ⟨-, hw16, -, hlw, h4⟩ := pre_ws h.pre
  obtain p := kpre h.pre
  have l1 := p.l1
  rw [consts_eq, WP.seq_iff]
  refine reg_step (exec_li (show 0 < 2 ^ 15 by decide)) ?_
  obtain g0 : Keep [.r6] s (s.write .r6 (BitVec.ofNat 64 0)) := Keep.write _ _ _
  obtain w0 := hw.of_keep g0
  obtain q6 : (s.write .r6 (BitVec.ofNat 64 0)).gpr .r6 = BitVec.ofNat 64 (4 * 0) := by
    simp [State.write]
  refine setDigitE w0 ks (j := aOne) (x := 1) (k := 0) (hx := by decide) (hk := by omega_arith) (h6 := q6)
    (hv := by rw [z1]; decide)
    (kk := fun t1 h1 k1 f1 r1 => ?_)
  obtain ⟨V1, k1, e1, o1⟩ := k1.vx
  obtain q6 : t1.gpr .r6 = BitVec.ofNat 64 (4 * 0) := by rw [r1.gpr _ (by decide)]; exact q6
  refine setDigitE h1 k1 (j := aTwo) (x := 2) (k := 0) (hx := by decide) (hk := by omega_arith) (h6 := q6)
    (hv := by rw [o1 _ (by decide), z2]; decide) (kk := fun t2 h2 k2 f2 r2 => ?_)
  obtain ⟨V2, k2, e2, o2⟩ := k2.vx
  obtain q6 : t2.gpr .r6 = BitVec.ofNat 64 (4 * 0) := by rw [r2.gpr _ (by decide)]; exact q6
  refine setDigitE h2 k2 (j := aThree) (x := 3) (k := 0) (hx := by decide) (hk := by omega_arith) (h6 := q6)
    (hv := by rw [o2 _ (by decide), o1 _ (by decide), z3]; decide) (kk := fun t3 h3 k3 f3 r3 => ?_)
  obtain ⟨V3, k3, e3, o3⟩ := k3.vx
  obtain q6 : t3.gpr .r6 = BitVec.ofNat 64 (4 * 0) := by rw [r3.gpr _ (by decide)]; exact q6
  refine setDigitE h3 k3 (j := aC) (x := 1) (k := 0) (hx := by decide) (hk := by omega_arith) (h6 := q6)
    (hv := by rw [o3 _ (by decide), o2 _ (by decide), o1 _ (by decide), z4]; decide) (kk := fun t4 h4' k4 f4 r4 => ?_)
  obtain ⟨V4, k4, e4, o4⟩ := k4.vx
  obtain a4 := ha.of_keep ((((g0.trans r1).trans r2).trans r3).trans r4)
  refine reg_step (exec_addi (show Reg.r22 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide)) ?_
  obtain g5 : Keep [.r6] t4 (t4.write .r6 (t4.gpr .r22 + BitVec.ofNat 64 0)) := Keep.write _ _ _
  obtain q6 : (t4.write .r6 (t4.gpr .r22 + BitVec.ofNat 64 0)).gpr .r6 = BitVec.ofNat 64 (4 * (kL s0 / 4)) := by
    simp only [State.write, ↓reduceIte, BitVec.add_zero, a4.r22]
    rw [show 4 * (kL s0 / 4) = kL s0 by omega_arith]; exact ofNat_toNat64 _
  obtain v4 : V4 aC = 1 := by rw [e4, o3 _ (by decide), o2 _ (by decide), o1 _ (by decide), z4]
  obtain hlt : (1 : Nat) < 2 ^ (32 * (kL s0 / 4)) := Nat.one_lt_two_pow (by omega_arith)
  refine setDigitE (h4'.of_keep g5) k4 (j := aC) (x := 1) (k := kL s0 / 4) (hx := by decide) (hk := by omega_arith) (h6 := q6)
    (hv := by rw [v4]; exact hlt) (kk := fun t5 h5 k5 f5 r5 => ?_)
  obtain ⟨V5, k5, e5, o5⟩ := k5.vx
  refine reg_step (exec_li (show 4 < 2 ^ 15 by decide)) ?_
  obtain g6 : Keep [.r6] t5 (t5.write .r6 (BitVec.ofNat 64 4)) := Keep.write _ _ _
  obtain q6 : (t5.write .r6 (BitVec.ofNat 64 4)).gpr .r6 = BitVec.ofNat 64 (4 * 1) := by simp [State.write]
  refine setDigitE (h5.of_keep g6) k5 (j := aC33) (x := 2) (k := 1) (hx := by decide) (hk := by omega_arith) (h6 := q6)
    (hv := by rw [o5 _ (by decide), o4 _ (by decide), o3 _ (by decide), o2 _ (by decide), o1 _ (by decide), z5]; decide)
    (kk := fun t6 h6 k6 f6 r6 => ?_)
  obtain ⟨V6, k6, e6, o6⟩ := k6.vx
  refine reg_step (exec_li (show 1 < 2 ^ 15 by decide)) (WP.block_nil ?_)
  obtain g7 : Keep [.r9] t6 (t6.write .r9 (BitVec.ofNat 64 1)) := Keep.write _ _ _
  obtain K7 := (((((((((g0.trans r1).trans r2).trans r3).trans r4).trans g5).trans r5).trans g6).trans
    r6).trans g7)
  obtain f7 : KK (kB s0) (kW s0) s.mem (t6.write .r9 (BitVec.ofNat 64 1)).mem :=
    ((((f1.trans f2).trans f3).trans f4).trans f5).trans f6
  obtain b7 : Base s0 (t6.write .r9 (BitVec.ofNat 64 1)) := h.of_phase f7 K7
  refine WP.mono (halfE (h6.of_keep g7) k6 (j := aTop) (c := 1) (h9 := by simp [State.write]) (hc := by decide))
    fun t ⟨ht, kt, ft, rt⟩ => ⟨b7.of_phase ft rt, ht, ?_, (K7.trans rt).mono⟩
  obtain ⟨V7, kt, e7, o7⟩ := kt.vx
  obtain c : ∀ j, j ≠ aOne → j ≠ aTwo → j ≠ aThree → j ≠ aC → j ≠ aC33 → V6 j = V j := fun j a b c d e => by
    rw [o6 j e, o5 j d, o4 j d, o3 j c, o2 j b, o1 j a]
  refine ⟨V7, kt, fun j a b c' d e f => by rw [o7 j f, c j a b c' d e], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [o7 _ (by decide), o6 _ (by decide), o5 _ (by decide), o4 _ (by decide), o3 _ (by decide),
      o2 _ (by decide), e1, z1]
  · rw [o7 _ (by decide), o6 _ (by decide), o5 _ (by decide), o4 _ (by decide), o3 _ (by decide), e2, o1 _ (by decide), z2]
  · rw [o7 _ (by decide), o6 _ (by decide), o5 _ (by decide), o4 _ (by decide), e3, o2 _ (by decide), o1 _ (by decide), z3]
  · rw [o7 _ (by decide), o6 _ (by decide), e5, v4, Nat.mul_one,
      show 32 * (kL s0 / 4) = 8 * kL s0 by omega_arith, Nat.add_comm]
  · rw [o7 _ (by decide), e6, o5 _ (by decide), o4 _ (by decide), o3 _ (by decide), o2 _ (by decide),
      o1 _ (by decide), z5]
  · rw [e7, c _ (by decide) (by decide) (by decide) (by decide) (by decide), z6, Nat.zero_add, Nat.mul_one]
    have : 32 * kW s0 = (32 * kW s0 - 1) + 1 := by omega_arith
    rw [this, Nat.pow_succ, Nat.mul_div_cancel _ (by decide), Nat.add_sub_cancel]

end VG.Proof.RsaKeyGen.PPC64LE.Key
