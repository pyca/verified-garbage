module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.CvContract
public import VerifiedGarbage.Impl.Rsa.PPC64LE.CrtValues
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs

/-!
# `vg_rsa_crt_values` on PPC64LE: what every stage keeps, and the entry

`Base s0 s`: from the initial state `s0` (`cvP.pre`), the stack pointer, the
link register and the regions are `s0`'s, memory outside the working space
(`cvZ s0` bytes at `cvB s0`, the scratch buffer) is `s0`'s, the working
space's base is in `r31`, and the header's first fourteen words hold the
saved `r14`–`r24` and `r29`–`r31` (`hdrVal`). `Args s0 s`: the pointers and
lengths in `r14`–`r24`. `entry_ok`: the entry establishes both.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.CrtValues

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Rsa.PPC64LE.CrtValues (entry stackArg stackOff)

/-- The working space's base, size, `n_len` and `w = ⌈n_len / 4⌉`. -/
abbrev cvB (s0 : State) : Addr := PPC64LE.stackArg s0 6
abbrev cvZ (s0 : State) : Nat := (PPC64LE.stackArg s0 7).toNat * 8
abbrev cvK (s0 : State) : Nat := (s0.gpr .r10).toNat
abbrev cvW (s0 : State) : Nat := (cvK s0 + 3) / 4

/-- The register saved in the header word `i` (bytes `8 i`). -/
def savedReg : Nat → Reg
  | 0 => .r14 | 1 => .r15 | 2 => .r16 | 3 => .r17 | 4 => .r18 | 5 => .r19 | 6 => .r20 | 7 => .r21
  | 8 => .r22 | 9 => .r23 | 10 => .r24 | 11 => .r29 | 12 => .r30 | _ => .r31

/-- The header word `i` on entry's completion. -/
abbrev hdrVal (s0 : State) (i : Nat) : BitVec 64 := s0.gpr (savedReg i)

/-- The pointers and lengths, in `r14`–`r24`. -/
structure Args (s0 s : State) : Prop where
  r14 : s.gpr .r14 = s0.gpr .r3
  r15 : s.gpr .r15 = s0.gpr .r5
  r16 : s.gpr .r16 = s0.gpr .r7
  r17 : s.gpr .r17 = s0.gpr .r9
  r18 : s.gpr .r18 = s0.gpr .r10
  r19 : s.gpr .r19 = PPC64LE.stackArg s0 0
  r20 : s.gpr .r20 = PPC64LE.stackArg s0 1
  r21 : s.gpr .r21 = PPC64LE.stackArg s0 2
  r22 : s.gpr .r22 = PPC64LE.stackArg s0 3
  r23 : s.gpr .r23 = PPC64LE.stackArg s0 4
  r24 : s.gpr .r24 = PPC64LE.stackArg s0 5

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
  pre : cvP.pre s0
  sp : s.sp = s0.sp
  lr : s.lr = s0.lr
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  frame : ∀ x, cvZ s0 ≤ ofs (cvB s0) x → s.mem x = s0.mem x
  hdr : ∀ i < 14, s.mem.readW (off (cvB s0) (8 * i)) 64 = hdrVal s0 i
  r31 : s.gpr .r31 = cvB s0

/-! ## Facts of the precondition -/

theorem pre_scr {s0 : State} (h : cvP.pre s0) :
    (⟨cvB s0, cvZ s0⟩ : Region) ∈ s0.wr ∧ (cvB s0).toNat + cvZ s0 ≤ 2 ^ 64 ∧
      8 * (16 * cvK s0 + 32) ≤ cvZ s0 ∧ 64 ≤ cvK s0 ∧ cvK s0 ≤ 1024 := by
  obtain ⟨-, -, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, nwS, ⟨hk, hk'⟩, -, -, -, -, -, -, -, -, -, hsl⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  exact ⟨by rw [hwr]; simp, nwS, by simp only [cvZ, cvK]; omega, hk, hk'⟩

theorem pre_args {s0 : State} (h : cvP.pre s0) :
    (⟨stackArgAddr s0 0, 64⟩ : Region) ∈ s0.rd ∧ s0.sp.toNat + 32 + 8 * 16 ≤ 2 ^ 64 := by
  obtain ⟨hsp, hrd, -⟩ := h
  exact ⟨by rw [hrd]; simp, hsp⟩

/-- A stack argument's address. -/
theorem stackArg_addr (s : State) (i : Nat) : s.sp + BitVec.ofNat 64 (stackOff i) = stackArgAddr s i := by
  simp only [stackOff, stackArgAddr]
  congr 2
  omega

/-- `addSp`. -/
theorem exec_addSp {s : State} {d : Reg} {imm : Nat} (h : imm < 2 ^ 15) :
    exec (.addSp d imm) s = some (s.write d (s.sp + BitVec.ofNat 64 imm)) := by
  simp only [exec, h, ↓reduceIte]

/-- The stack argument `i < 8` is readable. -/
theorem arg_rd {s0 s : State} (h : cvP.pre s0) (hrd : s.rd = s0.rd) (hsp : s.sp = s0.sp) {i : Nat}
    (hi : i < 8) : InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8 := by
  obtain ⟨hm, hs⟩ := pre_args h
  refine ⟨_, List.mem_append_left _ (hrd ▸ hm), ?_⟩
  simp only [stackArgAddr, hsp]
  rw [show s0.sp + BitVec.ofNat 64 (32 + 8 * (8 + i)) = stackArgAddr s0 0 + BitVec.ofNat 64 (8 * i) by
    rw [stackArgAddr, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega]
  exact Offset.contains_base _ (by omega) (by omega)

/-- `stackArg r i`: the stack argument `i` into `r`. -/
theorem stackArg_ok {s0 s : State} (h : cvP.pre s0) (hrd : s.rd = s0.rd) (hsp : s.sp = s0.sp)
    {r : Reg} (hr : r ≠ .r0) {i : Nat} (hi : i < 8) {rest : List Instr} {Q : State → Prop}
    (k : WP isa (.block rest) (s.write r (PPC64LE.stackArg s i)) Q) :
    WP isa (.block (stackArg r i ++ rest)) s Q := by
  have rd := arg_rd h hrd hsp hi
  have ho : stackOff i < 2 ^ 15 := by simp only [stackOff]; omega
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

/-- A byte of a region apart from the working space is past its end. -/
theorem past_of_disjoint {B : Addr} {Z : Nat} {r : Region} (hd : r.Disjoint ⟨B, Z⟩) {a : Addr}
    (ha : r.Contains a 1) : Z ≤ ofs B a := by
  have := hd a ha
  simp only [Region.Contains] at this
  simp only [ofs]; omega

/-- The stack arguments are `s0`'s. -/
theorem Base.stackArg {s0 s : State} (h : Base s0 s) {i : Nat} (hi : i < 8) :
    PPC64LE.stackArg s i = PPC64LE.stackArg s0 i := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hsa, -⟩ := h.pre
  obtain ⟨-, hs⟩ := pre_args h.pre
  simp only [PPC64LE.stackArg, stackArgAddr, h.sp]
  refine Mem.readW_congr fun b hb => h.frame _ (past_of_disjoint hsa.symm ?_)
  rw [show s0.sp + BitVec.ofNat 64 (32 + 8 * (8 + i)) + BitVec.ofNat 64 b =
    stackArgAddr s0 0 + BitVec.ofNat 64 (8 * i + b) by
      rw [stackArgAddr, BitVec.add_assoc, BitVec.add_assoc, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
      congr 2; omega]
  exact Offset.contains_base _ (by omega) (by omega)

/-- A step that keeps memory and `r31` keeps `Base`. -/
theorem Base.of_regs {s0 s t : State} (h : Base s0 s) {rs : List Reg} (k : Keep rs s t) (hm : t.mem = s.mem)
    (hr : .r31 ∉ rs := by decide) : Base s0 t :=
  ⟨h.pre, k.sp.trans h.sp, k.lr.trans h.lr, k.rd.trans h.rd, k.wr.trans h.wr,
    fun x hx => by rw [hm]; exact h.frame x hx, fun i hi => by rw [hm]; exact h.hdr i hi,
    (k.gpr _ hr).trans h.r31⟩

/-- `stackArg r i`, from a state with `Base`. -/
theorem argStep {s0 s : State} (h : Base s0 s) {r : Reg} (hr : r ≠ .r0) (hr31 : .r31 ∉ [r]) {i : Nat}
    (hi : i < 8) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Base s0 t → t.gpr r = PPC64LE.stackArg s0 i → Keep [r] s t → WP isa (.block rest) t Q) :
    WP isa (.block (stackArg r i ++ rest)) s Q :=
  stackArg_ok h.pre h.rd h.sp hr hi (k _ (h.of_regs (Keep.write _ _ _) rfl hr31)
    (by simp only [State.write, ↓reduceIte]; exact h.stackArg hi) (Keep.write _ _ _))

/-! ## The entry -/

/-- The header after the entry's stores. -/
def entryMem (s0 : State) : Mem :=
  (((((((((((((s0.mem.writeW (off (cvB s0) 0) (s0.gpr .r14)).writeW (off (cvB s0) 8) (s0.gpr .r15)).writeW
    (off (cvB s0) 16) (s0.gpr .r16)).writeW (off (cvB s0) 24) (s0.gpr .r17)).writeW (off (cvB s0) 32)
      (s0.gpr .r18)).writeW (off (cvB s0) 40) (s0.gpr .r19)).writeW (off (cvB s0) 48) (s0.gpr .r20)).writeW
        (off (cvB s0) 56) (s0.gpr .r21)).writeW (off (cvB s0) 64) (s0.gpr .r22)).writeW (off (cvB s0) 72)
          (s0.gpr .r23)).writeW (off (cvB s0) 80) (s0.gpr .r24)).writeW (off (cvB s0) 88) (s0.gpr .r29)).writeW
            (off (cvB s0) 96) (s0.gpr .r30)).writeW (off (cvB s0) 104) (s0.gpr .r31)

theorem entryMem_frame {s0 : State} (h : cvP.pre s0) :
    ∀ x, cvZ s0 ≤ ofs (cvB s0) x → entryMem s0 x = s0.mem x := by
  obtain ⟨-, nw, hz, -, -⟩ := pre_scr h
  intro x hx
  have o : ∀ (m : Mem) (d : Nat) (v : BitVec 64), d + 8 ≤ 112 → (m.writeW (off (cvB s0) d) v) x = m x :=
    fun m d v hd => writeW_outside m (cvB s0) (d := d) v (by omega) x (Or.inr (by omega))
  simp only [entryMem]
  rw [o _ 104 _ (by decide), o _ 96 _ (by decide), o _ 88 _ (by decide), o _ 80 _ (by decide),
    o _ 72 _ (by decide), o _ 64 _ (by decide), o _ 56 _ (by decide), o _ 48 _ (by decide),
    o _ 40 _ (by decide), o _ 32 _ (by decide), o _ 24 _ (by decide), o _ 16 _ (by decide),
    o _ 8 _ (by decide), o _ 0 _ (by decide)]

/-- A word read through a write of another, at offsets of `B`. -/
theorem readW_sep (m : Mem) (B : Addr) {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (off B e) v).readW (off B d) 64 = m.readW (off B d) 64 :=
  Mem.readW_writeW_sep (Offset.sep B h hd he) (by decide)

theorem entryMem_hdr (s0 : State) :
    ∀ i < 14, (entryMem s0).readW (off (cvB s0) (8 * i)) 64 = hdrVal s0 i := by
  intro i hi
  simp only [entryMem]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11 ∨ i = 12 ∨ i = 13 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := decide) only [hdrVal, savedReg, Nat.mul_zero, Nat.reduceMul, readW_sep, Mem.readW_writeW_self64]

theorem entry_eq : entry = stackArg .r11 6 ++ (([.store .d .r14 .r11 0, .store .d .r15 .r11 8,
    .store .d .r16 .r11 16, .store .d .r17 .r11 24, .store .d .r18 .r11 32, .store .d .r19 .r11 40,
    .store .d .r20 .r11 48, .store .d .r21 .r11 56, .store .d .r22 .r11 64, .store .d .r23 .r11 72,
    .store .d .r24 .r11 80, .store .d .r29 .r11 88, .store .d .r30 .r11 96, .store .d .r31 .r11 104,
    .addi .r31 .r11 0, .addi .r14 .r3 0, .addi .r15 .r5 0, .addi .r16 .r7 0, .addi .r17 .r9 0,
    .addi .r18 .r10 0] : List Instr) ++ (stackArg .r19 0 ++ (stackArg .r20 1 ++ (stackArg .r21 2 ++ (stackArg .r22 3 ++
      (stackArg .r23 4 ++ (stackArg .r24 5 ++ ([] : List Instr)))))))) := rfl

/-- The registers the entry changes. -/
abbrev entryRegs : List Reg := [.r11, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r31]

theorem entry_ok {s0 : State} (h : cvP.pre s0) :
    WP isa (.block entry) s0 fun s => Base s0 s ∧ Args s0 s ∧ Keep entryRegs s0 s := by
  obtain ⟨hm, nw, hz, hk, hk'⟩ := pre_scr h
  have hs : Scr s0 (cvB s0) (cvZ s0) := Scr.of_mem hm nw
  rw [entry_eq]
  refine stackArg_ok h rfl rfl (r := .r11) (by decide) (by decide) ?_
  have k1 : Keep [.r11] s0 (s0.write .r11 (PPC64LE.stackArg s0 6)) := Keep.write _ _ _
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r14, .r15, .r16, .r17, .r18, .r31] (Q := fun s => s.mem = entryMem s0 ∧
      s.gpr .r31 = cvB s0 ∧ s.gpr .r14 = s0.gpr .r3 ∧ s.gpr .r15 = s0.gpr .r5 ∧ s.gpr .r16 = s0.gpr .r7 ∧
      s.gpr .r17 = s0.gpr .r9 ∧ s.gpr .r18 = s0.gpr .r10) ?_ (by decide))
    fun s ⟨⟨m, r31, a14, a15, a16, a17, a18⟩, k⟩ => ?_
  · prun [hs.st (d := 0) (n := 8) (by omega), hs.st (d := 8) (n := 8) (by omega),
      hs.st (d := 16) (n := 8) (by omega), hs.st (d := 24) (n := 8) (by omega),
      hs.st (d := 32) (n := 8) (by omega), hs.st (d := 40) (n := 8) (by omega),
      hs.st (d := 48) (n := 8) (by omega), hs.st (d := 56) (n := 8) (by omega),
      hs.st (d := 64) (n := 8) (by omega), hs.st (d := 72) (n := 8) (by omega),
      hs.st (d := 80) (n := 8) (by omega), hs.st (d := 88) (n := 8) (by omega),
      hs.st (d := 96) (n := 8) (by omega), hs.st (d := 104) (n := 8) (by omega)]
    exact ⟨rfl, BitVec.add_zero _, BitVec.add_zero _, BitVec.add_zero _, BitVec.add_zero _, BitVec.add_zero _,
      BitVec.add_zero _⟩
  · have kk : Keep [.r11, .r14, .r15, .r16, .r17, .r18, .r31] s0 s := (k1.trans k).mono
    have b : Base s0 s := ⟨h, kk.sp, kk.lr, kk.rd, kk.wr, fun x hx => by rw [m]; exact entryMem_frame h x hx,
      fun i hi => by rw [m]; exact entryMem_hdr s0 i hi, r31⟩
    refine argStep b (r := .r19) (by decide) (by decide) (by decide) fun t1 b1 e19 k19 => ?_
    refine argStep b1 (r := .r20) (by decide) (by decide) (by decide) fun t2 b2 e20 k20 => ?_
    refine argStep b2 (r := .r21) (by decide) (by decide) (by decide) fun t3 b3 e21 k21 => ?_
    refine argStep b3 (r := .r22) (by decide) (by decide) (by decide) fun t4 b4 e22 k22 => ?_
    refine argStep b4 (r := .r23) (by decide) (by decide) (by decide) fun t5 b5 e23 k23 => ?_
    refine argStep b5 (r := .r24) (by decide) (by decide) (by decide) fun t b6 e24 k24 => WP.block_nil ?_
    have K := ((((((kk.trans k19).trans k20).trans k21).trans k22).trans k23).trans k24)
    have K6 := (((((k19.trans k20).trans k21).trans k22).trans k23).trans k24)
    refine ⟨b6, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, e24⟩, K.mono⟩
    · rw [K6.gpr _ (by decide)]; exact a14
    · rw [K6.gpr _ (by decide)]; exact a15
    · rw [K6.gpr _ (by decide)]; exact a16
    · rw [K6.gpr _ (by decide)]; exact a17
    · rw [K6.gpr _ (by decide)]; exact a18
    · rw [((((k20.trans k21).trans k22).trans k23).trans k24).gpr _ (by decide)]; exact e19
    · rw [(((k21.trans k22).trans k23).trans k24).gpr _ (by decide)]; exact e20
    · rw [((k22.trans k23).trans k24).gpr _ (by decide)]; exact e21
    · rw [(k23.trans k24).gpr _ (by decide)]; exact e22
    · rw [k24.gpr _ (by decide)]; exact e23

end VG.Proof.Rsa.PPC64LE.CrtValues
