module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.KeyCheck
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBase

/-!
# The checks of an RSA key on PPC64LE: what every stage keeps

`KPre s0 B Z K oS`: what the proofs use of either function's precondition:
the working space (`Z` bytes at `B`, the stack argument `oS`), writable and
apart from the stack arguments (`na` of them, readable), and `n_len = K` in
`r4`. `KBase B Z s0 s`: from the initial state `s0`, the stack pointer, the
link register and the regions are `s0`'s, memory outside the working space
is `s0`'s, the working space's base is in `r31`, and the header's first
fifteen words hold the saved registers (`kSaved`). `save_ok`: the entry's
first block establishes it; `restore_ok`: the exit restores the registers.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.KeyCheck

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Rsa.PPC64LE.KeyCheck (save restore)

/-- What the proofs use of the precondition. -/
structure KPre (s0 : State) (B : Addr) (Z K oS na : Nat) : Prop where
  wr : (⟨B, Z⟩ : Region) ∈ s0.wr
  nowrap : B.toNat + Z ≤ 2 ^ 64
  zk : 8 * (16 * K + 32) ≤ Z
  k64 : 64 ≤ K
  k1024 : K ≤ 1024
  sp : s0.sp.toNat + 32 + 8 * (8 + na) ≤ 2 ^ 64
  args : (⟨stackArgAddr s0 0, 8 * na⟩ : Region) ∈ s0.rd
  disj : (⟨B, Z⟩ : Region).Disjoint ⟨stackArgAddr s0 0, 8 * na⟩
  base : PPC64LE.stackArg s0 oS = B
  hoS : oS < na
  r4 : (s0.gpr .r4).toNat = K

/-- The register saved in the header word `i`. -/
def kSaved : Nat → Reg
  | 0 => .r14 | 1 => .r15 | 2 => .r16 | 3 => .r17 | 4 => .r18 | 5 => .r19 | 6 => .r20 | 7 => .r21
  | 8 => .r22 | 9 => .r23 | 10 => .r24 | 11 => .r26 | 12 => .r29 | 13 => .r30 | _ => .r31

structure KBase (B : Addr) (Z : Nat) (s0 s : State) : Prop where
  sp : s.sp = s0.sp
  lr : s.lr = s0.lr
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  frame : ∀ x, Z ≤ ofs B x → s.mem x = s0.mem x
  hdr : ∀ i < 15, s.mem.readW (off B (8 * i)) 64 = s0.gpr (kSaved i)
  r31 : s.gpr .r31 = B

theorem KBase.of_regs {B : Addr} {Z : Nat} {s0 s t : State} (h : KBase B Z s0 s) {rs : List Reg}
    (k : Keep rs s t) (hm : t.mem = s.mem) (hr : .r31 ∉ rs := by decide) : KBase B Z s0 t :=
  ⟨k.sp.trans h.sp, k.lr.trans h.lr, k.rd.trans h.rd, k.wr.trans h.wr,
    fun x hx => by rw [hm]; exact h.frame x hx, fun i hi => by rw [hm]; exact h.hdr i hi,
    (k.gpr _ hr).trans h.r31⟩

/-- A step that writes only arrays and slots at 120 or after keeps `KBase`. -/
theorem KBase.of_keep {B : Addr} {Z : Nat} {s0 s t : State} (h : KBase B Z s0 s) {w : Nat}
    {js ds : List Nat} (k : KeyWorkspace.Keep B w js ds s.mem t.mem) (hnw : B.toNat + Z ≤ 2 ^ 64)
    (hjs : ∀ j ∈ js, KeyWorkspace.arr w j + KeyWorkspace.S w ≤ Z)
    (hds : ∀ d ∈ ds, 120 ≤ d ∧ d + 4 ≤ 160) (h160 : 160 ≤ Z) {rs : List Reg} (kr : Keep rs s t)
    (hr : .r31 ∉ rs := by decide) : KBase B Z s0 t := by
  refine ⟨kr.sp.trans h.sp, kr.lr.trans h.lr, kr.rd.trans h.rd, kr.wr.trans h.wr, fun x hx => ?_,
    fun i hi => ?_, (kr.gpr _ hr).trans h.r31⟩
  · rw [← h.frame x hx]
    exact k.out (Z := Z) hjs (fun d hd => by have := hds d hd; omega_arith) hx
  · rw [← h.hdr i hi]
    refine Mem.readW_congr fun b hb => ?_
    rw [off, Offset.add_add]
    refine k _ fun r hr => ?_
    rw [ofs, Mem.sub_ofNat_toNat _ (by omega_arith)]
    simp only [KeyWorkspace.ranges, List.mem_append, List.mem_map] at hr
    rcases hr with ⟨j, -, rfl⟩ | ⟨d, hd, rfl⟩
    · left; simp only [KeyWorkspace.arr, KeyWorkspace.hdr]; omega_arith
    · left; have := hds d hd; dsimp only; omega_arith

/-- A step that writes only bytes from 160 on, within the working space, keeps `KBase`. -/
theorem KBase.of_outside {B : Addr} {Z : Nat} {s0 s t : State} (h : KBase B Z s0 s) {n : Nat}
    (o : Outside B 160 n s.mem t.mem) (hn : 160 + n ≤ Z) {rs : List Reg}
    (kr : Keep rs s t) (hr : .r31 ∉ rs := by decide) : KBase B Z s0 t := by
  refine ⟨kr.sp.trans h.sp, kr.lr.trans h.lr, kr.rd.trans h.rd, kr.wr.trans h.wr, fun x hx => ?_,
    fun i hi => ?_, (kr.gpr _ hr).trans h.r31⟩
  · rw [← h.frame x hx]; exact o x (Or.inr (by omega_arith))
  · rw [← h.hdr i hi]
    refine Mem.readW_congr fun b hb => ?_
    rw [off, Offset.add_add]
    refine o _ (Or.inl ?_)
    rw [ofs, Mem.sub_ofNat_toNat _ (by omega_arith)]
    omega_arith

/-- The stack arguments are `s0`'s. -/
theorem KBase.stackArg {B : Addr} {Z K oS na : Nat} {s0 s : State} (h : KBase B Z s0 s)
    (hp : KPre s0 B Z K oS na) {i : Nat} (hi : i < na) :
    PPC64LE.stackArg s i = PPC64LE.stackArg s0 i := by
  have hs := hp.sp
  simp only [PPC64LE.stackArg, stackArgAddr, h.sp]
  refine Mem.readW_congr fun b hb => h.frame _ (CrtValues.past_of_disjoint hp.disj.symm ?_)
  rw [show s0.sp + BitVec.ofNat 64 (32 + 8 * (8 + i)) + BitVec.ofNat 64 b =
    stackArgAddr s0 0 + BitVec.ofNat 64 (8 * i + b) by
      rw [stackArgAddr, BitVec.add_assoc, BitVec.add_assoc, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
      congr 2; omega_arith]
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

/-- The stack argument `i` is readable. -/
theorem KPre.arg_rd {s0 s : State} {B : Addr} {Z K oS na : Nat} (h : KPre s0 B Z K oS na)
    (hrd : s.rd = s0.rd) (hsp : s.sp = s0.sp) {i : Nat} (hi : i < na) :
    InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8 := by
  have hs := h.sp
  refine ⟨_, List.mem_append_left _ (hrd ▸ h.args), ?_⟩
  simp only [stackArgAddr, hsp]
  rw [show s0.sp + BitVec.ofNat 64 (32 + 8 * (8 + i)) = stackArgAddr s0 0 + BitVec.ofNat 64 (8 * i) by
    rw [stackArgAddr, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega_arith]
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

/-- `stackArg r i`: the stack argument `i` into `r`. -/
theorem KPre.stackArg_ok {s0 s : State} {B : Addr} {Z K oS na : Nat} (h : KPre s0 B Z K oS na)
    (hrd : s.rd = s0.rd) (hsp : s.sp = s0.sp) {r : Reg} (hr : r ≠ .r0) {i : Nat} (hi : i < na)
    (hi' : 96 + 8 * i < 2 ^ 15) {rest : List Instr} {Q : State → Prop}
    (k : WP isa (.block rest) (s.write r (PPC64LE.stackArg s i)) Q) :
    WP isa (.block (VG.Impl.Rsa.PPC64LE.CrtValues.stackArg r i ++ rest)) s Q := by
  have rd := h.arg_rd hrd hsp hi
  have ho : VG.Impl.Rsa.PPC64LE.CrtValues.stackOff i < 2 ^ 15 := hi'
  rw [WP.block_append_iff]
  have ea : (s.write r (s.sp + BitVec.ofNat 64 (VG.Impl.Rsa.PPC64LE.CrtValues.stackOff i))).gpr r +
      BitVec.ofNat 64 0 = stackArgAddr s i := by
    simp only [State.write, ite_true, BitVec.add_zero, CrtValues.stackArg_addr]
  have hrd' : InRegions ((s.write r (s.sp + BitVec.ofNat 64 (VG.Impl.Rsa.PPC64LE.CrtValues.stackOff i))).rd ++
      (s.write r (s.sp + BitVec.ofNat 64 (VG.Impl.Rsa.PPC64LE.CrtValues.stackOff i))).wr)
      ((s.write r (s.sp + BitVec.ofNat 64 (VG.Impl.Rsa.PPC64LE.CrtValues.stackOff i))).gpr r +
        BitVec.ofNat 64 0) 8 := by
    rw [ea]; exact rd
  refine WP.of_runBlock ⟨s.write r (PPC64LE.stackArg s i), ?_, k⟩
  simp only [VG.Impl.Rsa.PPC64LE.CrtValues.stackArg, runBlock_cons, runStep_some, runBlock_nil,
    CrtValues.exec_addSp ho, exec_load_d hr ⟨by decide, by decide⟩ hrd', Option.some.injEq]
  rw [ea, VG.Proof.Rsa.PPC64LE.Keys.write_write]
  rfl

/-! ## The entry and the exit -/

/-- The header after the entry's stores. -/
def kEntryMem (s0 : State) (B : Addr) : Mem :=
  ((((((((((((((s0.mem.writeW (off B 0) (s0.gpr .r14)).writeW (off B 8) (s0.gpr .r15)).writeW (off B 16) (s0.gpr .r16)).writeW (off B 24) (s0.gpr .r17)).writeW (off B 32) (s0.gpr .r18)).writeW (off B 40) (s0.gpr .r19)).writeW (off B 48) (s0.gpr .r20)).writeW (off B 56) (s0.gpr .r21)).writeW (off B 64) (s0.gpr .r22)).writeW (off B 72) (s0.gpr .r23)).writeW (off B 80) (s0.gpr .r24)).writeW (off B 88) (s0.gpr .r26)).writeW (off B 96) (s0.gpr .r29)).writeW (off B 104) (s0.gpr .r30)).writeW (off B 112) (s0.gpr .r31)

theorem kEntryMem_frame {s0 : State} {B : Addr} {Z : Nat} (hnw : B.toNat + Z ≤ 2 ^ 64) (hz : 120 ≤ Z) :
    ∀ x, Z ≤ ofs B x → kEntryMem s0 B x = s0.mem x := by
  intro x hx
  have o : ∀ (m : Mem) (d : Nat) (v : BitVec 64), d + 8 ≤ 120 → (m.writeW (off B d) v) x = m x :=
    fun m d v hd => writeW_outside m B (d := d) v (by omega_arith) x (Or.inr (by omega_arith))
  simp only [kEntryMem]
  rw [o _ 112 _ (by decide), o _ 104 _ (by decide), o _ 96 _ (by decide), o _ 88 _ (by decide), o _ 80 _ (by decide),
      o _ 72 _ (by decide), o _ 64 _ (by decide), o _ 56 _ (by decide), o _ 48 _ (by decide), o _ 40 _ (by decide),
      o _ 32 _ (by decide), o _ 24 _ (by decide), o _ 16 _ (by decide), o _ 8 _ (by decide), o _ 0 _ (by decide)]

theorem kEntryMem_hdr (s0 : State) (B : Addr) :
    ∀ i < 15, (kEntryMem s0 B).readW (off B (8 * i)) 64 = s0.gpr (kSaved i) := by
  intro i hi
  simp only [kEntryMem]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11
      ∨ i = 12 ∨ i = 13 ∨ i = 14 by omega_arith) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := decide) only [kSaved, Nat.mul_zero, Nat.reduceMul, CrtValues.readW_sep,
    Mem.readW_writeW_self64]

/-- `save oS`: the registers saved, `KBase`. -/
theorem save_ok {s0 : State} {B : Addr} {Z K oS na : Nat} (h : KPre s0 B Z K oS na) (hoS : 96 + 8 * oS < 2 ^ 15)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s, KBase B Z s0 s → Keep [.r11, .r31] s0 s → WP isa (.block rest) s Q) :
    WP isa (.block (save oS ++ rest)) s0 Q := by
  have hs : Scr s0 B Z := Scr.of_mem h.wr h.nowrap
  have hz := h.zk
  rw [save, List.append_assoc]
  refine h.stackArg_ok rfl rfl (r := .r11) (by decide) h.hoS hoS ?_
  rw [h.base]
  have k1 : Keep [.r11] s0 (s0.write .r11 B) := Keep.write _ _ _
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r31] (Q := fun s => s.mem = kEntryMem s0 B ∧ s.gpr .r31 = B) ?_ (by decide))
    fun s ⟨⟨m, r31⟩, kk⟩ => ?_
  · prun [hs.st (d := 0) (n := 8) (by omega_arith), hs.st (d := 8) (n := 8) (by omega_arith),
      hs.st (d := 16) (n := 8) (by omega_arith), hs.st (d := 24) (n := 8) (by omega_arith), hs.st (d := 32) (n := 8) (by omega_arith),
      hs.st (d := 40) (n := 8) (by omega_arith), hs.st (d := 48) (n := 8) (by omega_arith), hs.st (d := 56) (n := 8) (by omega_arith),
      hs.st (d := 64) (n := 8) (by omega_arith), hs.st (d := 72) (n := 8) (by omega_arith), hs.st (d := 80) (n := 8) (by omega_arith),
      hs.st (d := 88) (n := 8) (by omega_arith), hs.st (d := 96) (n := 8) (by omega_arith), hs.st (d := 104) (n := 8) (by omega_arith),
      hs.st (d := 112) (n := 8) (by omega_arith)]
    exact ⟨rfl, BitVec.add_zero _⟩
  · have K := (k1.trans kk).mono (rs' := [.r11, .r31])
    exact k s ⟨K.sp, K.lr, K.rd, K.wr, fun x hx => by rw [m]; exact kEntryMem_frame h.nowrap (by omega_arith) x hx,
      fun i hi => by rw [m]; exact kEntryMem_hdr s0 B i hi, r31⟩ K

/-- `restore`: the saved registers from the header. -/
theorem restore_ok {B : Addr} {Z : Nat} {s0 t : State} (h : KBase B Z s0 t) (hwr : (⟨B, Z⟩ : Region) ∈ s0.wr)
    (hnw : B.toNat + Z ≤ 2 ^ 64) (hz : 120 ≤ Z) :
    WP isa (.block restore) t fun u => (u.gpr .r14 = s0.gpr .r14 ∧ u.gpr .r15 = s0.gpr .r15
        ∧ u.gpr .r16 = s0.gpr .r16 ∧ u.gpr .r17 = s0.gpr .r17 ∧ u.gpr .r18 = s0.gpr .r18 ∧ u.gpr .r19 = s0.gpr .r19
        ∧ u.gpr .r20 = s0.gpr .r20 ∧ u.gpr .r21 = s0.gpr .r21 ∧ u.gpr .r22 = s0.gpr .r22 ∧ u.gpr .r23 = s0.gpr .r23
        ∧ u.gpr .r24 = s0.gpr .r24 ∧ u.gpr .r26 = s0.gpr .r26 ∧ u.gpr .r29 = s0.gpr .r29 ∧ u.gpr .r30 = s0.gpr .r30
        ∧ u.gpr .r31 = s0.gpr .r31 ∧ u.mem = t.mem) ∧
      Keep [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r26, .r29, .r30, .r31] t u := by
  have hs : Scr t B Z := Scr.of_mem (by rw [h.wr]; exact hwr) hnw
  have e0 := h.hdr 0 (by decide)
  have e1 := h.hdr 1 (by decide)
  have e2 := h.hdr 2 (by decide)
  have e3 := h.hdr 3 (by decide)
  have e4 := h.hdr 4 (by decide)
  have e5 := h.hdr 5 (by decide)
  have e6 := h.hdr 6 (by decide)
  have e7 := h.hdr 7 (by decide)
  have e8 := h.hdr 8 (by decide)
  have e9 := h.hdr 9 (by decide)
  have e10 := h.hdr 10 (by decide)
  have e11 := h.hdr 11 (by decide)
  have e12 := h.hdr 12 (by decide)
  have e13 := h.hdr 13 (by decide)
  have e14 := h.hdr 14 (by decide)
  simp only [kSaved, Nat.reduceMul] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
  refine WP.keep _ ?_ (by decide)
  prun [restore, h.r31, hs.ld (d := 0) (n := 8) (by omega_arith), hs.ld (d := 8) (n := 8) (by omega_arith),
      hs.ld (d := 16) (n := 8) (by omega_arith), hs.ld (d := 24) (n := 8) (by omega_arith), hs.ld (d := 32) (n := 8) (by omega_arith),
      hs.ld (d := 40) (n := 8) (by omega_arith), hs.ld (d := 48) (n := 8) (by omega_arith), hs.ld (d := 56) (n := 8) (by omega_arith),
      hs.ld (d := 64) (n := 8) (by omega_arith), hs.ld (d := 72) (n := 8) (by omega_arith), hs.ld (d := 80) (n := 8) (by omega_arith),
      hs.ld (d := 88) (n := 8) (by omega_arith), hs.ld (d := 96) (n := 8) (by omega_arith), hs.ld (d := 104) (n := 8) (by omega_arith),
      hs.ld (d := 112) (n := 8) (by omega_arith), e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14]
  exact e0

end VG.Proof.Rsa.PPC64LE.KeyCheck
