module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.RecoverDet
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RdContract
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcFrame
public import VerifiedGarbage.Proof.Rsa.KeyWorkspace
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBase
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
public import VerifiedGarbage.Proof.Rsa.BoolNat
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyHalf
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvLoads
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyOps
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvCheck
import VerifiedGarbage.Proof.Rsa.PPC64LE.KcCk
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBytes
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvStores
import VerifiedGarbage.Proof.Bignum.ByteWords

/-!
# `vg_rsa_recover_primes_det` on PPC64LE: the frame, the entry, the check of `n` and the loads

`rvB s0`, `rvZ s0`: the working space; `kK s0`: `n_len`; `ww k`: the digits
of the key working space, `2 ⌈k / 8⌉ + 2`; `sv k`: the offset of its array
`nArr`, where the entry saves the nonvolatile registers. `RBase s0 s`: from
the initial state `s0`, the stack pointer, the link register and the
regions are `s0`'s, memory is the entry's but on the working space's first
`sv` bytes, and the working space's base is in `r31`.

The slots of the header as numbers and flags as words (`b64`); the top
digits of an array (`setTop_ok`, `clrW_ok`). `entry_ok`: the entry saves
the registers, sets up `w` and the stride, and keeps the arguments
(`RArgs`). `ctxW_ok`, `ctxw_ok`: from `w` digits to `W = 2 w + 2` and
back; `zeroAll_ok`: every array zeroed. `nCheck_ok`: `r0` is 0 iff `n` is a
valid modulus. `loads_ok`: `n`, `e` and `d` read from their bytes.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Proof.Rsa.PPC64LE.KeyCheck (KPre)
open VG.Impl.Rsa.PPC64LE.Recover (save restore savedReg nArr wOf saveBase)

abbrev rvB (s0 : State) : Addr := PPC64LE.stackArg s0 2
abbrev rvZ (s0 : State) : Nat := (PPC64LE.stackArg s0 3).toNat * 8
abbrev kK (s0 : State) : Nat := (s0.gpr .r8).toNat
abbrev ww (k : Nat) : Nat := 2 * ((k + 7) / 8) + 2
abbrev sv (k : Nat) : Nat := KeyWorkspace.arr (ww k) nArr

theorem rv_kpre {s0 : State} (h : rvPre s0) : KPre s0 (rvB s0) (rvZ s0) (kK s0) 2 4 := by
  obtain ⟨hsp, hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, sa, -, -, -, -, -, nw, ⟨hk, hk'⟩, h4, -, -, -,
    -, -, hsl⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  exact ⟨by rw [hwr]; simp, nw, by simp only [rvZ, kK]; omega_arith, hk, hk', by omega_arith, by rw [hrd]; simp, sa, rfl,
    by decide, h4⟩

theorem rv_sv {s0 : State} (h : rvPre s0) :
    sv (kK s0) + 2 * KeyWorkspace.S (ww (kK s0)) ≤ rvZ s0 := by
  have hp := rv_kpre h
  have z := hp.zk; have k1 := hp.k64
  show 160 + 44 * (4 * (2 * ((kK s0 + 7) / 8) + 2 + 2)) + 2 * (4 * (2 * ((kK s0 + 7) / 8) + 2 + 2)) ≤ rvZ s0
  clear h hp
  generalize rvZ s0 = Z at z ⊢
  generalize kK s0 = K at z k1 ⊢
  have h8 : 8 * ((K + 7) / 8) ≤ K + 7 := Nat.mul_div_le _ _
  generalize (K + 7) / 8 = q at *
  have e : 160 + 44 * (4 * (2 * q + 2 + 2)) + 2 * (4 * (2 * q + 2 + 2)) = 368 * q + 896 := by omega_arith
  rw [e]
  have : 368 * q ≤ 46 * (K + 7) := by omega_arith
  omega_arith

theorem wOf_val (x : BitVec 64) (hx : x.toNat ≤ 1024) :
    (x + BitVec.ofNat 64 7) >>> 3 <<< 1 + BitVec.ofNat 64 2 = BitVec.ofNat 64 (ww x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (x + BitVec.ofNat 64 7).toNat = x.toNat + 7 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 7 < 2 ^ 64 by decide),
      Nat.mod_eq_of_lt (by omega_arith)]
  have h2 : ((x + BitVec.ofNat 64 7) >>> 3).toNat = (x.toNat + 7) / 8 := by
    rw [BitVec.toNat_ushiftRight, h1, Nat.shiftRight_eq_div_pow]
  have h3 : ((x + BitVec.ofNat 64 7) >>> 3 <<< 1).toNat = 2 * ((x.toNat + 7) / 8) := by
    rw [BitVec.toNat_shiftLeft, h2, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  rw [BitVec.toNat_add, h3, BitVec.toNat_ofNat, BitVec.toNat_ofNat]

theorem stride_val (w : Nat) :
    (BitVec.ofNat 64 w + BitVec.ofNat 64 2) <<< 2 = BitVec.ofNat 64 (KeyWorkspace.S w) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, KeyWorkspace.S]
  omega_arith

/-- `wOf rd`: `w = 2 ⌈n_len / 8⌉ + 2` into `rd`. -/
theorem wOf_ok {s : State} {rd : Reg} (hrd : rd ≠ .r0) (h8 : (s.gpr .r8).toNat ≤ 1024)
    {rest : List Instr} {Q : State → Prop}
    (k : WP isa (.block rest) (s.write rd (BitVec.ofNat 64 (ww (s.gpr .r8).toNat))) Q) :
    WP isa (.block (wOf rd ++ rest)) s Q := by
  rw [WP.block_append_iff]
  refine WP.of_runBlock ?_
  simp only [wOf, runBlock_cons, runStep_some, runBlock_nil,
    exec_addi (show Reg.r8 ≠ .r0 by decide) (show 7 < 2 ^ 15 by decide), exec_lsr_d (show 3 < 64 by decide),
    exec_lsl (show 1 < 64 by decide), exec_addi hrd (show 2 < 2 ^ 15 by decide), Option.some.injEq,
    exists_eq_left', gpr_write, ite_true, VG.Proof.Rsa.PPC64LE.Keys.write_write, wOf_val _ h8]
  exact k

/-- The stride of `w` (in `rs`) into `rd`. -/
theorem strideOf_ok {s : State} {rd rs : Reg} (hrs : rs ≠ .r0) {w : Nat} (hw : s.gpr rs = BitVec.ofNat 64 w)
    {rest : List Instr} {Q : State → Prop}
    (k : WP isa (.block rest) (s.write rd (BitVec.ofNat 64 (KeyWorkspace.S w))) Q) :
    WP isa (.block (([.addi rd rs 2, .lsl rd rd 2] : List Instr) ++ rest)) s Q := by
  rw [WP.block_append_iff]
  refine WP.of_runBlock ?_
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addi hrs (show 2 < 2 ^ 15 by decide),
    exec_lsl (show 2 < 64 by decide), Option.some.injEq, exists_eq_left', gpr_write, ite_true,
    VG.Proof.Rsa.PPC64LE.Keys.write_write, hw, stride_val]
  exact k

/-- `saveBase rd b st`: the address of the key array `nArr` into `rd`. -/
theorem saveBase_ok {s : State} {rd b st : Reg} (hrd : rd ≠ .r0) (hb : b ≠ rd) (hst : st ≠ rd) {B : Addr}
    {w : Nat} (hB : s.gpr b = B) (hS : s.gpr st = BitVec.ofNat 64 (KeyWorkspace.S w))
    {rest : List Instr} {Q : State → Prop}
    (k : WP isa (.block rest) (s.write rd (off B (KeyWorkspace.arr w nArr))) Q) :
    WP isa (.block (saveBase rd b st ++ rest)) s Q := by
  rw [WP.block_append_iff]
  refine WP.of_runBlock ?_
  simp only [saveBase, runBlock_cons, runStep_some, runBlock_nil, exec_li (show nArr < 2 ^ 15 by decide),
    exec_mul, exec_add, VG.Proof.Rsa.PPC64LE.Keys.hdr_eq, exec_addi hrd (show KeyWorkspace.hdr < 2 ^ 15 by decide),
    Option.some.injEq, exists_eq_left', gpr_write, ite_true, hb, hst, ite_false,
    VG.Proof.Rsa.PPC64LE.Keys.write_write, hB, hS, VG.Proof.Rsa.PPC64LE.Keys.ptr_val]
  exact k

/-- The memory after the entry's stores. -/
def rEntryMem (s0 : State) : Mem :=
  (((((((((((((((((s0.mem.writeW (off (rvB s0) (sv (kK s0))) (s0.gpr .r14)).writeW (off (rvB s0) (sv (kK s0) + 8)) (s0.gpr .r15)).writeW (off (rvB s0) (sv (kK s0) + 16)) (s0.gpr .r16)).writeW (off (rvB s0) (sv (kK s0) + 24)) (s0.gpr .r17)).writeW (off (rvB s0) (sv (kK s0) + 32)) (s0.gpr .r18)).writeW (off (rvB s0) (sv (kK s0) + 40)) (s0.gpr .r19)).writeW (off (rvB s0) (sv (kK s0) + 48)) (s0.gpr .r20)).writeW (off (rvB s0) (sv (kK s0) + 56)) (s0.gpr .r21)).writeW (off (rvB s0) (sv (kK s0) + 64)) (s0.gpr .r22)).writeW (off (rvB s0) (sv (kK s0) + 72)) (s0.gpr .r23)).writeW (off (rvB s0) (sv (kK s0) + 80)) (s0.gpr .r24)).writeW (off (rvB s0) (sv (kK s0) + 88)) (s0.gpr .r25)).writeW (off (rvB s0) (sv (kK s0) + 96)) (s0.gpr .r26)).writeW (off (rvB s0) (sv (kK s0) + 104)) (s0.gpr .r27)).writeW (off (rvB s0) (sv (kK s0) + 112)) (s0.gpr .r28)).writeW (off (rvB s0) (sv (kK s0) + 120)) (s0.gpr .r29)).writeW (off (rvB s0) (sv (kK s0) + 128)) (s0.gpr .r30)).writeW (off (rvB s0) (sv (kK s0) + 136)) (s0.gpr .r31)

theorem saveStores_eq : (List.range 18).map (fun i => Instr.store .d (savedReg i) .r12 (8 * i)) =
    [.store .d .r14 .r12 0, .store .d .r15 .r12 8, .store .d .r16 .r12 16, .store .d .r17 .r12 24, .store .d .r18 .r12 32, .store .d .r19 .r12 40, .store .d .r20 .r12 48, .store .d .r21 .r12 56, .store .d .r22 .r12 64, .store .d .r23 .r12 72, .store .d .r24 .r12 80, .store .d .r25 .r12 88, .store .d .r26 .r12 96, .store .d .r27 .r12 104, .store .d .r28 .r12 112, .store .d .r29 .r12 120, .store .d .r30 .r12 128, .store .d .r31 .r12 136] := rfl

/-- `save`: the working space's base into `r11`, and the nonvolatile
registers saved in its arrays 44–45. -/
theorem save_ok {s0 : State} (h : rvPre s0) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s, s.mem = rEntryMem s0 → s.gpr .r11 = rvB s0 → s.sp = s0.sp → Keep [.r0, .r11, .r12] s0 s →
      WP isa (.block rest) s Q) :
    WP isa (.block (save ++ rest)) s0 Q := by
  have hp := rv_kpre h
  have hs : Scr s0 (rvB s0) (rvZ s0) := Scr.of_mem hp.wr hp.nowrap
  have hsv := rv_sv h
  have h8 : (s0.gpr .r8).toNat ≤ 1024 := hp.k1024
  simp only [save, List.append_assoc]
  refine hp.stackArg_ok rfl rfl (r := .r11) (by decide) (by decide) (by decide) ?_
  refine wOf_ok (by decide) (by simpa [gpr_write] using h8) ?_
  rw [show (s0.write .r11 (PPC64LE.stackArg s0 2)).gpr .r8 = s0.gpr .r8 from rfl]
  refine strideOf_ok (rs := .r12) (w := ww (kK s0)) (by decide) (by simp [gpr_write]) ?_
  refine saveBase_ok (b := .r11) (w := ww (kK s0)) (by decide) (by decide) (by decide) (by simp [gpr_write]; rfl)
    (by simp [gpr_write]) ?_
  have h80 : 72 ≤ KeyWorkspace.S (ww (kK s0)) := by
    have := hp.k64; simp only [KeyWorkspace.S, ww]; omega_arith
  rw [saveStores_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = rEntryMem s0) ?_ (by decide)) fun t ⟨m, kt⟩ => ?_
  · prun [hs.st (d := sv (kK s0)) (n := 8) (by omega_arith), hs.st (d := sv (kK s0) + 8) (n := 8) (by omega_arith),
      hs.st (d := sv (kK s0) + 16) (n := 8) (by omega_arith), hs.st (d := sv (kK s0) + 24) (n := 8) (by omega_arith),
      hs.st (d := sv (kK s0) + 32) (n := 8) (by omega_arith), hs.st (d := sv (kK s0) + 40) (n := 8) (by omega_arith),
      hs.st (d := sv (kK s0) + 48) (n := 8) (by omega_arith), hs.st (d := sv (kK s0) + 56) (n := 8) (by omega_arith),
      hs.st (d := sv (kK s0) + 64) (n := 8) (by omega_arith), hs.st (d := sv (kK s0) + 72) (n := 8) (by omega_arith),
      hs.st (d := sv (kK s0) + 80) (n := 8) (by omega_arith), hs.st (d := sv (kK s0) + 88) (n := 8) (by omega_arith),
      hs.st (d := sv (kK s0) + 96) (n := 8) (by omega_arith), hs.st (d := sv (kK s0) + 104) (n := 8) (by omega_arith),
      hs.st (d := sv (kK s0) + 112) (n := 8) (by omega_arith), hs.st (d := sv (kK s0) + 120) (n := 8) (by omega_arith),
      hs.st (d := sv (kK s0) + 128) (n := 8) (by omega_arith), hs.st (d := sv (kK s0) + 136) (n := 8) (by omega_arith), off_add]
    rfl
  · refine k t m ?_ kt.sp ?_
    · rw [kt.gpr _ (by decide)]; simp [gpr_write]
    · exact (((((Keep.write _ _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans
        (Keep.write _ _ _)).trans kt).mono

theorem rEntryMem_outside (s0 : State) (hb : sv (kK s0) + 144 ≤ 2 ^ 64) :
    Outside (rvB s0) (sv (kK s0)) 144 s0.mem (rEntryMem s0) := by
  intro x hx
  have o : ∀ (m : Mem) (d : Nat) (v : BitVec 64), sv (kK s0) ≤ d → d + 8 ≤ sv (kK s0) + 144 →
      (m.writeW (off (rvB s0) d) v) x = m x :=
    fun m d v h1 h2 => writeW_outside m (rvB s0) (d := d) v (by omega_arith) x (by omega_arith)
  simp only [rEntryMem]
  rw [o _ (sv (kK s0) + 136) _ (by omega_arith) (by omega_arith), o _ (sv (kK s0) + 128) _ (by omega_arith) (by omega_arith), o _ (sv (kK s0) + 120) _ (by omega_arith) (by omega_arith), o _ (sv (kK s0) + 112) _ (by omega_arith) (by omega_arith), o _ (sv (kK s0) + 104) _ (by omega_arith) (by omega_arith), o _ (sv (kK s0) + 96) _ (by omega_arith) (by omega_arith), o _ (sv (kK s0) + 88) _ (by omega_arith) (by omega_arith), o _ (sv (kK s0) + 80) _ (by omega_arith) (by omega_arith), o _ (sv (kK s0) + 72) _ (by omega_arith) (by omega_arith), o _ (sv (kK s0) + 64) _ (by omega_arith) (by omega_arith), o _ (sv (kK s0) + 56) _ (by omega_arith) (by omega_arith), o _ (sv (kK s0) + 48) _ (by omega_arith) (by omega_arith), o _ (sv (kK s0) + 40) _ (by omega_arith) (by omega_arith), o _ (sv (kK s0) + 32) _ (by omega_arith) (by omega_arith), o _ (sv (kK s0) + 24) _ (by omega_arith) (by omega_arith), o _ (sv (kK s0) + 16) _ (by omega_arith) (by omega_arith), o _ (sv (kK s0) + 8) _ (by omega_arith) (by omega_arith), o _ (sv (kK s0)) _ (by omega_arith) (by omega_arith)]

theorem rEntryMem_saved (s0 : State) (hb : sv (kK s0) + 144 ≤ 2 ^ 64) :
    ∀ i < 18, (rEntryMem s0).readW (off (rvB s0) (sv (kK s0) + 8 * i)) 64 = s0.gpr (savedReg i) := by
  intro i hi
  simp only [rEntryMem]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 by omega_arith) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := omega_arith) only [savedReg, Nat.mul_zero, Nat.add_zero, Nat.reduceMul, CrtValues.readW_sep,
    Mem.readW_writeW_self64, List.getD_cons_zero, List.getD_cons_succ]

/-- What every stage keeps of the initial state. -/
structure RBase (s0 s : State) : Prop where
  pre : rvPre s0
  sp : s.sp = s0.sp
  lr : s.lr = s0.lr
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  mem : Outs (rvB s0) [(0, sv (kK s0))] (rEntryMem s0) s.mem
  r31 : s.gpr .r31 = rvB s0

theorem RBase.nowrap {s0 s : State} (h : RBase s0 s) : (rvB s0).toNat + rvZ s0 ≤ 2 ^ 64 :=
  (rv_kpre h.pre).nowrap

theorem RBase.svZ {s0 s : State} (h : RBase s0 s) : sv (kK s0) + 2 * KeyWorkspace.S (ww (kK s0)) ≤ rvZ s0 :=
  rv_sv h.pre

theorem RBase.s72 {s0 s : State} (h : RBase s0 s) : 72 ≤ KeyWorkspace.S (ww (kK s0)) := by
  have := (rv_kpre h.pre).k64; simp only [KeyWorkspace.S, ww]; omega_arith

theorem RBase.of_regs {s0 s t : State} (h : RBase s0 s) {rs : List Reg} (k : Keep rs s t) (hm : t.mem = s.mem)
    (hr : .r31 ∉ rs := by decide) : RBase s0 t :=
  ⟨h.pre, k.sp.trans h.sp, k.lr.trans h.lr, k.rd.trans h.rd, k.wr.trans h.wr, hm ▸ h.mem,
    (k.gpr _ hr).trans h.r31⟩

/-- A step that changes memory only on ranges below `sv`. -/
theorem RBase.of_outs {s0 s t : State} (h : RBase s0 s) {rs' : List (Nat × Nat)}
    (o : Outs (rvB s0) rs' s.mem t.mem) (ho : ∀ r ∈ rs', r.1 + r.2 ≤ sv (kK s0)) {rs : List Reg}
    (k : Keep rs s t) (hr : .r31 ∉ rs := by decide) : RBase s0 t :=
  ⟨h.pre, k.sp.trans h.sp, k.lr.trans h.lr, k.rd.trans h.rd, k.wr.trans h.wr,
    h.mem.trans (Outs.cover o fun r hr => ⟨(0, sv (kK s0)), List.mem_singleton_self _, Nat.zero_le _,
      by have := ho r hr; dsimp only; omega_arith⟩),
    (k.gpr _ hr).trans h.r31⟩

/-- A step that writes arrays of the key working space below `nArr`, and slots. -/
theorem RBase.of_keep {s0 s t : State} (h : RBase s0 s) {w : Nat} {js ds : List Nat}
    (kw : KeyWorkspace.Keep (rvB s0) w js ds s.mem t.mem)
    (hjs : ∀ j ∈ js, KeyWorkspace.arr w j + KeyWorkspace.S w ≤ sv (kK s0))
    (hds : ∀ d ∈ ds, d + 4 ≤ KeyWorkspace.hdr) {rs : List Reg} (k : Keep rs s t)
    (hr : .r31 ∉ rs := by decide) : RBase s0 t := by
  refine h.of_outs kw (fun r hr' => ?_) k hr
  simp only [KeyWorkspace.ranges, List.mem_append, List.mem_map] at hr'
  rcases hr' with ⟨j, hj, rfl⟩ | ⟨d, hd, rfl⟩
  · exact hjs j hj
  · have := hds d hd
    have : KeyWorkspace.hdr ≤ sv (kK s0) := Nat.le_add_right _ _
    dsimp only; omega_arith

/-- Memory outside the working space is the initial state's. -/
theorem RBase.frame {s0 s : State} (h : RBase s0 s) : ∀ x, rvZ s0 ≤ ofs (rvB s0) x → s.mem x = s0.mem x := by
  intro x hx
  have := h.svZ; have := h.s72; have := h.nowrap
  rw [h.mem x (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; dsimp only; omega_arith)]
  exact rEntryMem_outside s0 (by omega_arith) x (Or.inr (by omega_arith))

/-- The saved registers. -/
theorem RBase.saved {s0 s : State} (h : RBase s0 s) :
    ∀ i < 18, s.mem.readW (off (rvB s0) (sv (kK s0) + 8 * i)) 64 = s0.gpr (savedReg i) := by
  intro i hi
  have := h.svZ; have := h.s72; have := h.nowrap
  rw [← rEntryMem_saved s0 (by omega_arith) i hi]
  refine Mem.readW_congr fun b hb => h.mem _ fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  dsimp only
  rw [ofs_off (rvB s0) (by omega_arith)]
  omega_arith

/-- The stack arguments are `s0`'s. -/
theorem RBase.stackArg {s0 s : State} (h : RBase s0 s) {i : Nat} (hi : i < 4) :
    PPC64LE.stackArg s i = PPC64LE.stackArg s0 i := by
  have hp := rv_kpre h.pre
  have hs := hp.sp
  simp only [PPC64LE.stackArg, stackArgAddr, h.sp]
  refine Mem.readW_congr fun b hb => h.frame _ (CrtValues.past_of_disjoint hp.disj.symm ?_)
  rw [show s0.sp + BitVec.ofNat 64 (32 + 8 * (8 + i)) + BitVec.ofNat 64 b =
    stackArgAddr s0 0 + BitVec.ofNat 64 (8 * i + b) by
      rw [stackArgAddr, BitVec.add_assoc, BitVec.add_assoc, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
      congr 2; omega_arith]
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

/-- What the restore needs: the saved registers, the base and the stride. -/
structure RFin (s0 t : State) : Prop where
  pre : rvPre s0
  sp : t.sp = s0.sp
  lr : t.lr = s0.lr
  rd : t.rd = s0.rd
  wr : t.wr = s0.wr
  r31 : t.gpr .r31 = rvB s0
  r30 : t.gpr .r30 = BitVec.ofNat 64 (KeyWorkspace.S (ww (kK s0)))
  saved : ∀ i < 18, t.mem.readW (off (rvB s0) (sv (kK s0) + 8 * i)) 64 = s0.gpr (savedReg i)

theorem RBase.fin {s0 t : State} (h : RBase s0 t) (h30 : t.gpr .r30 = BitVec.ofNat 64 (KeyWorkspace.S (ww (kK s0)))) :
    RFin s0 t :=
  ⟨h.pre, h.sp, h.lr, h.rd, h.wr, h.r31, h30, h.saved⟩

/-- A step that writes only bytes outside the working space. -/
theorem RFin.of_out {s0 s t : State} (h : RFin s0 s) (o : ∀ x, ofs (rvB s0) x < rvZ s0 → t.mem x = s.mem x)
    {rs : List Reg} (k : Keep rs s t) (h30 : .r30 ∉ rs := by decide) (h31 : .r31 ∉ rs := by decide) :
    RFin s0 t := by
  have := rv_sv h.pre; have := (rv_kpre h.pre).nowrap
  have s72 : 72 ≤ KeyWorkspace.S (ww (kK s0)) := by
    have := (rv_kpre h.pre).k64; simp only [KeyWorkspace.S, ww]; omega_arith
  refine ⟨h.pre, k.sp.trans h.sp, k.lr.trans h.lr, k.rd.trans h.rd, k.wr.trans h.wr, (k.gpr _ h31).trans h.r31,
    (k.gpr _ h30).trans h.r30, fun i hi => ?_⟩
  rw [← h.saved i hi]
  refine Mem.readW_congr fun b hb => o _ ?_
  rw [ofs_off (rvB s0) (by omega_arith)]
  omega_arith

/-- `restore`: the saved registers back, from the arrays 44–45. -/
theorem restore_ok {s0 t : State} (h : RFin s0 t) :
    WP isa (.block restore) t fun u => ((u.gpr .r14 = s0.gpr .r14 ∧ u.gpr .r15 = s0.gpr .r15 ∧ u.gpr .r16 = s0.gpr .r16 ∧ u.gpr .r17 = s0.gpr .r17 ∧ u.gpr .r18 = s0.gpr .r18 ∧ u.gpr .r19 = s0.gpr .r19 ∧ u.gpr .r20 = s0.gpr .r20 ∧ u.gpr .r21 = s0.gpr .r21 ∧ u.gpr .r22 = s0.gpr .r22 ∧ u.gpr .r23 = s0.gpr .r23 ∧ u.gpr .r24 = s0.gpr .r24 ∧ u.gpr .r25 = s0.gpr .r25 ∧ u.gpr .r26 = s0.gpr .r26 ∧ u.gpr .r27 = s0.gpr .r27 ∧ u.gpr .r28 = s0.gpr .r28 ∧ u.gpr .r29 = s0.gpr .r29 ∧ u.gpr .r30 = s0.gpr .r30 ∧ u.gpr .r31 = s0.gpr .r31) ∧ u.mem = t.mem) ∧
      Keep [.r11, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31] t u := by
  have hp := rv_kpre h.pre
  have hs : Scr t (rvB s0) (rvZ s0) := Scr.of_mem (by rw [h.wr]; exact hp.wr) hp.nowrap
  have e0 := h.saved 0 (by decide)
  have e1 := h.saved 1 (by decide)
  have e2 := h.saved 2 (by decide)
  have e3 := h.saved 3 (by decide)
  have e4 := h.saved 4 (by decide)
  have e5 := h.saved 5 (by decide)
  have e6 := h.saved 6 (by decide)
  have e7 := h.saved 7 (by decide)
  have e8 := h.saved 8 (by decide)
  have e9 := h.saved 9 (by decide)
  have e10 := h.saved 10 (by decide)
  have e11 := h.saved 11 (by decide)
  have e12 := h.saved 12 (by decide)
  have e13 := h.saved 13 (by decide)
  have e14 := h.saved 14 (by decide)
  have e15 := h.saved 15 (by decide)
  have e16 := h.saved 16 (by decide)
  have e17 := h.saved 17 (by decide)
  simp only [savedReg, List.getD_cons_zero, List.getD_cons_succ, Nat.mul_zero, Nat.add_zero, Nat.reduceMul]
    at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
  unfold restore
  have := rv_sv h.pre
  have : 72 ≤ KeyWorkspace.S (ww (kK s0)) := by
    have := hp.k64; simp only [KeyWorkspace.S, ww]; omega_arith
  refine saveBase_ok (b := .r31) (w := ww (kK s0)) (by decide) (by decide) (by decide) h.r31 h.r30 ?_
  rw [show (List.range 18).map (fun i => Instr.load .d (savedReg i) .r11 (8 * i)) =
    [.load .d .r14 .r11 0, .load .d .r15 .r11 8, .load .d .r16 .r11 16, .load .d .r17 .r11 24, .load .d .r18 .r11 32, .load .d .r19 .r11 40, .load .d .r20 .r11 48, .load .d .r21 .r11 56, .load .d .r22 .r11 64, .load .d .r23 .r11 72, .load .d .r24 .r11 80, .load .d .r25 .r11 88, .load .d .r26 .r11 96, .load .d .r27 .r11 104, .load .d .r28 .r11 112, .load .d .r29 .r11 120, .load .d .r30 .r11 128, .load .d .r31 .r11 136] from rfl]
  refine WP.mono (WP.keep [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31] (Q := fun u => ((u.gpr .r14 = s0.gpr .r14 ∧ u.gpr .r15 = s0.gpr .r15 ∧ u.gpr .r16 = s0.gpr .r16 ∧ u.gpr .r17 = s0.gpr .r17 ∧ u.gpr .r18 = s0.gpr .r18 ∧ u.gpr .r19 = s0.gpr .r19 ∧ u.gpr .r20 = s0.gpr .r20 ∧ u.gpr .r21 = s0.gpr .r21 ∧ u.gpr .r22 = s0.gpr .r22 ∧ u.gpr .r23 = s0.gpr .r23 ∧ u.gpr .r24 = s0.gpr .r24 ∧ u.gpr .r25 = s0.gpr .r25 ∧ u.gpr .r26 = s0.gpr .r26 ∧ u.gpr .r27 = s0.gpr .r27 ∧ u.gpr .r28 = s0.gpr .r28 ∧ u.gpr .r29 = s0.gpr .r29 ∧ u.gpr .r30 = s0.gpr .r30 ∧ u.gpr .r31 = s0.gpr .r31) ∧ u.mem = t.mem)) ?_ (by decide))
    fun u ⟨q, k⟩ => ⟨q, ((Keep.write _ _ _).trans k).mono⟩
  prun [hs.ld (d := sv (kK s0)) (n := 8) (by omega_arith), hs.ld (d := sv (kK s0) + 8) (n := 8) (by omega_arith),
      hs.ld (d := sv (kK s0) + 16) (n := 8) (by omega_arith), hs.ld (d := sv (kK s0) + 24) (n := 8) (by omega_arith),
      hs.ld (d := sv (kK s0) + 32) (n := 8) (by omega_arith), hs.ld (d := sv (kK s0) + 40) (n := 8) (by omega_arith),
      hs.ld (d := sv (kK s0) + 48) (n := 8) (by omega_arith), hs.ld (d := sv (kK s0) + 56) (n := 8) (by omega_arith),
      hs.ld (d := sv (kK s0) + 64) (n := 8) (by omega_arith), hs.ld (d := sv (kK s0) + 72) (n := 8) (by omega_arith),
      hs.ld (d := sv (kK s0) + 80) (n := 8) (by omega_arith), hs.ld (d := sv (kK s0) + 88) (n := 8) (by omega_arith),
      hs.ld (d := sv (kK s0) + 96) (n := 8) (by omega_arith), hs.ld (d := sv (kK s0) + 104) (n := 8) (by omega_arith),
      hs.ld (d := sv (kK s0) + 112) (n := 8) (by omega_arith), hs.ld (d := sv (kK s0) + 120) (n := 8) (by omega_arith),
      hs.ld (d := sv (kK s0) + 128) (n := 8) (by omega_arith), hs.ld (d := sv (kK s0) + 136) (n := 8) (by omega_arith), off_add, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17]
  exact e0

end VG.Proof.Rsa.PPC64LE.Recover

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys VG.Proof.Rsa
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- A slot apart from a store. -/
theorem slot_wne (m : Mem) (B : Addr) {d e : Nat} (v : BitVec 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d)
    (hd : d + 4 ≤ 2 ^ 64) (he : e + 4 ≤ 2 ^ 64) : slot (m.writeW (off B d) v) B e = slot m B e := by
  simp only [slot, w32, off]
  rw [Mem.readW_writeW_sep (Offset.sep B (h.symm) he hd) (by decide)]

/-- A slot loaded. -/
theorem ld_slot {m : Mem} {B : Addr} {d v : Nat} (h : slot m B d = v) :
    (m.readW (B + BitVec.ofNat 64 d) 32).setWidth 64 = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  have := (m.readW (B + BitVec.ofNat 64 d) 32).isLt
  simp only [slot, w32, off] at h
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), h]
  rw [← h]; omega

/-- A flag as a word. -/
abbrev b64 (b : Bool) : BitVec 64 := BitVec.ofNat 64 (b2n b)

end VG.Proof.Rsa.PPC64LE.Recover

namespace VG.Proof.Rsa.PPC64LE.Keys

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Rsa.PPC64LE.Recover (setTop clrW)
open VG.Proof.Rsa.KeyWorkspace (arr S num)

theorem off_sub (p : Addr) {a b : Nat} (h : b ≤ a) :
    off p a - BitVec.ofNat 64 b = off p (a - b) := by
  simp only [off]
  rw [show BitVec.ofNat 64 a = BitVec.ofNat 64 (a - b) + BitVec.ofNat 64 b by
    rw [BitVec.ofNat_add_ofNat]; congr 1; omega_arith, ← BitVec.add_assoc, BitVec.add_sub_cancel]

/-- `setTop j`: the top digit of the zero array `j` := `2^31`. -/
theorem setTop_ok {s : State} {B : Addr} {Z v N j : Nat} (h : Ws s B Z v N) (hj : j < N) (hN : N ≤ 256)
    (hz : ∀ i < v, w32 s.mem B (arr v j + 4 * i) = 0) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z v N → KeyWorkspace.Keep B v [j] [] s.mem t.mem → num t.mem B v j = 2 ^ (32 * v - 1) →
      Keep [.r0, .r5] s t → WP isa (.block rest) t Q) :
    WP isa (.block (setTop j ++ rest)) s Q := by
  have fit := h.arr_fit hj
  have nw := h.nowrap
  have hS : S v = 4 * (v + 2) := rfl
  have hv := h.wpos
  have := h.wle
  have hs := h.scr
  rw [setTop, List.append_assoc]
  refine ptr_ok h (r := .r5) (by decide) (by decide) (by decide) (show j < 2 ^ 15 by omega_arith) ?_
  rw [WP.block_append_iff]
  let d := arr v j + 4 * (v - 1)
  have ea : off B (arr v j + 4 * v) - 4#64 = off B d := by
    rw [off_sub _ (by omega_arith)]; congr 1; omega_arith
  have ev : (1#64 <<< 31).setWidth 32 = BitVec.ofNat 32 (2 ^ 31) := by decide
  refine WP.mono (WP.keep [.r0, .r5] (Q := fun t => t.mem = s.mem.writeW (off B d) (BitVec.ofNat 32 (2 ^ 31)))
    ?_ (by decide)) fun t ⟨m, kt⟩ => ?_
  · prun [h.r29, shl2_ofNat, ea, exec_store_w (show Reg.r5 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
      hs.st (d := d) (n := 4) (by omega_arith), BitVec.add_zero, ev]
  · have o : Outside B d 4 s.mem t.mem := by rw [m]; exact writeW32_outside _ _ _ (by omega_arith)
    have K : Keep [.r0, .r5] s t := ((Keep.write _ _ _).trans kt).mono
    refine k t (h.of_keep K) (KeyWorkspace.Keep.of_arr (o := j) (d := 4 * (v - 1)) o (by omega_arith) (by simp)) ?_ K
    obtain ⟨u, rfl⟩ : ∃ u, v = u + 1 := ⟨v - 1, by omega_arith⟩
    simp only [num]
    rw [val32_append t.mem B (arr (u + 1) j) u 1]
    have lo : val32 t.mem B (arr (u + 1) j) u = 0 := by
      rw [← CrtValues.val32_of_zero (m := s.mem) (B := B) (d := arr (u + 1) j) (n := u) (fun i hi => hz i (by omega_arith))]
      refine val32_congr fun i hi => congrArg BitVec.toNat (Mem.readW_congr fun b hb => o _ ?_)
      rw [ofs_off B (by omega_arith)]; omega_arith
    have hi : val32 t.mem B (arr (u + 1) j + 4 * u) 1 = 2 ^ 31 := by
      simp only [val32, Nat.mul_zero, Nat.add_zero]
      rw [m, show arr (u + 1) j + 4 * u = d by omega_arith, w32_write_self]
      rfl
    rw [lo, hi, Nat.zero_add, ← Nat.pow_add]
    congr 1

/-- `clrW j`: the digit after the top of array `j` := 0. -/
theorem clrW_ok {s : State} {B : Addr} {Z v N j : Nat} (h : Ws s B Z v N) (hj : j < N) (hN : N ≤ 256)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z v N → KeyWorkspace.Keep B v [j] [] s.mem t.mem →
      Outside B (arr v j + 4 * v) 4 s.mem t.mem → w32 t.mem B (arr v j + 4 * v) = 0 →
      Keep [.r0, .r5] s t → WP isa (.block rest) t Q) :
    WP isa (.block (clrW j ++ rest)) s Q := by
  have fit := h.arr_fit hj
  have nw := h.nowrap
  have hS : S v = 4 * (v + 2) := rfl
  have := h.wle
  have hs := h.scr
  rw [clrW, List.append_assoc]
  refine ptr_ok h (r := .r5) (by decide) (by decide) (by decide) (show j < 2 ^ 15 by omega_arith) ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r0, .r5] (Q := fun t => t.mem = s.mem.writeW (off B (arr v j + 4 * v)) (0 : BitVec 32))
    ?_ (by decide))
    fun t ⟨m, kt⟩ => ?_
  · prun [h.r29, shl2_ofNat, exec_store_w (show Reg.r5 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
      hs.st (d := arr v j + 4 * v) (n := 4) (by omega_arith), BitVec.add_zero, off_add]
    rfl
  · have o : Outside B (arr v j + 4 * v) 4 s.mem t.mem := by rw [m]; exact writeW32_outside _ _ _ (by omega_arith)
    have K : Keep [.r0, .r5] s t := ((Keep.write _ _ _).trans kt).mono
    refine k t (h.of_keep K) (KeyWorkspace.Keep.of_arr (o := j) (d := 4 * v) o (by omega_arith) (by simp)) o ?_ K
    rw [m, w32_write_self]
    rfl

end VG.Proof.Rsa.PPC64LE.Keys

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Rsa.PPC64LE.Recover (entry save)

/-- The pointers and lengths the entry keeps. -/
structure RArgs (s0 t : State) : Prop where
  r21 : t.gpr .r21 = s0.gpr .r3
  r23 : t.gpr .r23 = s0.gpr .r5
  r24 : t.gpr .r24 = s0.gpr .r7
  r25 : t.gpr .r25 = s0.gpr .r8
  r26 : t.gpr .r26 = s0.gpr .r9
  r27 : t.gpr .r27 = s0.gpr .r10
  r28 : t.gpr .r28 = PPC64LE.stackArg s0 0
  r22 : t.gpr .r22 = PPC64LE.stackArg s0 1

/-- The registers `RArgs` is about. -/
abbrev argKeep : List Reg := [.r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28]

theorem RArgs.of_keep {s0 t u : State} (h : RArgs s0 t) {rs : List Reg} (k : Keep rs t u)
    (hr : ∀ r ∈ argKeep, r ∉ rs := by decide) : RArgs s0 u := by
  have e : ∀ r ∈ argKeep, u.gpr r = t.gpr r := fun r hr' => k.gpr r (hr r hr')
  exact ⟨(e _ (by decide)).trans h.r21, (e _ (by decide)).trans h.r23, (e _ (by decide)).trans h.r24,
    (e _ (by decide)).trans h.r25, (e _ (by decide)).trans h.r26, (e _ (by decide)).trans h.r27,
    (e _ (by decide)).trans h.r28, (e _ (by decide)).trans h.r22⟩

/-- The registers the entry changes. -/
abbrev entryRegs : List Reg :=
  [.r0, .r9, .r10, .r11, .r12, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

/-- After the entry. -/
structure REnt (s0 t : State) : Prop where
  base : RBase s0 t
  args : RArgs s0 t
  r29 : t.gpr .r29 = BitVec.ofNat 64 (ww (kK s0))
  r30 : t.gpr .r30 = BitVec.ofNat 64 (KeyWorkspace.S (ww (kK s0)))
  mem : t.mem = rEntryMem s0
  keep : Keep entryRegs s0 t

theorem entry_ok {s0 : State} (h : rvPre s0) : WP isa (.block entry) s0 (REnt s0) := by
  have hp := rv_kpre h
  have h8 : (s0.gpr .r8).toNat ≤ 1024 := hp.k1024
  rw [← List.append_nil entry]
  simp only [entry, List.append_assoc]
  refine save_ok h fun s m e11 esp k1 => ?_
  have e8 : s.gpr .r8 = s0.gpr .r8 := k1.gpr _ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r31] (Q := fun t => t.gpr .r31 = rvB s0 ∧ t.mem = s.mem) (by prun [e11, BitVec.add_zero])
    (by decide)) fun s₁ ⟨⟨a31, m1⟩, k2⟩ => ?_
  have e8' : s₁.gpr .r8 = s0.gpr .r8 := (k2.gpr _ (by decide)).trans e8
  refine wOf_ok (rd := .r29) (by decide) (by rw [e8']; exact h8) ?_
  rw [e8']
  refine strideOf_ok (rd := .r30) (rs := .r29) (w := ww (kK s0)) (by decide) (by simp [gpr_write]) ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r21, .r23, .r24, .r25, .r26, .r27]
    (Q := fun t => (t.gpr .r21 = s0.gpr .r3 ∧ t.gpr .r23 = s0.gpr .r5 ∧ t.gpr .r24 = s0.gpr .r7 ∧
      t.gpr .r25 = s0.gpr .r8 ∧ t.gpr .r26 = s0.gpr .r9 ∧ t.gpr .r27 = s0.gpr .r10) ∧ t.mem = s₁.mem)
    (by prun [k2.gpr .r3 (by decide), k2.gpr .r5 (by decide), k2.gpr .r7 (by decide), e8',
      k2.gpr .r9 (by decide), k2.gpr .r10 (by decide), k1.gpr .r3 (by decide), k1.gpr .r5 (by decide),
      k1.gpr .r7 (by decide), k1.gpr .r9 (by decide), k1.gpr .r10 (by decide), BitVec.add_zero]) (by decide))
    fun s₂ ⟨⟨⟨a21, a23, a24, a25, a26, a27⟩, m2⟩, k3⟩ => ?_
  have K : Keep (.r30 :: .r29 :: .r31 :: entryRegs) s0 s₂ :=
    (((k1.trans k2).trans ((Keep.write _ _ _).trans (Keep.write _ _ _))).trans k3).mono
  have hsp : s₂.sp = s0.sp := K.sp
  have hrd : s₂.rd = s0.rd := K.rd
  refine hp.stackArg_ok hrd hsp (r := .r28) (by decide) (by decide) (by decide) ?_
  refine hp.stackArg_ok (s := s₂.write .r28 _) hrd hsp (r := .r22) (by decide) (by decide) (by decide)
    (WP.block_nil ?_)
  have m3 : s₂.mem = rEntryMem s0 := by rw [m2]; exact m1.trans m
  have r31' : s₂.gpr .r31 = rvB s0 := by rw [k3.gpr _ (by decide)]; simpa [gpr_write] using a31
  have b2 : RBase s0 s₂ := ⟨h, hsp, K.lr, hrd, K.wr, by rw [m3]; exact Outs.refl _ _ _, r31'⟩
  have sa0 := b2.stackArg (i := 0) (by decide)
  have b3 := b2.of_regs (Keep.write s₂ .r28 (PPC64LE.stackArg s₂ 0)) rfl
  have sa1 := b3.stackArg (i := 1) (by decide)
  have e29 : s₂.gpr .r29 = BitVec.ofNat 64 (ww (kK s0)) := by rw [k3.gpr _ (by decide)]; simp [gpr_write]
  have e30 : s₂.gpr .r30 = BitVec.ofNat 64 (KeyWorkspace.S (ww (kK s0))) := by
    rw [k3.gpr _ (by decide)]; simp [gpr_write]
  refine ⟨b3.of_regs (Keep.write _ _ _) rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, m3,
    (K.trans ((Keep.write _ _ _).trans (Keep.write _ _ _))).mono⟩
  rotate_left 7
  · simp only [gpr_write, ite_true]; exact sa1
  all_goals simp only [gpr_write, reduceCtorEq, ite_false, ite_true, sa0, a21, a23, a24, a25, a26, a27, e29, e30]

end VG.Proof.Rsa.PPC64LE.Recover

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Recover (ctxW ctxw zeroAll nArr)
open VG.Proof.Rsa.KeyWorkspace (arr S)

theorem W_val (w : Nat) :
    BitVec.ofNat 64 w <<< 1 + BitVec.ofNat 64 2 = BitVec.ofNat 64 (2 * w + 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem w_val (w : Nat) (hw : w ≤ 1024) :
    (BitVec.ofNat 64 (2 * w + 2) - 2#64) >>> 1 = BitVec.ofNat 64 w := by
  apply BitVec.eq_of_toNat_eq
  have e : BitVec.ofNat 64 (2 * w + 2) - 2#64 = BitVec.ofNat 64 (2 * w) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  rw [e, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

/-- `ctxW`: `W = 2 w + 2` and its stride. -/
theorem ctxW_ok {s : State} {B : Addr} {Z w N N' : Nat} (h : Ws s B Z w N) (hW : 2 * w + 2 ≤ 1024)
    (fits : arr (2 * w + 2) N' ≤ Z) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z (2 * w + 2) N' → t.mem = s.mem → Keep [.r29, .r30] s t → WP isa (.block rest) t Q) :
    WP isa (.block (ctxW ++ rest)) s Q := by
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r29, .r30] (Q := fun t => t.gpr .r29 = BitVec.ofNat 64 (2 * w + 2) ∧
    t.gpr .r30 = BitVec.ofNat 64 (S (2 * w + 2)) ∧ t.mem = s.mem) ?_ (by decide)) fun t ⟨⟨t29, t30, tm⟩, kt⟩ =>
      k t ⟨h.scr.congr kt.wr, fits, by omega, hW, t29, t30, (kt.gpr _ (by decide)).trans h.r31⟩ tm kt
  have := h.wle
  prun [ctxW, VG.Impl.Rsa.PPC64LE.Keys.stride, h.r29, W_val, stride_val]

/-- `ctxw`: back to `w` and its stride. -/
theorem ctxw_ok {s : State} {B : Addr} {Z w N N' : Nat} (h : Ws s B Z (2 * w + 2) N) (hw : 0 < w)
    (fits : arr w N' ≤ Z) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z w N' → t.mem = s.mem → Keep [.r29, .r30] s t → WP isa (.block rest) t Q) :
    WP isa (.block (ctxw ++ rest)) s Q := by
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r29, .r30] (Q := fun t => t.gpr .r29 = BitVec.ofNat 64 w ∧
    t.gpr .r30 = BitVec.ofNat 64 (S w) ∧ t.mem = s.mem) ?_ (by decide)) fun t ⟨⟨t29, t30, tm⟩, kt⟩ =>
      k t ⟨h.scr.congr kt.wr, fits, hw, by have := h.wle; omega, t29, t30, (kt.gpr _ (by decide)).trans h.r31⟩ tm kt
  have := h.wle
  prun [ctxw, VG.Impl.Rsa.PPC64LE.Keys.stride, h.r29, w_val w (by omega), stride_val]

theorem digits_val (w : Nat) (hw : w ≤ 1024) :
    (BitVec.ofNat 64 44 * BitVec.ofNat 64 (S w)) >>> 2 = BitVec.ofNat 64 (nArr * (w + 2)) := by
  rw [← BitVec.ofNat_mul]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  simp only [S, nArr]
  rw [Nat.mod_eq_of_lt (show 44 * (4 * (w + 2)) < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 44 * (w + 2) < 2 ^ 64 by omega)]
  omega

/-- `zeroAll`: the digits of the arrays `0`–`nArr - 1` := 0. -/
theorem zeroAll_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) (fits : arr w nArr ≤ Z) :
    WP isa zeroAll s fun t => Ws t B Z w N ∧ (∀ i < nArr * (w + 2), w32 t.mem B (160 + 4 * i) = 0) ∧
      Outside B 160 (4 * (nArr * (w + 2))) s.mem t.mem ∧ Keep opRegs s t := by
  have := h.wle
  rw [zeroAll, WP.seq_iff]
  refine WP.mono (WP.keep [.r8] (Q := fun t => t.gpr .r8 = BitVec.ofNat 64 (nArr * (w + 2)) ∧ t.mem = s.mem)
    (by prun [nArr, h.r30, digits_val w (by omega)]) (by decide)) fun u ⟨⟨u8, um⟩, ku⟩ => ?_
  refine WP.mono (zeroArrays_ok (h.of_keep ku) u8 (by simp only [nArr]; omega) (by simp only [nArr]; omega)
    (by
      have e : 160 + 4 * (nArr * (w + 2)) = arr w nArr := by
        simp only [arr, S, VG.Proof.Rsa.KeyWorkspace.hdr]; rw [Nat.mul_left_comm]
      rw [e]; exact fits))
    fun t ⟨ht, z, out, kt⟩ => ⟨ht, z, by rw [← um]; exact out, (ku.trans kt).mono⟩

end VG.Proof.Rsa.PPC64LE.Recover

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Rsa.PPC64LE.Recover (nCheck)

/-- `n`'s bytes. -/
abbrev nB0 (s0 : State) : List Byte := Spec.Rsa.bytesAt s0.mem (s0.gpr .r7) (kK s0)

theorem len_nB0 (s0 : State) : (nB0 s0).length = kK s0 := by simp [Spec.Rsa.bytesAt]

theorem getD_of_lt {l : List Byte} {i : Nat} (h : i < l.length) : l.getD i 0 = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-- After `check1`. -/
def NC1 (s0 t : State) : Prop :=
  RBase s0 t ∧ RArgs s0 t ∧ t.gpr .r10 = BitVec.ofNat 64 (kK s0) ∧
    (t.gpr .r0 = 0 ↔ ((nB0 s0).getD (kK s0 - 1) 0).toNat % 2 = 1) ∧
    t.gpr .r11 = BitVec.ofNat 64 ((nB0 s0).getD 0 0).toNat

/-- After `check2`. -/
def NC2 (s0 t : State) : Prop :=
  RBase s0 t ∧ RArgs s0 t ∧
    (t.gpr .r0 = 0 ↔ Spec.Rsa.modulusValid (Spec.Rsa.os2ip (nB0 s0)) (kK s0) = true)

/-- The registers `nCheck` changes. -/
abbrev ncRegs : List Reg := [.r0, .r9, .r10, .r11, .r12]

theorem nc1_ok {s0 s : State} (b : RBase s0 s) (a : RArgs s0 s) :
    WP isa (.seq (.block [.addi .r9 .r24 0, .addi .r10 .r25 0]) (.block VG.Impl.Rsa.PPC64LE.CrtValues.check1)) s
      fun u => NC1 s0 u ∧ u.mem = s.mem ∧ Keep ncRegs s u := by
  obtain ⟨-, hrd, -, -, -, -, -, -, -, -, -, -, -, -, dn, -, -, -, -, -, wn, -, -, -, ⟨hk, -⟩, -⟩ := id b.pre
  refine WP.seq (WP.mono (CrtValues.mv2_ok (s := s) (d₁ := .r9) (d₂ := .r10) (a := .r24) (b := .r25)
    (by decide) (by decide) (by decide) (by decide)) fun t3 ⟨⟨u9, u10, m3⟩, k3⟩ => ?_)
  have b3 := b.of_regs k3 m3
  have wn' : (s0.gpr .r7).toNat + kK s0 ≤ 2 ^ 64 := wn
  have hc : ∀ i < kK s0, (⟨s0.gpr .r7, kK s0⟩ : Region).Contains (off (s0.gpr .r7) i) 1 := fun i hi =>
    Offset.contains_base _ (by omega) (by omega)
  have h10 : t3.gpr .r10 = BitVec.ofNat 64 (kK s0) := by rw [u10, a.r25]; exact CrtValues.ofNat_toNat64 _
  refine WP.mono (CrtValues.check1_ok (N := s0.gpr .r7) (k := kK s0) (nb := nB0 s0)
    (by rw [u9, a.r24]; simp [off]) h10 hk (len_nB0 _)
    (fun i hi => ⟨_, List.mem_append_left _ (by rw [b3.rd, hrd]; simp), hc i hi⟩)
    (fun i hi => by
      rw [b3.frame _ (CrtValues.past_of_disjoint dn (hc i hi))]; simp [Spec.Rsa.bytesAt, off]))
    fun t4 ⟨⟨i0, i11, im⟩, k4⟩ => ⟨⟨b3.of_regs k4 im, (a.of_keep k3).of_keep k4, by rw [k4.gpr _ (by decide), h10],
      by rw [i0, getD_of_lt (l := nB0 s0) (i := kK s0 - 1) (by simp only [len_nB0, kK]; omega)],
      by rw [i11, getD_of_lt (l := nB0 s0) (i := 0) (by simp only [len_nB0, kK]; omega)]⟩,
      im.trans m3, (k3.trans k4).mono⟩

theorem nc2_ok {s0 s : State} (h : NC1 s0 s) :
    WP isa VG.Impl.Rsa.PPC64LE.CrtValues.check2 s fun u => NC2 s0 u ∧ u.mem = s.mem ∧ Keep ncRegs s u := by
  obtain ⟨b, a, h10, i0, i11⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hk, hk'⟩, -⟩ := id b.pre
  refine WP.mono (CrtValues.check2_ok h10 hk hk' (len_nB0 _)
    (by rw [i0, getD_of_lt (l := nB0 s0) (i := kK s0 - 1) (by simp only [len_nB0, kK]; omega)])
    (by rw [i11, getD_of_lt (l := nB0 s0) (i := 0) (by simp only [len_nB0, kK]; omega)]))
    fun t ⟨hv, tm, kt⟩ => ⟨⟨b.of_regs kt tm, a.of_keep kt, hv⟩, tm, kt.mono⟩

theorem nCheck_ok {s0 s : State} (b : RBase s0 s) (a : RArgs s0 s) :
    WP isa nCheck s fun u => NC2 s0 u ∧ u.mem = s.mem ∧ Keep ncRegs s u := by
  unfold nCheck VG.Impl.Rsa.PPC64LE.CrtValues.check
  refine WP.assoc (WP.seq (WP.mono (nc1_ok b a) fun u ⟨h, m, k⟩ => WP.mono (nc2_ok h)
    fun v ⟨h', m', k'⟩ => ⟨h', m'.trans m, (k.trans k').mono⟩))

end VG.Proof.Rsa.PPC64LE.Recover

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Recover (loadR)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Proof.Rsa.KeyWorkspace (arr S num)

/-- An input: readable, apart from the working space. -/
structure InR (s0 : State) (P : Addr) (L : Nat) : Prop where
  rd : (⟨P, L⟩ : Region) ∈ s0.rd
  disj : (⟨P, L⟩ : Region).Disjoint ⟨rvB s0, rvZ s0⟩
  nowrap : P.toNat + L ≤ 2 ^ 64

theorem in_n {s0 : State} (h : rvPre s0) : InR s0 (s0.gpr .r7) (kK s0) := by
  obtain ⟨-, hrd, -, -, -, -, -, -, -, -, -, -, -, -, ns, -, -, -, -, -, wn, -⟩ := h
  exact ⟨by rw [hrd]; simp, ns, wn⟩

theorem in_e {s0 : State} (h : rvPre s0) : InR s0 (s0.gpr .r9) (s0.gpr .r10).toNat := by
  obtain ⟨-, hrd, -, -, -, -, -, -, -, -, -, -, -, -, -, es, -, -, -, -, -, we, -⟩ := h
  exact ⟨by rw [hrd]; simp, es, we⟩

theorem in_d {s0 : State} (h : rvPre s0) :
    InR s0 (PPC64LE.stackArg s0 0) (PPC64LE.stackArg s0 1).toNat := by
  obtain ⟨-, hrd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ds, -, -, -, -, -, wd, -⟩ := h
  exact ⟨by rw [hrd]; simp, ds, wd⟩

/-- `loadR rP rL j`: array `j` (of `v` digits), 0, := the `L` bytes at `P`. -/
theorem ldR_ok {s0 t : State} (b : RBase s0 t) {v N : Nat} (h : Ws t (rvB s0) (rvZ s0) v N) {j : Nat}
    (hj : j < N) (hN : N ≤ 256) {rP rL : Reg} (hrP : rP ≠ .r0) (hrL : rL ≠ .r0) (hrL6 : rL ≠ .r6)
    {P : Addr} {L : Nat} (hP : t.gpr rP = P) (hL : t.gpr rL = BitVec.ofNat 64 L) (hL1 : 1 ≤ L)
    (hLw : L ≤ 4 * v) (hi : InR s0 P L)
    (hz : ∀ i < v, w32 t.mem (rvB s0) (arr v j + 4 * i) = 0) :
    WP isa (seqs (loadR rP rL j)) t fun u =>
      Ws u (rvB s0) (rvZ s0) v N ∧ KeyWorkspace.Keep (rvB s0) v [j] [] t.mem u.mem ∧
      num u.mem (rvB s0) v j = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem P L) ∧
      Outside (rvB s0) (arr v j) (4 * v) t.mem u.mem ∧ Keep [.r0, .r5, .r6, .r8] t u := by
  rw [loadR]
  refine WP.seq (WP.mono (CrtValues.mv2_ok (s := t) (d₁ := .r6) (d₂ := .r8) hrP hrL hrL6 (by decide))
    fun u ⟨⟨u6, u8, um⟩, ku⟩ => ?_)
  have hu := h.of_keep ku
  have hP' := hi.nowrap
  have hc : ∀ i < L, (⟨P, L⟩ : Region).Contains (off P i) 1 := fun i hi =>
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  have hz' : val32 u.mem (rvB s0) (arr v j) v = 0 := by rw [um]; exact CrtValues.val32_of_zero hz
  refine WP.mono (load_ok hu hj hN (u6.trans hP) (u8.trans hL) hL1 hLw
    (fun i hi' => ⟨_, List.mem_append_left _ (by rw [ku.rd, b.rd]; exact hi.rd), hc i hi'⟩)
    (fun i hi' x hx e => by have := CrtValues.past_of_disjoint hi.disj (hc i hi'); rw [e] at this; omega_arith)
    (fun p hp => by rw [← off_add]; exact VG.Proof.Bignum.byte_zero_of_val32 hz' hp))
    fun w' ⟨hv, k, val, kv, o⟩ => ⟨hv, um ▸ k, ?_, um ▸ o, (ku.trans kv).mono⟩
  rw [val]
  congr 1
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun c hc' => ?_
  rw [um]
  exact b.frame _ (CrtValues.past_of_disjoint hi.disj (hc c (List.mem_range.mp hc')))

end VG.Proof.Rsa.PPC64LE.Recover

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Recover (loadR loads zeroAll ctxW nArr aN aOne aZ wZ wE wD wM wMod)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Proof.Rsa.KeyWorkspace (arr S num)

/-- `W = 2 w + 2`. -/
abbrev wW (k : Nat) : Nat := 2 * ww k + 2

/-- The bits of `d e`: `c = 8 (e_len + d_len)`. -/
abbrev cB (s0 : State) : Nat := 8 * ((s0.gpr .r10).toNat + (PPC64LE.stackArg s0 1).toNat)

abbrev nV (s0 : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r7) (kK s0))
abbrev eV (s0 : State) : Nat := Spec.Rsa.os2ip (eB s0)
abbrev dV (s0 : State) : Nat := Spec.Rsa.os2ip (dB s0)

theorem w32_out {B : Addr} {a n : Nat} {m m' : Mem} (o : Outside B a n m m') {d : Nat}
    (h : d + 4 ≤ a ∨ a + n ≤ d) (hd : d + 4 ≤ 2 ^ 64) : w32 m' B d = w32 m B d := by
  have := Outs.val32 (k := 1) (d := d) (Outs.of_outside o (List.mem_singleton_self _))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; dsimp only; omega_arith) (by omega_arith)
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using this

/-- The sizes. -/
structure Sz (s0 : State) : Prop where
  w1 : 18 ≤ ww (kK s0)
  w2 : ww (kK s0) ≤ 258
  kw : kK s0 ≤ 4 * ww (kK s0) - 8
  svw : sv (kK s0) = arr (ww (kK s0)) nArr
  svW : arr (wW (kK s0)) 16 ≤ sv (kK s0)
  svZ : sv (kK s0) + 2 * S (ww (kK s0)) ≤ rvZ s0
  nw : (rvB s0).toNat + rvZ s0 ≤ 2 ^ 64

theorem RBase.sz {s0 t : State} (b : RBase s0 t) : Sz s0 := by
  have hp := rv_kpre b.pre
  have k1 := hp.k64; have k2 := hp.k1024
  have h8 : 8 * ((kK s0 + 7) / 8) ≤ kK s0 + 7 := Nat.mul_div_le _ _
  have h8' : kK s0 + 7 < 8 * ((kK s0 + 7) / 8) + 8 := by omega_arith
  refine ⟨by simp only [ww]; omega_arith, by simp only [ww]; omega_arith, by simp only [ww]; omega_arith, rfl, ?_, b.svZ, b.nowrap⟩
  simp only [sv, wW, arr, S, nArr, VG.Proof.Rsa.KeyWorkspace.hdr]
  generalize ww (kK s0) = w
  omega_arith

/-- After the numbers are read. -/
structure LdD (s0 t : State) : Prop where
  base : RBase s0 t
  ws : Ws t (rvB s0) (rvZ s0) (wW (kK s0)) 16
  r21 : t.gpr .r21 = s0.gpr .r3
  r23 : t.gpr .r23 = s0.gpr .r5
  r24 : t.gpr .r24 = s0.gpr .r7
  r25 : t.gpr .r25 = s0.gpr .r8
  r26 : t.gpr .r26 = BitVec.ofNat 64 (cB s0)
  r27 : t.gpr .r27 = s0.gpr .r10
  vN : num t.mem (rvB s0) (ww (kK s0)) aN = nV s0
  vE : num t.mem (rvB s0) (wW (kK s0)) wE = eV s0
  vD : num t.mem (rvB s0) (wW (kK s0)) wD = dV s0
  zW : ∀ j ∈ [wZ, wM, wMod], ∀ i < wW (kK s0) + 2, w32 t.mem (rvB s0) (arr (wW (kK s0)) j + 4 * i) = 0
  zK : ∀ j ∈ [aOne, aZ], ∀ i < ww (kK s0) + 2, w32 t.mem (rvB s0) (arr (ww (kK s0)) j + 4 * i) = 0

theorem val32_out {B : Addr} {a n : Nat} {m m' : Mem} (o : Outside B a n m m') {d k : Nat}
    (h : d + 4 * k ≤ a ∨ a + n ≤ d) (hd : d + 4 * k ≤ 2 ^ 64) : val32 m' B d k = val32 m B d k :=
  Outs.val32 (Outs.of_outside o (List.mem_singleton_self _))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; dsimp only; omega_arith) hd

theorem c_val (a b : BitVec 64) :
    (a + b) <<< 3 = BitVec.ofNat 64 (8 * (a.toNat + b.toNat)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

/-- The entry's state is a working space of `w` digits. -/
theorem REnt.ws {s0 t : State} (e : REnt s0 t) : Ws t (rvB s0) (rvZ s0) (ww (kK s0)) nArr := by
  have hp := rv_kpre e.base.pre
  have z := e.base.sz
  exact ⟨Scr.of_mem (by rw [e.base.wr]; exact hp.wr) hp.nowrap, by rw [← z.svw]; have := z.svZ; omega_arith,
    by have := z.w1; omega_arith, by have := z.w2; omega_arith, e.r29, e.r30, e.base.r31⟩

/-- The registers the reading of the numbers changes. -/
abbrev ldRegs : List Reg := [.r0, .r3, .r5, .r6, .r7, .r8, .r9, .r26, .r29, .r30]

theorem loads_ok {s0 t : State} (e : REnt s0 t) : WP isa loads t fun u => LdD s0 u ∧ Keep ldRegs t u := by
  have b := e.base
  have z := b.sz
  have hp := rv_kpre b.pre
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hk, hk'⟩, -, -, e1, e2, d1, d2,
    -⟩ := id b.pre
  have w1 := z.w1; have w2 := z.w2; have kw := z.kw; have svW := z.svW
  have svw := z.svw
  have hkK : kK s0 = (s0.gpr .r8).toNat := rfl
  have hS : S (ww (kK s0)) = 4 * (ww (kK s0) + 2) := rfl
  have hSW : S (wW (kK s0)) = 4 * (2 * ww (kK s0) + 4) := rfl
  have nw := z.nw; have svZ := z.svZ
  simp only [loads, List.append_assoc, List.cons_append, List.nil_append]
  rw [wp_seqs_cons (by simp [loadR])]
  refine WP.mono (zeroAll_ok e.ws (by rw [← svw]; omega_arith)) fun t1 ⟨w1', z1, o1, k1⟩ => ?_
  have b1 : RBase s0 t1 := b.of_outs (Outs.of_outside o1 (List.mem_singleton_self _))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      show 160 + 4 * (nArr * (ww (kK s0) + 2)) ≤ sv (kK s0)
      simp only [sv, arr, S, VG.Proof.Rsa.KeyWorkspace.hdr]; rw [Nat.mul_left_comm]) k1
  -- `n`.
  rw [wp_seqs_append (by simp [loadR]) (by simp)]
  have zn : ∀ i < ww (kK s0), w32 t1.mem (rvB s0) (arr (ww (kK s0)) aN + 4 * i) = 0 := fun i hi => by
    have := z1 (32 * (ww (kK s0) + 2) + i) (by simp only [nArr]; omega_arith)
    rwa [show 160 + 4 * (32 * (ww (kK s0) + 2) + i) = arr (ww (kK s0)) aN + 4 * i by
      simp only [arr, S, aN, VG.Proof.Rsa.KeyWorkspace.hdr]; omega_arith] at this
  have a25 : t1.gpr .r25 = BitVec.ofNat 64 (kK s0) := by
    rw [k1.gpr _ (by decide), e.args.r25]; exact CrtValues.ofNat_toNat64 _
  refine WP.mono (ldR_ok b1 w1' (j := aN) (by decide) (by decide) (rP := .r24) (rL := .r25) (by decide) (by decide)
    (by decide) (by rw [k1.gpr _ (by decide), e.args.r24]) a25 (by simp only [kK]; omega_arith) (by omega_arith) (in_n b.pre)
    zn) fun t2 ⟨w2, kk2, v2, o2, k2⟩ => ?_
  have b2 : RBase s0 t2 := b1.of_keep kk2 (fun j hj => by
    simp only [List.mem_singleton] at hj; subst hj; rw [svw]; exact VG.Proof.Rsa.KeyWorkspace.arr_end (by decide))
    (by simp) k2
  -- `W`.
  rw [wp_seqs_cons (by simp [loadR]), ← List.append_nil ctxW]
  refine ctxW_ok w2 (by omega_arith) (Nat.le_trans svW (Nat.le_trans (Nat.le_add_right _ _) svZ)) fun t3 w3 m3 k3 =>
    WP.block_nil ?_
  have b3 := b2.of_regs k3 m3
  have hWw : 2 * ww (kK s0) + 2 = wW (kK s0) := rfl
  rw [hWw] at w3
  -- The digits still 0 after `n` is read: any outside `n`'s array.
  have zz2 : ∀ i < nArr * (ww (kK s0) + 2), (160 + 4 * i + 4 ≤ arr (ww (kK s0)) aN ∨
      arr (ww (kK s0)) aN + 4 * ww (kK s0) ≤ 160 + 4 * i) → w32 t2.mem (rvB s0) (160 + 4 * i) = 0 :=
    fun i hi hs => by rw [w32_out o2 hs (by simp only [nArr] at hi; omega_arith)]; exact z1 i hi
  have hA : ∀ j i, arr (wW (kK s0)) j + 4 * i = 160 + 4 * (j * (wW (kK s0) + 2) + i) := fun j i => by
    simp only [arr, S, VG.Proof.Rsa.KeyWorkspace.hdr]; rw [Nat.mul_left_comm, Nat.mul_add 4 _ i, Nat.add_assoc]
  have hAw : ∀ j i, arr (ww (kK s0)) j + 4 * i = 160 + 4 * (j * (ww (kK s0) + 2) + i) := fun j i => by
    simp only [arr, S, VG.Proof.Rsa.KeyWorkspace.hdr]; rw [Nat.mul_left_comm, Nat.mul_add 4 _ i, Nat.add_assoc]
  have haN : arr (ww (kK s0)) aN = 160 + 4 * (32 * (ww (kK s0) + 2)) := by
    have := hAw aN 0; simp only [aN, Nat.mul_zero, Nat.add_zero] at this; exact this
  -- `e`.
  rw [wp_seqs_append (by simp [loadR]) (by simp [loadR])]
  have a27 : t3.gpr .r27 = BitVec.ofNat 64 (s0.gpr .r10).toNat := by
    rw [k3.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide), e.args.r27]
    exact CrtValues.ofNat_toNat64 _
  refine WP.mono (ldR_ok b3 w3 (j := wE) (by decide) (by decide) (rP := .r26) (rL := .r27) (by decide) (by decide)
    (by decide) (by rw [k3.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide), e.args.r26]) a27 e1
    (by simp only [wW]; omega_arith) (in_e b.pre) (fun i hi => by
      rw [m3, hA, zz2 _ (by simp only [nArr, wE, wW] at hi ⊢; omega_arith) (by rw [haN]; simp only [wE, wW] at hi ⊢; omega_arith)]))
    fun t4 ⟨w4, kk4, v4, o4, k4⟩ => ?_
  have b4 : RBase s0 t4 := b3.of_keep kk4 (fun j hj => by
    simp only [List.mem_singleton] at hj; subst hj
    exact Nat.le_trans (VG.Proof.Rsa.KeyWorkspace.arr_end (by decide)) svW) (by simp) k4
  -- `d`.
  rw [wp_seqs_append (by simp [loadR]) (by simp)]
  have a22 : t4.gpr .r22 = BitVec.ofNat 64 (PPC64LE.stackArg s0 1).toNat := by
    rw [k4.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide), e.args.r22]
    exact CrtValues.ofNat_toNat64 _
  refine WP.mono (ldR_ok b4 w4 (j := wD) (by decide) (by decide) (rP := .r28) (rL := .r22) (by decide) (by decide)
    (by decide) (by rw [k4.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide),
      e.args.r28]) a22 d1 (by simp only [wW]; omega_arith) (in_d b.pre) (fun i hi => by
      rw [w32_out o4 (by rw [hA, hA]; simp only [wE, wD, wW] at hi ⊢; omega_arith) (by rw [hA]; simp only [wD, wW] at hi ⊢; omega_arith),
        m3, hA, zz2 _ (by simp only [nArr, wD, wW] at hi ⊢; omega_arith) (by rw [haN]; simp only [wD, wW] at hi ⊢; omega_arith)]))
    fun t5 ⟨w5, kk5, v5, o5, k5⟩ => ?_
  have b5 : RBase s0 t5 := b4.of_keep kk5 (fun j hj => by
    simp only [List.mem_singleton] at hj; subst hj
    exact Nat.le_trans (VG.Proof.Rsa.KeyWorkspace.arr_end (by decide)) svW) (by simp) k5
  -- `c`.
  rw [show seqs [.block [.add .r26 .r27 .r22, .lsl .r26 .r26 3]] = .block [.add .r26 .r27 .r22, .lsl .r26 .r26 3]
    from rfl]
  have a27' : t5.gpr .r27 = BitVec.ofNat 64 (s0.gpr .r10).toNat := by
    rw [k5.gpr _ (by decide), k4.gpr _ (by decide)]; exact a27
  have a22' : t5.gpr .r22 = BitVec.ofNat 64 (PPC64LE.stackArg s0 1).toNat := by rw [k5.gpr _ (by decide)]; exact a22
  refine WP.mono (WP.keep [.r26] (Q := fun u => u.gpr .r26 = BitVec.ofNat 64 (cB s0) ∧ u.mem = t5.mem)
    (by
      prun [a27', a22', c_val]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show (s0.gpr .r10).toNat < 2 ^ 64 by omega_arith),
        Nat.mod_eq_of_lt (show (PPC64LE.stackArg s0 1).toNat < 2 ^ 64 by omega_arith)]) (by decide))
    fun u ⟨⟨u26, um⟩, ku⟩ => ?_
  have K : Keep ldRegs t u := (((((k1.trans k2).trans k3).trans k4).trans k5).trans ku).mono
  have g : ∀ r ∈ [Reg.r21, .r23, .r24, .r25, .r27], u.gpr r = t.gpr r := fun r hr => K.gpr r (by revert r hr; decide)
  -- The digits still 0 at the end.
  have zz : ∀ i < nArr * (ww (kK s0) + 2), (160 + 4 * i + 4 ≤ arr (ww (kK s0)) aN ∨
      arr (ww (kK s0)) aN + 4 * ww (kK s0) ≤ 160 + 4 * i) →
      (160 + 4 * i + 4 ≤ arr (wW (kK s0)) wE ∨ arr (wW (kK s0)) wE + 4 * wW (kK s0) ≤ 160 + 4 * i) →
      (160 + 4 * i + 4 ≤ arr (wW (kK s0)) wD ∨ arr (wW (kK s0)) wD + 4 * wW (kK s0) ≤ 160 + 4 * i) →
      w32 u.mem (rvB s0) (160 + 4 * i) = 0 := fun i hi h1 h2 h3 => by
    have := hi; simp only [nArr] at this
    rw [um, w32_out o5 h3 (by omega_arith), w32_out o4 h2 (by omega_arith), m3]
    exact zz2 i hi h1
  have haE : arr (wW (kK s0)) wE = 160 + 4 * (wW (kK s0) + 2) := by
    have := hA wE 0; simp only [wE, Nat.one_mul, Nat.mul_zero, Nat.add_zero] at this; exact this
  have haD : arr (wW (kK s0)) wD = 160 + 4 * (2 * (wW (kK s0) + 2)) := by
    have := hA wD 0; simp only [wD, Nat.mul_zero, Nat.add_zero] at this; exact this
  refine ⟨⟨b5.of_regs ku um, w5.of_keep ku, (g _ (by decide)).trans e.args.r21, (g _ (by decide)).trans e.args.r23,
    (g _ (by decide)).trans e.args.r24, (g _ (by decide)).trans e.args.r25, u26, (g _ (by decide)).trans e.args.r27,
    ?_, ?_, ?_, ?_, ?_⟩, K⟩
  · simp only [VG.Proof.Rsa.KeyWorkspace.num]
    rw [um, val32_out o5 (by rw [haN, haD]; simp only [wW]; omega_arith) (by rw [haN]; simp only [nArr] at *; omega_arith),
      val32_out o4 (by rw [haN, haE]; simp only [wW]; omega_arith) (by rw [haN]; simp only [nArr] at *; omega_arith), m3]
    exact v2
  · simp only [VG.Proof.Rsa.KeyWorkspace.num]
    rw [um, val32_out o5 (by rw [haE, haD]; simp only [wW]; omega_arith) (by rw [haE]; simp only [wW]; omega_arith)]
    exact v4
  · rw [um]; exact v5
  · intro j hj i hi
    simp only [wZ, wM, wMod, List.mem_cons, List.not_mem_nil, or_false] at hj
    rw [hA]
    rcases hj with rfl | rfl | rfl <;>
      exact zz _ (by simp only [nArr, wW] at hi ⊢; omega_arith) (by rw [haN]; simp only [wW] at hi ⊢; omega_arith)
        (by rw [haE]; simp only [wW] at hi ⊢; omega_arith) (by rw [haD]; simp only [wW] at hi ⊢; omega_arith)
  · intro j hj i hi
    simp only [aOne, aZ, List.mem_cons, List.not_mem_nil, or_false] at hj
    rw [hAw]
    rcases hj with rfl | rfl <;>
      exact zz _ (by simp only [nArr] at hi ⊢; omega_arith) (by rw [haN]; omega_arith)
        (by rw [haE]; simp only [wW] at hi ⊢; omega_arith) (by rw [haD]; simp only [wW] at hi ⊢; omega_arith)

end VG.Proof.Rsa.PPC64LE.Recover
