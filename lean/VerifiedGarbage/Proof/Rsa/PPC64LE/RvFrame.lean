module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.Recover
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvContract
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcFrame
public import VerifiedGarbage.Proof.Rsa.KeyWorkspace
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBase
import VerifiedGarbage.Proof.Mont.RangeCover

/-!
# `vg_rsa_recover_primes` on PPC64LE: what every stage keeps

`rvB s0`, `rvZ s0`: the working space; `kK s0`: `n_len`; `ww k`: the digits
of the key working space, `2 ⌈k / 8⌉ + 2`; `sv k`: the offset of its array
`nArr`, where the entry saves the nonvolatile registers. `RBase s0 s`: from
the initial state `s0`, the stack pointer, the link register and the
regions are `s0`'s, memory is the entry's but on the working space's first
`sv` bytes, and the working space's base is in `r31`.
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

theorem rv_kpre {s0 : State} (h : rvP.pre s0) : KPre s0 (rvB s0) (rvZ s0) (kK s0) 2 4 := by
  obtain ⟨hsp, hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, sa, -, -, -, -, -, nw, ⟨hk, hk'⟩, h4, -, -, -,
    -, -, hsl⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  exact ⟨by rw [hwr]; simp, nw, by simp only [rvZ, kK]; omega, hk, hk', by omega, by rw [hrd]; simp, sa, rfl,
    by decide, h4⟩

theorem rv_sv {s0 : State} (h : rvP.pre s0) :
    sv (kK s0) + 2 * KeyWorkspace.S (ww (kK s0)) ≤ rvZ s0 := by
  have hp := rv_kpre h
  have z := hp.zk; have k1 := hp.k64
  show 160 + 44 * (4 * (2 * ((kK s0 + 7) / 8) + 2 + 2)) + 2 * (4 * (2 * ((kK s0 + 7) / 8) + 2 + 2)) ≤ rvZ s0
  clear h hp
  generalize rvZ s0 = Z at z ⊢
  generalize kK s0 = K at z k1 ⊢
  have h8 : 8 * ((K + 7) / 8) ≤ K + 7 := Nat.mul_div_le _ _
  generalize (K + 7) / 8 = q at *
  have e : 160 + 44 * (4 * (2 * q + 2 + 2)) + 2 * (4 * (2 * q + 2 + 2)) = 368 * q + 896 := by omega
  rw [e]
  have : 368 * q ≤ 46 * (K + 7) := by omega
  omega

theorem wOf_val (x : BitVec 64) (hx : x.toNat ≤ 1024) :
    (x + BitVec.ofNat 64 7) >>> 3 <<< 1 + BitVec.ofNat 64 2 = BitVec.ofNat 64 (ww x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (x + BitVec.ofNat 64 7).toNat = x.toNat + 7 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 7 < 2 ^ 64 by decide),
      Nat.mod_eq_of_lt (by omega)]
  have h2 : ((x + BitVec.ofNat 64 7) >>> 3).toNat = (x.toNat + 7) / 8 := by
    rw [BitVec.toNat_ushiftRight, h1, Nat.shiftRight_eq_div_pow]
  have h3 : ((x + BitVec.ofNat 64 7) >>> 3 <<< 1).toNat = 2 * ((x.toNat + 7) / 8) := by
    rw [BitVec.toNat_shiftLeft, h2, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
  rw [BitVec.toNat_add, h3, BitVec.toNat_ofNat, BitVec.toNat_ofNat]

theorem stride_val (w : Nat) :
    (BitVec.ofNat 64 w + BitVec.ofNat 64 2) <<< 2 = BitVec.ofNat 64 (KeyWorkspace.S w) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, KeyWorkspace.S]
  omega

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
theorem save_ok {s0 : State} (h : rvP.pre s0) {rest : List Instr} {Q : State → Prop}
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
    have := hp.k64; simp only [KeyWorkspace.S, ww]; omega
  rw [saveStores_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = rEntryMem s0) ?_ (by decide)) fun t ⟨m, kt⟩ => ?_
  · prun [hs.st (d := sv (kK s0)) (n := 8) (by omega), hs.st (d := sv (kK s0) + 8) (n := 8) (by omega),
      hs.st (d := sv (kK s0) + 16) (n := 8) (by omega), hs.st (d := sv (kK s0) + 24) (n := 8) (by omega),
      hs.st (d := sv (kK s0) + 32) (n := 8) (by omega), hs.st (d := sv (kK s0) + 40) (n := 8) (by omega),
      hs.st (d := sv (kK s0) + 48) (n := 8) (by omega), hs.st (d := sv (kK s0) + 56) (n := 8) (by omega),
      hs.st (d := sv (kK s0) + 64) (n := 8) (by omega), hs.st (d := sv (kK s0) + 72) (n := 8) (by omega),
      hs.st (d := sv (kK s0) + 80) (n := 8) (by omega), hs.st (d := sv (kK s0) + 88) (n := 8) (by omega),
      hs.st (d := sv (kK s0) + 96) (n := 8) (by omega), hs.st (d := sv (kK s0) + 104) (n := 8) (by omega),
      hs.st (d := sv (kK s0) + 112) (n := 8) (by omega), hs.st (d := sv (kK s0) + 120) (n := 8) (by omega),
      hs.st (d := sv (kK s0) + 128) (n := 8) (by omega), hs.st (d := sv (kK s0) + 136) (n := 8) (by omega), off_add]
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
    fun m d v h1 h2 => writeW_outside m (rvB s0) (d := d) v (by omega) x (by omega)
  simp only [rEntryMem]
  rw [o _ (sv (kK s0) + 136) _ (by omega) (by omega), o _ (sv (kK s0) + 128) _ (by omega) (by omega), o _ (sv (kK s0) + 120) _ (by omega) (by omega), o _ (sv (kK s0) + 112) _ (by omega) (by omega), o _ (sv (kK s0) + 104) _ (by omega) (by omega), o _ (sv (kK s0) + 96) _ (by omega) (by omega), o _ (sv (kK s0) + 88) _ (by omega) (by omega), o _ (sv (kK s0) + 80) _ (by omega) (by omega), o _ (sv (kK s0) + 72) _ (by omega) (by omega), o _ (sv (kK s0) + 64) _ (by omega) (by omega), o _ (sv (kK s0) + 56) _ (by omega) (by omega), o _ (sv (kK s0) + 48) _ (by omega) (by omega), o _ (sv (kK s0) + 40) _ (by omega) (by omega), o _ (sv (kK s0) + 32) _ (by omega) (by omega), o _ (sv (kK s0) + 24) _ (by omega) (by omega), o _ (sv (kK s0) + 16) _ (by omega) (by omega), o _ (sv (kK s0) + 8) _ (by omega) (by omega), o _ (sv (kK s0)) _ (by omega) (by omega)]

theorem rEntryMem_saved (s0 : State) (hb : sv (kK s0) + 144 ≤ 2 ^ 64) :
    ∀ i < 18, (rEntryMem s0).readW (off (rvB s0) (sv (kK s0) + 8 * i)) 64 = s0.gpr (savedReg i) := by
  intro i hi
  simp only [rEntryMem]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := omega) only [savedReg, Nat.mul_zero, Nat.add_zero, Nat.reduceMul, CrtValues.readW_sep,
    Mem.readW_writeW_self64, List.getD_cons_zero, List.getD_cons_succ]

/-- What every stage keeps of the initial state. -/
structure RBase (s0 s : State) : Prop where
  pre : rvP.pre s0
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
  have := (rv_kpre h.pre).k64; simp only [KeyWorkspace.S, ww]; omega

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
      by have := ho r hr; dsimp only; omega⟩),
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
    dsimp only; omega

/-- Memory outside the working space is the initial state's. -/
theorem RBase.frame {s0 s : State} (h : RBase s0 s) : ∀ x, rvZ s0 ≤ ofs (rvB s0) x → s.mem x = s0.mem x := by
  intro x hx
  have := h.svZ; have := h.s72; have := h.nowrap
  rw [h.mem x (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; dsimp only; omega)]
  exact rEntryMem_outside s0 (by omega) x (Or.inr (by omega))

/-- The saved registers. -/
theorem RBase.saved {s0 s : State} (h : RBase s0 s) :
    ∀ i < 18, s.mem.readW (off (rvB s0) (sv (kK s0) + 8 * i)) 64 = s0.gpr (savedReg i) := by
  intro i hi
  have := h.svZ; have := h.s72; have := h.nowrap
  rw [← rEntryMem_saved s0 (by omega) i hi]
  refine Mem.readW_congr fun b hb => h.mem _ fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  dsimp only
  rw [ofs_off (rvB s0) (by omega)]
  omega

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
      congr 2; omega]
  exact Offset.contains_base _ (by omega) (by omega)

/-- What the restore needs: the saved registers, the base and the stride. -/
structure RFin (s0 t : State) : Prop where
  pre : rvP.pre s0
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
    have := (rv_kpre h.pre).k64; simp only [KeyWorkspace.S, ww]; omega
  refine ⟨h.pre, k.sp.trans h.sp, k.lr.trans h.lr, k.rd.trans h.rd, k.wr.trans h.wr, (k.gpr _ h31).trans h.r31,
    (k.gpr _ h30).trans h.r30, fun i hi => ?_⟩
  rw [← h.saved i hi]
  refine Mem.readW_congr fun b hb => o _ ?_
  rw [ofs_off (rvB s0) (by omega)]
  omega

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
    have := hp.k64; simp only [KeyWorkspace.S, ww]; omega
  refine saveBase_ok (b := .r31) (w := ww (kK s0)) (by decide) (by decide) (by decide) h.r31 h.r30 ?_
  rw [show (List.range 18).map (fun i => Instr.load .d (savedReg i) .r11 (8 * i)) =
    [.load .d .r14 .r11 0, .load .d .r15 .r11 8, .load .d .r16 .r11 16, .load .d .r17 .r11 24, .load .d .r18 .r11 32, .load .d .r19 .r11 40, .load .d .r20 .r11 48, .load .d .r21 .r11 56, .load .d .r22 .r11 64, .load .d .r23 .r11 72, .load .d .r24 .r11 80, .load .d .r25 .r11 88, .load .d .r26 .r11 96, .load .d .r27 .r11 104, .load .d .r28 .r11 112, .load .d .r29 .r11 120, .load .d .r30 .r11 128, .load .d .r31 .r11 136] from rfl]
  refine WP.mono (WP.keep [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31] (Q := fun u => ((u.gpr .r14 = s0.gpr .r14 ∧ u.gpr .r15 = s0.gpr .r15 ∧ u.gpr .r16 = s0.gpr .r16 ∧ u.gpr .r17 = s0.gpr .r17 ∧ u.gpr .r18 = s0.gpr .r18 ∧ u.gpr .r19 = s0.gpr .r19 ∧ u.gpr .r20 = s0.gpr .r20 ∧ u.gpr .r21 = s0.gpr .r21 ∧ u.gpr .r22 = s0.gpr .r22 ∧ u.gpr .r23 = s0.gpr .r23 ∧ u.gpr .r24 = s0.gpr .r24 ∧ u.gpr .r25 = s0.gpr .r25 ∧ u.gpr .r26 = s0.gpr .r26 ∧ u.gpr .r27 = s0.gpr .r27 ∧ u.gpr .r28 = s0.gpr .r28 ∧ u.gpr .r29 = s0.gpr .r29 ∧ u.gpr .r30 = s0.gpr .r30 ∧ u.gpr .r31 = s0.gpr .r31) ∧ u.mem = t.mem)) ?_ (by decide))
    fun u ⟨q, k⟩ => ⟨q, ((Keep.write _ _ _).trans k).mono⟩
  prun [hs.ld (d := sv (kK s0)) (n := 8) (by omega), hs.ld (d := sv (kK s0) + 8) (n := 8) (by omega),
      hs.ld (d := sv (kK s0) + 16) (n := 8) (by omega), hs.ld (d := sv (kK s0) + 24) (n := 8) (by omega),
      hs.ld (d := sv (kK s0) + 32) (n := 8) (by omega), hs.ld (d := sv (kK s0) + 40) (n := 8) (by omega),
      hs.ld (d := sv (kK s0) + 48) (n := 8) (by omega), hs.ld (d := sv (kK s0) + 56) (n := 8) (by omega),
      hs.ld (d := sv (kK s0) + 64) (n := 8) (by omega), hs.ld (d := sv (kK s0) + 72) (n := 8) (by omega),
      hs.ld (d := sv (kK s0) + 80) (n := 8) (by omega), hs.ld (d := sv (kK s0) + 88) (n := 8) (by omega),
      hs.ld (d := sv (kK s0) + 96) (n := 8) (by omega), hs.ld (d := sv (kK s0) + 104) (n := 8) (by omega),
      hs.ld (d := sv (kK s0) + 112) (n := 8) (by omega), hs.ld (d := sv (kK s0) + 120) (n := 8) (by omega),
      hs.ld (d := sv (kK s0) + 128) (n := 8) (by omega), hs.ld (d := sv (kK s0) + 136) (n := 8) (by omega), off_add, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17]
  exact e0

end VG.Proof.Rsa.PPC64LE.Recover
