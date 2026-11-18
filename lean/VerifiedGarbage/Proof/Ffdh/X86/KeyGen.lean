module

public import VerifiedGarbage.Proof.Ffdh.X86.CheckPrivate
import VerifiedGarbage.Proof.Ffdh.Power
public import VerifiedGarbage.Impl.Ffdh.X86.KeyGen
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Export
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Import
import VerifiedGarbage.Proof.Ffdh.X86.Checks
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Dsa.PackedBytes
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Ctx
public import VerifiedGarbage.Proof.Ffdh.X86.Ops
public import VerifiedGarbage.Proof.Ffdh.X86.Stages
import VerifiedGarbage.Proof.Ffdh.ScanAt
public import VerifiedGarbage.Proof.Ffdh.X86.KeyScan
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Powers
import VerifiedGarbage.Proof.Dsa.X86.StackArgument
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.In
public import VerifiedGarbage.Proof.Bignum.X86.CrtValue
public import VerifiedGarbage.Proof.Ffdh.KeyScalar
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Spec.Dsa

/-! ### `Ffdh.X86.KeyCut`, which this module and modules that import it used -/

section

/-!
# FFDH key generation on i686: the random octets cut to the bound

`cutStep` writes octet `j` of `x`: zero before octet `ld`, `rand`'s and'ed
with the mask `t` at it, `rand`'s after it, without a branch; after every
octet, `x` holds `KeyScalar.cut rand ld t` (`cut_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.KeyCut

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86 VG.Proof.Ffdh
open VG.Proof.Ffdh.X86.KeyScan (upd_get sbb_self cmask_not cmask_and sel word_room count_loop bytesAt_getD)
open VG.Impl.Ffdh.X86

/-- The mask of octet `j`. -/
def cutMask (j ld : Nat) (tt : Byte) : BitVec 32 :=
  if j < ld then 0 else if j = ld then tt.setWidth 32 else 0xFF

/-- The carry of `x + 0xFFFFFFFF`: whether `x` is nonzero. -/
theorem carry_ne32 (x : BitVec 32) :
    decide (2 ^ 32 ≤ x.toNat + (0xFFFFFFFF : BitVec 32).toNat) = (x != 0) := by
  by_cases h : x = 0
  · subst h; decide
  · have : x.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    rw [show (x != 0) = true from bne_iff_ne.mpr h]
    exact decide_eq_true (by change 2 ^ 32 ≤ x.toNat + 4294967295; omega_arith)

theorem xor_ofNat_ne {j ld : Nat} (hj : j < 2 ^ 32) (hl : ld < 2 ^ 32) :
    (BitVec.ofNat 32 j ^^^ BitVec.ofNat 32 ld != 0) = !decide (j = ld) := by
  by_cases e : j = ld
  · subst e; simp
  · have : BitVec.ofNat 32 j ^^^ BitVec.ofNat 32 ld ≠ 0 := by
      intro z
      have := congrArg BitVec.toNat (BitVec.xor_eq_zero_iff.mp z)
      simp only [BitVec.toNat_ofNat] at this
      omega_arith
    rw [show (BitVec.ofNat 32 j ^^^ BitVec.ofNat 32 ld != 0) = true from bne_iff_ne.mpr this, decide_eq_false e]
    rfl

/-- The cut octet, from the mask. -/
theorem cut_byte (rb tt : Byte) (j ld : Nat) :
    ((rb.setWidth 32 &&& cutMask j ld tt).setWidth 8) =
      if j < ld then 0 else if j = ld then rb &&& tt else rb := by
  unfold cutMask
  split
  · simp
  · split
    · ext i hi; simp
    · ext i hi; simp
      have all : ∀ i (h : i < 8), (255#8)[i] = true := by decide
      exact fun _ => all i hi

/-! ## One octet -/

def cutA : List Instr :=
  [.mov .eax (.reg .ecx), .alu .cmp .eax (.mem (sc ldOff)), .alu .sbb .edx (.reg .edx),
    .alu .xor .eax (.mem (sc ldOff)), .alu .add .eax (.imm 0xFFFFFFFF), .alu .sbb .ebp (.reg .ebp),
    .mov .eax (.mem (sc tOff)), .alu .xor .eax (.imm 0xFF), .alu .and .eax (.reg .ebp), .alu .xor .eax (.mem (sc tOff)),
    .alu .xor .edx (.imm 0xFFFFFFFF), .alu .and .eax (.reg .edx)]

def cutB : List Instr := [.movzx8 .edx ⟨.esi, 0⟩, .alu .and .edx (.reg .eax), .store8 ⟨.ebx, 0⟩ .dl]

def cutC : List Instr :=
  [.alu .add .esi (.imm 1), .alu .add .ebx (.imm 1), .alu .add .ecx (.imm 1),
    .mov .eax (.mem (PublicRt.argAt 0 3)), .alu .cmp .ecx (.reg .eax)]

theorem cutStep_eq : GenerateKey.cutStep = cutA ++ (cutB ++ cutC) := rfl

section
variable {s : State} {base : Addr} {bytes : Nat}

theorem cutA_ok (hs : Scr s base bytes) (r24 : ldOff + 4 ≤ bytes) (r28 : tOff + 4 ≤ bytes) {j ld : Nat}
    {tt : Byte} (hc : s.gpr .ecx = BitVec.ofNat 32 j) (hj : j < 2 ^ 32)
    (hld : s.mem.readW (off base ldOff) 32 = BitVec.ofNat 32 ld) (hl : ld < 2 ^ 32)
    (ht : s.mem.readW (off base tOff) 32 = tt.setWidth 32) :
    WP isa (.block cutA) s fun u => u.gpr .eax = cutMask j ld tt ∧ u.mem = s.mem ∧ Keeps [.eax, .edx, .ebp] s u := by
  refine wp_movS rfl fun u1 a1 _ => ?_
  have k1 : Keeps [.eax, .edx, .ebp] s u1 := a1.keeps.mono (by decide)
  have rd (d : Nat) (hd : d + 4 ≤ bytes) {u : State} (k : Keeps [.eax, .edx, .ebp] s u) (m : u.mem = s.mem) :
      readSrc u (.mem (sc d)) = some (s.mem.readW (off base d) 32) := by
    rw [readSrc_sc (hs.of_keeps k (by decide)) hd, m]
  refine VG.Proof.Bignum.X86.CrtRt.wp_cmpC (rd ldOff r24 k1 a1.mem) fun u2 f2 c2 => ?_
  refine wp_sbbS rfl c2 fun u3 a3 _ => ?_
  have k3 := (k1.widen (f2.keeps [])).widen a3.keeps
  have m3 : u3.mem = s.mem := by rw [a3.mem, f2.mem, a1.mem]
  refine wp_logicS (.inr rfl) (rd ldOff r24 k3 m3) fun u4 a4 => ?_
  refine wp_addS rfl fun u5 a5 c5 => ?_
  refine wp_sbbS rfl c5 fun u6 a6 _ => ?_
  have k6 := ((k3.widen a4.keeps).widen a5.keeps).widen a6.keeps
  have m6 : u6.mem = s.mem := by rw [a6.mem, a5.mem, a4.mem, m3]
  refine wp_movS (rd tOff r28 k6 m6) fun u7 a7 _ => ?_
  refine wp_logicS (.inr rfl) rfl fun u8 a8 => ?_
  refine wp_logicS (.inl rfl) rfl fun u9 a9 => ?_
  have k9 := ((k6.widen a7.keeps).widen a8.keeps).widen a9.keeps
  have m9 : u9.mem = s.mem := by rw [a9.mem, a8.mem, a7.mem, m6]
  refine wp_logicS (.inr rfl) (rd tOff r28 k9 m9) fun u10 a10 => ?_
  refine wp_logicS (.inr rfl) rfl fun u11 a11 => ?_
  refine wp_logicS (.inl rfl) rfl fun t a12 => WP.block_nil ⟨?_, ?_, ((k9.widen a10.keeps).widen a11.keeps).widen
    a12.keeps⟩
  · have e2 : u2.gpr = u1.gpr := f2.gpr
    simp only [upd_get a12, upd_get a11, upd_get a10, upd_get a9, upd_get a8, upd_get a7, upd_get a6, upd_get a5,
      upd_get a4, upd_get a3, e2, upd_get a1, reduceCtorEq, ite_true, ite_false, hc, ht, hld, KeyScan.sbb_self]
    rw [carry_ne32, xor_ofNat_ne hj hl, KeyScan.cmask_not]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hl]
    unfold cutMask
    by_cases h1 : j < ld
    · simp [h1, cmask]
    · by_cases h2 : j = ld
      · subst h2; simp [cmask]
        rw [show (4294967295#32) = BitVec.allOnes 32 from rfl, BitVec.and_allOnes]
      · simp [h1, h2, cmask]
        rw [show (4294967295#32) = BitVec.allOnes 32 from rfl, BitVec.and_allOnes, BitVec.and_allOnes,
          BitVec.xor_assoc, BitVec.xor_comm 255#32, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · rw [a12.mem, a11.mem, a10.mem, m9]

/-- `mov byte [m], r`. -/
theorem wp_store8 {is : List Instr} {Q : State → Prop} {m : MemOp} {r : Reg8} {a : Addr} (ha : s.ea m = a)
    (hw : InRegions s.wr a 1) (k : ∀ t, Mupd s t (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) t Q) :
    WP isa (.block (.store8 m r :: is)) s Q :=
  cons (s' := { s with mem := s.mem.writeW a ((s.gpr r.reg).setWidth 8) })
    (by simp only [exec, State.store8, ha, hw, ↓reduceIte]) (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

theorem cutB_ok {ar ax : Addr} (har : s.ea ⟨.esi, 0⟩ = ar) (hr : InRegions (s.rd ++ s.wr) ar 1)
    (hax : s.ea ⟨.ebx, 0⟩ = ax) (hx : InRegions s.wr ax 1) :
    WP isa (.block cutB) s fun u =>
      u.mem = s.mem.writeW ax (((s.mem ar).setWidth 32 &&& s.gpr .eax).setWidth 8) ∧ Keeps [.edx] s u := by
  refine KeyScan.wp_movzx8 har hr fun u1 a1 => ?_
  refine wp_logicS (.inl rfl) rfl fun u2 a2 => ?_
  have k2 : Keeps [.edx] s u2 := a1.keeps.widen a2.keeps
  refine wp_store8 (a := ax) (by change addr (u2.gpr .ebx) 0 = ax; rw [k2.1 _ (by decide)]; exact hax)
    (by rw [k2.2.2]; exact hx) fun t m3 => WP.block_nil ⟨?_, k2.widen (m3.keeps [])⟩
  rw [m3.mem, a2.mem, a1.mem]
  simp only [upd_get a2, upd_get a1, reduceCtorEq, ite_true, ite_false]
  rfl

theorem cutC_ok {L : BitVec 32} (hL : readSrc s (.mem (PublicRt.argAt 0 3)) = some L) :
    WP isa (.block cutC) s fun u =>
      u.gpr .esi = s.gpr .esi + 1 ∧ u.gpr .ebx = s.gpr .ebx + 1 ∧ u.gpr .ecx = s.gpr .ecx + 1 ∧
        u.zf = some (s.gpr .ecx + 1 - L == 0) ∧ u.mem = s.mem ∧ Keeps [.esi, .ebx, .ecx, .eax] s u := by
  refine wp_addS rfl fun u1 a1 _ => ?_
  refine wp_addS rfl fun u2 a2 _ => ?_
  refine wp_addS rfl fun u3 a3 _ => ?_
  have k3 : Keeps [.esi, .ebx, .ecx, .eax] s u3 := ((a1.keeps.mono (by decide)).widen a2.keeps).widen a3.keeps
  refine wp_movS ((argument_keep k3 (by decide) (by rw [a3.mem, a2.mem, a1.mem]) 3).trans hL) fun u4 a4 _ => ?_
  refine wp_cmpS rfl fun t f z => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, (k3.widen a4.keeps).widen (f.keeps [])⟩
  · simp only [f.gpr, upd_get a4, upd_get a3, upd_get a2, upd_get a1, reduceCtorEq, ite_true, ite_false]
  · simp only [f.gpr, upd_get a4, upd_get a3, upd_get a2, upd_get a1, reduceCtorEq, ite_true, ite_false]
  · simp only [f.gpr, upd_get a4, upd_get a3, upd_get a2, upd_get a1, reduceCtorEq, ite_true, ite_false]
  · rw [z]; simp only [upd_get a4, upd_get a3, upd_get a2, upd_get a1, reduceCtorEq, ite_true, ite_false]
  · rw [f.mem, a4.mem, a3.mem, a2.mem, a1.mem]

end

/-! ## The loop -/

section
variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- The inputs through a write of a region apart from the working space and the arguments' frame. -/
theorem in_keepOut (h : In Ex base bytes len args s) {t : State} {regs : List Reg} (K : Keeps regs s t)
    (di : .edi ∉ regs) (sp : .esp ∉ regs) {r : Region} (F : Frame [r] s.mem t.mem)
    (hf : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 76⟩ r) : In Ex base bytes len args t := by
  have top := h.top
  refine ⟨h.scratch.of_keeps K di sp, h.lower, h.upper, fun i hi => ⟨(h.stack i hi).stack.keep K sp, ?_⟩,
    h.outLen, by rw [K.1 _ sp]; exact h.room, by rw [K.1 _ sp]; exact h.top, h.need, h.hbase, h.hbytes,
    by rw [K.2.1, K.2.2]; exact h.extra⟩
  have P : VG.Proof.Dsa.X86.stackAddress t i = VG.Proof.Dsa.X86.stackAddress s i := by
    simp only [VG.Proof.Dsa.X86.stackAddress, K.1 _ sp]
  have E : VG.Proof.Dsa.X86.stackAddress s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
    addr_eq (by omega_arith)
  refine Eq.trans ?_ (h.stack i hi).value
  unfold VG.Proof.Dsa.X86.stackValue
  rw [P]
  refine F.readW (r := ⟨VG.Proof.Dsa.X86.stackAddress s i, 4⟩) (Region.contains_self _ _) (fun r' hr' => ?_)
    (by decide)
  obtain rfl := List.mem_singleton.mp hr'
  rw [E]
  exact hf.sub_left (Offset.sub_base _ (by omega_arith))

/-- Where `rand` and `x` are. -/
structure CutGeo (base : Addr) (bytes len : Nat) (rp xp sp : BitVec 32) (rd wr : List Region) : Prop where
  rfit : rp.toNat + len ≤ 2 ^ 32
  xfit : xp.toNat + len ≤ 2 ^ 32
  rrd : InRegions (rd ++ wr) (byteAddr rp) len
  xwr : InRegions wr (byteAddr xp) len
  apart : Region.Disjoint ⟨byteAddr rp, len⟩ ⟨byteAddr xp, len⟩
  xWs : Region.Disjoint ⟨byteAddr xp, len⟩ ⟨base, bytes⟩
  xFrame : Region.Disjoint ⟨sp.setWidth 64, 76⟩ ⟨byteAddr xp, len⟩

/-- Before octet `j`. -/
structure CutInv (s₀ : State) (rp xp : BitVec 32) (rb : List Byte) (ld : Nat) (tt : Byte) (j : Nat)
    (t : State) : Prop where
  frame : Frame [⟨byteAddr xp, len⟩] s₀.mem t.mem
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s₀ t
  esi : t.gpr .esi = rp + BitVec.ofNat 32 j
  ebx : t.gpr .ebx = xp + BitVec.ofNat 32 j
  ecx : t.gpr .ecx = BitVec.ofNat 32 j
  out : ∀ i < j, t.mem (byteAddr xp + BitVec.ofNat 64 i) = (KeyScalar.cut rb ld tt).getD i 0

theorem byte_write_self (m : Mem) (a : Addr) (v : BitVec 8) : (m.writeW a v) a = v := by
  simp only [Mem.writeW, Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.mul_zero]
  apply BitVec.eq_of_toNat_eq
  simp

theorem ea_at {u : State} {r : Reg} {p : BitVec 32} {j n : Nat} (hr : u.gpr r = p + BitVec.ofNat 32 j)
    (hj : j < n) (fit : p.toNat + n ≤ 2 ^ 32) : u.ea ⟨r, 0⟩ = byteAddr p + BitVec.ofNat 64 j := by
  change addr (u.gpr r) 0 = _
  rw [hr, addr_eq (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith), BitVec.add_zero]
  exact addr_eq (by omega_arith)

theorem cut_getD {r : List Byte} {ld : Nat} (tt : Byte) (h : ld < r.length) {i : Nat} (hi : i < r.length) :
    (KeyScalar.cut r ld tt).getD i 0 = if i < ld then 0 else if i = ld then r.getD i 0 &&& tt else r.getD i 0 := by
  rw [getD_of (by rw [KeyScalar.cut_length tt h]; exact hi), KeyScalar.cut_get tt h hi,
    getD_of hi]

theorem cutStep_ok (h₀ : In Ex base bytes len args s) {t : State} {rp xp : BitVec 32} {ld j : Nat} {tt : Byte}
    (hj : j < len) (hld : ld < len) (C : CutGeo base bytes len rp xp (s.gpr .esp) s.rd s.wr)
    (h3 : args 3 = BitVec.ofNat 32 len)
    (wld : s.mem.readW (off base ldOff) 32 = BitVec.ofNat 32 ld)
    (wt : s.mem.readW (off base tOff) 32 = tt.setWidth 32)
    (I : CutInv (len := len) s rp xp (Spec.Rsa.bytesAt s.mem (byteAddr rp) len) ld tt j t) :
    WP isa (.block GenerateKey.cutStep) t fun u =>
      CutInv (len := len) s rp xp (Spec.Rsa.bytesAt s.mem (byteAddr rp) len) ld tt (j + 1) u ∧
        u.zf = some (decide (j + 1 = len)) := by
  have h := in_keepOut h₀ I.keeps (by decide) (by decide) I.frame C.xFrame
  have lw := h.lower
  have up := h.upper
  have rf := C.rfit
  have xf := C.xfit
  have r24 := word_room h (d := ldOff) (by decide)
  have r28 := word_room h (d := tOff) (by decide)
  have ws : ∀ d, d + 4 ≤ 32 → t.mem.readW (off base d) 32 = s.mem.readW (off base d) 32 := fun d hd =>
    I.frame.readW (r := ⟨base, bytes⟩) (Scr.contains h.scratch.nowrap (by have := word_room h hd; omega_arith))
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact C.xWs.symm) (by decide)
  rw [cutStep_eq]
  refine WP.block_append (WP.mono (cutA_ok (ld := ld) (tt := tt) h.scratch r24 r28 I.ecx (by omega_arith)
    (by rw [ws _ (by decide), wld]) (by omega_arith) (by rw [ws _ (by decide), wt])) fun uA ⟨eA, mA, kA⟩ => ?_)
  have esiA : uA.gpr .esi = rp + BitVec.ofNat 32 j := by rw [kA.1 _ (by decide), I.esi]
  have ebxA : uA.gpr .ebx = xp + BitVec.ofNat 32 j := by rw [kA.1 _ (by decide), I.ebx]
  have rdA : InRegions (uA.rd ++ uA.wr) (byteAddr rp + BitVec.ofNat 64 j) 1 := by
    rw [kA.2.1, kA.2.2, I.keeps.2.1, I.keeps.2.2]; exact VG.CallLay.inRegions_sub C.rrd (by omega_arith) (by omega_arith)
  have wrA : InRegions uA.wr (byteAddr xp + BitVec.ofNat 64 j) 1 := by
    rw [kA.2.2, I.keeps.2.2]; exact VG.CallLay.inRegions_sub C.xwr (by omega_arith) (by omega_arith)
  refine WP.block_append (WP.mono (cutB_ok (ea_at esiA hj rf) rdA (ea_at ebxA hj xf) wrA)
    fun uB ⟨mB, kB⟩ => ?_)
  have FB : Frame [⟨byteAddr xp, len⟩] s.mem uB.mem := by
    rw [mB, mA]
    exact I.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
  have kB' : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s uB := (I.keeps.widen kA).widen kB
  have hB := in_keepOut h₀ kB' (by decide) (by decide) FB C.xFrame
  refine WP.mono (cutC_ok (L := BitVec.ofNat 32 len) (by rw [← h3]; exact (hB.stack 3 (by decide)).readSrc))
    fun u ⟨e1, e2, e3, z, mu, ku⟩ => ?_
  have e1j : BitVec.ofNat 32 j + 1 = BitVec.ofNat 32 (j + 1) := by rw [BitVec.ofNat_add]; rfl
  have rb : uA.mem (byteAddr rp + BitVec.ofNat 64 j) = (Spec.Rsa.bytesAt s.mem (byteAddr rp) len).getD j 0 := by
    rw [mA, bytesAt_getD _ _ hj]
    refine I.frame _ fun r hr hc => ?_
    obtain rfl := List.mem_singleton.mp hr
    exact C.apart _ (Offset.contains_base _ (by omega_arith) (by omega_arith)) hc
  have hl : (Spec.Rsa.bytesAt s.mem (byteAddr rp) len).length = len := by simp [Spec.Rsa.bytesAt]
  refine ⟨⟨by rw [mu]; exact FB, kB'.widen ku, ?_, ?_, ?_, fun i hi => ?_⟩, ?_⟩
  · rw [e1, kB.1 _ (by decide), esiA, BitVec.add_assoc, e1j]
  · rw [e2, kB.1 _ (by decide), ebxA, BitVec.add_assoc, e1j]
  · rw [e3, kB.1 _ (by decide), kA.1 _ (by decide), I.ecx, e1j]
  · rw [mu, mB]
    by_cases e : i = j
    · subst e
      rw [byte_write_self, rb, eA, cut_byte, cut_getD tt (by rw [hl]; exact hld) (by rw [hl]; exact hj)]
    · rw [Mem.writeW, Mem.write_apply (by rw [Offset.sub_toNat' _ (by omega_arith) (by omega_arith)]; split <;> omega_arith), mA,
        I.out i (by omega_arith)]
  · rw [z, kB.1 _ (by decide), kA.1 _ (by decide), I.ecx, e1j]
    by_cases e : j + 1 = len
    · subst e; rw [BitVec.sub_self, decide_eq_true rfl]; rfl
    · rw [decide_eq_false e]
      refine congrArg some (beq_eq_false_iff_ne.mpr fun z => e ?_)
      have z' : BitVec.ofNat 32 (j + 1) = BitVec.ofNat 32 len := by
        have := BitVec.sub_eq_iff_eq_add.mp z; simpa using this
      have := congrArg BitVec.toNat z'
      simp only [BitVec.toNat_ofNat] at this
      omega_arith

/-- What the cut leaves: `x` holds the cut octets of `rand`, nothing else changed. -/
structure CutOut (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat)
    (args : Nat → BitVec 32) (s₀ : State) (ld : Nat) (tt : Byte) (u : State) : Prop where
  inp : In Ex base bytes len args u
  frame : Frame [⟨byteAddr (args 0), len⟩] s₀.mem u.mem
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s₀ u
  x : Spec.Rsa.bytesAt u.mem (byteAddr (args 0)) len =
    KeyScalar.cut (Spec.Rsa.bytesAt s₀.mem (byteAddr (args 10)) len) ld tt

theorem cut_ok (h : In Ex base bytes len args s) {ld : Nat} {tt : Byte} (hld : ld < len)
    (C : CutGeo base bytes len (args 10) (args 0) (s.gpr .esp) s.rd s.wr) (h3 : args 3 = BitVec.ofNat 32 len)
    (wld : s.mem.readW (off base ldOff) 32 = BitVec.ofNat 32 ld)
    (wt : s.mem.readW (off base tOff) 32 = tt.setWidth 32) :
    WP isa GenerateKey.cut s (CutOut Ex base bytes len args s ld tt) := by
  have lw := h.lower
  unfold GenerateKey.cut GenerateKey.cutInit
  refine WP.seq (wp_movS (h.stack 10 (by decide)).readSrc fun u1 a1 _ => ?_)
  refine wp_movS ((argument_keep a1.keeps (by decide) a1.mem 0).trans (h.stack 0 (by decide)).readSrc)
    fun u2 a2 _ => ?_
  refine wp_movS rfl fun u3 a3 _ => WP.block_nil ?_
  have k3 : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u3 :=
    ((a1.keeps.mono (by decide)).widen a2.keeps).widen a3.keeps
  have m3 : u3.mem = s.mem := by rw [a3.mem, a2.mem, a1.mem]
  have I0 : CutInv (len := len) s (args 10) (args 0) (Spec.Rsa.bytesAt s.mem (byteAddr (args 10)) len) ld tt 0 u3 :=
    ⟨by rw [m3]; exact Frame.refl _ _, k3,
      by simp only [upd_get a3, upd_get a2, upd_get a1, reduceCtorEq, ite_true, ite_false, BitVec.add_zero],
      by simp only [upd_get a3, upd_get a2, reduceCtorEq, ite_true, ite_false, BitVec.add_zero],
      by simp only [upd_get a3, ite_true]; rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  refine WP.mono (count_loop (n := len) (by omega_arith) _ (fun k hk v Iv => cutStep_ok h hk hld C h3 wld wt Iv) I0)
    fun u Iu => ⟨in_keepOut h Iu.keeps (by decide) (by decide) Iu.frame C.xFrame, Iu.frame, Iu.keeps, ?_⟩
  have hl : (Spec.Rsa.bytesAt s.mem (byteAddr (args 10)) len).length = len := by simp [Spec.Rsa.bytesAt]
  apply List.ext_getElem
  · rw [KeyScalar.cut_length _ (by rw [hl]; exact hld), hl]; simp [Spec.Rsa.bytesAt]
  · intro i h1 h2
    have hi : i < len := by simpa [Spec.Rsa.bytesAt] using h1
    rw [← getD_of h1, ← getD_of h2, bytesAt_getD _ _ hi, Iu.out i hi]

end

end VG.Proof.Ffdh.X86.KeyCut

end

end

/-!
# `vg_ffdh_generate_key` on i686: the key pair

`export_ok`: a wide slot's number, or zeros unless accepted, to an output.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.KeyGen

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86
open VG.Impl.Ffdh.X86

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- An output of `len` bytes at synthetic argument `p`. -/
structure OutAt (args : Nat → BitVec 32) (base : Addr) (bytes len p : Nat) (sp : BitVec 32) (wr : List Region) :
    Prop where
  fit : (args p).toNat + len ≤ 2 ^ 32
  wr : InRegions wr (byteAddr (args p)) len
  apart : Region.Disjoint ⟨base, bytes⟩ ⟨byteAddr (args p), len⟩
  frame : Region.Disjoint ⟨sp.setWidth 64, 76⟩ ⟨byteAddr (args p), len⟩
  below : Region.Disjoint ⟨byteAddr (args p), len⟩ (below sp 96)

theorem OutAt.keep {p : Nat} {sp : BitVec 32} {wr : List Region} (O : OutAt args base bytes len p sp wr) {t : State}
    {rs : List Reg} (e : s.wr = wr) (K : Keeps rs s t) : OutAt args base bytes len p sp t.wr := by
  rw [K.2.2, e]; exact O

/-- The working space through a write apart from it. -/
theorem out_val32 {r : Region} {m m' : Mem} (F : Frame [r] m m') (hr : Region.Disjoint ⟨base, bytes⟩ r)
    (nw : base.toNat + bytes ≤ 2 ^ 32) {d k : Nat} (hd : d + 4 * k ≤ bytes) :
    val32 m' base d k = val32 m base d k := by
  rw [← VG.Proof.Bignum.read_eq_val32, ← VG.Proof.Bignum.read_eq_val32]
  refine congrArg BitVec.toNat (F.read (r := ⟨off base d, 4 * k⟩) (Region.contains_self _ _) (fun r' hr' => ?_)
    (by omega_arith))
  obtain rfl := List.mem_singleton.mp hr'
  exact hr.sub_left (Offset.sub_base base (by omega_arith))

/-- The slots and the header through a write apart from the working space. -/
theorem kept_out (h : In Ex base bytes len args s) {r : Region} {m m' : Mem} (F : Frame [r] m m')
    (hr : Region.Disjoint ⟨base, bytes⟩ r) : Kept base len [] [] m m' := by
  have nw := h.scratch.nowrap
  have bl := h.bytes_lt
  have nd := h.need
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  refine ⟨fun j hj9 hj _ => ?_, fun d hd hd' _ _ => ?_⟩
  · have := slot_fit1 h (j := j) (by omega_arith)
    obtain bw := bc_eq_cwc len .wide
    rw [cb1] at this
    exact out_val32 F hr nw (by omega_arith)
  · rw [← w32_val32_one, ← w32_val32_one]
    exact out_val32 F hr nw (by omega_arith)

/-- The wide slot 19's number, or zeros unless the acceptance word is set, to the output at `p`. -/
theorem export_ok (h : In Ex base bytes len args s) {p l : Nat} (hp : p < 18) (hl : l < 18)
    (lenArg : args l = BitVec.ofNat 32 len) (O : OutAt args base bytes len p (s.gpr .esp) s.wr) {c : Bool}
    (hm : s.mem.readW (off base accOff) 32 = cmask c) {v : Nat}
    (hv : val32 s.mem base (lo len (.slot .wide 19)) (cwc len .wide) = v) (vlt : c = true → v < 2 ^ (8 * len)) :
    WP isa (exportTo p l) s fun t =>
      Spec.Rsa.bytesAt t.mem (byteAddr (args p)) len = Spec.Rsa.i2osp (if c then v else 0) len ∧
      t.gpr .eax = BitVec.ofNat 32 c.toNat ∧
      Frame (⟨byteAddr (args p), len⟩ :: frameR base (s.gpr .esp) (fR len)) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧ In Ex base bytes len args t ∧
      Kept base len [19] [] s.mem t.mem := by
  have ao : accOff = 8 := rfl
  have nb : numBase = 3336 := rfl
  have bl := h.bytes_lt
  obtain e19 := lo_wide len 19
  unfold exportTo
  refine maskResult_ok h (c := c) hm fun u₉ O₉ V₉ K₉ => ?_
  obtain S₉ : Step Ex base bytes len args s u₉ := Step.slot h (by decide) O₉ K₉
  refine WP.mono (writeTo_ok S₉.inp hp hl lenArg O.fit ((O.keep rfl S₉.keeps).wr) O.apart)
    fun t ⟨B, A, Ft, Kt⟩ => ⟨?_, ?_, ?_, S₉.keeps.trans (Kt.mono (by decide)),
      KeyCut.in_keepOut S₉.inp Kt (by decide) (by decide) Ft (by rw [S₉.esp]; exact O.frame),
      (kept_slot h (a := 19) O₉).trans ((kept_out S₉.inp Ft O.apart).mono)⟩
  · rw [V₉, hv] at B
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte] at B ⊢
      exact B (Nat.two_pow_pos _)
    · simp only [↓reduceIte] at B ⊢
      exact B (vlt rfl)
  · have a₉ : u₉.mem.readW (off base accOff) 32 = cmask c := by
      rw [show u₉.mem.readW (off base accOff) 32 = s.mem.readW (off base accOff) 32 from
        BitVec.eq_of_toNat_eq (O₉.w32 (d := accOff) (.inl (by omega_arith)) (by omega_arith)), hm]
    rw [A, a₉, cmask_and_one]
  · refine (S₉.frame.mono fun r hr => List.mem_cons_of_mem _ hr).trans (Ft.mono fun r hr => ?_)
    rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..

/-- The wide slot `a` copied into 19. -/
theorem copy19_ok (h : In Ex base bytes len args s) {a : Nat} (ha : a ≤ 18) :
    WP isa (copy (.slot .wide a) (.slot .wide 19) (one .wide)) s fun u => Step Ex base bytes len args s u ∧
      val32 u.mem base (lo len (.slot .wide 19)) (cwc len .wide) = sv s.mem base len .wide a ∧
      Kept base len [19] [] s.mem u.mem := by
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  obtain ea := lo_wide len a
  obtain e19 := lo_wide len 19
  have := Nat.mul_le_mul_right (st len .wide) ha
  refine WP.mono (copy_ok h (x := .slot .wide a) (d := .slot .wide 19) (one_ok .wide)
    (slot_fit1 h (by omega_arith)) (slot_fit1 h (by decide)) (by rw [cb1]; exact .inr (by omega_arith)))
    fun u ⟨O, V, K⟩ => ?_
  rw [cb1] at O
  rw [cw1] at V
  exact ⟨Step.slot h (by decide) O K, V, kept_slot h O⟩

/-- x and y (the wide slots 13 and 12), or zeros unless accepted, to the outputs at 0 and 8. -/
theorem outputs_ok (h : In Ex base bytes len args s) (Ox : OutAt args base bytes len 0 (s.gpr .esp) s.wr)
    (Oy : OutAt args base bytes len 8 (s.gpr .esp) s.wr) (h9 : args 9 = BitVec.ofNat 32 len)
    (xy : Region.Disjoint ⟨byteAddr (args 0), len⟩ ⟨byteAddr (args 8), len⟩) {c : Bool}
    (hm : w32 s.mem base accOff = (cmask c).toNat) {x y : Nat} (hx : sv s.mem base len .wide 13 = x)
    (hy : sv s.mem base len .wide 12 = y) (xlt : c = true → x < 2 ^ (8 * len)) (ylt : c = true → y < 2 ^ (8 * len)) :
    WP isa GenerateKey.outputs s fun t =>
      Spec.Rsa.bytesAt t.mem (byteAddr (args 0)) len = Spec.Rsa.i2osp (if c then x else 0) len ∧
      Spec.Rsa.bytesAt t.mem (byteAddr (args 8)) len = Spec.Rsa.i2osp (if c then y else 0) len ∧
      t.gpr .eax = BitVec.ofNat 32 c.toNat ∧
      Frame (⟨byteAddr (args 0), len⟩ :: ⟨byteAddr (args 8), len⟩ :: frameR base (s.gpr .esp) (fR len))
        s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have ao : accOff = 8 := rfl
  have nb : numBase = 3336 := rfl
  have acc {m : Mem} (e : w32 m base accOff = (cmask c).toNat) : m.readW (off base accOff) 32 = cmask c :=
    BitVec.eq_of_toNat_eq e
  unfold GenerateKey.outputs
  refine WP.seq (WP.mono (copy19_ok h (a := 13) (by decide)) fun u₁ ⟨S₁, V₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (export_ok S₁.inp (p := 0) (l := 1) (c := c) (by decide) (by decide) h.outLen
    (by rw [S₁.esp]; exact Ox.keep rfl S₁.keeps) (acc (by rw [k₁.word_eq]; exact hm)) (by rw [V₁, hx]) xlt)
    fun u₂ ⟨Bx, _, F₂, K₂, I₂, k₂⟩ => ?_)
  obtain S₁₂ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₂ := S₁.keeps.trans K₂
  refine WP.seq (WP.mono (copy19_ok I₂ (a := 12) (by decide)) fun u₃ ⟨S₃, V₃, k₃⟩ => ?_)
  obtain sp₃ : u₃.gpr .esp = s.gpr .esp := by rw [S₃.esp, K₂.1 _ (by decide), S₁.esp]
  refine WP.mono (export_ok S₃.inp (p := 8) (l := 9) (c := c) (by decide) (by decide) h9
    (by rw [sp₃]; exact Oy.keep rfl (S₁₂.trans S₃.keeps)) (acc (by rw [k₃.word_eq, k₂.word_eq, k₁.word_eq]; exact hm))
    (by rw [V₃, k₂.slot_eq, k₁.slot_eq, hy]) ylt) fun t ⟨By, A, F₄, K₄, _, _⟩ => ?_
  have sp₁ : u₁.gpr .esp = s.gpr .esp := S₁.esp
  obtain sp₂ : u₂.gpr .esp = s.gpr .esp := by rw [K₂.1 _ (by decide), sp₁]
  rw [sp₁] at F₂
  rw [sp₃] at F₄
  have F₃ := S₃.frame
  rw [sp₂] at F₃
  refine ⟨?_, By, A, ?_, (S₁₂.trans S₃.keeps).trans K₄⟩
  · rw [← Bx]
    have := h.upper
    refine frame_bytes ((F₃.mono fun r hr => List.mem_cons_of_mem _ hr).trans F₄) (fun r hr => ?_) (by omega_arith)
    rcases List.mem_cons.mp hr with rfl | hr
    · exact xy
    · rw [frameR, List.mem_cons, List.mem_map] at hr
      rcases hr with rfl | ⟨q, hq, rfl⟩
      · exact Ox.below
      · have := fR_fit h q hq
        exact Ox.apart.symm.sub_right (Offset.sub_base _ (by omega_arith))
  · have F₁ := S₁.frame
    refine ((F₁.mono fun r hr => ?_).trans (F₂.mono fun r hr => ?_)).trans
      ((F₃.mono fun r hr => ?_).trans (F₄.mono fun r hr => ?_))
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)

/-- The wide slot `a` copied into `b`. -/
theorem copyW_ok (h : In Ex base bytes len args s) {a b : Nat} (ha : a ≤ 19) (hb : b ≤ 19) (hab : a ≠ b) :
    WP isa (copy (.slot .wide a) (.slot .wide b) (one .wide)) s fun u => Step Ex base bytes len args s u ∧
      sv u.mem base len .wide b = sv s.mem base len .wide a ∧ Kept base len [b] [] s.mem u.mem := by
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  obtain ea := lo_wide len a
  obtain eb := lo_wide len b
  obtain apart : Apart (lo len (.slot .wide b)) (cb len (one .wide)) (lo len (.slot .wide a)) (cb len (one .wide)) := by
    rw [cb1]
    rcases Nat.lt_or_gt_of_ne hab with l | l
    · have := Nat.mul_le_mul_right (st len .wide) (Nat.succ_le_of_lt l); rw [Nat.succ_mul] at this
      exact .inr (by omega_arith)
    · have := Nat.mul_le_mul_right (st len .wide) (Nat.succ_le_of_lt l); rw [Nat.succ_mul] at this
      exact .inl (by omega_arith)
  refine WP.mono (copy_ok h (x := .slot .wide a) (d := .slot .wide b) (one_ok .wide)
    (slot_fit1 h (by omega_arith)) (slot_fit1 h (by omega_arith)) apart) fun u ⟨O, V, K⟩ => ?_
  rw [cb1] at O
  rw [cw1] at V
  exact ⟨Step.slot h (by omega_arith) O K, V, kept_slot h O⟩

/-- The tail up to the outputs, with the stage `pow` computing y into slot 6. -/
abbrev tailFrontWith (pow : Prog isa) : List (Prog isa) :=
  [pow, copy (.slot .wide 6) (.slot .wide 12) (one .wide), rangeMask 12, .block [.store (sc accOff) .ecx]]

/-- The status from the acceptance's low bit. -/
abbrev statusOf : List Instr :=
  [.alu .add .eax (.reg .eax), .mov .ecx (.imm 3), .alu .sub .ecx (.reg .eax), .mov .eax (.reg .ecx)]

/-- The tail with the stage `pow`. -/
abbrev tailWith (pow : Prog isa) : Prog isa :=
  Prog.chain (tailFrontWith pow) (.seq GenerateKey.outputs (.block statusOf))

/-- y (from the stage `pow`, `Y` in slot 6) into the wide slot 12, and its range into the acceptance
word. -/
theorem tailFrontWith_ok {pow : Prog isa} {Y : Nat} {ds : List Nat}
    (hpow : WP isa pow s fun u => Step Ex base bytes len args s u ∧ Kept base len [] ds s.mem u.mem ∧
      sv u.mem base len .wide 6 = Y) :
    WP isa (Prog.chain (tailFrontWith pow) (.block [])) s fun u =>
      Step Ex base bytes len args s u ∧ Kept base len [12] (ds ++ [maskOff, accOff]) s.mem u.mem ∧
      sv u.mem base len .wide 12 = Y ∧
      w32 u.mem base accOff = (cmask (decide (sv u.mem base len .wide 12 < sv s.mem base len .wide 15) &&
        decide (sv s.mem base len .wide 14 < sv u.mem base len .wide 12))).toNat := by
  have ao : accOff = 8 := rfl
  have mo : maskOff = 12 := rfl
  have nb : numBase = 3336 := rfl
  obtain m₁ : ∀ d ∈ ds, d ∈ ds ++ [maskOff, accOff] := fun d hd => List.mem_append_left _ hd
  obtain m₂ : ∀ d ∈ [maskOff], d ∈ ds ++ [maskOff, accOff] := fun d hd => by simp_all
  obtain m₃ : ∀ d ∈ [accOff], d ∈ ds ++ [maskOff, accOff] := fun d hd => by simp_all
  obtain m₀ : ∀ d ∈ ([] : List Nat), d ∈ ds ++ [maskOff, accOff] := fun d hd => by simp at hd
  refine WP.seq (WP.mono hpow fun u₁ ⟨S₁, k₁, Y₁⟩ => ?_)
  refine WP.seq (WP.mono (copyW_ok S₁.inp (a := 6) (b := 12) (by decide) (by decide) (by decide))
    fun u₂ ⟨S₂, V₂, k₂⟩ => ?_)
  refine WP.seq (WP.mono (rangeMask_ok S₂.inp (a := 12) (by decide)) fun u₃ ⟨I₃, e₃, O₃, K₃⟩ => ?_)
  obtain S₃ : Step Ex base bytes len args u₂ u₃ := Step.word S₂.inp (by decide) O₃ K₃
  obtain k₃ := kept_word S₂.inp (d := maskOff) (by decide) (by decide) O₃
  refine WP.seq (WP.mono (storeMask_ok I₃ (d := accOff) (by omega_arith) e₃) fun u₄ ⟨_, O₄, W₄, _, K₄⟩ =>
    WP.block_nil ?_)
  obtain S₄ : Step Ex base bytes len args u₃ u₄ := Step.word I₃ (by omega_arith) O₄ K₄
  obtain k₄ := kept_word I₃ (d := accOff) (by omega_arith) (by decide) O₄
  obtain kk : Kept base len [12] (ds ++ [maskOff, accOff]) s.mem u₄.mem :=
    (((k₁.mono (by simp) m₁).trans (k₂.mono (by simp) m₀)).trans (k₃.mono (by simp) m₂)).trans
      (k₄.mono (by simp) m₃)
  obtain v12 : sv u₄.mem base len .wide 12 = sv u₂.mem base len .wide 12 := by
    rw [k₄.slot_eq, k₃.slot_eq]
  refine ⟨((S₁.trans S₂).trans S₃).trans S₄, kk, ?_, ?_⟩
  · rw [v12, V₂, Y₁]
  · rw [W₄, v12, k₂.slot_eq (j := 15), k₂.slot_eq (j := 14), k₁.slot_eq (j := 15), k₁.slot_eq (j := 14)]

/-- The acceptance of `y`: its range. -/
abbrev accept (len p y : Nat) : Bool := decide (y < pm1 len p) && decide (1 < y)

theorem statusOf_ok {c : Bool} (he : s.gpr .eax = BitVec.ofNat 32 c.toNat) :
    WP isa (.block statusOf) s fun t => t.gpr .eax = BitVec.ofNat 32 (if c then 1 else 3) ∧ t.mem = s.mem ∧
      Keeps [.eax, .ecx] s t := by
  refine wp_addS rfl fun u1 a1 _ => wp_movS rfl fun u2 a2 _ => wp_subS rfl fun u3 a3 _ =>
    wp_movS rfl fun t a4 _ => WP.block_nil ⟨?_, ?_, ?_⟩
  · simp only [KeyScan.upd_get a4, KeyScan.upd_get a3, KeyScan.upd_get a2, KeyScan.upd_get a1, reduceCtorEq,
      ite_true, ite_false, he]
    cases c <;> rfl
  · rw [a4.mem, a3.mem, a2.mem, a1.mem]
  · exact (((a1.keeps.mono (by decide)).widen a2.keeps).widen a3.keeps).widen a4.keeps

/-- The tail with the stage `pow` computing y: y, its acceptance, x and y written (zeros unless accepted),
and `3 − 2 flag`. -/
theorem tailWith_ok (Ox : OutAt args base bytes len 0 (s.gpr .esp) s.wr)
    (Oy : OutAt args base bytes len 8 (s.gpr .esp) s.wr)
    (h9a : args 9 = BitVec.ofNat 32 len) (xy : Region.Disjoint ⟨byteAddr (args 0), len⟩ ⟨byteAddr (args 8), len⟩)
    {p x Y : Nat} (h13 : sv s.mem base len .wide 13 = x) (h14 : sv s.mem base len .wide 14 = 1)
    (h15 : sv s.mem base len .wide 15 = pm1 len p)
    (xlt : x < 2 ^ (8 * len)) (ylt : Y < 2 ^ (8 * len)) {pow : Prog isa} {ds : List Nat}
    (hpow : WP isa pow s fun u => Step Ex base bytes len args s u ∧ Kept base len [] ds s.mem u.mem ∧
      sv u.mem base len .wide 6 = Y) :
    WP isa (tailWith pow) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (if accept len p Y then 1 else 3) ∧
      Spec.Rsa.bytesAt t.mem (byteAddr (args 0)) len =
        Spec.Rsa.i2osp (if accept len p Y then x else 0) len ∧
      Spec.Rsa.bytesAt t.mem (byteAddr (args 8)) len =
        Spec.Rsa.i2osp (if accept len p Y then Y else 0) len ∧
      Frame (⟨byteAddr (args 0), len⟩ :: ⟨byteAddr (args 8), len⟩ :: frameR base (s.gpr .esp) (fR len))
        s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.chain_split (tailFrontWith_ok hpow) fun u ⟨Su, k, V12, W⟩ => ?_
  rw [V12, h15, h14] at W
  refine WP.seq (WP.mono (outputs_ok Su.inp (by rw [Su.esp]; exact Ox.keep rfl Su.keeps)
    (by rw [Su.esp]; exact Oy.keep rfl Su.keeps) h9a xy W (by rw [k.slot_eq, h13])
    V12 (fun _ => xlt) (fun _ => ylt)) fun w ⟨Bx, By, A, F, K⟩ => ?_)
  refine WP.mono (statusOf_ok A) fun t ⟨E, M, Kt⟩ => ⟨E, by rw [M]; exact Bx, by rw [M]; exact By, ?_,
    (Su.keeps.trans K).trans (Kt.mono (by decide))⟩
  rw [M, Su.esp] at *
  exact (Su.frame.mono fun r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)).trans F

/-! ## The bound's octets -/

theorem boundAt_eq {dlen : Nat} {rd wr : List Region} (G : DomGeo args base bytes len dlen rd wr) :
    KeyScan.boundAt args = args 2 + BitVec.ofNat 32 (2 * (dlen - 2 * len)) := by
  have dl := G.dl
  have up := G.upper
  unfold KeyScan.boundAt
  rw [G.e12, G.e3, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_arith) (by omega_arith),
    BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_arith) (by omega_arith), BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2; omega_arith

/-- The bound's octets are within the domain: q's, or p's. -/
theorem bound_geo {dlen : Nat} {sp : BitVec 32} {rd wr : List Region} (G : DomGeo args base bytes len dlen rd wr)
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below sp 96)) :
    KeyScan.BGeo base bytes len (KeyScan.boundAt args) sp rd wr := by
  have dl := G.dl
  have up := G.upper
  have fit := G.fit
  obtain ho : 2 * (dlen - 2 * len) + len ≤ dlen := by omega_arith
  obtain ea : byteAddr (KeyScan.boundAt args) = byteAddr (args 2) + BitVec.ofNat 64 (2 * (dlen - 2 * len)) := by
    rw [boundAt_eq G]; exact addr_eq (by omega_arith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [boundAt_eq G, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2 * _) (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  · rw [ea]; exact VG.CallLay.inRegions_sub G.rd ho (by omega_arith)
  · rw [ea]; exact G.apart.sub_left (Offset.sub_base _ ho)
  · rw [ea]; exact hb40.sub_left (Offset.sub_base _ ho)

theorem bound_bytes {dlen : Nat} {rd wr : List Region} (G : DomGeo args base bytes len dlen rd wr) (m : Mem) :
    Spec.Rsa.bytesAt m (byteAddr (KeyScan.boundAt args)) len =
      KeyScalar.bnd len (Spec.Rsa.bytesAt m (byteAddr (args 2)) dlen) := by
  have dl := G.dl
  have lw := G.lower
  have up := G.upper
  have fit := G.fit
  obtain ea : byteAddr (KeyScan.boundAt args) = byteAddr (args 2) + BitVec.ofNat 64 (2 * (dlen - 2 * len)) := by
    rw [boundAt_eq G]; exact addr_eq (by omega_arith)
  rw [ea]
  unfold KeyScalar.bnd
  rw [VG.Proof.Bignum.bytesAt_length]
  rcases dl with e | e
  · have : ¬ dlen = 3 * len := by omega_arith
    rw [ite_eq_right this, VG.Proof.Ffdh.take_bytesAt m _ (k := len) (dl := dlen) (by omega_arith), show 2 * (dlen - 2 * len) = 0 by omega_arith,
      BitVec.add_zero]
  · rw [ite_eq_left e, VG.Proof.Dsa.bytesAt_slice m _ (total := dlen) (offset := 2 * len) (len := len) (by omega_arith), show 2 * (dlen - 2 * len) = 2 * len by omega_arith]

/-! ## The scalar -/

/-- The domain's octets. -/
abbrev domOf (m : Mem) (args : Nat → BitVec 32) (dlen : Nat) : List Byte :=
  Spec.Rsa.bytesAt m (byteAddr (args 2)) dlen

/-- The scalar of `rand` cut at its octet `ld`, and'ed with `tt` there. -/
abbrev cutOf (m : Mem) (args : Nat → BitVec 32) (len ld : Nat) (tt : Byte) : Nat :=
  Spec.Rsa.os2ip (KeyScalar.cut (Spec.Rsa.bytesAt m (byteAddr (args 10)) len) ld tt)

/-- The body up to its branch on the scalar, with the stage `st` choosing the cut. -/
abbrev mainFrontWith (st : Prog isa) : List (Prog isa) :=
  [pSetup, load (.slot .wide 10) (one .wide) 4 5, st, GenerateKey.cut,
    load (.slot .wide 13) (one .wide) 0 1, CheckPrivate.bound, CheckPrivate.scalarMask, testMask]

/-- A component through a write of `x`, apart from the domain. -/
theorem comp_x {dlen : Nat} {rd wr : List Region} (G : DomGeo args base bytes len dlen rd wr)
    (domX : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ ⟨byteAddr (args 0), len⟩) {m m' : Mem}
    (F : Frame [⟨byteAddr (args 0), len⟩] m m') {k : Nat} (hk : k * len + len ≤ dlen) :
    comp m' args len k = comp m args len k := by
  have := G.fit
  unfold comp
  rw [frame_bytes F (fun r hr => by
    obtain rfl := List.mem_singleton.mp hr; exact domX.sub_left (Offset.sub_base _ hk)) (by omega_arith)]

theorem w32_ofNat {m : Mem} {d n : Nat} (h : w32 m base d = n) (hn : n < 2 ^ 32) :
    m.readW (off base d) 32 = BitVec.ofNat 32 n :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]; exact h)

/-- What the body's front leaves, for the scalar `xs`. -/
structure FrontW (Ex : List Region → List Region → Prop) (base : Addr) (bytes len dlen : Nat)
    (args : Nat → BitVec 32) (s : State) (xs : Nat) (u : State) : Prop where
  inp : In Ex base bytes len args u
  frame : Frame (⟨byteAddr (args 0), len⟩ :: frameR base (s.gpr .esp) (fR len)) s.mem u.mem
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u
  gate : Gate u (Spec.Ffdh.privateValid (CheckPrivate.params s.mem args len dlen) xs = false)
  v9 : sv u.mem base len .wide 9 = comp s.mem args len 0
  v10 : sv u.mem base len .wide 10 = comp s.mem args len 1
  v13 : sv u.mem base len .wide 13 = xs
  v14 : sv u.mem base len .wide 14 = 1
  v15 : sv u.mem base len .wide 15 = pm1 len (comp s.mem args len 0)
  v16 : ¬ dlen = 2 * len → sv u.mem base len .wide 16 = comp s.mem args len 2

/-- The front up to the bound, with the stage `st` choosing the cut. -/
abbrev prefixWith (st : Prog isa) : List (Prog isa) :=
  [pSetup, load (.slot .wide 10) (one .wide) 4 5, st, GenerateKey.cut, load (.slot .wide 13) (one .wide) 0 1]

/-- What the front leaves up to the bound, for the scalar `xs`. -/
structure PrefW (Ex : List Region → List Region → Prop) (base : Addr) (bytes len dlen : Nat)
    (args : Nat → BitVec 32) (s : State) (xs : Nat) (u : State) : Prop where
  inp : In Ex base bytes len args u
  frame : Frame (⟨byteAddr (args 0), len⟩ :: frameR base (s.gpr .esp) (fR len)) s.mem u.mem
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u
  v9 : sv u.mem base len .wide 9 = comp s.mem args len 0
  v10 : sv u.mem base len .wide 10 = comp s.mem args len 1
  v13 : sv u.mem base len .wide 13 = xs
  v14 : sv u.mem base len .wide 14 = 1
  v15 : sv u.mem base len .wide 15 = pm1 len (comp s.mem args len 0)
  q : ¬ dlen = 2 * len → comp u.mem args len 2 = comp s.mem args len 2

/-- What a stage choosing the cut leaves: the cut's first octet `ld` and its mask `tt` in the
header, which it alone changes. -/
structure CutPar (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat)
    (args : Nat → BitVec 32) (s : State) (ld : Nat) (tt : Byte) (u : State) : Prop where
  step : Step Ex base bytes len args s u
  kept : Kept base len [] [tbOff, foundOff, ldOff, tOff] s.mem u.mem
  ld : w32 u.mem base ldOff = ld
  t : w32 u.mem base tOff = tt.toNat

/-- The front up to the bound, with a stage choosing the cut at `ld` with the mask `tt`. -/
theorem prefixWith_ok (h : In Ex base bytes len args s) {dlen : Nat} (G : DomGeo args base bytes len dlen s.rd s.wr)
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below (s.gpr .esp) 96))
    (C : KeyCut.CutGeo base bytes len (args 10) (args 0) (s.gpr .esp) s.rd s.wr)
    (rWs : Region.Disjoint ⟨byteAddr (args 10), len⟩ ⟨base, bytes⟩)
    (r40 : Region.Disjoint ⟨byteAddr (args 10), len⟩ (below (s.gpr .esp) 96))
    (domX : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ ⟨byteAddr (args 0), len⟩) {st : Prog isa} {ld : Nat}
    {tt : Byte} (hld : ld < len)
    (hst : ∀ u, Step Ex base bytes len args s u → WP isa st u (CutPar Ex base bytes len args u ld tt)) :
    WP isa (Prog.chain (prefixWith st) (.block [])) s (PrefW Ex base bytes len dlen args s (cutOf s.mem args len ld tt)) := by
  have dl := G.dl
  have fit := G.fit
  have lw := G.lower
  have up := G.upper
  obtain h2 : 2 * len ≤ dlen := by omega_arith
  obtain hpa := comp_p s.mem args h2
  obtain hqa : (CheckPrivate.params s.mem args len dlen).q =
      if dlen = 2 * len then none else some (comp s.mem args len 2) := by
    rcases dl with e | e
    · simp only [e, ↓reduceIte]; exact VG.Proof.Ffdh.domainOf_q2 _ _ (by omega_arith)
    · have : ¬ 3 * len = 2 * len := by omega_arith
      simp only [e, this, ↓reduceIte]; exact comp_q s.mem args
  have nb : numBase = 3336 := rfl
  generalize hP : comp s.mem args len 0 = p at hpa
  generalize hG : comp s.mem args len 1 = g
  -- p, one and `p − 1`.
  refine WP.seq (WP.mono (pSetup_ok h G.e3 (by omega_arith)
    (by have := VG.CallLay.inRegions_sub G.rd (off := 0) (l := len) (by omega_arith) (by omega_arith)
        rwa [BitVec.add_zero] at this)
    (G.apart.sub_left (Region.sub_prefix (by omega_arith))))
    fun u₁ ⟨I₁, F₁, k₁, V9, V14, V15, K₁⟩ => ?_)
  rw [CheckDomain.argNum_comp, hP] at V9 V15
  obtain S₁ : Step Ex base bytes len args s u₁ := ⟨I₁, F₁, K₁⟩
  -- g.
  refine WP.seq (WP.mono (loadComp_ok I₁ (G.keep ⟨rfl, rfl⟩ K₁) (k := 1) (j := 10) (by decide) (by omega_arith)
    (by decide)) fun u₂ ⟨V₂, O₂, K₂⟩ => ?_)
  rw [comp_keep h G hb40 F₁ (by omega_arith), hG] at V₂
  obtain S₂ : Step Ex base bytes len args u₁ u₂ := Step.slot I₁ (by decide) O₂ K₂
  obtain k₂ := kept_slot I₁ (a := 10) O₂
  obtain S₁₂ := S₁.trans S₂
  -- The cut's first octet and mask.
  refine WP.seq (WP.mono (hst u₂ S₁₂) fun u₃ Sc => ?_)
  obtain S₁₃ := S₁₂.trans Sc.step
  -- The cut.
  have tlt := tt.isLt
  obtain C₃ : KeyCut.CutGeo base bytes len (args 10) (args 0) (u₃.gpr .esp) u₃.rd u₃.wr := by
    rw [S₁₃.esp, S₁₃.keeps.2.1, S₁₃.keeps.2.2]; exact C
  refine WP.seq (WP.mono (KeyCut.cut_ok Sc.step.inp hld C₃ G.e3 (w32_ofNat Sc.ld (by omega_arith))
    (tt := tt) (by
      rw [w32_ofNat Sc.t (by omega_arith)]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth])) fun u₄ Ct => ?_)
  obtain rb : Spec.Rsa.bytesAt u₃.mem (byteAddr (args 10)) len = Spec.Rsa.bytesAt s.mem (byteAddr (args 10)) len :=
    KeyScan.bytes_keep h rWs (by omega_arith) r40 S₁₃.frame
  have Cxv := Ct.x
  rw [rb] at Cxv
  obtain kc := kept_out Sc.step.inp Ct.frame C.xWs.symm
  obtain S₁₄k : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₄ := S₁₃.keeps.trans Ct.keeps
  -- x.
  obtain xrd : InRegions (u₄.rd ++ u₄.wr) (byteAddr (args 0)) len := by
    rw [S₁₄k.2.1, S₁₄k.2.2]
    obtain ⟨r, hr, hc⟩ := C.xwr
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.seq (WP.mono (load_ok Ct.inp (one_ok .wide) (slot_fit1 Ct.inp (j := 13) (by decide)) (p := 0) (l := 1)
    (L := len) (by decide) (by decide) h.outLen (by omega_arith) (by rw [cb1]; exact len_le_bc len) C.xfit xrd
    C.xWs) fun u₅ ⟨V₅, O₅, K₅⟩ => WP.block_nil ?_)
  rw [cw1, Cxv] at V₅
  rw [cb1] at O₅
  obtain S₅ : Step Ex base bytes len args u₄ u₅ := Step.slot Ct.inp (by decide) O₅ K₅
  obtain k₅ := kept_slot Ct.inp (a := 13) O₅
  obtain k₁₅ : Kept base len [9, 10, 13, 14, 15] [tbOff, foundOff, ldOff, tOff] s.mem u₅.mem :=
    (((k₁.mono.trans k₂.mono).trans Sc.kept.mono).trans kc.mono).trans k₅.mono
  obtain v9 : sv u₅.mem base len .wide 9 = p := by
    rw [k₅.slot_eq, kc.slot_eq, Sc.kept.slot_eq, k₂.slot_eq, V9]
  obtain v10 : sv u₅.mem base len .wide 10 = g := by rw [k₅.slot_eq, kc.slot_eq, Sc.kept.slot_eq, V₂]
  obtain v14 : sv u₅.mem base len .wide 14 = 1 := by
    rw [k₅.slot_eq, kc.slot_eq, Sc.kept.slot_eq, k₂.slot_eq, V14]
  obtain v15 : sv u₅.mem base len .wide 15 = pm1 len p := by
    rw [k₅.slot_eq, kc.slot_eq, Sc.kept.slot_eq, k₂.slot_eq, V15]
  obtain S₁₅k : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₅ := S₁₄k.trans S₅.keeps
  have sp₃ : u₃.gpr .esp = s.gpr .esp := S₁₃.esp
  obtain sp₄ : u₄.gpr .esp = s.gpr .esp := by rw [Ct.keeps.1 _ (by decide), sp₃]
  obtain q₅ : ¬ dlen = 2 * len → comp u₅.mem args len 2 = comp s.mem args len 2 := fun _ => by
    have F₅ := S₅.frame
    rw [sp₄] at F₅
    rw [comp_keep h G hb40 F₅ (by omega_arith), comp_x G domX Ct.frame (by omega_arith),
      comp_keep h G hb40 S₁₃.frame (by omega_arith)]
  have F₅ := S₅.frame
  rw [sp₄] at F₅
  have F₃ := S₁₃.frame
  refine ⟨S₅.inp, ?_, S₁₅k, ?_, ?_, V₅, v14, ?_, q₅⟩
  · refine ((F₃.mono fun r hr => List.mem_cons_of_mem _ hr).trans (Ct.frame.mono fun r hr => ?_)).trans
      (F₅.mono fun r hr => List.mem_cons_of_mem _ hr)
    rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..
  · rw [v9, hP]
  · rw [v10, hG]
  · rw [v15, hP]

/-- The front, from the prefix's: the bound and the scalar's check. -/
theorem frontWith_ok {dlen : Nat} (G : DomGeo args base bytes len dlen s.rd s.wr)
    {st : Prog isa} {xs : Nat}
    (hpre : WP isa (Prog.chain (prefixWith st) (.block [])) s (PrefW Ex base bytes len dlen args s xs)) :
    WP isa (Prog.chain (mainFrontWith st) (.block [])) s (FrontW Ex base bytes len dlen args s xs) := by
  have dl := G.dl
  have lw := G.lower
  obtain h2 : 2 * len ≤ dlen := by omega_arith
  obtain hpa := comp_p s.mem args h2
  obtain hqa : (CheckPrivate.params s.mem args len dlen).q =
      if dlen = 2 * len then none else some (comp s.mem args len 2) := by
    rcases dl with e | e
    · simp only [e, ↓reduceIte]; exact VG.Proof.Ffdh.domainOf_q2 _ _ (by omega_arith)
    · have : ¬ 3 * len = 2 * len := by omega_arith
      simp only [e, this, ↓reduceIte]; exact comp_q s.mem args
  show WP isa (Prog.chain (prefixWith st) (Prog.chain [CheckPrivate.bound, CheckPrivate.scalarMask, testMask]
    (.block []))) s _
  refine WP.chain_split hpre fun u₅ P => ?_
  refine WP.mono (CheckPrivate.boundTest_ok P.inp (G.keep ⟨rfl, rfl⟩ P.keeps) P.v15 P.v13 P.v9 P.q)
    fun u₆ ⟨S₆, k₆, z, v16⟩ => ?_
  have F₆ := S₆.frame
  rw [P.keeps.1 _ (by decide)] at F₆
  refine ⟨S₆.inp, P.frame.trans (F₆.mono fun r hr => List.mem_cons_of_mem _ hr), P.keeps.trans S₆.keeps,
    Gate.of_eval z (CheckPrivate.scalar_iff hpa.symm hqa), ?_, ?_, ?_, ?_, ?_, fun n2 => by rw [v16, ite_eq_right n2]⟩
  · rw [k₆.slot_eq, P.v9]
  · rw [k₆.slot_eq, P.v10]
  · rw [k₆.slot_eq]; exact P.v13
  · rw [k₆.slot_eq, P.v14]
  · rw [k₆.slot_eq, P.v15]

/-! ## The body -/

theorem fail_ok (h : In Ex base bytes len args s) (Ox : OutAt args base bytes len 0 (s.gpr .esp) s.wr)
    (Oy : OutAt args base bytes len 8 (s.gpr .esp) s.wr) (h9a : args 9 = BitVec.ofNat 32 len)
    (xy : Region.Disjoint ⟨byteAddr (args 0), len⟩ ⟨byteAddr (args 8), len⟩) :
    WP isa GenerateKey.fail s fun t =>
      t.gpr .eax = BitVec.ofNat 32 2 ∧
      Spec.Rsa.bytesAt t.mem (byteAddr (args 0)) len = List.replicate len 0 ∧
      Spec.Rsa.bytesAt t.mem (byteAddr (args 8)) len = List.replicate len 0 ∧
      Frame (⟨byteAddr (args 0), len⟩ :: ⟨byteAddr (args 8), len⟩ :: frameR base (s.gpr .esp) (fR len))
        s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have ao : accOff = 8 := rfl
  have nb : numBase = 3336 := rfl
  unfold GenerateKey.fail
  refine WP.seq (show WP isa (.block ([.mov .ecx (.imm 0)] ++ [.store (sc accOff) .ecx])) s _ from
    WP.block_append (wp_movS rfl fun u a _ => WP.block_nil ?_))
  obtain hu : In Ex base bytes len args u := h.regs a.keeps a.mem
  refine WP.mono (storeMask_ok hu (d := accOff) (c := false) (by omega_arith) a.gpr) fun v ⟨I, O, W, _, K⟩ => ?_
  obtain S : Step Ex base bytes len args s v := (Step.regs h a.mem a.keeps).trans (Step.word hu (by omega_arith) O K)
  refine WP.seq (WP.mono (outputs_ok I (by rw [S.esp]; exact Ox.keep rfl S.keeps) (by rw [S.esp]; exact Oy.keep rfl S.keeps)
    h9a xy W rfl rfl (fun e => nomatch e) (fun e => nomatch e)) fun w ⟨Bx, By, _, F, Kw⟩ => ?_)
  refine WP.mono ret_ok fun t ⟨E, M, Kt⟩ => ⟨E, ?_, ?_, ?_, (S.keeps.trans Kw).trans (Kt.mono (by decide))⟩
  · rw [M, Bx]; exact VG.Proof.Bignum.i2osp_zero' _
  · rw [M, By]; exact VG.Proof.Bignum.i2osp_zero' _
  · rw [M]; rw [S.esp] at F
    exact (S.frame.mono fun r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)).trans F

/-- A power of a valid domain's generator is accepted exactly when it is a valid public value: its
range decides it, since `g^q mod p = 1` (`publicValid_power`). -/
theorem accept_iff {a : Spec.Ffdh.Parameters} (hv : Spec.Ffdh.parametersValid a = true) {p g : Nat}
    (hp : a.p = p) (hg : a.g = g) (p1 : 1 < p) (x : Nat) :
    accept len p (g ^ x % p) = true ↔ Spec.Ffdh.publicValid ⟨a, g ^ x % p⟩ = true := by
  subst hp hg
  rw [VG.Proof.Ffdh.publicValid_power hv x]
  simp only [accept, pm1_of (show 0 < a.p by omega_using [p1]), Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, b⟩ => ⟨b, a⟩⟩

/-- A component's number fits its `len` octets. -/
theorem comp_lt (m : Mem) (k : Nat) : comp m args len k < 2 ^ (8 * len) := by
  have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt m (byteAddr (args 2) + BitVec.ofNat 64 (k * len)) len)
  rw [VG.Proof.Bignum.bytesAt_length, VG.Proof.Bignum.pow256_eq] at this
  exact this

end VG.Proof.Ffdh.X86.KeyGen
