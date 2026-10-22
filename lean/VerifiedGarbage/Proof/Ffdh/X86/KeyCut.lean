module

public import VerifiedGarbage.Impl.Ffdh.X86.KeyGen
import VerifiedGarbage.Proof.Ffdh.X86.KeyScan
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Powers
import VerifiedGarbage.Proof.Dsa.X86.StackArgument
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.In
public import VerifiedGarbage.Proof.Bignum.X86.CrtValue
public import VerifiedGarbage.Proof.Ffdh.KeyScalar
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Spec.Dsa

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
    exact decide_eq_true (by change 2 ^ 32 ≤ x.toNat + 4294967295; omega)

theorem xor_ofNat_ne {j ld : Nat} (hj : j < 2 ^ 32) (hl : ld < 2 ^ 32) :
    (BitVec.ofNat 32 j ^^^ BitVec.ofNat 32 ld != 0) = !decide (j = ld) := by
  by_cases e : j = ld
  · subst e; simp
  · have : BitVec.ofNat 32 j ^^^ BitVec.ofNat 32 ld ≠ 0 := by
      intro z
      have := congrArg BitVec.toNat (BitVec.xor_eq_zero_iff.mp z)
      simp only [BitVec.toNat_ofNat] at this
      omega
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
    addr_eq (by omega)
  refine Eq.trans ?_ (h.stack i hi).value
  unfold VG.Proof.Dsa.X86.stackValue
  rw [P]
  refine F.readW (r := ⟨VG.Proof.Dsa.X86.stackAddress s i, 4⟩) (Region.contains_self _ _) (fun r' hr' => ?_)
    (by decide)
  obtain rfl := List.mem_singleton.mp hr'
  rw [E]
  exact hf.sub_left (Offset.sub_base _ (by omega))

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
  rw [hr, addr_eq (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega), BitVec.add_zero]
  exact addr_eq (by omega)

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
    I.frame.readW (r := ⟨base, bytes⟩) (Scr.contains h.scratch.nowrap (by have := word_room h hd; omega))
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact C.xWs.symm) (by decide)
  rw [cutStep_eq]
  refine WP.block_append (WP.mono (cutA_ok (ld := ld) (tt := tt) h.scratch r24 r28 I.ecx (by omega)
    (by rw [ws _ (by decide), wld]) (by omega) (by rw [ws _ (by decide), wt])) fun uA ⟨eA, mA, kA⟩ => ?_)
  have esiA : uA.gpr .esi = rp + BitVec.ofNat 32 j := by rw [kA.1 _ (by decide), I.esi]
  have ebxA : uA.gpr .ebx = xp + BitVec.ofNat 32 j := by rw [kA.1 _ (by decide), I.ebx]
  have rdA : InRegions (uA.rd ++ uA.wr) (byteAddr rp + BitVec.ofNat 64 j) 1 := by
    rw [kA.2.1, kA.2.2, I.keeps.2.1, I.keeps.2.2]; exact VG.CallLay.inRegions_sub C.rrd (by omega) (by omega)
  have wrA : InRegions uA.wr (byteAddr xp + BitVec.ofNat 64 j) 1 := by
    rw [kA.2.2, I.keeps.2.2]; exact VG.CallLay.inRegions_sub C.xwr (by omega) (by omega)
  refine WP.block_append (WP.mono (cutB_ok (ea_at esiA hj rf) rdA (ea_at ebxA hj xf) wrA)
    fun uB ⟨mB, kB⟩ => ?_)
  have FB : Frame [⟨byteAddr xp, len⟩] s.mem uB.mem := by
    rw [mB, mA]
    exact I.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  have kB' : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s uB := (I.keeps.widen kA).widen kB
  have hB := in_keepOut h₀ kB' (by decide) (by decide) FB C.xFrame
  refine WP.mono (cutC_ok (L := BitVec.ofNat 32 len) (by rw [← h3]; exact (hB.stack 3 (by decide)).readSrc))
    fun u ⟨e1, e2, e3, z, mu, ku⟩ => ?_
  have e1j : BitVec.ofNat 32 j + 1 = BitVec.ofNat 32 (j + 1) := by rw [BitVec.ofNat_add]; rfl
  have rb : uA.mem (byteAddr rp + BitVec.ofNat 64 j) = (Spec.Rsa.bytesAt s.mem (byteAddr rp) len).getD j 0 := by
    rw [mA, bytesAt_getD _ _ hj]
    refine I.frame _ fun r hr hc => ?_
    obtain rfl := List.mem_singleton.mp hr
    exact C.apart _ (Offset.contains_base _ (by omega) (by omega)) hc
  have hl : (Spec.Rsa.bytesAt s.mem (byteAddr rp) len).length = len := by simp [Spec.Rsa.bytesAt]
  refine ⟨⟨by rw [mu]; exact FB, kB'.widen ku, ?_, ?_, ?_, fun i hi => ?_⟩, ?_⟩
  · rw [e1, kB.1 _ (by decide), esiA, BitVec.add_assoc, e1j]
  · rw [e2, kB.1 _ (by decide), ebxA, BitVec.add_assoc, e1j]
  · rw [e3, kB.1 _ (by decide), kA.1 _ (by decide), I.ecx, e1j]
  · rw [mu, mB]
    by_cases e : i = j
    · subst e
      rw [byte_write_self, rb, eA, cut_byte, cut_getD tt (by rw [hl]; exact hld) (by rw [hl]; exact hj)]
    · rw [Mem.writeW, Mem.write_apply (by rw [Offset.sub_toNat' _ (by omega) (by omega)]; split <;> omega), mA,
        I.out i (by omega)]
  · rw [z, kB.1 _ (by decide), kA.1 _ (by decide), I.ecx, e1j]
    by_cases e : j + 1 = len
    · subst e; rw [BitVec.sub_self, decide_eq_true rfl]; rfl
    · rw [decide_eq_false e]
      refine congrArg some (beq_eq_false_iff_ne.mpr fun z => e ?_)
      have z' : BitVec.ofNat 32 (j + 1) = BitVec.ofNat 32 len := by
        have := BitVec.sub_eq_iff_eq_add.mp z; simpa using this
      have := congrArg BitVec.toNat z'
      simp only [BitVec.toNat_ofNat] at this
      omega

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
  refine WP.mono (count_loop (n := len) (by omega) _ (fun k hk v Iv => cutStep_ok h hk hld C h3 wld wt Iv) I0)
    fun u Iu => ⟨in_keepOut h Iu.keeps (by decide) (by decide) Iu.frame C.xFrame, Iu.frame, Iu.keeps, ?_⟩
  have hl : (Spec.Rsa.bytesAt s.mem (byteAddr (args 10)) len).length = len := by simp [Spec.Rsa.bytesAt]
  apply List.ext_getElem
  · rw [KeyScalar.cut_length _ (by rw [hl]; exact hld), hl]; simp [Spec.Rsa.bytesAt]
  · intro i h1 h2
    have hi : i < len := by simpa [Spec.Rsa.bytesAt] using h1
    rw [← getD_of h1, ← getD_of h2, bytesAt_getD _ _ hi, Iu.out i hi]

end

end VG.Proof.Ffdh.X86.KeyCut
