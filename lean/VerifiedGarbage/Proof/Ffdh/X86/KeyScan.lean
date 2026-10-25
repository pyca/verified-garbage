module

public import VerifiedGarbage.Impl.Ffdh.X86.KeyGen
public import VerifiedGarbage.Proof.Ffdh.X86.Stages
public import VerifiedGarbage.Proof.Ffdh.ScanAt
public import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Ffdh.X86.Checks
import VerifiedGarbage.Proof.Ffdh.X86.Ops

/-!
# FFDH key generation on i686: the scan of the bound's octets

`scanStep` keeps, without a branch, the first nonzero octet of the bound and
its index: after `j` octets, `ebx` and the header words hold `scanAt bs j`
(`scanStep_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.KeyScan

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86 VG.Proof.Ffdh
open VG.Impl.Ffdh.X86

/-! ## The masks -/

theorem sbb_self (x : BitVec 32) (c : Bool) : x - x - (BitVec.ofBool c).setWidth 32 = cmask c := by
  cases c <;> simp [cmask] <;> decide

theorem cmask_not (c : Bool) : cmask c ^^^ 0xFFFFFFFF = cmask (!c) := by cases c <;> decide

theorem cmask_and (a b : Bool) : cmask a &&& cmask b = cmask (a && b) := by cases a <;> cases b <;> decide

theorem cmask_or (a b : Bool) : cmask a ||| cmask b = cmask (a || b) := by cases a <;> cases b <;> decide

/-- A choice by a mask, as `x ^ ((x ^ y) & m)`. -/
theorem sel (x y : BitVec 32) (c : Bool) : x ^^^ ((x ^^^ y) &&& cmask c) = if c then y else x := by
  cases c
  · simp [cmask]
  · simp only [cmask, ite_true, BitVec.and_allOnes, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- The same choice, as `x ^ ((y ^ x) & m)`. -/
theorem sel' (x y : BitVec 32) (c : Bool) : x ^^^ ((y ^^^ x) &&& cmask c) = if c then y else x := by
  rw [BitVec.xor_comm y x, sel]

/-- The carry of `b + 0xFFFFFFFF` for an octet `b`: whether it is nonzero. -/
theorem carry_ne (b : Byte) :
    decide (2 ^ 32 ≤ (b.setWidth 32).toNat + (0xFFFFFFFF : BitVec 32).toNat) = (b != 0) := by
  have hb := b.isLt
  have e : (b.setWidth 32).toNat = b.toNat := by simp [BitVec.toNat_setWidth]; omega_arith
  rw [e]
  by_cases h : b = 0
  · subst h; decide
  · have : b.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    rw [show (b != 0) = true from bne_iff_ne.mpr h]
    exact decide_eq_true (by change 2 ^ 32 ≤ b.toNat + 4294967295; omega_arith)

/-! ## One octet -/

/-- A register after an update, as an `if` that `simp` decides for literal registers. -/
theorem upd_get {s t : State} {d : Reg} {v : BitVec 32} (u : Upd s t d v) (r : Reg) :
    t.gpr r = if r = d then v else s.gpr r := by
  by_cases e : r = d
  · subst e; rw [u.gpr, ite_eq_left rfl]
  · rw [u.other r e, ite_eq_right e]

/-- The flag of the octet and whether it is the first nonzero one, the flag word updated. -/
def partA : List Instr :=
  [.movzx8 .eax ⟨.esi, 0⟩, .mov .edx (.reg .eax), .alu .add .edx (.imm 0xFFFFFFFF), .alu .sbb .edx (.reg .edx),
    .mov .ebp (.mem (sc foundOff)), .alu .xor .ebp (.imm 0xFFFFFFFF), .alu .and .ebp (.reg .edx),
    .alu .or .edx (.mem (sc foundOff)), .store (sc foundOff) .edx]

/-- The index chosen. -/
def partB : List Instr :=
  [.mov .edx (.reg .ebx), .alu .xor .edx (.reg .ecx), .alu .and .edx (.reg .ebp), .alu .xor .ebx (.reg .edx)]

/-- The octet chosen. -/
def partC : List Instr :=
  [.mov .edx (.mem (sc tbOff)), .alu .xor .eax (.reg .edx), .alu .and .eax (.reg .ebp), .alu .xor .edx (.reg .eax),
    .store (sc tbOff) .edx]

/-- The next octet. -/
def partD : List Instr :=
  [.alu .add .esi (.imm 1), .alu .add .ecx (.imm 1), .mov .edx (.mem (PublicRt.argAt 0 3)), .alu .cmp .ecx (.reg .edx)]

theorem scanStep_eq : GenerateKey.scanStep = partA ++ (partB ++ (partC ++ partD)) := rfl

section
variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

theorem word_room (h : In Ex base bytes len args s) {d : Nat} (hd : d + 4 ≤ 32) : d + 4 ≤ bytes := by
  have := h.need
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  omega_arith

/-- `movzx d, byte [m]`. -/
theorem wp_movzx8 {is : List Instr} {Q : State → Prop} {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ t, Upd s t d ((s.mem a).setWidth 32) → WP isa (.block is) t Q) :
    WP isa (.block (.movzx8 d m :: is)) s Q :=
  cons (s' := s.setReg d ((s.mem a).setWidth 32))
    (by simp only [exec, ha, State.load8, hin, ite_true, Option.map_some]) (k _ (Upd.setReg _ _ _))

theorem partA_ok (h : In Ex base bytes len args s) {a : Addr} (ha : s.ea ⟨.esi, 0⟩ = a)
    (hin : InRegions (s.rd ++ s.wr) a 1) {f : Bool} (hf : s.mem.readW (off base foundOff) 32 = cmask f) :
    WP isa (.block partA) s fun u =>
      u.gpr .eax = (s.mem a).setWidth 32 ∧ u.gpr .ebp = cmask (!f && s.mem a != 0) ∧
      u.mem = s.mem.writeW (off base foundOff) (cmask (s.mem a != 0 || f)) ∧ Keeps [.eax, .edx, .ebp] s u := by
  have r := word_room h (d := foundOff) (by decide)
  refine wp_movzx8 ha hin fun u1 a1 => ?_
  refine wp_movS rfl fun u2 a2 _ => ?_
  refine wp_addS rfl fun u3 a3 c3 => ?_
  refine wp_sbbS rfl c3 fun u4 a4 _ => ?_
  have k1 : Keeps [.eax, .edx, .ebp] s u1 := a1.keeps.mono (by decide)
  have k4 := ((k1.widen a2.keeps).widen a3.keeps).widen a4.keeps
  have s4 : Scr u4 base bytes := h.scratch.of_keeps k4 (by decide)
  refine wp_movS (readSrc_sc s4 (d := foundOff) r) fun u5 a5 _ => ?_
  refine wp_logicS (.inr rfl) rfl fun u6 a6 => ?_
  refine wp_logicS (.inl rfl) rfl fun u7 a7 => ?_
  have k7 := ((k4.widen a5.keeps).widen a6.keeps).widen a7.keeps
  have s7 : Scr u7 base bytes := h.scratch.of_keeps k7 (by decide)
  refine wp_orS (readSrc_sc s7 (d := foundOff) r) fun u8 a8 => ?_
  have s8 : Scr u8 base bytes := s7.of_keeps a8.keeps (by decide)
  refine wp_storeS (s8.ea (d := foundOff) (by omega_arith)) (s8.write (d := foundOff) (n := 4) r) fun t m9 => WP.block_nil ?_
  have M : u8.mem = s.mem := by rw [a8.mem, a7.mem, a6.mem, a5.mem, a4.mem, a3.mem, a2.mem, a1.mem]
  have F : u4.mem.readW (off base foundOff) 32 = cmask f := by rw [a4.mem, a3.mem, a2.mem, a1.mem, hf]
  have E4 : u4.gpr .edx = cmask (s.mem a != 0) := by
    rw [a4.gpr, sbb_self, a2.gpr, a1.gpr, carry_ne]
  have E7 : u7.gpr .ebp = cmask (!f && s.mem a != 0) := by
    rw [a7.gpr, a6.gpr, a5.gpr, a6.other .edx (by decide), a5.other .edx (by decide), E4, F]
    simp only [ite_true, reduceCtorEq, ite_false, cmask_not, cmask_and]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [m9.gpr, a8.other _ (by decide), a7.other _ (by decide), a6.other _ (by decide), a5.other _ (by decide),
      a4.other _ (by decide), a3.other _ (by decide), a2.other _ (by decide), a1.gpr]
  · rw [m9.gpr, a8.other _ (by decide), E7]
  · rw [m9.mem, a8.gpr, a7.other _ (by decide), a6.other _ (by decide), a5.other _ (by decide), E4, M,
      show u7.mem.readW (off base foundOff) 32 = cmask f by rw [a7.mem, a6.mem, a5.mem, F], cmask_or]
  · exact (k7.widen a8.keeps).widen (m9.keeps [])

theorem partB_ok {c : Bool} (hp : s.gpr .ebp = cmask c) :
    WP isa (.block partB) s fun u =>
      u.gpr .ebx = (if c then s.gpr .ecx else s.gpr .ebx) ∧ u.mem = s.mem ∧ Keeps [.edx, .ebx] s u := by
  refine wp_movS rfl fun u1 a1 _ => ?_
  refine wp_logicS (.inr rfl) rfl fun u2 a2 => ?_
  refine wp_logicS (.inl rfl) rfl fun u3 a3 => ?_
  refine wp_logicS (.inr rfl) rfl fun t a4 => WP.block_nil ⟨?_, ?_, ?_⟩
  · simp only [upd_get a4, upd_get a3, upd_get a2, upd_get a1, reduceCtorEq, ite_true, ite_false, hp, sel]
  · rw [a4.mem, a3.mem, a2.mem, a1.mem]
  · have k1 : Keeps [.edx, .ebx] s u1 := a1.keeps.mono (by decide)
    exact ((k1.widen a2.keeps).widen a3.keeps).widen a4.keeps

theorem partC_ok (h : In Ex base bytes len args s) {c : Bool} (hp : s.gpr .ebp = cmask c) :
    WP isa (.block partC) s fun u =>
      u.mem = s.mem.writeW (off base tbOff)
        (if c then s.gpr .eax else s.mem.readW (off base tbOff) 32) ∧ Keeps [.eax, .edx] s u := by
  have r := word_room h (d := tbOff) (by decide)
  refine wp_movS (readSrc_sc h.scratch (d := tbOff) r) fun u1 a1 _ => ?_
  refine wp_logicS (.inr rfl) rfl fun u2 a2 => ?_
  refine wp_logicS (.inl rfl) rfl fun u3 a3 => ?_
  refine wp_logicS (.inr rfl) rfl fun u4 a4 => ?_
  have k1 : Keeps [.eax, .edx] s u1 := a1.keeps.mono (by decide)
  have k4 := ((k1.widen a2.keeps).widen a3.keeps).widen a4.keeps
  have s4 : Scr u4 base bytes := h.scratch.of_keeps k4 (by decide)
  refine wp_storeS (s4.ea (d := tbOff) (by omega_arith)) (s4.write (d := tbOff) (n := 4) r) fun t m5 => WP.block_nil ?_
  refine ⟨?_, k4.widen (m5.keeps [])⟩
  rw [m5.mem, a4.mem, a3.mem, a2.mem, a1.mem]
  simp only [upd_get a4, upd_get a3, upd_get a2, upd_get a1, reduceCtorEq, ite_true, ite_false, hp, sel']

theorem partD_ok {L : BitVec 32} (hL : readSrc s (.mem (PublicRt.argAt 0 3)) = some L) :
    WP isa (.block partD) s fun u =>
      u.gpr .esi = s.gpr .esi + 1 ∧ u.gpr .ecx = s.gpr .ecx + 1 ∧ u.zf = some (s.gpr .ecx + 1 - L == 0) ∧
        u.mem = s.mem ∧ Keeps [.esi, .ecx, .edx] s u := by
  refine wp_addS rfl fun u1 a1 _ => ?_
  refine wp_addS rfl fun u2 a2 _ => ?_
  have k2 : Keeps [.esi, .ecx, .edx] s u2 := (a1.keeps.mono (by decide)).widen a2.keeps
  refine wp_movS ((argument_keep k2 (by decide) (by rw [a2.mem, a1.mem]) 3).trans hL) fun u3 a3 _ => ?_
  refine wp_cmpS rfl fun t f z => WP.block_nil ⟨?_, ?_, ?_, ?_, (k2.widen a3.keeps).widen (f.keeps [])⟩
  · simp only [f.gpr, upd_get a3, upd_get a2, upd_get a1, reduceCtorEq, ite_true, ite_false]
  · simp only [f.gpr, upd_get a3, upd_get a2, upd_get a1, reduceCtorEq, ite_true, ite_false]
  · rw [z]; simp only [upd_get a3, upd_get a2, upd_get a1, reduceCtorEq, ite_true, ite_false]
  · rw [f.mem, a3.mem, a2.mem, a1.mem]

/-- Where the bound's octets are: `len` of them at `bp`, readable, apart from the working space and
the stack below `sp`. -/
structure BGeo (base : Addr) (bytes len : Nat) (bp sp : BitVec 32) (rd wr : List Region) : Prop where
  fit : bp.toNat + len ≤ 2 ^ 32
  rd : InRegions (rd ++ wr) (byteAddr bp) len
  apart : Region.Disjoint ⟨byteAddr bp, len⟩ ⟨base, bytes⟩
  below : Region.Disjoint ⟨byteAddr bp, len⟩ (below sp 96)

/-- Before octet `j`. -/
structure ScanInv (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat)
    (args : Nat → BitVec 32) (s₀ : State) (bp : BitVec 32) (bs : List Byte) (j : Nat) (t : State) : Prop where
  step : Step Ex base bytes len args s₀ t
  kept : Kept base len [] [tbOff, foundOff] s₀.mem t.mem
  esi : t.gpr .esi = bp + BitVec.ofNat 32 j
  ecx : t.gpr .ecx = BitVec.ofNat 32 j
  ebx : t.gpr .ebx = BitVec.ofNat 32 (scanAt bs j).2.1
  found : t.mem.readW (off base foundOff) 32 = cmask (scanAt bs j).1
  tb : t.mem.readW (off base tbOff) 32 = (scanAt bs j).2.2.setWidth 32

theorem found_step (f c : Bool) : (if (!f && c) = true then true else f) = (c || f) := by
  cases f <;> cases c <;> rfl

theorem bytesAt_getD (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (Spec.Rsa.bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_range hi]

theorem tb_found_sep (base : Addr) (m : Mem) (v : BitVec 32) :
    (m.writeW (off base foundOff) v).readW (off base tbOff) 32 = m.readW (off base tbOff) 32 :=
  Mem.readW_writeW_sep (Offset.sep base (by decide) (by decide) (by decide)) (by decide)

theorem found_tb_sep (base : Addr) (m : Mem) (v : BitVec 32) :
    (m.writeW (off base tbOff) v).readW (off base foundOff) 32 = m.readW (off base foundOff) 32 :=
  Mem.readW_writeW_sep (Offset.sep base (by decide) (by decide) (by decide)) (by decide)

/-- Bytes apart from the working space and the stack below `sp`, through a stage. -/
theorem bytes_keep (h : In Ex base bytes len args s) {p : Addr} {n : Nat}
    (apart : Region.Disjoint ⟨p, n⟩ ⟨base, bytes⟩) (hn : n ≤ 2 ^ 64) {sp : BitVec 32}
    (hb40 : Region.Disjoint ⟨p, n⟩ (below sp 96)) {m m' : Mem} (F : Frame (frameR base sp (fR len)) m m') :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  have fit := fR_fit h
  refine frame_bytes F (fun r hr => ?_) hn
  rw [frameR, List.mem_cons, List.mem_map] at hr
  rcases hr with rfl | ⟨q, hq, rfl⟩
  · exact hb40
  · have := fit q hq
    exact apart.sub_right (Offset.sub_base _ (by omega_arith))

theorem scanStep_ok {s₀ t : State} {bp : BitVec 32} {bs : List Byte} {j : Nat} (hj : j < len)
    (B : BGeo base bytes len bp (s₀.gpr .esp) s₀.rd s₀.wr) (hbs : Spec.Rsa.bytesAt s₀.mem (byteAddr bp) len = bs)
    (h3 : args 3 = BitVec.ofNat 32 len) (I : ScanInv Ex base bytes len args s₀ bp bs j t) :
    WP isa (.block GenerateKey.scanStep) t fun u =>
      ScanInv Ex base bytes len args s₀ bp bs (j + 1) u ∧ u.zf = some (decide (j + 1 = len)) := by
  have h := I.step.inp
  have lw := h.lower
  have up := h.upper
  have fit := B.fit
  have sp : t.gpr .esp = s₀.gpr .esp := I.step.esp
  -- The octet.
  have ea : t.ea ⟨.esi, 0⟩ = byteAddr bp + BitVec.ofNat 64 j := by
    change addr (t.gpr .esi) 0 = _
    rw [I.esi, addr_eq (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith), BitVec.add_zero]
    exact addr_eq (by omega_arith)
  have rdB : InRegions (t.rd ++ t.wr) (byteAddr bp + BitVec.ofNat 64 j) 1 := by
    rw [I.step.keeps.2.1, I.step.keeps.2.2]
    exact VG.CallLay.inRegions_sub B.rd (by omega_arith) (by omega_arith)
  have byte : t.mem (byteAddr bp + BitVec.ofNat 64 j) = bs.getD j 0 := by
    rw [← hbs, ← bytes_keep h B.apart (by omega_arith) B.below I.step.frame, bytesAt_getD _ _ hj]
  generalize hb : bs.getD j 0 = b at byte
  generalize hf : (scanAt bs j).1 = f
  have F1 : (scanAt bs (j + 1)).1 = (b != 0 || f) := by
    rw [scanAt_succ, hb, hf, ← found_step f (b != 0)]; split <;> first | rfl | exact hf
  have F2 : (scanAt bs (j + 1)).2.1 = if (!f && b != 0) = true then j else (scanAt bs j).2.1 := by
    rw [scanAt_succ, hb, hf]; split <;> rfl
  have F3 : (scanAt bs (j + 1)).2.2 = if (!f && b != 0) = true then b else (scanAt bs j).2.2 := by
    rw [scanAt_succ, hb, hf]; split <;> rfl
  have hfw : t.mem.readW (off base foundOff) 32 = cmask f := by rw [I.found, hf]
  rw [scanStep_eq]
  refine WP.block_append (WP.mono (partA_ok h ea rdB hfw) fun uA ⟨eA, pA, mA, kA⟩ => ?_)
  rw [byte] at eA pA mA
  have OA : Outside base foundOff 4 t.mem uA.mem := by rw [mA]; exact writeW32_outside _ _ _ (by decide)
  have SA : Step Ex base bytes len args t uA := Step.word h (by decide) OA kA
  refine WP.block_append (WP.mono (partB_ok pA) fun uB ⟨eB, mB, kB⟩ => ?_)
  have SB : Step Ex base bytes len args uA uB := Step.regs SA.inp mB kB
  have pB : uB.gpr .ebp = cmask (!f && b != 0) := by rw [kB.1 _ (by decide), pA]
  refine WP.block_append (WP.mono (partC_ok SB.inp pB) fun uC ⟨mC, kC⟩ => ?_)
  have OC : Outside base tbOff 4 uB.mem uC.mem := by rw [mC]; exact writeW32_outside _ _ _ (by decide)
  have SC : Step Ex base bytes len args uB uC := Step.word SB.inp (by decide) OC kC
  refine WP.mono (partD_ok (L := BitVec.ofNat 32 len) (by rw [← h3]; exact (SC.inp.stack 3 (by decide)).readSrc))
    fun uD ⟨eD1, eD2, zD, mD, kD⟩ => ?_
  have SD : Step Ex base bytes len args uC uD := Step.regs SC.inp mD kD
  have cC : uC.gpr .ecx = BitVec.ofNat 32 j := by
    rw [kC.1 _ (by decide), kB.1 _ (by decide), kA.1 _ (by decide), I.ecx]
  have hj32 : j + 1 < 2 ^ 32 := by omega_arith
  refine ⟨⟨I.step.trans (((SA.trans SB).trans SC).trans SD), ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have kA' := kept_word h (d := foundOff) (by decide) (by decide) OA
    have kC' := kept_word SB.inp (d := tbOff) (by decide) (by decide) OC
    refine (I.kept.trans kA'.mono).trans ?_
    rw [mD]
    refine Kept.trans ?_ kC'.mono
    rw [mB]; exact (Kept.refl _).mono
  · rw [eD1, kC.1 _ (by decide), kB.1 _ (by decide), kA.1 _ (by decide), I.esi]
    bv_omega_arith
  · rw [eD2, cC]; bv_omega_arith
  · rw [kD.1 _ (by decide), kC.1 _ (by decide), eB, kA.1 _ (by decide), kA.1 _ (by decide), I.ecx, I.ebx, F2]
    split <;> rfl
  · rw [mD, mC, mB, mA, found_tb_sep, Mem.readW_writeW_self32, F1]
  · rw [mD, mC, mB, Mem.readW_writeW_self32, mA, tb_found_sep, I.tb, F3, kB.1 _ (by decide), eA]
    split <;> rfl
  · have e1 : BitVec.ofNat 32 j + 1 = BitVec.ofNat 32 (j + 1) := by rw [BitVec.ofNat_add]; rfl
    rw [zD, cC, e1]
    by_cases e : j + 1 = len
    · subst e; rw [BitVec.sub_self, decide_eq_true rfl]; rfl
    · rw [decide_eq_false e]
      refine congrArg some (beq_eq_false_iff_ne.mpr fun z => e ?_)
      have z' : BitVec.ofNat 32 (j + 1) = BitVec.ofNat 32 len := by
        have := BitVec.sub_eq_iff_eq_add.mp z; simpa using this
      have := congrArg BitVec.toNat z'
      simp only [BitVec.toNat_ofNat] at this
      omega_arith

/-- A do-while loop over `ne` that runs its body `n > 0` times, with ZF set exactly on the last
iteration. -/
theorem count_loop {body : Prog isa} {n : Nat} (hn : 0 < n) (I : Nat → State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s → WP isa body s fun s' => I (k + 1) s' ∧ s'.zf = some (decide (k + 1 = n)))
    {s : State} (h0 : I 0 s) : WP isa (.loop body .ne) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega_arith, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hz⟩ => ?_
  have he : isa.eval .ne s' = some (!decide (k + 1 = n)) := by
    show s'.zf.map (!·) = _; rw [hz]; rfl
  by_cases hl : k + 1 = n
  · exact .inl ⟨by rw [he]; simp [hl], hl ▸ hi'⟩
  · exact .inr ⟨by rw [he]; simp [hl], n - (k + 1), by omega_arith, k + 1, rfl, by omega_arith, hi'⟩

/-- The bound's pointer: the domain's, plus twice its length beyond p and g. -/
abbrev boundAt (args : Nat → BitVec 32) : BitVec 32 :=
  args 2 + (args 12 - args 3 - args 3) + (args 12 - args 3 - args 3)

theorem init_ok (h : In Ex base bytes len args s) (h3 : args 3 = BitVec.ofNat 32 len) {bs : List Byte}
    (hl : bs.length = len) :
    WP isa (.block (GenerateKey.boundPtr ++ GenerateKey.scanInit)) s
      (ScanInv Ex base bytes len args s (boundAt args) bs 0) := by
  have r16 := word_room h (d := tbOff) (by decide)
  have r20 := word_room h (d := foundOff) (by decide)
  have lw := h.lower
  have rd (i : Nat) (hi : i < 18) {u : State} (K : Keeps [.eax, .ebx, .ecx, .esi] s u) (M : u.mem = s.mem) :
      readSrc u (.mem (PublicRt.argAt 0 i)) = some (args i) :=
    (argument_keep K (by decide) M i).trans (h.stack i hi).readSrc
  have k0 := Keeps.refl [.eax, .ebx, .ecx, .esi] s
  refine wp_movS (rd 12 (by decide) k0 rfl) fun u1 a1 _ => ?_
  have k1 := k0.widen a1.keeps
  refine wp_movS (rd 3 (by decide) k1 a1.mem) fun u2 a2 _ => ?_
  refine wp_subS rfl fun u3 a3 _ => ?_
  refine wp_subS rfl fun u4 a4 _ => ?_
  have k4 := ((k1.widen a2.keeps).widen a3.keeps).widen a4.keeps
  refine wp_movS (rd 2 (by decide) k4 (by rw [a4.mem, a3.mem, a2.mem, a1.mem])) fun u5 a5 _ => ?_
  refine wp_addS rfl fun u6 a6 _ => ?_
  refine wp_addS rfl fun u7 a7 _ => ?_
  have k7 := ((k4.widen a5.keeps).widen a6.keeps).widen a7.keeps
  have m7 : u7.mem = s.mem := by rw [a7.mem, a6.mem, a5.mem, a4.mem, a3.mem, a2.mem, a1.mem]
  refine wp_movS (rd 3 (by decide) k7 m7) fun u8 a8 _ => ?_
  refine wp_subS rfl fun u9 a9 _ => ?_
  refine wp_movS rfl fun u10 a10 _ => ?_
  refine wp_movS rfl fun u11 a11 _ => ?_
  have k11 := (((k7.widen a8.keeps).widen a9.keeps).widen a10.keeps).widen a11.keeps
  have m11 : u11.mem = s.mem := by rw [a11.mem, a10.mem, a9.mem, a8.mem, m7]
  have s11 : Scr u11 base bytes := h.scratch.of_keeps k11 (by decide)
  refine wp_storeS (s11.ea (d := tbOff) (by omega_arith)) (s11.write (d := tbOff) (n := 4) r16) fun u12 m12 => ?_
  have s12 : Scr u12 base bytes := s11.of_keeps (m12.keeps []) (by decide)
  refine wp_storeS (s12.ea (d := foundOff) (by omega_arith)) (s12.write (d := foundOff) (n := 4) r20) fun t m13 =>
    WP.block_nil ?_
  have e0 : u11.gpr .eax = 0 := a11.gpr
  have O12 : Outside base tbOff 4 u11.mem u12.mem := by rw [m12.mem]; exact writeW32_outside _ _ _ (by decide)
  have O13 : Outside base foundOff 4 u12.mem t.mem := by rw [m13.mem]; exact writeW32_outside _ _ _ (by decide)
  have S11 : Step Ex base bytes len args s u11 := Step.regs h m11 k11
  have S12 : Step Ex base bytes len args u11 u12 := Step.word S11.inp (by decide) O12 (m12.keeps [])
  have S13 : Step Ex base bytes len args u12 t := Step.word S12.inp (by decide) O13 (m13.keeps [])
  refine ⟨(S11.trans S12).trans S13, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have k12 := kept_word S11.inp (d := tbOff) (by decide) (by decide) O12
    have k13 := kept_word S12.inp (d := foundOff) (by decide) (by decide) O13
    rw [← m11]; exact k12.mono.trans k13.mono
  · simp only [m13.gpr, m12.gpr, upd_get a11, upd_get a10, upd_get a9, upd_get a8, upd_get a7, upd_get a6,
      upd_get a5, upd_get a4, upd_get a3, upd_get a2, upd_get a1, reduceCtorEq, ite_true, ite_false]
    rw [BitVec.add_zero]
  · simp only [m13.gpr, m12.gpr, upd_get a11, upd_get a10, reduceCtorEq, ite_true, ite_false]; rfl
  · simp only [m13.gpr, m12.gpr, upd_get a11, upd_get a10, upd_get a9, upd_get a8, reduceCtorEq, ite_true,
      ite_false, scanAt, hl, h3]
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith)]
  · rw [m13.mem, Mem.readW_writeW_self32, m12.gpr, e0]; rfl
  · rw [m13.mem, tb_found_sep, m12.mem, Mem.readW_writeW_self32, e0]; rfl

/-- The bits up to the top one of a word. -/
def smear32 (x : BitVec 32) : BitVec 32 :=
  let a := x ||| x >>> 1
  let b := a ||| a >>> 2
  b ||| b >>> 4

theorem smear32_toNat (b : Byte) : (smear32 (b.setWidth 32)).toNat = KeyScalar.smearN b.toNat := by
  have hb := b.isLt
  simp only [smear32, KeyScalar.smearN, BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (show b.toNat < 2 ^ 32 by omega_arith)]

theorem scanEnd_ok (h : In Ex base bytes len args s) :
    WP isa (.block GenerateKey.scanEnd) s fun u =>
      u.mem = (s.mem.writeW (off base ldOff) (s.gpr .ebx)).writeW (off base tOff)
        (smear32 (s.mem.readW (off base tbOff) 32)) ∧ Keeps [.eax, .edx] s u := by
  have r24 := word_room h (d := ldOff) (by decide)
  have r28 := word_room h (d := tOff) (by decide)
  have r16 := word_room h (d := tbOff) (by decide)
  refine wp_storeS (h.scratch.ea (d := ldOff) (by omega_arith)) (h.scratch.write (d := ldOff) (n := 4) r24)
    fun u1 m1 => ?_
  have s1 : Scr u1 base bytes := h.scratch.of_keeps (m1.keeps []) (by decide)
  refine wp_movS (readSrc_sc s1 (d := tbOff) r16) fun u2 a2 _ => ?_
  refine wp_movS rfl fun u3 a3 _ => ?_
  refine wp_shr (by decide) fun u4 a4 _ => ?_
  refine wp_orS (show readSrc u4 (.reg .edx) = some (u4.gpr .edx) from rfl) fun u5 a5 => ?_
  refine wp_movS rfl fun u6 a6 _ => ?_
  refine wp_shr (by decide) fun u7 a7 _ => ?_
  refine wp_orS (show readSrc u7 (.reg .edx) = some (u7.gpr .edx) from rfl) fun u8 a8 => ?_
  refine wp_movS rfl fun u9 a9 _ => ?_
  refine wp_shr (by decide) fun u10 a10 _ => ?_
  refine wp_orS (show readSrc u10 (.reg .edx) = some (u10.gpr .edx) from rfl) fun u11 a11 => ?_
  have k2 : Keeps [.eax, .edx] u1 u2 := a2.keeps.mono (by decide)
  have k11 := ((((((((k2.widen a3.keeps).widen a4.keeps).widen a5.keeps).widen a6.keeps).widen a7.keeps).widen
    a8.keeps).widen a9.keeps).widen a10.keeps).widen a11.keeps
  have s11 : Scr u11 base bytes := s1.of_keeps k11 (by decide)
  refine wp_storeS (s11.ea (d := tOff) (by omega_arith)) (s11.write (d := tOff) (n := 4) r28) fun t m12 =>
    WP.block_nil ⟨?_, ((m1.keeps [.eax, .edx]).widen k11).widen (m12.keeps [])⟩
  have M : u11.mem = u1.mem := by
    rw [a11.mem, a10.mem, a9.mem, a8.mem, a7.mem, a6.mem, a5.mem, a4.mem, a3.mem, a2.mem]
  rw [m12.mem, M, m1.mem]
  congr 1
  simp only [upd_get a11, upd_get a10, upd_get a9, upd_get a8, upd_get a7, upd_get a6, upd_get a5, upd_get a4,
    upd_get a3, upd_get a2, reduceCtorEq, ite_true, ite_false, m1.mem, smear32]
  rw [Mem.readW_writeW_sep (Offset.sep base (by decide) (by decide) (by decide)) (by decide)]

/-- What the scan leaves. -/
structure ScanOut (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat)
    (args : Nat → BitVec 32) (s₀ : State) (bs : List Byte) (u : State) : Prop where
  step : Step Ex base bytes len args s₀ u
  kept : Kept base len [] [tbOff, foundOff, ldOff, tOff] s₀.mem u.mem
  ld : w32 u.mem base ldOff = lead bs
  t : w32 u.mem base tOff = KeyScalar.smearN (bs.getD (lead bs) 0).toNat

theorem scan_ok (h : In Ex base bytes len args s) (h3 : args 3 = BitVec.ofNat 32 len)
    (B : BGeo base bytes len (boundAt args) (s.gpr .esp) s.rd s.wr) :
    WP isa GenerateKey.scan s
      (ScanOut Ex base bytes len args s (Spec.Rsa.bytesAt s.mem (byteAddr (boundAt args)) len)) := by
  generalize hbs : Spec.Rsa.bytesAt s.mem (byteAddr (boundAt args)) len = bs
  have hl : bs.length = len := by rw [← hbs]; simp [Spec.Rsa.bytesAt]
  have lw := h.lower
  have ne : bs ≠ [] := by intro e; rw [e] at hl; simp at hl; omega_arith
  unfold GenerateKey.scan
  refine WP.seq (WP.mono (init_ok h h3 hl) fun u I => ?_)
  refine WP.seq (WP.mono (count_loop (n := len) (by omega_arith) (ScanInv Ex base bytes len args s (boundAt args) bs)
    (fun k hk v Iv => scanStep_ok hk B hbs h3 Iv) I) fun v Iv => ?_)
  refine WP.mono (scanEnd_ok Iv.step.inp) fun t ⟨mt, kt⟩ => ?_
  have O1 : Outside base ldOff 4 v.mem (v.mem.writeW (off base ldOff) (v.gpr .ebx)) :=
    writeW32_outside _ _ _ (by decide)
  have O2 : Outside base tOff 4 (v.mem.writeW (off base ldOff) (v.gpr .ebx)) t.mem := by
    rw [mt]; exact writeW32_outside _ _ _ (by decide)
  have k1 := kept_word Iv.step.inp (d := ldOff) (by decide) (by decide) O1
  have k2 := kept_word Iv.step.inp (d := tOff) (by decide) (by decide) O2
  have Sd : Step Ex base bytes len args v t := by
    have hv := Iv.step.inp
    have bl := hv.bytes_lt
    have nd := hv.need
    have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
    have nb : numBase = 3336 := rfl
    have l24 : ldOff = 24 := rfl
    have t28 : tOff = 28 := rfl
    exact ⟨hv.keep kt (by decide) (by decide) ((O1.mono (Nat.zero_le _) (by omega_arith)).trans
      (O2.mono (Nat.zero_le _) (by omega_arith))), (wordF hv (by decide) O1).trans (wordF hv (by decide) O2),
      kt.mono (by decide)⟩
  have sc := scanAt_length ne
  rw [hl] at sc
  refine ⟨Iv.step.trans Sd, Iv.kept.mono.trans (k1.mono.trans k2.mono), ?_, ?_⟩
  · show (t.mem.readW (off base ldOff) 32).toNat = _
    rw [mt, Mem.readW_writeW_sep (Offset.sep base (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32, Iv.ebx, sc]
    simp only [BitVec.toNat_ofNat]
    have := lead_lt ne
    have := h.upper
    omega_arith
  · show (t.mem.readW (off base tOff) 32).toNat = _
    rw [mt, Mem.readW_writeW_self32, Iv.tb, sc, smear32_toNat]

end

end VG.Proof.Ffdh.X86.KeyScan
