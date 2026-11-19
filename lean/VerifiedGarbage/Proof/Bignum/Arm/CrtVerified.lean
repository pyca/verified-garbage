module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPower
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Bignum.Arm.CrtInput
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Impl.Bignum.Arm.R2
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Rsa.CrtPrecomputedContract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Impl.Bignum.Arm.CrtPrecomputed
import VerifiedGarbage.Proof.Bignum.Arm.CrtEntryCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtEntryReady
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPowerCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowShared
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtCallStack
import VerifiedGarbage.Proof.Bignum.Arm.PcPush
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Rsa.Contract
meta import VerifiedGarbage.Proof.Rsa.Contract
meta import VerifiedGarbage.Proof.Rsa.CrtPrecomputedContract
meta import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Bignum.Arm.PrimeR2FromCT
import VerifiedGarbage.Proof.Bignum.Arm.PrimeR2From
import VerifiedGarbage.Proof.Bignum.Arm.CopyBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstLayout
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.SelectArrayCT
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.R2CT
import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.X25519.Arm.Instr
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Bignum.Arm.PrimeR2FromCT
meta import VerifiedGarbage.Proof.Bignum.Arm.PrimeR2From
meta import VerifiedGarbage.Proof.Bignum.Arm.CopyBytesCT
meta import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
meta import VerifiedGarbage.Proof.Bignum.Arm.SmallConstLayout
meta import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
meta import VerifiedGarbage.Proof.Bignum.Arm.SelectArrayCT
meta import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Bignum.Arm.Stack
meta import VerifiedGarbage.Proof.Bignum.Arm.R2CT
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
meta import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowShared
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Inline
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.SubModArrayArgs
import VerifiedGarbage.Proof.Bignum.Arm.CopyBuffer
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.R2
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Arm.ArrayFrame
import VerifiedGarbage.Proof.Bignum.Arm.ClearArrayWide
import VerifiedGarbage.Proof.Bignum.Arm.SelectArray
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.ExportEncoding
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Impl.Bignum.Arm.CrtPrecomputed
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPower
meta import VerifiedGarbage.Proof.Bignum.Arm.SubModArrayArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.CopyBuffer
meta import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
meta import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
meta import VerifiedGarbage.Proof.Bignum.Arm.R2
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Bignum.Arm.ArrayFrame
meta import VerifiedGarbage.Proof.Bignum.Arm.ClearArrayWide
meta import VerifiedGarbage.Proof.Bignum.Arm.SelectArray
meta import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
meta import VerifiedGarbage.Proof.Bignum.ExportEncoding
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.CallLay

/-! ### `Bignum.Arm.CrtGivenCT`, which only this module used -/

section

/-! ### `Bignum.Arm.CrtGiven`, which this module and modules that import it used -/

section

/-! # Preparing a factor with its given `R² mod p`

`narrowPrimeGiven` leaves what `narrowPrime` does (`NarrowPrimePost`), for
a CRT given the factors' `R² mod p` and `R² mod q` (`CrtGeometry.r2`). -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt Keeps)
open VG.Proof.X25519.Arm (Rest Upd wp_ldr wp_str wp_mov wp_dp wp_cmp op2_reg op2_imm op2_lsl op2_lsr dpVal)

/-! ## The test of the width -/

theorem ceil8_ofNat {k : Nat} (hk : k < 2 ^ 28) :
    (BitVec.ofNat 32 k + 7) >>> 3 = BitVec.ofNat 32 ((k + 7) / 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  omega_arith

theorem beq_sub_ofNat {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b == 0) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · have ne : BitVec.ofNat 32 a - BitVec.ofNat 32 b ≠ 0 := by
      intro e
      apply h
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
        Nat.mod_eq_of_lt hb] at this
      change _ = 0 at this
      omega_using [ha, hb, this]
    simp only [h, decide_false]
    exact beq_eq_false_iff_ne.mpr ne

theorem r2WidthTest_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {j : Fin 6} {v : Nat}
    (shared : CrtShared g bs s) (ready : ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v s) :
    WP isa (.block (r2WidthTest (56 + 8 * j.val + 4))) s fun t =>
      t.z = decide (v = (g.sourceLength j.succ + 7) / 8) ∧ t.mem = s.mem ∧ Rest [.r1, .r2] s t := by
  have nw := ready.workspace
  obtain header := nativeHeader_of_layout s.mem (crtN g.base g.words) nw.nowrap (Nat.le_refl _) ready.layout
  rw [ready.width] at header
  have size : 256 ≤ 8 * workspaceWords g.words := shared.main.toCrtLayoutState.size
  have hj := j.isLt
  obtain lenSmall : g.sourceLength j.succ < 2 ^ 28 := by
    have := (crt_width_valid shared.buffers.lengthValid).2.1
    have := shared.buffers.lengthValid.2
    have := shared.buffers.pShort
    have := shared.buffers.qShort
    have : g.sourceLength j.succ ≤ g.length := by
      unfold CrtGeometry.sourceLength; split <;> omega_arith
    omega_arith
  obtain vSmall : v < 2 ^ 28 := by
    have := ready.width ▸ ready.layout.2.2.1
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at this
    have := nw.nowrap
    omega_arith
  have nNow := nw.nowrap
  have spNow := shared.stack.nowrap
  unfold r2WidthTest
  refine wp_ldr (a := off (State.addr (crtN g.base g.words)) 48) (by decide)
    (by rw [ready.ptr]; exact addr_add (by omega_using [size, nNow])) (nw.read (by omega_using [size])) fun u a => ?_
  obtain slotAddr : State.addr (u.sp + BitVec.ofNat 32 (56 + 8 * j.val + 4)) = off (State.addr s.sp) (60 + 8 * j.val) := by
    rw [a.sp, show 56 + 8 * j.val + 4 = 60 + 8 * j.val by omega_using []]
    exact addr_add (by omega_using [spNow])
  refine wp_loadStack (a := off (State.addr s.sp) (60 + 8 * j.val)) (by omega_using []) slotAddr
    (by rw [a.rd, a.wr]; exact shared.stack.read (by omega_using [])) fun z b => ?_
  refine wp_dp (op2_imm (by decide)) fun y c => ?_
  refine wp_mov (op2_lsr ⟨by decide, by decide⟩) fun x d => ?_
  refine wp_cmp (op2_reg _ _) fun t e zf => WP.block_nil ?_
  obtain r1 : x.gpr .r1 = BitVec.ofNat 32 v := by
    rw [d.other .r1 (by decide), c.other .r1 (by decide), b.other .r1 (by decide), a.gpr]
    exact header.count
  obtain r2 : x.gpr .r2 = BitVec.ofNat 32 ((g.sourceLength j.succ + 7) / 8) := by
    rw [d.gpr, c.gpr, dpVal, b.gpr, a.mem, shared.stack.length j]
    exact ceil8_ofNat lenSmall
  refine ⟨?_, e.mem.trans (d.mem.trans (c.mem.trans (b.mem.trans a.mem))),
    (a.rest (by decide)).trans ((b.rest (by decide)).trans ((c.rest (by decide)).trans
      ((d.rest (by decide)).trans (e.rest _))))⟩
  rw [zf, r1, r2]
  exact beq_sub_ofNat (by omega_using [vSmall]) (by omega_using [lenSmall])

/-! ## The given value's address -/

/-- The address of the factor `j.succ`'s given `R² mod X`. -/
def r2Src (g : CrtGeometry) (a : BitVec 32) (j : Fin 6) : BitVec 32 :=
  if j = 2 then a + BitVec.ofNat 32 (8 * Spec.Rsa.primeWords g.pLength) else a

theorem maxTwo_ofNat {c : Nat} (h1 : 1 ≤ c) (hc : c < 2 ^ 28) :
    BitVec.ofNat 32 c + (BitVec.ofNat 32 c - 2) >>> 31 = BitVec.ofNat 32 (max 2 c) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_sub,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  by_cases h : c = 1
  · subst h; decide
  · rw [Nat.max_eq_right (by omega_using [h1, h])]
    omega_arith

theorem r2Source_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {a : BitVec 32} {j : Fin 6}
    (hj : j = 1 ∨ j = 2) (ha : g.r2 = some a) (shared : CrtShared g bs s) :
    WP isa (.block (r2Source (56 + 8 * j.val))) s fun t =>
      t.gpr .r1 = r2Src g a j ∧ t.mem = s.mem ∧ Rest [.r1, .r2, .r3] s t := by
  obtain r := shared.buffers.r2 a ha
  have slot := r.slotFit
  rcases hj with rfl | rfl
  · show WP isa (.block [.ldrSp .r1 112]) s _
    refine wp_loadStack (a := off (State.addr s.sp) 112) (by decide) (addr_add (by omega_using [slot])) r.slotRead
      fun t b => WP.block_nil ?_
    exact ⟨by rw [b.gpr, r.slot]; rfl, b.mem, b.rest (by decide)⟩
  · show WP isa (.block [.ldrSp .r1 112, .ldrSp .r2 68, .dp .add .r2 .r2 (.imm 7), .mov .r2 (.shifted .r2 .lsr 3),
      .dp .sub .r3 .r2 (.imm 2), .mov .r3 (.shifted .r3 .lsr 31), .dp .add .r2 .r2 (.reg .r3),
      .dp .add .r1 .r1 (.shifted .r2 .lsl 3)]) s _
    have spNow := shared.stack.nowrap
    obtain pLen : g.pLength < 2 ^ 28 := by
      have := shared.buffers.pShort; have := shared.buffers.lengthValid.2; omega_arith
    have pPos := shared.buffers.pPositive
    refine wp_loadStack (a := off (State.addr s.sp) 112) (by decide) (addr_add (by omega_using [slot])) r.slotRead
      fun u b => ?_
    refine wp_loadStack (a := off (State.addr s.sp) 68) (by decide)
      (by rw [b.sp]; exact addr_add (by omega_using [slot])) (by rw [b.rd, b.wr]; exact shared.stack.read (by decide))
      fun v c => ?_
    refine wp_dp (op2_imm (by decide)) fun x d => ?_
    refine wp_mov (op2_lsr ⟨by decide, by decide⟩) fun y e => ?_
    refine wp_dp (op2_imm (by decide)) fun z f => ?_
    refine wp_mov (op2_lsr ⟨by decide, by decide⟩) fun w i => ?_
    refine wp_dp (op2_reg _ _) fun q k => ?_
    refine wp_dp (op2_lsl ⟨by decide, by decide⟩) fun t l => WP.block_nil ?_
    obtain len : s.mem.readW (off (State.addr s.sp) 68) 32 = BitVec.ofNat 32 g.pLength := shared.stack.length 1
    obtain cY : y.gpr .r2 = BitVec.ofNat 32 ((g.pLength + 7) / 8) := by
      rw [e.gpr, d.gpr, dpVal, c.gpr, b.mem, len]
      exact ceil8_ofNat pLen
    obtain cQ : q.gpr .r2 = BitVec.ofNat 32 (Spec.Rsa.primeWords g.pLength) := by
      rw [k.gpr, dpVal, i.other .r2 (by decide), f.other .r2 (by decide), i.gpr, f.gpr, dpVal, cY]
      unfold Spec.Rsa.primeWords Spec.Rsa.modulusWords
      exact maxTwo_ofNat (by omega_using [pPos]) (by omega_using [pLen])
    obtain aQ : q.gpr .r1 = a := by
      rw [k.other .r1 (by decide), i.other .r1 (by decide), f.other .r1 (by decide), e.other .r1 (by decide),
        d.other .r1 (by decide), c.other .r1 (by decide), b.gpr, r.slot]
    refine ⟨?_, l.mem.trans (k.mem.trans (i.mem.trans (f.mem.trans (e.mem.trans (d.mem.trans (c.mem.trans b.mem)))))),
      (b.rest (by decide)).trans ((c.rest (by decide)).trans ((d.rest (by decide)).trans ((e.rest (by decide)).trans
        ((f.rest (by decide)).trans ((i.rest (by decide)).trans ((k.rest (by decide)).trans (l.rest (by decide))))))))⟩
    rw [l.gpr, dpVal, aQ, cQ, shl32_ofNat]
    unfold r2Src
    simp only [↓reduceIte]

/-! ## The given value -/

theorem r2_wordsAt_append (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Rsa.wordsAt m p (a + b) = Spec.Rsa.wordsAt m p a ++ Spec.Rsa.wordsAt m (p + BitVec.ofNat 64 (8 * a)) b := by
  simp only [Spec.Rsa.wordsAt, List.range_add, List.map_append, List.map_map]
  refine congrArg (_ ++ ·) (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp_apply]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]

/-- `n` words that are `x`'s, read as one number. -/
theorem read_of_toWords {m : Mem} {p : Addr} {n x : Nat}
    (h : Spec.Rsa.wordsAt m p n = Spec.Rsa.toWords x n) (hx : x < 2 ^ (64 * n)) :
    (m.read p (8 * n)).toNat = x := by
  obtain e := VG.Proof.Bignum.read_eq_wv m p 0 n
  simp only [off, BitVec.add_zero] at e
  rw [e, ← Nat.mod_eq_of_lt hx]
  rw [Spec.Rsa.wordsAt, Spec.Rsa.toWords, List.map_inj_left] at h
  refine VG.Proof.Bignum.wv_of_words fun i hi => ?_
  show (m.readW (p + BitVec.ofNat 64 (0 + 8 * i)) 64).toNat = _
  rw [Nat.zero_add, h i (List.mem_range.mpr hi), BitVec.toNat_ofNat]

/-- The factor `j.succ`'s given `R² mod X`, `v = max(2, ⌈len/8⌉)` words at
`r2Src`, apart from the CRT's workspace. -/
theorem r2Src_given {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {a : BitVec 32} {j : Fin 6}
    (hj : j = 1 ∨ j = 2) (ha : g.r2 = some a) (shared : CrtShared g bs s) :
    (r2Src g a j).toNat + 8 * Spec.Rsa.primeWords (g.sourceLength j.succ) ≤ 2 ^ 32 ∧
      InRegions (s.rd ++ s.wr) (State.addr (r2Src g a j)) (8 * Spec.Rsa.primeWords (g.sourceLength j.succ)) ∧
      Region.Disjoint ⟨State.addr (r2Src g a j), 8 * Spec.Rsa.primeWords (g.sourceLength j.succ)⟩
        ⟨State.addr g.base, g.size⟩ ∧
      Spec.Rsa.wordsAt s.mem (State.addr (r2Src g a j)) (Spec.Rsa.primeWords (g.sourceLength j.succ)) =
        Spec.Rsa.primeR2 (bs j.succ) := by
  obtain r := shared.buffers.r2 a ha
  have fit := r.fit
  have words := r.words
  have read := r.read
  have sep := r.separate
  unfold CrtGeometry.r2Words at fit words read sep
  obtain p2 : 2 ≤ Spec.Rsa.primeWords g.pLength := Nat.le_max_left _ _
  obtain q2 : 2 ≤ Spec.Rsa.primeWords g.qLength := Nat.le_max_left _ _
  rw [r2_wordsAt_append] at words
  obtain lenP : (Spec.Rsa.wordsAt s.mem (State.addr a) (Spec.Rsa.primeWords g.pLength)).length =
      (Spec.Rsa.primeR2 (bs 2)).length := by
    simp only [Spec.Rsa.wordsAt, Spec.Rsa.primeR2, Spec.Rsa.toWords, List.length_map, List.length_range]
    rw [(shared.buffers.source 2).length]; rfl
  obtain ⟨wp, wq⟩ := List.append_inj words lenP
  obtain hq : State.addr (a + BitVec.ofNat 32 (8 * Spec.Rsa.primeWords g.pLength)) =
      State.addr a + BitVec.ofNat 64 (8 * Spec.Rsa.primeWords g.pLength) := addr_add (by omega_using [fit, q2])
  rcases hj with rfl | rfl
  · change a.toNat + 8 * Spec.Rsa.primeWords g.pLength ≤ _ ∧
      InRegions _ (State.addr a) (8 * Spec.Rsa.primeWords g.pLength) ∧
      Region.Disjoint ⟨State.addr a, 8 * Spec.Rsa.primeWords g.pLength⟩ _ ∧
      Spec.Rsa.wordsAt s.mem (State.addr a) (Spec.Rsa.primeWords g.pLength) = _
    refine ⟨by omega_using [fit], ?_, sep.sub_left (Region.sub_prefix (by omega_using [])), wp⟩
    simpa only [BitVec.add_zero] using CallLay.inRegions_sub (off := 0) read (by omega_using []) (by omega_using [fit])
  · change (a + BitVec.ofNat 32 (8 * Spec.Rsa.primeWords g.pLength)).toNat + 8 * Spec.Rsa.primeWords g.qLength ≤ _ ∧
      InRegions _ (State.addr (a + BitVec.ofNat 32 (8 * Spec.Rsa.primeWords g.pLength))) (8 * Spec.Rsa.primeWords g.qLength) ∧
      Region.Disjoint ⟨State.addr (a + BitVec.ofNat 32 (8 * Spec.Rsa.primeWords g.pLength)),
        8 * Spec.Rsa.primeWords g.qLength⟩ _ ∧
      Spec.Rsa.wordsAt s.mem (State.addr (a + BitVec.ofNat 32 (8 * Spec.Rsa.primeWords g.pLength)))
        (Spec.Rsa.primeWords g.qLength) = _
    rw [hq]
    refine ⟨?_, CallLay.inRegions_sub read (by omega_using []) (by omega_using [fit]),
      sep.sub_left (Offset.sub_base _ (by omega_using [])), wq⟩
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [fit, q2]), Nat.mod_eq_of_lt (by omega_using [fit, q2])]
    omega_using [fit]

/-! ## The copy and the selection -/

section
variable {g : CrtGeometry} {a : BitVec 32} {j : Fin 6} {v : Nat}

/-- Before the copy. -/
structure CopyIn (g : CrtGeometry) (bs : Fin 7 → List Byte) (j : Fin 6) (v : Nat) (s : State) : Prop where
  shared : CrtShared g bs s
  ready : ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v s
  width : v = Spec.Rsa.primeWords (g.sourceLength j.succ)
  bit : (s.mem.readW (off (State.addr s.sp) 48) 32).toNat ≤ 1

/-- The copy's source, destination and count. -/
def CopyHead (g : CrtGeometry) (a : BitVec 32) (j : Fin 6) (v : Nat) (s z : State) : Prop :=
  z.gpr .r0 = crtN g.base g.words + BitVec.ofNat 32 (arrAt v 4) ∧ z.gpr .r5 = crtN g.base g.words ∧
    z.gpr .lr = BitVec.ofNat 32 (8 * v) ∧ z.gpr .r1 = r2Src g a j ∧ z.mem = s.mem ∧ Rest roundClobbers s z

/-- After the copy. -/
def Copied (g : CrtGeometry) (a : BitVec 32) (j : Fin 6) (v : Nat) (s x : State) : Prop :=
  ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v x ∧
    numAt x.mem (State.addr (crtN g.base g.words)) v 0 = numAt s.mem (State.addr (crtN g.base g.words)) v 0 ∧
    numAt x.mem (State.addr (crtN g.base g.words)) v 4 = (s.mem.read (State.addr (r2Src g a j)) (8 * v)).toNat ∧
    Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s.mem x.mem ∧ Rest roundClobbers s x

theorem CopyIn.slotSep {bs : Fin 7 → List Byte} {s : State} (h : CopyIn g bs j v s) :
    Region.Disjoint ⟨off (State.addr s.sp) 48, 4⟩
      ⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩ :=
  (h.shared.stack.separate.sub_left (Offset.sub_base _ (by decide))).sub_right
    (crt_region_sub_workspace h.shared.buffers.workspace h.shared.buffers.storageFits h.shared.narrow_member)

theorem copyHead_ok {bs : Fin 7 → List Byte} (s : State) (hj : j = 1 ∨ j = 2) (ha : g.r2 = some a)
    (h : CopyIn g bs j v s) :
    WP isa (.block (r2Source (56 + 8 * j.val) ++ lowArgs 4)) s (CopyHead g a j v s) := by
  refine VG.Proof.X25519.Arm.WP.append (r2Source_ok s hj ha h.shared) fun u ⟨src, memU, restU⟩ => ?_
  refine WP.mono (crt_lowArgs_ok u (h.ready.of_mem memU restU ((restU.gpr .r0 (by decide)).trans h.ready.ptr))
    (by decide : 4 < 8)) ?_
  rintro z ⟨d0, d5, dlr, d1, memZ, restZ⟩
  exact ⟨d0, d5, dlr, d1.trans src, memZ.trans memU, (restU.mono (by decide)).trans (restZ.mono (by decide))⟩

theorem copied_ok {bs : Fin 7 → List Byte} (s z : State) (hj : j = 1 ∨ j = 2) (ha : g.r2 = some a)
    (h : CopyIn g bs j v s) (head : CopyHead g a j v s z) :
    WP isa (.seq copyBytes (.block [.mov .r0 (.reg .r5)])) z (Copied g a j v s) := by
  obtain ⟨p0, p5, plr, p1, memZ, restZ⟩ := head
  have ready := h.ready
  obtain ⟨srcFit, srcRead, srcSep, _⟩ := r2Src_given hj ha h.shared
  rw [← h.width] at srcFit srcRead srcSep
  have nw := ready.workspace
  have nNow := nw.nowrap
  obtain hv : 2 ≤ v := ready.width ▸ ready.layout.1
  obtain fits : arrAt v 8 ≤ 8 * workspaceWords g.words := ready.width ▸ ready.layout.2.2.1
  obtain end4 := Nat.le_trans (array_end_le (w := v) (by decide : 4 < 8)) fits
  obtain narrowSub := crt_region_sub_workspace h.shared.buffers.workspace h.shared.buffers.storageFits
    h.shared.narrow_member
  obtain dstAddr : State.addr (crtN g.base g.words + BitVec.ofNat 32 (arrAt v 4)) =
      off (State.addr (crtN g.base g.words)) (arrAt v 4) := addr_add (by omega_using [nNow, end4])
  obtain dstNat : (crtN g.base g.words + BitVec.ofNat 32 (arrAt v 4)).toNat =
      (crtN g.base g.words).toNat + arrAt v 4 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [nNow, end4]), Nat.mod_eq_of_lt (by omega_using [nNow, end4])]
  obtain dstSub : Region.Sub ⟨State.addr (crtN g.base g.words + BitVec.ofNat 32 (arrAt v 4)), 8 * v⟩
      ⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩ := by
    rw [dstAddr]; exact Offset.sub_base _ (by omega_using [end4])
  rw [WP.seq_iff]
  refine WP.mono (copyBuffer_ok z (n := 8 * v) (by omega_using [hv]) srcFit (by rw [dstNat]; omega_using [nNow, end4]) (by omega_using [nNow, end4])
    (by rw [restZ.rd, restZ.wr]; exact srcRead)
    (by
      rw [dstAddr, restZ.wr]
      exact ⟨_, nw.writable, Offset.contains_base _ (by omega_using [end4]) (by omega_using [dstNat])⟩)
    ((srcSep.sub_right narrowSub).sub_right dstSub) p0 p1 plr) ?_
  rintro y ⟨value, frameY, _, restY⟩
  rw [dstAddr] at value frameY
  refine wp_mov (op2_reg _ _) fun x mv => WP.block_nil ?_
  obtain ptrX : x.gpr .r0 = crtN g.base g.words := by
    rw [mv.gpr, restY.gpr .r5 (by decide), p5]
  obtain outside := frame_array_outside (by omega_using [srcFit, dstNat] : arrAt v 4 + 8 * v < 2 ^ 64) frameY
  obtain frameX : Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s.mem x.mem := by
    rw [mv.mem, ← memZ]; exact outside_workspace outside (by omega_using [end4])
  obtain keepsX : Keeps (State.addr (crtN g.base g.words)) (workspaceWords g.words) v 4 s.mem x.mem := by
    rw [mv.mem, ← memZ]
    exact outside_array_prefix_keeps outside (by omega_using [nNow] : 8 * workspaceWords g.words < 2 ^ 64) (by omega_using [])
  obtain restX : Rest roundClobbers s x :=
    restZ.trans ((restY.mono (by decide)).trans (mv.rest (by decide)))
  obtain ⟨readyX, modX⟩ := ready.after_array (by decide : 4 ≠ 0) keepsX frameX restX ptrX
  refine ⟨readyX, modX, ?_, frameX, restX⟩
  change (x.mem.read (off (State.addr (crtN g.base g.words)) (arrAt v 4)) (8 * v)).toNat = _
  rw [mv.mem, value, memZ]

/-- After the selection. -/
def CopyOut (g : CrtGeometry) (a : BitVec 32) (j : Fin 6) (v : Nat) (s t : State) : Prop :=
  ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v t ∧
    numAt t.mem (State.addr (crtN g.base g.words)) v 0 = numAt s.mem (State.addr (crtN g.base g.words)) v 0 ∧
    numAt t.mem (State.addr (crtN g.base g.words)) v 4 =
      (if (s.mem.readW (off (State.addr s.sp) 48) 32).toNat = 0 then 1
        else (s.mem.read (State.addr (r2Src g a j)) (8 * v)).toNat) ∧
    Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s.mem t.mem ∧
    Rest roundClobbers s t

theorem selected_ok {bs : Fin 7 → List Byte} (s x : State) (h : CopyIn g bs j v s) (copied : Copied g a j v s x) :
    WP isa (.seq (smallConst 7 1) (.seq (.block [.ldrSp .r11 48]) (selectArray 4 7 4))) x (CopyOut g a j v s) := by
  obtain ⟨readyX, modX, arr4X, frameX, restX⟩ := copied
  obtain fits : arrAt v 8 ≤ 8 * workspaceWords g.words := readyX.width ▸ readyX.layout.2.2.1
  have nNow := readyX.workspace.nowrap
  have spNow := h.shared.stack.nowrap
  rw [WP.seq_iff]
  refine WP.mono (smallConstLayout_ok x 1 readyX.workspace readyX.layout readyX.width readyX.ptr
    (by decide : 7 < 8) (by decide) (by decide) readyX.stackRead readyX.stackSep readyX.saved) ?_
  rintro w ⟨_, _, number7, outside7, frame7, rest7, ptrW⟩
  obtain keeps7 := outside_array_keeps outside7 (len := workspaceWords g.words) (by omega_using [nNow])
  obtain ⟨readyW, modW⟩ := readyX.after_array (by decide : 7 ≠ 0) keeps7 frame7 rest7 ptrW
  obtain arr4W := (keeps_array_num keeps7 fits
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Proof.Rsa.Mont.Operand 4)
    (by decide)).trans arr4X
  obtain restSW := restX.trans rest7
  obtain frameSW := frameX.trans frame7
  obtain flagW : w.mem.readW (off (State.addr w.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 := by
    rw [restSW.sp]
    exact frameSW.readW (r := ⟨off (State.addr s.sp) 48, 4⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst r; exact h.slotSep) (by decide)
  rw [WP.seq_iff]
  refine wp_loadStack (a := off (State.addr w.sp) 48) (by decide) (addr_add (by rw [restSW.sp]; omega_using [spNow]))
    (by rw [restSW.rd, restSW.wr, restSW.sp]; exact h.shared.stack.read (by decide)) fun q ld => WP.block_nil ?_
  obtain r11 : q.gpr .r11 = s.mem.readW (off (State.addr s.sp) 48) 32 := ld.gpr.trans flagW
  obtain readyQ := readyW.of_mem ld.mem (ld.rest (by decide : Reg.r11 ∈ [Reg.r11]))
    (by rw [ld.other .r0 (by decide)]; exact readyW.ptr)
  refine WP.mono (selectArray_ok q readyQ.workspace readyQ.layout readyQ.width readyQ.ptr
    (by decide : 4 < 8) (by decide : 7 < 8) (by decide : 4 < 8) (by rw [r11]; exact h.bit)
    readyQ.stackRead readyQ.stackSep readyQ.saved) ?_
  rintro t ⟨_, _, valueT, outsideT, frameT, restT, ptrT⟩
  obtain keepsT := outside_array_keeps outsideT (len := workspaceWords g.words) (by omega_using [nNow])
  obtain ⟨readyT, modT⟩ := readyQ.after_array (by decide : 4 ≠ 0) keepsT frameT restT ptrT
  refine ⟨readyT, by rw [modT, ld.mem, modW, modX], ?_, frameSW.trans (by rw [← ld.mem]; exact frameT),
    restSW.trans ((ld.rest (by decide)).trans restT)⟩
  rw [valueT, r11, ld.mem, number7, arr4W]
  rfl

theorem r2Copy_ok {bs : Fin 7 → List Byte} (s : State) (hj : j = 1 ∨ j = 2) (ha : g.r2 = some a)
    (h : CopyIn g bs j v s) : WP isa (r2Copy (56 + 8 * j.val)) s (CopyOut g a j v s) := by
  rw [r2Copy, WP.seq_iff]
  refine WP.mono (copyHead_ok s hj ha h) fun z head => ?_
  apply WP.assoc
  rw [WP.seq_iff]
  exact WP.mono (copied_ok s z hj ha h head) fun x copied => selected_ok s x h copied

end

/-! ## `R² mod X`, given or computed -/

theorem two_pow_mod_three (v : Nat) : 2 ^ (128 * v) % 3 = 1 := by
  rw [show 128 * v = 2 * (64 * v) by omega_using [], Nat.pow_mul, Nat.pow_mod]
  simp

theorem r2Given_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {a : BitVec 32} {j : Fin 6}
    (hj : j = 1 ∨ j = 2) (ha : g.r2 = some a) {v M : Nat} (shared : CrtShared g bs s)
    (ready : ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v s)
    (narrow : v = narrowWords (g.sourceLength j.succ) g.words)
    (bit : (s.mem.readW (off (State.addr s.sp) 48) 32).toNat ≤ 1)
    (valid : (s.mem.readW (off (State.addr s.sp) 48) 32).toNat ≠ 0 → 1 < Spec.Rsa.os2ip (bs j.succ))
    (modulus : numAt s.mem (State.addr (crtN g.base g.words)) v 0 = M)
    (safe : M = safePrime (s.mem.readW (off (State.addr s.sp) 48) 32).toNat (Spec.Rsa.os2ip (bs j.succ))) :
    WP isa (r2Given (56 + 8 * j.val)) s fun t =>
      ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v t ∧
      numAt t.mem (State.addr (crtN g.base g.words)) v 0 = M ∧
      numAt t.mem (State.addr (crtN g.base g.words)) v 4 = 2 ^ (128 * v) % M ∧
      Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  obtain hv : 2 ≤ v := ready.width ▸ ready.layout.1
  obtain ⟨_, le, _, _, _, _, _⟩ := shared.narrow_fits j hj
  obtain words : g.words ≤ 128 := (crt_width_valid shared.buffers.lengthValid).2.1
  rw [r2Given, WP.seq_iff]
  refine WP.mono (r2WidthTest_ok s (j := j) shared ready) ?_
  rintro u ⟨z, memU, restU⟩
  obtain readyU := ready.of_mem memU restU ((restU.gpr .r0 (by decide)).trans ready.ptr)
  obtain sharedU := shared.of_mem memU restU
  obtain flagU : u.mem.readW (off (State.addr u.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 := by
    rw [memU, restU.sp]
  by_cases same : v = (g.sourceLength j.succ + 7) / 8
  · refine WP.ite true (by rw [VG.Proof.X25519.Arm.eval_eq, z, decide_eq_true same]) (fun _ => ?_) (by simp)
    obtain width : v = Spec.Rsa.primeWords (g.sourceLength j.succ) := by
      unfold Spec.Rsa.primeWords Spec.Rsa.modulusWords; omega_using [hv, same]
    refine WP.mono (r2Copy_ok u hj ha ⟨sharedU, readyU, width, by rw [flagU]; exact bit⟩) ?_
    rintro t ⟨readyT, modT, valueT, frameT, restT⟩
    refine ⟨readyT, by rw [modT, memU]; exact modulus, ?_, by rw [← memU]; exact frameT,
      (restU.mono (by decide)).trans restT⟩
    rw [valueT, flagU, safe, memU]
    by_cases b0 : (s.mem.readW (off (State.addr s.sp) 48) 32).toNat = 0
    · simp only [b0, ↓reduceIte, safePrime]
      exact (two_pow_mod_three v).symm
    · simp only [b0, ↓reduceIte, safePrime]
      obtain ⟨_, _, _, given⟩ := r2Src_given hj ha shared
      obtain large := valid b0
      obtain len : (bs j.succ).length = g.sourceLength j.succ := (shared.buffers.source j.succ).length
      rw [← width] at given
      unfold Spec.Rsa.primeR2 at given
      rw [len, ← width] at given
      refine read_of_toWords given ?_
      obtain lt := VG.Proof.Bignum.os2ip_lt (bs j.succ)
      rw [len, VG.Proof.Bignum.pow256_eq] at lt
      have : 2 ^ (8 * g.sourceLength j.succ) ≤ 2 ^ (64 * v) := Nat.pow_le_pow_right (by decide) (by omega_arith)
      have := Nat.mod_lt (2 ^ (128 * v)) (by omega_using [large] : 0 < Spec.Rsa.os2ip (bs j.succ))
      omega_arith
  · refine WP.ite false (by rw [VG.Proof.X25519.Arm.eval_eq, z, decide_eq_false same]) (by simp) (fun _ => ?_)
    refine WP.mono (r2_ok u readyU (by omega_using [narrow, le, words])) ?_
    rintro t ⟨done, valueT, modT, frameT, restT⟩
    obtain modU : numAt u.mem (State.addr (crtN g.base g.words)) v 0 = M := by rw [memU]; exact modulus
    rw [modU] at valueT modT
    refine ⟨done.toReady (by rw [modT]; rw [← modU]; exact readyU.modulus), modT, valueT,
      by rw [← memU]; exact frameT, (restU.mono (by decide)).trans restT⟩

/-- `narrowPrime` with the given `R² mod X`. -/
theorem crt_narrowPrimeGiven_ok {g : CrtGeometry} {bs : Fin 7 → List Byte} {a : BitVec 32} (j : Fin 6)
    (s : State) (hj : j = 1 ∨ j = 2) (ha : g.r2 = some a) (h : CrtPrimeIn g bs j s) :
    WP isa (narrowPrimeGiven (56 + 8 * j.val)) s (NarrowPrimePost (crtN g.base g.words) (workspaceWords g.words)
      (narrowWords (g.sourceLength j.succ) g.words) (bs j.succ) s) := by
  obtain ⟨shared, input⟩ := h
  rw [narrowPrimeGiven, WP.seq_iff]
  refine WP.mono (crt_narrowPrimeInv_ok s input) ?_
  rintro u ⟨readyU, modU, odd, flagU, frameU, restU⟩
  obtain sharedU := shared.after_narrow (frameU.mono (by simp)) restU
  obtain narrowSub := crt_region_sub_workspace shared.buffers.workspace shared.buffers.storageFits shared.narrow_member
  refine WP.mono (r2Given_ok u (j := j) hj ha sharedU readyU rfl (by rw [flagU]; exact input.bit)
    (by rw [flagU]; exact fun ne => (input.valid ne).1) modU (by rw [flagU])) ?_
  rintro t ⟨readyT, modT, r2T, frameT, restT⟩
  obtain restST := restU.trans restT
  refine ⟨readyT, modT, odd, r2T, ?_, frameU.trans frameT, restST⟩
  rw [restST.sp]
  obtain keep := (frameU.trans frameT).readW (a := off (State.addr s.sp) 48) (w := 32)
    (r := ⟨off (State.addr s.sp) 48, 4⟩) (Region.contains_self _ _)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact (shared.stack.separate.sub_left (Offset.sub_base _ (by decide))).sub_right narrowSub) (by decide)
  exact keep

end VG.Proof.Bignum.Arm

end

end

/-! # Preparing a factor with its given `R² mod p` is constant-time

The copy's addresses and count are the factor's given value's, the narrow
workspace's and its width, which both runs share; the selection and
`R² mod X` computed from 1 are constant-time; the width test reads only
public lengths. -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt)
open VG.Proof.X25519.Arm (Rest)

section
variable {g : CrtGeometry} {a : BitVec 32} {j : Fin 6} {v : Nat}

/-- A block that only moves registers. -/
theorem moveBlock_ct {P : State → State → Prop} (d n : Reg) :
    RelCT isa P (.block [.mov d (.reg n)]) (fun _ _ => True) :=
  single_ct (fun _ _ _ => by simp [addrs]) (fun _ _ _ _ _ _ _ => trivial)

/-- Ready for the selection: the narrow workspace, and frame slot 48 readable. -/
def SelectIn (g : CrtGeometry) (v : Nat) (s : State) : Prop :=
  ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v s ∧
    InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 48) 4 ∧ s.sp.toNat + 52 ≤ 2 ^ 32

theorem selectIn_smallConst (x : State) (h : SelectIn g v x) :
    WP isa (smallConst 7 1) x (SelectIn g v) := by
  obtain ⟨h, read, fit⟩ := h
  have fits : arrAt v 8 ≤ 8 * workspaceWords g.words := h.width ▸ h.layout.2.2.1
  have nNow := h.workspace.nowrap
  refine WP.mono (smallConstLayout_ok x 1 h.workspace h.layout h.width h.ptr
    (by decide : 7 < 8) (by decide) (by decide) h.stackRead h.stackSep h.saved) ?_
  rintro w ⟨_, _, _, outside7, frame7, rest7, ptrW⟩
  exact ⟨(h.after_array (by decide : 7 ≠ 0) (outside_array_keeps outside7 (len := workspaceWords g.words) (by omega_using [nNow]))
    frame7 rest7 ptrW).1, by rw [rest7.rd, rest7.wr, rest7.sp]; exact read, by rw [rest7.sp]; exact fit⟩

theorem selectPart_ct :
    RelCT isa (fun s t => SelectIn g v s ∧ SelectIn g v t ∧ s.sp = t.sp)
      (.seq (smallConst 7 1) (.seq (.block [.ldrSp .r11 48]) (selectArray 4 7 4))) (fun _ _ => True) := by
  have small := (smallConst_ct (base := crtN g.base g.words) (len := workspaceWords g.words) (w := v) (o := 7) 1
    (by decide) (by decide) (by decide)).mono (P' := fun (s t : State) => SelectIn g v s ∧ SelectIn g v t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ _ => trivial)
  have load : RelCT isa (fun s t => SelectIn g v s ∧ SelectIn g v t ∧ s.sp = t.sp) (.block [.ldrSp .r11 48])
      (fun _ _ => True) :=
    (loadStack_ct .r11 48).mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have loadWP (s : State) (h : SelectIn g v s) : WP isa (.block [.ldrSp .r11 48]) s (SelectIn g v) := by
    refine wp_loadStack (a := off (State.addr s.sp) 48) (by decide) (addr_add (by have := h.2.2; omega_using [this])) h.2.1
      fun t ld => WP.block_nil ?_
    exact ⟨h.1.of_mem ld.mem (ld.rest (by decide : Reg.r11 ∈ [Reg.r11]))
      (by rw [ld.other .r0 (by decide)]; exact h.1.ptr), by rw [ld.rd, ld.wr, ld.sp]; exact h.2.1,
      by rw [ld.sp]; exact h.2.2⟩
  have select := selectArray_ct (base := crtN g.base g.words) (len := workspaceWords g.words) (w := v)
    (by decide : 4 < 8) (by decide : 7 < 8) (by decide : 4 < 8)
  exact crt_seq_ct small (fun s h => selectIn_smallConst s h) (fun s h => selectIn_smallConst s h)
    (crt_seq_ct load loadWP loadWP (select.mono
      (fun _ _ h => ⟨⟨h.1.1.workspace, h.1.1.layout, h.1.1.width, h.1.1.ptr⟩,
        ⟨h.2.1.1.workspace, h.2.1.1.layout, h.2.1.1.width, h.2.1.1.ptr⟩, h.2.2⟩) (fun _ _ _ => trivial)))

def R0Eq (s t : State) : Prop := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0

/-- An instruction that keeps r0 and accesses memory only through r0 and the stack. -/
def r0Instruction : Instr → Bool
  | .ldr t n _ => decide (n = .r0) && decide (t ≠ .r0)
  | .ldrSp t _ => decide (t ≠ .r0)
  | .dp _ d _ _ => decide (d ≠ .r0)
  | .mov d _ => decide (d ≠ .r0)
  | .cmp _ _ => true
  | _ => false

theorem r0Instruction_ct {i : Instr} (hi : r0Instruction i = true) :
    RelCT isa R0Eq (.block [i]) R0Eq := by
  apply single_ct
  · intro s t h
    cases i <;> simp_all [r0Instruction, addrs, R0Eq]
  · intro s t u v h e1 e2
    have keep : clobbers i .r0 = false := by
      cases i <;> simp_all [r0Instruction, clobbers, dstOf] <;> first | exact Ne.symm hi | exact (Ne.symm hi.2)
    exact ⟨(exec_sp e1).trans (h.1.trans (exec_sp e2).symm),
      (exec_gpr keep e1).trans (h.2.trans (exec_gpr keep e2).symm)⟩

theorem r0Block_keep_ct (code : List Instr) (h : code.all r0Instruction = true) :
    RelCT isa R0Eq (.block code) R0Eq := by
  induction code with
  | nil => exact RelCT.block_nil (fun _ _ h => h)
  | cons i rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    exact RelCT.block_append ((r0Instruction_ct h.1).seq (ih h.2))

theorem r2CopyHead_ct {bs1 bs2 : Fin 7 → List Byte} (hj : j = 1 ∨ j = 2) :
    RelCT isa (fun s t => CopyIn g bs1 j v s ∧ CopyIn g bs2 j v t ∧ s.sp = t.sp)
      (.block (r2Source (56 + 8 * j.val) ++ lowArgs 4)) (fun _ _ => True) := by
  have split : r2Source (56 + 8 * j.val) ++ lowArgs 4 =
      (r2Source (56 + 8 * j.val) ++ (lowArgs 4).dropLast) ++ [.mov .r0 (.reg .r4)] := by
    simp [lowArgs]
  rw [split]
  refine RelCT.block_append (((r0Block_keep_ct _ ?_).mono (fun _ _ h => ⟨h.2.2, ?_⟩) (fun _ _ _ => trivial)).seq
    (moveBlock_ct .r0 .r4))
  · rcases hj with rfl | rfl <;> decide
  · exact h.1.ready.ptr.trans h.2.1.ready.ptr.symm

theorem r2Copy_ct {bs1 bs2 : Fin 7 → List Byte} (hj : j = 1 ∨ j = 2) (ha : g.r2 = some a) :
    RelCT isa (fun s t => CopyIn g bs1 j v s ∧ CopyIn g bs2 j v t ∧ s.sp = t.sp)
      (r2Copy (56 + 8 * j.val)) (fun _ _ => True) := by
  let H := fun (bs : Fin 7 → List Byte) (z : State) => ∃ s0, CopyIn g bs j v s0 ∧ CopyHead g a j v s0 z
  let C := fun (bs : Fin 7 → List Byte) (x : State) => ∃ s0, CopyIn g bs j v s0 ∧ Copied g a j v s0 x
  have headWP (s : State) {bs : Fin 7 → List Byte} (h : CopyIn g bs j v s) :
      WP isa (.block (r2Source (56 + 8 * j.val) ++ lowArgs 4)) s (H bs) :=
    (copyHead_ok s hj ha h).mono fun z hz => ⟨s, h, hz⟩
  have copyCT : RelCT isa (fun s t => H bs1 s ∧ H bs2 t ∧ s.sp = t.sp)
      (.seq copyBytes (.block [.mov .r0 (.reg .r5)])) (fun _ _ => True) := by
    refine RelCT.seq (R := fun _ _ => True) ?_ (moveBlock_ct .r0 .r5)
    intro s t tr1 tr2 u w h e1 e2
    obtain ⟨⟨_, _, ⟨s0, s5, slr, s1, _⟩⟩, ⟨_, _, ⟨t0, t5, tlr, t1, _⟩⟩, _⟩ := h
    exact ⟨copyBytes_ct s t tr1 tr2 u w trivial trivial
      ⟨s0.trans t0.symm, s1.trans t1.symm, slr.trans tlr.symm⟩ e1 e2, trivial⟩
  have copyWP (z : State) {bs : Fin 7 → List Byte} (h : H bs z) :
      WP isa (.seq copyBytes (.block [.mov .r0 (.reg .r5)])) z (C bs) := by
    obtain ⟨s0, h0, head⟩ := h
    exact (copied_ok s0 z hj ha h0 head).mono fun x hx => ⟨s0, h0, hx⟩
  have selectIn (x : State) {bs : Fin 7 → List Byte} (h : C bs x) : SelectIn g v x := by
    obtain ⟨s0, h0, ready, _, _, _, rest⟩ := h
    have spNow := h0.shared.stack.nowrap
    exact ⟨ready, by rw [rest.rd, rest.wr, rest.sp]; exact h0.shared.stack.read (by decide),
      by rw [rest.sp]; omega_using [spNow]⟩
  rw [r2Copy]
  exact crt_seq_ct (r2CopyHead_ct hj) (fun s h => headWP s h) (fun s h => headWP s h)
    (crt_seq_ct copyCT (fun z h => copyWP z h) (fun z h => copyWP z h)
      (selectPart_ct.mono (fun _ _ h => ⟨selectIn _ h.1, selectIn _ h.2.1, h.2.2⟩) (fun _ _ _ => trivial))).assoc

/-- Before `r2Given`. -/
def GivenIn (g : CrtGeometry) (bs : Fin 7 → List Byte) (j : Fin 6) (s : State) : Prop :=
  CrtShared g bs s ∧
    ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) (narrowWords (g.sourceLength j.succ) g.words) s ∧
    (s.mem.readW (off (State.addr s.sp) 48) 32).toNat ≤ 1

theorem r2Given_ct {bs1 bs2 : Fin 7 → List Byte} (hj : j = 1 ∨ j = 2) (ha : g.r2 = some a) :
    RelCT isa (fun s t => GivenIn g bs1 j s ∧ GivenIn g bs2 j t ∧ s.sp = t.sp)
      (r2Given (56 + 8 * j.val)) (fun _ _ => True) := by
  let v := narrowWords (g.sourceLength j.succ) g.words
  let T := fun (bs : Fin 7 → List Byte) (u : State) =>
    GivenIn g bs j u ∧ u.z = decide (v = (g.sourceLength j.succ + 7) / 8)
  have testWP (s : State) {bs : Fin 7 → List Byte} (h : GivenIn g bs j s) :
      WP isa (.block (r2WidthTest (56 + 8 * j.val + 4))) s (T bs) := by
    refine (r2WidthTest_ok s h.1 h.2.1).mono ?_
    rintro u ⟨z, mem, rest⟩
    exact ⟨⟨h.1.of_mem mem rest, h.2.1.of_mem mem rest ((rest.gpr .r0 (by decide)).trans h.2.1.ptr),
      by rw [mem, rest.sp]; exact h.2.2⟩, z⟩
  have test : RelCT isa (fun s t => GivenIn g bs1 j s ∧ GivenIn g bs2 j t ∧ s.sp = t.sp)
      (.block (r2WidthTest (56 + 8 * j.val + 4))) (fun _ _ => True) := by
    refine (r0Block_keep_ct _ ?_).mono (fun _ _ h => ⟨h.2.2, h.1.2.1.ptr.trans h.2.1.2.1.ptr.symm⟩)
      (fun _ _ _ => trivial)
    rcases hj with rfl | rfl <;> decide
  rw [r2Given]
  refine crt_seq_ct test (fun s h => testWP s h) (fun s h => testWP s h)
    (crt_ite_ct (cond := decide (v = (g.sourceLength j.succ + 7) / 8))
      (fun s h => by rw [VG.Proof.X25519.Arm.eval_eq, h.2]) (fun s h => by rw [VG.Proof.X25519.Arm.eval_eq, h.2])
      (fun hc => ?_) (fun _ => ?_))
  · have same := of_decide_eq_true hc
    have copyIn (s : State) {bs : Fin 7 → List Byte} (h : T bs s) : CopyIn g bs j v s := by
      have hv : 2 ≤ v := by have := h.1.2.1.layout.1; rw [h.1.2.1.width] at this; exact this
      refine ⟨h.1.1, h.1.2.1, ?_, h.1.2.2⟩
      unfold Spec.Rsa.primeWords Spec.Rsa.modulusWords; omega_using [same, hv]
    exact (r2Copy_ct hj ha).mono (fun _ _ h => ⟨copyIn _ h.1, copyIn _ h.2.1, h.2.2⟩) (fun _ _ _ => trivial)
  · exact relCT_of_pre fun s _ h => (r2_ct (by
      obtain ⟨_, le, _, _, _, _, _⟩ := h.1.1.1.narrow_fits j hj
      have : g.words ≤ 128 := (crt_width_valid h.1.1.1.buffers.lengthValid).2.1
      omega_using [le, this])).mono (fun _ _ h => ⟨h.1.1.2.1, h.2.1.1.2.1, h.2.2⟩) (fun _ _ _ => trivial)

theorem crt_narrowPrimeGiven_ct {bs1 bs2 : Fin 7 → List Byte} (hj : j = 1 ∨ j = 2) (ha : g.r2 = some a) :
    RelCT isa (fun s t => CrtPrimeIn g bs1 j s ∧ CrtPrimeIn g bs2 j t ∧ s.sp = t.sp)
      (narrowPrimeGiven (56 + 8 * j.val)) (fun _ _ => True) := by
  have invWP (s : State) {bs : Fin 7 → List Byte} (h : CrtPrimeIn g bs j s) :
      WP isa (narrowPrimeInv (56 + 8 * j.val)) s (GivenIn g bs j) := by
    refine (crt_narrowPrimeInv_ok s h.2).mono ?_
    rintro u ⟨readyU, _, _, flagU, frameU, restU⟩
    exact ⟨h.1.after_narrow (frameU.mono (by simp)) restU, readyU, by rw [flagU]; exact h.2.bit⟩
  rw [narrowPrimeGiven]
  exact crt_seq_ct (crt_narrowPrimeInv_ct.mono (fun _ _ h => ⟨h.1.2, h.2.1.2, h.2.2⟩) (fun _ _ _ => trivial))
    (fun s h => invWP s h) (fun s h => invWP s h) (r2Given_ct hj ha)

end

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.CrtContract`, which only this module used -/

section

/-! ### `Bignum.Arm.CrtContractInput`, which only this module used -/

section

/-! # Native private-CRT arguments satisfy the shared API's buffer contract -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

def crtCallGeometry (s : State) : CrtGeometry where
  base := stackArg s 12
  output := s.gpr .r0
  modulus := s.gpr .r2
  input := stackArg s 0
  p := stackArg s 2
  q := stackArg s 4
  dp := stackArg s 6
  dq := stackArg s 8
  qi := stackArg s 10
  size := 8 * (stackArg s 13).toNat
  length := (s.gpr .r3).toNat
  pLength := (stackArg s 3).toNat
  qLength := (stackArg s 5).toNat

def crtCallBytes (s : State) (i : Fin 7) : List Byte :=
  Spec.Rsa.bytesAt s.mem (State.addr ((crtCallGeometry s).source i)) ((crtCallGeometry s).sourceLength i)

theorem crt_contract_pre (s : State) (h : (Proof.Rsa.privateCrtContract abi 56).pre s) :
    CrtFnInput (crtCallGeometry s) (crtCallBytes s) s := by
  sig_pre [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
  have argAddr : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  rw [argAddr] at h
  sig_split h
  rename_i stackFit argFit rd wr _ _ _ _ _ _ _ outWs _
    nWs inputWs pWs qWs dpWs dqWs qiWs wsArgs
    stackOut stackN stackInput stackP stackQ stackDp stackDq stackQi stackWs stackArgs
    outFit nFit inputFit pFit qFit dpFit dqFit qiFit wsFit
    valid outLen inputLen pPositive pShort qPositive qShort dpLen qiLen dqLen
  have space := h
  rw [outLen] at wr outWs stackOut outFit
  rw [inputLen, dpLen, qiLen, dqLen] at rd
  rw [inputLen] at inputWs stackInput inputFit
  rw [dpLen] at dpWs stackDp dpFit
  rw [qiLen] at qiWs stackQi qiFit
  rw [dqLen] at dqWs stackDq dqFit
  have frame : FrameStack.belowA s.sp 56 = ⟨State.addr s.sp - BitVec.ofNat 64 56, 56⟩ := by
    unfold FrameStack.belowA
    rw [FrameStack.addr_sub' stackFit]
  have argRead (i : Nat) (hi : i < 14) :
      s.mem.readW (VG.Proof.Mont.off (State.addr s.sp) (4 * i)) 32 = stackArg s i := by
    unfold stackArg stackArgAddr VG.Proof.Mont.off
    rw [addr_add (by omega_arith : s.sp.toNat + 4 * i < 2 ^ 32)]
  refine {
    workspace := ⟨?_, ?_⟩, lengthValid := valid,
    storageFits := Nat.le_trans (crt_layout_fits valid) (Nat.mul_le_mul_left 8 space),
    pPositive := pPositive, pShort := pShort, qPositive := qPositive, qShort := qShort,
    r2 := (fun _ ha => by cases ha),
    source := ?_, sourceSeparate := ?_, outputFits := outFit, write := ?_, outputSeparate := ?_,
    output := rfl, modulus := rfl, count := ?_, stackFit := stackFit, argFit := argFit,
    argRead := ?_, pointer := ?_, length := ?_, workspaceArg := argRead 12 (by decide),
    stackWorkspace := ?_, argsWorkspace := ?_, stackSource := ?_, stackOutput := ?_, stackArgs := ?_ }
  · simpa only [crtCallGeometry, Nat.mul_comm] using wsFit
  · rw [wr]; simp [crtCallGeometry, State.addr, Nat.mul_comm]
  · intro i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 from by omega_arith) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨nFit, ?_, rfl⟩
      change InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2)) (s.gpr .r3).toNat
      exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
    · refine ⟨inputFit, ?_, rfl⟩
      change InRegions (s.rd ++ s.wr) (State.addr (stackArg s 0)) (s.gpr .r3).toNat
      exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
    · refine ⟨pFit, ?_, rfl⟩
      change InRegions (s.rd ++ s.wr) (State.addr (stackArg s 2)) (stackArg s 3).toNat
      exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
    · refine ⟨qFit, ?_, rfl⟩
      change InRegions (s.rd ++ s.wr) (State.addr (stackArg s 4)) (stackArg s 5).toNat
      exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
    · refine ⟨dpFit, ?_, rfl⟩
      change InRegions (s.rd ++ s.wr) (State.addr (stackArg s 6)) (stackArg s 3).toNat
      exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
    · refine ⟨dqFit, ?_, rfl⟩
      change InRegions (s.rd ++ s.wr) (State.addr (stackArg s 8)) (stackArg s 5).toNat
      exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
    · refine ⟨qiFit, ?_, rfl⟩
      change InRegions (s.rd ++ s.wr) (State.addr (stackArg s 10)) (stackArg s 3).toNat
      exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  · intro i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 from by omega_arith) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change Region.Disjoint ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ ⟨State.addr (stackArg s 12), 8 * (stackArg s 13).toNat⟩
      simpa only [State.addr, Nat.mul_comm] using nWs
    · change Region.Disjoint ⟨State.addr (stackArg s 0), (s.gpr .r3).toNat⟩ ⟨State.addr (stackArg s 12), 8 * (stackArg s 13).toNat⟩
      simpa only [State.addr, Nat.mul_comm] using inputWs
    · change Region.Disjoint ⟨State.addr (stackArg s 2), (stackArg s 3).toNat⟩ ⟨State.addr (stackArg s 12), 8 * (stackArg s 13).toNat⟩
      simpa only [State.addr, Nat.mul_comm] using pWs
    · change Region.Disjoint ⟨State.addr (stackArg s 4), (stackArg s 5).toNat⟩ ⟨State.addr (stackArg s 12), 8 * (stackArg s 13).toNat⟩
      simpa only [State.addr, Nat.mul_comm] using qWs
    · change Region.Disjoint ⟨State.addr (stackArg s 6), (stackArg s 3).toNat⟩ ⟨State.addr (stackArg s 12), 8 * (stackArg s 13).toNat⟩
      simpa only [State.addr, Nat.mul_comm] using dpWs
    · change Region.Disjoint ⟨State.addr (stackArg s 8), (stackArg s 5).toNat⟩ ⟨State.addr (stackArg s 12), 8 * (stackArg s 13).toNat⟩
      simpa only [State.addr, Nat.mul_comm] using dqWs
    · change Region.Disjoint ⟨State.addr (stackArg s 10), (stackArg s 3).toNat⟩ ⟨State.addr (stackArg s 12), 8 * (stackArg s 13).toNat⟩
      simpa only [State.addr, Nat.mul_comm] using qiWs
  · exact ⟨_, by rw [wr]; exact List.mem_cons_self, Region.contains_self _ _⟩
  · simpa only [crtCallGeometry, State.addr, Nat.mul_comm] using outWs.symm
  · simp [crtCallGeometry]
  · exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  · intro i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 from by omega_arith) with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only [crtCallGeometry, CrtGeometry.source]
    · exact argRead 0 (by decide)
    · exact argRead 2 (by decide)
    · exact argRead 4 (by decide)
    · exact argRead 6 (by decide)
    · exact argRead 8 (by decide)
    · exact argRead 10 (by decide)

  · intro i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 from by omega_arith) with rfl | rfl | rfl | rfl | rfl | rfl
    · change s.mem.readW (VG.Proof.Mont.off (State.addr s.sp) (4 * 1)) 32 = BitVec.ofNat 32 (s.gpr .r3).toNat
      rw [argRead 1 (by decide)]
      rw [← inputLen]
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · change s.mem.readW (VG.Proof.Mont.off (State.addr s.sp) (4 * 3)) 32 = BitVec.ofNat 32 (stackArg s 3).toNat
      rw [argRead 3 (by decide)]
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · change s.mem.readW (VG.Proof.Mont.off (State.addr s.sp) (4 * 5)) 32 = BitVec.ofNat 32 (stackArg s 5).toNat
      rw [argRead 5 (by decide)]
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · change s.mem.readW (VG.Proof.Mont.off (State.addr s.sp) (4 * 7)) 32 = BitVec.ofNat 32 (stackArg s 3).toNat
      rw [argRead 7 (by decide)]
      rw [← dpLen]
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · change s.mem.readW (VG.Proof.Mont.off (State.addr s.sp) (4 * 9)) 32 = BitVec.ofNat 32 (stackArg s 5).toNat
      rw [argRead 9 (by decide)]
      rw [← dqLen]
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · change s.mem.readW (VG.Proof.Mont.off (State.addr s.sp) (4 * 11)) 32 = BitVec.ofNat 32 (stackArg s 3).toNat
      rw [argRead 11 (by decide)]
      rw [← qiLen]
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [frame]; simpa only [crtCallGeometry, State.addr, Nat.mul_comm] using stackWs
  · simpa only [crtCallGeometry, State.addr, Nat.mul_comm] using wsArgs.symm
  · intro i
    rw [frame]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 from by omega_arith) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact stackN
    · exact stackInput
    · exact stackP
    · exact stackQ
    · exact stackDp
    · exact stackDq
    · exact stackQi
  · rw [frame]; exact stackOut
  · rw [frame]; exact stackArgs

end VG.Proof.Bignum.Arm

/-! # `vg_rsa_private_crt_precomputed`'s arguments as the CRT's input

`vg_rsa_private_crt`'s (`crt_contract_pre`), and the factors' `R²` at its
argument 14. -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

def crtCallGeometryP (s : State) : CrtGeometry := { crtCallGeometry s with r2 := some (stackArg s 14) }

theorem crt_contract_preP (s : State) (h : (Proof.Rsa.privateCrtPrecomputedContract abi 56).pre s) :
    CrtFnInput (crtCallGeometryP s) (crtCallBytes s) s := by
  sig_pre [Proof.Rsa.privateCrtPrecomputedContract, Proof.Rsa.privateCrtPrecomputedSig, Proof.Rsa.privateCrtSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr] at h
  have argAddr : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  rw [argAddr] at h
  sig_split h
  rename_i stackFit argFit rd wr _ _ _ _ _ _ _ outWs outR2 outArgs
    nWs inputWs pWs qWs dpWs dqWs qiWs wsR2 wsArgs
    stackOut stackN stackInput stackP stackQ stackDp stackDq stackQi stackWs stackR2 stackArgs
    outFit nFit inputFit pFit qFit dpFit dqFit qiFit wsFit r2Fit
    valid outLen inputLen pPositive pShort qPositive qShort dpLen qiLen dqLen space
    r2Len r2Words
  rw [outLen] at wr outWs stackOut outFit outR2 outArgs
  rw [inputLen, dpLen, qiLen, dqLen] at rd
  rw [inputLen] at inputWs stackInput inputFit
  rw [dpLen] at dpWs stackDp dpFit
  rw [qiLen] at qiWs stackQi qiFit
  rw [dqLen] at dqWs stackDq dqFit
  have frame : FrameStack.belowA s.sp 56 = ⟨State.addr s.sp - BitVec.ofNat 64 56, 56⟩ := by
    unfold FrameStack.belowA
    rw [FrameStack.addr_sub' stackFit]
  have argRead (i : Nat) (hi : i < 16) :
      s.mem.readW (VG.Proof.Mont.off (State.addr s.sp) (4 * i)) 32 = stackArg s i := by
    unfold stackArg stackArgAddr VG.Proof.Mont.off
    rw [addr_add (by omega_arith : s.sp.toNat + 4 * i < 2 ^ 32)]
  refine {
    workspace := ⟨?_, ?_⟩, lengthValid := valid,
    storageFits := Nat.le_trans (crt_layout_fits valid) (Nat.mul_le_mul_left 8 space),
    pPositive := pPositive, pShort := pShort, qPositive := qPositive, qShort := qShort,
    r2 := ?_,
    source := ?_, sourceSeparate := ?_, outputFits := outFit, write := ?_, outputSeparate := ?_,
    output := rfl, modulus := rfl, count := ?_, stackFit := stackFit, argFit := by omega_using [argFit],
    argRead := ?_, pointer := ?_, length := ?_, workspaceArg := argRead 12 (by decide),
    stackWorkspace := ?_, argsWorkspace := ?_, stackSource := ?_, stackOutput := ?_, stackArgs := ?_ }
  · simpa only [crtCallGeometryP, crtCallGeometry, Nat.mul_comm] using wsFit
  · rw [wr]; simp [crtCallGeometryP, crtCallGeometry, State.addr, Nat.mul_comm]
  · intro i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 from by omega_arith) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨nFit, ?_, rfl⟩
      change InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2)) (s.gpr .r3).toNat
      exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
    · refine ⟨inputFit, ?_, rfl⟩
      change InRegions (s.rd ++ s.wr) (State.addr (stackArg s 0)) (s.gpr .r3).toNat
      exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
    · refine ⟨pFit, ?_, rfl⟩
      change InRegions (s.rd ++ s.wr) (State.addr (stackArg s 2)) (stackArg s 3).toNat
      exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
    · refine ⟨qFit, ?_, rfl⟩
      change InRegions (s.rd ++ s.wr) (State.addr (stackArg s 4)) (stackArg s 5).toNat
      exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
    · refine ⟨dpFit, ?_, rfl⟩
      change InRegions (s.rd ++ s.wr) (State.addr (stackArg s 6)) (stackArg s 3).toNat
      exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
    · refine ⟨dqFit, ?_, rfl⟩
      change InRegions (s.rd ++ s.wr) (State.addr (stackArg s 8)) (stackArg s 5).toNat
      exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
    · refine ⟨qiFit, ?_, rfl⟩
      change InRegions (s.rd ++ s.wr) (State.addr (stackArg s 10)) (stackArg s 3).toNat
      exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  · intro i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 from by omega_arith) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change Region.Disjoint ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ ⟨State.addr (stackArg s 12), 8 * (stackArg s 13).toNat⟩
      simpa only [State.addr, Nat.mul_comm] using nWs
    · change Region.Disjoint ⟨State.addr (stackArg s 0), (s.gpr .r3).toNat⟩ ⟨State.addr (stackArg s 12), 8 * (stackArg s 13).toNat⟩
      simpa only [State.addr, Nat.mul_comm] using inputWs
    · change Region.Disjoint ⟨State.addr (stackArg s 2), (stackArg s 3).toNat⟩ ⟨State.addr (stackArg s 12), 8 * (stackArg s 13).toNat⟩
      simpa only [State.addr, Nat.mul_comm] using pWs
    · change Region.Disjoint ⟨State.addr (stackArg s 4), (stackArg s 5).toNat⟩ ⟨State.addr (stackArg s 12), 8 * (stackArg s 13).toNat⟩
      simpa only [State.addr, Nat.mul_comm] using qWs
    · change Region.Disjoint ⟨State.addr (stackArg s 6), (stackArg s 3).toNat⟩ ⟨State.addr (stackArg s 12), 8 * (stackArg s 13).toNat⟩
      simpa only [State.addr, Nat.mul_comm] using dpWs
    · change Region.Disjoint ⟨State.addr (stackArg s 8), (stackArg s 5).toNat⟩ ⟨State.addr (stackArg s 12), 8 * (stackArg s 13).toNat⟩
      simpa only [State.addr, Nat.mul_comm] using dqWs
    · change Region.Disjoint ⟨State.addr (stackArg s 10), (stackArg s 3).toNat⟩ ⟨State.addr (stackArg s 12), 8 * (stackArg s 13).toNat⟩
      simpa only [State.addr, Nat.mul_comm] using qiWs
  · exact ⟨_, by rw [wr]; exact List.mem_cons_self, Region.contains_self _ _⟩
  · simpa only [crtCallGeometryP, crtCallGeometry, State.addr, Nat.mul_comm] using outWs.symm
  · simp [crtCallGeometryP, crtCallGeometry]
  · exact ⟨⟨State.addr s.sp, 64⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]),
      by simp [Region.Contains]⟩
  · intro i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 from by omega_arith) with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only [crtCallGeometryP, crtCallGeometry, CrtGeometry.source]
    · exact argRead 0 (by decide)
    · exact argRead 2 (by decide)
    · exact argRead 4 (by decide)
    · exact argRead 6 (by decide)
    · exact argRead 8 (by decide)
    · exact argRead 10 (by decide)

  · intro i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 from by omega_arith) with rfl | rfl | rfl | rfl | rfl | rfl
    · change s.mem.readW (VG.Proof.Mont.off (State.addr s.sp) (4 * 1)) 32 = BitVec.ofNat 32 (s.gpr .r3).toNat
      rw [argRead 1 (by decide)]
      rw [← inputLen]
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · change s.mem.readW (VG.Proof.Mont.off (State.addr s.sp) (4 * 3)) 32 = BitVec.ofNat 32 (stackArg s 3).toNat
      rw [argRead 3 (by decide)]
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · change s.mem.readW (VG.Proof.Mont.off (State.addr s.sp) (4 * 5)) 32 = BitVec.ofNat 32 (stackArg s 5).toNat
      rw [argRead 5 (by decide)]
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · change s.mem.readW (VG.Proof.Mont.off (State.addr s.sp) (4 * 7)) 32 = BitVec.ofNat 32 (stackArg s 3).toNat
      rw [argRead 7 (by decide)]
      rw [← dpLen]
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · change s.mem.readW (VG.Proof.Mont.off (State.addr s.sp) (4 * 9)) 32 = BitVec.ofNat 32 (stackArg s 5).toNat
      rw [argRead 9 (by decide)]
      rw [← dqLen]
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · change s.mem.readW (VG.Proof.Mont.off (State.addr s.sp) (4 * 11)) 32 = BitVec.ofNat 32 (stackArg s 3).toNat
      rw [argRead 11 (by decide)]
      rw [← qiLen]
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [frame]; simpa only [crtCallGeometryP, crtCallGeometry, State.addr, Nat.mul_comm] using stackWs
  · exact (by simpa only [crtCallGeometryP, crtCallGeometry, State.addr, Nat.mul_comm] using wsArgs.symm : Region.Disjoint _ _).sub_left
      (Region.sub_prefix (by decide))
  · intro i
    rw [frame]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 from by omega_arith) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact stackN
    · exact stackInput
    · exact stackP
    · exact stackQ
    · exact stackDp
    · exact stackDq
    · exact stackQi
  · rw [frame]; exact stackOut
  · rw [frame]; exact stackArgs.sub_right (Region.sub_prefix (by decide))
  · intro a ha
    cases ha
    have words : 8 * (crtCallGeometryP s).r2Words = (stackArg s 15).toNat * 8 := by
      rw [r2Len]; simp [crtCallGeometryP, crtCallGeometry, CrtGeometry.r2Words, Nat.mul_comm]
    have slotSub : Region.Sub ⟨VG.Proof.Mont.off (State.addr s.sp) 56, 4⟩ ⟨State.addr s.sp, 64⟩ :=
      Offset.sub_base _ (by decide)
    have args : InRegions (s.rd ++ s.wr) (State.addr s.sp) 64 :=
      ⟨⟨State.addr s.sp, 64⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
    refine ⟨by omega_using [argFit], VG.CallLay.inRegions_sub args (by decide : 56 + 4 ≤ 64) (by decide),
      argRead 14 (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (by simpa only [crtCallGeometryP, crtCallGeometry, State.addr, Nat.mul_comm] using wsArgs.symm : Region.Disjoint _ _).sub_left slotSub
    · exact (by simpa only [crtCallGeometryP, crtCallGeometry, State.addr] using outArgs.symm : Region.Disjoint _ _).sub_left slotSub
    · rw [frame]; exact stackArgs.sub_right slotSub
    · rw [words]; simpa only [State.addr] using r2Fit
    · rw [words]; exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
    · rw [words]; simpa only [crtCallGeometryP, crtCallGeometry, State.addr, Nat.mul_comm] using wsR2.symm
    · rw [words, frame]; simpa only [State.addr] using stackR2
    · rw [words]; simpa only [crtCallGeometryP, crtCallGeometry, State.addr] using outR2.symm
    · rw [show (crtCallGeometryP s).r2Words = (stackArg s 15).toNat by omega_using [words]]
      exact r2Words

theorem crt_contract_pqP (s : State) (h : (Proof.Rsa.privateCrtPrecomputedContract abi 56).pre s) :
    Spec.Rsa.os2ip (crtCallBytes s 2) * Spec.Rsa.os2ip (crtCallBytes s 3) = Spec.Rsa.os2ip (crtCallBytes s 0) := by
  sig_pre [Proof.Rsa.privateCrtPrecomputedContract, Proof.Rsa.privateCrtPrecomputedSig, Proof.Rsa.privateCrtSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr] at h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end VG.Proof.Bignum.Arm

end
end

end

/-! # Private CRT RSA satisfies its shared contract under AAPCS -/

public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt

/-- `vg_rsa_private_crt`'s key check and factor preparation. -/
def baselineStages : CrtStages where
  check := CrtFn.validate
  prime := narrowPrime
  ok _ _ := True
  checkOk s _ h ready := crt_validateStage_ok s h ready
  checkCt _ _ := crt_validateStage_ct
  primeOk := fun {g} {_} j s hj _ h => by
    obtain ⟨_, le, _, _, _, _, _⟩ := h.1.narrow_fits j hj
    have words : g.words ≤ 128 := (crt_width_valid h.1.buffers.lengthValid).2.1
    exact crt_narrowPrime_ok s h.2 (by omega_using [le, words])
  primeCt := fun {g} {_} {_} j hj _ _ => by
    intro s t tr1 tr2 u w h e1 e2
    obtain ⟨_, le, _, _, _, _, _⟩ := h.1.1.narrow_fits j hj
    have words : g.words ≤ 128 := (crt_width_valid h.1.1.buffers.lengthValid).2.1
    exact crt_narrowPrime_ct (by omega_using [le, words]) s t tr1 tr2 u w ⟨h.1.2, h.2.1.2, h.2.2⟩ e1 e2

end VG.Proof.Bignum.Arm
end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtFnCT.lean`, which only this module imported.
section

/-! # The callable private RSA operation leaks only public geometry and modulus -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem crtFn_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} (modulus : bs1 0 = bs2 0)
    (st : CrtStages) (hst1 : st.ok g bs1) (hst2 : st.ok g bs2) (kernel : WindowKernel := baselineWindowKernel) :
    RelCT isa (fun s t => CrtFnInput g bs1 s ∧ CrtFnInput g bs2 t ∧ s.sp = t.sp)
      (CrtFn.codeOf st.check st.prime kernel.code) (fun _ _ => True) := by
  unfold CrtFn.codeOf
  apply RelCT.frame (fun _ _ h => h.2.2)
  intro s t tr1 tr2 u v hp e1 e2
  obtain ⟨s0, t0, ⟨hs, ht, sp⟩, ps, pt⟩ := hp
  have ps' := push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide) hs.stackFit
  have pt' := push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide) ht.stackFit
  have es : pcPushed s0 = s := Option.some.inj (ps'.symm.trans ps)
  have et : pcPushed t0 = t := Option.some.inj (pt'.symm.trans pt)
  subst s; subst t
  cases e1 with
  | seq entry1 tail1 =>
    cases e2 with
    | seq entry2 tail2 =>
      obtain ⟨trace, sp'⟩ := crt_entry_ct _ _ _ _ _ _ (by simp only [pcPushed, pushed_sp, sp]) entry1 entry2
      obtain ⟨_, s1, run1, ready1, _, _, _⟩ := crt_entry_ready s0 hs
      obtain ⟨_, t1, run2, ready2, _, _, _⟩ := crt_entry_ready t0 ht
      obtain ⟨-, rfl⟩ := Exec.det entry1 run1
      obtain ⟨-, rfl⟩ := Exec.det entry2 run2
      have body := relCT_keep_sp
        (crt_body_scoped_ct (kernel := kernel) (g := g) modulus st hst1 hst2)
        (fun _ _ h => h.2.2)
      have restore : RelCT isa (fun s t => s.sp = t.sp) (.block PcFn.restore) (fun s t => s.sp = t.sp) :=
        stackLoads_ct pcCalleeSaved
      obtain ⟨tailTrace, _⟩ := body.seq restore _ _ _ _ _ _ ⟨ready1, ready2, sp'⟩ tail1 tail2
      exact ⟨by rw [trace, tailTrace], trivial⟩

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtSaved.lean`, which only this module imported.
section

/-! # The secret acceptance slot does not overlap saved AAPCS registers -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont

theorem crt_callee_saved {s t : State} {g : CrtGeometry} {regs : Reg → BitVec 32}
    (saved : Spill.Saved s.mem (State.addr s.sp) regs pcCalleeSaved)
    (frame : Frame (crtMutable g s.sp ++ [⟨State.addr g.output, g.length⟩]) s.mem t.mem)
    (workspace : (⟨State.addr s.sp, 56⟩ : Region).Disjoint ⟨State.addr g.base, g.size⟩)
    (output : (⟨State.addr s.sp, 56⟩ : Region).Disjoint ⟨State.addr g.output, g.length⟩) :
    Spill.Saved t.mem (State.addr s.sp) regs pcCalleeSaved := by
  intro p hp
  have fit : p.2 + 4 ≤ 56 := by
    simp only [pcCalleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have gap : p.2 + 4 ≤ 48 ∨ 52 ≤ p.2 := by
    simp only [pcCalleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have low : 16 ≤ p.2 := by
    simp only [pcCalleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have sub : (⟨off (State.addr s.sp) p.2, 4⟩ : Region).Sub ⟨State.addr s.sp, 56⟩ :=
    Offset.sub_base _ fit
  have keep := frame.readW (a := off (State.addr s.sp) p.2) (w := 32) (r := ⟨off (State.addr s.sp) p.2, 4⟩) (by simp [Region.Contains])
    (by
      intro r hr
      simp only [crtMutable, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl | rfl) | rfl
      · exact workspace.sub_left sub
      · exact Offset.disjoint_base _ (by omega_using [low]) (by omega_using [fit])
      · exact Offset.disjoint _ (Or.inr (by omega_using [low])) (by omega_using [fit]) (by decide)
      · exact Offset.disjoint _ gap (by omega_using [fit]) (by decide)
      · exact output.sub_left sub) (by decide : 32 / 8 < 2 ^ 64)
  exact keep.trans (saved p hp)

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtFn.lean`, which only this module imported.
section

/-! # Callable ARMv7 private RSA preserves AAPCS and implements the shared result -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

theorem crtFn_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : CrtFnInput g bs s)
    (st : CrtStages) (hst : st.ok g bs) (kernel : WindowKernel := baselineWindowKernel) :
    WP isa (CrtFn.codeOf st.check st.prime kernel.code) s fun t => abiPreserved s t ∧
      Spec.Rsa.written t.mem (State.addr g.output) g.length (t.gpr .r0)
        (Spec.Rsa.privateCrt (bs 0) (bs 1) (bs 2) (bs 3) (bs 4) (bs 5) (bs 6)) := by
  unfold CrtFn.codeOf
  refine WP.frame (by decide) h.stackFit (by decide) ?_
  rw [WP.seq_iff]
  refine WP.mono (crt_entry_ready s h) ?_
  rintro u ⟨ready, _, savedU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono ((crt_body_scoped_ok (kernel := kernel)) u ready st hst) ?_
  rintro v ⟨result, frameV, restV⟩
  have spV : v.sp = s.sp - BitVec.ofNat 32 56 := restV.sp.trans restU.sp
  have wrV : v.wr = (pcPushed s).wr := restV.wr.trans restU.wr
  have saved : Spill.Saved v.mem (State.addr v.sp) s.gpr pcCalleeSaved := by
    rw [restV.sp]
    apply crt_callee_saved savedU frameV
    · rw [restU.sp]; exact h.stackWorkspace
    · rw [restU.sp]; exact h.stackOutput
  have fit : v.sp.toNat + 56 ≤ 2 ^ 32 := by
    rw [spV, FrameStack.sub_toNat' h.stackFit]
    have := s.sp.isLt
    omega_using []
  have read : InRegions (v.rd ++ v.wr) (State.addr v.sp) 56 := by
    refine ⟨⟨State.addr v.sp, 56⟩, List.mem_append_right _ ?_, Region.contains_self _ _⟩
    rw [wrV, spV]
    exact List.mem_cons_self
  refine WP.mono (pc_restore_ok v s.gpr fit read saved) ?_
  rintro t ⟨restored, memT, restT⟩ ml ul hfl
  have ret : t.gpr .r0 = v.gpr .r0 := restT.gpr .r0 (by decide)
  have outEq : Spec.Rsa.bytesAt ml (State.addr g.output) g.length =
      Spec.Rsa.bytesAt t.mem (State.addr g.output) g.length :=
    rsa_bytes_frame hfl (by have := h.outputFits; omega_using [this]) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.stackOutput.symm)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    have ne : r ≠ .r12 := by intro he; subst r; simp [preserved] at hr
    rw [popped_gpr ne]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact restored (.r4, 16) (by decide)
    · exact restored (.r5, 20) (by decide)
    · exact restored (.r6, 24) (by decide)
    · exact restored (.r7, 28) (by decide)
    · exact restored (.r8, 32) (by decide)
    · exact restored (.r9, 36) (by decide)
    · exact restored (.r10, 40) (by decide)
    · exact restored (.r11, 44) (by decide)
    · exact restored (.lr, 52) (by decide)
  · rw [popped_sp, restT.sp, spV]
    exact BitVec.sub_add_cancel _ _
  · dsimp only
    revert result
    cases Spec.Rsa.privateCrt (bs 0) (bs 1) (bs 2) (bs 3) (bs 4) (bs 5) (bs 6) <;>
      simp only [Spec.Rsa.written, popped_gpr (by decide : Reg.r0 ≠ .r12), outEq, memT, ret] <;> exact id

end VG.Proof.Bignum.Arm
end

end

/-! ## `vg_rsa_private_crt_precomputed`'s key check and factor preparation

For a key whose factors' `R² mod p` and `R² mod q` are given (`g.r2`) and
whose factors' product is the modulus, which those values imply. -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

/-- The keys `givenStages` is for. -/
def GivenOk (g : CrtGeometry) (bs : Fin 7 → List Byte) : Prop :=
  g.r2.isSome ∧ Spec.Rsa.os2ip (bs 2) * Spec.Rsa.os2ip (bs 3) = Spec.Rsa.os2ip (bs 0)

theorem given_check_ok {g : CrtGeometry} {bs : Fin 7 → List Byte} (s : State) (hok : GivenOk g bs)
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s) :
    WP isa CrtFn.validateGiven s (CrtCheckPost g bs s) :=
  crt_validateGivenStage_ok s hok.2 h ready

theorem given_check_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} :
    RelCT isa (fun s t => CrtSelected g bs1 g.base s ∧ CrtSelected g bs2 g.base t ∧ s.sp = t.sp)
      CrtFn.validateGiven (fun _ _ => True) :=
  crt_validateGivenStage_ct

theorem given_prime_ok {g : CrtGeometry} {bs : Fin 7 → List Byte} (j : Fin 6) (s : State) (hj : j = 1 ∨ j = 2)
    (hok : GivenOk g bs) (h : CrtPrimeIn g bs j s) :
    WP isa (narrowPrimeGiven (56 + 8 * j.val)) s (NarrowPrimePost (crtN g.base g.words) (workspaceWords g.words)
      (narrowWords (g.sourceLength j.succ) g.words) (bs j.succ) s) := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hok.1
  exact crt_narrowPrimeGiven_ok j s hj ha h

theorem given_prime_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} (j : Fin 6) (hj : j = 1 ∨ j = 2)
    (hok : GivenOk g bs1) :
    RelCT isa (fun s t => CrtPrimeIn g bs1 j s ∧ CrtPrimeIn g bs2 j t ∧ s.sp = t.sp)
      (narrowPrimeGiven (56 + 8 * j.val)) (fun _ _ => True) := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hok.1
  exact crt_narrowPrimeGiven_ct hj ha

def givenStages : CrtStages where
  check := CrtFn.validateGiven
  prime := narrowPrimeGiven
  ok := GivenOk
  checkOk s hok h ready := given_check_ok s hok h ready
  checkCt _ _ := given_check_ct
  primeOk j s hj hok h := given_prime_ok j s hj hok h
  primeCt j hj hok _ := given_prime_ct j hj hok

end VG.Proof.Bignum.Arm
end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem crt_contract_correct (s : State) (h : (Proof.Rsa.privateCrtContract abi 56).pre s) (kernel : WindowKernel := baselineWindowKernel) :
    ∃ tr t, Exec isa (CrtFn.codeWith kernel.code) s tr t ∧ abiPreserved s t ∧
      (Proof.Rsa.privateCrtContract abi 56).post s t := by
  obtain ⟨tr, t, run, preserved, post⟩ := (crtFn_ok (kernel := kernel)) s (crt_contract_pre s h) baselineStages trivial
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  exact post

theorem crt_contract_ct (kernel : WindowKernel := baselineWindowKernel) : ConstantTime isa (Proof.Rsa.privateCrtContract abi 56).pre
    (Proof.Rsa.privateCrtContract abi 56).pub (CrtFn.codeWith kernel.code) := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  have is := crt_contract_pre s hs
  have it := crt_contract_pre t ht
  sig_pub [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, _, p2, p3, a0, _, a2, a3, a4, a5, a6, _, a8, _, a10, _, a12, a13⟩ := hp
  have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
  simp only [List.map_map, Function.comp_def, BitVec.ofNat_toNat, BitVec.setWidth_eq, List.map_id'] at byteEq
  have geometry : crtCallGeometry s = crtCallGeometry t := by
    simp only [crtCallGeometry, p0, p2, p3, a0, a2, a3, a4, a5, a6, a8, a10, a12, a13]
  rw [← geometry] at it
  have modulus : crtCallBytes s 0 = crtCallBytes t 0 := byteEq
  exact ((crtFn_ct (kernel := kernel)) modulus baselineStages trivial trivial s t tr1 tr2 u v ⟨is, it, sp⟩ e1 e2).1

/-! ## `vg_rsa_private_crt_precomputed` -/

theorem crt_contract_correctP (s : State) (h : (Proof.Rsa.privateCrtPrecomputedContract abi 56).pre s)
    (kernel : WindowKernel := baselineWindowKernel) :
    ∃ tr t, Exec isa (CrtFn.codeGiven kernel.code) s tr t ∧ abiPreserved s t ∧
      (Proof.Rsa.privateCrtPrecomputedContract abi 56).post s t := by
  obtain ⟨tr, t, run, preserved, post⟩ := (crtFn_ok (kernel := kernel)) s (crt_contract_preP s h) givenStages
    (show GivenOk _ _ from ⟨rfl, crt_contract_pqP s h⟩)
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Proof.Rsa.privateCrtPrecomputedContract, Proof.Rsa.privateCrtPrecomputedSig, Proof.Rsa.privateCrtSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  exact post

theorem crt_contract_ctP (kernel : WindowKernel := baselineWindowKernel) :
    ConstantTime isa (Proof.Rsa.privateCrtPrecomputedContract abi 56).pre
      (Proof.Rsa.privateCrtPrecomputedContract abi 56).pub (CrtFn.codeGiven kernel.code) := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  have is := crt_contract_preP s hs
  have it := crt_contract_preP t ht
  have oks : GivenOk (crtCallGeometryP s) (crtCallBytes s) := ⟨rfl, crt_contract_pqP s hs⟩
  have okt : GivenOk (crtCallGeometryP t) (crtCallBytes t) := ⟨rfl, crt_contract_pqP t ht⟩
  sig_pub [Proof.Rsa.privateCrtPrecomputedContract, Proof.Rsa.privateCrtPrecomputedSig, Proof.Rsa.privateCrtSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, _, p2, p3, a0, _, a2, a3, a4, a5, a6, _, a8, _, a10, _, a12, a13, a14, _⟩ := hp
  have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
  simp only [List.map_map, Function.comp_def, BitVec.ofNat_toNat, BitVec.setWidth_eq, List.map_id'] at byteEq
  have geometry : crtCallGeometryP s = crtCallGeometryP t := by
    simp only [crtCallGeometryP, crtCallGeometry, p0, p2, p3, a0, a2, a3, a4, a5, a6, a8, a10, a12, a13, a14]
  rw [← geometry] at it okt
  have modulus : crtCallBytes s 0 = crtCallBytes t 0 := byteEq
  exact ((crtFn_ct (kernel := kernel)) modulus givenStages oks okt s t tr1 tr2 u v ⟨is, it, sp⟩ e1 e2).1

end VG.Proof.Bignum.Arm

end

end


/-! # ARMv7 private CRT RSA is verified against the shared RSA contract -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

/-- Separate buffers for a 64-byte modulus and 32-byte factors, with native stack arguments. -/
def crtSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x2000 | .r3 => 64 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x30 else
    if a = 0x8004 then 0x40 else
    if a = 0x8009 then 0x31 else
    if a = 0x800c then 0x20 else
    if a = 0x8011 then 0x32 else
    if a = 0x8014 then 0x20 else
    if a = 0x8019 then 0x33 else
    if a = 0x801c then 0x20 else
    if a = 0x8021 then 0x34 else
    if a = 0x8024 then 0x20 else
    if a = 0x8029 then 0x35 else
    if a = 0x802c then 0x20 else
    if a = 0x8031 then 0x40 else
    if a = 0x8034 then 0x20 else
    if a = 0x8035 then 0x4 else
    0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 64⟩, ⟨0x3100, 32⟩, ⟨0x3200, 32⟩,
    ⟨0x3300, 32⟩, ⟨0x3400, 32⟩, ⟨0x3500, 32⟩, ⟨0x8000, 56⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x4000, 8448⟩]

theorem crt_contract_sat : ∃ s, (Proof.Rsa.privateCrtContract abi 56).pre s := by
  sig_implies_sat [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [crtSatState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid,
      Spec.Rsa.scratchWords] using crtSatState

theorem crt_verified (kernel : WindowKernel := baselineWindowKernel) : Verified target (CrtFn.codeWith kernel.code) (Proof.Rsa.privateCrtContract abi 56) :=
  ⟨(crt_contract_correct (kernel := kernel)), (crt_contract_ct (kernel := kernel)), crt_contract_sat⟩

theorem os2ip_replicate_zero' (n : Nat) : Spec.Rsa.os2ip (List.replicate n 0) = 0 := by
  unfold Spec.Rsa.os2ip
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ', List.foldl_append, ih]; rfl

/-- `crtSatState`, with factors of one octet, zero (whose product is the zero
modulus, and whose `R² mod p`, `2^256` of 2 words, is zeros), and their `R²`
at `0x3600`. -/
def crtSatStateP : State :=
  { crtSatState with
    mem := fun a => if a = 0x8039 then 0x36 else if a = 0x803c then 4 else
      if a = 0x800c ∨ a = 0x8014 ∨ a = 0x801c ∨ a = 0x8024 ∨ a = 0x802c then 1 else crtSatState.mem a
    rd := [⟨0x2000, 64⟩, ⟨0x3000, 64⟩, ⟨0x3100, 1⟩, ⟨0x3200, 1⟩,
      ⟨0x3300, 1⟩, ⟨0x3400, 1⟩, ⟨0x3500, 1⟩, ⟨0x3600, 32⟩, ⟨0x8000, 64⟩] }

theorem crt_contract_satP : ∃ s, (Proof.Rsa.privateCrtPrecomputedContract abi 56).pre s := by
  refine ⟨crtSatStateP, ?_⟩
  sig_pre [Proof.Rsa.privateCrtPrecomputedContract, Proof.Rsa.privateCrtPrecomputedSig,
      Proof.Rsa.privateCrtSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  sig_and_intros
  rotate_right 3
  · decide
  · rw [show Spec.Rsa.wordsAt _ _ _ = List.replicate 4 0 by decide,
      show Spec.Rsa.bytesAt _ _ _ = [0] by decide, show Spec.Rsa.bytesAt _ _ _ = [0] by decide]
    decide
  · rw [show Spec.Rsa.bytesAt _ _ _ = [0] by decide, show Spec.Rsa.bytesAt _ _ _ = [0] by decide,
      show Spec.Rsa.bytesAt _ _ _ = List.replicate 64 0 by decide, os2ip_replicate_zero']
    rfl
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (simp only [Spec.Rsa.lenValid]; decide)
    | (intro a h₁ h₂
       sig_simp_only [Region.Contains, crtSatStateP, crtSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
         at h₁ h₂
       bv_omega)

theorem crt_verifiedP (kernel : WindowKernel := baselineWindowKernel) :
    Verified target (CrtFn.codeGiven kernel.code) (Proof.Rsa.privateCrtPrecomputedContract abi 56) :=
  ⟨(crt_contract_correctP (kernel := kernel)), (crt_contract_ctP (kernel := kernel)), crt_contract_satP⟩

end VG.Proof.Bignum.Arm
