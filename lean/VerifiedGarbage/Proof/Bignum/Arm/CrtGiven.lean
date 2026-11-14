module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtPrecomputed
public import VerifiedGarbage.Proof.Bignum.Arm.CrtStages
import VerifiedGarbage.Proof.Bignum.Arm.PrimeR2From
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowCopy
import VerifiedGarbage.Proof.Bignum.Arm.CopyBuffer
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.R2
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.ArrayFrame
import VerifiedGarbage.Proof.Bignum.Arm.ClearArrayWide
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstLayout
import VerifiedGarbage.Proof.Bignum.Arm.SelectArray
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Bignum.ExportEncoding
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.RelCTAssoc

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
  have header := nativeHeader_of_layout s.mem (crtN g.base g.words) nw.nowrap (Nat.le_refl _) ready.layout
  rw [ready.width] at header
  have size : 256 ≤ 8 * workspaceWords g.words := shared.main.toCrtLayoutState.size
  have hj := j.isLt
  have lenSmall : g.sourceLength j.succ < 2 ^ 28 := by
    have := (crt_width_valid shared.buffers.lengthValid).2.1
    have := shared.buffers.lengthValid.2
    have := shared.buffers.pShort
    have := shared.buffers.qShort
    have : g.sourceLength j.succ ≤ g.length := by
      unfold CrtGeometry.sourceLength; split <;> omega_arith
    omega_arith
  have vSmall : v < 2 ^ 28 := by
    have := ready.width ▸ ready.layout.2.2.1
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at this
    have := nw.nowrap
    omega_arith
  have nNow := nw.nowrap
  have spNow := shared.stack.nowrap
  unfold r2WidthTest
  refine wp_ldr (a := off (State.addr (crtN g.base g.words)) 48) (by decide)
    (by rw [ready.ptr]; exact addr_add (by omega_using [size, nNow])) (nw.read (by omega_using [size])) fun u a => ?_
  have slotAddr : State.addr (u.sp + BitVec.ofNat 32 (56 + 8 * j.val + 4)) = off (State.addr s.sp) (60 + 8 * j.val) := by
    rw [a.sp, show 56 + 8 * j.val + 4 = 60 + 8 * j.val by omega_using []]
    exact addr_add (by omega_using [spNow])
  refine wp_loadStack (a := off (State.addr s.sp) (60 + 8 * j.val)) (by omega_using []) slotAddr
    (by rw [a.rd, a.wr]; exact shared.stack.read (by omega_using [])) fun z b => ?_
  refine wp_dp (op2_imm (by decide)) fun y c => ?_
  refine wp_mov (op2_lsr ⟨by decide, by decide⟩) fun x d => ?_
  refine wp_cmp (op2_reg _ _) fun t e zf => WP.block_nil ?_
  have r1 : x.gpr .r1 = BitVec.ofNat 32 v := by
    rw [d.other .r1 (by decide), c.other .r1 (by decide), b.other .r1 (by decide), a.gpr]
    exact header.count
  have r2 : x.gpr .r2 = BitVec.ofNat 32 ((g.sourceLength j.succ + 7) / 8) := by
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
  have r := shared.buffers.r2 a ha
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
    have pLen : g.pLength < 2 ^ 28 := by
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
    have len : s.mem.readW (off (State.addr s.sp) 68) 32 = BitVec.ofNat 32 g.pLength := shared.stack.length 1
    have cY : y.gpr .r2 = BitVec.ofNat 32 ((g.pLength + 7) / 8) := by
      rw [e.gpr, d.gpr, dpVal, c.gpr, b.mem, len]
      exact ceil8_ofNat pLen
    have cQ : q.gpr .r2 = BitVec.ofNat 32 (Spec.Rsa.primeWords g.pLength) := by
      rw [k.gpr, dpVal, i.other .r2 (by decide), f.other .r2 (by decide), i.gpr, f.gpr, dpVal, cY]
      unfold Spec.Rsa.primeWords Spec.Rsa.modulusWords
      exact maxTwo_ofNat (by omega_using [pPos]) (by omega_using [pLen])
    have aQ : q.gpr .r1 = a := by
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
  have e := VG.Proof.Bignum.read_eq_wv m p 0 n
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
  have r := shared.buffers.r2 a ha
  have fit := r.fit
  have words := r.words
  have read := r.read
  have sep := r.separate
  unfold CrtGeometry.r2Words at fit words read sep
  have p2 : 2 ≤ Spec.Rsa.primeWords g.pLength := Nat.le_max_left _ _
  have q2 : 2 ≤ Spec.Rsa.primeWords g.qLength := Nat.le_max_left _ _
  rw [r2_wordsAt_append] at words
  have lenP : (Spec.Rsa.wordsAt s.mem (State.addr a) (Spec.Rsa.primeWords g.pLength)).length =
      (Spec.Rsa.primeR2 (bs 2)).length := by
    simp only [Spec.Rsa.wordsAt, Spec.Rsa.primeR2, Spec.Rsa.toWords, List.length_map, List.length_range]
    rw [(shared.buffers.source 2).length]; rfl
  obtain ⟨wp, wq⟩ := List.append_inj words lenP
  have hq : State.addr (a + BitVec.ofNat 32 (8 * Spec.Rsa.primeWords g.pLength)) =
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
  have hv : 2 ≤ v := ready.width ▸ ready.layout.1
  have fits : arrAt v 8 ≤ 8 * workspaceWords g.words := ready.width ▸ ready.layout.2.2.1
  have end4 := Nat.le_trans (array_end_le (w := v) (by decide : 4 < 8)) fits
  have narrowSub := crt_region_sub_workspace h.shared.buffers.workspace h.shared.buffers.storageFits
    h.shared.narrow_member
  have dstAddr : State.addr (crtN g.base g.words + BitVec.ofNat 32 (arrAt v 4)) =
      off (State.addr (crtN g.base g.words)) (arrAt v 4) := addr_add (by omega_using [nNow, end4])
  have dstNat : (crtN g.base g.words + BitVec.ofNat 32 (arrAt v 4)).toNat =
      (crtN g.base g.words).toNat + arrAt v 4 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [nNow, end4]), Nat.mod_eq_of_lt (by omega_using [nNow, end4])]
  have dstSub : Region.Sub ⟨State.addr (crtN g.base g.words + BitVec.ofNat 32 (arrAt v 4)), 8 * v⟩
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
  have ptrX : x.gpr .r0 = crtN g.base g.words := by
    rw [mv.gpr, restY.gpr .r5 (by decide), p5]
  have outside := frame_array_outside (by omega_using [srcFit, dstNat] : arrAt v 4 + 8 * v < 2 ^ 64) frameY
  have frameX : Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s.mem x.mem := by
    rw [mv.mem, ← memZ]; exact outside_workspace outside (by omega_using [end4])
  have keepsX : Keeps (State.addr (crtN g.base g.words)) (workspaceWords g.words) v 4 s.mem x.mem := by
    rw [mv.mem, ← memZ]
    exact outside_array_prefix_keeps outside (by omega_using [nNow] : 8 * workspaceWords g.words < 2 ^ 64) (by omega_using [])
  have restX : Rest roundClobbers s x :=
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
  have fits : arrAt v 8 ≤ 8 * workspaceWords g.words := readyX.width ▸ readyX.layout.2.2.1
  have nNow := readyX.workspace.nowrap
  have spNow := h.shared.stack.nowrap
  rw [WP.seq_iff]
  refine WP.mono (smallConstLayout_ok x 1 readyX.workspace readyX.layout readyX.width readyX.ptr
    (by decide : 7 < 8) (by decide) (by decide) readyX.stackRead readyX.stackSep readyX.saved) ?_
  rintro w ⟨_, _, number7, outside7, frame7, rest7, ptrW⟩
  have keeps7 := outside_array_keeps outside7 (len := workspaceWords g.words) (by omega_using [nNow])
  obtain ⟨readyW, modW⟩ := readyX.after_array (by decide : 7 ≠ 0) keeps7 frame7 rest7 ptrW
  have arr4W := (keeps_array_num keeps7 fits
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Proof.Rsa.Mont.Operand 4)
    (by decide)).trans arr4X
  have restSW := restX.trans rest7
  have frameSW := frameX.trans frame7
  have flagW : w.mem.readW (off (State.addr w.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 := by
    rw [restSW.sp]
    exact frameSW.readW (r := ⟨off (State.addr s.sp) 48, 4⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst r; exact h.slotSep) (by decide)
  rw [WP.seq_iff]
  refine wp_loadStack (a := off (State.addr w.sp) 48) (by decide) (addr_add (by rw [restSW.sp]; omega_using [spNow]))
    (by rw [restSW.rd, restSW.wr, restSW.sp]; exact h.shared.stack.read (by decide)) fun q ld => WP.block_nil ?_
  have r11 : q.gpr .r11 = s.mem.readW (off (State.addr s.sp) 48) 32 := ld.gpr.trans flagW
  have readyQ := readyW.of_mem ld.mem (ld.rest (by decide : Reg.r11 ∈ [Reg.r11]))
    (by rw [ld.other .r0 (by decide)]; exact readyW.ptr)
  refine WP.mono (selectArray_ok q readyQ.workspace readyQ.layout readyQ.width readyQ.ptr
    (by decide : 4 < 8) (by decide : 7 < 8) (by decide : 4 < 8) (by rw [r11]; exact h.bit)
    readyQ.stackRead readyQ.stackSep readyQ.saved) ?_
  rintro t ⟨_, _, valueT, outsideT, frameT, restT, ptrT⟩
  have keepsT := outside_array_keeps outsideT (len := workspaceWords g.words) (by omega_using [nNow])
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
  have hv : 2 ≤ v := ready.width ▸ ready.layout.1
  obtain ⟨_, le, _, _, _, _, _⟩ := shared.narrow_fits j hj
  have words : g.words ≤ 128 := (crt_width_valid shared.buffers.lengthValid).2.1
  rw [r2Given, WP.seq_iff]
  refine WP.mono (r2WidthTest_ok s (j := j) shared ready) ?_
  rintro u ⟨z, memU, restU⟩
  have readyU := ready.of_mem memU restU ((restU.gpr .r0 (by decide)).trans ready.ptr)
  have sharedU := shared.of_mem memU restU
  have flagU : u.mem.readW (off (State.addr u.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 := by
    rw [memU, restU.sp]
  by_cases same : v = (g.sourceLength j.succ + 7) / 8
  · refine WP.ite true (by rw [VG.Proof.X25519.Arm.eval_eq, z, decide_eq_true same]) (fun _ => ?_) (by simp)
    have width : v = Spec.Rsa.primeWords (g.sourceLength j.succ) := by
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
      have large := valid b0
      have len : (bs j.succ).length = g.sourceLength j.succ := (shared.buffers.source j.succ).length
      rw [← width] at given
      unfold Spec.Rsa.primeR2 at given
      rw [len, ← width] at given
      refine read_of_toWords given ?_
      have lt := VG.Proof.Bignum.os2ip_lt (bs j.succ)
      rw [len, VG.Proof.Bignum.pow256_eq] at lt
      have : 2 ^ (8 * g.sourceLength j.succ) ≤ 2 ^ (64 * v) := Nat.pow_le_pow_right (by decide) (by omega_arith)
      have := Nat.mod_lt (2 ^ (128 * v)) (by omega_using [large] : 0 < Spec.Rsa.os2ip (bs j.succ))
      omega_arith
  · refine WP.ite false (by rw [VG.Proof.X25519.Arm.eval_eq, z, decide_eq_false same]) (by simp) (fun _ => ?_)
    refine WP.mono (r2_ok u readyU (by omega_using [narrow, le, words])) ?_
    rintro t ⟨done, valueT, modT, frameT, restT⟩
    have modU : numAt u.mem (State.addr (crtN g.base g.words)) v 0 = M := by rw [memU]; exact modulus
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
  have sharedU := shared.after_narrow (frameU.mono (by simp)) restU
  have narrowSub := crt_region_sub_workspace shared.buffers.workspace shared.buffers.storageFits shared.narrow_member
  refine WP.mono (r2Given_ok u (j := j) hj ha sharedU readyU rfl (by rw [flagU]; exact input.bit)
    (by rw [flagU]; exact fun ne => (input.valid ne).1) modU (by rw [flagU])) ?_
  rintro t ⟨readyT, modT, r2T, frameT, restT⟩
  have restST := restU.trans restT
  refine ⟨readyT, modT, odd, r2T, ?_, frameU.trans frameT, restST⟩
  rw [restST.sp]
  have keep := (frameU.trans frameT).readW (a := off (State.addr s.sp) 48) (w := 32)
    (r := ⟨off (State.addr s.sp) 48, 4⟩) (Region.contains_self _ _)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact (shared.stack.separate.sub_left (Offset.sub_base _ (by decide))).sub_right narrowSub) (by decide)
  exact keep

end VG.Proof.Bignum.Arm
