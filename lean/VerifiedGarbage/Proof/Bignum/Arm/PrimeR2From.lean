module

public import VerifiedGarbage.Impl.Bignum.Arm.PrimeR2From
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPrime
import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimeAcceptance
import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulus
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeInverse
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowCopy
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Bignum.PrimeR2
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowHalf
import VerifiedGarbage.Proof.Bignum.Arm.ClearArrayWide
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.MontOp
import VerifiedGarbage.Proof.Bignum.Arm.SubModArray
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.DoubleCountMemory
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoop
import VerifiedGarbage.Proof.Bignum.Arm.R2
import VerifiedGarbage.Proof.Bignum.Arm.SquareOp
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopState

/-! # A factor's `R² mod p` from `R² mod n`: correctness

`narrowPrimeInv` imports the factor at the narrow width, accepts it or
replaces it by 3, and computes its inverse (`crt_narrowPrimeInv_ok`), as
`narrowPrime` does before its `R² mod X`. When `w ≤ 2 v`, `r2Fold` then
folds p's copy of `R² mod n`, `x = h R + l`, to `x R⁻² = h R⁻¹ + l R⁻²`
(`crt_foldReduce_ok`), which is `2^(64 e)` for `e = 2 (w - v)` modulo a
factor of `n` (`fold_reduced`), and doubles and squares it to `R_X²` as
`r2` does (`r2Fold_ok`). Otherwise `r2FromN` computes it from 1
(`r2FromN_ok`). The fold's value holds only for a factor of `n`; a rejected
key, whose factor is replaced by 3, gets some value below it, which the
mask clears.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt Keeps Operand)
open VG.Proof.X25519.Arm (Rest Upd wp_ldr wp_str wp_mov wp_dp wp_cmp op2_reg op2_imm op2_lsl op2_lsr dpVal)

theorem crt_narrowPrimeInv_ok (s : State) {base pp : BitVec 32} {len v k ps : Nat} {pb : List Byte}
    (h : NarrowPrimeInput base pp len v k ps pb s) :
    WP isa (narrowPrimeInv ps) s fun t =>
      let M := safePrime (s.mem.readW (off (State.addr s.sp) 48) 32).toNat (Spec.Rsa.os2ip pb)
      ArithmeticReady base len v t ∧ numAt t.mem (State.addr base) v 0 = M ∧ M % 2 = 1 ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [narrowPrimeInv, WP.seq_iff]
  refine WP.mono (crt_narrowImport_ok s h) ?_
  rintro u ⟨accepted, value, flagU, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (crt_primeAcceptance_ready u accepted.toLayoutFrameReady accepted.stackFit accepted.flagRead
    accepted.bit accepted.valid) ?_
  rintro y ⟨ready, number, bitY, frameY, restY⟩
  have valid := safePrime_valid ready.valid
  rw [WP.seq_iff]
  refine WP.mono (sanitizeModulus_ok y ready.workspace ready.layout ready.width ready.ptr ready.bit ready.stackRead
    ready.stackSep ready.saved) ?_
  rintro z ⟨layoutZ, widthZ, modulus, _, frameZ, restZ, ptrZ⟩
  change numAt z.mem (State.addr base) v 0 = safePrime _ _ at modulus
  refine WP.mono (precomputeInverse_ok z (ready.workspace.congr restZ.wr) layoutZ widthZ ptrZ
    (by rw [modulus]; exact valid.2) (by rw [modulus]; exact valid.1)
    (by rw [restZ.rd, restZ.wr, restZ.sp]; exact ready.stackRead)
    (by rw [restZ.sp]; exact ready.stackSep) (saved_base_kept frameZ ready.stackSep ready.saved restZ.sp)) ?_
  rintro t ⟨readyT, modT, frameT, restT⟩
  have restUT : Rest roundClobbers u t := (restY.mono (by decide)).trans (restZ.trans restT)
  have frameUT := frameY.trans (frameZ.trans frameT)
  have eq : WorkspaceEq (State.addr u.sp) 112 u.mem t.mem := WorkspaceEq.of_frame (by decide) frameUT
    (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      have sep := h.source.stackSeparate
      rw [← restU.sp] at sep
      exact sep)
  have flagT : t.mem.readW (off (State.addr t.sp) 48) 32 = u.mem.readW (off (State.addr u.sp) 48) 32 := by
    rw [restUT.sp]; exact eq.word (d := 48) (bits := 32) (by decide)
  rw [bitY, number, value, flagU] at modulus
  rw [bitY, flagU, number, value] at valid
  exact ⟨readyT, modT.trans modulus, valid.2, flagT.trans flagU, frameU.trans frameUT, restU.trans restUT⟩

/-- `(a - b) >>> 31` is zero iff `b ≤ a`, for numbers below `2^31`. -/
theorem sub_shr31_eq_zero {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    ((BitVec.ofNat 32 a - BitVec.ofNat 32 b) >>> 31 - 0 == 0) = decide (b ≤ a) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, show ∀ x : BitVec 32, x - 0 = x from fun x => BitVec.sub_zero x, ← BitVec.toNat_inj,
    BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (show a < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show b < 2 ^ 32 by omega), show (0 : BitVec 32).toNat = 0 from rfl]
  constructor
  · intro h
    by_contra hc
    rw [show 2 ^ 32 - b + a = 2 ^ 32 - (b - a) by omega, Nat.mod_eq_of_lt (by omega)] at h
    have := Nat.div_eq_zero_iff.mp h
    omega
  · intro h
    rw [show 2 ^ 32 - b + a = (a - b) + 2 ^ 32 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    exact Nat.div_eq_of_lt (by omega)

/-- The main workspace's `w` and the narrow one's `v`. -/
theorem foldWidths_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32} {slot v : Nat}
    (h : CrtCopyCtx g bs child slot v s) :
    WP isa (.block foldWidths) s fun t => t.gpr .r1 = BitVec.ofNat 32 g.words ∧ t.gpr .r2 = BitVec.ofNat 32 v ∧
      t.mem = s.mem ∧ Rest [.r1, .r2] s t := by
  have main := h.shared.buffers.context.main
  have nw := h.ready.workspace
  unfold foldWidths
  refine wp_loadStack (a := off (State.addr s.sp) 8) (by decide)
    (addr_add (by have := h.shared.stack.nowrap; omega)) (h.shared.stack.read (by decide)) fun u a => ?_
  have base : u.gpr .r1 = g.base := by rw [a.gpr]; exact h.shared.savedMain
  refine wp_ldr (a := off (State.addr g.base) 48) (by decide)
    (by rw [base]; exact addr_add (by have := main.nowrap; have := h.shared.main.toCrtLayoutState.size; omega))
    (by rw [a.rd, a.wr]; exact main.read (by have := h.shared.main.toCrtLayoutState.size; omega)) fun z b => ?_
  have r0 : z.gpr .r0 = crtN g.base g.words := by rw [b.other .r0 (by decide), a.other .r0 (by decide)]; exact h.ready.ptr
  have size : 256 ≤ 8 * workspaceWords g.words := h.shared.main.toCrtLayoutState.size
  refine wp_ldr (a := off (State.addr (crtN g.base g.words)) 48) (by decide)
    (by rw [r0]; exact addr_add (by have := nw.nowrap; omega))
    (by rw [b.rd, b.wr, a.rd, a.wr]; exact nw.read (by omega)) fun t c => WP.block_nil ?_
  have header := nativeHeader_of_layout s.mem (crtN g.base g.words) nw.nowrap (Nat.le_refl _) h.ready.layout
  rw [h.ready.width] at header
  refine ⟨by rw [c.other .r1 (by decide), b.gpr, a.mem]; exact h.shared.main.toCrtLayoutState.nativeCount main,
    by rw [c.gpr, b.mem, a.mem]; exact header.count, c.mem.trans (b.mem.trans a.mem),
    (a.rest (by decide)).trans ((b.rest (by decide)).trans (c.rest (by decide)))⟩

/-- `foldTest`: Z iff `w ≤ 2 v`. -/
theorem foldTest_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32} {slot v : Nat}
    (h : CrtCopyCtx g bs child slot v s) :
    WP isa (.block foldTest) s fun t => t.z = decide (g.words ≤ 2 * v) ∧ t.mem = s.mem ∧
      Rest [.r1, .r2, .r3] s t := by
  have words : g.words ≤ 128 := (crt_width_valid h.shared.buffers.lengthValid).2.1
  have le := h.le
  unfold foldTest
  refine VG.Proof.X25519.Arm.WP.append (foldWidths_ok s h) fun u ⟨r1, r2, mem, rest⟩ => ?_
  refine wp_dp (op2_reg _ _) fun a ha => ?_
  refine wp_dp (op2_reg _ _) fun b hb => ?_
  refine wp_mov (op2_lsr ⟨by decide, by decide⟩) fun c hc => ?_
  refine wp_cmp (op2_imm (by decide)) fun t ht z => WP.block_nil ?_
  have r3 : c.gpr .r3 = (BitVec.ofNat 32 (2 * v) - BitVec.ofNat 32 g.words) >>> 31 := by
    rw [hc.gpr, hb.gpr, dpVal, ha.gpr, ha.other .r1 (by decide), dpVal, r1, r2,
      ← BitVec.ofNat_add, ← Nat.two_mul]
  refine ⟨by rw [z, r3]; exact sub_shr31_eq_zero (by omega) (by omega), ht.mem.trans (hc.mem.trans
    (hb.mem.trans (ha.mem.trans mem))), (rest.mono (by decide)).trans ((ha.rest (by decide)).trans
    ((hb.rest (by decide)).trans ((hc.rest (by decide)).trans (ht.rest _))))⟩

/-- `foldReduce`: array 4 `:= x R⁻²` mod `X`, for `x` p's full array 4. -/
theorem crt_foldReduce_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {v M : Nat} (h : CrtCopyCtx g bs child 224 v s) (half : g.words ≤ 2 * v)
    (modulus : numAt s.mem (State.addr (crtN g.base g.words)) v 0 = M) :
    WP isa foldReduce s fun t =>
      ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v t ∧
      numAt t.mem (State.addr (crtN g.base g.words)) v 0 = M ∧
      numAt t.mem (State.addr (crtN g.base g.words)) v 4 < M ∧
      numAt t.mem (State.addr (crtN g.base g.words)) v 4 * 2 ^ (64 * v) * 2 ^ (64 * v) % M =
        numAt s.mem (State.addr child) g.words 4 % M ∧
      Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  have fits : arrAt v 8 ≤ 8 * workspaceWords g.words := h.ready.width ▸ h.ready.layout.2.2.1
  have op : ∀ q, q = 0 ∨ q = 1 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 → Operand q := by
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have large : 1 < M := modulus ▸ h.ready.modulus
  have positive : 0 < M := by omega
  -- One.
  rw [foldReduce, WP.seq_iff]
  refine WP.mono (smallConst_ok s (o := 7) 1 h.ready (by decide) (by decide) (by decide) (by decide)) ?_
  rintro s1 ⟨ready1, one1, _, keeps1, frame1, rest1⟩
  replace one1 : numAt s1.mem (State.addr (crtN g.base g.words)) v 7 = 1 := one1
  have mod1 := (keeps_array_num keeps1 fits (op 0 (by simp)) (by decide)).trans modulus
  -- Arrays 5 and 1 cleared.
  rw [WP.seq_iff]
  refine WP.mono (clearArrayWide_ok s1 ready1 (o := 5) (by decide) (by decide)) ?_
  rintro s2 ⟨ready2, cleared2, keeps2, frame2, rest2⟩
  have mod2 := (keeps_array_num keeps2 fits (op 0 (by simp)) (by decide)).trans mod1
  have one2 := (keeps_array_num keeps2 fits (op 7 (by simp)) (by decide)).trans one1
  have zero2 : numAt s2.mem (State.addr (crtN g.base g.words)) v 5 = 0 := numAt_of_cleared cleared2
  rw [WP.seq_iff]
  refine WP.mono (clearArrayWide_ok s2 ready2 (o := 1) (by decide) (by decide)) ?_
  rintro s3 ⟨ready3, cl13, keeps3, frame3, rest3⟩
  have mod3 := (keeps_array_num keeps3 fits (op 0 (by simp)) (by decide)).trans mod2
  have one3 := (keeps_array_num keeps3 fits (op 7 (by simp)) (by decide)).trans one2
  have zero3 := (keeps_array_num keeps3 fits (op 5 (by simp)) (by decide)).trans zero2
  -- `h` into array 1, `l` into array 6.
  have frame13 : Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s.mem s3.mem :=
    frame1.trans (frame2.trans frame3)
  have rest13 : Rest roundClobbers s s3 := rest1.trans (rest2.trans rest3)
  have ctx3 := h.after_narrow ready3 frame13 rest13
  rw [WP.seq_iff]
  refine WP.mono (crt_copyHigh_ok s3 ctx3 (j := 4) (d := 1) (by decide) (by decide) (by decide) half) ?_
  rintro s4 ⟨ready4, high4, keeps4, frame4, rest4⟩
  replace high4 := high4 cl13
  rw [h.child_num (by decide) frame13] at high4
  have mod4 := (keeps_array_num keeps4 fits (op 0 (by simp)) (by decide)).trans mod3
  have one4 := (keeps_array_num keeps4 fits (op 7 (by simp)) (by decide)).trans one3
  have zero4 := (keeps_array_num keeps4 fits (op 5 (by simp)) (by decide)).trans zero3
  have ctx4 := ctx3.after_narrow ready4 frame4 rest4
  rw [WP.seq_iff]
  refine WP.mono (crt_copyLow_ok s4 ctx4 (j := 4) (d := 6) (by decide) (by decide) (by decide)) ?_
  rintro s5 ⟨ready5, low5, keeps5, frame5, rest5⟩
  rw [ctx3.child_num (by decide) frame4, h.child_num (by decide) frame13] at low5
  have mod5 := (keeps_array_num keeps5 fits (op 0 (by simp)) (by decide)).trans mod4
  have one5 := (keeps_array_num keeps5 fits (op 7 (by simp)) (by decide)).trans one4
  have zero5 := (keeps_array_num keeps5 fits (op 5 (by simp)) (by decide)).trans zero4
  have high5 := (keeps_array_num keeps5 fits (op 1 (by simp)) (by decide)).trans high4
  -- `a = h R⁻¹`, `b = l R⁻¹`, `c = b R⁻¹`.
  rw [WP.seq_iff]
  refine WP.mono (montOp_ok s5 ready5 (o := 1) (a := 1) (b := 7) (op 1 (by simp)) (op 1 (by simp))
    (op 7 (by simp)) (by decide) (by rw [one5, mod5]; exact large)) ?_
  rintro s6 ⟨ready6, mod6, lt6, val6, keeps6, frame6, rest6⟩
  rw [mod5] at mod6 lt6 val6
  rw [one5, Nat.mul_one, high5] at val6
  have one6 := (keeps_array_num keeps6 fits (op 7 (by simp)) (by decide)).trans one5
  have zero6 := (keeps_array_num keeps6 fits (op 5 (by simp)) (by decide)).trans zero5
  have low6 := (keeps_array_num keeps6 fits (op 6 (by simp)) (by decide)).trans low5
  rw [WP.seq_iff]
  refine WP.mono (montOp_ok s6 ready6 (o := 6) (a := 6) (b := 7) (op 6 (by simp)) (op 6 (by simp))
    (op 7 (by simp)) (by decide) (by rw [one6, mod6]; exact large)) ?_
  rintro s7 ⟨ready7, mod7, lt7, val7, keeps7, frame7, rest7⟩
  rw [mod6] at mod7 lt7 val7
  rw [one6, Nat.mul_one, low6] at val7
  have one7 := (keeps_array_num keeps7 fits (op 7 (by simp)) (by decide)).trans one6
  have zero7 := (keeps_array_num keeps7 fits (op 5 (by simp)) (by decide)).trans zero6
  have a7 := (keeps_array_num keeps7 fits (op 1 (by simp)) (by decide))
  rw [WP.seq_iff]
  refine WP.mono (montOp_ok s7 ready7 (o := 6) (a := 6) (b := 7) (op 6 (by simp)) (op 6 (by simp))
    (op 7 (by simp)) (by decide) (by rw [one7, mod7]; exact large)) ?_
  rintro s8 ⟨ready8, mod8, lt8, val8, keeps8, frame8, rest8⟩
  rw [mod7] at mod8 lt8 val8
  rw [one7, Nat.mul_one] at val8
  have zero8 := (keeps_array_num keeps8 fits (op 5 (by simp)) (by decide)).trans zero7
  have a8 := (keeps_array_num keeps8 fits (op 1 (by simp)) (by decide)).trans a7
  -- `-a`, `c + a`, and the sum into array 4.
  rw [WP.seq_iff]
  refine WP.mono (subModArray_ok s8 ready8 (o := 4) (a := 5) (b := 1) (op 4 (by simp)) (op 5 (by simp))
    (op 1 (by simp)) (by decide) (by decide) (by decide) (by rw [zero8, mod8]; exact positive)
    (by rw [a8, mod8]; exact lt6)) ?_
  rintro s9 ⟨ready9, neg9, keeps9, frame9, rest9⟩
  rw [zero8, mod8, a8] at neg9
  have mod9 := (keeps_array_num keeps9 fits (op 0 (by simp)) (by decide)).trans mod8
  have c9 := (keeps_array_num keeps9 fits (op 6 (by simp)) (by decide))
  have zero9 := (keeps_array_num keeps9 fits (op 5 (by simp)) (by decide)).trans zero8
  rw [WP.seq_iff]
  refine WP.mono (subModArray_ok s9 ready9 (o := 1) (a := 6) (b := 4) (op 1 (by simp)) (op 6 (by simp))
    (op 4 (by simp)) (by decide) (by decide) (by decide) (by rw [c9, mod9]; exact lt8)
    (by rw [neg9, mod9]; exact Nat.mod_lt _ positive)) ?_
  rintro s10 ⟨ready10, sum10, keeps10, frame10, rest10⟩
  rw [c9, mod9, neg9] at sum10
  have mod10 := (keeps_array_num keeps10 fits (op 0 (by simp)) (by decide)).trans mod9
  have zero10 := (keeps_array_num keeps10 fits (op 5 (by simp)) (by decide)).trans zero9
  refine WP.mono (subModArray_ok s10 ready10 (o := 4) (a := 1) (b := 5) (op 4 (by simp)) (op 1 (by simp))
    (op 5 (by simp)) (by decide) (by decide) (by decide) (by rw [sum10, mod10]; exact Nat.mod_lt _ positive)
    (by rw [zero10, mod10]; exact positive)) ?_
  rintro t ⟨readyT, valT, keepsT, frameT, restT⟩
  rw [sum10, mod10, zero10] at valT
  have sumEq := half_combine (l := numAt s8.mem (State.addr (crtN g.base g.words)) v 6)
    (c := numAt s6.mem (State.addr (crtN g.base g.words)) v 1) positive
  rw [Nat.mod_eq_of_lt lt8, Nat.mod_eq_of_lt lt6] at sumEq
  have valT' : numAt t.mem (State.addr (crtN g.base g.words)) v 4 =
      (numAt s8.mem (State.addr (crtN g.base g.words)) v 6 + numAt s6.mem (State.addr (crtN g.base g.words)) v 1) % M := by
    rw [valT, Nat.sub_zero, Nat.add_mod_right, Nat.mod_mod, sumEq]
  refine ⟨readyT, (keeps_array_num keepsT fits (op 0 (by simp)) (by decide)).trans mod10,
    by rw [valT']; exact Nat.mod_lt _ positive, ?_,
    frame13.trans (frame4.trans (frame5.trans (frame6.trans (frame7.trans (frame8.trans (frame9.trans
      (frame10.trans frameT))))))),
    rest13.trans (rest4.trans (rest5.trans (rest6.trans (rest7.trans (rest8.trans (rest9.trans
      (rest10.trans restT)))))))⟩
  rw [valT', fold_mont val6 val7 val8, Nat.mod_add_div']

/-! ## The counts, the doublings and the squarings -/

/-- The fold's doublings for `w` and `v`. -/
def foldC (w v : Nat) : Nat := if 2 * (w - v) ≤ v then 64 * (v - 2 * (w - v)) + v else 64 * (2 * v - 2 * (w - v))

theorem shl32_ofNat (x k : Nat) : BitVec.ofNat 32 x <<< k = BitVec.ofNat 32 (2 ^ k * x) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_mul_mod, Nat.mul_comm]

theorem DoubleLoopReady.of_regs {s t : State} {base : BitVec 32} {len w c : Nat} {rs : List Reg}
    (h : DoubleLoopReady base len w c s) (mem : t.mem = s.mem) (rest : Rest rs s t) (r0 : Reg.r0 ∉ rs) :
    DoubleLoopReady base len w c t :=
  ⟨h.workspace.congr rest.wr, by rw [mem]; exact h.layout, by rw [mem]; exact h.width,
    (rest.gpr .r0 r0).trans h.ptr, by rw [mem]; exact h.inverse, by rw [mem]; exact h.operand,
    by rw [mem]; exact h.two, by rw [mem]; exact h.counter, by rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead,
    by rw [rest.sp]; exact h.stackSep, by rw [mem, rest.sp]; exact h.saved⟩

theorem DoubleLoopReady.toReady {s : State} {base : BitVec 32} {len w c : Nat}
    (h : DoubleLoopReady base len w c s) (large : 1 < numAt s.mem (State.addr base) w 0) :
    ArithmeticReady base len w s :=
  ⟨h.workspace, h.layout, h.width, h.ptr, h.inverse, large, h.stackRead, h.stackSep, h.saved⟩

/-- `DoubleLoopReady.after_count` for a store that changes other registers. -/
theorem DoubleLoopReady.after_count' {s t : State} {base : BitVec 32} {len w c c' : Nat} {rs : List Reg}
    (h : DoubleLoopReady base len w c s)
    (mem : t.mem = s.mem.writeW (off (State.addr base) 208) (BitVec.ofNat 32 c'))
    (rest : Rest rs s t) (r0 : Reg.r0 ∉ rs) :
    DoubleLoopReady base len w c' t ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧
      numAt t.mem (State.addr base) w 4 = numAt s.mem (State.addr base) w 4 ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 := by
  let u : State := { t with gpr := s.gpr }
  have ru : Rest [.r1] s u := ⟨fun _ _ => rfl, rest.rd, rest.wr, rest.sp⟩
  obtain ⟨d, f, n4, n0⟩ := h.after_count (t := u) mem ru
  exact ⟨⟨d.workspace.congr rfl, d.layout, d.width, (rest.gpr .r0 r0).trans h.ptr, d.inverse, d.operand, d.two,
    d.counter, d.stackRead, d.stackSep, d.saved⟩, f, n4, n0⟩

/-- `foldCountArgs`: `e = 2 (w - v)` into r1, `v` into r2, and Z iff `e ≤ v`. -/
theorem foldCountArgs_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32} {slot v : Nat}
    (h : CrtCopyCtx g bs child slot v s) (half : g.words ≤ 2 * v) :
    WP isa (.block foldCountArgs) s fun t => t.gpr .r1 = BitVec.ofNat 32 (2 * (g.words - v)) ∧
      t.gpr .r2 = BitVec.ofNat 32 v ∧ t.z = decide (2 * (g.words - v) ≤ v) ∧ t.mem = s.mem ∧
      Rest [.r1, .r2, .r3] s t := by
  have words : g.words ≤ 128 := (crt_width_valid h.shared.buffers.lengthValid).2.1
  have le := h.le
  unfold foldCountArgs
  refine VG.Proof.X25519.Arm.WP.append (foldWidths_ok s h) fun u ⟨r1, r2, mem, rest⟩ => ?_
  refine wp_dp (op2_reg _ _) fun a ha => ?_
  refine wp_dp (op2_reg _ _) fun b hb => ?_
  refine wp_dp (op2_reg _ _) fun c hc => ?_
  refine wp_mov (op2_lsr ⟨by decide, by decide⟩) fun d hd => ?_
  refine wp_cmp (op2_imm (by decide)) fun t ht z => WP.block_nil ?_
  have e1 : b.gpr .r1 = BitVec.ofNat 32 (2 * (g.words - v)) := by
    rw [hb.gpr, dpVal, ha.gpr, dpVal, r1, r2, VG.Offset.ofNat_sub_ofNat le, ← BitVec.ofNat_add, ← Nat.two_mul]
  have e2 : b.gpr .r2 = BitVec.ofNat 32 v := by rw [hb.other .r2 (by decide), ha.other .r2 (by decide), r2]
  have r3 : d.gpr .r3 = (BitVec.ofNat 32 v - BitVec.ofNat 32 (2 * (g.words - v))) >>> 31 := by
    rw [hd.gpr, hc.gpr, dpVal, e1, e2]
  refine ⟨by rw [ht.gpr, hd.other .r1 (by decide), hc.other .r1 (by decide)]; exact e1,
    by rw [ht.gpr, hd.other .r2 (by decide), hc.other .r2 (by decide)]; exact e2,
    by rw [z, r3]; exact sub_shr31_eq_zero (by omega) (by omega),
    ht.mem.trans (hd.mem.trans (hc.mem.trans (hb.mem.trans (ha.mem.trans mem)))),
    (rest.mono (by decide)).trans ((ha.rest (by decide)).trans ((hb.rest (by decide)).trans
      ((hc.rest (by decide)).trans ((hd.rest (by decide)).trans (ht.rest _)))))⟩

/-- `foldCounts`: the doublings into header 208. -/
theorem foldCounts_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32} {slot v c : Nat}
    (h : CrtCopyCtx g bs child slot v s) (half : g.words ≤ 2 * v)
    (d : DoubleLoopReady (crtN g.base g.words) (workspaceWords g.words) v c s) :
    WP isa foldCounts s fun t =>
      DoubleLoopReady (crtN g.base g.words) (workspaceWords g.words) v (foldC g.words v) t ∧
      Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s.mem t.mem ∧
      numAt t.mem (State.addr (crtN g.base g.words)) v 4 = numAt s.mem (State.addr (crtN g.base g.words)) v 4 ∧
      numAt t.mem (State.addr (crtN g.base g.words)) v 0 = numAt s.mem (State.addr (crtN g.base g.words)) v 0 ∧
      Rest roundClobbers s t := by
  have le := h.le
  have words : g.words ≤ 128 := (crt_width_valid h.shared.buffers.lengthValid).2.1
  have nw := h.ready.workspace
  have size : 256 ≤ 8 * workspaceWords g.words := h.shared.main.toCrtLayoutState.size
  rw [foldCounts, WP.seq_iff]
  refine WP.mono (foldCountArgs_ok s h half) ?_
  rintro u ⟨r1, r2, z, mem, rest⟩
  have du := d.of_regs mem rest (by decide)
  have a208 : State.addr (u.gpr .r0 + BitVec.ofNat 32 208) = off (State.addr (crtN g.base g.words)) 208 := by
    rw [du.ptr]; exact addr_add (by have := nw.nowrap; omega)
  by_cases hle : 2 * (g.words - v) ≤ v
  · refine WP.ite true (by rw [VG.Proof.X25519.Arm.eval_eq, z, decide_eq_true hle]) (fun _ => ?_) (by simp)
    unfold foldCountLow
    refine wp_dp (op2_reg _ _) fun a ha => ?_
    refine wp_mov (op2_lsl ⟨by decide, by decide⟩) fun b hb => ?_
    refine wp_dp (op2_reg _ _) fun c' hc => ?_
    refine wp_str (a := off (State.addr (crtN g.base g.words)) 208) (by decide)
      (by rw [hc.other .r0 (by decide), hb.other .r0 (by decide), ha.other .r0 (by decide)]; exact a208)
      (by rw [hc.wr, hb.wr, ha.wr]; exact du.workspace.write (by omega)) fun t ht => WP.block_nil ?_
    have val : c'.gpr .r3 = BitVec.ofNat 32 (foldC g.words v) := by
      rw [hc.gpr, dpVal, hb.gpr, ha.gpr, dpVal, hb.other .r2 (by decide), ha.other .r2 (by decide),
        r1, r2, VG.Offset.ofNat_sub_ofNat hle, shl32_ofNat, ← BitVec.ofNat_add, foldC,
        ite_eq_left_iff.mpr (fun h' => absurd hle h')]
    have rt : Rest [.r3] u t := (ha.rest (by decide)).trans ((hb.rest (by decide)).trans
      ((hc.rest (by decide)).trans (ht.rest _)))
    obtain ⟨dt, ft, n4, n0⟩ := du.after_count' (t := t) (c' := foldC g.words v)
      (by rw [ht.mem, hc.mem, hb.mem, ha.mem, val]) rt (by decide)
    exact ⟨dt, by rw [mem] at ft; exact ft, n4.trans (by rw [mem]), n0.trans (by rw [mem]),
      (rest.mono (by decide)).trans (rt.mono (by decide))⟩
  · refine WP.ite false (by rw [VG.Proof.X25519.Arm.eval_eq, z, decide_eq_false hle]) (by simp) (fun _ => ?_)
    unfold foldCountHigh
    refine wp_dp (op2_reg _ _) fun a ha => ?_
    refine wp_dp (op2_reg _ _) fun b hb => ?_
    refine wp_mov (op2_lsl ⟨by decide, by decide⟩) fun c' hc => ?_
    refine wp_str (a := off (State.addr (crtN g.base g.words)) 208) (by decide)
      (by rw [hc.other .r0 (by decide), hb.other .r0 (by decide), ha.other .r0 (by decide)]; exact a208)
      (by rw [hc.wr, hb.wr, ha.wr]; exact du.workspace.write (by omega)) fun t ht => WP.block_nil ?_
    have val : c'.gpr .r3 = BitVec.ofNat 32 (foldC g.words v) := by
      rw [hc.gpr, hb.gpr, dpVal, ha.gpr, dpVal, ha.other .r1 (by decide), r1, r2,
        ← BitVec.ofNat_add, VG.Offset.ofNat_sub_ofNat (by omega), shl32_ofNat, foldC, ite_eq_right_iff.mpr (fun h' => absurd h' hle)]
      congr 1; omega
    have rt : Rest [.r3] u t := (ha.rest (by decide)).trans ((hb.rest (by decide)).trans
      ((hc.rest (by decide)).trans (ht.rest _)))
    obtain ⟨dt, ft, n4, n0⟩ := du.after_count' (t := t) (c' := foldC g.words v)
      (by rw [ht.mem, hc.mem, hb.mem, ha.mem, val]) rt (by decide)
    exact ⟨dt, by rw [mem] at ft; exact ft, n4.trans (by rw [mem]), n0.trans (by rw [mem]),
      (rest.mono (by decide)).trans (rt.mono (by decide))⟩

/-- The doublings' test: Z iff `c = 0`. -/
theorem doublesTest_ok (s : State) {base : BitVec 32} {len w c : Nat}
    (h : DoubleLoopReady base len w c s) (hc : c < 2 ^ 32) :
    WP isa (.block [.ldr .r1 .r0 208, .cmp .r1 (.imm 0)]) s fun t => DoubleLoopReady base len w c t ∧
      t.z = decide (c = 0) ∧ t.mem = s.mem ∧ Rest [.r1] s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  refine wp_ldr (a := off (State.addr base) 208) (by decide)
    (by rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega)) (h.workspace.read (by omega)) fun u a => ?_
  refine wp_cmp (op2_imm (by decide)) fun t ht z => WP.block_nil ?_
  have rt : Rest [.r1] s t := (a.rest (by decide)).trans (ht.rest _)
  refine ⟨h.of_regs (ht.mem.trans a.mem) rt (by decide), ?_, ht.mem.trans a.mem, rt⟩
  rw [z, a.gpr, h.counter, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff,
    show ∀ x : BitVec 32, x - 0 = x from fun x => BitVec.sub_zero x]
  constructor
  · intro e
    have := congrArg BitVec.toNat e
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc] at this
  · rintro rfl; rfl

/-- `foldDoubles`: `c` doublings, none if `c = 0`. -/
theorem foldDoubles_ok (s : State) {base : BitVec 32} {len w c : Nat}
    (h : DoubleLoopReady base len w c s) (hc : c < 2 ^ 32) :
    WP isa foldDoubles s fun t => DoubleLoopReady base len w 0 t ∧
      numAt t.mem (State.addr base) w 4 =
        (2 ^ c * numAt s.mem (State.addr base) w 4) % numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [foldDoubles, WP.seq_iff]
  refine WP.mono (doublesTest_ok s h hc) ?_
  rintro t ⟨ht', zc, memT, rt⟩
  by_cases c0 : c = 0
  · subst c0
    refine WP.ite true (by rw [VG.Proof.X25519.Arm.eval_eq, zc, decide_eq_true rfl]) (fun _ => WP.block_nil ?_) (by simp)
    refine ⟨ht', ?_, by rw [memT], by rw [memT]; exact Frame.refl _ _, rt.mono (by decide)⟩
    rw [memT, Nat.pow_zero, Nat.one_mul, Nat.mod_eq_of_lt h.operand]
  · refine WP.ite false (by rw [VG.Proof.X25519.Arm.eval_eq, zc, decide_eq_false c0]) (by simp) (fun _ => ?_)
    refine WP.mono (doubleLoop_ok t ht' (by omega) hc) ?_
    rintro y ⟨dy, vy, my, fy, ry⟩
    rw [memT] at vy my fy
    exact ⟨dy, vy, my, fy, (rt.mono (by decide)).trans ry⟩

/-- `R2Sq`, its value only under `P`: after a fold, the value is `R_X²` only
for a factor of `n`. -/
structure FoldSq (base : BitVec 32) (len w m : Nat) (P : Prop) (k : Nat) (s : State) : Prop where
  ready : ArithmeticReady base len w s
  modulus : numAt s.mem (State.addr base) w 0 = m
  operand : numAt s.mem (State.addr base) w 4 < m
  value : P → numAt s.mem (State.addr base) w 4 % m = 2 ^ (64 * w + k) % m
  two : w32 s.mem (State.addr base) (arrAt w 7) = 2
  counter : s.mem.readW (off (State.addr base) 208) 32 = BitVec.ofNat 32 0

theorem FoldSq.of_regs {s t : State} {base : BitVec 32} {len w m k : Nat} {P : Prop} {rs : List Reg}
    (h : FoldSq base len w m P k s) (mem : t.mem = s.mem) (rest : Rest rs s t) (r0 : Reg.r0 ∉ rs) :
    FoldSq base len w m P k t :=
  ⟨h.ready.of_mem mem rest ((rest.gpr .r0 r0).trans h.ready.ptr), by rw [mem]; exact h.modulus,
    by rw [mem]; exact h.operand, by rw [mem]; exact h.value, by rw [mem]; exact h.two,
    by rw [mem]; exact h.counter⟩

theorem FoldSq.toDouble {s : State} {base : BitVec 32} {len w m k : Nat} {P : Prop}
    (h : FoldSq base len w m P k s) : DoubleLoopReady base len w 0 s :=
  ⟨h.ready.workspace, h.ready.layout, h.ready.width, h.ready.ptr, h.ready.inverse,
    by rw [h.modulus]; exact h.operand, h.two, h.counter, h.ready.stackRead, h.ready.stackSep, h.ready.saved⟩

/-- `r2Square_ok` under `P`. -/
theorem foldSquare_ok (s : State) {base : BitVec 32} {len w m k : Nat} {P : Prop} (h : FoldSq base len w m P k s) :
    WP isa (squareOp 4 4) s fun t => FoldSq base len w m P (2 * k) t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have hw : 2 ≤ w := h.ready.width ▸ h.ready.layout.1
  have fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op7 : Operand 7 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have odd : m % 2 = 1 := h.modulus ▸ numAt_odd_of_inverse s.mem _ (by omega) h.ready.inverse
  refine WP.mono (squareOp_ok s h.ready op4 op4 (by decide) (by rw [h.modulus]; exact h.operand)) ?_
  rintro t ⟨ready, modulus, bound, value, keeps, frame, rest⟩
  rw [h.modulus] at modulus bound value
  refine ⟨⟨ready, modulus, bound, fun p => r2_square_value odd (h.value p) value, ?_, ?_⟩, frame, rest⟩
  · have := keeps_array_word (d := 0) (bits := 32) keeps fits op7 (by decide) (by omega)
    simp only [Nat.add_zero] at this
    change (t.mem.readW (off (State.addr base) (arrAt w 7)) 32).toNat = 2
    rw [this]; exact h.two
  · rw [keeps_header_readW keeps size (d := 208) (bits := 32) (by decide)]; exact h.counter

/-- `r2Squares_ok` under `P`. -/
theorem foldSquares6_ok (s : State) {base : BitVec 32} {len w m k : Nat} {P : Prop}
    (h : FoldSq base len w m P k s) :
    WP isa r2Squares s fun t => FoldSq base len w m P (64 * k) t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  unfold r2Squares
  refine WP.seq (WP.mono (foldSquare_ok s h) fun s1 ⟨h1, f1, r1⟩ => ?_)
  refine WP.seq (WP.mono (foldSquare_ok s1 h1) fun s2 ⟨h2, f2, r2⟩ => ?_)
  refine WP.seq (WP.mono (foldSquare_ok s2 h2) fun s3 ⟨h3, f3, r3⟩ => ?_)
  refine WP.seq (WP.mono (foldSquare_ok s3 h3) fun s4 ⟨h4, f4, r4⟩ => ?_)
  refine WP.seq (WP.mono (foldSquare_ok s4 h4) fun s5 ⟨h5, f5, r5⟩ => ?_)
  refine WP.mono (foldSquare_ok s5 h5) fun t ⟨h6, f6, r6⟩ => ?_
  refine ⟨?_, f1.trans (f2.trans (f3.trans (f4.trans (f5.trans f6)))),
    r1.trans (r2.trans (r3.trans (r4.trans (r5.trans r6))))⟩
  rw [show 2 * (2 * (2 * (2 * (2 * (2 * k))))) = 64 * k by omega] at h6
  exact h6

/-- `foldSquares`: six squarings if `e ≤ v`, where the doublings stopped at
`2^(64 v + v)`. -/
theorem foldSquares_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32} {slot v M : Nat}
    {P : Prop} (h : CrtCopyCtx g bs child slot v s) (half : g.words ≤ 2 * v)
    (sq : FoldSq (crtN g.base g.words) (workspaceWords g.words) v M P
      (if 2 * (g.words - v) ≤ v then v else 64 * v) s) :
    WP isa foldSquares s fun t => FoldSq (crtN g.base g.words) (workspaceWords g.words) v M P (64 * v) t ∧
      Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  rw [foldSquares, WP.seq_iff]
  refine WP.mono (foldCountArgs_ok s h half) ?_
  rintro u ⟨_, _, z, mem, rest⟩
  have su := sq.of_regs mem rest (by decide)
  by_cases hle : 2 * (g.words - v) ≤ v
  · rw [ite_eq_left_iff.mpr (fun h' => absurd hle h')] at su
    refine WP.ite true (by rw [VG.Proof.X25519.Arm.eval_eq, z, decide_eq_true hle]) (fun _ => ?_) (by simp)
    refine WP.mono (foldSquares6_ok u su) fun t ⟨ht, ft, rt⟩ => ?_
    rw [mem] at ft
    exact ⟨ht, ft, (rest.mono (by decide)).trans rt⟩
  · rw [ite_eq_right_iff.mpr (fun h' => absurd h' hle)] at su
    refine WP.ite false (by rw [VG.Proof.X25519.Arm.eval_eq, z, decide_eq_false hle]) (by simp)
      (fun _ => WP.block_nil ?_)
    exact ⟨su, by rw [mem]; exact Frame.refl _ _, rest.mono (by decide)⟩

/-- The fold: `R² mod n`'s copy in p's workspace reduced, doubled and
squared to `R_X² mod X`, for a factor `X` of `n`. -/
theorem r2Fold_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32} {v M : Nat}
    (h : CrtCopyCtx g bs child 224 v s) (half : g.words ≤ 2 * v)
    (modulus : numAt s.mem (State.addr (crtN g.base g.words)) v 0 = M) :
    WP isa r2Fold s fun t =>
      DoubleLoopReady (crtN g.base g.words) (workspaceWords g.words) v 0 t ∧
      numAt t.mem (State.addr (crtN g.base g.words)) v 0 = M ∧
      (numAt s.mem (State.addr child) g.words 4 % M = 2 ^ (128 * g.words) % M →
        numAt t.mem (State.addr (crtN g.base g.words)) v 4 = 2 ^ (128 * v) % M) ∧
      Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  have words : g.words ≤ 128 := (crt_width_valid h.shared.buffers.lengthValid).2.1
  have le := h.le
  have hv : 2 ≤ v := h.ready.width ▸ h.ready.layout.1
  have fits : arrAt v 8 ≤ 8 * workspaceWords g.words := h.ready.width ▸ h.ready.layout.2.2.1
  have odd : M % 2 = 1 := modulus ▸ numAt_odd_of_inverse s.mem _ (by omega) h.ready.inverse
  have large : 1 < M := modulus ▸ h.ready.modulus
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  rw [r2Fold, WP.seq_iff]
  refine WP.mono (crt_foldReduce_ok s h half modulus) ?_
  rintro s1 ⟨ready1, mod1, lt1, val1, frame1, rest1⟩
  rw [WP.seq_iff]
  refine WP.mono (smallConst_ok s1 (o := 7) 2 ready1 (by decide) (by decide) (by decide) (by decide)) ?_
  rintro s2 ⟨ready2, _, two2, keeps2, frame2, rest2⟩
  have mod2 := (keeps_array_num keeps2 fits op0 (by decide)).trans mod1
  have a2 := keeps_array_num keeps2 fits op4 (by decide)
  have d2 : DoubleLoopReady (crtN g.base g.words) (workspaceWords g.words) v
      (s2.mem.readW (off (State.addr (crtN g.base g.words)) 208) 32).toNat s2 :=
    ⟨ready2.workspace, ready2.layout, ready2.width, ready2.ptr, ready2.inverse,
      by rw [a2, mod2]; exact lt1, two2, by simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq],
      ready2.stackRead, ready2.stackSep, ready2.saved⟩
  have ctx2 := h.after_narrow ready2 (frame1.trans frame2) (rest1.trans rest2)
  rw [WP.seq_iff]
  refine WP.mono (foldCounts_ok s2 ctx2 half d2) ?_
  rintro s3 ⟨d3, frame3, n43, n03, rest3⟩
  have mod3 := n03.trans mod2
  have ctx3 := ctx2.after_narrow (d3.toReady (by rw [mod3]; exact large)) frame3 rest3
  rw [WP.seq_iff]
  refine WP.mono (foldDoubles_ok s3 d3 (by unfold foldC; split <;> omega)) ?_
  rintro s4 ⟨d4, v4, m4, frame4, rest4⟩
  rw [mod3, n43, a2] at v4
  have mod4 := m4.trans mod3
  have ready4 := d4.toReady (by rw [mod4]; exact large)
  have ctx4 := ctx3.after_narrow ready4 frame4 rest4
  have sq4 : FoldSq (crtN g.base g.words) (workspaceWords g.words) v M
      (numAt s.mem (State.addr child) g.words 4 % M = 2 ^ (128 * g.words) % M)
      (if 2 * (g.words - v) ≤ v then v else 64 * v) s4 := by
    refine ⟨ready4, mod4, by rw [← mod4]; exact d4.operand, fun hx => ?_, d4.two, d4.counter⟩
    rw [v4, Nat.mod_mod, Nat.mul_mod, fold_reduced le odd (val1.trans hx), ← Nat.mul_mod, ← Nat.pow_add]
    congr 2
    unfold foldC
    split <;> omega
  refine WP.mono (foldSquares_ok s4 ctx4 half sq4) ?_
  rintro t ⟨sqT, frameT, restT⟩
  refine ⟨sqT.toDouble, sqT.modulus, fun hx => ?_,
    frame1.trans (frame2.trans (frame3.trans (frame4.trans frameT))),
    rest1.trans (rest2.trans (rest3.trans (rest4.trans restT)))⟩
  rw [← Nat.mod_eq_of_lt sqT.operand, sqT.value hx]
  congr 2
  omega

/-- `r2FromN`: `R_X² mod X`, folded from p's copy of `R² mod n` when
`w ≤ 2 v` (then only for a factor of `n`), else computed from 1. -/
theorem r2FromN_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32} {v M : Nat}
    (h : CrtCopyCtx g bs child 224 v s)
    (modulus : numAt s.mem (State.addr (crtN g.base g.words)) v 0 = M) :
    WP isa r2FromN s fun t =>
      DoubleLoopReady (crtN g.base g.words) (workspaceWords g.words) v 0 t ∧
      numAt t.mem (State.addr (crtN g.base g.words)) v 0 = M ∧
      (numAt s.mem (State.addr child) g.words 4 % M = 2 ^ (128 * g.words) % M →
        numAt t.mem (State.addr (crtN g.base g.words)) v 4 = 2 ^ (128 * v) % M) ∧
      Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  have words : g.words ≤ 128 := (crt_width_valid h.shared.buffers.lengthValid).2.1
  have le := h.le
  rw [r2FromN, WP.seq_iff]
  refine WP.mono (foldTest_ok s h) ?_
  rintro u ⟨z, mem, rest⟩
  have readyU := h.ready.of_mem mem rest ((rest.gpr .r0 (by decide)).trans h.ready.ptr)
  have ctxU := h.after_narrow readyU (by rw [mem]; exact Frame.refl _ _) rest
  have modU : numAt u.mem (State.addr (crtN g.base g.words)) v 0 = M := by rw [mem]; exact modulus
  have childU : numAt u.mem (State.addr child) g.words 4 = numAt s.mem (State.addr child) g.words 4 := by rw [mem]
  by_cases half : g.words ≤ 2 * v
  · refine WP.ite true (by rw [VG.Proof.X25519.Arm.eval_eq, z, decide_eq_true half]) (fun _ => ?_) (by simp)
    refine WP.mono (r2Fold_ok u ctxU half modU) fun t ⟨dt, mt, vt, ft, rt⟩ => ?_
    rw [mem, childU] at *
    exact ⟨dt, mt, vt, ft, (rest.mono (by decide)).trans rt⟩
  · refine WP.ite false (by rw [VG.Proof.X25519.Arm.eval_eq, z, decide_eq_false half]) (by simp) (fun _ => ?_)
    refine WP.mono (r2_ok u readyU (by omega)) fun t ⟨dt, vt, mt, ft, rt⟩ => ?_
    rw [mem] at ft
    rw [modU] at vt mt
    exact ⟨dt, mt, fun _ => vt, ft, (rest.mono (by decide)).trans rt⟩

/-- p's workspace's arrays are kept by writes outside it and the stack's
first word. -/
theorem CrtShared.p_num {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {regions : List Region}
    {m m' : Mem} {j : Nat} (h : CrtShared g bs s) (frame : Frame (⟨State.addr s.sp, 4⟩ :: regions) m m')
    (sep : ∀ r ∈ regions, (⟨State.addr (crtP g.base g.words), 8 * workspaceWords g.words⟩ : Region).Disjoint r)
    (hj : j < 8) :
    numAt m' (State.addr (crtP g.base g.words)) g.words j = numAt m (State.addr (crtP g.base g.words)) g.words j := by
  obtain ⟨member, ws, lay, -⟩ := h.child (child := crtP g.base g.words) (slot := 224) (Or.inl ⟨rfl, rfl⟩)
  have fits := lay.layout.2.2.1
  rw [lay.width] at fits
  exact (h.eq_of_frame ws member frame sep).number fits hj

/-- `narrowPrime` with its `R² mod X` folded from p's copy of `R² mod n`. -/
theorem crt_narrowPrimeFrom_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {pp : BitVec 32}
    {v k ps : Nat} {pb : List Byte} (shared : CrtShared g bs s)
    (h : NarrowPrimeInput (crtN g.base g.words) pp (workspaceWords g.words) v k ps pb s) (le : v ≤ g.words) :
    WP isa (narrowPrimeFrom ps) s fun t =>
      let M := safePrime (s.mem.readW (off (State.addr s.sp) 48) 32).toNat (Spec.Rsa.os2ip pb)
      ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v t ∧
      numAt t.mem (State.addr (crtN g.base g.words)) v 0 = M ∧ M % 2 = 1 ∧
      (numAt s.mem (State.addr (crtP g.base g.words)) g.words 4 % M = 2 ^ (128 * g.words) % M →
        numAt t.mem (State.addr (crtN g.base g.words)) v 4 = 2 ^ (128 * v) % M) ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 ∧
      Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  rw [narrowPrimeFrom, WP.seq_iff]
  refine WP.mono (crt_narrowPrimeInv_ok s h) ?_
  rintro u ⟨readyU, modU, odd, flagU, frameU, restU⟩
  have sharedU := shared.after_narrow (frameU.mono (by simp)) restU
  have ctx := sharedU.copyCtx (child := crtP g.base g.words) (slot := 224) (Or.inl ⟨rfl, rfl⟩) readyU le
  have sepP := (shared.child (child := crtP g.base g.words) (slot := 224) (Or.inl ⟨rfl, rfl⟩)).2.2.2.1
  have childU : numAt u.mem (State.addr (crtP g.base g.words)) g.words 4 =
      numAt s.mem (State.addr (crtP g.base g.words)) g.words 4 :=
    shared.p_num (frameU.mono fun _ hr => List.mem_cons_of_mem _ hr)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst r; exact sepP) (by decide)
  have narrowSub := crt_region_sub_workspace shared.buffers.workspace shared.buffers.storageFits
    sharedU.narrow_member
  refine WP.mono (r2FromN_ok u ctx modU) ?_
  rintro t ⟨dt, mt, vt, ft, rt⟩
  rw [childU] at vt
  have flagT : t.mem.readW (off (State.addr t.sp) 48) 32 = u.mem.readW (off (State.addr u.sp) 48) 32 := by
    rw [rt.sp]
    exact ft.readW (r := ⟨off (State.addr u.sp) 48, 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst r
        exact (sharedU.stack.separate.sub_right narrowSub).sub_left (Offset.sub_base _ (by decide)))
      (by decide)
  exact ⟨dt.toReady (by rw [mt, ← modU]; exact readyU.modulus), mt, odd, vt, flagT.trans flagU,
    frameU.trans ft, restU.trans rt⟩

end VG.Proof.Bignum.Arm
