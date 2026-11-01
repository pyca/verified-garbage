module
public import VerifiedGarbage.Proof.Bignum.Arm.Bases
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Impl.Bignum.Arm.Square
public import VerifiedGarbage.Proof.Bignum.Arm.SquareState

import VerifiedGarbage.Proof.Bignum.Arm.SquareBody
import VerifiedGarbage.Proof.Bignum.Arm.MontOpArgs
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.MontMath
import VerifiedGarbage.Proof.Framework.Block

/-! # The Montgomery square in an RSA frame meets `montOp o a a`'s specification -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wordAt wOf numAt Layout Operand Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem keeps_of_square {mem mem' : Mem} {base : BitVec 32} {len w o : Nat}
    (nowrap : base.toNat + 8 * len ≤ 2 ^ 32)
    (outside : Outs (State.addr base)
      [(arrAt w 2, 4 * (2 * (2 * w) + 8)), (arrAt w o, 4 * (2 * w))] mem mem') :
    Keeps (State.addr base) len w o mem mem' := by
  intro i hi separate
  have h2 := separate 2 (by simp [Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
  have h3 := separate 3 (by simp [Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
  have ho := separate o (by simp)
  have e3 : arrAt w 3 = arrAt w 2 + 8 * (w + 2) := by simp only [arrAt]; rw [Nat.add_assoc, ← Nat.succ_mul]
  apply outside
  intro r hr
  have ofsEq : ofs (State.addr base) (State.addr base + BitVec.ofNat 64 i) = i := by
    unfold ofs
    rw [Mem.sub_ofNat_toNat _ (by omega_arith)]
  rw [ofsEq]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp only <;> omega_arith

theorem frame_of_square {mem mem' : Mem} {base : Addr} {size w o : Nat}
    (ho : o < 8) (fit : arrAt w 8 ≤ size)
    (outside : Outs base [(arrAt w 2, 4 * (2 * (2 * w) + 8)), (arrAt w o, 4 * (2 * w))] mem mem') :
    Frame [⟨base, size⟩] mem mem' := by
  have f3 := array_end_le (w := w) (j := 3) (k := 8) (by decide)
  have fo := array_end_le (w := w) ho
  have e3 : arrAt w 3 = arrAt w 2 + 8 * (w + 2) := by simp only [arrAt]; rw [Nat.add_assoc, ← Nat.succ_mul]
  intro x hx
  have h := hx ⟨base, size⟩ (by simp)
  change ¬ ((x - base).toNat + 1 ≤ size) at h
  apply outside
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp only [ofs] <;> omega_arith

/-- The square's environment, from the RSA layout. -/
theorem sqEnv_of_layout (s u : State) {base : BitVec 32} {len o a : Nat} {inv : BitVec 32} {rs : List Reg}
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (ho : Operand o) (ha : Operand a)
    (header : NativeHeader s.mem base (wOf s.mem (State.addr base)) (arrAt (wOf s.mem (State.addr base))) inv)
    (hinv : (val32 s.mem (State.addr base) (arrAt (wOf s.mem (State.addr base)) 0)
      (2 * wOf s.mem (State.addr base)) * inv.toNat + 1) % 2 ^ 32 = 0)
    (operand : numAt s.mem (State.addr base) (wOf s.mem (State.addr base)) a <
      numAt s.mem (State.addr base) (wOf s.mem (State.addr base)) 0)
    (stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, 8 * len⟩)
    (saved : s.mem.readW (State.addr s.sp) 32 = base) (mem : u.mem = s.mem) (rest : Rest rs s u) :
    SqEnv u.mem base (8 * len) (arrAt (wOf s.mem (State.addr base)) o) (arrAt (wOf s.mem (State.addr base)) a)
      (arrAt (wOf s.mem (State.addr base)) 0) (arrAt (wOf s.mem (State.addr base)) 2)
      (2 * wOf s.mem (State.addr base)) inv u := by
  have hw : 2 ≤ wOf s.mem (State.addr base) := layout.1
  have fit : arrAt (wOf s.mem (State.addr base)) 8 ≤ 8 * len := layout.2.2.1
  generalize wOf s.mem (State.addr base) = w at *
  obtain ⟨ho8, ho2, ho3⟩ := ho
  obtain ⟨ha8, ha2, ha3⟩ := ha
  change o ≠ 2 at ho2; change o ≠ 3 at ho3
  change a ≠ 2 at ha2; change a ≠ 3 at ha3
  have f4 := array_end_le (w := w) (j := 3) (k := 4) (by decide)
  have e3 : arrAt w 3 = arrAt w 2 + 8 * (w + 2) := by simp only [arrAt]; rw [Nat.add_assoc, ← Nat.succ_mul]
  have e4 : arrAt w 4 ≤ arrAt w 8 := by simp only [arrAt]; omega_arith
  have region (j : Nat) (hj : j < 8) (h2 : j ≠ 2) (h3 : j ≠ 3) :
      arrAt w 2 + 4 * (2 * (2 * w) + 8) ≤ arrAt w j ∨ arrAt w j + 4 * (2 * w) ≤ arrAt w 2 := by
    rcases Nat.lt_or_ge j 2 with h | h
    · have := array_end_le (w := w) (j := j) (k := 2) h; right; omega_arith
    · have : 4 ≤ j := by omega_arith
      have := Nat.mul_le_mul_right (8 * (w + 2)) this
      left; simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at *; omega_arith
  have fits (j : Nat) (hj : j < 8) : arrAt w j + 4 * (2 * w) ≤ 8 * len := by
    have := array_end_le (w := w) (j := j) (k := 8) (by omega_arith); omega_arith
  refine ⟨ws.congr rest.wr, by omega_arith, by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega_arith, by omega_arith,
    fits a ha8, fits 0 (by decide), fits o ho8, region a ha8 ha2 ha3, region 0 (by decide) (by decide) (by decide),
    region o ho8 ho2 ho3, Outs.refl _ _ _, by rw [rest.rd, rest.wr, rest.sp]; exact stackRead,
    by rw [rest.sp]; exact stackSep, by rw [rest.sp, mem]; exact saved, by rw [mem]; exact header.array 2 (by decide),
    by rw [mem]; exact header.array 0 (by decide), by rw [mem]; exact header.inverse, ?_, by rw [mem]; exact hinv⟩
  rw [mem, ← numAt_native, ← numAt_native]; exact operand

theorem squareBody_ok (s : State) {base : BitVec 32} {len o a : Nat}
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (ho : Operand o) (ha : Operand a)
    (ptr : s.gpr .r0 = base) (po : s.gpr .r2 = BitVec.ofNat 32 o)
    (pa : s.gpr .r3 = BitVec.ofNat 32 a) (pb : s.gpr .r12 = BitVec.ofNat 32 a)
    (inverse : ((word s.mem (State.addr base) (arrAt (wOf s.mem (State.addr base)) 0)).toNat *
      (wordAt s.mem (State.addr base) Proof.Rsa.Mont.minvWord).toNat + 1) % 2 ^ 64 = 0)
    (operand : numAt s.mem (State.addr base) (wOf s.mem (State.addr base)) a <
      numAt s.mem (State.addr base) (wOf s.mem (State.addr base)) 0)
    (stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, 8 * len⟩)
    (saved : s.mem.readW (State.addr s.sp) 32 = base) :
    WP isa squareBody s fun t =>
      let w := wOf s.mem (State.addr base)
      let M := numAt s.mem (State.addr base) w 0
      numAt t.mem (State.addr base) w o < M ∧
      numAt t.mem (State.addr base) w o * 2 ^ (64 * w) % M =
        numAt s.mem (State.addr base) w a * numAt s.mem (State.addr base) w a % M ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  let w := wOf s.mem (State.addr base)
  have hw : 2 ≤ w := layout.1
  have fits : arrAt w 8 ≤ 8 * len := layout.2.2.1
  have header := nativeHeader_of_layout s.mem base ws.nowrap (Nat.le_refl _) layout
  have bound : 128 ≤ 8 * len := by
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits
    omega_arith
  rw [squareBody, WP.seq_iff]
  refine WP.mono (bases_ok s ws bound header ho.1 ha.1 ha.1 ptr po pa pb) ?_
  rintro u ⟨regs, mem, keep⟩
  have envU := sqEnv_of_layout s u ws layout ho ha header
    (native_inverse s.mem (State.addr base) (by omega_arith) inverse) operand stackRead stackSep saved mem keep
  refine WP.mono (sqBody_ok u envU regs.accPtr regs.count regs.aPtr regs.outPtr) ?_
  rintro t ⟨lt, value, outside, rest⟩
  rw [mem] at lt value outside
  refine ⟨?_, ?_, keeps_of_square ws.nowrap outside, frame_of_square ho.1 fits outside, keep.trans rest⟩
  · simpa only [numAt_native] using lt
  · rw [numAt_native, numAt_native, numAt_native, Nat.mul_comm _ (2 ^ (64 * w))]
    simpa only [radix32] using value

theorem squareOp_ok (s : State) {base : BitVec 32} {len w o a : Nat}
    (h : ArithmeticReady base len w s) (ho : Operand o) (ha : Operand a) (ho0 : o ≠ 0)
    (operand : numAt s.mem (State.addr base) w a < numAt s.mem (State.addr base) w 0) :
    WP isa (squareOp o a) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o < numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o * 2 ^ (64 * w) % numAt s.mem (State.addr base) w 0 =
        numAt s.mem (State.addr base) w a * numAt s.mem (State.addr base) w a % numAt s.mem (State.addr base) w 0 ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [squareOp, WP.seq_iff]
  refine WP.mono (montOpArgs_ok s ho.1 ha.1 ha.1) ?_
  rintro u ⟨po, pa, pb, memU, restU⟩
  have ready := h.of_mem memU restU ((restU.gpr .r0 (by decide)).trans h.ptr)
  have body := squareBody_ok u ready.workspace ready.layout ho ha ready.ptr po pa pb
    (by rw [ready.width]; exact ready.inverse) (by rw [ready.width, memU]; exact operand)
    ready.stackRead ready.stackSep ready.saved
  simp only [ready.width] at body
  rw [WP.seq_iff]
  refine WP.mono body ?_
  rintro v ⟨bound, value, keeps, frame, restV⟩
  have savedV := saved_base_kept frame ready.stackSep ready.saved restV.sp
  refine WP.mono (restoreBase_ok v (by rw [restV.rd, restV.wr, restV.sp]; exact ready.stackRead) savedV) ?_
  rintro t ⟨ptr, memT, restT⟩
  rw [memU] at bound value keeps frame
  rw [← memT] at bound value keeps frame
  have rest : Rest roundClobbers s t := (restU.mono (by decide)).trans
    (restV.trans (restT.mono (by decide)))
  obtain ⟨final, modulus⟩ := h.after_array ho0 keeps frame rest ptr
  exact ⟨final, modulus, bound, value, keeps, frame, rest⟩

end VG.Proof.Bignum.Arm
