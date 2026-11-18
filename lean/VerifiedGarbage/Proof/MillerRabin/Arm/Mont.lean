module

public import VerifiedGarbage.Proof.MillerRabin.Arm.Base
public import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.MillerRabin.Arm.Ops
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Rsa.Arm.KcStart
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineBase
public import VerifiedGarbage.Impl.MillerRabin.Arm.Arithmetic
import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineFnBody
import VerifiedGarbage.Proof.Bignum.Arm.FiosFastRound
import VerifiedGarbage.Proof.Bignum.Arm.MontOp
import VerifiedGarbage.Proof.Bignum.Arm.SquareOp
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.Arm.MontOpArgs
import VerifiedGarbage.Proof.Bignum.Arm.MontFnBody
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Framework.Block

/-! ### `MillerRabin.Arm.Arithmetic`, which this module and modules that import it used -/

section

/-! The fused primality-testing kernel preserves the existing fixed-index operation contracts. -/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm.Arithmetic
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Impl.MillerRabin.Arm.Arithmetic
open VG.Proof.Rsa.Mont (Operand numAt Keeps)
open VG.Proof.X25519.Arm (Rest)

private theorem product_fios_ok (s : State) {base : BitVec 32} {len w o a b : Nat}
    (h : ArithmeticReady base len w s) (ho : Operand o) (ha : Operand a) (hb : Operand b) (ho0 : o ≠ 0)
    (operand : numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0) :
    WP isa (product true o a b) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o < numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o * 2 ^ (64 * w) % numAt s.mem (State.addr base) w 0 =
        numAt s.mem (State.addr base) w a * numAt s.mem (State.addr base) w b % numAt s.mem (State.addr base) w 0 ∧
      Proof.Rsa.Mont.Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  simp only [product, ↓reduceIte]
  rw [WP.seq_iff]
  refine WP.mono (montOpArgs_ok s ho.1 ha.1 hb.1) ?_
  rintro u ⟨po, pa, pb, memU, restU⟩
  have ready := h.of_mem memU restU ((restU.gpr .r0 (by simp)).trans h.ptr)
  have body := MontPipeline.fnBody_ok FiosFast.round (MontPipeline.RoundLaw.loop FiosFast.round_law) u ready.workspace ready.layout ho ha hb ready.ptr po pa pb
    (by rw [ready.width]; exact ready.inverse) (by rw [ready.width, memU]; exact operand)
  simp only [ready.width] at body
  rw [WP.seq_iff]
  refine WP.mono body ?_
  rintro v ⟨bound, value, keeps, frame, restV⟩
  have savedV := saved_base_kept frame ready.stackSep ready.saved restV.sp
  refine WP.mono (restoreBase_ok v (by rw [restV.rd, restV.wr, restV.sp]; exact ready.stackRead) savedV) ?_
  rintro t ⟨ptr, memT, restT⟩
  rw [memU] at bound value keeps frame
  rw [← memT] at bound value keeps frame
  have rest : Rest roundClobbers s t := (restU.mono (by simp [roundClobbers])).trans
    (restV.trans (restT.mono (by simp [roundClobbers])))
  obtain ⟨final, modulus⟩ := h.after_array ho0 keeps frame rest ptr
  exact ⟨final, modulus, bound, value, keeps, frame, rest⟩

theorem product_ok (fios : Bool) (s : State) {base : BitVec 32} {len w o a b : Nat}
    (h : ArithmeticReady base len w s) (ho : Operand o) (ha : Operand a) (hb : Operand b) (ho0 : o ≠ 0)
    (operand : numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0) :
    WP isa (product fios o a b) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o < numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o * 2 ^ (64 * w) % numAt s.mem (State.addr base) w 0 =
        numAt s.mem (State.addr base) w a * numAt s.mem (State.addr base) w b % numAt s.mem (State.addr base) w 0 ∧
      Proof.Rsa.Mont.Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  cases fios with
  | false => exact montOp_ok s h ho ha hb ho0 operand
  | true => exact product_fios_ok s h ho ha hb ho0 operand

theorem square_ok (fios : Bool) (s : State) {base : BitVec 32} {len w o a : Nat}
    (h : ArithmeticReady base len w s) (ho : Operand o) (ha : Operand a) (ho0 : o ≠ 0)
    (operand : numAt s.mem (State.addr base) w a < numAt s.mem (State.addr base) w 0) :
    WP isa (square fios o a) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o < numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o * 2 ^ (64 * w) % numAt s.mem (State.addr base) w 0 =
        numAt s.mem (State.addr base) w a * numAt s.mem (State.addr base) w a % numAt s.mem (State.addr base) w 0 ∧
      Proof.Rsa.Mont.Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  cases fios with
  | false => exact squareOp_ok s h ho ha ho0 operand
  | true => exact product_fios_ok s h ho ha ha ho0 operand

end VG.Proof.MillerRabin.Arm.Arithmetic

end

end

/-! # The Miller–Rabin round on ARMv7: the key view's context, and Montgomery products

`ctx_ok`: from `ws` in `r0`, the key view's registers (`Ws`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)

section
variable {P : MP} {σ s t : State} {A : Nat → Nat} {live : List Nat} {V : Nat → Nat} {ls : List Nat}

/-- The low half of header word 6 is `w`. -/
theorem KS.w32_six (h : KS P σ A live V ls s) : s.mem.readW (off (State.addr P.ws) 48) 32 = BitVec.ofNat 32 P.w := by
  have wd : (word s.mem (State.addr P.ws) 48).toNat = P.w := h.width
  rw [word_eq_w32] at wd
  have hw := h.pre.w128
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  show w32 s.mem (State.addr P.ws) 48 = P.w % 2 ^ 32
  omega_using [wd, hw]

/-- `ctx`, from `ws` in `r0`. -/
theorem KS.ctx_ok (h : KS P σ A live V ls s) (r0 : s.gpr .r0 = P.ws) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live V ls t → Ws t P.B P.Z P.W nArr → Rest [.r7, .r8, .r9] s t → t.mem = s.mem →
      WP isa (.block rest) t Q) :
    WP isa (.block (ctx ++ rest)) s Q := by
  have pre := h.pre
  have fit := pre.fit
  have len := pre.len
  have w128 := pre.w128
  unfold ctx
  simp only [List.cons_append, List.append_assoc]
  refine wp_dp (op2_imm (by decide)) fun s1 u1 => ?_
  have rd : InRegions (s1.rd ++ s1.wr) (off (State.addr P.ws) 48) 4 :=
    ⟨P.rS, List.mem_append_right _ (by rw [u1.wr, h.wr, pre.wr]; simp),
      Offset.contains_base _ (by omega_using [len]) (by omega_using [])⟩
  refine wp_ldr (by decide) (by rw [u1.other _ (by decide), r0]; exact addr_add (by omega_using [fit, len])) rd fun s2 u2 => ?_
  refine wp_mov (op2_lsl (by decide)) fun s3 u3 => ?_
  refine wp_dp (op2_imm (by decide)) fun s4 u4 => ?_
  have e9 : s4.gpr .r9 = BitVec.ofNat 32 P.W := by
    rw [u4.gpr, dpVal, u3.gpr, u2.gpr, u1.mem, h.w32_six]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (2 : BitVec 32).toNat = 2 from rfl]
    simp only [MP.W]
    omega_using []
  refine VG.Proof.Rsa.Arm.KeyCheck.stride_ok (by simp only [MP.W]; omega_using [w128]) e9 fun t h7 r m => ?_
  have rt : Rest [.r7, .r8, .r9] s t :=
    (u1.rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans
      (r.mono (by simp)))))
  have mt : t.mem = s.mem := m.trans (u4.mem.trans (u3.mem.trans (u2.mem.trans u1.mem)))
  have ht := h.of_rest rt mt
  have r8 : t.gpr .r8 = P.B := by
    rw [r.gpr _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.gpr, dpVal,
      r0]
  exact k t ht (ht.ws h7 r8 (by rw [r.gpr _ (by decide), e9])) rt mt

/-- A Montgomery multiplication writes, of the key arrays, only its own two and its result's. -/
theorem keep_of_mont (pre : In P σ) {o : Nat} {m m' : Mem}
    (keeps : Proof.Rsa.Mont.Keeps (State.addr P.ws) P.len P.w o m m') (frame : Frame [P.rS] m m') :
    Keep P.B P.W [2, 3, o] [] m m' := by
  have fit := pre.fit
  have len := pre.len
  have hS := pre.S_eq
  intro x hx
  by_cases hin : (x - State.addr P.ws).toNat < 8 * P.len
  · have ex : x = State.addr P.ws + BitVec.ofNat 64 (x - State.addr P.ws).toNat := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
    rw [ex]
    refine keeps _ hin fun j hj => ?_
    by_cases hlo : (x - State.addr P.ws).toNat < kOff
    · simp only [arrAt, Proof.Rsa.Mont.hdrBytes, kOff] at hlo ⊢; omega_using [hlo]
    have hB := pre.ofsB (x := x) (by simp only [ofs]; omega_using [hlo])
    have hj' : (arr P.W j, S P.W) ∈ ranges P.W [2, 3, o] [] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      simp only [ranges, List.map_cons, List.map_nil, List.append_nil, List.mem_cons, List.not_mem_nil,
        or_false]
      rcases hj with rfl | rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl rfl)
      · exact .inr (.inr rfl)
    have h1 := hx _ hj'
    have := pre.arr_eq j
    simp only [ofs] at hB h1
    rw [hB, hS] at h1
    omega_using [h1, this]
  · refine frame x fun r hr hc => hin ?_
    simp only [List.mem_singleton] at hr
    subst hr
    simp only [Region.Contains] at hc
    omega_using [hc]

end

end VG.Proof.MillerRabin.Arm
