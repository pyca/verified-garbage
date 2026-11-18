module

public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Ffdh.Arm.Checks
import VerifiedGarbage.Proof.Ffdh.Arm.CheckFlag
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
public import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
public import VerifiedGarbage.Proof.Mont.Words32
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Ffdh.Arm.BelowP`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.SetLowBit`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.LowBit`, which this module and modules that import it used -/

section

/-! Setting the low bit of a packed operand implements the p-1 bound. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Proof.Mont

theorem orOne (n : Nat) : n ||| 1 = n + (1 - n % 2) := by
  have div : (n ||| 1) / 2 = n / 2 := by rw [Nat.or_div_two]; simp
  have mod : (n ||| 1) % 2 = 1 := Nat.or_mod_two_eq_one.mpr (Or.inr rfl)
  omega_using [div, mod]

theorem bitvecOrOne (x : BitVec 32) : (x ||| 1).toNat = x.toNat + (1 - x.toNat % 2) := by
  rw [BitVec.toNat_or, show (1 : BitVec 32).toNat = 1 from rfl, orOne]

theorem val32_setLowBit (m : Mem) (B : Addr) (d k : Nat) (hk : 0 < k)
    (fit : d + 4 * k ≤ 2 ^ 64) :
    val32 (m.writeW (off B d) (m.readW (off B d) 32 ||| 1)) B d k =
      val32 m B d k + (1 - val32 m B d k % 2) := by
  have outside := writeW32_outside m B (m.readW (off B d) 32 ||| 1) (d := d) (by omega_using [hk, fit])
  have tail := outside.val32 (d := d + 4) (k := k - 1) (by right; omega_using []) (by omega_using [hk, fit])
  have count : k = (k - 1) + 1 := by omega_using [hk]
  conv_lhs => rw [count, val32]
  conv_rhs => rw [count, val32]
  rw [w32_write_self, tail, bitvecOrOne]
  change _ = w32 m B d + 2 ^ 32 * val32 m B (d + 4) (k - 1) +
    (1 - (w32 m B d + 2 ^ 32 * val32 m B (d + 4) (k - 1)) % 2)
  have parity : (w32 m B d + 2 ^ 32 * val32 m B (d + 4) (k - 1)) % 2 = w32 m B d % 2 := by
    simp [Nat.add_mod, Nat.mul_mod]
  rw [parity]
  simp only [w32]
  omega_using []

theorem belowOdd (x p : Nat) (odd : p % 2 = 1) :
    x + (1 - x % 2) < p ↔ x < p - 1 := by omega_using [odd]

end VG.Proof.Ffdh.Arm

end

end

/-! The p-1 comparison changes only array 7's low word. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem setLowBit_store (s : State) {base : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s) :
    WP isa (.block VG.Impl.Ffdh.Arm.setLowBit) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) (arrAt w 7))
        (s.mem.readW (off (State.addr base) (arrAt w 7)) 32 ||| 1) ∧ Rest [.r3, .r4] s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have bound := array_end_le (w := w) (by decide : 7 < 8)
  have size : 128 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_using [fits]
  have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  have pointer := header.array 7 (by decide)
  have a120 : State.addr (base + BitVec.ofNat 32 120) = off (State.addr base) 120 :=
    VG.Arm.addr_add (by have := h.workspace.nowrap; omega_using [size, this])
  have arrAddr : State.addr (base + BitVec.ofNat 32 (arrAt w 7)) = off (State.addr base) (arrAt w 7) :=
    VG.Arm.addr_add (by have := h.workspace.nowrap; omega_using [fits, bound, this])
  have rh := h.workspace.read (off := 120) (by omega_using [size])
  have ra := h.workspace.read (off := arrAt w 7) (by omega_using [fits, bound])
  have wa := h.workspace.write (off := arrAt w 7) (by omega_using [fits, bound])
  refine withRest_all [.r3, .r4] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.setLowBit
  ffrun [h.ptr, a120, arrAddr, rh, ra, wa, pointer, off, BitVec.add_zero]

theorem setLowBit_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s) :
    WP isa (.block VG.Impl.Ffdh.Arm.setLowBit) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 7 = numAt s.mem (State.addr base) w 7 +
        (1 - numAt s.mem (State.addr base) w 7 % 2) ∧
      Keeps (State.addr base) len w 7 s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have bound := array_end_le (w := w) (by decide : 7 < 8)
  have nowrap := h.workspace.nowrap
  refine WP.mono (setLowBit_store s h) ?_
  rintro t ⟨mem, restT⟩
  have outside := writeW32_outside s.mem (State.addr base)
    (s.mem.readW (off (State.addr base) (arrAt w 7)) 32 ||| 1) (d := arrAt w 7) (by omega_using [fits, bound, nowrap])
  rw [← mem] at outside
  have wide := outside.mono (o' := arrAt w 7) (n' := 8 * w) (by omega_using []) (by omega_using [hw])
  have keeps := outside_array_keeps wide (len := len) (by omega_using [nowrap])
  have frame := outside_workspace wide (size := 8 * len) (by omega_using [fits, bound])
  have rest : Rest roundClobbers s t := restT.mono (by simp [roundClobbers])
  refine ⟨(h.after_array (by decide : 7 ≠ 0) keeps frame rest
    ((restT.gpr .r0 (by simp)).trans h.ptr)).1, ?_, keeps, frame, rest⟩
  rw [numAt_native, numAt_native, mem]
  exact val32_setLowBit _ _ _ _ (by omega_using [hw]) (by omega_using [fits, bound, nowrap])

end VG.Proof.Ffdh.Arm

end

end

/-! Compare against p-1 using full-width, fixed-schedule native operations. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem belowP_ok (s : State) {base : BitVec 32} {len w a : Nat}
    (h : ArithmeticReady base len w s) (ha : a < 8)
    (odd : numAt s.mem (State.addr base) w 0 % 2 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.belowP a) s fun t => ArithmeticReady base len w t ∧
      t.gpr .r11 = (if numAt s.mem (State.addr base) w a < numAt s.mem (State.addr base) w 0 - 1 then 1 else 0) ∧
      (∀ q, Operand q → q ≠ 7 → numAt t.mem (State.addr base) w q = numAt s.mem (State.addr base) w q) ∧
      t.mem.readW (off (State.addr base) 136) 32 = s.mem.readW (off (State.addr base) 136) 32 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_using [fits]
  rw [VG.Impl.Ffdh.Arm.belowP, WP.seq_iff]
  refine WP.mono (copy_ok s h (by decide : 7 < 8) ha (by decide)) ?_
  rintro u ⟨readyU, valueU, keepsU, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (setLowBit_ok u readyU) ?_
  rintro v ⟨readyV, valueV, keepsV, frameV, restV⟩
  have arraysUV (q : Nat) (hq : Operand q) (nq : q ≠ 7) :=
    (keeps_array_num keepsV fits hq nq).trans (keeps_array_num keepsU fits hq nq)
  refine WP.mono (compare_ok v readyV (by decide : 7 < 8) (by decide : 0 < 8) (by decide) (by decide)) ?_
  rintro t ⟨ready, flag, keepsT, frameT, restT⟩
  refine ⟨ready, ?_, ?_, ?_, frameU.trans (frameV.trans frameT), restU.trans (restV.trans restT)⟩
  · rw [valueV, valueU, arraysUV 0 (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)] at flag
    simp only [belowOdd _ _ odd] at flag
    exact flag
  · intro q hq nq
    exact (keeps_array_num keepsT fits hq hq.2.2).trans (arraysUV q hq nq)
  · exact (keeps_header_readW keepsT size (d := 136) (bits := 32) (by decide)).trans
      ((keeps_header_readW keepsV size (d := 136) (bits := 32) (by decide)).trans
        (keeps_header_readW keepsU size (d := 136) (bits := 32) (by decide)))

end VG.Proof.Ffdh.Arm

end

end

/-! All FFDH value ranges are checked without secret-dependent iteration. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem andFlag_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s) :
    WP isa (.block VG.Impl.Ffdh.Arm.andFlag) s fun t =>
      (t.gpr .r11 = s.gpr .r11 &&& s.mem.readW (off (State.addr base) 136) 32 ∧ t.mem = s.mem) ∧
      Rest [.r3, .r11] s t := by
  have size : 256 ≤ 8 * len := by
    have := h.layout.2.2.1
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at this
    omega_using [this]
  have addr : State.addr (base + BitVec.ofNat 32 136) = off (State.addr base) 136 :=
    VG.Arm.addr_add (by have := h.workspace.nowrap; omega_using [size, this])
  have read := h.workspace.read (off := 136) (by omega_using [size])
  refine withRest_all [.r3, .r11] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.andFlag
  ffrun [h.ptr, addr, read, off]

theorem andFlags (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1 else 0) : BitVec 32) &&& (if q then 1 else 0) =
      (if p ∧ q then 1 else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem inRange_ok (s : State) {base : BitVec 32} {len w a : Nat}
    (h : ArithmeticReady base len w s) (ha : Operand a) (na7 : a ≠ 7)
    (odd : numAt s.mem (State.addr base) w 0 % 2 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.inRange a) s fun t => ArithmeticReady base len w t ∧
      t.gpr .r11 = (if 1 < numAt s.mem (State.addr base) w a ∧
        numAt s.mem (State.addr base) w a < numAt s.mem (State.addr base) w 0 - 1 then 1 else 0) ∧
      (∀ q, Operand q → q ≠ 7 → numAt t.mem (State.addr base) w q = numAt s.mem (State.addr base) w q) ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  rw [VG.Impl.Ffdh.Arm.inRange, WP.seq_iff]
  refine WP.mono (greaterOne_ok s h ha.1 ha.2.2 na7 ha) ?_
  rintro u ⟨readyU, lower, arraysU, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (saveFlag_ok u readyU) ?_
  rintro v ⟨readyV, saved, arraysV, frameV, restV⟩
  have arraysUV (q : Nat) (hq : Operand q) (nq : q ≠ 7) :=
    (arraysV q hq.1).trans (arraysU q hq nq)
  have oddV : numAt v.mem (State.addr base) w 0 % 2 = 1 := by
    rw [arraysUV 0 op0 (by decide)]; exact odd
  rw [WP.seq_iff]
  refine WP.mono (belowP_ok v readyV ha.1 oddV) ?_
  rintro z ⟨readyZ, upper, arraysZ, headerZ, frameZ, restZ⟩
  refine WP.mono (andFlag_ok z readyZ) ?_
  rintro t ⟨⟨flag, memT⟩, restT⟩
  refine ⟨readyZ.of_mem memT restT ((restT.gpr .r0 (by simp)).trans readyZ.ptr), ?_, ?_, ?_, ?_⟩
  · rw [flag, upper, headerZ, saved, lower, arraysUV a ha na7, arraysUV 0 op0 (by decide), andFlags]
    simp only [and_comm]
  · intro q hq nq
    rw [memT, arraysZ q hq nq, arraysUV q hq nq]
  · rw [memT]; exact frameU.trans (frameV.trans frameZ)
  · exact restU.trans ((restV.mono (by simp [roundClobbers])).trans
      (restZ.trans (restT.mono (by simp [roundClobbers]))))

end VG.Proof.Ffdh.Arm
