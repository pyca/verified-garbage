import VerifiedGarbage.Impl.Ed25519.Arm.Packed
import VerifiedGarbage.Impl.Ed25519.Arm.Field
import VerifiedGarbage.Impl.Ed25519.Arm.Word
import VerifiedGarbage.Proof.X25519.Arm.Verified
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Impl.Ed25519.Arm.FieldMemory
import Mathlib.Logic.Function.Basic
import VerifiedGarbage.Impl.Ed25519.Arm.PointAccumulate
import VerifiedGarbage.Impl.Ed25519.Arm.PointLoop
import VerifiedGarbage.Impl.Ed25519.Arm.PointEncode
import VerifiedGarbage.Impl.Ed25519.Arm.Power
import VerifiedGarbage.Proof.Ed25519.RootPower
import VerifiedGarbage.Proof.Ed25519.BaseTable
import VerifiedGarbage.Impl.Ed25519.Arm.PointPowers
import VerifiedGarbage.Impl.Ed25519.Arm.PointSelect
import VerifiedGarbage.Impl.Ed25519.Arm.BatchBits
import VerifiedGarbage.Impl.Ed25519.Arm.Freeze
import VerifiedGarbage.Impl.Ed25519.Arm.PointEqual
import VerifiedGarbage.Impl.Ed25519.Arm.FieldCheck
import VerifiedGarbage.Impl.Ed25519.Arm.RecoverSign
import VerifiedGarbage.Impl.Ed25519.Arm.ScalarABI
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Impl.Ed25519.Arm.Recover
import VerifiedGarbage.Proof.Ed25519.Recover
import VerifiedGarbage.Impl.Ed25519.Arm.PointDecode
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.Ed25519.Arm.PointBatch
import VerifiedGarbage.Impl.Ed25519.Arm.PointFromScalar
import VerifiedGarbage.Impl.Ed25519.Arm.PointMul
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Impl.Ed25519.Arm.ScalarBase
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Impl.Ed25519.Arm.Verify

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.PointEqual`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.Field`. -/
section

/-!
# Ed25519 on ARMv7: field elements in the working space

The field arithmetic is X25519's (`Proof/X25519/Arm/Field`, `AddSub`, `Mul`,
`Cswap`, `Slots`), in a working space of 8192 bytes (`Ctx`) with the product
at `ACC`.
-/

namespace VG.Proof.Ed25519.Arm

open VG VG.Arm VG.Impl.Ed25519.Arm

/-- `r0` holds the working space `b`, 8192 writable bytes. -/
abbrev Ctx := Proof.X25519.Arm.CtxN 4096

theorem ACC_eq : ACC = 1472 := rfl

/-- The field area `[64, 1600)` of the working space: the elements and `ACC`
(X25519's `FA ACC b`). -/
abbrev FA (b : BitVec 32) : Region := ⟨State.addr b + BitVec.ofNat 64 64, 1536⟩

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.FieldMemory`. -/
section

/-! Constants and copies in the sixteen-limb field workspace. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem slot_range (o : Slot) : 64 ≤ offset o ∧ offset o + 64 ≤ ACC := by
  simp only [offset, ACC]
  omega

theorem slot_sep (o a : Slot) :
    offset o = offset a ∨ offset o + 64 ≤ offset a ∨ offset a + 64 ≤ offset o := by
  simp only [offset]
  omega

/-- A prefix of sixteen independent limb stores. -/
structure FillInv (b : BitVec 32) (o : Nat) (s0 : State) (f : Nat → Nat) (k : Nat)
    (s : State) (ws : List Reg := [.r3]) : Prop where
  rest : Rest ws s0 s
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 o, 4 * k⟩] s0.mem s.mem
  outs : ∀ j < k, limb s.mem (State.addr b) o j = f j

theorem fill_regs_ok {ws : List Reg} (h0 : Reg.r0 ∉ ws) {b : BitVec 32} {o : Nat} {src : Nat → List Instr} {s0 : State}
    {f : Nat → Nat} (hc : VG.Proof.Ed25519.Arm.Ctx b s0) (ho : o + 64 ≤ 4096)
    (hsrc : ∀ k < 16, ∀ s, VG.Proof.Ed25519.Arm.FillInv b o s0 f k s ws →
      WP isa (.block (src k)) s fun t =>
        (t.gpr .r3).toNat = f k ∧ Rest ws s t ∧ t.mem = s.mem) :
    WP isa (.block ((List.range 16).flatMap fun k =>
      src k ++ ([.str .r3 .r0 (o + 4 * k)] : List Instr))) s0 (fun t => VG.Proof.Ed25519.Arm.FillInv b o s0 f 16 t ws) := by
  refine wp_range_flatMap (M := isa) (fun k t => VG.Proof.Ed25519.Arm.FillInv b o s0 f k t ws) (fun k s hk h => ?_)
    16 (Nat.le_refl _) s0 ⟨Rest.refl _ _, Frame.refl _ _, fun j hj => by omega⟩
  refine WP.append (hsrc k hk s h) fun t ⟨hv, hr, hm⟩ => ?_
  refine str0_ok ((hc.of_rest h.rest h0).of_rest hr h0)
    (by omega) fun u hu => WP.block_nil ?_
  have em : u.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 (o + 4 * k))
      (t.gpr .r3) := by rw [hu.mem, hm]
  refine ⟨h.rest.trans (hr.trans (hu.rest _)), ?_, fun j hj => ?_⟩
  · rw [em]
    refine (h.frame.sub fun r hmem => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (Nat.le_add_right _ _)
        (by omega) (by omega))
    rw [List.mem_singleton.mp hmem]
    exact Region.sub_prefix (by omega)
  · rw [limb, em]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
      exact h.outs j hj
    · rw [wd_write_self, hv]

theorem fill_ok {b : BitVec 32} {o : Nat} {src : Nat → List Instr} {s0 : State}
    {f : Nat → Nat} (hc : VG.Proof.Ed25519.Arm.Ctx b s0) (ho : o + 64 ≤ 4096)
    (hsrc : ∀ k < 16, ∀ s, VG.Proof.Ed25519.Arm.FillInv b o s0 f k s →
      WP isa (.block (src k)) s fun t =>
        (t.gpr .r3).toNat = f k ∧ Rest [.r3] s t ∧ t.mem = s.mem) :
    WP isa (.block ((List.range 16).flatMap fun k =>
      src k ++ ([.str .r3 .r0 (o + 4 * k)] : List Instr))) s0 (VG.Proof.Ed25519.Arm.FillInv b o s0 f 16) :=
  VG.Proof.Ed25519.Arm.fill_regs_ok (by decide) hc ho hsrc

theorem val16_digits (v n : Nat) :
    val16 (fun k => v / 2 ^ (16 * k) % 65536) n = v % 2 ^ (16 * n) := by
  induction n with
  | zero => simp only [val16, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]
  | succ n ih =>
    rw [val16_succ, ih, pow16_succ, Nat.mod_mul]

theorem constField_op {b : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (o : Slot)
    (v : Spec.X25519.Fe) :
    WP isa (.block (constField o v)) s fun t =>
      Rest [.r3] s t ∧ Frame [⟨State.addr b + BitVec.ofNat 64 (offset o), 64⟩] s.mem t.mem ∧
      Lim t.mem (State.addr b) (offset o) ∧ FS t.mem (State.addr b) (offset o) = v := by
  have ho := VG.Proof.Ed25519.Arm.slot_range o
  refine WP.mono (VG.Proof.Ed25519.Arm.fill_ok (src := fun k => [.movw .r3 (BitVec.ofNat 16 (v.val / 2 ^ (16 * k)))])
    (f := fun k => v.val / 2 ^ (16 * k) % 65536) hc (by rw [VG.Proof.Ed25519.Arm.ACC_eq] at ho; omega)
    (fun k _ t _ => wp_movw fun u hu => WP.block_nil ⟨?_, hu.rest (by decide), hu.mem⟩))
    fun t ht => ⟨ht.rest, ht.frame, ?_, ?_⟩
  · rw [hu.gpr, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    exact Nat.lt_trans (Nat.mod_lt _ (by decide : 0 < 2 ^ 16)) (by decide)
  · intro k hk
    rw [ht.outs k hk]
    exact Nat.mod_lt _ (by decide)
  · rw [FS, V, val16_congr ht.outs, VG.Proof.Ed25519.Arm.val16_digits, Nat.mod_eq_of_lt]
    · exact VG.Proof.X25519.toFe_self v
    · have := v.isLt
      simp only [Spec.X25519.P] at this
      omega

theorem copyField_op {b : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (o a : Slot)
    (hl : Lim s.mem (State.addr b) (offset a)) :
    WP isa (.block (copyField o a)) s fun t =>
      Rest [.r3] s t ∧ Frame [⟨State.addr b + BitVec.ofNat 64 (offset o), 64⟩] s.mem t.mem ∧
      Lim t.mem (State.addr b) (offset o) ∧
      FS t.mem (State.addr b) (offset o) = FS s.mem (State.addr b) (offset a) := by
  have ho := VG.Proof.Ed25519.Arm.slot_range o
  have ha := VG.Proof.Ed25519.Arm.slot_range a
  have hsep := VG.Proof.Ed25519.Arm.slot_sep o a
  rw [VG.Proof.Ed25519.Arm.ACC_eq] at ho ha
  refine WP.mono (VG.Proof.Ed25519.Arm.fill_ok (src := fun k => [.ldr .r3 .r0 (offset a + 4 * k)])
    (f := limb s.mem (State.addr b) (offset a)) hc (by omega)
    (fun k hk t ht => ldr0_ok (hc.of_rest ht.rest (by decide)) (by omega)
      fun u hu => WP.block_nil ⟨?_, hu.rest (by decide), hu.mem⟩))
    fun t ht => ⟨ht.rest, ht.frame, ?_, ?_⟩
  · rw [hu.gpr]
    exact wd_frame ht.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · intro k hk
    rw [ht.outs k hk]
    exact hl k hk
  · exact congrArg VG.Proof.X25519.toFe (val16_congr ht.outs)

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.Packed`. -/
section

/-! The compact point-table representation. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm
open VG.Spec.X25519 (bytesAt)
open VG.Proof.X25519 (leNum leBytes leNum_append bytesAt_add bytesAt_succ length_bytesAt)

def byteN (m : Mem) (p : Addr) (i : Nat) : Nat := (m (p + BitVec.ofNat 64 i)).toNat
def packedLimb (m : Mem) (p : Addr) (k : Nat) : Nat :=
  VG.Proof.Ed25519.Arm.byteN m p (2 * k) + 256 * VG.Proof.Ed25519.Arm.byteN m p (2 * k + 1)
def packedV (m : Mem) (p : Addr) : Nat := val16 (VG.Proof.Ed25519.Arm.packedLimb m p) 16
def packedF (m : Mem) (p : Addr) : Spec.X25519.Fe := VG.Proof.X25519.toFe (VG.Proof.Ed25519.Arm.packedV m p)

theorem packedLimb_lt (m : Mem) (p : Addr) (k : Nat) : VG.Proof.Ed25519.Arm.packedLimb m p k < 65536 := by
  have := (m (p + BitVec.ofNat 64 (2 * k))).isLt
  have := (m (p + BitVec.ofNat 64 (2 * k + 1))).isLt
  simp only [VG.Proof.Ed25519.Arm.packedLimb, VG.Proof.Ed25519.Arm.byteN]
  omega

theorem leNum_bytesAt2 (m : Mem) (p : Addr) :
    ∀ n, leNum (VG.Spec.X25519.bytesAt m p (2 * n)) = val16 (VG.Proof.Ed25519.Arm.packedLimb m p) n
  | 0 => rfl
  | n + 1 => by
    rw [show 2 * (n + 1) = 2 * n + 2 from rfl, bytesAt_add, leNum_append, VG.Proof.Ed25519.Arm.leNum_bytesAt2 m p n,
      val16_succ, length_bytesAt, show (256 : Nat) ^ (2 * n) = 2 ^ (16 * n) by
        rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; congr 1; omega]
    congr 2
    rw [bytesAt_succ, bytesAt_succ, show VG.Spec.X25519.bytesAt m (p + BitVec.ofNat 64 (2 * n) + 1 + 1) 0 = [] from rfl]
    simp only [leNum, VG.Proof.Ed25519.Arm.packedLimb, VG.Proof.Ed25519.Arm.byteN, Nat.mul_zero, Nat.add_zero]
    rw [Offset.add_ofNat_add_one]

theorem byte_eq {v : BitVec 32} {n : Nat} (h : v.toNat = n) : v.setWidth 8 = BitVec.ofNat 8 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, h]

theorem packedV_eq {m : Mem} {p : Addr} {f : Nat → Nat} (hl : ∀ k < 16, f k < 65536)
    (h0 : ∀ k < 16, m (p + BitVec.ofNat 64 (2 * k)) = BitVec.ofNat 8 (f k))
    (h1 : ∀ k < 16, m (p + BitVec.ofNat 64 (2 * k + 1)) = BitVec.ofNat 8 (f k / 256)) :
    VG.Proof.Ed25519.Arm.packedV m p = val16 f 16 := by
  apply val16_congr
  intro k hk
  simp only [VG.Proof.Ed25519.Arm.packedLimb, VG.Proof.Ed25519.Arm.byteN, h0 k hk, h1 k hk, BitVec.toNat_ofNat]
  have := hl k hk
  omega

theorem packedV_frame {m m' : Mem} {p : Addr} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨p, 32⟩ : Region).Disjoint r) : VG.Proof.Ed25519.Arm.packedV m' p = VG.Proof.Ed25519.Arm.packedV m p := by
  apply val16_congr
  intro k hk
  simp only [VG.Proof.Ed25519.Arm.packedLimb, VG.Proof.Ed25519.Arm.byteN,
    hf.bytes hd (by decide : 32 ≤ 2 ^ 64) (by omega : 2 * k < 32),
    hf.bytes hd (by decide : 32 ≤ 2 ^ 64) (by omega : 2 * k + 1 < 32)]

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.PackField`. -/
section

/-! Store bounded field limbs in a compact 32-byte buffer. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

structure PackInv (p : Addr) (f : Nat → Nat) (s0 : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.r3] s0 s
  frame : Frame [⟨p, 2 * k⟩] s0.mem s.mem
  b0 : ∀ i < k, s.mem (p + BitVec.ofNat 64 (2 * i)) = BitVec.ofNat 8 (f i)
  b1 : ∀ i < k, s.mem (p + BitVec.ofNat 64 (2 * i + 1)) = BitVec.ofNat 8 (f i / 256)

theorem packField_ok {b p : BitVec 32} {a dst : Nat} {s0 : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s0)
    (ha : a + 64 ≤ 4096) (hl : Lim s0.mem (State.addr b) a) (hd : dst + 32 ≤ 4096)
    (hp : s0.gpr .r12 = p) (hfit : p.toNat + dst + 32 ≤ 2 ^ 32)
    (hw : ∀ i < 32, InRegions s0.wr (State.addr p + BitVec.ofNat 64 (dst + i)) 1)
    (hsep : (⟨State.addr b + BitVec.ofNat 64 a, 64⟩ : Region).Disjoint
      ⟨State.addr p + BitVec.ofNat 64 dst, 32⟩) :
    WP isa (.block (packField a dst)) s0 fun t => Rest [.r3] s0 t ∧
      Frame [⟨State.addr p + BitVec.ofNat 64 dst, 32⟩] s0.mem t.mem ∧
      VG.Proof.Ed25519.Arm.packedV t.mem (State.addr p + BitVec.ofNat 64 dst) = V s0.mem (State.addr b) a := by
  let O := State.addr p + BitVec.ofNat 64 dst
  refine WP.mono (wp_range_flatMap (M := isa) (VG.Proof.Ed25519.Arm.PackInv O (limb s0.mem (State.addr b) a) s0)
    (fun k s hk h => ?_) 16 (Nat.le_refl _) s0
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => by omega, fun _ h => by omega⟩)
    fun t ht => ⟨ht.rest, ht.frame, VG.Proof.Ed25519.Arm.packedV_eq hl ht.b0 ht.b1⟩
  have hcs := hc.of_rest h.rest (by decide)
  have hp' : s.gpr .r12 = p := (h.rest.gpr _ (by decide)).trans hp
  have he : wd s.mem (State.addr b) (a + 4 * k) = limb s0.mem (State.addr b) a k :=
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (hsep.sub_left (Offset.sub _ (by omega) (by omega))).sub_right
        (Region.sub_prefix (by omega))
  unfold packStep
  refine ldr0_ok hcs (by omega) fun s1 u1 => ?_
  have e1 : (s1.gpr .r3).toNat = limb s0.mem (State.addr b) a k := by rw [u1.gpr]; exact he
  refine wp_strb (a := O + BitVec.ofNat 64 (2 * k)) (by omega)
    (by rw [u1.other _ (by decide), hp', addr_add (by omega)]; simp only [O, Offset.add_add])
    (by rw [u1.wr, h.rest.wr]; simpa only [O, Offset.add_add] using hw (2 * k) (by omega))
    fun s2 u2 => wp_mov (op2_lsr (by decide)) fun s3 u3 => ?_
  refine wp_strb (a := O + BitVec.ofNat 64 (2 * k + 1)) (by omega)
    (by rw [u3.other _ (by decide), u2.gpr, u1.other _ (by decide), hp', addr_add (by omega)]
        simp only [O, Offset.add_add, Nat.add_assoc])
    (by rw [u3.wr, u2.wr, u1.wr, h.rest.wr]
        simpa only [O, Offset.add_add, Nat.add_assoc] using hw (2 * k + 1) (by omega))
    fun t ht => WP.block_nil ?_
  have hm : t.mem = (s.mem.writeW (O + BitVec.ofNat 64 (2 * k)) ((s1.gpr .r3).setWidth 8)).writeW
      (O + BitVec.ofNat 64 (2 * k + 1)) ((s1.gpr .r3 >>> 8).setWidth 8) := by
    rw [ht.mem, u3.gpr, u2.gpr, u3.mem, u2.mem, u1.mem]
  have ne : ∀ i j : Nat, i < 32 → j < 32 → i ≠ j → O + BitVec.ofNat 64 i ≠ O + BitVec.ofNat 64 j :=
    fun i j hi hj hij => Offset.add_ofNat_ne _ (by omega) (by omega) hij
  refine ⟨h.rest.trans ((u1.rest (by decide)).trans ((u2.rest _).trans
    ((u3.rest (by decide)).trans (ht.rest _)))), ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hm]
    refine ((h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · rw [hm, VG.WriteBytes.writeW8_apply, VG.WriteBytes.writeW8_apply,
      ite_eq_right (ne _ _ (by omega) (by omega) (by omega))]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right (ne _ _ (by omega) (by omega) (by omega))]; exact h.b0 i hi
    · rw [ite_eq_left rfl]; exact VG.Proof.Ed25519.Arm.byte_eq e1
  · rw [hm, VG.WriteBytes.writeW8_apply, VG.WriteBytes.writeW8_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right (ne _ _ (by omega) (by omega) (by omega)),
        ite_eq_right (ne _ _ (by omega) (by omega) (by omega))]
      exact h.b1 i hi
    · rw [ite_eq_left rfl]; exact VG.Proof.Ed25519.Arm.byte_eq (by rw [toNat_shr, e1])

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.UnpackField`. -/
section

/-! Load a compact field into bounded sixteen-bit limbs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem toNat_setWidth8 (v : BitVec 8) : (v.setWidth 32).toNat = v.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans v.isLt (by decide))]

theorem unpackField_ok {b p : BitVec 32} {o src : Nat} {s0 : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s0)
    (ho : o + 64 ≤ 4096) (hs : src + 32 ≤ 4096) (hp : s0.gpr .r12 = p)
    (hfit : p.toNat + src + 32 ≤ 2 ^ 32)
    (hr : ∀ i < 32, InRegions (s0.rd ++ s0.wr) (State.addr p + BitVec.ofNat 64 (src + i)) 1)
    (hsep : (⟨State.addr p + BitVec.ofNat 64 src, 32⟩ : Region).Disjoint
      ⟨State.addr b + BitVec.ofNat 64 o, 64⟩) :
    WP isa (.block (unpackField o src)) s0 fun t => Rest [.r2, .r3] s0 t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩] s0.mem t.mem ∧
      Lim t.mem (State.addr b) o ∧
      V t.mem (State.addr b) o = VG.Proof.Ed25519.Arm.packedV s0.mem (State.addr p + BitVec.ofNat 64 src) := by
  let O := State.addr p + BitVec.ofNat 64 src
  refine WP.mono (VG.Proof.Ed25519.Arm.fill_regs_ok (ws := [.r2, .r3]) (by decide) (src := unpackSrc src)
    (f := VG.Proof.Ed25519.Arm.packedLimb s0.mem O) hc ho (fun k hk s h => ?_))
    fun t ht => ⟨ht.rest, ht.frame, fun k hk => by rw [ht.outs k hk]; exact VG.Proof.Ed25519.Arm.packedLimb_lt _ _ _,
      val16_congr ht.outs⟩
  have hp' : s.gpr .r12 = p := (h.rest.gpr _ (by decide)).trans hp
  have href : ∀ i < 32, s.mem (O + BitVec.ofNat 64 i) = s0.mem (O + BitVec.ofNat 64 i) :=
    fun i hi => h.frame.bytes (fun r hm => by
      rw [List.mem_singleton.mp hm]
      exact hsep.sub_right (Region.sub_prefix (by omega))) (by decide : 32 ≤ 2 ^ 64) hi
  unfold unpackSrc
  refine wp_ldrb (a := O + BitVec.ofNat 64 (2 * k)) (by omega)
    (by rw [hp', addr_add (by omega)]; simp only [O, Offset.add_add])
    (by rw [h.rest.rd, h.rest.wr]; simpa only [O, Offset.add_add] using hr (2 * k) (by omega))
    fun s1 u1 => ?_
  refine wp_ldrb (a := O + BitVec.ofNat 64 (2 * k + 1)) (by omega)
    (by rw [u1.other _ (by decide), hp', addr_add (by omega)]; simp only [O, Offset.add_add, Nat.add_assoc])
    (by rw [u1.rd, u1.wr, h.rest.rd, h.rest.wr]
        simpa only [O, Offset.add_add, Nat.add_assoc] using hr (2 * k + 1) (by omega))
    fun s2 u2 => wp_dp (op2_lsl (by decide)) fun s3 u3 => WP.block_nil ?_
  have el : (s2.gpr .r3).toNat = VG.Proof.Ed25519.Arm.byteN s0.mem O (2 * k) := by
    rw [u2.other _ (by decide), u1.gpr, VG.Proof.Ed25519.Arm.toNat_setWidth8, href _ (by omega)]
    rfl
  have eh : (s2.gpr .r2 <<< 8).toNat = 256 * VG.Proof.Ed25519.Arm.byteN s0.mem O (2 * k + 1) := by
    rw [u2.gpr, u1.mem, toNat_shl, VG.Proof.Ed25519.Arm.toNat_setWidth8, href _ (by omega)]
    have := (s0.mem (O + BitVec.ofNat 64 (2 * k + 1))).isLt
    simp only [VG.Proof.Ed25519.Arm.byteN]
    omega
  refine ⟨?_, (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide))),
    by rw [u3.mem, u2.mem, u1.mem]⟩
  rw [u3.gpr]
  change (s2.gpr .r3 + (s2.gpr .r2 <<< 8)).toNat = _
  rw [toNat_add_lt (by
    rw [el, eh]
    exact Nat.lt_trans (VG.Proof.Ed25519.Arm.packedLimb_lt _ _ _) (by decide)), el, eh]
  rfl

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.FieldProg`. -/
section

/-! Compositional field programs and the extended Edwards formulas. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

abbrev Env := Slot → Spec.X25519.Fe

def env (m : Mem) (b : BitVec 32) : VG.Proof.Ed25519.Arm.Env := fun i => FS m (State.addr b) (offset i)

def AllLim (m : Mem) (b : BitVec 32) : Prop := ∀ i : Slot, Lim m (State.addr b) (offset i)

def evalOp (op : FieldOp) (e : VG.Proof.Ed25519.Arm.Env) : VG.Proof.Ed25519.Arm.Env :=
  match op with
  | .copy o a => Function.update e o (e a)
  | .const o v => Function.update e o v
  | .mul o a b => Function.update e o (e a * e b)
  | .add o a b => Function.update e o (e a + e b)
  | .sub o a b => Function.update e o (e a - e b)

def evalOps (ops : List FieldOp) (e : VG.Proof.Ed25519.Arm.Env) : VG.Proof.Ed25519.Arm.Env := ops.foldl (fun e op => VG.Proof.Ed25519.Arm.evalOp op e) e

structure Keep (b : BitVec 32) (s s' : State) : Prop where
  rest : Rest clob s s'
  frame : Frame [VG.Proof.Ed25519.Arm.FA b] s.mem s'.mem

theorem Keep.refl (b : BitVec 32) (s : State) : VG.Proof.Ed25519.Arm.Keep b s s :=
  ⟨Rest.refl _ _, Frame.refl _ _⟩

theorem Keep.trans {b : BitVec 32} {s t u : State} (h : VG.Proof.Ed25519.Arm.Keep b s t) (k : VG.Proof.Ed25519.Arm.Keep b t u) :
    VG.Proof.Ed25519.Arm.Keep b s u := ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

theorem Keep.ctx {b : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.Arm.Keep b s t) (hs : VG.Proof.Ed25519.Arm.Ctx b s) : VG.Proof.Ed25519.Arm.Ctx b t :=
  hs.of_rest h.rest (by decide)

theorem limb_slot_frame {b : BitVec 32} {m m' : Mem} {o i : Slot} (hne : i ≠ o)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 (offset o), 64⟩,
      ⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] m m') :
    ∀ k < 16, limb m' (State.addr b) (offset i) k = limb m (State.addr b) (offset i) k := by
  have hi := VG.Proof.Ed25519.Arm.slot_range i
  have ho := VG.Proof.Ed25519.Arm.slot_range o
  have hsep : offset i + 64 ≤ offset o ∨ offset o + 64 ≤ offset i := by
    have hv : i.val ≠ o.val := fun e => hne (Fin.ext e)
    simp only [offset]
    omega
  rw [VG.Proof.Ed25519.Arm.ACC_eq] at hi ho
  refine limb_frame hf fun r hr k hk => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · exact Offset.disjoint _ (.inl (by rw [VG.Proof.Ed25519.Arm.ACC_eq]; omega)) (by omega) (by rw [VG.Proof.Ed25519.Arm.ACC_eq]; omega)

theorem field_update {b : BitVec 32} {m m' : Mem} (o : Slot) (hl : VG.Proof.Ed25519.Arm.AllLim m b)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 (offset o), 64⟩,
      ⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] m m')
    (ho : Lim m' (State.addr b) (offset o)) :
    VG.Proof.Ed25519.Arm.AllLim m' b ∧ VG.Proof.Ed25519.Arm.env m' b = Function.update (VG.Proof.Ed25519.Arm.env m b) o (FS m' (State.addr b) (offset o)) := by
  constructor
  · intro i
    by_cases hi : i = o
    · subst hi; exact ho
    · intro k hk
      rw [VG.Proof.Ed25519.Arm.limb_slot_frame hi hf k hk]
      exact hl i k hk
  · funext i
    by_cases hi : i = o
    · subst hi; simp only [Function.update_self, VG.Proof.Ed25519.Arm.env]
    · rw [Function.update_of_ne hi]
      exact congrArg VG.Proof.X25519.toFe (val16_congr (VG.Proof.Ed25519.Arm.limb_slot_frame hi hf))

theorem field_finish {b : BitVec 32} {s t : State} (o : Slot) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem b)
    (hr : Rest clob s t)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 (offset o), 64⟩,
      ⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] s.mem t.mem)
    (ho : Lim t.mem (State.addr b) (offset o)) {v : Spec.X25519.Fe}
    (hv : FS t.mem (State.addr b) (offset o) = v) :
    VG.Proof.Ed25519.Arm.Keep b s t ∧ VG.Proof.Ed25519.Arm.AllLim t.mem b ∧ VG.Proof.Ed25519.Arm.env t.mem b = Function.update (VG.Proof.Ed25519.Arm.env s.mem b) o v := by
  obtain ⟨hlim, he⟩ := VG.Proof.Ed25519.Arm.field_update o hl hf ho
  rw [hv] at he
  exact ⟨⟨hr, frame_FA (by decide) (VG.Proof.Ed25519.Arm.slot_range o) hf⟩, hlim, he⟩

theorem fieldOp_ok {b : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem b)
    (op : FieldOp) :
    WP isa op.code s fun t => VG.Proof.Ed25519.Arm.Keep b s t ∧ VG.Proof.Ed25519.Arm.AllLim t.mem b ∧
      VG.Proof.Ed25519.Arm.env t.mem b = VG.Proof.Ed25519.Arm.evalOp op (VG.Proof.Ed25519.Arm.env s.mem b) := by
  cases op with
  | copy o a =>
    refine WP.mono (VG.Proof.Ed25519.Arm.copyField_op hc o a (hl a)) fun t ⟨hr, hf, ho, hv⟩ => ?_
    exact VG.Proof.Ed25519.Arm.field_finish o hl (hr.mono (by decide)) (frame_o hf) ho hv
  | const o v =>
    refine WP.mono (VG.Proof.Ed25519.Arm.constField_op hc o v) fun t ⟨hr, hf, ho, hv⟩ => ?_
    exact VG.Proof.Ed25519.Arm.field_finish o hl (hr.mono (by decide)) (frame_o hf) ho hv
  | mul o a c =>
    refine WP.mono (mul_ok (by decide) (VG.Proof.Ed25519.Arm.slot_range o).2 (VG.Proof.Ed25519.Arm.slot_range a).2 (VG.Proof.Ed25519.Arm.slot_range c).2 hc (hl a) (hl c))
      fun t ⟨hr, hf, ho, hv⟩ => ?_
    exact VG.Proof.Ed25519.Arm.field_finish o hl hr hf ho (VG.Proof.X25519.toFe_mul hv)
  | add o a c =>
    have ho := VG.Proof.Ed25519.Arm.slot_range o
    have ha := VG.Proof.Ed25519.Arm.slot_range a
    have hb := VG.Proof.Ed25519.Arm.slot_range c
    rw [VG.Proof.Ed25519.Arm.ACC_eq] at ho ha hb
    refine WP.mono (add_ok (by omega) (by omega) (by omega) (VG.Proof.Ed25519.Arm.slot_sep o a) (VG.Proof.Ed25519.Arm.slot_sep o c)
      hc (hl a) (hl c)) fun t ⟨hr, hf, ho, hv⟩ => ?_
    exact VG.Proof.Ed25519.Arm.field_finish o hl hr (frame_o hf) ho (VG.Proof.X25519.toFe_add hv)
  | sub o a c =>
    have ho := VG.Proof.Ed25519.Arm.slot_range o
    have ha := VG.Proof.Ed25519.Arm.slot_range a
    have hb := VG.Proof.Ed25519.Arm.slot_range c
    rw [VG.Proof.Ed25519.Arm.ACC_eq] at ho ha hb
    refine WP.mono (sub_ok (by omega) (by omega) (by omega) (VG.Proof.Ed25519.Arm.slot_sep o a) (VG.Proof.Ed25519.Arm.slot_sep o c)
      hc (hl a) (hl c)) fun t ⟨hr, hf, ho, hv⟩ => ?_
    exact VG.Proof.Ed25519.Arm.field_finish o hl hr (frame_o hf) ho (VG.Proof.X25519.toFe_sub hv)

theorem fieldCode_ok (ops : List FieldOp) {s : State} {b : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx b s)
    (hl : VG.Proof.Ed25519.Arm.AllLim s.mem b) :
    WP isa (fieldCode ops) s fun t => VG.Proof.Ed25519.Arm.Keep b s t ∧ VG.Proof.Ed25519.Arm.AllLim t.mem b ∧
      VG.Proof.Ed25519.Arm.env t.mem b = VG.Proof.Ed25519.Arm.evalOps ops (VG.Proof.Ed25519.Arm.env s.mem b) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, hl, rfl⟩
  | cons op ops ih =>
    rw [fieldCode, WP.seq_iff]
    refine WP.mono (VG.Proof.Ed25519.Arm.fieldOp_ok hc hl op) fun t ⟨ht, hlt, et⟩ => ?_
    refine WP.mono (ih (ht.ctx hc) hlt) fun u ⟨hu, hlu, eu⟩ => ?_
    exact ⟨ht.trans hu, hlu, by rw [eu, et]; rfl⟩

theorem constField_ok {s : State} {b : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem b)
    (o : Slot) (v : Spec.X25519.Fe) :
    WP isa (.block (constField o v)) s fun t => VG.Proof.Ed25519.Arm.Keep b s t ∧ VG.Proof.Ed25519.Arm.AllLim t.mem b ∧
      VG.Proof.Ed25519.Arm.env t.mem b = Function.update (VG.Proof.Ed25519.Arm.env s.mem b) o v := VG.Proof.Ed25519.Arm.fieldOp_ok hc hl (.const o v)

theorem copyField_ok {s : State} {b : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem b)
    (o a : Slot) :
    WP isa (.block (copyField o a)) s fun t => VG.Proof.Ed25519.Arm.Keep b s t ∧ VG.Proof.Ed25519.Arm.AllLim t.mem b ∧
      VG.Proof.Ed25519.Arm.env t.mem b = Function.update (VG.Proof.Ed25519.Arm.env s.mem b) o (VG.Proof.Ed25519.Arm.env s.mem b a) := VG.Proof.Ed25519.Arm.fieldOp_ok hc hl (.copy o a)

/-- Coordinates in four consecutive slots. -/
def point (e : VG.Proof.Ed25519.Arm.Env) (x y z t : Slot) : Spec.Ed25519.Point := ⟨e x, e y, e z, e t⟩

def addResult (e : VG.Proof.Ed25519.Arm.Env) (q : Nat) (hq : q + 3 < 22) : Spec.Ed25519.Point :=
  let x := e ⟨q, by omega⟩
  let y := e ⟨q + 1, by omega⟩
  let z := e ⟨q + 2, by omega⟩
  let t := e ⟨q + 3, by omega⟩
  let a := (e 1 - e 0) * (y - x)
  let b := (e 1 + e 0) * (y + x)
  let c := (e 3 * e 16 + e 3 * e 16) * t
  let dd := (e 2 + e 2) * z
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem pointAdd_formula (e : VG.Proof.Ed25519.Arm.Env) :
    VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.evalOps pointAddOps e) 0 1 2 3 = VG.Proof.Ed25519.Arm.addResult e 4 (by decide) := by
  rfl

theorem pointDouble_formula (e : VG.Proof.Ed25519.Arm.Env) :
    VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.evalOps pointDoubleOps e) 0 1 2 3 = VG.Proof.Ed25519.Arm.addResult e 0 (by decide) := by
  rfl

theorem addResult_eq (e : VG.Proof.Ed25519.Arm.Env) (q : Nat) (hq : q + 3 < 22) (hd : e 16 = Spec.Ed25519.d) :
    VG.Proof.Ed25519.Arm.addResult e q hq = Spec.Ed25519.pointAdd (VG.Proof.Ed25519.Arm.point e 0 1 2 3)
      (VG.Proof.Ed25519.Arm.point e ⟨q, by omega⟩ ⟨q + 1, by omega⟩ ⟨q + 2, by omega⟩ ⟨q + 3, hq⟩) := by
  simp only [VG.Proof.Ed25519.Arm.addResult, VG.Proof.Ed25519.Arm.point, Spec.Ed25519.pointAdd, hd]
  congr 1 <;> grind

theorem pointAdd_eval (e : VG.Proof.Ed25519.Arm.Env) (hd : e 16 = Spec.Ed25519.d) :
    VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.evalOps pointAddOps e) 0 1 2 3 =
      Spec.Ed25519.pointAdd (VG.Proof.Ed25519.Arm.point e 0 1 2 3) (VG.Proof.Ed25519.Arm.point e 4 5 6 7) :=
  (VG.Proof.Ed25519.Arm.pointAdd_formula e).trans (VG.Proof.Ed25519.Arm.addResult_eq e 4 (by decide) hd)

theorem pointDouble_eval (e : VG.Proof.Ed25519.Arm.Env) (hd : e 16 = Spec.Ed25519.d) :
    VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.evalOps pointDoubleOps e) 0 1 2 3 =
      Spec.Ed25519.pointAdd (VG.Proof.Ed25519.Arm.point e 0 1 2 3) (VG.Proof.Ed25519.Arm.point e 0 1 2 3) :=
  (VG.Proof.Ed25519.Arm.pointDouble_formula e).trans (VG.Proof.Ed25519.Arm.addResult_eq e 0 (by decide) hd)

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.Points`. -/
section

/-! Exact extended-coordinate operations and the slots they preserve. -/

namespace VG.Proof.Ed25519.Arm

open VG VG.Arm VG.Impl.Ed25519.Arm

def fieldDest : FieldOp → Slot
  | .copy o _ | .const o _ | .mul o _ _ | .add o _ _ | .sub o _ _ => o

theorem evalOp_unchanged (op : FieldOp) (e : VG.Proof.Ed25519.Arm.Env) (i : Slot) (hi : i ≠ VG.Proof.Ed25519.Arm.fieldDest op) :
    VG.Proof.Ed25519.Arm.evalOp op e i = e i := by
  cases op <;> exact Function.update_of_ne hi _ _

theorem evalOps_unchanged (ops : List FieldOp) (e : VG.Proof.Ed25519.Arm.Env) (i : Slot)
    (hi : ∀ op ∈ ops, i ≠ VG.Proof.Ed25519.Arm.fieldDest op) : VG.Proof.Ed25519.Arm.evalOps ops e i = e i := by
  induction ops generalizing e with
  | nil => rfl
  | cons op ops ih =>
    change VG.Proof.Ed25519.Arm.evalOps ops (VG.Proof.Ed25519.Arm.evalOp op e) i = e i
    rw [ih (VG.Proof.Ed25519.Arm.evalOp op e) (fun p hp => hi p (List.mem_cons_of_mem _ hp)), VG.Proof.Ed25519.Arm.evalOp_unchanged op e i (hi op (by simp))]

theorem point_ops_high (ops : List FieldOp) (hops : ∀ op ∈ ops, (VG.Proof.Ed25519.Arm.fieldDest op).val < 16)
    (e : VG.Proof.Ed25519.Arm.Env) (i : Slot) (hi : 16 ≤ i.val) : VG.Proof.Ed25519.Arm.evalOps ops e i = e i := by
  apply VG.Proof.Ed25519.Arm.evalOps_unchanged
  intro op hop heq
  have h := hops op hop
  have := congrArg Fin.val heq
  omega

theorem pointAdd_high (e : VG.Proof.Ed25519.Arm.Env) (i : Slot) (hi : 16 ≤ i.val) :
    VG.Proof.Ed25519.Arm.evalOps pointAddOps e i = e i :=
  VG.Proof.Ed25519.Arm.point_ops_high _ (by decide) e i hi

theorem pointDouble_high (e : VG.Proof.Ed25519.Arm.Env) (i : Slot) (hi : 16 ≤ i.val) :
    VG.Proof.Ed25519.Arm.evalOps pointDoubleOps e i = e i :=
  VG.Proof.Ed25519.Arm.point_ops_high _ (by decide) e i hi

theorem constPoint_eval (p : Spec.Ed25519.Point) (e : VG.Proof.Ed25519.Arm.Env) :
    VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.evalOps (constPointOps p) e) 0 1 2 3 = p := by cases p; rfl

theorem savePoint_eval (e : VG.Proof.Ed25519.Arm.Env) :
    VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.evalOps savePointOps e) 17 18 19 20 = VG.Proof.Ed25519.Arm.point e 0 1 2 3 := rfl

theorem restorePoint_eval (e : VG.Proof.Ed25519.Arm.Env) :
    VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.evalOps restorePointOps e) 0 1 2 3 = VG.Proof.Ed25519.Arm.point e 17 18 19 20 := rfl

theorem copyPointToQ_eval (e : VG.Proof.Ed25519.Arm.Env) :
    VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.evalOps copyPointToQOps e) 4 5 6 7 = VG.Proof.Ed25519.Arm.point e 0 1 2 3 := rfl

theorem pointDouble_ok {s : State} {base : BitVec 32} (hs : VG.Proof.Ed25519.Arm.Ctx base s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem base)
    (hd : VG.Proof.Ed25519.Arm.env s.mem base 16 = Spec.Ed25519.d) :
    WP isa pointDouble s fun t =>
      VG.Proof.Ed25519.Arm.Keep base s t ∧ VG.Proof.Ed25519.Arm.AllLim t.mem base ∧ VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointAdd (VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env s.mem base) 0 1 2 3) (VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env s.mem base) 0 1 2 3) ∧
      ∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.Arm.env t.mem base i = VG.Proof.Ed25519.Arm.env s.mem base i := by
  refine WP.mono (VG.Proof.Ed25519.Arm.fieldCode_ok pointDoubleOps hs hl) fun t ⟨hk, hlt, hv⟩ => ?_
  rw [hv]
  exact ⟨hk, hlt, VG.Proof.Ed25519.Arm.pointDouble_eval _ hd, VG.Proof.Ed25519.Arm.pointDouble_high _⟩

theorem pointAdd_ok {s : State} {base : BitVec 32} (hs : VG.Proof.Ed25519.Arm.Ctx base s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem base)
    (hd : VG.Proof.Ed25519.Arm.env s.mem base 16 = Spec.Ed25519.d) :
    WP isa pointAdd s fun t =>
      VG.Proof.Ed25519.Arm.Keep base s t ∧ VG.Proof.Ed25519.Arm.AllLim t.mem base ∧ VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointAdd (VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env s.mem base) 0 1 2 3) (VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env s.mem base) 4 5 6 7) ∧
      ∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.Arm.env t.mem base i = VG.Proof.Ed25519.Arm.env s.mem base i := by
  refine WP.mono (VG.Proof.Ed25519.Arm.fieldCode_ok pointAddOps hs hl) fun t ⟨hk, hlt, hv⟩ => ?_
  rw [hv]
  exact ⟨hk, hlt, VG.Proof.Ed25519.Arm.pointAdd_eval _ hd, VG.Proof.Ed25519.Arm.pointAdd_high _⟩

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.PointTableLoad`. -/
section

/-! Merged from `Proof.Ed25519.Arm.PointTable`. -/
section
/-! Compact point tables in the caller's eight-KiB workspace. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem Ctx.ptr_nat {b : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) {o : Nat} (ho : o < 8192) :
    (b + BitVec.ofNat 32 o).toNat = b.toNat + o := by
  have hb := hc.fit
  rw [toNat_add_lt (by rw [toNat_imm (by omega)]; omega), toNat_imm (by omega)]

theorem Ctx.ptr_addr {b : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) {o : Nat} (ho : o < 8192) :
    State.addr (b + BitVec.ofNat 32 o) = State.addr b + BitVec.ofNat 64 o :=
  addr_add (by have := hc.fit; omega)

structure TableKeep (b : BitVec 32) (o n : Nat) (s t : State) : Prop where
  rest : Rest [.r2, .r3] s t
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 o, n⟩] s.mem t.mem

theorem TableKeep.ctx {b : BitVec 32} {s t : State} {o n : Nat}
    (h : VG.Proof.Ed25519.Arm.TableKeep b o n s t) (hc : VG.Proof.Ed25519.Arm.Ctx b s) : VG.Proof.Ed25519.Arm.Ctx b t := hc.of_rest h.rest (by decide)

theorem TableKeep.trans {b : BitVec 32} {s t u : State} {o n : Nat}
    (h : VG.Proof.Ed25519.Arm.TableKeep b o n s t) (k : VG.Proof.Ed25519.Arm.TableKeep b o n t u) : VG.Proof.Ed25519.Arm.TableKeep b o n s u :=
  ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

theorem TableKeep.mono {b : BitVec 32} {s t : State} {o n o' n' : Nat}
    (h : VG.Proof.Ed25519.Arm.TableKeep b o n s t) (ho : o' ≤ o) (hn : o + n ≤ o' + n') : VG.Proof.Ed25519.Arm.TableKeep b o' n' s t :=
  ⟨h.rest, h.frame.sub fun r hm => ⟨_, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hm]; exact Offset.sub _ ho hn⟩⟩

theorem TableKeep.slot {b : BitVec 32} {s t : State} {o n : Nat}
    (h : VG.Proof.Ed25519.Arm.TableKeep b o n s t) (hn : o + n ≤ 8192) (i : Slot)
    (hsep : offset i + 64 ≤ o ∨ o + n ≤ offset i) :
    ∀ k < 16, limb t.mem (State.addr b) (offset i) k = limb s.mem (State.addr b) (offset i) k := by
  have hi := VG.Proof.Ed25519.Arm.slot_range i
  rw [VG.Proof.Ed25519.Arm.ACC_eq] at hi
  refine limb_frame h.frame fun r hm k hk => ?_
  rw [List.mem_singleton.mp hm]
  exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem TableKeep.env {b : BitVec 32} {s t : State} {o n : Nat}
    (h : VG.Proof.Ed25519.Arm.TableKeep b o n s t) (ho : 1600 ≤ o) (hn : o + n ≤ 8192) : VG.Proof.Ed25519.Arm.env t.mem b = VG.Proof.Ed25519.Arm.env s.mem b := by
  funext i
  have hi := VG.Proof.Ed25519.Arm.slot_range i
  rw [VG.Proof.Ed25519.Arm.ACC_eq] at hi
  exact congrArg VG.Proof.X25519.toFe (val16_congr (h.slot hn i (.inl (by omega))))

theorem TableKeep.lim {b : BitVec 32} {s t : State} {o n : Nat}
    (h : VG.Proof.Ed25519.Arm.TableKeep b o n s t) (ho : 1600 ≤ o) (hn : o + n ≤ 8192)
    (hl : VG.Proof.Ed25519.Arm.AllLim s.mem b) : VG.Proof.Ed25519.Arm.AllLim t.mem b := by
  intro i k hk
  have hi := VG.Proof.Ed25519.Arm.slot_range i
  rw [VG.Proof.Ed25519.Arm.ACC_eq] at hi
  rw [h.slot hn i (.inl (by omega)) k hk]
  exact hl i k hk

def tableF (m : Mem) (b : BitVec 32) (o : Nat) : Spec.X25519.Fe :=
  VG.Proof.Ed25519.Arm.packedF m (State.addr b + BitVec.ofNat 64 o)

theorem TableKeep.tableF {b : BitVec 32} {s t : State} {o n d : Nat}
    (h : VG.Proof.Ed25519.Arm.TableKeep b o n s t) (hn : o + n ≤ 8192) (hd : d + 32 ≤ 8192)
    (hsep : d + 32 ≤ o ∨ o + n ≤ d) : VG.Proof.Ed25519.Arm.tableF t.mem b d = VG.Proof.Ed25519.Arm.tableF s.mem b d := by
  refine congrArg VG.Proof.X25519.toFe (VG.Proof.Ed25519.Arm.packedV_frame h.frame fun r hm => ?_)
  rw [List.mem_singleton.mp hm]
  exact Offset.disjoint _ hsep (by omega) (by omega)

theorem toTableQuarter_ok {s : State} {b : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem b)
    {o : Nat} (hp : s.gpr .r12 = b + BitVec.ofNat 32 o) (hlo : 1600 ≤ o)
    (ho : o + 128 ≤ 8192) (j : Nat) (hj : j < 4) :
    WP isa (.block (packField (64 + 64 * j) (32 * j))) s fun t =>
      VG.Proof.Ed25519.Arm.tableF t.mem b (o + 32 * j) = VG.Proof.Ed25519.Arm.env s.mem b ⟨j, by omega⟩ ∧
      VG.Proof.Ed25519.Arm.TableKeep b (o + 32 * j) 32 s t := by
  have ea := hc.ptr_addr (by omega : o < 8192)
  refine WP.mono (VG.Proof.Ed25519.Arm.packField_ok hc (by omega) (hl ⟨j, by omega⟩) (by omega) hp
    (by rw [hc.ptr_nat (by omega)]; have := hc.fit; omega)
    (fun i hi => by rw [ea, Offset.add_add]; exact in_base hc.wr (by omega) (by omega))
    (by rw [ea, Offset.add_add]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)))
    fun t ⟨hr, hf, hv⟩ => ?_
  rw [ea, Offset.add_add] at hf hv
  exact ⟨congrArg VG.Proof.X25519.toFe hv, ⟨hr.mono (by decide), hf⟩⟩

theorem toTablePrefix_ok {s : State} {b : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem b)
    {o : Nat} (hp : s.gpr .r12 = b + BitVec.ofNat 32 o) (hlo : 1600 ≤ o)
    (ho : o + 128 ≤ 8192) (n : Nat) (hn : n ≤ 4) :
    WP isa (.block ((List.range n).flatMap fun j => packField (64 + 64 * j) (32 * j))) s fun t =>
      (∀ j (hj : j < n), VG.Proof.Ed25519.Arm.tableF t.mem b (o + 32 * j) = VG.Proof.Ed25519.Arm.env s.mem b ⟨j, by omega⟩) ∧
      VG.Proof.Ed25519.Arm.TableKeep b o (32 * n) s t := by
  induction n generalizing s with
  | zero => exact WP.block_nil ⟨fun _ h => by omega, ⟨Rest.refl _ _, Frame.refl _ _⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hc hl hp (by omega)) fun t ⟨hv, hk⟩ => ?_
    refine WP.mono (VG.Proof.Ed25519.Arm.toTableQuarter_ok (hk.ctx hc) (hk.lim hlo (by omega) hl)
      ((hk.rest.gpr _ (by decide)).trans hp) hlo ho n (by omega)) fun u ⟨hu, ku⟩ => ?_
    refine ⟨fun j hj => ?_, (hk.mono (by omega) (by omega)).trans (ku.mono (by omega) (by omega))⟩
    by_cases h : j < n
    · rw [ku.tableF (by omega) (by omega) (.inl (by omega)), hv j h]
    · have e : j = n := by omega
      subst j
      rw [hu, hk.env hlo (by omega)]

def tablePoint (m : Mem) (b : BitVec 32) (o : Nat) : Spec.Ed25519.Point :=
  ⟨VG.Proof.Ed25519.Arm.tableF m b o, VG.Proof.Ed25519.Arm.tableF m b (o + 32), VG.Proof.Ed25519.Arm.tableF m b (o + 64), VG.Proof.Ed25519.Arm.tableF m b (o + 96)⟩

theorem pointToTable_ok {s : State} {b : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem b)
    {o : Nat} (hp : s.gpr .r12 = b + BitVec.ofNat 32 o) (hlo : 1600 ≤ o)
    (ho : o + 128 ≤ 8192) :
    WP isa (.block pointToTable) s fun t => VG.Proof.Ed25519.Arm.tablePoint t.mem b o = VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env s.mem b) 0 1 2 3 ∧
      VG.Proof.Ed25519.Arm.TableKeep b o 128 s t := by
  refine WP.mono (VG.Proof.Ed25519.Arm.toTablePrefix_ok hc hl hp hlo ho 4 (by decide)) fun t ⟨hv, hk⟩ => ?_
  have h0 := hv 0 (by decide)
  have h1 := hv 1 (by decide)
  have h2 := hv 2 (by decide)
  have h3 := hv 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
  refine ⟨?_, hk⟩
  simp only [VG.Proof.Ed25519.Arm.tablePoint, VG.Proof.Ed25519.Arm.point, h0, h1, h2, h3]
  rfl

end VG.Proof.Ed25519.Arm
end

/-! Restore compact table entries into working point coordinates. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem fromTableQuarter_ok {s : State} {b : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem b)
    {o : Nat} (hp : s.gpr .r12 = b + BitVec.ofNat 32 o) (hlo : 1600 ≤ o)
    (ho : o + 128 ≤ 8192) (j : Nat) (hj : j < 4) :
    WP isa (.block (unpackField (64 + 64 * j) (32 * j))) s fun t =>
      VG.Proof.Ed25519.Arm.env t.mem b ⟨j, by omega⟩ = VG.Proof.Ed25519.Arm.tableF s.mem b (o + 32 * j) ∧ VG.Proof.Ed25519.Arm.AllLim t.mem b ∧
      VG.Proof.Ed25519.Arm.TableKeep b (64 + 64 * j) 64 s t := by
  have ea := hc.ptr_addr (by omega : o < 8192)
  refine WP.mono (VG.Proof.Ed25519.Arm.unpackField_ok hc (by omega) (by omega) hp
    (by rw [hc.ptr_nat (by omega)]; have := hc.fit; omega)
    (fun i hi => by
      rw [ea, Offset.add_add]
      exact in_base (List.mem_append_right _ hc.wr) (by omega) (by omega))
    (by rw [ea, Offset.add_add]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)))
    fun t ⟨hr, hf, hlt, hv⟩ => ?_
  rw [ea, Offset.add_add] at hv
  have hu := VG.Proof.Ed25519.Arm.field_update ⟨j, by omega⟩ hl (frame_o hf) hlt
  exact ⟨congrArg VG.Proof.X25519.toFe hv, hu.1, ⟨hr, hf⟩⟩

theorem fromTablePrefix_ok {s : State} {b : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem b)
    {o : Nat} (hp : s.gpr .r12 = b + BitVec.ofNat 32 o) (hlo : 1600 ≤ o)
    (ho : o + 128 ≤ 8192) (n : Nat) (hn : n ≤ 4) :
    WP isa (.block ((List.range n).flatMap fun j => unpackField (64 + 64 * j) (32 * j))) s fun t =>
      (∀ j (hj : j < n), VG.Proof.Ed25519.Arm.env t.mem b ⟨j, by omega⟩ = VG.Proof.Ed25519.Arm.tableF s.mem b (o + 32 * j)) ∧
      VG.Proof.Ed25519.Arm.AllLim t.mem b ∧ VG.Proof.Ed25519.Arm.TableKeep b 64 (64 * n) s t := by
  induction n generalizing s with
  | zero => exact WP.block_nil ⟨fun _ h => by omega, hl, ⟨Rest.refl _ _, Frame.refl _ _⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hc hl hp (by omega)) fun t ⟨hv, hlt, hk⟩ => ?_
    refine WP.mono (VG.Proof.Ed25519.Arm.fromTableQuarter_ok (hk.ctx hc) hlt
      ((hk.rest.gpr _ (by decide)).trans hp) hlo ho n (by omega)) fun u ⟨hu, hlu, ku⟩ => ?_
    refine ⟨fun j hj => ?_, hlu,
      (hk.mono (by omega) (by omega)).trans (ku.mono (by omega) (by omega))⟩
    by_cases h : j < n
    · have he : VG.Proof.Ed25519.Arm.env u.mem b ⟨j, by omega⟩ = VG.Proof.Ed25519.Arm.env t.mem b ⟨j, by omega⟩ :=
        congrArg VG.Proof.X25519.toFe (val16_congr (ku.slot (by omega) ⟨j, by omega⟩
          (.inl (by simp only [offset]; omega))))
      rw [he, hv j h]
    · have e : j = n := by omega
      subst j
      rw [hu, hk.tableF (by omega) (by omega) (.inr (by omega))]

theorem pointFromTable_ok {s : State} {b : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem b)
    {o : Nat} (hp : s.gpr .r12 = b + BitVec.ofNat 32 o) (hlo : 1600 ≤ o)
    (ho : o + 128 ≤ 8192) :
    WP isa (.block pointFromTable) s fun t => VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env t.mem b) 0 1 2 3 = VG.Proof.Ed25519.Arm.tablePoint s.mem b o ∧
      VG.Proof.Ed25519.Arm.AllLim t.mem b ∧ VG.Proof.Ed25519.Arm.TableKeep b 64 256 s t := by
  refine WP.mono (VG.Proof.Ed25519.Arm.fromTablePrefix_ok hc hl hp hlo ho 4 (by decide)) fun t ⟨hv, hlt, hk⟩ => ?_
  have h0 := hv 0 (by decide)
  have h1 := hv 1 (by decide)
  have h2 := hv 2 (by decide)
  have h3 := hv 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
  refine ⟨?_, hlt, hk⟩
  change VG.Proof.Ed25519.Arm.env t.mem b 0 = _ at h0
  change VG.Proof.Ed25519.Arm.env t.mem b 1 = _ at h1
  change VG.Proof.Ed25519.Arm.env t.mem b 2 = _ at h2
  change VG.Proof.Ed25519.Arm.env t.mem b 3 = _ at h3
  simp only [VG.Proof.Ed25519.Arm.tablePoint, VG.Proof.Ed25519.Arm.point, h0, h1, h2, h3]

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.Power`. -/
section

/-! Merged from `Proof.Ed25519.Arm.PowerEnv`. -/
section
/-! Compositional field exponentiation and fixed-count squaring loops. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm
open VG.Proof.X25519 (sqn)

def opMul (o a b : Slot) (e : VG.Proof.Ed25519.Arm.Env) : VG.Proof.Ed25519.Arm.Env := Function.update e o (e a * e b)

/-- Field work and its fixed-count squaring counter. -/
structure IKeep (b : BitVec 32) (s t : State) : Prop where
  rest : Rest (.r10 :: clob) s t
  frame : Frame [VG.Proof.Ed25519.Arm.FA b] s.mem t.mem

theorem IKeep.trans {b : BitVec 32} {s t u : State} (h : VG.Proof.Ed25519.Arm.IKeep b s t) (k : VG.Proof.Ed25519.Arm.IKeep b t u) :
    VG.Proof.Ed25519.Arm.IKeep b s u := ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

theorem IKeep.ctx {b : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.Arm.IKeep b s t) (hc : VG.Proof.Ed25519.Arm.Ctx b s) : VG.Proof.Ed25519.Arm.Ctx b t :=
  hc.of_rest h.rest (by decide)

theorem IKeep.of_counter {b : BitVec 32} {s t : State} (hr : Rest [.r10] s t)
    (hm : t.mem = s.mem) : VG.Proof.Ed25519.Arm.IKeep b s t :=
  ⟨hr.mono (by decide), by rw [hm]; exact Frame.refl _ _⟩

def ISpec (b : BitVec 32) (c : Prog isa) (f : VG.Proof.Ed25519.Arm.Env → VG.Proof.Ed25519.Arm.Env) : Prop :=
  ∀ s, VG.Proof.Ed25519.Arm.Ctx b s → VG.Proof.Ed25519.Arm.AllLim s.mem b → WP isa c s fun t =>
    VG.Proof.Ed25519.Arm.IKeep b s t ∧ VG.Proof.Ed25519.Arm.AllLim t.mem b ∧ VG.Proof.Ed25519.Arm.env t.mem b = f (VG.Proof.Ed25519.Arm.env s.mem b)

theorem ISpec.seq {b : BitVec 32} {c₁ c₂ : Prog isa} {f g : VG.Proof.Ed25519.Arm.Env → VG.Proof.Ed25519.Arm.Env}
    (h₁ : VG.Proof.Ed25519.Arm.ISpec b c₁ f) (h₂ : VG.Proof.Ed25519.Arm.ISpec b c₂ g) : VG.Proof.Ed25519.Arm.ISpec b (.seq c₁ c₂) fun e => g (f e) :=
  fun s hc hl => WP.seq (WP.mono (h₁ s hc hl) fun _ ⟨k₁, l₁, e₁⟩ =>
    WP.mono (h₂ _ (k₁.ctx hc) l₁) fun _ ⟨k₂, l₂, e₂⟩ =>
      ⟨k₁.trans k₂, l₂, by rw [e₂, e₁]⟩)

theorem mulI_ok {s : State} {base : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx base s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem base)
    (o a b : Slot) :
    WP isa (mulP o a b) s fun t => VG.Proof.Ed25519.Arm.IKeep base s t ∧ VG.Proof.Ed25519.Arm.AllLim t.mem base ∧
      t.gpr .r10 = s.gpr .r10 ∧ VG.Proof.Ed25519.Arm.env t.mem base = VG.Proof.Ed25519.Arm.opMul o a b (VG.Proof.Ed25519.Arm.env s.mem base) :=
  WP.mono (VG.Proof.Ed25519.Arm.fieldOp_ok hc hl (.mul o a b)) fun _ ⟨hk, hlt, he⟩ =>
    ⟨⟨hk.rest.mono (by decide), hk.frame⟩, hlt, hk.rest.gpr _ (by decide), he⟩

theorem mulI (base : BitVec 32) (o a b : Slot) : VG.Proof.Ed25519.Arm.ISpec base (mulP o a b) (VG.Proof.Ed25519.Arm.opMul o a b) :=
  fun _ hc hl => WP.mono (VG.Proof.Ed25519.Arm.mulI_ok hc hl o a b) fun _ ⟨hk, hlt, _, he⟩ => ⟨hk, hlt, he⟩

theorem decR10_ok {s : State} {k : Nat} (hk : k < 2 ^ 32)
    (hb : s.gpr .r10 = BitVec.ofNat 32 (k + 1)) :
    WP isa (.block [.subs .r10 .r10 (.imm 1)]) s fun t =>
      t.gpr .r10 = BitVec.ofNat 32 k ∧ t.z = decide (k = 0) ∧
      Rest [.r10] s t ∧ t.mem = s.mem := by
  refine wp_subs (op2_imm (by decide)) fun t ht hz => WP.block_nil ?_
  have he : s.gpr .r10 - 1 = BitVec.ofNat 32 k := by
    rw [hb, BitVec.ofNat_add]
    change BitVec.ofNat 32 k + (1 : BitVec 32) - 1 = _
    exact BitVec.add_sub_cancel _ _
  exact ⟨ht.gpr.trans he, by rw [hz, he, ofNat_beq_zero hk], ht.rest (by decide), ht.mem⟩

def opSqn (o a : Slot) (n : Nat) (e : VG.Proof.Ed25519.Arm.Env) : VG.Proof.Ed25519.Arm.Env := Function.update e o (sqn (e a) n)

theorem opMul_update (o : Slot) (e : VG.Proof.Ed25519.Arm.Env) (v : Spec.X25519.Fe) :
    VG.Proof.Ed25519.Arm.opMul o o o (Function.update e o v) = Function.update e o (v * v) := by
  simp only [VG.Proof.Ed25519.Arm.opMul, Function.update_self, Function.update_idem]

theorem sqLoop_ok {s₀ : State} {base : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx base s₀)
    (o : Slot) (x : Spec.X25519.Fe) (n : Nat) (hn : n < 65536) :
    ∀ m s, 1 ≤ m → m < n → VG.Proof.Ed25519.Arm.IKeep base s₀ s → VG.Proof.Ed25519.Arm.AllLim s.mem base →
      s.gpr .r10 = BitVec.ofNat 32 m →
      VG.Proof.Ed25519.Arm.env s.mem base = Function.update (VG.Proof.Ed25519.Arm.env s₀.mem base) o (sqn x (n - m)) →
      WP isa (.loop (.seq (mulP o o o) (.block [.subs .r10 .r10 (.imm 1)])) .ne) s fun t =>
        VG.Proof.Ed25519.Arm.IKeep base s₀ t ∧ VG.Proof.Ed25519.Arm.AllLim t.mem base ∧
        VG.Proof.Ed25519.Arm.env t.mem base = Function.update (VG.Proof.Ed25519.Arm.env s₀.mem base) o (sqn x n) := by
  intro m s h1 h2 hk hl hb he
  refine WP.loop (M := isa) (Inv := fun m (s : State) =>
    1 ≤ m ∧ m < n ∧ VG.Proof.Ed25519.Arm.IKeep base s₀ s ∧ VG.Proof.Ed25519.Arm.AllLim s.mem base ∧
    s.gpr .r10 = BitVec.ofNat 32 m ∧
    VG.Proof.Ed25519.Arm.env s.mem base = Function.update (VG.Proof.Ed25519.Arm.env s₀.mem base) o (sqn x (n - m))) ?_
    m s ⟨h1, h2, hk, hl, hb, he⟩
  intro m s ⟨h1, h2, hk, hl, hb, he⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.mulI_ok (hk.ctx hc) hl o o o) fun s1 ⟨k1, l1, b1, e1⟩ => ?_)
  refine WP.mono (VG.Proof.Ed25519.Arm.decR10_ok (by omega) (b1.trans hb)) fun s2 ⟨b2, z2, r2, mem2⟩ => ?_
  have k2 : VG.Proof.Ed25519.Arm.IKeep base s₀ s2 := hk.trans (k1.trans (IKeep.of_counter r2 mem2))
  have l2 : VG.Proof.Ed25519.Arm.AllLim s2.mem base := by rw [mem2]; exact l1
  have e2 : VG.Proof.Ed25519.Arm.env s2.mem base = Function.update (VG.Proof.Ed25519.Arm.env s₀.mem base) o (sqn x (n - m)) := by
    rw [mem2, e1, he, VG.Proof.Ed25519.Arm.opMul_update]
    apply congrArg (Function.update (VG.Proof.Ed25519.Arm.env s₀.mem base) o)
    rw [show n - m = (n - (m + 1)) + 1 by omega]
    rfl
  simp only [VG.Arm.eval, z2]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, k2, l2, by rw [e2, Nat.sub_zero]⟩
  · exact .inr ⟨by simp only [decide_eq_false (by omega : m ≠ 0), Bool.not_false],
      m, by omega, by omega, by omega, k2, l2, b2, e2⟩

theorem sqnI (base : BitVec 32) (o a : Slot) (n : Nat) (hn : 2 ≤ n) (hn' : n < 65536) :
    VG.Proof.Ed25519.Arm.ISpec base (Impl.Ed25519.Arm.sqn o a n) (VG.Proof.Ed25519.Arm.opSqn o a n) := by
  intro s hc hl
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.mulI_ok hc hl o a a) fun s1 ⟨k1, l1, _, e1⟩ => ?_)
  refine WP.seq (wp_movw fun s2 h2 => WP.block_nil ?_)
  have b2 : s2.gpr .r10 = BitVec.ofNat 32 (n - 1) := by
    rw [h2.gpr]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : n - 1 < 2 ^ 16)]
  have k2 : VG.Proof.Ed25519.Arm.IKeep base s s2 := k1.trans (IKeep.of_counter (h2.rest (by decide)) h2.mem)
  refine VG.Proof.Ed25519.Arm.sqLoop_ok hc o (VG.Proof.Ed25519.Arm.env s.mem base a) n hn' (n - 1) s2 (by omega) (by omega) k2
    (by rw [h2.mem]; exact l1) b2 ?_
  rw [h2.mem, e1, show n - (n - 1) = 1 by omega]
  rfl

end VG.Proof.Ed25519.Arm
end

/-! The shared addition chain computes inversion and square-root powers. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

def power250Env (e : VG.Proof.Ed25519.Arm.Env) : VG.Proof.Ed25519.Arm.Env :=
  VG.Proof.Ed25519.Arm.opMul 15 16 15 (VG.Proof.Ed25519.Arm.opSqn 16 16 50 (VG.Proof.Ed25519.Arm.opMul 16 17 16 (VG.Proof.Ed25519.Arm.opSqn 17 16 100
    (VG.Proof.Ed25519.Arm.opMul 16 16 15 (VG.Proof.Ed25519.Arm.opSqn 16 15 50 (VG.Proof.Ed25519.Arm.opMul 15 16 15 (VG.Proof.Ed25519.Arm.opSqn 16 16 10 (VG.Proof.Ed25519.Arm.opMul 16 17 16 (VG.Proof.Ed25519.Arm.opSqn 17 16 20
    (VG.Proof.Ed25519.Arm.opMul 16 16 15 (VG.Proof.Ed25519.Arm.opSqn 16 15 10 (VG.Proof.Ed25519.Arm.opMul 15 16 15 (VG.Proof.Ed25519.Arm.opSqn 16 15 5 (VG.Proof.Ed25519.Arm.opMul 15 15 16
    (VG.Proof.Ed25519.Arm.opMul 16 14 14 (VG.Proof.Ed25519.Arm.opMul 14 14 15 (VG.Proof.Ed25519.Arm.opMul 15 2 15 (VG.Proof.Ed25519.Arm.opMul 15 15 15 (VG.Proof.Ed25519.Arm.opMul 15 14 14
    (VG.Proof.Ed25519.Arm.opMul 14 2 2 e))))))))))))))))))))

theorem power250_spec (base : BitVec 32) : VG.Proof.Ed25519.Arm.ISpec base power250 VG.Proof.Ed25519.Arm.power250Env := by
  exact
    (VG.Proof.Ed25519.Arm.mulI base 14 2 2).seq <|
    (VG.Proof.Ed25519.Arm.mulI base 15 14 14).seq <|
    (VG.Proof.Ed25519.Arm.mulI base 15 15 15).seq <|
    (VG.Proof.Ed25519.Arm.mulI base 15 2 15).seq <|
    (VG.Proof.Ed25519.Arm.mulI base 14 14 15).seq <|
    (VG.Proof.Ed25519.Arm.mulI base 16 14 14).seq <|
    (VG.Proof.Ed25519.Arm.mulI base 15 15 16).seq <|
    (VG.Proof.Ed25519.Arm.sqnI base 16 15 5 (by decide) (by decide)).seq <|
    (VG.Proof.Ed25519.Arm.mulI base 15 16 15).seq <|
    (VG.Proof.Ed25519.Arm.sqnI base 16 15 10 (by decide) (by decide)).seq <|
    (VG.Proof.Ed25519.Arm.mulI base 16 16 15).seq <|
    (VG.Proof.Ed25519.Arm.sqnI base 17 16 20 (by decide) (by decide)).seq <|
    (VG.Proof.Ed25519.Arm.mulI base 16 17 16).seq <|
    (VG.Proof.Ed25519.Arm.sqnI base 16 16 10 (by decide) (by decide)).seq <|
    (VG.Proof.Ed25519.Arm.mulI base 15 16 15).seq <|
    (VG.Proof.Ed25519.Arm.sqnI base 16 15 50 (by decide) (by decide)).seq <|
    (VG.Proof.Ed25519.Arm.mulI base 16 16 15).seq <|
    (VG.Proof.Ed25519.Arm.sqnI base 17 16 100 (by decide) (by decide)).seq <|
    (VG.Proof.Ed25519.Arm.mulI base 16 17 16).seq <|
    (VG.Proof.Ed25519.Arm.sqnI base 16 16 50 (by decide) (by decide)).seq <|
    (VG.Proof.Ed25519.Arm.mulI base 15 16 15)

def invEnv (e : VG.Proof.Ed25519.Arm.Env) : VG.Proof.Ed25519.Arm.Env := VG.Proof.Ed25519.Arm.opMul 15 15 14 (VG.Proof.Ed25519.Arm.opSqn 15 15 5 (VG.Proof.Ed25519.Arm.power250Env e))
def rootEnv (e : VG.Proof.Ed25519.Arm.Env) : VG.Proof.Ed25519.Arm.Env := VG.Proof.Ed25519.Arm.opMul 15 15 2 (VG.Proof.Ed25519.Arm.opSqn 15 15 2 (VG.Proof.Ed25519.Arm.power250Env e))

theorem invert_spec (base : BitVec 32) : VG.Proof.Ed25519.Arm.ISpec base invert VG.Proof.Ed25519.Arm.invEnv := by
  have h : VG.Proof.Ed25519.Arm.ISpec base _ _ := (VG.Proof.Ed25519.Arm.power250_spec base).seq ((VG.Proof.Ed25519.Arm.sqnI base 15 15 5 (by decide) (by decide)).seq
    (VG.Proof.Ed25519.Arm.mulI base 15 15 14))
  exact h

theorem rootPower_spec (base : BitVec 32) : VG.Proof.Ed25519.Arm.ISpec base Impl.Ed25519.Arm.rootPower VG.Proof.Ed25519.Arm.rootEnv := by
  have h : VG.Proof.Ed25519.Arm.ISpec base _ _ := (VG.Proof.Ed25519.Arm.power250_spec base).seq ((VG.Proof.Ed25519.Arm.sqnI base 15 15 2 (by decide) (by decide)).seq
    (VG.Proof.Ed25519.Arm.mulI base 15 15 2))
  exact h

theorem invEnv_eval (e : VG.Proof.Ed25519.Arm.Env) : VG.Proof.Ed25519.Arm.invEnv e 15 = VG.Proof.X25519.invert (e 2) := by
  simp only [↓reduceIte, VG.Proof.Ed25519.Arm.invEnv, VG.Proof.Ed25519.Arm.power250Env, VG.Proof.Ed25519.Arm.opMul, VG.Proof.Ed25519.Arm.opSqn, Function.update_apply]
  rfl

theorem rootEnv_eval (e : VG.Proof.Ed25519.Arm.Env) : VG.Proof.Ed25519.Arm.rootEnv e 15 = VG.Proof.Ed25519.rootPower (e 2) := by
  simp only [↓reduceIte, VG.Proof.Ed25519.Arm.rootEnv, VG.Proof.Ed25519.Arm.power250Env, VG.Proof.Ed25519.Arm.opMul, VG.Proof.Ed25519.Arm.opSqn, Function.update_apply]
  rfl

theorem invert_ok {s : State} {base : BitVec 32} (hs : VG.Proof.Ed25519.Arm.Ctx base s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem base) :
    WP isa invert s fun t => VG.Proof.Ed25519.Arm.IKeep base s t ∧ VG.Proof.Ed25519.Arm.AllLim t.mem base ∧
      VG.Proof.Ed25519.Arm.env t.mem base 15 = VG.Proof.X25519.invert (VG.Proof.Ed25519.Arm.env s.mem base 2) :=
  WP.mono (VG.Proof.Ed25519.Arm.invert_spec base s hs hl) fun _ ⟨hk, hlt, hv⟩ => ⟨hk, hlt, by rw [hv, VG.Proof.Ed25519.Arm.invEnv_eval]⟩

theorem rootPower_ok {s : State} {base : BitVec 32} (hs : VG.Proof.Ed25519.Arm.Ctx base s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem base) :
    WP isa Impl.Ed25519.Arm.rootPower s fun t => VG.Proof.Ed25519.Arm.IKeep base s t ∧ VG.Proof.Ed25519.Arm.AllLim t.mem base ∧
      VG.Proof.Ed25519.Arm.env t.mem base 15 = VG.Proof.Ed25519.rootPower (VG.Proof.Ed25519.Arm.env s.mem base 2) :=
  WP.mono (VG.Proof.Ed25519.Arm.rootPower_spec base s hs hl) fun _ ⟨hk, hlt, hv⟩ => ⟨hk, hlt, by rw [hv, VG.Proof.Ed25519.Arm.rootEnv_eval]⟩

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.PointAffine`. -/
section

/-! Affine conversion using the verified inversion chain. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

theorem IKeep.of_keep {b : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.Arm.Keep b s t) : VG.Proof.Ed25519.Arm.IKeep b s t :=
  ⟨h.rest.mono (by decide), h.frame⟩

theorem affine_eval (e : VG.Proof.Ed25519.Arm.Env) :
    VG.Proof.Ed25519.Arm.evalOps affineOps e 0 = e 0 * e 15 ∧ VG.Proof.Ed25519.Arm.evalOps affineOps e 1 = e 1 * e 15 := ⟨rfl, rfl⟩

theorem invEnv_xy (e : VG.Proof.Ed25519.Arm.Env) : VG.Proof.Ed25519.Arm.invEnv e 0 = e 0 ∧ VG.Proof.Ed25519.Arm.invEnv e 1 = e 1 := by
  simp only [↓reduceIte, VG.Proof.Ed25519.Arm.invEnv, VG.Proof.Ed25519.Arm.power250Env, VG.Proof.Ed25519.Arm.opMul, VG.Proof.Ed25519.Arm.opSqn, Function.update_apply]
  exact ⟨rfl, rfl⟩

theorem pointAffine_ok {s : State} {base : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx base s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem base) :
    WP isa pointAffine s fun t => VG.Proof.Ed25519.Arm.IKeep base s t ∧ VG.Proof.Ed25519.Arm.AllLim t.mem base ∧
      VG.Proof.Ed25519.Arm.env t.mem base 0 = VG.Proof.Ed25519.Arm.env s.mem base 0 * Spec.X25519.pow (VG.Proof.Ed25519.Arm.env s.mem base 2) (Spec.X25519.P - 2) ∧
      VG.Proof.Ed25519.Arm.env t.mem base 1 = VG.Proof.Ed25519.Arm.env s.mem base 1 * Spec.X25519.pow (VG.Proof.Ed25519.Arm.env s.mem base 2) (Spec.X25519.P - 2) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.invert_spec base s hc hl) fun t ⟨hk, hlt, hv⟩ => ?_)
  refine WP.mono (VG.Proof.Ed25519.Arm.fieldCode_ok affineOps (hk.ctx hc) hlt) fun u ⟨ku, hlu, vu⟩ => ?_
  refine ⟨hk.trans (IKeep.of_keep ku), hlu, ?_, ?_⟩
  · rw [vu, (VG.Proof.Ed25519.Arm.affine_eval _).1, hv, (VG.Proof.Ed25519.Arm.invEnv_xy _).1, VG.Proof.Ed25519.Arm.invEnv_eval, Proof.X25519.invert_eq]
  · rw [vu, (VG.Proof.Ed25519.Arm.affine_eval _).2, hv, (VG.Proof.Ed25519.Arm.invEnv_xy _).2, VG.Proof.Ed25519.Arm.invEnv_eval, Proof.X25519.invert_eq]

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.PointPowers`. -/
section

/-! Merged from `Proof.Ed25519.Arm.PointTableAddr`. -/
section
/-! Merged from `Proof.Ed25519.Arm.PointLoop`. -/
section
/-! Fixed batches of exact doublings preserve the saved accumulator. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem doubleBody_ok {s : State} {b : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem b)
    (n : Nat) (hn : n < 16) (hcount : s.gpr .r10 = BitVec.ofNat 32 (n + 1))
    (hd : VG.Proof.Ed25519.Arm.env s.mem b 16 = Spec.Ed25519.d) :
    WP isa doubleBody s fun t => t.gpr .r10 = BitVec.ofNat 32 n ∧ t.z = decide (n = 0) ∧
      VG.Proof.Ed25519.Arm.AllLim t.mem b ∧ VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env t.mem b) 0 1 2 3 =
        Spec.Ed25519.pointAdd (VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env s.mem b) 0 1 2 3) (VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env s.mem b) 0 1 2 3) ∧
      (∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.Arm.env t.mem b i = VG.Proof.Ed25519.Arm.env s.mem b i) ∧ VG.Proof.Ed25519.Arm.IKeep b s t := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.pointDouble_ok hc hl hd) fun t ⟨hk, hlt, hv, hi⟩ => ?_)
  refine WP.mono (VG.Proof.Ed25519.Arm.decR10_ok (by omega) ((hk.rest.gpr _ (by decide)).trans hcount))
    fun u ⟨hu, hz, hr, hm⟩ => ?_
  exact ⟨hu, hz, hm ▸ hlt, by rw [hm]; exact hv, by rw [hm]; exact hi,
    (IKeep.of_keep hk).trans (IKeep.of_counter hr hm)⟩

structure DoubleInv (s₀ : State) (b : BitVec 32) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 16
  ctx : VG.Proof.Ed25519.Arm.Ctx b s
  lim : VG.Proof.Ed25519.Arm.AllLim s.mem b
  counter : s.gpr .r10 = BitVec.ofNat 32 n
  value : VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env s.mem b) 0 1 2 3 = powerPoint (VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env s₀.mem b) 0 1 2 3) (16 - n)
  high : ∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.Arm.env s.mem b i = VG.Proof.Ed25519.Arm.env s₀.mem b i
  keep : VG.Proof.Ed25519.Arm.IKeep b s₀ s

theorem doubleLoop_ok {s₀ : State} {b : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx b s₀) (hl : VG.Proof.Ed25519.Arm.AllLim s₀.mem b)
    (hcount : s₀.gpr .r10 = 16) (hd : VG.Proof.Ed25519.Arm.env s₀.mem b 16 = Spec.Ed25519.d) :
    WP isa (.loop doubleBody .ne) s₀ fun t => VG.Proof.Ed25519.Arm.AllLim t.mem b ∧
      VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env t.mem b) 0 1 2 3 = powerPoint (VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env s₀.mem b) 0 1 2 3) 16 ∧
      (∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.Arm.env t.mem b i = VG.Proof.Ed25519.Arm.env s₀.mem b i) ∧ VG.Proof.Ed25519.Arm.IKeep b s₀ t := by
  apply WP.loop (VG.Proof.Ed25519.Arm.DoubleInv s₀ b) (n := 16)
  · intro n s hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hi.positive; omega : n ≠ 0)
    have hk : k < 16 := by have := hi.bound; omega
    refine WP.mono (VG.Proof.Ed25519.Arm.doubleBody_ok hi.ctx hi.lim k hk hi.counter
      ((hi.high 16 (by decide)).trans hd)) fun t ⟨htc, htz, htl, htv, hthi, htk⟩ => ?_
    have hv : VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env t.mem b) 0 1 2 3 = powerPoint (VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env s₀.mem b) 0 1 2 3) (16 - k) := by
      rw [htv, hi.value, show 16 - k = (16 - (k + 1)) + 1 by omega, powerPoint]
    have hh : ∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.Arm.env t.mem b i = VG.Proof.Ed25519.Arm.env s₀.mem b i :=
      fun i h => (hthi i h).trans (hi.high i h)
    have hkeep := hi.keep.trans htk
    by_cases hk0 : k = 0
    · subst hk0
      exact .inl ⟨by simp only [VG.Arm.eval, htz, decide_true, Bool.not_true], htl, hv, hh, hkeep⟩
    · exact .inr ⟨by simp only [VG.Arm.eval, htz, decide_eq_false hk0, Bool.not_false],
        k, by omega, ⟨by omega, by omega, htk.ctx hi.ctx, htl, htc, hv, hh, hkeep⟩⟩
  · exact ⟨by decide, by decide, hc, hl, hcount, rfl, fun _ _ => rfl,
      ⟨Rest.refl _ _, Frame.refl _ _⟩⟩

theorem double16_ok {s : State} {b : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem b)
    (hd : VG.Proof.Ed25519.Arm.env s.mem b 16 = Spec.Ed25519.d) :
    WP isa double16 s fun t => VG.Proof.Ed25519.Arm.AllLim t.mem b ∧
      VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env t.mem b) 0 1 2 3 = powerPoint (VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env s.mem b) 0 1 2 3) 16 ∧
      (∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.Arm.env t.mem b i = VG.Proof.Ed25519.Arm.env s.mem b i) ∧ VG.Proof.Ed25519.Arm.IKeep b s t := by
  refine WP.seq (wp_movw fun t ht => WP.block_nil ?_)
  have hk : VG.Proof.Ed25519.Arm.IKeep b s t := IKeep.of_counter (ht.rest (by decide)) ht.mem
  refine WP.mono (VG.Proof.Ed25519.Arm.doubleLoop_ok (hk.ctx hc) (by rw [ht.mem]; exact hl)
    ht.gpr (by rw [ht.mem]; exact hd)) fun u ⟨hlu, hv, hh, hu⟩ => ?_
  rw [ht.mem] at hv hh
  exact ⟨hlu, hv, hh, hk.trans hu⟩

end VG.Proof.Ed25519.Arm
end

/-! Public table addresses and bounded counters. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem movw_nat {v : Nat} (hv : v < 65536) : ((BitVec.ofNat 16 v).setWidth 32).toNat = v := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv,
    Nat.mod_eq_of_lt (by omega)]

theorem tableAddr_ok {s : State} {b : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (start j : Nat)
    (ho : start + 128 * j < 8192) (hj : j < 32) (h11 : s.gpr .r11 = BitVec.ofNat 32 j) :
    WP isa (.block (tableAddr start)) s fun t =>
      t.gpr .r12 = b + BitVec.ofNat 32 (start + 128 * j) ∧
      Rest [.r3, .r12] s t ∧ t.mem = s.mem := by
  have hb := hc.fit
  refine wp_movw fun s1 u1 => wp_dp (op2_reg _ _) fun s2 u2 =>
    wp_dp (op2_lsl (by decide)) fun s3 u3 => WP.block_nil ?_
  have e1 : (s1.gpr .r3).toNat = start := by rw [u1.gpr, VG.Proof.Ed25519.Arm.movw_nat (by omega)]
  have e2 : (s2.gpr .r12).toNat = b.toNat + start := by
    rw [u2.gpr]
    change (s1.gpr .r0 + s1.gpr .r3).toNat = _
    rw [u1.other _ (by decide), hc.r0, toNat_add_lt (by rw [e1]; omega), e1]
  have e11 : (s2.gpr .r11 <<< 7).toNat = 128 * j := by
    rw [u2.other _ (by decide), u1.other _ (by decide), h11, toNat_shl, toNat_imm (by omega)]
    omega
  refine ⟨?_, (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide))),
    by rw [u3.mem, u2.mem, u1.mem]⟩
  apply BitVec.eq_of_toNat_eq
  rw [u3.gpr]
  change (s2.gpr .r12 + (s2.gpr .r11 <<< 7)).toNat = _
  rw [toNat_add_lt (by rw [e2, e11]; omega), e2, e11, hc.ptr_nat ho]
  omega

theorem sub_beq_zero_nat {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (BitVec.ofNat 32 x - BitVec.ofNat 32 y == 0) = decide (x = y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add]
  have hz : (0 : BitVec 32) + BitVec.ofNat 32 y = BitVec.ofNat 32 y := BitVec.zero_add _
  rw [hz]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [toNat_imm hx, toNat_imm hy] at this
  · exact congrArg (BitVec.ofNat 32)

theorem powersNext_ok (s : State) (j count : Nat) (hj : j < count) (hn : count ≤ 32)
    (h11 : s.gpr .r11 = BitVec.ofNat 32 j) :
    WP isa (.block (powersNext count)) s fun t =>
      t.gpr .r11 = BitVec.ofNat 32 (j + 1) ∧ t.z = decide (j + 1 = count) ∧
      Rest [.r3, .r11] s t ∧ t.mem = s.mem := by
  refine wp_movw fun s1 u1 => wp_dp (op2_imm (by decide)) fun s2 u2 =>
    wp_cmp (op2_reg _ _) fun s3 u3 hz => WP.block_nil ?_
  have e2 : s2.gpr .r11 = BitVec.ofNat 32 (j + 1) := by
    rw [u2.gpr]
    change s1.gpr .r11 + 1 = _
    rw [u1.other _ (by decide), h11, BitVec.ofNat_add]
    rfl
  have e3 : s2.gpr .r3 = BitVec.ofNat 32 count := by
    rw [u2.other _ (by decide), u1.gpr]
    apply BitVec.eq_of_toNat_eq
    rw [VG.Proof.Ed25519.Arm.movw_nat (by omega), toNat_imm (by omega)]
  exact ⟨by rw [u3.gpr]; exact e2,
    by rw [hz, e2, e3, VG.Proof.Ed25519.Arm.sub_beq_zero_nat (by omega) (by omega)],
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest _)),
    by rw [u3.mem, u2.mem, u1.mem]⟩

end VG.Proof.Ed25519.Arm
end

/-! Constructing bounded tables of exact point doublings. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

abbrev TableFrame (b : BitVec 32) (o n : Nat) (m m' : Mem) : Prop :=
  Frame [VG.Proof.Ed25519.Arm.FA b, ⟨State.addr b + BitVec.ofNat 64 o, n⟩] m m'

theorem TableFrame.mono {b : BitVec 32} {o n o' n' : Nat} {m m' : Mem}
    (h : VG.Proof.Ed25519.Arm.TableFrame b o n m m') (ho : o' ≤ o) (hn : o + n ≤ o' + n') : VG.Proof.Ed25519.Arm.TableFrame b o' n' m m' := by
  refine h.sub fun r hm => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Offset.sub _ ho hn⟩

theorem TableFrame.workspace {b : BitVec 32} {o n : Nat} {m m' : Mem}
    (h : Frame [VG.Proof.Ed25519.Arm.FA b] m m') : VG.Proof.Ed25519.Arm.TableFrame b o n m m' :=
  h.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..

theorem TableFrame.table {b : BitVec 32} {o n : Nat} {m m' : Mem}
    (h : Frame [⟨State.addr b + BitVec.ofNat 64 o, n⟩] m m') : VG.Proof.Ed25519.Arm.TableFrame b o n m m' :=
  h.mono fun _ hr => List.mem_cons_of_mem _ hr

theorem tablePoint_frame {b : BitVec 32} {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    {d : Nat} (hd : ∀ r ∈ rs, (⟨State.addr b + BitVec.ofNat 64 d, 128⟩ : Region).Disjoint r) :
    VG.Proof.Ed25519.Arm.tablePoint m' b d = VG.Proof.Ed25519.Arm.tablePoint m b d := by
  have he : ∀ i, i + 32 ≤ 128 → VG.Proof.Ed25519.Arm.tableF m' b (d + i) = VG.Proof.Ed25519.Arm.tableF m b (d + i) := by
    intro i hi
    refine congrArg VG.Proof.X25519.toFe (VG.Proof.Ed25519.Arm.packedV_frame hf fun r hm => ?_)
    exact (hd r hm).sub_left (Offset.sub _ (by omega) (by omega))
  have h0 := he 0 (by decide)
  simp only [Nat.add_zero] at h0
  simp only [VG.Proof.Ed25519.Arm.tablePoint, h0, he 32 (by decide), he 64 (by decide), he 96 (by decide)]

theorem TableFrame.point {b : BitVec 32} {o n : Nat} {m m' : Mem}
    (h : VG.Proof.Ed25519.Arm.TableFrame b o n m m') {d : Nat} (hd : 1600 ≤ d)
    (hsep : d + 128 ≤ o ∨ o + n ≤ d) (hb : d + 128 ≤ 8192) (hn : o + n ≤ 8192) :
    VG.Proof.Ed25519.Arm.tablePoint m' b d = VG.Proof.Ed25519.Arm.tablePoint m b d := by
  refine VG.Proof.Ed25519.Arm.tablePoint_frame h fun r hm => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by decide)
  · exact Offset.disjoint _ hsep (by omega) (by omega)

theorem workspace_tablePoint {b : BitVec 32} {m m' : Mem} (h : Frame [VG.Proof.Ed25519.Arm.FA b] m m')
    {d : Nat} (hd : 1600 ≤ d) (hb : d + 128 ≤ 8192) : VG.Proof.Ed25519.Arm.tablePoint m' b d = VG.Proof.Ed25519.Arm.tablePoint m b d := by
  refine VG.Proof.Ed25519.Arm.tablePoint_frame h fun r hm => ?_
  rw [List.mem_singleton.mp hm]
  exact Offset.disjoint _ (.inr (by omega)) (by omega) (by decide)

abbrev powersClob : List Reg := [.r10, .r11, .r12] ++ clob

structure PowersKeep (b : BitVec 32) (o n : Nat) (s t : State) : Prop where
  rest : Rest VG.Proof.Ed25519.Arm.powersClob s t
  frame : VG.Proof.Ed25519.Arm.TableFrame b o n s.mem t.mem

theorem PowersKeep.refl (b : BitVec 32) (o n : Nat) (s : State) : VG.Proof.Ed25519.Arm.PowersKeep b o n s s :=
  ⟨Rest.refl _ _, Frame.refl _ _⟩

theorem PowersKeep.ctx {b : BitVec 32} {o n : Nat} {s t : State}
    (h : VG.Proof.Ed25519.Arm.PowersKeep b o n s t) (hc : VG.Proof.Ed25519.Arm.Ctx b s) : VG.Proof.Ed25519.Arm.Ctx b t := hc.of_rest h.rest (by decide)

theorem PowersKeep.trans {b : BitVec 32} {o n : Nat} {s t u : State}
    (h : VG.Proof.Ed25519.Arm.PowersKeep b o n s t) (k : VG.Proof.Ed25519.Arm.PowersKeep b o n t u) : VG.Proof.Ed25519.Arm.PowersKeep b o n s u :=
  ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

theorem PowersKeep.mono {b : BitVec 32} {o n o' n' : Nat} {s t : State}
    (h : VG.Proof.Ed25519.Arm.PowersKeep b o n s t) (ho : o' ≤ o) (hn : o + n ≤ o' + n') : VG.Proof.Ed25519.Arm.PowersKeep b o' n' s t :=
  ⟨h.rest, TableFrame.mono h.frame ho hn⟩

theorem powerBatch_ok {s : State} {b : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem b)
    (hd : VG.Proof.Ed25519.Arm.env s.mem b 16 = Spec.Ed25519.d) (batch : Bool) :
    WP isa (powerBatch batch) s fun t => VG.Proof.Ed25519.Arm.AllLim t.mem b ∧
      VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env t.mem b) 0 1 2 3 = powerPoint (VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env s.mem b) 0 1 2 3) (powerStride batch) ∧
      (∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.Arm.env t.mem b i = VG.Proof.Ed25519.Arm.env s.mem b i) ∧ VG.Proof.Ed25519.Arm.IKeep b s t := by
  cases batch with
  | true => exact VG.Proof.Ed25519.Arm.double16_ok hc hl hd
  | false =>
    refine WP.mono (VG.Proof.Ed25519.Arm.pointDouble_ok hc hl hd) fun t ⟨hk, hlt, hv, hh⟩ => ?_
    exact ⟨hlt, hv, hh, IKeep.of_keep hk⟩

theorem powersBody_ok (batch : Bool) {s : State} {b : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx b s)
    (hl : VG.Proof.Ed25519.Arm.AllLim s.mem b) (o j count : Nat) (hlo : 1600 ≤ o) (hbound : o + 128 * count ≤ 8192)
    (hj : j < count) (hn : count ≤ 32) (h11 : s.gpr .r11 = BitVec.ofNat 32 j)
    (hd : VG.Proof.Ed25519.Arm.env s.mem b 16 = Spec.Ed25519.d) :
    WP isa (powersBody o count batch) s fun t => t.gpr .r11 = BitVec.ofNat 32 (j + 1) ∧
      t.z = decide (j + 1 = count) ∧ VG.Proof.Ed25519.Arm.AllLim t.mem b ∧
      VG.Proof.Ed25519.Arm.tablePoint t.mem b (o + 128 * j) = VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env s.mem b) 0 1 2 3 ∧
      VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env t.mem b) 0 1 2 3 = powerPoint (VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env s.mem b) 0 1 2 3) (powerStride batch) ∧
      (∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.Arm.env t.mem b i = VG.Proof.Ed25519.Arm.env s.mem b i) ∧
      VG.Proof.Ed25519.Arm.PowersKeep b (o + 128 * j) 128 s t := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.Arm.tableAddr_ok hc o j (by omega) (by omega) h11) fun t ⟨htp, htr, htm⟩ => ?_
  have hct := hc.of_rest htr (by decide)
  refine WP.mono (VG.Proof.Ed25519.Arm.pointToTable_ok hct (by rw [htm]; exact hl) htp (by omega) (by omega))
    fun u ⟨hut, huk⟩ => ?_
  have heu : VG.Proof.Ed25519.Arm.env u.mem b = VG.Proof.Ed25519.Arm.env s.mem b := (huk.env (by omega) (by omega)).trans
    (congrArg (fun m => VG.Proof.Ed25519.Arm.env m b) htm)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.powerBatch_ok (huk.ctx hct)
    (huk.lim (by omega) (by omega) (by rw [htm]; exact hl)) (by rw [heu]; exact hd) batch)
    fun v ⟨hvl, hvp, hvhi, hvk⟩ => ?_)
  have hvc : v.gpr .r11 = BitVec.ofNat 32 j := by
    rw [hvk.rest.gpr _ (by decide), huk.rest.gpr _ (by decide), htr.gpr _ (by decide), h11]
  refine WP.mono (VG.Proof.Ed25519.Arm.powersNext_ok v j count hj hn hvc) fun w ⟨hwc, hwz, hwr, hwm⟩ => ?_
  refine ⟨hwc, hwz, by rw [hwm]; exact hvl, ?_, ?_, ?_, ?_⟩
  · rw [hwm, VG.Proof.Ed25519.Arm.workspace_tablePoint hvk.frame (by omega) (by omega), hut, htm]
  · rw [hwm, hvp, heu]
  · intro i hi
    rw [hwm, hvhi i hi, heu]
  · refine ⟨(htr.mono (by decide)).trans ((huk.rest.mono (by decide)).trans
      ((hvk.rest.mono (by decide)).trans (hwr.mono (by decide)))), ?_⟩
    rw [hwm, ← htm]
    exact (TableFrame.table huk.frame).trans (TableFrame.workspace hvk.frame)

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.AccumulateStep`. -/
section

/-! Merged from `Proof.Ed25519.Arm.PointAccumulate`. -/
section
/-! Merged from `Proof.Ed25519.Arm.AccKeep`. -/
section
/-! Point accumulation changes the field workspace and its table pointer. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

abbrev accClob : List Reg := .r12 :: clob
structure AccKeep (b : BitVec 32) (s t : State) : Prop where
  rest : Rest VG.Proof.Ed25519.Arm.accClob s t
  frame : Frame [VG.Proof.Ed25519.Arm.FA b] s.mem t.mem

theorem AccKeep.ctx {b : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.Arm.AccKeep b s t) (hc : VG.Proof.Ed25519.Arm.Ctx b s) : VG.Proof.Ed25519.Arm.Ctx b t :=
  hc.of_rest h.rest (by decide)

theorem AccKeep.trans {b : BitVec 32} {s t u : State} (h : VG.Proof.Ed25519.Arm.AccKeep b s t) (k : VG.Proof.Ed25519.Arm.AccKeep b t u) :
    VG.Proof.Ed25519.Arm.AccKeep b s u := ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

theorem AccKeep.of_keep {b : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.Arm.Keep b s t) : VG.Proof.Ed25519.Arm.AccKeep b s t :=
  ⟨h.rest.mono (by decide), h.frame⟩

theorem AccKeep.of_rest {b : BitVec 32} {s t : State} {ws : List Reg} (hr : Rest ws s t)
    (hws : ∀ r ∈ ws, r ∈ VG.Proof.Ed25519.Arm.accClob) (hm : t.mem = s.mem) : VG.Proof.Ed25519.Arm.AccKeep b s t :=
  ⟨hr.mono hws, by rw [hm]; exact Frame.refl _ _⟩

theorem AccKeep.of_table {b : BitVec 32} {s t : State} {o n : Nat} (h : VG.Proof.Ed25519.Arm.TableKeep b o n s t)
    (ho : 64 ≤ o) (hn : o + n ≤ 1600) : VG.Proof.Ed25519.Arm.AccKeep b s t :=
  ⟨h.rest.mono (by decide), h.frame.sub fun r hm => ⟨_, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hm]; exact Offset.sub _ ho hn⟩⟩

theorem TableKeep.high {b : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.Arm.TableKeep b 64 256 s t)
    (i : Slot) (hi : 4 ≤ i.val) :
    VG.Proof.Ed25519.Arm.env t.mem b i = VG.Proof.Ed25519.Arm.env s.mem b i :=
  congrArg VG.Proof.X25519.toFe (val16_congr (h.slot (by decide) i
    (.inr (by simp only [offset]; omega))))

theorem point_congr {e f : VG.Proof.Ed25519.Arm.Env} (x y z t : Slot) (hx : e x = f x) (hy : e y = f y)
    (hz : e z = f z) (ht : e t = f t) : VG.Proof.Ed25519.Arm.point e x y z t = VG.Proof.Ed25519.Arm.point f x y z t := by
  simp only [VG.Proof.Ed25519.Arm.point, hx, hy, hz, ht]

theorem savePoint_d (e : VG.Proof.Ed25519.Arm.Env) : VG.Proof.Ed25519.Arm.evalOps savePointOps e 16 = e 16 := rfl
theorem copyPointToQ_d (e : VG.Proof.Ed25519.Arm.Env) : VG.Proof.Ed25519.Arm.evalOps copyPointToQOps e 16 = e 16 := rfl
theorem restorePoint_d (e : VG.Proof.Ed25519.Arm.Env) : VG.Proof.Ed25519.Arm.evalOps restorePointOps e 16 = e 16 := rfl
theorem copyPointToQ_saved (e : VG.Proof.Ed25519.Arm.Env) :
    VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.evalOps copyPointToQOps e) 17 18 19 20 = VG.Proof.Ed25519.Arm.point e 17 18 19 20 := rfl
theorem restorePoint_saved (e : VG.Proof.Ed25519.Arm.Env) :
    VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.evalOps restorePointOps e) 17 18 19 20 = VG.Proof.Ed25519.Arm.point e 17 18 19 20 := rfl
theorem restorePoint_q (e : VG.Proof.Ed25519.Arm.Env) : VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.evalOps restorePointOps e) 4 5 6 7 = VG.Proof.Ed25519.Arm.point e 4 5 6 7 := rfl

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.PrepareAdd`. -/
section
/-! Save the accumulator and load the next exact power into Q. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem prepareAdd_ok {s : State} {b : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem b)
    (j : Nat) (hj : j < 16) (h11 : s.gpr .r11 = BitVec.ofNat 32 j) :
    WP isa prepareAdd s fun t => VG.Proof.Ed25519.Arm.AccKeep b s t ∧ VG.Proof.Ed25519.Arm.AllLim t.mem b ∧
      VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env t.mem b) 0 1 2 3 = VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env s.mem b) 0 1 2 3 ∧
      VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env t.mem b) 4 5 6 7 = VG.Proof.Ed25519.Arm.tablePoint s.mem b (5696 + 128 * j) ∧
      VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env t.mem b) 17 18 19 20 = VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env s.mem b) 0 1 2 3 ∧
      VG.Proof.Ed25519.Arm.env t.mem b 16 = VG.Proof.Ed25519.Arm.env s.mem b 16 := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.fieldCode_ok savePointOps hc hl) fun a ⟨ka, la, ea⟩ => ?_)
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.Arm.tableAddr_ok (ka.ctx hc) 5696 j (by omega) (by omega)
    ((ka.rest.gpr _ (by decide)).trans h11)) fun a' ⟨hptr, hr, hm⟩ => ?_
  have ka' : VG.Proof.Ed25519.Arm.AccKeep b a a' := AccKeep.of_rest hr (by decide) hm
  refine WP.mono (VG.Proof.Ed25519.Arm.pointFromTable_ok (ka'.ctx (ka.ctx hc)) (by rw [hm]; exact la)
    hptr (by omega) (by omega)) fun c ⟨pc, lc, kc⟩ => ?_
  have kc' : VG.Proof.Ed25519.Arm.AccKeep b a' c := AccKeep.of_table kc (by decide) (by decide)
  have ks : VG.Proof.Ed25519.Arm.AccKeep b s c := (AccKeep.of_keep ka).trans (ka'.trans kc')
  have savec : VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env c.mem b) 17 18 19 20 = VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env s.mem b) 0 1 2 3 := by
    rw [VG.Proof.Ed25519.Arm.point_congr _ _ _ _ (kc.high 17 (by decide)) (kc.high 18 (by decide))
      (kc.high 19 (by decide)) (kc.high 20 (by decide)), hm, ea, VG.Proof.Ed25519.Arm.savePoint_eval]
  have dc : VG.Proof.Ed25519.Arm.env c.mem b 16 = VG.Proof.Ed25519.Arm.env s.mem b 16 := by rw [kc.high 16 (by decide), hm, ea, VG.Proof.Ed25519.Arm.savePoint_d]
  have tc : VG.Proof.Ed25519.Arm.tablePoint a'.mem b (5696 + 128 * j) = VG.Proof.Ed25519.Arm.tablePoint s.mem b (5696 + 128 * j) := by
    rw [hm]
    exact VG.Proof.Ed25519.Arm.workspace_tablePoint ka.frame (by omega) (by omega)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.fieldCode_ok copyPointToQOps (ks.ctx hc) lc) fun d ⟨kd, ld, ed⟩ => ?_)
  refine WP.mono (VG.Proof.Ed25519.Arm.fieldCode_ok restorePointOps (kd.ctx (ks.ctx hc)) ld) fun t ⟨kt, lt, et⟩ => ?_
  refine ⟨ks.trans ((AccKeep.of_keep kd).trans (AccKeep.of_keep kt)), lt, ?_, ?_, ?_, ?_⟩
  · rw [et, VG.Proof.Ed25519.Arm.restorePoint_eval, ed, VG.Proof.Ed25519.Arm.copyPointToQ_saved, savec]
  · rw [et, VG.Proof.Ed25519.Arm.restorePoint_q, ed, VG.Proof.Ed25519.Arm.copyPointToQ_eval, pc, tc]
  · rw [et, VG.Proof.Ed25519.Arm.restorePoint_saved, ed, VG.Proof.Ed25519.Arm.copyPointToQ_saved, savec]
  · rw [et, VG.Proof.Ed25519.Arm.restorePoint_d, ed, VG.Proof.Ed25519.Arm.copyPointToQ_d, dc]

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.BitMask`. -/
section
/-! Scalar bits in the sixteen-byte batch buffer. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem AccKeep.bit {b : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.Arm.AccKeep b s t) (j : Nat) (hj : j < 16) :
    t.mem (State.addr b + BitVec.ofNat 64 (32 + j)) = s.mem (State.addr b + BitVec.ofNat 64 (32 + j)) := by
  refine h.frame _ fun r hr => ?_
  rw [List.mem_singleton.mp hr]
  exact (Offset.disjoint (State.addr b) (d := 32 + j) (n := 1) (e := 64) (k := 1536)
    (.inl (by omega)) (by omega) (by decide)) _ (Region.contains_self _ _)


theorem scalarBitMask_ok {b : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (j : Nat) (hj : j < 16)
    (h11 : s.gpr .r11 = BitVec.ofNat 32 j) (bit : Bool)
    (hbit : s.mem (State.addr b + BitVec.ofNat 64 (32 + j)) = BitVec.ofNat 8 bit.toNat) :
    WP isa (.block scalarBitMask) s fun t => VG.Proof.Ed25519.Arm.AccKeep b s t ∧ t.mem = s.mem ∧
      t.gpr .r9 = 0 - BitVec.ofNat 32 (!bit).toNat := by
  refine wp_dp (op2_reg _ _) fun s1 u1 => ?_
  have ep : s1.gpr .r2 = b + BitVec.ofNat 32 j := by
    rw [u1.gpr]
    change s.gpr .r0 + s.gpr .r11 = _
    rw [hc.r0, h11]
  refine wp_ldrb (a := State.addr b + BitVec.ofNat 64 (32 + j)) (by decide)
    (by rw [ep, Offset.add_add, addr_add (by have := hc.fit; omega)]; rw [Nat.add_comm j 32])
    (by rw [u1.rd, u1.wr]; exact hc.inR (by omega)) fun s2 u2 =>
    wp_dp (op2_imm (by decide)) fun s3 u3 => WP.block_nil ?_
  have hr : Rest [.r2, .r9] s s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  have hm : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  refine ⟨AccKeep.of_rest hr (by decide) hm, hm, ?_⟩
  rw [u3.gpr]
  change s2.gpr .r9 - 1 = _
  rw [u2.gpr, u1.mem, hbit]
  cases bit <;> decide

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.PointSelect`. -/
section
/-! Branch-free selection using the verified limb swaps. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def swapSlot (a b : Slot) (sw : Bool) (i : Slot) : Slot :=
  if sw then if i = a then b else if i = b then a else i else i

def swapEnv (a b : Slot) (sw : Bool) (e : VG.Proof.Ed25519.Arm.Env) : VG.Proof.Ed25519.Arm.Env := fun i => e (VG.Proof.Ed25519.Arm.swapSlot a b sw i)
def swapEnvs (ops : List (Slot × Slot)) (sw : Bool) (e : VG.Proof.Ed25519.Arm.Env) : VG.Proof.Ed25519.Arm.Env :=
  ops.foldl (fun e (a, b) => VG.Proof.Ed25519.Arm.swapEnv a b sw e) e

theorem swapEnvs_step (ops : List (Slot × Slot)) (a b : Slot) (sw : Bool) {e f g : VG.Proof.Ed25519.Arm.Env}
    (hf : f = VG.Proof.Ed25519.Arm.swapEnv a b sw e) (hg : g = VG.Proof.Ed25519.Arm.swapEnvs ops sw f) :
    g = VG.Proof.Ed25519.Arm.swapEnvs ((a, b) :: ops) sw e := hg.trans (congrArg (VG.Proof.Ed25519.Arm.swapEnvs ops sw) hf)

theorem swapField_ok {s : State} {base : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx base s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem base)
    (a b : Slot) (hab : a ≠ b) {sw : Bool} (hm : s.gpr .r9 = 0 - BitVec.ofNat 32 sw.toNat) :
    WP isa (.block (cswap (offset a) (offset b))) s fun t => VG.Proof.Ed25519.Arm.Keep base s t ∧ VG.Proof.Ed25519.Arm.AllLim t.mem base ∧
      t.gpr .r9 = s.gpr .r9 ∧ VG.Proof.Ed25519.Arm.env t.mem base = VG.Proof.Ed25519.Arm.swapEnv a b sw (VG.Proof.Ed25519.Arm.env s.mem base) := by
  have ha := VG.Proof.Ed25519.Arm.slot_range a
  have hb := VG.Proof.Ed25519.Arm.slot_range b
  rw [VG.Proof.Ed25519.Arm.ACC_eq] at ha hb
  have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  refine WP.mono (cswap_ok (by omega) (by omega) (by simp only [offset]; omega) hc
    (show sw.toNat ≤ 1 by cases sw <;> decide) hm) fun t ht => ?_
  have he : ∀ (i : Slot) k, k < 16 → limb t.mem (State.addr base) (offset i) k =
      limb s.mem (State.addr base) (offset (VG.Proof.Ed25519.Arm.swapSlot a b sw i)) k := by
    intro i k hk
    by_cases hia : i = a
    · subst i
      cases sw <;> simpa only [VG.Proof.Ed25519.Arm.swapSlot, Bool.false_eq_true, ite_false, ite_true, sel, Bool.toNat_false, Bool.toNat_true, Nat.zero_ne_one] using ht.lx k hk
    by_cases hib : i = b
    · subst i
      cases sw <;> simpa only [VG.Proof.Ed25519.Arm.swapSlot, Bool.false_eq_true, ite_false, ite_true, hia, sel, Bool.toNat_false, Bool.toNat_true, Nat.zero_ne_one] using ht.ly k hk
    · have hn1 : i.val ≠ a.val := fun h => hia (Fin.ext h)
      have hn2 : i.val ≠ b.val := fun h => hib (Fin.ext h)
      have hi := VG.Proof.Ed25519.Arm.slot_range i
      rw [VG.Proof.Ed25519.Arm.ACC_eq] at hi
      have ei : VG.Proof.Ed25519.Arm.swapSlot a b sw i = i := by simp only [VG.Proof.Ed25519.Arm.swapSlot, hia, hib, ite_false, ite_self]
      rw [ei]
      refine limb_frame ht.frame (fun r hr j hj => ?_) k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;>
        exact Offset.disjoint _ (by simp only [offset]; omega) (by omega) (by omega)
  refine ⟨⟨ht.rest.mono (by decide), ?_⟩,
    fun i k hk => by rw [he i k hk]; exact hl _ k hk,
    ht.rest.gpr _ (by decide), funext fun i => congrArg VG.Proof.X25519.toFe (val16_congr (he i))⟩
  refine ht.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Offset.sub _ (by omega) (by omega)

theorem swapFields_ok {s : State} {base : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx base s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem base)
    (ops : List (Slot × Slot)) (hops : ∀ ab ∈ ops, ab.1 ≠ ab.2) {sw : Bool}
    (hm : s.gpr .r9 = 0 - BitVec.ofNat 32 sw.toNat) :
    WP isa (.block (swapFields ops)) s fun t => VG.Proof.Ed25519.Arm.Keep base s t ∧ VG.Proof.Ed25519.Arm.AllLim t.mem base ∧
      t.gpr .r9 = s.gpr .r9 ∧ VG.Proof.Ed25519.Arm.env t.mem base = VG.Proof.Ed25519.Arm.swapEnvs ops sw (VG.Proof.Ed25519.Arm.env s.mem base) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, hl, rfl, rfl⟩
  | cons ab ops ih =>
    rcases ab with ⟨a, b⟩
    rw [swapFields, List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed25519.Arm.swapField_ok hc hl a b (hops (a, b) (by simp)) hm) fun t ⟨hk, hlt, ht9, hv⟩ => ?_
    refine WP.mono (ih (hk.ctx hc) hlt (fun p hp => hops p (List.mem_cons_of_mem _ hp)) (ht9.trans hm))
      fun u ⟨ku, hlu, hu9, vu⟩ => ?_
    refine ⟨hk.trans ku, hlu, hu9.trans ht9, ?_⟩
    exact VG.Proof.Ed25519.Arm.swapEnvs_step ops a b sw (e := VG.Proof.Ed25519.Arm.env s.mem base) (f := VG.Proof.Ed25519.Arm.env t.mem base) (g := VG.Proof.Ed25519.Arm.env u.mem base) hv vu

theorem pointSelect_eval (e : VG.Proof.Ed25519.Arm.Env) (sw : Bool) :
    VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.swapEnvs pointSelectPairs sw e) 0 1 2 3 =
      if sw then VG.Proof.Ed25519.Arm.point e 17 18 19 20 else VG.Proof.Ed25519.Arm.point e 0 1 2 3 := by cases sw <;> rfl

theorem pointSelect_d (e : VG.Proof.Ed25519.Arm.Env) (sw : Bool) : VG.Proof.Ed25519.Arm.swapEnvs pointSelectPairs sw e 16 = e 16 := by
  cases sw <;> rfl

theorem pointSelect_ok {s : State} {base : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx base s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem base)
    {sw : Bool} (hm : s.gpr .r9 = 0 - BitVec.ofNat 32 sw.toNat) :
    WP isa (.block pointSelect) s fun t => VG.Proof.Ed25519.Arm.Keep base s t ∧ VG.Proof.Ed25519.Arm.AllLim t.mem base ∧
      VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env t.mem base) 0 1 2 3 =
        (if sw then VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env s.mem base) 17 18 19 20 else VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env s.mem base) 0 1 2 3) ∧
      VG.Proof.Ed25519.Arm.env t.mem base 16 = VG.Proof.Ed25519.Arm.env s.mem base 16 := by
  refine WP.mono (VG.Proof.Ed25519.Arm.swapFields_ok hc hl pointSelectPairs (by decide) hm) fun t ⟨hk, hlt, _, hv⟩ => ?_
  exact ⟨hk, hlt, by rw [hv, VG.Proof.Ed25519.Arm.pointSelect_eval], by rw [hv, VG.Proof.Ed25519.Arm.pointSelect_d]⟩

end VG.Proof.Ed25519.Arm
end

/-! Add one exact table power and select with its scalar bit. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem select_flip {α : Type} (bit : Bool) {a b c d e : α}
    (hc : c = if !bit then d else e) (hd : d = a) (he : e = b) : c = if bit then b else a := by
  cases bit with
  | false => exact hc.trans hd
  | true => exact hc.trans he

theorem pointAccumulate_ok {s : State} {b : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem b)
    (j : Nat) (hj : j < 16) (h11 : s.gpr .r11 = BitVec.ofNat 32 j)
    (hd : VG.Proof.Ed25519.Arm.env s.mem b 16 = Spec.Ed25519.d) (bit : Bool)
    (hbit : s.mem (State.addr b + BitVec.ofNat 64 (32 + j)) = BitVec.ofNat 8 bit.toNat) :
    WP isa pointAccumulate s fun t => VG.Proof.Ed25519.Arm.AccKeep b s t ∧ VG.Proof.Ed25519.Arm.AllLim t.mem b ∧
      VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env t.mem b) 0 1 2 3 =
        (if bit then Spec.Ed25519.pointAdd (VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env s.mem b) 0 1 2 3)
          (VG.Proof.Ed25519.Arm.tablePoint s.mem b (5696 + 128 * j)) else VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env s.mem b) 0 1 2 3) ∧
      VG.Proof.Ed25519.Arm.env t.mem b 16 = VG.Proof.Ed25519.Arm.env s.mem b 16 := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.prepareAdd_ok hc hl j hj h11) fun u ⟨ku, lu, up, uq, us, ud⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.pointAdd_ok (ku.ctx hc) lu (ud.trans hd)) fun v ⟨kv, lv, vp, vh⟩ => ?_)
  have ks := ku.trans (AccKeep.of_keep kv)
  have hvc : v.gpr .r11 = BitVec.ofNat 32 j := (ks.rest.gpr _ (by decide)).trans h11
  have hvb : v.mem (State.addr b + BitVec.ofNat 64 (32 + j)) = BitVec.ofNat 8 bit.toNat :=
    (ks.bit j hj).trans hbit
  have vs : VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env v.mem b) 17 18 19 20 = VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env s.mem b) 0 1 2 3 :=
    (VG.Proof.Ed25519.Arm.point_congr (e := VG.Proof.Ed25519.Arm.env v.mem b) (f := VG.Proof.Ed25519.Arm.env u.mem b) 17 18 19 20 (vh 17 (by decide)) (vh 18 (by decide))
      (vh 19 (by decide)) (vh 20 (by decide))).trans us
  have vp' : VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env v.mem b) 0 1 2 3 =
      Spec.Ed25519.pointAdd (VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env s.mem b) 0 1 2 3) (VG.Proof.Ed25519.Arm.tablePoint s.mem b (5696 + 128 * j)) :=
    vp.trans (congrArg₂ Spec.Ed25519.pointAdd up uq)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.Arm.scalarBitMask_ok (ks.ctx hc) j hj hvc bit hvb) fun w ⟨kw, mw, mask⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.Arm.pointSelect_ok (kw.ctx (ks.ctx hc)) (by rw [mw]; exact lv) mask)
    fun t ⟨kt, lt, tp, td⟩ => ?_
  refine ⟨ks.trans (kw.trans (AccKeep.of_keep kt)), lt, ?_, ?_⟩
  · exact VG.Proof.Ed25519.Arm.select_flip bit tp
      ((congrArg (fun m => VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env m b) 17 18 19 20) mw).trans vs)
      ((congrArg (fun m => VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env m b) 0 1 2 3) mw).trans vp')
  · exact td.trans ((congrArg (fun m => VG.Proof.Ed25519.Arm.env m b 16) mw).trans ((vh 16 (by decide)).trans ud))

end VG.Proof.Ed25519.Arm
end

/-! One descending scalar bit implements the specification's recursion. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def scalarBit (s n : Nat) : Bool := decide ((s / 2 ^ n) % 2 ≠ 0)

theorem scalarBit_nat (s n : Nat) : (VG.Proof.Ed25519.Arm.scalarBit s n).toNat = (s / 2 ^ n) % 2 := by
  rcases Nat.mod_two_eq_zero_or_one (s / 2 ^ n) with h | h <;> simp only [VG.Proof.Ed25519.Arm.scalarBit, h] <;> decide

theorem choose_after (s n : Nat) (p x y : Spec.Ed25519.Point)
    (hx : x = after s p (n + 1)) (hy : y = powerPoint p n) :
    (if VG.Proof.Ed25519.Arm.scalarBit s n then Spec.Ed25519.pointAdd x y else x) = after s p n := by
  rw [hx, hy]
  have h := (after_step s p n).symm
  by_cases hz : (s / 2 ^ n) % 2 = 0
  · simpa only [VG.Proof.Ed25519.Arm.scalarBit, hz, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
      ite_false, ite_true] using h
  · simpa only [VG.Proof.Ed25519.Arm.scalarBit, hz, ne_eq, not_false_eq_true, decide_true, ite_true, ite_false] using h

abbrev loopClob : List Reg := .r11 :: VG.Proof.Ed25519.Arm.accClob
structure LoopKeep (b : BitVec 32) (s t : State) : Prop where
  rest : Rest VG.Proof.Ed25519.Arm.loopClob s t
  frame : Frame [VG.Proof.Ed25519.Arm.FA b] s.mem t.mem

theorem LoopKeep.refl (b : BitVec 32) (s : State) : VG.Proof.Ed25519.Arm.LoopKeep b s s := ⟨Rest.refl _ _, Frame.refl _ _⟩
theorem LoopKeep.ctx {b : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.Arm.LoopKeep b s t) (hc : VG.Proof.Ed25519.Arm.Ctx b s) : VG.Proof.Ed25519.Arm.Ctx b t :=
  hc.of_rest h.rest (by decide)
theorem LoopKeep.trans {b : BitVec 32} {s t u : State} (h : VG.Proof.Ed25519.Arm.LoopKeep b s t) (k : VG.Proof.Ed25519.Arm.LoopKeep b t u) :
    VG.Proof.Ed25519.Arm.LoopKeep b s u := ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩
theorem LoopKeep.of_acc {b : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.Arm.AccKeep b s t) : VG.Proof.Ed25519.Arm.LoopKeep b s t :=
  ⟨h.rest.mono (by decide), h.frame⟩
theorem LoopKeep.of_rest {b : BitVec 32} {s t : State} {ws : List Reg} (hr : Rest ws s t)
    (hw : ∀ r ∈ ws, r ∈ VG.Proof.Ed25519.Arm.loopClob) (hm : t.mem = s.mem) : VG.Proof.Ed25519.Arm.LoopKeep b s t :=
  ⟨hr.mono hw, by rw [hm]; exact Frame.refl _ _⟩

theorem LoopKeep.bit {b : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.Arm.LoopKeep b s t) (j : Nat) (hj : j < 16) :
    t.mem (State.addr b + BitVec.ofNat 64 (32 + j)) = s.mem (State.addr b + BitVec.ofNat 64 (32 + j)) := by
  refine h.frame _ fun r hr => ?_
  rw [List.mem_singleton.mp hr]
  exact (Offset.disjoint (State.addr b) (d := 32 + j) (n := 1) (e := 64) (k := 1536)
    (.inl (by omega)) (by omega) (by decide)) _ (Region.contains_self _ _)

theorem accumulateDec_ok (s : State) (n : Nat) (h11 : s.gpr .r11 = BitVec.ofNat 32 (n + 1)) :
    WP isa (.block [.dp .sub .r11 .r11 (.imm 1)]) s fun t =>
      t.gpr .r11 = BitVec.ofNat 32 n ∧ Rest [.r11] s t ∧ t.mem = s.mem := by
  refine wp_dp (op2_imm (by decide)) fun t ht => WP.block_nil ⟨?_, ht.rest (by decide), ht.mem⟩
  rw [ht.gpr]
  change s.gpr .r11 - 1 = _
  rw [h11, BitVec.ofNat_add]
  exact BitVec.add_sub_cancel _ _

theorem accumulateTest_ok (s : State) (n : Nat) (hn : n < 16) (h11 : s.gpr .r11 = BitVec.ofNat 32 n) :
    WP isa (.block [.cmp .r11 (.imm 0)]) s fun t => t.z = decide (n = 0) ∧
      Rest [] s t ∧ t.mem = s.mem := by
  refine wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ⟨?_, ht.rest _, ht.mem⟩
  have he : BitVec.ofNat 32 n - (0 : BitVec 32) = BitVec.ofNat 32 n := BitVec.sub_zero _
  rw [hz, h11, he, ofNat_beq_zero (by omega)]

theorem accumulateBody_ok {s : State} {b : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem b)
    (n start scalar : Nat) (p : Spec.Ed25519.Point) (hn : n < 16)
    (h11 : s.gpr .r11 = BitVec.ofNat 32 (n + 1))
    (hb : s.mem (State.addr b + BitVec.ofNat 64 (32 + n)) = BitVec.ofNat 8 (VG.Proof.Ed25519.Arm.scalarBit scalar (start + n)).toNat)
    (hd : VG.Proof.Ed25519.Arm.env s.mem b 16 = Spec.Ed25519.d)
    (hp : VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env s.mem b) 0 1 2 3 = after scalar p (start + n + 1))
    (ht : VG.Proof.Ed25519.Arm.tablePoint s.mem b (5696 + 128 * n) = powerPoint p (start + n)) :
    WP isa accumulateBody s fun t => t.gpr .r11 = BitVec.ofNat 32 n ∧ t.z = decide (n = 0) ∧
      VG.Proof.Ed25519.Arm.AllLim t.mem b ∧ VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env t.mem b) 0 1 2 3 = after scalar p (start + n) ∧
      VG.Proof.Ed25519.Arm.env t.mem b 16 = Spec.Ed25519.d ∧ VG.Proof.Ed25519.Arm.LoopKeep b s t := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.accumulateDec_ok s n h11) fun u ⟨uc, ur, um⟩ => ?_)
  have uk : VG.Proof.Ed25519.Arm.LoopKeep b s u := LoopKeep.of_rest ur (by decide) um
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.pointAccumulate_ok (uk.ctx hc) (by rw [um]; exact hl) n hn uc
    (by rw [um]; exact hd) (VG.Proof.Ed25519.Arm.scalarBit scalar (start + n)) (by rw [um]; exact hb))
    fun v ⟨vk, vl, vp, vd⟩ => ?_)
  have vc := (vk.rest.gpr .r11 (by decide)).trans uc
  have vpoint : VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env v.mem b) 0 1 2 3 = after scalar p (start + n) :=
    vp.trans (VG.Proof.Ed25519.Arm.choose_after scalar (start + n) p _ _
      ((congrArg (fun m => VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env m b) 0 1 2 3) um).trans hp)
      ((congrArg (fun m => VG.Proof.Ed25519.Arm.tablePoint m b (5696 + 128 * n)) um).trans ht))
  refine WP.mono (VG.Proof.Ed25519.Arm.accumulateTest_ok v n hn vc) fun t ⟨tz, tr, tm⟩ => ?_
  exact ⟨(tr.gpr _ (by decide)).trans vc, tz, tm ▸ vl,
    (congrArg (fun m => VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env m b) 0 1 2 3) tm).trans vpoint,
    (congrArg (fun m => VG.Proof.Ed25519.Arm.env m b 16) tm).trans (vd.trans ((congrArg (fun m => VG.Proof.Ed25519.Arm.env m b 16) um).trans hd)),
    uk.trans ((LoopKeep.of_acc vk).trans (LoopKeep.of_rest tr (by decide) tm))⟩

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.BatchBits`. -/
section

/-! Merged from `Proof.Ed25519.Arm.BatchDigit`. -/
section
/-! Read the public-indexed sixteen-bit scalar digit. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem batchDigit_ok {b p : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s)
    (n j : Nat) (hj : j < n) (_hn : n ≤ 32) (hfit : p.toNat + 2 * n ≤ 2 ^ 32)
    (hp : s.mem.readW (State.addr b + BitVec.ofNat 64 52) 32 = p)
    (hcj : s.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 j)
    (hr : ∀ i < 2 * n, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1) :
    WP isa (.block batchDigit) s fun t => Rest [.r2, .r3, .r12] s t ∧ t.mem = s.mem ∧
      (t.gpr .r3).toNat = VG.Proof.Ed25519.Arm.packedLimb s.mem (State.addr p) j := by
  unfold batchDigit unpackSrc
  simp only [List.cons_append, List.nil_append, Nat.mul_zero, Nat.add_zero]
  refine ldr0_ok hc (by decide) fun s1 u1 =>
    ldr0_ok (hc.of_rest (u1.rest (ws := [.r12]) (by decide)) (by decide)) (by decide) fun s2 u2 =>
    wp_dp (op2_lsl (by decide)) fun s3 u3 => ?_
  have ej : s2.gpr .r2 = BitVec.ofNat 32 j := by rw [u2.gpr, u1.mem]; exact hcj
  have ep : s3.gpr .r12 = p + BitVec.ofNat 32 (2 * j) := by
    rw [u3.gpr]
    change s2.gpr .r12 + (s2.gpr .r2 <<< 1) = _
    rw [u2.other _ (by decide), u1.gpr, hp, ej]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [toNat_shl, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  have r3 : Rest [.r2, .r3, .r12] s s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  have m3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  refine wp_ldrb (a := State.addr p + BitVec.ofNat 64 (2 * j)) (by decide)
    (by
      rw [ep]
      exact (congrArg State.addr (BitVec.add_zero (p + BitVec.ofNat 32 (2 * j)))).trans
        (addr_add (by omega)))
    (by rw [r3.rd, r3.wr]; exact hr _ (by omega)) fun s4 u4 => ?_
  refine wp_ldrb (a := State.addr p + BitVec.ofNat 64 (2 * j + 1)) (by decide)
    (by rw [u4.other _ (by decide), ep, Offset.add_add, addr_add (by omega)])
    (by rw [u4.rd, u4.wr, r3.rd, r3.wr]; exact hr _ (by omega)) fun s5 u5 =>
    wp_dp (op2_lsl (by decide)) fun t ht => WP.block_nil ?_
  have el : (s5.gpr .r3).toNat = VG.Proof.Ed25519.Arm.byteN s.mem (State.addr p) (2 * j) := by
    rw [u5.other _ (by decide), u4.gpr, m3, VG.Proof.Ed25519.Arm.toNat_setWidth8]; rfl
  have eh : (s5.gpr .r2 <<< 8).toNat = 256 * VG.Proof.Ed25519.Arm.byteN s.mem (State.addr p) (2 * j + 1) := by
    rw [u5.gpr, u4.mem, m3, toNat_shl, VG.Proof.Ed25519.Arm.toNat_setWidth8]
    have := (s.mem (State.addr p + BitVec.ofNat 64 (2 * j + 1))).isLt
    simp only [VG.Proof.Ed25519.Arm.byteN]
    omega
  refine ⟨r3.trans ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (ht.rest (by decide)))),
    by rw [ht.mem, u5.mem, u4.mem, m3], ?_⟩
  rw [ht.gpr]
  change (s5.gpr .r3 + (s5.gpr .r2 <<< 8)).toNat = _
  rw [toNat_add_lt (by rw [el, eh]; exact Nat.lt_trans (VG.Proof.Ed25519.Arm.packedLimb_lt _ _ _) (by decide)), el, eh]
  rfl

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ExpandBits`. -/
section
/-! Expansion of one scalar digit, with an exact sixteen-byte frame. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

structure ExpandInv (b : BitVec 32) (word : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.r3, .r9] s₀ s
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 32, k⟩] s₀.mem s.mem
  value : (s.gpr .r3).toNat = word / 2 ^ k
  bits : ∀ i < k, s.mem (State.addr b + BitVec.ofNat 64 (32 + i)) =
    BitVec.ofNat 8 ((word / 2 ^ i) % 2)

theorem expandBits_ok {b : BitVec 32} {s₀ : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s₀)
    (word : Nat) (hw : (s₀.gpr .r3).toNat = word) :
    WP isa (.block expandBits) s₀ fun t => Rest [.r3, .r9] s₀ t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 32, 16⟩] s₀.mem t.mem ∧
      ∀ i < 16, t.mem (State.addr b + BitVec.ofNat 64 (32 + i)) =
        BitVec.ofNat 8 ((word / 2 ^ i) % 2) := by
  refine WP.mono (wp_range_flatMap (M := isa) (VG.Proof.Ed25519.Arm.ExpandInv b word s₀)
    (fun k s hk h => ?_) 16 (Nat.le_refl _) s₀
    ⟨Rest.refl _ _, Frame.refl _ _, by simpa only [Nat.pow_zero, Nat.div_one] using hw,
      fun _ hi => by omega⟩) fun t ht => ⟨ht.rest, ht.frame, ht.bits⟩
  have hs := hc.of_rest h.rest (by decide)
  unfold expandBit
  refine wp_dp (op2_imm (by decide)) fun s1 u1 => ?_
  have e1 : (s1.gpr .r9).toNat = (word / 2 ^ k) % 2 := by
    rw [u1.gpr]
    change (s.gpr .r3 &&& (1 : BitVec 32)).toNat = _
    rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod, h.value]
  refine wp_strb (a := State.addr b + BitVec.ofNat 64 (32 + k)) (by omega)
    (by rw [u1.other _ (by decide)]; exact hs.ea (by omega))
    (by rw [u1.wr]; exact hs.inW (by omega)) fun s2 u2 =>
    wp_mov (op2_lsr (by decide)) fun t ht => WP.block_nil ?_
  have hm : t.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 (32 + k)) ((s1.gpr .r9).setWidth 8) := by
    rw [ht.mem, u2.mem, u1.mem]
  refine ⟨h.rest.trans ((u1.rest (by decide)).trans ((u2.rest _).trans (ht.rest (by decide)))),
    ?_, ?_, fun i hi => ?_⟩
  · rw [hm]
    refine (h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) _ ?_
    exact Offset.contains (State.addr b) (d := 32 + k) (n := 1) (e := 32) (k := k + 1)
      (by omega) (by omega) (by omega)
  · rw [ht.gpr]
    change (s2.gpr .r3 >>> 1).toNat = _
    rw [toNat_shr, u2.gpr, u1.other _ (by decide), h.value, Nat.div_div_eq_div_mul]
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
  · rw [hm, VG.WriteBytes.writeW8_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right (Offset.add_ofNat_ne _ (by omega) (by omega) (by omega))]
      exact h.bits i hi
    · rw [ite_eq_left rfl]; exact VG.Proof.Ed25519.Arm.byte_eq e1

end VG.Proof.Ed25519.Arm
end

/-! Each expanded digit contains the corresponding scalar bits. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem digit_bit (scalar start i : Nat) (hi : i < 16) :
    ((scalar / 2 ^ start) % 65536 / 2 ^ i) % 2 = (VG.Proof.Ed25519.Arm.scalarBit scalar (start + i)).toNat := by
  have hp : (65536 : Nat) = 2 ^ i * 2 ^ (16 - i) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
  rw [VG.Proof.Ed25519.Arm.scalarBit_nat, hp, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (show 2 ∣ 2 ^ (16 - i) from Nat.pow_dvd_pow (m := 1) (n := 16 - i) 2 (by omega)),
    Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem packedLimb_digit (m : Mem) (p : Addr) (n j : Nat) (hj : j < n) :
    VG.Proof.Ed25519.Arm.packedLimb m p j = val16 (VG.Proof.Ed25519.Arm.packedLimb m p) n / 2 ^ (16 * j) % 65536 :=
  (val16_div (fun k _ => VG.Proof.Ed25519.Arm.packedLimb_lt m p k) hj).symm

theorem batchBits_ok {b p : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s)
    (n j : Nat) (hj : j < n) (hn : n ≤ 32) (hfit : p.toNat + 2 * n ≤ 2 ^ 32)
    (hp : s.mem.readW (State.addr b + BitVec.ofNat 64 52) 32 = p)
    (hcj : s.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 j)
    (hr : ∀ i < 2 * n, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1) :
    WP isa (.block batchBits) s fun t => Rest [.r2, .r3, .r9, .r12] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 32, 16⟩] s.mem t.mem ∧
      ∀ i < 16, t.mem (State.addr b + BitVec.ofNat 64 (32 + i)) =
        BitVec.ofNat 8 (VG.Proof.Ed25519.Arm.scalarBit (val16 (VG.Proof.Ed25519.Arm.packedLimb s.mem (State.addr p)) n) (16 * j + i)).toNat := by
  unfold batchBits
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.Arm.batchDigit_ok hc n j hj hn hfit hp hcj hr) fun u ⟨ur, um, uv⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.Arm.expandBits_ok (hc.of_rest ur (by decide)) _ uv) fun t ⟨tr, tf, tb⟩ => ?_
  refine ⟨(ur.mono (by decide)).trans (tr.mono (by decide)), by rw [← um]; exact tf, fun i hi => ?_⟩
  rw [tb i hi, VG.Proof.Ed25519.Arm.packedLimb_digit _ _ n j hj, VG.Proof.Ed25519.Arm.digit_bit _ _ i hi]

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.Freeze`. -/
section

/-! Merged from `Proof.Ed25519.Arm.FreezeSteps`. -/
section
/-! Canonical reduction of the two temporary field elements. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem low15_val (x : BitVec 32) : ((x <<< 17) >>> 17).toNat = x.toNat % 32768 := by
  rw [toNat_shr, toNat_shl, show (2 : Nat) ^ 32 = 32768 * 2 ^ 17 from rfl, Nat.mul_mod_mul_right,
    Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

theorem sel0r (a c : BitVec 32) : a ^^^ ((c ^^^ a) &&& (0 - BitVec.ofNat 32 0)) = a := by simp

theorem sel1r (a c : BitVec 32) : a ^^^ ((c ^^^ a) &&& (0 - BitVec.ofNat 32 1)) = c := by
  have : (0 : BitVec 32) - BitVec.ofNat 32 1 = BitVec.allOnes 32 := by decide
  rw [this, BitVec.and_allOnes, BitVec.xor_comm c, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

variable {b : BitVec 32}

/-- The start of `freeze`: bit 255 of `[FR]` cleared, 19 times it in `r5`. -/
theorem freezeA_ok {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hl : Lim s.mem (State.addr b) FR) :
    WP isa (.block freezeA) s fun s' =>
      s'.gpr .r6 = mask16 ∧ (s'.gpr .r5).toNat = 19 * (limb s.mem (State.addr b) FR 15 / 32768) ∧
      (∀ k < 16, limb s'.mem (State.addr b) FR k = mask15 (limb s.mem (State.addr b) FR) k) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 FR, 64⟩] s.mem s'.mem ∧
      Rest [.r2, .r3, .r5, .r6] s s' := by
  have hX : FR = 1472 := rfl
  simp only [freezeA, low15, List.cons_append, List.nil_append]
  refine wp_movw fun s1 u1 => ?_
  have hc1 : VG.Proof.Ed25519.Arm.Ctx b s1 := hc.of_rest (u1.rest (ws := [.r6]) (by decide)) (by decide)
  refine ldr0_ok hc1 (d := FR + 60) (by decide) fun s2 u2 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s3 u3 => wp_mov (op2_lsl (by decide)) fun s4 u4 =>
    wp_mov (op2_lsr (by decide)) fun s5 u5 => ?_
  have hr5 : Rest [.r3, .r5, .r6] s s5 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans (u5.rest (by decide)))))
  have hc5 : VG.Proof.Ed25519.Arm.Ctx b s5 := hc.of_rest hr5 (by decide)
  refine str0_ok hc5 (d := FR + 60) (by decide) fun s6 u6 => ?_
  refine wp_mov (op2_imm (by decide)) fun s7 u7 => wp_mul fun s8 u8 => WP.block_nil ?_
  have hl15 := hl 15 (by decide)
  have e2 : (s2.gpr .r3).toNat = limb s.mem (State.addr b) FR 15 := by rw [u2.gpr, u1.mem]; rfl
  have e5 : (s5.gpr .r3).toNat = limb s.mem (State.addr b) FR 15 % 32768 := by
    rw [u5.gpr, u4.gpr, VG.Proof.Ed25519.Arm.low15_val, u3.other .r3 (by decide), e2]
  have e3 : (s3.gpr .r5).toNat = limb s.mem (State.addr b) FR 15 / 32768 := by
    rw [u3.gpr, toNat_shr, e2]
  have hm6 : s6.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 (FR + 60)) (s5.gpr .r3) := by
    rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨?_, ?_, fun k hk => ?_, ?_, ?_⟩
  · rw [u8.other _ (by decide), u7.other _ (by decide), u6.gpr, u5.other .r6 (by decide),
      u4.other .r6 (by decide), u3.other .r6 (by decide), u2.other .r6 (by decide), u1.gpr]
  · rw [u8.gpr, u7.other _ (by decide), u7.gpr, u6.gpr, u5.other _ (by decide), u4.other _ (by decide),
      toNat_mul_lt (by rw [e3]; show _ * 19 < _; omega), e3]
    show _ * 19 = _
    omega
  · rw [limb, u8.mem, u7.mem, hm6]
    rcases Nat.lt_or_ge k 15 with h | h
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
      simp only [mask15, show k ≠ 15 by omega, ite_false]; rfl
    · rw [show FR + 4 * k = FR + 60 by omega, wd_write_self, e5, show k = 15 by omega]; rfl
  · rw [u8.mem, u7.mem, hm6]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (d := FR + 60) (n := 4) (Nat.le_add_right _ _) (by omega) (by omega))
  · exact (hr5.mono (by decide)).trans ((u6.rest _).trans ((u7.rest (by decide)).trans (u8.rest (by decide))))

/-- `freezeB`: the mask `-(bit 255 of [FY])` in `r9`, and bit 255 of `[FY]` cleared. -/
theorem freezeB_ok {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) :
    WP isa (.block freezeB) s fun s' =>
      s'.gpr .r9 = 0 - BitVec.ofNat 32 (limb s.mem (State.addr b) FY 15 / 32768) ∧
      (∀ k < 16, limb s'.mem (State.addr b) FY k = mask15 (limb s.mem (State.addr b) FY) k) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 FY, 64⟩] s.mem s'.mem ∧ Rest [.r1, .r3, .r9] s s' := by
  have hFY : FY = 1536 := rfl
  simp only [freezeB, low15, List.cons_append, List.nil_append]
  refine ldr0_ok hc (d := FY + 60) (by decide) fun s1 u1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s2 u2 => wp_mov (op2_imm (by decide)) fun s3 u3 =>
    wp_dp (op2_reg _ _) fun s4 u4 => wp_mov (op2_lsl (by decide)) fun s5 u5 =>
    wp_mov (op2_lsr (by decide)) fun s6 u6 => ?_
  have hr6 : Rest [.r1, .r3, .r9] s s6 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  refine str0_ok (hc.of_rest hr6 (by decide)) (d := FY + 60) (by decide) fun s7 u7 => WP.block_nil ?_
  have e1 : (s1.gpr .r3).toNat = limb s.mem (State.addr b) FY 15 := by rw [u1.gpr]; rfl
  have hm7 : s7.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 (FY + 60)) (s6.gpr .r3) := by
    rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨?_, fun k hk => ?_, ?_, hr6.trans (u7.rest _)⟩
  · rw [u7.gpr, u6.other _ (by decide), u5.other _ (by decide), u4.gpr]
    show s3.gpr .r1 - s3.gpr .r9 = _
    rw [u3.gpr, u3.other _ (by decide), u2.gpr]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [toNat_shr, e1, toNat_imm (by have := wd_lt s.mem (State.addr b) (FY + 4 * 15); unfold limb; omega)]
  · rw [limb, hm7]
    rcases Nat.lt_or_ge k 15 with h | h
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
      simp only [mask15, show k ≠ 15 by omega, ite_false]; rfl
    · rw [show FY + 4 * k = FY + 60 by omega, wd_write_self, u6.gpr, u5.gpr, VG.Proof.Ed25519.Arm.low15_val, u4.other .r3 (by decide),
        u3.other .r3 (by decide), u2.other .r3 (by decide), e1, show k = 15 by omega]; rfl
  · rw [hm7]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (d := FY + 60) (n := 4) (Nat.le_add_right _ _) (by omega) (by omega))

theorem freezeCopy_ok {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (a : Slot) :
    WP isa (.block (freezeCopy a)) s fun t => Rest [.r3] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 FR, 64⟩] s.mem t.mem ∧
      ∀ k < 16, limb t.mem (State.addr b) FR k = limb s.mem (State.addr b) (offset a) k := by
  have ha := VG.Proof.Ed25519.Arm.slot_range a
  rw [VG.Proof.Ed25519.Arm.ACC_eq] at ha
  refine WP.mono (VG.Proof.Ed25519.Arm.fill_ok (src := fun k => [.ldr .r3 .r0 (offset a + 4 * k)])
    (f := limb s.mem (State.addr b) (offset a)) hc (by decide)
    (fun k hk t ht => ldr0_ok (hc.of_rest ht.rest (by decide)) (by omega)
      fun u hu => WP.block_nil ⟨?_, hu.rest (by decide), hu.mem⟩))
    fun t ht => ⟨ht.rest, ht.frame, ht.outs⟩
  rw [hu.gpr]
  exact wd_frame ht.frame fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by change _ ≤ 1472; omega)) (by omega) (by change 1472 + _ ≤ _; omega)

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.FreezeSelect`. -/
section
/-! Select the reduced limbs without a data-dependent branch. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem freezeSelect_ok {b : BitVec 32} {s0 : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s0) {sw : Nat}
    (hsw : sw ≤ 1) (h9 : s0.gpr .r9 = 0 - BitVec.ofNat 32 sw) :
    WP isa (.block freezeSelect) s0 fun t => Rest [.r2, .r3] s0 t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 FR, 64⟩] s0.mem t.mem ∧
      ∀ k < 16, limb t.mem (State.addr b) FR k =
        sel sw (limb s0.mem (State.addr b) FR k) (limb s0.mem (State.addr b) FY k) := by
  have hR : FR = 1472 := rfl
  have hY : FY = 1536 := rfl
  refine WP.mono (VG.Proof.Ed25519.Arm.fill_regs_ok (ws := [.r2, .r3]) (by decide) (src := selectSrc)
    (f := fun k => sel sw (limb s0.mem (State.addr b) FR k) (limb s0.mem (State.addr b) FY k))
    hc (by decide) (fun k hk s h => ?_)) fun t ht => ⟨ht.rest, ht.frame, ht.outs⟩
  have hcs := hc.of_rest h.rest (by decide)
  unfold selectSrc
  refine ldr0_ok hcs (d := FR + 4 * k) (by omega) fun t1 v1 => ?_
  refine ldr0_ok (hcs.of_rest (v1.rest (ws := [.r3]) (by decide)) (by decide))
    (d := FY + 4 * k) (by omega) fun t2 v2 => ?_
  refine wp_dp (op2_reg _ _) fun t3 v3 => wp_dp (op2_reg _ _) fun t4 v4 =>
    wp_dp (op2_reg _ _) fun t5 v5 => WP.block_nil ?_
  have ex : t2.gpr .r3 = s.mem.readW (State.addr b + BitVec.ofNat 64 (FR + 4 * k)) 32 := by
    rw [v2.other _ (by decide), v1.gpr]
  have ey : t2.gpr .r2 = s.mem.readW (State.addr b + BitVec.ofNat 64 (FY + 4 * k)) 32 := by
    rw [v2.gpr, v1.mem]
  have em : t3.gpr .r9 = 0 - BitVec.ofNat 32 sw := by
    rw [v3.other _ (by decide), v2.other _ (by decide), v1.other _ (by decide),
      h.rest.gpr _ (by decide), h9]
  have hx : limb s.mem (State.addr b) FR k = limb s0.mem (State.addr b) FR k :=
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  have hy : limb s.mem (State.addr b) FY k = limb s0.mem (State.addr b) FY k :=
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  refine ⟨?_, (v1.rest (by decide)).trans ((v2.rest (by decide)).trans
    ((v3.rest (by decide)).trans ((v4.rest (by decide)).trans (v5.rest (by decide))))),
    by rw [v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]⟩
  rw [v5.gpr]
  show (t4.gpr .r3 ^^^ t4.gpr .r2).toNat = _
  rw [v4.other .r3 (by decide), v4.gpr]
  show (t3.gpr .r3 ^^^ (t3.gpr .r2 &&& t3.gpr .r9)).toNat = _
  rw [v3.other .r3 (by decide), v3.gpr, em]
  show (t2.gpr .r3 ^^^ ((t2.gpr .r2 ^^^ t2.gpr .r3) &&& _)).toNat = _
  rw [ex, ey]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
  · rw [VG.Proof.Ed25519.Arm.sel0r]; exact hx
  · rw [VG.Proof.Ed25519.Arm.sel1r]; exact hy

end VG.Proof.Ed25519.Arm
end

/-! Canonical reduction preserves all working field elements. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm
open VG.Spec.X25519 (P)
variable {b : BitVec 32}

theorem freezeCore_ok {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hl : Lim s.mem (State.addr b) FR) :
    WP isa (.block freezeCore) s fun t => Rest clob s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] s.mem t.mem ∧
      Lim t.mem (State.addr b) FR ∧ V t.mem (State.addr b) FR = V s.mem (State.addr b) FR % P := by
  have hX : FR = 1472 := rfl
  have hFY : FY = 1536 := rfl
  obtain ⟨tA, tFY, hS, hR, hv⟩ := freeze_facts hl
  obtain ⟨-, -, lm, c1⟩ := mask15_facts hl
  simp only [freezeCore, List.append_assoc, List.cons_append, List.nil_append]
  refine WP.append (VG.Proof.Ed25519.Arm.freezeA_ok hc hl) fun s1 ⟨h6, h5, hl1, hf1, hr1⟩ => ?_
  have hc1 : VG.Proof.Ed25519.Arm.Ctx b s1 := hc.of_rest hr1 (by decide)
  refine WP.append (pass_ok (rb := .r0) (o := FR) (s0 := s1) (c := mask15 (limb s.mem (State.addr b) FR))
    (cin := 19 * (limb s.mem (State.addr b) FR 15 / 32768)) (by decide) (by decide)
    (by rw [hc1.r0]; have := hc.fit; omega) (fun k hk => by rw [hc1.r0]; exact hc1.inW (by omega)) h6 h5
    (fun k hk => by have := lm k hk; omega) (by omega) ?_) fun s2 hp2 => ?_
  · intro k hk s' hp
    refine WP.mono (ldSrc_ok (hc1.of_rest hp.rest (by decide)) (o := FR) (k := k) (by omega)) fun t ht => ⟨?_, ht.2.1.mono (by decide), ht.2.2⟩
    rw [ht.1, wd_pass hc1 hp.frame (by omega) (by omega) (by omega)]
    exact hl1 k hk
  have hc2 : VG.Proof.Ed25519.Arm.Ctx b s2 := hc1.of_rest hp2.rest (by decide)
  have hpo2 : ∀ j < 16, wd s2.mem (State.addr b) (FR + 4 * j) = frA (limb s.mem (State.addr b) FR) j :=
    fun j hj => by have := hp2.outs j hj; rwa [hc1.r0] at this
  have hpf2 : Frame [⟨State.addr b + BitVec.ofNat 64 FR, 64⟩] s1.mem s2.mem := by
    have := hp2.frame; rwa [hc1.r0] at this
  refine wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
  have hc3 : VG.Proof.Ed25519.Arm.Ctx b s3 := hc2.of_rest (u3.rest (ws := [.r5]) (by decide)) (by decide)
  refine WP.append (pass_ok (rb := .r0) (o := FY) (s0 := s3) (c := frA (limb s.mem (State.addr b) FR))
    (cin := 19) (by decide) (by decide)
    (by rw [hc3.r0]; have := hc.fit; omega) (fun k hk => by rw [hc3.r0]; exact hc3.inW (by omega))
    (by rw [u3.other _ (by decide), hp2.rest.gpr _ (by decide)]; exact h6)
    (by rw [u3.gpr]; rfl) (fun k hk => by have := out_lt (mask15 (limb s.mem (State.addr b) FR)) (19 * (limb s.mem (State.addr b) FR 15 / 32768)) k; unfold frA; omega) (by decide) ?_) fun s4 hp4 => ?_
  · intro k hk s' hp
    refine WP.mono (ldSrc_ok (hc3.of_rest hp.rest (by decide)) (o := FR) (k := k) (by omega)) fun t ht => ⟨?_, ht.2.1.mono (by decide), ht.2.2⟩
    rw [ht.1, wd_pass hc3 hp.frame (by omega) (by omega) (by omega), u3.mem]
    exact hpo2 k hk
  have hc4 : VG.Proof.Ed25519.Arm.Ctx b s4 := hc3.of_rest hp4.rest (by decide)
  have hpo4 : ∀ j < 16, wd s4.mem (State.addr b) (FY + 4 * j) = frY (limb s.mem (State.addr b) FR) j :=
    fun j hj => by have := hp4.outs j hj; rwa [hc3.r0] at this
  have hpf4 : Frame [⟨State.addr b + BitVec.ofNat 64 FY, 64⟩] s3.mem s4.mem := by
    have := hp4.frame; rwa [hc3.r0] at this
  have hx4 : ∀ k < 16, limb s4.mem (State.addr b) FR k = frA (limb s.mem (State.addr b) FR) k := by
    intro k hk
    rw [limb, wd_frame hpf4 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega),
      u3.mem, hpo2 k hk]
  refine WP.append (VG.Proof.Ed25519.Arm.freezeB_ok hc4) fun s5 ⟨h9, hy5, hf5, hr5⟩ => ?_
  have hc5 : VG.Proof.Ed25519.Arm.Ctx b s5 := hc4.of_rest hr5 (by decide)
  have hx5 : ∀ k < 16, limb s5.mem (State.addr b) FR k = frA (limb s.mem (State.addr b) FR) k := by
    intro k hk
    rw [limb, wd_frame hf5 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)]
    exact hx4 k hk
  have hy5' : ∀ k < 16, limb s5.mem (State.addr b) FY k = mask15 (frY (limb s.mem (State.addr b) FR)) k := by
    intro k hk
    rw [hy5 k hk]
    simp only [mask15]
    split
    · rename_i h; subst h; rw [limb, hpo4 15 (by decide)]
    · rw [limb, hpo4 k hk]
  have h9' : s5.gpr .r9 = 0 - BitVec.ofNat 32 (frS (limb s.mem (State.addr b) FR)) := by
    rw [h9, limb, hpo4 15 (by decide)]; rfl
  have hr45 : Rest [.r1, .r2, .r3, .r4, .r5, .r6, .r9] s s5 :=
    (hr1.mono (by decide)).trans ((hp2.rest.mono (by decide)).trans ((u3.rest (by decide)).trans
      ((hp4.rest.mono (by decide)).trans (hr5.mono (by decide)))))
  refine WP.mono (VG.Proof.Ed25519.Arm.freezeSelect_ok hc5 hS h9') fun s6 h6' => ?_
  have hr : ∀ k < 16, limb s6.mem (State.addr b) FR k = frR (limb s.mem (State.addr b) FR) k :=
    fun k hk => by rw [h6'.2.2 k hk, hx5 k hk, hy5' k hk]; rfl
  refine ⟨(hr45.mono (by decide)).trans (h6'.1.mono (by decide)), ?_,
    fun k hk => by rw [hr k hk]; exact hR k hk, ?_⟩
  · have hfa : ∀ z, ACC ≤ z → z + 64 ≤ ACC + 128 →
        Region.Sub ⟨State.addr b + BitVec.ofNat 64 z, 64⟩
          ⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩ :=
      fun z h1 h2 => Offset.sub _ h1 h2
    have extend : ∀ {z m m'}, (z = FR ∨ z = FY) →
        Frame [⟨State.addr b + BitVec.ofNat 64 z, 64⟩] m m' →
        Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] m m' := by
      intro z m m' hz hf
      refine hf.sub fun r hmem => ⟨_, List.mem_singleton_self _, ?_⟩
      rw [List.mem_singleton.mp hmem]
      rcases hz with rfl | rfl <;> exact hfa _ (by decide) (by decide)
    refine (extend (.inl rfl) hf1).trans ((extend (.inl rfl) hpf2).trans ?_)
    rw [← u3.mem]
    exact (extend (.inr rfl) hpf4).trans ((extend (.inr rfl) hf5).trans (extend (.inl rfl) h6'.2.1))
  · rw [V, val16_congr hr, hv]
    rfl

theorem freezeRaw_ok {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem b) (a : Slot) :
    WP isa (.block (freeze a)) s fun t => VG.Proof.Ed25519.Arm.Keep b s t ∧ VG.Proof.Ed25519.Arm.AllLim t.mem b ∧
      VG.Proof.Ed25519.Arm.env t.mem b = VG.Proof.Ed25519.Arm.env s.mem b ∧ Lim t.mem (State.addr b) FR ∧
      V t.mem (State.addr b) FR = (VG.Proof.Ed25519.Arm.env s.mem b a).val ∧
      ∀ (i : Slot) k, k < 16 → limb t.mem (State.addr b) (offset i) k = limb s.mem (State.addr b) (offset i) k := by
  rw [freeze, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.Arm.freezeCopy_ok hc a) fun u ⟨hr, hf, he⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.Arm.freezeCore_ok (hc.of_rest hr (by decide))
    (fun k hk => by rw [he k hk]; exact hl a k hk)) fun t ⟨hr', hf', hl', hv⟩ => ?_
  have hframe : Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] s.mem t.mem :=
    (hf.sub fun r hm => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hm]; exact Region.sub_prefix (by decide)⟩).trans hf'
  have hs : ∀ (i : Slot) k, k < 16 →
      limb t.mem (State.addr b) (offset i) k = limb s.mem (State.addr b) (offset i) k := by
    intro i k hk
    have hi := VG.Proof.Ed25519.Arm.slot_range i
    refine limb_frame hframe (fun r hm j hj => ?_) k hk
    rw [List.mem_singleton.mp hm]
    exact Offset.disjoint _ (.inl (by omega)) (by rw [VG.Proof.Ed25519.Arm.ACC_eq] at hi; omega) (by decide)
  refine ⟨⟨(hr.mono (by decide)).trans hr', ?_⟩,
    fun i k hk => by rw [hs i k hk]; exact hl i k hk,
    funext fun i => congrArg VG.Proof.X25519.toFe (val16_congr (hs i)), hl', ?_, hs⟩
  · exact hframe.sub fun r hm => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hm]; exact Offset.sub _ (by decide) (by decide)⟩
  · rw [hv, V, val16_congr he]
    rfl

theorem freeze_ok {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem b) (a : Slot) :
    WP isa (.block (freeze a)) s fun t => VG.Proof.Ed25519.Arm.Keep b s t ∧ VG.Proof.Ed25519.Arm.AllLim t.mem b ∧
      VG.Proof.Ed25519.Arm.env t.mem b = VG.Proof.Ed25519.Arm.env s.mem b ∧ Lim t.mem (State.addr b) FR ∧
      V t.mem (State.addr b) FR = (VG.Proof.Ed25519.Arm.env s.mem b a).val :=
  WP.mono (VG.Proof.Ed25519.Arm.freezeRaw_ok hc hl a) fun _ ⟨hk, ht, he, hf, hv, _⟩ => ⟨hk, ht, he, hf, hv⟩

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.InitFields`. -/
section

/-! Establish the limb bounds for the whole field workspace. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm
variable {b : BitVec 32}

/-- Stores of register `r` into the `n` words from `o`. -/
theorem stores_ok {r : Reg} {o n : Nat} (ho : o + 4 * n ≤ 4096) {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) :
    WP isa (.block (storeN r o n)) s fun s' =>
      (∀ j < n, wd s'.mem (State.addr b) (o + 4 * j) = (s.gpr r).toNat) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 4 * n⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ Rest [] s s' := by
  unfold storeN
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun m s' => (∀ j < m, wd s'.mem (State.addr b) (o + 4 * j) = (s.gpr r).toNat) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 4 * m⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ Rest [] s s')
    (fun m s' hm ⟨h1, h2, h3, h4⟩ => ?_) n (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, rfl, Rest.refl _ _⟩) fun s' h => h
  refine str0_ok (hc.of_rest h4 (by decide)) (d := o + 4 * m) (by omega) fun s2 u2 =>
    WP.block_nil ⟨fun j hj => ?_, ?_, by rw [u2.gpr, h3], h4.trans (u2.rest _)⟩
  · rw [u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h1 j hj
    · rw [wd_write_self, h3]
  · rw [u2.mem]
    exact (h2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))

theorem initFields_ok {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) :
    WP isa (.block initFields) s fun t => VG.Proof.Ed25519.Arm.Keep b s t ∧ VG.Proof.Ed25519.Arm.AllLim t.mem b ∧
      ∀ i : Slot, VG.Proof.Ed25519.Arm.env t.mem b i = 0 := by
  rw [initFields, WP.block_append_iff]
  refine wp_mov (op2_imm (by decide)) fun u hu => WP.block_nil ?_
  refine WP.mono (VG.Proof.Ed25519.Arm.stores_ok (r := .r3) (o := 64) (n := 352) (by decide)
    (hc.of_rest (hu.rest (ws := [.r3]) (by decide)) (by decide)))
    fun t ⟨hout, hf, _, hr⟩ => ?_
  have he : ∀ (i : Slot) k, k < 16 → limb t.mem (State.addr b) (offset i) k = 0 := by
    intro i k hk
    have h := hout (16 * i.val + k) (by omega)
    rw [hu.gpr] at h
    have hd : 64 + 4 * (16 * i.val + k) = offset i + 4 * k := by
      simp only [offset]
      omega
    rw [hd] at h
    exact h
  refine ⟨⟨(hu.rest (by decide)).trans (hr.mono (by decide)), ?_⟩,
    fun i k hk => by rw [he i k hk]; decide, fun i => ?_⟩
  · rw [← hu.mem]
    exact hf.sub fun r hmem => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hmem]; exact Region.sub_prefix (by decide)⟩
  · change VG.Proof.X25519.toFe (val16 (limb t.mem (State.addr b) (offset i)) 16) = 0
    rw [val16_congr (he i), val16_zero_fn]
    rfl

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.PointEncode`. -/
section

/-! Canonical point encoding in sixteen bounded limbs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem parity_limb {m : Mem} {base : Addr} {o : Nat} (hl : Lim m base o) :
    V m base o % 2 = limb m base o 0 % 2 := by
  have he := val16_div hl (k := 0) (by decide)
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one] at he
  rw [← he, Nat.mod_mod_of_dvd _ (by decide)]
  rfl

theorem pointSign_ok {s : State} {b : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx b s)
    (hl : Lim s.mem (State.addr b) FR) :
    WP isa (.block pointSign) s fun t => VG.Proof.Ed25519.Arm.IKeep b s t ∧ t.mem = s.mem ∧
      (t.gpr .r10).toNat = (V s.mem (State.addr b) FR % 2) * 32768 := by
  refine ldr0_ok hc (by decide) fun s1 u1 => wp_dp (op2_imm (by decide)) fun s2 u2 =>
    wp_mov (op2_lsl (by decide)) fun s3 u3 => WP.block_nil ?_
  have hm : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  refine ⟨⟨(u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide))),
    by rw [hm]; exact Frame.refl _ _⟩, hm, ?_⟩
  rw [u3.gpr, toNat_shl, u2.gpr]
  change (((s1.gpr .r3 &&& 1).toNat) * 32768) % 2 ^ 32 = _
  rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod, u1.gpr]
  have he : (s.mem.readW (State.addr b + BitVec.ofNat 64 FR) 32).toNat =
      limb s.mem (State.addr b) FR 0 := rfl
  rw [he, ← VG.Proof.Ed25519.Arm.parity_limb hl, Nat.mod_eq_of_lt (by omega)]

theorem encodeSign_ok {s : State} {b : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx b s)
    (hl : Lim s.mem (State.addr b) FR) (x y : Nat) (hy : y < 2 ^ 255)
    (hv : V s.mem (State.addr b) FR = y) (hs : (s.gpr .r10).toNat = (x % 2) * 32768) :
    WP isa (.block encodeSign) s fun t => VG.Proof.Ed25519.Arm.Keep b s t ∧ Lim t.mem (State.addr b) FR ∧
      V t.mem (State.addr b) FR = y + (x % 2) * 2 ^ 255 := by
  have hR : FR = 1472 := rfl
  have hy' : val16 (limb s.mem (State.addr b) FR) 15 +
      2 ^ 240 * limb s.mem (State.addr b) FR 15 = y := hv
  have hb : limb s.mem (State.addr b) FR 15 < 32768 := by omega
  refine ldr0_ok hc (by decide) fun s1 u1 => wp_dp (op2_reg _ _) fun s2 u2 => ?_
  have hr2 : Rest [.r3] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have he : (s2.gpr .r3).toNat = limb s.mem (State.addr b) FR 15 + (x % 2) * 32768 := by
    rw [u2.gpr]
    change (s1.gpr .r3 + s1.gpr .r10).toNat = _
    rw [u1.other .r10 (by decide), u1.gpr]
    have hread : (s.mem.readW (State.addr b + BitVec.ofNat 64 (FR + 60)) 32).toNat =
        limb s.mem (State.addr b) FR 15 := rfl
    rw [toNat_add_lt (by rw [hread, hs]; omega), hread, hs]
  refine str0_ok (hc.of_rest hr2 (by decide)) (by decide) fun t ht => WP.block_nil ?_
  have hm : t.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 (FR + 60)) (s2.gpr .r3) := by
    rw [ht.mem, u2.mem, u1.mem]
  have epre : ∀ k < 15, limb t.mem (State.addr b) FR k = limb s.mem (State.addr b) FR k := by
    intro k hk
    rw [limb, hm, wd_write_other _ _ _ (by omega) (by omega) (by omega)]
    rfl
  have elast : limb t.mem (State.addr b) FR 15 =
      limb s.mem (State.addr b) FR 15 + (x % 2) * 32768 := by
    rw [limb, hm, wd_write_self, he]
  refine ⟨⟨(hr2.trans (ht.rest _)).mono (by decide), ?_⟩, ?_, ?_⟩
  · rw [hm]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by decide) (by decide) (by decide))
  · intro k hk
    rcases Nat.lt_or_ge k 15 with hk' | hk'
    · rw [epre k hk']; exact hl k hk
    · rw [show k = 15 by omega, elast]; omega
  · rw [V, val16_succ, val16_congr epre, elast]
    change val16 (limb s.mem (State.addr b) FR) 15 +
      2 ^ 240 * (limb s.mem (State.addr b) FR 15 + (x % 2) * 32768) = _
    omega

theorem pointEncode_ok {s : State} {base : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx base s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem base) :
    WP isa pointEncode s fun t => VG.Proof.Ed25519.Arm.IKeep base s t ∧ Lim t.mem (State.addr base) FR ∧
      V t.mem (State.addr base) FR =
        (VG.Proof.Ed25519.Arm.env s.mem base 1 * Spec.X25519.pow (VG.Proof.Ed25519.Arm.env s.mem base 2) (Spec.X25519.P - 2)).val +
        ((VG.Proof.Ed25519.Arm.env s.mem base 0 * Spec.X25519.pow (VG.Proof.Ed25519.Arm.env s.mem base 2) (Spec.X25519.P - 2)).val % 2) * 2 ^ 255 := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.pointAffine_ok hc hl) fun a ⟨ka, la, ax, ay⟩ => ?_)
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.Arm.freeze_ok (ka.ctx hc) la 0) fun b ⟨kb, lb, eb, lxb, bx⟩ => ?_
  have kab : VG.Proof.Ed25519.Arm.IKeep base s b := ka.trans (IKeep.of_keep kb)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.Arm.pointSign_ok (kab.ctx hc) lxb) fun c ⟨kc, mc, cx⟩ => ?_
  have kabc := kab.trans kc
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.Arm.freeze_ok (kabc.ctx hc) (by rw [mc]; exact lb) 1)
    fun d ⟨kd, _, _, lyd, dy⟩ => ?_
  have kabcd := kabc.trans (IKeep.of_keep kd)
  have dx : (d.gpr .r10).toNat =
      ((VG.Proof.Ed25519.Arm.env s.mem base 0 * Spec.X25519.pow (VG.Proof.Ed25519.Arm.env s.mem base 2) (Spec.X25519.P - 2)).val % 2) * 32768 := by
    rw [kd.rest.gpr .r10 (by decide), cx, bx, ax]
  rw [mc, eb, ay] at dy
  refine WP.mono (VG.Proof.Ed25519.Arm.encodeSign_ok (kabcd.ctx hc) lyd _ _
    (Nat.lt_trans (VG.Proof.Ed25519.Arm.env s.mem base 1 * Spec.X25519.pow (VG.Proof.Ed25519.Arm.env s.mem base 2) (Spec.X25519.P - 2)).isLt
      (by decide : Spec.X25519.P < 2 ^ 255)) dy dx) fun t ⟨kt, lt, vt⟩ => ?_
  exact ⟨kabcd.trans (IKeep.of_keep kt), lt, vt⟩

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.RecoverAdjust`. -/
section

/-! Merged from `Proof.Ed25519.Arm.RecoverParity`. -/
section
/-! Merged from `Proof.Ed25519.Arm.FieldCheck`. -/
section
/-! Merged from `Proof.Ed25519.Arm.WordsZero`. -/
section
/-! Summing sixteen bounded limbs cannot overflow and detects zero. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def limbSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => VG.Proof.Ed25519.Arm.limbSum f n + f n

theorem limbSum_bound {f : Nat → Nat} {n : Nat} (hf : ∀ k < n, f k < 65536) :
    VG.Proof.Ed25519.Arm.limbSum f n ≤ 65535 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h := ih (fun k hk => hf k (by omega))
    have hn := hf n (by omega)
    simp only [VG.Proof.Ed25519.Arm.limbSum, Nat.mul_succ]
    omega

theorem limbSum_zero (f : Nat → Nat) (n : Nat) : VG.Proof.Ed25519.Arm.limbSum f n = 0 ↔ val16 f n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [VG.Proof.Ed25519.Arm.limbSum, val16_succ, Nat.add_eq_zero_iff, Nat.mul_eq_zero,
      Nat.ne_of_gt (Nat.two_pow_pos _), false_or, ih]

structure SumInv (b : BitVec 32) (o : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.r3, .r9] s₀ s
  mem : s.mem = s₀.mem
  value : (s.gpr .r9).toNat = VG.Proof.Ed25519.Arm.limbSum (limb s₀.mem (State.addr b) o) k

theorem sumLimbs_ok {b : BitVec 32} {s₀ : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s₀) (o : Nat) (ho : o + 64 ≤ 4096)
    (hl : Lim s₀.mem (State.addr b) o) (hz : (s₀.gpr .r9).toNat = 0) :
    WP isa (.block ((List.range 16).flatMap (sumLimb o))) s₀ fun t => Rest [.r3, .r9] s₀ t ∧
      t.mem = s₀.mem ∧ (t.gpr .r9).toNat = VG.Proof.Ed25519.Arm.limbSum (limb s₀.mem (State.addr b) o) 16 := by
  refine WP.mono (wp_range_flatMap (M := isa) (VG.Proof.Ed25519.Arm.SumInv b o s₀) (fun k s hk h => ?_)
    16 (Nat.le_refl _) s₀ ⟨Rest.refl _ _, rfl, hz⟩) fun t ht => ⟨ht.rest, ht.mem, ht.value⟩
  refine ldr0_ok (hc.of_rest h.rest (by decide)) (by omega) fun u hu =>
    wp_dp (op2_reg _ _) fun t ht => WP.block_nil ?_
  have el : (u.gpr .r3).toNat = limb s₀.mem (State.addr b) o k := by rw [hu.gpr, h.mem]; rfl
  have es : (u.gpr .r9).toNat = VG.Proof.Ed25519.Arm.limbSum (limb s₀.mem (State.addr b) o) k := by
    rw [hu.other _ (by decide), h.value]
  refine ⟨h.rest.trans ((hu.rest (by decide)).trans (ht.rest (by decide))),
    by rw [ht.mem, hu.mem, h.mem], ?_⟩
  rw [ht.gpr]
  change (u.gpr .r9 + u.gpr .r3).toNat = _
  rw [toNat_add_lt (by
    rw [es, el]
    have := VG.Proof.Ed25519.Arm.limbSum_bound (fun j hj => hl j (by omega) : ∀ j < k, limb s₀.mem (State.addr b) o j < 65536)
    have := hl k hk
    omega), es, el]
  rfl

theorem wordsZero_ok {b : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (o : Nat) (ho : o + 64 ≤ 4096)
    (hl : Lim s.mem (State.addr b) o) :
    WP isa (.block (wordsZero o)) s fun t => Rest [.r3, .r9] s t ∧ t.mem = s.mem ∧
      t.z = decide (V s.mem (State.addr b) o = 0) := by
  unfold wordsZero
  rw [List.append_assoc, WP.block_append_iff]
  refine wp_mov (op2_imm (by decide)) fun u hu => WP.block_nil ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.Arm.sumLimbs_ok (hc.of_rest (hu.rest (ws := [.r9]) (by decide)) (by decide)) o ho
    (by rw [hu.mem]; exact hl) (by rw [hu.gpr]; rfl)) fun v ⟨vr, vm, vv⟩ => ?_
  refine wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ?_
  refine ⟨(hu.rest (by decide)).trans (vr.trans (ht.rest _)), by rw [ht.mem, vm, hu.mem], ?_⟩
  have ve : v.gpr .r9 = BitVec.ofNat 32 (VG.Proof.Ed25519.Arm.limbSum (limb s.mem (State.addr b) o) 16) := by
    apply BitVec.eq_of_toNat_eq
    rw [vv, hu.mem, toNat_imm (by have := VG.Proof.Ed25519.Arm.limbSum_bound hl; omega)]
  have he : v.gpr .r9 - (0 : BitVec 32) = v.gpr .r9 := BitVec.sub_zero _
  rw [hz, he, ve, ofNat_beq_zero (by have := VG.Proof.Ed25519.Arm.limbSum_bound hl; omega)]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact VG.Proof.Ed25519.Arm.limbSum_zero _ _

end VG.Proof.Ed25519.Arm
end

/-! Canonical representatives give exact field comparisons. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem fieldZero_ok {s : State} {b : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem b) (a : Slot) :
    WP isa (fieldZero a) s fun t => VG.Proof.Ed25519.Arm.Keep b s t ∧ VG.Proof.Ed25519.Arm.AllLim t.mem b ∧ VG.Proof.Ed25519.Arm.env t.mem b = VG.Proof.Ed25519.Arm.env s.mem b ∧
      t.z = decide (VG.Proof.Ed25519.Arm.env s.mem b a = 0) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.freeze_ok hc hl a) fun u ⟨uk, ul, ue, uf, uv⟩ => ?_)
  refine WP.mono (VG.Proof.Ed25519.Arm.wordsZero_ok (uk.ctx hc) FR (by decide) uf) fun t ⟨tr, tm, tz⟩ => ?_
  refine ⟨uk.trans ⟨tr.mono (by decide), by rw [tm]; exact Frame.refl _ _⟩,
    tm ▸ ul, (congrArg (fun m => VG.Proof.Ed25519.Arm.env m b) tm).trans ue, ?_⟩
  rw [tz, uv]
  have he : (VG.Proof.Ed25519.Arm.env s.mem b a).val = 0 ↔ VG.Proof.Ed25519.Arm.env s.mem b a = 0 :=
    ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  simp only [he]

theorem fieldEqual_ok {s : State} {base : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx base s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem base)
    (a b : Slot) :
    WP isa (fieldEqual a b) s fun t => VG.Proof.Ed25519.Arm.Keep base s t ∧ VG.Proof.Ed25519.Arm.AllLim t.mem base ∧
      (∀ i : Slot, i ≠ 21 → VG.Proof.Ed25519.Arm.env t.mem base i = VG.Proof.Ed25519.Arm.env s.mem base i) ∧
      t.z = decide (VG.Proof.Ed25519.Arm.env s.mem base a = VG.Proof.Ed25519.Arm.env s.mem base b) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.fieldCode_ok [.sub 21 a b] hc hl) fun u ⟨uk, ul, ue⟩ => ?_)
  refine WP.mono (VG.Proof.Ed25519.Arm.fieldZero_ok (uk.ctx hc) ul 21) fun t ⟨tk, tl, te, tz⟩ => ?_
  refine ⟨uk.trans tk, tl, fun i hi => ?_, ?_⟩
  · rw [te, ue]
    exact Function.update_of_ne hi _ _
  · rw [tz, ue]
    change decide (VG.Proof.Ed25519.Arm.env s.mem base a - VG.Proof.Ed25519.Arm.env s.mem base b = 0) = _
    simp only [show ∀ u v : VG.Spec.X25519.Fe, u - v = 0 ↔ u = v from
      fun _ _ => ⟨fun _ => by grind, fun _ => by grind⟩]

end VG.Proof.Ed25519.Arm
end

/-! Sign checks use the canonical x-coordinate and the saved sign bit. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem IKeep.sign {base : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.Arm.IKeep base s t) :
    t.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 =
      s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 := by
  apply BitVec.eq_of_toNat_eq
  exact wd_frame h.frame fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)

theorem Keep.sign {base : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.Arm.Keep base s t) :
    t.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 =
      s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 := (IKeep.of_keep h).sign

theorem parity_match (x : Nat) (b : Bool) : decide (x % 2 = b.toNat) = ((x % 2 == 1) == b) := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rw [h] <;> cases b <;> decide

theorem recoverParity_ok {s : State} {base : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx base s) (b : Bool)
    (hl : Lim s.mem (State.addr base) FR)
    (hb : s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 = BitVec.ofNat 32 b.toNat) :
    WP isa (.block recoverParity) s fun t => Rest [.r2, .r3, .r9] s t ∧ t.mem = s.mem ∧
      t.z = ((V s.mem (State.addr base) FR % 2 == 1) == b) := by
  refine ldr0_ok hc (by decide) fun s1 u1 => wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
  have r2 : Rest [.r2, .r3, .r9] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  refine ldr0_ok (hc.of_rest r2 (by decide)) (by decide) fun s3 u3 =>
    wp_dp (op2_reg _ _) fun s4 u4 => wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ?_
  have he : (s3.gpr .r9).toNat = V s.mem (State.addr base) FR % 2 := by
    rw [u3.other _ (by decide), u2.gpr]
    change (s1.gpr .r3 &&& (1 : BitVec 32)).toNat = _
    rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod, u1.gpr]
    exact (VG.Proof.Ed25519.Arm.parity_limb hl).symm
  have es : s3.gpr .r2 = BitVec.ofNat 32 b.toNat := by rw [u3.gpr, u2.mem, u1.mem]; exact hb
  refine ⟨r2.trans ((u3.rest (by decide)).trans ((u4.rest (by decide)).trans (ht.rest _))),
    by rw [ht.mem, u4.mem, u3.mem, u2.mem, u1.mem], ?_⟩
  have sub0 : s4.gpr .r9 - (0 : BitVec 32) = s4.gpr .r9 := BitVec.sub_zero _
  rw [hz, sub0, u4.gpr]
  change (s3.gpr .r9 ^^^ s3.gpr .r2 == 0) = _
  rw [← VG.Proof.Ed25519.Arm.parity_match]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  change (s3.gpr .r9 ^^^ s3.gpr .r2 = 0#32) ↔ _
  rw [BitVec.xor_eq_zero_iff]
  have en : (s3.gpr .r2).toNat = b.toNat := by rw [es, toNat_imm (by cases b <;> decide)]
  constructor
  · intro h
    exact he.symm.trans ((congrArg BitVec.toNat h).trans en)
  · intro h
    exact BitVec.eq_of_toNat_eq (he.trans (h.trans en.symm))

end VG.Proof.Ed25519.Arm
end

/-! Choose the encoded sign and finish the extended coordinates. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def recoveredPoint (x y : Spec.X25519.Fe) : Spec.Ed25519.Point := ⟨x, y, 1, x * y⟩
def signedX (x : Spec.X25519.Fe) (b : Bool) : Spec.X25519.Fe :=
  if (x.val % 2 == 1) == b then x else 0 - x

theorem returnFlag_ok (s : State) (b : Bool) :
    WP isa (.block [.mov .r9 (.imm b.toNat)]) s fun t =>
      Rest [.r9] s t ∧ t.mem = s.mem ∧ t.gpr .r9 = BitVec.ofNat 32 b.toNat := by
  refine wp_mov (op2_imm (by cases b <;> decide)) fun t ht => WP.block_nil ⟨ht.rest (by decide), ht.mem, ht.gpr⟩

theorem recoverSuccess_ok {s : State} {base : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx base s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem base) :
    WP isa recoverSuccess s fun t => VG.Proof.Ed25519.Arm.Keep base s t ∧ VG.Proof.Ed25519.Arm.AllLim t.mem base ∧ t.gpr .r9 = 1 ∧
      VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env t.mem base) 0 1 2 3 = VG.Proof.Ed25519.Arm.recoveredPoint (VG.Proof.Ed25519.Arm.env s.mem base 0) (VG.Proof.Ed25519.Arm.env s.mem base 1) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.fieldCode_ok recoverSuccessOps hc hl) fun u ⟨uk, ul, ue⟩ => ?_)
  refine WP.mono (VG.Proof.Ed25519.Arm.returnFlag_ok u true) fun t ⟨tr, tm, tv⟩ => ?_
  refine ⟨uk.trans ⟨tr.mono (by decide), by rw [tm]; exact Frame.refl _ _⟩, tm ▸ ul, tv, ?_⟩
  rw [tm, ue]
  rfl

theorem adjustBranch_ok {s : State} {base : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx base s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem base)
    (b : Bool) (hz : s.z = (((VG.Proof.Ed25519.Arm.env s.mem base 0).val % 2 == 1) == b)) :
    WP isa (.ite .eq (.block []) (fieldCode [.const 5 0, .sub 0 5 0])) s fun t =>
      VG.Proof.Ed25519.Arm.Keep base s t ∧ VG.Proof.Ed25519.Arm.AllLim t.mem base ∧ VG.Proof.Ed25519.Arm.env t.mem base 0 = VG.Proof.Ed25519.Arm.signedX (VG.Proof.Ed25519.Arm.env s.mem base 0) b ∧
      VG.Proof.Ed25519.Arm.env t.mem base 1 = VG.Proof.Ed25519.Arm.env s.mem base 1 := by
  apply WP.ite (((VG.Proof.Ed25519.Arm.env s.mem base 0).val % 2 == 1) == b) (by simp only [VG.Arm.eval, hz])
  · intro h
    exact WP.block_nil ⟨Keep.refl _ _, hl, by simp only [VG.Proof.Ed25519.Arm.signedX, h, ite_true], rfl⟩
  · intro h
    refine WP.mono (VG.Proof.Ed25519.Arm.fieldCode_ok [.const 5 0, .sub 0 5 0] hc hl) fun t ⟨tk, tl, te⟩ => ?_
    refine ⟨tk, tl, ?_, ?_⟩
    · rw [te]
      change 0 - VG.Proof.Ed25519.Arm.env s.mem base 0 = VG.Proof.Ed25519.Arm.signedX (VG.Proof.Ed25519.Arm.env s.mem base 0) b
      simp only [VG.Proof.Ed25519.Arm.signedX, h, Bool.false_eq_true, ite_false]
    · rw [te]; rfl

theorem recoverAdjustSign_ok {s : State} {base : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx base s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem base)
    (b : Bool) (hb : s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 = BitVec.ofNat 32 b.toNat) :
    WP isa recoverAdjustSign s fun t => VG.Proof.Ed25519.Arm.Keep base s t ∧ VG.Proof.Ed25519.Arm.AllLim t.mem base ∧ t.gpr .r9 = 1 ∧
      VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env t.mem base) 0 1 2 3 = VG.Proof.Ed25519.Arm.recoveredPoint (VG.Proof.Ed25519.Arm.signedX (VG.Proof.Ed25519.Arm.env s.mem base 0) b) (VG.Proof.Ed25519.Arm.env s.mem base 1) := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.Arm.freeze_ok hc hl 0) fun a ⟨ak, al, ae, af, av⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.Arm.recoverParity_ok (ak.ctx hc) b af (ak.sign.trans hb)) fun c ⟨cr, cm, cz⟩ => ?_
  have ck : VG.Proof.Ed25519.Arm.Keep base s c := ak.trans ⟨cr.mono (by decide), by rw [cm]; exact Frame.refl _ _⟩
  have ce : VG.Proof.Ed25519.Arm.env c.mem base = VG.Proof.Ed25519.Arm.env s.mem base := (congrArg (fun m => VG.Proof.Ed25519.Arm.env m base) cm).trans ae
  have ch : c.z = (((VG.Proof.Ed25519.Arm.env c.mem base 0).val % 2 == 1) == b) := by rw [cz, av, ce]
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.adjustBranch_ok (ck.ctx hc) (cm ▸ al) b ch) fun d ⟨dk, dl, dx, dy⟩ => ?_)
  refine WP.mono (VG.Proof.Ed25519.Arm.recoverSuccess_ok ((ck.trans dk).ctx hc) dl) fun t ⟨tk, tl, tr, tp⟩ => ?_
  exact ⟨(ck.trans dk).trans tk, tl, tr, by rw [tp, dx, dy, ce]⟩

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.RecoverSign`. -/
section

/-! Reject negative zero and otherwise return the selected sign. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def DecodeResult (base : BitVec 32) (p : Option Spec.Ed25519.Point) (s : State) : Prop :=
  match p with
  | none => s.gpr .r9 = 0
  | some p => s.gpr .r9 = 1 ∧ VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env s.mem base) 0 1 2 3 = p

def signResult (x y : Spec.X25519.Fe) (b : Bool) : Option Spec.Ed25519.Point :=
  if x = 0 && b then none else some (VG.Proof.Ed25519.Arm.recoveredPoint (VG.Proof.Ed25519.Arm.signedX x b) y)

theorem recoverInvalid_ok (s : State) (base : BitVec 32) :
    WP isa recoverInvalid s fun t => VG.Proof.Ed25519.Arm.Keep base s t ∧ t.mem = s.mem ∧ VG.Proof.Ed25519.Arm.DecodeResult base none t :=
  WP.mono (VG.Proof.Ed25519.Arm.returnFlag_ok s false) fun _ ⟨tr, tm, tv⟩ =>
    ⟨⟨tr.mono (by decide), by rw [tm]; exact Frame.refl _ _⟩, tm, tv⟩

theorem signTest_ok {s : State} {base : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx base s) (b : Bool)
    (hb : s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 = BitVec.ofNat 32 b.toNat) :
    WP isa (.block signTest) s fun t => Rest [.r3] s t ∧ t.mem = s.mem ∧ t.z = !b := by
  refine ldr0_ok hc (by decide) fun u hu => wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ?_
  refine ⟨(hu.rest (by decide)).trans (ht.rest _), by rw [ht.mem, hu.mem], ?_⟩
  rw [hz, hu.gpr, hb]
  cases b <;> rfl

theorem recoverSign_ok {s : State} {base : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx base s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem base)
    (b : Bool) (hb : s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 = BitVec.ofNat 32 b.toNat) :
    WP isa recoverSign s fun t => VG.Proof.Ed25519.Arm.Keep base s t ∧ VG.Proof.Ed25519.Arm.AllLim t.mem base ∧
      VG.Proof.Ed25519.Arm.DecodeResult base (VG.Proof.Ed25519.Arm.signResult (VG.Proof.Ed25519.Arm.env s.mem base 0) (VG.Proof.Ed25519.Arm.env s.mem base 1) b) t := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.fieldZero_ok hc hl 0) fun a ⟨ak, al, ae, az⟩ => ?_)
  apply WP.ite (decide (VG.Proof.Ed25519.Arm.env s.mem base 0 = 0)) (by simp only [VG.Arm.eval, az])
  · intro hzero
    have hz : VG.Proof.Ed25519.Arm.env s.mem base 0 = 0 := of_decide_eq_true hzero
    refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.signTest_ok (ak.ctx hc) b (ak.sign.trans hb)) fun c ⟨cr, cm, cz⟩ => ?_)
    have ck : VG.Proof.Ed25519.Arm.Keep base s c := ak.trans ⟨cr.mono (by decide), by rw [cm]; exact Frame.refl _ _⟩
    have cl : VG.Proof.Ed25519.Arm.AllLim c.mem base := cm ▸ al
    have ce : VG.Proof.Ed25519.Arm.env c.mem base = VG.Proof.Ed25519.Arm.env s.mem base := (congrArg (fun m => VG.Proof.Ed25519.Arm.env m base) cm).trans ae
    apply WP.ite b (by simp only [VG.Arm.eval, cz, Bool.not_not])
    · intro ht
      refine WP.mono (VG.Proof.Ed25519.Arm.recoverInvalid_ok c base) fun t ⟨tk, tm, tr⟩ => ?_
      refine ⟨ck.trans tk, tm ▸ cl, ?_⟩
      simpa only [VG.Proof.Ed25519.Arm.signResult, hz, ht, decide_true, Bool.and_self, ite_true] using tr
    · intro hf
      refine WP.mono (VG.Proof.Ed25519.Arm.recoverAdjustSign_ok (ck.ctx hc) cl b (ck.sign.trans hb)) fun t ⟨tk, tl, tr, tv⟩ => ?_
      refine ⟨ck.trans tk, tl, ?_⟩
      simp only [VG.Proof.Ed25519.Arm.signResult, hf, Bool.and_false, Bool.false_eq_true, ite_false, VG.Proof.Ed25519.Arm.DecodeResult]
      exact ⟨tr, by rw [tv, ce, hf]⟩
  · intro hnonzero
    have hn : VG.Proof.Ed25519.Arm.env s.mem base 0 ≠ 0 := of_decide_eq_false hnonzero
    refine WP.mono (VG.Proof.Ed25519.Arm.recoverAdjustSign_ok (ak.ctx hc) al b (ak.sign.trans hb)) fun t ⟨tk, tl, tr, tv⟩ => ?_
    refine ⟨ak.trans tk, tl, ?_⟩
    simp only [VG.Proof.Ed25519.Arm.signResult, hn, decide_false, Bool.false_and, Bool.false_eq_true, ite_false, VG.Proof.Ed25519.Arm.DecodeResult]
    exact ⟨tr, by rw [tv, ae]⟩

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.PointEqual`. -/
section

/-! Compare points exactly as the reviewed verification equation does. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

theorem equalOps_eval (e : VG.Proof.Ed25519.Arm.Env) :
    VG.Proof.Ed25519.Arm.evalOps pointEqualOps e 8 = e 0 * e 6 ∧ VG.Proof.Ed25519.Arm.evalOps pointEqualOps e 9 = e 4 * e 2 ∧
    VG.Proof.Ed25519.Arm.evalOps pointEqualOps e 10 = e 1 * e 6 ∧ VG.Proof.Ed25519.Arm.evalOps pointEqualOps e 11 = e 5 * e 2 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem pointEqual_ok {s : State} {base : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx base s) (hl : VG.Proof.Ed25519.Arm.AllLim s.mem base) :
    WP isa Impl.Ed25519.Arm.pointEqual s fun t => VG.Proof.Ed25519.Arm.Keep base s t ∧ VG.Proof.Ed25519.Arm.AllLim t.mem base ∧
      t.gpr .r9 = BitVec.ofNat 32 (Spec.Ed25519.pointEqual (VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env s.mem base) 0 1 2 3)
        (VG.Proof.Ed25519.Arm.point (VG.Proof.Ed25519.Arm.env s.mem base) 4 5 6 7)).toNat := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.fieldCode_ok pointEqualOps hc hl) fun a ⟨ka, la, va⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.fieldEqual_ok (ka.ctx hc) la 8 9) fun b ⟨kb, lb, be, bz⟩ => ?_)
  have kab := ka.trans kb
  have bx : b.z = decide (VG.Proof.Ed25519.Arm.env s.mem base 0 * VG.Proof.Ed25519.Arm.env s.mem base 6 = VG.Proof.Ed25519.Arm.env s.mem base 4 * VG.Proof.Ed25519.Arm.env s.mem base 2) := by
    rw [bz, va, (VG.Proof.Ed25519.Arm.equalOps_eval _).1, (VG.Proof.Ed25519.Arm.equalOps_eval _).2.1]
  apply WP.ite _ (congrArg some bx)
  · intro htx
    have hx := of_decide_eq_true htx
    refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.fieldEqual_ok (kab.ctx hc) lb 10 11) fun c ⟨kc, lc, _, cz⟩ => ?_)
    have cy : c.z = decide (VG.Proof.Ed25519.Arm.env s.mem base 1 * VG.Proof.Ed25519.Arm.env s.mem base 6 = VG.Proof.Ed25519.Arm.env s.mem base 5 * VG.Proof.Ed25519.Arm.env s.mem base 2) := by
      rw [cz, be 10 (by decide), be 11 (by decide), va, (VG.Proof.Ed25519.Arm.equalOps_eval _).2.2.1, (VG.Proof.Ed25519.Arm.equalOps_eval _).2.2.2]
    apply WP.ite _ (congrArg some cy)
    · intro hty
      have hy := of_decide_eq_true hty
      refine WP.mono (VG.Proof.Ed25519.Arm.returnFlag_ok c true) fun t ⟨tr, tm, tv⟩ => ?_
      refine ⟨(kab.trans kc).trans ⟨tr.mono (by decide), by rw [tm]; exact Frame.refl _ _⟩, tm ▸ lc, ?_⟩
      simpa only [Spec.Ed25519.pointEqual, VG.Proof.Ed25519.Arm.point, hx, hy, beq_self_eq_true, Bool.and_self] using tv
    · intro hfy
      have hy := of_decide_eq_false hfy
      refine WP.mono (VG.Proof.Ed25519.Arm.recoverInvalid_ok c base) fun t ⟨kt, tm, tr⟩ => ?_
      refine ⟨(kab.trans kc).trans kt, tm ▸ lc, ?_⟩
      simp only [Spec.Ed25519.pointEqual, VG.Proof.Ed25519.Arm.point, hx, beq_self_eq_true, beq_eq_false_iff_ne.mpr hy,
        Bool.and_false, Bool.toNat_false]
      exact tr
  · intro hfx
    have hx := of_decide_eq_false hfx
    refine WP.mono (VG.Proof.Ed25519.Arm.recoverInvalid_ok b base) fun t ⟨kt, tm, tr⟩ => ?_
    refine ⟨kab.trans kt, tm ▸ lb, ?_⟩
    simp only [Spec.Ed25519.pointEqual, VG.Proof.Ed25519.Arm.point, beq_eq_false_iff_ne.mpr hx, Bool.false_and, Bool.toNat_false]
    exact tr

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.ScalarABI`. -/
section

/-! Saving and restoring the callee-saved registers in the reviewed scratch buffer. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

/-- The registers `g` saved at `[0, 32)` of the working space at `B`. -/
def ScalarSaved (B : Addr) (g : Reg → BitVec 32) (m : Mem) : Prop :=
  ∀ i < 8, m.readW (B + BitVec.ofNat 64 (4 * i)) 32 = g (scalarSavedReg i)

section
variable {b : BitVec 32}

theorem scalarSave_ok {s : State} {base : Reg} (h3 : s.gpr base = b) (hfit : b.toNat + 8192 ≤ 2 ^ 32)
    (hw : (⟨State.addr b, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block (scalarSave base)) s fun s' =>
      VG.Proof.Ed25519.Arm.ScalarSaved (State.addr b) s.gpr s'.mem ∧ Frame [⟨State.addr b, 32⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧
        Rest [] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ i < n, s'.mem.readW (State.addr b + BitVec.ofNat 64 (4 * i)) 32 = s.gpr (scalarSavedReg i)) ∧
      Frame [⟨State.addr b, 4 * n⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ Rest [] s s')
    (fun n s' hn ⟨h1, h2, h3', h4⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, rfl, Rest.refl _ _⟩)
    fun s' h => ⟨h.1, h.2.1, h.2.2⟩
  refine wp_str (a := State.addr b + BitVec.ofNat 64 (4 * n)) (by omega)
    (by rw [h3', h3]; exact addr_add (by omega)) (by rw [h4.wr]; exact in_base hw (by omega) (by omega))
    fun s2 u2 => WP.block_nil ⟨fun i hi => ?_, ?_, by rw [u2.gpr, h3'], h4.trans (u2.rest _)⟩
  · rw [u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]; exact h1 i hi
    · rw [Mem.readW_writeW_self32, h3']
  · rw [u2.mem]
    exact (h2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

theorem scalarRestore_ok {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) {g : Reg → BitVec 32} (hs : VG.Proof.Ed25519.Arm.ScalarSaved (State.addr b) g s.mem) :
    WP isa (.block scalarRestore) s fun s' => (∀ i < 8, s'.gpr (scalarSavedReg i) = g (scalarSavedReg i)) ∧
      Rest [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s s' ∧ s'.mem = s.mem := by
  have hsr : ∀ i < 8, scalarSavedReg i ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] := by decide
  have hinj : ∀ i < 8, ∀ j < 8, scalarSavedReg i = scalarSavedReg j → i = j := by decide
  have h0 : ∀ i < 8, scalarSavedReg i ≠ .r0 := by decide
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ i < n, s'.gpr (scalarSavedReg i) = g (scalarSavedReg i)) ∧
      Rest [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s s' ∧ s'.mem = s.mem)
    (fun n s' hn ⟨hl, hr, hm⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Rest.refl _ _, rfl⟩) fun s' h => h
  refine ldr0_ok (hc.of_rest hr (by decide)) (d := 4 * n) (by omega) fun s1 u1 =>
    WP.block_nil ⟨fun i hi => ?_, hr.trans (u1.rest (hsr n hn)), by rw [u1.mem, hm]⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | rfl
  · rw [u1.other _ (fun e => absurd (hinj _ (by omega) _ hn e) (by omega))]; exact hl i h'
  · rw [u1.gpr, hm, hs i hn]

/-- The saved registers stay where no code writes. -/
theorem ScalarSaved.frame {g : Reg → BitVec 32} {m m' : Mem} (hs : VG.Proof.Ed25519.Arm.ScalarSaved (State.addr b) g m) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, ∀ i < 8, Region.Disjoint ⟨State.addr b + BitVec.ofNat 64 (4 * i), 4⟩ r) :
    VG.Proof.Ed25519.Arm.ScalarSaved (State.addr b) g m' := fun i hi => by
  rw [hf.readW (Region.contains_self _ _) (fun r hr => hd r hr i hi) (by decide)]; exact hs i hi

end

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.ScalarCodec`. -/
section

/-! Compact 16-bit limbs use the scalar specification's exact byte encoding. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

theorem scalar_packed_decode (m : Mem) (p : Addr) :
    Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p 32) = VG.Proof.Ed25519.Arm.packedV m p := by
  rw [decodeLE_eq]
  exact VG.Proof.Ed25519.Arm.leNum_bytesAt2 m p 16

theorem scalar_packed_encode (m : Mem) (p : Addr) :
    Spec.Ed25519.bytesAt m p 32 = Spec.Ed25519.encodeLE 32 (VG.Proof.Ed25519.Arm.packedV m p) := by
  have h := VG.Proof.X25519.bytesAt_leBytes m p 32
  rw [← VG.Proof.X25519.leNum_bytesAt_read, VG.Proof.Ed25519.Arm.leNum_bytesAt2 m p 16] at h
  change Spec.Ed25519.bytesAt m p 32 = VG.Proof.X25519.leBytes 32 (VG.Proof.Ed25519.Arm.packedV m p) at h
  rw [h]
  simp only [Spec.Ed25519.encodeLE, VG.Proof.X25519.leBytes, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

end VG.Proof.Ed25519.Arm

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.RecoverPoint`. -/
section

/-! Merged from `Proof.Ed25519.Arm.RecoverCandidate`. -/
section
/-! Candidate root and its square check agree with the decoding specification. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

private theorem recoverInit_eval (e : Env) :
    evalOps recoverInitOps e 1 = e 1 ∧
    evalOps recoverInitOps e 6 = rootU (e 1) ∧
    evalOps recoverInitOps e 7 = rootV (e 1) ∧
    evalOps recoverInitOps e 9 = Spec.X25519.pow (rootV (e 1)) 3 ∧
    evalOps recoverInitOps e 2 = rootU (e 1) * Spec.X25519.pow (rootV (e 1)) 7 := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · exact pow_three _
  · exact congrArg (rootU (e 1) * ·) (pow_seven _)

private theorem recoverFinish_eval (e : Env) :
    evalOps recoverFinishOps e 0 = e 6 * e 9 * e 15 ∧
    evalOps recoverFinishOps e 1 = e 1 ∧
    evalOps recoverFinishOps e 5 = 0 ∧
    evalOps recoverFinishOps e 6 = e 6 ∧
    evalOps recoverFinishOps e 7 = e 7 ∧
    evalOps recoverFinishOps e 11 = e 7 * (e 6 * e 9 * e 15) * (e 6 * e 9 * e 15) ∧
    evalOps recoverFinishOps e 12 = 0 - e 6 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem rootEnv_low (e : Env) (i : Slot) (hi : i.val < 14) : rootEnv e i = e i := by
  have h14 : i ≠ 14 := by intro h; have := congrArg Fin.val h; omega
  have h15 : i ≠ 15 := by intro h; have := congrArg Fin.val h; omega
  have h16 : i ≠ 16 := by intro h; have := congrArg Fin.val h; omega
  have h17 : i ≠ 17 := by intro h; have := congrArg Fin.val h; omega
  simp only [rootEnv, power250Env, VG.Proof.Ed25519.Arm.opMul, opSqn, Function.update_of_ne h14,
    Function.update_of_ne h15, Function.update_of_ne h16, Function.update_of_ne h17]

theorem recoverCandidate_ok {s : State} {base : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx base s) (hl : AllLim s.mem base) :
    WP isa recoverCandidate s fun t => IKeep base s t ∧ AllLim t.mem base ∧
      VG.Proof.Ed25519.Arm.env t.mem base 0 = rootX (VG.Proof.Ed25519.Arm.env s.mem base 1) ∧
      VG.Proof.Ed25519.Arm.env t.mem base 1 = VG.Proof.Ed25519.Arm.env s.mem base 1 ∧
      VG.Proof.Ed25519.Arm.env t.mem base 5 = 0 ∧ VG.Proof.Ed25519.Arm.env t.mem base 6 = rootU (VG.Proof.Ed25519.Arm.env s.mem base 1) ∧
      VG.Proof.Ed25519.Arm.env t.mem base 7 = rootV (VG.Proof.Ed25519.Arm.env s.mem base 1) ∧
      VG.Proof.Ed25519.Arm.env t.mem base 11 = rootV (VG.Proof.Ed25519.Arm.env s.mem base 1) * rootX (VG.Proof.Ed25519.Arm.env s.mem base 1) * rootX (VG.Proof.Ed25519.Arm.env s.mem base 1) ∧
      VG.Proof.Ed25519.Arm.env t.mem base 12 = 0 - rootU (VG.Proof.Ed25519.Arm.env s.mem base 1) := by
  refine WP.seq (WP.mono (fieldCode_ok recoverInitOps hc hl) fun a ⟨ka, la, va⟩ => ?_)
  refine WP.seq (WP.mono (rootPower_spec base a (ka.ctx hc) la) fun b ⟨kb, lb, vb⟩ => ?_)
  have be : ∀ i : Slot, i.val < 14 → VG.Proof.Ed25519.Arm.env b.mem base i = VG.Proof.Ed25519.Arm.env a.mem base i := by
    intro i hi
    rw [vb, rootEnv_low _ i hi]
  refine WP.mono (fieldCode_ok recoverFinishOps (kb.ctx (ka.ctx hc)) lb) fun t ⟨kt, lt, vt⟩ => ?_
  have ay := (recoverInit_eval (VG.Proof.Ed25519.Arm.env s.mem base)).1
  have au := (recoverInit_eval (VG.Proof.Ed25519.Arm.env s.mem base)).2.1
  have av := (recoverInit_eval (VG.Proof.Ed25519.Arm.env s.mem base)).2.2.1
  have av3 := (recoverInit_eval (VG.Proof.Ed25519.Arm.env s.mem base)).2.2.2.1
  have az := (recoverInit_eval (VG.Proof.Ed25519.Arm.env s.mem base)).2.2.2.2
  have bx : VG.Proof.Ed25519.Arm.env b.mem base 6 * VG.Proof.Ed25519.Arm.env b.mem base 9 * VG.Proof.Ed25519.Arm.env b.mem base 15 = rootX (VG.Proof.Ed25519.Arm.env s.mem base 1) := by
    rw [be 6 (by decide), be 9 (by decide), vb, rootEnv_eval, rootPower_eq, va, au, av3, az]
    rfl
  refine ⟨(IKeep.of_keep ka).trans (kb.trans (IKeep.of_keep kt)), lt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [vt, (recoverFinish_eval _).1, bx]
  · rw [vt, (recoverFinish_eval _).2.1, be 1 (by decide), va, ay]
  · rw [vt, (recoverFinish_eval _).2.2.1]
  · rw [vt, (recoverFinish_eval _).2.2.2.1, be 6 (by decide), va, au]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.1, be 7 (by decide), va, av]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.2.1, bx, be 7 (by decide), va, av]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.2.2, be 6 (by decide), va, au]

end VG.Proof.Ed25519.Arm
end

/-! Candidate validation implements RFC 8032 recovery exactly. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

def recoverResult (y : Spec.X25519.Fe) (b : Bool) : Option Spec.Ed25519.Point :=
  if rootV y * rootX y * rootX y = rootU y then signResult (rootX y) y b
  else if rootV y * rootX y * rootX y = 0 - rootU y then signResult (rootX y * Spec.Ed25519.sqrtM1) y b
  else none

private theorem signResult_map (x y : Spec.X25519.Fe) (b : Bool) :
    signResult x y b = (do
      let z ← some x
      if z = 0 && b then none else some (signedX z b)).map (fun z => recoveredPoint z y) := by
  unfold signResult
  change (if x = 0 && b then none else some (recoveredPoint (signedX x b) y)) =
    (if x = 0 && b then none else some (signedX x b)).map (fun z => recoveredPoint z y)
  split <;> rfl

theorem recoverResult_spec (y : Spec.X25519.Fe) (b : Bool) :
    recoverResult y b = (Spec.Ed25519.recoverX y b).map (fun x => recoveredPoint x y) := by
  unfold recoverResult Spec.Ed25519.recoverX
  change (if rootV y * rootX y * rootX y = rootU y then signResult (rootX y) y b
    else if rootV y * rootX y * rootX y = 0 - rootU y then signResult (rootX y * Spec.Ed25519.sqrtM1) y b else none) =
    (if rootV y * rootX y * rootX y = rootU y then (do
        let z ← some (rootX y)
        if z = 0 && b then none else some (signedX z b))
      else if rootV y * rootX y * rootX y = 0 - rootU y then (do
        let z ← some (rootX y * Spec.Ed25519.sqrtM1)
        if z = 0 && b then none else some (signedX z b))
      else none).map (fun x => recoveredPoint x y)
  by_cases h : rootV y * rootX y * rootX y = rootU y
  · rw [ite_eq_left h, ite_eq_left h]
    exact signResult_map _ _ _
  · rw [ite_eq_right h, ite_eq_right h]
    by_cases h' : rootV y * rootX y * rootX y = 0 - rootU y
    · rw [ite_eq_left h', ite_eq_left h']
      exact signResult_map _ _ _
    · rw [ite_eq_right h', ite_eq_right h']
      rfl


private theorem sign_known {s : State} {base : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx base s) (hl : AllLim s.mem base)
    (b : Bool) (hb : s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 = BitVec.ofNat 32 b.toNat)
    (x y : Spec.X25519.Fe) (hx : VG.Proof.Ed25519.Arm.env s.mem base 0 = x) (hy : VG.Proof.Ed25519.Arm.env s.mem base 1 = y) :
    WP isa recoverSign s fun t => IKeep base s t ∧ AllLim t.mem base ∧ DecodeResult base (signResult x y b) t := by
  refine WP.mono (recoverSign_ok hc hl b hb) fun t ⟨tk, tl, tr⟩ => ?_
  exact ⟨IKeep.of_keep tk, tl, by rw [hx, hy] at tr; exact tr⟩

theorem recoverPoint_ok {s : State} {base : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx base s) (hl : AllLim s.mem base)
    (b : Bool) (hb : s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 = BitVec.ofNat 32 b.toNat) :
    WP isa recoverPoint s fun t => IKeep base s t ∧ AllLim t.mem base ∧
      DecodeResult base ((Spec.Ed25519.recoverX (VG.Proof.Ed25519.Arm.env s.mem base 1) b).map
        (fun x => recoveredPoint x (VG.Proof.Ed25519.Arm.env s.mem base 1))) t := by
  rw [← recoverResult_spec, recoverPoint]
  refine WP.seq (WP.mono (recoverCandidate_ok hc hl) fun a ⟨ka, la, ax, ay, _, au, _, avx, anu⟩ => ?_)
  refine WP.seq (WP.mono (fieldEqual_ok (ka.ctx hc) la 11 6) fun c ⟨kc, lc, ce, cz⟩ => ?_)
  have kac := ka.trans (IKeep.of_keep kc)
  have cx : VG.Proof.Ed25519.Arm.env c.mem base 0 = rootX (VG.Proof.Ed25519.Arm.env s.mem base 1) := (ce 0 (by decide)).trans ax
  have cy : VG.Proof.Ed25519.Arm.env c.mem base 1 = VG.Proof.Ed25519.Arm.env s.mem base 1 := (ce 1 (by decide)).trans ay
  apply WP.ite (decide (rootV (VG.Proof.Ed25519.Arm.env s.mem base 1) * rootX (VG.Proof.Ed25519.Arm.env s.mem base 1) * rootX (VG.Proof.Ed25519.Arm.env s.mem base 1) =
    rootU (VG.Proof.Ed25519.Arm.env s.mem base 1))) (by simp only [VG.Arm.eval, cz, avx, au])
  · intro ht
    have ht' := of_decide_eq_true ht
    refine WP.mono (sign_known (kac.ctx hc) lc b (kac.sign.trans hb) _ _ cx cy) fun t ⟨kt, lt, tr⟩ => ?_
    exact ⟨kac.trans kt, lt, by simpa only [recoverResult, ht', ite_true] using tr⟩
  · intro hf
    have hf' := of_decide_eq_false hf
    refine WP.seq (WP.mono (fieldEqual_ok (kac.ctx hc) lc 11 12) fun d ⟨kd, ld, de, dz⟩ => ?_)
    have kacd := kac.trans (IKeep.of_keep kd)
    have dx : VG.Proof.Ed25519.Arm.env d.mem base 0 = rootX (VG.Proof.Ed25519.Arm.env s.mem base 1) := (de 0 (by decide)).trans cx
    have dy : VG.Proof.Ed25519.Arm.env d.mem base 1 = VG.Proof.Ed25519.Arm.env s.mem base 1 := (de 1 (by decide)).trans cy
    apply WP.ite (decide (rootV (VG.Proof.Ed25519.Arm.env s.mem base 1) * rootX (VG.Proof.Ed25519.Arm.env s.mem base 1) * rootX (VG.Proof.Ed25519.Arm.env s.mem base 1) =
      0 - rootU (VG.Proof.Ed25519.Arm.env s.mem base 1))) (by simp only [VG.Arm.eval, dz, ce 11 (by decide), ce 12 (by decide), avx, anu])
    · intro ht
      have ht' := of_decide_eq_true ht
      refine WP.seq (WP.mono (fieldCode_ok [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18] (kacd.ctx hc) ld)
        fun e ⟨ke, le, ve⟩ => ?_)
      have ex : VG.Proof.Ed25519.Arm.env e.mem base 0 = rootX (VG.Proof.Ed25519.Arm.env s.mem base 1) * Spec.Ed25519.sqrtM1 := by
        rw [ve]; change VG.Proof.Ed25519.Arm.env d.mem base 0 * Spec.Ed25519.sqrtM1 = _; rw [dx]
      have ey : VG.Proof.Ed25519.Arm.env e.mem base 1 = VG.Proof.Ed25519.Arm.env s.mem base 1 := by rw [ve]; exact dy
      have kacde := kacd.trans (IKeep.of_keep ke)
      refine WP.mono (sign_known (kacde.ctx hc) le b (kacde.sign.trans hb) _ _ ex ey) fun t ⟨kt, lt, tr⟩ => ?_
      exact ⟨kacde.trans kt, lt, by rw [recoverResult, ite_eq_right hf', ite_eq_left ht']; exact tr⟩
    · intro hf2
      have hf2' := of_decide_eq_false hf2
      refine WP.mono (recoverInvalid_ok d base) fun t ⟨kt, tm, tr⟩ => ?_
      exact ⟨kacd.trans (IKeep.of_keep kt), tm ▸ ld,
        by simpa only [recoverResult, hf', hf2', ite_false] using tr⟩

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseVerified`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.DecodeCTLit`. -/
section

namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm
materialize_code recoverCandidate
materialize_code pointDecodeLoad
materialize_code recoverSuccess
materialize_code equal116CT := fieldEqual 11 6
materialize_code equal1112CT := fieldEqual 11 12
materialize_code equal89CT := fieldEqual 8 9
materialize_code equal1011CT := fieldEqual 10 11
materialize_code equalOpsCT := fieldCode pointEqualOps
materialize_code zero0CT := fieldZero 0
materialize_code parityCT := (.block (freeze 0 ++ recoverParity) : Prog isa)
materialize_code negateCT := fieldCode [.const 5 0, .sub 0 5 0]
materialize_code rootAdjustCT := fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18]
end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.MulKeep`. -/
section

/-! Merged from `Proof.Ed25519.Arm.PointPowersLoop`. -/
section
/-! Checkpoint-loop termination and exact table contents. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

structure PowersInv (s₀ : State) (b : BitVec 32) (o count n : Nat) (batch : Bool) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ count
  ctx : VG.Proof.Ed25519.Arm.Ctx b s
  lim : AllLim s.mem b
  counter : s.gpr .r11 = BitVec.ofNat 32 (count - n)
  value : point (env s.mem b) 0 1 2 3 =
    powerPoint (point (env s₀.mem b) 0 1 2 3) (powerStride batch * (count - n))
  table : ∀ j < count - n, tablePoint s.mem b (o + 128 * j) =
    powerPoint (point (env s₀.mem b) 0 1 2 3) (powerStride batch * j)
  high : ∀ i : Slot, 16 ≤ i.val → env s.mem b i = env s₀.mem b i
  keep : PowersKeep b o (128 * count) s₀ s

theorem powersLoop_ok (batch : Bool) {s₀ : State} {b : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx b s₀)
    (hl : AllLim s₀.mem b) (o count : Nat) (hlo : 1600 ≤ o) (hbound : o + 128 * count ≤ 8192)
    (hn0 : 0 < count) (hn : count ≤ 32) (h11 : s₀.gpr .r11 = 0)
    (hd : env s₀.mem b 16 = Spec.Ed25519.d) :
    WP isa (.loop (powersBody o count batch) .ne) s₀ fun t => AllLim t.mem b ∧
      (∀ j < count, tablePoint t.mem b (o + 128 * j) =
        powerPoint (point (env s₀.mem b) 0 1 2 3) (powerStride batch * j)) ∧
      point (env t.mem b) 0 1 2 3 = powerPoint (point (env s₀.mem b) 0 1 2 3) (powerStride batch * count) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s₀.mem b i) ∧
      PowersKeep b o (128 * count) s₀ t := by
  apply WP.loop (fun n => VG.Proof.Ed25519.Arm.PowersInv s₀ b o count n batch) (n := count)
  · intro n s hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hi.positive; omega : n ≠ 0)
    have hk : k < count := by have := hi.bound; omega
    refine WP.mono (powersBody_ok batch hi.ctx hi.lim o (count - (k + 1)) count hlo hbound
      (by omega) hn hi.counter ((hi.high 16 (by decide)).trans hd))
      fun t ⟨htc, htz, htl, htt, htv, hthi, htk⟩ => ?_
    have hstep : count - (k + 1) + 1 = count - k := by omega
    have hv : point (env t.mem b) 0 1 2 3 =
        powerPoint (point (env s₀.mem b) 0 1 2 3) (powerStride batch * (count - k)) := by
      rw [htv, hi.value, ← powerPoint_add]
      exact congrArg (powerPoint _) (by
        cases batch <;> simp only [powerStride, Bool.false_eq_true, ite_true, ite_false] <;> omega)
    have ht : ∀ j < count - k, tablePoint t.mem b (o + 128 * j) =
        powerPoint (point (env s₀.mem b) 0 1 2 3) (powerStride batch * j) := by
      intro j hj
      by_cases h : j < count - (k + 1)
      · rw [TableFrame.point htk.frame (by omega) (.inl (by omega)) (by omega) (by omega), hi.table j h]
      · have he : j = count - (k + 1) := by omega
        rw [he, htt, hi.value]
    have hh : ∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s₀.mem b i :=
      fun i h => (hthi i h).trans (hi.high i h)
    have hkeep := hi.keep.trans (htk.mono (by omega) (by omega))
    by_cases hk0 : k = 0
    · subst hk0
      exact .inl ⟨by simp only [VG.Arm.eval, htz, show count - (0 + 1) + 1 = count by omega,
        decide_true, Bool.not_true], htl, ht, hv, hh, hkeep⟩
    · exact .inr ⟨by simp only [VG.Arm.eval, htz,
        decide_eq_false (show count - (k + 1) + 1 ≠ count by omega), Bool.not_false],
        k, by omega, ⟨by omega, by omega, htk.ctx hi.ctx, htl, hstep ▸ htc, hv, ht, hh, hkeep⟩⟩
  · refine ⟨hn0, Nat.le_refl _, hc, hl, ?_, ?_, ?_, fun _ _ => rfl, PowersKeep.refl _ _ _ _⟩
    · rw [Nat.sub_self]; exact h11
    · simp only [Nat.sub_self, Nat.mul_zero, powerPoint]
    · intro j hj; omega

theorem pointPowers_ok (batch : Bool) {s : State} {b : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx b s)
    (hl : AllLim s.mem b) (o count : Nat) (hlo : 1600 ≤ o) (hbound : o + 128 * count ≤ 8192)
    (hn0 : 0 < count) (hn : count ≤ 32) (hd : env s.mem b 16 = Spec.Ed25519.d) :
    WP isa (pointPowers o count batch) s fun t => AllLim t.mem b ∧
      (∀ j < count, tablePoint t.mem b (o + 128 * j) =
        powerPoint (point (env s.mem b) 0 1 2 3) (powerStride batch * j)) ∧
      point (env t.mem b) 0 1 2 3 = powerPoint (point (env s.mem b) 0 1 2 3) (powerStride batch * count) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s.mem b i) ∧ PowersKeep b o (128 * count) s t := by
  refine WP.seq (wp_movw fun t ht => WP.block_nil ?_)
  have hr : Rest [.r11] s t := ht.rest (by decide)
  refine WP.mono (VG.Proof.Ed25519.Arm.powersLoop_ok batch (hc.of_rest hr (by decide)) (by rw [ht.mem]; exact hl)
    o count hlo hbound hn0 hn ht.gpr (by rw [ht.mem]; exact hd)) fun u ⟨hlu, htu, hv, hh, hu⟩ => ?_
  have hkeep : PowersKeep b o (128 * count) s t :=
    ⟨hr.mono (by decide), by rw [ht.mem]; exact Frame.refl _ _⟩
  rw [ht.mem] at htu hv hh
  exact ⟨hlu, htu, hv, hh, hkeep.trans hu⟩

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.PointBatch`. -/
section
/-! Merged from `Proof.Ed25519.Arm.AccumulateLoop`. -/
section
/-! The descending sixteen-bit loop follows the specification exactly. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

structure AccumulateInv (s₀ : State) (b : BitVec 32) (start scalar : Nat)
    (p : Spec.Ed25519.Point) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 16
  ctx : VG.Proof.Ed25519.Arm.Ctx b s
  lim : AllLim s.mem b
  counter : s.gpr .r11 = BitVec.ofNat 32 n
  d : env s.mem b 16 = Spec.Ed25519.d
  value : point (env s.mem b) 0 1 2 3 = after scalar p (start + n)
  bits : ∀ i < 16, s.mem (State.addr b + BitVec.ofNat 64 (32 + i)) =
    BitVec.ofNat 8 (VG.Proof.Ed25519.Arm.scalarBit scalar (start + i)).toNat
  table : ∀ i < 16, tablePoint s.mem b (5696 + 128 * i) = powerPoint p (start + i)
  keep : LoopKeep b s₀ s

theorem accumulateLoop_ok {s₀ : State} {b : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx b s₀) (hl : AllLim s₀.mem b)
    (start scalar : Nat) (p : Spec.Ed25519.Point) (h11 : s₀.gpr .r11 = 16)
    (hb : ∀ i < 16, s₀.mem (State.addr b + BitVec.ofNat 64 (32 + i)) =
      BitVec.ofNat 8 (VG.Proof.Ed25519.Arm.scalarBit scalar (start + i)).toNat)
    (hd : env s₀.mem b 16 = Spec.Ed25519.d)
    (hp : point (env s₀.mem b) 0 1 2 3 = after scalar p (start + 16))
    (ht : ∀ i < 16, tablePoint s₀.mem b (5696 + 128 * i) = powerPoint p (start + i)) :
    WP isa (.loop accumulateBody .ne) s₀ fun t => AllLim t.mem b ∧
      point (env t.mem b) 0 1 2 3 = after scalar p start ∧ env t.mem b 16 = Spec.Ed25519.d ∧
      LoopKeep b s₀ t := by
  apply WP.loop (VG.Proof.Ed25519.Arm.AccumulateInv s₀ b start scalar p) (n := 16)
  · intro n s h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.positive; omega : n ≠ 0)
    have hk : k < 16 := by have := h.bound; omega
    refine WP.mono (accumulateBody_ok h.ctx h.lim k start scalar p hk h.counter
      (h.bits k hk) h.d (by rw [Nat.add_assoc]; exact h.value) (h.table k hk))
      fun t ⟨tc, tz, tl, tv, td, tk⟩ => ?_
    have hb' : ∀ i < 16, t.mem (State.addr b + BitVec.ofNat 64 (32 + i)) =
        BitVec.ofNat 8 (VG.Proof.Ed25519.Arm.scalarBit scalar (start + i)).toNat :=
      fun i hi => (tk.bit i hi).trans (h.bits i hi)
    have ht' : ∀ i < 16, tablePoint t.mem b (5696 + 128 * i) = powerPoint p (start + i) := by
      intro i hi
      exact (workspace_tablePoint tk.frame (by omega) (by omega)).trans (h.table i hi)
    by_cases hk0 : k = 0
    · subst hk0
      exact .inl ⟨by simp only [VG.Arm.eval, tz, decide_true, Bool.not_true], tl, tv, td, h.keep.trans tk⟩
    · exact .inr ⟨by simp only [VG.Arm.eval, tz, decide_eq_false hk0, Bool.not_false],
        k, by omega, ⟨by omega, by omega, tk.ctx h.ctx, tl, tc, td, tv, hb', ht', h.keep.trans tk⟩⟩
  · exact ⟨by decide, by decide, hc, hl, h11, hd, hp, hb, ht, LoopKeep.refl _ _⟩

theorem accumulate16_ok {s : State} {b : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hl : AllLim s.mem b)
    (start scalar : Nat) (p : Spec.Ed25519.Point)
    (hb : ∀ i < 16, s.mem (State.addr b + BitVec.ofNat 64 (32 + i)) =
      BitVec.ofNat 8 (VG.Proof.Ed25519.Arm.scalarBit scalar (start + i)).toNat)
    (hd : env s.mem b 16 = Spec.Ed25519.d)
    (hp : point (env s.mem b) 0 1 2 3 = after scalar p (start + 16))
    (ht : ∀ i < 16, tablePoint s.mem b (5696 + 128 * i) = powerPoint p (start + i)) :
    WP isa accumulate16 s fun t => AllLim t.mem b ∧
      point (env t.mem b) 0 1 2 3 = after scalar p start ∧ env t.mem b 16 = Spec.Ed25519.d ∧
      LoopKeep b s t := by
  refine WP.seq (wp_movw fun u hu => WP.block_nil ?_)
  have ku : LoopKeep b s u := LoopKeep.of_rest (hu.rest (ws := [.r11]) (by decide)) (by decide) hu.mem
  refine WP.mono (VG.Proof.Ed25519.Arm.accumulateLoop_ok (ku.ctx hc) (by rw [hu.mem]; exact hl) start scalar p hu.gpr
    (by rw [hu.mem]; exact hb) (by rw [hu.mem]; exact hd) (by rw [hu.mem]; exact hp)
    (by rw [hu.mem]; exact ht)) fun t ⟨tl, tv, td, tk⟩ => ?_
  exact ⟨tl, tv, td, ku.trans tk⟩

end VG.Proof.Ed25519.Arm
end

/-! The local table preserves the accumulator and the checkpoint table. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem PowersKeep.of_acc {b : BitVec 32} {o n : Nat} {s t : State} (h : AccKeep b s t) :
    PowersKeep b o n s t := ⟨h.rest.mono (by decide), TableFrame.workspace h.frame⟩
theorem PowersKeep.of_keep {b : BitVec 32} {o n : Nat} {s t : State} (h : Keep b s t) :
    PowersKeep b o n s t := ⟨h.rest.mono (by decide), TableFrame.workspace h.frame⟩

theorem loadCheckpoint_ok {s : State} {b : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hl : AllLim s.mem b)
    (j : Nat) (hj : j < 32) (h11 : s.gpr .r11 = BitVec.ofNat 32 j) :
    WP isa loadCheckpoint s fun t => AccKeep b s t ∧ AllLim t.mem b ∧
      point (env t.mem b) 0 1 2 3 = tablePoint s.mem b (1600 + 128 * j) ∧
      point (env t.mem b) 17 18 19 20 = point (env s.mem b) 0 1 2 3 ∧
      env t.mem b 16 = env s.mem b 16 := by
  refine WP.seq (WP.mono (fieldCode_ok savePointOps hc hl) fun a ⟨ka, la, ea⟩ => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (ka.ctx hc) 1600 j (by omega) hj
    ((ka.rest.gpr _ (by decide)).trans h11)) fun a' ⟨hptr, hr, hm⟩ => ?_
  have ka' : AccKeep b a a' := AccKeep.of_rest hr (by decide) hm
  refine WP.mono (pointFromTable_ok (ka'.ctx (ka.ctx hc)) (by rw [hm]; exact la)
    hptr (by omega) (by omega)) fun t ⟨pt, lt, kt⟩ => ?_
  refine ⟨(AccKeep.of_keep ka).trans (ka'.trans (AccKeep.of_table kt (by decide) (by decide))), lt, ?_, ?_, ?_⟩
  · rw [pt, hm]
    exact workspace_tablePoint ka.frame (by omega) (by omega)
  · rw [point_congr (e := env t.mem b) (f := env a'.mem b) 17 18 19 20
      (kt.high 17 (by decide)) (kt.high 18 (by decide)) (kt.high 19 (by decide)) (kt.high 20 (by decide)),
      hm, ea, savePoint_eval]
  · rw [kt.high 16 (by decide), hm, ea, savePoint_d]

theorem prepareBatch_ok {s : State} {base : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx base s) (hl : AllLim s.mem base)
    (j : Nat) (hj : j < 32) (h11 : s.gpr .r11 = BitVec.ofNat 32 j)
    (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa prepareBatch s fun t => PowersKeep base 5696 2048 s t ∧ AllLim t.mem base ∧
      point (env t.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 ∧
      (∀ i < 16, tablePoint t.mem base (5696 + 128 * i) =
        powerPoint (tablePoint s.mem base (1600 + 128 * j)) i) ∧ env t.mem base 16 = Spec.Ed25519.d := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.loadCheckpoint_ok hc hl j hj h11) fun a ⟨ka, la, ap, av, ad⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.pointPowers_ok false (ka.ctx hc) la 5696 16 (by decide)
    (by decide) (by decide) (by decide) (ad.trans hd)) fun b ⟨lb, bt, _, bh, kb⟩ => ?_)
  refine WP.mono (fieldCode_ok restorePointOps (kb.ctx (ka.ctx hc)) lb) fun t ⟨kt, lt, et⟩ => ?_
  refine ⟨((PowersKeep.of_acc ka).trans kb).trans (PowersKeep.of_keep kt), lt, ?_, ?_, ?_⟩
  · rw [et, restorePoint_eval,
      point_congr (e := env b.mem base) (f := env a.mem base) 17 18 19 20
        (bh 17 (by decide)) (bh 18 (by decide)) (bh 19 (by decide)) (bh 20 (by decide)), av]
  · intro i hi
    have htab := bt i hi
    simp only [powerStride, Bool.false_eq_true, ite_false, Nat.one_mul] at htab
    exact (workspace_tablePoint kt.frame (by omega) (by omega)).trans
      (htab.trans (congrArg (fun p => powerPoint p i) ap))
  · rw [et, restorePoint_d, bh 16 (by decide), ad, hd]

end VG.Proof.Ed25519.Arm
end

/-! Frames for scalar multiplication preserve argument pointers,
register saves, and all data beyond the compact tables. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

abbrev mulRegions (b : BitVec 32) (o n : Nat) : List Region :=
  [⟨State.addr b + BitVec.ofNat 64 32, 16⟩, ⟨State.addr b + BitVec.ofNat 64 56, 4⟩, FA b,
    ⟨State.addr b + BitVec.ofNat 64 o, n⟩]

structure MulKeep (b : BitVec 32) (o n : Nat) (s t : State) : Prop where
  rest : Rest powersClob s t
  frame : Frame (VG.Proof.Ed25519.Arm.mulRegions b o n) s.mem t.mem

theorem MulKeep.refl (b : BitVec 32) (o n : Nat) (s : State) : VG.Proof.Ed25519.Arm.MulKeep b o n s s :=
  ⟨Rest.refl _ _, Frame.refl _ _⟩
theorem MulKeep.ctx {b : BitVec 32} {o n : Nat} {s t : State}
    (h : VG.Proof.Ed25519.Arm.MulKeep b o n s t) (hc : VG.Proof.Ed25519.Arm.Ctx b s) : VG.Proof.Ed25519.Arm.Ctx b t := hc.of_rest h.rest (by decide)
theorem MulKeep.trans {b : BitVec 32} {o n : Nat} {s t u : State}
    (h : VG.Proof.Ed25519.Arm.MulKeep b o n s t) (k : VG.Proof.Ed25519.Arm.MulKeep b o n t u) : VG.Proof.Ed25519.Arm.MulKeep b o n s u :=
  ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

theorem MulKeep.mono {b : BitVec 32} {o n o' n' : Nat} {s t : State}
    (h : VG.Proof.Ed25519.Arm.MulKeep b o n s t) (ho : o' ≤ o) (hn : o + n ≤ o' + n') : VG.Proof.Ed25519.Arm.MulKeep b o' n' s t := by
  refine ⟨h.rest, h.frame.sub fun r hr => ?_⟩
  simp only [VG.Proof.Ed25519.Arm.mulRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_singleton_self _))), Offset.sub _ ho hn⟩
theorem MulKeep.of_powers {b : BitVec 32} {o n : Nat} {s t : State}
    (h : PowersKeep b o n s t) : VG.Proof.Ed25519.Arm.MulKeep b o n s t :=
  ⟨h.rest, Frame.mono h.frame (by intro r hr; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))⟩
theorem MulKeep.of_loop {b : BitVec 32} {o n : Nat} {s t : State}
    (h : LoopKeep b s t) : VG.Proof.Ed25519.Arm.MulKeep b o n s t :=
  ⟨h.rest.mono (by decide), h.frame.mono (by intro r hr; rw [List.mem_singleton.mp hr]; simp only [VG.Proof.Ed25519.Arm.mulRegions, List.mem_cons, true_or, or_true])⟩
theorem MulKeep.of_bits {b : BitVec 32} {o n : Nat} {s t : State} {ws : List Reg}
    (hr : Rest ws s t) (hw : ∀ r ∈ ws, r ∈ powersClob)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 32, 16⟩] s.mem t.mem) : VG.Proof.Ed25519.Arm.MulKeep b o n s t :=
  ⟨hr.mono hw, hf.mono (by intro r hr; rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..)⟩
theorem MulKeep.of_rest {b : BitVec 32} {o n : Nat} {s t : State} {ws : List Reg}
    (hr : Rest ws s t) (hw : ∀ r ∈ ws, r ∈ powersClob) (hm : t.mem = s.mem) : VG.Proof.Ed25519.Arm.MulKeep b o n s t :=
  ⟨hr.mono hw, by rw [hm]; exact Frame.refl _ _⟩

theorem MulKeep.word {b : BitVec 32} {o n : Nat} {s t : State}
    (h : VG.Proof.Ed25519.Arm.MulKeep b o n s t) (ho : 1600 ≤ o) (hn : o + n ≤ 8192)
    (d : Nat) (hd : d = 48 ∨ d = 52) :
    t.mem.readW (State.addr b + BitVec.ofNat 64 d) 32 =
      s.mem.readW (State.addr b + BitVec.ofNat 64 d) 32 := by
  apply BitVec.eq_of_toNat_eq
  exact wd_frame h.frame fun r hr => by
    simp only [VG.Proof.Ed25519.Arm.mulRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem MulKeep.table {b : BitVec 32} {o n : Nat} {s t : State}
    (h : VG.Proof.Ed25519.Arm.MulKeep b o n s t) {d : Nat} (hd : 1600 ≤ d) (hb : d + 128 ≤ 8192)
    (hn : o + n ≤ 8192) (hs : d + 128 ≤ o ∨ o + n ≤ d) :
    tablePoint t.mem b d = tablePoint s.mem b d := by
  refine tablePoint_frame h.frame fun r hr => ?_
  simp only [VG.Proof.Ed25519.Arm.mulRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;>
    exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem smallFrame_env {b : BitVec 32} {m m' : Mem} {o n : Nat}
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, n⟩] m m') (hn : o + n ≤ 64) :
    env m' b = env m b := by
  funext i
  exact congrArg VG.Proof.X25519.toFe (val16_congr (limb_frame hf fun r hr k hk => by
    rw [List.mem_singleton.mp hr]
    have hi := slot_range i
    rw [ACC_eq] at hi
    exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)))

theorem smallFrame_lim {b : BitVec 32} {m m' : Mem} {o n : Nat}
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, n⟩] m m') (hn : o + n ≤ 64)
    (hl : AllLim m b) : AllLim m' b := by
  intro i k hk
  rw [limb_frame hf (fun r hr j hj => by
    rw [List.mem_singleton.mp hr]
    have hi := slot_range i
    rw [ACC_eq] at hi
    exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) k hk]
  exact hl i k hk

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.DecodeKeep`. -/
section

/-! Decoding writes the saved sign and field workspace only. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

structure DecodeKeep (b : BitVec 32) (s t : State) : Prop where
  rest : Rest (.r10 :: clob) s t
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 60, 4⟩, FA b] s.mem t.mem

theorem DecodeKeep.ctx {b : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.Arm.DecodeKeep b s t) (hc : VG.Proof.Ed25519.Arm.Ctx b s) : VG.Proof.Ed25519.Arm.Ctx b t :=
  hc.of_rest h.rest (by decide)
theorem DecodeKeep.trans {b : BitVec 32} {s t u : State} (h : VG.Proof.Ed25519.Arm.DecodeKeep b s t) (k : VG.Proof.Ed25519.Arm.DecodeKeep b t u) :
    VG.Proof.Ed25519.Arm.DecodeKeep b s u := ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩
theorem DecodeKeep.of_ikeep {b : BitVec 32} {s t : State} (h : IKeep b s t) : VG.Proof.Ed25519.Arm.DecodeKeep b s t :=
  ⟨h.rest, h.frame.mono (fun _ hr => List.mem_cons_of_mem _ hr)⟩
theorem DecodeKeep.of_keep {b : BitVec 32} {s t : State} (h : Keep b s t) : VG.Proof.Ed25519.Arm.DecodeKeep b s t :=
  DecodeKeep.of_ikeep (IKeep.of_keep h)

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.MulInput`. -/
section

/-! The scalar input remains unchanged throughout table construction
and descending accumulation. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem mulRegions_sub {b : BitVec 32} {o n : Nat} (hn : o + n ≤ 8192) :
    ∀ r ∈ VG.Proof.Ed25519.Arm.mulRegions b o n, r.Sub ⟨State.addr b, 8192⟩ := by
  intro r hr
  simp only [VG.Proof.Ed25519.Arm.mulRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact Offset.sub_base _ (by omega)

structure MulInput (b p : BitVec 32) (n scalar : Nat) (s : State) : Prop where
  bound : n ≤ 32
  fit : p.toNat + 2 * n ≤ 2 ^ 32
  readable : ∀ i < 2 * n, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1
  separate : (⟨State.addr p, 2 * n⟩ : Region).Disjoint ⟨State.addr b, 8192⟩
  pointer : s.mem.readW (State.addr b + BitVec.ofNat 64 52) 32 = p
  value : val16 (packedLimb s.mem (State.addr p)) n = scalar

theorem MulInput.keep {b p : BitVec 32} {n scalar o len : Nat} {s t : State}
    (h : VG.Proof.Ed25519.Arm.MulInput b p n scalar s) (hk : VG.Proof.Ed25519.Arm.MulKeep b o len s t)
    (ho : 1600 ≤ o) (hn : o + len ≤ 8192) : VG.Proof.Ed25519.Arm.MulInput b p n scalar t := by
  refine ⟨h.bound, h.fit, ?_, h.separate, (hk.word ho hn 52 (.inr rfl)).trans h.pointer, ?_⟩
  · intro i hi
    rw [hk.rest.rd, hk.rest.wr]
    exact h.readable i hi
  · have hb : ∀ i < 2 * n, t.mem (State.addr p + BitVec.ofNat 64 i) =
        s.mem (State.addr p + BitVec.ofNat 64 i) :=
      fun i hi => hk.frame.bytes (fun r hr => h.separate.sub_right (VG.Proof.Ed25519.Arm.mulRegions_sub hn r hr))
        (by have := h.bound; omega : 2 * n ≤ 2 ^ 64) hi
    refine (val16_congr fun j hj => ?_).trans h.value
    simp only [packedLimb, VG.Proof.Ed25519.Arm.byteN, hb (2 * j) (by omega), hb (2 * j + 1) (by omega)]

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.PointDecode`. -/
section

/-! Merged from `Proof.Ed25519.Arm.SplitYSign`. -/
section
/-! Separate bit 255 while retaining all bounded field limbs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem bitNat_eq {q : Nat} (hq : q ≤ 1) : (q == 1).toNat = q := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq with rfl | rfl <;> rfl

theorem splitYSign_ok {s : State} {base : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx base s) (hl : AllLim s.mem base) :
    WP isa (.block splitYSign) s fun t => VG.Proof.Ed25519.Arm.DecodeKeep base s t ∧ AllLim t.mem base ∧
      V t.mem (State.addr base) (offset 1) = V s.mem (State.addr base) (offset 1) % 2 ^ 255 ∧
      t.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 =
        BitVec.ofNat 32 (V s.mem (State.addr base) (offset 1) / 2 ^ 255 == 1).toNat := by
  let f := limb s.mem (State.addr base) (offset 1)
  have hoff : offset (1 : Slot) = 128 := rfl
  have mf := mask15_facts (hl 1)
  refine ldr0_ok hc (by decide) fun s1 u1 => wp_mov (op2_lsr (by decide)) fun s2 u2 => ?_
  have r2 : Rest [.r2, .r3, .r4] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have e2 : (s2.gpr .r2).toNat = f 15 / 32768 := by rw [u2.gpr, toNat_shr, u1.gpr]; rfl
  refine str0_ok (hc.of_rest r2 (by decide)) (by decide) fun s3 u3 => ?_
  have m3 : s3.mem = s.mem.writeW (State.addr base + BitVec.ofNat 64 60) (s2.gpr .r2) := by
    rw [u3.mem, u2.mem, u1.mem]
  have f3 : Frame [⟨State.addr base + BitVec.ofNat 64 60, 4⟩] s.mem s3.mem := by
    rw [m3]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have r3 : Rest [.r2, .r3, .r4] s s3 := r2.trans (u3.rest _)
  refine wp_movw fun s4 u4 => wp_dp (op2_reg _ _) fun s5 u5 => ?_
  have r5 : Rest [.r2, .r3, .r4] s s5 := r3.trans ((u4.rest (by decide)).trans (u5.rest (by decide)))
  have e5 : (s5.gpr .r3).toNat = f 15 % 32768 := by
    rw [u5.gpr]
    change (s4.gpr .r3 &&& s4.gpr .r4).toNat = _
    rw [BitVec.toNat_and, u4.gpr, u4.other _ (by decide), u3.gpr, u2.other _ (by decide), u1.gpr]
    change f 15 &&& (2 ^ 15 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod]
  refine str0_ok (hc.of_rest r5 (by decide)) (by decide) fun t ht => WP.block_nil ?_
  have mt : t.mem = s3.mem.writeW (State.addr base + BitVec.ofNat 64 (offset 1 + 60)) (s5.gpr .r3) := by
    rw [ht.mem, u5.mem, u4.mem]
  have ft : Frame [⟨State.addr base + BitVec.ofNat 64 (offset 1), 64⟩] s3.mem t.mem := by
    rw [mt]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (State.addr base) (d := offset 1 + 60) (n := 4) (e := offset 1) (k := 64)
        (by decide) (by decide) (by decide))
  have ys : ∀ k < 16, limb s3.mem (State.addr base) (offset 1) k = f k :=
    limb_frame f3 fun r hr k hk => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr (by omega)) (by omega) (by decide)
  have yt : ∀ k < 16, limb t.mem (State.addr base) (offset 1) k = mask15 f k := by
    intro k hk
    rw [limb, mt]
    by_cases hk15 : k = 15
    · subst hk15
      rw [wd_write_self, e5]
      rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
      change limb s3.mem (State.addr base) (offset 1) k = _
      rw [ys k hk]
      simp only [mask15, hk15, ite_false]
  have lt : AllLim t.mem base := (field_update 1 (VG.Proof.Ed25519.Arm.smallFrame_lim f3 (by decide) hl) (frame_o ft)
    (fun k hk => by rw [yt k hk]; exact mf.2.2.1 k hk)).1
  refine ⟨⟨(r5.trans (ht.rest _)).mono (by decide), ?_⟩, lt, ?_, ?_⟩
  · exact (f3.mono (fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..)).trans
      (ft.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), by
        rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by decide) (by decide)⟩)
  · rw [V, val16_congr yt]
    have hv : V s.mem (State.addr base) (offset 1) = val16 (mask15 f) 16 + 2 ^ 255 * (f 15 / 32768) := mf.1
    have hb : val16 (mask15 f) 16 < 2 ^ 255 := mf.2.1
    omega
  · apply BitVec.eq_of_toNat_eq
    have hz : wd t.mem (State.addr base) 60 = (s2.gpr .r2).toNat := by
      rw [wd_frame ft (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)),
        wd, m3, Mem.readW_writeW_self32]
    change wd t.mem (State.addr base) 60 = _
    rw [hz, e2, toNat_imm (by have := Bool.toNat_le (V s.mem (State.addr base) (offset 1) / 2 ^ 255 == 1); omega)]
    have he : V s.mem (State.addr base) (offset 1) / 2 ^ 255 = f 15 / 32768 := by
      have hv : V s.mem (State.addr base) (offset 1) = val16 (mask15 f) 16 + 2 ^ 255 * (f 15 / 32768) := mf.1
      have hb : val16 (mask15 f) 16 < 2 ^ 255 := mf.2.1
      omega
    rw [he, VG.Proof.Ed25519.Arm.bitNat_eq mf.2.2.2]

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.DecodeLoad`. -/
section
/-! Merged from `Proof.Ed25519.Arm.CanonicalY`. -/
section
/-! Merged from `Proof.Ed25519.Arm.WordsEqual`. -/
section
/-! Compare bounded fields before modular reduction. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem val16_inj {f g : Nat → Nat} {n : Nat} (hf : ∀ k < n, f k < 65536)
    (hg : ∀ k < n, g k < 65536) : (∀ k < n, f k = g k) ↔ val16 f n = val16 g n := by
  refine ⟨val16_congr, fun h k hk => ?_⟩
  exact (val16_div hf hk).symm.trans ((congrArg (fun x => x / 2 ^ (16 * k) % 65536) h).trans (val16_div hg hk))

structure EqualInv (base : BitVec 32) (a b : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.r2, .r3, .r9] s₀ s
  mem : s.mem = s₀.mem
  zero : s.gpr .r9 = 0#32 ↔ ∀ i < k, limb s₀.mem (State.addr base) a i = limb s₀.mem (State.addr base) b i

theorem equalLimbs_ok {base : BitVec 32} {s₀ : State} (hc : VG.Proof.Ed25519.Arm.Ctx base s₀) (a b : Nat)
    (ha : a + 64 ≤ 4096) (hb : b + 64 ≤ 4096) (hz : s₀.gpr .r9 = 0#32) :
    WP isa (.block ((List.range 16).flatMap (equalLimb a b))) s₀ fun t =>
      VG.Proof.Ed25519.Arm.EqualInv base a b s₀ 16 t := by
  refine wp_range_flatMap (M := isa) (VG.Proof.Ed25519.Arm.EqualInv base a b s₀) (fun k s hk h => ?_) 16 (Nat.le_refl _) s₀
    ⟨Rest.refl _ _, rfl, ⟨fun _ _ h => by omega, fun _ => hz⟩⟩
  have hcs := hc.of_rest h.rest (by decide)
  refine ldr0_ok hcs (by omega) fun s1 u1 =>
    ldr0_ok (hcs.of_rest (u1.rest (ws := [.r3]) (by decide)) (by decide)) (by omega) fun s2 u2 =>
    wp_dp (op2_reg _ _) fun s3 u3 => wp_dp (op2_reg _ _) fun t ht => WP.block_nil ?_
  have el : (s2.gpr .r3).toNat = limb s₀.mem (State.addr base) a k := by
    rw [u2.other _ (by decide), u1.gpr, h.mem]; rfl
  have er : (s2.gpr .r2).toNat = limb s₀.mem (State.addr base) b k := by
    rw [u2.gpr, u1.mem, h.mem]; rfl
  have eqv : s2.gpr .r3 = s2.gpr .r2 ↔ limb s₀.mem (State.addr base) a k = limb s₀.mem (State.addr base) b k :=
    ⟨fun h => el.symm.trans ((congrArg BitVec.toNat h).trans er),
      fun h => BitVec.eq_of_toNat_eq (el.trans (h.trans er.symm))⟩
  refine ⟨h.rest.trans ((u1.rest (by decide)).trans ((u2.rest (by decide)).trans
    ((u3.rest (by decide)).trans (ht.rest (by decide))))), by rw [ht.mem, u3.mem, u2.mem, u1.mem, h.mem], ?_⟩
  rw [ht.gpr]
  change (s3.gpr .r9 ||| s3.gpr .r3 = 0#32) ↔ _
  rw [BitVec.or_eq_zero_iff, u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), h.zero,
    u3.gpr]
  change (_ ∧ (s2.gpr .r3 ^^^ s2.gpr .r2 = 0#32)) ↔ _
  rw [BitVec.xor_eq_zero_iff, eqv]
  constructor
  · rintro ⟨hpre, hlast⟩ i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact hpre i hi
    · exact hlast
  · intro h
    exact ⟨fun i hi => h i (by omega), h k (by omega)⟩

theorem wordsEqual_ok {base : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx base s) (a b : Nat)
    (ha : a + 64 ≤ 4096) (hb : b + 64 ≤ 4096)
    (hla : Lim s.mem (State.addr base) a) (hlb : Lim s.mem (State.addr base) b) :
    WP isa (.block (wordsEqual a b)) s fun t => Rest [.r2, .r3, .r9] s t ∧ t.mem = s.mem ∧
      t.z = decide (V s.mem (State.addr base) a = V s.mem (State.addr base) b) := by
  unfold wordsEqual
  rw [List.append_assoc, WP.block_append_iff]
  refine wp_mov (op2_imm (by decide)) fun u hu => WP.block_nil ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.Arm.equalLimbs_ok (hc.of_rest (hu.rest (ws := [.r9]) (by decide)) (by decide)) a b ha hb hu.gpr)
    fun v hv => ?_
  refine wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ?_
  refine ⟨(hu.rest (by decide)).trans (hv.rest.trans (ht.rest _)), by rw [ht.mem, hv.mem, hu.mem], ?_⟩
  have he : v.gpr .r9 - (0 : BitVec 32) = v.gpr .r9 := BitVec.sub_zero _
  rw [hz, he]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  change (v.gpr .r9 = 0#32) ↔ _
  rw [hv.zero, hu.mem]
  exact VG.Proof.Ed25519.Arm.val16_inj hla hlb

end VG.Proof.Ed25519.Arm
end

/-! Equality with the canonical representative rejects y >= p. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem canonicalY_ok {s : State} {base : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx base s) (hl : AllLim s.mem base) :
    WP isa canonicalY s fun t => Keep base s t ∧ AllLim t.mem base ∧ env t.mem base = env s.mem base ∧
      t.z = decide (V s.mem (State.addr base) (offset 1) < Spec.X25519.P) := by
  refine WP.seq (WP.mono (freezeRaw_ok hc hl 1) fun u ⟨uk, ul, ue, uf, uv, uraw⟩ => ?_)
  refine WP.mono (VG.Proof.Ed25519.Arm.wordsEqual_ok (uk.ctx hc) (offset 1) FR (by decide) (by decide) (ul 1) uf)
    fun t ⟨tr, tm, tz⟩ => ?_
  refine ⟨uk.trans ⟨tr.mono (by decide), by rw [tm]; exact Frame.refl _ _⟩,
    tm ▸ ul, (congrArg (fun m => env m base) tm).trans ue, ?_⟩
  have vy : V u.mem (State.addr base) (offset 1) = V s.mem (State.addr base) (offset 1) :=
    val16_congr (uraw 1)
  rw [tz, vy, uv]
  change decide (V s.mem (State.addr base) (offset 1) = V s.mem (State.addr base) (offset 1) % Spec.X25519.P) = _
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    exact h ▸ Nat.mod_lt _ (by decide)
  · intro h
    exact (Nat.mod_eq_of_lt h).symm

end VG.Proof.Ed25519.Arm
end

/-! Read canonical y and the encoded sign from the 32 input bytes. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem packedV_decode (m : Mem) (p : Addr) :
    packedV m p = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p 32) := by
  rw [decodeLE_eq]
  exact (VG.Proof.Ed25519.Arm.leNum_bytesAt2 m p 16).symm

theorem pointDecodeLoad_ok {s : State} {base ptr : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx base s) (hl : AllLim s.mem base)
    (hp : s.gpr .r12 = ptr) (hfit : ptr.toNat + 32 ≤ 2 ^ 32)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (State.addr ptr + BitVec.ofNat 64 i) 1)
    (hsep : (⟨State.addr ptr, 32⟩ : Region).Disjoint ⟨State.addr base, 8192⟩) :
    WP isa pointDecodeLoad s fun t => VG.Proof.Ed25519.Arm.DecodeKeep base s t ∧ AllLim t.mem base ∧
      t.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 =
        BitVec.ofNat 32 (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) / 2 ^ 255 == 1).toNat ∧
      env t.mem base 1 = VG.Proof.X25519.toFe
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) % 2 ^ 255) ∧
      t.z = decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) % 2 ^ 255 < Spec.X25519.P) := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (unpackField_ok hc (o := offset 1) (src := 0) (by decide) (by decide) hp
    (by omega) (by simpa only [Nat.zero_add] using hr) ?_) fun u ⟨ur, uf, ul, uv⟩ => ?_
  · have hp0 : State.addr ptr + BitVec.ofNat 64 0 = State.addr ptr := BitVec.add_zero _
    rw [hp0]
    exact hsep.sub_right (Offset.sub_base _ (by decide))
  have vu : V u.mem (State.addr base) (offset 1) =
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) :=
    uv.trans ((congrArg (packedV s.mem) (BitVec.add_zero _)).trans (VG.Proof.Ed25519.Arm.packedV_decode _ _))
  obtain ⟨uk, ull, _⟩ := field_finish 1 hl (ur.mono (by decide)) (frame_o uf) ul (v := FS u.mem (State.addr base) (offset 1)) rfl
  refine WP.mono (VG.Proof.Ed25519.Arm.splitYSign_ok (uk.ctx hc) ull) fun v ⟨vk, vl, vy, vs⟩ => ?_
  have kv : VG.Proof.Ed25519.Arm.DecodeKeep base s v := (DecodeKeep.of_keep uk).trans vk
  have ve : env v.mem base 1 = VG.Proof.X25519.toFe
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) % 2 ^ 255) :=
    congrArg VG.Proof.X25519.toFe (vy.trans (congrArg (· % 2 ^ 255) vu))
  refine WP.mono (VG.Proof.Ed25519.Arm.canonicalY_ok (kv.ctx hc) vl) fun t ⟨tk, tl, te, tz⟩ => ?_
  refine ⟨kv.trans (DecodeKeep.of_keep tk), tl, ?_, (congrFun te 1).trans ve, ?_⟩
  · rw [tk.sign, vs, vu]
  · rw [tz, vy, vu]

end VG.Proof.Ed25519.Arm
end

/-! The public byte decoder matches the reviewed strict specification. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

theorem pointDecode_ok {s : State} {base ptr : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx base s) (hl : AllLim s.mem base)
    (hp : s.gpr .r12 = ptr) (hfit : ptr.toNat + 32 ≤ 2 ^ 32)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (State.addr ptr + BitVec.ofNat 64 i) 1)
    (hsep : (⟨State.addr ptr, 32⟩ : Region).Disjoint ⟨State.addr base, 8192⟩) :
    WP isa pointDecode s fun t => VG.Proof.Ed25519.Arm.DecodeKeep base s t ∧ AllLim t.mem base ∧
      DecodeResult base (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32)) t := by
  have hlen : (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32).length = 32 := by
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.pointDecodeLoad_ok hc hl hp hfit hr hsep) fun a ⟨ak, al, asign, ay, az⟩ => ?_)
  apply WP.ite (decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) % 2 ^ 255 < Spec.X25519.P))
    (by simp only [VG.Arm.eval, az])
  · intro ht
    have hy := of_decide_eq_true ht
    refine WP.mono (recoverPoint_ok (ak.ctx hc) al _ asign) fun t ⟨tk, tl, tr⟩ => ?_
    refine ⟨ak.trans (DecodeKeep.of_ikeep tk), tl, ?_⟩
    rw [decodePoint32 _ hlen, ite_eq_left hy]
    rw [ay] at tr
    exact tr
  · intro hf
    have hy := of_decide_eq_false hf
    refine WP.mono (recoverInvalid_ok a base) fun t ⟨tk, tm, tr⟩ => ?_
    refine ⟨ak.trans (DecodeKeep.of_keep tk), tm ▸ al, ?_⟩
    rw [decodePoint32 _ hlen, ite_eq_right hy]
    exact tr

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.PointMulBody`. -/
section

/-! Merged from `Proof.Ed25519.Arm.BatchFrame`. -/
section
/-! Merged from `Proof.Ed25519.Arm.BatchCounter`. -/
section
/-! The public descending batch counter is saved across field operations. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem counterStore_ok {b : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (j : Nat)
    (hv : s.gpr .r11 = BitVec.ofNat 32 j) :
    WP isa (.block [.str .r11 .r0 56]) s fun t => Rest [] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 56, 4⟩] s.mem t.mem ∧
      t.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 j := by
  refine str0_ok hc (by decide) fun t ht => WP.block_nil ⟨ht.rest _, ?_, ?_⟩
  · rw [ht.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · rw [ht.mem, Mem.readW_writeW_self32, hv]

theorem MulKeep.of_counter {b : BitVec 32} {o n : Nat} {s t : State} {ws : List Reg}
    (hr : Rest ws s t) (hw : ∀ r ∈ ws, r ∈ powersClob)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 56, 4⟩] s.mem t.mem) : VG.Proof.Ed25519.Arm.MulKeep b o n s t :=
  ⟨hr.mono hw, hf.mono (by
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩

theorem batchStart_ok {b : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (j : Nat)
    (hv : s.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 (j + 1)) :
    WP isa (.block batchStart) s fun t => Rest [.r11] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 56, 4⟩] s.mem t.mem ∧
      t.gpr .r11 = BitVec.ofNat 32 j ∧
      t.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 j := by
  refine ldr0_ok hc (by decide) fun u hu => wp_dp (op2_imm (by decide)) fun v hv' => ?_
  have ev : v.gpr .r11 = BitVec.ofNat 32 j := by
    rw [hv'.gpr]
    change u.gpr .r11 - 1 = _
    rw [hu.gpr, hv, BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  have rv : Rest [.r11] s v := (hu.rest (by decide)).trans (hv'.rest (by decide))
  have mv : v.mem = s.mem := by rw [hv'.mem, hu.mem]
  refine WP.mono (VG.Proof.Ed25519.Arm.counterStore_ok (hc.of_rest rv (by decide)) j ev) fun t ⟨tr, tf, tv⟩ => ?_
  exact ⟨rv.trans (tr.mono (by decide)), by rw [← mv]; exact tf,
    (tr.gpr _ (by decide)).trans ev, tv⟩

theorem batchTest_ok {b : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (j : Nat) (hj : j < 32)
    (hv : s.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 j) :
    WP isa (.block batchTest) s fun t => Rest [.r11] s t ∧ t.mem = s.mem ∧ t.z = decide (j = 0) := by
  refine ldr0_ok hc (by decide) fun u hu => wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ?_
  refine ⟨(hu.rest (by decide)).trans (ht.rest _), by rw [ht.mem, hu.mem], ?_⟩
  have he : BitVec.ofNat 32 j - (0 : BitVec 32) = BitVec.ofNat 32 j := BitVec.sub_zero _
  rw [hz, hu.gpr, hv, he, ofNat_beq_zero (by omega)]

end VG.Proof.Ed25519.Arm
end

/-! The saved batch counter survives the table and bit operations. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem PowersKeep.counter {b : BitVec 32} {o n : Nat} {s t : State}
    (h : PowersKeep b o n s t) (ho : 1600 ≤ o) (hn : o + n ≤ 8192) :
    t.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 =
      s.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 := by
  apply BitVec.eq_of_toNat_eq
  exact wd_frame h.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.disjoint _ (.inl (by omega)) (by decide) (by omega)

theorem LoopKeep.counter {b : BitVec 32} {s t : State} (h : LoopKeep b s t) :
    t.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 =
      s.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 := by
  apply BitVec.eq_of_toNat_eq
  exact wd_frame h.frame fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)

theorem bitsFrame_counter {b : BitVec 32} {m m' : Mem}
    (h : Frame [⟨State.addr b + BitVec.ofNat 64 32, 16⟩] m m') :
    m'.readW (State.addr b + BitVec.ofNat 64 56) 32 =
      m.readW (State.addr b + BitVec.ofNat 64 56) 32 := by
  apply BitVec.eq_of_toNat_eq
  exact wd_frame h fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)

theorem smallFrame_table {b : BitVec 32} {m m' : Mem} {o n d : Nat}
    (h : Frame [⟨State.addr b + BitVec.ofNat 64 o, n⟩] m m') (hn : o + n ≤ 64)
    (hd : 1600 ≤ d) (hb : d + 128 ≤ 8192) : tablePoint m' b d = tablePoint m b d := by
  refine tablePoint_frame h fun r hr => ?_
  rw [List.mem_singleton.mp hr]
  exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)

end VG.Proof.Ed25519.Arm
end

/-! One outer batch consumes exactly sixteen scalar bits. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem pointMulBody_ok {b ptr : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hl : AllLim s.mem b)
    (count scalar j : Nat) (p : Spec.Ed25519.Point) (hi : VG.Proof.Ed25519.Arm.MulInput b ptr count scalar s)
    (hj : j < count) (hd : env s.mem b 16 = Spec.Ed25519.d)
    (hp : point (env s.mem b) 0 1 2 3 = after scalar p (16 * (j + 1)))
    (hcj : s.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 (j + 1))
    (ht : tablePoint s.mem b (1600 + 128 * j) = powerPoint p (16 * j)) :
    WP isa pointMulBody s fun t => VG.Proof.Ed25519.Arm.MulKeep b 5696 2048 s t ∧ AllLim t.mem b ∧
      env t.mem b 16 = Spec.Ed25519.d ∧ point (env t.mem b) 0 1 2 3 = after scalar p (16 * j) ∧
      t.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 j ∧ t.z = decide (j = 0) := by
  have hj32 : j < 32 := Nat.lt_of_lt_of_le hj hi.bound
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.batchStart_ok hc j hcj) fun a ⟨ar, af, av, ac⟩ => ?_)
  have ak : VG.Proof.Ed25519.Arm.MulKeep b 5696 2048 s a := MulKeep.of_counter ar (by decide) af
  have al := VG.Proof.Ed25519.Arm.smallFrame_lim af (by decide) hl
  have ae := VG.Proof.Ed25519.Arm.smallFrame_env af (by decide)
  have ad : env a.mem b 16 = Spec.Ed25519.d := (congrFun ae 16).trans hd
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.prepareBatch_ok (ak.ctx hc) al j hj32 av ad) fun u ⟨uk, ul, up, ut, ud⟩ => ?_)
  have kum : VG.Proof.Ed25519.Arm.MulKeep b 5696 2048 s u := ak.trans (MulKeep.of_powers uk)
  have ui := hi.keep kum (by decide) (by decide)
  have uc := (uk.counter (by decide) (by decide)).trans ac
  have upt : point (env u.mem b) 0 1 2 3 = after scalar p (16 * j + 16) :=
    up.trans ((congrArg (fun e => point e 0 1 2 3) ae).trans
      (hp.trans (congrArg (after scalar p) (by omega))))
  have utt : ∀ i < 16, tablePoint u.mem b (5696 + 128 * i) = powerPoint p (16 * j + i) := by
    intro i hib
    exact (ut i hib).trans ((congrArg (fun q => powerPoint q i)
      ((VG.Proof.Ed25519.Arm.smallFrame_table af (by decide) (by omega) (by omega)).trans ht)).trans
      (powerPoint_add p (16 * j) i).symm)
  refine WP.seq (WP.mono (batchBits_ok (kum.ctx hc) count j hj ui.bound ui.fit ui.pointer uc ui.readable)
    fun v ⟨vr, vf, vb⟩ => ?_)
  have kv : VG.Proof.Ed25519.Arm.MulKeep b 5696 2048 u v := MulKeep.of_bits vr (by decide) vf
  have ve := VG.Proof.Ed25519.Arm.smallFrame_env vf (by decide)
  have vl := VG.Proof.Ed25519.Arm.smallFrame_lim vf (by decide) ul
  have vbits : ∀ i < 16, v.mem (State.addr b + BitVec.ofNat 64 (32 + i)) =
      BitVec.ofNat 8 (VG.Proof.Ed25519.Arm.scalarBit scalar (16 * j + i)).toNat := by
    intro i hib
    exact (vb i hib).trans (congrArg (fun x => BitVec.ofNat 8 (VG.Proof.Ed25519.Arm.scalarBit x (16 * j + i)).toNat) ui.value)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.accumulate16_ok (kv.ctx (kum.ctx hc)) vl (16 * j) scalar p vbits
    ((congrFun ve 16).trans ud) ((congrArg (fun e => point e 0 1 2 3) ve).trans upt)
    (fun i hib => (VG.Proof.Ed25519.Arm.smallFrame_table vf (by decide) (by omega) (by omega)).trans (utt i hib)))
    fun w ⟨wl, wp, wd, wk⟩ => ?_)
  have kwm : VG.Proof.Ed25519.Arm.MulKeep b 5696 2048 s w := kum.trans (kv.trans (MulKeep.of_loop wk))
  have wc := wk.counter.trans ((VG.Proof.Ed25519.Arm.bitsFrame_counter vf).trans uc)
  refine WP.mono (VG.Proof.Ed25519.Arm.batchTest_ok (kwm.ctx hc) j hj32 wc) fun t ⟨tr, tm, tz⟩ => ?_
  exact ⟨kwm.trans (MulKeep.of_rest tr (by decide) tm), tm ▸ wl,
    (congrArg (fun m => env m b 16) tm).trans wd,
    (congrArg (fun m => point (env m b) 0 1 2 3) tm).trans wp,
    (congrArg (fun m => m.readW (State.addr b + BitVec.ofNat 64 56) 32) tm).trans wc, tz⟩

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.PointMulLoop`. -/
section

/-! Descending through every checkpoint proves the full scalar product. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

structure PointMulInv (s₀ : State) (b ptr : BitVec 32) (count scalar : Nat)
    (p : Spec.Ed25519.Point) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ count
  ctx : VG.Proof.Ed25519.Arm.Ctx b s
  lim : AllLim s.mem b
  input : VG.Proof.Ed25519.Arm.MulInput b ptr count scalar s
  counter : s.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 n
  d : env s.mem b 16 = Spec.Ed25519.d
  value : point (env s.mem b) 0 1 2 3 = after scalar p (16 * n)
  table : ∀ j < count, tablePoint s.mem b (1600 + 128 * j) = powerPoint p (16 * j)
  keep : VG.Proof.Ed25519.Arm.MulKeep b 5696 2048 s₀ s

theorem pointMulLoop_ok {b ptr : BitVec 32} {s₀ : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s₀) (hl : AllLim s₀.mem b)
    (count scalar : Nat) (p : Spec.Ed25519.Point) (hi : VG.Proof.Ed25519.Arm.MulInput b ptr count scalar s₀)
    (hn : 0 < count) (hd : env s₀.mem b 16 = Spec.Ed25519.d)
    (hp : point (env s₀.mem b) 0 1 2 3 = after scalar p (16 * count))
    (hcj : s₀.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 count)
    (ht : ∀ j < count, tablePoint s₀.mem b (1600 + 128 * j) = powerPoint p (16 * j)) :
    WP isa (.loop pointMulBody .ne) s₀ fun t => VG.Proof.Ed25519.Arm.MulKeep b 5696 2048 s₀ t ∧ AllLim t.mem b ∧
      env t.mem b 16 = Spec.Ed25519.d ∧ point (env t.mem b) 0 1 2 3 = Spec.Ed25519.pointMul scalar p := by
  apply WP.loop (VG.Proof.Ed25519.Arm.PointMulInv s₀ b ptr count scalar p) (n := count)
  · intro n s h
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.positive; omega : n ≠ 0)
    have hj : j < count := by have := h.bound; omega
    refine WP.mono (VG.Proof.Ed25519.Arm.pointMulBody_ok h.ctx h.lim count scalar j p h.input hj h.d h.value h.counter
      (h.table j hj)) fun t ⟨tk, tl, td, tp, tc, tz⟩ => ?_
    have tt : ∀ i < count, tablePoint t.mem b (1600 + 128 * i) = powerPoint p (16 * i) := by
      intro i hib
      have := h.input.bound
      exact (tk.table (by omega) (by omega) (by decide) (.inl (by omega))).trans (h.table i hib)
    by_cases hj0 : j = 0
    · subst hj0
      exact .inl ⟨by simp only [VG.Arm.eval, tz, decide_true, Bool.not_true], h.keep.trans tk,
        tl, td, tp.trans (after_zero scalar p)⟩
    · exact .inr ⟨by simp only [VG.Arm.eval, tz, decide_eq_false hj0, Bool.not_false],
        j, by omega, ⟨by omega, by omega, tk.ctx h.ctx, tl,
          h.input.keep tk (by decide) (by decide), tc, td, tp, tt, h.keep.trans tk⟩⟩
  · exact ⟨hn, Nat.le_refl _, hc, hl, hi, hcj, hd, hp, ht, MulKeep.refl _ _ _ _⟩

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.PointMul`. -/
section

/-! Full scalar multiplication agrees with the reviewed specification. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem constPoint_d (p : Spec.Ed25519.Point) (e : Env) : evalOps (constPointOps p) e 16 = e 16 := rfl

theorem pointMultiply_ok {b ptr : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hl : AllLim s.mem b)
    (count scalar : Nat) (hi : VG.Proof.Ed25519.Arm.MulInput b ptr count scalar s) (hn : 0 < count)
    (hd : env s.mem b 16 = Spec.Ed25519.d) :
    WP isa (pointMultiply count) s fun t => VG.Proof.Ed25519.Arm.MulKeep b 1600 6144 s t ∧ AllLim t.mem b ∧
      env t.mem b 16 = Spec.Ed25519.d ∧ point (env t.mem b) 0 1 2 3 =
        Spec.Ed25519.pointMul scalar (point (env s.mem b) 0 1 2 3) := by
  let p := point (env s.mem b) 0 1 2 3
  have hs : scalar < 2 ^ (16 * count) := by
    rw [← hi.value]
    exact val16_lt (fun k _ => packedLimb_lt _ _ k)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.pointPowers_ok true hc hl 1600 count (by decide)
    (by have := hi.bound; omega) hn hi.bound hd) fun a ⟨al, ats, _, ah, ak⟩ => ?_)
  have kam : VG.Proof.Ed25519.Arm.MulKeep b 1600 6144 s a := (MulKeep.of_powers ak).mono (by decide) (by have := hi.bound; omega)
  refine WP.seq (WP.mono (fieldCode_ok (constPointOps Spec.Ed25519.identity) (kam.ctx hc) al)
    fun u ⟨uk, ul, ue⟩ => ?_)
  have kum : VG.Proof.Ed25519.Arm.MulKeep b 1600 6144 s u := kam.trans (MulKeep.of_powers (PowersKeep.of_keep uk))
  have ud : env u.mem b 16 = Spec.Ed25519.d := by rw [ue, VG.Proof.Ed25519.Arm.constPoint_d, ah 16 (by decide), hd]
  have up : point (env u.mem b) 0 1 2 3 = after scalar p (16 * count) :=
    ((congrArg (fun e => point e 0 1 2 3) ue).trans (constPoint_eval _ _)).trans
      (after_top scalar (16 * count) p hs).symm
  have ut : ∀ j < count, tablePoint u.mem b (1600 + 128 * j) = powerPoint p (16 * j) := by
    intro j hj
    have := hi.bound
    exact (workspace_tablePoint uk.frame (by omega) (by omega)).trans (ats j hj)
  refine WP.seq (wp_movw fun v hv => ?_)
  have vc : v.gpr .r11 = BitVec.ofNat 32 count := by
    apply BitVec.eq_of_toNat_eq
    rw [hv.gpr, movw_nat (by have := hi.bound; omega), toNat_imm (by have := hi.bound; omega)]
  have kvm : VG.Proof.Ed25519.Arm.MulKeep b 1600 6144 s v := kum.trans
    (MulKeep.of_rest (hv.rest (ws := [.r11]) (by decide)) (by decide) hv.mem)
  refine WP.mono (VG.Proof.Ed25519.Arm.counterStore_ok (kvm.ctx hc) count vc) fun w ⟨wr, wf, wc⟩ => ?_
  have kwm : VG.Proof.Ed25519.Arm.MulKeep b 1600 6144 s w := kvm.trans (MulKeep.of_counter wr (by decide) wf)
  have we : env w.mem b = env u.mem b := (VG.Proof.Ed25519.Arm.smallFrame_env wf (by decide)).trans
    (congrArg (fun m => env m b) hv.mem)
  have wl : AllLim w.mem b := VG.Proof.Ed25519.Arm.smallFrame_lim wf (by decide) (by rw [hv.mem]; exact ul)
  refine WP.mono (VG.Proof.Ed25519.Arm.pointMulLoop_ok (kwm.ctx hc) wl count scalar p
    (hi.keep kwm (by decide) (by decide)) hn ((congrFun we 16).trans ud)
    ((congrArg (fun e => point e 0 1 2 3) we).trans up) wc (fun j hj => ?_))
    fun t ⟨tk, tl, td, tp⟩ => ⟨kwm.trans (tk.mono (by decide) (by decide)), tl, td, tp⟩
  have := hi.bound
  exact (VG.Proof.Ed25519.Arm.smallFrame_table wf (by decide) (by omega) (by omega)).trans
    ((congrArg (fun m => tablePoint m b (1600 + 128 * j)) hv.mem).trans (ut j hj))

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.PointKeep`. -/
section

/-! Point engines preserve register saves, the output pointer, and
the three packed points reserved for verification. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

abbrev pointRegions (b : BitVec 32) : List Region :=
  [⟨State.addr b + BitVec.ofNat 64 32, 16⟩, ⟨State.addr b + BitVec.ofNat 64 52, 7692⟩]

structure PointKeep (b : BitVec 32) (s t : State) : Prop where
  rest : Rest powersClob s t
  frame : Frame (VG.Proof.Ed25519.Arm.pointRegions b) s.mem t.mem

theorem PointKeep.refl (b : BitVec 32) (s : State) : VG.Proof.Ed25519.Arm.PointKeep b s s := ⟨Rest.refl _ _, Frame.refl _ _⟩
theorem PointKeep.ctx {b : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.Arm.PointKeep b s t) (hc : VG.Proof.Ed25519.Arm.Ctx b s) : VG.Proof.Ed25519.Arm.Ctx b t :=
  hc.of_rest h.rest (by decide)
theorem PointKeep.trans {b : BitVec 32} {s t u : State} (h : VG.Proof.Ed25519.Arm.PointKeep b s t) (k : VG.Proof.Ed25519.Arm.PointKeep b t u) :
    VG.Proof.Ed25519.Arm.PointKeep b s u := ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩
theorem PointKeep.of_mul {b : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.Arm.MulKeep b 1600 6144 s t) : VG.Proof.Ed25519.Arm.PointKeep b s t := by
  refine ⟨h.rest, h.frame.sub fun r hr => ?_⟩
  simp only [VG.Proof.Ed25519.Arm.mulRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  all_goals exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Offset.sub _ (by decide) (by decide)⟩
theorem PointKeep.of_ikeep {b : BitVec 32} {s t : State} (h : IKeep b s t) : VG.Proof.Ed25519.Arm.PointKeep b s t :=
  ⟨h.rest.mono (by decide), h.frame.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), by
    rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by decide) (by decide)⟩⟩
theorem PointKeep.of_keep {b : BitVec 32} {s t : State} (h : Keep b s t) : VG.Proof.Ed25519.Arm.PointKeep b s t :=
  PointKeep.of_ikeep (IKeep.of_keep h)
theorem PointKeep.of_small {b : BitVec 32} {s t : State} {o n : Nat} {ws : List Reg}
    (hr : Rest ws s t) (hw : ∀ r ∈ ws, r ∈ powersClob)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, n⟩] s.mem t.mem) (ho : 52 ≤ o) (hn : o + n ≤ 7744) :
    VG.Proof.Ed25519.Arm.PointKeep b s t := ⟨hr.mono hw, hf.sub fun r hm => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), by
      rw [List.mem_singleton.mp hm]; exact Offset.sub _ ho hn⟩⟩

theorem PointKeep.word {b : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.Arm.PointKeep b s t)
    (d : Nat) (hd : d = 48 ∨ 7744 ≤ d) (hn : d + 4 ≤ 8192) :
    t.mem.readW (State.addr b + BitVec.ofNat 64 d) 32 = s.mem.readW (State.addr b + BitVec.ofNat 64 d) 32 := by
  apply BitVec.eq_of_toNat_eq
  exact wd_frame h.frame fun r hr => by
    simp only [VG.Proof.Ed25519.Arm.pointRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega) (by omega) (by decide)

theorem PointKeep.table {b : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.Arm.PointKeep b s t) {d : Nat}
    (hd : 7744 ≤ d) (hn : d + 128 ≤ 8192) : tablePoint t.mem b d = tablePoint s.mem b d := by
  refine tablePoint_frame h.frame fun r hr => ?_
  simp only [VG.Proof.Ed25519.Arm.pointRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Offset.disjoint _ (.inr (by omega)) (by omega) (by decide)

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.PointFromScalar`. -/
section

/-! Scalar multiplication reads either all 256 or all 512 input bits. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem packedDigits_decode (m : Mem) (ptr : Addr) (n : Nat) :
    val16 (packedLimb m ptr) n = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m ptr (2 * n)) := by
  rw [decodeLE_eq]
  exact (VG.Proof.Ed25519.Arm.leNum_bytesAt2 m ptr n).symm

theorem packedDigits_frame {m m' : Mem} {ptr : Addr} {n : Nat} {rs : List Region}
    (hf : Frame rs m m') (hn : n ≤ 32) (hs : ∀ r ∈ rs, (⟨ptr, 2 * n⟩ : Region).Disjoint r) :
    val16 (packedLimb m' ptr) n = val16 (packedLimb m ptr) n := by
  apply val16_congr
  intro k hk
  have hb : ∀ i < 2 * n, m' (ptr + BitVec.ofNat 64 i) = m (ptr + BitVec.ofNat 64 i) :=
    fun i hi => hf.bytes hs (by omega : 2 * n ≤ 2 ^ 64) hi
  simp only [packedLimb, VG.Proof.Ed25519.Arm.byteN, hb (2 * k) (by omega), hb (2 * k + 1) (by omega)]

theorem pointFromScalar_ok {s : State} {base ptr : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx base s) (hl : AllLim s.mem base)
    (hp : s.gpr .r12 = ptr) (count : Nat) (hn0 : 0 < count) (hn : count ≤ 32)
    (hfit : ptr.toNat + 2 * count ≤ 2 ^ 32)
    (hr : ∀ i < 2 * count, InRegions (s.rd ++ s.wr) (State.addr ptr + BitVec.ofNat 64 i) 1)
    (hsep : (⟨State.addr ptr, 2 * count⟩ : Region).Disjoint ⟨State.addr base, 8192⟩) :
    WP isa (pointFromScalar count) s fun t => VG.Proof.Ed25519.Arm.PointKeep base s t ∧ AllLim t.mem base ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ point (env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) (2 * count)))
          (point (env s.mem base) 0 1 2 3) := by
  refine WP.seq (str0_ok hc (by decide) fun u hu => WP.block_nil ?_)
  have uf : Frame [⟨State.addr base + BitVec.ofNat 64 52, 4⟩] s.mem u.mem := by
    rw [hu.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have uk : VG.Proof.Ed25519.Arm.PointKeep base s u := PointKeep.of_small (hu.rest []) (by decide) uf (by decide) (by decide)
  have ue := VG.Proof.Ed25519.Arm.smallFrame_env uf (by decide)
  have ui : VG.Proof.Ed25519.Arm.MulInput base ptr count (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) (2 * count))) u := by
    refine ⟨hn, hfit, ?_, hsep, ?_, ?_⟩
    · intro i hi
      rw [hu.rd, hu.wr]
      exact hr i hi
    · rw [hu.mem, Mem.readW_writeW_self32, hp]
    · exact (VG.Proof.Ed25519.Arm.packedDigits_frame uf hn (fun r hm => by
        rw [List.mem_singleton.mp hm]; exact hsep.sub_right (Offset.sub_base _ (by decide)))).trans
        (VG.Proof.Ed25519.Arm.packedDigits_decode _ _ count)
  refine WP.seq (WP.mono (fieldCode_ok [.const 16 Spec.Ed25519.d] (uk.ctx hc)
    (VG.Proof.Ed25519.Arm.smallFrame_lim uf (by decide) hl)) fun v ⟨vk, vl, ve⟩ => ?_)
  have vm : VG.Proof.Ed25519.Arm.MulKeep base 1600 6144 u v := MulKeep.of_powers (PowersKeep.of_keep vk)
  have vd : env v.mem base 16 = Spec.Ed25519.d := by rw [ve]; rfl
  have vp : point (env v.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by
    rw [ve]
    change point (env u.mem base) 0 1 2 3 = _
    exact congrArg (fun e => point e 0 1 2 3) ue
  refine WP.mono (VG.Proof.Ed25519.Arm.pointMultiply_ok (vk.ctx (uk.ctx hc)) vl count _
    (ui.keep vm (by decide) (by decide)) hn0 vd) fun t ⟨tk, tl, td, tp⟩ => ?_
  exact ⟨(uk.trans (PointKeep.of_keep vk)).trans (PointKeep.of_mul tk), tl, td,
    tp.trans (congrArg (Spec.Ed25519.pointMul _) vp)⟩

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTSupport`. -/
section

/-! Relational composition restores public metadata from checked functional proofs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm

abbrev CT := RelCT isa

theorem ctRegs {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hp : ∀ x y, P x y → ∀ r ∈ rs, x.gpr r = y.gpr r)
    {hint : VG.Taint.Hint VG.Arm.Taint.T}
    (hc : (VG.Arm.taint.check (VG.Arm.Taint.ofRegs rs) c hint).isSome = true) :
    VG.Proof.Ed25519.Arm.CT P c (fun _ _ => True) :=
  RelCT.taint (A := VG.Arm.taint) (VG.Arm.Taint.ofRegs rs)
    (fun x y h => VG.Arm.Taint.agree_ofRegs (hp x y h)) hc

theorem ctRegsKeeping {P : State → State → Prop} {c : Prog isa} (rs out : List Reg)
    (hp : ∀ x y, P x y → ∀ r ∈ rs, x.gpr r = y.gpr r)
    {hint : VG.Taint.Hint VG.Arm.Taint.T}
    (hc : ((VG.Arm.taint.check (VG.Arm.Taint.ofRegs rs) c hint).map
      fun t => (RegSet.ofList out).subset t.regs) = some true) :
    VG.Proof.Ed25519.Arm.CT P c (fun x y => ∀ r ∈ out, x.gpr r = y.gpr r) := by
  intro x y tx ty u v h ex ey
  obtain ⟨tau, ht, ho⟩ := Option.map_eq_some_iff.mp hc
  have ha : VG.Arm.Taint.Agree (VG.Arm.Taint.ofRegs rs) x y := VG.Arm.Taint.agree_ofRegs (hp x y h)
  obtain ⟨he, hf⟩ := VG.Taint.check_sound ht ha ex ey
  exact ⟨he, fun r hr => hf.rf.1 r (RegSet.mem_of_subset ho (RegSet.mem_ofList.mpr hr))⟩

theorem ctBoth {P F : State → Prop} {c : Prog isa}
    (hc : VG.Proof.Ed25519.Arm.CT (fun x y => P x ∧ P y) c (fun _ _ => True))
    (hw : ∀ s, P s → WP isa c s F) : VG.Proof.Ed25519.Arm.CT (fun x y => P x ∧ P y) c (fun x y => F x ∧ F y) :=
  (hc.wp (fun x y h => ⟨hw x h.1, hw y h.2⟩)).mono (fun _ _ h => h) (fun _ _ h => h.2)

theorem ctBlockAppend {P R Q : State → State → Prop} {xs ys : List Instr}
    (hx : VG.Proof.Ed25519.Arm.CT P (.block xs) R) (hy : VG.Proof.Ed25519.Arm.CT R (.block ys) Q) : VG.Proof.Ed25519.Arm.CT P (.block (xs ++ ys)) Q := by
  intro x y tx ty u v hp ex ey
  have splitRun {s t : State} {tr : List Leak} (h : Exec isa (.block (xs ++ ys)) s tr t) :
      Exec isa (.seq (.block xs) (.block ys)) s tr t := by
    rw [Exec.block_iff, execBlock_append] at h
    obtain ⟨⟨a, ta⟩, ha, hb⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨b, tb⟩, hb', he⟩ := Option.map_eq_some_iff.mp hb
    cases he
    exact .seq (.block ha) (.block hb')
  exact RelCT.seq hx hy _ _ _ _ _ _ hp (splitRun ex) (splitRun ey)

theorem ctSeqAssoc {P Q : State → State → Prop} {a b c : Prog isa}
    (h : VG.Proof.Ed25519.Arm.CT P (.seq (.seq a b) c) Q) : VG.Proof.Ed25519.Arm.CT P (.seq a (.seq b c)) Q := by
  intro x y tx ty u v hp ex ey
  cases ex with
  | seq ea ex =>
    cases ex with
    | seq eb ec =>
      cases ey with
      | seq fa ey =>
        cases ey with
        | seq fb fc =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (Exec.seq (Exec.seq ea eb) ec) (Exec.seq (Exec.seq fa fb) fc)
          exact ⟨by simpa only [List.append_assoc] using ht, hq⟩

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.RecoverCTBlocks`. -/
section

/-! Straight-line and fixed-loop pieces of public point decoding. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

theorem r0_agree {b : BitVec 32} {x y : State} (hx : x.gpr .r0 = b) (hy : y.gpr .r0 = b) :
    ∀ r ∈ ([.r0] : List Reg), x.gpr r = y.gpr r := by
  intro r hr
  rw [List.mem_singleton] at hr
  subst r
  exact hx.trans hy.symm

theorem returnFlag_ct (b : Bool) :
    VG.Proof.Ed25519.Arm.CT (fun _ _ => True) (.block [.mov .r9 (.imm b.toNat)]) (fun _ _ => True) := by
  cases b <;> apply VG.Proof.Ed25519.Arm.ctRegs [] _ (by taint_decide)
  all_goals intro _ _ _ r h; exact (List.not_mem_nil h).elim

theorem recoverInvalid_ct : VG.Proof.Ed25519.Arm.CT (fun _ _ => True) recoverInvalid (fun _ _ => True) := VG.Proof.Ed25519.Arm.returnFlag_ct false

theorem recoverSuccess_ct (base : BitVec 32) :
    VG.Proof.Ed25519.Arm.CT (fun x y => x.gpr .r0 = base ∧ y.gpr .r0 = base) recoverSuccess (fun _ _ => True) := by
  apply VG.Proof.Ed25519.Arm.ctRegs [.r0] _ (by taint_decide)
  exact fun _ _ h => VG.Proof.Ed25519.Arm.r0_agree h.1 h.2

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.RecoverCTRoot`. -/
section

/-! Merged from `Proof.Ed25519.Arm.RecoverCTSign`. -/
section
/-! Merged from `Proof.Ed25519.Arm.RecoverCTAdjust`. -/
section
/-! The sign-adjustment branch depends only on the public coordinate and sign. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def SignCTPre (base : BitVec 32) (b : Bool) (x : Spec.X25519.Fe) (s : State) : Prop :=
  VG.Proof.Ed25519.Arm.Ctx base s ∧ AllLim s.mem base ∧
    s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 = BitVec.ofNat 32 b.toNat ∧ VG.Proof.Ed25519.Arm.env s.mem base 0 = x

theorem parityBlockCT_ok {s : State} {base : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx base s) (hl : AllLim s.mem base)
    (b : Bool) (hb : s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 = BitVec.ofNat 32 b.toNat) :
    WP isa (.block (freeze 0 ++ recoverParity)) s fun t =>
      VG.Proof.Ed25519.Arm.Ctx base t ∧ t.z = (((VG.Proof.Ed25519.Arm.env s.mem base 0).val % 2 == 1) == b) := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.Arm.freeze_ok hc hl 0) fun a ⟨ak, _, _, af, av⟩ => ?_
  refine WP.mono (recoverParity_ok (ak.ctx hc) b af (ak.sign.trans hb)) fun t ⟨tr, _, tz⟩ => ?_
  exact ⟨(ak.ctx hc).of_rest tr (by decide), by rw [tz, av]⟩

theorem adjustTail_ct :
    VG.Proof.Ed25519.Arm.CT (fun x y => x.gpr .r0 = y.gpr .r0 ∧ x.z = y.z)
      (.seq (.ite .eq (.block []) (fieldCode [.const 5 0, .sub 0 5 0])) recoverSuccess) (fun _ _ => True) := by
  refine RelCT.seq (R := fun (x y : State) => ∀ r ∈ ([.r0] : List Reg), x.gpr r = y.gpr r)
    (RelCT.ite (fun _ _ h => congrArg some h.2) ?_ ?_) ?_
  · apply VG.Proof.Ed25519.Arm.ctRegsKeeping [.r0] [.r0] _ (by taint_decide)
    intro x y h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.1
  · apply VG.Proof.Ed25519.Arm.ctRegsKeeping [.r0] [.r0] _ (by taint_decide)
    intro x y h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.1
  · apply VG.Proof.Ed25519.Arm.ctRegs [.r0] _ (by taint_decide)
    exact fun _ _ h => h

theorem recoverAdjustSign_ct (base : BitVec 32) (b : Bool) (x : Spec.X25519.Fe) :
    VG.Proof.Ed25519.Arm.CT (fun s t => VG.Proof.Ed25519.Arm.SignCTPre base b x s ∧ VG.Proof.Ed25519.Arm.SignCTPre base b x t) recoverAdjustSign (fun _ _ => True) := by
  have ht : VG.Proof.Ed25519.Arm.CT (fun s t => VG.Proof.Ed25519.Arm.SignCTPre base b x s ∧ VG.Proof.Ed25519.Arm.SignCTPre base b x t)
      (.block (freeze 0 ++ recoverParity)) (fun _ _ => True) := by
    apply VG.Proof.Ed25519.Arm.ctRegs [.r0] _ (by taint_decide)
    exact fun _ _ h => VG.Proof.Ed25519.Arm.r0_agree h.1.1.r0 h.2.1.r0
  have hw (s : State) (h : VG.Proof.Ed25519.Arm.SignCTPre base b x s) :
      WP isa (.block (freeze 0 ++ recoverParity)) s fun t =>
        VG.Proof.Ed25519.Arm.Ctx base t ∧ t.z = ((x.val % 2 == 1) == b) := by
    refine WP.mono (VG.Proof.Ed25519.Arm.parityBlockCT_ok h.1 h.2.1 b h.2.2.1) fun t ⟨hc, hz⟩ => ?_
    exact ⟨hc, by rw [hz, h.2.2.2]⟩
  have hp := (ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)).mono (fun _ _ h => h)
    (fun _ _ h => And.intro (h.2.1.1.r0.trans h.2.2.1.r0.symm) (h.2.1.2.trans h.2.2.2.symm))
  exact RelCT.seq hp VG.Proof.Ed25519.Arm.adjustTail_ct

end VG.Proof.Ed25519.Arm
end

/-! The negative-zero rejection depends only on the public coordinate and sign. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

theorem signTestThen_ct (base : BitVec 32) (b : Bool) (x : Spec.X25519.Fe) :
    VG.Proof.Ed25519.Arm.CT (fun s t => VG.Proof.Ed25519.Arm.SignCTPre base b x s ∧ VG.Proof.Ed25519.Arm.SignCTPre base b x t)
      (.seq (.block signTest) (.ite .ne recoverInvalid recoverAdjustSign)) (fun _ _ => True) := by
  have ht : VG.Proof.Ed25519.Arm.CT (fun s t => VG.Proof.Ed25519.Arm.SignCTPre base b x s ∧ VG.Proof.Ed25519.Arm.SignCTPre base b x t)
      (.block signTest) (fun _ _ => True) := by
    apply VG.Proof.Ed25519.Arm.ctRegs [.r0] _ (by taint_decide)
    exact fun _ _ h => VG.Proof.Ed25519.Arm.r0_agree h.1.1.r0 h.2.1.r0
  have hw (s : State) (h : VG.Proof.Ed25519.Arm.SignCTPre base b x s) :
      WP isa (.block signTest) s fun t => VG.Proof.Ed25519.Arm.SignCTPre base b x t ∧ t.z = !b := by
    refine WP.mono (signTest_ok h.1 b h.2.2.1) fun t ⟨tr, tm, tz⟩ => ?_
    exact ⟨⟨h.1.of_rest tr (by decide), tm ▸ h.2.1, tm ▸ h.2.2.1, tm ▸ h.2.2.2⟩, tz⟩
  refine RelCT.seq (ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)) (RelCT.ite ?_ ?_ ?_)
  · intro s t h
    simp only [VG.Arm.eval, h.2.1.2, h.2.2.2]
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact (VG.Proof.Ed25519.Arm.recoverAdjustSign_ct base b x).mono (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)

theorem recoverSign_ct (base : BitVec 32) (b : Bool) (x : Spec.X25519.Fe) :
    VG.Proof.Ed25519.Arm.CT (fun s t => VG.Proof.Ed25519.Arm.SignCTPre base b x s ∧ VG.Proof.Ed25519.Arm.SignCTPre base b x t) recoverSign (fun _ _ => True) := by
  have ht : VG.Proof.Ed25519.Arm.CT (fun s t => VG.Proof.Ed25519.Arm.SignCTPre base b x s ∧ VG.Proof.Ed25519.Arm.SignCTPre base b x t)
      (fieldZero 0) (fun _ _ => True) := by
    apply VG.Proof.Ed25519.Arm.ctRegs [.r0] _ (by taint_decide)
    exact fun _ _ h => VG.Proof.Ed25519.Arm.r0_agree h.1.1.r0 h.2.1.r0
  have hw (s : State) (h : VG.Proof.Ed25519.Arm.SignCTPre base b x s) :
      WP isa (fieldZero 0) s fun t => VG.Proof.Ed25519.Arm.SignCTPre base b x t ∧ t.z = decide (x = 0) := by
    refine WP.mono (fieldZero_ok h.1 h.2.1 0) fun t ⟨tk, tl, te, tz⟩ => ?_
    refine ⟨⟨tk.ctx h.1, tl, tk.sign.trans h.2.2.1, ?_⟩, ?_⟩
    · rw [te]; exact h.2.2.2
    · rw [tz, h.2.2.2]
  rw [recoverSign]
  refine RelCT.seq (ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)) (RelCT.ite ?_ ?_ ?_)
  · exact fun _ _ h => congrArg some (h.2.1.2.trans h.2.2.2.symm)
  · exact (VG.Proof.Ed25519.Arm.signTestThen_ct base b x).mono (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)
  · exact (VG.Proof.Ed25519.Arm.recoverAdjustSign_ct base b x).mono (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)

end VG.Proof.Ed25519.Arm
end

/-! Candidate validation branches only on the public encoded coordinate. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

def RootCTState (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) (s : State) : Prop :=
  VG.Proof.Ed25519.Arm.SignCTPre base b (rootX y) s ∧ VG.Proof.Ed25519.Arm.env s.mem base 11 = rootV y * rootX y * rootX y ∧
    VG.Proof.Ed25519.Arm.env s.mem base 6 = rootU y ∧ VG.Proof.Ed25519.Arm.env s.mem base 12 = 0 - rootU y

def rootCheckValue (y : Spec.X25519.Fe) (minus : Bool) : Bool :=
  decide (rootV y * rootX y * rootX y = if minus then 0 - rootU y else rootU y)

theorem rootCheck_ct (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) (minus : Bool) :
    VG.Proof.Ed25519.Arm.CT (fun s t => VG.Proof.Ed25519.Arm.RootCTState base b y s ∧ VG.Proof.Ed25519.Arm.RootCTState base b y t)
      (fieldEqual 11 (if minus then 12 else 6))
      (fun s t => (VG.Proof.Ed25519.Arm.RootCTState base b y s ∧ s.z = VG.Proof.Ed25519.Arm.rootCheckValue y minus) ∧
        (VG.Proof.Ed25519.Arm.RootCTState base b y t ∧ t.z = VG.Proof.Ed25519.Arm.rootCheckValue y minus)) := by
  apply VG.Proof.Ed25519.Arm.ctBoth
  · cases minus
    · apply VG.Proof.Ed25519.Arm.ctRegs [.r0] _ (by taint_decide)
      exact fun _ _ h => VG.Proof.Ed25519.Arm.r0_agree h.1.1.1.r0 h.2.1.1.r0
    · apply VG.Proof.Ed25519.Arm.ctRegs [.r0] _ (by taint_decide)
      exact fun _ _ h => VG.Proof.Ed25519.Arm.r0_agree h.1.1.1.r0 h.2.1.1.r0
  · intro s h
    refine WP.mono (fieldEqual_ok h.1.1 h.1.2.1 11 (if minus then 12 else 6)) fun t ⟨kt, lt, te, tz⟩ => ?_
    refine ⟨⟨⟨kt.ctx h.1.1, lt, kt.sign.trans h.1.2.2.1,
      (te 0 (by decide)).trans h.1.2.2.2⟩, (te 11 (by decide)).trans h.2.1,
      (te 6 (by decide)).trans h.2.2.1, (te 12 (by decide)).trans h.2.2.2⟩, ?_⟩
    rw [tz, VG.Proof.Ed25519.Arm.rootCheckValue, h.2.1]
    cases minus <;> simp only [Bool.false_eq_true, ite_false, ite_true, h.2.2.1, h.2.2.2]

theorem rootAdjustSign_ct (base : BitVec 32) (b : Bool) (x : Spec.X25519.Fe) :
    VG.Proof.Ed25519.Arm.CT (fun s t => VG.Proof.Ed25519.Arm.SignCTPre base b x s ∧ VG.Proof.Ed25519.Arm.SignCTPre base b x t)
      (.seq (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18]) recoverSign) (fun _ _ => True) := by
  have hp : VG.Proof.Ed25519.Arm.CT (fun s t => VG.Proof.Ed25519.Arm.SignCTPre base b x s ∧ VG.Proof.Ed25519.Arm.SignCTPre base b x t)
      (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])
      (fun s t => VG.Proof.Ed25519.Arm.SignCTPre base b (x * Spec.Ed25519.sqrtM1) s ∧ VG.Proof.Ed25519.Arm.SignCTPre base b (x * Spec.Ed25519.sqrtM1) t) := by
    apply VG.Proof.Ed25519.Arm.ctBoth
    · apply VG.Proof.Ed25519.Arm.ctRegs [.r0] _ (by taint_decide)
      exact fun _ _ h => VG.Proof.Ed25519.Arm.r0_agree h.1.1.r0 h.2.1.r0
    · intro s h
      refine WP.mono (fieldCode_ok [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18] h.1 h.2.1)
        fun t ⟨kt, lt, te⟩ => ?_
      refine ⟨kt.ctx h.1, lt, kt.sign.trans h.2.2.1, ?_⟩
      rw [te]
      change VG.Proof.Ed25519.Arm.env s.mem base 0 * Spec.Ed25519.sqrtM1 = _
      rw [h.2.2.2]
  exact RelCT.seq hp (VG.Proof.Ed25519.Arm.recoverSign_ct base b (x * Spec.Ed25519.sqrtM1))

theorem recoverMinus_ct (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) :
    VG.Proof.Ed25519.Arm.CT (fun s t => VG.Proof.Ed25519.Arm.RootCTState base b y s ∧ VG.Proof.Ed25519.Arm.RootCTState base b y t)
      (.seq (fieldEqual 11 12) (.ite .eq
        (.seq (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18]) recoverSign) recoverInvalid)) (fun _ _ => True) := by
  refine RelCT.seq (VG.Proof.Ed25519.Arm.rootCheck_ct base b y true) (RelCT.ite ?_ ?_ ?_)
  · exact fun _ _ h => congrArg some (h.1.2.trans h.2.2.symm)
  · exact (VG.Proof.Ed25519.Arm.rootAdjustSign_ct base b (rootX y)).mono
      (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem recoverChecks_ct (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) :
    VG.Proof.Ed25519.Arm.CT (fun s t => VG.Proof.Ed25519.Arm.RootCTState base b y s ∧ VG.Proof.Ed25519.Arm.RootCTState base b y t)
      (.seq (fieldEqual 11 6) (.ite .eq recoverSign
        (.seq (fieldEqual 11 12) (.ite .eq
          (.seq (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18]) recoverSign) recoverInvalid)))) (fun _ _ => True) := by
  refine RelCT.seq (VG.Proof.Ed25519.Arm.rootCheck_ct base b y false) (RelCT.ite ?_ ?_ ?_)
  · exact fun _ _ h => congrArg some (h.1.2.trans h.2.2.symm)
  · exact (VG.Proof.Ed25519.Arm.recoverSign_ct base b (rootX y)).mono (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) (fun _ _ h => h)
  · exact (VG.Proof.Ed25519.Arm.recoverMinus_ct base b y).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) (fun _ _ h => h)

def RecoverCTPre (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) (s : State) : Prop :=
  VG.Proof.Ed25519.Arm.Ctx base s ∧ AllLim s.mem base ∧
    s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 = BitVec.ofNat 32 b.toNat ∧ VG.Proof.Ed25519.Arm.env s.mem base 1 = y

theorem recoverPoint_ct (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) :
    VG.Proof.Ed25519.Arm.CT (fun s t => VG.Proof.Ed25519.Arm.RecoverCTPre base b y s ∧ VG.Proof.Ed25519.Arm.RecoverCTPre base b y t) recoverPoint (fun _ _ => True) := by
  have hp : VG.Proof.Ed25519.Arm.CT (fun s t => VG.Proof.Ed25519.Arm.RecoverCTPre base b y s ∧ VG.Proof.Ed25519.Arm.RecoverCTPre base b y t)
      recoverCandidate (fun s t => VG.Proof.Ed25519.Arm.RootCTState base b y s ∧ VG.Proof.Ed25519.Arm.RootCTState base b y t) := by
    apply VG.Proof.Ed25519.Arm.ctBoth
    · apply VG.Proof.Ed25519.Arm.ctRegs [.r0] _ (by taint_decide)
      exact fun _ _ h => VG.Proof.Ed25519.Arm.r0_agree h.1.1.r0 h.2.1.r0
    · intro s h
      refine WP.mono (recoverCandidate_ok h.1 h.2.1) fun t ⟨kt, lt, tx, _, _, tu, _, tv, tn⟩ => ?_
      refine ⟨⟨kt.ctx h.1, lt, kt.sign.trans h.2.2.1, ?_⟩, ?_, ?_, ?_⟩
      · rw [tx, h.2.2.2]
      · rw [tv, h.2.2.2]
      · rw [tu, h.2.2.2]
      · rw [tn, h.2.2.2]
  exact RelCT.seq hp (VG.Proof.Ed25519.Arm.recoverChecks_ct base b y)

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTLit`. -/
section

/-! The point arithmetic and the inversion chain as literals
(`materialize_value`, `materialize_code`), which the literals of the code
that contains them read rather than build each field multiplication again. -/
namespace VG.Impl.Ed25519.Arm

materialize_code pointAdd
materialize_code pointDouble
materialize_code power250
materialize_code VG.Impl.Ed25519.Arm.invert
materialize_code VG.Impl.Ed25519.Arm.rootPower

end VG.Impl.Ed25519.Arm

namespace VG.Impl.Ed25519.Arm
materialize_code prepareBatch
materialize_code accumulate16
materialize_code pointEncode
materialize_code powers32CT := pointPowers 1600 32 true
materialize_code powers16CT := pointPowers 1600 16 true
materialize_code identityCT := constPoint Spec.Ed25519.identity
materialize_code basePointCT := constPoint Spec.Ed25519.basePoint
end VG.Impl.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTBody`. -/
section

/-! Merged from `Proof.Ed25519.Arm.ScalarBaseCTBits`. -/
section
/-! Reloading the scalar pointer and batch index restores their public values. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def BitsCTPre (b p : BitVec 32) (j : Nat) (s : State) : Prop :=
  VG.Proof.Ed25519.Arm.Ctx b s ∧ s.mem.readW (State.addr b + BitVec.ofNat 64 52) 32 = p ∧
    s.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 j

theorem batchBits_ct (b p : BitVec 32) (j : Nat) :
    VG.Proof.Ed25519.Arm.CT (fun x y => VG.Proof.Ed25519.Arm.BitsCTPre b p j x ∧ VG.Proof.Ed25519.Arm.BitsCTPre b p j y)
      (.block batchBits) (fun x y => ∀ r ∈ ([.r0] : List Reg), x.gpr r = y.gpr r) := by
  let head : List Instr := [.ldr .r12 .r0 52, .ldr .r2 .r0 56]
  have hh : VG.Proof.Ed25519.Arm.CT (fun x y => VG.Proof.Ed25519.Arm.BitsCTPre b p j x ∧ VG.Proof.Ed25519.Arm.BitsCTPre b p j y)
      (.block head) (fun x y => (x.gpr .r0 = b ∧ x.gpr .r12 = p ∧ x.gpr .r2 = BitVec.ofNat 32 j) ∧
        (y.gpr .r0 = b ∧ y.gpr .r12 = p ∧ y.gpr .r2 = BitVec.ofNat 32 j)) := by
    apply VG.Proof.Ed25519.Arm.ctBoth
    · dsimp only [head]
      apply VG.Proof.Ed25519.Arm.ctRegs [.r0] _ (by taint_decide)
      intro x y h r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.1.1.r0.trans h.2.1.r0.symm
    · intro s ⟨hc, hp, hj⟩
      refine ldr0_ok hc (by decide) fun u hu =>
        ldr0_ok (hc.of_rest (hu.rest (ws := [.r12]) (by decide)) (by decide)) (by decide)
          fun t ht => WP.block_nil ?_
      refine ⟨(ht.other _ (by decide)).trans ((hu.other _ (by decide)).trans hc.r0),
        (ht.other _ (by decide)).trans (hu.gpr.trans hp), ?_⟩
      rw [ht.gpr, hu.mem]
      exact hj
  change VG.Proof.Ed25519.Arm.CT _ (.block (head ++
    (([.dp .add .r12 .r12 (.shifted .r2 .lsl 1)] : List Instr) ++ unpackSrc 0 0 ++ expandBits))) _
  refine VG.Proof.Ed25519.Arm.ctBlockAppend hh ?_
  dsimp only [head]
  apply VG.Proof.Ed25519.Arm.ctRegsKeeping [.r0, .r12, .r2] [.r0] _ (by taint_decide)
  intro x y h r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.1.1.trans h.2.1.symm
  · exact h.1.2.1.trans h.2.2.1.symm
  · exact h.1.2.2.trans h.2.2.2.symm

end VG.Proof.Ed25519.Arm
end

/-! Each batch uses the same public checkpoint and scalar-byte addresses. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def BodyCTPre (b p : BitVec 32) (j : Nat) (s : State) : Prop :=
  VG.Proof.Ed25519.Arm.Ctx b s ∧ AllLim s.mem b ∧ s.mem.readW (State.addr b + BitVec.ofNat 64 52) 32 = p ∧
    s.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 (j + 1) ∧
    env s.mem b 16 = Spec.Ed25519.d

def BodyCTReady (b p : BitVec 32) (j : Nat) (s : State) : Prop :=
  VG.Proof.Ed25519.Arm.Ctx b s ∧ AllLim s.mem b ∧ s.mem.readW (State.addr b + BitVec.ofNat 64 52) 32 = p ∧
    s.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 j ∧
    env s.mem b 16 = Spec.Ed25519.d ∧ s.gpr .r11 = BitVec.ofNat 32 j

theorem batchStart_ct (b p : BitVec 32) (j : Nat) :
    VG.Proof.Ed25519.Arm.CT (fun x y => VG.Proof.Ed25519.Arm.BodyCTPre b p j x ∧ VG.Proof.Ed25519.Arm.BodyCTPre b p j y)
      (.block batchStart) (fun x y => VG.Proof.Ed25519.Arm.BodyCTReady b p j x ∧ VG.Proof.Ed25519.Arm.BodyCTReady b p j y) := by
  apply VG.Proof.Ed25519.Arm.ctBoth
  · apply VG.Proof.Ed25519.Arm.ctRegs [.r0] _ (by taint_decide)
    intro x y h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.1.r0.trans h.2.1.r0.symm
  · intro s ⟨hc, hl, hi, hj, hd⟩
    refine WP.mono (VG.Proof.Ed25519.Arm.batchStart_ok hc j hj) fun t ⟨tr, tf, tv, tc⟩ => ?_
    have tk : VG.Proof.Ed25519.Arm.MulKeep b 5696 2048 s t := MulKeep.of_counter tr (by decide) tf
    exact ⟨tk.ctx hc, VG.Proof.Ed25519.Arm.smallFrame_lim tf (by decide) hl, (tk.word (by decide) (by decide) 52 (.inr rfl)).trans hi, tc,
      (congrFun (VG.Proof.Ed25519.Arm.smallFrame_env tf (by decide)) 16).trans hd, tv⟩

theorem prepareBatch_ct (b p : BitVec 32) (j : Nat) (hj : j < 32) :
    VG.Proof.Ed25519.Arm.CT (fun x y => VG.Proof.Ed25519.Arm.BodyCTReady b p j x ∧ VG.Proof.Ed25519.Arm.BodyCTReady b p j y)
      prepareBatch (fun x y => VG.Proof.Ed25519.Arm.BitsCTPre b p j x ∧ VG.Proof.Ed25519.Arm.BitsCTPre b p j y) := by
  apply VG.Proof.Ed25519.Arm.ctBoth
  · apply VG.Proof.Ed25519.Arm.ctRegs [.r0, .r11] _ (by taint_decide)
    intro x y h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.r0.trans h.2.1.r0.symm
    · exact h.1.2.2.2.2.2.trans h.2.2.2.2.2.2.symm
  · intro s ⟨hc, hl, hi, hcj, hd, hv⟩
    refine WP.mono (VG.Proof.Ed25519.Arm.prepareBatch_ok hc hl j hj hv hd) fun t ⟨tk, _, _, _, _⟩ => ?_
    exact ⟨tk.ctx hc, ((MulKeep.of_powers tk).word (by decide) (by decide) 52 (.inr rfl)).trans hi,
      (tk.counter (by decide) (by decide)).trans hcj⟩

theorem pointMulBody_ct (b p : BitVec 32) (j : Nat) (hj : j < 32) :
    VG.Proof.Ed25519.Arm.CT (fun x y => VG.Proof.Ed25519.Arm.BodyCTPre b p j x ∧ VG.Proof.Ed25519.Arm.BodyCTPre b p j y)
      pointMulBody (fun _ _ => True) := by
  rw [pointMulBody]
  refine RelCT.seq (VG.Proof.Ed25519.Arm.batchStart_ct b p j)
    (RelCT.seq (VG.Proof.Ed25519.Arm.prepareBatch_ct b p j hj) (RelCT.seq (VG.Proof.Ed25519.Arm.batchBits_ct b p j) ?_))
  apply VG.Proof.Ed25519.Arm.ctRegs [.r0] _ (by taint_decide)
  intro x y h
  exact h

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTMul`. -/
section

/-! Merged from `Proof.Ed25519.Arm.ScalarBaseCTInit`. -/
section
/-! Merged from `Proof.Ed25519.Arm.ScalarBaseCTLoop`. -/
section
/-! Both runs descend through the same public checkpoint count. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem pointMulLoop_ct (s₁ s₂ : State) (b ptr : BitVec 32) (count scalar₁ scalar₂ : Nat)
    (p₁ p₂ : Spec.Ed25519.Point) (n : Nat) :
    VG.Proof.Ed25519.Arm.CT (fun x y => VG.Proof.Ed25519.Arm.PointMulInv s₁ b ptr count scalar₁ p₁ n x ∧
      VG.Proof.Ed25519.Arm.PointMulInv s₂ b ptr count scalar₂ p₂ n y) (.loop pointMulBody .ne) (fun _ _ => True) := by
  apply RelCT.loop (M := isa) (fun n x y => VG.Proof.Ed25519.Arm.PointMulInv s₁ b ptr count scalar₁ p₁ n x ∧
    VG.Proof.Ed25519.Arm.PointMulInv s₂ b ptr count scalar₂ p₂ n y) _ n
  intro k
  cases k with
  | zero =>
    apply RelCT.of_false
    intro x y h
    exact Nat.not_lt_zero _ h.1.positive
  | succ j =>
    by_cases hj : j < count ∧ count ≤ 32
    · have hc := (VG.Proof.Ed25519.Arm.pointMulBody_ct b ptr j (by omega)).mono
        (fun x y (h : VG.Proof.Ed25519.Arm.PointMulInv s₁ b ptr count scalar₁ p₁ (j + 1) x ∧
            VG.Proof.Ed25519.Arm.PointMulInv s₂ b ptr count scalar₂ p₂ (j + 1) y) =>
          ⟨⟨h.1.ctx, h.1.lim, h.1.input.pointer, h.1.counter, h.1.d⟩,
           ⟨h.2.ctx, h.2.lim, h.2.input.pointer, h.2.counter, h.2.d⟩⟩)
        (fun _ _ h => h)
      intro x y tx ty u v h ex ey
      have he := (hc _ _ _ _ _ _ h ex ey).1
      obtain ⟨_, u', eu, hu⟩ := VG.Proof.Ed25519.Arm.pointMulBody_ok h.1.ctx h.1.lim count scalar₁ j p₁ h.1.input
        hj.1 h.1.d h.1.value h.1.counter (h.1.table j hj.1)
      obtain ⟨_, v', ev, hv⟩ := VG.Proof.Ed25519.Arm.pointMulBody_ok h.2.ctx h.2.lim count scalar₂ j p₂ h.2.input
        hj.1 h.2.d h.2.value h.2.counter (h.2.table j hj.1)
      obtain ⟨_, rfl⟩ := Exec.det ex eu
      obtain ⟨_, rfl⟩ := Exec.det ey ev
      have ez : VG.Arm.eval .ne u = VG.Arm.eval .ne v := by
        simp only [VG.Arm.eval, hu.2.2.2.2.2, hv.2.2.2.2.2]
      refine ⟨he, ez, fun _ => trivial, ?_⟩
      intro hj0
      have hnz : j ≠ 0 := by
        intro hz
        subst j
        simp only [VG.Arm.eval, hu.2.2.2.2.2, decide_true, Bool.not_true] at hj0
        cases hj0
      refine ⟨j, by omega, ?_, ?_⟩
      · refine ⟨by omega, by omega, hu.1.ctx h.1.ctx, hu.2.1,
          h.1.input.keep hu.1 (by decide) (by decide), hu.2.2.2.2.1,
          hu.2.2.1, hu.2.2.2.1, ?_, h.1.keep.trans hu.1⟩
        intro i hi
        exact (hu.1.table (by omega) (by omega) (by decide) (.inl (by omega))).trans (h.1.table i hi)
      · refine ⟨by omega, by omega, hv.1.ctx h.2.ctx, hv.2.1,
          h.2.input.keep hv.1 (by decide) (by decide), hv.2.2.2.2.1,
          hv.2.2.1, hv.2.2.2.1, ?_, h.2.keep.trans hv.1⟩
        intro i hi
        exact (hv.1.table (by omega) (by omega) (by decide) (.inl (by omega))).trans (h.2.table i hi)
    · apply RelCT.of_false
      intro x y h
      have := h.1.bound
      have := h.1.input.bound
      omega

end VG.Proof.Ed25519.Arm
end

/-! Checked initialization of the public descending loop. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def pointMultiplyInitCT (count : Nat) : Prog isa :=
  .seq (pointPowers 1600 count true) (.seq (constPoint Spec.Ed25519.identity)
    (.block [.movw .r11 (BitVec.ofNat 16 count), .str .r11 .r0 56]))

theorem pointMultiplyInitCT_ok {b ptr : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hl : AllLim s.mem b)
    (count scalar : Nat) (hi : VG.Proof.Ed25519.Arm.MulInput b ptr count scalar s) (hn : 0 < count)
    (hd : env s.mem b 16 = Spec.Ed25519.d) :
    WP isa (VG.Proof.Ed25519.Arm.pointMultiplyInitCT count) s fun t =>
      VG.Proof.Ed25519.Arm.PointMulInv t b ptr count scalar (point (env s.mem b) 0 1 2 3) count t := by
  let p := point (env s.mem b) 0 1 2 3
  have hs : scalar < 2 ^ (16 * count) := by
    rw [← hi.value]
    exact val16_lt (fun k _ => packedLimb_lt _ _ k)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.pointPowers_ok true hc hl 1600 count (by decide)
    (by have := hi.bound; omega) hn hi.bound hd) fun a ⟨al, ats, _, ah, ak⟩ => ?_)
  have kam : VG.Proof.Ed25519.Arm.MulKeep b 1600 6144 s a := (MulKeep.of_powers ak).mono (by decide) (by have := hi.bound; omega)
  refine WP.seq (WP.mono (fieldCode_ok (constPointOps Spec.Ed25519.identity) (kam.ctx hc) al)
    fun u ⟨uk, ul, ue⟩ => ?_)
  have kum : VG.Proof.Ed25519.Arm.MulKeep b 1600 6144 s u := kam.trans (MulKeep.of_powers (PowersKeep.of_keep uk))
  have ud : env u.mem b 16 = Spec.Ed25519.d := by rw [ue, VG.Proof.Ed25519.Arm.constPoint_d, ah 16 (by decide), hd]
  have up : point (env u.mem b) 0 1 2 3 = after scalar p (16 * count) :=
    ((congrArg (fun e => point e 0 1 2 3) ue).trans (constPoint_eval _ _)).trans
      (after_top scalar (16 * count) p hs).symm
  have ut : ∀ j < count, tablePoint u.mem b (1600 + 128 * j) = powerPoint p (16 * j) := by
    intro j hj
    have := hi.bound
    exact (workspace_tablePoint uk.frame (by omega) (by omega)).trans (ats j hj)
  refine wp_movw fun v hv => ?_
  have vc : v.gpr .r11 = BitVec.ofNat 32 count := by
    apply BitVec.eq_of_toNat_eq
    rw [hv.gpr, movw_nat (by have := hi.bound; omega), toNat_imm (by have := hi.bound; omega)]
  have kvm : VG.Proof.Ed25519.Arm.MulKeep b 1600 6144 s v := kum.trans
    (MulKeep.of_rest (hv.rest (ws := [.r11]) (by decide)) (by decide) hv.mem)
  refine WP.mono (VG.Proof.Ed25519.Arm.counterStore_ok (kvm.ctx hc) count vc) fun w ⟨wr, wf, wc⟩ => ?_
  have kwm : VG.Proof.Ed25519.Arm.MulKeep b 1600 6144 s w := kvm.trans (MulKeep.of_counter wr (by decide) wf)
  have we : env w.mem b = env u.mem b := (VG.Proof.Ed25519.Arm.smallFrame_env wf (by decide)).trans
    (congrArg (fun m => env m b) hv.mem)
  have wl : AllLim w.mem b := VG.Proof.Ed25519.Arm.smallFrame_lim wf (by decide) (by rw [hv.mem]; exact ul)
  refine ⟨hn, Nat.le_refl _, kwm.ctx hc, wl,
    hi.keep kwm (by decide) (by decide), wc, (congrFun we 16).trans ud,
    (congrArg (fun e => point e 0 1 2 3) we).trans up, ?_, MulKeep.refl _ _ _ _⟩
  intro j hj
  have := hi.bound
  exact (VG.Proof.Ed25519.Arm.smallFrame_table wf (by decide) (by omega) (by omega)).trans
    ((congrArg (fun m => tablePoint m b (1600 + 128 * j)) hv.mem).trans (ut j hj))

end VG.Proof.Ed25519.Arm
end

/-! Public initialization and synchronized batches prove scalar multiplication constant time. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

materialize_code mulInit16CT := VG.Proof.Ed25519.Arm.pointMultiplyInitCT 16
materialize_code mulInit32CT := VG.Proof.Ed25519.Arm.pointMultiplyInitCT 32

def MulCTPre (b ptr : BitVec 32) (count scalar : Nat) (s : State) : Prop :=
  VG.Proof.Ed25519.Arm.Ctx b s ∧ AllLim s.mem b ∧ VG.Proof.Ed25519.Arm.MulInput b ptr count scalar s ∧ env s.mem b 16 = Spec.Ed25519.d

theorem pointMultiply_ct (b ptr : BitVec 32) (count scalar₁ scalar₂ : Nat)
    (hn : count = 16 ∨ count = 32) :
    VG.Proof.Ed25519.Arm.CT (fun x y => VG.Proof.Ed25519.Arm.MulCTPre b ptr count scalar₁ x ∧ VG.Proof.Ed25519.Arm.MulCTPre b ptr count scalar₂ y)
      (pointMultiply count) (fun _ _ => True) := by
  have hn0 : 0 < count := by rcases hn with rfl | rfl <;> decide
  have hi : VG.Proof.Ed25519.Arm.CT (fun x y => VG.Proof.Ed25519.Arm.MulCTPre b ptr count scalar₁ x ∧ VG.Proof.Ed25519.Arm.MulCTPre b ptr count scalar₂ y)
      (VG.Proof.Ed25519.Arm.pointMultiplyInitCT count) (fun _ _ => True) := by
    have hr : ∀ x y, (VG.Proof.Ed25519.Arm.MulCTPre b ptr count scalar₁ x ∧ VG.Proof.Ed25519.Arm.MulCTPre b ptr count scalar₂ y) →
        ∀ r ∈ ([.r0] : List Reg), x.gpr r = y.gpr r := by
      intro x y h r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.1.1.r0.trans h.2.1.r0.symm
    rcases hn with rfl | rfl
    · exact VG.Proof.Ed25519.Arm.ctRegs [.r0] hr (by taint_decide)
    · exact VG.Proof.Ed25519.Arm.ctRegs [.r0] hr (by taint_decide)
  intro x y tx ty u v h ex ey
  cases ex with
  | seq ep ex =>
    cases ex with
    | seq ec ex =>
      cases ex with
      | seq ei el =>
        cases ey with
        | seq fp ey =>
          cases ey with
          | seq fc ey =>
            cases ey with
            | seq fi fl =>
              have exi := Exec.seq ep (Exec.seq ec ei)
              have eyi := Exec.seq fp (Exec.seq fc fi)
              have ht := (hi _ _ _ _ _ _ h exi eyi).1
              obtain ⟨_, a, ea, ha⟩ := VG.Proof.Ed25519.Arm.pointMultiplyInitCT_ok h.1.1 h.1.2.1 count scalar₁ h.1.2.2.1 hn0 h.1.2.2.2
              obtain ⟨_, b', eb, hb⟩ := VG.Proof.Ed25519.Arm.pointMultiplyInitCT_ok h.2.1 h.2.2.1 count scalar₂ h.2.2.2.1 hn0 h.2.2.2.2
              obtain ⟨_, rfl⟩ := Exec.det exi ea
              obtain ⟨_, rfl⟩ := Exec.det eyi eb
              have hl := (VG.Proof.Ed25519.Arm.pointMulLoop_ct _ _ b ptr count scalar₁ scalar₂ _ _ count _ _ _ _ _ _
                ⟨ha, hb⟩ el fl).1
              exact ⟨by simpa only [List.append_assoc] using congrArg₂ (fun (a b : List Leak) => a ++ b) ht hl, trivial⟩

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTFrom`. -/
section

/-! Public scalar pointers remain public across point preparation. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def pointFromPrepareCT : Prog isa :=
  .seq (.block [.str .r12 .r0 52]) (fieldCode [.const 16 Spec.Ed25519.d])

def FromCTPre (base ptr : BitVec 32) (count : Nat) (s : State) : Prop :=
  VG.Proof.Ed25519.Arm.Ctx base s ∧ AllLim s.mem base ∧ s.gpr .r12 = ptr ∧ ptr.toNat + 2 * count ≤ 2 ^ 32 ∧
    (∀ i < 2 * count, InRegions (s.rd ++ s.wr) (State.addr ptr + BitVec.ofNat 64 i) 1) ∧
    (⟨State.addr ptr, 2 * count⟩ : Region).Disjoint ⟨State.addr base, 8192⟩

theorem pointFromPrepareCT_ok {s : State} {base ptr : BitVec 32}
    (count : Nat) (hn : count ≤ 32) (h : VG.Proof.Ed25519.Arm.FromCTPre base ptr count s) :
    WP isa VG.Proof.Ed25519.Arm.pointFromPrepareCT s (VG.Proof.Ed25519.Arm.MulCTPre base ptr count
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) (2 * count)))) := by
  obtain ⟨hc, hl, hp, hfit, hr, hsep⟩ := h
  refine WP.seq (str0_ok hc (by decide) fun u hu => WP.block_nil ?_)
  have uf : Frame [⟨State.addr base + BitVec.ofNat 64 52, 4⟩] s.mem u.mem := by
    rw [hu.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have uk : VG.Proof.Ed25519.Arm.PointKeep base s u := PointKeep.of_small (hu.rest []) (by decide) uf (by decide) (by decide)
  have ue := VG.Proof.Ed25519.Arm.smallFrame_env uf (by decide)
  have ui : VG.Proof.Ed25519.Arm.MulInput base ptr count (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) (2 * count))) u := by
    refine ⟨hn, hfit, ?_, hsep, ?_, ?_⟩
    · intro i hi
      rw [hu.rd, hu.wr]
      exact hr i hi
    · rw [hu.mem, Mem.readW_writeW_self32, hp]
    · exact (VG.Proof.Ed25519.Arm.packedDigits_frame uf hn (fun r hm => by
        rw [List.mem_singleton.mp hm]; exact hsep.sub_right (Offset.sub_base _ (by decide)))).trans
        (VG.Proof.Ed25519.Arm.packedDigits_decode _ _ count)
  refine WP.mono (fieldCode_ok [.const 16 Spec.Ed25519.d] (uk.ctx hc)
    (VG.Proof.Ed25519.Arm.smallFrame_lim uf (by decide) hl)) fun v ⟨vk, vl, ve⟩ => ?_
  have vm : VG.Proof.Ed25519.Arm.MulKeep base 1600 6144 u v := MulKeep.of_powers (PowersKeep.of_keep vk)
  have vd : env v.mem base 16 = Spec.Ed25519.d := by rw [ve]; rfl
  exact ⟨vk.ctx (uk.ctx hc), vl, ui.keep vm (by decide) (by decide), vd⟩

theorem pointFromScalar_ct (base ptr : BitVec 32) (count : Nat) (hn : count = 16 ∨ count = 32) :
    VG.Proof.Ed25519.Arm.CT (fun x y => VG.Proof.Ed25519.Arm.FromCTPre base ptr count x ∧ VG.Proof.Ed25519.Arm.FromCTPre base ptr count y)
      (pointFromScalar count) (fun _ _ => True) := by
  have hc : VG.Proof.Ed25519.Arm.CT (fun x y => VG.Proof.Ed25519.Arm.FromCTPre base ptr count x ∧ VG.Proof.Ed25519.Arm.FromCTPre base ptr count y)
      VG.Proof.Ed25519.Arm.pointFromPrepareCT (fun _ _ => True) := by
    apply VG.Proof.Ed25519.Arm.ctRegs [.r0, .r12] _ (by taint_decide)
    intro x y h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.r0.trans h.2.1.r0.symm
    · exact h.1.2.2.1.trans h.2.2.2.1.symm
  have hb : count ≤ 32 := by rcases hn with rfl | rfl <;> decide
  intro x y tx ty u v h ex ey
  cases ex with
  | seq es ex =>
    cases ex with
    | seq ef em =>
      cases ey with
      | seq fs ey =>
        cases ey with
        | seq ff fm =>
          have exi := Exec.seq es ef
          have eyi := Exec.seq fs ff
          have ht := (hc _ _ _ _ _ _ h exi eyi).1
          obtain ⟨_, a, ea, ha⟩ := VG.Proof.Ed25519.Arm.pointFromPrepareCT_ok count hb h.1
          obtain ⟨_, b, eb, hb⟩ := VG.Proof.Ed25519.Arm.pointFromPrepareCT_ok count hb h.2
          obtain ⟨_, rfl⟩ := Exec.det exi ea
          obtain ⟨_, rfl⟩ := Exec.det eyi eb
          have hm := (VG.Proof.Ed25519.Arm.pointMultiply_ct base ptr count _ _ hn _ _ _ _ _ _ ⟨ha, hb⟩ em fm).1
          exact ⟨by simpa only [List.append_assoc] using congrArg₂ (fun (a b : List Leak) => a ++ b) ht hm, trivial⟩

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.ScalarFinish`. -/
section

/-! Canonical scalar output and restoration of the saved registers. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

abbrev scalarFinishClob : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem scalarFinish_ok {b p : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s)
    (hl : Lim s.mem (State.addr b) SR) (hp : s.mem.readW (State.addr b + 32) 32 = p)
    (hfit : p.toNat + 32 ≤ 2 ^ 32) (hw : (⟨State.addr p, 32⟩ : Region) ∈ s.wr)
    (hsep : (⟨State.addr p, 32⟩ : Region).Disjoint ⟨State.addr b, 8192⟩)
    {g : Reg → BitVec 32} (hs : ScalarSaved (State.addr b) g s.mem) :
    WP isa (.block scalarFinish) s fun t =>
      (∀ i < 8, t.gpr (scalarSavedReg i) = g (scalarSavedReg i)) ∧ Rest VG.Proof.Ed25519.Arm.scalarFinishClob s t ∧
      Frame [⟨State.addr p, 32⟩] s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr p) 32 = Spec.Ed25519.encodeLE 32 (V s.mem (State.addr b) SR) := by
  rw [scalarFinish, List.append_assoc]
  simp only [List.cons_append, List.nil_append]
  refine ldr0_ok hc (by decide) fun u hu => ?_
  have hcu := hc.of_rest (hu.rest (ws := [.r12]) (by decide)) (by decide)
  refine WP.append (packField_ok (p := p) (a := SR) (dst := 0) hcu (by decide) (hu.mem ▸ hl) (by decide)
    (hu.gpr.trans hp) (by omega)
    (fun i hi => by rw [hu.wr]; simpa only [Nat.zero_add] using in_base hw (by omega) (by omega))
    (by simpa only [BitVec.add_zero] using
      hsep.symm.sub_left (Offset.sub_base _ (by decide : SR + 64 ≤ 8192))))
    fun v ⟨kv, fv, vv⟩ => ?_
  have hcv := hcu.of_rest kv (by decide)
  have hs' : ScalarSaved (State.addr b) g v.mem :=
    (hu.mem ▸ hs).frame fv fun r hr i hi => by
      rw [List.mem_singleton.mp hr, BitVec.add_zero]
      exact hsep.symm.sub_left (Offset.sub_base _ (by omega))
  refine WP.mono (scalarRestore_ok hcv hs') fun t ⟨saved, kt, mt⟩ => ?_
  refine ⟨saved, (hu.rest (by decide)).trans ((kv.mono (by decide)).trans (kt.mono (by decide))), ?_, ?_⟩
  · rw [mt, ← hu.mem]; simpa only [BitVec.add_zero] using fv
  · rw [mt, scalar_packed_encode, ← hu.mem]
    have e : packedV v.mem (State.addr p) = V u.mem (State.addr b) SR := by
      simpa only [BitVec.add_zero] using vv
    exact congrArg (Spec.Ed25519.encodeLE 32) e

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseVerified`. -/
section

/-! Merged from `Proof.Ed25519.Arm.ScalarBaseEngine`. -/
section
/-! All input scalar bits, exact point multiplication, and canonical encoding compose. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def encodedValue (p : Spec.Ed25519.Point) : Nat :=
  (p.Y * Spec.X25519.pow p.Z (Spec.X25519.P - 2)).val +
    ((p.X * Spec.X25519.pow p.Z (Spec.X25519.P - 2)).val % 2) * 2 ^ 255

theorem encodedValue_spec (p : Spec.Ed25519.Point) :
    Spec.Ed25519.encodePoint p = Spec.Ed25519.encodeLE 32 (VG.Proof.Ed25519.Arm.encodedValue p) := rfl

theorem scalarBaseEngine_ok {s : State} {base ptr : BitVec 32} (hc : Ctx base s)
    (hp : s.gpr .r12 = ptr) (hfit : ptr.toNat + 32 ≤ 2 ^ 32)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (State.addr ptr + BitVec.ofNat 64 i) 1)
    (hsep : (⟨State.addr ptr, 32⟩ : Region).Disjoint ⟨State.addr base, 8192⟩) :
    WP isa scalarBaseEngine s fun t => VG.Proof.Ed25519.Arm.PointKeep base s t ∧ Lim t.mem (State.addr base) FR ∧
      V t.mem (State.addr base) FR = VG.Proof.Ed25519.Arm.encodedValue
        (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32)) Spec.Ed25519.basePoint) := by
  refine WP.seq (WP.mono (initFields_ok hc) fun a ⟨ak, al, _⟩ => ?_)
  refine WP.seq (WP.mono (fieldCode_ok (constPointOps Spec.Ed25519.basePoint) (ak.ctx hc) al)
    fun u ⟨uk, ul, ue⟩ => ?_)
  have ku := ak.trans uk
  have up : u.gpr .r12 = ptr := (ku.rest.gpr _ (by decide)).trans hp
  have ur : ∀ i < 32, InRegions (u.rd ++ u.wr) (State.addr ptr + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [ku.rest.rd, ku.rest.wr]
    exact hr i hi
  have uv : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt u.mem (State.addr ptr) 32) =
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) := by
    rw [← VG.Proof.Ed25519.Arm.packedDigits_decode _ _ 16, ← VG.Proof.Ed25519.Arm.packedDigits_decode _ _ 16]
    exact VG.Proof.Ed25519.Arm.packedDigits_frame ku.frame (by decide) fun r hm => by
      rw [List.mem_singleton.mp hm]
      exact hsep.sub_right (Offset.sub_base _ (by decide))
  have upp : point (env u.mem base) 0 1 2 3 = Spec.Ed25519.basePoint :=
    (congrArg (fun e => point e 0 1 2 3) ue).trans (constPoint_eval _ _)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.pointFromScalar_ok (ku.ctx hc) ul up 16 (by decide) (by decide) hfit ur hsep)
    fun v ⟨vk, vl, _, vp⟩ => ?_)
  have ksv := (PointKeep.of_keep ku).trans vk
  refine WP.mono (pointEncode_ok (ksv.ctx hc) vl) fun t ⟨tk, tl, tv⟩ => ?_
  refine ⟨ksv.trans (PointKeep.of_ikeep tk), tl, ?_⟩
  change V t.mem (State.addr base) FR = VG.Proof.Ed25519.Arm.encodedValue (point (env v.mem base) 0 1 2 3) at tv
  exact tv.trans (congrArg VG.Proof.Ed25519.Arm.encodedValue
    (vp.trans (congrArg₂ Spec.Ed25519.pointMul uv upp)))

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarBaseCTEngine`. -/
section
/-! Initialization, secret scalar multiplication, and encoding have public traces. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def BaseCTPre (b p : BitVec 32) (s : State) : Prop :=
  Ctx b s ∧ s.gpr .r12 = p ∧ p.toNat + 32 ≤ 2 ^ 32 ∧
    (∀ i < 32, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1) ∧
    (⟨State.addr p, 32⟩ : Region).Disjoint ⟨State.addr b, 8192⟩

def basePrepareCT : Prog isa := .seq (.block initFields) (constPoint Spec.Ed25519.basePoint)

materialize_code VG.Proof.Ed25519.Arm.basePrepareCT

theorem basePrepareCT_ok {s : State} {base ptr : BitVec 32} (h : VG.Proof.Ed25519.Arm.BaseCTPre base ptr s) :
    WP isa VG.Proof.Ed25519.Arm.basePrepareCT s (VG.Proof.Ed25519.Arm.FromCTPre base ptr 16) := by
  obtain ⟨hc, hp, hfit, hr, hsep⟩ := h
  refine WP.seq (WP.mono (initFields_ok hc) fun a ⟨ak, al, _⟩ => ?_)
  refine WP.mono (fieldCode_ok (constPointOps Spec.Ed25519.basePoint) (ak.ctx hc) al)
    fun u ⟨uk, ul, _⟩ => ?_
  have ku := ak.trans uk
  refine ⟨ku.ctx hc, ul, (ku.rest.gpr _ (by decide)).trans hp, hfit, ?_, hsep⟩
  intro i hi
  rw [ku.rest.rd, ku.rest.wr]
  exact hr i hi

theorem scalarBaseEngine_ct (base ptr : BitVec 32) :
    VG.Proof.Ed25519.Arm.CT (fun x y => VG.Proof.Ed25519.Arm.BaseCTPre base ptr x ∧ VG.Proof.Ed25519.Arm.BaseCTPre base ptr y)
      scalarBaseEngine (fun _ _ => True) := by
  have hp : VG.Proof.Ed25519.Arm.CT (fun x y => VG.Proof.Ed25519.Arm.BaseCTPre base ptr x ∧ VG.Proof.Ed25519.Arm.BaseCTPre base ptr y)
      VG.Proof.Ed25519.Arm.basePrepareCT (fun x y => VG.Proof.Ed25519.Arm.FromCTPre base ptr 16 x ∧ VG.Proof.Ed25519.Arm.FromCTPre base ptr 16 y) := by
    apply VG.Proof.Ed25519.Arm.ctBoth
    · apply VG.Proof.Ed25519.Arm.ctRegs [.r0] _ (by taint_decide)
      intro x y h r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.1.1.r0.trans h.2.1.r0.symm
    · exact fun _ h => VG.Proof.Ed25519.Arm.basePrepareCT_ok h
  have hm := (VG.Proof.Ed25519.Arm.pointFromScalar_ct base ptr 16 (.inl rfl)).wpDep (fun x y h =>
    ⟨VG.Proof.Ed25519.Arm.pointFromScalar_ok h.1.1 h.1.2.1 h.1.2.2.1 16 (by decide) (by decide)
      h.1.2.2.2.1 h.1.2.2.2.2.1 h.1.2.2.2.2.2,
     VG.Proof.Ed25519.Arm.pointFromScalar_ok h.2.1 h.2.2.1 h.2.2.2.1 16 (by decide) (by decide)
      h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2⟩)
  have hm' := hm.mono (fun _ _ h => h) (fun x y ⟨_, a, b, h, hx, hy⟩ =>
    And.intro (hx.1.ctx h.1.1).r0 (hy.1.ctx h.2.1).r0)
  have he : VG.Proof.Ed25519.Arm.CT (fun (x y : State) => x.gpr .r0 = base ∧ y.gpr .r0 = base)
      pointEncode (fun _ _ => True) := by
    apply VG.Proof.Ed25519.Arm.ctRegs [.r0] _ (by taint_decide)
    intro x y h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.trans h.2.symm
  intro x y tx ty u v h ex ey
  cases ex with
  | seq ei ex =>
    cases ex with
    | seq ep em =>
      cases ey with
      | seq fi ey =>
        cases ey with
        | seq fp fm =>
          obtain ⟨ht, hh⟩ := hp _ _ _ _ _ _ h (Exec.seq ei ep) (Exec.seq fi fp)
          have hm := (RelCT.seq hm' he _ _ _ _ _ _ hh em fm).1
          exact ⟨by simpa only [List.append_assoc] using
            congrArg₂ (fun (a b : List Leak) => a ++ b) ht hm, trivial⟩

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarBaseSetup`. -/
section
/-! The base-point multiplication wrapper's local contract and scratch setup. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def scalarBaseLocal : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 32⟩
    let scalar : Region := ⟨State.addr (s.gpr .r1), 32⟩
    let ws : Region := ⟨State.addr (s.gpr .r2), 8192⟩
    s.rd = [scalar] ∧ s.wr = [out, ws] ∧ out.Disjoint scalar ∧ out.Disjoint ws ∧
      scalar.Disjoint ws ∧ (s.gpr .r0).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .r1).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32
  post s t := Spec.Ed25519.bytesAt t.mem (State.addr (s.gpr .r0)) 32 =
    Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 32)
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .r2 = t.gpr .r2

structure ScalarBasePre (s : State) : Prop where
  rd : s.rd = [⟨State.addr (s.gpr .r1), 32⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r0), 32⟩, ⟨State.addr (s.gpr .r2), 8192⟩]
  out_scalar : (⟨State.addr (s.gpr .r0), 32⟩ : Region).Disjoint ⟨State.addr (s.gpr .r1), 32⟩
  out_ws : (⟨State.addr (s.gpr .r0), 32⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), 8192⟩
  scalar_ws : (⟨State.addr (s.gpr .r1), 32⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), 8192⟩
  f0 : (s.gpr .r0).toNat + 32 ≤ 2 ^ 32
  f1 : (s.gpr .r1).toNat + 32 ≤ 2 ^ 32
  f2 : (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32

theorem ScalarBasePre.of {s : State} (h : scalarBaseLocal.pre s) : VG.Proof.Ed25519.Arm.ScalarBasePre s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

theorem scalarBaseSetup_ok {s : State} (h : VG.Proof.Ed25519.Arm.ScalarBasePre s) :
    WP isa (.block scalarBaseSetup) s fun t =>
      Ctx (s.gpr .r2) t ∧ t.gpr .r12 = s.gpr .r1 ∧
      ScalarSaved (State.addr (s.gpr .r2)) s.gpr t.mem ∧
      t.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 48) 32 = s.gpr .r0 ∧
      Rest [.r0, .r12] s t ∧ Frame [⟨State.addr (s.gpr .r2), 52⟩] s.mem t.mem := by
  have hw : (⟨State.addr (s.gpr .r2), 8192⟩ : Region) ∈ s.wr := by rw [h.wr]; simp
  rw [scalarBaseSetup]
  refine WP.append (scalarSave_ok rfl h.f2 hw) fun u ⟨su, fu, gu, ku⟩ => ?_
  refine wp_str (a := State.addr (s.gpr .r2) + BitVec.ofNat 64 48) (by decide)
    (by rw [gu]; exact addr_add (by have := h.f2; omega))
    (by rw [ku.wr]; exact in_base hw (by decide) (by decide)) fun v hv => ?_
  refine wp_mov (op2_reg _ _) fun w hw' => wp_mov (op2_reg _ _) fun t ht => WP.block_nil ?_
  have kt : Rest [.r0, .r12] s t :=
    (ku.mono (by decide)).trans ((hv.rest _).trans ((hw'.rest (by decide)).trans (ht.rest (by decide))))
  have mt : t.mem = u.mem.writeW (State.addr (s.gpr .r2) + BitVec.ofNat 64 48) (s.gpr .r0) := by
    rw [ht.mem, hw'.mem, hv.mem, gu]
  refine ⟨⟨?_, h.f2, by rw [kt.wr]; exact hw⟩, ?_, ?_, ?_, kt, ?_⟩
  · rw [ht.other _ (by decide), hw'.gpr, hv.gpr, gu]
  · rw [ht.gpr, hw'.other _ (by decide), hv.gpr, gu]
  · intro i hi
    rw [mt, Mem.readW_writeW_sep (Offset.sep _ (d := 4 * i) (e := 48) (n := 4) (k := 4) (by omega) (by omega) (by omega)) (by decide)]
    exact su i hi
  · rw [mt, Mem.readW_writeW_self32]
  · rw [mt]
    exact (fu.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarBaseCT`. -/
section
/-! The public ABI pointers survive the secret base-point computation. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def BaseWrapCTPre (b p out : BitVec 32) (s : State) : Prop :=
  scalarBaseLocal.pre s ∧ s.gpr .r0 = out ∧ s.gpr .r1 = p ∧ s.gpr .r2 = b

def BaseWorkCTPre (b p out : BitVec 32) (s : State) : Prop :=
  VG.Proof.Ed25519.Arm.BaseCTPre b p s ∧ s.mem.readW (State.addr b + BitVec.ofNat 64 48) 32 = out

def BaseFinishCTPre (b out : BitVec 32) (s : State) : Prop :=
  Ctx b s ∧ s.mem.readW (State.addr b + BitVec.ofNat 64 48) 32 = out

theorem scalarBaseSetup_ct (b p out : BitVec 32) :
    VG.Proof.Ed25519.Arm.CT (fun x y => VG.Proof.Ed25519.Arm.BaseWrapCTPre b p out x ∧ VG.Proof.Ed25519.Arm.BaseWrapCTPre b p out y)
      (.block scalarBaseSetup) (fun x y => VG.Proof.Ed25519.Arm.BaseWorkCTPre b p out x ∧ VG.Proof.Ed25519.Arm.BaseWorkCTPre b p out y) := by
  apply VG.Proof.Ed25519.Arm.ctBoth
  · apply VG.Proof.Ed25519.Arm.ctRegs [.r0, .r1, .r2] _ (by taint_decide)
    intro x y h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1.2.1.trans h.2.2.1.symm
    · exact h.1.2.2.1.trans h.2.2.2.1.symm
    · exact h.1.2.2.2.trans h.2.2.2.2.symm
  · intro s ⟨h, ho, hp, hb⟩
    have hs := ScalarBasePre.of h
    refine WP.mono (VG.Proof.Ed25519.Arm.scalarBaseSetup_ok hs) fun t ⟨hc, hptr, _, hout, hr, _⟩ => ?_
    have hi : (⟨State.addr (s.gpr .r1), 32⟩ : Region) ∈ s.rd ++ s.wr := by rw [hs.rd]; simp
    have ht : VG.Proof.Ed25519.Arm.BaseWorkCTPre (s.gpr .r2) (s.gpr .r1) (s.gpr .r0) t := by
      refine ⟨⟨hc, hptr, hs.f1, ?_, hs.scalar_ws⟩, hout⟩
      intro i hib
      rw [hr.rd, hr.wr]
      exact in_base hi (by omega) (by omega)
    rw [ho, hp, hb] at ht
    exact ht

theorem scalarBaseWork_ct (b p out : BitVec 32) :
    VG.Proof.Ed25519.Arm.CT (fun x y => VG.Proof.Ed25519.Arm.BaseWorkCTPre b p out x ∧ VG.Proof.Ed25519.Arm.BaseWorkCTPre b p out y)
      scalarBaseEngine (fun x y => VG.Proof.Ed25519.Arm.BaseFinishCTPre b out x ∧ VG.Proof.Ed25519.Arm.BaseFinishCTPre b out y) := by
  apply VG.Proof.Ed25519.Arm.ctBoth
  · exact (VG.Proof.Ed25519.Arm.scalarBaseEngine_ct b p).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) (fun _ _ h => h)
  · intro s ⟨⟨hc, hp, hf, hr, hsep⟩, ho⟩
    refine WP.mono (VG.Proof.Ed25519.Arm.scalarBaseEngine_ok hc hp hf hr hsep) fun t ⟨tk, _, _⟩ => ?_
    exact ⟨tk.ctx hc, (tk.word 48 (.inl rfl) (by decide)).trans ho⟩

theorem scalarBaseFinish_ct (b out : BitVec 32) :
    VG.Proof.Ed25519.Arm.CT (fun x y => VG.Proof.Ed25519.Arm.BaseFinishCTPre b out x ∧ VG.Proof.Ed25519.Arm.BaseFinishCTPre b out y)
      (.block scalarBaseFinish) (fun _ _ => True) := by
  have hh : VG.Proof.Ed25519.Arm.CT (fun x y => VG.Proof.Ed25519.Arm.BaseFinishCTPre b out x ∧ VG.Proof.Ed25519.Arm.BaseFinishCTPre b out y)
      (.block [.ldr .r12 .r0 48])
      (fun x y => (x.gpr .r0 = b ∧ x.gpr .r12 = out) ∧ (y.gpr .r0 = b ∧ y.gpr .r12 = out)) := by
    apply VG.Proof.Ed25519.Arm.ctBoth
    · apply VG.Proof.Ed25519.Arm.ctRegs [.r0] _ (by taint_decide)
      intro x y h r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.1.1.r0.trans h.2.1.r0.symm
    · intro s ⟨hc, ho⟩
      refine ldr0_ok hc (by decide) fun t ht => WP.block_nil ?_
      exact ⟨(ht.other _ (by decide)).trans hc.r0, ht.gpr.trans ho⟩
  change VG.Proof.Ed25519.Arm.CT _ (.block (([.ldr .r12 .r0 48] : List Instr) ++ (packField FR 0 ++ scalarRestore))) _
  refine VG.Proof.Ed25519.Arm.ctBlockAppend hh ?_
  apply VG.Proof.Ed25519.Arm.ctRegs [.r0, .r12] _ (by taint_decide)
  intro x y h r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.1.trans h.2.1.symm
  · exact h.1.2.trans h.2.2.symm

theorem scalarBase_ct : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBase := by
  have hct (b p out : BitVec 32) :
      VG.Proof.Ed25519.Arm.CT (fun x y => VG.Proof.Ed25519.Arm.BaseWrapCTPre b p out x ∧ VG.Proof.Ed25519.Arm.BaseWrapCTPre b p out y) scalarBase (fun _ _ => True) :=
    RelCT.seq (VG.Proof.Ed25519.Arm.scalarBaseSetup_ct b p out) (RelCT.seq (VG.Proof.Ed25519.Arm.scalarBaseWork_ct b p out) (VG.Proof.Ed25519.Arm.scalarBaseFinish_ct b out))
  intro s t tx ty u v hs ht ⟨_, h0, h1, h2⟩ ex ey
  exact (hct (s.gpr .r2) (s.gpr .r1) (s.gpr .r0) _ _ _ _ _ _
    ⟨⟨hs, rfl, rfl, rfl⟩, ⟨ht, h0.symm, h1.symm, h2.symm⟩⟩ ex ey).1

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarBaseMain`. -/
section
/-! Merged from `Proof.Ed25519.Arm.ScalarBaseFinish`. -/
section
/-! Canonical point output and restoration of the saved registers. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scalarBaseFinish_ok {b p : BitVec 32} {s : State} (hc : Ctx b s)
    (hl : Lim s.mem (State.addr b) FR) (hp : s.mem.readW (State.addr b + BitVec.ofNat 64 48) 32 = p)
    (hfit : p.toNat + 32 ≤ 2 ^ 32) (hw : (⟨State.addr p, 32⟩ : Region) ∈ s.wr)
    (hsep : (⟨State.addr p, 32⟩ : Region).Disjoint ⟨State.addr b, 8192⟩)
    {g : Reg → BitVec 32} (hs : ScalarSaved (State.addr b) g s.mem) :
    WP isa (.block scalarBaseFinish) s fun t =>
      (∀ i < 8, t.gpr (scalarSavedReg i) = g (scalarSavedReg i)) ∧ Rest VG.Proof.Ed25519.Arm.scalarFinishClob s t ∧
      Frame [⟨State.addr p, 32⟩] s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr p) 32 = Spec.Ed25519.encodeLE 32 (V s.mem (State.addr b) FR) := by
  rw [scalarBaseFinish, List.append_assoc]
  simp only [List.cons_append, List.nil_append]
  refine ldr0_ok hc (by decide) fun u hu => ?_
  have hcu := hc.of_rest (hu.rest (ws := [.r12]) (by decide)) (by decide)
  refine WP.append (packField_ok (p := p) (a := FR) (dst := 0) hcu (by decide) (hu.mem ▸ hl) (by decide)
    (hu.gpr.trans hp) (by omega)
    (fun i hi => by rw [hu.wr]; simpa only [Nat.zero_add] using in_base hw (by omega) (by omega))
    (by simpa only [BitVec.add_zero] using
      hsep.symm.sub_left (Offset.sub_base _ (by decide : FR + 64 ≤ 8192))))
    fun v ⟨kv, fv, vv⟩ => ?_
  have hcv := hcu.of_rest kv (by decide)
  have hs' : ScalarSaved (State.addr b) g v.mem :=
    (hu.mem ▸ hs).frame fv fun r hr i hi => by
      rw [List.mem_singleton.mp hr, BitVec.add_zero]
      exact hsep.symm.sub_left (Offset.sub_base _ (by omega))
  refine WP.mono (scalarRestore_ok hcv hs') fun t ⟨saved, kt, mt⟩ => ?_
  refine ⟨saved, (hu.rest (by decide)).trans ((kv.mono (by decide)).trans (kt.mono (by decide))), ?_, ?_⟩
  · rw [mt, ← hu.mem]; simpa only [BitVec.add_zero] using fv
  · rw [mt, scalar_packed_encode, ← hu.mem]
    have e : packedV v.mem (State.addr p) = V u.mem (State.addr b) FR := by
      simpa only [BitVec.add_zero] using vv
    exact congrArg (Spec.Ed25519.encodeLE 32) e

end VG.Proof.Ed25519.Arm
end

/-! Base-point multiplication, output encoding, and the complete ARM ABI. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scalarBase_correct {s : State} (h : VG.Proof.Ed25519.Arm.ScalarBasePre s) :
    WP isa scalarBase s fun t => abiPreserved s t ∧ scalarBaseLocal.post s t := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.scalarBaseSetup_ok h) fun u ⟨hcu, pu, su, ou, ku, fu⟩ => ?_)
  have input : (⟨State.addr (s.gpr .r1), 32⟩ : Region) ∈ s.rd ++ s.wr := by rw [h.rd]; simp
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.scalarBaseEngine_ok hcu pu h.f1
    (fun n hn => by rw [ku.rd, ku.wr]; exact in_base input (by omega) (by omega)) h.scalar_ws)
    fun v ⟨kv, lv, vv⟩ => ?_)
  have sv : ScalarSaved (State.addr (s.gpr .r2)) s.gpr v.mem :=
    su.frame kv.frame fun r hr i hi => by
      simp only [VG.Proof.Ed25519.Arm.pointRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)
  have ov : v.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 48) 32 = s.gpr .r0 :=
    (kv.word 48 (.inl rfl) (by decide)).trans ou
  refine WP.mono (VG.Proof.Ed25519.Arm.scalarBaseFinish_ok (kv.ctx hcu) lv ov h.f0
    (by rw [kv.rest.wr, ku.wr, h.wr]; simp) h.out_ws sv) fun t ⟨gt, kt, _, bt⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [kt.sp, kv.rest.sp, ku.sp]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact gt 0 (by decide)
    · exact gt 1 (by decide)
    · exact gt 2 (by decide)
    · exact gt 3 (by decide)
    · exact gt 4 (by decide)
    · exact gt 5 (by decide)
    · exact gt 6 (by decide)
    · exact gt 7 (by decide)
    · rw [kt.gpr _ (by decide), kv.rest.gpr _ (by decide), ku.gpr _ (by decide)]
  · have hb : Spec.Ed25519.bytesAt u.mem (State.addr (s.gpr .r1)) 32 =
        Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 32 := by
      unfold Spec.Ed25519.bytesAt
      refine List.map_congr_left fun n hn => fu.bytes (R := ⟨State.addr (s.gpr .r1), 32⟩)
        (fun r hr => ?_) (by decide : 32 ≤ 2 ^ 64) (List.mem_range.mp hn)
      rw [List.mem_singleton.mp hr]
      exact h.scalar_ws.sub_right (Region.sub_prefix (by decide))
    change Spec.Ed25519.bytesAt t.mem _ 32 = Spec.Ed25519.scalarBase _
    rw [bt, vv, hb, Spec.Ed25519.scalarBase, VG.Proof.Ed25519.Arm.encodedValue_spec]

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarBaseLit`. -/
section
namespace VG.Impl.Ed25519.Arm
materialize_code scalarBase
end VG.Impl.Ed25519.Arm
end

/-! The complete base-point multiplier meets the merged specification,
preserves the ABI, and keeps all scalar bytes secret. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

def baseSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x3000, 8192⟩]

theorem scalarBase_ok (s : State) (hs : scalarBaseLocal.pre s) :
    ∃ t s', Exec isa scalarBase s t s' ∧ abiPreserved s s' ∧ scalarBaseLocal.post s s' :=
  VG.Proof.Ed25519.Arm.scalarBase_correct (ScalarBasePre.of hs)

theorem scalarBase_verified : Verified Arm.target scalarBase
    (Spec.Ed25519.scalarBaseContract Arm.abi) :=
  Verified.of_correct VG.Proof.Ed25519.Arm.scalarBase_ok VG.Proof.Ed25519.Arm.scalarBase_ct (by
    sig_implies [Spec.Ed25519.scalarBaseContract, Spec.Ed25519.scalarBaseSig,
      Spec.Ed25519.scratchWords, VG.Proof.Ed25519.Arm.scalarBaseLocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [baseSatState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.Ed25519.Arm.baseSatState)

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTLit`. -/
section

/-! Checked code literals for verifier composition. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm
materialize_code verifyBasePoint := constPoint Spec.Ed25519.basePoint
materialize_code verifyWriteA := (.block (pointTableWrite 7744) : Prog isa)
materialize_code verifyWriteR := (.block (pointTableWrite 7872) : Prog isa)
materialize_code verifyWriteLhs := (.block (pointTableWrite 8000) : Prog isa)
materialize_code verifyReadA := (.block (pointTableRead 7744) : Prog isa)
materialize_code verifyCombine
materialize_code verifyScalarTail := (.block (unpackField SR 0 ++ scalarCompare ++ ([.cmp .r5 (.imm 0)] : List Instr)) : Prog isa)
materialize_code verifySetupBlock := (.block verifySetup : Prog isa)
materialize_code verifyFinishBlock := (.block verifyFinish : Prog isa)
end VG.Proof.Ed25519.Arm

end

end
