module
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.TCB.Arm.Isa

import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The native arithmetic frame implies the shared RSA workspace frame -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt Keeps)

theorem keeps_of_native {mem mem' : Mem} {base : BitVec 32} {len w o : Nat}
    (nowrap : base.toNat + 8 * len ≤ 2 ^ 32) (hw : 2 ≤ w)
    (outside : Outs (State.addr base)
      [(arrAt w 2, 4 * (2 * w + 2)), (arrAt w 3, 32), (arrAt w 3 + 16, 8),
       (arrAt w 3, 4 * (2 * w)), (arrAt w o, 4 * (2 * w))] mem mem') :
    Keeps (State.addr base) len w o mem mem' := by
  intro i hi separate
  have h2 := separate 2 (by simp [Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
  have h3 := separate 3 (by simp [Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
  have ho := separate o (by simp)
  apply outside
  intro r hr
  have ofsEq : ofs (State.addr base) (State.addr base + BitVec.ofNat 64 i) = i := by
    unfold ofs
    rw [Mem.sub_ofNat_toNat _ (by omega)]
  rw [ofsEq]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega


theorem frame_of_native {mem mem' : Mem} {base : Addr} {size w o : Nat}
    (hw : 2 ≤ w) (ho : o < 8) (fit : arrAt w 8 ≤ size)
    (outside : Outs base
      [(arrAt w 2, 4 * (2 * w + 2)), (arrAt w 3, 32), (arrAt w 3 + 16, 8),
       (arrAt w 3, 4 * (2 * w)), (arrAt w o, 4 * (2 * w))] mem mem') :
    Frame [⟨base, size⟩] mem mem' := by
  have f2 := array_end_le (w := w) (j := 2) (k := 8) (by decide)
  have f3 := array_end_le (w := w) (j := 3) (k := 8) (by decide)
  have fo := array_end_le (w := w) ho
  intro x hx
  have h := hx ⟨base, size⟩ (by simp)
  change ¬ ((x - base).toNat + 1 ≤ size) at h
  apply outside
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [ofs] <;> omega

end VG.Proof.Bignum.Arm
