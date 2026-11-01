module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Dsa.Arm.PublicValidation
public import VerifiedGarbage.Proof.Dsa.Arm.Session
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Weierstrass.MontContract

/-! # Resources of the shared public-key validation contract -/

@[expose] public section
namespace VG.Proof.Dsa.Arm.PublicValidation
open VG VG.Arm VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Impl.Dsa.Arm.PublicValidation
open VG.Spec.Dsa.PublicValidation (component)
open VG.Spec.Dsa.ModPow (numAt)

abbrev ws (s : State) : Addr := State.addr (s.gpr .r0)
abbrev key (s : State) : Addr := State.addr (s.gpr .r2)
abbrev size (s : State) : Nat := 8 * (s.gpr .r1).toNat
abbrev keyLen (s : State) : Nat := (s.gpr .r3).toNat

/-- The shared signature expressed directly in the ARM registers. -/
def armContract (pLen qLen : Nat) : Contract isa where
  pre s := s.rd = [⟨key s, keyLen s⟩] ∧ s.wr = [⟨ws s, size s⟩] ∧
    (s.gpr .r0).toNat + size s ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + keyLen s ≤ 2 ^ 32 ∧
    (⟨key s, keyLen s⟩ : Region).Disjoint ⟨ws s, size s⟩ ∧
    Spec.Dsa.PublicValidation.pre (layout pLen qLen) 4 (ws s) (s.gpr .r1).toNat (key s) (keyLen s) s.mem
  post s t := Spec.Dsa.PublicValidation.post (layout pLen qLen) (ws s) (s.gpr .r1).toNat (key s) s.mem t.mem
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧
    s.gpr .r2 = t.gpr .r2 ∧ s.gpr .r3 = t.gpr .r3

theorem pointer_addr {m : Mem} {base a : Addr} {d : Nat}
    (H : numAt m base d 4 = a.toNat) : State.addr (m.readW (off base d) 32) = a := by
  apply BitVec.eq_of_toNat_eq
  rw [VG.Proof.X25519.Arm.addr_toNat]
  simpa only [numAt, Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq] using H

theorem keyInput {s : State} {pLen qLen offset len : Nat} {f : Impl.Dsa.Layout.Field}
    (H : (armContract pLen qLen).pre s) (hf : f ≠ .mask) (hl : offset + len ≤ keyLen s)
    (hp : numAt s.mem (ws s) (Impl.Dsa.Arm.Layout.field f) 4 =
      (key s + BitVec.ofNat 64 offset).toNat) :
    Input s (ws s) (size s) (.input f) len (component s.mem (key s) offset len) := by
  obtain ⟨rd, wr, wn, kn, apart, pre⟩ := H
  have P : State.addr (pointerValue (ws s) s (.input f)) = key s + BitVec.ofNat 64 offset := pointer_addr hp
  have kn' : (key s).toNat + keyLen s ≤ 2 ^ 32 := by
    simpa only [key, VG.Proof.X25519.Arm.addr_toNat] using kn
  have PN : (pointerValue (ws s) s (.input f)).toNat = (key s).toNat + offset := by
    have := congrArg BitVec.toNat P
    have An : (key s + BitVec.ofNat 64 offset).toNat = (key s).toNat + offset := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show offset < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (by omega)]
    rw [VG.Proof.X25519.Arm.addr_toNat, An] at this
    exact this
  have contained : (⟨key s + BitVec.ofNat 64 offset, len⟩ : Region).Sub ⟨key s, keyLen s⟩ :=
    Offset.sub_base _ hl
  have big : 4960 ≤ size s := by have := pre.1; change 15713 ≤ size s at this; omega
  refine ⟨⟨hf, by rw [PN]; omega, ?_, ?_⟩, ?_, ?_⟩
  · intro e k he
    rw [P, rd, wr]
    refine ⟨⟨key s, keyLen s⟩, by simp, ?_⟩
    rw [Offset.add_ofNat_add_ofNat]
    exact Offset.contains_base _ (by omega) (by omega)

  · rw [P]
    exact (apart.sub_left contained).sub_right (Region.sub_prefix big)
  · rw [P]
    exact apart.sub_left contained
  · simp only [operand, component, P]

theorem entry {s : State} {pLen qLen : Nat} (H : (armContract pLen qLen).pre s) :
    Pow.Entry s (ws s) (size s) :=
  ⟨rfl, ⟨size s, Nat.le_refl _, by have := H.2.2.1; omega, by rw [H.2.1]; simp⟩,
    by simpa only [ws, VG.Proof.X25519.Arm.addr_toNat] using H.2.2.1⟩

end VG.Proof.Dsa.Arm.PublicValidation
