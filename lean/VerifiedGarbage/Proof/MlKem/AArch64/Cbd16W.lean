module

public import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16W.Step
meta import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16W.Step

/-!
# `vg_mlkem16_cbd2` on AArch64

`Impl.MlKem.AArch64.Cbd16.code16` meets `Spec.MlKem.cbd2_16Contract`: the
loop writes the two bytes of each coefficient (`Inv.out`), which are the
coefficient stored with 16 bits (`polyIsW16_of_bytes`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Cbd16W

open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Cbd16 (code16)

/-- A 16-bit coefficient from its two bytes. -/
theorem coeffAtW16_toNat (m : Mem) (p : Addr) (i : Nat) :
    (coeffAtW 16 m p i).toNat =
      (m (p + BitVec.ofNat 64 (2 * i))).toNat + 256 * (m (p + BitVec.ofNat 64 (2 * i + 1))).toNat := by
  have e : coeffAtW 16 m p i = (m (p + BitVec.ofNat 64 (2 * i) + 1) ++ m (p + BitVec.ofNat 64 (2 * i)) : BitVec 16) := by
    rw [coeffAtW, Mem.readW, show 16 / 8 * i = 2 * i by omega]
    apply BitVec.eq_of_toNat_eq
    simp only [Mem.read, BitVec.toNat_setWidth, BitVec.toNat_append]
    rw [show (0#0).toNat = 0 from rfl, Nat.zero_shiftLeft, Nat.zero_or]
    exact Nat.mod_eq_of_lt (by
      rw [← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt _), Nat.shiftLeft_eq]
      have := (m (p + BitVec.ofNat 64 (2 * i) + 1)).isLt
      have := (m (p + BitVec.ofNat 64 (2 * i))).isLt
      omega)
  rw [e, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt _), Nat.shiftLeft_eq,
    show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ptr_add]
  omega

/-- All bytes of the output written: the polynomial, stored with 16 bits. -/
theorem polyIsW16_of_bytes {s₀ : State} {m : Mem} {old : Nat → Byte}
    (h : BytesUpTo m (Cbd2.fP s₀) 512 512 (L s₀) old) :
    PolyIsW 16 m (Cbd2.fP s₀) (samplePolyCBD 2 (Cbd2.B s₀)) := by
  have hc : ∀ i < n, (coeffAtW 16 m (Cbd2.fP s₀) i).toNat = coef s₀ i := fun i hi => by
    have hi' : i < 256 := hi
    have hq : coef s₀ i < 3329 := Fin.isLt _
    rw [coeffAtW16_toNat, h _ (by omega), h _ (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
      L, L, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (2 * i) / 2 = i by omega,
      show (2 * i + 1) / 2 = i by omega, show 2 * i % 2 = 0 by omega, show (2 * i + 1) % 2 = 1 by omega,
      Nat.pow_zero, Nat.pow_one, Nat.div_one]
    omega
  refine ⟨fun i hi => by rw [hc i hi]; exact Fin.isLt _, ext_getElem! fun i hi => ?_⟩
  rw [getElem!_eq _ hi]
  simp only [polyAtW, Vector.getElem_ofFn]
  rw [hc i hi, ofNat_val]

theorem correct (s : State) (hs : cbd2_16AArch64.pre s) :
    ∃ t s', Exec isa code16 s t s' ∧ abiPreserved s s' ∧ cbd2_16AArch64.post s s' := by
  obtain ⟨h1, h2, h3⟩ := hs
  obtain ⟨t, s', he, hi⟩ := loop_ok (s₀ := s) ⟨h1, h2, h3⟩
  exact ⟨t, s', he, abi_of rfl (by decide +kernel) he, polyIsW16_of_bytes hi.out⟩

theorem ct : ConstantTime isa cbd2_16AArch64.pre cbd2_16AArch64.pub code16 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1])
    (fun _ _ _ _ ⟨h0, h1, hsp⟩ => agree_of hsp (by simp [h0, h1])) (by taint_decide)

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 512⟩]

theorem verified : Verified AArch64.target code16 (Spec.MlKem.cbd2_16Contract AArch64.abi) :=
  Verified.of_correct correct ct (by
    mlkem_implies [Spec.MlKem.cbd2_16Contract, Spec.MlKem.cbd2_16Sig, cbd2_16AArch64, AArch64.abi,
      AArch64.argRegs] [sat] using sat)

end VG.Proof.MlKem.AArch64.Cbd16W
