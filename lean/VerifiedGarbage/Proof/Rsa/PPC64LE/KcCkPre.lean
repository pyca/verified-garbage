module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcContract
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcFrame

/-! # `vg_rsa_check_key` and `vg_rsa_check_crt_key` on PPC64LE: their preconditions' `KPre` -/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.KeyCheck

open VG VG.PPC64LE

/-- The working space of `vg_rsa_check_key`. -/
abbrev ckB (s0 : State) : Addr := PPC64LE.stackArg s0 8
abbrev ckZ (s0 : State) : Nat := (PPC64LE.stackArg s0 9).toNat * 8
/-- The modulus' length. -/
abbrev kK (s0 : State) : Nat := (s0.gpr .r4).toNat

theorem ck_kpre {s0 : State} (h : ckP.pre s0) : KPre s0 (ckB s0) (ckZ s0) (kK s0) 8 10 := by
  obtain ⟨hsp, hrd, hwr, -, -, -, -, -, -, -, -, hsa, -, -, -, -, -, -, -, -, nw, ⟨hk, hk'⟩, -, -, -, -, -, -,
    -, -, -, -, -, hsl⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  exact ⟨by rw [hwr]; simp, nw, by simp only [ckZ, kK]; omega, hk, hk', by omega, by rw [hrd]; simp, hsa, rfl,
    by decide, rfl⟩

/-- The working space of `vg_rsa_check_crt_key`. -/
abbrev cckB (s0 : State) : Addr := PPC64LE.stackArg s0 6
abbrev cckZ (s0 : State) : Nat := (PPC64LE.stackArg s0 7).toNat * 8

theorem cck_kpre {s0 : State} (h : cckP.pre s0) : KPre s0 (cckB s0) (cckZ s0) (kK s0) 6 8 := by
  obtain ⟨hsp, hrd, hwr, -, -, -, -, -, -, -, hsa, -, -, -, -, -, -, -, nw, ⟨hk, hk'⟩, -, -, -, -, -, -,
    -, -, -, hsl⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  exact ⟨by rw [hwr]; simp, nw, by simp only [cckZ, kK]; omega, hk, hk', by omega, by rw [hrd]; simp, hsa, rfl,
    by decide, rfl⟩

end VG.Proof.Rsa.PPC64LE.KeyCheck
