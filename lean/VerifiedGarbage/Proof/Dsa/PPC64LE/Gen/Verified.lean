module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Body
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.Generation.ByteResult
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on PPC64LE meets its contract

From the shared contract's precondition, the body (`body_vp`) returns the
status of `Spec.Dsa.generateParametersBytes` and writes its parameters (or
zeros) (`code_ok`); two calls with the same public data have the same
public parameters, so the same trace (`code_ct`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

section
variable {g1 g2 g3 : Geo}

/-- The result as the contract states it. -/
theorem sRes_bytes {σ : State} (h : CIn 176 σ) :
    Spec.Dsa.generateParametersBytes (σ.gpr .r5).toNat (σ.gpr .r6).toNat
      (Spec.Rsa.bytesAt σ.mem (σ.gpr .r7) (σ.gpr .r8).toNat)
      (Spec.Rsa.bytesAt σ.mem (σ.gpr .r9) (σ.gpr .r10).toNat)
      (Spec.Rsa.bytesAt σ.mem (stackArg σ 0) (stackArg σ 1).toNat) =
    (sRes (mkG σ)).map (Spec.Dsa.encodeParams (mkG σ).pLen (mkG σ).qLen) :=
  VG.Proof.Dsa.Generation.generateParametersBytes_attempt h.lens _ _ _
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact h.seedsMod)
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact h.hsMod)

theorem code_ok (K1 : GeoOk g1 128 20) (K2 : GeoOk g2 256 32) (K3 : GeoOk g3 384 32) {s : State}
    (hs : (Spec.Dsa.generateParametersContract abi 176).pre s) :
    WP isa (code g1 g2 g3) s fun t => abiPreserved s t ∧ (Spec.Dsa.generateParametersContract abi 176).post s t := by
  have hpre := cin_of_pre (n := 175) s hs
  refine WP.mono ((body_vp (G := mkG s) K1 K2 K3).wp s _ ⟨rfl, hpre, rfl⟩) fun u hu => ⟨hu.abi, ?_⟩
  sig_post [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_four,
    List.append_eq]
  rw [sRes_bytes hpre]
  refine ⟨?_, hu.out⟩
  rw [hu.r3]
  cases sRes (mkG s) <;> rfl

theorem map_toNat_inj {a b : List Byte} (h : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h

/-- Two calls with the same public data have the same public parameters. -/
theorem mkG_eq {s₁ s₂ : State} (h : (Spec.Dsa.generateParametersContract abi 176).pub s₁ s₂) : mkG s₁ = mkG s₂ := by
  sig_pub [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_four,
    List.append_eq] at h
  obtain ⟨hsp, hl, r3, r4, r5, r6, r7, r8, r9, r10, a0, a1, a2, a3⟩ := h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
    at a0 a1 a2 a3
  simp only [List.append_assoc] at hl
  obtain ⟨hS, hl⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, r8])
  obtain ⟨hH, hW⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, r10])
  have e₁ := map_toNat_inj hS
  have e₂ := map_toNat_inj hH
  have e₃ := map_toNat_inj hW
  simp only [mkG]
  rw [e₁, e₂, e₃, hsp, r3, r4, r5, r6, r7, r8, r9, r10, a0, a1, a2, a3]

/-- The code leaks only what its contract makes public. -/
theorem code_ct (K1 : GeoOk g1 128 20) (K2 : GeoOk g2 256 32) (K3 : GeoOk g3 384 32) :
    ConstantTime isa (Spec.Dsa.generateParametersContract abi 176).pre
      (Spec.Dsa.generateParametersContract abi 176).pub (code g1 g2 g3) := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp e₁ e₂
  have p₁ := cin_of_pre (n := 175) s₁ h₁
  have p₂ := cin_of_pre (n := 175) s₂ h₂
  have hG := mkG_eq hp
  exact ((body_vp (G := mkG s₁) K1 K2 K3).ct _ _ _ _ _ _ ⟨s₁, s₂, ⟨rfl, p₁, rfl⟩, ⟨rfl, p₂, hG.symm⟩⟩ e₁ e₂).1

/-- A 1024/160 call with empty tapes: `out` at `0x1000`, the tapes at
`0x5000`, `0x6000` and `0x7000`, `scratch` at `0x30000`. -/
def generateSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 276 | .r5 => 128 | .r6 => 20 | .r7 => 0x5000 | .r9 => 0x6000 | _ => 0
  lr := 0
  sp := 0x20000
  mem a := bif Nat.beq a.toNat 0x20061 then 0x70 else bif Nat.beq a.toNat 0x20072 then 0x03
    else bif Nat.beq a.toNat 0x20079 then 0x24 else 0
  rd := [⟨0x5000, 0⟩, ⟨0x6000, 0⟩, ⟨0x7000, 0⟩, ⟨0x20060, 32⟩]
  wr := [⟨0x1000, 276⟩, ⟨0x30000, 73728⟩]

theorem generate_satisfiable : ∃ s, (Spec.Dsa.generateParametersContract abi 176).pre s := by
  sig_implies_sat [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs,
    stackArgs_four, List.append_eq, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [generateSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using generateSat

/-- `vg_dsa_generate_parameters` over the three geometries meets its contract. -/
theorem generate_verified (K1 : GeoOk g1 128 20) (K2 : GeoOk g2 256 32) (K3 : GeoOk g3 384 32) :
    Verified target (code g1 g2 g3) (Spec.Dsa.generateParametersContract abi 176) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_ok K1 K2 K3 hs; ⟨t, s', he, hq.1, hq.2⟩, code_ct K1 K2 K3,
    generate_satisfiable⟩

end

end VG.Proof.Dsa.PPC64LE.Gen
