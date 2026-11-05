module

public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Body
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Sat
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/-! # DSA parameter search on RISC-V meets its contract -/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64
open VG.Impl.Dsa.RISCV64.ParameterSearch

/-- The contract, with the table, for the 512 bytes of stack the tests use. -/
abbrev searchK : Contract isa := Spec.Dsa.parameterSearchContract (abi.withConsts kT) 512

theorem map_toNat_inj {a b : List Byte} (h : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h

theorem map_toNat_inj64 {a b : List (BitVec 64)} (h : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h

/-- Two calls with the same public data have the same public parameters. -/
theorem mkG_eq {s₁ s₂ : State} (h : searchK.pub s₁ s₂) : mkG s₁ = mkG s₂ := by
  obtain ⟨h, hy⟩ := (pub_consts (c₀ := (Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed))
    (cs := [])).mp h
  have ht := hy _ List.mem_cons_self
  sig_pub [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs, List.append_eq] at h
  obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6, r7⟩ := h
  have l1 : ((Spec.Rsa.wordsAt s₁.mem (s₁.gpr .a7) 4).map (·.toNat)).length =
      ((Spec.Rsa.wordsAt s₂.mem (s₂.gpr .a7) 4).map (·.toNat)).length := by simp [Spec.Rsa.wordsAt]
  obtain ⟨hw, hb⟩ := List.append_inj hl l1
  have ew := map_toNat_inj64 hw
  have eb := map_toNat_inj hb
  simp only [Spec.Rsa.wordsAt, List.range, List.range.loop, List.map_cons, List.map_nil, List.cons.injEq,
    Nat.mul_zero, BitVec.add_zero, Nat.mul_one] at ew
  obtain ⟨w0, w1, -⟩ := ew
  have e8 : (BitVec.ofNat 64 8 : BitVec 64) = 8 := rfl
  rw [e8] at w1
  simp only [mkG]
  rw [w0, w1, eb, hsp, r0, r1, r2, r3, r4, r5, r6, r7, ht]

section
variable {g1 g2 g3 : Geo}

theorem code_ok (K1 : GeoOk g1 128 20) (K2 : GeoOk g2 256 32) (K3 : GeoOk g3 384 32) {s : State}
    (hs : searchK.pre s) : WP isa (code g1 g2 g3) s fun t => abiPreserved s t ∧ searchK.post s t := by
  have hpre := cin_of_pre (n := 511) s hs
  refine WP.mono ((body_vp (G := mkG s) K1 K2 K3).wp s _ ⟨rfl, hpre, rfl⟩ rfl) fun u hu => ⟨hu.abi, ?_⟩
  refine (post_consts (c₀ := (Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed))
    (cs := [])).mpr ?_
  sig_post [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs, List.append_eq]
  exact ⟨hu.status, hu.out, hu.used, hu.state⟩

/-- The code leaks only what its contract makes public. -/
theorem code_ct (K1 : GeoOk g1 128 20) (K2 : GeoOk g2 256 32) (K3 : GeoOk g3 384 32) :
    ConstantTime isa searchK.pre searchK.pub (code g1 g2 g3) := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp e₁ e₂
  have p₁ := cin_of_pre (n := 511) s₁ h₁
  have p₂ := cin_of_pre (n := 511) s₂ h₂
  have hG := mkG_eq hp
  exact ((body_vp (G := mkG s₁) K1 K2 K3).ct _ _ _ _ _ _ ⟨s₁, s₂, ⟨⟨rfl, p₁, rfl⟩, rfl⟩, ⟨⟨rfl, p₂, hG.symm⟩, rfl⟩⟩ e₁ e₂).1

/-- `vg_dsa_parameter_search` over the three widths meets its contract. -/
theorem search_verified (K1 : GeoOk g1 128 20) (K2 : GeoOk g2 256 32) (K3 : GeoOk g3 384 32) :
    Verified target (code g1 g2 g3) searchK :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_ok K1 K2 K3 hs; ⟨t, s', he, hq.1, hq.2⟩, code_ct K1 K2 K3,
    ⟨satState, sat⟩⟩

end

end VG.Proof.Dsa.RISCV64.PSearch
