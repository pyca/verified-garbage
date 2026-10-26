module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Body
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Dsa.Generation.ByteResult
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on PPC64LE meets its contract

From the shared contract's precondition, the body (`body_vp`) returns the
status of `Spec.Dsa.generateParametersBytes` and writes its parameters (or
zeros) (`code_ok`); two calls with the same public data have the same
public parameters, so the same trace (`code_ct`). The contract's calling
convention adds the table of small primes the probable-prime tests read.
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

/-- The contract. -/
abbrev genK : Contract isa := Spec.Dsa.generateParametersContract (abi.withConsts kT) 176

theorem code_ok (K1 : GeoOk g1 128 20) (K2 : GeoOk g2 256 32) (K3 : GeoOk g3 384 32) {s : State}
    (hs : genK.pre s) : WP isa (code g1 g2 g3) s fun t => abiPreserved s t ∧ genK.post s t := by
  have hpre := cin_of_pre (n := 175) s hs
  refine WP.mono ((body_vp (G := mkG s) K1 K2 K3).wp s _ ⟨rfl, hpre, rfl⟩ rfl) fun u hu => ⟨hu.abi, ?_⟩
  refine (post_consts (c₀ := (Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed))
    (cs := [])).mpr ?_
  sig_post [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_four,
    List.append_eq]
  rw [sRes_bytes hpre]
  refine ⟨?_, hu.out⟩
  rw [hu.r3]
  cases sRes (mkG s) <;> rfl

theorem map_toNat_inj {a b : List Byte} (h : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h

/-- Two calls with the same public data have the same public parameters. -/
theorem mkG_eq {s₁ s₂ : State} (h : genK.pub s₁ s₂) : mkG s₁ = mkG s₂ := by
  obtain ⟨h, hy⟩ := (pub_consts (c₀ := (Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed))
    (cs := [])).mp h
  have ht := hy _ List.mem_cons_self
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
  rw [e₁, e₂, e₃, hsp, r3, r4, r5, r6, r7, r8, r9, r10, a0, a1, a2, a3, ht]

/-- The code leaks only what its contract makes public. -/
theorem code_ct (K1 : GeoOk g1 128 20) (K2 : GeoOk g2 256 32) (K3 : GeoOk g3 384 32) :
    ConstantTime isa genK.pre genK.pub (code g1 g2 g3) := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp e₁ e₂
  have p₁ := cin_of_pre (n := 175) s₁ h₁
  have p₂ := cin_of_pre (n := 175) s₂ h₂
  have hG := mkG_eq hp
  exact ((body_vp (G := mkG s₁) K1 K2 K3).ct _ _ _ _ _ _ ⟨s₁, s₂, ⟨⟨rfl, p₁, rfl⟩, rfl⟩, ⟨⟨rfl, p₂, hG.symm⟩, rfl⟩⟩ e₁ e₂).1

/-- The witness's memory: the stack arguments, and the table at `0x50000`. -/
def satMem : Mem := fun a =>
  bif Nat.beq a.toNat 0x20061 then 0x70 else bif Nat.beq a.toNat 0x20072 then 0x03
    else bif Nat.beq a.toNat 0x20079 then 0x24
    else if (a - 0x50000#64).toNat < 8192 then constMem 0x50000#64 Impl.RsaKeyGen.TrialTable32.packed a else 0

/-- A 1024/160 call with empty tapes: `out` at `0x1000`, the tapes at
`0x5000`, `0x6000` and `0x7000`, `scratch` at `0x30000`, the table at
`0x50000`. -/
def generateSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 276 | .r5 => 128 | .r6 => 20 | .r7 => 0x5000 | .r9 => 0x6000 | _ => 0
  lr := 0
  sp := 0x20000
  mem := satMem
  rd := [⟨0x5000, 0⟩, ⟨0x6000, 0⟩, ⟨0x7000, 0⟩, ⟨0x20060, 32⟩, ⟨0x50000, 8192⟩]
  wr := [⟨0x1000, 276⟩, ⟨0x30000, 73728⟩]
  syms _ := 0x50000

theorem sat_table : Abi.constsHeld satMem (fun _ => 0x50000#64) kT := by
  intro k hk i index
  simp only [kT, Impl.RsaKeyGen.TrialTable32.consts, List.mem_cons, List.not_mem_nil, or_false] at hk
  subst hk
  dsimp only at index ⊢
  have fit : 8 * Impl.RsaKeyGen.TrialTable32.packed.length ≤ 2 ^ 64 := by
    rw [VG.Proof.RsaKeyGen.TrialTable32.packed_length]; decide
  have small : i < 1024 := by rw [VG.Proof.RsaKeyGen.TrialTable32.packed_length] at index; exact index
  refine Eq.trans (Mem.readW_congr (m := satMem) (m' := constMem 0x50000 Impl.RsaKeyGen.TrialTable32.packed) ?_)
    (constMem_held 0x50000 Impl.RsaKeyGen.TrialTable32.packed fit i index)
  intro j hj
  have hj' : j < 8 := hj
  have e : (0x50000#64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j).toNat = 0x50000 + (8 * i + j) := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have ne : ∀ n, n < 0x50000 → Nat.beq (0x50000#64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j).toNat n = false :=
    fun n hn => by
      rw [e]
      cases h : Nat.beq (0x50000 + (8 * i + j)) n
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) (by omega)
  show (bif _ then _ else bif _ then _ else bif _ then _ else if _ then _ else _) = _
  rw [ne _ (by decide), ne _ (by decide), ne _ (by decide)]
  simp only [Bool.cond_false]
  split
  · rfl
  · next hn => exact (hn (by simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)).elim

theorem generate_satisfiable : ∃ s, genK.pre s := by
  have e : constRegs [(Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed)] generateSat = _ :=
    constRegs_kT generateSat
  refine ⟨generateSat, (pre_consts (c₀ := (Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed))
    (cs := [])).mpr ⟨?_, ?_, sat_table, ?_, ?_⟩⟩
  · sig_pre [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs,
      stackArgs_four, List.append_eq, stackArg, stackArgAddr, List.getD, List.range, List.range.loop, stripConsts]
    sig_and_intros
    all_goals first
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)
  · rw [e]; rfl
  · rw [e]
    intro t ht
    rw [List.mem_singleton] at ht
    subst ht
    refine ⟨by decide, fun r hr => ?_, fun r hr => ?_⟩
    · simp only [generateSat, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
    · simp only [abi, stackBelow, List.mem_singleton] at hr
      subst hr
      exact Region.disjoint_of_sep (by decide)
  · rw [e]
    intro t ht
    rw [List.mem_singleton] at ht
    subst ht
    decide

/-- `vg_dsa_generate_parameters` over the three geometries meets its contract. -/
theorem generate_verified (K1 : GeoOk g1 128 20) (K2 : GeoOk g2 256 32) (K3 : GeoOk g3 384 32) :
    Verified target (code g1 g2 g3) genK :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_ok K1 K2 K3 hs; ⟨t, s', he, hq.1, hq.2⟩, code_ct K1 K2 K3,
    generate_satisfiable⟩

end

end VG.Proof.Dsa.PPC64LE.Gen
