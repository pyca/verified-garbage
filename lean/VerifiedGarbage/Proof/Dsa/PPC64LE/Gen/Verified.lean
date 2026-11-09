module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Body
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation over refillable tapes on PPC64LE meets its contract

From the shared contract's precondition, the body (`body_vp`) returns the
status of `Spec.Dsa.parameterSearch` and writes its parameters (or zeros),
`used` and `state` (`code_ok`); two calls with the same public data have the
same public parameters, so the same trace (`code_ct`). The contract's calling
convention adds the table of small primes the probable-prime tests read.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

section
variable {g1 g2 g3 : Geo}

/-- The contract. -/
abbrev genK : Contract isa := Spec.Dsa.parameterSearchContract (abi.withConsts kT) 176

theorem outBytes_eq (G : GP) (o : COut) :
    outBytes G o = match (cRes G o).outcome with
      | .accepted a => Spec.Dsa.encodeParams G.pLen G.qLen a
      | _ => List.replicate G.outLen 0 := by
  cases o with
  | found => rfl
  | noSeeds => rfl
  | ranOut j c =>
    simp only [outBytes, cRes, VG.Proof.Dsa.Generation.ranOutResult]
    by_cases hb : Spec.Dsa.parameterEntropy G.pLen ≤ G.witLen - c
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hb)]

theorem code_ok (K1 : GeoOk g1 128 20) (K2 : GeoOk g2 256 32) (K3 : GeoOk g3 384 32) {s : State}
    (hs : genK.pre s) : WP isa (code g1 g2 g3) s fun t => abiPreserved s t ∧ genK.post s t := by
  have hpre := cin_of_pre (n := 175) s hs
  refine WP.mono ((body_vp (G := mkG s) K1 K2 K3).wp s _ ⟨rfl, hpre, rfl⟩ rfl) fun u hu => ⟨hu.abi, ?_⟩
  obtain ⟨v, fo, m, r3⟩ := hu.fo
  have res := hu.res
  refine (post_consts (c₀ := (Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed))
    (cs := [])).mpr ?_
  sig_post [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs]
  have hp : 0 < pLenOf s := by
    have := hpre.valid; simp only [Spec.Dsa.generationPLenValid, Bool.or_eq_true, beq_iff_eq] at this; omega
  have ht : Spec.Dsa.parameterSearch (pLenOf s) (s.mem.readW (s.gpr .r10) 64).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat) = cRes (mkG s) (oOf (mkG s)) := res.symm
  have w8 : s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 (pLenOf s) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
  have w16 : s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 16) 64 =
      BitVec.ofNat 64 (Spec.Dsa.parameterEntropy (pLenOf s)) := hpre.budget
  rw [ht]
  refine ⟨?_, ?_, ?_, VG.Proof.Dsa.Generation.requested (pLenOf s) (cRes (mkG s) (oOf (mkG s))), ?_,
    by rw [← ht]; exact VG.Proof.Dsa.Generation.requested_requests hp _ _⟩
  · have hst : (cRes (mkG s) (oOf (mkG s))).status < 4 := by
      unfold Spec.Entropy.Result.status Spec.Entropy.Outcome.status; split <;> decide
    have e3 : u.gpr .r3 = BitVec.ofNat 64 (cRes (mkG s) (oOf (mkG s))).status := r3.trans fo.r3
    rw [e3, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [m]; exact fo.out.trans (outBytes_eq _ _)
  · rw [m]; exact congrArg (· :: []) fo.used
  · rw [m]
    exact List.cons_eq_cons.mpr ⟨fo.st0, List.cons_eq_cons.mpr ⟨fo.st1.trans w8,
      List.cons_eq_cons.mpr ⟨fo.st2.trans w16, List.cons_eq_cons.mpr ⟨fo.st3, rfl⟩⟩⟩⟩

theorem map_toNat_inj {a b : List Byte} (h : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h

theorem map_toNat_inj64 {a b : List (BitVec 64)} (h : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h

/-- Two calls with the same public data have the same public parameters. -/
theorem mkG_eq {s₁ s₂ : State} (h : genK.pub s₁ s₂) : mkG s₁ = mkG s₂ := by
  obtain ⟨h, hy⟩ := (pub_consts (c₀ := (Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed))
    (cs := [])).mp h
  have ht := hy _ List.mem_cons_self
  sig_pub [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs] at h
  obtain ⟨hsp, hl, r3, r4, r5, r6, r7, r8, r9, r10⟩ := h
  obtain ⟨hW, hR⟩ := List.append_inj hl (by simp [Spec.Rsa.wordsAt, r10])
  have eW := map_toNat_inj64 hW
  have eR := map_toNat_inj hR
  simp only [Spec.Rsa.wordsAt, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, List.cons_append, List.cons.injEq] at eW
  obtain ⟨w0, w1, -, -⟩ := eW
  have pl : pLenOf s₁ = pLenOf s₂ := congrArg BitVec.toNat w1
  have kk : s₁.mem.readW (s₁.gpr .r10) 64 = s₂.mem.readW (s₂.gpr .r10) 64 := by
    have := w0; simp only [Nat.mul_zero, BitVec.add_zero] at this; exact this
  unfold mkG
  rw [pl, kk, eR, ht, hsp, r3, r4, r5, r6, r7, r8, r9, r10]

/-- The code leaks only what its contract makes public. -/
theorem code_ct (K1 : GeoOk g1 128 20) (K2 : GeoOk g2 256 32) (K3 : GeoOk g3 384 32) :
    ConstantTime isa genK.pre genK.pub (code g1 g2 g3) := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp e₁ e₂
  have p₁ := cin_of_pre (n := 175) s₁ h₁
  have p₂ := cin_of_pre (n := 175) s₂ h₂
  have hG := mkG_eq hp
  exact ((body_vp (G := mkG s₁) K1 K2 K3).ct _ _ _ _ _ _ ⟨s₁, s₂, ⟨⟨rfl, p₁, rfl⟩, rfl⟩, ⟨⟨rfl, p₂, hG.symm⟩, rfl⟩⟩ e₁ e₂).1

/-- The witness's memory: `state` at `0x3000` (`[0, 128, 32769 · 128, 0]`) and
the table at `0x50000`. -/
def satMem : Mem := fun a =>
  bif Nat.beq a.toNat 0x3008 then 0x80 else bif Nat.beq a.toNat 0x3010 then 0x80
    else bif Nat.beq a.toNat 0x3012 then 0x40
    else if (a - 0x50000#64).toNat < 8192 then constMem 0x50000#64 Impl.RsaKeyGen.TrialTable32.packed a else 0

/-- A 1024/160 call with an empty tape: `out` at `0x1000`, `used` at
`0x2000`, `rand` at `0x5000`, `state` at `0x3000`, `scratch` at `0x30000`,
the table at `0x50000`. -/
def searchSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 276 | .r5 => 0x2000 | .r6 => 0x5000 | .r8 => 0x30000 | .r9 => 9216
    | .r10 => 0x3000 | _ => 0
  lr := 0
  sp := 0x20000
  mem := satMem
  rd := [⟨0x5000, 0⟩, ⟨0x50000, 8192⟩]
  wr := [⟨0x1000, 276⟩, ⟨0x2000, 8⟩, ⟨0x30000, 73728⟩, ⟨0x3000, 32⟩]
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

theorem search_satisfiable : ∃ s, genK.pre s := by
  have e : constRegs [(Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed)] searchSat = _ :=
    constRegs_kT searchSat
  refine ⟨searchSat, (pre_consts (c₀ := (Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed))
    (cs := [])).mpr ⟨?_, ?_, sat_table, ?_, ?_⟩⟩
  · sig_pre [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackBelow, stripConsts]
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
    · simp only [searchSat, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
    · simp only [abi, stackBelow, List.mem_singleton] at hr
      subst hr
      exact Region.disjoint_of_sep (by decide)
  · rw [e]
    intro t ht
    rw [List.mem_singleton] at ht
    subst ht
    decide

/-- `vg_dsa_parameter_search` over the three geometries meets its contract. -/
theorem search_verified (K1 : GeoOk g1 128 20) (K2 : GeoOk g2 256 32) (K3 : GeoOk g3 384 32) :
    Verified target (code g1 g2 g3) genK :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_ok K1 K2 K3 hs; ⟨t, s', he, hq.1, hq.2⟩, code_ct K1 K2 K3,
    search_satisfiable⟩

end

end VG.Proof.Dsa.PPC64LE.Gen
