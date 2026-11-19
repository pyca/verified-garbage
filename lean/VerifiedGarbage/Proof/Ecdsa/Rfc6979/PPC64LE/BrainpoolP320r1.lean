module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Table
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.PPC64LEComb
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP320r1
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP320r1.CombLit
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Table
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.PPC64LEComb
meta import VerifiedGarbage.Spec.Ecdsa.BrainpoolP320r1
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP320r1.CombLit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Main
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.CombAll
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.Ecdsa.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP320r1
public import VerifiedGarbage.Proof.BrainpoolP320r1.PPC64LE.Comb
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Main
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.CombAll
meta import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
meta import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP320r1
meta import VerifiedGarbage.Proof.BrainpoolP320r1.PPC64LE.Comb
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.BrainpoolP320r1
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Spec.Ecdsa.Generic
meta import VerifiedGarbage.Spec.BrainpoolP320r1
meta import VerifiedGarbage.TCB.PPC64LE.Isa
meta import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `Ecdsa.PPC64LE.BrainpoolP320r1.Comb`, which only this module used -/

section

/-! ### `Ecdsa.PPC64LE.BrainpoolP320r1.Contract`, which only this module used -/

section

/-!
# ECDSA signatures over brainpoolP320r1 on PPC64LE: the contract the proof is written against

The facts of `Proof.Ecdsa.Instance.signContract Spec.Ecdsa.BrainpoolP320r1.inst` for PPC64LE, by name:
`vg_ecdsa_brainpoolp320r1_sign(out, d, digest, k, scratch)`, with the arguments in
`r3`–`r7` and the result in `r3` (ELFv2).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE.BrainpoolP320r1

open VG VG.PPC64LE Spec.Weierstrass Spec.Ecdsa

/-- The signature of the arguments, as the specification computes it. -/
abbrev sig (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith Spec.BrainpoolP320r1.curve (ofBytes (bytesAt m d 40)) (hashToInt Spec.BrainpoolP320r1.curve (bytesAt m digest 40))
    (ofBytes (bytesAt m k 40))

def signPPC : Contract PPC64LE.isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 80⟩
    let d : Region := ⟨s.gpr .r4, 40⟩
    let digest : Region := ⟨s.gpr .r5, 40⟩
    let k : Region := ⟨s.gpr .r6, 40⟩
    let scratch : Region := ⟨s.gpr .r7, 8192⟩
    s.rd = [d, digest, k] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      (s.gpr .r3).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + 40 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 40 ≤ 2 ^ 64 ∧
      (s.gpr .r6).toNat + 40 ≤ 2 ^ 64 ∧ (s.gpr .r7).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match sig s.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r6) with
    | some rs => s'.gpr .r3 = 1 ∧ bytesAt s'.mem (s.gpr .r3) 80 = encode Spec.BrainpoolP320r1.curve rs
    | none => s'.gpr .r3 = 0 ∧ bytesAt s'.mem (s.gpr .r3) 80 = List.replicate 80 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7

end VG.Proof.Ecdsa.PPC64LE.BrainpoolP320r1

end

end

/-!
# ECDSA signatures over brainpoolP320r1 by the comb on PPC64LE: `Verified`

`vg_ecdsa_brainpoolp320r1_sign` with `[k]G` by the seven-bit comb, whose table is a
read-only constant (`Abi.withConsts`): `combSign_ok`, from `signWith_ok` and
the comb as the generator; `combSign_ct`, by `taint_decide` with the
table's address public; and the contract with the table.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE.BrainpoolP320r1

open VG VG.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.Weierstrass.PPC64LE Spec.Weierstrass
open VG.Proof.Weierstrass.PPC64LE.TComb

theorem pre_of {s : State} (h : signPPC.pre s) : Pre brainpoolp320r1 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem post_of {s s' : State} (h : SignPost brainpoolp320r1 s s') : signPPC.post s s' := by
  unfold SignPost at h
  show match sig s.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r6) with
    | some rs => s'.gpr .r3 = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .r3) 80 = Spec.Ecdsa.encode Spec.BrainpoolP320r1.curve rs
    | none => s'.gpr .r3 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .r3) 80 = List.replicate 80 0
  revert h
  generalize hq : sig s.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r6) = q
  rw [show Spec.Ecdsa.signWith brainpoolp320r1.C (ofBytes (Spec.Ecdsa.bytesAt s.mem (s.gpr .r4) brainpoolp320r1.C.len))
      (Spec.Ecdsa.hashToInt brainpoolp320r1.C (Spec.Ecdsa.bytesAt s.mem (s.gpr .r5) brainpoolp320r1.C.len))
      (ofBytes (Spec.Ecdsa.bytesAt s.mem (s.gpr .r6) brainpoolp320r1.C.len)) = sig s.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r6)
    from rfl, hq]
  rcases q with _ | rs <;> exact id

/-- A state satisfying the precondition (without the table). -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x4000 | .r7 => 0x8000 | _ => 0
  lr := 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 40⟩, ⟨0x3000, 40⟩, ⟨0x4000, 40⟩]
  wr := [⟨0x1000, 80⟩, ⟨0x8000, 8192⟩]

/-- The contract as the proof states it implies the signature's (without the table). -/
theorem signPPC_implies : signPPC.Implies (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.BrainpoolP320r1.inst PPC64LE.abi) :=
    { pre := by
        sig_implies_pre [Spec.Ecdsa.BrainpoolP320r1.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
          Spec.BrainpoolP320r1.curve, Spec.Ecdsa.scratchWords, signPPC, sig, PPC64LE.abi, PPC64LE.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.Ecdsa.BrainpoolP320r1.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
          Spec.BrainpoolP320r1.curve, Spec.Ecdsa.scratchWords, signPPC, sig, PPC64LE.abi, PPC64LE.argRegs]
        simp only [signPPC, sig, Spec.BrainpoolP320r1.curve] at h
        revert h
        generalize Spec.Ecdsa.signWith _ _ _ _ = q
        rcases q with _ | rs <;> exact fun h => ⟨by rw [h.1]; rfl, h.2⟩
      pub := by
        sig_implies_pub [Spec.Ecdsa.BrainpoolP320r1.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
          Spec.BrainpoolP320r1.curve, Spec.Ecdsa.scratchWords, signPPC, sig, PPC64LE.abi, PPC64LE.argRegs]
      sat := by
        sig_implies_sat [Spec.Ecdsa.BrainpoolP320r1.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
          Spec.BrainpoolP320r1.curve, Spec.Ecdsa.scratchWords, signPPC, sig, PPC64LE.abi, PPC64LE.argRegs]
          [satState] using satState }


/-- The signature's contract with the table, as the proof states it. -/
def signPC : Contract isa := Tab.withTable signPPC brainpoolp320r1CombConsts brainpoolp320r1Comb.tsym

theorem combSign_ok (hL : Weierstrass.Law Spec.BrainpoolP320r1.curve) (s : State) (hs : signPC.pre s) :
    ∃ t s', Exec isa signBrainpoolP320r1Comb s t s' ∧ abiPreserved s s' ∧ signPC.post s s' := by
  obtain ⟨hp, hk⟩ := hs
  obtain ⟨t, s', he, K, hpost⟩ := Tab.sign_ok brainpoolp320r1_ok (by decide) hL
    (Proof.BrainpoolP320r1.PPC64LE.comb_generator_ok hL) (pre_of hp) hk
  exact ⟨t, s', he, K, Tab.post_intro (post_of hpost)⟩

theorem combSign_ct : ConstantTime isa signPC.pre signPC.pub signBrainpoolP320r1Comb :=
  VG.Taint.constantTime (A := vectorTaintSym [brainpoolp320r1Comb.tsym]) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ ⟨⟨hsp, h3, h4, h5, h6, h7⟩, sy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5
      · exact h6
      · exact h7⟩, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact sy⟩)
    (by taint_decide)

theorem combConsts_eq : brainpoolp320r1CombConsts = [(brainpoolp320r1Comb.tsym, brainpoolp320r1CombWords)] := rfl

/-- A state satisfying the precondition with the table. -/
def combSatC : State :=
  { satState with
    mem := Proof.BrainpoolP320r1.PPC64LE.combSatMem
    rd := [⟨0x2000, 40⟩, ⟨0x3000, 40⟩, ⟨0x4000, 40⟩, ⟨0x100000, 235520⟩]
    syms := fun _ => 0x100000 }

theorem combSign_sat :
    (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.BrainpoolP320r1.inst (abi.withConsts brainpoolp320r1CombConsts)).pre combSatC := by
  have hl := Proof.BrainpoolP320r1.PPC64LE.comb_words_length
  have held := Proof.BrainpoolP320r1.PPC64LE.combSatMem_held
  rw [combConsts_eq]
  obtain ⟨W, eW⟩ : ∃ W, brainpoolp320r1CombWords = W := ⟨_, rfl⟩
  rw [eW] at hl held ⊢
  generalize e : combSatC = s
  sig_pre [Spec.Ecdsa.BrainpoolP320r1.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
    Spec.BrainpoolP320r1.curve, Spec.Ecdsa.scratchWords, abi, argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
  subst e
  rw [hl]
  refine ⟨rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, by decide, ?_⟩
  · change r ∈ [⟨0x1000, 80⟩, ⟨0x8000, 8192⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl

theorem signPC_implies :
    signPC.Implies (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.BrainpoolP320r1.inst (abi.withConsts brainpoolp320r1CombConsts)) :=
  Tab.implies signPPC_implies ⟨combSatC, combSign_sat⟩

theorem combSign_verified (hL : Weierstrass.Law Spec.BrainpoolP320r1.curve) :
    Verified PPC64LE.target signBrainpoolP320r1Comb
      (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.BrainpoolP320r1.inst (PPC64LE.abi.withConsts brainpoolp320r1CombConsts)) :=
  Verified.of_correct (combSign_ok hL) combSign_ct signPC_implies

end VG.Proof.Ecdsa.PPC64LE.BrainpoolP320r1

end

end

/-! # Deterministic ECDSA on PPC64LE: brainpoolP320r1

Its signature with a given `k` (`brainpoolp320r1Core`), as the proof's curve (`brainpoolp320r1R`), the
taint checks of the blocks that depend on it (`brainpoolp320r1_blk`), and the signature
with the HMAC of a table (`brainpoolp320r1T_verified`). -/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE

/-- `vg_ecdsa_brainpoolp320r1_sign`, with `[k]G` by the comb, and brainpoolP320r1's group law `hL`. -/
def brainpoolp320r1Core (hL : Weierstrass.Law Spec.BrainpoolP320r1.curve) : Core where
  E := Spec.Ecdsa.BrainpoolP320r1.inst
  cs := Impl.Weierstrass.PPC64LE.brainpoolp320r1CombConsts
  C := Impl.Ecdsa.PPC64LE.signBrainpoolP320r1Comb
  N := "vg_ecdsa_brainpoolp320r1_sign_k"
  V := (Proof.Ecdsa.PPC64LE.BrainpoolP320r1.combSign_verified hL).1
  ct := (Proof.Ecdsa.PPC64LE.BrainpoolP320r1.combSign_verified hL).2.1
  d := by lit_decide

theorem brainpoolp320r1_nBits : Spec.Ecdsa.nBits Spec.BrainpoolP320r1.curve = 320 := by
  show Spec.BrainpoolP320r1.curve.n.log2 + 1 = 320
  have h₁ : 319 ≤ Spec.BrainpoolP320r1.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.BrainpoolP320r1.curve.n.log2 < 320 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega_using [h₁, h₂]

/-! ## The curve's blocks, and the signature with the HMAC of a table -/

theorem brainpoolp320r1_sizes : (Spec.BrainpoolP320r1.curve.len = 24 ∨ Spec.BrainpoolP320r1.curve.len = 28 ∨ Spec.BrainpoolP320r1.curve.len = 32 ∨ Spec.BrainpoolP320r1.curve.len = 40 ∨ Spec.BrainpoolP320r1.curve.len = 48 ∨ Spec.BrainpoolP320r1.curve.len = 64) ∧
    5 = (Spec.BrainpoolP320r1.curve.len + 7) / 8 ∧ Spec.Ecdsa.nBits Spec.BrainpoolP320r1.curve = 8 * Spec.BrainpoolP320r1.curve.len ∧ 2 ^ (8 * Spec.BrainpoolP320r1.curve.len) < 2 * Spec.BrainpoolP320r1.curve.n :=
  ⟨by decide, by decide, by rw [brainpoolp320r1_nBits]; decide, by decide +kernel⟩

theorem brainpoolp320r1_sh : 0 = 8 * Spec.BrainpoolP320r1.curve.len - Spec.Ecdsa.nBits Spec.BrainpoolP320r1.curve := by rw [brainpoolp320r1_nBits]; decide

theorem brainpoolp320r1_blk : RfcT (cfgC 5 40 false 0 Spec.BrainpoolP320r1.curve.n) := by rfcT_decide

/-- brainpoolP320r1, with the group law `hL`. -/
def brainpoolp320r1R (hL : Weierstrass.Law Spec.BrainpoolP320r1.curve) : RfcCurve where
  C := brainpoolp320r1Core hL
  w := 5
  big := false
  sizes := brainpoolp320r1_sizes
  sh := 0
  sh_eq := brainpoolp320r1_sh

/-- `vg_ecdsa_brainpoolp320r1_sign`, with the tables of `vs`, meets `TableInstance.signContract`. -/
theorem brainpoolp320r1T_verified (hL : Weierstrass.Law Spec.BrainpoolP320r1.curve) (vs : List Proof.HmacTable.PPC64LE.HVar)
    (hv : OK vs ∧ "VG_BRAINPOOLP320R1_COMB" ∉ Proof.HmacTable.PPC64LE.names vs) :
    Verified PPC64LE.target (signCodeT (brainpoolp320r1R hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1 Impl.Weierstrass.PPC64LE.brainpoolp320r1CombConsts vs) :=
  signT_verified ⟨rfl, by decide, by decide⟩ brainpoolp320r1_blk rfl hv.1
    (sat_one hv.1 Proof.BrainpoolP320r1.PPC64LE.combSatMem hv.2
      (by rw [Proof.BrainpoolP320r1.PPC64LE.comb_words_length]; decide) Proof.BrainpoolP320r1.PPC64LE.combSatMem_held (by decide) rfl)

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
