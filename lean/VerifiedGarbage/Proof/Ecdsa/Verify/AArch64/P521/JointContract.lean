module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointMain
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointMain
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointAbi
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPrefix
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPrefix
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Lit
public import VerifiedGarbage.Impl.AArch64Instrs
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Lit
import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Verified
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
meta import Mathlib.Data.Finset.Card
meta import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Tables
public import VerifiedGarbage.Spec.Ecdsa.P521
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Tables
meta import VerifiedGarbage.Spec.Ecdsa.P521
meta import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
meta import VerifiedGarbage.Proof.Framework.GetElem

/-! ### `Ecdsa.Verify.AArch64.P521.Contract`, which this module and modules that import it used -/

section

/-!
# ECDSA verification over P-521 on AArch64: the contract the proof is written against

The facts of `Proof.Ecdsa.verifyContract Spec.Ecdsa.P521.inst` for AArch64, by name:
`vg_ecdsa_p521_verify(public = x0, digest = x1, sig = x2, scratch = x3)`,
the result in `w0`. Only the pointers are public here: the proof shows that
nothing else affects timing, although the contract would let the contents of
the three buffers.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.P521

open VG VG.AArch64 Spec.Weierstrass Spec.Ecdsa
open VG.Impl.Ecdsa.AArch64 (p521)
open VG.Proof.Ecdsa.AArch64.P521 (TblHeld p521_combConsts p521_combWords_length satMem satMem_held)

/-- Whether the signature at `sig` of the hash at `digest` is valid for the
public key at `pk`, as the specification says. -/
abbrev vf (m : Mem) (pk digest sig : Addr) : Bool :=
  verify Spec.P521.curve (bytesAt m pk 133) (hashToInt Spec.P521.curve (bytesAt m digest 66)) (bytesAt m sig 132)

def verifyAArch64 : Contract AArch64.isa where
  pre s :=
    let pk : Region := ⟨s.gpr .x0, 133⟩
    let digest : Region := ⟨s.gpr .x1, 66⟩
    let sig : Region := ⟨s.gpr .x2, 132⟩
    let scratch : Region := ⟨s.gpr .x3, 8192⟩
    s.rd = [pk, digest, sig, ⟨s.syms p521.tsym, 8 * p521.combWords.length⟩] ∧ s.wr = [scratch] ∧
      pk.Disjoint scratch ∧ digest.Disjoint scratch ∧ sig.Disjoint scratch ∧
      (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64 ∧ TblHeld s [scratch]
  post s s' := (s'.gpr .x0).setWidth 32 = if vf s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) then 1 else 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp ∧ s₁.syms p521.tsym = s₂.syms p521.tsym

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .x0, 133⟩, ⟨s.gpr .x1, 66⟩, ⟨s.gpr .x2, 132⟩,
      ⟨s.syms p521.tsym, 8 * p521.combWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x3, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .x0, 133⟩ ⟨s.gpr .x3, 8192⟩)
    (h2 : Region.Disjoint ⟨s.gpr .x1, 66⟩ ⟨s.gpr .x3, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .x2, 132⟩ ⟨s.gpr .x3, 8192⟩)
    (f0 : (s.gpr .x0).toNat + 133 ≤ 2 ^ 64) (f1 : (s.gpr .x1).toNat + 66 ≤ 2 ^ 64)
    (f2 : (s.gpr .x2).toNat + 132 ≤ 2 ^ 64) (f3 : (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64)
    (ht : TblHeld s [⟨s.gpr .x3, 8192⟩])
    (hal : (s.syms p521.tsym).toNat % 64 = 0) :
    (Proof.Ecdsa.verifyContract Spec.Ecdsa.P521.inst (AArch64.abi.withConsts p521.combConsts)).pre s := by
  sig_pre [Spec.Ecdsa.P521.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig,
    Spec.P521.curve, Spec.Ecdsa.scratchWords, AArch64.abi, AArch64.argRegs, p521_combConsts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact hdw, hal, by rw [hrd]; rfl, hw, h1, h2, h3, f0, f1, f2,
    f3⟩

/-- A state satisfying the precondition: the tables at `0x100000`. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x8000 | _ => 0
  sp := 0x20000
  mem := satMem
  rd := [⟨0x1000, 133⟩, ⟨0x2000, 66⟩, ⟨0x3000, 132⟩, ⟨0x100000, 764928⟩]
  wr := [⟨0x8000, 8192⟩]
  syms _ := 0x100000

theorem sat_spec :
    (Proof.Ecdsa.verifyContract Spec.Ecdsa.P521.inst (AArch64.abi.withConsts p521.combConsts)).pre satState := by
  have hl := p521_combWords_length
  have held : ∀ i < p521.combWords.length, satState.mem.readW (satState.syms p521.tsym +
      BitVec.ofNat 64 (8 * i)) 64 = p521.combWords.getD i 0 := satMem_held
  refine spec_pre (by rw [hl]; rfl) rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide)) (by decide) (by decide)
    (by decide) (by decide) ⟨held, ?_, ?_⟩ (by decide)
  all_goals rw [hl]
  · decide
  · simp only [List.mem_singleton]
    rintro r rfl; exact Region.disjoint_of_sep (by decide)

theorem implies : verifyAArch64.Implies
    (Proof.Ecdsa.verifyContract Spec.Ecdsa.P521.inst (AArch64.abi.withConsts p521.combConsts)) where
  pre s h := by
    sig_pre [Spec.Ecdsa.P521.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig,
      Spec.P521.curve, Spec.Ecdsa.scratchWords, AArch64.abi, AArch64.argRegs, p521_combConsts,
      Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨hd, hheld, hfit, hdw, -, ht, hw, h1, h2, h3, -, -, -, h4⟩ := h
    refine ⟨?_, hw, h1, h2, h3, h4, hheld, hfit, by rw [hw] at hdw; exact hdw⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
  post := by
    sig_implies_post [Spec.Ecdsa.P521.inst, Proof.Ecdsa.verifyContract,
      Proof.Ecdsa.verifySig, Spec.P521.curve, Spec.Ecdsa.scratchWords, AArch64.abi,
      AArch64.argRegs, p521_combConsts, Abi.withConsts, verifyAArch64, vf]
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ecdsa.P521.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig,
      Spec.P521.curve, Spec.Ecdsa.scratchWords, AArch64.abi, AArch64.argRegs, p521_combConsts,
      Abi.withConsts] at h
    obtain ⟨hsp, hsy, -, h0, h1, h2, h3⟩ := h
    exact ⟨h0, h1, h2, h3, hsp, hsy⟩
  sat := ⟨satState, sat_spec⟩

end VG.Proof.Ecdsa.Verify.AArch64.P521

end

end

/-! The joint P-521 verifier satisfies the existing public verification contract.
The width-seven generator and width-five peer digits share one doubling chain;
all branch decisions depend only on the contract's public signature inputs. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.P521

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P521

theorem pre_of {s : State} (h : verifyAArch64.pre s) : VPre p521 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, held, fit, hdw⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, ⟨by rw [h1]; simp, held, fit, hdw _ (by simp)⟩⟩

theorem verify_a64 (hL : Weierstrass.Law Spec.P521.curve) (hO : Weierstrass.PrimeOrder Spec.P521.curve)
    (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (s : State)
    (hs : verifyAArch64.pre s) :
    ∃ t s', Exec isa verifyP521 s t s' ∧ abiPreserved s s' ∧ verifyAArch64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := Joint.verify_ok (p521_ok hI) hL hO (by decide) hT
    (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of he verify_callsKeep verify_untouched verify_keepsV hsv, hpost⟩

/-- The contract's public inputs: the pointers, the table, and the key, digest and signature. -/
theorem jacPublic_of_spec {s₁ s₂ : State}
    (pub : (Proof.Ecdsa.verifyContract Spec.Ecdsa.P521.inst (AArch64.abi.withConsts p521.combConsts)).pub s₁ s₂) :
    JacPublic p521 s₁ s₂ := by
  sig_pub [Spec.Ecdsa.P521.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig,
    Spec.P521.curve, Spec.Ecdsa.scratchWords, AArch64.abi, AArch64.argRegs, p521_combConsts,
    Abi.withConsts] at pub
  obtain ⟨hsp, hsy, inputs, h0, h1, h2, h3⟩ := pub
  refine ⟨⟨hsp, fun r hr => ?_⟩, hsy, ?_, ?_, ?_⟩
  · simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  all_goals
    have eqBytes := (List.map_inj_right (fun (a b : BitVec 8) h => BitVec.eq_of_toNat_eq h)).mp inputs
    have parts := List.append_inj eqBytes (by simp only [List.length_append, Weierstrass.length_bytesAt])
    have front := List.append_inj parts.1 (by simp only [Weierstrass.length_bytesAt])
  · exact front.1
  · exact front.2
  · exact parts.2

end VG.Proof.Ecdsa.Verify.AArch64.P521
