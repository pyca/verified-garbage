module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.CT
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig

/-!
# DSA's probable-prime test on PPC64LE: verified

`correct`: the contract's postcondition (with the table, `abi.withConsts`),
from `code_ok`. `constantTime`: from `code_ct`, the contract's public data
(the arguments, the stack pointer, the candidate, the tape's octets and the
table's address) giving the same `PD` in both runs. `satisfiable`: an
all-ones candidate and an empty tape. `verified`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Prime
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.ProbablePrime
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Two)

/-- The contract, with the table. -/
abbrev contract (bits : Nat) : Contract isa :=
  Proof.Dsa.ProbablePrime.contract (layout bits) (abi.withConsts K) 176

theorem pre_of {bits : Nat} {s : State} (hs : (contract bits).pre s) : CIn bits s ∧ ConstsOk K 176 s := by
  unfold contract Proof.Dsa.ProbablePrime.contract at hs
  obtain ⟨hp, hk⟩ := pre_consts.mp hs
  exact ⟨CIn.ofStrip (cin_of_pre bits _ hp), hk⟩

theorem correct (Ri : RoundImpl) {bits : Nat} (hb : Bits bits) (s : State) (hs : (contract bits).pre s) :
    ∃ t s', Exec isa (code bits Ri.name Ri.code) s t s' ∧ abiPreserved s s' ∧ (contract bits).post s s' := by
  obtain ⟨h, hk⟩ := pre_of hs
  obtain ⟨t, s', he, hc⟩ := code_ok Ri hb h hk
  refine ⟨t, s', he, hc.abi, ?_⟩
  unfold contract Proof.Dsa.ProbablePrime.contract
  refine post_consts.mpr ?_
  sig_post [Proof.Dsa.ProbablePrime.sig, abi, argRegs]
  refine ⟨?_, hc.keeps, hc.used⟩
  rw [hc.r3, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have := status_le (res bits s)
  simp only [res, cand, tape] at this ⊢
  omega

theorem constantTime (Ri : RoundImpl) {bits : Nat} (hb : Bits bits) :
    ConstantTime isa (contract bits).pre (contract bits).pub (code bits Ri.name Ri.code) := by
  refine RelCT.constantTime ((code_ct Ri hb).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ?_) fun _ _ h => h)
  obtain ⟨c₁, k₁⟩ := pre_of h₁
  obtain ⟨c₂, k₂⟩ := pre_of h₂
  unfold contract Proof.Dsa.ProbablePrime.contract at hp
  obtain ⟨hp, hsy⟩ := pub_consts.mp hp
  sig_pub [Proof.Dsa.ProbablePrime.sig, abi, argRegs] at hp
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7⟩ := hp
  obtain ⟨hc, ht⟩ := List.cons.inj hl
  have ht' : tape s₁ = tape s₂ :=
    (List.map_inj_right fun _ _ e => BitVec.eq_of_toNat_eq e).mp ht
  refine ⟨⟨s₁.gpr .r3, s₁.gpr .r4, s₁.gpr .r5, s₁.gpr .r6, s₁.gpr .r7, s₁.sp, s₁.syms VG.Impl.RsaKeyGen.TrialTable32.symbol,
    cand bits s₁, tape s₁⟩, ⟨hb, c₁, k₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨hb, c₂, k₂, h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, hsp.symm, (hsy _ List.mem_cons_self).symm, hc.symm,
      ht'.symm⟩⟩

end VG.Proof.Dsa.PPC64LE.Prime
