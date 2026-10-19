module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.HeaderCT
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Montgomery
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Sieve
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Residue
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Load
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.HeaderCT
meta import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Montgomery
meta import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Sieve
meta import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Residue
meta import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Load
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMs
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH parameter generation on x86-64: timing of nested workspace operations -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Impl.Bignum.X86_64 (sArr)
open VG.Impl.Bignum.X86_64.Public

structure InnerPublic where
  B : Addr
  w : Nat
  wr : List Region
  src : Addr
  len : Nat
  gen : BitVec 64

def InnerHeader (p : InnerPublic) (s : State) : Prop :=
  InnerKW p.B p.wr ∧ HP (off p.B 256) p.wr (gvs (off p.B 256) p.w) s

def InnerNumber (p : InnerPublic) (s : State) : Prop :=
  InnerHeader p s ∧ s.gpr .rsi = p.src ∧ s.gpr .rcx = BitVec.ofNat 64 p.len

private theorem pins_innerNumber : Pins InnerNumber [.rsi, .rcx] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h₁.2.1.trans h₂.2.1.symm
  · exact h₁.2.2.trans h₂.2.2.symm

theorem inner_loadCandidate_ct : RelCT isa (Two InnerNumber) loadCandidate fun _ _ => True :=
  inner_ct InnerPublic.B InnerPublic.wr gS (fun p => gvs (off p.B 256) p.w) [.rsi, .rcx] (by decide)
    (fun p => gvs_fst _ _) (fun _ _ h => h.1) pins_innerNumber (by taint_decide)

theorem inner_loadWitness_ct : RelCT isa (Two InnerNumber) (loadNumber aXm) fun _ _ => True :=
  inner_ct InnerPublic.B InnerPublic.wr gS (fun p => gvs (off p.B 256) p.w) [.rsi, .rcx] (by decide)
    (fun p => gvs_fst _ _) (fun _ _ h => h.1) pins_innerNumber (by taint_decide)

theorem inner_sieve_ct : RelCT isa (Two InnerHeader) sieve fun _ _ => True :=
  inner_ct InnerPublic.B InnerPublic.wr gS (fun p => gvs (off p.B 256) p.w) [] (by decide)
    (fun p => gvs_fst _ _) (fun _ _ h => h) (pins_nil _) (by taint_decide)

theorem inner_generator_ct : RelCT isa (Two fun p s => InnerHeader p s ∧ s.gpr .rdx = p.gen)
    generatorCheck fun _ _ => True :=
  inner_ct InnerPublic.B InnerPublic.wr gS (fun p => gvs (off p.B 256) p.w) [.rdx] (by decide)
    (fun p => gvs_fst _ _) (fun _ _ h => h.1)
    (fun _ _ _ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h₁.2.trans h₂.2.symm)
    (by taint_decide)

theorem inner_preparePrefix_ct : RelCT isa (Two InnerHeader)
    (VG.Impl.Bignum.X86_64.seqs [.block prepareHead, VG.Impl.Bignum.X86_64.setWord aOne .rcx,
      .block [.mov .r10 (.mem (VG.Impl.Bignum.X86_64.hdr (sArr aN)))]]) fun _ _ => True :=
  inner_ct InnerPublic.B InnerPublic.wr gS (fun p => gvs (off p.B 256) p.w) [] (by decide)
    (fun p => gvs_fst _ _) (fun _ _ h => h) (pins_nil _) (by taint_decide)

theorem inner_copyR1_ct : RelCT isa (Two InnerHeader) copyR1 fun _ _ => True :=
  inner_ct InnerPublic.B InnerPublic.wr gS (fun p => gvs (off p.B 256) p.w) [] (by decide)
    (fun p => gvs_fst _ _) (fun _ _ h => h) (pins_nil _) (by taint_decide)

theorem inner_negateR1_ct : RelCT isa (Two InnerHeader) negateR1 fun _ _ => True :=
  inner_ct InnerPublic.B InnerPublic.wr gS (fun p => gvs (off p.B 256) p.w) [] (by decide)
    (fun p => gvs_fst _ _) (fun _ _ h => h) (pins_nil _) (by taint_decide)

theorem inner_expSetup_ct : RelCT isa (Two InnerHeader)
    (VG.Impl.Bignum.X86_64.seqs VG.Impl.RsaKeyGen.X86_64.Candidate.expSetup) fun _ _ => True :=
  inner_ct InnerPublic.B InnerPublic.wr gS (fun p => gvs (off p.B 256) p.w) [] (by decide)
    (fun p => gvs_fst _ _) (fun _ _ h => h) (pins_nil _) (by taint_decide)

theorem inner_oddTest_ct : RelCT isa (Two InnerHeader) (.block oddTest) fun _ _ => True :=
  inner_ct InnerPublic.B InnerPublic.wr gS (fun p => gvs (off p.B 256) p.w) [] (by decide)
    (fun p => gvs_fst _ _) (fun _ _ h => h) (pins_nil _) (by taint_decide)

end VG.Proof.Ffdh.X86_64.ParameterCandidate
