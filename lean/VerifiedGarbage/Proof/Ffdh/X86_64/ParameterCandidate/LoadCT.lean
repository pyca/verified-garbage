module

public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Load
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Load
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMs
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH parameter generation on x86-64: timing of candidate and witness loading -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Impl.Bignum.X86_64.Public

structure NumberPub where
  B : Addr
  w : Nat
  wr : List Region
  src : Addr
  len : Nat

def NumberHeader (p : NumberPub) (s : State) : Prop :=
  (KW p.B p.wr ∧ HP p.B p.wr (gvs p.B p.w) s) ∧
    s.gpr .rsi = p.src ∧ s.gpr .rcx = BitVec.ofNat 64 p.len

private theorem pins_number : Pins NumberHeader [.rsi, .rcx] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h₁.2.1.trans h₂.2.1.symm
  · exact h₁.2.2.trans h₂.2.2.symm

theorem loadCandidate_ct : RelCT isa (Two NumberHeader) loadCandidate fun _ _ => True :=
  kt_ct NumberPub.B NumberPub.wr gS (fun p => gvs p.B p.w) [.rsi, .rcx] (by decide)
    (fun p => gvs_fst p.B p.w) (fun _ _ h => h.1) pins_number (by taint_decide)

theorem loadWitness_ct : RelCT isa (Two NumberHeader) (loadNumber aXm) fun _ _ => True :=
  kt_ct NumberPub.B NumberPub.wr gS (fun p => gvs p.B p.w) [.rsi, .rcx] (by decide)
    (fun p => gvs_fst p.B p.w) (fun _ _ h => h.1) pins_number (by taint_decide)

end VG.Proof.Ffdh.X86_64.ParameterCandidate
