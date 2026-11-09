module

-- separate module: the canonical conversion/recoding postcondition is checked independently of peer validation

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.PrepareAssemble
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-! Ordinary point/constant slots and bounded scalar input are established together. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
attribute [local instance high] instPowNat
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime montBase)
open VG.Impl.Weierstrass.AArch64.P521Native (outerBlock005)

def prepareFieldScalar : Prog isa := .seq prepareRepresentations (.block outerBlock005)

def prepareReadyWrites : List (Nat × Nat) :=
  [(2800,72),(3160,72),(424,72),(496,72),(568,72),(2296,72),(3944,80)]

/-- The end of preparation keeps the original scalar and validity flag while
leaving all five ordinary-field slots and the bounded offset scalar ready. -/
theorem prepare_field_scalar_ok {s : State} {base : Addr} (hs : Scr s base 8192)
    (bounds : ∀d∈[2800,3160,424,496,568],wordsVal s.mem base d 9<fieldPrime) :
    WP isa prepareFieldScalar s fun t =>
      Scr t base 8192 ∧
      (∀d∈[2800,3160,424,496,568],wordsVal t.mem base d 9<fieldPrime ∧
        Fin.ofNat fieldPrime (wordsVal t.mem base d 9)=toM fieldPrime montBase (wordsVal s.mem base d 9)) ∧
      wordsVal t.mem base 3944 10=wordsVal s.mem base 2296 9%2^521+recodeOffset ∧
      wordsVal t.mem base 3944 10<32^105 ∧ t.gpr .x19=80 ∧ t.gpr .x5=1 ∧
      wordsVal t.mem base 2368 9=wordsVal s.mem base 2368 9 ∧ word t.mem base 3232=word s.mem base 3232 ∧
      t.gpr .x20=s.gpr .x20 ∧ t.gpr .x26=s.gpr .x26 ∧
      KeepRegs (representationClob++(.x19::clob 9)) s t ∧ Unch base prepareReadyWrites s.mem t.mem := by
  rw [prepareFieldScalar]
  refine WP.seq (WP.mono (prepare_representations_ok hs bounds) fun u ⟨hsu,fields,ku,unchU⟩ => ?_)
  have inputSame : wordsVal u.mem base 2296 9=wordsVal s.mem base 2296 9 :=
    unchU.wordsVal (by decide) (by decide)
  refine WP.mono (prepare_scalar_ok hsu) fun t ⟨hst,offset,offsetBound,counter,one,kt,unchT⟩ => ?_
  have allUnch : Unch base prepareReadyWrites s.mem t.mem := unchU.trans unchT
  have kept : KeepRegs (representationClob++(.x19::clob 9)) s t :=
    (ku.mono (by intro r hr; exact List.mem_append_left _ hr)).trans
      (kt.mono (by intro r hr; exact List.mem_append_right _ hr))
  refine ⟨hst,?_,?_,offsetBound,counter,one,?_,?_,kept.gpr .x20 (by decide),
    kept.gpr .x26 (by decide),kept,allUnch⟩
  · intro d hd
    have preserved : wordsVal t.mem base d 9=wordsVal u.mem base d 9 := by
      have casesD : d=2800 ∨ d=3160 ∨ d=424 ∨ d=496 ∨ d=568 := by
        simpa only [List.mem_cons,List.not_mem_nil,or_false] using hd
      apply unchT.wordsVal
      · rcases casesD with rfl|rfl|rfl|rfl|rfl <;> decide
      · rcases casesD with rfl|rfl|rfl|rfl|rfl <;> decide
    rw [preserved]
    exact fields d hd
  · rw [offset,inputSame]
  · exact allUnch.wordsVal (by decide) (by decide)
  · exact allUnch.word (by decide) (by decide)

end VG.Proof.Weierstrass.AArch64.P521Native
