module

-- separate module: the disjoint five-slot conversion induction is independent of peer validity and scalar recoding

public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Code
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.RepresentationMemory
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-! The five disjoint ordinary-field boundaries at the end of peer validation. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime montBase)
open VG.Impl.Weierstrass.AArch64.P521Native (sequence)

def prepareFromSlots (ds : List Nat) : Prog isa := sequence (ds.map fun d =>
  .block (VG.Impl.Weierstrass.AArch64.P521Native.representationMemoryCode
    VG.Impl.Weierstrass.AArch64.P521Native.representationFromCode d))

theorem prepare_from_slots_ok (ds : List Nat) (nd : ds.Nodup) {s : State} {base : Addr} {W : Nat}
    (hs : Scr s base W) (bounds : ∀d∈ds,wordsVal s.mem base d 9<fieldPrime)
    (fits : ∀d∈ds,d+72≤W) (aligned : ∀d∈ds,d%8=0)
    (apart : ∀d∈ds,∀e∈ds,d≠e → d+72≤e ∨ e+72≤d) :
    WP isa (prepareFromSlots ds) s fun t =>
      Scr t base W ∧ (∀d∈ds,wordsVal t.mem base d 9<fieldPrime ∧
        Fin.ofNat fieldPrime (wordsVal t.mem base d 9)=toM fieldPrime montBase (wordsVal s.mem base d 9)) ∧
      KeepRegs representationClob s t ∧ Unch base (ds.map fun d => (d,72)) s.mem t.mem := by
  induction ds generalizing s with
  | nil =>
    apply WP.block_nil
    refine ⟨hs,?_,⟨fun _ _ => rfl,rfl,rfl,rfl⟩,Unch.refl _ _ _⟩
    intro d hd
    cases hd
  | cons d ds ih =>
    rw [prepareFromSlots,sequence,List.map_cons,List.foldr_cons]
    refine WP.seq (WP.mono (representation_from_memory hs (fits d (by simp)) (aligned d (by simp))
      (bounds d (by simp))) fun u ⟨value,bound,k,outside⟩ => ?_)
    have hsu := hs.of_keepRegs k (by decide)
    have unchanged (e : Nat) (he : e∈ds) : wordsVal u.mem base e 9=wordsVal s.mem base e 9 := by
      apply outside.wordsVal
      · have sep := apart e (by simp [he]) d (by simp)
          (fun h => (List.nodup_cons.mp nd).1 (h ▸ he))
        simpa only [Nat.reduceMul] using sep
      · have h := fits e (by simp [he]); have hn:=hs.enc
        omega_arith
    have later := ih (List.nodup_cons.mp nd).2 hsu (fun e he => by rw [unchanged e he]; exact bounds e (by simp [he]))
      (fun e he => fits e (by simp [he])) (fun e he => aligned e (by simp [he]))
      (fun e he f hf hef => apart e (by simp [he]) f (by simp [hf]) hef)
    refine WP.mono later fun t ⟨hst,values,kt,ut⟩ => ?_
    have keepFirst : wordsVal t.mem base d 9=wordsVal u.mem base d 9 := by
      apply ut.wordsVal
      · intro w hw
        obtain ⟨e,he,rfl⟩ := List.mem_map.mp hw
        have sep := apart d (by simp) e (by simp [he]) (fun h => (List.nodup_cons.mp nd).1 (h.symm ▸ he))
        simpa only [Nat.reduceMul] using sep
      · have h:=fits d (by simp); have hn:=hs.enc
        omega_arith
    refine ⟨hst,?_,k.trans kt,?_⟩
    · intro e he
      rcases List.mem_cons.mp he with equal|he
      · subst e
        rw [keepFirst,value]
        have canonical := bounds d (List.mem_cons_self ..)
        have field := fromMontValue_field canonical
        refine ⟨?_,field⟩
        exact Eq.mp (congrArg (fun n => n<fieldPrime) value) bound
      · have ev := values e he
        rw [unchanged e he] at ev
        exact ev
    · exact outside.unch.trans ut

def prepareRepresentations : Prog isa := prepareFromSlots [2800,3160,424,496,568]

theorem prepare_representations_ok {s : State} {base : Addr} (hs : Scr s base 8192)
    (bounds : ∀d∈[2800,3160,424,496,568],wordsVal s.mem base d 9<fieldPrime) :
    WP isa prepareRepresentations s fun t =>
      Scr t base 8192 ∧ (∀d∈[2800,3160,424,496,568],wordsVal t.mem base d 9<fieldPrime ∧
        Fin.ofNat fieldPrime (wordsVal t.mem base d 9)=toM fieldPrime montBase (wordsVal s.mem base d 9)) ∧
      KeepRegs representationClob s t ∧ Unch base [(2800,72),(3160,72),(424,72),(496,72),(568,72)] s.mem t.mem := by
  exact prepare_from_slots_ok _ (by decide) hs bounds (by decide) (by decide) (by decide)

end VG.Proof.Weierstrass.AArch64.P521Native
