import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideTry
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFourStep

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64

private theorem bit_and_ite (P Q : Prop) [Decidable P] [Decidable Q] :
    ((if P then 1 else 0) : BitVec 32) &&& (if Q then 1 else 0) =
      if P ∧ Q then 1 else 0 := by
  by_cases hp : P <;> by_cases hq : Q <;> simp only [hp,hq,ite_true,ite_false,
    and_true,and_false] <;> rfl

private theorem all_succ (P : Nat → Prop) (n : Nat) :
    (∀j<n+1,P j) ↔ (∀j<n,P j) ∧ P n := by
  constructor
  · intro h; exact ⟨fun j hj => h j (by omega),h n (by omega)⟩
  · rintro ⟨h,hn⟩ j hj
    by_cases he : j=n
    · subst j; exact hn
    · exact h j (by omega)

/-- Each accumulated lane bit describes the same lane in all preceding
four-candidate probes. -/
theorem quarterMask_word {s : State} (hc : Constants s) (n : Nat) {e : Nat} (he : e<4) :
    vword (quarterMask (wideInitial s) n) e =
      if ∀j<n,candidate s.mem (s.gpr .x2+BitVec.ofNat 64 (12*j+3*e))<8380417 then 1 else 0 := by
  have ha (j : Nat) :
      vword (accepted (quarterValues (wideInitial s) j) ((wideInitial s).v .v5)) e =
        if candidate s.mem (s.gpr .x2+BitVec.ofNat 64 (12*j+3*e))<8380417 then 1 else 0 := by
    have hv : (vword (quarterValues (wideInitial s) j) e).toNat=
        candidate s.mem (s.gpr .x2+BitVec.ofNat 64 (12*j+3*e)) := by
      unfold quarterValues
      change (vword (candidates (s.mem.read (s.gpr .x2+BitVec.ofNat 64 (12*j)) 16) (s.v .v4)) e).toNat=_
      rw [candidates_word _ _ _ he (hc.mask e he),Offset.add_add]
    change vword (accepted (quarterValues (wideInitial s) j) (s.v .v5)) e = _
    rw [accepted_word _ _ he (hc.modulus e he) (by rw [hv]; exact candidate_bound _ _),hv]
  induction n with
  | zero =>
    change vword (ofVDwords (s.gpr .x12) (s.gpr .x12)) e=_
    rw [hc.ones]
    have hh : ∀e<4,vword (ofVDwords 0x100000001 0x100000001) e=1 := by decide +kernel
    rw [hh e he,ite_eq_left (by simp)]
  | succ n ih =>
    rw [quarterMask]
    rw [show vword (quarterMask (wideInitial s) n &&&
      accepted (quarterValues (wideInitial s) n) ((wideInitial s).v .v5)) e =
      vword (quarterMask (wideInitial s) n) e &&&
      vword (accepted (quarterValues (wideInitial s) n) ((wideInitial s).v .v5)) e by
        exact BitVec.extractLsb'_and]
    rw [ih,ha,bit_and_ite]
    simp only [all_succ]

/-- The horizontal branch flag is zero exactly when all sixteen candidates
are acceptable; no rejected value can enter the vector-store path. -/
theorem wideMask_all {s : State} (hc : Constants s) :
    ((vdword (quarterMask (wideInitial s) 4) 0 &&& vdword (quarterMask (wideInitial s) 4) 1) ^^^
      s.gpr .x12)=0 ↔
      ∀e<4,∀j<4,candidate s.mem (s.gpr .x2+BitVec.ofNat 64 (12*j+3*e))<8380417 := by
  rw [hc.ones,←ofVWords_vword (quarterMask (wideInitial s) 4),
    quarterMask_word hc 4 (by decide : 0<4),quarterMask_word hc 4 (by decide : 1<4),
    quarterMask_word hc 4 (by decide : 2<4),quarterMask_word hc 4 (by decide : 3<4)]
  let P (e : Nat) := ∀j<4,candidate s.mem (s.gpr .x2+BitVec.ofNat 64 (12*j+3*e))<8380417
  have hh := reduce_accept_bits (decide (P 0)) (decide (P 1)) (decide (P 2)) (decide (P 3))
  simp only [decide_eq_true_eq] at hh
  rw [hh]
  constructor
  · rintro ⟨h0,h1,h2,h3⟩ e he
    rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 by omega) with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · intro h; exact ⟨h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide)⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
