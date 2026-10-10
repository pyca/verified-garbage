import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideFold
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFourStep

/-! ## From `ResidentRejWideTry.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

/-- Initial mask consists of the public all-one acceptance bit in each lane. -/
def wideInitial (s : State) : State := s.setV .v20 (ofVDwords (s.gpr .x12) (s.gpr .x12))

/-- Exact sixteen-candidate probe, using four independent decoders and one
horizontal acceptance reduction. No input-dependent memory access occurs. -/
theorem wideTry_ok {s : State} (hi : s.v .v3=gatherIndex)
    (hr : ∀j<4,InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 (12*j)) 16) :
    WP isa (.block wideTry) s fun t =>
      ProbeFrame [.x6,.x7] wideVectors s t ∧
      (∀j<4,t.v wideRegs[j]! = quarterValues s j) ∧
      t.gpr .x6=(vdword (quarterMask (wideInitial s) 4) 0 &&&
        vdword (quarterMask (wideInitial s) 4) 1) ^^^ s.gpr .x12 := by
  rw [show wideTry=.vop (.dup .d2 .v20 .x12)::
      ((List.range 4).flatMap quarterCode++reduceRegisterCode .v20) from rfl]
  refine wp_vop (d := .v20) rfl fun a ha => ?_
  rw [WP.block_append_iff]
  refine WP.mono (quarters_ok 4 (by decide) (s := a)
    (by rw [ha.other .v3 (by decide)]; exact hi)
    (fun j hj => by rw [ha.rd,ha.wr,ha.gpr]; exact hr j hj)) fun b hb => ?_
  refine WP.mono (reduceRegister_ok b .v20) fun t ⟨ht,hvec,hflag⟩ => ?_
  have hf : ProbeFrame [.x6,.x7] wideVectors s t :=
    (((ProbeFrame.ofVector ha.chg (by decide)).trans hb.frame).trans
      (ProbeFrame.ofScalar ht hvec)).mono (by simp) (by simp [wideVectors])
  refine ⟨hf,?_,?_⟩
  · intro j hj
    rw [hvec,hb.values j hj,quarterValues,ha.mem,ha.gpr,ha.other .v4 (by decide)]
    rfl
  · rw [hflag,hb.mask,hb.frame.only.get .x12,ha.gpr]
    have hmask : quarterMask a 4=quarterMask (wideInitial s) 4 := by
      simp only [quarterMask,quarterValues,ha.v,ha.mem,ha.gpr,
        ha.other .v4 (by decide),ha.other .v5 (by decide)]
      rfl
    rw [hmask]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejWideValue.lean` -/

section

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

end
