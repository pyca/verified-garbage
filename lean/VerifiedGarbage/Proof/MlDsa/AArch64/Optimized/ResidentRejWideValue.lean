module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFrame
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTry
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFourStep
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.AArch64.Sums

/-! ### `MlDsa.AArch64.Optimized.ResidentRejWideFold`, which only this module used -/

section

/-! ## From `ResidentRejWide.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def quarterCode (j : Nat) : List Instr :=
 let d := wideRegs[j]!
 [.addImm .x .x6 .x2 (12*j),.ldrq .v0 .x6 0,.vop (.tbl d .v0 .v3),
  .vop (.logic .and d d .v4),.vop (.sub .s4 .v2 d .v5),
  .vop (.shift .ushr .s4 .v2 .v2 31),.vop (.logic .and .v20 .v20 .v2)]

/-- One quarter of a sixteen-candidate probe updates only its own value
vector and the accumulated acceptance mask. Source buffers remain untouched. -/
theorem quarter_ok {s : State} {j : Nat} (hj : j<4)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 (12*j)) 16)
    (hi : s.v .v3=gatherIndex) :
    WP isa (.block (quarterCode j)) s fun t =>
      ProbeFrame [.x6] [.v0,wideRegs[j]!, .v2,.v20] s t ∧
      t.v wideRegs[j]! =candidates (s.mem.read (s.gpr .x2+BitVec.ofNat 64 (12*j)) 16) (s.v .v4) ∧
      t.v .v20=s.v .v20 &&&
        accepted (candidates (s.mem.read (s.gpr .x2+BitVec.ofNat 64 (12*j)) 16) (s.v .v4)) (s.v .v5) := by
  let d := wideRegs[j]!
  have hn : d≠.v0 ∧ d≠.v2 ∧ d≠.v3 ∧ d≠.v4 ∧ d≠.v5 ∧ d≠.v20 := by
    rcases (show j=0 ∨ j=1 ∨ j=2 ∨ j=3 by omega_using [hj]) with rfl | rfl | rfl | rfl <;> decide
  have hvpres : ∀r∈preservedV,r∉[.v0,d,.v2,.v20] := by
    rcases (show j=0 ∨ j=1 ∨ j=2 ∨ j=3 by omega_using [hj]) with rfl | rfl | rfl | rfl <;> decide
  have hadd : WP isa (.block [.addImm .x .x6 .x2 (12*j)]) s fun a =>
      Only [.x6] s a ∧ a.gpr .x6=s.gpr .x2+BitVec.ofNat 64 (12*j) := by
    refine wp_addImm (by omega_using [hj]) fun a ha ea => wp_nil ⟨ha,ea⟩
  change WP isa (.block (([.addImm .x .x6 .x2 (12*j)] : List Instr)++_)) s _
  refine wp_scalar (by rfl) hadd fun a ⟨ha,ea⟩ hava => ?_
  refine wp_ldrq (a := s.gpr .x2+BitVec.ofNat 64 (12*j)) (by decide)
    (by rw [ea]; exact ptr_zero _) (by rw [ha.rd,ha.wr]; exact hr) fun b hb => ?_
  rw [show ([Instr.vop (.tbl d .v0 .v3),.vop (.logic .and d d .v4),
      .vop (.sub .s4 .v2 d .v5),.vop (.shift .ushr .s4 .v2 .v2 31),
      .vop (.logic .and .v20 .v20 .v2)] : List Instr)=
      ([.vop (.tbl d .v0 .v3),.vop (.logic .and d d .v4),
      .vop (.sub .s4 .v2 d .v5),.vop (.shift .ushr .s4 .v2 .v2 31)] : List Instr)++
      [.vop (.logic .and .v20 .v20 .v2)] from rfl,WP.block_append_iff]
  refine WP.mono (decode_ok hn.2.1 hn.2.2.2.1 hn.2.2.2.2.1
    (by rw [hb.other .v3 (by decide),hava]; exact hi)) fun c ⟨hc,hval,hbits⟩ => ?_
  refine wp_vop (d := .v20) rfl fun t ht => WP.block_nil_iff.mpr ?_
  have hvc : VChg [.v0,d,.v2,.v20] a t :=
    ((hb.chg.trans hc).trans ht.chg).mono (by
      intro r hr
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
      grind only)
  refine ⟨((ProbeFrame.ofScalar ha hava).trans (ProbeFrame.ofVector hvc hvpres)).mono
    (by simp) (by simp [d]),?_,?_⟩
  · rw [ht.other d hn.2.2.2.2.2,hval,hb.v,ha.mem,hb.other .v4 (by decide),hava]
  · rw [ht.v,hc.get .v20 (by simp [Ne.symm hn.2.2.2.2.2]),
      hb.other .v20 (by decide),hbits,hb.v,ha.mem,hb.other .v4 (by decide),
      hb.other .v5 (by decide),hava]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejWideFold.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

abbrev wideVectors : List VReg := [.v0,.v2,.v20,.v16,.v17,.v18,.v19]

def quarterValues (s : State) (j : Nat) : BitVec 128 :=
 candidates (s.mem.read (s.gpr .x2+BitVec.ofNat 64 (12*j)) 16) (s.v .v4)

def quarterMask (s : State) : Nat → BitVec 128
 | 0 => s.v .v20
 | j+1 => quarterMask s j &&& accepted (quarterValues s j) (s.v .v5)

structure QuarterPost (s : State) (n : Nat) (t : State) : Prop where
 frame : ProbeFrame [.x6] wideVectors s t
 values : ∀j<n,t.v wideRegs[j]! = quarterValues s j
 mask : t.v .v20=quarterMask s n

private theorem wide_ne {j : Nat} (hj : j<4) :
    wideRegs[j]! ≠ .v0 ∧ wideRegs[j]! ≠ .v2 ∧ wideRegs[j]! ≠ .v20 := by
  rcases (show j=0 ∨ j=1 ∨ j=2 ∨ j=3 by omega_using [hj]) with rfl | rfl | rfl | rfl <;> decide

private theorem wide_inj {i j : Nat} (hi : i<4) (hj : j<4) (hne : i≠j) :
    wideRegs[i]! ≠ wideRegs[j]! := by
  have hh : ∀i<4,∀j<4,wideRegs[i]! =wideRegs[j]! → i=j := by decide +kernel
  exact fun he => hne (hh i hi j hj he)

/-- Compose the four independent probes while preserving earlier decoded
vectors and accumulating their acceptance bits. -/
theorem quarters_ok (n : Nat) (hn : n≤4) {s : State}
    (hi : s.v .v3=gatherIndex)
    (hr : ∀j<n,InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 (12*j)) 16) :
    WP isa (.block ((List.range n).flatMap quarterCode)) s (QuarterPost s n) := by
  induction n with
  | zero =>
    exact WP.block_nil_iff.mpr ⟨⟨Only.refl _ _,fun _ _ => rfl⟩,
      fun _ h => absurd h (Nat.not_lt_zero _),rfl⟩
  | succ n ih =>
    have hn4 : n<4 := by omega_using [hn]
    rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hn]) (fun j hj => hr j (by omega_using [hj]))) fun a ha => ?_
    refine WP.mono (quarter_ok (s := a) hn4
      (by rw [ha.frame.only.rd,ha.frame.only.wr,ha.frame.only.get .x2]; exact hr n (by omega_using []))
      (by rw [ha.frame.vectors .v3 (by decide)]; exact hi)) fun t ⟨ht,hval,hmask⟩ => ?_
    have hv : candidates (a.mem.read (a.gpr .x2+BitVec.ofNat 64 (12*n)) 16) (a.v .v4)=
        quarterValues s n := by
      rw [ha.frame.only.mem,ha.frame.only.get .x2,ha.frame.vectors .v4 (by decide)]
      rfl
    have hframe : ProbeFrame [.x6] wideVectors s t := (ha.frame.trans ht).mono
      (by simp) (by
        intro r hr'
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr'
        rcases hr' with h | rfl | h | rfl | rfl
        · simpa only [wideVectors,List.mem_cons,List.not_mem_nil,or_false] using h
        · decide
        · rcases h with rfl
          rcases (show n=0 ∨ n=1 ∨ n=2 ∨ n=3 by omega_using [hn]) with rfl | rfl | rfl | rfl <;> decide
        · decide
        · decide)
    refine ⟨hframe,?_,?_⟩
    · intro j hj
      by_cases he : j=n
      · subst j
        rw [hval,hv]
      · rw [ht.vectors _ (by
          have hh := wide_ne (j := j) (by omega_using [hn, hj])
          simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
          exact ⟨hh.1,wide_inj (by omega_using [hn, hj]) hn4 he,hh.2.1,hh.2.2⟩)]
        exact ha.values j (by omega_using [hj, he])
    · rw [hmask,hv,ha.mask,ha.frame.vectors .v5 (by decide)]
      rfl

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

end

end


/-! ## From `ResidentRejWideTry.lean` -/

@[expose] public section

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
  · intro h; exact ⟨fun j hj => h j (by omega_using [hj]),h n (by omega_using [])⟩
  · rintro ⟨h,hn⟩ j hj
    by_cases he : j=n
    · subst j; exact hn
    · exact h j (by omega_using [hj, he])

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
    rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 by omega_using [he]) with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · intro h; exact ⟨h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide)⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end
