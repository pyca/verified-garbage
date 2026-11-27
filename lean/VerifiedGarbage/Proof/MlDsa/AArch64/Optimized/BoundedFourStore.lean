module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourTable
public import VerifiedGarbage.Proof.MlDsa.Sample.HalfByte
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourCompact
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.BoundedFour
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `MlDsa.AArch64.Optimized.BoundedFourVec`, which this module and modules that import it used -/

section

/-! ## From `BoundedFourWord.lean` -/

@[expose] public section

section

/-! Exact finite half-byte arithmetic used by the vector parser. -/
namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.Spec.MlDsa VG.Proof.MlDsa.Sample

/-- The lane value after the eta-specific reduction and unsigned minimum. -/
def valueWord (η : Nat) (x : BitVec 32) : BitVec 32 :=
 let r := if η=2 then x-((x*13#32)>>>6)*5#32 else x
 let v := BitVec.ofNat 32 (q+η)-r
 if v.toNat ≤ (v-8380417#32).toNat then v else v-8380417#32

/-- The acceptance bit before multiplication by the lane's mask weight. -/
def acceptWord (η : Nat) (x : BitVec 32) : BitVec 32 :=
 (x-BitVec.ofNat 32 (rbB η))>>>31

theorem valueWord_two : ∀ b < 16,
    valueWord 2 (BitVec.ofNat 32 b) = BitVec.ofNat 32 (ofInt (rbC 2 b)).val := by decide

theorem valueWord_four : ∀ b < 16,
    valueWord 4 (BitVec.ofNat 32 b) = BitVec.ofNat 32 (ofInt (rbC 4 b)).val := by decide

theorem valueWord_eq {η : Nat} (hη : η=2 ∨ η=4) {b : Nat} (hb : b<16) :
    valueWord η (BitVec.ofNat 32 b) = BitVec.ofNat 32 (ofInt (rbC η b)).val := by
  rcases hη with rfl | rfl
  · exact valueWord_two b hb
  · exact valueWord_four b hb

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourVec.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour

/-- Canonicalize all four eta-minus-nibble values in registers. -/
theorem valueTail_ok (η : Nat) {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀e<4,vword (s.v .v21) e=8380417#32)
    (hη : ∀e<4,vword (s.v .v20) e=BitVec.ofNat 32 (Spec.MlDsa.q+η))
    (k : ∀t,VChg [.v1,.v2] s t →
      (∀e<4,vword (t.v .v1) e=
        let v:=BitVec.ofNat 32 (Spec.MlDsa.q+η)-vword (s.v .v1) e
        if v.toNat≤(v-8380417#32).toNat then v else v-8380417#32) →
      WP isa (.block rest) t Q) :
    WP isa (.block (valueTail++rest)) s Q := by
  refine wp_vop (d := .v1) rfl fun a ha => wp_vop (d := .v2) rfl fun b hb =>
    wp_vop (d := .v1) rfl fun t ht => ?_
  refine k t (((ha.chg.trans hb.chg).trans ht.chg).mono ?_) ?_
  · intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  · intro e he
    rw [ht.v,VG.AArch64.vword_map2 _ _ _ he,hb.v,VG.AArch64.vword_map2 _ _ _ he,
      hb.get .v1 (by decide),ha.v,VG.AArch64.vword_map2 _ _ _ he,
      ha.get .v21 (by decide),hq e he,hη e he]

/-- Exact per-lane arithmetic for the selected eta=2 and eta=4 kernels. -/
theorem vectorVal_ok (η : Nat) {s : State} {rest : List Instr} {Q : State → Prop}
    (h13 : ∀e<4,vword (s.v .v18) e=13#32)
    (h5 : ∀e<4,vword (s.v .v19) e=5#32)
    (hq : ∀e<4,vword (s.v .v21) e=8380417#32)
    (hη : ∀e<4,vword (s.v .v20) e=BitVec.ofNat 32 (Spec.MlDsa.q+η))
    (k : ∀t,VChg [.v1,.v2] s t →
      (∀e<4,vword (t.v .v1) e=valueWord η (vword (s.v .v1) e)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (vectorVal η++rest)) s Q := by
  by_cases he : η=2
  · subst η
    simp only [vectorVal,BEq.rfl,ite_true,List.cons_append,List.nil_append]
    refine wp_vop (d := .v2) rfl fun a ha => wp_vop (d := .v2) rfl fun b hb =>
      wp_vop (d := .v2) rfl fun c hc => wp_vop (d := .v1) rfl fun d hd => ?_
    have hkeep : VChg [.v1,.v2] s d :=
      (((ha.chg.trans hb.chg).trans hc.chg).trans hd.chg).mono (by
        intro r hr
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
        grind only)
    have hr (e : Nat) (he : e<4) :
        vword (d.v .v1) e=vword (s.v .v1) e-((vword (s.v .v1) e*13#32)>>>6)*5#32 := by
      rw [hd.v,VG.AArch64.vword_map2 _ _ _ he,hc.get .v1 (by decide),
        hb.get .v1 (by decide),ha.get .v1 (by decide),hc.v,VG.AArch64.vword_map2 _ _ _ he,
        hb.get .v19 (by decide),ha.get .v19 (by decide),h5 e he,
        hb.v,VG.AArch64.vword_map2 _ _ _ he,ha.v,VG.AArch64.vword_map2 _ _ _ he,h13 e he]
      rfl
    refine valueTail_ok 2 (fun e he => by rw [hkeep.v .v21 (by decide)]; exact hq e he)
      (fun e he => by rw [hkeep.v .v20 (by decide)]; exact hη e he) fun t ht hv => ?_
    refine k t ((hkeep.trans ht).mono (by
      intro r hr; simpa only [List.mem_append,or_self] using hr)) ?_
    intro e he
    rw [hv e he,hr e he]
    rfl
  · simp only [vectorVal,beq_iff_eq,he,ite_false,List.nil_append]
    refine valueTail_ok η hq hη fun t ht hv => k t ht ?_
    intro e hb
    rw [hv e hb]
    simp only [valueWord,he,ite_false]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

end

end

/-! ## From `BoundedFourValues.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (acceptedIndices vectorVal)

/-- Reduction and compaction preserve every accepted value, with no assumptions
about the ignored lanes that are subsequently overwritten by the parser. -/
theorem valueCompact_ok {η mask : Nat} (hη : η=2∨η=4) (hm : mask<16)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (h13 : ∀e<4,vword (s.v .v18) e=13#32)
    (h5 : ∀e<4,vword (s.v .v19) e=5#32)
    (hq : ∀e<4,vword (s.v .v21) e=8380417#32)
    (heta : ∀e<4,vword (s.v .v20) e=BitVec.ofNat 32 (Spec.MlDsa.q+η))
    (h6 : s.v .v6=shuffleWord mask)
    (hn : ∀e<4,(vword (s.v .v1) e).toNat<16)
    (k : ∀t,VChg [.v1,.v2] s t →
      (∀i<(acceptedIndices mask).length,vword (t.v .v1) i=
        BitVec.ofNat 32 (Spec.MlDsa.ofInt (VG.Proof.MlDsa.Sample.rbC η
          (vword (s.v .v1) (acceptedIndices mask)[i]!).toNat)).val) →
      WP isa (.block rest) t Q) :
    WP isa (.block (vectorVal η++(.vop (.tbl .v1 .v1 .v6)::rest))) s Q := by
  refine vectorVal_ok η h13 h5 hq heta fun a ha hv=>?_
  refine compact_ok hm (by rw [ha.get .v6]; exact h6) fun t ht hc=>?_
  refine k t ((ha.trans ht).mono (by decide)) ?_
  intro i hi
  rw [hc i hi,hv _ (index_bound mask hm i hi)]
  have hh:=valueWord_eq hη (hn _ (index_bound mask hm i hi))
  simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using hh

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourStore.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Arith.Neon (coeffAt_write16)

/-- A full vector store is safe with four free slots; only its accepted prefix
extends the meaningful scalar output. Later lanes may be overwritten. -/
theorem stored_append_vector {m : Mem} {p : Addr} {L A : List Zq} {v : BitVec 128}
    (hL : L.length+4≤256) (hA : A.length≤4) (hs : Stored m p L)
    (hv : ∀i<A.length,vword v i=zw (A.getD i 0)) :
    Stored (m.write (coeffAddr p L.length) 16 v) p (L++A) := by
  intro i hi
  have hil : i<L.length+A.length:=by simpa only [List.length_append] using hi
  rw [coeffAt_write16 _ _ hL _ (by omega_using [hL, hA, hil])]
  by_cases hbefore : i<L.length
  · rw [ite_eq_right (by omega_using [hbefore]),hs i hbefore]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left hbefore]
  · rw [ite_eq_left (by omega_using [hA, hil, hbefore]),hv _ (by omega_using [hil, hbefore])]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega_using [hbefore] : L.length≤i)]

theorem storeAccepted_ok {s : State} {p : Addr} {L A : List Zq}
    (hL : L.length+4≤256) (hA : A.length≤4) (hs : Stored s.mem p L)
    (h3 : s.gpr .x3=coeffAddr p L.length)
    (hw : InRegions s.wr (coeffAddr p L.length) 16)
    (hv : ∀i<A.length,vword (s.v .v1) i=zw (A.getD i 0)) :
    WP isa (.block [.strq .v1 .x3 0]) s fun t=>
      VG.Proof.MlKem.AArch64.Keep [] s t ∧ t.gpr=s.gpr ∧ t.v=s.v ∧
      Frame [polyR p] s.mem t.mem ∧ Stored t.mem p (L++A) := by
  refine VG.Proof.MlKem.AArch64.wp_strq (by decide) (by simpa using h3) hw fun t ht=>
    VG.Proof.MlKem.AArch64.wp_nil ?_
  refine ⟨ht.keep,ht.gpr,ht.v,?_,?_⟩
  · rw [ht.mem]
    exact (Frame.refl [polyR p] s.mem).write (by simp) _
      (VG.Proof.MlDsa.AArch64.Arith.Neon.vector_contains p hL)
  · rw [ht.mem]
    exact stored_append_vector hL hA hs hv

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end
