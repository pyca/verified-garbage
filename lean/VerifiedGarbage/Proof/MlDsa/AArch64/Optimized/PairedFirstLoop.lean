module

import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFirstMemory
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedStageRun
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFive
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedTableMemory
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.GetElem

/-! ### `MlDsa.AArch64.Optimized.PairedTableDecode`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.PairedTable
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase (z bar)

theorem Words.layer1 {m : Mem} {p : Addr} (h : Words m p)
    {u g e : Nat} (hu : u<8) (hg : g<4) (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (480*u+0+32*g)) 16) e=BitVec.ofNat 32 (z (255-16*u-4*g-e)) ∧
    vword (m.read (p+BitVec.ofNat 64 (480*u+0+32*g+16)) 16) e=BitVec.ofNat 32 (bar (z (255-16*u-4*g-e))) := by
  exact h.row (by decide) he (by omega_using [hu, hg]) (layer1_values hu hg he)

theorem Words.layer2 {m : Mem} {p : Addr} (h : Words m p)
    {u g e : Nat} (hu : u<8) (hg : g<4) (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (480*u+128+32*g)) 16) e=BitVec.ofNat 32 (z (127-8*u-2*g-e/2)) ∧
    vword (m.read (p+BitVec.ofNat 64 (480*u+128+32*g+16)) 16) e=BitVec.ofNat 32 (bar (z (127-8*u-2*g-e/2))) := by
  exact h.row (by decide) he (by omega_using [hu, hg]) (layer2_values hu hg he)

theorem Words.layer4 {m : Mem} {p : Addr} (h : Words m p)
    {u g e : Nat} (hu : u<8) (hg : g<4) (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (480*u+256+32*g)) 16) e=BitVec.ofNat 32 (z (63-4*u-g)) ∧
    vword (m.read (p+BitVec.ofNat 64 (480*u+256+32*g+16)) 16) e=BitVec.ofNat 32 (bar (z (63-4*u-g))) := by
  exact h.row (by decide) he (by omega_using [hu, hg]) (layer4_values hu hg he)

theorem Words.layer8 {m : Mem} {p : Addr} (h : Words m p)
    {u g e : Nat} (hu : u<8) (hg : g<2) (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (480*u+384+32*g)) 16) e=BitVec.ofNat 32 (z (31-2*u-g)) ∧
    vword (m.read (p+BitVec.ofNat 64 (480*u+384+32*g+16)) 16) e=BitVec.ofNat 32 (bar (z (31-2*u-g))) := by
  exact h.row (by decide) he (by omega_using [hu, hg]) (layer8_values hu hg he)

theorem Words.layer16 {m : Mem} {p : Addr} (h : Words m p)
    {u e : Nat} (hu : u<8) (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (480*u+448)) 16) e=BitVec.ofNat 32 (z (15-u)) ∧
    vword (m.read (p+BitVec.ofNat 64 (480*u+464)) 16) e=BitVec.ofNat 32 (bar (z (15-u))) := by
  exact h.row (g := 0) (off := 448) (by decide) he (by omega_using [hu]) (layer16_values hu he)

theorem Words.tail {m : Mem} {p : Addr} (h : Words m p)
    {j e : Nat} (hj : j<8) (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (3840+32*j)) 16) e=BitVec.ofNat 32 (tailRoot j) ∧
    vword (m.read (p+BitVec.ofNat 64 (3840+32*j+16)) 16) e=BitVec.ofNat 32 (bar (tailRoot j)) := by
  have hv := tail_values hj he
  have h0 : 3840+32*j=4*(960+8*j) := by omega_using []
  have h1 : 3840+32*j+16=4*(960+8*j+4) := by omega_using []
  constructor
  · rw [h0,h.vector (by omega_using [hj]) he,hv.1]
  · rw [h1,h.vector (by omega_using [hj]) he,show 960+8*j+4+e=960+8*j+e+4 by omega_using [],hv.2]

end VG.Proof.MlDsa.AArch64.Optimized.PairedTable

end

end

/-! ### `MlDsa.AArch64.Optimized.PairedFirstRoots`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Inverse

theorem local_words {m : Mem} {p : Addr} (h : PairedTable.Words m p)
    {u : Nat} (hu : u<8) (i : Fin 7) {e : Nat} (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (480*u+localOffset i.val)) 16) e=BitVec.ofInt 32 (localRoot u i.val e) ∧
    vword (m.read (p+BitVec.ofNat 64 (480*u+localOffset i.val+16)) 16) e=
      BitVec.ofInt 32 (reciprocal (localRoot u i.val e)) := by
  by_cases hi : i.val<4
  · simp only [localOffset,localRoot,localIndex,hi,ite_true,← Nat.add_assoc]
    exact nat_row (n := VG.Impl.MlDsa.AArch64.Optimized.Inverse.z (63-4*u-i.val)) (h.layer4 (u := u) (g := i.val) (e := e) hu hi he)
  · by_cases hj : i.val<6
    · simp only [localOffset,localRoot,localIndex,hi,hj,ite_false,ite_true,← Nat.add_assoc]
      exact nat_row (n := VG.Impl.MlDsa.AArch64.Optimized.Inverse.z (31-2*u-(i.val-4))) (h.layer8 (u := u) (g := i.val-4) (e := e) hu (by omega_using [hj]) he)
    · simp only [localOffset,localRoot,localIndex,hi,hj,ite_false]
      exact nat_row (n := VG.Impl.MlDsa.AArch64.Optimized.Inverse.z (15-u)) (h.layer16 (u := u) (e := e) hu he)


theorem packed_words {m : Mem} {p : Addr} (h : PairedTable.Words m p)
    {u g len e : Nat} (hu : u<8) (hg : g<4) (hl : len=1 ∨ len=2) (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (480*u+packedOffset g len)) 16) e=BitVec.ofInt 32 (packedRoot u g len e) ∧
    vword (m.read (p+BitVec.ofNat 64 (480*u+packedOffset g len+16)) 16) e=
      BitVec.ofInt 32 (reciprocal (packedRoot u g len e)) := by
  rcases hl with rfl | rfl
  · simp only [packedRoot,packedOffset,ite_true,← Nat.add_assoc]
    exact nat_row (n := VG.Impl.MlDsa.AArch64.Optimized.Inverse.z (255-16*u-4*g-e))
      (h.layer1 (u := u) (g := g) (e := e) hu hg he)
  · simp only [packedRoot,packedOffset,show ¬(2=1) by decide,ite_false,← Nat.add_assoc]
    exact nat_row (n := VG.Impl.MlDsa.AArch64.Optimized.Inverse.z (127-8*u-2*g-e/2))
      (h.layer2 (u := u) (g := g) (e := e) hu hg he)

theorem packed_tableRoots {s : State} {p : Addr} {u : Nat} (hu : u<8)
    (h : PairedTable.Words s.mem p)
    (hr : ∀ off, off+16≤4096 → InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 off) 16)
    (hx : s.gpr .x1=p+BitVec.ofNat 64 (480*u))
    (hq : ∀ e<4, vword (s.v .v31) e=8380417#32) : PackedRoots s (packedRoot u) := by
  refine ⟨hq,fun g _ len _ e _ => packedRoot_range u g len e,?_,?_,?_⟩
  · intro g hg len hl b hb
    rw [hx,BitVec.add_assoc,← BitVec.ofNat_add]
    have ho : packedOffset g len≤224 := by
      rcases hl with rfl | rfl <;> simp [packedOffset] <;> omega_using [hg]
    exact hr _ (by rcases hb with rfl | rfl <;> omega_using [hu, ho])
  · intro g hg len hl e he
    rw [hx,BitVec.add_assoc,← BitVec.ofNat_add]
    exact (packed_words h hu hg hl he).1
  · intro g hg len hl e he
    rw [hx,BitVec.add_assoc,← BitVec.ofNat_add]
    simpa only [Nat.add_assoc] using (packed_words h hu hg hl he).2

theorem local_tableReady {s : State} {p : Addr} {u : Nat} (hu : u<8)
    (h : PairedTable.Words s.mem p)
    (hr : ∀off,off+16≤4096 → InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 off) 16)
    (hx : s.gpr .x1=p+BitVec.ofNat 64 (480*u)) (i : Fin 7) :
    RootReady s (localOffset i.val) (localRoot u i.val) := by
  have hb := localOffset_bound i
  refine ⟨hb.2,by omega_using [hb],?_,?_,fun e _ => localRoot_range u i e,?_,?_⟩
  · rw [hx,BitVec.add_assoc,← BitVec.ofNat_add]
    exact hr _ (by omega_using [hu, hb])
  · rw [hx,BitVec.add_assoc,← BitVec.ofNat_add]
    exact hr _ (by omega_using [hu, hb])
  · intro e he
    rw [hx,BitVec.add_assoc,← BitVec.ofNat_add]
    exact (local_words h hu i he).1
  · intro e he
    rw [hx,BitVec.add_assoc,← BitVec.ofNat_add]
    simpa only [Nat.add_assoc] using (local_words h hu i he).2

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end


/-! ## From `PairedAdvance.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem firstAdvance_ok (s : State) : WP isa (.block firstAdvance) s fun t =>
    ((t.gpr .x0=s.gpr .x0+128 ∧ t.gpr .x1=s.gpr .x1+480 ∧
      t.gpr .x13=s.gpr .x13+128 ∧ t.gpr .x14=s.gpr .x14+128 ∧
      t.gpr .x11=s.gpr .x11-1 ∧ t.mem=s.mem) ∧
      Keep [.x0,.x1,.x11,.x13,.x14] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold firstAdvance
  arun
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedFirstLoop.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (Keep)

theorem tableWords_frame {m m' : Mem} {p : Addr} {rs : List Region}
    (h : PairedTable.Words m p) (hf : Frame rs m m')
    (hd : ∀r∈rs,(⟨p,4096⟩:Region).Disjoint r) : PairedTable.Words m' p := by
  intro k hk
  rw [hf.readW (r:=⟨p,4096⟩) (by exact Offset.contains_base p (by omega_using [hk]) (by omega_using [hk])) hd (by decide)]
  exact h k hk

theorem firstLoop_ok {s : State}
    (ht : PairedTable.Words s.mem (s.gpr .x1))
    (hd : ((⟨s.gpr .x1,4096⟩ : Region)).Disjoint ((⟨s.gpr .x0,2048⟩ : Region)))
    (hc : s.gpr .x11=8) (hq : ProductConstants s)
    (hrt : ∀ off, off+16≤4096 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hr : ∀ u<8, ∀ i : Fin 8,
      InRegions (s.rd++s.wr) ((s.gpr .x13+BitVec.ofNat 64 (128*u))+BitVec.ofNat 64 (16*i.val)) 16 ∧
      ∀poly:Fin 2,InRegions (s.rd++s.wr) ((s.gpr .x14+BitVec.ofNat 64 (128*u))+BitVec.ofNat 64 (1024*poly.val+16*i.val)) 16)
    (hw : ∀ u<8, ∀poly:Fin 2,∀ i : Fin 8, InRegions s.wr
      ((s.gpr .x0+BitVec.ofNat 64 (128*u))+BitVec.ofNat 64 (1024*poly.val+16*i.val)) 16) :
    WP isa (.loop (.block (firstCode++firstAdvance)) (.nonzero .x .x11)) s fun t =>
      Keep [.x0,.x1,.x11,.x13,.x14] s t ∧ ProductConstants t ∧
      t.gpr .x0=s.gpr .x0+1024 ∧ t.gpr .x1=s.gpr .x1+3840 ∧
      t.gpr .x13=s.gpr .x13+1024 ∧ t.gpr .x14=s.gpr .x14+1024 ∧
      t.mem=firstPassMem s.mem (s.gpr .x0) (s.gpr .x13) (s.gpr .x14) 8 := by
  let I := fun u t => Keep [.x0,.x1,.x11,.x13,.x14] s t ∧ ProductConstants t ∧
    t.gpr .x0=s.gpr .x0+BitVec.ofNat 64 (128*u) ∧
    t.gpr .x1=s.gpr .x1+BitVec.ofNat 64 (480*u) ∧
    t.gpr .x13=s.gpr .x13+BitVec.ofNat 64 (128*u) ∧
    t.gpr .x14=s.gpr .x14+BitVec.ofNat 64 (128*u) ∧
    t.mem=firstPassMem s.mem (s.gpr .x0) (s.gpr .x13) (s.gpr .x14) u
  apply VG.Proof.MlDsa.AArch64.Arith.wp_countdown (N := 8) (by decide) (by decide) I ?_ ?_ hc
  · intro u hu t hi _
    rcases hi with ⟨hk,hqt,hp0,hp1,hp13,hp14,hm⟩
    have hf : Frame [(⟨s.gpr .x0,2048⟩ : Region)] s.mem t.mem := by
      rw [hm]; exact firstPass_frame (by omega_using [hu])
    have ht' : PairedTable.Words t.mem (s.gpr .x1) :=
      tableWords_frame ht hf (by simpa only [List.mem_singleton,forall_eq,Region] using hd)
    have hrt' : ∀ off, off+16≤4096 → InRegions (t.rd++t.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16 := by
      simpa only [hk.rd,hk.wr] using hrt
    have hqword : ∀ e<4, vword (t.v .v31) e=8380417#32 := by
      intro e he
      rw [hqt.qv,VG.Proof.MlKem.AArch64.vword_ofVWords _ _ _ _ he]
      have heq : e=0 ∨ e=1 ∨ e=2 ∨ e=3 := by omega_using [he]
      rcases heq with rfl | rfl | rfl | rfl <;> rfl
    refine first_ok u hqt (packed_tableRoots hu ht' hrt' hp1 hqword)
      (local_tableReady hu ht' hrt' hp1) ?_ ?_ fun t₁ ⟨v,hv,hv₁⟩ => ?_
    · intro j hj
      constructor
      · simpa only [hk.rd,hk.wr,hp13] using (hr u hu ⟨j,hj⟩).1
      · intro poly hpoly
        simpa only [hk.rd,hk.wr,hp14] using (hr u hu ⟨j,hj⟩).2 ⟨poly,hpoly⟩
    · intro poly j
      simpa only [hk.wr,hp0] using hw u hu poly j
    · have hk₁ : Keep [] t t₁ := (hv.keep.trans hv₁.keep).mono
      refine WP.mono (firstAdvance_ok t₁) fun t₂ ⟨⟨⟨hp₂,hp₃,hp₄,hp₅,hc₂,hm₂⟩,hk₂⟩,hvec₂⟩ => ?_
      refine ⟨⟨((hk.trans hk₁).trans hk₂).mono,?_,?_,?_,?_,?_,?_⟩,?_⟩
      · exact ⟨by rw [hvec₂,hv₁.v,hv.get .v31 (by decide)]; exact hqt.qv,
          by rw [hvec₂,hv₁.v,hv.get .v30 (by decide)]; exact hqt.qiv⟩
      · rw [hp₂,hk₁.get .x0,hp0]
        rw [show 128*(u+1)=128*u+128 by omega_using [],BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hp₃,hk₁.get .x1,hp1]
        rw [show 480*(u+1)=480*u+480 by omega_using [],BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hp₄,hk₁.get .x13,hp13]
        rw [show 128*(u+1)=128*u+128 by omega_using [],BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hp₅,hk₁.get .x14,hp14]
        rw [show 128*(u+1)=128*u+128 by omega_using [],BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hm₂,hv₁.mem]
        simp only [inputValues_eq,hm,hp0,hp13,hp14,firstPassMem]
      · rw [hc₂,hk₁.get .x11]; rfl
  · exact ⟨Keep.refl _ _,hq,by simp,by simp,by simp,by simp,rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end
