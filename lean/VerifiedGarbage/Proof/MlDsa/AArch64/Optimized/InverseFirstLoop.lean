module

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.SliceFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFive
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Slice
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! ### `MlDsa.AArch64.Optimized.InverseFiveSlice`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg VMem)

def fiveSliceCode : List Instr := firstLoads ++ fiveCode ++ firstStores

def fiveSliceMem (u : Nat) (s : State) : Mem :=
  writeBank (fiveValues u (readBank s.mem (s.gpr .x0) 16)) (s.gpr .x0) 16 s.mem

theorem firstLoads_eq : firstLoads=(bankLoads (regs 0) 16).map (fun p => Instr.ldrq p.1 .x0 p.2) := by decide +kernel
theorem firstStores_eq : firstStores=(bankLoads (regs 7) 16).map (fun p => Instr.strq p.1 .x0 p.2) := rfl

theorem fiveSlice_ok (u : Nat) {s : State} {rest : List Instr} {Q : State → Prop}
    (hp : PackedRoots s (packedRoot u)) (hl : TableRoots localOffset (localRoot u) s)
    (hr : ∀ i : Fin 8, InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*i.val)) 16)
    (hw : ∀ i : Fin 8, InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 (16*i.val)) 16)
    (k : ∀ t, (∃ mid, VChg runRegs s mid ∧ VMem mid t (fiveSliceMem u s)) → WP isa (.block rest) t Q) :
    WP isa (.block (fiveSliceCode ++ rest)) s Q := by
  have ho : ∀ i : Fin 8, (16*i.val)%16=0 ∧ 16*i.val<65536 := by intro i; omega_using []
  have hsub : ((bankLoads (regs 0) 16).map Prod.fst)⊆packedRegs := by decide +kernel
  simp only [fiveSliceCode,firstLoads_eq,firstStores_eq,List.append_assoc]
  refine loadBank_ok (regs 0) 16 .x0 initial_inj ho hr fun s₁ hc₁ hb₁ => ?_
  have hc₁' := hc₁.mono hsub
  refine five_ok u hb₁ (hp.frame hc₁') (hl.frame hc₁' (by decide)) fun s₂ hc₂ hb₂ => ?_
  refine storeBank_ok (regs 7) 16 .x0 ho hb₂ ?_ fun t hm => ?_
  · intro i
    simpa only [hc₂.gpr,hc₂.wr,hc₁.gpr,hc₁.wr] using hw i
  · have hc : VChg runRegs s s₂ := VChg.mono (hc₁'.trans hc₂) (by
      intro r h
      rcases List.mem_append.mp h with h | h
      · exact (show packedRegs⊆runRegs by decide) h
      · exact h)
    have hm' : VMem s₂ t (fiveSliceMem u s) := by
      simpa only [fiveSliceMem,hc₂.mem,hc₁.mem,hc₂.gpr,hc₁.gpr] using hm
    exact k t ⟨s₂,hc,hm'⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def firstPassMem (m : Mem) (p : Addr) : Nat → Mem
  | 0 => m
  | u+1 => let prior := firstPassMem m p u
           let base := p+BitVec.ofNat 64 (128*u)
           writeBank (fiveValues u (readBank prior base 16)) base 16 prior

theorem firstAdvance_ok (s : State) :
    WP isa (.block firstAdvance) s fun t =>
      ((t.gpr .x0=s.gpr .x0+128 ∧ t.gpr .x1=s.gpr .x1+480 ∧
        t.gpr .x11=s.gpr .x11-1 ∧ t.mem=s.mem) ∧ Keep [.x0,.x1,.x11] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold firstAdvance
  arun
  exact ⟨rfl,rfl,rfl⟩

/-- Output stores preserve every static reciprocal-table word. -/
theorem tableWords_frame {m m' : Mem} {p : Addr} {rs : List Region}
    (h : InverseTable.Words m p) (hf : Frame rs m m')
    (hd : ∀ r∈rs, (⟨p,3904⟩ : Region).Disjoint r) : InverseTable.Words m' p := by
  intro k hk
  rw [hf.readW (r := ⟨p,3904⟩) (by
    exact VG.Offset.contains_base p (by omega_using [hk]) (by omega_using [hk])) hd (by decide)]
  exact h k hk

/-- All local stores stay within the output polynomial. -/
theorem firstPass_frame {m : Mem} {p : Addr} {u : Nat} (hu : u≤8) :
    Frame [⟨p,1024⟩] m (firstPassMem m p u) := by
  induction u with
  | zero => exact Frame.refl _ _
  | succ u ih =>
    simp only [firstPassMem]
    apply writeBank_frame _ _ _ (r := ⟨p,1024⟩) (by simp) ?_ (ih (by omega_using [hu]))
    intro i
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact VG.Offset.contains_base p (by omega_using [hu]) (by omega_using [hu])

/-- Eight contiguous five-layer blocks, retaining exact memory and the public
cursors needed by the final strided pass. -/
theorem firstLoop_ok {s : State}
    (ht : InverseTable.Words s.mem (s.gpr .x1))
    (hd : (⟨s.gpr .x1,3904⟩ : Region).Disjoint ⟨s.gpr .x0,1024⟩)
    (hc : s.gpr .x11=8)
    (hq : ∀ e<4, vword (s.v .v31) e=8380417#32)
    (hrt : ∀ off, off+16≤3904 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hr : ∀ u<8, ∀ i : Fin 8, InRegions (s.rd++s.wr)
      ((s.gpr .x0+BitVec.ofNat 64 (128*u))+BitVec.ofNat 64 (16*i.val)) 16)
    (hw : ∀ u<8, ∀ i : Fin 8, InRegions s.wr
      ((s.gpr .x0+BitVec.ofNat 64 (128*u))+BitVec.ofNat 64 (16*i.val)) 16) :
    WP isa (.loop (.block (fiveSliceCode++firstAdvance)) (.nonzero .x .x11)) s fun t =>
      Keep [.x0,.x1,.x11] s t ∧ (∀ e<4, vword (t.v .v31) e=8380417#32) ∧
      t.gpr .x0=s.gpr .x0+1024 ∧ t.gpr .x1=s.gpr .x1+3840 ∧
      t.mem=firstPassMem s.mem (s.gpr .x0) 8 := by
  let I := fun u t => Keep [.x0,.x1,.x11] s t ∧
    (∀ e<4, vword (t.v .v31) e=8380417#32) ∧
    t.gpr .x0=s.gpr .x0+BitVec.ofNat 64 (128*u) ∧
    t.gpr .x1=s.gpr .x1+BitVec.ofNat 64 (480*u) ∧
    t.mem=firstPassMem s.mem (s.gpr .x0) u
  apply VG.Proof.MlDsa.AArch64.Arith.wp_countdown (N := 8) (by decide) (by decide) I ?_ ?_ hc
  · intro u hu t hi _
    rcases hi with ⟨hk,hqt,hp0,hp1,hm⟩
    have ht' : InverseTable.Words t.mem (s.gpr .x1) := by
      rw [hm]
      exact tableWords_frame ht (firstPass_frame (by omega_using [hu])) (by
        intro r hr
        have he := List.mem_singleton.mp hr
        subst r
        exact hd)
    have hrt' : ∀ off, off+16≤3904 → InRegions (t.rd++t.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16 := by
      simpa only [hk.rd,hk.wr] using hrt
    refine fiveSlice_ok u (packed_tableRoots hu ht' hrt' hp1 hqt)
      (local_tableRoots hu ht' hrt' hp1 hqt) ?_ ?_ fun t₁ ⟨v,hv,hv₁⟩ => ?_
    · intro i
      simpa only [hk.rd,hk.wr,hp0] using hr u hu i
    · intro i
      simpa only [hk.wr,hp0] using hw u hu i
    · have hk₁ : Keep [] t t₁ := (hv.keep.trans hv₁.keep).mono
      refine WP.mono (firstAdvance_ok t₁) fun t₂ ⟨⟨⟨hp₂,hp₃,hc₂,hm₂⟩,hk₂⟩,hvec₂⟩ => ?_
      refine ⟨⟨((hk.trans hk₁).trans hk₂).mono,?_,?_,?_,?_⟩,?_⟩
      · intro e he
        rw [hvec₂,hv₁.v,hv.get .v31 (by decide)]
        exact hqt e he
      · rw [hp₂,hk₁.get .x0,hp0]
        rw [show 128*(u+1)=128*u+128 by omega_using [],BitVec.ofNat_add,BitVec.add_assoc]
        rfl
      · rw [hp₃,hk₁.get .x1,hp1]
        rw [show 480*(u+1)=480*u+480 by omega_using [],BitVec.ofNat_add,BitVec.add_assoc]
        rfl
      · rw [hm₂,hv₁.mem]
        simp only [fiveSliceMem,hm,hp0,firstPassMem]
      · rw [hc₂,hk₁.get .x11]
        rfl
  · exact ⟨Keep.refl _ _,hq,by simp,by simp,rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
