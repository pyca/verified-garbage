module

public import VerifiedGarbage.Proof.MlDsa.Sample.RejNtt
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqPhase
public import VerifiedGarbage.Proof.MlDsa.Sample.Mem

import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Zero
import VerifiedGarbage.Proof.MlDsa.Sample.Hash
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Sponge
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Setup
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Squeeze
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Init
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Env
import VerifiedGarbage.Proof.Framework.Offset

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Sample/Rej4/Sponge.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (init setup squeezeStepWith)

structure Ready (σ s : State) : Prop where
  env : Env σ s
  out : ∀ k < 4, ∀ j < 1008, s.mem (bufP σ k+BitVec.ofNat 64 j) = F σ k j

theorem sponge_ok (sha3 : Bool) {σ : State} (hp : Pre σ) :
    WP isa (.seq (.block (init++setup))
      (.loop (squeezeStepWith sha3) (.nonzero .x .x28))) σ (Ready σ) := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (init_ok hp) fun s ⟨he,h0,h1⟩ => ?_
  refine WP.mono (setup_ok he h0 h1) fun u hu => ?_
  refine WP.mono (squeeze_ok sha3 hp hu) fun t ht => ⟨ht.env,?_⟩
  intro k hk j hj
  exact ht.out k hk j (by simpa using hj)
end VG.Proof.MlDsa.AArch64.Sample.Rej4
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Sample/Rej4/ParseMem.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlDsa.Sample (polyR coeffAddr)

def polyP (σ : State) (k : Nat) : Addr := aP σ+BitVec.ofNat 64 (1024*k)

theorem poly_sub (σ : State) {k : Nat} (hk : k < 4) : Region.Sub (polyR (polyP σ k)) (aR σ) :=
  Offset.sub_base (aP σ) (by omega)

theorem buf_sub (σ : State) {k : Nat} (hk : k < 4) : Region.Sub (⟨bufP σ k,1008⟩ : Region) (scrR σ) :=
  Offset.sub_base (scr σ) (by dsimp only [VG.Impl.MlDsa.AArch64.Sample.Rej4.oBuf]; omega)

theorem buf_poly {σ : State} (hp : Pre σ) {j k : Nat} (hj : j < 4) (hk : k < 4) :
    (⟨bufP σ j,1008⟩ : Region).Disjoint (polyR (polyP σ k)) :=
  hp.a_scr.symm.sub_left (buf_sub σ hj) |>.sub_right (poly_sub σ hk)

theorem coeffs_in {σ s : State} (hp : Pre σ) (hw : s.wr = σ.wr) {k : Nat} (hk : k < 4) :
    ∀ i < 256,InRegions s.wr (coeffAddr (polyP σ k) i) 4 := by
  intro i hi
  rw [hw,hp.wr]
  refine ⟨aR σ,by simp,?_⟩
  unfold coeffAddr polyP
  rw [Offset.add_add]
  exact Offset.contains_base _ (by omega) (by omega)

theorem Env.polyStep {σ s t : State} (hp : Pre σ) {k : Nat} (hk : k < 4) (he : Env σ s)
    (hf : Frame [polyR (polyP σ k)] s.mem t.mem)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hsp : t.sp = s.sp)
    (hg : ∀ r ∈ [Reg.x19,.x20,.x21,.x30],t.gpr r = s.gpr r) : Env σ t :=
  he.frameStep hf (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨aR σ,by simp,poly_sub σ hk⟩)
    (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.a_scr.symm.sub_left (Offset.sub_base (scr σ) (by decide)) |>.sub_right (poly_sub σ hk))
    hr hw hsp hg

theorem Ready.polyStep {σ s t : State} (hp : Pre σ) {k : Nat} (hk : k < 4) (h : Ready σ s)
    (hf : Frame [polyR (polyP σ k)] s.mem t.mem)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hsp : t.sp = s.sp)
    (hg : ∀ r ∈ [Reg.x19,.x20,.x21,.x30],t.gpr r = s.gpr r) : Ready σ t := by
  refine ⟨h.env.polyStep hp hk hf hr hw hsp hg,fun j hj i hi => ?_⟩
  rw [← h.out j hj i hi]
  exact hf _ (fun r hr hc => by
    rw [List.mem_singleton.mp hr] at hc
    exact buf_poly hp hj hk _ (Offset.contains_base _ (by omega) (by omega)) hc)
end VG.Proof.MlDsa.AArch64.Sample.Rej4
end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep wp_addImm wp_subImm wp_lsr wp_and wp_nil toNat_lsr)
open VG.Proof.MlDsa.AArch64.Sample (zeroPoly_ok)
open VG.Proof.MlDsa.Sample (rnFold G_length Stored polyR)
open VG.Impl.MlDsa.AArch64.Sample (rnLoop retZ)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (sample oBuf)

abbrev X (σ : State) (k : Nat) := Spec.MlDsa.G (B σ k) 1008
abbrev L (σ : State) (k : Nat) := rnFold [] (X σ k)
abbrev result (σ : State) (k : Nat) : BitVec 64 := if (L σ k).length = 256 then 1 else 0
abbrev parseRegs : List Reg := [.x0,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x13,.x14,.x15,.x25,.x26,.x27]

theorem sampleArgs_ok {σ s : State} (he : Env σ s) {k : Nat} (hk : k < 4) :
    WP isa (.block ([.addImm .x .x25 .x19 (1008*k),.addImm .x .x26 .x21 (1024*k)] : List Instr)) s
      fun t => Only [.x25,.x26] s t ∧ t.gpr .x25 = at' σ (1008*k) ∧ t.gpr .x26 = polyP σ k := by
  refine wp_addImm (by omega) fun u h1 e1 => wp_addImm (by omega) fun t h2 e2 => wp_nil ⟨?_,?_,?_⟩
  · exact (h1.trans h2).mono (by simp)
  · rw [h2.get .x25,e1,he.x19]; rfl
  · rw [e2,h1.get .x21,he.x21]; rfl

theorem retZ_ok {σ s : State} {k : Nat} (h4 : (s.gpr .x4).toNat = 256-(L σ k).length) :
    WP isa (.block (retZ++([.logic .and .x .x27 .x27 .x0] : List Instr))) s fun t =>
      Only [.x0,.x27] s t ∧ t.gpr .x27 = s.gpr .x27 &&& result σ k := by
  unfold retZ
  refine wp_subImm (by decide) fun u h1 e1 => wp_lsr (by decide) fun v h2 e2 =>
    wp_and fun t h3 e3 => wp_nil ⟨((h1.trans h2).trans h3).mono (by simp),?_⟩
  have hl := VG.Proof.MlDsa.Sample.rnFold_length_le (a := ([] : List Spec.MlDsa.Zq)) (by simp) (X σ k)
  have er : v.gpr .x0 = result σ k := by
    apply BitVec.eq_of_toNat_eq
    rw [e2,toNat_lsr,e1,BitVec.toNat_sub,h4]
    have one : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [one]
    unfold result
    have hn1 : (1 : BitVec 64).toNat = 1 := rfl
    have hn0 : (0 : BitVec 64).toNat = 0 := rfl
    simp only [VG.Spec.MlDsa.n] at hl
    change (L σ k).length ≤ 256 at hl
    split
    · rw [hn1]; omega
    · rw [hn0]; omega
  rw [e3,h2.get .x27,h1.get .x27,er]

theorem sample_ok {σ s : State} (hp : Pre σ) (h : Ready σ s) {k : Nat} (hk : k < 4) :
    WP isa (sample k) s fun t => Ready σ t ∧ Keep parseRegs s t ∧
      Frame [polyR (polyP σ k)] s.mem t.mem ∧ Stored t.mem (polyP σ k) (L σ k) ∧
        t.gpr .x27 = s.gpr .x27 &&& result σ k := by
  unfold sample
  refine WP.seq (WP.mono (sampleArgs_ok h.env hk) fun s1 ⟨h1,e25,e26⟩ => ?_)
  have he1 : Ready σ s1 := h.polyStep hp hk (by rw [h1.mem]; exact Frame.refl _ _)
    h1.rd h1.wr h1.sp (fun r hr => h1.get r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide))
  refine WP.seq (WP.mono (zeroPoly_ok (coeffs_in hp he1.env.wr hk) e26) fun s2 ⟨h2,_,f2⟩ => ?_)
  have he2 : Ready σ s2 := he1.polyStep hp hk f2 h2.rd h2.wr h2.sp (fun r hr => h2.get r (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide))
  have hlp : VG.Proof.MlDsa.AArch64.Sample.RejNtt.LPre (X σ k) (bufP σ k) (polyP σ k) s2 :=
    ⟨he2.out k hk,fun j hj => by
      unfold bufP at'
      rw [Offset.add_add]
      exact in_scr_rd hp he2.env.rd he2.env.wr (by dsimp only [oBuf]; omega),
      coeffs_in hp he2.env.wr hk,buf_poly hp hk hk,by
        rw [h2.get .x25,e25]
        unfold at' bufP
        rw [Offset.add_add]
        exact congrArg (fun d => scr σ+BitVec.ofNat 64 d) (by dsimp only [oBuf]; omega),
      (h2.get .x26).trans e26⟩
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sample.RejNtt.loop_ok (G_length _ _) hlp)
    fun s3 h3 => ?_)
  have he3 := he2.polyStep hp hk h3.frame h3.keep.rd h3.keep.wr h3.keep.sp
    (fun r hr => h3.keep.get r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide))
  have hx4 := h3.x4
  have hst := h3.st
  rw [VG.Proof.MlDsa.AArch64.Sample.RejNtt.Lt_336 (G_length _ _)] at hx4 hst
  refine WP.mono (retZ_ok hx4) fun t ⟨h4,e27⟩ => ?_
  refine ⟨he3.polyStep hp hk (by rw [h4.mem]; exact Frame.refl _ _)
    h4.rd h4.wr h4.sp (fun r hr => h4.get r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)),
    (((h1.keep.trans h2).trans h3.keep).trans h4.keep).mono (by simp [parseRegs,VG.Proof.MlDsa.AArch64.Sample.RejNtt.lRegs]),
    ?_,?_,?_⟩
  · rw [h4.mem,← h1.mem]
    exact f2.trans h3.frame
  · rw [h4.mem]; exact hst
  · rw [e27,h3.keep.get .x27,h2.get .x27,h1.get .x27]
end VG.Proof.MlDsa.AArch64.Sample.Rej4
