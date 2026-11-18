module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rel
import VerifiedGarbage.Proof.MlKem.AArch64.Sample
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttCT
import Std.Tactic.BVDecide.Normalize.Prop
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rel
meta import VerifiedGarbage.Proof.MlKem.AArch64.Sample
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttCT
meta import Std.Tactic.BVDecide.Normalize.Prop
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
meta import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Zero
import VerifiedGarbage.Proof.MlDsa.Sample.Hash
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.MlDsa.Sample.RejNtt
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqPhase
public import VerifiedGarbage.Proof.MlDsa.Sample.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Sponge
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Setup
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Squeeze
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Init
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Env
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Epi
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttLoop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Zero
meta import VerifiedGarbage.Proof.MlDsa.Sample.Hash
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.MlDsa.Sample.RejNtt
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqPhase
meta import VerifiedGarbage.Proof.MlDsa.Sample.Mem
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Sponge
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Setup
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Squeeze
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Init
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Env
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Epi

/-! ### `MlDsa.AArch64.Sample.Rej4.CTBase`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Sample.Rej4.Top`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Sample.Rej4.Parse`, which only this module used -/

section

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Sample/Rej4/Sponge.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (init setup squeezeStepWith)

structure Ready (σ s : State) : Prop where
  env : Env σ s
  out : ∀ k < 4, ∀ j < 1008, s.mem (bufP σ k+BitVec.ofNat 64 j) = F σ k j

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
  Offset.sub_base (aP σ) (by omega_using [hk])

theorem buf_sub (σ : State) {k : Nat} (hk : k < 4) : Region.Sub (⟨bufP σ k,1008⟩ : Region) (scrR σ) :=
  Offset.sub_base (scr σ) (by dsimp only [VG.Impl.MlDsa.AArch64.Sample.Rej4.oBuf]; omega_using [hk])

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
  exact Offset.contains_base _ (by omega_using [hk, hi]) (by omega_using [hk, hi])

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
    exact buf_poly hp hj hk _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) hc)
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
  refine wp_addImm (by omega_using [hk]) fun u h1 e1 => wp_addImm (by omega_using [hk]) fun t h2 e2 => wp_nil ⟨?_,?_,?_⟩
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
    · rw [hn1]; omega_arith
    · rw [hn0]; omega_arith
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
      exact in_scr_rd hp he2.env.rd he2.env.wr (by dsimp only [oBuf]; omega_using [hk, hj]),
      coeffs_in hp he2.env.wr hk,buf_poly hp hk hk,by
        rw [h2.get .x25,e25]
        unfold at' bufP
        rw [Offset.add_add]
        exact congrArg (fun d => scr σ+BitVec.ofNat 64 d) (by dsimp only [oBuf]; omega_using []),
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

end

end


@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (wp_movz wp_nil)
open VG.Proof.MlDsa.Sample (Stored stored_frame stored_polyIs rnFold_length_le)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (sample epi rejNTT4With)

def mask (σ : State) (n : Nat) : BitVec 64 :=
  if (List.range n).all (fun k => (L σ k).length == 256) then 1 else 0

theorem mask_step (σ : State) (n : Nat) : mask σ n &&& result σ n = mask σ (n+1) := by
  have er : result σ n = if (L σ n).length == 256 then (1 : BitVec 64) else 0 := by
    simp only [result,beq_iff_eq]
  rw [er]
  simp only [mask,List.range_succ,List.all_append,List.all_cons,List.all_nil,Bool.and_true]
  cases (List.range n).all (fun k => (L σ k).length == 256) <;>
    cases (L σ n).length == 256 <;> rfl

structure Parsed (σ : State) (n : Nat) (s : State) : Prop where
  ready : Ready σ s
  mask : s.gpr .x27 = mask σ n
  stored : ∀ k < n,Stored s.mem (polyP σ k) (L σ k)

theorem parsed_step {σ s : State} (hp : Pre σ) {n : Nat} (hn : n < 4) (h : Parsed σ n s) :
    WP isa (sample n) s (Parsed σ (n+1)) := by
  refine WP.mono (sample_ok hp h.ready hn) fun t ⟨hr,_,hf,hs,hm⟩ => ⟨hr,?_,fun k hk => ?_⟩
  · rw [hm,h.mask,mask_step]
  · by_cases he : k = n
    · subst k; exact hs
    · exact stored_frame hf (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint (aP σ) (d := 1024*k) (e := 1024*n) (n := 1024) (k := 1024)
          (by omega_using [he]) (by omega_using [hn, hk]) (by omega_using [hn])) (h.stored k (by omega_using [hk, he])) (rnFold_length_le (by simp) _)

def r4K : Contract isa where
  pre := Pre
  post s t := (t.gpr .x0).setWidth 32 = (mask s 4).setWidth 32 ∧
    ∀ k < 4,(L s k).length = 256 → Proof.MlDsa.PolyIs t.mem (polyP s k) (VG.Proof.MlDsa.Sample.toPoly (L s k))
  pub s t := seedP s = seedP t ∧ aP s = aP t ∧ scr s = scr t ∧ s.sp = t.sp ∧
    Spec.Sha3.bytesAt s.mem (seedP s) 136 = Spec.Sha3.bytesAt t.mem (seedP t) 136

theorem end_ok {σ s : State} (hp : Pre σ) (h : Parsed σ 4 s) :
    WP isa (.block epi) s fun t => abiPreserved σ t ∧ r4K.post σ t := by
  refine WP.mono (epi_ok hp h.ready.env) fun t ⟨hab,hm,h0,_,_⟩ => ⟨hab,?_,fun k hk he => ?_⟩
  · rw [h0,h.mask]
  · rw [hm]; exact stored_polyIs (h.stored k hk) he

theorem body_ok {σ s : State} (hp : Pre σ) (h : Ready σ s) :
    WP isa (.seq (.block [.movz .x .x27 1 0])
      (.seq (sample 0) (.seq (sample 1) (.seq (sample 2) (.seq (sample 3) (.block epi)))))) s
      fun t => abiPreserved σ t ∧ r4K.post σ t := by
  refine WP.seq (wp_movz fun t ht et => wp_nil ?_)
  have hr := h.polyStep hp (k := 0) (by decide) (by rw [ht.mem]; exact Frame.refl _ _)
    ht.rd ht.wr ht.sp (fun r hr => ht.get r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide))
  have h0 : Parsed σ 0 t := ⟨hr,by rw [et]; rfl,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  exact WP.seq (WP.mono (parsed_step hp (by decide) h0) fun _ h1 =>
    WP.seq (WP.mono (parsed_step hp (by decide) h1) fun _ h2 =>
      WP.seq (WP.mono (parsed_step hp (by decide) h2) fun _ h3 =>
        WP.seq (WP.mono (parsed_step hp (by decide) h3) fun _ h4 => end_ok hp h4))))

theorem correct (sha3 : Bool) (σ : State) (hp : r4K.pre σ) :
    ∃ tr t,Exec isa (rejNTT4With sha3) σ tr t ∧ abiPreserved σ t ∧ r4K.post σ t := by
  unfold rejNTT4With
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (init_ok hp) fun s ⟨he,h0,h1⟩ => ?_
  refine WP.mono (setup_ok he h0 h1) fun u hu => ?_
  refine WP.seq (WP.mono (squeeze_ok sha3 hp hu) fun t ht => body_ok hp ⟨ht.env,fun k hk j hj =>
    ht.out k hk j (by simpa using hj)⟩)
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Sample (Rel2 relStep relTaintStep relMem relTaint)
open VG.Proof.MlDsa.Sample (polyR coeffAddr G_length coeff_contains)
open VG.Proof.MlKem.AArch64 (ptr_zero)
open VG.Impl.MlDsa.AArch64.Sample (zeroPoly rnLoop retZ)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (oBuf)

/-- The four seeds are slices of the public 136-byte input. -/
theorem B_pub {σ τ : State} (hq : r4K.pub σ τ) {k : Nat} (hk : k < 4) : B σ k = B τ k := by
  unfold B Proof.MlDsa.seed4
  rw [← VG.Proof.MlKem.bytesAt_slice σ.mem (seedP σ) (show 34*k+34 ≤ 136 by omega_using [hk]),
    ← VG.Proof.MlKem.bytesAt_slice τ.mem (seedP τ) (show 34*k+34 ≤ 136 by omega_using [hk]),hq.2.2.2.2]

theorem X_pub {σ τ : State} (hq : r4K.pub σ τ) {k : Nat} (hk : k < 4) : X σ k = X τ k := by
  unfold X
  rw [B_pub hq hk]

structure ArgReady (σ : State) (k : Nat) (s : State) : Prop where
  ready : Ready σ s
  x25 : s.gpr .x25 = at' σ (1008*k)
  x26 : s.gpr .x26 = polyP σ k

structure ZeroReady (σ : State) (k : Nat) (s : State) : Prop extends ArgReady σ k s where
  zero : ∀ i < 256,Proof.MlDsa.coeffAt s.mem (polyP σ k) i = 0

theorem args_ready {σ s : State} {k : Nat} (hk : k < 4) (hp : Pre σ) (h : Ready σ s) :
    WP isa (.block ([.addImm .x .x25 .x19 (1008*k),.addImm .x .x26 .x21 (1024*k)] : List Instr)) s (ArgReady σ k) :=
  WP.mono (sampleArgs_ok h.env hk) fun _ ⟨ht,e25,e26⟩ =>
    ⟨h.polyStep hp hk (by rw [ht.mem]; exact Frame.refl _ _) ht.rd ht.wr ht.sp
      (fun r hr => ht.get r (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide)),e25,e26⟩

theorem zero_ready {σ s : State} {k : Nat} (hk : k < 4) (hp : Pre σ) (h : ArgReady σ k s) :
    WP isa zeroPoly s (ZeroReady σ k) :=
  WP.mono (VG.Proof.MlDsa.AArch64.Sample.zeroPoly_ok (coeffs_in hp h.ready.env.wr hk) h.x26)
    fun _ ⟨ht,hz,hf⟩ => ⟨⟨h.ready.polyStep hp hk hf ht.rd ht.wr ht.sp
      (fun r hr => ht.get r (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide)),
      (ht.get .x25).trans h.x25,(ht.get .x26).trans h.x26⟩,hz⟩

theorem zero_lpre {σ s : State} (hp : Pre σ) {k : Nat} (hk : k < 4) (h : ZeroReady σ k s) :
    VG.Proof.MlDsa.AArch64.Sample.RejNtt.LPre (X σ k) (bufP σ k) (polyP σ k) s :=
  ⟨h.ready.out k hk,fun j hj => by
    unfold bufP at'
    rw [Offset.add_add]
    exact in_scr_rd hp h.ready.env.rd h.ready.env.wr (by dsimp only [oBuf]; omega_using [hk, hj]),
    coeffs_in hp h.ready.env.wr hk,buf_poly hp hk hk,by
      rw [h.x25]
      unfold at' bufP
      rw [Offset.add_add]
      exact congrArg (fun d => scr σ+BitVec.ofNat 64 d) (by dsimp only [oBuf]; omega_using []),h.x26⟩

theorem loop_ready {σ s : State} (hp : Pre σ) {k : Nat} (hk : k < 4) (h : ZeroReady σ k s) :
    WP isa rnLoop s (Ready σ) :=
  WP.mono (VG.Proof.MlDsa.AArch64.Sample.RejNtt.loop_ok (G_length _ _) (zero_lpre hp hk h))
    fun _ ht => h.ready.polyStep hp hk ht.frame ht.keep.rd ht.keep.wr ht.keep.sp (fun r hr => ht.keep.get r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide))
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Sample (Rel2 relMem byte_zero)
open VG.Proof.MlDsa.Sample (polyR coeff_contains G_length)
open VG.Impl.MlDsa.AArch64.Sample (rnLoop)
open VG.Proof.MlKem.AArch64 (ptr_zero)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (oBuf)

def lrd (σ : State) (k : Nat) : List Region := [⟨bufP σ k,1008⟩]
def lwr (σ : State) (k : Nat) : List Region := [polyR (polyP σ k)]

theorem buf_pub {σ τ : State} (hq : r4K.pub σ τ) (k : Nat) : bufP σ k = bufP τ k := by
  unfold bufP at'
  rw [hq.2.2.1]

theorem poly_pub {σ τ : State} (hq : r4K.pub σ τ) (k : Nat) : polyP σ k = polyP τ k := by
  unfold polyP
  rw [hq.2.1]

theorem loop_ct {k : Nat} (hk : k < 4) :
    RelCT isa (Rel2 r4K.pre r4K.pub (fun σ => ZeroReady σ k)) rnLoop fun _ _ => True := by
  refine relMem (fun σ => lrd σ k) (fun σ => lwr σ k) [.x25,.x26]
    (fun σ τ _ _ hq => by simp only [lrd,lwr,buf_pub hq,poly_pub hq]; exact ⟨trivial,trivial⟩)
    (fun σ s hp h => ?_) (fun σ s hp h => ?_)
    (fun σ τ s t _ _ hq hs ht => ?_) (by taint_decide)
  · rw [h.ready.env.rd,h.ready.env.wr,hp.rd,hp.wr]
    refine ⟨Covers.of_sub (fun r hr => ?_),Covers.of_sub (fun r hr => ?_)⟩
    · simp only [lrd,lwr,List.mem_append,List.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact ⟨scrR σ,by simp,VG.Impl.MlDsa.AArch64.Sample.Rej4.oBuf+1008*k,rfl,
          by dsimp only [oBuf,scrR]; omega_using [hk]⟩
      · exact ⟨aR σ,by simp,1024*k,rfl,by dsimp only [aR,polyR]; omega_using [hk]⟩
    · rw [List.mem_singleton.mp hr]
      exact ⟨aR σ,by simp,1024*k,rfl,by dsimp only [aR,polyR]; omega_using [hk]⟩
  · have h := zero_lpre hp hk h
    obtain ⟨tr,u,he,_⟩ := VG.Proof.MlDsa.AArch64.Sample.RejNtt.loop_ok (G_length _ _)
      (s₀ := s.withRegions (lrd σ k) (lwr σ k))
      ⟨h.buf,fun j hj => VG.Proof.MlKem.AArch64.in_rd (VG.Proof.MlKem.AArch64.in_regions
        (List.mem_singleton_self _) (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))),
        fun i hi => VG.Proof.MlKem.AArch64.in_regions (List.mem_singleton_self _) (coeff_contains _ hi),
        h.disj,h.x25,h.x26⟩
    exact ⟨tr,u,he⟩
  · refine ⟨by rw [hs.ready.env.sp,ht.ready.env.sp,hq.2.2.2.1],fun r hr => ?_,fun x hx => ?_⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · rw [hs.x25,ht.x25]
        unfold at'
        rw [hq.2.2.1]
      · rw [hs.x26,ht.x26,poly_pub hq]
    · obtain ⟨r,hr,hc⟩ := hx
      simp only [lrd,lwr,List.mem_append,List.mem_singleton] at hr
      rcases hr with rfl | rfl
      · obtain ⟨j,hj,rfl⟩ := VG.Proof.MlKem.AArch64.Sample.at_off hc
        rw [hs.ready.out k hk j hj,buf_pub hq,ht.ready.out k hk j hj]
        exact congrArg (fun b : List Byte => b.getD j 0) (X_pub hq hk)
      · rw [byte_zero hs.zero hc,byte_zero ht.zero (by rw [← poly_pub hq]; exact hc)]
end VG.Proof.MlDsa.AArch64.Sample.Rej4
