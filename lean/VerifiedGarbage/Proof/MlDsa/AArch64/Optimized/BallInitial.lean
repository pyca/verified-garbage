module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Ball
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallChunk
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Keep
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Load
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Sponge

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallFirst
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallFrame
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
/-! ## From `BallZero.lean` -/

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/BallSponge.lean`, which only this module imported.
section

/-! Retain the SHAKE continuation relation discarded by the original sampler
wrapper. This uses the existing squeeze contract without specifying an internal
state representation or assuming a particular cursor value. -/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Sample
open VG.Proof.MlKem.AArch64 (squeeze_callWith stk)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample (padded)
open VG.Spec.Sha3 (bytesAt stateAt rates shakeSuffix)

structure Resume (rate outlen : Nat) (P : Sp) (σ s : State) : Prop where
  first : J6 rate outlen P σ s
  pos : (s.gpr .x0).toNat ≤ rate
  next : ∀ d, Spec.Sha3.squeezeFrom rate (stateAt s.mem P.scr) (s.gpr .x0).toNat d =
    Spec.Sha3.squeezeFrom rate (padded rate shakeSuffix (P.msg σ)) outlen d

variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp
theorem call3Resume_ok (v : Proof.Sha3.AArch64.Permutation) {rate outlen : Nat} (hr : rate ∈ rates) (ho : 840 + outlen ≤ 2016) {s : State}
    (h : J5 rate outlen P σ s) :
    WP isa (.call ("vg_keccak_squeeze_scratch" ++ v.callee.suffix) (Impl.Sha3.AArch64.Stream.squeezeWith v.callee)) s (Resume rate outlen P σ) := by
  have hsp := h.env.sp
  have cw : Covers [⟨P.scr, 200⟩, ⟨P.at' 840, outlen⟩, ⟨P.at' 200, 640⟩] s.wr :=
    cov_scr hp h.env.wr fun r hr => by
      rcases mem3 hr with rfl | rfl | rfl
      · exact ⟨0, (at_zero).symm, by simp⟩
      · exact ⟨840, rfl, by simp; omega⟩
      · exact ⟨200, rfl, by simp⟩
  refine squeeze_callWith v (st := P.scr) (out := P.at' 840) (sc := P.at' 200) h.x0 h.x1 h.x2 h.x3 h.x4 h.x5 hr
    (Nat.zero_le _)
    (by rw [← at_zero (P := P)]; exact disj_scr (.inl (by omega)) (by omega) (by omega))
    (by rw [← at_zero (P := P)]; exact disj_scr (.inl (by omega)) (by omega) (by omega))
    (disj_scr (.inr (by omega)) (by omega) (by omega))
    (by rw [hsp]; exact hp.sp16) (by rw [stk, hsp]; exact hp.stk_scr.sub_right (sub_scr0 (by omega)))
    (by rw [stk, hsp]; exact stk_scr' hp (by omega)) (by rw [stk, hsp]; exact stk_scr' hp (by omega))
    (cov_rd cw) cw fun s' hk hout hpos hresume => ⟨⟨Env.call hp h.env hk ?_, ?_⟩, hpos, ?_⟩
  · intro r hr
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact .inl ⟨0, 200, by rw [at_zero], by omega⟩
    · exact .inl ⟨840, outlen, rfl, ho⟩
    · exact .inl ⟨200, 640, rfl, by omega⟩
    · exact .inr rfl
  · rw [hout, h.st]
  · intro d
    rw [hresume d, h.st, Nat.zero_add]

/-- The sponge, from `J0`: `outlen` bytes of SHAKE at `scratch + 840`. -/
theorem spongeResume_ok (v : Proof.Sha3.AArch64.Permutation) {rate outlen : Nat} (hr : rate ∈ rates) (ho : 840 + outlen ≤ 2016) {s : State}
    (h : J0 P σ s) : WP isa (spongeWith v.callee rate outlen) s (Resume rate outlen P σ) :=
  WP.seq (WP.mono (blk1_ok hp (rate_lt hr) h) fun _ h1 =>
    WP.seq (WP.mono ((call1With_ok (v := v)) hp hr h1) fun _ h2 => WP.seq (WP.mono (blk2_ok hr h2) fun _ h3 =>
      WP.seq (WP.mono ((call2With_ok (v := v)) hp hr h3) fun _ h4 =>
        WP.seq (WP.mono (blk3_ok hr (by omega) h4) fun _ h5 => (call3Resume_ok (v := v)) hp hr ho h5)))))


end VG.Proof.MlDsa.AArch64.Optimized.Ball
end

end

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_vop wp_strq VMem)
open VG.Impl.MlDsa.AArch64.Optimized.Ball (zeroWide)

def outputR (p : Addr) : Region := ⟨p,1024⟩

theorem zeroWide_ok {s : State} {p : Addr} (hp : s.gpr .x26 = p)
    (hw : ∀ i < 64, InRegions s.wr (wordAddr p i) 16) :
    WP isa zeroWide s fun t => RegKeep [] s t ∧
      Frame [outputR p] s.mem t.mem ∧ ∀ i < 64, t.mem.read (wordAddr p i) 16 = 0 := by
  unfold zeroWide
  rw [List.cons_append,WP.block_cons_iff]
  refine ⟨s.setV .v0 0,rfl,?_⟩
  have hz := VG.Proof.MlKem.AArch64.vupd_setV s .v0 0
  rw [List.nil_append,List.map_eq_flatMap]
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun k t => RegKeep [] s t ∧ t.v .v0 = 0 ∧ Frame [outputR p] s.mem t.mem ∧
      ∀ i < k, t.mem.read (wordAddr p i) 16 = 0)
    (fun k t hk ⟨ht,hv,hf,hvals⟩ => ?_) 64 (Nat.le_refl _) (s.setV .v0 0)
    ⟨RegKeep.vupd hz,hz.v,by rw [hz.mem]; exact Frame.refl _ _,
      fun _ h => False.elim (Nat.not_lt_zero _ h)⟩)
    fun t ⟨ht,_,hf,hvals⟩ => ⟨ht,hf,hvals⟩
  refine wp_strq (a := wordAddr p k) (by omega)
    (by rw [ht.gpr .x26 (by simp),hp]; rfl)
    (by rw [ht.wr]; exact hw k hk) fun u hu => WP.block_nil_iff.mpr ⟨?_,?_,?_,?_⟩
  · exact (ht.trans (RegKeep.vmem hu)).mono (by simp)
  · rw [hu.v]; exact hv
  · rw [hu.mem]
    exact hf.write (List.mem_singleton_self _) _ (Offset.contains_base p (by omega) (by omega))
  · intro i hi
    rw [hu.mem,hv]
    by_cases he : i = k
    · subst i; rw [read_write16]
    · have hsep : Mem.Sep (wordAddr p i) 16 (wordAddr p k) 16 :=
        Offset.sep p (d := 16*i) (e := 16*k) (n := 16) (k := 16) (by omega) (by omega) (by omega)
      rw [Mem.read_write_sep hsep (by decide)]
      exact hvals i (by omega)

/-- The SIMD clear preserves the complete calling-convention frame. -/
theorem zeroWide_coeffs {s : State} {p : Addr} (hp : s.gpr .x26 = p)
    (hw : ∀ i<64, InRegions s.wr (wordAddr p i) 16) :
    WP isa zeroWide s fun t => VG.Proof.MlKem.AArch64.Keep [] s t ∧
      Frame [VG.Proof.MlDsa.Sample.polyR p] s.mem t.mem ∧
      ∀ i<256, VG.Proof.MlDsa.coeffAt t.mem p i = 0 := by
  refine WP.mono (WP.preservedV (zeroWide_ok hp hw) (hc := by lit_decide))
    fun t ⟨⟨hk,hf,hz⟩,hv⟩ => ?_
  refine ⟨⟨hk.gpr,hk.rd,hk.wr,hk.sp,hv⟩,hf,fun i hi => ?_⟩
  have hword := hz (i/4) (by omega)
  have hread : t.mem.read (p+BitVec.ofNat 64 (4*i)) 4 = 0 := by
    apply Mem.read_eq_of_bytes
    intro j hj
    have hbyte := Mem.extractLsb'_read t.mem (wordAddr p (i/4))
      (n := 16) (j := 4*(i%4)+j) (by omega)
    rw [hword] at hbyte
    have ha : wordAddr p (i/4)+BitVec.ofNat 64 (4*(i%4)+j) =
        p+BitVec.ofNat 64 (4*i)+BitVec.ofNat 64 j := by
      simp only [wordAddr,BitVec.add_assoc,← BitVec.ofNat_add]
      congr 2
      have := Nat.mod_add_div i 4
      omega
    rw [ha] at hbyte
    simpa [BitVec.extractLsb'] using hbyte.symm
  simp only [VG.Proof.MlDsa.coeffAt,Mem.readW,hread]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Ball

end

/-! ## From `BallInitial.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.Sha3 (bytesAt stateAt)
open VG.Proof.MlDsa.AArch64.Sample.Ball (spOf W St)

abbrev firstBytes (σ : State) := Spec.MlDsa.H ((spOf σ).msg σ) 136
abbrev tailBytes (σ : State) := Spec.Sha3.squeezeFrom 136
  (padded 136 Spec.Sha3.shakeSuffix ((spOf σ).msg σ)) 136 136

structure Initial (σ s : State) : Prop where
  env : Env (spOf σ) σ s
  parser : Parser (spOf σ).a (ballFold (tauOf σ) (firstBytes σ)).1
    (ballFold (tauOf σ) (firstBytes σ)).2
    (W (firstBytes σ) >>> ((ballFold (tauOf σ) (firstBytes σ)).2-(256-tauOf σ))) s
  pos : (s.gpr .x0).toNat≤136
  next : Spec.Sha3.squeezeFrom 136 (stateAt s.mem (spOf σ).scr) (s.gpr .x0).toNat 136=tailBytes σ

 theorem initial_full_ok {σ s : State} (hp : sbK.pre σ) (h : Resume 136 136 (spOf σ) σ s) :
    WP isa (.seq Impl.MlDsa.AArch64.Optimized.Ball.zeroWide Impl.MlDsa.AArch64.Optimized.Ball.first)
      s (fun u => Initial σ u ∧ u.gpr .x0=s.gpr .x0) := by
  have ps := Sample.Ball.spOk hp
  have hl : (firstBytes σ).length=136 := H_length _ _
  refine WP.seq (WP.mono (zeroWide_coeffs h.first.env.x26 (fun i hi => ?_)) fun t ⟨kt,ft,hz⟩ => ?_)
  · rw [h.first.env.wr,ps.wr]
    exact in_regions (List.mem_cons_self ..) (Offset.contains_base _ (by omega) (by omega))
  have et := h.first.env.keepA ps kt ft
  have ot : bytesAt t.mem ((spOf σ).at' 840) 136=firstBytes σ := by
    rw [MlKem.bytesAt_frame ft (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (a_scr' ps (by decide)).symm) (by decide),h.first.out]
    exact (H_eq _ _).symm
  have st : stateAt t.mem (spOf σ).scr=stateAt s.mem (spOf σ).scr :=
    state_frame ft (fun r hr => by rw [List.mem_singleton.mp hr]; exact ps.a_scr.symm.sub_left (sub_scr0 (by decide)))
  refine WP.mono (first_ok (τ := tauOf σ) (b := (spOf σ).at' 840) hl (by rw [et.x25]) et.x26
    (by rw [et.x27]; simp [tauOf]; omega) (by have := (Sample.Ball.params hp).2.2; omega)
    (inScrRd ps et.rd et.wr (by decide))
    (fun j hj => by rw [at_add]; exact inScrRd ps et.rd et.wr (by omega))
    (fun j hj => by rw [← ot,MlKem.bytesAt_getD _ _ hj])
    (fun j hj => inA ps et.wr hj) (a_scr' ps (by decide)).symm hz) fun u hu => ?_
  have eqfold : St (firstBytes σ) (tauOf σ) 128=ballFold (tauOf σ) (firstBytes σ) := by
    simp only [St,ballFold]
    rw [List.take_of_length_le (by rw [List.length_drop,hl])]
  refine ⟨⟨et.keepA ps hu.keep hu.frame,?_,?_,?_⟩,by rw [hu.keep.get .x0,kt.get .x0]⟩
  · simpa only [eqfold] using hu.parser
  · rw [hu.keep.get .x0,kt.get .x0]; exact h.pos
  · have su : stateAt u.mem (spOf σ).scr=stateAt t.mem (spOf σ).scr :=
      state_frame hu.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact ps.a_scr.symm.sub_left (sub_scr0 (by decide)))
    rw [su,st,hu.keep.get .x0,kt.get .x0]
    exact h.next 136
theorem initial_ok {σ s : State} (hp : sbK.pre σ) (h : Resume 136 136 (spOf σ) σ s) :
    WP isa (.seq Impl.MlDsa.AArch64.Optimized.Ball.zeroWide Impl.MlDsa.AArch64.Optimized.Ball.first)
      s (Initial σ) := WP.mono (initial_full_ok hp h) fun _ hh => hh.1
end VG.Proof.MlDsa.AArch64.Optimized.Ball

end
