import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Sponge

/-! Retain the SHAKE continuation relation discarded by the original sampler
wrapper. This uses the existing squeeze contract without specifying an internal
state representation or assuming a particular cursor value. -/
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
