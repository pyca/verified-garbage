import VerifiedGarbage.Proof.Ed448.Arm.SignCached.Calls
import VerifiedGarbage.Proof.Ed448.Signing

/-!
# Ed448 signing with a cached public key on ARMv7: the body

`body_ok`: the steps (`Hash.lean`, `Calls.lean`) in order, each keeping
what the later ones read (the header of `dom4`, `s`, the prefix, `r` and
`R`), leave `Spec.Ed448.sign` in `out` (`Proof.Ed448.sign_pipeline`), given
the public key of the private key.
-/

namespace VG.Proof.Ed448.Arm.SignCached

open VG VG.Arm VG.Impl.Ed448.Arm.SignCached VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.Ctx Whole.FR Whole.Within)
open VG.Proof.Ed448.Arm.Shake (Kit Args argVal kWr kArgs hdrBytes frame_bytes)
open VG.Proof.Ed448 (BaseLadderOk)

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

/-- The two halves of a 114-byte region. -/
theorem bytes_halves (m : Mem) (p : Addr) :
    Spec.Ed448.bytesAt m p 114 = Spec.Ed448.bytesAt m p 57 ++ Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  simp only [Proof.Ed448.bytesAt_eq]
  exact Proof.X25519.bytesAt_add m p 57 57

theorem drop57 (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 114).drop 57 = Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  rw [bytes_halves]
  exact List.drop_left' (by simp [Spec.Ed448.bytesAt])

theorem disj1 {D r₀ : Region} (h : D.Disjoint r₀) : ∀ r ∈ [r₀], D.Disjoint r := fun r hr => by
  rw [List.mem_singleton.mp hr]; exact h

theorem disj2 {D r₀ r₁ : Region} (h₀ : D.Disjoint r₀) (h₁ : D.Disjoint r₁) : ∀ r ∈ [r₀, r₁], D.Disjoint r :=
  fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact h₀
    · rw [List.mem_singleton.mp hr]; exact h₁

/-- Regions of the frame and of `out` that a step keeps. -/
theorem keep {D : Region} (h : Away L D) {ex : List Region} (hx : ∀ r ∈ ex, D.Disjoint r)
    {m m' : Mem} (hf : Frame (W L ex) m m') (hn : D.len ≤ 2 ^ 64) :
    Spec.Ed448.bytesAt m' D.base D.len = Spec.Ed448.bytesAt m D.base D.len := h.bytes hx hf hn

theorem body_ok (hl : BaseLadderOk) (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀)
    (hpk : Spec.Ed448.bytesAt m₀ (State.addr L.pk) 57 =
      Spec.Ed448.publicKey (Spec.Ed448.bytesAt m₀ (State.addr L.seed) 57)) :
    WP isa body t fun u => Ctx L g m₀ u ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.out) 114 =
        Spec.Ed448.sign (Spec.Ed448.bytesAt m₀ (State.addr L.seed) 57)
          (Spec.Ed448.bytesAt m₀ (State.addr L.ctx) L.ctxLen.toNat)
          (Spec.Ed448.bytesAt m₀ (State.addr L.msg) L.len.toNat) := by
  have hk := hL.kit
  have n10 : (10 : Nat) ≤ 2 ^ 64 := by decide
  have n57 : (57 : Nat) ≤ 2 ^ 64 := by decide
  -- Regions kept, and the disjointness of each from what the steps write.
  have dHS : (L.fr HDR 10).Disjoint (L.fr S 114) := fr_fr (by decide) (by decide) (by decide)
  have dHS' : (L.fr HDR 10).Disjoint (L.fr S 57) := fr_fr (by decide) (by decide) (by decide)
  have dHH : (L.fr HDR 10).Disjoint (L.fr HASH 114) := fr_fr (by decide) (by decide) (by decide)
  have dHr : (L.fr HDR 10).Disjoint (L.ob 57 57) := (hL.ob_stk (by decide) (by decide)).symm
  have dHc : (L.fr HDR 10).Disjoint L.SCR := hk.stack_scr (by decide)
  have dHR : (L.fr HDR 10).Disjoint L.R0 :=
    (hL.ko.sub_left (Offset.sub_base _ (by decide : 236 + 10 ≤ 280))).sub_right (r0_sub L)
  have dKS : (L.fr K 57).Disjoint (L.fr S 57) := fr_fr (by decide) (by decide) (by decide)
  have dSH : (L.fr S 57).Disjoint (L.fr HASH 114) := fr_fr (by decide) (by decide) (by decide)
  have dSr : (L.fr S 57).Disjoint (L.ob 57 57) := (hL.ob_stk (by decide) (by decide)).symm
  have dSc : (L.fr S 57).Disjoint L.SCR := hk.stack_scr (by decide)
  have dSR : (L.fr S 57).Disjoint L.R0 :=
    (hL.ko.sub_left (Offset.sub_base _ (by decide : 122 + 57 ≤ 280))).sub_right (r0_sub L)
  have dSK : (L.fr S 57).Disjoint (L.fr K 57) := dKS.symm
  have drR : (L.ob 57 57).Disjoint L.R0 := Offset.disjoint_base _ (by decide) (by decide)
  have drc : (L.ob 57 57).Disjoint L.SCR := hL.ob_scr (by decide)
  have drH : (L.ob 57 57).Disjoint (L.fr HASH 114) := hL.ob_stk (by decide) (by decide)
  have drK : (L.ob 57 57).Disjoint (L.fr K 57) := hL.ob_stk (by decide) (by decide)
  have dRH : L.R0.Disjoint (L.fr HASH 114) :=
    ((hL.ko.sub_left (Offset.sub_base _ (by decide : 8 + 114 ≤ 280))).sub_right (r0_sub L)).symm
  have dRK : L.R0.Disjoint (L.fr K 57) :=
    ((hL.ko.sub_left (Offset.sub_base _ (by decide : 179 + 57 ≤ 280))).sub_right (r0_sub L)).symm
  have dRc : L.R0.Disjoint L.SCR := hL.oc.sub_left (r0_sub L)
  have dRr : L.R0.Disjoint (L.ob 57 57) := drR.symm
  have aH := hL.away_hdr
  have aS := hL.away_s
  have ar := hL.away_ob (o := 57) (l := 57) (by decide)
  have aR := hL.away_r0
  -- The header.
  refine WP.seq (WP.mono (hdr_step hc hL ha) fun t1 ⟨hc1, hh1⟩ => ?_)
  -- `SHAKE256(seed)`, pruned.
  refine WP.seq (WP.mono (seed_step hc1 hL ha) fun t2 ⟨hc2, hf2, hb2⟩ => ?_)
  have hh2 := keep aH (disj1 dHS) hf2 n10
  simp only at hh2
  refine WP.seq (WP.mono (prune_step hc2 hL) fun t3 ⟨hc3, hf3, hs3⟩ => ?_)
  have hh3 := frame_bytes hf3 (D := L.fr HDR 10) (disj1 dHS') n10
  have hp3 := frame_bytes hf3 (D := L.fr K 57) (disj1 dKS) n57
  simp only at hh3 hp3
  have hpfx : Spec.Ed448.bytesAt t3.mem (State.addr L.E + BitVec.ofNat 64 K) 57 =
      (Spec.Sha3.shake256 (Spec.Ed448.bytesAt m₀ (State.addr L.seed) 57) 114).drop 57 := by
    rw [hp3, ← hb2, drop57, Offset.add_add]; rfl
  rw [hb2] at hs3
  -- The nonce's hash, and `r`.
  refine WP.seq (WP.mono (nonce_step hc3 hL ha (by rw [hh3, hh2, hh1])) fun t4 ⟨hc4, hf4, hb4⟩ => ?_)
  have hh4 := keep aH (disj1 dHH) hf4 n10
  have hs4 := keep aS (disj1 dSH) hf4 n57
  simp only at hh4 hs4
  rw [hpfx] at hb4
  refine WP.seq (WP.mono (reduceR_step hc4 hL ha) fun t5 ⟨hc5, hf5, hr5⟩ => ?_)
  have hh5 := keep aH (disj2 dHr dHc) hf5 n10
  have hs5 := keep aS (disj2 dSr dSc) hf5 n57
  simp only at hh5 hs5
  rw [hb4] at hr5
  -- `R`.
  refine WP.seq (WP.mono (base_step hl hc5 hL ha) fun t6 ⟨hc6, hf6, hR6⟩ => ?_)
  have hh6 := keep aH (disj2 dHR dHc) hf6 n10
  have hs6 := keep aS (disj2 dSR dSc) hf6 n57
  have hr6 := keep ar (disj2 drR drc) hf6 n57
  simp only at hh6 hs6 hr6
  rw [hr5] at hR6 hr6
  -- The challenge's hash, and `k`.
  refine WP.seq (WP.mono (chal_step hc6 hL ha (by rw [hh6, hh5, hh4, hh3, hh2, hh1]))
    fun t7 ⟨hc7, hf7, hb7⟩ => ?_)
  have hs7 := keep aS (disj1 dSH) hf7 n57
  have hr7 := keep ar (disj1 drH) hf7 n57
  have hR7 := keep aR (disj1 dRH) hf7 n57
  simp only at hs7 hr7 hR7
  rw [hR6] at hb7
  refine WP.seq (WP.mono (reduceK_step hc7 hL ha) fun t8 ⟨hc8, hf8, hk8⟩ => ?_)
  have hs8 := keep aS (disj2 dSK dSc) hf8 n57
  have hr8 := keep ar (disj2 drK drc) hf8 n57
  have hR8 := keep aR (disj2 dRK dRc) hf8 n57
  simp only at hs8 hr8 hR8
  rw [hb7] at hk8
  -- `S`.
  refine WP.seq (WP.mono (mulAdd_step hc8 hL ha) fun t9 ⟨hc9, hf9, hS9⟩ => ?_)
  have hR9 := keep aR (disj2 dRr dRc) hf9 n57
  simp only at hR9
  -- The locals, cleared.
  refine WP.mono (wipe_step hc9 hL) fun u ⟨hu, hw⟩ => ⟨hu, ?_⟩
  rw [hw, bytes_halves, hR9, hR8, hR7, hR6, hS9, hr8, hr7, hr6, hk8, hs8, hs7, hs6, hs5, hs4]
  exact Proof.Ed448.sign_pipeline _ _ _ _ _ hpk hs3

end VG.Proof.Ed448.Arm.SignCached
