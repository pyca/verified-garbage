import VerifiedGarbage.Proof.Ed448.AArch64.SignCached.Correct

/-!
# Ed448 signing with a cached public key on AArch64: the body's run

The body's steps in turn (`body_ok`), each keeping what later steps read
(`s`, `r` and `R`, apart from what each step writes), and the signature
`R ‖ S` in `out`: `Proof.Ed448.sign_pipeline`.
-/

namespace VG.Proof.Ed448.AArch64.SignCached

open VG VG.AArch64 VG.Impl.Ed448.AArch64.SignCached
open VG.Proof.Ed448.AArch64.Whole (WCtx ST KS st_within ks_within sha3_bytesAt_length)
open VG.Proof.Ed25519.AArch64.Whole (Within FR CK ck_frame)

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

/-- 57 bytes apart from what a step writes are kept. -/
theorem keep57 {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 57⟩ r) : Spec.Ed448.bytesAt m' p 57 = Spec.Ed448.bytesAt m p 57 :=
  keep_bytes (R := ⟨p, 57⟩) hf hd (Nat.le_refl _) (show 57 ≤ 2 ^ 64 by decide)

/-- `s`, `r` and `R` miss what the steps after they are written write. -/
structure Apart57 (L : Lay) (p : Addr) : Prop where
  scr : Region.Disjoint ⟨p, 57⟩ L.SCR
  ck : Region.Disjoint ⟨p, 57⟩ (CK L.E)
  h : Region.Disjoint ⟨p, 57⟩ ⟨L.E + BitVec.ofNat 64 fH, 114⟩
  k : Region.Disjoint ⟨p, 57⟩ ⟨L.E + BitVec.ofNat 64 fH, 57⟩

theorem Apart57.hw {p : Addr} (h : Apart57 L p) : ∀ r ∈ HW L, Region.Disjoint ⟨p, 57⟩ r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  exacts [h.scr, h.ck, h.h]

theorem Apart57.call {p q : Addr} (h : Apart57 L p) (hq : Region.Disjoint ⟨p, 57⟩ ⟨q, 57⟩) :
    ∀ r ∈ [⟨q, 57⟩, L.SCR, CK L.E], Region.Disjoint ⟨p, 57⟩ r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  exacts [hq, h.scr, h.ck]

theorem apart_out (hL : L.Ok) : Apart57 L L.out where
  scr := hL.oc.sub_left (outR_within L).sub
  ck := (hL.co.sub_right (outR_within L).sub).symm
  h := (fr_out hL (by decide)).symm.sub_left (outR_within L).sub
  k := (fr_out hL (by decide)).symm.sub_left (outR_within L).sub

theorem apart_outS (hL : L.Ok) : Apart57 L (L.out + BitVec.ofNat 64 57) where
  scr := hL.oc.sub_left (outS_within L).sub
  ck := (hL.co.sub_right (outS_within L).sub).symm
  h := (fr_out hL (by decide)).symm.sub_left (outS_within L).sub
  k := (fr_out hL (by decide)).symm.sub_left (outS_within L).sub

theorem apart_s (hL : L.Ok) : Apart57 L (L.E + BitVec.ofNat 64 fS) where
  scr := fr_scr hL (by decide)
  ck := (ck_frame (by decide)).symm
  h := Offset.disjoint _ (by decide) (by decide) (by decide)
  k := Offset.disjoint _ (by decide) (by decide) (by decide)

/-- `H(dom4(0, C) ‖ X ‖ M)` as the specification writes it. -/
theorem hash_eq (L : Lay) (m : Mem) (X : List Byte) :
    Spec.Sha3.shake256 (domIn L m X) 114 =
      Spec.Ed448.hash (Spec.Ed448.bytesAt m L.ctx L.ctxLen.toNat) (X ++ Spec.Ed448.bytesAt m L.msg L.len.toNat) := by
  rw [dom_eq]
  rfl

theorem body_ok (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.AArch64.BaseOk) (hL : L.Ok)
    (hc : Ctx0 L g vec m₀ t) (ha : Args L m₀) (h6 : t.gpr .x6 = L.len) (h7 : t.gpr .x7 = L.scr)
    (hsy : t.syms Impl.X448.AArch64.Base.combSym = L.T)
    (hpk : Spec.Ed448.bytesAt m₀ L.pk 57 = Spec.Ed448.publicKey (Spec.Ed448.bytesAt m₀ L.seed 57)) :
    WP isa (body v.callee) t fun u => Ctx0 L g vec m₀ u ∧
      Spec.Ed448.bytesAt u.mem L.out 114 = Spec.Ed448.sign (Spec.Ed448.bytesAt m₀ L.seed 57)
        (Spec.Ed448.bytesAt m₀ L.ctx L.ctxLen.toNat) (Spec.Ed448.bytesAt m₀ L.msg L.len.toNat) := by
  have aR := apart_out hL
  have ar := apart_outS hL
  have as := apart_s hL
  refine WP.seq (WP.mono (entry_ok hL hc ha h6 h7 hsy) fun t₁ hc₁ => ?_)
  refine WP.seq (WP.mono (seedHash_ok v hL hc₁ ha) fun t₂ ⟨hc₂, hH₂⟩ => ?_)
  refine WP.seq (WP.mono (prune_step hL hc₂ hH₂) fun t₃ ⟨hc₃, hf₃, hs₃⟩ => ?_)
  have hp₃ : Spec.Sha3.bytesAt t₃.mem (L.E + BitVec.ofNat 64 (fH + 57)) 57 =
      (Spec.Sha3.shake256 (Spec.Sha3.bytesAt m₀ L.seed 57) 114).drop 57 := by
    rw [keep_bytes (R := ⟨L.E + BitVec.ofNat 64 (fH + 57), 57⟩) hf₃ (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by decide) (by decide) (by decide))
      (Nat.le_refl _) (show 57 ≤ 2 ^ 64 by decide), ← hH₂, bytes_split, Offset.add_add,
      List.drop_left' (sha3_bytesAt_length _ _ _)]
  -- `r`.
  refine WP.seq (WP.mono (domHash_ok v hL hc₃ ha (x := .val (.frame (fH + 57)))
    (show fH + 57 < 4096 by decide) rfl (xp := L.E + BitVec.ofNat 64 (fH + 57)) (fun _ => rfl)
    (.inl ⟨fH + 57, rfl, show fH + 57 + 57 ≤ 256 by decide⟩) (fr_st hL (by decide)) (fr_ks hL (by decide))
    (ck_frame (by decide))) fun t₄ ⟨hc₄, hf₄, hH₄⟩ => ?_)
  rw [hp₃] at hH₄
  have hs₄ := keep57 hf₄ as.hw
  refine WP.seq (WP.mono (reduceR_step hL hc₄ ha) fun t₅ ⟨hc₅, hf₅, hr₅⟩ => ?_)
  have hs₅ := keep57 hf₅ (as.call ((fr_out hL (by decide)).sub_right (outS_within L).sub))
  -- `R`.
  refine WP.seq (WP.mono (base_step hb hL hc₅ ha) fun t₆ ⟨hc₆, hf₆, hR₆⟩ => ?_)
  have hs₆ := keep57 hf₆ (as.call ((fr_out hL (by decide)).sub_right (outR_within L).sub))
  have hr₆ := keep57 hf₆ (ar.call (out_sep hL).symm)
  -- `k`.
  refine WP.seq (WP.mono (chalHash_ok v hL hc₆ ha) fun t₇ ⟨hc₇, hf₇, hH₇⟩ => ?_)
  have hs₇ := keep57 hf₇ as.hw
  have hr₇ := keep57 hf₇ ar.hw
  have hR₇ := keep57 hf₇ aR.hw
  refine WP.seq (WP.mono (reduceK_step hL hc₇) fun t₈ ⟨hc₈, hf₈, hk₈⟩ => ?_)
  have hs₈ := keep57 hf₈ (as.call as.k)
  have hr₈ := keep57 hf₈ (ar.call ar.k)
  have hR₈ := keep57 hf₈ (aR.call aR.k)
  -- `S`.
  refine WP.seq (WP.mono (mulAdd_step hL hc₈ ha) fun t₉ ⟨hc₉, hf₉, hS₉⟩ => ?_)
  have hR₉ := keep57 hf₉ (aR.call (out_sep hL))
  refine WP.mono (wipe_step hL hc₉) fun u ⟨hu, hf⟩ => ⟨hu.1, ?_⟩
  have hRu := keep57 hf fun r hr => by rw [List.mem_singleton.mp hr]; exact (fr_out hL (by decide)).symm.sub_left (outR_within L).sub
  have hSu := keep57 hf fun r hr => by rw [List.mem_singleton.mp hr]; exact (fr_out hL (by decide)).symm.sub_left (outS_within L).sub
  rw [ed448_bytesAt, bytes_split, ← ed448_bytesAt, ← ed448_bytesAt, hRu, hSu, hS₉, hR₉, hR₈, hR₇, hR₆,
    hr₈, hr₇, hr₆, hk₈, hs₈, hs₇, hs₆, hs₅, hs₄, hr₅, ed448_bytesAt _ _ 114, hH₄, ed448_bytesAt _ _ 114, hH₇,
    hash_eq, hash_eq, ← ed448_bytesAt, ← ed448_bytesAt _ L.out, hR₆, hr₅, ed448_bytesAt _ _ 114, hH₄, hash_eq]
  exact Proof.Ed448.sign_pipeline _ _ _ _ _ hpk hs₃

end VG.Proof.Ed448.AArch64.SignCached
