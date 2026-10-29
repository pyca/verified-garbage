module

public import VerifiedGarbage.Proof.Ed448.AArch64.BaseContract
public import VerifiedGarbage.Proof.Ed448.AArch64.SignCached.Body
public import VerifiedGarbage.Proof.Sha3.AArch64.Variant

import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Calls
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed448.AArch64.ScalarLit
import VerifiedGarbage.Proof.Ed448.AArch64.SignCached.Hash
import VerifiedGarbage.Proof.Ed448.AArch64.SignCached.Correct
import VerifiedGarbage.Proof.Ed448.Signing
import VerifiedGarbage.Proof.Framework.AddrArith
/-!
# Ed448 signing with a cached public key on AArch64: the whole function

`vg_ed448_sign_cached` meets `scLocal` and the ABI (`signCached_ok`), for any
implementation `v` of the Keccak permutation, given that
`vg_ed448_scalar_base` meets its contract (`BaseOk`): the frame
(`Proof.Ed25519.AArch64.Whole.wrap_ok`) runs the body, whose signature is
RFC 8032's for the inputs as on entry.
-/

-- Formerly `VerifiedGarbage/Proof/Ed448/AArch64/SignCached/Run.lean`, which only this module imported.
section

/-!
# Ed448 signing with a cached public key on AArch64: the body's run

The body's steps in turn (`body_ok`), each keeping what later steps read
(`s`, `r` and `R`, apart from what each step writes), and the signature
`R ‖ S` in `out`: `Proof.Ed448.sign_pipeline`.
-/

section

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
end

end

@[expose] public section

namespace VG.Proof.Ed448.AArch64.SignCached

open VG VG.AArch64 VG.Impl.Ed448.AArch64.SignCached
open VG.Proof.Ed25519.AArch64.Whole (entered bodyRd bodyWr)
open VG.Impl.X448.AArch64.Base (combSym)

theorem entry_writes {s : State} (h : scLocal.pre s) : ∀ r ∈ s.wr, (below s.sp 352).Disjoint r := by
  intro r hr
  rw [h.2.1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem entry_below {s : State} (h : scLocal.pre s) : 352 ≤ s.sp.toNat :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem entry_ctx {s p : State} (h : scLocal.pre s) (hp : VG.Proof.Ed25519.AArch64.Whole.Saved (entered s) 6 p) :
    Ctx0 (lay s) s.gpr s.v p.mem (p.withRegions (bodyRd s) (bodyWr s)) := by
  have hc := VG.Proof.Ed25519.AArch64.Whole.saved_ctx hp
  simpa only [bodyRd, bodyWr, h.1, h.2.1, Ctx0, Lay.env, Lay.inputs, Lay.OUT, Lay.SEED, Lay.PK, Lay.CTX,
    Lay.MSG, Lay.SCR, Lay.TB, lay, List.cons_append, List.nil_append] using hc

theorem entry_args {s p : State} (h : scLocal.pre s)
    (hp : VG.Proof.Ed25519.AArch64.Whole.Saved (entered s) 6 p) : Args (lay s) p.mem := by
  refine ⟨fun j hj => ?_, fun i hi => ?_⟩
  · have hw := VG.Proof.Ed25519.AArch64.Whole.saved_words hp hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl <;> exact hw
  · obtain ⟨held, fit, dj⟩ := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hf := VG.Proof.Ed25519.AArch64.Whole.saved_frame hp
    rw [← held i hi]
    refine hf.readW (r := VG.Proof.Ed448.AArch64.Whole.TBL (s.syms combSym))
      (Offset.contains_base _ (by omega) (by omega)) (fun r hr => ?_) (by decide)
    rw [List.mem_singleton.mp hr]
    exact (dj (below s.sp 352) (by simp)).sub_right (VG.Proof.Ed25519.AArch64.Whole.stk_sub s)

theorem entry_syms {s p : State} (hp : VG.Proof.Ed25519.AArch64.Whole.Saved (entered s) 6 p) :
    (p.withRegions (bodyRd s) (bodyWr s)).syms combSym = (lay s).T :=
  congrFun hp.step.syms combSym

theorem entry_x6 {s p : State} (hp : VG.Proof.Ed25519.AArch64.Whole.Saved (entered s) 6 p) :
    (p.withRegions (bodyRd s) (bodyWr s)).gpr .x6 = (lay s).len :=
  hp.step.regs .x6 (by decide)

theorem entry_x7 {s p : State} (hp : VG.Proof.Ed25519.AArch64.Whole.Saved (entered s) 6 p) :
    (p.withRegions (bodyRd s) (bodyWr s)).gpr .x7 = (lay s).scr :=
  hp.step.regs .x7 (by decide)

theorem body_ctx {s p u : State} (h : scLocal.pre s) (hu : Ctx0 (lay s) s.gpr s.v p.mem u) :
    VG.Proof.Ed25519.AArch64.Whole.Ctx (VG.Proof.Ed25519.AArch64.Whole.base s) s.gpr s.v p.mem (bodyRd s)
      s.wr u := by
  simpa only [bodyRd, bodyWr, h.1, h.2.1, Ctx0, Lay.env, Lay.inputs, Lay.OUT, Lay.SEED, Lay.PK, Lay.CTX,
    Lay.MSG, Lay.SCR, Lay.TB, lay, List.cons_append, List.nil_append] using hu

/-- An input's bytes after the frame's writes, as on entry. -/
theorem below_bytes {m m' : Mem} {s : State} (hf : Frame [below s.sp 336] m m') {R : Region}
    (hd : (below s.sp 352).Disjoint R) {n : Nat} (hn : n ≤ R.len) (hl : R.len ≤ 2 ^ 64) :
    Spec.Ed448.bytesAt m' R.base n = Spec.Ed448.bytesAt m R.base n :=
  keep_bytes hf (fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact (hd.sub_left (VG.Proof.Ed25519.AArch64.Whole.stk_sub s)).symm) hn hl

theorem body_depth (v : Proof.Sha3.AArch64.Permutation) : (body v.callee).aarch64Depth ≤ 1 := by
  have ha := v.absorb_depth
  have hp := v.pad_depth
  have hs := v.squeeze_depth
  have hr := VG.Proof.Ed25519.AArch64.Whole.depth_zero_of_noFrames VG.Proof.Ed448.AArch64.Whole.reduce_noFrames
  have hb := VG.Proof.Ed25519.AArch64.Whole.depth_zero_of_noFrames VG.Proof.Ed448.AArch64.Whole.base_noFrames
  have hm := VG.Proof.Ed25519.AArch64.Whole.depth_zero_of_noFrames VG.Proof.Ed448.AArch64.Whole.mulAdd_noFrames
  simp only [body, seedHash, nonceHash, chalHash, Impl.Ed448.AArch64.Whole.zeroSt,
    Impl.Ed448.AArch64.Whole.kabs, Impl.Ed448.AArch64.Whole.kpad, Impl.Ed448.AArch64.Whole.ksqz,
    Impl.Ed448.AArch64.Whole.callS, Code.aarch64Depth, Nat.max_le, ha, hp, hs, hr, hb, hm]
  omega

theorem entry_pk {s p : State} (h : scLocal.pre s)
    (hp : VG.Proof.Ed25519.AArch64.Whole.Saved (entered s) 6 p) :
    Spec.Ed448.bytesAt p.mem (lay s).pk 57 = Spec.Ed448.publicKey (Spec.Ed448.bytesAt p.mem (lay s).seed 57) := by
  have hf := VG.Proof.Ed25519.AArch64.Whole.saved_frame hp
  show Spec.Ed448.bytesAt p.mem (s.gpr .x2) 57 = Spec.Ed448.publicKey (Spec.Ed448.bytesAt p.mem (s.gpr .x1) 57)
  rw [below_bytes hf h.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (R := ⟨s.gpr .x2, 57⟩) (n := 57) (Nat.le_refl _)
      (show 57 ≤ 2 ^ 64 by decide),
    below_bytes hf h.2.2.2.2.2.2.2.2.2.2.2.2.1 (R := ⟨s.gpr .x1, 57⟩) (n := 57) (Nat.le_refl _)
      (show 57 ≤ 2 ^ 64 by decide)]
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The frame's body, from the state the frame enters it in. -/
theorem signCached_ok_body (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.AArch64.BaseOk) {s p : State}
    (h : scLocal.pre s) (hp : VG.Proof.Ed25519.AArch64.Whole.Saved (entered s) 6 p) :
    WP isa (body v.callee) (p.withRegions (bodyRd s) (bodyWr s)) fun u => Ctx0 (lay s) s.gpr s.v p.mem u ∧
      Spec.Ed448.bytesAt u.mem (lay s).out 114 = Spec.Ed448.sign (Spec.Ed448.bytesAt p.mem (lay s).seed 57)
        (Spec.Ed448.bytesAt p.mem (lay s).ctx (lay s).ctxLen.toNat)
        (Spec.Ed448.bytesAt p.mem (lay s).msg (lay s).len.toNat) :=
  body_ok v hb (lay_ok h) (entry_ctx h hp) (entry_args h hp) (entry_x6 hp) (entry_x7 hp) (entry_syms hp)
    (entry_pk h hp)

theorem signCached_ok (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.AArch64.BaseOk) {s : State}
    (h : scLocal.pre s) :
    WP isa (signCachedWith v.callee) s fun u => abiPreserved s u ∧ scLocal.post s u := by
  have hw := VG.Proof.Ed25519.AArch64.Whole.wrap_ok (body_depth v) (entry_below h) (entry_writes h)
    (P := fun m m' _ => Spec.Ed448.bytesAt m' (s.gpr .x0) 114 = Spec.Ed448.sign
      (Spec.Ed448.bytesAt m (s.gpr .x1) 57) (Spec.Ed448.bytesAt m (s.gpr .x3) (s.gpr .x4).toNat)
      (Spec.Ed448.bytesAt m (s.gpr .x5) (s.gpr .x6).toNat))
    (fun p hp => WP.mono (signCached_ok_body v hb h hp) fun u ⟨hu, ho⟩ => ⟨body_ctx h hu, ho⟩)
  refine WP.mono hw fun u ⟨hu, m, hf, hp⟩ => ⟨hu, ?_⟩
  change Spec.Ed448.bytesAt u.mem (s.gpr .x0) 114 = _
  rw [hp, below_bytes hf h.2.2.2.2.2.2.2.2.2.2.2.2.1 (R := ⟨s.gpr .x1, 57⟩) (n := 57) (Nat.le_refl _)
      (show 57 ≤ 2 ^ 64 by decide),
    below_bytes hf h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (R := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩) (n := (s.gpr .x4).toNat)
      (Nat.le_refl _) (Nat.le_of_lt (BitVec.isLt _)),
    below_bytes hf h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (R := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩) (n := (s.gpr .x6).toNat)
      (Nat.le_refl _) (Nat.le_of_lt (BitVec.isLt _))]

end VG.Proof.Ed448.AArch64.SignCached
