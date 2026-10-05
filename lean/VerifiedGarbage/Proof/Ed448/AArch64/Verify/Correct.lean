import VerifiedGarbage.Proof.Ed448.AArch64.Verify.Hash

/-!
# Ed448 verification on AArch64: the frame's body

After the hash: `k`, the hash reduced modulo `L` (`reduce_step`), and the
verification equation's result in `x0` (`equation_step`), for the inputs as
on entry (`body_ok`).
-/

namespace VG.Proof.Ed448.AArch64.Verify

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Verify
open VG.Impl.Ed448.AArch64.Whole (Src setupS callS)
open VG.Proof.Ed448.AArch64.Whole (Env WCtx srcValue srcValid ScrOk wsetup_ok reduce_call equation_call
  Readable Writable Apart)
open VG.Proof.Ed25519.AArch64.Whole (Within FR CK)

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem scr_writable (L : Lay) : Writable L.env L.SCR := .inr ⟨L.SCR, by simp [Lay.env], within_self _ _⟩

theorem fr_scr (hL : L.Ok) {d n : Nat} (h : d + n ≤ 336) :
    Region.Disjoint ⟨L.E + BitVec.ofNat 64 d, n⟩ L.SCR :=
  hL.kc.sub_left (Offset.sub_base _ h)

theorem k_apart (L : Lay) : Apart L.env ⟨L.E + BitVec.ofNat 64 fK, 57⟩ :=
  ⟨⟨fK, rfl, show fK + 57 ≤ 256 by decide⟩, fun p hp => by
    simp only [Lay.env, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;>
      exact Offset.disjoint _ (by simp [fScr, fHdr, fK]) (by simp [fScr, fHdr]) (by simp [fK])⟩

theorem reduce_step (hL : L.Ok) (hc : WCtx L.env g vec m₀ t) :
    WP isa (callS reduceArgs "vg_ed448_scalar_reduce" Impl.Ed448.AArch64.scalarReduce) t fun u =>
      WCtx L.env g vec m₀ u ∧ Spec.Ed448.bytesAt u.mem (L.E + BitVec.ofNat 64 fK) 57 =
        Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt t.mem (L.E + BitVec.ofNat 64 fH) 114) := by
  have hV := env_ok hL
  refine WP.seq (WP.mono (wsetup_ok hV hc (args := reduceArgs) (by decide)
    (by simp [reduceArgs, srcValid, VG.Proof.Ed25519.AArch64.Whole.valid, fK, fH, fScr]) rfl
    (by decide)) fun u ⟨hu, hm, hv⟩ => ?_)
  have h0 : u.gpr .x0 = L.E + BitVec.ofNat 64 fK := hv (.x0, .val (.frame fK)) (List.mem_of_getElem? (i := 0) rfl)
  have h1 : u.gpr .x1 = L.E + BitVec.ofNat 64 fH := hv (.x1, .val (.frame fH)) (List.mem_of_getElem? (i := 1) rfl)
  have h2 : u.gpr .x2 = L.scr := by
    rw [hv (.x2, .loc fScr 0) (List.mem_of_getElem? (i := 2) rfl), (scrOk hL).loc hc, BitVec.add_zero]
  refine WP.mono (reduce_call hV hu h0 h1 h2 (fr_scr hL (by decide)) (.inl ⟨fH, rfl, show fH + 114 ≤ 256 by decide⟩)
    (.inl (k_apart L)) (scr_writable L)) fun w ⟨hw, _, hk⟩ => ⟨hw, by rw [hk, hm]⟩

theorem equation_step (hR : Proof.Ed448.RecoverOk) (hE : Proof.Ed448.VerifyEqOk) (hL : L.Ok)
    (hc : WCtx L.env g vec m₀ t) (ha : Args L m₀) :
    WP isa (callS equationArgs "vg_ed448_verify_equation" Impl.Ed448.AArch64.verifyEquation) t fun u =>
      WCtx L.env g vec m₀ u ∧ u.gpr .x0 = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt m₀ L.pk 57)
        (Spec.Ed448.bytesAt m₀ L.sig 114) (Spec.Ed448.bytesAt t.mem (L.E + BitVec.ofNat 64 fK) 57) then 1 else 0 := by
  have hV := env_ok hL
  refine WP.seq (WP.mono (wsetup_ok hV hc (args := equationArgs) (by decide)
    (by simp [equationArgs, srcValid, VG.Proof.Ed25519.AArch64.Whole.valid, aPk, aSig, fK, fScr]) rfl
    (by decide)) fun u ⟨hu, hm, hv⟩ => ?_)
  have h0 : u.gpr .x0 = L.pk := (hv (.x0, aPk) (List.mem_of_getElem? (i := 0) rfl)).trans
    (arg_src hL hc.1 ha (j := 0) (by decide) _)
  have h1 : u.gpr .x1 = L.sig := (hv (.x1, aSig) (List.mem_of_getElem? (i := 1) rfl)).trans
    (arg_src hL hc.1 ha (j := 5) (by decide) _)
  have h2 : u.gpr .x2 = L.E + BitVec.ofNat 64 fK := hv (.x2, .val (.frame fK)) (List.mem_of_getElem? (i := 2) rfl)
  have h3 : u.gpr .x3 = L.scr := by
    rw [hv (.x3, .loc fScr 0) (List.mem_of_getElem? (i := 3) rfl), (scrOk hL).loc hc, BitVec.add_zero]
  refine WP.mono (equation_call hR hE hV hu h0 h1 h2 h3 hL.pc hL.sc (fr_scr hL (by decide)) hL.nc
    (in_readable L.PK (by simp [Lay.inputs])) (in_readable L.SIG (by simp [Lay.inputs]))
    (.inl ⟨fK, rfl, show fK + 57 ≤ 256 by decide⟩) (scr_writable L)) fun w ⟨hw, _, hx⟩ => ⟨hw, ?_⟩
  have eP : Spec.Ed448.bytesAt u.mem L.pk 57 = Spec.Ed448.bytesAt m₀ L.pk 57 :=
    in_bytes hL hu.1 (R := L.PK) (by simp [Lay.inputs]) (Nat.le_refl _) (show 57 ≤ 2 ^ 64 by decide)
  have eS : Spec.Ed448.bytesAt u.mem L.sig 114 = Spec.Ed448.bytesAt m₀ L.sig 114 :=
    in_bytes hL hu.1 (R := L.SIG) (by simp [Lay.inputs]) (Nat.le_refl _) (show 114 ≤ 2 ^ 64 by decide)
  rw [hx, eP, eS, hm]

/-- The frame's body: `x0` is the verification equation's result for the
reduced hash. -/
theorem body_ok (v : Proof.Sha3.AArch64.Permutation) (hR : Proof.Ed448.RecoverOk) (hE : Proof.Ed448.VerifyEqOk)
    (hL : L.Ok) (hc : Ctx0 L g vec m₀ t) (ha : Args L m₀) (h6 : t.gpr .x6 = L.scr) :
    WP isa (body v.callee) t fun u => Ctx0 L g vec m₀ u ∧
      u.gpr .x0 = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt m₀ L.pk 57) (Spec.Ed448.bytesAt m₀ L.sig 114)
        (Spec.Ed448.scalarReduce (Spec.Sha3.shake256 (hashIn L m₀) 114)) then 1 else 0 := by
  refine WP.seq (WP.mono (entry_ok hL hc ha h6) fun t₁ hc₁ => ?_)
  refine WP.seq (WP.mono (hash_ok v hL hc₁ ha) fun t₂ ⟨hc₂, hh₂⟩ => ?_)
  refine WP.seq (WP.mono (reduce_step hL hc₂) fun t₃ ⟨hc₃, hk₃⟩ => ?_)
  refine WP.mono (equation_step hR hE hL hc₃ ha) fun u ⟨hu, hx⟩ => ⟨hu.1, ?_⟩
  rw [hx, hk₃, show Spec.Ed448.bytesAt t₂.mem (L.E + BitVec.ofNat 64 fH) 114 =
    Spec.Sha3.bytesAt t₂.mem (L.E + BitVec.ofNat 64 fH) 114 from rfl, hh₂]

end VG.Proof.Ed448.AArch64.Verify
