import VerifiedGarbage.Proof.Ed448.AArch64.SignCached.Run

/-!
# Ed448 signing with a cached public key on AArch64: the whole function

`vg_ed448_sign_cached` meets `scLocal` and the ABI (`signCached_ok`), for any
implementation `v` of the Keccak permutation, given that the reference
ladder encodes `[k]B` (`BaseLadderOk`): the frame
(`Proof.Ed25519.AArch64.Whole.wrap_ok`) runs the body, whose signature is
RFC 8032's for the inputs as on entry.
-/

namespace VG.Proof.Ed448.AArch64.SignCached

open VG VG.AArch64 VG.Impl.Ed448.AArch64.SignCached
open VG.Proof.Ed25519.AArch64.Whole (entered bodyRd bodyWr)

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
    Lay.MSG, Lay.SCR, lay, List.cons_append, List.nil_append] using hc

theorem entry_args {s p : State} (hp : VG.Proof.Ed25519.AArch64.Whole.Saved (entered s) 6 p) :
    Args (lay s) p.mem := fun j hj => by
  have hw := VG.Proof.Ed25519.AArch64.Whole.saved_words hp hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> exact hw

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
    Lay.MSG, Lay.SCR, lay, List.cons_append, List.nil_append] using hu

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
theorem signCached_ok_body (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.BaseLadderOk) {s p : State}
    (h : scLocal.pre s) (hp : VG.Proof.Ed25519.AArch64.Whole.Saved (entered s) 6 p) :
    WP isa (body v.callee) (p.withRegions (bodyRd s) (bodyWr s)) fun u => Ctx0 (lay s) s.gpr s.v p.mem u ∧
      Spec.Ed448.bytesAt u.mem (lay s).out 114 = Spec.Ed448.sign (Spec.Ed448.bytesAt p.mem (lay s).seed 57)
        (Spec.Ed448.bytesAt p.mem (lay s).ctx (lay s).ctxLen.toNat)
        (Spec.Ed448.bytesAt p.mem (lay s).msg (lay s).len.toNat) :=
  body_ok v hb (lay_ok h) (entry_ctx h hp) (entry_args hp) (entry_x6 hp) (entry_x7 hp) (entry_pk h hp)

theorem signCached_ok (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.BaseLadderOk) {s : State}
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
