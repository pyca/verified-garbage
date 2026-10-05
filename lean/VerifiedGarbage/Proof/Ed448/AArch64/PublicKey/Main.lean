import VerifiedGarbage.Proof.Ed448.AArch64.PublicKey.Base
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wrap
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Ed448 public-key derivation on AArch64: the whole function

The contract the proof is written against (`pkLocal`: the facts of
`Spec.Ed448.publicKeyContract` for 352 bytes of stack, stated for AArch64),
and the correctness of `vg_ed448_public_key` against it, for any
implementation `v` of the Keccak permutation, given that
`vg_ed448_scalar_base` meets its contract (`BaseOk`, which the generic file passes in):
`SHAKE256(seed, 114)`, pruned, multiplies the base point into `out`; the
frame (`Proof.Ed25519.AArch64.Whole.wrap_ok`) restores `x30` and the stack
pointer, and the callee-saved registers are never written.
-/

namespace VG.Proof.Ed448.AArch64.PublicKey

open VG VG.AArch64 VG.Impl.Ed448.AArch64.PublicKey

/-- `vg_ed448_public_key(out = x0, seed = x1, scratch = x2)`, with 352 bytes of stack. -/
def pkLocal : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 57⟩
    let seed : Region := ⟨s.gpr .x1, 57⟩
    let scr : Region := ⟨s.gpr .x2, 8192⟩
    let stk : Region := below s.sp 352
    s.rd = [seed] ∧ s.wr = [out, scr] ∧
      out.Disjoint seed ∧ out.Disjoint scr ∧ seed.Disjoint scr ∧
      stk.Disjoint out ∧ stk.Disjoint seed ∧ stk.Disjoint scr ∧
      (s.gpr .x0).toNat + 57 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 57 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64 ∧ 352 ≤ s.sp.toNat
  post s t := Spec.Ed448.bytesAt t.mem (s.gpr .x0) 57 =
    Spec.Ed448.publicKey (Spec.Ed448.bytesAt s.mem (s.gpr .x1) 57)
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2

/-- The layout of a call from `s`. -/
def lay (s : State) : Lay := ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, VG.Proof.Ed25519.AArch64.Whole.base s⟩

theorem lay_ok {s : State} (h : pkLocal.pre s) : (lay s).Ok := by
  obtain ⟨_, _, os, oc, sc, ko, ks, kc, no, ns, nc, hsp⟩ := h
  exact ⟨os, oc, sc, ko.sub_left (VG.Proof.Ed25519.AArch64.Whole.stk_sub s),
    ks.sub_left (VG.Proof.Ed25519.AArch64.Whole.stk_sub s),
    kc.sub_left (VG.Proof.Ed25519.AArch64.Whole.stk_sub s), no, ns, nc,
    VG.Proof.Ed25519.AArch64.Whole.base_16 hsp, ko.sub_left (VG.Proof.Ed25519.AArch64.Whole.ck_sub s),
    ks.sub_left (VG.Proof.Ed25519.AArch64.Whole.ck_sub s), kc.sub_left (VG.Proof.Ed25519.AArch64.Whole.ck_sub s)⟩

theorem entry_below {s : State} (h : pkLocal.pre s) : 352 ≤ s.sp.toNat := h.2.2.2.2.2.2.2.2.2.2.2

theorem entry_writes {s : State} (h : pkLocal.pre s) :
    ∀ r ∈ s.wr, (below s.sp 352).Disjoint r := by
  intro r hr
  rw [h.2.1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.1

theorem entry_ctx {s p : State} (h : pkLocal.pre s)
    (hp : VG.Proof.Ed25519.AArch64.Whole.Saved (VG.Proof.Ed25519.AArch64.Whole.entered s) 6 p) :
    Ctx (lay s) s.gpr s.v p.mem (p.withRegions (VG.Proof.Ed25519.AArch64.Whole.bodyRd s)
      (VG.Proof.Ed25519.AArch64.Whole.bodyWr s)) := by
  have hc := VG.Proof.Ed25519.AArch64.Whole.saved_ctx hp
  simpa only [VG.Proof.Ed25519.AArch64.Whole.bodyRd, h.1, VG.Proof.Ed25519.AArch64.Whole.bodyWr, h.2.1,
    Ctx, Lay.inputs, Lay.outputs, Lay.SEED, Lay.OUT, Lay.SCR, Lay.ARGS, lay, List.cons_append,
    List.nil_append] using hc

theorem entry_args {s p : State}
    (hp : VG.Proof.Ed25519.AArch64.Whole.Saved (VG.Proof.Ed25519.AArch64.Whole.entered s) 6 p) :
    Arguments (lay s) p.mem := by
  intro j hj
  have hw := VG.Proof.Ed25519.AArch64.Whole.saved_words hp (j := j) (by omega)
  have he : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases he with rfl | rfl | rfl <;> exact hw

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem body_ok (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.AArch64.BaseOk)
    (hc : Ctx L g vec m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (body v.callee) t fun u => Ctx L g vec m₀ u ∧
      Spec.Ed448.bytesAt u.mem L.out 57 = Spec.Ed448.publicKey (Spec.Ed448.bytesAt m₀ L.seed 57) := by
  refine WP.seq (WP.mono (hash_ok v hc hL ha) fun u ⟨hu, hh⟩ => ?_)
  refine WP.seq (WP.mono (prune_step hu hh) fun u' ⟨hu', hs⟩ => ?_)
  refine WP.seq (WP.mono (base_step hb hu' hL ha hs) fun u'' ⟨hu'', hp⟩ => ?_)
  exact WP.mono (wipe_step hu'' hL) fun w ⟨hw, hm⟩ => ⟨hw, hm.trans hp⟩

theorem body_depth (v : Proof.Sha3.AArch64.Permutation) : (body v.callee).aarch64Depth ≤ 1 := by
  have ha := v.absorb_depth
  have hp := v.pad_depth
  have hs := v.squeeze_depth
  have hb := VG.Proof.Ed25519.AArch64.Whole.depth_zero_of_noFrames base_noFrames
  simp only [body, Impl.Ed448.AArch64.PublicKey.hash, Impl.Ed25519.AArch64.Whole.callWith, Code.aarch64Depth, Nat.max_le, hb, ha, hp, hs]
  omega

theorem publicKey_ok (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.AArch64.BaseOk) {s : State}
    (h : pkLocal.pre s) :
    WP isa (publicKeyWith v.callee) s fun u => abiPreserved s u ∧ pkLocal.post s u := by
  have hw := VG.Proof.Ed25519.AArch64.Whole.wrap_ok (body_depth v) (entry_below h) (entry_writes h)
    (P := fun m m' _ => Spec.Ed448.bytesAt m' (s.gpr .x0) 57 =
      Spec.Ed448.publicKey (Spec.Ed448.bytesAt m (s.gpr .x1) 57))
    (fun p hp => WP.mono (body_ok v hb (entry_ctx h hp) (lay_ok h) (entry_args hp)) fun u ⟨hu, ho⟩ => ⟨by
      simpa only [VG.Proof.Ed25519.AArch64.Whole.bodyRd, h.1, Ctx, Lay.inputs, Lay.outputs, Lay.SEED,
        Lay.OUT, Lay.SCR, Lay.ARGS, lay, h.2.1, List.cons_append, List.nil_append] using hu, ho⟩)
  refine WP.mono hw fun u ⟨hu, m, hf, hp⟩ => ⟨hu, ?_⟩
  have hs : Spec.Ed448.bytesAt m (s.gpr .x1) 57 = Spec.Ed448.bytesAt s.mem (s.gpr .x1) 57 := by
    unfold Spec.Ed448.bytesAt
    refine List.map_congr_left fun i hi => hf.bytes (R := ⟨s.gpr .x1, 57⟩) ?_
      (by change 57 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
    rintro r hr
    rw [List.mem_singleton.mp hr]
    exact (lay_ok h).ks.symm
  change Spec.Ed448.bytesAt u.mem (s.gpr .x0) 57 = _
  rw [hp, hs]

end VG.Proof.Ed448.AArch64.PublicKey
