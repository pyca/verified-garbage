import VerifiedGarbage.Proof.Ed448.AArch64.SignCached.Hash
import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Prune
import VerifiedGarbage.Proof.Ed448.Signing
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wipe

/-!
# Ed448 signing with a cached public key on AArch64: the frame's body

Pruning (`prune_step`), the calls of the Ed448 primitives (`reduceR_step`,
`base_step`, `reduceK_step`, `mulAdd_step`), each with what it writes, the
locals cleared (`wipe_step`), and the body (`body_ok`): the signature in
`out`, for the inputs as on entry (`Proof.Ed448.sign_pipeline`).
-/

namespace VG.Proof.Ed448.AArch64.SignCached

open VG VG.AArch64 VG.Impl.Ed448.AArch64.SignCached
open VG.Impl.Ed448.AArch64.Whole (Src setupS callS)
open VG.Proof.Ed448.AArch64.Whole (Env WCtx srcValue srcValid ScrOk wsetup_ok reduce_call base_call
  mulAdd_call Readable Writable Apart kept_frame prune_run sha3_bytesAt_length)
open VG.Proof.Ed25519.AArch64.Whole (Within FR CK ck_frame)

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem ed448_bytesAt (m : Mem) (p : Addr) (n : Nat) :
    Spec.Ed448.bytesAt m p n = Spec.Sha3.bytesAt m p n := rfl

theorem scr_writable (L : Lay) : Writable L.env L.SCR := .inr ⟨L.SCR, by simp [Lay.env], within_self _ _⟩

theorem outR_within (L : Lay) : Within ⟨L.out, 57⟩ L.OUT := ⟨0, (BitVec.add_zero _).symm, by show 0 + 57 ≤ 114; decide⟩
theorem outS_within (L : Lay) : Within ⟨L.out + BitVec.ofNat 64 57, 57⟩ L.OUT :=
  ⟨57, rfl, by show 57 + 57 ≤ 114; decide⟩

theorem outR_writable (L : Lay) : Writable L.env ⟨L.out, 57⟩ := .inr ⟨L.OUT, by simp [Lay.env], outR_within L⟩
theorem outS_writable (L : Lay) : Writable L.env ⟨L.out + BitVec.ofNat 64 57, 57⟩ :=
  .inr ⟨L.OUT, by simp [Lay.env], outS_within L⟩

theorem fr_scr (hL : L.Ok) {d n : Nat} (h : d + n ≤ 336) :
    Region.Disjoint ⟨L.E + BitVec.ofNat 64 d, n⟩ L.SCR :=
  hL.kc.sub_left (Offset.sub_base _ h)

theorem fr_out (hL : L.Ok) {d n : Nat} (h : d + n ≤ 336) :
    Region.Disjoint ⟨L.E + BitVec.ofNat 64 d, n⟩ L.OUT :=
  hL.ko.sub_left (Offset.sub_base _ h)

/-- A region of the locals apart from the kept words. -/
theorem fr_apart {d n : Nat} (h₁ : 16 ≤ d) (h₂ : d + n ≤ 200) : Apart L.env ⟨L.E + BitVec.ofNat 64 d, n⟩ :=
  ⟨⟨d, rfl, by show d + n ≤ 256; omega⟩, fun p hp => by
    simp only [Lay.env, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
      exact Offset.disjoint _ (by simp [fLen, fScr, fHdr]; omega) (by simp [fLen, fScr, fHdr]) (by omega)⟩

theorem out_sep (hL : L.Ok) : Region.Disjoint ⟨L.out, 57⟩ ⟨L.out + BitVec.ofNat 64 57, 57⟩ := by
  have h := Offset.disjoint (L.out) (d := 0) (n := 57) (e := 57) (k := 57) (by omega) (by omega)
    (by have := hL.no; omega)
  rwa [BitVec.add_zero] at h

/-- The word of `out` at 57. -/
theorem outS_src (hL : L.Ok) (hc : WCtx L.env g vec m₀ t) (ha : Args L m₀) (x0 : BitVec 64) :
    srcValue L.env.E t.mem x0 aR = L.out + BitVec.ofNat 64 57 := by
  show t.mem.read (L.E + BitVec.ofNat 64 (256 + 8 * 0)) 8 + BitVec.ofNat 64 57 = _
  rw [arg_word hL hc.1 ha (j := 0) (by decide)]
  rfl

/-- `s`: the hash pruned. -/
theorem prune_step (hL : L.Ok) (hc : WCtx L.env g vec m₀ t) {hb : List Byte}
    (hh : Spec.Sha3.bytesAt t.mem (L.E + BitVec.ofNat 64 fH) 114 = hb) :
    WP isa (.block prune) t fun u => WCtx L.env g vec m₀ u ∧
      Frame [⟨L.E + BitVec.ofNat 64 fS, 64⟩] t.mem u.mem ∧
      Spec.Ed448.decodeLE (Spec.Ed448.bytesAt u.mem (L.E + BitVec.ofNat 64 fS) 57) = Spec.Ed448.prune hb := by
  have hV := env_ok hL
  have hwrite : (⟨t.sp, 256⟩ : Region) ∈ t.wr := by rw [hc.1.sp, hc.1.wr]; exact List.mem_cons_self
  have hh' : Spec.Sha3.bytesAt t.mem (t.sp + BitVec.ofNat 64 fH) 114 = hb := by rw [hc.1.sp]; exact hh
  refine WP.mono (prune_run (h := fH) (d := fS) hwrite (by decide) (by decide) (by decide) (by decide)
    (by decide) hh') fun u ⟨hu, hf, hp⟩ => ?_
  rw [hc.1.sp] at hf hp
  refine ⟨hc.of_frame hV hu.rd hu.wr hu.sp (fun r hr _ => ?_) (fun r _ => by rw [hu.v]) hf ?_, hf, hp⟩
  · apply hu.regs r <;> intro h <;> subst r <;> simp [preserved] at hr
  · intro r hr
    rw [List.mem_singleton.mp hr]
    exact .inl (fr_apart (by decide) (by decide))

/-- `r`, into the second half of `out`. -/
theorem reduceR_step (hL : L.Ok) (hc : WCtx L.env g vec m₀ t) (ha : Args L m₀) :
    WP isa (callS reduceRArgs "vg_ed448_scalar_reduce" Impl.Ed448.AArch64.scalarReduce) t fun u =>
      WCtx L.env g vec m₀ u ∧
      Frame [⟨L.out + BitVec.ofNat 64 57, 57⟩, L.SCR, CK L.E] t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem (L.out + BitVec.ofNat 64 57) 57 =
        Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt t.mem (L.E + BitVec.ofNat 64 fH) 114) := by
  have hV := env_ok hL
  refine WP.seq (WP.mono (wsetup_ok hV hc (args := reduceRArgs) (by decide)
    (by simp [reduceRArgs, aR, srcValid, VG.Proof.Ed25519.AArch64.Whole.valid, fH, fScr]) rfl
    (by simp [reduceRArgs, preserved])) fun u ⟨hu, hm, hv⟩ => ?_)
  have h0 : u.gpr .x0 = L.out + BitVec.ofNat 64 57 :=
    (hv (.x0, aR) (by simp [reduceRArgs])).trans (outS_src hL hc ha _)
  have h1 : u.gpr .x1 = L.E + BitVec.ofNat 64 fH := hv (.x1, .val (.frame fH)) (by simp [reduceRArgs])
  have h2 : u.gpr .x2 = L.scr := by
    rw [hv (.x2, .loc fScr 0) (by simp [reduceRArgs]), (scrOk hL).loc hc, BitVec.add_zero]
  refine WP.mono (reduce_call hV hu h0 h1 h2 (fr_scr hL (by decide)) (.inl ⟨fH, rfl, show fH + 114 ≤ 256 by decide⟩)
    (outS_writable L) (scr_writable L)) fun w ⟨hw, hf, hk⟩ => ⟨hw, by rw [← hm]; exact hf, by rw [hk, hm]⟩

/-- `R = [r]B`, into the first half of `out`. -/
theorem base_step (hb : Proof.Ed448.BaseLadderOk) (hL : L.Ok) (hc : WCtx L.env g vec m₀ t) (ha : Args L m₀) :
    WP isa (callS baseArgs "vg_ed448_scalar_base" Impl.Ed448.AArch64.scalarBase) t fun u =>
      WCtx L.env g vec m₀ u ∧ Frame [⟨L.out, 57⟩, L.SCR, CK L.E] t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem L.out 57 =
        Spec.Ed448.scalarBase (Spec.Ed448.bytesAt t.mem (L.out + BitVec.ofNat 64 57) 57) := by
  have hV := env_ok hL
  refine WP.seq (WP.mono (wsetup_ok hV hc (args := baseArgs) (by decide)
    (by simp [baseArgs, aOut, aR, srcValid, VG.Proof.Ed25519.AArch64.Whole.valid, fScr]) rfl
    (by simp [baseArgs, preserved])) fun u ⟨hu, hm, hv⟩ => ?_)
  have h0 : u.gpr .x0 = L.out :=
    (hv (.x0, aOut) (by simp [baseArgs])).trans (arg_src hL hc.1 ha (j := 0) (by decide) _)
  have h1 : u.gpr .x1 = L.out + BitVec.ofNat 64 57 :=
    (hv (.x1, aR) (by simp [baseArgs])).trans (outS_src hL hc ha _)
  have h2 : u.gpr .x2 = L.scr := by
    rw [hv (.x2, .loc fScr 0) (by simp [baseArgs]), (scrOk hL).loc hc, BitVec.add_zero]
  refine WP.mono (base_call hb hV hu h0 h1 h2 (hL.oc.sub_left (outR_within L).sub)
    (hL.oc.sub_left (outS_within L).sub) hL.nc (.inr ⟨L.OUT, by simp [Lay.env], outS_within L⟩)
    (outR_writable L) (scr_writable L)) fun w ⟨hw, hf, hk⟩ => ⟨hw, by rw [← hm]; exact hf, by rw [hk, hm]⟩

/-- `k`, over the hash. -/
theorem reduceK_step (hL : L.Ok) (hc : WCtx L.env g vec m₀ t) :
    WP isa (callS reduceKArgs "vg_ed448_scalar_reduce" Impl.Ed448.AArch64.scalarReduce) t fun u =>
      WCtx L.env g vec m₀ u ∧ Frame [⟨L.E + BitVec.ofNat 64 fH, 57⟩, L.SCR, CK L.E] t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem (L.E + BitVec.ofNat 64 fH) 57 =
        Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt t.mem (L.E + BitVec.ofNat 64 fH) 114) := by
  have hV := env_ok hL
  refine WP.seq (WP.mono (wsetup_ok hV hc (args := reduceKArgs) (by decide)
    (by simp [reduceKArgs, srcValid, VG.Proof.Ed25519.AArch64.Whole.valid, fH, fScr]) rfl
    (by simp [reduceKArgs, preserved])) fun u ⟨hu, hm, hv⟩ => ?_)
  have h0 : u.gpr .x0 = L.E + BitVec.ofNat 64 fH := hv (.x0, .val (.frame fH)) (by simp [reduceKArgs])
  have h1 : u.gpr .x1 = L.E + BitVec.ofNat 64 fH := hv (.x1, .val (.frame fH)) (by simp [reduceKArgs])
  have h2 : u.gpr .x2 = L.scr := by
    rw [hv (.x2, .loc fScr 0) (by simp [reduceKArgs]), (scrOk hL).loc hc, BitVec.add_zero]
  refine WP.mono (reduce_call hV hu h0 h1 h2 (fr_scr hL (by decide)) (.inl ⟨fH, rfl, show fH + 114 ≤ 256 by decide⟩)
    (.inl (fr_apart (by decide) (by decide))) (scr_writable L)) fun w ⟨hw, hf, hk⟩ =>
      ⟨hw, by rw [← hm]; exact hf, by rw [hk, hm]⟩

/-- `S = (r + k s) mod L`, into the second half of `out`. -/
theorem mulAdd_step (hL : L.Ok) (hc : WCtx L.env g vec m₀ t) (ha : Args L m₀) :
    WP isa (callS mulAddArgs "vg_ed448_scalar_mul_add" Impl.Ed448.AArch64.scalarMulAdd) t fun u =>
      WCtx L.env g vec m₀ u ∧ Frame [⟨L.out + BitVec.ofNat 64 57, 57⟩, L.SCR, CK L.E] t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem (L.out + BitVec.ofNat 64 57) 57 =
        Spec.Ed448.scalarMulAdd (Spec.Ed448.bytesAt t.mem (L.out + BitVec.ofNat 64 57) 57)
          (Spec.Ed448.bytesAt t.mem (L.E + BitVec.ofNat 64 fH) 57)
          (Spec.Ed448.bytesAt t.mem (L.E + BitVec.ofNat 64 fS) 57) := by
  have hV := env_ok hL
  refine WP.seq (WP.mono (wsetup_ok hV hc (args := mulAddArgs) (by decide)
    (by simp [mulAddArgs, aR, srcValid, VG.Proof.Ed25519.AArch64.Whole.valid, fH, fS, fScr]) rfl
    (by simp [mulAddArgs, preserved])) fun u ⟨hu, hm, hv⟩ => ?_)
  have h0 : u.gpr .x0 = L.out + BitVec.ofNat 64 57 :=
    (hv (.x0, aR) (by simp [mulAddArgs])).trans (outS_src hL hc ha _)
  have h1 : u.gpr .x1 = L.out + BitVec.ofNat 64 57 :=
    (hv (.x1, aR) (by simp [mulAddArgs])).trans (outS_src hL hc ha _)
  have h2 : u.gpr .x2 = L.E + BitVec.ofNat 64 fH := hv (.x2, .val (.frame fH)) (by simp [mulAddArgs])
  have h3 : u.gpr .x3 = L.E + BitVec.ofNat 64 fS := hv (.x3, .val (.frame fS)) (by simp [mulAddArgs])
  have h4 : u.gpr .x4 = L.scr := by
    rw [hv (.x4, .loc fScr 0) (by simp [mulAddArgs]), (scrOk hL).loc hc, BitVec.add_zero]
  refine WP.mono (mulAdd_call hV hu h0 h1 h2 h3 h4 (hL.oc.sub_left (outS_within L).sub)
    (fr_scr hL (by decide)) (fr_scr hL (by decide)) (.inr ⟨L.OUT, by simp [Lay.env], outS_within L⟩)
    (.inl ⟨fH, rfl, show fH + 57 ≤ 256 by decide⟩) (.inl ⟨fS, rfl, show fS + 57 ≤ 256 by decide⟩)
    (outS_writable L) (scr_writable L)) fun w ⟨hw, hf, hk⟩ => ⟨hw, by rw [← hm]; exact hf, by rw [hk, hm]⟩

/-- The hash, `k` and `s` cleared. -/
theorem wipe_step (hL : L.Ok) (hc : WCtx L.env g vec m₀ t) :
    WP isa (.block wipe) t fun u => WCtx L.env g vec m₀ u ∧
      Frame [⟨L.E + BitVec.ofNat 64 16, 184⟩] t.mem u.mem := by
  have hV := env_ok hL
  refine WP.mono (VG.Proof.Ed25519.AArch64.Whole.Ctx.zeroWords hc.1 (start := 2) (count := 23) (by decide))
    fun u ⟨hu, hf, _⟩ => ⟨⟨hu, kept_frame hV hc.2 (hf.mono fun r hr => List.mem_append_left _ hr) fun r hr => ?_⟩, hf⟩
  rw [List.mem_singleton.mp hr]
  exact .inl (fr_apart (by decide) (by decide))

/-- The specification's hash input. -/
theorem dom_eq (L : Lay) (m : Mem) (X : List Byte) :
    domIn L m X = Spec.Ed448.dom4 0 (Spec.Sha3.bytesAt m L.ctx L.ctxLen.toNat) ++
      (X ++ Spec.Sha3.bytesAt m L.msg L.len.toNat) := by
  simp only [domIn, hdrBytes, Spec.Ed448.dom4, sha3_bytesAt_length, List.append_assoc, List.cons_append,
    List.nil_append]

theorem bytes_split (m : Mem) (p : Addr) :
    Spec.Sha3.bytesAt m p 114 = Spec.Sha3.bytesAt m p 57 ++ Spec.Sha3.bytesAt m (p + BitVec.ofNat 64 57) 57 :=
  Proof.X25519.bytesAt_add m p 57 57

end VG.Proof.Ed448.AArch64.SignCached
