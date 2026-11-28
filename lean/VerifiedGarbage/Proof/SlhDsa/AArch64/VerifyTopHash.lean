module

-- separate module: the digest, over TopHash, rebuilt only when it or Ctx changes

public import VerifiedGarbage.Proof.SlhDsa.AArch64.VerifyTopCtx
public import VerifiedGarbage.Proof.SlhDsa.AArch64.TopHash
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SLH-DSA (SHAKE) on AArch64, `verify`: the digest

The hash of the body (`TopHash.hashM_ok`), from a state of `Ctx` with the
message and the context string in `x20`–`x23` (`HRegs`): the digest
`H_msg(R, PK.seed, PK.root, M′)`, `R` the signature's first `n` bytes, to
`oDigest` (`hash_ok`), keeping `Ctx`.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.VerifyTop

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Impl.SlhDsa.AArch64.Shake (Arg)
open VG.Proof.MlKem.AArch64 (Kept)
open VG.Proof.SlhDsa.AArch64.Sign (SCR PROT mPrime)

section
variable {p : Params} {σ t : State}

theorem stream_sub (σ : State) {o l : Nat} (_h₁ : Layout.oStream ≤ o) (h₂ : o + l ≤ Layout.oStream + 840) :
    Region.Sub ⟨at' (σ.gpr .x7) o, l⟩ (SCR σ) :=
  Offset.sub_base _ (by simp only [Layout.oStream, scratchLen] at h₂ ⊢; omega)

/-- What lies apart from `scratch` and the stack keeps its bytes. -/
theorem Ctx.bytes_out (hc : Ctx p σ t) {a : Addr} {l : Nat} (hl : l ≤ 2 ^ 64)
    (h1 : Region.Disjoint ⟨a, l⟩ (SCR σ)) (h3 : Region.Disjoint ⟨a, l⟩ (below σ.sp 16)) :
    bytesAt t.mem a l = bytesAt σ.mem a l :=
  bytesAt_frame hc.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> with_reducible assumption) hl

theorem stk_eq (hc : Ctx p σ t) : MlKem.AArch64.stk t = below σ.sp 16 := by
  simp only [MlKem.AArch64.stk, hc.sp]; rfl

theorem ks_of (hK : VG p σ) (hc : Ctx p σ t) : KS t (σ.gpr .x7) := by
  refine ⟨hc.x19, by rw [hc.sp]; exact hK.sp, ?_, ?_, ?_⟩
  · rw [stk_eq hc]; exact hK.stk_scr.sub_right (stream_sub σ (Nat.le_refl _) (by omega))
  · rw [stk_eq hc]; exact hK.stk_scr.sub_right (stream_sub σ (by omega) (by omega))
  · rw [hc.wr, hK.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Layout.oStream, rfl, by simp only [Layout.oStream, scratchLen]; omega⟩
    · exact ⟨_, List.mem_cons_self .., Layout.oStream + 200, rfl, by simp only [Layout.oStream, scratchLen]; omega⟩

/-- A piece in `scratch`, apart from the stream. -/
theorem pieceIn_scr (hK : VG p σ) (hc : Ctx p σ t) {o l : Nat} (h : o + l ≤ Layout.oStream) :
    PieceIn t (σ.gpr .x7) (at' (σ.gpr .x7) o) l := by
  have hs : Region.Sub ⟨at' (σ.gpr .x7) o, l⟩ (SCR σ) :=
    Offset.sub_base _ (by simp only [Layout.oStream, scratchLen] at h ⊢; omega)
  refine ⟨Offset.disjoint _ (by omega) (by simp only [Layout.oStream] at h ⊢; omega)
      (by simp only [Layout.oStream]; omega),
    Offset.disjoint _ (by omega) (by simp only [Layout.oStream] at h ⊢; omega) (by simp only [Layout.oStream]; omega),
    by rw [stk_eq hc]; exact hK.stk_scr.sub_right hs, ?_⟩
  rw [hc.rd, hc.wr, hK.rd, hK.wr]
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), o, rfl, by
    simp only [Layout.oStream, scratchLen] at h ⊢; omega⟩

/-- A piece apart from `scratch` and the stack, in a region of `σ`. -/
theorem pieceIn_out (hc : Ctx p σ t) {a : Addr} {l : Nat} (hd : Region.Disjoint ⟨a, l⟩ (SCR σ))
    (hs : (below σ.sp 16).Disjoint ⟨a, l⟩) (hin : Covers [⟨a, l⟩] (σ.rd ++ σ.wr)) :
    PieceIn t (σ.gpr .x7) a l :=
  ⟨hd.sub_right (stream_sub σ (Nat.le_refl _) (by omega)), hd.sub_right (stream_sub σ (by omega) (by omega)),
    by rw [stk_eq hc]; exact hs, by rw [hc.rd, hc.wr]; exact hin⟩

/-- A piece the hash writes: a part of `scratch` apart from the stream. -/
theorem pieceOut_scr (hK : VG p σ) (hc : Ctx p σ t) {o l : Nat}
    (h : o + l ≤ Layout.oStream) : PieceOut t (σ.gpr .x7) (at' (σ.gpr .x7) o) l := by
  have hs : Region.Sub ⟨at' (σ.gpr .x7) o, l⟩ (SCR σ) :=
    Offset.sub_base _ (by simp only [Layout.oStream, scratchLen] at h ⊢; omega)
  refine ⟨Offset.disjoint _ (by omega) (by simp only [Layout.oStream]; omega)
      (by simp only [Layout.oStream] at h ⊢; omega),
    Offset.disjoint _ (by omega) (by simp only [Layout.oStream] at h ⊢; omega) (by simp only [Layout.oStream]; omega),
    by rw [stk_eq hc]; exact hK.stk_scr.sub_right hs, ?_⟩
  rw [hc.wr, hK.wr]
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_cons_self .., o, rfl, by simp only [Layout.oStream, scratchLen] at h ⊢; omega⟩

theorem free_hash (hc : Ctx p σ t) {D : Region} (hD : Free σ D) :
    ∀ r ∈ hashR t (σ.gpr .x7) ++ [D], Free σ r := by
  intro r hr
  simp only [hashR, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  have eS : Layout.oStream = 2368 := rfl
  have eT : Layout.oTop = 1536 := rfl
  rcases hr with (rfl | rfl | rfl) | rfl
  · exact .inl ⟨stream_sub σ (Nat.le_refl _) (by omega), Offset.disjoint (σ.gpr .x7) (d := Layout.oStream) (n := 200)
      (e := Layout.oTop) (k := 256) (by omega) (by omega) (by omega)⟩
  · exact .inl ⟨stream_sub σ (by omega) (by omega), Offset.disjoint (σ.gpr .x7) (d := Layout.oStream + 200) (n := 640)
      (e := Layout.oTop) (k := 256) (by omega) (by omega) (by omega)⟩
  · exact .inr (by rw [hc.sp]; exact fun x hx => hx)
  · exact hD

theorem hregs_kept {rs : List Region} {u : State} (hr : HRegs σ t) (hk : Kept rs t u) : HRegs σ u :=
  ⟨by rw [hk.cs .x20 (by decide) (by decide), hr.x20], by rw [hk.cs .x21 (by decide) (by decide), hr.x21],
    by rw [hk.cs .x22 (by decide) (by decide), hr.x22], by rw [hk.cs .x23 (by decide) (by decide), hr.x23]⟩

theorem ctx_kept (hz : Sz p) (hK : VG p σ) (hc : Ctx p σ t) {u : State} {D : Region} (hD : Free σ D)
    (hk : Kept (hashR t (σ.gpr .x7) ++ [D]) t u) : Ctx p σ u :=
  hc.of_frame hz.n32 hK hk.rd hk.wr hk.sp (hk.cs .x19 (by decide) (by decide)) (hk.cs .x24 (by decide) (by decide))
    (fun r hr => hk.cs r (by revert r; decide) (by revert r; decide)) hk.vcs hk.frame (free_hash hc hD)

/-- `M′`, as the hash reads it. -/
theorem mprime_eq (hK : VG p σ) (hc : Ctx p σ t) (hr : HRegs σ t) :
    bytesAt t.mem (at' (σ.gpr .x7) Layout.oHdr) 2 ++ bytesAt t.mem (t.gpr .x22) (t.gpr .x23).toNat ++
      bytesAt t.mem (t.gpr .x20) (t.gpr .x21).toNat = mPrime σ := by
  rw [hc.hdr, hr.x22, hr.x23, hr.x20, hr.x21,
    hc.bytes_out (by have := hK.f_ctx; omega) hK.ctx_scr hK.stk_ctx.symm,
    hc.bytes_out (by have := hK.f_msg; omega) hK.msg_scr hK.stk_msg.symm]

theorem sigR_sub (hsl : (σ.gpr .x6).toNat = p.sigLen) (hn : p.n ≤ p.sigLen) :
    Region.Sub ⟨σ.gpr .x5, p.n⟩ ⟨σ.gpr .x5, (σ.gpr .x6).toNat⟩ :=
  Region.sub_prefix (by omega)

/-- What the hash of the digest needs. -/
theorem hashIn (hz : Sz p) (hm : p.m ≤ 64) (hK : VG p σ) (hsl : (σ.gpr .x6).toNat = p.sigLen)
    (hc : Ctx p σ t) (hr : HRegs σ t) :
    HashIn p.n t (σ.gpr .x7) [.reg .x24, .scr Layout.oPkSeed, .scr Layout.oPkRoot] (.scr Layout.oDigest) p.m := by
  have hn := hz.n32
  have hsig : p.n ≤ p.sigLen := by simp only [Params.sigLen]; exact Nat.le_mul_of_pos_left _ (by omega)
  have eS : ∀ o, argVal t (.scr o) = at' (σ.gpr .x7) o := fun o => by simp only [argVal, hc.x19]
  have eD : Layout.oDigest = 1792 := rfl
  refine ⟨ks_of hK hc, fun x hx => ?_, by simp; omega,
    pieceIn_scr hK hc (by simp only [Layout.oHdr, Layout.oStream, Layout.oTop]; omega),
    by rw [hr.x22, hr.x23]; exact pieceIn_out hc hK.ctx_scr hK.stk_ctx (Covers.one ⟨_, (by rw [hK.rd]; simp), Region.contains_self _ _⟩),
    by rw [hr.x20, hr.x21]; exact pieceIn_out hc hK.msg_scr hK.stk_msg (Covers.one ⟨_, (by rw [hK.rd]; simp), Region.contains_self _ _⟩),
    show Layout.oDigest < 4096 by decide,
    by rw [eS]; exact pieceOut_scr hK hc (by simp only [Layout.oStream]; omega), by omega⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
    show PieceIn t _ (t.gpr .x24) p.n
    rw [hc.x24]
    have hs := sigR_sub hsl hsig
    refine pieceIn_out hc (hK.sig_scr.sub_left hs) (hK.stk_sig.sub_right hs) ?_
    rw [hK.rd]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨σ.gpr .x5, (σ.gpr .x6).toNat⟩, by simp, 0, by simp, by simp only; omega⟩
  · exact ⟨show Layout.oPkSeed < 4096 by decide, by rw [eS]; exact pieceIn_scr hK hc (by
      simp only [Layout.oPkSeed, Layout.oKeys, Layout.oStream]; omega)⟩
  · exact ⟨show Layout.oPkRoot < 4096 by decide, by rw [eS]; exact pieceIn_scr hK hc (by
      simp only [Layout.oPkRoot, Layout.oKeys, Layout.oStream]; omega)⟩

/-- The digest to `oDigest`. -/
theorem hash_ok (hz : Sz p) (hm : p.m ≤ 64) (v : Proof.Sha3.AArch64.Permutation) {f : Impl.SlhDsa.AArch64.Shake.Fns}
    (hv : f.keccak = v.callee) (hK : VG p σ) (hsl : (σ.gpr .x6).toNat = p.sigLen) (hc : Ctx p σ t)
    (hr : HRegs σ t) :
    WP isa (Impl.SlhDsa.AArch64.Shake.hashM' p f [.reg .x24, .scr Layout.oPkSeed, .scr Layout.oPkRoot]
      (.scr Layout.oDigest) p.m) t fun t' =>
      Ctx p σ t' ∧ bytesAt t'.mem (at' (σ.gpr .x7) Layout.oDigest) p.m = Dv p σ := by
  have hn := hz.n32
  have hsig : p.n ≤ p.sigLen := by simp only [Params.sigLen]; exact Nat.le_mul_of_pos_left _ (by omega)
  have eS : ∀ o, argVal t (.scr o) = at' (σ.gpr .x7) o := fun o => by simp only [argVal, hc.x19]
  have eD : Layout.oDigest = 1792 := rfl
  have hfr : Free σ ⟨at' (σ.gpr .x7) Layout.oDigest, p.m⟩ :=
    .inl ⟨Offset.sub_base _ (by simp only [scratchLen]; omega), Offset.disjoint _ (by simp only [Layout.oTop]; omega)
      (by omega) (by simp only [Layout.oTop]; omega)⟩
  refine WP.mono (hashM_ok p hn v hv (hashIn hz hm hK hsl hc hr)) fun t' ⟨hk, hb⟩ => ?_
  rw [eS] at hk hb
  refine ⟨ctx_kept hz hK hc hfr hk, ?_⟩
  have hs := sigR_sub hsl hsig
  rw [hb, Dv, ← mprime_eq hK hc hr]
  simp only [hashMsg, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, eS]
  rw [show argVal t (.reg .x24) = t.gpr .x24 from rfl, hc.x24,
    hc.bytes_out (by omega) (hK.sig_scr.sub_left hs) (hK.stk_sig.sub_right hs).symm,
    show Layout.oPkSeed = Layout.oPkSeed + 32 * 0 from rfl, hc.keys 0 (by decide),
    show Layout.oPkRoot = Layout.oPkSeed + 32 * 1 from rfl, hc.keys 1 (by decide), Nat.mul_zero, Nat.mul_one,
    BitVec.add_zero]
  simp only [List.append_assoc]

end

end VG.Proof.SlhDsa.AArch64.VerifyTop
