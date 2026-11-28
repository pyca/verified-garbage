module

-- separate module: the two hashes, over TopHash, rebuilt only when it or Ctx changes

public import VerifiedGarbage.Proof.SlhDsa.AArch64.SignPro
public import VerifiedGarbage.Proof.SlhDsa.AArch64.TopHash
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SLH-DSA (SHAKE) on AArch64, `sign`: `R` and the digest

The two hashes of the body (`TopHash.hashM_ok`), from a state of `Ctx`
with the arguments in `x20`–`x25` (`HRegs`): `R = PRF_msg(SK.prf, addrnd,
M′)` to the signature's first `n` bytes (`hashR_ok`), then the digest
`H_msg(R, PK.seed, PK.root, M′)` to `oDigest` (`hashD_ok`), each keeping
`Ctx`.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Sign

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Impl.SlhDsa.AArch64.Shake (Arg)
open VG.Proof.MlKem.AArch64 (Kept)

/-- `R` and the digest of the entry state `σ`. -/
abbrev Rv (p : Params) (σ : State) : List Byte :=
  Spec.Sha3.shake256 (chunk (skB p σ) p.n 1 ++ rndB p σ ++ mPrime σ) p.n
abbrev Dv (p : Params) (σ : State) : List Byte :=
  Spec.Sha3.shake256 (Rv p σ ++ chunk (skB p σ) p.n 2 ++ chunk (skB p σ) p.n 3 ++ mPrime σ) p.m

/-- What lies apart from `scratch`, `sig` and the stack keeps its bytes. -/
theorem Ctx.bytes_out {p : Params} {σ t : State} (hc : Ctx p σ t) {a : Addr} {l : Nat} (hl : l ≤ 2 ^ 64)
    (h1 : Region.Disjoint ⟨a, l⟩ (SCR σ)) (h2 : Region.Disjoint ⟨a, l⟩ (SIG p σ))
    (h3 : Region.Disjoint ⟨a, l⟩ (below σ.sp 16)) : bytesAt t.mem a l = bytesAt σ.mem a l :=
  bytesAt_frame hc.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption) hl

section
variable {p : Params} {σ t : State}

theorem stk_eq (hc : Ctx p σ t) : MlKem.AArch64.stk t = below σ.sp 16 := by
  simp only [MlKem.AArch64.stk, hc.sp]; rfl

theorem stream_sub (σ : State) {o l : Nat} (_h₁ : Layout.oStream ≤ o) (h₂ : o + l ≤ Layout.oStream + 840) :
    Region.Sub ⟨at' (σ.gpr .x7) o, l⟩ (SCR σ) :=
  Offset.sub_base _ (by simp only [Layout.oStream, scratchLen] at h₂ ⊢; omega)

theorem ks_of (hK : SG p σ) (hc : Ctx p σ t) : KS t (σ.gpr .x7) := by
  refine ⟨hc.x19, by rw [hc.sp]; exact hK.sp, ?_, ?_, ?_⟩
  · rw [stk_eq hc]; exact hK.stk_scr.sub_right (stream_sub σ (Nat.le_refl _) (by omega))
  · rw [stk_eq hc]; exact hK.stk_scr.sub_right (stream_sub σ (by omega) (by omega))
  · rw [hc.wr, hK.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Layout.oStream, rfl, by
        simp only [Layout.oStream, scratchLen]; omega⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Layout.oStream + 200, rfl, by
        simp only [Layout.oStream, scratchLen]; omega⟩

/-- A piece in `scratch`, apart from the stream. -/
theorem pieceIn_scr (hK : SG p σ) (hc : Ctx p σ t) {o l : Nat} (h : o + l ≤ Layout.oStream) :
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
  exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), o, rfl, by
    simp only [Layout.oStream, scratchLen] at h ⊢; omega⟩

/-- A piece apart from `scratch` and the stack, in the regions of `σ`. -/
theorem pieceIn_out (hc : Ctx p σ t) {a : Addr} {l : Nat} (hd : Region.Disjoint ⟨a, l⟩ (SCR σ))
    (hs : (below σ.sp 16).Disjoint ⟨a, l⟩) (hin : ⟨a, l⟩ ∈ σ.rd ++ σ.wr) :
    PieceIn t (σ.gpr .x7) a l :=
  ⟨hd.sub_right (stream_sub σ (Nat.le_refl _) (by omega)), hd.sub_right (stream_sub σ (by omega) (by omega)),
    by rw [stk_eq hc]; exact hs, by rw [hc.rd, hc.wr]; exact Covers.one ⟨_, hin, Region.contains_self _ _⟩⟩

/-- A piece the hash writes: a part of `sig`. -/
theorem pieceOut_sig (hK : SG p σ) (hc : Ctx p σ t) {off l : Nat} (hl : off + l ≤ p.sigLen) :
    PieceOut t (σ.gpr .x7) (σ.gpr .x6 + BitVec.ofNat 64 off) l := by
  have hs : Region.Sub ⟨σ.gpr .x6 + BitVec.ofNat 64 off, l⟩ (SIG p σ) := Offset.sub_base _ hl
  refine ⟨(hK.sig_scr.sub_left hs).symm.sub_left (stream_sub σ (Nat.le_refl _) (by omega)),
    (hK.sig_scr.sub_left hs).sub_right (stream_sub σ (by omega) (by omega)),
    by rw [stk_eq hc]; exact hK.stk_sig.sub_right hs, ?_⟩
  rw [hc.wr, hK.wr]
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_cons_self .., off, rfl, hl⟩

/-- A piece the hash writes: a part of `scratch` apart from the stream and `PROT`. -/
theorem pieceOut_scr (hK : SG p σ) (hc : Ctx p σ t) {o l : Nat}
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
  exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), o, rfl, by
    simp only [Layout.oStream, scratchLen] at h ⊢; omega⟩

theorem free_hash (hc : Ctx p σ t) {D : Region} (hD : Free p σ D) :
    ∀ r ∈ hashR t (σ.gpr .x7) ++ [D], Free p σ r := by
  intro r hr
  simp only [hashR, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  have eS : Layout.oStream = 2368 := rfl
  have eT : Layout.oTop = 1536 := rfl
  rcases hr with (rfl | rfl | rfl) | rfl
  · exact .inl ⟨stream_sub σ (Nat.le_refl _) (by omega), Offset.disjoint (σ.gpr .x7) (d := Layout.oStream) (n := 200)
      (e := Layout.oTop) (k := 256) (by omega) (by omega) (by omega)⟩
  · exact .inl ⟨stream_sub σ (by omega) (by omega), Offset.disjoint (σ.gpr .x7) (d := Layout.oStream + 200) (n := 640)
      (e := Layout.oTop) (k := 256) (by omega) (by omega) (by omega)⟩
  · exact .inr (.inr (by rw [hc.sp]; exact fun x hx => hx))
  · exact hD

theorem hregs_kept {rs : List Region} {u : State} (hr : HRegs σ t) (hk : Kept rs t u) : HRegs σ u :=
  ⟨by rw [hk.cs .x20 (by decide) (by decide), hr.x20], by rw [hk.cs .x21 (by decide) (by decide), hr.x21],
    by rw [hk.cs .x22 (by decide) (by decide), hr.x22], by rw [hk.cs .x23 (by decide) (by decide), hr.x23],
    by rw [hk.cs .x24 (by decide) (by decide), hr.x24], by rw [hk.cs .x25 (by decide) (by decide), hr.x25]⟩

theorem ctx_kept (hz : Sz p) (hK : SG p σ) (hc : Ctx p σ t) {u : State} {D : Region} (hD : Free p σ D)
    (hk : Kept (hashR t (σ.gpr .x7) ++ [D]) t u) : Ctx p σ u :=
  hc.of_frame hz.n32 hK hk.rd hk.wr hk.sp (hk.cs .x19 (by decide) (by decide))
    (fun r hr => hk.cs r (by revert r; decide) (by revert r; decide)) hk.vcs hk.frame (free_hash hc hD)

/-- `M′`, as the hash reads it. -/
theorem mprime_eq (hK : SG p σ) (hc : Ctx p σ t) (hr : HRegs σ t) :
    bytesAt t.mem (at' (σ.gpr .x7) Layout.oHdr) 2 ++ bytesAt t.mem (t.gpr .x22) (t.gpr .x23).toNat ++
      bytesAt t.mem (t.gpr .x20) (t.gpr .x21).toNat = mPrime σ := by
  rw [hc.hdr, hr.x22, hr.x23, hr.x20, hr.x21,
    hc.bytes_out (by have := hK.f_ctx; omega) hK.ctx_scr hK.ctx_sig hK.stk_ctx.symm,
    hc.bytes_out (by have := hK.f_msg; omega) hK.msg_scr hK.msg_sig hK.stk_msg.symm]

/-- What the hash of `R` needs. -/
theorem hashInR (hz : Sz p) (hK : SG p σ) (hc : Ctx p σ t) (hr : HRegs σ t) :
    HashIn p.n t (σ.gpr .x7) [.scr Layout.oSkPrf, .reg .x24] (.reg .x25) p.n := by
  have hn := hz.n32
  have hsig : p.n ≤ p.sigLen := by simp only [Params.sigLen]; exact Nat.le_mul_of_pos_left _ (by omega)
  have e25 : argVal t (.reg .x25) = σ.gpr .x6 + BitVec.ofNat 64 0 := by
    rw [BitVec.add_zero]; exact hr.x25
  have eS : ∀ o, argVal t (.scr o) = at' (σ.gpr .x7) o := fun o => by simp only [argVal, hc.x19]
  refine ⟨ks_of hK hc, fun x hx => ?_, by simp; omega,
    pieceIn_scr hK hc (by simp only [Layout.oHdr, Layout.oStream, Layout.oTop]; omega),
    by rw [hr.x22, hr.x23]; exact pieceIn_out hc hK.ctx_scr hK.stk_ctx (by rw [hK.rd]; simp),
    by rw [hr.x20, hr.x21]; exact pieceIn_out hc hK.msg_scr hK.stk_msg (by rw [hK.rd]; simp),
    ⟨by decide, by decide, by decide⟩, by rw [e25]; exact pieceOut_sig hK hc (by omega), by omega⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨show Layout.oSkPrf < 4096 by decide, by rw [eS]; exact pieceIn_scr hK hc (by
        simp only [Layout.oSkPrf, Layout.oKeys, Layout.oStream]; omega)⟩
    · exact ⟨⟨by decide, by decide, by decide⟩, by
        show PieceIn t _ (t.gpr .x24) p.n
        rw [hr.x24]; exact pieceIn_out hc hK.rnd_scr hK.stk_rnd (by rw [hK.rd]; simp)⟩

/-- `R` to the signature's first `n` bytes. -/
theorem hashR_ok (hz : Sz p) (v : Proof.Sha3.AArch64.Permutation) {f : Impl.SlhDsa.AArch64.Shake.Fns}
    (hv : f.keccak = v.callee) (hK : SG p σ) (hc : Ctx p σ t) (hr : HRegs σ t) :
    WP isa (Impl.SlhDsa.AArch64.Shake.hashM' p f [.scr Layout.oSkPrf, .reg .x24] (.reg .x25) p.n) t fun t' =>
      Ctx p σ t' ∧ HRegs σ t' ∧ bytesAt t'.mem (σ.gpr .x6) p.n = Rv p σ := by
  have hn := hz.n32
  have hsig : p.n ≤ p.sigLen := by simp only [Params.sigLen]; exact Nat.le_mul_of_pos_left _ (by omega)
  have e25 : argVal t (.reg .x25) = σ.gpr .x6 + BitVec.ofNat 64 0 := by
    rw [BitVec.add_zero]; exact hr.x25
  have eS : ∀ o, argVal t (.scr o) = at' (σ.gpr .x7) o := fun o => by simp only [argVal, hc.x19]
  refine WP.mono (hashM_ok p hn v hv (hashInR hz hK hc hr)) fun t' ⟨hk, hb⟩ => ?_
  rw [e25] at hk hb
  refine ⟨ctx_kept hz hK hc (.inr (.inl (Offset.sub_base _ (by omega)))) hk, hregs_kept hr hk, ?_⟩
  rw [← BitVec.add_zero (σ.gpr .x6), hb, Rv, ← mprime_eq hK hc hr]
  simp only [hashMsg, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, eS]
  rw [show argVal t (.reg .x24) = t.gpr .x24 from rfl, hr.x24,
    hc.bytes_out (by have := hK.f_rnd; omega) hK.rnd_scr hK.rnd_sig hK.stk_rnd.symm,
    show Layout.oSkPrf = Layout.oKeys + 32 * 1 from rfl, hc.keys 1 (by decide), key_chunk p σ (by decide)]
  simp only [List.append_assoc]

/-- What the hash of the digest needs. -/
theorem hashInD (hz : Sz p) (hm : p.m ≤ 64) (hK : SG p σ) (hc : Ctx p σ t) (hr : HRegs σ t) :
    HashIn p.n t (σ.gpr .x7) [.reg .x25, .scr Layout.oPkSeed, .scr Layout.oPkRoot] (.scr Layout.oDigest) p.m := by
  have hn := hz.n32
  have hsig : p.n ≤ p.sigLen := by simp only [Params.sigLen]; exact Nat.le_mul_of_pos_left _ (by omega)
  have eS : ∀ o, argVal t (.scr o) = at' (σ.gpr .x7) o := fun o => by simp only [argVal, hc.x19]
  have eD : Layout.oDigest = 1792 := rfl
  have hfr : Free p σ ⟨at' (σ.gpr .x7) Layout.oDigest, p.m⟩ :=
    .inl ⟨Offset.sub_base _ (by simp only [scratchLen]; omega), Offset.disjoint _ (by simp only [Layout.oTop]; omega)
      (by omega) (by simp only [Layout.oTop]; omega)⟩
  refine ⟨ks_of hK hc, fun x hx => ?_, by simp; omega,
    pieceIn_scr hK hc (by simp only [Layout.oHdr, Layout.oStream, Layout.oTop]; omega),
    by rw [hr.x22, hr.x23]; exact pieceIn_out hc hK.ctx_scr hK.stk_ctx (by rw [hK.rd]; simp),
    by rw [hr.x20, hr.x21]; exact pieceIn_out hc hK.msg_scr hK.stk_msg (by rw [hK.rd]; simp),
    show Layout.oDigest < 4096 by decide,
    by rw [eS]; exact pieceOut_scr hK hc (by simp only [Layout.oStream]; omega), by omega⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
      show PieceIn t _ (t.gpr .x25) p.n
      rw [hr.x25]
      have hs : Region.Sub ⟨σ.gpr .x6, p.n⟩ (SIG p σ) := Region.sub_prefix hsig
      exact ⟨(hK.sig_scr.sub_left hs).sub_right (stream_sub σ (Nat.le_refl _) (by omega)),
        (hK.sig_scr.sub_left hs).sub_right (stream_sub σ (by omega) (by omega)),
        by rw [stk_eq hc]; exact hK.stk_sig.sub_right hs, by
          rw [hc.rd, hc.wr, hK.rd, hK.wr]
          refine Covers.of_sub fun r hr => ?_
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), 0, by simp, by simpa using hsig⟩⟩
    · exact ⟨show Layout.oPkSeed < 4096 by decide, by rw [eS]; exact pieceIn_scr hK hc (by
        simp only [Layout.oPkSeed, Layout.oKeys, Layout.oStream]; omega)⟩
    · exact ⟨show Layout.oPkRoot < 4096 by decide, by rw [eS]; exact pieceIn_scr hK hc (by
        simp only [Layout.oPkRoot, Layout.oKeys, Layout.oStream]; omega)⟩

/-- The digest to `oDigest`. -/
theorem hashD_ok (hz : Sz p) (hm : p.m ≤ 64) (v : Proof.Sha3.AArch64.Permutation) {f : Impl.SlhDsa.AArch64.Shake.Fns}
    (hv : f.keccak = v.callee) (hK : SG p σ) (hc : Ctx p σ t) (hr : HRegs σ t)
    (hR : bytesAt t.mem (σ.gpr .x6) p.n = Rv p σ) :
    WP isa (Impl.SlhDsa.AArch64.Shake.hashM' p f [.reg .x25, .scr Layout.oPkSeed, .scr Layout.oPkRoot]
      (.scr Layout.oDigest) p.m) t fun t' =>
      Ctx p σ t' ∧ HRegs σ t' ∧ bytesAt t'.mem (σ.gpr .x6) p.n = Rv p σ ∧
        bytesAt t'.mem (at' (σ.gpr .x7) Layout.oDigest) p.m = Dv p σ := by
  have hn := hz.n32
  have hsig : p.n ≤ p.sigLen := by simp only [Params.sigLen]; exact Nat.le_mul_of_pos_left _ (by omega)
  have eS : ∀ o, argVal t (.scr o) = at' (σ.gpr .x7) o := fun o => by simp only [argVal, hc.x19]
  have eD : Layout.oDigest = 1792 := rfl
  have hfr : Free p σ ⟨at' (σ.gpr .x7) Layout.oDigest, p.m⟩ :=
    .inl ⟨Offset.sub_base _ (by simp only [scratchLen]; omega), Offset.disjoint _ (by simp only [Layout.oTop]; omega)
      (by omega) (by simp only [Layout.oTop]; omega)⟩
  refine WP.mono (hashM_ok p hn v hv (hashInD hz hm hK hc hr)) fun t' ⟨hk, hb⟩ => ?_
  rw [eS] at hk hb
  refine ⟨ctx_kept hz hK hc hfr hk, hregs_kept hr hk, ?_, ?_⟩
  · rw [bytesAt_frame hk.frame (fun r hr => ?_) (by omega), hR]
    simp only [hashR, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    have hs : Region.Sub ⟨σ.gpr .x6, p.n⟩ (SIG p σ) := Region.sub_prefix hsig
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact (hK.sig_scr.sub_left hs).sub_right (stream_sub σ (Nat.le_refl _) (by omega))
    · exact (hK.sig_scr.sub_left hs).sub_right (stream_sub σ (by omega) (by omega))
    · rw [hc.sp]; exact hK.stk_sig.symm.sub_left hs
    · exact (hK.sig_scr.sub_left hs).sub_right (Offset.sub_base _ (by simp only [scratchLen]; omega))
  · rw [hb, Dv, ← mprime_eq hK hc hr]
    simp only [hashMsg, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, eS]
    rw [show argVal t (.reg .x25) = t.gpr .x25 from rfl, hr.x25, hR,
      show Layout.oPkSeed = Layout.oKeys + 32 * 2 from rfl, hc.keys 2 (by decide), key_chunk p σ (by decide),
      show Layout.oPkRoot = Layout.oKeys + 32 * 3 from rfl, hc.keys 3 (by decide), key_chunk p σ (by decide)]
    simp only [List.append_assoc]

end

end VG.Proof.SlhDsa.AArch64.Sign
