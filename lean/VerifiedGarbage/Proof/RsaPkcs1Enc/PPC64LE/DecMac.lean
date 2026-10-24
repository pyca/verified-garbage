module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecHash
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Init
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Finalize
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers

/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: the calls of HMAC-SHA-256

The calls of HMAC-SHA-256's `init` (`macInit_call`) and `finalize`
(`macFin_call`), and of SHA-256's `update` (`upd_call`), with the HMAC
states at `scratch + sSt` and `scratch + sOuter` and the working space at
`scratch + sWork`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK initG finG)

theorem init_fd : H.init.fdepth ≤ 2 := by
  have := VG.Proof.Hmac.Stream.PPC64LE.Init.initMain_fdepth hH
  simp only [Hash.init, Code.fdepth, Nat.max_le]; omega

theorem init_pf : pushFrames H.init = true := by
  simp [Hash.init, pushFrames, Instr.isPush, VG.Proof.Hmac.Stream.PPC64LE.Init.initMain_pf hH]

theorem fin_fd : H.finalize.fdepth ≤ 2 := by
  have := VG.Proof.Hmac.Stream.PPC64LE.Finalize.finalizeMain_fdepth hH
  simp only [Hash.finalize, Code.fdepth, Nat.max_le]; omega

theorem fin_pf : pushFrames H.finalize = true := by
  simp [Hash.finalize, pushFrames, Instr.isPush, VG.Proof.Hmac.Stream.PPC64LE.Finalize.finalizeMain_pf hH]

theorem init_ok : ∀ s, (initG hH.SH (H.W + 48) 96).pre s → ∃ t s', Exec isa H.init s t s' ∧
    abiPreserved s s' ∧ (initG hH.SH (H.W + 48) 96).post s s' := fun _ hs => by
  obtain ⟨t, s', he, h₁, h₂⟩ := VG.Proof.Hmac.Stream.PPC64LE.Init.correct hH hs
  exact ⟨t, s', he, h₁, h₂⟩

theorem fin_ok : ∀ s, (finG hH.SH (H.W + 48 + H.FD) 96).pre s → ∃ t s', Exec isa H.finalize s t s' ∧
    abiPreserved s s' ∧ (finG hH.SH (H.W + 48 + H.FD) 96).post s s' := fun _ hs => by
  obtain ⟨t, s', he, h₁, h₂⟩ := VG.Proof.Hmac.Stream.PPC64LE.Finalize.correct hH hs
  exact ⟨t, s', he, h₁, h₂⟩

/-- `blockKey` of a key of at most a block is a block. -/
theorem blockKey_length {key : List Byte} (h : key.length ≤ 64) :
    (Spec.Hmac.blockKey Spec.Hmac.sha256 key).length = 64 := by
  have : ¬ (64 < key.length) := by omega
  simp only [Spec.Hmac.blockKey, Spec.Hmac.sha256, this, ite_false, List.length_append, List.length_replicate]
  omega

section
variable {s : State} (h : DPre s) {R : BitVec 64} {EM : List Byte}
include h

/-- HMAC's `init`, keyed with the 32 bytes at `scratch + key`. -/
theorem macInit_call {t : State} (hc : Post s R EM t) {key : Nat} (hk₁ : 400 ≤ key) (hk₂ : key + 32 ≤ scrBytes)
    (h3 : t.gpr .r3 = scA s sSt) (h4 : t.gpr .r4 = scA s sOuter) (h5 : t.gpr .r5 = scA s key)
    (h6 : t.gpr .r6 = BitVec.ofNat 64 32) (h7 : t.gpr .r7 = scA s sWork) {Q : State → Prop}
    (hQ : ∀ u, Post s R EM u →
      hH.SH.Repr u.mem (scA s sSt)
        (Spec.Hmac.xorPad (Spec.Hmac.blockKey hH.SH.H (Spec.Sha256.bytesAt t.mem (scA s key) 32)) Spec.Hmac.ipad) →
      hH.SH.Repr u.mem (scA s sOuter)
        (Spec.Hmac.xorPad (Spec.Hmac.blockKey hH.SH.H (Spec.Sha256.bytesAt t.mem (scA s key) 32)) Spec.Hmac.opad) →
      Frame ([⟨scA s sSt, H.S⟩, ⟨scA s sOuter, H.S⟩, ⟨scA s sWork, H.W + 48⟩] ++ [below (fb s) 96]) t.mem u.mem →
      Q u) :
    WP isa macInitCall t Q := by
  have hs : 96 ≤ t.sp.toNat := by rw [hc.sp]; have := fb_ge h; omega
  have e₁ : H.S = 96 := rfl
  have e₂ : H.W = 160 := rfl
  have e₃ : H.D = 32 := rfl
  have e₄ : H.FD = 32 := rfl
  have c3 : t.callEntry.gpr .r3 = scA s sSt := (State.callEntry_gpr _ (by decide)).trans h3
  have c4 : t.callEntry.gpr .r4 = scA s sOuter := (State.callEntry_gpr _ (by decide)).trans h4
  have c5 : t.callEntry.gpr .r5 = scA s key := (State.callEntry_gpr _ (by decide)).trans h5
  have c6 : t.callEntry.gpr .r6 = BitVec.ofNat 64 32 := (State.callEntry_gpr _ (by decide)).trans h6
  have c7 : t.callEntry.gpr .r7 = scA s sWork := (State.callEntry_gpr _ (by decide)).trans h7
  have hb : ∀ {a l : Nat}, a + l ≤ scrBytes → (below t.sp 96).Disjoint ⟨scA s a, l⟩ := fun ha => by
    rw [hc.sp]; exact lowD h (by decide) ha
  refine WP.callF (k := initG hH.SH (H.W + 48) 96) init_ok (rd := [⟨scA s key, 32⟩])
    (wr := [⟨scA s sSt, H.S⟩, ⟨scA s sOuter, H.S⟩, ⟨scA s sWork, H.W + 48⟩]) ?_
    (Covers.append_left (scCovR h hc.wr hk₂) ((scCovR h hc.wr (a := sSt) (n := H.S) (by decide)).cons
      ((scCovR h hc.wr (a := sOuter) (n := H.S) (by decide)).cons
        (scCovR h hc.wr (a := sWork) (n := H.W + 48) (by decide)))))
    ((scCov h hc.wr (a := sSt) (n := H.S) (by decide)).cons ((scCov h hc.wr (a := sOuter) (n := H.S) (by decide)).cons
      (scCov h hc.wr (a := sWork) (n := H.W + 48) (by decide))))
    (fun u hrd hwr hsp hf hcs hpost => ?_) (by have := init_fd; omega) init_pf
  · simp only [initG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp, c3, c4, c5, c6, c7, hH.hS]
    exact ⟨by decide, rfl, trivial, scD h (by decide) (by decide) (by decide), scD h (by decide) (by decide) (by decide),
      scD h (by decide) (by decide) (by decide), scD h (.inr (by unfold sSt; omega)) hk₂ (by decide),
      scD h (.inr (by unfold sOuter; omega)) hk₂ (by decide), scD h (.inr (by unfold sWork; omega)) hk₂ (by decide), hs,
      hb (by decide), hb (by decide), hb hk₂, hb (by decide)⟩
  · simp only [initG, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c3, c4, c5, c6] at hpost
    have hf' : Frame ([⟨scA s sSt, H.S⟩, ⟨scA s sOuter, H.S⟩, ⟨scA s sWork, H.W + 48⟩] ++ [below t.sp 96]) t.mem
        u.mem := Frame.below_mono hf (by have := init_fd; omega) (by omega)
    refine hQ u ?_ hpost.1 hpost.2 (by rw [← hc.sp]; exact hf')
    exact hc.call h hrd hwr hsp hcs (by decide) hf' fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact scSub (by decide)

/-- HMAC's `finalize`, to `scratch + o`. -/
theorem macFin_call {t : State} (hc : Post s R EM t) {o : Nat} (ho₁ : 432 ≤ o) (ho₂ : o + 32 ≤ scrBytes)
    (h3 : t.gpr .r3 = scA s sSt) (h4 : t.gpr .r4 = scA s sOuter) (h6 : t.gpr .r6 = scA s o)
    (h7 : t.gpr .r7 = scA s sWork) {Q : State → Prop}
    (hQ : ∀ u, Post s R EM u →
      (∀ k0 text, k0.length = 64 → k0.length + text.length < 2 ^ 64 →
        hH.SH.Repr t.mem (scA s sSt) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad ++ text) →
        t.gpr .r5 = BitVec.ofNat 64 (64 + text.length) →
        hH.SH.Repr t.mem (scA s sOuter) (Spec.Hmac.xorPad k0 Spec.Hmac.opad) →
        Spec.Sha256.bytesAt u.mem (scA s o) 32 = Spec.Hmac.hmacBlockKey hH.SH.H k0 text) →
      Frame ([⟨scA s sSt, H.S⟩, ⟨scA s o, H.D⟩, ⟨scA s sWork, H.W + 48 + H.FD⟩] ++ [below (fb s) 96]) t.mem u.mem →
      Q u) :
    WP isa macFinCall t Q := by
  have hs : 96 ≤ t.sp.toNat := by rw [hc.sp]; have := fb_ge h; omega
  have e₁ : H.S = 96 := rfl
  have e₂ : H.W = 160 := rfl
  have e₃ : H.D = 32 := rfl
  have e₄ : H.FD = 32 := rfl
  have c3 : t.callEntry.gpr .r3 = scA s sSt := (State.callEntry_gpr _ (by decide)).trans h3
  have c4 : t.callEntry.gpr .r4 = scA s sOuter := (State.callEntry_gpr _ (by decide)).trans h4
  have c5 : t.callEntry.gpr .r5 = t.gpr .r5 := State.callEntry_gpr _ (by decide)
  have c6 : t.callEntry.gpr .r6 = scA s o := (State.callEntry_gpr _ (by decide)).trans h6
  have c7 : t.callEntry.gpr .r7 = scA s sWork := (State.callEntry_gpr _ (by decide)).trans h7
  have hb : ∀ {a l : Nat}, a + l ≤ scrBytes → (below t.sp 96).Disjoint ⟨scA s a, l⟩ := fun ha => by
    rw [hc.sp]; exact lowD h (by decide) ha
  refine WP.callF (k := finG hH.SH (H.W + 48 + H.FD) 96) fin_ok (rd := [⟨scA s sOuter, H.S⟩])
    (wr := [⟨scA s sSt, H.S⟩, ⟨scA s o, H.D⟩, ⟨scA s sWork, H.W + 48 + H.FD⟩]) ?_
    (Covers.append_left (scCovR h hc.wr (a := sOuter) (n := H.S) (by decide))
      ((scCovR h hc.wr (a := sSt) (n := H.S) (by decide)).cons ((scCovR h hc.wr (a := o) (n := H.D) ho₂).cons
        (scCovR h hc.wr (a := sWork) (n := H.W + 48 + H.FD) (by decide)))))
    ((scCov h hc.wr (a := sSt) (n := H.S) (by decide)).cons ((scCov h hc.wr (a := o) (n := H.D) ho₂).cons
      (scCov h hc.wr (a := sWork) (n := H.W + 48 + H.FD) (by decide))))
    (fun u hrd hwr hsp hf hcs hpost => ?_) (by have := fin_fd; omega) fin_pf
  · simp only [finG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp, c3, c4, c6, c7, hH.hS, hH.hD]
    exact ⟨trivial, trivial, scD h (by decide) (by decide) (by decide), scD h (by unfold sSt; omega) (by decide) ho₂,
      scD h (by decide) (by decide) (by decide), scD h (by unfold sOuter; omega) (by decide) ho₂,
      scD h (by decide) (by decide) (by decide), scD h (.inr (by unfold sWork; omega)) ho₂ (by decide), hs,
      hb (by decide), hb (by decide), hb ho₂, hb (by decide)⟩
  · simp only [finG, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c3, c4, c5, c6] at hpost
    have hf' : Frame ([⟨scA s sSt, H.S⟩, ⟨scA s o, H.D⟩, ⟨scA s sWork, H.W + 48 + H.FD⟩] ++ [below t.sp 96]) t.mem
        u.mem := Frame.below_mono hf (by have := fin_fd; omega) (by omega)
    refine hQ u ?_ hpost (by rw [← hc.sp]; exact hf')
    exact hc.call h hrd hwr hsp hcs (by decide) hf' fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact scSub (by decide)
      · exact scSub ho₂
      · exact scSub (by decide)

/-- SHA-256's `update` of the inner state with the `len` bytes at `dat`. -/
theorem upd_call {t : State} (hc : Post s R EM t) {dat : Addr} {len : Nat} (h3 : t.gpr .r3 = scA s sSt)
    (h5 : t.gpr .r5 = dat) (h6 : (t.gpr .r6).toNat = len) (h7 : t.gpr .r7 = scA s sWork)
    (d₁ : Region.Disjoint ⟨dat, len⟩ ⟨scA s sSt, H.S⟩) (d₂ : Region.Disjoint ⟨dat, len⟩ ⟨scA s sWork, H.W⟩)
    (d₃ : (below (fb s) 48).Disjoint ⟨dat, len⟩) (hcv : Covers [⟨dat, len⟩] (t.rd ++ t.wr)) {Q : State → Prop}
    (hQ : ∀ u, Post s R EM u →
      (∀ m, hH.SH.Repr t.mem (scA s sSt) m → t.gpr .r4 = BitVec.ofNat 64 m.length →
        hH.SH.Repr u.mem (scA s sSt) (m ++ Spec.Rsa.bytesAt t.mem dat len)) →
      Frame ([⟨scA s sSt, H.S⟩, ⟨scA s sWork, H.W⟩] ++ [below (fb s) 48]) t.mem u.mem → Q u) :
    WP isa updCall t Q := by
  have hs : 48 ≤ t.sp.toNat := by rw [hc.sp]; have := fb_ge h; omega
  refine hH.callUpd_ok h3 h5 h6 h7 (scD h (by decide) (by decide) (by decide)) d₁ d₂ hs
    (by rw [hc.sp]; exact lowD h (by decide) (by decide)) (by rw [hc.sp]; exact d₃)
    (by rw [hc.sp]; exact lowD h (by decide) (by decide))
    (Covers.append_left hcv (Covers.pair (scCovR h hc.wr (by decide)) (scCovR h hc.wr (by decide))))
    (Covers.pair (scCov h hc.wr (by decide)) (scCov h hc.wr (by decide)))
    fun u hrd hwr hsp hf hcs hr => hQ u ?_ hr (by rw [← hc.sp]; exact hf)
  exact hc.call h hrd hwr hsp hcs (by decide) hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact scSub (by decide)

end

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec
