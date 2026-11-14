module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecD
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha256
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Init
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Finalize
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Common

/-! ### `RsaPkcs1Enc.PPC64LE.DecMac`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.PPC64LE.DecHash`, which only this module used -/

section

/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: `DH = SHA256(D)`

The calls of SHA-256's streaming `init`, `update` and `finalize` on `D`
(`hashD_ok`, from `DB` to `DH`), and what any call working in `scratch`
leaves (`Post.call`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
open VG.Proof.Bignum.PPC64LE (Keep)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)

variable {pc : Bool}

/-- SHA-256's streaming functions, and the facts about them. -/
abbrev H : VG.Impl.Hmac.Stream.PPC64LE.Hash := VG.Proof.Hmac.Stream.PPC64LE.Sha256.hash
abbrev hH : HashOK H := VG.Proof.Hmac.Stream.PPC64LE.Sha256.ok

theorem fb_ge {s : State} (h : DPre pc s) : 3328 ≤ (fb s).toNat := by
  have := fb_toNat h; have := h.sp1; unfold stackBytes frameBytes Impl.Rsa.PPC64LE.Priv.frameBytes at *; omega_arith

/-- The stack below our frame misses `scratch`. -/
theorem lowD {s : State} (h : DPre pc s) {n : Nat} (hn : n ≤ Impl.Rsa.PPC64LE.Priv.frameBytes) {a l : Nat}
    (ha : a + l ≤ scrBytes) : (below (fb s) n).Disjoint ⟨scA s a, l⟩ :=
  (h.ks.sub_left (sub_trans (low_sub s hn) (callee_sub s))).sub_right (sub_trans (scSub ha) (sc_sub h))

theorem scCovR {s u : State} (h : DPre pc s) (hwr : u.wr = fr s :: s.wr) {a n : Nat} (ha : a + n ≤ scrBytes) :
    Covers [⟨scA s a, n⟩] (u.rd ++ u.wr) :=
  Covers.right (scCov h hwr ha)

theorem bytes_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {len : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, len⟩ r) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p len = Spec.Rsa.bytesAt m p len := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) hd hl (List.mem_range.mp hi)

/-- What a call working in `scratch`, on the stack below our frame, leaves. -/
theorem Post.call {s : State} (h : DPre pc s) {R : BitVec 64} {EM : List Byte} {t t' : State}
    (hc : Post s R EM t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hg : ∀ r ∈ preserved, t'.gpr r = t.gpr r) {ws : List Region} {n : Nat}
    (hn : n ≤ Impl.Rsa.PPC64LE.Priv.frameBytes) (hf : Frame (ws ++ [below t.sp n]) t.mem t'.mem)
    (hs : ∀ r ∈ ws, Region.Sub r (SC s)) : Post s R EM t' :=
  hc.step h hrd hwr hsp hg hf fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact .inl (hs r hr)
    · rw [List.mem_singleton.mp hr, hc.sp]; exact .inr (.inl (low_sub s hn))

/-- A range of `scratch` that a call working elsewhere in `scratch`, on the
stack below our frame, leaves as it was. -/
theorem keep_call {s : State} (h : DPre pc s) {m m' : Mem} {ws : List Region} {n : Nat}
    (hn : n ≤ Impl.Rsa.PPC64LE.Priv.frameBytes) (hf : Frame (ws ++ [below (fb s) n]) m m') {a l : Nat}
    (ha : a + l ≤ scrBytes) (hs : ∀ r ∈ ws, Region.Disjoint ⟨scA s a, l⟩ r) :
    Spec.Rsa.bytesAt m' (scA s a) l = Spec.Rsa.bytesAt m (scA s a) l :=
  bytes_frame hf (fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact hs r hr
    · rw [List.mem_singleton.mp hr]; exact (lowD h hn ha).symm) (by unfold scrBytes at ha; omega_using [ha])

/-- After `hashD`: `DH = SHA256(D)` at `scratch + sDH`. -/
structure DHS (s : State) (R : BitVec 64) (EM : List Byte) (t : State) : Prop where
  post : Post s R EM t
  dh : Spec.Rsa.bytesAt t.mem (scA s sDH) 32 =
    Spec.Sha256.hash (Spec.Rsa.i2osp (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat))
      (s.gpr .r7).toNat)

theorem slot_rd {s : State} {R : BitVec 64} {EM : List Byte} {t : State} (hc : Post s R EM t) {d : Nat}
    (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ frameBytes) : InRegions (t.rd ++ t.wr) (fb s + BitVec.ofNat 64 d) 8 :=
  slotIn hc.wr h₁ h₂

theorem shaInitArgs_ok {s : State} {R : BitVec 64} {EM : List Byte} {t : State} (hc : Post s R EM t) :
    WP isa (.block shaInitArgs) t fun u => (u.mem = t.mem ∧ u.gpr .r3 = scA s sSt) ∧ Keep [.r12, .r3] t u := by
  have c1 : oScr < 2 ^ 15 ∧ oScr % 4 = 0 := by decide
  have c2 : sSt < 2 ^ 15 := by decide
  have i1 := slot_rd hc (d := oScr) (by decide) (by decide)
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  unfold shaInitArgs scr
  prun [fp, exec_addSp0, hc.sp, c1, c2, i1, hc.sl.scr, exec_addi (show Reg.r3 ≠ .r0 by decide) c2]

theorem shaUpdArgs_ok {s : State} {R : BitVec 64} {EM : List Byte} {t : State} (hc : Post s R EM t) :
    WP isa (.block shaUpdArgs) t fun u => (u.mem = t.mem ∧ u.gpr .r3 = scA s sSt ∧ u.gpr .r4 = 0 ∧
      u.gpr .r5 = scA s sD ∧ u.gpr .r6 = s.gpr .r7 ∧ u.gpr .r7 = scA s sWork) ∧
      Keep [.r12, .r3, .r4, .r5, .r6, .r7] t u := by
  have c1 : oScr < 2 ^ 15 ∧ oScr % 4 = 0 := by decide
  have c2 : oK < 2 ^ 15 ∧ oK % 4 = 0 := by decide
  have c3 : sSt < 2 ^ 15 := by decide
  have c4 : sD < 2 ^ 15 := by decide
  have c5 : sWork < 2 ^ 15 := by decide
  have i1 := slot_rd hc (d := oScr) (by decide) (by decide)
  have i2 := slot_rd hc (d := oK) (by decide) (by decide)
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  unfold shaUpdArgs scr
  prun [fp, exec_addSp0, hc.sp, c1, c2, c3, c4, c5, i1, i2, hc.sl.scr, hc.sl.k,
    exec_addi (show Reg.r3 ≠ .r0 by decide) c3, exec_addi (show Reg.r5 ≠ .r0 by decide) c4,
    exec_addi (show Reg.r7 ≠ .r0 by decide) c5]
  rfl

theorem shaFinArgs_ok {s : State} {R : BitVec 64} {EM : List Byte} {t : State} (hc : Post s R EM t) :
    WP isa (.block shaFinArgs) t fun u => (u.mem = t.mem ∧ u.gpr .r3 = scA s sSt ∧ u.gpr .r4 = s.gpr .r7 ∧
      u.gpr .r5 = scA s sDH ∧ u.gpr .r6 = scA s sWork) ∧ Keep [.r12, .r3, .r4, .r5, .r6] t u := by
  have c1 : oScr < 2 ^ 15 ∧ oScr % 4 = 0 := by decide
  have c2 : oK < 2 ^ 15 ∧ oK % 4 = 0 := by decide
  have c3 : sSt < 2 ^ 15 := by decide
  have c4 : sDH < 2 ^ 15 := by decide
  have c5 : sWork < 2 ^ 15 := by decide
  have i1 := slot_rd hc (d := oScr) (by decide) (by decide)
  have i2 := slot_rd hc (d := oK) (by decide) (by decide)
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  unfold shaFinArgs scr
  prun [fp, exec_addSp0, hc.sp, c1, c2, c3, c4, c5, i1, i2, hc.sl.scr, hc.sl.k,
    exec_addi (show Reg.r3 ≠ .r0 by decide) c3, exec_addi (show Reg.r5 ≠ .r0 by decide) c4,
    exec_addi (show Reg.r6 ≠ .r0 by decide) c5]

section
variable {s : State} (h : DPre pc s) {R : BitVec 64} {EM : List Byte}
include h

theorem init_step {t : State} (hc : Post s R EM t) {rest : Prog isa} {Q : State → Prop}
    (hQ : ∀ u, Post s R EM u → hH.SH.Repr u.mem (scA s sSt) [] →
      Frame ([⟨scA s sSt, H.S⟩] ++ [below (fb s) 48]) t.mem u.mem → WP isa rest u Q) :
    WP isa (.seq (.block shaInitArgs) (.seq initCall rest)) t Q := by
  refine WP.seq (WP.mono (shaInitArgs_ok hc) fun u ⟨⟨um, u3⟩, ku⟩ => ?_)
  have hu : Post s R EM u := hc.regs ku.rd ku.wr ku.sp um fun r hr => ku.gpr r (by revert r; decide)
  have hs : 48 ≤ u.sp.toNat := by rw [hu.sp]; have := fb_ge h; omega_using [this]
  refine WP.seq <| hH.callInit_ok u3 ⟨hs, by rw [hu.sp]; exact lowD h (by decide) (by decide)⟩
    (scCovR h hu.wr (by decide)) (scCov h hu.wr (by decide))
    fun v hrd hwr hsp hf hcs hr => hQ v ?_ hr (by rw [← um, ← hu.sp]; exact hf)
  exact hu.call h hrd hwr hsp hcs (by decide) hf fun r hr => by
    rw [List.mem_singleton.mp hr]; exact scSub (by decide)

theorem upd_step {t : State} (hc : Post s R EM t) {rest : Prog isa} {Q : State → Prop}
    (hQ : ∀ u, Post s R EM u →
      (∀ m, hH.SH.Repr t.mem (scA s sSt) m → m.length = 0 →
        hH.SH.Repr u.mem (scA s sSt) (m ++ Spec.Rsa.bytesAt t.mem (scA s sD) (s.gpr .r7).toNat)) →
      Frame ([⟨scA s sSt, H.S⟩, ⟨scA s sWork, H.W⟩] ++ [below (fb s) 48]) t.mem u.mem → WP isa rest u Q) :
    WP isa (.seq (.block shaUpdArgs) (.seq updCall rest)) t Q := by
  have hk := h.k2
  refine WP.seq (WP.mono (shaUpdArgs_ok hc) fun u ⟨⟨um, u3, u4, u5, u6, u7⟩, ku⟩ => ?_)
  have hu : Post s R EM u := hc.regs ku.rd ku.wr ku.sp um fun r hr => ku.gpr r (by revert r; decide)
  have hs : 48 ≤ u.sp.toNat := by rw [hu.sp]; have := fb_ge h; omega_using [this]
  have lk : sD + (s.gpr .r7).toNat ≤ scrBytes := by unfold sD scrBytes; omega_using [hk]
  refine WP.seq <| hH.callUpd_ok (len := (s.gpr .r7).toNat) u3 u5 (by rw [u6]) u7 (scD h (by decide) (by decide) (by decide))
    (scD h (.inr (by decide)) lk (by decide)) (scD h (.inr (by decide)) lk (by decide)) hs
    (by rw [hu.sp]; exact lowD h (by decide) (by decide)) (by rw [hu.sp]; exact lowD h (by decide) lk)
    (by rw [hu.sp]; exact lowD h (by decide) (by decide))
    (Covers.append_left (scCovR h hu.wr lk) (Covers.pair (scCovR h hu.wr (by decide)) (scCovR h hu.wr (by decide))))
    (Covers.pair (scCov h hu.wr (by decide)) (scCov h hu.wr (by decide)))
    fun v hrd hwr hsp hf hcs hr => hQ v ?_ (fun m hm hl => ?_) (by rw [← um, ← hu.sp]; exact hf)
  · exact hu.call h hrd hwr hsp hcs (by decide) hf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact scSub (by decide)
      · exact scSub (by decide)
  · rw [← um]; exact hr m (um ▸ hm) (by rw [u4, hl]; rfl)

theorem fin_step {t : State} (hc : Post s R EM t) {Q : State → Prop}
    (hQ : ∀ u, Post s R EM u →
      (∀ m, hH.SH.Repr t.mem (scA s sSt) m → m.length = (s.gpr .r7).toNat →
        Spec.Rsa.bytesAt u.mem (scA s sDH) 32 = Spec.Sha256.hash m) → Q u) :
    WP isa (.seq (.block shaFinArgs) finCall) t Q := by
  have hk := h.k2
  refine WP.seq (WP.mono (shaFinArgs_ok hc) fun u ⟨⟨um, u3, u4, u5, u6⟩, ku⟩ => ?_)
  have hu : Post s R EM u := hc.regs ku.rd ku.wr ku.sp um fun r hr => ku.gpr r (by revert r; decide)
  have hs : 48 ≤ u.sp.toNat := by rw [hu.sp]; have := fb_ge h; omega_using [this]
  refine hH.callFin_ok u3 u5 u6 (scD h (by decide) (by decide) (by decide))
    (scD h (by decide) (by decide) (by decide)) (scD h (by decide) (by decide) (by decide)) hs
    (by rw [hu.sp]; exact lowD h (by decide) (by decide)) (by rw [hu.sp]; exact lowD h (by decide) (by decide))
    (by rw [hu.sp]; exact lowD h (by decide) (by decide))
    ((scCovR h hu.wr (a := sSt) (n := H.S) (by decide)).cons ((scCovR h hu.wr (a := sDH) (n := H.FD) (by decide)).cons
      (scCovR h hu.wr (a := sWork) (n := H.W) (by decide))))
    ((scCov h hu.wr (a := sSt) (n := H.S) (by decide)).cons ((scCov h hu.wr (a := sDH) (n := H.FD) (by decide)).cons
      (scCov h hu.wr (a := sWork) (n := H.W) (by decide))))
    fun v hrd hwr hsp hf hcs hr => hQ v ?_ fun m hm hl => ?_
  · exact hu.call h hrd hwr hsp hcs (by decide) hf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact scSub (by decide)
      · exact scSub (by decide)
      · exact scSub (by decide)
  · have e := hr m (um ▸ hm) (by rw [hl]; omega_using []) (by rw [u4, hl, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    show Spec.Sha256.bytesAt v.mem (scA s sDH) H.FD = _
    rw [e, ← List.take_of_length_le (l := hH.fh m) (i := H.D) (by rw [hH.fhLen]; decide)]
    exact (hH.hashTake m).symm

theorem hashD_ok {t : State} (hd : DB s R EM t) : WP isa hashD t (DHS s R EM) := by
  have hk := h.k2
  have lk : sD + (s.gpr .r7).toNat ≤ scrBytes := by unfold sD scrBytes; omega_using [hk]
  refine init_step h hd.post fun u hu hr hf => ?_
  have hD := (keep_call h (by decide) hf lk fun r hr => by
    rw [List.mem_singleton.mp hr]; exact scD h (.inr (by decide)) lk (by decide)).trans hd.D
  refine upd_step h hu fun v hv hr' _ => ?_
  refine fin_step h hv fun w hw hr'' => ⟨hw, ?_⟩
  rw [hr'' _ (hr' [] hr rfl) (by simp [Spec.Rsa.bytesAt]), List.nil_append, hD]

end

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

end

end


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

variable {pc : Bool}

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
  have : ¬ (64 < key.length) := by omega_using [h]
  simp only [Spec.Hmac.blockKey, Spec.Hmac.sha256, this, ite_false, List.length_append, List.length_replicate]
  omega_using [h]

section
variable {s : State} (h : DPre pc s) {R : BitVec 64} {EM : List Byte}
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
  have hs : 96 ≤ t.sp.toNat := by rw [hc.sp]; have := fb_ge h; omega_using [this]
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
    (fun u hrd hwr hsp hf hcs hpost => ?_) (by have := init_fd; omega_using [this]) init_pf
  · simp only [initG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp, c3, c4, c5, c6, c7, hH.hS]
    exact ⟨by decide, rfl, trivial, scD h (by decide) (by decide) (by decide), scD h (by decide) (by decide) (by decide),
      scD h (by decide) (by decide) (by decide), scD h (.inr (by unfold sSt; omega_using [hk₁, e₁])) hk₂ (by decide),
      scD h (.inr (by unfold sOuter; omega_using [hk₁, e₁])) hk₂ (by decide), scD h (.inr (by unfold sWork; omega_using [hk₁, e₂])) hk₂ (by decide), hs,
      hb (by decide), hb (by decide), hb hk₂, hb (by decide)⟩
  · simp only [initG, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c3, c4, c5, c6] at hpost
    have hf' : Frame ([⟨scA s sSt, H.S⟩, ⟨scA s sOuter, H.S⟩, ⟨scA s sWork, H.W + 48⟩] ++ [below t.sp 96]) t.mem
        u.mem := Frame.below_mono hf (by have := init_fd; omega_using [this]) (by omega_using [])
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
  have hs : 96 ≤ t.sp.toNat := by rw [hc.sp]; have := fb_ge h; omega_using [this]
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
    (fun u hrd hwr hsp hf hcs hpost => ?_) (by have := fin_fd; omega_using [this]) fin_pf
  · simp only [finG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp, c3, c4, c6, c7, hH.hS, hH.hD]
    exact ⟨trivial, trivial, scD h (by decide) (by decide) (by decide), scD h (by unfold sSt; omega_using [ho₁, e₁]) (by decide) ho₂,
      scD h (by decide) (by decide) (by decide), scD h (by unfold sOuter; omega_using [ho₁, e₁]) (by decide) ho₂,
      scD h (by decide) (by decide) (by decide), scD h (.inr (by unfold sWork; omega_using [ho₁, e₂, e₄])) ho₂ (by decide), hs,
      hb (by decide), hb (by decide), hb ho₂, hb (by decide)⟩
  · simp only [finG, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c3, c4, c5, c6] at hpost
    have hf' : Frame ([⟨scA s sSt, H.S⟩, ⟨scA s o, H.D⟩, ⟨scA s sWork, H.W + 48 + H.FD⟩] ++ [below t.sp 96]) t.mem
        u.mem := Frame.below_mono hf (by have := fin_fd; omega_using [this]) (by omega_using [])
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
  have hs : 48 ≤ t.sp.toNat := by rw [hc.sp]; have := fb_ge h; omega_using [this]
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

end

end


/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: `KDK = HMAC(DH, C)`

HMAC-SHA-256 keyed with `DH`, of the ciphertext, to `scratch + sKDK`
(`kdkMac_ok`, from `DHS` to `KD`), and the argument blocks of HMAC's `init`
for any key in `scratch` (`macInitArgs_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
open VG.Proof.Bignum.PPC64LE (Keep)

variable {pc : Bool}

/-- The ciphertext. -/
abbrev cOf (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 1) (s.gpr .r7).toNat

/-- The private exponent. -/
abbrev dOf (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat

/-- After `kdkMac`: `KDK` at `scratch + sKDK`. -/
structure KD (s : State) (R : BitVec 64) (EM : List Byte) (t : State) : Prop where
  post : Post s R EM t
  kdk : Spec.Rsa.bytesAt t.mem (scA s sKDK) 32 = Spec.RsaPkcs1Enc.kdk (s.gpr .r7).toNat (dOf s) (cOf s)

theorem xorPad_length (k : List Byte) (p : Byte) : (Spec.Hmac.xorPad k p).length = k.length := by
  simp [Spec.Hmac.xorPad]

section
variable {s : State} {R : BitVec 64} {EM : List Byte}

theorem macInitArgs_ok {t : State} (hc : Post s R EM t) {key : Nat} (hk : key < 2 ^ 15) :
    WP isa (.block (macInitArgs key)) t fun u => (u.mem = t.mem ∧ u.gpr .r3 = scA s sSt ∧
      u.gpr .r4 = scA s sOuter ∧ u.gpr .r5 = scA s key ∧ u.gpr .r6 = BitVec.ofNat 64 32 ∧
      u.gpr .r7 = scA s sWork) ∧ Keep [.r12, .r3, .r4, .r5, .r6, .r7] t u := by
  have c1 : oScr < 2 ^ 15 ∧ oScr % 4 = 0 := by decide
  have c2 : sSt < 2 ^ 15 := by decide
  have c3 : sOuter < 2 ^ 15 := by decide
  have c4 : sWork < 2 ^ 15 := by decide
  have i1 := slot_rd hc (d := oScr) (by decide) (by decide)
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  unfold macInitArgs scr
  prun [fp, exec_addSp0, hc.sp, c1, c2, c3, c4, hk, i1, hc.sl.scr, exec_addi (show Reg.r3 ≠ .r0 by decide) c2,
    exec_addi (show Reg.r4 ≠ .r0 by decide) c3, exec_addi (show Reg.r5 ≠ .r0 by decide) hk,
    exec_addi (show Reg.r7 ≠ .r0 by decide) c4]

theorem kdkUpdArgs_ok {t : State} (hc : Post s R EM t) :
    WP isa (.block kdkUpdArgs) t fun u => (u.mem = t.mem ∧ u.gpr .r3 = scA s sSt ∧
      u.gpr .r4 = BitVec.ofNat 64 64 ∧ u.gpr .r5 = stackArg s 1 ∧ u.gpr .r6 = s.gpr .r7 ∧
      u.gpr .r7 = scA s sWork) ∧ Keep [.r12, .r3, .r4, .r5, .r6, .r7] t u := by
  have c1 : oScr < 2 ^ 15 ∧ oScr % 4 = 0 := by decide
  have c2 : oIn < 2 ^ 15 ∧ oIn % 4 = 0 := by decide
  have c3 : oK < 2 ^ 15 ∧ oK % 4 = 0 := by decide
  have c4 : sSt < 2 ^ 15 := by decide
  have c5 : sWork < 2 ^ 15 := by decide
  have i1 := slot_rd hc (d := oScr) (by decide) (by decide)
  have i2 := slot_rd hc (d := oIn) (by decide) (by decide)
  have i3 := slot_rd hc (d := oK) (by decide) (by decide)
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  unfold kdkUpdArgs scr
  prun [fp, exec_addSp0, hc.sp, c1, c2, c3, c4, c5, i1, i2, i3, hc.sl.scr, hc.sl.inp, hc.sl.k,
    exec_addi (show Reg.r3 ≠ .r0 by decide) c4, exec_addi (show Reg.r7 ≠ .r0 by decide) c5]

theorem kdkFinArgs_ok {t : State} (hc : Post s R EM t) :
    WP isa (.block kdkFinArgs) t fun u => (u.mem = t.mem ∧ u.gpr .r3 = scA s sSt ∧
      u.gpr .r4 = scA s sOuter ∧ u.gpr .r5 = s.gpr .r7 + BitVec.ofNat 64 64 ∧ u.gpr .r6 = scA s sKDK ∧
      u.gpr .r7 = scA s sWork) ∧ Keep [.r12, .r3, .r4, .r5, .r6, .r7] t u := by
  have c1 : oScr < 2 ^ 15 ∧ oScr % 4 = 0 := by decide
  have c3 : oK < 2 ^ 15 ∧ oK % 4 = 0 := by decide
  have c4 : sSt < 2 ^ 15 := by decide
  have c5 : sWork < 2 ^ 15 := by decide
  have c6 : sOuter < 2 ^ 15 := by decide
  have c7 : sKDK < 2 ^ 15 := by decide
  have i1 := slot_rd hc (d := oScr) (by decide) (by decide)
  have i3 := slot_rd hc (d := oK) (by decide) (by decide)
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  unfold kdkFinArgs scr
  prun [fp, exec_addSp0, hc.sp, c1, c3, c4, c5, c6, c7, i1, i3, hc.sl.scr, hc.sl.k,
    exec_addi (show Reg.r3 ≠ .r0 by decide) c4, exec_addi (show Reg.r4 ≠ .r0 by decide) c6,
    exec_addi (show Reg.r5 ≠ .r0 by decide) (show 64 < 2 ^ 15 by decide),
    exec_addi (show Reg.r6 ≠ .r0 by decide) c7, exec_addi (show Reg.r7 ≠ .r0 by decide) c5]

end

section
variable {s : State} (h : DPre pc s) {R : BitVec 64} {EM : List Byte}
include h

/-- The ciphertext misses `scratch` and the stack. -/
theorem cR_eq : (⟨stackArg s 1, (s.gpr .r7).toNat⟩ : Region) = iR s := by simp only [iR, h.hi]

theorem c_sc {a l : Nat} (ha : a + l ≤ scrBytes) : Region.Disjoint ⟨stackArg s 1, (s.gpr .r7).toNat⟩ ⟨scA s a, l⟩ := by
  rw [cR_eq h]; exact (h.is.sub_right (sc_sub h)).sub_right (scSub ha)

theorem c_low {n : Nat} (hn : n ≤ Impl.Rsa.PPC64LE.Priv.frameBytes) :
    (below (fb s) n).Disjoint ⟨stackArg s 1, (s.gpr .r7).toNat⟩ := by
  rw [cR_eq h]; exact h.ki.sub_left (sub_trans (low_sub s hn) (callee_sub s))

theorem c_cov {t : State} (hc : Post s R EM t) : Covers [⟨stackArg s 1, (s.gpr .r7).toNat⟩] (t.rd ++ t.wr) := by
  rw [cR_eq h]
  exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, hc.rd, h.hrd]; simp)

theorem c_bytes {t : State} (hc : Post s R EM t) :
    Spec.Rsa.bytesAt t.mem (stackArg s 1) (s.gpr .r7).toNat = cOf s :=
  bytes_frame hc.mem (fun r hr => by
    rw [cR_eq h]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.ki.symm
    · exact h.oi.symm
    · exact h.is) (by have := h.k2; omega_using [])

theorem kdkMac_ok {t : State} (hd : DHS s R EM t) : WP isa kdkMac t (KD s R EM) := by
  have hk := h.k2
  have hK : sDH < 2 ^ 15 := by decide
  refine WP.seq (WP.mono (macInitArgs_ok hd.post hK) fun u ⟨⟨um, u3, u4, u5, u6, u7⟩, ku⟩ => ?_)
  have hu : Post s R EM u := hd.post.regs ku.rd ku.wr ku.sp um fun r hr => ku.gpr r (by revert r; decide)
  refine WP.seq (macInit_call h hu (by decide) (by decide) u3 u4 u5 u6 u7 fun v hv hI hO hf => ?_)
  refine WP.seq (WP.mono (kdkUpdArgs_ok hv) fun w ⟨⟨wm, w3, w4, w5, w6, w7⟩, kw⟩ => ?_)
  have hw : Post s R EM w := hv.regs kw.rd kw.wr kw.sp wm fun r hr => kw.gpr r (by revert r; decide)
  -- the key
  have k0l : (Spec.Hmac.blockKey hH.SH.H (Spec.Sha256.bytesAt u.mem (scA s sDH) 32)).length = 64 :=
    blockKey_length (by simp [Spec.Sha256.bytesAt])
  refine WP.seq (upd_call h hw w3 w5 (by rw [w6]) w7 (c_sc h (by decide)) (c_sc h (by decide)) (c_low h (by decide))
    (c_cov h hw) fun x hx hI' hf' => ?_)
  refine WP.seq (WP.mono (kdkFinArgs_ok hx) fun y ⟨⟨ym, y3, y4, y5, y6, y7⟩, ky⟩ => ?_)
  have hy : Post s R EM y := hx.regs ky.rd ky.wr ky.sp ym fun r hr => ky.gpr r (by revert r; decide)
  refine macFin_call h hy (by decide) (by decide) y3 y4 y6 y7 fun z hz hmac _ => ⟨hz, ?_⟩
  have hO' : hH.SH.Repr y.mem (scA s sOuter)
      (Spec.Hmac.xorPad (Spec.Hmac.blockKey hH.SH.H (Spec.Sha256.bytesAt u.mem (scA s sDH) 32)) Spec.Hmac.opad) := by
    rw [ym]
    refine hH.repr_keep hf' (by rw [xorPad_length, k0l]; rfl) (fun r hr => ?_) (wm ▸ hO)
    simp only [List.mem_cons, List.not_mem_nil, or_false, List.cons_append, List.nil_append] at hr
    rcases hr with rfl | rfl | rfl
    · exact scD h (by decide) (by decide) (by decide)
    · exact scD h (by decide) (by decide) (by decide)
    · exact (lowD h (by decide) (by decide)).symm
  have e := hmac _ (Spec.Rsa.bytesAt w.mem (stackArg s 1) (s.gpr .r7).toNat) k0l
    (by rw [k0l]; simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; omega_using [hk])
    (by rw [ym]; exact hI' _ (wm ▸ hI) (by rw [w4, xorPad_length, k0l]))
    (by
      rw [y5]; simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using []) hO'
  rw [c_bytes h hw, um] at e
  show Spec.Sha256.bytesAt z.mem (scA s sKDK) 32 = _
  rw [e]
  show Spec.Hmac.hmacBlockKey Spec.Hmac.sha256 (Spec.Hmac.blockKey Spec.Hmac.sha256 (Spec.Rsa.bytesAt t.mem (scA s sDH) 32))
    (cOf s) = _
  rw [hd.dh]; rfl

end

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec
