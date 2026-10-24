module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecD
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha256
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Covers

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

/-- SHA-256's streaming functions, and the facts about them. -/
abbrev H : VG.Impl.Hmac.Stream.PPC64LE.Hash := VG.Proof.Hmac.Stream.PPC64LE.Sha256.hash
abbrev hH : HashOK H := VG.Proof.Hmac.Stream.PPC64LE.Sha256.ok

theorem fb_ge {s : State} (h : DPre s) : 3328 ≤ (fb s).toNat := by
  have := fb_toNat h; have := h.sp1; unfold stackBytes frameBytes Impl.Rsa.PPC64LE.Priv.frameBytes at *; omega

/-- The stack below our frame misses `scratch`. -/
theorem lowD {s : State} (h : DPre s) {n : Nat} (hn : n ≤ Impl.Rsa.PPC64LE.Priv.frameBytes) {a l : Nat}
    (ha : a + l ≤ scrBytes) : (below (fb s) n).Disjoint ⟨scA s a, l⟩ :=
  (h.ks.sub_left (sub_trans (low_sub s hn) (callee_sub s))).sub_right (sub_trans (scSub ha) (sc_sub h))

theorem scCovR {s u : State} (h : DPre s) (hwr : u.wr = fr s :: s.wr) {a n : Nat} (ha : a + n ≤ scrBytes) :
    Covers [⟨scA s a, n⟩] (u.rd ++ u.wr) :=
  Covers.right (scCov h hwr ha)

theorem bytes_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {len : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, len⟩ r) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p len = Spec.Rsa.bytesAt m p len := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) hd hl (List.mem_range.mp hi)

/-- What a call working in `scratch`, on the stack below our frame, leaves. -/
theorem Post.call {s : State} (h : DPre s) {R : BitVec 64} {EM : List Byte} {t t' : State}
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
theorem keep_call {s : State} (h : DPre s) {m m' : Mem} {ws : List Region} {n : Nat}
    (hn : n ≤ Impl.Rsa.PPC64LE.Priv.frameBytes) (hf : Frame (ws ++ [below (fb s) n]) m m') {a l : Nat}
    (ha : a + l ≤ scrBytes) (hs : ∀ r ∈ ws, Region.Disjoint ⟨scA s a, l⟩ r) :
    Spec.Rsa.bytesAt m' (scA s a) l = Spec.Rsa.bytesAt m (scA s a) l :=
  bytes_frame hf (fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact hs r hr
    · rw [List.mem_singleton.mp hr]; exact (lowD h hn ha).symm) (by unfold scrBytes at ha; omega)

/-- After `hashD`: `DH = SHA256(D)` at `scratch + sDH`. -/
structure DHS (s : State) (R : BitVec 64) (EM : List Byte) (t : State) : Prop where
  post : Post s R EM t
  dh : Spec.Rsa.bytesAt t.mem (scA s sDH) 32 =
    Spec.Sha256.hash (Spec.Rsa.i2osp (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat))
      (s.gpr .r7).toNat)

theorem slot_rd {s : State} {R : BitVec 64} {EM : List Byte} {t : State} (hc : Post s R EM t) {d : Nat}
    (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ frameBytes) : InRegions (t.rd ++ t.wr) (fb s + BitVec.ofNat 64 d) 8 :=
  slotIn hc.wr h₁ h₂

section
variable {s : State} (h : DPre s) {R : BitVec 64} {EM : List Byte}
include h

theorem init_step {t : State} (hc : Post s R EM t) {rest : Prog isa} {Q : State → Prop}
    (hQ : ∀ u, Post s R EM u → hH.SH.Repr u.mem (scA s sSt) [] →
      Frame ([⟨scA s sSt, H.S⟩] ++ [below (fb s) 48]) t.mem u.mem → WP isa rest u Q) :
    WP isa (.seq (.block shaInitArgs) (.seq initCall rest)) t Q := by
  have c1 : oScr < 2 ^ 15 ∧ oScr % 4 = 0 := by decide
  have c2 : sSt < 2 ^ 15 := by decide
  have i1 := slot_rd hc (d := oScr) (by decide) (by decide)
  refine WP.seq (WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r12, .r3]
    (Q := fun u => u.mem = t.mem ∧ u.gpr .r3 = scA s sSt) ?_ rfl) fun u ⟨⟨um, u3⟩, ku⟩ => ?_)
  · unfold shaInitArgs scr
    prun [fp, exec_addSp0, hc.sp, c1, c2, i1, hc.sl.scr, exec_addi (show Reg.r3 ≠ .r0 by decide) c2]
  have hu : Post s R EM u := hc.regs ku.rd ku.wr ku.sp um fun r hr => ku.gpr r (by revert r; decide)
  have hs : 48 ≤ u.sp.toNat := by rw [hu.sp]; have := fb_ge h; omega
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
  have c1 : oScr < 2 ^ 15 ∧ oScr % 4 = 0 := by decide
  have c2 : oK < 2 ^ 15 ∧ oK % 4 = 0 := by decide
  have c3 : sSt < 2 ^ 15 := by decide
  have c4 : sD < 2 ^ 15 := by decide
  have c5 : sWork < 2 ^ 15 := by decide
  have i1 := slot_rd hc (d := oScr) (by decide) (by decide)
  have i2 := slot_rd hc (d := oK) (by decide) (by decide)
  refine WP.seq (WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r12, .r3, .r4, .r5, .r6, .r7]
    (Q := fun u => u.mem = t.mem ∧ u.gpr .r3 = scA s sSt ∧ u.gpr .r4 = 0 ∧ u.gpr .r5 = scA s sD ∧
      u.gpr .r6 = s.gpr .r7 ∧ u.gpr .r7 = scA s sWork) ?_ rfl) fun u ⟨⟨um, u3, u4, u5, u6, u7⟩, ku⟩ => ?_)
  · unfold shaUpdArgs scr
    prun [fp, exec_addSp0, hc.sp, c1, c2, c3, c4, c5, i1, i2, hc.sl.scr, hc.sl.k,
      exec_addi (show Reg.r3 ≠ .r0 by decide) c3, exec_addi (show Reg.r5 ≠ .r0 by decide) c4,
      exec_addi (show Reg.r7 ≠ .r0 by decide) c5]
    rfl
  have hu : Post s R EM u := hc.regs ku.rd ku.wr ku.sp um fun r hr => ku.gpr r (by revert r; decide)
  have hs : 48 ≤ u.sp.toNat := by rw [hu.sp]; have := fb_ge h; omega
  have lk : sD + (s.gpr .r7).toNat ≤ scrBytes := by unfold sD scrBytes; omega
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
  have c1 : oScr < 2 ^ 15 ∧ oScr % 4 = 0 := by decide
  have c2 : oK < 2 ^ 15 ∧ oK % 4 = 0 := by decide
  have c3 : sSt < 2 ^ 15 := by decide
  have c4 : sDH < 2 ^ 15 := by decide
  have c5 : sWork < 2 ^ 15 := by decide
  have i1 := slot_rd hc (d := oScr) (by decide) (by decide)
  have i2 := slot_rd hc (d := oK) (by decide) (by decide)
  refine WP.seq (WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r12, .r3, .r4, .r5, .r6]
    (Q := fun u => u.mem = t.mem ∧ u.gpr .r3 = scA s sSt ∧ u.gpr .r4 = s.gpr .r7 ∧ u.gpr .r5 = scA s sDH ∧
      u.gpr .r6 = scA s sWork) ?_ rfl) fun u ⟨⟨um, u3, u4, u5, u6⟩, ku⟩ => ?_)
  · unfold shaFinArgs scr
    prun [fp, exec_addSp0, hc.sp, c1, c2, c3, c4, c5, i1, i2, hc.sl.scr, hc.sl.k,
      exec_addi (show Reg.r3 ≠ .r0 by decide) c3, exec_addi (show Reg.r5 ≠ .r0 by decide) c4,
      exec_addi (show Reg.r6 ≠ .r0 by decide) c5]
  have hu : Post s R EM u := hc.regs ku.rd ku.wr ku.sp um fun r hr => ku.gpr r (by revert r; decide)
  have hs : 48 ≤ u.sp.toNat := by rw [hu.sp]; have := fb_ge h; omega
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
  · have e := hr m (um ▸ hm) (by rw [hl]; omega) (by rw [u4, hl, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    show Spec.Sha256.bytesAt v.mem (scA s sDH) H.FD = _
    rw [e, ← List.take_of_length_le (l := hH.fh m) (i := H.D) (by rw [hH.fhLen]; decide)]
    exact (hH.hashTake m).symm

theorem hashD_ok {t : State} (hd : DB s R EM t) : WP isa hashD t (DHS s R EM) := by
  have hk := h.k2
  have lk : sD + (s.gpr .r7).toNat ≤ scrBytes := by unfold sD scrBytes; omega
  refine init_step h hd.post fun u hu hr hf => ?_
  have hD := (keep_call h (by decide) hf lk fun r hr => by
    rw [List.mem_singleton.mp hr]; exact scD h (.inr (by decide)) lk (by decide)).trans hd.D
  refine upd_step h hu fun v hv hr' _ => ?_
  refine fin_step h hv fun w hw hr'' => ⟨hw, ?_⟩
  rw [hr'' _ (hr' [] hr rfl) (by simp [Spec.Rsa.bytesAt]), List.nil_append, hD]

end

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec
