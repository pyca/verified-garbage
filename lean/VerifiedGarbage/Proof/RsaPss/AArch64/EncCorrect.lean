module

public import VerifiedGarbage.Proof.RsaPss.AArch64.EncFrame
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hash
public import VerifiedGarbage.Proof.Mgf1.Basic
public import VerifiedGarbage.Proof.RsaPss.AArch64.Mgf
public import VerifiedGarbage.Proof.RsaPss.EncBytes
import VerifiedGarbage.Proof.RsaPss.AArch64.SignEncOk
import VerifiedGarbage.Proof.RsaPss.AArch64.SignEnc
import VerifiedGarbage.Proof.RsaPss.AArch64.SignChecks
import VerifiedGarbage.Proof.RsaPss.AArch64.MaskBits
import VerifiedGarbage.Proof.RsaPss.AArch64.Restore
import VerifiedGarbage.Proof.RsaPss.AArch64.CtComp
import VerifiedGarbage.Proof.RsaPss.AArch64.CtHash
import VerifiedGarbage.Proof.RsaPss.EncodeEq
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Encode
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# EMSA-PSS's encoding on AArch64: correctness

`code_ok`: `encode` keeps the calling convention, and returns 1 with `em`
holding `Spec.RsaPss.encode`'s encoding, or 0 if it fails (`Post`). After
the prologue, the checks of the lengths (`fitH_ok`, `saltFits_ok`), then the
encoding (`signEnc_ok`, with `k = emLen` and `lo = 0`) and its copy to `em`
(`encMain_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPss.AArch64 VG.WriteBytes
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_movz wp_addImm eval_nonzero)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_ldrSp wp_mov copy_ok)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss.AArch64 (off off_add Lay mgfWr signEnc_ok fitH_ok saltFits_ok restore_frame_ok ld_slot
  slot_not_below)
open VG.Proof.RsaPss.AArch64.Sgn (fb kR frame_sub frame_sub0 below_sub)

variable (G : Spec.Mgf1.Hash) in
/-- What `encodeContract.post` asks for. -/
def encOut (s : State) : Option (List Byte) :=
  Spec.RsaPss.encode G G (Spec.Rsa.bytesAt s.mem (s.gpr .x2) G.len)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) (s.gpr .x5).toNat

variable (G : Spec.Mgf1.Hash) in
/-- The outcome, from the memory and `x0`. -/
def OutOk (s : State) (m : Mem) (r : BitVec 64) : Prop :=
  match encOut G s with
  | some e => r.setWidth 32 = 1 ∧ Spec.Rsa.bytesAt m (s.gpr .x0) (s.gpr .x1).toNat = e
  | none => r.setWidth 32 = 0

/-- In the frame: the slots and the callee-saved registers' values. -/
structure MidE (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  fr : FrE s t.mem

theorem AtE.toMid {s u : State} (h : AtE s u) : MidE s u := ⟨h.sp, h.rd, h.wr, h.v, h.fr⟩

/-- `AtE` after code that writes registers other than ours. -/
theorem AtE.only {s u u' : State} (h : AtE s u) {rs : List Reg} (o : Only rs u u')
    (hr : ∀ r ∈ [Reg.x19, .x20, .x21, .x23], r ∉ rs := by decide) : AtE s u' where
  sp := o.sp.trans h.sp
  rd := o.rd.trans h.rd
  wr := o.wr.trans h.wr
  x19 := (o.gpr .x19 (hr _ (by simp))).trans h.x19
  x20 := (o.gpr .x20 (hr _ (by simp))).trans h.x20
  x21 := (o.gpr .x21 (hr _ (by simp))).trans h.x21
  x23 := (o.gpr .x23 (hr _ (by simp))).trans h.x23
  v := fun r hr' => (o.vcs r hr').trans (h.v r hr')
  mem := o.mem ▸ h.mem
  fr := o.mem ▸ h.fr
  lo := o.mem ▸ h.lo
  c := o.mem ▸ h.c

/-- Our part of the working space. -/
theorem rsa_sub {D : Nat} {s : State} (hp : PreE D s) : Region.Sub ⟨s.gpr .x6, oRsa⟩ (sR s) :=
  Region.sub_prefix (by have := hp.hs; unfold oRsa; omega)

/-- Our working space and the frame, laid out. -/
theorem lay_of {D : Nat} {s w : State} (hp : PreE D s) (hsp : w.sp = fb s) (h20 : w.gpr .x20 = s.gpr .x6)
    (hwr : w.wr = ⟨fb s, frameBytes⟩ :: s.wr) : Lay w (fb s) (s.gpr .x6) := by
  have hfb := fb_toNat hp
  have := s.sp.isLt
  have hws := hp.ws
  have hhs := hp.hs
  exact {
    sp := hsp
    x20 := h20
    fw := by rw [hwr]; exact List.mem_cons_self
    sw := ⟨sR s, by rw [hwr, hp.hwr]; simp, ⟨rfl, show oRsa ≤ (s.gpr .x7).toNat * 8 by unfold oRsa; omega⟩⟩
    Fw := by omega
    Sw := by unfold oRsa; omega
    dFS := (hp.ks.sub_left (frame_sub0 16 s)).sub_right (rsa_sub hp)
    dB := (hp.ks.sub_left (below_sub 16 s)).sub_right (rsa_sub hp) }

/-- A buffer apart from the stack and the working space is apart from what
the encoding writes. -/
theorem mgfWr_disj {D : Nat} {s : State} (hp : PreE D s) {R : Region} (hk : (kR 16 s).Disjoint R)
    (hs : R.Disjoint (sR s)) : ∀ r ∈ mgfWr (fb s) (s.gpr .x6), R.Disjoint r := by
  intro r hr
  simp only [mgfWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hs.sub_right (rsa_sub hp)
  · exact (hk.sub_left (below_sub 16 s)).symm
  · exact (hk.sub_left (frame_sub 16 s (by decide))).symm
  · exact (hk.sub_left (frame_sub 16 s (by decide))).symm

/-- What the encoding writes keeps `FrE`. -/
theorem fr_mgf {D : Nat} {s : State} (hp : PreE D s) {m m' : Mem} (h : FrE s m)
    (hf : Frame (mgfWr (fb s) (s.gpr .x6)) m m') : FrE s m' := by
  refine h.frame hf fun r hr => ?_
  simp only [mgfWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hp.ks.sub_left (frame_sub 16 s (d := 96) (n := 152) (by decide))).sub_right (rsa_sub hp)
  · exact Offset.disjoint_below _ (by omega)
  · exact Offset.disjoint _ (by decide) (by decide) (by decide)
  · exact Offset.disjoint _ (by decide) (by decide) (by decide)

/-- An input, in memory changed only in the frame. -/
theorem bytes_frame {s : State} {m : Mem} (hf : Frame [⟨fb s, frameBytes⟩] s.mem m) {R : Region}
    (hk : (kR 16 s).Disjoint R) (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len :=
  VG.Proof.RsaPkcs1Sig.bytes_apart hf (hk.sub_left (frame_sub0 16 s)).symm hl

/-- A refusal: 0. -/
theorem ret0_ok {G : Spec.Mgf1.Hash} {s u : State} (hu : AtE s u) (hn : encOut G s = none) :
    WP isa ret0 u fun t => MidE s t ∧ OutOk G s t.mem (t.gpr .x0) := by
  unfold ret0
  refine wp_movz fun t o e => wp_nil ⟨(hu.only o).toMid, ?_⟩
  simp only [OutOk, hn, e]
  rfl

variable (G : Spec.Mgf1.Hash) in
/-- The encoding's bytes, from the entry state: `emLen = k` bytes with
`lo = 0`. -/
def encF (D : Nat) (s : State) : Nat → Byte :=
  RsaPss.emT 0 ((s.gpr .x1).toNat - 0 - D - 1) (s.gpr .x4).toNat
    (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)
    (G.hash (Spec.RsaPss.zeros 8 ++ Spec.Rsa.bytesAt s.mem (s.gpr .x2) D ++
      Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat))
    (Spec.Mgf1.mgf1 G (G.hash (Spec.RsaPss.zeros 8 ++ Spec.Rsa.bytesAt s.mem (s.gpr .x2) D ++
      Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)) ((s.gpr .x1).toNat - 0 - D - 1)) (cE s)

/-- After `signEnc`: `EM` holds `em`. -/
structure AtCopy (s : State) (em : Nat → Byte) (t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  x20 : t.gpr .x20 = s.gpr .x6
  x23 : t.gpr .x23 = s.gpr .x1
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  fr : FrE s t.mem
  em : ∀ i < (s.gpr .x1).toNat, t.mem (off (s.gpr .x6) (oEm + i)) = em i

section
variable {H : Hash} (hH : HashOK H)

include hH in
/-- After the checks: the encoding. -/
theorem enc_ok {G : Spec.Mgf1.Hash} (hGh : ∀ x, G.hash x = hH.SH.H.hash x) (hGl : G.len = H.D)
    (hG : Proof.Mgf1.Valid G) {s w : State} (hp : PreE H.D s) (hw : AtE s w)
    (h9 : w.gpr .x9 = BitVec.ofNat 64 ((s.gpr .x1).toNat - (H.D + 2)))
    (hfit : H.D + (s.gpr .x4).toNat + 2 ≤ (s.gpr .x1).toNat) :
    WP isa (signEnc H) w (AtCopy s (encF G H.D s)) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have L := lay_of hp hw.sp hw.x20 hw.wr
  have hwd := hp.wd; have hwsa := hp.wsa
  have hdR : ∀ j < H.D, InRegions (w.rd ++ w.wr) (s.gpr .x2 + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hw.rd, hp.hrd]
    exact ⟨dgR H.D s, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hqR : ∀ j < (s.gpr .x4).toNat, InRegions (w.rd ++ w.wr) (s.gpr .x3 + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hw.rd, hp.hrd]
    exact ⟨saR s, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hbd : Spec.Rsa.bytesAt w.mem (s.gpr .x2) H.D = Spec.Rsa.bytesAt s.mem (s.gpr .x2) H.D :=
    bytes_frame (R := dgR H.D s) hw.mem hp.kd (by dsimp only; omega)
  have hbs : Spec.Rsa.bytesAt w.mem (s.gpr .x3) (s.gpr .x4).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat :=
    bytes_frame (R := saR s) hw.mem hp.ksa (by dsimp only; omega)
  refine WP.mono (signEnc_ok hH hGh hGl hG L (fun _ _ => rfl) (k := (s.gpr .x1).toNat) (lo := 0)
    (sl := (s.gpr .x4).toNat) (c := cE s) (dig := s.gpr .x2) (q := s.gpr .x3) hw.x19 hw.x21
    (by rw [hw.x23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by rw [h9, Nat.sub_zero]) hw.lo hw.c
    (hw.fr.rs (.x2, sDig) (by simp [encSlots])) (hw.fr.rs (.x3, sSalt) (by simp [encSlots]))
    (by rw [hw.fr.rs (.x4, sSaltLen) (by simp [encSlots]), BitVec.ofNat_toNat, BitVec.setWidth_eq])
    hk2 (Nat.zero_le 1) (by omega) hdR (mgfWr_disj hp hp.kd hp.ds) hqR (mgfWr_disj hp hp.ksa hp.sas))
    fun t ⟨sp₁, rd₁, wr₁, cs₁, v₁, f₁, em₁⟩ => ?_
  rw [hbd, hbs] at em₁
  exact {
    sp := sp₁.trans hw.sp
    rd := rd₁.trans hw.rd
    wr := wr₁.trans hw.wr
    x20 := (cs₁ .x20 (by decide)).trans hw.x20
    x23 := (cs₁ .x23 (by decide)).trans hw.x23
    v := fun r hr => (v₁ r hr).trans (hw.v r hr)
    fr := fr_mgf hp hw.fr f₁
    em := em₁ }

end

/-- The arguments of the copy: `EM`, `em` and `emLen`. -/
theorem copyArgs_ok {D : Nat} {s t : State} {em : Nat → Byte} (hp : PreE D s) (ht : AtCopy s em t) :
    WP isa (.block [.addImm .x .x11 .x20 oEm, ld .x14 sOut, VG.Impl.MdStream.AArch64.mov .x12 .x23]) t
      fun u => Only [.x11, .x14, .x12] t u ∧ u.gpr .x11 = off (s.gpr .x6) oEm ∧ u.gpr .x14 = s.gpr .x0 ∧
        u.gpr .x12 = s.gpr .x1 := by
  have L := lay_of hp ht.sp ht.x20 ht.wr
  refine wp_addImm (by decide) fun u₁ o₁ e₁ => wp_ldrSp (by decide)
    (by rw [o₁.sp, o₁.rd, o₁.wr]; exact ld_slot L (by decide)) fun u₂ o₂ e₂ => wp_mov fun u₃ o₃ e₃ =>
    wp_nil ⟨(o₁.trans (o₂.trans o₃)).mono, ?_, ?_, ?_⟩
  · rw [o₃.get .x11, o₂.get .x11, e₁, ht.x20]
  · rw [o₃.get .x14, e₂, o₁.mem, o₁.sp, ht.sp]
    exact ht.fr.rs (.x0, sOut) (by simp [encSlots])
  · rw [e₃, o₂.get .x23, o₁.get .x23, ht.x23]

/-- The copy of `EM` to `em`, and 1. -/
theorem copy_ok' {D : Nat} {s t : State} {em : Nat → Byte} (hp : PreE D s) (ht : AtCopy s em t) :
    WP isa (.seq copyOut (.block [movi .x0 1])) t fun t' => MidE s t' ∧ t'.gpr .x0 = BitVec.ofNat 64 1 ∧
      Spec.Rsa.bytesAt t'.mem (s.gpr .x0) (s.gpr .x1).toNat = (List.range (s.gpr .x1).toNat).map em := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hwe := hp.we
  have L := lay_of hp ht.sp ht.x20 ht.wr
  generalize hk : (s.gpr .x1).toNat = k at hk1 hk2 hwe
  unfold copyOut
  refine WP.seq (WP.seq (WP.mono (copyArgs_ok hp ht) fun u ⟨O, h11, h14, h12⟩ => ?_))
  have hd : ∀ j < k, ∀ i < k, off (s.gpr .x6) oEm + BitVec.ofNat 64 j ≠ s.gpr .x0 + BitVec.ofNat 64 i := by
    intro j hj i hi h
    have h₁ : (emR s).Contains (s.gpr .x0 + BitVec.ofNat 64 i) 1 :=
      Offset.contains_base (s.gpr .x0) (d := i) (n := 1) (k := (s.gpr .x1).toNat) (by omega) (by omega)
    have h₂ : (⟨s.gpr .x6, oRsa⟩ : Region).Contains (s.gpr .x0 + BitVec.ofNat 64 i) 1 := by
      rw [← h, off_add]
      exact Offset.contains_base _ (by unfold oEm oRsa; omega) (by unfold oEm; omega)
    exact hp.es _ h₁ (rsa_sub hp _ h₂)
  refine WP.mono (copy_ok (p := s.gpr .x0) (q := off (s.gpr .x6) oEm) (n := k) (by omega) (by omega) h14 h11
    (by rw [h12, ← hk, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (fun j hj => by rw [O.rd, O.wr, off_add]; exact L.ld (by simp only [oEm, oRsa]; omega))
    (fun i hi => by
      rw [O.wr, ht.wr, hp.hwr]
      exact ⟨emR s, by simp, Offset.contains_base _ (by omega) (by omega)⟩) hd) fun u₄ ⟨K₄, m₄⟩ => ?_
  refine wp_movz fun t₅ o₅ e₅ => wp_nil ⟨⟨?_, ?_, ?_, ?_, ?_⟩, by rw [e₅]; rfl, ?_⟩
  · rw [o₅.sp, K₄.sp, O.sp, ht.sp]
  · rw [o₅.rd, K₄.rd, O.rd, ht.rd]
  · rw [o₅.wr, K₄.wr, O.wr, ht.wr]
  · intro r hr; rw [o₅.vcs r hr, K₄.vcs r hr, O.vcs r hr, ht.v r hr]
  · rw [o₅.mem, m₄, O.mem]
    refine ht.fr.frame (writeBytes_frame _ _ _ (Region.contains_self _ _)) fun r hr => ?_
    rw [List.mem_singleton.mp hr, VG.Proof.RsaPkcs1Sig.bytesAt_length]
    have := hp.ke.sub_left (frame_sub 16 s (d := 96) (n := 152) (by decide))
    dsimp only [emR] at this
    rwa [hk] at this
  rw [o₅.mem, m₄, O.mem]
  have hx := VG.Proof.RsaPkcs1Sig.bytesAt_writeBytes t.mem (s.gpr .x0)
    (Spec.Rsa.bytesAt t.mem (off (s.gpr .x6) oEm) k) (by rw [VG.Proof.RsaPkcs1Sig.bytesAt_length]; omega)
  rw [VG.Proof.RsaPkcs1Sig.bytesAt_length] at hx
  rw [hx, show Spec.Rsa.bytesAt t.mem (off (s.gpr .x6) oEm) k =
    (List.range k).map fun i => t.mem (off (s.gpr .x6) oEm + BitVec.ofNat 64 i) from rfl]
  refine List.map_congr_left fun i hi => ?_
  rw [off_add, ht.em i (by rw [hk]; exact List.mem_range.mp hi)]

section
variable {H : Hash} (hH : HashOK H)

include hH in
/-- After the checks: the encoding, its copy to `em`, and 1. -/
theorem encMain_ok {G : Spec.Mgf1.Hash} (hGh : ∀ x, G.hash x = hH.SH.H.hash x) (hGl : G.len = H.D)
    (hG : Proof.Mgf1.Valid G) {s w : State} (hp : PreE H.D s) (hw : AtE s w)
    (h9 : w.gpr .x9 = BitVec.ofNat 64 ((s.gpr .x1).toNat - (H.D + 2)))
    (hfit : H.D + (s.gpr .x4).toNat + 2 ≤ (s.gpr .x1).toNat) :
    WP isa (encMain H) w fun t => MidE s t ∧ OutOk G s t.mem (t.gpr .x0) := by
  unfold encMain seqs seqs
  refine WP.seq (WP.mono (enc_ok hH hGh hGl hG hp hw h9 hfit) fun t ht => ?_)
  refine WP.mono (copy_ok' hp ht) fun t' ⟨m, h0, hb⟩ => ⟨m, ?_⟩
  have hsl' : (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat).length = (s.gpr .x4).toNat :=
    VG.Proof.RsaPkcs1Sig.bytesAt_length _ _ _
  have he := RsaPss.encode_eq G hG (mHash := Spec.Rsa.bytesAt s.mem (s.gpr .x2) G.len)
    (salt := Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) (emBits := (s.gpr .x5).toNat)
    (emLen := (s.gpr .x1).toNat) (db := (s.gpr .x1).toNat - 0 - H.D - 1) (VG.Proof.RsaPkcs1Sig.bytesAt_length _ _ _)
    hp.hel.symm (by omega) (by rw [hsl', hGl]; omega)
  simp only [OutOk, encOut, he]
  refine ⟨by rw [h0]; rfl, ?_⟩
  rw [hb, hGl, hsl']
  rfl

end

end VG.Proof.RsaPss.AArch64.Enc
