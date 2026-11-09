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

/-- What `encodeTContract.post` asks for: the encoding with the hash function
`Hs` (of digests of `D` bytes) and MGF1's `Gs`. -/
def encOut (D : Nat) (Hs Gs : Spec.Mgf1.Hash) (s : State) : Option (List Byte) :=
  Spec.RsaPss.encode Hs Gs (Spec.Rsa.bytesAt s.mem (s.gpr .x2) D)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) (s.gpr .x5).toNat

/-- The outcome, from the memory and `x0`. -/
def OutOk (D : Nat) (Hs Gs : Spec.Mgf1.Hash) (s : State) (m : Mem) (r : BitVec 64) : Prop :=
  match encOut D Hs Gs s with
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

/-- `AtT` after code that writes registers other than ours. -/
theorem AtT.only {s u u' : State} (h : AtT s u) {rs : List Reg} (o : Only rs u u') (hsy : u'.syms = u.syms)
    (hr : ∀ r ∈ [Reg.x19, .x20, .x21, .x23], r ∉ rs := by decide) : AtT s u' :=
  ⟨h.e.only o hr, o.mem ▸ h.wm, o.mem ▸ h.wi, o.mem ▸ h.wc, o.mem ▸ h.wd, hsy.trans h.sy⟩

/-- Our part of the working space. -/
theorem rsa_sub {D : Nat} {tsH tsG : List FnTable} {s : State} (hp : PreE D tsH tsG s) : Region.Sub ⟨s.gpr .x6, oRsa⟩ (sR s) :=
  Region.sub_prefix (by have := hp.hs; unfold oRsa Proof.RsaPss.encScratch at *; omega)

/-- The 16 bytes below the frame, in the stack. -/
theorem below16_sub (s : State) : Region.Sub (below (fb s) 16) (kR 288 s) := fun x h =>
  below_sub 288 s x (Offset.sub_below (fb s) (a := 16) (n := 16) (b := 288) (m := 288) (by decide) (by decide) x h)

/-- Our working space and the frame, laid out. -/
theorem lay_of {D : Nat} {tsH tsG : List FnTable} {s w : State} (hp : PreE D tsH tsG s) (hsp : w.sp = fb s) (h20 : w.gpr .x20 = s.gpr .x6)
    (hwr : w.wr = ⟨fb s, frameBytes⟩ :: s.wr) : Lay w (fb s) (s.gpr .x6) := by
  have hfb := fb_toNat hp
  have := s.sp.isLt
  have hws := hp.ws
  have hhs := hp.hs
  exact {
    sp := hsp
    x20 := h20
    fw := by rw [hwr]; exact List.mem_cons_self
    sw := ⟨sR s, by rw [hwr, hp.hwr]; simp, ⟨rfl, show oRsa ≤ (s.gpr .x7).toNat * 8 by unfold oRsa Proof.RsaPss.encScratch at *; omega⟩⟩
    Fw := by omega
    Sw := by unfold oRsa Proof.RsaPss.encScratch at *; omega
    dFS := (hp.ks.sub_left (frame_sub0 288 s)).sub_right (rsa_sub hp)
    dB := (hp.ks.sub_left (below16_sub s)).sub_right (rsa_sub hp) }

/-- A buffer apart from the stack and the working space is apart from what
the encoding writes. -/
theorem mgfWr_disj {D : Nat} {tsH tsG : List FnTable} {s : State} (hp : PreE D tsH tsG s) {R : Region} (hk : (kR 288 s).Disjoint R)
    (hs : R.Disjoint (sR s)) : ∀ r ∈ mgfWr (fb s) (s.gpr .x6), R.Disjoint r := by
  intro r hr
  simp only [mgfWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hs.sub_right (rsa_sub hp)
  · exact (hk.sub_left (below16_sub s)).symm
  · exact (hk.sub_left (frame_sub 288 s (by decide))).symm
  · exact (hk.sub_left (frame_sub 288 s (by decide))).symm
  · rw [mgfFrame_eq]; exact (hk.sub_left (below_sub 288 s)).symm

/-- What the encoding writes keeps `FrE`. -/
theorem fr_mgf {D : Nat} {tsH tsG : List FnTable} {s : State} (hp : PreE D tsH tsG s) {m m' : Mem} (h : FrE s m)
    (hf : Frame (mgfWr (fb s) (s.gpr .x6)) m m') : FrE s m' := by
  refine h.frame hf fun r hr => ?_
  simp only [mgfWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (hp.ks.sub_left (frame_sub 288 s (d := 96) (n := 152) (by decide))).sub_right (rsa_sub hp)
  · exact Offset.disjoint_below _ (by omega)
  · exact Offset.disjoint _ (by decide) (by decide) (by decide)
  · exact Offset.disjoint _ (by decide) (by decide) (by decide)
  · exact Offset.disjoint_below _ (by rw [mgfFrame_eq]; omega)

/-- An input, in memory changed only in the frame. -/
theorem bytes_frame {s : State} {m : Mem} (hf : Frame [⟨fb s, frameBytes⟩] s.mem m) {R : Region}
    (hk : (kR 288 s).Disjoint R) (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len :=
  VG.Proof.RsaPkcs1Sig.bytes_apart hf (hk.sub_left (frame_sub0 288 s)).symm hl

/-- A refusal: 0. -/
theorem ret0_ok {D : Nat} {Hs Gs : Spec.Mgf1.Hash} {s u : State} (hu : AtE s u) (hn : encOut D Hs Gs s = none) :
    WP isa ret0 u fun t => MidE s t ∧ OutOk D Hs Gs s t.mem (t.gpr .x0) := by
  unfold ret0
  refine wp_movz fun t o e => wp_nil ⟨(hu.only o).toMid, ?_⟩
  simp only [OutOk, hn, e]
  rfl

/-- The encoding's bytes, from the entry state: `emLen = k` bytes with
`lo = 0`. -/
def encF (Hs Gs : Spec.Mgf1.Hash) (D : Nat) (s : State) : Nat → Byte :=
  RsaPss.emT 0 ((s.gpr .x1).toNat - 0 - D - 1) (s.gpr .x4).toNat
    (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)
    (Hs.hash (Spec.RsaPss.zeros 8 ++ Spec.Rsa.bytesAt s.mem (s.gpr .x2) D ++
      Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat))
    (Spec.Mgf1.mgf1 Gs (Hs.hash (Spec.RsaPss.zeros 8 ++ Spec.Rsa.bytesAt s.mem (s.gpr .x2) D ++
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

/-- The slots of the table of `MdHash`, from the table at the entry. -/
theorem ht_of {H : Hash} {dn : String} {f : MdFns} {G : Impl.Pbkdf2.Md.AArch64.Stream}
    {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {s w : State} (ht : TabsAt H dn f G g (stackArg s 0) (stackArg s 1) s)
    (hw : AtT s w) : HT H dn f (fb s) w.mem w.syms where
  wi := hw.wi.trans (ht.h0.trans (by rw [hw.sy]))
  wc := hw.wc.trans (ht.h3.trans (by rw [hw.sy]))
  wd := hw.wd.trans (ht.h4.trans (by rw [hw.sy]))
  fi := by rw [hw.sy]; exact ht.fi
  fc := by rw [hw.sy]; exact ht.fc
  fd := by rw [hw.sy]; exact ht.fd

/-- MGF1's working space, in ours. -/
theorem mgfScr_sub {D : Nat} {tsH tsG : List FnTable} {s : State} (hp : PreE D tsH tsG s) :
    Region.Sub ⟨off (s.gpr .x6) mgfOff, 8192⟩ (sR s) :=
  Offset.sub_base _ (by have := hp.hs; unfold mgfOff Proof.RsaPss.encScratch at *; omega)

/-- Where MGF1 works, and the table of `Hash`, from the table at the entry. -/
theorem env_of {D : Nat} {tsH tsG : List FnTable} {H : Hash} {dn : String} {f : MdFns}
    {G : Impl.Pbkdf2.Md.AArch64.Stream} {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {s w : State}
    (hp : PreE D tsH tsG s) (ht : TabsAt H dn f G g (stackArg s 0) (stackArg s 1) s) (hw : AtT s w) :
    Env G g w (fb s) (s.gpr .x6) (stackArg s 1) := by
  have hfb := fb_toNat hp
  have hsp1 := hp.sp1
  have hwtG := hp.wtG
  have hws := hp.ws
  have hhs := hp.hs
  have hS := mgfScr_sub hp
  have kG : ∀ {R : Region}, R.Sub (kR 288 s) → Region.Disjoint ⟨stackArg s 1, 40⟩ R := fun hR =>
    (hp.ktG.sub_left hR).symm
  have sG : ∀ {R : Region}, R.Sub (sR s) → Region.Disjoint ⟨stackArg s 1, 40⟩ R := fun hR =>
    (hp.stG.sub_left hR).symm
  have hd : ∀ r ∈ mgfWr (fb s) (s.gpr .x6) ++ [⟨off (s.gpr .x6) mgfOff, 8192⟩, slotR (fb s) sPos],
      Region.Disjoint ⟨stackArg s 1, 40⟩ r := by
    intro r hr
    simp only [mgfWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sG (rsa_sub hp)
    · exact kG (below16_sub s)
    · exact kG (frame_sub 288 s (by decide))
    · exact kG (frame_sub 288 s (by decide))
    · rw [mgfFrame_eq]; exact (hp.ktG.sub_left (below_sub 288 s)).symm
    · exact sG hS
    · exact kG (frame_sub 288 s (by decide))
  have hd0 : ∀ r ∈ [(⟨fb s, frameBytes⟩ : Region)], Region.Disjoint ⟨stackArg s 1, 40⟩ r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact kG (frame_sub0 288 s)
  have hin : ∀ d, d + 8 ≤ 40 → InRegions (w.rd ++ w.wr) (off (stackArg s 1) d) 8 := fun d hd' => by
    rw [hw.e.rd, hp.hrd]
    exact ⟨tGR s, by simp, Offset.contains_base _ (k := 40) (by omega) (by omega)⟩
  exact {
    slot := hw.wm
    ok := by rw [hw.sy]; exact ht.gok
    rd := fun j hj => hin (8 * j) (by omega)
    rdD := hin 32 (by decide)
    mem := fun m hm => by
      rw [hw.sy]
      exact ⟨TabMem.keep (TabMem.keep ht.gm hw.e.mem hd0) hm hd,
        ((tabG_keep hm hd (by decide)).trans (tabG_keep hw.e.mem hd0 (by decide))).trans ht.gD⟩
    sc := Covers.one (by
      rw [hw.e.wr, hp.hwr]
      exact ⟨sR s, by simp, Offset.contains_base _ (by unfold mgfOff Proof.RsaPss.encScratch at *; omega)
        (by unfold mgfOff; omega)⟩)
    F288 := by rw [mgfFrame_eq]; unfold encStack Sgn.stk at hsp1; omega
    dStk := by rw [mgfFrame_eq]; exact (hp.ks.sub_left (below_sub 288 s)).sub_right hS
    Sw := by simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; unfold mgfOff Proof.RsaPss.encScratch at *; omega
    dFw := (hp.ks.sub_left (frame_sub0 288 s)).sub_right hS }

section
variable {H : Hash} (hH : HashOK H) {Gm : Impl.Pbkdf2.Md.AArch64.Stream}
  (hGm : VG.Proof.Pbkdf2.Md.AArch64.Calls.StreamOK Gm) {Hs Gs : Spec.Mgf1.Hash}
  (hHs : ∀ x, Hs.hash x = hH.SH.H.hash x) (hGh : ∀ x, Gs.hash x = hGm.SH.H.hash x) (hGl : Gs.len = Gm.D)
  (hGv : Proof.Mgf1.Valid Gs) {f : MdFns} {dn : String} (hdo : DigOK H.P) {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns}

include hH hHs hGh hGl hGv hdo in
/-- After the checks: the encoding. -/
theorem enc_ok {tsH tsG : List FnTable} {s w : State} (hp : PreE H.D tsH tsG s)
    (ht : TabsAt H dn f Gm g (stackArg s 0) (stackArg s 1) s) (hw : AtT s w)
    (h9 : w.gpr .x9 = BitVec.ofNat 64 ((s.gpr .x1).toNat - (H.D + 2)))
    (hfit : H.D + (s.gpr .x4).toNat + 2 ≤ (s.gpr .x1).toNat) :
    WP isa (signEnc f H g) w (AtCopy s (encF Hs Gs H.D s)) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have L := lay_of hp hw.e.sp hw.e.x20 hw.e.wr
  have hwd := hp.wd; have hwsa := hp.wsa
  have hdR : ∀ j < H.D, InRegions (w.rd ++ w.wr) (s.gpr .x2 + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hw.e.rd, hp.hrd]
    exact ⟨dgR H.D s, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hqR : ∀ j < (s.gpr .x4).toNat, InRegions (w.rd ++ w.wr) (s.gpr .x3 + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hw.e.rd, hp.hrd]
    exact ⟨saR s, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hbd : Spec.Rsa.bytesAt w.mem (s.gpr .x2) H.D = Spec.Rsa.bytesAt s.mem (s.gpr .x2) H.D :=
    bytes_frame (R := dgR H.D s) hw.e.mem hp.kd (by dsimp only; omega)
  have hbs : Spec.Rsa.bytesAt w.mem (s.gpr .x3) (s.gpr .x4).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat :=
    bytes_frame (R := saR s) hw.e.mem hp.ksa (by dsimp only; omega)
  refine WP.mono (signEnc_ok hH hGm hGh hGl hGv hHs hdo L (fun _ _ => rfl) (k := (s.gpr .x1).toNat) (lo := 0)
    (sl := (s.gpr .x4).toNat) (c := cE s) (dig := s.gpr .x2) (q := s.gpr .x3) hw.e.x19 hw.e.x21
    (by rw [hw.e.x23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by rw [h9, Nat.sub_zero]) hw.e.lo hw.e.c
    (hw.e.fr.rs (.x2, sDig) (by simp [encSlots])) (hw.e.fr.rs (.x3, sSalt) (by simp [encSlots]))
    (by rw [hw.e.fr.rs (.x4, sSaltLen) (by simp [encSlots]), BitVec.ofNat_toNat, BitVec.setWidth_eq])
    hk2 (Nat.zero_le 1) (by omega) hdR (mgfWr_disj hp hp.kd hp.ds) hqR (mgfWr_disj hp hp.ksa hp.sas)
    (ht_of ht hw) (env_of hp ht hw)) fun t ⟨sp₁, rd₁, wr₁, cs₁, v₁, f₁, em₁⟩ => ?_
  rw [hbd, hbs] at em₁
  exact {
    sp := sp₁.trans hw.e.sp
    rd := rd₁.trans hw.e.rd
    wr := wr₁.trans hw.e.wr
    x20 := (cs₁ .x20 (by decide)).trans hw.e.x20
    x23 := (cs₁ .x23 (by decide)).trans hw.e.x23
    v := fun r hr => (v₁ r hr).trans (hw.e.v r hr)
    fr := fr_mgf hp hw.e.fr f₁
    em := em₁ }

end

/-- The arguments of the copy: `EM`, `em` and `emLen`. -/
theorem copyArgs_ok {D : Nat} {tsH tsG : List FnTable} {s t : State} {em : Nat → Byte} (hp : PreE D tsH tsG s) (ht : AtCopy s em t) :
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
theorem copy_ok' {D : Nat} {tsH tsG : List FnTable} {s t : State} {em : Nat → Byte} (hp : PreE D tsH tsG s) (ht : AtCopy s em t) :
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
    have := hp.ke.sub_left (frame_sub 288 s (d := 96) (n := 152) (by decide))
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
variable {H : Hash} (hH : HashOK H) {Gm : Impl.Pbkdf2.Md.AArch64.Stream}
  (hGm : VG.Proof.Pbkdf2.Md.AArch64.Calls.StreamOK Gm) {Hs Gs : Spec.Mgf1.Hash}
  (hHs : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D) (hHv : Proof.Mgf1.Valid Hs)
  (hGh : ∀ x, Gs.hash x = hGm.SH.H.hash x) (hGl : Gs.len = Gm.D)
  (hGv : Proof.Mgf1.Valid Gs) {f : MdFns} {dn : String} (hdo : DigOK H.P) {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns}

include hH hHs hHl hHv hGh hGl hGv hdo in
/-- After the checks: the encoding, its copy to `em`, and 1. -/
theorem encMain_ok {tsH tsG : List FnTable} {s w : State} (hp : PreE H.D tsH tsG s)
    (ht : TabsAt H dn f Gm g (stackArg s 0) (stackArg s 1) s) (hw : AtT s w)
    (h9 : w.gpr .x9 = BitVec.ofNat 64 ((s.gpr .x1).toNat - (H.D + 2)))
    (hfit : H.D + (s.gpr .x4).toNat + 2 ≤ (s.gpr .x1).toNat) :
    WP isa (encMain f H g) w fun t => MidE s t ∧ OutOk H.D Hs Gs s t.mem (t.gpr .x0) := by
  unfold encMain seqs seqs
  refine WP.seq (WP.mono (enc_ok hH hGm hHs hGh hGl hGv hdo hp ht hw h9 hfit) fun t ht => ?_)
  refine WP.mono (copy_ok' hp ht) fun t' ⟨m, h0, hb⟩ => ⟨m, ?_⟩
  have hsl' : (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat).length = (s.gpr .x4).toNat :=
    VG.Proof.RsaPkcs1Sig.bytesAt_length _ _ _
  have he := RsaPss.encode_eq₂ Hs Gs hHv hGv (mHash := Spec.Rsa.bytesAt s.mem (s.gpr .x2) H.D)
    (salt := Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) (emBits := (s.gpr .x5).toNat)
    (emLen := (s.gpr .x1).toNat) (db := (s.gpr .x1).toNat - 0 - H.D - 1)
    (by rw [VG.Proof.RsaPkcs1Sig.bytesAt_length, hHl])
    hp.hel.symm (by rw [hHl]; omega) (by rw [hsl', hHl]; omega)
  simp only [OutOk, encOut, he]
  refine ⟨by rw [h0]; rfl, ?_⟩
  rw [hb, hsl']
  rfl

end

end VG.Proof.RsaPss.AArch64.Enc
