module

public import VerifiedGarbage.Proof.RsaPss.AArch64.ChkFrame
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hash
public import VerifiedGarbage.Proof.Mgf1.Basic
public import VerifiedGarbage.Proof.RsaPss.AArch64.Mgf
public import VerifiedGarbage.Proof.RsaPss.VerifyCases
import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyB1
import VerifiedGarbage.Proof.RsaPss.AArch64.FixedSaltSelect
import VerifiedGarbage.Proof.RsaPss.AArch64.SignEnc
import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyLogic
import VerifiedGarbage.Proof.RsaPss.AArch64.SignEncOk
import VerifiedGarbage.Proof.RsaPss.AArch64.CtComp
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Framework.Offset

/-!
# EMSA-PSS's check of an encoding on AArch64: correctness after the prologue

The encoding copied to `EM` (`copyIn_okC`); after the checks of the lengths,
verification's checks of `EM` (`check_ok`): `x0` is 1 exactly when the
encoding is consistent with the digest (`EncOk`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Chk

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_movz wp_addImm)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_mov)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss (EncOk)
open VG.Proof.RsaPss.AArch64 (off off_add Lay Rep mgfWr slotR slot_keep updL b1_ok B1 wct mkB nz nz_lt resV msgV
  acc0V acc1V vlogic copyIn_ok bytes_apartL)
open VG.Proof.RsaPss.AArch64.Sgn (fb kR frame_sub frame_sub0 below_sub)

variable (G : Spec.Mgf1.Hash) in
/-- What `checkEncodingContract.post` asks of `x0`. -/
def chkOut (s : State) : Bool :=
  Spec.RsaPss.verifyEncoding G G (Spec.Rsa.bytesAt s.mem (s.gpr .x0) G.len)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat) (s.gpr .x3).toNat
    (Spec.RsaPss.expectedSaltLen (s.gpr .x4) ((s.gpr .x5).setWidth 32))

/-- The encoding, as the entry state gives it. -/
abbrev emB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat

/-- In the frame: the slots and the callee-saved registers' values. -/
structure MidC (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  fr : FrC s t.mem

theorem AtC.toMid {s u : State} (h : AtC s u) : MidC s u := ⟨h.sp, h.rd, h.wr, h.v, h.fr⟩

/-- `AtC` after code that writes registers other than ours, and nothing but
`EM` in memory. -/
theorem AtC.only {s u u' : State} (h : AtC s u) {rs : List Reg} (o : Only rs u u')
    (hr : ∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x1], r ∉ rs := by decide) : AtC s u' where
  sp := o.sp.trans h.sp
  rd := o.rd.trans h.rd
  wr := o.wr.trans h.wr
  x19 := (o.gpr .x19 (hr _ (by simp))).trans h.x19
  x20 := (o.gpr .x20 (hr _ (by simp))).trans h.x20
  x21 := (o.gpr .x21 (hr _ (by simp))).trans h.x21
  x23 := (o.gpr .x23 (hr _ (by simp))).trans h.x23
  x1 := (o.gpr .x1 (hr _ (by simp))).trans h.x1
  v := fun r hr' => (o.vcs r hr').trans (h.v r hr')
  mem := o.mem ▸ h.mem
  fr := o.mem ▸ h.fr
  lo := o.mem ▸ h.lo
  c := o.mem ▸ h.c

/-- Our part of the working space. -/
theorem rsa_sub {D : Nat} {s : State} (hp : PreC D s) : Region.Sub ⟨s.gpr .x6, oRsa⟩ (sR s) :=
  Region.sub_prefix (by have := hp.hs; unfold oRsa; omega)

/-- Our working space and the frame, laid out. -/
theorem lay_of {D : Nat} {s w : State} (hp : PreC D s) (hsp : w.sp = fb s) (h20 : w.gpr .x20 = s.gpr .x6)
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

/-- What the checks write keeps `FrC`. -/
theorem fr_mgf {D : Nat} {s : State} (hp : PreC D s) {m m' : Mem} (h : FrC s m)
    (hf : Frame (mgfWr (fb s) (s.gpr .x6) ++ [slotR (fb s) sPos]) m m') : FrC s m' := by
  refine h.frame hf (fun r hr => ?_) (fun r hr => ?_) <;>
  · simp only [mgfWr, slotR, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (hp.ks.sub_left (frame_sub 16 s (by decide))).sub_right (rsa_sub hp)
    · exact Offset.disjoint_below _ (by omega)
    · exact Offset.disjoint _ (by decide) (by decide) (by decide)
    · exact Offset.disjoint _ (by decide) (by decide) (by decide)
    · exact Offset.disjoint _ (by decide) (by decide) (by decide)

/-- `AtC` after code that writes registers other than ours, and memory only
in our working space. -/
theorem AtC.keep {D : Nat} {s u u' : State} (hp : PreC D s) (h : AtC s u) {rs : List Reg} (k : Keep rs u u')
    (hf : Frame [⟨s.gpr .x6, oRsa⟩] u.mem u'.mem)
    (hr : ∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x1], r ∉ rs := by decide) : AtC s u' := by
  have hd : ∀ {d n : Nat}, d + n ≤ frameBytes →
      ∀ r ∈ [(⟨s.gpr .x6, oRsa⟩ : Region)], Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, n⟩ r := fun hdn r hr' => by
    rw [List.mem_singleton.mp hr']
    exact (hp.ks.sub_left (frame_sub 16 s hdn)).sub_right (rsa_sub hp)
  exact {
    sp := k.sp.trans h.sp
    rd := k.rd.trans h.rd
    wr := k.wr.trans h.wr
    x19 := (k.gpr .x19 (hr _ (by simp))).trans h.x19
    x20 := (k.gpr .x20 (hr _ (by simp))).trans h.x20
    x21 := (k.gpr .x21 (hr _ (by simp))).trans h.x21
    x23 := (k.gpr .x23 (hr _ (by simp))).trans h.x23
    x1 := (k.gpr .x1 (hr _ (by simp))).trans h.x1
    v := fun r hr' => (k.vcs r hr').trans (h.v r hr')
    mem := h.mem.trans (hf.mono (by simp))
    fr := h.fr.frame hf (hd (by decide)) (hd (by decide))
    lo := by rw [slot_keep (d := sLo) hf (hd (by decide))]; exact h.lo
    c := by rw [slot_keep (d := sC) hf (hd (by decide))]; exact h.c }

/-- The encoding copied to `EM`. -/
theorem copyIn_okC {D : Nat} {s u : State} (hp : PreC D s) (hu : AtC s u) :
    WP isa copyIn u fun t => AtC s t ∧
      ∀ i < (s.gpr .x2).toNat, t.mem (off (s.gpr .x6) (oEm + i)) = (emB s).getD i 0 := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hwe := hp.we
  have L := lay_of hp hu.sp hu.x20 hu.wr
  unfold copyIn
  refine WP.seq (wp_mov fun u₁ o₁ e₁ => wp_addImm (by decide) fun u₂ o₂ e₂ => wp_mov fun u₃ o₃ e₃ => wp_nil ?_)
  have O : Only [.x11, .x14, .x12] u u₃ := (o₁.trans (o₂.trans o₃)).mono
  have L₃ := L.congr O.sp O.wr (O.get .x20)
  have hu₃ := hu.only O
  refine WP.mono (copyIn_ok L₃ (V := fun o => u₃.mem (off (s.gpr .x6) o)) (fun _ _ => rfl)
    (q := s.gpr .x1) (o := oEm) (n := (s.gpr .x2).toNat) (by omega) (by unfold oEm oRsa; omega)
    (by rw [o₃.get .x14, e₂, o₁.get .x20, hu.x20])
    (by rw [o₃.get .x11, o₂.get .x11, e₁, hu.x1])
    (by rw [e₃, o₂.get .x23, o₁.get .x23, hu.x23, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (fun j hj => by
      rw [O.rd, O.wr, hu.rd, hp.hrd]
      exact ⟨emR s, by simp, Offset.contains_base _ (by omega) (by omega)⟩)
    (hp.es.sub_right (rsa_sub hp))) fun t ⟨K, F, R⟩ => ⟨hu₃.keep hp K F, fun i hi => ?_⟩
  have hb : Spec.Rsa.bytesAt u₃.mem (s.gpr .x1) (s.gpr .x2).toNat = emB s :=
    bytes_apartL hu₃.mem (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.ke.sub_left (frame_sub0 16 s)).symm
      · exact hp.es.sub_right (rsa_sub hp)) (by omega)
  rw [R (oEm + i) (by unfold oEm oRsa; omega)]
  simp only [updL]
  rw [ite_eq_left ⟨by omega, by rw [VG.Proof.RsaPkcs1Sig.bytesAt_length]; omega⟩, Nat.add_sub_cancel_left, hb]

section
variable {H : Hash} (hH : HashOK H)

include hH in
/-- After the checks of the lengths: `EM` checked, `x0` 1 exactly when the
encoding is consistent. -/
theorem chkMain_ok {G : Spec.Mgf1.Hash} (hGh : ∀ x, G.hash x = hH.SH.H.hash x) (hGl : G.len = H.D)
    (hG : Proof.Mgf1.Valid G) {s u : State} (hp : PreC H.D s) (hu : AtC s u)
    (hem : ∀ i < (s.gpr .x2).toNat, u.mem (off (s.gpr .x6) (oEm + i)) = (emB s).getD i 0)
    (h9 : u.gpr .x9 = BitVec.ofNat 64 ((s.gpr .x2).toNat - (H.D + 2)))
    (hfit : H.D + 2 ≤ (s.gpr .x2).toNat)
    (hs : anyC s = 0 → (s.gpr .x4).toNat < (s.gpr .x2).toNat - H.D - 1) :
    WP isa (chkMain H) u fun t => MidC s t ∧ ∀ b : Bool, (b = true ↔ (0 = 1 → (emB s).getD 0 0 = 0) ∧
      EncOk G (Spec.Rsa.bytesAt s.mem (s.gpr .x0) H.D) ((emB s).drop 0) ((s.gpr .x2).toNat - 0) (zC s)
        (if anyC s = 0 then some (s.gpr .x4).toNat else none)) → t.gpr .x0 = if b then 1#64 else 0#64 := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have L₀ := lay_of hp hu.sp hu.x20 hu.wr
  show WP isa (.seq (.block dbRegs) (seqs [.block acc0, mgfXor H, .block clearTop, posScan, posCheck,
    FixedSalt.select H])) u _
  refine WP.seq (WP.mono (dbRegs_ok L₀ h9 hu.lo) fun t ⟨O, x25, x24⟩ => ?_)
  have ht := hu.only O
  have L := lay_of hp ht.sp ht.x20 ht.wr
  generalize hk : (s.gpr .x2).toNat = k at hfit hs x25 hk1 hk2 hem
  have hkd : 0 + (k - H.D - 1) + H.D + 1 = k := by omega
  have h25 : t.gpr .x25 = BitVec.ofNat 64 (k - H.D - 1) := by rw [x25]; congr 1; omega
  have h23 : t.gpr .x23 = BitVec.ofNat 64 k := by rw [ht.x23, ← hk, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine (b1_ok hH hGh hGl hG L (V := fun o => t.mem (off (s.gpr .x6) o)) (fun _ _ => rfl) (k := k) (lo := 0)
    (db := k - H.D - 1) (c := cC s) (any := anyC s) (sv := s.gpr .x4) hkd (by omega) hk2 (Nat.zero_le 1) ht.x19
    ht.x21 h23 x24 h25 ht.lo ht.c ht.fr.any ht.fr.sl
    (rest := Impl.RsaPss.AArch64.FixedSalt.select H)
    fun u B => ?_ : WP isa (seqs [.block acc0, mgfXor H, .block clearTop, posScan, posCheck,
      Impl.RsaPss.AArch64.FixedSalt.select H]) t _)
  have gu : ∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x25], u.gpr r = t.gpr r := B.cs
  have hslot : ∀ d, d + 8 ≤ frameBytes →
      (d + 8 ≤ sNb ∨ sNb + 8 ≤ d) → (d + 8 ≤ sDone ∨ sDone + 8 ≤ d) →
      (d + 8 ≤ sPos ∨ sPos + 8 ≤ d) →
      u.mem.readW (off (fb s) d) 64 = t.mem.readW (off (fb s) d) 64 := by
    intro d hd hn hf hpos
    apply slot_keep B.fr
    intro r hr
    rcases List.mem_append.mp hr with h | h
    · exact L.slotW hd hn hf r h
    · rw [List.mem_singleton.mp h]
      exact Offset.disjoint _ hpos (by unfold frameBytes at hd; omega) (by decide)
  have hrd : ∀ j < H.D, InRegions (u.rd ++ u.wr) (s.gpr .x0 + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [B.rd, B.wr, ht.rd, hp.hrd]
    exact ⟨dgR H.D s, by simp, Offset.contains_base _ (by omega) (by have := hp.wd; omega)⟩
  refine WP.mono (VG.Proof.RsaPss.AArch64.FixedSalt.select_ok hH (L.congr B.sp B.wr (gu .x20 (by decide)))
    (W := wct (fun o => t.mem (off (s.gpr .x6) o)) (mkB G H.D (fun o => t.mem (off (s.gpr .x6) o)) (oEm + 0)
      (k - H.D - 1)) (oEm + 0) (k - H.D - 1) (cC s)) (e := oEm + 0) (db := k - H.D - 1)
    B.em (by omega) (by unfold oEm oY; omega)
    (nz_lt (by omega)) (by omega) (by rw [gu .x19 (by decide), ht.x19]) (by rw [gu .x21 (by decide), ht.x21])
    (by rw [gu .x24 (by decide), x24]) (by rw [gu .x25 (by decide), h25]) B.acc B.pos
    (by rw [hslot sDig (by decide) (by decide) (by decide) (by decide)]; exact ht.fr.dig) hrd
    (hp.ds.sub_right (rsa_sub hp))
    (by rw [hslot sAny (by decide) (by decide) (by decide) (by decide)]; exact ht.fr.any)
    (sl := (s.gpr .x4).toNat)
    (by rw [hslot sSaltLen (by decide) (by decide) (by decide) (by decide), ht.fr.sl, BitVec.ofNat_toNat,
      BitVec.setWidth_eq])
    hs
    (by
      intro hany hacc
      have heq := (VG.Proof.RsaPss.AArch64.acc1V_eq_zero _ _ _ _ _).mp hacc
      exact (VG.Proof.RsaPss.AArch64.eq_ofNat_iff (by omega) _).mp (heq.2.2.2 hany))
    (by
      have hb := VG.Proof.RsaPss.AArch64.acc_lt (fun o => t.mem (off (s.gpr .x6) o)) k 0 (cC s)
        (fun i => wct (fun o => t.mem (off (s.gpr .x6) o))
          (mkB G H.D (fun o => t.mem (off (s.gpr .x6) o)) (oEm + 0) (k - H.D - 1))
          (oEm + 0) (k - H.D - 1) (cC s) (oEm + 0 + i))
        (k - H.D - 1) (anyC s) (s.gpr .x4) (fun _ => 0) 0 (by omega)
        (fun h => by have := hs h; omega) (fun _ => by decide)
      simpa [VG.Proof.RsaPss.AArch64.orF] using hb)) fun u' ⟨sp', rd', wr', cs', v', fr', x0'⟩ => ⟨?_, fun b hb => ?_⟩
  · exact ⟨by rw [sp', B.sp, ht.sp], by rw [rd', B.rd, ht.rd], by rw [wr', B.wr, ht.wr],
      fun r hr => by rw [v' r hr, B.v r hr, ht.v r hr],
      fr_mgf hp (fr_mgf hp ht.fr B.fr) (fr'.mono fun r hr => List.mem_append_left _ hr)⟩
  have hl : H.D ≤ 2 ^ 64 := by have := hp.wd; omega
  have hd : ∀ r ∈ mgfWr (fb s) (s.gpr .x6) ++ [slotR (fb s) sPos], Region.Disjoint (dgR H.D s) r := fun r hr => by
    simp only [mgfWr, slotR, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hp.ds.sub_right (rsa_sub hp)
    · exact (hp.kd.sub_left (below_sub 16 s)).symm
    · exact (hp.kd.sub_left (frame_sub 16 s (by decide))).symm
    · exact (hp.kd.sub_left (frame_sub 16 s (by decide))).symm
    · exact (hp.kd.sub_left (frame_sub 16 s (by decide))).symm
  have hdig : Spec.Rsa.bytesAt u.mem (s.gpr .x0) H.D = Spec.Rsa.bytesAt s.mem (s.gpr .x0) H.D := by
    rw [bytes_apartL B.fr hd hl]
    exact bytes_apartL ht.mem (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.kd.sub_left (frame_sub0 16 s)).symm
      · exact hp.ds.sub_right (rsa_sub hp)) hl
  rw [x0', hdig, ← funext hGh]
  refine vlogic hG hGl (x := emB s) (k := k) (lo := 0) (db := k - H.D - 1) (by rw [VG.Proof.RsaPkcs1Sig.bytesAt_length, hk]) (fun i hi => ?_) hkd
    (by omega) (Nat.zero_le 1) hk2 (VG.Proof.RsaPkcs1Sig.bytesAt_length _ _ _) rfl (fun h => hs h) ?_
  · show t.mem (off (s.gpr .x6) (oEm + i)) = _
    rw [O.mem]; exact hem i hi
  exact hb

end

end VG.Proof.RsaPss.AArch64.Chk
