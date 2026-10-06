import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecoverFrame
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyCall

/-!
# `vg_rsa_pkcs1_recover` on AArch64: the call of `vg_rsa_public_checked`

`call_ok`: from `AtCall`, the call writes `EM = s^e mod n` (or zeros) to
`EM₁`, and keeps the values in `x19`–`x22` and the saved slots
(`AfterCall`).
-/

namespace VG.Proof.RsaPkcs1Sig.AArch64.Rec

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.Recover
open VG.Impl.RsaPkcs1Sig.AArch64.Verify (frameBytes oEM1 oEM2 saved)
open VG.Proof.RsaPkcs1Sig.AArch64.Ver (stk sR aR kR fb kb fb_eq off_fb frame_sub frame_sub0 below_fb in_frame
  in_frame0 saved_offs bytes_of_frame)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo)

/-- `EM₁`, of `k` bytes. -/
abbrev em1R (s : State) : Region := ⟨fb s + BitVec.ofNat 64 oEM1, (s.gpr .x3).toNat⟩

/-- RSAVP1 of the signature, as the entry state gives it. -/
def pubOut (s : State) : Option (List Byte) :=
  Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .x7) (s.gpr .x3).toNat)

/-- In the frame, from the entry state `s`: the registers saved, `x19`–`x22`
holding `out`, `out_len`, `k` and `hash`. -/
structure Mid (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  x19 : t.gpr .x19 = s.gpr .x0
  x20 : t.gpr .x20 = s.gpr .x1
  x21 : t.gpr .x21 = s.gpr .x3
  x22 : t.gpr .x22 = ((s.gpr .x6).setWidth 32).setWidth 64
  hi : ∀ r ∈ [Reg.x23, .x24, .x25, .x26, .x27, .x28], t.gpr r = s.gpr r
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  sv : Spill.Saved (fb s) s.gpr saved t.mem

/-- After the call: `Mid`, and `EM₁` written with RSAVP1's result. -/
structure AfterCall (s t : State) : Prop extends Mid s t where
  res : Spec.Rsa.written t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .x3).toNat ((t.gpr .x0).setWidth 32) (pubOut s)

/-- `EM₁` is in the frame. -/
theorem em1_sub {K : Nat} {s : State} (hp : PreR K s) : Region.Sub (em1R s) (kR K s) :=
  frame_sub K s (by have := hp.k2; unfold oEM1 frameBytes; omega)

theorem pubOk_of (c : PubChecked) {s t : State} (hp : PreR c.stack s) (ha : AtCall s t)
    (hsig : stackArg s 0 = s.gpr .x3) : PubOk c.stack t := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hfb := fb_toNat hp
  have hkb := kb_toNat hp
  have hcl := c.le
  have hem : em1R s = ⟨kb c.stack s + BitVec.ofNat 64 (c.stack + oEM1), (s.gpr .x3).toNat⟩ := by
    rw [em1R, off_fb c.stack]
  have hfK : fb s - BitVec.ofNat 64 c.stack = kb c.stack s := by rw [fb_eq c.stack, BitVec.add_sub_cancel]
  have hgK : (kR c.stack s).Disjoint ⟨s.gpr .x7, (s.gpr .x3).toNat⟩ := by have := hp.kg; rwa [gR, hsig] at this
  have hgS : (⟨s.gpr .x7, (s.gpr .x3).toNat⟩ : Region).Disjoint (sR s) := by have := hp.gs; rwa [gR, hsig] at this
  have hfb80 : (fb s + BitVec.ofNat 64 oEM1).toNat = (fb s).toNat + oEM1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oEM1 frameBytes at *; omega
  have hkK : Region.Sub ⟨kb c.stack s, c.stack⟩ (kR c.stack s) := Region.sub_prefix (by unfold stk; omega)
  have ha16 : (⟨fb s, 16⟩ : Region) = ⟨kb c.stack s + BitVec.ofNat 64 c.stack, 16⟩ := by rw [fb_eq c.stack]
  refine ⟨?hl, ?hrd, ?hwr, ?hk, ?h1, ?h7, ?he1, ?he2, ?hs⟩
  case hl =>
    rw [ha.x0, ha.x2, ha.x4, ha.x6, ha.x1, ha.x3, ha.x5, ha.x7, ha.a0, ha.a1, ha.sp]
    exact {
      sp1 := by unfold stk at *; omega
      sp2 := by omega
      on := hp.kn.sub_left (em1_sub hp)
      oe := hp.ke.sub_left (em1_sub hp)
      oi := hgK.sub_left (em1_sub hp)
      os := hp.ks.sub_left (em1_sub hp)
      oa := Offset.disjoint_base (fb s) (by decide) (by unfold oEM1 frameBytes at *; omega)
      ns := hp.ns
      es := hp.es
      is := hgS
      sa := (hp.ks.sub_left fun a h => frame_sub0 c.stack s a (Region.sub_prefix (by decide) a h)).symm
      ko := by
        rw [hfK]; have := hem; simp only [em1R] at this; rw [this]
        exact Offset.base_disjoint _ (by unfold oEM1; omega) (by unfold oEM1 stk frameBytes at *; omega)
      kn := by rw [hfK]; exact hp.kn.sub_left hkK
      ke := by rw [hfK]; exact hp.ke.sub_left hkK
      ki := by rw [hfK]; exact hgK.sub_left hkK
      ks := by rw [hfK]; exact hp.ks.sub_left hkK
      ka := by rw [hfK, ha16]; exact Offset.base_disjoint _ (by omega) (by unfold stk at *; omega)
      wo := by rw [hfb80]; unfold oEM1 frameBytes at *; omega
      wn := hp.wn
      we := hp.we
      wi := by have := hp.wg; rwa [hsig] at this
      ws := hp.ws }
  case hrd =>
    simp only [pubRd]
    rw [ha.x2, ha.x3, ha.x4, ha.x5, ha.x6, ha.x7, ha.sp, ha.rd, ha.wr]
    have hm : ∀ r ∈ [nR s, eR s, gR s, aR s], Covers [r] (s.rd ++ (⟨fb s, frameBytes⟩ :: s.wr)) :=
      fun r hr => Covers.left (Covers.trans (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; exact hr) hp.hrd)
    refine Covers.cons (hm _ (by simp)) (Covers.cons (hm _ (by simp)) (Covers.cons ?_
      (Covers.right (Covers.one (in_frame0 _ _ (by decide))))))
    have := hm (gR s) (by simp); rwa [gR, hsig] at this
  case hwr =>
    simp only [pubWr]
    rw [ha.x0, ha.x1, ha.a0, ha.a1, ha.wr]
    exact Covers.cons (Covers.one (in_frame _ _ (by unfold oEM1 frameBytes; omega)))
      (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; exact List.mem_cons_of_mem _ hp.hws)
  case hk => rw [ha.x3]; exact ⟨hk1, hk2⟩
  case h1 => rw [ha.x1, ha.x3]
  case h7 => rw [ha.x7, ha.x3]
  case he1 => rw [ha.x5]; exact hp.e1
  case he2 => rw [ha.x5, ha.x3]; exact hp.e2
  case hs => rw [ha.x3, ha.a1]; unfold Spec.Rsa.scratchWords; exact hp.hs

/-- The bytes of `n`, `e` and the signature at the call are the entry
state's. -/
theorem call_bytes {K : Nat} {s t : State} (hp : PreR K s) (ha : AtCall s t) (hsig : stackArg s 0 = s.gpr .x3) :
    Spec.Rsa.bytesAt t.mem (t.gpr .x2) (t.gpr .x3).toNat = Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat ∧
    Spec.Rsa.bytesAt t.mem (t.gpr .x4) (t.gpr .x5).toNat = Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat ∧
    Spec.Rsa.bytesAt t.mem (t.gpr .x6) (t.gpr .x3).toNat = Spec.Rsa.bytesAt s.mem (s.gpr .x7) (s.gpr .x3).toNat := by
  have hfr0 : Frame [kR K s, sR s] s.mem t.mem := ha.mem.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_sub0 K s⟩
  have hgK : (kR K s).Disjoint ⟨s.gpr .x7, (s.gpr .x3).toNat⟩ := by have := hp.kg; rwa [gR, hsig] at this
  have hgS : (⟨s.gpr .x7, (s.gpr .x3).toNat⟩ : Region).Disjoint (sR s) := by have := hp.gs; rwa [gR, hsig] at this
  have := hp.wn; have := hp.we; have := hp.wg; rw [hsig] at this
  rw [ha.x2, ha.x3, ha.x4, ha.x5, ha.x6]
  exact ⟨bytes_of_frame hfr0 hp.kn hp.ns.symm (by omega), bytes_of_frame hfr0 hp.ke hp.es.symm (by omega),
    bytes_of_frame hfr0 hgK hgS.symm (by omega)⟩

theorem call_ok (c : PubChecked) {s t : State} (hp : PreR c.stack s) (ha : AtCall s t)
    (hsig : stackArg s 0 = s.gpr .x3) :
    WP isa (.call c.name c.code) t (AfterCall s) := by
  have hk2 := hp.k2
  have hfb := fb_toNat hp
  have hkb := kb_toNat hp
  have hcl := c.le
  refine pubCall c (pubOk_of c hp ha hsig) ?hQ
  case hQ =>
    intro s' hrd' hwr' hsp' hf hpres hvs hpost
    simp only [pubWr] at hf
    rw [ha.x0, ha.x1, ha.a0, ha.a1, ha.sp] at hf
    have hd := c.depth
    obtain ⟨bn, be, bg⟩ := call_bytes hp ha hsig
    rw [bn, be, bg, ha.x0, ha.x3] at hpost
    exact {
      sp := hsp'.trans ha.sp
      rd := hrd'.trans ha.rd
      wr := hwr'.trans ha.wr
      x19 := (hpres .x19 (by decide) (by decide)).trans ha.x19
      x20 := (hpres .x20 (by decide) (by decide)).trans ha.x20
      x21 := (hpres .x21 (by decide) (by decide)).trans ha.x21
      x22 := (hpres .x22 (by decide) (by decide)).trans ha.x22
      hi := fun r hr => (hpres r (by revert r; decide) (by revert r; decide)).trans (ha.hi r hr)
      v := fun r hr => (hvs r hr).trans (ha.v r hr)
      sv := ha.sv.frame_in saved_offs hf fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.disjoint _ (by unfold oEM1; omega) (by decide) (by unfold oEM1; omega)
        · exact hp.ks.sub_left (frame_sub c.stack s (d := 16) (n := 40) (by decide))
        · exact Offset.disjoint_below (fb s) (by omega)
      res := hpost }

end VG.Proof.RsaPkcs1Sig.AArch64.Rec
