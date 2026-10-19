module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.AArch64.RecoverPrecomputed
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecoverCall
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.PrecomputedCorrect
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block

/-!
# `vg_rsa_pkcs1_recover_precomputed` on AArch64: the call

As `vg_rsa_pkcs1_recover`'s (`RecoverCall.lean`), with `pre` and `pre_len`
for the modulus (`AtCallP`, as for `vg_rsa_pkcs1_verify_precomputed`): the
precomputed public operation writes RSAVP1's result to `EM₁` if `pre` holds
the modulus' values (`AfterCallP`), and keeps `Mid` whatever it holds.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.AArch64.RecPc

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.RecoverPrecomputed
open VG.Impl.RsaPkcs1Sig.AArch64.Verify (frameBytes oEM1 oEM2 saved)
open VG.Proof.RsaPkcs1Sig.AArch64.Ver (stk sR aR kR fb kb fb_eq off_fb frame_sub frame_sub0 in_frame in_frame0
  saved_offs stackArgAddr_eq stackArgAddr_fb keep_of_frame bytes_of_frame)
open VG.Proof.RsaPkcs1Sig.AArch64.Rec (PreR oR nR eR gR AtCall Mid pubOut em1R em1_sub fb_toNat kb_toNat)
open VG.Proof.RsaPkcs1Sig.AArch64.Pc (pR a40 stackArgs_five a24_sub words_of_frame)
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_ldrSp PdChecked PdOk pdCall)

/-- `recoverPrecomputedContract.pre`, by name: `vg_rsa_pkcs1_recover`'s
(`PreR`), and the precomputed values. -/
structure PrePR (K : Nat) (s : State) : Prop where
  r : PreR K s
  ra : Covers [pR s, a40 s] s.rd
  sp : (sR s).Disjoint (pR s)
  kp : (kR K s).Disjoint (pR s)
  ka : (kR K s).Disjoint (a40 s)
  sp2 : s.sp.toNat + 40 ≤ 2 ^ 64
  wp : (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64
  hl : (stackArg s 4).toNat = Spec.Rsa.precomputedWords (s.gpr .x3).toNat

theorem prePR_of {K : Nat} {s : State}
    (h : (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi (stk K)).pre s) : PrePR K s := by
  have e : stk K = (frameBytes + K - 1) + 1 := by unfold stk frameBytes; omega
  rw [e] at h
  sig_pre [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig, abi, argRegs,
    stackArgs_five, List.append_eq] at h
  sig_pre [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig, abi, argRegs,
    stackArgs_five, List.append_eq] at h
  obtain ⟨sp1, sp2, hrd, hwr, on, oe, og, os, op, oa, ns, es, gs, sp, sa, ko, kn, ke, kg, ks, kp, ka, wo, wn, we,
    wg, ws, wp, ⟨k1, k2⟩, e1, e2, hh, hs, hl⟩ := h
  rw [← e] at sp1 ko kn ke kg ks kp ka
  refine ⟨⟨sp1, by omega, ?_, by rw [hwr]; simp, by rw [hwr]; simp, on, oe, og, os, oa.sub_right (a24_sub s),
    ns, es, gs, sa.sub_right (a24_sub s), ko, kn, ke, kg, ks, ka.sub_right (a24_sub s), wo, wn, we, wg, ws, k1,
    k2, e1, e2, hh, hs⟩, ?_, sp, kp, ka, sp2, wp, hl⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨nR s, by rw [hrd]; simp, 0, by simp, by simp⟩
    · exact ⟨eR s, by rw [hrd]; simp, 0, by simp, by simp⟩
    · exact ⟨gR s, by rw [hrd]; simp, 0, by simp, by simp⟩
    · exact ⟨a40 s, by rw [hrd]; simp, 0, by simp, by simp⟩
  · exact Covers.of_mem fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> rw [hrd] <;> simp

/-! ## The call -/

/-- At the call: `vg_rsa_pkcs1_recover`'s state at its call (`AtCall`), but
for `pre` and `pre_len` in `x2` and `x3`. -/
structure AtCallP (s t : State) : Prop where
  base : ∃ t₀, AtCall s t₀ ∧ Only [.x2, .x3] t₀ t
  x2 : t.gpr .x2 = stackArg s 3
  x3 : t.gpr .x3 = stackArg s 4

/-- A stack argument, in memory changed only in the frame. -/
theorem arg_frameP {K : Nat} {s : State} (hp : PrePR K s) {m : Mem} (h : Frame [⟨fb s, frameBytes⟩] s.mem m)
    {j : Nat} (hj : j < 5) : m.readW (stackArgAddr s j) 64 = stackArg s j :=
  h.readW (r := a40 s) (by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega))
    (keep_of_frame hp.ka) (by decide)

theorem arg_inP {K : Nat} {s : State} (hp : PrePR K s) {rs : List Region} (hrd : Covers s.rd rs) {j : Nat}
    (hj : j < 5) : InRegions rs (stackArgAddr s j) 8 :=
  hrd _ _ <| hp.ra _ _ ⟨a40 s, by simp, by
    rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩

theorem pubArgs_okP {K : Nat} {s u : State} (hp : PrePR K s) (hsp : u.sp = fb s) (hrd : u.rd = s.rd)
    (hwr : u.wr = ⟨fb s, frameBytes⟩ :: s.wr) (hm : u.mem = s.mem) (hg : ∀ r, r ≠ .x8 → u.gpr r = s.gpr r)
    (hv : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) :
    WP isa (.block pubArgs) u (AtCallP s) := by
  unfold pubArgs
  rw [WP.block_append_iff]
  refine WP.mono (Rec.pubArgs_ok hp.r hsp hrd hwr hm hg hv) fun t ht => ?_
  have a3 : t.sp + BitVec.ofNat 64 (frameBytes + 24) = stackArgAddr s 3 := by rw [ht.sp, stackArgAddr_fb]
  have a4 : t.sp + BitVec.ofNat 64 (frameBytes + 32) = stackArgAddr s 4 := by rw [ht.sp, stackArgAddr_fb]
  refine wp_ldrSp (by decide) (by rw [a3, ht.rd]; exact arg_inP hp (Covers.left (Covers.refl _)) (by decide))
    fun t₁ o₁ e₁ => wp_ldrSp (by decide) (by
      rw [o₁.sp, o₁.rd, o₁.wr, a4, ht.rd]; exact arg_inP hp (Covers.left (Covers.refl _)) (by decide))
    fun t₂ o₂ e₂ => wp_nil ⟨⟨t, ht, (o₁.trans o₂).mono⟩, ?_, ?_⟩
  · rw [o₂.get .x2, e₁, a3, arg_frameP hp ht.mem (by decide)]
  · rw [e₂, o₁.sp, a4, o₁.mem, arg_frameP hp ht.mem (by decide)]

theorem pdOk_of (c : PdChecked) {s t : State} (hp : PrePR c.stack s) (hc : AtCallP s t)
    (hsig : stackArg s 0 = s.gpr .x3) : PdOk c.stack t := by
  obtain ⟨⟨t₀, ha, o⟩, hx2, hx3⟩ := hc
  have hv := hp.r
  have hk1 := hv.k1; have hk2 := hv.k2
  have hfb := fb_toNat hv
  have hkb := kb_toNat hv
  have hcl := c.le
  have hem : em1R s = ⟨kb c.stack s + BitVec.ofNat 64 (c.stack + oEM1), (s.gpr .x3).toNat⟩ := by
    rw [em1R, off_fb c.stack]
  have hfK : fb s - BitVec.ofNat 64 c.stack = kb c.stack s := by rw [fb_eq c.stack, BitVec.add_sub_cancel]
  have hgK : (kR c.stack s).Disjoint ⟨s.gpr .x7, (s.gpr .x3).toNat⟩ := by have := hv.kg; rwa [gR, hsig] at this
  have hgS : (⟨s.gpr .x7, (s.gpr .x3).toNat⟩ : Region).Disjoint (sR s) := by have := hv.gs; rwa [gR, hsig] at this
  have hfb80 : (fb s + BitVec.ofNat 64 oEM1).toNat = (fb s).toNat + oEM1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oEM1 frameBytes at *; omega
  have hkK : Region.Sub ⟨kb c.stack s, c.stack⟩ (kR c.stack s) := Region.sub_prefix (by unfold stk; omega)
  have ha16 : (⟨fb s, 16⟩ : Region) = ⟨kb c.stack s + BitVec.ofNat 64 c.stack, 16⟩ := by rw [fb_eq c.stack]
  have g : ∀ r ∈ [Reg.x0, .x1, .x4, .x5, .x6, .x7], t.gpr r = t₀.gpr r := fun r hr =>
    o.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
                rcases hr with h | h | h | h | h | h <;> subst h <;> decide)
  have x0 : t.gpr .x0 = fb s + BitVec.ofNat 64 oEM1 := (g .x0 (by simp)).trans ha.x0
  have x1 : t.gpr .x1 = s.gpr .x3 := (g .x1 (by simp)).trans ha.x1
  have x4 : t.gpr .x4 = s.gpr .x4 := (g .x4 (by simp)).trans ha.x4
  have x5 : t.gpr .x5 = s.gpr .x5 := (g .x5 (by simp)).trans ha.x5
  have x6 : t.gpr .x6 = s.gpr .x7 := (g .x6 (by simp)).trans ha.x6
  have x7 : t.gpr .x7 = s.gpr .x3 := (g .x7 (by simp)).trans ha.x7
  have sp : t.sp = fb s := o.sp.trans ha.sp
  have a0 : stackArg t 0 = stackArg s 1 := by
    rw [← ha.a0]; simp only [stackArg, stackArgAddr, o.sp, o.mem]
  have a1 : stackArg t 1 = stackArg s 2 := by
    rw [← ha.a1]; simp only [stackArg, stackArgAddr, o.sp, o.mem]
  have hl4 := hp.hl
  refine ⟨?hl, ?hrd, ?hwr, ?hk, ?h3, ?h7, ?he1, ?he2, ?hs⟩
  case hl =>
    rw [x0, hx2, x4, x6, x1, hx3, x5, x7, a0, a1, sp]
    exact {
      sp1 := by unfold stk at *; omega
      sp2 := by omega
      on := hp.kp.sub_left (em1_sub hv)
      oe := hv.ke.sub_left (em1_sub hv)
      oi := hgK.sub_left (em1_sub hv)
      os := hv.ks.sub_left (em1_sub hv)
      oa := Offset.disjoint_base (fb s) (by decide) (by unfold oEM1 frameBytes at *; omega)
      ns := hp.sp.symm
      es := hv.es
      is := hgS
      sa := (hv.ks.sub_left fun a h => frame_sub0 c.stack s a (Region.sub_prefix (by decide) a h)).symm
      ko := by
        rw [hfK]; have := hem; simp only [em1R] at this; rw [this]
        exact Offset.base_disjoint _ (by unfold oEM1; omega) (by unfold oEM1 stk frameBytes at *; omega)
      kn := by rw [hfK]; exact hp.kp.sub_left hkK
      ke := by rw [hfK]; exact hv.ke.sub_left hkK
      ki := by rw [hfK]; exact hgK.sub_left hkK
      ks := by rw [hfK]; exact hv.ks.sub_left hkK
      ka := by rw [hfK, ha16]; exact Offset.base_disjoint _ (by omega) (by unfold stk at *; omega)
      wo := by rw [hfb80]; unfold oEM1 frameBytes at *; omega
      wn := hp.wp
      we := hv.we
      wi := by have := hv.wg; rwa [hsig] at this
      ws := hv.ws }
  case hrd =>
    simp only [VG.Proof.RsaPkcs1Sig.AArch64.pdRd]
    rw [hx2, hx3, x4, x5, x6, x7, sp, o.rd, ha.rd, o.wr, ha.wr]
    have hm : ∀ r ∈ [nR s, eR s, gR s, aR s], Covers [r] (s.rd ++ (⟨fb s, frameBytes⟩ :: s.wr)) :=
      fun r hr => Covers.left (Covers.trans (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; exact hr)
        hv.hrd)
    refine Covers.cons (Covers.left (Covers.trans (Covers.of_mem fun x hx => by
      rw [List.mem_singleton.mp hx]; simp) hp.ra)) (Covers.cons (hm _ (by simp)) (Covers.cons ?_
      (Covers.right (Covers.one (in_frame0 _ _ (by decide))))))
    have := hm (gR s) (by simp); rwa [gR, hsig] at this
  case hwr =>
    simp only [VG.Proof.RsaPkcs1Sig.AArch64.pubWr]
    rw [x0, x1, a0, a1, o.wr, ha.wr]
    exact Covers.cons (Covers.one (in_frame _ _ (by unfold oEM1 frameBytes; omega)))
      (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; exact List.mem_cons_of_mem _ hv.hws)
  case hk => rw [x1]; exact ⟨hk1, hk2⟩
  case h3 => rw [hx3, x1]; exact hl4
  case h7 => rw [x7, x1]
  case he1 => rw [x5]; exact hv.e1
  case he2 => rw [x5, x1]; exact hv.e2
  case hs => rw [x1, a1]; exact hv.hs

/-- Whether `pre` holds the values for `n`. -/
def Consistent (s : State) : Prop :=
  Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 3) (stackArg s 4).toNat)

/-- After the call: `Mid`, and `EM₁` written with RSAVP1's result if `pre`
holds the modulus' values. -/
structure AfterCallP (s t : State) : Prop extends Mid s t where
  res : Consistent s →
    Spec.Rsa.written t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .x3).toNat ((t.gpr .x0).setWidth 32) (pubOut s)

theorem callP_ok (c : PdChecked) {s t : State} (hp : PrePR c.stack s) (hc : AtCallP s t)
    (hsig : stackArg s 0 = s.gpr .x3) :
    WP isa (.call c.name c.code) t (AfterCallP s) := by
  have hv := hp.r
  have hd := c.depth
  have hcl := c.le
  have hk2 := hv.k2
  have hfb := fb_toNat hv
  have hkb := kb_toNat hv
  obtain ⟨⟨t₀, ha, o⟩, hx2, hx3⟩ := hc
  refine pdCall c (pdOk_of c hp ⟨⟨t₀, ha, o⟩, hx2, hx3⟩ hsig) fun s' hrd' hwr' hsp' hf hpres hvs hpost => ?_
  have g : ∀ r ∈ [Reg.x0, .x1, .x4, .x5, .x6, .x7], t.gpr r = t₀.gpr r := fun r hr =>
    o.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
                rcases hr with h | h | h | h | h | h <;> subst h <;> decide)
  have x0 : t.gpr .x0 = fb s + BitVec.ofNat 64 oEM1 := (g .x0 (by simp)).trans ha.x0
  have x1 : t.gpr .x1 = s.gpr .x3 := (g .x1 (by simp)).trans ha.x1
  have x4 : t.gpr .x4 = s.gpr .x4 := (g .x4 (by simp)).trans ha.x4
  have x5 : t.gpr .x5 = s.gpr .x5 := (g .x5 (by simp)).trans ha.x5
  have x6 : t.gpr .x6 = s.gpr .x7 := (g .x6 (by simp)).trans ha.x6
  have sp : t.sp = fb s := o.sp.trans ha.sp
  have a0 : stackArg t 0 = stackArg s 1 := by
    rw [← ha.a0]; simp only [stackArg, stackArgAddr, o.sp, o.mem]
  have a1 : stackArg t 1 = stackArg s 2 := by
    rw [← ha.a1]; simp only [stackArg, stackArgAddr, o.sp, o.mem]
  simp only [VG.Proof.RsaPkcs1Sig.AArch64.pubWr] at hf
  rw [x0, x1, a0, a1, sp] at hf
  have hfr0 : Frame [kR c.stack s, sR s] s.mem t.mem := by
    rw [o.mem]
    exact ha.mem.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_sub0 c.stack s⟩
  have hgK : (kR c.stack s).Disjoint ⟨s.gpr .x7, (s.gpr .x3).toNat⟩ := by have := hv.kg; rwa [gR, hsig] at this
  have hgS : (⟨s.gpr .x7, (s.gpr .x3).toNat⟩ : Region).Disjoint (sR s) := by have := hv.gs; rwa [gR, hsig] at this
  refine {
    sp := hsp'.trans sp
    rd := hrd'.trans (o.rd.trans ha.rd)
    wr := hwr'.trans (o.wr.trans ha.wr)
    x19 := (hpres .x19 (by decide) (by decide)).trans ((o.get .x19).trans ha.x19)
    x20 := (hpres .x20 (by decide) (by decide)).trans ((o.get .x20).trans ha.x20)
    x21 := (hpres .x21 (by decide) (by decide)).trans ((o.get .x21).trans ha.x21)
    x22 := (hpres .x22 (by decide) (by decide)).trans ((o.get .x22).trans ha.x22)
    hi := fun r hr => (hpres r (by revert r; decide) (by revert r; decide)).trans
      ((o.gpr r (by revert r; decide)).trans (ha.hi r hr))
    v := fun r hr => (hvs r hr).trans ((o.vcs r hr).trans (ha.v r hr))
    sv := by
      rw [o.mem] at hf
      exact ha.sv.frame_in saved_offs hf fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.disjoint _ (by unfold oEM1; omega) (by decide) (by unfold oEM1; omega)
        · exact hv.ks.sub_left (frame_sub c.stack s (d := 16) (n := 40) (by decide))
        · exact Offset.disjoint_below (fb s) (by omega)
    res := fun hq => ?_ }
  have hw : Spec.Rsa.wordsAt t.mem (t.gpr .x2) (t.gpr .x3).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 3) (stackArg s 4).toNat := by
    rw [hx2, hx3]; exact words_of_frame hfr0 hp.kp hp.sp hp.wp
  have := hpost (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (by rw [x1, VG.Proof.RsaPkcs1Sig.bytesAt_length])
    (by rw [hw]; exact hq)
  rw [x0, x1, x4, x5, x6, bytes_of_frame hfr0 hv.ke hv.es.symm (by have := hv.we; omega),
    bytes_of_frame hfr0 hgK hgS.symm (by have := hv.wg; rw [hsig] at this; omega)] at this
  exact this

end VG.Proof.RsaPkcs1Sig.AArch64.RecPc
