module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecoverCorrect
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.RsaPkcs1Sig.AArch64.RecoverPrecomputed
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecoverCall
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.PrecomputedCorrect

/-! ### `RsaPkcs1Sig.AArch64.RecPcCall`, which this module and modules that import it used -/

section

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
  have e : stk K = (frameBytes + K - 1) + 1 := by unfold stk frameBytes; omega_arith
  rw [e] at h
  sig_pre [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig, abi, argRegs,
    stackArgs_five, List.append_eq, List.range, List.range.loop] at h
  obtain ⟨sp1, sp2, hrd, hwr, on, oe, og, os, op, oa, ns, es, gs, sp, sa, ko, kn, ke, kg, ks, kp, ka, wo, wn, we,
    wg, ws, wp, ⟨k1, k2⟩, e1, e2, hh, hs, hl⟩ := h
  rw [← e] at sp1 ko kn ke kg ks kp ka
  refine ⟨⟨sp1, by omega_arith, ?_, by rw [hwr]; simp, by rw [hwr]; simp, on, oe, og, os, oa.sub_right (a24_sub s),
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
  h.readW (r := a40 s) (by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_arith) (by omega_arith))
    (keep_of_frame hp.ka) (by decide)

theorem arg_inP {K : Nat} {s : State} (hp : PrePR K s) {rs : List Region} (hrd : Covers s.rd rs) {j : Nat}
    (hj : j < 5) : InRegions rs (stackArgAddr s j) 8 :=
  hrd _ _ <| hp.ra _ _ ⟨a40 s, by simp, by
    rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

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
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oEM1 frameBytes at *; omega_arith
  have hkK : Region.Sub ⟨kb c.stack s, c.stack⟩ (kR c.stack s) := Region.sub_prefix (by unfold stk; omega_arith)
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
      sp1 := by unfold stk at *; omega_arith
      sp2 := by omega_arith
      on := hp.kp.sub_left (em1_sub hv)
      oe := hv.ke.sub_left (em1_sub hv)
      oi := hgK.sub_left (em1_sub hv)
      os := hv.ks.sub_left (em1_sub hv)
      oa := Offset.disjoint_base (fb s) (by decide) (by unfold oEM1 frameBytes at *; omega_arith)
      ns := hp.sp.symm
      es := hv.es
      is := hgS
      sa := (hv.ks.sub_left fun a h => frame_sub0 c.stack s a (Region.sub_prefix (by decide) a h)).symm
      ko := by
        rw [hfK]; have := hem; simp only [em1R] at this; rw [this]
        exact Offset.base_disjoint _ (by unfold oEM1; omega_arith) (by unfold oEM1 stk frameBytes at *; omega_arith)
      kn := by rw [hfK]; exact hp.kp.sub_left hkK
      ke := by rw [hfK]; exact hv.ke.sub_left hkK
      ki := by rw [hfK]; exact hgK.sub_left hkK
      ks := by rw [hfK]; exact hv.ks.sub_left hkK
      ka := by rw [hfK, ha16]; exact Offset.base_disjoint _ (by omega_arith) (by unfold stk at *; omega_arith)
      wo := by rw [hfb80]; unfold oEM1 frameBytes at *; omega_arith
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
    exact Covers.cons (Covers.one (in_frame _ _ (by unfold oEM1 frameBytes; omega_arith)))
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
        · exact Offset.disjoint _ (by unfold oEM1; omega_arith) (by decide) (by unfold oEM1; omega_arith)
        · exact hv.ks.sub_left (frame_sub c.stack s (d := 16) (n := 40) (by decide))
        · exact Offset.disjoint_below (fb s) (by omega_arith)
    res := fun hq => ?_ }
  have hw : Spec.Rsa.wordsAt t.mem (t.gpr .x2) (t.gpr .x3).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 3) (stackArg s 4).toNat := by
    rw [hx2, hx3]; exact words_of_frame hfr0 hp.kp hp.sp hp.wp
  have := hpost (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (by rw [x1, VG.Proof.RsaPkcs1Sig.bytesAt_length])
    (by rw [hw]; exact hq)
  rw [x0, x1, x4, x5, x6, bytes_of_frame hfr0 hv.ke hv.es.symm (by have := hv.we; omega_arith),
    bytes_of_frame hfr0 hgK hgS.symm (by have := hv.wg; rw [hsig] at this; omega_arith)] at this
  exact this

end VG.Proof.RsaPkcs1Sig.AArch64.RecPc

end

end

/-!
# `vg_rsa_pkcs1_recover_precomputed` on AArch64: after the call

Whatever the call left in `EM₁` and its status: the status is kept in the
frame's word at `oSt`; `EM₁`'s last `out_len` bytes are encoded into `EM₂`
and, if that succeeds, compared with `EM₁` (`vg_rsa_pkcs1_recover`'s
pieces); the mask, all ones exactly when they are equal and the status is
not 0, goes to the frame's word at `oMk` (`maskM_ok`); the value is copied to
`out` and masked (`maskLoop_ok`), and the result is 1 under the mask. With
the status and `EM₁` the call writes if `pre` holds the modulus' values,
this is `vg_rsa_pkcs1_recover`'s result (`afterPub_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.AArch64.RecPc

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.RecoverPrecomputed VG.WriteBytes
open VG.Impl.RsaPkcs1Sig.AArch64 (encode compare)
open VG.Impl.RsaPkcs1Sig.AArch64.Verify (frameBytes oEM1 oEM2 saved)
open VG.Impl.RsaPkcs1Sig.AArch64.Recover (zeroKept copyOut encArgs cmpArgs)
open VG.Proof.RsaPkcs1Sig.AArch64.Ver (stk sR kR fb frame_sub in_frame in_frame0)
open VG.Proof.RsaPkcs1Sig.AArch64.Rec (PreR oR Mid pubOut hlen valA slots_out out_wr copyOut_ok AtEnc AfterEnc
  AtCmp AfterCmp encRes recOut zeroKept_ok)
open VG.Proof.RsaPkcs1Sig.AArch64.Ver (eval_zero')
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_ldrx wp_strx wp_ldrb wp_strb wp_addImm
  wp_subImm wp_and only_write)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp wp_mov)
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_writeBytes frame_writeBytes bytes_apart writeBytes_out)

/-! ## Masks -/

theorem add_not_self (r : BitVec 64) : r + ~~~r = BitVec.allOnes 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_allOnes]
  have := r.isLt
  rw [Nat.mod_eq_of_lt (by omega_arith)]; omega_arith

theorem sbc_carry (r : BitVec 64) (c : Bool) :
    r + ~~~r + BitVec.ofNat 64 c.toNat = if c then 0 else BitVec.allOnes 64 := by
  rw [add_not_self]; cases c <;> decide

/-- The carry of `a - 1`: no borrow exactly when `a` is not 0. -/
theorem carry_sub1 {n : Nat} (hn : 0 < n) (a : BitVec n) :
    (2 ^ n ≤ a.toNat + (~~~(1 : BitVec n)).toNat + true.toNat) ↔ a.toNat ≠ 0 := by
  have h1 : (1 : BitVec n).toNat = 1 := by
    show (BitVec.ofNat n 1).toNat = 1
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega_arith))
  rw [BitVec.toNat_not, h1]
  have := a.isLt
  have hp : 2 ≤ 2 ^ n := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hn; simpa using this
  simp only [Bool.toNat_true]
  omega_arith

theorem setWidth_one (sz : Size) : ((1 : BitVec 64).setWidth sz.bits) = 1 := by
  cases sz <;> rfl

theorem bits_pos (sz : Size) : 0 < sz.bits := by cases sz <;> decide

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `d ← -(d = 0)`, from the low `sz` bits of `d`, with `1` in `m`. -/
theorem wp_isZero {sz : Size} {d m : Reg} (h1 : s.gpr m = 1)
    (k : ∀ s', Only [d] s s' → s'.gpr d = (if s.read sz d = 0 then BitVec.allOnes 64 else 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.subs sz d d m :: .sbc .x d d d :: is)) s Q := by
  refine VG.Proof.MlKem.AArch64.WP.cons rfl (VG.Proof.MlKem.AArch64.WP.cons rfl
    (k _ ⟨fun r hr => ?_, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩ ?_))
  · have hr' : r ≠ d := fun h => hr (by simp [h])
    simp only [State.write, State.addWithCarry, hr', ite_false]
  · simp only [State.write, State.addWithCarry, State.read, ite_true, BitVec.setWidth_eq, h1, setWidth_one,
      sbc_carry]
    have hc := carry_sub1 (bits_pos sz) ((s.gpr d).setWidth sz.bits)
    by_cases h : (s.gpr d).setWidth sz.bits = 0
    · have : ¬ (2 ^ sz.bits ≤ ((s.gpr d).setWidth sz.bits).toNat + (~~~(1 : BitVec sz.bits)).toNat +
          true.toNat) := fun h' => hc.mp h' (by rw [h]; rfl)
      rw [decide_eq_false this]
      simp only [Bool.false_eq_true, ↓reduceIte, h]
    · have : 2 ^ sz.bits ≤ ((s.gpr d).setWidth sz.bits).toNat + (~~~(1 : BitVec sz.bits)).toNat +
          true.toNat := hc.mpr fun h' => h (BitVec.eq_of_toNat_eq (by rw [h']; rfl))
      rw [decide_eq_true this]
      simp only [↓reduceIte, h]

theorem rotateRight_zero (x : BitVec 64) : x.rotateRight 0 = x := by
  ext i hi; simp [BitVec.getElem_rotateRight, hi]

theorem wp_bic {d n m : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = (s.gpr n &&& ~~~(s.gpr m)) → WP isa (.block is) s' Q) :
    WP isa (.block (.bicRor .x d n m 0 :: is)) s Q :=
  VG.Proof.MlKem.AArch64.wp_x (by simp [exec, State.read, rotateRight_zero]) k

end

/-- The mask from the comparison's difference `d` and the status `st`. -/
def mk (d st : BitVec 64) : BitVec 64 := if d = 0 ∧ st.setWidth 32 ≠ 0 then BitVec.allOnes 64 else 0

theorem mk_eq (d st : BitVec 64) :
    ((if d.setWidth 64 = 0 then BitVec.allOnes 64 else 0) &&&
      ~~~(if st.setWidth 32 = 0 then BitVec.allOnes 64 else 0)) = mk d st := by
  unfold mk
  rw [BitVec.setWidth_eq]
  (repeat' split) <;> first | decide | simp_all

/-- A word of the frame is readable and writable. -/
theorem frame_rw {s t : State} (hwr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr) {d n : Nat} (h : d + n ≤ frameBytes) :
    InRegions (t.rd ++ t.wr) (fb s + BitVec.ofNat 64 d) n :=
  let ⟨r, hr, hc⟩ := Ver.wr_frame hwr h
  ⟨r, List.mem_append_right _ hr, hc⟩

/-- A word of the frame `d` bytes from its base is apart from the saved
registers' slots if it is at or after `oSt`. -/
theorem slot_saved {s : State} {d : Nat} (hd : 56 ≤ d) (hn : d + 8 ≤ frameBytes) :
    Region.Disjoint ⟨fb s + BitVec.ofNat 64 16, 40⟩ ⟨fb s + BitVec.ofNat 64 d, 8⟩ :=
  Offset.disjoint _ (by omega_arith) (by decide) (by unfold frameBytes at hn; omega_arith)

theorem slot_write {s t w : State} (hm : Mid s t) {d : Nat} (hd : 56 ≤ d) (hn : d + 8 ≤ frameBytes)
    {v : BitVec 64} (m : MemTo t w (t.mem.writeW (fb s + BitVec.ofNat 64 d) v)) : Mid s w :=
  hm.frame m.keep (R := ⟨fb s + BitVec.ofNat 64 d, 8⟩) (by
    rw [m.mem]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _))
    (slot_saved hd hn)

/-! ## The mask -/

theorem maskM_ok {s y : State} (hm : Mid s y) :
    WP isa (.block maskM) y fun z => Mid s z ∧
      z.mem = y.mem.writeW (fb s + BitVec.ofNat 64 oMk) (mk (y.gpr .x12) (y.mem.readW (fb s + BitVec.ofNat 64 oSt) 64)) := by
  unfold maskM
  refine wp_movz fun z₁ o₁ e₁ => ?_
  refine wp_isZero (sz := .x) (by rw [e₁]; rfl) fun z₂ o₂ e₂ => ?_
  refine wp_addSp (by decide) fun z₃ o₃ e₃ => ?_
  have x16 : z₃.gpr .x16 = fb s := by rw [e₃, o₂.sp, o₁.sp, hm.sp, BitVec.add_zero]
  have w₃ : z₃.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [o₃.wr, o₂.wr, o₁.wr, hm.wr]
  refine wp_ldrx (a := fb s + BitVec.ofNat 64 oSt) (by decide) (by rw [x16]) (frame_rw w₃ (by decide))
    fun z₄ o₄ e₄ => ?_
  refine wp_isZero (sz := .w) (by rw [o₄.get .x13, o₃.get .x13, o₂.get .x13, e₁]; rfl) fun z₅ o₅ e₅ => ?_
  refine wp_bic fun z₆ o₆ e₆ => ?_
  have O₆ : Only [.x13, .x12, .x16, .x8] y z₆ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans o₆))))).mono
  refine wp_strx (a := fb s + BitVec.ofNat 64 oMk) (by decide)
    (by rw [o₆.get .x16, o₅.get .x16, o₄.get .x16, x16]) (by rw [O₆.wr, hm.wr]; exact in_frame _ _ (by decide))
    fun z₇ m₇ => wp_nil ⟨slot_write (hm.only O₆) (d := oMk) (by decide) (by decide) m₇, ?_⟩
  rw [m₇.mem, e₆, O₆.mem, o₅.get .x12, e₅, o₄.get .x12, o₃.get .x12, e₂]
  simp only [State.read, e₄, o₃.mem, o₂.mem, o₁.mem, o₁.get .x12]
  rw [← mk_eq]

/-! ## Masking `out` -/

theorem and_byte (b : Byte) (x : BitVec 64) : ((b.setWidth 64) &&& x).setWidth 8 = b &&& x.setWidth 8 := by
  ext i hi; simp [show i < 64 by omega_arith]

theorem off_ne {p : Addr} {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) (hne : i ≠ j) :
    p + BitVec.ofNat 64 i ≠ p + BitVec.ofNat 64 j := fun h => by
  have h' := congrArg (· - p) h
  simp only [Offset.add_sub_cancel_left] at h'
  have := congrArg BitVec.toNat h'
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  exact hne this

/-- `maskLoop` ANDs each of the `n` bytes at `x11 = p`, counted down in `x12`,
with the low byte of `x9`. -/
theorem maskLoop_ok {s : State} {p : Addr} {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 64)
    (h11 : s.gpr .x11 = p) (h12 : s.gpr .x12 = BitVec.ofNat 64 n)
    (hw : ∀ i < n, InRegions s.wr (p + BitVec.ofNat 64 i) 1) :
    WP isa maskLoop s fun t => Keep [.x10, .x11, .x12] s t ∧
      t.mem = writeBytes s.mem p ((Spec.Rsa.bytesAt s.mem p n).map (· &&& (s.gpr .x9).setWidth 8)) := by
  refine WP.mono (VG.Proof.RsaPkcs1Sig.AArch64.wp_countdown (cnt := .x12) hn' hn
    (fun i t => Keep [.x10, .x11, .x12] s t ∧
      t.mem = writeBytes s.mem p (((Spec.Rsa.bytesAt s.mem p n).take i).map (· &&& (s.gpr .x9).setWidth 8)) ∧
      t.gpr .x11 = p + BitVec.ofNat 64 i) ?_
    ⟨Keep.refl _ _, by simp [writeBytes_nil], by simp [h11]⟩ h12) fun t h => ⟨h.1, ?_⟩
  · intro i hi t ⟨hK, hm, h11'⟩ _
    have hlt : (((Spec.Rsa.bytesAt s.mem p n).take i).map (· &&& (s.gpr .x9).setWidth 8)).length = i := by
      simp [bytesAt_length]; omega_arith
    have hR : InRegions (t.rd ++ t.wr) (t.gpr .x11 + BitVec.ofNat 64 0) 1 := by
      obtain ⟨r, hr, hc⟩ := hw i hi
      exact ⟨r, List.mem_append_right _ (by rw [hK.wr]; exact hr), by rw [h11', BitVec.add_zero]; exact hc⟩
    have hv : t.mem (p + BitVec.ofNat 64 i) = s.mem (p + BitVec.ofNat 64 i) := by
      rw [hm, writeBytes_out _ _ _ _ i (fun j hj => off_ne (by omega_arith) (by omega_arith) (by omega_arith)) (by rw [hlt])]
    refine wp_ldrb (by decide) rfl hR fun s₁ o₁ e₁ => ?_
    refine wp_and fun s₂ o₂ e₂ => ?_
    have hW : InRegions s₂.wr (s₂.gpr .x11 + BitVec.ofNat 64 0) 1 := by
      rw [o₂.wr, o₁.wr, o₂.get .x11, o₁.get .x11, h11', hK.wr, BitVec.add_zero]; exact hw i hi
    refine wp_strb (by decide) rfl hW fun s₃ m₃ => ?_
    refine wp_addImm (by decide) fun s₄ o₄ e₄ => ?_
    refine wp_subImm (by decide) fun s₅ o₅ e₅ => wp_nil ?_
    have hK' : Keep [.x10, .x11, .x12] t s₅ :=
      (o₁.keep.trans (o₂.keep.trans (m₃.keep.trans (o₄.keep.trans o₅.keep)))).mono
    refine ⟨⟨(hK.trans hK').mono, ?_, ?_⟩, ?_⟩
    · rw [o₅.mem, o₄.mem, m₃.mem, o₂.mem, e₂, o₂.get .x11, o₁.get .x11, e₁, o₁.mem, o₁.get .x9, hK.get .x9,
        h11', BitVec.add_zero, hv, and_byte, hm, bytesAt_take_succ _ _ hi, List.map_append, List.map_singleton,
        writeBytes_snoc _ _ _ _ (by rw [hlt]; omega_arith), hlt]
    · rw [o₅.get .x11, e₄, m₃.gpr, o₂.get .x11, o₁.get .x11, h11', VG.Proof.RsaPkcs1Sig.AArch64.ofNat_succ']
    · rw [e₅, o₄.get .x12, m₃.gpr, o₂.get .x12, o₁.get .x12]
  · rw [List.take_of_length_le (by simp [bytesAt_length])] at h
    exact h.2.1

/-! ## The release -/

/-- A word of the frame, after writes to `out`. -/
theorem slot_out {K : Nat} {s : State} (hp : PreR K s) {d : Nat} (hd : d + 8 ≤ frameBytes) {m : Mem}
    (xs : List Byte) (hl : xs.length = (s.gpr .x1).toNat) :
    (writeBytes m (s.gpr .x0) xs).readW (fb s + BitVec.ofNat 64 d) 64 = m.readW (fb s + BitVec.ofNat 64 d) 64 :=
  (frame_writeBytes m (s.gpr .x0) xs).readW (r := ⟨fb s + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
    (fun r hr => by
      rw [List.mem_singleton.mp hr, hl]
      exact hp.ko.sub_left (frame_sub K s hd)) (by decide)

theorem written_mask {m : Mem} {o : Addr} {n : Nat} {val : List Byte} (hl : val.length = n) (hn : n < 2 ^ 64)
    (M : BitVec 64) (hM : M = BitVec.allOnes 64 ∨ M = 0) :
    Spec.Rsa.written (writeBytes m o (val.map (· &&& M.setWidth 8))) o n ((1 &&& M).setWidth 32)
      (if M = BitVec.allOnes 64 then some val else none) := by
  have hb : Spec.Rsa.bytesAt (writeBytes m o (val.map (· &&& M.setWidth 8))) o n = val.map (· &&& M.setWidth 8) := by
    have := bytesAt_writeBytes m o (val.map (· &&& M.setWidth 8)) (by simp [hl, hn])
    rwa [List.length_map, hl] at this
  rcases hM with rfl | rfl
  · rw [ite_eq_left rfl]
    refine ⟨by decide, ?_⟩
    have ha : ∀ x : Byte, x &&& (BitVec.allOnes 64).setWidth 8 = x := fun x => by
      rw [show (BitVec.allOnes 64).setWidth 8 = BitVec.allOnes 8 from by decide, BitVec.and_allOnes]
    rw [hb]
    simp only [ha, List.map_id']
  · have h0 : ¬ (0 : BitVec 64) = BitVec.allOnes 64 := by decide
    rw [ite_eq_right h0]
    refine ⟨by decide, ?_⟩
    rw [hb, ← hl]
    simp [List.map_const']

theorem mk_cases (d st : BitVec 64) : mk d st = BitVec.allOnes 64 ∨ mk d st = 0 := by
  unfold mk
  by_cases h : d = 0 ∧ st.setWidth 32 ≠ 0
  · exact .inl (ite_eq_left h)
  · exact .inr (ite_eq_right h)

theorem mk_allOnes (d st : BitVec 64) : mk d st = BitVec.allOnes 64 ↔ d = 0 ∧ st.setWidth 32 ≠ 0 := by
  unfold mk
  by_cases h : d = 0 ∧ st.setWidth 32 ≠ 0
  · rw [ite_eq_left h]; exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [ite_eq_right h]; exact ⟨fun e => absurd e (by decide), fun h' => absurd h' h⟩

theorem release_ok {K : Nat} {s y : State} (hp : PreR K s) (hm : Mid s y) {val : List Byte}
    (hv : Spec.Rsa.bytesAt y.mem (valA s) (s.gpr .x1).toNat = val) :
    WP isa release y fun w => Mid s w ∧ Spec.Rsa.written w.mem (s.gpr .x0) (s.gpr .x1).toNat
      ((w.gpr .x0).setWidth 32)
      (if y.gpr .x12 = 0 ∧ (y.mem.readW (fb s + BitVec.ofNat 64 oSt) 64).setWidth 32 ≠ 0 then some val else none) := by
  obtain ⟨hl0, hl1⟩ := hlen hp
  have hk2 := hp.k2
  obtain ⟨M, hM⟩ : ∃ M, M = mk (y.gpr .x12) (y.mem.readW (fb s + BitVec.ofNat 64 oSt) 64) := ⟨_, rfl⟩
  have hvl : val.length = (s.gpr .x1).toNat := by rw [← hv, bytesAt_length]
  unfold release
  refine WP.seq (WP.mono (maskM_ok hm) fun z ⟨mz, hz⟩ => ?_)
  rw [← hM] at hz
  have hvz : Spec.Rsa.bytesAt z.mem (valA s) (s.gpr .x1).toNat = val := by
    rw [← hv, hz]
    refine bytes_apart (R := ⟨valA s, (s.gpr .x1).toNat⟩)
      (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)) ?_
      (by show (s.gpr .x1).toNat ≤ 2 ^ 64; omega_arith)
    show Region.Disjoint ⟨fb s + BitVec.ofNat 64 (oEM1 + ((s.gpr .x3).toNat - (s.gpr .x1).toNat)), _⟩ _
    exact Offset.disjoint _ (.inr (by unfold oEM1 oMk; omega_arith)) (by unfold oEM1; omega_arith) (by unfold oMk; omega_arith)
  refine WP.seq (WP.mono (copyOut_ok hp mz) fun w₁ ⟨m₁, wr₁, hm₁, x0₁⟩ => ?_)
  rw [hvz] at wr₁ hm₁
  have hk₁ : w₁.mem.readW (fb s + BitVec.ofNat 64 oMk) 64 = M := by
    rw [hm₁, slot_out hp (by decide) val hvl, hz]
    exact Mem.readW_writeW_self (n := 8) _ _ _ (by decide)
  have hb₁ : Spec.Rsa.bytesAt w₁.mem (s.gpr .x0) (s.gpr .x1).toNat = val := wr₁.2
  -- The mask loop's registers.
  unfold maskArgs
  refine WP.seq (wp_addSp (by decide) fun w₂ o₂ e₂ => ?_)
  have x16 : w₂.gpr .x16 = fb s := by rw [e₂, m₁.sp, BitVec.add_zero]
  have w₂w : w₂.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [o₂.wr, m₁.wr]
  refine wp_ldrx (a := fb s + BitVec.ofNat 64 oMk) (by decide) (by rw [x16]) (frame_rw w₂w (by decide))
    fun w₃ o₃ e₃ => wp_mov fun w₄ o₄ e₄ => wp_mov fun w₅ o₅ e₅ => wp_nil ?_
  have O₅ : Only [.x16, .x9, .x11, .x12] w₁ w₅ := (o₂.trans (o₃.trans (o₄.trans o₅))).mono
  have x9 : w₅.gpr .x9 = M := by rw [o₅.get .x9, o₄.get .x9, e₃, o₂.mem, hk₁]
  have x11 : w₅.gpr .x11 = s.gpr .x0 := by rw [o₅.get .x11, e₄, o₃.get .x19, o₂.get .x19, m₁.x19]
  have x12 : w₅.gpr .x12 = BitVec.ofNat 64 (s.gpr .x1).toNat := by
    rw [e₅, o₄.get .x20, o₃.get .x20, o₂.get .x20, m₁.x20, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have m₅ := m₁.only O₅
  refine WP.seq (WP.mono (maskLoop_ok hl0 (by omega_arith) x11 x12 (by rw [O₅.wr, m₁.wr]; exact out_wr hp [_]))
    fun w₆ ⟨k₆, hm₆⟩ => ?_)
  rw [O₅.mem, hb₁, x9] at hm₆
  unfold fin
  refine wp_and fun w₇ o₇ e₇ => wp_nil ⟨?_, ?_⟩
  · have m₆ : Mid s w₆ := m₅.frame k₆ (R := oR s) (by
      rw [hm₆, O₅.mem]
      have := frame_writeBytes w₁.mem (s.gpr .x0) (val.map (· &&& M.setWidth 8))
      rwa [List.length_map, hvl] at this) (slots_out hp)
    exact m₆.only o₇
  · rw [o₇.mem, hm₆, e₇, k₆.get .x0, k₆.get .x9, x9, O₅.get .x0, x0₁]
    have hif : (y.gpr .x12 = 0 ∧ (y.mem.readW (fb s + BitVec.ofNat 64 oSt) 64).setWidth 32 ≠ 0) ↔
        M = BitVec.allOnes 64 := by rw [hM, mk_allOnes]
    rw [show (if y.gpr .x12 = 0 ∧ (y.mem.readW (fb s + BitVec.ofNat 64 oSt) 64).setWidth 32 ≠ 0 then some val
        else none) = if M = BitVec.allOnes 64 then some val else none from by simp only [hif]]
    exact written_mask hvl (by omega_arith) M (hM ▸ mk_cases _ _)

/-! ## After the encoding -/

theorem cmpArgs_okP {s w : State} {h : Spec.RsaPkcs1Sig.Hash} {em em' : List Byte} (hm : Mid s w)
    (b1 : Spec.Rsa.bytesAt w.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .x3).toNat = em)
    (b2 : Spec.Rsa.bytesAt w.mem (fb s + BitVec.ofNat 64 oEM2) (s.gpr .x3).toNat = em')
    (hv : Spec.Rsa.bytesAt w.mem (valA s) (s.gpr .x1).toNat = em.drop ((s.gpr .x3).toNat - h.len)) :
    WP isa (.block cmpArgs) w fun v => AtCmp s h em em' v ∧ v.mem = w.mem := by
  unfold cmpArgs
  refine wp_addSp (by decide) fun v₁ p₁ f₁ => wp_addSp (by decide) fun v₂ p₂ f₂ =>
    wp_mov fun v₃ p₃ f₃ => wp_nil ?_
  have P₃ : Only [.x14, .x15, .x13] w v₃ := (p₁.trans (p₂.trans p₃)).mono
  refine ⟨⟨hm.only P₃, ?_, ?_, ?_, by rw [P₃.mem, b1], by rw [P₃.mem, b2], by rw [P₃.mem, hv]⟩, P₃.mem⟩
  · rw [p₃.get .x14, p₂.get .x14, f₁, hm.sp]
  · rw [p₃.get .x15, f₂, p₁.sp, hm.sp]
  · rw [f₃, p₂.get .x21, p₁.get .x21, hm.x21, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem cmp_okP {K : Nat} {s v : State} (hp : PreR K s) {h : Spec.RsaPkcs1Sig.Hash} {em em' : List Byte}
    (hv : AtCmp s h em em' v) : WP isa compare v fun y => AfterCmp s h em em' y ∧ y.mem = v.mem := by
  have hk1 := hp.k1; have hk2 := hp.k2
  refine WP.mono (VG.Proof.RsaPkcs1Sig.AArch64.compare_ok (s := v) (n := (s.gpr .x3).toNat) (by omega_arith) (by omega_arith)
    hv.x13
    (fun j hj => by rw [hv.x14]; exact Rec.frame_bytes hv.mid.wr (by unfold oEM1 frameBytes; omega_arith) j hj)
    (fun j hj => by rw [hv.x15]; exact Rec.frame_bytes hv.mid.wr (by unfold oEM2 frameBytes; omega_arith) j hj))
    fun y ⟨oy, hiff, _⟩ => ⟨⟨hv.mid.only oy, ?_, by rw [oy.mem, hv.val]⟩, oy.mem⟩
  rw [hv.x14, hv.x15, hv.b1, hv.b2] at hiff
  exact hiff

/-- The result after the encoding, from `EM₁`'s bytes `em` and the status
`st`. -/
def tailOut (s : State) (h : Spec.RsaPkcs1Sig.Hash) (em : List Byte) (st : BitVec 64) : Option (List Byte) :=
  match encRes s h em with
  | none => none
  | some em' => if em = em' ∧ st.setWidth 32 ≠ 0 then some (em.drop ((s.gpr .x3).toNat - h.len)) else none

theorem tail_ok {K : Nat} {s w : State} (hp : PreR K s) {h : Spec.RsaPkcs1Sig.Hash} {em : List Byte}
    (hw : AfterEnc s h em w) {st : BitVec 64} (hst : w.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = st) :
    WP isa tail w fun w' => Mid s w' ∧ Spec.Rsa.written w'.mem (s.gpr .x0) (s.gpr .x1).toNat
      ((w'.gpr .x0).setWidth 32) (tailOut s h em st) := by
  have hres := hw.res
  unfold tail tailOut
  cases heo : encRes s h em with
  | none =>
    rw [heo] at hres
    refine WP.ite true ((eval_zero' w .x0).trans (by rw [hres]; rfl)) (fun _ => ?_) (by simp)
    exact zeroKept_ok hp hw.mid
  | some em' =>
    rw [heo] at hres
    obtain ⟨h1, b1, b2, hv⟩ := hres
    dsimp only
    refine WP.ite false ((eval_zero' w .x0).trans (by rw [h1]; rfl)) (by simp) fun _ => ?_
    refine WP.seq (WP.mono (cmpArgs_okP hw.mid b1 b2 hv) fun v ⟨hv', mv⟩ =>
      WP.seq (WP.mono (cmp_okP hp hv') fun y ⟨hy, my⟩ => ?_))
    refine WP.mono (release_ok hp hy.mid hy.val) fun w' ⟨m', r'⟩ => ⟨m', ?_⟩
    rw [my, mv, hst] at r'
    have e : (y.gpr .x12 = 0 ∧ st.setWidth 32 ≠ 0) ↔ (em = em' ∧ st.setWidth 32 ≠ 0) := by rw [hy.hiff]
    simp only [e] at r'
    exact r'

/-- The result is `vg_rsa_pkcs1_recover`'s, with what the call writes if
`pre` holds the modulus' values. -/
theorem tailOut_eq {s : State} {h : Spec.RsaPkcs1Sig.Hash} {em : List Byte} {st : BitVec 64} {m : Mem}
    (hw : Spec.Rsa.written m (fb s + BitVec.ofNat 64 oEM1) (s.gpr .x3).toNat (st.setWidth 32) (pubOut s))
    (hem : Spec.Rsa.bytesAt m (fb s + BitVec.ofNat 64 oEM1) (s.gpr .x3).toNat = em) :
    tailOut s h em st = recOut s h := by
  unfold tailOut recOut encRes
  cases hpo : pubOut s with
  | none =>
    rw [hpo] at hw
    have h0 := hw.1
    cases Spec.RsaPkcs1Sig.encode h (em.drop ((s.gpr .x3).toNat - h.len)) (s.gpr .x3).toNat with
    | none => rfl
    | some em' => exact ite_eq_right fun h' => h'.2 h0
  | some e0 =>
    rw [hpo] at hw
    obtain ⟨h1, hb⟩ := hw
    obtain rfl : em = e0 := hem.symm.trans hb
    dsimp only
    cases Spec.RsaPkcs1Sig.encode h (em.drop ((s.gpr .x3).toNat - h.len)) (s.gpr .x3).toNat with
    | none => exact (ite_eq_right fun (h' : (none : Option (List Byte)) = some em) => by cases h').symm
    | some em' =>
      dsimp only
      by_cases hq : em = em'
      · subst hq
        rw [ite_eq_left ⟨rfl, by rw [h1]; decide⟩, ite_eq_left rfl]
      · rw [ite_eq_right fun h' => hq h'.1, ite_eq_right fun h' => hq (Option.some.inj h').symm]

/-! ## After the call -/

theorem afterPub_ok {K : Nat} {s t : State} (hp : PreR K s) {h : Spec.RsaPkcs1Sig.Hash}
    (hh : Spec.RsaPkcs1Sig.Hash.ofId ((s.gpr .x6).setWidth 32).toNat = some h) (hol : (s.gpr .x1).toNat = h.len)
    (ha : AfterCallP s t) :
    WP isa afterPub t fun w => Mid s w ∧ (Consistent s →
      Spec.Rsa.written w.mem (s.gpr .x0) (s.gpr .x1).toNat ((w.gpr .x0).setWidth 32) (recOut s h)) := by
  have hk2 := hp.k2
  unfold afterPub
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine wp_addSp (by decide) fun t₁ o₁ e₁ => wp_strx (a := fb s + BitVec.ofNat 64 oSt) (by decide)
    (by rw [e₁, ha.sp, BitVec.add_zero]) (by rw [o₁.wr, ha.wr]; exact in_frame _ _ (by decide))
    fun t₂ m₂ => wp_nil ?_
  have mid₂ : Mid s t₂ := slot_write (ha.toMid.only o₁) (d := oSt) (by decide) (by decide) m₂
  have hst₂ : t₂.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = t.gpr .x0 := by
    rw [m₂.mem, o₁.get .x0]; exact Mem.readW_writeW_self (n := 8) _ _ _ (by decide)
  obtain ⟨em, hem⟩ : ∃ em, Spec.Rsa.bytesAt t₂.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .x3).toNat = em :=
    ⟨_, rfl⟩
  have hemt : Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .x3).toNat = em := by
    rw [← hem, m₂.mem, o₁.mem]
    refine (bytes_apart (R := ⟨fb s + BitVec.ofNat 64 oEM1, (s.gpr .x3).toNat⟩)
      (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)) ?_
      (by show (s.gpr .x3).toNat ≤ 2 ^ 64; omega_arith)).symm
    exact Offset.disjoint _ (.inr (by unfold oEM1 oSt; omega_arith)) (by unfold oEM1; omega_arith) (by unfold oSt; omega_arith)
  refine WP.mono (Rec.encArgs_ok hp mid₂) fun u ⟨O, x8, x9, x10, x12, x11⟩ => ?_
  have hu : AtEnc s em u := ⟨mid₂.only O, x8, x9, x10, x12, x11, by rw [O.mem, hem]⟩
  refine WP.seq (WP.mono (Rec.enc_ok hp hh hol hu) fun w ⟨hw, fw⟩ => ?_)
  have hst : w.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = t.gpr .x0 := by
    rw [fw.readW (r := ⟨fb s + BitVec.ofNat 64 oSt, 8⟩) (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by unfold oEM2 oSt; omega_arith)) (by unfold oSt; omega_arith)
        (by unfold oEM2; omega_arith)) (by decide), O.mem, hst₂]
  refine WP.mono (tail_ok hp hw hst) fun w' ⟨m', r'⟩ => ⟨m', fun hq => ?_⟩
  rwa [tailOut_eq (ha.res hq) hemt] at r'

end VG.Proof.RsaPkcs1Sig.AArch64.RecPc
