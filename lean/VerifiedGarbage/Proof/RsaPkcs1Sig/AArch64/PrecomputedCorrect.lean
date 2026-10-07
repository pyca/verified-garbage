import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed
import VerifiedGarbage.Impl.RsaPkcs1Sig.AArch64.Precomputed
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyCorrect

/-!
# `vg_rsa_pkcs1_verify_precomputed` on AArch64: correctness

As `vg_rsa_pkcs1_verify` (`VerifyCorrect.lean`), whose frame, registers and
padding check (`padCheck_ok`) it shares: the call's arguments are
`vg_rsa_pkcs1_verify`'s with `pre` and `pre_len` for the modulus
(`AtCallP`); the precomputed public operation writes RSAVP1's result to
`EM₁` if `pre` holds the modulus' values (`AfterCallP`); the status is kept
in the frame, and masks the padding check's result.
-/

namespace VG.Proof.RsaPkcs1Sig.AArch64.Pc

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.Precomputed VG.Proof.RsaPkcs1Sig.AArch64.Ver
open VG.Impl.RsaPkcs1Sig.AArch64.Verify (frameBytes oEM1 oEM2 saved restore lenCheck ret0 encArgs tail)
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_strx wp_ldrx)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp wp_ldrSp)

theorem stackArgs_five (s : State) :
    List.map (stackArg s) (List.range 5) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4] := rfl

/-- The precomputed values. -/
abbrev pR (s : State) : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩

/-- The arguments on the stack. -/
abbrev a40 (s : State) : Region := ⟨stackArgAddr s 0, 40⟩

/-- `verifyPrecomputedContract.pre`, by name: `vg_rsa_pkcs1_verify`'s
(`PreV`), and the precomputed values. -/
structure PreP (K : Nat) (s : State) : Prop where
  v : PreV K s
  ra : Covers [pR s, a40 s] s.rd
  sp : (sR s).Disjoint (pR s)
  kp : (kR K s).Disjoint (pR s)
  ka : (kR K s).Disjoint (a40 s)
  sp2 : s.sp.toNat + 40 ≤ 2 ^ 64
  wp : (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64
  hl : (stackArg s 4).toNat = Spec.Rsa.precomputedWords (s.gpr .x1).toNat

theorem a24_sub (s : State) : Region.Sub (aR s) (a40 s) := Region.sub_prefix (by decide)

theorem preP_of {K : Nat} {s : State}
    (h : (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi (stk K)).pre s) : PreP K s := by
  have e : stk K = (frameBytes + K - 1) + 1 := by unfold stk frameBytes; omega
  rw [e] at h
  sig_pre [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig, abi, argRegs,
    stackArgs_five, List.append_eq] at h
  sig_pre [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig, abi, argRegs,
    stackArgs_five, List.append_eq] at h
  obtain ⟨sp1, sp2, hrd, hwr, ns, es, ds, gs, sp, sa, kn, ke, kd, kg, ks, kp, ka, wn, we, wd, wg, ws, wp,
    ⟨k1, k2⟩, e1, e2, hs, hl⟩ := h
  rw [← e] at sp1 kn ke kd kg ks kp ka
  refine ⟨⟨sp1, by omega, ?_, by rw [hwr]; simp, ns, es, ds, gs, sa.sub_right (a24_sub s), kn, ke, kd, kg,
    ks, ka.sub_right (a24_sub s), wn, we, wd, wg, ws, k1, k2, e1, e2,
    by unfold Spec.Rsa.scratchWords at hs; omega⟩, ?_, sp, kp, ka, sp2, wp, hl⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨nR s, by rw [hrd]; simp, 0, by simp, by simp⟩
    · exact ⟨eR s, by rw [hrd]; simp, 0, by simp, by simp⟩
    · exact ⟨dR s, by rw [hrd]; simp, 0, by simp, by simp⟩
    · exact ⟨gR s, by rw [hrd]; simp, 0, by simp, by simp⟩
    · exact ⟨a40 s, by rw [hrd]; simp, 0, by simp, by simp⟩
  · exact Covers.of_mem fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> rw [hrd] <;> simp

/-! ## The call -/

/-- At the call: `vg_rsa_pkcs1_verify`'s state at its call (`AtCall`), but
for `pre` and `pre_len` in `x2` and `x3`. -/
structure AtCallP (s t : State) : Prop where
  base : ∃ t₀, AtCall s t₀ ∧ Only [.x2, .x3] t₀ t
  x2 : t.gpr .x2 = stackArg s 3
  x3 : t.gpr .x3 = stackArg s 4

/-- A stack argument, in memory changed only in the frame. -/
theorem arg_frameP {K : Nat} {s : State} (hp : PreP K s) {m : Mem} (h : Frame [⟨fb s, frameBytes⟩] s.mem m)
    {j : Nat} (hj : j < 5) : m.readW (stackArgAddr s j) 64 = stackArg s j :=
  h.readW (r := a40 s) (by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega))
    (keep_of_frame hp.ka) (by decide)

theorem arg_inP {K : Nat} {s : State} (hp : PreP K s) {rs : List Region} (hrd : Covers s.rd rs) {j : Nat}
    (hj : j < 5) : InRegions rs (stackArgAddr s j) 8 :=
  hrd _ _ <| hp.ra _ _ ⟨a40 s, by simp, by
    rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩

theorem pubArgs_okP {K : Nat} {s u : State} (hp : PreP K s) (hsp : u.sp = fb s) (hrd : u.rd = s.rd)
    (hwr : u.wr = ⟨fb s, frameBytes⟩ :: s.wr) (hm : u.mem = s.mem) (hg : ∀ r, r ≠ .x8 → u.gpr r = s.gpr r)
    (hv : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) :
    WP isa (.block pubArgs) u (AtCallP s) := by
  unfold pubArgs
  rw [WP.block_append_iff]
  refine WP.mono (pubArgs_ok hp.v hsp hrd hwr hm hg hv) fun t ht => ?_
  have a3 : t.sp + BitVec.ofNat 64 (frameBytes + 24) = stackArgAddr s 3 := by rw [ht.sp, stackArgAddr_fb]
  have a4 : t.sp + BitVec.ofNat 64 (frameBytes + 32) = stackArgAddr s 4 := by rw [ht.sp, stackArgAddr_fb]
  refine wp_ldrSp (by decide) (by rw [a3, ht.rd]; exact arg_inP hp (Covers.left (Covers.refl _)) (by decide))
    fun t₁ o₁ e₁ => wp_ldrSp (by decide) (by
      rw [o₁.sp, o₁.rd, o₁.wr, a4, ht.rd]; exact arg_inP hp (Covers.left (Covers.refl _)) (by decide))
    fun t₂ o₂ e₂ => wp_nil ⟨⟨t, ht, (o₁.trans o₂).mono⟩, ?_, ?_⟩
  · rw [o₂.get .x2, e₁, a3, arg_frameP hp ht.mem (by decide)]
  · rw [e₂, o₁.sp, a4, o₁.mem, arg_frameP hp ht.mem (by decide)]

theorem pdOk_of (c : PdChecked) {s t : State} (hp : PreP c.stack s) (hc : AtCallP s t)
    (hsig : stackArg s 0 = s.gpr .x1) : PdOk c.stack t := by
  obtain ⟨⟨t₀, ha, o⟩, hx2, hx3⟩ := hc
  have hv := hp.v
  have hk1 := hv.k1; have hk2 := hv.k2
  have hfb := fb_toNat hv
  have hkb := kb_toNat hv
  have hcl := c.le
  have hem : em1R s = ⟨kb c.stack s + BitVec.ofNat 64 (c.stack + oEM1), (s.gpr .x1).toNat⟩ := by
    rw [em1R, off_fb c.stack]
  have hfK : fb s - BitVec.ofNat 64 c.stack = kb c.stack s := by rw [fb_eq c.stack, BitVec.add_sub_cancel]
  have hgK : (kR c.stack s).Disjoint ⟨s.gpr .x7, (s.gpr .x1).toNat⟩ := by have := hv.kg; rwa [gR, hsig] at this
  have hgS : (⟨s.gpr .x7, (s.gpr .x1).toNat⟩ : Region).Disjoint (sR s) := by have := hv.gs; rwa [gR, hsig] at this
  have hfb80 : (fb s + BitVec.ofNat 64 oEM1).toNat = (fb s).toNat + oEM1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oEM1 frameBytes at *; omega
  have hkK : Region.Sub ⟨kb c.stack s, c.stack⟩ (kR c.stack s) := Region.sub_prefix (by unfold stk; omega)
  have ha16 : (⟨fb s, 16⟩ : Region) = ⟨kb c.stack s + BitVec.ofNat 64 c.stack, 16⟩ := by rw [fb_eq c.stack]
  have g : ∀ r ∈ [Reg.x0, .x1, .x4, .x5, .x6, .x7], t.gpr r = t₀.gpr r := fun r hr =>
    o.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
                rcases hr with h | h | h | h | h | h <;> subst h <;> decide)
  have x0 : t.gpr .x0 = fb s + BitVec.ofNat 64 oEM1 := (g .x0 (by simp)).trans ha.x0
  have x1 : t.gpr .x1 = s.gpr .x1 := (g .x1 (by simp)).trans ha.x1
  have x4 : t.gpr .x4 = s.gpr .x2 := (g .x4 (by simp)).trans ha.x4
  have x5 : t.gpr .x5 = s.gpr .x3 := (g .x5 (by simp)).trans ha.x5
  have x6 : t.gpr .x6 = s.gpr .x7 := (g .x6 (by simp)).trans ha.x6
  have x7 : t.gpr .x7 = s.gpr .x1 := (g .x7 (by simp)).trans ha.x7
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
    simp only [pdRd]
    rw [hx2, hx3, x4, x5, x6, x7, sp, o.rd, ha.rd, o.wr, ha.wr]
    have hm : ∀ r ∈ [nR s, eR s, dR s, gR s, aR s], Covers [r] (s.rd ++ (⟨fb s, frameBytes⟩ :: s.wr)) :=
      fun r hr => Covers.left (Covers.trans (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; exact hr)
        hv.hrd)
    refine Covers.cons (Covers.left (Covers.trans (Covers.of_mem fun x hx => by
      rw [List.mem_singleton.mp hx]; simp) hp.ra)) (Covers.cons (hm _ (by simp)) (Covers.cons ?_
      (Covers.right (Covers.one (in_frame0 _ _ (by decide))))))
    have := hm (gR s) (by simp); rwa [gR, hsig] at this
  case hwr =>
    simp only [pubWr]
    rw [x0, x1, a0, a1, o.wr, ha.wr]
    exact Covers.cons (Covers.one (in_frame _ _ (by unfold oEM1 frameBytes; omega)))
      (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; exact List.mem_cons_of_mem _ hv.hwr)
  case hk => rw [x1]; exact ⟨hk1, hk2⟩
  case h3 => rw [hx3, x1]; exact hl4
  case h7 => rw [x7, x1]
  case he1 => rw [x5]; exact hv.e1
  case he2 => rw [x5, x1]; exact hv.e2
  case hs => rw [x1, a1]; unfold Spec.Rsa.scratchWords; exact hv.hs

/-- Words of the caller that the function does not write. -/
theorem words_of_frame {K : Nat} {s : State} {m : Mem} (hf : Frame [kR K s, sR s] s.mem m) {p : Addr}
    {n : Nat} (hk : (kR K s).Disjoint ⟨p, n * 8⟩) (hs : (sR s).Disjoint ⟨p, n * 8⟩) (hl : p.toNat + n * 8 ≤ 2 ^ 64) :
    Spec.Rsa.wordsAt m p n = Spec.Rsa.wordsAt s.mem p n := by
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => hf.readW (r := ⟨p, n * 8⟩) ?_ (fun r hr => ?_) (by decide)
  · have := List.mem_range.mp hi
    exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hk.symm
    · exact hs.symm

/-- After the call: `Mid`, and `EM₁` written with RSAVP1's result if `pre`
holds the modulus' values. -/
structure AfterCallP (K : Nat) (s t : State) : Prop extends Mid K s t where
  res : Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) =
      some (Spec.Rsa.wordsAt s.mem (stackArg s 3) (stackArg s 4).toNat) →
    Spec.Rsa.written t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .x1).toNat ((t.gpr .x0).setWidth 32) (pubOut s)

theorem callP_ok (c : PdChecked) {s t : State} (hp : PreP c.stack s) (hc : AtCallP s t)
    (hsig : stackArg s 0 = s.gpr .x1) :
    WP isa (.call c.name c.code) t (AfterCallP c.stack s) := by
  have hv := hp.v
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
  have x1 : t.gpr .x1 = s.gpr .x1 := (g .x1 (by simp)).trans ha.x1
  have x4 : t.gpr .x4 = s.gpr .x2 := (g .x4 (by simp)).trans ha.x4
  have x5 : t.gpr .x5 = s.gpr .x3 := (g .x5 (by simp)).trans ha.x5
  have x6 : t.gpr .x6 = s.gpr .x7 := (g .x6 (by simp)).trans ha.x6
  have sp : t.sp = fb s := o.sp.trans ha.sp
  have a0 : stackArg t 0 = stackArg s 1 := by
    rw [← ha.a0]; simp only [stackArg, stackArgAddr, o.sp, o.mem]
  have a1 : stackArg t 1 = stackArg s 2 := by
    rw [← ha.a1]; simp only [stackArg, stackArgAddr, o.sp, o.mem]
  simp only [pubWr] at hf
  rw [x0, x1, a0, a1, sp] at hf
  have hbs : Region.Sub (below (fb s) (16 * c.code.aarch64Depth)) (kR c.stack s) := fun a h =>
    VG.Proof.RsaPkcs1Sig.AArch64.Ver.below_sub c.stack s a
      (VG.AArch64.below_sub (sp := fb s) hd (by omega) a h)
  have hf' : Frame [kR c.stack s, sR s] t.mem s'.mem := hf.sub fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., em1_sub hv⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_self .., hbs⟩
  have hfr0 : Frame [kR c.stack s, sR s] s.mem t.mem := by
    rw [o.mem]
    exact ha.mem.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_sub0 c.stack s⟩
  have hgK : (kR c.stack s).Disjoint ⟨s.gpr .x7, (s.gpr .x1).toNat⟩ := by have := hv.kg; rwa [gR, hsig] at this
  have hgS : (⟨s.gpr .x7, (s.gpr .x1).toNat⟩ : Region).Disjoint (sR s) := by have := hv.gs; rwa [gR, hsig] at this
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
    mem := hfr0.trans hf'
    sv := by
      rw [o.mem] at hf
      exact ha.sv.frame_in saved_offs hf fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.disjoint _ (by unfold oEM1; omega) (by decide) (by unfold oEM1; omega)
        · exact hv.ks.sub_left (frame_sub c.stack s (d := 16) (n := 40) (by decide))
        · exact Offset.disjoint_below (fb s) (by omega)
    res := fun hc => ?_ }
  have hw : Spec.Rsa.wordsAt t.mem (t.gpr .x2) (t.gpr .x3).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 3) (stackArg s 4).toNat := by
    rw [hx2, hx3]; exact words_of_frame hfr0 hp.kp hp.sp hp.wp
  have := hpost (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) (by rw [x1, bytesAt_length])
    (by rw [hw]; exact hc)
  rw [x0, x1, x4, x5, x6, bytes_of_frame hfr0 hv.ke hv.es.symm (by have := hv.we; omega),
    bytes_of_frame hfr0 hgK hgS.symm (by omega)] at this
  exact this

/-! ## After the call -/

/-- `Mid` is kept by code that writes only registers other than `x19`–`x28`
and memory in the frame above the saved registers. -/
theorem _root_.VG.Proof.RsaPkcs1Sig.AArch64.Ver.Mid.frameW {K : Nat} {s t w : State} {rs : List Reg} (h : Mid K s t) (o : Keep rs t w) {d n : Nat}
    (hd : 56 ≤ d) (hdn : d + n ≤ frameBytes) (hm : Frame [⟨fb s + BitVec.ofNat 64 d, n⟩] t.mem w.mem)
    (hrs : ∀ r ∈ rs, r ∉ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] := by decide) :
    Mid K s w :=
  have hw : Mid K s { t with gpr := w.gpr, v := w.v } :=
    Mid.only (w := { t with gpr := w.gpr, v := w.v }) h ⟨o.gpr, rfl, rfl, rfl, rfl, o.vcs⟩ hrs
  { hw with
    sp := o.sp.trans h.sp
    rd := o.rd.trans h.rd
    wr := o.wr.trans h.wr
    mem := h.mem.trans (hm.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_sub K s hdn⟩)
    sv := h.sv.frame_in saved_offs hm fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (by omega) (by decide) (by unfold frameBytes at hdn; omega) }

theorem and01 (c : Bool) (r : BitVec 32) (hr : r = 1 ∨ r = 0) :
    ((if c then (1 : BitVec 32) else 0) &&& r) = if c ∧ r = 1 then 1 else 0 := by
  rcases hr with rfl | rfl <;> cases c <;> decide

theorem afterPubP_ok {K : Nat} {s t : State} (hp : PreP K s) (hsig : stackArg s 0 = s.gpr .x1)
    (ha : AfterCallP K s t) :
    WP isa afterPub t fun w => Mid K s w ∧
      (Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) =
          some (Spec.Rsa.wordsAt s.mem (stackArg s 3) (stackArg s 4).toNat) →
        (w.gpr .x0).setWidth 32 = if verOut s then 1 else 0) := by
  have hv := hp.v
  unfold afterPub
  refine WP.seq (wp_addSp (by decide) fun t₁ o₁ e₁ => wp_strx (a := fb s + BitVec.ofNat 64 oSt) (by decide)
    (by rw [e₁, ha.sp, BitVec.add_zero])
    (by rw [o₁.wr, ha.wr]; exact in_frame _ _ (by unfold oSt frameBytes; omega)) fun t₂ m₂ => wp_nil ?_)
  have fr₂ : Frame [⟨fb s + BitVec.ofNat 64 oSt, 8⟩] t₁.mem t₂.mem := by
    rw [m₂.mem]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have mid₂ : Mid K s t₂ := (ha.toMid.only o₁).frameW m₂.keep (d := oSt) (n := 8) (by decide) (by decide) fr₂
  have hB : Spec.Rsa.bytesAt t₂.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .x1).toNat =
      Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .x1).toNat := by
    rw [m₂.mem, o₁.mem]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => (Frame.writeW (Frame.refl [⟨fb s + BitVec.ofNat 64 oSt, 8⟩] t.mem)
      (List.mem_singleton_self _) _ (Region.contains_self _ _)).bytes
      (R := ⟨fb s + BitVec.ofNat 64 oEM1, (s.gpr .x1).toNat⟩) (fun r hr => ?_) (by have := hv.k2; dsimp only; omega)
      (List.mem_range.mp hi)
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (by unfold oSt oEM1; omega) (by have := hv.k2; unfold oEM1; omega) (by decide)
  have hslot : t₂.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = t.gpr .x0 := by
    rw [m₂.mem, o₁.get .x0, o₁.mem]; exact Mem.readW_writeW_self64 _ _ _
  refine WP.seq (WP.mono (padCheck_ok hv mid₂) fun w ⟨mw, fw, rw⟩ => ?_)
  have hsl : w.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = t.gpr .x0 := by
    rw [fw.readW (r := ⟨fb s + BitVec.ofNat 64 oSt, 8⟩) (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by unfold oSt oEM2; omega) (by decide)
        (by unfold oEM2; omega)) (by decide), hslot]
  have hc56 : (⟨fb s, frameBytes⟩ : Region).Contains (fb s + BitVec.ofNat 64 oSt) 8 :=
    Offset.contains_base _ (by unfold oSt frameBytes; omega) (by unfold oSt; omega)
  refine wp_addSp (by decide) fun w₁ p₁ f₁ => VG.Proof.MlKem.AArch64.wp_ldrx
    (a := fb s + BitVec.ofNat 64 oSt) (by decide) (by rw [f₁, mw.sp, BitVec.add_zero]) (by
      rw [p₁.rd, p₁.wr, mw.wr]
      exact InRegions_append_cons (xs := w.rd) |>.mpr (.inl hc56)) fun w₂ p₂ f₂ => ?_
  refine VG.Proof.MlKem.AArch64.WP.cons (s' := w₂.write .w .x0 (w₂.read .w .x0 &&& w₂.read .w .x8))
    (by simp [exec]) (wp_nil ⟨((mw.only p₁).only p₂).only (VG.Proof.MlKem.AArch64.only_write _ _ _ _), fun hc => ?_⟩)
  rw [p₁.mem, hsl] at f₂
  simp only [State.write, State.read, ite_true, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
    BitVec.setWidth_eq]
  rw [f₂, p₂.get .x0, p₁.get .x0, rw, hB, verOut_eq hsig]
  have hres := ha.res hc
  cases hpo : pubOut s with
  | none =>
    rw [hpo] at hres
    rw [hres.1]
    cases encOut s <;> simp
  | some em =>
    rw [hpo] at hres
    rw [hres.1, hres.2]
    cases encOut s with
    | none => simp
    | some em' => by_cases h : em = em' <;> simp [h]

end VG.Proof.RsaPkcs1Sig.AArch64.Pc
