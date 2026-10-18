module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Main
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.PrePc
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtPcCode
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Ws
import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# `vg_rsa_private_crt_precomputed_ifma` on x86-64: the computation

`CrtIfma.main` with `pc` (`mainPc_ok`): `pre` and the phases take `R² mod n`
and each prime's `R_X mod X` from `pre`; and `CrtIfma.code` with `pc`
against `crtPcContract` (`codePc_correct`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64.CrtIfma (Lay lay2048 lay3072 lay4096 sizes ifma)
open VG.Proof.Bignum.X86_64 (ofNat_eq_iff mx_ffff CrtReady.of_regs APost PreSrc PreVals prePc_ok qPartPc_ok
  pPartPc_ok crtMain_pc NReady.weak nPartPc_ok crtCtxPc_of crtPcCode_fin preVals_of crtPcContract)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- `pre` with `pc`, from the checks, for the layout `l` of the key's sizes. -/
theorem branchA1Pc_ok (hl : LayOk l) (M : Mont) {s t₀ : State} {B : Addr} {Z k : Nat}
    {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64}
    {Mk : Bool} {ok : Prop} {Pr : Addr} {W : Nat}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk ok)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (hw32 : (k + 7) / 8 = 2 * l.W) (hpl : wsWords pl = l.W) (hql : wsWords ql = l.W)
    (hp₀ : PreSrc t₀ B Z Pr W) (hW : 2 * ((k + 7) / 8) + l.W + l.W ≤ W)
    (hpre : (seqs (CrtIfma.pre M.mm true)).allInstrs (fun i => !loadsMxcsr i) = true) :
    WP isa (seqs (CrtIfma.pre M.mm true)) t₀ fun s₁ =>
      APost t₀ s₁ B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) l.W minv mp mq
        (Spec.Rsa.os2ip nb) (if Mk then Spec.Rsa.os2ip pb else 3) (if Mk then Spec.Rsa.os2ip qb else 3)
        (Spec.Rsa.os2ip xb) ok
        (ok ∧ wv t₀.mem Pr (8 * (2 * ((k + 7) / 8))) l.W =
          2 ^ (64 * l.W) % if Mk then Spec.Rsa.os2ip pb else 3)
        (ok ∧ wv t₀.mem Pr (8 * (2 * ((k + 7) / 8) + l.W)) l.W =
          2 ^ (64 * l.W) % if Mk then Spec.Rsa.os2ip qb else 3) ∧ s₁.mxcsr = t₀.mxcsr := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  have hk1 := h.k1
  have hZq := h.z
  obtain ⟨hMk', hP', hQ'⟩ := mask_facts hMk hodd hPN hQN
  have hn := hr.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have h16 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  obtain ⟨hW1, hW2⟩ := W_bounds hl
  have hoq : offQ ((k + 7) / 8) pl = slot ((k + 7) / 8) 8 + slot l.W 8 + wsTab l.W := by
    unfold offQ; rw [hpl]
  rw [hql] at hZq
  have pws := hr.pws
  have pxv := hr.pxv
  have qws := hr.qws
  have qxv := hr.qxv
  rw [hpl] at pws pxv
  rw [hql] at qws qxv
  exact WP.mono_mx hpre
    (prePc_ok M (wp := l.W) hr.good (by omega_using [hw32, hW2]) (le_refl _) (by rw [hoq]) (by omega_using [hZq])
      (by omega_using [hW1]) (by omega_using [hw32]) hr.wsP hr.wsQ pws qws hr.nv hr.xm pxv hP'.1 hP'.2 qxv hQ'.1
      hQ'.2 hp₀ hW)
    fun s₁ hA mx₁ => ⟨hA, mx₁⟩

/-- The IFMA computation with `pc`, for the layout `l` of the key's sizes. -/
theorem ifmaPartPc_ok (hl : LayOk l) (M : Mont) {s t₀ : State} {B : Addr} {Z k : Nat}
    {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    {minv mp mq : BitVec 64} {ok : Prop} {Pr : Addr} {W : Nat}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
      (keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
        (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) ok)
    (mx₀ : t₀.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10)
    (hs : SizesOf l ((k + 7) / 8) pl ql) (hpre : PreSrc s B Z Pr W)
    (hW : 2 * ((k + 7) / 8) + wsWords pl + wsWords ql ≤ W)
    (hY : ok → wv s.mem Pr (8 * (2 * ((k + 7) / 8))) (wsWords pl) = 2 ^ (64 * wsWords pl) % Spec.Rsa.os2ip pb ∧
      wv s.mem Pr (8 * (2 * ((k + 7) / 8) + wsWords pl)) (wsWords ql) = 2 ^ (64 * wsWords ql) % Spec.Rsa.os2ip qb)
    (hpreC : (seqs (CrtIfma.pre M.mm true)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    WP isa (seqs (CrtIfma.pre M.mm true ++ ([CrtIfma.ifmaAny] : List (Prog isa)) ++ CrtIfma.post M.mm)) t₀
      (MainQ s B Z k pl ql minv mp mq nb xb pb qb qib dpb dqb ok) := by
  obtain ⟨hW1, -⟩ := W_bounds hl
  have hw := hs.1
  have hp : wsWords pl = l.W := by unfold wsWords; omega
  have hq : wsWords ql = l.W := by unfold wsWords; omega
  rw [List.append_assoc]
  exact wp_seqs_append (by simp [CrtIfma.pre, CrtIfma.prep]) (by simp)
    (WP.mono (branchA1Pc_ok hl M h hv hr rfl hw hp hq (hpre.congrK hr.iscr hr.keep (by decide))
      (by rw [hp, hq] at hW; exact hW) hpreC) fun s₁ ⟨hA, mx₁⟩ =>
      wp_seqs_append (by simp) (by simp [CrtIfma.post])
        (WP.mono (ifmaAny_ok hl h hv hr rfl hs (fun hok hm => by
            have hy := hY hok
            rw [hp, hq] at hy
            rw [hpre.wv_eq hr.iscr (by omega), hpre.wv_eq hr.iscr (by omega), hy.1, hy.2]
            simp only [hm, ↓reduceIte, and_true]; exact ⟨hok, hok⟩) hA) fun t ⟨hd, mxa⟩ =>
          WP.mono (branchB_ok hl M h hv hd rfl hw hp hq hpost) fun t' ⟨hd', mxb⟩ =>
            ⟨hd', by rw [mxb, mxa, mx_ffff, mx₁, mx₀]⟩))

theorem mainPc_eq (mul : Nat → Nat → Nat → Prog isa) : CrtIfma.main mul true =
    seqs ((nSetup mul true ++ primesSetup ++ checks) ++
      (([.seq CrtIfma.anySizes (.ite .e (seqs (CrtIfma.pre mul true ++ ([CrtIfma.ifmaAny] : List (Prog isa)) ++
        CrtIfma.post mul)) (seqs (qPhase mul (Crt.expLoop mul Crt.tabSelect) true ++
          pPhase mul (Crt.expLoop mul Crt.tabSelect) true)))] : List (Prog isa)) ++ finish)) := by
  simp only [CrtIfma.main, List.append_assoc]

/-- `main` with `pc`, for a valid modulus: `privateCrt`'s result if `pre` holds
its values, and MXCSR's control bits. -/
theorem mainPc_ok (M : Mont) {s : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {Pr : Addr} {W : Nat}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) (hpre : PreSrc s B Z Pr W)
    (hW : 2 * ((k + 7) / 8) + wsWords pl + wsWords ql ≤ W)
    (hfront : (seqs (nSetup M.mm true ++ primesSetup ++ checks)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpreC : (seqs (CrtIfma.pre M.mm true)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hcrt : (seqs (qPhase M.mm (CrtExpL.w4 M).code true ++ pPhase M.mm (CrtExpL.w4 M).code true)).allInstrs
      (fun i => !loadsMxcsr i) = true) :
    WP isa (CrtIfma.main M.mm true) s fun t => (∃ Mk : Bool, CrtPost s t B Z k op
      (if Mk then crtResult (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip dpb) (Spec.Rsa.os2ip dqb)
        (Spec.Rsa.os2ip qib) (Spec.Rsa.os2ip xb) else 0) Mk
      (PreVals s.mem Pr ((k + 7) / 8) (wsWords pl) (wsWords ql) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
        (Spec.Rsa.os2ip qb)) ∧
      (Mk = true ↔ Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb =
        Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip qib < Spec.Rsa.os2ip pb)) ∧
      t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  have hfr : WP isa (seqs (nSetup M.mm true ++ primesSetup ++ checks)) s fun t => ∃ minv mp mq,
      CrtReady s t B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
        (keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
          (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
        (PreVals s.mem Pr ((k + 7) / 8) (wsWords pl) (wsWords ql) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
          (Spec.Rsa.os2ip qb)) :=
    wp_seqs_append (by simp [nSetup]) (by simp [checks]) (wp_seqs_append (by simp [nSetup]) (by simp [primesSetup])
      (WP.mono (nPartPc_ok M h hv hpre (by omega)) fun _ ⟨minv, hr⟩ =>
        WP.mono (setupPart_ok h (hr.weak fun hp' => hp'.1)) fun _ ⟨_, _, hr'⟩ =>
          WP.mono (checksPart_ok h hv hr') fun _ ⟨mp', mq', hr''⟩ => ⟨minv, mp', mq', hr''⟩))
  rw [mainPc_eq]
  refine wp_seqs_append (by simp [nSetup]) (by simp) (WP.mono_mx hfront hfr
    fun t₀ ⟨minv, mp, mq, hr⟩ mx₀ => ?_)
  refine wp_seqs_append (by simp) (by simp [finish]) ?_
  have hdisp : WP isa (.seq CrtIfma.anySizes (.ite .e (seqs (CrtIfma.pre M.mm true ++
      ([CrtIfma.ifmaAny] : List (Prog isa)) ++ CrtIfma.post M.mm))
      (seqs (qPhase M.mm (CrtExpL.w4 M).code true ++ pPhase M.mm (CrtExpL.w4 M).code true)))) t₀
      (MainQ s B Z k pl ql minv mp mq nb xb pb qb qib dpb dqb
        (PreVals s.mem Pr ((k + 7) / 8) (wsWords pl) (wsWords ql) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
          (Spec.Rsa.os2ip qb))) := by
    refine WP.seq (WP.mono (anySizes_ok h hr) fun t₁ ⟨z₁, r₁, x₁⟩ => ?_)
    have mx₁ : t₁.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by rw [x₁, mx₀]
    refine WP.ite _ z₁ (fun hb => ?_) (fun _ => WP.mono_mx hcrt (wp_seqs_append (by simp [qPhase])
      (by simp [pPhase]) (WP.mono (qPartPc_ok M (CrtExpL.w4 M) h hv r₁ rfl hpre hW fun hp' => hp'.2.2) fun _ hq =>
        pPartPc_ok M (CrtExpL.w4 M) h hv hq rfl hpre (by omega) fun hp' => hp'.2.1)) fun t hp' mxc =>
          ⟨hp', by rw [mxc, mx₁]⟩)
    rcases of_decide_eq_true hb with hs | hs | hs
    · exact ifmaPartPc_ok (Or.inl rfl) M h hv r₁ mx₁ hs hpre hW (fun hp' => ⟨hp'.2.1, hp'.2.2⟩) hpreC hpost
    · exact ifmaPartPc_ok (Or.inr (Or.inl rfl)) M h hv r₁ mx₁ hs hpre hW (fun hp' => ⟨hp'.2.1, hp'.2.2⟩) hpreC
        hpost
    · exact ifmaPartPc_ok (Or.inr (Or.inr rfl)) M h hv r₁ mx₁ hs hpre hW (fun hp' => ⟨hp'.2.1, hp'.2.2⟩) hpreC
        hpost
  refine WP.mono hdisp fun t₂ ⟨hp, mx₂⟩ => ?_
  refine WP.mono_mx (by decide +kernel) (finPart_ok h hv hp rfl) fun t ht mxf => ⟨⟨_, ht, ?_⟩, by rw [mxf, mx₂]⟩
  simp only [keyMask, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- `vg_rsa_private_crt_precomputed_ifma` with Montgomery multiplication `M`,
given that the parts of its code outside the vector code never load MXCSR
(which the registration file evaluates). -/
theorem codePc_correct (M : Mont)
    (hfront : (seqs (nSetup M.mm true ++ primesSetup ++ checks)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpreC : (seqs (CrtIfma.pre M.mm true)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hcrt : (seqs (qPhase M.mm (CrtExpL.w4 M).code true ++ pPhase M.mm (CrtExpL.w4 M).code true)).allInstrs
      (fun i => !loadsMxcsr i) = true)
    (s : State) (h : crtPcContract.pre s) :
    ∃ t s', Exec isa (CrtIfma.code M.mm true) s t s' ∧ abiPreserved s s' ∧ crtPcContract.post s s' := by
  obtain ⟨c, hpre, hW⟩ := crtCtxPc_of h
  clear h
  have hZ' := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  suffices hwp : WP isa (CrtIfma.code M.mm true) s fun s' => (gprPreserved s s' ∧ crtPcContract.post s s') ∧
      s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 by
    obtain ⟨t, s', he, ⟨hg, hp⟩, hmx⟩ := hwp
    exact ⟨t, s', he, ⟨hg.1, hg.2, hmx⟩, hp⟩
  unfold CrtIfma.code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono_mx (c := .block (Crt.entry ++ ([.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] :
    List Instr))) (by decide +kernel) (crtHead_ok c) fun t₁ h₁ mx₁ => ?_
  have hnb₁ := c.hnb.congrK h₁.inScr h₁.keep
  refine WP.mono_mx (by decide +kernel) (invalid_ok h₁.rdx h₁.rcx hk1 hk2
    (bytesAt_length _ _ _) (fun i hi => hnb₁.rd i (by rw [bytesAt_length]; exact hi))
    (fun i hi => hnb₁.val i _)) fun t₂ ⟨hz₂, hm₂, k₂⟩ mx₂ => ?_
  have hpre' := crtPre_of c h₁ hm₂ k₂
  have i₂ : InScr (stackArg s 10) ((stackArg s 11).toNat * 8) s.mem t₂.mem := by rw [hm₂]; exact h₁.inScr
  have hp₂ := hpre.congrK i₂ (h₁.keep.trans k₂) (by decide)
  refine WP.ite (!Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
    (s.gpr .rcx).toNat) (by simp [eval, hz₂]) (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = false := by simpa using hb
    exact WP.mono_mx (by decide +kernel) (fail_ok hpre'.scr hpre'.rdi (by omega)
      (by omega) (by omega) hpre'.hO hpre'.hK hpre'.out hpre'.outSep)
      fun t hp mx => ⟨crtPcCode_fin (ok := True) c h₁ hm₂ k₂ ⟨fun _ => hp.bytes, hp.rax, hp.saved, hp.frame,
        hp.keep⟩ (fun _ => trivial) (fun h => absurd h (by rw [hv]; decide)) fun _ => ⟨rfl, rfl⟩,
        by rw [mx, mx₂, mx₁]⟩
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = true := by simpa using hb
    have hW' : 2 * (((s.gpr .rcx).toNat + 7) / 8) + wsWords (stackArg s 1).toNat + wsWords (stackArg s 3).toNat ≤
        (stackArg s 13).toNat := by
      rw [hW]; unfold Spec.Rsa.privatePrecomputedWords Spec.Rsa.precomputedWords Spec.Rsa.primeWords
        Spec.Rsa.modulusWords wsWords; omega
    exact WP.mono (mainPc_ok M hpre' hv hp₂ hW' hfront hpreC hpost hcrt) fun t ⟨⟨Mk, hp, hiff⟩, mx⟩ =>
      ⟨crtPcCode_fin c h₁ hm₂ k₂ hp (preVals_of hpre hW i₂) (fun _ => ⟨hiff, rfl⟩)
        fun h => absurd h (by rw [hv]; decide), by rw [mx, mx₂, mx₁]⟩

end VG.Proof.Bignum.X86_64.Ifma
