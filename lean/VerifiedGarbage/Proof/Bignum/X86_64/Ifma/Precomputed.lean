module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Main
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Verified
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtPreCT
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTPre
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTPost
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCode
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTFin
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTP
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExpL
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Main
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Verified
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPreCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTPre
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTPost
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCode
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTFin
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTP
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExpL
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_private_crt_ifma_precomputed` and `_ifma512_precomputed` on x86-64

`CrtIfma.codeP` is `CrtIfma.code` with `R² mod n` copied from the key's
precomputed values (`nSetupP`): correct (`codeP_correct`) and constant time
but for `n` and `pre`'s address (`codeP_constantTime`) against
`crtContractP`, from `CrtIfma.code`'s proofs of what follows the setup of
`n` (`mainBack_ok`, `dispatch_ct`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64
open VG.Proof.Bignum.X86_64

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

local notation "CLay" => VG.Impl.Rsa.X86_64.CrtIfma.Lay

/-- `ifmaPart_ok` with `preP` and `postP`, with `R_p² mod p` and `R_q² mod q`
in `pre` (`hpP`, `hpQ`, from the start `s`). -/
theorem ifmaPartP_ok {l2 : VG.Impl.Rsa.X86_64.CrtIfma.Lay} (h2 : Lay2 l2) (hl2 : LayOf l2 l) (M : Mont) {s t₀ : State} {B : Addr} {Z k : Nat}
    {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    {minv mp mq : BitVec 64}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
      (keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
        (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)))
    (mx₀ : t₀.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10)
    (hs : SizesOf l ((k + 7) / 8) pl ql)
    (hpP : PreW s B Z (2 * ((k + 7) / 8)) (Spec.Rsa.primeWords pl)
      (2 ^ (128 * Spec.Rsa.primeWords pl) % Spec.Rsa.os2ip pb))
    (hpQ : PreW s B Z (2 * ((k + 7) / 8) + Spec.Rsa.primeWords pl) (Spec.Rsa.primeWords ql)
      (2 ^ (128 * Spec.Rsa.primeWords ql) % Spec.Rsa.os2ip qb))
    (hpre : (seqs (CrtIfma.preP M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpost : (seqs (CrtIfma.postP M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    WP isa (seqs (CrtIfma.preP M.mm ++ ([CrtIfma.ifmaAny l2] : List (Prog isa)) ++ CrtIfma.postP M.mm)) t₀
      (MainQ s B Z k pl ql minv mp mq nb xb pb qb qib dpb dqb) := by
  have hl : LayOk l := hl2.ok h2
  obtain ⟨hW1, -⟩ := W_bounds hl
  have hw := hs.1
  have hp : wsWords pl = l.W := by unfold wsWords; omega
  have hq : wsWords ql = l.W := by unfold wsWords; omega
  rw [List.append_assoc]
  exact wp_seqs_append (by simp [CrtIfma.preP, CrtIfma.prepP]) (by simp)
    (WP.mono (branchA1P_ok hl M h hv hr rfl hw hp hq
      (hpP.congr hr.iscr (hr.keep.gpr (by decide)) hr.keep.2.1 hr.keep.2.2)
      (hpQ.congr hr.iscr (hr.keep.gpr (by decide)) hr.keep.2.1 hr.keep.2.2) hpre) fun s₁ ⟨hA, mx₁⟩ =>
      wp_seqs_append (by simp) (by simp [CrtIfma.postP])
        (WP.mono (ifmaAny_ok h2 hl2 h hv hr rfl hs hA) fun t ⟨hd, mxa⟩ =>
          WP.mono (branchBP_ok hl M h hv hd rfl hw hp hq
            (hpP.congr hd.iscr (hd.keep.gpr (by decide)) hd.keep.2.1 hd.keep.2.2) hpost) fun t' ⟨hd', mxb⟩ =>
            ⟨hd', by rw [mxb, mxa, mx_ffff, mx₁, mx₀]⟩))

/-- `mainBack_ok` with `preP` and `postP`. -/
theorem mainBackP_ok {l2 : VG.Impl.Rsa.X86_64.CrtIfma.Lay} (h2 : Lay2 l2) (M : Mont) {s t₀ : State} {B : Addr} {Z k : Nat}
    {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
      (keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
        (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)))
    (mx₀ : t₀.mxcsr = s.mxcsr)
    (hpP : PreW s B Z (2 * ((k + 7) / 8)) (Spec.Rsa.primeWords pl)
      (2 ^ (128 * Spec.Rsa.primeWords pl) % Spec.Rsa.os2ip pb))
    (hpQ : PreW s B Z (2 * ((k + 7) / 8) + Spec.Rsa.primeWords pl) (Spec.Rsa.primeWords ql)
      (2 ^ (128 * Spec.Rsa.primeWords ql) % Spec.Rsa.os2ip qb))
    (hpre : (seqs (CrtIfma.preP M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpost : (seqs (CrtIfma.postP M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hcrt : (seqs (qPhase M.mm (CrtExpL.w4 M).code ++ pPhase M.mm (CrtExpL.w4 M).code)).allInstrs (fun i => !loadsMxcsr i) = true) :
    WP isa (seqs (([.seq CrtIfma.anySizes (.ite .e (seqs (CrtIfma.preP M.mm ++ ([CrtIfma.ifmaAny l2] : List (Prog isa)) ++
        CrtIfma.postP M.mm)) (seqs (qPhase M.mm (Crt.expLoop M.mm Crt.tabSelect) ++
          pPhase M.mm (Crt.expLoop M.mm Crt.tabSelect))))] : List (Prog isa)) ++ finish)) t₀
      (MainOut s B Z k op nb xb pb qb dpb dqb qib) := by
  refine wp_seqs_append (by simp) (by simp [finish]) ?_
  have hcrtB : ∀ t₁, CrtReady s t₁ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
      (keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
        (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) →
      t₁.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 →
      WP isa (seqs (qPhase M.mm (CrtExpL.w4 M).code ++ pPhase M.mm (CrtExpL.w4 M).code)) t₁ (MainQ s B Z k pl ql minv mp mq nb xb pb qb qib dpb dqb) :=
    fun t₁ hr₁ mx₁ => WP.mono_mx hcrt (wp_seqs_append (by simp [qPhase]) (by simp [pPhase])
      (WP.mono (qPart_ok M (CrtExpL.w4 M) h hv hr₁ rfl) fun _ hq => pPart_ok M (CrtExpL.w4 M) h hv hq rfl)) fun t hp' mxc =>
        ⟨hp', by rw [mxc, mx₁]⟩
  have hdisp : WP isa (.seq CrtIfma.anySizes (.ite .e (seqs (CrtIfma.preP M.mm ++ ([CrtIfma.ifmaAny l2] : List (Prog isa)) ++
      CrtIfma.postP M.mm)) (seqs (qPhase M.mm (CrtExpL.w4 M).code ++ pPhase M.mm (CrtExpL.w4 M).code)))) t₀
      (MainQ s B Z k pl ql minv mp mq nb xb pb qb qib dpb dqb) := by
    refine WP.seq (WP.mono (anySizes_ok h hr) fun t₁ ⟨z₁, r₁, x₁⟩ => ?_)
    refine WP.ite _ z₁ (fun hb => ?_) (fun _ => hcrtB t₁ r₁ (by rw [x₁, mx₀]))
    have mx₁ : t₁.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by rw [x₁, mx₀]
    rcases of_decide_eq_true hb with hs | hs | hs
    · exact ifmaPartP_ok h2 (Or.inl rfl) M h hv r₁ mx₁ ((h2.sizes _ _ _).2 hs) hpP hpQ hpre hpost
    · exact ifmaPartP_ok h2 (Or.inr (Or.inl rfl)) M h hv r₁ mx₁ hs hpP hpQ hpre hpost
    · exact ifmaPartP_ok h2 (Or.inr (Or.inr rfl)) M h hv r₁ mx₁ hs hpP hpQ hpre hpost
  refine WP.mono hdisp fun t₂ ⟨hp, mx₂⟩ => ?_
  refine WP.mono_mx (by decide +kernel) (finPart_ok h hv hp rfl) fun t ht mxf => ⟨⟨_, ht, ?_⟩, by rw [mxf, mx₂]⟩
  simp only [keyMask, Bool.and_eq_true, decide_eq_true_eq, and_assoc]


theorem mainP_eq (l2 : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (mul : Nat → Nat → Nat → Prog isa) : CrtIfma.mainP l2 mul =
    seqs ((nSetupP mul ++ primesSetup ++ checksP) ++
      (([.seq CrtIfma.anySizes (.ite .e (seqs (CrtIfma.preP mul ++ ([CrtIfma.ifmaAny l2] : List (Prog isa)) ++
        CrtIfma.postP mul)) (seqs (qPhase mul (Crt.expLoop mul Crt.tabSelect) ++
          pPhase mul (Crt.expLoop mul Crt.tabSelect))))] : List (Prog isa)) ++ finish)) := by
  simp only [CrtIfma.mainP, List.append_assoc]

/-- `mainP`, for a valid modulus: as `main_ok`. -/
theorem mainP_ok {l2 : VG.Impl.Rsa.X86_64.CrtIfma.Lay} (h2 : Lay2 l2) (M : Mont) {s : State} {B : Addr} {Z k : Nat}
    {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hp : PreR2 s B Z ((k + 7) / 8) (Spec.Rsa.os2ip nb))
    (hpq : Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb)
    (hpP : PreW s B Z (2 * ((k + 7) / 8)) (Spec.Rsa.primeWords pl)
      (2 ^ (128 * Spec.Rsa.primeWords pl) % Spec.Rsa.os2ip pb))
    (hpQ : PreW s B Z (2 * ((k + 7) / 8) + Spec.Rsa.primeWords pl) (Spec.Rsa.primeWords ql)
      (2 ^ (128 * Spec.Rsa.primeWords ql) % Spec.Rsa.os2ip qb))
    (hfront : (seqs (nSetupP M.mm ++ primesSetup ++ checksP)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpre : (seqs (CrtIfma.preP M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpost : (seqs (CrtIfma.postP M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hcrt : (seqs (qPhase M.mm (CrtExpL.w4 M).code ++ pPhase M.mm (CrtExpL.w4 M).code)).allInstrs (fun i => !loadsMxcsr i) = true) :
    WP isa (CrtIfma.mainP l2 M.mm) s (MainOut s B Z k op nb xb pb qb dpb dqb qib) := by
  rw [mainP_eq]
  exact wp_seqs_append (by simp [nSetupP]) (by simp) (WP.mono_mx hfront (frontP_ok M h hv hp hpq)
    fun t₀ ⟨minv, mp, mq, hr⟩ mx₀ => mainBackP_ok h2 M h hv hr mx₀ hpP hpQ hpre hpost hcrt)

/-- `vg_rsa_private_crt_ifma_precomputed` with Montgomery multiplication `M`,
given that the parts of its code outside the vector code never load MXCSR
(which the registration file evaluates). -/
theorem codeP_correct {l2 : VG.Impl.Rsa.X86_64.CrtIfma.Lay} (h2 : Lay2 l2) (M : Mont)
    (hfront : (seqs (nSetupP M.mm ++ primesSetup ++ checksP)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpre : (seqs (CrtIfma.preP M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpost : (seqs (CrtIfma.postP M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hcrt : (seqs (qPhase M.mm (CrtExpL.w4 M).code ++ pPhase M.mm (CrtExpL.w4 M).code)).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : crtContractP.pre s) :
    ∃ t s', Exec isa (CrtIfma.codeP l2 M.mm) s t s' ∧ abiPreserved s s' ∧ crtContractP.post s s' := by
  obtain ⟨c, hv, hp, hpq⟩ := crtCtxP_of h
  obtain ⟨hpP, hpQ⟩ := crtPrimes_of h
  clear h
  have hZ' := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  suffices hwp : WP isa (CrtIfma.codeP l2 M.mm) s fun s' => (gprPreserved s s' ∧ crtContract.post s s') ∧
      s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 by
    obtain ⟨t, s', he, ⟨hg, hp⟩, hmx⟩ := hwp
    exact ⟨t, s', he, ⟨hg.1, hg.2, hmx⟩, hp⟩
  unfold CrtIfma.codeP
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono_mx (c := .block (Crt.entry ++ ([.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] :
    List Instr))) (by decide +kernel) (crtHead_ok c) fun t₁ h₁ mx₁ => ?_
  have hnb₁ := c.hnb.congrK h₁.inScr h₁.keep
  refine WP.mono_mx (by decide +kernel) (invalid_ok h₁.rdx h₁.rcx hk1 hk2
    (bytesAt_length _ _ _) (fun i hi => hnb₁.rd i (by rw [bytesAt_length]; exact hi))
    (fun i hi => hnb₁.val i _)) fun t₂ ⟨hz₂, hm₂, k₂⟩ mx₂ => ?_
  have hpre' := crtPre_of c h₁ hm₂ k₂
  have kk := h₁.keep.trans k₂
  have hp₂ := hp.congr (by rw [hm₂]; exact h₁.inScr) (kk.gpr (by decide)) kk.2.1 kk.2.2
  have hpP₂ := hpP.congr (by rw [hm₂]; exact h₁.inScr) (kk.gpr (by decide)) kk.2.1 kk.2.2
  have hpQ₂ := hpQ.congr (by rw [hm₂]; exact h₁.inScr) (kk.gpr (by decide)) kk.2.1 kk.2.2
  refine WP.ite (!Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
    (s.gpr .rcx).toNat) (by simp [eval, hz₂]) (fun hb => ?_) (fun _ => ?_)
  · exact absurd hb (by rw [hv]; decide)
  · exact WP.mono (mainP_ok h2 M hpre' hv hp₂ hpq hpP₂ hpQ₂ hfront hpre hpost hcrt) fun t ⟨⟨Mk, hp, hiff⟩, mx⟩ =>
      ⟨crtCode_fin c h₁ hm₂ k₂ hp (fun _ => ⟨hiff, rfl⟩) fun h => absurd h (by rw [hv]; decide),
        by rw [mx, mx₂, mx₁]⟩

/-! ## Constant time

`preP` and `postP` read `pre` from the stack: runs that agree on the stack
pointer and `pre`'s address leak the same. The stages of `main` (`Stage`)
carry them, and what `pre` holds, as facts of each run's start (`StageX`,
`EP`), which every part keeps (`stageX_step`).
-/

/-- What the start `σ` of a run of `mainP` has of `pre`: `p q = n`,
`R² mod n`, `R_p² mod p` and `R_q² mod q`. -/
def EP (p : CrtPub) (σ : State) (pb qb : List Byte) : Prop :=
  Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = p.N ∧ PreR2 σ p.B p.Z p.w p.N ∧
  PreW σ p.B p.Z (2 * p.w) (Spec.Rsa.primeWords p.pl)
    (2 ^ (128 * Spec.Rsa.primeWords p.pl) % Spec.Rsa.os2ip pb) ∧
  PreW σ p.B p.Z (2 * p.w + Spec.Rsa.primeWords p.pl) (Spec.Rsa.primeWords p.ql)
    (2 ^ (128 * Spec.Rsa.primeWords p.ql) % Spec.Rsa.os2ip qb)

/-- `R`, with `EP` at the start, whose stack pointer is `sp` and `pre`'s
address `A`. -/
def StageRel.withX (R : StageRel) (sp A : Addr) : StageRel := fun p σ xb pb qb dpb dqb qib t =>
  R p σ xb pb qb dpb dqb qib t ∧ EP p σ pb qb ∧ σ.gpr .rsp = sp ∧ stackArg σ 12 = A

/-- A stage of `mainP`, with the stack pointer and `pre`'s address public. -/
def StageX (R : StageRel) (q : CrtPub × Addr × Addr) (t : State) : Prop := Stage (StageRel.withX R q.2.1 q.2.2) q.1 t

theorem stageX_drop {R : StageRel} {q : CrtPub × Addr × Addr} {t : State} (h : StageX R q t) : Stage R q.1 t := by
  obtain ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, hr, -⟩ := h
  exact ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, hr⟩

theorem two_drop {R : StageRel} {s₁ s₂ : State} (h : Two (StageX R) s₁ s₂) : Two (Stage R) s₁ s₂ :=
  two_bind (fun q _ _ h₁ h₂ => ⟨q.1, stageX_drop h₁, stageX_drop h₂⟩) h

/-- A part constant time from a stage, with its correctness, goes to the
next stage, keeping the facts of the start. -/
theorem stageX_step {R R' : StageRel} {c : Prog isa} (hct : RelCT isa (Two (StageX R)) c fun _ _ => True)
    (hw : ∀ p σ xb pb qb dpb dqb qib t,
      CrtPre σ p.B p.Z p.k p.op p.np p.ip p.pp p.qp p.dpp p.dqp p.qip p.pl p.ql p.nb xb pb qb dpb dqb qib →
      Spec.Rsa.modulusValid p.N p.k = true → EP p σ pb qb → R p σ xb pb qb dpb dqb qib t →
      WP isa c t (R' p σ xb pb qb dpb dqb qib)) :
    RelCT isa (Two (StageX R)) c (Two (StageX R')) :=
  two_post hct fun q t ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, hr, he, hsp, ha⟩ =>
    WP.mono (hw q.1 σ xb pb qb dpb dqb qib t h hv he hr) fun _ h' =>
      ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, h', he, hsp, ha⟩

/-- A part's own constant time, from what a stage gives. -/
theorem two_stageX {R : StageRel} {α : Type} {Φ : α → State → Prop} (f : CrtPub × Addr × Addr → BitVec 64 → α)
    (m : ∀ (q : CrtPub × Addr × Addr) σ xb pb qb dpb dqb qib t,
      CrtPre σ q.1.B q.1.Z q.1.k q.1.op q.1.np q.1.ip q.1.pp q.1.qp q.1.dpp q.1.dqp q.1.qip q.1.pl q.1.ql q.1.nb
        xb pb qb dpb dqb qib →
      Spec.Rsa.modulusValid q.1.N q.1.k = true → StageRel.withX R q.2.1 q.2.2 q.1 σ xb pb qb dpb dqb qib t →
      ∃ minv, NVals t q.1.B q.1.w minv q.1.N ∧ Φ (f q minv) t)
    {s₁ s₂ : State} (h : Two (StageX R) s₁ s₂) : Two Φ s₁ s₂ := by
  obtain ⟨q, h₁, h₂⟩ := h
  exact two_stage (R := StageRel.withX R q.2.1 q.2.2) (fun p minv => f (p, q.2) minv)
    (fun p σ xb pb qb dpb dqb qib t h hv hr => m (p, q.2) σ xb pb qb dpb dqb qib t h hv hr) ⟨q.1, h₁, h₂⟩

/-- `preP_ok`'s hypotheses, after the checks. -/
theorem prePreP_of (hl : LayOk l) {s t₀ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool} {sp A : Addr}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (hw32 : (k + 7) / 8 = 2 * l.W) (hpl : wsWords pl = l.W) (hql : wsWords ql = l.W)
    (hpP : PreW s B Z (2 * ((k + 7) / 8)) (Spec.Rsa.primeWords pl)
      (2 ^ (128 * Spec.Rsa.primeWords pl) % Spec.Rsa.os2ip pb))
    (hpQ : PreW s B Z (2 * ((k + 7) / 8) + Spec.Rsa.primeWords pl) (Spec.Rsa.primeWords ql)
      (2 ^ (128 * Spec.Rsa.primeWords ql) % Spec.Rsa.os2ip qb))
    (hsp : s.gpr .rsp = sp) (ha : stackArg s 12 = A) :
    PrePreP ⟨⟨B, Z, (k + 7) / 8, minv, Spec.Rsa.os2ip nb, offP ((k + 7) / 8), offQ ((k + 7) / 8) pl, l.W⟩, sp, A⟩ t₀ := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  have hk1 := h.k1
  have hZq := h.z
  obtain ⟨hW1, hW2⟩ := W_bounds hl
  have hsp₀ : t₀.gpr .rsp = sp := (hr.keep.gpr (by decide)).trans hsp
  have ha₀ : stackArg t₀ 12 = A := (hpP.arg_eq hr.iscr (hr.keep.gpr (by decide))).trans ha
  have hpP₀ := hpP.congr hr.iscr (hr.keep.gpr (by decide)) hr.keep.2.1 hr.keep.2.2
  have hpQ₀ := hpQ.congr hr.iscr (hr.keep.gpr (by decide)) hr.keep.2.1 hr.keep.2.2
  rw [primeWords_eq, hpl, hw32, show 2 * (2 * l.W) = r2XOff false l.W by
    simp only [r2XOff, Bool.false_eq_true, ↓reduceIte]; omega] at hpP₀
  rw [primeWords_eq, primeWords_eq, hpl, hql, hw32, show 2 * (2 * l.W) + l.W = r2XOff true l.W by
    simp only [r2XOff, ↓reduceIte]; omega] at hpQ₀
  dsimp only [PrePreP]
  generalize Spec.Rsa.os2ip nb = N at *
  generalize Spec.Rsa.os2ip xb = C at *
  generalize Spec.Rsa.os2ip pb = P at *
  generalize Spec.Rsa.os2ip qb = Q at *
  generalize Spec.Rsa.os2ip qib = QI at *
  obtain ⟨hMk', hP', hQ'⟩ := mask_facts hMk hodd hPN hQN
  have hP0 : Mk = true → 0 < P := fun hm => by
    obtain ⟨_, hpq, _⟩ := hMk' hm
    exact Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.zero_mul] at hpq; omega_arith
  have hQ0 : Mk = true → 0 < Q := fun hm => by
    obtain ⟨_, hpq, _⟩ := hMk' hm
    exact Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at hpq; omega_arith
  have hn := hr.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hoq : offQ ((k + 7) / 8) pl = slot ((k + 7) / 8) 8 + slot l.W 8 + wsTab l.W := by
    unfold offQ; rw [hpl]
  rw [hql] at hZq
  have pws := hr.pws
  have pxv := hr.pxv
  have qws := hr.qws
  have qxv := hr.qxv
  rw [hpl] at pws pxv
  rw [hql] at qws qxv
  exact ⟨mp, mq, _, _, C, _, _, Mk, hr.good, by omega_arith, Nat.le_refl _, by rw [hoq]; rfl, by omega_arith,
    by omega_arith, by omega_arith, hr.wsP, hr.wsQ, pws, qws, hr.nv, hr.xm, pxv, hP'.1, hP'.2, qxv, hQ'.1, hQ'.2,
    hsp₀, ha₀, hr.msk, hpP₀, hpQ₀, fun hm => by simp [hm], (preV_mask hP0).1, fun hm => by simp [hm],
    (preV_mask hQ0).1⟩

/-- `postP_ok`'s hypotheses, after `ifma`. -/
theorem postPreP_of (hl : LayOk l) {s t₁ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool} {sp A : Addr}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hd : IDone l s t₁ B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl)
        (offQ ((k + 7) / 8) pl + slot l.W 8 + wsTab l.W) minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) dpp dqp qip pl ql dpb dqb Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (hw32 : (k + 7) / 8 = 2 * l.W) (hpl : wsWords pl = l.W) (hql : wsWords ql = l.W)
    (hpP : PreW s B Z (2 * ((k + 7) / 8)) (Spec.Rsa.primeWords pl)
      (2 ^ (128 * Spec.Rsa.primeWords pl) % Spec.Rsa.os2ip pb))
    (hsp : s.gpr .rsp = sp) (ha : stackArg s 12 = A) :
    PostPreP ⟨⟨B, Z, (k + 7) / 8, offP ((k + 7) / 8), wsWords pl, offQ ((k + 7) / 8) pl, qip, pl⟩, sp, A⟩ t₁ := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  have hk1 := h.k1
  have hpl1 := h.pl1
  have hZq := h.z
  have hqil := h.qil
  obtain ⟨hW1, hW2⟩ := W_bounds hl
  have hsp₁ : t₁.gpr .rsp = sp := (hd.keep.gpr (by decide)).trans hsp
  have ha₁ : stackArg t₁ 12 = A := (hpP.arg_eq hd.iscr (hd.keep.gpr (by decide))).trans ha
  have hpP₁ := hpP.congr hd.iscr (hd.keep.gpr (by decide)) hd.keep.2.1 hd.keep.2.2
  rw [primeWords_eq, hw32, show 2 * (2 * l.W) = r2XOff false (wsWords pl) by
    simp only [r2XOff, Bool.false_eq_true, ↓reduceIte]; omega] at hpP₁
  dsimp only [PostPreP]
  generalize Spec.Rsa.os2ip nb = N at *
  generalize Spec.Rsa.os2ip xb = C at *
  generalize Spec.Rsa.os2ip pb = P at *
  generalize Spec.Rsa.os2ip qb = Q at *
  generalize hQIe : Spec.Rsa.os2ip qib = QI at *
  obtain ⟨hMk', hP', hQ'⟩ := mask_facts hMk hodd hPN hQN
  have hP0 : Mk = true → 0 < P := fun hm => by
    obtain ⟨_, hpq, _⟩ := hMk' hm
    exact Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.zero_mul] at hpq; omega_arith
  have hn := hd.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hpl' : (pl + 7) / 8 ≤ l.W := by unfold wsWords at hpl; omega_arith
  have hop : offP ((k + 7) / 8) = slot ((k + 7) / 8) 8 := rfl
  have hoq : offQ ((k + 7) / 8) pl = slot ((k + 7) / 8) 8 + slot (wsWords pl) 8 + wsTab (wsWords pl) := rfl
  have hW8 : 256 ≤ slot (wsWords pl) 8 := by unfold slot hdrBytes; omega_arith
  have hm := hd.im
  exact ⟨minv, mp, mq, _, qib, Mk, _, hd.good, by omega_arith, by rw [hpl]; omega_arith, hm.wsQ,
    by rw [hpl]; exact hm.qws, by have := hZq; rw [hql] at this; rw [hpl]; exact this, Nat.le_refl _,
    by rw [hoq, hop], by rw [hpl]; omega_arith, hm.wsP, by rw [hpl]; exact hm.pws,
    by rw [hpl]; exact ⟨hm.pn, hm.pinv, hm.pone⟩, hP'.1, by rw [hpl]; exact hd.plt, hm.pmk, hd.qi,
    by rw [hqil]; exact hm.pl, h.qi.congrK hd.iscr hd.keep, by rw [hqil]; exact hpl1, by rw [hqil]; omega_arith,
    by rw [hqil, hpl]; omega_arith,
    fun hm' => by obtain ⟨_, _, hqi⟩ := hMk' hm'; simp only [hm', ↓reduceIte, hQIe]; exact hqi, hqil,
    hsp₁, ha₁, hd.msk, hpP₁, (preV_mask hP0).2⟩

/-! ### The parts -/

theorem frontX_ct (M : Mont) (hS : SetupCT) (hC : ChecksPCT) :
    RelCT isa (Two (StageX R0)) (seqs (nSetupP M.mm ++ primesSetup ++ checksP)) (Two (StageX R3)) := by
  refine stageX_step ((frontP_ct M hS hC).mono (fun _ _ h => two_bind (fun q t₁ t₂ h₁ h₂ => ⟨q, ?_, ?_⟩) h)
    fun _ _ _ => trivial) fun p σ xb pb qb dpb dqb qib t h hv ⟨hpq, hr2, _, _⟩ hr0 => ?_
  · obtain ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, hr0, ⟨hpq, hr2, _, _⟩, hsp, ha⟩ := h₁
    have e : t₁ = σ := hr0
    subst e
    exact ⟨⟨t₁, xb, pb, qb, dpb, dqb, qib, h, hv, rfl, hpq⟩, hsp, ha, hr2⟩
  · obtain ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, hr0, ⟨hpq, hr2, _, _⟩, hsp, ha⟩ := h₂
    have e : t₂ = σ := hr0
    subst e
    exact ⟨⟨t₂, xb, pb, qb, dpb, dqb, qib, h, hv, rfl, hpq⟩, hsp, ha, hr2⟩
  have e : t = σ := hr0
  subst e
  exact WP.mono (frontP_ok M h hv hr2 hpq) fun _ ⟨minv, mp, mq, hr⟩ => ⟨minv, mp, mq, hr⟩

theorem anySizesX_ct : RelCT isa (Two (StageX R3)) CrtIfma.anySizes (Two (StageX R3A)) :=
  stageX_step ((anySizes_ct).mono (fun _ _ h => two_drop h) fun _ _ _ => trivial)
    fun _ _ _ _ _ _ _ _ _ h _ _ ⟨minv, mp, mq, hr⟩ =>
      WP.mono (anySizes_ok h hr) fun _ ⟨zf, hr', _⟩ => ⟨⟨minv, mp, mq, hr'⟩, zf⟩

theorem preSX_ct (hl : LayOk l) (M : Mont) (hXm : RedcCT M Public.aXm)
    (hpre : (seqs (CrtIfma.preP M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    RelCT isa (Two (StageX (R3I l))) (seqs (CrtIfma.preP M.mm)) (Two (StageX (RAp l))) :=
  stageX_step ((preP_ct M hXm).mono (fun _ _ h => two_stageX (R := R3I l) (Φ := PrePreP) (fun q minv => (⟨⟨q.1.B, q.1.Z, q.1.w, minv, q.1.N,
      offP q.1.w, offQ q.1.w q.1.pl, l.W⟩, q.2.1, q.2.2⟩ : PrePubP))
    (fun _ _ _ _ _ _ _ _ _ h hv ⟨⟨⟨minv, _, _, hr⟩, hw, hp, hq⟩, ⟨_, _, hpP, hpQ⟩, hsp, ha⟩ =>
      ⟨minv, hr.nv, prePreP_of hl h hv hr rfl hw hp hq hpP hpQ hsp ha⟩) h) fun _ _ h => h)
    fun _ _ _ _ _ _ _ _ t h hv ⟨_, _, hpP, hpQ⟩ ⟨⟨minv, mp, mq, hr⟩, hw, hp, hq⟩ =>
      WP.mono (branchA1P_ok hl M h hv hr rfl hw hp hq
        (hpP.congr hr.iscr (hr.keep.gpr (by decide)) hr.keep.2.1 hr.keep.2.2)
        (hpQ.congr hr.iscr (hr.keep.gpr (by decide)) hr.keep.2.1 hr.keep.2.2) hpre)
        fun _ ⟨hA, _⟩ => ⟨minv, mp, mq, t, hr, hw, hp, hq, hA⟩

theorem ifmaAny_stage {l2 : CLay} (h2 : Lay2 l2) {p : CrtPub} {σ : State} {xb pb qb dpb dqb qib : List Byte}
    {t : State}
    (h : CrtPre σ p.B p.Z p.k p.op p.np p.ip p.pp p.qp p.dpp p.dqp p.qip p.pl p.ql p.nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid p.N p.k = true) (hr : AtLay l2 RAp p σ xb pb qb dpb dqb qib t) :
    WP isa (CrtIfma.ifmaAny l2) t (AtLay l2 RID p σ xb pb qb dpb dqb qib) := by
  have hs := sizes_of_rap h2 hr
  obtain ⟨minv, mp, mq, t₀, hr', hw, hp, hq, hA⟩ := hr
  exact WP.mono (ifmaAny_ok h2 (layOf_of l2 p.w) h hv hr' rfl hs hA) fun _ ⟨hd, _⟩ => ⟨minv, mp, mq, hd, hw, hp, hq⟩

theorem ifmaAnyX_ct {l2 : CLay} (h2 : Lay2 l2) :
    RelCT isa (Two (StageX (AtLay l2 RAp))) (CrtIfma.ifmaAny l2) (Two (StageX (AtLay l2 RID))) :=
  stageX_step ((ifmaAny_ct h2).mono (fun _ _ h => two_drop h) fun _ _ _ => trivial)
    fun _ _ _ _ _ _ _ _ _ h hv _ hr => ifmaAny_stage h2 h hv hr

theorem postSX_ct (hl : LayOk l) (M : Mont) (hL : LoadCT aChunk sQinv sPlen)
    (hpost : (seqs (CrtIfma.postP M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    RelCT isa (Two (StageX (RID l))) (seqs (CrtIfma.postP M.mm)) (Two (Stage R5)) :=
  (stageX_step (R' := R5) ((postP_ct M hL).mono (fun _ _ h => two_stageX (R := RID l) (Φ := PostPreP) (fun q _ => (⟨⟨q.1.B, q.1.Z, q.1.w,
      offP q.1.w, wsWords q.1.pl, offQ q.1.w q.1.pl, q.1.qip, q.1.pl⟩, q.2.1, q.2.2⟩ : PostPubP))
    (fun _ _ _ _ _ _ _ _ _ h hv ⟨⟨minv, _, _, hd, hw, hp, hq⟩, ⟨_, _, hpP, _⟩, hsp, ha⟩ =>
      ⟨minv, hd.nv, postPreP_of hl h hv hd rfl hw hp hq hpP hsp ha⟩) h) fun _ _ h => h)
    fun _ _ _ _ _ _ _ _ _ h hv ⟨_, _, hpP, _⟩ ⟨minv, mp, mq, hd, hw, hp, hq⟩ =>
      WP.mono (branchBP_ok hl M h hv hd rfl hw hp hq
        (hpP.congr hd.iscr (hd.keep.gpr (by decide)) hd.keep.2.1 hd.keep.2.2) hpost)
        fun _ ⟨hp', _⟩ => ⟨minv, mp, mq, hp'⟩).mono (fun _ _ h => h) fun _ _ h => two_drop h

/-- `atLay_ct` with the start's facts. -/
theorem atLayX_ct {l2 : CLay} (h2 : Lay2 l2) {R R' : CLay → StageRel} {c : Prog isa}
    (h : ∀ l, LayOk l → RelCT isa (Two (StageX (R l))) c (Two (StageX (R' l))))
    (hw : ∀ l p σ xb pb qb dpb dqb qib t, LayOk l → R' l p σ xb pb qb dpb dqb qib t → p.w = 2 * l.W) :
    RelCT isa (Two (StageX (AtLay l2 R))) c (Two (StageX (AtLay l2 R'))) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨q, h₁, h₂⟩ e₁ e₂
  obtain ⟨ht, q', ⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, hr, hx⟩,
    ⟨σ', xb', pb', qb', dpb', dqb', qib', hσ', hv', hr', hx'⟩⟩ :=
    h (layOf l2 q.1.w) (layOf_ok h2 _) s₁ s₂ t₁ t₂ s₁' s₂' ⟨q, h₁, h₂⟩ e₁ e₂
  have e : layOf l2 q'.1.w = layOf l2 q.1.w := by
    rw [hw _ _ _ _ _ _ _ _ _ _ (layOf_ok h2 _) hr, layOf_two h2 (layOf_of _ _)]
  refine ⟨ht, q', ⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, ?_, hx⟩,
    ⟨σ', xb', pb', qb', dpb', dqb', qib', hσ', hv', ?_, hx'⟩⟩
  · show R' (layOf l2 q'.1.w) q'.1 σ xb pb qb dpb dqb qib s₁'
    rw [e]; exact hr
  · show R' (layOf l2 q'.1.w) q'.1 σ' xb' pb' qb' dpb' dqb' qib' s₂'
    rw [e]; exact hr'

/-- The IFMA computation with `R_p²` and `R_q²` from `pre`, after
`anySizes` found the sizes of a layout. -/
theorem ifmaPartX_ct {l2 : CLay} (h2 : Lay2 l2) (M : Mont) (hXm : RedcCT M Public.aXm)
    (hL : LoadCT aChunk sQinv sPlen)
    (hpre : (seqs (CrtIfma.preP M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpost : (seqs (CrtIfma.postP M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    RelCT isa (Two (StageX (AtLay l2 R3I)))
      (seqs (CrtIfma.preP M.mm ++ ([CrtIfma.ifmaAny l2] : List (Prog isa)) ++ CrtIfma.postP M.mm))
      (Two (Stage R5)) := by
  rw [List.append_assoc]
  refine RelCT.seqs_append (by simp [CrtIfma.preP, CrtIfma.prepP]) (by simp)
    (RelCT.seq (atLayX_ct h2 (fun l hl => preSX_ct hl M hXm hpre)
      fun _ _ _ _ _ _ _ _ _ _ _ ⟨_, _, _, _, _, hw, _⟩ => hw) ?_)
  refine RelCT.seqs_append (by simp) (by simp [CrtIfma.postP]) (RelCT.seq (ifmaAnyX_ct h2) ?_)
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨q, h₁, h₂⟩ e₁ e₂
  exact postSX_ct (layOf_ok h2 q.1.w) M hL hpost s₁ s₂ t₁ t₂ s₁' s₂' ⟨q, h₁, h₂⟩ e₁ e₂

/-- `anySizes` and the branch on it, with `preP` and `postP`. -/
theorem dispatchX_ct {l2 : CLay} (h2 : Lay2 l2) (M : Mont) (hQ : QPhaseCT M (CrtExpL.w4 M))
    (hP : PPhaseCT M (CrtExpL.w4 M)) (hXm : RedcCT M Public.aXm) (hL : LoadCT aChunk sQinv sPlen)
    (hpre : (seqs (CrtIfma.preP M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpost : (seqs (CrtIfma.postP M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    RelCT isa (Two (StageX R3)) (.seq CrtIfma.anySizes (.ite .e (seqs (CrtIfma.preP M.mm ++
      ([CrtIfma.ifmaAny l2] : List (Prog isa)) ++ CrtIfma.postP M.mm))
      (seqs (qPhase M.mm (CrtExpL.w4 M).code ++ pPhase M.mm (CrtExpL.w4 M).code)))) (Two (Stage R5)) := by
  refine RelCT.seq anySizesX_ct (two_ite (fun q s₁ s₂ h₁ h₂ => ?_) ?_ ?_)
  · obtain ⟨_, _, _, _, _, _, _, _, _, ⟨_, z₁⟩, _⟩ := h₁
    obtain ⟨_, _, _, _, _, _, _, _, _, ⟨_, z₂⟩, _⟩ := h₂
    simp only [eval, z₁, z₂]
  · refine (ifmaPartX_ct h2 M hXm hL hpre hpost).mono (fun _ _ h => two_mono (fun q s h => ?_) h) fun _ _ h => h
    obtain ⟨⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, ⟨hr, hz⟩, hx⟩, he⟩ := h
    simp only [eval, hz, Option.some.injEq, decide_eq_true_eq] at he
    have hs := sizesOf_layOf h2 he
    obtain ⟨hW1, -⟩ := W_bounds (layOf_ok h2 q.1.w)
    exact ⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, ⟨hr, hs.1, by unfold wsWords; omega, by unfold wsWords; omega⟩, hx⟩
  · have d : ∀ (q : CrtPub × Addr × Addr) (s : State), StageX R3A q s ∧ isa.eval .e s = some false →
        Stage R3 q.1 s := fun _ _ ⟨⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, ⟨hr, _⟩, _⟩, _⟩ =>
      ⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, hr⟩
    exact (RelCT.seqs_append (by simp [qPhase]) (by simp [pPhase])
      (RelCT.seq (qS_ct M (CrtExpL.w4 M) hQ) (pS_ct M (CrtExpL.w4 M) hP))).mono
      (fun _ _ h => two_bind (fun q s₁ s₂ h₁ h₂ => ⟨q.1, d q s₁ h₁, d q s₂ h₂⟩) h) fun _ _ h => h

/-- `mainP` leaks the same in runs that agree on the public data, the stack
pointer and `pre`'s address, given that its parts do. -/
theorem mainP_ct {l2 : VG.Impl.Rsa.X86_64.CrtIfma.Lay} (h2 : Lay2 l2) (M : Mont) (hS : SetupCT) (hC : ChecksPCT)
    (hQ : QPhaseCT M (CrtExpL.w4 M)) (hP : PPhaseCT M (CrtExpL.w4 M))
    (hF : RelCT isa (Two (Stage R5)) (seqs finish) fun _ _ => True)
    (hXm : RedcCT M Public.aXm) (hL : LoadCT aChunk sQinv sPlen)
    (hpre : (seqs (CrtIfma.preP M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpost : (seqs (CrtIfma.postP M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    RelCT isa (Two (StageX R0)) (CrtIfma.mainP l2 M.mm) fun _ _ => True := by
  rw [mainP_eq]
  refine RelCT.seqs_append (by simp [nSetupP]) (by simp) (RelCT.seq (frontX_ct M hS hC) ?_)
  refine RelCT.seqs_append (by simp) (by simp [finish]) (RelCT.seq ?_ hF)
  exact dispatchX_ct h2 M hQ hP hXm hL hpre hpost

/-- `main`'s stage with `pre`, after the head and the modulus' check. -/
theorem cc3X_stage {q : CCPub × Addr} {t : State} (h : CC3W Prod.fst CCRelP q t)
    (he : isa.eval .ne t = some false) : StageX R0 (q.1.m, q.1.rsp, q.2) t := by
  obtain ⟨s, t₁, hs, hh, hm, k, hz⟩ := h
  have hv : Spec.Rsa.modulusValid q.1.m.N q.1.m.k = true := by
    simp only [eval, hz] at he; simpa using he
  obtain ⟨c, -, hB, hZ, hk, hop, hnp, hip, hpp, hqp, hdpp, hdqp, hqip, hpl, hql, hnb⟩ := ccRelP_ok q s hs
  obtain ⟨-, -, hp, hpq⟩ := crtCtxP_of hs.1
  obtain ⟨hpP, hpQ⟩ := crtPrimes_of hs.1
  have hsp := hs.2.1.1
  have harg := hs.2.2
  have hpre := crtPre_of c hh hm k
  have kk := hh.keep.trans k
  have hi : InScr (stackArg s 10) ((stackArg s 11).toNat * 8) s.mem t.mem := by rw [hm]; exact hh.inScr
  have ha : stackArg t 12 = q.2 := (hp.arg_eq hi (kk.gpr (by decide))).trans harg
  have hsp' : t.gpr .rsp = q.1.rsp := (kk.gpr (by decide)).trans hsp
  have hp' := hp.congr hi (kk.gpr (by decide)) kk.2.1 kk.2.2
  have hpP' := hpP.congr hi (kk.gpr (by decide)) kk.2.1 kk.2.2
  have hpQ' := hpQ.congr hi (kk.gpr (by decide)) kk.2.1 kk.2.2
  rw [hB, hZ, hk, hop, hnp, hip, hpp, hqp, hdpp, hdqp, hqip, hpl, hql] at hpre
  rw [hpp, hqp, hpl, hql, hnp, hk] at hpq
  rw [hB, hZ, hnp, hk] at hp'
  rw [hB, hZ, hk, hpp, hpl] at hpP'
  rw [hB, hZ, hk, hqp, hpl, hql] at hpQ'
  rw [hnp, hk] at hnb
  rw [hnb] at hpre hpq hp'
  exact ⟨t, _, _, _, _, _, _, hpre, hv, rfl, ⟨hpq, hp', hpP', hpQ'⟩, hsp', ha⟩

variable (M : Mont)

/-- `vg_rsa_private_crt_ifma_precomputed` leaks the same in runs that agree
on the public data and `pre`'s address, given that `main`'s parts do. -/
theorem codeP_ct {l2 : VG.Impl.Rsa.X86_64.CrtIfma.Lay} (h2 : Lay2 l2) (hS : SetupCT) (hC : ChecksPCT)
    (hQ : QPhaseCT M (CrtExpL.w4 M)) (hP : PPhaseCT M (CrtExpL.w4 M))
    (hF : RelCT isa (Two (Stage R5)) (seqs finish) fun _ _ => True)
    (hXm : RedcCT M Public.aXm) (hL : LoadCT aChunk sQinv sPlen)
    (hpre : (seqs (CrtIfma.preP M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpost : (seqs (CrtIfma.postP M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    RelCT isa (Two CCRelP) (CrtIfma.codeP l2 M.mm) fun _ _ => True := by
  unfold CrtIfma.codeP
  refine crtEntryWith_ct ccRelP_ok _ ?_
  exact (mainP_ct h2 M hS hC hQ hP hF hXm hL hpre hpost).mono (fun _ _ h => two_bind (fun q t₁ t₂ h₁ h₂ =>
    ⟨(q.1.m, q.1.rsp, q.2), cc3X_stage h₁.1 h₁.2, cc3X_stage h₂.1 h₂.2⟩) h) fun _ _ h => h

/-- `vg_rsa_private_crt_ifma_precomputed` is constant time but for `n` and
`pre`'s address. -/
theorem codeP_constantTime {l2 : VG.Impl.Rsa.X86_64.CrtIfma.Lay} (h2 : Lay2 l2)
    (hpre : (seqs (CrtIfma.preP M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpost : (seqs (CrtIfma.postP M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    ConstantTime isa crtContractP.pre crtContractP.pub (CrtIfma.codeP l2 M.mm) := by
  have hct := codeP_ct M h2 setup_ct checksP_ct
    (qPhase_ct M (CrtExpL.w4 M) (unit_ct M (gPow_ct_Q M) (redc_ct_Y M) (by taint_decide))
      (pow_ct M (CrtExpL.w4 M) (redc_ct_Y M) (CrtExpL.w4_ct M).2 (by taint_decide)))
    (pPhase_ct M (CrtExpL.w4 M) (unit_ct M (gPow_ct_P M) (redc_ct_Y M) (by taint_decide))
      (pow_ct M (CrtExpL.w4 M) (redc_ct_Y M) (CrtExpL.w4_ct M).1 (by taint_decide)) (redc_ct_X M) loadArr_ct_pI)
    crtFinish_ct (redc_ct_Xm M) loadArr_ct_pI hpre hpost
  refine RelCT.constantTime (hct.mono
    (fun s₁ s₂ ⟨h₁, h₂, hp, h12, _, _⟩ => ⟨(ccPubOf s₁, stackArg s₁ 12), ?_, ?_⟩) fun _ _ h => h)
  · exact ⟨h₁, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · obtain ⟨hr, a0, a1, a2, a3, a4, -, a6, -, a8, -, a10, a11, hn⟩ := hp
    have r : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
    exact ⟨h₂, ⟨r .rsp (by decide), a10.symm, by rw [← a11]; rfl, by rw [r .rcx (by decide)]; rfl,
      r .rdi (by decide), r .rdx (by decide), r .r8 (by decide), a0.symm, a2.symm, a4.symm, a6.symm, a8.symm,
      by rw [← a1]; rfl, by rw [← a3]; rfl, hn.symm⟩, h12.symm⟩

end VG.Proof.Bignum.X86_64.Ifma
