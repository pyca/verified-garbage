module

public import VerifiedGarbage.Proof.RsaPss.X86.VfLogic
import VerifiedGarbage.Proof.RsaPss.X86.SgEnc3
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt

/-!
# RSASSA-PSS verification with a precomputed public key on x86: the body

As on ARMv7 (`Proof/RsaPss/Arm/VfMain.lean`): the checks, then either 0 or
the call and the pieces after it, proven over the state the call leaves
(`VQ.reidx`); the result is `verify`'s (`fin_of`, `body_vq`). The stages keep
the addresses of the statics (`VP.syms`) for the indirect calls, and what the
tables give holds of the state the call leaves too (`hfacts_st`,
`tabfacts_st`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Vf

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes
open VG.Proof.RsaPss.X86.Sg (vpAssoc)

variable (h : PssHash)

/-- The end of the body, over the state `τ` the call leaves. -/
abbrev GE (P : EP) (τ t : State) : Prop :=
  Ctx (P.lay h.D) P.scr τ t ∧ K2 h P τ t.mem ∧
    t.gpr .eax = if acc2 h P τ = 0 ∧ HOk h P τ (if P.any = 0 then Mf h P τ else Ma h P τ) then 1 else 0

/-- The path for the expected salt length, or for any. -/
theorem tailIte_vp (P : EP) (hP : ∃ σ, In h.D P σ) {dn : String} {f : MdFns}
    (hTH : ∀ σ, P.TH σ → HFacts h dn f P.tabH P.hai P.hac P.had σ)
    (fne : f.init ≠ [] ∧ f.comp ≠ [] ∧ f.dig ≠ []) :
    VP (fun τ s => ((Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem) ∧ s.zf = some (decide (P.any = 0))) ∧
        s.syms = τ.syms)
      (.ite .e (fixedPathT f h.H) (anyPathT f h.H)) (fun τ s => GE h P τ s ∧ s.syms = τ.syms) := by
  refine VP.ite (fun σ s hs => ⟨decide (P.any = 0), by simp only [eval, hs.1.2]⟩)
    (fun _ _ _ _ h₁ h₂ => by simp only [eval, h₁.1.2, h₂.1.2]) ?_ ?_
  · by_cases ha : P.any = 0
    · exact (fixed_vp h P hP hTH fne).mono (fun τ s ⟨⟨⟨⟨hc, hk⟩, _⟩, sy⟩, _⟩ => ⟨⟨hc, hk, ha⟩, sy⟩)
        fun τ s ⟨⟨hc, hk, r0⟩, sy⟩ => ⟨⟨hc, hk, by rw [r0, ite_eq_left ha]⟩, sy⟩
    · exact VP.empty fun τ s ⟨⟨⟨_, z⟩, _⟩, e⟩ => by
        simp only [eval, z, decide_eq_false ha] at e; exact absurd e (by decide)
  · by_cases ha : P.any = 0
    · exact VP.empty fun τ s ⟨⟨⟨_, z⟩, _⟩, e⟩ => by
        simp only [eval, z, decide_eq_true ha] at e; exact absurd e (by decide)
    · exact (any_vp h P hP hTH fne).mono (fun τ s ⟨⟨⟨⟨hc, hk⟩, _⟩, sy⟩, _⟩ => ⟨⟨hc, hk, trivial⟩, sy⟩)
        fun τ s ⟨⟨hc, hk, r0⟩, sy⟩ => ⟨⟨hc, hk, by rw [r0, ite_eq_right ha]⟩, sy⟩

/-- After the call. -/
theorem rest_vp (P : EP) (hP : ∃ σ, In h.D P σ) {dn : String} {f : MdFns}
    (hTH : ∀ σ, P.TH σ → HFacts h dn f P.tabH P.hai P.hac P.had σ)
    (fneH : f.init ≠ [] ∧ f.comp ≠ [] ∧ f.dig ≠ []) {fG : Impl.RsaOaep.X86.Fns}
    (hT : ∀ σ, P.T σ → Proof.RsaOaep.X86.TabFacts P.g.H fG P.tab P.ai P.au P.af σ)
    (fne : fG.init ≠ [] ∧ fG.upd ≠ [] ∧ fG.fin ≠ []) :
    VP (fun τ s => W0 h P τ s ∧ s.syms = τ.syms)
      (seqs [.block accSet, .block acc0, .block (mgfArgsT h.H), Impl.RsaOaep.X86.mgfXor fG 15,
        .block topSet, .block topAnd, .block scanSet, countLoop scanBody, .block posChk,
        .ite .e (fixedPathT f h.H) (anyPathT f h.H)]) (fun τ s => GE h P τ s ∧ s.syms = τ.syms) :=
  vpAssoc ((Proof.RsaOaep.X86.VP.syms (acc_vp h P hP)).seq (unmask_vp h P hP hT fne
    ((Proof.RsaOaep.X86.VP.syms (scanSet_vp h P hP)).seq ((Proof.RsaOaep.X86.VP.syms (scan_vp h P hP)).seq
      ((Proof.RsaOaep.X86.VP.syms (pos_vp h P hP)).seq (tailIte_vp h P hP hTH fneH))))))

/-- The result is `verify`'s. -/
theorem fin_of (P : EP) {σ τ t : State} (hv : V2 h P σ τ) (hg : GE h P τ t) : Fin h P σ t := by
  obtain ⟨⟨hc, hi, hf, -⟩, hcr⟩ := hv
  obtain ⟨hc', hk, r0⟩ := hg
  have st : (P.lay h.D).St σ t :=
    ⟨hc.st.ok, hc'.st.sp, hc'.st.rd.trans hc.st.rd, hc'.st.wr.trans hc.st.wr, hc.st.frame.trans hc'.st.frame⟩
  refine ⟨⟨hi, st⟩, fun hpre => ?_⟩
  have hw := hcr hpre
  have hxb : Spec.Rsa.bytesAt τ.mem ((P.scr + BitVec.ofNat 32 oEm).setWidth 64) P.K =
      (Spec.Rsa.publicOpChecked P.nB P.eB (sigB P σ)).getD (Spec.RsaPss.zeros P.K) := by
    revert hw
    cases Spec.Rsa.publicOpChecked P.nB P.eB (sigB P σ) with
    | none => exact fun hw => hw.2
    | some y => exact fun hw => hw.2
  have hx : ∀ i < P.K, ((Spec.Rsa.publicOpChecked P.nB P.eB (sigB P σ)).getD (Spec.RsaPss.zeros P.K)).getD i 0 =
      emv P τ i := fun i hi' => by
    rw [← hxb, RsaPkcs1Sig.bytesAt_getD hi', (call_geo h hi).1, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have hdig : digB h P τ = digB h P σ := hc.st.ro (R := P.DIG h.D) (by simp)
  have g := good_iff h P τ hk.1 hf (RsaPkcs1Sig.bytesAt_len _ _ _) hx
  rw [hdig] at g
  rw [r0]
  by_cases e : acc2 h P τ = 0 ∧ HOk h P τ (if P.any = 0 then Mf h P τ else Ma h P τ)
  · rw [ite_eq_left e, ite_eq_left (g.1 e)]
  · rw [ite_eq_right e, ite_eq_right (fun h' => e (g.2 h'))]

/-- What the table of `MdHash` gives holds of a later state of the body. -/
theorem hfacts_st {P : EP} {σ τ : State} {dn : String} {f : MdFns} {ai ac ad : BitVec 32} (hi : In h.D P σ)
    (hs : (P.lay h.D).St σ τ) (sy : τ.syms = σ.syms) (hf : HFacts h dn f P.tabH ai ac ad σ) :
    HFacts h dn f P.tabH ai ac ad τ := by
  obtain ⟨R0, hR0, c0⟩ := hi.tblH 0 (by decide)
  obtain ⟨R3, hR3, c3⟩ := hi.tblH 3 (by decide)
  obtain ⟨R4, hR4, c4⟩ := hi.tblH 4 (by decide)
  exact ⟨by rw [sy]; exact hf.fi, by rw [sy]; exact hf.fc, by rw [sy]; exact hf.fd,
    by rw [Proof.RsaOaep.X86.St_roW hs hR0 c0]; exact hf.m0, by rw [Proof.RsaOaep.X86.St_roW hs hR3 c3]; exact hf.m3,
    by rw [Proof.RsaOaep.X86.St_roW hs hR4 c4]; exact hf.m4, by rw [sy]; exact hf.ai, by rw [sy]; exact hf.ac,
    by rw [sy]; exact hf.ad⟩

/-- What the table of `Hash` gives holds of a later state of the body. -/
theorem tabfacts_st {P : EP} {σ τ : State} {G : Impl.Pbkdf2.Stream.X86.Hash} {fG : Impl.RsaOaep.X86.Fns}
    {ai au af : BitVec 32} (hi : In h.D P σ) (hs : (P.lay h.D).St σ τ) (sy : τ.syms = σ.syms)
    (hf : Proof.RsaOaep.X86.TabFacts G fG P.tab ai au af σ) : Proof.RsaOaep.X86.TabFacts G fG P.tab ai au af τ := by
  obtain ⟨R, hR, hc⟩ := hi.tbl
  have e : ∀ o, o + 4 ≤ 20 → τ.mem.readW (VG.X86.addr P.tab o) 32 = σ.mem.readW (VG.X86.addr P.tab o) 32 :=
    fun o ho => Proof.RsaOaep.X86.St_roW hs hR (hc o ho)
  obtain ⟨m0, m4, m8⟩ := hf.mem
  exact ⟨by rw [sy]; exact hf.ok, ⟨by rw [e 0 (by decide), sy]; exact m0, by rw [e 4 (by decide), sy]; exact m4,
    by rw [e 8 (by decide), sy]; exact m8⟩, by rw [e 16 (by decide)]; exact hf.d, by rw [sy]; exact hf.ai,
    by rw [sy]; exact hf.au, by rw [sy]; exact hf.af⟩

/-- The body, with the hash function of the table of `MdHash` and MGF1's of
the table of `Hash`, whose facts hold of every later state of the body. -/
theorem body_vq (P : EP) (c : Ver.PublicImpl) {dn : String} {f : MdFns}
    (hTH : ∀ σ, P.TH σ → HFacts h dn f P.tabH P.hai P.hac P.had σ)
    (hTHs : ∀ σ τ, In h.D P σ → (P.lay h.D).St σ τ → τ.syms = σ.syms → P.TH τ)
    (fneH : f.init ≠ [] ∧ f.comp ≠ [] ∧ f.dig ≠ []) {fG : Impl.RsaOaep.X86.Fns}
    (hT : ∀ σ, P.T σ → Proof.RsaOaep.X86.TabFacts P.g.H fG P.tab P.ai P.au P.af σ)
    (hTs : ∀ σ τ, In h.D P σ → (P.lay h.D).St σ τ → τ.syms = σ.syms → P.T τ)
    (fne : fG.init ≠ [] ∧ fG.upd ≠ [] ∧ fG.fin ≠ []) :
    VQ (fun σ s => S h P σ s ∧ s.syms = σ.syms) (verifyTail f h.H fG c.name c.code) (Fin h P) := by
  by_cases hP : ∃ σ, In h.D P σ
  swap
  · exact VQ.of_vp (VP.empty fun σ s hs => hP ⟨σ, hs.1.1⟩)
  show VQ _ (.seq (.block (verifyChk ++ params h.H)) (.ite .ne (.block [mi .eax 0])
    (.seq (.block pubArgs) (.seq (.call c.name c.code) _)))) _
  refine VQ.seq (Proof.RsaOaep.X86.VP.syms (chk_vp h P)) (VQ.ite (fun σ s hs => ⟨!decide (fits h P), by
      simp only [eval, hs.1.2.2.2.2.2.2, Option.map_some]⟩)
    (fun _ _ _ _ h₁ h₂ => by simp only [eval, h₁.1.2.2.2.2.2.2, h₂.1.2.2.2.2.2.2])
    (VQ.of_vp ((fail_vp h P).mono (fun σ s ⟨⟨hc, _⟩, e⟩ => ⟨hc, e⟩) fun _ _ h => h)) ?_)
  refine VQ.seq ((Proof.RsaOaep.X86.VP.syms (pa_vp h P)).mono (fun σ s ⟨⟨h1, sy⟩, e⟩ => ⟨m0_of h h1 e, sy⟩)
    fun _ _ h => h) (VQ.seq (Proof.RsaOaep.X86.VP.syms (call_vp h P c)) (VQ.reidx (rest_vp h P hP hTH fneH hT fne)
      (fun σ s ⟨hv, sy⟩ => ⟨w0_self h hv (hTHs σ s hv.1.2.1 hv.1.1.st sy) (hTs σ s hv.1.2.1 hv.1.1.st sy), rfl⟩)
      fun σ τ t ⟨hv, _⟩ hg => fin_of h P hv hg.1))

end VG.Proof.RsaPss.X86.Vf
