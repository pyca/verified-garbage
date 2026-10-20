module

public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTMr
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTMont
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Test
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTTail
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTFront
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Shape
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Fin
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaKeyGen.Slots
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTMr
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTMont
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Test
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTTail
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTFront
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Shape
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Fin
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.Slots

/-!
# An FFDH parameter candidate on AArch64: constant time of a test

The working space for a modulus (`phase_ct`), `p` loaded again
(`shapeP_ct`), the Montgomery setup, the exponent and the witnesses
(`testTail_ct`), and the results (`pResult_ct`, `qResult_ct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-! ## The working space -/

theorem phase_ct' (q : Bool) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0]) (.block (phaseHead q ++ Keys.head ++ [movi .x9 0])) hc).isSome = true) :
    RelCT isa (Two PH) (seqs (phase q)) fun _ _ => True := by
  have e : seqs (phase q) = .seq (.block (phaseHead q ++ Keys.head ++ [movi .x9 0]))
      (.seq (countLoop .x6 [.add .x .x9 .x9 .x9, .addImm .x .x9 .x9 1]) (.block [sth .x9 fTop])) := rfl
  rw [e]
  refine (pin_ct (Ψ := fun _ _ => True) [.x0] [.x0, .x6, .x9] (fun p r => match r with
      | .x0 => p.B | .x6 => BitVec.ofNat 64 (mK (p.mb q)) | _ => 0)
    (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.x0, h₂.x0])
    ht (fun p s h => phaseBlk_ok h q) (by taint_decide) fun p s h => ?_).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  rw [← e]
  exact WP.mono (phase_ok h q) fun _ _ => trivial

/-- `phase q` leaks the same in runs with the same public data. -/
theorem phase_ct (q : Bool) : RelCT isa (Two PH) (seqs (phase q)) fun _ _ => True := by
  cases q
  · exact phase_ct' false (by taint_decide)
  · exact phase_ct' true (by taint_decide)

/-- Before `shapeP`. -/
def SP (p : PP) (s : State) : Prop :=
  PSt p (mW p.bits) s ∧ word s.mem p.B (8 * sK) = BitVec.ofNat 64 p.L ∧ p.L ≤ p.r.length

/-- `shapeP` leaks the same in runs with the same public data. -/
theorem shapeP_ct : RelCT isa (Two SP) (seqs shapeP) fun _ _ => True := by
  unfold shapeP
  refine ct_app' (by simp [loadA]) (by simp) (Ψ := fun p t => Ws t p.B p.Z (mW p.bits))
    (two_post (loadA_ct0 (fun p : PP => p.B) (fun p : PP => p.Z) (fun p : PP => mW p.bits) (j := aN)
      (sPtr := kRand) (sLen := kLen) (by decide) (by decide) (by decide) (fun p => p.rp) (fun p => p.L)
      (fun p s h => ⟨h.1.ws, h.1.args.rand, h.2.1⟩) (by taint_decide) (by taint_decide) (by taint_decide))
      fun p s ⟨h, hK, hr⟩ => ?_) ?_
  · have hb1 := h.dims.b1
    have hb2 := h.dims.b2
    exact WP.mono (loadA_ok h.ws (j := aN) (sPtr := kRand) (sLen := kLen) (len := p.L) (bs := p.r.take p.L)
      (by decide) (by decide) (by decide) h.args.rand hK (src_take h.src p.L) (by rw [List.length_take]; omega)
      (by simp only [PP.L]; omega) (by simp only [PP.L, mW]; omega)) fun t ⟨_, o, _, _, k⟩ =>
        h.ws.congr' (Frm.of_outside o (List.mem_singleton_self _))
          (fun r hr => by rw [List.mem_singleton.mp hr]; exact KMut.ofSlot _ _ _) k (by decide)
  · rw [seqs_one]
    exact (ws_block_ct0 (fun p : PP => p.B) (fun p : PP => p.Z) (fun p : PP => mW p.bits) (fun _ _ h => h)
      (by taint_decide))

/-! ## The test's tail -/

/-- The public data of a test: the candidate's, the modulus's bits, the
modulus, and the octets read before it. -/
structure TD where
  p : PP
  mb : Nat
  N : Nat
  u : Nat

/-- The witnesses' public data of a test. -/
abbrev TD.tq (d : TD) : TQ := ⟨d.p, mW d.mb, d.N, d.mb, Spec.Ffdh.primeChecks d.mb, d.u⟩

/-- The setup's public data of a test. -/
abbrev TD.mq (d : TD) : MQ := ⟨⟨d.p.B, d.p.Z, mW d.mb⟩, d.N⟩

theorem tt_mp0 {d : TD} {s : State} (h : TT d.p d.mb d.N d.u s) : MP0 d.mq s := by
  have hmb1 := h.mb1
  have hmb2 := h.mb2
  exact ⟨h.st.ws, by simp only [mW]; omega, by simp only [mW]; omega, h.n, h.odd,
    Nat.le_trans (Nat.pow_le_pow_right (by decide) (by simp only [mW]; omega)) h.lo⟩

/-- The Montgomery setup, the exponent and the witnesses. -/
theorem testTail_ct (M : Mont) (R : Kernel) : RelCT isa (Two fun (d : TD) s => TT d.p d.mb d.N d.u s)
    (seqs (montPrep M.mm ++ expSetup ++ VG.Impl.Ffdh.AArch64.ParameterCandidate.millerRabin M.mm R.run))
    (Two TE) := by
  refine ct_app' (by simp [montPrep]) (by simp [VG.Impl.Ffdh.AArch64.ParameterCandidate.millerRabin])
    (Ψ := fun d s => TP d.tq s) (two_post (ct_app' (by simp [montPrep]) (by simp [expSetup, lowWord])
      (Ψ := fun d s => EQ d.mq s)
      (two_post (two_map TD.mq (fun _ _ h => tt_mp0 h) (montPrep_ct M)) fun d s h => ?_)
      (two_map TD.mq (fun _ _ h => h) expSetup_ct')) fun d s h => ?_)
    (two_map TD.tq (fun _ _ h => h) (millerRabin_ct M R))
  · have hN3 := h.dims.n3
    exact WP.mono (montPrep_ok M h.st.ws (by have := h.mb1; simp only [mW]; omega) h.n h.odd (tt_mp0 h).2.2.2.2.2)
      fun t ⟨hw, _, hn, _⟩ => ⟨hw, hn, h.odd, show 1 < d.N by omega⟩
  · exact WP.mono (testPre_ok M h) fun t ⟨fix, hU, _⟩ => ⟨h.dims, fix, hU, h.ul, primeChecks_pos _⟩

/-! ## The results -/

/-- The public data of a result: the working space, `out` and `used`, and
the status. -/
structure FQ where
  B : Addr
  Z : Nat
  w : Nat
  op : Addr
  up : Addr
  L : Nat
  st : Nat

/-- Before a result. -/
def EndF (q : FQ) (s : State) : Prop :=
  Ws s q.B q.Z q.w ∧ word s.mem q.B (8 * kOut) = q.op ∧ word s.mem q.B (8 * kLen) = BitVec.ofNat 64 q.L ∧
    word s.mem q.B (8 * kUsedP) = q.up ∧ OutUp s q.B q.Z q.op q.up q.L ∧
    word s.mem q.B (8 * kStat) = BitVec.ofNat 64 q.st ∧ q.st < 4

theorem pins_endf {Φ : FQ → State → Prop} (h : ∀ q s, Φ q s → EndF q s) : Pins Φ [.x0] :=
  pins_ws' (fun q : FQ => q.B) (fun q : FQ => q.Z) (fun q : FQ => q.w) fun _ _ hx => (h _ _ hx).1

/-- The working space and `used`'s pointer. -/
def UpF (q : FQ) (s : State) : Prop := Ws s q.B q.Z q.w ∧ word s.mem q.B (8 * kUsedP) = q.up

theorem EndF.up {q : FQ} {s : State} (h : EndF q s) : UpF q s := ⟨h.1, h.2.2.2.1⟩

theorem upLoadF_ok {s : State} {q : FQ} (h : UpF q s) {l : List Instr} (hl : l = [movi .x3 0] ∨ l = [ldh .x3 kUsed]) :
    WP isa (.block (l ++ [ldh .x2 kUsedP])) s fun t => ∀ r ∈ [Reg.x2], t.gpr r = q.up := by
  obtain ⟨hw, hU⟩ := h
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  have hl' : ∀ i < 32, InRegions (s.rd ++ s.wr) (off q.B (8 * i)) 8 := fun i hi => hw.scr.ld (by omega)
  refine WP.mono (Q := fun (t : State) => t.gpr .x2 = q.up) ?_ fun t h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h
  rcases hl with rfl | rfl
  · brun [hw.x0, hdr_enc (show kUsedP < 32 by decide), hl' kUsedP (by decide), hU]
  · brun [hw.x0, hdr_enc (show kUsedP < 32 by decide), hdr_enc (show kUsed < 32 by decide), hl' kUsedP (by decide),
      hl' kUsed (by decide), hU]

/-- `finNone` and `finUsed r`. -/
theorem finStoreF_ct {Φ : FQ → State → Prop} (hE : ∀ q s, Φ q s → UpF q s) {l : List Instr} (r : Nat)
    (hl : l = [movi .x3 0] ∨ l = [ldh .x3 kUsed]) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0]) (.block (l ++ [ldh .x2 kUsedP])) hc).isSome = true)
    {hc' : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht' : (taint.check (Taint.ofRegs [.x2]) (.block ([st .x3 .x2, movi .x0 r] : List Instr)) hc').isSome = true) :
    RelCT isa (Two Φ) (.block ((l ++ [ldh .x2 kUsedP]) ++ ([st .x3 .x2, movi .x0 r] : List Instr)))
      fun _ _ => True :=
  RelCT.block_append (RelCT.seq (two_piece (Ψ := fun q t => ∀ r ∈ [Reg.x2], t.gpr r = q.up) [.x0]
    (pins_ws' (fun q : FQ => q.B) (fun q : FQ => q.Z) (fun q : FQ => q.w) fun _ _ hx => (hE _ _ hx).1) ht
    fun _ _ h => upLoadF_ok (hE _ _ h) hl) (two_taint [.x2] (pins_of _ (fun q _ => q.up) fun _ _ h => h) ht'))

/-- After `used` is written. -/
def EndFO (q : FQ) (s : State) : Prop :=
  Ws s q.B q.Z q.w ∧ word s.mem q.B (8 * kOut) = q.op ∧ word s.mem q.B (8 * kLen) = BitVec.ofNat 64 q.L

theorem finPrimeF_ct {Φ : FQ → State → Prop} (hE : ∀ q s, Φ q s → EndF q s) :
    RelCT isa (Two Φ) finPrime fun _ _ => True := by
  rw [finPrime_eq]
  refine RelCT.seq (RelCT.block_append (RelCT.seq (two_piece (Ψ := fun q t => EndF q t ∧ t.gpr .x2 = q.up) [.x0]
    (pins_endf hE) (by taint_decide) fun q s h => ?_) (two_piece (Ψ := EndFO) [.x2] (pins_of _ (fun q _ => q.up)
      fun _ _ h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.2) (by taint_decide)
      fun q s h => ?_))) (RelCT.seq (two_piece [.x0] (pins_ws' (fun q : FQ => q.B) (fun q : FQ => q.Z)
        (fun q : FQ => q.w) fun _ _ h => h.1) (by taint_decide) fun q s h =>
          storeBlk_ok' h.1 (show kOut < 32 by decide) (show kLen < 32 by decide) h.2.1 h.2.2)
      (two_taint _ (pins_of _ (fun q => soVal' q.B (off q.B (slot q.w aN)) q.op q.L) fun _ _ h => h)
        (by taint_decide)))
  · have he := hE q s h
    refine WP.mono (WP.keep [.x3, .x2] (Q := fun t => t.gpr .x2 = q.up ∧ t.mem = s.mem)
      (WP.and (WP.mono (upLoadF_ok he.up (.inr rfl)) fun t h => h .x2 (by simp)) (by
        have hw := he.1
        have hn := hw.scr.nowrap
        have h256 := hw.h256
        brun [hw.x0, hdr_enc (show kUsedP < 32 by decide), hdr_enc (show kUsed < 32 by decide),
          hw.scr.ld (d := 8 * kUsedP) (by simp only [kUsedP, sFn]; omega),
          hw.scr.ld (d := 8 * kUsed) (by simp only [kUsed, sFn]; omega)]))
      (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h2, hm⟩, k⟩ => ⟨?_, h2⟩
    obtain ⟨hw, hO, hK, hU, ho, hS, hst⟩ := he
    exact ⟨hw.congr' (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide), by rw [hm]; exact hO,
      by rw [hm]; exact hK, by rw [hm]; exact hU, ho.congr k.wr, by rw [hm]; exact hS, hst⟩
  · obtain ⟨⟨hw, hO, hK, hU, ho, -⟩, h2⟩ := h
    have h256 := hw.h256
    refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW q.up (s.gpr .x3)) (by
      have hup : q.up + BitVec.ofNat 64 0 = q.up := off_zero q.up
      brun [h2, hup, ho.upw]) (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ => ?_
    have f : Frm q.B [(q.Z, 2 ^ 64)] s.mem t.mem := by rw [hm]; exact frm_up ho.upZ _ _
    have hw' : ∀ i < 32, word t.mem q.B (8 * i) = word s.mem q.B (8 * i) := fun i hi =>
      f.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega)) (by omega)
    exact ⟨hw.congr' f (fun r hr => by rw [List.mem_singleton.mp hr]; exact KMut.past h256 _) k (by decide),
      (hw' _ (by decide)).trans hO, (hw' _ (by decide)).trans hK⟩

theorem endF_load {q : FQ} {s : State} (h : EndF q s) :
    WP isa (.block [ldh .x3 kStat]) s fun t => EndF q t ∧ t.gpr .x3 = BitVec.ofNat 64 q.st := by
  obtain ⟨hw, hO, hK, hU, ho, hS, hst⟩ := h
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 q.st ∧ t.mem = s.mem)
    (by brun [hw.x0, hdr_enc (show kStat < 32 by decide), hw.scr.ld (d := 8 * kStat) (by simp only [kStat, sFn]; omega),
      hS]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h3, hm⟩, k⟩ =>
    ⟨⟨hw.congr' (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide), by rw [hm]; exact hO,
      by rw [hm]; exact hK, by rw [hm]; exact hU, ho.congr k.wr, by rw [hm]; exact hS, hst⟩, h3⟩

/-- `pResult` leaks the same in runs with the same public data. -/
theorem pResult_ct : RelCT isa (Two EndF) pResult fun _ _ => True := by
  unfold pResult
  refine RelCT.seq (two_piece (Ψ := fun q t => EndF q t ∧ t.gpr .x3 = BitVec.ofNat 64 q.st) [.x0]
    (pins_endf fun _ _ h => h) (by taint_decide) fun q s h => endF_load h)
    (two_ite (fun _ _ _ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2, h₂.2])
      (finStoreF_ct (fun _ _ h => h.1.1.up) 0 (.inl rfl) (by taint_decide) (by taint_decide))
      (RelCT.seq (two_piece (Ψ := fun q t => EndF q t ∧
          t.gpr .x3 = BitVec.ofNat 64 q.st - BitVec.ofNat 64 1) [] (pins_nil' _) (by taint_decide)
        fun q s h => ?_)
        (two_ite (fun _ _ _ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2, h₂.2])
          (finPrimeF_ct fun _ _ h => h.1.1)
          (finStoreF_ct (fun _ _ h => h.1.1.up) 2 (.inr rfl) (by taint_decide) (by taint_decide)))))
  obtain ⟨⟨⟨hw, hO, hK, hU, ho, hS, hst⟩, h3⟩, -⟩ := h
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 q.st - BitVec.ofNat 64 1 ∧
    t.mem = s.mem) (by brun [h3]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h3', hm⟩, k⟩ =>
    ⟨⟨hw.congr' (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide), by rw [hm]; exact hO,
      by rw [hm]; exact hK, by rw [hm]; exact hU, ho.congr k.wr, by rw [hm]; exact hS, hst⟩, h3'⟩

/-- `qResult` leaks the same in runs with the same public data. -/
theorem qResult_ct : RelCT isa (Two EndF) qResult fun _ _ => True := by
  unfold qResult
  exact RelCT.seq (two_piece (Ψ := fun q t => EndF q t ∧ t.gpr .x3 = BitVec.ofNat 64 q.st) [.x0]
    (pins_endf fun _ _ h => h) (by taint_decide) fun q s h => endF_load h)
    (two_ite (fun _ _ _ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2, h₂.2])
      (finStoreF_ct (fun _ _ h => h.1.1.up) 0 (.inl rfl) (by taint_decide) (by taint_decide))
      (finStoreF_ct (fun _ _ h => h.1.1.up) 2 (.inr rfl) (by taint_decide) (by taint_decide)))

end VG.Proof.Ffdh.AArch64.ParameterCandidate
