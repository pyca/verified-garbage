import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Main
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombTiming

/-! Verification's table lookup uses only the public digest and signature. -/
namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 (U V)
variable {c : Cfg}

/-- The scalar is determined by the public digest and signature. -/
def publicU (c : Cfg) (s : State) : Nat :=
  (Fin.ofNat c.C.n (dig c s >>> c.sh) * Fin.ofNat c.C.n (sigS c s) ^ (c.C.n - 2)).val

/-- Equality of the digest and signature buffers implies equality of the
public lookup scalar, without reducing concrete curve arithmetic. -/
theorem publicU_congr {c : Cfg} {a b : State}
    (hd : Spec.Ecdsa.bytesAt a.mem (a.gpr .x1) c.C.len =
      Spec.Ecdsa.bytesAt b.mem (b.gpr .x1) c.C.len)
    (hs : Spec.Ecdsa.bytesAt a.mem (a.gpr .x2) (2 * c.C.len) =
      Spec.Ecdsa.bytesAt b.mem (b.gpr .x2) (2 * c.C.len)) : publicU c a = publicU c b := by
  rw [Nat.two_mul, bytesAt_add, bytesAt_add] at hs
  have hs' := (List.append_inj hs (by simp only [length_bytesAt])).2
  have hd' : dig c a = dig c b := congrArg Spec.Weierstrass.ofBytes hd
  have hss : sigS c a = sigS c b := congrArg Spec.Weierstrass.ofBytes hs'
  simp only [publicU, hd', hss]

theorem mid_publicU {c : Cfg} {s₀ s : State} {base : Addr} {g : Reg → BitVec 64}
    (h : Mid c s₀ base g s) : sv c base s U = publicU c s₀ := by
  have he := congrArg Fin.val h.u
  simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt h.u_lt, publicU] using he

/-- The state needed at the public comb boundary. -/
def CombReady (c : Cfg) (s₀ s : State) : Prop :=
  Scr s (s₀.gpr .x3) size ∧ ModOkA c.combCfg.M size c.C.p s.mem (s₀.gpr .x3) ∧
    TCombFixed c.combCfg c.C (s₀.gpr .x3) size s (publicU c s₀) (s₀.syms c.tsym) c.combWords

/-- Build the bit table and recover the fixed-base comb's precondition. -/
theorem bits_combReady (hc : CfgOk c) {s₀ s : State} {g : Reg → BitVec 64}
    (hM : Mid c s₀ (s₀.gpr .x3) g s) (hTP : TblPre c s₀ (s₀.syms c.tsym) (s₀.gpr .x3)) :
    WP isa (bits (c.sl U) (bitsAt c.n 0) (8 * c.n)) s (CombReady c s₀) := by
  let base := s₀.gpr .x3
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hM.scr.nowrap
  have hp3 := hc.p_ge
  have F := hM.fixed
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  refine WP.mono_syms (bits_ok hM.scr h0 (by omega) (sl_le c h7 (i := U) (by decide))
    (tbl_le h7) (sl_lt4096 h0 h7 (i := U) (by decide)) (by have := bitsAt0_le c h7; omega)
    (Or.inl (by have := sl_below_bits c (i := U) (by decide) 0 0; omega)))
    fun s₁ ⟨b₁, k₁, O₁⟩ sy₁ => ?_
  have hs₁ := hM.scr.of_keepRegs k₁ (by decide)
  have U₁ : Unch base [(bitsAt c.n 0, 64 * c.n)] s.mem s₁.mem := O₁.unch
  have F₁ := F.unch h7 hn (fixedOk_tbl 0) U₁
  obtain ⟨hTM, hout⟩ := tbl_of hTP hM.rd hM.unch
  have hTM₁ : TblMem s₁ (s₀.syms c.tsym) c.combWords :=
    TblMem.of_unch hTM (by rw [k₁.rd, k₁.wr]) U₁ (fun w hw => by
      rw [List.mem_singleton.mp hw]; exact tbl_le h7) hout
  refine ⟨hs₁, modP_of hc F₁.mp, ?_⟩
  rw [← mid_publicU hM]
  refine ⟨?_, ?_, ?_, F₁.zero, ?_, wordsVal_lt _ _ _ _, by rw [sy₁, hM.syms]; rfl, hTM₁, hout⟩
  · show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₁.mem base (c.sl AP) c.n) = _
    rw [F₁.ap]; exact toM_cmont hc _
  · show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₁.mem base (c.sl BM) c.n) = _
    rw [F₁.bm]; exact toM_cmont hc _
  · intro x hx
    simp only [combRo, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · show wordsVal s₁.mem base (c.sl AP) c.n < _; rw [F₁.ap]; exact hmont _
    · show wordsVal s₁.mem base (c.sl BM) c.n < _; rw [F₁.bm]; exact hmont _
    · show wordsVal s₁.mem base (c.sl ZERO) c.n < _; rw [F₁.zero]; omega
  · intro t ht
    show s₁.mem (off base (bitsAt c.n 0 + t)) = _
    rw [b₁ t ht]

/-- Everything up to the public comb, with an empty final block. -/
def verifyPrefix (c : Cfg) : Prog isa :=
  .seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.args c)) <|
  .seq (Impl.Ecdh.AArch64.Cfg.prefixWith c (some D)) <|
  .seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.loadS c)) <|
  .seq (.block (Impl.Ecdh.AArch64.Cfg.peer c)) <|
  .seq (Impl.Ecdh.AArch64.Cfg.validate c) <|
  .seq (Impl.Ecdsa.Verify.AArch64.Cfg.scalars c) <| .seq c.nPow <|
  .seq (Impl.Ecdsa.Verify.AArch64.Cfg.uv c) <|
  .seq (bits (c.sl U) (bitsAt c.n 0) (8 * c.n)) (.block [])

/-- After the public comb. -/
def verifySuffix (c : Cfg) : Prog isa :=
  .seq (.seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.save c))
    (.seq (c.winPrep (c.sl V)) (.seq (WinCfg.window (winQ c)) (Impl.Ecdsa.Verify.AArch64.Cfg.sum c))))
    (.seq c.pPow (Impl.Ecdsa.Verify.AArch64.Cfg.final c))

theorem verifyPrefix_ok (hc : CfgOk c) {s₀ : State} (hp : VPre c s₀) :
    WP isa (verifyPrefix c) s₀ (CombReady c s₀) := by
  refine front_ok hc hp fun g s₁ _ hF => mid_ok hc hF fun s₂ hM => ?_
  exact WP.seq (WP.mono (bits_combReady hc hM hp.tbl) fun _ h => WP.block_nil h)

/-- Splitting a full execution at the public lookup, preserving its trace. -/
theorem verify_cut {c : Cfg} {s s' : State} {t : List Leak}
    (he : Exec isa (Impl.Ecdsa.Verify.AArch64.Cfg.verify c) s t s') :
    ∃ a b tp tc ts, Exec isa (verifyPrefix c) s tp a ∧
      Exec isa (c.combCfg.comb (c.C.len == 32)) a tc b ∧ Exec isa (verifySuffix c) b ts s' ∧
      t = tp ++ tc ++ ts := by
  cases he with
  | seq e0 h => cases h with
    | seq e1 h => cases h with
      | seq e2 h => cases h with
        | seq e3 h => cases h with
          | seq e4 h => cases h with
            | seq e5 h => cases h with
              | seq e6 h => cases h with
                | seq e7 h => cases h with
                  | seq ep h =>
                    cases ep with
                    | seq eb h => cases h with
                      | seq ec er =>
                        have nil : ∀ a : State, Exec isa (.block []) a [] a := fun _ => .block rfl
                        have epre := Exec.seq e0 (.seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5
                          (.seq e6 (.seq e7 (.seq eb (nil _)))))))))
                        refine ⟨_, _, _, _, _, epre, ec, .seq er h, ?_⟩
                        simp only [List.append_nil, List.append_assoc]

/-- The shared contract makes the scalar, pointers and table address public. -/
def VerifyPublic (c : Cfg) (a b : State) : Prop :=
  AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3]) a b ∧
    a.syms c.tsym = b.syms c.tsym ∧ publicU c a = publicU c b

structure VerifyChecks (c : Cfg) : Prop where
  comb : PublicChecks c.combCfg
  before : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3])) (verifyPrefix c)
  after : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0])) (verifySuffix c)

/-- Timing of the entire verifier, allowing exactly its public inputs to
influence the selected addresses. -/
theorem verify_public_ct (hc : CfgOk c) (hC : Law c.C)
    (hT : CombOkW c.C Cfg.combW (Cfg.combJ c.n) c.tbl c.start)
    (hLookup : (c.C.len == 32) = true) (checks : VerifyChecks c) :
    ConstantTime isa (VPre c) (VerifyPublic c) (Impl.Ecdsa.Verify.AArch64.Cfg.verify c) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ ⟨pub, sym, scalar⟩ e₁ e₂
  obtain ⟨a₁, b₁, tp₁, tc₁, ts₁, ep₁, ec₁, es₁, et₁⟩ := verify_cut e₁
  obtain ⟨a₂, b₂, tp₂, tc₂, ts₂, ep₂, ec₂, es₂, et₂⟩ := verify_cut e₂
  rw [hLookup] at ec₁ ec₂
  have ht := checks.before _ _ _ _ _ _ trivial trivial pub ep₁ ep₂
  obtain ⟨_, _, wp₁, ready₁⟩ := verifyPrefix_ok hc pre₁
  obtain ⟨_, _, wp₂, ready₂⟩ := verifyPrefix_ok hc pre₂
  obtain ⟨_, rfl⟩ := Exec.det ep₁ wp₁
  obtain ⟨_, rfl⟩ := Exec.det ep₂ wp₂
  have base : s₁.gpr .x3 = s₂.gpr .x3 := pub.2 .x3 (by decide)
  have sp : a₁.sp = a₂.sp := (Exec.rdwr ep₁).2.2.trans (pub.1.trans (Exec.rdwr ep₂).2.2.symm)
  have second : Scr a₂ (s₁.gpr .x3) size ∧ ModOkA c.combCfg.M size c.C.p a₂.mem (s₁.gpr .x3) ∧
      TCombFixed c.combCfg c.C (s₁.gpr .x3) size a₂ (publicU c s₁) (s₁.syms c.tsym) c.combWords := by
    rw [base, scalar, sym]; exact ready₂
  have hh := publicComb_ct (tcombLay hc) (combA c) hC hc.am3 hc.onG (tcombVals hc hC hT)
    hc.p_lt checks.comb _ _ _ _ _ _
    ⟨ready₁.1, second.1, sp, ready₁.2.1, second.2.1, ready₁.2.2, second.2.2⟩ ec₁ ec₂
  have wpComb := fun {s₀ a : State} (h : CombReady c s₀ a) =>
    tcomb_ok (publicLookup := true) (tcombLay hc) (combA c) hC hc.am3 hc.onG
      (tcombVals hc hC hT) hc.p_lt h.1 h.2.1 h.2.2
  obtain ⟨_, _, wc₁, keep₁, _⟩ := wpComb ready₁
  obtain ⟨_, _, wc₂, keep₂, _⟩ := wpComb ready₂
  obtain ⟨_, rfl⟩ := Exec.det ec₁ wc₁
  obtain ⟨_, rfl⟩ := Exec.det ec₂ wc₂
  have ht' := checks.after _ _ _ _ _ _ trivial trivial
    ⟨keep₁.sp.trans (sp.trans keep₂.sp.symm), fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst hr
      rw [keep₁.gpr _ (x0_not_tcombClob hc.n10), keep₂.gpr _ (x0_not_tcombClob hc.n10),
        ready₁.1.x0, ready₂.1.x0, base]⟩ es₁ es₂
  rw [et₁, et₂, ht, hh.1, ht']

end VG.Proof.Ecdsa.Verify.AArch64
