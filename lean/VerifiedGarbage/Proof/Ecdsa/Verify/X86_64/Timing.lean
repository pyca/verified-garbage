import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Main
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombTiming

/-! Verification lookups depend only on public digest and signature inputs. -/
namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64
open VG.Impl.Ecdsa.Verify.X86_64 (U V)
variable {c : Cfg}

def publicU (c : Cfg) (s : State) : Nat :=
  (Fin.ofNat c.C.n (dig c s) * Fin.ofNat c.C.n (sigS c s) ^ (c.C.n - 2)).val

theorem publicU_congr {c : Cfg} {a b : State}
    (hd : Spec.Ecdsa.bytesAt a.mem (a.gpr .rsi) c.C.len =
      Spec.Ecdsa.bytesAt b.mem (b.gpr .rsi) c.C.len)
    (hs : Spec.Ecdsa.bytesAt a.mem (a.gpr .rdx) (2 * c.C.len) =
      Spec.Ecdsa.bytesAt b.mem (b.gpr .rdx) (2 * c.C.len)) : publicU c a = publicU c b := by
  rw [Nat.two_mul,bytesAt_add,bytesAt_add] at hs
  have hs' := (List.append_inj hs (by simp only [length_bytesAt])).2
  have hd' : dig c a = dig c b := congrArg (fun bs => Spec.Weierstrass.ofBytes bs >>> c.sh) hd
  have hss : sigS c a = sigS c b := congrArg Spec.Weierstrass.ofBytes hs'
  simp only [publicU,hd',hss]

theorem mid_publicU {s₀ s : State} {base : Addr} {g : Reg → BitVec 64}
    (h : Mid c s₀ base g s) : sv c base s U = publicU c s₀ := by
  have he := congrArg Fin.val h.u
  simpa only [Fin.val_ofNat,Nat.mod_eq_of_lt h.u_lt,publicU] using he

def CombReady (c : Cfg) (d : CombData) (s₀ s : State) : Prop :=
  Scr s (s₀.gpr .rcx) size ∧ ModOkW (c.combCfg d).M size c.C.p s.mem (s₀.gpr .rcx) ∧
    TCombFixed (c.combCfg d) c.C (s₀.gpr .rcx) size s (publicU c s₀) (s₀.syms d.tsym) (c.combWords d)

theorem bits_combReady (hc : BaseCfgOk c) {d : CombData} (hcd : c.comb = some d)
    {s₀ s : State} {g : Reg → BitVec 64} (hp : VPre c s₀) (hM : Mid c s₀ (s₀.gpr .rcx) g s) :
    WP isa (.seq (bits (c.sl U) (bitsAt c.n 0) (8 * c.n))
      (.block (setConst c.n (c.sl EM) (c.mont c.C.b)))) s (CombReady c d s₀) := by
  let base := s₀.gpr .rcx
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hM.scr.nowrap
  have hp3 := hc.p_ge
  have F := hM.fixed
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  refine WP.seq (WP.mono_syms (bits_ok hM.scr h0 (by omega) (sl_le c h7 (i := U) (by decide))
    (bitsAt_le c h7 (j := 0) (by decide))
    (Or.inl (by have := sl_below_bits c (i := U) (by decide) 0 0; omega)))
    fun s₁ ⟨b₁,k₁,O₁⟩ sy₁ => ?_)
  have hs₁ := hM.scr.of_keepRegs k₁ (by decide)
  have U₁ : Unch base [(bitsAt c.n 0,64*c.n)] s.mem s₁.mem := O₁.unch
  have F₁ := F.unch h7 hn (fixedOk_tbl 0) U₁
  have hTb : TblMem s₁ (s₁.syms d.tsym) (c.combWords d) ∧
      ∀ i < (c.combWords d).length, ∀ b < 8,
        size ≤ ofs base (s₁.syms d.tsym + BitVec.ofNat 64 (8*i) + BitVec.ofNat 64 b) := by
    rw [sy₁,hM.syms]
    refine tbl_of_held hcd hp.tbls (by rw [hp.wr]; simp only [List.mem_singleton]; rfl)
      (fun r hr => by rw [k₁.rd,hM.rd,hp.rd]; simp [hr]) ?_
    have hb0 := bitsAt_le c h7 (j := 0) (by decide)
    exact Unch.cover (hM.unch.trans U₁) fun w hw => by
      simp only [List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl | rfl
      · exact ⟨_,List.mem_singleton_self _,Nat.le_refl _,Nat.le_refl _⟩
      · exact ⟨_,List.mem_singleton_self _,Nat.zero_le _,by dsimp only; omega⟩
  obtain ⟨hTM,hout⟩ := hTb
  refine WP.mono_syms (setConst_ok hs₁ (n := c.n) (o := c.sl EM) (x := c.mont c.C.b)
    (sl_le c h7 (by decide)) (Nat.lt_trans (hmont _) hc.p_lt))
    fun s₂ ⟨e₂,k₂,O₂⟩ sy₂ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have F₂ := F₁.unch h7 hn (fixedOk_slW (l := [EM]) (by decide)) O₂.unch
  have ht₂ : ∀ t < 64*c.n, s₂.mem (off base (bitsAt c.n 0+t)) =
      if (sv c base s U).testBit t then 1 else 0 := fun t ht => by
    rw [tbl_unch (W := slW c [EM]) O₂.unch h7 hn (j := 0) (by decide) ht
      (tbl_apart_slW (by decide) 0 t)]
    exact b₁ t ht
  have hTM₂ : TblMem s₂ (s₁.syms d.tsym) (c.combWords d) :=
    hTM.of_unch (by rw [k₂.rd,k₂.wr]) O₂.unch (fun w hw => by
      rw [List.mem_singleton.mp hw]; exact sl_le c h7 (by decide)) hout
  refine ⟨hs₂,modP_of hc F₂.mp,?_⟩
  rw [← mid_publicU hM]
  have sym : s₂.syms d.tsym = s₀.syms d.tsym := by rw [sy₂,sy₁,hM.syms]
  refine ⟨?_,?_,fun x hx => ?_,F₂.zero,ht₂,wordsVal_lt _ _ _ _,sym,?_,?_⟩
  · show toM c.C.p (2 ^ (64*c.n)) (wordsVal s₂.mem base (c.sl AP) c.n) = _
    rw [F₂.ap]; exact toM_cmont hc _
  · show toM c.C.p (2 ^ (64*c.n)) (wordsVal s₂.mem base (c.sl EM) c.n) = _
    rw [e₂]; exact toM_cmont hc _
  · simp only [combRo,TCombCfg.toComb,Cfg.combCfg,Cfg.rcbSlots,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact lt_of_eq_of_lt F₂.ap (hmont _)
    · exact lt_of_eq_of_lt e₂ (hmont _)
    · exact lt_of_eq_of_lt F₂.zero (by omega)
  · rw [sy₁,hM.syms] at hTM₂; exact hTM₂
  · rw [sy₁,hM.syms] at hout; exact hout

def verifyPrefix (c : Cfg) : Prog isa :=
  .seq (.block (Impl.Ecdsa.Verify.X86_64.Cfg.args c)) <|
  .seq (Impl.Ecdh.X86_64.Cfg.prefix' c (some D)) <|
  .seq (.block (Impl.Ecdsa.Verify.X86_64.Cfg.loadS c)) <|
  .seq (.block (Impl.Ecdh.X86_64.Cfg.peer c)) <|
  .seq (Impl.Ecdh.X86_64.Cfg.validate c) <|
  .seq (Impl.Ecdsa.Verify.X86_64.Cfg.scalars c) <| .seq c.nPow <|
  .seq (Impl.Ecdsa.Verify.X86_64.Cfg.uv c) <|
  .seq (bits (c.sl U) (bitsAt c.n 0) (8*c.n)) <|
  .seq (.block (setConst c.n (c.sl EM) (c.mont c.C.b))) (.block [])

def verifySuffix (c : Cfg) : Prog isa :=
  .seq (.seq (.block (Impl.Ecdsa.Verify.X86_64.Cfg.save c))
    (.seq (Impl.Ecdsa.Verify.X86_64.Cfg.mulV c) (Impl.Ecdsa.Verify.X86_64.Cfg.sum c)))
    (Impl.Ecdsa.Verify.X86_64.Cfg.tail c)

theorem verifyPrefix_ok (hc : BaseCfgOk c) {d : CombData} (hcd : c.comb = some d)
    {s₀ : State} (hp : VPre c s₀) : WP isa (verifyPrefix c) s₀ (CombReady c d s₀) := by
  refine front_ok hc hp fun g s₁ _ hF => mid_ok hc hF fun s₂ hM => ?_
  have h := bits_combReady hc hcd hp hM
  rw [WP.seq_iff] at h
  refine WP.seq (WP.mono h fun s₃ h₃ => WP.seq (WP.mono h₃ fun _ h₄ => WP.block_nil h₄))

private theorem gMul_cut {d : CombData} (hcd : c.comb = some d) {s s' : State} {t : List Leak}
    (he : Exec isa (c.gMul c.pubVerify) s t s') :
    ∃ a tp tc, Exec isa (.block (setConst c.n (c.sl EM) (c.mont c.C.b))) s tp a ∧
      Exec isa ((c.combCfg d).comb c.pubVerify) a tc s' ∧ t = tp ++ tc := by
  rw [Cfg.gMul,hcd] at he
  cases he with
  | seq ep ec => exact ⟨_,_,_,ep,ec,rfl⟩

theorem verify_cut {d : CombData} (hcd : c.comb = some d) {s s' : State} {t : List Leak}
    (he : Exec isa (Impl.Ecdsa.Verify.X86_64.Cfg.verify c) s t s') :
    ∃ a b tp tc ts, Exec isa (verifyPrefix c) s tp a ∧
      Exec isa ((c.combCfg d).comb c.pubVerify) a tc b ∧ Exec isa (verifySuffix c) b ts s' ∧
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
                    | seq eb h' => cases h' with
                      | seq eg er =>
                        obtain ⟨_,_,_,eset,ec,etg⟩ := gMul_cut hcd eg
                        have nil : ∀ a : State, Exec isa (.block []) a [] a := fun _ => .block rfl
                        have epre := Exec.seq e0 (.seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5
                          (.seq e6 (.seq e7 (.seq eb (.seq eset (nil _))))))))))
                        refine ⟨_,_,_,_,_,epre,ec,.seq er h,?_⟩
                        simp only [etg,List.append_nil,List.append_assoc]

def VerifyPublic (c : Cfg) (d : CombData) (a b : State) : Prop :=
  X86_64.Taint.Agree (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx]) a b ∧
    a.syms d.tsym = b.syms d.tsym ∧ publicU c a = publicU c b

structure VerifyChecks (c : Cfg) (d : CombData) : Prop where
  comb : PublicChecks (c.combCfg d)
  before : ConstantTime isa (fun _ => True)
    (X86_64.Taint.Agree (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])) (verifyPrefix c)
  after : ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs [.rdi])) (verifySuffix c)

theorem verify_public_ct (hc : BaseCfgOk c) (hC : Law c.C) (hT : CombTbls c)
    {d : CombData} (hcd : c.comb = some d) (hLookup : c.pubVerify = true)
    (checks : VerifyChecks c d) :
    ConstantTime isa (VPre c) (VerifyPublic c d) (Impl.Ecdsa.Verify.X86_64.Cfg.verify c) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ ⟨pub,sym,scalar⟩ e₁ e₂
  obtain ⟨a₁,b₁,tp₁,tc₁,ts₁,ep₁,ec₁,es₁,et₁⟩ := verify_cut hcd e₁
  obtain ⟨a₂,b₂,tp₂,tc₂,ts₂,ep₂,ec₂,es₂,et₂⟩ := verify_cut hcd e₂
  rw [hLookup] at ec₁ ec₂
  have ht := checks.before _ _ _ _ _ _ trivial trivial pub ep₁ ep₂
  obtain ⟨_,_,wp₁,ready₁⟩ := verifyPrefix_ok hc hcd pre₁
  obtain ⟨_,_,wp₂,ready₂⟩ := verifyPrefix_ok hc hcd pre₂
  obtain ⟨_,rfl⟩ := Exec.det ep₁ wp₁
  obtain ⟨_,rfl⟩ := Exec.det ep₂ wp₂
  have base : s₁.gpr .rcx = s₂.gpr .rcx := pub.rf.1 .rcx (by decide)
  have second : Scr a₂ (s₁.gpr .rcx) size ∧ ModOkW (c.combCfg d).M size c.C.p a₂.mem (s₁.gpr .rcx) ∧
      TCombFixed (c.combCfg d) c.C (s₁.gpr .rcx) size a₂ (publicU c s₁) (s₁.syms d.tsym) (c.combWords d) := by
    rw [base,scalar,sym]; exact ready₂
  have hd := hc.comb d hcd
  have hh := publicComb_ct (tcombLay hc hd) hC (hc.comb_am3 d hcd) hc.onG (tcombVals hc hC (hT d hcd).1)
    hc.p_lt checks.comb _ _ _ _ _ _
    ⟨ready₁.1,second.1,ready₁.2.1,second.2.1,ready₁.2.2,second.2.2⟩ ec₁ ec₂
  have wpComb := fun {s₀ a : State} (h : CombReady c d s₀ a) =>
    tcomb_ok (tcombLay hc hd) hC (hc.comb_am3 d hcd) hc.onG (tcombVals hc hC (hT d hcd).1)
      hc.p_lt h.1 h.2.1 h.2.2 true
  obtain ⟨_,_,wc₁,keep₁,_⟩ := wpComb ready₁
  obtain ⟨_,_,wc₂,keep₂,_⟩ := wpComb ready₂
  obtain ⟨_,rfl⟩ := Exec.det ec₁ wc₁
  obtain ⟨_,rfl⟩ := Exec.det ec₂ wc₂
  have ht' := checks.after _ _ _ _ _ _ trivial trivial (Taint.agree_ofRegs fun r hr => by
    rw [List.mem_singleton.mp hr]
    rw [keep₁.gpr _ (by simp only [powClob,List.mem_cons,not_or]; exact ⟨by decide,rdi_not_clob _⟩),keep₂.gpr _ (by simp only [powClob,List.mem_cons,not_or]; exact ⟨by decide,rdi_not_clob _⟩),
      ready₁.1.rdi,ready₂.1.rdi,base]) es₁ es₂
  rw [et₁,et₂,ht,hh.1,ht']

end VG.Proof.Ecdsa.Verify.X86_64
