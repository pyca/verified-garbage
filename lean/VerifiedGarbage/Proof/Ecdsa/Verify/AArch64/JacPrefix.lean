import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Main
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombTiming
import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Jacobian
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPoints

/-! ## `Timing` -/

section

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
    (Impl.Ecdsa.Verify.AArch64.Cfg.tail c)

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
  have hh := publicComb_ct (tcombLay hc.toBaseCfgOk) (combA hc.toBaseCfgOk) hC hc.am3 hc.onG (tcombVals hc.toBaseCfgOk hC hT)
    hc.p_lt checks.comb _ _ _ _ _ _
    ⟨ready₁.1, second.1, sp, ready₁.2.1, second.2.1, ready₁.2.2, second.2.2⟩ ec₁ ec₂
  have wpComb := fun {s₀ a : State} (h : CombReady c s₀ a) =>
    tcomb_ok (publicLookup := true) (tcombLay hc.toBaseCfgOk) (combA hc.toBaseCfgOk) hC hc.am3 hc.onG
      (tcombVals hc.toBaseCfgOk hC hT) hc.p_lt h.1 h.2.1 h.2.2
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

end

/-! ## `JacPublic` -/

section

/-! The Jacobian branches depend on the public signature, digest and public key. -/
namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Mont
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Mont
open VG.Impl.Ecdsa.Verify.AArch64 (U V)

/-- The variable-base multiplication scalar. -/
def publicV (c : Cfg) (s : State) : Nat :=
  (Fin.ofNat c.C.n (sigR c s) * Fin.ofNat c.C.n (sigS c s) ^ (c.C.n-2)).val

theorem mid_publicV {c : Cfg} {s₀ s : State} {base : Addr} {g : Reg → BitVec 64}
    (h : Mid c s₀ base g s) : VG.Proof.Ecdsa.AArch64.sv c base s V = publicV c s₀ := by
  have he := congrArg Fin.val h.v
  simpa only [Fin.val_ofNat,Nat.mod_eq_of_lt h.v_lt,publicV] using he

/-- Equal public-key buffers determine every input of key validation. -/
theorem publicKey_congr {c : Cfg} {s t : State}
    (h : Spec.Ecdsa.bytesAt s.mem (s.gpr .x0) (1+2*c.C.len) =
      Spec.Ecdsa.bytesAt t.mem (t.gpr .x0) (1+2*c.C.len)) :
    s.mem (s.gpr .x0) = t.mem (t.gpr .x0) ∧ keyX c s = keyX c t ∧ keyY c s = keyY c t := by
  rw [bytesAt_add,bytesAt_add] at h
  obtain ⟨htag,hxy⟩ := List.append_inj h (by simp only [length_bytesAt])
  have ht : s.mem (s.gpr .x0) = t.mem (t.gpr .x0) := by
    simpa [Spec.Ecdsa.bytesAt] using htag
  rw [Nat.two_mul,bytesAt_add,bytesAt_add] at hxy
  obtain ⟨hx,hy⟩ := List.append_inj hxy (by simp only [length_bytesAt])
  refine ⟨ht,congrArg Spec.Weierstrass.ofBytes hx,?_⟩
  have hy' := congrArg Spec.Weierstrass.ofBytes hy
  simpa only [keyY,BitVec.ofNat_add,BitVec.add_assoc] using hy'

/-- The stronger internal relation uses only bytes the existing specification makes public. -/
structure JacPublic (c : Cfg) (s t : State) : Prop where
  ptrs : AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1,.x2,.x3]) s t
  table : s.syms c.tsym = t.syms c.tsym
  key : Spec.Ecdsa.bytesAt s.mem (s.gpr .x0) (1+2*c.C.len) =
    Spec.Ecdsa.bytesAt t.mem (t.gpr .x0) (1+2*c.C.len)
  digest : Spec.Ecdsa.bytesAt s.mem (s.gpr .x1) c.C.len =
    Spec.Ecdsa.bytesAt t.mem (t.gpr .x1) c.C.len
  sig : Spec.Ecdsa.bytesAt s.mem (s.gpr .x2) (2*c.C.len) =
    Spec.Ecdsa.bytesAt t.mem (t.gpr .x2) (2*c.C.len)

theorem JacPublic.u {c : Cfg} {s t : State} (h : JacPublic c s t) : publicU c s = publicU c t :=
  publicU_congr h.digest h.sig

theorem JacPublic.signature {c : Cfg} {s t : State} (h : JacPublic c s t) :
    sigR c s = sigR c t ∧ sigS c s = sigS c t := by
  have hs := h.sig
  rw [Nat.two_mul,bytesAt_add,bytesAt_add] at hs
  obtain ⟨hr,hs⟩ := List.append_inj hs (by simp only [length_bytesAt])
  exact ⟨congrArg Spec.Weierstrass.ofBytes hr,congrArg Spec.Weierstrass.ofBytes hs⟩

theorem JacPublic.v {c : Cfg} {s t : State} (h : JacPublic c s t) : publicV c s = publicV c t := by
  rw [publicV,publicV,h.signature.1,h.signature.2]

theorem JacPublic.keyOk {c : Cfg} {s t : State} (h : JacPublic c s t) : KeyOk c s ↔ KeyOk c t := by
  obtain ⟨tag,x,y⟩ := publicKey_congr h.key
  simp only [KeyOk,tag,x,y]

/-- The initialized peer coordinates are equal in the two executions. -/
theorem mid_peer_public {c : Cfg} {s₀ t₀ s t : State} {base : Addr}
    {g₁ g₂ : Reg → BitVec 64} (h : JacPublic c s₀ t₀)
    (hs : Mid c s₀ base g₁ s) (ht : Mid c t₀ base g₂ t) :
    VG.Proof.Weierstrass.AArch64.tmv c.C c.n base s (c.sl VG.Impl.Ecdh.AArch64.PX) =
      VG.Proof.Weierstrass.AArch64.tmv c.C c.n base t (c.sl VG.Impl.Ecdh.AArch64.PX) ∧
    VG.Proof.Weierstrass.AArch64.tmv c.C c.n base s (c.sl VG.Impl.Ecdh.AArch64.PY) =
      VG.Proof.Weierstrass.AArch64.tmv c.C c.n base t (c.sl VG.Impl.Ecdh.AArch64.PY) := by
  obtain ⟨_,x,y⟩ := publicKey_congr h.key
  change toM _ _ _ = toM _ _ _ ∧ toM _ _ _ = toM _ _ _
  rw [hs.px,ht.px,hs.py,ht.py]
  simp only [h.keyOk,x,y]
  exact ⟨True.intro,True.intro⟩

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JacPeer` -/

section

/-! The verifier's initialized peer point is determined by its public key buffer. -/
namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)

theorem Mid.peer_rep {c : Cfg} (hc : CfgOk c) (hC : Law c.C)
    {s₀ a : State} {base : Addr} {g : Reg → BitVec 64} (h : Mid c s₀ base g a) :
    Rep c.C (tmv c.C c.n base a (c.sl PX)) (tmv c.C c.n base a (c.sl PY))
      (tmv c.C c.n base a (c.sl ONEP))
      (peerPt c (s₀.mem (s₀.gpr .x0)=4) (keyX c s₀) (keyY c s₀)) := by
  rw [onep_tmv hc h.fixed]
  exact peerPt_rep hC _ _ _ h.px h.py

theorem JacPublic.peerPoint {c : Cfg} {s t : State} (h : JacPublic c s t) :
    peerPt c (s.mem (s.gpr .x0)=4) (keyX c s) (keyY c s) =
      peerPt c (t.mem (t.gpr .x0)=4) (keyX c t) (keyY c t) := by
  obtain ⟨tag,x,y⟩ := publicKey_congr h.key
  rw [tag,x,y]

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JacPrefix` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (SM' EM' RM' UM VM U V UX UY UZ)
variable {c : Cfg}

/-- Building the public scalar's bits preserves all initialized scalar and peer slots. -/
theorem bits_mid (hc : CfgOk c) {s₀ s : State} {base : Addr} {g : Reg → BitVec 64}
    (hM : Mid c s₀ base g s) :
    WP isa (bits (c.sl U) (bitsAt c.n 0) (8*c.n)) s (Mid c s₀ base g) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hM.scr.nowrap
  refine WP.mono_syms (bits_ok hM.scr h0 (by omega) (sl_le c h7 (i:=U) (by decide))
    (tbl_le h7) (sl_lt4096 h0 h7 (i:=U) (by decide)) (by have := bitsAt0_le c h7; omega)
    (Or.inl (by have := sl_below_bits c (i:=U) (by decide) 0 0; omega)))
    fun t ⟨_,kt,ot⟩ sy => ?_
  have ut : Unch base [(bitsAt c.n 0,64*c.n)] s.mem t.mem := ot.unch
  have eqv : ∀ {i},i<45 → sv c base t i=sv c base s i := fun hi =>
    sv_unch ut h7 hn hi (apart_tbl hi 0 h7)
  refine ⟨hM.scr.of_keepRegs kt (by decide),kt.wr.trans hM.wr,kt.rd.trans hM.rd,
    hM.fixed.unch h7 hn (fixedOk_tbl 0) ut,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,sy.trans hM.syms,?_⟩
  · rw [eqv (by decide)]; exact hM.rx
  · rw [eqv (by decide)]; exact hM.ry
  · rw [eqv (by decide)]; exact hM.rz
  · rw [ut.word (fun w hw => ?_) (by have := sl_le c h7 (i:=FLAG) (by decide); omega)]
    · exact hM.flag
    · rw [List.mem_singleton.mp hw]
      exact Or.inl (by have := sl_below_bits c (i:=FLAG) (by decide) 0 0; omega)
  · rw [eqv (by decide)]; exact hM.px_lt
  · rw [eqv (by decide)]; exact hM.py_lt
  · rw [eqv (by decide)]; exact hM.px
  · rw [eqv (by decide)]; exact hM.py
  · rw [eqv (by decide)]; exact hM.rm_lt
  · rw [eqv (by decide)]; exact hM.rm
  · rw [eqv (by decide)]; exact hM.u_lt
  · rw [eqv (by decide)]; exact hM.u
  · rw [eqv (by decide)]; exact hM.v_lt
  · rw [eqv (by decide)]; exact hM.v
  · apply unch_whole (hM.unch.trans ut)
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · rw [List.mem_singleton.mp hw]; exact Nat.zero_add size |>.le
    · rw [List.mem_singleton.mp hw]; exact tbl_le h7
  · rw [eqv (by decide)]; exact hM.k

/-- The public comb boundary retains the field and scalar data needed by the next loop. -/
def JacReady (c : Cfg) (s₀ s : State) : Prop :=
  CombReady c s₀ s ∧ ∃ g, Mid c s₀ (s₀.gpr .x3) g s

theorem jacPrefix_ok (hc : CfgOk c) {s₀ : State} (hp : VPre c s₀) :
    WP isa (verifyPrefix c) s₀ (JacReady c s₀) := by
  refine front_ok hc hp fun g s₁ _ hF => mid_ok hc hF fun s₂ hM => ?_
  obtain ⟨tr,t,e,r⟩ := bits_combReady hc hM hp.tbl
  obtain ⟨_,_,e',m⟩ := bits_mid hc hM
  obtain ⟨_,rfl⟩ := Exec.det e e'
  exact WP.seq ⟨tr,t,e,WP.block_nil ⟨r,g,m⟩⟩

end VG.Proof.Ecdsa.Verify.AArch64

end
