module

-- separate module: generic over the curve, for every curve whose `a` is not `-3` (brainpoolP384r1's and brainpoolP512r1's signatures next), and not imported by the ECDH, verification and public-key proofs
public import VerifiedGarbage.Impl.Ecdsa.X86_64.CombGeneral
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
public import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
import VerifiedGarbage.Proof.Ecdsa.X86_64.GMul
import VerifiedGarbage.Proof.Ecdsa.X86_64.Lays
import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Ecdsa.X86_64.Inv

/-!
# ECDSA's signature on x86-64 with a comb for any `a`

## The comb

`TCombCfg.generalComb` (`Impl/Weierstrass/X86_64/TCombGeneral.lean`) is
`TCombCfg.comb` but for its additions, so its proof is `tcomb_ok`'s
(`Proof/Weierstrass/X86_64/TComb.lean`) but for theirs: after the entry is
selected and negated (`tentry_ok`), `3 b R mod p` is put in the slot of `-y`
(`TEntryPost.setNeg`: the entry is not changed), and the complete addition
for any `a` (`rcb_ok`, `Law.add`), with `a R mod p` in `S.a` and that slot as
its `b3` (`generalS_apart`), gives `D`, which `A` takes unless the digit is
zero, as there (`generalStep_ok`, `generalComb_ok`).

## The signature

`Cfg.signG d` (`Impl/Ecdsa/X86_64/CombGeneral.lean`) is `Cfg.sign` with
`[k]G` by the comb of `Cfg.combCfgG d`, whose additions are the complete ones
for any `a`, from the tables of `d`, which the configuration declares as its
`gtab`. Its proof is `sign_ok`'s (`Proof/Ecdsa/X86_64/Main.lean`), with the
comb's: the comb's slots are numbered slots, apart as `generalComb_ok` needs
(`tcombLayG`, as `tcombLay` but with `a R mod p`, `AP`, read), its constants
are `tcombVals`'s, and after `b R mod p` is put in `EM` (`gMulG_ok'`, as
`gMulComb_ok'`) the comb computes `[k]G` (`generalComb_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

/-- The complete addition of `generalStep` writes apart from what it reads:
`neg`, its `b3`, is one of the comb's slots that the addition does not write. -/
theorem generalS_apart {K : TCombCfg} {size : Nat} (hL : TCombLay K size) :
    RcbApart K.generalS K.A K.E K.D := by
  have h := hL.comb.add
  have hnd := hL.comb.nodup
  dsimp only [TCombCfg.toComb, combWs] at hnd h
  refine ⟨h.nodup, fun x hx => ?_⟩
  simp only [rcbR, TCombCfg.generalS, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.apart _ (by simp [rcbR])
  · show K.neg ∉ rcbW K.S K.D
    exact fun hm => (List.nodup_append.mp hnd).2.2 _ (by simp) _ hm rfl
  all_goals exact h.apart _ (by simp [rcbR])

/-- The entry survives `3 b R mod p` stored to `-y`'s slot, which only `rax`
and that slot's bytes change. -/
theorem TEntryPost.setNeg {K : TCombCfg} {C : Curve} {base : Addr} {size k i : Nat} {s s₂ s₃ : State}
    (hL : TCombLay K size) (E : TEntryPost K C base size k i s s₂) (k₃ : KeepRegs [.rax] s₂ s₃)
    (O₃ : Outside base K.neg (8 * K.M.n) s₂.mem s₃.mem) : TEntryPost K C base size k i s s₃ := by
  have hn := E.scr.nowrap
  have hnd := hL.comb.nodup
  dsimp only [TCombCfg.toComb] at hnd
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  have hle : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ size := fun x hx => hL.comb.lay.le x hx
  have hw : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s₃.mem base x K.M.n = wordsVal s₂.mem base x K.M.n := by
    intro x hx
    have hxs : x ∈ combWs K.toComb := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> tcomb_mem
    have hne : x ≠ K.neg := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> nd_ne hnd
    refine O₃.unch.wordsVal (fun w hw => ?_) (by have := hle x (combWs_slots _ x hxs); omega_using [hn, this])
    simp only [List.mem_singleton] at hw; subst hw
    exact hL.comb.apart₂ hxs (by tcomb_mem) hne
  have ht : ∀ x ∈ [K.E.x, K.E.y, K.E.z], tmv C K.M.n base s₃ x = tmv C K.M.n base s₂ x :=
    fun x hx => by show toM _ _ _ = toM _ _ _; rw [hw x hx]
  refine ⟨E.scr.of_keepRegs k₃ (by decide), E.keep.trans (k₃.mono fun r hr => ?_),
    (E.unch.trans O₃.unch).mono fun w hw => ?_, fun x hx => by rw [hw x hx]; exact E.lt x hx, ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; simp [clob, acc]
  · rcases List.mem_append.mp hw with h | h
    · exact h
    · simp only [List.mem_singleton] at h; subst h; simp
  · rw [ht _ (by simp), ht _ (by simp), ht _ (by simp)]; exact E.rep
  · rw [ht _ (by simp)]; exact E.z

theorem generalStep_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hC : Law C)
    (b3 : Nat) (hb : b3 < C.p) (hbm : toM C.p (2 ^ (64 * K.M.n)) b3 = Fin.ofNat C.p (3 * C.b))
    (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl)
    (hpn : C.p < 2 ^ (64 * K.M.n)) {s₀ : State}
    (hF : TCombFixed K C base size s₀ k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j ≤ K.J)
    (hI : TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s j)
    (haS : tmv C K.M.n base s₀ K.S.a = Fin.ofNat C.p C.a) (publicLookup : Bool := false) :
    WP isa (K.generalStep b3 publicLookup).inline s fun s' =>
      TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s' (j - 1) ∧
        s'.zf = some (decide (j - 1 = 0)) := by
  have hn := hI.scr.nowrap
  have hsz : size ≤ 2 ^ 64 := by omega_using [hn]
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  have hle : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ size := fun x hx => hL.comb.lay.le x hx
  have hnd := hL.comb.nodup
  dsimp only [TCombCfg.toComb] at hnd
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  refine WP.of_syms ?_
  unfold TCombCfg.generalStep
  simp only [Code.inline]
  refine WP.seq ?_
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono_syms (decRbx_ok s hj (by omega_using [hjn, hJ]) hI.rbx) fun s₁ ⟨b₁, k₁⟩ sy₁ => ?_
  have hs₁ := hI.scr.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  have hM₁ : ModOkW K.M size C.p s₁.mem base := by rw [hm₁]; exact hI.mod
  have hbits₁ : ∀ t < K.w * K.J, s₁.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by rw [hm₁]; exact hI.bits t ht
  have hz : wordsVal s₁.mem base K.zero K.M.n = 0 := by
    rw [hm₁, hI.unch.wordsVal (tcombW_ro hL (x := K.zero) (by simp [combRo, TCombCfg.toComb]))
      (by have := hle K.zero (by tcomb_mem); omega_using [hn, this]), hF.zero]
  have hT : s₁.syms K.tsym = T := by rw [sy₁]; exact hI.tsym
  have hTM : TblMem s₁ T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) :=
    hI.tbl.unch (by rw [k₁.2.2.1, k₁.2.2.2]) fun _ _ _ _ => by rw [hm₁]
  refine WP.mono (tentry_ok hL hC hV hpn hs₁ hM₁ (i := j - 1) (by omega_using [hjn, hJ]) b₁ hbits₁ hz hT hTM publicLookup)
    fun s₂ h₂ => WP.seq (WP.mono h₂ fun s₃' E₃' => WP.seq (WP.mono (setConst_ok E₃'.scr (n := K.M.n)
      (o := K.neg) (x := b3) (hle K.neg (by tcomb_mem)) (Nat.lt_trans hb hpn)) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_))
  have E₃ := E₃'.setNeg hL k₃ O₃
  have hEW : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n), (K.neg, 8 * K.M.n),
      (K.M.tmp, 8 * K.M.n)], w ∈ combW K.toComb := combEntryW_sub (K := K.toComb)
  have U₁₃ : Unch base (combW K.toComb) s.mem s₃.mem := by
    rw [← hm₁]; exact E₃.unch.mono hEW
  have hmoW := tcombW_mo hL hI.mod
  have hM₃ : ModOkW K.M size C.p s₃.mem base :=
    hI.mod.unch U₁₃ (fun w hw => hmoW w (List.mem_append_left _ hw)) hn
  -- What `A` and the read-only slots hold at `s₃`.
  have hAx : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s₃.mem base x K.M.n = wordsVal s.mem base x K.M.n :=
    fun x hx => by rw [← hm₁]; exact hL.comb.wordsVal_entry hsz E₃.unch x hx
  have U₃ : Unch base (tcombW K) s₀.mem s₃.mem :=
    (hI.unch.trans U₁₃).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact List.mem_append_left _ hw
  have hro : ∀ x ∈ combRo K.toComb, wordsVal s₃.mem base x K.M.n = wordsVal s₀.mem base x K.M.n :=
    fun x hx => U₃.wordsVal (tcombW_ro hL hx) (by have := hle x (combRo_slots x hx); omega_using [hn, this])
  have hSl : ∀ x ∈ rcbR K.generalS K.A K.E, x ∈ combSlots K.toComb := by
    intro x hx
    simp only [rcbR, TCombCfg.generalS, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> tcomb_mem
  have hlt₃ : ∀ x ∈ rcbR K.generalS K.A K.E, wordsVal s₃.mem base x K.M.n < C.p := by
    intro x hx
    simp only [rcbR, TCombCfg.generalS, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hro _ (by simp [combRo, TCombCfg.toComb])]; exact hF.ro_lt _ (by simp [combRo, TCombCfg.toComb])
    · rw [e₃]; exact hb
    · rw [hAx _ (by simp)]; exact hI.lt _ (by simp)
    · rw [hAx _ (by simp)]; exact hI.lt _ (by simp)
    · rw [hAx _ (by simp)]; exact hI.lt _ (by simp)
    · exact E₃.lt _ (by simp)
    · exact E₃.lt _ (by simp)
    · exact E₃.lt _ (by simp)
  have I₃ : Inv K.M base size C.p (· ∈ combSlots K.toComb) (rcbR K.generalS K.A K.E) (tmv C K.M.n base s₃) s₃ :=
    ⟨E₃.scr, hM₃, hSl, hlt₃, fun _ _ => rfl⟩
  have hSl' : ∀ x ∈ rcbW K.generalS K.D ++ rcbR K.generalS K.A K.E, x ∈ combSlots K.toComb := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · simp only [combSlots, List.mem_append, TCombCfg.toComb]; exact Or.inr hx
    · exact hSl x hx
  refine WP.seq ((WP.mono (rcb_ok hL.comb.lay hV.unit (generalS_apart hL) hSl' I₃
    (fun _ h => h)) fun s₄ ⟨P₄, I₄, t₄, _⟩ => ?_))
  dsimp only [TCombCfg.toComb] at P₄ I₄ t₄
  -- The sum.
  have ta : tmv C K.M.n base s₃ K.S.a = Fin.ofNat C.p C.a := by
    show toM _ _ _ = _; rw [hro _ (by simp [combRo, TCombCfg.toComb])]; exact haS
  have tb : tmv C K.M.n base s₃ K.neg = Fin.ofNat C.p (3 * C.b) := by
    show toM _ _ _ = _; rw [e₃]; exact hbm
  have hRA : Rep C (tmv C K.M.n base s₃ K.A.x) (tmv C K.M.n base s₃ K.A.y)
      (tmv C K.M.n base s₃ K.A.z) (mul (combEW K.w k K.J j) (G C)) := by
    have ex : tmv C K.M.n base s₃ K.A.x = tmv C K.M.n base s K.A.x := by
      show toM _ _ _ = toM _ _ _; rw [hAx _ (by simp)]
    have ey : tmv C K.M.n base s₃ K.A.y = tmv C K.M.n base s K.A.y := by
      show toM _ _ _ = toM _ _ _; rw [hAx _ (by simp)]
    have ez : tmv C K.M.n base s₃ K.A.z = tmv C K.M.n base s K.A.z := by
      show toM _ _ _ = toM _ _ _; rw [hAx _ (by simp)]
    rw [ex, ey, ez]; exact hI.rep
  rw [show K.generalS.a = K.S.a from rfl, show K.generalS.b3 = K.neg from rfl] at t₄
  rw [ta, tb] at t₄
  have hP := hC.onCurve_mul hG (combEW K.w k K.J j)
  have hQ : onCurve C (signedPtW C K.w k (j - 1)) = true := by
    unfold signedPtW combPtW
    split
    · exact hC.onCurve_mul hG _
    · exact onCurve_negPt (hC.onCurve_mul hG _)
  have hadd := combW_add hC hG (w := K.w) (k := k) (J := K.J) (j := j - 1) (by omega_using [hjn, hJ])
  rw [Nat.sub_add_cancel hj] at hadd
  have hsp : signedPtW C K.w k (j - 1) = (if 2 ^ (K.w - 1) ≤ combWin K.w k (j - 1) then
      combPtW C K.w (j - 1) (combWin K.w k (j - 1) - 2 ^ (K.w - 1))
      else negPt (combPtW C K.w (j - 1) (2 ^ (K.w - 1) - combWin K.w k (j - 1)))) := rfl
  have hEz := E₃.z
  have hErep := E₃.rep
  generalize ha : magH K.H (combWin K.w k (j - 1)) = a at hEz
  -- For a nonzero digit, the entry is affine, and `D` is the sum.
  have hRD : 1 ≤ a → Rep C (runOps (rcb K.generalS K.A K.E K.D) (tmv C K.M.n base s₃) K.D.x)
      (runOps (rcb K.generalS K.A K.E K.D) (tmv C K.M.n base s₃) K.D.y)
      (runOps (rcb K.generalS K.A K.E K.D) (tmv C K.M.n base s₃) K.D.z)
      (mul (combEW K.w k K.J (j - 1)) (G C)) := fun h1 => by
    rw [hEz] at hErep
    simp only [h1, ↓reduceIte] at hErep
    have t₄' := t₄
    rw [hEz] at t₄'
    simp only [h1, ↓reduceIte] at t₄'
    have hR := hC.add hP hQ hRA hErep t₄'.symm
    rw [hsp, hadd] at hR
    exact hR
  -- For a zero digit, the entry is the point at infinity, and the sum is `A`.
  have hRA0 : a = 0 → Rep C (tmv C K.M.n base s₃ K.A.x) (tmv C K.M.n base s₃ K.A.y)
      (tmv C K.M.n base s₃ K.A.z) (mul (combEW K.w k K.J (j - 1)) (G C)) := fun h0 => by
    have hw : combWin K.w k (j - 1) = 2 ^ (K.w - 1) := by
      have e : K.H = 2 ^ (K.w - 1) := rfl
      unfold magH at ha; rw [e] at ha; split at ha <;> omega
    rw [← hadd, hw]
    simp only [Nat.le_refl, ↓reduceIte, Nat.sub_self]
    rw [show combPtW C K.w (j - 1) 0 = .infinity by simp [combPtW, Spec.Weierstrass.mul], add_infinity]
    exact hRA
  -- The digit again, and `A = D` unless it is zero.
  have hs₄ := I₄.scr
  have hb₄ : s₄.gpr .rbx = BitVec.ofNat 64 (j - 1) := by
    rw [P₄.gpr _ (rbx_not_clob _), E₃.keep.gpr _ (rbx_not_clob _), b₁]
  have U₄ : Unch base (combW K.toComb) s₃.mem s₄.mem := P₄.unch.mono fun w hw => by
    simp only [combW, List.mem_append, List.mem_map, List.mem_singleton] at hw ⊢
    rcases hw with ⟨y, hy, rfl⟩ | h
    · exact Or.inl ⟨y, by simp only [combWs, List.mem_append, TCombCfg.toComb]; exact Or.inr hy, rfl⟩
    · exact Or.inr (by rw [h]; rfl)
  have hbl := hL.bits
  have hz' : K.w * K.J ≤ K.kbytes + 8 * K.zw := by unfold TCombCfg.zw; have := hL.kbytes; omega_using []
  have hbits₄ : ∀ t < K.w * K.J, s₄.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 := by
    intro t ht
    rw [(U₁₃.trans U₄).byte (fun w hw => by
      rcases List.mem_append.mp hw with h | h <;> exact combW_bits hL ht w h)
      (by omega_using [hbl, hz', ht, hn])]
    exact hI.bits t ht
  have hAE₄ : ∀ x ∈ [K.A.x, K.A.y, K.A.z, K.E.x, K.E.y, K.E.z],
      wordsVal s₄.mem base x K.M.n = wordsVal s₃.mem base x K.M.n := hL.comb.wordsVal_add hsz P₄.unch
  have hA₄ : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s₄.mem base x K.M.n = wordsVal s₃.mem base x K.M.n :=
    fun x hx => hAE₄ x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with h | h | h <;> simp [h])
  have hw := hL.w
  have hwi : K.w * (j - 1) + K.w ≤ K.w * K.J := by
    have := Nat.mul_le_mul_left K.w (show j - 1 + 1 ≤ K.J by omega_using [hjn, hJ]); rwa [Nat.mul_succ] at this
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (digit_ok K hs₄ (k := k) (j := j - 1) (N := K.w * K.J) hw.1 hw.2 hwi
    (by omega_using [hbl, hz', hn]) hb₄ hbits₄) fun s₅ ⟨_, r₅, k₅⟩ => ?_
  have hs₅ := hs₄.of_keeps k₅ (by decide)
  rw [ha] at r₅
  have hH2 : 2 ^ K.w = 2 * K.H := by
    unfold TCombCfg.H; rw [← Nat.pow_succ']; congr 1; omega_using [hw]
  have hHle : K.H ≤ 128 := by
    unfold TCombCfg.H; exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (show K.w - 1 ≤ 7 by omega_using [hw]))
      (by decide)
  have hmag : a ≤ K.H := by
    rw [← ha]; exact magH_le (by rw [← hH2]; exact combWin_lt K.w k (j - 1))
  rw [WP.block_append_iff]
  refine WP.mono (eqMask_ok s₅ (v := 0) (a := a) (by decide) (by omega_using [hHle, hmag]) r₅) fun s₆ ⟨c₆, k₆, _⟩ => ?_
  have hs₆ := hs₅.of_keeps k₆ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (selPtKeep_ok hs₆ (decide (a = 0)) (by rw [c₆]) (n := K.M.n) (o := K.A) (a := K.D)
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hle _ (by tcomb_mem))
    hL.comb.apart_A hL.comb.apart_AD) fun s₇ ⟨ex₇, ey₇, ez₇, k₇, O₇⟩ => ?_
  have hs₇ := hs₆.of_keepRegs k₇ (by decide)
  have hb₇ : s₇.gpr .rbx = BitVec.ofNat 64 (j - 1) := by
    rw [k₇.gpr _ (by decide), k₆.1 _ (by decide), k₅.1 _ (by decide), hb₄]
  refine WP.mono (testRbx_ok s₇ (by omega_using [hjn, hJ]) hb₇) fun s₈ ⟨z₈, k₈⟩ sy₈ => ?_
  have m₈ : s₈.mem = s₇.mem := k₈.2.1
  have m₆ : s₆.mem = s₄.mem := by rw [k₆.2.1, k₅.2.1]
  have U₈ : Unch base (combW K.toComb) s₄.mem s₈.mem := by
    rw [m₈, ← m₆]
    refine Unch.mono (W := [(K.A.x, 8 * K.M.n), (K.A.y, 8 * K.M.n), (K.A.z, 8 * K.M.n)])
      (fun x hx => O₇ x (hx (K.A.x, 8 * K.M.n) (by simp)) (hx (K.A.y, 8 * K.M.n) (by simp))
        (hx (K.A.z, 8 * K.M.n) (by simp))) (combSelW_A_sub (K := K.toComb))
  have U : Unch base (combW K.toComb) s.mem s₈.mem := (U₁₃.trans (U₄.trans U₈)).mono fun w hw => by
    simp only [List.mem_append] at hw; rcases hw with h | h | h <;> exact h
  have hDv : ∀ x ∈ [K.D.x, K.D.y, K.D.z], x ∈ rcbW K.generalS K.D ++ rcbR K.generalS K.A K.E :=
    fun _ hx => List.mem_append_left _ (by
      simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h | h <;> simp [h])
  have hDval : ∀ x ∈ [K.D.x, K.D.y, K.D.z], toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₄.mem base x K.M.n) =
      runOps (rcb K.generalS K.A K.E K.D) (tmv C K.M.n base s₃) x := fun x hx => I₄.val x (hDv x hx)
  have hDlt : ∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal s₄.mem base x K.M.n < C.p := fun x hx => I₄.lt x (hDv x hx)
  rw [m₆] at ex₇ ey₇ ez₇
  refine ⟨⟨hs₇.of_keeps k₈ (by decide), by rw [k₈.1 _ (by decide), hb₇], ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [sy₈]; exact hI.tsym⟩, z₈⟩
  · have c₁ : KeepRegs (powClob K.M.n) s s₁ := (Keeps.regs k₁).mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..
    have c₃ : KeepRegs (powClob K.M.n) s₁ s₃ := E₃.keep.mono clob_powClob
    have c₄ : KeepRegs (powClob K.M.n) s₃ s₄ :=
      (⟨P₄.gpr, P₄.rd, P₄.wr⟩ : KeepRegs (clob K.M.n) s₃ s₄).mono clob_powClob
    have hcl : ∀ r ∈ [Reg.rax, .rcx, .rdx, .r8], r ∈ powClob K.M.n := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact clob_powClob _ (by simp [clob])
      · exact clob_powClob _ (by simp [clob])
      · exact clob_powClob _ (by simp [clob])
      · exact clob_powClob _ (r8_mem_clob _)
    have c₅ : KeepRegs (powClob K.M.n) s₄ s₅ := (Keeps.regs k₅).mono hcl
    have c₆ : KeepRegs (powClob K.M.n) s₅ s₆ := (Keeps.regs k₆).mono fun r hr => hcl r (by
      simp only [List.mem_singleton] at hr; subst hr; simp)
    have c₇ : KeepRegs (powClob K.M.n) s₆ s₇ := k₇.mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h])
    have c₈ : KeepRegs (powClob K.M.n) s₇ s₈ := (Keeps.regs k₈).mono fun r hr => absurd hr List.not_mem_nil
    exact hI.keep.trans (c₁.trans (c₃.trans (c₄.trans (c₅.trans (c₆.trans (c₇.trans c₈))))))
  · exact (hI.unch.trans U).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact List.mem_append_left _ hw
  · exact hI.mod.unch U (fun w hw => hmoW w (List.mem_append_left _ hw)) hn
  · have hA : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s₄.mem base x K.M.n < C.p := fun x hx => by
      rw [hA₄ x hx, hAx x hx]; exact hI.lt x hx
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [m₈, ex₇]; split
      · exact hA _ (by simp)
      · exact hDlt _ (by simp)
    · rw [m₈, ey₇]; split
      · exact hA _ (by simp)
      · exact hDlt _ (by simp)
    · rw [m₈, ez₇]; split
      · exact hA _ (by simp)
      · exact hDlt _ (by simp)
  · have e : ∀ {x y : Nat}, wordsVal s₈.mem base x K.M.n = wordsVal s₄.mem base y K.M.n →
        tmv C K.M.n base s₈ x = tmv C K.M.n base s₄ y := fun h => by show toM _ _ _ = toM _ _ _; rw [h]
    by_cases h0 : a = 0
    · simp only [decide_eq_true h0, ↓reduceIte] at ex₇ ey₇ ez₇
      rw [e (by rw [m₈, ex₇]), e (by rw [m₈, ey₇]), e (by rw [m₈, ez₇])]
      have e₃ : ∀ x ∈ [K.A.x, K.A.y, K.A.z], tmv C K.M.n base s₄ x = tmv C K.M.n base s₃ x :=
        fun x hx => by show toM _ _ _ = toM _ _ _; rw [hA₄ x hx]
      rw [e₃ _ (by simp), e₃ _ (by simp), e₃ _ (by simp)]
      exact hRA0 h0
    · simp only [decide_eq_false h0, Bool.false_eq_true, ↓reduceIte] at ex₇ ey₇ ez₇
      rw [e (by rw [m₈, ex₇]), e (by rw [m₈, ey₇]), e (by rw [m₈, ez₇])]
      show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
      rw [hDval _ (by simp), hDval _ (by simp), hDval _ (by simp)]
      exact hRD (by omega_using [h0])
  · intro t ht
    rw [U.byte (combW_bits hL ht) (by omega_using [hbl, hz', ht, hn])]
    exact hI.bits t ht
  · exact TblMem.of_unch hI.tbl (by rw [k₈.2.2.1, k₈.2.2.2, k₇.rd, k₇.wr, k₆.2.2.1, k₆.2.2.2, k₅.2.2.1,
      k₅.2.2.2, P₄.rd, P₄.wr, E₃.keep.rd, E₃.keep.wr, k₁.2.2.1, k₁.2.2.2]) U
      (fun w hw => tcombW_size hL hI.mod w (List.mem_append_left _ hw)) hF.out


/-- `[k]G` into `A` by `generalComb b3`, for `k < 2^kbytes` whose bits are
the table at `K.bits`, with `a R mod p` in `S.a` and `b3 = 3 b R mod p`; only
`powClob` and `tcombW` change. -/
theorem generalComb_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hC : Law C)
    (b3 : Nat) (hb : b3 < C.p) (hbm : toM C.p (2 ^ (64 * K.M.n)) b3 = Fin.ofNat C.p (3 * C.b))
    (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl)
    (hpn : C.p < 2 ^ (64 * K.M.n)) {s : State} (hs : Scr s base size)
    (hM : ModOkW K.M size C.p s.mem base)
    (hF : TCombFixed K C base size s k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    (haS : tmv C K.M.n base s K.S.a = Fin.ofNat C.p C.a) (publicLookup : Bool := false) :
    WP isa (K.generalComb b3 publicLookup).inline s fun s' => KeepRegs (powClob K.M.n) s s' ∧
      Unch base (tcombW K) s.mem s'.mem ∧ ModOkW K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.A.x) (tmv C K.M.n base s' K.A.y) (tmv C K.M.n base s' K.A.z)
        (mul k (G C)) := by
  have hk : k < 2 ^ (K.w * K.J) :=
    Nat.lt_of_lt_of_le hF.k_lt (Nat.pow_le_pow_right (by decide) hL.kbytes)
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  unfold TCombCfg.generalComb
  refine WP.seq (WP.mono (tcomb_init_ok hL hV hpn hs hM hF) fun s₆ I₆ => ?_)
  exact countLoop_ok (Inv := fun j s' =>
      TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s s' j) (n := K.J)
    (fun j s' h1 h2 hi => generalStep_ok hL hC b3 hb hbm hG hV hpn hF h1 h2 hi haS publicLookup)
    (fun s' hi => ⟨hi.keep, hi.unch, hi.mod, hi.lt, by rw [← combEW_zero hk]; exact hi.rep⟩)
    hJ.1 I₆

end VG.Proof.Weierstrass.X86_64

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

theorem combSlotsG_eq (c : Cfg) (d : CombData) : combSlots (c.combCfgG d).toComb = [AP, EM, ZERO, RX, RY,
    RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ].map c.sl := rfl

theorem combLayG {d : CombData} (hc : BaseCfgOk c) (hd : CombOk c d) :
    CombLay (c.combCfgG d).toComb size := by
  have hn := hc.n0
  have h7 := hc.n10
  have hJ : (c.combCfgG d).toComb.J = c.combJ d.w := by rw [TCombCfg.toComb_J]; rfl
  have hJb := combJ_bounds hc hd
  refine ⟨?_, rcbApart_of hn (lw := [T0, T1, T2, T3, T4, T5, DX, DY, DZ])
      (lr := [AP, EM, RX, RY, RZ, TX, TY, TZ]) rfl rfl (by decide) (by decide), ?_,
    map_sl_nodup hn (l := [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ])
      (by decide), ⟨by rw [hJ]; omega, by rw [hJ]; omega⟩, ?_, ?_, ?_⟩
  · exact lay_map hc rfl rfl rfl (l := [AP, EM, ZERO, RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3,
      T4, T5, DX, DY, DZ]) (by decide)
  · exact map_sl_disj hn (l₁ := [AP, EM, ZERO])
      (l₂ := [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ]) (by decide)
  · rw [hJ]; show bitsAt c.n 0 + 4 * c.combJ d.w ≤ 8192; rw [bitsAt_eq]; omega
  · show bitsAt c.n 0 + 3 < 4096; rw [bitsAt_eq]; omega
  · intro w hw
    rw [show combW (c.combCfgG d).toComb = combW (c.combCfg d).toComb from rfl, combW_eq] at hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    have hl : ∀ i ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP], i < 45 := by
      decide
    by_cases hT : i = TMP
    · subst hT; rw [hJ]; exact tmp_apart_comb hd
    · exact Or.inr (sl_below_bits c (hl i hi) 0 0 (.inl hT))

theorem tcombLayG {d : CombData} (hc : BaseCfgOk c) (hd : CombOk c d) : TCombLay (c.combCfgG d) size := by
  have hL := tcombLay hc hd
  refine ⟨combLayG hc hd, hL.w, hL.kbytes, hL.bits, hL.bits8, hL.bits_w, ?_, hL.n, hL.exy, hL.tbl⟩
  have hn := hc.n0
  have h7 := hc.n10
  have hb := bitsAt_le_pad c h7 (j := 0) (by decide)
  have hz := zw_le hd
  have hk : (c.combCfgG d).kbytes = 64 * c.n := rfl
  have hbits : (c.combCfgG d).bits = bitsAt c.n 0 := rfl
  intro x hx
  rw [hbits, hk]
  simp only [List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact Or.inr (sl_below_bits c (i := MP) (by decide) 0 _)
  · rw [combSlotsG_eq] at hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have : ∀ i ∈ [AP, EM, ZERO, RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ],
      i < 45 := by decide
    exact Or.inr (sl_below_bits c (this i hi) 0 _ (.inl fun h => by subst h; exact absurd hi (by decide)))

/-- The comb's constants: `tcombVals`'s, which do not depend on the addition's slots. -/
theorem tcombValsG {d : CombData} (hc : BaseCfgOk c) (hC : Law c.C)
    (hd : CombOkW c.C d.w (c.combJ d.w) d.tbl d.start) : TCombVals (c.combCfgG d) c.C d.tbl :=
  have V := tcombVals hc hC hd
  ⟨V.len, V.lenH, V.unit, V.one_lt, V.one, V.entry, V.start_lt, V.start⟩

/-- The comb's tables, from the arguments' facts, for the configuration's
`gtab`. -/
theorem tbl_of_gtab {d : CombData} (hcd : c.gtab = some d) {s₀ s : State} (hp : Pre c s₀)
    (hrd : s.rd = s₀.rd) (hu : Unch (s₀.gpr .r8) [(0, size)] s₀.mem s.mem) :
    TblMem s (s₀.syms d.tsym) (c.combWords d) ∧ ∀ i < (c.combWords d).length, ∀ b < 8,
      size ≤ ofs (s₀.gpr .r8) (s₀.syms d.tsym + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b) :=
  tbl_of_held_mem (gtab_mem_consts hcd) hp.tbls (by rw [hp.wr]; simp)
    (fun r hr => by rw [hrd, hp.rd]; simp [hr]) hu

/-- `R = [k]G` by the comb of `combCfgG d` (`gMulG d`), from the table of `k`'s
bits, with its tables where it reads them: `gMul_ok'`'s postcondition. -/
theorem gMulG_ok' (hc : BaseCfgOk c) (hC : Law c.C) {d : CombData} (hd : CombOk c d)
    (hW : CombOkW c.C d.w (c.combJ d.w) d.tbl d.start) {base : Addr} {g : Reg → BitVec 64}
    {s : State} (hs : Scr s base size) (F : Fixed c base g s.mem) {k : Nat} (hkl : k < 2 ^ (64 * c.n))
    (ht₀ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0)
    (hTM : TblMem s (s.syms d.tsym) (c.combWords d))
    (hout : ∀ i < (c.combWords d).length, ∀ b < 8,
      size ≤ ofs base (s.syms d.tsym + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)) :
    WP isa (c.gMulG d).inline s fun s' => KeepRegs (powClob c.n) s s' ∧ Unch base (gW c) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem base ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
        (tmv c.C c.n base s' (c.sl RZ)) (mul k (G c.C)) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  have hn := hs.nowrap
  unfold Cfg.gMulG
  -- `b R mod p` in `EM`.
  refine WP.seq (WP.mono_syms (setConst_ok hs (n := c.n) (o := c.sl EM) (x := c.mont c.C.b)
    (sl_le c h7 (by decide)) (by have := hc.p_lt; have := hmont c.C.b; omega))
    fun s₁ ⟨e₁, k₁, O₁⟩ sy₁ => ?_)
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have hmp₁ : wordsVal s₁.mem base (c.sl MP) c.n = c.C.p :=
    (sv_unch O₁.unch h7 hn (i := MP) (by decide) (apart_slW (l := [EM]) (by decide))).trans F.mp
  have hz₁ : wordsVal s₁.mem base (c.sl ZERO) c.n = 0 :=
    (sv_unch O₁.unch h7 hn (i := ZERO) (by decide) (apart_slW (l := [EM]) (by decide))).trans F.zero
  have hap₁ : wordsVal s₁.mem base (c.sl AP) c.n = c.mont c.C.a :=
    (sv_unch O₁.unch h7 hn (i := AP) (by decide) (apart_slW (l := [EM]) (by decide))).trans F.ap
  have ht₁ : ∀ t < 64 * c.n, s₁.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by
      rw [tbl_unch (W := slW c [EM]) O₁.unch h7 hn (j := 0) (by decide) ht (tbl_apart_slW (by decide) 0 t ht)]
      exact ht₀ t ht
  have hTM₁ : TblMem s₁ (s.syms d.tsym) (c.combWords d) :=
    hTM.of_unch (by rw [k₁.rd, k₁.wr]) O₁.unch (fun w hw => by
      rw [List.mem_singleton.mp hw]; exact sl_le c h7 (by decide)) hout
  have hF : TCombFixed (c.combCfgG d) c.C base size s₁ k (s₁.syms d.tsym)
      (tcombWords (c.combCfgG d).M.n (2 ^ (64 * (c.combCfgG d).M.n)) c.C.p d.tbl) := by
    refine ⟨?_, fun x hx => ?_, hz₁, ht₁, hkl, rfl, by rw [sy₁]; exact hTM₁,
      by rw [sy₁]; exact hout⟩
    · show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₁.mem _ (c.sl EM) c.n) = _
      rw [e₁]; exact toM_cmont hc _
    · simp only [combRo, TCombCfg.toComb, Cfg.combCfgG, Cfg.combCfg, Cfg.rcbSlots, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact lt_of_eq_of_lt hap₁ (hmont _)
      · exact lt_of_eq_of_lt e₁ (hmont _)
      · exact lt_of_eq_of_lt hz₁ (by omega)
  have haS : tmv c.C (c.combCfgG d).M.n base s₁ (c.combCfgG d).S.a = Fin.ofNat c.C.p c.C.a := by
    show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₁.mem _ (c.sl AP) c.n) = _
    rw [hap₁]; exact toM_cmont hc _
  refine WP.mono (generalComb_ok (tcombLayG hc hd) hC (c.mont (3 * c.C.b)) (hmont _) (toM_cmont hc _)
      hc.onG (tcombValsG hc hC hW) hc.p_lt hs₁ ((modP_of hc hmp₁).inl c.hot) hF haS)
    fun s' ⟨K', U', M', L', R'⟩ =>
      ⟨(k₁.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp [powClob, clob]).trans K', ?_, M'.of_inl, L', R'⟩
  rw [show tcombW (c.combCfgG d) = tcombW (c.combCfg d) from rfl, tcombW_eq] at U'
  have hz := zw_le hd
  refine Unch.cover (O₁.unch.trans U') fun w hw => ?_
  rcases List.mem_append.mp hw with hw | hw
  · rw [List.mem_singleton.mp hw]
    exact ⟨_, List.mem_append_left _ (List.mem_map_of_mem (f := fun i => (c.sl i, 8 * c.n))
      (show EM ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM] by decide)),
      Nat.le_refl _, Nat.le_refl _⟩
  rcases List.mem_append.mp hw with hw | hw
  · have sub : ∀ i ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP],
        i ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM] := by decide
    exact ⟨w, List.mem_append_left _ (List.map_subset _ sub hw), Nat.le_refl _, Nat.le_refl _⟩
  · rw [List.mem_singleton.mp hw]
    exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by dsimp only; omega, by dsimp only; omega⟩

/-- `R = [k]G` by `gMulG d`, after the setup and the tables. -/
theorem gMulG_ok (hc : BaseCfgOk c) (hC : Law c.C) {d : CombData} (hd : CombOk c d)
    (hW : CombOkW c.C d.w (c.combJ d.w) d.tbl d.start) (hcd : c.gtab = some d) {hs : Option Nat}
    {s₀ : State} (hp : Pre c s₀) {s : State} (hS : St₁ c hs s₀ (s₀.gpr .r8) s false) :
    WP isa (c.gMulG d).inline s fun s' => KeepRegs (powClob c.n) s s' ∧ Unch (s₀.gpr .r8) (gWA c) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem (s₀.gpr .r8) ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem (s₀.gpr .r8) x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n (s₀.gpr .r8) s' (c.sl RX)) (tmv c.C c.n (s₀.gpr .r8) s' (c.sl RY))
        (tmv c.C c.n (s₀.gpr .r8) s' (c.sl RZ)) (mul (kv c s₀) (G c.C)) := by
  obtain ⟨hTM, hout⟩ := tbl_of_gtab hcd hp hS.rd hS.unch
  rw [← hS.syms] at hTM hout
  exact WP.mono (gMulG_ok' hc hC hd hW hS.scr hS.fixed (hS.k ▸ wordsVal_lt _ _ _ _) (hS.t₀ rfl) hTM hout)
    fun s' ⟨K', U', M', L', R'⟩ => ⟨K', U'.mono fun w hw => List.mem_append_left _ hw, M', L', R'⟩

/-- `[k]G` by the comb of `combCfgG d`, then `Z^(p-2)`: `stage₂`. -/
theorem stage₂G (hc : BaseCfgOk c) (hC : Law c.C) {d : CombData} (hd : CombOk c d)
    (hW : CombOkW c.C d.w (c.combJ d.w) d.tbl d.start) (hcd : c.gtab = some d) {hs : Option Nat} {s₀ : State} (hp : Pre c s₀) {base : Addr}
    (hb : base = s₀.gpr .r8) {s : State} (hS : St₁ c hs s₀ base s false)
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', St₂ c hs s₀ base s' → WP isa rest s' Q) :
    WP isa (.seq (c.gMulG d).inline (.seq c.pPow.inline rest)) s Q := by
  subst hb
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hS.scr.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have F := hS.fixed
  refine WP.seq (WP.mono (gMulG_ok hc hC hd hW hcd hp hS) fun s₅ ⟨K₅, U₅, M₅, L₅, R₅⟩ => ?_)
  have hs₅ := hS.scr.of_keepRegs K₅ (rdi_not_powClob _)
  have F₅ := F.unch h7 hn fixedOk_gWA U₅
  refine WP.seq (WP.mono (pPow_ok hc hs₅ M₅
    (L₅ (c.sl RZ) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))) F₅.onep
    (fun h9 t ht => by
      show s₅.mem (off (s₀.gpr .r8) (bitsAt c.n 1 + t)) = _
      rw [tbl_unch U₅ h7 hn (j := 1) (by decide) ht (tbl_apart_gWA (Or.inl rfl) ht)]
      exact hS.t₁ h9 t ht)) fun s₆ ⟨K₆, U₆, lt₆, v₆⟩ => h s₆ ?_)
  have e₆ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → i ≠ TT →
      i ∉ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM] →
      sv c (s₀.gpr .r8) s₆ i = sv c (s₀.gpr .r8) s i := fun hi h₁ h₃ h₂ =>
    (sv_unch U₆ h7 hn hi (apart_pwW hi h₁)).trans
      (sv_unch U₅ h7 hn hi (apart_gWA hi h₂ fun h => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · exact h₁ (by decide)
        · exact h₃ rfl))
  have r₆ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → sv c (s₀.gpr .r8) s₆ i = sv c (s₀.gpr .r8) s₅ i := fun hi h₁ =>
    sv_unch U₆ h7 hn hi (apart_pwW hi h₁)
  refine ⟨⟨hs₅.of_keepRegs K₆ (rdi_not_invClob _), ?_, by rw [K₆.wr, K₅.wr, hS.wr],
    F₅.unch h7 hn fixedOk_pwW U₆⟩,
    by rw [e₆ (by decide) (by decide) (by decide) (by decide), hS.k],
    by rw [e₆ (by decide) (by decide) (by decide) (by decide), hS.d],
    by rw [e₆ (by decide) (by decide) (by decide) (by decide), hS.e],
    by rw [flag_unch_pwW U₆ h7 h0 hn, flag_unch_gWA U₅ h7 h0 hn, hS.flag], ?_, ?_, lt₆, ?_,
    ?_⟩
  · rw [K₆.gpr _ (rsi_not_invClob _), K₅.gpr _ (rsi_not_powClob _), hS.rsi]
  · intro t ht
    rw [tbl_unch U₆ h7 hn (j := 2) (by decide) ht (tbl_apart_pwW (by decide) ht),
      tbl_unch U₅ h7 hn (j := 2) (by decide) ht (tbl_apart_gWA (Or.inr rfl) ht)]
    exact hS.t₂ t ht
  · show Rep c.C (toM _ _ (sv c (s₀.gpr .r8) s₆ RX)) (toM _ _ (sv c (s₀.gpr .r8) s₆ RY)) (toM _ _ (sv c (s₀.gpr .r8) s₆ RZ)) _
    rw [r₆ (i := RX) (by decide) (by decide), r₆ (i := RY) (by decide) (by decide),
      r₆ (i := RZ) (by decide) (by decide)]
    exact R₅
  · show _ = toM _ _ (sv c (s₀.gpr .r8) s₆ RZ) ^ _
    rw [r₆ (i := RZ) (by decide) (by decide)]
    exact v₆
  · rw [r₆ (i := RZ) (by decide) (by decide)]
    exact L₅ (c.sl RZ) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))


theorem signG_inline (c : Cfg) (d : CombData) : (c.signG d).inline = .seq (.block c.setup) (.seq (c.kBitsIf false)
    (.seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n)) (.seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n))
    (.seq (c.gMulG d).inline (.seq c.pPow.inline (.seq c.middle.inline (.seq c.nPow.inline c.scalar.inline))))))) := by
  show Code.seq _ (Code.seq (c.kBitsIf false).inline (Code.seq _ (Code.seq _ (Code.seq _
    (Code.seq c.pPow.inline (Code.seq c.middle.inline (Code.seq c.nPow.inline c.scalar.inline))))))) = _
  rw [kBitsIf_inline]
  rfl

/-- `sign_ok` for `signG d`. -/
theorem signG_ok (hc : BaseCfgOk c) (hC : Law c.C) {d : CombData} (hd : CombOk c d)
    (hW : CombOkW c.C d.w (c.combJ d.w) d.tbl d.start) (hcd : c.gtab = some d) {s₀ : State} (hp : Pre c s₀) :
    WP isa (c.signG d).inline s₀ fun s' => (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s₀.gpr r) ∧ SignPost c s₀ s' := by
  rw [signG_inline]
  exact stage₁ hc (Or.inr (Or.inr rfl)) hp.setup fun _ S₁ => stage₂G hc hC hd hW hcd hp rfl S₁ fun _ S₂ =>
    stage₃ hc S₂ fun _ S₃ => stage₄ hc hC hp rfl S₃

end VG.Proof.Ecdsa.X86_64
