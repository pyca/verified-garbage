import VerifiedGarbage.Proof.EcKey.X86.Finish
import VerifiedGarbage.Proof.Ecdsa.X86.Middle
import VerifiedGarbage.Proof.Ecdsa.X86.Main
import VerifiedGarbage.Proof.EcKey.PublicKey

/-!
# Elliptic curve public keys on x86 (32-bit): the whole function

As on x86-64 and AArch64 (`Proof/EcKey/AArch64/Main.lean`).

`middle_ok`: `middle` computes `x = X Z^(p-2)` and `y = Y Z^(p-2)` from the
power in `ACC`, each left Montgomery's form (`pkOps_ok`), ands the masks of
`d ∈ [1, n-1]` and `Z ≠ 0` into the flag, and writes the result
(`pkFinish_ok`).

`publicKey_ok`: `Cfg.publicKey` computes the specification's public key of
`d`, for any curve the ECDSA proof supports (`CfgOk`), and restores the
callee-saved registers. The code up to `Z^(p-2)` is the signature's, with
its setup reading `k`, `d` and the hash all from `d` (`Args.publicKey`):
its proof (`stage₁`, `stage₂`) is for any arguments the setup reads.
-/

namespace VG.Proof.EcKey.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86
open VG.Impl.EcKey.X86 (YM Y Args.publicKey)

variable {c : Cfg}

theorem middle_eq (c : Cfg) : Impl.EcKey.X86.Cfg.middle c =
    .seq (mul c.MP' c.wk (c.sl XM) (c.sl RX) (c.sl ACC))
    (.seq (mul c.MP' c.wk (c.sl X) (c.sl XM) (c.sl ONE))
    (.seq (mul c.MP' c.wk (c.sl YM) (c.sl RY) (c.sl ACC))
    (.seq (mul c.MP' c.wk (c.sl Y) (c.sl YM) (c.sl ONE))
    (.block (c.checkRange (c.sl D) ++ c.checkNonzero (c.sl RZ) ++ Impl.EcKey.X86.Cfg.finish c))))) := rfl

/-- What `middle`'s field operations leave. -/
structure OpsPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  gpr : ∀ r, r ∉ clob → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unch : Unch base (slW c [XM, X, YM, Y, TMP] ++ [(c.wk, 16 * c.n + 4)]) s.mem s'.mem
  x_lt : sv c base s' X < c.C.p
  x : Fin.ofNat c.C.p (sv c base s' X) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)
  y_lt : sv c base s' Y < c.C.p
  y : Fin.ofNat c.C.p (sv c base s' Y) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s RY) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)

/-- The four field operations of `middle`. -/
theorem pkOps_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hMP : ModOkW c.MP' size c.C.p s.mem base) (hacc : sv c base s ACC < c.C.p) (hone : sv c base s ONE = 1)
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', OpsPost c base s s' → WP isa rest s' Q) :
    WP isa (.seq (mul c.MP' c.wk (c.sl XM) (c.sl RX) (c.sl ACC))
      (.seq (mul c.MP' c.wk (c.sl X) (c.sl XM) (c.sl ONE))
      (.seq (mul c.MP' c.wk (c.sl YM) (c.sl RY) (c.sl ACC))
      (.seq (mul c.MP' c.wk (c.sl Y) (c.sl YM) (c.sl ONE)) rest)))) s Q := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  -- `XM = X · ACC`.
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) (.inl rfl) rfl h7 hs hMP (o := XM) (a := RX) (b := ACC) (by decide)
    (by decide) (by decide) (by decide) hacc) fun s₁ ⟨k₁, _, e₁⟩ => ?_)
  have hs₁ := k₁.scr hs
  have kP₁ := hMP.keepX86 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  have v₁ : ∀ {i}, i < 45 → i ≠ XM → i ≠ TMP → sv c base s₁ i = sv c base s i := fun hi h₁ h₂ =>
    sv_keep (MP'_n c) rfl h7 hn k₁ hi h₁ h₂
  -- `X = XM · 1`.
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) (.inl rfl) rfl h7 hs₁ kP₁ (o := X) (a := XM) (b := ONE) (by decide)
    (by decide) (by decide) (by decide) (by rw [v₁ (by decide) (by decide) (by decide), hone]; omega))
    fun s₂ ⟨k₂, lt₂, e₂⟩ => ?_)
  have hs₂ := k₂.scr hs₁
  have kP₂ := kP₁.keepX86 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  have v₂ : ∀ {i}, i < 45 → i ≠ XM → i ≠ X → i ≠ TMP → sv c base s₂ i = sv c base s i := fun hi h₁ h₂ h₃ =>
    (sv_keep (MP'_n c) rfl h7 hn k₂ hi h₂ h₃).trans (v₁ hi h₁ h₃)
  have x₂ : Fin.ofNat c.C.p (sv c base s₂ X) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) := by
    rw [toM_one_mul hpR (by rw [e₂, v₁ (i := ONE) (by decide) (by decide) (by decide), hone]),
      toM_mul hpR e₁]
  -- `YM = Y · ACC`.
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) (.inl rfl) rfl h7 hs₂ kP₂ (o := YM) (a := RY) (b := ACC) (by decide)
    (by decide) (by decide) (by decide) (by rw [v₂ (by decide) (by decide) (by decide) (by decide)]; exact hacc))
    fun s₃ ⟨k₃, _, e₃⟩ => ?_)
  have hs₃ := k₃.scr hs₂
  have kP₃ := kP₂.keepX86 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₃ (by decide) (by decide)
  have v₃ : ∀ {i}, i < 45 → i ≠ XM → i ≠ X → i ≠ YM → i ≠ TMP → sv c base s₃ i = sv c base s i :=
    fun hi h₁ h₂ h₃ h₄ => (sv_keep (MP'_n c) rfl h7 hn k₃ hi h₃ h₄).trans (v₂ hi h₁ h₂ h₄)
  -- `Y = YM · 1`.
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) (.inl rfl) rfl h7 hs₃ kP₃ (o := Y) (a := YM) (b := ONE) (by decide)
    (by decide) (by decide) (by decide)
    (by rw [v₃ (by decide) (by decide) (by decide) (by decide) (by decide), hone]; omega))
    fun s₄ ⟨k₄, lt₄, e₄⟩ => h s₄ ?_)
  have X₄ : sv c base s₄ X = sv c base s₂ X := by
    rw [sv_keep (MP'_n c) rfl h7 hn k₄ (by decide) (by decide) (by decide),
      sv_keep (MP'_n c) rfl h7 hn k₃ (by decide) (by decide) (by decide)]
  have e₃' : sv c base s₃ YM * 2 ^ (64 * c.n) % c.C.p = sv c base s RY * sv c base s ACC % c.C.p := by
    rw [e₃, v₂ (i := RY) (by decide) (by decide) (by decide) (by decide),
      v₂ (i := ACC) (by decide) (by decide) (by decide) (by decide)]
  refine ⟨k₄.scr hs₃, fun r hr => ?_, by rw [k₄.rd, k₃.rd, k₂.rd, k₁.rd], by rw [k₄.wr, k₃.wr, k₂.wr, k₁.wr],
    ?_, by rw [X₄]; exact lt₂, by rw [X₄]; exact x₂, lt₄, ?_⟩
  · rw [k₄.gpr r hr, k₃.gpr r hr, k₂.gpr r hr, k₁.gpr r hr]
  · exact (((unch_slots (MP'_n c) rfl k₁.unch (l := [XM, X, YM, Y, TMP]) (by simp) (by simp)).trans
      (unch_slots (MP'_n c) rfl k₂.unch (l := [XM, X, YM, Y, TMP]) (by simp) (by simp))).trans
      ((unch_slots (MP'_n c) rfl k₃.unch (l := [XM, X, YM, Y, TMP]) (by simp) (by simp)).trans
      (unch_slots (MP'_n c) rfl k₄.unch (l := [XM, X, YM, Y, TMP]) (by simp) (by simp)))).mono fun w hw => by
        simpa only [List.mem_append, or_self] using hw
  · rw [toM_one_mul hpR (by rw [e₄, v₃ (i := ONE) (by decide) (by decide) (by decide) (by decide) (by decide),
      hone]), toM_mul hpR e₃']

/-- Whether the public key is a point the result encodes: `d` in `[1, n-1]`
and `Z ≠ 0`. -/
abbrev ok (c : Cfg) (base : Addr) (s : State) : Bool :=
  decide ((0 < sv c base s D ∧ sv c base s D < c.C.n) ∧ sv c base s RZ ≠ 0)

/-- `x`, `y`, the checks and the result, from a state that changed only the
working space since `s₀`. -/
theorem middle_ok (hc : CfgOk c) {s₀ : State} {base : Addr} {s : State} (hs : Scr s base size)
    (F : Fixed c base s₀.gpr s.mem) (hacc : sv c base s ACC < c.C.p) (hflag : flagW c base s = BitVec.allOnes 32)
    (hwhole : Unch base [(0, size)] s₀.mem s.mem) (hesp : s.gpr .esp = s₀.gpr .esp) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hin : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ 0) 4)
    (hdarg : Region.Disjoint ⟨argAddr s₀ 0, 4⟩ ⟨base, size⟩) (hofit : (arg s₀ 0).toNat + (1 + 16 * c.n) ≤ 2 ^ 32)
    (hw : (⟨ptr s₀ 0, 1 + 16 * c.n⟩ : Region) ∈ s₀.wr)
    (hd : Region.Disjoint ⟨ptr s₀ 0, 1 + 16 * c.n⟩ ⟨base, size⟩) :
    WP isa (Impl.EcKey.X86.Cfg.middle c) s fun s' => ∃ xv yv, xv < c.C.p ∧
      Fin.ofNat c.C.p xv =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) ∧
      yv < c.C.p ∧ Fin.ofNat c.C.p yv =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s RY) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) ∧
      Spec.Ecdsa.bytesAt s'.mem (ptr s₀ 0) (1 + 16 * c.n) =
        (if ok c base s then 4 :: (toBytes (8 * c.n) xv ++ toBytes (8 * c.n) yv)
          else List.replicate (1 + 16 * c.n) 0) ∧
      s'.gpr .eax = (if ok c base s then 1 else 0) ∧
      (∀ rd ∈ Cfg.saved, s'.gpr rd.1 = s₀.gpr rd.1) ∧ s'.gpr .esp = s₀.gpr .esp ∧
      ∃ m, Unch base [(0, size)] s₀.mem m ∧ Outside (ptr s₀ 0) 0 (1 + 16 * c.n) m s'.mem := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hf : c.sl FLAG + 4 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega
  rw [middle_eq]
  refine pkOps_ok hc hs (modP_of hc F.mp) hacc F.one fun s₄ Op => ?_
  have F₄ := F.unch h7 hn (fixedOk_slWk (l := [XM, X, YM, Y, TMP]) (by decide)) Op.unch
  have e₄ : ∀ {i}, i < 45 → i ∉ [XM, X, YM, Y, TMP] → sv c base s₄ i = sv c base s i := fun hi hl =>
    sv_unch Op.unch h7 hn hi (apart_slWk hi hl)
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (checkRange_ok c Op.scr h0 (sl_le c h7 (i := D) (by decide)) (sl_le c h7 (i := MN) (by decide))
    hf) fun s₅ ⟨f₅, k₅, O₅⟩ => ?_
  have hs₅ := Op.scr.of_keeps k₅ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (checkNonzero_ok c hs₅ h0 (sl_le c h7 (i := RZ) (by decide)) hf) fun s₆ ⟨f₆, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_keeps k₆ (by decide)
  have F₆ := (F₄.unch h7 hn fixedOk_flag O₅.unch).unch h7 hn fixedOk_flag O₆.unch
  have e₆ : ∀ {i}, i < 45 → i ≠ FLAG → sv c base s₆ i = sv c base s₄ i := fun hi hif =>
    (sv_flag O₆ h0 h7 hn hi hif).trans (sv_flag O₅ h0 h7 hn hi hif)
  have hflag₆ : flagW c base s₆ = mask32 (ok c base s = true) := by
    have hMN : wordsVal s₄.mem base (c.sl MN) c.n = c.C.n := F₄.mn
    have z₄ : wordsVal s₄.mem base (c.sl RZ) c.n = sv c base s RZ := e₄ (by decide) (by decide)
    have d₄ : wordsVal s₄.mem base (c.sl D) c.n = sv c base s D := e₄ (by decide) (by decide)
    rw [f₆, f₅, flagW, flag_unch Op.unch h7 h0 hn (by decide), ← flagW, hflag,
      sv_flag O₅ h0 h7 hn (i := RZ) (by decide) (by decide), hMN, z₄, d₄, BitVec.allOnes_and, mask32_and]
    simp only [mask32, decide_eq_true_eq]
  have W₆ : Unch base [(0, size)] s₀.mem s₆.mem :=
    whole_of (whole_of (whole_of hwhole Op.unch (slWk_le h7 (by decide))) O₅.unch (flag_le h0 h7))
      O₆.unch (flag_le h0 h7)
  have hesp₆ : s₆.gpr .esp = s₀.gpr .esp := by
    rw [k₆.1 _ (by decide), k₅.1 _ (by decide), Op.gpr _ (by decide), hesp]
  have hrd₆ : s₆.rd = s₀.rd := by rw [k₆.2.1, k₅.2.1, Op.rd, hrd]
  have hwr₆ : s₆.wr = s₀.wr := by rw [k₆.2.2, k₅.2.2, Op.wr, hwr]
  have hout := argLoad_ok (i := 0) hin hdarg hesp₆ (by rw [hrd₆, hwr₆]) (W₆.outside fun w hw => by
    rw [List.mem_singleton.mp hw]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩)
  refine WP.mono (pkFinish_ok hc hs₆ hout hofit (by rw [hwr₆]; exact hw) hd F₆.saved _ hflag₆)
    fun s' ⟨bytes, ret, saved, others, Oout⟩ =>
      ⟨_, _, Op.x_lt, Op.x, Op.y_lt, Op.y, ?_, ret, saved, by rw [others _ (by decide), hesp₆],
        s₆.mem, W₆, Oout⟩
  rw [bytes, e₆ (i := X) (by decide) (by decide), e₆ (i := Y) (by decide) (by decide)]

/-- The arguments: `out` (`1 + 16 n` bytes), `d` (`8 n` bytes) and `scratch`,
readable and writable as the contract says and apart from each other as it
says. -/
structure PkPre (c : Cfg) (s : State) : Prop where
  rd : s.rd = [⟨ptr s 1, 8 * c.n⟩, ⟨argAddr s 0, 12⟩]
  wr : s.wr = [⟨ptr s 0, 1 + 16 * c.n⟩, ⟨ptr s 2, size⟩]
  out_sc : Region.Disjoint ⟨ptr s 0, 1 + 16 * c.n⟩ ⟨ptr s 2, size⟩
  out_d : Region.Disjoint ⟨ptr s 0, 1 + 16 * c.n⟩ ⟨ptr s 1, 8 * c.n⟩
  d_sc : Region.Disjoint ⟨ptr s 1, 8 * c.n⟩ ⟨ptr s 2, size⟩
  args_out : Region.Disjoint ⟨argAddr s 0, 12⟩ ⟨ptr s 0, 1 + 16 * c.n⟩
  args_sc : Region.Disjoint ⟨argAddr s 0, 12⟩ ⟨ptr s 2, size⟩
  ret_out : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨ptr s 0, 1 + 16 * c.n⟩
  ret_sc : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨ptr s 2, size⟩
  out_fit : (arg s 0).toNat + (1 + 16 * c.n) ≤ 2 ^ 32
  d_fit : (arg s 1).toNat + 8 * c.n ≤ 2 ^ 32
  sc_fit : (arg s 2).toNat + size ≤ 2 ^ 32
  sp_fit : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32

theorem idx_publicKey {i : Nat} (hi : i ∈ Args.publicKey.idx) : i < 3 := by
  simp only [Args.idx, List.mem_cons, List.not_mem_nil, or_false] at hi
  omega

theorem PkPre.setup {s : State} (hp : PkPre c s) (hl : c.C.len = 8 * c.n) : SetupPre c Args.publicKey s where
  shift := .inl rfl
  wr := by rw [hp.wr]; simp
  arg_in := fun i hi => ⟨_, by rw [hp.rd]; simp, arg_containsN (k := 3) (by have := hp.sp_fit; omega)
    (idx_publicKey hi)⟩
  arg_sc := fun i hi => hp.args_sc.sub_left (arg_subN (k := 3) (by have := hp.sp_fit; omega) (idx_publicKey hi))
  sp_fit := fun i hi => by have := idx_publicKey hi; have := hp.sp_fit; omega
  k_in := hl ▸ inRegions_words (by rw [hp.rd]; simp) (by have := hp.d_fit; omega)
  d_in := hl ▸ inRegions_words (by rw [hp.rd]; simp) (by have := hp.d_fit; omega)
  e_in := hl ▸ inRegions_words (by rw [hp.rd]; simp) (by have := hp.d_fit; omega)
  k_sc := hl ▸ hp.d_sc
  d_sc := hl ▸ hp.d_sc
  e_sc := hl ▸ hp.d_sc
  k_fit := hl ▸ hp.d_fit
  d_fit := hl ▸ hp.d_fit
  e_fit := hl ▸ hp.d_fit
  sc_fit := hp.sc_fit

/-- The private key. -/
abbrev dk (c : Cfg) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 1) (8 * c.n))

/-- The result the contract asks for: the specification's public key of `d`,
`04 ‖ x ‖ y`, and `1`, or zeros and `0`. -/
def PkPost (c : Cfg) (s₀ s' : State) : Prop :=
  match Spec.EcKey.publicKey c.C (dk c s₀) with
  | some (.affine x y) => s'.gpr .eax = 1 ∧
      Spec.Ecdsa.bytesAt s'.mem (ptr s₀ 0) (1 + 16 * c.n) = Spec.EcKey.encodePoint (.affine x y)
  | _ => s'.gpr .eax = 0 ∧
      Spec.Ecdsa.bytesAt s'.mem (ptr s₀ 0) (1 + 16 * c.n) = List.replicate (1 + 16 * c.n) 0

/-- What the function keeps: the callee-saved registers, `esp`, and memory
but the working space and `out`. -/
structure PkKeep (c : Cfg) (s₀ s' : State) : Prop where
  saved : ∀ rd ∈ Cfg.saved, s'.gpr rd.1 = s₀.gpr rd.1
  esp : s'.gpr .esp = s₀.gpr .esp
  frame : ∃ m : Mem, Unch (ptr s₀ 2) [(0, size)] s₀.mem m ∧ Outside (ptr s₀ 0) 0 (1 + 16 * c.n) m s'.mem

theorem publicKey_eq' (c : Cfg) : Impl.EcKey.X86.Cfg.publicKey c =
    .seq (.seq (.block (c.setupWith Args.publicKey)) (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n))
      (.seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n)) (.seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n))
      (.seq (ladder c.ladderCfg c.wk) (.seq (pow c.powP c.wk) (.block [])))))))
      (Impl.EcKey.X86.Cfg.middle c) := rfl

/-- `vg_ec_<curve>_public_key` computes the specification's public key and
restores the callee-saved registers. -/
theorem publicKey_ok (hc : CfgOk c) (hl : c.C.len = 8 * c.n) (hC : Law c.C) {s₀ : State} (hp : PkPre c s₀) :
    WP isa (Impl.EcKey.X86.Cfg.publicKey c) s₀ fun s' => PkKeep c s₀ s' ∧ PkPost c s₀ s' := by
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  rw [publicKey_eq']
  refine WP.seq (stage₁ hc (hp.setup hl) fun _ S₁ => stage₂ hc hC S₁ fun s₂ S₂ => WP.block_nil ?_)
  have h3 : (s₀.gpr .esp).toNat + 4 + 4 * 3 ≤ 2 ^ 32 := by have := hp.sp_fit; omega
  refine WP.mono (middle_ok hc S₂.scr S₂.fixed S₂.acc_lt S₂.flag S₂.whole S₂.esp S₂.rd S₂.wr
    ⟨_, by rw [hp.rd]; simp, arg_containsN h3 (by decide)⟩ (hp.args_sc.sub_left (arg_subN h3 (by decide)))
    hp.out_fit (by rw [hp.wr]; simp) hp.out_sc)
    fun s' ⟨xv, yv, hxl, hx, hyl, hy, bytes, rax, saved, esp, frame⟩ => ⟨⟨saved, esp, frame⟩, ?_⟩
  -- The specification.
  have hD : sv c (ptr s₀ 2) s₂ D = dk c s₀ := by rw [S₂.d, dv_eq rfl, hl]
  have hR := S₂.rep
  have hxX : Fin.ofNat c.C.p xv = tmv c.C c.n (ptr s₀ 2) s₂ (c.sl RX) *
      tmv c.C c.n (ptr s₀ 2) s₂ (c.sl RZ) ^ (c.C.p - 2) := by rw [hx, S₂.acc]
  have hyY : Fin.ofNat c.C.p yv = tmv c.C c.n (ptr s₀ 2) s₂ (c.sl RY) *
      tmv c.C c.n (ptr s₀ 2) s₂ (c.sl RZ) ^ (c.C.p - 2) := by rw [hy, S₂.acc]
  have hz := toM_eq_zero_iff hpR (x := sv c (ptr s₀ 2) s₂ RZ) S₂.rz_lt
  unfold PkPost
  have hdk : dk c s₀ = kv c Args.publicKey s₀ := by rw [kv_eq rfl, hl]
  rw [hdk, publicKey_eq hC hR hxl hxX hyl hyY, ← hdk]
  by_cases hd : 1 ≤ dk c s₀ ∧ dk c s₀ < c.C.n
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hd)]
    by_cases h0 : sv c (ptr s₀ 2) s₂ RZ = 0
    · have hok : ok c (ptr s₀ 2) s₂ = false := decide_eq_false (by rw [hD]; omega)
      rw [ite_eq_left_of_eq_true _ _ (eq_true (hz.mpr h0))]
      exact ⟨by rw [rax, hok]; rfl, by rw [bytes, hok]; rfl⟩
    · have hok : ok c (ptr s₀ 2) s₂ = true := decide_eq_true (by rw [hD]; omega)
      rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => h0 (hz.mp h)))]
      refine ⟨by rw [rax, hok]; rfl, ?_⟩
      rw [bytes, hok]
      show _ = 4 :: (toBytes c.C.len xv ++ toBytes c.C.len yv)
      rw [hl]; rfl
  · have hok : ok c (ptr s₀ 2) s₂ = false := decide_eq_false (by rw [hD]; omega)
    rw [ite_eq_right_of_eq_false _ _ (eq_false hd)]
    exact ⟨by rw [rax, hok]; rfl, by rw [bytes, hok]; rfl⟩

end VG.Proof.EcKey.X86
