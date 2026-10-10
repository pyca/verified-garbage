import VerifiedGarbage.Proof.Ecdh.Arm.Validate
import VerifiedGarbage.Proof.Ecdh.Exchange

/-!
# ECDH on 32-bit ARM: the result, and the whole function

As on x86 (`Proof/Ecdh/X86/Main.lean`).

## `x`, the checks and the result

`middle` computes `x = X Z^(p-2)` from `X` and the power in `ACC`, left
Montgomery's form by a multiplication by 1, ands the masks of `d ∈ [1, n-1]`
and `Z ≠ 0` into the flag, and writes `x` or zeros through `lr`
(`middle_ok`); `finish` writes the result as the signature's does
(`ecFinish_ok`).
-/

namespace VG.Proof.Ecdh.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp op2_imm dpVal)

variable {c : Cfg}

theorem finish_eq (c : Cfg) : Impl.Ecdh.Arm.Cfg.finish c = .ldr .r10 wb (c.sl FLAG) ::
    (storeBytes c.C.len c.n .lr 0 (c.sl X) ++ (.dp .and .r0 .r10 (.imm 1) :: Cfg.restore)) := by
  simp only [Impl.Ecdh.Arm.Cfg.finish, List.append_assoc, List.cons_append, List.nil_append]

/-- `x` or zeros, the return value and the callee-saved registers. -/
theorem ecFinish_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size) {o32 : BitVec 32}
    (hout : s.gpr .lr = o32) (hofit : o32.toNat + c.C.len ≤ 2 ^ 32)
    (hw : (⟨State.addr o32, c.C.len⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨State.addr o32, c.C.len⟩ ⟨base, size⟩)
    {g : Reg → BitVec 32} (hsv : ∀ rd ∈ Cfg.saved, s.mem.readW (off base rd.2) 32 = g rd.1) (b : Bool)
    (hf : flagW c base s = mask32 (b = true)) :
    WP isa (.block (Impl.Ecdh.Arm.Cfg.finish c)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem (State.addr o32) c.C.len =
        (if b then toBytes c.C.len (sv c base s X) else List.replicate c.C.len 0) ∧
      s'.gpr .r0 = (if b then 1 else 0) ∧
      (∀ rd ∈ Cfg.saved, s'.gpr rd.1 = g rd.1) ∧
      Rest [.r0, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr] s s' ∧
      Outside (State.addr o32) 0 c.C.len s.mem s'.mem := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hsz : size = 4096 := rfl
  have hn0 := hc.n0
  have hX := sl_le c h7 (i := X) (by decide)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  generalize hout64 : State.addr o32 = out at hw hd ⊢
  have h0 : ∀ e, out + BitVec.ofNat 64 0 + BitVec.ofNat 64 e = out + BitVec.ofNat 64 e := fun e =>
    congrArg (· + BitVec.ofNat 64 e) (BitVec.add_zero out)
  rw [finish_eq]
  refine wp_ldr (hs.off_lt (by omega_arith)) (hs.ea (by omega_arith)) (hs.read (d := c.sl FLAG) (n := 4) (by omega_arith))
    fun s₁ u₁ => ?_
  have k₁ : Rest [.r10] s s₁ := u₁.rest (by simp)
  have hs₁ := hs.of_rest k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := u₁.mem
  have hc₁ : s₁.gpr .r10 = mask32 (b = true) := by rw [u₁.gpr, ← flagW, hf]
  have hr₁ : s₁.gpr .lr = o32 := by rw [u₁.other _ (by decide), hout]
  refine VG.Proof.X25519.Arm.WP.append (storeBytes_ok hs₁ (dst := .lr) (d := 0) (a := c.sl X) (by decide)
    (by decide) b hc₁ hX (by have := hc.len8; omega_arith) hc.len_hi (by rw [hr₁]; omega_arith)
    (by have := hc.len_hi; omega_arith) (fun e m he => ⟨_, by rw [k₁.wr]; exact hw, by
      rw [hr₁, hout64, h0]; exact Offset.contains_base out (by omega_arith) (by omega_arith)⟩)
    (by
      rw [hr₁, hout64]
      exact (hd.symm.sub_left (Offset.sub_base base hX)).sub_right (Offset.sub_base out (by omega_arith))))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  rw [hr₁, hout64] at e₂ O₂
  rw [(BitVec.add_zero out : out + BitVec.ofNat 64 0 = out)] at e₂ O₂
  have hs₂ := hs₁.of_rest k₂ (by decide)
  have U₂ := O₂.unch_far hd.symm
  have hc₂ : s₂.gpr .r10 = mask32 (b = true) := by rw [k₂.gpr _ (by decide), hc₁]
  have hsv₂ : ∀ rd ∈ Cfg.saved, s₂.mem.readW (off base rd.2) 32 = g rd.1 := by
    intro rd hrd
    have := saved_lt rd hrd
    have h16 : ∀ w ∈ [(size, 2 ^ 64)], rd.2 + 4 ≤ w.1 ∨ w.1 + w.2 ≤ rd.2 := fun w hw => by
      simp only [List.mem_singleton] at hw; subst hw; exact .inl (by omega_arith)
    rw [Unch.readW32 U₂ h16 (by omega_arith), hm₁, hsv rd hrd]
  -- The return value.
  refine wp_dp (op2_imm (by decide)) fun s₃ u₃ => ?_
  have hs₃ := hs₂.of_rest (u₃.rest (ws := [.r0]) (by simp)) (by decide)
  have r0₃ : s₃.gpr .r0 = if b then 1 else 0 := by
    rw [u₃.gpr, dpVal, hc₂]; exact mask_bit b
  -- The callee-saved registers.
  rw [restore_eq]
  refine WP.mono (ldrs_ok hs₃ Cfg.saved (fun p hp => by have := saved_lt p hp; omega_arith) saved_nodup
    (fun p hp => (saved_r12 p hp).1)) fun s' ⟨m', K', V'⟩ => ⟨?_, ?_, fun rd hrd => ?_, ?_, ?_⟩
  · rw [m', u₃.mem, e₂, hm₁]
  · rw [K'.gpr _ (by decide), r0₃]
  · rw [V' rd hrd, u₃.mem, hsv₂ rd hrd]
  · exact ((k₁.mono (by simp)).trans (k₂.mono (by simp))).trans
      ((u₃.rest (by simp)).trans (K'.mono (by decide)))
  · rw [m', u₃.mem, ← hm₁]
    exact O₂

theorem middle_eq (c : Cfg) : Impl.Ecdh.Arm.Cfg.middle c =
    .seq (Mont.mulCall c.SP (c.sl XM) (c.sl RX) (c.sl ACC))
    (.seq (Mont.mulCall c.SP (c.sl X) (c.sl XM) (c.sl ONE))
    (.block (c.checkRange (c.sl D) ++ c.checkNonzero (c.sl RZ) ++ Impl.Ecdh.Arm.Cfg.finish c))) := rfl

/-- Whether the result is a shared secret: the peer's key (`V`), `d` in
`[1, n-1]`, and `Z ≠ 0`. -/
abbrev ok (c : Cfg) (base : Addr) (s : State) (V : Prop) [Decidable V] : Bool :=
  decide ((V ∧ 0 < sv c base s D ∧ sv c base s D < c.C.n) ∧ sv c base s RZ ≠ 0)

/-- `x`, the checks of `d` and `Z`, and the result, from a state that
changed only the working space since `s₀`, with `out` in `lr`. -/
theorem middle_ok (hc : CfgOk c) {s₀ : State} {base : Addr} {s : State} (hs : Scr s base size) (hfar : Far s base 8192)
    (F : Fixed c base s₀.gpr s.mem) (hacc : sv c base s ACC < c.C.p)
    {V : Prop} [Decidable V] (hflag : flagW c base s = mask32 V)
    (hwhole : Unch base [(0, 8192)] s₀.mem s.mem) (hrest : Rest (.lr :: work) s₀ s) (hlr : s.gpr .lr = s₀.gpr .r0)
    (hofit : (s₀.gpr .r0).toNat + c.C.len ≤ 2 ^ 32)
    (hw : (⟨ptr s₀ .r0, c.C.len⟩ : Region) ∈ s₀.wr) (hd : Region.Disjoint ⟨ptr s₀ .r0, c.C.len⟩ ⟨base, size⟩) :
    WP isa (Impl.Ecdh.Arm.Cfg.middle c) s fun s' => ∃ xv, xv < c.C.p ∧
      Fin.ofNat c.C.p xv =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) ∧
      Spec.Ecdsa.bytesAt s'.mem (ptr s₀ .r0) c.C.len =
        (if ok c base s V then toBytes c.C.len xv else List.replicate c.C.len 0) ∧
      s'.gpr .r0 = (if ok c base s V then 1 else 0) ∧
      (∀ rd ∈ Cfg.saved, s'.gpr rd.1 = s₀.gpr rd.1) ∧ s'.sp = s₀.sp ∧
      ∃ m, Unch base [(0, 8192)] s₀.mem m ∧ Outside (ptr s₀ .r0) 0 c.C.len m s'.mem := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hfl : c.sl FLAG + 4 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_arith
  rw [middle_eq]
  have hM := modP_of hc F.mp
  have hone : sv c base s ONE = 1 := F.one
  -- `XM = X · ACC`.
  refine WP.seq (WP.mono (slMul_ok hc.fp (MP'_n c) h7 hs hfar (o := XM) (a := RX) (b := ACC) (by decide) (by decide) (by decide) hacc) fun s₁ ⟨k₁, _, e₁⟩ => ?_)
  have hs₁ := k₁.scr hs
  have hf₁ := hfar.of_rest k₁.rest
  have kP₁ := hM.keepArm (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  have v₁ : ∀ {i}, i < 45 → i ≠ XM → i ≠ TMP → sv c base s₁ i = sv c base s i := fun hi h₁ h₂ =>
    sv_keep (MP'_n c) rfl h7 hn k₁ hi h₁ h₂
  -- `X = XM · 1`.
  refine WP.seq (WP.mono (slMul_ok hc.fp (MP'_n c) h7 hs₁ hf₁ (o := X) (a := XM) (b := ONE) (by decide) (by decide) (by decide) (by rw [v₁ (by decide) (by decide) (by decide), hone]; omega_arith))
    fun s₂ ⟨k₂, lt₂, e₂⟩ => ?_)
  have hs₂ := k₂.scr hs₁
  have hf₂ := hf₁.of_rest k₂.rest
  have v₂ : ∀ {i}, i < 45 → i ≠ XM → i ≠ X → i ≠ TMP → sv c base s₂ i = sv c base s i := fun hi h₁ h₂ h₃ =>
    (sv_keep (MP'_n c) rfl h7 hn k₂ hi h₂ h₃).trans (v₁ hi h₁ h₃)
  have x₂ : Fin.ofNat c.C.p (sv c base s₂ X) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) := by
    rw [toM_one_mul hpR (by rw [e₂, v₁ (i := ONE) (by decide) (by decide) (by decide), hone]),
      toM_mul hpR e₁]
  have U₂ : Unch base (slWk c [XM, X, TMP]) s.mem s₂.mem :=
    ((unch_slots (MP'_n c) rfl k₁.unchOne (l := [XM, X, TMP]) (by simp) (by simp)).trans
      (unch_slots (MP'_n c) rfl k₂.unchOne (l := [XM, X, TMP]) (by simp) (by simp))).mono
      fun w hw => by simpa only [List.mem_append, or_self] using hw
  have F₂ := F.unch h7 hn (fixedOk_slWk h7 (l := [XM, X, TMP]) (by decide)) U₂
  rw [List.append_assoc]
  refine VG.Proof.X25519.Arm.WP.append (checkRange_ok c hs₂ h0 (sl_le c h7 (i := D) (by decide))
    (sl_le c h7 (i := MN) (by decide)) hfl) fun s₅ ⟨f₅, k₅, O₅⟩ => ?_
  have hs₅ := hs₂.of_rest k₅ (by decide)
  refine VG.Proof.X25519.Arm.WP.append (checkNonzero_ok c hs₅ h0 (sl_le c h7 (i := RZ) (by decide)) hfl)
    fun s₆ ⟨f₆, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_rest k₆ (by decide)
  have F₆ := (F₂.unch h7 hn fixedOk_flag O₅.unch).unch h7 hn fixedOk_flag O₆.unch
  have hflag₆ : flagW c base s₆ = mask32 (ok c base s V = true) := by
    have hMN : wordsVal s₂.mem base (c.sl MN) c.n = c.C.n := F₂.mn
    have z₂ : wordsVal s₂.mem base (c.sl RZ) c.n = sv c base s RZ := v₂ (by decide) (by decide) (by decide) (by decide)
    have d₂ : wordsVal s₂.mem base (c.sl D) c.n = sv c base s D := v₂ (by decide) (by decide) (by decide) (by decide)
    rw [f₆, f₅, flagW, flag_unch U₂ h7 h0 hn (by decide), ← flagW, hflag,
      sv_flag O₅ h0 h7 hn (i := RZ) (by decide) (by decide), hMN, z₂, d₂, mask32_and, mask32_and]
    simp only [mask32, decide_eq_true_eq]
  have W₆ : Unch base [(0, 8192)] s₀.mem s₆.mem :=
    whole_of (whole_of (whole_of hwhole U₂ (slWk_le h7 (by decide))) O₅.unch (flag_le h0 h7))
      O₆.unch (flag_le h0 h7)
  have K₆ : Rest work s s₆ :=
    ((k₁.rest.trans k₂.rest).mono callClob_work).trans ((k₅.mono (by decide)).trans (k₆.mono (by decide)))
  have hlr₆ : s₆.gpr .lr = s₀.gpr .r0 := by rw [K₆.gpr _ (by decide), hlr]
  have hwr₆ : s₆.wr = s₀.wr := by rw [K₆.wr, hrest.wr]
  refine WP.mono (ecFinish_ok hc hs₆ hlr₆ hofit (by rw [hwr₆]; exact hw) hd F₆.saved _ hflag₆)
    fun s' ⟨bytes, ret, saved, others, Oout⟩ =>
      ⟨_, lt₂, x₂, ?_, ret, saved, by rw [others.sp, K₆.sp, hrest.sp], s₆.mem, W₆, Oout⟩
  have x₆ : sv c base s₆ X = sv c base s₂ X := (sv_flag O₆ h0 h7 hn (i := X) (by decide) (by decide)).trans
    (sv_flag O₅ h0 h7 hn (i := X) (by decide) (by decide))
  rw [bytes, x₆]

end VG.Proof.Ecdh.Arm

/-!
## The whole function

`exchange_ok`: `Cfg.exchange` computes the specification's shared secret of
`d` and the peer's public key, for any curve the ECDSA proof supports
(`CfgOk`), and restores the callee-saved registers.

The signature's setup, reading `k`, `d` and the hash all from `d` and the
working space from `r3` (`Args.ecdh`), and its tables (`stage₁`, which
leaves the peer's pointer in `r2`); then `peer_ok`, `validate_ok`,
`ladPow_ok` and `middle_ok`; `exchange_eq` connects what they compute to the
specification.
-/

namespace VG.Proof.Ecdh.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.Arm
open VG.Proof.X25519.Arm (Rest)
open VG.Impl.Ecdh.Arm (QY R2P BP QXM QYM W0 W1 W2 W3 PX PY Args.ecdh)

variable {c : Cfg}

/-- The arguments: `out` (`8 n` bytes), `d` (`8 n` bytes), `peer`
(`1 + 16 n` bytes) and `scratch`, readable and writable as the contract says
and apart from each other as it says. -/
structure EPre (c : Cfg) (s : State) : Prop where
  rd : s.rd = [⟨ptr s .r1, c.C.len⟩, ⟨ptr s .r2, 1 + 2 * c.C.len⟩]
  wr : s.wr = [⟨ptr s .r0, c.C.len⟩, ⟨ptr s .r3, 8192⟩]
  out_sc : Region.Disjoint ⟨ptr s .r0, c.C.len⟩ ⟨ptr s .r3, 8192⟩
  d_sc : Region.Disjoint ⟨ptr s .r1, c.C.len⟩ ⟨ptr s .r3, 8192⟩
  peer_sc : Region.Disjoint ⟨ptr s .r2, 1 + 2 * c.C.len⟩ ⟨ptr s .r3, 8192⟩
  out_fit : (s.gpr .r0).toNat + c.C.len ≤ 2 ^ 32
  d_fit : (s.gpr .r1).toNat + c.C.len ≤ 2 ^ 32
  peer_fit : (s.gpr .r2).toNat + (1 + 2 * c.C.len) ≤ 2 ^ 32
  sc_fit : (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32

theorem EPre.setup {s : State} (hp : EPre c s) : SetupPre c Args.ecdh s where
  shift := .inl rfl
  args := by unfold argsOk; decide
  sc_in := fun h => nomatch h
  wr := by show (⟨ptr s .r3, 8192⟩ : Region) ∈ s.wr; rw [hp.wr]; simp
  k_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.d_fit; omega_arith)
  d_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.d_fit; omega_arith)
  e_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.d_fit; omega_arith)
  k_sc := hp.d_sc.sub_right (Region.sub_prefix (by decide))
  d_sc := hp.d_sc.sub_right (Region.sub_prefix (by decide))
  e_sc := hp.d_sc.sub_right (Region.sub_prefix (by decide))
  k_fit := hp.d_fit
  d_fit := hp.d_fit
  e_fit := hp.d_fit
  sc_fit := hp.sc_fit

/-- The private key. -/
abbrev dk (c : Cfg) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r1) c.C.len)

/-- The result the contract asks for: the specification's shared secret, and
`1`, or zeros and `0`. -/
def EPost (c : Cfg) (s₀ s' : State) : Prop :=
  match Spec.Ecdh.exchange c.C (dk c s₀) (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r2) (1 + 2 * c.C.len)) with
  | some z => s'.gpr .r0 = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (ptr s₀ .r0) c.C.len = z
  | none => s'.gpr .r0 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (ptr s₀ .r0) c.C.len = List.replicate c.C.len 0

/-- What the function keeps: the callee-saved registers and `lr`, `sp`, and
memory but the working space and `out`. -/
structure EKeep (c : Cfg) (s₀ s' : State) : Prop where
  saved : ∀ rd ∈ Cfg.saved, s'.gpr rd.1 = s₀.gpr rd.1
  sp : s'.sp = s₀.sp
  frame : ∃ m : Mem, Unch (ptr s₀ .r3) [(0, 8192)] s₀.mem m ∧ Outside (ptr s₀ .r0) 0 c.C.len m s'.mem

/-- The point the ladder multiplies: the peer's, if its key is valid as the
code checks it, else `G`. -/
def peerPt (c : Cfg) (b4 : Prop) [Decidable b4] (x y : Nat) : Point c.C :=
  if h : ((b4 ∧ x < c.C.p) ∧ y < c.C.p) ∧ OnCurve c (Fin.ofNat c.C.p x) (Fin.ofNat c.C.p y) then
    .affine ⟨x, h.1.1.2⟩ ⟨y, h.1.2⟩ else G c.C

theorem peerPt_onCurve (hc : CfgOk c) (b4 : Prop) [Decidable b4] (x y : Nat) :
    onCurve c.C (peerPt c b4 x y) = true := by
  unfold peerPt
  split
  · next h => exact (onCurve_iff _ _).mpr h.2
  · exact hc.onG

theorem peerPt_rep (hC : Law c.C) (b4 : Prop) [Decidable b4] (x y : Nat) {X Y : Fe c.C}
    (hX : X = if ((b4 ∧ x < c.C.p) ∧ y < c.C.p) ∧ OnCurve c (Fin.ofNat c.C.p x) (Fin.ofNat c.C.p y)
      then Fin.ofNat c.C.p x else Fin.ofNat c.C.p c.C.gx)
    (hY : Y = if ((b4 ∧ x < c.C.p) ∧ y < c.C.p) ∧ OnCurve c (Fin.ofNat c.C.p x) (Fin.ofNat c.C.p y)
      then Fin.ofNat c.C.p y else Fin.ofNat c.C.p c.C.gy) :
    Rep c.C X Y 1 (peerPt c b4 x y) := by
  unfold peerPt
  by_cases h : ((b4 ∧ x < c.C.p) ∧ y < c.C.p) ∧ OnCurve c (Fin.ofNat c.C.p x) (Fin.ofNat c.C.p y)
  · rw [dite_eq_left h]; rw [ite_eq_left h] at hX hY
    rw [hX, hY]
    exact ⟨one_ne_zero_fe hC, by rw [EcKey.fe_eq h.1.1.2 rfl, Lean.Grind.Semiring.mul_one],
      by rw [EcKey.fe_eq h.1.2 rfl, Lean.Grind.Semiring.mul_one]⟩
  · rw [dite_eq_right h]; rw [ite_eq_right h] at hX hY; rw [hX, hY]
    exact rep_affine' hC _ _

/-- The peer's key: `04`, `x` and `y`. -/
theorem peer_bytes (m : Mem) (p : Addr) (L : Nat) :
    Spec.Ecdsa.bytesAt m p (1 + 2 * L) = m p :: (Spec.Ecdsa.bytesAt m (p + BitVec.ofNat 64 1) L ++
      Spec.Ecdsa.bytesAt m (p + BitVec.ofNat 64 (1 + L)) L) := by
  have h1 : Spec.Ecdsa.bytesAt m p 1 = [m p] := by
    simp only [Spec.Ecdsa.bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero]
  rw [show 1 + 2 * L = 1 + (L + L) by omega_arith, bytesAt_add, bytesAt_add, h1, BitVec.add_assoc,
    BitVec.ofNat_add_ofNat]
  rfl

theorem exchange_eq' (c : Cfg) : Impl.Ecdh.Arm.Cfg.exchange c =
    .seq (.seq (.block (c.setupWith Args.ecdh))
      (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) (.seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n))
      (.seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) (.block [])))))
    (.seq (.block (Impl.Ecdh.Arm.Cfg.peerAt c .r2)) (.seq (Impl.Ecdh.Arm.Cfg.validate c)
    (.seq (VG.Impl.Weierstrass.Arm.Point.ladderP (Impl.Ecdh.Arm.Cfg.ladderQ c) c.SP) (.seq (pow c.powP c.SP) (Impl.Ecdh.Arm.Cfg.middle c))))) :=
  rfl

/-- `vg_ecdh_<curve>` computes the specification's shared secret and restores
the callee-saved registers. -/
theorem exchange_ok (hc : CfgOk c) (hC : Law c.C) {s₀ : State} (hp : EPre c s₀) :
    WP isa (Impl.Ecdh.Arm.Cfg.exchange c) s₀ fun s' => EKeep c s₀ s' ∧ EPost c s₀ s' := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hlhi := hc.len_hi
  have hl8 := hc.len8
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  rw [exchange_eq']
  refine WP.seq (stage₁ hc hp.setup fun s₂ S₂ => WP.block_nil ?_)
  replace S₂ : St₁ c Args.ecdh s₀ (ptr s₀ .r3) s₂ := S₂
  have hn := S₂.scr.nowrap
  have W₂ : Outside (ptr s₀ .r3) 0 8192 s₀.mem s₂.mem :=
    S₂.whole.outside fun w hw => by rw [List.mem_singleton.mp hw]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  have hq₂ : s₂.gpr .r2 = s₀.gpr .r2 := S₂.args .r2 (by simp)
  have hpsc : Region.Disjoint ⟨ptr s₀ .r2, 1 + 2 * c.C.len⟩ ⟨ptr s₀ .r3, 8192⟩ := hp.peer_sc
  -- The peer's key.
  refine WP.seq (WP.mono (peer_ok hc S₂.scr (q := .r2) (by decide) (by decide)
    (by rw [hq₂]; exact hp.peer_fit) (by rw [hq₂, S₂.rest.rd, S₂.rest.wr, hp.rd]; simp)
    (by rw [hq₂]; exact hpsc.sub_right (Region.sub_prefix (by decide))) S₂.fixed.mp) fun s₃ ⟨hs₃, k₃, U₃, r2₃, bp₃, x₃, y₃, f₃⟩ => ?_)
  rw [hq₂] at x₃ y₃ f₃
  have F₃ := S₂.fixed.unch h7 hn ((fixedOk_slW (l := [R2P, BP, E, QY]) (by decide)).append fixedOk_flag) U₃
  have e₃ : ∀ {i}, i < 45 → i ∉ [R2P, BP, E, QY] → i ≠ FLAG →
      sv c (ptr s₀ .r3) s₃ i = sv c (ptr s₀ .r3) s₂ i := fun hi hl hf =>
    sv_unch U₃ h7 hn hi (apart_append (apart_slW hl) (apart_flag h0 hf))
  have hq0 : s₂.mem (ptr s₀ .r2) = s₀.mem (ptr s₀ .r2) := by
    have := keep_of_disjoint' W₂ hpsc (by omega_arith) (i := 0) (by omega_arith) (by omega_arith)
    rwa [BitVec.add_zero] at this
  -- What the code checks of the peer's key so far.
  have hf₃ : flagW c (ptr s₀ .r3) s₃ = mask32 (((s₀.mem (ptr s₀ .r2) = 4 ∧
      sv c (ptr s₀ .r3) s₃ E < c.C.p) ∧ sv c (ptr s₀ .r3) s₃ QY < c.C.p)) := by
    rw [f₃, S₂.flag, BitVec.allOnes_and, mask32_and, mask32_and]
    simp only [hq0]
  refine WP.seq (WP.mono (validate_ok hc hs₃ (S₂.far.of_rest k₃) F₃ r2₃ bp₃ hf₃)
    fun s₄ ⟨hs₄, g₄, U₄, f₄, px_lt, py_lt, px, py⟩ => ?_)
  have F₄ := F₃.unch h7 hn ((fixedOk_slWk h7 (l := [QXM, QYM, TMP, W0, W1, W2, W3, PY]) (by decide)).append
    fixedOk_flag) U₄
  have e₄ : ∀ {i}, i < 45 → i ∉ [QXM, QYM, TMP, W0, W1, W2, W3, PY] → i ≠ FLAG →
      sv c (ptr s₀ .r3) s₄ i = sv c (ptr s₀ .r3) s₃ i := fun hi hl hf =>
    sv_unch U₄ h7 hn hi (apart_append (apart_slWk h7 hi hl) (apart_flag h0 hf))
  have t₄ : ∀ {j}, j < 3 → ∀ t < 64 * c.n,
      s₄.mem (off (ptr s₀ .r3) (bitsAt c.n j + t)) = s₂.mem (off (ptr s₀ .r3) (bitsAt c.n j + t)) :=
    fun hj t ht => by
      rw [tbl_unch U₄ h7 hj ht (apart_append (tbl_apart_slWk h7 (by decide)) (tbl_apart_flag h7 h0 _ t)),
        tbl_unch U₃ h7 hj ht (apart_append (tbl_apart_slW h7 (by decide) _ t) (tbl_apart_flag h7 h0 _ t))]
  have hpk : sv c (ptr s₀ .r3) s₂ K < 2 ^ (64 * c.n) := wordsVal_lt _ _ _ _
  -- `[d]P`, then `Z^(p-2)`.
  have hstep := step_rep (L := Impl.Ecdh.Arm.Cfg.ladderQ c) (k := sv c (ptr s₀ .r3) s₂ K) hC
    (peerPt_onCurve hc _ _ _)
    (by
      show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₄.mem _ (c.sl AP) c.n) = _
      rw [F₄.ap]; exact toM_cmont hc _)
    (by
      show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₄.mem _ (c.sl B3P) c.n) = _
      rw [F₄.b3p]; exact toM_cmont hc _)
    (peerPt_rep hC _ _ _ px py |> fun h => by
      show Rep c.C (toM c.C.p (2 ^ (64 * c.n)) (sv c (ptr s₀ .r3) s₄ PX))
        (toM c.C.p (2 ^ (64 * c.n)) (sv c (ptr s₀ .r3) s₄ PY))
        (toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₄.mem (ptr s₀ .r3) (c.sl ONEP) c.n)) _
      rw [F₄.onep, toM_one hpR]; exact h)
  refine ladPow_ok hc hs₄ ((S₂.far.of_rest k₃).of_rest g₄) F₄ hstep
    (by rw [shiftRight_eq_zero hpk, mul_zero_pt]; exact rep_infinity' hC)
    px_lt py_lt
    (by rw [e₄ (by decide) (by decide) (by decide), e₃ (by decide) (by decide) (by decide)]; exact S₂.rx)
    (by rw [e₄ (by decide) (by decide) (by decide), e₃ (by decide) (by decide) (by decide)]; exact S₂.ry)
    (by rw [e₄ (by decide) (by decide) (by decide), e₃ (by decide) (by decide) (by decide)]; exact S₂.rz)
    (fun t ht => by rw [t₄ (j := 0) (by decide) t ht, S₂.t₀ t ht, S₂.k])
    (fun t ht => by rw [t₄ (j := 1) (by decide) t ht, S₂.t₁ t ht]) fun s₅ L => ?_
  have hs₅ := L.scr
  have F₅ := F₄.unch h7 hn ((fixedOk_slWkP h7 (by decide)).append (fixedOk_slWk h7 (l := [ACC, PT, TMP]) (by decide)))
    L.unch
  have e₅ : ∀ {i}, i < 45 → i ∉ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5,
      TX, TY, TZ, TMP] → i ∉ [ACC, PT, TMP] → sv c (ptr s₀ .r3) s₅ i = sv c (ptr s₀ .r3) s₄ i :=
    fun hi h₁ h₂ => sv_unch L.unch h7 hn hi (apart_append (apart_slWkP h7 hi h₁) (apart_slWk h7 hi h₂))
  have hflag₅ : flagW c (ptr s₀ .r3) s₅ = mask32 (PeerOk c (ptr s₀ .r3) s₃ ((s₀.mem (ptr s₀ .r2) = 4 ∧
      sv c (ptr s₀ .r3) s₃ E < c.C.p) ∧ sv c (ptr s₀ .r3) s₃ QY < c.C.p)) := by
    have hFl := sl_le c h7 (i := FLAG) (by decide)
    have ap : ∀ w ∈ slWkP c [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5,
        TX, TY, TZ, TMP] ++ slWk c [ACC, PT, TMP], c.sl FLAG + 4 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG := by
      intro w hw
      rcases apart_append (apart_slWkP (c := c) h7 (i := FLAG) (by decide) (by decide))
        (apart_slWk (c := c) h7 (i := FLAG) (l := [ACC, PT, TMP]) (by decide) (by decide)) w hw with h | h
      · exact Or.inl (by omega_arith)
      · exact Or.inr h
    rw [flagW, Unch.readW32 L.unch ap (by omega_arith), ← flagW]
    exact f₄
  have K₅ : Rest (.lr :: work) s₀ s₅ := S₂.rest.trans
    (((k₃.mono (by decide)).trans ((g₄.mono powClob_work).trans (L.rest.mono powClob_work))).mono (by simp))
  have hlr₅ : s₅.gpr .lr = s₀.gpr .r0 := by
    rw [L.rest.gpr _ (by decide), g₄.gpr _ (by decide), k₃.gpr _ (by decide), S₂.lr]
  have W₅ : Unch (ptr s₀ .r3) [(0, 8192)] s₀.mem s₅.mem :=
    whole_of (whole_of (whole_of S₂.whole U₃ (le_append (slWk_le h7 (l := [R2P, BP, E, QY]) (by decide) |>
      fun h w hw => h w (List.mem_append_left _ hw)) (flag_le h0 h7))) U₄
      (le_append (slWk_le h7 (by decide)) (flag_le h0 h7))) L.unch
      (le_append (slWkP_le h7 (by decide)) (slWk_le h7 (by decide)))
  refine WP.mono (middle_ok hc hs₅ (((S₂.far.of_rest k₃).of_rest g₄).of_rest L.rest) F₅ L.acc_lt hflag₅ W₅ K₅ hlr₅ hp.out_fit (by rw [hp.wr]; simp)
    (hp.out_sc.sub_right (Region.sub_prefix (by decide))))
    fun s' ⟨xv, hxl, hxv, bytes, ret, saved, sp, m, Wm, Om⟩ => ⟨⟨saved, sp, m, Wm, Om⟩, ?_⟩
  -- The specification.
  have hlen : (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r2) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
    rw [length_bytesAt]; omega_arith
  have hb0 : (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r2) (1 + 2 * c.C.len)).head? = some (s₀.mem (ptr s₀ .r2)) := by
    rw [peer_bytes]; rfl
  have hxs : ofBytes (((Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r2) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
      sv c (ptr s₀ .r3) s₃ E := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _), x₃,
      bytesAt_keep W₂ (hpsc.sub_left (Offset.sub_base _ (by omega_arith))) (by omega_arith) (by omega_arith)]
  have hys : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r2) (1 + 2 * c.C.len)).drop (c.C.len + 1)) =
      sv c (ptr s₀ .r3) s₃ QY := by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _), y₃,
      bytesAt_keep W₂ (hpsc.sub_left (Offset.sub_base _ (by omega_arith))) (by omega_arith) (by omega_arith)]
  have hP' : ∀ h : Ecdh.Valid c.C (s₀.mem (ptr s₀ .r2)) (sv c (ptr s₀ .r3) s₃ E) (sv c (ptr s₀ .r3) s₃ QY),
      peerPt c (s₀.mem (ptr s₀ .r2) = 4) (sv c (ptr s₀ .r3) s₃ E) (sv c (ptr s₀ .r3) s₃ QY) =
        .affine ⟨_, h.2.1⟩ ⟨_, h.2.2.1⟩ := fun h => by
    unfold peerPt; rw [dite_eq_left ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩]
  have hk : sv c (ptr s₀ .r3) s₂ K = dk c s₀ := by rw [S₂.k, kv_eq (A := Args.ecdh) rfl]
  have hR := L.q
  rw [Nat.shiftRight_zero, hk] at hR
  have hxoX : Fin.ofNat c.C.p xv = tmv c.C c.n (ptr s₀ .r3) s₅ (c.sl RX) *
      tmv c.C c.n (ptr s₀ .r3) s₅ (c.sl RZ) ^ (c.C.p - 2) := by rw [hxv, L.acc]
  have hspec := exchange_eq hC hlen hb0 hxs hys hP' hR hxl hxoX
  have hD₅ : sv c (ptr s₀ .r3) s₅ D = dk c s₀ := by
    rw [e₅ (by decide) (by decide) (by decide), e₄ (by decide) (by decide) (by decide),
      e₃ (by decide) (by decide) (by decide), S₂.d, dv_eq (A := Args.ecdh) rfl]
  have hz : tmv c.C c.n (ptr s₀ .r3) s₅ (c.sl RZ) ≠ 0 ↔ sv c (ptr s₀ .r3) s₅ RZ ≠ 0 :=
    not_congr (toM_eq_zero_iff hpR L.rz_lt)
  unfold EPost
  rw [hspec]
  by_cases hcond : (1 ≤ dk c s₀ ∧ dk c s₀ < c.C.n) ∧
      Ecdh.Valid c.C (s₀.mem (ptr s₀ .r2)) (sv c (ptr s₀ .r3) s₃ E) (sv c (ptr s₀ .r3) s₃ QY) ∧
      tmv c.C c.n (ptr s₀ .r3) s₅ (c.sl RZ) ≠ 0
  · have hok : ok c (ptr s₀ .r3) s₅ (PeerOk c (ptr s₀ .r3) s₃ ((s₀.mem (ptr s₀ .r2) = 4 ∧
        sv c (ptr s₀ .r3) s₃ E < c.C.p) ∧ sv c (ptr s₀ .r3) s₃ QY < c.C.p)) = true := by
      refine decide_eq_true ⟨⟨⟨⟨⟨hcond.2.1.1, hcond.2.1.2.1⟩, hcond.2.1.2.2.1⟩, hcond.2.1.2.2.2⟩, ?_, ?_⟩,
        hz.mp hcond.2.2⟩
      · rw [hD₅]; exact hcond.1.1
      · rw [hD₅]; exact hcond.1.2
    rw [ite_eq_left hcond]
    exact ⟨by rw [ret, hok]; rfl, by rw [bytes, hok]; rfl⟩
  · have hok : ok c (ptr s₀ .r3) s₅ (PeerOk c (ptr s₀ .r3) s₃ ((s₀.mem (ptr s₀ .r2) = 4 ∧
        sv c (ptr s₀ .r3) s₃ E < c.C.p) ∧ sv c (ptr s₀ .r3) s₃ QY < c.C.p)) = false := by
      refine decide_eq_false fun h => hcond ⟨⟨?_, ?_⟩, ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2⟩,
        hz.mpr h.2⟩
      · rw [← hD₅]; exact h.1.2.1
      · rw [← hD₅]; exact h.1.2.2
    rw [ite_eq_right hcond]
    exact ⟨by rw [ret, hok]; rfl, by rw [bytes, hok]; rfl⟩

end VG.Proof.Ecdh.Arm
