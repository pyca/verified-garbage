import VerifiedGarbage.Proof.Ecdh.X86_64.MulOk
import VerifiedGarbage.Proof.Ecdh.Exchange
import VerifiedGarbage.Proof.Weierstrass.X86_64.Rep

/-!
# ECDH on x86-64: the result, and the whole function

## `x`, the checks and the result

`middle` computes `x = X Z^(p-2)` from `X` and the power in `ACC`, left
Montgomery's form by a multiplication by 1, ands the masks of `d ∈ [1, n-1]`
and `Z ≠ 0` into the flag, and writes `x` or zeros (`middle_ok`); `finish`
writes the result as the signature's does (`ecFinish_ok`).
-/

namespace VG.Proof.Ecdh.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

variable {c : Cfg}

theorem finish_eq (c : Cfg) : Impl.Ecdh.X86_64.Cfg.finish c =
    ([.mov .rcx (.mem (sc (c.sl FLAG)))] : List Instr) ++ (storeBytes c.C.len c.n .rsi 0 (c.sl X) ++
    (([.mov .rax (.reg .rcx), .alu .and .rax (.imm 1)] : List Instr) ++
    Spill.restoreCode .rdi Cfg.saved)) := by
  simp only [Impl.Ecdh.X86_64.Cfg.finish, List.append_assoc]; rfl

/-- `x` or zeros, the return value and the callee-saved registers. -/
theorem ecFinish_ok (hc : BaseCfgOk c) {base : Addr} {s : State} (hs : Scr s base size) {out : Addr}
    (hrsi : s.gpr .rsi = out) (hw : (⟨out, c.C.len⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨out, c.C.len⟩ ⟨base, size⟩) (hfit : out.toNat + c.C.len ≤ 2 ^ 64)
    {g : Reg → BitVec 64} (hsv : Spill.Saved s.mem base g Cfg.saved) (b : Bool)
    (hf : word s.mem base (c.sl FLAG) = if b then BitVec.allOnes 64 else 0) :
    WP isa (.block (Impl.Ecdh.X86_64.Cfg.finish c)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem out c.C.len =
        (if b then toBytes c.C.len (sv c base s X) else List.replicate c.C.len 0) ∧
      (s'.gpr .rax).setWidth 32 = (if b then 1 else 0) ∧
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = g r) := by
  have h7 := hc.n10
  have hn0 := hc.n0
  have := hc.len8; have := hc.len_lo; have := hc.len_hi
  have hn := hs.nowrap
  have hX := sl_le c h7 (i := X) (by decide)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  have h0 : ∀ e, out + BitVec.ofNat 64 0 + BitVec.ofNat 64 e = out + BitVec.ofNat 64 e := fun e =>
    congrArg (· + BitVec.ofNat 64 e) (BitVec.add_zero out)
  rw [finish_eq, WP.block_append_iff]
  refine WP.mono (movRcx_mem_ok hs (d := c.sl FLAG) (by omega)) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  have hrsi₁ : s₁.gpr .rsi = out := by rw [k₁.1 _ (by decide), hrsi]
  rw [WP.block_append_iff]
  refine WP.mono (storeBytes_ok hs₁ (dst := .rsi) (d := 0) (a := c.sl X) (by decide) (by decide) b
    (by rw [e₁, hf]) hX (by omega) hc.len_lo hc.len_hi (by rw [hrsi₁, BitVec.add_zero]; exact hfit)
    (fun e m he => ⟨_, by rw [k₁.2.2.2]; exact hw, by
      rw [hrsi₁, h0]; exact Offset.contains_base out (by omega) (by omega)⟩)
    (by rw [hrsi₁, BitVec.add_zero]; exact (hd.symm.sub_left (Offset.sub_base base hX))))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  rw [hrsi₁, BitVec.add_zero] at e₂ O₂
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have U₂ := O₂.unch_far hd.symm
  have hrcx₂ : s₂.gpr .rcx = if b then BitVec.allOnes 64 else 0 := by
    rw [k₂.gpr _ (by decide), e₁, hf]
  rw [WP.block_append_iff]
  refine WP.mono (raxBit_ok s₂) fun s₃ ⟨e₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have hsv₃ : Spill.Saved s₃.mem base g Cfg.saved := by
    rw [k₃.2.1]
    have h48 : ∀ w ∈ [(size, 2 ^ 64)], 48 ≤ w.1 := fun w hw => by
      simp only [List.mem_singleton] at hw; subst hw; decide
    exact Saved.unch (hm₁ ▸ hsv) h48 U₂
  refine WP.mono (Spill.restore_ok .rdi Cfg.saved g s₃ (by decide) (fun p hp => ?_)
    (by rw [hs₃.rdi]; exact hsv₃)) fun s₄ ⟨g₄, r₄, m₄, _, _⟩ => ?_
  · have := saved_lt p hp
    rw [hs₃.rdi]; exact ⟨_, List.mem_append_right _ hs₃.wr, hs₃.contains (by have : size = 8192 := rfl; omega) (by decide)⟩
  refine ⟨?_, ?_, g₄⟩
  · rw [m₄, k₃.2.1, e₂, hm₁]
  · have hra : Reg.rax ∉ Cfg.saved.map Prod.fst := by decide
    rw [r₄ _ hra, e₃, hrcx₂, mask_bit]

theorem middle_eq (c : Cfg) : Impl.Ecdh.X86_64.Cfg.middle c =
    .seq (.block (Impl.Mont.X86_64.mul c.MP' (c.sl XM) (c.sl RX) (c.sl ACC)))
    (.seq (.block (Impl.Mont.X86_64.mul c.MP' (c.sl X) (c.sl XM) (c.sl ONE)))
    (.block (c.checkRange (c.sl D) ++ c.checkNonzero (c.sl RZ) ++ Impl.Ecdh.X86_64.Cfg.finish c))) := rfl

/-- Whether the result is a shared secret: the peer's key (`V`), `d` in
`[1, n-1]`, and `Z ≠ 0`. -/
abbrev ok (c : Cfg) (base : Addr) (s : State) (V : Prop) [Decidable V] : Bool :=
  decide ((V ∧ 0 < sv c base s D ∧ sv c base s D < c.C.n) ∧ sv c base s RZ ≠ 0)

/-- `x`, the checks of `d` and `Z`, and the result. -/
theorem middle_ok (hc : BaseCfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (F : Fixed c base g s.mem) (hacc : sv c base s ACC < c.C.p)
    {V : Prop} [Decidable V] (hflag : word s.mem base (c.sl FLAG) = mask V) {out : Addr}
    (hrsi : s.gpr .rsi = out) (hw : (⟨out, c.C.len⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨out, c.C.len⟩ ⟨base, size⟩) (hfit : out.toNat + c.C.len ≤ 2 ^ 64) :
    WP isa (Impl.Ecdh.X86_64.Cfg.middle c) s fun s' => ∃ xv, xv < c.C.p ∧
      Fin.ofNat c.C.p xv =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) ∧
      Spec.Ecdsa.bytesAt s'.mem out c.C.len =
        (if ok c base s V then toBytes c.C.len xv else List.replicate c.C.len 0) ∧
      (s'.gpr .rax).setWidth 32 = (if ok c base s V then 1 else 0) ∧
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = g r) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hf : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega
  rw [middle_eq]
  have hM := modP_of hc F.mp
  have hone : sv c base s ONE = 1 := F.one
  -- `XM = X · ACC`.
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) (MP'_tmp c) (MP'_mo c) h7 hs hM (o := XM) (a := RX) (b := ACC) (by decide)
    (by decide) (by decide) (by decide) hacc) fun s₁ ⟨k₁, _, e₁⟩ => ?_)
  have hs₁ := k₁.scr hs
  have kP₁ := hM.keep (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  have v₁ : ∀ {i}, i < 45 → i ≠ XM → i ≠ TMP → sv c base s₁ i = sv c base s i := fun hi h₁ h₂ =>
    sv_keep (MP'_n c) rfl h7 hn k₁ hi h₁ h₂
  -- `X = XM · 1`.
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) (MP'_tmp c) (MP'_mo c) h7 hs₁ kP₁ (o := X) (a := XM) (b := ONE) (by decide)
    (by decide) (by decide) (by decide) (by rw [v₁ (by decide) (by decide) (by decide), hone]; omega))
    fun s₂ ⟨k₂, lt₂, e₂⟩ => ?_)
  have hs₂ := k₂.scr hs₁
  have v₂ : ∀ {i}, i < 45 → i ≠ XM → i ≠ X → i ≠ TMP → sv c base s₂ i = sv c base s i := fun hi h₁ h₂ h₃ =>
    (sv_keep (MP'_n c) rfl h7 hn k₂ hi h₂ h₃).trans (v₁ hi h₁ h₃)
  have x₂ : Fin.ofNat c.C.p (sv c base s₂ X) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) := by
    rw [toM_one_mul hpR (by rw [e₂, v₁ (i := ONE) (by decide) (by decide) (by decide), hone]),
      toM_mul hpR e₁]
  have U₂ : Unch base (slW c [XM, X, TMP]) s.mem s₂.mem :=
    ((unch_slots (MP'_n c) rfl k₁.unch (l := [XM, X, TMP]) (by simp) (by simp)).trans
      (unch_slots (MP'_n c) rfl k₂.unch (l := [XM, X, TMP]) (by simp) (by simp))).mono
      fun w hw => by simp only [List.mem_append, or_self] at hw; exact hw
  have F₂ := F.unch h7 hn (fixedOk_slW (l := [XM, X, TMP]) (by decide)) U₂
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (checkRange_ok c hs₂ h0 (sl_le c h7 (i := D) (by decide)) (sl_le c h7 (i := MN) (by decide))
    hf) fun s₅ ⟨f₅, k₅, O₅⟩ => ?_
  have hs₅ := hs₂.of_keepRegs k₅ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (checkNonzero_ok c hs₅ h0 (sl_le c h7 (i := RZ) (by decide)) hf) fun s₆ ⟨f₆, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_keepRegs k₆ (by decide)
  have F₆ := (F₂.unch h7 hn fixedOk_flag O₅.unch).unch h7 hn fixedOk_flag O₆.unch
  have hflag₆ : word s₆.mem base (c.sl FLAG) = if ok c base s V then BitVec.allOnes 64 else 0 := by
    have hMN : wordsVal s₂.mem base (c.sl MN) c.n = c.C.n := F₂.mn
    have z₂ : wordsVal s₂.mem base (c.sl RZ) c.n = sv c base s RZ := v₂ (by decide) (by decide) (by decide) (by decide)
    have d₂ : wordsVal s₂.mem base (c.sl D) c.n = sv c base s D := v₂ (by decide) (by decide) (by decide) (by decide)
    rw [f₆, f₅, flag_unch U₂ h7 h0 hn (by decide), hflag, sv_flag O₅ h0 h7 hn (i := RZ) (by decide)
      (by decide), hMN, z₂, d₂, mask_and, mask_and]
    simp only [mask, decide_eq_true_eq, and_assoc]
  have hrsi₆ : s₆.gpr .rsi = out := by
    rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), k₂.gpr _ (rsi_not_clob _),
      k₁.gpr _ (rsi_not_clob _), hrsi]
  have hw₆ : (⟨out, c.C.len⟩ : Region) ∈ s₆.wr := by rw [k₆.wr, k₅.wr, k₂.wr, k₁.wr]; exact hw
  refine WP.mono (ecFinish_ok hc hs₆ hrsi₆ hw₆ hd hfit F₆.saved _ hflag₆) fun s' ⟨bytes, rax, saved⟩ =>
    ⟨_, lt₂, x₂, ?_, rax, saved⟩
  have x₆ : sv c base s₆ X = sv c base s₂ X := (sv_flag O₆ h0 h7 hn (i := X) (by decide) (by decide)).trans
    (sv_flag O₅ h0 h7 hn (i := X) (by decide) (by decide))
  rw [bytes, x₆]

end VG.Proof.Ecdh.X86_64

/-!
## The whole function

`exchangeWith_ok`: `Cfg.exchangeWith c mq` computes the specification's
shared secret of `d` and the peer's public key, for any curve the ECDSA proof
supports (`CfgOk`) and any scalar multiplication `mq` that computes `[d]P`
(`MulOk`, writing only areas `W` that keep what the rest reads: `MulW`), and
restores the callee-saved registers; `exchange_ok` is `Cfg.exchange`'s, by
the window method or the ladder (`mulQ_ok`).

After `args`, the signature's setup and tables (`stage₁`, whose `SetupPre`
the arguments meet as they are) read `d` and the peer's `x`; then `peer_ok`,
`validate_ok`, `mq` and the power, and `middle_ok`; `exchange_eq` connects
what they compute to the specification.
-/

namespace VG.Proof.Ecdh.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64
open VG.Proof.X25519.X86_64 (Keeps)
open VG.Impl.Ecdh.X86_64 (QY R2P BP QXM QYM W0 W1 W2 W3 PX PY)

variable {c : Cfg}

/-- The arguments: `out = rdi` (`len` bytes), `d = rsi` (`len` bytes),
`peer = rdx` (`1 + 2 len` bytes) and `scratch = rcx`, readable and writable
as the contract says and apart from each other as it says. -/
structure EPre (c : Cfg) (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .rsi, c.C.len⟩, ⟨s.gpr .rdx, 1 + 2 * c.C.len⟩]
  wr : s.wr = [⟨s.gpr .rdi, c.C.len⟩, ⟨s.gpr .rcx, size⟩]
  out_sc : Region.Disjoint ⟨s.gpr .rdi, c.C.len⟩ ⟨s.gpr .rcx, size⟩
  d_sc : Region.Disjoint ⟨s.gpr .rsi, c.C.len⟩ ⟨s.gpr .rcx, size⟩
  peer_sc : Region.Disjoint ⟨s.gpr .rdx, 1 + 2 * c.C.len⟩ ⟨s.gpr .rcx, size⟩
  out_fit : (s.gpr .rdi).toNat + c.C.len ≤ 2 ^ 64
  sc_fit : (s.gpr .rcx).toNat + size ≤ 2 ^ 64

/-- The private key. -/
abbrev dk (c : Cfg) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rsi) c.C.len)

/-- The result the contract asks for: the specification's shared secret, and
`1`, or zeros and `0`. -/
def EPost (c : Cfg) (s₀ s' : State) : Prop :=
  match Spec.Ecdh.exchange c.C (dk c s₀) (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdx) (1 + 2 * c.C.len)) with
  | some z => (s'.gpr .rax).setWidth 32 = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (s₀.gpr .rdi) c.C.len = z
  | none => (s'.gpr .rax).setWidth 32 = 0 ∧
      Spec.Ecdsa.bytesAt s'.mem (s₀.gpr .rdi) c.C.len = List.replicate c.C.len 0

theorem args_ok (s : State) :
    WP isa (.block Impl.Ecdh.X86_64.Cfg.args) s fun s' =>
      s'.gpr .r8 = s.gpr .rcx ∧ s'.gpr .r9 = s.gpr .rdx ∧ s'.gpr .rcx = s.gpr .rsi ∧
        s'.gpr .rdx = s.gpr .rdx + BitVec.ofNat 64 1 ∧ Keeps [.r8, .r9, .rcx, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Ecdh.X86_64.Cfg.args, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true,
    reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, by rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- The point the ladder multiplies: the peer's, if its key is valid as the
code checks it, else `G`. -/
def peerPt (c : Cfg) (b4 : Prop) [Decidable b4] (x y : Nat) : Point c.C :=
  if h : ((b4 ∧ x < c.C.p) ∧ y < c.C.p) ∧ OnCurve c (Fin.ofNat c.C.p x) (Fin.ofNat c.C.p y) then .affine ⟨x, h.1.1.2⟩ ⟨y, h.1.2⟩ else G c.C

theorem peerPt_onCurve (hc : BaseCfgOk c) (b4 : Prop) [Decidable b4] (x y : Nat) :
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
theorem peer_bytes (m : Mem) (p : Addr) (len : Nat) :
    Spec.Ecdsa.bytesAt m p (1 + 2 * len) = m p :: (Spec.Ecdsa.bytesAt m (p + BitVec.ofNat 64 1) len ++
      Spec.Ecdsa.bytesAt m (p + BitVec.ofNat 64 (1 + len)) len) := by
  have h1 : Spec.Ecdsa.bytesAt m p 1 = [m p] := by
    simp only [Spec.Ecdsa.bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero]
  rw [show 1 + 2 * len = 1 + (len + len) by omega, bytesAt_add, bytesAt_add, h1, BitVec.add_assoc,
    BitVec.ofNat_add_ofNat]
  rfl

/-- `exchange_eq_of_lt`, for `R` that represents `[d]P` only for `d` in `[1, n-1]`. -/
theorem exchange_eq_of_range {C : Curve} (hC : Law C) {d : Nat} {bs : List Byte}
    (hlen : bs.length = 2 * C.len + 1) {b0 : Byte} (hb0 : bs.head? = some b0) {x y : Nat}
    (hxv : ofBytes ((bs.drop 1).take C.len) = x) (hyv : ofBytes (bs.drop (C.len + 1)) = y) {P : Point C}
    (hP : ∀ h : Ecdh.Valid C b0 x y, P = .affine ⟨x, h.2.1⟩ ⟨y, h.2.2.1⟩)
    {X Y Z : Fe C} (hR : 1 ≤ d → d < C.n → Rep C X Y Z (mul d P)) {xo : Nat} (hxo : xo < C.p)
    (hxoX : Fin.ofNat C.p xo = X * Z ^ (C.p - 2)) :
    Spec.Ecdh.exchange C d bs =
      if (1 ≤ d ∧ d < C.n) ∧ Ecdh.Valid C b0 x y ∧ Z ≠ 0 then some (toBytes C.len xo) else none := by
  by_cases hd : 1 ≤ d
  · exact exchange_eq_of_lt hC hlen hb0 hxv hyv hP (hR hd) hxo hxoX
  · unfold Spec.Ecdh.exchange
    simp only [hd, false_and, ite_false]

theorem exchangeWith_eq' (c : Cfg) (mq : Prog isa) : Impl.Ecdh.X86_64.Cfg.exchangeWith c mq =
    .seq (.block Impl.Ecdh.X86_64.Cfg.args) (.seq (.seq (.block (c.setupWith none))
      (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) (.seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n))
      (.seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) (.block [])))))
    (.seq (.block (Impl.Ecdh.X86_64.Cfg.peer c)) (.seq (Impl.Ecdh.X86_64.Cfg.validate c)
    (.seq mq (.seq c.pPow (Impl.Ecdh.X86_64.Cfg.middle c)))))) := rfl

/-- `vg_ecdh_<curve>`, with a scalar multiplication `mq` computing `[d]P`
(`MulOk`) and writing only `W` (`MulW`), computes the specification's shared
secret and restores the callee-saved registers. -/
theorem exchangeWith_ok (hc : BaseCfgOk c) (hC : Law c.C) {mq : Prog isa} {W : List (Nat × Nat)}
    (hmq : MulOk c mq W) (hW : MulW c W) {s₀ : State} (hp : EPre c s₀) :
    WP isa (Impl.Ecdh.X86_64.Cfg.exchangeWith c mq) s₀ fun s' =>
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s₀.gpr r) ∧ EPost c s₀ s' := by
  have h0 := hc.n0
  have h7 := hc.n10
  have := hc.len8; have := hc.len_lo; have := hc.len_hi
  have hsz : size = 8192 := rfl
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  rw [exchangeWith_eq']
  refine WP.seq (WP.mono (args_ok s₀) fun s₁ ⟨r8₁, r9₁, rcx₁, rdx₁, k₁⟩ => ?_)
  have rsi₁ : s₁.gpr .rsi = s₀.gpr .rsi := k₁.1 _ (by decide)
  have rdi₁ : s₁.gpr .rdi = s₀.gpr .rdi := k₁.1 _ (by decide)
  have hrd₁ : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [k₁.2.2.1, k₁.2.2.2]
  have hsp : SetupPre c s₁ := by
    refine ⟨by rw [k₁.2.2.2, hp.wr, r8₁]; simp, fun e he => ?_, fun e he => ?_, fun e he => ?_, ?_, ?_, ?_,
      by rw [r8₁]; exact hp.sc_fit⟩
    · rw [rcx₁, hrd₁, hp.rd]
      exact ⟨_, by simp, Offset.contains_base _ he (by have := hp.out_fit; omega)⟩
    · rw [rsi₁, hrd₁, hp.rd]
      exact ⟨_, by simp, Offset.contains_base _ he (by have := hp.out_fit; omega)⟩
    · rw [rdx₁, hrd₁, hp.rd, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact ⟨⟨s₀.gpr .rdx, 1 + 2 * c.C.len⟩, by simp,
        Offset.contains_base _ (by omega) (by have := hp.out_fit; omega)⟩
    · rw [rsi₁, r8₁]; exact hp.d_sc
    · rw [rdx₁, r8₁]; exact hp.peer_sc.sub_left (Offset.sub_base _ (by omega))
    · rw [rcx₁, r8₁]; exact hp.d_sc
  refine WP.seq (WP.mono (stage₁ hc (hs := none) (Or.inl rfl) hsp (rest := .block [])
    (Q := St₁ c none s₁ (s₁.gpr .r8))
    fun _ S => WP.block_nil S) fun s₂ S₂ => ?_)
  rw [r8₁] at S₂
  have hn := S₂.scr.nowrap
  have hq₂ : s₂.gpr .r9 = s₀.gpr .rdx := by rw [S₂.gpr _ (by decide), r9₁]
  have hrw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [S₂.rd, S₂.wr, hrd₁]
  -- The peer's key.
  refine WP.seq (WP.mono (peer_ok hc S₂.scr hq₂ (by rw [hrw₂, hp.rd]; simp) hp.peer_sc S₂.fixed.mp)
    fun s₃ ⟨hs₃, k₃, U₃, r2₃, bp₃, y₃, f₃⟩ => ?_)
  have F₃ := S₂.fixed.unch h7 hn ((fixedOk_slW (l := [R2P, BP, QY]) (by decide)).append fixedOk_flag) U₃
  have e₃ : ∀ {i}, i < 45 → i ∉ [R2P, BP, QY] → i ≠ FLAG →
      sv c (s₀.gpr .rcx) s₃ i = sv c (s₀.gpr .rcx) s₂ i := fun hi hl hf =>
    sv_unch U₃ h7 hn hi (apart_append (apart_slW hl) (apart_flag h0 hf))
  have x₃ : sv c (s₀.gpr .rcx) s₃ E = sv c (s₀.gpr .rcx) s₂ E := e₃ (by decide) (by decide) (by decide)
  -- The peer's key has not changed.
  have W₂ : Outside (s₀.gpr .rcx) 0 size s₀.mem s₂.mem := fun x hx =>
    (S₂.unch x fun w hw => by rw [List.mem_singleton.mp hw]; exact hx).trans (congrFun k₁.2.1 x)
  have hq0 : s₂.mem (s₀.gpr .rdx) = s₀.mem (s₀.gpr .rdx) := by
    have := keep_of_disjoint' W₂ hp.peer_sc (by omega) (i := 0) (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  -- What the code checks of the peer's key so far.
  have hf₃ : word s₃.mem (s₀.gpr .rcx) (c.sl FLAG) = mask (((s₀.mem (s₀.gpr .rdx) = 4 ∧
      sv c (s₀.gpr .rcx) s₃ E < c.C.p) ∧ sv c (s₀.gpr .rcx) s₃ QY < c.C.p)) := by
    rw [f₃, S₂.flag, BitVec.allOnes_and, mask_and, mask_and, x₃, hq0]
  refine WP.seq (WP.mono (validate_ok hc hs₃ F₃ r2₃ bp₃ hf₃)
    fun s₄ ⟨hs₄, g₄, rd₄, wr₄, U₄, f₄, px_lt, py_lt, px, py⟩ => ?_)
  have F₄ := F₃.unch h7 hn ((fixedOk_slW (l := [QXM, QYM, TMP, W0, W1, W2, W3, PY]) (by decide)).append
    fixedOk_flag) U₄
  have e₄ : ∀ {i}, i < 45 → i ∉ [QXM, QYM, TMP, W0, W1, W2, W3, PY] → i ≠ FLAG →
      sv c (s₀.gpr .rcx) s₄ i = sv c (s₀.gpr .rcx) s₃ i := fun hi hl hf =>
    sv_unch U₄ h7 hn hi (apart_append (apart_slW hl) (apart_flag h0 hf))
  have t₄ : ∀ {j}, j < 3 → ∀ t < 64 * c.n,
      s₄.mem (off (s₀.gpr .rcx) (bitsAt c.n j + t)) = s₂.mem (off (s₀.gpr .rcx) (bitsAt c.n j + t)) :=
    fun hj t ht => by
      rw [tbl_unch U₄ h7 hn hj ht (apart_append (tbl_apart_slW (by decide) _ t) (tbl_apart_flag h0 _ t)),
        tbl_unch U₃ h7 hn hj ht (apart_append (tbl_apart_slW (by decide) _ t) (tbl_apart_flag h0 _ t))]
  have hpk : sv c (s₀.gpr .rcx) s₂ K < 2 ^ (64 * c.n) := wordsVal_lt _ _ _ _
  have hk₄ : sv c (s₀.gpr .rcx) s₄ K = sv c (s₀.gpr .rcx) s₂ K := by
    rw [e₄ (by decide) (by decide) (by decide), e₃ (by decide) (by decide) (by decide)]
  -- `[d]P`, then `Z^(p-2)`.
  refine hmq hs₄ F₄
    (by rw [e₄ (by decide) (by decide) (by decide)]; exact bp₃)
    (peerPt_onCurve hc _ _ _) px_lt py_lt
    (peerPt_rep hC _ _ _ px py |> fun h => by
      show Rep c.C (toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .rcx) s₄ PX))
        (toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .rcx) s₄ PY))
        (toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₄.mem (s₀.gpr .rcx) (c.sl ONEP) c.n)) _
      rw [F₄.onep, toM_one hpR]; exact h)
    (by rw [e₄ (by decide) (by decide) (by decide), e₃ (by decide) (by decide) (by decide)]; exact S₂.rx)
    (by rw [e₄ (by decide) (by decide) (by decide), e₃ (by decide) (by decide) (by decide)]; exact S₂.ry)
    (by rw [e₄ (by decide) (by decide) (by decide), e₃ (by decide) (by decide) (by decide)]; exact S₂.rz)
    hk₄
    (by rw [S₂.k]; exact ofBytes_bytesAt_lt _ _ _)
    (fun t ht => by rw [t₄ (j := 0) (by decide) t ht, S₂.t₀ t ht, S₂.k])
    (fun t ht => by rw [t₄ (j := 1) (by decide) t ht, S₂.t₁ t ht]) fun s₅ L => ?_
  have hs₅ := L.scr
  have F₅ := F₄.unch h7 hn hW.fixed L.unch
  have d₅ : sv c (s₀.gpr .rcx) s₅ D = sv c (s₀.gpr .rcx) s₄ D := sv_unch L.unch h7 hn (by decide) hW.d
  have hflag₅ := f₄
  have hF := sl_le c h7 (i := FLAG) (by decide)
  rw [← L.unch.word hW.flag (by omega)] at hflag₅
  have hrsi₅ : s₅.gpr .rsi = s₀.gpr .rdi := by
    rw [L.rsi, g₄ _ (rsi_not_clob _), k₃.gpr _ (by decide), S₂.rsi, rdi₁]
  have hw₅ : (⟨s₀.gpr .rdi, c.C.len⟩ : Region) ∈ s₅.wr := by
    rw [L.wr, wr₄, k₃.wr, S₂.wr, k₁.2.2.2, hp.wr]; simp
  refine WP.mono (middle_ok hc hs₅ F₅ L.acc_lt hflag₅ hrsi₅ hw₅ hp.out_sc hp.out_fit)
    fun s' ⟨xv, hxl, hxv, bytes, rax, saved⟩ => ⟨fun r hr => ?_, ?_⟩
  · have hsv : ∀ r ∈ Cfg.saved.map Prod.fst, r ∉ [Reg.r8, .r9, .rcx, .rdx] := by decide
    rw [saved r hr, k₁.1 r (hsv r hr)]
  -- The specification.
  have hlen : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdx) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
    rw [length_bytesAt]; omega
  have hb0 : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdx) (1 + 2 * c.C.len)).head? = some (s₀.mem (s₀.gpr .rdx)) := by
    rw [peer_bytes]; rfl
  have hxs : ofBytes (((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdx) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
      sv c (s₀.gpr .rcx) s₃ E := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _), x₃, S₂.e]
    simp only [k₁.2.1, rdx₁, shAt_none, Nat.shiftRight_zero]
  have hys : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdx) (1 + 2 * c.C.len)).drop (c.C.len + 1)) =
      sv c (s₀.gpr .rcx) s₃ QY := by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _), y₃,
      bytesAt_keep W₂ (hp.peer_sc.sub_left (Offset.sub_base _ (by omega))) (by omega) (by omega)]
  have hP' : ∀ h : Ecdh.Valid c.C (s₀.mem (s₀.gpr .rdx)) (sv c (s₀.gpr .rcx) s₃ E) (sv c (s₀.gpr .rcx) s₃ QY),
      peerPt c (s₀.mem (s₀.gpr .rdx) = 4) (sv c (s₀.gpr .rcx) s₃ E) (sv c (s₀.gpr .rcx) s₃ QY) =
        .affine ⟨_, h.2.1⟩ ⟨_, h.2.2.1⟩ := fun h => by
    unfold peerPt; rw [dite_eq_left ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩]
  have hk : sv c (s₀.gpr .rcx) s₂ K = dk c s₀ := by rw [S₂.k]; simp only [kv, dk, k₁.2.1, rcx₁]
  have hR := fun (h1 : 1 ≤ sv c (s₀.gpr .rcx) s₂ K) (hd : sv c (s₀.gpr .rcx) s₂ K < c.C.n) => L.q h1 hd
  rw [hk] at hR
  have hxoX : Fin.ofNat c.C.p xv = tmv c.C c.n (s₀.gpr .rcx) s₅ (c.sl RX) *
      tmv c.C c.n (s₀.gpr .rcx) s₅ (c.sl RZ) ^ (c.C.p - 2) := by rw [hxv, L.acc]
  have hspec := exchange_eq_of_range hC hlen hb0 hxs hys hP' hR hxl hxoX
  have hD₅ : sv c (s₀.gpr .rcx) s₅ D = dk c s₀ := by
    rw [d₅, e₄ (by decide) (by decide) (by decide),
      e₃ (by decide) (by decide) (by decide), S₂.d, shAt_none, Nat.shiftRight_zero]
    simp only [dv, dk, k₁.2.1, rsi₁]
  have hz : tmv c.C c.n (s₀.gpr .rcx) s₅ (c.sl RZ) ≠ 0 ↔ sv c (s₀.gpr .rcx) s₅ RZ ≠ 0 :=
    not_congr (toM_eq_zero_iff hpR L.rz_lt)
  unfold EPost
  rw [hspec]
  by_cases hcond : (1 ≤ dk c s₀ ∧ dk c s₀ < c.C.n) ∧
      Ecdh.Valid c.C (s₀.mem (s₀.gpr .rdx)) (sv c (s₀.gpr .rcx) s₃ E) (sv c (s₀.gpr .rcx) s₃ QY) ∧
      tmv c.C c.n (s₀.gpr .rcx) s₅ (c.sl RZ) ≠ 0
  · have hok : ok c (s₀.gpr .rcx) s₅ (PeerOk c (s₀.gpr .rcx) s₃ ((s₀.mem (s₀.gpr .rdx) = 4 ∧
        sv c (s₀.gpr .rcx) s₃ E < c.C.p) ∧ sv c (s₀.gpr .rcx) s₃ QY < c.C.p)) = true := by
      refine decide_eq_true ⟨⟨⟨⟨⟨hcond.2.1.1, hcond.2.1.2.1⟩, hcond.2.1.2.2.1⟩, hcond.2.1.2.2.2⟩, ?_, ?_⟩,
        hz.mp hcond.2.2⟩
      · rw [hD₅]; exact hcond.1.1
      · rw [hD₅]; exact hcond.1.2
    rw [ite_eq_left hcond]
    exact ⟨by rw [rax, hok]; rfl, by rw [bytes, hok]; rfl⟩
  · have hok : ok c (s₀.gpr .rcx) s₅ (PeerOk c (s₀.gpr .rcx) s₃ ((s₀.mem (s₀.gpr .rdx) = 4 ∧
        sv c (s₀.gpr .rcx) s₃ E < c.C.p) ∧ sv c (s₀.gpr .rcx) s₃ QY < c.C.p)) = false := by
      refine decide_eq_false fun h => hcond ⟨⟨?_, ?_⟩, ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2⟩,
        hz.mpr h.2⟩
      · rw [← hD₅]; exact h.1.2.1
      · rw [← hD₅]; exact h.1.2.2
    rw [ite_eq_right hcond]
    exact ⟨by rw [rax, hok]; rfl, by rw [bytes, hok]; rfl⟩

/-- `vg_ecdh_<curve>`, by the window method or the ladder (`mulQ_ok`). -/
theorem exchange_ok (hc : BaseCfgOk c) (hC : Law c.C) {s₀ : State} (hp : EPre c s₀) :
    WP isa (Impl.Ecdh.X86_64.Cfg.exchange c) s₀ fun s' =>
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s₀.gpr r) ∧ EPost c s₀ s' :=
  exchangeWith_ok hc hC (mulQ_ok hc hC) (mulQ_w hc) hp

end VG.Proof.Ecdh.X86_64
