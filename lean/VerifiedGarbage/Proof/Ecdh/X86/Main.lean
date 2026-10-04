import VerifiedGarbage.Proof.Ecdh.X86.Validate
import VerifiedGarbage.Proof.Ecdh.Exchange

/-!
# ECDH on x86 (32-bit): the result, and the whole function

As on AArch64 (`Proof/Ecdh/AArch64/Main.lean`).

## `x`, the checks and the result

`middle` computes `x = X Z^(p-2)` from `X` and the power in `ACC`, left
Montgomery's form by a multiplication by 1, ands the masks of `d ∈ [1, n-1]`
and `Z ≠ 0` into the flag, and writes `x` or zeros (`middle_ok`); `finish`
writes the result as the signature's does, then the signature's tail
(`ecFinish_ok`).
-/

namespace VG.Proof.Ecdh.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86

variable {c : Cfg}

theorem finish_eq (c : Cfg) : Impl.Ecdh.X86.Cfg.finish c =
    .mov .ecx (.mem (sc (c.sl FLAG))) :: .mov .ebx (.mem (Cfg.argOp 0)) ::
    (storeBE c.n .ebx 0 (c.sl X) ++
    (([.mov .eax (.reg .ecx), .alu .and .eax (.imm 1)] : List Instr) ++ Cfg.restore)) := by
  simp only [Impl.Ecdh.X86.Cfg.finish, List.append_assoc, List.cons_append, List.nil_append]

/-- `x` or zeros, the return value and the callee-saved registers. -/
theorem ecFinish_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size) {o32 : BitVec 32}
    (hout : readSrc s (.mem (Cfg.argOp 0)) = some o32) (hofit : o32.toNat + 8 * c.n ≤ 2 ^ 32)
    (hw : (⟨o32.setWidth 64, 8 * c.n⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨o32.setWidth 64, 8 * c.n⟩ ⟨base, size⟩)
    {g : Reg → BitVec 32} (hsv : ∀ rd ∈ Cfg.saved, s.mem.readW (off base rd.2) 32 = g rd.1) (b : Bool)
    (hf : flagW c base s = mask32 (b = true)) :
    WP isa (.block (Impl.Ecdh.X86.Cfg.finish c)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem (o32.setWidth 64) (8 * c.n) =
        (if b then toBytes (8 * c.n) (sv c base s X) else List.replicate (8 * c.n) 0) ∧
      s'.gpr .eax = (if b then 1 else 0) ∧
      (∀ rd ∈ Cfg.saved, s'.gpr rd.1 = g rd.1) ∧
      (∀ r, r ∉ [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] → s'.gpr r = s.gpr r) ∧
      Outside (o32.setWidth 64) 0 (8 * c.n) s.mem s'.mem := by
  have h7 := hc.n7
  have hn0 := hc.n0
  have hn := hs.nowrap
  have hsz : size = 8192 := rfl
  have hX := sl_le c h7 (i := X) (by decide)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  generalize hout64 : o32.setWidth 64 = out at hw hd ⊢
  have h0 : ∀ e, out + BitVec.ofNat 64 0 + BitVec.ofNat 64 e = out + BitVec.ofNat 64 e := fun e =>
    congrArg (· + BitVec.ofNat 64 e) (BitVec.add_zero out)
  have h16 : ∀ rd ∈ Cfg.saved, ∀ w ∈ [(size, 2 ^ 64)], rd.2 + 4 ≤ w.1 ∨ w.1 + w.2 ≤ rd.2 :=
    fun rd hrd w hw => by
      have := saved_lt rd hrd
      simp only [List.mem_singleton] at hw; subst hw; exact .inl (by omega)
  rw [finish_eq]
  refine wp_movS (readSrc_sc hs (d := c.sl FLAG) (by omega)) fun s₁ u₁ _ => ?_
  refine wp_movS (show readSrc s₁ (.mem (Cfg.argOp 0)) = some o32 by
    have hea : s₁.ea (Cfg.argOp 0) = s.ea (Cfg.argOp 0) := by
      show addr (s₁.gpr .esp) _ = addr (s.gpr .esp) _
      rw [u₁.other _ (by decide)]
    rw [← hout]; show s₁.load32 _ = s.load32 _
    rw [State.load32, State.load32, hea, u₁.rd, u₁.wr, u₁.mem]) fun s₂ u₂ _ => ?_
  have k₂ : Keeps [.ebx, .ecx] s s₂ := (u₁.keeps.mono (by decide)).widen u₂.keeps
  have hs₂ := hs.of_keeps k₂ (by decide)
  have hm₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have hc₂ : s₂.gpr .ecx = mask32 (b = true) := by
    rw [u₂.other _ (by decide), u₁.gpr, ← flagW, hf]
  refine WP.block_append (WP.mono (storeBE_ok hs₂ (dst := .ebx) (d := 0) (a := c.sl X) (by decide) b
    hc₂ hX (by rw [u₂.gpr]; omega) (fun e he => ⟨_, by rw [k₂.2.2]; exact hw, by
      rw [u₂.gpr, hout64, h0]; exact Offset.contains_base out (by omega) (by omega)⟩)
    (by rw [u₂.gpr, hout64, BitVec.add_zero]; exact hd.symm.sub_left (Offset.sub_base base hX)))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_)
  rw [u₂.gpr, hout64, BitVec.add_zero] at e₃ O₃
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have U₃ := O₃.unch_far hd.symm
  have hsv₃ : ∀ rd ∈ Cfg.saved, s₃.mem.readW (off base rd.2) 32 = g rd.1 := fun rd hrd => by
    have := saved_lt rd hrd
    rw [Unch.readW32 U₃ (h16 rd hrd) (by omega), hm₂, hsv rd hrd]
  refine WP.mono (tail_ok hs₃ hsv₃ b (by rw [k₃.1 _ (by decide), hc₂]))
    fun s' ⟨hm', eax', saved', others'⟩ => ⟨?_, eax', saved', fun r hr => ?_, ?_⟩
  · rw [hm', e₃, hm₂]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7'⟩ := hr
    rw [others' _ (by simp [h1, h2, h4, h5, h6, h7']), k₃.1 _ (by simp [h1]), k₂.1 _ (by simp [h2, h3])]
  · rw [hm', ← hm₂]; exact O₃

theorem middle_eq (c : Cfg) : Impl.Ecdh.X86.Cfg.middle c =
    .seq (mul c.MP' c.wk (c.sl XM) (c.sl RX) (c.sl ACC))
    (.seq (mul c.MP' c.wk (c.sl X) (c.sl XM) (c.sl ONE))
    (.block (c.checkRange (c.sl D) ++ c.checkNonzero (c.sl RZ) ++ Impl.Ecdh.X86.Cfg.finish c))) := rfl

/-- Whether the result is a shared secret: the peer's key (`V`), `d` in
`[1, n-1]`, and `Z ≠ 0`. -/
abbrev ok (c : Cfg) (base : Addr) (s : State) (V : Prop) [Decidable V] : Bool :=
  decide ((V ∧ 0 < sv c base s D ∧ sv c base s D < c.C.n) ∧ sv c base s RZ ≠ 0)

/-- `x`, the checks of `d` and `Z`, and the result, from a state that
changed only the working space since `s₀`. -/
theorem middle_ok (hc : CfgOk c) {s₀ : State} {base : Addr} {s : State} (hs : Scr s base size)
    (F : Fixed c base s₀.gpr s.mem) (hacc : sv c base s ACC < c.C.p)
    {V : Prop} [Decidable V] (hflag : flagW c base s = mask32 V)
    (hwhole : Unch base [(0, size)] s₀.mem s.mem) (hesp : s.gpr .esp = s₀.gpr .esp) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hin : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ 0) 4)
    (hdarg : Region.Disjoint ⟨argAddr s₀ 0, 4⟩ ⟨base, size⟩) (hofit : (arg s₀ 0).toNat + 8 * c.n ≤ 2 ^ 32)
    (hw : (⟨ptr s₀ 0, 8 * c.n⟩ : Region) ∈ s₀.wr) (hd : Region.Disjoint ⟨ptr s₀ 0, 8 * c.n⟩ ⟨base, size⟩) :
    WP isa (Impl.Ecdh.X86.Cfg.middle c) s fun s' => ∃ xv, xv < c.C.p ∧
      Fin.ofNat c.C.p xv =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) ∧
      Spec.Ecdsa.bytesAt s'.mem (ptr s₀ 0) (8 * c.n) =
        (if ok c base s V then toBytes (8 * c.n) xv else List.replicate (8 * c.n) 0) ∧
      s'.gpr .eax = (if ok c base s V then 1 else 0) ∧
      (∀ rd ∈ Cfg.saved, s'.gpr rd.1 = s₀.gpr rd.1) ∧ s'.gpr .esp = s₀.gpr .esp ∧
      ∃ m, Unch base [(0, size)] s₀.mem m ∧ Outside (ptr s₀ 0) 0 (8 * c.n) m s'.mem := by
  have h0 := hc.n0
  have h7 := hc.n7
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hf : c.sl FLAG + 4 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega
  rw [middle_eq]
  have hM := modP_of hc F.mp
  have hone : sv c base s ONE = 1 := F.one
  -- `XM = X · ACC`.
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) (.inl rfl) rfl h7 hs hM (o := XM) (a := RX) (b := ACC) (by decide)
    (by decide) (by decide) (by decide) hacc) fun s₁ ⟨k₁, _, e₁⟩ => ?_)
  have hs₁ := k₁.scr hs
  have kP₁ := hM.keepX86 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  have v₁ : ∀ {i}, i < 45 → i ≠ XM → i ≠ TMP → sv c base s₁ i = sv c base s i := fun hi h₁ h₂ =>
    sv_keep (MP'_n c) rfl h7 hn k₁ hi h₁ h₂
  -- `X = XM · 1`.
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) (.inl rfl) rfl h7 hs₁ kP₁ (o := X) (a := XM) (b := ONE) (by decide)
    (by decide) (by decide) (by decide) (by rw [v₁ (by decide) (by decide) (by decide), hone]; omega))
    fun s₂ ⟨k₂, lt₂, e₂⟩ => ?_)
  have hs₂ := k₂.scr hs₁
  have v₂ : ∀ {i}, i < 45 → i ≠ XM → i ≠ X → i ≠ TMP → sv c base s₂ i = sv c base s i := fun hi h₁ h₂ h₃ =>
    (sv_keep (MP'_n c) rfl h7 hn k₂ hi h₂ h₃).trans (v₁ hi h₁ h₃)
  have x₂ : Fin.ofNat c.C.p (sv c base s₂ X) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) := by
    rw [toM_one_mul hpR (by rw [e₂, v₁ (i := ONE) (by decide) (by decide) (by decide), hone]),
      toM_mul hpR e₁]
  have U₂ : Unch base (slWk c [XM, X, TMP]) s.mem s₂.mem :=
    ((unch_slots (MP'_n c) rfl k₁.unch (l := [XM, X, TMP]) (by simp) (by simp)).trans
      (unch_slots (MP'_n c) rfl k₂.unch (l := [XM, X, TMP]) (by simp) (by simp))).mono
      fun w hw => by simpa only [List.mem_append, or_self] using hw
  have F₂ := F.unch h7 hn (fixedOk_slWk (l := [XM, X, TMP]) (by decide)) U₂
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (checkRange_ok c hs₂ h0 (sl_le c h7 (i := D) (by decide)) (sl_le c h7 (i := MN) (by decide))
    hf) fun s₅ ⟨f₅, k₅, O₅⟩ => ?_
  have hs₅ := hs₂.of_keeps k₅ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (checkNonzero_ok c hs₅ h0 (sl_le c h7 (i := RZ) (by decide)) hf) fun s₆ ⟨f₆, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_keeps k₆ (by decide)
  have F₆ := (F₂.unch h7 hn fixedOk_flag O₅.unch).unch h7 hn fixedOk_flag O₆.unch
  have hflag₆ : flagW c base s₆ = mask32 (ok c base s V = true) := by
    have hMN : wordsVal s₂.mem base (c.sl MN) c.n = c.C.n := F₂.mn
    have z₂ : wordsVal s₂.mem base (c.sl RZ) c.n = sv c base s RZ := v₂ (by decide) (by decide) (by decide) (by decide)
    have d₂ : wordsVal s₂.mem base (c.sl D) c.n = sv c base s D := v₂ (by decide) (by decide) (by decide) (by decide)
    rw [f₆, f₅, flagW, flag_unch U₂ h7 h0 hn (by decide), ← flagW, hflag,
      sv_flag O₅ h0 h7 hn (i := RZ) (by decide) (by decide), hMN, z₂, d₂, mask32_and, mask32_and]
    simp only [mask32, decide_eq_true_eq]
  have W₆ : Unch base [(0, size)] s₀.mem s₆.mem :=
    whole_of (whole_of (whole_of hwhole U₂ (slWk_le h7 (by decide))) O₅.unch (flag_le h0 h7))
      O₆.unch (flag_le h0 h7)
  have hesp₆ : s₆.gpr .esp = s₀.gpr .esp := by
    rw [k₆.1 _ (by decide), k₅.1 _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide), hesp]
  have hrd₆ : s₆.rd = s₀.rd := by rw [k₆.2.1, k₅.2.1, k₂.rd, k₁.rd, hrd]
  have hwr₆ : s₆.wr = s₀.wr := by rw [k₆.2.2, k₅.2.2, k₂.wr, k₁.wr, hwr]
  have hout := argLoad_ok (i := 0) hin hdarg hesp₆ (by rw [hrd₆, hwr₆]) (W₆.outside fun w hw => by
    rw [List.mem_singleton.mp hw]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩)
  refine WP.mono (ecFinish_ok hc hs₆ hout hofit (by rw [hwr₆]; exact hw) hd F₆.saved _ hflag₆)
    fun s' ⟨bytes, ret, saved, others, Oout⟩ =>
      ⟨_, lt₂, x₂, ?_, ret, saved, by rw [others _ (by decide), hesp₆], s₆.mem, W₆, Oout⟩
  have x₆ : sv c base s₆ X = sv c base s₂ X := (sv_flag O₆ h0 h7 hn (i := X) (by decide) (by decide)).trans
    (sv_flag O₅ h0 h7 hn (i := X) (by decide) (by decide))
  rw [bytes, x₆]

end VG.Proof.Ecdh.X86

/-!
## The whole function

`exchange_ok`: `Cfg.exchange` computes the specification's shared secret of
`d` and the peer's public key, for any curve the ECDSA proof supports
(`CfgOk`), and restores the callee-saved registers.

The signature's setup, reading `k`, `d` and the hash all from `d`
(`Args.ecdh`), and its tables (`stage₁`); then `peer_ok`, `validate_ok`,
`ladPow_ok` and `middle_ok`; `exchange_eq` connects what they compute to the
specification.
-/

namespace VG.Proof.Ecdh.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86
open VG.Impl.Ecdh.X86 (QY R2P BP QXM QYM W0 W1 W2 W3 PX PY Args.ecdh)

variable {c : Cfg}

/-- The arguments: `out` (`8 n` bytes), `d` (`8 n` bytes), `peer`
(`1 + 16 n` bytes) and `scratch`, readable and writable as the contract says
and apart from each other as it says. -/
structure EPre (c : Cfg) (s : State) : Prop where
  rd : s.rd = [⟨ptr s 1, 8 * c.n⟩, ⟨ptr s 2, 1 + 16 * c.n⟩, ⟨argAddr s 0, 16⟩]
  wr : s.wr = [⟨ptr s 0, 8 * c.n⟩, ⟨ptr s 3, size⟩]
  out_sc : Region.Disjoint ⟨ptr s 0, 8 * c.n⟩ ⟨ptr s 3, size⟩
  out_d : Region.Disjoint ⟨ptr s 0, 8 * c.n⟩ ⟨ptr s 1, 8 * c.n⟩
  out_peer : Region.Disjoint ⟨ptr s 0, 8 * c.n⟩ ⟨ptr s 2, 1 + 16 * c.n⟩
  d_sc : Region.Disjoint ⟨ptr s 1, 8 * c.n⟩ ⟨ptr s 3, size⟩
  peer_sc : Region.Disjoint ⟨ptr s 2, 1 + 16 * c.n⟩ ⟨ptr s 3, size⟩
  args_out : Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨ptr s 0, 8 * c.n⟩
  args_sc : Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨ptr s 3, size⟩
  ret_out : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨ptr s 0, 8 * c.n⟩
  ret_sc : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨ptr s 3, size⟩
  out_fit : (arg s 0).toNat + 8 * c.n ≤ 2 ^ 32
  d_fit : (arg s 1).toNat + 8 * c.n ≤ 2 ^ 32
  peer_fit : (arg s 2).toNat + (1 + 16 * c.n) ≤ 2 ^ 32
  sc_fit : (arg s 3).toNat + size ≤ 2 ^ 32
  sp_fit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32

theorem idx_ecdh {i : Nat} (hi : i ∈ Args.ecdh.idx) : i < 4 := by
  simp only [Args.idx, List.mem_cons, List.not_mem_nil, or_false] at hi
  omega

theorem EPre.setup {s : State} (hp : EPre c s) (h7 : c.n < 7) : SetupPre c Args.ecdh s where
  wr := by rw [hp.wr]; simp
  arg_in := fun i hi => ⟨_, by rw [hp.rd]; simp, arg_containsN (k := 4) (by have := hp.sp_fit; omega)
    (idx_ecdh hi)⟩
  arg_sc := fun i hi => hp.args_sc.sub_left (arg_subN (k := 4) (by have := hp.sp_fit; omega) (idx_ecdh hi))
  sp_fit := fun i hi => by have := idx_ecdh hi; have := hp.sp_fit; omega
  k_in := inRegions_words (by rw [hp.rd]; simp) (by omega)
  d_in := inRegions_words (by rw [hp.rd]; simp) (by omega)
  e_in := inRegions_words (by rw [hp.rd]; simp) (by omega)
  k_sc := hp.d_sc
  d_sc := hp.d_sc
  e_sc := hp.d_sc
  k_fit := hp.d_fit
  d_fit := hp.d_fit
  e_fit := hp.d_fit
  sc_fit := hp.sc_fit

/-- The private key. -/
abbrev dk (c : Cfg) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 1) (8 * c.n))

/-- The result the contract asks for: the specification's shared secret, and
`1`, or zeros and `0`. -/
def EPost (c : Cfg) (s₀ s' : State) : Prop :=
  match Spec.Ecdh.exchange c.C (dk c s₀) (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 2) (1 + 16 * c.n)) with
  | some z => s'.gpr .eax = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (ptr s₀ 0) (8 * c.n) = z
  | none => s'.gpr .eax = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (ptr s₀ 0) (8 * c.n) = List.replicate (8 * c.n) 0

/-- What the function keeps: the callee-saved registers, `esp`, and memory
but the working space and `out`. -/
structure EKeep (c : Cfg) (s₀ s' : State) : Prop where
  saved : ∀ rd ∈ Cfg.saved, s'.gpr rd.1 = s₀.gpr rd.1
  esp : s'.gpr .esp = s₀.gpr .esp
  frame : ∃ m : Mem, Unch (ptr s₀ 3) [(0, size)] s₀.mem m ∧ Outside (ptr s₀ 0) 0 (8 * c.n) m s'.mem

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
theorem peer_bytes (m : Mem) (p : Addr) (n : Nat) :
    Spec.Ecdsa.bytesAt m p (1 + 16 * n) = m p :: (Spec.Ecdsa.bytesAt m (p + BitVec.ofNat 64 1) (8 * n) ++
      Spec.Ecdsa.bytesAt m (p + BitVec.ofNat 64 (1 + 8 * n)) (8 * n)) := by
  have h1 : Spec.Ecdsa.bytesAt m p 1 = [m p] := by
    simp only [Spec.Ecdsa.bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero]
  rw [show 1 + 16 * n = 1 + (8 * n + 8 * n) by omega, bytesAt_add, bytesAt_add, h1, BitVec.add_assoc,
    BitVec.ofNat_add_ofNat]
  rfl

theorem exchange_eq' (c : Cfg) : Impl.Ecdh.X86.Cfg.exchange c =
    .seq (.seq (.block (c.setupWith Args.ecdh))
      (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) (.seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n))
      (.seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) (.block [])))))
    (.seq (.block (Impl.Ecdh.X86.Cfg.peer c)) (.seq (Impl.Ecdh.X86.Cfg.validate c)
    (.seq (ladder (Impl.Ecdh.X86.Cfg.ladderQ c) c.wk) (.seq (pow c.powP c.wk) (Impl.Ecdh.X86.Cfg.middle c))))) :=
  rfl

/-- `vg_ecdh_<curve>` computes the specification's shared secret and restores
the callee-saved registers. -/
theorem exchange_ok (hc : CfgOk c) (hC : Law c.C) {s₀ : State} (hp : EPre c s₀) :
    WP isa (Impl.Ecdh.X86.Cfg.exchange c) s₀ fun s' => EKeep c s₀ s' ∧ EPost c s₀ s' := by
  have h0 := hc.n0
  have h7 := hc.n7
  have hsz : size = 8192 := rfl
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have h4 : (s₀.gpr .esp).toNat + 4 + 4 * 4 ≤ 2 ^ 32 := by have := hp.sp_fit; omega
  rw [exchange_eq']
  refine WP.seq (stage₁ hc (hp.setup h7) fun s₂ S₂ => WP.block_nil ?_)
  have hn := S₂.scr.nowrap
  have W₂ : Outside (ptr s₀ 3) 0 size s₀.mem s₂.mem :=
    S₂.whole.outside fun w hw => by rw [List.mem_singleton.mp hw]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  have hq : ∀ t : State, t.gpr .esp = s₂.gpr .esp → t.rd ++ t.wr = s₂.rd ++ s₂.wr →
      Outside (ptr s₀ 3) 0 size s₂.mem t.mem → readSrc t (.mem (Cfg.argOp 2)) = some (arg s₀ 2) :=
    fun t he hrw ho => argLoad_ok (i := 2) ⟨_, by rw [hp.rd]; simp, arg_containsN h4 (by decide)⟩
      (hp.args_sc.sub_left (arg_subN h4 (by decide))) (he.trans S₂.esp)
      (hrw.trans (by rw [S₂.rd, S₂.wr])) (W₂.trans ho)
  -- The peer's key.
  refine WP.seq (WP.mono (peer_ok hc S₂.scr hq hp.peer_fit (by rw [S₂.rd, S₂.wr, hp.rd]; simp) hp.peer_sc
    S₂.fixed.mp) fun s₃ ⟨hs₃, k₃, U₃, r2₃, bp₃, x₃, y₃, f₃⟩ => ?_)
  have F₃ := S₂.fixed.unch h7 hn ((fixedOk_slW (l := [R2P, BP, E, QY]) (by decide)).append fixedOk_flag) U₃
  have e₃ : ∀ {i}, i < 45 → i ∉ [R2P, BP, E, QY] → i ≠ FLAG →
      sv c (ptr s₀ 3) s₃ i = sv c (ptr s₀ 3) s₂ i := fun hi hl hf =>
    sv_unch U₃ h7 hn hi (apart_append (apart_slW hl) (apart_flag h0 hf))
  have hq0 : s₂.mem (ptr s₀ 2) = s₀.mem (ptr s₀ 2) := by
    have := keep_of_disjoint' W₂ hp.peer_sc (by omega) (i := 0) (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  -- What the code checks of the peer's key so far.
  have hf₃ : flagW c (ptr s₀ 3) s₃ = mask32 (((s₀.mem (ptr s₀ 2) = 4 ∧
      sv c (ptr s₀ 3) s₃ E < c.C.p) ∧ sv c (ptr s₀ 3) s₃ QY < c.C.p)) := by
    rw [f₃, S₂.flag, BitVec.allOnes_and, mask32_and, mask32_and]
    simp only [hq0]
  refine WP.seq (WP.mono (validate_ok hc hs₃ F₃ r2₃ bp₃ hf₃)
    fun s₄ ⟨hs₄, g₄, rd₄, wr₄, U₄, f₄, px_lt, py_lt, px, py⟩ => ?_)
  have F₄ := F₃.unch h7 hn ((fixedOk_slWk (l := [QXM, QYM, TMP, W0, W1, W2, W3, PY]) (by decide)).append
    fixedOk_flag) U₄
  have e₄ : ∀ {i}, i < 45 → i ∉ [QXM, QYM, TMP, W0, W1, W2, W3, PY] → i ≠ FLAG →
      sv c (ptr s₀ 3) s₄ i = sv c (ptr s₀ 3) s₃ i := fun hi hl hf =>
    sv_unch U₄ h7 hn hi (apart_append (apart_slWk hi hl) (apart_flag h0 hf))
  have t₄ : ∀ {j}, j < 3 → ∀ t < 64 * c.n,
      s₄.mem (off (ptr s₀ 3) (bitsAt c.n j + t)) = s₂.mem (off (ptr s₀ 3) (bitsAt c.n j + t)) :=
    fun hj t ht => by
      rw [tbl_unch U₄ h7 hj ht (apart_append (tbl_apart_slWk (by decide) hj ht) (tbl_apart_flag h0 _ t)),
        tbl_unch U₃ h7 hj ht (apart_append (tbl_apart_slW (by decide) _ t) (tbl_apart_flag h0 _ t))]
  have hpk : sv c (ptr s₀ 3) s₂ K < 2 ^ (64 * c.n) := wordsVal_lt _ _ _ _
  -- `[d]P`, then `Z^(p-2)`.
  have hstep := step_rep (L := Impl.Ecdh.X86.Cfg.ladderQ c) (k := sv c (ptr s₀ 3) s₂ K) hC
    (peerPt_onCurve hc _ _ _)
    (by
      show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₄.mem _ (c.sl AP) c.n) = _
      rw [F₄.ap]; exact toM_cmont hc _)
    (by
      show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₄.mem _ (c.sl B3P) c.n) = _
      rw [F₄.b3p]; exact toM_cmont hc _)
    (peerPt_rep hC _ _ _ px py |> fun h => by
      show Rep c.C (toM c.C.p (2 ^ (64 * c.n)) (sv c (ptr s₀ 3) s₄ PX))
        (toM c.C.p (2 ^ (64 * c.n)) (sv c (ptr s₀ 3) s₄ PY))
        (toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₄.mem (ptr s₀ 3) (c.sl ONEP) c.n)) _
      rw [F₄.onep, toM_one hpR]; exact h)
  refine ladPow_ok hc hs₄ F₄ hstep
    (by rw [shiftRight_eq_zero hpk, mul_zero_pt]; exact rep_infinity' hC)
    px_lt py_lt
    (by rw [e₄ (by decide) (by decide) (by decide), e₃ (by decide) (by decide) (by decide)]; exact S₂.rx)
    (by rw [e₄ (by decide) (by decide) (by decide), e₃ (by decide) (by decide) (by decide)]; exact S₂.ry)
    (by rw [e₄ (by decide) (by decide) (by decide), e₃ (by decide) (by decide) (by decide)]; exact S₂.rz)
    (fun t ht => by rw [t₄ (j := 0) (by decide) t ht, S₂.t₀ t ht, S₂.k])
    (fun t ht => by rw [t₄ (j := 1) (by decide) t ht, S₂.t₁ t ht]) fun s₅ L => ?_
  have hs₅ := L.scr
  have F₅ := F₄.unch h7 hn ((fixedOk_slWk (by decide)).append (fixedOk_slWk (l := [ACC, PT, TMP]) (by decide)))
    L.unch
  have e₅ : ∀ {i}, i < 45 → i ∉ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5,
      TX, TY, TZ, TMP] → i ∉ [ACC, PT, TMP] → sv c (ptr s₀ 3) s₅ i = sv c (ptr s₀ 3) s₄ i :=
    fun hi h₁ h₂ => sv_unch L.unch h7 hn hi (apart_append (apart_slWk hi h₁) (apart_slWk hi h₂))
  have hflag₅ : flagW c (ptr s₀ 3) s₅ = mask32 (PeerOk c (ptr s₀ 3) s₃ ((s₀.mem (ptr s₀ 2) = 4 ∧
      sv c (ptr s₀ 3) s₃ E < c.C.p) ∧ sv c (ptr s₀ 3) s₃ QY < c.C.p)) := by
    have hFl := sl_le c h7 (i := FLAG) (by decide)
    have ap : ∀ w ∈ slWk c [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5,
        TX, TY, TZ, TMP] ++ slWk c [ACC, PT, TMP], c.sl FLAG + 4 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG := by
      intro w hw
      rcases apart_append (apart_slWk (c := c) (i := FLAG) (by decide) (by decide))
        (apart_slWk (c := c) (i := FLAG) (l := [ACC, PT, TMP]) (by decide) (by decide)) w hw with h | h
      · exact Or.inl (by omega)
      · exact Or.inr h
    rw [flagW, Unch.readW32 L.unch ap (by omega), ← flagW]
    exact f₄
  have hesp₅ : s₅.gpr .esp = s₀.gpr .esp := by
    rw [L.gpr _ (by decide), g₄ _ (by decide), k₃.1 _ (by decide), S₂.esp]
  have W₅ : Unch (ptr s₀ 3) [(0, size)] s₀.mem s₅.mem :=
    whole_of (whole_of (whole_of S₂.whole U₃ (le_append (slWk_le h7 (l := [R2P, BP, E, QY]) (by decide) |>
      fun h w hw => h w (List.mem_append_left _ hw)) (flag_le h0 h7))) U₄
      (le_append (slWk_le h7 (by decide)) (flag_le h0 h7))) L.unch
      (le_append (slWk_le h7 (by decide)) (slWk_le h7 (by decide)))
  refine WP.mono (middle_ok hc hs₅ F₅ L.acc_lt hflag₅ W₅ hesp₅ (by rw [L.rd, rd₄, k₃.2.1, S₂.rd])
    (by rw [L.wr, wr₄, k₃.2.2, S₂.wr]) ⟨_, by rw [hp.rd]; simp, arg_containsN h4 (by decide)⟩
    (hp.args_sc.sub_left (arg_subN h4 (by decide))) hp.out_fit (by rw [hp.wr]; simp) hp.out_sc)
    fun s' ⟨xv, hxl, hxv, bytes, ret, saved, esp, m, Wm, Om⟩ => ⟨⟨saved, esp, m, Wm, Om⟩, ?_⟩
  -- The specification.
  have hlen : (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 2) (1 + 16 * c.n)).length = 2 * c.C.len + 1 := by
    rw [length_bytesAt, hc.len]; omega
  have hb0 : (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 2) (1 + 16 * c.n)).head? = some (s₀.mem (ptr s₀ 2)) := by
    rw [peer_bytes]; rfl
  have hxs : ofBytes (((Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 2) (1 + 16 * c.n)).drop 1).take c.C.len) =
      sv c (ptr s₀ 3) s₃ E := by
    rw [peer_bytes, List.drop_one, List.tail_cons, hc.len, List.take_left' (length_bytesAt _ _ _), x₃,
      bytesAt_keep W₂ (hp.peer_sc.sub_left (Offset.sub_base _ (by omega))) (by omega) (by omega)]
  have hys : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 2) (1 + 16 * c.n)).drop (c.C.len + 1)) =
      sv c (ptr s₀ 3) s₃ QY := by
    rw [peer_bytes, hc.len, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _), y₃,
      bytesAt_keep W₂ (hp.peer_sc.sub_left (Offset.sub_base _ (by omega))) (by omega) (by omega)]
  have hP' : ∀ h : Ecdh.Valid c.C (s₀.mem (ptr s₀ 2)) (sv c (ptr s₀ 3) s₃ E) (sv c (ptr s₀ 3) s₃ QY),
      peerPt c (s₀.mem (ptr s₀ 2) = 4) (sv c (ptr s₀ 3) s₃ E) (sv c (ptr s₀ 3) s₃ QY) =
        .affine ⟨_, h.2.1⟩ ⟨_, h.2.2.1⟩ := fun h => by
    unfold peerPt; rw [dite_eq_left ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩]
  have hk : sv c (ptr s₀ 3) s₂ K = dk c s₀ := S₂.k
  have hR := L.q
  rw [Nat.shiftRight_zero, hk] at hR
  have hxoX : Fin.ofNat c.C.p xv = tmv c.C c.n (ptr s₀ 3) s₅ (c.sl RX) *
      tmv c.C c.n (ptr s₀ 3) s₅ (c.sl RZ) ^ (c.C.p - 2) := by rw [hxv, L.acc]
  have hspec := exchange_eq hC hlen hb0 hxs hys hP' hR hxl hxoX
  have hD₅ : sv c (ptr s₀ 3) s₅ D = dk c s₀ := by
    rw [e₅ (by decide) (by decide) (by decide), e₄ (by decide) (by decide) (by decide),
      e₃ (by decide) (by decide) (by decide)]
    exact S₂.d
  have hz : tmv c.C c.n (ptr s₀ 3) s₅ (c.sl RZ) ≠ 0 ↔ sv c (ptr s₀ 3) s₅ RZ ≠ 0 :=
    not_congr (toM_eq_zero_iff hpR L.rz_lt)
  unfold EPost
  rw [hspec]
  by_cases hcond : (1 ≤ dk c s₀ ∧ dk c s₀ < c.C.n) ∧
      Ecdh.Valid c.C (s₀.mem (ptr s₀ 2)) (sv c (ptr s₀ 3) s₃ E) (sv c (ptr s₀ 3) s₃ QY) ∧
      tmv c.C c.n (ptr s₀ 3) s₅ (c.sl RZ) ≠ 0
  · have hok : ok c (ptr s₀ 3) s₅ (PeerOk c (ptr s₀ 3) s₃ ((s₀.mem (ptr s₀ 2) = 4 ∧
        sv c (ptr s₀ 3) s₃ E < c.C.p) ∧ sv c (ptr s₀ 3) s₃ QY < c.C.p)) = true := by
      refine decide_eq_true ⟨⟨⟨⟨⟨hcond.2.1.1, hcond.2.1.2.1⟩, hcond.2.1.2.2.1⟩, hcond.2.1.2.2.2⟩, ?_, ?_⟩,
        hz.mp hcond.2.2⟩
      · rw [hD₅]; exact hcond.1.1
      · rw [hD₅]; exact hcond.1.2
    rw [ite_eq_left hcond]
    exact ⟨by rw [ret, hok]; rfl, by rw [bytes, hok, hc.len]; rfl⟩
  · have hok : ok c (ptr s₀ 3) s₅ (PeerOk c (ptr s₀ 3) s₃ ((s₀.mem (ptr s₀ 2) = 4 ∧
        sv c (ptr s₀ 3) s₃ E < c.C.p) ∧ sv c (ptr s₀ 3) s₃ QY < c.C.p)) = false := by
      refine decide_eq_false fun h => hcond ⟨⟨?_, ?_⟩, ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2⟩,
        hz.mpr h.2⟩
      · rw [← hD₅]; exact h.1.2.1
      · rw [← hD₅]; exact h.1.2.2
    rw [ite_eq_right hcond]
    exact ⟨by rw [ret, hok]; rfl, by rw [bytes, hok]; rfl⟩

end VG.Proof.Ecdh.X86
