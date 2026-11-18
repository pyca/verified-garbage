module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Main
public import VerifiedGarbage.Proof.Ecdsa.Arm.PublicCT
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ecdsa.Verify
public import VerifiedGarbage.Proof.Ecdh.Arm.Main
import VerifiedGarbage.Proof.Ecdsa.Arm.Main
import VerifiedGarbage.Proof.Weierstrass.Pow
import VerifiedGarbage.Proof.Weierstrass.Words

/-!
# ECDSA verification on 32-bit ARM: constant time in its secrets

Verification has no secret, and `[v]Q` is by `vg_<curve>_mul_public`, whose
timing depends on `v` and `Q`: on the signature and the public key, which
the contract lets timing depend on. So `verifyWith` is not constant time by
the taint analysis alone, which takes only the pointers for public.

`verifyWith_ct` relates two runs on the same pointers, key and signature
(`VPub`). `verifyWith` runs as `verifyHead`, the call, and `verifyTail`
(`verifyWith_eqv`). The taint analysis proves the two parts around the call
(the hypotheses, for a curve's proof to check), correctness (`verifyHead_ok`)
gives both runs the call's number and point, which the key and the
signature determine, and `pubCall_ct` relates the calls.
-/

-- separate module: only the curves' constant-time proofs import it

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.Arm VG.Proof.Ecdh.Arm
open VG.Proof.X25519.Arm (Rest)
open VG.Impl.Ecdh.Arm (PX PY)
open VG.Impl.Ecdsa.Verify.Arm (U V)

variable {c : Cfg}

/-! ## Code that runs the same -/

/-- `p` and `q` run the same, and leak the same. -/
def Eqv (p q : Prog isa) : Prop := ∀ s t s', Exec isa p s t s' ↔ Exec isa q s t s'

theorem Eqv.refl (p : Prog isa) : Eqv p p := fun _ _ _ => Iff.rfl

theorem Eqv.symm {p q : Prog isa} (h : Eqv p q) : Eqv q p := fun s t s' => (h s t s').symm

theorem Eqv.trans {p q r : Prog isa} (h₁ : Eqv p q) (h₂ : Eqv q r) : Eqv p r :=
  fun s t s' => (h₁ s t s').trans (h₂ s t s')

theorem Eqv.seq_right {a b b' : Prog isa} (h : Eqv b b') : Eqv (.seq a b) (.seq a b') := by
  intro s t s'
  constructor
  · intro e
    cases e with
    | seq e₁ e₂ => exact .seq e₁ ((h _ _ _).mp e₂)
  · intro e
    cases e with
    | seq e₁ e₂ => exact .seq e₁ ((h _ _ _).mpr e₂)

theorem Eqv.assoc (a b d : Prog isa) : Eqv (.seq (.seq a b) d) (.seq a (.seq b d)) := by
  intro s t s'
  constructor
  · intro e
    cases e with
    | seq e₁ e₃ =>
      cases e₁ with
      | seq ea eb => rw [List.append_assoc]; exact .seq ea (.seq eb e₃)
  · intro e
    cases e with
    | seq ea e₂ =>
      cases e₂ with
      | seq eb ec => rw [← List.append_assoc]; exact .seq (.seq ea eb) ec

/-- The pieces `l` in sequence, then `p`. -/
def seqs : List (Prog isa) → Prog isa → Prog isa
  | [], p => p
  | a :: l, p => .seq a (seqs l p)

theorem Eqv.seqs_right (l : List (Prog isa)) {p q : Prog isa} (h : Eqv p q) : Eqv (seqs l p) (seqs l q) := by
  induction l with
  | nil => exact h
  | cons a l ih => exact Eqv.seq_right ih

theorem Eqv.seqs_left (l : List (Prog isa)) (m t : Prog isa) :
    Eqv (.seq (seqs l m) t) (seqs l (.seq m t)) := by
  induction l with
  | nil => exact Eqv.refl _
  | cons a l ih => exact (Eqv.assoc _ _ _).trans (Eqv.seq_right ih)

theorem Eqv.seqs_pre (l : List (Prog isa)) (a rest : Prog isa) :
    Eqv (seqs l (.seq a rest)) (.seq (seqs l a) rest) := by
  induction l with
  | nil => exact Eqv.refl _
  | cons x l ih => exact (Eqv.seq_right ih).trans (Eqv.assoc _ _ _).symm

theorem Eqv.relCT {p q : Prog isa} (h : Eqv p q) {P Q : State → State → Prop} (hp : RelCT isa P p Q) :
    RelCT isa P q Q :=
  fun _ _ _ _ _ _ hP e₁ e₂ => hp _ _ _ _ _ _ hP ((h _ _ _).mpr e₁) ((h _ _ _).mpr e₂)

/-! ## The parts around the call -/

/-- `verifyWith` up to the call of `vg_<curve>_mul_public`. -/
def verifyHead (c : Cfg) (generator : Prog isa) : Prog isa :=
  seqs [Impl.Ecdsa.Verify.Arm.Cfg.prefix' c, .block (Impl.Ecdsa.Verify.Arm.Cfg.loadS c),
    .block (Impl.Ecdh.Arm.Cfg.peerAt c .r0), Impl.Ecdh.Arm.Cfg.validate c,
    Impl.Ecdsa.Verify.Arm.Cfg.scalars c, pow c.powN c.SN c.umaal, Impl.Ecdsa.Verify.Arm.Cfg.uv c,
    Impl.Ecdsa.Verify.Arm.Cfg.scalarAt c U, generator, .block (Impl.Ecdsa.Verify.Arm.Cfg.save c),
    Impl.Ecdsa.Verify.Arm.Cfg.scalarAt c V] (.block (c.callMulArgs PX PY))

/-- `verifyWith` after the call. -/
def verifyTail (c : Cfg) : Prog isa :=
  .seq (.block [.mov .lr (.reg .r10)]) <| .seq (Impl.Ecdsa.Verify.Arm.Cfg.sum c) <|
  .seq (pow c.powP c.SP c.umaal) (Impl.Ecdsa.Verify.Arm.Cfg.final c)

/-- `vg_<curve>_mul_public`'s name. -/
def pubName (c : Cfg) (C : Impl.Weierstrass.Mul.Curve) : String :=
  s!"vg_{C.curve}_mul_public" ++ if c.umaal then "_umaal" else ""

/-- `verifyWith` runs as its head, the call and its tail. -/
theorem verifyWith_eqv {C : Impl.Weierstrass.Mul.Curve} (hm : c.mul = some C) (generator : Prog isa) :
    Eqv (Impl.Ecdsa.Verify.Arm.Cfg.verifyWith c generator)
      (.seq (.seq (verifyHead c generator) (.call (pubName c C) c.pubFn)) (verifyTail c)) := by
  have e : Impl.Ecdsa.Verify.Arm.Cfg.verifyWith c generator =
      seqs [Impl.Ecdsa.Verify.Arm.Cfg.prefix' c, .block (Impl.Ecdsa.Verify.Arm.Cfg.loadS c),
        .block (Impl.Ecdh.Arm.Cfg.peerAt c .r0), Impl.Ecdh.Arm.Cfg.validate c,
        Impl.Ecdsa.Verify.Arm.Cfg.scalars c, pow c.powN c.SN c.umaal, Impl.Ecdsa.Verify.Arm.Cfg.uv c]
        (.seq (seqs [Impl.Ecdsa.Verify.Arm.Cfg.scalarAt c U, generator,
            .block (Impl.Ecdsa.Verify.Arm.Cfg.save c), Impl.Ecdsa.Verify.Arm.Cfg.scalarAt c V]
          (.seq (.seq (.block (c.callMulArgs PX PY))
            (.seq (.call (pubName c C) c.pubFn) (.block [.mov .lr (.reg .r10)])))
            (Impl.Ecdsa.Verify.Arm.Cfg.sum c)))
          (.seq (pow c.powP c.SP c.umaal) (Impl.Ecdsa.Verify.Arm.Cfg.final c))) := by
    unfold Impl.Ecdsa.Verify.Arm.Cfg.verifyWith Impl.Ecdsa.Verify.Arm.Cfg.backWith
      Impl.Ecdsa.Verify.Arm.Cfg.pointsWith Cfg.qMulPub Cfg.qMulWith
    rw [hm]
    rfl
  rw [e]
  refine (Eqv.seqs_right _ ((Eqv.seqs_left _ _ _).trans (Eqv.seqs_right _ ?_))).trans
    ((Eqv.seqs_pre [Impl.Ecdsa.Verify.Arm.Cfg.prefix' c, .block (Impl.Ecdsa.Verify.Arm.Cfg.loadS c),
      .block (Impl.Ecdh.Arm.Cfg.peerAt c .r0), Impl.Ecdh.Arm.Cfg.validate c,
      Impl.Ecdsa.Verify.Arm.Cfg.scalars c, pow c.powN c.SN c.umaal, Impl.Ecdsa.Verify.Arm.Cfg.uv c,
      Impl.Ecdsa.Verify.Arm.Cfg.scalarAt c U, generator, .block (Impl.Ecdsa.Verify.Arm.Cfg.save c),
      Impl.Ecdsa.Verify.Arm.Cfg.scalarAt c V] (.block (c.callMulArgs PX PY))
      (.seq (.call (pubName c C) c.pubFn) (verifyTail c))).trans (Eqv.assoc _ _ _).symm)
  exact (Eqv.assoc _ _ _).trans ((Eqv.assoc _ _ _).trans (Eqv.seq_right (Eqv.assoc _ _ _)))

/-! ## What the call finds -/

/-- What the call of `vg_<curve>_mul_public` finds, from `s₀`: after `u` and
`v` (`Mid`), the key's point and `v` where the call reads them (`PtsCall`),
then the call's arguments (`CallMid`). -/
def HeadPost (c : Cfg) (s₀ s₄ : State) : Prop :=
  ∃ sm s, Mid c s₀ (ptr s₀ .r3) sm ∧
    PtsCall c s₀ (ptr s₀ .r3) (peerPt c (s₀.mem (ptr s₀ .r0) = 4) (keyX c s₀) (keyY c s₀)) sm s ∧
    CallMid c (ptr s₀ .r3) PX PY s s₄

/-- `verifyHead`, as `verifyWith_ok` runs it. -/
theorem verifyHead_ok (hc : CfgOk c) (hC : Law c.C) {s₀ : State} {extra : List Region}
    (hp : VPre c s₀ extra) {generator : Prog isa} {a0₁ : Bool} (ha₁ : a0₁ = true → c.qA0 = true)
    (hMul : ∀ s, Mid c s₀ (ptr s₀ .r3) s → s.syms=s₀.syms →
      GeneratorWP c generator s₀ (ptr s₀ .r3) (sv c (ptr s₀ .r3) s U)
        (fun j X Y Z => Rep c.C X Y Z (mul (sv c (ptr s₀ .r3) s U >>> j) (G c.C))) s.syms a0₁) :
    WP isa (verifyHead c generator) s₀ (HeadPost c s₀) := by
  have setupRun := front_ok hc hp (rest := .seq (Impl.Ecdsa.Verify.Arm.Cfg.scalars c)
    (.seq (pow c.powN c.SN c.umaal) (.seq (Impl.Ecdsa.Verify.Arm.Cfg.uv c) (.block []))))
    (Q := fun s => Mid c s₀ (ptr s₀ .r3) s)
    (fun _ F => mid_ok hc F fun _ M => WP.block_nil M)
  have finish : ∀ s₂, Mid c s₀ (ptr s₀ .r3) s₂ → s₂.syms=s₀.syms →
      WP isa (seqs [Impl.Ecdsa.Verify.Arm.Cfg.scalarAt c U, generator,
        .block (Impl.Ecdsa.Verify.Arm.Cfg.save c), Impl.Ecdsa.Verify.Arm.Cfg.scalarAt c V]
        (.block (c.callMulArgs PX PY))) s₂ (HeadPost c s₀) := by
    intro s₂ hM syms₂
    have F₂ := hM.fixed
    obtain ⟨ha, hb, h1⟩ := consts_tmv hc F₂
    have hG : Rep c.C (tmv c.C c.n (ptr s₀ .r3) s₂ (c.sl GX)) (tmv c.C c.n (ptr s₀ .r3) s₂ (c.sl GY))
        (tmv c.C c.n (ptr s₀ .r3) s₂ (c.sl ONEP)) (G c.C) := by
      show Rep c.C (toM _ _ (wordsVal s₂.mem _ (c.sl GX) c.n)) (toM _ _ (wordsVal s₂.mem _ (c.sl GY) c.n))
        (toM _ _ (wordsVal s₂.mem _ (c.sl ONEP) c.n)) (G c.C)
      rw [F₂.gx, F₂.gy, toM_cmont hc, toM_cmont hc, show toM c.C.p (2 ^ (64 * c.n))
        (wordsVal s₂.mem (ptr s₀ .r3) (c.sl ONEP) c.n) = 1 from h1]
      exact rep_affine' hC _ _
    have hQ : Rep c.C (tmv c.C c.n (ptr s₀ .r3) s₂ (c.sl PX)) (tmv c.C c.n (ptr s₀ .r3) s₂ (c.sl PY)) 1
        (peerPt c (s₀.mem (ptr s₀ .r0) = 4) (keyX c s₀) (keyY c s₀)) :=
      peerPt_rep hC _ _ _ hM.px hM.py
    have hu : sv c (ptr s₀ .r3) s₂ U < 2 ^ (8 * c.C.len) := Nat.lt_trans hM.u_lt hc.n_enc
    have h0 : c.qA0 = true → (Fin.ofNat c.C.p c.C.a : Fe c.C) = 0 ∧
        tmv c.C c.n (ptr s₀ .r3) s₂ (c.sl ONEP) = 1 := fun h =>
      ⟨by simp only [Impl.Ecdsa.Arm.Cfg.qA0, Bool.and_eq_true, beq_iff_eq] at h; rw [h.2.1]; rfl, h1⟩
    refine pointsHead_ok hc hM
      (Q₁ := fun j X Y Z => Rep c.C X Y Z (mul (sv c (ptr s₀ .r3) s₂ U >>> j) (G c.C)))
      (hMul s₂ hM syms₂)
      (step_rep' (L := c.ladderCfg) (base := ptr s₀ .r3) (s := s₂) hC hc.onG ha hb hG fun h => h0 (ha₁ h))
      (by rw [shiftRight_eq_zero hu, mul_zero_pt]; exact rep_infinity' hC) hQ fun s hpts => ?_
    exact WP.mono (callMulArgs_ok hc hpts.scr (by decide) (by decide) (by decide) (by decide))
      fun s₄ M => ⟨s₂, s, hM, hpts, M⟩
  have run := WP.mono_syms setupRun finish
  simpa only [verifyHead, seqs, WP.seq_iff (M := isa), WP.block_nil_iff (M := isa)] using run

/-- The call's function finds the key's point and `v`, which the signature
determines. -/
theorem HeadPost.entry (hc : CfgOk c) {C : Impl.Weierstrass.Mul.Curve} (hm : c.mul = some C)
    {s₀ s₄ : State} (h : HeadPost c s₀ s₄) :
    ∃ k, PubEntry c (s₀.gpr .r3) (peerPt c (s₀.mem (ptr s₀ .r0) = 4) (keyX c s₀) (keyY c s₀)) k s₄ ∧
      k < c.C.n ∧
      Fin.ofNat c.C.n k = Fin.ofNat c.C.n (sigR c s₀) * Fin.ofNat c.C.n (sigS c s₀) ^ (c.C.n - 2) := by
  obtain ⟨sm, s, hM, pts, M⟩ := h
  have e : ∀ {i}, i < 45 → i ≠ RX → i ≠ RY → sv c (ptr s₀ .r3) s₄ i = sv c (ptr s₀ .r3) s i := M.same
  refine ⟨sv c (ptr s₀ .r3) sm V, ⟨M.r0.trans (scr_r12 pts.scr), (pts.scr.of_rest M.keep (by decide)).wr,
    pts.far.of_rest M.keep, (e (by decide) (by decide) (by decide)).trans pts.fixed.mp,
    (e (by decide) (by decide) (by decide)).trans pts.fixed.ap,
    (e (by decide) (by decide) (by decide)).trans pts.fixed.b3p,
    (e (by decide) (by decide) (by decide)).trans pts.fixed.zero,
    (e (by decide) (by decide) (by decide)).trans pts.fixed.onep,
    lt_of_eq_of_lt M.rx pts.px_lt, lt_of_eq_of_lt M.ry pts.py_lt, ?_,
    (e (by decide) (by decide) (by decide)).trans (pts.k (by rw [hm]; rfl)),
    Nat.lt_trans hM.v_lt hc.n_enc⟩, hM.v_lt, hM.v⟩
  show Rep _ (toM _ _ (sv c _ s₄ RX)) (toM _ _ (sv c _ s₄ RY)) _ _
  rw [M.rx, M.ry]; exact pts.rep

/-! ## Two runs on the same key and signature -/

/-- What verification's timing depends on besides the pointers: the working
space, and the key and the signature, which determine `[v]Q`. -/
structure VPub (c : Cfg) (x y : State) : Prop where
  r3 : x.gpr .r3 = y.gpr .r3
  b0 : x.mem (ptr x .r0) = y.mem (ptr y .r0)
  kx : keyX c x = keyX c y
  ky : keyY c x = keyY c y
  r : sigR c x = sigR c y
  s : sigS c x = sigS c y

/-- From the key's and the signature's octets, as the contract has them. -/
theorem VPub.of_bytes {x y : State} (h3 : x.gpr .r3 = y.gpr .r3)
    (hk : Spec.Ecdsa.bytesAt x.mem (ptr x .r0) (1 + 2 * c.C.len) =
      Spec.Ecdsa.bytesAt y.mem (ptr y .r0) (1 + 2 * c.C.len))
    (hs : Spec.Ecdsa.bytesAt x.mem (ptr x .r2) (2 * c.C.len) =
      Spec.Ecdsa.bytesAt y.mem (ptr y .r2) (2 * c.C.len)) : VPub c x y := by
  have hb0 : ∀ s₀ : State, (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r0) (1 + 2 * c.C.len)).head? =
      some (s₀.mem (ptr s₀ .r0)) := fun s₀ => by rw [peer_bytes]; rfl
  have hxv : ∀ s₀ : State, ofBytes (((Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r0) (1 + 2 * c.C.len)).drop 1).take
      c.C.len) = keyX c s₀ := fun s₀ => by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _)]
  have hyv : ∀ s₀ : State, ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r0) (1 + 2 * c.C.len)).drop
      (c.C.len + 1)) = keyY c s₀ := fun s₀ => by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _)]
  have h16 : 2 * c.C.len = c.C.len + c.C.len := by omega_using []
  have hr : ∀ s₀ : State, ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r2) (2 * c.C.len)).take c.C.len) =
      sigR c s₀ := fun s₀ => by
    rw [h16, bytesAt_add, List.take_left' (length_bytesAt _ _ _)]
  have hsv : ∀ s₀ : State, ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r2) (2 * c.C.len)).drop c.C.len) =
      sigS c s₀ := fun s₀ => by
    rw [h16, bytesAt_add, List.drop_left' (length_bytesAt _ _ _)]
  exact ⟨h3, Option.some.inj (by rw [← hb0 x, ← hb0 y, hk]), by rw [← hxv x, ← hxv y, hk],
    by rw [← hyv x, ← hyv y, hk], by rw [← hr x, ← hr y, hs], by rw [← hsv x, ← hsv y, hs]⟩

/-- From what the contract lets timing depend on (`verifyContract`'s `leak`):
the octets of the key, the hash and the signature. -/
theorem VPub.of_leak {x y : State} (h3 : x.gpr .r3 = y.gpr .r3) {n₁ n₂ n₃ : Nat}
    (e₁ : n₁ = 1 + 2 * c.C.len) (e₃ : n₃ = 2 * c.C.len)
    (h : (Spec.Ecdsa.bytesAt x.mem (ptr x .r0) n₁ ++ Spec.Ecdsa.bytesAt x.mem (ptr x .r1) n₂ ++
        Spec.Ecdsa.bytesAt x.mem (ptr x .r2) n₃).map (fun b => BitVec.toNat b) =
      (Spec.Ecdsa.bytesAt y.mem (ptr y .r0) n₁ ++ Spec.Ecdsa.bytesAt y.mem (ptr y .r1) n₂ ++
        Spec.Ecdsa.bytesAt y.mem (ptr y .r2) n₃).map (fun b => BitVec.toNat b)) : VPub c x y := by
  subst e₁ e₃
  have h' := (List.map_inj_right fun a b e => BitVec.eq_of_toNat_eq e).mp h
  obtain ⟨h12, hs⟩ := List.append_inj h' (by
    rw [List.length_append, List.length_append, length_bytesAt, length_bytesAt, length_bytesAt, length_bytesAt])
  obtain ⟨hk, -⟩ := List.append_inj h12 (by rw [length_bytesAt, length_bytesAt])
  exact VPub.of_bytes h3 hk hs

/-- `verifyWith` leaks the same in two runs on the same pointers, key and
signature (`hpub`), for a curve with `vg_<curve>_mul_public`, whose pieces
(`L`) and the two parts of verification around its call (`hhead`, `htail`)
the taint analysis proves, and whose generator's multiplication is correct
(`hwp`, `verifyHead_ok`). -/
theorem verifyWith_ct (hc : CfgOk c) (hC : Law c.C) {C : Impl.Weierstrass.Mul.Curve} (hm : c.mul = some C)
    {generator : Prog isa} {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ x y, Pre x → Pre y → Pub x y → VPub c x y)
    (hwp : ∀ s₀, Pre s₀ → WP isa (verifyHead c generator) s₀ (HeadPost c s₀))
    (hhead : RelCT isa (fun x y => Pre x ∧ Pre y ∧ Pub x y) (verifyHead c generator) fun _ _ => True)
    (htail : LeafCT [.r12] (verifyTail c)) (L : PubLeaves c) :
    ConstantTime isa Pre Pub (Impl.Ecdsa.Verify.Arm.Cfg.verifyWith c generator) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ((verifyWith_eqv hm generator).symm.relCT ?_)
  refine RelCT.seq (R := fun (x y : State) => x.gpr .r12 = y.gpr .r12) ?_
    (RelCT.mono htail (fun _ _ h => regs1 h) fun _ _ h => h)
  -- The working space is in `r12` again after the call.
  have hw : ∀ s₀, Pre s₀ → WP isa (.seq (verifyHead c generator) (.call (pubName c C) c.pubFn)) s₀
      fun s' => s'.gpr .r12 = s₀.gpr .r3 := fun s₀ hp =>
    WP.seq (WP.mono (hwp s₀ hp) fun s₄ ⟨sm, s, hM, pts, M⟩ =>
      WP.mono (callMulCall_ok hc (pubBody_bodyOk hc hC) _ (hc.pubNf C hm) pts.scr pts.far M pts.fixed.mp
        pts.fixed.ap pts.fixed.b3p pts.fixed.onep pts.fixed.zero pts.px_lt pts.py_lt
        (peerPt_onCurve hc _ _ _) pts.rep (by
          rw [pts.k (by rw [hm]; rfl)]; exact Nat.lt_trans hM.v_lt hc.n_enc))
        fun s₇ ⟨_, _, _, _, R, _⟩ => R.trans (scr_r12 pts.scr))
  refine RelCT.mono (RelCT.wpDep (F := fun (s₀ s' : State) => s'.gpr .r12 = s₀.gpr .r3)
    (RelCT.seq (R := fun (x y : State) => ∃ w P k, onCurve c.C P = true ∧ PubEntry c w P k x ∧ PubEntry c w P k y)
      (Q := fun _ _ => True) ?_ ?_) fun x y h => ⟨hw x h.1, hw y h.2.1⟩) (fun _ _ h => h)
    fun _ _ ⟨_, σ₁, σ₂, hσ, e₁, e₂⟩ => e₁.trans ((hpub σ₁ σ₂ hσ.1 hσ.2.1 hσ.2.2).r3.trans e₂.symm)
  · -- The head: both runs call the function on the same number and point.
    refine RelCT.mono (RelCT.wpDep (F := HeadPost c) hhead fun x y h => ⟨hwp x h.1, hwp y h.2.1⟩)
      (fun _ _ h => h) fun x' y' ⟨_, σ₁, σ₂, hσ, h₁, h₂⟩ => ?_
    obtain V := hpub σ₁ σ₂ hσ.1 hσ.2.1 hσ.2.2
    obtain ⟨k₁, E₁, l₁, v₁⟩ := h₁.entry hc hm
    obtain ⟨k₂, E₂, l₂, v₂⟩ := h₂.entry hc hm
    have ek : k₂ = k₁ := by
      rw [V.r, V.s] at v₁
      have e := congrArg Fin.val (v₂.trans v₁.symm)
      rwa [Fin.val_ofNat, Fin.val_ofNat, Nat.mod_eq_of_lt l₂, Nat.mod_eq_of_lt l₁] at e
    refine ⟨_, _, k₁, peerPt_onCurve hc _ _ _, E₁, ?_⟩
    rw [← V.r3, ← V.b0, ← V.kx, ← V.ky, ek] at E₂
    exact E₂
  · exact fun x y t₁ t₂ x' y' ⟨_, _, _, hP, hx, hy⟩ e₁ e₂ =>
      pubCall_ct hc hC hP L _ x y t₁ t₂ x' y' ⟨hx, hy⟩ e₁ e₂

end VG.Proof.Ecdsa.Verify.Arm
