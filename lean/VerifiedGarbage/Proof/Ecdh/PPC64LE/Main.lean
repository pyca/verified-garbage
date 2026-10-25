module

public import VerifiedGarbage.Proof.Ecdh.PPC64LE.Validate
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.LadderP
public import VerifiedGarbage.Impl.Ecdh.PPC64LE
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.Ecdh
import VerifiedGarbage.Proof.Ecdh.PPC64LE.Peer
import VerifiedGarbage.Proof.Ecdh.Exchange
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.EcKey.PPC64LE.Finish
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Finish
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Setup
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Flags
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.SlotOps
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.BytesLen
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Keep
import VerifiedGarbage.Proof.Weierstrass.BytesLen
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ECDH on PPC64LE: the whole function

As on 32-bit ARM (`Proof/Ecdh/Arm/Main.lean`). `ecFinish_ok`: `x` or zeros
to `out`, the return value and the callee-saved registers; `middle_ok`:
`x = X Z^(p-2)` out of Montgomery's form, the masks of `d ∈ [1, n-1]` and
`Z ≠ 0`, and the result.

`exchange_ok`: `Cfg.exchange` computes the specification's shared secret of
`d` and the peer's public key, for any curve the proof of the code supports
(`CfgOk`, coordinates of 3 to 6 words) whose group law the proofs support
(`Law`), restores the callee-saved registers and `lr`, and changes memory
only in the working space and `out`: the signature's setup and tables
(`stage₁`'s, with `peer` kept in `r12`), then `peer_ok`, `validate_ok`, the
ladder and the power (`ladPow_ok`) and `middle_ok`; `exchange_eq` connects
what they compute to the specification.
-/

@[expose] public section

namespace VG.Proof.Ecdh.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Spec.Weierstrass
open VG.Proof.EcKey.PPC64LE (toNat_add_of)
open VG.Proof.Weierstrass.PPC64LE.Point (tmv)
open VG.Impl.Ecdh.PPC64LE (QY R2P BP QXM QYM W0 W1 W2 W3 PX PY)

variable {c : Cfg}

theorem finish_eq (c : Cfg) : Impl.Ecdh.PPC64LE.Cfg.finish c =
    ([.load .d .r10 wb (c.sl FLAG)] : List Instr) ++ (storeBytes c.C.len c.n .r14 0 (c.sl X) ++
    (.li .r4 1 :: .logic .and .r4 .r10 .r4 :: (Cfg.restore ++ [mov .r3 .r4]))) := by
  simp only [Impl.Ecdh.PPC64LE.Cfg.finish, List.append_assoc, List.cons_append, List.nil_append]

/-- `x` or zeros, the return value and the callee-saved registers. -/
theorem ecFinish_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base) {out : Addr}
    (h14 : s.gpr .r14 = out) (hofit : out.toNat + c.C.len ≤ 2 ^ 64)
    (hwr : (⟨out, c.C.len⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨out, c.C.len⟩ ⟨base, size⟩) (b : Bool)
    (hf : flagW c base s = mask64 (b = true)) :
    WP isa (.block (Impl.Ecdh.PPC64LE.Cfg.finish c)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem out c.C.len =
        (if b then toBytes c.C.len (sv c base s X) else List.replicate c.C.len 0) ∧
      s'.gpr .r3 = (if b then 1 else 0) ∧
      s'.lr = word s.mem base Cfg.lrAt ∧ s'.gpr .r14 = word s.mem base 0 ∧ s'.gpr .r31 = word s.mem base 8 ∧
      Rk [.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31] s s' ∧
      Outside out 0 c.C.len s.mem s'.mem := by
  have h7 := hc.n10
  have hl8 := hc.len8
  have hlhi := hc.len_hi
  have hllo := hc.len_lo
  have hn := hw.nowrap
  have hsz : size = 8192 := rfl
  have hX := sl_le c h7 (i := X) (by decide)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  have hs := hw.ws
  have h3 := hw.at3
  have h0 : out + BitVec.ofNat 64 0 = out := BitVec.add_zero out
  rw [finish_eq, List.singleton_append]
  refine wp_step (ld0_ok hs h3 (by decide) (sl_al c FLAG) (by omega_arith)) ?_
  have hs₁ := hs.write .r10 (word s.mem base (c.sl FLAG))
  have h3₁ := h3.write (d := .r10) (word s.mem base (c.sl FLAG))
  have hc₁ : (s.write .r10 (word s.mem base (c.sl FLAG))).gpr .r10 = if b then BitVec.allOnes 64 else 0 := by
    simp only [write_gpr, ite_true]; rw [← flagW, hf]
  have hb₁ : (s.write .r10 (word s.mem base (c.sl FLAG))).gpr .r14 = out := by
    simp only [write_gpr, reduceCtorEq, ite_false]; exact h14
  refine wp_append (WP.mono (storeBytes_ok hs₁ h3₁ (dst := .r14) (d := 0) (a := c.sl X) (by decide) (by decide)
    (by decide) (by decide) b hc₁ (by omega_arith) (sl_al c X) (by omega_arith) (by omega_arith) hlhi (by omega_arith)
    (by rw [hb₁, h0]; exact hofit)
    (fun e m he => ⟨_, hwr, by rw [hb₁, h0]; exact Offset.contains_base out he (by omega_arith)⟩)
    (by rw [hb₁, h0]; exact hd.symm.sub_left (Offset.sub_base base (by omega_arith)))) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_)
  rw [hb₁, h0] at e₂ O₂
  have U₂ := O₂.unch_far hd.symm
  have hsv : ∀ d, d + 8 ≤ 24 → word s₂.mem base d = word s.mem base d := fun d hd' =>
    U₂.word (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega_arith) (by omega_arith)
  have hs₂ := k₂.ws hs₁
  have h3₂ := k₂.at h3₁
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_logic ?_
  refine restore_ok ((hs₂.write _ _).write _ _) ((h3₂.write _).write _) (by omega_arith) fun t Kt mt lrt r14t r31t => ?_
  refine wp_step exec_mov (WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  · simp only [write_mem]; rw [mt]; simp only [write_mem]; rw [e₂]; rfl
  · simp only [write_gpr, ite_true]
    rw [Kt.gpr _ (by decide)]
    simp only [write_gpr, ite_true, reduceCtorEq, ite_false]
    rw [k₂.g, hc₁, ← mask_bit]
  · simp only [write_lr]; rw [lrt]; simp only [write_mem]; exact hsv _ (by decide)
  · simp only [write_gpr, reduceCtorEq, ite_false]; rw [r14t]; simp only [write_mem]; exact hsv _ (by decide)
  · simp only [write_gpr, reduceCtorEq, ite_false]; rw [r31t]; simp only [write_mem]; exact hsv _ (by decide)
  · have R₁ : Rk [.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31] s s₂ :=
      ((Kp.write s (d := .r10) _ (rs := [.r10]) (by decide)).rk).trans
        (k₂.rk (rs' := [.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31]))
    exact ((R₁.trans (((Kp.write s₂ (d := .r4) (BitVec.ofNat 64 1) (rs := [.r4]) (by decide)).trans
      (Kp.write _ (d := .r4) _ (rs := [.r4]) (by decide))).rk)).trans (Kt.mono (by decide))).trans
      ((Kp.write t (d := .r3) _ (rs := [.r3]) (by decide)).rk)
  · simp only [write_mem]; rw [mt]; simp only [write_mem]; exact O₂

theorem middle_eq (c : Cfg) : Impl.Ecdh.PPC64LE.Cfg.middle c =
    .seq (mulCall c.SP (c.sl XM) (c.sl RX) (c.sl ACC))
    (.seq (mulCall c.SP (c.sl X) (c.sl XM) (c.sl ONE))
    (.block (c.checkRange (c.sl D) ++ c.checkNonzero (c.sl RZ) ++ Impl.Ecdh.PPC64LE.Cfg.finish c))) := rfl

/-- Whether the result is a shared secret: the peer's key (`V`), `d` in
`[1, n-1]`, and `Z ≠ 0`. -/
abbrev ok (c : Cfg) (base : Addr) (s : State) (V : Prop) [Decidable V] : Bool :=
  decide ((V ∧ 0 < sv c base s D ∧ sv c base s D < c.C.n) ∧ sv c base s RZ ≠ 0)

/-- `x`, the checks of `d` and `Z`, and the result, from a state that kept
what the stages keep since `s₀`. -/
theorem middle_ok (hc : CfgOk c) {s₀ : State} {base : Addr} {s : State} (K : Keep c s₀ base s)
    (hacc : sv c base s ACC < c.C.p) {V : Prop} [Decidable V] (hflag : flagW c base s = mask64 V)
    (hofit : (s₀.gpr .r3).toNat + c.C.len ≤ 2 ^ 64)
    (hw : (⟨s₀.gpr .r3, c.C.len⟩ : Region) ∈ s₀.wr)
    (hd : Region.Disjoint ⟨s₀.gpr .r3, c.C.len⟩ ⟨base, size⟩) :
    WP isa (Impl.Ecdh.PPC64LE.Cfg.middle c) s fun s' => ∃ xv, xv < c.C.p ∧
      Fin.ofNat c.C.p xv =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) ∧
      Spec.Ecdsa.bytesAt s'.mem (s₀.gpr .r3) c.C.len =
        (if ok c base s V then toBytes c.C.len xv else List.replicate c.C.len 0) ∧
      s'.gpr .r3 = (if ok c base s V then 1 else 0) ∧
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧ s'.lr = s₀.lr ∧
      ∃ m, Unch base [(0, size)] s₀.mem m ∧ Outside (s₀.gpr .r3) 0 c.C.len m s'.mem := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := K.ws.nowrap
  have hsz : size = 8192 := rfl
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hfl : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_arith
  have hone : sv c base s ONE = 1 := K.fixed.one
  rw [middle_eq]
  -- `XM = X · ACC`.
  refine WP.seq (WP.mono (slMul_ok hc.fp hc.fpk hc.fpm h7 K.ws (o := XM) (a := RX) (b := ACC) (by decide)
    (by decide) (by decide) hacc) fun s₁ ⟨k₁, U₁, _, e₁⟩ => ?_)
  have K₁ := K.step h7 k₁ (hU := U₁) (hW := fixedOk_callW h7 (by decide)) (hWs := callW_le h7 (by decide))
  have v₁ : ∀ {i}, i < 45 → i ≠ XM → sv c base s₁ i = sv c base s i := fun hi h₁ =>
    sv_unch U₁ h7 hn hi (apart_callW h7 hi h₁)
  -- `X = XM · 1`.
  refine WP.seq (WP.mono (slMul_ok hc.fp hc.fpk hc.fpm h7 K₁.ws (o := X) (a := XM) (b := ONE) (by decide)
    (by decide) (by decide) (by rw [v₁ (by decide) (by decide), hone]; omega_arith)) fun s₂ ⟨k₂, U₂, lt₂, e₂⟩ => ?_)
  have K₂ := K₁.step h7 k₂ (hU := U₂) (hW := fixedOk_callW h7 (by decide)) (hWs := callW_le h7 (by decide))
  have v₂ : ∀ {i}, i < 45 → i ≠ XM → i ≠ X → sv c base s₂ i = sv c base s i := fun hi h₁ h₂ =>
    (sv_unch U₂ h7 hn hi (apart_callW h7 hi h₂)).trans (v₁ hi h₁)
  have x₂ : Fin.ofNat c.C.p (sv c base s₂ X) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) := by
    rw [toM_one_mul hpR (by rw [e₂, v₁ (i := ONE) (by decide) (by decide), hone]), toM_mul hpR e₁]
  have fl₂ : flagW c base s₂ = flagW c base s := by
    simp only [flagW]
    rw [flag_callW h0 h7 (o := X) (by decide) U₂, flag_callW h0 h7 (o := XM) (by decide) U₁]
  rw [List.append_assoc]
  refine wp_append (WP.mono (checkRange_ok c K₂.ws.ws K₂.ws.at3 (sl_al c D) h0
    (by have := sl_le c h7 (i := D) (by decide); omega_arith) (by have := sl_le c h7 (i := MN) (by decide); omega_arith) hfl)
    fun s₅ ⟨f₅, k₅, O₅⟩ => ?_)
  have K₅ := K₂.step h7 (k₅.rk (rs' := [.r0, .r4, .r5, .r6, .r7, .r8, .r9])) (hU := O₅.unch) (hW := fixedOk_flag)
    (hWs := by intro w hw; rw [List.mem_singleton.mp hw]; exact hfl)
  refine wp_append (WP.mono (checkNonzero_ok c K₅.ws.ws K₅.ws.at3 (sl_al c RZ) h0
    (by have := sl_le c h7 (i := RZ) (by decide); omega_arith) hfl) fun s₆ ⟨f₆, k₆, O₆⟩ => ?_)
  have K₆ := K₅.step h7 (k₆.rk (rs' := [.r4, .r5])) (hU := O₆.unch) (hW := fixedOk_flag) (hWs := by
    intro w hw; rw [List.mem_singleton.mp hw]; exact hfl)
  have e₆ : ∀ {i}, i < 45 → i ≠ FLAG → sv c base s₆ i = sv c base s₂ i := fun hi hif =>
    (sv_unch O₆.unch h7 hn hi (apart_flag h0 hif)).trans (sv_unch O₅.unch h7 hn hi (apart_flag h0 hif))
  have hMN : wordsVal s₂.mem base (c.sl MN) c.n = c.C.n := K₂.fixed.mn
  have z₅ : wordsVal s₅.mem base (c.sl RZ) c.n = sv c base s RZ :=
    (sv_unch O₅.unch h7 hn (i := RZ) (by decide) (apart_flag h0 (by decide))).trans
      (v₂ (by decide) (by decide) (by decide))
  have d₂ : wordsVal s₂.mem base (c.sl D) c.n = sv c base s D := v₂ (by decide) (by decide) (by decide)
  have hflag₆ : flagW c base s₆ = mask64 (ok c base s V = true) := by
    rw [f₆, f₅, fl₂, hflag, hMN, z₅, d₂, mask64_and, mask64_and]
    simp only [ok, decide_eq_true_eq]
  refine WP.mono (ecFinish_ok hc K₆.ws (by rw [K₆.r14]) hofit (by rw [K₆.rk.wr]; exact hw) hd _ hflag₆)
    fun s' ⟨bytes, r3, lr, r14, r31, rk, out⟩ => ?_
  have x₆ : sv c base s₆ X = sv c base s₂ X := e₆ (by decide) (by decide)
  have hsv := K₆.fixed.saved
  refine ⟨_, lt₂, x₂, by rw [bytes, x₆], r3, ?_, by rw [rk.sp, K₆.rk.sp],
    by rw [lr, K₆.fixed.savedLr], s₆.mem, K₆.whole, out⟩
  intro r hr
  have hcases : ∀ r ∈ preserved, r = .r14 ∨ r = .r31 ∨
      (r ∉ [Reg.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31] ∧ r ∉ work) := by decide
  rcases hcases r hr with rfl | rfl | ⟨h₁, h₂⟩
  · rw [r14]; exact hsv (.r14, 0) (by decide)
  · rw [r31]; exact hsv (.r31, 8) (by decide)
  · rw [rk.gpr r h₁, K₆.rk.gpr r h₂]

/-- The arguments: `out` (`len` bytes), `d` (`len` bytes), `peer`
(`1 + 2 len` bytes) and `scratch`, readable and writable as the contract
says and apart from each other as it says. -/
structure EPre (c : Cfg) (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r4, c.C.len⟩, ⟨s.gpr .r5, 1 + 2 * c.C.len⟩]
  wr : s.wr = [⟨s.gpr .r3, c.C.len⟩, ⟨s.gpr .r6, size⟩]
  out_sc : Region.Disjoint ⟨s.gpr .r3, c.C.len⟩ ⟨s.gpr .r6, size⟩
  d_sc : Region.Disjoint ⟨s.gpr .r4, c.C.len⟩ ⟨s.gpr .r6, size⟩
  peer_sc : Region.Disjoint ⟨s.gpr .r5, 1 + 2 * c.C.len⟩ ⟨s.gpr .r6, size⟩
  out_fit : (s.gpr .r3).toNat + c.C.len ≤ 2 ^ 64
  d_fit : (s.gpr .r4).toNat + c.C.len ≤ 2 ^ 64
  peer_fit : (s.gpr .r5).toNat + (1 + 2 * c.C.len) ≤ 2 ^ 64
  sc_fit : (s.gpr .r6).toNat + size ≤ 2 ^ 64

theorem EPre.setup {s : State} (hp : EPre c s) : SetupPre c Impl.Ecdh.PPC64LE.Args.ecdh s where
  shift := .inl rfl
  k_reg := by decide
  d_reg := by decide
  e_reg := by decide
  sc_reg := by decide
  wr := by show (⟨s.gpr .r6, size⟩ : Region) ∈ s.wr; rw [hp.wr]; simp
  sc_fit := hp.sc_fit
  k_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.d_fit; omega_arith)
  d_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.d_fit; omega_arith)
  e_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.d_fit; omega_arith)
  k_sc := hp.d_sc
  d_sc := hp.d_sc
  e_sc := hp.d_sc
  k_fit := hp.d_fit
  d_fit := hp.d_fit
  e_fit := hp.d_fit

/-- The private key. -/
abbrev dk (c : Cfg) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r4) c.C.len)

/-- The result the contract asks for: the specification's shared secret, and
`1`, or zeros and `0`. -/
def EPost (c : Cfg) (s₀ s' : State) : Prop :=
  match Spec.Ecdh.exchange c.C (dk c s₀) (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r5) (1 + 2 * c.C.len)) with
  | some z => s'.gpr .r3 = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (s₀.gpr .r3) c.C.len = z
  | none => s'.gpr .r3 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (s₀.gpr .r3) c.C.len = List.replicate c.C.len 0

/-- What the function keeps: the callee-saved registers, `sp` and `lr`, and
memory but the working space and `out`. -/
structure EKeep (c : Cfg) (s₀ s' : State) : Prop where
  saved : ∀ r ∈ preserved, s'.gpr r = s₀.gpr r
  sp : s'.sp = s₀.sp
  lr : s'.lr = s₀.lr
  frame : ∃ m : Mem, Unch (s₀.gpr .r6) [(0, size)] s₀.mem m ∧ Outside (s₀.gpr .r3) 0 c.C.len m s'.mem

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

theorem exchange_eq' (c : Cfg) : Impl.Ecdh.PPC64LE.Cfg.exchange c =
    .seq (.block (c.setupWith Impl.Ecdh.PPC64LE.Args.ecdh ++ [mov .r12 .r5]))
      (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) (.seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n))
      (.seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n))
      (.seq (.block (Impl.Ecdh.PPC64LE.Cfg.peerAt c .r12)) (.seq (Impl.Ecdh.PPC64LE.Cfg.validate c)
      (.seq (Point.ladderP (ladderAt c PX PY) c.SP) (.seq (pow c.powP c.SP) (Impl.Ecdh.PPC64LE.Cfg.middle c)))))))) :=
  rfl

/-- `vg_ecdh_<curve>` computes the specification's shared secret and restores
the callee-saved registers and `lr`. -/
theorem exchange_ok (hc : CfgOk c) (h3 : 3 ≤ c.n) (hC : Law c.C) {s₀ : State} (hp : EPre c s₀) :
    WP isa (Impl.Ecdh.PPC64LE.Cfg.exchange c) s₀ fun s' => EKeep c s₀ s' ∧ EPost c s₀ s' := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hlhi := hc.len_hi
  have hl8 := hc.len8
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hsz : size = 8192 := rfl
  rw [exchange_eq']
  -- The setup, and `peer` to `r12`.
  refine WP.seq (wp_append (WP.mono (stage₀' hc hp.setup) fun s₁ ⟨S₁, kp₁⟩ =>
    wp_step exec_mov (WP.block_nil ?_)))
  generalize hb : s₀.gpr .r6 = base at S₁
  replace S₁ : St₀ c Impl.Ecdh.PPC64LE.Args.ecdh s₀ base (BitVec.allOnes 64) s₁ := S₁
  have hn := S₁.ws.nowrap
  have kw : Kp [.r12] s₁ (s₁.write .r12 (s₁.gpr .r5)) := Kp.write _ _ (by decide)
  have S₁' : St₀ c Impl.Ecdh.PPC64LE.Args.ecdh s₀ base (BitVec.allOnes 64) (s₁.write .r12 (s₁.gpr .r5)) :=
    ⟨S₁.toKeep.step h7 (kw.rk (rs' := [.r12])) (W := []) (hU := Unch.refl _ _ _) (hW := fun _ h => absurd h List.not_mem_nil)
      (hWs := fun _ h => absurd h List.not_mem_nil),
      S₁.k, S₁.d, S₁.e, S₁.rx, S₁.ry, S₁.rz, S₁.expp, S₁.expn, S₁.flag⟩
  have r12₁ : (s₁.write .r12 (s₁.gpr .r5)).gpr .r12 = s₀.gpr .r5 := by
    simp only [write_gpr, ite_true]; exact kp₁.gpr _ (by decide)
  -- The tables of bits.
  refine tables_ok hc S₁' fun s₂ S₂ kb => ?_
  have r12₂ : s₂.gpr .r12 = s₀.gpr .r5 := by rw [kb.gpr _ (by decide), r12₁]
  have W₂ : Outside base 0 size s₀.mem s₂.mem :=
    S₂.whole.outside fun w hw => by rw [List.mem_singleton.mp hw]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  have hpsc : Region.Disjoint ⟨s₀.gpr .r5, 1 + 2 * c.C.len⟩ ⟨base, size⟩ := by rw [← hb]; exact hp.peer_sc
  -- The peer's key.
  refine WP.seq (WP.mono (peer_ok hc S₂.ws (q := .r12) (by decide)
    (by rw [r12₂]; exact hp.peer_fit) (by rw [r12₂, S₂.rk.rd, S₂.rk.wr, hp.rd]; simp)
    (by rw [r12₂]; exact hpsc) S₂.fixed.mp) fun s₃ ⟨hw₃, k₃, U₃, r2₃, bp₃, x₃, y₃, f₃⟩ => ?_)
  rw [r12₂] at x₃ y₃ f₃
  have hl₃ : ∀ i ∈ [R2P, BP, E, QY], i < 45 := by decide
  have K₃ := S₂.toKeep.step h7 (k₃.rk (rs' := peerClob)) (hU := U₃)
    (hW := (fixedOk_slW (by decide)).append fixedOk_flag)
    (hWs := le_append (fun w hw => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      have := sl_le c h7 (hl₃ i hi); dsimp only; omega_arith)
      (fun w hw => by
        rw [List.mem_singleton.mp hw]; have := sl_le c h7 (i := FLAG) (by decide); dsimp only; omega_arith))
  have e₃ : ∀ {i}, i < 45 → i ∉ [R2P, BP, E, QY] → i ≠ FLAG → sv c base s₃ i = sv c base s₂ i :=
    fun hi hl hf => sv_unch U₃ h7 hn hi (apart_append (apart_slW hl) (apart_flag h0 hf))
  have hq0 : s₂.mem (s₀.gpr .r5) = s₀.mem (s₀.gpr .r5) := by
    have := keep_of_disjoint' W₂ hpsc (by omega_arith) (i := 0) (by omega_arith) (by omega_arith)
    rwa [BitVec.add_zero] at this
  -- What the code checks of the peer's key so far.
  have hf₃ : flagW c base s₃ = mask64 ((s₀.mem (s₀.gpr .r5) = 4 ∧ sv c base s₃ E < c.C.p) ∧
      sv c base s₃ QY < c.C.p) := by
    rw [f₃, hq0, S₂.flag, BitVec.allOnes_and, mask64_and, mask64_and]
  refine WP.seq (WP.mono (validate_ok hc K₃.ws K₃.fixed r2₃ bp₃ hf₃)
    fun s₄ ⟨hw₄, k₄, U₄, f₄, px_lt, py_lt, px, py⟩ => ?_)
  have K₄ := K₃.step h7 k₄ (hU := U₄) (hW := fixedOk_valW h7) (hWs := valW_le h7)
  have e₄ : ∀ {i}, i < 45 → i ∉ [QXM, QYM, W0, W1, W2, W3, PY] → i ≠ FLAG → sv c base s₄ i = sv c base s₃ i :=
    fun hi hl hf => sv_unch U₄ h7 hn hi (apart_append (apart_slW hl)
      (show ∀ w ∈ [(own c.n, 64 * c.n)] ++ [(c.sl FLAG, 8)], _ from
        apart_append (apart_own h7 hi) (apart_flag h0 hf)))
  have t₄ : ∀ {j}, j < 3 → ∀ t < 64 * c.n,
      s₄.mem (off base (bitsAt c.n j + t)) = s₂.mem (off base (bitsAt c.n j + t)) :=
    fun hj t ht => by
      rw [tbl_unch U₄ h7 hj ht (tbl_apart_valW h7 h0 _ t),
        tbl_unch U₃ h7 hj ht (apart_append (tbl_apart_slW h7 (by decide) _ t) (tbl_apart_flag h7 h0 _ t))]
  have hkv : kv c Impl.Ecdh.PPC64LE.Args.ecdh s₀ = dk c s₀ := Nat.shiftRight_zero
  have hdv : dv c Impl.Ecdh.PPC64LE.Args.ecdh s₀ = dk c s₀ := Nat.shiftRight_zero
  have r₄ : ∀ {i}, i ∈ [RX, RY, RZ, D] → sv c base s₄ i = sv c base s₂ i := fun hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;>
      rw [e₄ (by decide) (by decide) (by decide), e₃ (by decide) (by decide) (by decide)]
  -- `[d]P`, then `Z^(p-2)`.
  refine ladPow_ok hc h3 hC (gx := PX) (gy := PY) (by decide) (by decide) (by decide) (by decide) K₄ (k := dk c s₀)
    (ofBytes_bytesAt_lt _ _ _) (by rw [r₄ (by simp)]; exact S₂.rx) (by rw [r₄ (by simp)]; exact S₂.ry)
    (by rw [r₄ (by simp)]; exact S₂.rz)
    (fun t ht => by rw [t₄ (j := 0) (by decide) t ht, S₂.t₀ t ht, hkv])
    (fun t ht => by rw [t₄ (j := 1) (by decide) t ht, S₂.t₁ t ht])
    (peerPt_onCurve hc _ _ _)
    (peerPt_rep hC _ _ _ px py |> fun h => by
      show Rep c.C (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₄ PX))
        (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₄ PY))
        (toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₄.mem base (c.sl ONEP) c.n)) _
      rw [K₄.fixed.onep, toM_one hpR]; exact h) px_lt py_lt fun s₅ L => ?_
  refine WP.mono (middle_ok hc L.toKeep L.acc_lt (L.flag.trans f₄) hp.out_fit (by rw [hp.wr]; simp)
    (by rw [← hb]; exact hp.out_sc))
    fun s' ⟨xv, hxl, hxv, bytes, ret, saved, sp, lr, m, Wm, Om⟩ => ⟨⟨saved, sp, lr, m, by rw [hb]; exact Wm, Om⟩, ?_⟩
  -- The specification.
  have hlen : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r5) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
    rw [length_bytesAt]; omega_arith
  have hb0 : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r5) (1 + 2 * c.C.len)).head? = some (s₀.mem (s₀.gpr .r5)) := by
    rw [peer_bytes]; rfl
  have hxs : ofBytes (((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r5) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
      sv c base s₃ E := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _), x₃,
      bytesAt_keep W₂ (hpsc.sub_left (Offset.sub_base _ (by omega_arith))) (by omega_arith) (by omega_arith)]
  have hys : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r5) (1 + 2 * c.C.len)).drop (c.C.len + 1)) =
      sv c base s₃ QY := by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _), y₃,
      bytesAt_keep W₂ (hpsc.sub_left (Offset.sub_base _ (by omega_arith))) (by omega_arith) (by omega_arith)]
  have hP' : ∀ h : Valid c.C (s₀.mem (s₀.gpr .r5)) (sv c base s₃ E) (sv c base s₃ QY),
      peerPt c (s₀.mem (s₀.gpr .r5) = 4) (sv c base s₃ E) (sv c base s₃ QY) =
        .affine ⟨_, h.2.1⟩ ⟨_, h.2.2.1⟩ := fun h => by
    unfold peerPt; rw [dite_eq_left ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩]
  have hR := L.rep
  have hxoX : Fin.ofNat c.C.p xv = tmv c.C c.n base s₅ (c.sl RX) *
      tmv c.C c.n base s₅ (c.sl RZ) ^ (c.C.p - 2) := by rw [hxv, L.acc]
  have hspec := exchange_eq hC hlen hb0 hxs hys hP' hR hxl hxoX
  have hD₅ : sv c base s₅ D = dk c s₀ := by
    rw [L.same (by decide) (by decide), r₄ (by simp), S₂.d, hdv]
  have hz : tmv c.C c.n base s₅ (c.sl RZ) ≠ 0 ↔ sv c base s₅ RZ ≠ 0 :=
    not_congr (toM_eq_zero_iff hpR L.rz_lt)
  unfold EPost
  rw [hspec]
  by_cases hcond : (1 ≤ dk c s₀ ∧ dk c s₀ < c.C.n) ∧
      Valid c.C (s₀.mem (s₀.gpr .r5)) (sv c base s₃ E) (sv c base s₃ QY) ∧
      tmv c.C c.n base s₅ (c.sl RZ) ≠ 0
  · have hok : ok c base s₅ (PeerOk c base s₃ ((s₀.mem (s₀.gpr .r5) = 4 ∧
        sv c base s₃ E < c.C.p) ∧ sv c base s₃ QY < c.C.p)) = true := by
      refine decide_eq_true ⟨⟨⟨⟨⟨hcond.2.1.1, hcond.2.1.2.1⟩, hcond.2.1.2.2.1⟩, hcond.2.1.2.2.2⟩, ?_, ?_⟩,
        hz.mp hcond.2.2⟩
      · rw [hD₅]; exact hcond.1.1
      · rw [hD₅]; exact hcond.1.2
    rw [ite_eq_left hcond]
    exact ⟨by rw [ret, hok]; rfl, by rw [bytes, hok]; rfl⟩
  · have hok : ok c base s₅ (PeerOk c base s₃ ((s₀.mem (s₀.gpr .r5) = 4 ∧
        sv c base s₃ E < c.C.p) ∧ sv c base s₃ QY < c.C.p)) = false := by
      refine decide_eq_false fun h => hcond ⟨⟨?_, ?_⟩, ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2⟩,
        hz.mpr h.2⟩
      · rw [← hD₅]; exact h.1.2.1
      · rw [← hD₅]; exact h.1.2.2
    rw [ite_eq_right hcond]
    exact ⟨by rw [ret, hok]; rfl, by rw [bytes, hok]; rfl⟩

end VG.Proof.Ecdh.PPC64LE
