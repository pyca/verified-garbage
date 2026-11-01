module

import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Scalar
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.Ecdsa
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Finish
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Flags
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Setup
import VerifiedGarbage.Proof.EcKey.PPC64LE.Finish
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.BytesLen
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Keep
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Middle
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.LadPow
public import VerifiedGarbage.Proof.Weierstrass.MulContract

/-!
# ECDSA signatures on PPC64LE: the whole function

As on 32-bit ARM (`Proof/Ecdsa/Arm/Main.lean`). `signFinish_ok`: `r ‖ s`
or zeros to `out`, the return value and the callee-saved registers;
`stage₄`: `s`, its check and the result; `sign_ok`: `Cfg.sign` computes
the specification's signature, for any curve the proof of the code supports
(`CfgOk`, coordinates of 3 to 6 words) whose group law the proofs support
(`Law`), restores the callee-saved registers and `lr`, and changes memory
only in the working space and `out`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Weierstrass.PPC64LE.Point VG.Spec.Weierstrass
open VG.Proof.EcKey.PPC64LE (toNat_add_of)

variable {c : Cfg}

theorem finish_eq' (c : Cfg) : c.finish =
    ([.load .d .r10 wb (c.sl FLAG)] : List Instr) ++ (storeBytes c.C.len c.n .r14 0 (c.sl RR) ++
    (storeBytes c.C.len c.n .r14 c.C.len (c.sl SS) ++
    (.li .r4 1 :: .logic .and .r4 .r10 .r4 :: (Cfg.restore ++ [mov .r3 .r4])))) := by
  simp only [Cfg.finish, List.append_assoc, List.cons_append, List.nil_append]

/-- The signature, the return value and the callee-saved registers. -/
theorem signFinish_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base) {out : Addr}
    (h14 : s.gpr .r14 = out) (hofit : out.toNat + 2 * c.C.len ≤ 2 ^ 64)
    (hwr : (⟨out, 2 * c.C.len⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨out, 2 * c.C.len⟩ ⟨base, size⟩) (b : Bool)
    (hf : flagW c base s = mask64 (b = true)) :
    WP isa (.block c.finish) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem out (2 * c.C.len) =
        (if b then toBytes c.C.len (sv c base s RR) ++ toBytes c.C.len (sv c base s SS)
          else List.replicate (2 * c.C.len) 0) ∧
      s'.gpr .r3 = (if b then 1 else 0) ∧
      s'.lr = word s.mem base Cfg.lrAt ∧ s'.gpr .r14 = word s.mem base 0 ∧ s'.gpr .r31 = word s.mem base 8 ∧
      Rk [.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31] s s' ∧
      Outside out 0 (2 * c.C.len) s.mem s'.mem := by
  have h7 := hc.n10
  have hl8 := hc.len8
  have hlhi := hc.len_hi
  have hllo := hc.len_lo
  have hn := hw.nowrap
  have hsz : size = 8192 := rfl
  have hX := sl_le c h7 (i := RR) (by decide)
  have hY := sl_le c h7 (i := SS) (by decide)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  have hs := hw.ws
  have h3 := hw.at3
  have hdsc : ∀ {a d : Nat}, a + 8 * c.n ≤ size → d + c.C.len ≤ 2 * c.C.len →
      Region.Disjoint ⟨off base a, 8 * c.n⟩ ⟨out + BitVec.ofNat 64 d, c.C.len⟩ := fun ha hd' =>
    (hd.symm.sub_left (Offset.sub_base base ha)).sub_right (Offset.sub_base out hd')
  have hin : ∀ {d e m : Nat}, d + e + m ≤ 2 * c.C.len →
      InRegions s.wr (out + BitVec.ofNat 64 d + BitVec.ofNat 64 e) m := fun hd' =>
    ⟨_, hwr, by rw [Offset.add_add]; exact Offset.contains_base out hd' (by omega_arith)⟩
  rw [finish_eq', List.singleton_append]
  refine wp_step (ld0_ok hs h3 (by decide) (sl_al c FLAG) (by omega_arith)) ?_
  have hs₁ := hs.write .r10 (word s.mem base (c.sl FLAG))
  have h3₁ := h3.write (d := .r10) (word s.mem base (c.sl FLAG))
  have hc₁ : (s.write .r10 (word s.mem base (c.sl FLAG))).gpr .r10 = if b then BitVec.allOnes 64 else 0 := by
    simp only [write_gpr, ite_true]; rw [← flagW, hf]
  have hb₁ : (s.write .r10 (word s.mem base (c.sl FLAG))).gpr .r14 = out := by
    simp only [write_gpr, reduceCtorEq, ite_false]; exact h14
  -- `r`, from `out`.
  refine wp_append (WP.mono (storeBytes_ok hs₁ h3₁ (dst := .r14) (d := 0) (a := c.sl RR) (by decide) (by decide)
    (by decide) (by decide) b hc₁ (by omega_arith) (sl_al c RR) (by omega_arith) (by omega_arith) hlhi (by omega_arith)
    (by rw [hb₁, toNat_add_of (by omega_arith)]; omega_arith) (fun e m he => by rw [hb₁]; exact hin (by omega_arith))
    (by rw [hb₁]; exact hdsc (by omega_arith) (by omega_arith))) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_)
  rw [hb₁] at e₂ O₂
  have U₂ := O₂.unch_far (hd.symm.sub_right (Offset.sub_base out (d := 0) (n := c.C.len) (by omega_arith)))
  have hb₂ : s₂.gpr .r14 = out := by rw [k₂.g, hb₁]
  have hc₂ : s₂.gpr .r10 = if b then BitVec.allOnes 64 else 0 := by rw [k₂.g, hc₁]
  have y₂ : wordsVal s₂.mem base (c.sl SS) c.n = sv c base s SS :=
    U₂.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega_arith) (by omega_arith)
  -- `s`, from `out + len`.
  refine wp_append (WP.mono (storeBytes_ok (k₂.ws hs₁) (k₂.at h3₁) (dst := .r14) (d := c.C.len) (a := c.sl SS)
    (by decide) (by decide) (by decide) (by decide) b hc₂ (by omega_arith) (sl_al c SS) (by omega_arith) (by omega_arith) hlhi (by omega_arith)
    (by rw [hb₂, toNat_add_of (by omega_arith)]; omega_arith) (fun e m he => by rw [k₂.wr, hb₂]; exact hin (by omega_arith))
    (by rw [hb₂]; exact hdsc (by omega_arith) (by omega_arith))) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_)
  rw [hb₂, y₂] at e₃
  rw [hb₂] at O₃
  have U₃ := O₃.unch_far (hd.symm.sub_right (Offset.sub_base out (d := c.C.len) (n := c.C.len) (by omega_arith)))
  have hsv : ∀ d, d + 8 ≤ 24 → word s₃.mem base d = word s.mem base d := fun d hd' => by
    rw [U₃.word (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega_arith) (by omega_arith),
      U₂.word (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega_arith) (by omega_arith)]
    rfl
  have hs₃ := k₃.ws (k₂.ws hs₁)
  have h3₃ := k₃.at (k₂.at h3₁)
  -- The return value and the callee-saved registers.
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_logic ?_
  refine restore_ok ((hs₃.write _ _).write _ _) ((h3₃.write _).write _) (by omega_arith) fun t Kt mt lrt r14t r31t => ?_
  refine wp_step exec_mov (WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  · have rs : Spec.Ecdsa.bytesAt s₃.mem out c.C.len =
        if b then toBytes c.C.len (sv c base s RR) else List.replicate c.C.len 0 := by
      rw [bytesAt_keep O₃ (Offset.base_disjoint out (Nat.le_refl _) (by omega_arith)) (by omega_arith) (by omega_arith)]
      rw [BitVec.add_zero] at e₂; exact e₂
    simp only [write_mem]
    rw [mt]
    simp only [write_mem]
    rw [show 2 * c.C.len = c.C.len + c.C.len by omega_arith, bytesAt_add, rs, e₃]
    cases b
    · simp only [Bool.false_eq_true, ite_false, List.replicate_append_replicate]
    · simp only [ite_true]
  · simp only [write_gpr, ite_true]
    rw [Kt.gpr _ (by decide)]
    simp only [write_gpr, ite_true, reduceCtorEq, ite_false]
    rw [k₃.g, hc₂, ← mask_bit]
  · simp only [write_lr]; rw [lrt]; simp only [write_mem]; exact hsv _ (by decide)
  · simp only [write_gpr, reduceCtorEq, ite_false]; rw [r14t]; simp only [write_mem]; exact hsv _ (by decide)
  · simp only [write_gpr, reduceCtorEq, ite_false]; rw [r31t]; simp only [write_mem]; exact hsv _ (by decide)
  · have R₁ : Rk [.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31] s s₃ :=
      (((Kp.write s (d := .r10) _ (rs := [.r10]) (by decide)).rk).trans
        (k₂.rk (rs' := [.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31]))).trans
        (k₃.rk (rs' := [.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31]))
    exact ((R₁.trans (((Kp.write s₃ (d := .r4) (BitVec.ofNat 64 1) (rs := [.r4]) (by decide)).trans
      (Kp.write _ (d := .r4) _ (rs := [.r4]) (by decide))).rk)).trans (Kt.mono (by decide))).trans
      ((Kp.write t (d := .r3) _ (rs := [.r3]) (by decide)).rk)
  · simp only [write_mem]
    rw [mt]
    simp only [write_mem]
    rw [BitVec.add_zero] at O₂
    exact (O₂.mono (Nat.zero_le _) (by omega_arith)).trans ((outside_shift O₃ (by omega_arith)).mono (Nat.zero_le _)
      (by omega_arith))

/-- What the function needs: `d`, the hash and `k` readable, `out` and the
working space writable, the working space apart from all of them. -/
structure Pre (c : Cfg) (s : State) (extra : List Region := []) : Prop where
  rd : s.rd = [⟨s.gpr .r4, c.C.len⟩, ⟨s.gpr .r5, c.C.len⟩, ⟨s.gpr .r6, c.C.len⟩] ++ extra
  wr : s.wr = [⟨s.gpr .r3, 2 * c.C.len⟩, ⟨s.gpr .r7, size⟩]
  out_sc : Region.Disjoint ⟨s.gpr .r3, 2 * c.C.len⟩ ⟨s.gpr .r7, size⟩
  d_sc : Region.Disjoint ⟨s.gpr .r4, c.C.len⟩ ⟨s.gpr .r7, size⟩
  digest_sc : Region.Disjoint ⟨s.gpr .r5, c.C.len⟩ ⟨s.gpr .r7, size⟩
  k_sc : Region.Disjoint ⟨s.gpr .r6, c.C.len⟩ ⟨s.gpr .r7, size⟩
  out_fit : (s.gpr .r3).toNat + 2 * c.C.len ≤ 2 ^ 64
  d_fit : (s.gpr .r4).toNat + c.C.len ≤ 2 ^ 64
  digest_fit : (s.gpr .r5).toNat + c.C.len ≤ 2 ^ 64
  k_fit : (s.gpr .r6).toNat + c.C.len ≤ 2 ^ 64
  sc_fit : (s.gpr .r7).toNat + size ≤ 2 ^ 64

theorem Pre.setup {s : State} {extra : List Region} (hp : Pre c s extra) : SetupPre c Args.sign s where
  shift := .inr (.inr rfl)
  k_reg := by decide
  d_reg := by decide
  e_reg := by decide
  sc_reg := by decide
  wr := by show (⟨s.gpr .r7, size⟩ : Region) ∈ s.wr; rw [hp.wr]; simp
  sc_fit := hp.sc_fit
  k_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.k_fit; omega_arith)
  d_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.d_fit; omega_arith)
  e_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.digest_fit; omega_arith)
  k_sc := hp.k_sc
  d_sc := hp.d_sc
  e_sc := hp.digest_sc
  k_fit := hp.k_fit
  d_fit := hp.d_fit
  e_fit := hp.digest_fit

/-- The hash's integer is the bytes shifted as the setup shifts them. -/
theorem hashToInt_eq (c : Cfg) (m : Mem) (q : Addr) :
    Spec.Ecdsa.hashToInt c.C (Spec.Ecdsa.bytesAt m q c.C.len) =
      ofBytes (Spec.Ecdsa.bytesAt m q c.C.len) >>> c.sh := by
  simp only [Spec.Ecdsa.hashToInt, length_bytesAt, Cfg.sh]
  split
  · rw [show 8 * c.C.len - Spec.Ecdsa.nBits c.C = 0 by omega_arith, Nat.shiftRight_zero]
  · rfl

/-- The result the contract asks for: the specification's signature of the
hash with `d` and `k`, big-endian, and `1`, or zeros and `0`. -/
def SignPost (c : Cfg) (s₀ s' : State) : Prop :=
  match Spec.Ecdsa.signWith c.C (ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r4) c.C.len))
      (Spec.Ecdsa.hashToInt c.C (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r5) c.C.len))
      (ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r6) c.C.len)) with
  | some rs => s'.gpr .r3 = 1 ∧
      Spec.Ecdsa.bytesAt s'.mem (s₀.gpr .r3) (2 * c.C.len) = Spec.Ecdsa.encode c.C rs
  | none => s'.gpr .r3 = 0 ∧
      Spec.Ecdsa.bytesAt s'.mem (s₀.gpr .r3) (2 * c.C.len) = List.replicate (2 * c.C.len) 0

/-- What the function keeps: the callee-saved registers, `sp` and `lr`, and
memory but the working space and `out`. -/
structure SignKeep (c : Cfg) (s₀ s' : State) : Prop where
  saved : ∀ r ∈ preserved, s'.gpr r = s₀.gpr r
  sp : s'.sp = s₀.sp
  lr : s'.lr = s₀.lr
  frame : ∃ m : Mem, Unch (s₀.gpr .r7) [(0, size)] s₀.mem m ∧ Outside (s₀.gpr .r3) 0 (2 * c.C.len) m s'.mem

/-- `s`, its check, and the result. -/
theorem stage₄ (hc : CfgOk c) (hC : Law c.C) {s₀ : State} {extra : List Region} (hp : Pre c s₀ extra)
    {s : State} (S : St₃ c .sign s₀ (s₀.gpr .r7) (BitVec.allOnes 64) (G c.C) s) :
    WP isa c.scalar s fun s' => SignKeep c s₀ s' ∧ SignPost c s₀ s' := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := S.ws.nowrap
  have hsz : size = 8192 := rfl
  have hfl : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_arith
  rw [scalar_eq]
  refine scOps_ok hc S.toKeep fun s₇ Sc => ?_
  refine wp_append (WP.mono (checkNonzero_ok c Sc.ws.ws Sc.ws.at3 (sl_al c SS) h0
    (by have := sl_le c h7 (i := SS) (by decide); omega_arith) hfl) fun s₈ ⟨f₈, k₈, O₈⟩ => ?_)
  have K₈ := Sc.toKeep.step h7 (k₈.rk (rs' := [.r4, .r5])) (hU := O₈.unch) (hW := fixedOk_flag) (hWs := by
    intro w hw; rw [List.mem_singleton.mp hw]; exact hfl)
  have e₈ : ∀ {i}, i < 45 → i ≠ FLAG → sv c (s₀.gpr .r7) s₈ i = sv c (s₀.gpr .r7) s₇ i := fun hi hf =>
    sv_unch O₈.unch h7 hn hi (apart_flag h0 hf)
  -- The flag.
  have hflag : flagW c (s₀.gpr .r7) s₈ =
      mask64 (decide ((((0 < dv c .sign s₀ ∧ dv c .sign s₀ < c.C.n) ∧ (0 < kv c .sign s₀ ∧ kv c .sign s₀ < c.C.n)) ∧
        sv c (s₀.gpr .r7) s X % c.C.n ≠ 0) ∧ sv c (s₀.gpr .r7) s₇ SS ≠ 0) = true) := by
    rw [f₈, Sc.flag, S.flag, BitVec.allOnes_and, mask64_and, mask64_and, mask64_and]
    simp only [mask64, decide_eq_true_eq]
  have hw : (⟨s₀.gpr .r3, 2 * c.C.len⟩ : Region) ∈ s₈.wr := by
    rw [K₈.rk.wr, hp.wr]; simp
  refine WP.mono (signFinish_ok hc K₈.ws (by rw [K₈.r14]) hp.out_fit hw hp.out_sc _ hflag)
    fun s' ⟨bytes, r3, lr, r14, r31, rk, out⟩ => ⟨⟨?_, by rw [rk.sp, K₈.rk.sp],
      by rw [lr, K₈.fixed.savedLr], s₈.mem, K₈.whole, out⟩, ?_⟩
  · intro r hr
    have hcases : ∀ r ∈ preserved, r = .r14 ∨ r = .r31 ∨
        (r ∉ [Reg.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31] ∧ r ∉ work) := by decide
    rcases hcases r hr with rfl | rfl | ⟨h₁, h₂⟩
    · rw [r14]; exact K₈.fixed.saved (.r14, 0) (by decide)
    · rw [r31]; exact K₈.fixed.saved (.r31, 8) (by decide)
    · rw [rk.gpr r h₁, K₈.rk.gpr r h₂]
  -- The specification.
  have hsig := signWith_eq hC (C := c.C) (d := dv c .sign s₀) (e := ev c .sign s₀) (k := kv c .sign s₀) S.rep
    S.x_lt S.x (s := sv c (s₀.gpr .r7) s₇ SS) Sc.ss_lt (by rw [Sc.ss, S.acc, S.rr, S.d, S.e])
  unfold SignPost
  have hd : dv c .sign s₀ = ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r4) c.C.len) := Nat.shiftRight_zero
  have hk : kv c .sign s₀ = ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r6) c.C.len) := Nat.shiftRight_zero
  have he : ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r5) c.C.len) >>> c.sh = ev c .sign s₀ :=
    congrArg (_ >>> ·) (shAt_self c E).symm
  rw [← hd, ← hk, hashToInt_eq c, he, hsig]
  have rr₈ : sv c (s₀.gpr .r7) s₈ RR = sv c (s₀.gpr .r7) s X % c.C.n := by
    rw [e₈ (by decide) (by decide), Sc.same (by decide) (by decide), S.rr]
  have ss₈ : sv c (s₀.gpr .r7) s₈ SS = sv c (s₀.gpr .r7) s₇ SS := e₈ (by decide) (by decide)
  rw [ss₈, rr₈] at bytes
  by_cases hP : 1 ≤ dv c .sign s₀ ∧ dv c .sign s₀ < c.C.n ∧ 1 ≤ kv c .sign s₀ ∧ kv c .sign s₀ < c.C.n ∧
      sv c (s₀.gpr .r7) s X % c.C.n ≠ 0 ∧ sv c (s₀.gpr .r7) s₇ SS ≠ 0
  · have hdc : decide ((((0 < dv c .sign s₀ ∧ dv c .sign s₀ < c.C.n) ∧ (0 < kv c .sign s₀ ∧ kv c .sign s₀ < c.C.n)) ∧
        sv c (s₀.gpr .r7) s X % c.C.n ≠ 0) ∧ sv c (s₀.gpr .r7) s₇ SS ≠ 0) = true := by
      simp only [decide_eq_true_eq]; omega_arith
    rw [ite_eq_left_of_eq_true _ _ (eq_true hP)]
    refine ⟨by rw [r3, hdc]; rfl, ?_⟩
    rw [bytes, hdc, ite_eq_left_of_eq_true _ _ (eq_true rfl), Spec.Ecdsa.encode]
  · have hdc : decide ((((0 < dv c .sign s₀ ∧ dv c .sign s₀ < c.C.n) ∧ (0 < kv c .sign s₀ ∧ kv c .sign s₀ < c.C.n)) ∧
        sv c (s₀.gpr .r7) s X % c.C.n ≠ 0) ∧ sv c (s₀.gpr .r7) s₇ SS ≠ 0) = false := by
      simp only [decide_eq_false_iff_not]; omega_arith
    rw [ite_eq_right_of_eq_false _ _ (eq_false hP)]
    refine ⟨by rw [r3, hdc]; rfl, ?_⟩
    rw [bytes, hdc]; rfl

theorem sign_eq (c : Cfg) : c.sign = .seq (.block (c.setupWith Args.sign))
    (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n))
    (.seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n)) (.seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n))
    (.seq (c.qMul GX GY) (.seq (pow c.powP c.SP) (.seq c.middle
      (.seq (pow c.powN c.SN) c.scalar))))))) := rfl

/-- `vg_ecdsa_<curve>_sign` computes the specification's signature, restores
the callee-saved registers and `lr`, and changes only the working space and
`out`. -/
theorem sign_ok (hc : CfgOk c) (h3 : 3 ≤ c.n) (hC : Law c.C) {s₀ : State} {extra : List Region}
    (hp : Pre c s₀ extra) :
    WP isa c.sign s₀ fun s' => SignKeep c s₀ s' ∧ SignPost c s₀ s' := by
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  rw [sign_eq]
  refine stage₁ hc hp.setup fun s₁ S₁ => ?_
  have F := S₁.fixed
  have hG : Rep c.C (tmv c.C c.n (s₀.gpr .r7) s₁ (c.sl GX)) (tmv c.C c.n (s₀.gpr .r7) s₁ (c.sl GY))
      (tmv c.C c.n (s₀.gpr .r7) s₁ (c.sl ONEP)) (G c.C) := by
    show Rep c.C (toM _ _ (wordsVal s₁.mem _ (c.sl GX) c.n)) (toM _ _ (wordsVal s₁.mem _ (c.sl GY) c.n))
      (toM _ _ (wordsVal s₁.mem _ (c.sl ONEP) c.n)) (G c.C)
    rw [F.gx, F.gy, F.onep, toM_cmont hc, toM_cmont hc, toM_one hpR]
    exact rep_affine' hC _ _
  exact stage₂ hc h3 hC (gx := GX) (gy := GY) (by decide) (by decide) (by decide) (by decide) S₁ hc.onG hG
    (lt_of_eq_of_lt F.gx (hmont _)) (lt_of_eq_of_lt F.gy (hmont _)) fun s₂ S₂ =>
      stage₃ hc S₂ fun s₃ S₃ => stage₄ hc hC hp S₃

end VG.Proof.Ecdsa.PPC64LE
