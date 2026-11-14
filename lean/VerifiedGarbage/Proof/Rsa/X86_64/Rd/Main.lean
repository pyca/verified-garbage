module
-- separate module: its proofs build in parallel with the constant-time ones, `CTBase`, `CTParts` and `CTLoops`

public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Tail
public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Entry
import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
import VerifiedGarbage.Proof.Rsa.X86_64.CvMain
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Prod
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Stages
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.TwoStages
import VerifiedGarbage.Proof.Rsa.RecoverDetWords
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Divs
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.SqrtFin
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.RootModel
import VerifiedGarbage.Proof.Rsa.RecoverRoot
import VerifiedGarbage.Proof.Rsa.X86_64.Div
import VerifiedGarbage.Proof.Rsa.KeyMath
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on x86-64: `main`

`DS`: what every piece of `main` keeps (the working space at the width the
header gives, the arguments it reads at the end, memory outside the working
space). `main`, phase by phase between the changes of width, gives the
model's values (`Proof/Rsa/RecoverDetModel.lean`), and so Appendix C.2's
factors (`rdMain_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Proof.Rsa.RecoverDet

/-! ## The prefix: the head, the loads and `d e` (narrow) -/

/-- The prefix of `main`. -/
abbrev p1 : List (Prog isa) := [.block RecoverDet.head] ++
  (loadA Impl.Bignum.X86_64.Public.aN Impl.Bignum.X86_64.Public.sN Impl.Bignum.X86_64.Public.sK ++
  ([zeroA 1] ++ (loadA Recover.aE Impl.Bignum.X86_64.Public.sE Impl.Bignum.X86_64.Public.sElen ++
  (loadA Recover.aD Recover.sD Recover.sDl ++ Recover.prod))))

/-- The prefix: the narrow width, the mask all ones, `n` (narrow arrays 0 and
1, all their words) and `d e` (wide array 5). -/
theorem phase1_ok {I : RpIn} {s : State} (h : RpPre I s) (hel8 : I.el ≤ 8) :
    WP isa (seqs p1) s fun t => DS I s.mem (nv I.k) t ∧ mw t.mem I.B = mask true ∧
      wv t.mem I.B (slot (nv I.k) 0) (2 * (nv I.k + 2)) = I.N ∧
      wv t.mem I.B (slot (nv I.k) 10) (2 * (nv I.k + 2)) = I.D * I.E := by
  have L := h.L
  have hn := h.scr.nowrap
  have hZ := L.z
  have k1 := L.k1
  have k2 := L.k2
  have ⟨bW, b26, bv, bv9⟩ := rd_bounds L.k1 L.k2 L.z
  have hZ' : 256 + 26 * (8 * (nv I.k + 2)) ≤ I.Z := b26
  unfold p1
  -- The head.
  refine wp_seqs_append (by simp) (by simp [loadA]) ?_
  rw [show seqs [Code.block RecoverDet.head] = .block (width false ++ ([.mov .rax (.imm (BitVec.ofInt 32 (-1))),
    .store (hdr Impl.Bignum.X86_64.Public.sMask) .rax] : List Instr)) from rfl]
  refine WP.block_append_iff.mpr (WP.mono (width_ok false h.scr h.rdi L.k1 L.k2 L.z h.args.k)
    fun t₀ ⟨hw₀, hf₀, k₀⟩ => ?_)
  replace hw₀ : Ws t₀ I.B I.Z (nv I.k) := hw₀
  have h256 := hw₀.h256
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = t₀.mem.writeW (off I.B (8 * Impl.Bignum.X86_64.Public.sMask))
      (mask true)) (by
    xrun [State.ea, hdr, hw₀.rdi, hdrOff, hw₀.scr.st (d := 8 * Impl.Bignum.X86_64.Public.sMask) (by p1_omega),
      sx_m1]; rfl) rfl) fun t₁ ⟨m₁, k₁⟩ => ?_
  have hw₁ := hw₀.congrW m₁ (by p1_omega) (by decide) k₁ (by simp)
  have hm₁ : FrmP I.B (fun y => 48 ≤ y ∧ y < 128 ∨ 176 ≤ y ∧ y < 184 ∨ 224 ≤ y ∧ y < 232) t₀.mem t₁.mem := by
    rw [m₁]
    refine FrmP.of_writeW _ (by p1_omega) fun y h1 h2 => ?_
    simp only [Impl.Bignum.X86_64.Public.sMask, sFn] at h1 h2
    omega_arith
  have hf₁ : FrmP I.B (fun y => 48 ≤ y ∧ y < 128 ∨ 176 ≤ y ∧ y < 184 ∨ 224 ≤ y ∧ y < 232) s.mem t₁.mem := by
    refine (FrmP.of_frm hf₀ fun r hr y h1 h2 => ?_).trans hm₁
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [sW, sArr, sStride, sFn] at h1 h2 ⊢ <;> omega_arith
  have ha₁ := h.args.congr fun i hi =>
    hf₁.word_eq (fun y h1 h2 hy => by unfold rArg at hi; omega_arith) (by unfold rArg at hi; omega_arith)
  have hi₁ : InScr I.B I.Z s.mem t₁.mem := fun x hx => hf₁ x fun hy => absurd hx (by simp only at hy; omega_arith)
  have kk₁ := k₀.trans k₁
  -- `n`, all its words.
  refine wp_seqs_append (by simp [loadA]) (by simp) (WP.mono (loadA2_ok hw₁ (j := 0) (by decide) (by decide)
    (by decide) ha₁.n ha₁.k (h.n.congrK hi₁ kk₁) L.nbl (by omega_arith) (by unfold nv wk; omega_arith))
    fun t₂ ⟨v2, o2, k2⟩ => ?_)
  have hw₂ := hw₁.congrO o2 (by p1_omega) k2 (by simp)
  have ha₂ := ha₁.out o2 (by p1_omega)
  have hi₂ : InScr I.B I.Z t₁.mem t₂.mem := InScr.of_outside o2 (by have := hw₁.sl (j := 0) (by decide); omega_arith)
  refine wp_seqs_append (a := [zeroA 1]) (by simp) (by simp [loadA]) (WP.mono (zeroA_ok hw₂ (j := 1) (by decide))
    fun t₃ ⟨z3, o3, k3⟩ => ?_)
  have hw₃ := hw₂.congrO o3 (by p1_omega) k3 (by simp)
  have ha₃ := ha₂.out o3 (by p1_omega)
  have hi₃ : InScr I.B I.Z t₂.mem t₃.mem := InScr.of_outside o3 (by have := hw₂.sl (j := 1) (by decide); omega_arith)
  have kk₃ := (kk₁.trans k2).trans k3
  have hi13 := (hi₁.trans hi₂).trans hi₃
  -- `e` and `d`.
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (loadA_ok hw₃ (j := Recover.aE) (by decide)
    (by decide) (by decide) ha₃.e ha₃.el (h.e.congrK hi13 kk₃) L.ebl L.el1 (by unfold nv wk; omega_arith))
    fun t₄ ⟨v4, o4, k4⟩ => ?_)
  have hw₄ := hw₃.congrO o4 (by p1_omega) k4 (by simp)
  have ha₄ := ha₃.out o4 (by p1_omega)
  have hi₄ : InScr I.B I.Z t₃.mem t₄.mem := InScr.of_outside o4 (by have := hw₃.sl (j := Recover.aE) (by decide); omega_arith)
  refine wp_seqs_append (by simp [loadA]) (by simp [Recover.prod]) (WP.mono (loadA_ok hw₄ (j := Recover.aD)
    (by decide) (by decide) (by decide) ha₄.d ha₄.dl (h.d.congrK (hi13.trans hi₄) ((kk₃.trans k4))) L.dbl L.dl1
    (by unfold nv wk; have := L.dl2; omega_arith)) fun t₅ ⟨v5, o5, k5⟩ => ?_)
  have hw₅ := hw₄.congrO o5 (by p1_omega) k5 (by simp)
  have ha₅ := ha₄.out o5 (by p1_omega)
  have hi₅ : InScr I.B I.Z t₄.mem t₅.mem := InScr.of_outside o5 (by have := hw₄.sl (j := Recover.aD) (by decide); omega_arith)
  -- `d e`.
  have E₅ : wv t₅.mem I.B (slot (nv I.k) Recover.aE) (nv I.k) = I.E := by rw [o5.wv (by p1_omega) (by p1_omega), v4]
  have hE : I.E < 2 ^ (64 * ((I.el + 7) / 8)) := by
    have := os2ip_lt I.eb; rw [L.ebl] at this; exact Nat.lt_of_lt_of_le this (pow256_le_wk I.el)
  refine WP.mono (prod_ok hw₅ ha₅.el L.el1 (by unfold nv wk; omega_arith) (by rw [E₅]; exact hE))
    fun t ⟨v6, o6, k6⟩ => ?_
  rw [E₅, v5] at v6
  have hw₆ := hw₅.congrO o6 (by p1_omega) k6 (by simp)
  have ha₆ := ha₅.out o6 (by p1_omega)
  have hi₆ : InScr I.B I.Z t₅.mem t.mem := InScr.of_outside o6 (by have := hw₅.sl (j := Recover.aM + 1) (by decide); simp only [Bignum.slot, hdrBytes, Recover.aM] at this ⊢; omega_arith)
  refine ⟨⟨hw₆, ha₆.p, ha₆.q, ha₆.k, ha₆.saved, ((((hi13.trans hi₄).trans hi₅).trans hi₆)), by
    rw [k6.2.2, k5.2.2, k4.2.2, kk₃.2.2, h.wr], by rw [k6.gpr (by decide), k5.gpr (by decide), k4.gpr (by decide),
    kk₃.gpr (by decide), h.rsp]⟩, ?_, ?_, ?_⟩
  · unfold mw
    rw [o6.word (by p1_omega) (by p1_omega), o5.word (by p1_omega) (by p1_omega), o4.word (by p1_omega) (by p1_omega),
      o3.word (by p1_omega) (by p1_omega), o2.word (by p1_omega) (by p1_omega), m₁, word_writeW_self]
  · have n0 : wv t.mem I.B (slot (nv I.k) 0) (nv I.k + 2) = I.N := by
      rw [o6.wv (by p1_omega) (by p1_omega), o5.wv (by p1_omega) (by p1_omega), o4.wv (by p1_omega) (by p1_omega),
        o3.wv (by p1_omega) (by p1_omega), v2]
    have n1 : wv t.mem I.B (slot (nv I.k) 1) (nv I.k + 2) = 0 := by
      rw [o6.wv (by p1_omega) (by p1_omega), o5.wv (by p1_omega) (by p1_omega), o4.wv (by p1_omega) (by p1_omega), z3]
    rw [show 2 * (nv I.k + 2) = (nv I.k + 2) + (nv I.k + 2) by omega_arith, wv_add,
      show slot (nv I.k) 0 + 8 * (nv I.k + 2) = slot (nv I.k) 1 by simp only [Bignum.slot, hdrBytes]; omega_arith,
      n0, n1, Nat.mul_zero, Nat.add_zero]
  · simp only [Recover.aM] at v6
    exact v6

/-! ## `d e - 1`, the halvings and the GCD -/

/-! ## The halvings and the GCD

`twosInit`, the halvings by stages (`twos`) and the GCD (`gcdW`), against
the model's `twoStep` (in closed form, `twos_closed`). -/

section
open VG.Proof.Rsa.RecoverDet
open VG.Proof.Bignum.ShiftStages (tz)

/-- What the halvings and the GCD change. -/
def TgP (w y : Nat) : Prop := (slot w 4 ≤ y ∧ y < slot w 8) ∨ (slot w 12 ≤ y ∧ y < slot w 26) ∨ (200 ≤ y ∧ y < 224)

macro "tg_omega" : tactic =>
  `(tactic| (simp only [TgP, DOk, Bignum.slot, hdrBytes, sCt, sU, sB2, sFn, twRs]; omega_arith))

/-- `twosInit`, the halvings and the GCD: `x` (wide array 2) doubled as `twoStep`
says, and `g = gcd(u, x₂)` in wide array 6 (narrow 12 and 13). -/
theorem twosG_ok [InvLaw] {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (hZ26 : slot w 26 ≤ Z)
    (hw20 : w < 2 ^ 20) (hw129 : w ≤ 129) {N X : Nat} (hN : wv s.mem B (slot w 0) w = N) (hN2 : 2 ≤ N)
    (hNw : N < 2 ^ (64 * (w - 1))) (hone : wv s.mem B (slot w 2) w = 1)
    (hX : wv s.mem B (slot w 4) (2 * w + 2) = X) :
    WP isa (seqs (twosInit ++ twos ++ [gcdW 6 12 7])) s fun t =>
      wv t.mem B (slot w 4) (2 * w + 2) = (twosSt w N X).2.2 ∧
      wv t.mem B (slot w 12) (2 * (w + 2)) = Nat.gcd (twosSt w N X).1 (twosSt w N X).2.1 ∧
      FrmP B (TgP w) s.mem t.mem ∧ Keep [.rax, .rbx, .rcx, .rdx, .rbp, .rsi, .r8, .r9, .r10, .r11, .r12, .r13,
        .r14, .r15] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hZ := h.hZ
  have hZ' : 256 + 26 * (8 * (w + 2)) ≤ Z := hZ26
  have hw1 := h.w1
  have hNlt : N < 2 ^ (64 * w) := Nat.lt_of_lt_of_le hNw (Nat.pow_le_pow_right (by decide) (by omega_arith))
  have hXw : X < 2 ^ (64 * (2 * w + 2)) := hX ▸ wv_lt _ _ _ _
  rw [List.append_assoc]
  refine wp_seqs_append (by simp [twosInit]) (by simp [twos, wordStages]) ?_
  simp only [twosInit, seqs]
  -- `x₂ := x mod 2^(64 w)`, its top words zero.
  refine WP.seq (WP.mono (zeroA_ok h (j := 6) (by decide)) fun t₁ ⟨z1, o1, k1⟩ => ?_)
  have h₁ := h.congrO o1 (by tg_omega) k1 (by simp)
  refine WP.seq (WP.mono (copyA_ok h₁ (o := 6) (a := 4) (by decide) (by decide) (by decide)) fun t₂ ⟨v2, o2, k2⟩ => ?_)
  have h₂ := h₁.congrO o2 (by tg_omega) k2 (by simp)
  -- `u := n - 1`, its top words zero.
  refine WP.seq (WP.mono (zeroA_ok h₂ (j := 7) (by decide)) fun t₃ ⟨z3, o3, k3⟩ => ?_)
  have h₃ := h₂.congrO o3 (by tg_omega) k3 (by simp)
  refine WP.seq (WP.mono (subA_ok h₃ (t := 7) (a := 0) (b := 2) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun t₄ ⟨_, e4, o4, k4⟩ => ?_)
  have h₄ := h₃.congrO o4 (by tg_omega) k4 (by simp)
  -- `g`'s arrays cleared.
  refine WP.seq (WP.mono (zeroA_ok h₄ (j := 12) (by decide)) fun t₅ ⟨z5, o5, k5⟩ => ?_)
  have h₅ := h₄.congrO o5 (by tg_omega) k5 (by simp)
  refine WP.mono (zeroA_ok h₅ (j := 13) (by decide)) fun t₆ ⟨z6, o6, k6⟩ => ?_
  have h₆ := h₅.congrO o6 (by tg_omega) k6 (by simp)
  -- The values before the halvings.
  have X₁ : wv t₁.mem B (slot w 4) (2 * w + 2) = X := by rw [o1.wv (by tg_omega) (by tg_omega), hX]
  have U₆ : wv t₆.mem B (slot w 7) w = N - 1 := by
    rw [o6.wv (by tg_omega) (by tg_omega), o5.wv (by tg_omega) (by tg_omega)]
    have eN : wv t₃.mem B (slot w 0) w = N := by
      rw [o3.wv (by tg_omega) (by tg_omega), o2.wv (by tg_omega) (by tg_omega), o1.wv (by tg_omega) (by tg_omega), hN]
    have e1 : wv t₃.mem B (slot w 2) w = 1 := by
      rw [o3.wv (by tg_omega) (by tg_omega), o2.wv (by tg_omega) (by tg_omega), o1.wv (by tg_omega) (by tg_omega), hone]
    rw [eN, e1] at e4
    rw [wsub_of_eq e4 (wv_lt _ _ _ _) hNlt (Nat.one_lt_two_pow (by omega_arith)), wsub_of_le hNlt (by omega_arith)]
  have X2₆ : wv t₆.mem B (slot w 6) w = X % 2 ^ (64 * w) := by
    rw [o6.wv (by tg_omega) (by tg_omega), o5.wv (by tg_omega) (by tg_omega),
      o4.wv (by tg_omega) (by tg_omega), o3.wv (by tg_omega) (by tg_omega), v2, ← X₁,
      show 2 * w + 2 = w + (w + 2) by omega_arith]
    exact wv_low_mod
  have X₆ : wv t₆.mem B (slot w 4) (2 * w + 2) = X := by
    rw [o6.wv (by tg_omega) (by tg_omega), o5.wv (by tg_omega) (by tg_omega),
      o4.wv (by tg_omega) (by tg_omega), o3.wv (by tg_omega) (by tg_omega), o2.wv (by tg_omega) (by tg_omega), X₁]
  have z7₆ : word t₆.mem B (slot w 7 + 8 * w) = 0 := by
    rw [o6.word (by tg_omega) (by tg_omega), o5.word (by tg_omega) (by tg_omega), o4.word (by tg_omega) (by tg_omega)]
    have := wv_zero_sub (a := w) (k := 1) z3 (by omega_arith)
    exact BitVec.eq_of_toNat_eq (by simpa [wv] using this)
  have z6₆ : word t₆.mem B (slot w 6 + 8 * w) = 0 := by
    rw [o6.word (by tg_omega) (by tg_omega), o5.word (by tg_omega) (by tg_omega),
      o4.word (by tg_omega) (by tg_omega), o3.word (by tg_omega) (by tg_omega), o2.word (by tg_omega) (by tg_omega)]
    have := wv_zero_sub (a := w) (k := 1) z1 (by omega_arith)
    exact BitVec.eq_of_toNat_eq (by simpa [wv] using this)
  -- The halvings.
  refine wp_seqs_append (by simp [twos, wordStages]) (by simp) (WP.mono (twos_ok ⟨h₆, U₆, z7₆, X2₆, z6₆, X₆⟩
    (by omega_arith) (by omega_arith) hw129 hXw) fun t₈ ⟨tv, f8, k8⟩ => ?_)
  have hcl := twos_closed (b := 64 * (2 * w + 2)) (N := N - 1) (x₂ := X % 2 ^ (64 * w)) (x₃ := X) (k := 64 * w)
    (by omega_arith) (by omega_arith) hXw
  have hst : twosSt w N X = ((N - 1) / 2 ^ tz (N - 1), X % 2 ^ (64 * w) / 2 ^ tz (Nat.gcd (N - 1) (X % 2 ^ (64 * w))),
      X * 2 ^ tz (Nat.gcd (N - 1) (X % 2 ^ (64 * w))) % 2 ^ (64 * (2 * w + 2))) := by
    rw [twosSt, wsub_of_le hNlt (by omega_arith), hcl]
  have h₈ := tv.ws
  -- The GCD.
  simp only [seqs]
  refine WP.mono (gcdW_ok h₈ hZ26 hw20 (iU := 6) (iV := 12) (iM := 7) (by decide) (by decide)
    (by decide)) fun t₉ ⟨f9, k9, hg9⟩ => ?_
  have uodd : wv t₈.mem B (slot w 7) w % 2 = 1 := by
    rw [tv.u]
    have := (twos_odd (b := 64 * (2 * w + 2)) (N := N - 1) (k := 64 * w) (X % 2 ^ (64 * w)) X (by omega_arith)
      (by omega_arith)).1
    rw [hcl] at this
    exact this
  have hg := hg9 uodd
  have f9' : FrmP B (fun y => (slot w 12 ≤ y ∧ y < slot w 12 + 8 * w) ∨
      (slot w 16 ≤ y ∧ y < slot w 16 + 80 * (w + 2))) t₈.mem t₉.mem := FrmP.of_frm f9 fun r hr y h1 h2 => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl ⟨h1, h2⟩
    · exact .inr ⟨h1, h2⟩
  have f8' : FrmP B (TgP w) t₆.mem t₈.mem := FrmP.of_frm f8 fun r hr y h1 h2 => by
    simp only [twRs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [TgP, Bignum.slot, hdrBytes, sB2, sFn] at h1 h2 ⊢ <;> omega_arith
  have fr : ∀ {o n : Nat} {m m' : Mem}, Outside B o n m m' → (∀ y, o ≤ y → y < o + n → TgP w y) →
      FrmP B (TgP w) m m' := fun ho hP => FrmP.of_out ho hP
  refine ⟨?_, ?_, ?_, ((((((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).trans k8).trans k9).mono
    (by simp [mmRegs]))⟩
  · rw [f9'.wv_eq (fun y => by tg_omega) (by tg_omega), tv.x, hst]
  · -- `g`'s top words are still zero.
    have zt : wv t₉.mem B (slot w 12 + 8 * w) (w + 4) = 0 := by
      rw [f9'.wv_eq (fun y => by tg_omega) (by tg_omega), f8.wv_eq (fun r hr => by
        simp only [twRs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp only [Bignum.slot, hdrBytes, sB2, sFn] <;> omega_arith) (by tg_omega)]
      have z5' : wv t₆.mem B (slot w 12) (w + 2) = 0 := by rw [o6.wv (by tg_omega) (by tg_omega)]; exact z5
      rw [show w + 4 = 2 + (w + 2) by omega_arith, wv_add, wv_zero_sub (a := w) (k := 2) z5' (by omega_arith),
        show slot w 12 + 8 * w + 8 * 2 = slot w 13 by simp only [Bignum.slot, hdrBytes]; omega_arith, z6]
    rw [show 2 * (w + 2) = w + (w + 4) by omega_arith, wv_top_zero zt, hg, Nat.gcd_comm, tv.u, tv.x2, hst]
  · exact ((((((fr o1 fun y => by tg_omega).trans (fr o2 fun y => by tg_omega)).trans (fr o3 fun y => by tg_omega)).trans
      (fr o4 fun y => by tg_omega)).trans (fr o5 fun y => by tg_omega)).trans (fr o6 fun y => by tg_omega)).trans
      (f8'.trans (f9'.mono fun y => by tg_omega))

end

/-- The model's widths: `64 v` and `64 W` bits. -/
abbrev nbk (k : Nat) : Nat := 64 * nv k
abbrev wbk (k : Nat) : Nat := 64 * wW k

abbrev p2 : List (Prog isa) := [.block (width true)] ++ (deMinus ++ ([.block (width false)] ++
  (twosInit ++ (twos ++ [gcdW 6 12 7]))))

macro "p2_omega" : tactic =>
  `(tactic| ((try simp only [DOk, TgP, DaP, DbP, MnP, Bignum.slot, hdrBytes, Impl.Bignum.X86_64.Public.sMask, Impl.Bignum.X86_64.Public.sElen, sFn, nbk, wbk]); omega_arith))

/-- `d e - 1` and whether `d e ≥ 2` (wide), then the halvings and the GCD
(narrow): `x'` (wide array 2) and `g` (wide array 6) as the model's
`twosOut` gives them. -/
theorem phase2_ok [InvLaw] {I : RpIn} {m₀ : Mem} {s : State} (h : DS I m₀ (nv I.k) s) (L : RpLens I)
    {N DE : Nat} (hN2 : 2 ≤ N) (hm : mw s.mem I.B = mask true)
    (hn : wv s.mem I.B (slot (nv I.k) 0) (2 * (nv I.k + 2)) = N)
    (hM : wv s.mem I.B (slot (nv I.k) 10) (2 * (nv I.k + 2)) = DE) (hDE : DE < 2 ^ nbk I.k)
    (hNk : N < 2 ^ (64 * wk I.k)) :
    WP isa (seqs p2) s fun t => DS I m₀ (nv I.k) t ∧ mw t.mem I.B = mask (okDE (wbk I.k) DE) ∧
      wv t.mem I.B (slot (nv I.k) 0) (2 * (nv I.k + 2)) = N ∧
      wv t.mem I.B (slot (nv I.k) 2) (2 * (nv I.k + 2)) = 1 ∧
      wv t.mem I.B (slot (nv I.k) 4) (wW I.k) = (twosOut (nbk I.k) (wbk I.k) N DE).2.2 ∧
      wv t.mem I.B (slot (nv I.k) 12) (2 * (nv I.k + 2)) =
        Nat.gcd (twosOut (nbk I.k) (wbk I.k) N DE).1 (twosOut (nbk I.k) (wbk I.k) N DE).2.1 := by
  have hnw := h.ws.scr.nowrap
  have ⟨bW, b26, bv, bv9⟩ := rd_bounds L.k1 L.k2 L.z
  have hZW : 256 + 16 * (8 * (wW I.k + 2)) ≤ I.Z := bW
  have hZ' : 256 + 26 * (8 * (nv I.k + 2)) ≤ I.Z := b26
  have hW : wW I.k = 2 * nv I.k + 2 := rfl
  have hNv : N < 2 ^ nbk I.k := Nat.lt_of_lt_of_le hNk (Nat.pow_le_pow_right (by decide) (by simp only [nbk, nv]; omega_arith))
  have k2 := L.k2
  unfold p2
  -- The wide width.
  refine wp_seqs_append (by simp) (by simp [deMinus]) (WP.mono (h.width true L) fun t₁ ⟨h₁, _, f₁, k₁⟩ => ?_)
  replace h₁ : DS I m₀ (wW I.k) t₁ := h₁
  have M₁ : wv t₁.mem I.B (slot (wW I.k) 5) (wW I.k) = DE := by
    rw [slot_wide, f₁.wv_eq (fun y => by p2_omega) (by p2_omega), wv_low_of_lt (v := wW I.k) (w := 2 * (nv I.k + 2))
      (by p2_omega) (by rw [hM]; exact Nat.lt_of_lt_of_le hDE (Nat.pow_le_pow_right (by decide) (by p2_omega))), hM]
  have hm₁ : mw t₁.mem I.B = mask true := by
    unfold mw at hm ⊢; rw [f₁.word_eq (fun y => by p2_omega) (by p2_omega), hm]
  -- `d e - 1`.
  refine wp_seqs_append (by simp [deMinus]) (by simp) (WP.mono (deMinus_ok h₁.ws M₁ hm₁)
    fun t₂ ⟨one₂, X₂, hm₂, f₂, k₂⟩ => ?_)
  rw [Bool.true_and] at hm₂
  have h₂ := h₁.step f₂ (fun y => by p2_omega) k₂ (by simp)
  -- The narrow width.
  refine wp_seqs_append (by simp) (by simp [twosInit]) (WP.mono (h₂.width false L) fun t₃ ⟨h₃, _, f₃, k₃⟩ => ?_)
  replace h₃ : DS I m₀ (nv I.k) t₃ := h₃
  have N₃ : wv t₃.mem I.B (slot (nv I.k) 0) (2 * (nv I.k + 2)) = N := by
    rw [f₃.wv_eq (fun y => by p2_omega) (by p2_omega), f₂.wv_eq (fun y => by p2_omega) (by p2_omega),
      f₁.wv_eq (fun y => by p2_omega) (by p2_omega), hn]
  have one₃ : wv t₃.mem I.B (slot (nv I.k) 2) (2 * (nv I.k + 2)) = 1 := by
    rw [f₃.wv_eq (fun y => by p2_omega) (by p2_omega), ← one₂, slot_wide]
    congr 1
  have X₃ : wv t₃.mem I.B (slot (nv I.k) 4) (2 * nv I.k + 2) = deX (wbk I.k) DE := by
    rw [f₃.wv_eq (fun y => by p2_omega) (by p2_omega), ← X₂, slot_wide]
  have lowv : ∀ {m : Mem} {d X : Nat}, wv m I.B d (2 * (nv I.k + 2)) = X → X < 2 ^ (64 * nv I.k) →
      wv m I.B d (nv I.k) = X := fun e hx => by
    rw [wv_low_of_lt (v := nv I.k) (w := 2 * (nv I.k + 2)) (by omega_arith) (by rw [e]; exact hx), e]
  rw [← List.append_assoc]
  refine WP.mono (twosG_ok h₃.ws b26 bv (by simp only [nv, wk]; omega_arith) (lowv N₃ hNv) hN2
    (by rw [show nv I.k - 1 = wk I.k by simp only [nv]; omega_arith]; exact hNk)
    (lowv one₃ (Nat.one_lt_two_pow (by omega_arith))) X₃) fun t ⟨X3, G, f4, k4⟩ => ?_
  have h₄ := h₃.step f4 (fun y => by p2_omega) k4 (by simp)
  refine ⟨h₄, ?_, ?_, ?_, X3, G⟩
  · unfold mw
    rw [f4.word_eq (fun y => by p2_omega) (by p2_omega), f₃.word_eq (fun y => by p2_omega) (by p2_omega)]
    exact hm₂
  · rw [f4.wv_eq (fun y => by p2_omega) (by p2_omega), N₃]
  · rw [f4.wv_eq (fun y => by p2_omega) (by p2_omega), one₃]

/-! ## `a`, `m`, `r`, `m + 1`, `n - r` and `b` (wide) -/

abbrev p3 : List (Prog isa) := [.block (width true)] ++ (divA ++ divB)

/-- The model's `a`, from `x'` and the GCD. -/
theorem aOf_eq {nb wb N DE : Nat} (hx : (twosOut nb wb N DE).2.2 < 2 ^ wb)
    (hg : Nat.gcd (twosOut nb wb N DE).1 (twosOut nb wb N DE).2.1 < 2 ^ nb) :
    aOf nb wb N DE = (twosOut nb wb N DE).2.2 * Nat.gcd (twosOut nb wb N DE).1 (twosOut nb wb N DE).2.1 % 2 ^ wb := by
  unfold aOf
  rw [prod_iter _ _ _ hx]
  simp only
  rw [Nat.mod_eq_of_lt hg, Nat.mul_comm]

/-- `a`, `m = a / n` and `r = a mod n` and whether `m < n`, then `m + 1`,
`n - r`, their quotient `q` and remainder, whether it is zero, and `b` (all
wide), as the model gives them where `d e ≥ 2` and `m < n`. -/
theorem phase3_ok {I : RpIn} {m₀ : Mem} {s : State} (h : DS I m₀ (nv I.k) s) (L : RpLens I)
    {N DE : Nat} (hN3 : 3 ≤ N) (hNlo : 2 ^ (64 * (wk I.k - 1)) ≤ N) (hNk : N < 2 ^ (64 * wk I.k))
    (hn8 : 8 * (N + 2) ≤ 2 ^ nbk I.k) (hDE : DE < 2 ^ nbk I.k)
    (hm : mw s.mem I.B = mask (okDE (wbk I.k) DE))
    (hn : wv s.mem I.B (slot (nv I.k) 0) (2 * (nv I.k + 2)) = N)
    (hone : wv s.mem I.B (slot (nv I.k) 2) (2 * (nv I.k + 2)) = 1)
    (hX : wv s.mem I.B (slot (nv I.k) 4) (wW I.k) = (twosOut (nbk I.k) (wbk I.k) N DE).2.2)
    (hG : wv s.mem I.B (slot (nv I.k) 12) (2 * (nv I.k + 2)) =
      Nat.gcd (twosOut (nbk I.k) (wbk I.k) N DE).1 (twosOut (nbk I.k) (wbk I.k) N DE).2.1)
    (hGv : Nat.gcd (twosOut (nbk I.k) (wbk I.k) N DE).1 (twosOut (nbk I.k) (wbk I.k) N DE).2.1 < 2 ^ nbk I.k) :
    WP isa (seqs p3) s fun t => ∃ q rem : Nat,
      (okDE (wbk I.k) DE = true → ltOf (nbk I.k) (wbk I.k) N DE = true →
        q = dOf (nbk I.k) (wbk I.k) N DE / m1Of (nbk I.k) (wbk I.k) N DE ∧
        rem = dOf (nbk I.k) (wbk I.k) N DE % m1Of (nbk I.k) (wbk I.k) N DE) ∧
      DS I m₀ (wW I.k) t ∧
      mw t.mem I.B = mask (okDE (wbk I.k) DE && ltOf (nbk I.k) (wbk I.k) N DE && decide (rem = 0)) ∧
      wv t.mem I.B (slot (wW I.k) 0) (wW I.k) = N ∧ wv t.mem I.B (slot (wW I.k) 1) (wW I.k) = 1 ∧
      wv t.mem I.B (slot (wW I.k) 4) (wW I.k) % 2 ^ nbk I.k = bOf (nbk I.k) q ∧
      word t.mem I.B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 (4 * wW I.k - 8) := by
  have hnw := h.ws.scr.nowrap
  have ⟨bW, b26, bv, bv9⟩ := rd_bounds L.k1 L.k2 L.z
  have hZW : 256 + 16 * (8 * (wW I.k + 2)) ≤ I.Z := bW
  have hZ' : 256 + 26 * (8 * (nv I.k + 2)) ≤ I.Z := b26
  have hW : wW I.k = 2 * wk I.k + 4 := by simp only [wW, nv]; omega_arith
  have hWn : wW I.k = 2 * nv I.k + 2 := rfl
  have hnv : nv I.k = wk I.k + 1 := rfl
  have k1 := L.k1
  have k2 := L.k2
  have hwk8 : 8 ≤ wk I.k := by unfold wk; omega_arith
  have hwk128 : wk I.k ≤ 128 := by unfold wk; omega_arith
  have lowW : ∀ {m : Mem} {d X : Nat}, wv m I.B d (2 * (nv I.k + 2)) = X → X < 2 ^ (64 * wW I.k) →
      wv m I.B d (wW I.k) = X := fun e hx => by
    rw [wv_low_of_lt (v := wW I.k) (w := 2 * (nv I.k + 2)) (by omega_arith) (by rw [e]; exact hx), e]
  have pvW : 2 ^ nbk I.k ≤ 2 ^ (64 * wW I.k) := Nat.pow_le_pow_right (by decide) (by p2_omega)
  have hNv : N < 2 ^ nbk I.k := Nat.lt_of_lt_of_le hNk (Nat.pow_le_pow_right (by decide) (by simp only [nbk, nv]; omega_arith))
  have hXw : (twosOut (nbk I.k) (wbk I.k) N DE).2.2 < 2 ^ wbk I.k := hX ▸ wv_lt _ _ _ _
  have hA := aOf_eq hXw hGv
  generalize hGt : Nat.gcd (twosOut (nbk I.k) (wbk I.k) N DE).1 (twosOut (nbk I.k) (wbk I.k) N DE).2.1 = Gt
    at hG hGv hA
  generalize hXt : (twosOut (nbk I.k) (wbk I.k) N DE).2.2 = Xt at hX hXw hA
  unfold p3
  refine wp_seqs_append (by simp) (by simp [divA]) (WP.mono (h.width true L) fun t₁ ⟨h₁, _, f₁, k₁⟩ => ?_)
  replace h₁ : DS I m₀ (wW I.k) t₁ := h₁
  have n₁ : wv t₁.mem I.B (slot (wW I.k) 0) (wW I.k) = N := by
    rw [slot_wide, f₁.wv_eq (fun y => by p2_omega) (by p2_omega)]; exact lowW hn (by omega_arith)
  have one₁ : wv t₁.mem I.B (slot (wW I.k) 1) (wW I.k) = 1 := by
    rw [slot_wide, f₁.wv_eq (fun y => by p2_omega) (by p2_omega)]
    exact lowW hone (Nat.one_lt_two_pow (by omega_arith))
  have G₁ : wv t₁.mem I.B (slot (wW I.k) 6) (wW I.k) = Gt := by
    rw [slot_wide, f₁.wv_eq (fun y => by p2_omega) (by p2_omega)]; exact lowW hG (by omega_arith)
  have X₁ : wv t₁.mem I.B (slot (wW I.k) 2) (wW I.k) = Xt := by
    rw [slot_wide, f₁.wv_eq (fun y => by p2_omega) (by p2_omega)]; exact hX
  have hm₁ : mw t₁.mem I.B = mask (okDE (wbk I.k) DE) := by
    unfold mw at hm ⊢; rw [f₁.word_eq (fun y => by p2_omega) (by p2_omega), hm]
  -- `a = x' g`, `m`, `r`.
  have hAok : okDE (wbk I.k) DE = true → Xt * Gt % 2 ^ (64 * wW I.k) < N * 2 ^ (64 * (wk I.k + 1)) := fun hk => by
    have hde2 : 2 ≤ DE := by
      unfold okDE deX wsub at hk
      by_contra c
      rcases (show DE = 0 ∨ DE = 1 by omega_arith) with rfl | rfl <;> simp at hk
    have ac := aOf_closed (nb := nbk I.k) (wb := wbk I.k) hN3 hn8 (by simp only [nbk, wbk, wW]; omega_arith) hde2 hDE
    rw [← hA, ac]
    have hg : Nat.gcd (N - 1) (DE - 1) ≤ N - 1 := Nat.gcd_le_left _ (by omega_arith)
    have : (DE - 1) * Nat.gcd (N - 1) (DE - 1) ≤ (DE - 1) * (N - 1) := Nat.mul_le_mul_left _ hg
    have : (DE - 1) * (N - 1) < 2 ^ (64 * (wk I.k + 1)) * N := by
      have e : 64 * (wk I.k + 1) = nbk I.k := by simp only [nbk, nv]
      rw [e]
      calc (DE - 1) * (N - 1) < 2 ^ nbk I.k * N := Nat.mul_lt_mul'' (by omega_arith) (by omega_arith)
        _ = 2 ^ nbk I.k * N := rfl
    rw [Nat.mul_comm N]; omega_arith
  refine wp_seqs_append (by simp [divA]) (by simp [divB]) (WP.mono (divA_ok h₁.ws hW hwk8 n₁ hNlo hNk G₁
    (by rw [show 64 * (wk I.k + 1) = nbk I.k by simp only [nbk, nv]]; exact hGv) X₁ hm₁ hAok)
    fun t₂ ⟨hm₂, MR₂, el₂, f₂, k₂, hw₂⟩ => ?_)
  have h₂ := h₁.step f₂ (fun y => by p2_omega) k₂ (by simp [mmRegs])
  have hAw : Xt * Gt % 2 ^ (64 * wW I.k) = aOf (nbk I.k) (wbk I.k) N DE := by rw [hA]
  rw [hAw] at hm₂ MR₂
  have hlt : decide (aOf (nbk I.k) (wbk I.k) N DE / N < N) = ltOf (nbk I.k) (wbk I.k) N DE := rfl
  rw [hlt] at hm₂
  have n₂ : wv t₂.mem I.B (slot (wW I.k) 0) (wW I.k) = N := by rw [f₂.wv_eq (fun y => by p2_omega) (by p2_omega), n₁]
  have one₂ : wv t₂.mem I.B (slot (wW I.k) 1) (wW I.k) = 1 := by
    rw [f₂.wv_eq (fun y => by p2_omega) (by p2_omega), one₁]
  -- `q = (n - r) / (m + 1)`, `b = q + 1`.
  refine WP.mono (divB_ok h₂.ws hW hwk8 hwk128 n₂ hNk one₂ rfl rfl hm₂ (fun hc => by
    simp only [Bool.and_eq_true] at hc
    obtain ⟨hM, hR⟩ := MR₂ hc.1
    rw [hM, hR]
    exact ⟨of_decide_eq_true hc.2, Nat.mod_lt _ (by omega_arith)⟩)) fun t ⟨q, hq, B₃, hm₃, f₃, k₃, hw₃⟩ => ?_
  refine ⟨q, (N - wv t₂.mem I.B (slot (wW I.k) 6) (wW I.k)) % (wv t₂.mem I.B (slot (wW I.k) 7) (wW I.k) + 1),
    fun hk hl => ?_, h₂.step f₃ (fun y => by p2_omega) k₃ (by simp [mmRegs]), hm₃, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hM, hR⟩ := MR₂ hk
    have hq' := hq (by simp [hk, hl])
    have mlt : mOf (nbk I.k) (wbk I.k) N DE < N := by simpa [ltOf] using hl
    have rlt : rOf (nbk I.k) (wbk I.k) N DE < N := Nat.mod_lt _ (by omega_arith)
    have dv : dOf (nbk I.k) (wbk I.k) N DE = N - rOf (nbk I.k) (wbk I.k) N DE := by
      unfold dOf; rw [Nat.mod_eq_of_lt (by omega_arith), wsub_of_le hNv (by omega_arith)]
    have m1 : m1Of (nbk I.k) (wbk I.k) N DE = mOf (nbk I.k) (wbk I.k) N DE + 1 := by
      unfold m1Of; rw [Nat.mod_eq_of_lt (a := mOf (nbk I.k) (wbk I.k) N DE) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
    rw [hM, hR] at hq' ⊢
    rw [dv, m1]
    exact ⟨hq', rfl⟩
  · rw [f₃.wv_eq (fun y => by p2_omega) (by p2_omega), n₂]
  · rw [f₃.wv_eq (fun y => by p2_omega) (by p2_omega), one₂]
  · rw [B₃, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by p2_omega))]; rfl
  · rw [f₃.word_eq (fun y => by p2_omega) (by p2_omega), el₂]

/-! ## `b² - 4 n` and its square root (wide) -/

abbrev p4 : List (Prog isa) := minus4n ++ (RecoverDet.sqrt ++ [.block (width false)])

macro "p4_omega" : tactic =>
  `(tactic| ((try simp only [DOk, MnP, SqrtP, NxP, SqLP, FinP, Bignum.slot, hdrBytes, Impl.Bignum.X86_64.Public.sMask,
    Impl.Bignum.X86_64.Public.sElen, sFn, sqZ, sqT, sqD, sqU, sqS, sqR, sCt, sU, nbk, wbk] at *); omega))

/-- `b² - 4 n` and whether `b² > 4 n`, then its square root by words and whether
`b² - 4 n` is a square (wide), and the narrow width. -/
theorem phase4_ok {I : RpIn} {m₀ : Mem} {s : State} (h : DS I m₀ (wW I.k) s) (L : RpLens I)
    {N b : Nat} {c : Bool} (hm : mw s.mem I.B = mask c)
    (hn : wv s.mem I.B (slot (wW I.k) 0) (wW I.k) = N) (hone : wv s.mem I.B (slot (wW I.k) 1) (wW I.k) = 1)
    (hb : wv s.mem I.B (slot (wW I.k) 4) (wW I.k) % 2 ^ nbk I.k = b)
    (hel : word s.mem I.B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 (4 * wW I.k - 8)) :
    WP isa (seqs p4) s fun t => DS I m₀ (nv I.k) t ∧
      mw t.mem I.B = mask (c && ok4Of (nbk I.k) (wbk I.k) N b &&
        decide (VG.Spec.Rsa.isqrt (xOf (nbk I.k) (wbk I.k) N b % 2 ^ (64 * (2 * wk I.k))) *
          VG.Spec.Rsa.isqrt (xOf (nbk I.k) (wbk I.k) N b % 2 ^ (64 * (2 * wk I.k))) =
          xOf (nbk I.k) (wbk I.k) N b % 2 ^ (64 * (2 * wk I.k)))) ∧
      wv t.mem I.B (slot (nv I.k) 8) (nv I.k) = b ∧
      wv t.mem I.B (slot (nv I.k) 4) (nv I.k) =
        VG.Spec.Rsa.isqrt (xOf (nbk I.k) (wbk I.k) N b % 2 ^ (64 * (2 * wk I.k))) := by
  have hnw := h.ws.scr.nowrap
  have ⟨bW, b26, bv, bv9⟩ := rd_bounds L.k1 L.k2 L.z
  have hZW : 256 + 16 * (8 * (wW I.k + 2)) ≤ I.Z := bW
  have hZ' : 256 + 26 * (8 * (nv I.k + 2)) ≤ I.Z := b26
  have k1 := L.k1
  have k2 := L.k2
  have hW : wW I.k = 2 * nv I.k + 2 := rfl
  have hWh : wW I.k = 2 * wk I.k + 4 := by simp only [wW, nv]; omega_arith
  have hnv : nv I.k = wk I.k + 1 := rfl
  unfold p4
  refine wp_seqs_append (by simp [minus4n]) (by simp [RecoverDet.sqrt, normX]) (WP.mono (minus4n_ok h.ws hW
    (by omega_arith) hn hone hb hel hm) fun t₁ ⟨X₁, hm₁, f₁, k₁, hw₁⟩ => ?_)
  have h₁ := h.step f₁ (fun y => by p2_omega) k₁ (by simp [mmRegs])
  have b₁ : wv t₁.mem I.B (slot (wW I.k) 4) (wW I.k) % 2 ^ nbk I.k = b := by
    rw [f₁.wv_eq (fun y => by p2_omega) (by p2_omega), hb]
  refine wp_seqs_append (by simp [RecoverDet.sqrt, normX]) (by simp) (WP.mono (sqrt_ok h₁.ws hWh
    (by unfold wk; omega_arith) (by unfold wk; omega_arith) X₁ hm₁) fun t₂ ⟨R₂, hm₂, f₂, k₂, hw₂⟩ => ?_)
  have h₂ := h₁.step f₂ (fun y hy => by p4_omega) k₂ (by simp [mmRegs])
  have b₂ : wv t₂.mem I.B (slot (wW I.k) 4) (wW I.k) % 2 ^ nbk I.k = b := by
    rw [f₂.wv_eq (fun y h1 h2 hy => by p4_omega) (by p4_omega), b₁]
  simp only [seqs]
  refine WP.mono (h₂.width false L) fun t ⟨h₃, _, f₃, k₃⟩ => ⟨h₃, ?_, ?_, ?_⟩
  · unfold mw at hm₂ ⊢; rw [f₃.word_eq (fun y => by p2_omega) (by p2_omega), hm₂]
  · rw [show slot (nv I.k) 8 = slot (wW I.k) 4 by rw [slot_wide], f₃.wv_eq (fun y => by p2_omega) (by p2_omega),
      ← wv_mod_low t₂.mem I.B _ (c := nv I.k) (n := wW I.k) (by omega_arith)]
    exact b₂
  · have hR : VG.Spec.Rsa.isqrt (xOf (nbk I.k) (wbk I.k) N b % 2 ^ (64 * (2 * wk I.k))) < 2 ^ (64 * nv I.k) := by
      have lo := VG.Proof.Rsa.RecoverDet.isqrt_sq_le (xOf (nbk I.k) (wbk I.k) N b % 2 ^ (64 * (2 * wk I.k)))
      have hx := Nat.mod_lt (xOf (nbk I.k) (wbk I.k) N b) (Nat.two_pow_pos (64 * (2 * wk I.k)))
      generalize VG.Spec.Rsa.isqrt (xOf (nbk I.k) (wbk I.k) N b % 2 ^ (64 * (2 * wk I.k))) = r at lo
      refine Nat.lt_of_not_le fun c => ?_
      have : 2 ^ (64 * nv I.k) * 2 ^ (64 * nv I.k) ≤ r * r := Nat.mul_self_le_mul_self c
      have : 2 ^ (64 * (2 * wk I.k)) ≤ 2 ^ (64 * nv I.k) * 2 ^ (64 * nv I.k) := by
        rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by simp only [nv]; omega_arith)
      omega_arith
    rw [show slot (nv I.k) 4 = slot (wW I.k) 2 by rw [slot_wide], f₃.wv_eq (fun y => by p2_omega) (by p2_omega),
      ← wv_mod_low t₂.mem I.B _ (c := nv I.k) (n := wW I.k) (by omega_arith),
      show slot (wW I.k) 2 = slot (wW I.k) sqR from rfl, R₂,
      Nat.mod_eq_of_lt hR]

/-! ## `main` -/

theorem main_eq : RecoverDet.main = seqs (p1 ++ (p2 ++ (p3 ++ (p4 ++ factors)))) := by
  simp only [RecoverDet.main, p1, p2, p3, p4, List.append_assoc, List.cons_append, List.nil_append]

/-- The model's mask and factors as `main` computes them. -/
theorem result_of {nb wb N DE q rem : Nat} :
    result nb wb N DE q rem = if (okDE wb DE && ltOf nb wb N DE && decide (rem = 0) &&
        ok4Of nb wb N (bOf nb q) && decide ((rootOf nb wb N (bOf nb q)).2.1 = 0)) then
      some ((bOf nb q + (rootOf nb wb N (bOf nb q)).2.2) % 2 ^ nb / 2,
        wsub nb (bOf nb q) (rootOf nb wb N (bOf nb q)).2.2 / 2) else none := by
  unfold result stage2
  simp only [Bool.and_assoc]

/-- The numbers' bounds, from a valid modulus. -/
theorem rd_nums {I : RpIn} (L : RpLens I) (hel8 : I.el ≤ 8) (hv : Spec.Rsa.modulusValid I.N I.k = true) :
    3 ≤ I.N ∧ I.N < 2 ^ (64 * wk I.k) ∧ 2 ^ (64 * (wk I.k - 1)) ≤ I.N ∧ 8 * (I.N + 2) ≤ 2 ^ nbk I.k ∧
      I.D * I.E < 2 ^ nbk I.k ∧
      Nat.gcd (twosOut (nbk I.k) (wbk I.k) I.N (I.D * I.E)).1 (twosOut (nbk I.k) (wbk I.k) I.N (I.D * I.E)).2.1
        < 2 ^ nbk I.k := by
  obtain ⟨-, hlo⟩ := valid_lo hv
  have hN3 : 3 ≤ I.N := by
    have : 256 ^ 63 ≤ 256 ^ (I.k - 1) := Nat.pow_le_pow_right (by decide) (by have := L.k1; omega_arith)
    have : 3 ≤ 256 ^ 63 := by decide
    omega_arith
  have hNk : I.N < 2 ^ (64 * wk I.k) := by
    have := os2ip_lt I.nb; rw [L.nbl] at this
    have hl : 8 * I.k ≤ 64 * wk I.k := by unfold wk; omega_arith
    have hp : 256 ^ I.k ≤ 2 ^ (64 * wk I.k) := by rw [pow256_eq]; exact Nat.pow_le_pow_right (by decide) hl
    exact Nat.lt_of_lt_of_le this hp
  have hNv : I.N < 2 ^ nbk I.k := Nat.lt_of_lt_of_le hNk (Nat.pow_le_pow_right (by decide) (by simp only [nbk, nv]; omega_arith))
  have hDk : I.D < 2 ^ (64 * wk I.k) := by
    have := os2ip_lt I.db; rw [L.dbl] at this
    have hl : 8 * I.dl ≤ 64 * wk I.k := by have := L.dl2; unfold wk; omega_arith
    have hp : 256 ^ I.dl ≤ 2 ^ (64 * wk I.k) := by rw [pow256_eq]; exact Nat.pow_le_pow_right (by decide) hl
    exact Nat.lt_of_lt_of_le this hp
  have hE64 : I.E < 2 ^ 64 := by
    have := os2ip_lt I.eb; rw [L.ebl] at this
    have hp : 256 ^ I.el ≤ 2 ^ 64 := by rw [pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by omega_arith)
    exact Nat.lt_of_lt_of_le this hp
  have hDE : I.D * I.E < 2 ^ nbk I.k := by
    rw [show nbk I.k = 64 * wk I.k + 64 by simp only [nbk, nv]; omega_arith, Nat.pow_add]
    exact Nat.mul_lt_mul'' hDk hE64
  have hNlo : 2 ^ (64 * (wk I.k - 1)) ≤ I.N := by
    refine Nat.le_trans ?_ hlo
    rw [pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by have := L.k1; unfold wk; omega_arith)
  have hn8 : 8 * (I.N + 2) ≤ 2 ^ nbk I.k := by
    have : 1 ≤ 2 ^ (64 * wk I.k) := Nat.one_le_two_pow
    rw [show nbk I.k = 64 * wk I.k + 64 by simp only [nbk, nv]; omega_arith, Nat.pow_add]
    have : 16 ≤ 2 ^ 64 := by decide
    have := Nat.mul_le_mul_left (2 ^ (64 * wk I.k)) this
    omega_arith
  have hGv : Nat.gcd (twosOut (nbk I.k) (wbk I.k) I.N (I.D * I.E)).1 (twosOut (nbk I.k) (wbk I.k) I.N (I.D * I.E)).2.1
      < 2 ^ nbk I.k := by
    have hN1 : wsub (nbk I.k) I.N 1 = I.N - 1 := wsub_of_le hNv (by omega_arith)
    obtain ⟨uo, ul⟩ := twos_odd (b := wbk I.k) (k := nbk I.k) (deX (wbk I.k) (I.D * I.E) % 2 ^ nbk I.k)
      (deX (wbk I.k) (I.D * I.E)) (show 0 < wsub (nbk I.k) I.N 1 by rw [hN1]; omega_arith)
      (by rw [hN1]; omega_arith)
    have uo' : (twosOut (nbk I.k) (wbk I.k) I.N (I.D * I.E)).1 % 2 = 1 := uo
    have ul' : (twosOut (nbk I.k) (wbk I.k) I.N (I.D * I.E)).1 ≤ wsub (nbk I.k) I.N 1 := ul
    have := Nat.gcd_le_left (twosOut (nbk I.k) (wbk I.k) I.N (I.D * I.E)).2.1
      (show 0 < (twosOut (nbk I.k) (wbk I.k) I.N (I.D * I.E)).1 by omega_arith)
    omega_arith
  exact ⟨hN3, hNk, hNlo, hn8, hDE, hGv⟩

/-- Everything before `divA`: the facts its division needs, at the wide width. -/
theorem pre3_ok [InvLaw] {I : RpIn} {s : State} (h : RpPre I s) (hel8 : I.el ≤ 8)
    (hv : Spec.Rsa.modulusValid I.N I.k = true) :
    WP isa (seqs (p1 ++ (p2 ++ ([.block (width true)] : List (Prog isa))))) s fun t => ∃ m₀ G X, DS I m₀ (wW I.k) t ∧
      (∃ c, mw t.mem I.B = mask c) ∧ wv t.mem I.B (slot (wW I.k) 0) (wW I.k) = I.N ∧
      wv t.mem I.B (slot (wW I.k) 6) (wW I.k) = G ∧ G < 2 ^ (64 * (wk I.k + 1)) ∧
      wv t.mem I.B (slot (wW I.k) 2) (wW I.k) = X := by
  have L := h.L
  have ⟨bW, b26, bv, bv9⟩ := rd_bounds L.k1 L.k2 L.z
  obtain ⟨hN3, hNk, hNlo, hn8, hDE, hGv⟩ := rd_nums L hel8 hv
  refine wp_seqs_append (by simp) (by simp) (WP.mono (phase1_ok h hel8) fun t₁ ⟨S₁, hm₁, n₁, M₁⟩ => ?_)
  refine wp_seqs_append (by simp) (by simp) (WP.mono (phase2_ok S₁ L (by omega_arith) hm₁ n₁ M₁ hDE hNk)
    fun t₂ ⟨S₂, hm₂, n₂, one₂, X₂, G₂⟩ => ?_)
  have hnw := S₂.ws.scr.nowrap
  have hZW : 256 + 16 * (8 * (wW I.k + 2)) ≤ I.Z := bW
  have hZ' : 256 + 26 * (8 * (nv I.k + 2)) ≤ I.Z := b26
  have hWn : wW I.k = 2 * nv I.k + 2 := rfl
  have hnv : nv I.k = wk I.k + 1 := rfl
  have lowW : ∀ {m : Mem} {d X : Nat}, wv m I.B d (2 * (nv I.k + 2)) = X → X < 2 ^ (64 * wW I.k) →
      wv m I.B d (wW I.k) = X := fun e hx => by
    rw [wv_low_of_lt (v := wW I.k) (w := 2 * (nv I.k + 2)) (by omega_arith) (by rw [e]; exact hx), e]
  have pvW : 2 ^ nbk I.k ≤ 2 ^ (64 * wW I.k) := Nat.pow_le_pow_right (by decide) (by p2_omega)
  have hNv : I.N < 2 ^ nbk I.k := Nat.lt_of_lt_of_le hNk (Nat.pow_le_pow_right (by decide) (by simp only [nbk, nv]; omega_arith))
  simp only [seqs]
  refine WP.mono (S₂.width true L) fun t ⟨h₁, _, f₁, k₁⟩ => ⟨_, _, (twosOut (nbk I.k) (wbk I.k) I.N (I.D * I.E)).2.2,
    h₁, ⟨okDE (wbk I.k) (I.D * I.E), ?_⟩, ?_, ?_,
    by rw [show 64 * (wk I.k + 1) = nbk I.k by simp only [nbk, nv]]; exact hGv, ?_⟩
  · unfold mw at hm₂ ⊢; rw [f₁.word_eq (fun y => by p2_omega) (by p2_omega), hm₂]
  · rw [slot_wide, f₁.wv_eq (fun y => by p2_omega) (by p2_omega)]; exact lowW n₂ (by omega_arith)
  · rw [slot_wide, f₁.wv_eq (fun y => by p2_omega) (by p2_omega)]; exact lowW G₂ (by omega_arith)
  · rw [slot_wide, f₁.wv_eq (fun y => by p2_omega) (by p2_omega)]; exact X₂

/-- `main`, from a valid modulus: Appendix C.2's factors written, or zeros. -/
theorem rdMain_ok [InvLaw] {I : RpIn} {s : State} (h : RpPre I s) (hel8 : I.el ≤ 8)
    (hv : Spec.Rsa.modulusValid I.N I.k = true) :
    WP isa RecoverDet.main s fun t => ∃ res : Option (Nat × Nat),
      Spec.Rsa.recoverDet I.N I.E I.D = res ∧
      (List.range I.k).map (fun i => t.mem (I.pP + BitVec.ofNat 64 i)) = Spec.Rsa.i2osp (fstOr res) I.k ∧
      (List.range I.k).map (fun i => t.mem (I.pQ + BitVec.ofNat 64 i)) = Spec.Rsa.i2osp (sndOr res) I.k ∧
      t.gpr .rax = BitVec.ofNat 64 res.isSome.toNat ∧ (∀ i < 6, t.gpr (saved.getD i .rax) = I.sv i) ∧
      (∀ x, I.Z ≤ ofs I.B x → (∀ i < I.k, x ≠ I.pP + BitVec.ofNat 64 i) →
        (∀ i < I.k, x ≠ I.pQ + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      t.gpr .rsp = s.gpr .rsp := by
  have L := h.L
  have ⟨bW, b26, bv, bv9⟩ := rd_bounds L.k1 L.k2 L.z
  obtain ⟨hNo, hlo⟩ := valid_lo hv
  obtain ⟨hN3, hNk, hNlo, hn8, hDE, hGv⟩ := rd_nums L hel8 hv
  have hNv : I.N < 2 ^ nbk I.k := Nat.lt_of_lt_of_le hNk (Nat.pow_le_pow_right (by decide) (by simp only [nbk, nv]; omega_arith))
  have hw2 : 2 * nbk I.k ≤ wbk I.k := by simp only [nbk, wbk, wW]; omega_arith
  have hwe : wbk I.k % 2 = 0 := by simp only [wbk]; omega_arith
  rw [main_eq]
  refine wp_seqs_append (by simp) (by simp) (WP.mono (phase1_ok h hel8) fun t₁ ⟨S₁, hm₁, n₁, M₁⟩ => ?_)
  refine wp_seqs_append (by simp) (by simp) (WP.mono (phase2_ok S₁ L (by omega_arith) hm₁ n₁ M₁ hDE hNk)
    fun t₂ ⟨S₂, hm₂, n₂, one₂, X₂, G₂⟩ => ?_)
  refine wp_seqs_append (by simp) (by simp) (WP.mono (phase3_ok S₂ L hN3 hNlo hNk hn8 hDE hm₂ n₂ one₂ X₂ G₂ hGv)
    fun t₃ ⟨q, rem, hqr, S₃, hm₃, n₃, one₃, b₃, el₃⟩ => ?_)
  refine wp_seqs_append (by simp [minus4n]) (by simp [factors]) (WP.mono (phase4_ok S₃ L hm₃ n₃ one₃ b₃ el₃)
    fun t₄ ⟨S₄, hm₄, b₄, y₄⟩ => ?_)
  -- The model.
  have hres := model_correct_c (nb := nbk I.k) (wb := wbk I.k) (n := I.N) (e := I.E) (d := I.D) (q := q) (rem := rem)
    hNo hN3 hn8 hDE hw2 hwe hqr
  rw [result_of] at hres
  generalize hX0 : xOf (nbk I.k) (wbk I.k) I.N (bOf (nbk I.k) q) % 2 ^ (64 * (2 * wk I.k)) = X0 at hm₄ y₄
  have hP : (I.N + 1) * (I.N + 1) ≤ 2 ^ (64 * (2 * wk I.k)) := by
    have : I.N + 1 ≤ 2 ^ (64 * wk I.k) := hNk
    rw [show 64 * (2 * wk I.k) = 64 * wk I.k + 64 * wk I.k by omega_arith, Nat.pow_add]
    exact Nat.mul_le_mul this this
  have hbr : (okDE (wbk I.k) (I.D * I.E) && ltOf (nbk I.k) (wbk I.k) I.N (I.D * I.E) && decide (rem = 0) &&
      ok4Of (nbk I.k) (wbk I.k) I.N (bOf (nbk I.k) q)) = true →
      (rootOf (nbk I.k) (wbk I.k) I.N (bOf (nbk I.k) q)).2.2 = VG.Spec.Rsa.isqrt X0 ∧
      ((rootOf (nbk I.k) (wbk I.k) I.N (bOf (nbk I.k) q)).2.1 = 0 ↔ VG.Spec.Rsa.isqrt X0 * VG.Spec.Rsa.isqrt X0 = X0) :=
    fun hc => by
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨⟨hk, hl⟩, -⟩, h4⟩ := hc
      rw [← hX0, Nat.mod_eq_of_lt (xOf_lt hN3 hn8 hw2 hP hl (hqr hk hl).1 h4)]
      exact (root_bridge hN3 hn8 hw2 hwe hl (hqr hk hl).1 h4).imp_right And.left
  generalize hcond : (okDE (wbk I.k) (I.D * I.E) && ltOf (nbk I.k) (wbk I.k) I.N (I.D * I.E) && decide (rem = 0) &&
    ok4Of (nbk I.k) (wbk I.k) I.N (bOf (nbk I.k) q) && decide (VG.Spec.Rsa.isqrt X0 * VG.Spec.Rsa.isqrt X0 = X0)) =
    cond at hm₄
  have hcd : (okDE (wbk I.k) (I.D * I.E) && ltOf (nbk I.k) (wbk I.k) I.N (I.D * I.E) && decide (rem = 0) &&
      ok4Of (nbk I.k) (wbk I.k) I.N (bOf (nbk I.k) q) &&
      decide ((rootOf (nbk I.k) (wbk I.k) I.N (bOf (nbk I.k) q)).2.1 = 0)) = cond := by
    rw [← hcond]
    by_cases hc : (okDE (wbk I.k) (I.D * I.E) && ltOf (nbk I.k) (wbk I.k) I.N (I.D * I.E) && decide (rem = 0) &&
        ok4Of (nbk I.k) (wbk I.k) I.N (bOf (nbk I.k) q)) = true
    · rw [hc, Bool.true_and, Bool.true_and]
      exact decide_eq_decide.mpr (hbr hc).2
    · simp only [Bool.not_eq_true] at hc
      rw [hc, Bool.false_and, Bool.false_and]
  rw [hcd] at hres
  have hroot : cond = true → (rootOf (nbk I.k) (wbk I.k) I.N (bOf (nbk I.k) q)).2.2 = VG.Spec.Rsa.isqrt X0 :=
    fun hc => (hbr (by
      rw [← hcond] at hc
      simp only [Bool.and_eq_true] at hc ⊢
      exact hc.1)).1
  have hm₄' : mw t₄.mem I.B = mask cond := hm₄
  have hfac : cond = true → (bOf (nbk I.k) q + VG.Spec.Rsa.isqrt X0) %
      2 ^ nbk I.k / 2 * (wsub (nbk I.k) (bOf (nbk I.k) q) (VG.Spec.Rsa.isqrt X0) / 2) = I.N := fun hc => by
    rw [hc] at hres
    simp only [↓reduceIte] at hres
    rw [← hroot hc]
    exact recoverDet_mul hres.symm
  have hlt : ∀ {a b' : Nat}, a * b' = I.N → a < 2 ^ (64 * ((I.k + 7) / 8)) ∧ b' < 2 ^ (64 * ((I.k + 7) / 8)) :=
    fun {a b'} e => by
      have ha : 0 < a := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.zero_mul] at e; omega_arith
      have hb : 0 < b' := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at e; omega_arith
      have := Nat.le_mul_of_pos_right a hb
      have := Nat.le_mul_of_pos_left b' ha
      have hNk' : I.N < 2 ^ (64 * ((I.k + 7) / 8)) := hNk
      exact ⟨by omega_arith, by omega_arith⟩
  refine WP.mono (factors_ok S₄.ws S₄.p S₄.q S₄.k S₄.sv hm₄' (by have := L.k1; omega_arith)
    (by unfold nv wk; omega_arith) b₄ y₄ (fun hc => (hlt (hfac hc)).1) (fun hc => (hlt (hfac hc)).2)
    ⟨fun i hi => by rw [S₄.wr, ← h.wr]; exact h.oP.wr i hi, h.oP.sep⟩
    ⟨fun i hi => by rw [S₄.wr, ← h.wr]; exact h.oQ.wr i hi, h.oQ.sep⟩ h.a) fun t ⟨bP, bQ, hax, hsv, hfr, kk⟩ => ?_
  refine ⟨_, hres.symm, ?_, ?_, ?_, hsv, fun x hx n1 n2 => ?_, ?_⟩
  · rw [bP]; cases hcc : cond
    · rfl
    · simp only [↓reduceIte, fstOr, hroot hcc]
  · rw [bQ]; cases hcc : cond
    · rfl
    · simp only [↓reduceIte, sndOr, hroot hcc]
  · rw [hax]; cases cond <;> rfl
  · rw [hfr x n1 n2 hx]
    exact S₄.inScr x hx
  · rw [kk.gpr (by decide), S₄.rsp, h.rsp]

end VG.Proof.Rsa.X86_64.Rd
