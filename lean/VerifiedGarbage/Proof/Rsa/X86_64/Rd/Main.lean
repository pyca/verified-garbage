module

public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Tail
public import VerifiedGarbage.Proof.Rsa.X86_64.RpMain
import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
import VerifiedGarbage.Proof.Rsa.X86_64.CvMain
import VerifiedGarbage.Proof.Rsa.X86_64.RpProd
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

/-- What every piece of `main` keeps, from the memory `m₀` on entry to
`main`, at the width `w`. -/
structure DS (I : RpIn) (m₀ : Mem) (w : Nat) (s : State) : Prop where
  ws : Ws s I.B I.Z w
  p : word s.mem I.B (8 * Recover.sP) = I.pP
  q : word s.mem I.B (8 * Recover.sQ) = I.pQ
  k : word s.mem I.B (8 * Impl.Bignum.X86_64.Public.sK) = BitVec.ofNat 64 I.k
  sv : ∀ i < 6, word s.mem I.B (8 * i) = I.sv i
  inScr : InScr I.B I.Z m₀ s.mem
  wr : s.wr = I.W
  rsp : s.gpr .rsp = I.sp

/-- `DS` after code that changes only offsets that `DOk` allows, below `Z`. -/
theorem DS.step {I : RpIn} {m₀ : Mem} {w : Nat} {s t : State} (h : DS I m₀ w s) {P : Nat → Prop}
    (hf : FrmP I.B P s.mem t.mem) (hP : ∀ y, P y → DOk y ∧ y < I.Z) {regs : List Reg} (k : Keep regs s t)
    (hr : .rdi ∉ regs ∧ .rsp ∉ regs) : DS I m₀ w t := by
  have hn := h.ws.scr.nowrap
  have h256 := h.ws.h256
  have hw : ∀ i, i < 6 ∨ i = 16 ∨ i = 18 ∨ i = 21 → word t.mem I.B (8 * i) = word s.mem I.B (8 * i) := fun i hi =>
    hf.word_eq (fun y h1 h2 hy => by have := (hP y hy).1; unfold DOk at this; omega_arith) (by omega_arith)
  refine ⟨h.ws.congrP hf (fun y hy => (hP y hy).1) k hr.1, (hw _ (by simp [Recover.sP,
    Impl.Bignum.X86_64.Public.sOut, sFn])).trans h.p, (hw _ (by simp [Recover.sQ, Impl.Bignum.X86_64.Public.sIn,
    sFn])).trans h.q, (hw _ (by simp [Impl.Bignum.X86_64.Public.sK, sFn])).trans h.k,
    fun i hi => (hw i (.inl hi)).trans (h.sv i hi), fun x hx => ?_, k.2.2.trans h.wr, (k.gpr hr.2).trans h.rsp⟩
  rw [hf x fun hy => absurd hx (Nat.not_le.mpr (hP _ hy).2)]
  exact h.inScr x hx

/-- The lengths, as `vg_rsa_recover_primes_det`'s contract bounds them. -/
theorem rd_bounds {k Z : Nat} (hk1 : 64 ≤ k) (hk2 : k ≤ 1024) (hZ : 128 * k ≤ Z) :
    slot (wW k) 16 ≤ Z ∧ slot (nv k) 26 ≤ Z ∧ nv k < 2 ^ 20 ∧ 9 ≤ nv k := by
  simp only [Bignum.slot, hdrBytes, wW, nv, wk]
  omega_arith

/-- `width wide`, keeping `DS`. -/
theorem DS.width {I : RpIn} {m₀ : Mem} {w : Nat} {s : State} (h : DS I m₀ w s) (wide : Bool) (L : RpLens I) :
    WP isa (.block (width wide)) s fun t => DS I m₀ (widthOf wide I.k) t ∧ t.mem = t.mem ∧
      FrmP I.B (fun y => 48 ≤ y ∧ y < 128 ∨ 224 ≤ y ∧ y < 232) s.mem t.mem ∧ Keep [.rax, .rdx, .r12] s t := by
  have hn := h.ws.scr.nowrap
  have h256 := h.ws.h256
  refine WP.mono (width_ok wide h.ws.scr h.ws.rdi L.k1 L.k2 L.z h.k) fun t ⟨hw, hf, k⟩ => ?_
  have hf' : FrmP I.B (fun y => 48 ≤ y ∧ y < 128 ∨ 224 ≤ y ∧ y < 232) s.mem t.mem := FrmP.of_frm hf fun r hr y h1 h2 => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [sW, sArr, sStride, sFn] at h1 h2 ⊢ <;> omega_arith
  have hwd : ∀ i, i < 6 ∨ i = 16 ∨ i = 18 ∨ i = 21 → word t.mem I.B (8 * i) = word s.mem I.B (8 * i) := fun i hi =>
    hf'.word_eq (fun y h1 h2 hy => by omega_arith) (by omega_arith)
  refine ⟨⟨hw, (hwd _ (by simp [Recover.sP, Impl.Bignum.X86_64.Public.sOut, sFn])).trans h.p,
    (hwd _ (by simp [Recover.sQ, Impl.Bignum.X86_64.Public.sIn, sFn])).trans h.q,
    (hwd _ (by simp [Impl.Bignum.X86_64.Public.sK, sFn])).trans h.k,
    fun i hi => (hwd i (.inl hi)).trans (h.sv i hi), fun x hx => ?_, k.2.2.trans h.wr,
    (k.gpr (by decide)).trans h.rsp⟩, rfl, hf', k⟩
  rw [hf' x fun hy => absurd hx (by have := h.ws.h256; simp only at hy; omega_arith)]
  exact h.inScr x hx

/-! ## The prefix: the head, the loads and `d e` (narrow) -/

/-- `RpArgs` after a piece that changes only bytes from offset 256 on. -/
theorem _root_.VG.Proof.Rsa.X86_64.RpArgs.out {m m' : Mem} {B : Addr} {k el dl : Nat} {pP pQ pN pE pD : Addr} {sv : Nat → BitVec 64}
    (h : RpArgs m B k el dl pP pQ pN pE pD sv) {o n : Nat} (ho : Outside B o n m m') (h256 : 256 ≤ o) :
    RpArgs m' B k el dl pP pQ pN pE pD sv :=
  h.congr fun i hi => ho.word (.inl (by unfold rArg at hi; omega_arith)) (by unfold rArg at hi; omega_arith)

/-- The prefix of `main`. -/
abbrev p1 : List (Prog isa) := [.block RecoverDet.head] ++
  (loadA Impl.Bignum.X86_64.Public.aN Impl.Bignum.X86_64.Public.sN Impl.Bignum.X86_64.Public.sK ++
  ([zeroA 1] ++ (loadA Recover.aE Impl.Bignum.X86_64.Public.sE Impl.Bignum.X86_64.Public.sElen ++
  (loadA Recover.aD Recover.sD Recover.sDl ++ Recover.prod))))

macro "p1_omega" : tactic =>
  `(tactic| (simp only [DOk, Bignum.slot, hdrBytes, Impl.Bignum.X86_64.Public.sMask, sFn, nv, wk, Recover.aE,
    Recover.aD, Recover.aM, Impl.Bignum.X86_64.Public.aN]; omega_arith))

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

/-- The model's widths: `64 v` and `64 W` bits. -/
abbrev nbk (k : Nat) : Nat := 64 * nv k
abbrev wbk (k : Nat) : Nat := 64 * wW k

abbrev p2 : List (Prog isa) := [.block (width true)] ++ (deMinus ++ ([.block (width false)] ++
  (twosInit ++ [.loop twosBody .ne, inverse 6 12 15 7])))

macro "p2_omega" : tactic =>
  `(tactic| ((try simp only [DOk, TgP, DaP, DbP, MnP, SqP, Bignum.slot, hdrBytes, Impl.Bignum.X86_64.Public.sMask, Impl.Bignum.X86_64.Public.sElen, sFn, nbk, wbk]); omega_arith))

/-- `d e - 1` and whether `d e ≥ 2` (wide), then the halvings and the GCD
(narrow): `x'` (wide array 2) and `g` (wide array 6) as the model's
`twosOut` gives them. -/
theorem phase2_ok [InvLaw] {I : RpIn} {m₀ : Mem} {s : State} (h : DS I m₀ (nv I.k) s) (L : RpLens I)
    {N DE : Nat} (hN2 : 2 ≤ N) (hm : mw s.mem I.B = mask true)
    (hn : wv s.mem I.B (slot (nv I.k) 0) (2 * (nv I.k + 2)) = N)
    (hM : wv s.mem I.B (slot (nv I.k) 10) (2 * (nv I.k + 2)) = DE) (hDE : DE < 2 ^ nbk I.k)
    (hNv : N < 2 ^ nbk I.k) :
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
  refine WP.mono (twosG_ok h₃.ws b26 bv (lowv N₃ hNv) hN2 (lowv one₃ (Nat.one_lt_two_pow (by omega_arith))) X₃)
    fun t ⟨X3, G, f4, k4⟩ => ?_
  have h₄ := h₃.step f4 (fun y => by p2_omega) k4 (by simp)
  refine ⟨h₄, ?_, ?_, ?_, X3, G⟩
  · unfold mw
    rw [f4.word_eq (fun y => by p2_omega) (by p2_omega), f₃.word_eq (fun y => by p2_omega) (by p2_omega)]
    exact hm₂
  · rw [f4.wv_eq (fun y => by p2_omega) (by p2_omega), N₃]
  · rw [f4.wv_eq (fun y => by p2_omega) (by p2_omega), one₃]

/-! ## `a`, `m`, `r`, `m + 1`, `n - r` and `b` -/

abbrev p3 : List (Prog isa) := [.block (width true)] ++ (divA ++ ([.block (width false)] ++ divB))

/-- The model's `a`, from `x'` and the GCD. -/
theorem aOf_eq {nb wb N DE : Nat} (hx : (twosOut nb wb N DE).2.2 < 2 ^ wb)
    (hg : Nat.gcd (twosOut nb wb N DE).1 (twosOut nb wb N DE).2.1 < 2 ^ nb) :
    aOf nb wb N DE = (twosOut nb wb N DE).2.2 * Nat.gcd (twosOut nb wb N DE).1 (twosOut nb wb N DE).2.1 % 2 ^ wb := by
  unfold aOf
  rw [prod_iter _ _ _ hx]
  simp only
  rw [Nat.mod_eq_of_lt hg, Nat.mul_comm]

/-- `a`, `m = a / n` and `r = a mod n` and whether `m < n` (wide), then
`m + 1`, `n - r`, their quotient `q` and remainder, whether it is zero, and
`b` (narrow), as the model gives them. -/
theorem phase3_ok {I : RpIn} {m₀ : Mem} {s : State} (h : DS I m₀ (nv I.k) s) (L : RpLens I)
    {N DE : Nat} {c : Bool} (hN0 : 0 < N) (hm : mw s.mem I.B = mask c)
    (hn : wv s.mem I.B (slot (nv I.k) 0) (2 * (nv I.k + 2)) = N)
    (hone : wv s.mem I.B (slot (nv I.k) 2) (2 * (nv I.k + 2)) = 1)
    (hX : wv s.mem I.B (slot (nv I.k) 4) (wW I.k) = (twosOut (nbk I.k) (wbk I.k) N DE).2.2)
    (hG : wv s.mem I.B (slot (nv I.k) 12) (2 * (nv I.k + 2)) =
      Nat.gcd (twosOut (nbk I.k) (wbk I.k) N DE).1 (twosOut (nbk I.k) (wbk I.k) N DE).2.1)
    (hGv : Nat.gcd (twosOut (nbk I.k) (wbk I.k) N DE).1 (twosOut (nbk I.k) (wbk I.k) N DE).2.1 < 2 ^ nbk I.k)
    (hNv : N < 2 ^ nbk I.k) :
    WP isa (seqs p3) s fun t => ∃ q rem : Nat,
      (0 < m1Of (nbk I.k) (wbk I.k) N DE → q = dOf (nbk I.k) (wbk I.k) N DE / m1Of (nbk I.k) (wbk I.k) N DE ∧
        rem = dOf (nbk I.k) (wbk I.k) N DE % m1Of (nbk I.k) (wbk I.k) N DE) ∧
      DS I m₀ (nv I.k) t ∧ mw t.mem I.B = mask (c && ltOf (nbk I.k) (wbk I.k) N DE && decide (rem = 0)) ∧
      wv t.mem I.B (slot (nv I.k) 0) (2 * (nv I.k + 2)) = N ∧
      wv t.mem I.B (slot (nv I.k) 2) (2 * (nv I.k + 2)) = 1 ∧
      wv t.mem I.B (slot (nv I.k) 8) (2 * (nv I.k + 2)) = bOf (nbk I.k) q ∧
      word t.mem I.B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 (4 * wW I.k - 8) := by
  have hnw := h.ws.scr.nowrap
  have ⟨bW, b26, bv, bv9⟩ := rd_bounds L.k1 L.k2 L.z
  have hZW : 256 + 16 * (8 * (wW I.k + 2)) ≤ I.Z := bW
  have hZ' : 256 + 26 * (8 * (nv I.k + 2)) ≤ I.Z := b26
  have hW : wW I.k = 2 * nv I.k + 2 := rfl
  have lowW : ∀ {m : Mem} {d X : Nat}, wv m I.B d (2 * (nv I.k + 2)) = X → X < 2 ^ (64 * wW I.k) →
      wv m I.B d (wW I.k) = X := fun e hx => by
    rw [wv_low_of_lt (v := wW I.k) (w := 2 * (nv I.k + 2)) (by omega_arith) (by rw [e]; exact hx), e]
  have pvW : 2 ^ nbk I.k ≤ 2 ^ (64 * wW I.k) := Nat.pow_le_pow_right (by decide) (by p2_omega)
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
  have G₁ : wv t₁.mem I.B (slot (wW I.k) 6) (wW I.k) = Gt := by
    rw [slot_wide, f₁.wv_eq (fun y => by p2_omega) (by p2_omega)]; exact lowW hG (by omega_arith)
  have X₁ : wv t₁.mem I.B (slot (wW I.k) 2) (wW I.k) = Xt := by
    rw [slot_wide, f₁.wv_eq (fun y => by p2_omega) (by p2_omega)]; exact hX
  have hm₁ : mw t₁.mem I.B = mask c := by
    unfold mw at hm ⊢; rw [f₁.word_eq (fun y => by p2_omega) (by p2_omega), hm]
  refine wp_seqs_append (by simp [divA]) (by simp) (WP.mono (divA_ok h₁.ws hW (by omega_arith) n₁ hN0 G₁ hGv X₁ hm₁)
    fun t₂ ⟨M₂, R₂, hm₂, el₂, f₂, k₂⟩ => ?_)
  simp only [wbk] at hA
  rw [← hA] at M₂ R₂ hm₂
  have h₂ := h₁.step f₂ (fun y => by p2_omega) k₂ (by simp)
  -- The narrow width.
  refine wp_seqs_append (by simp) (by simp [divB]) (WP.mono (h₂.width false L) fun t₃ ⟨h₃, _, f₃, k₃⟩ => ?_)
  replace h₃ : DS I m₀ (nv I.k) t₃ := h₃
  have lowv : ∀ {m : Mem} {d X : Nat}, wv m I.B d (2 * (nv I.k + 2)) = X → X < 2 ^ (64 * nv I.k) →
      wv m I.B d (nv I.k) = X := fun e hx => by
    rw [wv_low_of_lt (v := nv I.k) (w := 2 * (nv I.k + 2)) (by omega_arith) (by rw [e]; exact hx), e]
  have n₃ : wv t₃.mem I.B (slot (nv I.k) 0) (2 * (nv I.k + 2)) = N := by
    rw [f₃.wv_eq (fun y => by p2_omega) (by p2_omega), f₂.wv_eq (fun y => by p2_omega) (by p2_omega),
      f₁.wv_eq (fun y => by p2_omega) (by p2_omega), hn]
  have one₃ : wv t₃.mem I.B (slot (nv I.k) 2) (2 * (nv I.k + 2)) = 1 := by
    rw [f₃.wv_eq (fun y => by p2_omega) (by p2_omega), f₂.wv_eq (fun y => by p2_omega) (by p2_omega),
      f₁.wv_eq (fun y => by p2_omega) (by p2_omega), hone]
  have z₃ : wv t₃.mem I.B (slot (nv I.k) 3) (nv I.k) = 0 := by
    have e := one₃
    rw [show 2 * (nv I.k + 2) = (nv I.k + 2) + (nv I.k + 2) by omega_arith, wv_add,
      show slot (nv I.k) 2 + 8 * (nv I.k + 2) = slot (nv I.k) 3 by simp only [Bignum.slot, hdrBytes]; omega_arith] at e
    have : wv t₃.mem I.B (slot (nv I.k) 3) (nv I.k + 2) = 0 := by
      rcases Nat.eq_zero_or_pos (wv t₃.mem I.B (slot (nv I.k) 3) (nv I.k + 2)) with h0 | h0
      · exact h0
      · exfalso
        have : 2 ^ (64 * (nv I.k + 2)) ≤ 2 ^ (64 * (nv I.k + 2)) * wv t₃.mem I.B (slot (nv I.k) 3) (nv I.k + 2) :=
          Nat.le_mul_of_pos_right _ h0
        have := Nat.one_lt_two_pow (n := 64 * (nv I.k + 2)) (by omega_arith)
        omega_arith
    have := wv_zero_sub (a := 0) (k := nv I.k) this (by omega_arith)
    simpa using this
  have M₃ : wv t₃.mem I.B (slot (nv I.k) 14) (nv I.k) = mOf (nbk I.k) (wbk I.k) N DE % 2 ^ (64 * nv I.k) := by
    rw [f₃.wv_eq (fun y => by p2_omega) (by p2_omega),
      show mOf (nbk I.k) (wbk I.k) N DE = wv t₂.mem I.B (slot (wW I.k) 7) (wW I.k) from M₂.symm, slot_wide, hW,
      show 2 * nv I.k + 2 = nv I.k + (nv I.k + 2) by omega_arith]
    exact wv_low_mod
  have R₃ : wv t₃.mem I.B (slot (nv I.k) 12) (nv I.k) = rOf (nbk I.k) (wbk I.k) N DE % 2 ^ (64 * nv I.k) := by
    rw [f₃.wv_eq (fun y => by p2_omega) (by p2_omega),
      show rOf (nbk I.k) (wbk I.k) N DE = wv t₂.mem I.B (slot (wW I.k) 6) (wW I.k) from R₂.symm, slot_wide, hW,
      show 2 * nv I.k + 2 = nv I.k + (nv I.k + 2) by omega_arith]
    exact wv_low_mod
  have hm₃ : mw t₃.mem I.B = mask (c && ltOf (nbk I.k) (wbk I.k) N DE) := by
    unfold mw at hm₂ ⊢; rw [f₃.word_eq (fun y => by p2_omega) (by p2_omega), hm₂]; rfl
  refine WP.mono (divB_ok h₃.ws (lowv n₃ hNv) (lowv one₃ (Nat.one_lt_two_pow (by omega_arith))) z₃ M₃ R₃ hm₃)
    fun t ⟨q, rem, hqr, B₄, hm₄, f₄, k₄⟩ => ⟨q, rem, hqr, h₃.step f₄ (fun y => by p2_omega) k₄ (by simp),
      hm₄, ?_, ?_, B₄, ?_⟩
  · rw [f₄.wv_eq (fun y => by p2_omega) (by p2_omega), n₃]
  · rw [f₄.wv_eq (fun y => by p2_omega) (by p2_omega), one₃]
  · rw [f₄.word_eq (fun y => by p2_omega) (by p2_omega), f₃.word_eq (fun y => by p2_omega) (by p2_omega), el₂]

end VG.Proof.Rsa.X86_64.Rd
