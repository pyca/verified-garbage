module

public import VerifiedGarbage.Proof.Rsa.AArch64.RpMain
meta import VerifiedGarbage.Proof.Rsa.AArch64.RpMain
public import VerifiedGarbage.Proof.Rsa.AArch64.CvCTMain
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvCTMain
public import VerifiedGarbage.Proof.Rsa.RecoverTries
meta import VerifiedGarbage.Proof.Rsa.RecoverTries
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# `vg_rsa_recover_primes` on AArch64: constant time, what the pieces share

`RpP`: the public data of `vg_rsa_recover_primes` (the working space, the
pointers and lengths, `n` and `e`, and the number of candidates tried).
`GA p`: what holds between the pieces of `main` (`RpS`), for the public
data `p`; `GV F p`, with facts `F` about the memory. `GR0` … `GR3`: what
holds on entry to `rest`, after the halvings, after Montgomery form and
after the candidates. Pieces checked from the working space: `copyA`, `eqA`
and blocks checked from `x0` (`copyA_gct`, `eqA_gct`, `blk_gct`), a
Montgomery multiplication (`mm_gct`).

The pieces' proofs (`RpCT1` … `RpCT7`) import only this module and the
pieces they call, so that they are checked in parallel.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.Recover
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt sMask)
open VG.Spec.Rsa (splitTwos recoverStep recoverPrimes recoverTries)
open VG.Proof.Rsa (pqOf)

/-- The public data of `vg_rsa_recover_primes`. -/
structure RpP where
  B : Addr
  Z : Nat
  k : Nat
  el : Nat
  dl : Nat
  pP : Addr
  pQ : Addr
  pN : Addr
  pE : Addr
  pD : Addr
  nb : List Byte
  eb : List Byte
  W : List Region
  cnt : Nat
  deriving Inhabited

/-- The public part of the inputs. -/
def RpIn.pub (I : RpIn) : RpP :=
  ⟨I.B, I.Z, I.k, I.el, I.dl, I.pP, I.pQ, I.pN, I.pE, I.pD, I.nb, I.eb, I.W,
    (Spec.Rsa.primesKey I.nb I.eb I.db).2⟩

/-- The outputs: writable, outside the working space, and apart. -/
structure RpOuts (I : RpIn) : Prop where
  p : ∀ i < I.k, InRegions I.W (I.pP + BitVec.ofNat 64 i) 1
  q : ∀ i < I.k, InRegions I.W (I.pQ + BitVec.ofNat 64 i) 1
  sp : ∀ i < I.k, I.Z ≤ ofs I.B (I.pP + BitVec.ofNat 64 i)
  sq : ∀ i < I.k, I.Z ≤ ofs I.B (I.pQ + BitVec.ofNat 64 i)
  a : Apart I.pP I.k I.pQ I.k

theorem RpPre.outs {I : RpIn} {s : State} (h : RpPre I s) : RpOuts I :=
  ⟨fun i hi => by rw [← h.wr]; exact h.oP.wr i hi, fun i hi => by rw [← h.wr]; exact h.oQ.wr i hi,
    h.oP.sep, h.oQ.sep, h.a⟩

/-- `ws`, a block checked from `x0`, `x12` and `x11` that leaves the
registers `rs₂` with values of the public data, and code checked from
`rs₂`. -/
theorem ws_pin_ct {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat) {rest : List Instr}
    {c₂ : Prog isa} (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.block rest) hc₁).isSome = true)
    (rs₂ : List Reg) (f : α → Reg → BitVec 64)
    (hp : ∀ a s, Φ a s → WP isa (.block (ws ++ rest)) s fun t => ∀ r ∈ rs₂, t.gpr r = f a r)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T} (ht₂ : (taint.check (Taint.ofRegs rs₂) c₂ hc₂).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa (.seq (.block (ws ++ rest)) c₂) s (Ψ a)) :
    RelCT isa (Two Φ) (.seq (.block (ws ++ rest)) c₂) (Two Ψ) := by
  refine RelCT.block_seq (RelCT.seq (two_piece (Ψ := fun a t =>
      (∀ r ∈ [Reg.x0, .x12, .x11], t.gpr r = wsVal (B a) (w a) r) ∧
      WP isa (.block rest) t (fun u => ∀ r ∈ rs₂, u.gpr r = f a r) ∧ WP isa (.seq (.block rest) c₂) t (Ψ a))
      [.x0] (pins_ws B Z w hws) (by taint_decide) fun a s h => ?_)
    (pin_ct [.x0, .x12, .x11] rs₂ f (fun a s₁ s₂ h₁ h₂ r hr => (h₁.1 r hr).trans (h₂.1 r hr).symm) ht₁
      (fun a t h => h.2.1) ht₂ fun a t h => h.2.2))
  have e₁ := WP.block_append_iff.mp (hp a s h)
  have e₂ := WP.block_seq_iff.mp (hw a s h)
  exact WP.mono (WP.and (WP.and (ws_pin (hws a s h)) e₁) (WP.seq_iff.mp e₂)) fun t ⟨⟨hr, w₁⟩, w₂⟩ =>
    ⟨hr, w₁, w₂⟩

namespace Rp

/-- On entry to `main`. -/
def GM (p : RpP) (s : State) : Prop :=
  ∃ I : RpIn, I.pub = p ∧ RpPre I s ∧ Spec.Rsa.modulusValid I.N I.k = true

/-- Between the pieces of `main`. -/
def GA (p : RpP) (s : State) : Prop :=
  ∃ (I : RpIn) (m₀ : Mem), I.pub = p ∧ RpS I m₀ s ∧ RpLens I ∧ RpOuts I ∧
    Spec.Rsa.modulusValid I.N I.k = true

theorem GA.ws {p : RpP} {s : State} (h : GA p s) : Ws s p.B p.Z (wk p.k) := by
  obtain ⟨I, m₀, rfl, h, -⟩ := h
  exact h.ws

theorem pins_GA : Pins GA [.x0] := pins_ws RpP.B RpP.Z (fun p => wk p.k) fun _ _ h => h.ws

theorem pins_GM : Pins GM [.x0] := fun _ _ _ ⟨_, e₁, h₁, _⟩ ⟨_, e₂, h₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [h₁.x0, h₂.x0]
  exact (congrArg RpP.B e₁).trans (congrArg RpP.B e₂).symm

/-- `GA` after a piece that changes only arrays and slots of `rSlot`. -/
theorem GA.step {p : RpP} {s t : State} (h : GA p s) {js hs : List Nat}
    (hf : Frm p.B (rg (wk p.k) js hs) s.mem t.mem) (hjs : ∀ j ∈ js, j < 16) (hhs : ∀ i ∈ hs, rSlot i = true)
    {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs) : GA p t := by
  obtain ⟨I, m₀, rfl, h, L, O, hv⟩ := h
  exact ⟨I, m₀, rfl, h.step hf hjs hhs k hr, L, O, hv⟩

/-- `GA` after a piece that changes no memory. -/
theorem GA.same {p : RpP} {s t : State} (h : GA p s) (hm : t.mem = s.mem) {regs : List Reg} (k : Keep regs s t)
    (hr : .x0 ∉ regs) : GA p t :=
  h.step (js := []) (hs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) (by simp) k hr

/-- `GA` after a piece that changes only array `j`'s first `n` bytes. -/
theorem GA.arr {p : RpP} {s t : State} (h : GA p s) {j n : Nat} (hj : j < 16) (hn : n ≤ 8 * (wk p.k + 2))
    (o : Outside p.B (slot (wk p.k) j) n s.mem t.mem) {regs : List Reg} (k : Keep regs s t)
    (hr : .x0 ∉ regs) : GA p t :=
  h.step (Frm.rg_of_out o hn [j] [] (List.mem_singleton_self _)) (by simp [hj]) (by simp) k hr

/-- `GA` with facts `F` about the memory. -/
def GV (F : RpIn → Mem → Prop) (p : RpP) (s : State) : Prop :=
  ∃ (I : RpIn) (m₀ : Mem), I.pub = p ∧ RpS I m₀ s ∧ RpLens I ∧ RpOuts I ∧
    Spec.Rsa.modulusValid I.N I.k = true ∧ F I s.mem

theorem GV.ga {F : RpIn → Mem → Prop} {p : RpP} {s : State} (h : GV F p s) : GA p s := by
  obtain ⟨I, m₀, e, h, L, O, hv, -⟩ := h
  exact ⟨I, m₀, e, h, L, O, hv⟩

theorem GV.ws {F : RpIn → Mem → Prop} {p : RpP} {s : State} (h : GV F p s) : Ws s p.B p.Z (wk p.k) := h.ga.ws

theorem pins_GV {F : RpIn → Mem → Prop} : Pins (GV F) [.x0] :=
  pins_ws RpP.B RpP.Z (fun p => wk p.k) fun _ _ h => h.ws

/-! ## Between the pieces of `rest` -/

/-- On entry to `rest`. -/
def GR0 (p : RpP) (s : State) : Prop :=
  ∃ (I : RpIn) (m₀ : Mem), I.pub = p ∧ RestPre I m₀ I.N (I.D * I.E - 1) s ∧ RpOuts I ∧
    Spec.Rsa.modulusValid I.N I.k = true

/-- The halvings' count, `64 Bw`. -/
abbrev hN (p : RpP) : Nat := 64 * (wk p.k + (p.el + 7) / 8)

/-- After the halvings: `r` and `t`, and what Montgomery form needs. -/
def GR1 (p : RpP) (s : State) : Prop :=
  ∃ (I : RpIn) (m₀ : Mem), I.pub = p ∧ RpS I m₀ s ∧ RpLens I ∧ RpOuts I ∧
    Spec.Rsa.modulusValid I.N I.k = true ∧ I.N % 2 = 1 ∧ 2 ^ (64 * (wk I.k - 1)) ≤ I.N ∧
    wv s.mem I.B (slot (wk I.k) aN) (wk I.k) = I.N ∧
    ((word s.mem I.B (slot (wk I.k) aN)).toNat * (word s.mem I.B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0 ∧
    wv s.mem I.B (slot (wk I.k) aM) (2 * (wk I.k + 2)) = (splitTwos (I.D * I.E - 1)).2 ∧
    word s.mem I.B (8 * sT) = BitVec.ofNat 64 (splitTwos (I.D * I.E - 1)).1 ∧
    0 < I.D * I.E - 1 ∧ (I.D * I.E - 1) % 2 = 0 ∧ I.D * I.E - 1 < 2 ^ (64 * (wk I.k + (I.el + 7) / 8))

/-- After Montgomery form: what the candidates need. -/
def GR2 (p : RpP) (s : State) : Prop :=
  ∃ (I : RpIn) (m₀ : Mem), I.pub = p ∧ RpS I m₀ s ∧ RpLens I ∧ RpOuts I ∧
    Spec.Rsa.modulusValid I.N I.k = true ∧
    Cst s I.B I.Z (wk I.k) (word s.mem I.B (8 * sMinv)) I.N I.el (splitTwos (I.D * I.E - 1)).2
      (splitTwos (I.D * I.E - 1)).1 ∧ 0 < I.D * I.E - 1 ∧ (I.D * I.E - 1) % 2 = 0

/-- After the candidates: `recoverPrimes.go`'s result, and what the factors
need. -/
def GR3 (p : RpP) (s : State) : Prop :=
  ∃ (I : RpIn) (m₀ : Mem) (minv : BitVec 64) (res : Option Nat) (cnt : Nat), I.pub = p ∧ RpS I m₀ s ∧
    RpLens I ∧ RpOuts I ∧ Spec.Rsa.modulusValid I.N I.k = true ∧
    Cst s I.B I.Z (wk I.k) minv I.N I.el (splitTwos (I.D * I.E - 1)).2 (splitTwos (I.D * I.E - 1)).1 ∧
    recoverPrimes.go I.N (splitTwos (I.D * I.E - 1)).1 (splitTwos (I.D * I.E - 1)).2 recoverTries =
      (res.map (pqOf I.N), cnt) ∧ word s.mem I.B (8 * sC3) = mask res.isSome ∧
    (∀ y, res = some y → wv s.mem I.B (slot (wk I.k) aY) (wk I.k) = y * 2 ^ (64 * wk I.k) % I.N ∧ y < I.N ∧
      y * y % I.N = 1)

/-! ## Pieces checked from the working space, from correctness -/

theorem copyA_gct {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat)
    (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) {o a : Nat} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base a .x16 ++ base o .x17)) copyWords)
      hc).isSome = true)
    (hw : ∀ x s, Φ x s → WP isa (copyA o a) s (Ψ x)) : RelCT isa (Two Φ) (copyA o a) (Two Ψ) := by
  have e : copyA o a = .seq (.block (ws ++ (base a .x16 ++ base o .x17))) copyWords := by
    simp only [copyA, List.append_assoc]
  rw [e]
  exact ws_ct B Z w hws ht fun x s h => by rw [← e]; exact hw x s h

theorem eqA_gct {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat)
    (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) {a b : Nat} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block [movi .x9 0, mov .x14 .x12])
      (.seq (.block (base a .x16 ++ base b .x17)) (countLoop .x14 xorBody))) hc).isSome = true)
    (hw : ∀ x s, Φ x s → WP isa (seqs (eqA a b)) s (Ψ x)) : RelCT isa (Two Φ) (seqs (eqA a b)) (Two Ψ) :=
  ws_ct B Z w hws ht hw

theorem blk_gct {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat)
    (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) {l : List Instr} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0]) (.block l) hc).isSome = true)
    (hw : ∀ x s, Φ x s → WP isa (.block l) s (Ψ x)) : RelCT isa (Two Φ) (.block l) (Two Ψ) :=
  two_piece [.x0] (pins_ws B Z w hws) ht hw

theorem mm_gct {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat)
    (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) (M : Mont) {o a b : Nat} (hu : MmUse o a b)
    (hw : ∀ x s, Φ x s → WP isa (M.mm o a b) s (Ψ x)) : RelCT isa (Two Φ) (M.mm o a b) (Two Ψ) :=
  two_post (two_map (fun x => (⟨B x, Z x, w x⟩ : VG.Proof.Bignum.AArch64.Ws)) (fun x s h => ⟨_, (hws x s h).good⟩)
    (M.ct hu)) hw

end Rp

end VG.Proof.Rsa.AArch64
