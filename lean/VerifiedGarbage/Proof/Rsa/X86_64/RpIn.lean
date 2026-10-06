import VerifiedGarbage.Proof.Rsa.X86_64.RpLt
import VerifiedGarbage.Proof.Rsa.X86_64.CvFail

/-!
# `vg_rsa_recover_primes` on x86-64: the arguments

`RpArgs`: the arguments `entry` leaves in the header, kept by the pieces;
`RpS`: what every piece of `main` keeps (the working space, the arguments,
the inputs' bytes, and memory outside the working space), from a frame of
arrays and slots of `rSlot` (`RpS.step`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN)

/-- The inputs of `vg_rsa_recover_primes` and where they are. -/
structure RpIn where
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
  sv : Nat → BitVec 64
  nb : List Byte
  eb : List Byte
  db : List Byte
  W : List Region
  sp : BitVec 64

/-- The arguments in the header: the outputs' pointers, `n`'s, `e`'s and
`d`'s pointers and lengths, and the saved registers `sv`. -/
structure RpArgs (m : Mem) (B : Addr) (k el dl : Nat) (pP pQ pN pE pD : Addr) (sv : Nat → BitVec 64) : Prop where
  p : word m B (8 * sP) = pP
  q : word m B (8 * sQ) = pQ
  n : word m B (8 * Impl.Bignum.X86_64.Public.sN) = pN
  k : word m B (8 * Impl.Bignum.X86_64.Public.sK) = BitVec.ofNat 64 k
  e : word m B (8 * Impl.Bignum.X86_64.Public.sE) = pE
  el : word m B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el
  d : word m B (8 * sD) = pD
  dl : word m B (8 * sDl) = BitVec.ofNat 64 dl
  saved : ∀ i < 6, word m B (8 * i) = sv i

/-- The header slots of `RpArgs`. -/
def rArg (i : Nat) : Prop := i < 6 ∨ (16 ≤ i ∧ i < 22) ∨ i = 23 ∨ i = 24

theorem RpArgs.congr {m m' : Mem} {B : Addr} {k el dl : Nat} {pP pQ pN pE pD : Addr} {sv : Nat → BitVec 64}
    (h : RpArgs m B k el dl pP pQ pN pE pD sv) (hm : ∀ i, rArg i → word m' B (8 * i) = word m B (8 * i)) :
    RpArgs m' B k el dl pP pQ pN pE pD sv :=
  ⟨(hm _ (by simp [rArg, sP, Impl.Bignum.X86_64.Public.sOut, sFn])).trans h.p,
    (hm _ (by simp [rArg, sQ, Impl.Bignum.X86_64.Public.sIn, sFn])).trans h.q,
    (hm _ (by simp [rArg, Impl.Bignum.X86_64.Public.sN, sFn])).trans h.n,
    (hm _ (by simp [rArg, Impl.Bignum.X86_64.Public.sK, sFn])).trans h.k,
    (hm _ (by simp [rArg, Impl.Bignum.X86_64.Public.sE, sFn])).trans h.e,
    (hm _ (by simp [rArg, Impl.Bignum.X86_64.Public.sElen, sFn])).trans h.el,
    (hm _ (by simp [rArg, sD, Impl.Bignum.X86_64.Public.sI, sFn])).trans h.d,
    (hm _ (by simp [rArg, sDl, Impl.Bignum.X86_64.Public.sBit, sFn])).trans h.dl,
    fun i hi => (hm i (Or.inl hi)).trans (h.saved i hi)⟩

/-- An argument slot is not a slot of `rSlot`. -/
theorem rArg_rSlot {i : Nat} (hi : rArg i) : rSlot i = false := by
  unfold rArg at hi
  simp only [rSlot, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  omega

/-- The argument slots, after code that changes only arrays and slots of
`rSlot`. -/
theorem rArg_frm {m m' : Mem} {B : Addr} {w : Nat} {js hs : List Nat} (hf : Frm B (rg w js hs) m m')
    (hhs : ∀ i ∈ hs, rSlot i = true) : ∀ i, rArg i → word m' B (8 * i) = word m B (8 * i) := fun i hi =>
  hf.rg_word (by unfold rArg at hi; omega) fun hm => by have := hhs i hm; rw [rArg_rSlot hi] at this; cases this

/-- What every piece of `main` keeps, from the memory `m₀` on entry to
`main`. -/
structure RpS (I : RpIn) (m₀ : Mem) (s : State) : Prop where
  ws : Ws s I.B I.Z (wk I.k)
  args : RpArgs s.mem I.B I.k I.el I.dl I.pP I.pQ I.pN I.pE I.pD I.sv
  n : Src s I.B I.Z I.pN I.nb
  e : Src s I.B I.Z I.pE I.eb
  d : Src s I.B I.Z I.pD I.db
  inScr : InScr I.B I.Z m₀ s.mem
  wr : s.wr = I.W
  rsp : s.gpr .rsp = I.sp

/-- The ranges of `rg` are in the working space. -/
theorem rg_le {w Z : Nat} (hZ : slot w 16 ≤ Z) {js hs : List Nat} (hjs : ∀ j ∈ js, j < 16)
    (hhs : ∀ i ∈ hs, i < 32) : ∀ r ∈ rg w js hs, r.1 + r.2 ≤ Z := by
  intro r hr
  simp only [rg, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨j, hj, rfl⟩ | ⟨i, hi, rfl⟩
  · have := slot_lt (w := w) (hjs j hj); dsimp only; omega
  · have := hdr_lt_slot w 16 (hhs i hi); dsimp only; omega

theorem RpS.step {I : RpIn} {m₀ : Mem} {s t : State} (h : RpS I m₀ s) {js hs : List Nat}
    (hf : Frm I.B (rg (wk I.k) js hs) s.mem t.mem) (hjs : ∀ j ∈ js, j < 16) (hhs : ∀ i ∈ hs, rSlot i = true)
    {regs : List Reg} (k : Keep regs s t) (hr : .rdi ∉ regs ∧ .rsp ∉ regs) : RpS I m₀ t :=
  have h32 : ∀ i ∈ hs, i < 32 := fun i hi => by
    have := hhs i hi; simp only [rSlot, Bool.or_eq_true, beq_iff_eq] at this; omega
  have hi : InScr I.B I.Z s.mem t.mem := InScr.of_frm hf (rg_le h.ws.hZ hjs h32)
  ⟨h.ws.congrG hf hhs k hr.1, h.args.congr (rArg_frm hf hhs), h.n.congrK hi k, h.e.congrK hi k,
    h.d.congrK hi k, h.inScr.trans hi, k.2.2.trans h.wr, (k.gpr hr.2).trans h.rsp⟩

/-- The lengths, as `vg_rsa_recover_primes`'s contract bounds them. -/
structure RpLens (I : RpIn) : Prop where
  k1 : 64 ≤ I.k
  k2 : I.k ≤ 1024
  el1 : 1 ≤ I.el
  el2 : I.el ≤ I.k
  dl1 : 1 ≤ I.dl
  dl2 : I.dl ≤ I.k
  nbl : I.nb.length = I.k
  ebl : I.eb.length = I.el
  dbl : I.db.length = I.dl
  z : 128 * I.k ≤ I.Z

/-- The loads of `n`, `e` and `d`. -/
theorem rpLoads_ok {I : RpIn} {m₀ : Mem} {s : State} (h : RpS I m₀ s) (L : RpLens I) :
    WP isa (seqs (loadA aN Impl.Bignum.X86_64.Public.sN Impl.Bignum.X86_64.Public.sK ++
      (loadA aE Impl.Bignum.X86_64.Public.sE Impl.Bignum.X86_64.Public.sElen ++ loadA aD sD sDl))) s fun t =>
      RpS I m₀ t ∧ Frm I.B (rg (wk I.k) [aN, aE, aD] []) s.mem t.mem ∧
      wv t.mem I.B (slot (wk I.k) aN) (wk I.k) = Spec.Rsa.os2ip I.nb ∧
      wv t.mem I.B (slot (wk I.k) aE) (wk I.k) = Spec.Rsa.os2ip I.eb ∧
      wv t.mem I.B (slot (wk I.k) aD) (wk I.k) = Spec.Rsa.os2ip I.db ∧ Keep mmRegs s t := by
  have hk1 := L.k1
  have hk2 := L.k2
  have hel := L.el2
  have hdl := L.dl2
  have hZ16 : slot (wk I.k) 16 ≤ 2 ^ 64 := by have := h.ws.scr.nowrap; have := h.ws.hZ; omega
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (loadA_ok h.ws (j := aN) (by decide)
    (by decide) (by decide) h.args.n h.args.k h.n L.nbl (by omega) (by unfold wk; omega))
    fun s₁ ⟨v₁, o₁, k₁⟩ => ?_)
  have f₁ : Frm I.B (rg (wk I.k) [aN] []) s.mem s₁.mem := Frm.rg_of_out o₁ (Nat.le_refl _) _ _ (by decide)
  have h₁ := h.step f₁ (by decide) (by simp) k₁ (by decide)
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (loadA_ok h₁.ws (j := aE) (by decide)
    (by decide) (by decide) h₁.args.e h₁.args.el h₁.e L.ebl L.el1 (by unfold wk; omega))
    fun s₂ ⟨v₂, o₂, k₂⟩ => ?_)
  have f₂ : Frm I.B (rg (wk I.k) [aE] []) s₁.mem s₂.mem := Frm.rg_of_out o₂ (Nat.le_refl _) _ _ (by decide)
  have h₂ := h₁.step f₂ (by decide) (by simp) k₂ (by decide)
  refine WP.mono (loadA_ok h₂.ws (j := aD) (by decide) (by decide) (by decide) h₂.args.d h₂.args.dl h₂.d L.dbl
    L.dl1 (by unfold wk; omega)) fun t ⟨v₃, o₃, k₃⟩ => ?_
  have f₃ : Frm I.B (rg (wk I.k) [aD] []) s₂.mem t.mem := Frm.rg_of_out o₃ (Nat.le_refl _) _ _ (by decide)
  refine ⟨h₂.step f₃ (by decide) (by simp) k₃ (by decide), ((f₁.rg_trans f₂).rg_trans f₃).rg_mono (by decide)
    (by decide), ?_, ?_, v₃, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · rw [f₃.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega),
      f₂.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), v₁]
  · rw [f₃.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), v₂]

end VG.Proof.Rsa.X86_64
