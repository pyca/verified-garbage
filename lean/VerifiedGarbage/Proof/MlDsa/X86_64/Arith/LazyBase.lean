import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YLay21
import VerifiedGarbage.Proof.MlDsa.Arith.Lazy

/-! Doubleword storage relations for lazy NTT coefficients. -/
namespace VG.Proof.MlDsa.X86_64.Arith.Lazy
open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.Arith.Lazy
open VG.Proof.MlKem.X86_64 (Keep XOnly XKeep YOnly ylanes yld_ok yconst_ok ifp ifn)
open VG.Spec.MlDsa (q n Zq coeffAt zetas)

/-- The lazy butterfly also keeps twice q in xmm11. -/
structure VConsts (s : State) : Prop extends Arith.VConsts s where
  q2 : s.xmm .xmm11 = ofDwords 16760834#32 16760834#32 16760834#32 16760834#32

def YConsts (s : State) : Prop := ∀ l < 2, VConsts (s.proj l)

theorem xonly_vconsts {rs : List XReg} {s s' : State} (h : XOnly rs s s') (hc : VConsts s)
    (h14 : XReg.xmm14 ∉ rs) (h15 : XReg.xmm15 ∉ rs) (h11 : XReg.xmm11 ∉ rs := by decide) : VConsts s' :=
  ⟨Arith.xonly_vconsts h hc.toVConsts h14 h15, by rw [h.xmm _ h11]; exact hc.q2⟩

theorem yonly_yconsts {rs : List XReg} {s s' : State} (h : YOnly rs s s') (hc : YConsts s)
    (h14 : XReg.xmm14 ∉ rs) (h15 : XReg.xmm15 ∉ rs) (h11 : XReg.xmm11 ∉ rs := by decide) : YConsts s' :=
  fun l hl => ⟨⟨by rw [State.proj_xmm, h.lane _ h15 l hl]; exact (hc l hl).q,
    by rw [State.proj_xmm, h.lane _ h14 l hl]; exact (hc l hl).qinv⟩,
    by rw [State.proj_xmm, h.lane _ h11 l hl]; exact (hc l hl).q2⟩

structure BInvY (fP : Addr) (s₀ s : State) : Prop where
  keep : Keep [.r8, .rcx, .rdx, .rax] s₀ s
  frame : Frame [pR fP] s₀.mem s.mem
  consts : YConsts s
  mxcsr : s.mxcsr = s₀.mxcsr

theorem BInvY.trans {fP : Addr} {s₁ s₂ s₃ : State} (h₁ : BInvY fP s₁ s₂) (h₂ : BInvY fP s₂ s₃) :
    BInvY fP s₁ s₃ :=
  ⟨(h₁.keep.trans h₂.keep).mono (by simp), h₁.frame.trans h₂.frame, h₂.consts, h₂.mxcsr.trans h₁.mxcsr⟩

theorem ylanes_gpr {s s' : State} (h : ∀ r l, s'.lane r l = s.lane r l) {rs : List XReg} {s₀ : State}
    (o : YOnly rs s₀ s) (hc : YConsts s₀) (h14 : XReg.xmm14 ∉ rs) (h15 : XReg.xmm15 ∉ rs)
    (h11 : XReg.xmm11 ∉ rs := by decide) : YConsts s' :=
  fun l hl => ⟨⟨by rw [State.proj_xmm, h]; exact (yonly_yconsts o hc h14 h15 h11 l hl).q,
    by rw [State.proj_xmm, h]; exact (yonly_yconsts o hc h14 h15 h11 l hl).qinv⟩,
    by rw [State.proj_xmm, h]; exact (yonly_yconsts o hc h14 h15 h11 l hl).q2⟩

def PolyIs (m : Mem) (p : Addr) (f : Poly) : Prop :=
  ∀ i < n, (coeffAt m p i).toNat = f[i]!.val

theorem polyIs_toNat {m : Mem} {p : Addr} {f : Poly} (h : PolyIs m p f) {i : Nat} (hi : i < n) :
    (coeffAt m p i).toNat = f[i]!.val := h i hi

theorem polyIs_of_toNat {m : Mem} {p : Addr} {f : Poly}
    (h : ∀ i < n, (coeffAt m p i).toNat = f[i]!.val) : PolyIs m p f := h

def DLanes (x : BitVec 128) (f : Nat → Word) : Prop := ∀ i < 4, (dword x i).toNat = (f i).val

theorem dlanes_load {m : Mem} {p : Addr} {F : Poly} (h : PolyIs m p F) {j : Nat} (hj : j + 4 ≤ 256) :
    DLanes (m.readW (coeffAddr p j) 128) (fun e => F[j + e]!) := fun e he => by
  rw [dword_readW _ _ he, coeffAddr_add, ← coeffAt_eq]
  exact polyIs_toNat h (by rw [n_eq]; omega)

def YLanes (x : BitVec 256) (a : Nat → Word) : Prop := ∀ e < 8, (x.extractLsb' (32 * e) 32).toNat = (a e).val

/-- A register whose lanes hold `a` and `a (· + 4)`. -/
theorem ylanes_ymm {s : State} {r : XReg} {a : Nat → Word} (h0 : DLanes (s.lane r 0) a)
    (h1 : DLanes (s.lane r 1) (fun e => a (e + 4))) : YLanes (s.ymm r) a := fun e he => by
  have h0' : DLanes (s.xmm r) a := h0
  have h1' : DLanes (s.ymmHi r) (fun e => a (e + 4)) := h1
  rw [State.ymm, extract_ymm _ _ he]
  split
  · exact h0' e (by omega)
  · rw [h1' (e - 4) (by omega)]; dsimp only; rw [show e - 4 + 4 = e by omega]

/-- Two vectors of eight coefficients stored into a polynomial. -/
theorem polyIs_write2Y {m : Mem} {p : Addr} {P R : Poly} (hP : PolyIs m p P) {j j' : Nat}
    (hj : j + 8 ≤ 256) (hj' : j' + 8 ≤ 256) (hsep : j + 8 ≤ j' ∨ j' + 8 ≤ j) {x y : BitVec 256}
    {a b : Nat → Word} (hx : YLanes x a) (hy : YLanes y b)
    (hR : ∀ i < 256, R[i]! = if j ≤ i ∧ i < j + 8 then a (i - j)
      else if j' ≤ i ∧ i < j' + 8 then b (i - j') else P[i]!) :
    PolyIs ((m.writeW (coeffAddr p j) x).writeW (coeffAddr p j') y) p R := polyIs_of_toNat fun i hi => by
  rw [n_eq] at hi
  rw [coeffAt_write256 _ _ hj' _ hi, coeffAt_write256 _ _ hj _ hi, hR i hi]
  by_cases h1 : j' ≤ i ∧ i < j' + 8
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_left_of_eq_true _ _ (eq_true h1)]
    exact hy _ (by omega)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
    by_cases h2 : j ≤ i ∧ i < j + 8
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), ite_eq_left_of_eq_true _ _ (eq_true h2)]
      exact hx _ (by omega)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h2), ite_eq_right_of_eq_false _ _ (eq_false h2),
        ite_eq_right_of_eq_false _ _ (eq_false h1)]
      exact polyIs_toNat hP (by rw [n_eq]; exact hi)

theorem dlanes_loadY {m : Mem} {p : Addr} {F : Poly} (h : PolyIs m p F) {j : Nat} (hj : j + 8 ≤ 256)
    {l : Nat} (hl : l < 2) :
    DLanes (m.readW (coeffAddr p j + BitVec.ofNat 64 (16 * l)) 128) (fun e => F[j + 4 * l + e]!) := by
  rw [lane_load]
  exact dlanes_load h (by omega)

def VBflyOk (bf : List Instr) (op : Word → Word → Zq → Word × Word) : Prop :=
  ∀ s : State, VConsts s → ∀ x y : Nat → Word, ∀ ζ : Nat → Zq, DLanes (s.xmm .xmm0) x → DLanes (s.xmm .xmm1) y →
    ZLanes (s.xmm .xmm13) ζ → ZOdd (s.xmm .xmm13) (s.xmm .xmm12) →
    WP isa (.block bf) s fun s' => DLanes (s'.xmm .xmm0) (fun i => (op (x i) (y i) (ζ i)).1) ∧
      DLanes (s'.xmm .xmm3) (fun i => (op (x i) (y i) (ζ i)).2) ∧
      XOnly [.xmm1, .xmm2, .xmm4, .xmm0, .xmm3] s s'


end VG.Proof.MlDsa.X86_64.Arith.Lazy
