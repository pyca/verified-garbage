import VerifiedGarbage.Impl.MlDsa.AArch64.Round.Round
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.Round.Decompose

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic`. -/
section

/-!
# ML-DSA on AArch64: what the rounding proofs share

* For each function, a contract with the facts of its shared contract
  (`Spec/MlDsa/Poly.lean`) spelled out for AArch64: the arguments in their
  registers, the permitted regions, their disjointness, and the
  postcondition. `Verified.of_correct` moves a proof to the shared
  contract, which implies it (`mldsa_implies`).
* `mapLoop ptrs cnt body` runs `body` for coefficients `0, …, 255`, with the
  pointers `ptrs` at coefficient `i` of their polynomials. `loop_ok` proves
  it once for every function: from a body that writes, to coefficient `i`
  of each output polynomial (the registers `outs`), the value `V o i`, and
  keeps an invariant `J` of its other registers, the loop writes every
  coefficient of each output. The inputs (registers `ins`) are never
  written, so the body reads the coefficients of the initial memory
  (`Inv.read`).
* The functions with `γ₂` first zero-extend it (`zext`): `zext_ok` runs it,
  and `zext_ct` proves constant time from the taint of the rest, where the
  whole register is public. `onGamma_ok` runs the branch on `γ₂`.
-/

namespace VG.Proof.MlDsa.AArch64.Round

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Round VG.Proof.MlDsa.Round
open VG.Proof.MlDsa.AArch64.Arith (writesOnly movW_ok wp_countdown Qv)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa (coeffAt polyAt Reduced PolyIs NatPolyIs HintIs hintAt gamma2s power2Round highBits
  lowBits normRq makeHint useHint hintOnes ofInt n)

/-! ## The contracts -/

/-- A `u32` argument in `r`. -/
abbrev arg32 (s : State) (r : Reg) : Nat := ((s.gpr r).setWidth 32).toNat

/-- `vg_mldsa_power2round(t = x0, t1 = x1, t0 = x2)`. -/
def power2RoundK : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .x0)] ∧ s.wr = [pR (s.gpr .x1), pR (s.gpr .x2)] ∧
    (pR (s.gpr .x0)).Disjoint (pR (s.gpr .x1)) ∧ (pR (s.gpr .x0)).Disjoint (pR (s.gpr .x2)) ∧
    (pR (s.gpr .x1)).Disjoint (pR (s.gpr .x2)) ∧ Reduced s.mem (s.gpr .x0)
  post s s' :=
    NatPolyIs s'.mem (s.gpr .x1) ((polyAt s.mem (s.gpr .x0)).map fun c => (power2Round c).1.toNat) ∧
      PolyIs s'.mem (s.gpr .x2) ((polyAt s.mem (s.gpr .x0)).map fun c => ofInt (power2Round c).2)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.sp = s₂.sp

/-- `r = x0, gamma2 = w1, out = x2`, with the postcondition `post`. -/
def bitsK (post : State → State → Prop) : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .x0)] ∧ s.wr = [pR (s.gpr .x2)] ∧ (pR (s.gpr .x0)).Disjoint (pR (s.gpr .x2)) ∧
    VG.Proof.MlDsa.AArch64.Round.arg32 s .x1 ∈ gamma2s ∧ Reduced s.mem (s.gpr .x0)
  post := post
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ (s₁.gpr .x1).setWidth 32 = (s₂.gpr .x1).setWidth 32 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.sp = s₂.sp

/-- `vg_mldsa_high_bits(r = x0, gamma2 = w1, out = x2)`. -/
def highBitsK : Contract isa := VG.Proof.MlDsa.AArch64.Round.bitsK fun s s' =>
  NatPolyIs s'.mem (s.gpr .x2) ((polyAt s.mem (s.gpr .x0)).map fun c => (highBits (VG.Proof.MlDsa.AArch64.Round.arg32 s .x1) c).toNat)

/-- `vg_mldsa_low_bits(r = x0, gamma2 = w1, out = x2)`. -/
def lowBitsK : Contract isa := VG.Proof.MlDsa.AArch64.Round.bitsK fun s s' =>
  PolyIs s'.mem (s.gpr .x2) ((polyAt s.mem (s.gpr .x0)).map fun c => ofInt (lowBits (VG.Proof.MlDsa.AArch64.Round.arg32 s .x1) c))

/-- `vg_mldsa_norm_lt(f = x0, bound = w1)`. -/
def normLtK : Contract isa where
  pre s := s.rd = [pR (s.gpr .x0)] ∧ s.wr = [] ∧ Reduced s.mem (s.gpr .x0)
  post s s' := (s'.gpr .x0).setWidth 32 = if normRq [polyAt s.mem (s.gpr .x0)] < VG.Proof.MlDsa.AArch64.Round.arg32 s .x1 then 1 else 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ (s₁.gpr .x1).setWidth 32 = (s₂.gpr .x1).setWidth 32 ∧
    s₁.sp = s₂.sp

/-- `a = x0, b = x1, gamma2 = w2, out = x3`, with the precondition `pre'` on
the memory and the postcondition `post`. -/
def hintK (pre' : State → Prop) (post : State → State → Prop) : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .x0), pR (s.gpr .x1)] ∧ s.wr = [pR (s.gpr .x3)] ∧
    (pR (s.gpr .x0)).Disjoint (pR (s.gpr .x3)) ∧ (pR (s.gpr .x1)).Disjoint (pR (s.gpr .x3)) ∧
    VG.Proof.MlDsa.AArch64.Round.arg32 s .x2 ∈ gamma2s ∧ pre' s
  post := post
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    (s₁.gpr .x2).setWidth 32 = (s₂.gpr .x2).setWidth 32 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-- `vg_mldsa_make_hint(z = x0, r = x1, gamma2 = w2, h = x3)`. -/
def makeHintK : Contract isa :=
  VG.Proof.MlDsa.AArch64.Round.hintK (fun s => Reduced s.mem (s.gpr .x0) ∧ Reduced s.mem (s.gpr .x1)) fun s s' =>
    let hint := Vector.zipWith (makeHint (VG.Proof.MlDsa.AArch64.Round.arg32 s .x2)) (polyAt s.mem (s.gpr .x0)) (polyAt s.mem (s.gpr .x1))
    HintIs s'.mem (s.gpr .x3) 1 [hint] ∧ ((s'.gpr .x0).setWidth 32).toNat = hintOnes [hint]

/-- `vg_mldsa_use_hint(h = x0, r = x1, gamma2 = w2, out = x3)`. -/
def useHintK : Contract isa :=
  VG.Proof.MlDsa.AArch64.Round.hintK (fun s => Reduced s.mem (s.gpr .x1)) fun s s' =>
    NatPolyIs s'.mem (s.gpr .x3) (Vector.zipWith (fun hj rj => (useHint (VG.Proof.MlDsa.AArch64.Round.arg32 s .x2) hj rj).toNat)
      ((hintAt s.mem (s.gpr .x0) 1).headD (Vector.replicate n false)) (polyAt s.mem (s.gpr .x1)))

/-! ## Zero-extending `γ₂` -/

/-- The state after `zext gr`'s first instruction, which zero-extends `gr`. -/
def zextS (gr : Reg) (s : State) : State := s.write .w gr (s.read .w gr + BitVec.ofNat 32 0)

theorem zextS_exec (gr : Reg) (s : State) : Exec isa (.block [.addImm .w gr gr 0]) s [] (VG.Proof.MlDsa.AArch64.Round.zextS gr s) :=
  .block rfl

theorem zextS_gpr (gr : Reg) (s : State) (r : Reg) :
    (VG.Proof.MlDsa.AArch64.Round.zextS gr s).gpr r = if r = gr then ((s.gpr gr).setWidth 32).setWidth 64 else s.gpr r := by
  simp [VG.Proof.MlDsa.AArch64.Round.zextS, State.write, State.read]

theorem zextS_other {gr : Reg} (s : State) {r : Reg} (h : r ≠ gr) : (VG.Proof.MlDsa.AArch64.Round.zextS gr s).gpr r = s.gpr r := by
  rw [VG.Proof.MlDsa.AArch64.Round.zextS_gpr, ite_eq_right h]

theorem zextS_self (gr : Reg) (s : State) : (VG.Proof.MlDsa.AArch64.Round.zextS gr s).gpr gr = ((s.gpr gr).setWidth 32).setWidth 64 := by
  rw [VG.Proof.MlDsa.AArch64.Round.zextS_gpr, ite_eq_left rfl]

theorem zextS_toNat (gr : Reg) (s : State) : ((VG.Proof.MlDsa.AArch64.Round.zextS gr s).gpr gr).toNat = VG.Proof.MlDsa.AArch64.Round.arg32 s gr := by
  rw [VG.Proof.MlDsa.AArch64.Round.zextS_self, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := ((s.gpr gr).setWidth 32).isLt; omega)]

/-- Running `zext gr main`: `main` from the state with `gr` zero-extended. -/
theorem zext_ok {gr : Reg} {main : Prog isa} {s : State} {Q : State → Prop} (h : WP isa main (VG.Proof.MlDsa.AArch64.Round.zextS gr s) Q) :
    WP isa (zext gr main) s Q := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨[] ++ t, s', .seq (VG.Proof.MlDsa.AArch64.Round.zextS_exec gr s) he, hq⟩

/-- The registers of the initial state that `zext gr` keeps. -/
theorem zextS_keep (gr : Reg) (s : State) : Keep [gr] s (VG.Proof.MlDsa.AArch64.Round.zextS gr s) :=
  ⟨fun r hr => VG.Proof.MlDsa.AArch64.Round.zextS_other s (by simpa using hr), rfl, rfl, rfl, fun _ _ => rfl⟩

theorem zextS_mem (gr : Reg) (s : State) : (VG.Proof.MlDsa.AArch64.Round.zextS gr s).mem = s.mem := rfl

/-- Constant time of `zext gr main` from the taint of `main`, from states
that agree on what is public once `gr` is zero-extended. -/
theorem zext_ct {gr : Reg} {main : Prog isa} {Pre : State → Prop} {Pub : State → State → Prop}
    {τ : VG.AArch64.Taint.T}
    (hτ : ∀ s₁ s₂, Pub s₁ s₂ → VG.AArch64.Taint.Agree τ (VG.Proof.MlDsa.AArch64.Round.zextS gr s₁) (VG.Proof.MlDsa.AArch64.Round.zextS gr s₂))
    {hc : VG.Taint.Hint taint.T} (h : (taint.check τ main hc).isSome = true) :
    ConstantTime isa Pre Pub (zext gr main) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ hp e₁ e₂
  obtain ⟨τ', hc'⟩ := Option.isSome_iff_exists.mp h
  unfold zext at e₁ e₂
  cases e₁ with
  | seq a₁ b₁ =>
    cases e₂ with
    | seq a₂ b₂ =>
      obtain ⟨rfl, rfl⟩ := Exec.det a₁ (VG.Proof.MlDsa.AArch64.Round.zextS_exec gr s₁)
      obtain ⟨rfl, rfl⟩ := Exec.det a₂ (VG.Proof.MlDsa.AArch64.Round.zextS_exec gr s₂)
      rw [(VG.Taint.check_sound (A := taint) hc' (hτ _ _ hp) b₁ b₂).1]

/-- The registers `rs` are public, and `gr` once zero-extended. -/
theorem agree_zext {gr : Reg} {rs : List Reg} {s₁ s₂ : State} (hsp : s₁.sp = s₂.sp)
    (hg : (s₁.gpr gr).setWidth 32 = (s₂.gpr gr).setWidth 32) (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs (gr :: rs)) (VG.Proof.MlDsa.AArch64.Round.zextS gr s₁) (VG.Proof.MlDsa.AArch64.Round.zextS gr s₂) := by
  refine ⟨hsp, fun r hr => ?_⟩
  rw [VG.Proof.MlDsa.AArch64.Round.zextS_gpr, VG.Proof.MlDsa.AArch64.Round.zextS_gpr]
  split
  · rw [hg]
  · simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons] at hr
    exact h r (hr.resolve_left ‹_›)

/-! ## The branch on `γ₂` -/

theorem g32_setWidth : (BitVec.ofNat 32 g32).setWidth 64 = BitVec.ofNat 64 261888 := by decide

/-- `onGamma gr t arm` runs `arm γ₂`, if `γ₂` is in `gr`. -/
theorem onGamma_ok {gr t : Reg} (ht : t ≠ gr) {arm : Nat → Prog isa} {s : State} {Q : State → Prop}
    (hg : (s.gpr gr).toNat = g32 ∨ (s.gpr gr).toNat = g88)
    (h : ∀ g, (s.gpr gr).toNat = g → ∀ s', Keep [t] s s' → s'.mem = s.mem → WP isa (arm g) s' Q) :
    WP isa (onGamma gr t arm) s Q := by
  unfold onGamma
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (movW_ok t _ s) fun s₁ ⟨⟨h1, hm₁⟩, k₁⟩ => ?_
  have hgr : s₁.gpr gr = s.gpr gr := k₁.get gr (by simpa using ht.symm)
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.WP.keep [t] (Q := fun s' => s'.gpr t = s₁.gpr gr - s₁.gpr t ∧ s'.mem = s₁.mem)
    (by arun) (by simp [writesOnly, Code.allInstrs, dstOf]) (hv := rfl)) fun s₂ ⟨⟨h2, hm₂⟩, k₂⟩ => ?_
  have k := k₁.trans k₂
  have hk : Keep [t] s s₂ := k.mono (by simp)
  have hm : s₂.mem = s.mem := by rw [hm₂, hm₁]
  have e : s₂.gpr t = s.gpr gr - BitVec.ofNat 64 261888 := by rw [h2, hgr, h1, VG.Proof.MlDsa.AArch64.Round.g32_setWidth]
  have hz : isa.eval (.zero .x t) s₂ = some (decide ((s.gpr gr).toNat = g32)) := by
    rw [VG.Proof.MlKem.AArch64.eval_zero, e, VG.Proof.MlKem.AArch64.eq_zero_iff]
    refine congrArg some (decide_eq_decide.mpr ?_)
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
    have := (s.gpr gr).isLt
    simp only [g32]
    omega
  refine WP.ite _ hz (fun hb => h _ (of_decide_eq_true hb) s₂ hk hm) fun hb => h _ ?_ s₂ hk hm
  have := of_decide_eq_false hb
  omega

/-! ## The loop over the coefficients -/

theorem coeffAddr_next (p : Addr) (j : Nat) : coeffAddr p j + BitVec.ofNat 64 4 = coeffAddr p (j + 1) := by
  rw [coeffAddr, coeffAddr, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]

/-- Stores of `v` at `a` for each `(a, v)`, in order. -/
def writes (m : Mem) (ps : List (Addr × BitVec 32)) : Mem := ps.foldl (fun m p => m.writeW p.1 p.2) m

theorem writes_cons (m : Mem) (p : Addr × BitVec 32) (ps : List (Addr × BitVec 32)) :
    VG.Proof.MlDsa.AArch64.Round.writes m (p :: ps) = VG.Proof.MlDsa.AArch64.Round.writes (m.writeW p.1 p.2) ps := rfl

theorem writes_nil (m : Mem) : VG.Proof.MlDsa.AArch64.Round.writes m [] = m := rfl

section
variable (P : Reg → Addr)

/-- Writes to coefficient `j` of polynomials disjoint from that at `p` leave it unchanged. -/
theorem coeffAt_writes_disjoint (m : Mem) (outs : List Reg) (j : Nat) (hj : j < 256) (V : Reg → BitVec 32)
    {p : Addr} (hd : ∀ o ∈ outs, (pR p).Disjoint (pR (P o))) {k : Nat} (hk : k < 256) :
    coeffAt (VG.Proof.MlDsa.AArch64.Round.writes m (outs.map fun o => (coeffAddr (P o) j, V o))) p k = coeffAt m p k := by
  induction outs generalizing m with
  | nil => rfl
  | cons o os ih =>
    rw [List.map_cons, VG.Proof.MlDsa.AArch64.Round.writes_cons]
    rw [ih _ fun o' h => hd o' (List.mem_cons_of_mem _ h),
      coeffAt_writeW_disjoint m (hd o List.mem_cons_self) (coeff_contains _ hj) hk]

theorem coeffAt_writes (m : Mem) (outs : List Reg) (j : Nat) (hj : j < 256) (V : Reg → BitVec 32)
    (hpw : outs.Pairwise fun a b => (pR (P a)).Disjoint (pR (P b))) {o : Reg} (ho : o ∈ outs) {k : Nat}
    (hk : k < 256) :
    coeffAt (VG.Proof.MlDsa.AArch64.Round.writes m (outs.map fun o => (coeffAddr (P o) j, V o))) (P o) k =
      if j = k then V o else coeffAt m (P o) k := by
  induction outs generalizing m with
  | nil => cases ho
  | cons o' os ih =>
    rw [List.map_cons, VG.Proof.MlDsa.AArch64.Round.writes_cons]
    rw [List.pairwise_cons] at hpw
    by_cases hr : o ∈ os
    · rw [ih _ hpw.2 hr]
      have hd : (pR (P o)).Disjoint (pR (P o')) := (hpw.1 o hr).symm
      rw [coeffAt_writeW_disjoint m hd (coeff_contains _ hj) hk]
    · obtain rfl : o = o' := by simpa [hr] using ho
      rw [VG.Proof.MlDsa.AArch64.Round.coeffAt_writes_disjoint P _ os j hj V (fun o' h => hpw.1 o' h) hk, coeffAt_writeW m _ hk hj]

theorem frame_writes {rs : List Region} {m₀ m : Mem} (hf : Frame rs m₀ m) (outs : List Reg) (j : Nat)
    (hj : j < 256) (V : Reg → BitVec 32) (hin : ∀ o ∈ outs, pR (P o) ∈ rs) :
    Frame rs m₀ (VG.Proof.MlDsa.AArch64.Round.writes m (outs.map fun o => (coeffAddr (P o) j, V o))) := by
  induction outs generalizing m with
  | nil => exact hf
  | cons o os ih =>
    rw [List.map_cons, VG.Proof.MlDsa.AArch64.Round.writes_cons]
    exact ih (hf.writeW (hin o List.mem_cons_self) _ (coeff_contains _ hj)) fun o' h =>
      hin o' (List.mem_cons_of_mem _ h)

end

/-- Where the loop's polynomials are: inputs readable, outputs writable,
the outputs pairwise disjoint and disjoint from the inputs. -/
structure Layout (s₀ : State) (ins outs : List Reg) : Prop where
  rd : ∀ p ∈ ins, pR (s₀.gpr p) ∈ s₀.rd ++ s₀.wr
  wr : ∀ o ∈ outs, pR (s₀.gpr o) ∈ s₀.wr
  dis : ∀ p ∈ ins, ∀ o ∈ outs, (pR (s₀.gpr p)).Disjoint (pR (s₀.gpr o))
  pw : outs.Pairwise fun a b => (pR (s₀.gpr a)).Disjoint (pR (s₀.gpr b))

/-- The layout, in a state with the same pointers and permissions. -/
theorem Layout.congr {s₀ s : State} {ins outs : List Reg} (h : VG.Proof.MlDsa.AArch64.Round.Layout s₀ ins outs)
    (e : ∀ r ∈ ins ++ outs, s.gpr r = s₀.gpr r) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    VG.Proof.MlDsa.AArch64.Round.Layout s ins outs where
  rd p hp := by rw [e p (List.mem_append_left _ hp), hrd, hwr]; exact h.rd p hp
  wr o ho := by rw [e o (List.mem_append_right _ ho), hwr]; exact h.wr o ho
  dis p hp o ho := by
    rw [e p (List.mem_append_left _ hp), e o (List.mem_append_right _ ho)]; exact h.dis p hp o ho
  pw := h.pw.imp_of_mem fun ha hb hd => by
    rw [e _ (List.mem_append_right _ ha), e _ (List.mem_append_right _ hb)]; exact hd

/-- After `i` iterations: the pointers `ptrs` at coefficient `i`, the
registers `fixed` unchanged, the outputs hold their values below
coefficient `i`, and `J i`. -/
structure Inv (s₀ : State) (ptrs fixed outs : List Reg) (V : Reg → Nat → BitVec 32) (J : Nat → State → Prop)
    (i : Nat) (s : State) : Prop where
  ptr : ∀ p ∈ ptrs, s.gpr p = coeffAddr (s₀.gpr p) i
  fixed : ∀ r ∈ fixed, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (outs.map fun o => pR (s₀.gpr o)) s₀.mem s.mem
  done : ∀ o ∈ outs, ∀ k < i, coeffAt s.mem (s₀.gpr o) k = V o k
  j : J i s

section
variable {s₀ : State} {ins outs ptrs fixed : List Reg} {V : Reg → Nat → BitVec 32} {J : Nat → State → Prop}
  {i : Nat} {s : State}

theorem Inv.inR (hL : VG.Proof.MlDsa.AArch64.Round.Layout s₀ ins outs) (hI : VG.Proof.MlDsa.AArch64.Round.Inv s₀ ptrs fixed outs V J i s) {p : Reg} (hp : p ∈ ins)
    (hpp : p ∈ ptrs) (hi : i < 256) : InRegions (s.rd ++ s.wr) (s.gpr p) 4 := by
  rw [hI.rd, hI.wr, hI.ptr p hpp]
  exact ⟨_, hL.rd p hp, coeff_contains _ hi⟩

theorem Inv.inW (hL : VG.Proof.MlDsa.AArch64.Round.Layout s₀ ins outs) (hI : VG.Proof.MlDsa.AArch64.Round.Inv s₀ ptrs fixed outs V J i s) {o : Reg} (ho : o ∈ outs)
    (hpo : o ∈ ptrs) (hi : i < 256) : InRegions s.wr (s.gpr o) 4 := by
  rw [hI.wr, hI.ptr o hpo]
  exact ⟨_, hL.wr o ho, coeff_contains _ hi⟩

/-- The inputs are those of the initial memory. -/
theorem Inv.read (hL : VG.Proof.MlDsa.AArch64.Round.Layout s₀ ins outs) (hI : VG.Proof.MlDsa.AArch64.Round.Inv s₀ ptrs fixed outs V J i s) {p : Reg} (hp : p ∈ ins)
    (hpp : p ∈ ptrs) (hi : i < 256) : s.mem.readW (s.gpr p) 32 = coeffAt s₀.mem (s₀.gpr p) i := by
  rw [hI.ptr p hpp, ← coeffAt_eq]
  exact coeffAt_frame hI.frame (fun _ hr => by
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hr
    exact hL.dis p hp o ho) hi

end

/-- The loop, from a body that writes `V o i` to coefficient `i` of each output. -/
theorem loop_ok {s₀ : State} {ins outs ptrs fixed clob : List Reg} {cnt : Reg} {body : List Instr}
    {V : Reg → Nat → BitVec 32} {J : Nat → State → Prop} (hL : VG.Proof.MlDsa.AArch64.Round.Layout s₀ ins outs)
    (hout : ∀ o ∈ outs, o ∈ ptrs) (hfix : ∀ r ∈ fixed, r ∉ clob) (hpc : ∀ p ∈ ptrs, p ≠ cnt)
    (hfc : cnt ∉ fixed)
    (hJ : ∀ s, s.mem = s₀.mem → Keep [cnt] s₀ s → J 0 s)
    (hbody : ∀ i < 256, ∀ s, VG.Proof.MlDsa.AArch64.Round.Inv s₀ ptrs fixed outs V J i s →
      WP isa (.block (body ++ ptrs.map (fun p => .addImm .x p p 4) ++ ([.subImm .x cnt cnt 1] : List Instr))) s fun s' =>
        (s'.mem = VG.Proof.MlDsa.AArch64.Round.writes s.mem (outs.map fun o => (s.gpr o, V o i)) ∧
          (∀ p ∈ ptrs, s'.gpr p = s.gpr p + BitVec.ofNat 64 4) ∧
          s'.gpr cnt = s.gpr cnt - BitVec.ofNat 64 1 ∧ J (i + 1) s') ∧
        Keep clob s s') :
    WP isa (mapLoop ptrs cnt body) s₀ (VG.Proof.MlDsa.AArch64.Round.Inv s₀ ptrs fixed outs V J 256) := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Arith.WP.keep [cnt] (Q := fun s => s.mem = s₀.mem ∧ s.gpr cnt = BitVec.ofNat 64 256)
    (by arun) (by simp [writesOnly, Code.allInstrs, dstOf]) (hv := rfl))
    fun s₁ ⟨⟨hm, hc⟩, hk⟩ => ?_)
  have h0 : VG.Proof.MlDsa.AArch64.Round.Inv s₀ ptrs fixed outs V J 0 s₁ := by
    refine ⟨fun p hp => ?_, fun r hr => hk.get r (by simp only [List.mem_singleton]; rintro rfl; exact hfc hr), hk.rd, hk.wr, ?_,
      fun _ _ k h => absurd h (Nat.not_lt_zero _), hJ s₁ hm hk⟩
    · rw [hk.get p (by simpa using hpc p hp), coeffAddr, Nat.mul_zero, BitVec.add_zero]
    · rw [hm]; exact Frame.refl _ _
  refine wp_countdown (cnt := cnt) (N := 256) (by decide) (by decide) (VG.Proof.MlDsa.AArch64.Round.Inv s₀ ptrs fixed outs V J)
    (fun i hi s hI _ => ?_) h0 hc
  refine WP.mono (hbody i hi s hI) fun s' ⟨⟨hm', hp', hc', hJ'⟩, hk'⟩ => ⟨?_, hc'⟩
  have hw : s'.mem = VG.Proof.MlDsa.AArch64.Round.writes s.mem (outs.map fun o => (coeffAddr (s₀.gpr o) i, V o i)) := by
    rw [hm']
    exact congrArg (VG.Proof.MlDsa.AArch64.Round.writes s.mem) (List.map_congr_left fun o ho => by rw [hI.ptr o (hout o ho)])
  refine ⟨fun p hp => by rw [hp' p hp, hI.ptr p hp, VG.Proof.MlDsa.AArch64.Round.coeffAddr_next],
    fun r hr => (hk'.get r (hfix r hr)).trans (hI.fixed r hr), hk'.rd.trans hI.rd, hk'.wr.trans hI.wr,
    ?_, fun o ho k hk => ?_, hJ'⟩
  · rw [hw]
    exact VG.Proof.MlDsa.AArch64.Round.frame_writes _ hI.frame outs _ hi _ fun o ho => List.mem_map_of_mem ho
  · rw [hw, VG.Proof.MlDsa.AArch64.Round.coeffAt_writes _ _ outs _ hi _ hL.pw ho (by omega)]
    split
    · subst k; rfl
    · exact hI.done o ho k (by omega)

end VG.Proof.MlDsa.AArch64.Round

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Round.Arith`. -/
section

/-!
# ML-DSA on AArch64: the values the rounding code computes

`Decompose` by a multiplication and shifts (`fX`, `r1X`), as 64-bit values,
and the conditional steps on the sign bit, as natural numbers, from the
target-independent lemmas of `Proof/MlDsa/Round/Decompose.lean`.
-/

namespace VG.Proof.MlDsa.AArch64.Round

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa (q gamma2s)

/-- `γ₂` is one of its two values. -/
abbrev IsG (g : Nat) : Prop := g = g32 ∨ g = g88

theorem isG_of_mem {g : Nat} (h : g ∈ gamma2s) : VG.Proof.MlDsa.AArch64.Round.IsG g := by
  rcases mem_gamma2s h with e | e
  · exact .inr e
  · exact .inl e

theorem mem_of_isG {g : Nat} (h : VG.Proof.MlDsa.AArch64.Round.IsG g) : g ∈ gamma2s := by
  rcases h with rfl | rfl <;> decide

theorem dShift_lt {g : Nat} : dShift g < 64 := by unfold dShift; split <;> decide

theorem dMod_lt {g : Nat} : dMod g < 4096 := by unfold dMod; split <;> decide

theorem dMod_eq {g : Nat} (h : VG.Proof.MlDsa.AArch64.Round.IsG g) : dMod g = hbM g := by rcases h with rfl | rfl <;> rfl

theorem hbM_pos {g : Nat} (h : VG.Proof.MlDsa.AArch64.Round.IsG g) : 0 < hbM g := by rcases h with rfl | rfl <;> decide

/-- `f`, as `hbRaw` computes it from `a`, with `M` and `2^(S-1)` in their registers. -/
def fX (g : Nat) (a : BitVec 64) : BitVec 64 :=
  (((a + BitVec.ofNat 64 127) >>> 7) * BitVec.ofNat 64 (hbMul g) + BitVec.ofNat 64 (hbAdd g)) >>> dShift g

/-- `r₁ = f mod m`, as `hb` computes it: `f` times the sign bit of `f - m`. -/
def r1X (g : Nat) (a : BitVec 64) : BitVec 64 := VG.Proof.MlDsa.AArch64.Round.fX g a * ((VG.Proof.MlDsa.AArch64.Round.fX g a - BitVec.ofNat 64 (dMod g)) >>> 63)

theorem fX_toNat {g : Nat} (hg : VG.Proof.MlDsa.AArch64.Round.IsG g) {a : BitVec 64} (ha : a.toNat < q) :
    (VG.Proof.MlDsa.AArch64.Round.fX g a).toNat = hbF g a.toNat := by
  have hq : q = 8380417 := rfl
  rw [hbF_eq (VG.Proof.MlDsa.AArch64.Round.mem_of_isG hg) ha]
  have hM : hbMul g < 65536 := by rcases hg with rfl | rfl <;> decide
  have hA : hbAdd g ≤ 2 ^ 23 := by rcases hg with rfl | rfl <;> decide
  have hS : dShift g = hbShift g := rfl
  have e1 : ((a + BitVec.ofNat 64 127) >>> 7).toNat = (a.toNat + 127) / 128 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    congr 1; omega
  have e2 : (((a + BitVec.ofNat 64 127) >>> 7) * BitVec.ofNat 64 (hbMul g)).toNat =
      (a.toNat + 127) / 128 * hbMul g := by
    rw [BitVec.toNat_mul, e1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := hbMul g) (by omega)]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_refl _) (Nat.le_of_lt hM))
      (by omega))
  have e3 : (((a + BitVec.ofNat 64 127) >>> 7) * BitVec.ofNat 64 (hbMul g) + BitVec.ofNat 64 (hbAdd g)).toNat =
      (a.toNat + 127) / 128 * hbMul g + hbAdd g := by
    have : (a.toNat + 127) / 128 * hbMul g < 2 ^ 40 :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_refl _) (Nat.le_of_lt hM)) (by omega)
    rw [BitVec.toNat_add, e2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := hbAdd g) (by omega)]
    omega
  rw [VG.Proof.MlDsa.AArch64.Round.fX, BitVec.toNat_ushiftRight, e3, Nat.shiftRight_eq_div_pow, hS]

theorem r1X_toNat {g : Nat} (hg : VG.Proof.MlDsa.AArch64.Round.IsG g) {a : BitVec 64} (ha : a.toNat < q) :
    (VG.Proof.MlDsa.AArch64.Round.r1X g a).toNat = hbF g a.toNat % hbM g := by
  have hf := VG.Proof.MlDsa.AArch64.Round.fX_toNat hg ha
  have hle := hbF_le (VG.Proof.MlDsa.AArch64.Round.mem_of_isG hg) ha
  have hm := VG.Proof.MlDsa.AArch64.Round.hbM_pos hg
  have hmv : (BitVec.ofNat 64 (dMod g)).toNat = hbM g := by
    rw [BitVec.toNat_ofNat, VG.Proof.MlDsa.AArch64.Round.dMod_eq hg]; exact Nat.mod_eq_of_lt (by rcases hg with rfl | rfl <;> decide)
  have hm44 : hbM g ≤ 44 := by rcases hg with rfl | rfl <;> decide
  generalize hF : hbF g a.toNat = F at hf hle
  have hs : ((VG.Proof.MlDsa.AArch64.Round.fX g a - BitVec.ofNat 64 (dMod g)) >>> 63).toNat = if F < hbM g then 1 else 0 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, hf, hmv]
    split <;> omega
  rw [VG.Proof.MlDsa.AArch64.Round.r1X, BitVec.toNat_mul, hs, hf]
  split
  · rw [Nat.mul_one, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mul_zero, show F = hbM g by omega, Nat.mod_self]

theorem r1X_lt {g : Nat} (hg : VG.Proof.MlDsa.AArch64.Round.IsG g) {a : BitVec 64} (ha : a.toNat < q) : (VG.Proof.MlDsa.AArch64.Round.r1X g a).toNat < hbM g := by
  rw [VG.Proof.MlDsa.AArch64.Round.r1X_toNat hg ha]; exact Nat.mod_lt _ (VG.Proof.MlDsa.AArch64.Round.hbM_pos hg)

end VG.Proof.MlDsa.AArch64.Round

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Round.NormLt`. -/
section

/-!
# ML-DSA on AArch64: `vg_mldsa_norm_lt`

The top bit of `x10` says whether every coefficient `a` so far has `a < B` or
`q - a < B` (`J`): each is the sign bit of a difference of numbers less than
`2³²` (`sgn_sub`).
-/

namespace VG.Proof.MlDsa.AArch64.Round

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Round VG.Proof.MlDsa.Round
open VG.Proof.MlDsa.AArch64.Arith (Qv toNat_setWidth64 q32 movW_ok)
open VG.Impl.MlDsa.AArch64.Arith (movW)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa

/-- A bit, as a 64-bit value. -/
abbrev bitV (b : Bool) : BitVec 64 := BitVec.ofNat 64 b.toNat

/-- The sign bit of the difference of two numbers less than `2⁶³`. -/
theorem sgn_sub {x y : BitVec 64} (hx : x.toNat < 2 ^ 63) (hy : y.toNat < 2 ^ 63) :
    (x - y) >>> 63 = VG.Proof.MlDsa.AArch64.Round.bitV (decide (x.toNat < y.toNat)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, BitVec.toNat_ofNat]
  generalize x.toNat = a at *
  generalize y.toNat = b at *
  by_cases h : a < b
  · rw [decide_eq_true h]
    have e : (2 ^ 64 - b + a) % 2 ^ 64 = 2 ^ 64 - b + a := Nat.mod_eq_of_lt (by omega)
    rw [e]; simp only [Bool.toNat_true]; omega
  · rw [decide_eq_false h]
    have e : (2 ^ 64 - b + a) % 2 ^ 64 = a - b := by omega
    rw [e]; simp only [Bool.toNat_false]; omega

theorem bitV_and (b c : Bool) : VG.Proof.MlDsa.AArch64.Round.bitV b &&& VG.Proof.MlDsa.AArch64.Round.bitV c = VG.Proof.MlDsa.AArch64.Round.bitV (b && c) := by cases b <;> cases c <;> decide

theorem bitV_or (b c : Bool) : VG.Proof.MlDsa.AArch64.Round.bitV b ||| bitV c = VG.Proof.MlDsa.AArch64.Round.bitV (b || c) := by cases b <;> cases c <;> decide

theorem bitV_shr (b : Bool) : VG.Proof.MlDsa.AArch64.Round.bitV b >>> 63 = 0 := by cases b <;> decide

theorem nlBody_ok (s : State) (hq : s.gpr .x9 = Qv) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x0) 4) :
    WP isa (.block (nlBody ++ [Reg.x0].map (fun p => .addImm .x p p 4) ++ ([.subImm .x .x11 .x11 1] : List Instr))) s
      fun s' =>
      (s'.mem = s.mem ∧ s'.gpr .x10 = s.gpr .x10 &&& ((s.mem.readW (s.gpr .x0) 32).setWidth 64 - s.gpr .x1 |||
          Qv - (s.mem.readW (s.gpr .x0) 32).setWidth 64 - s.gpr .x1) ∧
        s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 4 ∧ s'.gpr .x11 = s.gpr .x11 - BitVec.ofNat 64 1) ∧
      Keep [.x0, .x10, .x11, .x12, .x13, .x14] s s' := by
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl)
  unfold nlBody
  arun [h0, hq, List.map_cons, List.map_nil]

/-- Whether coefficient `k` of `f` is within the bound. -/
def okN (m : Mem) (f : Addr) (B k : Nat) : Bool := decide ((coeffAt m f k).toNat < B ∨ q - (coeffAt m f k).toNat < B)

/-- Whether coefficients `0` to `i - 1` are. -/
def allOk (m : Mem) (f : Addr) (B i : Nat) : Bool := decide (∀ k < i, VG.Proof.MlDsa.AArch64.Round.okN m f B k = true)

theorem allOk_zero (m : Mem) (f : Addr) (B : Nat) : VG.Proof.MlDsa.AArch64.Round.allOk m f B 0 = true :=
  decide_eq_true fun _ hk => absurd hk (Nat.not_lt_zero _)

theorem allOk_succ (m : Mem) (f : Addr) (B i : Nat) :
    VG.Proof.MlDsa.AArch64.Round.allOk m f B (i + 1) = (VG.Proof.MlDsa.AArch64.Round.allOk m f B i && VG.Proof.MlDsa.AArch64.Round.okN m f B i) := by
  unfold VG.Proof.MlDsa.AArch64.Round.allOk
  by_cases h : VG.Proof.MlDsa.AArch64.Round.okN m f B i = true
  · rw [h, Bool.and_true]
    exact decide_eq_decide.mpr ⟨fun h' k hk => h' k (by omega), fun h' k hk => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      exacts [h' k hk, h]⟩
  · rw [Bool.not_eq_true] at h
    rw [h, Bool.and_false]
    exact decide_eq_false fun h' => by rw [h' i (Nat.lt_succ_self _)] at h; cases h

theorem ok_bit {a B : BitVec 64} (ha : a.toNat < q) (hB : B.toNat < 2 ^ 32) :
    (a - B ||| Qv - a - B) >>> 63 = VG.Proof.MlDsa.AArch64.Round.bitV (decide (a.toNat < B.toNat ∨ q - a.toNat < B.toNat)) := by
  have hq : q = 8380417 := rfl
  have hQ : Qv.toNat = 8380417 := rfl
  have e : (Qv - a).toNat = q - a.toNat := by
    rw [VG.Proof.MlKem.AArch64.toNat_sub_n (by rw [hQ]; omega), hQ]
  rw [BitVec.ushiftRight_or_distrib, VG.Proof.MlDsa.AArch64.Round.sgn_sub (by omega) (by omega),
    VG.Proof.MlDsa.AArch64.Round.sgn_sub (by rw [e]; omega) (by omega), e, VG.Proof.MlDsa.AArch64.Round.bitV_or]
  rw [Bool.decide_or]

theorem normLt_correct (s₀ : State) (hp : normLtK.pre s₀) :
    ∃ t s', Exec isa normLt s₀ t s' ∧ abiPreserved s₀ s' ∧ normLtK.post s₀ s' := by
  have hr : Reduced s₀.mem (s₀.gpr .x0) := hp.2.2
  let B := VG.Proof.MlDsa.AArch64.Round.arg32 s₀ .x1
  let J : Nat → State → Prop := fun i s => s.gpr .x10 >>> 63 = VG.Proof.MlDsa.AArch64.Round.bitV (VG.Proof.MlDsa.AArch64.Round.allOk s₀.mem (s₀.gpr .x0) B i)
  have hpro : WP isa (.block ([.addImm .w .x1 .x1 0] ++ movW .x9 (BitVec.ofNat 32 Impl.MlDsa.AArch64.Arith.qNat) ++
      ([.movz .x .x10 0 0, .subImm .x .x10 .x10 1] : List Instr))) s₀ fun s =>
      s.gpr .x1 = ((s₀.gpr .x1).setWidth 32).setWidth 64 ∧ s.gpr .x9 = Qv ∧ s.gpr .x10 = BitVec.allOnes 64 ∧
        s.mem = s₀.mem ∧ Keep [.x1, .x9, .x10] s₀ s := by
    rw [WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.WP.keep [.x1] (Q := fun s => s.gpr .x1 =
      ((s₀.gpr .x1).setWidth 32).setWidth 64 ∧ s.mem = s₀.mem) (by arun) (by rfl)) fun s₁ ⟨⟨h1, hm₁⟩, k₁⟩ => ?_
    refine WP.mono (movW_ok .x9 _ s₁) fun s₂ ⟨⟨h9, hm₂⟩, k₂⟩ => ?_
    refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.WP.keep [.x10] (Q := fun s => s.gpr .x10 = BitVec.allOnes 64 ∧
      s.mem = s₂.mem) (by arun) (by rfl)) fun s₃ ⟨⟨h10, hm₃⟩, k₃⟩ => ?_
    refine ⟨by rw [k₃.get .x1, k₂.get .x1, h1], by rw [k₃.get .x9, h9]; exact q32, h10,
      by rw [hm₃, hm₂, hm₁], ((k₁.trans k₂).trans k₃).mono⟩
  have hB : (((s₀.gpr .x1).setWidth 32).setWidth 64 : BitVec 64).toNat = B := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := ((s₀.gpr .x1).setWidth 32).isLt; omega)]
  have hB32 : B < 2 ^ 32 := ((s₀.gpr .x1).setWidth 32).isLt
  have hW : WP isa normLt s₀ fun s' =>
      (s'.gpr .x0).setWidth 32 = if normRq [polyAt s₀.mem (s₀.gpr .x0)] < B then 1 else 0 := by
    refine WP.seq (WP.mono hpro fun sL ⟨h1, h9, h10, hmL, kL⟩ => ?_)
    have hL : VG.Proof.MlDsa.AArch64.Round.Layout sL [.x0] [] :=
      { rd := fun p hp' => by
          simp only [List.mem_singleton] at hp'; subst hp'; rw [kL.get .x0, kL.rd, kL.wr, hp.1]; simp
        wr := fun _ h => by cases h
        dis := fun _ _ _ h => by cases h
        pw := List.Pairwise.nil }
    refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Round.loop_ok (fixed := [.x1, .x9]) (clob := [.x0, .x10, .x11, .x12, .x13, .x14])
      (V := fun _ _ => 0) (J := J) hL (by decide) (by decide) (by decide) (by decide)
      (fun s hm hk => ?_) fun i hi s hI => ?_) fun s2 hI => ?_)
    · show s.gpr .x10 >>> 63 = _
      rw [hk.get .x10, h10, VG.Proof.MlDsa.AArch64.Round.allOk_zero]
      decide
    · have hx9 : s.gpr .x9 = Qv := by rw [hI.fixed .x9 (by simp), h9]
      refine WP.mono (VG.Proof.MlDsa.AArch64.Round.nlBody_ok s hx9 (hI.inR hL (by simp) (by simp) hi)) fun s' ⟨⟨hm', h10', h0, hc⟩, hk'⟩ =>
        ⟨⟨by rw [hm']; rfl, fun p hp' => by simp only [List.mem_singleton] at hp'; subst hp'; exact h0, hc, ?_⟩,
          hk'⟩
      show s'.gpr .x10 >>> 63 = _
      have ha : ((s.mem.readW (s.gpr .x0) 32).setWidth 64).toNat = (coeffAt s₀.mem (s₀.gpr .x0) i).toNat := by
        rw [toNat_setWidth64, hI.read hL (by simp) (by simp) hi, hmL, kL.get .x0]
      have hx1 : (s.gpr .x1).toNat = B := by rw [hI.fixed .x1 (by simp), h1, hB]
      rw [h10', BitVec.ushiftRight_and_distrib, hI.j, VG.Proof.MlDsa.AArch64.Round.ok_bit (by rw [ha]; exact hr i hi) (by rw [hx1]; exact hB32),
        ha, hx1, VG.Proof.MlDsa.AArch64.Round.bitV_and, VG.Proof.MlDsa.AArch64.Round.allOk_succ]
      rfl
    · refine (VG.Proof.MlDsa.AArch64.Arith.WP.keep (Q := fun s3 => s3.gpr .x0 = s2.gpr .x10 >>> 63) [.x0]
        (by arun) (by rfl)).mono fun s3 ⟨h0, _⟩ => ?_
      rw [h0, hI.j]
      have e : VG.Proof.MlDsa.AArch64.Round.allOk s₀.mem (s₀.gpr .x0) B 256 = decide (normRq [polyAt s₀.mem (s₀.gpr .x0)] < B) := by
        unfold VG.Proof.MlDsa.AArch64.Round.allOk
        refine decide_eq_decide.mpr ?_
        rw [normRq_lt]
        refine ⟨fun h k hk => ?_, fun h k hk => ?_⟩
        · have := h k hk
          simp only [VG.Proof.MlDsa.AArch64.Round.okN, decide_eq_true_eq] at this
          rw [normZq_lt, polyAt_val hr hk]; exact this
        · have := h k hk
          rw [normZq_lt, polyAt_val hr hk] at this
          simp only [VG.Proof.MlDsa.AArch64.Round.okN, decide_eq_true_eq]; exact this
      rw [e]
      split <;> rename_i h <;> simp [h]
  obtain ⟨t, s', he, hpost⟩ := hW
  exact ⟨t, s', he, VG.Proof.MlKem.AArch64.abi_of rfl (by decide +kernel) he, hpost⟩

theorem normLt_ct : ConstantTime isa normLtK.pre normLtK.pub normLt :=
  VG.Taint.constantTime (A := taint) (VG.AArch64.Taint.ofRegs [.x0])
    (fun _ _ _ _ hp => VG.Proof.MlDsa.AArch64.Arith.agree_regs hp.2.2 fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.1)
    (by taint_decide)

/-- A state satisfying the precondition. -/
def normLtSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := []

theorem normLt_verified : Verified AArch64.target normLt (normLtContract AArch64.abi) :=
  Verified.of_correct VG.Proof.MlDsa.AArch64.Round.normLt_correct VG.Proof.MlDsa.AArch64.Round.normLt_ct (by
    mldsa_implies [normLtContract, normLtSig, VG.Proof.MlDsa.AArch64.Round.normLtK, AArch64.abi, AArch64.argRegs] [normLtSat]
      using VG.Proof.MlDsa.AArch64.Round.normLtSat)

end VG.Proof.MlDsa.AArch64.Round

end
