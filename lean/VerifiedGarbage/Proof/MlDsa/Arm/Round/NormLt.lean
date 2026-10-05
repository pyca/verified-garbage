import VerifiedGarbage.Impl.MlDsa.Arm.Round.Round
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.Round.Ones
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.Round.Decompose
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Round.Loop`. -/
section

/-!
# ML-DSA on 32-bit ARM: the loop over the coefficients

`mapLoop cnt body` runs `body` 256 times, `cnt` counting down, and iteration
`i` handles coefficient `i` of each polynomial, whose pointer (a register of
`ptrs`) the body advances by 4 bytes. `loop_ok` proves it once for every
function: from a body that writes, to coefficient `i` of each output
polynomial (in a register of `outs`), the value `V o i` and keeps an invariant
`J` of its other registers, the loop writes every coefficient of each output.
The inputs (registers `ins`) are never written, so the body reads the
coefficients of the initial memory (`Inv.read`).
-/

namespace VG.Proof.MlDsa.Arm.Round

open VG VG.Arm VG.Impl.MlDsa.Arm.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa (coeffAt)
open VG.Proof.MlKem.Arm (wp_loop_ne count_z count_sub addr_ptr)

/-- The address of the polynomial whose pointer is `r` in `s`. -/
abbrev P (s : State) (r : Reg) : Addr := State.addr (s.gpr r)

/-- A reduced word is the element of `ℤ_q` it represents. -/
theorem word_of_reduced {v : BitVec 32} (h : v.toNat < VG.Spec.MlDsa.q) :
    BitVec.ofNat 32 (Fin.ofNat VG.Spec.MlDsa.q v.toNat).val = v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Fin.val_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt v.isLt]

/-! ## The writes of an iteration -/

/-- Stores of `v` at `a` for each `(a, v)`, in order. -/
def writes (m : Mem) (ps : List (Addr × BitVec 32)) : Mem := ps.foldl (fun m p => m.writeW p.1 p.2) m

theorem writes_cons (m : Mem) (p : Addr × BitVec 32) (ps : List (Addr × BitVec 32)) :
    VG.Proof.MlDsa.Arm.Round.writes m (p :: ps) = VG.Proof.MlDsa.Arm.Round.writes (m.writeW p.1 p.2) ps := rfl

theorem writes_nil (m : Mem) : VG.Proof.MlDsa.Arm.Round.writes m [] = m := rfl

section
variable (Pa : Reg → Addr)

theorem coeffAt_writes_disjoint (m : Mem) (outs : List Reg) (j : Nat) (hj : j < 256) (V : Reg → BitVec 32)
    {p : Addr} (hd : ∀ o ∈ outs, (pR p).Disjoint (pR (Pa o))) {k : Nat} (hk : k < 256) :
    coeffAt (VG.Proof.MlDsa.Arm.Round.writes m (outs.map fun o => (coeffAddr (Pa o) j, V o))) p k = coeffAt m p k := by
  induction outs generalizing m with
  | nil => rfl
  | cons o os ih =>
    rw [List.map_cons, VG.Proof.MlDsa.Arm.Round.writes_cons]
    rw [ih _ fun o' h => hd o' (List.mem_cons_of_mem _ h),
      coeffAt_writeW_disjoint m (hd o List.mem_cons_self) (coeff_contains _ hj) hk]

theorem coeffAt_writes (m : Mem) (outs : List Reg) (j : Nat) (hj : j < 256) (V : Reg → BitVec 32)
    (hpw : outs.Pairwise fun a b => (pR (Pa a)).Disjoint (pR (Pa b))) {o : Reg} (ho : o ∈ outs) {k : Nat}
    (hk : k < 256) :
    coeffAt (VG.Proof.MlDsa.Arm.Round.writes m (outs.map fun o => (coeffAddr (Pa o) j, V o))) (Pa o) k =
      if j = k then V o else coeffAt m (Pa o) k := by
  induction outs generalizing m with
  | nil => cases ho
  | cons o' os ih =>
    rw [List.map_cons, VG.Proof.MlDsa.Arm.Round.writes_cons]
    rw [List.pairwise_cons] at hpw
    by_cases hr : o ∈ os
    · rw [ih _ hpw.2 hr]
      have hd : (pR (Pa o)).Disjoint (pR (Pa o')) := (hpw.1 o hr).symm
      rw [coeffAt_writeW_disjoint m hd (coeff_contains _ hj) hk]
    · obtain rfl : o = o' := by simpa [hr] using ho
      rw [VG.Proof.MlDsa.Arm.Round.coeffAt_writes_disjoint Pa _ os j hj V (fun o' h => hpw.1 o' h) hk, coeffAt_writeW m _ hk hj]

theorem frame_writes {rs : List Region} {m₀ m : Mem} (hf : Frame rs m₀ m) (outs : List Reg) (j : Nat)
    (hj : j < 256) (V : Reg → BitVec 32) (hin : ∀ o ∈ outs, pR (Pa o) ∈ rs) :
    Frame rs m₀ (VG.Proof.MlDsa.Arm.Round.writes m (outs.map fun o => (coeffAddr (Pa o) j, V o))) := by
  induction outs generalizing m with
  | nil => exact hf
  | cons o os ih =>
    rw [List.map_cons, VG.Proof.MlDsa.Arm.Round.writes_cons]
    exact ih (hf.writeW (hin o List.mem_cons_self) _ (coeff_contains _ hj)) fun o' h =>
      hin o' (List.mem_cons_of_mem _ h)

end

/-! ## The loop -/

/-- Where the loop's polynomials are: inputs readable, outputs writable,
the outputs pairwise disjoint and disjoint from the inputs, none wrapping
around. -/
structure Layout (s₀ : State) (ins outs : List Reg) : Prop where
  rd : ∀ p ∈ ins, pR (VG.Proof.MlDsa.Arm.Round.P s₀ p) ∈ s₀.rd ++ s₀.wr
  wr : ∀ o ∈ outs, pR (VG.Proof.MlDsa.Arm.Round.P s₀ o) ∈ s₀.wr
  dis : ∀ p ∈ ins, ∀ o ∈ outs, (pR (VG.Proof.MlDsa.Arm.Round.P s₀ p)).Disjoint (pR (VG.Proof.MlDsa.Arm.Round.P s₀ o))
  pw : outs.Pairwise fun a b => (pR (VG.Proof.MlDsa.Arm.Round.P s₀ a)).Disjoint (pR (VG.Proof.MlDsa.Arm.Round.P s₀ b))
  fit : ∀ p ∈ ins ++ outs, (s₀.gpr p).toNat + 1024 ≤ 2 ^ 32

/-- After `i` iterations: the pointers `ptrs` at coefficient `i`, `cnt` at
`256 - i`, the registers `fixed` unchanged, the outputs holding their values
below coefficient `i`, and `J i`. -/
structure Inv (s₀ : State) (ptrs fixed outs : List Reg) (cnt : Reg) (V : Reg → Nat → BitVec 32)
    (J : Nat → State → Prop) (i : Nat) (s : State) : Prop where
  ptr : ∀ p ∈ ptrs, s.gpr p = s₀.gpr p + BitVec.ofNat 32 (4 * i)
  cnt : s.gpr cnt = BitVec.ofNat 32 (1 * (256 - i))
  fixed : ∀ r ∈ fixed, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame (outs.map fun o => pR (VG.Proof.MlDsa.Arm.Round.P s₀ o)) s₀.mem s.mem
  done : ∀ o ∈ outs, ∀ k < i, coeffAt s.mem (VG.Proof.MlDsa.Arm.Round.P s₀ o) k = V o k
  j : J i s

section
variable {s₀ : State} {ins outs ptrs fixed : List Reg} {cnt : Reg} {V : Reg → Nat → BitVec 32}
  {J : Nat → State → Prop} {i : Nat} {s : State}

/-- The address a pointer `p` of the loop points at in iteration `i`. -/
theorem Inv.addr (hL : VG.Proof.MlDsa.Arm.Round.Layout s₀ ins outs) (hI : VG.Proof.MlDsa.Arm.Round.Inv s₀ ptrs fixed outs cnt V J i s) (hi : i < 256) {p : Reg}
    (hp : p ∈ ptrs) (hio : p ∈ ins ++ outs) :
    State.addr (s.gpr p + BitVec.ofNat 32 0) = coeffAddr (VG.Proof.MlDsa.Arm.Round.P s₀ p) i := by
  have := hL.fit p hio
  rw [hI.ptr p hp, addr_ptr _ _ _ (by omega), Nat.add_zero]

theorem Inv.inR (hL : VG.Proof.MlDsa.Arm.Round.Layout s₀ ins outs) (hI : VG.Proof.MlDsa.Arm.Round.Inv s₀ ptrs fixed outs cnt V J i s) (hi : i < 256) {p : Reg}
    (hp : p ∈ ptrs) (hin : p ∈ ins) : InRegions (s.rd ++ s.wr) (State.addr (s.gpr p + BitVec.ofNat 32 0)) 4 := by
  rw [hI.addr hL hi hp (List.mem_append_left _ hin), hI.rd, hI.wr]
  exact ⟨_, hL.rd p hin, coeff_contains _ (by rw [n_eq]; exact hi)⟩

theorem Inv.inW (hL : VG.Proof.MlDsa.Arm.Round.Layout s₀ ins outs) (hI : VG.Proof.MlDsa.Arm.Round.Inv s₀ ptrs fixed outs cnt V J i s) (hi : i < 256) {o : Reg}
    (hp : o ∈ ptrs) (ho : o ∈ outs) : InRegions s.wr (State.addr (s.gpr o + BitVec.ofNat 32 0)) 4 := by
  rw [hI.addr hL hi hp (List.mem_append_right _ ho), hI.wr]
  exact ⟨_, hL.wr o ho, coeff_contains _ (by rw [n_eq]; exact hi)⟩

/-- The inputs are those of the initial memory. -/
theorem Inv.read (hL : VG.Proof.MlDsa.Arm.Round.Layout s₀ ins outs) (hI : VG.Proof.MlDsa.Arm.Round.Inv s₀ ptrs fixed outs cnt V J i s) (hi : i < 256) {p : Reg}
    (hp : p ∈ ptrs) (hin : p ∈ ins) :
    s.mem.readW (State.addr (s.gpr p + BitVec.ofNat 32 0)) 32 = coeffAt s₀.mem (VG.Proof.MlDsa.Arm.Round.P s₀ p) i := by
  rw [hI.addr hL hi hp (List.mem_append_left _ hin), ← coeffAt_eq]
  exact coeffAt_frame hI.frame (fun _ hr => by
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hr
    exact hL.dis p hin o ho) (by rw [n_eq]; exact hi)

end

/-- What an iteration does: it writes `V o i` to coefficient `i` of each
output, advances the pointers, counts down, keeps the registers `fixed`,
and establishes `J (i + 1)`. -/
def Step (s₀ : State) (ptrs fixed outs : List Reg) (cnt : Reg) (V : Reg → Nat → BitVec 32)
    (J : Nat → State → Prop) (i : Nat) (s s' : State) : Prop :=
  s'.mem = VG.Proof.MlDsa.Arm.Round.writes s.mem (outs.map fun o => (coeffAddr (VG.Proof.MlDsa.Arm.Round.P s₀ o) i, V o i)) ∧
    (∀ p ∈ ptrs, s'.gpr p = s.gpr p + 4) ∧ s'.gpr cnt = s.gpr cnt - 1 ∧ s'.z = (s.gpr cnt - 1 == 0) ∧
    (∀ r ∈ fixed, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ J (i + 1) s'

/-- The loop, from a body that writes `V o i` to coefficient `i` of each output. -/
theorem loop_ok {s₀ : State} {ins outs ptrs fixed : List Reg} {cnt : Reg} {body : List Instr}
    {V : Reg → Nat → BitVec 32} {J : Nat → State → Prop} (hL : VG.Proof.MlDsa.Arm.Round.Layout s₀ ins outs)
    (hcf : cnt ∉ fixed) (hcp : cnt ∉ ptrs)
    (hJ : ∀ s, s.gpr = (fun r => if r = cnt then BitVec.ofNat 32 256 else s₀.gpr r) → s.mem = s₀.mem →
      J 0 s)
    (hbody : ∀ i < 256, ∀ s, VG.Proof.MlDsa.Arm.Round.Inv s₀ ptrs fixed outs cnt V J i s →
      WP isa (.block body) s (VG.Proof.MlDsa.Arm.Round.Step s₀ ptrs fixed outs cnt V J i s)) :
    WP isa (mapLoop cnt body) s₀ (VG.Proof.MlDsa.Arm.Round.Inv s₀ ptrs fixed outs cnt V J 256) := by
  refine WP.seq (WP.of_runBlock ⟨_, runBlock_cons.trans (by rfl), ?_⟩)
  refine wp_loop_ne (VG.Proof.MlDsa.Arm.Round.Inv s₀ ptrs fixed outs cnt V J) (N := 256) (by decide)
    (fun i hi s hI => WP.mono (hbody i hi s hI) fun s' ⟨hm, hp, hc, hz, hf, rd, wr, sp, hJ'⟩ => ?_)
    (fun _ h => h) ?_
  · refine ⟨⟨fun p hp' => ?_, ?_, fun r hr => (hf r hr).trans (hI.fixed r hr), rd.trans hI.rd, wr.trans hI.wr,
      sp.trans hI.sp, ?_, fun o ho k hk => ?_, hJ'⟩, ?_⟩
    · rw [hp p hp', hI.ptr p hp', BitVec.add_assoc, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
        ← BitVec.ofNat_add, Nat.mul_succ]
    · rw [hc, hI.cnt]; exact count_sub (k := 1) hi
    · rw [hm]
      exact VG.Proof.MlDsa.Arm.Round.frame_writes _ hI.frame outs _ hi _ fun o ho => List.mem_map_of_mem ho
    · rw [hm, VG.Proof.MlDsa.Arm.Round.coeffAt_writes _ _ outs _ hi _ hL.pw ho (by omega)]
      split
      · subst k; rfl
      · exact hI.done o ho k (by omega)
    · rw [hz, hI.cnt]; exact count_z (k := 1) hi (by decide) (by decide)
  · refine ⟨fun p hp => ?_, by simp [State.setReg], fun r hr => ?_, rfl, rfl, rfl, Frame.refl _ _,
      fun _ _ k hk => absurd hk (Nat.not_lt_zero k), hJ _ ?_ rfl⟩
    · have : p ≠ cnt := fun e => hcp (e ▸ hp)
      simp [State.setReg, this]
    · have : r ≠ cnt := fun e => hcf (e ▸ hr)
      simp [State.setReg, this]
    · funext r; rfl

end VG.Proof.MlDsa.Arm.Round

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Round.NormLt`. -/
section

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_norm_lt`

The loop body is symbolically executed once for any state (`body_ok`): a
coefficient `a` is bad when `bound ≤ a` and `bound ≤ q - a` (the carries of
the two comparisons), and `r4` becomes 1 at the first bad one (`acc`); the
result `1 - r4` is 1 exactly when no coefficient is bad, that is when the norm
is less than `bound` (`normRq_lt`, `normZq_lt`).
-/

namespace VG.Proof.MlDsa.Arm.Round.NormLt

open VG VG.Arm VG.Impl.MlDsa.Arm.Round VG.Proof.MlDsa.Round VG.Proof.MlDsa.Arm.Round
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced normRq normZq)
open VG.Proof.MlDsa.Arm.Arith (Entry wp_saving ct_of_saving preserved_of_saving Qw loadQ_val)

/-! ## The body -/

/-- 1 if the coefficient `a` is bad for the bound `b`, 0 otherwise. -/
def bad (a b : BitVec 32) : BitVec 32 :=
  (if b.toNat ≤ a.toNat then 1 else 0) &&& (if b.toNat ≤ (Qw - a).toNat then 1 else 0)

section
variable {s : State} {x b c v : BitVec 32} (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = b) (h2 : s.gpr .r2 = c)
  (h4 : s.gpr .r4 = v) (iF : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4)
include h0 h1 h2 h4 iF

theorem body_ok :
    WP isa (.block nlBody) s fun s' =>
      s'.gpr .r4 = v ||| bad (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32) b ∧ s'.gpr .r0 = x + 4 ∧
      s'.gpr .r2 = c - 1 ∧ s'.z = (c - 1 == 0) ∧ s'.mem = s.mem ∧
      (∀ r ∈ [Reg.r1, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr], s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [nlBody, VG.Proof.MlDsa.Arm.Round.NormLt.bad, loadQ_val, h0, h1, h2, h4, iF, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
    implies_true, and_self, and_true]
  have z : ∀ y : BitVec 32, (0 : BitVec 32) + 0 + y = y := fun y => by bv_omega
  simp only [decide_eq_true_eq, z]

end

/-- Whether coefficient `a` has `‖a‖∞ < b`. -/
abbrev Ok (a b : BitVec 32) : Prop := a.toNat < b.toNat ∨ q - a.toNat < b.toNat

theorem bad_eq {a : BitVec 32} (ha : a.toNat < q) (b : BitVec 32) :
    VG.Proof.MlDsa.Arm.Round.NormLt.bad a b = if VG.Proof.MlDsa.Arm.Round.NormLt.Ok a b then 0 else 1 := by
  have e : (Qw - a).toNat = q - a.toNat := by rw [q_eq] at *; bv_omega
  unfold VG.Proof.MlDsa.Arm.Round.NormLt.bad VG.Proof.MlDsa.Arm.Round.NormLt.Ok
  rw [e]
  by_cases h1 : b.toNat ≤ a.toNat <;> by_cases h2 : b.toNat ≤ q - a.toNat <;>
    simp only [h1, h2, ite_true, ite_false] <;>
    first
    | (rw [ite_eq_right (by omega)]; decide)
    | (rw [ite_eq_left (by omega)]; decide)

/-- The accumulator after the first `i` coefficients of `m` at `F`. -/
def acc (m : Mem) (F : Addr) (b : BitVec 32) (i : Nat) : BitVec 32 :=
  if ∀ k < i, VG.Proof.MlDsa.Arm.Round.NormLt.Ok (coeffAt m F k) b then 0 else 1

theorem acc_succ (m : Mem) (F : Addr) (b : BitVec 32) (i : Nat) :
    VG.Proof.MlDsa.Arm.Round.NormLt.acc m F b i ||| (if VG.Proof.MlDsa.Arm.Round.NormLt.Ok (coeffAt m F i) b then 0 else 1) = VG.Proof.MlDsa.Arm.Round.NormLt.acc m F b (i + 1) := by
  have H : (∀ k < i + 1, VG.Proof.MlDsa.Arm.Round.NormLt.Ok (coeffAt m F k) b) ↔ (∀ k < i, VG.Proof.MlDsa.Arm.Round.NormLt.Ok (coeffAt m F k) b) ∧ VG.Proof.MlDsa.Arm.Round.NormLt.Ok (coeffAt m F i) b :=
    ⟨fun h => ⟨fun k hk => h k (by omega), h i (by omega)⟩, fun ⟨h, h'⟩ k hk => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      exacts [h k hk, h']⟩
  unfold VG.Proof.MlDsa.Arm.Round.NormLt.acc
  by_cases h : ∀ k < i, VG.Proof.MlDsa.Arm.Round.NormLt.Ok (coeffAt m F k) b <;> by_cases h' : VG.Proof.MlDsa.Arm.Round.NormLt.Ok (coeffAt m F i) b <;>
    simp only [H, h', and_true, and_false, ite_true, ite_false] <;>
    first | (rw [ite_eq_left h]; decide) | (rw [ite_eq_right h]; decide)

/-! ## The loop -/

/-- The precondition, on entry. -/
structure PreE (s : State) : Prop where
  sp : 4 ≤ s.sp.toNat
  rd : s.rd = [pR (VG.Proof.MlDsa.Arm.Round.P s .r0)]
  wr : s.wr = []
  s0 : (belowA s.sp 4).Disjoint (pR (VG.Proof.MlDsa.Arm.Round.P s .r0))
  f0 : (s.gpr .r0).toNat + 1024 ≤ 2 ^ 32
  red : Reduced s.mem (VG.Proof.MlDsa.Arm.Round.P s .r0)

theorem pre_of {s : State} (h : (Spec.MlDsa.normLtContract Arm.abi 4).pre s) : VG.Proof.MlDsa.Arm.Round.NormLt.PreE s := by
  sig_pre [Spec.MlDsa.normLtContract, Spec.MlDsa.normLtSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h1, -, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- The registers the loop keeps. -/
abbrev fixedR : List Reg := [.r1, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]

theorem loop {s s₁ : State} (hp : VG.Proof.MlDsa.Arm.Round.NormLt.PreE s) (hE : Entry 4 s s₁) {s₂ : State} (hg : ∀ r, r ≠ .r4 → s₂.gpr r = s₁.gpr r)
    (h4 : s₂.gpr .r4 = 0) (hm : s₂.mem = s₁.mem) (hrd : s₂.rd = s₁.rd) (_hwr : s₂.wr = s₁.wr) (hsp : s₂.sp = s₁.sp) :
    WP isa (mapLoop .r2 nlBody) s₂ fun s' => (∀ r ∈ VG.Proof.MlDsa.Arm.Round.NormLt.fixedR, s'.gpr r = s.gpr r) ∧ s'.sp = s₁.sp ∧
      s'.mem = s₁.mem ∧ s'.gpr .r4 = VG.Proof.MlDsa.Arm.Round.NormLt.acc s.mem (VG.Proof.MlDsa.Arm.Round.P s .r0) (s.gpr .r1) 256 := by
  have g0 : s₂.gpr .r0 = s.gpr .r0 := (hg .r0 (by decide)).trans (congrFun hE.gpr _)
  have e : VG.Proof.MlDsa.Arm.Round.P s₂ .r0 = VG.Proof.MlDsa.Arm.Round.P s .r0 := by simp only [VG.Proof.MlDsa.Arm.Round.P, g0]
  have hL : VG.Proof.MlDsa.Arm.Round.Layout s₂ [.r0] [] := ⟨fun p hp' => by
      simp only [List.mem_singleton] at hp'; subst hp'; rw [hrd, hE.rd, e, hp.rd]; simp,
    fun _ h => (List.not_mem_nil h).elim, fun _ _ _ h => (List.not_mem_nil h).elim, List.Pairwise.nil,
    fun p hp' => by simp only [List.append_nil, List.mem_singleton] at hp'; subst hp'; rw [g0]; exact hp.f0⟩
  have eT : ∀ k < 256, coeffAt s₂.mem (VG.Proof.MlDsa.Arm.Round.P s₂ .r0) k = coeffAt s.mem (VG.Proof.MlDsa.Arm.Round.P s .r0) k := fun k hk => by
    rw [e, hm]
    exact coeffAt_frame hE.frame (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.s0.symm) (by rw [n_eq]; exact hk)
  refine WP.mono (VG.Proof.MlDsa.Arm.Round.loop_ok (ptrs := [.r0]) (fixed := VG.Proof.MlDsa.Arm.Round.NormLt.fixedR) (V := fun _ _ => 0)
    (J := fun i s' => s'.gpr .r4 = VG.Proof.MlDsa.Arm.Round.NormLt.acc s.mem (VG.Proof.MlDsa.Arm.Round.P s .r0) (s.gpr .r1) i) hL (by decide) (by decide)
    (fun s' hs' _ => by
      rw [hs']; simp only [show Reg.r4 ≠ Reg.r2 by decide, ite_false, h4]
      unfold VG.Proof.MlDsa.Arm.Round.NormLt.acc; rw [ite_eq_left fun k hk => absurd hk (Nat.not_lt_zero k)])
    fun i hi s' hI => ?_)
    fun s' hI => ⟨fun r hr => (hI.fixed r hr).trans ((hg r (by revert r; decide)).trans (congrFun hE.gpr r)),
      hI.sp.trans hsp, ?_, hI.j⟩
  · have g1 : s'.gpr .r1 = s.gpr .r1 :=
      (hI.fixed .r1 (by decide)).trans ((hg .r1 (by decide)).trans (congrFun hE.gpr _))
    refine WP.mono (VG.Proof.MlDsa.Arm.Round.NormLt.body_ok rfl g1 rfl hI.j (hI.inR hL hi (by simp) (by simp)))
      fun s'' ⟨r4, r0, r2, hz, hm', hf, rd, wr, sp⟩ => ⟨by rw [hm']; rfl, ?_, r2, hz, hf, rd, wr, sp, ?_⟩
    · intro p hp'; simp only [List.mem_singleton] at hp'; subst hp'; exact r0
    · show s''.gpr .r4 = _
      rw [r4, hI.read hL hi (by simp) (by simp), eT i hi, VG.Proof.MlDsa.Arm.Round.NormLt.bad_eq (hp.red i (by rw [n_eq]; exact hi)), VG.Proof.MlDsa.Arm.Round.NormLt.acc_succ]
  · have := hI.frame; simp only [List.map_nil] at this
    funext x; rw [← hm]; exact this x (fun _ h => (List.not_mem_nil h).elim)

theorem correct {s : State} (hp : VG.Proof.MlDsa.Arm.Round.NormLt.PreE s) :
    WP isa Impl.MlDsa.Arm.Round.normLt s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.gpr .r0 = if normRq [polyAt s.mem (VG.Proof.MlDsa.Arm.Round.P s .r0)] < (s.gpr .r1).toNat then 1 else 0 := by
  refine WP.mono (wp_saving [.r4] _ (W := [])
    (fun s₂ => (∀ r ∈ VG.Proof.MlDsa.Arm.Round.NormLt.fixedR, s₂.gpr r = s.gpr r) ∧
      s₂.gpr .r0 = if normRq [polyAt s.mem (VG.Proof.MlDsa.Arm.Round.P s .r0)] < (s.gpr .r1).toNat then 1 else 0)
    s hp.sp (fun _ h => (List.not_mem_nil h).elim) fun s₁ hE => ?_)
    fun s' ⟨s₂, ⟨hk, h0⟩, _, _, hsp, _, hg⟩ =>
      ⟨preserved_of_saving hg fun r hr hn => hk r (by revert r; decide), hsp, by rw [hg .r0]; exact h0⟩
  refine WP.seq (WP.of_runBlock ⟨_, runBlock_cons.trans (by rfl), ?_⟩)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Round.NormLt.loop hp hE (s₂ := s₁.setReg .r4 0) (fun r hr => by simp [State.setReg, hr])
    (by simp [State.setReg]) rfl rfl rfl rfl) fun s₃ ⟨hf, hsp, hm, h4⟩ => ?_)
  run_block [h4]
  refine ⟨fun x _ => by rw [hm], fun r hr => ?_, ?_⟩
  · have : r ≠ .r0 := by revert r; decide
    rw [ite_eq_right this, ite_eq_right this]; exact hf r hr
  · have hn := normRq_lt (polyAt s.mem (VG.Proof.MlDsa.Arm.Round.P s .r0)) (s.gpr .r1).toNat
    unfold VG.Proof.MlDsa.Arm.Round.NormLt.acc
    by_cases h : ∀ k < 256, VG.Proof.MlDsa.Arm.Round.NormLt.Ok (coeffAt s.mem (VG.Proof.MlDsa.Arm.Round.P s .r0) k) (s.gpr .r1)
    · rw [ite_eq_left h, ite_eq_left (hn.mpr fun i hi => ?_)]
      · rfl
      · rw [normZq_lt, polyAt_val hp.red hi]; exact h i (by rw [n_eq] at hi; exact hi)
    · rw [ite_eq_right h, ite_eq_right fun h' => h fun k hk => ?_]
      · rfl
      · have := (normZq_lt _ _).mp (hn.mp h' k (by rw [n_eq]; exact hk))
        rwa [polyAt_val hp.red (by rw [n_eq]; exact hk)] at this

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := []

theorem verified : Verified Arm.target Impl.MlDsa.Arm.Round.normLt (Spec.MlDsa.normLtContract Arm.abi 4) := by
  refine ⟨fun s hs => ?_, ct_of_saving [.r4] _ [.r0, .r1] (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, h⟩ := VG.Proof.MlDsa.Arm.Round.NormLt.correct (VG.Proof.MlDsa.Arm.Round.NormLt.pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Spec.MlDsa.normLtContract, Spec.MlDsa.normLtSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    rw [VG.Proof.MlKem.Arm.setWidth_append32, h]
    rfl
  · sig_pub [Spec.MlDsa.normLtContract, Spec.MlDsa.normLtSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    obtain ⟨hsp, h0, h1⟩ := h
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h0
    · simpa using h1
  · refine ⟨VG.Proof.MlDsa.Arm.Round.NormLt.satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlDsa.normLtContract, Spec.MlDsa.normLtSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
        Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact VG.Proof.MlDsa.Round.reduced_zero _

end VG.Proof.MlDsa.Arm.Round.NormLt

end
