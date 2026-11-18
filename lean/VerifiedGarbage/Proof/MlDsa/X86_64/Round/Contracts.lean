module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.MlDsa.Round.Mem
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Impl.MlDsa.X86_64.Round.Round
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

/-! ### `MlDsa.X86_64.Round.Loop`, which the modules that import this one used -/

section

/-!
# ML-DSA on x86-64: the loop over the coefficients

`mapLoop body` runs `body` for `rcx` = 256 down to 1, and iteration `i` (from 0)
handles coefficient `255 - i` at `[p + 4·rcx - 4]` (`cfAddr`) of each
polynomial `p`. `loop_ok` proves it once for every function: from a body that
writes, to coefficient `255 - i` of each output polynomial (in a register of
`outs`), the value `V o (255 - i)` and keeps an invariant `J` of its other
registers, the loop writes every coefficient of each output. The inputs
(registers `ins`) are never written, so the body reads the coefficients of the
initial memory (`Inv.read`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round VG.Proof.MlDsa.Round
open VG.Proof.MlDsa (coeffAt)
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep wp_countdown setReg_gpr setReg_mem ofNat64_pred)

/-! ## Addresses -/

/-- `p + 4c - 4`, the address of `cf p` when `rcx = c`. -/
def cfAddr (p c : Addr) : Addr := p + c * BitVec.ofNat 64 4 + BitVec.ofInt 64 (-4)

theorem ea_cf (s : State) (p : Reg) : s.ea (cf p) = cfAddr (s.gpr p) (s.gpr .rcx) := rfl

theorem cfAddr_eq (p : Addr) (j : Nat) :
    cfAddr p (BitVec.ofNat 64 (j + 1)) = coeffAddr p j := by
  unfold cfAddr coeffAddr
  rw [BitVec.add_assoc]
  refine congrArg (p + ·) ?_
  have e : BitVec.ofInt 64 (-4) = -BitVec.ofNat 64 4 := by decide
  rw [e, ← BitVec.sub_eq_add_neg]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_using []

/-! ## The writes of an iteration -/

/-- Stores of `v` at `a` for each `(a, v)`, in order. -/
def writes (m : Mem) (ps : List (Addr × BitVec 32)) : Mem := ps.foldl (fun m p => m.writeW p.1 p.2) m

theorem writes_cons (m : Mem) (p : Addr × BitVec 32) (ps : List (Addr × BitVec 32)) :
    writes m (p :: ps) = writes (m.writeW p.1 p.2) ps := rfl

section
variable (P : Reg → Addr)

/-- Writes to coefficient `j` of polynomials disjoint from that at `p` leave it unchanged. -/
theorem coeffAt_writes_disjoint (m : Mem) (outs : List Reg) (j : Nat) (hj : j < 256) (V : Reg → BitVec 32)
    {p : Addr} (hd : ∀ o ∈ outs, (pR p).Disjoint (pR (P o))) {k : Nat} (hk : k < 256) :
    coeffAt (writes m (outs.map fun o => (coeffAddr (P o) j, V o))) p k = coeffAt m p k := by
  induction outs generalizing m with
  | nil => rfl
  | cons o os ih =>
    rw [List.map_cons, writes_cons]
    rw [ih _ fun o' h => hd o' (List.mem_cons_of_mem _ h),
      coeffAt_writeW_disjoint m (hd o List.mem_cons_self) (coeff_contains _ hj) hk]

theorem coeffAt_writes (m : Mem) (outs : List Reg) (j : Nat) (hj : j < 256) (V : Reg → BitVec 32)
    (hpw : outs.Pairwise fun a b => (pR (P a)).Disjoint (pR (P b))) {o : Reg} (ho : o ∈ outs) {k : Nat}
    (hk : k < 256) :
    coeffAt (writes m (outs.map fun o => (coeffAddr (P o) j, V o))) (P o) k =
      if j = k then V o else coeffAt m (P o) k := by
  induction outs generalizing m with
  | nil => cases ho
  | cons o' os ih =>
    rw [List.map_cons, writes_cons]
    rw [List.pairwise_cons] at hpw
    by_cases hr : o ∈ os
    · rw [ih _ hpw.2 hr]
      have hd : (pR (P o)).Disjoint (pR (P o')) := (hpw.1 o hr).symm
      rw [coeffAt_writeW_disjoint m hd (coeff_contains _ hj) hk]
    · obtain rfl : o = o' := by simpa [hr] using ho
      rw [coeffAt_writes_disjoint P _ os j hj V (fun o' h => hpw.1 o' h) hk, coeffAt_writeW m _ hk hj]

theorem frame_writes {rs : List Region} {m₀ m : Mem} (hf : Frame rs m₀ m) (outs : List Reg) (j : Nat)
    (hj : j < 256) (V : Reg → BitVec 32) (hin : ∀ o ∈ outs, pR (P o) ∈ rs) :
    Frame rs m₀ (writes m (outs.map fun o => (coeffAddr (P o) j, V o))) := by
  induction outs generalizing m with
  | nil => exact hf
  | cons o os ih =>
    rw [List.map_cons, writes_cons]
    exact ih (hf.writeW (hin o List.mem_cons_self) _ (coeff_contains _ hj)) fun o' h =>
      hin o' (List.mem_cons_of_mem _ h)

end

/-! ## The loop -/

/-- Where the loop's polynomials are: inputs readable, outputs writable,
the outputs pairwise disjoint and disjoint from the inputs. -/
structure Layout (s₀ : State) (ins outs : List Reg) : Prop where
  rd : ∀ p ∈ ins, pR (s₀.gpr p) ∈ s₀.rd ++ s₀.wr
  wr : ∀ o ∈ outs, pR (s₀.gpr o) ∈ s₀.wr
  dis : ∀ p ∈ ins, ∀ o ∈ outs, (pR (s₀.gpr p)).Disjoint (pR (s₀.gpr o))
  pw : outs.Pairwise fun a b => (pR (s₀.gpr a)).Disjoint (pR (s₀.gpr b))

/-- After `i` iterations: the registers `fixed` are unchanged, the outputs
hold their values from coefficient `256 - i` on, and `J i`. -/
structure Inv (s₀ : State) (fixed outs : List Reg) (V : Reg → Nat → BitVec 32) (J : Nat → State → Prop)
    (i : Nat) (s : State) : Prop where
  fixed : ∀ r ∈ fixed, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (outs.map fun o => pR (s₀.gpr o)) s₀.mem s.mem
  done : ∀ o ∈ outs, ∀ k, 256 - i ≤ k → k < 256 → coeffAt s.mem (s₀.gpr o) k = V o k
  j : J i s

section
variable {s₀ : State} {ins outs fixed : List Reg} {V : Reg → Nat → BitVec 32} {J : Nat → State → Prop}
  {i : Nat} {s : State}

/-- The address of the coefficient that iteration `i` handles. -/
theorem Inv.addr (hI : Inv s₀ fixed outs V J i s) (hc : s.gpr .rcx = BitVec.ofNat 64 (256 - i)) (hi : i < 256)
    {p : Reg} (hp : p ∈ fixed) : cfAddr (s.gpr p) (s.gpr .rcx) = coeffAddr (s₀.gpr p) (255 - i) := by
  rw [hI.fixed p hp, hc, show 256 - i = 255 - i + 1 by omega_using [hi]]
  exact cfAddr_eq _ _

theorem Inv.inR (hL : Layout s₀ ins outs) (hI : Inv s₀ fixed outs V J i s) {p : Reg} (hp : p ∈ ins) {k : Nat}
    (hk : k < 256) : InRegions (s.rd ++ s.wr) (coeffAddr (s₀.gpr p) k) 4 := by
  rw [hI.rd, hI.wr]
  exact ⟨_, hL.rd p hp, coeff_contains _ hk⟩

theorem Inv.inW (hL : Layout s₀ ins outs) (hI : Inv s₀ fixed outs V J i s) {o : Reg} (ho : o ∈ outs) {k : Nat}
    (hk : k < 256) : InRegions s.wr (coeffAddr (s₀.gpr o) k) 4 := by
  rw [hI.wr]
  exact ⟨_, hL.wr o ho, coeff_contains _ hk⟩

/-- The inputs are those of the initial memory. -/
theorem Inv.read (hL : Layout s₀ ins outs) (hI : Inv s₀ fixed outs V J i s) {p : Reg} (hp : p ∈ ins) {k : Nat}
    (hk : k < 256) : s.mem.readW (coeffAddr (s₀.gpr p) k) 32 = coeffAt s₀.mem (s₀.gpr p) k :=
  coeffAt_frame hI.frame (fun _ hr => by
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hr
    exact hL.dis p hp o ho) hk

end

/-- The loop, from a body that writes `V o (255 - i)` to coefficient `255 - i` of each output. -/
theorem loop_ok {s₀ : State} {ins outs fixed clob : List Reg} {body : List Instr} {V : Reg → Nat → BitVec 32}
    {J : Nat → State → Prop} (hL : Layout s₀ ins outs) (hfix : ∀ r ∈ fixed, r ∉ clob) (hcx : .rcx ∈ clob)
    (hJ : ∀ s, s.gpr .rcx = BitVec.ofNat 64 256 → s.mem = s₀.mem → Keep [.rcx] s₀ s → J 0 s)
    (hbody : ∀ i < 256, ∀ s, Inv s₀ fixed outs V J i s → s.gpr .rcx = BitVec.ofNat 64 (256 - i) →
      WP isa (.block (body ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
        (s'.mem = writes s.mem (outs.map fun o => (coeffAddr (s₀.gpr o) (255 - i), V o (255 - i))) ∧
          s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧ J (i + 1) s') ∧
        Keep clob s s') :
    WP isa (mapLoop body) s₀ (Inv s₀ fixed outs V J 256) := by
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun s => s.mem = s₀.mem ∧ s.gpr .rcx = BitVec.ofNat 64 256)
    (by apply WP.of_runBlock; simp [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
      setReg_gpr, setReg_mem]) (by decide)) fun s₁ ⟨⟨hm, hc⟩, hk⟩ => ?_)
  have h0 : Inv s₀ fixed outs V J 0 s₁ := by
    refine ⟨fun r hr => hk.gpr fun h => ?_, hk.2.1, hk.2.2, ?_, fun _ _ k h₁ h₂ => absurd h₂ (by omega_using [h₁]),
      hJ s₁ hc hm hk⟩
    · simp only [List.mem_singleton] at h
      subst h
      exact hfix _ hr hcx
    · rw [hm]; exact Frame.refl _ _
  refine wp_countdown (cnt := .rcx) (N := 256) (by decide) (by decide) (Inv s₀ fixed outs V J)
    (fun i hi s hI hc => ?_) (fun _ h => h) h0 hc
  · refine WP.mono (hbody i hi s hI hc) fun s' ⟨⟨hm', hc', hz', hJ'⟩, hk'⟩ => ⟨?_, hc', hz'⟩
    refine ⟨fun r hr => (hk'.gpr (hfix r hr)).trans (hI.fixed r hr), hk'.2.1.trans hI.rd, hk'.2.2.trans hI.wr,
      ?_, fun o ho k h₁ h₂ => ?_, hJ'⟩
    · rw [hm']
      exact frame_writes _ hI.frame outs _ (by omega_using []) _ fun o ho => List.mem_map_of_mem ho
    · rw [hm', coeffAt_writes _ _ outs _ (by omega_using []) _ hL.pw ho h₂]
      split
      · subst k; rfl
      · exact hI.done o ho k (by omega_arith) h₂

end VG.Proof.MlDsa.X86_64.Round

end

end

/-!
# ML-DSA on x86-64: the contracts the rounding proofs are written against

For each function, a contract with the facts of its shared contract
(`Proof/MlDsa/Contract.lean`) spelled out for x86-64: the arguments in their
registers, the permitted regions, their disjointness, and the postcondition.
`Verified.of_correct` moves a proof to the shared contract, which implies it
(`round_implies`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Proof.MlDsa.Round
open VG.Spec.MlDsa

/-- The return address. -/
abbrev retR (s : State) : Region := ⟨s.gpr .rsp, 8⟩

/-- A `u32` argument in `r`. -/
abbrev arg32 (s : State) (r : Reg) : Nat := ((s.gpr r).setWidth 32).toNat

/-- `vg_mldsa_power2round(t = rdi, t1 = rsi, t0 = rdx)`. -/
def power2RoundK : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rdi)] ∧ s.wr = [pR (s.gpr .rsi), pR (s.gpr .rdx)] ∧
    (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) ∧ (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rdx)) ∧
    (pR (s.gpr .rsi)).Disjoint (pR (s.gpr .rdx)) ∧ (retR s).Disjoint (pR (s.gpr .rdi)) ∧
    (retR s).Disjoint (pR (s.gpr .rsi)) ∧ (retR s).Disjoint (pR (s.gpr .rdx)) ∧ Reduced s.mem (s.gpr .rdi)
  post s s' :=
    NatPolyIs s'.mem (s.gpr .rsi) ((polyAt s.mem (s.gpr .rdi)).map fun c => (power2Round c).1.toNat) ∧
      PolyIs s'.mem (s.gpr .rdx) ((polyAt s.mem (s.gpr .rdi)).map fun c => ofInt (power2Round c).2)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rsp = s₂.gpr .rsp

/-- `r = rdi, gamma2 = esi, out = rdx`, with the postcondition `post`. -/
def bitsK (post : State → State → Prop) : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rdi)] ∧ s.wr = [pR (s.gpr .rdx)] ∧ (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rdx)) ∧
    (retR s).Disjoint (pR (s.gpr .rdi)) ∧ (retR s).Disjoint (pR (s.gpr .rdx)) ∧ arg32 s .rsi ∈ gamma2s ∧
    Reduced s.mem (s.gpr .rdi)
  post := post
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    (s₁.gpr .rsi).setWidth 32 = (s₂.gpr .rsi).setWidth 32

/-- `vg_mldsa_high_bits(r = rdi, gamma2 = esi, out = rdx)`. -/
def highBitsK : Contract isa := bitsK fun s s' =>
  NatPolyIs s'.mem (s.gpr .rdx) ((polyAt s.mem (s.gpr .rdi)).map fun c => (highBits (arg32 s .rsi) c).toNat)

/-- `vg_mldsa_low_bits(r = rdi, gamma2 = esi, out = rdx)`. -/
def lowBitsK : Contract isa := bitsK fun s s' =>
  PolyIs s'.mem (s.gpr .rdx) ((polyAt s.mem (s.gpr .rdi)).map fun c => ofInt (lowBits (arg32 s .rsi) c))

/-- `vg_mldsa_norm_lt(f = rdi, bound = esi)`. -/
def normLtK : Contract isa where
  pre s := s.rd = [pR (s.gpr .rdi)] ∧ s.wr = [] ∧ (retR s).Disjoint (pR (s.gpr .rdi)) ∧ Reduced s.mem (s.gpr .rdi)
  post s s' := (s'.gpr .rax).setWidth 32 = if normRq [polyAt s.mem (s.gpr .rdi)] < arg32 s .rsi then 1 else 0
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    (s₁.gpr .rsi).setWidth 32 = (s₂.gpr .rsi).setWidth 32

/-- `a = rdi, b = rsi, gamma2 = edx, out = rcx`, with the precondition
`pre'` on the memory and the postcondition `post`. -/
def hintK (pre' : State → Prop) (post : State → State → Prop) : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rdi), pR (s.gpr .rsi)] ∧ s.wr = [pR (s.gpr .rcx)] ∧
    (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rcx)) ∧ (pR (s.gpr .rsi)).Disjoint (pR (s.gpr .rcx)) ∧
    (retR s).Disjoint (pR (s.gpr .rdi)) ∧ (retR s).Disjoint (pR (s.gpr .rsi)) ∧
    (retR s).Disjoint (pR (s.gpr .rcx)) ∧ arg32 s .rdx ∈ gamma2s ∧ pre' s
  post := post
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ (s₁.gpr .rdx).setWidth 32 = (s₂.gpr .rdx).setWidth 32

/-- `vg_mldsa_make_hint(z = rdi, r = rsi, gamma2 = edx, h = rcx)`. -/
def makeHintK : Contract isa :=
  hintK (fun s => Reduced s.mem (s.gpr .rdi) ∧ Reduced s.mem (s.gpr .rsi)) fun s s' =>
    let hint := Vector.zipWith (makeHint (arg32 s .rdx)) (polyAt s.mem (s.gpr .rdi)) (polyAt s.mem (s.gpr .rsi))
    HintIs s'.mem (s.gpr .rcx) 1 [hint] ∧ ((s'.gpr .rax).setWidth 32).toNat = hintOnes [hint]

/-- `vg_mldsa_use_hint(h = rdi, r = rsi, gamma2 = edx, out = rcx)`. -/
def useHintK : Contract isa :=
  hintK (fun s => Reduced s.mem (s.gpr .rsi)) fun s s' =>
    NatPolyIs s'.mem (s.gpr .rcx) (Vector.zipWith (fun hj rj => (useHint (arg32 s .rdx) hj rj).toNat)
      ((hintAt s.mem (s.gpr .rdi) 1).headD (Vector.replicate n false)) (polyAt s.mem (s.gpr .rsi)))

/-- The taint in which the registers `rs` are public, and the low halves of
`los` (public 32-bit arguments). -/
def regsLo (rs los : List Reg) : X86_64.Taint.T :=
  { regs := RegSet.ofList rs, flags := false, lo := RegSet.ofList los }

theorem agree_regsLo {rs los : List Reg} {s₁ s₂ : State} (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hl : ∀ r ∈ los, (s₁.gpr r).setWidth 32 = (s₂.gpr r).setWidth 32) :
    X86_64.Taint.Agree (regsLo rs los) s₁ s₂ where
  rf := ⟨fun r hr => h r (RegSet.mem_ofList.mp hr), fun h => by cases h⟩
  wr h := absurd rfl h
  wf₁ := ⟨fun h => absurd rfl h, fun _ h => by cases h⟩
  wf₂ := ⟨fun h => absurd rfl h, fun _ h => by cases h⟩
  ok _ h := by cases h
  slots _ h := by cases h
  lo r hr := hl r (RegSet.mem_ofList.mp hr)
  xr := X86_64.Taint.noXr

/-- `sig_implies`, whose satisfiability witness may need `Reduced` of the
memory of zeros. -/
tactic_template "round_implies " "[" ls:Lean.Parser.Tactic.simpLemma,* "]"
    " [" ws:Lean.Parser.Tactic.simpLemma,* "]" " using " w:term : tactic => `(tactic| exact
  { pre := by sig_implies_pre [$ls,*]
    post := by sig_implies_post [$ls,*]
    pub := by sig_implies_pub [$ls,*]
    sat := by
      refine ⟨$w, ?_⟩
      sig_pre [$ls,*]
      and_intros
      all_goals first
        | rfl
        | decide
        | exact Region.disjoint_of_sep (by decide)
        | exact reduced_zero _
        | (intro a h₁ h₂
           set_option linter.unusedSimpArgs false in
           simp only [Region.Contains, $ws,*] at h₁ h₂
           bv_omega) })

end VG.Proof.MlDsa.X86_64.Round
