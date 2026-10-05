import VerifiedGarbage.Proof.MlKem.X86.AddSub
import VerifiedGarbage.Proof.MlDsa.Pack.Hint2
import VerifiedGarbage.Spec.MlDsa.Poly
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Impl.MlDsa.X86.Pack.Hint

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Pack.HintBase`. -/
section

/-!
# ML-DSA on x86 (32-bit): what the proofs of the hint encodings share

* Loops whose number of iterations depends on the leaked data
  (`loopC`, which ends when a condition that correctness determines from
  public data fails, and `loopN`, with a public number of iterations), for
  the `Piece` framework of ML-KEM on x86 (`Proof/MlKem/X86/Piece.lean`).
* The layout both functions' contracts give (`Lay`): arguments `(r, rlen,
  omega, w, wlen)` on the stack, `r` read-only, `w` and the arguments
  writable, and where a leaf's body finds its arguments.
-/

namespace VG.Proof.MlDsa.X86.Pack.Hint

open VG VG.X86
open VG.Proof.MlKem.X86
open VG.Impl.MlKem.X86 (saveRegs)
open VG.Spec.MlDsa

/-! ## Running blocks

A block is run with `hrun`, a `simp only` that steps it one instruction at
a time (`runBlock_cons`, `runStep_some`) with `State.setReg` and the flags
kept folded (`RegUpd`); `Keep rs s s'` says that `s'` differs from `s` only
in the registers `rs` (and the flags and memory), and `WP.keep` proves it of
code none of whose instructions writes another register. -/

theorem arithFlags_eq (s : State) (x : BitVec 32) (c o : Bool) :
    arithFlags s x c o = s.setFlags (some c) (some o) (some (x == 0)) (some x.msb) := rfl
theorem sub_zero' (x : BitVec 32) : x - 0 = x := BitVec.sub_zero x
theorem setFlags_cf (s : State) (a b c d : Option Bool) : (s.setFlags a b c d).cf = a := rfl
theorem setFlags_zf (s : State) (a b c d : Option Bool) : (s.setFlags a b c d).zf = c := rfl

/-- Steps a block from a state whose accesses the hypotheses `ls` permit. -/
syntax "hrun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| hrun) => `(tactic| hrun [])
  | `(tactic| hrun [$ls,*]) => `(tactic| (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp (config := { decide := true }) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
        execAlu, arithFlags_eq, Proof.MlKem.X86.ea_at, State.load32, State.load8, State.store32,
        State.store8, Reg8.reg, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
        RegUpd.cf_setReg, RegUpd.zf_setReg, RegUpd.gpr_setFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags,
        RegUpd.wr_setFlags, setFlags_cf, setFlags_zf,
        Option.bind_some, Option.map_some, Option.map, Option.some.injEq, exists_eq_left', ite_true,
        ite_false, reduceCtorEq, BitVec.sub_self, sub_zero', true_and, and_true, $ls,*]))

/-- `s'` differs from `s` only in the registers `rs` (flags and memory
aside), with the same permissions. -/
def Keep (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem Keep.gpr {rs : List Reg} {s s' : State} (h : VG.Proof.MlDsa.X86.Pack.Hint.Keep rs s s') {r : Reg} (hr : r ∉ rs) :
    s'.gpr r = s.gpr r := h.1 r hr

theorem Keep.trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.MlDsa.X86.Pack.Hint.Keep rs s₁ s₂) (h₂ : VG.Proof.MlDsa.X86.Pack.Hint.Keep rs' s₂ s₃) :
    VG.Proof.MlDsa.X86.Pack.Hint.Keep (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.1 r hr.2, h₁.1 r hr.1], h₂.2.1.trans h₁.2.1, h₂.2.2.trans h₁.2.2⟩

theorem Keep.drop {r : Reg} {rs : List Reg} {s s' : State} (k : VG.Proof.MlDsa.X86.Pack.Hint.Keep (r :: rs) s s') (h : s'.gpr r = s.gpr r) :
    VG.Proof.MlDsa.X86.Pack.Hint.Keep rs s s' :=
  ⟨fun r' hr' => by
    by_cases e : r' = r
    · subst e; exact h
    · exact k.gpr (by simp only [List.mem_cons, not_or]; exact ⟨e, hr'⟩), k.2⟩

/-- Every register. -/
def allRegs : List Reg := [.eax, .ecx, .edx, .ebx, .esp, .ebp, .esi, .edi]

theorem mem_allRegs (r : Reg) : r ∈ VG.Proof.MlDsa.X86.Pack.Hint.allRegs := by cases r <;> decide

/-- Whether no instruction of `c` writes a register outside `rs`. -/
def writesOnly (rs : List Reg) (c : Prog isa) : Bool :=
  c.allInstrs fun i => allRegs.all fun r => rs.contains r || !Taint.clobbers i r

/-- A register that no instruction writes keeps its value. -/
theorem WP.keep {c : Prog isa} {s : State} {Q : State → Prop} (rs : List Reg) (h : WP isa c s Q)
    (hc : VG.Proof.MlDsa.X86.Pack.Hint.writesOnly rs c = true) : WP isa c s fun s' => Q s' ∧ VG.Proof.MlDsa.X86.Pack.Hint.Keep rs s s' := by
  obtain ⟨t, s', he, hq⟩ := h
  refine ⟨t, s', he, hq, fun r hr => Exec.gpr (fun i hi => ?_) he, (Exec.rdwr he).1, (Exec.rdwr he).2⟩
  unfold VG.Proof.MlDsa.X86.Pack.Hint.writesOnly at hc
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  have := List.all_eq_true.mp (hc i hi) r (VG.Proof.MlDsa.X86.Pack.Hint.mem_allRegs r)
  simp only [Bool.or_eq_true, List.contains_iff_mem, hr, false_or, Bool.not_eq_true'] at this
  exact this

/-- The byte a `store8` stores. -/
theorem b8_eq (x : BitVec 32) : BitVec.setWidth 8 x = BitVec.ofNat 8 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- A byte, zero-extended. -/
theorem toNat_setWidth32_8 (x : BitVec 8) : (BitVec.setWidth 32 x).toNat = x.toNat := by
  simp only [BitVec.toNat_setWidth]; omega

theorem add_one' (x : BitVec 32) (t : Nat) : x + BitVec.ofNat 32 t + 1 = x + BitVec.ofNat 32 (t + 1) := by
  rw [BitVec.add_assoc, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ofNat_add_ofNat]

theorem add_four' (x : BitVec 32) (t : Nat) : x + BitVec.ofNat 32 t + 4 = x + BitVec.ofNat 32 (t + 4) := by
  rw [BitVec.add_assoc, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ofNat_add_ofNat]

theorem add_1024' (x : BitVec 32) (t : Nat) : x + BitVec.ofNat 32 t + 1024 = x + BitVec.ofNat 32 (t + 1024) := by
  rw [BitVec.add_assoc, show (1024 : BitVec 32) = BitVec.ofNat 32 1024 from rfl, ofNat_add_ofNat]

theorem ofNat_add_one (t : Nat) : BitVec.ofNat 32 t + 1 = BitVec.ofNat 32 (t + 1) := by
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ofNat_add_ofNat]

theorem add_sub_one' (x : BitVec 32) {a : Nat} (h : 1 ≤ a) : x + BitVec.ofNat 32 a - 1 = x + BitVec.ofNat 32 (a - 1) := by
  rw [show BitVec.ofNat 32 a = BitVec.ofNat 32 (a - 1) + 1 by
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ofNat_add_ofNat, Nat.sub_add_cancel h],
    ← BitVec.add_assoc, BitVec.add_sub_cancel]

/-- A byte, zero-extended, as a number. -/
theorem byte32 (b : Byte) : b.setWidth 32 = BitVec.ofNat 32 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [VG.Proof.MlDsa.X86.Pack.Hint.toNat_setWidth32_8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := b.isLt; omega)]

/-- The loop condition after counting down. -/
theorem eval_ne_cnt {s : State} {N k : Nat} (hk : k < N) (hN : N < 2 ^ 32)
    (h : s.zf = some (BitVec.ofNat 32 (N - k) - 1 == 0)) : isa.eval .ne s = some (decide (k + 1 < N)) := by
  show s.zf.map (!·) = _
  rw [h]; exact cnt_ne hk hN

/-! ## Loops -/

section
variable {Pre : State → Prop} {Pub : State → State → Prop}

/-- A piece whose postcondition also says something of `s₀` that its
precondition implies. -/
theorem addX {A B : State → State → Prop} {c : Prog isa} {X : State → Prop} (h : Piece Pre Pub A B c)
    (hx : ∀ s₀ s, Pre s₀ → A s₀ s → X s₀) : Piece Pre Pub A (fun s₀ s => B s₀ s ∧ X s₀) c where
  wp s₀ s h₀ ha := (h.wp s₀ s h₀ ha).mono fun _ hb => ⟨hb, hx _ _ h₀ ha⟩
  ct := h.ct

/-- A loop that goes on after iteration `k` while `cont k s₀`, which
correctness determines from public data, and has fewer than `M s₀`
iterations. -/
theorem loopC {body : Prog isa} {cnd : Cond} (Inv : Nat → State → State → Prop) (B : State → State → Prop)
    (M : State → Nat) (cont : Nat → State → Bool)
    (hM : ∀ k s₀, Pre s₀ → cont k s₀ = true → k + 1 < M s₀)
    (hc : ∀ k s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → cont k s₀ = cont k s₀')
    (hb : ∀ k, Piece Pre Pub (Inv k) (fun s₀ s => isa.eval cnd s = some (cont k s₀) ∧
      (cont k s₀ = true → Inv (k + 1) s₀ s) ∧ (cont k s₀ = false → B s₀ s)) body) :
    Piece Pre Pub (Inv 0) B (.loop body cnd) where
  wp s₀ s h₀ ha := by
    refine WP.loop (M := isa) (fun n (s : State) => ∃ k, n = M s₀ - k ∧ Inv k s₀ s)
      (fun n s ⟨k, hn, hi⟩ => ?_) (M s₀) s ⟨0, (Nat.sub_zero _).symm, ha⟩
    refine ((hb k).wp _ _ h₀ hi).mono fun s' ⟨he, ht, hf⟩ => ?_
    cases h : cont k s₀
    · exact .inl ⟨by rw [he, h], hf h⟩
    · have := hM k s₀ h₀ h
      exact .inr ⟨by rw [he, h], M s₀ - (k + 1), by omega, k + 1, rfl, ht h⟩
  ct s₀ s₀' h₀ h₀' hp := by
    have := RelCT.loop (M := isa) (body := body) (c := cnd) (Q := fun _ _ => True)
      (fun n s s' => ∃ k, n = M s₀ - k ∧ Inv k s₀ s ∧ Inv k s₀' s')
      (fun n => by
        refine RelCT.exists_ fun k => ?_
        by_cases hk : n = M s₀ - k
        · refine ((hb k).ct' h₀ h₀' hp).mono (fun s s' ⟨_, a, a'⟩ => ⟨a, a'⟩) ?_
          rintro s s' ⟨⟨e₁, t₁, -⟩, e₂, t₂, -⟩
          refine ⟨by rw [e₁, e₂, hc k _ _ h₀ h₀' hp], fun _ => trivial, fun h => ?_⟩
          rw [e₁, Option.some.injEq] at h
          have := hM k s₀ h₀ h
          exact ⟨M s₀ - (k + 1), by omega, k + 1, rfl, t₁ h, t₂ (by rw [← hc k _ _ h₀ h₀' hp]; exact h)⟩
        · exact RelCT.of_false fun s s' ⟨h1, _⟩ => hk h1) (M s₀)
    exact this.mono (fun s s' ⟨a, a'⟩ => ⟨0, (Nat.sub_zero _).symm, a, a'⟩) fun _ _ h => h

/-- A loop of `N s₀ ≥ 1` iterations, where `N` is public. -/
theorem loopN {body : Prog isa} {cnd : Cond} (Inv : Nat → State → State → Prop) (N : State → Nat)
    (hN : ∀ s₀, Pre s₀ → 0 < N s₀) (hNp : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → N s₀ = N s₀')
    (hb : ∀ k, Piece Pre Pub (fun s₀ s => Inv k s₀ s ∧ k < N s₀)
      (fun s₀ s => Inv (k + 1) s₀ s ∧ isa.eval cnd s = some (decide (k + 1 < N s₀))) body) :
    Piece Pre Pub (Inv 0) (fun s₀ s => Inv (N s₀) s₀ s) (.loop body cnd) :=
  (VG.Proof.MlDsa.X86.Pack.Hint.loopC (fun k s₀ s => Inv k s₀ s ∧ k < N s₀) _ N (fun k s₀ => decide (k + 1 < N s₀))
    (fun _ _ _ h => of_decide_eq_true h) (fun k s₀ s₀' h₀ h₀' hp => by rw [hNp _ _ h₀ h₀' hp])
    fun k => (VG.Proof.MlDsa.X86.Pack.Hint.addX (X := fun s₀ => k < N s₀) (hb k) fun _ _ _ h => h.2).mono (fun _ _ _ h => h)
      fun s₀ s _ ⟨⟨hi, he⟩, hk⟩ => ⟨he, fun h => ⟨hi, of_decide_eq_true h⟩, fun h => by
        rw [show N s₀ = k + 1 by have := of_decide_eq_false h; omega]; exact hi⟩).mono
    (fun s₀ _ h₀ h => ⟨h, hN s₀ h₀⟩) fun _ _ _ h => h

/-- `loopN` over a block, which the taint analysis proves from `R`. -/
theorem countLoopN {body : List Instr} {cnd : Cond} (Inv : Nat → State → State → Prop) (N : State → Nat)
    (hN : ∀ s₀, Pre s₀ → 0 < N s₀) (hNp : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → N s₀ = N s₀')
    (R : List Reg)
    (hstep : ∀ k s₀ s, Pre s₀ → Inv k s₀ s → k < N s₀ → WP isa (.block body) s fun s' =>
      Inv (k + 1) s₀ s' ∧ isa.eval cnd s' = some (decide (k + 1 < N s₀)))
    (hR : ∀ k s₀ s₀' s s', Pre s₀ → Pre s₀' → Pub s₀ s₀' → Inv k s₀ s → Inv k s₀' s' →
      ∀ r ∈ R, s.gpr r = s'.gpr r)
    {hc : Taint.Hint VG.X86.Taint.T} (ht : (VG.X86.taint.check (τr R) (.block body) hc).isSome = true) :
    Piece Pre Pub (Inv 0) (fun s₀ s => Inv (N s₀) s₀ s) (.loop (.block body) cnd) :=
  VG.Proof.MlDsa.X86.Pack.Hint.loopN Inv N hN hNp fun k => Piece.taint R (fun s₀ s h₀ ⟨hi, hk⟩ => hstep k s₀ s h₀ hi hk)
    (fun s₀ s₀' s s' h₀ h₀' hp ⟨a, _⟩ ⟨a', _⟩ => hR k s₀ s₀' s s' h₀ h₀' hp a a') ht

/-- An empty block. -/
theorem nil_piece {A B : State → State → Prop} (h : ∀ s₀ s, Pre s₀ → A s₀ s → B s₀ s) :
    Piece Pre Pub A B (.block []) :=
  Piece.taint [] (fun s₀ s hp ha => WP.block_nil_iff.mpr (h s₀ s hp ha))
    (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)

end

/-! ## The layout -/

section
variable (s₀ : State)
/-- The buffer read, `w` the one written. -/
abbrev rA : Addr := (arg s₀ 0).setWidth 64
abbrev wA : Addr := (arg s₀ 3).setWidth 64
/-- `ω`. -/
abbrev ω : Nat := (arg s₀ 2).toNat
/-- The arguments. -/
abbrev gR : Region := ⟨argAddr s₀ 0, 20⟩
/-- The leaf's frame, as the contract gives it. -/
abbrev stkR : Region := ⟨(E0 s₀).setWidth 64 - 16#64, 16⟩
end

/-- The facts of both contracts' layouts, for a buffer of `a` bytes read and
one of `b` written. -/
structure Lay (s₀ : State) (a b : Nat) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 20 ≤ 2 ^ 32
  rd : s₀.rd = [⟨VG.Proof.MlDsa.X86.Pack.Hint.rA s₀, a⟩]
  wr : s₀.wr = [⟨VG.Proof.MlDsa.X86.Pack.Hint.wA s₀, b⟩, VG.Proof.MlDsa.X86.Pack.Hint.gR s₀]
  r_w : (⟨VG.Proof.MlDsa.X86.Pack.Hint.rA s₀, a⟩ : Region).Disjoint ⟨VG.Proof.MlDsa.X86.Pack.Hint.wA s₀, b⟩
  r_g : (⟨VG.Proof.MlDsa.X86.Pack.Hint.rA s₀, a⟩ : Region).Disjoint (VG.Proof.MlDsa.X86.Pack.Hint.gR s₀)
  w_g : (⟨VG.Proof.MlDsa.X86.Pack.Hint.wA s₀, b⟩ : Region).Disjoint (VG.Proof.MlDsa.X86.Pack.Hint.gR s₀)
  ret_r : (retR s₀).Disjoint ⟨VG.Proof.MlDsa.X86.Pack.Hint.rA s₀, a⟩
  ret_w : (retR s₀).Disjoint ⟨VG.Proof.MlDsa.X86.Pack.Hint.wA s₀, b⟩
  ret_g : (retR s₀).Disjoint (VG.Proof.MlDsa.X86.Pack.Hint.gR s₀)
  stk_r : (VG.Proof.MlDsa.X86.Pack.Hint.stkR s₀).Disjoint ⟨VG.Proof.MlDsa.X86.Pack.Hint.rA s₀, a⟩
  stk_w : (VG.Proof.MlDsa.X86.Pack.Hint.stkR s₀).Disjoint ⟨VG.Proof.MlDsa.X86.Pack.Hint.wA s₀, b⟩
  stk_g : (VG.Proof.MlDsa.X86.Pack.Hint.stkR s₀).Disjoint (VG.Proof.MlDsa.X86.Pack.Hint.gR s₀)
  r_fit : (arg s₀ 0).toNat + a ≤ 2 ^ 32
  w_fit : (arg s₀ 3).toNat + b ≤ 2 ^ 32

namespace Lay
variable {s₀ : State} {a b : Nat} (hl : VG.Proof.MlDsa.X86.Pack.Hint.Lay s₀ a b)
include hl

theorem stk_eq : VG.Proof.MlDsa.X86.Pack.Hint.stkR s₀ = frameR s₀ := by
  simp only [VG.Proof.MlDsa.X86.Pack.Hint.stkR, frameR, below]; rw [Taint.sub_setWidth hl.sp]

/-- The push changes nothing but the frame. -/
theorem P0_keep : Frame [frameR s₀] s₀.mem (P0 s₀).mem := by
  have hf := pushed_frame (rs := saveRegs) (s := s₀) (by decide) (by rw [saveRegs_len]; exact hl.sp)
  rw [saveRegs_len] at hf
  exact hf

/-- The arguments, after the push. -/
theorem P0_argw {i : Nat} (hi : i < 5) : (P0 s₀).mem.readW (argAddr s₀ i) 32 = arg s₀ i :=
  P0_arg hl.sp (n := 5) hi hl.sp' hl.stk_g

theorem argIn {s : State} (hrd : s.rd = (P0 s₀).rd) (hwr : s.wr = (P0 s₀).wr) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [hrd, hwr]
  exact P0_argIn hi hl.sp' (by simp [hl.wr])

theorem argOut {s : State} (hwr : s.wr = (P0 s₀).wr) {i : Nat} (hi : i < 5) : InRegions s.wr (argAddr s₀ i) 4 := by
  rw [hwr, P0_wr, hl.wr]
  exact ⟨VG.Proof.MlDsa.X86.Pack.Hint.gR s₀, by simp, arg_contains (n := 5) hi hl.sp'⟩

/-- The bytes read, as on entry. -/
theorem r_keep {s : State} {W : List Region} (hf : Frame W (P0 s₀).mem s.mem)
    (hW : ∀ r ∈ W, (⟨VG.Proof.MlDsa.X86.Pack.Hint.rA s₀, a⟩ : Region).Disjoint r) {t : Nat} (ht : t < a) :
    s.mem (VG.Proof.MlDsa.X86.Pack.Hint.rA s₀ + BitVec.ofNat 64 t) = s₀.mem (VG.Proof.MlDsa.X86.Pack.Hint.rA s₀ + BitVec.ofNat 64 t) := by
  have := hl.r_fit
  rw [hf.bytes (R := ⟨VG.Proof.MlDsa.X86.Pack.Hint.rA s₀, a⟩) hW (show a ≤ 2 ^ 64 by omega) ht,
    hl.P0_keep.bytes (R := ⟨VG.Proof.MlDsa.X86.Pack.Hint.rA s₀, a⟩) (by simpa [← hl.stk_eq] using hl.stk_r.symm) (show a ≤ 2 ^ 64 by omega) ht]

theorem wW : ∀ r ∈ [(⟨VG.Proof.MlDsa.X86.Pack.Hint.wA s₀, b⟩ : Region)], (frameR s₀).Disjoint r ∧ (retR s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact ⟨by rw [← hl.stk_eq]; exact hl.stk_w, hl.ret_w⟩

end Lay

theorem argEa {s₀ s : State} (h : s.gpr .esp = (P0 s₀).gpr .esp) (i : Nat) :
    (s.gpr .esp + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64 = argAddr s₀ i := by
  rw [h]; exact P0_argAddr s₀ i

end VG.Proof.MlDsa.X86.Pack.Hint

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Pack.HintPack`. -/
section

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_hint_bit_pack`

The code follows the fold form of `HintBitPack` (`Pack/Hint.lean`, `hpS` and
`hpT` of `Pack/Hint2.lean`) step by step: the bytes of `y` are the array of
the spec, and `eax` its index, which stays below `ω` because it counts the 1s
before the current coefficient (`hpT_idx_lt`).

Constant time but for the hint: the invariants state every register the
code branches on or addresses memory with as a function of the entry state
`s₀`, through the hint, which two runs with the same public data and leak
agree on (`PPub`); so the branches (`Piece.ite`) and the addresses (the
taint analysis, `Piece.taint`) agree.
-/

namespace VG.Proof.MlDsa.X86.Pack.Hint

open VG VG.X86 VG.Impl.MlDsa.X86.Pack
open VG.Impl.MlKem.X86 (at_ saveRegs)
open VG.Proof.MlKem.X86
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem (bytesAt_writeW8 bytesAt_eq)
open VG.Proof.MlDsa.Pack

namespace Pk

section
variable (s₀ : State)
/-- `hlen`, `len`, `k`. -/
abbrev hL : Nat := (arg s₀ 1).toNat
abbrev yL : Nat := (arg s₀ 4).toNat
abbrev K : Nat := VG.Proof.MlDsa.X86.Pack.Hint.Pk.yL s₀ - VG.Proof.MlDsa.X86.Pack.Hint.ω s₀
/-- `y`. -/
abbrev yR : Region := ⟨VG.Proof.MlDsa.X86.Pack.Hint.wA s₀, VG.Proof.MlDsa.X86.Pack.Hint.Pk.yL s₀⟩
/-- The hint. -/
abbrev H : List (Vector Bool n) := hintAt s₀.mem (VG.Proof.MlDsa.X86.Pack.Hint.rA s₀) (VG.Proof.MlDsa.X86.Pack.Hint.Pk.K s₀)
/-- The spec's state after `i` polynomials, and `j` coefficients. -/
abbrev S (i : Nat) : Array Byte × Nat := hpS (VG.Proof.MlDsa.X86.Pack.Hint.ω s₀) (VG.Proof.MlDsa.X86.Pack.Hint.Pk.K s₀) (VG.Proof.MlDsa.X86.Pack.Hint.Pk.H s₀) i
abbrev T (i j : Nat) : Array Byte × Nat := hpT (VG.Proof.MlDsa.X86.Pack.Hint.ω s₀) (VG.Proof.MlDsa.X86.Pack.Hint.Pk.K s₀) (VG.Proof.MlDsa.X86.Pack.Hint.Pk.H s₀) i j
/-- Coefficient `j` of polynomial `i`. -/
abbrev bit (i j : Nat) : Bool := ((VG.Proof.MlDsa.X86.Pack.Hint.Pk.H s₀).getD i noHint)[j]!
end

structure Pre (s₀ : State) : Prop extends VG.Proof.MlDsa.X86.Pack.Hint.Lay s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Pk.hL s₀ * 4) (VG.Proof.MlDsa.X86.Pack.Hint.Pk.yL s₀) where
  par : (VG.Proof.MlDsa.X86.Pack.Hint.ω s₀, VG.Proof.MlDsa.X86.Pack.Hint.Pk.K s₀) ∈ hintParams
  le : VG.Proof.MlDsa.X86.Pack.Hint.ω s₀ ≤ VG.Proof.MlDsa.X86.Pack.Hint.Pk.yL s₀
  hlen : VG.Proof.MlDsa.X86.Pack.Hint.Pk.hL s₀ = 256 * VG.Proof.MlDsa.X86.Pack.Hint.Pk.K s₀
  ones : hintOnes (VG.Proof.MlDsa.X86.Pack.Hint.Pk.H s₀) ≤ VG.Proof.MlDsa.X86.Pack.Hint.ω s₀

theorem Pre.of {s₀ : State} (h : (hintBitPackContract X86.abi 16).pre s₀) : VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pre s₀ := by
  sig_pre [hintBitPackContract, hintBitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩, h16, h17, h18, h19⟩

theorem Pre.facts {s₀ : State} (hp : VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pre s₀) :
    4 ≤ VG.Proof.MlDsa.X86.Pack.Hint.Pk.K s₀ ∧ VG.Proof.MlDsa.X86.Pack.Hint.Pk.K s₀ ≤ 8 ∧ VG.Proof.MlDsa.X86.Pack.Hint.ω s₀ ≤ 80 ∧ VG.Proof.MlDsa.X86.Pack.Hint.ω s₀ + VG.Proof.MlDsa.X86.Pack.Hint.Pk.K s₀ = VG.Proof.MlDsa.X86.Pack.Hint.Pk.yL s₀ ∧ VG.Proof.MlDsa.X86.Pack.Hint.Pk.hL s₀ = 256 * VG.Proof.MlDsa.X86.Pack.Hint.Pk.K s₀ := by
  have := mem_hintParams hp.par
  have := hp.le
  have := hp.hlen
  have e : VG.Proof.MlDsa.X86.Pack.Hint.Pk.K s₀ = VG.Proof.MlDsa.X86.Pack.Hint.Pk.yL s₀ - VG.Proof.MlDsa.X86.Pack.Hint.ω s₀ := rfl
  omega

/-- The public data: `esp`, the arguments and the hint. -/
structure Pub (s₀ s₀' : State) : Prop where
  e0 : E0 s₀ = E0 s₀'
  a0 : arg s₀ 0 = arg s₀' 0
  a1 : arg s₀ 1 = arg s₀' 1
  a2 : arg s₀ 2 = arg s₀' 2
  a3 : arg s₀ 3 = arg s₀' 3
  a4 : arg s₀ 4 = arg s₀' 4
  h : VG.Proof.MlDsa.X86.Pack.Hint.Pk.H s₀ = VG.Proof.MlDsa.X86.Pack.Hint.Pk.H s₀'

theorem Pub.of {s₀ s₀' : State} (hp : VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pre s₀) (h : (hintBitPackContract X86.abi 16).pub s₀ s₀') : VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pub s₀ s₀' := by
  sig_pub [hintBitPackContract, hintBitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e, hl, a0, a1, a2, a3, a4⟩ := h
  refine ⟨e, a0, a1, a2, a3, a4, ?_⟩
  rw [← a0, ← a1] at hl
  have hw := coeffAt_of_leak hl
  simp only [VG.Proof.MlDsa.X86.Pack.Hint.Pk.H, VG.Proof.MlDsa.X86.Pack.Hint.Pk.K, VG.Proof.MlDsa.X86.Pack.Hint.Pk.yL, VG.Proof.MlDsa.X86.Pack.Hint.ω, VG.Proof.MlDsa.X86.Pack.Hint.rA, ← a0, ← a2, ← a4]
  exact hintAt_congr fun t ht => hw t (by have := hp.hlen; simp only [VG.Proof.MlDsa.X86.Pack.Hint.Pk.hL, VG.Proof.MlDsa.X86.Pack.Hint.Pk.K, VG.Proof.MlDsa.X86.Pack.Hint.Pk.yL, VG.Proof.MlDsa.X86.Pack.Hint.ω] at this; omega)

theorem Pub.eK {s₀ s₀' : State} (h : VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pub s₀ s₀') : VG.Proof.MlDsa.X86.Pack.Hint.Pk.K s₀ = VG.Proof.MlDsa.X86.Pack.Hint.Pk.K s₀' := by
  show (arg s₀ 4).toNat - (arg s₀ 2).toNat = (arg s₀' 4).toNat - (arg s₀' 2).toNat; rw [h.a2, h.a4]
theorem Pub.eω {s₀ s₀' : State} (h : VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pub s₀ s₀') : VG.Proof.MlDsa.X86.Pack.Hint.ω s₀ = VG.Proof.MlDsa.X86.Pack.Hint.ω s₀' := by
  show (arg s₀ 2).toNat = (arg s₀' 2).toNat; rw [h.a2]
theorem Pub.eT {s₀ s₀' : State} (h : VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pub s₀ s₀') (i j : Nat) : VG.Proof.MlDsa.X86.Pack.Hint.Pk.T s₀ i j = VG.Proof.MlDsa.X86.Pack.Hint.Pk.T s₀' i j := by
  show hpT (VG.Proof.MlDsa.X86.Pack.Hint.ω s₀) (VG.Proof.MlDsa.X86.Pack.Hint.Pk.K s₀) (VG.Proof.MlDsa.X86.Pack.Hint.Pk.H s₀) i j = hpT (VG.Proof.MlDsa.X86.Pack.Hint.ω s₀') (VG.Proof.MlDsa.X86.Pack.Hint.Pk.K s₀') (VG.Proof.MlDsa.X86.Pack.Hint.Pk.H s₀') i j; rw [h.h, h.eω, h.eK]
theorem Pub.eS {s₀ s₀' : State} (h : VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pub s₀ s₀') (i : Nat) : VG.Proof.MlDsa.X86.Pack.Hint.Pk.S s₀ i = VG.Proof.MlDsa.X86.Pack.Hint.Pk.S s₀' i := by
  show hpS (VG.Proof.MlDsa.X86.Pack.Hint.ω s₀) (VG.Proof.MlDsa.X86.Pack.Hint.Pk.K s₀) (VG.Proof.MlDsa.X86.Pack.Hint.Pk.H s₀) i = hpS (VG.Proof.MlDsa.X86.Pack.Hint.ω s₀') (VG.Proof.MlDsa.X86.Pack.Hint.Pk.K s₀') (VG.Proof.MlDsa.X86.Pack.Hint.Pk.H s₀') i; rw [h.h, h.eω, h.eK]

/-! ## What holds throughout the body -/

structure Base (s₀ s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  frame : Frame [VG.Proof.MlDsa.X86.Pack.Hint.Pk.yR s₀] (P0 s₀).mem s.mem

theorem Base.keep {s₀ s s' : State} (h : VG.Proof.MlDsa.X86.Pack.Hint.Pk.Base s₀ s) {rs : List Reg} (k : VG.Proof.MlDsa.X86.Pack.Hint.Keep rs s s') (hsp : Reg.esp ∉ rs)
    (hm : Frame [VG.Proof.MlDsa.X86.Pack.Hint.Pk.yR s₀] s.mem s'.mem) : VG.Proof.MlDsa.X86.Pack.Hint.Pk.Base s₀ s' :=
  ⟨(k.gpr hsp).trans h.esp, k.2.1.trans h.rd, k.2.2.trans h.wr, h.frame.trans hm⟩

namespace Base
variable {s₀ s : State} (hp : VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pre s₀) (h : VG.Proof.MlDsa.X86.Pack.Hint.Pk.Base s₀ s)
include hp h

theorem argw {i : Nat} (hi : i < 5) : s.mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  rw [h.frame.readW (arg_contains (n := 5) hi hp.sp') (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.w_g.symm) (by decide)]
  exact hp.P0_argw hi

theorem argIn {i : Nat} (hi : i < 5) : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := hp.argIn h.rd h.wr hi

/-- A word of the hint, as on entry. -/
theorem word {t : Nat} (ht : t < 256 * VG.Proof.MlDsa.X86.Pack.Hint.Pk.K s₀) : coeffAt s.mem (VG.Proof.MlDsa.X86.Pack.Hint.rA s₀) t = coeffAt s₀.mem (VG.Proof.MlDsa.X86.Pack.Hint.rA s₀) t := by
  have := hp.facts
  have hf := hp.r_fit
  have hc : (⟨VG.Proof.MlDsa.X86.Pack.Hint.rA s₀, VG.Proof.MlDsa.X86.Pack.Hint.Pk.hL s₀ * 4⟩ : Region).Contains (coeffAddr (VG.Proof.MlDsa.X86.Pack.Hint.rA s₀) t) 4 :=
    Offset.contains_base _ (by omega) (by omega)
  rw [coeffAt_eq, coeffAt_eq, h.frame.readW hc (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.r_w) (by decide),
    hp.P0_keep.readW hc (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [← hp.stk_eq]; exact hp.stk_r.symm) (by decide)]

theorem inH {t : Nat} (ht : t < 256 * VG.Proof.MlDsa.X86.Pack.Hint.Pk.K s₀) : InRegions (s.rd ++ s.wr) (coeffAddr (VG.Proof.MlDsa.X86.Pack.Hint.rA s₀) t) 4 := by
  have := hp.facts
  have hf := hp.r_fit
  rw [h.rd, h.wr, pushed_rd, hp.rd]
  exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), Offset.contains_base _ (by omega) (by omega)⟩

theorem inY {t : Nat} (ht : t < VG.Proof.MlDsa.X86.Pack.Hint.Pk.yL s₀) : InRegions s.wr (VG.Proof.MlDsa.X86.Pack.Hint.wA s₀ + BitVec.ofNat 64 t) 1 := by
  have hf := hp.w_fit
  rw [h.wr, P0_wr, hp.wr]
  exact ⟨VG.Proof.MlDsa.X86.Pack.Hint.Pk.yR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩

end Base

/-- A byte of `y`. -/
theorem yAddr {s₀ : State} (hp : VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pre s₀) {t : Nat} (ht : t < VG.Proof.MlDsa.X86.Pack.Hint.Pk.yL s₀) :
    addr (arg s₀ 3 + BitVec.ofNat 32 t) 0 = VG.Proof.MlDsa.X86.Pack.Hint.wA s₀ + BitVec.ofNat 64 t := by
  have := hp.w_fit; rw [addr_add (by omega), Nat.add_zero]

/-- A word of the hint. -/
theorem hAddr {s₀ : State} (hp : VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pre s₀) {t : Nat} (ht : t < 256 * VG.Proof.MlDsa.X86.Pack.Hint.Pk.K s₀) :
    addr (arg s₀ 0 + BitVec.ofNat 32 (4 * t)) 0 = coeffAddr (VG.Proof.MlDsa.X86.Pack.Hint.rA s₀) t := by
  have := hp.facts; have := hp.r_fit; rw [addr_add (by omega), Nat.add_zero]

theorem bit_eq {s₀ : State} {i j : Nat} (hi : i < VG.Proof.MlDsa.X86.Pack.Hint.Pk.K s₀) (hj : j < 256) :
    VG.Proof.MlDsa.X86.Pack.Hint.Pk.bit s₀ i j = decide (coeffAt s₀.mem (VG.Proof.MlDsa.X86.Pack.Hint.rA s₀) (256 * i + j) ≠ 0) := hintAt_get hi hj

/-! ## Zeroing `y` -/

/-- After `t` bytes. -/
structure ZI (s₀ : State) (t : Nat) (s : State) : Prop extends VG.Proof.MlDsa.X86.Pack.Hint.Pk.Base s₀ s where
  edi : s.gpr .edi = arg s₀ 3 + BitVec.ofNat 32 t
  ecx : s.gpr .ecx = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Pk.yL s₀ - t)
  eax : s.gpr .eax = 0
  zero : ∀ u < t, s.mem (VG.Proof.MlDsa.X86.Pack.Hint.wA s₀ + BitVec.ofNat 64 u) = 0

theorem zinit_piece : Piece VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pre VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pub (fun s₀ s => s = P0 s₀) (VG.Proof.MlDsa.X86.Pack.Hint.Pk.ZI · 0) (.block hbpZeroInit) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_) (by taint_decide)
  · subst e
    have b₀ : VG.Proof.MlDsa.X86.Pack.Hint.Pk.Base s₀ (P0 s₀) := ⟨rfl, rfl, rfl, Frame.refl _ _⟩
    have a3 : addr ((P0 s₀).gpr .esp) 32 = argAddr s₀ 3 := VG.Proof.MlDsa.X86.Pack.Hint.argEa rfl 3
    have a4 : addr ((P0 s₀).gpr .esp) 36 = argAddr s₀ 4 := VG.Proof.MlDsa.X86.Pack.Hint.argEa rfl 4
    have i3 := b₀.argIn hp (i := 3) (by omega)
    have i4 := b₀.argIn hp (i := 4) (by omega)
    have v3 := b₀.argw hp (i := 3) (by omega)
    have v4 := b₀.argw hp (i := 4) (by omega)
    have hb : WP isa (.block hbpZeroInit) (P0 s₀) fun s' => s'.gpr .edi = arg s₀ 3 ∧ s'.gpr .ecx = arg s₀ 4 ∧
        s'.gpr .eax = 0 ∧ s'.mem = (P0 s₀).mem := by
      hrun [hbpZeroInit, a3, a4, i3, i4, v3, v4]
    refine (WP.keep [.edi, .ecx, .eax] hb (by decide)).mono fun s' ⟨⟨e1, e2, e3, m⟩, k⟩ =>
      ⟨b₀.keep k (by decide) (by rw [m]; exact Frame.refl _ _), by rw [e1]; simp, by rw [e2]; simp, e3,
        fun u hu => absurd hu (Nat.not_lt_zero _)⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', P0_esp, P0_esp, hq.e0]

theorem zstep {s₀ : State} (hp : VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pre s₀) {t : Nat} (ht : t < VG.Proof.MlDsa.X86.Pack.Hint.Pk.yL s₀) {s : State} (h : VG.Proof.MlDsa.X86.Pack.Hint.Pk.ZI s₀ t s) :
    WP isa (.block hbpZeroBody) s fun s' => VG.Proof.MlDsa.X86.Pack.Hint.Pk.ZI s₀ (t + 1) s' ∧ isa.eval .ne s' = some (decide (t + 1 < VG.Proof.MlDsa.X86.Pack.Hint.Pk.yL s₀)) := by
  have hf := hp.w_fit
  have := hp.facts
  have ea := VG.Proof.MlDsa.X86.Pack.Hint.Pk.yAddr hp ht
  have hin := h.inY hp ht
  have hb : WP isa (.block hbpZeroBody) s fun s' => s'.gpr .edi = s.gpr .edi + 1 ∧ s'.gpr .ecx = s.gpr .ecx - 1 ∧
      s'.zf = some (s.gpr .ecx - 1 == 0) ∧
      s'.mem = s.mem.writeW (VG.Proof.MlDsa.X86.Pack.Hint.wA s₀ + BitVec.ofNat 64 t) (BitVec.setWidth 8 (0 : BitVec 32)) := by
    hrun [hbpZeroBody, h.edi, ea, hin, h.eax]
  have hc : (VG.Proof.MlDsa.X86.Pack.Hint.Pk.yR s₀).Contains (VG.Proof.MlDsa.X86.Pack.Hint.wA s₀ + BitVec.ofNat 64 t) (8 / 8) := Offset.contains_base _ (by omega) (by omega)
  refine (WP.keep [.edi, .ecx] hb (by decide)).mono fun s' ⟨⟨e1, e2, z, m⟩, k⟩ => ?_
  have hm : Frame [VG.Proof.MlDsa.X86.Pack.Hint.Pk.yR s₀] s.mem s'.mem := by
    rw [m]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hc
  refine ⟨⟨h.keep k (by decide) hm, by rw [e1, h.edi, VG.Proof.MlDsa.X86.Pack.Hint.add_one'], by rw [e2, h.ecx]; exact cnt_next ht,
      by rw [k.gpr (by decide), h.eax], fun u hu => ?_⟩, VG.Proof.MlDsa.X86.Pack.Hint.eval_ne_cnt ht (by omega) (by rw [z, h.ecx])⟩
  rw [m, VG.WriteBytes.writeW8_apply]
  split
  · rfl
  · rename_i hne
    exact h.zero u (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hu) fun e => hne (by rw [e]))

theorem zloop_piece : Piece VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pre VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pub (VG.Proof.MlDsa.X86.Pack.Hint.Pk.ZI · 0) (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Pk.ZI s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Pk.yL s₀) s) (.loop (.block hbpZeroBody) .ne) :=
  VG.Proof.MlDsa.X86.Pack.Hint.countLoopN (fun t s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Pk.ZI s₀ t s) VG.Proof.MlDsa.X86.Pack.Hint.Pk.yL (fun s₀ hp => by have := hp.facts; omega)
    (fun _ _ _ _ hq => by simp only [VG.Proof.MlDsa.X86.Pack.Hint.Pk.yL, hq.a4]) [.edi] (fun t s₀ s hp h ht => VG.Proof.MlDsa.X86.Pack.Hint.Pk.zstep hp ht h)
    (fun t s₀ s₀' s s' _ _ hq h h' r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      rw [h.edi, h'.edi, hq.a3]) (by taint_decide)

/-! ## The polynomials -/

/-- Within polynomial `i`: the registers of coefficient `j`, and the data
after `d` coefficients. -/
structure CI (s₀ : State) (i j d : Nat) (s : State) : Prop extends VG.Proof.MlDsa.X86.Pack.Hint.Pk.Base s₀ s where
  lt : i < VG.Proof.MlDsa.X86.Pack.Hint.Pk.K s₀
  esi : s.gpr .esi = arg s₀ 0 + BitVec.ofNat 32 (4 * (256 * i + j))
  ebx : s.gpr .ebx = BitVec.ofNat 32 j
  eax : s.gpr .eax = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Pk.T s₀ i d).2
  edi : s.gpr .edi = arg s₀ 3
  ecx : s.gpr .ecx = arg s₀ 3 + BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.ω s₀ + i)
  ebp : s.gpr .ebp = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Pk.K s₀ - i)
  y : bytesAt s.mem (VG.Proof.MlDsa.X86.Pack.Hint.wA s₀) (VG.Proof.MlDsa.X86.Pack.Hint.Pk.yL s₀) = (VG.Proof.MlDsa.X86.Pack.Hint.Pk.T s₀ i d).1.toList

/-- `CI`, after a block that writes only `edx` and the flags. -/
theorem CI.edx {s₀ s s' : State} {i j d : Nat} (h : VG.Proof.MlDsa.X86.Pack.Hint.Pk.CI s₀ i j d s) (k : VG.Proof.MlDsa.X86.Pack.Hint.Keep [.edx] s s') (hm : s'.mem = s.mem) :
    VG.Proof.MlDsa.X86.Pack.Hint.Pk.CI s₀ i j d s' :=
  ⟨h.keep k (by decide) (by rw [hm]; exact Frame.refl _ _), h.lt, by rw [k.gpr (by decide), h.esi],
    by rw [k.gpr (by decide), h.ebx], by rw [k.gpr (by decide), h.eax], by rw [k.gpr (by decide), h.edi],
    by rw [k.gpr (by decide), h.ecx], by rw [k.gpr (by decide), h.ebp], by rw [hm, h.y]⟩

/-- Before polynomial `i`. -/
structure PI (s₀ : State) (i : Nat) (s : State) : Prop extends VG.Proof.MlDsa.X86.Pack.Hint.Pk.Base s₀ s where
  esi : s.gpr .esi = arg s₀ 0 + BitVec.ofNat 32 (4 * (256 * i))
  eax : s.gpr .eax = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Pk.S s₀ i).2
  edi : s.gpr .edi = arg s₀ 3
  ecx : s.gpr .ecx = arg s₀ 3 + BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.ω s₀ + i)
  ebp : s.gpr .ebp = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Pk.K s₀ - i)
  y : bytesAt s.mem (VG.Proof.MlDsa.X86.Pack.Hint.wA s₀) (VG.Proof.MlDsa.X86.Pack.Hint.Pk.yL s₀) = (VG.Proof.MlDsa.X86.Pack.Hint.Pk.S s₀ i).1.toList

theorem setup_piece : Piece VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pre VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pub (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Pk.ZI s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Pk.yL s₀) s) (VG.Proof.MlDsa.X86.Pack.Hint.Pk.PI · 0) (.block hbpSetup) := by
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) (by taint_decide)
  · have a0 : addr (s.gpr .esp) 20 = argAddr s₀ 0 := VG.Proof.MlDsa.X86.Pack.Hint.argEa h.esp 0
    have a2 : addr (s.gpr .esp) 28 = argAddr s₀ 2 := VG.Proof.MlDsa.X86.Pack.Hint.argEa h.esp 2
    have a3 : addr (s.gpr .esp) 32 = argAddr s₀ 3 := VG.Proof.MlDsa.X86.Pack.Hint.argEa h.esp 3
    have a4 : addr (s.gpr .esp) 36 = argAddr s₀ 4 := VG.Proof.MlDsa.X86.Pack.Hint.argEa h.esp 4
    have i0 := h.argIn hp (i := 0) (by omega)
    have i2 := h.argIn hp (i := 2) (by omega)
    have i3 := h.argIn hp (i := 3) (by omega)
    have i4 := h.argIn hp (i := 4) (by omega)
    have v0 := h.argw hp (i := 0) (by omega)
    have v2 := h.argw hp (i := 2) (by omega)
    have v3 := h.argw hp (i := 3) (by omega)
    have v4 := h.argw hp (i := 4) (by omega)
    have hb : WP isa (.block hbpSetup) s fun s' => s'.gpr .esi = arg s₀ 0 ∧ s'.gpr .edi = arg s₀ 3 ∧
        s'.gpr .ecx = arg s₀ 3 + arg s₀ 2 ∧ s'.gpr .ebp = arg s₀ 4 - arg s₀ 2 ∧ s'.mem = s.mem := by
      hrun [hbpSetup, a0, a2, a3, a4, i0, i2, i3, i4, v0, v2, v3, v4]
    have hf := hp.facts
    have l2 := (arg s₀ 2).isLt
    have l4 := (arg s₀ 4).isLt
    refine (WP.keep [.esi, .edi, .ecx, .ebp] hb (by decide)).mono fun s' ⟨⟨e0, e3, ec, eb, m⟩, k⟩ =>
      ⟨h.keep k (by decide) (by rw [m]; exact Frame.refl _ _), by rw [e0]; simp, ?_, e3, ?_, ?_, ?_⟩
    · rw [k.gpr (by decide), h.eax]; rfl
    · rw [ec]; simp
    · rw [eb]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
      simp only [VG.Proof.MlDsa.X86.Pack.Hint.Pk.K, VG.Proof.MlDsa.X86.Pack.Hint.Pk.yL, VG.Proof.MlDsa.X86.Pack.Hint.ω] at hf ⊢
      omega
    · rw [m]
      refine bytesAt_eq (by simp [VG.Proof.MlDsa.X86.Pack.Hint.Pk.S, hpS_zero]; omega) fun u hu => ?_
      rw [h.zero u hu]
      simp [VG.Proof.MlDsa.X86.Pack.Hint.Pk.S, hpS_zero]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, P0_esp, P0_esp, hq.e0]

theorem b0_piece (i : Nat) : Piece VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pre VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pub (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Pk.PI s₀ i s ∧ i < VG.Proof.MlDsa.X86.Pack.Hint.Pk.K s₀) (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Pk.CI s₀ i 0 0 s)
    (.block [.mov .ebx (.imm 0)]) := by
  refine Piece.taint [] (fun s₀ s hp ⟨h, hi⟩ => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  have hb : WP isa (.block [.mov .ebx (.imm 0)]) s fun s' => s'.gpr .ebx = 0 ∧ s'.mem = s.mem := by hrun
  exact (WP.keep [.ebx] hb (by decide)).mono fun s' ⟨⟨e, m⟩, k⟩ =>
    ⟨h.keep k (by decide) (by rw [m]; exact Frame.refl _ _), hi, by rw [k.gpr (by decide), h.esi]; rfl, by rw [e]; rfl,
      by rw [k.gpr (by decide), h.eax, VG.Proof.MlDsa.X86.Pack.Hint.Pk.T, hpT_zero], by rw [k.gpr (by decide), h.edi], by rw [k.gpr (by decide), h.ecx],
      by rw [k.gpr (by decide), h.ebp], by rw [m, h.y, VG.Proof.MlDsa.X86.Pack.Hint.Pk.T, hpT_zero]⟩

theorem ne_zero_eq (v : BitVec 32) : (!(v == 0)) = decide (v ≠ 0) := by
  by_cases hv : v = 0 <;> simp [hv, Bool.beq_eq_decide_eq]

theorem load_piece (i j : Nat) : Piece VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pre VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pub (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Pk.CI s₀ i j j s ∧ j < 256)
    (fun s₀ s => (VG.Proof.MlDsa.X86.Pack.Hint.Pk.CI s₀ i j j s ∧ j < 256) ∧ isa.eval .ne s = some (VG.Proof.MlDsa.X86.Pack.Hint.Pk.bit s₀ i j)) (.block hbpLoad) := by
  refine Piece.taint [.esi] (fun s₀ s hp ⟨h, hj⟩ => ?_) (fun s₀ s₀' s s' _ _ hq ⟨h, _⟩ ⟨h', _⟩ r hr => ?_)
    (by taint_decide)
  · have hf := hp.facts
    have ht : 256 * i + j < 256 * VG.Proof.MlDsa.X86.Pack.Hint.Pk.K s₀ := by have := h.lt; omega
    have ea : addr (s.gpr .esi) 0 = coeffAddr (VG.Proof.MlDsa.X86.Pack.Hint.rA s₀) (256 * i + j) := by rw [h.esi]; exact VG.Proof.MlDsa.X86.Pack.Hint.Pk.hAddr hp ht
    have hin := h.inH hp ht
    have hb : WP isa (.block hbpLoad) s fun s' =>
        s'.zf = some (s.mem.readW (coeffAddr (VG.Proof.MlDsa.X86.Pack.Hint.rA s₀) (256 * i + j)) 32 == 0) ∧ s'.mem = s.mem := by
      hrun [hbpLoad, ea, hin]
    refine (WP.keep [.edx] hb (by decide)).mono fun s' ⟨⟨z, m⟩, k⟩ => ⟨⟨h.edx k m, hj⟩, ?_⟩
    show s'.zf.map (!·) = _
    rw [z, ← coeffAt_eq, h.word hp ht, VG.Proof.MlDsa.X86.Pack.Hint.Pk.bit_eq h.lt hj]
    simp only [Option.map_some, VG.Proof.MlDsa.X86.Pack.Hint.Pk.ne_zero_eq]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esi, h'.esi, hq.a0]

theorem set_piece (i j : Nat) : Piece VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pre VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pub (fun s₀ s => ((VG.Proof.MlDsa.X86.Pack.Hint.Pk.CI s₀ i j j s ∧ j < 256) ∧
      isa.eval .ne s = some (VG.Proof.MlDsa.X86.Pack.Hint.Pk.bit s₀ i j)) ∧ VG.Proof.MlDsa.X86.Pack.Hint.Pk.bit s₀ i j = true) (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Pk.CI s₀ i j (j + 1) s ∧ j < 256)
    (.block hbpSet) := by
  refine Piece.taint [.edi, .eax] (fun s₀ s hp ⟨⟨⟨h, hj⟩, _⟩, h1⟩ => ?_)
    (fun s₀ s₀' s s' _ _ hq ⟨⟨⟨h, _⟩, _⟩, _⟩ ⟨⟨⟨h', _⟩, _⟩, _⟩ r hr => ?_) (by taint_decide)
  · have hf := hp.facts
    have hw := hp.w_fit
    have hlt : (VG.Proof.MlDsa.X86.Pack.Hint.Pk.T s₀ i j).2 < VG.Proof.MlDsa.X86.Pack.Hint.ω s₀ :=
      hpT_idx_lt (hintAt_length _ _ _) hp.ones h.lt (show j < n from hj) h1
    have ea : addr (s.gpr .edi + s.gpr .eax) 0 = VG.Proof.MlDsa.X86.Pack.Hint.wA s₀ + BitVec.ofNat 64 (VG.Proof.MlDsa.X86.Pack.Hint.Pk.T s₀ i j).2 := by
      rw [h.edi, h.eax]; exact VG.Proof.MlDsa.X86.Pack.Hint.Pk.yAddr hp (by omega)
    have hin := h.inY hp (t := (VG.Proof.MlDsa.X86.Pack.Hint.Pk.T s₀ i j).2) (by omega)
    have hb : WP isa (.block hbpSet) s fun s' => s'.gpr .eax = s.gpr .eax + 1 ∧
        s'.mem = s.mem.writeW (VG.Proof.MlDsa.X86.Pack.Hint.wA s₀ + BitVec.ofNat 64 (VG.Proof.MlDsa.X86.Pack.Hint.Pk.T s₀ i j).2) (BitVec.setWidth 8 (s.gpr .ebx)) := by
      hrun [hbpSet, ea, hin]
    have hT : VG.Proof.MlDsa.X86.Pack.Hint.Pk.T s₀ i (j + 1) = ((VG.Proof.MlDsa.X86.Pack.Hint.Pk.T s₀ i j).1.set! (VG.Proof.MlDsa.X86.Pack.Hint.Pk.T s₀ i j).2 (BitVec.ofNat 8 j), (VG.Proof.MlDsa.X86.Pack.Hint.Pk.T s₀ i j).2 + 1) := by
      show hpT _ _ _ i (j + 1) = _
      have h1' : ((VG.Proof.MlDsa.X86.Pack.Hint.Pk.H s₀).getD i noHint)[j]! = true := h1
      rw [hpT_succ, hpStep, h1']; rfl
    refine (WP.keep [.edx, .eax] hb (by decide)).mono fun s' ⟨⟨ea', m⟩, k⟩ => ⟨⟨h.keep k (by decide) ?_, h.lt,
      by rw [k.gpr (by decide), h.esi], by rw [k.gpr (by decide), h.ebx], ?_, by rw [k.gpr (by decide), h.edi],
      by rw [k.gpr (by decide), h.ecx], by rw [k.gpr (by decide), h.ebp], ?_⟩, hj⟩
    · rw [m]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · rw [ea', h.eax, hT, VG.Proof.MlDsa.X86.Pack.Hint.ofNat_add_one]
    · rw [m, bytesAt_writeW8 _ _ (by omega) (by omega), h.y, hT, h.ebx, VG.Proof.MlDsa.X86.Pack.Hint.b8_eq, toNat_ofNat32 (by omega),
        Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h.edi, h'.edi, hq.a3]
    · rw [h.eax, h'.eax, hq.eT]

theorem skip_piece (i j : Nat) : Piece VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pre VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pub (fun s₀ s => ((VG.Proof.MlDsa.X86.Pack.Hint.Pk.CI s₀ i j j s ∧ j < 256) ∧
      isa.eval .ne s = some (VG.Proof.MlDsa.X86.Pack.Hint.Pk.bit s₀ i j)) ∧ VG.Proof.MlDsa.X86.Pack.Hint.Pk.bit s₀ i j = false) (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Pk.CI s₀ i j (j + 1) s ∧ j < 256)
    (.block []) :=
  VG.Proof.MlDsa.X86.Pack.Hint.nil_piece fun s₀ s _ ⟨⟨⟨h, hj⟩, _⟩, h0⟩ => by
    have hT : VG.Proof.MlDsa.X86.Pack.Hint.Pk.T s₀ i (j + 1) = VG.Proof.MlDsa.X86.Pack.Hint.Pk.T s₀ i j := by
      show hpT _ _ _ i (j + 1) = _
      have h0' : ((VG.Proof.MlDsa.X86.Pack.Hint.Pk.H s₀).getD i noHint)[j]! = false := h0
      rw [hpT_succ, hpStep, h0']; rfl
    exact ⟨⟨h.toBase, h.lt, h.esi, h.ebx, by rw [hT]; exact h.eax, h.edi, h.ecx, h.ebp, by rw [hT]; exact h.y⟩, hj⟩

theorem cmp256 {j : Nat} (hj : j < 256) :
    (BitVec.ofNat 32 (j + 1) - 256 == 0) = decide (j + 1 = 256) := by
  rw [sub_beq_zero, toNat_ofNat32 (by omega)]; rfl

theorem next_piece (i j : Nat) : Piece VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pre VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pub (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Pk.CI s₀ i j (j + 1) s ∧ j < 256)
    (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Pk.CI s₀ i (j + 1) (j + 1) s ∧ isa.eval .ne s = some (decide (j + 1 < 256))) (.block hbpNext) := by
  refine Piece.taint [] (fun s₀ s hp ⟨h, hj⟩ => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  have hb : WP isa (.block hbpNext) s fun s' => s'.gpr .esi = s.gpr .esi + 4 ∧ s'.gpr .ebx = s.gpr .ebx + 1 ∧
      s'.zf = some (s.gpr .ebx + 1 - 256 == 0) ∧ s'.mem = s.mem := by hrun [hbpNext]
  refine (WP.keep [.esi, .ebx] hb (by decide)).mono fun s' ⟨⟨e1, e2, z, m⟩, k⟩ =>
    ⟨⟨h.keep k (by decide) (by rw [m]; exact Frame.refl _ _), h.lt, ?_, by rw [e2, h.ebx, VG.Proof.MlDsa.X86.Pack.Hint.ofNat_add_one],
      by rw [k.gpr (by decide), h.eax], by rw [k.gpr (by decide), h.edi], by rw [k.gpr (by decide), h.ecx],
      by rw [k.gpr (by decide), h.ebp], by rw [m, h.y]⟩, ?_⟩
  · rw [e1, h.esi, VG.Proof.MlDsa.X86.Pack.Hint.add_four']; congr 2
  · show s'.zf.map (!·) = _
    rw [z, h.ebx, VG.Proof.MlDsa.X86.Pack.Hint.ofNat_add_one, VG.Proof.MlDsa.X86.Pack.Hint.Pk.cmp256 hj]
    by_cases e : j + 1 = 256
    · simp [e]
    · simp only [e, decide_false, Option.map_some, Bool.not_false, Option.some.injEq]
      exact (decide_eq_true (by omega)).symm

theorem coef_piece (i j : Nat) : Piece VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pre VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pub (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Pk.CI s₀ i j j s ∧ j < 256)
    (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Pk.CI s₀ i (j + 1) (j + 1) s ∧ isa.eval .ne s = some (decide (j + 1 < 256))) hbpCoef :=
  Piece.seq (VG.Proof.MlDsa.X86.Pack.Hint.Pk.load_piece i j) <| Piece.seq (Piece.ite (fun s₀ => VG.Proof.MlDsa.X86.Pack.Hint.Pk.bit s₀ i j) (fun _ _ _ h => h.2)
    (fun s₀ s₀' _ _ hq => by show ((VG.Proof.MlDsa.X86.Pack.Hint.Pk.H s₀).getD i noHint)[j]! = ((VG.Proof.MlDsa.X86.Pack.Hint.Pk.H s₀').getD i noHint)[j]!; rw [hq.h])
    (VG.Proof.MlDsa.X86.Pack.Hint.Pk.set_piece i j) (VG.Proof.MlDsa.X86.Pack.Hint.Pk.skip_piece i j)) (VG.Proof.MlDsa.X86.Pack.Hint.Pk.next_piece i j)

theorem end_piece (i : Nat) : Piece VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pre VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pub (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Pk.CI s₀ i 256 256 s)
    (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Pk.PI s₀ (i + 1) s ∧ isa.eval .ne s = some (decide (i + 1 < VG.Proof.MlDsa.X86.Pack.Hint.Pk.K s₀))) (.block hbpEnd) := by
  refine Piece.taint [.ecx] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) (by taint_decide)
  · have hf := hp.facts
    have hw := hp.w_fit
    have hi := h.lt
    have ea : addr (s.gpr .ecx) 0 = VG.Proof.MlDsa.X86.Pack.Hint.wA s₀ + BitVec.ofNat 64 (VG.Proof.MlDsa.X86.Pack.Hint.ω s₀ + i) := by rw [h.ecx]; exact VG.Proof.MlDsa.X86.Pack.Hint.Pk.yAddr hp (by omega)
    have hin := h.inY hp (t := VG.Proof.MlDsa.X86.Pack.Hint.ω s₀ + i) (by omega)
    have hb : WP isa (.block hbpEnd) s fun s' => s'.gpr .ecx = s.gpr .ecx + 1 ∧ s'.gpr .ebp = s.gpr .ebp - 1 ∧
        s'.zf = some (s.gpr .ebp - 1 == 0) ∧
        s'.mem = s.mem.writeW (VG.Proof.MlDsa.X86.Pack.Hint.wA s₀ + BitVec.ofNat 64 (VG.Proof.MlDsa.X86.Pack.Hint.ω s₀ + i)) (BitVec.setWidth 8 (s.gpr .eax)) := by
      hrun [hbpEnd, ea, hin]
    have hle : (VG.Proof.MlDsa.X86.Pack.Hint.Pk.T s₀ i 256).2 ≤ VG.Proof.MlDsa.X86.Pack.Hint.ω s₀ := hpT_idx_le (hintAt_length _ _ _) hp.ones hi
    have hS : VG.Proof.MlDsa.X86.Pack.Hint.Pk.S s₀ (i + 1) = ((VG.Proof.MlDsa.X86.Pack.Hint.Pk.T s₀ i n).1.set! (VG.Proof.MlDsa.X86.Pack.Hint.ω s₀ + i) (BitVec.ofNat 8 (VG.Proof.MlDsa.X86.Pack.Hint.Pk.T s₀ i n).2), (VG.Proof.MlDsa.X86.Pack.Hint.Pk.T s₀ i n).2) :=
      hpS_succ _ _ _ i
    refine (WP.keep [.ecx, .ebp] hb (by decide)).mono fun s' ⟨⟨e1, e2, z, m⟩, k⟩ =>
      ⟨⟨h.keep k (by decide) ?_, ?_, ?_, by rw [k.gpr (by decide), h.edi], ?_, ?_, ?_⟩,
        VG.Proof.MlDsa.X86.Pack.Hint.eval_ne_cnt hi (by omega) (by rw [z, h.ebp])⟩
    · rw [m]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · rw [k.gpr (by decide), h.esi]; congr 2
    · rw [k.gpr (by decide), h.eax, hS]
    · rw [e1, h.ecx, VG.Proof.MlDsa.X86.Pack.Hint.add_one']; rfl
    · rw [e2, h.ebp]; exact cnt_next hi
    · rw [m, bytesAt_writeW8 _ _ (by omega) (by omega), h.y, hS, h.eax, VG.Proof.MlDsa.X86.Pack.Hint.b8_eq, toNat_ofNat32 (by omega),
        Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.ecx, h'.ecx, hq.a3, hq.eω]

theorem poly_piece (i : Nat) : Piece VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pre VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pub (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Pk.PI s₀ i s ∧ i < VG.Proof.MlDsa.X86.Pack.Hint.Pk.K s₀)
    (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Pk.PI s₀ (i + 1) s ∧ isa.eval .ne s = some (decide (i + 1 < VG.Proof.MlDsa.X86.Pack.Hint.Pk.K s₀))) hbpPoly :=
  Piece.seq (VG.Proof.MlDsa.X86.Pack.Hint.Pk.b0_piece i) <| Piece.seq (VG.Proof.MlDsa.X86.Pack.Hint.loopN (fun j s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Pk.CI s₀ i j j s) (fun _ => 256) (fun _ _ => by decide)
    (fun _ _ _ _ _ => rfl) (VG.Proof.MlDsa.X86.Pack.Hint.Pk.coef_piece i)) (VG.Proof.MlDsa.X86.Pack.Hint.Pk.end_piece i)

theorem main_piece : Piece VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pre VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pub (VG.Proof.MlDsa.X86.Pack.Hint.Pk.PI · 0) (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Pk.PI s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Pk.K s₀) s) (.loop hbpPoly .ne) :=
  VG.Proof.MlDsa.X86.Pack.Hint.loopN (fun i s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Pk.PI s₀ i s) VG.Proof.MlDsa.X86.Pack.Hint.Pk.K (fun s₀ hp => by have := hp.facts; omega) (fun _ _ _ _ hq => hq.eK)
    VG.Proof.MlDsa.X86.Pack.Hint.Pk.poly_piece

/-! ## The function -/

theorem body_piece : Piece VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pre VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pub (fun s₀ s => s = P0 s₀)
    (fun s₀ s => LeafEnd s₀ [VG.Proof.MlDsa.X86.Pack.Hint.Pk.yR s₀] s ∧ VG.Proof.MlDsa.X86.Pack.Hint.Pk.PI s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Pk.K s₀) s)
    (.seq (.block hbpZeroInit) (.seq (.loop (.block hbpZeroBody) .ne) (.seq (.block hbpSetup) (.loop hbpPoly .ne)))) :=
  (Piece.seq VG.Proof.MlDsa.X86.Pack.Hint.Pk.zinit_piece <| Piece.seq VG.Proof.MlDsa.X86.Pack.Hint.Pk.zloop_piece <| Piece.seq VG.Proof.MlDsa.X86.Pack.Hint.Pk.setup_piece VG.Proof.MlDsa.X86.Pack.Hint.Pk.main_piece).mono (fun _ _ _ h => h)
    fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩

theorem piece : Piece VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pre VG.Proof.MlDsa.X86.Pack.Hint.Pk.Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (VG.Proof.MlDsa.X86.Pack.Hint.Pk.PI s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Pk.K s₀)) s₀ s')
    Impl.MlDsa.X86.Pack.hintBitPack :=
  Piece.leaf (fun s₀ => [VG.Proof.MlDsa.X86.Pack.Hint.Pk.yR s₀]) (NoSp.of_all (by decide +kernel))
    (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩) (fun _ hp => hp.wW) (fun _ _ _ _ hq => hq.e0) VG.Proof.MlDsa.X86.Pack.Hint.Pk.body_piece

end Pk

/-- Memory with the arguments `0`, `1024`, `80`, `0x2000` and `84` at `0x5004`. -/
def packSatMem : Mem := fun a =>
  if a = 0x5009 then 4 else if a = 0x500c then 80 else if a = 0x5011 then 0x20 else if a = 0x5014 then 84 else 0

theorem packSat_hint : ∀ t < 256 * 4, coeffAt VG.Proof.MlDsa.X86.Pack.Hint.packSatMem 0 t = 0 := by
  intro t ht
  rw [coeffAt_eq, Mem.readW_congr (m' := fun _ => 0) fun i hi => ?_, ← coeffAt_eq, coeffAt_zero]
  have hlt : (coeffAddr 0 t + BitVec.ofNat 64 i).toNat < 0x1000 := by
    show (0 + BitVec.ofNat 64 (4 * t) + BitVec.ofNat 64 i).toNat < 0x1000
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show BitVec.toNat (0 : Addr) = 0 from rfl]
    omega
  generalize coeffAddr 0 t + BitVec.ofNat 64 i = a at hlt
  simp only [VG.Proof.MlDsa.X86.Pack.Hint.packSatMem]
  split_ifs with h1 h2 h3 h4 <;> first
    | rfl
    | (subst_vars; exact absurd hlt (by decide))

theorem hintBitPack_verified :
    Verified X86.target Impl.MlDsa.X86.Pack.hintBitPack (hintBitPackContract X86.abi 16) := by
  refine Piece.verified ((Pk.piece.pre_mono (fun _ h => Pk.Pre.of h)
    fun s s' h _ hq => Pk.Pub.of (Pk.Pre.of h) hq).mono (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [hintBitPackContract, hintBitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm]
    exact hinv.y.trans (hintBitPack_hpS _ _ _).symm
  · let st := satState VG.Proof.MlDsa.X86.Pack.Hint.packSatMem [⟨0, 4096⟩] [⟨0x2000, 84⟩, ⟨0x5004, 20⟩]
    have a0 : arg st 0 = 0 := by decide
    have a1 : arg st 1 = 1024 := by decide
    have a2 : arg st 2 = 80 := by decide
    have a3 : arg st 3 = 0x2000 := by decide
    have a4 : arg st 4 = 84 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [hintBitPackContract, hintBitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, a3, a4, e]
    refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide,
      by decide, by decide, ?_⟩
    all_goals first
      | exact Region.disjoint_of_sep (by decide)
      | (rw [hintOnes_of_zero fun t ht => by
          rw [show BitVec.setWidth 64 (0 : BitVec 32) = 0 from rfl]
          exact VG.Proof.MlDsa.X86.Pack.Hint.packSat_hint t (by simp at ht; omega)]
         exact Nat.zero_le _)

end VG.Proof.MlDsa.X86.Pack.Hint

end
