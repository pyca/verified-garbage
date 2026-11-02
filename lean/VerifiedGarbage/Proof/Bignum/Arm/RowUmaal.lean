module

public import VerifiedGarbage.Impl.Bignum.Arm.RowUmaal
import VerifiedGarbage.Proof.Bignum.Arm.Row
public import VerifiedGarbage.Proof.Framework.Subst
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Bignum.Arm.Mac
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.RowStep
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# `rowU` runs as `row` does

Every run of `row` is one of `rowU`, with the same trace and final state
(`row_sim`): from the pair loop's entry, every iteration of `rowU`'s loop
ends in a state from which `rowUEnd` gives the state the iteration of
`row`'s ends in (`body_sim`), so `rowLoopU` ends where `rowLoop2` does. The
proofs of the code built on `row` are then proofs of it built on `rowU`
(`Verified.subst`).
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (mask16 toNat_shr toNat_and_mask16 toNat_mul_lt)

/-! ## States equal but for their flags -/

/-- Two states equal but for their flags. -/
structure NoFlags (a b : State) : Prop where
  gpr : a.gpr = b.gpr
  sp : a.sp = b.sp
  mem : a.mem = b.mem
  rd : a.rd = b.rd
  wr : a.wr = b.wr
  unknowns : a.unknowns = b.unknowns
  syms : a.syms = b.syms

theorem NoFlags.refl (a : State) : NoFlags a a := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem NoFlags.symm {a b : State} (h : NoFlags a b) : NoFlags b a :=
  ⟨h.gpr.symm, h.sp.symm, h.mem.symm, h.rd.symm, h.wr.symm, h.unknowns.symm, h.syms.symm⟩

theorem NoFlags.trans {a b c : State} (h : NoFlags a b) (h' : NoFlags b c) : NoFlags a c :=
  ⟨h.gpr.trans h'.gpr, h.sp.trans h'.sp, h.mem.trans h'.mem, h.rd.trans h'.rd, h.wr.trans h'.wr,
    h.unknowns.trans h'.unknowns, h.syms.trans h'.syms⟩

theorem NoFlags.eq {a b : State} (h : NoFlags a b) (hn : a.n = b.n) (hz : a.z = b.z) (hc : a.c = b.c)
    (hv : a.v = b.v) : a = b := by
  obtain ⟨g, sp, m, rd, wr, u, sy⟩ := h
  cases a; cases b
  dsimp only at g sp m rd wr u sy hn hz hc hv
  subst g sp m rd wr u sy hn hz hc hv
  rfl

/-- The pair loop's advance sets every flag: it runs alike from states
equal but for their flags. -/
theorem advance_noFlags {a b : State} (h : NoFlags a b) :
    execBlock isa rowAdvance2 a = execBlock isa rowAdvance2 b := by
  obtain ⟨g, sp, m, rd, wr, u, sy⟩ := h
  cases a; cases b
  dsimp only at g sp m rd wr u sy
  subst g sp m rd wr u sy
  rfl

/-! ## Blocks without memory accesses -/

/-- An instruction that accesses no memory. -/
def noMem : Instr → Bool
  | .ldr .. | .str .. | .ldrb .. | .strb .. | .ldrSp .. | .push _ | .pop .. => false
  | _ => true

theorem addrs_noMem {i : Instr} (h : noMem i = true) (s : State) : addrs i s = [] := by
  cases i <;> simp_all [noMem, addrs]

theorem execBlock_noMem {is : List Instr} (h : is.all noMem = true) {s s' : State}
    {t : List Leak} (he : execBlock isa is s = some (s', t)) : t = [] := by
  induction is generalizing s s' t with
  | nil => simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at he; exact he.2.symm
  | cons i is ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [execBlock] at he
    split at he
    · cases he
    · rename_i s₁ _
      simp only [Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at he
      obtain ⟨s₂, t₂, h₂, -, rfl⟩ := he
      rw [ih h.2 h₂, addrs_noMem h.1 s]
      rfl

/-! ## Loads and stores -/

theorem ldr_block {t n : Reg} {k : Nat} (hk : k < 4096) {s s₁ : State} {tr : List Leak}
    (h : Exec isa (.block [.ldr t n k]) s tr s₁) :
    InRegions (s.rd ++ s.wr) (State.addr (s.gpr n + BitVec.ofNat 32 k)) 4 ∧
      s₁ = s.setReg t (s.mem.readW (State.addr (s.gpr n + BitVec.ofNat 32 k)) 32) ∧
      tr = [.addr (State.addr (s.gpr n + BitVec.ofNat 32 k))] := by
  have h := Exec.block_iff.mp h
  by_cases hr : InRegions (s.rd ++ s.wr) (State.addr (s.gpr n + BitVec.ofNat 32 k)) 4
  · simp only [execBlock, isa, exec, hk, ↓reduceIte, State.load32, hr, Option.map_some, addrs,
      Option.some.injEq, Prod.mk.injEq, List.map_cons, List.map_nil, List.append_nil] at h
    exact ⟨hr, h.1.symm, h.2.symm⟩
  · simp [execBlock, isa, exec, hk, State.load32, hr] at h

theorem str_block {t n : Reg} {k : Nat} (hk : k < 4096) {s s₁ : State} {tr : List Leak}
    (h : Exec isa (.block [.str t n k]) s tr s₁) :
    InRegions s.wr (State.addr (s.gpr n + BitVec.ofNat 32 k)) 4 ∧
      s₁ = { s with mem := s.mem.writeW (State.addr (s.gpr n + BitVec.ofNat 32 k)) (s.gpr t) } ∧
      tr = [.addr (State.addr (s.gpr n + BitVec.ofNat 32 k))] := by
  have h := Exec.block_iff.mp h
  by_cases hr : InRegions s.wr (State.addr (s.gpr n + BitVec.ofNat 32 k)) 4
  · simp only [execBlock, isa, exec, hk, ↓reduceIte, State.store32, hr, Option.map_some, addrs,
      Option.some.injEq, Prod.mk.injEq, List.map_cons, List.map_nil, List.append_nil] at h
    exact ⟨hr, h.1.symm, h.2.symm⟩
  · simp [execBlock, isa, exec, hk, State.store32, hr] at h

/-! ## A step of `row` -/

/-- The input and accumulator words of a step at `k`. -/
def inW (k : Nat) (s : State) : BitVec 32 := s.mem.readW (State.addr (s.gpr .r12 + BitVec.ofNat 32 k)) 32
def accW (k : Nat) (s : State) : BitVec 32 := s.mem.readW (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) 32

/-- The sum a step at `k` with the scalar `x` computes: `y x + c + a`. -/
def stepSum (k : Nat) (x : BitVec 32) (s : State) : Nat :=
  (inW k s).toNat * x.toNat + (s.gpr .r11).toNat + (accW k s).toNat

/-- The state `row`'s step at `k` ends in, but for its flags: the sum's low
word stored and in `r3`, its high word in `r11`, the accumulator word in
`r5`, the high word of `y x + a` in `r4`, the input word's halves in `r2`
and `r6`, and `x₀ y₁` in `r7`. -/
def stepOld (k : Nat) (x : BitVec 32) (s : State) : State :=
  { (((((((s.setReg .r2 (inW k s &&& mask16)).setReg .r6 (inW k s >>> 16)).setReg .r7
      ((x &&& mask16) * (inW k s >>> 16))).setReg .r5 (accW k s)).setReg .r4
      (BitVec.ofNat 32 (((inW k s).toNat * x.toNat + (0 : BitVec 32).toNat + (accW k s).toNat) / 2 ^ 32))).setReg
      .r3 (BitVec.ofNat 32 (stepSum k x s))).setReg .r11 (BitVec.ofNat 32 (stepSum k x s / 2 ^ 32))) with
    mem := s.mem.writeW (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) (BitVec.ofNat 32 (stepSum k x s)) }

theorem stepOld_noFlags {k : Nat} {x : BitVec 32} {a b : State} (h : NoFlags a b) :
    NoFlags (stepOld k x a) (stepOld k x b) := by
  obtain ⟨g, sp, m, rd, wr, u, sy⟩ := h
  refine ⟨?_, sp, ?_, rd, wr, u, sy⟩
  · simp only [stepOld, stepSum, inW, accW, State.setReg, g, m]
  · simp only [stepOld, stepSum, inW, accW, State.setReg, g, m]

/-- The registers `rowProduct` leaves besides the product. -/
theorem rowProduct_regs (s : State) :
    WP isa (.block rowProduct) s fun t =>
      t.gpr .r2 = s.gpr .r2 &&& s.gpr .r9 ∧ t.gpr .r6 = s.gpr .r2 >>> 16 ∧
      t.gpr .r7 = s.gpr .r1 * (s.gpr .r2 >>> 16) := by
  rw [rowProduct, List.append_assoc, List.append_assoc]
  apply WP.block_append_iff.mpr
  refine WP.mono (rowHalves_ok s) ?_
  rintro s1 ⟨b1, b0, frame1⟩
  apply WP.block_append_iff.mpr
  refine WP.mono (rowPartials_ok s1) ?_
  rintro s2 ⟨-, -, p01, -, frame2⟩
  apply WP.of_runBlock
  simp only [addCross, List.cons_append, List.nil_append, runBlock_cons, runStep_some, isa, exec,
    Op2.eval, show (1 ≤ 16 ∧ 16 ≤ 31) = True by decide, ↓reduceIte, Option.map_some, runBlock_nil]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ↓reduceIte]
    change s2.gpr .r2 = _
    rw [frame2.regs .r2 (by decide), b0]
  · simp only [gpr_setReg, reduceCtorEq, ↓reduceIte]
    change s2.gpr .r6 = _
    rw [frame2.regs .r6 (by decide), b1]
  · simp only [gpr_setReg, reduceCtorEq, ↓reduceIte]
    change s2.gpr .r7 = _
    rw [p01, frame1.regs .r1 (by decide), b1]

theorem toNat_hi {lo hi : BitVec 32} {v : Nat} (h : lo.toNat + hi.toNat * 2 ^ 32 = v) :
    hi = BitVec.ofNat 32 (v / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  have := lo.isLt
  have := hi.isLt
  rw [BitVec.toNat_ofNat]
  omega

theorem toNat_lo {lo hi : BitVec 32} {v : Nat} (h : lo.toNat + hi.toNat * 2 ^ 32 = v) :
    lo = BitVec.ofNat 32 v := by
  apply BitVec.eq_of_toNat_eq
  have := lo.isLt
  rw [BitVec.toNat_ofNat]
  omega

theorem seq_inv {a b : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa (.seq a b) s t s') :
    ∃ s₁ t₁ t₂, Exec isa a s t₁ s₁ ∧ Exec isa b s₁ t₂ s' ∧ t = t₁ ++ t₂ := by
  cases h with | seq h₁ h₂ => exact ⟨_, _, _, h₁, h₂, rfl⟩

/-- `addWord r5 ++ addCarry`: `r4:r3 += r5`, then `r11:r3 := r4:r3 + r11`. -/
theorem rowMac_ok (s : State)
    (h : (s.gpr .r3).toNat + (s.gpr .r4).toNat * 2 ^ 32 + (s.gpr .r5).toNat + (s.gpr .r11).toNat < 2 ^ 64) :
    WP isa (.block (addWord .r5 ++ addCarry)) s fun t =>
      (∃ lo : BitVec 32, lo.toNat + (t.gpr .r4).toNat * 2 ^ 32 =
        (s.gpr .r3).toNat + (s.gpr .r4).toNat * 2 ^ 32 + (s.gpr .r5).toNat ∧
        (t.gpr .r3).toNat + (t.gpr .r11).toNat * 2 ^ 32 = lo.toNat + (t.gpr .r4).toNat * 2 ^ 32 +
          (s.gpr .r11).toNat) ∧
      MacFrame [.r3, .r4, .r11] s t := by
  apply WP.block_append_iff.mpr
  refine WP.mono (addWord_ok s .r5 (by omega)) ?_
  rintro u ⟨sum, fu⟩
  have c11 : u.gpr .r11 = s.gpr .r11 := fu.regs .r11 (by decide)
  refine WP.mono (addCarry_ok u (by rw [sum, c11]; omega)) ?_
  rintro t ⟨sum', ft⟩
  have r4 : t.gpr .r4 = u.gpr .r4 := ft.regs .r4 (by decide)
  refine ⟨⟨u.gpr .r3, by rw [r4, sum], by rw [sum', r4, c11]⟩, ?_⟩
  exact (fu.mono (by decide)).trans (ft.mono (by decide))

/-- A run of `row`'s step at `k`: its trace, the memory it may access, and
the state it ends in but for its flags. -/
theorem rowStepAt_fwd {k : Nat} (hk : k < 4096) {x : BitVec 32} {s s' : State} {t : List Leak}
    (h1 : s.gpr .r1 = x &&& mask16) (h10 : s.gpr .r10 = x >>> 16) (h9 : s.gpr .r9 = mask16)
    (h : Exec isa (rowStepAt k) s t s') :
    t = [.addr (State.addr (s.gpr .r12 + BitVec.ofNat 32 k)), .addr (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)),
      .addr (State.addr (s.gpr .r0 + BitVec.ofNat 32 k))] ∧
    InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12 + BitVec.ofNat 32 k)) 4 ∧
    InRegions s.wr (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) 4 ∧
    NoFlags s' (stepOld k x s) := by
  unfold rowStepAt at h
  obtain ⟨s₁, t₁, r₁, e₁, h₁, rfl⟩ := seq_inv h
  obtain ⟨s₂, t₂, r₂, e₂, h₂, rfl⟩ := seq_inv h₁
  obtain ⟨s₃, t₃, r₃, e₃, h₃, rfl⟩ := seq_inv h₂
  obtain ⟨s₄, t₄, t₅, e₄, e₅, rfl⟩ := seq_inv h₃
  obtain ⟨hr₁, rfl, rfl⟩ := ldr_block hk e₁
  -- `rowProduct`
  have p1 : (s.setReg .r2 (inW k s)).gpr .r1 = x &&& mask16 := by
    simp only [gpr_setReg, reduceCtorEq, ↓reduceIte]; exact h1
  have p10 : (s.setReg .r2 (inW k s)).gpr .r10 = x >>> 16 := by
    simp only [gpr_setReg, reduceCtorEq, ↓reduceIte]; exact h10
  have p9 : (s.setReg .r2 (inW k s)).gpr .r9 = mask16 := by
    simp only [gpr_setReg, reduceCtorEq, ↓reduceIte]; exact h9
  obtain ⟨_, _, w₂, prod, f₂⟩ := rowProduct_ok _ x p1 p10 p9
  rw [(Exec.det w₂ e₂).2] at prod f₂
  obtain ⟨_, _, w₂', v2, v6, v7⟩ := rowProduct_regs (s.setReg .r2 (inW k s))
  rw [(Exec.det w₂' e₂).2] at v2 v6 v7
  have t₂0 : t₂ = [] := execBlock_noMem (by decide) (Exec.block_iff.mp e₂)
  subst t₂0
  have g0 : s₂.gpr .r0 = s.gpr .r0 := by
    rw [f₂.regs .r0 (by decide)]; simp only [gpr_setReg, reduceCtorEq, ↓reduceIte]
  have m₂ : s₂.mem = s.mem := f₂.mem
  -- the accumulator word
  obtain ⟨hr₃, rfl, rfl⟩ := ldr_block hk e₃
  -- `addWord r5 ++ addCarry`
  let s₃ := s₂.setReg .r5 (s₂.mem.readW (State.addr (s₂.gpr .r0 + BitVec.ofNat 32 k)) 32)
  have a3 : s₃.gpr .r5 = accW k s := by
    simp only [s₃, gpr_setReg, ↓reduceIte, g0, m₂, accW]
  have c3 : s₃.gpr .r11 = s.gpr .r11 := by
    simp only [s₃, gpr_setReg, reduceCtorEq, ↓reduceIte]
    rw [f₂.regs .r11 (by decide)]; simp only [gpr_setReg, reduceCtorEq, ↓reduceIte]
  have p3 : (s₃.gpr .r3).toNat + (s₃.gpr .r4).toNat * 2 ^ 32 = (inW k s).toNat * x.toNat := by
    simp only [s₃, gpr_setReg, reduceCtorEq, ↓reduceIte]
    rw [prod, Nat.mul_comm]; simp only [gpr_setReg, ↓reduceIte]
  have hb := mac_bound (inW k s) x (accW k s) (s.gpr .r11)
  obtain ⟨_, _, w₄, ⟨lo, sumA, sumC⟩, f₄⟩ := rowMac_ok s₃ (by rw [p3, a3, c3]; omega)
  rw [(Exec.det w₄ e₄).2] at sumA sumC f₄
  have t₄0 : t₄ = [] := execBlock_noMem (by decide) (Exec.block_iff.mp e₄)
  subst t₄0
  have g40 : s₄.gpr .r0 = s.gpr .r0 := by
    rw [f₄.regs .r0 (by decide)]; simp only [s₃, gpr_setReg, reduceCtorEq, ↓reduceIte]; exact g0
  obtain ⟨hw₅, rfl, rfl⟩ := str_block hk e₅
  have lo3 : s₄.gpr .r3 = BitVec.ofNat 32 (stepSum k x s) := by
    refine toNat_lo (hi := s₄.gpr .r11) ?_
    rw [sumC, sumA, p3, a3, c3, stepSum]; omega
  have hi11 : s₄.gpr .r11 = BitVec.ofNat 32 (stepSum k x s / 2 ^ 32) := by
    refine toNat_hi (lo := s₄.gpr .r3) ?_
    rw [sumC, sumA, p3, a3, c3, stepSum]; omega
  have hi4 : s₄.gpr .r4 = BitVec.ofNat 32
      (((inW k s).toNat * x.toNat + (0 : BitVec 32).toNat + (accW k s).toNat) / 2 ^ 32) := by
    refine toNat_hi (lo := lo) ?_
    rw [sumA, p3, a3]; simp
  have keep : ∀ r, r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → r ≠ .r11 →
      s₄.gpr r = s.gpr r := by
    intro r h2 h3 h4 h5 h6 h7 h11
    have e4 := f₄.regs r (by simp [h3, h4, h11])
    rw [e4]
    simp only [s₃, gpr_setReg, h5, ↓reduceIte]
    by_cases h8 : r = .r8
    · subst h8
      rw [VG.Arm.Exec.gpr (fun i hi => by revert i hi; decide) e₂]
      simp only [gpr_setReg, reduceCtorEq, ↓reduceIte]
    rw [f₂.regs r (by simp [h2, h3, h4, h5, h6, h7, h8])]
    simp only [gpr_setReg, h2, ↓reduceIte]
  have k5 : s₄.gpr .r5 = accW k s := by rw [f₄.regs _ (by decide)]; exact a3
  have k2 : s₄.gpr .r2 = inW k s &&& mask16 := by
    rw [f₄.regs _ (by decide)]; simp only [s₃, gpr_setReg, reduceCtorEq, ↓reduceIte]
    rw [v2, p9]; simp only [gpr_setReg, ↓reduceIte]
  have k6 : s₄.gpr .r6 = inW k s >>> 16 := by
    rw [f₄.regs _ (by decide)]; simp only [s₃, gpr_setReg, reduceCtorEq, ↓reduceIte]
    rw [v6]; simp only [gpr_setReg, ↓reduceIte]
  have k7 : s₄.gpr .r7 = (x &&& mask16) * (inW k s >>> 16) := by
    rw [f₄.regs _ (by decide)]; simp only [s₃, gpr_setReg, reduceCtorEq, ↓reduceIte]
    rw [v7, p1]; simp only [gpr_setReg, ↓reduceIte]
  have wr₄ : s₄.wr = s.wr := by rw [f₄.wr]; exact f₂.wr
  refine ⟨by simp [g0, g40], hr₁, by rw [g40, wr₄] at hw₅; exact hw₅, ?_⟩
  refine ⟨funext fun r => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change s₄.gpr r = _
    cases r <;> simp only [stepOld, gpr_setReg, reduceCtorEq, ↓reduceIte]
    all_goals first
      | exact keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      | exact lo3
      | exact hi11
      | exact hi4
      | exact k5
      | exact k2
      | exact k6
      | exact k7
  · change s₄.sp = s.sp; rw [f₄.sp]; exact f₂.sp
  · change s₄.mem.writeW _ (s₄.gpr .r3) = _
    simp only [stepOld]
    rw [lo3, g40, f₄.mem]
    change s₂.mem.writeW _ _ = _
    rw [m₂]
  · change s₄.rd = s.rd; rw [f₄.rd]; exact f₂.rd
  · exact wr₄
  · change s₄.unknowns = s.unknowns; rw [f₄.unknowns]; exact f₂.unknowns
  · change s₄.syms = s.syms; rw [f₄.syms]; exact f₂.syms

/-! ## A step of `rowU`, its advance and its end -/

/-- The state `rowStepU k` ends in. -/
def stepNew (k : Nat) (n : State) : State :=
  { ((((n.setReg .r2 (inW k n)).setReg .r3 (accW k n)).setReg .r5 (accW k n)).setReg .r3
      (BitVec.ofNat 32 ((inW k n).toNat * (n.gpr .r9).toNat + (n.gpr .r11).toNat + (accW k n).toNat))).setReg
      .r11 (BitVec.ofNat 32 (((inW k n).toNat * (n.gpr .r9).toNat + (n.gpr .r11).toNat +
        (accW k n).toNat) / 2 ^ 32)) with
    mem := n.mem.writeW (State.addr (n.gpr .r0 + BitVec.ofNat 32 k))
      (BitVec.ofNat 32 ((inW k n).toNat * (n.gpr .r9).toNat + (n.gpr .r11).toNat + (accW k n).toNat)) }

theorem rowStepU_exec {k : Nat} (hk : k < 4096) (n : State)
    (hr : InRegions (n.rd ++ n.wr) (State.addr (n.gpr .r12 + BitVec.ofNat 32 k)) 4)
    (hw : InRegions n.wr (State.addr (n.gpr .r0 + BitVec.ofNat 32 k)) 4) :
    execBlock isa (rowStepU k) n = some (stepNew k n,
      [.addr (State.addr (n.gpr .r12 + BitVec.ofNat 32 k)), .addr (State.addr (n.gpr .r0 + BitVec.ofNat 32 k)),
        .addr (State.addr (n.gpr .r0 + BitVec.ofNat 32 k))]) := by
  have hr0 : InRegions (n.rd ++ n.wr) (State.addr (n.gpr .r0 + BitVec.ofNat 32 k)) 4 := by
    obtain ⟨R, hR, hc⟩ := hw; exact ⟨R, List.mem_append_right _ hR, hc⟩
  simp only [rowStepU, execBlock, isa, exec, hk, ↓reduceIte, State.load32, State.store32, Op2.eval,
    gpr_setReg, reduceCtorEq, rd_setReg, wr_setReg, mem_setReg, hr, hr0, hw, Option.map_some, addrs,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  rfl

/-- The state the pair loop's advance ends in. -/
def advState (s : State) : State :=
  (subFlags ((s.setReg .r0 (s.gpr .r0 + 8)).setReg .r12 (s.gpr .r12 + 8)) (s.gpr .lr) 2).setReg .lr
    (s.gpr .lr - 2)

theorem advState_exec (s : State) : execBlock isa rowAdvance2 s = some (advState s, []) := by
  simp only [rowAdvance2, execBlock, isa, exec, Op2.eval,
    Option.map_some, addrs, List.map_nil, List.append_nil]
  rfl

/-- The state `rowUEnd` ends in. -/
def endState (n : State) : State :=
  let y := n.gpr .r2
  let a := n.gpr .r5
  let v := y.toNat * (n.gpr .r9).toNat + (0 : BitVec 32).toNat + a.toNat
  (((((((n.setReg .r6 a).setReg .r4 0).setReg .r6 (BitVec.ofNat 32 v)).setReg .r4
    (BitVec.ofNat 32 (v / 2 ^ 32))).setReg .r6 (y >>> 16)).setReg .r9 mask16).setReg .r2
    (y &&& mask16)).setReg .r7 (n.gpr .r1 * (y >>> 16))

theorem rowUEnd_exec (n : State) : execBlock isa rowUEnd n = some (endState n, []) := by
  simp only [rowUEnd, execBlock, isa, exec, Op2.eval, gpr_setReg, reduceCtorEq, ↓reduceIte,
    Option.map_some, addrs, List.map_nil, List.append_nil]
  rfl

/-! ## The pair loops -/

/-- A step overwrites the saved accumulator before using it. -/
theorem rowFirstU_exec (n : State)
    (hr : InRegions (n.rd ++ n.wr) (State.addr (n.gpr .r12 + BitVec.ofNat 32 0)) 4)
    (hw : InRegions n.wr (State.addr (n.gpr .r0 + BitVec.ofNat 32 0)) 4) :
    execBlock isa rowFirstU n = some ((stepNew 0 n).setReg .r5 (n.gpr .r5),
      [.addr (State.addr (n.gpr .r12 + BitVec.ofNat 32 0)), .addr (State.addr (n.gpr .r0 + BitVec.ofNat 32 0)),
        .addr (State.addr (n.gpr .r0 + BitVec.ofNat 32 0))]) := by
  have hr0 : InRegions (n.rd ++ n.wr) (State.addr (n.gpr .r0 + BitVec.ofNat 32 0)) 4 := by
    obtain ⟨R, hR, hc⟩ := hw; exact ⟨R, List.mem_append_right _ hR, hc⟩
  simp only [rowFirstU, execBlock, isa, exec,
    show (0 < 4096) = True by decide, ↓reduceIte, State.load32, State.store32,
    gpr_setReg, reduceCtorEq, rd_setReg, wr_setReg, mem_setReg, hr, hr0, hw, Option.map_some, addrs,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  congr 2
  simp only [stepNew, State.setReg]
  congr 1
  funext r
  cases r <;> simp [inW, accW]

theorem stepNew_set5 (k : Nat) (n : State) (v : BitVec 32) :
    stepNew k (n.setReg .r5 v) = stepNew k n := by
  simp only [stepNew, inW, accW, reduceCtorEq, ↓reduceIte, State.setReg]
  congr 1
  funext r
  cases r <;> rfl

/-- `rowU`'s state `n` and `row`'s `o` in its pair loop: equal but in the
registers `row`'s step leaves values in that `rowU` has only once
`rowUEnd` has run, and in the flags. -/
structure Agree (o n : State) : Prop where
  gpr : ∀ r, r ≠ .r2 → r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → r ≠ .r9 → o.gpr r = n.gpr r
  sp : o.sp = n.sp
  mem : o.mem = n.mem
  rd : o.rd = n.rd
  wr : o.wr = n.wr
  unknowns : o.unknowns = n.unknowns
  syms : o.syms = n.syms

theorem agree_endState (n : State) : Agree (endState n) n := by
  refine ⟨fun r h2 h4 h6 h7 h9 => ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp only [endState, gpr_setReg, h2, h4, h6, h7, h9, ↓reduceIte]

/-- One iteration of `rowU`'s pair loop from a state agreeing with `row`'s
ends in a state from which `rowUEnd` gives the one `row`'s ends in. -/
theorem body_sim {o n o' : State} {t : List Leak} {x : BitVec 32} (ag : Agree o n)
    (h1 : o.gpr .r1 = x &&& mask16) (h10 : o.gpr .r10 = x >>> 16) (h9 : o.gpr .r9 = mask16)
    (hx : n.gpr .r9 = x) (h : Exec isa rowBody2 o t o') :
    Exec isa (.block rowBodyU) n t (advState (stepNew 4 (stepNew 0 n))) ∧
      endState (advState (stepNew 4 (stepNew 0 n))) = o' := by
  unfold rowBody2 at h
  obtain ⟨o₁, t₀, r, e₀, h₁, rfl⟩ := seq_inv h
  obtain ⟨o₂, t₄, ta, e₄, ea, rfl⟩ := seq_inv h₁
  obtain ⟨rfl, rd₀, wr₀, nf₀⟩ := rowStepAt_fwd (k := 0) (by decide) h1 h10 h9 e₀
  have g₁ : ∀ r, r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → r ≠ .r11 →
      o₁.gpr r = o.gpr r := by
    intro r h2 h3 h4 h5 h6 h7 h11
    rw [nf₀.gpr]; simp only [stepOld, gpr_setReg, h2, h3, h4, h5, h6, h7, h11, ↓reduceIte]
  obtain ⟨rfl, rd₄, wr₄, nf₄⟩ := rowStepAt_fwd (k := 4) (by decide)
    (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1])
    (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h10])
    (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h9]) e₄
  have ea' := Exec.block_iff.mp ea
  rw [advance_noFlags (nf₄.trans (stepOld_noFlags nf₀)), advState_exec] at ea'
  simp only [Option.some.injEq, Prod.mk.injEq] at ea'
  obtain ⟨rfl, rfl⟩ := ea'
  have r0 : o.gpr .r0 = n.gpr .r0 := ag.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have r12 : o.gpr .r12 = n.gpr .r12 := ag.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have o₁r0 : o₁.gpr .r0 = o.gpr .r0 :=
    g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have o₁r12 : o₁.gpr .r12 = o.gpr .r12 :=
    g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have o₁rd : o₁.rd = o.rd := nf₀.rd
  have o₁wr : o₁.wr = o.wr := nf₀.wr
  have nr0 : InRegions (n.rd ++ n.wr) (State.addr (n.gpr .r12 + 0)) 4 := by
    rw [← r12, ← ag.rd, ← ag.wr]; exact rd₀
  have nw0 : InRegions n.wr (State.addr (n.gpr .r0 + 0)) 4 := by
    rw [← r0, ← ag.wr]; exact wr₀
  have nr4 : InRegions ((stepNew 0 n).rd ++ (stepNew 0 n).wr)
      (State.addr ((stepNew 0 n).gpr .r12 + 4#32)) 4 := by
      simp only [stepNew, gpr_setReg, reduceCtorEq, ↓reduceIte, rd_setReg, wr_setReg]
      rw [← r12, ← ag.rd, ← ag.wr, ← o₁r12, ← o₁rd, ← o₁wr]; exact rd₄
  have nw4 : InRegions (stepNew 0 n).wr
      (State.addr ((stepNew 0 n).gpr .r0 + 4#32)) 4 := by
      simp only [stepNew, gpr_setReg, reduceCtorEq, ↓reduceIte, wr_setReg]
      rw [← r0, ← ag.wr, ← o₁r0, ← o₁wr]; exact wr₄
  have n0 := rowFirstU_exec n nr0 nw0
  have n4 := rowStepU_exec (k := 4) (by decide) ((stepNew 0 n).setReg .r5 (n.gpr .r5))
    (by simpa only [rd_setReg, wr_setReg, gpr_setReg, reduceCtorEq, ↓reduceIte] using nr4)
    (by simpa only [wr_setReg, gpr_setReg, reduceCtorEq, ↓reduceIte] using nw4)
  rw [stepNew_set5] at n4
  refine ⟨Exec.block_iff.mpr ?_, ?_⟩
  · rw [rowBodyU, execBlock_append, execBlock_append, n0]
    simp only [Option.bind_some, n4, Option.map_some, advState_exec]
    simp only [stepNew, gpr_setReg, reduceCtorEq, ↓reduceIte, o₁r0, o₁r12, r0, r12, List.append_nil,
      List.cons_append, List.nil_append]
  · have kept : ∀ r, r ≠ .r2 → r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → r ≠ .r9 → o.gpr r = n.gpr r := ag.gpr
    have r1 := kept .r1 (by decide) (by decide) (by decide) (by decide) (by decide)
    have r8 := kept .r8 (by decide) (by decide) (by decide) (by decide) (by decide)
    have r10 := kept .r10 (by decide) (by decide) (by decide) (by decide) (by decide)
    have r11 := kept .r11 (by decide) (by decide) (by decide) (by decide) (by decide)
    have rlr := kept .lr (by decide) (by decide) (by decide) (by decide) (by decide)
    subst hx
    have hn1 : n.gpr .r1 = n.gpr .r9 &&& mask16 := r1 ▸ h1
    have gs : ∀ (s : State) (a b : BitVec 32), (subFlags s a b).gpr = s.gpr := fun _ _ _ => rfl
    have ms : ∀ (s : State) (a b : BitVec 32), (subFlags s a b).mem = s.mem := fun _ _ _ => rfl
    refine NoFlags.eq ⟨funext fun r => ?_, ag.sp.symm, ?_, ag.rd.symm, ag.wr.symm, ag.unknowns.symm,
      ag.syms.symm⟩ ?_ ?_ ?_ ?_
    · cases r <;> simp only [endState, advState, stepNew, stepOld, stepSum, inW, accW, gs, gpr_setReg,
        reduceCtorEq, ↓reduceIte, ag.mem, r0, r1, r8, r10, r11, r12, rlr, h9, hn1]
    · simp only [endState, advState, stepNew, stepOld, stepSum, inW, accW, ms, mem_setReg, gpr_setReg,
        reduceCtorEq, ↓reduceIte, ag.mem, r0, r11, r12]
    all_goals simp only [endState, advState, subFlags, n_setReg, z_setReg, c_setReg, v_setReg,
      gpr_setReg, reduceCtorEq, ↓reduceIte, stepNew, stepOld, rlr]

theorem body_keeps {n : State} :
    (advState (stepNew 4 (stepNew 0 n))).gpr .r1 = n.gpr .r1 ∧
      (advState (stepNew 4 (stepNew 0 n))).gpr .r10 = n.gpr .r10 ∧
      (advState (stepNew 4 (stepNew 0 n))).gpr .r9 = n.gpr .r9 := by
  simp only [advState, stepNew, subFlags, gpr_setReg, reduceCtorEq, ↓reduceIte, and_self]

/-- `rowU`'s pair loop runs as `row`'s, but for the registers `rowUEnd`
sets as `row`'s steps leave them. -/
theorem loop_sim {x : BitVec 32} {o o' : State} {tr : List Leak}
    (h : Exec isa (.loop rowBody2 .ne) o tr o') :
    ∀ {n : State}, Agree o n → o.gpr .r1 = x &&& mask16 → o.gpr .r10 = x >>> 16 → o.gpr .r9 = mask16 →
      n.gpr .r9 = x → ∃ n', Exec isa (.loop (.block rowBodyU) .ne) n tr n' ∧ endState n' = o' := by
  generalize hc : (Code.loop rowBody2 .ne : Prog isa) = c at h
  induction h with
  | icall | icallNext => cases hc
  | loopExit hb he =>
    cases hc
    intro n ag h1 h10 h9 hx
    obtain ⟨e, rfl⟩ := body_sim ag h1 h10 h9 hx hb
    exact ⟨_, .loopExit e (by simpa [isa, eval, endState, z_setReg] using he), rfl⟩
  | loopNext hb he _ _ ih =>
    cases hc
    intro n ag h1 h10 h9 hx
    obtain ⟨e, rfl⟩ := body_sim ag h1 h10 h9 hx hb
    obtain ⟨k1, k10, k9⟩ := body_keeps (n := n)
    obtain ⟨n', e', rfl⟩ := ih rfl (agree_endState _)
      (by simp only [endState, gpr_setReg, reduceCtorEq, ↓reduceIte]; rw [k1, ← ag.gpr .r1 (by decide)
        (by decide) (by decide) (by decide) (by decide), h1])
      (by simp only [endState, gpr_setReg, reduceCtorEq, ↓reduceIte]; rw [k10, ← ag.gpr .r10 (by decide)
        (by decide) (by decide) (by decide) (by decide), h10])
      (by simp only [endState, gpr_setReg, reduceCtorEq, ↓reduceIte])
      (by rw [k9, hx])
    exact ⟨n', .loopNext e (by simpa [isa, eval, endState, z_setReg] using he) e', rfl⟩
  | block => cases hc
  | seq => cases hc
  | iteT => cases hc
  | iteF => cases hc
  | call => cases hc
  | frame => cases hc

/-! ## The rows -/

/-- `rowLoopU` runs as `rowLoop2`, from a state where the scalar `x` is
split for `row`. -/
theorem rowLoopU_sim {x : BitVec 32} {s s' : State} {t : List Leak}
    (h1 : s.gpr .r1 = x &&& mask16) (h10 : s.gpr .r10 = x >>> 16) (h9 : s.gpr .r9 = mask16)
    (h : Exec isa rowLoop2 s t s') : Exec isa rowLoopU s t s' := by
  let n := s.setReg .r9 (s.gpr .r1 ||| (s.gpr .r10 <<< 16))
  have ej : Exec isa (.block rowUJoin) s [] n := by
    refine Exec.block_iff.mpr ?_
    simp only [rowUJoin, execBlock, isa, exec, Op2.eval, show (1 ≤ 16 ∧ 16 ≤ 31) = True by decide,
      ↓reduceIte, Option.map_some, addrs, List.map_nil, List.append_nil]
    rfl
  have hx : n.gpr .r9 = x := by
    simp only [n, gpr_setReg, ↓reduceIte, h1, h10]; exact join16 x
  have ag : Agree s n := ⟨fun r _ _ _ _ h9' => by simp only [n, gpr_setReg, h9', ↓reduceIte],
    rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨n', e', rfl⟩ := loop_sim h ag h1 h10 h9 hx
  have ee : Exec isa (.block rowUEnd) n' [] (endState n') := Exec.block_iff.mpr (rowUEnd_exec n')
  have := Exec.seq ej (Exec.seq e' ee)
  rwa [List.nil_append, List.append_nil] at this

/-- Every run of `row` is a run of `rowU`, with the same trace and final
state. -/
theorem row_sim : Sim (M := isa) row rowU := by
  intro s t s' h
  unfold row at h
  obtain ⟨s₁, t₁, r₁, e₁, h₁, rfl⟩ := seq_inv h
  obtain ⟨s₂, t₂, r₂, e₂, h₂, rfl⟩ := seq_inv h₁
  obtain ⟨s₃, t₃, r₃, e₃, h₃, rfl⟩ := seq_inv h₂
  obtain ⟨s₄, t₄, t₅, e₄, e₅, rfl⟩ := seq_inv h₃
  have wp : WP isa (.block (rowSplit ++ rowParity)) s fun u =>
      u.gpr .r1 = s.gpr .r1 &&& mask16 ∧ u.gpr .r10 = s.gpr .r1 >>> 16 ∧ u.gpr .r9 = mask16 := by
    apply WP.block_append_iff.mpr
    refine WP.mono (rowSplit_ok s) ?_
    rintro u ⟨a, b, c, -, -⟩
    apply WP.of_runBlock
    simp only [rowParity, runBlock_cons, isa, exec, Op2.eval]
    refine ⟨_, rfl, ?_⟩
    simp only [subFlags, gpr_setReg, reduceCtorEq, ↓reduceIte]
    exact ⟨a, b, c⟩
  obtain ⟨_, _, w, a1, a10, a9⟩ := wp
  rw [(Exec.det w e₁).2] at a1 a10 a9
  have k2 : ∀ r, r = .r1 ∨ r = .r10 ∨ r = .r9 → s₃.gpr r = s₁.gpr r := by
    rintro r hr
    rw [VG.Arm.Exec.gpr (fun i hi => by rcases hr with rfl | rfl | rfl <;> revert i hi <;> decide) e₃,
      VG.Arm.Exec.gpr (fun i hi => by rcases hr with rfl | rfl | rfl <;> revert i hi <;> decide) e₂]
  have E₄ : Exec isa (.ite .ne rowLoopU (.block [])) s₃ t₄ s₄ := by
    cases e₄ with
    | iteT hc e =>
      exact .iteT hc (rowLoopU_sim (by rw [k2 _ (.inl rfl), a1]) (by rw [k2 _ (.inr (.inl rfl)), a10])
        (by rw [k2 _ (.inr (.inr rfl)), a9]) e)
    | iteF hc e => exact .iteF hc e
  exact .seq e₁ (.seq e₂ (.seq e₃ (.seq E₄ e₅)))

/-- Code with `umaal` rows is verified as it is with `row`s. -/
theorem umaalRows_verified {c : Prog isa} {k : Contract isa} (h : Verified Arm.target c k) :
    Verified Arm.target (umaalRows c) k :=
  h.subst row_sim

/-- Rows have no frames: replacing them takes no more stack. -/
theorem armStack_umaalRows (c : Prog isa) :
    FrameStack.armStack (umaalRows c) ≤ FrameStack.armStack c := by
  unfold umaalRows
  induction c with
  | block _ => simp only [Code.subst]; split <;> simp [FrameStack.armStack, rowU, rowLoopU, rowBody, rowStep, rowStepAt]
  | seq a b iha ihb =>
    simp only [Code.subst]; split
    · simp [FrameStack.armStack, rowU, rowLoopU, rowBody, rowStep, rowStepAt]
    · simp only [FrameStack.armStack]; omega
  | ite _ t e iht ihe =>
    simp only [Code.subst]; split
    · simp [FrameStack.armStack, rowU, rowLoopU, rowBody, rowStep, rowStepAt]
    · simp only [FrameStack.armStack]; omega
  | loop b _ ih =>
    simp only [Code.subst]; split
    · simp [FrameStack.armStack, rowU, rowLoopU, rowBody, rowStep, rowStepAt]
    · simpa only [FrameStack.armStack] using ih
  | call _ b ih =>
    simp only [Code.subst]; split
    · simp [FrameStack.armStack, rowU, rowLoopU, rowBody, rowStep, rowStepAt]
    · simpa only [FrameStack.armStack] using ih
  | icall =>
    simp only [Code.subst]; split
    · simp [FrameStack.armStack, rowU, rowLoopU, rowBody, rowStep, rowStepAt]
    · exact Nat.le_refl _
  | frame i b j ih =>
    simp only [Code.subst]; split
    · simp [FrameStack.armStack, rowU, rowLoopU, rowBody, rowStep, rowStepAt]
    · cases i <;> simp only [FrameStack.armStack] <;> omega

end VG.Proof.Bignum.Arm
