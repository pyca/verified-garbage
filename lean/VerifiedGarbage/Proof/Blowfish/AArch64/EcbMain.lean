module

public import VerifiedGarbage.Proof.Blowfish.AArch64.Batch
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Blowfish.AArch64
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics

/-! ### `Blowfish.AArch64.Ecb`, which this module and modules that import it used -/

section

/-! ### `Blowfish.AArch64.Copy`, which this module and modules that import it used -/

section

/-!
# Copying words

`copy_ok`: the loop `copy` copies `n ≥ 1` words from `A` (in `x11`) to `B`
(in `x12`), where the two areas do not overlap, and changes nothing else in
memory. `x13` counts the words left, and `x10` holds each word.
-/

@[expose] public section

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64

/-- Block `i` (8 bytes each) from `p`. -/
abbrev wAt (p : Addr) (i : Nat) : Addr := p + BitVec.ofNat 64 (8 * i)

theorem wAt_wAt (D : Addr) (a i : Nat) : wAt (wAt D a) i = wAt D (a + i) := by
  simp only [wAt, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2; omega_using []

theorem cnt_sub (m : Nat) (h : 1 ≤ m) : BitVec.ofNat 64 m - 1 = BitVec.ofNat 64 (m - 1) := by
  have e : (1 : BitVec 64) = BitVec.ofNat 64 1 := rfl
  rw [e, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) h]

structure CopyPre (A B : Addr) (n : Nat) (s : State) : Prop where
  read : ∀ i < n, InRegions (s.rd ++ s.wr) (wAt A i) 8
  write : ∀ i < n, InRegions s.wr (wAt B i) 8
  sep : (⟨A, 8 * n⟩ : Region).Disjoint ⟨B, 8 * n⟩
  fitA : 8 * n < 2 ^ 64

theorem wAt_succ (p : Addr) (i : Nat) : wAt p i + BitVec.ofNat 64 8 = wAt p (i + 1) := by
  simp only [wAt, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2

/-- The registers the copy changes. -/
def CopyRegs (r : Reg) : Prop := r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13

structure CopyInv (A B : Addr) (n : Nat) (s₀ : State) (i : Nat) (s : State) : Prop where
  le : i < n
  src : s.gpr .x11 = wAt A i
  dst : s.gpr .x12 = wAt B i
  cnt : s.gpr .x13 = BitVec.ofNat 64 (n - i)
  copied : ∀ j < i, s.mem.readW (wAt B j) 64 = s₀.mem.readW (wAt A j) 64
  frame : Frame [⟨B, 8 * n⟩] s₀.mem s.mem
  regs : ∀ r, CopyRegs r → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  v : s.v = s₀.v

structure CopyPost (A B : Addr) (n : Nat) (s₀ s : State) : Prop where
  copied : ∀ j < n, s.mem.readW (wAt B j) 64 = s₀.mem.readW (wAt A j) 64
  frame : Frame [⟨B, 8 * n⟩] s₀.mem s.mem
  regs : ∀ r, CopyRegs r → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  v : s.v = s₀.v

theorem wAt_in {p : Addr} {i n : Nat} (hi : i < n) (hn : 8 * n < 2 ^ 64) :
    (⟨p, 8 * n⟩ : Region).Contains (wAt p i) 8 :=
  Offset.contains_base p (by omega_using [hi]) (by omega_using [hi, hn])

theorem add_ofNat_zero (a : Addr) : a + BitVec.ofNat 64 0 = a := by simp

theorem copy_ok {A B : Addr} {n : Nat} {s₀ : State} (hpre : CopyPre A B n s₀) (s : State) (i : Nat)
    (hs : CopyInv A B n s₀ i s) : WP isa copy s (CopyPost A B n s₀) := by
  refine WP.loop (M := isa) (fun m s => CopyInv A B n s₀ (n - m) s ∧ m ≤ n) ?_ (n - i) s
    ⟨by rw [show n - (n - i) = i by have := hs.le; omega_arith]; exact hs, by omega_arith⟩
  intro m s ⟨inv, hm⟩
  let j := n - m
  have hj : j < n := inv.le
  let v := s₀.mem.readW (wAt A j) 64
  have hv : s.mem.readW (wAt A j) 64 = v :=
    inv.frame.readW (wAt_in hj hpre.fitA) (by simpa using hpre.sep) (by decide)
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .x11 + BitVec.ofNat 64 0) 8 := by
    rw [add_ofNat_zero, inv.src, inv.rd, inv.wr]; exact hpre.read j hj
  let s₁ := s.write .x .x10 v
  have e₁ : exec (.ldr .x .x10 .x11 0) s = some s₁ := by
    rw [exec_ldr_x ⟨by decide, by decide⟩ hr, add_ofNat_zero, inv.src, hv]
  have hw : InRegions s₁.wr (s₁.gpr .x12 + BitVec.ofNat 64 0) 8 := by
    rw [add_ofNat_zero]
    have : (s.write .x .x10 v).gpr .x12 = s.gpr .x12 := by simp [State.write]
    show InRegions s.wr ((s.write .x .x10 v).gpr .x12) 8
    rw [this, inv.dst, inv.wr]; exact hpre.write j hj
  let s₂ : State := { s₁ with mem := s₁.mem.writeW (wAt B j) v }
  have e₂ : exec (.str .x .x10 .x12 0) s₁ = some s₂ := by
    rw [exec_str_x ⟨by decide, by decide⟩ hw, add_ofNat_zero]
    have h12 : s₁.gpr .x12 = wAt B j := by
      show (s.write .x .x10 v).gpr .x12 = _; simp [State.write, inv.dst]; rfl
    have h10 : s₁.gpr .x10 = v := by show (s.write .x .x10 v).gpr .x10 = _; simp [State.write]
    rw [h12, h10]
  let s₃ := s₂.write .x .x11 (s₂.read .x .x11 + BitVec.ofNat _ 8)
  let s₄ := s₃.write .x .x12 (s₃.read .x .x12 + BitVec.ofNat _ 8)
  let s₅ := s₄.write .x .x13 (s₄.read .x .x13 - BitVec.ofNat _ 1)
  have run : runBlock isa [.ldr .x .x10 .x11 0, .str .x .x10 .x12 0, .addImm .x .x11 .x11 8,
      .addImm .x .x12 .x12 8, .subImm .x .x13 .x13 1] s = some s₅ := by
    rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons,
      exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_addImm_x (by decide), runStep_some,
      runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_nil]
  refine WP.of_runBlock ⟨s₅, run, ?_⟩
  have g₅ : ∀ r, CopyRegs r → s₅.gpr r = s.gpr r := by
    intro r ⟨h1, h2, h3, h4⟩
    simp [s₅, s₄, s₃, s₂, s₁, State.write, h1, h2, h3, h4]
  have src₅ : s₅.gpr .x11 = wAt A (j + 1) := by
    simp [s₅, s₄, s₃, s₂, s₁, State.write, State.read, inv.src]
    exact wAt_succ A j
  have dst₅ : s₅.gpr .x12 = wAt B (j + 1) := by
    simp [s₅, s₄, s₃, s₂, s₁, State.write, State.read, inv.dst]
    exact wAt_succ B j
  have cnt₅ : s₅.gpr .x13 = s.gpr .x13 - 1 := by
    simp [s₅, s₄, s₃, s₂, s₁, State.write, State.read]
  have mem₅ : s₅.mem = s.mem.writeW (wAt B j) v := rfl
  have copied₅ : ∀ x < j + 1, s₅.mem.readW (wAt B x) 64 = s₀.mem.readW (wAt A x) 64 := by
    intro x hx
    rw [mem₅]
    have fit := hpre.fitA
    by_cases he : x = j
    · subst he; exact Mem.readW_writeW_self64 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep B (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
      exact inv.copied x (by omega_arith)
  have frame₅ : Frame [⟨B, 8 * n⟩] s₀.mem s₅.mem := by
    rw [mem₅]; exact inv.frame.writeW List.mem_cons_self _ (wAt_in hj hpre.fitA)
  have regs₅ : ∀ r, CopyRegs r → s₅.gpr r = s₀.gpr r := fun r hr => (g₅ r hr).trans (inv.regs r hr)
  have cntv : s₅.gpr .x13 = BitVec.ofNat 64 (m - 1) := by
    rw [cnt₅, inv.cnt, show n - j = m by omega_arith]
    exact cnt_sub m (by omega_arith)
  have flag : isa.eval (.nonzero .x .x13) s₅ = some (m - 1 != 0) := by
    show some (s₅.read .x .x13 != 0) = _
    have hlt : m - 1 < 2 ^ 64 := by have := hpre.fitA; omega_arith
    simp only [State.read, BitVec.setWidth_eq, cntv]
    congr 1
    by_cases h0 : m - 1 = 0
    · simp [h0]
    · have hne : BitVec.ofNat 64 (m - 1) ≠ 0 := by
        intro e; have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at this; simp at this; omega_arith
      change (BitVec.ofNat 64 (m - 1) != (0 : BitVec 64)) = (m - 1 != 0)
      simp only [bne, beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr h0]
  by_cases h1 : m = 1
  · left
    refine ⟨by rw [flag, h1]; rfl, ?_⟩
    exact ⟨fun x hx => copied₅ x (by omega_arith), frame₅, regs₅, inv.rd, inv.wr, inv.sp, inv.v⟩
  · right
    refine ⟨by rw [flag]; simp; omega_arith, m - 1, by omega_arith, ⟨?_, ?_, ?_, ?_, ?_, frame₅, regs₅, inv.rd,
      inv.wr, inv.sp, inv.v⟩, by omega_arith⟩
    · omega_arith
    · rw [src₅]; congr 2; omega_arith
    · rw [dst₅]; congr 2; omega_arith
    · rw [cntv]; congr 1; omega_arith
    · intro x hx; exact copied₅ x (by omega_arith)

end VG.Proof.Blowfish.AArch64

end

end

/-!
# The batches of sixteen blocks

While at least sixteen blocks are left, a batch runs on the next sixteen
in place (`wide_ok`).
-/

@[expose] public section

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64
open VG.Spec.Blowfish VG.Proof.Blowfish

/-- What the batches may assume of the state they start in: the schedule
readable, the `n` blocks of data and the working space writable, apart from
each other, and the constants in `c64` and `c128`. -/
structure Env (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .x0, 4168⟩]
  wr : s.wr = [⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩, ⟨s.gpr .x3, 256⟩]
  keyData : (⟨s.gpr .x0, 4168⟩ : Region).Disjoint ⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩
  keyBuf : (⟨s.gpr .x0, 4168⟩ : Region).Disjoint ⟨s.gpr .x3, 256⟩
  dataBuf : (⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩ : Region).Disjoint ⟨s.gpr .x3, 256⟩
  fit : (s.gpr .x1).toNat + 8 * (s.gpr .x2).toNat ≤ 2 ^ 64
  consts : Consts s

/-- A region disjoint from a nonempty one does not cover the whole address space. -/
theorem len_lt_of_disjoint {r₁ r₂ : Region} (h : r₁.Disjoint r₂) (h2 : 0 < r₂.len) : r₁.len < 2 ^ 64 := by
  by_contra hc
  refine h r₂.base ?_ ?_
  · simp only [Region.Contains]; have := (r₂.base - r₁.base).isLt; omega_arith
  · simp only [Region.Contains, BitVec.sub_self]; simp; omega_arith

theorem Env.len {s : State} (E : Env s) : 8 * (s.gpr .x2).toNat < 2 ^ 64 :=
  len_lt_of_disjoint E.dataBuf (by simp)

theorem Env.sched {s : State} (E : Env s) : SchedIn s .x0 := by
  intro off n h
  rw [E.rd]
  exact ⟨_, List.mem_cons_self, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 8⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, Vector.getElem_ofFn]
  exact hf.bytes (R := ⟨p, 8⟩) hd (by show 8 ≤ 2 ^ 64; decide) hi

theorem blockAt_eq_of_readW {m m' : Mem} {p p' : Addr} (h : m'.readW p' 64 = m.readW p 64) :
    blockAt m' p' = blockAt m p := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, Vector.getElem_ofFn]
  rw [← Mem.extractLsb'_read m' p' (n := 8) hi, ← Mem.extractLsb'_read m p (n := 8) hi]
  obtain e : ∀ (m : Mem) (p : Addr), m.read p 8 = m.readW p 64 := fun m p => by
    simp only [Mem.readW]; rfl
  rw [e, e, h]

theorem eval_zero (s : State) (r : Reg) {m : Nat} (h : s.gpr r = BitVec.ofNat 64 m)
    (hm : m < 2 ^ 64) : isa.eval (.zero .x r) s = some (m == 0) := by
  show some (s.read .x r == 0) = _
  simp only [State.read, BitVec.setWidth_eq, h]
  congr 1
  by_cases h0 : m = 0
  · subst h0; rfl
  · have : BitVec.ofNat 64 m ≠ 0 := by
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm] at this
      simp at this; omega_arith
    change (BitVec.ofNat 64 m == (0 : BitVec 64)) = (m == 0)
    simp only [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr h0]

theorem lsr4 (m : Nat) (hm : 8 * m < 2 ^ 64) :
    BitVec.ofNat 64 m >>> 4 = BitVec.ofNat 64 (m / 16) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]

/-! ## The batches of sixteen blocks -/

/-- The registers the batches change. -/
def WideRegs (r : Reg) : Prop :=
  r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x4 ∧ r ≠ .x5 ∧ r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x8

/-- `m` blocks left, a multiple of sixteen fewer than `n`, and at least sixteen. -/
structure WideInv (up : Bool) (s₀ : State) (n m : Nat) (s : State) : Prop where
  ge : 16 ≤ m
  le : m ≤ n
  mod : m % 16 = n % 16
  x2 : s.gpr .x2 = BitVec.ofNat 64 m
  x1 : s.gpr .x1 = wAt (s₀.gpr .x1) (n - m)
  gpr : ∀ r, WideRegs r → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  v : ∀ r, r ∉ roundRegs → s.v r = s₀.v r
  done : ∀ b < n - m, blockAt s.mem (wAt (s₀.gpr .x1) b) =
    blockOut (scheduleAt s₀.mem (s₀.gpr .x0)) up (blockAt s₀.mem (wAt (s₀.gpr .x1) b))
  frame : Frame [⟨s₀.gpr .x1, 8 * (n - m)⟩] s₀.mem s.mem

structure WidePost (up : Bool) (s₀ : State) (n : Nat) (s : State) : Prop where
  x2 : s.gpr .x2 = BitVec.ofNat 64 (n % 16)
  x1 : s.gpr .x1 = wAt (s₀.gpr .x1) (n - n % 16)
  gpr : ∀ r, WideRegs r → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  v : ∀ r, r ∉ roundRegs → s.v r = s₀.v r
  done : ∀ b < n - n % 16, blockAt s.mem (wAt (s₀.gpr .x1) b) =
    blockOut (scheduleAt s₀.mem (s₀.gpr .x0)) up (blockAt s₀.mem (wAt (s₀.gpr .x1) b))
  frame : Frame [⟨s₀.gpr .x1, 8 * (n - n % 16)⟩] s₀.mem s.mem

theorem loop_ok (up : Bool) {s₀ : State} (E : Env s₀) {n : Nat}
    (hn : (s₀.gpr .x2).toNat = n) (m : Nat) (s : State) (hs : WideInv up s₀ n m s) :
    WP isa (.loop (.seq (.block [.addImm .x .x4 .x1 0]) (.seq (batch up)
        (.block [.addImm .x .x1 .x1 128, .subImm .x .x2 .x2 16, wholeLeft])))
      (.nonzero .x .x8)) s (WidePost up s₀ n) := by
  refine WP.loop (M := isa) (WideInv up s₀ n) ?_ m s hs
  intro m s h
  have hl := E.len
  have hfit := E.fit
  rw [hn] at hl hfit
  have hge := h.ge
  have hle := h.le
  let D := s₀.gpr .x1
  let S := s₀.gpr .x0
  have g := h.gpr
  obtain hx0 : s.gpr .x0 = S := g _ (by simp [WideRegs])
  apply WP.seq
  let s₁ := s.write .x .x4 (s.read .x .x1 + BitVec.ofNat _ 0)
  refine WP.of_runBlock ⟨s₁, by rw [runBlock_cons, exec_addImm_x (by decide), runStep_some,
    runBlock_nil], ?_⟩
  obtain g₁ : ∀ r, r ≠ .x4 → s₁.gpr r = s.gpr r := fun r hr => by simp [s₁, State.write, hr]
  obtain x4₁ : s₁.gpr .x4 = wAt D (n - m) := by simp [s₁, State.write, State.read, h.x1]; rfl
  obtain dataR : (⟨D, 8 * n⟩ : Region) ∈ s₁.wr := by
    show _ ∈ s.wr; rw [h.wr, E.wr, hn]; exact List.mem_cons_self
  obtain hW₁ : ∀ k < 8, InRegions s₁.wr (s₁.gpr .x4 + BitVec.ofNat 64 (16 * k)) 16 := fun k hk =>
    ⟨_, dataR, by rw [x4₁, wAt, Offset.add_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain hS₁ : SchedIn s₁ .x0 := fun off n' h' => by
    rw [g₁ _ (by decide), hx0]
    show InRegions (s.rd ++ s.wr) _ n'
    rw [h.rd, h.wr]; exact E.sched off n' h'
  obtain hc₁ : Consts s₁ := ⟨fun e he => by rw [show s₁.v = s.v from rfl, h.v _ (by decide)]; exact E.consts.1 e he,
    fun e he => by rw [show s₁.v = s.v from rfl, h.v _ (by decide)]; exact E.consts.2 e he⟩
  apply WP.seq
  apply WP.mono (batch_ok up hS₁ hc₁ hW₁)
  intro s₂ q
  obtain g₂ : ∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x4 → s₂.gpr r = s.gpr r :=
    fun r a b c e => (q.gpr r a b c).trans (g₁ r e)
  let s₃ := s₂.write .x .x1 (s₂.read .x .x1 + BitVec.ofNat _ 128)
  let s₄ := s₃.write .x .x2 (s₃.read .x .x2 - BitVec.ofNat _ 16)
  let s₅ := s₄.write .x .x8 (s₄.read .x .x2 >>> 4)
  refine WP.of_runBlock ⟨s₅, by
    rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
      exec_subImm_x (by decide), runStep_some, runBlock_cons, wholeLeft, exec_lsr_x (by decide),
      runStep_some, runBlock_nil], ?_⟩
  obtain x2₅ : s₅.gpr .x2 = BitVec.ofNat 64 (m - 16) := by
    simp only [s₅, s₄, s₃, State.write, State.read, BitVec.setWidth_eq, reduceCtorEq, ite_false,
      ite_true]
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide), h.x2,
      show (BitVec.ofNat 64 16) = BitVec.ofNat 64 16 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) hge]
  obtain x1₅ : s₅.gpr .x1 = wAt D (n - (m - 16)) := by
    simp only [s₅, s₄, s₃, State.write, State.read, BitVec.setWidth_eq, reduceCtorEq, ite_false,
      ite_true]
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide), h.x1, wAt, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat]
    exact congrArg (fun i => D + BitVec.ofNat 64 i) (by omega_arith)
  obtain x8₅ : s₅.gpr .x8 = BitVec.ofNat 64 ((m - 16) / 16) := by
    simp only [s₅, State.write, State.read, BitVec.setWidth_eq, ite_true]
    have : s₄.gpr .x2 = s₅.gpr .x2 := by simp [s₅, State.write]
    rw [this, x2₅, lsr4 _ (by omega_arith)]
  obtain g₅ : ∀ r, WideRegs r → s₅.gpr r = s₀.gpr r := by
    intro r ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇⟩
    simp only [s₅, s₄, s₃, State.write, BitVec.setWidth_eq, a₇, a₂, a₁, ite_false]
    rw [g₂ r a₄ a₅ a₆ a₃, g r ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇⟩]
  have mem₅ : s₅.mem = s₂.mem := rfl
  obtain frame' : Frame [⟨D, 8 * (n - (m - 16))⟩] s₀.mem s₅.mem := by
    obtain f₁ : Frame [⟨D, 8 * (n - (m - 16))⟩] s₀.mem s.mem := h.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Region.sub_prefix (by omega_arith)⟩
    obtain f₂ : Frame [⟨D, 8 * (n - (m - 16))⟩] s.mem s₂.mem := q.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, by
        show Region.Sub ⟨s₁.gpr .x4, 128⟩ _
        rw [x4₁]; exact Offset.sub_base _ (by omega_arith)⟩
    rw [mem₅]; exact f₁.trans f₂
  obtain done' : ∀ b < n - (m - 16), blockAt s₅.mem (wAt D b) =
      blockOut (scheduleAt s₀.mem S) up (blockAt s₀.mem (wAt D b)) := by
    intro b hb
    rw [mem₅]
    by_cases hb' : b < n - m
    · rw [← h.done b hb']
      refine blockAt_frame q.frame fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      show Region.Disjoint _ ⟨s₁.gpr .x4, 128⟩
      rw [x4₁]
      exact Offset.disjoint D (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith)
    · obtain ⟨j, rfl⟩ : ∃ j, b = n - m + j := ⟨b - (n - m), by omega_arith⟩
      obtain e := q.out j (by omega_arith)
      rw [x4₁] at e
      rw [show wAt D (n - m + j) = wAt D (n - m) + BitVec.ofNat 64 (8 * j) by rw [← wAt_wAt], e,
        g₁ _ (by decide), hx0]
      obtain hK : scheduleAt s.mem S = scheduleAt s₀.mem S :=
        scheduleAt_eq_of_frame S h.frame fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hn ▸ E.keyData).sub_right (Region.sub_prefix (by omega_arith))
      obtain hB : blockAt s.mem (wAt D (n - m + j)) = blockAt s₀.mem (wAt D (n - m + j)) :=
        blockAt_frame h.frame fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint_base D (by omega_arith) (by omega_arith)
      show blockOut (scheduleAt s₁.mem S) up (blockAt s₁.mem _) = _
      rw [show s₁.mem = s.mem from rfl, hK, show wAt D (n - m) + BitVec.ofNat 64 (8 * j) = wAt D (n - m + j)
        by rw [← wAt_wAt], hB]
  obtain wr₅ : s₅.wr = s₀.wr := q.wr.trans h.wr
  obtain rd₅ : s₅.rd = s₀.rd := q.rd.trans h.rd
  obtain sp₅ : s₅.sp = s₀.sp := q.sp.trans h.sp
  obtain v₅ : ∀ r, r ∉ roundRegs → s₅.v r = s₀.v r := fun r hr => (q.v r hr).trans (h.v r hr)
  obtain flag := eval_nonzero s₅ .x8 x8₅ (by omega_arith)
  by_cases hend : m - 16 < 16
  · left
    obtain e : m - 16 = n % 16 := by have := h.mod; omega_arith
    refine ⟨by rw [flag]; simp; omega_arith, by rw [x2₅, e], by rw [x1₅, e], g₅, rd₅, wr₅, sp₅, v₅,
      by rw [← e]; exact done', by rw [← e]; exact frame'⟩
  · right
    refine ⟨by rw [flag]; simp; omega_arith, m - 16, by omega_arith,
      ⟨by omega_arith, by omega_arith, by have := h.mod; omega_arith, x2₅, x1₅, g₅, rd₅, wr₅, sp₅, v₅, done', frame'⟩⟩

theorem wide_ok (up : Bool) {s : State} (E : Env s) :
    WP isa (wide up) s (WidePost up s (s.gpr .x2).toNat) := by
  let n := (s.gpr .x2).toNat
  have hl := E.len
  rw [wide]
  apply WP.seq
  let s₁ := s.write .x .x8 (s.read .x .x2 >>> 4)
  refine WP.of_runBlock ⟨s₁, by rw [runBlock_cons, wholeLeft, exec_lsr_x (by decide), runStep_some,
    runBlock_nil], ?_⟩
  obtain x8₁ : s₁.gpr .x8 = BitVec.ofNat 64 (n / 16) := by
    simp only [s₁, State.write, State.read, BitVec.setWidth_eq, ite_true]
    rw [show s.gpr .x2 = BitVec.ofNat 64 n by simp [n], lsr4 _ hl]
  obtain g₁ : ∀ r, r ≠ .x8 → s₁.gpr r = s.gpr r := fun r hr => by simp [s₁, State.write, hr]
  apply WP.ite _ (eval_zero s₁ .x8 x8₁ (by omega_arith))
  · intro hz
    obtain hz' : n < 16 := by simp at hz; omega_arith
    apply WP.block_nil
    obtain e : n % 16 = n := Nat.mod_eq_of_lt hz'
    refine ⟨?_, ?_, fun r hr => g₁ r hr.2.2.2.2.2.2, rfl, rfl, rfl, fun _ _ => rfl, fun b hb => by omega_arith, ?_⟩
    · rw [g₁ _ (by decide), e]; simp [n]
    · rw [g₁ _ (by decide), e, Nat.sub_self]; simp [wAt]
    · rw [e, Nat.sub_self]; exact Frame.refl _ _
  · intro hnz
    obtain hge : 16 ≤ n := by simp at hnz; omega_arith
    obtain E₁ : Env s₁ := by
      obtain h0 := g₁ .x0 (by decide); have h1 := g₁ .x1 (by decide)
      obtain h2 := g₁ .x2 (by decide); have h3 := g₁ .x3 (by decide)
      exact ⟨by rw [h0]; exact E.rd, by rw [h1, h2, h3]; exact E.wr,
        by rw [h0, h1, h2]; exact E.keyData, by rw [h0, h3]; exact E.keyBuf,
        by rw [h1, h2, h3]; exact E.dataBuf, by rw [h1, h2]; exact E.fit, E.consts⟩
    obtain hn₁ : (s₁.gpr .x2).toNat = n := by rw [g₁ _ (by decide)]
    obtain I : WideInv up s₁ n n s₁ := ⟨hge, Nat.le_refl _, rfl, by rw [g₁ _ (by decide)]; simp [n],
      by simp [wAt], fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, fun b hb => by omega_arith,
      by rw [Nat.sub_self]; exact Frame.refl _ _⟩
    apply WP.mono (loop_ok up E₁ hn₁ n s₁ I)
    intro s₂ p
    obtain h0 := g₁ .x0 (by decide); have h1 := g₁ .x1 (by decide)
    refine ⟨p.x2, by rw [p.x1, h1], fun r hr => (p.gpr r hr).trans (g₁ r hr.2.2.2.2.2.2), p.rd, p.wr,
      p.sp, p.v, fun b hb => ?_, by rw [← h1]; exact p.frame⟩
    rw [← h1, p.done b hb, h0, h1]; rfl

end VG.Proof.Blowfish.AArch64

end

end

/-! ### `Blowfish.AArch64.Tail`, which only this module used -/

section

/-!
# The blocks left

Fewer than sixteen blocks left (`k` of them, at `x1`) are copied into the
working space (the first 128 bytes at `x3`), run there as a batch whose
other lanes hold whatever the buffer held, and copied back (`tail_ok`).
-/

@[expose] public section

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64
open VG.Spec.Blowfish VG.Proof.Blowfish

/-- What the blocks left need: the `k < 16` blocks at `x1` writable, the
working space at `x3` writable, the schedule at `x0` readable, apart from
each other, and the constants. -/
structure TailEnv (s : State) (k : Nat) : Prop where
  lt : k < 16
  x2 : s.gpr .x2 = BitVec.ofNat 64 k
  dataW : ∀ i < k, InRegions s.wr (wAt (s.gpr .x1) i) 8
  scratch : (⟨s.gpr .x3, 256⟩ : Region) ∈ s.wr
  key : SchedIn s .x0
  keyData : (⟨s.gpr .x0, 4168⟩ : Region).Disjoint ⟨s.gpr .x1, 8 * k⟩
  keyBuf : (⟨s.gpr .x0, 4168⟩ : Region).Disjoint ⟨s.gpr .x3, 256⟩
  dataBuf : (⟨s.gpr .x1, 8 * k⟩ : Region).Disjoint ⟨s.gpr .x3, 256⟩
  consts : Consts s

/-- The registers the blocks left change. -/
def TailRegs (r : Reg) : Prop :=
  r ≠ .x4 ∧ r ≠ .x5 ∧ r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13

structure TailPost (up : Bool) (k : Nat) (s s' : State) : Prop where
  out : ∀ b < k, blockAt s'.mem (wAt (s.gpr .x1) b) =
    blockOut (scheduleAt s.mem (s.gpr .x0)) up (blockAt s.mem (wAt (s.gpr .x1) b))
  gpr : ∀ r, TailRegs r → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  v : ∀ r, r ∉ roundRegs → s'.v r = s.v r
  frame : Frame [⟨s.gpr .x1, 8 * k⟩, ⟨s.gpr .x3, 128⟩] s.mem s'.mem

theorem wAt_zero (p : Addr) : wAt p 0 = p := by simp [wAt]

theorem scratch_word {B : Addr} {i : Nat} (hi : i < 16) :
    (⟨B, 256⟩ : Region).Contains (wAt B i) 8 := Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])

theorem tail_ok (up : Bool) {k : Nat} {s : State} (E : TailEnv s k) :
    WP isa (tail up) s (TailPost up k s) := by
  let D := s.gpr .x1
  let B := s.gpr .x3
  let S := s.gpr .x0
  have hk := E.lt
  obtain scrIn : ∀ i < 16, InRegions s.wr (wAt B i) 8 := fun i hi => ⟨_, E.scratch, scratch_word hi⟩
  rw [tail]
  apply WP.ite _ (eval_zero s .x2 E.x2 (by omega_using [hk]))
  · intro hz
    obtain hk0 : k = 0 := by simpa using hz
    subst hk0
    apply WP.block_nil
    exact ⟨fun b hb => by omega, fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  · intro hnz
    obtain hk0 : k ≠ 0 := by simpa using hnz
    apply WP.seq
    -- x11 := x1, x12 := x3, x13 := x2
    let s₁ := ((s.write .x .x11 (s.read .x .x1 + BitVec.ofNat _ 0)).write .x .x12
      ((s.write .x .x11 (s.read .x .x1 + BitVec.ofNat _ 0)).read .x .x3 + BitVec.ofNat _ 0))
    let s₁' := s₁.write .x .x13 (s₁.read .x .x2 + BitVec.ofNat _ 0)
    refine WP.of_runBlock ⟨s₁', ?_, ?_⟩
    · rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
        exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_addImm_x (by decide),
        runStep_some, runBlock_nil]; rfl
    obtain g₁ : ∀ r, r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s₁'.gpr r = s.gpr r := by
      intro r a b c; simp [s₁', s₁, State.write, a, b, c]
    obtain pre₁ : CopyPre D B k s₁' := by
      refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, by omega_using [hk]⟩
      · obtain ⟨r, hr, hc⟩ := E.dataW i hi
        exact ⟨r, List.mem_append_right _ hr, hc⟩
      · exact scrIn i (by omega_using [hk, hi])
      · exact E.dataBuf.sub_right (Region.sub_prefix (by omega_using [hk]))
    obtain inv₁ : CopyInv D B k s₁' 0 s₁' := by
      refine ⟨by omega_using [hk0], ?_, ?_, ?_, fun j hj => by omega, Frame.refl _ _, fun _ _ => rfl, rfl, rfl,
        rfl, rfl⟩
      · rw [wAt_zero]; simp [s₁', s₁, State.write, State.read, D]
      · rw [wAt_zero]; simp [s₁', s₁, State.write, State.read, B]
      · simp [s₁', s₁, State.write, State.read, E.x2]
    apply WP.seq
    apply WP.mono (copy_ok pre₁ s₁' 0 inv₁)
    intro s₂ c₂
    obtain g₂ : ∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s₂.gpr r = s.gpr r :=
      fun r a b c e => (c₂.regs r ⟨a, b, c, e⟩).trans (g₁ r b c e)
    apply WP.seq
    -- x4 := x3
    let s₃ := s₂.write .x .x4 (s₂.read .x .x3 + BitVec.ofNat _ 0)
    refine WP.of_runBlock ⟨s₃, ?_, ?_⟩
    · rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_nil]; rfl
    obtain g₃ : ∀ r, r ≠ .x4 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s₃.gpr r = s.gpr r := by
      intro r a b c e f; simp only [s₃, State.write, a, ite_false]; exact g₂ r b c e f
    obtain x4₃ : s₃.gpr .x4 = B := by
      simp [s₃, State.write, State.read]; exact g₂ _ (by decide) (by decide) (by decide) (by decide)
    have wr₃ : s₃.wr = s.wr := c₂.wr
    obtain hW₃ : ∀ k < 8, InRegions s₃.wr (s₃.gpr .x4 + BitVec.ofNat 64 (16 * k)) 16 := fun k hk =>
      ⟨_, by rw [wr₃]; exact E.scratch, by rw [x4₃]; exact Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])⟩
    obtain hS₃ : SchedIn s₃ .x0 := fun off n h => by
      rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
      show InRegions (s₂.rd ++ s₂.wr) _ n
      rw [c₂.rd, c₂.wr]; exact E.key off n h
    obtain hc₃ : Consts s₃ := by
      have : s₃.v = s.v := by rw [show s₃.v = s₂.v from rfl, c₂.v]; rfl
      rw [Consts, this]; exact E.consts
    apply WP.seq
    apply WP.mono (batch_ok up hS₃ hc₃ hW₃)
    intro s₄ q₄
    obtain g₄ : ∀ r, TailRegs r → s₄.gpr r = s.gpr r := by
      intro r ⟨a, b, c, e, f', i, j, l⟩
      rw [q₄.gpr r b c e, g₃ r a f' i j l]
    apply WP.seq
    -- x11 := x3, x12 := x1, x13 := x2
    let s₅ := ((s₄.write .x .x11 (s₄.read .x .x3 + BitVec.ofNat _ 0)).write .x .x12
      ((s₄.write .x .x11 (s₄.read .x .x3 + BitVec.ofNat _ 0)).read .x .x1 + BitVec.ofNat _ 0))
    let s₅' := s₅.write .x .x13 (s₅.read .x .x2 + BitVec.ofNat _ 0)
    refine WP.of_runBlock ⟨s₅', ?_, ?_⟩
    · rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
        exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_addImm_x (by decide),
        runStep_some, runBlock_nil]; rfl
    obtain g₅ : ∀ r, TailRegs r → s₅'.gpr r = s.gpr r := by
      intro r hr
      have ⟨_, _, _, _, _, i, j, l⟩ := hr
      simp only [s₅', s₅, State.write, i, j, l, ite_false]; exact g₄ r hr
    obtain wr₅ : s₅'.wr = s.wr := q₄.wr.trans wr₃
    obtain rd₅ : s₅'.rd = s.rd := q₄.rd.trans c₂.rd
    obtain pre₂ : CopyPre B D k s₅' := by
      refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, by omega_using [hk]⟩
      · obtain ⟨r, hr, hc⟩ := scrIn i (by omega_using [hk, hi])
        rw [wr₅]; exact ⟨r, List.mem_append_right _ hr, hc⟩
      · rw [wr₅]; exact E.dataW i hi
      · exact (E.dataBuf.sub_right (Region.sub_prefix (by omega_using [hk]))).symm
    obtain inv₂ : CopyInv B D k s₅' 0 s₅' := by
      refine ⟨by omega_using [hk0], ?_, ?_, ?_, fun j hj => by omega, Frame.refl _ _, fun _ _ => rfl, rfl, rfl,
        rfl, rfl⟩
      · rw [wAt_zero]; simp [s₅', s₅, State.write, State.read]
        exact g₄ _ ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
      · rw [wAt_zero]; simp [s₅', s₅, State.write, State.read]
        exact g₄ _ ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
      · simp [s₅', s₅, State.write, State.read]
        rw [g₄ _ ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
          by decide⟩, E.x2]
    apply WP.mono (copy_ok pre₂ s₅' 0 inv₂)
    intro s₆ c₆
    -- memory
    have m₃ : s₃.mem = s₂.mem := rfl
    have m₅ : s₅'.mem = s₄.mem := rfl
    obtain dataSep : (⟨D, 8 * k⟩ : Region).Disjoint ⟨B, 8 * k⟩ :=
      E.dataBuf.sub_right (Region.sub_prefix (by omega_using [hk]))
    obtain K₃ : scheduleAt s₃.mem (s₃.gpr .x0) = scheduleAt s.mem S := by
      rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), m₃]
      exact scheduleAt_eq_of_frame S c₂.frame fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact E.keyBuf.sub_right (Region.sub_prefix (by omega_using [hk]))
    refine ⟨fun b hb => ?_, fun r hr => (c₆.regs r ⟨hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2⟩).trans (g₅ r hr), c₆.rd.trans rd₅, c₆.wr.trans wr₅,
      c₆.sp.trans (q₄.sp.trans c₂.sp), fun r hr => ?_, ?_⟩
    · -- the block in the data, from the scratch buffer after the batch
      obtain e₆ : blockAt s₆.mem (wAt D b) = blockAt s₄.mem (wAt B b) := by
        rw [← m₅]; exact blockAt_eq_of_readW (c₆.copied b hb)
      -- the block in the scratch buffer before the batch, from the data
      obtain e₂ : blockAt s₂.mem (wAt B b) = blockAt s.mem (wAt D b) := by
        refine blockAt_eq_of_readW ((c₂.copied b hb).trans ?_)
        rfl
      rw [e₆]
      obtain o := q₄.out b (by omega_using [hk, hb])
      rw [x4₃, K₃, m₃, e₂] at o
      exact o
    · rw [c₆.v, show s₅'.v = s₄.v from rfl, q₄.v r hr, show s₃.v = s₂.v from rfl, c₂.v]; rfl
    · have a : Frame [⟨D, 8 * k⟩, ⟨B, 128⟩] s.mem s₂.mem := c₂.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by omega_using [hk])⟩
      obtain b : Frame [⟨D, 8 * k⟩, ⟨B, 128⟩] s₂.mem s₄.mem := q₄.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by rw [x4₃]; exact fun _ h => h⟩
      obtain c : Frame [⟨D, 8 * k⟩, ⟨B, 128⟩] s₅'.mem s₆.mem := c₆.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      rw [m₅] at c
      exact (a.trans b).trans c

end VG.Proof.Blowfish.AArch64

end

end


/-!
# The ECB function

`q8`–`q15` are saved in the second half of the working space, the constants
set, the batches and the blocks left run, and `q8`–`q15` restored
(`ecb_correct`).
-/

@[expose] public section

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64
open VG.Spec.Blowfish VG.Proof.Blowfish
open VG.AArch64.Tbl (VOnly)

/-- The callee-saved vector registers, in the order they are saved. -/
def savedReg (k : Nat) : VReg := [.v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15].getD k .v8

theorem savedReg_inj : ∀ a < 8, ∀ b < 8, a ≠ b → savedReg a ≠ savedReg b := by decide

theorem saveRegs_eq : saveRegs = (List.range 8).map fun k => .strq (savedReg k) .x3 (saveOff + 16 * k) := rfl
theorem restoreRegs_eq : restoreRegs = (List.range 8).map fun k => .ldrq (savedReg k) .x3 (saveOff + 16 * k) := rfl
/-- The save area: the 128 bytes at `x3 + 128`. -/
def saveR (s : State) : Region := ⟨s.gpr .x3 + BitVec.ofNat 64 128, 128⟩

theorem read_write_self16 (m : Mem) (a : Addr) (v : BitVec 128) : (m.write a 16 v).read a 16 = v :=
  Mem.read_eq_of_bytes fun i hi => by
    simp only [Mem.write, Mem.sub_ofNat_toNat a (show i < 2 ^ 64 by omega_using [hi]), hi, ite_true]

theorem strqs_run (off : Nat) (hoff : off % 16 = 0 ∧ off + 128 ≤ 4096) : ∀ (n : Nat), n ≤ 8 → ∀ (s : State),
    (∀ k < 8, InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 (off + 16 * k)) 16) →
    ∃ s', runBlock isa ((List.range n).map fun k => .strq (savedReg k) .x3 (off + 16 * k)) s = some s' ∧
      (∀ k < n, s'.mem.read (s.gpr .x3 + BitVec.ofNat 64 (off + 16 * k)) 16 = s.v (savedReg k)) ∧
      Frame [⟨s.gpr .x3 + BitVec.ofNat 64 off, 128⟩] s.mem s'.mem ∧ s' = { s with mem := s'.mem }
  | 0, _, s, _ => ⟨s, runBlock_nil, fun _ h => absurd h (by omega_using []), Frame.refl _ _, rfl⟩
  | n + 1, hn, s, hW => by
    obtain ⟨s', r, v, f, e⟩ := strqs_run off hoff n (by omega_using [hn]) s hW
    obtain hW' : InRegions s'.wr (s'.gpr .x3 + BitVec.ofNat 64 (off + 16 * n)) 16 := by
      rw [e]; exact hW n (by omega_using [hn])
    obtain ⟨s'', r', m', o'⟩ := strq_run (t := s') (savedReg n) .x3 (off := off + 16 * n) (by omega_using [hoff, hn]) hW'
    obtain g' : s'.gpr = s.gpr := by rw [e]
    obtain v' : s'.v = s.v := by rw [e]
    refine ⟨s'', by rw [List.range_succ, List.map_append]; exact cat_run r r',
      fun k hk => ?_, ?_, ?_⟩
    · rw [m', g', v']
      by_cases hkn : k = n
      · subst hkn; exact read_write_self16 _ _ _
      · rw [Mem.read_write_sep (Offset.sep _ (by omega_using [hkn]) (by omega_using [hoff, hn, hk]) (by omega_using [hoff, hn])) (by decide)]
        exact v k (by omega_using [hk, hkn])
    · rw [m', g']
      exact f.write (List.mem_singleton.mpr rfl) _ (Offset.contains _ (by omega_using []) (by omega_using [hn]) (by omega_using [hoff]))
    · have hv : s''.v = s.v := funext fun x => (o'.v x (List.not_mem_nil)).trans (by rw [v'])
      rw [o'.eq, e]; simp only [hv]

def savedRegs : List VReg := [.v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15]

theorem savedReg_mem : ∀ k < 8, savedReg k ∈ savedRegs := by decide

theorem ldrqs_run (off : Nat) (hoff : off % 16 = 0 ∧ off + 128 ≤ 4096) : ∀ (n : Nat), n ≤ 8 → ∀ (s : State),
    (∀ k < 8, InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (off + 16 * k)) 16) →
    ∃ s', runBlock isa ((List.range n).map fun k => .ldrq (savedReg k) .x3 (off + 16 * k)) s = some s' ∧
      (∀ k < n, s'.v (savedReg k) = s.mem.read (s.gpr .x3 + BitVec.ofNat 64 (off + 16 * k)) 16) ∧
      VOnly savedRegs s s'
  | 0, _, s, _ => ⟨s, runBlock_nil, fun _ h => absurd h (by omega_using []), VOnly.refl _ _⟩
  | n + 1, hn, s, hR => by
    obtain ⟨s', r, v, o⟩ := ldrqs_run off hoff n (by omega_using [hn]) s hR
    obtain ⟨s'', r', v', o'⟩ := ldrq_run (t := s') (savedReg n) .x3 (off := off + 16 * n)
      (by omega_using [hoff, hn]) (by rw [o.rd, o.wr, o.gpr]; exact hR n (by omega_using [hn]))
    refine ⟨s'', by rw [List.range_succ, List.map_append]; exact cat_run r r', fun k hk => ?_,
      o.trans (VOnly.mono o' (by simp; exact savedReg_mem n (by omega_using [hn])))⟩
    by_cases hkn : k = n
    · subst hkn; rw [v', o.mem, o.gpr]
    · rw [o'.2 _ (by simp; exact savedReg_inj k (by omega_using [hn, hk]) n (by omega_using [hn]) hkn), v k (by omega_using [hk, hkn])]

/-- `movz` and `dup .16b` of 64 and 128: the constants. -/
theorem constants_run (s : State) :
    ∃ s', runBlock isa constants s = some s' ∧ Consts s' ∧
      (∀ r, r ≠ .x6 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ VOnly [c64, c128] { s with gpr := s'.gpr } s' := by
  let s₁ := s.write .x .x6 ((64 : BitVec 16).setWidth 64 <<< (16 * 0))
  let s₂ := s₁.setV c64 (ofVBytes fun _ => (s₁.gpr .x6).setWidth 8)
  let s₃ := s₂.write .x .x6 ((128 : BitVec 16).setWidth 64 <<< (16 * 0))
  let s₄ := s₃.setV c128 (ofVBytes fun _ => (s₃.gpr .x6).setWidth 8)
  refine ⟨s₄, rfl, ⟨fun e he => ?_, fun e he => ?_⟩, fun r hr => ?_, rfl, rfl, rfl, rfl, ⟨rfl, fun r hr => ?_⟩⟩
  · simp only [s₄, s₃, s₂, v_setV_of_ne _ _ (by decide : c64 ≠ c128), v_write, v_setV_self]
    rw [vbyte_ofVBytes _ he]; rfl
  · simp only [s₄, v_setV_self]
    rw [vbyte_ofVBytes _ he]; rfl
  · simp only [s₄, s₃, s₂, s₁, gpr_setV, gpr_write_of_ne _ _ _ hr]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [s₄, s₃, s₂, s₁, v_setV_of_ne _ _ hr.2, v_write, v_setV_of_ne _ _ hr.1]

/-- What the function may assume: the schedule readable, the `n` blocks and
the working space writable, apart from each other. -/
structure EcbPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .x0, 4168⟩]
  wr : s.wr = [⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩, ⟨s.gpr .x3, 256⟩]
  keyData : (⟨s.gpr .x0, 4168⟩ : Region).Disjoint ⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩
  keyBuf : (⟨s.gpr .x0, 4168⟩ : Region).Disjoint ⟨s.gpr .x3, 256⟩
  dataBuf : (⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩ : Region).Disjoint ⟨s.gpr .x3, 256⟩
  fit : (s.gpr .x1).toNat + 8 * (s.gpr .x2).toNat ≤ 2 ^ 64

theorem ecb_eq (up : Bool) : ecb up =
    .seq (.block (saveRegs ++ constants)) (.seq (wide up) (.seq (tail up) (.block restoreRegs))) := rfl

theorem save_off (s : State) {k : Nat} (hk : k < 8) :
    (⟨s.gpr .x3, 256⟩ : Region).Contains (s.gpr .x3 + BitVec.ofNat 64 (saveOff + 16 * k)) 16 :=
  Offset.contains_base _ (by simp only [saveOff]; omega_using [hk]) (by simp only [saveOff]; omega_using [hk])

/-- Every block becomes its encryption or decryption, and `q8`–`q15` are
restored. -/
theorem ecb_correct (up : Bool) {s : State} (P : EcbPre s) :
    WP isa (ecb up) s (fun s' => (∀ b < (s.gpr .x2).toNat, blockAt s'.mem (wAt (s.gpr .x1) b) =
      blockOut (scheduleAt s.mem (s.gpr .x0)) up (blockAt s.mem (wAt (s.gpr .x1) b))) ∧
      ∀ r ∈ savedRegs, s'.v r = s.v r) := by
  let n := (s.gpr .x2).toNat
  let D := s.gpr .x1
  let S := s.gpr .x0
  let k := n % 16
  obtain bufW : (⟨s.gpr .x3, 256⟩ : Region) ∈ s.wr := by rw [P.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  -- the prologue
  obtain ⟨s₁, r₁, v₁, f₁, e₁⟩ := strqs_run saveOff (by decide) 8 (by decide) s fun k hk => ⟨_, bufW, save_off s hk⟩
  obtain ⟨s₂, r₂, c₂, g₂, m₂, rd₂, wr₂, sp₂, o₂⟩ := constants_run s₁
  obtain g₁ : s₁.gpr = s.gpr := by rw [e₁]
  obtain hg₂ : ∀ r, r ≠ .x6 → s₂.gpr r = s.gpr r := fun r hr => by rw [g₂ r hr, g₁]
  obtain hrd₂ : s₂.rd = s.rd := by rw [rd₂, e₁]
  obtain hwr₂ : s₂.wr = s.wr := by rw [wr₂, e₁]
  obtain E : Env s₂ := by
    obtain h0 := hg₂ .x0 (by decide); have h1 := hg₂ .x1 (by decide)
    obtain h2 := hg₂ .x2 (by decide); have h3 := hg₂ .x3 (by decide)
    exact ⟨by rw [hrd₂, h0]; exact P.rd, by rw [hwr₂, h1, h2, h3]; exact P.wr,
      by rw [h0, h1, h2]; exact P.keyData, by rw [h0, h3]; exact P.keyBuf,
      by rw [h1, h2, h3]; exact P.dataBuf, by rw [h1, h2]; exact P.fit, c₂⟩
  obtain saveSep : (saveR s).Disjoint ⟨s.gpr .x1, 8 * n⟩ :=
    (P.dataBuf.sub_right (Offset.sub_base _ (by omega_using []))).symm
  obtain hn₂ : (s₂.gpr .x2).toNat = n := by rw [hg₂ _ (by decide)]
  rw [ecb_eq]
  apply WP.seq
  refine WP.of_runBlock ⟨s₂, by rw [saveRegs_eq]; exact cat_run r₁ r₂, ?_⟩
  apply WP.seq
  apply WP.mono (wide_ok up E)
  intro s₃ w
  rw [hn₂] at w
  have g := w.gpr
  obtain h0 : s₃.gpr .x0 = S := (g _ (by simp [WideRegs])).trans (hg₂ _ (by decide))
  obtain h3 : s₃.gpr .x3 = s.gpr .x3 := (g _ (by simp [WideRegs])).trans (hg₂ _ (by decide))
  obtain h1 : s₃.gpr .x1 = wAt D (n - k) := by rw [w.x1, hg₂ _ (by decide)]
  obtain hl : 8 * n < 2 ^ 64 := by have := E.len; rw [hn₂] at this; exact this
  have hfit : D.toNat + 8 * n ≤ 2 ^ 64 := P.fit
  obtain sub₁ : Region.Sub ⟨s₃.gpr .x1, 8 * k⟩ ⟨D, 8 * n⟩ := by
    rw [h1]; exact Offset.sub_base _ (by omega_using [])
  obtain T : TailEnv s₃ k := by
    refine ⟨Nat.mod_lt _ (by decide), w.x2, fun i hi => ?_, ?_, fun off m h => ?_, ?_, ?_, ?_, ?_⟩
    · rw [w.wr, hwr₂, P.wr, h1, wAt_wAt]
      exact ⟨_, List.mem_cons_self, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hl, hi])⟩
    · rw [w.wr, hwr₂, P.wr, h3]; exact List.mem_cons_of_mem _ List.mem_cons_self
    · rw [w.rd, w.wr, h0, hrd₂, hwr₂, P.rd]
      exact ⟨_, List.mem_cons_self, Offset.contains_base _ (by omega_using [h]) (by omega_using [h])⟩
    · rw [h0]; exact P.keyData.sub_right sub₁
    · rw [h0, h3]; exact P.keyBuf
    · rw [h3]; exact P.dataBuf.sub_left sub₁
    · exact ⟨fun e he => by rw [w.v _ (by decide)]; exact E.consts.1 e he,
        fun e he => by rw [w.v _ (by decide)]; exact E.consts.2 e he⟩
  apply WP.seq
  apply WP.mono (tail_ok up T)
  intro s₄ t
  -- the epilogue
  obtain hR₄ : ∀ j < 8, InRegions (s₄.rd ++ s₄.wr) (s₄.gpr .x3 + BitVec.ofNat 64 (saveOff + 16 * j)) 16 := by
    intro j hj
    rw [t.rd, t.wr, t.gpr _ (by simp [TailRegs]), w.rd, w.wr, h3, hrd₂, hwr₂]
    exact ⟨_, List.mem_append_right _ bufW, save_off s hj⟩
  obtain ⟨s₅, r₅, v₅, o₅⟩ := ldrqs_run saveOff (by decide) 8 (by decide) s₄ hR₄
  have m₂' : s₂.mem = s₁.mem := m₂
  have hm₅ : s₅.mem = s₄.mem := o₅.mem
  have dataB : (⟨D, 8 * n⟩ : Region).Disjoint ⟨s.gpr .x3, 256⟩ := P.dataBuf
  -- the prologue left the data and the schedule as they were
  obtain pro : Frame [saveR s] s.mem s₂.mem := by rw [m₂']; exact f₁
  obtain hK₂ : scheduleAt s₂.mem S = scheduleAt s.mem S :=
    scheduleAt_eq_of_frame S pro fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact P.keyBuf.sub_right (Offset.sub_base _ (by omega_using []))
  obtain hB₂ : ∀ b < n, blockAt s₂.mem (wAt D b) = blockAt s.mem (wAt D b) := fun b hb =>
    blockAt_frame pro fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (saveSep.sub_right (Offset.sub_base _ (by omega_using [hb]))).symm
  refine WP.of_runBlock ⟨s₅, by rw [restoreRegs_eq]; exact r₅, ?_, ?_⟩
  · intro b hb
    rw [hm₅]
    obtain h1' : s₂.gpr .x1 = D := hg₂ _ (by decide)
    obtain h0' : s₂.gpr .x0 = S := hg₂ _ (by decide)
    by_cases hbk : b < n - k
    · have e := w.done b hbk
      rw [h1', h0', hK₂, hB₂ b hb] at e
      rw [← e]
      refine blockAt_frame t.frame fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h1]; exact Offset.disjoint D (Or.inl (by omega_using [hbk])) (by omega_using [hl, hb]) (by omega_using [hl])
      · rw [h3]; exact dataB.sub_left (Offset.sub_base _ (by omega_using [hb])) |>.sub_right (Region.sub_prefix (by omega_using []))
    · obtain ⟨j, rfl⟩ : ∃ j, b = n - k + j := ⟨b - (n - k), by omega_using [hbk]⟩
      obtain e := t.out j (by omega_using [hb])
      rw [h1, wAt_wAt, h0] at e
      rw [e]
      obtain hK : scheduleAt s₃.mem S = scheduleAt s₂.mem S :=
        scheduleAt_eq_of_frame S w.frame fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [h1']; exact P.keyData.sub_right (Region.sub_prefix (by omega_using []))
      obtain hB : blockAt s₃.mem (wAt D (n - k + j)) = blockAt s₂.mem (wAt D (n - k + j)) :=
        blockAt_frame w.frame fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [h1']; exact Offset.disjoint_base D (by omega_using []) (by omega_using [hl, hb])
      rw [hK, hB, hK₂, hB₂ _ hb]
  · -- the saved registers, from the save area, which nothing else wrote
    obtain ss : ∀ j < 8, s₅.v (savedReg j) = s.v (savedReg j) := by
      intro j hj
      obtain hc : (saveR s).Contains (s.gpr .x3 + BitVec.ofNat 64 (saveOff + 16 * j)) 16 :=
        Offset.contains _ (by simp only [saveOff]; omega_using []) (by simp only [saveOff]; omega_using [hj]) (by omega_using [])
      rw [v₅ j hj, t.gpr _ (by simp [TailRegs]), h3,
        t.frame.read hc (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact saveSep.sub_right sub₁
          · rw [h3]; exact Offset.disjoint_base _ (by omega_using []) (by omega_using [])) (by decide),
        w.frame.read hc (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [hg₂ _ (by decide)]; exact saveSep.sub_right (Region.sub_prefix (by omega_using []))) (by decide),
        m₂', v₁ j hj]
    intro r hr
    simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ss 0 (by decide)
    · exact ss 1 (by decide)
    · exact ss 2 (by decide)
    · exact ss 3 (by decide)
    · exact ss 4 (by decide)
    · exact ss 5 (by decide)
    · exact ss 6 (by decide)
    · exact ss 7 (by decide)

end VG.Proof.Blowfish.AArch64
