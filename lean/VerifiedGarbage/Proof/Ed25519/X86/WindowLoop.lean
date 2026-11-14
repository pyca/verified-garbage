module

import VerifiedGarbage.Proof.Ed25519.X86.WindowTables
public import VerifiedGarbage.Proof.Ed25519.X86.VerifyContract
public import VerifiedGarbage.Proof.Ed25519.WindowNibble
public import VerifiedGarbage.Proof.Ed25519.DblPoint
public import VerifiedGarbage.Proof.Ed25519.X86.PointTable
public import VerifiedGarbage.Proof.Ed25519.X86.PowerEnv
import VerifiedGarbage.Proof.Ed25519.X86.Point32.Call
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseMain
import VerifiedGarbage.Proof.Ed25519.Group.Double
import VerifiedGarbage.Proof.X25519.X86.Fold
import VerifiedGarbage.Proof.Ed25519.X86.Point32.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Ed25519.X86.Points
import VerifiedGarbage.Proof.Ed25519.ScalarBytes
import VerifiedGarbage.Proof.Framework.Taint

/-! ### `Ed25519.X86.WindowStep`, which only this module used -/

section

/-!
# Verification's windows

A window doubles the sum four times (`dbl-2008-hwcd`, `dblPoint_rep`), reads a
digit of a scalar from the inputs (its nibble `esi`), and adds the digit's
entry of a table, unless the digit is zero. The sum represents a
multiple of `A` plus a multiple of `-B` throughout (`Rep`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86 VG.Proof.Ed25519 Edwards
open VG.Impl.X25519.X86 (sc at_)

/-! ## Doublings -/

theorem dblOps_eval (e : Env) : point (evalOps dblOps e) 0 1 2 3 = dblPoint (point e 0 1 2 3) := rfl

theorem dbl_ok {s : State} {x : BitVec 32} (hc : Ctx x s) {a : EPoint dZ}
    (h : Rep (point (env s.mem x) 0 1 2 3) a) :
    WP isa dbl s fun t => FieldKeep x s t ∧ Rep (point (env t.mem x) 0 1 2 3) (a + a) ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem x i = env s.mem x i := by
  refine WP.mono (fieldCode_ok dblOps hc) fun t ⟨kt, vt⟩ => ⟨kt, ?_, fun i hi => ?_⟩
  · rw [vt, dblOps_eval]; exact dblPoint_rep h.proj
  · rw [vt]; exact point_ops_high _ (by decide) _ i hi

/-- `add d, v`, and the carry. -/
theorem wp_addiC {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {v : BitVec 32}
    (k : ∀ s', Wp.Upd s s' d (s.gpr d + v) → s'.cf = some (decide (2 ^ 32 ≤ (s.gpr d).toNat + v.toNat)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  Wp.cons rfl (k _ (Wp.Upd.flags _ _ _ _ _ _) rfl)

/-- The doubling loop's counter: `esi` after `4 - n` of its four iterations, `n` left, and
`2³⁰` added: the next count, carrying out exactly on the last. -/
theorem dblCount_step {e u : BitVec 32} {n : Nat} (he : e.toNat < 2 ^ 30) (h1 : 1 ≤ n) (h4 : n ≤ 4)
    (hu : u.toNat = e.toNat + (4 - n) * 2 ^ 30) :
    (u + 0x40000000).toNat = (e.toNat + (4 - (n - 1)) * 2 ^ 30) % 2 ^ 32 ∧
      (decide (2 ^ 32 ≤ u.toNat + (0x40000000 : BitVec 32).toNat) = decide (n = 1)) := by
  have h30 : (0x40000000 : BitVec 32).toNat = 2 ^ 30 := rfl
  rw [BitVec.toNat_add, hu, h30]
  constructor
  · congr 1; omega_arith
  · simp only [decide_eq_decide]; omega_arith

theorem doubleWindow_ok {s : State} {x : BitVec 32} (hc : Ctx x s) (hesi : (s.gpr .esi).toNat < 2 ^ 30)
    {a : EPoint dZ} (h : Rep (point (env s.mem x) 0 1 2 3) a) :
    WP isa doubleWindow s fun t => IKeep x s t ∧ t.gpr .esi = s.gpr .esi ∧
      Rep (point (env t.mem x) 0 1 2 3) ((16 : Nat) • a) ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem x i = env s.mem x i := by
  refine WP.loop (M := isa) (Inv := fun n (t : State) => 1 ≤ n ∧ n ≤ 4 ∧
    (t.gpr .esi).toNat = (s.gpr .esi).toNat + (4 - n) * 2 ^ 30 ∧ IKeep x s t ∧
    Rep (point (env t.mem x) 0 1 2 3) ((2 ^ (4 - n) : Nat) • a) ∧
    ∀ i : Slot, 16 ≤ i.val → env t.mem x i = env s.mem x i) ?_ 4 s
    ⟨by decide, by decide, by simp, IKeep.refl _ _, by simpa using h, fun _ _ => rfl⟩
  intro n t ⟨h1, h4, he, kt, rt, ht⟩
  rw [dblStep, WP.block_append_iff]
  refine WP.mono (dbl_ok (kt.ctx hc) rt) fun u ⟨ku, ru, hu⟩ => ?_
  refine wp_addiC fun v hv cv => WP.block_nil ?_
  have eu : (u.gpr .esi).toNat = (s.gpr .esi).toNat + (4 - n) * 2 ^ 30 := by rw [ku.keep.esi]; exact he
  obtain ⟨ev, cv'⟩ := dblCount_step hesi h1 h4 eu
  rw [cv'] at cv
  have kv : IKeep x s v := kt.trans ((IKeep.of_field ku).trans (IKeep.of_counter hv))
  have rv : Rep (point (env v.mem x) 0 1 2 3) ((2 ^ (4 - (n - 1)) : Nat) • a) := by
    rw [hv.mem, show 4 - (n - 1) = (4 - n) + 1 by omega_arith, pow_succ, mul_comm, ← smul_smul, two_nsmul]
    exact ru
  have hv16 : ∀ i : Slot, 16 ≤ i.val → env v.mem x i = env s.mem x i :=
    fun i hi => by rw [hv.mem, hu i hi, ht i hi]
  rw [← hv.gpr] at ev
  by_cases hn : n = 1
  · subst hn
    refine .inl ⟨by simp only [eval, cv]; rfl, kv, ?_, by simpa using rv, hv16⟩
    apply BitVec.eq_of_toNat_eq
    rw [ev]; omega_arith
  · refine .inr ⟨by simp only [eval, cv, hn]; rfl, n - 1, by omega_arith, by omega_arith, by omega_arith,
      by rw [ev, Nat.mod_eq_of_lt (by omega_arith)], kv, rv, hv16⟩

/-! ## Digits -/

/-- What reading a digit leaves: everything but `eax` and the flags. -/
structure EaxKeep (s t : State) : Prop where
  gpr : ∀ r, r ≠ .eax → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem EaxKeep.trans {s t u : State} (h : EaxKeep s t) (k : EaxKeep t u) : EaxKeep s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.mem.trans h.mem, k.rd.trans h.rd, k.wr.trans h.wr⟩

theorem EaxKeep.of_upd {s t : State} {v : BitVec 32} (h : Wp.Upd s t .eax v) : EaxKeep s t :=
  ⟨h.other, h.mem, h.rd, h.wr⟩

theorem EaxKeep.ikeep {x : BitVec 32} {s t : State} (h : EaxKeep s t) : IKeep x s t :=
  ⟨h.gpr _ (by decide), h.gpr _ (by decide), h.rd, h.wr, by rw [h.mem]; exact Frame.refl _ _⟩

theorem bytesAt_getD (m : Mem) (p : Addr) (n i : Nat) (hi : i < n) :
    (Spec.Ed25519.bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Ed25519.bytesAt, List.getD_eq_getElem?_getD, hi]

/-- `test d, v`. -/
theorem wp_testi {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {v : BitVec 32}
    (k : ∀ s', Wp.Fupd s s' → s'.zf = some (s.gpr d &&& v == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .test d (.imm v) :: is)) s Q :=
  Wp.cons rfl (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl)

theorem EaxKeep.of_fupd {s t : State} (h : Wp.Fupd s t) : EaxKeep s t :=
  ⟨fun _ _ => by rw [h.gpr], h.mem, h.rd, h.wr⟩

theorem shr1_ofNat {i : Nat} (hi : i < 2 ^ 32) : BitVec.ofNat 32 i >>> 1 = BitVec.ofNat 32 (i / 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_arith

theorem and1_beq {i : Nat} (hi : i < 2 ^ 32) :
    (BitVec.ofNat 32 i &&& 1 == 0) = decide (i % 2 = 0) := by
  have : BitVec.ofNat 32 i &&& 1 = BitVec.ofNat 32 (i % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
    simp only [BitVec.toNat_ofNat]
    omega_arith
  rw [this, Wp.ofNat_beq_zero (by omega_arith)]

private theorem nibble_fact : ∀ b : BitVec 8,
    b.setWidth 32 >>> 4 = BitVec.ofNat 32 (b.toNat / 16) ∧
    b.setWidth 32 &&& 15 = BitVec.ofNat 32 (b.toNat % 16) := by decide

/-- The address of a nibble's byte: the input's pointer plus half the nibble's index. -/
theorem nibbleAddr_ok {s₀ s : State} (hp : ScratchPre s₀ 3 4) (hs : Saved s₀ (arg s₀ 3) s)
    {a i : Nat} (ha : a < 4) (hi : i < 2 ^ 32) (hesi : s.gpr .esi = BitVec.ofNat 32 i) :
    WP isa (.block [.mov .eax (.reg .esi), .shift .shr .eax 1, .alu .add .eax (.mem (at_ .esp (4 + 4 * a)))])
      s fun t => EaxKeep s t ∧ t.gpr .eax = arg s₀ a + BitVec.ofNat 32 (i / 2) := by
  refine Wp.wp_mov fun u₁ h₁ => Wp.wp_shr (by decide) fun u₂ h₂ _ => ?_
  have e₂ : u₂.gpr .eax = BitVec.ofNat 32 (i / 2) := by rw [h₂.gpr, h₁.gpr, hesi, shr1_ofNat hi]
  have hr₂ : u₂.rd ++ u₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, hs.rd, hs.wr]
  refine Wp.wp_addm (B := s₀.gpr .esp) (by rw [h₂.other _ (by decide), h₁.other _ (by decide)]; exact hs.esp)
    (by rw [hr₂]; exact hp.argIn ha) fun t ht => WP.block_nil
      ⟨(EaxKeep.of_upd h₁).trans ((EaxKeep.of_upd h₂).trans (EaxKeep.of_upd ht)), ?_⟩
  rw [ht.gpr, e₂, h₂.mem, h₁.mem, hp.arg_same hs.frame ha, BitVec.add_comm]

/-- The byte of a nibble, and the nibble's parity in ZF. -/
theorem nibbleByte_ok {s₀ s : State} (hp : ScratchPre s₀ 3 4) (hs : Saved s₀ (arg s₀ 3) s)
    {a add n i : Nat} (ha : a < 4) (hsl : SlicePre s₀ 3 (arg s₀ a + BitVec.ofNat 32 add) n)
    (hi : i < 2 * n) (hn : n ≤ 64) (hesi : s.gpr .esi = BitVec.ofNat 32 i) :
    WP isa (.block [.mov .eax (.reg .esi), .shift .shr .eax 1, .alu .add .eax (.mem (at_ .esp (4 + 4 * a))),
      .movzx8 .eax (at_ .eax add), .alu .test .esi (.imm 1)]) s fun t => EaxKeep s t ∧
      t.gpr .eax = ((Spec.Ed25519.bytesAt s₀.mem ((arg s₀ a + BitVec.ofNat 32 add).setWidth 64) n).getD
        (i / 2) 0).setWidth 32 ∧ t.zf = some (decide (i % 2 = 0)) := by
  have hn : i < 2 ^ 32 := by omega_arith
  show WP isa (.block (([.mov .eax (.reg .esi), .shift .shr .eax 1,
    .alu .add .eax (.mem (at_ .esp (4 + 4 * a)))] : List Instr) ++
    [.movzx8 .eax (at_ .eax add), .alu .test .esi (.imm 1)])) s _
  refine WP.block_append (WP.mono (nibbleAddr_ok hp hs ha hn hesi) fun u₃ ⟨k₃, e₃⟩ => ?_)
  have hA : addr (u₃.gpr .eax) add = addr (arg s₀ a + BitVec.ofNat 32 add) (i / 2) := by
    rw [e₃]; simp only [addr]
    rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 32 (i / 2))]
  have hr₃ : u₃.rd ++ u₃.wr = s₀.rd ++ s₀.wr := by rw [k₃.rd, k₃.wr, hs.rd, hs.wr]
  refine scalar_ld8 hA (by rw [hr₃]; exact slice_read hsl (by omega_arith) (by decide)) fun u₄ h₄ =>
    wp_testi fun t ht zt => WP.block_nil ⟨?_, ?_, ?_⟩
  · exact k₃.trans ((EaxKeep.of_upd h₄).trans (EaxKeep.of_fupd ht))
  · rw [ht.gpr, h₄.gpr, k₃.mem, bytesAt_getD _ _ _ _ (by omega_arith), ← addr_eq (by have := hsl.fit; omega_arith)]
    congr 1
    apply hs.frame
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hsl.sep _ (slice_contains hsl (by omega_arith) (by decide))
    · exact hsl.stk _ (slice_contains hsl (by omega_arith) (by decide))
  · rw [zt, h₄.other _ (by decide), k₃.gpr _ (by decide), hesi, and1_beq hn]

theorem digitNibble_ok {s₀ s : State} (hp : ScratchPre s₀ 3 4) (hs : Saved s₀ (arg s₀ 3) s)
    {a add n i : Nat} (ha : a < 4) (hsl : SlicePre s₀ 3 (arg s₀ a + BitVec.ofNat 32 add) n)
    (hi : i < 2 * n) (hn : n ≤ 64) (hesi : s.gpr .esi = BitVec.ofNat 32 i) :
    WP isa (digitNibble (4 + 4 * a) add) s fun t => EaxKeep s t ∧
      t.gpr .eax = BitVec.ofNat 32 (nibbleOf (Spec.Ed25519.bytesAt s₀.mem
        ((arg s₀ a + BitVec.ofNat 32 add).setWidth 64) n) i) := by
  refine WP.seq (WP.mono (nibbleByte_ok hp hs ha hsl hi hn hesi) fun u ⟨ku, eu, zu⟩ => ?_)
  refine WP.ite (!decide (i % 2 = 0)) (by show u.zf.map (!·) = _; rw [zu]; rfl) (fun h => ?_) (fun h => ?_)
  · have h1 : i % 2 = 1 := by simp at h; omega_arith
    refine Wp.wp_shr (by decide) fun t ht _ => WP.block_nil ⟨ku.trans (EaxKeep.of_upd ht), ?_⟩
    rw [ht.gpr, eu, (nibble_fact _).1, nibbleOf, ite_eq_left h1]
  · have h0 : ¬ i % 2 = 1 := by simp at h; omega_arith
    refine Wp.wp_andi fun t ht => WP.block_nil ⟨ku.trans (EaxKeep.of_upd ht), ?_⟩
    rw [ht.gpr, eu, (nibble_fact _).2, nibbleOf, ite_eq_right h0]

/-! ## Adding a digit's entry -/

theorem entryAddr_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (o : Nat) {v : Nat} (hv : 1 ≤ v)
    (hv' : v < 16) (he : s.gpr .eax = BitVec.ofNat 32 v) :
    WP isa (.block (entryAddr o)) s fun t =>
      Keep s t ∧ t.mem = s.mem ∧ t.gpr .edx = x + BitVec.ofNat 32 (o + 128 * (v - 1)) := by
  refine Wp.wp_subi fun s₁ h₁ _ _ => Wp.wp_movi fun s₂ h₂ => wp_mul fun s₃ h₃ => ?_
  refine Wp.wp_add fun s₄ h₄ _ => Wp.wp_addi fun s₅ h₅ => Wp.wp_mov fun s₆ h₆ => WP.block_nil ?_
  have hk : Keep s s₆ := (updKeep h₁).trans ((updKeep h₂).trans (h₃.keep.trans
    ((updKeep h₄).trans ((updKeep h₅).trans (updKeep h₆)))))
  have e₁ : s₁.gpr .eax = BitVec.ofNat 32 (v - 1) := by rw [h₁.gpr, he]; exact Wp.ofNat_pred hv
  have hvv : s₃.gpr .eax = BitVec.ofNat 32 (128 * (v - 1)) := by
    apply BitVec.eq_of_toNat_eq
    change VG.Proof.X25519.X86.v s₃ .eax = _
    rw [h₃.eax]
    simp only [VG.Proof.X25519.X86.v, h₂.other .eax (by decide), e₁, h₂.gpr, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show v - 1 < 2 ^ 32 by omega_arith)]
    exact congrArg (fun n => n % 2 ^ 32) (Nat.mul_comm (v - 1) 128)
  refine ⟨hk, by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_⟩
  rw [h₆.gpr, h₅.gpr, h₄.gpr, hvv, h₃.other .edi (by decide) (by decide),
    h₂.other .edi (by decide), h₁.other .edi (by decide), hc.edi]
  rw [BitVec.add_comm (BitVec.ofNat 32 (128 * (v - 1))) x, BitVec.add_assoc,
    ← BitVec.ofNat_add, Nat.add_comm (128 * (v - 1)) o]

theorem digit_test_fact : ∀ v < 16, (BitVec.ofNat 32 v &&& BitVec.ofNat 32 v == 0) = decide (v = 0) := by
  decide

theorem addDigit_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {o : Nat} (ho : 1024 ≤ o)
    (hn : o + 1920 ≤ 8192) {v : Nat} (hv : v < 16) (he : s.gpr .eax = BitVec.ofNat 32 v)
    {X a : EPoint dZ} (htab : ∀ j < 15, Rep (tablePoint s.mem x (o + 128 * j)) ((j + 1) • X))
    (hacc : Rep (point (env s.mem x) 0 1 2 3) a) (hd : env s.mem x 16 = Spec.Ed25519.d) :
    WP isa (addDigit o) s fun t => IKeep x s t ∧ t.gpr .esi = s.gpr .esi ∧
      Rep (point (env t.mem x) 0 1 2 3) (a + v • X) ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem x i = env s.mem x i := by
  have htest : WP isa (.block [.alu .test .eax (.reg .eax)]) s fun t =>
      IKeep x s t ∧ t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.zf = some (decide (v = 0)) :=
    Wp.wp_test fun t ht zt => WP.block_nil ⟨⟨by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr,
      by rw [ht.mem]; exact Frame.refl _ _⟩, ht.mem, ht.gpr, by rw [zt, he, digit_test_fact v hv]⟩
  refine WP.seq (WP.mono htest fun u ⟨ku, mu, gu, zu⟩ => ?_)
  have cu := ku.ctx hc
  refine WP.ite (!decide (v = 0)) (by show u.zf.map (!·) = _; rw [zu]; rfl) (fun h => ?_) (fun h => ?_)
  · have hv0 : v ≠ 0 := by simpa using h
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine WP.mono (entryAddr_ok cu o (by omega_arith) hv (by rw [gu]; exact he)) fun b ⟨kb, mb, pb⟩ => ?_
    have cb := kb.ctx cu
    refine WP.mono (pointFromTableQ_ok cb pb (by omega_arith) (by omega_arith)) fun c ⟨kc, ec, pc, hc'⟩ => ?_
    have cc := kc.ctx cb
    refine WP.mono (pointAddCall_ok cc (by rw [hc' 16 (Or.inr (by decide)), mb, mu]; exact hd))
      fun t ⟨kt, pt, ht⟩ => ⟨((ku.trans (IKeep.of_mem kb mb)).trans kc).trans (IKeep.of_call kt), ?_, ?_,
        fun i hi => ?_⟩
    · rw [kt.keep.esi, ec, kb.esi, gu]
    · have p0 : point (env c.mem x) 0 1 2 3 = point (env s.mem x) 0 1 2 3 := by
        simp only [point, hc' 0 (Or.inl (by decide)), hc' 1 (Or.inl (by decide)),
          hc' 2 (Or.inl (by decide)), hc' 3 (Or.inl (by decide)), mb, mu]
      rw [pt, p0, pc, mb, mu]
      have := htab (v - 1) (by omega_arith)
      rw [show v - 1 + 1 = v by omega_arith] at this
      exact pointAdd_rep hacc this
    · rw [ht i hi, hc' i (Or.inr (by omega_arith)), mb, mu]
  · have hv0 : v = 0 := by simpa using h
    subst hv0
    refine WP.block_nil ⟨ku, by rw [gu], ?_, fun i _ => by rw [mu]⟩
    rw [mu, zero_smul, add_zero]; exact hacc

/-! ## Windows -/

/-- What the windows keep: the saved state, `d`, both tables and `R`. -/
structure WinCtx (s₀ : State) (Aa : EPoint dZ) (R : Spec.Ed25519.Point) (s : State) : Prop where
  pre : VerifyPre s₀
  saved : Saved s₀ (arg s₀ 3) s
  d : env s.mem (arg s₀ 3) 16 = Spec.Ed25519.d
  ta : ∀ j < 15, Rep (tablePoint s.mem (arg s₀ 3) (1024 + 128 * j)) ((j + 1) • Aa)
  tb : ∀ j < 15, Rep (tablePoint s.mem (arg s₀ 3) (3072 + 128 * j)) ((j + 1) • (-baseAff))
  r : tablePoint s.mem (arg s₀ 3) 7808 = R

theorem WinCtx.ctx {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) : Ctx (arg s₀ 3) s :=
  h.saved.ctx h.pre.scratch.fit h.pre.scratch.wr h.pre.scratch.stk

theorem WinCtx.of_ikeep {s₀ s t : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) (k : IKeep (arg s₀ 3) s t)
    (hd : env t.mem (arg s₀ 3) 16 = env s.mem (arg s₀ 3) 16) : WinCtx s₀ Aa R t := by
  have hfit := h.pre.scratch.fit
  refine ⟨h.pre, h.saved.ikeep hfit k, hd.trans h.d, fun j hj => ?_, fun j hj => ?_, ?_⟩
  · rw [workspace_table k h.ctx _ (by omega_arith) (by omega_arith)]; exact h.ta j hj
  · rw [workspace_table k h.ctx _ (by omega_arith) (by omega_arith)]; exact h.tb j hj
  · rw [workspace_table k h.ctx _ (by decide) (by decide)]; exact h.r

end VG.Proof.Ed25519.X86

end

end


/-!
# Verification's windows: the nibbles and the loops

After the bytes of the scalars from `i` up, the sum represents
`[k / 256^i]A + [S / 256^i](-B)` (`wsum`), and after their nibbles from `n`
up, `[k / 16^n]A + [S / 16^n](-B)` (`nsum`). The leading zero bytes of `k`
above its low 32 are skipped, where the sum is zero; then each window takes
one nibble of both scalars, `S` having none from 64 up (`S < 256^32`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86 VG.Proof.Ed25519 Edwards

abbrev verificationScalar (s : State) : Nat := Spec.Ed25519.decodeLE
  (Spec.Ed25519.bytesAt s.mem ((arg s 1 + BitVec.ofNat 32 32).setWidth 64) 32)
abbrev verificationChallenge (s : State) : Nat := Spec.Ed25519.decodeLE
  (Spec.Ed25519.bytesAt s.mem ((arg s 2 + BitVec.ofNat 32 0).setWidth 64) 64)

/-- Byte `i` of `k`. -/
abbrev kByte (s₀ : State) (i : Nat) : Byte :=
  (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ 2 + BitVec.ofNat 32 0).setWidth 64) 64).getD i 0

/-- The sum after the bytes from `i` up. -/
def wsum (s₀ : State) (Aa : EPoint dZ) (i : Nat) : EPoint dZ :=
  (verificationChallenge s₀ / 256 ^ i) • Aa + (verificationScalar s₀ / 256 ^ i) • (-baseAff)

theorem kByte_val (s₀ : State) (i : Nat) :
    (kByte s₀ i).toNat = verificationChallenge s₀ / 256 ^ i % 256 := (decodeLE_byte _ i).symm

/-- The sum after the nibbles from `n` up. -/
def nsum (s₀ : State) (Aa : EPoint dZ) (n : Nat) : EPoint dZ :=
  (verificationChallenge s₀ / 16 ^ n) • Aa + (verificationScalar s₀ / 16 ^ n) • (-baseAff)

theorem nsum_two_mul (s₀ : State) (Aa : EPoint dZ) (c : Nat) : nsum s₀ Aa (2 * c) = wsum s₀ Aa c := by
  simp only [nsum, wsum, div_pow16_two_mul]

/-- Nibble `n` of `k`. -/
def kNib (s₀ : State) (n : Nat) : Nat :=
  nibbleOf (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ 2 + BitVec.ofNat 32 0).setWidth 64) 64) n

/-- Nibble `n` of `S`. -/
def sNib (s₀ : State) (n : Nat) : Nat :=
  nibbleOf (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ 1 + BitVec.ofNat 32 32).setWidth 64) 32) n

theorem kNib_lt (s₀ : State) (n : Nat) : kNib s₀ n < 16 := nibbleOf_lt _ _

theorem sNib_lt (s₀ : State) (n : Nat) : sNib s₀ n < 16 := nibbleOf_lt _ _

theorem kNib_val (s₀ : State) (n : Nat) : kNib s₀ n = verificationChallenge s₀ / 16 ^ n % 16 :=
  (decodeLE_nibble _ n).symm

theorem sNib_val (s₀ : State) (n : Nat) : sNib s₀ n = verificationScalar s₀ / 16 ^ n % 16 :=
  (decodeLE_nibble _ n).symm

/-- `S` has no nibble from 64 up. -/
theorem sNib_high (s₀ : State) {n : Nat} (hn : 64 ≤ n) : sNib s₀ n = 0 := by
  rw [sNib_val, nibble_high_zero (decodeLE_lt32 _ _) hn]

/-- `k`'s nibble `n`. -/
theorem digitK_ok {s₀ : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {n : Nat} (hn : n < 128)
    (t : State) (ht : WinCtx s₀ Aa R t) (et : t.gpr .esi = BitVec.ofNat 32 n) :
    WP isa (digitNibble 12 0) t fun u => EaxKeep t u ∧ u.gpr .eax = BitVec.ofNat 32 (kNib s₀ n) :=
  digitNibble_ok (a := 2) ht.pre.scratch ht.saved (by decide) ht.pre.challenge (by omega_arith) (by decide) et

/-- `S`'s nibble `n`. -/
theorem digitS_ok {s₀ : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {n : Nat} (hn : n < 64)
    (t : State) (ht : WinCtx s₀ Aa R t) (et : t.gpr .esi = BitVec.ofNat 32 n) :
    WP isa (digitNibble 8 32) t fun u => EaxKeep t u ∧ u.gpr .eax = BitVec.ofNat 32 (sNib s₀ n) :=
  digitNibble_ok (a := 1) ht.pre.scratch ht.saved (by decide) ht.pre.scalar (by omega_arith) (by decide) et

/-- The nibble counter leaves the top two bits of `esi` to the doublings' loop. -/
theorem esi_lt {s : State} {i : Nat} (hi : i < 2 ^ 30) (hesi : s.gpr .esi = BitVec.ofNat 32 i) :
    (s.gpr .esi).toNat < 2 ^ 30 := by
  rw [hesi, BitVec.toNat_ofNat]; omega_arith

/-- `cmp esi, 64`: CF is set exactly below `S`'s 64 nibbles. -/
theorem cmp64_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} (h : WinCtx s₀ Aa R s)
    {n : Nat} (hn : n < 128) (hesi : s.gpr .esi = BitVec.ofNat 32 n) :
    WP isa (.block [.alu .cmp .esi (.imm 64)]) s fun t => WinCtx s₀ Aa R t ∧
      t.gpr .esi = s.gpr .esi ∧ t.mem = s.mem ∧ t.cf = some (decide (n < 64)) :=
  Wp.wp_cmpi fun t ht ct _ => WP.block_nil ⟨h.of_ikeep ⟨by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr,
    by rw [ht.mem]; exact Frame.refl _ _⟩ (by rw [ht.mem]), by rw [ht.gpr], ht.mem,
    by rw [ct, hesi, Wp.toNat_ofNat_lt (by omega_arith)]; rfl⟩

/-- `S`'s digit added, below its 64 nibbles. -/
theorem addS_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} (h : WinCtx s₀ Aa R s)
    {n : Nat} (hn : n < 128) (hesi : s.gpr .esi = BitVec.ofNat 32 n) {a : EPoint dZ}
    (hacc : Rep (point (env s.mem (arg s₀ 3)) 0 1 2 3) a) :
    WP isa addS s fun t => WinCtx s₀ Aa R t ∧ t.gpr .esi = s.gpr .esi ∧
      Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) (a + sNib s₀ n • (-baseAff)) := by
  refine WP.seq (WP.mono (cmp64_ok h hn hesi) fun u ⟨wu, eu, mu, cu⟩ => ?_)
  have ru : Rep (point (env u.mem (arg s₀ 3)) 0 1 2 3) a := by rw [mu]; exact hacc
  refine WP.ite (decide (n < 64)) cu (fun hh => ?_) (fun hh => ?_)
  · have h64 : n < 64 := by simpa using hh
    refine WP.seq (WP.mono (digitS_ok h64 u wu (eu.trans hesi)) fun c ⟨kc, ec⟩ => ?_)
    have wc := wu.of_ikeep kc.ikeep (by rw [kc.mem])
    have rc : Rep (point (env c.mem (arg s₀ 3)) 0 1 2 3) a := by rw [kc.mem]; exact ru
    refine WP.mono (addDigit_ok wc.ctx (by decide) (by decide) (nibbleOf_lt _ _) ec wc.tb rc wc.d)
      fun t ⟨kt, et, rt, ht⟩ => ⟨wc.of_ikeep kt (ht 16 (by decide)), ?_, rt⟩
    rw [et, kc.gpr _ (by decide)]; exact eu
  · have h64 : 64 ≤ n := by simp at hh; omega_arith
    refine WP.block_nil ⟨wu, eu, ?_⟩
    rw [sNib_high s₀ h64, zero_smul, add_zero]; exact ru

/-- `k`'s digit added. -/
theorem addK_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} (h : WinCtx s₀ Aa R s)
    {n : Nat} (hn : n < 128) (hesi : s.gpr .esi = BitVec.ofNat 32 n) {a : EPoint dZ}
    (hacc : Rep (point (env s.mem (arg s₀ 3)) 0 1 2 3) a) :
    WP isa addK s fun t => WinCtx s₀ Aa R t ∧ t.gpr .esi = s.gpr .esi ∧
      Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) (a + kNib s₀ n • Aa) := by
  refine WP.seq (WP.mono (digitK_ok hn s h hesi) fun c ⟨kc, ec⟩ => ?_)
  have wc := h.of_ikeep kc.ikeep (by rw [kc.mem])
  have rc : Rep (point (env c.mem (arg s₀ 3)) 0 1 2 3) a := by rw [kc.mem]; exact hacc
  refine WP.mono (addDigit_ok wc.ctx (by decide) (by decide) (nibbleOf_lt _ _) ec wc.ta rc wc.d)
    fun t ⟨kt, et, rt, ht⟩ => ⟨wc.of_ikeep kt (ht 16 (by decide)), ?_, rt⟩
  rw [et, kc.gpr _ (by decide)]

theorem esiDec_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} (h : WinCtx s₀ Aa R s)
    {i : Nat} (hesi : s.gpr .esi = BitVec.ofNat 32 (i + 1)) :
    WP isa (.block [.alu .sub .esi (.imm 1)]) s fun u => WinCtx s₀ Aa R u ∧
      u.gpr .esi = BitVec.ofNat 32 i ∧ u.mem = s.mem :=
  Wp.wp_subi fun u hu _ _ => WP.block_nil ⟨h.of_ikeep (IKeep.of_counter hu) (by rw [hu.mem]),
    by rw [hu.gpr, hesi, Wp.ofNat_pred (by omega_arith), Nat.add_sub_cancel], hu.mem⟩

theorem test_zero (i : Nat) (hi : i < 2 ^ 32) :
    (BitVec.ofNat 32 i &&& BitVec.ofNat 32 i == 0) = decide (i = 0) := by
  rw [BitVec.and_self, Wp.ofNat_beq_zero hi]

/-- A window: the nibble below `n + 1`. -/
theorem nibbleStep_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) {n : Nat} (hn : n < 128) (hesi : s.gpr .esi = BitVec.ofNat 32 (n + 1))
    (hacc : Rep (point (env s.mem (arg s₀ 3)) 0 1 2 3) (nsum s₀ Aa (n + 1))) :
    WP isa nibbleStep s fun t => WinCtx s₀ Aa R t ∧ t.gpr .esi = BitVec.ofNat 32 n ∧
      t.zf = some (decide (n = 0)) ∧ Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) (nsum s₀ Aa n) := by
  refine WP.seq (WP.mono (esiDec_ok h hesi) fun u ⟨wu, eu, mu⟩ => ?_)
  have ru : Rep (point (env u.mem (arg s₀ 3)) 0 1 2 3) (nsum s₀ Aa (n + 1)) := by rw [mu]; exact hacc
  refine WP.seq (WP.mono (doubleWindow_ok wu.ctx (esi_lt (by omega_arith) eu) ru) fun b ⟨kb, eb, rb, hb⟩ => ?_)
  have wb := wu.of_ikeep kb (hb 16 (by decide))
  have ebs : b.gpr .esi = BitVec.ofNat 32 n := eb.trans eu
  refine WP.seq (WP.mono (addK_ok wb hn ebs rb) fun d ⟨wd, ed, rd⟩ => ?_)
  refine WP.seq (WP.mono (addS_ok wd hn (ed.trans ebs) rd) fun e ⟨we, ee, re⟩ => ?_)
  refine Wp.wp_test fun t ht zt => WP.block_nil ⟨we.of_ikeep ⟨by rw [ht.gpr], by rw [ht.gpr], ht.rd,
    ht.wr, by rw [ht.mem]; exact Frame.refl _ _⟩ (by rw [ht.mem]), ?_, ?_, ?_⟩
  · rw [ht.gpr, ee, ed, ebs]
  · rw [zt, ee, ed, ebs, test_zero n (by omega_arith)]
  · rw [ht.mem, nsum, ← nibble_step Aa (-baseAff) (verificationChallenge s₀) (verificationScalar s₀) n,
      ← kNib_val, ← sNib_val]
    exact re

/-! ## The loop -/

theorem loopN_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) {c : Nat} (hc0 : 0 < c) (hc : c ≤ 128) (hesi : s.gpr .esi = BitVec.ofNat 32 c)
    (hacc : Rep (point (env s.mem (arg s₀ 3)) 0 1 2 3) (nsum s₀ Aa c)) :
    WP isa (.loop nibbleStep .ne) s fun t => WinCtx s₀ Aa R t ∧
      Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) (nsum s₀ Aa 0) := by
  refine WP.loop (M := isa) (Inv := fun m t => WinCtx s₀ Aa R t ∧ 0 < m ∧ m ≤ 128 ∧
    t.gpr .esi = BitVec.ofNat 32 m ∧ Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) (nsum s₀ Aa m)) ?_ c s
    ⟨h, hc0, hc, hesi, hacc⟩
  intro m u ⟨wu, hm0, hm, eu, ru⟩
  obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega_arith⟩
  refine WP.mono (nibbleStep_ok wu (by omega_arith) eu ru) fun t ⟨wt, et, zt, rt⟩ => ?_
  by_cases hi : i = 0
  · subst hi
    exact .inl ⟨by show t.zf.map (!·) = _; rw [zt]; rfl, wt, rt⟩
  · exact .inr ⟨by show t.zf.map (!·) = _; rw [zt, decide_eq_false hi]; rfl, i, by omega_arith,
      wt, by omega_arith, by omega_arith, et, rt⟩

/-- `add esi, esi`: the bytes left to the nibbles left. -/
theorem nibbles_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {c : Nat}
    (h : WinCtx s₀ Aa R s) (hesi : s.gpr .esi = BitVec.ofNat 32 c) :
    WP isa (.block [.alu .add .esi (.reg .esi)]) s fun t => WinCtx s₀ Aa R t ∧
      t.gpr .esi = BitVec.ofNat 32 (2 * c) ∧ t.mem = s.mem :=
  Wp.wp_add fun t ht _ => WP.block_nil ⟨h.of_ikeep (IKeep.of_counter ht) (by rw [ht.mem]),
    by rw [ht.gpr, hesi, ← BitVec.ofNat_add, Nat.two_mul], ht.mem⟩

/-! ## Skipping the leading zero bytes of `k` -/

theorem skipLoad_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) {c : Nat} (hc : 1 ≤ c) (hc' : c ≤ 64) (hesi : s.gpr .esi = BitVec.ofNat 32 c) :
    WP isa (.block skipLoad) s fun t => WinCtx s₀ Aa R t ∧ t.gpr .esi = BitVec.ofNat 32 c ∧
      t.gpr .edx = BitVec.ofNat 32 (c - 1) ∧ t.zf = some (decide ((kByte s₀ (c - 1)).toNat = 0)) ∧
      t.mem = s.mem := by
  have hp := h.pre
  have hs := h.saved
  refine Wp.wp_mov fun u₁ h₁ => Wp.wp_subi fun u₂ h₂ _ _ => ?_
  have e₂ : u₂.gpr .edx = BitVec.ofNat 32 (c - 1) := by
    rw [h₂.gpr, h₁.gpr, hesi]; exact Wp.ofNat_pred hc
  have hsp : u₂.gpr .esp = s₀.gpr .esp := by
    rw [h₂.other _ (by decide), h₁.other _ (by decide)]; exact hs.esp
  have hr₂ : u₂.rd ++ u₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, hs.rd, hs.wr]
  refine Wp.wp_ldm hsp (by rw [hr₂]; exact hp.scratch.argIn (i := 2) (by decide)) fun u₃ h₃ => ?_
  have m₂ : u₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  have e₃ : u₃.gpr .eax = arg s₀ 2 := by
    rw [h₃.gpr, m₂, show (12 : Nat) = 4 + 4 * 2 from rfl]; exact hp.scratch.arg_same hs.frame (by decide)
  refine Wp.wp_add fun u₄ h₄ _ => ?_
  have e₄ : u₄.gpr .eax = arg s₀ 2 + BitVec.ofNat 32 (c - 1) := by
    rw [h₄.gpr, e₃, h₃.other .edx (by decide), e₂]
  have hA : addr (u₄.gpr .eax) 0 = addr (arg s₀ 2 + BitVec.ofNat 32 0) (c - 1) := by
    rw [e₄]; simp only [addr]
    rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 32 (c - 1))]
  have hr₄ : u₄.rd ++ u₄.wr = s₀.rd ++ s₀.wr := by rw [h₄.rd, h₄.wr, h₃.rd, h₃.wr, hr₂]
  refine scalar_ld8 hA (by rw [hr₄]; exact slice_read hp.challenge (by omega_arith) (by decide))
    fun u₅ h₅ => Wp.wp_test fun t ht zt => WP.block_nil ?_
  have hsl := hp.challenge
  have byte : s.mem (addr (arg s₀ 2 + BitVec.ofNat 32 0) (c - 1)) = kByte s₀ (c - 1) := by
    rw [kByte, bytesAt_getD _ _ _ _ (by omega_arith), ← addr_eq (by have := hsl.fit; omega_arith)]
    apply hs.frame
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hsl.sep _ (slice_contains hsl (by omega_arith) (by decide))
    · exact hsl.stk _ (slice_contains hsl (by omega_arith) (by decide))
  have mt : t.mem = s.mem := by rw [ht.mem, h₅.mem, h₄.mem, h₃.mem, m₂]
  have k₅ : IKeep (arg s₀ 3) s t := ⟨by rw [ht.gpr, h₅.other _ (by decide), h₄.other _ (by decide),
      h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide)],
    by rw [ht.gpr, h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide),
      h₂.other _ (by decide), h₁.other _ (by decide)],
    by rw [ht.rd, h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd], by rw [ht.wr, h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr],
    by rw [mt]; exact Frame.refl _ _⟩
  refine ⟨h.of_ikeep k₅ (by rw [mt]), ?_, ?_, ?_, mt⟩
  · rw [ht.gpr, h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide),
      h₂.other _ (by decide), h₁.other _ (by decide), hesi]
  · rw [ht.gpr, h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide), e₂]
  · rw [zt, h₅.gpr, h₄.mem, h₃.mem, m₂, byte, BitVec.and_self]
    generalize kByte s₀ (c - 1) = b
    revert b; decide

/-- With `c` bytes of the scalars left. -/
def LoopAt (s₀ : State) (Aa : EPoint dZ) (R : Spec.Ed25519.Point) (c : Nat) (t : State) : Prop :=
  WinCtx s₀ Aa R t ∧ t.gpr .esi = BitVec.ofNat 32 c ∧
    Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) (wsum s₀ Aa c)

/-- Skipping, with `32 + m` bytes of `k` left, all of them above zero. -/
def SkipAt (s₀ : State) (Aa : EPoint dZ) (R : Spec.Ed25519.Point) (m : Nat) (t : State) : Prop :=
  WinCtx s₀ Aa R t ∧ 0 < m ∧ m ≤ 32 ∧ t.gpr .esi = BitVec.ofNat 32 (32 + m) ∧
    verificationChallenge s₀ / 256 ^ (32 + m) = 0 ∧ Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) 0

/-- Whether the skipping goes on below `32 + m` bytes: the byte below is zero, and not the last
of `k` alone. -/
def skipOn (s₀ : State) (m : Nat) : Bool :=
  decide ((kByte s₀ (32 + m - 1)).toNat = 0) && decide (m ≠ 1)

/-- Where the skipping stops, if it does below `32 + m` bytes. -/
def skipEnd (s₀ : State) (m : Nat) : Nat :=
  if (kByte s₀ (32 + m - 1)).toNat = 0 then 32 + m - 1 else 32 + m

theorem wsum_zero {s₀ : State} {Aa : EPoint dZ} {c : Nat} (hc : 32 ≤ c)
    (hk : verificationChallenge s₀ / 256 ^ c = 0) : wsum s₀ Aa c = 0 := by
  rw [wsum, hk, high_zero (decodeLE_lt32 _ _) hc, zero_smul, zero_smul, add_zero]

theorem skipBody_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {m : Nat}
    (h : SkipAt s₀ Aa R m s) :
    WP isa skipBody s fun t => t.zf.map (!·) = some (skipOn s₀ m) ∧
      (skipOn s₀ m = false → 32 ≤ skipEnd s₀ m ∧ skipEnd s₀ m ≤ 64 ∧ LoopAt s₀ Aa R (skipEnd s₀ m) t) ∧
      (skipOn s₀ m = true → SkipAt s₀ Aa R (m - 1) t) := by
  obtain ⟨wu, hm0, hm, eu, ku, ru⟩ := h
  refine WP.seq (WP.mono (skipLoad_ok wu (by omega_arith) (by omega_arith) eu) fun v ⟨wv, ev, dv, zv, mv⟩ => ?_)
  have rv : Rep (point (env v.mem (arg s₀ 3)) 0 1 2 3) 0 := by rw [mv]; exact ru
  refine WP.ite (!decide ((kByte s₀ (32 + m - 1)).toNat = 0)) (by show v.zf.map (!·) = _; rw [zv]; rfl)
    (fun hh => ?_) (fun hh => ?_)
  · have hnz : (kByte s₀ (32 + m - 1)).toNat ≠ 0 := by simpa using hh
    have son : skipOn s₀ m = false := by simp only [skipOn, decide_eq_false hnz, Bool.false_and]
    have sen : skipEnd s₀ m = 32 + m := by simp only [skipEnd, hnz, ↓reduceIte]
    refine Wp.wp_cmp fun t ht _ zt => WP.block_nil ⟨?_, fun _ => ?_, fun h => absurd h (by rw [son]; decide)⟩
    · rw [zt, son]; simp
    · rw [sen]
      refine ⟨by omega_arith, by omega_arith, wv.of_ikeep ⟨by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr,
        by rw [ht.mem]; exact Frame.refl _ _⟩ (by rw [ht.mem]), by rw [ht.gpr, ev], ?_⟩
      rw [ht.mem, wsum_zero (by omega_arith) ku]; exact rv
  · have hz : (kByte s₀ (32 + m - 1)).toNat = 0 := by simpa using hh
    have k' : verificationChallenge s₀ / 256 ^ (32 + m - 1) = 0 := by
      have := div_split (verificationChallenge s₀) (32 + m - 1)
      rw [show 32 + m - 1 + 1 = 32 + m by omega_arith, ku, ← kByte_val, hz] at this
      exact this
    have son : skipOn s₀ m = decide (m ≠ 1) := by
      simp only [skipOn, decide_eq_true hz, Bool.true_and]
    have sen : skipEnd s₀ m = 32 + m - 1 := by simp only [skipEnd, hz, ↓reduceIte]
    refine Wp.wp_mov fun w hw => Wp.wp_cmpi fun t ht _ zt => WP.block_nil ?_
    have ww : WinCtx s₀ Aa R t := (wv.of_ikeep (IKeep.of_counter hw) (by rw [hw.mem])).of_ikeep
      ⟨by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr, by rw [ht.mem]; exact Frame.refl _ _⟩ (by rw [ht.mem])
    have et : t.gpr .esi = BitVec.ofNat 32 (32 + m - 1) := by rw [ht.gpr, hw.gpr, dv]
    have rt : Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) 0 := by rw [ht.mem, hw.mem]; exact rv
    have zt' : t.zf = some (decide (32 + m - 1 = 32)) := by
      rw [zt, hw.gpr, dv, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl,
        Wp.sub_beq (by omega_arith) (by omega_arith)]
    refine ⟨?_, fun hf => ?_, fun hn => ?_⟩
    · rw [zt', son]
      by_cases h1 : m = 1
      · subst h1; rfl
      · rw [decide_eq_false (show ¬(32 + m - 1 = 32) by omega_arith), decide_eq_true h1]; rfl
    · have h1 : m = 1 := by
        rw [son] at hf
        by_contra hne
        rw [decide_eq_true hne] at hf
        cases hf
      subst h1
      rw [sen]
      exact ⟨by decide, by decide, ww, et, by rw [wsum_zero (le_refl _) k']; exact rt⟩
    · have h1 : m ≠ 1 := by
        rw [son] at hn
        exact of_decide_eq_true hn
      exact ⟨ww, by omega_arith, by omega_arith, by rw [et]; congr 1; omega_arith,
        by rw [show 32 + (m - 1) = 32 + m - 1 by omega_arith]; exact k', rt⟩

theorem skipZero_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) (hesi : s.gpr .esi = BitVec.ofNat 32 64)
    (hacc : Rep (point (env s.mem (arg s₀ 3)) 0 1 2 3) 0) :
    WP isa skipZero s fun t => ∃ c, 32 ≤ c ∧ c ≤ 64 ∧ LoopAt s₀ Aa R c t := by
  have high_zero_64 : verificationChallenge s₀ / 256 ^ (32 + 32) = 0 := Nat.div_eq_of_lt (decodeLE_lt64 _ _)
  refine WP.loop (M := isa) (Inv := fun m t => SkipAt s₀ Aa R m t) ?_ 32 s
    ⟨h, by decide, by decide, hesi, high_zero_64, hacc⟩
  intro m u hu
  have hm0 := hu.2.1
  refine WP.mono (skipBody_ok hu) fun t ⟨zt, ft, tt⟩ => ?_
  cases hs : skipOn s₀ m
  · exact .inl ⟨by show t.zf.map (!·) = _; rw [zt, hs], skipEnd s₀ m, ft hs⟩
  · exact .inr ⟨by show t.zf.map (!·) = _; rw [zt, hs], m - 1, by omega_arith, tt hs⟩

/-! ## The whole multiplication -/

theorem Saved.frame2s {s₀ s t : State} {x : BitVec 32} (h : Saved s₀ x s) (hx : x.toNat + 8192 ≤ 2 ^ 32)
    (hk : ScalarKeep s t) {o n o' n' : Nat} (hf : Frame [sub x o n, sub x o' n', callStk s] s.mem t.mem)
    (h1 : 16 ≤ o) (h2 : o + n ≤ 8192) (h3 : 16 ≤ o') (h4 : o' + n' ≤ 8192) (h5 : o < 8192)
    (h6 : o' < 8192) : Saved s₀ x t := by
  apply h.of_frame hk hf
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (by rw [scR_eq]; exact sub_sub hx (Nat.zero_le _) h2 h5)
    · exact .inl (by rw [scR_eq]; exact sub_sub hx (Nat.zero_le _) h4 h6)
    · exact .inr rfl
  · intro p hp r hr
    have := savedSlots_bound p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sub_disj (by omega_arith) (by omega_arith) (Or.inl (by omega_arith))
    · exact sub_disj (by omega_arith) (by omega_arith) (Or.inl (by omega_arith))
    · rw [callStk, h.esp]
      exact h.stk.2.sub_left (by rw [scR_eq]; exact sub_sub hx (Nat.zero_le _) (by omega_arith) (by omega_arith))

theorem windowPrep_ok {s₀ s : State} (hp : VerifyPre s₀) (hs : Saved s₀ (arg s₀ 3) s)
    {A R : Spec.Ed25519.Point} {Aa : EPoint dZ} (hA : Rep A Aa)
    (ha : tablePoint s.mem (arg s₀ 3) 7680 = A) (hr : tablePoint s.mem (arg s₀ 3) 7808 = R)
    (htb : ∀ j < 15, Rep (tablePoint s.mem (arg s₀ 3) (3072 + 128 * j)) ((j + 1) • (-baseAff))) :
    WP isa windowPrep s fun t => WinCtx s₀ Aa R t ∧ t.gpr .esi = BitVec.ofNat 32 64 ∧
      Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) 0 := by
  have hfit := hp.scratch.fit
  have hc := hs.ctx hfit hp.scratch.wr hp.scratch.stk
  refine WP.seq (WP.mono (fieldCode_ok [.const 16 Spec.Ed25519.d] hc) fun a ⟨ka, ea⟩ => ?_)
  have sa := hs.ikeep hfit (IKeep.of_field ka)
  have ca := ka.ctx hc
  have tpa : ∀ o, 928 ≤ o → o + 128 ≤ 8192 → tablePoint a.mem (arg s₀ 3) o = tablePoint s.mem (arg s₀ 3) o :=
    fun o h1 h2 => tablePoint_frame hfit ka.frame (by decide) h2 (Or.inr h1)
  refine WP.seq (WP.mono (aTable_ok ca hA (by rw [tpa 7680 (by decide) (by decide)]; exact ha)
    (by rw [ea]; rfl)) fun b hb => ?_)
  have sb := sa.frame2s hfit hb.keep hb.frame (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have cb := sb.ctx hfit hp.scratch.wr hp.scratch.stk
  rw [windowInit, WP.block_append_iff]
  refine WP.mono (fieldCode_ok _ cb) fun d ⟨kd, ed⟩ => ?_
  refine Wp.wp_movi fun e he => WP.block_nil ?_
  have ke : IKeep (arg s₀ 3) b e := (IKeep.of_field kd).trans (IKeep.of_counter he)
  have de : env e.mem (arg s₀ 3) 16 = env b.mem (arg s₀ 3) 16 := by rw [he.mem, ed]; rfl
  refine ⟨⟨hp, sb.ikeep hfit ke, de.trans hb.d, fun j hj => ?_, fun j hj => ?_, ?_⟩, he.gpr, ?_⟩
  · rw [workspace_table ke cb _ (by omega_arith) (by omega_arith)]
    exact hb.table j hj
  · rw [workspace_table ke cb _ (by omega_arith) (by omega_arith),
      tablePoint_frame2s ca hb.frame (by decide) (by decide) (by omega_arith) (Or.inr (by omega_arith)) (Or.inr (by omega_arith)),
      tpa _ (by omega_arith) (by omega_arith)]
    exact htb j hj
  · rw [workspace_table ke cb _ (by decide) (by decide),
      tablePoint_frame2s ca hb.frame (by decide) (by decide) (by decide) (Or.inr (by decide))
        (Or.inr (by decide)), tpa 7808 (by decide) (by decide)]
    exact hr
  · rw [he.mem, ed, constPoint_eval]; exact identity_rep

theorem windowMultiply_ok {s₀ s : State} (hp : VerifyPre s₀) (hs : Saved s₀ (arg s₀ 3) s)
    {A R : Spec.Ed25519.Point} {Aa : EPoint dZ} (hA : Rep A Aa)
    (ha : tablePoint s.mem (arg s₀ 3) 7680 = A) (hr : tablePoint s.mem (arg s₀ 3) 7808 = R)
    (htb : ∀ j < 15, Rep (tablePoint s.mem (arg s₀ 3) (3072 + 128 * j)) ((j + 1) • (-baseAff))) :
    WP isa windowMultiply s fun t => WinCtx s₀ Aa R t ∧
      Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3)
        (verificationChallenge s₀ • Aa + verificationScalar s₀ • (-baseAff)) := by
  refine WP.seq (WP.mono (windowPrep_ok hp hs hA ha hr htb) fun e ⟨we, ee, re⟩ => ?_)
  refine WP.seq (WP.mono (skipZero_ok we ee re) fun f ⟨c', hc1, hc2, wf, ef, rf⟩ => ?_)
  refine WP.seq (WP.mono (nibbles_ok wf ef) fun g ⟨wg, eg, mg⟩ => ?_)
  refine WP.mono (loopN_ok wg (by omega_arith) (by omega_arith) eg (by rw [mg, nsum_two_mul]; exact rf))
    fun t ⟨wt, rt⟩ => ⟨wt, ?_⟩
  simpa only [nsum, pow_zero, Nat.div_one] using rt

end VG.Proof.Ed25519.X86
