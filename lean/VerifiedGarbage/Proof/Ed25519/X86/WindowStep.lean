import VerifiedGarbage.Proof.Ed25519.X86.WindowTables
import VerifiedGarbage.Proof.Ed25519.X86.VerifyContract
import VerifiedGarbage.Proof.Ed25519.X86.InputSlice
import VerifiedGarbage.Proof.Ed25519.WindowNibble

/-!
# Verification's windows

A window doubles the sum four times (`dbl-2008-hwcd`, `dblPoint_rep`), reads a
digit of a scalar from the inputs (its nibble `esi`), and adds the digit's
entry of a table, unless the digit is zero. The sum represents a
multiple of `A` plus a multiple of `-B` throughout (`Rep`).
-/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86 VG.Proof.Ed25519 Edwards
open VG.Impl.X25519.X86 (sc at_)

/-! ## Doublings -/

theorem dblOps_eval (e : Env) : point (evalOps dblOps e) 0 1 2 3 = dblPoint (point e 0 1 2 3) := rfl

theorem dbl_ok {s : State} {x : BitVec 32} (hc : Ctx x s) {a : EPoint dZ}
    (h : Rep (point (env s.mem x) 0 1 2 3) a) :
    WP isa dbl s fun t => CallKeep x s t ∧ Rep (point (env t.mem x) 0 1 2 3) (a + a) ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem x i = env s.mem x i := by
  refine WP.mono (fieldProg_ok dblOps hc) fun t ⟨kt, vt⟩ => ⟨kt, ?_, fun i hi => ?_⟩
  · rw [vt, dblOps_eval]; exact dblPoint_rep h.proj
  · rw [vt]; exact point_ops_high _ (by decide) _ i hi

theorem two_smul_add (a : EPoint dZ) (n : Nat) : n • a + n • a = (2 * n) • a := by
  rw [← two_nsmul, smul_smul]

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
  · congr 1; omega
  · simp only [decide_eq_decide]; omega

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
  unfold dblStep
  refine WP.seq (WP.mono (dbl_ok (kt.ctx hc) rt) fun u ⟨ku, ru, hu⟩ => ?_)
  refine wp_addiC fun v hv cv => WP.block_nil ?_
  have eu : (u.gpr .esi).toNat = (s.gpr .esi).toNat + (4 - n) * 2 ^ 30 := by rw [ku.keep.esi]; exact he
  obtain ⟨ev, cv'⟩ := dblCount_step hesi h1 h4 eu
  rw [cv'] at cv
  have kv : IKeep x s v := kt.trans ((IKeep.of_call ku).trans (IKeep.of_counter hv))
  have rv : Rep (point (env v.mem x) 0 1 2 3) ((2 ^ (4 - (n - 1)) : Nat) • a) := by
    rw [hv.mem, show 4 - (n - 1) = (4 - n) + 1 by omega, pow_succ, mul_comm, ← smul_smul, two_nsmul]
    exact ru
  have hv16 : ∀ i : Slot, 16 ≤ i.val → env v.mem x i = env s.mem x i :=
    fun i hi => by rw [hv.mem, hu i hi, ht i hi]
  rw [← hv.gpr] at ev
  by_cases hn : n = 1
  · subst hn
    refine .inl ⟨by simp only [eval, cv]; rfl, kv, ?_, by simpa using rv, hv16⟩
    apply BitVec.eq_of_toNat_eq
    rw [ev]; omega
  · refine .inr ⟨by simp only [eval, cv, hn]; rfl, n - 1, by omega, by omega, by omega,
      by rw [ev, Nat.mod_eq_of_lt (by omega)], kv, rv, hv16⟩

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
  omega

theorem and1_beq {i : Nat} (hi : i < 2 ^ 32) :
    (BitVec.ofNat 32 i &&& 1 == 0) = decide (i % 2 = 0) := by
  have : BitVec.ofNat 32 i &&& 1 = BitVec.ofNat 32 (i % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
    simp only [BitVec.toNat_ofNat]
    omega
  rw [this, Wp.ofNat_beq_zero (by omega)]

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
  have hn : i < 2 ^ 32 := by omega
  show WP isa (.block (([.mov .eax (.reg .esi), .shift .shr .eax 1,
    .alu .add .eax (.mem (at_ .esp (4 + 4 * a)))] : List Instr) ++
    [.movzx8 .eax (at_ .eax add), .alu .test .esi (.imm 1)])) s _
  refine WP.block_append (WP.mono (nibbleAddr_ok hp hs ha hn hesi) fun u₃ ⟨k₃, e₃⟩ => ?_)
  have hA : addr (u₃.gpr .eax) add = addr (arg s₀ a + BitVec.ofNat 32 add) (i / 2) := by
    rw [e₃]; simp only [addr]
    rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 32 (i / 2))]
  have hr₃ : u₃.rd ++ u₃.wr = s₀.rd ++ s₀.wr := by rw [k₃.rd, k₃.wr, hs.rd, hs.wr]
  refine scalar_ld8 hA (by rw [hr₃]; exact slice_read hsl (by omega) (by decide)) fun u₄ h₄ =>
    wp_testi fun t ht zt => WP.block_nil ⟨?_, ?_, ?_⟩
  · exact k₃.trans ((EaxKeep.of_upd h₄).trans (EaxKeep.of_fupd ht))
  · rw [ht.gpr, h₄.gpr, k₃.mem, bytesAt_getD _ _ _ _ (by omega), ← addr_eq (by have := hsl.fit; omega)]
    congr 1
    apply hs.frame
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hsl.sep _ (slice_contains hsl (by omega) (by decide))
    · exact hsl.stk _ (slice_contains hsl (by omega) (by decide))
  · rw [zt, h₄.other _ (by decide), k₃.gpr _ (by decide), hesi, and1_beq hn]

theorem digitNibble_ok {s₀ s : State} (hp : ScratchPre s₀ 3 4) (hs : Saved s₀ (arg s₀ 3) s)
    {a add n i : Nat} (ha : a < 4) (hsl : SlicePre s₀ 3 (arg s₀ a + BitVec.ofNat 32 add) n)
    (hi : i < 2 * n) (hn : n ≤ 64) (hesi : s.gpr .esi = BitVec.ofNat 32 i) :
    WP isa (digitNibble (4 + 4 * a) add) s fun t => EaxKeep s t ∧
      t.gpr .eax = BitVec.ofNat 32 (nibbleOf (Spec.Ed25519.bytesAt s₀.mem
        ((arg s₀ a + BitVec.ofNat 32 add).setWidth 64) n) i) := by
  refine WP.seq (WP.mono (nibbleByte_ok hp hs ha hsl hi hn hesi) fun u ⟨ku, eu, zu⟩ => ?_)
  refine WP.ite (!decide (i % 2 = 0)) (by show u.zf.map (!·) = _; rw [zu]; rfl) (fun h => ?_) (fun h => ?_)
  · have h1 : i % 2 = 1 := by simp at h; omega
    refine Wp.wp_shr (by decide) fun t ht _ => WP.block_nil ⟨ku.trans (EaxKeep.of_upd ht), ?_⟩
    rw [ht.gpr, eu, (nibble_fact _).1, nibbleOf, ite_eq_left h1]
  · have h0 : ¬ i % 2 = 1 := by simp at h; omega
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
    rw [Nat.mod_eq_of_lt (show v - 1 < 2 ^ 32 by omega)]
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
    refine WP.mono (entryAddr_ok cu o (by omega) hv (by rw [gu]; exact he)) fun b ⟨kb, mb, pb⟩ => ?_
    have cb := kb.ctx cu
    refine WP.mono (pointFromTableQ_ok cb pb (by omega) (by omega)) fun c ⟨kc, ec, pc, hc'⟩ => ?_
    have cc := kc.ctx cb
    refine WP.mono (pointAdd_ok cc (by rw [hc' 16 (Or.inr (by decide)), mb, mu]; exact hd))
      fun t ⟨kt, pt, ht⟩ => ⟨((ku.trans (IKeep.of_mem kb mb)).trans kc).trans (IKeep.of_call kt), ?_, ?_,
        fun i hi => ?_⟩
    · rw [kt.keep.esi, ec, kb.esi, gu]
    · have p0 : point (env c.mem x) 0 1 2 3 = point (env s.mem x) 0 1 2 3 := by
        simp only [point, hc' 0 (Or.inl (by decide)), hc' 1 (Or.inl (by decide)),
          hc' 2 (Or.inl (by decide)), hc' 3 (Or.inl (by decide)), mb, mu]
      rw [pt, p0, pc, mb, mu]
      have := htab (v - 1) (by omega)
      rw [show v - 1 + 1 = v by omega] at this
      exact pointAdd_rep hacc this
    · rw [ht i hi, hc' i (Or.inr (by omega)), mb, mu]
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
  · rw [workspace_table k h.ctx _ (by omega) (by omega)]; exact h.ta j hj
  · rw [workspace_table k h.ctx _ (by omega) (by omega)]; exact h.tb j hj
  · rw [workspace_table k h.ctx _ (by decide) (by decide)]; exact h.r

end VG.Proof.Ed25519.X86
