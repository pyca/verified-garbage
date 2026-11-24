module

import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.X448.X86.Columns
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-!
# X448 on x86 (32-bit): addition, subtraction, and multiplication by a24

`addSub` and `mulA24` (`Impl/X448/X86.lean`), through the pointers `esi`,
`ebx` and `ebp` to the operands and the result: a carry chain (or a row of
products), whose carry out of 448 bits `foldChain` folds by
`2^448 = 2^224 + 1`, and then a carry of that, which its third chain, of the
low eight words, does not carry out of.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16
open VG.Proof.X25519.X86 (num num_succ num_congr num_add num_mul num_lt PassRel)

/-! ## Numbers of 32-bit words -/

theorem num_zero (n : Nat) : num (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [num_succ, ih, Nat.mul_zero]

theorem num_split (f : Nat → Nat) (a b : Nat) :
    num f (a + b) = num f a + (2 ^ 32) ^ a * num (fun i => f (a + i)) b := by
  induction b with
  | zero => simp only [Nat.add_zero, num, Nat.mul_zero]
  | succ b ih =>
    rw [Nat.add_succ, num_succ, num_succ, ih, Nat.pow_add, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

/-- A number whose words but the first are zero. -/
theorem num_first {f : Nat → Nat} {n : Nat} (h : ∀ k < n + 1, k ≠ 0 → f k = 0) : num f (n + 1) = f 0 := by
  rw [Nat.add_comm, num_split,
    num_congr (g := fun _ => 0) (fun i hi => h (1 + i) (by omega_arith) (by omega_arith)), num_zero,
    Nat.mul_zero, Nat.add_zero]
  simp only [num, Nat.pow_zero, Nat.one_mul, Nat.zero_add]

theorem pow7 : ((2 : Nat) ^ 32) ^ 7 = half := by decide +kernel
theorem pow14 : ((2 : Nat) ^ 32) ^ 14 = full := by decide +kernel
theorem pow8 : ((2 : Nat) ^ 32) ^ 8 = half * 2 ^ 32 := by decide +kernel

/-- The operands of a fold of `c`. -/
def foldV (c k : Nat) : Nat := if k = 0 ∨ k = 7 then c else 0

theorem foldV_14 (c : Nat) : num (foldV c) 14 = (half + 1) * c := by
  rw [show num (foldV c) 14 = num (foldV c) (7 + 7) from rfl, num_split, pow7,
    num_first (f := foldV c) (n := 6) (fun k hk h0 => ite_eq_right (by omega_arith)),
    num_first (f := fun i => foldV c (7 + i)) (n := 6) (fun k hk h0 => ite_eq_right (by omega_arith))]
  simp only [foldV, true_or, or_true, ite_true, Nat.add_zero]
  rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem foldV_8 (c : Nat) : num (foldV c) 8 = (half + 1) * c := by
  rw [show num (foldV c) 8 = num (foldV c) (7 + 1) from rfl, num_split, pow7,
    num_first (f := foldV c) (n := 6) (fun k hk h0 => ite_eq_right (by omega_arith))]
  simp only [foldV, num, true_or, or_true, ite_true, Nat.add_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
  rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem add_mod_cancel {a b c n : Nat} (h : (a + c) % n = (b + c) % n) : a % n = b % n := by
  have hn : (n * c - c + c) = n * c ∨ n = 0 := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exact .inr h0
    · exact .inl (Nat.sub_add_cancel (Nat.le_mul_of_pos_left c h0))
  rcases hn with hn | rfl
  · have k := congrArg (fun x => (x + (n * c - c)) % n) h
    simp only [Nat.mod_add_mod] at k
    rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm c, hn, Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left] at k
    exact k
  · simp only [Nat.mod_zero] at h ⊢; omega

/-! ## The fold of a carry -/

theorem full_mul (c : Nat) : full * c = Spec.X448.P * c + (half + 1) * c := by
  rw [full_eq, Nat.add_mul]

/-- The two chains of `foldChain`, for the number `R₁` and the carry `c₁`: `R₂` after the first, of
which the low eight words are `w` and the rest `hi`, and `r` for `w` after the second. -/
structure Folded (op : AluOp) (R₁ c₁ R : Nat) : Prop where
  out : ∃ R₂ w r hi c₂ c₃ : Nat, PassRel op R₁ ((half + 1) * c₁) 0 R₂ c₂ full ∧
    PassRel op w ((half + 1) * c₂) 0 r c₃ (half * 2 ^ 32) ∧ R₂ = w + half * 2 ^ 32 * hi ∧
    R = r + half * 2 ^ 32 * hi ∧ c₂ ≤ 1 ∧ c₃ ≤ 1 ∧ R₂ < full ∧ r < half * 2 ^ 32 ∧ w < half * 2 ^ 32

theorem folded_add {R₁ c₁ R : Nat} (h : Folded .adc R₁ c₁ R) (hR : R₁ < full) (hc : c₁ < 2 ^ 31) :
    R % Spec.X448.P = (R₁ + full * c₁) % Spec.X448.P := by
  obtain ⟨R₂, w, r, hi, c₂, c₃, h₂, h₃, eR, eF, b₂, b₃, lR, lr, lw⟩ := h.out
  rw [PassRel, ite_eq_left rfl, Nat.add_zero] at h₂ h₃
  have z₃ : c₃ = 0 := by
    simp only [full, half, radix, Nat.reducePow] at h₂ h₃ eR lR hR lw lr
    omega_using [h₂, h₃, eR, lR, hR, lw, lr, hc, b₂, b₃]
  rw [z₃, Nat.mul_zero, Nat.add_zero] at h₃
  have e : R + Spec.X448.P * (c₁ + c₂) = R₁ + full * c₁ := by
    rw [full_mul] at h₂ ⊢
    rw [Nat.mul_add]
    omega_using [h₂, h₃, eR, eF]
  rw [← e, Nat.add_mul_mod_self_left]

theorem folded_sub {R₁ c₁ R : Nat} (h : Folded .sbb R₁ c₁ R) (hR : R₁ < full) (hc : c₁ ≤ 1) :
    (R + full * c₁) % Spec.X448.P = R₁ % Spec.X448.P := by
  obtain ⟨R₂, w, r, hi, c₂, c₃, h₂, h₃, eR, eF, b₂, b₃, lR, lr, lw⟩ := h.out
  rw [PassRel, ite_eq_right (by decide), Nat.add_zero] at h₂ h₃
  have z₃ : c₃ = 0 := by
    simp only [full, half, radix, Nat.reducePow] at h₂ h₃ eR lR hR lw lr
    omega_using [h₂, h₃, eR, lR, hR, lw, lr, hc, b₂, b₃]
  rw [z₃, Nat.mul_zero, Nat.add_zero] at h₃
  have e : R + full * c₁ = R₁ + Spec.X448.P * (c₁ + c₂) := by
    rw [full_mul] at h₂ ⊢
    rw [Nat.mul_add]
    omega_using [h₂, h₃, eR, eF]
  rw [e, Nat.add_mul_mod_self_left]

/-- The address of word `k` at `r`, which points at `d`, from a state whose registers but `rs` are `s`'s. -/
theorem ptr_ea {s t : State} {base : Addr} (hs : Scr s base) {r : Reg} {d k : Nat} {rs : List Reg}
    (hp : s.gpr r = s.gpr .edi + BitVec.ofNat 32 d) (hk : Keeps rs s t) (hr : r ∉ rs) (he : .edi ∉ rs)
    (hd : d + 4 * k < 8192) : t.ea (wordAt r k) = off base (d + 4 * k) :=
  (hs.of_keeps hk he).ea_ptr (by rw [hk.1 _ hr, hk.1 _ he]; exact hp) hd

theorem readMem {s : State} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hr : InRegions (s.rd ++ s.wr) a 4) :
    readSrc s (.mem m) = some (s.mem.readW a 32) := by
  simp only [readSrc, ha, State.load32, hr, ite_true]

theorem foldSrc_read {s t : State} {c : Nat} (hc : s.gpr .ecx = BitVec.ofNat 32 c) (hk : Keeps [.eax] s t) (k : Nat) :
    readSrc t (foldSrc k) = some (BitVec.ofNat 32 (foldV c k)) := by
  unfold foldSrc foldV
  split
  · exact congrArg some ((hk.1 _ (by decide)).trans hc)
  · rfl

theorem foldV_lt {c : Nat} (hc : c < 2 ^ 32) (k : Nat) : (BitVec.ofNat 32 (foldV c k)).toNat = foldV c k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  unfold foldV
  split
  · exact hc
  · decide

/-- The carry `c` of 448 bits folded into the element at `ebp`. -/
theorem foldChain_ok {op : AluOp} (hop : op = .adc ∨ op = .sbb) {s : State} {base : Addr} (hs : Scr s base)
    {o c : Nat} (ho : Slot o) (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 o) (hcf : s.cf = some false)
    (hc : s.gpr .ecx = BitVec.ofNat 32 c) (hlt : c < 2 ^ 32) :
    WP isa (.block (foldChain op)) s fun t =>
      Folded op (fe s.mem base o) c (fe t.mem base o) ∧ Outside base o 56 s.mem t.mem ∧ Keeps [.eax, .ecx] s t := by
  have ho' : o + 56 ≤ 3584 := ho
  unfold foldChain
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (chain_ok hop hs (yo := o) (xo := o) (v := fun k => BitVec.ofNat 32 (foldV c k)) hcf 14 (by omega_arith)
    (by omega_arith) (.inl rfl) (fun k hk t tk => ?_) (fun k _ t tk _ => foldSrc_read hc tk k))
    fun t₁ ⟨k₁, m₁, c₂, f₁, r₁⟩ => ?_
  · have := ptr_ea hs (k := k) hp tk (by decide) (by decide) (by omega_arith)
    exact ⟨this, this⟩
  rw [WP.block_append_iff]
  refine WP.mono (carry1_ok f₁) fun t₂ ⟨f₂, e₂, m₂, k₂⟩ => ?_
  have k₁₂ : Keeps [.eax, .ecx] s t₂ := (k₁.mono (by decide)).trans (k₂.mono (by decide))
  have hs₂ := hs.of_keeps k₁₂ (by decide)
  have hp₂ : t₂.gpr .ebp = t₂.gpr .edi + BitVec.ofNat 32 o := by
    rw [k₁₂.1 _ (by decide), k₁₂.1 _ (by decide)]; exact hp
  refine WP.mono (chain_ok hop hs₂ (yo := o) (xo := o) (v := fun k => BitVec.ofNat 32 (foldV c₂.toNat k)) f₂ 8
    (by omega_arith) (by omega_arith) (.inl rfl) (fun k hk t tk => ?_) (fun k _ t tk _ => foldSrc_read e₂ tk k))
    fun t₃ ⟨k₃, m₃, c₃, _, r₃⟩ => ?_
  · have := ptr_ea hs₂ (k := k) hp₂ tk (by decide) (by decide) (by omega_arith)
    exact ⟨this, this⟩
  have b : ∀ d : Bool, d.toNat ≤ 1 := by decide
  have hi : num (fun i => limbs t₃.mem base o (8 + i)) 6 = num (fun i => limbs t₁.mem base o (8 + i)) 6 :=
    num_congr fun i hi => by
      show (word t₃.mem base (o + 4 * (8 + i))).toNat = _
      rw [m₃.word (Or.inr (by omega_arith)) (by omega_arith), m₂]
  have sp : ∀ m, fe m base o = num (limbs m base o) 8 + half * 2 ^ 32 * num (fun i => limbs m base o (8 + i)) 6 :=
    fun m => by rw [← pow8]; exact num_split _ 8 6
  have l8 : ∀ m, num (limbs m base o) 8 < half * 2 ^ 32 := fun m => by
    rw [← pow8]; exact num_lt fun _ _ => BitVec.isLt _
  rw [pow14, num_congr (fun k _ => foldV_lt hlt k), foldV_14] at r₁
  rw [pow8, num_congr (fun k _ => foldV_lt (Nat.lt_of_le_of_lt (b c₂) (by decide)) k), foldV_8, m₂] at r₃
  refine ⟨⟨fe t₁.mem base o, num (limbs t₁.mem base o) 8, num (limbs t₃.mem base o) 8,
    num (fun i => limbs t₁.mem base o (8 + i)) 6, c₂.toNat, c₃.toNat, r₁, r₃, sp _, ?_, b _, b _, fe_lt _ _ _,
    l8 _, l8 _⟩, ?_, k₁₂.trans (k₃.mono (by decide))⟩
  · rw [sp, hi]
  · rw [m₂] at m₃
    exact m₁.trans (m₃.mono (by omega_arith) (by omega_arith))

/-! ## Addition and subtraction -/

/-- The pointers of the binary operations. -/
structure Ptrs (s : State) (o a b : Nat) : Prop where
  o : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 o
  a : s.gpr .esi = s.gpr .edi + BitVec.ofNat 32 a
  b : s.gpr .ebx = s.gpr .edi + BitVec.ofNat 32 b

/-- The slots of a result and an operand: the same, or apart. -/
def SlotApart (o a : Nat) : Prop := o = a ∨ o + 56 ≤ a ∨ a + 56 ≤ o

theorem addSub_ok {op : AluOp} (hop : op = .adc ∨ op = .sbb) {s : State} {base : Addr} (hs : Scr s base)
    {o a b : Nat} (hp : Ptrs s o a b) (ho : Slot o) (ha : Slot a) (hb : Slot b) (hoa : SlotApart o a)
    (hob : SlotApart o b) :
    WP isa (.block (addSub op)) s fun t => (∃ R₁ c₁ : Nat, c₁ ≤ 1 ∧ R₁ < full ∧
        PassRel op (fe s.mem base a) (fe s.mem base b) 0 R₁ c₁ full ∧ Folded op R₁ c₁ (fe t.mem base o)) ∧
      Outside base o 56 s.mem t.mem ∧ Keeps [.eax, .ecx] s t := by
  have ho' : o + 56 ≤ 3584 := ho
  have ha' : a + 56 ≤ 3584 := ha
  have hb' : b + 56 ≤ 3584 := hb
  unfold SlotApart at hoa hob
  unfold addSub
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (clearCarry_ok s) fun t₀ ⟨f₀, _, m₀, k₀⟩ => ?_
  have hs₀ := hs.of_keeps k₀ (by decide)
  have p₀ : Ptrs t₀ o a b := ⟨by rw [k₀.1 _ (by decide), k₀.1 _ (by decide)]; exact hp.o,
    by rw [k₀.1 _ (by decide), k₀.1 _ (by decide)]; exact hp.a,
    by rw [k₀.1 _ (by decide), k₀.1 _ (by decide)]; exact hp.b⟩
  rw [WP.block_append_iff]
  refine WP.mono (chain_ok hop hs₀ (yo := o) (xo := a) (v := fun k => word s.mem base (b + 4 * k)) f₀ 14
    (by omega_arith) (by omega_arith) (by unfold Apart; omega_arith) (fun k hk t tk =>
      ⟨ptr_ea hs₀ p₀.a tk (by decide) (by decide) (by omega_arith),
        ptr_ea hs₀ p₀.o tk (by decide) (by decide) (by omega_arith)⟩) (fun k hk t tk tm => ?_))
    fun t₁ ⟨k₁, m₁, c₁, f₁, r₁⟩ => ?_
  · rw [readMem (ptr_ea hs₀ p₀.b tk (by decide) (by decide) (by omega_arith))
      ((hs₀.of_keeps tk (by decide)).read (by omega_arith)),
      show t.mem.readW (off base (b + 4 * k)) 32 = word t.mem base (b + 4 * k) from rfl,
      tm.word (by omega_arith) (by omega_arith), m₀]
  rw [WP.block_append_iff]
  refine WP.mono (carry1_ok f₁) fun t₂ ⟨f₂, e₂, m₂, k₂⟩ => ?_
  have k₁₂ : Keeps [.eax, .ecx] t₀ t₂ := (k₁.mono (by decide)).trans (k₂.mono (by decide))
  have b₁ : c₁.toNat ≤ 1 := by cases c₁ <;> decide
  refine WP.mono (foldChain_ok hop (hs₀.of_keeps k₁₂ (by decide)) ho
    (by rw [k₁₂.1 _ (by decide), k₁₂.1 _ (by decide)]; exact p₀.o) f₂ e₂ (Nat.lt_of_le_of_lt b₁ (by decide)))
    fun t₃ ⟨r₃, m₃, k₃⟩ => ⟨⟨fe t₁.mem base o, c₁.toNat, b₁, fe_lt _ _ _, ?_, ?_⟩, ?_,
      (k₀.mono (by decide)).trans (k₁₂.trans k₃)⟩
  · rw [pow14, m₀] at r₁; exact r₁
  · rw [m₂] at r₃; exact r₃
  · rw [m₂] at m₃; rw [m₀] at m₁; exact m₁.trans m₃

/-- The result of an operation, as the field functions state it. -/
abbrev FnPost (base : Addr) (o : Nat) (s t : State) : Prop :=
  Keeps (.esi :: clob) s t ∧ FieldMem base o s.mem t.mem WORK

/-- The pointers of the binary operations, from the arguments. -/
theorem ptrs_ok {s : State} {base : Addr} {o a b : Nat} (hc : FnCtx s base 4 o a)
    (hvb : arg s 3 = BitVec.ofNat 32 b) :
    WP isa (.block argPtrs) s fun t => Ptrs t o a b ∧ t.mem = s.mem ∧ Keeps [.esi, .ebx, .ebp] s t := by
  have same : ∀ {u v : State}, v.mem = u.mem → Outside base 0 8192 u.mem v.mem := fun h => by
    rw [h]; exact Outside.refl _ _ _ _
  unfold argPtrs
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (argPtr_ok hc.args (by decide) (by decide) hc.argA) fun t₁ ⟨p₁, m₁, k₁⟩ => ?_
  obtain ⟨a₁, g₁⟩ := hc.args.keep (k₁.1 _ (by decide)) k₁.2.1 k₁.2.2 (same m₁)
  rw [WP.block_append_iff]
  refine WP.mono (argPtr_ok a₁ (i := 3) (by decide) (by decide) ((g₁ 3 (by decide)).trans hvb)) fun t₂ ⟨p₂, m₂, k₂⟩ => ?_
  obtain ⟨a₂, g₂⟩ := a₁.keep (k₂.1 _ (by decide)) k₂.2.1 k₂.2.2 (same m₂)
  refine WP.mono (argPtr_ok a₂ (i := 1) (by decide) (by decide)
    ((g₂ 1 (by decide)).trans ((g₁ 1 (by decide)).trans hc.argO))) fun t₃ ⟨p₃, m₃, k₃⟩ =>
    ⟨⟨p₃, ?_, ?_⟩, m₃.trans (m₂.trans m₁),
      (k₁.mono (by decide)).trans ((k₂.mono (by decide)).trans (k₃.mono (by decide)))⟩
  · rw [k₃.1 .esi (by decide), k₂.1 .esi (by decide), p₁, k₃.1 .edi (by decide), k₂.1 .edi (by decide)]
  · rw [k₃.1 .ebx (by decide), p₂, k₃.1 .edi (by decide)]

/-- `vg_gf448_r32_add` and `vg_gf448_r32_sub` between their entry and their exit. -/
theorem addSubBody_ok {op : AluOp} (hop : op = .adc ∨ op = .sbb) {s : State} {base : Addr} {o a b : Nat}
    (hc : FnCtx s base 4 o a) (hvb : arg s 3 = BitVec.ofNat 32 b) (hb : Slot b) (hoa : SlotApart o a)
    (hob : SlotApart o b) :
    WP isa (.block (argPtrs ++ addSub op)) s fun t => FnPost base o s t ∧ ∃ R₁ c₁ : Nat, c₁ ≤ 1 ∧ R₁ < full ∧
        PassRel op (fe s.mem base a) (fe s.mem base b) 0 R₁ c₁ full ∧ Folded op R₁ c₁ (fe t.mem base o) := by
  rw [WP.block_append_iff]
  refine WP.mono (ptrs_ok hc hvb) fun t ⟨tp, tm, tk⟩ => ?_
  refine WP.mono (addSub_ok hop (hc.scr.of_keeps tk (by decide)) tp hc.slotO hc.slotA hb hoa hob)
    fun u ⟨h, um, uk⟩ => ⟨⟨(tk.mono (by decide)).trans (uk.mono (by decide)), ?_⟩, ?_⟩
  · rw [tm] at um; exact FieldMem.output um
  · rw [tm] at h; exact h

theorem add_val {A B R₁ c₁ R : Nat} (h₁ : PassRel .adc A B 0 R₁ c₁ full) (hR : R₁ < full) (hc : c₁ ≤ 1)
    (h : Folded .adc R₁ c₁ R) : R % Spec.X448.P = (A + B) % Spec.X448.P := by
  rw [PassRel, ite_eq_left rfl, Nat.add_zero] at h₁
  rw [folded_add h hR (Nat.lt_of_le_of_lt hc (by decide)), h₁]

theorem sub_val {A B R₁ c₁ R : Nat} (h₁ : PassRel .sbb A B 0 R₁ c₁ full) (hR : R₁ < full) (hc : c₁ ≤ 1)
    (h : Folded .sbb R₁ c₁ R) : (R + B) % Spec.X448.P = A % Spec.X448.P := by
  rw [PassRel, ite_eq_right (by decide), Nat.add_zero] at h₁
  have e := congrArg (· % Spec.X448.P) (congrArg (R + ·) h₁)
  have hm := folded_sub h hR hc
  have e₂ : (R + B + full * c₁ + R₁) % Spec.X448.P = (A + full * c₁ + R₁) % Spec.X448.P := by
    rw [h₁, show R + B + full * c₁ + R₁ = (R + full * c₁) + (R₁ + B) by omega_arith, Nat.add_mod, hm, ← Nat.add_mod,
      Nat.add_comm (R₁ + B)]
  clear e
  have e₃ : (R + B + (full * c₁ + R₁)) % Spec.X448.P = (A + (full * c₁ + R₁)) % Spec.X448.P := by
    rw [← Nat.add_assoc, ← Nat.add_assoc]; exact e₂
  exact add_mod_cancel e₃

/-! ## Multiplication by a24 -/

/-- `edx:eax = eax · ebx + ecx`. -/
theorem mulAdd_ok (s : State) : WP isa (.block [.mul .ebx, .alu .add .eax (.reg .ecx), .alu .adc .edx (.imm 0)]) s
    fun t => (t.gpr .eax).toNat + 2 ^ 32 * (t.gpr .edx).toNat =
      (s.gpr .eax).toNat * (s.gpr .ebx).toNat + (s.gpr .ecx).toNat ∧ t.mem = s.mem ∧ Keeps [.eax, .edx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execMul, readSrc,
    Option.bind_some, Option.map_some, RegUpd.cf_setReg, RegUpd.cf_arithFlags, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · simp only [reduceCtorEq, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, ↓reduceIte]
    have e := Proof.X25519.X86.toNat_mul_lo (s.gpr .eax) (s.gpr .ebx)
    have hp := Nat.mul_le_mul (Nat.le_pred_of_lt (s.gpr .eax).isLt) (Nat.le_pred_of_lt (s.gpr .ebx).isLt)
    have hc := (s.gpr .ecx).isLt
    generalize (BitVec.ofNat 32 ((s.gpr .eax).toNat * (s.gpr .ebx).toNat)) = lo at *
    generalize (BitVec.ofNat 32 ((s.gpr .eax).toNat * (s.gpr .ebx).toNat / 2 ^ 32)) = hi at *
    generalize (s.gpr .eax).toNat * (s.gpr .ebx).toNat = p at *
    have hl := lo.isLt; have hh := hi.isLt
    simp only [show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero, BitVec.toNat_add, Proof.X25519.X86.ofBool_toNat]
    rw [Proof.X25519.X86.carry_toNat (by omega_using [hl, hc])]
    simp only [Nat.reducePow, Nat.reduceSub, Nat.pred_eq_sub_one, Nat.reduceMul] at hp e hl hh hc ⊢
    omega_using [e, hp, hl, hh, hc]
  · simp only [RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.mem_setFlags]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_arithFlags, RegUpd.rd_setFlags]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_arithFlags, RegUpd.wr_setFlags]

/-- The pointers of the unary operations. -/
structure Ptrs2 (s : State) (o a : Nat) : Prop where
  o : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 o
  a : s.gpr .esi = s.gpr .edi + BitVec.ofNat 32 a

theorem a24Step_ok {s : State} {base : Addr} (hs : Scr s base) {o a k : Nat} (hp : Ptrs2 s o a)
    (ho : Slot o) (ha : Slot a) (hk : k < 14) (hb : s.gpr .ebx = 39081) (hc : (s.gpr .ecx).toNat ≤ 39081) :
    WP isa (.block (a24Step k)) s fun t => (t.gpr .ecx).toNat ≤ 39081 ∧ Keeps [.eax, .ecx, .edx] s t ∧
      ∃ r : BitVec 32, t.mem = s.mem.writeW (off base (o + 4 * k)) r ∧
        r.toNat + 2 ^ 32 * (t.gpr .ecx).toNat = 39081 * limbs s.mem base a k + (s.gpr .ecx).toNat := by
  have ho' : o + 56 ≤ 3584 := ho
  have ha' : a + 56 ≤ 3584 := ha
  unfold a24Step
  refine wp_load (a := off base (a + 4 * k)) (hs.ea_ptr hp.a (by omega_arith)) (hs.read (by omega_arith))
    fun t₁ u₁ => ?_
  change WP isa (.block (([.mul .ebx, .alu .add .eax (.reg .ecx), .alu .adc .edx (.imm 0)] : List Instr) ++
    [.store (wordAt .ebp k) .eax, .mov .ecx (.reg .edx)])) t₁ _
  rw [WP.block_append_iff]
  refine WP.mono (mulAdd_ok t₁) fun t₂ ⟨e₂, m₂, k₂⟩ => ?_
  have k₁ : Keeps [.eax, .edx] s t₁ := u₁.rest (by decide)
  have k₁₂ := k₁.trans k₂
  have hs₂ := hs.of_keeps k₁₂ (by decide)
  refine wp_store (a := off base (o + 4 * k)) (ptr_ea hs hp.o k₁₂ (by decide) (by decide) (by omega_arith))
    (hs₂.write (by omega_arith)) fun t₃ u₃ => wp_mov rfl fun t₄ u₄ => WP.block_nil ?_
  have e₄ : t₄.gpr .ecx = t₂.gpr .edx := by rw [u₄.gpr, u₃.gpr]
  have e : (t₂.gpr .eax).toNat + 2 ^ 32 * (t₄.gpr .ecx).toNat = 39081 * limbs s.mem base a k + (s.gpr .ecx).toNat := by
    rw [e₄, e₂, u₁.gpr, u₁.other .ebx (by decide), u₁.other .ecx (by decide), hb, Nat.mul_comm 39081]
    rfl
  refine ⟨?_, (k₁₂.mono (by decide)).trans ((u₃.rest _).trans (u₄.rest (by decide))), t₂.gpr .eax, ?_, e⟩
  · have hw : limbs s.mem base a k < 2 ^ 32 := BitVec.isLt _
    omega_using [e, hc, hw]
  · rw [u₄.mem, u₃.mem, m₂, u₁.mem]

theorem mulA24_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat} (hp : Ptrs2 s o a)
    (ho : Slot o) (ha : Slot a) (hoa : SlotApart o a) :
    WP isa (.block mulA24) s fun t => fe t.mem base o % Spec.X448.P = 39081 * fe s.mem base a % Spec.X448.P ∧
      Outside base o 56 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx] s t := by
  have ho' : o + 56 ≤ 3584 := ho
  have ha' : a + 56 ≤ 3584 := ha
  unfold SlotApart at hoa
  unfold mulA24
  rw [List.append_assoc, List.append_assoc]
  refine wp_mov rfl fun t₁ u₁ => wp_mov rfl fun t₂ u₂ => ?_
  have k₂ : Keeps [.eax, .ebx, .ecx, .edx] s t₂ := (u₁.rest (by decide)).trans (u₂.rest (by decide))
  have m₂ : t₂.mem = s.mem := u₂.mem.trans u₁.mem
  have hs₂ := hs.of_keeps k₂ (by decide)
  have b₂ : t₂.gpr .ebx = 39081 := (u₂.other _ (by decide)).trans u₁.gpr
  have p₂ : Ptrs2 t₂ o a := ⟨by rw [k₂.1 _ (by decide), k₂.1 _ (by decide)]; exact hp.o,
    by rw [k₂.1 _ (by decide), k₂.1 _ (by decide)]; exact hp.a⟩
  let inv := fun n (t : State) => Keeps [.eax, .ecx, .edx] t₂ t ∧ Outside base o (4 * n) s.mem t.mem ∧
    (t.gpr .ecx).toNat ≤ 39081 ∧
    num (limbs t.mem base o) n + (2 ^ 32) ^ n * (t.gpr .ecx).toNat = 39081 * num (limbs s.mem base a) n
  have step : ∀ n t, n < 14 → inv n t → WP isa (.block (a24Step n)) t (inv (n + 1)) := by
    intro n t hn ⟨tk, tm, tc, tv⟩
    have pt : Ptrs2 t o a := ⟨by rw [tk.1 _ (by decide), tk.1 _ (by decide)]; exact p₂.o,
      by rw [tk.1 _ (by decide), tk.1 _ (by decide)]; exact p₂.a⟩
    refine WP.mono (a24Step_ok (hs₂.of_keeps tk (by decide)) pt ho ha hn ((tk.1 _ (by decide)).trans b₂) tc)
      fun u ⟨uc, uk, r, um, ur⟩ => ⟨tk.trans uk, ?_, uc, ?_⟩
    · rw [um]
      exact (tm.mono (by omega_arith) (by omega_arith)).trans
        ((writeW_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
    · have la : limbs t.mem base a n = limbs s.mem base a n :=
        congrArg BitVec.toNat (tm.word (by omega_arith) (by omega_arith))
      have low : num (limbs u.mem base o) n = num (limbs t.mem base o) n := num_congr fun k hk => by
        show (word u.mem base (o + 4 * k)).toNat = _
        rw [um, word_write t.mem base (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith)]
      have top : limbs u.mem base o n = r.toNat := by
        show (word u.mem base (o + 4 * n)).toNat = _
        rw [um, word_write t.mem base (by omega_arith) (by omega_arith), ite_eq_left rfl]
      rw [la] at ur
      rw [num_succ, num_succ, low, top, Nat.pow_succ (2 ^ 32) n, Nat.mul_assoc ((2 ^ 32) ^ n), Nat.add_assoc,
        ← Nat.mul_add, ur, Nat.mul_add, Nat.mul_add 39081, ← tv, Nat.mul_left_comm]
      omega_arith
  change WP isa (.block (List.flatMap a24Step (List.range 14) ++
    (([.alu .test .ecx (.reg .ecx)] : List Instr) ++ foldChain .adc))) t₂ _
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (N := 14) inv step 14 (by decide) t₂
    ⟨Keeps.refl _ _, by rw [m₂]; exact Outside.refl _ _ _ _, by rw [u₂.gpr]; decide, by
      rw [u₂.gpr]; rfl⟩) fun t₃ ⟨k₃, m₃, c₃, v₃⟩ => ?_
  refine WP.cons (t := arithFlags t₃ (t₃.gpr .ecx &&& t₃.gpr .ecx) false false) rfl ?_
  have k₄ : Keeps [.eax, .ecx, .edx] t₂ (arithFlags t₃ (t₃.gpr .ecx &&& t₃.gpr .ecx) false false) :=
    k₃.trans ⟨fun _ _ => rfl, rfl, rfl⟩
  refine WP.mono (foldChain_ok (.inl rfl) (hs₂.of_keeps k₄ (by decide)) ho
    (by rw [k₄.1 _ (by decide), k₄.1 _ (by decide)]; exact p₂.o) rfl (c := (t₃.gpr .ecx).toNat)
    (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl) (BitVec.isLt _)) fun t₅ ⟨r₅, m₅, k₅⟩ =>
    ⟨?_, m₃.trans m₅, k₂.trans ((k₄.mono (by decide)).trans (k₅.mono (by decide)))⟩
  rw [folded_add r₅ (fe_lt _ _ _) (by omega_using [c₃])]
  rw [pow14] at v₃
  exact congrArg (· % Spec.X448.P) v₃

theorem a24Body_ok {s : State} {base : Addr} {o a : Nat} (hc : FnCtx s base 3 o a) (hoa : SlotApart o a) :
    WP isa (.block (argPtr .esi 2 ++ argPtr .ebp 1 ++ mulA24)) s fun t =>
      FnPost base o s t ∧ F t.mem base o = Spec.X448.a24 * F s.mem base a := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (argPtr_ok hc.args (by decide) (by decide) hc.argA) fun t₁ ⟨p₁, m₁, k₁⟩ => ?_
  obtain ⟨a₁, g₁⟩ := hc.args.keep (k₁.1 _ (by decide)) k₁.2.1 k₁.2.2 (by rw [m₁]; exact Outside.refl _ _ _ _)
  rw [WP.block_append_iff]
  refine WP.mono (argPtr_ok a₁ (i := 1) (by decide) (by decide) ((g₁ 1 (by decide)).trans hc.argO))
    fun t₂ ⟨p₂, m₂, k₂⟩ => ?_
  have k₁₂ : Keeps [.esi, .ebp] s t₂ := (k₁.mono (by decide)).trans (k₂.mono (by decide))
  refine WP.mono (mulA24_ok (hc.scr.of_keeps k₁₂ (by decide)) ⟨p₂, ?_⟩ hc.slotO hc.slotA hoa)
    fun t₃ ⟨v₃, m₃, k₃⟩ => ⟨⟨(k₁₂.mono (by decide)).trans (k₃.mono (by decide)), ?_⟩, ?_⟩
  · rw [k₂.1 .esi (by decide), p₁, k₂.1 .edi (by decide)]
  · rw [m₂, m₁] at m₃; exact FieldMem.output m₃
  · rw [m₂, m₁] at v₃; exact toFe_a24 v₃

end VG.Proof.X448.X86
