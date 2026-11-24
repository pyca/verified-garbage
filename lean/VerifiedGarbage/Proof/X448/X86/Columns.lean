module

import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.X86.Reduce
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.X448.X86.Field
public import VerifiedGarbage.Proof.X25519.X86.Arith
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.X448.X86.Instr
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.X86.Mem
import VerifiedGarbage.Proof.X448.X86.Step

/-! ### `X448.X86.RowPass`, which this module and modules that import it used -/

section

/-!
# X448 on x86 (32-bit): multiplication-row carry propagation

A pass stores one digit at a time and preserves the remaining coefficients for
the next step.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

structure CarryInv (base : Addr) (o : Nat) (s0 : State) (c : Nat → Nat) (k : Nat) (s : State) : Prop where
  regs : Keeps [.eax, .ebx, .edx] s0 s
  carry : (s.gpr .ebx).toNat = Radix16.carry c k
  mem : Outside base o (4 * k) s0.mem s.mem
  outs : ∀ j < k, limbs s.mem base o j = digit c j

theorem carryPass_ok {base : Addr} {o d : Nat} {rb : Reg} {src : Nat → List Instr} {s0 : State}
    {c : Nat → Nat} (hrb : rb ∉ [.eax, .ebx, .edx]) (ho : o + 112 ≤ 8192)
    (hea : ∀ k < 28, s0.ea (at_ rb (d + 4 * k)) = off base (o + 4 * k))
    (hw : ∀ k < 28, InRegions s0.wr (off base (o + 4 * k)) 4)
    (hzero : (s0.gpr .ebx).toNat = 0) (hc : ∀ k < 28, c k ≤ 2 ^ 32 - radix)
    (hsrc : ∀ k < 28, ∀ s, CarryInv base o s0 c k s →
      WP isa (.block (src k)) s fun t =>
        (t.gpr .eax).toNat = c k ∧ Keeps [.eax, .edx] s t ∧ t.mem = s.mem) :
    WP isa (.block (carryPass rb d src)) s0 (CarryInv base o s0 c 28) := by
  refine wp_range_flatMap (M := isa) (CarryInv base o s0 c) (fun k s hk h => ?_) 28 (Nat.le_refl _) s0
    ⟨Keeps.refl _ _, hzero, Outside.refl _ _ _ _, fun j hj => by omega⟩
  rw [WP.block_append_iff]
  refine WP.mono (hsrc k hk s h) fun t ⟨tv, tk, tm⟩ => ?_
  have tb : t.gpr .ebx = s.gpr .ebx := tk.1 _ (by decide)
  have tk' : Keeps [.eax, .ebx, .edx] s t := tk.mono (by decide)
  have trb : t.gpr rb = s0.gpr rb := (tk'.1 rb hrb).trans (h.regs.1 rb hrb)
  have ea : t.ea (at_ rb (d + 4 * k)) = off base (o + 4 * k) := by
    simpa only [State.ea, at_, trb] using hea k hk
  have bound : c k + Radix16.carry c k < 2 ^ 32 := by
    have a := hc k hk
    have b := carry_bound (n := k) (fun j hj => hc j (by omega_using [hk, hj]))
    simp only [radix] at a
    omega_using [a, b]
  refine WP.mono (carryRaw_ok hrb ea (by rw [tk.2.2, h.regs.2.2]; exact hw k hk)
    (by rw [tv, tb, h.carry]; exact bound)) fun u ⟨uc, um, uk⟩ => ?_
  rw [tv, tb, h.carry] at uc um
  rw [tm] at um
  refine ⟨h.regs.trans ((tk.mono (by decide)).trans uk), uc, ?_, ?_⟩
  · rw [um]
    exact (h.mem.mono (by omega_using []) (by omega_using [])).trans
      ((writeW_outside _ _ _ (by omega_using [ho, hk])).mono (by omega_using []) (by omega_using []))
  · intro j hj
    change (word u.mem base (o + 4 * j)).toNat = _
    rw [um, word_write s.mem base (by omega_using [ho, hk]) (by omega_using [ho, hk, hj])]
    by_cases he : j = k
    · rw [ite_eq_left he, he, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (Nat.lt_trans (digit_lt c k) (by decide : radix < 2 ^ 32))
    · rw [ite_eq_right he]; exact h.outs j (by omega_using [hj, he])

end VG.Proof.X448.X86

end

end

/-! ### `X448.X86.Args`, which this module and modules that import it used -/

section

/-!
# X448 on x86 (32-bit): the field functions' arguments

A field function (`vg_gf448_r32_*`, `Impl/X448/X86.lean`) reads its
arguments from the stack: the working space and the offsets. `ArgArea s base
n` says what it knows of the first `n` of them on entry: they are readable
and lie outside the working space at `base`, so that what the function
writes there leaves them alone (`ArgArea.keep`).
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

/-- The first `n` arguments: readable, and outside the working space at `base`. -/
structure ArgArea (s : State) (base : Addr) (n : Nat) : Prop where
  read : ∀ i < n, InRegions (s.rd ++ s.wr) (argAddr s i) 4
  out : ∀ i < n, ∀ k < 4, 8192 ≤ ofs base (argAddr s i + BitVec.ofNat 64 k)

theorem argOp_ea (s : State) (i : Nat) : s.ea (argOp i) = argAddr s i := rfl

/-- The arguments stay readable and unchanged while the code changes only
registers but `esp`, and memory in the working space. -/
theorem ArgArea.keep {s t : State} {base : Addr} {n : Nat} (h : ArgArea s base n)
    (hsp : t.gpr .esp = s.gpr .esp) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hm : Outside base 0 8192 s.mem t.mem) :
    ArgArea t base n ∧ ∀ i < n, arg t i = arg s i := by
  have ea : ∀ i, argAddr t i = argAddr s i := fun i => by simp only [argAddr, hsp]
  refine ⟨⟨fun i hi => by rw [ea, hrd, hwr]; exact h.read i hi,
    fun i hi k hk => by rw [ea]; exact h.out i hi k hk⟩, fun i hi => ?_⟩
  simp only [arg, ea]
  exact (Mem.readW_congr fun k hk => (hm _ (Or.inr (h.out i hi k hk))).symm).symm

/-- Loading argument `i`. -/
theorem ArgArea.load {s : State} {base : Addr} {n : Nat} (h : ArgArea s base n) {i : Nat} (hi : i < n)
    {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Upd s t r (arg s i) → WP isa (.block is) t Q) :
    WP isa (.block (.mov r (.mem (argOp i)) :: is)) s Q :=
  wp_load (argOp_ea s i) (h.read i hi) k

/-- The address `[r + k]`, for `r` pointing `d` bytes into the working space. -/
theorem Scr.ea_ptr {s : State} {base : Addr} (hs : Scr s base) {r : Reg} {d k : Nat}
    (hr : s.gpr r = s.gpr .edi + BitVec.ofNat 32 d) (hdk : d + k < 8192) :
    s.ea (at_ r k) = off base (d + k) := by
  change (s.gpr r + BitVec.ofNat 32 k).setWidth 64 = _
  rw [hr, Offset.add_add]
  exact hs.ea hdk

end VG.Proof.X448.X86

end

end

/-! ### `X448.X86.Chain`, which this module and modules that import it used -/

section

/-!
# X448 on x86 (32-bit): carry chains

`chain op y x src n` (`Impl/X448/X86.lean`) runs a carry (`adc`) or a borrow (`sbb`) through `n`
words (`chain_ok`), as X25519's passes do (`PassRel`): the words at `y` are those at `x` and the
operands `src`.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86
open VG.Proof.X25519.X86 (num num_succ num_congr PassRel PassRel.succ wp_adcC wp_sbbC add3_toNat sub3_toNat
  carry_toNat)

/-- The bytes from `ACC` that the field functions' arithmetic writes: the
operands' copies and the product, not the registers they save after them. -/
abbrev WORK : Nat := 496

/-- One word of a chain. -/
theorem chainStep_ok {op : AluOp} (hop : op = .adc ∨ op = .sbb) {s : State} {base : Addr} {y x : MemOp}
    {yo xo : Nat} {src : Src} {v : BitVec 32} {cin : Bool} (hcf : s.cf = some cin)
    (hx : s.ea x = off base xo) (hxr : InRegions (s.rd ++ s.wr) (off base xo) 4)
    (hy : ∀ t, Keeps [.eax] s t → t.ea y = off base yo) (hyw : InRegions s.wr (off base yo) 4)
    (hv : ∀ t, Keeps [.eax] s t → t.mem = s.mem → readSrc t src = some v) :
    WP isa (.block (chainStep op y x src)) s fun t => Keeps [.eax] s t ∧
      ∃ r : BitVec 32, ∃ c' : Bool, t.mem = s.mem.writeW (off base yo) r ∧ t.cf = some c' ∧
        PassRel op (word s.mem base xo).toNat v.toNat cin.toNat r.toNat c'.toNat (2 ^ 32) := by
  unfold chainStep
  refine WP.cons (t := s.setReg .eax (word s.mem base xo))
    (by simp only [reduceExec, readSrc, hx, State.load32, hxr, ite_true, Option.map_some]) ?_
  have u₁ := Upd.setReg s .eax (word s.mem base xo)
  have f₁ : (s.setReg .eax (word s.mem base xo)).cf = some cin := hcf
  generalize s.setReg .eax (word s.mem base xo) = s₁ at *
  have k₁ : Keeps [.eax] s s₁ := u₁.rest (by decide)
  have y₁ := hv s₁ k₁ u₁.mem
  have hw := (word s.mem base xo).isLt
  have hvl := v.isLt
  have hcl : cin.toNat ≤ 1 := by cases cin <;> decide
  rcases hop with rfl | rfl
  · refine wp_adcC y₁ f₁ fun s₂ u₂ f₂ => ?_
    have k₂ : Keeps [.eax] s s₂ := k₁.trans ⟨fun r hr => u₂.other r (by simpa using hr), u₂.rd, u₂.wr⟩
    refine WP.cons (t := { s₂ with mem := s₂.mem.writeW (off base yo) (s₂.gpr .eax) })
      (by simp only [reduceExec, hy s₂ k₂, State.store32, show s₂.wr = s.wr from k₂.2.2, hyw, ite_true])
      (WP.block_nil ⟨k₂, _, _, by rw [u₂.mem, u₁.mem], f₂, ?_⟩)
    rw [u₂.gpr, u₁.gpr, add3_toNat, PassRel, ite_eq_left rfl, carry_toNat (by omega_using [hw, hvl, hcl])]
    exact (Nat.mod_add_div _ _).symm
  · refine wp_sbbC y₁ f₁ fun s₂ u₂ f₂ => ?_
    have k₂ : Keeps [.eax] s s₂ := k₁.trans ⟨fun r hr => u₂.other r (by simpa using hr), u₂.rd, u₂.wr⟩
    refine WP.cons (t := { s₂ with mem := s₂.mem.writeW (off base yo) (s₂.gpr .eax) })
      (by simp only [reduceExec, hy s₂ k₂, State.store32, show s₂.wr = s.wr from k₂.2.2, hyw, ite_true])
      (WP.block_nil ⟨k₂, _, _, by rw [u₂.mem, u₁.mem], f₂, ?_⟩)
    rw [u₂.gpr, u₁.gpr, PassRel, ite_eq_right (by decide)]
    exact (sub3_toNat _ _ _).symm

/-- The words a chain reads, where it writes no word before it reads it. -/
def Apart (yo xo n : Nat) : Prop := yo = xo ∨ yo + 4 * n ≤ xo ∨ xo + 4 * n ≤ yo

/-- `n` words of a chain, for operands of values `v k` whatever the words below theirs hold. -/
theorem chain_ok {op : AluOp} (hop : op = .adc ∨ op = .sbb) {s : State} {base : Addr} (hs : Scr s base)
    {y x : Nat → MemOp} {yo xo : Nat} {src : Nat → Src} {v : Nat → BitVec 32} {cin : Bool}
    (hcf : s.cf = some cin) : ∀ n, yo + 4 * n ≤ 8192 → xo + 4 * n ≤ 8192 → Apart yo xo n →
    (∀ k < n, ∀ t, Keeps [.eax] s t → t.ea (x k) = off base (xo + 4 * k) ∧ t.ea (y k) = off base (yo + 4 * k)) →
    (∀ k < n, ∀ t, Keeps [.eax] s t → Outside base yo (4 * k) s.mem t.mem → readSrc t (src k) = some (v k)) →
    WP isa (.block (chain op y x src n)) s fun t => Keeps [.eax] s t ∧ Outside base yo (4 * n) s.mem t.mem ∧
      ∃ c' : Bool, t.cf = some c' ∧ PassRel op (num (limbs s.mem base xo) n) (num (fun k => (v k).toNat) n)
        cin.toNat (num (limbs t.mem base yo) n) c'.toNat ((2 ^ 32) ^ n)
  | 0, _, _, _, _, _ => WP.block_nil ⟨Keeps.refl _ _, Outside.refl _ _ _ _, cin, hcf, by
      rcases hop with rfl | rfl <;> simp [PassRel, num]⟩
  | n + 1, hyo, hxo, hap, hea, hv => by
    unfold Apart at hap
    rw [chain, List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (chain_ok hop hs hcf n (by omega_using [hyo]) (by omega_using [hxo])
      (by unfold Apart; omega_using [hap]) (fun k hk => hea k (by omega_using [hk]))
      (fun k hk => hv k (by omega_using [hk]))) fun t ⟨tk, tm, ct, hct, rt⟩ => ?_
    have ts := hs.of_keeps tk (by decide)
    have wx : word t.mem base (xo + 4 * n) = word s.mem base (xo + 4 * n) :=
      tm.word (by omega_using [hap]) (by omega_using [hxo])
    refine WP.mono (chainStep_ok hop hct (hea n (by omega_using []) t tk).1 (ts.read (by omega_using [hxo]))
      (fun u hu => (hea n (by omega_using []) u (tk.trans hu)).2) (ts.write (by omega_using [hyo]))
      fun u hu mu => hv n (by omega_using []) u (tk.trans hu) (by rw [mu]; exact tm))
      fun u ⟨uk, r, c', um, uc, ur⟩ => ⟨tk.trans uk, ?_, c', uc, ?_⟩
    · rw [um]
      exact (tm.mono (by omega_using []) (by omega_using [])).trans
        ((writeW_outside _ _ _ (by omega_using [hyo])).mono (by omega_using []) (by omega_using []))
    · have low : num (limbs u.mem base yo) n = num (limbs t.mem base yo) n := num_congr fun k hk => by
        show (word u.mem base (yo + 4 * k)).toNat = _
        rw [um, word_write t.mem base (by omega_using [hyo]) (by omega_using [hyo, hk]),
          ite_eq_right (by omega_using [hk])]
      have top : limbs u.mem base yo n = r.toNat := by
        show (word u.mem base (yo + 4 * n)).toNat = _
        rw [um, word_write t.mem base (by omega_using [hyo]) (by omega_using [hyo]), ite_eq_left rfl]
      rw [num_succ, num_succ, num_succ, low, top, Nat.pow_succ]
      rw [wx] at ur
      exact rt.succ ur

/-- The carry flag cleared. -/
theorem clearCarry_ok (s : State) : WP isa (.block clearCarry) s fun t =>
    t.cf = some false ∧ t.gpr .ecx = 0 ∧ t.mem = s.mem ∧ Keeps [.ecx] s t := by
  refine WP.cons (t := (arithFlags s (s.gpr .ecx ^^^ s.gpr .ecx) false false).setReg .ecx (s.gpr .ecx ^^^ s.gpr .ecx))
    rfl (WP.block_nil ?_)
  have u := Upd.flags s .ecx (s.gpr .ecx ^^^ s.gpr .ecx) (some false) (some false)
    (some (s.gpr .ecx ^^^ s.gpr .ecx == 0)) (some (s.gpr .ecx ^^^ s.gpr .ecx).msb)
  exact ⟨rfl, u.gpr.trans BitVec.xor_self, u.mem, u.rest (by decide)⟩

/-- `ecx` = the carry flag, and the flag cleared. -/
theorem carry1_ok {s : State} {c : Bool} (hcf : s.cf = some c) : WP isa (.block carry1) s fun t =>
    t.cf = some false ∧ t.gpr .ecx = BitVec.ofNat 32 c.toNat ∧ t.mem = s.mem ∧ Keeps [.ecx] s t := by
  refine Proof.X25519.X86.wp_sbbC (y := s.gpr .ecx) rfl hcf fun u hu _ => ?_
  refine WP.cons (t := (arithFlags u (u.gpr .ecx &&& 1) false false).setReg .ecx (u.gpr .ecx &&& 1)) rfl
    (WP.block_nil ?_)
  have v := Upd.flags u .ecx (u.gpr .ecx &&& 1) (some false) (some false)
    (some (u.gpr .ecx &&& 1 == 0)) (some (u.gpr .ecx &&& 1).msb)
  refine ⟨rfl, ?_, v.mem.trans hu.mem,
    Keeps.trans (s₂ := u) ⟨fun r hr => hu.other r (by simpa using hr), hu.rd, hu.wr⟩ (v.rest (by decide))⟩
  refine v.gpr.trans ?_
  rw [hu.gpr, BitVec.sub_self]
  cases c <;> rfl

/-- The carry flag added to `ecx`, which it does not carry out of. -/
theorem carryUp_ok {s : State} {c : Bool} {n : Nat} (hcf : s.cf = some c) (hn : s.gpr .ecx = BitVec.ofNat 32 n)
    (hb : n < 2 ^ 31) : WP isa (.block carryUp) s fun t =>
    t.cf = some false ∧ t.gpr .ecx = BitVec.ofNat 32 (n + c.toNat) ∧ t.mem = s.mem ∧ Keeps [.ecx] s t := by
  have hc : c.toNat ≤ 1 := by cases c <;> decide
  refine Proof.X25519.X86.wp_adcC (y := 0) rfl hcf fun u hu hcu => WP.block_nil ⟨?_, ?_, hu.mem,
    ⟨fun r hr => hu.other r (by simpa using hr), hu.rd, hu.wr⟩⟩
  · rw [hcu, hn, BitVec.toNat_ofNat, show (0 : BitVec 32).toNat = 0 from rfl]
    exact congrArg some (decide_eq_false (by omega_using [hb, hc]))
  · rw [hu.gpr, hn]
    apply BitVec.eq_of_toNat_eq
    rw [add3_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0 : BitVec 32).toNat = 0 from rfl]
    omega_using [hb, hc]

end VG.Proof.X448.X86

end

end

/-! ### `X448.X86.FnCtx`, which this module and modules that import it used -/

section

/-!
# X448 on x86 (32-bit): the field functions' context

What the field functions (`vg_gf448_r32_*`) know once `edi` holds the
working space (`FnCtx`): their arguments (`ArgArea`) and the offsets of the
result and the first operand, which fit below their own working space.
`argPtr_ok` points a register at an element from its offset.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

/-- What the field functions know on entry, after `edi = ws`: the working
space, the arguments, and the offsets `o`, `a` (and `b`) that fit below the
functions' own working space. -/
structure FnCtx (s : State) (base : Addr) (n : Nat) (o a : Nat) : Prop where
  scr : Scr s base
  args : ArgArea s base n
  n3 : 3 ≤ n
  argO : arg s 1 = BitVec.ofNat 32 o
  argA : arg s 2 = BitVec.ofNat 32 a
  slotO : Slot o
  slotA : Slot a

theorem FnCtx.keep {s t : State} {base : Addr} {n o a : Nat} (h : FnCtx s base n o a) {rs : List Reg}
    (hk : Keeps rs s t) (hr : .esp ∉ rs) (he : .edi ∉ rs) (hm : Outside base 0 8192 s.mem t.mem) :
    FnCtx t base n o a := by
  obtain ⟨ta, targ⟩ := h.args.keep (hk.1 _ hr) hk.2.1 hk.2.2 hm
  exact ⟨h.scr.of_keeps hk he, ta, h.n3, by rw [targ 1 (by have := h.n3; omega_using [this])]; exact h.argO,
    by rw [targ 2 (by have := h.n3; omega_using [this])]; exact h.argA, h.slotO, h.slotA⟩

/-- `r = ws + ` argument `i`. -/
theorem argPtr_ok {s : State} {base : Addr} {n : Nat} (ha : ArgArea s base n)
    {i : Nat} (hi : i < n) {r : Reg} (hr : r ≠ .edi) {d : Nat} (hd : arg s i = BitVec.ofNat 32 d) :
    WP isa (.block (argPtr r i)) s fun t =>
      t.gpr r = t.gpr .edi + BitVec.ofNat 32 d ∧ t.mem = s.mem ∧ Keeps [r] s t := by
  unfold argPtr
  refine ha.load hi fun u hu => wp_alu (Or.inl rfl) rfl fun v hv _ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [hv.gpr, hv.other .edi hr.symm]
    change u.gpr r + u.gpr .edi = _
    rw [hu.gpr, hd, BitVec.add_comm]
  · rw [hv.mem, hu.mem]
  · exact (hu.rest (by simp)).trans (hv.rest (by simp))

end VG.Proof.X448.X86

end

end
