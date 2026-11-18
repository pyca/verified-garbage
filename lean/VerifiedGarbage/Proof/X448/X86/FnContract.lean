module

import VerifiedGarbage.Proof.X25519.X86.Arith
public import VerifiedGarbage.Proof.X25519.X86.Column
import Batteries.Logic
import VerifiedGarbage.Proof.X448.X86.Step
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Spec.X448
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.X86.Mem
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.X448.X86.Instr
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.X448.X86.Columns
public import VerifiedGarbage.Proof.X448.X86.Small
public import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.X448.X86.Field

/-! ### `X448.X86.RowMem`, which this module and modules that import it used -/

section

/-!
# X448 on x86 (32-bit): multiplication-row memory

The public row pointer moves through the working space while all field inputs
remain unchanged.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

abbrev accw (m : Mem) (base : Addr) (k : Nat) : Nat := limbs m base ACC k

theorem rowEa {s : State} {base : Addr} (hs : Scr s base) {i d : Nat}
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i)) (hd : 4 * i + d < 8192) :
    s.ea (at_ .ebp d) = off base (4 * i + d) := by
  change ((s.gpr .ebp + BitVec.ofNat 32 d).setWidth 64) = _
  rw [hp, Offset.add_add]
  exact hs.ea hd

structure RowInv (base : Addr) (a b : Nat) (s0 : State) (i : Nat) (s : State) : Prop where
  scr : Scr s base
  regs : Keeps clob s0 s
  ptr : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i)
  mem : Outside base ACC 224 s0.mem s.mem
  lt : ∀ k < i + 28, accw s.mem base k < radix
  val : valN (accw s.mem base) (i + 28) = valN (limbs s0.mem base a) i * fe s0.mem base b

theorem rowSrcWith_ok {s : State} {base : Addr} (hs : Scr s base) {mb : Nat → MemOp} {b i j : Nat}
    (hb : Slot b) (hi : i < 28) (hj : j < 28)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i))
    (hm : s.ea (mb j) = off base (b + 4 * j))
    (hc : (s.gpr .ecx).toNat < radix) (hy : limbs s.mem base b j < radix)
    (hacc : accw s.mem base (i + j) < radix) :
    WP isa (.block (rowSrcWith mb j)) s fun t =>
      (t.gpr .eax).toNat = (s.gpr .ecx).toNat * limbs s.mem base b j + accw s.mem base (i + j) ∧
      Keeps [.eax, .edx] s t ∧ t.mem = s.mem := by
  have hb' : b + 112 ≤ 3584 := hb
  unfold rowSrcWith
  refine wp_load hm (hs.read (by omega_using [hj, hb'])) fun t ht => ?_
  refine wp_mul fun u uv um uk => ?_
  have us := (hs.of_upd ht (by decide)).of_keeps uk (by decide)
  have up : u.gpr .ebp = u.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [uk.1 _ (by decide), uk.1 _ (by decide), ht.other .ebp (by decide), ht.other .edi (by decide)]
    exact hp
  have ea : u.ea (at_ .ebp (ACC + 4 * j)) = off base (ACC + 4 * (i + j)) := by
    rw [rowEa us up (by simp only [ACC]; omega_using [hi, hj]), show 4 * i + (ACC + 4 * j) = ACC + 4 * (i + j) by omega_using []]
  have rd : readSrc u (.mem (at_ .ebp (ACC + 4 * j))) = some (word u.mem base (ACC + 4 * (i + j))) := by
    simp only [readSrc, ea, State.load32, us.read (d := ACC + 4 * (i + j)) (n := 4) (by simp only [ACC]; omega_using [hi, hj]), ite_true]
  refine wp_alu (Or.inl rfl) rd fun v hv _ => WP.block_nil ⟨?_, ?_, hv.mem.trans (um.trans ht.mem)⟩
  · rw [hv.gpr]
    change (u.gpr .eax + word u.mem base (ACC + 4 * (i + j))).toNat = _
    rw [uv, ht.gpr, ht.other .ecx (by decide), um, ht.mem, BitVec.toNat_add, BitVec.toNat_ofNat]
    have prod := Nat.mul_le_mul (Nat.le_of_lt_succ hc) (Nat.le_of_lt_succ hy)
    simp only [radix] at hc hy hacc prod
    change ((limbs s.mem base b j * (s.gpr .ecx).toNat) % 2 ^ 32 + accw s.mem base (i + j)) % 2 ^ 32 = _
    rw [Nat.mul_comm (limbs s.mem base b j)]
    omega_using [hacc, prod]
  · exact (ht.rest (by decide)).trans (uk.trans (hv.rest (by decide)))

end VG.Proof.X448.X86

end

end

/-! ### `X448.X86.Fn`, which this module and modules that import it used -/

section

/-! ### `X448.X86.Row`, which this module and modules that import it used -/

section

/-! ### `X448.X86.RowTail`, which only this module used -/

section

/-!
# X448 on x86 (32-bit): advancing the product row

The last carry becomes the next product word, and the public row pointer
controls loop termination.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem rowTail_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 28)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i)) :
    WP isa (.block rowEnd) s fun t =>
      t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (4 * (i + 1)) ∧
      t.zf = some (decide (i + 1 = 28)) ∧
      t.mem = s.mem.writeW (off base (ACC + 4 * (i + 28))) (s.gpr .ebx) ∧ Keeps clob s t := by
  have ea : s.ea (at_ .ebp (ACC + 112)) = off base (ACC + 4 * (i + 28)) := by
    rw [rowEa hs hp (by simp only [ACC]; omega_using [hi]), show 4 * i + (ACC + 112) = ACC + 4 * (i + 28) by omega_using []]
  unfold rowEnd
  refine wp_store ea (hs.write (by simp only [ACC]; omega_using [hi])) fun t ht => ?_
  refine wp_alu (Or.inl rfl) rfl fun u hu _ => ?_
  refine wp_mov rfl fun v hv => ?_
  refine wp_alu (Or.inl rfl) rfl fun w hw _ => ?_
  refine wp_cmp rfl fun x hx hz => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · rw [hx.gpr, hw.other .ebp (by decide), hv.other .ebp (by decide), hu.gpr]
    change t.gpr .ebp + BitVec.ofNat 32 4 = _
    rw [ht.gpr, hp, Offset.add_add, Nat.mul_succ,
      hw.other .edi (by decide), hv.other .edi (by decide), hu.other .edi (by decide), ht.gpr]
  · rw [hz, hw.other .ebp (by decide), hv.other .ebp (by decide), hu.gpr, hw.gpr]
    apply congrArg some
    change ((t.gpr .ebp + (4 : BitVec 32) - (v.gpr .edx + (112 : BitVec 32))) == 0) = _
    rw [hv.gpr, hu.other .edi (by decide), ht.gpr, hp]
    change ((s.gpr .edi + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4 - (s.gpr .edi + BitVec.ofNat 32 112)) == 0) = _
    rw [Offset.add_add, Offset.add_sub_add_left]
    have check : ∀ n < 28, ((BitVec.ofNat 32 (4 * n + 4) - BitVec.ofNat 32 112) == 0) = decide (n + 1 = 28) := by decide
    exact check i hi
  · rw [hx.mem, hw.mem, hv.mem, hu.mem, ht.mem]
  · exact (ht.rest _).trans ((hu.rest (by decide)).trans ((hv.rest (by decide)).trans
      ((hw.rest (by decide)).trans (hx.rest _))))

end VG.Proof.X448.X86

end

end


/-!
# X448 on x86 (32-bit): one multiplication row

Bounded input limbs and previous product digits keep every multiply-add within
a 32-bit word. The row reads `a_i` with code `ldA` and `b_j` at `mb j`
(`rowWith_ok`): the field function's through its operand pointers.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem acc_shift (m : Mem) (base : Addr) (i j : Nat) :
    limbs m base (ACC + 4 * i) j = accw m base (i + j) := by
  change (word m base (ACC + 4 * i + 4 * j)).toNat = _
  rw [show ACC + 4 * i + 4 * j = ACC + 4 * (i + j) by omega_using []]

/-- What a row needs of the code `ldA` loading `a_i` (from any state of the
row's invariant) and of the addresses `mb j` of `b_j` (from any state whose
registers but `clob` are those of `s0`). -/
structure RowCode (base : Addr) (a b : Nat) (s0 : State) (i : Nat) (ldA : List Instr)
    (mb : Nat → MemOp) : Prop where
  ldA : ∀ s, RowInv base a b s0 i s → WP isa (.block ldA) s fun t =>
    t.gpr .ecx = word s.mem base (a + 4 * i) ∧ Keeps [.ecx] s t ∧ t.mem = s.mem
  mb : ∀ j < 28, ∀ s, Scr s base → Keeps clob s0 s → s.ea (mb j) = off base (b + 4 * j)

theorem rowWith_ok {base : Addr} {a b : Nat} (ha : Slot a) (hb : Slot b) {s0 s : State}
    {ldA : List Instr} {mb : Nat → MemOp}
    (ab : Bounded s0.mem base a) (bb : Bounded s0.mem base b) {i : Nat} (hi : i < 28)
    (hc : RowCode base a b s0 i ldA mb) (h : RowInv base a b s0 i s) :
    WP isa (.block (rowWith ldA mb)) s fun t =>
      RowInv base a b s0 (i + 1) t ∧ t.zf = some (decide (i + 1 = 28)) := by
  have ha' : a + 112 ≤ 3584 := ha
  have hb' : b + 112 ≤ 3584 := hb
  have input : ∀ o, Slot o → ∀ j < 28, limbs s.mem base o j = limbs s0.mem base o j := by
    intro o ho j hj
    exact h.mem.limbs (Or.inl ho) (Nat.le_trans ho (by decide)) hj
  unfold rowWith
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (hc.ldA s h) fun t ⟨tc, tk, tm⟩ => ?_
  refine wp_mov rfl fun u hu => ?_
  have ku : Keeps [.ecx, .ebx] s u := (tk.mono (by decide)).trans (hu.rest (by decide))
  have us := h.scr.of_keeps ku (by decide)
  have um : u.mem = s.mem := hu.mem.trans tm
  have uc : (u.gpr .ecx).toNat = limbs s0.mem base a i := by
    rw [hu.other .ecx (by decide), tc]; exact input a ha i hi
  have up : u.gpr .ebp = u.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [ku.1 _ (by decide), ku.1 _ (by decide)]; exact h.ptr
  have k0u : Keeps clob s0 u := h.regs.trans (ku.mono (by decide))
  let c := rowC (accw s.mem base) (limbs s0.mem base a) (limbs s0.mem base b) i
  have cb : ∀ j < 28, c j ≤ 2 ^ 32 - radix := by
    intro j hj
    exact rowC_bound (ab i hi) (bb j hj) (h.lt (i + j) (by omega_using [hj]))
  change WP isa (.block (carryPass .ebp ACC (rowSrcWith mb) ++ rowEnd)) u _
  rw [WP.block_append_iff]
  refine WP.mono (carryPass_ok (s0 := u) (base := base) (o := ACC + 4 * i) (c := c)
    (by decide) (by simp only [ACC]; omega_using [hi])
    (fun j hj => by
      rw [rowEa us up (by simp only [ACC]; omega_using [hi, hj]),
        show 4 * i + (ACC + 4 * j) = ACC + 4 * i + 4 * j by omega_using []])
    (fun j hj => us.write (by simp only [ACC]; omega_using [hi, hj])) (by rw [hu.gpr]; rfl) cb ?_) fun v hv => ?_
  · intro j hj v hv
    have vs := us.of_keeps hv.regs (by decide)
    have vp : v.gpr .ebp = v.gpr .edi + BitVec.ofNat 32 (4 * i) := by
      rw [hv.regs.1 _ (by decide), hv.regs.1 _ (by decide)]; exact up
    have va : (v.gpr .ecx).toNat = limbs s0.mem base a i := by rw [hv.regs.1 _ (by decide), uc]
    have vb : limbs v.mem base b j = limbs s0.mem base b j := by
      rw [hv.mem.limbs (Or.inl (by simp only [ACC]; omega_using [hb'])) (by omega_using [hb']) hj, um, input b hb j hj]
    have vacc : accw v.mem base (i + j) = accw s.mem base (i + j) := by
      change (word v.mem base (ACC + 4 * (i + j))).toNat = _
      rw [hv.mem.word (Or.inr (by omega_using [])) (by simp only [ACC]; omega_using [hi, hj]), um]
    refine WP.mono (rowSrcWith_ok vs hb hi hj vp (hc.mb j hj v vs (k0u.trans (hv.regs.mono (by decide))))
      (by rw [va]; exact ab i hi) (by rw [vb]; exact bb j hj)
      (by rw [vacc]; exact h.lt (i + j) (by omega_using [hj]))) fun w ⟨wv, wk, wm⟩ => ⟨?_, wk, wm⟩
    rw [va, vb, vacc] at wv
    exact wv
  · have vs := us.of_keeps hv.regs (by decide)
    have vp : v.gpr .ebp = v.gpr .edi + BitVec.ofNat 32 (4 * i) := by
      rw [hv.regs.1 _ (by decide), hv.regs.1 _ (by decide)]; exact up
    refine WP.mono (rowTail_ok vs hi vp) fun w ⟨wp, wz, wm, wk⟩ => ?_
    have passMem : Outside base (ACC + 4 * i) 112 s.mem v.mem := by rw [← um]; exact hv.mem
    have kv : Keeps clob s v := (ku.mono (by decide)).trans (hv.regs.mono (by decide))
    have limbsOut : ∀ k < i + 29, accw w.mem base k =
        rowAcc (accw s.mem base) (limbs s0.mem base a) (limbs s0.mem base b) i k := by
      intro k hk
      change (word w.mem base (ACC + 4 * k)).toNat = _
      rw [wm, word_write v.mem base (by simp only [ACC]; omega_using [hi]) (by simp only [ACC]; omega_using [hi, hk])]
      by_cases he : k = i + 28
      · rw [ite_eq_left he, hv.carry]
        simp only [c, rowAcc, he, show ¬i + 28 < i by omega_using [], Nat.lt_irrefl, ite_false]
      · rw [ite_eq_right he]
        by_cases hk' : k < i
        · rw [passMem.word (Or.inl (by omega_using [hk'])) (by simp only [ACC]; omega_using [hi, hk])]
          simp only [rowAcc, hk', ite_true]
        · have out := hv.outs (k - i) (by omega_using [hk, he])
          rw [acc_shift, show i + (k - i) = k by omega_using [hk']] at out
          change accw v.mem base k = _
          rw [out]
          simp only [c, rowAcc, hk', show k < i + 28 by omega_using [hk, he], ite_false, ite_true]
    refine ⟨⟨vs.of_keeps wk (by decide), h.regs.trans (kv.trans wk), wp, ?_, ?_, ?_⟩, wz⟩
    · rw [wm]
      exact (h.mem.trans (passMem.mono (by omega_using []) (by omega_using [hi]))).trans
        ((writeW_outside _ _ _ (by simp only [ACC]; omega_using [hi])).mono (by omega_using []) (by omega_using [hi]))
    · intro k hk
      rw [limbsOut k hk]
      exact rowAcc_lt (fun k hk => h.lt k (by omega_using [hk])) cb k hk
    · rw [valN_congr limbsOut]
      exact row_val h.val

/-- X448's rows: `a_i` and `b_j` at constant offsets of `edi`. -/
theorem rowCode_sc (base : Addr) {a b : Nat} (ha : Slot a) (hb : Slot b) (s0 : State) {i : Nat}
    (hi : i < 28) :
    RowCode base a b s0 i [.mov .ecx (.mem (at_ .ebp a))] (fun j => sc (b + 4 * j)) := by
  have ha' : a + 112 ≤ 3584 := ha
  have hb' : b + 112 ≤ 3584 := hb
  refine ⟨fun s h => ?_, fun j hj s hs _ => hs.ea (by omega_using [hb', hj])⟩
  · refine wp_load (by rw [rowEa h.scr h.ptr (by omega_using [hi, ha']), Nat.add_comm]) (h.scr.read (by omega_using [hi, ha']))
      fun t ht => WP.block_nil ⟨ht.gpr, ht.rest (by decide), ht.mem⟩

end VG.Proof.X448.X86

end

end

/-! ### `X448.X86.Init`, which this module and modules that import it used -/

section

/-! ### `X448.X86.Fill`, which this module and modules that import it used -/

section

/-!
# X448 on x86 (32-bit): filling words with zero

Each store touches only its designated word in the working space.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

theorem storeOne_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat}
    (hd : d + 4 ≤ 4096) (r : Reg) : WP isa (.block [st r d]) s fun t =>
      t.mem = s.mem.writeW (off base d) (s.gpr r) ∧ Keeps [] s t := by
  refine store_ok hs (by omega_using [hd]) fun t ht => WP.block_nil ⟨ht.mem, ht.rest _⟩

theorem zeroEax_ok (s : State) : WP isa (.block [.mov .eax (.imm 0)]) s fun t =>
    t.gpr .eax = 0 ∧ t.mem = s.mem ∧ Keeps [.eax] s t := by
  refine wp_mov rfl
    fun t ht => WP.block_nil ⟨ht.gpr, ht.mem, ht.rest (by decide)⟩

theorem fill_ok {s : State} {base : Addr} (hs : Scr s base) {o n : Nat} (ho : o + 4 * n ≤ 4096)
    (hz : s.gpr .eax = 0) :
    WP isa (.block ((List.range n).map (fun i => st .eax (o + 4 * i)))) s fun t =>
      (∀ i < n, limbs t.mem base o i = 0) ∧ Outside base o (4 * n) s.mem t.mem ∧ Keeps [] s t := by
  let inv := fun k (t : State) =>
    (∀ i < k, limbs t.mem base o i = 0) ∧ Outside base o (4 * n) s.mem t.mem ∧ Keeps [] s t
  have step : ∀ k t, k < n → inv k t →
      WP isa (.block [st .eax (o + 4 * k)]) t (inv (k + 1)) := by
    intro k t hk ⟨tf, tm, tk⟩
    have ts := hs.of_keeps tk (by decide)
    refine WP.mono (storeOne_ok ts (by omega_using [ho, hk]) .eax) fun u ⟨um, uk⟩ => ?_
    rw [tk.1 .eax (by decide), hz] at um
    have out : Outside base (o + 4 * k) 4 t.mem u.mem := by
      rw [um]; exact writeW_outside _ _ _ (by omega_using [ho, hk])
    refine ⟨?_, tm.trans (out.mono (by omega_using []) (by omega_using [hk])), tk.trans uk⟩
    intro i hi
    change (word u.mem base (o + 4 * i)).toNat = _
    rw [um, word_write t.mem base (by omega_using [ho, hk]) (by omega_using [ho, hk, hi])]
    by_cases h : i = k
    · rw [ite_eq_left h]; rfl
    · rw [ite_eq_right h]; exact tf i (by omega_using [hi, h])
  rw [List.map_eq_flatMap]
  exact wp_range_flatMap (M := isa) (N := n) inv step n (by omega_using []) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.X86

end

end

/-!
# X448 on x86 (32-bit): initializing multiplication

The initial 28 zero digits represent the empty product prefix; each row adds
its final carry word.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem zeroAcc_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block zeroAcc) s fun t =>
      (∀ i < 28, accw t.mem base i = 0) ∧ Outside base ACC 112 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold zeroAcc
  rw [WP.block_append_iff]
  refine WP.mono (zeroEax_ok s) fun t ⟨tz, tm, tk⟩ => ?_
  have hf := fill_ok (hs.of_keeps tk (by decide)) (by decide : ACC + 4 * 28 ≤ 4096) tz
  rw [List.map_eq_flatMap] at hf
  refine WP.mono hf fun u ⟨uf, um, uk⟩ => ⟨uf, ?_, tk.trans (uk.mono (by simp))⟩
  rw [← tm]; exact um

theorem mulPre_ok {s : State} {base : Addr} (hs : Scr s base) (a b : Nat) :
    WP isa (.block mulPre) s (RowInv base a b s 0) := by
  unfold mulPre
  rw [WP.block_append_iff]
  refine WP.mono (zeroAcc_ok hs) fun t ⟨tf, tm, tk⟩ => ?_
  refine wp_mov rfl fun u hu => WP.block_nil ?_
  have uk : Keeps clob s u := (tk.mono (by decide)).trans (hu.rest (by decide))
  refine ⟨hs.of_keeps uk (by decide), uk, ?_, ?_, ?_, ?_⟩
  · change u.gpr .ebp = u.gpr .edi + BitVec.ofNat 32 0
    rw [BitVec.add_zero, hu.gpr, hu.other .edi (by decide)]
  · rw [hu.mem]; exact tm.mono (by decide) (by decide)
  · intro i hi; rw [hu.mem, tf i hi]; decide
  · rw [hu.mem, valN_congr tf, valN_zero]
    exact (Nat.zero_mul _).symm

end VG.Proof.X448.X86

end

end

/-! ### `X448.X86.Mul`, which only this module used -/

section

/-! ### `X448.X86.Words32`, which only this module used -/

section

/-!
# X448 on x86 (32-bit): numbers of 32-bit words

The arithmetic of `vg_gf448_r16_mul`'s product (`Impl/X448/X86.lean`): the
columns of a product of two numbers of `n` words (`conv_identity`), the
fold of its 28 words by `2^448 = 2^224 + 1` (`foldCol_mod`), the two folds
of the carry (`fold_carries`), and the words of an element from its limbs
(`num_pack`).
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.Proof.X448.Radix16
open VG.Proof.X25519.X86 (num num_succ num_congr num_add num_mul num_lt)

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

/-- A number shifted up by `m` words. -/
theorem num_shift (g : Nat → Nat) (m N : Nat) :
    num (fun k => if m ≤ k then g (k - m) else 0) (m + N) = (2 ^ 32) ^ m * num g N := by
  rw [num_split, num_congr (g := fun _ => 0) (fun k hk => ite_eq_right (by omega_arith)), num_zero, Nat.zero_add]
  exact congrArg (_ * ·) (num_congr fun i _ => by
    simp only [Nat.le_add_right, ite_true, Nat.add_sub_cancel_left])

/-- A number of `n` words, read as one of more. -/
theorem num_trunc (h : Nat → Nat) (n d : Nat) :
    num (fun j => if j < n then h j else 0) (n + d) = num h n := by
  rw [num_split, num_congr (g := h) (fun k hk => ite_eq_left hk),
    num_congr (f := fun i => if n + i < n then h (n + i) else 0) (g := fun _ => 0)
      (fun i _ => ite_eq_right (by omega_arith)), num_zero, Nat.mul_zero, Nat.add_zero]

/-- Column `k` of the product of two numbers of `n` words: the products
`a_i b_j` with `i + j = k`. -/
def convCol (n : Nat) (fa fb : Nat → Nat) (k : Nat) : Nat :=
  (((List.range n).filter fun i => i ≤ k && k - i < n).map fun i => fa i * fb (k - i)).sum

/-- The columns of the first `m` words of `a` times `b`. -/
theorem conv_rows (n : Nat) (fa fb : Nat → Nat) (N : Nat) : ∀ m, m + n ≤ N →
    num (fun k => (((List.range m).filter fun i => i ≤ k && k - i < n).map fun i => fa i * fb (k - i)).sum) N =
      num fa m * num fb n
  | 0, _ => by
    simp only [List.range_zero, List.filter_nil, List.map_nil, List.sum_nil, num_zero, num, Nat.zero_mul]
  | m + 1, h => by
    have e : ∀ k < N, (((List.range (m + 1)).filter fun i => i ≤ k && k - i < n).map
          fun i => fa i * fb (k - i)).sum =
        (((List.range m).filter fun i => i ≤ k && k - i < n).map fun i => fa i * fb (k - i)).sum +
          (if m ≤ k then (if k - m < n then fa m * fb (k - m) else 0) else 0) := by
      intro k _
      rw [List.range_succ, List.filter_append, List.map_append, List.sum_append]
      by_cases h1 : m ≤ k <;> by_cases h2 : k - m < n <;>
        simp only [List.filter_cons, List.filter_nil, h1, h2, decide_true, decide_false, Bool.and_self,
          Bool.and_false, Bool.false_and, ite_true, ite_false, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, Bool.false_eq_true, Nat.add_zero]
    rw [num_congr e, num_add, conv_rows n fa fb N m (by omega_arith), num_succ, Nat.add_mul]
    obtain ⟨d, rfl⟩ : ∃ d, N = m + (n + d) := ⟨N - m - n, by omega_arith⟩
    rw [num_shift (fun j => if j < n then fa m * fb j else 0), num_trunc, num_mul, Nat.mul_assoc]

/-- Product scanning: the columns of `a b`, for numbers of `n` words. -/
theorem conv_identity (n : Nat) (fa fb : Nat → Nat) :
    num (convCol n fa fb) (2 * n) = num fa n * num fb n :=
  conv_rows n fa fb (2 * n) n (by omega_arith)

/-! ## The fold by the prime -/

theorem pow7 : ((2 : Nat) ^ 32) ^ 7 = half := by decide +kernel
theorem pow14 : ((2 : Nat) ^ 32) ^ 14 = full := by decide +kernel

/-- Column `k` of the product's 28 words folded by `2^448 = 2^224 + 1`. -/
def foldCol (p : Nat → Nat) (k : Nat) : Nat :=
  p k + p (k + 14) + if k < 7 then p (k + 21) else p (k + 7) + p (k + 14)

theorem foldCol_val (p : Nat → Nat) :
    num (foldCol p) 14 =
      (num p 7 + num (fun i => p (14 + i)) 7 + num (fun i => p (21 + i)) 7) +
      half * (num (fun i => p (7 + i)) 7 + num (fun i => p (21 + i)) 7 +
        num (fun i => p (14 + i)) 7 + num (fun i => p (21 + i)) 7) := by
  rw [show num (foldCol p) 14 = num (foldCol p) (7 + 7) from rfl, num_split, pow7]
  apply congrArg₂ (· + ·)
  · rw [← num_add, ← num_add]
    apply num_congr
    intro i hi
    simp only [foldCol, ite_eq_left hi, Nat.add_comm i]
  · apply congrArg (half * ·)
    rw [← num_add, ← num_add, ← num_add]
    apply num_congr
    intro i _
    simp only [foldCol, ite_eq_right (by omega_arith : ¬ 7 + i < 7)]
    rw [show 7 + i + 14 = 21 + i by omega_arith, show 7 + i + 7 = 14 + i by omega_arith]
    omega_arith

theorem foldCol_mod (p : Nat → Nat) : num (foldCol p) 14 % Spec.X448.P = num p 28 % Spec.X448.P := by
  have hp : Spec.X448.P = full - half - 1 := by decide +kernel
  have he : num p 28 = num (foldCol p) 14 +
      Spec.X448.P * (num (fun i => p (14 + i)) 7 + (half + 1) * num (fun i => p (21 + i)) 7) := by
    rw [foldCol_val, show 28 = 14 + 14 from rfl, num_split, pow14,
      show 14 = 7 + 7 from rfl, num_split, num_split, pow7]
    simp only [← Nat.add_assoc, Nat.reduceAdd]
    simp only [hp, full, half, radix, Nat.reducePow]
    omega_arith
  rw [he, Nat.add_mul_mod_self_left]

theorem foldCol_lt {p : Nat → Nat} (h : ∀ i < 28, p i < 2 ^ 32) : num (foldCol p) 14 < 4 * full := by
  have b : ∀ d, d + 7 ≤ 28 → num (fun i => p (d + i)) 7 < half := fun d hd => by
    rw [← pow7]; exact num_lt fun i hi => h _ (by omega_arith)
  have b0 : num p 7 < half := by rw [← pow7]; exact num_lt fun i hi => h _ (by omega_arith)
  have b1 := b 7 (by decide); have b2 := b 14 (by decide); have b3 := b 21 (by decide)
  rw [foldCol_val]
  generalize num p 7 = x0 at *
  generalize num (fun i => p (7 + i)) 7 = x1 at *
  generalize num (fun i => p (14 + i)) 7 = x2 at *
  generalize num (fun i => p (21 + i)) 7 = x3 at *
  simp only [full, half, radix, Nat.reducePow] at b0 b1 b2 b3 ⊢
  omega_using [b0, b1, b2, b3]

/-- A number whose words but the first are zero. -/
theorem num_first {f : Nat → Nat} {n : Nat} (h : ∀ k < n + 1, k ≠ 0 → f k = 0) : num f (n + 1) = f 0 := by
  rw [Nat.add_comm, num_split,
    num_congr (g := fun _ => 0) (fun i hi => h (1 + i) (by omega_arith) (by omega_arith)), num_zero,
    Nat.mul_zero, Nat.add_zero]
  simp only [num, Nat.pow_zero, Nat.one_mul, Nat.zero_add]

/-- The carry `c` added to words 0 and 7. -/
theorem carry_val (r : Nat → Nat) (c : Nat) :
    num (fun k => r k + if k = 0 ∨ k = 7 then c else 0) 14 = num r 14 + (half + 1) * c := by
  rw [num_add]
  apply congrArg (num r 14 + ·)
  rw [show num (fun k => if k = 0 ∨ k = 7 then c else 0) 14 =
      num (fun k => if k = 0 ∨ k = 7 then c else 0) (7 + 7) from rfl, num_split, pow7,
    num_first (n := 6) (fun k hk h0 => ite_eq_right (by omega_arith)),
    num_first (n := 6) (fun k hk h0 => ite_eq_right (by omega_arith)),
    ite_eq_left (Or.inl rfl), ite_eq_left (Or.inr rfl), Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- The carry of the first fold of the carry. -/
theorem fold_carry1 {r1 c1 r2 c2 : Nat} (hc1 : c1 ≤ 3) (b1 : r1 < full)
    (h2 : r2 + full * c2 = r1 + (half + 1) * c1) : c2 ≤ 1 := by
  have small : 4 * (half + 1) < full := by decide +kernel
  have m1 : (half + 1) * c1 ≤ (half + 1) * 3 := Nat.mul_le_mul_left _ hc1
  rcases Nat.lt_or_ge c2 2 with h | h
  · exact Nat.le_of_lt_succ h
  · have hp := Nat.mul_le_mul_left full h
    omega_using [hp, m1, small, b1, h2]

/-- The words `r1` and the carry `c1` of the folded product, after the carry
is folded twice: the second fold does not carry. -/
theorem fold_carries {V r1 c1 r2 c2 r3 c3 : Nat} (h1 : r1 + full * c1 = V) (hc1 : c1 ≤ 3)
    (b1 : r1 < full) (b2 : r2 < full) (h2 : r2 + full * c2 = r1 + (half + 1) * c1)
    (h3 : r3 + full * c3 = r2 + (half + 1) * c2) :
    c3 = 0 ∧ r3 % Spec.X448.P = V % Spec.X448.P := by
  have small : 4 * (half + 1) < full := by decide +kernel
  have m1 : (half + 1) * c1 ≤ (half + 1) * 3 := Nat.mul_le_mul_left _ hc1
  have hc2 : c2 ≤ 1 := fold_carry1 hc1 b1 h2
  have hc3 : c3 = 0 := by
    by_contra hn
    have hp := Nat.mul_le_mul_left full (show 1 ≤ c3 from Nat.pos_of_ne_zero hn)
    rcases Nat.eq_zero_or_pos c2 with hc | hc
    · rw [hc, Nat.mul_zero, Nat.add_zero] at h3; omega_using [h3, hp, b2]
    · have hc : c2 = 1 := by omega_arith
      rw [hc, Nat.mul_one] at h2 h3
      omega_using [h2, h3, hp, m1, small, b1]
  refine ⟨hc3, ?_⟩
  rw [hc3, Nat.mul_zero, Nat.add_zero] at h3
  rw [h3, ← fold_mod, h2, ← fold_mod, h1]

/-! ## Words and limbs -/

/-- The number of the words that pack the limbs in pairs. -/
theorem num_pack {w l : Nat → Nat} : ∀ n, (∀ k < n, w k = l (2 * k) + 2 ^ 16 * l (2 * k + 1)) →
    num w n = valN l (2 * n)
  | 0, _ => rfl
  | n + 1, h => by
    rw [num_succ, num_pack n fun k hk => h k (by omega_arith), h n (by omega_arith),
      show 2 * (n + 1) = 2 * n + 1 + 1 from rfl, valN_succ, valN_succ, Nat.pow_succ radix,
      show (2 ^ 32 : Nat) ^ n = radix ^ (2 * n) by
        rw [radix, ← Nat.pow_mul, ← Nat.pow_mul]; exact congrArg (2 ^ ·) (by omega_arith)]
    simp only [radix, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

end VG.Proof.X448.X86

end

end


/-!
# X448 on x86 (32-bit): the product of `vg_gf448_r16_mul`

The operands packed into words (`pack_ok`), their product by X25519's
columns, folded by the prime with its carry (`mulWords_ok`), and the words
unpacked into the limbs of the result (`unpack_ok`).
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16
open VG.Proof.X25519.X86 (num num_succ num_congr num_add num_mul num_lt wd wv acc colv tval treads Ctx
  cols_ok colv_le_len wv_lt wv_mul_le)

/-! ## The working space, as the columns' proofs see it -/

theorem wd_word {s : State} {base : Addr} (hs : Scr s base) (m : Mem) {d : Nat} (hd : d < 8192) :
    wd m (s.gpr .edi) d = word m base d := by
  have := hs.nowrap
  rw [wd, VG.X86.addr_eq (by omega_using [hd, this]), hs.edi]

theorem Scr.ctx {s : State} {base : Addr} (hs : Scr s base) : Ctx 8192 (s.gpr .edi) s false :=
  ⟨rfl, hs.nowrap, by rw [Proof.X25519.X86.scR, hs.edi]; exact hs.wr, by decide, fun h => nomatch h⟩

theorem keeps_of_keep {s t : State} (h : Proof.X25519.X86.Keep s t) : Keeps clob s t :=
  ⟨fun r hr => by
    cases r <;> first | exact h.esi | exact h.edi | exact h.esp | exact absurd (by decide) hr, h.rd, h.wr⟩

/-- A frame of the `n` bytes at offset `d`. -/
theorem Outside.of_frameAt {base : Addr} {d n : Nat} {m m' : Mem} (hd : d + n ≤ 8192)
    (hf : Frame [⟨off base d, n⟩] m m') : Outside base d n m m' :=
  fun x hx => hf x fun r hr => by
    rw [List.mem_singleton.mp hr]
    change ¬ ((x - (base + BitVec.ofNat 64 d)).toNat + 1 ≤ n)
    have := (Offset.lt_iff x base (d := d) (n := n) (by omega_arith)).mp
    simp only [ofs] at hx
    intro h
    have := this (by omega_arith)
    omega_arith

theorem outside_of_frame {s : State} {base : Addr} (hs : Scr s base) {d n : Nat} {m m' : Mem}
    (hd : d + n ≤ 8192) (hn : 0 < n) (hf : Frame [Proof.X25519.X86.sub (s.gpr .edi) d n] m m') :
    Outside base d n m m' := by
  have := hs.nowrap
  rw [Proof.X25519.X86.sub, VG.X86.addr_eq (by omega_using [hd, hn, this]), hs.edi] at hf
  exact Outside.of_frameAt hd hf

/-! ## Packing -/

theorem limb_rotate {w : BitVec 32} (h : w.toNat < 2 ^ 16) : (w.rotateRight 16).toNat = 2 ^ 16 * w.toNat := by
  have hz : w >>> 16 = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    change w.toNat / 2 ^ 16 = 0
    omega_using [h]
  rw [BitVec.rotateRight_def, hz]
  rw [show (0 : BitVec 32) ||| w <<< (32 - 16 % 32) = w <<< 16 from BitVec.zero_or]
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega_using [h]

theorem packWord_ok {s : State} {base : Addr} (hs : Scr s base) {a o k : Nat} (ha : Slot a) (hk : k < 14)
    (ho : o + 56 ≤ 8192) (hp : s.gpr .esi = s.gpr .edi + BitVec.ofNat 32 a)
    (h1 : limbs s.mem base a (2 * k + 1) < radix) :
    WP isa (.block (packWord o k)) s fun t =>
      t.mem = s.mem.writeW (off base (o + 4 * k))
        (BitVec.ofNat 32 (limbs s.mem base a (2 * k) + 2 ^ 16 * limbs s.mem base a (2 * k + 1))) ∧
      Keeps [.eax, .edx] s t := by
  have ha' : a + 112 ≤ 3584 := ha
  unfold packWord
  refine wp_load (a := off base (a + 4 * (2 * k)))
    (by rw [show a + 4 * (2 * k) = a + 8 * k by omega_arith]; exact hs.ea_ptr hp (by omega_arith))
    (hs.read (by omega_arith)) fun t1 u1 => ?_
  have s1 := hs.of_upd u1 (by decide)
  have p1 : t1.gpr .esi = t1.gpr .edi + BitVec.ofNat 32 a := by
    rw [u1.other .esi (by decide), u1.other .edi (by decide)]; exact hp
  refine wp_load (a := off base (a + 4 * (2 * k + 1)))
    (by rw [show a + 4 * (2 * k + 1) = a + (8 * k + 4) by omega_arith]; exact s1.ea_ptr p1 (by omega_arith))
    (s1.read (by omega_arith)) fun t2 u2 => ?_
  refine wp_shift (by decide) fun t3 u3 => ?_
  refine wp_alu (Or.inl rfl) rfl fun t4 u4 _ => ?_
  have s4 := ((s1.of_upd u2 (by decide)).of_upd u3 (by decide)).of_upd u4 (by decide)
  refine store_ok s4 (by omega_arith) fun t5 u5 => WP.block_nil ⟨?_, ?_⟩
  · rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, u4.gpr]
    refine congrArg (s.mem.writeW _) ?_
    change t3.gpr .eax + t3.gpr .edx = _
    rw [u3.other .eax (by decide), u3.gpr, u2.other .eax (by decide), u1.gpr, u2.gpr, u1.mem]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, limb_rotate h1, BitVec.toNat_ofNat]
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans (u5.rest _))))

/-- The element at `esi = ws + a` packed into the fourteen words at `o`. -/
theorem pack_ok {s : State} {base : Addr} (hs : Scr s base) {a o : Nat} (ha : Slot a) (hoa : ACC ≤ o)
    (ho : o + 56 ≤ 8192) (hp : s.gpr .esi = s.gpr .edi + BitVec.ofNat 32 a) (ab : Bounded s.mem base a) :
    WP isa (.block (pack o)) s fun t =>
      num (fun k => (word t.mem base (o + 4 * k)).toNat) 14 = fe s.mem base a ∧
      Outside base o 56 s.mem t.mem ∧ Keeps [.eax, .edx] s t := by
  have ha' : a + 112 ≤ 3584 := ha
  have hoa' : 3584 ≤ o := hoa
  let inv := fun n (t : State) =>
    (∀ k < n, (word t.mem base (o + 4 * k)).toNat =
      limbs s.mem base a (2 * k) + 2 ^ 16 * limbs s.mem base a (2 * k + 1)) ∧
    Outside base o 56 s.mem t.mem ∧ Keeps [.eax, .edx] s t
  obtain step : ∀ n t, n < 14 → inv n t → WP isa (.block (packWord o n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    obtain lt : ∀ i < 28, limbs t.mem base a i = limbs s.mem base a i := fun i hi =>
      tm.limbs (Or.inl (by omega_arith)) (by omega_arith) hi
    obtain tp : t.gpr .esi = t.gpr .edi + BitVec.ofNat 32 a := by
      rw [tk.1 _ (by decide), tk.1 _ (by decide)]; exact hp
    refine WP.mono (packWord_ok (hs.of_keeps tk (by decide)) ha hn ho tp
      (by rw [lt _ (by omega_arith)]; exact ab _ (by omega_arith))) fun u ⟨um, uk⟩ => ?_
    rw [lt _ (by omega_arith), lt _ (by omega_arith)] at um
    obtain out : Outside base (o + 4 * n) 4 t.mem u.mem := by
      rw [um]; exact writeW_outside _ _ _ (by omega_arith)
    refine ⟨?_, tm.trans (out.mono (by omega_arith) (by omega_arith)), tk.trans uk⟩
    intro k hk
    rw [um, word_write t.mem base (by omega_arith) (by omega_arith)]
    by_cases h : k = n
    · have b0 := ab (2 * n) (by omega_arith)
      have b1 := ab (2 * n + 1) (by omega_arith)
      simp only [radix] at b0 b1
      rw [ite_eq_left h, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    · rw [ite_eq_right h]; exact tf k (by omega_arith)
  refine WP.mono (wp_range_flatMap (M := isa) (N := 14) inv step 14 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩) fun t ⟨tf, tm, tk⟩ => ⟨?_, tm, tk⟩
  exact num_pack 14 tf

/-! ## The columns -/

theorem prodTerms_reads {k : Nat} : ∀ t ∈ prodTerms k, ∀ d ∈ treads t, d + 4 ≤ PROD := by
  intro t ht d hd
  simp only [prodTerms, List.mem_map, List.mem_filter, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at ht
  obtain ⟨i, ⟨hi, -, hki⟩, rfl⟩ := ht
  simp only [treads, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl <;> simp only [PA, PB, PROD, ACC] <;> omega_arith

theorem prodTerms_colv (m : Mem) (x : BitVec 32) (k : Nat) :
    colv m x (prodTerms k) = convCol 14 (fun i => wv m x (PA + 4 * i)) (fun j => wv m x (PB + 4 * j)) k := by
  simp only [colv, prodTerms, convCol, List.map_map]; rfl

theorem prodTerms_lt (m : Mem) (x : BitVec 32) (k : Nat) : colv m x (prodTerms k) < 2 ^ 68 := by
  have hl : (prodTerms k).length ≤ 14 := by
    simp only [prodTerms, List.length_map]
    exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  have h1 := colv_le_len (m := m) (x := x) (B := 2 ^ 64) (ts := prodTerms k) fun t ht => by
    simp only [prodTerms, List.mem_map] at ht
    obtain ⟨i, -, rfl⟩ := ht
    exact wv_mul_le _ _ _ _
  have h2 := Nat.mul_le_mul_right (2 ^ 64) hl
  omega_using [h1, h2]

theorem foldTerms_reads {k : Nat} (hk : k < 14) : ∀ t ∈ foldTerms k, ∀ d ∈ treads t, d + 4 ≤ RED := by
  intro t ht d hd
  unfold foldTerms at ht
  split at ht
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> simp only [treads, List.mem_singleton] at hd <;> subst hd <;>
      simp only [PROD, RED, ACC, TMP] <;> omega_arith
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> simp only [treads, List.mem_singleton] at hd <;> subst hd <;>
      simp only [PROD, RED, ACC, TMP] <;> omega_arith

theorem foldTerms_colv (m : Mem) (x : BitVec 32) (k : Nat) :
    colv m x (foldTerms k) = foldCol (fun j => wv m x (PROD + 4 * j)) k := by
  unfold foldTerms foldCol
  split <;> simp only [colv, tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.cons_append, List.nil_append, Nat.add_zero, Nat.add_assoc]

theorem foldTerms_lt (m : Mem) (x : BitVec 32) (k : Nat) : colv m x (foldTerms k) < 2 ^ 68 := by
  rw [foldTerms_colv, foldCol]
  have h0 := wv_lt m x (PROD + 4 * k)
  have h1 := wv_lt m x (PROD + 4 * (k + 14))
  have h2 := wv_lt m x (PROD + 4 * (k + 21))
  have h3 := wv_lt m x (PROD + 4 * (k + 7))
  split <;> omega_using [h0, h1, h2, h3]

theorem carryTerms_colv (m : Mem) (x : BitVec 32) (k : Nat) :
    colv m x (carryTerms k) = wv m x (RED + 4 * k) + if k = 0 ∨ k = 7 then wv m x CW else 0 := by
  unfold carryTerms
  split <;> simp only [colv, tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]

/-- The carry in the accumulator folded into the words at `RED`, as `2^448 = 2^224 + 1`. -/
theorem foldCarry_ok {x : BitVec 32} {s : State} (hc : Ctx 8192 x s false) (ha : acc s < 2 ^ 32) :
    WP isa (.block foldCarry) s fun t => Proof.X25519.X86.Keep s t ∧
      Frame [Proof.X25519.X86.sub x RED 60] s.mem t.mem ∧
      num (fun k => wv t.mem x (RED + 4 * k)) 14 + (2 ^ 32) ^ 14 * acc t =
        num (fun k => wv s.mem x (RED + 4 * k)) 14 + (half + 1) * acc s ∧ acc t < 2 ^ 40 := by
  have hfit := hc.fit4
  change WP isa (.block (.store ⟨.edi, CW⟩ .ebx ::
    (Impl.X25519.X86.zeroAcc ++ Impl.X25519.X86.cols RED 14 carryTerms))) s _
  refine Wp.wp_stm hc.edi (hc.inW4 (by decide) (by decide)) fun s₁ u₁ => ?_
  have k₁ : Proof.X25519.X86.Keep s s₁ := ⟨by rw [u₁.gpr], by rw [u₁.gpr], by rw [u₁.gpr], u₁.rd, u₁.wr⟩
  have c₁ := k₁.ctx hc
  refine WP.block_append (WP.mono Proof.X25519.X86.zeroAcc_ok fun s₂ ⟨k₂, m₂, a₂⟩ => ?_)
  have c₂ := k₂.ctx c₁
  have hw : ∀ k < 14, wv s₂.mem x (RED + 4 * k) = wv s.mem x (RED + 4 * k) := fun k hk => by
    rw [m₂, u₁.mem, wv, Proof.X25519.X86.wd_write_ne _ _ (by simp only [RED, TMP]; omega_arith)
      (by simp only [CW, TMP]; omega_arith) (Or.inl (by simp only [RED, CW]; omega_arith))]
  have hcw : wv s₂.mem x CW = acc s := by
    rw [m₂, u₁.mem, wv, Proof.X25519.X86.wd_write_self]
    have hb := (s.gpr .ebx).isLt
    simp only [acc, Proof.X25519.X86.v] at ha ⊢
    omega_using [ha, hb]
  refine WP.mono (cols_ok c₂ carryTerms 14 (by decide) (fun k hk t ht d hd => ?_) (fun k hk => ?_)
    (by rw [a₂]; decide)) fun s₃ ⟨k₃, f₃, e₃, a₃⟩ => ⟨k₁.trans (k₂.trans k₃), ?_, ?_, a₃⟩
  · unfold carryTerms at ht
    split at ht
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> simp only [treads, List.mem_singleton] at hd <;> subst hd <;>
        simp only [RED, CW, TMP] <;> omega_arith
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      subst ht
      simp only [treads, List.mem_singleton] at hd
      subst hd
      simp only [RED, TMP]; omega_arith
  · rw [carryTerms_colv]
    have h0 := wv_lt s₂.mem x (RED + 4 * k)
    have h1 := wv_lt s₂.mem x CW
    split <;> omega_using [h0, h1]
  · rw [m₂, u₁.mem] at f₃
    refine (Proof.X25519.X86.frame_write1 (Frame.refl _ _) hfit (by decide) (d := CW) (by decide) (by decide) _).trans
      (Proof.X25519.X86.frameWiden f₃ hfit (Nat.le_refl _) (by decide) (by decide))
  · rw [a₂, Nat.zero_add] at e₃
    rw [e₃, ← carry_val, ← hcw]
    exact num_congr fun k hk => by rw [carryTerms_colv, hw k hk]

/-- The words at `PA` and `PB` multiplied, modulo the prime, into the fourteen words at `RED`. -/
theorem mulWords_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block mulWords) s fun t =>
      num (fun k => (word t.mem base (RED + 4 * k)).toNat) 14 % Spec.X448.P =
        num (fun k => (word s.mem base (PA + 4 * k)).toNat) 14 *
          num (fun k => (word s.mem base (PB + 4 * k)).toNat) 14 % Spec.X448.P ∧
      Outside base PROD 204 s.mem t.mem ∧ Keeps clob s t := by
  have hc := hs.ctx
  have eA : num (fun k => (word s.mem base (PA + 4 * k)).toNat) 14 =
      num (fun k => wv s.mem (s.gpr .edi) (PA + 4 * k)) 14 :=
    num_congr fun k hk => by rw [wv, wd_word hs _ (by simp only [PA, ACC]; omega_arith)]
  have eB : num (fun k => (word s.mem base (PB + 4 * k)).toNat) 14 =
      num (fun k => wv s.mem (s.gpr .edi) (PB + 4 * k)) 14 :=
    num_congr fun k hk => by rw [wv, wd_word hs _ (by simp only [PB, ACC]; omega_arith)]
  rw [eA, eB]
  refine WP.block_append (WP.block_append (WP.block_append (WP.block_append
    (WP.mono Proof.X25519.X86.zeroAcc_ok fun s₁ ⟨k₁, m₁, a₁⟩ => ?_))))
  have c₁ := k₁.ctx hc
  refine WP.mono (cols_ok c₁ prodTerms 28 (by decide) (fun k hk t ht d hd => ?_)
    (fun k hk => prodTerms_lt _ _ _) (by rw [a₁]; decide)) fun s₂ ⟨k₂, f₂, e₂, _⟩ => ?_
  · have := prodTerms_reads t ht d hd
    simp only [PROD, ACC] at this ⊢
    exact ⟨by omega_using [this], .inl this⟩
  rw [a₁, Nat.zero_add, m₁] at e₂
  rw [m₁] at f₂
  have eP : num (fun k => colv s.mem (s.gpr .edi) (prodTerms k)) 28 =
      num (fun i => wv s.mem (s.gpr .edi) (PA + 4 * i)) 14 *
        num (fun j => wv s.mem (s.gpr .edi) (PB + 4 * j)) 14 := by
    rw [← conv_identity 14]
    exact num_congr fun k _ => prodTerms_colv _ _ _
  rw [eP] at e₂
  have hA := num_lt (f := fun i => wv s.mem (s.gpr .edi) (PA + 4 * i)) (n := 14) fun _ _ => wv_lt _ _ _
  have hB := num_lt (f := fun j => wv s.mem (s.gpr .edi) (PB + 4 * j)) (n := 14) fun _ _ => wv_lt _ _ _
  generalize num (fun i => wv s.mem (s.gpr .edi) (PA + 4 * i)) 14 = va at *
  generalize num (fun j => wv s.mem (s.gpr .edi) (PB + 4 * j)) 14 = vb at *
  have hAB : va * vb < (2 ^ 32) ^ 28 := by
    have := Nat.mul_lt_mul_of_lt_of_lt hA hB
    rwa [← Nat.pow_add] at this
  have z₂ : acc s₂ = 0 := by
    rcases Nat.eq_zero_or_pos (acc s₂) with h | h
    · exact h
    · have := Nat.mul_le_mul_left ((2 ^ 32) ^ 28) h
      omega_using [this, e₂, hAB]
  rw [z₂, Nat.mul_zero, Nat.add_zero] at e₂
  have c₂ := k₂.ctx c₁
  refine WP.mono (cols_ok c₂ foldTerms 14 (by decide) (fun k hk t ht d hd => ?_)
    (fun k hk => foldTerms_lt _ _ _) (by rw [z₂]; decide)) fun s₃ ⟨k₃, f₃, e₃, _⟩ => ?_
  · have := foldTerms_reads hk t ht d hd
    simp only [RED, TMP] at this ⊢
    exact ⟨by omega_using [this], .inl this⟩
  rw [z₂, Nat.zero_add, pow14] at e₃
  have eF : num (fun k => colv s₂.mem (s.gpr .edi) (foldTerms k)) 14 =
      num (foldCol fun j => wv s₂.mem (s.gpr .edi) (PROD + 4 * j)) 14 :=
    num_congr fun k _ => foldTerms_colv _ _ _
  rw [eF] at e₃
  have hF := foldCol_mod fun j => wv s₂.mem (s.gpr .edi) (PROD + 4 * j)
  have hFlt := foldCol_lt (p := fun j => wv s₂.mem (s.gpr .edi) (PROD + 4 * j)) fun i _ => wv_lt _ _ _
  rw [e₂] at hF
  generalize num (foldCol fun j => wv s₂.mem (s.gpr .edi) (PROD + 4 * j)) 14 = V at *
  have r1 := num_lt (f := fun k => wv s₃.mem (s.gpr .edi) (RED + 4 * k)) (n := 14) fun _ _ => wv_lt _ _ _
  rw [pow14] at r1
  have hc1 : acc s₃ ≤ 3 := by
    rcases Nat.lt_or_ge (acc s₃) 4 with h | h
    · exact Nat.le_of_lt_succ h
    · have := Nat.mul_le_mul_left full h
      omega_using [this, e₃, hFlt]
  have c₃ := k₃.ctx c₂
  refine WP.mono (foldCarry_ok c₃ (by omega_using [hc1])) fun s₄ ⟨k₄, f₄, e₄, _⟩ => ?_
  rw [pow14] at e₄
  have r2 := num_lt (f := fun k => wv s₄.mem (s.gpr .edi) (RED + 4 * k)) (n := 14) fun _ _ => wv_lt _ _ _
  rw [pow14] at r2
  have hc2 := fold_carry1 hc1 r1 e₄
  have c₄ := k₄.ctx c₃
  refine WP.mono (foldCarry_ok c₄ (by omega_using [hc2])) fun s₅ ⟨k₅, f₅, e₅, _⟩ => ?_
  rw [pow14] at e₅
  obtain ⟨-, hv⟩ := fold_carries e₃ hc1 r1 r2 e₄ e₅
  refine ⟨?_, ?_, keeps_of_keep (k₁.trans (k₂.trans (k₃.trans (k₄.trans k₅))))⟩
  · rw [← hF, ← hv]
    exact congrArg (· % Spec.X448.P) (num_congr fun k hk => by
      rw [wv, wd_word hs _ (by simp only [RED, TMP]; omega_arith)])
  · have o₂ := outside_of_frame hs (by decide) (by decide) f₂
    have o₃ := outside_of_frame hs (by decide) (by decide) f₃
    have o₄ := outside_of_frame hs (by decide) (by decide) f₄
    have o₅ := outside_of_frame hs (by decide) (by decide) f₅
    exact (o₂.mono (by decide) (by decide)).trans ((o₃.mono (by decide) (by decide)).trans
      ((o₄.mono (by decide) (by decide)).trans (o₅.mono (by decide) (by decide))))

/-! ## Unpacking -/

theorem unpackWord_ok {s : State} {base : Addr} (hs : Scr s base) {o k : Nat} (ho : Slot o) (hk : k < 14)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 o) :
    WP isa (.block (unpackWord k)) s fun t =>
      t.mem = (s.mem.writeW (off base (o + 4 * (2 * k)))
          (BitVec.ofNat 32 ((word s.mem base (RED + 4 * k)).toNat % 2 ^ 16))).writeW
        (off base (o + 4 * (2 * k + 1)))
          (BitVec.ofNat 32 ((word s.mem base (RED + 4 * k)).toNat / 2 ^ 16)) ∧
      Keeps [.eax, .edx] s t := by
  have ho' : o + 112 ≤ 3584 := ho
  have hw := (word s.mem base (RED + 4 * k)).isLt
  unfold unpackWord
  refine load_ok hs (by simp only [RED, TMP]; omega_arith) fun t1 u1 => ?_
  refine wp_mov rfl fun t2 u2 => ?_
  refine wp_alu (Or.inr (Or.inr (Or.inl rfl))) rfl fun t3 u3 _ => ?_
  refine wp_shift (by decide) fun t4 u4 => ?_
  have k4 : Keeps [.eax, .edx] s t4 := (u1.rest (by decide)).trans ((u2.rest (by decide)).trans
    ((u3.rest (by decide)).trans (u4.rest (by decide))))
  have s4 := hs.of_keeps k4 (by decide)
  have p4 : t4.gpr .ebp = t4.gpr .edi + BitVec.ofNat 32 o := by
    rw [k4.1 _ (by decide), k4.1 _ (by decide)]; exact hp
  have va : t4.gpr .eax = BitVec.ofNat 32 ((word s.mem base (RED + 4 * k)).toNat % 2 ^ 16) := by
    rw [u4.other .eax (by decide), u3.gpr]
    change t2.gpr .eax &&& 65535 = _
    rw [u2.other .eax (by decide), u1.gpr]
    apply BitVec.eq_of_toNat_eq
    rw [and16_nat, BitVec.toNat_ofNat, radix, Nat.mod_eq_of_lt (a := _ % 2 ^ 16) (by omega_using [hw])]
  have vd : t4.gpr .edx = BitVec.ofNat 32 ((word s.mem base (RED + 4 * k)).toNat / 2 ^ 16) := by
    rw [u4.gpr]
    change t3.gpr .edx >>> 16 = _
    rw [u3.other .edx (by decide), u2.gpr, u1.gpr]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := _ / 2 ^ 16) (by omega_using [hw])]
  refine wp_store (a := off base (o + 4 * (2 * k)))
    (by rw [show o + 4 * (2 * k) = o + 8 * k by omega_arith]; exact s4.ea_ptr p4 (by omega_arith))
    (s4.write (by omega_arith)) fun t5 u5 => ?_
  have s5 := s4.of_keeps (u5.rest []) (by decide)
  have p5 : t5.gpr .ebp = t5.gpr .edi + BitVec.ofNat 32 o := by rw [u5.gpr]; exact p4
  refine wp_store (a := off base (o + 4 * (2 * k + 1)))
    (by rw [show o + 4 * (2 * k + 1) = o + (8 * k + 4) by omega_arith]; exact s5.ea_ptr p5 (by omega_arith))
    (s5.write (by omega_arith)) fun t6 u6 => WP.block_nil ⟨?_, k4.trans ((u5.rest _).trans (u6.rest _))⟩
  rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, u5.gpr, va, vd]

/-- The fourteen words at `RED` unpacked into the limbs of the element at `ebp = ws + o`. -/
theorem unpack_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : Slot o)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 o) :
    WP isa (.block unpack) s fun t =>
      Bounded t.mem base o ∧
      fe t.mem base o = num (fun k => (word s.mem base (RED + 4 * k)).toNat) 14 ∧
      Outside base o 112 s.mem t.mem ∧ Keeps [.eax, .edx] s t := by
  have ho' : o + 112 ≤ 3584 := ho
  let inv := fun n (t : State) =>
    (∀ k < n, limbs t.mem base o (2 * k) = (word s.mem base (RED + 4 * k)).toNat % 2 ^ 16 ∧
      limbs t.mem base o (2 * k + 1) = (word s.mem base (RED + 4 * k)).toNat / 2 ^ 16) ∧
    Outside base o 112 s.mem t.mem ∧ Keeps [.eax, .edx] s t
  obtain step : ∀ n t, n < 14 → inv n t → WP isa (.block (unpackWord n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    obtain tp : t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 o := by
      rw [tk.1 _ (by decide), tk.1 _ (by decide)]; exact hp
    obtain wt : word t.mem base (RED + 4 * n) = word s.mem base (RED + 4 * n) :=
      tm.word (Or.inr (by simp only [RED, TMP]; omega_arith)) (by simp only [RED, TMP]; omega_arith)
    have hw := (word s.mem base (RED + 4 * n)).isLt
    refine WP.mono (unpackWord_ok (hs.of_keeps tk (by decide)) ho hn tp) fun u ⟨um, uk⟩ => ?_
    rw [wt] at um
    obtain out : Outside base o 112 t.mem u.mem := by
      rw [um]
      exact ((writeW_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith)).trans
        ((writeW_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
    refine ⟨fun k hk => ⟨?_, ?_⟩, tm.trans out, tk.trans uk⟩
    · change (word u.mem base (o + 4 * (2 * k))).toNat = _
      rw [um, word_write _ base (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith),
        word_write _ base (by omega_arith) (by omega_arith)]
      by_cases h : k = n
      · rw [ite_eq_left (by omega_arith), h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hw])]
      · rw [ite_eq_right (by omega_arith)]; exact (tf k (by omega_arith)).1
    · change (word u.mem base (o + 4 * (2 * k + 1))).toNat = _
      rw [um, word_write _ base (by omega_arith) (by omega_arith)]
      by_cases h : k = n
      · rw [ite_eq_left (by omega_arith), h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hw])]
      · rw [ite_eq_right (by omega_arith), word_write _ base (by omega_arith) (by omega_arith),
          ite_eq_right (by omega_arith)]
        exact (tf k (by omega_arith)).2
  refine WP.mono (wp_range_flatMap (M := isa) (N := 14) inv step 14 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩) fun t ⟨tf, tm, tk⟩ => ⟨?_, ?_, tm, tk⟩
  · intro i hi
    have hw := (word s.mem base (RED + 4 * (i / 2))).isLt
    rcases Nat.mod_two_eq_zero_or_one i with h | h
    · rw [show i = 2 * (i / 2) by omega_arith, (tf (i / 2) (by omega_arith)).1, radix]
      exact Nat.mod_lt _ (by decide)
    · rw [show i = 2 * (i / 2) + 1 by omega_arith, (tf (i / 2) (by omega_arith)).2, radix]
      omega_using [hw]
  · refine (num_pack 14 fun k hk => ?_).symm
    rw [(tf k hk).1, (tf k hk).2, Nat.mod_add_div]

/-! ## The function's body -/

/-- An argument after code that keeps `esp` and writes only the working space. -/
theorem ArgArea.arg_keep {s t : State} {base : Addr} {n : Nat} (h : ArgArea s base n) {rs : List Reg}
    (hk : Keeps rs s t) (hr : .esp ∉ rs) (hm : Outside base 0 8192 s.mem t.mem) {i : Nat} (hi : i < n) :
    arg t i = arg s i :=
  (h.keep (hk.1 _ hr) hk.2.1 hk.2.2 hm).2 i hi

/-- `vg_gf448_r16_mul` between its entry and its exit. -/
theorem mulBody_ok {t : State} {base : Addr} {o a b : Nat} (tc : FnCtx t base 4 o a)
    (hvb : arg t 3 = BitVec.ofNat 32 b) (hb : Slot b) (ab : Bounded t.mem base a)
    (bb : Bounded t.mem base b) :
    WP isa (.block (argPtr .esi 2 ++ pack PA ++ argPtr .esi 3 ++ pack PB ++ mulWords ++ argPtr .ebp 1 ++
      unpack)) t fun w =>
      FieldMem base o t.mem w.mem WORK ∧ Bounded w.mem base o ∧
      F w.mem base o = F t.mem base a * F t.mem base b ∧ Keeps (.esi :: clob) t w := by
  have ha' : a + 112 ≤ 3584 := tc.slotA
  have hb' : b + 112 ≤ 3584 := hb
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (argPtr_ok tc.args (by decide) (by decide) tc.argA) fun s1 ⟨p1, m1, k1⟩ => ?_
  have c1 := tc.keep k1 (by decide) (by decide) (by rw [m1]; exact Outside.refl _ _ _ _)
  rw [WP.block_append_iff]
  refine WP.mono (pack_ok c1.scr tc.slotA (by decide) (by decide) p1 (by rw [m1]; exact ab))
    fun s2 ⟨v2, m2, k2⟩ => ?_
  rw [m1] at v2 m2
  have k02 : Keeps (.esi :: clob) t s2 := (k1.mono (by decide)).trans (k2.mono (by decide))
  have o2 : Outside base 0 8192 t.mem s2.mem := m2.mono (by decide) (by decide)
  have c2 := tc.keep k02 (by decide) (by decide) o2
  rw [WP.block_append_iff]
  refine WP.mono (argPtr_ok c2.args (by decide) (by decide)
    ((tc.args.arg_keep k02 (by decide) o2 (by decide)).trans hvb)) fun s3 ⟨p3, m3, k3⟩ => ?_
  have c3 := c2.keep k3 (by decide) (by decide) (by rw [m3]; exact Outside.refl _ _ _ _)
  have bb3 : Bounded s3.mem base b := fun i hi => by
    rw [m3, m2.limbs (Or.inl (by simp only [PA, ACC]; omega_arith)) (by omega_arith) hi]; exact bb i hi
  rw [WP.block_append_iff]
  refine WP.mono (pack_ok c3.scr hb (by decide) (by decide) p3 bb3) fun s4 ⟨v4, m4, k4⟩ => ?_
  rw [m3] at v4 m4
  rw [m2.fe (Or.inl (by simp only [PA, ACC]; omega_arith)) (by omega_arith)] at v4
  have va : num (fun k => (word s4.mem base (PA + 4 * k)).toNat) 14 = fe t.mem base a := by
    rw [← v2]
    exact Proof.X25519.X86.num_congr fun k hk => by
      rw [m4.word (Or.inl (by simp only [PA, PB]; omega_arith)) (by simp only [PA, ACC]; omega_arith)]
  have k24 : Keeps (.esi :: clob) s2 s4 := (k3.mono (by decide)).trans (k4.mono (by decide))
  have c4 := c2.keep k24 (by decide) (by decide) (m4.mono (by decide) (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (mulWords_ok c4.scr) fun s5 ⟨v5, m5, k5⟩ => ?_
  rw [va, v4] at v5
  have c5 := c4.keep k5 (by decide) (by decide) (m5.mono (by decide) (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (argPtr_ok c5.args (by decide) (by decide) c5.argO) fun s6 ⟨p6, m6, k6⟩ => ?_
  have c6 := c5.keep k6 (by decide) (by decide) (by rw [m6]; exact Outside.refl _ _ _ _)
  refine WP.mono (unpack_ok c6.scr tc.slotO p6) fun s7 ⟨b7, v7, m7, k7⟩ => ⟨?_, b7, ?_, ?_⟩
  · rw [m6] at m7
    exact (FieldMem.work m2 (by decide) (by decide)).trans ((FieldMem.work m4 (by decide) (by decide)).trans
      ((FieldMem.work m5 (by decide) (by decide)).trans (FieldMem.output m7)))
  · rw [m6] at v7
    exact toFe_mul (by rw [v7, v5])
  · exact k02.trans (k24.trans ((k5.mono (by decide)).trans ((k6.mono (by decide)).trans
      (k7.mono (by decide)))))

end VG.Proof.X448.X86

end

end


/-!
# X448 on x86 (32-bit): the field functions

`vg_gf448_r16_{mul,add,sub,mul_a24}` (`Impl/X448/X86.lean`) from their entry
(`FnEntry`: the working space `ws` at `base` and the offsets on the stack):
`fnEntry` loads `ws` into `edi` and saves the callee-saved registers in the
last 16 bytes of the functions' own working space (`fnEntry_ok`), the
operation writes its result (`Mul.lean`, `AddSub.lean`, `Small.lean`), and
`fnExit` restores the registers (`fnExit_ok`). Each function changes only
`eax`, `ecx`, `edx` and the flags, the result and its own working space
(`FnOut`).
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

/-- A field function's entry: the working space `ws` (its first argument) at
`base`, writable and not wrapping around; the first `n` arguments readable
outside it, as is the return address; the offsets `o` and `a` of the result
and the first operand, below the functions' own working space. -/
structure FnEntry (s : State) (base : Addr) (n o a : Nat) : Prop where
  ws : (arg s 0).setWidth 64 = base
  wr : (⟨base, 8192⟩ : Region) ∈ s.wr
  nowrap : (arg s 0).toNat + 8192 ≤ 2 ^ 32
  args : ArgArea s base n
  n3 : 3 ≤ n
  ret : ∀ k < 4, 8192 ≤ ofs base ((s.gpr .esp).setWidth 64 + BitVec.ofNat 64 k)
  argO : arg s 1 = BitVec.ofNat 32 o
  argA : arg s 2 = BitVec.ofNat 32 a
  slotO : Slot o
  slotA : Slot a

/-- What a field function changes: `eax`, `ecx` and `edx`, and in memory
the result at `o` and its own working space; the result's limbs are below
`2^16`. -/
structure FnOut (base : Addr) (o : Nat) (s t : State) : Prop where
  keeps : Keeps [.eax, .ecx, .edx] s t
  mem : FieldMem base o s.mem t.mem
  bounded : Bounded t.mem base o

/-- Where the field functions save the callee-saved registers. -/
def fnSlots : Spill.Slots := [(.ebx, SAVE), (.esi, SAVE + 4), (.edi, SAVE + 8), (.ebp, SAVE + 12)]

theorem fnSlots_fits : Spill.Fits 8192 fnSlots := by decide

abbrev FnSaved (base : Addr) (g : Reg → BitVec 32) (m : Mem) : Prop := Spill.Saved m (off base) g fnSlots

theorem fnEntry_ok {s : State} {base : Addr} {n o a : Nat} (h : FnEntry s base n o a) :
    WP isa (.block fnEntry) s fun t =>
      FnCtx t base n o a ∧ FnSaved base s.gpr t.mem ∧ Outside base SAVE 16 s.mem t.mem ∧
      Keeps [.eax, .edi] s t := by
  change WP isa (.block (.mov .eax (.mem (argOp 0)) ::
    (Spill.saveCode .eax fnSlots ++ [.mov .edi (.reg .eax)]))) s _
  refine h.args.load (by have := h.n3; omega_arith) fun t ht => ?_
  refine Spill.save_ofNat_ok fnSlots fnSlots_fits (by rw [ht.gpr]; exact h.nowrap)
    (fun p hp => by
      rw [ht.gpr, ht.wr, h.ws]
      exact ⟨_, h.wr, contains_sc (by have := fnSlots_fits.1 p hp; omega_arith)⟩) fun u hu => ?_
  obtain hm : u.mem = Spill.saveMem s.mem (off base) s.gpr fnSlots := by
    rw [hu.mem, ht.gpr, ht.mem, h.ws]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp => ht.other _ (by revert p hp; decide)
  refine wp_mov rfl fun v hv => WP.block_nil ?_
  obtain kv : Keeps [.eax, .edi] s v :=
    ((ht.rest (by decide)).trans (⟨fun r _ => by rw [hu.gpr], hu.rd, hu.wr⟩ : Keeps [.eax, .edi] t u)).trans
      (hv.rest (by decide))
  obtain mv : Outside base SAVE 16 s.mem v.mem := by
    rw [hv.mem, hm]
    refine Outside.of_frameAt (by decide) (Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p hp => ?_)
    have := fnSlots_fits.1 p hp
    obtain h2 : SAVE ≤ p.2 ∧ p.2 + 4 ≤ SAVE + 16 := by revert p hp; decide
    exact Offset.contains _ h2.1 h2.2 (by simp only [SAVE]; omega_arith)
  obtain vs : Scr v base := ⟨by rw [hv.gpr, hu.gpr, ht.gpr]; exact h.ws, by rw [hv.wr, hu.wr, ht.wr]; exact h.wr,
    by rw [hv.gpr, hu.gpr, ht.gpr]; exact h.nowrap⟩
  obtain ⟨va, varg⟩ := h.args.keep (kv.1 _ (by decide)) kv.2.1 kv.2.2 (mv.mono (by decide) (by decide))
  refine ⟨⟨vs, va, h.n3, by rw [varg 1 (by have := h.n3; omega_arith)]; exact h.argO,
    by rw [varg 2 (by have := h.n3; omega_arith)]; exact h.argA, h.slotO, h.slotA⟩, ?_, mv, kv⟩
  rw [hv.mem, hm]
  exact Spill.saveMem_saved_ofNat _ _ _ fnSlots_fits (by decide)

theorem fnExit_ok {s : State} {base : Addr} (hs : Scr s base) {g : Reg → BitVec 32}
    (hsv : FnSaved base g s.mem) :
    WP isa (.block fnExit) s fun t =>
      (∀ r ∈ [Reg.ebx, .esi, .edi, .ebp], t.gpr r = g r) ∧ t.mem = s.mem ∧
      Keeps [.ebx, .esi, .edi, .ebp] s t := by
  change WP isa (.block (Spill.restoreCode .edi ([(.ebx, SAVE), (.esi, SAVE + 4), (.ebp, SAVE + 12)] ++
    [(.edi, SAVE + 8)]) ++ [])) s _
  have hb : (s.gpr .edi).setWidth 64 = base := hs.edi
  obtain slot : ∀ p ∈ ([(.ebx, SAVE), (.esi, SAVE + 4), (.ebp, SAVE + 12)] ++ [(.edi, SAVE + 8)] : Spill.Slots),
      p ∈ fnSlots := by decide
  refine Spill.restoreBase_ok (g := g) _ (by decide) (fun p hp => ?_) (fun p hp => ?_) fun t ht => WP.block_nil ?_
  · have := fnSlots_fits.1 p (slot p hp)
    rw [Spill.addr_eq_of hs.nowrap (n := 8192) (by omega_arith), hb]
    exact hs.read (by omega_arith)
  · have := fnSlots_fits.1 p (slot p hp)
    rw [Spill.addr_eq_of hs.nowrap (n := 8192) (by omega_arith), hb]
    exact hsv p (slot p hp)
  · refine ⟨fun r hr => ?_, ht.mem, ⟨fun r hr => ht.other r (by
      simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, not_or] at hr ⊢
      exact ⟨⟨hr.1, hr.2.1, hr.2.2.2⟩, hr.2.2.1⟩), ht.rd, ht.wr⟩⟩
    have := ht.regs r (by revert r hr; decide)
    exact this

theorem FnSaved.keep {base : Addr} {g : Reg → BitVec 32} {m m' : Mem} (hs : FnSaved base g m)
    {o : Nat} (ho : Slot o) (h : FieldMem base o m m' WORK) : FnSaved base g m' := by
  have ho' : o + 112 ≤ 3584 := ho
  refine hs.of_readW fun p hp => ?_
  obtain hp' : SAVE ≤ p.2 ∧ p.2 + 4 ≤ SAVE + 16 := by revert p hp; decide
  obtain hs' : p.2 + 4 < 2 ^ 64 := by simp only [SAVE] at hp'; omega_arith
  exact Mem.readW_congr fun i hi => h _
    (Or.inr (by rw [ofs_off base (d := p.2) (i := i) (by omega_arith)]; simp only [SAVE] at hp'; omega_arith))
    (Or.inr (by rw [ofs_off base (d := p.2) (i := i) (by omega_arith)]; simp only [SAVE, ACC, WORK, TMP] at hp' ⊢; omega_arith))

/-- The exit, after a body that changed the registers `rs` (not `esp`) and,
in the working space, the result and the arithmetic's own bytes. -/
theorem fnExit_out {s t u : State} {base : Addr} {n o a : Nat} (tc : FnCtx t base n o a)
    (tv : FnSaved base s.gpr t.mem) (tm : Outside base SAVE 16 s.mem t.mem) (tk : Keeps [.eax, .edi] s t)
    {rs : List Reg} (hrs : .esp ∉ rs) (uk : Keeps rs t u) (us : Scr u base)
    (um : FieldMem base o t.mem u.mem WORK) (ub : Bounded u.mem base o) :
    WP isa (.block fnExit) u fun w => FnOut base o s w ∧ w.mem = u.mem := by
  refine WP.mono (fnExit_ok us (tv.keep tc.slotO um)) fun w ⟨wr, wm, wk⟩ => ?_
  refine ⟨⟨⟨fun r hr => ?_, wk.2.1.trans (uk.2.1.trans tk.2.1), wk.2.2.trans (uk.2.2.trans tk.2.2)⟩,
    ?_, by rw [wm]; exact ub⟩, wm⟩
  · by_cases hs : r ∈ [Reg.ebx, .esi, .edi, .ebp]
    · exact wr r hs
    · have hr' : r = .esp := by
        cases r <;> first | rfl | exact absurd (by decide) hr | exact absurd (by decide) hs
      subst hr'
      rw [wk.1 _ (by decide), uk.1 _ hrs, tk.1 _ (by decide)]
  · rw [wm]
    exact (FieldMem.work tm (by decide) (by decide)).trans (um.mono (by decide))

/-- A field function of one block: its entry, its `body`, and its exit. -/
theorem fnBlock_ok {s : State} {base : Addr} {n o a : Nat} (h : FnEntry s base n o a) {body : List Instr}
    {Q : Mem → Prop}
    (hb : ∀ t, FnCtx t base n o a → Outside base SAVE 16 s.mem t.mem → Keeps [.eax, .edi] s t →
      WP isa (.block body) t fun u => FnPost base o t u ∧ Q u.mem) :
    WP isa (.block (fnEntry ++ body ++ fnExit)) s fun w => FnOut base o s w ∧ Q w.mem := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (fnEntry_ok h) fun t ⟨tc, tv, tm, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hb t tc tm tk) fun u ⟨⟨uk, um, ub⟩, uq⟩ => ?_
  refine WP.mono (fnExit_out tc tv tm tk (by decide) uk (tc.scr.of_keeps uk (by decide)) um ub)
    fun w ⟨hw, wm⟩ => ⟨hw, by rw [wm]; exact uq⟩

theorem mulA24Fn_ok {s : State} {base : Addr} {o a : Nat} (h : FnEntry s base 3 o a)
    (ab : Bounded s.mem base a) :
    WP isa mulA24Fn s fun t => FnOut base o s t ∧ F t.mem base o = Spec.X448.a24 * F s.mem base a := by
  have ha' : a + 112 ≤ 3584 := h.slotA
  refine WP.mono (fnBlock_ok (body := argPtr .esi 2 ++ a24Cols ++ normalize)
    (Q := fun m => F m base o = Spec.X448.a24 * F s.mem base a) h fun t tc tm _ => ?_) fun _ h => h
  obtain ea : fe t.mem base a = fe s.mem base a := tm.fe (Or.inl (by simp only [SAVE]; omega_arith)) (by omega_arith)
  obtain bt : Bounded t.mem base a := fun i hi => by
    rw [tm.limbs (Or.inl (by simp only [SAVE]; omega_arith)) (by omega_arith) hi]; exact ab i hi
  refine WP.mono (a24Body_ok tc bt) fun u ⟨up, uv⟩ => ⟨up, ?_⟩
  rw [uv, F, F, ea]

/-- The third argument after the entry. -/
theorem argB_keep {s t : State} {base : Addr} {o a b : Nat} (h : FnEntry s base 4 o a)
    (hvb : arg s 3 = BitVec.ofNat 32 b) (tk : Keeps [.eax, .edi] s t)
    (tm : Outside base SAVE 16 s.mem t.mem) : arg t 3 = BitVec.ofNat 32 b := by
  rw [(h.args.keep (tk.1 _ (by decide)) tk.2.1 tk.2.2 (tm.mono (by decide) (by decide))).2 3 (by decide), hvb]

/-- Operands below the own working space read the same after the entry. -/
theorem entry_operand {s t : State} {base : Addr} {a : Nat} (ha : Slot a)
    (tm : Outside base SAVE 16 s.mem t.mem) :
    fe t.mem base a = fe s.mem base a ∧ (Bounded s.mem base a → Bounded t.mem base a) := by
  have ha' : a + 112 ≤ 3584 := ha
  refine ⟨tm.fe (Or.inl (by simp only [SAVE]; omega_arith)) (by omega_arith), fun ab i hi => ?_⟩
  rw [tm.limbs (Or.inl (by simp only [SAVE]; omega_arith)) (by omega_arith) hi]; exact ab i hi

theorem addFn_ok {s : State} {base : Addr} {o a b : Nat} (h : FnEntry s base 4 o a)
    (hvb : arg s 3 = BitVec.ofNat 32 b) (hb : Slot b) (ab : Bounded s.mem base a)
    (bb : Bounded s.mem base b) :
    WP isa addFn s fun t => FnOut base o s t ∧ F t.mem base o = F s.mem base a + F s.mem base b := by
  rw [show addFn = .block (fnEntry ++ (argPtr .esi 2 ++ argPtr .ebp 3 ++ addCols ++ normalize) ++ fnExit)
    by simp only [addFn, List.append_assoc]]
  refine fnBlock_ok (Q := fun m => F m base o = F s.mem base a + F s.mem base b) h fun t tc tm tk => ?_
  obtain ⟨ea, ba⟩ := entry_operand h.slotA tm
  obtain ⟨eb, bb'⟩ := entry_operand hb tm
  exact WP.mono (addBody_ok tc (argB_keep h hvb tk tm) hb (ba ab) (bb' bb)) fun u ⟨up, uv⟩ =>
    ⟨up, by rw [uv, F, F, ea, eb]⟩

theorem subFn_ok {s : State} {base : Addr} {o a b : Nat} (h : FnEntry s base 4 o a)
    (hvb : arg s 3 = BitVec.ofNat 32 b) (hb : Slot b) (ab : Bounded s.mem base a)
    (bb : Bounded s.mem base b) :
    WP isa subFn s fun t => FnOut base o s t ∧ F t.mem base o = F s.mem base a - F s.mem base b := by
  rw [show subFn = .block (fnEntry ++ (argPtr .esi 2 ++ argPtr .ebp 3 ++ subCols ++ normalize) ++ fnExit)
    by simp only [subFn, List.append_assoc]]
  refine fnBlock_ok (Q := fun m => F m base o = F s.mem base a - F s.mem base b) h fun t tc tm tk => ?_
  obtain ⟨ea, ba⟩ := entry_operand h.slotA tm
  obtain ⟨eb, bb'⟩ := entry_operand hb tm
  exact WP.mono (subBody_ok tc (argB_keep h hvb tk tm) hb (ba ab) (bb' bb)) fun u ⟨up, uv⟩ =>
    ⟨up, by rw [uv, F, F, ea, eb]⟩

theorem mulFn_ok {s : State} {base : Addr} {o a b : Nat} (h : FnEntry s base 4 o a)
    (hvb : arg s 3 = BitVec.ofNat 32 b) (hb : Slot b) (ab : Bounded s.mem base a)
    (bb : Bounded s.mem base b) :
    WP isa mulFn s fun t => FnOut base o s t ∧ F t.mem base o = F s.mem base a * F s.mem base b := by
  rw [show mulFn = .block (fnEntry ++ ((argPtr .esi 2 ++ pack PA ++ argPtr .esi 3 ++ pack PB ++ mulWords ++
    argPtr .ebp 1 ++ unpack) ++ fnExit)) by simp only [mulFn, List.append_assoc], WP.block_append_iff]
  refine WP.mono (fnEntry_ok h) fun t ⟨tc, tv, tm, tk⟩ => ?_
  obtain ⟨ea, ba⟩ := entry_operand h.slotA tm
  obtain ⟨eb, bb'⟩ := entry_operand hb tm
  rw [WP.block_append_iff]
  refine WP.mono (mulBody_ok tc (argB_keep h hvb tk tm) hb (ba ab) (bb' bb)) fun w ⟨wm, wb, wv, wk⟩ => ?_
  refine WP.mono (fnExit_out tc tv tm tk (by decide) wk (tc.scr.of_keeps wk (by decide)) wm wb)
    fun x ⟨hx, xm⟩ => ⟨hx, ?_⟩
  rw [xm, wv, F, F, F, F, ea, eb]

end VG.Proof.X448.X86

end

end

/-! ### `X448.Field16Contract`, which this module and modules that import it used -/

section

/-!
# Curve448's field in radix `2^16`

Not trusted: the representation of elements of `GF(p)`,
`p = 2^448 - 2^224 - 1`, each twenty-eight 16-bit limbs, that the 32-bit
targets' code of X448 and Ed448 keeps them in, and on which their field
functions (`vg_gf448_r16_mul`, `_add`, `_sub` and `_mul_a24`) work.

An element is twenty-eight limbs, each a 32-bit little-endian word below
`2^16`, least significant first (`Limbs`): the element `Σ lᵢ 2^(16 i)`
(`valAt`), any number below `2^448` (so not necessarily below `p`). The
elements live in a working space `ws` of 8192 bytes (`[u64; 1024]`, the
working space of X448's and Ed448's functions), each at a byte offset: `o`
for the result, `a` and `b` for the operands. The offsets are arguments, so
that the result may be an operand and the caller keeps its elements where
it likes. Bytes 3584 to 4095 of `ws` are the function's own working space
(`ownAt`), and the elements lie below them (`Fits`). On return the
function's own bytes are unspecified and may hold intermediate values;
every other byte of `ws` keeps its value but the result's (`Keeps`).

The result's limbs are below `2^16` again, so that it can be the operand of
any of the functions.
-/

@[expose] public section

namespace VG.Proof.X448.Field16

open VG.Spec VG.Spec.X448

/-- The limbs of an element. -/
def limbs : Nat := 28

/-- The bytes of an element: a 32-bit word per limb. -/
def elemBytes : Nat := 4 * limbs

/-- Where the function's own working space starts; it ends at byte 4096. -/
def ownAt : Nat := 3584

/-- Limb `i` of the element at byte offset `o` of the working space `ws`. -/
def limbAt (m : Mem) (ws : Addr) (o : BitVec 32) (i : Nat) : Nat :=
  (m.readW (ws + BitVec.ofNat 64 (o.toNat + 4 * i)) 32).toNat

/-- The value of the first `n` limbs of the element at `o`: `Σ lᵢ 2^(16 i)`. -/
def valN (m : Mem) (ws : Addr) (o : BitVec 32) : Nat → Nat
  | 0 => 0
  | n + 1 => valN m ws o n + 2 ^ (16 * n) * limbAt m ws o n

/-- The value of the element at `o`. -/
def valAt (m : Mem) (ws : Addr) (o : BitVec 32) : Nat := valN m ws o limbs

/-- Every limb of the element at `o` is below `2^16`. -/
def Limbs (m : Mem) (ws : Addr) (o : BitVec 32) : Prop := ∀ i < limbs, limbAt m ws o i < 2 ^ 16

/-- The element at `o` lies below the function's own working space. -/
abbrev Fits (o : BitVec 32) : Prop := o.toNat + elemBytes ≤ ownAt

/-- Every byte of `ws` but those of the function's own working space and of
the result at `o` keeps its value. -/
def Keeps (ws : Addr) (o : BitVec 32) (m m' : Mem) : Prop :=
  ∀ i < 8192, (i < ownAt ∨ 4096 ≤ i) → (i < o.toNat ∨ o.toNat + elemBytes ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

end VG.Proof.X448.Field16

end

end

/-!
# X448 on x86 (32-bit): the field functions' contracts

The contracts the field functions are proven against (`binX86`, `a24X86`):
the facts of the shared contracts of `Proof/X448/X86/FnContract.lean` stated for x86
(`fnPre`: the working space, and the arguments on the stack), which the
shared contracts imply (`sig_implies`, in `FnVerified.lean`). The entry
those facts give (`FnEntry.of_pre`), and the shared postcondition from what
the proofs state (`FnOut.post`).
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

/-- The working space, the first argument. -/
abbrev wsOf (s : State) : Addr := (arg s 0).setWidth 64

/-- The shared contracts' facts about the state, for arguments of `len` bytes. -/
def fnPre (len : Nat) (s : State) : Prop :=
  (s.gpr .esp).toNat + 4 + len ≤ 2 ^ 32 ∧ s.rd = [⟨argAddr s 0, len⟩] ∧ s.wr = [⟨wsOf s, 8192⟩] ∧
    Region.Disjoint ⟨wsOf s, 8192⟩ ⟨argAddr s 0, len⟩ ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨wsOf s, 8192⟩ ∧ (arg s 0).toNat + 8192 ≤ 2 ^ 32

/-- The binary functions' contract, for the relation `r` of the values. -/
def binX86 (r : Nat → Nat → Nat → Prop) : Contract isa where
  pre s := fnPre 16 s ∧ Proof.X448.Field16.Fits (arg s 1) ∧ Proof.X448.Field16.Fits (arg s 2) ∧
    Proof.X448.Field16.Fits (arg s 3) ∧ Proof.X448.Field16.Limbs s.mem (wsOf s) (arg s 2) ∧
    Proof.X448.Field16.Limbs s.mem (wsOf s) (arg s 3)
  post s s' := Proof.X448.Field16.Limbs s'.mem (wsOf s) (arg s 1) ∧
    r (Proof.X448.Field16.valAt s'.mem (wsOf s) (arg s 1)) (Proof.X448.Field16.valAt s.mem (wsOf s) (arg s 2))
      (Proof.X448.Field16.valAt s.mem (wsOf s) (arg s 3)) ∧
    Proof.X448.Field16.Keeps (wsOf s) (arg s 1) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧
    arg s₁ 2 = arg s₂ 2 ∧ arg s₁ 3 = arg s₂ 3

/-- `vg_gf448_r16_mul_a24`'s contract. -/
def a24X86 : Contract isa where
  pre s := fnPre 12 s ∧ Proof.X448.Field16.Fits (arg s 1) ∧ Proof.X448.Field16.Fits (arg s 2) ∧
    Proof.X448.Field16.Limbs s.mem (wsOf s) (arg s 2)
  post s s' := Proof.X448.Field16.Limbs s'.mem (wsOf s) (arg s 1) ∧
    Proof.X448.Field16.valAt s'.mem (wsOf s) (arg s 1) % Spec.X448.P =
      39081 * Proof.X448.Field16.valAt s.mem (wsOf s) (arg s 2) % Spec.X448.P ∧
    Proof.X448.Field16.Keeps (wsOf s) (arg s 1) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧
    arg s₁ 2 = arg s₂ 2

theorem not_contains_ofs {base x : Addr} (h : ¬ (⟨base, 8192⟩ : Region).Contains x 1) :
    8192 ≤ ofs base x := by
  simp only [Region.Contains] at h; simp only [ofs]; omega_using [h]

/-- The entry the facts of the contract give. -/
theorem FnEntry.of_pre {s : State} {n : Nat} (hn : 3 ≤ n) (h : fnPre (4 * n) s)
    (ho : Proof.X448.Field16.Fits (arg s 1)) (ha : Proof.X448.Field16.Fits (arg s 2)) :
    FnEntry s (wsOf s) n (arg s 1).toNat (arg s 2).toNat := by
  obtain ⟨hsp, hrd, hwr, hdis, hret, hfit⟩ := h
  have cont : ∀ i < n, (⟨argAddr s 0, 4 * n⟩ : Region).Contains (argAddr s i) 4 := fun i hi =>
    VG.Proof.X25519.X86.sub_contains (x := s.gpr .esp) (a := 4) (k := 4 * n) (by omega_using [hsp]) (by omega_using [])
      (by omega_using [hi]) (by decide)
  refine ⟨rfl, by rw [hwr]; exact List.mem_singleton_self _, hfit, ⟨fun i hi => ?_, fun i hi k hk => ?_⟩, hn,
    fun k hk => ?_, by simp, by simp,
    ho, ha⟩
  · exact ⟨_, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _), cont i hi⟩
  · refine not_contains_ofs fun hw => hdis _ hw ((cont i hi).byte ?_)
    rw [Offset.add_sub_cancel_left]; simp only [BitVec.toNat_ofNat]; omega_using [hk]
  · refine not_contains_ofs fun hw => hret _ ?_ hw
    simp only [Region.Contains]
    rw [Offset.add_sub_cancel_left]; simp only [BitVec.toNat_ofNat]; omega_using [hk]

/-- The value of an element, as `Spec` states it. -/
theorem valN_spec (m : Mem) (ws : Addr) (o : BitVec 32) :
    ∀ n, Proof.X448.Field16.valN m ws o n = valN (limbs m ws o.toNat) n
  | 0 => rfl
  | n + 1 => by
    rw [Proof.X448.Field16.valN, valN, valN_spec m ws o n, radix, ← Nat.pow_mul]
    rfl

theorem valAt_eq (m : Mem) (ws : Addr) (o : BitVec 32) :
    Proof.X448.Field16.valAt m ws o = fe m ws o.toNat := valN_spec m ws o 28

theorem limbs_spec {m : Mem} {ws : Addr} {o : BitVec 32} :
    Proof.X448.Field16.Limbs m ws o ↔ Bounded m ws o.toNat := Iff.rfl

/-- `Keeps` from the frame of the field functions. -/
theorem FieldMem.keeps {base : Addr} {o : BitVec 32} {m m' : Mem} (h : FieldMem base o.toNat m m') :
    Proof.X448.Field16.Keeps base o m m' := by
  intro i hi hw ho
  simp only [Proof.X448.Field16.ownAt, Proof.X448.Field16.elemBytes, Proof.X448.Field16.limbs] at hw ho
  exact h _ (by rw [ofs, Mem.sub_ofNat_toNat base (by omega_using [hi])]; omega_using [ho])
    (by rw [ofs, Mem.sub_ofNat_toNat base (by omega_using [hi])]; simp only [ACC]; omega_using [hw])

end VG.Proof.X448.X86
