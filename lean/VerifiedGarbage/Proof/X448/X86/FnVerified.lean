module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.X448.X86.FnLit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86.Call
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.X448.X86.FnLit
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.X25519.X86.Arith
public import VerifiedGarbage.Proof.X25519.X86.Column
import Batteries.Logic
import VerifiedGarbage.Proof.X448.X86.Step
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
public import VerifiedGarbage.Proof.X448.X86.Field
meta import VerifiedGarbage.Proof.X25519.X86.Arith
meta import VerifiedGarbage.Proof.X25519.X86.Column
meta import Batteries.Logic
meta import VerifiedGarbage.Proof.X448.X86.Step
meta import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Spec.X448
meta import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.X448.X86.Mem
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.X448.X86.Instr
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.X448.X86.Columns
meta import VerifiedGarbage.Proof.X448.X86.Small
meta import VerifiedGarbage.Proof.Framework.X86.Spill
meta import VerifiedGarbage.Proof.X448.X86.Field

/-! ### `X448.X86.FnContract`, which this module and modules that import it used -/

section

/-! ### `X448.X86.RowMem`, which this module and modules that import it used -/

section

/-!
# X448 on x86 (32-bit): multiplication-row memory, for Ed448's scalars

The public row pointer moves through the working space while all field inputs
remain unchanged.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

/-- The offset of twenty-eight words, of a scalar's limbs, below the field functions' own working space. -/
abbrev Slot16 (o : Nat) : Prop := o + 112 ≤ ACC

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
  val : valN (accw s.mem base) (i + 28) = valN (limbs s0.mem base a) i * fe16 s0.mem base b

theorem rowSrcWith_ok {s : State} {base : Addr} (hs : Scr s base) {mb : Nat → MemOp} {b i j : Nat}
    (hb : Slot16 b) (hi : i < 28) (hj : j < 28)
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

theorem rowWith_ok {base : Addr} {a b : Nat} (ha : Slot16 a) (hb : Slot16 b) {s0 s : State}
    {ldA : List Instr} {mb : Nat → MemOp}
    (ab : Bounded s0.mem base a) (bb : Bounded s0.mem base b) {i : Nat} (hi : i < 28)
    (hc : RowCode base a b s0 i ldA mb) (h : RowInv base a b s0 i s) :
    WP isa (.block (rowWith ldA mb)) s fun t =>
      RowInv base a b s0 (i + 1) t ∧ t.zf = some (decide (i + 1 = 28)) := by
  have ha' : a + 112 ≤ 3584 := ha
  have hb' : b + 112 ≤ 3584 := hb
  have input : ∀ o, Slot16 o → ∀ j < 28, limbs s.mem base o j = limbs s0.mem base o j := by
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
theorem rowCode_sc (base : Addr) {a b : Nat} (ha : Slot16 a) (hb : Slot16 b) (s0 : State) {i : Nat}
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

The arithmetic of `vg_gf448_r32_mul`'s product and `vg_gf448_r32_sqr`'s
square (`Impl/X448/X86.lean`): the columns of a product of two numbers of
`n` words (`conv_identity`) and of a square (`sqr_identity`), and the fold of
their 28 words by `2^448 = 2^224 + 1`.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.Proof.X448.Radix16
open VG.Proof.X25519.X86 (num num_succ num_congr num_add num_mul num_lt)

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

/-! ## The columns of a square -/

/-- A number whose words but word `m` are zero. -/
theorem num_delta (c m : Nat) {N : Nat} (h : m < N) :
    num (fun j => if j = m then c else 0) N = (2 ^ 32) ^ m * c := by
  obtain ⟨d, rfl⟩ : ∃ d, N = m + (d + 1) := ⟨N - m - 1, by omega_arith⟩
  rw [num_congr (g := fun k => if m ≤ k then (if k - m = 0 then c else 0) else 0) (fun k _ => ?_),
    num_shift (fun i => if i = 0 then c else 0), num_first (fun k _ hk => ite_eq_right hk),
    ite_eq_left rfl]
  by_cases h1 : k = m
  · rw [ite_eq_left h1, ite_eq_left (by omega_arith), ite_eq_left (by omega_arith)]
  · rw [ite_eq_right h1]
    by_cases h2 : m ≤ k
    · rw [ite_eq_left h2, ite_eq_right (by omega_arith)]
    · rw [ite_eq_right h2]

/-- The words of a number of `n` words from word `m` on. -/
def tailN (fa : Nat → Nat) (n m : Nat) : Nat := num (fun j => if m ≤ j then fa j else 0) n

theorem tailN_zero (fa : Nat → Nat) (n : Nat) : tailN fa n 0 = num fa n :=
  num_congr fun j _ => ite_eq_left (Nat.zero_le j)

theorem tailN_succ (fa : Nat → Nat) {n m : Nat} (h : m < n) :
    tailN fa n m = (2 ^ 32) ^ m * fa m + tailN fa n (m + 1) := by
  rw [← num_delta (fa m) m h, tailN, tailN, ← num_add]
  refine num_congr fun j _ => ?_
  by_cases h1 : j = m
  · rw [ite_eq_left h1, ite_eq_left (by omega_arith), ite_eq_right (by omega_arith), h1, Nat.add_zero]
  · rw [ite_eq_right h1, Nat.zero_add]
    by_cases h2 : m ≤ j
    · rw [ite_eq_left h2, ite_eq_left (by omega_arith)]
    · rw [ite_eq_right h2, ite_eq_right (by omega_arith)]

/-- Row `m` of a square: `a_m` times twice the words above it, and its square. -/
theorem sqr_row (fa : Nat → Nat) {n m N : Nat} (hm : m < n) (hN : m + n ≤ N) :
    num (fun k => if m ≤ k then (if m < k - m ∧ k - m < n then 2 * (fa m * fa (k - m)) else 0) +
        (if k - m = m then fa m * fa m else 0) else 0) N =
      (2 ^ 32) ^ m * (fa m * ((2 ^ 32) ^ m * fa m + 2 * tailN fa n (m + 1))) := by
  obtain ⟨d, rfl⟩ : ∃ d, N = m + (n + d) := ⟨N - m - n, by omega_arith⟩
  rw [num_shift (fun j => (if m < j ∧ j < n then 2 * (fa m * fa j) else 0) + (if j = m then fa m * fa m else 0)),
    num_add, num_delta _ _ (by omega_arith),
    num_congr (g := fun j => if j < n then (2 * fa m) * (if m + 1 ≤ j then fa j else 0) else 0) (fun j _ => ?_),
    num_trunc, num_mul]
  · rw [tailN, Nat.mul_add (fa m), Nat.mul_left_comm (fa m) ((2 ^ 32) ^ m), Nat.mul_left_comm (fa m) 2,
      Nat.mul_assoc 2, Nat.add_comm]
  · by_cases h1 : j < n
    · rw [ite_eq_left h1]
      by_cases h2 : m < j
      · rw [ite_eq_left ⟨h2, h1⟩, ite_eq_left (Nat.succ_le_of_lt h2), Nat.mul_assoc]
      · rw [ite_eq_right (fun h => h2 h.1), ite_eq_right (by omega_arith), Nat.mul_zero]
    · rw [ite_eq_right h1, ite_eq_right (fun h => h1 h.2)]

/-- The columns of the first `m` rows of a square, and the words from `m` on squared. -/
theorem sqr_rows (n : Nat) (fa : Nat → Nat) (N : Nat) (hN : 2 * n ≤ N) : ∀ m, m ≤ n →
    num (fun k => (((List.range m).filter fun i => 2 * i < k && k - i < n).map
        fun i => 2 * (fa i * fa (k - i))).sum +
        if k % 2 = 0 ∧ k / 2 < m then fa (k / 2) * fa (k / 2) else 0) N + tailN fa n m * tailN fa n m =
      num fa n * num fa n
  | 0, _ => by
    rw [num_congr (g := fun _ => 0) (fun k _ => by
      rw [ite_eq_right (fun h => Nat.not_lt_zero _ h.2)]; rfl), num_zero, Nat.zero_add, tailN_zero]
  | m + 1, h => by
    have e : ∀ k < N, (((List.range (m + 1)).filter fun i => 2 * i < k && k - i < n).map
          fun i => 2 * (fa i * fa (k - i))).sum +
          (if k % 2 = 0 ∧ k / 2 < m + 1 then fa (k / 2) * fa (k / 2) else 0) =
        ((((List.range m).filter fun i => 2 * i < k && k - i < n).map fun i => 2 * (fa i * fa (k - i))).sum +
          if k % 2 = 0 ∧ k / 2 < m then fa (k / 2) * fa (k / 2) else 0) +
          (if m ≤ k then (if m < k - m ∧ k - m < n then 2 * (fa m * fa (k - m)) else 0) +
            (if k - m = m then fa m * fa m else 0) else 0) := by
      intro k _
      have hf : (List.filter (fun i => decide (2 * i < k) && decide (k - i < n)) [m]) =
          if 2 * m < k ∧ k - m < n then [m] else [] := by
        simp only [List.filter_cons, List.filter_nil, Bool.and_eq_true, decide_eq_true_eq]
      rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, hf]
      by_cases hA : k = 2 * m
      · subst hA
        rw [ite_eq_right (by omega_arith), ite_eq_left (by omega_arith), ite_eq_right (by omega_arith),
          ite_eq_left (by omega_arith), ite_eq_right (by omega_arith), ite_eq_left (by omega_arith),
          show 2 * m / 2 = m by omega_arith]
        simp only [List.map_nil, List.sum_nil, Nat.add_zero, Nat.zero_add]
      · by_cases hB : 2 * m < k ∧ k - m < n
        · rw [ite_eq_left hB, ite_eq_right (by omega_arith), ite_eq_right (by omega_arith),
            ite_eq_left (by omega_arith), ite_eq_left (by omega_arith), ite_eq_right (by omega_arith)]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
        · rw [ite_eq_right hB]
          by_cases hC : k % 2 = 0 ∧ k / 2 < m
          · rw [ite_eq_left hC, ite_eq_left (by omega_arith)]
            by_cases hD : m ≤ k
            · rw [ite_eq_left hD, ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]
              simp only [List.map_nil, List.sum_nil, Nat.add_zero]
            · rw [ite_eq_right hD]
              simp only [List.map_nil, List.sum_nil, Nat.add_zero]
          · rw [ite_eq_right hC, ite_eq_right (by omega_arith)]
            by_cases hD : m ≤ k
            · rw [ite_eq_left hD, ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]
              simp only [List.map_nil, List.sum_nil, Nat.add_zero]
            · rw [ite_eq_right hD]
              simp only [List.map_nil, List.sum_nil, Nat.add_zero]
    rw [num_congr e, num_add, sqr_row fa (by omega_arith) (by omega_arith),
      ← sqr_rows n fa N hN m (by omega_arith), tailN_succ fa (m := m) (by omega_arith),
      ← Nat.mul_assoc ((2 ^ 32) ^ m) (fa m)]
    generalize num (fun k => (((List.range m).filter fun i => 2 * i < k && k - i < n).map
        fun i => 2 * (fa i * fa (k - i))).sum +
        if k % 2 = 0 ∧ k / 2 < m then fa (k / 2) * fa (k / 2) else 0) N = r
    generalize (2 ^ 32) ^ m * fa m = x
    generalize tailN fa n (m + 1) = t
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_comm t x, Nat.mul_left_comm x 2 t]
    omega_arith

/-- The columns of `a²`, for a number of `n` words: the products of distinct
words doubled, and the squares. -/
theorem sqr_identity (n : Nat) (fa : Nat → Nat) :
    num (fun k => (((List.range n).filter fun i => 2 * i < k && k - i < n).map
        fun i => 2 * (fa i * fa (k - i))).sum +
        if k % 2 = 0 ∧ k / 2 < n then fa (k / 2) * fa (k / 2) else 0) (2 * n) = num fa n * num fa n := by
  have h := sqr_rows n fa (2 * n) (Nat.le_refl _) n (Nat.le_refl _)
  have z : tailN fa n n = 0 := by
    rw [tailN, num_congr (g := fun _ => 0) (fun j hj => ite_eq_right (by omega_arith)), num_zero]
  rwa [z, Nat.mul_zero, Nat.add_zero] at h

/-! ## The fold by the prime -/

/-- The product's 28 words `A0 + A1 φ + A2 φ² + A3 φ³`, as `reduce` folds them. -/
theorem reduce_val (p : Nat → Nat) :
    (num p 14 + num (fun i => p (14 + i)) 14 + (half + 1) * num (fun i => p (21 + i)) 7 +
      half * num (fun i => p (14 + i)) 7) % Spec.X448.P = num p 28 % Spec.X448.P := by
  have hp : Spec.X448.P = full - half - 1 := by decide +kernel
  have h1 : num (fun i => p (14 + i)) 14 = num (fun i => p (14 + i)) 7 + half * num (fun i => p (21 + i)) 7 := by
    rw [show 14 = 7 + 7 from rfl, num_split, pow7]
    simp only [← Nat.add_assoc, Nat.reduceAdd]
  have he : num p 28 = num p 14 + num (fun i => p (14 + i)) 14 + (half + 1) * num (fun i => p (21 + i)) 7 +
      half * num (fun i => p (14 + i)) 7 +
      Spec.X448.P * (num (fun i => p (14 + i)) 7 + (half + 1) * num (fun i => p (21 + i)) 7) := by
    rw [show 28 = 14 + 14 from rfl, num_split, pow14, h1]
    simp only [hp, full, half, radix, Nat.reducePow]
    omega_arith
  rw [he, Nat.add_mul_mod_self_left]

/-- The fourteen operands of `reduce`'s second chain. -/
theorem wrap_val (q : Nat → Nat) : num (fun k => q (k % 7)) 14 = (half + 1) * num q 7 := by
  rw [show (14 : Nat) = 7 + 7 from rfl, num_split, pow7,
    num_congr (f := fun k => q (k % 7)) (g := q) (fun k hk => by rw [Nat.mod_eq_of_lt hk]),
    num_congr (f := fun i => q ((7 + i) % 7)) (g := q) (fun k hk => by
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt hk]), Nat.add_mul, Nat.one_mul, Nat.add_comm]

end VG.Proof.X448.X86

end

end


/-!
# X448 on x86 (32-bit): the products of `vg_gf448_r32_mul` and `vg_gf448_r32_sqr`

The operands copied (`operand_ok`), 28 columns of X25519's (`PROD`), and their
words reduced by the prime into the result (`reduce_ok`, `prodWords_ok`):
a product or a square.
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

/-! ## The operands -/

/-- The element at `esi = ws + a` copied to the fourteen words at `o`. -/
theorem operand_ok {s : State} {base : Addr} (hs : Scr s base) {a o : Nat} (ha : Slot a) (hoa : ACC ≤ o)
    (ho : o + 56 ≤ 8192) (hp : s.gpr .esi = s.gpr .edi + BitVec.ofNat 32 a) :
    WP isa (.block (operand o)) s fun t =>
      fe t.mem base o = fe s.mem base a ∧ Outside base o 56 s.mem t.mem ∧ Keeps [.eax] s t := by
  have ha' : a + 56 ≤ 3584 := ha
  have hoa' : 3584 ≤ o := hoa
  let inv := fun n (t : State) =>
    (∀ k < n, limbs t.mem base o k = limbs s.mem base a k) ∧ Outside base o 56 s.mem t.mem ∧ Keeps [.eax] s t
  have step : ∀ n t, n < 14 → inv n t →
      WP isa (.block [.mov .eax (.mem (wordAt .esi n)), st .eax (o + 4 * n)]) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    have ts := hs.of_keeps tk (by decide)
    refine wp_load (a := off base (a + 4 * n)) (ptr_ea hs hp tk (by decide) (by decide) (by omega_arith))
      (ts.read (by omega_arith)) fun u uu => ?_
    refine store_ok (ts.of_upd uu (by decide)) (by omega_arith) fun v uv => WP.block_nil ⟨?_, ?_, ?_⟩
    · intro k hk
      show (word v.mem base (o + 4 * k)).toNat = _
      rw [uv.mem, uu.mem, uu.gpr, word_write t.mem base (by omega_arith) (by omega_arith)]
      by_cases h : k = n
      · rw [ite_eq_left h, h]
        show limbs t.mem base a n = _
        exact tm.limbs (k := 14) (Or.inl (by omega_arith)) (by omega_arith) hn
      · rw [ite_eq_right h]; exact tf k (by omega_arith)
    · rw [uv.mem, uu.mem]
      exact tm.trans ((writeW_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
    · exact tk.trans ((uu.rest (by decide)).trans (uv.rest _))
  exact WP.mono (wp_range_flatMap (M := isa) (N := 14) inv step 14 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩) fun t ⟨tf, tm, tk⟩ => ⟨num_congr tf, tm, tk⟩

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

/-- The product's words at `PROD` reduced into the element at `ebp`. -/
theorem reduce_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : Slot o)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 o) :
    WP isa (.block Impl.X448.X86.reduce) s fun t =>
      fe t.mem base o % Spec.X448.P = num (limbs s.mem base PROD) 28 % Spec.X448.P ∧
      Outside base o 56 s.mem t.mem ∧ Keeps [.eax, .ecx] s t := by
  have ho' : o + 56 ≤ 3584 := ho
  have hP : PROD = 3696 := rfl
  have pq : ∀ {m : Mem} {n : Nat}, n ≤ 14 → Outside base o (4 * n) s.mem m → ∀ j < 28,
      word m base (PROD + 4 * j) = word s.mem base (PROD + 4 * j) := fun hn hm j hj =>
    hm.word (Or.inr (by omega_arith)) (by omega_arith)
  unfold Impl.X448.X86.reduce
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (clearCarry_ok s) fun t₀ ⟨f₀, e₀, m₀, k₀⟩ => ?_
  have k₀ : Keeps [.eax, .ecx] s t₀ := k₀.mono (by decide)
  have hs₀ := hs.of_keeps k₀ (by decide)
  have p₀ : t₀.gpr .ebp = t₀.gpr .edi + BitVec.ofNat 32 o := by
    rw [k₀.1 _ (by decide), k₀.1 _ (by decide)]; exact hp
  rw [WP.block_append_iff]
  refine WP.mono (chain_ok (.inl rfl) hs₀ (yo := o) (xo := PROD) (v := fun k => word s.mem base (PROD + 4 * (14 + k)))
    f₀ 14 (by omega_arith) (by decide) (by unfold Apart; omega_arith) (fun k hk t tk =>
      ⟨(hs₀.of_keeps tk (by decide)).ea (by omega_arith), ptr_ea hs₀ p₀ tk (by decide) (by decide) (by omega_arith)⟩)
    (fun k hk t tk tm => ?_)) fun t₁ ⟨k₁, m₁, c₁, f₁, r₁⟩ => ?_
  · have ts := hs₀.of_keeps tk (by decide)
    rw [pw, readMem (ts.ea (d := PROD + 4 * (14 + k)) (by omega_arith)) (ts.read (by omega_arith))]
    rw [m₀] at tm
    exact congrArg some (pq (by omega_arith) tm _ (by omega_arith))
  rw [m₀] at r₁ m₁
  rw [WP.block_append_iff]
  refine WP.mono (carryUp_ok (n := 0) f₁ ((k₁.1 _ (by decide)).trans e₀) (by decide)) fun t₂ ⟨f₂, e₂, m₂, k₂⟩ => ?_
  have k₂ : Keeps [.eax, .ecx] s t₂ := k₀.trans ((k₁.mono (by decide)).trans (k₂.mono (by decide)))
  have hs₂ := hs.of_keeps k₂ (by decide)
  have p₂ : t₂.gpr .ebp = t₂.gpr .edi + BitVec.ofNat 32 o := by
    rw [k₂.1 _ (by decide), k₂.1 _ (by decide)]; exact hp
  rw [WP.block_append_iff]
  refine WP.mono (chain_ok (.inl rfl) hs₂ (yo := o) (xo := o)
    (v := fun k => word s.mem base (PROD + 4 * (21 + k % 7))) f₂ 14 (by omega_arith) (by omega_arith) (.inl rfl)
    (fun k hk t tk => ?_) (fun k hk t tk tm => ?_)) fun t₃ ⟨k₃, m₃, c₂, f₃, r₃⟩ => ?_
  · have := ptr_ea hs₂ (k := k) p₂ tk (by decide) (by decide) (by omega_arith)
    exact ⟨this, this⟩
  · have ts := hs₂.of_keeps tk (by decide)
    rw [pw, readMem (ts.ea (d := PROD + 4 * (21 + k % 7)) (by omega_arith)) (ts.read (by omega_arith))]
    rw [m₂] at tm
    exact congrArg some (pq (n := 14) (by decide) (m₁.trans (tm.mono (by omega_arith) (by omega_arith))) _ (by omega_arith))
  rw [m₂] at r₃ m₃
  have m₁₃ := m₁.trans m₃
  rw [WP.block_append_iff]
  refine WP.mono (carryUp_ok (n := c₁.toNat) f₃ ((k₃.1 _ (by decide)).trans (by rw [e₂, Nat.zero_add]))
    (by cases c₁ <;> decide)) fun t₄ ⟨f₄, e₄, m₄, k₄⟩ => ?_
  have k₄ : Keeps [.eax, .ecx] s t₄ := k₂.trans ((k₃.mono (by decide)).trans (k₄.mono (by decide)))
  have hs₄ := hs.of_keeps k₄ (by decide)
  have p₄ : t₄.gpr .ebp = t₄.gpr .edi + BitVec.ofNat 32 o := by
    rw [k₄.1 _ (by decide), k₄.1 _ (by decide)]; exact hp
  rw [WP.block_append_iff]
  refine WP.mono (chain_ok (.inl rfl) hs₄ (yo := o + 28) (xo := o + 28)
    (v := fun k => word s.mem base (PROD + 4 * (14 + k))) f₄ 7 (by omega_arith) (by omega_arith) (.inl rfl)
    (fun k hk t tk => ?_) (fun k hk t tk tm => ?_)) fun t₅ ⟨k₅, m₅, c₃, f₅, r₅⟩ => ?_
  · have := ptr_ea hs₄ (k := 7 + k) p₄ tk (by decide) (by decide) (by omega_arith)
    rw [show o + 4 * (7 + k) = o + 28 + 4 * k by omega_arith] at this
    exact ⟨this, this⟩
  · have ts := hs₄.of_keeps tk (by decide)
    rw [pw, readMem (ts.ea (d := PROD + 4 * (14 + k)) (by omega_arith)) (ts.read (by omega_arith))]
    rw [m₄] at tm
    exact congrArg some (pq (n := 14) (by decide) (m₁₃.trans (tm.mono (by omega_arith) (by omega_arith))) _ (by omega_arith))
  rw [m₄] at r₅ m₅
  rw [WP.block_append_iff]
  refine WP.mono (carryUp_ok (n := c₁.toNat + c₂.toNat) f₅ ((k₅.1 _ (by decide)).trans e₄)
    (by cases c₁ <;> cases c₂ <;> decide)) fun t₆ ⟨f₆, e₆, m₆, k₆⟩ => ?_
  have k₆ : Keeps [.eax, .ecx] s t₆ := k₄.trans ((k₅.mono (by decide)).trans (k₆.mono (by decide)))
  have hs₆ := hs.of_keeps k₆ (by decide)
  have b : c₁.toNat + c₂.toNat + c₃.toNat ≤ 3 := by cases c₁ <;> cases c₂ <;> cases c₃ <;> decide
  refine WP.mono (foldChain_ok (.inl rfl) hs₆ ho (by rw [k₆.1 _ (by decide), k₆.1 _ (by decide)]; exact hp) f₆ e₆
    (Nat.lt_of_le_of_lt b (by decide))) fun t₇ ⟨r₇, m₇, k₇⟩ => ⟨?_, ?_, k₆.trans k₇⟩
  · rw [folded_add r₇ (fe_lt _ _ _) (Nat.lt_of_le_of_lt b (by decide)), ← reduce_val, m₆]
    have e13 : num (fun k => (word s.mem base (PROD + 4 * (14 + k))).toNat) 7 =
        num (fun i => limbs s.mem base PROD (14 + i)) 7 := rfl
    have e2 : num (fun k => (word s.mem base (PROD + 4 * (21 + k % 7))).toNat) 14 =
        (half + 1) * num (fun i => limbs s.mem base PROD (21 + i)) 7 :=
      wrap_val fun i => limbs s.mem base PROD (21 + i)
    have e1 : num (fun k => (word s.mem base (PROD + 4 * (14 + k))).toNat) 14 =
        num (fun i => limbs s.mem base PROD (14 + i)) 14 := rfl
    have sp : ∀ m, fe m base o = num (limbs m base o) 7 + half * num (limbs m base (o + 28)) 7 := fun m => by
      rw [← pow7]
      exact (num_split _ 7 7).trans <| congrArg (num (limbs m base o) 7 + (2 ^ 32) ^ 7 * ·) (num_congr fun k _ => by
        show (word m base (o + 4 * (7 + k))).toNat = (word m base (o + 28 + 4 * k)).toNat
        rw [show o + 4 * (7 + k) = o + 28 + 4 * k by omega_arith])
    have lo : num (limbs t₅.mem base o) 7 = num (limbs t₃.mem base o) 7 := num_congr fun k hk => by
      show (word t₅.mem base (o + 4 * k)).toNat = _
      rw [m₅.word (Or.inl (by omega_arith)) (by omega_arith)]
    rw [Proof.X25519.X86.PassRel, ite_eq_left rfl, pow14, show false.toNat = 0 from rfl, Nat.add_zero, e1] at r₁
    rw [Proof.X25519.X86.PassRel, ite_eq_left rfl, pow14, show false.toNat = 0 from rfl, Nat.add_zero, e2] at r₃
    rw [Proof.X25519.X86.PassRel, ite_eq_left rfl, pow7, show false.toNat = 0 from rfl, Nat.add_zero, e13] at r₅
    have r₅ := congrArg (half * ·) r₅
    have s₃ : num (limbs t₃.mem base o) 14 = _ := sp t₃.mem
    have s₅ := sp t₅.mem
    simp only [Nat.mul_add] at r₅
    rw [← Nat.mul_assoc, show half * half = full from by decide +kernel] at r₅
    rw [lo] at s₅
    rw [Nat.mul_add, Nat.mul_add]
    refine congrArg (· % Spec.X448.P) ?_
    omega_using [r₁, r₃, r₅, s₃, s₅]
  · rw [m₆] at m₇
    exact m₁₃.trans ((m₅.mono (by omega_arith) (by omega_arith)).trans m₇)

/-- The 28 columns `ts`, of value `V`, reduced modulo the prime into the element at `o`. -/
theorem prodWords_ok {s : State} {base : Addr} {n o a : Nat} (hc : FnCtx s base n o a)
    {ts : Nat → List Impl.X25519.X86.Term}
    {V : Nat} (hr : ∀ k < 28, ∀ t ∈ ts k, ∀ d ∈ treads t, d + 4 ≤ PROD)
    (hb : ∀ k < 28, colv s.mem (s.gpr .edi) (ts k) < 2 ^ 68)
    (hV : num (fun k => colv s.mem (s.gpr .edi) (ts k)) 28 = V) (hlt : V < (2 ^ 32) ^ 28) :
    WP isa (.block (prodWords ts)) s fun t =>
      fe t.mem base o % Spec.X448.P = V % Spec.X448.P ∧ FieldMem base o s.mem t.mem WORK ∧ Keeps clob s t := by
  have hs := hc.scr
  have hx := hs.ctx
  unfold prodWords
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono Proof.X25519.X86.zeroAcc_ok fun s₁ ⟨k₁, m₁, a₁⟩ => ?_)
  have c₁ := k₁.ctx hx
  refine WP.block_append (WP.mono (cols_ok c₁ ts 28 (by decide) (fun k hk t ht d hd => ?_)
    (fun k hk => by rw [m₁]; exact hb k hk) (by rw [a₁]; decide)) fun s₂ ⟨k₂, f₂, e₂, _⟩ => ?_)
  · have := hr k hk t ht d hd
    simp only [PROD, ACC] at this ⊢
    exact ⟨by omega_using [this], .inl this⟩
  rw [a₁, Nat.zero_add, m₁, hV] at e₂
  rw [m₁] at f₂
  have z₂ : acc s₂ = 0 := by
    rcases Nat.eq_zero_or_pos (acc s₂) with h | h
    · exact h
    · have := Nat.mul_le_mul_left ((2 ^ 32) ^ 28) h
      omega_using [this, e₂, hlt]
  rw [z₂, Nat.mul_zero, Nat.add_zero] at e₂
  have k₁₂ : Keeps clob s s₂ := keeps_of_keep (k₁.trans k₂)
  have o₂ := outside_of_frame hs (by decide) (by decide) f₂
  have hc₂ := hc.keep k₁₂ (by decide) (by decide) (o₂.mono (by decide) (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (argPtr_ok hc₂.args (by have := hc.n3; omega_arith) (by decide) hc₂.argO) fun s₃ ⟨p₃, m₃, k₃⟩ => ?_
  refine WP.mono (reduce_ok (hc₂.scr.of_keeps k₃ (by decide)) hc.slotO p₃) fun s₄ ⟨v₄, m₄, k₄⟩ =>
    ⟨?_, ?_, k₁₂.trans ((k₃.mono (by decide)).trans (k₄.mono (by decide)))⟩
  · rw [v₄, m₃, ← e₂]
    exact congrArg (· % Spec.X448.P) (num_congr fun k hk => by
      rw [wv, wd_word hs _ (by simp only [PROD, ACC]; omega_arith)])
  · rw [m₃] at m₄
    exact (FieldMem.work o₂ (by decide) (by decide)).trans (FieldMem.output m₄)

/-- The words at `PA` as the columns' proofs read them. -/
theorem num_wv {s : State} {base : Addr} (hs : Scr s base) (m : Mem) {o : Nat} (ho : o + 56 ≤ 8192) :
    num (fun k => wv m (s.gpr .edi) (o + 4 * k)) 14 = num (fun k => (word m base (o + 4 * k)).toNat) 14 :=
  num_congr fun k hk => by rw [wv, wd_word hs _ (by omega_arith)]

/-- The words at `PA` and `PB` multiplied, modulo the prime, into the element at `o`. -/
theorem mulWords_ok {s : State} {base : Addr} {n o a : Nat} (hc : FnCtx s base n o a) :
    WP isa (.block (prodWords prodTerms)) s fun t =>
      fe t.mem base o % Spec.X448.P = fe s.mem base PA * fe s.mem base PB % Spec.X448.P ∧
      FieldMem base o s.mem t.mem WORK ∧ Keeps clob s t := by
  rw [fe, fe, ← num_wv hc.scr _ (by decide), ← num_wv hc.scr _ (by decide)]
  have hA := num_lt (f := fun i => wv s.mem (s.gpr .edi) (PA + 4 * i)) (n := 14) fun _ _ => wv_lt _ _ _
  have hB := num_lt (f := fun j => wv s.mem (s.gpr .edi) (PB + 4 * j)) (n := 14) fun _ _ => wv_lt _ _ _
  refine prodWords_ok hc (fun k _ => prodTerms_reads) (fun k _ => prodTerms_lt _ _ _) ?_ ?_
  · rw [← conv_identity 14]
    exact num_congr fun k _ => prodTerms_colv _ _ _
  · have := Nat.mul_lt_mul_of_lt_of_lt hA hB
    rwa [← Nat.pow_add] at this

theorem sqrTerms_reads {k : Nat} : ∀ t ∈ sqrTerms k, ∀ d ∈ treads t, d + 4 ≤ PROD := by
  intro t ht d hd
  simp only [sqrTerms, List.mem_append, List.mem_map, List.mem_filter, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at ht
  rcases ht with ⟨i, ⟨hi, -, hki⟩, rfl⟩ | ht
  · simp only [treads, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> simp only [PA, PROD, ACC] <;> omega_arith
  · split at ht
    · rename_i hk2
      simp only [List.mem_singleton] at ht
      subst ht
      simp only [treads, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl <;> simp only [PA, PROD, ACC] <;> omega_arith
    · exact absurd ht List.not_mem_nil

theorem sqrTerms_colv (m : Mem) (x : BitVec 32) (k : Nat) :
    colv m x (sqrTerms k) =
      (((List.range 14).filter fun i => 2 * i < k && k - i < 14).map fun i =>
        2 * (wv m x (PA + 4 * i) * wv m x (PA + 4 * (k - i)))).sum +
      if k % 2 = 0 ∧ k / 2 < 14 then wv m x (PA + 4 * (k / 2)) * wv m x (PA + 4 * (k / 2)) else 0 := by
  unfold colv sqrTerms
  rw [List.map_append, List.sum_append, List.map_map]
  split <;> rfl

theorem sqrTerms_lt (m : Mem) (x : BitVec 32) {k : Nat} (hk : k < 28) : colv m x (sqrTerms k) < 2 ^ 68 := by
  have hl := (by decide : ∀ k < 28,
    ((List.range 14).filter fun i => 2 * i < k && k - i < 14).length ≤ 7) k hk
  have hl' : (sqrTerms k).length ≤ 8 := by
    simp only [sqrTerms, List.length_append, List.length_map]
    split <;> simp only [List.length_cons, List.length_nil] <;> omega_using [hl]
  have hw : ∀ a b, wv m x a * wv m x b ≤ 2 ^ 64 - 2 ^ 33 + 1 := fun a b =>
    Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt (wv_lt m x a)) (Nat.le_pred_of_lt (wv_lt m x b)))
      (by decide)
  have h1 := colv_le_len (m := m) (x := x) (B := 2 ^ 65 - 2) (ts := sqrTerms k) fun t ht => by
    simp only [sqrTerms, List.mem_append, List.mem_map] at ht
    rcases ht with ⟨i, -, rfl⟩ | ht
    · have := hw (PA + 4 * i) (PA + 4 * (k - i))
      simp only [tval]; omega_using [this]
    · split at ht
      · simp only [List.mem_singleton] at ht
        subst ht
        have := hw (PA + 4 * (k / 2)) (PA + 4 * (k / 2))
        simp only [tval]; omega_using [this]
      · exact absurd ht List.not_mem_nil
  have h2 := Nat.mul_le_mul_right (2 ^ 65 - 2) hl'
  omega_using [h1, h2]

/-- The words at `PA` squared, modulo the prime, into the element at `o`. -/
theorem sqrWords_ok {s : State} {base : Addr} {n o a : Nat} (hc : FnCtx s base n o a) :
    WP isa (.block (prodWords sqrTerms)) s fun t =>
      fe t.mem base o % Spec.X448.P = fe s.mem base PA * fe s.mem base PA % Spec.X448.P ∧
      FieldMem base o s.mem t.mem WORK ∧ Keeps clob s t := by
  rw [fe, ← num_wv hc.scr _ (by decide)]
  have hA := num_lt (f := fun i => wv s.mem (s.gpr .edi) (PA + 4 * i)) (n := 14) fun _ _ => wv_lt _ _ _
  refine prodWords_ok hc (fun k _ => sqrTerms_reads) (fun k hk => sqrTerms_lt _ _ hk) ?_ ?_
  · rw [← sqr_identity 14]
    exact num_congr fun k _ => sqrTerms_colv _ _ _
  · have := Nat.mul_lt_mul_of_lt_of_lt hA hA
    rwa [← Nat.pow_add] at this

/-! ## The function's body -/

/-- An argument after code that keeps `esp` and writes only the working space. -/
theorem ArgArea.arg_keep {s t : State} {base : Addr} {n : Nat} (h : ArgArea s base n) {rs : List Reg}
    (hk : Keeps rs s t) (hr : .esp ∉ rs) (hm : Outside base 0 8192 s.mem t.mem) {i : Nat} (hi : i < n) :
    arg t i = arg s i :=
  (h.keep (hk.1 _ hr) hk.2.1 hk.2.2 hm).2 i hi

/-- `vg_gf448_r32_mul` between its entry and its exit. -/
theorem mulBody_ok {t : State} {base : Addr} {o a b : Nat} (tc : FnCtx t base 4 o a)
    (hvb : arg t 3 = BitVec.ofNat 32 b) (hb : Slot b) :
    WP isa (.block (argPtr .esi 2 ++ operand PA ++ argPtr .esi 3 ++ operand PB ++ prodWords prodTerms)) t fun w =>
      FnPost base o t w ∧ F w.mem base o = F t.mem base a * F t.mem base b := by
  have ha' : a + 56 ≤ 3584 := tc.slotA
  have hb' : b + 56 ≤ 3584 := hb
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (argPtr_ok tc.args (by decide) (by decide) tc.argA) fun s1 ⟨p1, m1, k1⟩ => ?_
  have c1 := tc.keep k1 (by decide) (by decide) (by rw [m1]; exact Outside.refl _ _ _ _)
  rw [WP.block_append_iff]
  refine WP.mono (operand_ok c1.scr tc.slotA (by decide) (by decide) p1) fun s2 ⟨v2, m2, k2⟩ => ?_
  rw [m1] at v2 m2
  have k02 : Keeps (.esi :: clob) t s2 := (k1.mono (by decide)).trans (k2.mono (by decide))
  have o2 : Outside base 0 8192 t.mem s2.mem := m2.mono (by decide) (by decide)
  have c2 := tc.keep k02 (by decide) (by decide) o2
  rw [WP.block_append_iff]
  refine WP.mono (argPtr_ok c2.args (by decide) (by decide)
    ((tc.args.arg_keep k02 (by decide) o2 (by decide)).trans hvb)) fun s3 ⟨p3, m3, k3⟩ => ?_
  have c3 := c2.keep k3 (by decide) (by decide) (by rw [m3]; exact Outside.refl _ _ _ _)
  rw [WP.block_append_iff]
  refine WP.mono (operand_ok c3.scr hb (by decide) (by decide) p3) fun s4 ⟨v4, m4, k4⟩ => ?_
  rw [m3] at v4 m4
  rw [m2.fe (Or.inl (by simp only [PA, ACC]; omega_arith)) (by omega_arith)] at v4
  have va : fe s4.mem base PA = fe t.mem base a := by
    rw [← v2]; exact m4.fe (Or.inl (by decide)) (by decide)
  have k24 : Keeps (.esi :: clob) s2 s4 := (k3.mono (by decide)).trans (k4.mono (by decide))
  have c4 := c2.keep k24 (by decide) (by decide) (m4.mono (by decide) (by decide))
  refine WP.mono (mulWords_ok c4) fun s5 ⟨v5, m5, k5⟩ =>
    ⟨⟨k02.trans (k24.trans (k5.mono (by decide))), ?_⟩, ?_⟩
  · exact (FieldMem.work m2 (by decide) (by decide)).trans ((FieldMem.work m4 (by decide) (by decide)).trans m5)
  · rw [va, v4] at v5; exact toFe_mul v5

/-- `vg_gf448_r32_sqr` between its entry and its exit. -/
theorem sqrBody_ok {t : State} {base : Addr} {n o a : Nat} (tc : FnCtx t base n o a) :
    WP isa (.block (argPtr .esi 2 ++ operand PA ++ prodWords sqrTerms)) t fun w =>
      FnPost base o t w ∧ F w.mem base o = F t.mem base a * F t.mem base a := by
  have hn := tc.n3
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (argPtr_ok tc.args (by omega_arith) (by decide) tc.argA) fun s1 ⟨p1, m1, k1⟩ => ?_
  have c1 := tc.keep k1 (by decide) (by decide) (by rw [m1]; exact Outside.refl _ _ _ _)
  rw [WP.block_append_iff]
  refine WP.mono (operand_ok c1.scr tc.slotA (by decide) (by decide) p1) fun s2 ⟨v2, m2, k2⟩ => ?_
  rw [m1] at v2 m2
  have k02 : Keeps (.esi :: clob) t s2 := (k1.mono (by decide)).trans (k2.mono (by decide))
  have c2 := tc.keep k02 (by decide) (by decide) (m2.mono (by decide) (by decide))
  refine WP.mono (sqrWords_ok c2) fun s5 ⟨v5, m5, k5⟩ => ⟨⟨k02.trans (k5.mono (by decide)), ?_⟩, ?_⟩
  · exact (FieldMem.work m2 (by decide) (by decide)).trans m5
  · rw [v2] at v5; exact toFe_mul v5

end VG.Proof.X448.X86

end

end


/-!
# X448 on x86 (32-bit): the field functions

`vg_gf448_r32_{mul,sqr,add,sub,mul_a24}` (`Impl/X448/X86.lean`) from their entry
(`FnEntry`: the working space `ws` at `base` and the offsets on the stack):
`fnEntry` loads `ws` into `edi` and saves the callee-saved registers in the
last 16 bytes of the functions' own working space (`fnEntry_ok`), the
operation writes its result (`Small.lean` and above), and
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
the result at `o` and its own working space. -/
structure FnOut (base : Addr) (o : Nat) (s t : State) : Prop where
  keeps : Keeps [.eax, .ecx, .edx] s t
  mem : FieldMem base o s.mem t.mem

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
  have ho' : o + 56 ≤ 3584 := ho
  refine hs.of_readW fun p hp => ?_
  obtain hp' : SAVE ≤ p.2 ∧ p.2 + 4 ≤ SAVE + 16 := by revert p hp; decide
  obtain hs' : p.2 + 4 < 2 ^ 64 := by simp only [SAVE] at hp'; omega_arith
  exact Mem.readW_congr fun i hi => h _
    (Or.inr (by rw [ofs_off base (d := p.2) (i := i) (by omega_arith)]; simp only [SAVE] at hp'; omega_arith))
    (Or.inr (by rw [ofs_off base (d := p.2) (i := i) (by omega_arith)]; simp only [SAVE, ACC, WORK] at hp' ⊢; omega_arith))

/-- The exit, after a body that changed the registers `rs` (not `esp`) and,
in the working space, the result and the arithmetic's own bytes. -/
theorem fnExit_out {s t u : State} {base : Addr} {n o a : Nat} (tc : FnCtx t base n o a)
    (tv : FnSaved base s.gpr t.mem) (tm : Outside base SAVE 16 s.mem t.mem) (tk : Keeps [.eax, .edi] s t)
    {rs : List Reg} (hrs : .esp ∉ rs) (uk : Keeps rs t u) (us : Scr u base)
    (um : FieldMem base o t.mem u.mem WORK) :
    WP isa (.block fnExit) u fun w => FnOut base o s w ∧ w.mem = u.mem := by
  refine WP.mono (fnExit_ok us (tv.keep tc.slotO um)) fun w ⟨wr, wm, wk⟩ => ?_
  refine ⟨⟨⟨fun r hr => ?_, wk.2.1.trans (uk.2.1.trans tk.2.1), wk.2.2.trans (uk.2.2.trans tk.2.2)⟩,
    ?_⟩, wm⟩
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
  refine WP.mono (hb t tc tm tk) fun u ⟨⟨uk, um⟩, uq⟩ => ?_
  refine WP.mono (fnExit_out tc tv tm tk (by decide) uk (tc.scr.of_keeps uk (by decide)) um)
    fun w ⟨hw, wm⟩ => ⟨hw, by rw [wm]; exact uq⟩

/-- The third argument after the entry. -/
theorem argB_keep {s t : State} {base : Addr} {o a b : Nat} (h : FnEntry s base 4 o a)
    (hvb : arg s 3 = BitVec.ofNat 32 b) (tk : Keeps [.eax, .edi] s t)
    (tm : Outside base SAVE 16 s.mem t.mem) : arg t 3 = BitVec.ofNat 32 b := by
  rw [(h.args.keep (tk.1 _ (by decide)) tk.2.1 tk.2.2 (tm.mono (by decide) (by decide))).2 3 (by decide), hvb]

/-- Operands below the own working space read the same after the entry. -/
theorem entry_operand {s t : State} {base : Addr} {a : Nat} (ha : Slot a)
    (tm : Outside base SAVE 16 s.mem t.mem) : fe t.mem base a = fe s.mem base a := by
  have ha' : a + 56 ≤ 3584 := ha
  exact tm.fe (Or.inl (by simp only [SAVE]; omega_arith)) (by omega_arith)

theorem mulA24Fn_ok {s : State} {base : Addr} {o a : Nat} (h : FnEntry s base 3 o a) (hoa : SlotApart o a) :
    WP isa mulA24Fn s fun t => FnOut base o s t ∧ F t.mem base o = Spec.X448.a24 * F s.mem base a := by
  rw [show mulA24Fn = .block (fnEntry ++ (argPtr .esi 2 ++ argPtr .ebp 1 ++ mulA24) ++ fnExit)
    by simp only [mulA24Fn, List.append_assoc]]
  refine fnBlock_ok (Q := fun m => F m base o = Spec.X448.a24 * F s.mem base a) h fun t tc tm _ => ?_
  exact WP.mono (a24Body_ok tc hoa) fun u ⟨up, uv⟩ => ⟨up, by rw [uv, F, F, entry_operand h.slotA tm]⟩

theorem addFn_ok {s : State} {base : Addr} {o a b : Nat} (h : FnEntry s base 4 o a)
    (hvb : arg s 3 = BitVec.ofNat 32 b) (hb : Slot b) (hoa : SlotApart o a) (hob : SlotApart o b) :
    WP isa addFn s fun t => FnOut base o s t ∧ F t.mem base o = F s.mem base a + F s.mem base b := by
  rw [show addFn = .block (fnEntry ++ (argPtrs ++ addSub .adc) ++ fnExit)
    by simp only [addFn, List.append_assoc]]
  refine fnBlock_ok (Q := fun m => F m base o = F s.mem base a + F s.mem base b) h fun t tc tm tk => ?_
  refine WP.mono (addSubBody_ok (.inl rfl) tc (argB_keep h hvb tk tm) hb hoa hob)
    fun u ⟨up, R₁, c₁, hc, hR, h₁, hF⟩ => ⟨up, ?_⟩
  rw [entry_operand h.slotA tm, entry_operand hb tm] at h₁
  exact toFe_add (add_val h₁ hR hc hF)

theorem subFn_ok {s : State} {base : Addr} {o a b : Nat} (h : FnEntry s base 4 o a)
    (hvb : arg s 3 = BitVec.ofNat 32 b) (hb : Slot b) (hoa : SlotApart o a) (hob : SlotApart o b) :
    WP isa subFn s fun t => FnOut base o s t ∧ F t.mem base o = F s.mem base a - F s.mem base b := by
  rw [show subFn = .block (fnEntry ++ (argPtrs ++ addSub .sbb) ++ fnExit)
    by simp only [subFn, List.append_assoc]]
  refine fnBlock_ok (Q := fun m => F m base o = F s.mem base a - F s.mem base b) h fun t tc tm tk => ?_
  refine WP.mono (addSubBody_ok (.inr rfl) tc (argB_keep h hvb tk tm) hb hoa hob)
    fun u ⟨up, R₁, c₁, hc, hR, h₁, hF⟩ => ⟨up, ?_⟩
  rw [entry_operand h.slotA tm, entry_operand hb tm] at h₁
  exact toFe_sub (sub_val h₁ hR hc hF)

theorem mulFn_ok {s : State} {base : Addr} {o a b : Nat} (h : FnEntry s base 4 o a)
    (hvb : arg s 3 = BitVec.ofNat 32 b) (hb : Slot b) :
    WP isa mulFn s fun t => FnOut base o s t ∧ F t.mem base o = F s.mem base a * F s.mem base b := by
  rw [show mulFn = .block (fnEntry ++ (argPtr .esi 2 ++ operand PA ++ argPtr .esi 3 ++ operand PB ++
    prodWords prodTerms) ++ fnExit) by simp only [mulFn, List.append_assoc]]
  refine fnBlock_ok (Q := fun m => F m base o = F s.mem base a * F s.mem base b) h fun t tc tm tk => ?_
  exact WP.mono (mulBody_ok tc (argB_keep h hvb tk tm) hb) fun u ⟨up, uv⟩ =>
    ⟨up, by rw [uv, F, F, F, F, entry_operand h.slotA tm, entry_operand hb tm]⟩

theorem sqrFn_ok {s : State} {base : Addr} {o a : Nat} (h : FnEntry s base 3 o a) :
    WP isa sqrFn s fun t => FnOut base o s t ∧ F t.mem base o = F s.mem base a * F s.mem base a := by
  rw [show sqrFn = .block (fnEntry ++ (argPtr .esi 2 ++ operand PA ++ prodWords sqrTerms) ++
    fnExit) by simp only [sqrFn, List.append_assoc]]
  refine fnBlock_ok (Q := fun m => F m base o = F s.mem base a * F s.mem base a) h fun t tc tm tk => ?_
  exact WP.mono (sqrBody_ok tc) fun u ⟨up, uv⟩ => ⟨up, by rw [uv, F, F, entry_operand h.slotA tm]⟩

end VG.Proof.X448.X86

end

end

/-! ### `X448.Field32Contract`, which this module and modules that import it used -/

section

/-!
# Curve448's field in radix `2^32`

Not trusted: the representation of elements of `GF(p)`,
`p = 2^448 - 2^224 - 1`, each fourteen 32-bit words, that the 32-bit x86
code of X448 and Ed448 keeps them in, and on which its field
functions (`vg_gf448_r32_mul`, `_sqr`, `_add`, `_sub` and `_mul_a24`) work.

An element is fourteen 32-bit little-endian words, least significant first:
the element `Σ wᵢ 2^(32 i)` (`valAt`), any number below `2^448` (so not
necessarily below `p`). The
elements live in a working space `ws` of 8192 bytes (`[u64; 1024]`, the
working space of X448's and Ed448's functions), each at a byte offset: `o`
for the result, `a` and `b` for the operands. The offsets are arguments, so
that the result may be an operand (but not overlap one otherwise, `Apart`)
and the caller keeps its elements where it likes. Bytes 3584 to 4095 of `ws`
are the function's own working space (`ownAt`), and the elements lie below
them (`Fits`). On return the function's own bytes are unspecified and may
hold intermediate values; every other byte of `ws` keeps its value but the
result's (`Keeps`).
-/

@[expose] public section

namespace VG.Proof.X448.Field32

open VG.Spec VG.Spec.X448

/-- The words of an element. -/
def words : Nat := 14

/-- The bytes of an element. -/
def elemBytes : Nat := 4 * words

/-- Where the function's own working space starts; it ends at byte 4096. -/
def ownAt : Nat := 3584

/-- Word `i` of the element at byte offset `o` of the working space `ws`. -/
def wordAt (m : Mem) (ws : Addr) (o : BitVec 32) (i : Nat) : Nat :=
  (m.readW (ws + BitVec.ofNat 64 (o.toNat + 4 * i)) 32).toNat

/-- The value of the first `n` words of the element at `o`: `Σ wᵢ 2^(32 i)`. -/
def valN (m : Mem) (ws : Addr) (o : BitVec 32) : Nat → Nat
  | 0 => 0
  | n + 1 => valN m ws o n + (2 ^ 32) ^ n * wordAt m ws o n

/-- The value of the element at `o`. -/
def valAt (m : Mem) (ws : Addr) (o : BitVec 32) : Nat := valN m ws o words

/-- The elements at `o` and `a` are the same, or apart. -/
def Apart (o a : BitVec 32) : Prop :=
  o = a ∨ o.toNat + elemBytes ≤ a.toNat ∨ a.toNat + elemBytes ≤ o.toNat

/-- The element at `o` lies below the function's own working space. -/
abbrev Fits (o : BitVec 32) : Prop := o.toNat + elemBytes ≤ ownAt

/-- Every byte of `ws` but those of the function's own working space and of
the result at `o` keeps its value. -/
def Keeps (ws : Addr) (o : BitVec 32) (m m' : Mem) : Prop :=
  ∀ i < 8192, (i < ownAt ∨ 4096 ≤ i) → (i < o.toNat ∨ o.toNat + elemBytes ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

end VG.Proof.X448.Field32

end

end

/-!
# X448 on x86 (32-bit): the field functions' contracts

The contracts the field functions are proven against (`binX86`, `unX86`):
the facts of the shared contracts of `Proof/X448/X86/FnVerified.lean` stated for x86
(`fnPre`: the working space, and the arguments on the stack), which the
shared contracts imply (`sig_implies`, in `FnVerified.lean`). The entry
those facts give (`FnEntry.of_pre`), and the shared postcondition from what
the proofs state (`FnOut.post`).
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16
open VG.Proof.X25519.X86 (num)

/-- The working space, the first argument. -/
abbrev wsOf (s : State) : Addr := (arg s 0).setWidth 64

/-- The shared contracts' facts about the state, for arguments of `len` bytes. -/
def fnPre (len : Nat) (s : State) : Prop :=
  (s.gpr .esp).toNat + 4 + len ≤ 2 ^ 32 ∧ s.rd = [⟨argAddr s 0, len⟩] ∧ s.wr = [⟨wsOf s, 8192⟩] ∧
    Region.Disjoint ⟨wsOf s, 8192⟩ ⟨argAddr s 0, len⟩ ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨wsOf s, 8192⟩ ∧ (arg s 0).toNat + 8192 ≤ 2 ^ 32

/-- The binary functions' contract, for the relation `r` of the values. -/
def binX86 (r : Nat → Nat → Nat → Prop) : Contract isa where
  pre s := fnPre 16 s ∧ Proof.X448.Field32.Fits (arg s 1) ∧ Proof.X448.Field32.Fits (arg s 2) ∧
    Proof.X448.Field32.Fits (arg s 3) ∧ Proof.X448.Field32.Apart (arg s 1) (arg s 2) ∧
    Proof.X448.Field32.Apart (arg s 1) (arg s 3)
  post s s' :=
    r (Proof.X448.Field32.valAt s'.mem (wsOf s) (arg s 1)) (Proof.X448.Field32.valAt s.mem (wsOf s) (arg s 2))
      (Proof.X448.Field32.valAt s.mem (wsOf s) (arg s 3)) ∧
    Proof.X448.Field32.Keeps (wsOf s) (arg s 1) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧
    arg s₁ 2 = arg s₂ 2 ∧ arg s₁ 3 = arg s₂ 3

/-- The unary functions' contract, for the relation `r` of the values. -/
def unX86 (r : Nat → Nat → Prop) : Contract isa where
  pre s := fnPre 12 s ∧ Proof.X448.Field32.Fits (arg s 1) ∧ Proof.X448.Field32.Fits (arg s 2) ∧
    Proof.X448.Field32.Apart (arg s 1) (arg s 2)
  post s s' :=
    r (Proof.X448.Field32.valAt s'.mem (wsOf s) (arg s 1)) (Proof.X448.Field32.valAt s.mem (wsOf s) (arg s 2)) ∧
    Proof.X448.Field32.Keeps (wsOf s) (arg s 1) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧
    arg s₁ 2 = arg s₂ 2

/-- `vg_gf448_r32_mul_a24`'s contract. -/
def a24X86 : Contract isa := unX86 fun o a => o % Spec.X448.P = 39081 * a % Spec.X448.P

/-- `vg_gf448_r32_sqr`'s contract: what `vg_gf448_r32_mul`'s gives for equal operands. -/
def sqrX86 : Contract isa := unX86 fun o a => o % Spec.X448.P = a * a % Spec.X448.P

theorem not_contains_ofs {base x : Addr} (h : ¬ (⟨base, 8192⟩ : Region).Contains x 1) :
    8192 ≤ ofs base x := by
  simp only [Region.Contains] at h; simp only [ofs]; omega_using [h]

/-- The entry the facts of the contract give. -/
theorem FnEntry.of_pre {s : State} {n : Nat} (hn : 3 ≤ n) (h : fnPre (4 * n) s)
    (ho : Proof.X448.Field32.Fits (arg s 1)) (ha : Proof.X448.Field32.Fits (arg s 2)) :
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
    ∀ n, Proof.X448.Field32.valN m ws o n = num (limbs m ws o.toNat) n
  | 0 => rfl
  | n + 1 => by
    rw [Proof.X448.Field32.valN, num, valN_spec m ws o n]
    rfl

theorem valAt_eq (m : Mem) (ws : Addr) (o : BitVec 32) :
    Proof.X448.Field32.valAt m ws o = fe m ws o.toNat := valN_spec m ws o 14

theorem slotApart_of {o a : BitVec 32} (h : Proof.X448.Field32.Apart o a) : SlotApart o.toNat a.toNat := by
  rcases h with rfl | h
  · exact .inl rfl
  · exact .inr h

/-- `Keeps` from the frame of the field functions. -/
theorem FieldMem.keeps {base : Addr} {o : BitVec 32} {m m' : Mem} (h : FieldMem base o.toNat m m') :
    Proof.X448.Field32.Keeps base o m m' := by
  intro i hi hw ho
  simp only [Proof.X448.Field32.ownAt, Proof.X448.Field32.elemBytes, Proof.X448.Field32.words] at hw ho
  exact h _ (by rw [ofs, Mem.sub_ofNat_toNat base (by omega_using [hi])]; omega_using [ho])
    (by rw [ofs, Mem.sub_ofNat_toNat base (by omega_using [hi])]; simp only [ACC]; omega_using [hw])

end VG.Proof.X448.X86

end

end

/-!
# X448 on x86 (32-bit): the field functions' `Verified`

Correctness under `binX86` and `unX86` (`FnContract.lean`), constant time
by taint tracking (every branch is on the row pointer and every address is
`ws`, an offset, the row pointer or `esp` plus a constant: only the
arguments, which are public, and `esp` need be), satisfiability, and the
shared contracts of `Proof/X448/X86/FnVerified.lean`.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem slot_of_fits {o : BitVec 32} (h : Proof.X448.Field32.Fits o) : Slot o.toNat := h

/-- A difference, as `Spec` states it. -/
theorem toFe_sub_inv {a b c : Nat} (h : toFe c = toFe a - toFe b) : (c + b) % Spec.X448.P = a % Spec.X448.P := by
  have e := congrArg Fin.val h
  simp only [toFe_val, Fin.sub_def] at e
  have hx : a % Spec.X448.P < Spec.X448.P := Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne Spec.X448.P))
  have hy : b % Spec.X448.P < Spec.X448.P := Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne Spec.X448.P))
  rw [Nat.add_mod, e]
  generalize a % Spec.X448.P = x at *
  generalize b % Spec.X448.P = y at *
  rcases Nat.lt_or_ge (Spec.X448.P - y + x) Spec.X448.P with h1 | h1
  · rw [Nat.mod_eq_of_lt h1, show Spec.X448.P - y + x + y = x + Spec.X448.P by omega_using [hy], Nat.add_mod_right, Nat.mod_eq_of_lt hx]
  · rw [show (Spec.X448.P - y + x) % Spec.X448.P = Spec.X448.P - y + x - Spec.X448.P by rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega_using [hx])],
      show Spec.X448.P - y + x - Spec.X448.P + y = x by omega_using [hx, h1], Nat.mod_eq_of_lt hx]

/-- What a field function changes preserves the calling convention. -/
theorem FnOut.abi {c : Prog isa} (hc : NoSp c) (h0 : stackUse c = 0) {s s' : State} {tr : List Leak}
    (ex : Exec isa c s tr s') (hwr : ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ r)
    {base : Addr} {o : Nat} (h : FnOut base o s s') : abiPreserved s s' := by
  refine ⟨fun r hr => h.keeps.1 r (by revert r hr; decide), ?_⟩
  have hf := VG.X86.Exec.frameSp ex hc (by omega_using [h0])
  rw [h0] at hf
  refine Mem.readW_congr fun k hk => hf _ fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · exact fun hc' => hwr r hr _ (by simp only [Region.Contains]; rw [Offset.add_sub_cancel_left]; simp only [BitVec.toNat_ofNat]; omega_using [hk]) hc'
  · rw [List.mem_singleton.mp hr]; simp only [Region.Contains]; omega_using []

theorem fnPre_ret {len : Nat} {s : State} (h : fnPre len s) :
    ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ r := by
  intro r hr; rw [h.2.2.1, List.mem_singleton] at hr; subst hr; exact h.2.2.2.2.1

theorem mulFn_correct (s : State) (hs : (binX86 fun o a b => o % Spec.X448.P = a * b % Spec.X448.P).pre s) :
    ∃ t s', Exec isa mulFn s t s' ∧ abiPreserved s s' ∧
      (binX86 fun o a b => o % Spec.X448.P = a * b % Spec.X448.P).post s s' := by
  obtain ⟨hp, ho, ha, hb, la, lb⟩ := hs
  have he := FnEntry.of_pre (n := 4) (by decide) hp ho ha
  obtain ⟨t, s', ex, hk, hv⟩ := mulFn_ok he (b := (arg s 3).toNat) (by simp) (slot_of_fits hb)
  refine ⟨t, s', ex, hk.abi (NoSp.of_all (by lit_decide)) (by lit_decide) ex (fnPre_ret hp), ?_, hk.mem.keeps⟩
  rw [valAt_eq, valAt_eq, valAt_eq]
  exact toFe_eq_iff.mp (hv.trans (toFe_mul rfl).symm)

theorem addFn_correct (s : State) (hs : (binX86 fun o a b => o % Spec.X448.P = (a + b) % Spec.X448.P).pre s) :
    ∃ t s', Exec isa addFn s t s' ∧ abiPreserved s s' ∧
      (binX86 fun o a b => o % Spec.X448.P = (a + b) % Spec.X448.P).post s s' := by
  obtain ⟨hp, ho, ha, hb, la, lb⟩ := hs
  have he := FnEntry.of_pre (n := 4) (by decide) hp ho ha
  obtain ⟨t, s', ex, hk, hv⟩ := addFn_ok he (b := (arg s 3).toNat) (by simp) (slot_of_fits hb)
    (slotApart_of la) (slotApart_of lb)
  refine ⟨t, s', ex, hk.abi (NoSp.of_all (by lit_decide)) (by lit_decide) ex (fnPre_ret hp), ?_, hk.mem.keeps⟩
  rw [valAt_eq, valAt_eq, valAt_eq]
  exact toFe_eq_iff.mp (hv.trans (toFe_add rfl).symm)

theorem subFn_correct (s : State) (hs : (binX86 fun o a b => (o + b) % Spec.X448.P = a % Spec.X448.P).pre s) :
    ∃ t s', Exec isa subFn s t s' ∧ abiPreserved s s' ∧
      (binX86 fun o a b => (o + b) % Spec.X448.P = a % Spec.X448.P).post s s' := by
  obtain ⟨hp, ho, ha, hb, la, lb⟩ := hs
  have he := FnEntry.of_pre (n := 4) (by decide) hp ho ha
  obtain ⟨t, s', ex, hk, hv⟩ := subFn_ok he (b := (arg s 3).toNat) (by simp) (slot_of_fits hb)
    (slotApart_of la) (slotApart_of lb)
  refine ⟨t, s', ex, hk.abi (NoSp.of_all (by lit_decide)) (by lit_decide) ex (fnPre_ret hp), ?_, hk.mem.keeps⟩
  rw [valAt_eq, valAt_eq, valAt_eq]
  exact toFe_sub_inv hv

theorem mulA24Fn_correct (s : State) (hs : a24X86.pre s) :
    ∃ t s', Exec isa mulA24Fn s t s' ∧ abiPreserved s s' ∧ a24X86.post s s' := by
  obtain ⟨hp, ho, ha, la⟩ := hs
  have he := FnEntry.of_pre (n := 3) (by decide) hp ho ha
  obtain ⟨t, s', ex, hk, hv⟩ := mulA24Fn_ok he (slotApart_of la)
  refine ⟨t, s', ex, hk.abi (NoSp.of_all (by lit_decide)) (by lit_decide) ex (fnPre_ret hp), ?_, hk.mem.keeps⟩
  rw [valAt_eq, valAt_eq]
  exact toFe_eq_iff.mp (hv.trans (toFe_a24 rfl).symm)

theorem sqrFn_correct (s : State) (hs : sqrX86.pre s) :
    ∃ t s', Exec isa sqrFn s t s' ∧ abiPreserved s s' ∧ sqrX86.post s s' := by
  obtain ⟨hp, ho, ha, la⟩ := hs
  have he := FnEntry.of_pre (n := 3) (by decide) hp ho ha
  obtain ⟨t, s', ex, hk, hv⟩ := sqrFn_ok he
  refine ⟨t, s', ex, hk.abi (NoSp.of_all (by lit_decide)) (by lit_decide) ex (fnPre_ret hp), ?_, hk.mem.keeps⟩
  rw [valAt_eq, valAt_eq]
  exact toFe_eq_iff.mp (hv.trans (toFe_mul rfl).symm)

/-! ## Constant time -/

/-- The analysis starts with `esp` and the `len` bytes of arguments public. -/
def fnτ (len : Nat) : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 4 + len }

theorem fn_wf {len : Nat} {s : State} (h : fnPre len s) : VG.X86.Taint.Wf (fnτ len) s := by
  obtain ⟨hsp, _, hwr, hdis, hret, _⟩ := h
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨by simp only [fnτ]; omega_using [hsp], ?_⟩,
    fun _ h => (List.not_mem_nil h).elim⟩
  rw [hwr]
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact VG.X86.Taint.frame_disjoint (n := len) hsp hret hdis.symm

/-- Two states of the precondition whose `esp` and arguments agree agree on
what `fnτ` says is public. -/
theorem fn_agree {len : Nat} {s₁ s₂ : State} (h₁ : fnPre len s₁) (h₂ : fnPre len s₂)
    (hesp : s₁.gpr .esp = s₂.gpr .esp) (ha : ∀ i, 4 * i < len → arg s₁ i = arg s₂ i) :
    VG.X86.Taint.Agree (fnτ len) s₁ s₂ := by
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, fn_wf h₁, fn_wf h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [fnτ, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · simp only [fnτ] at hk
    rw [show VG.X86.Taint.depth (fnτ len).stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 4 + len) (by have := h₁.1; omega_using [this]) h4 hk,
      VG.X86.Taint.argByte_eq (n := 4 + len) (by have := h₂.1; omega_using [this]) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (ha _ (by omega_using [h4, hk]))

theorem mulFn_check : ∃ h, (taint.check (fnτ 16) mulFn h).isSome = true := ⟨_, by taint_decide⟩

theorem mulFn_ct {pre : State → Prop} {pub : State → State → Prop}
    (h : ∀ s₁ s₂, pre s₁ → pre s₂ → pub s₁ s₂ → VG.X86.Taint.Agree (fnτ 16) s₁ s₂) :
    ConstantTime isa pre pub mulFn :=
  let ⟨_, hc⟩ := mulFn_check
  VG.Taint.constantTime (A := taint) (fnτ 16) h hc

theorem addFn_check : ∃ h, (taint.check (fnτ 16) addFn h).isSome = true := ⟨_, by taint_decide⟩

theorem addFn_ct {pre : State → Prop} {pub : State → State → Prop}
    (h : ∀ s₁ s₂, pre s₁ → pre s₂ → pub s₁ s₂ → VG.X86.Taint.Agree (fnτ 16) s₁ s₂) :
    ConstantTime isa pre pub addFn :=
  let ⟨_, hc⟩ := addFn_check
  VG.Taint.constantTime (A := taint) (fnτ 16) h hc

theorem subFn_check : ∃ h, (taint.check (fnτ 16) subFn h).isSome = true := ⟨_, by taint_decide⟩

theorem subFn_ct {pre : State → Prop} {pub : State → State → Prop}
    (h : ∀ s₁ s₂, pre s₁ → pre s₂ → pub s₁ s₂ → VG.X86.Taint.Agree (fnτ 16) s₁ s₂) :
    ConstantTime isa pre pub subFn :=
  let ⟨_, hc⟩ := subFn_check
  VG.Taint.constantTime (A := taint) (fnτ 16) h hc

theorem mulA24Fn_check : ∃ h, (taint.check (fnτ 12) mulA24Fn h).isSome = true := ⟨_, by taint_decide⟩

theorem mulA24Fn_ct {pre : State → Prop} {pub : State → State → Prop}
    (h : ∀ s₁ s₂, pre s₁ → pre s₂ → pub s₁ s₂ → VG.X86.Taint.Agree (fnτ 12) s₁ s₂) :
    ConstantTime isa pre pub mulA24Fn :=
  let ⟨_, hc⟩ := mulA24Fn_check
  VG.Taint.constantTime (A := taint) (fnτ 12) h hc

theorem sqrFn_check : ∃ h, (taint.check (fnτ 12) sqrFn h).isSome = true := ⟨_, by taint_decide⟩

theorem sqrFn_ct {pre : State → Prop} {pub : State → State → Prop}
    (h : ∀ s₁ s₂, pre s₁ → pre s₂ → pub s₁ s₂ → VG.X86.Taint.Agree (fnτ 12) s₁ s₂) :
    ConstantTime isa pre pub sqrFn :=
  let ⟨_, hc⟩ := sqrFn_check
  VG.Taint.constantTime (A := taint) (fnτ 12) h hc

theorem bin_agree {r : Nat → Nat → Nat → Prop} (s₁ s₂ : State) (h₁ : (binX86 r).pre s₁)
    (h₂ : (binX86 r).pre s₂) (hp : (binX86 r).pub s₁ s₂) : VG.X86.Taint.Agree (fnτ 16) s₁ s₂ := by
  obtain ⟨e, a0, a1, a2, a3⟩ := hp
  refine fn_agree h₁.1 h₂.1 e fun i hi => ?_
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega_using [hi]
  rcases this with rfl | rfl | rfl | rfl
  exacts [a0, a1, a2, a3]

theorem un_agree {r : Nat → Nat → Prop} (s₁ s₂ : State) (h₁ : (unX86 r).pre s₁) (h₂ : (unX86 r).pre s₂)
    (hp : (unX86 r).pub s₁ s₂) : VG.X86.Taint.Agree (fnτ 12) s₁ s₂ := by
  obtain ⟨e, a0, a1, a2⟩ := hp
  refine fn_agree h₁.1 h₂.1 e fun i hi => ?_
  have : i = 0 ∨ i = 1 ∨ i = 2 := by omega_using [hi]
  rcases this with rfl | rfl | rfl
  exacts [a0, a1, a2]



end VG.Proof.X448.X86
