module

public import VerifiedGarbage.Proof.Ed448.X86.BaseLocal
public import VerifiedGarbage.Proof.Ed448.Formulas
public import VerifiedGarbage.Proof.Ed448.CombRef
import VerifiedGarbage.Proof.X448.X86.Counters
public import VerifiedGarbage.Proof.X448.X86.Ops
import VerifiedGarbage.Proof.X448.X86.Iter
public import VerifiedGarbage.Impl.Ed448.X86.ScalarBase
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ed448.X86.BaseEncode
public import VerifiedGarbage.Proof.X448.X86.Runs
public import VerifiedGarbage.Proof.Ed448.X86.ScalarIO
import VerifiedGarbage.Proof.X448.X86.FnLit
import VerifiedGarbage.Proof.X448.X86.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Impl.X25519.X86
public import VerifiedGarbage.Proof.X448.X86.Env
import VerifiedGarbage.Proof.X448.X86.FnContract
public import VerifiedGarbage.Proof.X448.X86.Bits
import VerifiedGarbage.Proof.Ed448.Scalar
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Framework.Range

/-! ### `Ed448.X86.BaseSetup`, which this module and modules that import it used -/

section

/-!
# Ed448 base-point multiplication on x86 (32-bit): the entry

Every slot set to its initial value (`initSlots_ok`): `R = (0 : 1 : 1)`, `B`
the base point, `d`, and zero elsewhere, every limb below `2¹⁶`. Then the
scalar's 57 bytes expanded into its 456 bits at `BITS` (`baseBytes_ok`), by
X448's `bitsLoop`.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Impl.Ed448.X86 (initVal initLimb initStep initSlot zeroSlots initSlots)
open VG.Impl.X448.X86 (slot ACC st BITS bitsLoop at_)
open VG.Spec.Ed448 (bytesAt decodeLE)

/-! ## The slots -/

theorem initVal_lt (i : Nat) : initVal i < Spec.X448.P := by
  unfold initVal
  repeat (first | exact Fin.isLt _ | (split; exact Fin.isLt _) | split)
  decide +kernel

theorem initLimb_lt (i k : Nat) : initLimb i k < 65536 := Nat.mod_lt _ (by decide)

theorem valN_digits (v : Nat) : ∀ n, valN (fun k => v / 2 ^ (16 * k) % 65536) n = v % radix ^ n
  | 0 => by simp [valN, Nat.mod_one]
  | n + 1 => by
    rw [valN_succ, valN_digits v n, Nat.mod_pow_succ, radix, ← Nat.pow_mul]

/-- The 704 words of the slots zeroed. -/
theorem zeroSlots_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa zeroSlots s fun t => (∀ j < 704, word t.mem base (64 + 4 * j) = 0) ∧
      Outside base 64 2816 s.mem t.mem ∧ Keeps [.eax, .ebx, .ebp] s t := by
  -- After `n` words.
  let inv : Nat → State → Prop := fun n t => Scr t base ∧
    t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (4 * (16 + n)) ∧ t.gpr .ebx = 0 ∧
    t.gpr .eax = BitVec.ofNat 32 (704 - n) ∧ (∀ j < n, word t.mem base (64 + 4 * j) = 0) ∧
    Outside base 64 2816 s.mem t.mem ∧ Keeps [.eax, .ebx, .ebp] s t
  unfold zeroSlots
  refine WP.seq (wp_mov rfl fun u₁ hu₁ => wp_alu (Or.inl rfl) rfl fun u₂ hu₂ _ => wp_mov rfl fun u₃ hu₃ =>
    wp_mov rfl fun u hu => WP.block_nil ?_)
  have ku : Keeps [.eax, .ebx, .ebp] s u :=
    (hu₁.rest (by decide)).trans ((hu₂.rest (by decide)).trans ((hu₃.rest (by decide)).trans (hu.rest (by decide))))
  have i₀ : inv 0 u := by
    refine ⟨hs.of_keeps ku (by decide), ?_, by rw [hu.other _ (by decide), hu₃.gpr], hu.gpr,
      fun _ h => absurd h (Nat.not_lt_zero _), by rw [hu.mem, hu₃.mem, hu₂.mem, hu₁.mem]; exact Outside.refl _ _ _ _,
      ku⟩
    rw [hu.other _ (by decide), hu₃.other _ (by decide), hu₂.gpr, hu.other _ (by decide), hu₃.other _ (by decide),
      hu₂.other _ (by decide), hu₁.gpr, hu₁.other _ (by decide)]
    rfl
  refine WP.mono (WP.loop (M := isa) (Q := inv 704) (fun m t => ∃ n, m = 704 - n ∧ n < 704 ∧ inv n t) ?_ 704 u
    ⟨0, rfl, by decide, i₀⟩) fun t ⟨_, _, _, _, z, o, k⟩ => ⟨z, o, k⟩
  rintro m t ⟨n, rfl, hn, ts, tp, tb, ta, tz, tm, tk⟩
  refine wp_store (a := off base (64 + 4 * n)) (by rw [rowEa ts tp (by omega_arith)]; congr 1; omega_arith)
    (ts.write (by omega_arith)) fun v hv => ?_
  refine wp_alu (Or.inl rfl) rfl fun w hw _ => wp_alu (Or.inr (Or.inl rfl)) rfl fun x hx hz => WP.block_nil ?_
  have kx : Keeps [.eax, .ebx, .ebp] t x :=
    (hv.rest _).trans ((hw.rest (by decide)).trans (hx.rest (by decide)))
  have mx : x.mem = t.mem.writeW (off base (64 + 4 * n)) (0 : BitVec 32) := by
    rw [hx.mem, hw.mem, hv.mem, tb]
  have ax : x.gpr .eax = BitVec.ofNat 32 (704 - (n + 1)) := by
    rw [hx.gpr, hw.other _ (by decide), hv.gpr, ta]
    simp only [aluVal]
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_arith)
      (by omega_arith)]
    congr 1
  have nx : inv (n + 1) x := by
    refine ⟨ts.of_keeps kx (by decide), ?_, ?_, ax, fun j hj => ?_, ?_, tk.trans kx⟩
    · rw [hx.other _ (by decide), hw.gpr, hv.gpr, tp, kx.1 _ (by decide)]
      simp only [aluVal]
      rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      congr 2
    · exact (hx.other _ (by decide)).trans ((hw.other _ (by decide)).trans ((congrFun hv.gpr _).trans tb))
    · rw [mx, word_write t.mem base (o := 64) (by omega_arith) (by omega_arith)]
      by_cases e : j = n
      · rw [ite_eq_left e]
      · rw [ite_eq_right e]; exact tz j (by omega_arith)
    · rw [mx]; exact tm.trans ((writeW_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  simp only [eval, hz, Option.map_some]
  by_cases done : n + 1 = 704
  · refine .inl ⟨?_, done ▸ nx⟩
    rw [hw.other _ (by decide), hv.gpr, ta]
    simp only [aluVal]
    rw [show n = 703 by omega_arith]; decide
  · refine .inr ⟨?_, 704 - (n + 1), by omega_arith, n + 1, rfl, by omega_arith, nx⟩
    rw [hw.other _ (by decide), hv.gpr, ta]
    simp only [aluVal]
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_arith)
      (by omega_arith)]
    have hlt : 704 - n - 1 < 2 ^ 32 := by omega_arith
    have h0 : BitVec.ofNat 32 (704 - n - 1) ≠ 0 := fun h => by
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at this
      have h2 : 704 - n - 1 = 0 := this.trans rfl
      omega_arith
    simpa using h0

theorem initStep_ok {s : State} {base : Addr} (hs : Scr s base)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * 16)) {i k : Nat} (hi : i < 22) (hk : k < 28)
    (hz : limbs s.mem base (slot i) k = 0) :
    WP isa (.block (initStep i k)) s fun t =>
      limbs t.mem base (slot i) k = initLimb i k ∧ Outside base (slot i + 4 * k) 4 s.mem t.mem ∧
        Keeps [.eax] s t := by
  have hsl : slot i + 4 * k + 4 ≤ 4096 := by simp only [slot]; omega_arith
  unfold initStep
  split
  · rename_i h0
    exact WP.block_nil ⟨by rw [hz, h0], Outside.refl _ _ _ _, Keeps.refl _ _⟩
  · refine wp_mov rfl fun u hu => ?_
    have hsu := hs.of_upd hu (by decide)
    refine wp_store (a := off base (slot i + 4 * k))
      (by rw [rowEa hsu (by rw [hu.other .ebp (by decide), hu.other .edi (by decide)]; exact hp) (by omega_arith)]
          congr 1; simp only [slot]; omega_arith)
      (hsu.write (by omega_arith)) fun t ht => WP.block_nil ⟨?_, ?_, (hu.rest (by decide)).trans (ht.rest _)⟩
    · change (Proof.X448.X86.word t.mem base (slot i + 4 * k)).toNat = _
      rw [ht.mem, hu.gpr, Proof.X448.X86.word, Mem.readW_writeW_self32, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by have := initLimb_lt i k; omega_arith)]
    · rw [ht.mem, hu.mem]; exact writeW_outside _ _ _ (by omega_arith)

theorem initSlot_ok {s : State} {base : Addr} (hs : Scr s base)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * 16)) {i : Nat}
    (hi : i < 22) (hz : ∀ k < 28, limbs s.mem base (slot i) k = 0) :
    WP isa (.block (initSlot i)) s fun t =>
      (∀ k < 28, limbs t.mem base (slot i) k = initLimb i k) ∧
        Outside base (slot i) 112 s.mem t.mem ∧ Keeps [.eax] s t := by
  have hsl : slot i + 112 ≤ 4096 := by simp only [slot]; omega_arith
  let inv := fun n (t : State) => (∀ k < n, limbs t.mem base (slot i) k = initLimb i k) ∧
    (∀ k, n ≤ k → k < 28 → limbs t.mem base (slot i) k = 0) ∧
    Outside base (slot i) 112 s.mem t.mem ∧ Keeps [.eax] s t
  refine WP.mono (wp_range_flatMap (M := isa) (N := 28) inv (fun n t hn ⟨tf, t0, tm, tk⟩ => ?_) 28 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun k _ hk => hz k hk, Outside.refl _ _ _ _, Keeps.refl _ _⟩)
    fun t ⟨tf, _, tm, tk⟩ => ⟨tf, tm, tk⟩
  refine WP.mono (initStep_ok (hs.of_keeps tk (by decide))
    (by rw [tk.1 _ (by decide), tk.1 _ (by decide)]; exact hp) hi hn (t0 n (Nat.le_refl _) hn))
    fun u ⟨uf, um, uk⟩ => ⟨fun k hk => ?_, fun k hk hk' => ?_, tm.trans (um.mono (by omega_arith) (by omega_arith)),
      tk.trans uk⟩
  · by_cases h : k = n
    · rw [h]; exact uf
    · change (Proof.X448.X86.word u.mem base (slot i + 4 * k)).toNat = _
      rw [um.word (by omega_arith) (by simp only [slot]; omega_arith)]
      exact tf k (by omega_arith)
  · change (Proof.X448.X86.word u.mem base (slot i + 4 * k)).toNat = _
    rw [um.word (by omega_arith) (by simp only [slot]; omega_arith)]
    exact t0 k (by omega_arith) hk'

theorem initSlots_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa initSlots s fun t =>
      (∀ i < 22, ∀ k < 28, limbs t.mem base (slot i) k = initLimb i k) ∧
        Outside base 64 2816 s.mem t.mem ∧ Keeps [.eax, .ebx, .ebp] s t := by
  unfold initSlots
  refine WP.seq (WP.mono (zeroSlots_ok hs) fun s₀ ⟨z₀, o₀, k₀⟩ => ?_)
  have hs₀ := hs.of_keeps k₀ (by decide)
  simp only [List.cons_append, List.nil_append]
  refine wp_mov rfl fun u₁ hu₁ => wp_alu (Or.inl rfl) rfl fun u hu _ => ?_
  have hsu := (hs₀.of_upd hu₁ (by decide)).of_upd hu (by decide)
  have ku : Keeps [.eax, .ebx, .ebp] s u :=
    k₀.trans ((hu₁.rest (by decide)).trans (hu.rest (by decide)))
  have hpu : u.gpr .ebp = u.gpr .edi + BitVec.ofNat 32 (4 * 16) := by
    rw [hu.gpr, hu.other .edi (by decide), hu₁.other .edi (by decide)]
    change u₁.gpr .ebp + BitVec.ofNat 32 64 = _
    rw [hu₁.gpr]
  have mu : u.mem = s₀.mem := by rw [hu.mem, hu₁.mem]
  let inv := fun n (t : State) => (∀ i < n, ∀ k < 28, limbs t.mem base (slot i) k = initLimb i k) ∧
    (∀ i, n ≤ i → i < 22 → ∀ k < 28, limbs t.mem base (slot i) k = 0) ∧
    Outside base 64 2816 s.mem t.mem ∧ Keeps [.eax] u t
  have zu : ∀ i, 0 ≤ i → i < 22 → ∀ k < 28, limbs u.mem base (slot i) k = 0 := fun i _ hi k hk => by
    change (Proof.X448.X86.word u.mem base (slot i + 4 * k)).toNat = 0
    rw [mu, show slot i + 4 * k = 64 + 4 * (32 * i + k) by simp only [slot]; omega_arith, z₀ _ (by omega_arith)]
    rfl
  have i0 : inv 0 u := ⟨fun _ h => absurd h (Nat.not_lt_zero _), zu, by rw [mu]; exact o₀, Keeps.refl _ _⟩
  refine WP.mono (wp_range_flatMap (M := isa) (N := 22) inv (fun n t hn ⟨tf, t0, tm, tk⟩ => ?_) 22
    (by decide) u i0)
    fun t ⟨tf, _, tm, tk⟩ => ⟨tf, tm, ku.trans (tk.mono (by simp))⟩
  refine WP.mono (initSlot_ok (hsu.of_keeps tk (by decide))
    (by rw [tk.1 _ (by decide), tk.1 _ (by decide)]; exact hpu) hn (t0 n (Nat.le_refl _) hn))
    fun v ⟨vf, vm, vk⟩ => ⟨fun i hi k hk => ?_, fun i hi hi' k hk => ?_,
      tm.trans (vm.mono (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith)), tk.trans vk⟩
  · by_cases h : i = n
    · subst h; exact vf k hk
    · rw [vm.limbs (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) hk]
      exact tf i (by omega_arith) k hk
  · rw [vm.limbs (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) hk]
    exact t0 i (by omega_arith) hi' k hk

/-- The slots' values. -/
theorem initSlots_E {m : Mem} {base : Addr}
    (h : ∀ i < 22, ∀ k < 28, limbs m base (slot i) k = initLimb i k) (i : Index) :
    E m base i = Proof.X448.toFe (initVal i.val) := by
  simp only [E, F, fe]
  rw [valN_congr (g := fun k => initVal i.val / 2 ^ (16 * k) % 65536) (h i.val i.isLt), valN_digits,
    Nat.mod_eq_of_lt (Nat.lt_trans (initVal_lt _) (by decide +kernel))]

theorem initSlots_bounded {m : Mem} {base : Addr}
    (h : ∀ i < 22, ∀ k < 28, limbs m base (slot i) k = initLimb i k) : BoundedEnv m base :=
  fun i k hk => by rw [h i.val i.isLt k hk]; exact initLimb_lt _ _

/-! ## The scalar's bits -/

/-- The 57 bytes at `esi` expanded into their bits at `BITS` (X448's `bitsLoop_ok`). -/
theorem baseBytes_ok {s : State} {base k : Addr} (hs : Scr s base)
    (hk : (s.gpr .esi).setWidth 64 = k) (hfit : (s.gpr .esi).toNat + 57 ≤ 2 ^ 32)
    (hr : ∀ i < 57, InRegions (s.rd ++ s.wr) (off k i) 1)
    (hd : ∀ i < 57, 8192 ≤ ofs base (off k i)) :
    WP isa (bitsLoop BITS 57) s fun t =>
      Keeps bitRegs s t ∧ Outside base BITS 456 s.mem t.mem ∧
      ∀ j < 456, t.mem (off base (BITS + j)) =
        BitVec.ofNat 8 ((decodeLE (bytesAt s.mem k 57) >>> j) &&& 1) :=
  WP.mono (bitsLoop_ok hs (by decide) (by decide) (by decide) hk hfit hr hd) fun t ⟨tk, tm, tb, _⟩ =>
    ⟨tk, tm, fun j hj => by rw [tb j hj, Proof.Ed448.scalar_bit _ _ hj]⟩

end VG.Proof.Ed448.X86

end

end

/-! ### `Ed448.X86.BaseStep`, which this module and modules that import it used -/

section

/-!
# Ed448 base-point multiplication on x86 (32-bit): the comb's rows

The doubling and addition programs (`Impl/Ed448/Formulas.lean`) run as X448's
verified field operations on the slots (`ops_ok`), and evaluate to `double`
and the specification's `pointAdd` (`rowEnv_r`): `Proof/Ed448/CombRef.lean`'s
`combRow`. One row (`combStep_ok`) doubles `R` (slots 0–2), computes the index
of its four bits of the scalar (`combDigit_ok`), selects the table's entry of
that index into `Q`'s `x` and `y` (slots 8 and 9: `combSelect_ok`, every entry
ORed in under the mask of its index being the row's), and adds `Q` into `T`
(slots 3–5), copied into `R`; the loop (`combLoop_ok`) leaves `R` as the comb
over all 114 rows, `comb k 114`.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Proof.Ed448 (double comb combRow combPoint comb_row combDigit_lt pt addWith)
open VG.Impl.Ed448 (doubleOps addOps)
open VG.Impl.Ed448.X86 (toOp field combLimb selMask selLimb selCoord selEntry zeroSlot combSelect takeOps
  combStep combLoop)
open VG.Impl.X448.X86 (BITS slot ACC ld st sc at_)

/-! ## The field programs -/

def doubleFields : List FieldOp := [
  .add 12 0 1, .mul 12 12 12, .mul 13 0 0, .mul 14 1 1, .add 15 13 14, .mul 16 2 2,
  .add 17 16 16, .sub 17 15 17, .sub 18 12 15, .mul 0 18 17, .sub 19 13 14, .mul 1 15 19,
  .mul 2 15 17]

def addFields : List FieldOp := [
  .mul 12 2 10, .mul 13 12 12, .mul 14 0 8, .mul 15 1 9, .mul 16 11 14, .mul 16 16 15,
  .sub 17 13 16, .add 18 13 16, .add 19 0 1, .add 20 8 9, .mul 19 19 20, .mul 20 12 17,
  .sub 19 19 14, .sub 19 19 15, .mul 3 20 19, .mul 20 12 18, .sub 19 15 14, .mul 4 20 19,
  .mul 5 17 18]

/-- `T` (slots 3–5) into `R` (slots 0–2). -/
def takeFields : List FieldOp := [.copy 0 3, .copy 1 4, .copy 2 5]

theorem doubleFields_impl : doubleOps.map toOp = doubleFields.map FieldOp.impl := by decide +kernel
theorem addTake_impl : addOps.map toOp ++ takeOps = (addFields ++ takeFields).map FieldOp.impl := by
  decide +kernel

/-- The table's entry `i` in `Q`'s `x` and `y`. -/
def selEnv (i : Nat) (e : Env) : Env :=
  Function.update (Function.update e 8 (Impl.Ed448.Comb.entry i).1) 9 (Impl.Ed448.Comb.entry i).2

/-- The slots after a row of index `i`. -/
def rowEnv (i : Nat) (e : Env) : Env :=
  applyOps (addFields ++ takeFields) (selEnv i (applyOps doubleFields e))

theorem rowEnv_pt (i : Nat) (e : Env) :
    pt (rowEnv i e) 0 1 2 = addWith (e 11) (double (pt e 0 1 2))
      ⟨(Impl.Ed448.Comb.entry i).1, (Impl.Ed448.Comb.entry i).2, e 10⟩ := rfl

theorem rowEnv_r (k t : Nat) (e : Env) (h1 : e 10 = 1) (hd : e 11 = Spec.Ed448.d) :
    pt (rowEnv (Proof.Ed448.combDigit k t) e) 0 1 2 = combRow k t (pt e 0 1 2) := by
  rw [rowEnv_pt, h1, hd]; rfl

theorem rowEnv_one (i : Nat) (e : Env) : rowEnv i e 10 = e 10 := rfl

theorem rowEnv_d (i : Nat) (e : Env) : rowEnv i e 11 = e 11 := rfl

/-! ## The row's index -/

theorem bit_lt (k t : Nat) : (k >>> t) &&& 1 < 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

/-- Four bits, each a byte, as the row's index. -/
theorem digit_val : ∀ b0 < 2, ∀ b1 < 2, ∀ b2 < 2, ∀ b3 < 2,
    (let c3 := (BitVec.ofNat 8 b3).setWidth 32
     let c2 := c3 + c3 + (BitVec.ofNat 8 b2).setWidth 32
     let c1 := c2 + c2 + (BitVec.ofNat 8 b1).setWidth 32
     c1 + c1 + (BitVec.ofNat 8 b0).setWidth 32) =
      BitVec.ofNat 32 (b0 + 2 * b1 + 4 * b2 + 8 * b3) := by
  decide

/-- The index of row `t` (`esi`) of the bits of `k`, a byte each from `o`, into `ecx`. -/
theorem combDigit_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : o + 456 ≤ 8192)
    {k t : Nat} (ht : t < 114) (hb : s.gpr .esi = BitVec.ofNat 32 t)
    (hbits : ∀ i < 456, s.mem (off base (o + i)) = BitVec.ofNat 8 ((k >>> i) &&& 1)) :
    WP isa (.block (Impl.Ed448.X86.combDigit o)) s fun u =>
      u.gpr .ecx = BitVec.ofNat 32 (Proof.Ed448.combDigit k t) ∧ Keeps [.ebp, .ecx, .eax] s u ∧
        u.mem = s.mem := by
  unfold Impl.Ed448.X86.combDigit
  refine wp_mov rfl fun u1 v1 => wp_alu (Or.inl rfl) rfl fun u2 v2 _ => ?_
  obtain ep : u2.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 t := by
    rw [v2.gpr]; change u1.gpr .ebp + u1.gpr .esi = _
    rw [v1.gpr, v1.other .esi (by decide), hb]
  obtain ea : ∀ (u : State) (c : Nat), u.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 t → c + t < 8192 →
      u.ea (at_ .ebp c) = off base (c + t) := fun u c hu hc => by
    change (u.gpr .ebp + BitVec.ofNat 32 c).setWidth 64 = _
    rw [hu, Offset.add_add, Nat.add_comm t c]
    exact hs.ea hc
  obtain rd : ∀ c, c + t < 8192 → InRegions (s.rd ++ s.wr) (off base (c + t)) 1 := fun c hc =>
    hs.read (by omega_using [hc])
  obtain bit : ∀ c, c + t < 456 → s.mem (off base (o + c + t)) = BitVec.ofNat 8 ((k >>> (t + c)) &&& 1) :=
    fun c hc => by
      rw [show o + c + t = o + (t + c) by omega_arith]
      exact hbits _ (by omega_using [hc])
  obtain m2 : u2.mem = s.mem := by rw [v2.mem, v1.mem]
  obtain r2 : u2.rd ++ u2.wr = s.rd ++ s.wr := by rw [v2.rd, v2.wr, v1.rd, v1.wr]
  refine wp_load8 (a := off base (o + 342 + t)) (ea u2 _ ep (by omega_using [ho, ht]))
    (by rw [r2]; exact rd _ (by omega_using [ho, ht])) fun u3 v3 => ?_
  obtain c3 : u3.gpr .ecx = (BitVec.ofNat 8 ((k >>> (t + 342)) &&& 1)).setWidth 32 := by
    rw [v3.gpr, m2, bit 342 (by omega_using [ht])]
  refine wp_load8 (a := off base (o + 228 + t))
    (ea u3 _ ((v3.other .ebp (by decide)).trans ep) (by omega_using [ho, ht]))
    (by rw [v3.rd, v3.wr, r2]; exact rd _ (by omega_using [ho, ht])) fun u4 v4 => ?_
  refine wp_alu (Or.inl rfl) rfl fun u5 v5 _ => wp_alu (Or.inl rfl) rfl fun u6 v6 _ => ?_
  obtain c6 : u6.gpr .ecx = u3.gpr .ecx + u3.gpr .ecx +
      (BitVec.ofNat 8 ((k >>> (t + 228)) &&& 1)).setWidth 32 := by
    rw [v6.gpr]; change u5.gpr .ecx + u5.gpr .eax = _
    rw [v5.gpr, v5.other .eax (by decide)]; change u4.gpr .ecx + u4.gpr .ecx + u4.gpr .eax = _
    rw [v4.gpr, v4.other .ecx (by decide), v3.mem, m2, bit 228 (by omega_using [ht])]
  obtain k6 : Keeps [.ebp, .ecx, .eax] u2 u6 :=
    (v3.rest (by decide)).trans ((v4.rest (by decide)).trans ((v5.rest (by decide)).trans (v6.rest (by decide))))
  obtain m6 : u6.mem = s.mem := by rw [v6.mem, v5.mem, v4.mem, v3.mem, m2]
  refine wp_load8 (a := off base (o + 114 + t))
    (ea u6 _ ((v6.other .ebp (by decide)).trans ((v5.other .ebp (by decide)).trans
      ((v4.other .ebp (by decide)).trans ((v3.other .ebp (by decide)).trans ep)))) (by omega_using [ho, ht]))
    (by rw [k6.2.1, k6.2.2, r2]; exact rd _ (by omega_using [ho, ht])) fun u7 v7 => ?_
  refine wp_alu (Or.inl rfl) rfl fun u8 v8 _ => wp_alu (Or.inl rfl) rfl fun u9 v9 _ => ?_
  obtain c9 : u9.gpr .ecx = u6.gpr .ecx + u6.gpr .ecx +
      (BitVec.ofNat 8 ((k >>> (t + 114)) &&& 1)).setWidth 32 := by
    rw [v9.gpr]; change u8.gpr .ecx + u8.gpr .eax = _
    rw [v8.gpr, v8.other .eax (by decide)]; change u7.gpr .ecx + u7.gpr .ecx + u7.gpr .eax = _
    rw [v7.gpr, v7.other .ecx (by decide), m6, bit 114 (by omega_using [ht])]
  obtain k9 : Keeps [.ebp, .ecx, .eax] u6 u9 :=
    (v7.rest (by decide)).trans ((v8.rest (by decide)).trans (v9.rest (by decide)))
  obtain m9 : u9.mem = s.mem := by rw [v9.mem, v8.mem, v7.mem, m6]
  refine wp_load8 (a := off base (o + 0 + t))
    (ea u9 _ ((v9.other .ebp (by decide)).trans ((v8.other .ebp (by decide)).trans
      ((v7.other .ebp (by decide)).trans ((v6.other .ebp (by decide)).trans ((v5.other .ebp (by decide)).trans
        ((v4.other .ebp (by decide)).trans ((v3.other .ebp (by decide)).trans ep)))))))
      (by omega_using [ho, ht]))
    (by rw [k9.2.1, k9.2.2, k6.2.1, k6.2.2, r2]; exact rd _ (by omega_using [ho, ht])) fun u10 v10 => ?_
  refine wp_alu (Or.inl rfl) rfl fun u11 v11 _ => wp_alu (Or.inl rfl) rfl fun u12 v12 _ =>
    WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [v12.gpr]; change u11.gpr .ecx + u11.gpr .eax = _
    rw [v11.gpr, v11.other .eax (by decide)]; change u10.gpr .ecx + u10.gpr .ecx + u10.gpr .eax = _
    rw [v10.gpr, v10.other .ecx (by decide), m9, bit 0 (by omega_using [ht]), c9, c6, c3]
    exact digit_val _ (bit_lt k t) _ (bit_lt k (t + 114)) _ (bit_lt k (t + 228)) _ (bit_lt k (t + 342))
  · exact ((v1.rest (by decide)).trans (v2.rest (by decide))).trans (k6.trans (k9.trans
      ((v10.rest (by decide)).trans ((v11.rest (by decide)).trans (v12.rest (by decide))))))
  · rw [v12.mem, v11.mem, v10.mem, m9]

/-! ## The selection -/

/-- The mask of entry `i`, for the index `d`. -/
theorem selMask_val : ∀ d < 16, ∀ i < 16,
    (0 : BitVec 32) - ((BitVec.ofNat 32 d ^^^ BitVec.ofNat 32 i) - 1) >>> 31 = mask (decide (d = i)) := by
  decide

theorem selMask_ok (s : State) {d i : Nat} (hd : d < 16) (hi : i < 16) (h5 : s.gpr .ecx = BitVec.ofNat 32 d) :
    WP isa (.block (selMask i)) s fun u =>
      u.gpr .ebx = mask (decide (d = i)) ∧ Keeps [.eax, .ebx] s u ∧ u.mem = s.mem := by
  unfold selMask
  refine wp_mov rfl fun u1 v1 => wp_alu (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) rfl fun u2 v2 _ => ?_
  refine wp_alu (Or.inr (Or.inl rfl)) rfl fun u3 v3 _ => wp_shift (by decide) fun u4 v4 => ?_
  refine wp_mov rfl fun u5 v5 => wp_alu (Or.inr (Or.inl rfl)) rfl fun u6 v6 _ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [v6.gpr]; change u5.gpr .ebx - u5.gpr .eax = _
    rw [v5.gpr, v5.other .eax (by decide), v4.gpr]; change (0 : BitVec 32) - u3.gpr .eax >>> 31 = _
    rw [v3.gpr]; change (0 : BitVec 32) - (u2.gpr .eax - 1) >>> 31 = _
    rw [v2.gpr]; change (0 : BitVec 32) - ((u1.gpr .eax ^^^ BitVec.ofNat 32 i) - 1) >>> 31 = _
    rw [v1.gpr, h5]; exact selMask_val d hd i hi
  · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans ((v5.rest (by decide)).trans (v6.rest (by decide))))))
  · rw [v6.mem, v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]

theorem selLimb_ok {s : State} {base : Addr} (hs : Scr s base) {o j : Nat} (ho : o + 112 ≤ 4096)
    (hj : j < 28) (v : Nat → Nat) {b : Bool} (h4 : s.gpr .ebx = mask b) :
    WP isa (.block (selLimb o v j)) s fun t =>
      t.mem = s.mem.writeW (off base (o + 4 * j))
        ((BitVec.ofNat 32 (v j) &&& mask b) ||| word s.mem base (o + 4 * j)) ∧
      Keeps [.eax] s t := by
  unfold selLimb
  refine wp_mov rfl fun u1 v1 => wp_alu (Or.inr (Or.inr (Or.inl rfl))) rfl fun u2 v2 _ => ?_
  obtain hs2 : Scr u2 base := (hs.of_upd v1 (by decide)).of_upd v2 (by decide)
  refine wp_alu (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (readSc hs2 (by omega_using [ho, hj])) fun u3 v3 _ => ?_
  refine store_ok (hs2.of_upd v3 (by decide)) (by omega_using [ho, hj]) fun u4 v4 => WP.block_nil ⟨?_, ?_⟩
  · rw [v4.mem, v3.mem, v3.gpr]
    change u2.mem.writeW _ (u2.gpr .eax ||| word u2.mem base _) = _
    rw [v2.gpr, v2.mem, v1.mem]
    change s.mem.writeW _ ((u1.gpr .eax &&& u1.gpr .ebx) ||| _) = _
    rw [v1.gpr, v1.other _ (by decide), h4]
  · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans (v4.rest _)))

theorem selCoord_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : o + 112 ≤ 4096)
    (v : Nat → Nat) {b : Bool} (h4 : s.gpr .ebx = mask b) :
    WP isa (.block (selCoord o v)) s fun t =>
      (∀ j < 28, word t.mem base (o + 4 * j) =
        (BitVec.ofNat 32 (v j) &&& mask b) ||| word s.mem base (o + 4 * j)) ∧
      Outside base o 112 s.mem t.mem ∧ Keeps [.eax] s t := by
  let inv := fun n (t : State) =>
    (∀ j < n, word t.mem base (o + 4 * j) =
      (BitVec.ofNat 32 (v j) &&& mask b) ||| word s.mem base (o + 4 * j)) ∧
    (∀ j, n ≤ j → j < 28 → word t.mem base (o + 4 * j) = word s.mem base (o + 4 * j)) ∧
    Outside base o 112 s.mem t.mem ∧ Keeps [.eax] s t
  obtain step : ∀ n t, n < 28 → inv n t → WP isa (.block (selLimb o v n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, ta, tm, tk⟩
    refine WP.mono (selLimb_ok (hs.of_keeps tk (by decide)) ho hn v ((tk.1 _ (by decide)).trans h4))
      fun u ⟨um, uk⟩ => ?_
    obtain out : Outside base (o + 4 * n) 4 t.mem u.mem := by
      rw [um]; exact writeW_outside _ _ _ (by omega_using [ho, hn])
    refine ⟨fun j hj => ?_, fun j hj hj' => ?_, tm.trans (out.mono (by omega_using []) (by omega_using [hn])),
      tk.trans uk⟩
    · rw [um, word_write t.mem base (by omega_using [ho, hn]) (by omega_using [ho, hn, hj])]
      by_cases h : j = n
      · rw [ite_eq_left h, h, ta n (Nat.le_refl _) hn]
      · rw [ite_eq_right h]; exact tf j (by omega_using [hj, h])
    · rw [out.word (by omega_using [hj]) (by omega_using [ho, hj'])]
      exact ta j (by omega_using [hj]) hj'
  refine WP.mono (wp_range_flatMap (M := isa) (N := 28) inv step 28 (by decide) s ?_)
    fun t ⟨tf, _, tm, tk⟩ => ⟨tf, tm, tk⟩
  exact ⟨fun _ hj => absurd hj (Nat.not_lt_zero _), fun _ _ _ => rfl, Outside.refl _ _ _ _, Keeps.refl _ _⟩

theorem zeroSlot_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : o + 112 ≤ 4096)
    (h3 : s.gpr .eax = 0) :
    WP isa (.block (zeroSlot o)) s fun t =>
      (∀ j < 28, word t.mem base (o + 4 * j) = 0) ∧ Outside base o 112 s.mem t.mem ∧ Keeps [] s t := by
  let inv := fun n (t : State) =>
    (∀ j < n, word t.mem base (o + 4 * j) = 0) ∧ Outside base o 112 s.mem t.mem ∧ Keeps [] s t
  obtain step : ∀ n t, n < 28 → inv n t → WP isa (.block [st .eax (o + 4 * n)]) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine store_ok (hs.of_keeps tk (by decide)) (by omega_using [ho, hn]) fun u hu => WP.block_nil ?_
    obtain out : Outside base (o + 4 * n) 4 t.mem u.mem := by
      rw [hu.mem]; exact writeW_outside _ _ _ (by omega_using [ho, hn])
    refine ⟨fun j hj => ?_, tm.trans (out.mono (by omega_using []) (by omega_using [hn])),
      tk.trans (hu.rest _)⟩
    rw [hu.mem, word_write t.mem base (by omega_using [ho, hn]) (by omega_using [ho, hn, hj])]
    by_cases h : j = n
    · rw [ite_eq_left h, tk.1 _ (by decide), h3]
    · rw [ite_eq_right h]; exact tf j (by omega_using [hj, h])
  exact wp_range_flatMap (M := isa) (N := 28) inv step 28 (by decide) s
    ⟨fun _ hj => absurd hj (Nat.not_lt_zero _), Outside.refl _ _ _ _, Keeps.refl _ _⟩

/-- After the first `n` entries: slots 8 and 9 hold the entry of index `d` if it is below `n`,
and zero otherwise. -/
def Sel (base : Addr) (d n : Nat) (m : Mem) : Prop :=
  ∀ c < 2, ∀ j < 28, word m base (slot (8 + c) + 4 * j) =
    if d < n then BitVec.ofNat 32 (combLimb d c j) else 0

theorem combLimb_lt (i c j : Nat) : combLimb i c j < 65536 := Nat.mod_lt _ (by decide)

theorem and_mask_true_or (x : BitVec 32) : (x &&& mask true) ||| (0 : BitVec 32) = x := by
  show (x &&& BitVec.allOnes 32) ||| 0 = x
  rw [BitVec.and_allOnes]
  exact BitVec.or_zero

theorem and_mask_false_or (w x : BitVec 32) : (x &&& mask false) ||| w = w := by
  have e : x &&& (0 : BitVec 32) = 0 := BitVec.and_zero
  show (x &&& 0) ||| w = w
  rw [e]
  exact BitVec.zero_or

/-- A limb of the selection after entry `n`. -/
theorem sel_word {d n : Nat} {w : BitVec 32} {v v' : Nat}
    (hw : w = if d < n then BitVec.ofNat 32 v' else 0) (hv' : d = n → v = v') :
    (BitVec.ofNat 32 v &&& mask (decide (d = n))) ||| w =
      if d < n + 1 then BitVec.ofNat 32 v' else 0 := by
  by_cases h : d = n
  · subst h
    rw [hw, ite_eq_right (Nat.lt_irrefl _), ite_eq_left (Nat.lt_succ_self _), decide_eq_true rfl, hv' rfl]
    exact and_mask_true_or _
  · rw [decide_eq_false h, and_mask_false_or, hw]
    by_cases hlt : d < n
    · rw [ite_eq_left hlt, ite_eq_left (by omega_using [hlt])]
    · rw [ite_eq_right hlt, ite_eq_right (by omega_using [hlt, h])]

theorem selEntry_ok {s : State} {base : Addr} (hs : Scr s base) {d n : Nat} (hd : d < 16) (hn : n < 16)
    (h5 : s.gpr .ecx = BitVec.ofNat 32 d) (hsel : Sel base d n s.mem) :
    WP isa (.block (selEntry n)) s fun t =>
      Sel base d (n + 1) t.mem ∧ Outside base (slot 8) 240 s.mem t.mem ∧ Keeps [.eax, .ebx] s t := by
  have h8 : slot 8 = 1088 := rfl
  have h9 : slot 9 = 1216 := rfl
  unfold selEntry
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (selMask_ok s hd hn h5) fun u ⟨u4, uk, um⟩ => ?_
  obtain hsu := hs.of_keeps uk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (selCoord_ok hsu (o := slot 8) (by omega_using [h8]) (combLimb n 0) u4)
    fun v ⟨vf, vm, vk⟩ => ?_
  obtain hsv := hsu.of_keeps vk (by decide)
  refine WP.mono (selCoord_ok hsv (o := slot 9) (by omega_using [h9]) (combLimb n 1)
    ((vk.1 _ (by decide)).trans u4)) fun w ⟨wf, wm, wk⟩ => ⟨?_, ?_, ?_⟩
  · intro c hc j hj
    rcases (by omega_using [hc] : c = 0 ∨ c = 1) with rfl | rfl
    · rw [show slot (8 + 0) = slot 8 from rfl, wm.word (by omega_using [h8, h9, hj]) (by omega_using [h8, hj]), vf j hj, um]
      exact sel_word (hsel 0 (by decide) j hj) (fun h => by rw [h])
    · rw [show slot (8 + 1) = slot 9 from rfl, wf j hj, vm.word (by omega_using [h8, h9, hj]) (by omega_using [h9, hj]), um]
      exact sel_word (hsel 1 (by decide) j hj) (fun h => by rw [h])
  · rw [← um]
    exact (vm.mono (by omega_using [h8]) (by omega_using [h8])).trans
      (wm.mono (by omega_using [h8, h9]) (by omega_using [h8, h9]))
  · exact uk.trans ((vk.mono (by decide)).trans (wk.mono (by decide)))

/-- A slot whose limbs are the digits of a field element holds it. -/
theorem F_digits {m : Mem} {base : Addr} {o : Nat} (x : Spec.X448.Fe)
    (h : ∀ k < 28, limbs m base o k = x.val / 2 ^ (16 * k) % 65536) : F m base o = x := by
  simp only [F, fe]
  rw [valN_congr (g := fun k => x.val / 2 ^ (16 * k) % 65536) h, valN_digits,
    Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide +kernel)), Proof.X448.toFe_self]

theorem combSelect_ok {s : State} {base : Addr} (hs : Scr s base) (hbd : BoundedEnv s.mem base) {d : Nat}
    (hd : d < 16) (h5 : s.gpr .ecx = BitVec.ofNat 32 d) :
    WP isa (.block combSelect) s fun t => Keep base s t ∧ BoundedEnv t.mem base ∧
      E t.mem base = selEnv d (E s.mem base) := by
  have h8 : slot 8 = 1088 := rfl
  have h9 : slot 9 = 1216 := rfl
  have hA : ACC = 3584 := rfl
  unfold combSelect
  rw [List.append_assoc]
  refine wp_mov rfl fun u hu => ?_
  obtain ku : Keeps [.eax, .ebx] s u := hu.rest (by decide)
  obtain hsu := hs.of_keeps ku (by decide)
  refine WP.block_append_iff.mpr (WP.mono (zeroSlot_ok hsu (o := slot 8) (by omega_using [h8]) hu.gpr)
    fun v ⟨vf, vm, vk⟩ => ?_)
  obtain hsv := hsu.of_keeps vk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zeroSlot_ok hsv (o := slot 9) (by omega_using [h9]) ((vk.1 _ (by decide)).trans hu.gpr))
    fun w ⟨wf, wm, wk⟩ => ?_
  obtain kw : Keeps [.eax, .ebx] s w := ku.trans ((vk.mono (by simp)).trans (wk.mono (by simp)))
  obtain ow : Outside base (slot 8) 240 s.mem w.mem := by
    rw [← hu.mem]
    exact (vm.mono (by omega_using [h8]) (by omega_using [h8])).trans
      (wm.mono (by omega_using [h8, h9]) (by omega_using [h8, h9]))
  obtain sel0 : Sel base d 0 w.mem := by
    intro c hc j hj
    rw [ite_eq_right (Nat.not_lt_zero _)]
    rcases (by omega_using [hc] : c = 0 ∨ c = 1) with rfl | rfl
    · rw [show slot (8 + 0) = slot 8 from rfl, wm.word (by omega_using [h8, h9, hj]) (by omega_using [h8, hj])]
      exact vf j hj
    · exact wf j hj
  let inv := fun n (t : State) =>
    Sel base d n t.mem ∧ Outside base (slot 8) 240 s.mem t.mem ∧ Keeps [.eax, .ebx] s t
  obtain step : ∀ n t, n < 16 → inv n t → WP isa (.block (selEntry n)) t (inv (n + 1)) := by
    intro n t hn ⟨ts, tm, tk⟩
    exact WP.mono (selEntry_ok (hs.of_keeps tk (by decide)) hd hn ((tk.1 _ (by decide)).trans h5) ts)
      fun x ⟨xs, xm, xk⟩ => ⟨xs, tm.trans xm, tk.trans xk⟩
  refine WP.mono (wp_range_flatMap (M := isa) (N := 16) inv step 16 (by decide) w ⟨sel0, ow, kw⟩)
    fun t ⟨ts, tm, tk⟩ => ?_
  obtain lx : ∀ j < 28, limbs t.mem base (slot 8) j = (Impl.Ed448.Comb.entry d).1.val / 2 ^ (16 * j) % 65536 :=
    fun j hj => by
      change (word t.mem base (slot (8 + 0) + 4 * j)).toNat = _
      rw [ts 0 (by decide) j hj, ite_eq_left hd, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.lt_trans (combLimb_lt _ _ _) (by decide))]
      rfl
  obtain ly : ∀ j < 28, limbs t.mem base (slot 9) j = (Impl.Ed448.Comb.entry d).2.val / 2 ^ (16 * j) % 65536 :=
    fun j hj => by
      change (word t.mem base (slot (8 + 1) + 4 * j)).toNat = _
      rw [ts 1 (by decide) j hj, ite_eq_left hd, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.lt_trans (combLimb_lt _ _ _) (by decide))]
      rfl
  obtain other : ∀ i : Index, i ≠ 8 → i ≠ 9 → ∀ j < 28,
      limbs t.mem base (slot i.val) j = limbs s.mem base (slot i.val) j := fun i h8' h9' j hj => by
    have e8 := slot_sep h8'
    have e9 := slot_sep h9'
    have hi := slot_bound i
    change slot i.val + 112 ≤ 3584 at hi
    exact tm.limbs (by change slot i.val + 112 ≤ slot 8 ∨ slot 8 + 112 ≤ slot i.val at e8
                       change slot i.val + 112 ≤ slot 9 ∨ slot 9 + 112 ≤ slot i.val at e9
                       omega_using [e8, e9, h8, h9]) (by omega_using [hi]) hj
  refine ⟨⟨tk.mono (by decide), fun p _ hp _ => tm p (by omega_using [hp, h8])⟩, fun i j hj => ?_, ?_⟩
  · by_cases i8 : i = 8
    · subst i8; change limbs t.mem base (slot 8) j < radix; rw [lx j hj]; exact Nat.mod_lt _ (by decide)
    · by_cases i9 : i = 9
      · subst i9; change limbs t.mem base (slot 9) j < radix; rw [ly j hj]; exact Nat.mod_lt _ (by decide)
      · rw [other i i8 i9 j hj]; exact hbd i j hj
  · funext i
    by_cases i9 : i = 9
    · subst i9; rw [selEnv, Function.update_self]; exact F_digits _ ly
    · rw [selEnv, Function.update_of_ne i9]
      by_cases i8 : i = 8
      · subst i8; rw [Function.update_self]; exact F_digits _ lx
      · rw [Function.update_of_ne i8]
        exact congrArg Proof.X448.toFe (valN_congr (other i i8 i9))

/-! ## One row -/

/-- The loop's invariant, after the rows above `n` of `k`. -/
structure CombInv (base : Addr) (k : Nat) (s₀ s : State) (n : Nat) : Prop where
  scr : Scr s base
  ctx : CallCtx s base
  bounded : BoundedEnv s.mem base
  regs : Keeps (.esi :: workRegs) s₀ s
  esi : s.gpr .esi = BitVec.ofNat 32 n
  mem : WsOut2 base 64 2816 ACC 512 s₀.mem s.mem
  r : pt (E s.mem base) 0 1 2 = comb k (114 - n)
  one : E s.mem base 10 = 1
  d : E s.mem base 11 = Spec.Ed448.d

theorem combStep_ok {s₀ s : State} {base : Addr} {k n : Nat} (hn : n < 114)
    (hbits : ∀ t < 456, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 ((k >>> t) &&& 1))
    (hi : CombInv base k s₀ s (n + 1)) :
    WP isa combStep s fun t => CombInv base k s₀ t n ∧ t.zf = some (decide (n = 0)) := by
  have hs := hi.scr
  have hB : BITS = 3072 := rfl
  have hA : ACC = 3584 := rfl
  unfold combStep
  refine WP.seq (WP.mono (decCounter_ok (by omega_using [hn]) hi.esi) fun s₁ ⟨b₁, g₁, m₁, rd₁, wr₁, _⟩ => ?_)
  obtain K₁ : Keeps [.esi] s s₁ := ⟨fun r hr => g₁ r (fun h => hr (by simp [h])), rd₁, wr₁⟩
  obtain hs₁ := hs.of_keeps K₁ (by decide)
  obtain hc₁ : CallCtx s₁ base := hi.ctx.keep (g₁ _ (by decide))
  rw [field, doubleFields_impl]
  refine WP.seq (WP.mono (ops_ok hs₁ hc₁ (m₁ ▸ hi.bounded) doubleFields) fun s₂ ⟨k₂, bb₂, e₂⟩ => ?_)
  obtain hs₂ := k₂.scr hs₁
  obtain b₂ : s₂.gpr .esi = BitVec.ofNat 32 n := by rw [k₂.regs.1 _ (by decide), b₁]
  obtain bits₂ : ∀ t < 456, s₂.mem (off base (BITS + t)) = BitVec.ofNat 8 ((k >>> t) &&& 1) := fun t ht => by
    rw [k₂.mem _ (by rw [ofs_off' base (by omega_using [ht, hB])]; omega_using [ht, hB])
      (by rw [ofs_off' base (by omega_using [ht, hB])]; omega_using [hB])
      (by rw [ofs_off' base (by omega_using [ht, hB])]; omega_using [ht, hB, hA]), m₁,
      hi.mem _ (by rw [ofs_off' base (by omega_using [ht, hB])]; omega_using [ht, hB])
        (by rw [ofs_off' base (by omega_using [ht, hB])]; omega_using [hB])
        (by rw [ofs_off' base (by omega_using [ht, hB])]; omega_using [ht, hB, hA])]
    exact hbits t ht
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (combDigit_ok hs₂ (by omega_using [hB]) hn b₂ bits₂) fun s₃ ⟨d₃, k₃, m₃⟩ => ?_
  obtain hs₃ := hs₂.of_keeps k₃ (by decide)
  refine WP.mono (combSelect_ok hs₃ (m₃ ▸ bb₂) (combDigit_lt k n) d₃) fun s₄ ⟨k₄, bb₄, e₄⟩ => ?_
  obtain K₃ : Keep base s₂ s₃ := ⟨k₃.mono (by decide), by rw [m₃]; exact WsOut2.refl _ _ _ _ _ _⟩
  obtain hs₄ := k₄.scr hs₃
  obtain hc₄ : CallCtx s₄ base := (K₃.trans k₄).ctx (k₂.ctx hc₁)
  rw [addTake_impl]
  refine WP.seq (WP.mono (ops_ok hs₄ hc₄ bb₄ (addFields ++ takeFields)) fun s₅ ⟨k₅, bb₅, e₅⟩ => ?_)
  refine wp_cmp rfl fun t vt hz => WP.block_nil ?_
  obtain K₆ : Keep base s₅ t := ⟨vt.rest _, by rw [vt.mem]; exact WsOut2.refl _ _ _ _ _ _⟩
  obtain core := k₂.trans (K₃.trans (k₄.trans (k₅.trans K₆)))
  obtain b₅ : s₅.gpr .esi = BitVec.ofNat 32 n := by
    rw [k₅.regs.1 _ (by decide), k₄.regs.1 _ (by decide), k₃.1 _ (by decide), b₂]
  obtain ee : E t.mem base = rowEnv (Proof.Ed448.combDigit k n) (E s.mem base) := by
    rw [vt.mem, e₅, e₄, m₃, e₂, m₁]; rfl
  refine ⟨⟨core.scr hs₁, core.ctx hc₁, vt.mem ▸ bb₅, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · refine hi.regs.trans ⟨fun r hr => ?_, core.regs.2.1.trans rd₁, core.regs.2.2.trans wr₁⟩
    rw [core.regs.1 r (fun h => hr (List.mem_cons_of_mem _ h)), g₁ r (fun h => hr (by simp [h]))]
  · rw [core.regs.1 _ (by decide), b₁]
  · refine hi.mem.trans ?_
    intro p h8 hp hq
    rw [core.mem p h8 hp hq, m₁]
  · rw [ee, rowEnv_r _ _ _ hi.one hi.d, hi.r, comb_row k hn]
  · rw [ee, rowEnv_one]; exact hi.one
  · rw [ee, rowEnv_d]; exact hi.d
  · rw [hz, b₅, show BitVec.ofNat 32 n - (0 : BitVec 32) = BitVec.ofNat 32 n from BitVec.sub_zero _,
      ofNat_beq_zero (by omega_using [hn])]

theorem combLoop_ok {s₀ s : State} {base : Addr} {k : Nat}
    (hbits : ∀ t < 456, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 ((k >>> t) &&& 1))
    (hi : ∀ s', s'.gpr .esi = BitVec.ofNat 32 114 → (∀ r, r ≠ .esi → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → CombInv base k s₀ s' 114) :
    WP isa combLoop s fun s' => CombInv base k s₀ s' 0 := by
  unfold combLoop
  refine WP.seq (WP.mono (setCounter_ok s 114 (by decide)) fun s' ⟨h1, h2, h3, h4, h5⟩ => ?_)
  refine WP.loop (M := isa) (body := combStep) (c := .ne) (Q := fun s' => CombInv base k s₀ s' 0)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 114 ∧ CombInv base k s₀ s m) ?_ 114 s'
    ⟨by decide, by decide, hi s' h1 h2 h3 h4 h5⟩
  intro m s ⟨h1, h2, hi⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega_arith⟩
  refine WP.mono (combStep_ok (by omega_arith) hbits hi) fun s' ⟨hi', hz⟩ => ?_
  simp only [eval, hz, Option.map_some]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, hi'⟩
  · refine .inr ⟨by simp only [decide_eq_false (by omega_arith : ¬m = 0), Bool.not_false], m, by omega_arith,
      by omega_arith, by omega_arith, hi'⟩

end VG.Proof.Ed448.X86

end

end


/-!
# Ed448 base-point multiplication on x86 (32-bit): the whole function

`vg_ed448_scalar_base(out = [esp + 4], scalar = [esp + 8], scratch = [esp + 12])`
against a local contract (`scalarBaseLocal`, `BaseLocal.lean`: the arguments
only read): it
computes the encoding of the comb over the scalar's bits
(`scalarBase_comb`): the entry, the scalar's bits, the loop (`R` ends as
`comb k 114`), the inversion of `Z` and the encoding. Every write is in the
working space but the result's, so the arguments and the scalar are read
unchanged; the callee-saved registers are restored from the working space,
and the return address is kept.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Proof.Ed448 (comb pt)
open VG.Impl.Ed448.X86 (scalarBase initSlots baseBits baseEntry initVal)
open VG.Impl.X448.X86 (slot BITS ACC at_)
open VG.Spec.Ed448 (bytesAt decodeLE)

/-- The precondition, by name. -/
structure BasePre (s : State) : Prop where
  rd : s.rd = [⟨(arg s 1).setWidth 64, 57⟩, ⟨argAddr s 0, 12⟩]
  wr : s.wr = [⟨(arg s 0).setWidth 64, 57⟩, scR (arg s 2)]
  out_sc : (⟨(arg s 0).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s 2))
  scalar_sc : (⟨(arg s 1).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s 2))
  args_out : (⟨argAddr s 0, 12⟩ : Region).Disjoint ⟨(arg s 0).setWidth 64, 57⟩
  args_sc : (⟨argAddr s 0, 12⟩ : Region).Disjoint (scR (arg s 2))
  ret_out : (retR s).Disjoint ⟨(arg s 0).setWidth 64, 57⟩
  ret_sc : (retR s).Disjoint (scR (arg s 2))
  out_fit : (arg s 0).toNat + 57 ≤ 2 ^ 32
  scalar_fit : (arg s 1).toNat + 57 ≤ 2 ^ 32
  sc_fit : (arg s 2).toNat + 8192 ≤ 2 ^ 32
  sp_fit : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  sp_room : 20 ≤ (s.gpr .esp).toNat
  stk_out : (stkR s).Disjoint ⟨(arg s 0).setWidth 64, 57⟩
  stk_sc : (stkR s).Disjoint (scR (arg s 2))

theorem BasePre.of {s : State} (h : scalarBaseLocal.pre s) : BasePre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

/-- The stack the calls use, as `below`. -/
theorem stkR_below {s : State} (h : 20 ≤ (s.gpr .esp).toNat) : stkR s = below (s.gpr .esp) 20 := by
  simp only [below]; rw [VG.X86.Taint.sub_setWidth h]

theorem BasePre.stk_args {s : State} (h : BasePre s) : (stkR s).Disjoint ⟨argAddr s 0, 12⟩ := by
  have h1 := h.sp_room
  have h2 := h.sp_fit
  refine Region.disjoint_of_le (Or.inl ?_) ?_ ?_ <;> simp only [argAddr] <;> bv_omega

theorem BasePre.stk_ret {s : State} (h : BasePre s) : (stkR s).Disjoint (retR s) := by
  have h1 := h.sp_room
  have h2 := h.sp_fit
  refine Region.disjoint_of_le (Or.inl ?_) ?_ ?_ <;> bv_omega

theorem BasePre.args {s : State} (h : BasePre s) : Args s 3 2 :=
  ⟨by rw [h.rd]; simp, by have := h.sp_fit; omega_using [this], by decide, by rw [h.wr]; simp, h.sc_fit,
    h.args_sc, h.ret_sc⟩

theorem initE (e : Env) (he : ∀ i : Index, e i = Proof.X448.toFe (initVal i.val)) :
    pt e 0 1 2 = Spec.Ed448.identity ∧ pt e 8 9 10 = Spec.Ed448.basePoint ∧ e 11 = Spec.Ed448.d := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [pt, he]
    rw [show ((0 : Index) : Nat) = 0 from rfl, show ((1 : Index) : Nat) = 1 from rfl,
      show ((2 : Index) : Nat) = 2 from rfl, show initVal 0 = Spec.Ed448.identity.X.val from rfl,
      show initVal 1 = Spec.Ed448.identity.Y.val from rfl,
      show initVal 2 = Spec.Ed448.identity.Z.val from rfl, Proof.X448.toFe_self,
      Proof.X448.toFe_self, Proof.X448.toFe_self]
  · simp only [pt, he]
    rw [show ((8 : Index) : Nat) = 8 from rfl, show ((9 : Index) : Nat) = 9 from rfl,
      show ((10 : Index) : Nat) = 10 from rfl, show initVal 8 = Spec.Ed448.basePoint.X.val from rfl,
      show initVal 9 = Spec.Ed448.basePoint.Y.val from rfl,
      show initVal 10 = Spec.Ed448.basePoint.Z.val from rfl, Proof.X448.toFe_self,
      Proof.X448.toFe_self, Proof.X448.toFe_self]
  · rw [he]; exact Proof.X448.toFe_self _

section
variable (σ : State)
/-- The working space and the scalar, from the entry state `σ`. -/
abbrev bsB : Addr := (arg σ 2).setWidth 64
abbrev kB : Nat := decodeLE (bytesAt σ.mem ((arg σ 1).setWidth 64) 57)
end

/-- After the entry block, from the entry state `σ`. -/
structure BMid (σ s : State) : Prop where
  pre : BasePre σ
  fe : FE bsB σ s
  rd : s.rd = σ.rd
  saved : Saved (bsB σ) σ.gpr s.mem
  bits : ∀ t < 456, s.mem (off (bsB σ) (BITS + t)) = BitVec.ofNat 8 ((kB σ >>> t) &&& 1)
  start : ∀ s', s'.gpr .esi = BitVec.ofNat 32 114 → (∀ r, r ≠ .esi → s'.gpr r = s.gpr r) →
    s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → CombInv (bsB σ) (kB σ) s s' 114

theorem entry_stage {s₀ : State} (h : BasePre s₀) :
    WP isa baseEntry s₀ (BMid s₀) := by
  have hA := h.args
  have hin : Input s₀ (bsB s₀) (arg s₀ 1) 57 :=
    Input.of_region h.scalar_fit (by rw [h.rd]; simp) h.scalar_sc
  refine WP.seq (WP.mono (save_ok hA) fun s₁ ⟨hs₁, sv₁, o₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (initSlots_ok hs₁) fun s₂ ⟨l₂, o₂, k₂⟩ => ?_)
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have k02 : Keeps [.eax, .ebx, .ebp, .edi] s₀ s₂ := (k₁.mono (by decide)).trans (k₂.mono (by decide))
  have o02 : Outside (bsB s₀) 0 8192 s₀.mem s₂.mem :=
    (o₁.mono (by omega_using []) (by omega_using [])).trans (o₂.mono (by omega_using []) (by omega_using []))
  unfold baseBits
  refine WP.seq (hA.load (i := 1) (k02.1 _ (by decide)) k02.2.1 k02.2.2 o02 (by decide)
    fun s₃ u₃ => WP.block_nil ?_)
  have hs₃ := hs₂.of_upd u₃ (by decide)
  refine WP.mono (baseBytes_ok (k := (arg s₀ 1).setWidth 64) hs₃ (by rw [u₃.gpr]) (by rw [u₃.gpr]; exact hin.fit)
    (by rw [u₃.rd, u₃.wr, k02.2.1, k02.2.2]; exact hin.read) hin.far) fun s₄ ⟨k₄, o₄, bits₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have mem34 : bytesAt s₃.mem ((arg s₀ 1).setWidth 64) 57 = bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 57 := by
    rw [u₃.mem]; exact hin.bytes o02
  rw [mem34] at bits₄
  have e₄ : ∀ i : Index, E s₄.mem (bsB s₀) i = Proof.X448.toFe (initVal i.val) := by
    intro i
    rw [← initSlots_E l₂ i]
    simp only [E, F]
    rw [o₄.fe (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega_using []))
      (by have := i.isLt; simp only [slot]; omega_using []), u₃.mem]
  have b₄ : BoundedEnv s₄.mem (bsB s₀) := by
    intro i j hj
    rw [o₄.limbs (d := slot i.val) (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega_using []))
      (by have := i.isLt; simp only [slot]; omega_using []) hj, u₃.mem]
    exact initSlots_bounded l₂ i j hj
  obtain ⟨er, eq, ed⟩ := initE _ e₄
  have k04 : Keeps [.eax, .ebx, .ebp, .edi, .esi, .edx, .ecx] s₀ s₄ :=
    (k02.mono (by decide)).trans ((u₃.rest (by decide)).trans (k₄.mono (by decide)))
  have sp₄ : s₄.gpr .esp = s₀.gpr .esp := k04.1 _ (by decide)
  have hc₄ : CallCtx s₄ (bsB s₀) := ⟨by rw [sp₄]; exact h.sp_room, by
    simp only [callStk, sp₄]; rw [← stkR_below h.sp_room]; exact h.stk_sc.symm⟩
  have o4w : Outside (bsB s₀) 0 8192 s₃.mem s₄.mem := o₄.mono (by omega_using []) (by simp only [BITS]; omega_using [])
  rw [u₃.mem] at o4w
  have ws : (⟨bsB s₀, 8192⟩ : Region) ∈ s₀.wr ++ [below (s₀.gpr .esp) 20] := by
    rw [h.wr]; simp
  refine ⟨h, ⟨⟨hs₄, hc₄, b₄⟩, sp₄, k04.2.2, (Outside.frame (o02.trans o4w)).mono fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ws⟩, k04.2.1,
    (sv₁.outside o₂ (by decide)).outside (u₃.mem ▸ o₄) (by decide), bits₄, fun s' h1 h2 h3 h4 h5 => ?_⟩
  have k' : Keeps (.esi :: workRegs) s₄ s' :=
    ⟨fun r hr => h2 r (fun e => hr (by subst r; exact List.mem_cons_self)), h4, h5⟩
  exact ⟨hs₄.of_keeps k' (by decide), hc₄.keep (h2 _ (by decide)), h3 ▸ b₄, k', h1,
    h3 ▸ WsOut2.refl _ _ _ _ _ _, by rw [h3, er]; rfl, by rw [h3]; exact congrArg Spec.Ed448.Point.Z eq,
    by rw [h3]; exact ed⟩

/-- In the loop, `n` iterations from its end, which started in `s₄`. -/
def BL (σ s₄ s : State) (n : Nat) : Prop :=
  BMid σ s₄ ∧ CombInv (bsB σ) (kB σ) s₄ s n ∧ FE bsB σ s

/-- `FE` from the loop's invariant, for code keeping it. -/
theorem BL.fin {σ s₄ s t : State} {n m : Nat} (h : BL σ s₄ s n) (ht : CombInv (bsB σ) (kB σ) s₄ t m) :
    FInv (bsB σ) t ∧ t.gpr .esp = s.gpr .esp ∧ t.wr = s.wr :=
  ⟨⟨ht.scr, ht.ctx, ht.bounded⟩, (ht.regs.1 _ (by decide)).trans (h.2.1.regs.1 _ (by decide)).symm,
    ht.regs.2.2.trans h.2.1.regs.2.2.symm⟩

theorem loop_stage {σ s : State} (h : BMid σ s) :
    WP isa Impl.Ed448.X86.combLoop s fun t => BL σ s t 0 :=
  WP.mono (h.fe.wp (NoSp.of_all (by lit_decide)) (by lit_decide)
    (Q := fun t => CombInv (bsB σ) (kB σ) s t 0) (WP.mono (combLoop_ok h.bits h.start) fun t ht =>
      ⟨⟨ht.scr, ht.ctx, ht.bounded⟩, ht.regs.1 _ (by decide), ht.regs.2.2, ht⟩))
    fun t ⟨fe, ht⟩ => ⟨h, ht, fe⟩

theorem step_stage {σ s₄ s : State} {n : Nat} (hn : n < 114) (h : BL σ s₄ s (n + 1)) :
    WP isa Impl.Ed448.X86.combStep s fun t => BL σ s₄ t n ∧ t.zf = some (decide (n = 0)) :=
  WP.mono (h.2.2.wp (NoSp.of_all (by lit_decide)) (by lit_decide)
    (Q := fun t => CombInv (bsB σ) (kB σ) s₄ t n ∧ t.zf = some (decide (n = 0)))
    (WP.mono (combStep_ok hn h.1.bits h.2.1) fun t ⟨ht, z⟩ => ⟨(BL.fin h ht).1, (BL.fin h ht).2.1, (BL.fin h ht).2.2, ht, z⟩))
    fun t ⟨fe, ht, z⟩ => ⟨⟨h.1, ht, fe⟩, z⟩

theorem encode_stage {σ s₄ s : State} (h : BL σ s₄ s 0) :
    WP isa Impl.Ed448.X86.baseEncode s fun t => abiPreserved σ t ∧
      bytesAt t.mem ((arg σ 0).setWidth 64) 57 = Spec.Ed448.encodePoint (comb (kB σ) 114) := by
  obtain ⟨m, hy, fe⟩ := h
  have hp := m.pre
  have hawr : ∀ r ∈ σ.wr ++ [below (σ.gpr .esp) 20], (⟨argAddr σ 0, 4 * 3⟩ : Region).Disjoint r := by
    rw [hp.wr, ← stkR_below hp.sp_room]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.args_out
    · exact hp.args_sc
    · exact hp.stk_args.symm
  refine WP.mono (baseEncode_ok hp.args (by decide) fe.sp (hy.regs.2.1.trans m.rd) fe.wr fe.frame hawr
    fe.fin.scr fe.fin.ctx fe.fin.bounded (by rw [hp.wr]; simp) hp.out_fit hp.out_sc
    (m.saved.wsout2 hy.mem (by decide) (by decide))) fun t ⟨bt, rt, kt, ft⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact rt (.ebx, 0) (by decide)
    · exact rt (.esi, 4) (by decide)
    · exact rt (.edi, 8) (by decide)
    · exact rt (.ebp, 12) (by decide)
    · rw [kt.1 _ (by decide), fe.sp]
  · have ret : (retR σ).Contains ((σ.gpr .esp).setWidth 64) 4 := by
      simpa only [BitVec.add_zero] using
        Offset.contains_base ((σ.gpr .esp).setWidth 64) (d := 0) (n := 4) (k := 4) (by decide)
          (by decide)
    refine (fe.frame.trans ft).readW ret ?_ (by decide)
    rw [hp.wr, ← stkR_below hp.sp_room]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.ret_out
    · exact hp.ret_sc
    · exact hp.stk_ret.symm
  · rw [bt]
    exact congrArg Spec.Ed448.encodePoint hy.r

theorem scalarBase_comb {s₀ : State} (h : BasePre s₀) :
    WP isa scalarBase s₀ fun t => abiPreserved s₀ t ∧
      bytesAt t.mem ((arg s₀ 0).setWidth 64) 57 =
        Spec.Ed448.encodePoint (comb (decodeLE (bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 57)) 114) := by
  unfold scalarBase
  exact WP.seq (WP.mono (entry_stage h) fun _ m => WP.seq (WP.mono (loop_stage m) fun _ l => encode_stage l))

end VG.Proof.Ed448.X86
