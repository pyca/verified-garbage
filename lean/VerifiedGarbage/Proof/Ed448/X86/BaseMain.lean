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
import VerifiedGarbage.Proof.X448.X86.FnVerified
public import VerifiedGarbage.Proof.X448.X86.Bits
import VerifiedGarbage.Proof.Ed448.Scalar
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Framework.Range

/-! ### `Ed448.X86.BaseSetup`, which this module and modules that import it used -/

section

/-!
# Ed448 base-point multiplication on x86 (32-bit): the entry

Every slot `i` set to its initial value `v i` (`initSlots_ok`). Then the
scalar's 57 bytes expanded into its 456 bits at `BITS` (`baseBytes_ok`), by
X448's `bitsLoop`.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Proof.X25519.X86 (num num_succ num_congr)
open VG.Impl.Ed448.X86 (initVal initLimb initStep initSlot zeroSlots initSlots)
open VG.Impl.X448.X86 (slot ACC st BITS bitsLoop at_)
open VG.Spec.Ed448 (bytesAt decodeLE)

/-! ## The slots -/

theorem initVal_lt (i : Nat) : initVal i < Spec.X448.P := by
  unfold initVal
  repeat (first | exact Fin.isLt _ | (split; exact Fin.isLt _) | split)
  decide +kernel

theorem initLimb_lt (v k : Nat) : initLimb v k < 2 ^ 32 := Nat.mod_lt _ (by decide)

theorem num_digits (v : Nat) : ∀ n, num (fun k => v / 2 ^ (32 * k) % 2 ^ 32) n = v % (2 ^ 32) ^ n
  | 0 => by simp [num, Nat.mod_one]
  | n + 1 => by
    rw [num_succ, num_digits v n, Nat.pow_succ (2 ^ 32) n, Nat.mod_mul, ← Nat.pow_mul]

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
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * 16)) (v : Nat) {i k : Nat} (hi : i < 22) (hk : k < 14)
    (hz : limbs s.mem base (slot i) k = 0) :
    WP isa (.block (initStep v i k)) s fun t =>
      limbs t.mem base (slot i) k = initLimb v k ∧ Outside base (slot i + 4 * k) 4 s.mem t.mem ∧
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
        Nat.mod_eq_of_lt (initLimb_lt v k)]
    · rw [ht.mem, hu.mem]; exact writeW_outside _ _ _ (by omega_arith)

theorem initSlot_ok {s : State} {base : Addr} (hs : Scr s base)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * 16)) (v : Nat) {i : Nat}
    (hi : i < 22) (hz : ∀ k < 14, limbs s.mem base (slot i) k = 0) :
    WP isa (.block (initSlot v i)) s fun t =>
      (∀ k < 14, limbs t.mem base (slot i) k = initLimb v k) ∧
        Outside base (slot i) 56 s.mem t.mem ∧ Keeps [.eax] s t := by
  have hsl : slot i + 56 ≤ 4096 := by simp only [slot]; omega_arith
  let inv := fun n (t : State) => (∀ k < n, limbs t.mem base (slot i) k = initLimb v k) ∧
    (∀ k, n ≤ k → k < 14 → limbs t.mem base (slot i) k = 0) ∧
    Outside base (slot i) 56 s.mem t.mem ∧ Keeps [.eax] s t
  refine WP.mono (wp_range_flatMap (M := isa) (N := 14) inv (fun n t hn ⟨tf, t0, tm, tk⟩ => ?_) 14 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun k _ hk => hz k hk, Outside.refl _ _ _ _, Keeps.refl _ _⟩)
    fun t ⟨tf, _, tm, tk⟩ => ⟨tf, tm, tk⟩
  refine WP.mono (initStep_ok (hs.of_keeps tk (by decide))
    (by rw [tk.1 _ (by decide), tk.1 _ (by decide)]; exact hp) v hi hn (t0 n (Nat.le_refl _) hn))
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

theorem initSlots_ok {s : State} {base : Addr} (hs : Scr s base) (v : Nat → Nat) :
    WP isa (initSlots v) s fun t =>
      (∀ i < 22, ∀ k < 14, limbs t.mem base (slot i) k = initLimb (v i) k) ∧
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
  let inv := fun n (t : State) => (∀ i < n, ∀ k < 14, limbs t.mem base (slot i) k = initLimb (v i) k) ∧
    (∀ i, n ≤ i → i < 22 → ∀ k < 14, limbs t.mem base (slot i) k = 0) ∧
    Outside base 64 2816 s.mem t.mem ∧ Keeps [.eax] u t
  have zu : ∀ i, 0 ≤ i → i < 22 → ∀ k < 14, limbs u.mem base (slot i) k = 0 := fun i _ hi k hk => by
    change (Proof.X448.X86.word u.mem base (slot i + 4 * k)).toNat = 0
    rw [mu, show slot i + 4 * k = 64 + 4 * (32 * i + k) by simp only [slot]; omega_arith, z₀ _ (by omega_arith)]
    rfl
  have i0 : inv 0 u := ⟨fun _ h => absurd h (Nat.not_lt_zero _), zu, by rw [mu]; exact o₀, Keeps.refl _ _⟩
  refine WP.mono (wp_range_flatMap (M := isa) (N := 22) inv (fun n t hn ⟨tf, t0, tm, tk⟩ => ?_) 22
    (by decide) u i0)
    fun t ⟨tf, _, tm, tk⟩ => ⟨tf, tm, ku.trans (tk.mono (by simp))⟩
  refine WP.mono (initSlot_ok (hsu.of_keeps tk (by decide))
    (by rw [tk.1 _ (by decide), tk.1 _ (by decide)]; exact hpu) (v n) hn (t0 n (Nat.le_refl _) hn))
    fun v ⟨vf, vm, vk⟩ => ⟨fun i hi k hk => ?_, fun i hi hi' k hk => ?_,
      tm.trans (vm.mono (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith)), tk.trans vk⟩
  · by_cases h : i = n
    · subst h; exact vf k hk
    · rw [vm.limbs (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) hk]
      exact tf i (by omega_arith) k hk
  · rw [vm.limbs (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) hk]
    exact t0 i (by omega_arith) hi' k hk

/-- The slots' values. -/
theorem initSlots_E {m : Mem} {base : Addr} {v : Nat → Nat} (hv : ∀ i, v i < Spec.X448.P)
    (h : ∀ i < 22, ∀ k < 14, limbs m base (slot i) k = initLimb (v i) k) (i : Index) :
    E m base i = Proof.X448.toFe (v i.val) := by
  simp only [E, F, fe]
  rw [num_congr (g := fun k => v i.val / 2 ^ (32 * k) % 2 ^ 32) (h i.val i.isLt), num_digits,
    Nat.mod_eq_of_lt (Nat.lt_trans (hv _) (by decide +kernel))]

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
# Ed448 base-point multiplication on x86 (32-bit): the field programs, and masks

The doubling and addition programs (`Impl/Ed448/Formulas.lean`) as X448's
verified field operations on the slots, and pieces of the comb's selection
(`Proof/Ed448/X86/CombBase.lean`): the mask of an index (`selMask_ok`) and a
word ORed in under it (`sel_word`).
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Proof.X25519.X86 (num num_succ num_congr)
open VG.Impl.Ed448 (doubleOps addOps)
open VG.Impl.Ed448.X86 (toOp selMask zeroSlot takeOps)
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

theorem zeroSlot_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : o + 56 ≤ 4096)
    (h3 : s.gpr .eax = 0) :
    WP isa (.block (zeroSlot o)) s fun t =>
      (∀ j < 14, word t.mem base (o + 4 * j) = 0) ∧ Outside base o 56 s.mem t.mem ∧ Keeps [] s t := by
  let inv := fun n (t : State) =>
    (∀ j < n, word t.mem base (o + 4 * j) = 0) ∧ Outside base o 56 s.mem t.mem ∧ Keeps [] s t
  obtain step : ∀ n t, n < 14 → inv n t → WP isa (.block [st .eax (o + 4 * n)]) t (inv (n + 1)) := by
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
  exact wp_range_flatMap (M := isa) (N := 14) inv step 14 (by decide) s
    ⟨fun _ hj => absurd hj (Nat.not_lt_zero _), Outside.refl _ _ _ _, Keeps.refl _ _⟩

theorem and_mask_true_or (x : BitVec 32) : (x &&& mask true) ||| (0 : BitVec 32) = x := by
  show (x &&& BitVec.allOnes 32) ||| 0 = x
  rw [BitVec.and_allOnes]
  exact BitVec.or_zero

theorem and_mask_false_or (w x : BitVec 32) : (x &&& mask false) ||| w = w := by
  have e : x &&& (0 : BitVec 32) = 0 := BitVec.and_zero
  show (x &&& 0) ||| w = w
  rw [e]
  exact BitVec.zero_or

/-- A word of the selection after entry `n`. -/
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

/-- A slot whose words are the digits of a field element holds it. -/
theorem F_digits {m : Mem} {base : Addr} {o : Nat} (x : Spec.X448.Fe)
    (h : ∀ k < 14, limbs m base o k = x.val / 2 ^ (32 * k) % 2 ^ 32) : F m base o = x := by
  simp only [F, fe]
  rw [num_congr (g := fun k => x.val / 2 ^ (32 * k) % 2 ^ 32) h, num_digits,
    Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide +kernel)), Proof.X448.toFe_self]

end VG.Proof.Ed448.X86

end

end


/-! ## The stack the calls use, and the initial points -/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86
open VG.Proof.Ed448 (pt)
open VG.Impl.Ed448.X86 (initVal)

/-- The stack the calls use, as `below`. -/
theorem stkR_below {s : State} (h : 20 ≤ (s.gpr .esp).toNat) : stkR s = below (s.gpr .esp) 20 := by
  simp only [below]; rw [VG.X86.Taint.sub_setWidth h]

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

end VG.Proof.Ed448.X86
