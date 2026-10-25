module

public import VerifiedGarbage.Proof.Dsa.Arm.CoreBase
import VerifiedGarbage.Proof.Dsa.Arm.ArithCall
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.PowCall
import VerifiedGarbage.Proof.Dsa.Frame
import VerifiedGarbage.Proof.Dsa.Encoding

/-!
# DSA on 32-bit ARM: the arithmetic operations

Each operation sets up a context for a modulus given by its saved pointer
(`setup_ok`), loads its operands, computes, and stores its result's `len`
big-endian bytes at an offset `output` of the working space past the
arithmetic (`power_ok`, `productMod_ok`, `sum_ok`, `reduce_ok`); an
exponentiation loads the modulus and calls `vg_dsa_pow_{n}_{e}`, which sets
up the context itself (`Pow.call_ok`). It changes only the arithmetic and its
output (`Stage`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm VG.Impl.Dsa.Layout
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_str wp_ldr wp_dp wp_movw op2_imm op2_reg dpVal)

/-- What an operation keeps: the registers but `coreClob`, and the memory but
the arithmetic's and the output's. -/
structure Stage (base : Addr) (s t : State) (output len : Nat) : Prop where
  rest : Rest coreClob s t
  mem : Outs base (arithRanges ++ [(output, len)]) s.mem t.mem

theorem Outs.arith_out {base : Addr} {m m' : Mem} (O : Outs base arithRanges m m') (output len : Nat) :
    Outs base (arithRanges ++ [(output, len)]) m m' :=
  O.mono fun _ hr => List.mem_append_left _ hr

theorem Outs.out {base : Addr} {m m' : Mem} {output len : Nat} (O : Outside base output len m m') :
    Outs base (arithRanges ++ [(output, len)]) m m' :=
  Outs.of_outside O (by simp)

/-- A modulus of `len` bytes: its context's size. -/
structure Width (len n : Nat) : Prop where
  n_eq : n = (len + 7) / 8
  four : 4 ≤ len
  max : len ≤ 384
  word : len % 4 = 0

theorem Width.bounds {len n : Nat} (w : Width len n) : 0 < n ∧ n ≤ 48 ∧ len ≤ 8 * n ∧ 8 * n ≤ len + 7 := by
  have := w.n_eq; have := w.four; have := w.max; omega_arith

theorem slot_lt {n i : Nat} (hn : n ≤ 48) (hi : i < 12) : 256 ≤ slot n i ∧ slot n i + 8 * n + 8 ≤ 4960 := by
  have := slot_bound (n := n) hi
  have := contextBytes_le hn
  have := slot_header n i
  simp only [stride] at *
  omega_arith

/-- The modulus's value below `2^(8 len)`. -/
theorem operand_lt (base : Addr) (s : State) (p : Pointer) (len : Nat) :
    operand base s p len < 256 ^ len := by
  have H := decodeBE_lt (Spec.Rsa.bytesAt s.mem (State.addr (pointerValue base s p)) len)
  simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at H
  exact H

theorem pow256_words {len : Nat} (hw : len % 4 = 0) : 256 ^ len = 2 ^ (32 * (len / 4)) := by
  rw [show 32 * (len / 4) = 8 * len by omega_arith, Nat.pow_mul]

/-- The context of the modulus at a saved pointer, without unused constants. -/
theorem setup_ok {s : State} {base : Addr} {size len n m : Nat} {modulus : Field} (hs : Ws s base size)
    (hz : 4960 ≤ size) (w : Width len n) (R : Ready s base (.input modulus) len)
    (hm : operand base s (.input modulus) len = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (Core.setup len modulus) s fun t => Context n m base size t ∧
      Outs base arithRanges s.mem t.mem ∧ Rest coreClob s t := by
  obtain ⟨n0, n48, hl, hl'⟩ := w.bounds
  have s0 := slot_lt (i := 0) n48 (by decide)
  have cb := contextBytes_le n48
  unfold Core.setup
  rw [← w.n_eq]
  refine WP.seq (WP.mono (load_ok (n := n) (dst := modS n) hs (by omega_arith) R (by simp only [modS]; omega_arith)
    (by simp only [modS]; omega_arith) (by omega_arith) w.four hl w.word (by simp only [modS]; omega_arith))
    fun u ⟨wu, Vu, Ru, Ou⟩ => ?_)
  refine WP.mono (Context.light_ok wu (by omega_arith) n0 n48 (by rw [← hm]; exact Vu) hm1 hodd)
    fun t ⟨ct, Ot, Rt⟩ => ⟨ct, ?_, (Ru.mono (by decide)).trans (Rt.mono (by decide))⟩
  exact (Outs.of_slot (i := 0) Ou (by decide) n48).trans (Outs.arith Ot (setupRanges_arith n48))

/-- The result slot of a context, below the modulus, in its `len` bytes. -/
theorem result_bytes {mem : Mem} {base : Addr} {n len m : Nat} (hw : len % 4 = 0) (hl : len ≤ 8 * n)
    (hm : m < 256 ^ len) (hv : val32 mem base (slot n 9) (2 * n) < m) :
    val32 mem base (slot n 9) (len / 4) = val32 mem base (slot n 9) (2 * n) :=
  val32_prefix_of_lt (by omega_arith) (by rw [← pow256_words hw]; omega_arith)

theorem power_ok {s : State} {base : Addr} {size len expLen n m output : Nat} {a b : Pointer} {modulus : Field}
    (hs : Ws s base size) (hz : 4960 ≤ size) (w : Width len n)
    (he4 : 4 ≤ expLen) (he : expLen ≤ len) (hwe : expLen % 4 = 0)
    (Rq : Ready s base (.input modulus) len) (Ra : Ready s base a len) (Rb : Ready s base b expLen)
    (hm : operand base s (.input modulus) len = m) (hm1 : 1 < m) (hodd : m % 2 = 1)
    (ho : 4960 ≤ output) (ho' : output + len ≤ size) (h16o : output < 2 ^ 16) :
    WP isa (Core.power len expLen modulus a b output) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base output) len =
        Spec.Dsa.encodeBE len (operand base s a len ^ operand base s b expLen % m) ∧
      Stage base s t output len := by
  obtain ⟨n0, n48, hl, hl'⟩ := w.bounds
  have s0 := slot_lt (i := 0) n48 (by decide)
  have s8 := slot_lt (i := 8) n48 (by decide)
  have s9 := slot_lt (i := 9) n48 (by decide)
  have s11 := slot_lt (i := 11) n48 (by decide)
  have nw := hs.nowrap
  have cb := contextBytes_le n48
  have mlt : m < 256 ^ len := hm ▸ operand_lt base s _ len
  unfold Core.power
  dsimp only
  rw [← w.n_eq]
  refine WP.seq (WP.mono (load_ok (n := n) (dst := modS n) hs (by omega_arith) Rq (by simp only [modS]; omega_arith)
    (by simp only [modS]; omega_arith) (by omega_arith) w.four hl w.word (by simp only [modS]; omega_arith))
    fun u ⟨wu, Vu, Ru, Ou⟩ => ?_)
  have Ou' := Outs.of_slot (i := 0) Ou (by decide) n48
  have Rau := Ra.keep_rest Ru (O := Ou') (hO := arith_hdr)
  have Rbu := Rb.keep_rest Ru (O := Ou') (hO := arith_hdr)
  refine WP.seq (WP.seq (WP.mono (load_ok (n := n) (dst := baseS n) wu (by omega_arith) Rau
    (by simp only [baseS]; omega_arith) (by simp only [baseS]; omega_arith) (by omega_arith) w.four hl w.word
    (by simp only [baseS]; omega_arith)) fun u₁ ⟨w₁, A₁, R₁, O₁⟩ => ?_))
  have Rb₁ := Rbu.keep_rest R₁ (O := Outs.of_slot (i := 8) O₁ (by decide) n48) (hO := arith_hdr)
  refine WP.mono (load_ok (n := n) (dst := expS n) w₁ (by omega_arith) Rb₁
    (by simp only [expS]; omega_arith) (by simp only [expS]; omega_arith) (by omega_arith) he4 (by omega_arith) hwe
    (by simp only [expS]; omega_arith)) fun u₂ ⟨w₂, B₂, R₂, O₂⟩ => ?_
  have K₂ : Outs base arithRanges s.mem u₂.mem :=
    (Ou'.trans (Outs.of_slot (i := 8) O₁ (by decide) n48)).trans (Outs.of_slot (i := 11) O₂ (by decide) n48)
  have R₂' : Rest coreClob s u₂ := ((Ru.mono (by decide)).trans (R₁.mono (by decide))).trans (R₂.mono (by decide))
  -- The values.
  have M₂ : val32 u₂.mem base (slot n 0) (2 * n) = m := by
    rw [O₂.val32 (by simp only [expS, slot, stride]; omega_arith) (by simp only [slot, stride]; omega_arith),
      O₁.val32 (by simp only [baseS, slot, stride]; omega_arith) (by simp only [slot, stride]; omega_arith)]
    exact Vu.trans hm
  have A₂ : val32 u₂.mem base (slot n 8) (2 * n) = operand base s a len := by
    rw [O₂.val32 (by simp only [expS, slot, stride]; omega_arith) (by simp only [slot, stride]; omega_arith)]
    exact A₁.trans (Ra.arith (Ru.gpr .r12 (by decide)) Ou')
  have B₂' : val32 u₂.mem base (slot n 11) (2 * n) = operand base s b expLen := by
    refine B₂.trans ?_
    rw [operand, pointerValue_keep (R₁.gpr .r12 (by decide)) (Outs.of_slot (i := 8) O₁ (by decide) n48) arith_hdr Rbu.ok,
      Rbu.bytes (Outs.of_slot (i := 8) O₁ (by decide) n48) (by decide)]
    exact Rb.arith (Ru.gpr .r12 (by decide)) Ou'
  have ek : (expLen + 3) / 4 ≤ 2 * n := by omega_arith
  have E₂ : val32 u₂.mem base (slot n 11) ((expLen + 3) / 4) = operand base s b expLen := by
    rw [val32_prefix_of_lt ek (by rw [B₂']; exact decoded_exponent_fits _ _ _), B₂']
  refine WP.seq (WP.mono (Pow.call_ok w₂ (by omega_arith) n0 n48 (by omega_arith) ek M₂ hm1 hodd)
    fun u₃ ⟨w₃, V₃, O₃, R₃⟩ => ?_)
  refine WP.mono (store_ok (output := output) w₃ w.n_eq.symm w.four w.word (by omega_arith) (by omega_arith) ho'
    h16o (by omega_arith)) fun t ⟨Vt, Rt, Ot⟩ => ⟨?_, R₂'.trans ((R₃.mono (by decide)).trans (Rt.mono (by decide))),
      ((Outs.arith_out K₂ _ _).trans (Outs.arith_out (Outs.arith O₃ (scratch_arith n48)) _ _)).trans
        (Outs.out Ot)⟩
  have lt₃ : val32 u₃.mem base (slot n 9) (2 * n) < m := by rw [V₃]; exact Nat.mod_lt _ (by omega_arith)
  rw [Vt, result_bytes w.word hl mlt lt₃, V₃, A₂, E₂]

theorem productMod_ok {s : State} {base : Addr} {size len n m output : Nat} {a b : Pointer} {modulus : Field}
    (hs : Ws s base size) (hz : 4960 ≤ size) (w : Width len n)
    (Rq : Ready s base (.input modulus) len) (Ra : Ready s base a len) (Rb : Ready s base b len)
    (hm : operand base s (.input modulus) len = m) (hm1 : 1 < m) (hodd : m % 2 = 1)
    (ho : 4960 ≤ output) (ho' : output + len ≤ size) (h16o : output < 2 ^ 16) :
    WP isa (Core.productMod len modulus a b output) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base output) len =
        Spec.Dsa.encodeBE len (operand base s a len * operand base s b len % m) ∧
      Stage base s t output len := by
  obtain ⟨n0, n48, hl, hl'⟩ := w.bounds
  have s0 := slot_lt (i := 0) n48 (by decide)
  have s8 := slot_lt (i := 8) n48 (by decide)
  have s9 := slot_lt (i := 9) n48 (by decide)
  have s11 := slot_lt (i := 11) n48 (by decide)
  have nw := hs.nowrap
  have cb := contextBytes_le n48
  have mlt : m < 256 ^ len := hm ▸ operand_lt base s _ len
  unfold Core.productMod
  dsimp only
  rw [← w.n_eq]
  refine WP.seq (WP.mono (load_ok (n := n) (dst := modS n) hs (by omega_arith) Rq (by simp only [modS]; omega_arith)
    (by simp only [modS]; omega_arith) (by omega_arith) w.four hl w.word (by simp only [modS]; omega_arith))
    fun u ⟨wu, Vu, Ru, Ou⟩ => ?_)
  have Ou' := Outs.of_slot (i := 0) Ou (by decide) n48
  have Rau := Ra.keep_rest Ru (O := Ou') (hO := arith_hdr)
  have Rbu := Rb.keep_rest Ru (O := Ou') (hO := arith_hdr)
  refine WP.seq (WP.seq (WP.mono (load_ok (n := n) (dst := baseS n) wu (by omega_arith) Rau
    (by simp only [baseS]; omega_arith) (by simp only [baseS]; omega_arith) (by omega_arith) w.four hl w.word
    (by simp only [baseS]; omega_arith)) fun u₁ ⟨w₁, A₁, R₁, O₁⟩ => ?_))
  have Rb₁ := Rbu.keep_rest R₁ (O := Outs.of_slot (i := 8) O₁ (by decide) n48) (hO := arith_hdr)
  refine WP.mono (load_ok (n := n) (dst := expS n) w₁ (by omega_arith) Rb₁
    (by simp only [expS]; omega_arith) (by simp only [expS]; omega_arith) (by omega_arith) w.four hl w.word
    (by simp only [expS]; omega_arith)) fun u₂ ⟨w₂, B₂, R₂, O₂⟩ => ?_
  have K₂ : Outs base arithRanges s.mem u₂.mem :=
    (Ou'.trans (Outs.of_slot (i := 8) O₁ (by decide) n48)).trans (Outs.of_slot (i := 11) O₂ (by decide) n48)
  have R₂' : Rest coreClob s u₂ := ((Ru.mono (by decide)).trans (R₁.mono (by decide))).trans (R₂.mono (by decide))
  have M₂ : val32 u₂.mem base (slot n 0) (2 * n) = m := by
    rw [O₂.val32 (by simp only [expS, slot, stride]; omega_arith) (by simp only [slot, stride]; omega_arith),
      O₁.val32 (by simp only [baseS, slot, stride]; omega_arith) (by simp only [slot, stride]; omega_arith)]
    exact Vu.trans hm
  have A₂ : val32 u₂.mem base (slot n 8) (2 * n) = operand base s a len := by
    rw [O₂.val32 (by simp only [expS, slot, stride]; omega_arith) (by simp only [slot, stride]; omega_arith)]
    exact A₁.trans (Ra.arith (Ru.gpr .r12 (by decide)) Ou')
  have B₂' : val32 u₂.mem base (slot n 11) (2 * n) = operand base s b len := by
    refine B₂.trans ?_
    rw [operand, pointerValue_keep (R₁.gpr .r12 (by decide)) (Outs.of_slot (i := 8) O₁ (by decide) n48) arith_hdr Rbu.ok,
      Rbu.bytes (Outs.of_slot (i := 8) O₁ (by decide) n48) (by decide)]
    exact Rb.arith (Ru.gpr .r12 (by decide)) Ou'
  refine WP.seq (WP.mono (Pow.mulCall_ok w₂ (by omega_arith) n0 n48 M₂ hm1 hodd) fun u₃ ⟨w₃, V₃, O₃, R₃⟩ => ?_)
  refine WP.mono (store_ok (output := output) w₃ w.n_eq.symm w.four w.word (by omega_arith) (by omega_arith) ho'
    h16o (by omega_arith)) fun t ⟨Vt, Rt, Ot⟩ => ⟨?_, R₂'.trans ((R₃.mono (by decide)).trans (Rt.mono (by decide))),
      ((Outs.arith_out K₂ _ _).trans (Outs.arith_out (Outs.arith O₃ (scratch_arith n48)) _ _)).trans
        (Outs.out Ot)⟩
  have lt₃ : val32 u₃.mem base (slot n 9) (2 * n) < m := by rw [V₃]; exact Nat.mod_lt _ (by omega_arith)
  rw [Vt, result_bytes w.word hl mlt lt₃, V₃, A₂, B₂']

theorem sum_ok {s : State} {base : Addr} {size len n m output : Nat} {a b : Pointer}
    (hs : Ws s base size) (hz : 4960 ≤ size) (w : Width len n)
    (Rq : Ready s base (.input .q) len) (Ra : Ready s base a len) (Rb : Ready s base b len)
    (hm : operand base s (.input .q) len = m) (hm1 : 1 < m) (hodd : m % 2 = 1)
    (hA : operand base s a len < m) (hB : operand base s b len < m)
    (ho : 4960 ≤ output) (ho' : output + len ≤ size) (h16o : output < 2 ^ 16) :
    WP isa (Core.sum len a b output) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base output) len =
        Spec.Dsa.encodeBE len ((operand base s a len + operand base s b len) % m) ∧
      Stage base s t output len := by
  obtain ⟨n0, n48, hl, hl'⟩ := w.bounds
  have s8 := slot_lt (i := 8) n48 (by decide)
  have s9 := slot_lt (i := 9) n48 (by decide)
  have s11 := slot_lt (i := 11) n48 (by decide)
  have nw := hs.nowrap
  have mlt : m < 256 ^ len := hm ▸ operand_lt base s _ len
  unfold Core.sum
  dsimp only
  rw [← w.n_eq]
  refine WP.seq (WP.mono (setup_ok hs hz w Rq hm hm1 hodd) fun u ⟨cu, Ou, Ru⟩ => ?_)
  have Rau := Ra.keep_rest Ru (O := Ou) (hO := arith_hdr)
  have Rbu := Rb.keep_rest Ru (O := Ou) (hO := arith_hdr)
  refine WP.seq (WP.seq (WP.mono (load_ok (n := n) (dst := baseS n) cu.ws (by omega_arith) Rau
    (by simp only [baseS]; omega_arith) (by simp only [baseS]; omega_arith) (by omega_arith) w.four hl w.word
    (by simp only [baseS]; omega_arith)) fun u₁ ⟨w₁, A₁, R₁, O₁⟩ => ?_))
  have c₁ := cu.of_slot w₁ O₁ (by decide)
  have Rb₁ := Rbu.keep_rest R₁ (O := Outs.of_slot (i := 8) O₁ (by decide) n48) (hO := arith_hdr)
  refine WP.mono (load_ok (n := n) (dst := expS n) c₁.ws (by omega_arith) Rb₁
    (by simp only [expS]; omega_arith) (by simp only [expS]; omega_arith) (by omega_arith) w.four hl w.word
    (by simp only [expS]; omega_arith)) fun u₂ ⟨w₂, B₂, R₂, O₂⟩ => ?_
  have c₂ := c₁.of_slot w₂ O₂ (by decide)
  have K₂ : Outs base arithRanges s.mem u₂.mem :=
    (Ou.trans (Outs.of_slot (i := 8) O₁ (by decide) n48)).trans (Outs.of_slot (i := 11) O₂ (by decide) n48)
  have R₂' : Rest coreClob s u₂ := (Ru.trans (R₁.mono (by decide))).trans (R₂.mono (by decide))
  have A₂ : val32 u₂.mem base (slot n 8) (2 * n) = operand base s a len := by
    rw [O₂.val32 (by simp only [expS, slot, stride]; omega_arith) (by simp only [slot, stride]; omega_arith)]
    exact A₁.trans (Ra.arith (Ru.gpr .r12 (by decide)) Ou)
  have B₂' : val32 u₂.mem base (slot n 11) (2 * n) = operand base s b len := by
    refine B₂.trans ?_
    rw [operand, pointerValue_keep (R₁.gpr .r12 (by decide)) (Outs.of_slot (i := 8) O₁ (by decide) n48) arith_hdr Rbu.ok,
      Rbu.bytes (Outs.of_slot (i := 8) O₁ (by decide) n48) (by decide)]
    exact Rb.arith (Ru.gpr .r12 (by decide)) Ou
  refine WP.seq (WP.mono (ordinaryAdd_ok c₂ (by rw [A₂]; exact hA) (by rw [B₂']; exact hB))
    fun u₃ ⟨c₃, K₃, V₃⟩ => ?_)
  refine WP.mono (store_ok (output := output) c₃.ws w.n_eq.symm w.four w.word (by omega_arith) (by omega_arith) ho'
    h16o (by omega_arith)) fun t ⟨Vt, Rt, Ot⟩ => ⟨?_, R₂'.trans ((K₃.rest.mono (by decide)).trans (Rt.mono (by decide))),
      ((Outs.arith_out K₂ _ _).trans (Outs.arith_out (Outs.arith K₃.streamRanges (streamRanges_arith n48)) _ _)).trans
        (Outs.out Ot)⟩
  have lt₃ : val32 u₃.mem base (slot n 9) (2 * n) < m := by rw [V₃]; exact Nat.mod_lt _ (by omega_arith)
  rw [Vt, result_bytes w.word hl mlt lt₃, V₃, A₂, B₂']

/-! ## Reductions -/

/-- The byte count of a reduction. -/
def countValue (base : Addr) (s : State) : Core.Count → Nat
  | .imm len => len
  | .field f => (s.mem.readW (off base (Impl.Dsa.Arm.Layout.field f)) 32).toNat

def CountOk : Core.Count → Prop
  | .imm len => len < 2 ^ 16
  | .field f => f ≠ .mask

theorem countValue_keep {base : Addr} {rs : List (Nat × Nat)} {s t : State} (O : Outs base rs s.mem t.mem)
    (hO : ∀ r ∈ rs, r.1 + r.2 ≤ 64 ∨ 116 ≤ r.1) {c : Core.Count} (hc : CountOk c) :
    countValue base t c = countValue base s c := by
  cases c with
  | imm len => rfl
  | field f => exact congrArg BitVec.toNat (field_keep O hO hc)

/-- `lr = r11 + count`. -/
theorem countEnd_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (hz : 120 ≤ size)
    {c : Core.Count} (hc : CountOk c) :
    WP isa (.block (Core.countEnd c)) s fun t =>
      t.gpr .lr = s.gpr .r11 + BitVec.ofNat 32 (countValue base s c) ∧ Rest [.lr] s t ∧ t.mem = s.mem := by
  cases c with
  | imm len =>
    refine wp_movw fun t₁ u₁ => wp_dp (op2_reg _ _) fun t u₂ => WP.block_nil
      ⟨?_, (u₁.rest (by decide)).trans (u₂.rest (by decide)), by rw [u₂.mem, u₁.mem]⟩
    rw [u₂.gpr, dpVal, u₁.gpr, u₁.other .r11 (by decide), movw_ofNat hc, BitVec.add_comm]
    rfl
  | field f =>
    have := field_bounds f
    refine wp_ldr (by omega_arith) (hs.ea12 (by omega_arith)) (hs.read (by omega_arith)) fun t₁ u₁ => wp_dp (op2_reg _ _) fun t u₂ =>
      WP.block_nil ⟨?_, (u₁.rest (by decide)).trans (u₂.rest (by decide)), by rw [u₂.mem, u₁.mem]⟩
    have e : ∀ x : BitVec 32, BitVec.ofNat 32 x.toNat = x := fun x => by
      apply BitVec.eq_of_toNat_eq; simp
    rw [u₂.gpr, dpVal, u₁.gpr, u₁.other .r11 (by decide), countValue, e, BitVec.add_comm]

theorem _root_.VG.Proof.Mont.Arm.Dyn.Context.of_rest {n m size : Nat} {base : Addr} {rs : List Reg} {s t : State} (h : Context n m base size s)
    (R : Rest rs s t) (h12 : .r12 ∉ rs) (hm : t.mem = s.mem) : Context n m base size t :=
  ⟨h.ws.of_rest R h12, h.size_le, h.small, h.n0, by rw [hm]; exact h.modulus, h.gt_one, by rw [hm]; exact h.inverse⟩

/-- `count` bytes at `input` reduced modulo `q`. -/
theorem reduce_ok {s : State} {base : Addr} {size len n m output : Nat} {count : Core.Count} {input : Pointer}
    (hs : Ws s base size) (hz : 4960 ≤ size) (w : Width len n) (Rq : Ready s base (.input .q) len)
    (hc : CountOk count) (Ri : Ready s base input (countValue base s count))
    (hm : operand base s (.input .q) len = m) (hm255 : 255 < m) (hodd : m % 2 = 1)
    (ho : 4960 ≤ output) (ho' : output + len ≤ size) (h16o : output < 2 ^ 16) :
    WP isa (Core.reduce len count input output) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base output) len =
        Spec.Dsa.encodeBE len (operand base s input (countValue base s count) % m) ∧
      Stage base s t output len := by
  obtain ⟨n0, n48, hl, hl'⟩ := w.bounds
  have s0 := slot_lt (i := 0) n48 (by decide)
  have s9 := slot_lt (i := 9) n48 (by decide)
  have cb := contextBytes_le n48
  have nw := hs.nowrap
  have mlt : m < 256 ^ len := hm ▸ operand_lt base s _ len
  unfold Core.reduce
  dsimp only
  rw [← w.n_eq]
  refine WP.seq (WP.mono (load_ok (n := n) (dst := modS n) hs (by omega_arith) Rq (by simp only [modS]; omega_arith)
    (by simp only [modS]; omega_arith) (by omega_arith) w.four hl w.word (by simp only [modS]; omega_arith))
    fun u ⟨wu, Vu, Ru, Ou⟩ => ?_)
  have Ou' := Outs.of_slot (i := 0) Ou (by decide) n48
  have Riu := Ri.keep_rest Ru (O := Ou') (hO := arith_hdr)
  have Cu := countValue_keep Ou' arith_hdr hc
  rw [← Cu] at Riu
  refine WP.seq (VG.Proof.X25519.Arm.WP.append (pointer_ok wu (by omega_arith) Riu.ok) fun v ⟨Pv, Rv, Mv⟩ =>
    WP.mono (countEnd_ok (wu.of_rest Rv (by decide)) (by omega_arith) hc) fun x ⟨Lx, Rx, Mx⟩ => ?_)
  have Rux : Rest [.r4, .r11, .lr] u x := (Rv.mono (by decide)).trans (Rx.mono (by decide))
  have wx := wu.of_rest Rux (by decide)
  have Cv : countValue base v count = countValue base u count :=
    countValue_keep (rs := []) (fun x _ => by rw [Mv]) (by simp) hc
  have r11 : x.gpr .r11 = pointerValue base u input := by rw [Rx.gpr .r11 (by decide), Pv]
  rw [Cv, Pv] at Lx
  have cl : countValue base s count < 2 ^ 32 := by
    cases count with
    | imm len => exact Nat.lt_trans hc (by decide)
    | field f => exact BitVec.isLt _
  have Vx : val32 x.mem base (slot n 0) (2 * n) = m := by rw [Mx, Mv]; exact Vu.trans hm
  have hrx : InRegions (x.rd ++ x.wr) (State.addr (pointerValue base u input)) (countValue base u count) := by
    have := Riu.reads 0 (countValue base u count) (by omega_arith)
    rw [Rux.rd, Rux.wr]
    simpa only [BitVec.add_zero] using this
  refine WP.seq (WP.mono (Pow.reduceCall_ok wx (by omega_arith) n0 n48 Vx hm255 hodd r11 Lx Riu.fits
    (by rw [Cu]; exact cl) hrx (Riu.apart.sub_right (Region.sub_prefix cb))) fun y ⟨wy, Vy, Oy, Ry⟩ => ?_)
  refine WP.mono (store_ok (output := output) wy w.n_eq.symm w.four w.word (by omega_arith) (by omega_arith) ho'
    h16o (by omega_arith)) fun t ⟨Vt, Rt, Ot⟩ => ⟨?_, ((Ru.mono (by decide)).trans (Rux.mono (by decide))).trans
      ((Ry.mono (by decide)).trans (Rt.mono (by decide))),
      ((Outs.arith_out Ou' _ _).trans (Outs.arith_out (Outs.arith (by rw [Mx, Mv] at Oy; exact Oy)
        (scratch_arith n48)) _ _)).trans (Outs.out Ot)⟩
  have lt : val32 y.mem base (slot n 9) (2 * n) < m := by rw [Vy]; exact Nat.mod_lt _ (by omega_arith)
  rw [Vt, result_bytes w.word hl mlt lt, Vy, Mx, Mv, Cu]
  exact congrArg (fun v => Spec.Dsa.encodeBE len (v % m)) (Ri.arith (Ru.gpr .r12 (by decide)) Ou')

end VG.Proof.Dsa.Arm
