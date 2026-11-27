module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Impl.Rc4.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Rc4.Contract
import VerifiedGarbage.Proof.Rc4.Scratch
import VerifiedGarbage.Proof.Rc4.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Rc4.Contract
meta import VerifiedGarbage.Proof.Rc4.Scratch
meta import VerifiedGarbage.Proof.Rc4.RISCV64.Lit
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rc4.Stream
meta import VerifiedGarbage.Proof.Rc4.Stream
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Impl.Rc4.RISCV64
meta import VerifiedGarbage.Impl.Rc4.RISCV64
public import VerifiedGarbage.Spec.Rc4
meta import VerifiedGarbage.Spec.Rc4
public import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Rc4.Memory
public import VerifiedGarbage.Proof.Rc4.Identity
public import VerifiedGarbage.Proof.Rc4.Schedule
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rc4.Table
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Wp
import VerifiedGarbage.Proof.Rc4.Qword
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Framework.RISCV64.MRun
public meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.TCB.RISCV64.Isa
meta import VerifiedGarbage.Proof.Rc4.Memory
meta import VerifiedGarbage.Proof.Rc4.Identity
meta import VerifiedGarbage.Proof.Rc4.Schedule
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Rc4.Table
meta import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
meta import VerifiedGarbage.Proof.Framework.RISCV64.Wp
meta import VerifiedGarbage.Proof.Rc4.Qword
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.InstancePriority
meta import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.TCB.Mem
meta import VerifiedGarbage.Proof.Framework.RISCV64.Inline
meta import VerifiedGarbage.TCB.RISCV64.Isa

/-! ### `Rc4.RISCV64.Verified`, which only this module used -/

section

/-! ### `Rc4.RISCV64.Init`, which only this module used -/

section

/-! ### `Rc4.RISCV64.Apply`, which this module and modules that import it used -/

section

/-! ### `Rc4.RISCV64.Lookup`, which this module and modules that import it used -/

section

/-! ### `Rc4.Scan64`, which only this module used -/

section

/-!
# RC4: a doubleword scan of the table without compares, step by step

What the 64-bit implementations without compare instructions (RISC-V) hold
after visiting the first doublewords of a scan of the table (`gather`,
`scatter`), and facts about masks, bytes in 64-bit registers, the key
offset and the memory around the context that their proofs share.
-/

@[expose] public section

namespace VG.Proof.Rc4.Scan64
open VG VG.Spec.Rc4 VG.Proof.Rc4

theorem byte_addr (b : Byte) : b.setWidth 64 = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-! ## Masks -/

theorem allOnes_and_ite (p : Prop) [Decidable p] (y : BitVec 64) :
    (if p then BitVec.allOnes 64 else 0#64) &&& y = if p then y else 0#64 := by
  split
  · exact BitVec.allOnes_and
  · exact BitVec.zero_and

theorem and_allOnes_ite (p : Prop) [Decidable p] (y : BitVec 64) :
    y &&& (if p then BitVec.allOnes 64 else 0#64) = if p then y else 0#64 := by
  split
  · exact BitVec.and_allOnes
  · exact BitVec.and_zero

/-! ## The lookup -/

/-- The doubleword holding byte `n`, once doublewords `0, …, k - 1` are visited. -/
def gather (m : Mem) (p : Addr) (n k : Nat) : BitVec 64 :=
  if n / 8 < k then m.readW (p + BitVec.ofNat 64 (8 * (n / 8))) 64 else 0

theorem gather_succ (m : Mem) (p : Addr) (n k : Nat) :
    gather m p n k ||| (if n / 8 = k then m.readW (p + BitVec.ofNat 64 (8 * k)) 64 else 0) =
      gather m p n (k + 1) := by
  unfold gather
  by_cases h0 : n / 8 < k
  · simp [h0, show ¬ n / 8 = k by omega_using [h0], show n / 8 < k + 1 by omega_using [h0]]
  · by_cases h1 : n / 8 = k
    · subst h1; simp
    · simp [h0, h1, show ¬ n / 8 < k + 1 by omega_using [h0, h1]]

theorem flatMap_succ {α : Type} (f : Nat → List α) (n : Nat) :
    (List.range (n + 1)).flatMap f = (List.range n).flatMap f ++ f n := by
  rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-! ## The replacement -/

/-- The memory once doublewords `0, …, k - 1` are stored back, XORed with `d`
where they hold byte `n`. -/
def scatter (m : Mem) (p : Addr) (n : Nat) (d : BitVec 64) (k : Nat) : Mem :=
  if n / 8 < k then
    m.writeW (p + BitVec.ofNat 64 (8 * (n / 8)))
      (m.readW (p + BitVec.ofNat 64 (8 * (n / 8))) 64 ^^^ d)
  else m

theorem scatter_succ (m : Mem) (p : Addr) (n : Nat) (d : BitVec 64) (k : Nat) :
    (scatter m p n d k).writeW (p + BitVec.ofNat 64 (8 * k))
      ((scatter m p n d k).readW (p + BitVec.ofNat 64 (8 * k)) 64 ^^^
        (if n / 8 = k then d else 0#64)) = scatter m p n d (k + 1) := by
  unfold scatter
  by_cases h0 : n / 8 < k
  · rw [ite_eq_left h0, ite_eq_right (show ¬ n / 8 = k by omega_using [h0]), BitVec.xor_zero, writeW_readW,
      ite_eq_left (show n / 8 < k + 1 by omega_using [h0])]
  · rw [ite_eq_right h0]
    by_cases h1 : n / 8 = k
    · rw [ite_eq_left h1, ite_eq_left (show n / 8 < k + 1 by omega_using [h1]), h1]
    · rw [ite_eq_right h1, BitVec.xor_zero, writeW_readW,
        ite_eq_right (show ¬ n / 8 < k + 1 by omega_using [h0, h1])]

theorem xor_byte (a b : Byte) : a.setWidth 64 ^^^ b.setWidth 64 = (a ^^^ b).setWidth 64 := by
  rw [BitVec.setWidth_xor]

/-! ## Bytes in registers -/

theorem low_byte (b : Byte) : (b.setWidth 64).setWidth 8 = b := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

theorem ofNat_low (r : Nat) : (BitVec.ofNat 64 r).setWidth 8 = BitVec.ofNat 8 r := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_using []

theorem low8 (x : BitVec 64) : (x <<< 56) >>> 56 = x &&& BitVec.ofNat 64 255 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_and, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    show (255 % 2 ^ 64 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega_using []

theorem mask255 (x : BitVec 64) : (x <<< 56) >>> 56 = (x.setWidth 8).setWidth 64 := by
  rw [low8]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [show (255 % 2 ^ 64 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega_using []

theorem byte_add (a b : Byte) :
    ((a.setWidth 64 + b.setWidth 64) <<< 56) >>> 56 = (a + b).setWidth 64 := by
  rw [mask255]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  omega_using []

theorem byte_add3 (j a k : Byte) :
    ((j.setWidth 64 + a.setWidth 64 + k.setWidth 64) <<< 56) >>> 56 = (j + a + k).setWidth 64 := by
  rw [mask255]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  omega_using []

theorem byte_inc (i : Byte) :
    ((i.setWidth 64 + 1#64) <<< 56) >>> 56 = (i + 1#8).setWidth 64 := by
  have h := byte_add i 1#8
  rwa [show (1#8).setWidth 64 = 1#64 from rfl] at h

theorem low_xor (a b : Byte) : (a.setWidth 64 ^^^ b.setWidth 64).setWidth 8 = a ^^^ b := by
  rw [xor_byte, low_byte]

/-! ## Counters -/

theorem sub256_ne (j : Nat) (hj : j + 1 < 256) :
    (BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 256 == (0 : BitVec 64)) = false := by
  apply beq_eq_false_iff_ne.mpr
  intro h
  have hh := congrArg BitVec.toNat h
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hh
  change _ = 0 at hh
  omega_using [hj, hh]

theorem len_ne (n : Nat) (hn : n + 1 + 1 < 2 ^ 64) :
    (BitVec.ofNat 64 (n + 1 + 1) - 1#64 == (0 : BitVec 64)) = false := by
  apply beq_eq_false_iff_ne.mpr
  rw [Offset.ofNat_sub_ofNat (by omega_using [])]
  intro hz0
  have hh := congrArg BitVec.toNat hz0
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn])] at hh
  change n + 1 + 1 - 1 = 0 at hh
  omega_using [hh]

theorem valid_length (len : BitVec 64) :
    (len - 1#64) >>> 8 = (0 : BitVec 64) ↔ 1 ≤ len.toNat ∧ len.toNat ≤ 256 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  rw [show BitVec.toNat (0 : BitVec 64) = 0 from rfl]
  omega_using []

/-! ## The key offset -/

/-- The key offset after `o`, advanced to `o + 1` and back to 0 at the key
length `len`, without a branch. -/
def offNext (o len : BitVec 64) : BitVec 64 :=
  (o + 1#64) &&& (((o + 1#64 - len - 1#64) ^^^ (o + 1#64 - len)) >>> 63 - 1#64)

theorem offNext_eq (r : Nat) (len : BitVec 64) (hl : 0 < len.toNat) (hlen : len.toNat ≤ 256) :
    offNext (BitVec.ofNat 64 (r % len.toNat)) len = BitVec.ofNat 64 ((r + 1) % len.toNat) := by
  have hb := Nat.mod_lt r hl
  have ht : (BitVec.ofNat 64 (r % len.toNat) + 1#64).toNat = r % len.toNat + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show r % len.toNat < 2 ^ 64 by omega_using [hb])]
    change (r % len.toNat + 1) % 2 ^ 64 = _
    omega_using [hb]
  have ha : (r + 1) % len.toNat = (r % len.toNat + 1) % len.toNat := by
    simp only [Nat.add_mod, Nat.mod_mod]
  unfold offNext
  by_cases h : r % len.toNat + 1 < len.toNat
  · have hd : ∀ x : BitVec 64, x.toNat = 2 ^ 64 - (len.toNat - (r % len.toNat + 1)) →
        x >>> 63 = 1#64 := by
      intro x hx
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hx]
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      omega_using [hlen, h]
    have h1 : (BitVec.ofNat 64 (r % len.toNat) + 1#64 - len) >>> 63 = 1#64 :=
      hd _ (by rw [BitVec.toNat_sub, ht]; omega_using [h])
    have h2 : (BitVec.ofNat 64 (r % len.toNat) + 1#64 - len - 1#64) >>> 63 = 1#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, BitVec.toNat_sub, ht]
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      omega_using [hlen, hb]
    rw [BitVec.ushiftRight_xor_distrib, h1, h2, show (1#64 ^^^ 1#64) - 1#64 = BitVec.allOnes 64 by
      decide, BitVec.and_allOnes]
    apply BitVec.eq_of_toNat_eq
    rw [ht, BitVec.toNat_ofNat, ha, Nat.mod_eq_of_lt h,
      Nat.mod_eq_of_lt (show r % len.toNat + 1 < 2 ^ 64 by omega_using [hb])]
  · have he : BitVec.ofNat 64 (r % len.toNat) + 1#64 = len := by
      apply BitVec.eq_of_toNat_eq
      rw [ht]; omega_using [hb, h]
    rw [he, BitVec.sub_self, ha, show r % len.toNat + 1 = len.toNat by omega_using [hb, h], Nat.mod_self,
      show (0#64 - 1#64 ^^^ 0#64) >>> 63 - 1#64 = 0#64 by decide, BitVec.and_zero]

end VG.Proof.Rc4.Scan64

end

end


/-! # RC4 on RISC-V: the table lookup, a doubleword at a time -/

@[expose] public section

namespace VG.Proof.Rc4.RISCV64
open VG VG.RISCV64 VG.Impl.Rc4.RISCV64 VG.Proof.Rc4 VG.Proof.Rc4.Scan64

/-- Steps a block of the RC4 code (`mrun`). -/
syntax "rrun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| rrun) => `(tactic| rrun [])
  | `(tactic| rrun [$ls,*]) => `(tactic| mrun [$ls,*])

/-- An 8-byte aligned offset of an 8-byte aligned base. -/
theorem al_add {p : Addr} (hp : p.toNat % 8 = 0) {d : Nat} (hd : d % 8 = 0) (hd' : d < 2 ^ 64) :
    (p + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) hd']
  have := p.isLt
  omega_using [hp, hd]

/-! ## The row's bit and masks -/

/-- Bit `c` of `q` shifted to the top and arithmetically back: all ones if
it is set. -/
theorem bit_mask (q : BitVec 64) {c : Nat} (hc : c < 64) :
    (q <<< (63 - c)).sshiftRight 63 = if q.getLsbD c then BitVec.allOnes 64 else 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_sshiftRight, BitVec.msb_eq_getLsbD_last]
  have key : (q <<< (63 - c)).getLsbD 63 = q.getLsbD c := by
    rw [BitVec.getLsbD_shiftLeft]
    simp only [show (63 : Nat) < 64 by decide, decide_true, Bool.true_and,
      show ¬ (63 < 63 - c) by omega_using [], decide_false, Bool.not_false, show 63 - (63 - c) = c by omega_using [hc]]
  rw [show (if 63 + i < 64 then (q <<< (63 - c)).getLsbD (63 + i) else (q <<< (63 - c)).getLsbD (64 - 1)) =
    (q <<< (63 - c)).getLsbD 63 by split; (congr 1; omega_arith); rfl, key]
  cases q.getLsbD c
  · simp
  · simp only [ite_true, BitVec.getLsbD_allOnes, hi, decide_true, show ¬ 64 ≤ i by omega_using [hi], decide_false,
      Bool.not_false, Bool.and_true]

/-- Doubleword `k`'s mask from the bit of byte `idx`'s doubleword. -/
theorem row_bit (idx : Byte) {k : Nat} (hk : k < 32) :
    (BitVec.twoPow 64 (idx.toNat / 8) <<< (63 - k)).sshiftRight 63 =
      if idx.toNat / 8 = k then BitVec.allOnes 64 else 0#64 := by
  rw [bit_mask _ (by omega_using [hk]), BitVec.getLsbD_twoPow]
  by_cases h : idx.toNat / 8 = k
  · subst h; simp only [ite_true, decide_eq_true (by omega_using [] : idx.toNat / 8 < 64), Bool.true_and, decide_true]
  · simp [h]

theorem rowBit_run (s : State) (idx : Byte) (h4 : s.gpr .a4 = idx.setWidth 64) :
    WP isa (.block rowBit) s fun t => t.gpr .t5 = BitVec.twoPow 64 (idx.toNat / 8) ∧ t.mem = s.mem := by
  have := idx.isLt
  unfold rowBit
  rrun [h4]
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (show idx.toNat < 2 ^ 64 by omega_using []), show (2 : Nat) ^ 3 = 8 from rfl,
    Nat.mod_eq_of_lt (show idx.toNat / 8 < 64 by omega_using [])]
  rfl

/-- The lane's shift: eight times byte `idx`'s offset in its doubleword. -/
theorem lane_shift (idx : Byte) :
    ((idx.setWidth 64 &&& BitVec.ofNat 64 7) <<< 3).toNat % 64 = 8 * (idx.toNat % 8) := by
  have := Nat.mod_lt idx.toNat (by decide : 8 > 0)
  have hi := idx.isLt
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show idx.toNat < 2 ^ 64 by omega_using []), show 7 % 2 ^ 64 = 2 ^ 3 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega_using []),
    Nat.mod_eq_of_lt (by omega_using []), Nat.mul_comm]

theorem laneShift_run (s : State) (idx : Byte) (h4 : s.gpr .a4 = idx.setWidth 64) :
    WP isa (.block laneShift) s fun t => (t.gpr .t2).toNat % 64 = 8 * (idx.toNat % 8) ∧ t.mem = s.mem := by
  unfold laneShift
  rrun [h4]
  exact lane_shift idx

/-! ## Visiting the doublewords -/

theorem gather_step (s : State) (idx : Byte) {k : Nat} (hk : k < 32)
    (h5 : s.gpr .t5 = BitVec.twoPow 64 (idx.toNat / 8)) (hal : (s.gpr .a7).toNat % 8 = 0)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .a7 + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block (gatherStep k)) s fun t =>
      t.gpr .t1 = s.gpr .t1 |||
        (if idx.toNat / 8 = k then s.mem.readW (s.gpr .a7 + BitVec.ofNat 64 (8 * k)) 64 else 0) ∧
      t.gpr .a4 = s.gpr .a4 ∧ t.gpr .t5 = s.gpr .t5 ∧ t.gpr .t6 = s.gpr .t6 ∧ t.gpr .a7 = s.gpr .a7 ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hal' := al_add hal (d := 8 * k) (by omega_using []) (by omega_using [hk])
  unfold gatherStep rowMask
  rrun [h5, hr, hal', show 8 * k < 2048 by omega_using [hk], show 63 - k < 64 by omega_using []]
  rw [row_bit idx hk, and_allOnes_ite]; rfl

def GInv (s₀ : State) (idx : Byte) (k : Nat) (t : State) : Prop :=
  t.gpr .t1 = gather s₀.mem (s₀.gpr .a7) idx.toNat k ∧ t.gpr .a4 = s₀.gpr .a4 ∧
    t.gpr .t5 = s₀.gpr .t5 ∧ t.gpr .t6 = s₀.gpr .t6 ∧ t.gpr .a7 = s₀.gpr .a7 ∧ t.mem = s₀.mem ∧
    t.rd = s₀.rd ∧ t.wr = s₀.wr

theorem gather0_run (s : State) (idx : Byte) (h5 : s.gpr .t5 = BitVec.twoPow 64 (idx.toNat / 8))
    (hal : (s.gpr .a7).toNat % 8 = 0) (hr : InRegions (s.rd ++ s.wr) (s.gpr .a7) 256) :
    WP isa (.block gather0) s (GInv s idx 1) := by
  have hr0 : InRegions (s.rd ++ s.wr) (s.gpr .a7) 8 := by
    simpa using region_offset _ _ 256 0 8 (by omega_using []) (by omega_using []) hr
  unfold gather0 rowMask
  rrun [GInv, h5, hr0, hal]
  rw [row_bit idx (k := 0) (by decide), and_allOnes_ite]
  unfold gather
  by_cases h : idx.toNat / 8 = 0
  · rw [ite_eq_left h, ite_eq_left (by omega_using [h]), h, Nat.mul_zero, BitVec.add_zero]
  · rw [ite_eq_right h, ite_eq_right (by omega_using [h])]; rfl

theorem gather_steps (s₀ : State) (idx : Byte) (h5 : s₀.gpr .t5 = BitVec.twoPow 64 (idx.toNat / 8))
    (hal : (s₀.gpr .a7).toNat % 8 = 0)
    (hr : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .a7) 256) :
    ∀ n ≤ 31, ∀ s, GInv s₀ idx 1 s →
      WP isa (.block ((List.range n).flatMap fun k => gatherStep (k + 1))) s (GInv s₀ idx (n + 1)) := by
  intro n hn
  induction n with
  | zero => intro s h; exact WP.block_nil h
  | succ n ih =>
    intro s h
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hn]) s h) fun t ht => ?_
    obtain ⟨h1, h4', h5', h6', hp, hm, hrd, hwr⟩ := ht
    have hq : InRegions (t.rd ++ t.wr) (t.gpr .a7 + BitVec.ofNat 64 (8 * (n + 1))) 8 := by
      rw [hrd, hwr, hp]
      exact region_offset _ _ _ _ _ (by omega_using [hn]) (by omega_using [hn]) hr
    refine WP.mono (gather_step t idx (by omega_using [hn]) (h5'.trans h5) (by rw [hp]; exact hal) hq) fun u hu => ?_
    obtain ⟨u1, u4, u5, u6, up, um, urd, uwr⟩ := hu
    refine ⟨?_, u4.trans h4', u5.trans h5', u6.trans h6', up.trans hp, um.trans hm, urd.trans hrd,
      uwr.trans hwr⟩
    rw [u1, h1, hp, hm, gather_succ]

/-! ## The lookup -/

theorem lookup_core (s : State) (idx : Byte) (h4 : s.gpr .a4 = idx.setWidth 64)
    (hal : (s.gpr .a7).toNat % 8 = 0)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .a7) 256) :
    WP isa (.block lookup) s fun t =>
      t.gpr .a5 = (s.mem (s.gpr .a7 + BitVec.ofNat 64 idx.toNat)).setWidth 64 ∧
      t.gpr .t5 = BitVec.twoPow 64 (idx.toNat / 8) ∧ t.mem = s.mem := by
  have hn := idx.isLt
  simp only [lookup, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t2, .t5] (rowBit_run s idx h4) (by decide +kernel) rfl)
    fun t ⟨⟨t5, tm⟩, tk⟩ => ?_
  have t4 : t.gpr .a4 = s.gpr .a4 := tk.gpr (by decide)
  have tp : t.gpr .a7 = s.gpr .a7 := tk.gpr (by decide)
  have hrt : InRegions (t.rd ++ t.wr) (t.gpr .a7) 256 := by rw [tk.2.1, tk.2.2, tp]; exact hr
  have halt : (t.gpr .a7).toNat % 8 = 0 := by rw [tp]; exact hal
  rw [WP.block_append_iff]
  refine WP.mono (gather0_run t idx t5 halt hrt) fun u hu => ?_
  rw [WP.block_append_iff]
  refine WP.mono (gather_steps t idx t5 halt hrt 31 (by decide) u hu) fun v hv => ?_
  obtain ⟨v1, v4, v5, _, _, vm, _, _⟩ := hv
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t2] (laneShift_run v idx (v4.trans (t4.trans h4))) (by decide +kernel) rfl)
    fun w ⟨⟨w2, wm⟩, wk⟩ => ?_
  have w1 : w.gpr .t1 = v.gpr .t1 := wk.gpr (by decide)
  have w5 : w.gpr .t5 = v.gpr .t5 := wk.gpr (by decide)
  have hL : idx.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
  rrun [w2, w1, wm, vm, tm, w5, v5, t5]
  rw [v1, tp]
  unfold gather
  rw [ite_eq_left (by omega_using []), qword_byte _ _ hL, row_lane, tm]

end VG.Proof.Rc4.RISCV64

end

end

/-! ### `Rc4.RISCV64.Frame`, which this module and modules that import it used -/

section

/-! # RC4 on RISC-V: the table in the frame

The table is kept in a frame on the stack, copied there from the context
(`table_copy`), and the frame is zeroed before returning (`wipe_ok`). -/

@[expose] public section

namespace VG.Proof.Rc4.RISCV64
open VG VG.RISCV64 VG.Impl.Rc4.RISCV64 VG.Spec.Rc4 VG.Proof.Rc4

/-- A table copied byte for byte. -/
theorem table_copy {m m' : Mem} {p q : Addr}
    (h : ∀ k < 256, m' (q + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) :
    (contextAt m' q).table = (contextAt m p).table := by
  apply Vector.ext
  intro k hk
  simp only [contextAt, Vector.getElem_ofFn]
  exact h k hk

/-- The context, from its table and its two indices. -/
theorem context_of {m : Mem} {p : Addr} {c : Context} (ht : (contextAt m p).table = c.table)
    (hi : m (p + 256#64) = c.i) (hj : m (p + 257#64) = c.j) : contextAt m p = c :=
  context_ext ht hi hj

/-- The doublewords of the frame zeroed. -/
theorem wipe_ok (s : State) (hal : (s.gpr .a7).toNat % 8 = 0)
    (hw : InRegions s.wr (s.gpr .a7) 256) :
    WP isa (.block wipe) s fun t => Frame [⟨s.gpr .a7, 256⟩] s.mem t.mem ∧ t.gpr = s.gpr ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have hw' : wipe = (List.range 32).flatMap fun k => [.store .d .t6 .a7 (8 * k)] := by
    rfl
  rw [hw']
  refine wp_range_flatMap (M := isa) (fun _ t => Frame [⟨s.gpr .a7, 256⟩] s.mem t.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp) (fun k t hk h => ?_) 32
    (Nat.le_refl _) s ⟨Frame.refl _ _, rfl, rfl, rfl, rfl⟩
  obtain ⟨hf, hg, hrd, hwr, hsp⟩ := h
  refine Wp.wp_sd (a := s.gpr .a7 + BitVec.ofNat 64 (8 * k)) (by omega_using [hk]) (by rw [hg])
    (al_add hal (by omega_using []) (by omega_using [hk]))
    (by rw [hwr]; exact region_offset _ _ _ _ _ (by omega_using [hk]) (by omega_using [hk]) hw) fun u hu =>
    WP.block_nil ⟨?_, hu.gpr.trans hg, hu.rd.trans hrd, hu.wr.trans hwr, hu.sp.trans hsp⟩
  rw [hu.mem]
  exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk]))

end VG.Proof.Rc4.RISCV64

end

end

/-! ### `Rc4.RISCV64.Replace`, which this module and modules that import it used -/

section

/-! # RC4 on RISC-V: replacing a secret-indexed byte of the table -/

@[expose] public section

namespace VG.Proof.Rc4.RISCV64
open VG VG.RISCV64 VG.Impl.Rc4.RISCV64 VG.Proof.Rc4 VG.Proof.Rc4.Scan64

/-! ## Storing back every doubleword -/

theorem scatter_step (s : State) (idx : Byte) {k : Nat} (hk : k < 32)
    (h5 : s.gpr .t5 = BitVec.twoPow 64 (idx.toNat / 8)) (hal : (s.gpr .a7).toNat % 8 = 0)
    (hw : InRegions s.wr (s.gpr .a7 + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block (scatterStep k)) s fun t =>
      t.mem = s.mem.writeW (s.gpr .a7 + BitVec.ofNat 64 (8 * k))
        (s.mem.readW (s.gpr .a7 + BitVec.ofNat 64 (8 * k)) 64 ^^^
          (if idx.toNat / 8 = k then s.gpr .t1 else 0#64)) ∧
      t.gpr .t1 = s.gpr .t1 ∧ t.gpr .a4 = s.gpr .a4 ∧ t.gpr .t5 = s.gpr .t5 ∧ t.gpr .t6 = s.gpr .t6 ∧
      t.gpr .a7 = s.gpr .a7 ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .a7 + BitVec.ofNat 64 (8 * k)) 8 := by
    obtain ⟨r, hr, hc⟩ := hw
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hal' := al_add hal (d := 8 * k) (by omega_using []) (by omega_using [hk])
  unfold scatterStep rowMask
  rrun [h5, hr, hw, hal', show 8 * k < 2048 by omega_using [hk], show 63 - k < 64 by omega_using []]
  rw [row_bit idx hk, allOnes_and_ite]

theorem scatter_steps (s₀ : State) (idx : Byte) (d : BitVec 64)
    (h5 : s₀.gpr .t5 = BitVec.twoPow 64 (idx.toNat / 8)) (hal : (s₀.gpr .a7).toNat % 8 = 0)
    (hw : InRegions s₀.wr (s₀.gpr .a7) 256) :
    ∀ n ≤ 32, ∀ s, s.gpr .t1 = d → s.gpr .a4 = s₀.gpr .a4 → s.gpr .t5 = s₀.gpr .t5 →
      s.gpr .t6 = s₀.gpr .t6 → s.gpr .a7 = s₀.gpr .a7 → s.wr = s₀.wr → s.mem = s₀.mem →
      WP isa (.block ((List.range n).flatMap scatterStep)) s fun t =>
        t.mem = scatter s₀.mem (s₀.gpr .a7) idx.toNat d n ∧ t.gpr .t1 = d ∧
        t.gpr .a4 = s₀.gpr .a4 ∧ t.gpr .t5 = s₀.gpr .t5 ∧ t.gpr .t6 = s₀.gpr .t6 ∧
        t.gpr .a7 = s₀.gpr .a7 ∧ t.wr = s₀.wr := by
  intro n hn
  induction n with
  | zero =>
    intro s h1 h4' h5' h6' hp hwr hm
    refine WP.block_nil ⟨?_, h1, h4', h5', h6', hp, hwr⟩
    rw [hm]; unfold scatter; rw [ite_eq_right (Nat.not_lt_zero _)]
  | succ n ih =>
    intro s h1 h4' h5' h6' hp hwr hm
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hn]) s h1 h4' h5' h6' hp hwr hm) fun t ⟨tm, t1, t4, t5, t6, tp, twr⟩ => ?_
    have hq : InRegions t.wr (t.gpr .a7 + BitVec.ofNat 64 (8 * n)) 8 := by
      rw [twr, tp]
      exact region_offset _ _ _ _ _ (by omega_using [hn]) (by omega_using [hn]) hw
    refine WP.mono (scatter_step t idx (by omega_using [hn]) (t5.trans h5) (by rw [tp]; exact hal)
      hq) fun u ⟨um, u1, u4, u5, u6, up, _, uwr⟩ => ?_
    refine ⟨?_, u1.trans t1, u4.trans t4, u5.trans t5, u6.trans t6, up.trans tp, uwr.trans twr⟩
    rw [um, tm, t1, tp, scatter_succ]

/-! ## The replacement -/

theorem replace_core (s : State) (idx ii : Byte) (h4 : s.gpr .a4 = idx.setWidth 64)
    (hcx : s.gpr .a3 = ii.setWidth 64) (hal : (s.gpr .a7).toNat % 8 = 0)
    (hw : InRegions s.wr (s.gpr .a7) 256) :
    WP isa (.block replace) s fun t =>
      t.gpr .a5 = (s.mem (s.gpr .a7 + BitVec.ofNat 64 idx.toNat)).setWidth 64 ∧
      t.mem = s.mem.write (s.gpr .a7 + BitVec.ofNat 64 idx.toNat) 1
        (s.mem (s.gpr .a7 + BitVec.ofNat 64 ii.toNat)) := by
  have hn := idx.isLt
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .a7) 256 := by
    obtain ⟨r, hr, hc⟩ := hw
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hi : InRegions (s.rd ++ s.wr) (s.gpr .a7 + BitVec.ofNat 64 ii.toNat) 1 :=
    region_offset _ _ _ _ _ (by have := ii.isLt; omega_using []) (by have := ii.isLt; omega_using []) hr
  have hit : InRegions (s.rd ++ s.wr) (s.gpr .a7 + ii.setWidth 64) 1 := by
    rw [byte_addr]; exact hi
  let p := s.gpr .a7
  let b := s.mem (p + BitVec.ofNat 64 idx.toNat)
  let v := s.mem (p + BitVec.ofNat 64 ii.toNat)
  simp only [replace, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t0, .a5, .t1, .t2, .t5] (lookup_core s idx h4 hal hr) (by decide +kernel))
    fun t ⟨⟨tax, t5, tm⟩, tk⟩ => ?_
  have t4 : t.gpr .a4 = s.gpr .a4 := tk.gpr (by decide)
  have t6 : t.gpr .t6 = s.gpr .t6 := tk.gpr (by decide)
  have tp : t.gpr .a7 = s.gpr .a7 := tk.gpr (by decide)
  have tcx : t.gpr .a3 = s.gpr .a3 := tk.gpr (by decide)
  rw [← List.append_assoc, WP.block_append_iff]
  have h1 : WP isa (.block (loadI ++ ([.logic .xor .a5 .a5 .t0] : List Instr))) t
      fun u =>
      u.gpr .a5 = (b ^^^ v).setWidth 64 ∧ u.gpr .a4 = s.gpr .a4 ∧ u.gpr .t5 = t.gpr .t5 ∧
        u.gpr .t6 = s.gpr .t6 ∧ u.gpr .a7 = s.gpr .a7 ∧ u.gpr .a3 = s.gpr .a3 ∧ u.mem = s.mem ∧
        u.rd = s.rd ∧ u.wr = s.wr := by
    unfold loadI
    rrun [hit, tax, tm, t4, t6, tp, tcx, tk.2.1, tk.2.2, hcx]
    rw [byte_addr ii, xor_byte]
  refine WP.mono h1 fun u ⟨uax, u4, u5, u6, up, ucx, um, urd, uwr⟩ => ?_
  rw [← List.append_assoc, WP.block_append_iff]
  have hsp : WP isa (.block (laneShift ++ ([.shiftReg .sll .d .t1 .a5 .t2] : List Instr))) u fun w =>
      w.gpr .t1 = (b ^^^ v).setWidth 64 <<< (8 * (idx.toNat % 8)) ∧ w.mem = u.mem := by
    rw [WP.block_append_iff]
    refine WP.mono (WP.keep [.t2] (laneShift_run u idx (u4.trans h4)) (by decide +kernel) rfl)
      fun w ⟨⟨w2, wm⟩, wk⟩ => ?_
    have wax : w.gpr .a5 = u.gpr .a5 := wk.gpr (by decide)
    rrun [w2, wax, uax, wm]
  refine WP.mono (WP.keep [.t1, .t2] hsp (by decide +kernel) rfl) fun w ⟨⟨w1, wm⟩, wk⟩ => ?_
  have wax : w.gpr .a5 = u.gpr .a5 := wk.gpr (by decide)
  have w4 : w.gpr .a4 = s.gpr .a4 := (wk.gpr (by decide)).trans u4
  have w5 : w.gpr .t5 = t.gpr .t5 := (wk.gpr (by decide)).trans u5
  have w6 : w.gpr .t6 = s.gpr .t6 := (wk.gpr (by decide)).trans u6
  have wp : w.gpr .a7 = s.gpr .a7 := (wk.gpr (by decide)).trans up
  have wcx : w.gpr .a3 = s.gpr .a3 := (wk.gpr (by decide)).trans ucx
  have wrd : w.rd = s.rd := wk.2.1.trans urd
  have wwr : w.wr = s.wr := wk.2.2.trans uwr
  rw [← List.append_assoc, WP.block_append_iff]
  have h2 : WP isa (.block (loadI ++ ([.logic .xor .a5 .a5 .t0] : List Instr))) w
      fun x => x.gpr .a5 = b.setWidth 64 ∧ x.gpr .t1 = w.gpr .t1 ∧ x.gpr .a4 = s.gpr .a4 ∧
        x.gpr .t5 = t.gpr .t5 ∧ x.gpr .t6 = s.gpr .t6 ∧ x.gpr .a7 = s.gpr .a7 ∧ x.mem = s.mem ∧
        x.wr = s.wr := by
    unfold loadI
    rrun [hit, wax, uax, wm, um, w4, w5, w6, wp, wcx, wwr, wrd, hcx]
    rw [byte_addr ii, xor_byte, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  refine WP.mono h2 fun x ⟨xax, x1, x4, x5, x6, xp, xm, xwr⟩ => ?_
  refine WP.mono (WP.keep [.t0, .t2]
    (scatter_steps x idx _ (x5.trans t5) (by rw [xp]; exact hal) (by rw [xwr, xp]; exact hw) 32 (by decide) x
      rfl rfl rfl rfl rfl rfl rfl)
    (by decide +kernel)) fun y ⟨⟨ym, _⟩, yk⟩ => ?_
  refine ⟨(yk.gpr (by decide)).trans xax, ?_⟩
  rw [ym, x1, w1, xm, xp]
  unfold scatter
  rw [ite_eq_left (by omega_using []), writeW_byte, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

end VG.Proof.Rc4.RISCV64

end

end

/-! ### `Rc4.RISCV64.ApplyLoop`, which only this module used -/

section

/-! ### `Rc4.RISCV64.ApplyStep`, which only this module used -/

section

/-! # RC4 on RISC-V: one PRGA step, on the table in the frame -/

@[expose] public section

namespace VG.Proof.Rc4.RISCV64
open VG VG.RISCV64 VG.Impl.Rc4.RISCV64 VG.Spec.Rc4 VG.Proof.Rc4 VG.Proof.Rc4.Scan64

/-- `i += 1`, then `j += S[i]`, copied to the index of the replacement. -/
def applyBefore : List Instr :=
  ([.addi .a3 .a3 1, .shift .sll .d .a3 .a3 56, .shift .srl .d .a3 .a3 56] : List Instr) ++ loadI ++
    ([.add .t4 .t4 .t0, .shift .sll .d .t4 .t4 56, .shift .srl .d .t4 .t4 56, .logic .or .a4 .t4 .t4] :
      List Instr)

/-- `S[i] := S[j]` (in `a5`), and the index `S[i] + S[j]` of the keystream byte. -/
def applyMiddle : List Instr :=
  loadI ++ ([.store .b .a5 .t2 0, .add .a4 .a5 .t0, .shift .sll .d .a4 .a4 56,
    .shift .srl .d .a4 .a4 56] : List Instr)

/-- The keystream byte XORed into the data. -/
def applyAfter : List Instr :=
  [.load .b .t0 .a1 0, .logic .xor .t0 .t0 .a5, .store .b .t0 .a1 0, .addi .a1 .a1 1,
    .addi .a2 .a2 (-1)]

theorem applyStep_eq :
    applyStep = applyBefore ++ (replace ++ (applyMiddle ++ (lookup ++ applyAfter))) := by
  simp only [applyStep, applyBefore, applyMiddle, applyAfter, List.append_assoc]

theorem apply_before (s : State) (i j : Byte)
    (hcx : s.gpr .a3 = i.setWidth 64) (h7 : s.gpr .t4 = j.setWidth 64)
    (hp : InRegions (s.rd ++ s.wr) (s.gpr .a7) 256) :
    WP isa (.block applyBefore) s fun t =>
      t.gpr .a3 = (i + 1#8).setWidth 64 ∧
      t.gpr .t4 = (j + s.mem (s.gpr .a7 + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 64 ∧
      t.gpr .a4 = (j + s.mem (s.gpr .a7 + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 64 ∧
      Keep [.t0, .a3, .t4, .a4, .t2] s t ∧ t.mem = s.mem := by
  obtain hi : InRegions (s.rd ++ s.wr) (s.gpr .a7 + (i + 1#8).setWidth 64) 1 := by
    rw [byte_addr (i + 1#8)]
    exact region_offset _ _ _ _ _ (by have := (i + 1#8).isLt; omega_using [])
      (by have := (i + 1#8).isLt; omega_using []) hp
  refine WP.mono (WP.keep (Q := fun t => t.gpr .a3 = (i + 1#8).setWidth 64 ∧
      t.gpr .t4 = (j + s.mem (s.gpr .a7 + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 64 ∧
      t.gpr .a4 = (j + s.mem (s.gpr .a7 + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 64 ∧
      t.mem = s.mem) [.t0, .a3, .t4, .a4, .t2] ?_ (by decide +kernel))
    fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, hk, h.2.2.2⟩
  unfold applyBefore loadI
  rrun [hcx, h7, byte_inc, hi, BitVec.or_self]
  rw [byte_addr (i + 1#8), byte_add]

theorem apply_middle (s : State) (ii b : Byte)
    (hcx : s.gpr .a3 = ii.setWidth 64) (hax : s.gpr .a5 = b.setWidth 64)
    (hw : InRegions s.wr (s.gpr .a7 + BitVec.ofNat 64 ii.toNat) 1) :
    WP isa (.block applyMiddle) s fun t =>
      t.mem = s.mem.write (s.gpr .a7 + BitVec.ofNat 64 ii.toNat) 1 b ∧
      t.gpr .a4 = (b + s.mem (s.gpr .a7 + BitVec.ofNat 64 ii.toNat)).setWidth 64 ∧
      Keep [.t0, .a4, .t2] s t := by
  obtain hw' : InRegions s.wr (s.gpr .a7 + ii.setWidth 64) 1 := by rw [byte_addr ii]; exact hw
  obtain hr : InRegions (s.rd ++ s.wr) (s.gpr .a7 + ii.setWidth 64) 1 := by
    obtain ⟨r, hr, hc⟩ := hw'
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write (s.gpr .a7 + BitVec.ofNat 64 ii.toNat) 1 b ∧
      t.gpr .a4 = (b + s.mem (s.gpr .a7 + BitVec.ofNat 64 ii.toNat)).setWidth 64)
      [.t0, .a4, .t2] ?_ (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h.1, h.2, hk⟩
  unfold applyMiddle loadI
  rrun [hcx, hax, hw', hr, low_byte, byte_add]
  rw [byte_addr ii]
  exact ⟨rfl, rfl⟩

theorem apply_after (s : State) (k : Byte) (hax : s.gpr .a5 = k.setWidth 64)
    (hd : InRegions s.wr (s.gpr .a1) 1) :
    WP isa (.block applyAfter) s fun t =>
      t.mem = s.mem.write (s.gpr .a1) 1 (s.mem (s.gpr .a1) ^^^ k) ∧
      t.gpr .a1 = s.gpr .a1 + 1#64 ∧ t.gpr .a2 = s.gpr .a2 - 1#64 ∧
      Keep [.t0, .a1, .a2] s t := by
  obtain hr : InRegions (s.rd ++ s.wr) (s.gpr .a1) 1 := by
    obtain ⟨r, hr, hc⟩ := hd
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write (s.gpr .a1) 1 (s.mem (s.gpr .a1) ^^^ k) ∧
      t.gpr .a1 = s.gpr .a1 + 1#64 ∧ t.gpr .a2 = s.gpr .a2 - 1#64) [.t0, .a1, .a2] ?_
      (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2, hk⟩
  unfold applyAfter
  rrun [hax, hd, hr, low_xor]

/-- One iteration, with the writes expressed against the original memory.
Both swap operands are read before either write, including for a self-swap. -/
theorem apply_step (s : State) (i j : Byte)
    (hcx : s.gpr .a3 = i.setWidth 64) (h7 : s.gpr .t4 = j.setWidth 64)
    (hal : (s.gpr .a7).toNat % 8 = 0)
    (hp : InRegions s.wr (s.gpr .a7) 256) (hd : InRegions s.wr (s.gpr .a1) 1) :
    let ii := i + 1#8
    let a := s.mem (s.gpr .a7 + BitVec.ofNat 64 ii.toNat)
    let jj := j + a
    let b := s.mem (s.gpr .a7 + BitVec.ofNat 64 jj.toNat)
    let swapped := (s.mem.write (s.gpr .a7 + BitVec.ofNat 64 jj.toNat) 1 a).write
      (s.gpr .a7 + BitVec.ofNat 64 ii.toNat) 1 b
    let k := swapped (s.gpr .a7 + BitVec.ofNat 64 (a + b).toNat)
    WP isa (.block applyStep) s fun t =>
      t.mem = swapped.write (s.gpr .a1) 1 (swapped (s.gpr .a1) ^^^ k) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .a7 = s.gpr .a7 ∧ t.gpr .t6 = s.gpr .t6 ∧
      t.gpr .a0 = s.gpr .a0 ∧
      t.gpr .a1 = s.gpr .a1 + 1#64 ∧ t.gpr .a2 = s.gpr .a2 - 1#64 ∧
      t.gpr .a3 = ii.setWidth 64 ∧ t.gpr .t4 = jj.setWidth 64 := by
  intro ii a jj b swapped k
  obtain hr : InRegions (s.rd ++ s.wr) (s.gpr .a7) 256 := by
    obtain ⟨r, hr, hc⟩ := hp
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  rw [applyStep_eq, WP.block_append_iff]
  refine WP.mono (apply_before s i j hcx h7 hr) fun t ⟨tcx, t7, t9, tk, tm⟩ => ?_
  obtain tp : t.gpr .a7 = s.gpr .a7 := tk.gpr (by decide)
  obtain t0' : t.gpr .a0 = s.gpr .a0 := tk.gpr (by decide)
  obtain t1 : t.gpr .a1 = s.gpr .a1 := tk.gpr (by decide)
  obtain t2 : t.gpr .a2 = s.gpr .a2 := tk.gpr (by decide)
  obtain t6 : t.gpr .t6 = s.gpr .t6 := tk.gpr (by decide)
  obtain htp : InRegions t.wr (t.gpr .a7) 256 := by rw [tk.2.2, tp]; exact hp
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t0, .a5, .t1, .t2, .t5]
    (replace_core t jj ii t9 tcx (by rw [tp]; exact hal) htp)
    (by decide +kernel)) fun u ⟨⟨uax, um⟩, uk⟩ => ?_
  rw [tm, tp] at uax um
  obtain ucx : u.gpr .a3 = ii.setWidth 64 := (uk.gpr (by decide)).trans tcx
  obtain u7 : u.gpr .t4 = jj.setWidth 64 := (uk.gpr (by decide)).trans t7
  obtain up : u.gpr .a7 = s.gpr .a7 := (uk.gpr (by decide)).trans tp
  obtain u0 : u.gpr .a0 = s.gpr .a0 := (uk.gpr (by decide)).trans t0'
  obtain u1 : u.gpr .a1 = s.gpr .a1 := (uk.gpr (by decide)).trans t1
  obtain u2 : u.gpr .a2 = s.gpr .a2 := (uk.gpr (by decide)).trans t2
  obtain u6 : u.gpr .t6 = s.gpr .t6 := (uk.gpr (by decide)).trans t6
  obtain urd : u.rd = s.rd := uk.2.1.trans tk.2.1
  obtain uwr : u.wr = s.wr := uk.2.2.trans tk.2.2
  obtain hw : InRegions u.wr (u.gpr .a7 + BitVec.ofNat 64 ii.toNat) 1 := by
    rw [uwr, up]
    exact region_offset _ _ _ _ _ (by have := ii.isLt; omega_using []) (by have := ii.isLt; omega_using []) hp
  rw [WP.block_append_iff]
  refine WP.mono (apply_middle u ii b ucx uax hw) fun v ⟨vm, v9, vk⟩ => ?_
  obtain ha : u.mem (u.gpr .a7 + BitVec.ofNat 64 ii.toNat) = a := by
    rw [um, up, write_byte]
    split <;> rfl
  rw [ha] at v9
  rw [up, um] at vm
  have hvm : v.mem = swapped := vm
  obtain v9' : v.gpr .a4 = (a + b).setWidth 64 := by rw [v9, BitVec.add_comm]
  obtain vp : v.gpr .a7 = s.gpr .a7 := (vk.gpr (by decide)).trans up
  obtain v6 : v.gpr .t6 = s.gpr .t6 := (vk.gpr (by decide)).trans u6
  obtain vrd : v.rd = s.rd := vk.2.1.trans urd
  obtain vwr : v.wr = s.wr := vk.2.2.trans uwr
  obtain hvp : InRegions (v.rd ++ v.wr) (v.gpr .a7) 256 := by rw [vrd, vwr, vp]; exact hr
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t0, .a5, .t1, .t2, .t5]
    (lookup_core v (a + b) v9' (by rw [vp]; exact hal) hvp)
    (by decide +kernel)) fun w ⟨⟨wax, _, wm⟩, wk⟩ => ?_
  rw [hvm, vp] at wax
  obtain w0 : w.gpr .a0 = s.gpr .a0 := (wk.gpr (by decide)).trans ((vk.gpr (by decide)).trans u0)
  obtain w1 : w.gpr .a1 = s.gpr .a1 := (wk.gpr (by decide)).trans ((vk.gpr (by decide)).trans u1)
  obtain w2 : w.gpr .a2 = s.gpr .a2 := (wk.gpr (by decide)).trans ((vk.gpr (by decide)).trans u2)
  obtain wp : w.gpr .a7 = s.gpr .a7 := (wk.gpr (by decide)).trans vp
  obtain w6 : w.gpr .t6 = s.gpr .t6 := (wk.gpr (by decide)).trans v6
  obtain wrd : w.rd = s.rd := wk.2.1.trans vrd
  obtain wwr : w.wr = s.wr := wk.2.2.trans vwr
  obtain hwd : InRegions w.wr (w.gpr .a1) 1 := by rw [wwr, w1]; exact hd
  refine WP.mono (apply_after w k wax hwd) fun z ⟨zm, z1, z2, zk⟩ => ?_
  refine ⟨?_, zk.2.1.trans wrd, zk.2.2.trans wwr, (zk.gpr (by decide)).trans wp,
    (zk.gpr (by decide)).trans w6, (zk.gpr (by decide)).trans w0, ?_, ?_, ?_, ?_⟩
  · rw [zm, wm, hvm, w1]
  · rw [z1, w1]
  · rw [z2, w2]
  · rw [zk.gpr (by decide), wk.gpr (by decide), vk.gpr (by decide), ucx]
  · rw [zk.gpr (by decide), wk.gpr (by decide), vk.gpr (by decide), u7]

end VG.Proof.Rc4.RISCV64

end

end


/-! # RC4 on RISC-V: the stream loop, on the table in the frame -/

@[expose] public section

namespace VG.Proof.Rc4.RISCV64
open VG VG.RISCV64 VG.Impl.Rc4.RISCV64 VG.Spec.Rc4 VG.Proof.Rc4 VG.Proof.Rc4.Scan64

/-- The concrete stream iteration realizes the abstract PRGA transition. -/
theorem apply_step_table (s : State) (i j : Byte)
    (hcx : s.gpr .a3 = i.setWidth 64) (h7 : s.gpr .t4 = j.setWidth 64)
    (hal : (s.gpr .a7).toNat % 8 = 0)
    (hp : InRegions s.wr (s.gpr .a7) 256) (hd : InRegions s.wr (s.gpr .a1) 1)
    (hs : Mem.Sep (s.gpr .a7) 256 (s.gpr .a1) 1) :
    let next := step { table := (contextAt s.mem (s.gpr .a7)).table, i, j }
    WP isa (.block applyStep) s fun t =>
      (contextAt t.mem (s.gpr .a7)).table = next.1.table ∧
      t.gpr .a3 = next.1.i.setWidth 64 ∧ t.gpr .t4 = next.1.j.setWidth 64 ∧
      t.mem (s.gpr .a1) = s.mem (s.gpr .a1) ^^^ next.2 ∧
      StreamFrame (s.gpr .a7) (s.gpr .a1) 1 s.mem t.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .a7 = s.gpr .a7 ∧ t.gpr .t6 = s.gpr .t6 ∧
      t.gpr .a0 = s.gpr .a0 ∧
      t.gpr .a1 = s.gpr .a1 + 1#64 ∧ t.gpr .a2 = s.gpr .a2 - 1#64 := by
  dsimp only
  rw [step_eq]
  dsimp only
  simp only [table_get]
  have hone : (1 : Byte) = 1#8 := rfl
  simp only [hone]
  refine WP.mono (apply_step s i j hcx h7 hal hp hd) fun t ht => ?_
  obtain ⟨hmem, hrd, hwr, h0, h6', ha0, h1, h2, hi, hj⟩ := ht
  refine ⟨?_, hi, hj, ?_, ?_, hrd, hwr, h0, h6', ha0, h1, h2⟩
  · rw [hmem, table_write_sep _ _ _ _ hs, table_swap]
  · rw [hmem, write_byte, ite_eq_left rfl]
    have hne (idx : Byte) : s.gpr .a1 ≠ s.gpr .a7 + BitVec.ofNat 64 idx.toNat := by
      intro he
      obtain hn := hs (s.gpr .a1) (by rw [he, Mem.sub_ofNat_toNat _ (by omega_using [])]; exact idx.isLt)
      exact hn (by simp [BitVec.sub_self])
    rw [write_byte, ite_eq_right (hne _), write_byte, ite_eq_right (hne _)]
    obtain ht := table_swap s.mem (s.gpr .a7) (i + 1#8)
      (j + s.mem (s.gpr .a7 + BitVec.ofNat 64 (i + 1#8).toNat))
    rw [← ht, table_get]
  · rw [hmem]
    exact stream_frame_step _ _ _ _ _ _

/-- The unconsumed data remains unchanged by a stream iteration. -/
theorem apply_step_tail (s : State) (i j : Byte) (n : Nat)
    (hn : n + 1 < 2 ^ 64)
    (hcx : s.gpr .a3 = i.setWidth 64) (h7 : s.gpr .t4 = j.setWidth 64)
    (hal : (s.gpr .a7).toNat % 8 = 0)
    (hp : InRegions s.wr (s.gpr .a7) 256) (hd : InRegions s.wr (s.gpr .a1) 1)
    (hs : Mem.Sep (s.gpr .a7) 256 (s.gpr .a1) (n + 1)) :
    WP isa (.block applyStep) s fun t =>
      bytesAt t.mem (s.gpr .a1 + 1#64) n = bytesAt s.mem (s.gpr .a1 + 1#64) n := by
  refine WP.mono (apply_step s i j hcx h7 hal hp hd) fun t ht => ?_
  rw [ht.1]
  rw [bytes_write_sep _ _ _ _ _ (by omega_using [hn])
    (sep_symm (Offset.sep_base (s.gpr .a1) (by decide) (by omega_using [hn])))]
  exact bytes_table_frame _ _ _ _ _ (by omega_using [hn]) (swap_frame _ _ _ _)
    (sep_symm (sep_tail hn hs))

structure LoopPost (s : State) (ctx : Context) (n : Nat) (t : State) : Prop where
  table : (contextAt t.mem (s.gpr .a7)).table =
    (update ctx (bytesAt s.mem (s.gpr .a1) n)).1.table
  i : t.gpr .a3 = (update ctx (bytesAt s.mem (s.gpr .a1) n)).1.i.setWidth 64
  j : t.gpr .t4 = (update ctx (bytesAt s.mem (s.gpr .a1) n)).1.j.setWidth 64
  data : bytesAt t.mem (s.gpr .a1) n = (update ctx (bytesAt s.mem (s.gpr .a1) n)).2
  frame : StreamFrame (s.gpr .a7) (s.gpr .a1) n s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  p : t.gpr .a7 = s.gpr .a7
  zero : t.gpr .t6 = s.gpr .t6
  ctx : t.gpr .a0 = s.gpr .a0

/-- Streaming correctness by induction on the public byte count. -/
theorem apply_loop (n : Nat) (s : State) (ctx : Context)
    (hn : n + 1 < 2 ^ 64)
    (htable : (contextAt s.mem (s.gpr .a7)).table = ctx.table)
    (hcx : s.gpr .a3 = ctx.i.setWidth 64) (h7 : s.gpr .t4 = ctx.j.setWidth 64)
    (h6 : s.gpr .t6 = 0#64) (hal : (s.gpr .a7).toNat % 8 = 0)
    (hlen : s.gpr .a2 = BitVec.ofNat 64 (n + 1))
    (hp : InRegions s.wr (s.gpr .a7) 256)
    (hd : InRegions s.wr (s.gpr .a1) (n + 1))
    (hs : Mem.Sep (s.gpr .a7) 256 (s.gpr .a1) (n + 1)) :
    WP isa (.loop (.block applyStep) (.nonzero .a2)) s (LoopPost s ctx (n + 1)) := by
  induction n generalizing s ctx with
  | zero =>
    have hd1 : InRegions s.wr (s.gpr .a1) 1 := hd
    obtain hctx : ({ table := (contextAt s.mem (s.gpr .a7)).table, i := ctx.i, j := ctx.j } :
        Context) = ctx := context_ext htable rfl rfl
    obtain hstep := apply_step_table s ctx.i ctx.j hcx h7 hal hp hd1 hs
    rw [hctx] at hstep
    obtain ⟨tr, t, he, ht⟩ := hstep
    obtain ⟨htab, hti, htj, hbyte, hf, hrd, hwr, hp0, h60, ha0, _, hcount⟩ := ht
    have hbytes (m : Mem) : bytesAt m (s.gpr .a1) 1 = [m (s.gpr .a1)] := by
      simp [bytesAt]
    refine ⟨_, t, .loopExit he ?_, ?_⟩
    · rw [Steps.eval_nonzero, hcount, hlen]
      rfl
    · constructor
      · simpa only [Nat.zero_add, hbytes, update] using htab
      · simpa only [Nat.zero_add, hbytes, update] using hti
      · simpa only [Nat.zero_add, hbytes, update] using htj
      · simp only [Nat.zero_add, hbytes, update, hbyte]
      · exact hf
      · exact hrd
      · exact hwr
      · exact hp0
      · exact h60
      · exact ha0
  | succ n ih =>
    obtain hd1 : InRegions s.wr (s.gpr .a1) 1 := by
      obtain hh := region_offset _ _ _ 0 1 (by decide) (by omega_using []) hd
      simpa only [BitVec.add_zero] using hh
    obtain hs1 : Mem.Sep (s.gpr .a7) 256 (s.gpr .a1) 1 := fun x hx hy => hs x hx (by omega_using [hy])
    obtain hctx : ({ table := (contextAt s.mem (s.gpr .a7)).table, i := ctx.i, j := ctx.j } :
        Context) = ctx := context_ext htable rfl rfl
    obtain hstep := apply_step_table s ctx.i ctx.j hcx h7 hal hp hd1 hs1
    rw [hctx] at hstep
    obtain ⟨tr, t, he, ht⟩ := hstep
    obtain ⟨htab, hti, htj, hbyte, hf, hrd, hwr, hp0, ht6, ha0, hdptr, hcount⟩ := ht
    obtain htail : bytesAt t.mem (s.gpr .a1 + 1#64) (n + 1) =
        bytesAt s.mem (s.gpr .a1 + 1#64) (n + 1) := by
      obtain ⟨_, u, he', hh⟩ := apply_step_tail s ctx.i ctx.j (n + 1) hn hcx h7 hal hp hd1 hs
      obtain ⟨_, rfl⟩ := Exec.det he' he
      exact hh
    obtain htlen : t.gpr .a2 = BitVec.ofNat 64 (n + 1) := by
      rw [hcount, hlen]
      exact Offset.ofNat_sub_ofNat (by omega_using [])
    obtain hpt : InRegions t.wr (t.gpr .a7) 256 := by rw [hwr, hp0]; exact hp
    obtain hdt : InRegions t.wr (t.gpr .a1) (n + 1) := by
      rw [hwr, hdptr]
      exact region_offset _ _ _ 1 (n + 1) (by decide) (by omega_using []) hd
    obtain hst : Mem.Sep (t.gpr .a7) 256 (t.gpr .a1) (n + 1) := by
      rw [hp0, hdptr]
      exact sep_tail hn hs
    obtain htab' : (contextAt t.mem (t.gpr .a7)).table = (step ctx).1.table := by
      rw [hp0]; exact htab
    obtain ⟨tr', u, he', hu⟩ := ih t (step ctx).1 (by omega_using [hn]) htab' hti htj (ht6.trans h6)
      (by rw [hp0]; exact hal) htlen hpt hdt hst
    refine ⟨_, u, .loopNext he ?_ he', ?_⟩
    · rw [Steps.eval_nonzero, hcount, hlen, bne, len_ne n hn]
      rfl
    · have hresult : update ctx (bytesAt s.mem (s.gpr .a1) (n + 1 + 1)) =
          ((update (step ctx).1 (bytesAt t.mem (t.gpr .a1) (n + 1))).1,
            (s.mem (s.gpr .a1) ^^^ (step ctx).2) ::
              (update (step ctx).1 (bytesAt t.mem (t.gpr .a1) (n + 1))).2) := by
        rw [bytes_cons, hdptr, htail]
        rfl
      constructor
      · rw [hresult, ← hp0]; exact hu.table
      · rw [hresult]; exact hu.i
      · rw [hresult]; exact hu.j
      · rw [bytes_cons, hresult]
        obtain hh : u.mem (s.gpr .a1) = t.mem (s.gpr .a1) := by
          have hf' := hu.frame
          rw [hp0, hdptr] at hf'
          exact stream_head _ _ _ _ _ hn hf' hs
        rw [hh, hbyte, ← hdptr, hu.data]
      · have hf' := hu.frame
        rw [hp0, hdptr] at hf'
        exact stream_frame_trans_tail hf hf'
      · exact hu.rd.trans hrd
      · exact hu.wr.trans hwr
      · exact hu.p.trans hp0
      · exact hu.zero.trans ht6
      · exact hu.ctx.trans ha0

end VG.Proof.Rc4.RISCV64

end

end


/-! # RC4 on RISC-V: the stream function

`apply` copies the table into its frame, runs the stream loop there
(`apply_loop`), copies it back with the PRGA indices, and zeroes the frame. -/

@[expose] public section

namespace VG.Proof.Rc4.RISCV64
open VG VG.RISCV64 VG.Impl.Rc4.RISCV64 VG.Spec.Rc4 VG.Proof.Rc4 VG.Proof.Rc4.Scan64

theorem bytes_congr {m m' : Mem} {d : Addr} {n : Nat}
    (h : ∀ i < n, m' (d + BitVec.ofNat 64 i) = m (d + BitVec.ofNat 64 i)) :
    bytesAt m' d n = bytesAt m d n := by
  unfold bytesAt
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

/-- A byte outside the one region of a frame. -/
theorem frame_byte {R : Region} {m m' : Mem} (hf : Frame [R] m m') {x : Addr}
    (hx : ¬ (x - R.base).toNat < R.len) : m' x = m x :=
  hf x fun r hr hc => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact hx (by simp only [Region.Contains] at hc; omega_using [hc])

/-- Copying 256 bytes, from `src` to `dst`, separate. -/
theorem copy256_ok (s : State) {src dst : Reg} (hs : Reg.t0 ≠ src) (hd : Reg.t0 ≠ dst)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr src) 256) (hw : InRegions s.wr (s.gpr dst) 256)
    (hsep : Mem.Sep (s.gpr dst) 256 (s.gpr src) 256) :
    WP isa (.block (Impl.Words.RISCV64.copyBytes .t0 src dst 0 0 256)) s fun t =>
      (∀ k < 256, t.mem (s.gpr dst + BitVec.ofNat 64 k) = s.mem (s.gpr src + BitVec.ofNat 64 k)) ∧
      Frame [⟨s.gpr dst, 256⟩] s.mem t.mem ∧ (∀ r, r ≠ .t0 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  refine WP.mono (Bytes.copyBytes_ok hs hd (by decide) (by decide)
    (fun i hi => by rw [Nat.zero_add]; exact region_offset _ _ _ _ _ (by omega_using [hi]) (by omega_using [hi]) hr)
    (fun i hi => by rw [Nat.zero_add]; exact region_offset _ _ _ _ _ (by omega_using [hi]) (by omega_using [hi]) hw)
    (fun i hi hc => ?_)) fun t ht => ?_
  · simp only [Region.Contains, Nat.zero_add, BitVec.add_zero] at hc
    exact hsep (s.gpr src + BitVec.ofNat 64 i) (by omega_using [hc]) (by rw [Mem.sub_ofNat_toNat _ (by omega_using [hi])]; exact hi)
  · refine ⟨fun k hk => by simpa only [Nat.zero_add] using ht.copied k hk, ?_, ht.gpr, ht.rd,
      ht.wr, ht.sp⟩
    have hf := ht.frame
    simp only [BitVec.add_zero] at hf
    exact hf

theorem apply_start (s : State) (hp : InRegions (s.rd ++ s.wr) (s.gpr .a0) 258) :
    WP isa (.block [.load .b .a3 .a0 256, .load .b .t4 .a0 257, .li .t6 0]) s fun t =>
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.gpr .a0 = s.gpr .a0 ∧ t.gpr .a1 = s.gpr .a1 ∧ t.gpr .a2 = s.gpr .a2 ∧
      t.gpr .a3 = (s.mem (s.gpr .a0 + 256#64)).setWidth 64 ∧
      t.gpr .t4 = (s.mem (s.gpr .a0 + 257#64)).setWidth 64 ∧ t.gpr .t6 = 0#64 := by
  obtain h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  obtain h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  rrun [h256, h257]

/-- Copying the table back to the context with the PRGA indices, and zeroing
the frame. -/
theorem apply_end (s : State) (hal : (s.gpr .a7).toNat % 8 = 0)
    (hF : InRegions s.wr (s.gpr .a7) 256) (hp : InRegions s.wr (s.gpr .a0) 258)
    (hFc : Mem.Sep (s.gpr .a7) 256 (s.gpr .a0) 258) :
    WP isa (.block (Impl.Words.RISCV64.copyBytes .t0 .a7 .a0 0 0 256 ++
      ([.store .b .a3 .a0 256, .store .b .t4 .a0 257] : List Instr) ++ wipe)) s fun t =>
      (∀ k < 256, t.mem (s.gpr .a0 + BitVec.ofNat 64 k) = s.mem (s.gpr .a7 + BitVec.ofNat 64 k)) ∧
      t.mem (s.gpr .a0 + 256#64) = (s.gpr .a3).setWidth 8 ∧
      t.mem (s.gpr .a0 + 257#64) = (s.gpr .t4).setWidth 8 ∧
      ∀ x, ¬ (x - s.gpr .a0).toNat < 258 → ¬ (x - s.gpr .a7).toNat < 256 → t.mem x = s.mem x := by
  obtain hr : InRegions (s.rd ++ s.wr) (s.gpr .a7) 256 := by
    obtain ⟨region, h, hc⟩ := hF
    exact ⟨region, List.mem_append_right _ h, hc⟩
  obtain hw : InRegions s.wr (s.gpr .a0) 256 := by
    simpa only [BitVec.add_zero] using region_offset _ _ _ 0 256 (by decide) (by decide) hp
  obtain hsep : Mem.Sep (s.gpr .a0) 256 (s.gpr .a7) 256 := fun x hx hy => hFc x hy (by omega_using [hx])
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copy256_ok s (by decide) (by decide) hr hw hsep) fun u ⟨uc, uf, ug, urd, uwr, usp⟩ => ?_
  obtain u0 : u.gpr .a0 = s.gpr .a0 := ug _ (by decide)
  obtain u7 : u.gpr .a7 = s.gpr .a7 := ug _ (by decide)
  obtain h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  obtain h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  obtain hb : WP isa (.block [.store .b .a3 .a0 256, .store .b .t4 .a0 257]) u fun v =>
      v.mem = (u.mem.write (s.gpr .a0 + 256#64) 1 ((s.gpr .a3).setWidth 8)).write
        (s.gpr .a0 + 257#64) 1 ((s.gpr .t4).setWidth 8) ∧ v.gpr = u.gpr ∧ v.rd = u.rd ∧
        v.wr = u.wr ∧ v.sp = u.sp := by
    obtain h256' : InRegions u.wr (s.gpr .a0 + BitVec.ofNat 64 256) 1 := by rw [uwr]; exact h256
    obtain h257' : InRegions u.wr (s.gpr .a0 + BitVec.ofNat 64 257) 1 := by rw [uwr]; exact h257
    rrun [h256', h257', u0, ug _ (show Reg.a3 ≠ .t0 by decide), ug _ (show Reg.t4 ≠ .t0 by decide)]
  refine WP.mono hb fun v ⟨vm, vg, vrd, vwr, vsp⟩ => ?_
  obtain v7 : v.gpr .a7 = s.gpr .a7 := by rw [vg, u7]
  refine WP.mono (wipe_ok v (by rw [v7]; exact hal) (by rw [vwr, uwr, v7]; exact hF))
    fun t ⟨tf, _, _, _, _⟩ => ?_
  rw [v7] at tf
  have hne (k : Nat) (hk : k < 256) (e : Nat) (he : 256 ≤ e) (he' : e < 258) :
      s.gpr .a0 + BitVec.ofNat 64 k ≠ s.gpr .a0 + BitVec.ofNat 64 e :=
    Offset.add_ofNat_ne _ (by omega_using [hk]) (by omega_using [he']) (by omega_using [hk, he])
  have hout (k : Nat) (hk : k < 258) : ¬ (s.gpr .a0 + BitVec.ofNat 64 k - s.gpr .a7).toNat < 256 :=
    fun h => hFc _ h (by rw [Mem.sub_ofNat_toNat _ (by omega_using [hk])]; exact hk)
  refine ⟨fun k hk => ?_, ?_, ?_, fun x hx hx' => ?_⟩
  · rw [frame_byte tf (hout k (by omega_using [hk])), vm, write_byte, ite_eq_right (hne k hk 257 (by decide) (by decide)),
      write_byte, ite_eq_right (hne k hk 256 (by decide) (by decide)), uc k hk]
  · rw [frame_byte tf (hout 256 (by decide)), vm, write_byte,
      ite_eq_right (Offset.add_ofNat_ne _ (by decide) (by decide) (by decide)), write_byte, ite_eq_left rfl]
  · rw [frame_byte tf (hout 257 (by decide)), vm, write_byte, ite_eq_left rfl]
  · have h1 : x ≠ s.gpr .a0 + 256#64 := by
      intro he; apply hx; rw [he, Mem.sub_ofNat_toNat _ (by decide)]; decide
    obtain h2 : x ≠ s.gpr .a0 + 257#64 := by
      intro he; apply hx; rw [he, Mem.sub_ofNat_toNat _ (by decide)]; decide
    rw [frame_byte tf hx', vm, write_byte, ite_eq_right h2, write_byte, ite_eq_right h1,
      frame_byte uf (by simp only; omega_using [hx])]

/-- A byte apart from a frame is what it was once the frame's bytes are lost. -/
theorem lost_sep {a b : Addr} {n k : Nat} {m m' : Mem} (f : Frame [⟨a, n⟩] m m') (hs : Mem.Sep a n b k)
    {i : Nat} (hi : i < k) : m' (b + BitVec.ofNat 64 i) = m (b + BitVec.ofNat 64 i) := by
  refine f _ fun r hr hc => ?_
  simp only [List.mem_singleton] at hr; subst hr
  refine hs (b + BitVec.ofNat 64 i) (by simp only [Region.Contains] at hc; omega_using [hc]) ?_
  rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  have := Nat.mod_le i (2 ^ 64)
  omega_using [hi, this]

/-- `applyMain`, with its frame at the stack pointer, from the PRGA indices
loaded. -/
theorem apply_main (s : State) (n : Nat) (hbound : n + 1 < 2 ^ 64)
    (hlen : s.gpr .a2 = BitVec.ofNat 64 (n + 1))
    (h3 : s.gpr .a3 = (s.mem (s.gpr .a0 + 256#64)).setWidth 64)
    (h4 : s.gpr .t4 = (s.mem (s.gpr .a0 + 257#64)).setWidth 64) (h6 : s.gpr .t6 = 0#64)
    (hal : s.sp.toNat % 8 = 0) (hF : InRegions s.wr s.sp 256)
    (hp : InRegions s.wr (s.gpr .a0) 258)
    (hd : InRegions s.wr (s.gpr .a1) (n + 1))
    (hs : Mem.Sep (s.gpr .a0) 258 (s.gpr .a1) (n + 1))
    (hFc : Mem.Sep s.sp 256 (s.gpr .a0) 258)
    (hFd : Mem.Sep s.sp 256 (s.gpr .a1) (n + 1)) :
    WP isa applyMain s fun t =>
      let result := update (contextAt s.mem (s.gpr .a0)) (bytesAt s.mem (s.gpr .a1) (n + 1))
      contextAt t.mem (s.gpr .a0) = result.1 ∧ bytesAt t.mem (s.gpr .a1) (n + 1) = result.2 := by
  obtain hpRead : InRegions (s.rd ++ s.wr) (s.gpr .a0) 258 := by
    obtain ⟨region, hr, hc⟩ := hp
    exact ⟨region, List.mem_append_right _ hr, hc⟩
  unfold applyMain
  refine WP.seq (Wp.wp_addSp (by decide) fun b hb => ?_)
  obtain b7 : b.gpr .a7 = s.sp := by rw [hb.gpr, BitVec.add_zero]
  obtain b0 : b.gpr .a0 = s.gpr .a0 := hb.other _ (by decide)
  obtain hbr : InRegions (b.rd ++ b.wr) (b.gpr .a0) 256 := by
    rw [hb.rd, hb.wr, b0]
    simpa only [BitVec.add_zero] using region_offset _ _ _ 0 256 (by decide) (by decide) hpRead
  refine WP.mono (copy256_ok b (src := .a0) (dst := .a7) (by decide) (by decide) hbr
    (by rw [hb.wr, b7]; exact hF)
    (by rw [b7, b0]; exact fun x hx hy => hFc x hx (by omega_using [hy])))
    fun c ⟨cc, cf, cg, crd, cwr, csp⟩ => ?_
  rw [b7, b0, hb.mem] at cc
  rw [b7, hb.mem] at cf
  obtain c7 : c.gpr .a7 = s.sp := (cg _ (by decide)).trans b7
  obtain c0 : c.gpr .a0 = s.gpr .a0 := (cg _ (by decide)).trans b0
  obtain c1 : c.gpr .a1 = s.gpr .a1 := (cg _ (by decide)).trans (hb.other _ (by decide))
  obtain c2 : c.gpr .a2 = s.gpr .a2 := (cg _ (by decide)).trans (hb.other _ (by decide))
  obtain c3 : c.gpr .a3 = s.gpr .a3 := (cg _ (by decide)).trans (hb.other _ (by decide))
  obtain c4 : c.gpr .t4 = s.gpr .t4 := (cg _ (by decide)).trans (hb.other _ (by decide))
  obtain c6 : c.gpr .t6 = s.gpr .t6 := (cg _ (by decide)).trans (hb.other _ (by decide))
  obtain cw : c.wr = s.wr := by rw [cwr, hb.wr]
  obtain hdata : bytesAt c.mem (s.gpr .a1) (n + 1) = bytesAt s.mem (s.gpr .a1) (n + 1) :=
    bytes_congr fun i hi => frame_byte cf fun h =>
      hFd _ h (by rw [Mem.sub_ofNat_toNat _ (by omega_using [hbound, hi])]; exact hi)
  let ctx := contextAt s.mem (s.gpr .a0)
  refine WP.seq (WP.mono (apply_loop n c ctx hbound
    (by rw [c7]; exact table_copy cc) (c3.trans h3) (c4.trans h4) (c6.trans h6)
    (by rw [c7]; exact hal) (c2.trans hlen)
    (by rw [cw, c7]; exact hF) (by rw [cw, c1]; exact hd) (by rw [c7, c1]; exact hFd))
    fun e he => ?_)
  obtain e7 : e.gpr .a7 = s.sp := he.p.trans c7
  obtain e0 : e.gpr .a0 = s.gpr .a0 := he.ctx.trans c0
  obtain ew : e.wr = s.wr := he.wr.trans cw
  refine WP.mono (apply_end e (by rw [e7]; exact hal) (by rw [ew, e7]; exact hF)
    (by rw [ew, e0]; exact hp) (by rw [e7, e0]; exact hFc)) fun t ⟨ttab, ti, tj, tout⟩ => ?_
  rw [e0, e7] at ttab
  rw [e0] at ti tj tout
  rw [e7] at tout
  have htab := he.table
  have hi := he.i
  have hj := he.j
  have hdat := he.data
  rw [c7] at htab
  rw [c1, hdata] at htab hi hj hdat
  refine ⟨context_of (by rw [table_copy ttab, htab]) (by rw [ti, hi, low_byte])
    (by rw [tj, hj, low_byte]), ?_⟩
  rw [← hdat]
  exact bytes_congr fun i hi => tout _
    (fun h => hs _ h (by rw [Mem.sub_ofNat_toNat _ (by omega_using [hbound, hi])]; exact hi))
    (fun h => hFd _ h (by rw [Mem.sub_ofNat_toNat _ (by omega_using [hbound, hi])]; exact hi))

/-- The stream function, in its frame of 256 bytes below the stack pointer. -/
theorem apply_ok (s : State) (hal : s.sp.toNat % 16 = 0) (hsp : 256 ≤ s.sp.toNat)
    (hp : InRegions s.wr (s.gpr .a0) 258)
    (hd : InRegions s.wr (s.gpr .a1) (s.gpr .a2).toNat)
    (hs : Mem.Sep (s.gpr .a0) 258 (s.gpr .a1) (s.gpr .a2).toNat)
    (hFc : Mem.Sep (s.sp - 256#64) 256 (s.gpr .a0) 258)
    (hFd : Mem.Sep (s.sp - 256#64) 256 (s.gpr .a1) (s.gpr .a2).toNat) :
    WP isa VG.Impl.Rc4.RISCV64.apply s fun t =>
      let result := update (contextAt s.mem (s.gpr .a0))
        (bytesAt s.mem (s.gpr .a1) (s.gpr .a2).toNat)
      contextAt t.mem (s.gpr .a0) = result.1 ∧
        bytesAt t.mem (s.gpr .a1) (s.gpr .a2).toNat = result.2 := by
  obtain hpRead : InRegions (s.rd ++ s.wr) (s.gpr .a0) 258 := by
    obtain ⟨region, hr, hc⟩ := hp
    exact ⟨region, List.mem_append_right _ hr, hc⟩
  unfold VG.Impl.Rc4.RISCV64.apply
  refine WP.seq (WP.mono (apply_start s hpRead) fun a ha => ?_)
  obtain ⟨ham, har, haw, hasp, ha0, ha1, ha2, ha3, ha4, ha6⟩ := ha
  refine WP.ite (s.gpr .a2 == 0) (by rw [Steps.eval_zero, ha2]) (fun hz => ?_) (fun hnz => ?_)
  · have hz' : s.gpr .a2 = 0 := beq_iff_eq.mp hz
    refine WP.block_nil ?_
    simp only [hz', ham]
    exact ⟨context_ext rfl rfl rfl, rfl⟩
  · have hnz' : s.gpr .a2 ≠ 0 := beq_eq_false_iff_ne.mp hnz
    obtain ⟨n, hnEq⟩ := Nat.exists_eq_succ_of_ne_zero (show (s.gpr .a2).toNat ≠ 0 by
      intro h; exact hnz' (BitVec.eq_of_toNat_eq h))
    change (s.gpr .a2).toNat = n + 1 at hnEq
    obtain hbound : n + 1 < 2 ^ 64 := by rw [← hnEq]; exact (s.gpr .a2).isLt
    rw [hnEq]
    rw [hnEq] at hd hs hFd
    obtain hF : (s.sp - 256#64).toNat = s.sp.toNat - 256 := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [hsp])]; rfl
    refine WP.alloc (n := frameBytes) (by decide) (by rw [hasp]; exact hsp) ?_
    obtain hsp' : (allocd frameBytes a).sp = s.sp - 256#64 := by
      show a.sp - BitVec.ofNat 64 256 = _
      rw [hasp]
    have hg : (allocd frameBytes a).gpr = a.gpr := rfl
    have hm : (allocd frameBytes a).mem = a.mem := rfl
    obtain hw : (allocd frameBytes a).wr = ⟨s.sp - 256#64, 256⟩ :: s.wr := by
      show (⟨a.sp - BitVec.ofNat 64 256, 256⟩ :: a.wr : List Region) = _
      rw [hasp, haw]
    have hwr (r : Region) (h : r ∈ s.wr) : r ∈ (allocd frameBytes a).wr := by
      rw [hw]; exact List.mem_cons_of_mem _ h
    refine WP.mono (apply_main (allocd frameBytes a) n hbound
      (by rw [hg, ha2, ← hnEq, BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (by rw [hg, hm, ha3, ha0, ham]) (by rw [hg, hm, ha4, ha0, ham]) (by rw [hg, ha6])
      (by rw [hsp', hF]; omega_using [hal])
      ⟨⟨s.sp - 256#64, 256⟩, by rw [hw]; exact List.mem_cons_self,
        by rw [hsp']; exact Region.contains_self _ _⟩
      (by obtain ⟨r, hr, hc⟩ := hp; exact ⟨r, hwr r hr, by rw [hg, ha0]; exact hc⟩)
      (by obtain ⟨r, hr, hc⟩ := hd; exact ⟨r, hwr r hr, by rw [hg, ha1]; exact hc⟩)
      (by rw [hg, ha0, ha1]; exact hs) (by rw [hsp', hg, ha0]; exact hFc)
      (by rw [hsp', hg, ha1]; exact hFd)) fun u hu m _ fl => ?_
    rw [hg, hm, ha0, ha1, ham] at hu
    -- The `free` loses the frame's bytes, which lie apart from the context and the data.
    have fl' : Frame [⟨s.sp - 256#64, 256⟩] u.mem m := by rw [← hasp]; exact fl
    exact ⟨(Proof.Rc4.contextAt_congr fun i hi => lost_sep fl' hFc hi).trans hu.1,
      (List.map_congr_left fun i hi => lost_sep fl' hFd (List.mem_range.mp hi)).trans hu.2⟩

end VG.Proof.Rc4.RISCV64

end

end

/-! ### `Rc4.RISCV64.Schedule`, which only this module used -/

section

/-! # RC4 on RISC-V: key scheduling, in the frame -/

@[expose] public section

namespace VG.Proof.Rc4.RISCV64
open VG VG.RISCV64 VG.Impl.Rc4.RISCV64 VG.Spec.Rc4 VG.Proof.Rc4 VG.Proof.Rc4.Scan64

/-! ## The identity permutation -/

def IdentityInv (s₀ : State) (r : Nat) (s : State) : Prop :=
  s.mem = identityMem s₀.mem (s₀.gpr .a7) r ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
    s.gpr .a7 = s₀.gpr .a7 ∧ s.gpr .a0 = s₀.gpr .a0 ∧ s.gpr .a1 = s₀.gpr .a1 ∧
    s.gpr .a2 = s₀.gpr .a2 ∧ s.gpr .a3 = BitVec.ofNat 64 r

theorem identity_step (s₀ s : State) {r : Nat} (hr : r < 256)
    (hp : InRegions s₀.wr (s₀.gpr .a7) 256) (h : IdentityInv s₀ r s) :
    WP isa (.block identityStep) s fun t => IdentityInv s₀ (r + 1) t ∧
      t.gpr .t2 = BitVec.ofNat 64 (r + 1) - BitVec.ofNat 64 256 := by
  obtain ⟨hm, hrd, hwr, hp7, h0, h1, h2, h3⟩ := h
  have hw : InRegions s₀.wr (s₀.gpr .a7 + BitVec.ofNat 64 r) 1 :=
    region_offset _ _ _ _ _ (by omega_using [hr]) (by omega_using [hr]) hp
  have hadd : BitVec.ofNat 64 r + 1#64 = BitVec.ofNat 64 (r + 1) := by
    rw [BitVec.ofNat_add]
  unfold identityStep
  rrun [hw, hm, hrd, hwr, hp7, h0, h1, h2, h3, hadd, ofNat_low, IdentityInv]
  exact identityMem_store _ _ _ hr

theorem identity_loop (s₀ s : State) {r : Nat} (hr : r < 256)
    (hp : InRegions s₀.wr (s₀.gpr .a7) 256) (h : IdentityInv s₀ r s) :
    WP isa (.loop (.block identityStep) (.nonzero .t2)) s (IdentityInv s₀ 256) := by
  refine WP.loop (M := isa) (fun rem t => ∃ j, j < 256 ∧ rem = 256 - j ∧ IdentityInv s₀ j t)
    ?_ (256 - r) s ⟨r, hr, rfl, h⟩
  intro rem t ⟨j, hj, hrem, ht⟩
  refine WP.mono (identity_step s₀ t hj hp ht) fun u ⟨hu, hz⟩ => ?_
  by_cases hend : j + 1 = 256
  · left
    refine ⟨?_, hend ▸ hu⟩
    rw [Steps.eval_nonzero, hz, hend]
    rfl
  · right
    refine ⟨?_, 256 - (j + 1), by omega_using [hj, hrem], j + 1, by omega_using [hj, hend], rfl, hu⟩
    rw [Steps.eval_nonzero, hz, bne, sub256_ne j (by omega_using [hj, hend])]
    rfl

/-! ## One round -/

theorem schedule_before (s : State) (i j : Byte)
    (hcx : s.gpr .a3 = i.setWidth 64) (h4 : s.gpr .a4 = j.setWidth 64)
    (hp : InRegions (s.rd ++ s.wr) (s.gpr .a7) 256)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .a0 + s.gpr .t3) 1) :
    WP isa (.block (loadI ++ ([.add .a4 .a4 .t0, .add .t2 .a0 .t3, .load .b .t0 .t2 0,
      .add .a4 .a4 .t0, .shift .sll .d .a4 .a4 56, .shift .srl .d .a4 .a4 56] : List Instr))) s
      fun t => t.gpr .a4 = (j + s.mem (s.gpr .a7 + BitVec.ofNat 64 i.toNat) +
          s.mem (s.gpr .a0 + s.gpr .t3)).setWidth 64 ∧ Keep [.t0, .a4, .t2] s t ∧
        t.mem = s.mem := by
  have hi : InRegions (s.rd ++ s.wr) (s.gpr .a7 + s.gpr .a3) 1 := by
    rw [hcx, byte_addr i]
    exact region_offset _ _ _ _ _ (by have := i.isLt; omega_using []) (by have := i.isLt; omega_using []) hp
  refine WP.mono (WP.keep (Q := fun t => t.gpr .a4 = (j + s.mem (s.gpr .a7 + BitVec.ofNat 64 i.toNat) +
      s.mem (s.gpr .a0 + s.gpr .t3)).setWidth 64 ∧ t.mem = s.mem) [.t0, .a4, .t2] ?_
      (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h.1, hk, h.2⟩
  unfold loadI
  rrun [hi, hk, h4]
  rw [hcx, byte_addr i, byte_add3]

theorem schedule_after (s : State) (i b : Byte)
    (hcx : s.gpr .a3 = i.setWidth 64) (hax : s.gpr .a5 = b.setWidth 64)
    (hw : InRegions s.wr (s.gpr .a7 + BitVec.ofNat 64 i.toNat) 1) :
    WP isa (.block [.add .t2 .a7 .a3, .store .b .a5 .t2 0,
      .addi .t3 .t3 1, .sub .t2 .t3 .a1, .addi .t0 .t2 (-1), .logic .xor .t0 .t0 .t2,
      .shift .srl .d .t2 .t0 63, .addi .t2 .t2 (-1), .logic .and .t3 .t3 .t2,
      .addi .a3 .a3 1, .li .t2 256, .sub .t2 .a3 .t2]) s fun t =>
      t.mem = s.mem.write (s.gpr .a7 + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .t3 = offNext (s.gpr .t3) (s.gpr .a1) ∧
      t.gpr .a3 = i.setWidth 64 + 1#64 ∧
      t.gpr .t2 = i.setWidth 64 + 1#64 - BitVec.ofNat 64 256 ∧
      Keep [.t0, .t3, .a3, .t2] s t := by
  have hw' : InRegions s.wr (s.gpr .a7 + s.gpr .a3) 1 := by rw [hcx, byte_addr i]; exact hw
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write (s.gpr .a7 + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .t3 = offNext (s.gpr .t3) (s.gpr .a1) ∧
      t.gpr .a3 = i.setWidth 64 + 1#64 ∧
      t.gpr .t2 = i.setWidth 64 + 1#64 - BitVec.ofNat 64 256) [.t0, .t3, .a3, .t2] ?_
    (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hk⟩
  rrun [hw', hax, low_byte, offNext]
  rw [hcx, byte_addr i]
  exact ⟨rfl, rfl, rfl⟩

/-- One key-scheduling round, with both swap operands read before either write. -/
theorem schedule_step (s : State) (i j : Byte)
    (hcx : s.gpr .a3 = i.setWidth 64) (h4 : s.gpr .a4 = j.setWidth 64)
    (hal : (s.gpr .a7).toNat % 8 = 0) (hp : InRegions s.wr (s.gpr .a7) 256)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .a0 + s.gpr .t3) 1) :
    let a := s.mem (s.gpr .a7 + BitVec.ofNat 64 i.toNat)
    let jj := j + a + s.mem (s.gpr .a0 + s.gpr .t3)
    let b := s.mem (s.gpr .a7 + BitVec.ofNat 64 jj.toNat)
    WP isa (.block scheduleStep) s fun t =>
      t.mem = (s.mem.write (s.gpr .a7 + BitVec.ofNat 64 jj.toNat) 1 a).write
        (s.gpr .a7 + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .t3 = offNext (s.gpr .t3) (s.gpr .a1) ∧
      t.gpr .a4 = jj.setWidth 64 ∧ t.gpr .a3 = i.setWidth 64 + 1#64 ∧
      t.gpr .t2 = i.setWidth 64 + 1#64 - BitVec.ofNat 64 256 ∧
      Keep ([.t0, .a4, .t2] ++ [.t0, .a5, .t1, .t2, .t5] ++ [.t0, .t3, .a3, .t2]) s t := by
  intro a jj b
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .a7) 256 := by
    obtain ⟨r, hr, hc⟩ := hp
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  unfold scheduleStep
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (schedule_before s i j hcx h4 hr hk) fun t ⟨t4, tk, tm⟩ => ?_
  have tcx : t.gpr .a3 = i.setWidth 64 := (tk.gpr (by decide)).trans hcx
  have tp : t.gpr .a7 = s.gpr .a7 := tk.gpr (by decide)
  have tr3 : t.gpr .t3 = s.gpr .t3 := tk.gpr (by decide)
  have tr1 : t.gpr .a1 = s.gpr .a1 := tk.gpr (by decide)
  have htp : InRegions t.wr (t.gpr .a7) 256 := by rw [tk.2.2, tp]; exact hp
  refine WP.mono (WP.keep [.t0, .a5, .t1, .t2, .t5]
    (replace_core t jj i t4 tcx (by rw [tp]; exact hal) htp)
    (by decide +kernel)) fun u ⟨⟨uax, um⟩, uk⟩ => ?_
  have ucx : u.gpr .a3 = i.setWidth 64 := (uk.gpr (by decide)).trans tcx
  have up : u.gpr .a7 = s.gpr .a7 := (uk.gpr (by decide)).trans tp
  have ur3 : u.gpr .t3 = s.gpr .t3 := (uk.gpr (by decide)).trans tr3
  have ur1 : u.gpr .a1 = s.gpr .a1 := (uk.gpr (by decide)).trans tr1
  have u4 : u.gpr .a4 = jj.setWidth 64 := (uk.gpr (by decide)).trans t4
  rw [tm, tp] at uax um
  have hw : InRegions u.wr (u.gpr .a7 + BitVec.ofNat 64 i.toNat) 1 := by
    rw [uk.2.2, tk.2.2, up]
    exact region_offset _ _ _ _ _ (by have := i.isLt; omega_using []) (by have := i.isLt; omega_using []) hp
  refine WP.mono (schedule_after u i b ucx uax hw) fun v ⟨vm, v3, vcx, vz, vk⟩ => ?_
  refine ⟨?_, ?_, (vk.gpr (by decide)).trans u4, vcx, vz, (tk.trans uk).trans vk⟩
  · rw [vm, um, up]
  · rw [v3, ur3, ur1]

/-- The key bytes, from the key pointer and length of a state. -/
def keyAt (s : State) : List Byte := bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat

structure ScheduleInv (s₀ : State) (r : Nat) (s : State) : Prop where
  frame : TableFrame (s₀.gpr .a7) s₀.mem s.mem
  table : (contextAt s.mem (s₀.gpr .a7)).table = (schedulePrefix (keyAt s₀) r).1
  j : s.gpr .a4 = (schedulePrefix (keyAt s₀) r).2.setWidth 64
  i : s.gpr .a3 = BitVec.ofNat 64 r
  off : s.gpr .t3 = BitVec.ofNat 64 (r % (s₀.gpr .a1).toNat)
  p : s.gpr .a7 = s₀.gpr .a7
  len : s.gpr .a1 = s₀.gpr .a1
  key : s.gpr .a0 = s₀.gpr .a0
  ctx : s.gpr .a2 = s₀.gpr .a2
  zero : s.gpr .t6 = 0#64
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem schedule_inv_step (s₀ s : State) {r : Nat} (hr : r < 256)
    (hlen : 1 ≤ (s₀.gpr .a1).toNat ∧ (s₀.gpr .a1).toNat ≤ 256)
    (hal : (s₀.gpr .a7).toNat % 8 = 0) (hp : InRegions s₀.wr (s₀.gpr .a7) 256)
    (hk : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .a0) (s₀.gpr .a1).toNat)
    (hs : Mem.Sep (s₀.gpr .a0) (s₀.gpr .a1).toNat (s₀.gpr .a7) 256)
    (h : ScheduleInv s₀ r s) :
    WP isa (.block scheduleStep) s fun t => ScheduleInv s₀ (r + 1) t ∧
      t.gpr .t2 = BitVec.ofNat 64 (r + 1) - BitVec.ofNat 64 256 := by
  let key := keyAt s₀
  let st := schedulePrefix key r
  have hrt : (BitVec.ofNat 8 r).toNat = r := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  have hi : s.gpr .a3 = (BitVec.ofNat 8 r).setWidth 64 := by
    rw [h.i, byte_addr, hrt]
  have hpoint : InRegions s.wr (s.gpr .a7) 256 := by rw [h.wr, h.p]; exact hp
  have hmod := Nat.mod_lt r (show 0 < (s₀.gpr .a1).toNat by omega_using [hlen])
  have hkeypoint : InRegions (s.rd ++ s.wr) (s.gpr .a0 + s.gpr .t3) 1 := by
    rw [h.rd, h.wr, h.key, h.off]
    exact region_offset _ _ _ _ _ (by omega_using [hmod]) (by omega_using [hmod]) hk
  have hkeybyte : s.mem (s.gpr .a0 + s.gpr .t3) = key.getD (r % key.length) 0 := by
    rw [h.key, h.off]
    have hsep := hs (s₀.gpr .a0 + BitVec.ofNat 64 (r % (s₀.gpr .a1).toNat))
      (by rw [Mem.sub_ofNat_toNat _ (by omega_using [hmod])]; exact hmod)
    rw [h.frame _ hsep]
    dsimp only [key, keyAt]
    rw [bytes_length, bytes_get _ _ _ _ hmod]
  have htablebyte : s.mem (s.gpr .a7 + BitVec.ofNat 64 r) = st.1.getD r 0 := by
    rw [h.p]
    have hg := table_get s.mem (s₀.gpr .a7) (BitVec.ofNat 8 r)
    rw [hrt, h.table] at hg
    exact hg.symm
  refine WP.mono (schedule_step s _ _ hi h.j (by rw [h.p]; exact hal) hpoint hkeypoint)
    fun t ⟨tm, t3, t4, tcx, tz, tk⟩ => ?_
  have hnext := schedule_succ key r
  dsimp only [scheduleRound] at hnext
  have hcast : (BitVec.ofNat 8 r).setWidth 64 + 1#64 = BitVec.ofNat 64 (r + 1) := by
    rw [byte_addr, hrt, BitVec.ofNat_add]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, (tk.gpr (by decide)).trans h.p, (tk.gpr (by decide)).trans h.len,
    (tk.gpr (by decide)).trans h.key, (tk.gpr (by decide)).trans h.ctx,
    (tk.gpr (by decide)).trans h.zero, tk.2.1.trans h.rd, tk.2.2.trans h.wr⟩, ?_⟩
  · rw [tm, h.p]
    exact h.frame.trans (swap_frame _ _ _ _)
  · rw [tm, h.p, table_swap, h.table, hnext, hrt]
    have hb := htablebyte
    rw [h.p] at hb
    rw [hb, hkeybyte]
  · rw [t4, hrt, htablebyte, hkeybyte, hnext]
  · rw [tcx, hcast]
  · rw [t3, h.off, h.len]
    exact offNext_eq r _ (by omega_using [hlen]) hlen.2
  · rw [tz, hcast]

/-- All 256 scheduling rounds realize the complete specified permutation. -/
theorem schedule_loop (s₀ s : State) {r : Nat} (hr : r < 256)
    (hlen : 1 ≤ (s₀.gpr .a1).toNat ∧ (s₀.gpr .a1).toNat ≤ 256)
    (hal : (s₀.gpr .a7).toNat % 8 = 0) (hp : InRegions s₀.wr (s₀.gpr .a7) 256)
    (hk : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .a0) (s₀.gpr .a1).toNat)
    (hs : Mem.Sep (s₀.gpr .a0) (s₀.gpr .a1).toNat (s₀.gpr .a7) 256)
    (h : ScheduleInv s₀ r s) :
    WP isa (.loop (.block scheduleStep) (.nonzero .t2)) s (ScheduleInv s₀ 256) := by
  refine WP.loop (M := isa) (fun rem t => ∃ j, j < 256 ∧ rem = 256 - j ∧ ScheduleInv s₀ j t)
    ?_ (256 - r) s ⟨r, hr, rfl, h⟩
  intro rem t ⟨j, hj, hrem, ht⟩
  refine WP.mono (schedule_inv_step s₀ t hj hlen hal hp hk hs ht) fun u ⟨hu, hz⟩ => ?_
  by_cases hend : j + 1 = 256
  · left
    refine ⟨?_, hend ▸ hu⟩
    rw [Steps.eval_nonzero, hz, hend]
    rfl
  · right
    refine ⟨?_, 256 - (j + 1), by omega_using [hj, hrem], j + 1, by omega_using [hj, hend], rfl, hu⟩
    rw [Steps.eval_nonzero, hz, bne, sub256_ne j (by omega_using [hj, hend])]
    rfl

end VG.Proof.Rc4.RISCV64

end

end


/-! # RC4 on RISC-V: checked initialization

`init` builds the table in its frame (`identity_loop`, `schedule_loop`),
copies it to the context with two zero PRGA indices, and zeroes the frame. -/

@[expose] public section

namespace VG.Proof.Rc4.RISCV64
open VG VG.RISCV64 VG.Impl.Rc4.RISCV64 VG.Spec.Rc4 VG.Proof.Rc4 VG.Proof.Rc4.Scan64

/-- Copying the table to the context with two zero PRGA indices, returning 0,
and zeroing the frame. -/
theorem init_end (s : State) (hal : (s.gpr .a7).toNat % 8 = 0)
    (hF : InRegions s.wr (s.gpr .a7) 256) (hp : InRegions s.wr (s.gpr .a2) 258)
    (hFc : Mem.Sep (s.gpr .a7) 256 (s.gpr .a2) 258) :
    WP isa (.block (Impl.Words.RISCV64.copyBytes .t0 .a7 .a2 0 0 256 ++
      ([.li .t2 0, .store .b .t2 .a2 256, .store .b .t2 .a2 257, .li .a0 0] : List Instr) ++ wipe)) s
      fun t =>
      (∀ k < 256, t.mem (s.gpr .a2 + BitVec.ofNat 64 k) = s.mem (s.gpr .a7 + BitVec.ofNat 64 k)) ∧
      t.mem (s.gpr .a2 + 256#64) = 0#8 ∧ t.mem (s.gpr .a2 + 257#64) = 0#8 ∧ t.gpr .a0 = 0#64 := by
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .a7) 256 := by
    obtain ⟨region, h, hc⟩ := hF
    exact ⟨region, List.mem_append_right _ h, hc⟩
  have hw : InRegions s.wr (s.gpr .a2) 256 := by
    simpa only [BitVec.add_zero] using region_offset _ _ _ 0 256 (by decide) (by decide) hp
  have hsep : Mem.Sep (s.gpr .a2) 256 (s.gpr .a7) 256 := fun x hx hy => hFc x hy (by omega_using [hx])
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copy256_ok s (by decide) (by decide) hr hw hsep) fun u ⟨uc, _, ug, _, uwr, _⟩ => ?_
  have u7 : u.gpr .a7 = s.gpr .a7 := ug _ (by decide)
  have h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  have h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  have hb : WP isa (.block [.li .t2 0, .store .b .t2 .a2 256, .store .b .t2 .a2 257, .li .a0 0]) u
      fun v => v.mem = (u.mem.write (s.gpr .a2 + 256#64) 1 0#8).write (s.gpr .a2 + 257#64) 1 0#8 ∧
        v.gpr .a0 = 0#64 ∧ v.gpr .a7 = u.gpr .a7 ∧ v.wr = u.wr := by
    have h256' : InRegions u.wr (s.gpr .a2 + BitVec.ofNat 64 256) 1 := by rw [uwr]; exact h256
    have h257' : InRegions u.wr (s.gpr .a2 + BitVec.ofNat 64 257) 1 := by rw [uwr]; exact h257
    rrun [h256', h257', ug _ (show Reg.a2 ≠ .t0 by decide)]
    rfl
  refine WP.mono hb fun v ⟨vm, v0, v7, vwr⟩ => ?_
  rw [u7] at v7
  refine WP.mono (WP.rdwr (WP.keep [] (wipe_ok v (by rw [v7]; exact hal)
    (by rw [vwr, uwr, v7]; exact hF)) (by decide +kernel)))
    fun t ⟨⟨⟨tf, _⟩, tk⟩, _⟩ => ?_
  rw [v7] at tf
  have hne (k : Nat) (hk : k < 256) (e : Nat) (he : 256 ≤ e) (he' : e < 258) :
      s.gpr .a2 + BitVec.ofNat 64 k ≠ s.gpr .a2 + BitVec.ofNat 64 e :=
    Offset.add_ofNat_ne _ (by omega_using [hk]) (by omega_using [he']) (by omega_using [hk, he])
  have hout (k : Nat) (hk : k < 258) : ¬ (s.gpr .a2 + BitVec.ofNat 64 k - s.gpr .a7).toNat < 256 :=
    fun h => hFc _ h (by rw [Mem.sub_ofNat_toNat _ (by omega_using [hk])]; exact hk)
  refine ⟨fun k hk => ?_, ?_, ?_, (tk.gpr (by decide)).trans v0⟩
  · rw [frame_byte tf (hout k (by omega_using [hk])), vm, write_byte, ite_eq_right (hne k hk 257 (by decide) (by decide)),
      write_byte, ite_eq_right (hne k hk 256 (by decide) (by decide)), uc k hk]
  · rw [frame_byte tf (hout 256 (by decide)), vm, write_byte,
      ite_eq_right (Offset.add_ofNat_ne _ (by decide) (by decide) (by decide)), write_byte, ite_eq_left rfl]
  · rw [frame_byte tf (hout 257 (by decide)), vm, write_byte, ite_eq_left rfl]

/-- Key scheduling, with its frame at the stack pointer. -/
theorem init_main (s : State) (hal : s.sp.toNat % 8 = 0) (hF : InRegions s.wr s.sp 256)
    (hlen : 1 ≤ (s.gpr .a1).toNat ∧ (s.gpr .a1).toNat ≤ 256)
    (hp : InRegions s.wr (s.gpr .a2) 258)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .a0) (s.gpr .a1).toNat)
    (hs : Mem.Sep (s.gpr .a0) (s.gpr .a1).toNat s.sp 256)
    (hFc : Mem.Sep s.sp 256 (s.gpr .a2) 258) :
    WP isa initMain s fun t => t.gpr .a0 = 0#64 ∧
      contextAt t.mem (s.gpr .a2) =
        { table := keySchedule (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat), i := 0, j := 0 } := by
  have hstart : WP isa (.block [.addSp .a7 0, .li .a3 0]) s
      fun a => a.mem = s.mem ∧ a.rd = s.rd ∧ a.wr = s.wr ∧ a.gpr .a7 = s.sp ∧
        a.gpr .a0 = s.gpr .a0 ∧ a.gpr .a1 = s.gpr .a1 ∧ a.gpr .a2 = s.gpr .a2 ∧
        a.gpr .a3 = 0#64 := by
    rrun
  unfold initMain
  refine WP.seq (WP.mono hstart fun a ha => ?_)
  obtain ⟨ham, har, haw, hap, ha0, ha1, ha2, ha3⟩ := ha
  have hpa : InRegions a.wr (a.gpr .a7) 256 := by rw [haw, hap]; exact hF
  have hia : IdentityInv a 0 a :=
    ⟨by rw [identityMem_zero], rfl, rfl, rfl, rfl, rfl, rfl, ha3⟩
  refine WP.seq (WP.mono (identity_loop a a (by decide) hpa hia) fun b hb => ?_)
  obtain ⟨hbm, hbr, hbw, hbp, hb0, hb1, hb2, _⟩ := hb
  have hreset : WP isa (.block [.li .a3 0, .li .t3 0, .li .a4 0, .li .t6 0]) b
      fun c => c.mem = b.mem ∧ c.rd = b.rd ∧ c.wr = b.wr ∧ c.gpr .a7 = b.gpr .a7 ∧
        c.gpr .a0 = b.gpr .a0 ∧ c.gpr .a1 = b.gpr .a1 ∧ c.gpr .a2 = b.gpr .a2 ∧
        c.gpr .a3 = 0#64 ∧ c.gpr .t3 = 0#64 ∧ c.gpr .a4 = 0#64 ∧ c.gpr .t6 = 0#64 := by
    rrun
  refine WP.seq (WP.mono hreset fun c hc => ?_)
  obtain ⟨hcm, hcr, hcw, hcp, hc0, hc1, hc2, hc3, hct3, hc4, hc6⟩ := hc
  have hcp' : c.gpr .a7 = s.sp := by rw [hcp, hbp, hap]
  have hlc : 1 ≤ (c.gpr .a1).toNat ∧ (c.gpr .a1).toNat ≤ 256 := by
    rw [hc1, hb1, ha1]; exact hlen
  have hpc : InRegions c.wr (c.gpr .a7) 256 := by rw [hcw, hbw, haw, hcp']; exact hF
  have hkc : InRegions (c.rd ++ c.wr) (c.gpr .a0) (c.gpr .a1).toNat := by
    rw [hcr, hcw, hc0, hc1, hbr, hbw, hb0, hb1, har, haw, ha0, ha1]; exact hk
  have hsc : Mem.Sep (c.gpr .a0) (c.gpr .a1).toNat (c.gpr .a7) 256 := by
    rw [hc0, hc1, hcp', hb0, hb1, ha0, ha1]; exact hs
  have hic : ScheduleInv c 0 c := by
    refine ⟨TableFrame.refl _ _, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, hc6, rfl, rfl⟩
    · rw [hcm, hbm, hcp, hbp, identityMem_table, schedule_zero]
    · rw [hc4]; rfl
    · rw [hc3]
    · rw [hct3, Nat.zero_mod]
  refine WP.seq (WP.mono (schedule_loop c c (by decide) hlc (by rw [hcp']; exact hal) hpc hkc hsc
    hic) fun d hd => ?_)
  have hd7 : d.gpr .a7 = s.sp := hd.p.trans hcp'
  have hd2 : d.gpr .a2 = s.gpr .a2 := by rw [hd.ctx, hc2, hb2, ha2]
  have hdw : d.wr = s.wr := by rw [hd.wr, hcw, hbw, haw]
  refine WP.mono (init_end d (by rw [hd7]; exact hal) (by rw [hdw, hd7]; exact hF)
    (by rw [hdw, hd2]; exact hp) (by rw [hd7, hd2]; exact hFc)) fun e ⟨etab, ei, ej, e0⟩ => ?_
  rw [hd2, hd7] at etab
  rw [hd2] at ei ej
  have hkey : keyAt c = bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat := by
    unfold keyAt
    rw [hcm, hc0, hc1, hb0, hb1, ha0, ha1, hbm, ham]
    exact bytes_table_frame _ _ _ _ _ (s.gpr .a1).isLt
      (identityMem_frame _ _ _ (by decide)) (by rw [hap]; exact hs)
  refine ⟨e0, context_of ?_ ei ej⟩
  rw [table_copy etab, ← hcp', hd.table, ← keySchedule_eq, hkey]

theorem valid_check (s : State) :
    WP isa (.block [.addi .t2 .a1 (-1), .shift .srl .d .t2 .t2 8]) s fun t =>
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.gpr .a0 = s.gpr .a0 ∧
      t.gpr .a1 = s.gpr .a1 ∧ t.gpr .a2 = s.gpr .a2 ∧
      t.gpr .t2 = (s.gpr .a1 - 1#64) >>> 8 := by
  rrun

/-- The checked initializer, including both key-length boundaries, in its
frame of 256 bytes below the stack pointer. -/
theorem init_ok (s : State) (hal : s.sp.toNat % 16 = 0) (hsp : 256 ≤ s.sp.toNat)
    (hp : InRegions s.wr (s.gpr .a2) 258)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .a0) (s.gpr .a1).toNat)
    (hs : Mem.Sep (s.gpr .a0) (s.gpr .a1).toNat (s.sp - 256#64) 256)
    (hFc : Mem.Sep (s.sp - 256#64) 256 (s.gpr .a2) 258) :
    WP isa VG.Impl.Rc4.RISCV64.init s fun t =>
      match VG.Spec.Rc4.init (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) with
      | .ok ctx => t.gpr .a0 = 0#64 ∧ contextAt t.mem (s.gpr .a2) = ctx
      | .error .invalidKeyLength => t.gpr .a0 = 1#64 := by
  unfold VG.Impl.Rc4.RISCV64.init
  refine WP.seq (WP.mono (valid_check s) fun t ht => ?_)
  obtain ⟨htm, htr, htw, htsp, ht0, ht1, ht2, ht12⟩ := ht
  let good := 1 ≤ (s.gpr .a1).toNat ∧ (s.gpr .a1).toNat ≤ 256
  have hcond : isa.eval (.nonzero .t2) t = some (decide (¬ good)) := by
    rw [Steps.eval_nonzero, ht12, bne]
    congr 1
    by_cases hg : good
    · rw [beq_iff_eq.mpr ((valid_length _).mpr hg), decide_eq_false (not_not_intro hg)]
      rfl
    · rw [beq_eq_false_iff_ne.mpr (fun h => hg ((valid_length _).mp h)), decide_eq_true hg]
      rfl
  refine WP.ite (decide (¬ good)) hcond (fun hn => ?_) (fun hy => ?_)
  · have hn' : ¬ good := of_decide_eq_true hn
    change ¬ (1 ≤ (s.gpr .a1).toNat ∧ (s.gpr .a1).toNat ≤ 256) at hn'
    simp only [VG.Spec.Rc4.init, bytes_length, hn', ite_false]
    rrun
  · have hg : good := Classical.not_not.mp (of_decide_eq_false hy)
    change 1 ≤ (s.gpr .a1).toNat ∧ (s.gpr .a1).toNat ≤ 256 at hg
    simp only [VG.Spec.Rc4.init, bytes_length, hg, and_self, ite_true]
    have hF : (s.sp - 256#64).toNat = s.sp.toNat - 256 := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [hsp])]; rfl
    refine WP.alloc (n := frameBytes) (by decide) (by rw [htsp]; exact hsp) ?_
    have hsp' : (allocd frameBytes t).sp = s.sp - 256#64 := by
      show t.sp - BitVec.ofNat 64 256 = _
      rw [htsp]
    refine WP.mono (init_main (allocd frameBytes t) (by rw [hsp', hF]; omega_using [hal])
      ⟨⟨s.sp - 256#64, 256⟩, by
        show _ ∈ (⟨t.sp - BitVec.ofNat 64 256, 256⟩ :: t.wr : List Region)
        rw [htsp]; exact List.mem_cons_self, by rw [hsp']; exact Region.contains_self _ _⟩
      (by rw [show (allocd frameBytes t).gpr = t.gpr from rfl, ht1]; exact hg)
      (by
        show InRegions (⟨_, _⟩ :: t.wr) (t.gpr .a2) 258
        obtain ⟨r, hr, hc⟩ := hp
        exact ⟨r, List.mem_cons_of_mem _ (by rw [htw]; exact hr), by rw [ht2]; exact hc⟩)
      (by
        show InRegions (t.rd ++ ⟨_, _⟩ :: t.wr) (t.gpr .a0) (t.gpr .a1).toNat
        obtain ⟨r, hr, hc⟩ := hk
        refine ⟨r, ?_, by rw [ht0, ht1]; exact hc⟩
        rw [htr, htw] at *
        rcases List.mem_append.mp hr with h | h
        · exact List.mem_append_left _ h
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ h))
      (by rw [hsp', show (allocd frameBytes t).gpr = t.gpr from rfl, ht0, ht1]; exact hs)
      (by rw [hsp', show (allocd frameBytes t).gpr = t.gpr from rfl, ht2]; exact hFc))
      fun u ⟨hu0, huc⟩ m _ fl => ?_
    refine ⟨hu0, ?_⟩
    rw [show (allocd frameBytes t).gpr = t.gpr from rfl, ht0, ht1, ht2,
      show (allocd frameBytes t).mem = t.mem from rfl, htm] at huc
    -- The `free` loses the frame's bytes, which lie apart from the context.
    have fl' : Frame [⟨s.sp - 256#64, 256⟩] u.mem m := by rw [← htsp]; exact fl
    exact (Proof.Rc4.contextAt_congr fun i hi => lost_sep fl' hFc hi).trans huc

end VG.Proof.Rc4.RISCV64

end

end

/-!
# RC4 on RISC-V: verified against the shared contracts

The proofs are written against per-target contracts (`initX`, `applyX`),
which state the frame of 256 bytes below the stack pointer, and moved to the
shared contracts of `Spec/Rc4/Contract.lean` with `stack := 256`. The code
writes only temporaries and argument registers.
-/

@[expose] public section

namespace VG.Proof.Rc4.RISCV64
open VG VG.RISCV64 VG.Impl.Rc4.RISCV64 VG.Spec.Rc4 VG.Proof.Rc4

/-- The registers the code writes: no preserved register, nor `ra`. -/
def written : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a0, .a1, .a2, .a3, .a4, .a5, .a7]

/-- `Region.Disjoint` as `Mem.Sep`. -/
theorem sep_of_disjoint {r₁ r₂ : Region} (h : r₁.Disjoint r₂) : Mem.Sep r₁.base r₁.len r₂.base r₂.len :=
  fun x hx hy => h x (by simp only [Region.Contains]; omega_using [hx]) (by simp only [Region.Contains]; omega_using [hy])

/-! ## Initialization -/

/-- The contract the proof of `vg_rc4_init` is written against. -/
def initX : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let ctx : Region := ⟨s.gpr .a2, 258⟩
    let stack : Region := ⟨s.sp - 256, 256⟩
    s.rd = [key] ∧ s.wr = [ctx] ∧ key.Disjoint ctx ∧
    s.sp.toNat % 16 = 0 ∧ 256 ≤ s.sp.toNat ∧ stack.Disjoint key ∧ stack.Disjoint ctx
  post s s' :=
    match Spec.Rc4.init (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) with
    | .ok c => (s'.gpr .a0).setWidth 32 = 0 ∧ contextAt s'.mem (s.gpr .a2) = c
    | .error .invalidKeyLength => (s'.gpr .a0).setWidth 32 = 1
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.sp = s₂.sp

theorem init_correct (s : State) (hs : initX.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initX.post s s' := by
  obtain ⟨hrd, hwr, _, hal, hsp, hsk, hsc⟩ := hs
  have hp : InRegions s.wr (s.gpr .a2) 258 :=
    ⟨⟨s.gpr .a2, 258⟩, by rw [hwr]; exact List.mem_cons_self, Region.contains_self _ _⟩
  have hk : InRegions (s.rd ++ s.wr) (s.gpr .a0) (s.gpr .a1).toNat :=
    ⟨⟨s.gpr .a0, (s.gpr .a1).toNat⟩,
      by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _), Region.contains_self _ _⟩
  -- The separations elaborated first: unifying them with `init_ok`'s
  -- arguments while the regions are unknown unfolds `Mem.Sep` (seconds).
  have hks := sep_symm (sep_of_disjoint hsk)
  have hcs := sep_of_disjoint hsc
  obtain ⟨tr, t, he, hpost, hkeep⟩ :=
    WP.keep written (init_ok s hal hsp hp hk hks hcs) (by lit_decide) (by lit_decide)
  refine ⟨tr, t, he, abiPreserved_of_keep he hkeep (by decide) (by decide), ?_⟩
  unfold initX
  dsimp only
  revert hpost
  cases Spec.Rc4.init (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) with
  | ok c => intro hpost; exact ⟨by rw [hpost.1]; rfl, hpost.2⟩
  | error e => cases e; intro hpost; rw [hpost]; rfl

theorem init_ct : ConstantTime isa initX.pre initX.pub init := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine ⟨h.2.2.2, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1

def initSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 1 | .a2 => 0x2000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 1⟩]
  wr := [⟨0x2000, 258⟩]

theorem init_verified : Verified RISCV64.target init (Spec.Rc4.initContract RISCV64.abi 256) :=
  Verified.of_correct init_correct init_ct (by
    sig_implies [Spec.Rc4.initContract, Spec.Rc4.initSig, Spec.Rc4.initPost, initX, RISCV64.abi,
      RISCV64.argRegs] [initSat]
      using initSat)

/-! ## The stream function -/

/-- The contract the proof of `vg_rc4_apply` is written against. -/
def applyX : Contract isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .a0, 258⟩
    let data : Region := ⟨s.gpr .a1, (s.gpr .a2).toNat⟩
    let stack : Region := ⟨s.sp - 256, 256⟩
    s.rd = [] ∧ s.wr = [ctx, data] ∧ ctx.Disjoint data ∧
    s.sp.toNat % 16 = 0 ∧ 256 ≤ s.sp.toNat ∧ stack.Disjoint ctx ∧ stack.Disjoint data
  post s s' :=
    let result := update (contextAt s.mem (s.gpr .a0))
      (bytesAt s.mem (s.gpr .a1) (s.gpr .a2).toNat)
    contextAt s'.mem (s.gpr .a0) = result.1 ∧
      bytesAt s'.mem (s.gpr .a1) (s.gpr .a2).toNat = result.2
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.sp = s₂.sp ∧
    [(s₁.mem (s₁.gpr .a0 + 256)).toNat] = [(s₂.mem (s₂.gpr .a0 + 256)).toNat]

theorem apply_correct (s : State) (hs : applyX.pre s) :
    ∃ t s', Exec isa apply s t s' ∧ abiPreserved s s' ∧ applyX.post s s' := by
  obtain ⟨_, hwr, hcd, hal, hsp, hsc, hsd⟩ := hs
  have hp : InRegions s.wr (s.gpr .a0) 258 :=
    ⟨⟨s.gpr .a0, 258⟩, by rw [hwr]; exact List.mem_cons_self, Region.contains_self _ _⟩
  have hd : InRegions s.wr (s.gpr .a1) (s.gpr .a2).toNat :=
    ⟨⟨s.gpr .a1, (s.gpr .a2).toNat⟩, by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self,
      Region.contains_self _ _⟩
  -- As in `init_correct`.
  have hcds := sep_of_disjoint hcd
  have hcs := sep_of_disjoint hsc
  have hds := sep_of_disjoint hsd
  obtain ⟨tr, t, he, hpost, hkeep⟩ :=
    WP.keep written (apply_ok s hal hsp hp hd hcds hcs hds) (by lit_decide) (by lit_decide)
  exact ⟨tr, t, he, abiPreserved_of_keep he hkeep (by decide) (by decide), hpost⟩

structure EntryAgree (a b : State) : Prop where
  p : a.gpr .a0 = b.gpr .a0
  data : a.gpr .a1 = b.gpr .a1
  len : a.gpr .a2 = b.gpr .a2
  sp : a.sp = b.sp
  i : a.mem (a.gpr .a0 + 256#64) = b.mem (b.gpr .a0 + 256#64)

def ReadValid (s : State) : Prop := InRegions (s.rd ++ s.wr) (s.gpr .a0) 258

def startBlock : List Instr := [.load .b .a3 .a0 256, .load .b .t4 .a0 257, .li .t6 0]

/-- The PRGA index `i` is loaded from the context, where the taint analysis
takes it for secret: it may leak, so it is public. -/
theorem apply_start_ct : RelCT isa (fun a b => ReadValid a ∧ ReadValid b ∧ EntryAgree a b)
    (.block startBlock) fun a b => RISCV64.Taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3]) a b := by
  intro a b tr tr' a' b' ⟨hpa, hpb, hab⟩ ea eb
  have hct : RelCT isa (fun a b => EntryAgree a b) (.block startBlock) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2]) (fun a b h => by
      refine ⟨h.sp, fun r hr => ?_⟩
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.p
      · exact h.data
      · exact h.len) (by taint_decide)
  obtain ⟨htrace, -⟩ := hct a b tr tr' a' b' hab ea eb
  obtain ⟨_, u, eu, hau⟩ := apply_start a hpa
  obtain ⟨_, rfl⟩ := Exec.det eu ea
  obtain ⟨_, v, ev, hbv⟩ := apply_start b hpb
  obtain ⟨_, rfl⟩ := Exec.det ev eb
  obtain ⟨_, _, _, _, ha0, ha1, ha2, ha3, _, _⟩ := hau
  obtain ⟨_, _, _, _, hb0, hb1, hb2, hb3, _, _⟩ := hbv
  refine ⟨htrace, ⟨(Exec.sp eu).trans (hab.sp.trans (Exec.sp ev).symm), fun r hr => ?_⟩⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ha0.trans (hab.p.trans hb0.symm)
  · exact ha1.trans (hab.data.trans hb1.symm)
  · exact ha2.trans (hab.len.trans hb2.symm)
  · rw [ha3, hb3, hab.i]

theorem apply_ct : ConstantTime isa ReadValid EntryAgree apply := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  unfold apply
  refine RelCT.seq apply_start_ct (RelCT.ite ?_ ?_ ?_)
  · intro a b h
    rw [Steps.eval_zero, Steps.eval_zero, h.2 .a2 (by simp [Taint.mem_ofRegs])]
  · exact RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ h => ⟨h.1.1, by simp⟩)
      (by taint_decide)
  · exact RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) (fun _ _ h => h.1)
      (by taint_decide)

theorem apply_ct' : ConstantTime isa applyX.pre applyX.pub apply := by
  intro s₁ s₂ tr₁ tr₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  have hv (s : State) (h : applyX.pre s) : ReadValid s :=
    ⟨⟨s.gpr .a0, 258⟩, List.mem_append_right _ (by rw [h.2.1]; exact List.mem_cons_self),
      Region.contains_self _ _⟩
  exact apply_ct s₁ s₂ tr₁ tr₂ t₁ t₂ (hv s₁ h₁) (hv s₂ h₂)
    ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, BitVec.eq_of_toNat_eq (List.cons.inj hp.2.2.2.2).1⟩ e₁ e₂

def applySat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 1 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 258⟩, ⟨0x2000, 1⟩]

theorem apply_verified : Verified RISCV64.target apply (Spec.Rc4.applyContract RISCV64.abi 256) :=
  Verified.of_correct apply_correct apply_ct' (by
    sig_implies [Spec.Rc4.applyContract, Spec.Rc4.applySig, Spec.Rc4.applyPost, Spec.Rc4.applyLeak,
      applyX, RISCV64.abi, RISCV64.argRegs] [applySat]
      using applySat)

end VG.Proof.Rc4.RISCV64

end

end

/-!
# Rc4 on RISC-V, without secret residue

Each function, followed by `Impl.Scrub.RISCV64.scrubTail`
(`Impl.Rc4.RISCV64.Fn`, the functions as emitted), which clears the
caller-saved registers and the stack its frames used. Their postconditions read the memory on return only
within their buffers (`RISCV64.Scrub.PostOut`), as on x86-64
(`Proof/Rc4/X86_64/Scrub.lean`).

Every function instead clears only the runs of doublewords that the residue
analysis (`RISCV64.rtaint`) finds may differ between two runs
(`Impl.Scrub.RISCV64.scrubSel`). Their code wipes most of
its own scratch space, which leaves few such doublewords, or none.
-/

@[expose] public section

namespace VG.Proof.Rc4.RISCV64.Scrub

open VG.Spec.Rc4 VG.RISCV64 VG.RISCV64.Scrub

/-! ## Postconditions -/

theorem initOut (stack : Nat) : PostOut (Spec.Rc4.initContract RISCV64.abi stack) (Spec.Rc4.initSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Rc4.initPostOut_local _)

theorem applyOut (stack : Nat) : PostOut (Spec.Rc4.applyContract RISCV64.abi stack) (Spec.Rc4.applySig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain (Proof.Rc4.applyPostOut_local _)

/-! ## The functions as emitted

Each theorem states that a function as emitted (`Impl.Rc4.RISCV64.Fn`) meets its
contract in constant time and returns without secret residue
(`VerifiedScrubbed`, by `RISCV64.Scrub.verifiedScrubbedAll`, or
`verifiedScrubbedSel` for the selective cleanup, whose residue analysis the
kernel evaluates here): what its registration binds. -/

/-- `Spec.Rc4.initApi` as emitted (`Impl.Rc4.RISCV64.Fn.init`) meets its contract
in constant time and returns without secret residue. -/
theorem init_scrubbed :
    VerifiedScrubbed RISCV64.target Impl.Rc4.RISCV64.Fn.init
      (Spec.Rc4.initContract RISCV64.abi 256) 32 :=
  verifiedScrubbedSel (api := Spec.Rc4.initApi) (W := 256) (rb := 32)
    { code := Impl.Rc4.RISCV64.init
      verified := Proof.Rc4.RISCV64.init_verified }
    _ [] (initOut _) (by lit_decide) (hbp_nil _) ⟨_, by taint_decide_ct⟩

/-- `Spec.Rc4.applyApi` as emitted (`Impl.Rc4.RISCV64.Fn.apply`) meets its contract
in constant time and returns without secret residue. -/
theorem apply_scrubbed :
    VerifiedScrubbed RISCV64.target Impl.Rc4.RISCV64.Fn.apply
      (Spec.Rc4.applyContract RISCV64.abi 256) 0 :=
  verifiedScrubbedSel (api := Spec.Rc4.applyApi) (W := 256) (rb := 0)
    { code := Impl.Rc4.RISCV64.apply
      verified := Proof.Rc4.RISCV64.apply_verified }
    _ [] (applyOut _) (by lit_decide) (hbp_nil _) ⟨_, by taint_decide_ct⟩

end VG.Proof.Rc4.RISCV64.Scrub
