module

import VerifiedGarbage.Proof.Poly1305.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Poly1305.Spec
public import VerifiedGarbage.Proof.Poly1305.RISCV64.State
public import VerifiedGarbage.Proof.Poly1305.RISCV64.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Poly1305.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Poly1305.RISCV64.State
meta import VerifiedGarbage.Proof.Poly1305.RISCV64.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Poly1305.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Poly1305.Spec
import VerifiedGarbage.Proof.Poly1305.RISCV64.Reduce
meta import VerifiedGarbage.Proof.Poly1305.RISCV64.Reduce

/-! ### `Poly1305.RISCV64.Blocks`, which this module and modules that import it used -/

section

/-!
# Poly1305 on RISC-V: `blocks`

As on AArch64 (`Proof/Poly1305/AArch64/Radix64/Blocks.lean`): the loop
invariant says that the accumulator in the registers is that of the message
on entry followed by the blocks absorbed so far, modulo `p`; the epilogue
reduces and stores it. The code writes only temporaries and argument
registers, and the memory only in the state's accumulator.
-/

@[expose] public section

namespace VG.Proof.Poly1305.RISCV64

open VG VG.RISCV64 VG.RISCV64.Wide VG.Impl.Poly1305.RISCV64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

/-- The registers the code writes: no preserved register, nor `ra`. -/
def written : List Reg :=
  [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a1, .a2, .a3, .a4, .a5, .a6, .a7]

/-- The absorbing of a block, with the key from `Keys`. -/
theorem absorb_key_ok (s : State) (b : Reg) (off : Nat) (pad : Bool) (wide : Bool) {R : Nat}
    (hk : Keys R s)
    (ho : off + 15 < 2048)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 off) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 (off + 8)) 8)
    (hal : wide = true → (s.gpr b + BitVec.ofNat 64 off).toNat % 8 = 0)
    (hb : b ∉ absorbRegs := by decide) :
    WP isa (.block (absorb b off pad wide)) s fun s' =>
      (Bounds s → hv s' % P =
        ((hv s + (word s.mem (s.gpr b) off + 2 ^ 64 * word s.mem (s.gpr b) (off + 8) +
          2 ^ 128 * pad.toNat)) * R) % P ∧ Bounds s') ∧ Keeps absorbRegs s s' := by
  obtain ⟨q, hr0, hr1, hq, hs1, hr⟩ := hk
  simpa only [← hr, Bounds] using absorb_ok s b off pad wide hr0 hr1 hq hs1 ho h0 h8 hal hb

/-! ## The precondition -/

/-- The value of block `i`, with the `0x01` byte appended: its two words and `2¹²⁸`. -/
theorem block_value (m : Mem) (p : Addr) :
    word m p 0 + 2 ^ 64 * word m p (0 + 8) + 2 ^ 128 * true.toNat =
      leNum (bytesAt m p 16 ++ [0x01]) := by
  rw [Poly1305.leNum_append, Poly1305.length_bytesAt, leNum_key]
  have h1 : leNum [(0x01 : Byte)] = 1 := rfl
  rw [h1, Bool.toNat_true, show (256 : Nat) ^ 16 = 2 ^ 128 from rfl]

end VG.Proof.Poly1305.RISCV64

end

end

/-!
# Poly1305 on RISC-V: the buffer

The buffer (bytes 56–71 of the state) as `update` and `finalize` fill it, and
absorbing it as a block, as on PPC64LE (`Proof/Poly1305/PPC64LE/Buffer.lean`).
-/

@[expose] public section

namespace VG.Proof.Poly1305.RISCV64

open VG VG.RISCV64 VG.RISCV64.Wide VG.Impl.Poly1305.RISCV64
open VG.Spec.Poly1305 (P leNum bytesAt Repr Buffered)

theorem off_56 (p : Addr) : off p 56 = p + 56 := rfl

/-- `x &&& 15`. -/
theorem and15 (x : BitVec 64) : x &&& BitVec.ofInt 64 15 = BitVec.ofNat 64 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (BitVec.ofInt 64 15).toNat = 2 ^ 4 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := x.toNat % 16) (by omega_using [])]

/-- The buffer. -/
abbrev bfR (st : Addr) : Region := ⟨off st 56, 16⟩

theorem bfR_sub_wR (st : Addr) : Region.Sub (bfR st) (wR st) :=
  Offset.sub st (by decide) (by decide)

/-- The two words of the buffer, as a number. -/
theorem leNum_buf (m : Mem) (st : Addr) :
    word m st 56 + 2 ^ 64 * word m st (56 + 8) = leNum (bytesAt m (off st 56) 16) := by
  rw [leNum_key, word, word, word, word, add_ofNat_zero, off, Offset.add_add]

/-- Absorbing the buffer: its 16 bytes, and `pad · 2¹²⁸`. -/
theorem absorbBuf_ok (s : State) (pad : Bool) {R : Nat} (hk : Keys R s)
    (hw : sR (s.gpr .a0) ∈ s.wr) :
    WP isa (.block (absorb .a0 56 pad)) s fun s' =>
      (Bounds s → hv s' % P = ((hv s + (leNum (bytesAt s.mem (off (s.gpr .a0) 56) 16) +
        2 ^ 128 * pad.toNat)) * R) % P ∧ Bounds s') ∧ Keeps absorbRegs s s' := by
  have hin : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (s.gpr .a0 + BitVec.ofNat 64 d) 8 :=
    fun d hd => in_st' (List.mem_append_right _ hw) hd
  refine WP.mono (absorb_key_ok s .a0 56 pad false hk (by decide) (hin 56 (by decide))
    (hin (56 + 8) (by decide)) (fun h => by cases h)) fun s' ⟨ha, k⟩ => ⟨fun hb => ?_, k⟩
  obtain ⟨hv', hb'⟩ := ha hb
  refine ⟨?_, hb'⟩
  rw [hv', leNum_buf]

/-- The `k + n` bytes at `base` after `n` bytes are written from `base + k` on. -/
theorem bytesAt_after {m m' : Mem} {base : Addr} {k n : Nat} (hkn : k + n ≤ 16)
    (hf : Frame [⟨base + BitVec.ofNat 64 k, n⟩] m m') (src : Nat → Byte)
    (hc : ∀ i < n, m' (base + BitVec.ofNat 64 k + BitVec.ofNat 64 i) = src i) :
    bytesAt m' base (k + n) = bytesAt m base k ++ (List.range n).map src := by
  rw [Poly1305.bytesAt_add]
  congr 1
  · refine Poly1305.bytesAt_frame hf (fun r hr => ?_) (by omega_using [hkn])
    simp only [List.mem_singleton] at hr
    subst hr
    exact Offset.base_disjoint base (by omega_using []) (by omega_using [hkn])
  · simp only [bytesAt]
    exact List.map_congr_left fun i hi => hc i (List.mem_range.mp hi)

/-- The proof contracts of `update` and `finalize` only need the length
of the message modulo 16. -/
theorem count_mod {count : BitVec 64} {n : Nat} (h : count = BitVec.ofNat 64 n) :
    count.toNat % 16 = n % 16 := by
  rw [h, BitVec.toNat_ofNat]; omega_using []

end VG.Proof.Poly1305.RISCV64
