module

public import VerifiedGarbage.Proof.X448.Radix16Bytes
public import VerifiedGarbage.Proof.X448.X86.Instr
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# X448 on x86 (32-bit): decoding a coordinate word

A word of the coordinate is written to both initial coordinate slots.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16
theorem byte_rotate (b : BitVec 8) : (b.setWidth 32).rotateRight 24 = b.setWidth 32 <<< 8 := by
  have hz : b.setWidth 32 >>> 24 = 0 := by
    apply BitVec.eq_of_toNat_eq
    have hb := b.isLt
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
    change b.toNat % 2 ^ 32 / 2 ^ 24 = 0
    omega_using []
  rw [BitVec.rotateRight_def, hz]
  exact BitVec.zero_or


/-- A string of `4 n` bytes is the number of its `n` words. -/
theorem bytes_num (m : Mem) (p : Addr) :
    ∀ n, VG.Proof.X25519.leNum (Spec.X448.bytesAt m p (4 * n)) =
      Proof.X25519.X86.num (fun k => (m.readW (off p (4 * k)) 32).toNat) n
  | 0 => rfl
  | n + 1 => by
    rw [show 4 * (n + 1) = 4 * n + 4 from rfl, bytesAt_add, VG.Proof.X25519.leNum_append, bytes_num m p n,
      length_bytesAt, Nat.pow_mul, Proof.X25519.X86.num_succ]
    exact congrArg (_ + _ * ·) (VG.Proof.X25519.leNum_bytesAt_32bit m _)

theorem decodeWord_ok {s : State} {base p : Addr} (hs : Scr s base) {i : Nat}
    (hi : i < 14) (hp : (s.gpr .esi).setWidth 64 = p) (hfit : (s.gpr .esi).toNat + 56 ≤ 2 ^ 32)
    (hr : ∀ k < 14, InRegions (s.rd ++ s.wr) (off p (4 * k)) 4) :
    WP isa (.block (decodeWord i)) s fun t =>
      t.mem = (s.mem.writeW (off base (X1 + 4 * i)) (s.mem.readW (off p (4 * i)) 32)).writeW
        (off base (X3 + 4 * i)) (s.mem.readW (off p (4 * i)) 32) ∧ Keeps [.eax] s t := by
  unfold decodeWord
  refine wp_load (a := off p (4 * i)) (by
    change addr (s.gpr .esi) (4 * i) = _
    rw [VG.X86.addr_eq (by omega_using [hi, hfit]), hp]) (hr i hi) fun s1 h1 => ?_
  have hs1 := hs.of_upd h1 (by decide)
  refine store_ok hs1 (by simp only [X1, slot]; omega_using [hi]) fun s4 h4 => ?_
  have hs4 := hs1.of_keeps ((h4.rest [])) (by decide)
  refine store_ok hs4 (by simp only [X3, slot]; omega_using [hi]) fun s5 h5 => WP.block_nil ⟨?_, ?_⟩
  · rw [h5.mem, h4.mem, h1.mem, h4.gpr, h1.gpr]
  · exact (h1.rest (by decide)).trans ((h4.rest _).trans (h5.rest _))

/-- The two coordinate words lie inside their respective slots. -/
theorem decodeWord_outside (m : Mem) (base : Addr) {i : Nat} (hi : i < 14) (v : BitVec 32) :
    Outside2 base X1 (4 * (i + 1)) X3 (4 * (i + 1)) m
      ((m.writeW (off base (X1 + 4 * i)) v).writeW (off base (X3 + 4 * i)) v) := by
  intro p hp hq
  rw [writeW_outside _ _ _ (by simp only [X3, slot]; omega_using [hi]) p (by omega_using [hq]),
    writeW_outside _ _ _ (by simp only [X1, slot]; omega_using [hi]) p (by omega_using [hp])]

end VG.Proof.X448.X86
