import VerifiedGarbage.Proof.Mont.Words

/-! # Sixteen-byte accesses to Montgomery working space -/
namespace VG.Proof.Mont
open VG

/-- A 16-byte write changes only its bytes. -/
theorem writeW128_out (m : Mem) (base : Addr) {d : Nat} (v : BitVec 128) (h : d + 16 ≤ 2 ^ 64) :
    Outside base d 16 m (m.writeW (off base d) v) := by
  intro x hx
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by omega)]
  simp only [ofs] at hx
  omega

/-- 16 bytes outside the bytes that changed. -/
theorem Outside.read128 {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') {d : Nat}
    (hd : d + 16 ≤ o ∨ o + n ≤ d) (hd' : d + 16 ≤ 2 ^ 64) : m'.readW (off base d) 128 = m.readW (off base d) 128 :=
  (Mem.readW_congr fun i hi => (h _ (by rw [ofs_off base (by omega)]; omega)).symm).symm

end VG.Proof.Mont
