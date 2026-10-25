module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtRecP1
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtRecP2
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtRecP3
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCopy
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The RSA private-key operation on PPC64LE: `h` in `p`'s working space

`recombineP_ok`: `h = (m₁ + p - m₂ mod p) mod p · qInv mod p` into array 4.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- `recombineP`, in `p`'s working space `off BX oA` (`P` in array 0, `m₁` in
array 4), for `m₂`'s `qL` bytes in `X`'s array 1 and `qInv` in its array 7. -/
theorem recombineP_ok {s : State} {BX : Addr} {Z oA wP wX qL Pv m1 m2 QI : Nat}
    (hs : Scr s BX Z) (hA : oA + slot wP 24 ≤ Z) (hXA : slot wX 8 ≤ oA) (hw2 : 2 ≤ wP) (hw' : wP < 2 ^ 31)
    (hwx : wP ≤ wX) (hwX : wX < 2 ^ 31)
    (h10 : s.gpr .r10 = off (off BX oA) (slot wP 0)) (h21 : s.gpr .r21 = off (off BX oA) (slot wP 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (wP + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * wP))
    (h23 : s.gpr .r23 = BX) (h27 : s.gpr .r27 = off BX (slot wX 0))
    (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hQL : word s.mem BX oQLen = BitVec.ofNat 64 qL) (hq1 : 1 ≤ qL) (hqx : qL ≤ 8 * (wX + 2))
    (hP : val32 s.mem (off BX oA) (slot wP 0) (2 * wP) = Pv) (hP2 : 2 ≤ Pv) (hPodd : Pv % 2 = 1)
    (hm1 : val32 s.mem (off BX oA) (slot wP 4) (2 * wP) = m1) (hm1P : m1 < Pv)
    (hm2 : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off BX (slot wX 1)) qL) = m2)
    (hQ : wv s.mem BX (slot wX 7) wP = QI) (hQP : QI < Pv) :
    WP isa recombineP s fun t =>
      (val32 t.mem (off BX oA) (slot wP 4) (2 * wP) = (m1 + Pv - m2 % Pv) % Pv * QI % Pv ∧
        Outside BX oA (slot wP 24) s.mem t.mem) ∧ Keep recRegs s t := by
  have hn := hs.nowrap
  have e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have hh : hdrBytes = 256 := rfl
  have eA0 := e wP 0; have eA3 := e wP 3; have eA4 := e wP 4; have eA7 := e wP 7; have eA8 := e wP 24
  have sX7 := slot_le (w := wX) (show 7 < 8 by decide)
  unfold recombineP
  refine recP1_ok hs hA hXA hw2 hw' h10 h29 h11 h23 h27 h28 hQL hq1 hqx hwX hP hP2 hPodd hm1 hm2
    fun t₁ v0 v1 v4 v7 i12 iinv out1 k1 => ?_
  have hsA := (hs.congr k1.wr).sub hA
  refine recP2a_ok hsA (by unfold slot; omega_arith) hw2 hw' ((k1.gpr _ (by decide)).trans h10)
    ((k1.gpr _ (by decide)).trans h21) ((k1.gpr _ (by decide)).trans h29)
    ((k1.gpr _ (by decide)).trans h11) v0 v1 v4 (Nat.mod_lt _ (by omega_arith)) hm1P
    fun t₂ v3 out2 a10 k2 => ?_
  have hr2 : ∀ j, j ≠ 3 → j ≠ 4 → j < 8 →
      ∀ r ∈ [(slot wP 3, 8 * (wP + 2)), (slot wP 4, 8 * (wP + 2))],
        slot wP j + 4 * (2 * wP) ≤ r.1 ∨ r.1 + r.2 ≤ slot wP j := by
    intro j h3 h4 h8 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have s3 := slot_sep (w := wP) h3; have s4 := slot_sep (w := wP) h4
    rcases hr with rfl | rfl <;> simp only <;> omega_arith
  have out2' := outs_sub (S := slot wP 24) out2 (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_arith) (by omega_arith)
  have o12 := out1.trans out2'
  refine WP.mono (recP3_ok (hs.congr (k1.trans k2).wr) hA hXA hw2 hw' a10
    ((k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans h29))
    ((k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans h11))
    ((k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans h27))
    ((k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans h28))
    (by rw [k2.gpr _ (by decide)]; exact i12)
    (by
      rw [k2.gpr _ (by decide)]
      refine Eq.trans ?_ iinv
      refine congrArg (fun v => (v * (t₁.gpr .r12).toNat + 1) % 2 ^ 32) ?_
      refine congrArg BitVec.toNat (Mem.readW_congr fun i hi => out2 _ fun r hr => ?_)
      have := hr2 0 (by decide) (by decide) (by decide) r hr
      rw [Mont.ofs_off (off BX oA) (d := slot wP 0) (i := i) (by omega_arith)]; omega_arith)
    (by rw [out2.val32 (hr2 0 (by decide) (by decide) (by decide)) (by omega_arith), v0]) hPodd v3
    (by rw [out2.val32 (hr2 7 (by decide) (by decide) (by decide)) (by omega_arith), v7])
    (by rw [o12.wv (Or.inl (by omega_arith)) (by omega_arith)]; exact hQ) hQP)
    fun t ⟨⟨v4', out3⟩, k3⟩ => ⟨⟨v4', o12.trans out3⟩, ((k1.trans k2).trans k3).mono⟩

end VG.Proof.Bignum.PPC64LE.Crt
