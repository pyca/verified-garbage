import VerifiedGarbage.Proof.Mont.X86.SparseChain
import VerifiedGarbage.Proof.Mont.X86.Row

/-! # Sparse chains inside a larger accumulator -/
namespace VG.Proof.Mont.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Proof.Mont

theorem positive_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {acc i w : Nat} (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i))
    (hw : 4 * i + acc = w) (hb : w + 40 ≤ size) :
    WP isa (.block (multiChain (acc + 12) positiveMask 7)) s fun u =>
      Outside base w 40 s.mem u.mem ∧
      (∃ c : Bool, val32 u.mem base w 10 + 2 ^ 320 * c.toNat =
        val32 s.mem base w 10 + (s.gpr .ecx).toNat * (2 ^ 96 + 2 ^ 192 + 2 ^ 256)) ∧ Keeps [.eax] s u := by
  have hn := hs.nowrap
  refine WP.mono (multiChain_ok hs hp (w := w + 12) (by omega) positiveMask 6 (by omega))
    fun u ⟨O, ⟨c, _, V⟩, K⟩ => ⟨O.mono (by omega) (by omega), ⟨c, ?_⟩, K⟩
  have hv : multiWeight positiveMask 7 = 1 + 2 ^ 96 + 2 ^ 160 := by decide +kernel
  rw [hv] at V
  rw [show 10 = 3 + 7 from rfl, val32_append u.mem base w 3 7, val32_append s.mem base w 3 7,
    O.val32 (d := w) (k := 3) (by omega) (by omega)]
  simp only [Nat.reduceMul, Nat.reduceAdd] at V ⊢
  omega

theorem sparseShiftSub_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {acc i w j k N : Nat} (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i))
    (hw : 4 * i + acc = w) (hN : N = j + (k + 1)) (hb : w + 4 * N ≤ size) :
    WP isa (.block (sparseChain (acc + 4 * j) .sub .sbb (k + 1))) s fun u =>
      Outside base w (4 * N) s.mem u.mem ∧
      (∃ c : Bool, val32 u.mem base w N + 2 ^ (32 * j) * (s.gpr .ecx).toNat =
        val32 s.mem base w N + 2 ^ (32 * N) * c.toNat) ∧ Keeps [.eax] s u := by
  have hn := hs.nowrap
  refine WP.mono (sparseChainSub_ok hs hp (w := w + 4 * j) (by omega) k (by omega))
    fun u ⟨O, ⟨c, _, V⟩, K⟩ => ⟨O.mono (by omega) (by omega), ⟨c, ?_⟩, K⟩
  rw [hN, val32_append u.mem base w j (k + 1), val32_append s.mem base w j (k + 1), O.val32 (d := w) (k := j) (by omega) (by omega), pow32_add]
  generalize 2 ^ (32 * j) = P at *
  generalize 2 ^ (32 * (k + 1)) = Q at *
  grind

end VG.Proof.Mont.X86
