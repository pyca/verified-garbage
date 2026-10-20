module
public import VerifiedGarbage.Impl.Bignum.X86.WideProduct
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.Words32

import VerifiedGarbage.Proof.Bignum.X86.WideMultiplier
import VerifiedGarbage.Proof.Bignum.X86.WideAdvance
import VerifiedGarbage.Proof.Bignum.WideWindow
import VerifiedGarbage.Proof.Mont.X86.RowW
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # A full multiplication row adds its shifted partial product -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem wideRow_ok {s : State} {base : Addr} {bytes N out a b mult i : Nat}
    (hs : Scr s base bytes) (hi : i < N)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i))
    (ha : a + 4 * N ≤ bytes) (hb : b + 4 * N ≤ bytes)
    (ho : out + 4 * (2 * N + 1) ≤ bytes) (hm : mult + 4 ≤ bytes)
    (sep : b + 4 * N ≤ out ∨ out + 4 * (2 * N + 1) ≤ b)
    (mb : mult + 4 ≤ b ∨ b + 4 * N ≤ mult)
    (mo : mult + 4 ≤ out ∨ out + 4 * (2 * N + 1) ≤ mult)
    (small : val32 s.mem base (out + 4 * i) (N + 2) +
      w32 s.mem base (a + 4 * i) * val32 s.mem base b N < 2 ^ (32 * (N + 2))) :
    WP isa (wideProductRow N out a b mult) s fun t =>
      t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (4 * (i + 1)) ∧
      t.zf = some (decide (i + 1 = N)) ∧
      val32 t.mem base out (2 * N + 1) = val32 s.mem base out (2 * N + 1) +
        2 ^ (32 * i) * (w32 s.mem base (a + 4 * i) * val32 s.mem base b N) ∧
      Outs base [(out, 4 * (2 * N + 1)), (mult, 4)] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have nw := hs.nowrap
  unfold wideProductRow
  refine WP.seq (WP.mono (wideMultiplier_ok hs hp (by omega) hm) fun u ⟨M, O, K⟩ => ?_)
  have Hu := hs.of_keeps K (by decide)
  have Pu : u.gpr .ebp = u.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [K.1 _ (by decide), K.1 _ (by decide)]; exact hp
  have Win := O.val32 (d := out + 4 * i) (k := N + 2) (by omega) (by omega)
  have B := O.val32 (d := b) (k := N) (by omega) (by omega)
  have All := O.val32 (d := out) (k := 2 * N + 1) (by omega) (by omega)
  refine WP.seq (WP.mono (mulRowW_ok Hu (by omega) Pu
    (show 4 * i + out = out + 4 * i by omega) hb (by omega) (by omega) hm (by omega)
    (by rw [Win, M, B]; exact small)) fun v ⟨Ov, V, Kv⟩ => ?_)
  have Pv : v.gpr .ebp = v.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [Kv.1 _ (by decide), Kv.1 _ (by decide)]; exact Pu
  have Owide : Outside base out (4 * (2 * N + 1)) u.mem v.mem := Ov.mono (by omega) (by omega)
  have Full := val32_window_add (width := N + 2) (tail := N - 1 - i)
    (by simpa only [show 4 * (N + 2) = 4 * N + 8 by omega] using Ov)
    (by omega : out + 4 * (i + (N + 2) + (N - 1 - i)) ≤ 2 ^ 64) V
  rw [show i + (N + 2) + (N - 1 - i) = 2 * N + 1 by omega, All, M, B] at Full
  refine WP.mono (wideAdvance_ok hi (by omega) Pv) fun t ⟨Pt, Zt, Mt, Kt⟩ => ?_
  refine ⟨Pt, Zt, by rw [Mt]; exact Full, ?_,
    ((K.mono (by decide)).trans (Kv.mono (by decide))).trans (Kt.mono (by decide))⟩
  rw [Mt]
  exact (Outs.of_outside O (by simp)).trans (Outs.of_outside Owide (by simp))

end VG.Proof.Bignum.X86
