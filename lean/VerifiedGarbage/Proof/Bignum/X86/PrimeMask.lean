module

public import VerifiedGarbage.Proof.Bignum.X86.PrimeMaskFinish
public import VerifiedGarbage.Proof.Bignum.X86.SmallConstant
public import VerifiedGarbage.Proof.Mont.X86.ContextInit

/-! # The mask accepts exactly odd secret factors greater than one -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86 VG.Proof.Ecdsa.X86

theorem primeMask_ok {s : State} {base : Addr} {bytes n : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (hz : contextBytes n ≤ bytes) :
    WP isa (primeMask n) s fun t =>
      t.gpr .ecx = mask32 (1 < wordsVal s.mem base (slot n 0) n ∧
        wordsVal s.mem base (slot n 0) n % 2 = 1) ∧
      Outside base (slot n 7) (8 * n) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have b7 := slot_bound (n := n) (i := 7) (by decide)
  have sep := slot_le (n := n) (i := 0) (j := 7) (by decide)
  have nw := hs.nowrap
  unfold primeMask
  refine WP.seq (WP.mono (smallConstant_ok hs hn (by decide)
    (by unfold stride at b7; omega)) fun u ⟨O, One, K⟩ => ?_)
  have M : wordsVal u.mem base (slot n 0) n = wordsVal s.mem base (slot n 0) n := by
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    exact O.val32 (by unfold stride at sep; omega) (by unfold stride at b0; omega)
  refine WP.seq (WP.mono (lessThan_ok n (hs.of_keeps K (by decide)) hn
    (by unfold stride at b7; omega) (by unfold stride at b0; omega)) fun v ⟨E, Kv, Mv⟩ => ?_)
  have Kv' : Keeps [.eax, .ecx, .edx, .ebp] s v := (K.mono (by decide)).trans Kv
  have low := modulus_low (mem := v.mem) hn (by rw [Mv, M])
  refine WP.mono (primeMaskFinish_ok (hs.of_keeps Kv' (by decide))
    (by unfold stride at b0; omega) low (by rw [E, One, M])) fun t ⟨T, Mt, Kt⟩ => ?_
  exact ⟨T, by rw [Mt, Mv]; exact O, Kv'.trans (Kt.mono (by decide))⟩

end VG.Proof.Bignum.X86
