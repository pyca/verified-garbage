module

public import VerifiedGarbage.Proof.Bignum.X86.CrtFrame
public import VerifiedGarbage.Impl.Bignum.X86.CopyArray
import VerifiedGarbage.Proof.Bignum.X86.CopyArray
import VerifiedGarbage.Proof.Bignum.X86.CrtLayout
import VerifiedGarbage.Proof.Mont.X86.ContextLayout

/-! # Slot-local transfers preserve every disjoint CRT component -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic

theorem slot_value {n i j k len : Nat} {base : Addr} {m m' : Mem}
    (O : Outside base (slot n j) len m m') (ne : i ≠ j) (hi : i < 20)
    (hk : k ≤ 2 * n) (hl : len ≤ 16 * n + 4)
    (fit : VG.Impl.Bignum.X86.Crt.size n ≤ 2 ^ 64) :
    wordsVal m' base (slot n i) k = wordsVal m base (slot n i) k := by
  have sep := slot_sep (n := n) ne
  have bound := slot_bound (n := n) hi
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  exact O.val32 (by unfold stride at sep; omega) (by unfold stride at bound; omega)

theorem slot_arithmetic_frame {n i len : Nat} {base : Addr} {m m' : Mem}
    (O : Outside base (slot n i) len m m') (hi : i < 9) (hl : len ≤ 16 * n + 4) :
    Outs base (arithmeticRanges n) m m' := by
  have bound := VG.Proof.Mont.X86.Dynamic.slot_bound (n := n) hi
  have head := slot_header n i
  intro a ha
  have high := ha (64, contextBytes n - 64) (by simp [arithmeticRanges])
  apply O a
  unfold stride at bound
  omega

theorem copySlot_ok {s : VG.X86.State} {base : Addr} {bytes n src dst : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (hz : VG.Impl.Bignum.X86.Crt.size n ≤ bytes)
    (hsrc : src < 20) (hdst : dst < 20) (ne : dst ≠ src) :
    WP VG.X86.isa (VG.Impl.Bignum.X86.copyArray n (slot n src) (slot n dst)) s fun t =>
      wordsVal t.mem base (slot n dst) n = wordsVal s.mem base (slot n src) n ∧
      Outside base (slot n dst) (8 * n) s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have bs := slot_bound (n := n) hsrc
  have bd := slot_bound (n := n) hdst
  have sep := slot_sep (n := n) ne
  exact copyArray_ok hs hn (by unfold stride at bs; omega) (by unfold stride at bd; omega)
    (by unfold stride at sep; omega)

end VG.Proof.Bignum.X86.Crt
