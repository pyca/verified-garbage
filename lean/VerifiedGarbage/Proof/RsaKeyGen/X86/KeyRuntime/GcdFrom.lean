module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Inverse
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGcdFrom
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Widen
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Ops
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseBridge
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32

/-! # Prime-width GCD computation preserves the full RSA workspace

A saved bit chooses the computed gcd or one. The bit is retained across
the smaller inverse, and widening clears every unused output word.
-/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aU aDen aOne kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr
open VG.Proof.RsaKeyGen.X86.Key (gcdRanges inverse_workspace inverse_array_layout inverse_end_le
  inverse_preserves_num inverse_preserves_slot InverseLayout)

theorem gcdFrom_ok {s : State} {B : Addr} {Z n k : Nat}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k)
    (boundU : num s.mem B n aU < 2 ^ (32 * k)) (boundM : num s.mem B n aDen < 2 ^ (32 * k))
    (odd : num s.mem B n aDen % 2 = 1) (large : 1 < num s.mem B n aDen)
    (one : num s.mem B n aOne = 1) (bit : slot s.mem B kFlag ≤ 1) :
    WP isa gcdFrom s fun t =>
      Ws t B Z n 32 ∧ Outs B (gcdRanges n k) s.mem t.mem ∧
      num t.mem B n aDen = (if slot s.mem B kFlag = 0 then 1 else
        Nat.gcd (num s.mem B n aU) (num s.mem B n aDen)) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have small : k ≤ n := by omega
  have hk := inverse_workspace h.old positive small
  have layout := inverse_array_layout h.old small (a := aU) (b := aDen)
    (by decide) (by decide) (by decide) (by decide)
  have U := VG.Proof.RsaKeyGen.WordBounds32.low_eq small boundU
  have M := VG.Proof.RsaKeyGen.WordBounds32.low_eq small boundM
  have divWidth : n / 2 = k := by omega
  unfold gcdFrom seqs
  have layout' : InverseLayout Z (Width.prime.words n)
      ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aU).offset n)
      ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aDen).offset n) := by
    simpa only [VG.Impl.RsaKeyGen.X86.KeyRuntime.arr, offset_array, Width.words, divWidth] using layout
  refine WP.seq (WP.mono (inverseFrom_ok h (by decide) (by decide) layout' 
    (by change val32 s.mem B (arr n aDen) (n / 2) % 2 = 1; rw [divWidth, M]; exact odd)
    (by change 1 < val32 s.mem B (arr n aDen) (n / 2); rw [divWidth, M]; exact large)) fun u ⟨hu, Ou, gcd, _, _, Ku⟩ => ?_)
  simp only [VG.Impl.RsaKeyGen.X86.KeyRuntime.arr, offset_array, Width.words, divWidth] at Ou gcd
  change num u.mem B k 1 = Nat.gcd (val32 s.mem B (arr n aU) k) (val32 s.mem B (arr n aDen) k) at gcd
  rw [U, M] at gcd
  have oneU : num u.mem B n aOne = 1 := by
    rw [inverse_preserves_num small (by decide) (h.fit64 (by decide)) Ou, one]
  have flagU : slot u.mem B kFlag = slot s.mem B kFlag := inverse_preserves_slot (by decide) Ou
  have sourceBound : arr k 1 + 4 * k ≤ Z := by
    have F := hk.arr_fit (j := 1) (by decide)
    unfold S at F
    omega
  have before : arr k 1 + 4 * k ≤ arr n aDen := by
    have F := arr_end (w := k) (show 1 < 15 by decide)
    have E := inverse_end_le small (j := aDen) (by decide)
    unfold S at F
    omega
  have widenProof := widen_ok hu .prime (VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aDen)
    (.array .prime 1) (by change n / 2 ≤ n; omega)
    (by exact h.arr_fit (by decide))
    (by simpa only [offset_array, Width.words, divWidth] using sourceBound)
    (Or.inl (by simpa only [VG.Impl.RsaKeyGen.X86.KeyRuntime.arr, offset_array, Width.words, divWidth] using before))
  simp only [VG.Impl.RsaKeyGen.X86.KeyRuntime.arr, offset_array, Width.words, divWidth] at widenProof
  refine WP.seq (WP.mono widenProof
    fun v ⟨hv, Ov, _, widened, Kv⟩ => ?_)
  have denV : num v.mem B n aDen = Nat.gcd (num s.mem B n aU) (num s.mem B n aDen) := widened.trans gcd
  have oneV : num v.mem B n aOne = 1 := by
    change val32 v.mem B (arr n aOne) n = 1
    rw [Ov.val32 (d := arr n aOne) (k := n) (by unfold arr S aOne aDen; omega) (by have := h.fit64 (j := aOne) (by decide); unfold S at this; omega)]
    exact oneU
  have flagV : slot v.mem B kFlag = slot s.mem B kFlag := by
    change w32 v.mem B kFlag = w32 s.mem B kFlag
    rw [Ov.w32 (d := kFlag) (by unfold arr aDen kFlag hdr; omega) (by decide)]
    exact flagU
  refine WP.mono (sel_ok hv (by decide) (by decide) (by decide) (by decide)
    (by rw [flagV]; exact bit) (by decide)) fun t ⟨ht, Ot, selected, Kt⟩ => ?_
  refine ⟨ht, ?_, by rw [selected, flagV, oneV, denV],
    Ku.trans ((Kv.mono (by decide)).trans (Kt.mono (by decide)))⟩
  have first : Outs B (gcdRanges n k) s.mem u.mem :=
    Ou.mono (fun r hr => List.mem_append_left _ hr)
  have middle : Outs B (gcdRanges n k) u.mem v.mem :=
    Outs.of_outside Ov (List.mem_append_right _ (List.mem_singleton_self _))
  have last : Outs B (gcdRanges n k) v.mem t.mem := by
    change Outs B [(arr n aDen, S n)] v.mem t.mem at Ot
    exact Ot.mono (fun r hr => List.mem_append_right _ hr)
  exact (first.trans middle).trans last

end VG.Proof.RsaKeyGen.X86.KeyRuntime
