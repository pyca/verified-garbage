module
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup


/-! # Complete chunks of an immutable input tape -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem source_slice {s : State} {B ptr : Addr} {Z used width : Nat} {bytes : List Byte}
    (h : Src s B Z ptr bytes) (hroom : used + width ≤ bytes.length) :
    Src s B Z (off ptr used) ((bytes.drop used).take width) := by
  have hl : ((bytes.drop used).take width).length = width := by
    simp only [List.length_take, List.length_drop]; omega
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · change InRegions (s.rd ++ s.wr) (off (off ptr used) i) 1
    rw [off_off]
    exact h.rd (used + i) (by omega)
  · change s.mem (off (off ptr used) i) = _
    rw [off_off, h.val (used + i) (by omega)]
    simp only [List.getElem_take, List.getElem_drop]
  · change Z ≤ ofs B (off (off ptr used) i)
    rw [off_off]
    exact h.out (used + i) (by omega)

end VG.Proof.Dsa.X86_64.Generation
