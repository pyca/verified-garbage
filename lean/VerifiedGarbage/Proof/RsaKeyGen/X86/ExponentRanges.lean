module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64Check
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64Preserve

/-! # Exponent filtering preserves the candidate header and its saved minus-one array -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentFilter
open VG VG.Proof.Mont VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

def ranges (w : Nat) : List (Nat × Nat) := Gcd64.checkRanges ++ [(slot w 0, 8 * w)]

def protectedHeader (d bytes : Nat) : Prop := d + bytes ≤ 100 ∨ 112 ≤ d ∧ d + bytes ≤ 160

theorem gcd_ranges_class {r : Nat × Nat} (mem : r ∈ Gcd64.checkRanges) :
    r.1 + r.2 ≤ 112 ∧ 100 ≤ r.1 ∨ 160 ≤ r.1 := by
  simp only [Gcd64.checkRanges, VG.Proof.Rsa.X86.Keys.ranges, Gcd64.arrays, Gcd64.slots,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at mem
  repeat' first
    | (rcases mem with mem | mem)
    | (rcases mem with rfl)
  all_goals decide

theorem ranges_apart {w d bytes : Nat} (safe : protectedHeader d bytes) {r : Nat × Nat}
    (mem : r ∈ ranges w) : d + bytes ≤ r.1 ∨ r.1 + r.2 ≤ d := by
  rcases List.mem_append.mp mem with mem | mem
  · have C := gcd_ranges_class mem
    unfold protectedHeader at safe
    omega
  · obtain rfl := List.mem_singleton.mp mem
    have lo : 256 ≤ slot w 0 := by change 256 ≤ 256 + 0 * stride w; omega
    unfold protectedHeader at safe
    exact Or.inl (by omega)

theorem saved_apart {w : Nat} (width : 4 ≤ w) {r : Nat × Nat} (mem : r ∈ ranges w) :
    r.1 + r.2 ≤ slot w 5 := by
  rcases List.mem_append.mp mem with mem | mem
  · have hi := Gcd64.ranges_below mem
    have lo : 400 ≤ slot w 5 := by unfold slot stride VG.Impl.Bignum.hdrBytes; omega
    omega
  · obtain rfl := List.mem_singleton.mp mem
    unfold slot stride VG.Impl.Bignum.hdrBytes
    omega

end VG.Proof.RsaKeyGen.X86.ExponentFilter
