module

public import VerifiedGarbage.Proof.MlKem.AArch64.Width
public import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlKem.Encode

/-!
# ML-KEM on AArch64: what `vg_mlkem_compress_encode` writes

Group `g` of the output is the number whose base-`2ᵈ` digits are the
compressed coefficients `c g … c g + c - 1` (`byteEncode_group`): byte `j` of
it is `acc g c / 2^(8 j)` (`L_eq`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.CE

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

section
variable (w : Width) (s₀ : State)

abbrev fP : Addr := s₀.gpr .x0
abbrev oP : Addr := s₀.gpr .x2
abbrev oR : Region := ⟨oP s₀, 32 * w.d⟩
abbrev P : Poly := polyAt s₀.mem (fP s₀)
/-- Coefficient `i`, compressed. -/
def C (i : Nat) : Nat := compress w.d (P s₀)[i]!
/-- Byte `j` of the output. -/
def L (j : Nat) : Byte := (compressEncode w.d (P s₀))[j]!
/-- The first `e` compressed coefficients of group `g`, as the digits of a number. -/
def acc (g e : Nat) : Nat := digits w.d ((List.range e).map fun e' => C w s₀ (w.c * g + e'))
/-- The output's bytes before. -/
def old (j : Nat) : Byte := s₀.mem (oP s₀ + BitVec.ofNat 64 j)

end

structure Pre (w : Width) (s₀ : State) : Prop where
  rd : s₀.rd = [polyRegion (fP s₀)]
  wr : s₀.wr = [oR w s₀]
  disj : (polyRegion (fP s₀)).Disjoint (oR w s₀)
  red : Reduced s₀.mem (fP s₀)

theorem C_lt (w : Width) (s₀ : State) (i : Nat) : C w s₀ i < 2 ^ w.d := compress_lt _ _

theorem acc_succ (w : Width) (s₀ : State) (g e : Nat) :
    acc w s₀ g (e + 1) = acc w s₀ g e + 2 ^ (w.d * e) * C w s₀ (w.c * g + e) :=
  digits_range_succ _ _ _

theorem acc_lt (w : Width) (s₀ : State) (g e : Nat) : acc w s₀ g e < 2 ^ (w.d * e) :=
  digits_range_lt (fun _ => C_lt _ _ _) _

/-- Byte `j` of group `g` of the output. -/
theorem L_eq {w : Width} (hw : WOk w) (s₀ : State) {g j : Nat} (hg : g < 256 / w.c) (hj : j < w.nb) :
    L w s₀ (w.nb * g + j) = BitVec.ofNat 8 (acc w s₀ g w.c / 2 ^ (8 * j)) := by
  have hcg : w.c * g + w.c ≤ 256 := by
    have := hw.cG
    have : w.c * (g + 1) ≤ w.c * (256 / w.c) := Nat.mul_le_mul_left _ hg
    rw [Nat.mul_succ] at this
    omega
  have hk : w.nb * g + j < 32 * w.d := by
    have := hw.bytes
    have : w.nb * (g + 1) ≤ w.nb * (256 / w.c) := Nat.mul_le_mul_left _ hg
    rw [Nat.mul_succ] at this
    omega
  rw [L, Spec.MlKem.compressEncode, byteEncode_group hw.d_pos hw.dc (map_toList_lt _ (compress_lt w.d)) hj hk,
    take_drop_eq _ 0 (by rw [map_toList_length]; exact hcg), acc]
  refine congrArg (fun x => BitVec.ofNat 8 (digits w.d x / 2 ^ (8 * j))) (List.map_congr_left ?_)
  intro e he
  rw [map_toList_getD _ _ (by have := List.mem_range.mp he; omega)]
  rfl

theorem Pre.coeff {w : Width} {s₀ : State} (hp : Pre w s₀) {m : Mem}
    (hf : Frame [oR w s₀] s₀.mem m) {i : Nat} (hi : i < 256) :
    (coeffAt m (fP s₀) i).toNat = ((P s₀)[i]!).val := by
  rw [coeffAt_frame hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.disj) hi,
    polyAt_val hp.red (show i < n from hi)]

end VG.Proof.MlKem.AArch64.CE
