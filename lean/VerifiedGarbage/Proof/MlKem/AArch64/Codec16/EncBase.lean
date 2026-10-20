module
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.TCB.AArch64.Isa

import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.Framework.Contract

/-! # ByteEncode12 contract and input representation -/

@[expose] public section

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- AArch64 contract for `vg_mlkem_encode12(f = x0, out = x1)`: if the
polynomial at `f` is reduced, writes `ByteEncode₁₂` of it to the 384 bytes at
`out`. The code may read `f` and write `out`, which do not overlap. -/
def encode12AArch64 : Contract AArch64.isa where
  pre s :=
    s.rd = [⟨s.gpr .x0, 1024⟩] ∧ s.wr = [⟨s.gpr .x1, 384⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, 1024⟩ ⟨s.gpr .x1, 384⟩ ∧ Reduced s.mem (s.gpr .x0)
  post s s' := bytesAt s'.mem (s.gpr .x1) 384 = encode12 (polyAt s.mem (s.gpr .x0))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64.Encode12

open VG VG.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

section
variable (s₀ : State)

abbrev fP : Addr := s₀.gpr .x0
abbrev oP : Addr := s₀.gpr .x1
abbrev oR : Region := ⟨oP s₀, 384⟩
abbrev P : Poly := polyAt s₀.mem (fP s₀)
/-- Byte `j` of the output. -/
def L (j : Nat) : Byte := (encode12 (P s₀))[j]!

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [polyRegion (fP s₀)]
  wr : s₀.wr = [oR s₀]
  disj : (polyRegion (fP s₀)).Disjoint (oR s₀)
  red : Reduced s₀.mem (fP s₀)

theorem Pre.coeff {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [oR s₀] s₀.mem m) {i : Nat}
    (hi : i < 256) : (coeffAt m (fP s₀) i).toNat = ((P s₀)[i]!).val := by
  rw [coeffAt_frame hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.disj) hi,
    polyAt_val hp.red (show i < n from hi)]

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 384⟩]

end VG.Proof.MlKem.AArch64.Encode12
