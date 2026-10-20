module
public import VerifiedGarbage.Proof.MlKem.Arith
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.TCB.AArch64.Isa

import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Framework.Contract

/-! # ByteDecode12 contract and input representation -/

@[expose] public section

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- AArch64 contract for `vg_mlkem_decode12(b = x0, f = x1)`: writes
`ByteDecode₁₂` of the 384 bytes at `b` to `f`, reduced. The code may read `b`
and write `f`, which do not overlap. -/
def decode12AArch64 : Contract AArch64.isa where
  pre s :=
    s.rd = [⟨s.gpr .x0, 384⟩] ∧ s.wr = [⟨s.gpr .x1, 1024⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, 384⟩ ⟨s.gpr .x1, 1024⟩
  post s s' := PolyIs s'.mem (s.gpr .x1) (decode12 (bytesAt s.mem (s.gpr .x0) 384))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64.Decode12

open VG VG.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

section
variable (s₀ : State)

abbrev bP : Addr := s₀.gpr .x0
abbrev fP : Addr := s₀.gpr .x1
abbrev bR : Region := ⟨bP s₀, 384⟩
abbrev B : List Byte := bytesAt s₀.mem (bP s₀) 384
/-- Coefficient `i` of the output. -/
def G (i : Nat) : BitVec 32 := BitVec.ofNat 32 ((decode12 (B s₀))[i]!).val
/-- Byte `j` of the input, as a number. -/
abbrev byte (j : Nat) : Nat := ((B s₀).getD j 0).toNat

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [bR s₀]
  wr : s₀.wr = [polyRegion (fP s₀)]
  disj : (bR s₀).Disjoint (polyRegion (fP s₀))

theorem Pre.byte_eq {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [polyRegion (fP s₀)] s₀.mem m)
    {j : Nat} (hj : j < 384) : (m (bP s₀ + BitVec.ofNat 64 j)).toNat = byte s₀ j := by
  rw [byte_frame (len := 384) hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.disj)
    (by decide) hj]
  show _ = ((bytesAt s₀.mem (bP s₀) 384).getD j 0).toNat
  rw [bytesAt_getD _ _ hj]

theorem G_even (s₀ : State) {k : Nat} (hk : k < 128) :
    G s₀ (2 * k) = BitVec.ofNat 32 (condSub (byte s₀ (3 * k) + (byte s₀ (3 * k + 1) % 16) * 256)) := by
  have : byte s₀ (3 * k) < 256 := byte_lt _
  have : byte s₀ (3 * k + 1) < 256 := byte_lt _
  have : ((B s₀).getD (3 * k) 0).toNat < 256 := byte_lt _
  have : ((B s₀).getD (3 * k + 1) 0).toNat < 256 := byte_lt _
  have hq : q = 3329 := rfl
  rw [G, decode12_even _ (bytesAt_length _ _ _) hk, val_ofNat, condSub_eq (by omega), Nat.mul_comm 256]

theorem G_odd (s₀ : State) {k : Nat} (hk : k < 128) :
    G s₀ (2 * k + 1) = BitVec.ofNat 32 (condSub (byte s₀ (3 * k + 1) / 16 + byte s₀ (3 * k + 2) * 16)) := by
  have : byte s₀ (3 * k + 1) < 256 := byte_lt _
  have : byte s₀ (3 * k + 2) < 256 := byte_lt _
  have : ((B s₀).getD (3 * k + 1) 0).toNat < 256 := byte_lt _
  have : ((B s₀).getD (3 * k + 2) 0).toNat < 256 := byte_lt _
  have hq : q = 3329 := rfl
  rw [G, decode12_odd _ (bytesAt_length _ _ _) hk, val_ofNat, condSub_eq (by omega), Nat.mul_comm 16]

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 1024⟩]

end VG.Proof.MlKem.AArch64.Decode12
