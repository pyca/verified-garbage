module

public import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.Spec.ChaCha20
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# ChaCha20 keystream XOR on AArch64
-/

@[expose] public section

namespace VG.Proof.ChaCha20

open Spec.ChaCha20 VG.AArch64

/-- AArch64 contract for `vg_chacha20_xor(state: *mut [u32; 16], src: *const u8,
len: usize, buf: *mut [u32; 80], dst: *mut u8)`: writes the `len` bytes at
`src` XORed with the first `len` bytes of the keystream of the state at
`state` to the `len` bytes at `dst`.

The code may read `src` (`len` bytes), and read and write `state` (64 bytes;
its contents on exit are unspecified), `dst` (`len` bytes) and `buf` (320
bytes of working space). `dst` is either `src` (in place) or apart from it;
otherwise they may not overlap each other; neither `src` nor `dst` wraps
around the end of the address space. The return address is in `x30`, not on
the stack, and the code uses no stack. The pointers and the length are
public; the state and the data are secret. -/
def xorAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 64⟩
    let src : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat⟩
    let buf : Region := ⟨s.gpr .x3, 320⟩
    let dst : Region := ⟨s.gpr .x4, (s.gpr .x2).toNat⟩
    s.rd = [src] ∧ s.wr = [state, dst, buf] ∧
    state.Disjoint src ∧ state.Disjoint dst ∧ state.Disjoint buf ∧ src.Disjoint buf ∧
    dst.Disjoint buf ∧ (s.gpr .x4 = s.gpr .x1 ∨ src.Disjoint dst) ∧
    (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64
  post s s' :=
    bytesAt s'.mem (s.gpr .x4) (s.gpr .x2).toNat =
      List.zipWith (· ^^^ ·) (bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
        (keystream (stateAt s.mem (s.gpr .x0)) (s.gpr .x2).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

end VG.Proof.ChaCha20

