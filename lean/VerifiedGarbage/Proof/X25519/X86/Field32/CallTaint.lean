module

public import VerifiedGarbage.Proof.Framework.X86.Taint

/-!
# The x86 (32-bit) curve-25519 functions' calls: what is public before each

The point and scalar code of Ed25519 and X25519 calls `vg_ed25519_r32_point_add`
with the workspace pointer `edi` pushed as the argument, from taints that
all know the same about memory and have at least `τCall` public: `esp` and
`edi`, the workspace's base and the pushed word. The addition chain
(`Field32.pow250Call`) calls `vg_gf25519_r32_mul` and `vg_gf25519_r32_sqn`
with the workspace in `edi`, from taints with at least `τField` public
(`esp`, `edi` and the workspace's base), and `τFieldN` (with the count in
`eax` too) for `vg_gf25519_r32_sqn`. Their summaries (`Point32/AddSum`,
`Field32/Pow250Sum`) analyse each function once in place of every call.
-/

@[expose] public section

namespace VG.Proof.X25519.X86

/-- What is public before every call of the functions: `esp`, `edi` and the pushed argument. -/
def τCall : VG.X86.Taint.T :=
  { regs := ⟨144⟩, flags := false, lens := [4, 0, 8192], bases := [(.edi, 2, 0), (.esp, 0, 0)],
    slots := [(0, 0, 4)], wbases := [(0, 0, 2)], argLen := 0, argBases := [], stk := [some 4], room := 8 }

/-- What is public before every call of `vg_gf25519_r32_mul`: `esp`, `edi` and the
workspace's base. -/
def τField : VG.X86.Taint.T :=
  { regs := ⟨144⟩, flags := false, lens := [0, 8192], bases := [(.edi, 1, 0)], room := 8 }

/-- What is public before every call of `vg_gf25519_r32_sqn`: `τField`, and the count in `eax`. -/
def τFieldN : VG.X86.Taint.T := { τField with regs := ⟨145⟩ }

end VG.Proof.X25519.X86
