import VerifiedGarbage.Proof.Framework.X86.Taint

/-!
# The x86 (32-bit) curve-25519 functions' calls: what is public before each

The point and scalar code of Ed25519 and X25519 calls `vg_gf25519_r32_pow250`
and `vg_ed25519_r32_point_add` with the workspace pointer `edi` pushed as the
argument, from taints that all know the same about memory and have at least
`τCall` public: `esp` and `edi`, the workspace's base and the pushed word.
Their summaries (`Field32/Pow250Sum`, `Point32/AddSum`) analyse each function
once, from `τCall`, in place of every call.
-/

namespace VG.Proof.X25519.X86

/-- What is public before every call of the functions: `esp`, `edi` and the pushed argument. -/
def τCall : VG.X86.Taint.T :=
  { regs := ⟨144⟩, flags := false, lens := [4, 0, 8192], bases := [(.edi, 2, 0), (.esp, 0, 0)],
    slots := [(0, 0, 4)], wbases := [(0, 0, 2)], argLen := 0, argBases := [], stk := [some 4], room := 8 }

end VG.Proof.X25519.X86
