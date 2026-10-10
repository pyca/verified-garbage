import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Verified

/-! # Ed448's point doubling and affine addition, in radix `2^64`, on x86-64 -/

namespace VG.Artifacts.Ed448R64.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64.Point64 VG.Proof.Ed448.X86_64.Point64
open VG.Spec.Ed448.Point64 (doubleApi addAffineApi doubleContract addAffineContract)

/-- How the functions work. -/
def notes (formula : String) : List String := ["Uses baseline integer instructions, and SSE2 moves \
  to keep `rbp` and `r12`–`r15` in `xmm0`–`xmm4` while it runs. " ++ formula ++ ", with \
  `vg_x448`'s field operations on seven 64-bit words (multiplied with `mul` by columns), the \
  temporaries in slots 12 to 20 and the product's words at byte 1536."]

theorem double_verified : Verified X86_64.target doubleFn (doubleContract X86_64.abi) :=
  Verified.of_correct (double_correct (by intro r hr; simp only [keptRegs, kept, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> lit_decide)
    (by lit_decide))
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsp]) (fun _ _ _ _ hp => fnPub_agree hp)
      (by taint_decide))
    doubleK_implies

theorem add_verified : Verified X86_64.target addFn (addAffineContract X86_64.abi) :=
  Verified.of_correct (add_correct (by intro r hr; simp only [keptRegs, kept, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> lit_decide)
    (by lit_decide))
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsp]) (fun _ _ _ _ hp => fnPub_agree hp)
      (by taint_decide))
    addK_implies

def artifacts : List Artifact := [
  { doubleApi with
    target := X86_64.target
    doc := doubleApi.doc (notes := notes "Runs RFC 8032's doubling formulas, seven products")
    code := doubleFn
    contract := doubleContract X86_64.abi
    verified := double_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { addAffineApi with
    target := X86_64.target
    doc := addAffineApi.doc (notes := notes "Runs RFC 8032's complete addition formula with \
      `A = Z₁` for `Z₁ Z₂`, as `Z₂ = 1`: ten products")
    code := addFn
    contract := addAffineContract X86_64.abi
    verified := add_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Ed448R64.X86_64
