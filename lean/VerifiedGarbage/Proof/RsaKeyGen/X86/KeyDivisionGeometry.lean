module

public import VerifiedGarbage.Impl.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Rsa.X86.DivContext
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs

/-! # The four-array native RSA division bank -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys

def divisionGeometry (B : Addr) (Z n : Nat) : VG.Proof.Rsa.X86.Div.Geometry :=
  { base := B, size := Z, n := n, offsets := fun i => arr n i.val }

theorem division_context {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 4) :
    VG.Proof.Rsa.X86.Div.Context (divisionGeometry B Z n) s := by
  refine ⟨h.workspace, h.wpos, by have := h.wle; change n < 2 ^ 24; omega, ?_, ?_⟩
  · intro i
    have fit := h.arr_fit i.isLt
    change arr n i.val + 4 * (if i = 0 then n else n + 1) ≤ Z
    unfold S at fit
    split <;> omega
  · intro i j ne
    have indices : i.val ≠ j.val := fun e => ne (Fin.ext e)
    have disj := arr_disj (w := n) indices
    change arr n i.val + 4 * (if i = 0 then n else n + 1) ≤ arr n j.val ∨
      arr n j.val + 4 * (if j = 0 then n else n + 1) ≤ arr n i.val
    unfold S at disj
    split <;> split <;> omega

theorem division_frame {m m' : Mem} {B : Addr} {Z n : Nat}
    (O : Outs B (divisionGeometry B Z n).ranges m m') :
    Outside B VG.Impl.Rsa.X86.Keys.hdr (4 * (4 * (n + 2))) m m' := by
  intro x hx
  apply O x
  intro r hr
  simp only [VG.Proof.Rsa.X86.Div.Geometry.ranges, divisionGeometry,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  all_goals simp only [arr, S] at hx ⊢
  all_goals omega

end VG.Proof.RsaKeyGen.X86.Key
