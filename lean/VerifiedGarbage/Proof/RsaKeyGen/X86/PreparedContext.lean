module

public import VerifiedGarbage.Proof.MillerRabin.X86.Modulus
public import VerifiedGarbage.Proof.Mont.X86.DynamicOps
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
import VerifiedGarbage.Proof.Bignum.X86.PublicLayout

/-! # Compact preparation arithmetic and the runtime prepared-round context agree -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Prepared
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

theorem slot_eq (g : Geometry) (j : Nat) : slot g.w j = g.array j := by
  unfold slot stride Geometry.array Proof.Rsa.Mont.arrAt VG.Impl.Bignum.hdrBytes Proof.Rsa.Mont.hdrBytes
  congr 1

theorem layout {g : Geometry} (v : g.Valid) :
    OpLay (modulus g.w) g.L (g.array 2) (g.array 6) (g.array 6) (g.array 6) := by
  rw [← slot_eq g 2, ← slot_eq g 6]
  apply VG.Proof.Bignum.X86.PublicContext.operation_layout
  · have fit := v.arraysFit
    simp only [size, slot, stride, Proof.Rsa.Mont.arrAt, VG.Impl.Bignum.hdrBytes, Proof.Rsa.Mont.hdrBytes] at *
    omega
  all_goals first | (unfold operand; decide) | decide

theorem dynamicModulus {g : Geometry} (v : g.Valid) {c : Nat} {m : Mem} (M : Modulus g c m) :
    VG.Proof.Mont.X86.Dynamic.Modulus (modulus g.w) g.L c m g.W := by
  have a := v.arrayFit (j := 0) (by decide)
  have b := v.arrayFit (j := 1) (by decide)
  have sep := g.arrayBefore (i := 0) (j := 1) (by decide)
  simp only [Geometry.words] at a b sep
  refine ⟨by change 0 < g.w; have := v.minWidth; omega, ?_, ?_, ?_, ?_⟩
  · change slot g.w 0 + 8 * g.w ≤ g.L
    rw [slot_eq]; omega
  · change slot g.w 1 + 8 * g.w ≤ g.L
    rw [slot_eq]; omega
  · left
    change slot g.w 0 + 8 * g.w ≤ slot g.w 1
    rw [slot_eq, slot_eq]; omega
  · change wordsVal m g.W (slot g.w 0) g.w = c
    rw [slot_eq, wordsVal_eq_val32]; exact M.candidate

theorem keepRanges {g : Geometry} (v : g.Valid) {s t : State} (C : Context g s)
    {rs : List Reg} (K : Keeps rs s t) (base : .edi ∉ rs)
    {ranges : List (Nat × Nat)} (O : Outs g.W ranges s.mem t.mem)
    (header : ∀ r ∈ ranges, 256 ≤ r.1) : Context g t := by
  have F := WorkspaceFrame.of_outs C.ws.nowrap O
  have read {d : Nat} (fit : d + 4 ≤ 256) : w32 t.mem g.W d = w32 s.mem g.W d := by
    exact congrArg BitVec.toNat (F.read32 (Nat.le_trans fit v.headerFit)
      (fun r mem => Or.inl (Nat.le_trans fit (header r mem))))
  refine ⟨C.ws.of_keeps K, ?_, ?_, ?_, ?_⟩
  · rw [VG.Proof.Mont.X86.Rt.PtrAt, K.1 .edi base]; exact C.base
  · rw [read (by decide)]; exact C.width
  · rw [read (by decide)]; exact C.stride
  · intro j index
    rw [read (by omega)]; exact C.pointers j index

end VG.Proof.RsaKeyGen.X86.Prepared
