module

public import VerifiedGarbage.Proof.MillerRabin.X86.ProductFrame
public import VerifiedGarbage.Proof.MillerRabin.X86.OperandFrame

/-! # The live word, window count, and flag between arithmetic operations -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt)

structure WindowHeaders (m : Mem) (base : Addr) (v : BitVec 32) (k : Nat) (F : Bool) : Prop where
  word : m.readW (off base sV) 32 = v
  count : m.readW (off base sK) 32 = BitVec.ofNat 32 k
  flag : m.readW (off base sF) 32 = BitVec.ofNat 32 F.toNat

namespace WindowHeaders

theorem of_reads {m m' : Mem} {base : Addr} {v : BitVec 32} {k : Nat} {F : Bool}
    (h : WindowHeaders m base v k F)
    (same : ∀ d, d ∈ [sV, sK, sF] → m'.readW (off base d) 32 = m.readW (off base d) 32) :
    WindowHeaders m' base v k F :=
  ⟨(same sV (by simp)).trans h.word, (same sK (by simp)).trans h.count,
    (same sF (by simp)).trans h.flag⟩

theorem of_array {s : State} {m' : Mem} {base : Addr} {bytes w o : Nat} {v : BitVec 32} {k : Nat} {F : Bool}
    (h : WindowHeaders s.mem base v k F) (ctx : ProtectedContext s base bytes)
    (hf : arrAt w 28 ≤ bytes) (ho : o < 28)
    (frame : Frame [⟨off base (arrAt w o), 8 * w⟩] s.mem m') : WindowHeaders m' base v k F := by
  apply h.of_reads
  intro d hd
  have small : d + 4 ≤ 256 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;> decide
  exact array_frame_header ctx.ws.nowrap hf ho small frame

theorem of_product {s : State} {m' : Mem} {base : Addr} {bytes w o : Nat} {v : BitVec 32} {k : Nat} {F : Bool}
    (h : WindowHeaders s.mem base v k F) (ctx : ProtectedContext s base bytes)
    (room : CallRoom (s.gpr .esp) base bytes) (hf : arrAt w 28 ≤ bytes) (ho : o < 28)
    (frame : Frame [⟨off base (arrAt w o), 8 * w⟩,
      ⟨off base (scratch w), Spec.Rsa.MontMul.scratchBytes w⟩,
      below (s.gpr .esp) 40] s.mem m') : WindowHeaders m' base v k F := by
  apply h.of_reads
  intro d hd
  have small : d + 4 ≤ 256 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;> decide
  exact product_frame_header ctx room hf ho small frame

theorem of_equal {s : State} {m' : Mem} {base : Addr} {bytes w o : Nat} {v : BitVec 32} {k : Nat} {F : Bool}
    (h : WindowHeaders s.mem base v k F) (ctx : ProtectedContext s base bytes)
    (hf : arrAt w 28 ≤ bytes) (ho : o = sE1 ∨ o = sE2)
    (frame : Frame [⟨off base o, 4⟩] s.mem m') : WindowHeaders m' base v k F := by
  have hdrFit : 256 ≤ bytes := Nat.le_trans (Nat.le_add_right _ _) hf
  apply h.of_reads
  intro d hd
  have small : d + 4 ≤ 256 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;> decide
  have out : o + 4 ≤ 256 := by rcases ho with rfl | rfl <;> decide
  have apart : d + 4 ≤ o ∨ o + 4 ≤ d := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    all_goals rcases ho with rfl | rfl <;> decide
  exact workspace_frame_word ctx.ws.nowrap (Nat.le_trans small hdrFit) (Nat.le_trans out hdrFit) apart frame

end WindowHeaders
end VG.Proof.MillerRabin.X86
