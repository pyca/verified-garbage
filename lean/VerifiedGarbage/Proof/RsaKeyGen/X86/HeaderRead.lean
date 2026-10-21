module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Header
import VerifiedGarbage.Proof.Framework.Offset

/-! # Pointer initialization preserves the scalar metadata and inverse -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Header
open VG VG.Proof.Mont

theorem read64_write {base : Addr} {m : Mem} {d e : Nat} {v : BitVec 64}
    (apart : d + 8 ≤ e ∨ e + 8 ≤ d) (readFit : d + 8 ≤ 2 ^ 64) (writeFit : e + 8 ≤ 2 ^ 64) :
    (m.writeW (off base e) v).readW (off base d) 64 = m.readW (off base d) 64 :=
  Mem.readW_writeW_sep (Offset.sep base apart readFit writeFit) (by decide)

theorem pointers_read64 (indices : List Nat) {base : Addr} {p : BitVec 32} {w d : Nat} {m : Mem}
    (bound : ∀ i ∈ indices, i < 8) (fit : d + 8 ≤ 2 ^ 64)
    (apart : d + 8 ≤ 64 ∨ 128 ≤ d) :
    (indices.foldl (pointerMemory base p w) m).readW (off base d) 64 = m.readW (off base d) 64 := by
  induction indices generalizing m with
  | nil => rfl
  | cons i indices ih =>
    rw [List.foldl_cons, ih (fun j mem => bound j (List.mem_cons_of_mem _ mem))]
    unfold pointerMemory
    apply read64_write _ fit
    · have := bound i (List.mem_cons_self ..)
      omega
    · have := bound i (List.mem_cons_self ..)
      omega

theorem header_inverse {base : Addr} {p : BitVec 32} {w : Nat} {m : Mem} :
    (headerMemory base p w m).readW (off base 56) 64 = m.readW (off base 56) 64 := by
  unfold headerMemory
  rw [pointers_read64 _ (fun _ mem => List.mem_range.mp mem) (by decide) (by decide),
    read64_write (by decide) (by decide) (by decide),
    read64_write (by decide) (by decide) (by decide)]

theorem header_width {base : Addr} {p : BitVec 32} {w : Nat} {m : Mem} :
    (headerMemory base p w m).readW (off base 48) 64 = 0#32 ++ BitVec.ofNat 32 w := by
  unfold headerMemory
  rw [pointers_read64 _ (fun _ mem => List.mem_range.mp mem) (by decide) (by decide),
    read64_write (by decide) (by decide) (by decide), Mem.readW_writeW_self64]

theorem header_stride {base : Addr} {p : BitVec 32} {w : Nat} {m : Mem} :
    (headerMemory base p w m).readW (off base 224) 64 =
      0#32 ++ BitVec.ofNat 32 (VG.Impl.Bignum.X86.PublicContext.stride w) := by
  unfold headerMemory
  rw [pointers_read64 _ (fun _ mem => List.mem_range.mp mem) (by decide) (by decide),
    Mem.readW_writeW_self64]

theorem pointers_read64_at (indices : List Nat) {base : Addr} {p : BitVec 32} {w j : Nat} {m : Mem}
    (bound : ∀ i ∈ indices, i < 8) (index : j < 8) :
    (indices.foldl (pointerMemory base p w) m).readW (off base (64 + 8 * j)) 64 =
      if j ∈ indices then 0#32 ++ (p + BitVec.ofNat 32 (VG.Impl.Bignum.X86.PublicContext.slot w j))
      else m.readW (off base (64 + 8 * j)) 64 := by
  induction indices generalizing m with
  | nil => rfl
  | cons i indices ih =>
    rw [List.foldl_cons, ih (fun k mem => bound k (List.mem_cons_of_mem _ mem))]
    by_cases tail : j ∈ indices
    · simp only [tail, ite_true, List.mem_cons, or_true]
    · rw [ite_eq_right tail]
      by_cases same : j = i
      · subst i
        simp only [List.mem_cons, true_or, ite_true, pointerMemory, Mem.readW_writeW_self64]
      · simp only [List.mem_cons, same, false_or, tail, ite_false]
        unfold pointerMemory
        apply read64_write
        · omega
        · omega
        · have := bound i (List.mem_cons_self ..)
          omega

theorem header_pointer {base : Addr} {p : BitVec 32} {w j : Nat} {m : Mem} (index : j < 8) :
    (headerMemory base p w m).readW (off base (64 + 8 * j)) 64 =
      0#32 ++ (p + BitVec.ofNat 32 (VG.Impl.Bignum.X86.PublicContext.slot w j)) := by
  unfold headerMemory
  rw [pointers_read64_at _ (fun _ mem => List.mem_range.mp mem) index, ite_eq_left (List.mem_range.mpr index)]

end VG.Proof.RsaKeyGen.X86.Header
