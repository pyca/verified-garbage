module

public import VerifiedGarbage.Impl.MillerRabin.X86.Workspace
public import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Framework.Omega

/-! # Public widths and pointers in the shared i686 primality workspace -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt)
open VG.Proof.Mont.X86.Rt (PtrAt)

section
variable {s : State} {is : List Instr} {Q : State → Prop}

theorem width_ok {r : Reg} {w : Nat}
    (hr : readSrc s (.mem (sc 48)) = some (BitVec.ofNat 32 w))
    (k : ∀ t, Keeps [r] s t → t.mem = s.mem → t.gpr r = BitVec.ofNat 32 (8 * w) →
      WP isa (.block is) t Q) :
    WP isa (.block (width r ++ is)) s Q := by
  simp only [width, List.cons_append, List.nil_append]
  refine wp_movS hr fun s₁ u₁ _ => wp_addS rfl fun s₂ u₂ _ =>
    wp_addS rfl fun s₃ u₃ _ => wp_addS rfl fun t u₄ _ => ?_
  refine k t (((u₁.keeps.trans u₂.keeps).trans u₃.keeps).trans u₄.keeps)
    (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]) ?_
  rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
  repeat rw [← BitVec.ofNat_add]
  congr 1
  omega

theorem arrayOffset_ok {r t : Reg} {w j : Nat} (hrt : r ≠ t)
    (hr : readSrc s (.mem (sc 48)) = some (BitVec.ofNat 32 w)) (hw : w ≤ 128)
    (k : ∀ u, Keeps [r, t] s u → u.mem = s.mem →
      u.gpr r = BitVec.ofNat 32 (arrAt w j) → u.gpr t = BitVec.ofNat 32 (8 * (w + 2)) →
      WP isa (.block is) u Q) :
    WP isa (.block (arrayOffset r j t ++ is)) s Q := by
  simp only [arrayOffset, List.append_assoc, List.cons_append]
  refine width_ok hr fun s₁ K₁ m₁ e₁ => wp_addS rfl fun s₂ u₂ _ => wp_movS rfl fun s₃ u₃ _ => ?_
  refine VG.Proof.Bignum.X86.PublicRt.adds_ok hrt j fun u K m e => ?_
  have et : s₃.gpr t = BitVec.ofNat 32 (8 * (w + 2)) := by
    rw [u₃.other _ hrt.symm, u₂.gpr, e₁]
    change BitVec.ofNat 32 (8 * w) + BitVec.ofNat 32 16 = _
    rw [← BitVec.ofNat_add]
    congr 1
  refine k u ((K₁.trans u₂.keeps).mono (by simp) |>.trans ((u₃.keeps.trans K).mono (by simp)))
    (by rw [m, u₃.mem, u₂.mem, m₁]) ?_ (by rw [K.1 _ (by simp [hrt.symm]), et])
  rw [e, u₃.gpr, et, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  change BitVec.ofNat 32 256 + BitVec.ofNat 32 (j * (8 * (w + 2))) = _
  rw [← BitVec.ofNat_add]
  rfl

theorem arrayPointer_ok {r t : Reg} {w j : Nat} {base : Addr}
    (hrt : r ≠ t) (hre : r ≠ .edi) (hte : t ≠ .edi)
    (hr : readSrc s (.mem (sc 48)) = some (BitVec.ofNat 32 w)) (hw : w ≤ 128)
    (hedi : (s.gpr .edi).toNat = base.toNat)
    (k : ∀ u, Keeps [r, t] s u → u.mem = s.mem → PtrAt u base r (arrAt w j) →
      WP isa (.block is) u Q) :
    WP isa (.block (arrayPointer r j t ++ is)) s Q := by
  simp only [arrayPointer, List.append_assoc, List.cons_append]
  refine arrayOffset_ok hrt hr hw fun s₁ K m e _ => wp_addS rfl fun u U _ => ?_
  refine k u (K.trans (U.keeps.mono (by simp))) (U.mem.trans m) ?_
  rw [PtrAt, U.gpr, e, K.1 .edi (by simp [hre.symm, hte.symm]), BitVec.toNat_add,
    BitVec.toNat_ofNat, hedi, Nat.mod_add_mod, Nat.add_comm]

theorem stackPointer_ok {r : Reg} {d : Nat}
    (k : ∀ t, Keeps [r] s t → t.mem = s.mem → t.gpr r = s.gpr .esp + BitVec.ofNat 32 d →
      WP isa (.block is) t Q) :
    WP isa (.block (stackPointer r d ++ is)) s Q := by
  simp only [stackPointer, List.cons_append, List.nil_append]
  refine wp_movS rfl fun s₁ U₁ _ => wp_addS rfl fun t U₂ _ =>
    k t (U₁.keeps.trans U₂.keeps) (U₂.mem.trans U₁.mem) ?_
  rw [U₂.gpr, U₁.gpr]

theorem scratchOffset_ok {r : Reg} {w : Nat}
    (hr : readSrc s (.mem (sc 48)) = some (BitVec.ofNat 32 w))
    (k : ∀ t, Keeps [r] s t → t.mem = s.mem → t.gpr r = BitVec.ofNat 32 (256 + 16 * w) →
      WP isa (.block is) t Q) :
    WP isa (.block (scratchOffset r ++ is)) s Q := by
  simp only [scratchOffset, List.append_assoc, List.cons_append]
  refine width_ok hr fun s₁ K₁ m₁ e₁ => wp_addS rfl fun s₂ U₂ _ => wp_addS rfl fun t U₃ _ => ?_
  refine k t ((K₁.trans U₂.keeps).trans U₃.keeps) (by rw [U₃.mem, U₂.mem, m₁]) ?_
  rw [U₃.gpr, U₂.gpr, e₁]
  change (BitVec.ofNat 32 (8 * w) + BitVec.ofNat 32 (8 * w)) + BitVec.ofNat 32 256 = _
  rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 1
  omega

theorem scratchPointer_ok {r : Reg} {w : Nat} {base : Addr}
    (hre : r ≠ .edi)
    (hr : readSrc s (.mem (sc 48)) = some (BitVec.ofNat 32 w))
    (hedi : (s.gpr .edi).toNat = base.toNat)
    (k : ∀ t, Keeps [r] s t → t.mem = s.mem → PtrAt t base r (256 + 16 * w) →
      WP isa (.block is) t Q) :
    WP isa (.block (scratchPointer r ++ is)) s Q := by
  simp only [scratchPointer, List.append_assoc, List.cons_append]
  refine scratchOffset_ok hr fun s₁ K m e => wp_addS rfl fun t U _ => ?_
  refine k t (K.trans U.keeps) (U.mem.trans m) ?_
  rw [PtrAt, U.gpr, e, K.1 .edi (by simp [hre.symm]), BitVec.toNat_add,
    BitVec.toNat_ofNat, hedi, Nat.mod_add_mod, Nat.add_comm]

end
end VG.Proof.MillerRabin.X86
