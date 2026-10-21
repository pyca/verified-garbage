module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace

/-! # A runtime-sized key array is cleared by the existing zero loop -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.Mont.X86.Rt (PtrAt)

theorem zero_ok {s : State} {B : Addr} {Z n N : Nat} (h : Ws s B Z n N)
    (w : Width) (out : Loc) (fit : out.offset n + 4 * (w.words n + 2) ≤ Z) :
    WP isa (zero w out) s fun t => Ws t B Z n N ∧
      Outside B (out.offset n) (4 * (w.words n + 2)) s.mem t.mem ∧
      val32 t.mem B (out.offset n) (w.words n + 2) = 0 ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have nowrap := h.old.workspace.nowrap
  have nBound := h.old.wle
  have wBound : w.words n ≤ 1024 := by
    cases w <;> simp only [Width.words] <;> omega
  unfold zero
  simp only [List.append_assoc]
  refine WP.seq (h.ptr_ok out (by decide) (by decide) (by omega) fun u K1 m1 P1 => ?_)
  have hu := h.keep K1 (by rw [m1]; exact Outside.refl _ _ _ _)
  refine hu.bytes_ok w .ecx fun v K2 m2 count => ?_
  refine wp_addS rfl fun a A _ => wp_movS rfl fun b U _ => WP.block_nil ?_
  have K : Keeps [.eax, .ecx, .edx, .ebp] s b :=
    ((K1.mono (by decide)).trans (K2.mono (by decide))).trans
      ((A.keeps.mono (by decide)).trans (U.keeps.mono (by decide)))
  have m : b.mem = s.mem := U.mem.trans (A.mem.trans (m2.trans m1))
  have pointer : PtrAt b B .ebp (out.offset n) := by
    rw [PtrAt, U.other _ (by decide), A.other _ (by decide), K2.1 _ (by decide)]
    exact P1
  have ecx : (b.gpr .ecx).toNat = 4 * (w.words n + 2) := by
    rw [U.other _ (by decide), A.gpr, BitVec.toNat_add, count]
    change (4 * Width.words n w + 8) % 2 ^ 32 = _
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  refine WP.mono (VG.Proof.Bignum.X86.PublicRt.zeroLoop_ok (h.full.rt.of_keeps K)
    (by omega : 0 < w.words n + 2) fit pointer ecx U.gpr) fun t ⟨O, V, Kt⟩ => ?_
  rw [m] at O
  have allK := K.trans (Kt.mono (by decide))
  exact ⟨h.keep allK (O.mono (Nat.zero_le _) (by omega)), O, V, allK⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
