import VerifiedGarbage.Proof.Weierstrass.X86.PointVerified
import VerifiedGarbage.Proof.Weierstrass.X86.MontP192
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P192
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P224
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P256
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P384
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Spec.P192
import VerifiedGarbage.Spec.P224
import VerifiedGarbage.Spec.P256
import VerifiedGarbage.Spec.P384

/-!
# Complete point addition and doubling as functions, on x86 (32-bit): the curves

Each curve of `Spec.Weierstrass.Point.curves` is one the functions support:
its prime's Montgomery functions (`FnOk`), and the functions' constant time
by taint tracking (`τP`: the stack pointer and the argument public, the word
holding `ws` the base address of the writable region, the 20 bytes below
`esp` outside it). Fermat's little theorem in `Fin p` follows from the
curve's group law (`fermat_of_law`), which the registration files supply.
-/

namespace VG.Proof.Weierstrass.X86.Point

open VG VG.X86 VG.Impl.Weierstrass.X86.Point VG.Proof.Weierstrass.X86.Mont Spec.Weierstrass.Point
open VG.Proof.Weierstrass.Point (Fermat)

/-- The facts of a modulus's functions depend only on its `k` and `m`. -/
theorem FnOk.of_eq {M M' : Spec.Weierstrass.Mont.Modulus} (h : FnOk M) (hk : M.k = M'.k) (hm : M.m = M'.m) :
    FnOk M' := by
  obtain ⟨c, w, m, k, d⟩ := M
  obtain ⟨c', w', m', k', d'⟩ := M'
  dsimp only at hk hm
  subst hk hm
  exact ⟨h.mul, h.k9, h.nsMul, h.nsAdd, h.nsSub⟩

/-- The taint analysis starts with the stack argument public, the word
holding `ws` the base address of the writable region, and the 20 bytes the
calls use below `esp` outside it. -/
def τP : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [8192], argLen := 8, argBases := [(4, 0)], room := 20 }

theorem wfP {C : Curve} {dbl : Bool} {s : State} (h : (sumX86 C dbl).pre s) : VG.X86.Taint.Wf τP s := by
  obtain ⟨hrd, hwr, hfit, h20, hsp, haw, hrw, hzw, -⟩ := h
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨by simp [hwr, τP], by simp [hwr], ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [τP]; omega, ?_⟩, ?_⟩ fun _ => ⟨by simp only [τP]; omega, ?_⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl; simp only [BitVec.toNat_setWidth]; omega
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl
    exact VG.X86.Taint.frame_disjoint (n := 4) (by omega) hrw haw
  · intro p hp'
    simp only [τP, List.mem_cons, List.not_mem_nil, or_false] at hp'
    subst hp'
    refine ⟨by decide, ?_⟩
    simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl
    exact hzw

theorem agreeP {C : Curve} {dbl : Bool} {s₁ s₂ : State} (h₁ : (sumX86 C dbl).pre s₁) (h₂ : (sumX86 C dbl).pre s₂)
    (hpub : (sumX86 C dbl).pub s₁ s₂) : VG.X86.Taint.Agree τP s₁ s₂ := by
  obtain ⟨hesp, a0⟩ := hpub
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wfP h₁, wfP h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τP, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [h₁.2.1, h₂.2.1]; show [(⟨(arg s₁ 0).setWidth 64, 8192⟩ : Region)] = _; rw [a0]
  · simp only [τP] at hk
    rw [show VG.X86.Taint.depth τP.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by have := h₁.2.2.2.2.1; omega) h4 hk,
      VG.X86.Taint.argByte_eq (by have := h₂.2.2.2.2.1; omega) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    have : (k - 4) / 4 = 0 := by omega
    rw [this]
    exact congrArg _ a0

theorem p192_fn : FnOk (modP p192) :=
  FnOk.of_eq p192p_ok rfl (by simp only [Spec.Weierstrass.Mont.p192p, p192])

theorem p192_add_ct : ConstantTime isa (sumX86 p192 false).pre (sumX86 p192 false).pub (fn (modP p192) false) :=
  VG.Taint.constantTime (A := VG.X86.taint) τP (fun _ _ h₁ h₂ hp => agreeP h₁ h₂ hp) (by taint_decide)

theorem p192_double_ct : ConstantTime isa (sumX86 p192 true).pre (sumX86 p192 true).pub (fn (modP p192) true) :=
  VG.Taint.constantTime (A := VG.X86.taint) τP (fun _ _ h₁ h₂ hp => agreeP h₁ h₂ hp) (by taint_decide)

theorem p192_add_verified (hF : Fermat p192.p) :
    Verified X86.target (pointAdd p192) (p192.addContract X86.abi 20) :=
  sum_verified p192 p192_fn (by decide) (by decide) (by decide +kernel) (by decide +kernel) hF false p192_add_ct

theorem p192_double_verified (hF : Fermat p192.p) :
    Verified X86.target (pointDouble p192) (p192.doubleContract X86.abi 20) :=
  sum_verified p192 p192_fn (by decide) (by decide) (by decide +kernel) (by decide +kernel) hF true p192_double_ct

theorem p224_fn : FnOk (modP p224) :=
  FnOk.of_eq p224p_ok rfl (by simp only [Spec.Weierstrass.Mont.p224p, p224])

theorem p224_add_ct : ConstantTime isa (sumX86 p224 false).pre (sumX86 p224 false).pub (fn (modP p224) false) :=
  VG.Taint.constantTime (A := VG.X86.taint) τP (fun _ _ h₁ h₂ hp => agreeP h₁ h₂ hp) (by taint_decide)

theorem p224_double_ct : ConstantTime isa (sumX86 p224 true).pre (sumX86 p224 true).pub (fn (modP p224) true) :=
  VG.Taint.constantTime (A := VG.X86.taint) τP (fun _ _ h₁ h₂ hp => agreeP h₁ h₂ hp) (by taint_decide)

theorem p224_add_verified (hF : Fermat p224.p) :
    Verified X86.target (pointAdd p224) (p224.addContract X86.abi 20) :=
  sum_verified p224 p224_fn (by decide) (by decide) (by decide +kernel) (by decide +kernel) hF false p224_add_ct

theorem p224_double_verified (hF : Fermat p224.p) :
    Verified X86.target (pointDouble p224) (p224.doubleContract X86.abi 20) :=
  sum_verified p224 p224_fn (by decide) (by decide) (by decide +kernel) (by decide +kernel) hF true p224_double_ct

theorem p256_fn : FnOk (modP p256) :=
  FnOk.of_eq p256p_ok rfl (by simp only [Spec.Weierstrass.Mont.p256p, p256])

theorem p256_add_ct : ConstantTime isa (sumX86 p256 false).pre (sumX86 p256 false).pub (fn (modP p256) false) :=
  VG.Taint.constantTime (A := VG.X86.taint) τP (fun _ _ h₁ h₂ hp => agreeP h₁ h₂ hp) (by taint_decide)

theorem p256_double_ct : ConstantTime isa (sumX86 p256 true).pre (sumX86 p256 true).pub (fn (modP p256) true) :=
  VG.Taint.constantTime (A := VG.X86.taint) τP (fun _ _ h₁ h₂ hp => agreeP h₁ h₂ hp) (by taint_decide)

theorem p256_add_verified (hF : Fermat p256.p) :
    Verified X86.target (pointAdd p256) (p256.addContract X86.abi 20) :=
  sum_verified p256 p256_fn (by decide) (by decide) (by decide +kernel) (by decide +kernel) hF false p256_add_ct

theorem p256_double_verified (hF : Fermat p256.p) :
    Verified X86.target (pointDouble p256) (p256.doubleContract X86.abi 20) :=
  sum_verified p256 p256_fn (by decide) (by decide) (by decide +kernel) (by decide +kernel) hF true p256_double_ct

theorem p384_fn : FnOk (modP p384) :=
  FnOk.of_eq p384p_ok rfl (by simp only [Spec.Weierstrass.Mont.p384p, p384])

theorem p384_add_ct : ConstantTime isa (sumX86 p384 false).pre (sumX86 p384 false).pub (fn (modP p384) false) :=
  VG.Taint.constantTime (A := VG.X86.taint) τP (fun _ _ h₁ h₂ hp => agreeP h₁ h₂ hp) (by taint_decide)

theorem p384_double_ct : ConstantTime isa (sumX86 p384 true).pre (sumX86 p384 true).pub (fn (modP p384) true) :=
  VG.Taint.constantTime (A := VG.X86.taint) τP (fun _ _ h₁ h₂ hp => agreeP h₁ h₂ hp) (by taint_decide)

theorem p384_add_verified (hF : Fermat p384.p) :
    Verified X86.target (pointAdd p384) (p384.addContract X86.abi 20) :=
  sum_verified p384 p384_fn (by decide) (by decide) (by decide +kernel) (by decide +kernel) hF false p384_add_ct

theorem p384_double_verified (hF : Fermat p384.p) :
    Verified X86.target (pointDouble p384) (p384.doubleContract X86.abi 20) :=
  sum_verified p384 p384_fn (by decide) (by decide) (by decide +kernel) (by decide +kernel) hF true p384_double_ct

end VG.Proof.Weierstrass.X86.Point
