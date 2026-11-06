module

import VerifiedGarbage.Proof.Ecdsa.X86.Main
public import VerifiedGarbage.Proof.Ecdsa.X86.Secp256k1.Contract
public import VerifiedGarbage.Proof.Ecdsa.X86.Layout
public import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
public import VerifiedGarbage.Spec.Ecdsa.Secp256k1
import VerifiedGarbage.Proof.Secp256k1.Point
import VerifiedGarbage.Proof.Weierstrass.X86.MontSecp256k1
import VerifiedGarbage.Proof.Secp256k1.Prime
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Ecdsa.X86.Secp256k1.Lit
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ecdsa.X86.Main
meta import VerifiedGarbage.Proof.Ecdsa.X86.Secp256k1.Contract
meta import VerifiedGarbage.Proof.Ecdsa.X86.Layout
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
meta import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
meta import VerifiedGarbage.Spec.Ecdsa.Secp256k1
meta import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Proof.Secp256k1.Point
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontSecp256k1
meta import VerifiedGarbage.Proof.Secp256k1.Prime
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ecdsa.X86.Secp256k1.Lit
meta import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Contract

/-!
# ECDSA over secp256k1 on x86 (32-bit): `Verified`

secp256k1 is a curve the proof supports (`secp256k1_ok`, and `Law` for its group law,
which the registration file supplies: `Proof.Secp256k1.law`), so `sign_ok` gives
the contract's postcondition; `ebx`, `esi`, `edi` and `ebp` are restored,
`esp` kept, and the return address too, as every write is in the working
space or `out`. Constant time by taint tracking: the only branches are on
loop counters, and every address is an argument plus a constant or a
counter.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86.Secp256k1

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

theorem secp256k1_nBits : Spec.Ecdsa.nBits secp256k1.C = 256 := by
  show Spec.Secp256k1.curve.n.log2 + 1 = 256
  have h1 : 255 ≤ Spec.Secp256k1.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h2 : Spec.Secp256k1.curve.n.log2 < 256 :=
    (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- No bit of a hash of `32` bytes is dropped. -/
theorem secp256k1_sh : secp256k1.sh = 0 := by
  unfold Cfg.sh
  rw [secp256k1_nBits]
  rfl

theorem secp256k1_ok (hI : Inv.InvSounds) : CfgOk secp256k1 where
  n0 := by decide
  n10 := by decide
  onG := Proof.Secp256k1.onCurve_G
  p_odd := by decide +kernel
  n_odd := by decide +kernel
  p_lt := by decide +kernel
  n_lt := by decide +kernel
  p_ge := by decide +kernel
  n_ge := by decide +kernel
  p_lt_2n := by decide +kernel
  minv_p := by decide +kernel
  minv_n := by decide +kernel
  len8 := by decide
  len_lo := by decide
  len_hi := by decide
  sh := by rw [secp256k1_sh]; decide

  inv_p _ := ⟨@hI _ secp256k1.C.p_ne_zero Proof.Secp256k1.p_prime,
    Inv.InvOk.ofMod (by decide +kernel) Mont.secp256k1p_ok rfl rfl⟩
  inv_n _ := ⟨@hI _ secp256k1.C.n_ne_zero Proof.Secp256k1.n_prime,
    Inv.InvOk.ofMod (by decide +kernel) Mont.secp256k1n_ok rfl rfl⟩
  fp := ⟨rfl, rfl, Mont.secp256k1p_ok⟩
  fn := ⟨rfl, rfl, Mont.secp256k1n_ok⟩

theorem pre_of {s : State} (h : signX86.pre s) : Pre secp256k1 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22⟩

/-- No instruction writes `esp`, and the calls use 28 bytes of stack. -/
theorem sign_sp : SpOk signSecp256k1 secp256k1.stk := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

theorem sign_x86 (hL : Weierstrass.Law Spec.Secp256k1.curve) (hI : Inv.InvSounds) (s : State) (hs : signX86.pre s) :
    ∃ t s', Exec isa signSecp256k1 s t s' ∧ abiPreserved s s' ∧ signX86.post s s' := by
  have hp := pre_of hs
  obtain ⟨t, s', he, K, hpost⟩ := sign_ok (secp256k1_ok hI) hL rfl sign_sp hp
  refine ⟨t, s', he, ⟨fun r hr => ?_, K.ret hp⟩, ?_⟩
  swap
  · simp only [signX86, BitVec.setWidth_append_eq_right]
    exact hpost
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact K.saved (.ebx, 0) (by decide)
  · exact K.saved (.esi, 4) (by decide)
  · exact K.saved (.edi, 8) (by decide)
  · exact K.saved (.ebp, 12) (by decide)
  · exact K.esp

/-- The hints of the constant-time checks forget the words known to hold base
addresses (`native_taint_decide_weak`): no address depends on a value loaded from
the working space, and the kernel evaluates every instruction faster with
less to look through. They keep the public slots of memory, which the
inversions by divsteps read back (their batch counter). Inside the calls of
the field arithmetic (`τ.stk ≠ []`), they keep everything: the functions read
their pointers from the words of the call's frame. -/
def weak (τ : VG.X86.Taint.T) : VG.X86.Taint.T := if τ.stk = [] then { τ with wbases := [] } else τ

/-- The taint analysis starts with the stack arguments public, and the words
holding `out` and `scratch` known to be the base addresses of the writable
regions. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [64, 8192], argLen := 24, argBases := [(4, 0), (20, 1)],
    room := 28 }

theorem wf₀ {s : State} (hp : Pre secp256k1 s) : VG.X86.Taint.Wf τ₀ s := by
  have hsc := hp.sc_fit; have ho := hp.out_fit; have hs := hp.sp_fit
  have hn9 : secp256k1.C.len = 32 := rfl
  rw [hn9] at ho
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨by simp [hp.wr, τ₀, hn9], by simpa [hp.wr, hn9] using hp.out_sc, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩ fun _ => ⟨hp.sp_lo, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth, hn9] <;> omega_using [hsc, ho]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_using [hs]) hp.ret_out hp.args_out
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_using [hs]) hp.ret_sc hp.args_sc
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.stk_out
    · exact hp.stk_sc

theorem agree₀ {s₁ s₂ : State} (h₁ : signX86.pre s₁) (h₂ : signX86.pre s₂)
    (hpub : signX86.pub s₁ s₂) : VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1, a2, a3, a4⟩ := hpub
  have hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [outR, scR, ptr, a0, a4]
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by have := hp₁.sp_fit; omega) h4 hk,
      VG.X86.Taint.argByte_eq (by have := hp₂.sp_fit; omega) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 ∨ (k - 4) / 4 = 2 ∨ (k - 4) / 4 = 3 ∨ (k - 4) / 4 = 4 := by
      omega_using [hk]
    rcases this with h | h | h | h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1
    · exact congrArg _ a2
    · exact congrArg _ a3
    · exact congrArg _ a4

theorem sign_ct : ConstantTime isa signX86.pre signX86.pub signSecp256k1 :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp)
    (by native_taint_decide_weak VG.Proof.Ecdsa.X86.Secp256k1.weak)

end VG.Proof.Ecdsa.X86.Secp256k1
