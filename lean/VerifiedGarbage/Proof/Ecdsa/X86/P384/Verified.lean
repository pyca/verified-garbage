module

import VerifiedGarbage.Proof.Ecdsa.X86.Main
import VerifiedGarbage.Proof.Weierstrass.X86.MontContract
public import VerifiedGarbage.Proof.Ecdsa.X86.P384.Contract
public import VerifiedGarbage.Proof.Ecdsa.X86.Layout
public import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
public import VerifiedGarbage.Spec.Ecdsa.P384
import VerifiedGarbage.Proof.P384.Point
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Ecdsa.X86.P384.Lit
public import VerifiedGarbage.Impl.Ecdsa.P384.X86
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ecdsa.X86.Main
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontContract
meta import VerifiedGarbage.Proof.Ecdsa.X86.P384.Contract
meta import VerifiedGarbage.Proof.Ecdsa.X86.Layout
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
meta import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
meta import VerifiedGarbage.Spec.Ecdsa.P384
meta import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Proof.P384.Point
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ecdsa.X86.P384.Lit
meta import VerifiedGarbage.Impl.Ecdsa.P384.X86
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Contract

/-!
# ECDSA over P-384 on x86 (32-bit): `Verified`

P-384 is a curve the proof supports (`p384_ok`, and `Law` for its group law,
which the registration file supplies: `Proof.P384.law`), so `sign_ok` gives
the contract's postcondition; `ebx`, `esi`, `edi` and `ebp` are restored,
`esp` kept, and the return address too, as every write is in the working
space or `out`. Constant time by taint tracking: the only branches are on
loop counters, and every address is an argument plus a constant or a
counter.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86.P384

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

theorem p384_nBits : 64 * p384.n ≤ Spec.Ecdsa.nBits p384.C := by
  show 384 ≤ Spec.P384.curve.n.log2 + 1
  have : 383 ≤ Spec.P384.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- No bit of a hash of `48` bytes is dropped. -/
theorem p384_sh : p384.sh = 0 := by
  have h : 64 * 6 ≤ Spec.Ecdsa.nBits p384.C := p384_nBits
  show 8 * 48 - Spec.Ecdsa.nBits p384.C = 0; omega

theorem p384_ok : CfgOk p384 where
  n0 := by decide
  n10 := by decide
  onG := Proof.P384.onCurve_G
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
  sh := by rw [p384_sh]; decide

  inv_p h := False.elim ((by decide : ¬ (p384.n = 4 ∧ p384.C.len = 32)) h)
  inv_n h := False.elim ((by decide : ¬ (p384.n = 4 ∧ p384.C.len = 32)) h)
  fp := ⟨rfl, rfl, Mont.p384p_ok⟩
  fn := ⟨rfl, rfl, Mont.p384n_ok⟩

theorem pre_of {s : State} (h : signX86.pre s) : Pre p384 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22⟩

/-- No instruction writes `esp`, and the calls use 28 bytes of stack. -/
theorem sign_sp : SpOk signP384 p384.stk := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

theorem sign_x86 (hL : Weierstrass.Law Spec.P384.curve) (s : State) (hs : signX86.pre s) :
    ∃ t s', Exec isa signP384 s t s' ∧ abiPreserved s s' ∧ signX86.post s s' := by
  have hp := pre_of hs
  obtain ⟨t, s', he, K, hpost⟩ := sign_ok p384_ok hL rfl sign_sp hp
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

/-- The hints of the constant-time checks forget the public slots of memory
and the words known to hold base addresses (`native_taint_decide_weak`): no address
or branch depends on a value loaded from the working space, and the kernel
evaluates every instruction faster with less to look through. -/
def weak (τ : VG.X86.Taint.T) : VG.X86.Taint.T := if τ.stk = [] then { τ with slots := .empty, wbases := [] } else τ

/-- The taint analysis starts with the stack arguments public, and the words
holding `out` and `scratch` known to be the base addresses of the writable
regions. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [96, 8192], argLen := 24, argBases := [(4, 0), (20, 1)],
    room := 28 }

theorem wf₀ {s : State} (hp : Pre p384 s) : VG.X86.Taint.Wf τ₀ s := by
  have hsc := hp.sc_fit; have ho := hp.out_fit; have hs := hp.sp_fit
  have hn6 : p384.C.len = 48 := rfl
  rw [hn6] at ho
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨by simp [hp.wr, τ₀, hn6], by simpa [hp.wr, hn6] using hp.out_sc, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩ fun _ => ⟨hp.sp_lo, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth, hn6] <;> omega_using [hsc, ho]
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

theorem sign_ct : ConstantTime isa signX86.pre signX86.pub signP384 :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp)
    (by native_taint_decide_weak VG.Proof.Ecdsa.X86.P384.weak)

end VG.Proof.Ecdsa.X86.P384
