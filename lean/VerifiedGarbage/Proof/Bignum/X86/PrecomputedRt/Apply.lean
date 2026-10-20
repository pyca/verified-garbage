module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedRt.Checks
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Sized
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.ExpWeak
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.MulEnv
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Env
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Env
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Env
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Load
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.ReadPrefix
public import VerifiedGarbage.Proof.Bignum.X86.ExponentBits
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedRt.Copy
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Call
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Callee
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Double
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Exp
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Exponentiate
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.MulArgs
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Output
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Reduce
public import VerifiedGarbage.Proof.Dsa.Arithmetic
public import VerifiedGarbage.Proof.Dsa.X86.PowABI
public import VerifiedGarbage.Proof.Dsa.X86.PowEntry
public import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Proof.Mont.Read
public import VerifiedGarbage.Proof.Mont.X86.ArgFar
public import VerifiedGarbage.Proof.Mont.X86.ArgWs
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
public import VerifiedGarbage.Proof.Mont.X86.ContextMath
public import VerifiedGarbage.Proof.Mont.X86.Dynamic
public import VerifiedGarbage.Proof.Mont.X86.DynamicOps
public import VerifiedGarbage.Proof.Mont.X86.ExponentShift
public import VerifiedGarbage.Proof.Mont.X86.Inverse
public import VerifiedGarbage.Proof.Mont.X86.Ops
public import VerifiedGarbage.Proof.Mont.X86.Row
public import VerifiedGarbage.Proof.Mont.X86.Rt.ABI
public import VerifiedGarbage.Proof.Mont.X86.Rt.Args
public import VerifiedGarbage.Proof.Mont.X86.Rt.Blocks
public import VerifiedGarbage.Proof.Mont.X86.Rt.Body
public import VerifiedGarbage.Proof.Mont.X86.Rt.Csub
public import VerifiedGarbage.Proof.Mont.X86.Rt.Front
public import VerifiedGarbage.Proof.Mont.X86.Rt.Row
public import VerifiedGarbage.Proof.Mont.X86.Rt.RowFull
public import VerifiedGarbage.Proof.Mont.X86.Rt.Rows
public import VerifiedGarbage.Proof.Mont.X86.Rt.Save
public import VerifiedGarbage.Proof.Mont.X86.Rt.Stages
public import VerifiedGarbage.Proof.Mont.X86.Rt.Sub
public import VerifiedGarbage.Proof.Mont.X86.Rt.Verified
public import VerifiedGarbage.Proof.Mont.X86.Rt.Zero
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Spec.Sha1
public import VerifiedGarbage.Spec.Sha256

/-! # The operation from the precomputed values, once they pass the checks

`applyInput`: the input read and compared with `M`, `-M⁻¹ mod 2³²`, the
exponentiation, and the result cleared unless the input is below `M` and
written out (`applyInput_ok`). From any `R²` below `M` it ends; its result is
`x^e mod M` when number 4 is `R² mod M` and `M` fits the output.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PrecomputedRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt
open VG.Impl.Bignum.X86.PrecomputedRt VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.PublicRt

/-- The input read and compared with `M`, the acceptance and `-M⁻¹ mod 2³²`: `Env`, and what the
exponentiation and the output need. -/
theorem applyPrefix_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : RtIn base bytes len args s)
    (R : CallRoom (s.gpr .esp) base bytes) (top : (s.gpr .esp).toNat + 44 ≤ 2 ^ 32) {M e x : Nat}
    (N : val32 s.mem base (numAt len 0) (nw len) = M) (odd : M % 2 = 1)
    (exponent : val32 s.mem base 128 2 = e)
    (hx : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 6)) len) = x) :
    WP isa applyPrefix s fun u =>
      Env base bytes len args M u ∧ u.mem.readW (off base 144) 32 = cmask (decide (x < M)) ∧
      val32 u.mem base (numAt len 4) (nw len) = val32 s.mem base (numAt len 4) (nw len) ∧
      val32 u.mem base (numAt len 3) (nw len) = val32 s.mem base (numAt len 3) (nw len) ∧
      val32 u.mem base (numAt len 1) (nw len) = x ∧ val32 u.mem base 128 2 = e ∧
      Outside base 16 (bytes - 16) s.mem u.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have dims := h.dimensions
  have nw' := h.scratch.nowrap
  have wbe := wb_eq len
  have f7 := h.fits (j := 7) (by decide)
  have wl := wb_ge h.lower
  have e1 : numAt len 1 = 256 + wb len := by simp only [numAt, numOff] <;> omega
  have e2 : numAt len 2 = 256 + 2 * wb len := by simp only [numAt, numOff] <;> omega
  have e3 : numAt len 3 = 256 + 3 * wb len := by simp only [numAt, numOff] <;> omega
  have e4 : numAt len 4 = 256 + 4 * wb len := by simp only [numAt, numOff] <;> omega
  have e5 : numAt len 5 = 256 + 5 * wb len := by simp only [numAt, numOff] <;> omega
  have e7 : numAt len 7 = 256 + 7 * wb len := by simp only [numAt, numOff] <;> omega
  have n0 : numAt len 0 = numOff := by simp [numAt]
  have h256 : numOff = 256 := rfl
  have ha : PublicFn.acceptanceOffset = 144 := rfl
  unfold applyPrefix
  -- The input.
  refine WP.seq (WP.mono (load_ok h (j := 1) (p := 6) (l := 7) (by decide) (by decide) (by decide) h.inLen h.inFit
    h.inRead h.inApart) fun u₂ ⟨X₂, O₂, K₂⟩ => ?_)
  rw [hx] at X₂
  have h₂ := h.keep K₂ (by decide) (by decide) (O₂.mono (by omega) (by omega))
  have N₂ : val32 u₂.mem base (numAt len 0) (nw len) = M := by
    rw [O₂.val32 (d := numAt len 0) (k := nw len) (.inl (by omega)) (by omega), N]
  refine WP.seq (WP.mono (compare_ok h₂) fun u₃ ⟨M₃, C₃, K₃⟩ => ?_)
  rw [X₂, N₂] at C₃
  have h₃ := h₂.keep K₃ (by decide) (by decide) (by rw [M₃]; exact Outside.refl _ _ _ _)
  -- The acceptance and the inverse.
  refine WP.mono (setup_ok h₃ C₃ (by rw [M₃, ← n0, N₂]; exact odd)) fun u₄ ⟨A₄, I₄, O₄, K₄⟩ => ?_
  simp only [PublicFn.acceptanceOffset] at A₄
  have h₄ := h₃.keep K₄ (by decide) (by decide) (O₄.mono (by omega) (by omega))
  have M₄ : val32 u₄.mem base numOff (nw len) = M := by
    rw [Outside.val32 O₄ (.inr (by omega)) (by omega), M₃, ← n0, N₂]
  have K₁₄ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₄ :=
    ((K₂.mono (by decide)).trans (K₃.mono (by decide))).trans (K₄.mono (by decide))
  have sp₄ : u₄.gpr .esp = s.gpr .esp := K₁₄.1 _ (by decide)
  have E₄ : Env base bytes len args M u₄ := ⟨h₄, by rw [sp₄]; exact R, M₄,
    by rw [M₃, ← n0, N₂] at I₄; exact I₄, by rw [sp₄]; exact top⟩
  have pv : ∀ d, d + 4 * nw len ≤ numAt len 1 ∨ numAt len 1 + wb len ≤ d → 140 + 16 ≤ d → d + 4 * nw len ≤ bytes →
      val32 u₄.mem base d (nw len) = val32 s.mem base d (nw len) := fun d hd hd' hb => by
    rw [Outside.val32 O₄ (.inr (by omega)) (by omega), M₃, O₂.val32 hd (by omega)]
  have T₄ := pv (numAt len 4) (.inr (by omega)) (by omega) (by omega)
  have One₄ := pv (numAt len 3) (.inr (by omega)) (by omega) (by omega)
  have X₄ : val32 u₄.mem base (numAt len 1) (nw len) = x := by
    rw [Outside.val32 O₄ (.inr (by omega)) (by omega), M₃, X₂]
  have W₄ : val32 u₄.mem base 128 2 = e := by
    rw [Outside.val32 O₄ (.inl (by omega)) (by omega), M₃, O₂.val32 (.inl (by omega)) (by omega), exponent]
  have S₄ : Outside base 16 (bytes - 16) s.mem u₄.mem :=
    ((O₂.mono (by omega) (by omega)).trans (by rw [M₃]; exact Outside.refl _ _ _ _)).trans
      (O₄.mono (by omega) (by omega))
  exact ⟨E₄, A₄, T₄, One₄, X₄, W₄, S₄, K₁₄⟩

theorem applyInput_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : RtIn base bytes len args s) (hbase : (args 8).toNat = base.toNat)
    (hbytes : bytes = (args 9).toNat * 8) (R : CallRoom (s.gpr .esp) base bytes)
    (top : (s.gpr .esp).toNat + 44 ≤ 2 ^ 32) {M e x : Nat}
    (N : val32 s.mem base (numAt len 0) (nw len) = M) (odd : M % 2 = 1) (hM1 : 1 < M)
    (T : val32 s.mem base (numAt len 4) (nw len) < M) (one : val32 s.mem base (numAt len 3) (nw len) = 1)
    (exponent : val32 s.mem base 128 2 = e)
    (hx : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 6)) len) = x) :
    WP isa applyInput s fun t =>
      (val32 s.mem base (numAt len 4) (nw len) = 2 ^ (32 * nw len) * 2 ^ (32 * nw len) % M → M < 2 ^ (8 * len) →
        Spec.Rsa.bytesAt t.mem (byteAddr (args 0)) len = Spec.Rsa.i2osp (if x < M then x ^ e % M else 0) len) ∧
      t.gpr .eax = BitVec.ofNat 32 (decide (x < M)).toNat ∧
      Frame [⟨off base 16, bytes - 16⟩, ⟨byteAddr (args 0), len⟩, below (s.gpr .esp) 40] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have dims := h.dimensions
  have nw' := h.scratch.nowrap
  have wbe := wb_eq len
  have f7 := h.fits (j := 7) (by decide)
  have wl := wb_ge h.lower
  have e1 : numAt len 1 = 256 + wb len := by simp only [numAt, numOff] <;> omega
  have e2 : numAt len 2 = 256 + 2 * wb len := by simp only [numAt, numOff] <;> omega
  have e5 : numAt len 5 = 256 + 5 * wb len := by simp only [numAt, numOff] <;> omega
  have h256 : numOff = 256 := rfl
  have ha : PublicFn.acceptanceOffset = 144 := rfl
  unfold applyInput
  refine WP.seq (WP.mono (applyPrefix_ok h R top N odd exponent hx) fun u₄ ⟨E₄, A₄, T₄, One₄, X₄, W₄, S₄, K₁₄⟩ => ?_)
  have sp₄ : u₄.gpr .esp = s.gpr .esp := K₁₄.1 _ (by decide)
  -- The exponentiation.
  refine WP.seq (WP.mono (exponentiate_cond_ok E₄ hbase hbytes hM1 (by rw [T₄]; exact T) (by rw [One₄, one]))
    fun u₇ ⟨E₇, F₇, K₇, Y₇⟩ => ?_)
  rw [X₄, W₄, T₄] at Y₇
  rw [sp₄] at F₇
  have A₇ : u₇.mem.readW (off base 144) 32 = cmask (decide (x < M)) := by
    have a₇ : u₇.mem.readW (off base 144) 32 = u₄.mem.readW (off base 144) 32 := by
      simp only [Mem.readW]
      rw [frame_read F₇ R nw' (by omega) (d := 144) (k := 4) (by omega) (.inr ⟨by decide, by omega⟩)]
    rw [a₇, A₄]
  -- The result cleared unless the input was accepted, and written out.
  refine WP.seq (WP.mono (maskOut_ok E₇.pi (c := decide (x < M)) A₇) fun u₈ ⟨O₈, V₈, K₈⟩ => ?_)
  have h₈ := E₇.pi.keep K₈ (by decide) (by decide) (O₈.mono (by omega) (by omega))
  refine WP.mono (write_any_ok h₈) fun t ⟨B, Ax, Ft, Kt⟩ => ⟨?_, ?_, ?_, ?_⟩
  · intro hT fit
    have V := Y₇ hT
    rw [V] at V₈
    have fitv : val32 u₈.mem base (numAt len 2) (nw len) < 2 ^ (8 * len) := by
      rw [V₈]; split
      · exact Nat.lt_trans (Nat.mod_lt _ (by omega)) fit
      · exact Nat.two_pow_pos _
    rw [B fitv, V₈]; simp only [decide_eq_true_eq]
  · have a₈ : u₈.mem.readW (off base PublicFn.acceptanceOffset) 32 = cmask (decide (x < M)) := by
      rw [← A₇]
      exact BitVec.eq_of_toNat_eq (O₈.w32 (.inl (by simp only [PublicFn.acceptanceOffset]; omega)) (by
        simp only [PublicFn.acceptanceOffset]; omega))
    rw [Ax, a₈]
    cases decide (x < M) <;> rfl
  · have G₄ := ((outside_frame S₄ (by omega)).mono (rs' := [⟨off base 16, bytes - 16⟩, ⟨byteAddr (args 0), len⟩,
      below (s.gpr .esp) 40]) (by simp))
    have G₇ : Frame [⟨off base 16, bytes - 16⟩, ⟨byteAddr (args 0), len⟩, below (s.gpr .esp) 40] u₄.mem u₇.mem := by
      refine F₇.sub fun r hr => ?_
      simp only [Chg, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., sub_off (by omega) (by omega)⟩
      · exact ⟨_, List.mem_cons_self .., sub_off (by omega) (by omega)⟩
      · exact ⟨below (s.gpr .esp) 40, by simp, fun _ h => h⟩
    have G₈ := ((outside_frame (O₈.mono (o' := 16) (n' := bytes - 16) (by omega) (by omega)) (by omega)).mono
      (rs' := [⟨off base 16, bytes - 16⟩, ⟨byteAddr (args 0), len⟩, below (s.gpr .esp) 40]) (by simp))
    exact ((G₄.trans G₇).trans G₈).trans (Ft.mono (by simp))
  · exact ((K₁₄.trans K₇).trans (K₈.mono (by decide))).trans (Kt.mono (by decide))

end VG.Proof.Bignum.X86.PrecomputedRt
