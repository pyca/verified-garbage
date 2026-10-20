module

import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Exponentiate
import VerifiedGarbage.Proof.Mont.X86.Inverse
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Env
public import VerifiedGarbage.Impl.Mont.X86.Inverse
public import VerifiedGarbage.Proof.Mont.X86.Loop
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Load
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.MulEnv
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Output
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Mont.X86.ExponentShift
public import VerifiedGarbage.Proof.Bignum.X86.LoadBE
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops2
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBuffer
public import VerifiedGarbage.Proof.Mont.X86.Csub
public import VerifiedGarbage.Proof.Mont.X86.Rt.Step

/-! # Public RSA at a run-time width, from the inputs to the result

`sized` (`Impl/Bignum/X86/PublicRt.lean`): the modulus and the input read,
the input's acceptance kept as a mask at 144, `-M⁻¹ mod 2³²` at 152 (the
setup, `setup_ok`), one, `R² mod M`, the exponentiation, and the result
cleared unless the input was accepted and written out (`sized_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Mont.X86.Dynamic

/-- The acceptance mask and the inverse. -/
theorem setup_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : RtIn base bytes len args s) {c : Bool} (hc : s.gpr .ecx = cmask c)
    (hodd : val32 s.mem base numOff (nw len) % 2 = 1) :
    WP isa (.block (([.store (sc PublicFn.acceptanceOffset) .ecx] : List Instr) ++ VG.Impl.Mont.X86.Dynamic.setupInverse numOff invOff)) s fun t =>
      t.mem.readW (off base PublicFn.acceptanceOffset) 32 = cmask c ∧
      (val32 s.mem base numOff (nw len) * w32 t.mem base invOff + 1) % 2 ^ 32 = 0 ∧
      Outside base PublicFn.acceptanceOffset 12 s.mem t.mem ∧ Keeps clob s t := by
  have nw' := h.scratch.nowrap
  have f0 := (h.fits (j := 0) (by decide)).1
  have dims := h.dimensions
  have n0 : numAt len 0 = 256 := by simp [numAt, numOff]
  have wbe := wb_eq len
  rw [n0] at f0
  have b264 : 264 ≤ bytes := by have := dims.1; simp only [wb] at f0; omega
  simp only [List.cons_append, List.nil_append, PublicFn.acceptanceOffset] at *
  refine wp_storeS (h.scratch.ea (d := 144) (by omega)) (h.scratch.write (d := 144) (n := 4) (by omega))
    fun u m => ?_
  have hu : Scr u base bytes := h.scratch.of_keeps (m.keeps []) (by decide) (by decide)
  have O₁ : Outside base 144 4 s.mem u.mem := by rw [m.mem]; exact writeW32_outside _ _ _ (by omega)
  have w₁ : w32 u.mem base numOff = w32 s.mem base numOff :=
    Outside.w32 O₁ (by simp only [numOff]; omega) (by simp only [numOff]; omega)
  have hodd' : w32 u.mem base numOff % 2 = 1 := by
    rw [w₁]
    obtain ⟨k, hk⟩ : ∃ k, nw len = k + 1 := ⟨nw len - 1, by simp only [nw]; omega⟩
    rw [hk, val32_parity] at hodd; exact hodd
  refine WP.mono (setupInverse_ok hu (mo := numOff) (inv := invOff) (by simp only [numOff]; omega) (by simp only [invOff]; omega) hodd')
    fun t ⟨I, O₂, K⟩ => ⟨?_, ?_, ?_, (m.keeps _).trans K⟩
  · have a₂ : t.mem.readW (off base 144) 32 = u.mem.readW (off base 144) 32 :=
      BitVec.eq_of_toNat_eq (Outside.w32 O₂ (by simp only [invOff]; omega) (by omega))
    rw [a₂, m.mem, Mem.readW_writeW_self32, hc]
  · rw [w₁] at I
    obtain ⟨k, hk⟩ : ∃ k, nw len = k + 1 := ⟨nw len - 1, by simp only [nw]; omega⟩
    rw [hk, val32, Nat.add_mul, Nat.mul_assoc, Nat.add_right_comm, Nat.add_mul_mod_self_left]
    exact I
  · exact (O₁.mono (by decide) (by decide)).trans (O₂.mono (by simp [invOff]) (by simp [invOff]))

/-- Everything before the exponentiation: `Env`, with `R² mod M` (number 4), one (number 3), the input
(number 1), the exponent and the input's acceptance. -/
theorem prepare_ok {s : State} {base : Addr} {bytes len e : Nat} {args : Nat → BitVec 32}
    (h : PublicInputs base bytes len args s) (hbase : (args 8).toNat = base.toNat)
    (R : CallRoom (s.gpr .esp) base bytes) (top : (s.gpr .esp).toNat + 44 ≤ 2 ^ 32)
    (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len = true)
    (exponent : val32 s.mem base 128 2 = e) {m x : Nat}
    (hm : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len) = m)
    (hx : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 6)) len) = x) :
    WP isa prepare s fun u =>
      Env base bytes len args m u ∧
      val32 u.mem base (numAt len 4) (nw len) = 2 ^ (32 * nw len) * 2 ^ (32 * nw len) % m ∧
      val32 u.mem base (numAt len 3) (nw len) = 1 ∧ val32 u.mem base (numAt len 1) (nw len) = x ∧
      val32 u.mem base 128 2 = e ∧ u.mem.readW (off base 144) 32 = cmask (decide (x < m)) ∧
      Outside base 16 (bytes - 16) s.mem u.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  subst hm hx
  have nL := h.nLen
  have nF := h.nFit
  have nR := h.nRead
  have nA := h.nApart
  replace h := h.rt
  set m := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len) with hm
  set x := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 6)) len) with hx
  have dims := h.dimensions
  have facts := valid_facts valid h.lower
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
  have modFit : m < 2 ^ (8 * len) := by
    have B := os2ip_lt (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)
    simpa only [bytesAt_length, pow256_eq] using B
  unfold prepare
  -- The modulus and the input.
  refine WP.seq (WP.mono (load_ok h (j := 0) (p := 2) (l := 3) (by decide) (by decide) (by decide) nL nF
    nR nA) fun u₁ ⟨N₁, O₁, K₁⟩ => ?_)
  have O₁' : Outside base 0 bytes s.mem u₁.mem := O₁.mono (by omega) (by omega)
  have h₁ := h.keep K₁ (by decide) (by decide) O₁'
  have xs := scratch_bytes O₁' (by have := h.upper; omega) h.inApart
  refine WP.seq (WP.mono (load_ok h₁ (j := 1) (p := 6) (l := 7) (by decide) (by decide) (by decide) h.inLen h.inFit
    h₁.inRead h.inApart) fun u₂ ⟨X₂, O₂, K₂⟩ => ?_)
  rw [xs] at X₂
  have h₂ := h₁.keep K₂ (by decide) (by decide) (O₂.mono (by omega) (by omega))
  have N₂ : val32 u₂.mem base (numAt len 0) (nw len) = m := by
    rw [O₂.val32 (.inl (by omega)) (by omega), N₁]
  refine WP.seq (WP.mono (compare_ok h₂) fun u₃ ⟨M₃, C₃, K₃⟩ => ?_)
  rw [X₂, N₂] at C₃
  have h₃ := h₂.keep K₃ (by decide) (by decide) (by rw [M₃]; exact Outside.refl _ _ _ _)
  -- The acceptance and the inverse.
  refine WP.seq (WP.mono (setup_ok h₃ C₃ (by rw [M₃, ← n0, N₂]; exact facts.1)) fun u₄ ⟨A₄, I₄, O₄, K₄⟩ => ?_)
  simp only [PublicFn.acceptanceOffset] at A₄
  have h₄ := h₃.keep K₄ (by decide) (by decide) (O₄.mono (by omega) (by omega))
  have M₄ : val32 u₄.mem base numOff (nw len) = m := by
    rw [Outside.val32 O₄ (.inr (by omega)) (by omega), M₃, ← n0, N₂]
  have K₁₄ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₄ :=
    (((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide))).trans (K₄.mono (by decide))
  have sp₄ : u₄.gpr .esp = s.gpr .esp := K₁₄.1 _ (by decide)
  have E₄ : Env base bytes len args m u₄ := ⟨h₄, by rw [sp₄]; exact R, M₄,
    by rw [M₃, ← n0, N₂] at I₄; exact I₄, by rw [sp₄]; exact top⟩
  -- One, and `R² mod M`.
  refine WP.seq (WP.mono (setOne_ok h₄ (j := 3) (by decide)) fun u₅ ⟨O₅, One₅, K₅⟩ => ?_)
  have E₅ := E₄.keep K₅ (by decide) (by decide) (Outside.chg O₅ (.inr ⟨by omega, by omega⟩))
  refine WP.mono (powerTwo_ok E₅.pi hbase (by rw [n0, E₅.mod]; exact facts.2.1))
    fun u₆ ⟨O₆, T₆, d₆, K₆⟩ => ?_
  have K₆' := Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .ebp, .esi]) K₆ d₆
  have E₆ := E₅.keep K₆' (by decide) (by decide) (Outside.chg O₆ (.inr ⟨by omega, by omega⟩))
  have K₁₆ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₆ := (K₁₄.trans (K₅.mono (by decide))).trans K₆'
  have sp₆ : u₆.gpr .esp = s.gpr .esp := K₁₆.1 _ (by decide)
  have hT : val32 u₆.mem base (numAt len 4) (nw len) = 2 ^ (32 * nw len) * 2 ^ (32 * nw len) % m := by
    rw [T₆, n0, E₅.mod, ← Nat.pow_add, show 16 * wb len = 32 * nw len + 32 * nw len by omega]
  have hO : val32 u₆.mem base (numAt len 3) (nw len) = 1 := by
    rw [O₆.val32 (.inl (by omega)) (by omega), One₅]
  have X₆ : val32 u₆.mem base (numAt len 1) (nw len) = x := by
    rw [O₆.val32 (.inl (by omega)) (by omega), O₅.val32 (.inl (by omega)) (by omega),
      Outside.val32 O₄ (.inr (by omega)) (by omega), M₃, X₂]
  have W₆ : val32 u₆.mem base 128 2 = e := by
    rw [O₆.val32 (.inl (by omega)) (by omega), O₅.val32 (.inl (by omega)) (by omega),
      Outside.val32 O₄ (.inl (by omega)) (by omega), M₃, O₂.val32 (.inl (by omega)) (by omega),
      O₁.val32 (.inl (by omega)) (by omega), exponent]
  have a₆ : u₆.mem.readW (off base 144) 32 = cmask (decide (x < m)) := by
    rw [← A₄]
    exact BitVec.eq_of_toNat_eq ((O₆.w32 (.inl (by omega)) (by omega)).trans (O₅.w32 (.inl (by omega)) (by omega)))
  have S₆ : Outside base 16 (bytes - 16) s.mem u₆.mem :=
    (((((O₁.mono (by omega) (by omega)).trans (O₂.mono (by omega) (by omega))).trans
      (by rw [M₃]; exact Outside.refl _ _ _ _)).trans (O₄.mono (by omega) (by omega))).trans
      (O₅.mono (by omega) (by omega))).trans (O₆.mono (by omega) (by omega))
  exact ⟨E₆, hT, hO, X₆, W₆, a₆, S₆, K₁₆⟩

/-- The operation on a valid modulus: the result written out when the input is below the modulus, and zeros
otherwise. -/
theorem sized_ok {s : State} {base : Addr} {bytes len e : Nat} {args : Nat → BitVec 32}
    (h : PublicInputs base bytes len args s) (hbase : (args 8).toNat = base.toNat)
    (hbytes : bytes = (args 9).toNat * 8) (R : CallRoom (s.gpr .esp) base bytes)
    (top : (s.gpr .esp).toNat + 44 ≤ 2 ^ 32)
    (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len = true)
    (exponent : val32 s.mem base 128 2 = e) :
    WP isa sized s fun t =>
      let m := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)
      let x := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 6)) len)
      Spec.Rsa.bytesAt t.mem (byteAddr (args 0)) len = Spec.Rsa.i2osp (if x < m then x ^ e % m else 0) len ∧
      t.gpr .eax = BitVec.ofNat 32 (decide (x < m)).toNat ∧
      Frame [⟨off base 16, bytes - 16⟩, ⟨byteAddr (args 0), len⟩, below (s.gpr .esp) 40] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have hP := h
  replace h := h.rt
  set m := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len) with hm
  set x := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 6)) len) with hx
  have dims := h.dimensions
  have facts := valid_facts valid h.lower
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
  have modFit : m < 2 ^ (8 * len) := by
    have B := os2ip_lt (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)
    simpa only [bytesAt_length, pow256_eq] using B
  unfold sized
  refine WP.seq (WP.mono (prepare_ok hP hbase R top valid exponent hm.symm hx.symm) fun u₆ ⟨E₆, hT, hO, X₆, W₆, a₆, S₆, K₁₆⟩ => ?_)
  have sp₆ : u₆.gpr .esp = s.gpr .esp := K₁₆.1 _ (by decide)
  -- The exponentiation.
  refine WP.seq (WP.mono (exponentiate_ok E₆ hbase hbytes facts.2.1 hT hO) fun u₇ ⟨E₇, F₇, Y₇, K₇⟩ => ?_)
  rw [X₆, W₆] at Y₇
  rw [sp₆] at F₇
  have A₇ : u₇.mem.readW (off base 144) 32 = cmask (decide (x < m)) := by
    have a₇ : u₇.mem.readW (off base 144) 32 = u₆.mem.readW (off base 144) 32 := by
      simp only [Mem.readW]
      rw [frame_read F₇ R nw' (by omega) (d := 144) (k := 4) (by omega) (.inr ⟨by decide, by omega⟩)]
    rw [a₇, a₆]
  -- The result cleared unless the input was accepted, and written out.
  refine WP.seq (WP.mono (maskOut_ok E₇.pi (c := decide (x < m)) A₇) fun u₈ ⟨O₈, V₈, K₈⟩ => ?_)
  have h₈ := E₇.pi.keep K₈ (by decide) (by decide) (O₈.mono (by omega) (by omega))
  rw [Y₇] at V₈
  have fitv : val32 u₈.mem base (numAt len 2) (nw len) < 2 ^ (8 * len) := by
    rw [V₈]; split
    · exact Nat.lt_trans (Nat.mod_lt _ (by omega)) modFit
    · exact Nat.two_pow_pos _
  refine WP.mono (write_ok h₈ fitv) fun t ⟨B, Ax, Ft, Kt⟩ => ⟨?_, ?_, ?_, ?_⟩
  · rw [B, V₈]; simp only [decide_eq_true_eq]
  · have a₈ : u₈.mem.readW (off base PublicFn.acceptanceOffset) 32 = cmask (decide (x < m)) := by
      rw [← A₇]
      exact BitVec.eq_of_toNat_eq (O₈.w32 (.inl (by simp only [PublicFn.acceptanceOffset]; omega)) (by
        simp only [PublicFn.acceptanceOffset]; omega))
    rw [Ax, a₈]
    cases decide (x < m) <;> rfl
  · have G₆ := ((outside_frame S₆ (by omega)).mono (rs' := [⟨off base 16, bytes - 16⟩, ⟨byteAddr (args 0), len⟩,
      below (s.gpr .esp) 40]) (by simp))
    have G₇ : Frame [⟨off base 16, bytes - 16⟩, ⟨byteAddr (args 0), len⟩, below (s.gpr .esp) 40] u₆.mem u₇.mem := by
      refine F₇.sub fun r hr => ?_
      simp only [Chg, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., sub_off (by omega) (by omega)⟩
      · exact ⟨_, List.mem_cons_self .., sub_off (by omega) (by omega)⟩
      · exact ⟨below (s.gpr .esp) 40, by simp, fun _ h => h⟩
    have G₈ := ((outside_frame (O₈.mono (o' := 16) (n' := bytes - 16) (by omega) (by omega)) (by omega)).mono
      (rs' := [⟨off base 16, bytes - 16⟩, ⟨byteAddr (args 0), len⟩, below (s.gpr .esp) 40]) (by simp))
    exact ((G₆.trans G₇).trans G₈).trans (Ft.mono (by simp))
  · exact ((K₁₆.trans K₇).trans (K₈.mono (by decide))).trans (Kt.mono (by decide))

end VG.Proof.Bignum.X86.PublicRt
