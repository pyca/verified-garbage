module

import VerifiedGarbage.Proof.Bignum.X86.PrecomputedRt.Apply
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedPostFrame
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Top
import VerifiedGarbage.Proof.Bignum.ExportEncoding
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.WordsFrame
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedPost
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedRt.Checks
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.PublicWritten
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedRt.Checks
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedRt.Key
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Stages
import VerifiedGarbage.Proof.Dsa.X86.PowABI

/-! # Precomputed public RSA at a run-time width, from the values to the result

`sized`: the values copied in, checked, and the operation or the failure
(`sized_ok`), as the contract's postcondition says of every modulus whose
values `pre` holds (`Post`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PrecomputedRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt
open VG.Impl.Bignum.X86.PrecomputedRt VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.PublicRt VG.Proof.Bignum.X86.PublicContext

/-- `PrecomputedPost`, with the stack below `sp` changed. -/
def Post (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (mem : Mem) (t : State) : Prop :=
  (∀ nB : List Byte, nB.length = len →
    Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt mem (byteAddr (args 2)) (2 * Spec.Rsa.modulusWords len)) →
    Spec.Rsa.written t.mem (byteAddr (args 0)) len (t.gpr .eax)
      (Spec.Rsa.publicOpChecked nB (Spec.Rsa.bytesAt mem (byteAddr (args 4)) (args 5).toNat)
        (Spec.Rsa.bytesAt mem (byteAddr (args 6)) len))) ∧
  Frame [⟨off base 16, bytes - 16⟩, ⟨byteAddr (args 0), len⟩, below sp 40] mem t.mem

theorem Post.of_old {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {sp : BitVec 32} {mem : Mem}
    {t : State} (P : PrecomputedPost base bytes len args mem t) : Post base bytes len args sp mem t :=
  ⟨P.1, P.2.mono (by simp)⟩

theorem val32_eq_wv (m : Mem) (P : Addr) (d W : Nat) : val32 m P d (2 * W) = wv m P d W := by
  rw [← VG.Proof.Dsa.X86.Pow.read_eq_val32, ← VG.Proof.Bignum.read_eq_wv, show 4 * (2 * W) = 8 * W by omega]

theorem _root_.VG.Proof.Bignum.X86.PrecomputedInputs.pre {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PrecomputedInputs base bytes len args s) : PreIn base bytes len args s :=
  ⟨by have := h.preFit; simp only [wb]; omega, by have := h.preRead; simpa only [wb,
    show 2 * (8 * Spec.Rsa.modulusWords len) = 16 * Spec.Rsa.modulusWords len by omega] using this,
    by have := h.preApart; simpa only [wb,
    show 2 * (8 * Spec.Rsa.modulusWords len) = 16 * Spec.Rsa.modulusWords len by omega] using this⟩

theorem sized_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PrecomputedInputs base bytes len args s) (X : Room base bytes args s)
    (E : val32 s.mem base 128 2 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat))
    (validE : Spec.Rsa.exponentValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat)) = true) :
    WP isa PrecomputedRt.sized s fun t => Post base bytes len args (s.gpr .esp) s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have hr := h.rt
  have P := h.pre
  have dims := hr.dimensions
  have nw' := hr.scratch.nowrap
  have wbe := wb_eq len
  have f7 := hr.fits (j := 7) (by decide)
  have wl := wb_ge h.lower
  have e3 : numAt len 3 = 256 + 3 * wb len := by simp only [numAt, numOff] <;> omega
  have e4 : numAt len 4 = 256 + 4 * wb len := by simp only [numAt, numOff] <;> omega
  have e5 : numAt len 5 = 256 + 5 * wb len := by simp only [numAt, numOff] <;> omega
  have n0 : numAt len 0 = 256 := by simp [numAt, numOff]
  have h256 : numOff = 256 := rfl
  unfold PrecomputedRt.sized
  refine WP.seq (WP.mono (importKey_ok hr P) fun u ⟨V0, V4, V3, O₁, K₁⟩ => ?_)
  have O₁' : Outside base 0 bytes s.mem u.mem := O₁.mono (by omega) (by omega)
  have hu := h.keep K₁ (by decide) (by decide) O₁'
  refine WP.seq (WP.mono (checks_ok hu.rt V3) fun v ⟨Z, O₂, K₂⟩ => ?_)
  simp only [checkOffset] at O₂
  have O₂' : Outside base 0 bytes u.mem v.mem := O₂.mono (by omega) (by omega)
  have hv := hu.keep K₂ (by decide) (by decide) O₂'
  have Osv : Outside base 16 (bytes - 16) s.mem v.mem :=
    (O₁.mono (by omega) (by omega)).trans (O₂.mono (by omega) (by omega))
  have Osv0 : Outside base 0 bytes s.mem v.mem := O₁'.trans O₂'
  have W := scratch_words Osv0 (by omega) (n := 2 * Spec.Rsa.modulusWords len) (by omega)
    (by simpa only [show 8 * (2 * Spec.Rsa.modulusWords len) = 16 * Spec.Rsa.modulusWords len by omega] using h.preApart)
  have Ksv : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v := (K₁.mono (by decide)).trans (K₂.mono (by decide))
  have uv : ∀ j, j ≤ 4 → val32 v.mem base (numAt len j) (nw len) = val32 u.mem base (numAt len j) (nw len) :=
    fun j hj => O₂.val32 (.inr (by simp only [numAt, numOff]; omega)) (by
      have := (hr.fits (j := j) (by omega)).1; simp only [nw, wb] at *; omega)
  -- The values, as the modulus a key's values give.
  set M := val32 s.mem (byteAddr (args 2)) 0 (nw len) with hM
  set T := val32 s.mem (byteAddr (args 2)) (wb len) (nw len) with hT
  have key : ∀ nB : List Byte, nB.length = len →
      Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt s.mem (byteAddr (args 2)) (2 * Spec.Rsa.modulusWords len)) →
      Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) len = true ∧ M = Spec.Rsa.os2ip nB ∧
        T = 2 ^ (32 * nw len) * 2 ^ (32 * nw len) % M := by
    intro nB length k
    obtain ⟨valid, modulus, power⟩ := pre_of_some length h.lower k
    have mW : M = Spec.Rsa.os2ip nB := by rw [hM, val32_eq_wv]; exact modulus
    refine ⟨valid, mW, ?_⟩
    rw [hT, show wb len = 8 * ((len + 7) / 8) from rfl, val32_eq_wv]
    show wv s.mem _ (8 * ((len + 7) / 8)) ((len + 7) / 8) = _
    rw [power, mW, ← Nat.pow_add]
    congr 2
    simp only [nw, Spec.Rsa.modulusWords]
    omega
  refine WP.ite (!Accepted M T) (by show v.zf = _; rw [Z, V0, V4]) ?_ ?_
  · intro bad
    have failed : ∀ nB : List Byte, nB.length = len →
        Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt v.mem (byteAddr (args 2)) (2 * Spec.Rsa.modulusWords len)) →
        Spec.Rsa.publicOpChecked nB (Spec.Rsa.bytesAt v.mem (byteAddr (args 4)) (args 5).toNat)
          (Spec.Rsa.bytesAt v.mem (byteAddr (args 6)) len) = none := by
      intro nB length kv
      rw [W] at kv
      obtain ⟨valid, mW, tW⟩ := key nB length kv
      have facts := valid_facts valid h.lower
      have acc : Accepted M T = true := by
        simp only [Accepted, Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨⟨by omega, by rw [tW]; exact Nat.mod_lt _ (by omega)⟩, by omega⟩
      rw [acc] at bad
      cases bad
    refine WP.mono (precomputedFailure_post hv failed) fun t ⟨Pt, Kt⟩ => ⟨Post.of_old ?_, Ksv.trans Kt⟩
    exact precomputedPost_compose h Osv Pt
  · intro good
    have acc : Accepted M T = true := by simpa using good
    simp only [Accepted, Bool.and_eq_true, decide_eq_true_eq] at acc
    obtain ⟨⟨hM1, hTM⟩, odd⟩ := acc
    have EB := scratch_bytes Osv0 (by have := h.eBound; have := h.upper; omega) h.eApart
    have XB := scratch_bytes Osv0 (by have := h.upper; omega) h.inApart
    have spv : v.gpr .esp = s.gpr .esp := Ksv.1 _ (by decide)
    have Wv : val32 v.mem base 128 2 = val32 s.mem base 128 2 := by
      rw [O₂.val32 (.inl (by decide)) (by decide), O₁.val32 (.inl (by decide)) (by decide)]
    refine WP.mono (applyInput_ok hv.rt X.hbase X.hbytes (by rw [spv]; exact X.room) (by rw [spv]; exact X.top)
      (M := M) (x := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 6)) len))
      (e := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat))
      (by rw [uv 0 (by decide), V0]) odd hM1 (by rw [uv 4 (by decide), V4]; exact hTM)
      (by rw [uv 3 (by decide), V3]) (by rw [Wv, E]) (by rw [XB])) fun t ⟨B, Ax, F, Kt⟩ => ⟨⟨?_, ?_⟩, Ksv.trans Kt⟩
    · intro nB length k
      obtain ⟨valid, mW, tW⟩ := key nB length k
      have fit : M < 2 ^ (8 * len) := by
        have B := os2ip_lt nB
        rw [length, pow256_eq] at B
        rw [mW]; exact B
      have Bv := B (by rw [uv 4 (by decide), V4]; exact tW) fit
      refine publicOutput_written length valid validE ?_ ?_
      · rw [Bv, powMod_eq, ← mW]
        split <;> simp_all only [i2osp_zero']
      · rw [Ax, ← mW]
    · rw [spv] at F
      exact ((outside_frame Osv (by omega)).mono (by simp)).trans F

end VG.Proof.Bignum.X86.PrecomputedRt
