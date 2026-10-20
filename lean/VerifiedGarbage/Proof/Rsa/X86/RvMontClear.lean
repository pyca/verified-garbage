module

public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.RvBase
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Clearing a Montgomery result's two extra narrow-array words

`clrTop_ok`: the words `w - 2` and `w - 1` of narrow array `j` zeroed, so that
its number is the callee's result of `w - 2` words.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.RecoverRt (clrTop nar)
open VG.Proof.Rsa.X86.Keys (Ws Keep arr num S)
open VG.Proof.Rsa.X86.KeyRt

theorem clrTop_ok {s : State} {B : Addr} {Z len N : Nat} (h : RtWs nar s B Z len N) {j : Nat} (hj : j < N)
    (two : 2 ≤ kw len) :
    WP isa (.block (clrTop j)) s fun t =>
      RtWs nar t B Z len N ∧ Keep B (kw len) [j] [] s.mem t.mem ∧
      num t.mem B (kw len) j = val32 s.mem B (arr (kw len) j) (kw len - 2) ∧
      Keeps [.eax, .ecx, .edx] s t := by
  have fit := h.ws.arr_fit hj
  have nowrap := h.ws.workspace.nowrap
  simp only [S] at fit
  unfold clrTop
  refine arrPtr_ok (lenSrc h) h.lenLe h.edi (by decide) (by decide) (by omega) fun u K m p e => ?_
  refine wp_addS rfl fun u₁ U₁ _ => wp_subS rfl fun u₂ U₂ _ => wp_movS rfl fun u₃ U₃ _ => ?_
  have K₃ : Keeps [.eax, .ecx, .edx] s u₃ :=
    ((K.mono (by decide)).trans ((U₁.keeps.trans U₂.keeps).mono (by decide))).trans (U₃.keeps.mono (by decide))
  have hu := h.rt.of_keeps K₃
  have ptr : PtrAt u₃ B .eax (arr (kw len) j + 4 * (kw len - 2)) := by
    rw [PtrAt, U₃.other _ (by decide), U₂.gpr, U₁.gpr, BitVec.toNat_sub, BitVec.toNat_add, p, e,
      show (16 : BitVec 32).toNat = 16 from rfl]
    omega
  have ecx₃ : u₃.gpr .ecx = 0 := U₃.gpr
  refine wp_storeS (ea_ptr hu ptr (d := 0) (by omega))
    (ws_write hu (y := arr (kw len) j + 4 * (kw len - 2) + 0) (n := 4) (by omega)) fun u₄ T₄ => ?_
  have hu₄ := hu.of_keeps (T₄.keeps [])
  have ptr₄ : PtrAt u₄ B .eax (arr (kw len) j + 4 * (kw len - 2)) := by rw [PtrAt, T₄.gpr]; exact ptr
  refine wp_storeS (ea_ptr hu₄ ptr₄ (d := 4) (by omega))
    (ws_write hu₄ (y := arr (kw len) j + 4 * (kw len - 2) + 4) (n := 4) (by omega)) fun t T => WP.block_nil ?_
  have val0 : u₄.gpr .ecx = 0 := by rw [T₄.gpr]; exact ecx₃
  have mem : t.mem = (s.mem.writeW (off B (arr (kw len) j + 4 * (kw len - 2))) (0 : BitVec 32)).writeW
      (off B (arr (kw len) j + 4 * (kw len - 2) + 4)) (0 : BitVec 32) := by
    rw [T.mem, val0, T₄.mem, ecx₃, U₃.mem, U₂.mem, U₁.mem, m, Nat.add_zero]
  have f₁ := writeW32_outside s.mem B (d := arr (kw len) j + 4 * (kw len - 2)) (0 : BitVec 32) (by omega)
  have f₂ := writeW32_outside (s.mem.writeW (off B (arr (kw len) j + 4 * (kw len - 2))) (0 : BitVec 32)) B
    (d := arr (kw len) j + 4 * (kw len - 2) + 4) (0 : BitVec 32) (by omega)
  rw [← mem] at f₂
  have O : Outside B (arr (kw len) j + 4 * (kw len - 2)) 8 s.mem t.mem :=
    (f₁.mono (Nat.le_refl _) (by omega)).trans (f₂.mono (by omega) (by omega))
  have Kt : Keeps [.eax, .ecx, .edx] s t := (K₃.trans ((T₄.keeps []).mono (by decide))).trans ((T.keeps []).mono (by decide))
  refine ⟨h.keep Kt (by decide) (by decide) (O.mono (Nat.zero_le _) (by omega)),
    Keep.of_arr O (by simp only [S]; omega) (by simp), ?_, Kt⟩
  change val32 _ _ _ _ = _
  have split := val32_append t.mem B (arr (kw len) j) (kw len - 2) 2
  rw [show kw len - 2 + 2 = kw len by omega] at split
  rw [split, O.val32 (.inl (by omega)) (by omega)]
  have w0 : w32 t.mem B (arr (kw len) j + 4 * (kw len - 2)) = 0 := by
    rw [f₂.w32 (.inl (by omega)) (by omega), w32_write_self]; rfl
  have w1 : w32 t.mem B (arr (kw len) j + 4 * (kw len - 2) + 4) = 0 := by
    rw [mem, w32_write_self]; rfl
  have zero : val32 t.mem B (arr (kw len) j + 4 * (kw len - 2)) 2 = 0 := by
    rw [val32_succ, val32_succ]
    simp only [val32, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.pow_zero, w0, w1]
  rw [zero, Nat.mul_zero, Nat.add_zero]

end VG.Proof.Rsa.X86.Recover
