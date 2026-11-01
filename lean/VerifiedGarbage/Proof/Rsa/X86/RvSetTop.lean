module

public import VerifiedGarbage.Impl.Rsa.X86.RecoverRt
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Weierstrass.MontContract

/-! # A power-of-two modulus for the exact product of the key exponents

`setTop_ok`: the top word of the wide array `[wMod]` set to `2³¹`, through a
pointer to the array and its stride.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.RecoverRt (setTop wid)
open VG.Impl.Rsa.X86.Recover (wMod)
open VG.Proof.Rsa.X86.Keys (Ws Keep arr num S)
open VG.Proof.Rsa.X86.KeyRt

theorem setTop_ok {s : State} {B : Addr} {Z len N : Nat} (h : RtWs wid s B Z len N) (hj : wMod < N) :
    WP isa (.block setTop) s fun t =>
      RtWs wid t B Z len N ∧ Keep B (kw len) [wMod] [] s.mem t.mem ∧
      num t.mem B (kw len) wMod =
        val32 s.mem B (arr (kw len) wMod) (kw len - 1) + 2 ^ (32 * (kw len - 1)) * 2 ^ 31 ∧
      Keeps [.eax, .ecx, .edx] s t := by
  have fit := h.ws.arr_fit hj
  have nowrap := h.ws.workspace.nowrap
  have pos := h.kw_pos
  simp only [S] at fit
  unfold setTop
  refine arrPtr_ok (lenSrc h) h.lenLe h.edi (by decide) (by decide) (by omega) fun u K m p e => ?_
  refine wp_addS rfl fun u₁ U₁ _ => wp_subS rfl fun u₂ U₂ _ => wp_movS rfl fun u₃ U₃ _ => ?_
  have K₃ : Keeps [.eax, .ecx, .edx] s u₃ :=
    ((K.mono (by decide)).trans ((U₁.keeps.trans U₂.keeps).mono (by decide))).trans (U₃.keeps.mono (by decide))
  have hu := h.rt.of_keeps K₃
  have ptr : PtrAt u₃ B .eax (arr (kw len) wMod + 4 * (kw len - 1)) := by
    rw [PtrAt, U₃.other _ (by decide), U₂.gpr, U₁.gpr, BitVec.toNat_sub, BitVec.toNat_add, p, e,
      show (12 : BitVec 32).toNat = 12 from rfl]
    omega
  refine wp_storeS (ea_ptr hu ptr (d := 0) (by omega)) (ws_write hu (y := arr (kw len) wMod + 4 * (kw len - 1) + 0)
    (n := 4) (by omega)) fun t T => WP.block_nil ?_
  have mem : t.mem = s.mem.writeW (off B (arr (kw len) wMod + 4 * (kw len - 1))) (0x80000000 : BitVec 32) := by
    rw [T.mem, U₃.gpr, U₃.mem, U₂.mem, U₁.mem, m, Nat.add_zero]
  have frame := writeW32_outside s.mem B (d := arr (kw len) wMod + 4 * (kw len - 1))
    (0x80000000 : BitVec 32) (by omega)
  rw [← mem] at frame
  have Kt : Keeps [.eax, .ecx, .edx] s t := K₃.trans ((T.keeps []).mono (by decide))
  refine ⟨h.keep Kt (by decide) (by decide) (frame.mono (Nat.zero_le _) (by omega)),
    Keep.of_arr frame (by simp only [S]; omega) (by simp), ?_, Kt⟩
  change val32 _ _ _ _ = _
  have expand := val32_succ t.mem B (arr (kw len) wMod) (kw len - 1)
  rw [show kw len - 1 + 1 = kw len by omega] at expand
  rw [expand, frame.val32 (.inl (by omega)) (by omega)]
  congr 2
  simp only [w32]
  rw [mem, Mem.readW_writeW_self32]
  rfl

end VG.Proof.Rsa.X86.Recover
