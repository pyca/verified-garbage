module

public import VerifiedGarbage.Proof.Rsa.X86.RvGcd
import VerifiedGarbage.Proof.Rsa.X86.RvOps
import VerifiedGarbage.Proof.Rsa.X86.RvWrite
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Framework.Omega

/-! # Preparing the division of the modulus by the recovered GCD -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Impl.Rsa.X86.RecoverRt (nar)
open VG.Impl.Rsa.X86.KeyRt (arrPtr)
open VG.Impl.Mont.X86 (at_)
open VG.Proof.Mont.X86.Rt (PtrAt ea_ptr ws_write)
open VG.Proof.Rsa.X86.KeyRt (kw)
open VG.Proof.Rsa.X86.Keys

/-- The word above narrow array `j`'s number zeroed, through a pointer to the array. -/
theorem zeroAbove_ok {s : State} {B : Addr} {Z len N : Nat}
    (h : VG.Proof.Rsa.X86.KeyRt.RtWs nar s B Z len N) {j : Nat} (hj : j < N) :
    WP isa (.block (arrPtr nar .eax j .edx ++ ([.alu .add .eax (.reg .edx), .alu .sub .eax (.imm 8),
        .mov .ecx (.imm 0), .store (at_ .eax 0) .ecx] : List Instr))) s fun t =>
      VG.Proof.Rsa.X86.KeyRt.RtWs nar t B Z len N ∧ Keep B (kw len) [j] [] s.mem t.mem ∧
      num t.mem B (kw len) j = num s.mem B (kw len) j ∧
      w32 t.mem B (arr (kw len) j + 4 * kw len) = 0 ∧ Keeps [.eax, .ecx, .edx] s t := by
  have fit := h.ws.arr_fit hj
  have nowrap := h.ws.workspace.nowrap
  simp only [S] at fit
  refine VG.Proof.Rsa.X86.KeyRt.arrPtr_ok (VG.Proof.Rsa.X86.KeyRt.lenSrc h) h.lenLe h.edi (by decide)
    (by decide) (by omega) fun u K m p e => ?_
  refine wp_addS rfl fun u₁ U₁ _ => wp_subS rfl fun u₂ U₂ _ => wp_movS rfl fun u₃ U₃ _ => ?_
  have K₃ : Keeps [.eax, .ecx, .edx] s u₃ :=
    ((K.mono (by decide)).trans ((U₁.keeps.trans U₂.keeps).mono (by decide))).trans (U₃.keeps.mono (by decide))
  have hu := h.rt.of_keeps K₃
  have ptr : PtrAt u₃ B .eax (arr (kw len) j + 4 * kw len) := by
    rw [PtrAt, U₃.other _ (by decide), U₂.gpr, U₁.gpr, BitVec.toNat_sub, BitVec.toNat_add, p, e,
      show (8 : BitVec 32).toNat = 8 from rfl]
    omega
  refine wp_storeS (ea_ptr hu ptr (d := 0) (by omega))
    (ws_write hu (y := arr (kw len) j + 4 * kw len + 0) (n := 4) (by omega)) fun t T => WP.block_nil ?_
  have mem : t.mem = s.mem.writeW (off B (arr (kw len) j + 4 * kw len)) (0 : BitVec 32) := by
    rw [T.mem, U₃.gpr, U₃.mem, U₂.mem, U₁.mem, m, Nat.add_zero]
  have O := writeW32_outside s.mem B (d := arr (kw len) j + 4 * kw len) (0 : BitVec 32) (by omega)
  rw [← mem] at O
  have Kt : Keeps [.eax, .ecx, .edx] s t := K₃.trans ((T.keeps []).mono (by decide))
  refine ⟨h.keep Kt (by decide) (by decide) (O.mono (Nat.zero_le _) (by omega)),
    Keep.of_arr O (by simp only [S]; omega) (by simp), ?_, by rw [mem, w32_write_self]; rfl, Kt⟩
  exact O.val32 (.inl (by omega)) (by omega)

def AD (m p : Nat) : Nat → Nat := upd (upd (AP m p) aQ m) aDv p

theorem divSet_ok {g : Geo} {s0 s : State} {V : Nat → Nat} {m p : Nat}
    (h : KS g s0 (AP m p) [1, aN, aZero] (fun _ => 0) [] V [sMask] s) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.divSet s fun t =>
      KS g s0 (AD m p) [aQ, aDv, 1, aZero] (fun _ => 0) [] V [sMask] t ∧
      w32 t.mem g.B (arr g.w aDv + 4 * g.w) = 0 := by
  unfold VG.Impl.Rsa.X86.RecoverRt.divSet
  simp only [seqs]
  refine WP.seq (WP.mono (h.copy_w (o := aQ) (a := aN) (by decide) (by simp) (by decide) (by simp))
    fun s1 ⟨h1, _, _⟩ => ?_)
  have vn : AP m p aN = m := rfl
  rw [vn] at h1
  refine WP.seq (WP.mono (h1.copy_w (o := aDv) (a := 1) (by decide) (by simp) (by decide) (by simp))
    fun s2 ⟨h2, _, _⟩ => ?_)
  have vp : upd (AP m p) aQ m 1 = p := rfl
  rw [vp] at h2
  refine WP.mono (zeroAbove_ok h2.rt (j := aDv) (by decide)) fun t ⟨_, keep, val, top, r⟩ => ?_
  rw [kw_nar] at keep val top
  have hout := h2.write_w keep (by decide) (by simp) (r.mono (by decide)) (val.trans (h2.arrs aDv (by simp)))
    (by simp) (by simp)
  rw [upd_self] at hout
  refine ⟨hout.mono ?_ (by simp) (fun d hd => ⟨hd, rfl⟩), top⟩
  intro j hj
  refine ⟨by simp only [List.mem_cons] at *; grind, ?_⟩
  by_cases e : j = aDv
  · subst e; simp only [AD, upd_self]
  · simp only [AD, upd_ne _ _ e]

end VG.Proof.Rsa.X86.Recover
