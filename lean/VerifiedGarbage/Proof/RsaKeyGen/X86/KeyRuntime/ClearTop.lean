module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace

/-! # The division bank's extra divisor word is explicitly zero -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.Mont.X86.Rt (PtrAt)

theorem clearTop_ok {s : State} {B : Addr} {Z n N j : Nat} (h : Ws s B Z n N)
    (w : Width) (fit : Loc.offset n (.array w j) + 4 * w.words n + 4 ≤ Z) :
    WP isa (clearTop w j) s fun t => Ws t B Z n N ∧
      Outside B (Loc.offset n (.array w j) + 4 * w.words n) 4 s.mem t.mem ∧
      w32 t.mem B (Loc.offset n (.array w j) + 4 * w.words n) = 0 ∧
      Keeps [.eax, .edx, .ebp] s t := by
  have nowrap := h.old.workspace.nowrap
  unfold clearTop
  simp only [List.append_assoc]
  refine h.ptr_ok (.array w j) (by decide) (by decide) (by omega) fun a K1 m1 P1 => ?_
  have ha := h.keep K1 (by rw [m1]; exact Outside.refl _ _ _ _)
  refine ha.bytes_ok w .edx fun b K2 m2 count => ?_
  refine wp_addS rfl fun c C _ => wp_movS rfl fun d U _ => ?_
  have K : Keeps [.eax, .edx, .ebp] s d :=
    ((K1.mono (by decide)).trans (K2.mono (by decide))).trans
      ((C.keeps.mono (by decide)).trans (U.keeps.mono (by decide)))
  have hw := h.full.rt.of_keeps K
  have P2 : PtrAt b B .ebp (Loc.offset n (.array w j)) := by
    rw [PtrAt, K2.1 _ (by decide)]; exact P1
  have P : PtrAt d B .ebp (Loc.offset n (.array w j) + 4 * w.words n) := by
    rw [PtrAt, U.other _ (by decide), C.gpr, VG.Proof.Mont.X86.Rt.ptr_add P2, count]
  refine wp_storeS (VG.Proof.Mont.X86.Rt.ea_ptr hw P (d := 0) (by omega))
    (VG.Proof.Mont.X86.Rt.ws_write hw (y := Loc.offset n (.array w j) + 4 * w.words n + 0)
      (n := 4) (by omega)) fun t T => WP.block_nil ?_
  have memory : t.mem = s.mem.writeW (off B (Loc.offset n (.array w j) + 4 * w.words n)) (0#32) := by
    rw [T.mem, U.mem, C.mem, m2, m1, U.gpr, Nat.add_zero]
    rfl
  have O : Outside B (Loc.offset n (.array w j) + 4 * w.words n) 4 s.mem t.mem := by
    rw [memory]; exact writeW32_outside _ _ _ (by omega)
  have allK := K.trans (T.keeps _)
  refine ⟨h.keep allK (O.mono (Nat.zero_le _) (by omega)), O, ?_, allK⟩
  rw [memory, w32_write_self]
  rfl

end VG.Proof.RsaKeyGen.X86.KeyRuntime
