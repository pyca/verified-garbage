module
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs

import VerifiedGarbage.Proof.Rsa.KeyBits32
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Scalar header operations for the binary RSA inverse -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Keys
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Proof.Rsa.KeyBits32

theorem store_slot {s : State} {B : Addr} {Z w N d : Nat} (h : Ws s B Z w N)
    (hd : d + 4 ≤ hdr) (r : Reg) :
    WP isa (.block [.store (VG.Impl.Mont.X86.sc d) r]) s fun t =>
      Ws t B Z w N ∧ Keep B w [] [d] s.mem t.mem ∧
      slot t.mem B d = (s.gpr r).toNat ∧ Keeps [] s t := by
  have head := h.hdr_le
  refine wp_storeS (h.workspace.ea (by omega)) (h.workspace.write (by omega)) fun t T => WP.block_nil ?_
  refine ⟨h.rest (T.keeps []) (by decide) (by decide), ?_, ?_, T.keeps []⟩
  · rw [T.mem]
    exact Keep.of_slot (writeW32_outside _ _ _ (by unfold hdr at hd; omega)) (by simp)
  · unfold slot; rw [T.mem, w32_write_self]

theorem andS_ok {s : State} {B : Addr} {Z w N d a b : Nat} (h : Ws s B Z w N)
    (hd : d + 4 ≤ hdr) (ha : a + 4 ≤ hdr) (hb : b + 4 ≤ hdr)
    (ba : slot s.mem B a ≤ 1) (bb : slot s.mem B b ≤ 1) :
    WP isa (.block (andS d a b)) s fun t =>
      Ws t B Z w N ∧ Keep B w [] [d] s.mem t.mem ∧
      slot t.mem B d = (if slot s.mem B a = 1 ∧ slot s.mem B b = 1 then 1 else 0) ∧
      Keeps [.eax] s t := by
  have head := h.hdr_le
  unfold andS
  refine wp_movS (readSrc_sc h.workspace (by omega)) fun u U _ => ?_
  have hu := h.workspace.of_keeps U.keeps (by decide)
  refine wp_logicS (.inl rfl) (readSrc_sc hu (by omega)) fun v V => ?_
  have hv := hu.of_keeps V.keeps (by decide)
  refine wp_storeS (hv.ea (by omega)) (hv.write (by omega)) fun t T => WP.block_nil ?_
  have r : Keeps [.eax] s t := (U.keeps.trans V.keeps).trans (T.keeps _)
  have mem : t.mem = s.mem.writeW (off B d) (v.gpr .eax) := by rw [T.mem, V.mem, U.mem]
  refine ⟨h.rest r, ?_, ?_, r⟩
  · rw [mem]
    exact Keep.of_slot (writeW32_outside _ _ _ (by unfold hdr at hd; omega)) (by simp)
  · unfold slot
    rw [mem, w32_write_self, V.gpr, ite_eq_left rfl, U.gpr, U.mem]
    exact bv_and_bits ba bb
end VG.Proof.Rsa.X86.Keys
