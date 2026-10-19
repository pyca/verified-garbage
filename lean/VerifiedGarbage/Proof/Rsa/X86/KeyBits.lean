module

public import VerifiedGarbage.Proof.Rsa.X86.KeyHalf
public import VerifiedGarbage.Proof.Rsa.KeyBits32

/-! # Low-bit extraction for the binary RSA inverse -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Keys
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Proof.Rsa.KeyBits32

theorem num_mod2 (m : Mem) (B : Addr) {w j : Nat} (hw : 0 < w) :
    num m B w j % 2 = w32 m B (arr w j) % 2 :=
  VG.Proof.Rsa.KeyWorkspace.num_mod2 m B hw

theorem bitOf_ok {s : State} {B : Addr} {Z w N j sl : Nat} (h : Ws s B Z w N)
    (hj : j < N) (hsl : sl + 4 ≤ hdr) :
    WP isa (.block (bitOf w sl j)) s fun t => Ws t B Z w N ∧
      Keep B w [] [sl] s.mem t.mem ∧ slot t.mem B sl = num s.mem B w j % 2 ∧
      Keeps [.eax] s t := by
  have fit := h.arr_fit hj
  have head := h.hdr_le
  simp only [S] at fit
  unfold bitOf
  change WP isa (.block (.mov .eax (.mem (VG.Impl.Mont.X86.sc (arr w j))) :: _)) s _
  refine wp_movS (readSrc_sc h.workspace (by have := h.wpos; omega)) fun u U _ => ?_
  refine wp_logicS (.inl rfl) rfl fun v V => ?_
  have hv := (h.workspace.of_keeps U.keeps (by decide)).of_keeps V.keeps (by decide)
  refine wp_storeS (hv.ea (by omega)) (hv.write (by omega)) fun t T => WP.block_nil ?_
  have r : Keeps [.eax] s t := (U.keeps.trans V.keeps).trans (T.keeps _)
  have mem : t.mem = s.mem.writeW (off B sl) (v.gpr .eax) := by rw [T.mem, V.mem, U.mem]
  refine ⟨h.rest r, ?_, ?_, r⟩
  · rw [mem]
    exact Keep.of_slot (writeW32_outside _ _ _ (by unfold hdr at hsl; omega)) (by simp)
  · unfold slot
    rw [mem, w32_write_self, V.gpr, ite_eq_left rfl, U.gpr, bv_and_one, num_mod2 _ _ h.wpos]
end VG.Proof.Rsa.X86.Keys
