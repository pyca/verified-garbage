module
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs

import VerifiedGarbage.Proof.Rsa.KeyBits32
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Updating low words of RSA workspace arrays -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Keys
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Proof.Rsa.KeyBits32

theorem storeLow_ok {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N) :
    WP isa (.block [.store (VG.Impl.Mont.X86.sc (arr w j)) .eax]) s fun t =>
      Ws t B Z w N ∧ Keep B w [j] [] s.mem t.mem ∧
      num t.mem B w j = (s.gpr .eax).toNat + 2 ^ 32 * (num s.mem B w j / 2 ^ 32) ∧
      Keeps [] s t ∧ w32 t.mem B (arr w j + 4 * w) = w32 s.mem B (arr w j + 4 * w) := by
  have fit := h.arr_fit hj
  have positive := h.wpos
  have nw := h.workspace.nowrap
  simp only [S] at fit
  refine wp_storeS (h.workspace.ea (by omega)) (h.workspace.write (by omega)) fun t T => WP.block_nil ?_
  have outside := writeW32_outside s.mem B (d := arr w j) (s.gpr .eax) (by omega)
  refine ⟨h.rest (T.keeps []) (by decide) (by decide), ?_, ?_, T.keeps [], ?_⟩
  · rw [T.mem]
    exact Keep.of_arr (d := 0) (by simpa using outside) (by unfold S; omega) (by simp)
  · rw [T.mem]
    exact VG.Proof.Rsa.KeyWorkspace.num_write0 _ _ h.wpos (by change arr w j + 4 * w ≤ 2 ^ 64; omega) _
  · rw [T.mem]; exact outside.w32 (by omega) (by omega)

theorem setOne_ok {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N) :
    WP isa (.block (setOne w j)) s fun t => Ws t B Z w N ∧ Keep B w [j] [] s.mem t.mem ∧
      num t.mem B w j = 1 + 2 ^ 32 * (num s.mem B w j / 2 ^ 32) ∧ Keeps [.eax] s t := by
  unfold setOne
  refine wp_movS rfl fun u U _ => ?_
  refine WP.mono (storeLow_ok (h.rest U.keeps (by decide) (by decide)) hj) ?_
  rintro t ⟨ht, frame, value, rest, _⟩
  rw [U.mem] at frame value
  rw [U.gpr] at value
  exact ⟨ht, frame, value, U.keeps.trans (rest.mono (by decide))⟩

theorem orOne_ok {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N) :
    WP isa (.block (orOne w j)) s fun t => Ws t B Z w N ∧ Keep B w [j] [] s.mem t.mem ∧
      num t.mem B w j = 2 * (num s.mem B w j / 2) + 1 ∧ Keeps [.eax] s t := by
  have fit := h.arr_fit hj
  have positive := h.wpos
  simp only [S] at fit
  unfold orOne
  change WP isa (.block (.mov .eax (.mem (VG.Impl.Mont.X86.sc (arr w j))) :: _)) s _
  refine wp_movS (readSrc_sc h.workspace (by omega)) fun u U _ => ?_
  refine wp_orS rfl fun v V => ?_
  have hv := (h.rest U.keeps (by decide) (by decide)).rest V.keeps (by decide) (by decide)
  refine WP.mono (storeLow_ok hv hj) fun t ⟨ht, frame, value, rest, _⟩ => ?_
  have mem : v.mem = s.mem := V.mem.trans U.mem
  rw [mem] at frame value
  refine ⟨ht, frame, ?_, (U.keeps.trans V.keeps).trans (rest.mono (by decide))⟩
  rw [value, V.gpr, U.gpr, bv_or_one]
  have low := VG.Proof.Rsa.KeyWorkspace.num_mod32 s.mem B (j := j) h.wpos
  change num s.mem B w j % 2 ^ 32 = (s.mem.readW (off B (arr w j)) 32).toNat at low
  omega

theorem clrLow_ok {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N) :
    WP isa (.block (clrLow w j)) s fun t => Ws t B Z w N ∧ Keep B w [j] [] s.mem t.mem ∧
      num t.mem B w j = 2 * (num s.mem B w j / 2) ∧ Keeps [.eax] s t ∧
      w32 t.mem B (arr w j + 4 * w) = w32 s.mem B (arr w j + 4 * w) := by
  have fit := h.arr_fit hj
  have positive := h.wpos
  simp only [S] at fit
  unfold clrLow
  change WP isa (.block (.mov .eax (.mem (VG.Impl.Mont.X86.sc (arr w j))) :: _)) s _
  refine wp_movS (readSrc_sc h.workspace (by omega)) fun u U _ => ?_
  refine wp_orS rfl fun v V => ?_
  refine wp_logicS (.inr rfl) rfl fun z Zr => ?_
  have hz := ((h.rest U.keeps (by decide) (by decide)).rest V.keeps (by decide) (by decide)).rest
    Zr.keeps (by decide) (by decide)
  refine WP.mono (storeLow_ok hz hj) fun t ⟨ht, frame, value, rest, top⟩ => ?_
  have mem : z.mem = s.mem := Zr.mem.trans (V.mem.trans U.mem)
  rw [mem] at frame value top
  refine ⟨ht, frame, ?_, ((U.keeps.trans V.keeps).trans Zr.keeps).trans (rest.mono (by decide)), top⟩
  rw [value, Zr.gpr, ite_eq_right (by decide), V.gpr, U.gpr, bv_clr_one]
  have low := VG.Proof.Rsa.KeyWorkspace.num_mod32 s.mem B (j := j) h.wpos
  change num s.mem B w j % 2 ^ 32 = (s.mem.readW (off B (arr w j)) 32).toNat at low
  omega

end VG.Proof.Rsa.X86.Keys
