module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeySized
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDispatch
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry

/-! # The public modulus byte length selects a supported native key width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Mont.X86 VG.Impl.RsaKeyGen.X86.Key

theorem front_ok {E : Environment} {s : State} (h : Input E s) :
    WP isa (.seq (.block [.mov .eax (.mem (sc 4)), .shift .shr .eax 4]) (dispatch widths)) s fun t =>
      Ws t E.base E.size E.n 32 ∧ BodyOutcome E s.mem t ∧
      Frame E.outputs.writes s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have valid := h.valid.length
  have dimensions := h.valid.widths
  let w := E.primeLength / 8
  have bounds : 4 ≤ w ∧ w ≤ 64 := by unfold w; obtain ⟨_, _, _⟩ := valid; omega
  have width : E.n = 4 * w := by unfold w Environment.n; obtain ⟨_, _, _⟩ := valid; omega
  have lengthBound : 2 * E.primeLength < 2 ^ 32 := by omega
  have space := h.ws.hdr_le
  refine WP.seq (wp_movS (readSrc_sc h.ws.workspace (by unfold VG.Impl.Rsa.X86.Keys.hdr at space; omega))
    fun a A _ => wp_shr (by decide) fun b B _ => WP.block_nil ?_)
  have memory : b.mem = s.mem := B.mem.trans A.mem
  have K : Keeps [.eax] s b := A.keeps.trans B.keeps
  have hb := h.keep (h.ws.rest K) K (by intro d hd; rw [memory])
  have selected : b.gpr .eax = BitVec.ofNat 32 w := by
    rw [B.gpr, A.gpr, h.arguments 1 (by decide)]
    change BitVec.ofNat 32 (2 * E.primeLength) >>> 4 = BitVec.ofNat 32 w
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt lengthBound, Nat.mod_eq_of_lt (by omega : w < 2 ^ 32)]
    change (2 * E.primeLength) / 16 = w
    unfold w
    omega
  refine WP.mono (dispatch_ok hb width (by omega) selected widths ?_ ?_)
    fun t ⟨ht, result, F, Kt⟩ => ?_
  · exact List.mem_map.mpr ⟨w - 4, List.mem_range.mpr (by omega), by omega⟩
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    have H := List.mem_range.mp hi
    omega
  · rw [memory] at result F
    exact ⟨ht, result, F, (K.mono (by decide)).trans Kt⟩

end VG.Proof.RsaKeyGen.X86.Key
