module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.DispatchIO
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # The public byte length selects a small input or output adapter -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86
open VG.Impl.RsaKeyGen.X86.Key (widths)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (Environment Input)

theorem selectIO_ok {E : Environment} {s : State} {part : Nat → Prog isa} {Q : State → Prop}
    (h : Input E s)
    (correct : ∀ t, Keeps [.eax] s t → t.mem = s.mem → WP isa (part E.n) t Q) :
    WP isa (selectIO part) s Q := by
  have valid := h.valid.length
  let w := E.primeLength / 8
  have bounds : 4 ≤ w ∧ w ≤ 64 := by unfold w; obtain ⟨_, _, _⟩ := valid; omega
  have width : E.n = 4 * w := by unfold w VG.Proof.RsaKeyGen.X86.Key.Environment.n; obtain ⟨_, _, _⟩ := valid; omega
  have lengthBound : 2 * E.primeLength < 2 ^ 32 := by omega
  have space := h.ws.hdr_le
  unfold selectIO
  refine WP.seq (wp_movS (readSrc_sc h.ws.workspace
    (by unfold VG.Impl.Rsa.X86.Keys.hdr at space; omega))
    fun a A _ => wp_shr (by decide) fun b B _ => WP.block_nil ?_)
  have memory : b.mem = s.mem := B.mem.trans A.mem
  have K : Keeps [.eax] s b := A.keeps.trans B.keeps
  have selected : b.gpr .eax = BitVec.ofNat 32 w := by
    rw [B.gpr, A.gpr, h.arguments 1 (by decide)]
    change BitVec.ofNat 32 (2 * E.primeLength) >>> 4 = BitVec.ofNat 32 w
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt lengthBound, Nat.mod_eq_of_lt (by omega : w < 2 ^ 32)]
    change (2 * E.primeLength) / 16 = w
    unfold w
    omega
  refine dispatchIO_ok (by omega) widths ?_ ?_ selected ?_
  · exact List.mem_map.mpr ⟨w - 4, List.mem_range.mpr (by omega), by omega⟩
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    have H := List.mem_range.mp hi
    omega
  · intro t Kt mt
    rw [← width]
    exact correct t (K.trans (Kt.mono (by decide))) (mt.trans memory)

end VG.Proof.RsaKeyGen.X86.KeyRuntime
