module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWritePort
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWritePorts
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputMap
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Offset

/-! # Complete masked key export, including an independent retry status -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem writeOutputs_ok {g : OutputGeometry} {s : State} (h : OutputInput g s) (accept : Bool)
    (mask : slot s.mem g.base kOk = if accept then 1 else 0) :
    WP isa (writeOutputs g.n) s fun t =>
      Ws t g.base g.size g.n 32 ∧ (t.gpr .eax).toNat = slot s.mem g.base kStatus ∧
      (∀ i, i < 7 → Spec.Rsa.bytesAt t.mem (g.region i).base (g.region i).len = portResult g s.mem accept i) ∧
      Frame g.writes s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have fits := h.ws.arr_fit (j := aZero) (by decide)
  have fit64 := h.ws.fit64 (j := aZero) (by decide)
  unfold writeOutputs seqs
  refine WP.seq (WP.mono (zerosW_ok h.ws.workspace (by omega)
    (by change arr g.n aZero + 4 * (g.n + 2) ≤ g.size; exact fits))
    fun u ⟨Ou, zero, Ku⟩ => ?_)
  change Outside g.base (arr g.n aZero) (S g.n) s.mem u.mem at Ou
  change val32 u.mem g.base (arr g.n aZero) (g.n + 2) = 0 at zero
  have hu := h.ws.rest Ku
  have clear : Keep g.base g.n [aZero] [] s.mem u.mem :=
    Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using Ou) (by unfold S; omega) (by simp)
  have header : ∀ d, d + 4 ≤ hdr → slot u.mem g.base d = slot s.mem g.base d :=
    fun d hd => clear.slot hd (by simp)
  have Pu : ExportProgress g s.mem accept 0 u := by
    refine ⟨h.after hu Ku header, ?_, (header kOk (by decide)).trans mask, header, ?_, ?_⟩
    · change val32 u.mem g.base (arr g.n aZero) g.n = 0
      have H := VG.Proof.Rsa.KeyWorkspace.val32_zero_part zero (a := 0) (c := g.n) (by omega)
      simpa only [Nat.mul_zero, Nat.add_zero] using H
    · intro i _ hi
      exact clear.num (by intro a ha; obtain rfl := List.mem_singleton.mp ha; exact outputIndex_zero hi)
        (by simp) (h.ws.fit64 (outputIndex_bound hi))
    · intro i hi
      omega
  have Fu : Frame g.writes s.mem u.mem := by
    apply (VG.Proof.Bignum.outside_frame Ou fit64).sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨g.scratch, List.mem_cons_self, Offset.sub_base g.base fits⟩
  refine WP.seq (WP.mono (writePorts_ok Pu (by decide : 0 + 7 ≤ 7))
    fun v ⟨Pv, Fv, Kv⟩ => ?_)
  have head := Pv.input.ws.hdr_le
  refine wp_movS (readSrc_sc Pv.input.ws.workspace (by unfold kStatus hdr at *; omega))
    fun t T _ => WP.block_nil ?_
  refine ⟨Pv.input.ws.rest T.keeps, ?_, ?_, ?_,
    (Ku.mono (by decide)).trans (Kv.trans (T.keeps.mono (by decide)))⟩
  · rw [T.gpr]
    exact Pv.header kStatus (by decide)
  · intro i hi
    rw [T.mem]
    exact Pv.done i hi hi
  · rw [T.mem]
    exact Fu.trans Fv

end VG.Proof.RsaKeyGen.X86.Key
