module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportWorkspace
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportLoad
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWidenCopy
import VerifiedGarbage.Proof.RsaKeyGen.FrameOutside
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Import a prime in native words without reading uninitialized padding -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def loadPrimeRanges (n k out : Nat) : List (Nat × Nat) := [(arr n 0, 4 * k), (arr n out, S n)]

theorem loadPrime_ok {s : State} {B : Addr} {Z n k pointer out : Nat} {p : BitVec 32}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k)
    (header : pointer + 4 ≤ hdr) (ho : out < 32) (persistent : 15 ≤ out)
    (source : s.mem.readW (off B pointer) 32 = p)
    (fit : p.toNat + 4 * k ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (p.setWidth 64) (4 * k))
    (separate : Region.Disjoint ⟨p.setWidth 64, 4 * k⟩ ⟨B, Z⟩) :
    WP isa (loadPrime n pointer out) s fun t =>
      Ws t B Z n 32 ∧ Outs B (loadPrimeRanges n k out) s.mem t.mem ∧
      num t.mem B n out = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (p.setWidth 64) (4 * k)) ∧
      num t.mem B n out < 2 ^ (32 * k) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have small : k ≤ n := by omega
  have half : n / 2 = k := by omega
  have space : arr n 0 + 4 * k ≤ Z := by
    have F := h.arr_fit (j := 0) (by decide)
    unfold S at F
    omega
  have noWrap := h.workspace.nowrap
  unfold loadPrime seqs
  rw [half]
  refine WP.seq (wp_movS (readSrc_sc h.workspace (by have := h.hdr_le; omega)) fun u U _ => WP.block_nil ?_)
  have hu := h.rest U.keeps
  have src : u.gpr .esi = p := U.gpr.trans source
  have context := Import.context_workspace hu.workspace positive space fit
    (by rw [U.keeps.2.1, U.keeps.2.2]; exact readable) separate
  refine WP.seq (WP.mono (Import.load_ok context src rfl) fun v ⟨value, F, Kv⟩ => ?_)
  have dest : (u.gpr .edi + BitVec.ofNat 32 (arr n 0)).setWidth 64 = off B (arr n 0) :=
    hu.workspace.ea (d := arr n 0) (by omega)
  change (v.mem.read ((u.gpr .edi + BitVec.ofNat 32 (arr n 0)).setWidth 64) (4 * k)).toNat =
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt u.mem (p.setWidth 64) (4 * k)) at value
  rw [dest, U.mem] at value
  have imported : val32 v.mem B (arr n 0) k =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (p.setWidth 64) (4 * k)) := by
    rw [← VG.Proof.Bignum.read_eq_val32]
    exact value
  change Frame [⟨(u.gpr .edi + BitVec.ofNat 32 (arr n 0)).setWidth 64, 4 * k⟩] u.mem v.mem at F
  rw [dest, U.mem] at F
  have Ov : Outside B (arr n 0) (4 * k) s.mem v.mem :=
    VG.Proof.RsaKeyGen.frame_outside F (by omega)
  have hv := hu.rest Kv
  have before : arr n 0 + 4 * k ≤ arr n out := by
    have H := arr_end (w := n) (show 0 < out by omega)
    unfold S at H
    omega
  refine WP.mono (widenCopy_ok hv positive small ho space (Or.inl before))
    fun t ⟨ht, Ot, _, copied, Kt⟩ => ?_
  refine ⟨ht, ?_, copied.trans imported, ?_,
    (U.keeps.mono (by decide)).trans ((Kv.mono (by decide)).trans (Kt.mono (by decide)))⟩
  · exact (Outs.of_outside Ov (by simp [loadPrimeRanges])).trans
      (Outs.of_outside Ot (by simp [loadPrimeRanges]))
  · rw [copied]
    exact val32_lt _ _ _ _

end VG.Proof.RsaKeyGen.X86.Key
