module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLoadExponent
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Widen
import VerifiedGarbage.Proof.Bignum.X86.LoadBE
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # The public exponent imported through its argument pointer and length -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (arr S num)
open VG.Proof.Bignum.X86 (byteAddr)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Impl.RsaKeyGen.X86.Key (kEv aE)

/-- `Key.loadExponent_ok` with the pointer and length from arguments 14 and 15. -/
theorem loadExponent_ok {s : State} {B : Addr} {Z n len : Nat} {p : BitVec 32}
    (h : Ws s B Z n 32) (positive : 0 < len) (bound : len ≤ 8)
    (pointer : VG.Proof.Bignum.X86.CallArgument s B Z 18 p)
    (length : VG.Proof.Bignum.X86.CallArgument s B Z 19 (BitVec.ofNat 32 len))
    (fit : p.toNat + len ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (byteAddr p) len)
    (separate : Region.Disjoint ⟨byteAddr p, len⟩ ⟨off B kEv, 8⟩) :
    WP isa loadExponent s fun t =>
      Ws t B Z n 32 ∧ Outs B (VG.Proof.RsaKeyGen.X86.Key.loadExponentRanges n) s.mem t.mem ∧
      val32 t.mem B kEv 2 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr p) len) ∧
      num t.mem B n aE = val32 t.mem B kEv 2 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have head := h.hdr_le
  have nBound := h.old.wle
  have size := h.size
  unfold loadExponent VG.Impl.Rsa.X86.Keys.seqs
  refine WP.seq (wp_movS pointer.readSrc fun u U _ => ?_)
  refine wp_movS (length.keep U.keeps (by decide) (by rw [U.mem]; exact Outside.refl _ _ _ _)).readSrc
    fun v V _ => WP.block_nil ?_
  have K : Keeps [.esi, .ecx] s v := (U.keeps.mono (by decide)).trans (V.keeps.mono (by decide))
  have memory : v.mem = s.mem := V.mem.trans U.mem
  have hv := h.keep K (by rw [memory]; exact Outside.refl _ _ _ _)
  have source : v.gpr .esi = p := by rw [V.other _ (by decide), U.gpr]
  have count : v.gpr .ecx = BitVec.ofNat 32 len := V.gpr
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86.loadBE_ok hv.old.workspace (by decide)
    (by unfold kEv VG.Impl.Rsa.X86.Keys.hdr at *; omega) positive bound (by rw [source]; exact fit) count
    (by rw [source, K.2.1, K.2.2]; exact readable) (by rw [source]; exact separate))
    fun w ⟨value, Ow, Kw⟩ => ?_)
  have hw := hv.keep Kw (Ow.mono (Nat.zero_le _) (by unfold kEv VG.Impl.Rsa.X86.Keys.hdr at *; omega))
  rw [memory, source, wordsVal_eq_val32] at value
  change val32 w.mem B kEv 2 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr p) len) at value
  have eFit := h.arr_fit (j := aE) (by decide)
  unfold S at eFit
  have eStart := VG.Proof.Rsa.X86.Keys.arr_end (w := n) (show 0 < aE by decide)
  have hdrArr : VG.Impl.Rsa.X86.Keys.hdr ≤ arr n 0 := by unfold VG.Proof.Rsa.X86.Keys.arr; omega
  refine WP.mono (widen_ok hw .exponent (arr aE) (.fixed kEv) (by simp only [Width.words]; omega)
    (by change arr n aE + _ ≤ Z; omega)
    (by change kEv + 4 * 2 ≤ Z; unfold kEv VG.Impl.Rsa.X86.Keys.hdr at *; omega)
    (Or.inl (by change kEv + 4 * 2 ≤ arr n aE; unfold kEv VG.Impl.Rsa.X86.Keys.hdr at *; omega)))
    fun t ⟨ht, Ot, _, copied, Kt⟩ => ?_
  change Outside B (arr n aE) (4 * (n + 2)) w.mem t.mem at Ot
  change val32 t.mem B (arr n aE) n = val32 w.mem B kEv 2 at copied
  have exponent : val32 t.mem B kEv 2 = val32 w.mem B kEv 2 :=
    Ot.val32 (Or.inl (by unfold kEv VG.Impl.Rsa.X86.Keys.hdr at *; omega)) (by decide)
  refine ⟨ht, ?_, exponent.trans value, copied.trans exponent.symm,
    (K.mono (by decide)).trans (Kw.trans (Kt.mono (by decide)))⟩
  have first : Outs B (VG.Proof.RsaKeyGen.X86.Key.loadExponentRanges n) s.mem w.mem := by
    rw [← memory]
    exact Outs.of_outside Ow (by simp [VG.Proof.RsaKeyGen.X86.Key.loadExponentRanges])
  exact first.trans (Outs.of_outside (Ot.mono (o' := arr n aE) (n' := S n) (Nat.le_refl _) (by unfold S; omega))
    (by simp [VG.Proof.RsaKeyGen.X86.Key.loadExponentRanges]))

end VG.Proof.RsaKeyGen.X86.KeyRuntime
