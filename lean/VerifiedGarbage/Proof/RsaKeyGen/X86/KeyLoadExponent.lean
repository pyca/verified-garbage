module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
import VerifiedGarbage.Proof.Bignum.X86.LoadBE
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWidenCopy
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Import the public exponent into a pair and a persistent native array -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Bignum.X86 (byteAddr)
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def loadExponentRanges (n : Nat) : List (Nat × Nat) := [(kEv, 8), (arr n aE, S n)]

theorem loadExponent_preserves_num {m m' : Mem} {B : Addr} {n j : Nat}
    (unchanged : j ≠ aE) (fit : arr n j + S n ≤ 2 ^ 64)
    (O : Outs B (loadExponentRanges n) m m') : num m' B n j = num m B n j := by
  change val32 m' B (arr n j) n = val32 m B (arr n j) n
  apply O.val32 _ (by unfold S at fit; omega)
  intro r hr
  simp only [loadExponentRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Or.inr (Nat.le_trans (by decide : kEv + 8 ≤ hdr) (Nat.le_add_right ..))
  · have D := arr_disj (w := n) unchanged
    unfold S at D ⊢
    omega

theorem loadExponent_ok {s : State} {B : Addr} {Z n len : Nat} {p : BitVec 32}
    (h : Ws s B Z n 32) (width : 2 ≤ n) (positive : 0 < len) (bound : len ≤ 8)
    (pointer : s.mem.readW (off B 56) 32 = p)
    (length : s.mem.readW (off B 60) 32 = BitVec.ofNat 32 len)
    (fit : p.toNat + len ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (byteAddr p) len)
    (separate : Region.Disjoint ⟨byteAddr p, len⟩ ⟨off B kEv, 8⟩) :
    WP isa (loadExponent n) s fun t =>
      Ws t B Z n 32 ∧ Outs B (loadExponentRanges n) s.mem t.mem ∧
      val32 t.mem B kEv 2 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr p) len) ∧
      num t.mem B n aE = val32 t.mem B kEv 2 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have head := h.hdr_le
  unfold loadExponent seqs
  refine WP.seq (wp_movS (readSrc_sc h.workspace (by unfold hdr at head; omega)) fun u U _ => ?_)
  have hu := h.rest U.keeps
  refine wp_movS (readSrc_sc hu.workspace (by unfold hdr at head; omega)) fun v V _ => WP.block_nil ?_
  have K : Keeps [.esi, .ecx] s v := (U.keeps.mono (by decide)).trans (V.keeps.mono (by decide))
  have hv := h.rest K
  have memory : v.mem = s.mem := V.mem.trans U.mem
  have source : v.gpr .esi = p := by rw [V.other _ (by decide), U.gpr, pointer]
  have count : v.gpr .ecx = BitVec.ofNat 32 len := by rw [V.gpr, U.mem, length]
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86.loadBE_ok hv.workspace (by decide)
    (by unfold kEv hdr at *; omega) positive bound (by rw [source]; exact fit) count
    (by rw [source, K.2.1, K.2.2]; exact readable) (by rw [source]; exact separate))
    fun w ⟨value, Ow, Kw⟩ => ?_)
  have hw := hv.rest Kw
  rw [memory, source, wordsVal_eq_val32] at value
  change val32 w.mem B kEv 2 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr p) len) at value
  refine WP.mono (widenCopy_ok hw (by decide) width (by decide)
    (by unfold kEv hdr at *; omega)
    (Or.inl (Nat.le_trans (by decide : kEv + 4 * 2 ≤ hdr) (Nat.le_add_right ..))))
    fun t ⟨ht, Ot, _, copied, Kt⟩ => ?_
  have exponent : val32 t.mem B kEv 2 = val32 w.mem B kEv 2 :=
    Ot.val32 (Or.inl (Nat.le_trans (by decide : kEv + 4 * 2 ≤ hdr) (Nat.le_add_right ..))) (by decide)
  refine ⟨ht, ?_, exponent.trans value, copied.trans exponent.symm,
    (K.mono (by decide)).trans (Kw.trans (Kt.mono (by decide)))⟩
  have first : Outs B (loadExponentRanges n) s.mem w.mem := by
    rw [← memory]
    exact Outs.of_outside Ow (by simp [loadExponentRanges])
  exact first.trans (Outs.of_outside Ot (by simp [loadExponentRanges]))

end VG.Proof.RsaKeyGen.X86.Key
