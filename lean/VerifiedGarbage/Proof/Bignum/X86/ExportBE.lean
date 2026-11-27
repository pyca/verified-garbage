module

public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.Bignum.X86.StoreBE
import VerifiedGarbage.Proof.Bignum.X86.ReverseBuffer
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.ReadPrefix
import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Bignum.X86.StoreBEArgs`, which this module and modules that import it used -/

section

/-! # Setting the source pointer for RSA integer export -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont.X86

theorem storeBEArgs_ok (s : State) (src : Nat) {k : Nat} (hk : 0 < k)
    (count : s.gpr .ecx = BitVec.ofNat 32 k) :
    WP isa (.block (storeBEArgs src)) s fun t =>
      t.gpr .esi = (s.gpr .edi + BitVec.ofNat 32 src) + BitVec.ofNat 32 (k - 1) ∧
      t.mem = s.mem ∧ Keeps [.esi] s t := by
  unfold storeBEArgs
  refine wp_movS rfl fun s₁ u₁ _ => ?_
  refine wp_addS rfl fun s₂ u₂ _ => ?_
  refine wp_addS rfl fun s₃ u₃ _ => ?_
  refine wp_subS rfl fun t u₄ _ => WP.block_nil ?_
  refine ⟨?_, ?_, ((u₁.keeps.trans u₂.keeps).trans u₃.keeps).trans u₄.keeps⟩
  · rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, u₂.other .ecx (by decide),
      u₁.other .ecx (by decide), count]
    change (s.gpr .edi + BitVec.ofNat 32 src) + BitVec.ofNat 32 k - BitVec.ofNat 32 1 = _
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      Offset.ofNat_sub_ofNat (by omega_using [hk])]
  · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]

end VG.Proof.Bignum.X86

end

end

/-! # Exact big-endian export of the low bytes of an RSA workspace integer -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem storeBE_read_ok {s : State} {base : Addr} {bytes src len : Nat}
    (hs : Scr s base bytes) (hl : 0 < len) (ho : src + len ≤ bytes)
    (hc : s.gpr .ecx = BitVec.ofNat 32 len)
    (dstFit : (s.gpr .ebx).toNat + len ≤ 2 ^ 32)
    (write : InRegions s.wr (byteAddr (s.gpr .ebx)) len)
    (sep : Region.Disjoint ⟨off base src, len⟩ ⟨byteAddr (s.gpr .ebx), len⟩) :
    WP isa (storeBE src) s fun t =>
      Spec.Rsa.bytesAt t.mem (byteAddr (s.gpr .ebx)) len =
        Spec.Rsa.i2osp (s.mem.read (off base src) len).toNat len ∧
      Frame [⟨byteAddr (s.gpr .ebx), len⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .esi, .ecx] s t := by
  have nw := hs.nowrap
  let source := s.gpr .edi + BitVec.ofNat 32 src
  have sourceAddr : byteAddr source = off base src := hs.ea (by omega_using [hl, ho])
  have sourceNat : source.toNat = base.toNat + src := by
    dsimp only [source]
    rw [BitVec.toNat_add, hs.edi_toNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show src < 2 ^ 32 by omega_using [hl, ho, nw]), Nat.mod_eq_of_lt (by omega_using [hl, ho, nw])]
  unfold storeBE
  refine WP.seq (WP.mono (storeBEArgs_ok s src hl hc) fun u ⟨P, M, K⟩ => ?_)
  refine WP.mono (reverseBuffer_ok u (src := source) (dst := s.gpr .ebx) hl
    (by omega_using [ho, nw, sourceNat]) dstFit (by have := hs.size_lt; omega_using [ho, this])
    (by rw [K.2.1, K.2.2, sourceAddr]; exact hs.read ho)
    (by rw [K.2.2]; exact write) (by rw [sourceAddr]; exact sep)
    (K.1 .ebx (by decide)) P (by rw [K.1 .ecx (by decide), hc]))
    fun t ⟨V, F, _, T⟩ => ?_
  rw [sourceAddr, M] at V
  rw [M] at F
  exact ⟨V, F, (K.mono (by decide)).trans T⟩

theorem storeBE_ok {s : State} {base : Addr} {bytes src n len : Nat}
    (hs : Scr s base bytes) (hl : 0 < len) (hlen : len ≤ 8 * n)
    (ho : src + 8 * n ≤ bytes) (hc : s.gpr .ecx = BitVec.ofNat 32 len)
    (valueFit : wordsVal s.mem base src n < 2 ^ (8 * len))
    (dstFit : (s.gpr .ebx).toNat + len ≤ 2 ^ 32)
    (write : InRegions s.wr (byteAddr (s.gpr .ebx)) len)
    (sep : Region.Disjoint ⟨off base src, len⟩ ⟨byteAddr (s.gpr .ebx), len⟩) :
    WP isa (storeBE src) s fun t =>
      Spec.Rsa.bytesAt t.mem (byteAddr (s.gpr .ebx)) len =
        Spec.Rsa.i2osp (wordsVal s.mem base src n) len ∧
      Frame [⟨byteAddr (s.gpr .ebx), len⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .esi, .ecx] s t := by
  refine WP.mono (storeBE_read_ok hs hl (by omega_using [hlen, ho]) hc dstFit write sep) fun t ⟨V, F, K⟩ => ?_
  have eq : (s.mem.read (off base src) (8 * n)).toNat = wordsVal s.mem base src n := by
    rw [wordsVal_eq_val32, ← read_eq_val32]
    congr 2 <;> omega_using []
  rw [read_prefix_value s.mem _ hlen (by rw [eq]; exact valueFit), eq] at V
  exact ⟨V, F, K⟩

end VG.Proof.Bignum.X86
