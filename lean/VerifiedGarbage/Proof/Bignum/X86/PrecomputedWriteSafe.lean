module
public import VerifiedGarbage.Impl.Bignum.X86.PublicFn
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes

import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Bignum.X86.ExportBE
import VerifiedGarbage.Proof.Bignum.X86.PublicLayout
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-! # Export remains safe even when malformed packed keys produce oversized integers -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicContext
open VG.Proof.Mont VG.Proof.Mont.X86

theorem writeResult_safe {s : State} {base : Addr} {bytes n len : Nat} {out : BitVec 32}
    (hs : Scr s base bytes) (hz : size n ≤ bytes) (hl : 0 < len) (hlen : len ≤ 8 * n)
    (accept : Bool) (Mask : s.mem.readW (off base 144) 32 = if accept then BitVec.allOnes 32 else 0)
    (P : readSrc s (.mem (PublicFn.argument 0)) = some out)
    (L : readSrc s (.mem (PublicFn.argument 1)) = some (BitVec.ofNat 32 len))
    (fit : out.toNat + len ≤ 2 ^ 32) (write : InRegions s.wr (byteAddr out) len)
    (sep : Region.Disjoint ⟨base, bytes⟩ ⟨byteAddr out, len⟩) :
    WP isa (PublicFn.writeResult n) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 accept.toNat ∧
      Frame [⟨byteAddr out, len⟩] s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .esi] s t := by
  have b7 := slot_bound (n := n) (i := 7) (by decide)
  have sz := size_eq n
  have nw := hs.nowrap
  simp only [stride] at b7
  unfold PublicFn.writeResult
  refine WP.seq (WP.mono (argumentPair_ok (d := .ebx) (by decide) (by decide) P L)
    fun u ⟨Ptr, Count, M, K⟩ => ?_)
  have hu := hs.of_keeps K (by decide)
  refine WP.seq (WP.mono (storeBE_read_ok hu hl (by omega) Count (by rw [Ptr]; exact fit)
    (by rw [Ptr, K.2.2]; exact write)
    (by rw [Ptr]; exact sep.sub_left (Offset.sub_base base (by omega))))
    fun v ⟨_, F, T⟩ => ?_)
  have hv := hu.of_keeps T (by decide)
  have maskV : v.mem.readW (off base 144) 32 = if accept then BitVec.allOnes 32 else 0 := by
    have R := F.readW (r := ⟨base, bytes⟩) (a := off base 144) (w := 32)
      (Scr.contains hs.nowrap (by omega))
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; rw [Ptr]; exact sep) (by decide)
    rw [R, M, Mask]
  refine wp_movS (readSrc_sc hv (by change 144 + 4 ≤ bytes; omega)) fun w U _ => ?_
  refine wp_logicS (.inl rfl) rfl fun t B => WP.block_nil ?_
  have mt : t.mem = v.mem := B.mem.trans U.mem
  refine ⟨?_, ?_, ?_⟩
  · rw [B.gpr, U.gpr]
    change (if AluOp.and = AluOp.and then
      v.mem.readW (off base 144) 32 &&& 1 else v.mem.readW (off base 144) 32 ^^^ 1) = _
    rw [maskV]
    cases accept <;> rfl
  · simpa only [mt, M, Ptr] using F
  · exact (((K.mono (by decide)).trans (T.mono (by decide))).widen U.keeps).widen B.keeps

end VG.Proof.Bignum.X86.PublicContext
