module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeImport
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeOut
public import VerifiedGarbage.Proof.Bignum.X86.PublicPowerFrame

/-! # Correct precomputation for a validated modulus of a fixed width -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicContext
open VG.Proof.Mont VG.Proof.Mont.X86

theorem precomputeSized_ok {s : State} {base : Addr} {bytes n len : Nat} {np dst : BitVec 32}
    (hs : Scr s base bytes) (hn : 0 < n) (hn32 : 128 * n < 2 ^ 32)
    (hz : size n ≤ bytes) (hl : 0 < len) (hlen : len ≤ 8 * n)
    (NP : CallArgument s base bytes 2 np) (NL : CallArgument s base bytes 3 (BitVec.ofNat 32 len))
    (DP : CallArgument s base bytes 0 dst)
    (nf : np.toNat + len ≤ 2 ^ 32) (nr : InRegions (s.rd ++ s.wr) (byteAddr np) len)
    (ns : Region.Disjoint ⟨byteAddr np, len⟩ ⟨base, bytes⟩)
    (fit : dst.toNat + 16 * n ≤ 2 ^ 32) (write : InRegions s.wr (byteAddr dst) (16 * n))
    (apart : Region.Disjoint ⟨base, bytes⟩ ⟨byteAddr dst, 16 * n⟩)
    (gt : 1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr np) len))
    (odd : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr np) len) % 2 = 1) :
    WP isa (PrecomputeFn.sized n) s fun t =>
      t.gpr .eax = 1 ∧
      Spec.Rsa.wordsAt t.mem (byteAddr dst) (2 * n) =
        Spec.Rsa.toWords (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr np) len)) n ++
        Spec.Rsa.toWords (2 ^ (128 * n) % Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr np) len)) n ∧
      Frame [⟨off base 16, bytes - 16⟩, ⟨byteAddr dst, 16 * n⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have nw := hs.nowrap
  have sz := size_eq n
  unfold PrecomputeFn.sized
  refine WP.seq (WP.mono (precomputeImport_ok hs hn hz hl hlen NP NL nf nr ns)
    fun u ⟨N, O, K⟩ => ?_)
  refine WP.seq (WP.mono (setup_ok (hs.of_keeps K (by decide)) hn hn32 hz N gt odd)
    fun v ⟨C, _, R, Ov, Kv⟩ => ?_)
  have Os : Outside base 16 (bytes - 16) s.mem v.mem :=
    (O.mono (by omega) (by omega)).trans (power_saved (Ov.mono (by
      intro r hr; exact List.mem_append_left _ hr)) hz)
  have Ks : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v := K.trans (Kv.mono (by decide))
  have D := (DP.keep Ks (by decide) (Os.mono (by omega) (by omega))).readSrc
  refine WP.seq (wp_movS D fun w T _ => WP.block_nil ?_)
  refine WP.mono (precomputeOut_ok (C.scr.of_keeps T.keeps (by decide)) hn hz fit
    (by rw [T.keeps.2.2, Ks.2.2]; exact write) apart T.gpr) fun t ⟨B, V, F, Kt⟩ => ?_
  refine ⟨B, ?_, ?_, (Ks.trans (T.keeps.mono (by decide))).trans (Kt.mono (by decide))⟩
  · rw [V, T.mem, R]
    have M := C.mod.val
    change wordsVal v.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 0) n = _ at M
    rw [M]
  · have Fsv := outside_frame Os (by omega)
    rw [← T.mem] at Fsv
    exact (Fsv.mono (by simp)).trans (F.mono (by simp))

end VG.Proof.Bignum.X86.PublicContext
