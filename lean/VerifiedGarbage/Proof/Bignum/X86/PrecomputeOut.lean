module

public import VerifiedGarbage.Impl.Bignum.X86.PrecomputeOut
public import VerifiedGarbage.Proof.Bignum.X86.ExportArray
public import VerifiedGarbage.Proof.Bignum.PackedRead
public import VerifiedGarbage.Proof.Bignum.ExportEncoding
public import VerifiedGarbage.Proof.Framework.CallLay

/-! # Export both precomputation arrays in the shared RSA word format -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Bignum.X86
open VG.Impl.Bignum.X86.PublicContext

theorem precomputeOut_ok {s : State} {base : Addr} {bytes n : Nat} {dst : BitVec 32}
    (hs : Scr s base bytes) (positive : 0 < n) (space : size n ≤ bytes)
    (fit : dst.toNat + 16 * n ≤ 2 ^ 32) (write : InRegions s.wr (byteAddr dst) (16 * n))
    (apart : Region.Disjoint ⟨base, bytes⟩ ⟨byteAddr dst, 16 * n⟩) (P : s.gpr .ebx = dst) :
    WP isa (precomputeOut n) s fun t =>
      t.gpr .eax = 1 ∧ Spec.Rsa.wordsAt t.mem (byteAddr dst) (2 * n) =
        Spec.Rsa.toWords (wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 0) n) n ++
        Spec.Rsa.toWords (wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 5) n) n ∧
      Frame [⟨byteAddr dst, 16 * n⟩] s.mem t.mem ∧ Keeps [.eax, .ebx, .esi, .ecx] s t := by
  have b0 := PublicContext.slot_bound (n := n) (i := 0) (by decide)
  have b5 := PublicContext.slot_bound (n := n) (i := 5) (by decide)
  simp only [stride] at b0 b5
  have nw := hs.nowrap
  let dst2 := dst + BitVec.ofNat 32 (8 * n)
  have address : byteAddr dst2 = off (byteAddr dst) (8 * n) := byteAddr_add (by omega)
  have dstNat : dst2.toNat = dst.toNat + 8 * n := by
    simp only [dst2, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 8 * n < 2 ^ 32), Nat.mod_eq_of_lt (by omega : dst.toNat + 8 * n < 2 ^ 32)]
  have firstWrite : InRegions s.wr (byteAddr dst) (8 * n) := by
    simpa only [BitVec.add_zero] using CallLay.inRegions_sub (off := 0) write (by omega : 0 + 8 * n ≤ 16 * n) (by omega)
  have secondSub : Region.Sub ⟨byteAddr dst2, 8 * n⟩ ⟨byteAddr dst, 16 * n⟩ := by
    rw [address]; exact Offset.sub_base _ (by omega)
  have halves : Region.Disjoint ⟨byteAddr dst, 8 * n⟩ ⟨byteAddr dst2, 8 * n⟩ := by
    rw [address]; exact Offset.base_disjoint _ (by omega) (by omega)
  unfold precomputeOut
  refine WP.seq (WP.mono (exportArray_ok hs positive (by omega) (by omega) (by omega) firstWrite
    (apart.sub_right (Region.sub_prefix (by omega : 8 * n ≤ 16 * n))) P) fun u ⟨N, D, F, K⟩ => ?_)
  have hu := hs.of_keeps K (by decide)
  have secondWrite : InRegions u.wr (byteAddr dst2) (8 * n) := by
    rw [K.2.2, address]
    exact CallLay.inRegions_sub write (by omega) (by omega)
  refine WP.seq (WP.mono (exportArray_ok hu positive (by omega) (by omega) (by rw [dstNat]; omega)
    secondWrite (apart.sub_right secondSub) D) fun v ⟨R, _, Fv, Kv⟩ => ?_)
  have Original : wordsVal u.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 5) n = wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 5) n := by
    apply wordsVal_frame F (Scr.contains nw (by omega)) ?_ (by omega)
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact apart.sub_right (Region.sub_prefix (by omega : 8 * n ≤ 16 * n))
  have First := Fv.read (Region.contains_self (byteAddr dst) (8 * n))
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact halves) (by omega)
  refine wp_movS rfl fun t T _ => WP.block_nil ⟨T.gpr, ?_, ?_, ?_⟩
  · rw [T.mem]
    apply wordsAt_two_reads
    · rw [First]; exact N
    · rw [← address, R, Original]
  · rw [T.mem]
    apply (F.sub ?_).trans (Fv.sub ?_)
    · intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega : 8 * n ≤ 16 * n)⟩
    · intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_singleton_self _, secondSub⟩
  · exact (K.trans Kv).trans (T.keeps.mono (by decide))

end VG.Proof.Bignum.X86
