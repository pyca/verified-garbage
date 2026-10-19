module

public import VerifiedGarbage.Impl.Bignum.X86.PrecomputedImport
public import VerifiedGarbage.Proof.Bignum.X86.ImportArray
public import VerifiedGarbage.Proof.Bignum.ExportEncoding
public import VerifiedGarbage.Proof.Framework.CallLay

/-! # Both imported arrays equal the caller's stored precomputation -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Bignum.X86
open VG.Impl.Bignum.X86.PublicContext

theorem precomputedImport_ok {s : State} {base : Addr} {bytes n : Nat} {src : BitVec 32}
    (hs : Scr s base bytes) (positive : 0 < n) (space : size n ≤ bytes)
    (fit : src.toNat + 16 * n ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (byteAddr src) (16 * n))
    (apart : Region.Disjoint ⟨byteAddr src, 16 * n⟩ ⟨base, bytes⟩) (P : s.gpr .esi = src) :
    WP isa (precomputedImport n) s fun t =>
      wordsVal t.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 0) n = wv s.mem (byteAddr src) 0 n ∧
      wordsVal t.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 5) n = wv s.mem (byteAddr src) (8 * n) n ∧
      Frame [⟨off base (VG.Impl.Bignum.X86.PublicContext.slot n 0), 8 * n⟩, ⟨off base (VG.Impl.Bignum.X86.PublicContext.slot n 5), 8 * n⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .esi, .ecx] s t := by
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have b5 := slot_bound (n := n) (i := 5) (by decide)
  have sep := slot_le (n := n) (i := 0) (j := 5) (by decide)
  simp only [stride] at b0 b5 sep
  have nw := hs.nowrap
  let src2 := src + BitVec.ofNat 32 (8 * n)
  have address : byteAddr src2 = off (byteAddr src) (8 * n) := byteAddr_add (by omega)
  have srcNat : src2.toNat = src.toNat + 8 * n := by
    simp only [src2, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 8 * n < 2 ^ 32), Nat.mod_eq_of_lt (by omega : src.toNat + 8 * n < 2 ^ 32)]
  have firstRead : InRegions (s.rd ++ s.wr) (byteAddr src) (8 * n) := by
    simpa only [BitVec.add_zero] using CallLay.inRegions_sub (off := 0) read
      (by omega : 0 + 8 * n ≤ 16 * n) (by omega)
  have sub : Region.Sub ⟨byteAddr src2, 8 * n⟩ ⟨byteAddr src, 16 * n⟩ := by
    rw [address]; exact Offset.sub_base _ (by omega)
  unfold precomputedImport
  refine WP.seq (WP.mono (importArray_ok hs positive (by omega) (by omega) (by omega) firstRead
    (apart.sub_left (Region.sub_prefix (by omega : 8 * n ≤ 16 * n))) P) fun u ⟨N, S, F, K⟩ => ?_)
  have secondRead : InRegions (u.rd ++ u.wr) (byteAddr src2) (8 * n) := by
    rw [K.2.1, K.2.2, address]
    exact CallLay.inRegions_sub read (by omega) (by omega)
  refine WP.mono (importArray_ok (hs.of_keeps K (by decide)) positive (by omega) (by omega)
    (by rw [srcNat]; omega) secondRead (apart.sub_left sub) S) fun t ⟨R, _, Ft, Kt⟩ => ?_
  refine ⟨?_, ?_, (F.mono (by simp)).trans (Ft.mono (by simp)), K.trans Kt⟩
  · have V : wordsVal t.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 0) n = wordsVal u.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 0) n := by
      apply wordsVal_frame Ft (Region.contains_self _ _) ?_ (by omega)
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    rw [V, N, ← read_eq_wv]
    simp only [off, BitVec.add_zero]
  · have Original : u.mem.read (byteAddr src2) (8 * n) = s.mem.read (byteAddr src2) (8 * n) := F.read (r := ⟨byteAddr src, 16 * n⟩)
      (by rw [address]; exact Offset.contains_base _ (by omega) (by omega))
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr
          exact apart.sub_right (Offset.sub_base _ (by omega))) (by omega)
    rw [R, Original, address, read_eq_wv]

end VG.Proof.Bignum.X86.PublicContext
