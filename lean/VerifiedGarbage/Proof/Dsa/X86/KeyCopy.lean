module

public import VerifiedGarbage.Proof.Dsa.X86.KeyCopyStep
public import VerifiedGarbage.Spec.Rsa.Contract

/-! # A bounded masked copy of disjoint buffers -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86

theorem keyCopy_ok {s : State} {src out : BitVec 32} {len : Nat} {mask : BitVec 32}
    (hl : 0 < len) (h32 : len < 2 ^ 32)
    (hs : src.toNat + len ≤ 2 ^ 32) (ho : out.toNat + len ≤ 2 ^ 32)
    (apart : Region.Disjoint ⟨src.setWidth 64, len⟩ ⟨out.setWidth 64, len⟩)
    (hp : s.gpr .esi = src) (hd : s.gpr .edx = out)
    (hc : s.gpr .ecx = BitVec.ofNat 32 len) (hm : s.gpr .ebx = mask)
    (read : ∀ i, i < len → InRegions (s.rd ++ s.wr) (off (src.setWidth 64) i) 1)
    (write : ∀ i, i < len → InRegions s.wr (off (out.setWidth 64) i) 1) :
    WP isa Generate.copyMasked s fun t =>
      KeyCopyInv src out len len mask s t := by
  have I0 : KeyCopyInv src out len 0 mask s s :=
    ⟨by simpa using hp, by simpa using hd, by simpa using hc, hm,
      by intro j hj; omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩
  refine WP.loop (M := isa) (fun k t => ∃ i, k = len - i ∧ i < len ∧ KeyCopyInv src out len i mask s t)
    ?_ len s ⟨0, rfl, hl, I0⟩
  rintro k t ⟨i, rfl, hi, I⟩
  refine WP.mono (keyCopyStep_ok hi h32 hs ho apart
    (by rw [I.keeps.2.1, I.keeps.2.2]; exact read i hi)
    (by rw [I.keeps.2.2]; exact write i hi) I) fun u ⟨next, Z⟩ => ?_
  by_cases done : i + 1 = len
  · refine .inl ⟨?_, done ▸ next⟩
    simp only [eval, Z, done, decide_true, Option.map_some, Bool.not_true]
  · refine .inr ⟨?_, len - (i + 1), by omega, i + 1, rfl, by omega, next⟩
    simp only [eval, Z, decide_eq_false done, Option.map_some, Bool.not_false]

theorem KeyCopyInv.result {s t : State} {src out : BitVec 32} {len : Nat} {mask : BitVec 32}
    (I : KeyCopyInv src out len len mask s t) :
    Spec.Rsa.bytesAt t.mem (out.setWidth 64) len =
      (Spec.Rsa.bytesAt s.mem (src.setWidth 64) len).map
        (fun b => (b.setWidth 32 &&& mask).setWidth 8) := by
  simp only [Spec.Rsa.bytesAt, List.map_map]
  apply List.map_congr_left
  intro i hi
  exact I.bytes i (List.mem_range.mp hi)

end VG.Proof.Dsa.X86
