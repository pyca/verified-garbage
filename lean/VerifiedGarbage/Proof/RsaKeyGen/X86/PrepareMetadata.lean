module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Prepare

/-! # Preparation preserves candidate arguments and the entropy cursor -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Prepare
open VG VG.Proof.Mont VG.Proof.MillerRabin.X86

def protectedHeader (d bytes : Nat) : Prop :=
  d + bytes ≤ 48 ∨ 128 ≤ d ∧ d + bytes ≤ 136 ∨ 144 ≤ d ∧ d + bytes ≤ 224

theorem ranges_apart {g : Geometry} {d bytes : Nat} (safe : protectedHeader d bytes)
    {r : Nat × Nat} (mem : r ∈ ranges g) : d + bytes ≤ r.1 ∨ r.1 + r.2 ≤ d := by
  simp only [ranges, PrepareHeader.ranges, Header.ranges, PreparedR2.ranges,
    PreparedR2.coreRanges, PreparedR2.phaseRanges, Constants.ranges, montWrites,
    Exponent.preparedRanges, Exponent.ranges, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at mem
  repeat' first
    | (rcases mem with mem | mem)
    | (rcases mem with rfl)
  all_goals
    simp only [Geometry.array, Geometry.words, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes,
      VG.Impl.RsaKeyGen.X86.Exponent.markerOffset]
    unfold protectedHeader at safe
    omega

theorem metadata32 {g : Geometry} (v : g.Valid) {m m' : Mem}
    (W : WorkspaceFrame g (ranges g) m m') {d : Nat} (safe : protectedHeader d 4) :
    m'.readW (off g.W d) 32 = m.readW (off g.W d) 32 := by
  apply W.read32 (by have := v.headerFit; unfold protectedHeader at safe; omega)
  exact fun _ mem => ranges_apart safe mem

theorem metadata64 {g : Geometry} (v : g.Valid) {m m' : Mem}
    (W : WorkspaceFrame g (ranges g) m m') {d : Nat} (safe : protectedHeader d 8) :
    m'.readW (off g.W d) 64 = m.readW (off g.W d) 64 := by
  apply W.read64 (by have := v.headerFit; unfold protectedHeader at safe; omega)
  exact fun _ mem => ranges_apart safe mem

end VG.Proof.RsaKeyGen.X86.Prepare
