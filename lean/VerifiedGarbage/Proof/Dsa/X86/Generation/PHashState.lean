module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Frame
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashResources

/-! # Stable inputs and disjoint contribution buffers for repeated seed hashing -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

structure ContributionPlan where
  frame : Addr
  source : BitVec 32
  wrapped : BitVec 32
  hashes : BitVec 32
  scratch : BitVec 32
  seed : List Byte
  count : Nat
  offset : Nat
  stack : Region

def ContributionPlan.output (G : ContributionPlan) (j : Nat) : BitVec 32 :=
  G.hashes + BitVec.ofNat 32 ((G.count - j) * G.seed.length)

def ContributionPlan.writes (G : ContributionPlan) {H : Hash} (K : HashOK H) (j : Nat) : List Region :=
  [⟨G.wrapped.setWidth 64, G.seed.length⟩, ⟨(G.scratch + 512#32).setWidth 64, H.S⟩,
   ⟨(G.output j).setWidth 64, H.F⟩, ⟨G.scratch.setWidth 64, K.Wb⟩, G.stack]

structure ContributionLayout {H : Hash} (K : HashOK H) (G : ContributionPlan) : Prop where
  lengthBound : G.seed.length < 2 ^ 31
  offsetBound : G.offset + G.count < 2 ^ 24
  sourceFit : G.source.toNat + G.seed.length ≤ 2 ^ 32
  sourceWrapped : Region.Disjoint ⟨G.source.setWidth 64, G.seed.length⟩ ⟨G.wrapped.setWidth 64, G.seed.length⟩
  digestLength : H.D = G.seed.length
  finalLength : H.F = G.seed.length
  frameApart : ∀ j ≤ G.count, ∀ r ∈ G.writes K j, Region.Disjoint ⟨G.frame, VG.Impl.Dsa.X86.Generation.frameBytes⟩ r
  sourceApart : ∀ j ≤ G.count, ∀ r ∈ G.writes K j, Region.Disjoint ⟨G.source.setWidth 64, G.seed.length⟩ r
  outputApart : ∀ i ≤ G.count, ∀ j ≤ G.count, i ≠ j → ∀ r ∈ G.writes K j,
    Region.Disjoint ⟨(G.output i).setWidth 64, G.seed.length⟩ r

structure ContributionReady {H : Hash} (K : HashOK H) (G : ContributionPlan) (s : State) : Prop where
  frame : SearchFrame s G.frame
  stack : stk s = G.stack
  source : s.mem.readW (off G.frame 4) 32 = G.source
  wrapped : s.mem.readW (off G.frame 12) 32 = G.wrapped
  hashes : s.mem.readW (off G.frame 16) 32 = G.hashes
  scratch : s.mem.readW (off G.frame 56) 32 = G.scratch
  offset : s.mem.readW (off G.frame 8) 32 = BitVec.ofNat 32 G.offset
  resources : ∀ j ≤ G.count, HashResources K G.wrapped (G.output j) G.scratch G.seed.length s
  sourceRead : ∀ i < G.seed.length, InRegions (s.rd ++ s.wr) (off (G.source.setWidth 64) i) 1
  wrappedWrite : ∀ i < G.seed.length, InRegions s.wr (off (G.wrapped.setWidth 64) i) 1
  bytes : ∀ i < G.seed.length, s.mem (off (G.source.setWidth 64) i) = G.seed.getD i 0

theorem ContributionReady.keep {H : Hash} {K : HashOK H} {G : ContributionPlan} {s t : State} {j : Nat}
    (R : ContributionReady K G s) (L : ContributionLayout K G) (hj : j ≤ G.count)
    (O : Frame (G.writes K j) s.mem t.mem) {regs : List Reg} (Ke : Keeps regs s t) (sp : .esp ∉ regs) :
    ContributionReady K G t := by
  have header (d : Nat) (hd : d + 4 ≤ VG.Impl.Dsa.X86.Generation.frameBytes) : t.mem.readW (off G.frame d) 32 = s.mem.readW (off G.frame d) 32 :=
    O.readW (Offset.contains_base _ hd (by have := R.frame.nowrap; unfold VG.Impl.Dsa.X86.Generation.frameBytes at *; omega))
      (L.frameApart j hj) (by decide)
  refine ⟨R.frame.keeps Ke sp, ?_, (header 4 (by decide)).trans R.source,
    (header 12 (by decide)).trans R.wrapped, (header 16 (by decide)).trans R.hashes,
    (header 56 (by decide)).trans R.scratch, (header 8 (by decide)).trans R.offset,
    fun i hi => (R.resources i hi).keeps Ke sp, ?_, ?_, ?_⟩
  · rw [stk, Ke.1 _ sp]; exact R.stack
  · intro i hi; rw [Ke.2.1, Ke.2.2]; exact R.sourceRead i hi
  · intro i hi; rw [Ke.2.2]; exact R.wrappedWrite i hi
  · intro i hi
    exact (O.bytes (L.sourceApart j hj) (by change G.seed.length ≤ 2 ^ 64; have := L.lengthBound; omega) hi).trans (R.bytes i hi)
end VG.Proof.Dsa.X86.Generation
