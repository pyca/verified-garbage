module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryTape
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
import VerifiedGarbage.Proof.Dsa.Generation.Memory

/-! # Persistent inputs shared by every phase of the native parameter search -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

structure GenerationContext where
  geo : GenerationGeometry
  seeds : GenerationTape geo
  hs : GenerationTape geo
  rand : GenerationTape geo
  saved : Nat → BitVec 64
  wrappedSlot : saved 3 = VG.Proof.Bignum.off geo.B wrappedSeed
  hashesSlot : saved 4 = VG.Proof.Bignum.off geo.B hashes
  baseSlot : saved 5 = geo.B
  seedsSlot : saved 8 = seeds.ptr
  seedsLengthSlot : saved 9 = BitVec.ofNat 64 seeds.bytes.length
  hSlot : saved 11 = hs.ptr
  hLengthSlot : saved 13 = BitVec.ofNat 64 hs.bytes.length
  randSlot : saved 14 = rand.ptr
  randLengthSlot : saved 15 = BitVec.ofNat 64 rand.bytes.length
  pLenSlot : saved 17 = BitVec.ofNat 64 geo.pLen
  qLenSlot : saved 18 = BitVec.ofNat 64 geo.qLen
  hashLenSlot : saved 26 = BitVec.ofNat 64 geo.qLen

def generationSlots : List Nat := [3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 17, 18, 26]

def GenerationContext.changed (p : GenerationContext) : List Region :=
  [⟨p.geo.B, usedBytes p.geo.pLen⟩, ⟨p.geo.F, frameBytes⟩, below p.geo.F 16]

structure GenerationTapeMemory {p : GenerationGeometry} (tape : GenerationTape p) (s : State) : Prop where
  cover : Covers [⟨tape.ptr, tape.bytes.length⟩] (s.rd ++ s.wr)
  bytes : Spec.Rsa.bytesAt s.mem tape.ptr tape.bytes.length = tape.bytes

structure GenerationMemory (p : GenerationContext) (W : Nat → BitVec 64) (s : State) : Prop where
  layout : Lay s p.geo.F p.geo.hash
  rep : ∃ V, Rep s.mem p.geo.F p.geo.hash V W
  slots : ∀ k ∈ generationSlots, W k = p.saved k
  scratch : Scr s p.geo.B (usedBytes p.geo.pLen)
  seeds : GenerationTapeMemory p.seeds s
  hs : GenerationTapeMemory p.hs s
  rand : GenerationTapeMemory p.rand s

theorem GenerationTapeMemory.source {p : GenerationGeometry} {tape : GenerationTape p} {s : State}
    (h : GenerationTapeMemory tape s) {d n : Nat} (hd : d + n ≤ usedBytes p.pLen) :
    Src s (VG.Proof.Bignum.off p.B d) n tape.ptr tape.bytes := by
  apply tape.source hd
  · intro i hi
    exact h.cover _ _ ⟨⟨tape.ptr, tape.bytes.length⟩, by simp, Offset.contains_base _ (by omega) (by omega_using [hi, tape.size])⟩
  · intro i hi
    have he := congrArg (fun bs : List Byte => bs[i]?) h.bytes
    simpa only [Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range, hi, ↓reduceIte,
      Option.map_some, List.getElem?_eq_getElem hi, Option.some.injEq] using he

theorem GenerationTapeMemory.frame {p : GenerationContext} {tape : GenerationTape p.geo} {s t : State}
    (h : GenerationTapeMemory tape s) (hf : Frame p.changed s.mem t.mem)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) : GenerationTapeMemory tape t where
  cover := by rw [hr, hw]; exact h.cover
  bytes := by
    rw [VG.Proof.Dsa.Generation.frame_bytesAt hf (by
      intro r hr
      simp only [GenerationContext.changed, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact tape.arena
      · exact tape.frame
      · exact tape.stack) (Nat.le_of_lt tape.size)]
    exact h.bytes

theorem GenerationMemory.frame {p : GenerationContext} {W W' : Nat → BitVec 64} {s t : State}
    (h : GenerationMemory p W s) (L : Lay t p.geo.F p.geo.hash)
    (R : ∃ V, Rep t.mem p.geo.F p.geo.hash V W')
    (hs : ∀ k ∈ generationSlots, W' k = W k)
    (hf : Frame p.changed s.mem t.mem) (hr : t.rd = s.rd) (hw : t.wr = s.wr) : GenerationMemory p W' t :=
  ⟨L, R, fun k hk => (hs k hk).trans (h.slots k hk), h.scratch.congr hw,
    h.seeds.frame hf hr hw, h.hs.frame hf hr hw, h.rand.frame hf hr hw⟩

end VG.Proof.Dsa.AArch64.Generation
