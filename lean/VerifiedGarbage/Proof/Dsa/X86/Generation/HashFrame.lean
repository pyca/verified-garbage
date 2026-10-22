module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashArguments
import VerifiedGarbage.Proof.Framework.Offset

/-! # Seed bytes stay outside all of the streaming calls' writes -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

def hashAreas {H : Hash} (ok : HashOK H) (st digest scratch : BitVec 32) (s : State) : List Region :=
  [⟨st.setWidth 64, H.S⟩, ⟨digest.setWidth 64, H.F⟩, ⟨scratch.setWidth 64, ok.Wb⟩, stk s]

theorem HashGeometry.seed_bytes {H : Hash} {ok : HashOK H} {st data digest scratch : BitVec 32} {len : Nat} {s t : State}
    (G : HashGeometry ok st data digest scratch len s)
    (F : Frame (hashAreas ok st digest scratch s) s.mem t.mem) :
    Spec.Sha256.bytesAt t.mem (data.setWidth 64) len = Spec.Sha256.bytesAt s.mem (data.setWidth 64) len := by
  unfold Spec.Sha256.bytesAt
  apply List.map_congr_left
  intro i hi
  apply F.bytes (R := ⟨data.setWidth 64, len⟩) ?_ (by change len ≤ 2 ^ 64; have := G.small; omega) (List.mem_range.mp hi)
  intro r hr
  simp only [hashAreas, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact G.data_st
  · exact G.data_digest
  · exact G.data_scratch
  · exact G.stack_data.symm

end VG.Proof.Dsa.X86.Generation
