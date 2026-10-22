module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashFrame

/-! # Compose streaming-call frames while keeping seed data outside them -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

abbrev HashAfter {H : Hash} (ok : HashOK H) (st digest scratch : BitVec 32) (s t : State) : Prop :=
  After s [⟨st.setWidth 64, H.S⟩, ⟨digest.setWidth 64, H.F⟩, ⟨scratch.setWidth 64, ok.Wb⟩] t

theorem hash_after_mono {H : Hash} {ok : HashOK H} {st digest scratch : BitVec 32} {s t : State} {ws : List Region}
    (A : After s ws t) (sub : ∀ r ∈ ws, r ∈ [⟨st.setWidth 64, H.S⟩, ⟨digest.setWidth 64, H.F⟩, ⟨scratch.setWidth 64, ok.Wb⟩]) :
    HashAfter ok st digest scratch s t := by
  refine ⟨A.rd, A.wr, A.cs, A.frame.mono ?_⟩
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact List.mem_append_left _ (sub r hr)
  · exact List.mem_append_right _ hr

theorem hash_after_trans {H : Hash} {ok : HashOK H} {st digest scratch : BitVec 32} {s u t : State}
    (A : HashAfter ok st digest scratch s u) (B : HashAfter ok st digest scratch u t) :
    HashAfter ok st digest scratch s t := by
  refine ⟨B.rd.trans A.rd, B.wr.trans A.wr, fun r hr => (B.cs r hr).trans (A.cs r hr), ?_⟩
  apply A.frame.trans
  simpa only [stk, A.esp] using B.frame

theorem hash_after_setup {H : Hash} {ok : HashOK H} {st digest scratch : BitVec 32} {s t : State}
    (mem : t.mem = s.mem) (K : VG.Proof.Mont.X86.Keeps [.edx, .ecx, .eax] s t) :
    HashAfter ok st digest scratch s t := by
  refine ⟨K.2.1, K.2.2, fun r hr => K.1 r ?_, ?_⟩
  · exact (by decide : ∀ r ∈ calleeSaved, r ∉ [.edx, .ecx, .eax]) r hr
  · rw [mem]
    exact Frame.refl _ _

end VG.Proof.Dsa.X86.Generation
