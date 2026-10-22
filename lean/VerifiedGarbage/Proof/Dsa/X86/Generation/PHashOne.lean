module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.PSeed
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashDigestWorkspace
import VerifiedGarbage.Proof.Dsa.X86.Generation.WorkspaceSource
import VerifiedGarbage.Proof.Framework.Offset

/-! One exact FIPS modulus-search hash contribution, using the common SHA and seed adder. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

def PHashOneFrame (base : Addr) (sp : BitVec 32) (seedLen destination digestLen : Nat) (s t : State) : Prop :=
  Frame [⟨off base Layout.wrappedSeed, seedLen⟩, ⟨off base Layout.hash, 8192⟩,
    ⟨off base destination, digestLen⟩, below sp 52] s.mem t.mem

theorem p_hash_one {H : Hash} (ok : HashOK H) {s : State} {base : Addr}
    {bytes offset j count : Nat} {src : BitVec 32} {seed : List Byte}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (room : RoundRoom (s.gpr .esp) base bytes)
    (tape : WitnessTape base bytes (s.gpr .esp) src seed s) (length : seed.length ≤ 32)
    (pointer : s.mem.readW (off base seedPointer) 32 = src)
    (value : s.mem.readW (off base candidateOffset) 32 = BitVec.ofNat 32 offset)
    (small : offset + j < 2 ^ 31)
    (hash : ∀ x, ok.SH.H.hash x = Spec.Dsa.seedHash (8 * H.D) x)
    (destinationFit : Layout.hashes + (count - j) * H.D + H.D < bytes) :
    WP isa (pHashOne H seed.length count j) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base (Layout.hashes + (count - j) * H.D)) H.D =
        Spec.Dsa.seedHash (8 * H.D) (Spec.Dsa.encodeBE seed.length (Spec.Dsa.decodeBE seed + (offset + j))) ∧
      PHashOneFrame base (s.gpr .esp) seed.length (Layout.hashes + (count - j) * H.D) H.D s t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t := by
  unfold pHashOne
  refine WP.seq (WP.mono (p_seed scr capacity tape length pointer value small) fun a ⟨encoded, F, K⟩ => ?_)
  refine WP.seq (WP.mono (workspace_source (s := a) Layout.wrappedSeed) fun b ⟨source, memory, KB⟩ => ?_)
  have SB := (scr.of_keeps K (by decide)).of_keeps KB (by decide)
  have RB : RoundRoom (b.gpr .esp) base bytes := by rw [KB.1 .esp (by decide), K.1 .esp (by decide)]; exact room
  have srcAddr : (a.gpr .edi + BitVec.ofNat 32 Layout.wrappedSeed).setWidth 64 = off base Layout.wrappedSeed :=
    workspace_pointer_address (scr.of_keeps K (by decide)) (by unfold Layout.wrappedSeed; omega)
  refine WP.mono (hash_digest_workspace (input := Spec.Dsa.encodeBE seed.length (Spec.Dsa.decodeBE seed + (offset + j))) ok SB capacity RB source (by omega)
    (by rw [← KB.1 .edi (by decide)]; exact workspace_pointer_fit SB (by unfold Layout.wrappedSeed; omega))
    (by rw [srcAddr]; exact SB.read (by unfold Layout.wrappedSeed; omega))
    (by rw [srcAddr]; exact Offset.disjoint base (.inr (by decide)) (by unfold Layout.wrappedSeed; omega) (by decide))
    (by rw [srcAddr]; exact RB.apart.sub_right (Offset.sub_base base (by unfold Layout.wrappedSeed; omega)))
    (by rw [srcAddr, memory]; exact encoded)
    (by unfold Layout.wrappedSeed Layout.hashes; omega) destinationFit) fun t ⟨hashed, FT, KT⟩ => ?_
  refine ⟨hashed.trans (hash _), ?_, ((K.mono (by decide)).trans (KB.mono (by decide))).trans KT⟩
  have first : PHashOneFrame base (s.gpr .esp) seed.length (Layout.hashes + (count - j) * H.D) H.D s b := by
    unfold PHashOneFrame
    rw [memory]
    exact F.mono (by simp)
  apply first.trans
  rw [KB.1 .esp (by decide), K.1 .esp (by decide)] at FT
  exact FT.mono (by simp)

end VG.Proof.Dsa.X86.Generation
