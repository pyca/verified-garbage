module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashFinish

/-! # The complete seed hash uses only existing verified SHA operations -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

theorem hash_digest_setup {s : State} {st data scratch digest : BitVec 32} {len offset : Nat}
    (R : HashRegisters st data scratch len s) (position : scratch + BitVec.ofNat 32 offset = digest) :
    WP isa (.block [.mov .edx (.reg .ebp), .alu .add .edx (.imm (BitVec.ofNat 32 offset))]) s fun t =>
      t.gpr .edx = digest ∧ t.mem = s.mem ∧ Keeps [.edx] s t := by
  refine wp_movS rfl fun u U _ => wp_addS rfl fun t T _ => WP.block_nil ?_
  exact ⟨by rw [T.gpr, U.gpr, R.scratch]; exact position, by rw [T.mem, U.mem], U.keeps.trans T.keeps⟩

theorem seed_hash {H : Hash} {ok : HashOK H} {st data digest scratch : BitVec 32} {len offset : Nat} {s : State}
    (G : HashGeometry ok st data digest scratch len s) (R : HashRegisters st data scratch len s)
    (position : scratch + BitVec.ofNat 32 offset = digest) :
    WP isa (Impl.Dsa.X86.Generation.seedHash H offset) s fun t =>
      HashAfter ok st digest scratch s t ∧ HashRegisters st data scratch len t ∧
      (Spec.Sha256.bytesAt t.mem (digest.setWidth 64) H.F).take H.D =
        ok.SH.H.hash (Spec.Sha256.bytesAt s.mem (data.setWidth 64) len) := by
  unfold Impl.Dsa.X86.Generation.seedHash
  refine WP.seq (WP.mono (hash_absorb G R) ?_)
  rintro u ⟨A, Ru, repr⟩
  have Gu := G.after A
  refine WP.seq (WP.mono (hash_digest_setup Ru position) ?_)
  rintro v ⟨edx, memory, K⟩
  have Rv := Ru.of_keeps K (by decide)
  have Gv := Gu.of_regions K.2.1 K.2.2 (K.1 _ (by decide))
  have Av := hash_after_setup (ok := ok) (st := st) (digest := digest) (scratch := scratch) memory (K.mono (by decide))
  refine WP.mono (hash_finish Gv Rv edx (by rw [memory]; exact repr) (by simp only [Spec.Sha256.bytesAt, List.length_map, List.length_range])) ?_
  rintro t ⟨B, Rt, value⟩
  exact ⟨hash_after_trans (hash_after_trans A Av) B, Rt, value⟩

end VG.Proof.Dsa.X86.Generation
