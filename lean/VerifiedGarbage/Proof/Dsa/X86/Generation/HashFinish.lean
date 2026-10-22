module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashAbsorb

/-! # Finalize seed hashes with the existing SHA serialization and padding proof -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

theorem hash_finish_setup {s : State} {st data scratch digest : BitVec 32} {len : Nat}
    (R : HashRegisters st data scratch len s) (digestReg : s.gpr .edx = digest) :
    WP isa (.block [.mov .eax (.reg .edi), .mov .ecx (.imm 0)]) s fun t =>
      HashRegisters st data scratch len t ∧ t.gpr .edx = digest ∧ t.gpr .ecx = 0 ∧
      t.gpr .eax = BitVec.ofNat 32 len ∧ t.mem = s.mem ∧ Keeps [.edx, .ecx, .eax] s t := by
  refine wp_movS rfl fun u U _ => wp_movS rfl fun t T _ => WP.block_nil ?_
  have K : Keeps [.edx, .ecx, .eax] s t := (U.keeps.mono (by decide)).trans (T.keeps.mono (by decide))
  exact ⟨R.of_keeps K (by decide), by rw [T.other .edx (by decide), U.other .edx (by decide)]; exact digestReg,
    T.gpr, by rw [T.other .eax (by decide), U.gpr, R.length], by rw [T.mem, U.mem], K⟩

theorem hash_finish {H : Hash} {ok : HashOK H} {st data digest scratch : BitVec 32} {len : Nat} {s : State} {bs : List Byte}
    (G : HashGeometry ok st data digest scratch len s) (R : HashRegisters st data scratch len s)
    (digestReg : s.gpr .edx = digest) (repr : ok.SH.Repr s.mem (st.setWidth 64) bs) (length : bs.length = len) :
    WP isa (Impl.Dsa.X86.Generation.hashFinish H) s fun t =>
      HashAfter ok st digest scratch s t ∧ HashRegisters st data scratch len t ∧
      (Spec.Sha256.bytesAt t.mem (digest.setWidth 64) H.F).take H.D = ok.SH.H.hash bs := by
  unfold Impl.Dsa.X86.Generation.hashFinish
  refine WP.seq (WP.mono (hash_finish_setup R digestReg) ?_)
  rintro u ⟨Ru, edx, ecx, eax, memory, K⟩
  have Gu := G.of_regions K.2.1 K.2.2 (K.1 _ (by decide))
  have Au := hash_after_setup (ok := ok) (st := st) (digest := digest) (scratch := scratch) memory K
  have reprU : ok.SH.Repr u.mem (st.setWidth 64) bs := by rw [memory]; exact repr
  refine fin_frame ok (Gu.finish_args Ru eax ecx edx) fun t B finalize => ?_
  have Bt : HashAfter ok st digest scratch u t := B
  refine ⟨hash_after_trans Au Bt, Ru.after B, finalize bs reprU ?_ ?_⟩
  · rw [length]
    have := G.small
    omega
  · rw [length]
    exact zero_append_ofNat G.small

end VG.Proof.Dsa.X86.Generation
