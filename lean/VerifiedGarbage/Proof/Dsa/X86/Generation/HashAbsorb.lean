module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashAfter

/-! # Absorb seed bytes using the existing SHA initialization and update proofs -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

theorem hash_absorb {H : Hash} {ok : HashOK H} {st data digest scratch : BitVec 32} {len : Nat} {s : State}
    (G : HashGeometry ok st data digest scratch len s) (R : HashRegisters st data scratch len s) :
    WP isa (Impl.Dsa.X86.Generation.hashAbsorb H) s fun t =>
      HashAfter ok st digest scratch s t ∧ HashRegisters st data scratch len t ∧
      ok.SH.Repr t.mem (st.setWidth 64) (Spec.Sha256.bytesAt s.mem (data.setWidth 64) len) := by
  unfold Impl.Dsa.X86.Generation.hashAbsorb
  refine WP.seq (init_frame ok (G.init_args R) fun u A empty => ?_)
  have Gu := G.after A
  have Ru := R.after A
  have Au := hash_after_mono (ok := ok) (digest := digest) (scratch := scratch) A
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self)
  refine WP.seq (WP.mono (hash_update_setup Ru) ?_)
  rintro v ⟨Rv, edx, ecx, eax, memory, K⟩
  have Gv := Gu.of_regions K.2.1 K.2.2 (K.1 _ (by decide))
  have Av := hash_after_setup (ok := ok) (st := st) (digest := digest) (scratch := scratch) memory K
  have emptyV : ok.SH.Repr v.mem (st.setWidth 64) [] := by rw [memory]; exact empty
  refine upd_frame ok (Gv.update_args Rv eax ecx edx) fun t B absorb => ?_
  have Bt := hash_after_mono (digest := digest) B (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have repr := absorb [] emptyV rfl
  rw [List.nil_append, memory, G.seed_bytes Au.frame] at repr
  exact ⟨hash_after_trans (hash_after_trans Au Av) Bt, Rv.after B, repr⟩

end VG.Proof.Dsa.X86.Generation
