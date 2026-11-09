module

-- separate module: its proofs build in parallel with `RndCT`'s, which `RndVerified` also imports

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.RndCall
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.RndReject

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on PPC64LE: correctness

The pieces in order (`body_ok`), from the frame's push to its pop
(`code_correct`), to the contract's postcondition by name (`post`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Rnd

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Random VG.Proof.RsaPkcs1Sig.PPC64LE

theorem post_congr {s x y : State} (hm : x.mem = y.mem) (h3 : x.gpr .r3 = y.gpr .r3) (h : post s y) : post s x := by
  unfold post at *; rw [hm, h3]; exact h

theorem freed_mem' (b : Nat) (s : State) : (freed b s).mem = s.mem := rfl

theorem freed_gpr' (b : Nat) (s : State) : (freed b s).gpr = s.gpr := rfl

theorem body_ok {s : State} (hp : RPre s) :
    WP isa body (allocated frameBytes s) fun w => abiPreserved s (freed frameBytes w) ∧
      post s (freed frameBytes w) := by
  unfold body
  refine WP.seq (WP.mono (setup_ok hp) ?_)
  intro t ht
  obtain ⟨hM, h0⟩ := ht
  refine WP.seq (WP.mono (scan_ok hp hM h0) ?_)
  intro u hu
  obtain ⟨i, hI, hres⟩ := hu
  refine WP.seq (WP.mono (full_ok hp hI) ?_)
  intro v hv'
  obtain ⟨hv, ev⟩ := hv'
  refine WP.seq (WP.mono (Q := Fin s) ?_ ?_)
  · rcases hres with ⟨hf, hpre⟩ | ⟨hi, hc⟩
    · exact WP.ite true (by rw [ev, decide_eq_true hf.symm]) (fun _ => accept_ok hp hM hv hf hpre)
        (fun h => absurd h (by decide))
    · subst hi
      exact WP.ite false (by rw [ev, decide_eq_false (by omega)]) (fun h => absurd h (by decide))
        fun _ => reject_ok hp hM hv hc
  · intro w F
    refine WP.mono (restore_ok F.sv) ?_
    intro w' hw'
    refine ⟨hw'.1, ?_⟩
    have h3 : (freed frameBytes w').gpr .r3 = w.gpr .r3 := by rw [freed_gpr']; exact hw'.2.1
    have hm : (freed frameBytes w').mem = w.mem := by rw [freed_mem']; exact hw'.2.2
    exact post_congr hm h3 F.post

theorem code_correct (s : State) (h : (Spec.RsaPkcs1Enc.encryptRandomContract abi rndStack).pre s) :
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ post s s' := by
  have hp := pre_of h
  show WP isa code s fun t => abiPreserved s t ∧ post s t
  unfold code
  exact WP.alloc ⟨by decide, by decide, by decide⟩ (by have := hp.sp1; unfold rndStack at this; omega) (body_ok hp)

end VG.Proof.RsaPkcs1Enc.PPC64LE.Rnd
