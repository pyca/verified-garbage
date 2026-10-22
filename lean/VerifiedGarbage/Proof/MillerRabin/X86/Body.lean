module

public import VerifiedGarbage.Proof.MillerRabin.X86.Arithmetic
public import VerifiedGarbage.Proof.MillerRabin.X86.RestoreRegisters

/-! # The callable body's result, preserved bytes, and restored registers -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (wOf)

def BodyResult (s t : State) : Prop :=
  (∀ r ∈ calleeSaved, t.gpr r = (allocFrame VG.Impl.MillerRabin.X86.frameBytes s).gpr r) ∧
  Frame (bodyAreas s) s.mem t.mem ∧ ∃ σ, SnapshotReady s σ ∧
    t.gpr .eax = BitVec.ofNat 32 (finalFlag σ (wsOf s) (wOf s.mem (wsOf s))).toNat ∧
    Spec.MillerRabin.Keeps Spec.MillerRabin.compact (wsOf s) (arg s 1).toNat
      (wOf s.mem (wsOf s)) σ.mem t.mem

theorem body_ok {s : State} (A : RoundABI s) :
    WP isa body (allocFrame VG.Impl.MillerRabin.X86.frameBytes s) (BodyResult s) := by
  unfold body seqs
  simp only [List.foldr_cons, List.foldr_nil]
  refine WP.seq (WP.mono (entry_ok A) fun u entry => ?_)
  refine WP.seq (WP.mono (snapshot_ok A entry) fun σ ready => ?_)
  have facts := round_facts_of (bytes := bytesOf s) rfl ready.width ready.layout ready.prepared ready.length
  have initial := Stage.initial ready.context ready.room (w := wOf s.mem (wsOf s))
  refine WP.seq (WP.mono (arithmetic_ok facts initial (prepared_tail ready.width ready.prepared)) ?_)
  rintro v ⟨stage, flag⟩
  refine WP.seq (WP.mono (restore_stage (len := (arg s 1).toNat) facts stage (by dsimp only [bytesOf]; omega) ready.tail ready.array) ?_)
  rintro z ⟨keepsWS, flagZ, restored, K⟩
  have saved := restore_saved ready.saved stage facts.fit restored K
  have ctxZ := stage.context.of_keeps K
  have spZ : z.gpr .esp = (allocFrame VG.Impl.MillerRabin.X86.frameBytes s).gpr .esp :=
    ((K.1 .esp (by decide)).trans stage.stack).trans ready.sp
  have frameZ := restore_body_frame facts.fit (ready.stage_frame stage facts.fit) restored
  refine WP.seq (WP.mono (finish_ok ctxZ facts.fit saved spZ (flagZ.trans flag)) ?_)
  rintro t ⟨registers, value, mem, _, _⟩
  refine WP.block_nil ⟨registers, ?_, σ, ready, value, ?_⟩
  · rw [mem]
    exact frameZ
  · rw [mem]
    exact keepsWS

end VG.Proof.MillerRabin.X86
