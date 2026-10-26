module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Start
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.NativeResult
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Basic.IsEmpty.Defs

/-! # FFDH parameter generation on x86-64: the complete callable body -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64

def BodyPost (s t : State) : Prop :=
  let p := candidateOfState s
  ∃ used, CandidateTape p used t ∧ t.gpr .rdi = p.B ∧ NativeResult p used t.mem ∧
    (word t.mem p.B (8 * oStatus) = 1 → Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem p.op p.k) = p.P) ∧
    (∀ i < 6, word t.mem p.B (8 * i) = s.gpr (saved.getD i .rax)) ∧ Keep (.rdi :: mmRegs) s t

theorem body_ok (M : Mont) (R : R2Impl M) (K : Kernel) {s : State} (c : PcCtx s) :
    WP isa (body M.mm R.code K.run) s (BodyPost s) := by
  let p := candidateOfState s
  change WP isa (body M.mm R.code K.run) s (fun t => ∃ used,
    CandidateTape p used t ∧ t.gpr .rdi = p.B ∧ NativeResult p used t.mem ∧
      (word t.mem p.B (8 * oStatus) = 1 → Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem p.op p.k) = p.P) ∧
      (∀ i < 6, word t.mem p.B (8 * i) = s.gpr (saved.getD i .rax)) ∧ Keep (.rdi :: mmRegs) s t)
  unfold body
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (candidateEntry_base c) fun u ⟨hu, hdu, hstatus, _, hsaved, ku⟩ => ?_
  change CandidateTape p 0 u at hu
  change u.gpr .rdi = p.B at hdu
  change word u.mem p.B (8 * oStatus) = 0 at hstatus
  have hlen := hu.base.hdr (oLen, BitVec.ofNat 64 p.k) (by simp [CandidateP.headers])
  have hleft : word u.mem p.B (8 * oRandLeft) = BitVec.ofNat 64 p.rand.length := by simpa using hu.left
  have hrd : ∀ j < 32, InRegions (u.rd ++ u.wr) (off p.B (8 * j)) 8 :=
    fun j hj => hu.base.scr.ld (by omega_using [hj, hu.base.header_room])
  refine WP.mono (WP.keep [.rax] (Q := fun v => v.cf = some (decide (p.rand.length < p.k)) ∧ v.mem = u.mem)
    (by
      xrun [State.ea, hdr, hdrOff, hdu, hleft, hlen, hrd oRandLeft (by decide), hrd oLen (by decide)]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu.base.randLen,
        Nat.mod_eq_of_lt (show p.k < 2 ^ 64 by omega_using [hu.base.widths.2])]) rfl)
    fun v ⟨⟨hcf, hm⟩, kv⟩ => ?_
  obtain ⟨hv, _, _⟩ := hu.same_mem hm kv (by decide)
  have hdv : v.gpr .rdi = p.B := (kv.gpr (by decide)).trans hdu
  have hsavedv : ∀ i < 6, word v.mem p.B (8 * i) = s.gpr (saved.getD i .rax) := by
    intro i hi; rw [hm]; exact hsaved i hi
  have kk : Keep (.rdi :: mmRegs) s v := (ku.trans kv).mono (by decide)
  refine WP.ite (decide (p.rand.length < p.k)) (by simp [eval, hcf]) ?_ ?_
  · intro hshort
    have hr := hv.base.short_result (of_decide_eq_true hshort)
    have hstat : word v.mem p.B (8 * oStatus) = 0 := by rw [hm]; exact hstatus
    refine WP.block_nil ⟨0, hv, hdv, ?_, ?_, hsavedv, kk⟩
    · simp [NativeResult, hr, Spec.Ffdh.candidateStatus, hstat]
    · intro he; rw [hstat] at he; contradiction
  · intro havail
    refine WP.mono (testCandidate_ok M R K hv hdv (by omega_using [of_decide_eq_false havail]))
      fun t ⟨n, _, ht, hdt, hresult, hout, hs, _, kt⟩ => ?_
    exact ⟨p.k + n, ht, hdt, hv.base.nativeResult (by omega_using [of_decide_eq_false havail]) hresult,
      hout, fun i hi => (hs i (by omega)).trans (hsavedv i hi), (kk.trans kt).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
