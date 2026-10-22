module

public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Draw
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The FFDH candidate on i686: a phase of Miller–Rabin

`phase j`: the modulus `w` in wide slot `j` prepared, then draws from the
tape at the cursor until `n` witnesses pass, one fails or the tape runs
out: the status `drawStatus` of `checkWitnesses w n` (`phase_ok`), and the
cursor where it left the tape.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Ffdh.X86
open VG.Impl.Ffdh.X86.Candidate

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- A phase for the modulus `w` in wide slot `j`, with `n` witnesses to go and the tape `T` read
from `c`: its status, the cursor where its result leaves the tape, and the words it changes. -/
theorem phase_ok {j w n c : Nat} {T : List Byte} (h : In Ex base bytes len args s)
    (G : TapeGeo Ex args base bytes (s.gpr .esp) T.length)
    (hT : Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) T.length = T) (hj9 : 9 ≤ j) (hj : j ≤ 10)
    (hw : sv s.mem base len .wide j = w) (hw3 : 3 ≤ w) (hodd : w % 2 = 1)
    (ho : w32 s.mem base octOff = Spec.Ffdh.witnessOctets w)
    (hk : w32 s.mem base kOff = Spec.RsaKeyGen.bitLength (w - 1))
    (hn : w32 s.mem base cntOff = n) (hn1 : 1 ≤ n) (hc : w32 s.mem base curOff = c) (hcT : c ≤ T.length) :
    WP isa (phase j) s fun u => Step Ex base bytes len args s u ∧
      u.gpr .eax = BitVec.ofNat 32 (drawStatus (ParameterCandidate.checkWitnesses w n (T.drop c))) ∧
      (∀ b r, ParameterCandidate.checkWitnesses w n (T.drop c) = some (b, r) →
        ∃ c', w32 u.mem base curOff = c' ∧ c' ≤ T.length ∧ T.drop c' = r) ∧
      Kept base len [11, 13, 14, 15] (twoOff :: drawDs) s.mem u.mem := by
  have hwl : w - 1 < 2 ^ (32 * cwc len .wide) := by
    have := val32_lt s.mem base (lo len (.slot .wide j)) (cwc len .wide)
    change sv s.mem base len .wide j < _ at this
    omega
  unfold phase
  refine WP.seq (WP.mono (prepPhase_ok h hj9 hj hw hw3 hodd) fun u₁ ⟨S₁, P₁, k₁⟩ => ?_)
  refine WP.seq (wp_movi fun u₂ U₂ => hdr_store (S₁.inp.regs U₂.keeps U₂.mem) hdr_st
    fun u₃ S₃ W₃ k₃ O₃ _ _ _ => WP.block_nil ?_)
  have S₂ : Step Ex base bytes len args u₁ u₂ := Step.regs S₁.inp U₂.mem U₂.keeps
  have S₀ : Step Ex base bytes len args s u₃ := S₁.trans (S₂.trans S₃)
  have k₀ : Kept base len [11, 14, 15] [twoOff, stOff] s.mem u₃.mem :=
    k₁.mono.trans ((by rw [U₂.mem]; exact (Kept.refl _).mono : Kept base len [11, 14, 15] [twoOff, stOff] u₁.mem u₂.mem).trans
      k₃.mono)
  have P₀ : Prepped Ex base bytes len args w u₃ :=
    P₁.keep ((P₁.toReady.regs U₂.keeps (by decide) (by decide) U₂.mem).hdr hdr_st S₃.keeps (by decide) (by decide) O₃)
      ((by rw [U₂.mem]; exact (Kept.refl _).mono : Kept base len [] [stOff] u₁.mem u₂.mem).trans k₃) (by decide)
  have G₀ : TapeGeo Ex args base bytes (u₃.gpr .esp) T.length := by rw [S₀.esp]; exact G
  have A₀ : DrawAt Ex base bytes len args u₃ w T n c u₃ := by
    refine ⟨⟨Step.regs S₀.inp rfl (rs := []) ⟨fun _ _ => rfl, rfl, rfl⟩, P₀, by rw [tape_keep G S₀, hT],
      (Kept.refl _).mono⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [k₀.word_eq, ho]
    · rw [k₀.word_eq, hk]
    · rw [k₀.word_eq, hc]
    · rw [k₀.word_eq, hn]
    · rw [W₃, U₂.gpr]; rfl
  refine WP.seq (WP.mono (WP.loop (M := isa) (Q := DrawEnd Ex base bytes len args u₃ w T
      (ParameterCandidate.checkWitnesses w n (T.drop c)))
    (fun m t => ∃ n' c', m = T.length - c' ∧ DrawAt Ex base bytes len args u₃ w T n' c' t ∧ 1 ≤ n' ∧
      c' ≤ T.length ∧ ParameterCandidate.checkWitnesses w n' (T.drop c') =
        ParameterCandidate.checkWitnesses w n (T.drop c)) ?_ (T.length - c) u₃ ⟨n, c, rfl, A₀, hn1, hcT, rfl⟩)
    fun u E => ?_)
  · rintro m t ⟨n', c', rfl, A, hn', hc', hD⟩
    refine WP.mono (draw_ok G₀ hw3 hodd hwl A hn' hc') fun u o => ?_
    rcases o with ⟨ev, n'', c'', A', h1, h2, h3, h4⟩ | ⟨ev, E⟩
    · exact .inr ⟨ev, T.length - c'', by omega, n'', c'', rfl, A', h1, h3, by rw [h4, hD]⟩
    · exact .inl ⟨ev, by rw [hD] at E; exact E⟩
  refine wp_movS (hdr_read E.step.inp hdr_st) fun v U _ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · exact S₀.trans (E.step.trans (Step.regs E.step.inp U.mem U.keeps))
  · rw [U.gpr, E.status]
  · intro b r e
    obtain ⟨c', hc', hl, hr⟩ := E.used b r e
    exact ⟨c', by rw [U.mem, hc'], hl, hr⟩
  · exact k₀.mono.trans (E.kept.mono.trans (by rw [U.mem]; exact (Kept.refl _).mono))

end VG.Proof.Ffdh.X86.Cand
