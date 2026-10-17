module

public import VerifiedGarbage.Proof.MlKem.X86_64.EkFusedCT
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkFusedCT

/-!
# ML-KEM on x86-64: encapsulation hashing the key

`kemEncaps L v.callee` for any implementation `v` of `vg_mlkem_sample_ntt4`:
with the sponge functions when `v` has no fragment (`EkScalar.lean`), and in
the matrix's fragments when it has one (`EkFused.lean`, `EkFusedCT.lean`); its
control flow and its stack pointer, for each parameter set, by `s4_ctl` and
`s4_sp` without a fragment and `ek_ctl` and `ek_sp` with one.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

theorem kemEncaps_correct (v : Sample4Impl) {L : Kem} (W : Ek.EkWf L) (F : EkF.EkHWf L) {wc wd : List Nat}
    (K : KemCalls L wc wd) (hctl : ctlOk (kemEncaps L v.callee) = true) (σ : State) (hp : (encK L).pre σ) :
    ∃ t s', Exec isa (kemEncaps L v.callee) σ t s' ∧ abiPreserved σ s' ∧ (encK L).post σ s' := by
  rcases hb : v.callee.batchH with _ | b
  · exact kemEncapsS_correct v W K hb hctl σ hp
  · exact kemEncapsF_correct v F K hb hctl σ hp

theorem kemEncaps_ct (v : Sample4Impl) {L : Kem} (W : Ek.EkWf L) (F : EkF.EkHWf L) (T : EkF.EkTWf L)
    {wc wd : List Nat} (K : KemCalls L wc wd) :
    ConstantTime isa (encK L).pre (encK L).pub (kemEncaps L v.callee) := by
  rcases hb : v.callee.batchH with _ | b
  · exact kemEncapsS_ct v W K hb
  · exact kemEncapsF_ct v F T K hb

/-- A state satisfying the precondition of `vg_mlkem*_encaps` for keys of
`ekLen` bytes, ciphertexts of `ctLen` bytes and `scr` bytes of working space. -/
def encapsSat (ekLen ctLen scr : Nat) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000 | .r8 => 0x10000
    | .rsp => 0x80000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, ekLen⟩, ⟨0x2000, 32⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, ctLen⟩, ⟨0x10000, scr⟩]

/-- `ctlOk` of code that calls the implementation `v` and inlines its fragment `b`
(`hB : BatchHOk b`). -/
tactic_template "ek_ctl " v:ident b:ident hB:ident : tactic =>
  `(tactic| repeat' (first
    | (closed_in $b; s4_ctl $v; done) | apply ctlOk_seq | apply ctlOk_ite | with_reducible exact ($hB).ctl | rfl))

/-- That code that calls the implementation `v` and inlines its fragment `b` never writes the stack pointer. -/
tactic_template "ek_sp " v:ident b:ident hB:ident : tactic =>
  `(tactic| repeat' (first
    | (closed_in $b; s4_sp $v; done) | apply all_seq | apply all_ite | with_reducible exact ($hB).sp | rfl))

end VG.Proof.MlKem.X86_64
