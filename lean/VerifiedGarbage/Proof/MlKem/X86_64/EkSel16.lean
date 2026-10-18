module

public import VerifiedGarbage.Proof.MlKem.X86_64.EkTop
public import VerifiedGarbage.Proof.MlKem.X86_64.EkFused16
public import VerifiedGarbage.Proof.MlKem.X86_64.EkFusedCT16
public import VerifiedGarbage.Proof.MlKem.X86_64.Top16Ctl
public meta import VerifiedGarbage.Proof.MlKem.X86_64.Top16Ctl

/-!
# ML-KEM on x86-64: encapsulation hashing the key, for each implementation

An implementation `v` with a 16-bit sampler and a fragment sampling 16-bit
polynomials (`Callee4.s16`, `Callee4.batchH16`) runs the encapsulation with
16-bit polynomials (`kemEncaps16`); any other, the one with polynomials of
`u32`s (`kemEncaps`). As `Sel16.lean`, with `ek16_ctl` and `ek16_sp` for
the control flow and the stack pointer of `kemEncaps16`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

/-- `ctlOk` of code that calls the 16-bit sampler `c` of the implementation
`v` (`S : S16Ok c`) and the K-PKE functions (`hK`), and inlines the fragment
`b` (`B : BatchHOk16 b`). -/
tactic_template "ek16_ctl " v:ident c:ident b:ident S:ident B:ident hK:ident : tactic =>
  `(tactic| repeat' (first
    | with_reducible exact ($B).ctl | (closed_in $b; s16_ctl $v $c $S $hK; done)
    | (code_whnf; with_reducible apply ctlOk_seq) | (code_whnf; with_reducible apply ctlOk_ite) | rfl))

/-- That code that calls the 16-bit sampler `c` of the implementation `v` and
the K-PKE functions, and inlines the fragment `b`, never writes the stack pointer. -/
tactic_template "ek16_sp " v:ident c:ident b:ident S:ident B:ident hK:ident : tactic =>
  `(tactic| repeat' (first
    | with_reducible exact ($B).sp | (closed_in $b; s16_sp $v $c $S $hK; done)
    | (code_whnf; with_reducible apply all_seq) | (code_whnf; with_reducible apply all_ite) | rfl))

theorem encapsSel_verified {K : Kem16} (hK : KpkeOk K.L) (v : Sample4Impl) (F16 : EkF16.Ek16HWf K)
    (T16 : EkF16.EkT16Wf K) (W : Ek.EkWf K.L) (F : EkF.EkHWf K.L) (T : EkF.EkTWf K.L) {wc wd : List Nat}
    (C : KemCalls K.L wc wd) {k : Contract isa} (hk : (encK K.L).Implies k)
    (hctl16 : ∀ n c b, S16Ok c → BatchHOk16 b → ctlOk (kemEncaps16 K v.callee (n, c) b) = true)
    (hctl : ctlOk (kemEncaps K.L v.callee) = true) :
    Verified X86_64.target (kemEncapsSel K v.callee) k := by
  unfold kemEncapsSel
  split
  · rename_i p b hs hb
    obtain ⟨n, c⟩ := p
    exact Verified.of_correct
      (kemEncaps16_correct hK v F16 hs hb (hctl16 n c b (v.s16 n c hs) (v.batchH16 b hb)))
      (kemEncaps16_ct hK v F16 T16 hs hb) hk
  · exact Verified.of_correct (kemEncaps_correct v W F C hctl) (kemEncaps_ct v W F T C) hk

/-- No instruction of `kemEncapsSel K c` writes the stack pointer, if neither
of the functions it may run does. -/
theorem encapsSel_sp {K : Kem16} (v : Sample4Impl) {p : Instr → Bool}
    (h16 : ∀ n c b, S16Ok c → BatchHOk16 b → (kemEncaps16 K v.callee (n, c) b).all p = true)
    (h : (kemEncaps K.L v.callee).all p = true) : (kemEncapsSel K v.callee).all p = true := by
  unfold kemEncapsSel
  split
  · rename_i q b hs hb
    obtain ⟨n, c⟩ := q
    exact h16 n c b (v.s16 n c hs) (v.batchH16 b hb)
  · exact h

end VG.Proof.MlKem.X86_64
