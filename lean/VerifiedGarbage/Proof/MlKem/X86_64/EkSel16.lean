module

public import VerifiedGarbage.Proof.MlKem.X86_64.EkTop
public import VerifiedGarbage.Proof.MlKem.X86_64.EkFused16
public import VerifiedGarbage.Proof.MlKem.X86_64.EkFusedCT16
public import VerifiedGarbage.Proof.MlKem.X86_64.Narrow
public import VerifiedGarbage.Proof.MlKem.X86_64.Top16Ctl
public meta import VerifiedGarbage.Proof.MlKem.X86_64.Top16Ctl

/-!
# ML-KEM on x86-64: encapsulation hashing the key, for each implementation

An implementation `v` with a 16-bit sampler and a fragment sampling 16-bit
polynomials (`Callee4.s16`, `Callee4.batchH16`) runs the encapsulation with
16-bit polynomials (`kemEncaps16`); any other, the one with polynomials of
`u32`s (`kemEncaps`). As `Sel16.lean`, with `ek16_ctl` and `ek16_sp` for
the control flow and the stack pointer of `kemEncaps16`, which is proven
for the layout with only the first `n` bytes of `scratch` and leaves the
rest of it as it was (`encapsSel_keep`).
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

/-- Encapsulation with 16-bit polynomials, against the contract of `K` with
the first `n` bytes of `scratch`. -/
theorem xdLe_batch {k : Nat} {b : Prog isa} (B : BatchHOk16 b) : xdLe k b = true :=
  xdLe_of_le (by rw [B.xd]; exact Nat.zero_le _)

/-- That the calls of code that calls the 16-bit sampler `c` of the
implementation `v` and the K-PKE functions, and inlines the fragment `b`, use
at most `k` bytes of stack (a goal `xdLe k _ = true`). -/
tactic_template "ek16_xd " v:ident c:ident b:ident S:ident B:ident hK:ident : tactic =>
  `(tactic| repeat' (first
    | with_reducible exact xdLe_batch $B | (closed_in $b; s16_xd $v $c $S $hK; done)
    | (code_whnf; with_reducible apply xdLe_seq) | (code_whnf; with_reducible apply xdLe_ite) | rfl))

theorem encaps16_narrow {K : Kem16} {n : Nat} (hn : n ≤ K.L.scr) (hK : KpkeOk K.L) (v : Sample4Impl)
    (F16 : EkF16.Ek16HWf (narrowK K n)) (T16 : EkF16.EkT16Wf (narrowK K n)) {m : String} {c : Prog isa}
    (hs : v.callee.s16 = some (m, c)) {b : Prog isa} (hb : v.callee.batchH16 = some b)
    (hctl : ctlOk (kemEncaps16 K v.callee (m, c) b) = true) (hsat : ∃ s, (encK K.L).pre s) :
    Verified X86_64.target (kemEncaps16 K v.callee (m, c) b) (encK (narrowL K.L n)) :=
  Verified.of_correct (kemEncaps16_correct (K := narrowK K n) (hK.narrow n) v F16 hs hb hctl)
    (kemEncaps16_ct (K := narrowK K n) (hK.narrow n) v F16 T16 hs hb)
    (.refl (hsat.elim fun _ hs => ⟨_, encK_pre hn hs⟩))

theorem encapsSel_verified {K : Kem16} {n : Nat} (hn : n ≤ K.L.scr) (hK : KpkeOk K.L) (v : Sample4Impl)
    (F16 : EkF16.Ek16HWf (narrowK K n)) (T16 : EkF16.EkT16Wf (narrowK K n)) (W : Ek.EkWf K.L)
    {wc wd : List Nat} (C : KemCalls K.L wc wd) {k : Contract isa} (hk : (encK K.L).Implies k)
    (hctl16 : ∀ n c b, S16Ok c → BatchHOk16 b → ctlOk (kemEncaps16 K v.callee (n, c) b) = true)
    (hctl : ctlOk (kemEncaps K.L v.callee) = true) :
    Verified X86_64.target (kemEncapsSel K v.callee) k := by
  unfold kemEncapsSel
  split
  · rename_i p b hs hb
    obtain ⟨m, c⟩ := p
    exact Verified.of_implies (encK_widen hn (encaps16_narrow hn hK v F16 T16 hs hb
      (hctl16 m c b (v.s16 m c hs) (v.batchH16 b hb)) hk.sat_left) hk.sat_left) hk
  · exact Verified.of_correct (kemEncaps_correct v W C hctl) (kemEncaps_ct v W C) hk

/-- Encapsulation with 16-bit polynomials leaves `scratch` from its `n`-th
byte on as it was. -/
theorem encapsSel_keep {K : Kem16} {n : Nat} (hn : n ≤ K.L.scr) (hK : KpkeOk K.L) (v : Sample4Impl)
    (F16 : EkF16.Ek16HWf (narrowK K n)) (T16 : EkF16.EkT16Wf (narrowK K n)) {m : String} {c : Prog isa}
    (hs : v.callee.s16 = some (m, c)) {b : Prog isa} (hb : v.callee.batchH16 = some b)
    (hctl : ctlOk (kemEncaps16 K v.callee (m, c) b) = true) (hsp : SpSafe (kemEncaps16 K v.callee (m, c) b))
    (hd : (kemEncaps16 K v.callee (m, c) b).x86_64Depth ≤ 32) {s : State} (hp : (encK K.L).pre s)
    {t : List Leak} {s' : State} (he : Exec isa (kemEncapsSel K v.callee) s t s') {i : Nat} (hi : n ≤ i)
    (hil : i < K.L.scr) : s'.mem (s.gpr .r8 + BitVec.ofNat 64 i) = s.mem (s.gpr .r8 + BitVec.ofNat 64 i) := by
  unfold kemEncapsSel at he
  rw [hs, hb] at he
  obtain ⟨-, hwr, -, -, -, -, -, -, -, d8, d9, -, -, -, -, -, -, -, -, -, b5, -, -, -, -, o5⟩ := id hp
  refine verified_keepTail (encaps16_narrow hn hK v F16 T16 hs hb hctl ⟨s, hp⟩) hsp hd (encK_pre hn hp)
    (by rw [hwr]; exact prefix3 hn) he o5 (fun r hr => ?_) b5 hi hil
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inr d8
  · exact .inr d9
  · exact .inl rfl

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
