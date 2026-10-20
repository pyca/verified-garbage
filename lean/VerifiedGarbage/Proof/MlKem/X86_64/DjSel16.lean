module

public import VerifiedGarbage.Proof.MlKem.X86_64.DjFusedCT16
import VerifiedGarbage.Proof.MlKem.X86_64.EkSel16
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkSel16
public import VerifiedGarbage.Proof.MlKem.X86_64.Top16Ctl
public import VerifiedGarbage.Proof.MlKem.X86_64.Narrow

/-!
# ML-KEM on x86-64: decapsulation hashing `z ‖ c` in the matrix's fragments, for each implementation

An implementation `v` with a 16-bit sampler and a fragment sampling 16-bit
polynomials (`Callee4.s16`, `Callee4.batchH16`) runs the decapsulation with
16-bit polynomials that hashes `z ‖ c` in the fragments (`kemDecapsJ16`);
any other, the one with polynomials of `u32`s (`kemDecaps`). As
`EkSel16.lean`, whose `ek16_ctl` and `ek16_sp` give its control flow and
stack pointer.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

/-- Decapsulation hashing `z ‖ c` in the fragments, against the contract of
`K` with the first `n` bytes of `scratch`. -/
theorem decapsJ16_narrow {K : Kem16} {n : Nat} (hn : n ≤ K.L.scr) (hK : KpkeOk K.L) (v : Sample4Impl)
    (F16 : DjF16.DjHWf (narrowK K n)) (T16 : DjF16.DjTWf (narrowK K n)) {m : String} {c : Prog isa}
    (hs : v.callee.s16 = some (m, c)) {b : Prog isa} (hb : v.callee.batchH16 = some b)
    (hctl : ctlOk (kemDecapsJ16 K v.callee (m, c) b) = true) (hsat : ∃ s, (decapsK K.L).pre s) :
    Verified X86_64.target (kemDecapsJ16 K v.callee (m, c) b) (decapsK (narrowL K.L n)) :=
  Verified.of_correct (kemDecapsJ16_correct (K := narrowK K n) (hK.narrow n) v F16 hs hb hctl)
    (kemDecapsJ16_ct (K := narrowK K n) (hK.narrow n) v F16 T16 hs hb)
    (.refl (hsat.elim fun _ hs => ⟨_, decapsK_pre hn hs⟩))

theorem decapsSel_verified {K : Kem16} {n : Nat} (hn : n ≤ K.L.scr) (hK : KpkeOk K.L) (v : Sample4Impl)
    (F16 : DjF16.DjHWf (narrowK K n)) (T16 : DjF16.DjTWf (narrowK K n)) (W : Decaps.DcWf K.L) {wc wd : List Nat}
    (C : KemCalls K.L wc wd) {k : Contract isa} (hk : (decapsK K.L).Implies k)
    (hctl16 : ∀ n c b, S16Ok c → BatchHOk16 b → ctlOk (kemDecapsJ16 K v.callee (n, c) b) = true)
    (hctl : ctlOk (kemDecaps K.L v.callee) = true) :
    Verified X86_64.target (kemDecapsSel K v.callee) k := by
  unfold kemDecapsSel
  split
  · rename_i p b hs hb
    obtain ⟨m, c⟩ := p
    exact Verified.of_implies (decapsK_widen hn (decapsJ16_narrow hn hK v F16 T16 hs hb
      (hctl16 m c b (v.s16 m c hs) (v.batchH16 b hb)) hk.sat_left) hk.sat_left) hk
  · exact Verified.of_correct (kemDecaps_correct v W C hctl) (kemDecaps_ct v W C) hk

/-- Decapsulation hashing `z ‖ c` in the fragments leaves `scratch` from its
`n`-th byte on as it was. -/
theorem decapsSel_keep {K : Kem16} {n : Nat} (hn : n ≤ K.L.scr) (hK : KpkeOk K.L) (v : Sample4Impl)
    (F16 : DjF16.DjHWf (narrowK K n)) (T16 : DjF16.DjTWf (narrowK K n)) {m : String} {c : Prog isa}
    (hs : v.callee.s16 = some (m, c)) {b : Prog isa} (hb : v.callee.batchH16 = some b)
    (hctl : ctlOk (kemDecapsJ16 K v.callee (m, c) b) = true) (hsp : SpSafe (kemDecapsJ16 K v.callee (m, c) b))
    (hd : (kemDecapsJ16 K v.callee (m, c) b).x86_64Depth ≤ 32) {s : State} (hp : (decapsK K.L).pre s)
    {t : List Leak} {s' : State} (he : Exec isa (kemDecapsSel K v.callee) s t s') {i : Nat} (hi : n ≤ i)
    (hil : i < K.L.scr) : s'.mem (s.gpr .rcx + BitVec.ofNat 64 i) = s.mem (s.gpr .rcx + BitVec.ofNat 64 i) := by
  unfold kemDecapsSel at he
  rw [hs, hb] at he
  obtain ⟨-, hwr, -, -, -, -, d5, -, -, -, -, -, -, -, b4, -, -, -, o4⟩ := id hp
  refine verified_keepTail (decapsJ16_narrow hn hK v F16 T16 hs hb hctl ⟨s, hp⟩) hsp hd (decapsK_pre hn hp)
    (by rw [hwr]; exact prefix2 hn) he o4 (fun r hr => ?_) b4 hi hil
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inr d5
  · exact .inl rfl

/-- No instruction of `kemDecapsSel K c` writes the stack pointer, if neither
of the functions it may run does. -/
theorem decapsSel_sp {K : Kem16} (v : Sample4Impl) {p : Instr → Bool}
    (h16 : ∀ n c b, S16Ok c → BatchHOk16 b → (kemDecapsJ16 K v.callee (n, c) b).all p = true)
    (h : (kemDecaps K.L v.callee).all p = true) : (kemDecapsSel K v.callee).all p = true := by
  unfold kemDecapsSel
  split
  · rename_i q b hs hb
    obtain ⟨n, c⟩ := q
    exact h16 n c b (v.s16 n c hs) (v.batchH16 b hb)
  · exact h

end VG.Proof.MlKem.X86_64
