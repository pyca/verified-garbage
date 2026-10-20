module

import VerifiedGarbage.Proof.MlKem.X86_64.KgTop16
public import VerifiedGarbage.Proof.MlKem.X86_64.EcTop16
import VerifiedGarbage.Proof.MlKem.X86_64.DcTop16
import VerifiedGarbage.Proof.MlKem.X86_64.KgTop
import VerifiedGarbage.Proof.MlKem.X86_64.DcTop
public import VerifiedGarbage.Proof.MlKem.X86_64.Narrow
public import VerifiedGarbage.Proof.MlKem.X86_64.Dc16Dec

/-!
# ML-KEM on x86-64: the top-level functions of each implementation

An implementation `v` with a 16-bit sampler (`Callee4.s16`) runs the
top-level functions with 16-bit polynomials (`kemKeyGenSel`, …); the
baseline, those with polynomials of `u32`s. Each is `Verified` by the proof
of the one it runs, against any contract the K-PKE functions' parameter
set's implies. The ones with 16-bit polynomials are proven for the layout
with only the first `n` bytes of `scratch` (`narrowK`), and leave the rest
of it as it was (`keyGenSel_keep`, …).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

/-- Key generation with 16-bit polynomials, against the contract of `K` with
the first `n` bytes of `scratch`. -/
theorem keyGen16_narrow {K : Kem16} {n : Nat} (hn : n ≤ K.L.scr) (hK : KpkeOk K.L) (v : Sample4Impl)
    (W16 : KeyGen16.Kg16Wf (narrowK K n)) {m : String} {c : Prog isa} (hs : v.callee.s16 = some (m, c))
    (hctl : ctlOk (kemKeyGen16 K v.callee (m, c)) = true) (hsat : ∃ s, (keyGenK K.L).pre s) :
    Verified X86_64.target (kemKeyGen16 K v.callee (m, c)) (keyGenK (narrowL K.L n)) :=
  Verified.of_correct (kemKeyGen16_correct (K := narrowK K n) (hK.narrow n) v W16 hs hctl)
    (kemKeyGen16_ct (K := narrowK K n) (hK.narrow n) v W16 hs)
    (.refl (hsat.elim fun _ hs => ⟨_, keyGenK_pre hn hs⟩))

theorem keyGenSel_verified {K : Kem16} {n : Nat} (hn : n ≤ K.L.scr) (hK : KpkeOk K.L) (v : Sample4Impl)
    (W16 : KeyGen16.Kg16Wf (narrowK K n)) (W : KeyGen.KgWf K.L) {k : Contract isa}
    (hk : (keyGenK K.L).Implies k)
    (hctl16 : ∀ n c, S16Ok c → ctlOk (kemKeyGen16 K v.callee (n, c)) = true)
    (hctl : ctlOk (kemKeyGen K.L v.callee) = true) :
    Verified X86_64.target (kemKeyGenSel K v.callee) k := by
  unfold kemKeyGenSel
  match hs : v.callee.s16 with
  | some (m, c) =>
    exact Verified.of_implies (keyGenK_widen hn
      (keyGen16_narrow hn hK v W16 hs (hctl16 m c (v.s16 m c hs)) hk.sat_left) hk.sat_left) hk
  | none => exact Verified.of_correct (kemKeyGen_correct v W hctl) (kemKeyGen_ct v W) hk

/-- Key generation with 16-bit polynomials leaves `scratch` from its `n`-th
byte on as it was. -/
theorem keyGenSel_keep {K : Kem16} {n : Nat} (hn : n ≤ K.L.scr) (hK : KpkeOk K.L) (v : Sample4Impl)
    (W16 : KeyGen16.Kg16Wf (narrowK K n)) {m : String} {c : Prog isa} (hs : v.callee.s16 = some (m, c))
    (hctl : ctlOk (kemKeyGen16 K v.callee (m, c)) = true) (hsp : SpSafe (kemKeyGen16 K v.callee (m, c)))
    (hd : (kemKeyGen16 K v.callee (m, c)).x86_64Depth ≤ 32) {s : State} (hp : (keyGenK K.L).pre s)
    {t : List Leak} {s' : State} (he : Exec isa (kemKeyGenSel K v.callee) s t s') {i : Nat} (hi : n ≤ i)
    (hil : i < K.L.scr) : s'.mem (s.gpr .rcx + BitVec.ofNat 64 i) = s.mem (s.gpr .rcx + BitVec.ofNat 64 i) := by
  unfold kemKeyGenSel at he
  rw [hs] at he
  obtain ⟨-, hwr, -, -, -, -, d5, d6, -, -, -, -, -, -, -, b4, -, -, -, o4⟩ := id hp
  refine verified_keepTail (keyGen16_narrow hn hK v W16 hs hctl ⟨s, hp⟩) hsp hd (keyGenK_pre hn hp)
    (by rw [hwr]; exact prefix3 hn) he o4 (fun r hr => ?_) b4 hi hil
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inr d5
  · exact .inr d6
  · exact .inl rfl

/-- Encapsulation with 16-bit polynomials, against the contract of `K` with
the first `n` bytes of `scratch`. -/
theorem encapsH16_narrow {K : Kem16} {n : Nat} (hn : n ≤ K.L.scr) (hK : KpkeOk K.L) (v : Sample4Impl)
    (W16 : Encaps16.Ec16Wf (narrowK K n)) {m : String} {c : Prog isa} (hs : v.callee.s16 = some (m, c))
    (hctl : ctlOk (kemEncapsH16 K v.callee (m, c)) = true) (hsat : ∃ s, (encapsK K.L).pre s) :
    Verified X86_64.target (kemEncapsH16 K v.callee (m, c)) (encapsK (narrowL K.L n)) :=
  Verified.of_correct (kemEncapsH16_correct (K := narrowK K n) (hK.narrow n) v W16 hs hctl)
    (kemEncapsH16_ct (K := narrowK K n) (hK.narrow n) v W16 hs)
    (.refl (hsat.elim fun _ hs => ⟨_, encapsK_pre hn hs⟩))

theorem encapsHSel_verified {K : Kem16} {n : Nat} (hn : n ≤ K.L.scr) (hK : KpkeOk K.L) (v : Sample4Impl)
    (W16 : Encaps16.Ec16Wf (narrowK K n)) (W : Encaps.EcWf K.L) {wc wd : List Nat} (C : KemCalls K.L wc wd)
    {k : Contract isa} (hk : (encapsK K.L).Implies k)
    (hctl16 : ∀ n c, S16Ok c → ctlOk (kemEncapsH16 K v.callee (n, c)) = true)
    (hctl : ctlOk (kemEncapsH K.L v.callee) = true) :
    Verified X86_64.target (kemEncapsHSel K v.callee) k := by
  unfold kemEncapsHSel
  match hs : v.callee.s16 with
  | some (m, c) =>
    exact Verified.of_implies (encapsK_widen hn
      (encapsH16_narrow hn hK v W16 hs (hctl16 m c (v.s16 m c hs)) hk.sat_left) hk.sat_left) hk
  | none => exact Verified.of_correct (kemEncapsH_correct v W C hctl) (kemEncapsH_ct v W C) hk

/-- Encapsulation with 16-bit polynomials leaves `scratch` from its `n`-th
byte on as it was. -/
theorem encapsHSel_keep {K : Kem16} {n : Nat} (hn : n ≤ K.L.scr) (hK : KpkeOk K.L) (v : Sample4Impl)
    (W16 : Encaps16.Ec16Wf (narrowK K n)) {m : String} {c : Prog isa} (hs : v.callee.s16 = some (m, c))
    (hctl : ctlOk (kemEncapsH16 K v.callee (m, c)) = true) (hsp : SpSafe (kemEncapsH16 K v.callee (m, c)))
    (hd : (kemEncapsH16 K v.callee (m, c)).x86_64Depth ≤ 32) {s : State} (hp : (encapsK K.L).pre s)
    {t : List Leak} {s' : State} (he : Exec isa (kemEncapsHSel K v.callee) s t s') {i : Nat} (hi : n ≤ i)
    (hil : i < K.L.scr) : s'.mem (s.gpr .r9 + BitVec.ofNat 64 i) = s.mem (s.gpr .r9 + BitVec.ofNat 64 i) := by
  unfold kemEncapsHSel at he
  rw [hs] at he
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, -, -, d11, d12, -, -, -, -, -, -, -, -, -, -, -, b6, -, -, -, -, -, o6, -⟩ := id hp
  refine verified_keepTail (encapsH16_narrow hn hK v W16 hs hctl ⟨s, hp⟩) hsp hd (encapsK_pre hn hp)
    (by rw [hwr]; exact prefix3 hn) he o6 (fun r hr => ?_) b6 hi hil
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inr d11
  · exact .inr d12
  · exact .inl rfl

/-- No instruction of the top-level function `kemKeyGenSel K c` writes the
stack pointer, if neither of the functions it may run does. -/
theorem keyGenSel_sp {K : Kem16} (v : Sample4Impl) {p : Instr → Bool}
    (h16 : ∀ n c, S16Ok c → (kemKeyGen16 K v.callee (n, c)).all p = true)
    (h : (kemKeyGen K.L v.callee).all p = true) : (kemKeyGenSel K v.callee).all p = true := by
  unfold kemKeyGenSel
  match hs : v.callee.s16 with
  | some (n, c) => exact h16 n c (v.s16 n c hs)
  | none => exact h

theorem encapsHSel_sp {K : Kem16} (v : Sample4Impl) {p : Instr → Bool}
    (h16 : ∀ n c, S16Ok c → (kemEncapsH16 K v.callee (n, c)).all p = true)
    (h : (kemEncapsH K.L v.callee).all p = true) : (kemEncapsHSel K v.callee).all p = true := by
  unfold kemEncapsHSel
  match hs : v.callee.s16 with
  | some (n, c) => exact h16 n c (v.s16 n c hs)
  | none => exact h

end VG.Proof.MlKem.X86_64
