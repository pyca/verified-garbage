module

import VerifiedGarbage.Proof.MlKem.X86_64.KgTop16
public import VerifiedGarbage.Proof.MlKem.X86_64.Narrow
public import VerifiedGarbage.Proof.MlKem.X86_64.Kg16
public import VerifiedGarbage.Proof.MlKem.X86_64.EcTop
public import VerifiedGarbage.Proof.MlKem.X86_64.Enc16
import VerifiedGarbage.Proof.MlKem.X86_64.EncTop

/-! ### `MlKem.X86_64.EcTop16`, which this module and modules that import it used -/

section

/-!
# ML-KEM on x86-64: encapsulation with `H(ek)` given, with 16-bit polynomials

As with polynomials of `u32`s (`EcTop.lean`), but for K-PKE.Encrypt with
16-bit polynomials (`Enc16.lean`), which writes the ciphertext straight to
`ct`, so that the outputs are only `K` copied to `key`
(`kemEncapsH16_correct`, `kemEncapsH16_ct`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Encaps16

open Encaps VG.Impl.MlKem.X86_64.EncapsH

variable (K : Kem16)

/-- What encapsulation with 16-bit polynomials needs of the layout, evaluated for each parameter set. -/
structure Ec16Wf : Prop extends EcWfB K.L where
  enc : Enc16.EncChks K (ecB K.L) (ecW K.L) (eckChk K.L) (.r14, 0)
  tl : Enc16.tailChk K (ecB K.L) (ecW K.L) (eckChk K.L) (.r14, 0) (.r13, 0) = true
  o₁T : keepB (ecB K.L) [((.r12, 0), 32)] (.r13, 0) K.L.ctLen = true

variable {K}

/-- The end of `K-PKE.Encrypt`. -/
abbrev EncO16 (W : Ec16Wf K) (σ s : State) : Prop :=
  Enc16.EOut16 K (ecC W.toEcWfB σ) (.r13, 0) (ecEk K.L σ) (ecMs σ) (ecG K.L σ).2 s

theorem out_ok (W : Ec16Wf K) {σ : State} {s : State} (h : EncO16 W σ s) :
    WP isa (copy (.r12, 0) (sc oG) 32) s (ECEnd K.L σ) := by
  have hp := h.out.1
  have L₀ := h.out.2.ec.lay W.toEcWfB hp
  refine WP.mono (copy_okL L₀ (dst := (.r12, 0)) (src := sc oG) (n := 32) (by decide) W.o₁) fun s₁ ⟨hP₁, hb₁⟩ => ?_
  refine ⟨h.out.2.ec.step W.toEcWfB hp hP₁.b W.o₁K, by rw [hP₁.cs .r15 (by decide)]; exact h.r15, ?_, fun ho => ?_⟩
  · rw [hP₁.pa (by decide), hb₁]; exact h.out.2.k
  · rw [L₀.keepBytes hP₁.b W.o₁T]; exact h.ct ho

end Encaps16

open Encaps Encaps16 in
theorem kemEncapsH16_correct {K : Kem16} (hK : KpkeOk K.L) (v : Sample4Impl) (W : Ec16Wf K) {n : String}
    {c : Prog isa} (hs : v.callee.s16 = some (n, c)) (hctl : ctlOk (kemEncapsH16 K v.callee (n, c)) = true)
    (σ : State) (hp : (encapsK K.L).pre σ) :
    ∃ t s', Exec isa (kemEncapsH16 K v.callee (n, c)) σ t s' ∧ abiPreserved σ s' ∧ (encapsK K.L).post σ s' := by
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok W.toEcWfB hp) fun s₁ h₁ =>
    WP.seq (WP.mono (hCopy_ok W.toEcWfB hp h₁) fun s₂ ⟨h₂, hH, h15⟩ =>
      WP.seq (WP.mono (hashes_ok W.toEcWfB hp h₂ hH h15) fun s₃ h₃ =>
        WP.seq (WP.mono (Enc16.encrypt_ok hK v hs (C := ecC W.toEcWfB σ) (show Reg.r14 ∉ argRegs by decide)
            (by decide) W.k.2 W.enc W.tl h₃.1 h₃.2) fun s₄ h₄ =>
          WP.seq (WP.mono (out_ok W h₄) fun s₅ h₅ =>
            WP.mono (topEpi_ok h₅.ec.top (h₅.hin W.toEcWfB hp)) fun s₆ ⟨hr, hg, hm⟩ =>
              (⟨hg, post_of W.toEcWfB h₅ hr hm⟩ : gprPreserved σ s₆ ∧ (encapsK K.L).post σ s₆))))))
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hF.1, hF.2⟩

namespace Encaps16

open Encaps VG.Impl.MlKem.X86_64.EncapsH

variable {K : Kem16}

theorem encrypt_tr (hK : KpkeOk K.L) (v : Sample4Impl) (W : Ec16Wf K) {n : String} {c : Prog isa}
    (hs : v.callee.s16 = some (n, c)) :
    RelCT isa (R K.L (EncI W.toEcWfB)) (Top16.encrypt K v.callee (n, c) (.r14, 0) (.r13, 0)) fun _ _ => True := by
  obtain ⟨_, rhoT⟩ := W.rhoT
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => LRel (ecR K.L) (ecW K.L) x y ∧
      Enc.EIρ K.L (ecCA W.toEcWfB) (.r14, 0) ρ x ∧ Enc.EIρ K.L (ecCA W.toEcWfB) (.r14, 0) ρ y) (Q := fun _ _ => True)
      fun ρ => RelCT.mono (Enc16.encrypt_tr hK v hs (C := ecCA W.toEcWfB) (show Reg.r14 ∉ argRegs by decide)
        (by decide) W.k.2 W.enc W.tl W.ijT rhoT (ρ := ρ)) (fun _ _ h => h) fun _ _ _ => trivial) ?_
    fun _ _ _ => trivial
  rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
  have i₁ : Enc.EIρ K.L (ecCA W.toEcWfB) (.r14, 0) (Enc.rhoE K.L (ecEk K.L σ₁)) x :=
    ⟨_, _, _, rfl, EIn.any h₁.1, h₁.2⟩
  have i₂ : Enc.EIρ K.L (ecCA W.toEcWfB) (.r14, 0) (Enc.rhoE K.L (ecEk K.L σ₁)) y :=
    ⟨_, _, _, (rho_pub pub).symm, EIn.any h₂.1, h₂.2⟩
  exact ⟨Enc.rhoE K.L (ecEk K.L σ₁), ec_lrel W.toEcWfB p₁ p₂ pub h₁.1.out.2.ec h₂.1.out.2.ec, i₁, i₂⟩

theorem out_tr (W : Ec16Wf K) : RelCT isa (R K.L (EncO16 W)) (copy (.r12, 0) (sc oG) 32) fun _ _ => True := by
  obtain ⟨_, oT₁⟩ := W.oT₁
  exact rel2_of (trL W.toEcWfB oT₁) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    ec_lrel W.toEcWfB p₁ p₂ pub h₁.out.2.ec h₂.out.2.ec

end Encaps16

open Encaps Encaps16 in
theorem kemEncapsH16_ct {K : Kem16} (hK : KpkeOk K.L) (v : Sample4Impl) (W : Ec16Wf K) {n : String}
    {c : Prog isa} (hs : v.callee.s16 = some (n, c)) :
    ConstantTime isa (encapsK K.L).pre (encapsK K.L).pub (kemEncapsH16 K v.callee (n, c)) := by
  refine relStart (Q := fun _ _ => True) ?_
  unfold kemEncapsH16
  refine RelCT.seq (relInv (I' := ProOut K.L) (fun σ s hp hs => by subst hs; exact pro_ok W.toEcWfB hp) pro_tr) ?_
  refine RelCT.seq (relInv (I' := fun σ s => EC K.L σ s ∧ bytesAt s.mem (pa s (sc oH)) 32 = H (ecEk K.L σ) ∧
    s.gpr .r15 = 1) (fun σ s hp hs => hCopy_ok W.toEcWfB hp hs) hCopy_tr) ?_
  refine RelCT.seq (relInv (I' := EncI W.toEcWfB) (fun σ s hp hs => hashes_ok W.toEcWfB hp hs.1 hs.2.1 hs.2.2)
    (hashes_tr W.toEcWfB)) ?_
  refine RelCT.seq (relInv (I' := EncO16 W) (fun σ s _ hi =>
      Enc16.encrypt_ok hK v hs (C := ecC W.toEcWfB σ) (show Reg.r14 ∉ argRegs by decide) (by decide) W.k.2 W.enc W.tl
        hi.1 hi.2) (encrypt_tr hK v W hs)) ?_
  refine RelCT.seq (relInv (I' := ECEnd K.L) (fun σ s _ hi => out_ok W hi) (out_tr W)) ?_
  exact RelCT.mono epi_tr (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.MlKem.X86_64

end

end

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
