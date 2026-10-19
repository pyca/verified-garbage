module

public import VerifiedGarbage.Proof.MlKem.X86_64.EkFused16
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkFused16
public import VerifiedGarbage.Proof.MlKem.X86_64.EkFrag
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkFrag
import all Init.Data.Nat.Bitwise.Basic
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
meta import Mathlib.Tactic.Conv
meta import VerifiedGarbage.Proof.MlKem.X86_64.YLanes

/-!
# ML-KEM on x86-64: encapsulation hashing the key in the matrix's fragments, with 16-bit polynomials, constant time

As `EkFusedCT.lean`, for `kemEncaps16` (`kemEncaps16_ct`): two runs whose
pointers and `ρ` agree leak the same, the fragments' blocks of `pad(ek)` and
the sponge's state, which only the fourth Keccak state absorbs, at fixed
addresses, and K-PKE.Encrypt with 16-bit polynomials for the same `ρ`
(`Enc16.rest_tr`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace EkF16

open VG.Proof.MlKem.X86_64.Encaps (ecR ecW ecB ecB_bases EcWfB trL)
open VG.Proof.MlKem.X86_64.Ek (EK ekE ekMs ekG ProOut R ek_lrel rho_pub)
open VG.Proof.MlKem.X86_64.EkF (relFalse)
open VG.Impl.MlKem.X86_64.Encaps (nb)
open VG.Impl.MlKem.X86_64.Encaps16 (oHS oHB hzero matH hblk frag)

variable (K : Kem16)

/-- The taint checks of the pieces the fused encapsulation adds, from the pointers. -/
structure EkT16Wf : Prop where
  rT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14])
    (copy (sc oSB) (.r14, 384 * K.L.k) 32) h).isSome = true
  zT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14]) (.block (hzero K)) h).isSome = true
  hT : ∀ i < nb K.L, ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14]) (hblk K i) h).isSome = true
  hcT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14])
    (copy (sc oH) (sc (oHS K)) 32) h).isSome = true
  ij : ∀ i < nb K.L, ∀ J < 4, (3 * i + J) / K.L.k < 4 ∧ (3 * i + J) % K.L.k < 4

variable {K}

section
variable (F : Ek16HWf K) (T : EkT16Wf K)
include F T

theorem rho16_tr : RelCT isa (R K.L (ProOut K.L)) (copy (sc oSB) (.r14, 384 * K.L.k) 32) fun _ _ => True := by
  obtain ⟨_, t⟩ := T.rT
  exact rel2_of (trL F.toEcWfB t) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ek_lrel F.toEcWfB p₁ p₂ pub h₁.ec h₂.ec

theorem hz16_tr : RelCT isa (R K.L (RI16 K)) (.block (hzero K)) fun _ _ => True := by
  obtain ⟨_, t⟩ := T.zT
  exact rel2_of (trL F.toEcWfB t) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ek_lrel F.toEcWfB p₁ p₂ pub h₁.ec h₂.ec

theorem hcopy16_tr : RelCT isa (R K.L fun σ s => FI16 K σ (nb K.L) s) (copy (sc oH) (sc (oHS K)) 32) fun _ _ => True := by
  obtain ⟨_, t⟩ := T.hcT
  exact rel2_of (trL F.toEcWfB t) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ek_lrel F.toEcWfB p₁ p₂ pub h₁.ec h₂.ec

end

/-- Before fragment `i`, for the `ρ` of `ek`. -/
abbrev FIρ16 (K : Kem16) (ρ : List Byte) (i : Nat) (s : State) : Prop :=
  ∃ σ, (encK K.L).pre σ ∧ FI16 K σ i s ∧ Enc.rhoE K.L (ekE K.L σ) = ρ

theorem frag16_tr (F : Ek16HWf K) (T : EkT16Wf K) {b : Prog isa} (hB : BatchHOk16 b) {i : Nat} (hi : i < nb K.L) :
    RelCT isa (R K.L fun σ s => FI16 K σ i s) (frag K b i) fun _ _ => True := by
  have W := F.toEcWfB
  obtain ⟨_, t⟩ := T.hT i hi
  have hsd := F.sd i hi
  simp only [sdChk, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hsd
  have hsm := F.sm i hi
  simp only [smChk, Bool.and_eq_true] at hsm
  have hc := F.hb i hi
  simp only [hbChk, Bool.and_eq_true] at hc
  have h16 : K.L.k * K.L.k ≤ 16 := Nat.mul_le_mul W.k.2 W.k.2
  have hnb := F.nbK
  have c4 := hsm.1
  have hin : inB (ecB K.L) (sc 0) 136 = true := by
    simp only [s4_16Chk, rdOk, Bool.and_eq_true] at c4; exact c4.1.1.1.1.1.2
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => LRel (ecR K.L) (ecW K.L) x y ∧ FIρ16 K ρ i x ∧ FIρ16 K ρ i y)
    (Q := fun _ _ => True) fun ρ => ?_) ?_ fun _ _ _ => trivial
  · unfold frag
    have hok : ∀ x, FIρ16 K ρ i x → WP isa (hblk K i) x fun x' =>
        PPostB x x' [(sc (oHB K), 408)] ∧ SeedsIs ρ K.L.k (3 * i) 0 x' := fun x ⟨σ, hp, h, e⟩ =>
      WP.mono (hblk16_ok F.toEk16FWf hp hi h) fun x' ⟨hP, h15, _⟩ =>
        ⟨hP, ⟨by rw [(h.keep W hp hP h15 hc.2).sb, e], fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩
    refine RelCT.seq (RelCT.postDep (RelCT.mono (trL W t) (fun _ _ h => h.1) fun _ _ h => h)
      (F := fun x x' => PPostB x x' [(sc (oHB K), 408)] ∧ SeedsIs ρ K.L.k (3 * i) 0 x')
      (Q := RQ (ecR K.L) (ecW K.L) ρ K.L.k (3 * i) 0) (fun x y h => ⟨hok x h.2.1, hok y h.2.2⟩)
      fun _ _ _ _ h hx hy => ⟨h.1.post (ecB_bases K.L) hx.1 hy.1, hx.2, hy.2⟩) ?_
    refine RelCT.seq (seed_tr (ecB_bases K.L) (K := 0) (by omega) (by decide) (T.ij i hi 0 (by decide)).1
      (T.ij i hi 0 (by decide)).2 (hsd 0 (by decide)).1.1) ?_
    refine RelCT.seq (seed_tr (ecB_bases K.L) (K := 1) (by omega) (by decide) (T.ij i hi 1 (by decide)).1
      (T.ij i hi 1 (by decide)).2 (hsd 1 (by decide)).1.1) ?_
    refine RelCT.seq (seed_tr (ecB_bases K.L) (K := 2) (by omega) (by decide) (T.ij i hi 2 (by decide)).1
      (T.ij i hi 2 (by decide)).2 (hsd 2 (by decide)).1.1) ?_
    refine RelCT.seq (seed_tr (ecB_bases K.L) (K := 3) (by omega) (by decide) (T.ij i hi 3 (by decide)).1
      (T.ij i hi 3 (by decide)).2 (hsd 3 (by decide)).1.1) ?_
    refine RelCT.mono (sampleHAt16_tr hB) (fun x y h => ⟨SHH16.of h.1.1 c4, SHH16.of h.1.2.1 c4, h.1.eq W.inBs.1,
      h.1.2.2.2, ?_⟩) fun _ _ h => h
    rw [bytesAt136, bytesAt136, seed4_eq h.2.1 (k := 0) (by decide), seed4_eq h.2.1 (k := 1) (by decide),
      seed4_eq h.2.1 (k := 2) (by decide), seed4_eq h.2.1 (k := 3) (by decide), seed4_eq h.2.2 (k := 0) (by decide),
      seed4_eq h.2.2 (k := 1) (by decide), seed4_eq h.2.2 (k := 2) (by decide), seed4_eq h.2.2 (k := 3) (by decide)]
  · rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
    exact ⟨Enc.rhoE K.L (ekE K.L σ₁), ek_lrel W p₁ p₂ pub h₁.ec h₂.ec, ⟨σ₁, p₁, h₁, rfl⟩,
      ⟨σ₂, p₂, h₂, (rho_pub pub).symm⟩⟩

theorem frags16_tr (F : Ek16HWf K) (T : EkT16Wf K) {b : Prog isa} (hB : BatchHOk16 b) :
    RelCT isa (R K.L fun σ s => FI16 K σ 0 s) (seqR (frag K b) 0 (nb K.L)) (R K.L fun σ s => FI16 K σ (nb K.L) s) := by
  have := seqR_tr (R := fun i => R K.L fun σ s => FI16 K σ i s) (nb K.L) 0 fun k _ hk =>
    relInv (fun σ s hp h => frag16_ok F.toEk16FWf hB hp (by omega) h) (frag16_tr F T hB (by omega))
  rwa [Nat.zero_add] at this

theorem quadM16_tr {n : String} {c : Prog isa} (v : S16Ok c) (F : Ek16HWf K) {q : Nat} (hq : q < K.L.k * K.L.k / 4) (h3 : 3 * nb K.L ≤ 4 * q) :
    RelCT isa (R K.L fun σ s => MI16 K σ (4 * q) s) (quad16 (n, c) K.L.k (4 * q) (sc (K.oA + 512 * (4 * q))) (sc K.oW))
      fun _ _ => True := by
  have W := F.toEcWfB
  have hc := F.qC q hq h3
  simp only [Bool.and_eq_true] at hc
  have h16 : K.L.k * K.L.k ≤ 16 := Nat.mul_le_mul W.k.2 W.k.2
  have hk4 := W.k.2
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => RQ (ecR K.L) (ecW K.L) ρ K.L.k (4 * q) 0 x y)
    (Q := fun _ _ => True) fun ρ => quad16_tr (ρ := ρ) v (ecB_bases K.L) (by omega)
      (fun t ht => ⟨by have := div_lt_k (show 4 * q + t < K.L.k * K.L.k by omega); omega,
        by have := mod_lt_k (show 4 * q + t < K.L.k * K.L.k by omega); omega⟩) hc.1.1) ?_ fun _ _ _ => trivial
  rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
  exact ⟨Enc.rhoE K.L (ekE K.L σ₁), ek_lrel W p₁ p₂ pub h₁.ec h₂.ec,
    ⟨h₁.sb, fun _ h => absurd h (Nat.not_lt_zero _)⟩,
    ⟨by rw [h₂.sb, rho_pub pub], fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩

theorem entsM16_tr {n : String} {c : Prog isa} (v : S16Ok c) (F : Ek16HWf K) :
    RelCT isa (R K.L fun σ s => MI16 K σ (3 * nb K.L) s) (ents16 (n, c) K.L.k K.oA (sc K.oW) (3 * nb K.L) (K.L.k * K.L.k - 3 * nb K.L))
      (R K.L fun σ s => MI16 K σ (K.L.k * K.L.k) s) := by
  have := ents16_tr (n, c) K.L.k K.oA (sc K.oW) (R := fun e => R K.L fun σ s => 3 * nb K.L ≤ e ∧ MI16 K σ e s)
    (fun e he he' => relFalse fun _ _ ⟨_, _, _, _, _, ⟨h3, _⟩, _⟩ => absurd F.noS (by omega))
    (fun q hq => if h3 : 3 * nb K.L ≤ 4 * q then
        relInv (fun σ s hp hs => WP.mono (quadM16_ok v F hp hq hs.1 hs.2) fun _ h => ⟨by omega, h⟩)
          (RelCT.mono (quadM16_tr v F hq h3)
            (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, h₁.2, h₂.2⟩) fun _ _ h => h)
      else relFalse fun _ _ ⟨_, _, _, _, _, ⟨h3', _⟩, _⟩ => h3 h3')
    (K.L.k * K.L.k - 3 * nb K.L) (3 * nb K.L) (by have := F.nbK; omega) F.eS
  rw [Nat.add_sub_cancel' F.nbK.2] at this
  exact RelCT.mono this (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, ⟨Nat.le_refl _, h₁⟩,
    ⟨Nat.le_refl _, h₂⟩⟩) fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, h₁.2, h₂.2⟩

theorem matH16_tr {n : String} {c : Prog isa} (v : S16Ok c) (F : Ek16HWf K) (T : EkT16Wf K) {b : Prog isa} (hB : BatchHOk16 b) :
    RelCT isa (R K.L (ProOut K.L)) (matH K (n, c) b) (R K.L fun σ s => MI16 K σ (K.L.k * K.L.k) s) := by
  unfold matH
  exact RelCT.seq (relInv (I' := RI16 K) (fun σ s hp h => rho16_ok F hp h) (rho16_tr F T))
    (RelCT.seq (relInv (I' := fun σ s => FI16 K σ 0 s) (fun σ s hp h => hz16_ok F hp h) (hz16_tr F T))
      (RelCT.seq (frags16_tr F T hB)
        (RelCT.seq (relInv (I' := fun σ s => MI16 K σ (3 * nb K.L) s) (fun σ s hp h => hcopy16_ok F hp h) (hcopy16_tr F T))
          (entsM16_tr v F))))

theorem hashesF16_tr (F : Ek16HWf K) :
    RelCT isa (R K.L fun σ s => MI16 K σ (K.L.k * K.L.k) s) EncapsH.hashes fun _ _ => True :=
  rel2_of (Encaps.hashes_trL F.toEcWfB) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ek_lrel F.toEcWfB p₁ p₂ pub h₁.ec h₂.ec

/-- The rest of K-PKE.Encrypt if every `SampleNTT` succeeded, for a given `ρ`. -/
theorem ifRest16ρ_tr (hK : KpkeOk K.L) (v : Sample4Impl) {rbs wbs : List (Reg × Nat)} {C : Ctx rbs wbs}
    (hk : K.L.k ≤ 4) (hc : Enc16.EncChks K (rbs ++ wbs) wbs C.chk (.r14, 0))
    (ht : Enc16.tailChk K (rbs ++ wbs) wbs C.chk (.r14, 0) (.r13, 0) = true) {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ Enc16.EBρ K C (.r14, 0) ρ (K.L.k * K.L.k) x ∧
        Enc16.EBρ K C (.r14, 0) ρ (K.L.k * K.L.k) y)
      (ifOk (Top16.encRest K v.callee (.r14, 0) (.r13, 0))) fun _ _ => True := by
  refine ifOk_tr (fun x y ⟨_, ⟨_, _, _, e₁, h₁⟩, ⟨_, _, _, e₂, h₂⟩⟩ => by rw [h₁.m.r15, h₂.m.r15, e₁, e₂])
    (RelCT.mono (Enc16.rest_tr hK v (show Reg.r14 ∉ argRegs by decide) (by decide) hk hc ht (ρ := ρ)) ?_
      fun _ _ _ => trivial) fun _ _ _ => trivial
  rintro x y ⟨x₀, y₀, ⟨hl, ⟨ek₁, m₁, r₁, e₁, h₁⟩, ⟨ek₂, m₂, r₂, e₂, h₂⟩⟩, hx, hy, hne⟩
  have o₁ := KeyGen.r15_ne h₁.m.r15 hne
  have o₂ : allOk K.L.k (Enc.rhoE K.L ek₂) (K.L.k * K.L.k) := by rw [e₂, ← e₁]; exact o₁
  exact ⟨hl.post C.bs hx.b hy.b, ⟨ek₁, m₁, r₁, e₁, Enc16.ER0.start (h₁.flag hx hc) o₁⟩,
    ⟨ek₂, m₂, r₂, e₂, Enc16.ER0.start (h₂.flag hy hc) o₂⟩⟩

theorem ifRest16_tr (hK : KpkeOk K.L) (v : Sample4Impl) (F : Ek16HWf K) :
    RelCT isa (R K.L fun σ s =>
        Enc16.EB16 K (Ek.ekC F.toEcWfB σ) (.r14, 0) (ekE K.L σ) (ekMs σ) (ekG K.L σ).2 (K.L.k * K.L.k) s)
      (ifOk (Top16.encRest K v.callee (.r14, 0) (.r13, 0))) fun _ _ => True := by
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => LRel (ecR K.L) (ecW K.L) x y ∧
      Enc16.EBρ K (Ek.ekCA F.toEcWfB) (.r14, 0) ρ (K.L.k * K.L.k) x ∧
      Enc16.EBρ K (Ek.ekCA F.toEcWfB) (.r14, 0) ρ (K.L.k * K.L.k) y)
    (Q := fun _ _ => True) fun ρ => ifRest16ρ_tr hK v (C := Ek.ekCA F.toEcWfB) F.k.2 F.enc F.tl) ?_
    fun _ _ _ => trivial
  rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
  exact ⟨Enc.rhoE K.L (ekE K.L σ₁), ek_lrel F.toEcWfB p₁ p₂ pub h₁.i.out.2.ec h₂.i.out.2.ec,
    ⟨_, _, _, rfl, Ek.EIn.any h₁.i, h₁.sb, h₁.m⟩, ⟨_, _, _, (rho_pub pub).symm, Ek.EIn.any h₂.i, h₂.sb, h₂.m⟩⟩

theorem out16_tr (F : Ek16HWf K) :
    RelCT isa (R K.L (EncO16 F)) (copy (.r12, 0) (sc oG) 32) fun _ _ => True := by
  obtain ⟨_, oT₁⟩ := F.oT₁
  exact rel2_of (trL F.toEcWfB oT₁) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    ek_lrel F.toEcWfB p₁ p₂ pub h₁.out.2.ec h₂.out.2.ec

end EkF16

open EkF16 Ek in
theorem kemEncaps16_ct {K : Kem16} (hK : KpkeOk K.L) (v : Sample4Impl) (F : Ek16HWf K) (T : EkT16Wf K)
    {n : String} {c : Prog isa} (hs : v.callee.s16 = some (n, c)) {b : Prog isa} (hb : v.callee.batchH16 = some b) :
    ConstantTime isa (encK K.L).pre (encK K.L).pub (kemEncaps16 K v.callee (n, c) b) := by
  have hB := v.batchH16 b hb
  have hS := v.s16 n c hs
  refine relStart (Q := fun _ _ => True) ?_
  unfold kemEncaps16
  refine RelCT.seq (relInv (I' := ProOut K.L) (fun σ s hp hs => by subst hs; exact pro_ok F.toEcWfB hp) pro_tr) ?_
  refine RelCT.seq (matH16_tr hS F T hB) ?_
  refine RelCT.seq (relInv (I' := fun σ s => Enc16.EB16 K (ekC F.toEcWfB σ) (.r14, 0) (ekE K.L σ) (ekMs σ)
    (ekG K.L σ).2 (K.L.k * K.L.k) s) (fun σ s hp hs => hashesF16_ok F hp hs) (hashesF16_tr F)) ?_
  refine RelCT.seq (relInv (I' := EncO16 F) (fun σ s _ hs => ifRest16_ok hK v F hs) (ifRest16_tr hK v F)) ?_
  refine RelCT.seq (relInv (I' := EKEnd K.L) (fun σ s _ hs => out16_ok F hs) (out16_tr F)) ?_
  exact RelCT.mono epi_tr (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.MlKem.X86_64
