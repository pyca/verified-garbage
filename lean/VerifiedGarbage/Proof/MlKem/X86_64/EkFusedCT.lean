module

public import VerifiedGarbage.Proof.MlKem.X86_64.EkFused
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkFused
import all Init.Data.Nat.Bitwise.Basic
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
meta import Mathlib.Tactic.Conv
meta import VerifiedGarbage.Proof.MlKem.X86_64.YLanes

/-!
# ML-KEM on x86-64: encapsulation hashing the key in the matrix's fragments, constant time

Two runs of `kemEncaps L v.callee` with a fragment `b`, from states whose
pointers and `ρ` agree, leak the same (`kemEncapsF_ct`): the copies and
the padding of `pad(ek)` are proven by the taint analysis from the pointers
(`EkTWf`, evaluated for each parameter set); the seeds of a fragment are
those of `ρ`, so its fragment `b` is constant time from them
(`sampleHAt_tr`), whatever `ek` its fourth Keccak state absorbs; and the rest
is `kemEncapsH`'s.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace EkF

open VG.Proof.MlKem.X86_64.Encaps (ecR ecW ecB ecB_bases EcWf trL)
open VG.Proof.MlKem.X86_64.Ek (EK ekE ekMs ekG ProOut R ek_lrel rho_pub)
open VG.Impl.MlKem.X86_64.Encaps (oHS nb hzero matH hblk frag)

variable (L : Kem)

/-- The taint checks of the pieces the fused encapsulation adds, from the pointers. -/
structure EkTWf : Prop where
  rT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14])
    (copy (sc oSB) (.r14, 384 * L.k) 32) h).isSome = true
  zT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14]) (.block (hzero L)) h).isSome = true
  hT : ∀ i < nb L, ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14]) (hblk L i) h).isSome = true
  hcT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14])
    (copy (sc oH) (sc (oHS L)) 32) h).isSome = true
  ij : ∀ i < nb L, ∀ K < 4, (3 * i + K) / L.k < 4 ∧ (3 * i + K) % L.k < 4

variable {L}

/-- Code whose runs are never related. -/
theorem relFalse {P Q : State → State → Prop} {c : Prog isa} (h : ∀ x y, P x y → False) : RelCT isa P c Q :=
  fun _ _ _ _ _ _ hp _ _ => (h _ _ hp).elim

section
variable (F : EkHWf L) (T : EkTWf L)
include F T

theorem rho_tr : RelCT isa (R L (ProOut L)) (copy (sc oSB) (.r14, 384 * L.k) 32) fun _ _ => True := by
  obtain ⟨_, t⟩ := T.rT
  exact rel2_of (trL F.toEcWf t) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ek_lrel F.toEcWf p₁ p₂ pub h₁.ec h₂.ec

theorem hz_tr : RelCT isa (R L (RI L)) (.block (hzero L)) fun _ _ => True := by
  obtain ⟨_, t⟩ := T.zT
  exact rel2_of (trL F.toEcWf t) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ek_lrel F.toEcWf p₁ p₂ pub h₁.ec h₂.ec

theorem hcopy_tr : RelCT isa (R L fun σ s => FI L σ (nb L) s) (copy (sc oH) (sc (oHS L)) 32) fun _ _ => True := by
  obtain ⟨_, t⟩ := T.hcT
  exact rel2_of (trL F.toEcWf t) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ek_lrel F.toEcWf p₁ p₂ pub h₁.ec h₂.ec

end

/-- Before fragment `i`, for the `ρ` of `ek`. -/
abbrev FIρ (L : Kem) (ρ : List Byte) (i : Nat) (s : State) : Prop :=
  ∃ σ, (encK L).pre σ ∧ FI L σ i s ∧ Enc.rhoE L (ekE L σ) = ρ

theorem frag_tr (F : EkHWf L) (T : EkTWf L) {b : Prog isa} (hB : BatchHOk b) {i : Nat} (hi : i < nb L) :
    RelCT isa (R L fun σ s => FI L σ i s) (frag L b i) fun _ _ => True := by
  have W := F.toEcWf
  obtain ⟨_, t⟩ := T.hT i hi
  have hsd := F.sd i hi
  simp only [sdChk, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hsd
  have hsm := F.sm i hi
  simp only [smChk, Bool.and_eq_true] at hsm
  have hc := F.hb i hi
  simp only [hbChk, Bool.and_eq_true] at hc
  have h16 : L.k * L.k ≤ 16 := Nat.mul_le_mul W.k.2 W.k.2
  have hnb := F.nbK
  have c4 := hsm.1
  have hin : inB (ecB L) (sc 0) 136 = true := by
    simp only [s4Chk, rdOk, Bool.and_eq_true] at c4; exact c4.1.1.1.1.1.2
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => LRel (ecR L) (ecW L) x y ∧ FIρ L ρ i x ∧ FIρ L ρ i y)
    (Q := fun _ _ => True) fun ρ => ?_) ?_ fun _ _ _ => trivial
  · unfold frag
    have hok : ∀ x, FIρ L ρ i x → WP isa (hblk L i) x fun x' =>
        PPostB x x' [(sc (Encaps.oHB L), 408)] ∧ SeedsIs ρ L.k (3 * i) 0 x' := fun x ⟨σ, hp, h, e⟩ =>
      WP.mono (hblk_ok F.toEkFWf hp hi h) fun x' ⟨hP, h15, _⟩ =>
        ⟨hP, ⟨by rw [(h.keep W hp hP h15 hc.2).sb, e], fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩
    refine RelCT.seq (RelCT.postDep (RelCT.mono (trL W t) (fun _ _ h => h.1) fun _ _ h => h)
      (F := fun x x' => PPostB x x' [(sc (Encaps.oHB L), 408)] ∧ SeedsIs ρ L.k (3 * i) 0 x')
      (Q := RQ (ecR L) (ecW L) ρ L.k (3 * i) 0) (fun x y h => ⟨hok x h.2.1, hok y h.2.2⟩)
      fun _ _ _ _ h hx hy => ⟨h.1.post (ecB_bases L) hx.1 hy.1, hx.2, hy.2⟩) ?_
    refine RelCT.seq (seed_tr (ecB_bases L) (K := 0) (by omega) (by decide) (T.ij i hi 0 (by decide)).1
      (T.ij i hi 0 (by decide)).2 (hsd 0 (by decide)).1.1) ?_
    refine RelCT.seq (seed_tr (ecB_bases L) (K := 1) (by omega) (by decide) (T.ij i hi 1 (by decide)).1
      (T.ij i hi 1 (by decide)).2 (hsd 1 (by decide)).1.1) ?_
    refine RelCT.seq (seed_tr (ecB_bases L) (K := 2) (by omega) (by decide) (T.ij i hi 2 (by decide)).1
      (T.ij i hi 2 (by decide)).2 (hsd 2 (by decide)).1.1) ?_
    refine RelCT.seq (seed_tr (ecB_bases L) (K := 3) (by omega) (by decide) (T.ij i hi 3 (by decide)).1
      (T.ij i hi 3 (by decide)).2 (hsd 3 (by decide)).1.1) ?_
    refine RelCT.mono (sampleHAt_tr hB) (fun x y h => ⟨SHH.of h.1.1 c4, SHH.of h.1.2.1 c4, h.1.eq W.inBs.1,
      h.1.2.2.2, ?_⟩) fun _ _ h => h
    rw [bytesAt136, bytesAt136, seed4_eq h.2.1 (k := 0) (by decide), seed4_eq h.2.1 (k := 1) (by decide),
      seed4_eq h.2.1 (k := 2) (by decide), seed4_eq h.2.1 (k := 3) (by decide), seed4_eq h.2.2 (k := 0) (by decide),
      seed4_eq h.2.2 (k := 1) (by decide), seed4_eq h.2.2 (k := 2) (by decide), seed4_eq h.2.2 (k := 3) (by decide)]
  · rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
    exact ⟨Enc.rhoE L (ekE L σ₁), ek_lrel W p₁ p₂ pub h₁.ec h₂.ec, ⟨σ₁, p₁, h₁, rfl⟩,
      ⟨σ₂, p₂, h₂, (rho_pub pub).symm⟩⟩

theorem frags_tr (F : EkHWf L) (T : EkTWf L) {b : Prog isa} (hB : BatchHOk b) :
    RelCT isa (R L fun σ s => FI L σ 0 s) (seqR (frag L b) 0 (nb L)) (R L fun σ s => FI L σ (nb L) s) := by
  have := seqR_tr (R := fun i => R L fun σ s => FI L σ i s) (nb L) 0 fun k _ hk =>
    relInv (fun σ s hp h => frag_ok F.toEkFWf hB hp (by omega) h) (frag_tr F T hB (by omega))
  rwa [Nat.zero_add] at this

theorem quadM_tr (v : Sample4Impl) (F : EkHWf L) {q : Nat} (hq : q < L.k * L.k / 4) (h3 : 3 * nb L ≤ 4 * q) :
    RelCT isa (R L fun σ s => MI L σ (4 * q) s) (quad v.callee L.k (4 * q) (pS (L.pA + 4 * q)) (pS L.pW))
      fun _ _ => True := by
  have W := F.toEcWf
  have hc := F.qC q hq h3
  simp only [Bool.and_eq_true] at hc
  have h16 : L.k * L.k ≤ 16 := Nat.mul_le_mul W.k.2 W.k.2
  have hk4 := W.k.2
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => RQ (ecR L) (ecW L) ρ L.k (4 * q) 0 x y)
    (Q := fun _ _ => True) fun ρ => quad_tr (ρ := ρ) v (ecB_bases L) (by omega)
      (fun t ht => ⟨by have := div_lt_k (show 4 * q + t < L.k * L.k by omega); omega,
        by have := mod_lt_k (show 4 * q + t < L.k * L.k by omega); omega⟩) hc.1.1) ?_ fun _ _ _ => trivial
  rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
  exact ⟨Enc.rhoE L (ekE L σ₁), ek_lrel W p₁ p₂ pub h₁.ec h₂.ec,
    ⟨h₁.sb, fun _ h => absurd h (Nat.not_lt_zero _)⟩,
    ⟨by rw [h₂.sb, rho_pub pub], fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩

theorem entsM_tr (v : Sample4Impl) (F : EkHWf L) :
    RelCT isa (R L fun σ s => MI L σ (3 * nb L) s) (L.ents v.callee (3 * nb L) (L.k * L.k - 3 * nb L))
      (R L fun σ s => MI L σ (L.k * L.k) s) := by
  have := ents_tr L v.callee (R := fun e => R L fun σ s => 3 * nb L ≤ e ∧ MI L σ e s)
    (fun e he he' => relFalse fun _ _ ⟨_, _, _, _, _, ⟨h3, _⟩, _⟩ => absurd F.noS (by omega))
    (fun q hq => if h3 : 3 * nb L ≤ 4 * q then
        relInv (fun σ s hp hs => WP.mono (quadM_ok v F hp hq hs.1 hs.2) fun _ h => ⟨by omega, h⟩)
          (RelCT.mono (quadM_tr v F hq h3)
            (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, h₁.2, h₂.2⟩) fun _ _ h => h)
      else relFalse fun _ _ ⟨_, _, _, _, _, ⟨h3', _⟩, _⟩ => h3 h3')
    (L.k * L.k - 3 * nb L) (3 * nb L) (by have := F.nbK; omega) F.eS
  rw [Nat.add_sub_cancel' F.nbK.2] at this
  exact RelCT.mono this (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, ⟨Nat.le_refl _, h₁⟩,
    ⟨Nat.le_refl _, h₂⟩⟩) fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, h₁.2, h₂.2⟩

theorem matH_tr (v : Sample4Impl) (F : EkHWf L) (T : EkTWf L) {b : Prog isa} (hB : BatchHOk b) :
    RelCT isa (R L (ProOut L)) (matH L v.callee b) (R L fun σ s => MI L σ (L.k * L.k) s) := by
  unfold matH
  exact RelCT.seq (relInv (I' := RI L) (fun σ s hp h => rho_ok F hp h) (rho_tr F T))
    (RelCT.seq (relInv (I' := fun σ s => FI L σ 0 s) (fun σ s hp h => hz_ok F hp h) (hz_tr F T))
      (RelCT.seq (frags_tr F T hB)
        (RelCT.seq (relInv (I' := fun σ s => MI L σ (3 * nb L) s) (fun σ s hp h => hcopy_ok F hp h) (hcopy_tr F T))
          (entsM_tr v F))))

theorem hashesF_tr (F : EkHWf L) :
    RelCT isa (R L fun σ s => MI L σ (L.k * L.k) s) EncapsH.hashes fun _ _ => True :=
  rel2_of (Encaps.hashes_trL F.toEcWf) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ek_lrel F.toEcWf p₁ p₂ pub h₁.ec h₂.ec

/-- The rest of `K-PKE.Encrypt` if every `SampleNTT` succeeded, for a given `ρ`. -/
theorem ifRestρ_tr (v : Sample4Impl) {wc wd : List Nat} (K : KemCalls L wc wd) (W : KemWf L)
    {rbs wbs : List (Reg × Nat)} {C : Ctx rbs wbs} (hc : Enc.EncChks L (rbs ++ wbs) wbs C.chk (.r14, 0))
    {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ Enc.EBρ L C (.r14, 0) ρ (L.k * L.k) x ∧
        Enc.EBρ L C (.r14, 0) ρ (L.k * L.k) y)
      (ifOk (Encrypt.rest L v.callee (.r14, 0))) fun _ _ => True := by
  refine ifOk_tr (fun x y ⟨_, ⟨_, _, _, e₁, h₁⟩, ⟨_, _, _, e₂, h₂⟩⟩ => by rw [h₁.m.r15, h₂.m.r15, e₁, e₂])
    (RelCT.mono (Enc.rest_tr v K W hc (ρ := ρ)) ?_ fun _ _ _ => trivial) fun _ _ _ => trivial
  rintro x y ⟨x₀, y₀, ⟨hl, ⟨ek₁, m₁, r₁, e₁, h₁⟩, ⟨ek₂, m₂, r₂, e₂, h₂⟩⟩, hx, hy, hne⟩
  have o₁ := KeyGen.r15_ne h₁.m.r15 hne
  have o₂ : allOk L.k (Enc.rhoE L ek₂) (L.k * L.k) := by rw [e₂, ← e₁]; exact o₁
  exact ⟨hl.post C.bs hx.b hy.b, ⟨ek₁, m₁, r₁, e₁, Enc.ER0.start (h₁.flag hx hc.inK hc.aK hc.sbK) o₁⟩,
    ⟨ek₂, m₂, r₂, e₂, Enc.ER0.start (h₂.flag hy hc.inK hc.aK hc.sbK) o₂⟩⟩

theorem ifRest_tr (v : Sample4Impl) (F : EkHWf L) {wc wd : List Nat} (K : KemCalls L wc wd) :
    RelCT isa (R L fun σ s => Enc.EB L (Ek.ekC F.toEcWf.toEcWfB σ) (.r14, 0) (ekE L σ) (ekMs σ) (ekG L σ).2 (L.k * L.k) s)
      (ifOk (Encrypt.rest L v.callee (.r14, 0))) fun _ _ => True := by
  have W := F.toEcWf
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => LRel (ecR L) (ecW L) x y ∧
      Enc.EBρ L (Ek.ekCA W.toEcWfB) (.r14, 0) ρ (L.k * L.k) x ∧ Enc.EBρ L (Ek.ekCA W.toEcWfB) (.r14, 0) ρ (L.k * L.k) y)
    (Q := fun _ _ => True) fun ρ => ifRestρ_tr v K W.toKemWf (C := Ek.ekCA W.toEcWfB) (Enc.encChk_spec W.enc)) ?_
    fun _ _ _ => trivial
  rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
  exact ⟨Enc.rhoE L (ekE L σ₁), ek_lrel W p₁ p₂ pub h₁.i.out.2.ec h₂.i.out.2.ec,
    ⟨_, _, _, rfl, Ek.EIn.any h₁.i, h₁.sb, h₁.m⟩, ⟨_, _, _, (rho_pub pub).symm, Ek.EIn.any h₂.i, h₂.sb, h₂.m⟩⟩

end EkF

open EkF Ek in
theorem kemEncapsF_ct (v : Sample4Impl) {L : Kem} (F : EkHWf L) (T : EkTWf L) {wc wd : List Nat}
    (K : KemCalls L wc wd) {b : Prog isa} (hb : v.callee.batchH = some b) :
    ConstantTime isa (encK L).pre (encK L).pub (kemEncaps L v.callee) := by
  have W₀ := F.toEcWf
  have hB := v.batchH b hb
  refine relStart (Q := fun _ _ => True) ?_
  unfold kemEncaps
  rw [hb]
  refine RelCT.seq (relInv (I' := ProOut L) (fun σ s hp hs => by subst hs; exact pro_ok W₀.toEcWfB hp) pro_tr) ?_
  refine RelCT.seq (matH_tr v F T hB) ?_
  refine RelCT.seq (relInv (I' := fun σ s => Enc.EB L (ekC W₀.toEcWfB σ) (.r14, 0) (ekE L σ) (ekMs σ) (ekG L σ).2
    (L.k * L.k) s) (fun σ s hp hs => hashesF_ok F hp hs) (hashesF_tr F)) ?_
  refine RelCT.seq (relInv (I' := EncO W₀) (fun σ s _ hs => ifRest_ok v F K hs) (ifRest_tr v F K)) ?_
  refine RelCT.seq (relInv (I' := EKEnd L) (fun σ s _ hs => out_ok W₀ hs) (out_tr W₀)) ?_
  exact RelCT.mono epi_tr (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.MlKem.X86_64
