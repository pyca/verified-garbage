module

public import VerifiedGarbage.Proof.MlKem.X86_64.DjFused16
meta import VerifiedGarbage.Proof.MlKem.X86_64.DjFused16
import VerifiedGarbage.Proof.MlKem.X86_64.EkFusedCT16
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkFusedCT16
import all Init.Data.Nat.Bitwise.Basic
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlKem.X86_64.KgTop
import VerifiedGarbage.Proof.MlKem.X86_64.KgCT
meta import Mathlib.Tactic.Conv
meta import VerifiedGarbage.Proof.MlKem.X86_64.YLanes

/-!
# ML-KEM on x86-64: decapsulation hashing `z ‖ c` in the matrix's fragments, constant time

`kemDecapsJ16_ct`: two runs whose pointers and `ρ` agree leak the same. The
fragments' blocks of `pad(z ‖ c)` and the sponge's state, which only the
fourth Keccak state absorbs, are at fixed addresses (`jblk` and the copies
pass the taint analysis from the pointers, `DjTWf`), and the sampling's
branches and addresses depend on the seeds of `ρ` alone, as in
`kemEncaps16_ct`; the rest leaks only the pointers, as in the
decapsulation of `u32` polynomials.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace DjF16

open VG.Proof.MlKem.X86_64.Decaps (DC DM dcEk dcR dcW dcB dcB_bases DcWfB R dc_lrel rho_pub dcXA)
open VG.Proof.MlKem.X86_64.EkF (relFalse)
open VG.Impl.MlKem.X86_64.Encaps (nb)
open VG.Impl.MlKem.X86_64.Encaps16 (oHS oHB hzero)
open VG.Impl.MlKem.X86_64.DecapsJ16 (hashG jblk frag matJ)

variable (K : Kem16)

/-- The taint checks of the pieces the fused decapsulation adds, from the pointers. -/
structure DjTWf : Prop where
  rbpIn : inB (dcB K.L) (.rbp, 0) 1 = true
  zT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r14]) (.block (hzero K)) h).isSome = true
  jT : ∀ i < nb K.L, ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r14]) (jblk K i) h).isSome = true
  kT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r14])
    (copy (sc oKB) (sc (oHS K)) 32) h).isSome = true
  ij : ∀ i < nb K.L, ∀ J < 4, (3 * i + J) / K.L.k < 4 ∧ (3 * i + J) % K.L.k < 4

variable {K}

section
variable (F : DjHWf K) (T : DjTWf K)
include F T

/-- Code the taint analysis proves constant time from the pointers. -/
theorem trLD {c : Prog isa} {h : VG.Taint.Hint X86_64.Taint.T}
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r14]) c h).isSome = true) :
    RelCT isa (LRel (dcR K.L) (dcW K.L)) c fun _ _ => True :=
  taintRel [.rbx, .rbp, .r12, .r14] (fun _ _ h =>
    fa4 (h.eq (p := sc 0) (l := 1) F.inBs.1) (h.eq (p := (.rbp, 0)) (l := 1) T.rbpIn)
      (h.eq (p := (.r12, 0)) (l := 1) F.inBs.2.1) (h.eq (p := (.r14, 0)) (l := 1) F.inBs.2.2)) ht

theorem rhoJ_tr :
    RelCT isa (R K.L (GI F.toDcWfB)) (copy (sc oSB) (.rbp, 384 * K.L.k + 384 * K.L.k) 32) fun _ _ => True := by
  obtain ⟨_, t⟩ := F.rhoT
  exact rel2_of (taintRel [.rbx, .rbp] (fun _ _ h =>
      fa2 (h.eq (p := sc 0) (l := 1) F.inBs.1) (h.eq (p := (.rbp, 0)) (l := 1) T.rbpIn)) t)
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => dc_lrel F.toDcWfB p₁ p₂ pub h₁.1.out.2.dc h₂.1.out.2.dc

theorem hzJ_tr : RelCT isa (R K.L fun σ s => EBG F.toDcWfB σ 0 s) (.block (hzero K)) fun _ _ => True := by
  obtain ⟨_, t⟩ := T.zT
  exact rel2_of (trLD F T t) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    dc_lrel F.toDcWfB p₁ p₂ pub h₁.i.out.2.dc h₂.i.out.2.dc

theorem kbJ_tr : RelCT isa (R K.L fun σ s => FJ F.toDcWfB σ (nb K.L) s) (copy (sc oKB) (sc (oHS K)) 32)
    fun _ _ => True := by
  obtain ⟨_, t⟩ := T.kT
  exact rel2_of (trLD F T t) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    dc_lrel F.toDcWfB p₁ p₂ pub h₁.eb.i.out.2.dc h₂.eb.i.out.2.dc

end

theorem hashG_tr (W : DcWfB K.L oCT16) : RelCT isa (R K.L (DM K.L)) (hashG K) fun _ _ => True := by
  unfold hashG
  exact rel2_of (hash_tr (dcB_bases K.L) (ps := [(sc oM, 32), ((.rbp, 768 * K.L.k + 32), 32)]) (rate := 72)
    (out := sc oG) (len := 64) W.h₁ (show 6 < 256 by decide)) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    dc_lrel W p₁ p₂ pub h₁.dc h₂.dc

/-- Before fragment `i`, for the `ρ` of `dk`'s key. -/
abbrev FJρ (W : DcWfB K.L oCT16) (ρ : List Byte) (i : Nat) (s : State) : Prop :=
  ∃ σ, (decapsK K.L).pre σ ∧ FJ W σ i s ∧ Enc.rhoE K.L (dcEk K.L σ) = ρ

theorem fragJ_tr (F : DjHWf K) (T : DjTWf K) {b : Prog isa} (hB : BatchHOk16 b) {i : Nat} (hi : i < nb K.L) :
    RelCT isa (R K.L fun σ s => FJ F.toDcWfB σ i s) (frag K b i) fun _ _ => True := by
  obtain ⟨_, t⟩ := T.jT i hi
  have hsd := F.sd i hi
  simp only [sdChk, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hsd
  have hsm := F.sm i hi
  simp only [smChk, Bool.and_eq_true] at hsm
  have hc := F.jb i hi
  simp only [jbChk, Bool.and_eq_true] at hc
  have h16 : K.L.k * K.L.k ≤ 16 := Nat.mul_le_mul F.k.2 F.k.2
  have hnb := F.nbK
  have c4 := hsm.1
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => LRel (dcR K.L) (dcW K.L) x y ∧ FJρ F.toDcWfB ρ i x ∧
    FJρ F.toDcWfB ρ i y) (Q := fun _ _ => True) fun ρ => ?_) ?_ fun _ _ _ => trivial
  · unfold frag
    have hok : ∀ x, FJρ F.toDcWfB ρ i x → WP isa (jblk K i) x fun x' =>
        PPostB x x' [(sc (oHB K), 408)] ∧ SeedsIs ρ K.L.k (3 * i) 0 x' := fun x ⟨σ, hp, h, e⟩ =>
      WP.mono (jblk_ok F.toDjFWf hi h) fun x' ⟨hP, h15, _⟩ =>
        ⟨hP, ⟨by rw [(h.keep hP h15 hc.2).eb.sb, e], fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩
    refine RelCT.seq (RelCT.postDep (RelCT.mono (trLD F T t) (fun _ _ h => h.1) fun _ _ h => h)
      (F := fun x x' => PPostB x x' [(sc (oHB K), 408)] ∧ SeedsIs ρ K.L.k (3 * i) 0 x')
      (Q := RQ (dcR K.L) (dcW K.L) ρ K.L.k (3 * i) 0) (fun x y h => ⟨hok x h.2.1, hok y h.2.2⟩)
      fun _ _ _ _ h hx hy => ⟨h.1.post (dcB_bases K.L) hx.1 hy.1, hx.2, hy.2⟩) ?_
    refine RelCT.seq (seed_tr (dcB_bases K.L) (K := 0) (by omega) (by decide) (T.ij i hi 0 (by decide)).1
      (T.ij i hi 0 (by decide)).2 (hsd 0 (by decide)).1.1) ?_
    refine RelCT.seq (seed_tr (dcB_bases K.L) (K := 1) (by omega) (by decide) (T.ij i hi 1 (by decide)).1
      (T.ij i hi 1 (by decide)).2 (hsd 1 (by decide)).1.1) ?_
    refine RelCT.seq (seed_tr (dcB_bases K.L) (K := 2) (by omega) (by decide) (T.ij i hi 2 (by decide)).1
      (T.ij i hi 2 (by decide)).2 (hsd 2 (by decide)).1.1) ?_
    refine RelCT.seq (seed_tr (dcB_bases K.L) (K := 3) (by omega) (by decide) (T.ij i hi 3 (by decide)).1
      (T.ij i hi 3 (by decide)).2 (hsd 3 (by decide)).1.1) ?_
    refine RelCT.mono (sampleHAt16_tr hB) (fun x y h => ⟨SHH16.of h.1.1 c4, SHH16.of h.1.2.1 c4, h.1.eq F.inBs.1,
      h.1.2.2.2, ?_⟩) fun _ _ h => h
    rw [bytesAt136, bytesAt136, seed4_eq h.2.1 (k := 0) (by decide), seed4_eq h.2.1 (k := 1) (by decide),
      seed4_eq h.2.1 (k := 2) (by decide), seed4_eq h.2.1 (k := 3) (by decide), seed4_eq h.2.2 (k := 0) (by decide),
      seed4_eq h.2.2 (k := 1) (by decide), seed4_eq h.2.2 (k := 2) (by decide), seed4_eq h.2.2 (k := 3) (by decide)]
  · rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
    exact ⟨Enc.rhoE K.L (dcEk K.L σ₁), dc_lrel F.toDcWfB p₁ p₂ pub h₁.eb.i.out.2.dc h₂.eb.i.out.2.dc,
      ⟨σ₁, p₁, h₁, rfl⟩, ⟨σ₂, p₂, h₂, (rho_pub pub).symm⟩⟩

theorem fragsJ_tr (F : DjHWf K) (T : DjTWf K) {b : Prog isa} (hB : BatchHOk16 b) :
    RelCT isa (R K.L fun σ s => FJ F.toDcWfB σ 0 s) (seqR (frag K b) 0 (nb K.L))
      (R K.L fun σ s => FJ F.toDcWfB σ (nb K.L) s) := by
  have := seqR_tr (R := fun i => R K.L fun σ s => FJ F.toDcWfB σ i s) (nb K.L) 0 fun k _ hk =>
    relInv (fun σ s hp h => fragJ_ok F.toDjFWf hB (by omega) h) (fragJ_tr F T hB (by omega))
  rwa [Nat.zero_add] at this

theorem quadJ_tr {n : String} {c : Prog isa} (v : S16Ok c) (F : DjHWf K) {q : Nat} (hq : q < K.L.k * K.L.k / 4) :
    RelCT isa (R K.L fun σ s => EBX F.toDcWfB σ (4 * q) s)
      (quad16 (n, c) K.L.k (4 * q) (sc (K.oA + 512 * (4 * q))) (sc K.oW)) fun _ _ => True := by
  have hc := F.enc.q q hq
  simp only [Enc16.quadEChk, Bool.and_eq_true] at hc
  have h16 : K.L.k * K.L.k ≤ 16 := Nat.mul_le_mul F.k.2 F.k.2
  have hk4 := F.k.2
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => RQ (dcR K.L) (dcW K.L) ρ K.L.k (4 * q) 0 x y)
    (Q := fun _ _ => True) fun ρ => quad16_tr (ρ := ρ) v (dcB_bases K.L) (by omega)
      (fun t ht => ⟨by have := div_lt_k (show 4 * q + t < K.L.k * K.L.k by omega); omega,
        by have := mod_lt_k (show 4 * q + t < K.L.k * K.L.k by omega); omega⟩) hc.1.1.1) ?_ fun _ _ _ => trivial
  rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
  exact ⟨Enc.rhoE K.L (dcEk K.L σ₁), dc_lrel F.toDcWfB p₁ p₂ pub h₁.i.out.2.dc h₂.i.out.2.dc,
    ⟨h₁.sb, fun _ h => absurd h (Nat.not_lt_zero _)⟩,
    ⟨by rw [h₂.sb, rho_pub pub], fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩

theorem entsJ_tr {n : String} {c : Prog isa} (v : S16Ok c) (F : DjHWf K) :
    RelCT isa (R K.L fun σ s => EBX F.toDcWfB σ (3 * nb K.L) s)
      (ents16 (n, c) K.L.k K.oA (sc K.oW) (3 * nb K.L) (K.L.k * K.L.k - 3 * nb K.L))
      (R K.L fun σ s => EBX F.toDcWfB σ (K.L.k * K.L.k) s) := by
  have h16 : K.L.k * K.L.k ≤ 16 := Nat.mul_le_mul F.k.2 F.k.2
  have := ents16_tr (n, c) K.L.k K.oA (sc K.oW)
    (R := fun e => R K.L fun σ s => 3 * nb K.L ≤ e ∧ EBX F.toDcWfB σ e s)
    (fun e he he' => relFalse fun _ _ ⟨_, _, _, _, _, ⟨h3, _⟩, _⟩ => absurd F.noS (by omega))
    (fun q hq => relInv (fun σ s hp hs => WP.mono (Enc16.quadE_step v (C := Decaps.dcX F.toDcWfB σ) (by omega) (F.enc.q q hq) hs.2)
        fun _ h => ⟨by omega, h.2⟩)
      (RelCT.mono (quadJ_tr v F hq)
        (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, h₁.2, h₂.2⟩) fun _ _ h => h))
    (K.L.k * K.L.k - 3 * nb K.L) (3 * nb K.L) (by have := F.nbK; omega) F.eS
  rw [Nat.add_sub_cancel' F.nbK.2] at this
  exact RelCT.mono this (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, ⟨Nat.le_refl _, h₁⟩,
    ⟨Nat.le_refl _, h₂⟩⟩) fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, h₁.2, h₂.2⟩

theorem matJ_tr {n : String} {c : Prog isa} (v : S16Ok c) (F : DjHWf K) (T : DjTWf K) {b : Prog isa}
    (hB : BatchHOk16 b) :
    RelCT isa (R K.L (GI F.toDcWfB)) (matJ K (n, c) b) (R K.L fun σ s => EBX F.toDcWfB σ (K.L.k * K.L.k) s) := by
  unfold matJ
  exact RelCT.seq (relInv (I' := fun σ s => EBG F.toDcWfB σ 0 s) (fun σ s hp h => rhoJ_ok F h) (rhoJ_tr F T))
    (RelCT.seq (relInv (I' := fun σ s => FJ F.toDcWfB σ 0 s) (fun σ s hp h => hzJ_ok F h) (hzJ_tr F T))
      (RelCT.seq (fragsJ_tr F T hB)
        (RelCT.seq (relInv (I' := fun σ s => EBX F.toDcWfB σ (3 * nb K.L) s) (fun σ s hp h => kbJ_ok F h)
          (kbJ_tr F T)) (entsJ_tr v F))))

/-- The rest of the re-encryption if every `SampleNTT` succeeded. -/
theorem ifRestJ_tr (hK : KpkeOk K.L) (v : Sample4Impl) (F : DjHWf K) :
    RelCT isa (R K.L fun σ s => EBX F.toDcWfB σ (K.L.k * K.L.k) s)
      (ifOk (Top16.encRest K v.callee (.rbp, 384 * K.L.k) (sc oCT16))) fun _ _ => True := by
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => LRel (dcR K.L) (dcW K.L) x y ∧
      Enc16.EBρ K (dcXA F.toDcWfB) (.rbp, 384 * K.L.k) ρ (K.L.k * K.L.k) x ∧
      Enc16.EBρ K (dcXA F.toDcWfB) (.rbp, 384 * K.L.k) ρ (K.L.k * K.L.k) y)
    (Q := fun _ _ => True) fun ρ => ?_) ?_ fun _ _ _ => trivial
  · refine ifOk_tr (fun x y ⟨_, ⟨_, _, _, e₁, h₁⟩, ⟨_, _, _, e₂, h₂⟩⟩ => by rw [h₁.m.r15, h₂.m.r15, e₁, e₂])
      (RelCT.mono (Enc16.rest_tr hK v (C := dcXA F.toDcWfB) (show Reg.rbp ∉ argRegs by decide) (by decide) F.k.2 F.enc F.tl
        (ρ := ρ)) ?_
        fun _ _ _ => trivial) fun _ _ _ => trivial
    rintro x y ⟨x₀, y₀, ⟨hl, ⟨ek₁, m₁, r₁, e₁, h₁⟩, ⟨ek₂, m₂, r₂, e₂, h₂⟩⟩, hx, hy, hne⟩
    have o₁ := KeyGen.r15_ne h₁.m.r15 hne
    have o₂ : allOk K.L.k (Enc.rhoE K.L ek₂) (K.L.k * K.L.k) := by rw [e₂, ← e₁]; exact o₁
    exact ⟨hl.post (dcXA F.toDcWfB).bs hx.b hy.b, ⟨ek₁, m₁, r₁, e₁, Enc16.ER0.start (h₁.flag hx F.enc) o₁⟩,
      ⟨ek₂, m₂, r₂, e₂, Enc16.ER0.start (h₂.flag hy F.enc) o₂⟩⟩
  · rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
    exact ⟨Enc.rhoE K.L (dcEk K.L σ₁), dc_lrel F.toDcWfB p₁ p₂ pub h₁.i.out.2.dc h₂.i.out.2.dc,
      ⟨_, _, _, rfl, Decaps.EIn.any h₁.i, h₁.sb, h₁.m⟩, ⟨_, _, _, (rho_pub pub).symm, Decaps.EIn.any h₂.i, h₂.sb, h₂.m⟩⟩

end DjF16

open Decaps Decaps16 DjF16 in
theorem kemDecapsJ16_ct {K : Kem16} (hK : KpkeOk K.L) (v : Sample4Impl) (F : DjHWf K) (T : DjTWf K)
    {n : String} {c : Prog isa} (hs : v.callee.s16 = some (n, c)) {b : Prog isa} (hb : v.callee.batchH16 = some b) :
    ConstantTime isa (decapsK K.L).pre (decapsK K.L).pub (kemDecapsJ16 K v.callee (n, c) b) := by
  have hB := v.batchH16 b hb
  have hS := v.s16 n c hs
  refine relStart (Q := fun _ _ => True) ?_
  unfold kemDecapsJ16
  refine RelCT.seq (relInv (I' := fun σ s => DC K.L σ s ∧ s.gpr .r15 = 1)
    (fun σ s hp hs => by subst hs; exact pro_ok F.toDcWfB hp) pro_tr) ?_
  refine RelCT.seq (relInv (I' := DM K.L) (fun σ s hp hs => dec_ok hK F.toDc16Wf hp hs.1 hs.2)
    (dec_tr hK F.toDc16Wf)) ?_
  refine RelCT.seq (relInv (I' := GI F.toDcWfB) (fun σ s hp hs => hashG_ok F.toDcWfB hp hs)
    (hashG_tr F.toDcWfB)) ?_
  refine RelCT.seq (matJ_tr hS F T hB) ?_
  refine RelCT.seq (relInv (I' := EncO16 F.toDc16Wf) (fun σ s _ hs => ifRestJ_ok hK v F hs) (ifRestJ_tr hK v F)) ?_
  refine RelCT.seq (relInv (I' := DEnd K.L) (fun σ s _ hs => select_okD F.toDcWfB hs.sel)
    (RelCT.mono (select_tr F.toDcWfB) (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ =>
      ⟨σ₁, σ₂, p₁, p₂, pub, h₁.sel, h₂.sel⟩) fun _ _ h => h)) ?_
  exact RelCT.mono epi_tr (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.MlKem.X86_64
