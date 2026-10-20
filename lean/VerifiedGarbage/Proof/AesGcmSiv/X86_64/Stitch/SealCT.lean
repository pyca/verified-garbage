module

public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.OpenCT
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Seal
import VerifiedGarbage.Proof.Framework.X86_64.Narrow
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Ctr
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Fn
meta import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.OpenCT
meta import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Seal
meta import VerifiedGarbage.Proof.Framework.X86_64.Narrow
meta import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Ctr
meta import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Fn
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Callee

/-!
# AES-GCM-SIV on x86-64: `vg_aes_gcm_siv_seal` with the loops is constant time

Untrusted: everything here is checked by Lean. As for `seal` (`FnCT.lean`),
two runs with the same public arguments are related piece by piece: the
loops (`hash_check`, `ctr_check`) and the straight blocks pass the taint
analysis from the registers that agree, the calls are related as
`polyval`'s and `crypt`'s are (`absorb_rel`, `lens_rel`, `cryptRest_rel`),
and what each run keeps between the pieces (`Bufs`, `St`) follows from their
correctness.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl toNat_ofNat_of_lt)
open VG.Proof.Aes.X86_64 (BlocksImpl)

/-! ## `hashS` -/

/-- The registers `hash` takes. -/
structure HArgsAt (W D : Addr) (n : Nat) (t : State) : Prop where
  rcx : t.gpr .rcx = W + BitVec.ofNat 64 80
  r8 : t.gpr .r8 = W + BitVec.ofNat 64 64
  r11 : t.gpr .r11 = W + BitVec.ofNat 64 1512
  rdx : t.gpr .rdx = D
  r9 : t.gpr .r9 = BitVec.ofNat 64 (16 * (n / 256))

theorem hArgs_wp {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {t : State}
    (h : Bufs K W SP R N A D al n t) :
    WP isa (.block hArgs) t fun t₁ => Bufs K W SP R N A D al n t₁ ∧ HArgsAt W D n t₁ := by
  obtain ⟨t₁, run₁, hm₁, rcx₁, r8₁, r11₁, rdx₁, r9₁, hg₁, hrd₁, hwr₁⟩ := hArgs_ok h.one.env h.one.sl h.data.lt
  have E₁ : Env K W SP t₁ := h.one.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide)) hrd₁ hwr₁
  exact WP.of_runBlock ⟨t₁, run₁, h.frame E₁ (by rw [hm₁]; exact Frame.refl [] _) (by simp) hrd₁ hwr₁,
    ⟨rcx₁, r8₁, r11₁, rdx₁, r9₁⟩⟩

theorem hArgs_check : ∃ hc, (taint.check (sivT []) (.block hArgs) hc).isSome = true := ⟨_, by taint_decide⟩

theorem hash_check : ∃ hc, (taint.check (sivT [.rcx, .r8, .r11, .rdx, .r9])
    Impl.AesGcmSiv.X86_64Stitch.hash hc).isSome = true := ⟨_, by taint_decide⟩

/-- The hashing loop keeps `Bufs`. -/
theorem hash_bufs {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat}
    (h256 : 256 ≤ n) {t : State} (h : Bufs K W SP R N A D al n t ∧ HArgsAt W D n t) :
    WP isa Impl.AesGcmSiv.X86_64Stitch.hash t (Bufs K W SP R N A D al n) := by
  obtain ⟨hB, G⟩ := h
  have hp := hpre_of L hB.one.env hB.data hB.dw h256 G.rcx G.r8 G.r11 G.rdx G.r9
  refine WP.mono (Stitch.hash_ok hp) fun t' Hp => ?_
  have Fh : Frame [⟨W + BitVec.ofNat 64 80, 16⟩, ⟨W + BitVec.ofNat 64 1512, 256⟩] t.mem t'.mem := by
    have h := Hp.frame
    simp only [Stitch.yR, Stitch.pR, Stitch.yp, Stitch.pp, G.rcx, G.r11] at h
    exact h
  refine hB.frame (hB.one.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Hp.gpr _ (by decide) (by decide) (by decide)) Hp.rd Hp.wr)
    Fh (fun q hq => ?_) Hp.rd Hp.wr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)

theorem HArgsAt.both {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {t₁ t₂ : State}
    (h₁ : Bufs K W SP R N A D al n t₁ ∧ HArgsAt W D n t₁) (h₂ : Bufs K W SP R N A D al n t₂ ∧ HArgsAt W D n t₂) :
    Both K W SP R N A D al n [.rcx, .r8, .r11, .rdx, .r9] t₁ t₂ :=
  ⟨h₁.1.one, h₂.1.one, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [h₁.2.rcx, h₂.2.rcx]
    · rw [h₁.2.r8, h₂.2.r8]
    · rw [h₁.2.r11, h₂.2.r11]
    · rw [h₁.2.rdx, h₂.2.rdx]
    · rw [h₁.2.r9, h₂.2.r9]⟩

/-- `hashS`, in two runs with the same public arguments. -/
theorem hashS_rel (v : GcmImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) (hal : al < 2 ^ 64) (hn' : n < 2 ^ 64)
    (h256 : 256 ≤ n) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → Bufs K W SP R N A D al n t₁ ∧ Bufs K W SP R N A D al n t₂) :
    RelCT isa P (Impl.AesGcmSiv.X86_64Stitch.hashS v.callees wide) fun _ _ => True := by
  have r₁ := (rel_taintC [] hDW hn (fun t₁ t₂ h => ⟨(hP _ _ h).1.one, (hP _ _ h).2.one, fun _ h => nomatch h⟩)
    polyA_check).wp
    (F₁ := fun (t : State) => AbsIn K W SP R N A D al n A al t ∧ Bufs K W SP R N A D al n t)
    (F₂ := fun (t : State) => AbsIn K W SP R N A D al n A al t ∧ Bufs K W SP R N A D al n t)
    fun t₁ t₂ h => ⟨polyBlk_wp (o₁ := aadO) (o₂ := alenO) (hP _ _ h).1 (hP _ _ h).1.aad (hP _ _ h).1.one.sl.aad
        (hP _ _ h).1.one.sl.alen (by decide) (by decide),
      polyBlk_wp (o₁ := aadO) (o₂ := alenO) (hP _ _ h).2 (hP _ _ h).2.aad (hP _ _ h).2.one.sl.aad
        (hP _ _ h).2.one.sl.alen (by decide) (by decide)⟩
  have r₂ := (absorb_rel v wide L hDW hn (Q := A) (nb := al) (P := fun t₁ t₂ => True ∧
      (AbsIn K W SP R N A D al n A al t₁ ∧ Bufs K W SP R N A D al n t₁) ∧
      (AbsIn K W SP R N A D al n A al t₂ ∧ Bufs K W SP R N A D al n t₂))
    fun t₁ t₂ h => ⟨h.2.1.1, h.2.2.1⟩).wp
    (F₁ := Bufs K W SP R N A D al n) (F₂ := Bufs K W SP R N A D al n)
    fun t₁ t₂ h => ⟨absorb_bufs v wide L h.2.1, absorb_bufs v wide L h.2.2⟩
  have r₃ := (rel_taintC [] (P := fun t₁ t₂ => True ∧ Bufs K W SP R N A D al n t₁ ∧ Bufs K W SP R N A D al n t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.one, h.2.2.one, fun _ h => nomatch h⟩) hArgs_check).wp
    (F₁ := fun (t : State) => Bufs K W SP R N A D al n t ∧ HArgsAt W D n t)
    (F₂ := fun (t : State) => Bufs K W SP R N A D al n t ∧ HArgsAt W D n t)
    fun t₁ t₂ h => ⟨hArgs_wp h.2.1, hArgs_wp h.2.2⟩
  have r₄ := (rel_taintC [.rcx, .r8, .r11, .rdx, .r9] (P := fun t₁ t₂ => True ∧
      (Bufs K W SP R N A D al n t₁ ∧ HArgsAt W D n t₁) ∧ (Bufs K W SP R N A D al n t₂ ∧ HArgsAt W D n t₂))
    hDW hn (fun t₁ t₂ h => HArgsAt.both h.2.1 h.2.2) hash_check).wp
    (F₁ := Bufs K W SP R N A D al n) (F₂ := Bufs K W SP R N A D al n)
    fun t₁ t₂ h => ⟨hash_bufs L h256 h.2.1, hash_bufs L h256 h.2.2⟩
  have absIn : ∀ {t : State}, (Bufs K W SP R N A D al n t ∧
      t.gpr .r12 = D + BitVec.ofNat 64 (256 * (n / 256)) ∧ t.gpr .rbp = BitVec.ofNat 64 (n % 256)) →
      AbsIn K W SP R N A D al n (D + BitVec.ofNat 64 (256 * (n / 256))) (n % 256) t ∧
        Bufs K W SP R N A D al n t := fun h =>
    ⟨⟨h.1.one, h.1.data.slice (by omega), h.2.1, h.2.2⟩, h.1⟩
  have r₅ := (rel_taintC [] (P := fun t₁ t₂ => True ∧ Bufs K W SP R N A D al n t₁ ∧ Bufs K W SP R N A D al n t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.one, h.2.2.one, fun _ h => nomatch h⟩) rest_check).wp
    (F₁ := fun (t : State) =>
      AbsIn K W SP R N A D al n (D + BitVec.ofNat 64 (256 * (n / 256))) (n % 256) t ∧ Bufs K W SP R N A D al n t)
    (F₂ := fun (t : State) =>
      AbsIn K W SP R N A D al n (D + BitVec.ofNat 64 (256 * (n / 256))) (n % 256) t ∧ Bufs K W SP R N A D al n t)
    fun t₁ t₂ h => ⟨WP.mono (rest_wp h.2.1) fun _ h => absIn h, WP.mono (rest_wp h.2.2) fun _ h => absIn h⟩
  have r₆ := (absorb_rel v wide L hDW hn (Q := D + BitVec.ofNat 64 (256 * (n / 256))) (nb := n % 256)
    (P := fun t₁ t₂ => True ∧
      (AbsIn K W SP R N A D al n (D + BitVec.ofNat 64 (256 * (n / 256))) (n % 256) t₁ ∧ Bufs K W SP R N A D al n t₁) ∧
      (AbsIn K W SP R N A D al n (D + BitVec.ofNat 64 (256 * (n / 256))) (n % 256) t₂ ∧ Bufs K W SP R N A D al n t₂))
    fun t₁ t₂ h => ⟨h.2.1.1, h.2.2.1⟩).wp
    (F₁ := Bufs K W SP R N A D al n) (F₂ := Bufs K W SP R N A D al n)
    fun t₁ t₂ h => ⟨absorb_bufs v wide L h.2.1, absorb_bufs v wide L h.2.2⟩
  have r₇ := (lens_rel v L hDW hn hal hn' (P := fun t₁ t₂ => True ∧ Bufs K W SP R N A D al n t₁ ∧
      Bufs K W SP R N A D al n t₂) fun t₁ t₂ h => ⟨h.2.1.one, h.2.2.one⟩).wp
    (F₁ := Bufs K W SP R N A D al n) (F₂ := Bufs K W SP R N A D al n)
    fun t₁ t₂ h => ⟨lens_bufs v L hal hn' h.2.1, lens_bufs v L hal hn' h.2.2⟩
  have r₈ := rel_taintC [] (P := fun t₁ t₂ => True ∧ Bufs K W SP R N A D al n t₁ ∧ Bufs K W SP R N A D al n t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.one, h.2.2.one, fun _ h => nomatch h⟩) tagIn_check
  exact RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ (RelCT.seq r₄ (RelCT.seq r₅ (RelCT.seq r₆
    (RelCT.seq r₇ r₈))))))

/-! ## `cryptS` -/

theorem ctr_check : ∃ hc, (taint.check (sivT [.rdi, .rsi, .rdx, .rcx, .r8, .r11, .r12, .r9])
    Impl.AesGcmSiv.X86_64Stitch.ctr hc).isSome = true := ⟨_, by taint_decide⟩

/-- Counter mode on the groups keeps `Bufs`. -/
theorem ctr_bufs {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr} {al n : Nat}
    (h256 : 256 ≤ n) {t : State} (h : Bufs K W SP R N A D al n t ∧ ArgsAt W D R n t) :
    WP isa Impl.AesGcmSiv.X86_64Stitch.ctr t (Bufs K W SP R N A D al n) := by
  obtain ⟨hB, G⟩ := h
  have hn := hB.data.lt
  have hp := spre_of L hR hB.one.env hB.data hB.dw h256 G.rdi G.rsi G.rdx G.rcx G.r8 G.r11 G.r12 G.r9
  have hnb : Stitch.nb t = 16 * (n / 256) := by
    show (t.gpr .r9).toNat = _; rw [G.r9, toNat_ofNat_of_lt (by omega)]
  refine WP.mono (Stitch.ctr_ok hp (by rw [hnb]; omega)) fun t' Cp => ?_
  have Fd : Frame [⟨W + BitVec.ofNat 64 96, 16⟩, ⟨D, 16 * (16 * (n / 256))⟩,
      ⟨W + BitVec.ofNat 64 1768, 256⟩] t.mem t'.mem := by
    have h := Cp.frame
    simp only [Stitch.cR, Stitch.dR, Stitch.pR, Stitch.cp, Stitch.dp, Stitch.pp, hnb, G.rdx, G.r12, G.r11] at h
    exact h
  refine hB.frame (hB.one.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Cp.gpr _ (by decide) (by decide) (by decide) (by decide)) Cp.rd Cp.wr)
    Fd (fun q hq => ?_) Cp.rd Cp.wr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact (hB.data.w.sub_left (Region.sub_prefix (by omega))).sub_right (Lay.wSub (by decide)) |>.symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)

/-- `cryptS`, in two runs with the same public arguments. -/
theorem cryptS_rel (v : GcmImpl) (eb : BlocksImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {R : Nat}
    (hR : R = 10 ∨ R = 14) {N A D : Addr} {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩)
    (hn : n ≤ 2 ^ 64) (h256 : 256 ≤ n) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → Bufs K W SP R N A D al n t₁ ∧ Bufs K W SP R N A D al n t₂) :
    RelCT isa P (Impl.AesGcmSiv.X86_64Stitch.cryptS v.callees ⟨eb.enc.name, eb.enc.code⟩ wide)
      fun _ _ => True := by
  have r₁ := (rel_taintC [] hDW hn (fun t₁ t₂ h => ⟨(hP _ _ h).1.one, (hP _ _ h).2.one, fun _ h => nomatch h⟩)
    sHead_check).wp
    (F₁ := Bufs K W SP R N A D al n) (F₂ := Bufs K W SP R N A D al n)
    fun t₁ t₂ h => ⟨WP.mono (sHead_wp L (hP _ _ h).1) fun _ h => h.2, WP.mono (sHead_wp L (hP _ _ h).2) fun _ h => h.2⟩
  have r₂ := (rel_taintC [] (P := fun t₁ t₂ => True ∧ Bufs K W SP R N A D al n t₁ ∧ Bufs K W SP R N A D al n t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.one, h.2.2.one, fun _ h => nomatch h⟩) sArgs_check).wp
    (F₁ := fun (t : State) => Bufs K W SP R N A D al n t ∧ ArgsAt W D R n t)
    (F₂ := fun (t : State) => Bufs K W SP R N A D al n t ∧ ArgsAt W D R n t)
    fun t₁ t₂ h => ⟨sArgs_wp h.2.1, sArgs_wp h.2.2⟩
  have r₃ := (rel_taintC [.rdi, .rsi, .rdx, .rcx, .r8, .r11, .r12, .r9] (P := fun t₁ t₂ => True ∧
      (Bufs K W SP R N A D al n t₁ ∧ ArgsAt W D R n t₁) ∧ (Bufs K W SP R N A D al n t₂ ∧ ArgsAt W D R n t₂))
    hDW hn (fun t₁ t₂ h => ArgsAt.both h.2.1 h.2.2) ctr_check).wp
    (F₁ := Bufs K W SP R N A D al n) (F₂ := Bufs K W SP R N A D al n)
    fun t₁ t₂ h => ⟨ctr_bufs L hR h256 h.2.1, ctr_bufs L hR h256 h.2.2⟩
  have r₄ := (rel_taintC [] (P := fun t₁ t₂ => True ∧ Bufs K W SP R N A D al n t₁ ∧ Bufs K W SP R N A D al n t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.one, h.2.2.one, fun _ h => nomatch h⟩) rest_check).wp
    (F₁ := fun (t : State) => Bufs K W SP R N A D al n t ∧
      t.gpr .r12 = D + BitVec.ofNat 64 (256 * (n / 256)) ∧ t.gpr .rbp = BitVec.ofNat 64 (n % 256))
    (F₂ := fun (t : State) => Bufs K W SP R N A D al n t ∧
      t.gpr .r12 = D + BitVec.ofNat 64 (256 * (n / 256)) ∧ t.gpr .rbp = BitVec.ofNat 64 (n % 256))
    fun t₁ t₂ h => ⟨rest_wp h.2.1, rest_wp h.2.2⟩
  have restIn : ∀ {t : State}, (Bufs K W SP R N A D al n t ∧
      t.gpr .r12 = D + BitVec.ofNat 64 (256 * (n / 256)) ∧ t.gpr .rbp = BitVec.ofNat 64 (n % 256)) →
      RestIn K W SP R N A D al n (16 * (n / 256)) t := fun h =>
    ⟨h.1.one, h.1.data, by rw [h.2.1, show 256 * (n / 256) = 16 * (16 * (n / 256)) by omega],
      by rw [h.2.2, show n % 256 = n - 16 * (16 * (n / 256)) by omega]⟩
  have r₅ := cryptRest_rel v eb wide L hR hDW hn (j₀ := 16 * (n / 256)) (by omega) (P := fun t₁ t₂ => True ∧
      (Bufs K W SP R N A D al n t₁ ∧ t₁.gpr .r12 = D + BitVec.ofNat 64 (256 * (n / 256)) ∧
        t₁.gpr .rbp = BitVec.ofNat 64 (n % 256)) ∧
      (Bufs K W SP R N A D al n t₂ ∧ t₂.gpr .r12 = D + BitVec.ofNat 64 (256 * (n / 256)) ∧
        t₂.gpr .rbp = BitVec.ofNat 64 (n % 256)))
    fun t₁ t₂ h => ⟨restIn h.2.1, restIn h.2.2⟩
  exact RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ (RelCT.seq r₄ r₅)))

/-! ## `vg_aes_gcm_siv_seal` -/

theorem lenCmp_st {K W SP : Addr} {R : Nat} {N A D T : Addr} {al n : Nat} {t : State}
    (h : St K W SP R N A D al n T t) :
    WP isa (.block [.mov .rax (.mem (Impl.AesGcm.X86_64.at_ .r15 lenO)), .alu .cmp .rax (imm 256)]) t fun t' =>
      St K W SP R N A D al n T t' ∧ t'.cf = some (decide (n < 256)) := by
  obtain ⟨t₁, run₁, hcf₁, hg₁, hm₁, hrd₁, hwr₁⟩ := lenCmp_ok h.bufs.one.env h.bufs.one.sl h.bufs.data.lt
  exact WP.of_runBlock ⟨t₁, run₁, h.frame (h.bufs.one.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide)) hrd₁ hwr₁) (by rw [hm₁]; exact Frame.refl [] _)
    (by simp) (by rw [hm₁]; exact Frame.refl _ _) hrd₁ hwr₁, hcf₁⟩

/-- POLYVAL and the tag input, either way, keep `St`. -/
theorem poly_st (v : GcmImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D T : Addr}
    {al n : Nat} {t : State} (h : StK K W SP R N A D al n T t ∧ t.cf = some (decide (n < 256))) :
    WP isa (.ite .b (polyval v.callees wide) (Impl.AesGcmSiv.X86_64Stitch.hashS v.callees wide)) t
      (St K W SP R N A D al n T) := by
  obtain ⟨h, hcf⟩ := h
  refine WP.ite (decide (n < 256)) (eval_b hcf) (fun _ => polyval_st v wide L h) (fun hf => ?_)
  exact WP.mono (hashS_ok v wide L h.1.bufs.one.env h.1.bufs.one.sl h.1.bufs.aad h.1.bufs.data h.1.nonce h.1.bufs.dw
    h.2.1 h.2.2 (by simpa using hf)) fun _ Po => h.1.frame Po.env Po.frame (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) ((Po.frame.sub (polyR_mutW W SP)).sub (mutW_mut W SP D n)) Po.rd Po.wr

/-- Counter mode, either way, keeps `St`. -/
theorem cry_st (v : GcmImpl) (eb : BlocksImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {R : Nat}
    (hR : R = 10 ∨ R = 14) {N A D T : Addr} {al n : Nat} {t : State}
    (h : St K W SP R N A D al n T t ∧ t.cf = some (decide (n < 256))) :
    WP isa (.ite .b (crypt v.callees ⟨eb.enc.name, eb.enc.code⟩ wide)
      (Impl.AesGcmSiv.X86_64Stitch.cryptS v.callees ⟨eb.enc.name, eb.enc.code⟩ wide)) t
      (St K W SP R N A D al n T) := by
  obtain ⟨h, hcf⟩ := h
  refine WP.ite (decide (n < 256)) (eval_b hcf) (fun _ => crypt_st0 v eb wide L hR h) (fun hf => ?_)
  exact WP.mono (cryptS_ok v eb wide L hR h.bufs.one.env h.bufs.one.sl h.bufs.data h.bufs.dw (by simpa using hf))
    fun _ Cr => h.frame Cr.env Cr.frame (slots_cryR L h.bufs.data) (Cr.frame.sub (cryR_mut W SP D n)) Cr.rd Cr.wr

/-- `seal` after its entry, up to the copy of the tag. -/
abbrev sealSFront (v : GcmImpl) (eb : BlocksImpl) (wide : Bool) : Prog isa :=
  .seq (.seq (.seq (.seq (.seq (keys v.callees ⟨eb.enc.name, eb.enc.code⟩) (.block Impl.AesGcmSiv.X86_64Stitch.lenCmp))
    (.ite .b (polyval v.callees wide) (Impl.AesGcmSiv.X86_64Stitch.hashS v.callees wide))) (tag v.callees tagO))
    (.block Impl.AesGcmSiv.X86_64Stitch.lenCmp))
    (.ite .b (crypt v.callees ⟨eb.enc.name, eb.enc.code⟩ wide)
      (Impl.AesGcmSiv.X86_64Stitch.cryptS v.callees ⟨eb.enc.name, eb.enc.code⟩ wide))

theorem sealSFront_st (v : GcmImpl) (eb : BlocksImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {R : Nat}
    (hR : R = 10 ∨ R = 14) {N A D T : Addr} {al n : Nat} {t : State} (h : St K W SP R N A D al n T t) :
    WP isa (sealSFront v eb wide) t (St K W SP R N A D al n T) :=
  WP.seq (WP.mono (WP.seq (WP.mono (WP.seq (WP.mono (WP.seq (WP.mono (WP.seq (WP.mono (keys_st v eb L hR h)
    fun _ h => lenCmp_stk h)) fun _ h => poly_st v wide L h)) fun _ h => tag_st v L hR (by decide) h))
    fun _ h => lenCmp_st h)) fun _ h => cry_st v eb wide L hR h)

/-- `sealSFront`, in two runs. -/
theorem sealSFront_rel (v : GcmImpl) (eb : BlocksImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {R : Nat}
    (hR : R = 10 ∨ R = 14) {N A D T : Addr} {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩)
    (hn : n ≤ 2 ^ 64) (hal : al < 2 ^ 64) (hn' : n < 2 ^ 64) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂) :
    RelCT isa P (sealSFront v eb wide) fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧
      St K W SP R N A D al n T t₂ := by
  have r₁ := (keys_rel v eb L hR hDW hn fun t₁ t₂ h => ⟨⟨(hP _ _ h).1.bufs.one, (hP _ _ h).1.nonce⟩,
      ⟨(hP _ _ h).2.bufs.one, (hP _ _ h).2.nonce⟩⟩).wp
    (F₁ := StK K W SP R N A D al n T) (F₂ := StK K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨keys_st v eb L hR (hP _ _ h).1, keys_st v eb L hR (hP _ _ h).2⟩
  have r₂ := (rel_taintC [] (P := fun t₁ t₂ => True ∧ StK K W SP R N A D al n T t₁ ∧
      StK K W SP R N A D al n T t₂) hDW hn (fun t₁ t₂ h => ⟨h.2.1.1.bufs.one, h.2.2.1.bufs.one, fun _ h => nomatch h⟩)
    lenCmp_check).wp
    (F₁ := fun (t : State) => StK K W SP R N A D al n T t ∧ t.cf = some (decide (n < 256)))
    (F₂ := fun (t : State) => StK K W SP R N A D al n T t ∧ t.cf = some (decide (n < 256)))
    fun t₁ t₂ h => ⟨lenCmp_stk h.2.1, lenCmp_stk h.2.2⟩
  have i₃ : RelCT isa (fun t₁ t₂ => True ∧ (StK K W SP R N A D al n T t₁ ∧ t₁.cf = some (decide (n < 256))) ∧
        (StK K W SP R N A D al n T t₂ ∧ t₂.cf = some (decide (n < 256))))
      (.ite .b (polyval v.callees wide) (Impl.AesGcmSiv.X86_64Stitch.hashS v.callees wide)) fun _ _ => True := by
    refine RelCT.ite (fun t₁ t₂ h => by rw [eval_b h.2.1.2, eval_b h.2.2.2]) ?_ ?_
    · exact polyval_rel v wide L hDW hn hal hn' fun t₁ t₂ h => ⟨h.1.2.1.1.1.bufs, h.1.2.2.1.1.bufs⟩
    · by_cases hn256 : 256 ≤ n
      · exact hashS_rel v wide L hDW hn hal hn' hn256 fun t₁ t₂ h => ⟨h.1.2.1.1.1.bufs, h.1.2.2.1.1.bufs⟩
      · refine RelCT.of_false fun _ _ h => hn256 ?_
        have := h.2; rw [eval_b h.1.2.1.2] at this; simp at this; omega
  have r₃ := i₃.wp (F₁ := St K W SP R N A D al n T) (F₂ := St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨poly_st v wide L h.2.1, poly_st v wide L h.2.2⟩
  have r₄ := (tag_rel v L hR hDW hn (o := tagO) (by decide) (P := fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧
      St K W SP R N A D al n T t₂) fun t₁ t₂ h => ⟨h.2.1.bufs.one, h.2.2.bufs.one, fun _ h => nomatch h⟩).wp
    (F₁ := St K W SP R N A D al n T) (F₂ := St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨tag_st v L hR (by decide) h.2.1, tag_st v L hR (by decide) h.2.2⟩
  have r₅ := (rel_taintC [] (P := fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧
      St K W SP R N A D al n T t₂) hDW hn (fun t₁ t₂ h => ⟨h.2.1.bufs.one, h.2.2.bufs.one, fun _ h => nomatch h⟩)
    lenCmp_check).wp
    (F₁ := fun (t : State) => St K W SP R N A D al n T t ∧ t.cf = some (decide (n < 256)))
    (F₂ := fun (t : State) => St K W SP R N A D al n T t ∧ t.cf = some (decide (n < 256)))
    fun t₁ t₂ h => ⟨lenCmp_st h.2.1, lenCmp_st h.2.2⟩
  have i₆ : RelCT isa (fun t₁ t₂ => True ∧ (St K W SP R N A D al n T t₁ ∧ t₁.cf = some (decide (n < 256))) ∧
        (St K W SP R N A D al n T t₂ ∧ t₂.cf = some (decide (n < 256))))
      (.ite .b (crypt v.callees ⟨eb.enc.name, eb.enc.code⟩ wide)
        (Impl.AesGcmSiv.X86_64Stitch.cryptS v.callees ⟨eb.enc.name, eb.enc.code⟩ wide)) fun _ _ => True := by
    refine RelCT.ite (fun t₁ t₂ h => by rw [eval_b h.2.1.2, eval_b h.2.2.2]) ?_ ?_
    · exact crypt_rel v eb wide L hR hDW hn fun t₁ t₂ h => ⟨⟨h.1.2.1.1.bufs.one, h.1.2.1.1.bufs.data⟩,
        ⟨h.1.2.2.1.bufs.one, h.1.2.2.1.bufs.data⟩⟩
    · by_cases hn256 : 256 ≤ n
      · exact cryptS_rel v eb wide L hR hDW hn hn256 fun t₁ t₂ h => ⟨h.1.2.1.1.bufs, h.1.2.2.1.bufs⟩
      · refine RelCT.of_false fun _ _ h => hn256 ?_
        have := h.2; rw [eval_b h.1.2.1.2] at this; simp at this; omega
  have r₆ := i₆.wp (F₁ := St K W SP R N A D al n T) (F₂ := St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨cry_st v eb wide L hR h.2.1, cry_st v eb wide L hR h.2.2⟩
  exact (RelCT.seq (RelCT.seq (RelCT.seq (RelCT.seq (RelCT.seq r₁ r₂) r₃) r₄) r₅) r₆).mono (fun _ _ h => h)
    fun _ _ h => ⟨trivial, h.2⟩

/-- `vg_aes_gcm_siv_seal`, in two runs with the same public arguments. -/
theorem sealS_rel (v : GcmImpl) (eb : BlocksImpl) (wide : Bool) {s₀ s₀' : State} (hp : sealPre s₀)
    (hp' : sealPre s₀') (hq : onePub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (Impl.AesGcmSiv.X86_64Stitch.«seal» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide)
      fun _ _ => True := by
  have Ar := (args_of_seal hp).1.1
  have L := Ar.lay
  refine RelCT.seq (entry_rel (pub_regs hq) (hq.2.2.2.2.2.2.2 2 (by decide)) (argW_in Ar rfl)
    (argW_in (args_of_seal hp').1.1 rfl) (entry_seal hp) (entry_seal_pub hp' hq)) ?_
  refine RelCT.assoc (RelCT.assoc (RelCT.assoc (RelCT.assoc (RelCT.assoc ?_))))
  have hn := Nat.le_of_lt Ar.data.lt
  have front := rel_narrow (c := sealSFront v eb wide)
    (P := fun s₁ s₂ => True ∧
      SealIn (s₀.gpr .rdi) (arg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9)
        (s₀.gpr .r8).toNat (arg s₀ 0).toNat (arg s₀ 1) s₁ ∧
      SealIn (s₀.gpr .rdi) (arg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9)
        (s₀.gpr .r8).toNat (arg s₀ 0).toNat (arg s₀ 1) s₂)
    [⟨arg s₀ 1, 16⟩] [⟨s₀.gpr .r9, (arg s₀ 0).toNat⟩, ⟨arg s₀ 2, 3816⟩]
    (sealSFront_rel v eb wide L Ar.rounds Ar.data.w hn Ar.aad.lt Ar.data.lt
      fun _ _ h => by obtain ⟨_, _, hp, rfl, rfl⟩ := h; exact ⟨hp.2.1.2, hp.2.2.2⟩)
    fun s₁ s₂ h => by
      have hc : ∀ {s : State}, s.wr = [⟨s₀.gpr .r9, (arg s₀ 0).toNat⟩, ⟨arg s₀ 1, 16⟩, ⟨arg s₀ 2, 3816⟩] →
          Covers ([⟨arg s₀ 1, 16⟩] ++ [⟨s₀.gpr .r9, (arg s₀ 0).toNat⟩, ⟨arg s₀ 2, 3816⟩]) s.wr ∧
          Covers [⟨s₀.gpr .r9, (arg s₀ 0).toNat⟩, ⟨arg s₀ 2, 3816⟩] s.wr := fun hw => by
        rw [hw]
        refine ⟨Covers.of_mem fun r hr => ?_, Covers.of_mem fun r hr => ?_⟩ <;>
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢ <;>
          rcases hr with h | h | h <;> simp [h]
      obtain ⟨_, ⟨hw₁, p₁⟩, ⟨hw₂, p₂⟩⟩ := h
      obtain ⟨t₁, u₁, e₁, -⟩ := sealSFront_st v eb wide L Ar.rounds p₁
      obtain ⟨t₂, u₂, e₂, -⟩ := sealSFront_st v eb wide L Ar.rounds p₂
      exact ⟨⟨(hc hw₁).1, (hc hw₁).2, t₁, u₁, e₁⟩, ⟨(hc hw₂).1, (hc hw₂).2, t₂, u₂, e₂⟩⟩
  exact RelCT.seq front (rel_loadT (l := tagOut.tail ++ restore) (fun _ _ h => by
    obtain ⟨_, _, ⟨-, m₁, m₂⟩, ⟨g₁, h₁, c₁⟩, ⟨g₂, h₂, c₂⟩⟩ := h
    exact ⟨m₁.tagIn g₁ h₁ c₁, m₂.tagIn g₂ h₂ c₂⟩) tagOut_check)

end VG.Proof.AesGcmSiv.X86_64
