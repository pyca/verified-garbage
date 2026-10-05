import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTPieces
import VerifiedGarbage.Proof.Rsa.X86_64.KeyMain

/-!
# `vg_rsa_check_key` on x86-64: constant time of the setup

From `main`'s hypotheses (`M0`), the setup leaves the checks' context
(`KK`). Its pieces load from the header and from `n`, so each runs from
the registers that correctness pins after the one before: `setup_nested`
states them, piece by piece, and `setupK_ct` follows it.
-/

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask sN sK)

/-- The public data of `main`: the checks', `n`'s pointer and its length. -/
structure MPub where
  kp : KPub
  np : Addr
  k : Nat

/-- `main`'s hypotheses, with the public data `a`. -/
def M0 (a : MPub) (s : State) : Prop :=
  ∃ nb db pb qb dpb dqb qib ev, MainPre s a.kp.B a.kp.Z a.k a.np a.kp.pd a.kp.pp a.kp.pq a.kp.pdp a.kp.pdq
    a.kp.pqi nb db pb qb dpb dqb qib ev ∧ a.kp.w = (a.k + 7) / 8 ∧ db.length = a.kp.dl ∧ pb.length = a.kp.pl ∧
    qb.length = a.kp.ql

/-- The setup's last piece. -/
abbrev maskInit : List Instr := [.mov32 .rax (.imm 0), .alu .sub .rax (.imm 1), .store (hdr sMask) .rax]

/-- Before the last piece. -/
def S4 (a : MPub) (t : State) : Prop := t.gpr .rdi = a.kp.B ∧ WP isa (.block maskInit) t (KK a.kp)

/-- Before `setWord`. -/
def S3 (a : MPub) (t : State) : Prop :=
  RegsAre [(.rdi, a.kp.B), (.r12, BitVec.ofNat 64 a.kp.w), (.rcx, BitVec.ofNat 64 0)] t ∧
    WP isa (.block [.mov .r8 (.mem (hdr (sArr aOne)))]) t (RegsAre [(.r8, kb a.kp aOne)]) ∧
    WP isa (setWord aOne .rcx) t (S4 a)

/-- Before the constants. -/
def S2 (a : MPub) (t : State) : Prop := WP isa (.block [.mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)]) t (S3 a)

/-- Before `n`'s load. -/
def S1 (a : MPub) (t : State) : Prop :=
  RegsAre [(.rsi, a.np), (.rcx, BitVec.ofNat 64 a.k), (.rbx, kb a.kp aN)] t ∧ WP isa loadBE t (S2 a)

theorem setup_nested {a : MPub} {s : State} (h : M0 a s) : WP isa (.block VG.Impl.Rsa.X86_64.head) s (S1 a) := by
  obtain ⟨nb, db, pb, qb, dpb, dqb, qib, ev, hp, hw, hdl, hpl, hql⟩ := h
  obtain ⟨⟨B, Z, w, pd, pp, pq, pdp, pdq, pqi, dl, pl, ql⟩, np, k⟩ := a
  simp only at hp hw hdl hpl hql ⊢
  subst hw hdl hpl hql
  have hs := hp.scr
  have hn := hs.nowrap
  have := hp.k1
  have := hp.k2
  have := hp.dl2
  have := hp.pl2
  have := hp.ql2
  have hZ : slot ((k + 7) / 8) 8 ≤ Z := by have := hp.zk; unfold slot hdrBytes; omega
  have h8 := hdr_lt_slot ((k + 7) / 8) 0 (show 31 < 32 by decide)
  have h0 := slot_le (w := (k + 7) / 8) (show 0 < 8 by decide)
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have eM : sMask = 22 := rfl
  have eI : sMinv = 7 := rfl
  have e1 : sArr aOne = 15 := rfl
  have hsl : ∀ r ∈ [(8 * sW, 8), (8 * sArr 0, 64)], r.1 + r.2 ≤ Z := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl) <;> simp only [eW, eA] <;> omega
  have hfw : ∀ i, i ≠ 6 → (i < 8 ∨ 16 ≤ i) → ∀ r ∈ [(8 * sW, 8), (8 * sArr 0, 64)],
      8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i := by
    intro i h6 hr
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl) <;> simp only [eW, eA] <;> omega
  refine WP.mono (setupHead_ok hs hp.rdi hZ (by omega) hp.hK hp.hN)
    fun t₁ ⟨h12, hcx, hsi, hbx, hW₁, hb₁, hf₁, k₁⟩ => ⟨regsAre_cons hsi (regsAre_cons hcx (regsAre_cons hbx
      regsAre_nil)), ?_⟩
  have hs₁ := hs.congr k₁.2.2
  have in₁ : InScr B Z s.mem t₁.mem := InScr.of_frm hf₁ hsl
  refine WP.mono (loadArr_ok hs₁ (j := aN) (by decide) hZ (hp.srN.congrK in₁ k₁) hp.nl (by omega)
    (by omega) hsi hcx hbx) fun t₂ ⟨hv₂, ha₂, k₂⟩ => ?_
  have hs₂ := hs₁.congr k₂.2.2
  have hdi₂ : t₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hp.rdi)
  refine WP.mono (WP.keep [.rdx, .rcx] (Q := fun t => t.gpr .rdx = 1 ∧
      t.gpr .rcx = BitVec.ofNat 64 0 ∧ t.mem = t₂.mem) (by xrun []) rfl)
    fun t₃ ⟨⟨hdx₃, hcx₃, hm₃⟩, k₃⟩ => ?_
  have hH : Hdr t₃.mem B ((k + 7) / 8) (word s.mem B (8 * sMinv)) :=
    ⟨by rw [hm₃, ha₂.hslot (by decide)]; exact hW₁,
      by rw [hm₃, ha₂.hslot (by decide), hf₁.word_eq (hfw sMinv (by decide) (by decide)) (by omega)],
      fun j hj => by rw [hm₃, ha₂.hslot (by unfold sArr; omega)]; exact hb₁ j hj⟩
  have hs₃ := hs₂.congr k₃.2.2
  have h12₃ : t₃.gpr .r12 = BitVec.ofNat 64 ((k + 7) / 8) :=
    (k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12)
  have hdi₃ : t₃.gpr .rdi = B := (k₃.gpr (by decide)).trans hdi₂
  refine ⟨regsAre_cons hdi₃ (regsAre_cons h12₃ (regsAre_cons hcx₃ regsAre_nil)),
    WP.mono (WP.keep [.r8] (Q := fun t => t.gpr .r8 = off B (slot ((k + 7) / 8) aOne)) (by
      xrun [State.ea, hdr, hdi₃, hdrOff, hs₃.ld (d := 8 * sArr aOne) (by rw [e1]; omega),
        hH.harr aOne (by decide)]) rfl) fun t ⟨h8', _⟩ => regsAre_cons h8' regsAre_nil, ?_⟩
  refine WP.mono (setWord_ok hs₃ hdi₃ hH hZ h12₃ (by omega) (by omega) (o := aOne) (by decide)
    (ri := .rcx) (by decide) (i := 0) (by omega) hcx₃) fun t₄ ⟨hone, ho₄, k₄⟩ => ?_
  have hs₄ := hs₃.congr k₄.2.2
  have hdi₄ : t₄.gpr .rdi = B := (k₄.gpr (by decide)).trans hdi₃
  refine ⟨hdi₄, WP.mono (WP.keep [.rax] (Q := fun t => t.mem = t₄.mem.writeW (off B (8 * sMask)) (mask true)) (by
    xrun [State.ea, hdr, hdi₄, hdrOff, hs₄.st (d := 8 * sMask) (by omega)]
    exact congrArg _ (by decide)) rfl) fun t ⟨hm, k₅⟩ => ?_⟩
  have ha₄ : Arrays B ((k + 7) / 8) [aOne] t₃.mem t₄.mem :=
    Arrays.of_outside (List.mem_singleton_self _) ho₄ (Nat.le_refl _) (Nat.le_refl _)
  have hn' : B.toNat + slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega
  have ho₅ : Outside B (8 * sMask) 8 t₄.mem t.mem := by rw [hm]; exact writeW_outside _ B _ (by omega)
  have kk : Keep mmRegs s t := ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by decide)
  have hin : InScr B Z s.mem t.mem :=
    ((in₁.trans (InScr.of_arrays ha₂ hZ (by decide))).trans (by rw [hm₃]; exact InScr.refl _ _ _)).trans
      ((InScr.of_arrays ha₄ hZ (by decide)).trans (InScr.of_outside ho₅ (by omega)))
  have hh : ∀ i < 32, setupSlot i = false → word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi hsi => by
    obtain ⟨h6, hr, h22⟩ := setupSlot_false i hi hsi
    rw [hm, hdrStore_hdr _ _ _ (by decide) hi (by rw [eM]; omega), ha₄.hslot hi, hm₃, ha₂.hslot hi,
      hf₁.word_eq (hfw i h6 hr) (by omega)]
  have sr : ∀ {p : Addr} {bs : List Byte}, Src s B Z p bs → Src t B Z p bs := fun h => h.congr hin kk.2.1 kk.2.2
  refine ⟨t, word s.mem B (8 * sMinv), Spec.Rsa.os2ip nb, ⟨⟨hs₄.congr k₅.2.2, (k₅.gpr (by decide)).trans hdi₄,
      by rw [hm]; exact Hdr.store (ha₄.hdr hH) (i := sMask) (by decide) (by decide) _⟩,
    hZ, by dsimp only; omega, by dsimp only; omega, fun _ _ _ => rfl, InScr.refl _ _ _, rfl, rfl, ?_, ?_,
    Keep.refl _ _⟩,
    { hD := by rw [hh sD (by decide) (by decide)]; exact hp.hD
      hDl := by rw [hh sDlen (by decide) (by decide)]; exact hp.hDl
      hP := by rw [hh sP (by decide) (by decide)]; exact hp.hP
      hPl := by rw [hh sPlen (by decide) (by decide)]; exact hp.hPl
      hQ := by rw [hh sQ (by decide) (by decide)]; exact hp.hQ
      hQl := by rw [hh sQlen (by decide) (by decide)]; exact hp.hQl
      hDP := by rw [hh sDP (by decide) (by decide)]; exact hp.hDP
      hDQ := by rw [hh sDQ (by decide) (by decide)]; exact hp.hDQ
      hQI := by rw [hh sQI (by decide) (by decide)]; exact hp.hQI
      srD := ⟨db, sr hp.srD, rfl⟩
      srP := ⟨pb, sr hp.srP, rfl⟩
      srQ := ⟨qb, sr hp.srQ, rfl⟩
      srDP := ⟨dpb, sr hp.srDP, hp.dpl⟩
      srDQ := ⟨dqb, sr hp.srDQ, hp.dql⟩
      srQI := ⟨qib, sr hp.srQI, hp.qil⟩
      dl1 := hp.dl1
      dl2 := by dsimp only; omega
      pl1 := hp.pl1
      pl2 := by dsimp only; omega
      ql1 := hp.ql1
      ql2 := by dsimp only; omega }⟩
  · rw [Outside.wv_arr ho₅ (by decide) hZ hn (by dsimp only; omega), ha₄.wv_of_not_mem (by decide) (by decide) hn', hm₃]
    exact hv₂
  · rw [Outside.wv_arr ho₅ (by decide) hZ hn (by dsimp only; omega), hone, hdx₃]; rfl

theorem pins_regsAre {α : Type} {Φ : α → State → Prop} (vs : α → List (Reg × BitVec 64)) {rs : List Reg}
    (hrs : ∀ a, (vs a).map Prod.fst = rs) (h : ∀ a s, Φ a s → RegsAre (vs a) s) : Pins Φ rs :=
  fun a s₁ s₂ h₁ h₂ => pins_regs vs hrs a s₁ s₂ (h a s₁ h₁) (h a s₂ h₂)

/-- The setup is constant time from `M0`, and leaves `KK`. -/
theorem setupK_ct : RelCT isa (Two M0) (seqs [.block VG.Impl.Rsa.X86_64.head, loadBE,
    .block [.mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)], setWord aOne .rcx, .block maskInit])
    (Two fun (a : MPub) t => KK a.kp t) := by
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := S1) [.rdi] (pins_of (fun (a : MPub) _ => a.kp.B) fun a s h r hr => by
      obtain ⟨_, _, _, _, _, _, _, _, hp, -⟩ := h
      simp only [List.mem_singleton] at hr; subst hr; exact hp.rdi) (by taint_decide)
    fun _ _ h => setup_nested h) ?_
  refine RelCT.seq (two_post (two_taint [.rsi, .rcx, .rbx]
    (pins_regsAre (fun a => [(.rsi, a.np), (.rcx, BitVec.ofNat 64 a.k), (.rbx, kb a.kp aN)]) (fun _ => rfl)
      fun _ _ h => h.1) (by taint_decide)) fun _ _ h => h.2) ?_
  refine RelCT.seq (two_post (two_taint [] (fun _ _ _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide))
    fun _ _ h => h) ?_
  refine RelCT.seq (two_post ?_ fun _ _ h => h.2.2) ?_
  · unfold setWord
    refine RelCT.seq (two_piece (Ψ := fun a t => RegsAre [(.r8, kb a.kp aOne), (.r12, BitVec.ofNat 64 a.kp.w),
        (.rcx, BitVec.ofNat 64 0)] t) [.rdi]
      (pins_of (fun a _ => a.kp.B) fun _ _ h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.1 (.rdi, _) (List.mem_cons_self ..))
      (by taint_decide) fun a t h => ?_)
      (two_taint [.r8, .r12, .rcx] (pins_regsAre (fun a => [(.r8, kb a.kp aOne), (.r12, BitVec.ofNat 64 a.kp.w),
        (.rcx, BitVec.ofNat 64 0)]) (fun _ => rfl) fun _ _ h => h) (by taint_decide))
    exact WP.mono (WP.keep [.r8] h.2.1 rfl) fun t' ⟨h8, k⟩ => regsAre_cons (h8 (.r8, kb a.kp aOne) (by simp))
      (regsAre_cons ((k.gpr (by decide)).trans (h.1 (.r12, BitVec.ofNat 64 a.kp.w) (by simp)))
        (regsAre_cons ((k.gpr (by decide)).trans (h.1 (.rcx, BitVec.ofNat 64 0) (by simp))) regsAre_nil))
  · exact two_post (two_taint [.rdi] (pins_of (fun a _ => a.kp.B) fun _ _ h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.1) (by taint_decide)) fun _ _ h => h.2

end VG.Proof.Rsa.X86_64.Key
