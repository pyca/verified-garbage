module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeMul
meta import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeMul
import VerifiedGarbage.Proof.Framework.Omega

/-! # The trace of the exponentiation, in public RSA at a run-time width

Its pieces between calls are checked by the taint analysis (`τA`), its
multiplications related by `mul_relCT`; what each needs of a run (`St`:
`Env`, the base and one below the modulus, the count in `esi`) each keeps
(`mask_st`, `mulKeep_ok`, …), so the runs of a step (`expStep_relCT`), of the
loop of 64 (`expLoop_relCT`) and of the exponentiation
(`exponentiate_relCT`) leak the same traces.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Mont.X86.Dynamic

/-- Two runs, each meeting `F`. -/
abbrev Both (F : State → Prop) (s t : State) : Prop := F s ∧ F t

theorem relCT_both {P F : State → Prop} {c : Prog isa} (hct : RelCT isa (Both P) c fun _ _ => True)
    (hw : ∀ s, P s → WP isa c s F) : RelCT isa (Both P) c (Both F) :=
  (hct.wp (F₁ := F) (F₂ := F) fun s t h => ⟨hw s h.1, hw t h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

theorem taint_both {P F : State → Prop} {c : Prog isa} (hag : ∀ s t, P s → P t → VG.X86.Taint.Agree τA s t)
    (hc : VG.Taint.Hint VG.X86.Taint.T) (hT : (VG.Taint.check taint τA c hc).isSome = true)
    (hw : ∀ s, P s → WP isa c s F) : RelCT isa (Both P) c (Both F) :=
  relCT_both (RelCT.taint (A := taint) τA (fun s t h => hag s t h.1 h.2) hT) hw

section
variable {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- What the exponentiation keeps of a run: `Env` with the modulus `M`, the arguments apart, `esp`, the
base (number 1) and one (number 3) below `M`, and the count `k` in `esi`. -/
def St (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (M k : Nat) (s : State) : Prop :=
  Env base bytes len args M s ∧ ArgsOk s ∧ s.gpr .esp = sp ∧
    val32 s.mem base (numAt len 1) (nw len) < M ∧ val32 s.mem base (numAt len 3) (nw len) < M ∧
    s.gpr .esi = BitVec.ofNat 32 k

theorem St.agree {sp : BitVec 32} {M₁ M₂ k₁ k₂ : Nat} {s t : State} (S₁ : St base bytes len args sp M₁ k₁ s)
    (S₂ : St base bytes len args sp M₂ k₂ t) : VG.X86.Taint.Agree τA s t :=
  agreeA S₁.1.pi S₂.1.pi S₁.2.1 S₂.2.1 (S₁.2.2.1.trans S₂.2.2.1.symm)

/-- A multiplication in `Env`: what it keeps. -/
theorem mulKeep_ok {s : State} {M : Nat} (E : Env base bytes len args M s) (A : ArgsOk s)
    (hbytes : bytes = (args 9).toNat * 8) {o a b : Nat} (ho : 1 ≤ o) (ho4 : o ≤ 4) (ha : a ≤ 4) (hb : b ≤ 4)
    (hB : val32 s.mem base (numAt len b) (nw len) < M) :
    WP isa (PublicRt.mul o a b) s fun u =>
      Env base bytes len args M u ∧ ArgsOk u ∧ Keeps [.eax, .ecx, .edx] s u ∧
      val32 u.mem base (numAt len o) (nw len) < M ∧
      (∀ j ≤ 4, j ≠ o → val32 u.mem base (numAt len j) (nw len) = val32 s.mem base (numAt len j) (nw len)) ∧
      u.mem.readW (off base 136) 32 = s.mem.readW (off base 136) 32 := by
  have h := E.pi
  have nw' := h.scratch.nowrap
  have wbe := wb_eq len
  have f5 := (h.fits (j := 5) (by decide)).2
  have fo := (h.fits (j := o) (by omega)).1
  have n0 : numOff = 256 := rfl
  refine WP.mono (mulRaw_ok E hbytes ho ho4 ha hb hB) fun u ⟨Eu, _, K, F, L, _⟩ =>
    ⟨Eu, A.keep K (by decide), K, L, fun j hj hjo => ?_, ?_⟩
  · have h5 : numAt len j + 4 * nw len ≤ numAt len 5 := by
      have := Nat.mul_le_mul_right (wb len) (show j + 1 ≤ 5 by omega)
      simp only [numAt]; rw [Nat.add_mul, Nat.one_mul] at this; omega
    refine mulFrame_val32 E.room nw' F ?_ h5 (by omega) fo f5
    rcases Nat.lt_or_gt_of_ne hjo with hl | hl
    · left
      have := Nat.mul_le_mul_right (wb len) (show j + 1 ≤ o by omega)
      simp only [numAt] at this ⊢; rw [← wbe]; rw [Nat.add_mul, Nat.one_mul] at this; omega
    · right
      have := Nat.mul_le_mul_right (wb len) (show o + 1 ≤ j by omega)
      simp only [numAt] at this ⊢; rw [Nat.add_mul, Nat.one_mul] at this; omega
  · have f0 := (h.fits (j := 0) (by decide)).1
    simp only [numAt, numOff] at f0
    simp only [Mem.readW]
    rw [mulFrame_hdr E.room nw' F (by decide) (by omega) fo f5]

variable (sp : BitVec 32)

theorem mask_st {M k : Nat} {s : State} (S : St base bytes len args sp M k s) :
    WP isa (.block (VG.Impl.Mont.X86.Dynamic.exponentMask PublicContext.exponentOffset PublicContext.maskOffset)) s fun u =>
      St base bytes len args sp M k u ∧ ∃ c, u.mem.readW (off base 136) 32 = cmask c := by
  obtain ⟨E, A, sp₀, X, O, c₀⟩ := S
  have h := E.pi
  have nw' := h.scratch.nowrap
  have wbe := wb_eq len
  have f5 := (h.fits (j := 5) (by decide)).2
  have e1 : numAt len 1 = 256 + wb len := by simp only [numAt, numOff] <;> omega
  have e3 : numAt len 3 = 256 + 3 * wb len := by simp only [numAt, numOff] <;> omega
  have e5 : numAt len 5 = 256 + 5 * wb len := by simp only [numAt, numOff] <;> omega
  refine WP.mono (exponentMask_ok h.scratch (exp := 128) (mask := 136) (by omega) (by omega))
    fun u ⟨O₁, M₁, K₁⟩ => ⟨⟨E.keep K₁ (by decide) (by decide) (Outside.chg O₁ (.inl ⟨by decide, by decide⟩)),
      A.keep K₁ (by decide), (K₁.1 _ (by decide)).trans sp₀,
      by rw [O₁.val32 (.inr (by omega)) (by omega)]; exact X, by rw [O₁.val32 (.inr (by omega)) (by omega)]; exact O,
      (K₁.1 _ (by decide)).trans c₀⟩, decide (w32 s.mem base 128 % 2 = 1), ?_⟩
  rw [M₁]
  by_cases hp : w32 s.mem base 128 % 2 = 1 <;> simp [hp, cmask]

theorem mul421_st (hbytes : bytes = (args 9).toNat * 8) {M k : Nat} {s : State} (S : St base bytes len args sp M k s)
    (hm : ∃ c, s.mem.readW (off base 136) 32 = cmask c) :
    WP isa (PublicRt.mul 4 2 1) s fun u =>
      St base bytes len args sp M k u ∧ ∃ c, u.mem.readW (off base 136) 32 = cmask c := by
  obtain ⟨E, A, sp₀, X, O, c₀⟩ := S
  refine WP.mono (mulKeep_ok E A hbytes (o := 4) (a := 2) (b := 1) (by decide) (by decide) (by decide)
    (by decide) X) fun u ⟨Eu, Au, K, _, V, m⟩ => ⟨⟨Eu, Au, (K.1 _ (by decide)).trans sp₀,
      by rw [V 1 (by decide) (by decide)]; exact X, by rw [V 3 (by decide) (by decide)]; exact O,
      (K.1 _ (by decide)).trans c₀⟩, by rw [m]; exact hm⟩

theorem mov_st {M k : Nat} {s : State} (S : St base bytes len args sp M k s)
    (hm : ∃ c, s.mem.readW (off base 136) 32 = cmask c) :
    WP isa (.block [.mov .ecx (.mem (sc PublicContext.maskOffset))]) s fun u =>
      St base bytes len args sp M k u ∧ ∃ c, u.gpr .ecx = cmask c := by
  obtain ⟨E, A, sp₀, X, O, c₀⟩ := S
  have h := E.pi
  have f0 := (h.fits (j := 0) (by decide)).1
  simp only [numAt, numOff] at f0
  refine wp_movS (readSrc_sc h.scratch (d := 136) (by omega)) fun u e _ => WP.block_nil ?_
  obtain ⟨c, hc⟩ := hm
  exact ⟨⟨E.keep e.keeps (by decide) (by decide) (by rw [e.mem]; exact Frame.refl _ _), A.keep e.keeps (by decide),
    (e.other _ (by decide)).trans sp₀, by rw [e.mem]; exact X, by rw [e.mem]; exact O,
    (e.other _ (by decide)).trans c₀⟩, c, by rw [e.gpr]; exact hc⟩

theorem select_st (hbase : (args 8).toNat = base.toNat) {M k : Nat} {s : State} (S : St base bytes len args sp M k s)
    (hm : ∃ c, s.gpr .ecx = cmask c) :
    WP isa (select 4 2) s (St base bytes len args sp M k) := by
  obtain ⟨E, A, sp₀, X, O, c₀⟩ := S
  obtain ⟨c, hc⟩ := hm
  have h := E.pi
  have nw' := h.scratch.nowrap
  have wbe := wb_eq len
  have f5 := (h.fits (j := 5) (by decide)).2
  have e1 : numAt len 1 = 256 + wb len := by simp only [numAt, numOff] <;> omega
  have e2 : numAt len 2 = 256 + 2 * wb len := by simp only [numAt, numOff] <;> omega
  have e3 : numAt len 3 = 256 + 3 * wb len := by simp only [numAt, numOff] <;> omega
  have e5 : numAt len 5 = 256 + 5 * wb len := by simp only [numAt, numOff] <;> omega
  refine WP.mono (select_ok h hbase (x := 4) (d := 2) (by decide) (by decide) (by decide) hc)
    fun u ⟨O₄, _, edi₄, K₄⟩ => ?_
  have K := Keeps.drop_edi (rs := [.eax, .ebx, .edx, .ebp]) K₄ edi₄
  exact ⟨E.keep K (by decide) (by decide) (Outside.chg O₄ (.inr ⟨by omega, by omega⟩)), A.keep K (by decide),
    (K.1 _ (by decide)).trans sp₀, by rw [O₄.val32 (.inl (by omega)) (by omega)]; exact X,
    by rw [O₄.val32 (.inr (by omega)) (by omega)]; exact O, (K.1 _ (by decide)).trans c₀⟩

theorem mul111_st (hbytes : bytes = (args 9).toNat * 8) {M k : Nat} {s : State} (S : St base bytes len args sp M k s) :
    WP isa (PublicRt.mul 1 1 1) s (St base bytes len args sp M k) := by
  obtain ⟨E, A, sp₀, X, O, c₀⟩ := S
  exact WP.mono (mulKeep_ok E A hbytes (o := 1) (a := 1) (b := 1) (by decide) (by decide) (by decide)
    (by decide) X) fun u ⟨Eu, Au, K, L, V, _⟩ => ⟨Eu, Au, (K.1 _ (by decide)).trans sp₀, L,
      by rw [V 3 (by decide) (by decide)]; exact O, (K.1 _ (by decide)).trans c₀⟩

theorem last_st {M k : Nat} {s : State} (hk : 0 < k) (hk32 : k < 2 ^ 32) (S : St base bytes len args sp M k s) :
    WP isa (.block (VG.Impl.Mont.X86.Dynamic.shiftExponent 2 PublicContext.exponentOffset ++ ([.alu .sub .esi (.imm 1)] : List Instr))) s fun u =>
      St base bytes len args sp M (k - 1) u ∧ u.zf = some (decide (k = 1)) := by
  obtain ⟨E, A, sp₀, X, O, c₀⟩ := S
  have h := E.pi
  have nw' := h.scratch.nowrap
  have wbe := wb_eq len
  have f5 := (h.fits (j := 5) (by decide)).2
  have e1 : numAt len 1 = 256 + wb len := by simp only [numAt, numOff] <;> omega
  have e3 : numAt len 3 = 256 + 3 * wb len := by simp only [numAt, numOff] <;> omega
  have e5 : numAt len 5 = 256 + 5 * wb len := by simp only [numAt, numOff] <;> omega
  refine WP.block_append (WP.mono (shiftExponent_ok h.scratch 2 128 (by omega)) fun u₆ ⟨O₆, _, K₆⟩ => ?_)
  refine wp_subZ rfl fun t e₇ z₇ => WP.block_nil ?_
  have E₆ := E.keep K₆ (by decide) (by decide) (Outside.chg O₆ (.inl ⟨by decide, by decide⟩))
  have esi₆ : u₆.gpr .esi = BitVec.ofNat 32 k := (K₆.1 _ (by decide)).trans c₀
  refine ⟨⟨E₆.keep e₇.keeps (by decide) (by decide) (by rw [e₇.mem]; exact Frame.refl _ _),
    (A.keep K₆ (by decide)).keep e₇.keeps (by decide), (e₇.other _ (by decide)).trans ((K₆.1 _ (by decide)).trans sp₀),
    by rw [e₇.mem, O₆.val32 (.inr (by omega)) (by omega)]; exact X,
    by rw [e₇.mem, O₆.val32 (.inr (by omega)) (by omega)]; exact O, ?_⟩, ?_⟩
  · rw [e₇.gpr, esi₆, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
  · rw [z₇, esi₆, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by omega)]
    simp only [show k - 1 = 0 ↔ k = 1 by omega]

theorem expStep_relCT (hbase : (args 8).toNat = base.toNat) (hbytes : bytes = (args 9).toNat * 8) {k : Nat} (hk : 0 < k) (hk32 : k < 2 ^ 32) :
    RelCT isa (Both fun s => ∃ M, St base bytes len args sp M k s) expStep
      (Both fun s => (∃ M, St base bytes len args sp M (k - 1) s) ∧ s.zf = some (decide (k = 1))) := by
  unfold expStep
  refine VG.RelCT.seq (taint_both (F := fun s => ∃ M, St base bytes len args sp M k s ∧
      ∃ c, s.mem.readW (off base 136) 32 = cmask c) (fun _ _ ⟨_, S₁⟩ ⟨_, S₂⟩ => S₁.agree S₂) (.block [])
    (by taint_decide) fun _ ⟨M, S⟩ => WP.mono (mask_st sp S) fun _ h => ⟨M, h⟩) ?_
  refine VG.RelCT.seq (relCT_both (F := fun s => ∃ M, St base bytes len args sp M k s ∧
      ∃ c, s.mem.readW (off base 136) 32 = cmask c)
    ((mul_relCT hbytes sp (o := 4) (a := 2) (b := 1) (by decide) (by decide) (by decide) (by decide)
      (by taint_decide)).mono (fun _ _ ⟨⟨_, S₁, _⟩, ⟨_, S₂, _⟩⟩ =>
        ⟨S₁.2.2.1, S₂.2.2.1, ⟨⟨_, S₁.1, S₁.2.2.2.1⟩, S₁.2.1⟩, ⟨⟨_, S₂.1, S₂.2.2.2.1⟩, S₂.2.1⟩⟩) fun _ _ h => h)
    fun _ ⟨M, S, hm⟩ => WP.mono (mul421_st sp hbytes S hm) fun _ h => ⟨M, h⟩) ?_
  refine VG.RelCT.seq (taint_both (F := fun s => ∃ M, St base bytes len args sp M k s ∧ ∃ c, s.gpr .ecx = cmask c)
    (fun _ _ ⟨_, S₁, _⟩ ⟨_, S₂, _⟩ => S₁.agree S₂) (.block [])
    (by taint_decide) fun _ ⟨M, S, hm⟩ => WP.mono (mov_st sp S hm) fun _ h => ⟨M, h⟩) ?_
  refine VG.RelCT.seq (taint_both (F := fun s => ∃ M, St base bytes len args sp M k s)
    (fun _ _ ⟨_, S₁, _⟩ ⟨_, S₂, _⟩ => S₁.agree S₂) (VG.Taint.hintOf taint τA (select 4 2))
    (by taint_decide) fun _ ⟨M, S, hm⟩ => WP.mono (select_st sp hbase S hm) fun _ h => ⟨M, h⟩) ?_
  refine VG.RelCT.seq (relCT_both (F := fun s => ∃ M, St base bytes len args sp M k s)
    ((mul_relCT hbytes sp (o := 1) (a := 1) (b := 1) (by decide) (by decide) (by decide) (by decide)
      (by taint_decide)).mono (fun _ _ ⟨⟨_, S₁⟩, ⟨_, S₂⟩⟩ =>
        ⟨S₁.2.2.1, S₂.2.2.1, ⟨⟨_, S₁.1, S₁.2.2.2.1⟩, S₁.2.1⟩, ⟨⟨_, S₂.1, S₂.2.2.2.1⟩, S₂.2.1⟩⟩) fun _ _ h => h)
    fun _ ⟨M, S⟩ => WP.mono (mul111_st sp hbytes S) fun _ h => ⟨M, h⟩) ?_
  exact taint_both (fun _ _ ⟨_, S₁⟩ ⟨_, S₂⟩ => S₁.agree S₂) (.block []) (by taint_decide)
    fun _ ⟨M, S⟩ => WP.mono (last_st sp hk hk32 S) fun _ ⟨h, z⟩ => ⟨⟨M, h⟩, z⟩

theorem expLoop_relCT (hbase : (args 8).toNat = base.toNat) (hbytes : bytes = (args 9).toNat * 8) (n : Nat) (hn : 0 < n) (hn64 : n ≤ 64) :
    RelCT isa (Both fun s => ∃ M, St base bytes len args sp M n s) (.loop expStep .ne)
      (Both fun s => ∃ M, St base bytes len args sp M 0 s) := by
  refine (VG.RelCT.loop (I := fun n s t => 0 < n ∧ n ≤ 64 ∧ Both (fun s => ∃ M, St base bytes len args sp M n s) s t)
    (fun n => ?_) n).mono (fun _ _ h => ⟨hn, hn64, h⟩) fun _ _ h => h
  refine VG.RelCT.exists_ (P := fun (_ : 0 < n ∧ n ≤ 64) => Both fun s => ∃ M, St base bytes len args sp M n s)
    (fun hb => ?_) |>.mono (fun _ _ ⟨h₁, h₂, h⟩ => ⟨⟨h₁, h₂⟩, h⟩) fun _ _ h => h
  refine (expStep_relCT sp hbase hbytes hb.1 (by omega)).mono (fun _ _ h => h) ?_
  rintro s t ⟨⟨S₁, z₁⟩, ⟨S₂, z₂⟩⟩
  have e₁ : isa.eval .ne s = some (!decide (n = 1)) := by show s.zf.map (!·) = _; rw [z₁]; rfl
  have e₂ : isa.eval .ne t = some (!decide (n = 1)) := by show t.zf.map (!·) = _; rw [z₂]; rfl
  refine ⟨e₁.trans e₂.symm, fun h => ?_, fun h => ?_⟩
  · rw [e₁] at h
    have : n = 1 := by simpa using h
    subst this
    exact ⟨S₁, S₂⟩
  · rw [e₁] at h
    have : n ≠ 1 := by simpa using h
    exact ⟨n - 1, by omega, by omega, by omega, S₁, S₂⟩

end

end VG.Proof.Bignum.X86.PublicRt
