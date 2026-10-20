module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeTable
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeTable
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86.PowerInit
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.MulOk
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.MulOk
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Select
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Select
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Shift
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Shift
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.StageR
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.StageR
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Window
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Window

/-! # The trace of a windowed power

Each window's squares and product are related by `mul_relCT`, its window
and entry selected by code the taint analysis checks; the runs keep the
table and slots 3 and 6 below the modulus (`WSt`) and the count in `esi`,
so the loop's runs (`windowLoop_relCT`) and the power's
(`windowPower_relCT`) leak the same trace. `WinChecks` collects the taint
checks of a context's code, which hold for both (`winChecks`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.PublicRt (Both)

/-- A multiplication's arguments, checked. -/
abbrev MulCheck (c : Ctx) (o a b : Nat) : Prop :=
  (VG.Taint.check taint τF (.block (mulArgs c o a b)) (.block [])).isSome = true

/-- Code checked by the taint analysis from `τA`. -/
abbrev ACheck (p : Prog isa) : Prop := (VG.Taint.check taint τA p (VG.Taint.hintOf taint τA p)).isSome = true

/-- The taint checks of a context's windowed power. -/
structure WinChecks (c : Ctx) : Prop where
  m643 : MulCheck c 6 4 3
  m554 : MulCheck c 5 5 4
  m775 : MulCheck c 7 7 5
  m666 : MulCheck c 6 6 6
  m667 : MulCheck c 6 6 7
  m663 : MulCheck c 6 6 3
  tail : (VG.Taint.check taint τAs (tableTail c) (VG.Taint.hintOf taint τAs (tableTail c))).isSome = true
  setup : ACheck (Prog.chain (tableSetup c) (.block []))
  next : ACheck (nextWindow c)
  select : ACheck (selectWindow c)
  count : ACheck (.block (widthC 0 c .esi ++ [.alu .add .esi (.reg .esi)]))
  dec : ACheck (.block [.alu .sub .esi (.imm 1)])

theorem winChecks (c : Ctx) : WinChecks c := by
  cases c <;> constructor <;> (try dsimp only [MulCheck, ACheck]) <;> taint_decide

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {c : Ctx} {sp : BitVec 32}

theorem nwR_sv3 (h : In base bytes len args s) {m m' : Mem}
    (F : Frame (frameR base sp (nwR len c)) m m') (R : CallRoom sp base bytes) :
    sv m' base len c 3 = sv m base len c 3 := by
  have nw := h.crt.scratch.nowrap
  have f8 := h.slot_fit c (j := 8) (by decide)
  have bw := bc_eq_cwc len c
  have est : st len c = 2 * bc len c + 32 := rfl
  have e8 : lo len (.slot c 8) = numBase + 8 * st len c := rfl
  have e3 : lo len (.slot c 3) = numBase + 3 * st len c := rfl
  have nb : numBase = 3336 := rfl
  have wo : winOff = 4 := rfl
  have fit : ∀ p ∈ nwR len c, p.1 + p.2 ≤ bytes := fun p hp => wR_fit h c p (wR_sub_nw len c p hp)
  refine frameR_val32 F R nw (by omega) ?_ fit
  intro p hp; simp only [nwR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> dsimp only <;> omega

/-- A window's run: slots 3 and 6 and the table below the modulus, the count `n` in `esi`. -/
abbrev WinSt (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (c : Ctx) (ks : List Nat)
    (n : Nat) (s : State) : Prop :=
  WSt base bytes len args sp c ks 16 s ∧ s.gpr .esi = BitVec.ofNat 32 n

theorem nextWindow_wst {n : Nat} (W : WinSt base bytes len args sp c [3, 6] n s) :
    WP isa (nextWindow c) s fun u => WinSt base bytes len args sp c [3, 6] n u ∧ w32 u.mem base winOff < 16 := by
  obtain ⟨⟨M, C, Hk, He, A, sp₀⟩, e⟩ := W
  have h := C.inp
  refine WP.mono (nextWindow_ok h c) fun u ⟨F, Wn, _, K⟩ => ?_
  obtain ⟨Y, T⟩ := nwR_keep h F h.crt.room
  have Y3 := nwR_sv3 h F h.crt.room
  refine ⟨⟨⟨M, C.keepF2 K (by decide) (by decide) F (fun p hp => wR_fit h c p (wR_sub_nw len c p hp))
    (fun p hp => wR_hdr len c p (wR_sub_nw len c p hp)), fun j hj => ?_, fun j hj => by rw [T j hj]; exact He j hj,
    A.keep K, (K.1 _ (by decide)).trans sp₀⟩, (K.1 _ (by decide)).trans e⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · rw [Y3]; exact Hk 3 (by decide)
    · rw [Y]; exact Hk 6 (by decide)
  · rw [Wn, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    have := val32_lt s.mem base (lo len (.slot c 8)) (cwc len c)
    simp only [sv]; omega

theorem selectWindow_wst {n : Nat} (W : WinSt base bytes len args sp c [3, 6] n s ∧ w32 s.mem base winOff < 16) :
    WP isa (selectWindow c) s (WinSt base bytes len args sp c [3, 6, 7] n) := by
  obtain ⟨⟨⟨M, C, Hk, He, A, sp₀⟩, e⟩, hw⟩ := W
  have h := C.inp
  have bl := h.bytes_lt
  have f8 := h.slot_fit c (j := 8) (by decide)
  have T := h.table_fit c
  have bw := bc_eq_cwc len c
  have est : st len c = 2 * bc len c + 32 := rfl
  have e3 : lo len (.slot c 3) = numBase + 3 * st len c := rfl
  have e6 : lo len (.slot c 6) = numBase + 6 * st len c := rfl
  have e7 : lo len (.slot c 7) = numBase + 7 * st len c := rfl
  have e8 : lo len (.slot c 8) = numBase + 8 * st len c := rfl
  have z0 : lo len (.slot c 0) = numBase := sl_zero len c
  have e01 : lo len (.slot c 0) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  have T8 : lo len (.slot c 8) + st len c ≤ te len c 0 := by
    have := ctx_in h c (j := 8) (by decide)
    have W := bc_le_wide len c
    have t0 : te len c 0 = lo len (.slot .wide 20) := by simp [te]
    have e20 : lo len (.slot .wide 20) = numBase + 20 * st len .wide := rfl
    have estw : st len .wide = 2 * bc len .wide + 32 := rfl
    omega
  refine WP.mono (selectWindow_ok h hw) fun u ⟨O, S, K⟩ => ?_
  have C' := C.keepF (K.mono (by decide) : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u) (by decide) (by decide)
    (ws := [(lo len (.slot c 7), bc len c)]) (frameR_of_outside O (by omega) (by simp))
    (by intro q hq; simp only [List.mem_singleton] at hq; subst hq; dsimp only; omega)
    (by intro q hq; simp only [List.mem_singleton] at hq; subst hq; dsimp only; omega)
  refine ⟨⟨M, C', fun j hj => ?_, fun j hj => ?_, A.keep K, (K.1 _ (by decide)).trans sp₀⟩,
    (K.1 _ (by decide)).trans e⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl
    · simp only [sv]; rw [Outside.val32 O (.inl (by omega)) (by omega)]; exact Hk 3 (by decide)
    · simp only [sv]; rw [Outside.val32 O (.inl (by omega)) (by omega)]; exact Hk 6 (by decide)
    · simp only [sv]; rw [S]; exact He _ hw
  · obtain ⟨tj0, tj⟩ := te_le (len := len) (c := c) hj
    rw [Outside.val32 O (.inr (by omega)) (by omega)]; exact He j hj

theorem dec_wst {n : Nat} (hn0 : 0 < n) (hn : n < 2 ^ 32) (W : WinSt base bytes len args sp c [3, 6] n s) :
    WP isa (.block [.alu .sub .esi (.imm 1)]) s fun u =>
      WinSt base bytes len args sp c [3, 6] (n - 1) u ∧ u.zf = some (decide (n = 1)) := by
  obtain ⟨⟨M, C, Hk, He, A, sp₀⟩, e⟩ := W
  refine wp_subZ rfl fun u a z => WP.block_nil ?_
  have sub : BitVec.ofNat 32 n - 1 = BitVec.ofNat 32 (n - 1) := VG.Proof.Mont.X86.Dynamic.counter_sub hn hn0
  refine ⟨⟨⟨M, C.regs a.keeps a.mem, by rw [a.mem]; exact Hk, by rw [a.mem]; exact He, A.keep a.keeps,
    (a.other _ (by decide)).trans sp₀⟩, by rw [a.gpr, e, sub]⟩, ?_⟩
  rw [z, e, sub]
  have zz := VG.Proof.Mont.X86.Dynamic.counter_zero hn hn0
  rw [show ∀ x : BitVec 32, x - 0 = x from BitVec.sub_zero] at zz
  rw [zz]

theorem windowStep_relCT (hc : WinChecks c) {n : Nat} (hn0 : 0 < n) (hn : n < 2 ^ 32) :
    RelCT isa (Both (WinSt base bytes len args sp c [3, 6] n)) (windowStep c)
      (Both fun u => WinSt base bytes len args sp c [3, 6] (n - 1) u ∧ u.zf = some (decide (n = 1))) := by
  have sq : RelCT isa (Both (WinSt base bytes len args sp c [3, 6] n)) (square c)
      (Both (WinSt base bytes len args sp c [3, 6] n)) :=
    mul_wst_relCT (X := fun s => s.gpr .esi = BitVec.ofNat 32 n) (X' := fun s => s.gpr .esi = BitVec.ofNat 32 n)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.m666 (ks' := [3, 6]) (by decide)
      (by decide) (by decide) fun _ _ e K => (K.1 _ (by decide)).trans e
  unfold windowStep
  refine VG.RelCT.seq sq (VG.RelCT.seq sq (VG.RelCT.seq sq (VG.RelCT.seq sq ?_)))
  refine VG.RelCT.seq (taint_both (fun _ _ W₁ W₂ => W₁.1.agree W₂.1) _ hc.next fun _ W => nextWindow_wst W) ?_
  refine VG.RelCT.seq (taint_both (fun _ _ W₁ W₂ => W₁.1.1.agree W₂.1.1) _ hc.select
    fun _ W => selectWindow_wst W) ?_
  refine VG.RelCT.seq (mul_wst_relCT (X := fun s => s.gpr .esi = BitVec.ofNat 32 n)
    (X' := fun s => s.gpr .esi = BitVec.ofNat 32 n) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hc.m667 (ks' := [3, 6]) (by decide) (by decide) (by decide)
    fun _ _ e K => (K.1 _ (by decide)).trans e) ?_
  exact taint_both (fun _ _ W₁ W₂ => W₁.1.agree W₂.1) _ hc.dec fun _ W => dec_wst hn0 hn W

theorem windowLoop_relCT (hc : WinChecks c) {N : Nat} (hN : 0 < N) (hN32 : N < 2 ^ 32) :
    RelCT isa (Both (WinSt base bytes len args sp c [3, 6] N)) (.loop (windowStep c) .ne)
      (Both (WinSt base bytes len args sp c [3, 6] 0)) := by
  refine (relCT_countLoop (I := fun j => WinSt base bytes len args sp c [3, 6] (N - j)) hN fun j hj => ?_).mono
    (fun _ _ h => by simpa only [Nat.sub_zero] using h) (fun _ _ h => by simpa only [Nat.sub_self] using h)
  refine (windowStep_relCT hc (n := N - j) (by omega) (by omega)).mono (fun _ _ h => h) ?_
  rintro s t ⟨⟨W₁, z₁⟩, ⟨W₂, z₂⟩⟩
  have e : N - j - 1 = N - (j + 1) := by omega
  have d : (N - j = 1) = (j + 1 = N) := propext (by omega)
  rw [e] at W₁ W₂
  simp only [d] at z₁ z₂
  exact ⟨⟨W₁, z₁⟩, ⟨W₂, z₂⟩⟩

theorem count_wst (W : TSt base bytes len args sp c [3, 5, 6] 16 s) :
    WP isa (.block (widthC 0 c .esi ++ ([.alu .add .esi (.reg .esi)] : List Instr))) s
      (WinSt base bytes len args sp c [3, 6] (2 * bc len c)) := by
  obtain ⟨⟨M, C, Hk, He, A, sp₀⟩, -⟩ := W
  have h := C.inp
  have hb := bc_le h.upper' c
  refine widthC_ok (k := 0) (c := c) (r := .esi) h.width h.upper' fun s₄ K₄ M₄ e₄ =>
    wp_addS rfl fun s₅ a₅ _ => WP.block_nil ?_
  have K : Keeps [.esi] s s₅ := K₄.trans (a₅.keeps.mono (by decide))
  have m : s₅.mem = s.mem := by rw [a₅.mem, M₄]
  refine ⟨⟨M, C.regs K m, fun j hj => by rw [sv, m]; exact Hk j (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega),
    fun j hj => by rw [m]; exact He j hj, A.keep K, (K.1 _ (by decide)).trans sp₀⟩, ?_⟩
  rw [a₅.gpr, e₄, BitVec.ofNat_add_ofNat]; congr 1; omega

/-- A windowed power's runs, from slots 3 and 4 below the modulus. -/
theorem windowPower_relCT (hc : WinChecks c) :
    RelCT isa (Both (WSt base bytes len args sp c [3, 4] 0)) (windowPower c)
      (Both (WSt base bytes len args sp c [6] 0)) := by
  unfold windowPower
  refine VG.RelCT.seq (mul_wst_relCT0 (o := 6) (a := 4) (b := 3) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc.m643 (ks' := [3, 4, 6]) (by decide) (by decide) (by decide)) ?_
  refine VG.RelCT.seq (mul_wst_relCT0 (o := 5) (a := 5) (b := 4) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc.m554 (ks' := [3, 5, 6]) (by decide) (by decide) (by decide)) ?_
  refine VG.RelCT.seq (buildTable_relCT hc.m775 hc.tail hc.setup) ?_
  refine VG.RelCT.seq (taint_both (fun _ _ W₁ W₂ => W₁.1.agree W₂.1) _ hc.count fun _ W => count_wst W) ?_
  by_cases hN : 0 < 2 * bc len c ∧ 2 * bc len c < 2 ^ 32
  · refine VG.RelCT.seq (windowLoop_relCT hc hN.1 hN.2) ?_
    exact (mul_wst_relCT0 (o := 6) (a := 6) (b := 3) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) hc.m663 (ks := [3, 6]) (ks' := [6]) (by decide) (by decide) (by decide)).mono
      (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => ⟨h.1.mono, h.2.mono⟩
  · refine VG.RelCT.of_false fun s₁ s₂ h => hN ?_
    obtain ⟨⟨⟨_, C, _⟩, _⟩, _⟩ := h
    have := bc_ge C.inp.lower' c
    have := bc_le C.inp.upper' c
    omega

end

end VG.Proof.Bignum.X86.CrtRt
