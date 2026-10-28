module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Kinds
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Slots
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Start
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Count
import VerifiedGarbage.Proof.Weierstrass.X86.InvLoop
import VerifiedGarbage.Proof.Weierstrass.X86.Loop
import VerifiedGarbage.Proof.Mont.X86.Inverse
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Weierstrass.X86.Inv

/-! # The batched inverse's header operations, each in both runs

The slots (from `Pre0`), the start of the state and its count, the inverse word, the windows'
steps, `redSum`'s two ends, and the counts of the two loops, whose flags agree.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt.Time

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Rsa.X86.InvBatchRt
open VG.Proof.Weierstrass (Unch)
open VG.Proof.Weierstrass.X86.Inv (wordClob)
open VG.Impl.Weierstrass.X86 (decCounter testCounter)

theorem stable_esi {rs : List Reg} (h : Reg.esi ∉ rs) (v : BitVec 32) : Stable rs fun g => g .esi = v :=
  fun _ _ k e => (k _ h).trans e

/-- `Dynamic.inverse` writes only registers. -/
theorem inverse_frame (s : State) :
    WP isa (.block VG.Impl.Mont.X86.Dynamic.inverse) s fun t => Keeps [.eax, .ecx, .edx, .ebp] s t ∧ t.mem = s.mem := by
  unfold VG.Impl.Mont.X86.Dynamic.inverse
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_movS rfl fun t₀ u₀ _ => ?_
  refine WP.block_append (WP.mono (VG.Proof.Mont.X86.Dynamic.newton_ok t₀) fun t₁ ⟨_, k₁, m₁⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Mont.X86.Dynamic.newton_ok t₁) fun t₂ ⟨_, k₂, m₂⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Mont.X86.Dynamic.newton_ok t₂) fun t₃ ⟨_, k₃, m₃⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Mont.X86.Dynamic.newton_ok t₃) fun t₄ ⟨_, k₄, m₄⟩ => ?_)
  refine wp_movS rfl fun t₅ u₅ _ => wp_subS rfl fun t₆ u₆ _ => WP.block_nil ⟨?_, ?_⟩
  · exact (((((u₀.keeps.mono (by decide)).trans k₁).trans k₂).trans k₃).trans k₄ |>.widen u₅.keeps).widen u₆.keeps
  · rw [u₆.mem, u₅.mem, m₄, m₃, m₂, m₁, u₀.mem]

variable {L : Lay} {B : Addr} {Z len N : Nat} {args : Nat → BitVec 32} {sp : BitVec 32} {C : Nat → Prop}
  {G : (Reg → BitVec 32) → Prop}

theorem relSlots (hL : L.ws = 14) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint τ0 (.block (slots L)) hc).isSome = true) :
    RelCT isa (fun s t => Pre0 L B Z len N args sp s ∧ Pre0 L B Z len N args sp t) (.block (slots L))
      (Both L B Z len N args sp (fun _ => True) fun _ => True ∧ True) :=
  leaf0 hL (fun s ps => by
    rw [show slots L = slots L ++ [] from (List.append_nil _).symm]
    exact slots_ok ps.1 ps.2.1 fun u H K O => WP.block_nil ⟨H, ps.2.2.keep K (by decide)
      (O.mono (Nat.zero_le _) (by have := H.halfZ; simp only [slotBase, halfSlot] at this ⊢; omega)),
      trivial, trivial, trivial⟩) h

/-- `delta = 1`. -/
theorem relWinOne (hL : L.ws = 14) (hG : Stable [.eax] G) (hfit : 160 + 16 * (8 * nw len + 8) ≤ Z) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint τS (.block [.mov .eax (.imm 1), .store (sc win) .eax]) hc).isSome = true) :
    RelCT isa (Both L B Z len N args sp C fun g => G g ∧ True) (.block [.mov .eax (.imm 1), .store (sc win) .eax])
      (Both L B Z len N args sp C fun g => G g ∧ True) :=
  relOp (ws := [(win, 4)]) hL (by decide) hG (fun w hw => by
      simp only [List.mem_singleton] at hw; subst w; exact ⟨.inr (by decide), by simp only [win]; omega⟩)
    (fun s hb _ => by
      have hZ := hb.halfZ
      refine wp_movS rfl fun u₁ V₁ _ => ?_
      have hs₁ := hb.ws.ws.workspace.of_keeps V₁.keeps (by decide)
      refine wp_storeS (hs₁.ea (by simp only [win, halfSlot] at hZ ⊢; omega))
        (hs₁.write (d := win) (n := 4) (by simp only [win, halfSlot] at hZ ⊢; omega)) fun u₂ V₂ => WP.block_nil ?_
      have O₂ : Outside B win 4 s.mem u₂.mem := by
        rw [V₂.mem, V₁.mem]; exact writeW32_outside _ _ _ (by have := hb.nowrap; simp only [win]; omega)
      exact ⟨hb.keepLow (V₁.keeps.trans (V₂.keeps _)) (by decide) (by decide) O₂ (by decide),
        V₁.keeps.trans (V₂.keeps _), O₂.unch, trivial⟩) h

/-- The coefficient `1` in `[7]`. -/
theorem relA7One (hL : L.ws = 14) (hG : Stable [.eax, .ecx, .edx] G) (hfit : 160 + 16 * (8 * nw len + 8) ≤ Z)
    {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint τS (.block (ptr L .eax (a 7) .edx ++ ([.mov .ecx (.imm 1), .store (at_ .eax 0) .ecx] : List Instr)))
      hc).isSome = true) :
    RelCT isa (Both L B Z len N args sp C fun g => G g ∧ True)
      (.block (ptr L .eax (a 7) .edx ++ ([.mov .ecx (.imm 1), .store (at_ .eax 0) .ecx] : List Instr)))
      (Both L B Z len N args sp C fun g => G g ∧ True) := by
  have r7 := rv_a len 7
  refine relOp (ws := [(rv (kw len) (a 7), 4)]) hL (by decide) hG (ws1 (by omega) (by omega)) (fun s hb _ => ?_) h
  have hn := hb.nowrap
  refine ptr_ok hb.ws hb.slots hb.halfZ (r := .eax) (t := .edx) (x := a 7) (by decide) (by decide) (by decide)
    (by decide) (by intro e; cases e) (by omega) fun u₅ K₅ m₅ p₅ => ?_
  refine wp_movS rfl fun u₆ V₆ _ => ?_
  have hw₆ := (hb.ws.rt.of_keeps K₅).of_keeps V₆.keeps
  have p₆ : PtrAt u₆ B .eax (rv (kw len) (a 7)) := by rw [PtrAt, V₆.other _ (by decide)]; exact p₅
  have ea₆ : u₆.ea (at_ .eax 0) = off B (rv (kw len) (a 7)) := by simpa using ea_ptr hw₆ p₆ (d := 0) (by omega)
  refine wp_storeS ea₆ (ws_write hw₆ (by omega)) fun u₇ V₇ => WP.block_nil ?_
  have K₇ : Keeps [.eax, .ecx, .edx] s u₇ := ((K₅.mono (by decide)).trans (V₆.keeps.mono (by decide))).trans
    (V₇.keeps _)
  have O₇ : Outside B (rv (kw len) (a 7)) 4 s.mem u₇.mem := by
    rw [V₇.mem, V₆.mem, m₅]; exact writeW32_outside _ _ _ (by omega)
  exact ⟨hb.keep K₇ (by decide) (by decide) O₇ (by omega) (by omega), K₇, O₇.unch, trivial⟩

/-- The inverse word, from `[2]`'s low word. -/
theorem relInverse (hL : L.ws = 14) (hG : Stable [.eax, .ebx, .ecx, .edx, .ebp] G)
    (hfit : 160 + 16 * (8 * nw len + 8) ≤ Z) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint τS (.block (ptr L .eax (a 2) .edx ++ ([.mov .ebx (.mem (at_ .eax 0))] : List Instr) ++
      VG.Impl.Mont.X86.Dynamic.inverse ++ ([.store (sc (win + 28)) .eax] : List Instr))) hc).isSome = true) :
    RelCT isa (Both L B Z len N args sp C fun g => G g ∧ True)
      (.block (ptr L .eax (a 2) .edx ++ ([.mov .ebx (.mem (at_ .eax 0))] : List Instr) ++
        VG.Impl.Mont.X86.Dynamic.inverse ++ ([.store (sc (win + 28)) .eax] : List Instr)))
      (Both L B Z len N args sp C fun g => G g ∧ True) := by
  have r2 := rv_a len 2
  refine relOp (ws := [(win + 28, 4)]) hL (by decide) hG (fun w hw => by
      simp only [List.mem_singleton] at hw; subst w; exact ⟨.inr (by decide), by simp only [win]; omega⟩)
    (fun s hb _ => ?_) h
  have hn := hb.nowrap
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine ptr_ok hb.ws hb.slots hb.halfZ (r := .eax) (t := .edx) (x := a 2) (by decide) (by decide) (by decide)
    (by decide) (by intro e; cases e) (by omega) fun u₈ K₈ m₈ p₈ => ?_
  have hw₈ := hb.ws.rt.of_keeps K₈
  refine wp_movS (readSrc_ptr hw₈ p₈ (d := 0) (by omega)) fun u₉ V₉ _ => ?_
  refine WP.block_append (WP.mono (inverse_frame u₉) fun u₁₀ ⟨K₁₀, M₁₀⟩ => ?_)
  have K₁₀' : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u₁₀ :=
    ((K₈.mono (by decide)).trans (V₉.keeps.mono (by decide))).trans (K₁₀.mono (by decide))
  have hs₁₀ := hb.ws.ws.workspace.of_keeps K₁₀' (by decide)
  refine wp_storeS (hs₁₀.ea (by simp only [win]; omega)) (hs₁₀.write (d := win + 28) (n := 4) (by simp only [win]; omega))
    fun u₁₁ V₁₁ => WP.block_nil ?_
  have O₁₁ : Outside B (win + 28) 4 s.mem u₁₁.mem := by
    rw [V₁₁.mem, M₁₀, V₉.mem, m₈]; exact writeW32_outside _ _ _ (by simp only [win]; omega)
  exact ⟨hb.keepLow (K₁₀'.trans (V₁₁.keeps _)) (by decide) (by decide) O₁₁ (by decide), K₁₀'.trans (V₁₁.keeps _),
    O₁₁.unch, trivial⟩

/-- The batch count, `3 (n + 1)`. -/
theorem relBatches (hL : L.ws = 14) (hG : Stable [.eax, .ecx] G) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint τS (.block batches) hc).isSome = true) :
    RelCT isa (Both L B Z len N args sp C fun g => G g ∧ True) (.block batches)
      (Both L B Z len N args sp (· = 3 * (nw len + 1)) fun g => G g ∧ True) :=
  leafU hL (fun s ps => by
    have hb := ps.1
    have hn := hb.nowrap
    have hZ := hb.halfZ
    have hw := kw_bound hb.ws.lenLe
    have ke := kw_eq len
    have hf16 := hb.fits16
    unfold batches
    refine nBytes_ok hb.ws.ws.workspace hb.slots hZ (by omega) (e := 1) (by decide) fun u₁₂ K₁₂ m₁₂ c₁₂ => ?_
    refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun u₁₃ V₁₃ => ?_
    refine wp_movS rfl fun u₁₄ V₁₄ _ => wp_addS rfl fun u₁₅ V₁₅ _ => wp_addS rfl fun u₁₆ V₁₆ _ => ?_
    have K₁₆ : Keeps [.eax, .ecx] s u₁₆ :=
      ((((K₁₂.mono (by decide)).trans (V₁₃.keeps.mono (by decide))).trans (V₁₄.keeps.mono (by decide))).trans
        (V₁₅.keeps.mono (by decide))).trans (V₁₆.keeps.mono (by decide))
    have hs₁₆ := hb.ws.ws.workspace.of_keeps K₁₆ (by decide)
    refine wp_storeS (hs₁₆.ea (by omega)) (hs₁₆.write (d := 100) (n := 4) (by omega)) fun z Vz => WP.block_nil ?_
    have m₁₆ : u₁₆.mem = s.mem := by rw [V₁₆.mem, V₁₅.mem, V₁₄.mem, V₁₃.mem, m₁₂]
    have Oz : Outside B 100 4 s.mem z.mem := by rw [Vz.mem, m₁₆]; exact writeW32_outside _ _ _ (by omega)
    have Kz := K₁₆.trans (Vz.keeps _)
    refine ⟨hb.keepHigh Kz (by decide) (by decide) Oz (by decide) (by omega),
      ps.2.1.keep Kz (by decide) (Oz.mono (Nat.zero_le _) (by omega)), ?_, hG _ _ Kz.1 ps.2.2.2.1, trivial⟩
    show w32 z.mem B 100 = 3 * (nw len + 1)
    rw [Vz.mem, w32_write_self, V₁₆.gpr, V₁₅.gpr, V₁₅.other .ecx (by decide), V₁₄.gpr, V₁₄.other _ (by decide),
      V₁₃.gpr]
    have e₁₂ : (u₁₂.gpr .eax).toNat = 4 * (nw len + 1) := by rw [c₁₂]; omega
    have e₁₃ : (u₁₂.gpr .eax >>> 2).toNat = nw len + 1 := by
      rw [BitVec.toNat_ushiftRight, e₁₂, Nat.shiftRight_eq_div_pow]; omega
    simp only [BitVec.toNat_add, e₁₃]
    omega) h

theorem relStart (hL : L.ws = 14) (hG : Stable wordClob G) (hfit : 160 + 16 * (8 * nw len + 8) ≤ Z) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint τS (.block (start L)) hc).isSome = true) :
    RelCT isa (Both L B Z len N args sp C fun g => G g ∧ True) (.block (start L))
      (Both L B Z len N args sp C fun g => G g ∧ True) :=
  relOp (ws := [(win + 4, 24)]) hL (by decide) hG (fun w hw => by
      simp only [List.mem_singleton] at hw; subst w; exact ⟨.inr (by decide), by simp only [win]; omega⟩)
    (fun s hb _ => WP.mono (start_ok hb) fun _ ⟨H, _, K, O⟩ => ⟨H, K, O.unch, trivial⟩) h

theorem relWordSteps (hL : L.ws = 14) (hG : Stable wordClob G) (hfit : 160 + 16 * (8 * nw len + 8) ≤ Z) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint τS (VG.Impl.Weierstrass.X86.Inv.wordSteps win 30) hc).isSome = true) :
    RelCT isa (Both L B Z len N args sp C fun g => G g ∧ True) (VG.Impl.Weierstrass.X86.Inv.wordSteps win 30)
      (Both L B Z len N args sp C fun g => G g ∧ True) :=
  relOp (ws := [(win, 28)]) hL (by decide) hG (fun w hw => by
      simp only [List.mem_singleton] at hw; subst w; exact ⟨.inr (by decide), by simp only [win]; omega⟩)
    (fun s hb _ => WP.mono (VG.Proof.Weierstrass.X86.Inv.wordSteps_ok hb.ws.ws.workspace (t := win)
      (by have := hb.halfZ; simp only [win, halfSlot] at this ⊢; omega) (by decide) (by decide))
      fun t ⟨_, K, O⟩ => ⟨hb.keepLow K (by decide) (by decide) O (by decide), K, O.unch, trivial⟩) h

/-- The batch count down by one, its flags set by the new count. -/
theorem relCountDown {m : Nat} (hL : L.ws = 14) (hm : 1 ≤ m) (hm32 : m < 2 ^ 32) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint τS (.block [.mov .esi (.mem (sc 100)), decCounter, .store (sc 100) .esi,
      testCounter]) hc).isSome = true) :
    RelCT isa (Both L B Z len N args sp (· = m) fun _ => True ∧ True)
      (.block [.mov .esi (.mem (sc 100)), decCounter, .store (sc 100) .esi, testCounter])
      (fun s t => Both L B Z len N args sp (· = m - 1) (fun _ => True ∧ True) s t ∧
        s.zf = some (decide (m - 1 = 0)) ∧ t.zf = some (decide (m - 1 = 0))) :=
  (leafU (Q := fun t => Pre L B Z len N args sp (fun g m' => (· = m - 1) (w32 m' B 100) ∧ True ∧ True) t ∧
      t.zf = some (decide (m - 1 = 0))) hL (fun s ps => by
    have hb := ps.1
    have hZ := hb.halfZ
    have hf16 := hb.fits16
    exact WP.mono (VG.Proof.Rsa.X86.GcdBatch.countDown_ok hb.ws.ws.workspace (d := 100)
      (by simp only [halfSlot] at hZ; omega) hm hm32 ps.2.2.1) fun z ⟨c, zf, K, O⟩ =>
      ⟨⟨hb.keepHigh K (by decide) (by decide) O (by decide) (by omega),
        ps.2.1.keep K (by decide) (O.mono (Nat.zero_le _) (by omega)), c, trivial, trivial⟩, zf⟩) h).mono
    (fun _ _ h => h) fun _ _ ⟨⟨a, za⟩, ⟨b, zb⟩⟩ => ⟨⟨a, b⟩, za, zb⟩

/-- The doublings' count into `esi`. -/
theorem relDoublings (hL : L.ws = 14) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint τS (.block doublings) hc).isSome = true) :
    RelCT isa (Both L B Z len N args sp C fun _ => True ∧ True) (.block doublings)
      (Both L B Z len N args sp C fun g => g .esi = BitVec.ofNat 32 (6 * (nw len + 1)) ∧ True) :=
  (relOp (L := L) (B := B) (Z := Z) (len := len) (N := N) (ws := []) (G := fun _ => True) (H := fun _ => True)
    (X := fun g => g .esi = BitVec.ofNat 32 (6 * (nw len + 1))) hL (by decide) (stable_true [.eax, .esi])
    (fun _ h => nomatch h) (fun s hb _ => by
    have hw := kw_bound hb.ws.lenLe
    have ke := kw_eq len
    have hf16 := hb.fits16
    unfold doublings
    refine nBytes_ok hb.ws.ws.workspace hb.slots hb.halfZ (by omega) (e := 1) (by decide)
      fun s₄ K₄ m₄ c₄ => ?_
    refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun s₅ V₅ => ?_
    refine wp_movS rfl fun s₆ V₆ _ => wp_addS rfl fun s₇ V₇ _ => wp_addS rfl fun s₈ V₈ _ => WP.block_nil ?_
    have K₈ : Keeps [.eax, .esi] s s₈ :=
      ((((K₄.mono (by decide)).trans (V₅.keeps.mono (by decide))).trans (V₆.keeps.mono (by decide))).trans
        (V₇.keeps.mono (by decide))).trans (V₈.keeps.mono (by decide))
    have m₈ : s₈.mem = s.mem := by rw [V₈.mem, V₇.mem, V₆.mem, V₅.mem, m₄]
    refine ⟨hb.keep K₈ (by decide) (by decide) (o := 160) (c := 0)
      (by rw [m₈]; exact Outside.refl _ _ _ _) (Nat.le_refl _) (by omega), K₈, by rw [m₈]; exact Unch.refl _ _ _, ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [V₈.gpr, V₇.gpr, V₇.other .eax (by decide), V₆.gpr]
    have e₄ : (s₄.gpr .esi).toNat = 4 * (nw len + 1) := by rw [c₄]; omega
    have e₅ : (s₅.gpr .esi).toNat = 2 * (nw len + 1) := by
      rw [V₅.gpr, BitVec.toNat_ushiftRight, e₄, Nat.shiftRight_eq_div_pow]; omega
    have e₆ : s₆.gpr .esi = s₅.gpr .esi := V₆.other _ (by decide)
    rw [e₆]
    simp only [BitVec.toNat_add, e₅, BitVec.toNat_ofNat]
    omega) h).mono (fun _ _ h => h) fun _ _ ⟨⟨b, p, c, _, e⟩, ⟨b', p', c', _, e'⟩⟩ =>
    ⟨⟨b, p, c, e, trivial⟩, ⟨b', p', c', e', trivial⟩⟩

/-- The doublings' count down by one, its flags set by the new count. -/
theorem relDecTest {k : Nat} (hL : L.ws = 14) (hk : 1 ≤ k) (hk32 : k < 2 ^ 32) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint τS (.block [decCounter, testCounter]) hc).isSome = true) :
    RelCT isa (Both L B Z len N args sp C fun g => g .esi = BitVec.ofNat 32 k ∧ True) (.block [decCounter, testCounter])
      (fun s t => Both L B Z len N args sp C (fun g => g .esi = BitVec.ofNat 32 (k - 1) ∧ True) s t ∧
        s.zf = some (decide (k - 1 = 0)) ∧ t.zf = some (decide (k - 1 = 0))) :=
  (leafU (Q := fun t => Pre L B Z len N args sp (fun g m' => C (w32 m' B 100) ∧
      g .esi = BitVec.ofNat 32 (k - 1) ∧ True) t ∧ t.zf = some (decide (k - 1 = 0))) hL (fun s ps => by
    have hb := ps.1
    refine VG.Proof.Weierstrass.X86.wp_decCounter hk ps.2.2.2.1 fun v₁ cv₁ kv₁ mv₁ => ?_
    refine VG.Proof.Weierstrass.X86.wp_testCounter (by omega) cv₁ fun z F zf => WP.block_nil ?_
    have mz : z.mem = s.mem := F.mem.trans mv₁
    have Kz : Keeps [.esi] s z := kv₁.trans (F.keeps _)
    refine ⟨⟨hb.keep Kz (by decide) (by decide) (o := 160) (c := 0) (by rw [mz]; exact Outside.refl _ _ _ _)
      (Nat.le_refl _) (by have := hb.fits16; omega), ps.2.1.keep Kz (by decide) (by rw [mz]; exact Outside.refl _ _ _ _),
      by rw [mz]; exact ps.2.2.1, by rw [F.gpr]; exact cv₁, trivial⟩, zf⟩) h).mono
    (fun _ _ h => h) fun _ _ ⟨⟨a, za⟩, ⟨b, zb⟩⟩ => ⟨⟨a, b⟩, za, zb⟩

end VG.Proof.Rsa.X86.InvBatchRt.Time
