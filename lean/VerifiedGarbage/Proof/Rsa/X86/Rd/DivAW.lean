module

public import VerifiedGarbage.Proof.Rsa.X86.Rd.Ops
public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Prep
public import VerifiedGarbage.Proof.Bignum.ShiftStages
public import VerifiedGarbage.Spec.Rsa.RecoverDet
public import VerifiedGarbage.Proof.Rsa.BoolNat
public import VerifiedGarbage.Proof.Rsa.Sub32
import VerifiedGarbage.Proof.Rsa.X86.Rd.Loops
import VerifiedGarbage.Proof.Rsa.X86.Rd.Move
import VerifiedGarbage.Proof.Rsa.X86.Rd.TwosW
import VerifiedGarbage.Proof.Rsa.X86.Rd.DivQ
import VerifiedGarbage.Proof.Rsa.X86.Rd.DivBW
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Half
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Zero
import VerifiedGarbage.Proof.Rsa.X86.WordRt.Mul
import VerifiedGarbage.Proof.Framework.Omega

/-! # `m = ⌊a / n⌋` and `r = a mod n` on i686

`RecoverDetRt.divA`: `n` widened (`wideN`), `n` and the dividend `a` (`W + 1` words) doubled until
`n`'s word `W' - 1` has its top bit set (`normA`, `z` times, counted in `sZ`), then divided by words
(`wordDivQ … true`): the quotient `⌊a 2^z / n 2^z⌋ = ⌊a / n⌋` in `wA`'s low words, the rest of them
cleared (`clearQTop`), and the remainder `(a mod n) 2^z` halved back `z` times (`unnormA`); then `n`
widened again and whether `m < n`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot aM sB
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.RecoverDetRt hiding aN aP aQ
open VG.Impl.Rsa.X86.Recover (aN)
open VG.Proof.Rsa.X86.Keys
open VG.Spec.Rsa (isqrt)
open VG.Proof.Rsa (b2n sub32)
open VG.Impl.Mont.X86 (sc at_)
open VG.Proof.Mont.X86.Rt (PtrAt readSrc_ptr ptr_add)
open VG.Proof.Rsa.X86.WordRt (MLen wq)

/-! ## Helpers -/

/-- `test d, imm`: ZF is `d &&& v = 0`. -/
theorem wp_testI {s : State} {is : List Instr} {Q : State → Prop} {d : Reg} {v : BitVec 32}
    (k : ∀ s', Fupd s s' → s'.zf = some (s.gpr d &&& v == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .test d (.imm v) :: is)) s Q :=
  VG.X86.Wp.cons rfl (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl)

/-- A word's top bit clear. -/
theorem topBit_clear (x : BitVec 32) :
    (x &&& BitVec.ofNat 32 0x80000000 == 0) = decide (x.toNat < 2 ^ 31) := by
  have hx := x.isLt
  have key : x.toNat &&& 2 ^ 31 = x.toNat / 2 ^ 31 % 2 * 2 ^ 31 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow]
    rcases Nat.mod_two_eq_zero_or_one (x.toNat / 2 ^ 31) with e | e
    · rw [e, Nat.zero_mul, Nat.zero_testBit]
      by_cases hi : 31 = i
      · subst hi; simp [Nat.testBit_eq_decide_div_mod_eq, e]
      · simp [hi]
    · rw [e, Nat.one_mul, Nat.testBit_two_pow]
      by_cases hi : 31 = i
      · subst hi; simp [Nat.testBit_eq_decide_div_mod_eq, e]
      · simp [hi]
  have e : (x &&& BitVec.ofNat 32 0x80000000).toNat = x.toNat / 2 ^ 31 % 2 * 2 ^ 31 := by
    rw [BitVec.toNat_and, show (BitVec.ofNat 32 0x80000000).toNat = 2 ^ 31 from rfl, key]
  by_cases h : x.toNat < 2 ^ 31
  · have z : x.toNat / 2 ^ 31 = 0 := Nat.div_eq_of_lt h
    rw [z] at e
    simp only [h, decide_true, beq_iff_eq]
    exact BitVec.eq_of_toNat_eq (by rw [e]; rfl)
  · have z : x.toNat / 2 ^ 31 = 1 := by omega
    rw [z] at e
    simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro c; rw [c] at e; simp at e

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

/-- `wideN`: `n` (narrow `aN`) into the wide `wN`, its extra word zero; `wA`'s extra word kept. -/
theorem KS.wideN_ok (h : KS g s0 A live AW liveW V ls s) (hN : aN ∈ live) (hl : ∀ i ∈ live, i / 2 ≠ wN)
    (hlW : ∀ j ∈ liveW, j ≠ wN) :
    WP isa wideN s fun t =>
      KS g s0 A live (upd (upd AW wN 0) wN (A aN)) (wN :: liveW) V ls t ∧
      w32 t.mem g.B (arr g.W wN + 4 * g.W) = 0 ∧
      w32 t.mem g.B (arr g.W wA + 4 * g.W) = w32 s.mem g.B (arr g.W wA + 4 * g.W) := by
  have fA := h.wsW.fit64 (j := wA) (by decide)
  have e17 := arr_end (w := g.W) (show wA < wN by decide)
  have e19 : arr g.W wN = arr g.w (2 * wN) := arr_W' g wN
  have wW : g.W = 2 * g.w + 2 := rfl
  simp only [S] at e17
  unfold wideN
  refine WP.seq (WP.mono (WP.and (h.zeroWide_W (j := wN) (by decide) hl)
    (VG.Proof.Rsa.X86.KeyRt.zeroWide_ok h.rtW (j := wN) (by decide))) fun u ⟨⟨hu, z⟩, ⟨_, ku, _, _⟩⟩ => ?_)
  rw [kw_wid] at ku
  have hu' := hu.mono (liveW' := liveW) (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨List.mem_cons_of_mem _ hj, rfl⟩)
    (fun d hd => ⟨hd, rfl⟩)
  refine WP.mono (WP.and (hu'.widen (k := wN) (a := aN) (by decide) hN (by decide) z hl hlW)
    (copyOut_ok hu'.rt (o := 2 * wN) (a := aN) (by decide) (hu'.live_lt aN hN) (by decide)))
    fun v ⟨⟨hv, top⟩, ⟨_, Ov, _, _⟩⟩ => ⟨hv, top, ?_⟩
  rw [kw_nar] at Ov
  change Outside g.B (arr g.w (2 * wN)) (4 * g.w) u.mem v.mem at Ov
  have dj : arr g.W wA + 4 * g.W + 4 ≤ arr g.w (2 * wN) := by rw [← e19]; omega
  rw [Ov.w32 (.inl dj) (by simp only [S] at fA; omega)]
  have e := ku.word (j := wA) (i := g.W) (by show 4 * g.W + 4 ≤ 4 * (g.W + 2); omega) (by decide) (by simp) fA
  exact e

/-- `topBit`: ZF set exactly where the top bit of `n`'s word `W' - 1` is clear. -/
theorem KS.topBit_ok {a : Nat} {is : List Instr} {Q : State → Prop} (h : KS g s0 A live AW liveW V ls s)
    (hm : MLen s g.B g.Z VG.Impl.Rsa.X86.RecoverDetRt.nl a) (hN : wN ∈ liveW) (hw1 : 1 ≤ wq a)
    (hw : wq a ≤ g.w)
    (k : ∀ t, KS g s0 A live AW liveW V ls t → t.mem = s.mem →
      t.zf = some (decide (AW wN % 2 ^ (32 * wq a) / 2 ^ (32 * (wq a - 1)) < 2 ^ 31)) →
      WP isa (.block is) t Q) :
    WP isa (.block (topBit ++ is)) s Q := by
  have hW := h.rtW
  have nw := hW.ws.workspace.nowrap
  have fa := h.wsW.arr_fit (j := wN) (by decide)
  have wW : g.W = 2 * g.w + 2 := rfl
  simp only [S] at fa
  unfold topBit
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine VG.Proof.Rsa.X86.WordRt.topPtr_ok hW hm (j := wN) (i := 1) (r := .ebx) (t := .ecx)
    (by decide) (by decide) (by decide) (by decide) (by decide) hw1 (by rw [kw_wid]; change wq a ≤ g.W + 2; omega)
    fun u₁ U₁ m₁ p₁ _ => ?_
  rw [kw_wid] at p₁
  change PtrAt u₁ g.B .ebx (arr g.W wN + 4 * wq a - 4 * 1) at p₁
  refine wp_movS (readSrc_ptr (h.rt.rt.of_wr U₁.2.2) p₁ (d := 0) (by omega)) fun u₂ U₂ _ =>
    wp_testI fun u₃ F₃ z₃ => k u₃ ?_ (by rw [F₃.mem, U₂.mem, m₁]) ?_
  · exact h.of_rest (rs := opRegs) ((U₁.mono (by decide)).trans ((U₂.keeps.mono (by decide)).trans
      ⟨fun r _ => by rw [F₃.gpr], F₃.rd, F₃.wr⟩)) (fun x hx => hx) (by rw [F₃.mem, U₂.mem, m₁])
  · rw [z₃, topBit_clear, U₂.gpr, m₁, Nat.add_zero,
      show arr g.W wN + 4 * wq a - 4 * 1 = arr g.W wN + 4 * (wq a - 1) by omega]
    change some (decide (w32 s.mem g.B (arr g.W wN + 4 * (wq a - 1)) < 2 ^ 31)) = _
    have e := val32_top (m := s.mem) (B := g.B) (d := arr g.W wN) (K := g.W - wq a) hw1
    rw [show wq a + (g.W - wq a) = g.W by omega] at e
    rw [← h.arrsW wN hN]
    change _ = some (decide (val32 s.mem g.B (arr g.W wN) g.W % _ / _ < _))
    rw [e]


/-- `[wA]` doubled over its `W + 1` words (the extra word too). -/
theorem KS.dblX (h : KS g s0 A live AW liveW V ls s) (hA : wA ∈ liveW) (hl : ∀ i ∈ live, i / 2 ≠ wA)
    {X : Nat} (hX : val32 s.mem g.B (arr g.W wA) (g.W + 1) = X) (hX2 : 2 * X < 2 ^ (32 * (g.W + 1))) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.chain wid .adc wA wA wA true) s fun t =>
      KS g s0 A live (upd AW wA (2 * X % 2 ^ (32 * g.W))) (wA :: liveW) V ls t ∧
      val32 t.mem g.B (arr g.W wA) (g.W + 1) = 2 * X := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.chainAdd_ok h.rtW (o := wA) (a := wA) (b := wA)
    (h.liveW_lt wA hA) (h.liveW_lt wA hA) (h.liveW_lt wA hA) true) fun t ⟨_, k, ⟨c, _, v⟩, r⟩ => ?_
  simp only [VG.Proof.Rsa.X86.KeyRt.kk, Bool.toNat_true] at v
  rw [kw_wid] at k v
  change val32 t.mem g.B (arr g.W wA) (g.W + 1) + _ = val32 s.mem g.B (arr g.W wA) (g.W + 1) +
    val32 s.mem g.B (arr g.W wA) (g.W + 1) at v
  rw [hX] at v
  obtain ⟨xv, _⟩ := sum_carry (val32_lt _ _ _ _) v
  have e2 : val32 t.mem g.B (arr g.W wA) (g.W + 1) = 2 * X := by rw [xv, ← Nat.two_mul, Nat.mod_eq_of_lt hX2]
  refine ⟨h.write_W k (h.liveW_lt wA hA) (by simp) (r.mono (by decide)) ?_ hl (by simp), e2⟩
  change val32 t.mem g.B (arr g.W wA) g.W = _
  rw [← val32_mod (k := 1), e2]

end

/-! ## `normA` -/

/-- `normA`'s state after `z` doublings. -/
def NS (g : Geo) (s0 : State) (A : Nat → Nat) (ok n x z : Nat) (t : State) : Prop :=
  ∃ AW V, KS g s0 A [aZero, aN] AW [wN, wA] V [sZ, sOkDE] t ∧ V sZ = z ∧ V sOkDE = ok ∧
    AW wN = n * 2 ^ z ∧ AW wA = x * 2 ^ z % 2 ^ (32 * g.W) ∧
    val32 t.mem g.B (arr g.W wA) (g.W + 1) = x * 2 ^ z

/-- A word below `2^(32 W')`: its word `W' - 1` is below `2^31` exactly when it is below
`2^(32 W' - 1)`. -/
theorem top_lt_iff {v W' : Nat} (hv : v < 2 ^ (32 * W')) (hW : 1 ≤ W') :
    v % 2 ^ (32 * W') / 2 ^ (32 * (W' - 1)) < 2 ^ 31 ↔ v < 2 ^ (32 * W' - 1) := by
  rw [Nat.mod_eq_of_lt hv, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add,
    show 31 + 32 * (W' - 1) = 32 * W' - 1 by omega]

section
variable {g : Geo} {s0 : State} {A : Nat → Nat}

/-- A doubling of `normA`'s loop, and its test of `n`'s top bit. -/
theorem normStep_ok {ok n x z a : Nat} {t : State} (h : NS g s0 A ok n x z t)
    (ha : g.args VG.Impl.Rsa.X86.RecoverDetRt.nl = BitVec.ofNat 32 a) (ha1 : a ≤ 1024)
    (hw1 : 1 ≤ wq a) (hw : wq a ≤ g.w) (hx : x < 2 ^ (32 * g.W)) (hz : z < 31)
    (hn : n * 2 ^ (z + 1) < 2 ^ (32 * wq a)) :
    WP isa (seqs [VG.Impl.Rsa.X86.KeyRt.chain wid .adc wN wN wN false,
      VG.Impl.Rsa.X86.KeyRt.chain wid .adc wA wA wA true,
      .block (([.mov .eax (.mem (sc sZ)), .alu .add .eax (.imm 1), .store (sc sZ) .eax] : List Instr) ++ topBit)])
      t fun u =>
      NS g s0 A ok n x (z + 1) u ∧
        u.zf = some (decide (n * 2 ^ (z + 1) < 2 ^ (32 * wq a - 1))) := by
  obtain ⟨AW, V, h, hzV, hok, hN, hA, hX⟩ := h
  have pw : 2 ^ (32 * wq a) ≤ 2 ^ (32 * g.W) := Nat.pow_le_pow_right (by decide)
    (by simp only [Geo.W, VG.Impl.Rsa.X86.Recover.wide]; simp only [Geo.w] at hw; omega)
  have fA := h.wsW.fit64 (j := wA) (by decide)
  simp only [seqs]
  -- `n` doubled.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.KeyRt.chainAdd_ok h.rtW (o := wN) (a := wN) (b := wN)
    (by decide) (by decide) (by decide) false) fun t₁ ⟨_, k₁, ⟨c₁, _, v₁⟩, r₁⟩ => ?_)
  simp only [VG.Proof.Rsa.X86.KeyRt.kk, Bool.toNat_false, Nat.add_zero] at v₁
  rw [kw_wid] at k₁ v₁
  change num t₁.mem g.B g.W wN + _ = num t.mem g.B g.W wN + num t.mem g.B g.W wN at v₁
  rw [h.arrsW wN (by simp), hN] at v₁
  obtain ⟨xv₁, _⟩ := sum_carry (val32_lt _ _ _ _) v₁
  have e₁ : num t₁.mem g.B g.W wN = n * 2 ^ (z + 1) := by
    change val32 t₁.mem g.B (arr g.W wN) g.W = _
    rw [xv₁, ← Nat.two_mul, Nat.mul_left_comm, ← Nat.pow_succ']; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hn pw)
  have h₁ := h.write_W k₁ (by decide) (by simp) (r₁.mono (by decide)) e₁ (by decide) (by simp)
  have X₁ : val32 t₁.mem g.B (arr g.W wA) (g.W + 1) = x * 2 ^ z := by
    rw [← hX]
    exact val32_congr fun i hi => k₁.word (j := wA) (i := i) (by show 4 * i + 4 ≤ 4 * (g.W + 2); omega) (by decide) (by simp) fA
  -- `a` doubled over `W + 1` words.
  have X2 : 2 * (x * 2 ^ z) < 2 ^ (32 * (g.W + 1)) := by
    have e : 2 * (x * 2 ^ z) = x * 2 ^ (z + 1) := by rw [Nat.mul_left_comm, ← Nat.pow_succ']
    rw [e]
    calc x * 2 ^ (z + 1) < 2 ^ (32 * g.W) * 2 ^ (z + 1) := Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos _)
      _ = 2 ^ (32 * g.W + (z + 1)) := (Nat.pow_add _ _ _).symm
      _ ≤ 2 ^ (32 * (g.W + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
  refine WP.seq (WP.mono (h₁.dblX (by simp) (by decide) X₁ X2) fun t₂ ⟨h₂, X₂⟩ => ?_)
  -- `sZ := z + 1`, then the test.
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (h₂.readSlot (d := sZ) (by simp)) fun u₁ U₁ _ => wp_addS rfl fun u₂ U₂ _ => ?_
  have h₂' := h₂.of_rest (rs := opRegs) ((U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide)))
    (fun x hx => hx) (by rw [U₂.mem, U₁.mem])
  have ez : (u₂.gpr .eax).toNat = z + 1 := by
    rw [U₂.gpr, U₁.gpr, BitVec.toNat_add, hzV, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (show z < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show z + 1 < 2 ^ 32 by omega)]
  refine storeHdr h₂'.ws (d := sZ) (by decide) .eax fun u₃ K₃ e₃ k₃ _ _ => ?_
  rw [ez] at e₃
  have h₃ := (h₂'.slot1 K₃ (by decide) (k₃.mono (by decide)) e₃).mono (ls' := [sZ, sOkDE])
    (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨List.mem_cons_of_mem _ hd, rfl⟩)
  rw [show topBit = topBit ++ [] from (List.append_nil _).symm]
  refine KS.topBit_ok h₃ (h₃.mlen ha ha1) (by simp) hw1 hw fun u₄ h₄ m₄ zf₄ => WP.block_nil ⟨?_, ?_⟩
  · refine ⟨_, _, h₄.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨by simp at hj ⊢; omega, rfl⟩)
      (fun d hd => ⟨hd, rfl⟩),
      upd_self .., by rw [upd_ne _ _ (by decide), hok], ?_, ?_, ?_⟩
    · rw [upd_ne _ _ (by decide), upd_self]
    · rw [upd_self, Nat.mul_left_comm, ← Nat.pow_succ']
    · have X₄ : val32 u₄.mem g.B (arr g.W wA) (g.W + 1) = val32 t₂.mem g.B (arr g.W wA) (g.W + 1) := by
        rw [m₄, show t₂.mem = u₂.mem by rw [U₂.mem, U₁.mem]]
        exact val32_congr fun i hi => K₃.toW.word (j := wA) (i := i)
          (by show 4 * i + 4 ≤ 4 * (2 * g.w + 2 + 2); have : g.W = 2 * g.w + 2 := rfl; omega) (by simp)
          (by decide) fA
      rw [X₄, X₂, Nat.mul_left_comm, ← Nat.pow_succ']
  · rw [zf₄, upd_ne _ _ (by decide), upd_self]
    simp only [top_lt_iff hn hw1]


theorem z_bound {n y W' : Nat} (hW : 1 ≤ W') (hn0 : 2 ^ (32 * (W' - 1)) ≤ n)
    (c : n * 2 ^ y < 2 ^ (32 * W' - 1)) : y < 31 := by
  have : 2 ^ (32 * (W' - 1) + y) < 2 ^ (32 * (W' - 1) + 31) :=
    calc 2 ^ (32 * (W' - 1) + y) = 2 ^ (32 * (W' - 1)) * 2 ^ y := Nat.pow_add _ _ _
      _ ≤ n * 2 ^ y := Nat.mul_le_mul_right _ hn0
      _ < 2 ^ (32 * W' - 1) := c
      _ = 2 ^ (32 * (W' - 1) + 31) := by rw [show 32 * W' - 1 = 32 * (W' - 1) + 31 by omega]
  have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp this
  omega

/-- `normA`: `n` and `a` doubled `z` times, until `n`'s word `W' - 1` has its top bit set. -/
theorem normA_ok {V AW : Nat → Nat} {n x a : Nat} {t : State}
    (h : KS g s0 A [aZero, aN] AW [wN, wA] V [sOkDE] t) (hN : AW wN = n) (hA : AW wA = x)
    (hxt : w32 t.mem g.B (arr g.W wA + 4 * g.W) = 0)
    (ha : g.args VG.Impl.Rsa.X86.RecoverDetRt.nl = BitVec.ofNat 32 a) (ha1 : a ≤ 1024)
    (hw1 : 1 ≤ wq a) (hw : wq a ≤ g.w) (hx : x < 2 ^ (32 * g.W))
    (hn0 : 2 ^ (32 * (wq a - 1)) ≤ n) (hn' : n < 2 ^ (32 * wq a)) :
    WP isa normA t fun u => ∃ z, z ≤ 31 ∧ NS g s0 A (V sOkDE) n x z u ∧
      2 ^ (32 * wq a - 1) ≤ n * 2 ^ z ∧ n * 2 ^ z < 2 ^ (32 * wq a) := by
  have fA := h.wsW.fit64 (j := wA) (by decide)
  unfold normA
  simp only [seqs, List.cons_append, List.nil_append]
  refine WP.seq (wp_movS (v := 0) rfl fun u₁ U₁ _ => ?_)
  have h₁ := h.of_rest U₁.keeps (by decide) U₁.mem
  refine storeHdr h₁.ws (d := sZ) (by decide) .eax fun u₂ K₂ e₂ k₂ _ _ => ?_
  have h₂ := h₁.slot1 K₂ (by decide) (k₂.mono (by decide)) e₂
  rw [show topBit = topBit ++ [] from (List.append_nil _).symm]
  refine KS.topBit_ok h₂ (h₂.mlen ha ha1) (by simp) hw1 hw fun u₃ h₃ m₃ zf₃ => WP.block_nil ?_
  have X₃ : val32 u₃.mem g.B (arr g.W wA) (g.W + 1) = x := by
    rw [m₃, val32_succ]
    have k₂W := K₂.toW
    rw [U₁.mem] at k₂W
    have e := k₂W.word (j := wA) (i := g.W) (by show 4 * g.W + 4 ≤ 4 * (g.W + 2); omega) (by simp) (by decide) fA
    change w32 u₂.mem g.B (arr g.W wA + 4 * g.W) = w32 t.mem g.B (arr g.W wA + 4 * g.W) at e
    rw [e, hxt]
    change val32 u₂.mem g.B (arr g.W wA) g.W + 0 = x
    rw [Nat.add_zero, ← hA, ← h₂.arrsW wA (by simp)]
  have P₀ : NS g s0 A (V sOkDE) n x 0 u₃ :=
    ⟨_, _, h₃, by rw [upd_self, U₁.gpr]; rfl, by rw [upd_ne _ _ (by decide)], by rw [hN, Nat.pow_zero, Nat.mul_one],
      by rw [hA, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hx], by rw [X₃, Nat.pow_zero, Nat.mul_one]⟩
  simp only [hN, top_lt_iff hn' hw1] at zf₃
  refine WP.ite (!decide (n < 2 ^ (32 * wq a - 1))) (by simp only [eval, zf₃, Option.map_some]) (fun hb => ?_)
    (fun hb => ?_)
  · refine WP.block_nil ⟨0, by omega, P₀, ?_, by simpa using hn'⟩
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at hb
    simpa using hb
  · simp only [Bool.not_eq_false', decide_eq_true_eq] at hb
    refine WP.loop (M := isa) (fun k u => ∃ z, k = 31 - z ∧ z < 31 ∧ NS g s0 A (V sOkDE) n x z u ∧
      n * 2 ^ z < 2 ^ (32 * wq a - 1)) ?_ (31 - 0) u₃ ⟨0, rfl, by decide, P₀, by simpa using hb⟩
    rintro k u ⟨z, rfl, hz, P, hlt⟩
    have hn2 : n * 2 ^ (z + 1) < 2 ^ (32 * wq a) := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]
      have : 2 ^ (32 * wq a) = 2 ^ (32 * wq a - 1) * 2 := by
        rw [← Nat.pow_succ]; exact congrArg (2 ^ ·) (by omega)
      omega
    refine WP.mono (normStep_ok P ha ha1 hw1 hw hx hz hn2) fun u' ⟨P', zf'⟩ => ?_
    by_cases c : n * 2 ^ (z + 1) < 2 ^ (32 * wq a - 1)
    · refine .inr ⟨by simp only [eval, zf', c, decide_true], 31 - (z + 1), by omega, z + 1, rfl,
        z_bound hw1 hn0 c, P', c⟩
    · refine .inl ⟨by simp only [eval, zf', c, decide_false], z + 1, by omega, P', by omega, hn2⟩

end

/-! ## `clearQTop` -/

section
open VG.Proof.Mont.X86.Rt (ea_ptr ws_write)

/-- After words `0, …, j - 1` of `K` cleared from `d`. -/
structure ZI (s : State) (B : Addr) (d K j : Nat) (u : State) : Prop where
  si : PtrAt u B .esi (d + 4 * j)
  dx : (u.gpr .edx).toNat = 4 * (K - j)
  keep : Keeps [.eax, .edx, .esi] s u
  out : Outside B d (4 * j) s.mem u.mem
  zero : ∀ i < j, w32 u.mem B (d + 4 * i) = 0

theorem zeroStep_ok {B : Addr} {s u : State} {bytes d K j : Nat} (ws : VG.Proof.Mont.X86.Rt.Ws s B bytes)
    (nw : B.toNat + bytes ≤ 2 ^ 32) (hd : d + 4 * K ≤ bytes) (hj : j < K) (I : ZI s B d K j u) :
    WP isa (.block [.mov .eax (.imm 0), .store (at_ .esi 0) .eax, .alu .add .esi (.imm 4), .alu .sub .edx (.imm 4)])
      u fun u' => u'.zf = some (decide (j + 1 = K)) ∧ ZI s B d K (j + 1) u' := by
  have wsu := ws.of_wr I.keep.2.2
  refine wp_movS (v := 0) rfl fun u₁ U₁ _ => ?_
  have ws₁ := wsu.of_wr U₁.wr
  have p₁ : PtrAt u₁ B .esi (d + 4 * j) := by rw [PtrAt, U₁.other _ (by decide)]; exact I.si
  refine wp_storeS (ea_ptr ws₁ p₁ (d := 0) (by omega)) (ws_write ws₁ (by omega)) fun u₂ M₂ => ?_
  refine wp_addS rfl fun u₃ U₃ _ => VG.Proof.Mont.X86.Rt.wp_subZ rfl fun u₄ U₄ z₄ => WP.block_nil ?_
  have hc := VG.Proof.Mont.X86.Rt.count_zf (N := K) (x := u.gpr .edx) I.dx hj
  have dx₃ : u₃.gpr .edx = u.gpr .edx := by
    rw [U₃.other _ (by decide), M₂.gpr, U₁.other _ (by decide)]
  have m₄ : u₄.mem = u.mem.writeW (off B (d + 4 * j)) (0 : BitVec 32) := by
    rw [U₄.mem, U₃.mem, M₂.mem, U₁.mem, U₁.gpr, Nat.add_zero]
  have O := writeW32_outside u.mem B (d := d + 4 * j) (0 : BitVec 32) (by omega)
  rw [← m₄] at O
  refine ⟨by rw [z₄, dx₃, hc.2], ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [PtrAt, U₄.other _ (by decide), U₃.gpr, ptr_add (s := u₂) (x := d + 4 * j)
      (by rw [PtrAt, M₂.gpr]; exact p₁)]
    congr 2
  · rw [U₄.gpr, dx₃, hc.1]
  · exact I.keep.trans ((U₁.keeps.mono (by decide)).trans ((M₂.keeps _).trans
      ((U₃.keeps.mono (by decide)).trans (U₄.keeps.mono (by decide)))))
  · exact (I.out.mono (by omega) (by omega)).trans (O.mono (by omega) (by omega))
  · intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [O.w32 (.inl (by omega)) (by omega)]; exact I.zero i hi
    · rw [m₄, w32_write_self]; rfl

theorem zeroLoop_ok {B : Addr} {s u : State} {bytes d K : Nat} (ws : VG.Proof.Mont.X86.Rt.Ws s B bytes)
    (nw : B.toNat + bytes ≤ 2 ^ 32) (hd : d + 4 * K ≤ bytes) (hK : 0 < K) (I : ZI s B d K 0 u) :
    WP isa (.loop (.block [.mov .eax (.imm 0), .store (at_ .esi 0) .eax, .alu .add .esi (.imm 4),
      .alu .sub .edx (.imm 4)]) .ne) u (ZI s B d K K) := by
  refine WP.loop (M := isa) (fun n v => ∃ j, n = K - j ∧ j < K ∧ ZI s B d K j v) ?_ _ u ⟨0, rfl, hK, I⟩
  rintro n v ⟨j, rfl, hj, J⟩
  refine WP.mono (zeroStep_ok ws nw hd hj J) fun v' ⟨z, J'⟩ => ?_
  by_cases e : j + 1 = K
  · exact .inl ⟨by simp only [eval, z, e, decide_true, Option.map_some, Bool.not_true], e ▸ J'⟩
  · exact .inr ⟨by simp only [eval, z, e, decide_false, Option.map_some, Bool.not_false], K - (j + 1),
      by omega, j + 1, rfl, by omega, J'⟩

variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

/-- `clearQTop`: `[wA]`'s words `W - W' + 2, …, W + 1` cleared, so it holds its low `W - W' + 2`. -/
theorem KS.clearQTop_ok {a : Nat} (h : KS g s0 A live AW liveW V ls s)
    (hm : MLen s g.B g.Z VG.Impl.Rsa.X86.RecoverDetRt.nl a) (hl : ∀ j ∈ live, j / 2 ≠ wA)
    (hw2 : 2 ≤ wq a) (hw : wq a ≤ g.w) :
    WP isa clearQTop s fun t =>
      KS g s0 A live (upd AW wA (val32 s.mem g.B (arr g.W wA) (g.W - wq a + 2))) (wA :: liveW) V ls t := by
  have hW := h.rtW
  have nw := hW.ws.workspace.nowrap
  have fa := h.wsW.arr_fit (j := wA) (by decide)
  have wW : g.W = 2 * g.w + 2 := rfl
  have wb : g.w ≤ 258 := by
    have := h.upper; simp only [Geo.w, VG.Impl.Rsa.X86.Recover.width]; omega
  simp only [S] at fa
  unfold clearQTop
  simp only [seqs]
  refine WP.seq ?_
  simp only [List.append_assoc]
  refine VG.Proof.Rsa.X86.KeyRt.arrPtr_ok (VG.Proof.Rsa.X86.KeyRt.lenSrc hW) hW.lenLe hW.edi
    (r := .esi) (t := .edx) (j := wA) (by decide) (by decide) (by rw [kw_wid]; change arr g.W wA < 2 ^ 32; omega)
    fun u₁ U₁ m₁ p₁ _ => ?_
  rw [kw_wid] at p₁
  change PtrAt u₁ g.B .esi (arr g.W wA) at p₁
  have hW₁ := hW.keep U₁ (by decide) (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _)
  refine VG.Proof.Rsa.X86.KeyRt.bytesB_ok (VG.Proof.Rsa.X86.KeyRt.lenSrc hW₁) hW₁.lenLe (r := .eax)
    fun u₂ U₂ m₂ e₂ => ?_
  rw [kw_wid] at e₂
  change (u₂.gpr .eax).toNat = 4 * g.W at e₂
  simp only [List.cons_append, List.nil_append]
  refine wp_addS rfl fun u₃ U₃ _ => ?_
  have m₃ : u₃.mem = s.mem := by rw [U₃.mem, m₂, m₁]
  refine VG.Proof.Rsa.X86.WordRt.width4_ok (hm.keep (((U₁.mono (by decide)).trans ((U₂.mono (by decide)).trans
    (U₃.keeps.mono (by decide)))) : Keeps [.eax, .edx, .esi] s u₃) (by decide) (by rw [m₃]; exact Outside.refl _ _ _ _))
    (r := .edx) fun u₄ U₄ m₄ e₄ => ?_
  have w4 : 4 * wq a < 2 ^ 32 := by omega
  refine wp_subS rfl fun u₅ U₅ _ => wp_addS rfl fun u₆ U₆ _ => WP.block_nil ?_
  have e₃ : (u₃.gpr .esi).toNat = g.B.toNat + arr g.W wA + 4 * g.W := by
    rw [U₃.gpr, BitVec.toNat_add, U₂.1 .esi (by decide), p₁, e₂]
    have := g.B.isLt; omega
  have p₆ : PtrAt u₆ g.B .esi (arr g.W wA + 4 * (g.W - wq a + 2)) := by
    rw [PtrAt, U₆.gpr, BitVec.toNat_add, U₅.gpr, BitVec.toNat_sub, U₄.1 .esi (by decide), e₃,
      e₄, BitVec.toNat_ofNat, Nat.mod_eq_of_lt w4, show (8 : BitVec 32).toNat = 8 from rfl]
    omega
  have K₆ : Keeps [.eax, .edx, .esi] s u₆ := (U₁.mono (by decide)).trans ((U₂.mono (by decide)).trans
    ((U₃.keeps.mono (by decide)).trans ((U₄.mono (by decide)).trans ((U₅.keeps.mono (by decide)).trans
      (U₆.keeps.mono (by decide))))))
  have m₆ : u₆.mem = s.mem := by rw [U₆.mem, U₅.mem, m₄, m₃]
  have I₀ : ZI u₆ g.B (arr g.W wA + 4 * (g.W - wq a + 2)) (wq a) 0 u₆ := by
    refine ⟨by rw [Nat.mul_zero, Nat.add_zero]; exact p₆, ?_, Keeps.refl _ _, Outside.refl _ _ _ _,
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    rw [U₆.other _ (by decide), U₅.other _ (by decide), e₄, BitVec.toNat_ofNat, Nat.mod_eq_of_lt w4, Nat.sub_zero]
  refine WP.mono (zeroLoop_ok (h.rt.rt.of_keeps K₆) nw (by omega) (by omega) I₀) fun t I => ?_
  have O : Outside g.B (arr g.W wA + 4 * (g.W - wq a + 2)) (4 * wq a) s.mem t.mem := by rw [← m₆]; exact I.out
  have k : Keep g.B g.W [wA] [] s.mem t.mem :=
    Keep.of_arr (d := 4 * (g.W - wq a + 2)) O (by simp only [S]; omega) (by simp)
  refine h.write_W k (by decide) (by simp) ((K₆.trans I.keep).mono (by decide)) ?_ hl (by simp)
  change val32 t.mem g.B (arr g.W wA) g.W = _
  have e := val32_append t.mem g.B (arr g.W wA) (g.W - wq a + 2) (wq a - 2)
  rw [show g.W - wq a + 2 + (wq a - 2) = g.W by omega] at e
  have lowEq : val32 t.mem g.B (arr g.W wA) (g.W - wq a + 2) =
      val32 s.mem g.B (arr g.W wA) (g.W - wq a + 2) := by
    rw [← m₆]; exact I.out.val32 (.inl (Nat.le_refl _)) (by omega)
  have hiZ : val32 t.mem g.B (arr g.W wA + 4 * (g.W - wq a + 2)) (wq a - 2) = 0 :=
    VG.Proof.Rsa.X86.WordRt.val32_eq_zero fun i hi => I.zero i (by omega)
  rw [e, lowEq, hiZ, Nat.mul_zero, Nat.add_zero]

end

/-! ## `unnormA` -/

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

theorem ofNat_beq_zero {z : Nat} (hz : z < 2 ^ 32) : (BitVec.ofNat 32 z == 0) = decide (z = 0) := by
  by_cases h : z = 0
  · subst h; rfl
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro c; have := congrArg BitVec.toNat c; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hz] at this
    exact h this

/-- `unnormA`: `[wR] = R 2^z` halved `z` times (`z` in `sZ`). -/
theorem KS.unnormA_ok {z R : Nat} (h : KS g s0 A live AW liveW V ls s) (hS : sZ ∈ ls) (hVS : V sZ = z)
    (hR : wR ∈ liveW) (hRv : AW wR = R * 2 ^ z) (hz : z < 2 ^ 32) (hl : ∀ j ∈ live, j / 2 ≠ wR) :
    WP isa unnormA s fun t => ∃ V', KS g s0 A live (upd AW wR R) (wR :: liveW) V' (sZ :: ls) t ∧
      ∀ d, d ≠ sZ → V' d = V d := by
  unfold unnormA
  simp only [seqs]
  refine WP.seq (wp_movS (h.readSlot hS) fun u₁ U₁ _ => VG.X86.Wp.wp_test fun u₂ F₂ z₂ => WP.block_nil ?_)
  have h₂ := h.of_rest (rs := opRegs) ((U₁.keeps.mono (by decide)).trans ⟨fun r _ => by rw [F₂.gpr], F₂.rd, F₂.wr⟩)
    (fun x hx => hx) (by rw [F₂.mem, U₁.mem])
  rw [U₁.gpr, BitVec.and_self, hVS, ofNat_beq_zero hz] at z₂
  refine WP.ite (decide (z = 0)) (by simp only [eval, z₂]) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    refine WP.block_nil ⟨V, h₂.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨?_, ?_⟩) (fun d hd => ⟨?_, rfl⟩),
      fun _ _ => rfl⟩
    · exact (List.mem_cons.mp hj).elim (fun e => e ▸ hR) id
    · by_cases e : j = wR
      · subst e; rw [upd_self, hRv, Nat.pow_zero, Nat.mul_one]
      · rw [upd_ne _ _ e]
    · exact (List.mem_cons.mp hd).elim (fun e => e ▸ hS) id
  simp only [decide_eq_false_iff_not] at hb
  have I₀ : KS g s0 A live (upd AW wR (R * 2 ^ (z - 0))) (wR :: liveW) (upd V sZ (z - 0)) (sZ :: ls) u₂ := by
    refine h₂.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨?_, ?_⟩) (fun d hd => ⟨?_, ?_⟩)
    · exact (List.mem_cons.mp hj).elim (fun e => e ▸ hR) id
    · by_cases e : j = wR
      · subst e; rw [upd_self, hRv, Nat.sub_zero]
      · rw [upd_ne _ _ e]
    · exact (List.mem_cons.mp hd).elim (fun e => e ▸ hS) id
    · by_cases e : d = sZ
      · subst e; rw [upd_self, hVS, Nat.sub_zero]
      · rw [upd_ne _ _ e]
  refine WP.loop (M := isa) (fun k u => ∃ i, k = z - i ∧ i < z ∧
    KS g s0 A live (upd AW wR (R * 2 ^ (z - i))) (wR :: liveW) (upd V sZ (z - i)) (sZ :: ls) u) ?_ (z - 0) u₂
    ⟨0, rfl, by omega, I₀⟩
  rintro k u ⟨i, rfl, hi, P⟩
  refine WP.seq (wp_movS rfl fun u₁ U₁' _ => WP.block_nil ?_)
  have P₁ := P.of_rest U₁'.keeps (by decide) U₁'.mem
  refine WP.seq (WP.mono (P₁.half_W (j := wR) (by simp) (by rw [U₁'.gpr]; rfl) hl) fun u₂ ⟨P₂, _⟩ => ?_)
  refine wp_movS (P₂.readSlot (d := sZ) (by simp)) fun u₃ U₃ _ =>
    VG.Proof.Mont.X86.Rt.wp_subZ (v := 1) rfl fun u₄ U₄ z₄ => ?_
  have P₄ := P₂.of_rest (rs := opRegs) ((U₃.keeps.mono (by decide)).trans (U₄.keeps.mono (by decide)))
    (fun x hx => hx) (by rw [U₄.mem, U₃.mem])
  refine WP.mono (P₄.storeSlot (d := sZ) (by decide) .eax) fun t ⟨P₅, zf₅, _⟩ => ?_
  have ev : (u₄.gpr .eax).toNat = z - (i + 1) := by
    rw [U₄.gpr, U₃.gpr, upd_self, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show z - i < 2 ^ 32 by omega),
      show (1 : BitVec 32).toNat = 1 from rfl]
    omega
  rw [ev] at P₅
  have e2 : R * 2 ^ (z - i) / 2 = R * 2 ^ (z - (i + 1)) := by
    rw [show z - i = z - (i + 1) + 1 by omega, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_div_cancel _ (by decide)]
  have P₆ : KS g s0 A live (upd AW wR (R * 2 ^ (z - (i + 1)))) (wR :: liveW) (upd V sZ (z - (i + 1))) (sZ :: ls) t :=
    P₅.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨List.mem_cons_of_mem _ hj, by rw [upd_upd, upd_self, e2]⟩)
      (fun d hd => ⟨List.mem_cons_of_mem _ hd, by rw [upd_upd]⟩)
  have zz : (u₃.gpr .eax - 1 == 0) = decide (i + 1 = z) := by
    rw [U₃.gpr, upd_self]
    by_cases e : i + 1 = z
    · simp only [e, decide_true, beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show z - i < 2 ^ 32 by omega)]; simp; omega
    · simp only [e, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro c; have := congrArg BitVec.toNat c
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show z - i < 2 ^ 32 by omega)] at this; simp at this; omega
  rw [zz] at z₄
  by_cases e : i + 1 = z
  · refine .inl ⟨by simp only [eval, zf₅, z₄, e, decide_true, Option.map_some, Bool.not_true], upd V sZ 0, ?_,
      fun d hd => by rw [upd_ne _ _ hd]⟩
    rw [← e, Nat.sub_self] at P₆
    rw [Nat.pow_zero, Nat.mul_one] at P₆
    exact P₆
  · exact .inr ⟨by simp only [eval, zf₅, z₄, e, decide_false, Option.map_some, Bool.not_false], z - (i + 1),
      by omega, i + 1, rfl, by omega, P₆⟩

end

/-! ## `divA` -/

section
open VG.Proof.Rsa.X86.WordRt (mw)

/-- `divA`: `m = ⌊a / n⌋` (`wA`) and `r = a mod n` (`wR`), `n` wide again, and whether `m < n`. -/
theorem divA_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {n x a : Nat}
    (h : KS g s0 A [aZero, aN] AW [wA] V [sOkDE] s)
    (_hz : A aZero = 0) (hn : A aN = n) (hx : AW wA = x)
    (hxt : VG.Proof.Mont.w32 s.mem g.B (arr g.W wA + 4 * g.W) = 0)
    (ha : g.args VG.Impl.Rsa.X86.RecoverDetRt.nl = BitVec.ofNat 32 a) (ha0 : 64 ≤ a) (ha1 : a ≤ 1024)
    (haw : VG.Proof.Rsa.X86.WordRt.wq a ≤ g.w)
    (hn0 : 2 ^ (32 * (VG.Proof.Rsa.X86.WordRt.wq a - 1)) ≤ n)
    (hn' : n < 2 ^ (32 * VG.Proof.Rsa.X86.WordRt.wq a)) :
    WP isa divA s fun t => ∃ AW' V',
      KS g s0 A [aZero, aN] AW' [wA, wR, wN] V' [sLt, sOkDE] t ∧
      AW' wA = x / n ∧ AW' wR = x % n ∧ AW' wN = n ∧
      V' sLt = b2n (decide (x / n < n)) ∧ V' sOkDE = V sOkDE := by
  have hw1 : 16 ≤ wq a := by simp only [wq]; omega
  have hwq : wq a ≤ 256 := by simp only [wq]; omega
  have wW : g.W = 2 * g.w + 2 := rfl
  have pw : 2 ^ (32 * wq a) ≤ 2 ^ (32 * g.w) := Nat.pow_le_pow_right (by decide) (by omega)
  have pwW : 2 ^ (32 * g.w) ≤ 2 ^ (32 * g.W) := Nat.pow_le_pow_right (by decide) (by omega)
  have kwW : VG.Proof.Rsa.X86.KeyRt.kw (16 * g.n + 24) = g.W := kw_wid _
  have xlt : x < 2 ^ (32 * g.W) := by rw [← hx, ← h.arrsW wA (by simp)]; exact val32_lt _ _ _ _
  have n0 : 0 < n := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hn0
  unfold divA
  simp only [seqs]
  -- `n` wide.
  refine WP.seq (WP.mono (h.wideN_ok (by simp) (by decide) (by decide)) fun t₁ ⟨h₁, _, ex₁⟩ => ?_)
  -- `n` and `a` normalized.
  refine WP.seq (WP.mono (normA_ok h₁ (by rw [upd_self, hn]) (by rw [upd_ne _ _ (by decide),
    upd_ne _ _ (by decide), hx]) (by rw [ex₁]; exact hxt) ha ha1 (by omega) haw xlt hn0 hn')
    fun t₂ ⟨z, hz31, P₂, top₂, lt₂⟩ => ?_)
  obtain ⟨AW₂, V₂, h₂, hz₂, hok₂, hN₂, hA₂, hX₂⟩ := P₂
  -- The division.
  refine WP.seq (WP.mono (wordDivQ_ok h₂.rtW (h₂.mlen ha ha1) (x := wA) (r := wR) (m := wN) (t := wDt)
    (extra := true) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by omega) (by rw [kwW]; omega))
    fun t₃ ⟨_, k₃, mw₃, mt₃, rem₃, quo₃, _, K₃⟩ => ?_)
  rw [kwW] at k₃ mw₃ mt₃ rem₃ quo₃
  simp only [xn, kwW, Bool.toNat_true] at rem₃ quo₃
  have eN2 : num t₂.mem g.B g.W wN = n * 2 ^ z := by rw [h₂.arrsW wN (by simp), hN₂]
  have low2 : val32 t₂.mem g.B (arr g.W wN) (wq a) = n * 2 ^ z := by
    have e := val32_mod (m := t₂.mem) (B := g.B) (arr g.W wN) (wq a) (g.W - wq a)
    rw [show wq a + (g.W - wq a) = g.W by omega] at e
    rw [← e]; change num t₂.mem g.B g.W wN % _ = _; rw [eN2, Nat.mod_eq_of_lt lt₂]
  have topw : 2 ^ 31 ≤ w32 t₂.mem g.B (arr g.W wN + 4 * (wq a - 1)) := by
    have e := val32_top (m := t₂.mem) (B := g.B) (d := arr g.W wN) (W' := wq a) (K := 0) (by omega)
    rw [Nat.add_zero, low2, Nat.mod_eq_of_lt lt₂] at e
    rw [← e, Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← Nat.pow_add,
      show 31 + 32 * (wq a - 1) = 32 * wq a - 1 by omega]
    exact top₂
  have low3 : val32 t₃.mem g.B (arr g.W wN) (wq a) = n * 2 ^ z := by
    rw [← low2]
    apply val32_congr
    intro j hj
    by_cases ej : j = wq a - 1
    · subst ej
      have lt32 := (t₂.mem.readW (off g.B (arr g.W wN + 4 * (wq a - 1))) 32).isLt
      have e := mt₃
      simp only [mw] at e
      change w32 t₃.mem g.B (arr g.W wN + 4 * (wq a - 1)) = w32 t₂.mem g.B (arr g.W wN + 4 * (wq a - 1))
      rw [e]
      have : w32 t₂.mem g.B (arr g.W wN + 4 * (wq a - 1)) < 2 ^ 32 := lt32
      omega
    · exact mw₃ j (by omega) ej
  rw [hX₂, low3, Nat.mul_mod_mul_right] at rem₃
  rw [hX₂, low3, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _),
    show g.W + 1 - wq a + 1 = g.W - wq a + 2 by omega] at quo₃
  -- Back to the stage's arrays.
  have h₂m := h₂.mono (AW' := AW₂) (liveW' := []) (fun j hj => ⟨hj, rfl⟩) (fun j hj => by simp at hj)
    (fun d hd => ⟨hd, rfl⟩)
  have h₃ : KS g s0 A [aZero, aN] (upd (upd AW₂ wA (num t₃.mem g.B g.W wA)) wR (num t₃.mem g.B g.W wR))
      [wA, wR] V₂ [sZ, sOkDE] t₃ :=
    h₂m.core k₃ (fun j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl <;> exact h₂m.wsW.arr_fit (by decide)) (by decide)
      (K₃.mono (by decide)) (h₂m.arrs_W k₃ (by decide) (by decide)) (by decide)
      (fun j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · rw [upd_ne _ _ (by decide), upd_self]
        · rw [upd_self])
      (by decide) (h₂m.sl_keep k₃ (by decide)) h₂m.ls_ok
  -- The quotient's top words cleared.
  refine WP.seq (WP.mono (h₃.clearQTop_ok (h₃.mlen ha ha1) (by decide) (by omega) haw) fun t₄ h₄ => ?_)
  rw [quo₃] at h₄
  -- The remainder halved back.
  refine WP.seq (WP.mono (h₄.unnormA_ok (z := z) (R := x % n) (by simp) hz₂ (by simp)
    (by rw [upd_ne _ _ (by decide), upd_self, rem₃]) (by omega) (by decide)) fun t₅ ⟨V₅, h₅, hV₅⟩ => ?_)
  -- `n` wide again.
  refine WP.seq (WP.mono (h₅.wideN_ok (by simp) (by decide) (by decide)) fun t₆ ⟨h₆, _, _⟩ => ?_)
  -- `m < n`.
  refine WP.seq (WP.mono (h₆.subWrap_W (o := wT) (a := wA) (b := wN) (by decide) (by simp) (by simp)
    (by decide) (by decide) (by decide)) fun t₇ ⟨h₇, b₇⟩ => ?_)
  refine WP.mono (h₇.storeSlot (d := sLt) (by decide) .ebx) fun t ⟨h₈, _, _⟩ => ?_
  rw [b₇] at h₈
  have hn₀ : A 32 = n := hn
  refine ⟨_, _, h₈.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨by simp at hj ⊢; omega, rfl⟩)
    (fun d hd => ⟨by simp at hd ⊢; omega, rfl⟩), ?_, ?_, ?_, ?_, ?_⟩
  · simp [upd, wA, wR, wN, wT]
  · simp [upd, wR, wN, wT]
  · simp [upd, wN, wT, aN, hn₀]
  · simp [upd, wA, wR, wN, aN, hn₀, sLt]
  · have h144 : V₅ 144 = V 144 := by rw [hV₅ 144 (by decide)]; exact hok₂
    simp [upd, sLt, sOkDE, h144]

end
end VG.Proof.Rsa.X86.Recover
