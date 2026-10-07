import VerifiedGarbage.Proof.Weierstrass.AArch64.CombSelect
import VerifiedGarbage.Proof.Weierstrass.AArch64.Ladder
import VerifiedGarbage.Proof.Weierstrass.CombLay
import VerifiedGarbage.Proof.Weierstrass.Law3

/-!
# The fixed-base comb on AArch64: what its digits and additions share

The registers the comb changes (`combClob`), the negation of `y` for a
negative digit (`signMask_ok`; `Rep.negY` is in `Law.lean`), where the selected entry `E` is
(`combLay_E`, `entryW_sub`), and the addition `A = A + E` by the complete
formulas (`combSum_ok`): what the comb from tables in memory
(`Proof/Weierstrass/AArch64/TComb.lean`) and ECDH's window method use.
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass CombCfg

/-- The registers the comb changes. -/
def combClob (n : Nat) : List Reg := .x19 :: .x9 :: maskRegs ++ clob n

/-! ## Representatives -/

/-! ## The digit's sign -/

theorem testBit_three (k j : Nat) : k.testBit (4 * j + 3) = decide (8 ≤ nib k j) := by
  have := nib_eq k j
  have h0 := Bool.toNat_le (k.testBit (4 * j))
  have h1 := Bool.toNat_le (k.testBit (4 * j + 1))
  have h2 := Bool.toNat_le (k.testBit (4 * j + 2))
  cases h3 : k.testBit (4 * j + 3) <;> simp only [h3, Bool.toNat_true, Bool.toNat_false] at this <;>
    simp only [decide_eq_true_eq, decide_eq_false_iff_not, Bool.false_eq, Bool.true_eq] <;> omega

theorem sign_byte (b : Bool) :
    ((((if b then 1 else 0 : BitVec 8)).setWidth 32).setWidth 64) - BitVec.ofNat 64 1 =
      bmask (!b) := by
  cases b <;> decide

/-- `x3` all ones if digit `j = x19` is negative. -/
theorem signMask_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (bits : Nat)
    {k j N : Nat} (hj : 4 * j + 4 ≤ N) (hN : bits + N ≤ size) (hb4 : bits + 3 < 4096)
    (hx : s.gpr .x19 = BitVec.ofNat 64 j)
    (hbits : ∀ t < N, s.mem (off base (bits + t)) = if k.testBit t then 1 else 0) :
    WP isa (.block (signMask bits)) s fun t =>
      t.gpr .x3 = bmask (decide (nib k j < 8)) ∧ Keeps [.x3, .x16] s t := by
  have hn := hs.nowrap
  rw [signMask, show ([.lsl .x .x16 .x19 2, .add .x .x16 .x0 .x16, .ldrb .x3 .x16 (bits + 3),
      .subImm .x .x3 .x3 1] : List Instr) = ([.lsl .x .x16 .x19 2, .add .x .x16 .x0 .x16] : List Instr) ++
      [.ldrb .x3 .x16 (bits + 3), .subImm .x .x3 .x3 1] from rfl, WP.block_append_iff]
  refine WP.mono (combIndex_ok s hs (by omega) hx) fun a ⟨a16, ka⟩ => ?_
  have hr : InRegions (a.rd ++ a.wr) (off base (bits + (4 * j + 3))) 1 :=
    ⟨_, List.mem_append_right _ (ka.wr ▸ hs.wr), hs.contains (by omega) (by decide)⟩
  have he : a.gpr .x16 + BitVec.ofNat 64 (bits + 3) = off base (bits + (4 * j + 3)) := by
    rw [a16, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact congrArg (off base) (by omega)
  have hv : ((a.mem.read (off base (bits + (4 * j + 3))) 1).setWidth 32).setWidth 64 =
      (((if k.testBit (4 * j + 3) then 1 else 0 : BitVec 8)).setWidth 32).setWidth 64 := by
    rw [read1_zext, ka.mem, hbits _ (by omega)]
    rfl
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    State.load, addr, Size.bits, RegUpd.gpr_write, BitVec.setWidth_eq, Nat.mod_one,
    show bits + 3 < 4096 * 1 by omega, show (1 : Nat) < 4096 by decide,
    and_self, he, hr, hv, ite_true, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, ka.mem, ka.rd, ka.wr, ka.sp⟩⟩
  · rw [sign_byte, testBit_three]
    by_cases h : 8 ≤ nib k j
    · simp [h, show ¬ nib k j < 8 by omega]
    · simp [h, show nib k j < 8 by omega]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, ite_false]
    exact ka.gpr r (by simpa using hr.2)

/-! ## The entry -/

/-- An operation changes only its output and the temporary area. -/
theorem _root_.VG.Proof.Mont.OpKeep.unch {M : Mod} {base : Addr} {o : Nat} {s s' : State}
    (h : OpKeep M base o s s') : Unch base [(o, 8 * M.n), (M.tmp, 8 * M.n)] s.mem s'.mem :=
  fun x hx => h.mem x (hx (o, 8 * M.n) (by simp)) (hx (M.tmp, 8 * M.n) (by simp))

/-- The modulus survives a change of memory apart from it. -/
theorem _root_.VG.Proof.Mont.AArch64.ModOkA.unch {M : Mod} {size m : Nat} {base : Addr} {mem mem' : Mem}
    (hM : ModOkA M size m mem base) {W : List (Nat × Nat)} (hU : Unch base W mem mem')
    (hW : ∀ w ∈ W, M.mo + 8 * M.n ≤ w.1 ∨ w.1 + w.2 ≤ M.mo) (hn : base.toNat + size ≤ 2 ^ 64) :
    ModOkA M size m mem' base :=
  ⟨hM.n0, hM.n10, hM.mo, hM.tmp, hM.sep,
    by rw [hU.wordsVal hW (by have := hM.mo; omega)]; exact hM.val, hM.inv, hM.red, hM.call⟩

/-- The comb's slots and modulus at offsets that loads and stores can encode. -/
structure CombA (K : CombCfg) : Prop where
  sl : ∀ x ∈ combSlots K, x % 8 = 0
  mod : ModA K.M
  call : ∀ f m', Mont.callOf K.M = some (f, m') → Mont.ModOk K.M.n m' ∧
    ∀ x ∈ combSlots K, x + 8 * K.M.n ≤ Mont.own K.M.n

theorem CombA.al {K : CombCfg} (h : CombA K) : Aligned K.M (· ∈ combSlots K) :=
  ⟨h.sl, h.mod, fun f m' h' => (h.call f m' h').1⟩

theorem CombA.low {K : CombCfg} (h : CombA K) {l : List Nat} (hl : ∀ x ∈ l, x ∈ combSlots K) : Low K.M l :=
  Low.of_call fun f m' h' x hx => (h.call f m' h').2 x (hl x hx)

/-- After the selection and negation: `E` represents the signed entry of
digit `i`, and only `E`, `-y` and the temporary area changed. -/
theorem combE_mem {K : CombCfg} : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ∈ combWs K := by
  intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> comb_mem

theorem combLay_E {K : CombCfg} {size : Nat} (hL : CombLay K size) (hA : CombA K) :
    (∀ d ∈ [K.E.x, K.E.y, K.E.z], d + 8 * K.M.n ≤ size ∧ d % 8 = 0) ∧
    ((K.E.x + 8 * K.M.n ≤ K.E.y ∨ K.E.y + 8 * K.M.n ≤ K.E.x) ∧
      (K.E.x + 8 * K.M.n ≤ K.E.z ∨ K.E.z + 8 * K.M.n ≤ K.E.x) ∧
      (K.E.y + 8 * K.M.n ≤ K.E.z ∨ K.E.z + 8 * K.M.n ≤ K.E.y)) := by
  have hnd := hL.nodup
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  refine ⟨fun d hd => ⟨hL.lay.le d (combWs_slots K d (combE_mem d hd)),
    hA.sl d (combWs_slots K d (combE_mem d hd))⟩, ?_, ?_, ?_⟩
  · exact hL.apart₂ (by comb_mem) (by comb_mem) (by grind)
  · exact hL.apart₂ (by comb_mem) (by comb_mem) (by grind)
  · exact hL.apart₂ (by comb_mem) (by comb_mem) (by grind)

theorem entryW_sub {K : CombCfg} : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n),
    (K.E.z, 8 * K.M.n), (K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)], w ∈ combW K := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  simp only [combW, combWs, List.mem_append, List.mem_map, List.mem_singleton]
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨_, by comb_mem, rfl⟩
  · exact Or.inl ⟨_, by comb_mem, rfl⟩
  · exact Or.inl ⟨_, by comb_mem, rfl⟩
  · exact Or.inl ⟨_, by comb_mem, rfl⟩
  · exact Or.inr rfl

/-- The modulus is apart from what the comb writes. -/
theorem combW_mo {K : CombCfg} {size : Nat} (hL : CombLay K size) {m : Nat} {mem : Mem} {base : Addr}
    (hM : ModOkA K.M size m mem base) :
    ∀ w ∈ combW K, K.M.mo + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.M.mo := by
  intro w hw
  simp only [combW, List.mem_append, List.mem_map, List.mem_singleton] at hw
  rcases hw with ⟨y, hy, rfl⟩ | rfl
  · have := hL.lay.mo y (combWs_slots K y hy); dsimp only; omega
  · have := hM.sep; dsimp only; omega


/-! ## The addition -/

/-- After the addition: `A` holds `rcbAdd` of what `A` and `E` held. -/
structure SumPost (K : CombCfg) (C : Curve) (base : Addr) (size : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (clob K.M.n) s s'
  unch : Unch base (combW K) s.mem s'.mem
  lt : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s'.mem base x K.M.n < C.p
  val : (tmv C K.M.n base s' K.A.x, tmv C K.M.n base s' K.A.y, tmv C K.M.n base s' K.A.z) =
    VG.Proof.Weierstrass.rcbAdd3 (tmv C K.M.n base s K.S.b3)
      (tmv C K.M.n base s K.A.x) (tmv C K.M.n base s K.A.y) (tmv C K.M.n base s K.A.z)
      (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z)

/-- `A = A + E` by the complete addition into `D`, then copied. -/
theorem combSum_ok {K : CombCfg} {C : Curve} {base : Addr} {size : Nat} (hL : CombLay K size)
    (hA : CombA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {s : State} (hs : Scr s base size)
    (hM : ModOkA K.M size C.p s.mem base)
    (hlt : ∀ x ∈ rcbR K.S K.A K.E, wordsVal s.mem base x K.M.n < C.p) :
    WP isa (.seq (fprogB K.M (rcb3 K.S K.A K.E K.D)) (.block (copyPt K.M.n K.A K.D))) s
      (SumPost K C base size s) := by
  have hn := hs.nowrap
  have hR : ∀ x ∈ rcbR K.S K.A K.E, x ∈ combSlots K := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> comb_mem
  have hI : Inv K.M base size C.p (· ∈ combSlots K) (rcbR K.S K.A K.E) (tmv C K.M.n base s) s :=
    ⟨hs, hM, hR, hlt, fun _ _ => rfl⟩
  have hSl : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.A K.E, x ∈ combSlots K := by
    intro x hx
    simp only [rcbW, rcbR, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> comb_mem
  have W := rcb3_ok hL.lay ⟨hA.sl, hA.mod, fun f m' h => (hA.call f m' h).1⟩ hp hL.add hSl
    (Low.of_call fun f m' h x hx => (hA.call f m' h).2 x (hSl x hx)) hI (fun x hx => hx)
  refine WP.seq (WP.mono W fun s₁ h₁ => ?_)
  obtain ⟨k₁, I₁, v₁⟩ := h₁
  have hnd := hL.nodup
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  have le : ∀ x ∈ combWs K, x + 8 * K.M.n ≤ size := fun x hx => hL.lay.le x (combWs_slots K x hx)
  have al : ∀ x ∈ combWs K, x % 8 = 0 := fun x hx => hA.sl x (combWs_slots K x hx)
  have axd := hL.apart₂ (x := K.A.x) (y := K.D.x) (by comb_mem) (by comb_mem) (by grind)
  have ayd := hL.apart₂ (x := K.A.y) (y := K.D.y) (by comb_mem) (by comb_mem) (by grind)
  have azd := hL.apart₂ (x := K.A.z) (y := K.D.z) (by comb_mem) (by comb_mem) (by grind)
  have axy := hL.apart₂ (x := K.A.x) (y := K.A.y) (by comb_mem) (by comb_mem) (by grind)
  have axz := hL.apart₂ (x := K.A.x) (y := K.A.z) (by comb_mem) (by comb_mem) (by grind)
  have ayz := hL.apart₂ (x := K.A.y) (y := K.A.z) (by comb_mem) (by comb_mem) (by grind)
  have dxay := hL.apart₂ (x := K.D.x) (y := K.A.y) (by comb_mem) (by comb_mem) (by grind)
  have dxaz := hL.apart₂ (x := K.D.x) (y := K.A.z) (by comb_mem) (by comb_mem) (by grind)
  have dyaz := hL.apart₂ (x := K.D.y) (y := K.A.z) (by comb_mem) (by comb_mem) (by grind)
  have hs₁ := k₁.scr hs
  rw [copyPt, List.append_assoc, WP.block_append_iff]
  have b64 : ∀ x ∈ combWs K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := le x hx; omega_using [this, hn]
  have W2 := copy_ok K.M.n hs₁ (le _ (by comb_mem)) (le _ (by comb_mem)) (al _ (by comb_mem))
    (al _ (by comb_mem)) (o := K.A.x) (a := K.D.x) (axd.imp (fun h => by omega_using [h]) id)
  refine WP.mono W2 fun s₂ h₂ => ?_
  obtain ⟨e₂, k₂, O₂⟩ := h₂
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  have W3 := copy_ok K.M.n hs₂ (le _ (by comb_mem)) (le _ (by comb_mem)) (al _ (by comb_mem))
    (al _ (by comb_mem)) (o := K.A.y) (a := K.D.y) (ayd.imp (fun h => by omega_using [h]) id)
  refine WP.mono W3 fun s₃ h₃ => ?_
  obtain ⟨e₃, k₃, O₃⟩ := h₃
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have W4 := copy_ok K.M.n hs₃ (le _ (by comb_mem)) (le _ (by comb_mem)) (al _ (by comb_mem))
    (al _ (by comb_mem)) (o := K.A.z) (a := K.D.z) (azd.imp (fun h => by omega_using [h]) id)
  refine WP.mono W4 fun s₄ h₄ => ?_
  obtain ⟨e₄, k₄, O₄⟩ := h₄
  have dyax := hL.apart₂ (x := K.D.y) (y := K.A.x) (by comb_mem) (by comb_mem) (by grind)
  have dzax := hL.apart₂ (x := K.D.z) (y := K.A.x) (by comb_mem) (by comb_mem) (by grind)
  have dzay := hL.apart₂ (x := K.D.z) (y := K.A.y) (by comb_mem) (by comb_mem) (by grind)
  have hDx : K.D.x ∈ [K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.A K.E := by simp
  have hDy : K.D.y ∈ [K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.A K.E := by simp
  have hDz : K.D.z ∈ [K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.A K.E := by simp
  have bAx := b64 K.A.x (by comb_mem)
  have bAy := b64 K.A.y (by comb_mem)
  have bAz := b64 K.A.z (by comb_mem)
  have bDx := b64 K.D.x (by comb_mem)
  have bDy := b64 K.D.y (by comb_mem)
  have bDz := b64 K.D.z (by comb_mem)
  have wx : wordsVal s₄.mem base K.A.x K.M.n = wordsVal s₁.mem base K.D.x K.M.n := by
    rw [O₄.wordsVal axz bAx, O₃.wordsVal axy bAx, e₂]
  have wy : wordsVal s₄.mem base K.A.y K.M.n = wordsVal s₁.mem base K.D.y K.M.n := by
    rw [O₄.wordsVal ayz bAy, e₃, O₂.wordsVal dyax bDy]
  have wz : wordsVal s₄.mem base K.A.z K.M.n = wordsVal s₁.mem base K.D.z K.M.n := by
    rw [e₄, O₃.wordsVal dzay bDz, O₂.wordsVal dzax bDz]
  refine ⟨hs₃.of_keepRegs k₄ (by decide), ?_, ?_, ?_, ?_⟩
  · have c1 : ∀ r ∈ [Reg.x1], r ∈ clob K.M.n := by intro r hr; simp at hr; subst hr; simp [clob]
    exact ((⟨k₁.gpr, k₁.rd, k₁.wr, k₁.sp⟩ : KeepRegs (clob K.M.n) s s₁).trans
      ((k₂.mono c1).trans ((k₃.mono c1).trans (k₄.mono c1))))
  · refine (k₁.unch.trans (O₂.unch.trans (O₃.unch.trans O₄.unch))).mono ?_
    intro w hw
    simp only [combW, combWs, rcbW, List.map_append, List.map_cons, List.map_nil, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    grind
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [wx]; exact I₁.lt _ hDx
    · rw [wy]; exact I₁.lt _ hDy
    · rw [wz]; exact I₁.lt _ hDz
  · rw [← v₁]
    show (toM _ _ _, toM _ _ _, toM _ _ _) = _
    rw [wx, wy, wz, I₁.val _ hDx, I₁.val _ hDy, I₁.val _ hDz]


theorem combClob_mem {n : Nat} {r : Reg} (h : r ∈ [Reg.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x16, .x17]) :
    r ∈ combClob n := by
  simp only [combClob, clob, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h ⊢
  rcases h with h | h | h | h | h | h | h | h | h <;> simp [h]

end VG.Proof.Weierstrass.AArch64
