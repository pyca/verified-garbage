module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.EcKey.Compressed.Decode
public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64.Decompress
import VerifiedGarbage.Proof.EcKey.AArch64.Main
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Ecdh.AArch64.Main
public import VerifiedGarbage.Impl.EcKey.Compressed
public import VerifiedGarbage.Proof.EcKey.Compressed.Root
public import VerifiedGarbage.Impl.EcKey.Compressed.Root
public import VerifiedGarbage.Spec.EcKey.Compressed
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Front
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Fixed
import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.AArch64.Middle
import VerifiedGarbage.Proof.Mont.AArch64.Ops
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Ecdsa.AArch64.Scalar
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Pow
import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64.Chain
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFnG
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Proof.EcKey.Compressed.Parity
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract

/-! ### `EcKey.Compressed.AArch64.DecompressMiddle`, which this module and modules that import it used -/

section

/-! ### `EcKey.Compressed.AArch64.Parity`, which only this module used -/

section

/-! # The canonical root's parity mismatch mask -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

 theorem parityMask_ok {c : Cfg} {s : State} {base : Addr}
    (hs : Scr s base size) (hn : 0 < c.n)
    (hy : c.sl Impl.Ecdh.AArch64.QY + 8 ≤ size) (ht : c.sl D + 8 ≤ size) :
    WP isa (.block (Impl.EcKey.Compressed.AArch64.parityMask c)) s fun t =>
      t.gpr .x3 = mask (sv c base s Impl.Ecdh.AArch64.QY % 2 ≠
        (word s.mem base (c.sl D)).toNat % 2) ∧ Keeps [.x1, .x2, .x3, .x7] s t := by
  change WP isa (.block ([ld .x1 (c.sl Impl.Ecdh.AArch64.QY)] ++
    ([ld .x2 (c.sl D)] ++ _))) s _
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok hs hy (sl_mod8 c _) .x1) fun s₁ ⟨y₁, k₁, _⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok (hs.of_keeps k₁ (by decide)) ht (sl_mod8 c D) .x2)
    fun s₂ ⟨tag₂, k₂, _⟩ => ?_
  have y₂ : s₂.gpr .x1 = word s.mem base (c.sl Impl.Ecdh.AArch64.QY) :=
    (k₂.gpr _ (by decide)).trans y₁
  rw [k₁.mem] at tag₂
  refine WP.mono (show WP isa (.block _) s₂ (fun t =>
    t.gpr .x3 = 0 - ((s₂.gpr .x1 ^^^ s₂.gpr .x2) &&& 1) ∧ Keeps [.x1, .x2, .x3, .x7] s₂ t) by
    apply WP.of_runBlock
    simp only [zero7, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
      show 16 * 0 < Size.x.bits by decide, ite_true, RegUpd.gpr_write,
      BitVec.setWidth_eq, reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · rw [BitVec.xor_comm]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false])
    fun t ⟨m, k₃⟩ => ?_
  refine ⟨?_, ((k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))).trans k₃⟩
  rw [m, y₂, tag₂, xor_low_mask, slot_parity _ _ _ _ hn]

 theorem invertMask_ok (s : State) (P : Prop) [Decidable P] (h : s.gpr .x3 = mask P) :
    WP isa (.block Impl.EcKey.Compressed.AArch64.invertMask) s fun t =>
      t.gpr .x2 = mask (¬ P) ∧ Keeps [.x2, .x7] s t := by
  apply WP.of_runBlock
  simp only [Impl.EcKey.Compressed.AArch64.invertMask, zero7,
    runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show 16 * 0 < Size.x.bits by decide, show (1 : Nat) < 4096 by decide,
    ite_true, RegUpd.gpr_write, BitVec.setWidth_eq,
    reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · rw [h]
    by_cases hp : P <;> simp [mask, hp] <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

end VG.Proof.EcKey.Compressed.AArch64

end

end

/-! ### `EcKey.Compressed.AArch64.Frame`, which this module and modules that import it used -/

section

/-! # Frames for the converter's scratch slots -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Ecdsa.AArch64
open VG.Impl.Ecdsa.AArch64

theorem unch_same {base : Addr} {W : List (Nat × Nat)} {a b c : Mem}
    (h₁ : Unch base W a b) (h₂ : Unch base W b c) : Unch base W a c :=
  fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem slot_frame {c : Cfg} {base : Addr} {a b : Mem} {i len : Nat} {slots : List Nat}
    (hi : i ∈ slots) (hlen : len ≤ 8 * c.n) (h : Outside base (c.sl i) len a b) :
    Unch base (slW c slots) a b :=
  (h.mono (o' := c.sl i) (n' := 8 * c.n) (Nat.le_refl _) (by omega_using [hlen])).unch.mono fun w hw => by
    obtain rfl := List.mem_singleton.mp hw
    exact List.mem_map_of_mem hi

theorem slots_widen {c : Cfg} {base : Addr} {a b : Mem} {slots slots' : List Nat}
    (h : Unch base (slW c slots) a b) (hsub : ∀ i ∈ slots, i ∈ slots') :
    Unch base (slW c slots') a b := h.mono fun w hw => by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  exact List.mem_map_of_mem (hsub i hi)

 theorem x0_not_powClob (n : Nat) : VG.AArch64.Reg.x0 ∉ VG.Proof.Weierstrass.AArch64.powClob n := by
  intro h
  rcases List.mem_cons.mp h with h | h
  · cases h
  · exact (by decide : VG.AArch64.Reg.x0 ∉ VG.Proof.Mont.AArch64.clobAll)
      (VG.Proof.Mont.AArch64.mem_clobAll h)

 theorem x20_not_powClob (n : Nat) : VG.AArch64.Reg.x20 ∉ VG.Proof.Weierstrass.AArch64.powClob n := by
  intro h
  rcases List.mem_cons.mp h with h | h
  · cases h
  · exact (by decide : VG.AArch64.Reg.x20 ∉ VG.Proof.Mont.AArch64.clobAll)
      (VG.Proof.Mont.AArch64.mem_clobAll h)

 theorem mulPP_eq_op {c : Cfg} (o a b : Nat) (h : a ≠ b) :
    VG.Impl.Weierstrass.AArch64.opProg c.MP' (.mul o a b) = c.mulPP o a b := by
  unfold VG.Impl.Weierstrass.AArch64.opProg VG.Impl.Ecdsa.AArch64.Cfg.mulPP
  cases hh : VG.Impl.Weierstrass.AArch64.Mont.callOf c.MP' with
  | none => simp [VG.Impl.Weierstrass.AArch64.opCode, h]
  | some fm => obtain ⟨f, m⟩ := fm; simp [h, MP'_n]

end VG.Proof.EcKey.Compressed.AArch64

end

end

/-! ### `EcKey.Compressed.AArch64.Candidate`, which this module and modules that import it used -/

section

/-! ### `EcKey.Compressed.AArch64.RootPow`, which this module and modules that import it used -/

section

/-! ### `EcKey.Compressed.AArch64.Chain`, which only this module used -/

section

/-! # Refinement of field-call chains to the existing exponent-chain semantics -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.AArch64.Chain
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

/-- What the chain's products need of their function, if they are calls
(`Mont.rootCallOf`): that it computes them modulo `m`, and that the chain's
slots are below its working space. -/
structure Backend (P : ChainCfg) (m : Nat) : Prop where
  sound : ∀ f m', Mont.rootCallOf P.M = some (f, m') → m' = m ∧ VG.Proof.Weierstrass.AArch64.Mont.ModOk P.M.n m'
  low : Mont.rootCallOf P.M = none ∨
    P.acc + 8 * P.M.n ≤ Mont.own P.M.n ∧ P.base + 8 * P.M.n ≤ Mont.own P.M.n ∧
      P.tbl + 9 * (8 * P.M.n) ≤ Mont.own P.M.n

 theorem mul_ok {P : ChainCfg} {m : Nat} (B : Backend P m) {base : Addr} {size : Nat} {s : State}
    (hs : Scr s base size) (hM : ModOkA P.M size m s.mem base) (hA : ModA P.M)
    {o a b : Nat} (ho : o + 8 * P.M.n ≤ size) (ha : a + 8 * P.M.n ≤ size)
    (hb : b + 8 * P.M.n ≤ size) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0) (hb8 : b % 8 = 0)
    (hB : wordsVal s.mem base b P.M.n < m)
    (hslots : ∀ x ∈ [o, a, b], x = P.acc ∨ x = P.base ∨
      (P.tbl ≤ x ∧ x + 8 * P.M.n ≤ P.tbl + 9 * (8 * P.M.n))) :
    WP isa (VG.Impl.EcKey.Compressed.AArch64.Chain.mul P o a b) s fun t => OpKeep P.M base o s t ∧
      wordsVal t.mem base o P.M.n < m ∧
      wordsVal t.mem base o P.M.n * 2 ^ (64 * P.M.n) % m =
        wordsVal s.mem base a P.M.n * wordsVal s.mem base b P.M.n % m := by
  unfold VG.Impl.EcKey.Compressed.AArch64.Chain.mul
  cases hc : Mont.rootCallOf P.M with
  | none => exact VG.Proof.Mont.AArch64.mul_ok hs hM hA ho ha hb ho8 ha8 hb8 hB
  | some fm =>
    obtain ⟨f, m'⟩ := fm
    obtain ⟨rfl, hH⟩ := B.sound f m' hc
    have ht : P.M.tmp = Mont.moAt P.M.n := by
      unfold Mont.rootCallOf at hc
      split at hc
      · rename_i h
        unfold Mont.callOf at h
        split at h
        · assumption
        · cases h
      · split at hc
        · assumption
        · cases hc
    have hl := B.low.resolve_left (by rw [hc]; simp)
    have hx : ∀ x ∈ [o, a, b], x + 8 * P.M.n ≤ Mont.own P.M.n := by
      intro x h
      rcases hslots x h with rfl | rfl | h
      · exact hl.1
      · exact hl.2.1
      · omega_arith
    exact Mont.mulCall_ok hs hM hH ht (hx _ (by simp))
      (hx _ (by simp)) (hx _ (by simp)) hB

 theorem oddPowers_ok {P : ChainCfg} {N : Nat} (Inv : Nat → State → Prop)
    (hstep : ∀ k s, k < N → Inv k s →
      WP isa (VG.Impl.EcKey.Compressed.AArch64.Chain.mul P (P.slot (k + 1)) (P.slot k) (P.slot 8)) s (Inv (k + 1))) :
    ∀ n ≤ N, ∀ s, Inv 0 s → WP isa (VG.Impl.EcKey.Compressed.AArch64.Chain.oddPowers P n) s (Inv n) := by
  intro n hn
  induction n with
  | zero => exact fun _ h => WP.block_nil h
  | succ n ih =>
    intro s hs
    exact WP.seq (WP.mono (ih (by omega_arith) s hs) fun t ht => hstep n t (by omega_arith) ht)

theorem table_ok {P : ChainCfg} {base : Addr} {size m : Nat} [NeZero m] (hL : ChainLay P size) (B : Backend P m)
    (hm : UnitMod m (2 ^ (64 * P.M.n))) {s₀ s : State} (h : ChainSt P base size m s₀ s)
    (hB : wordsVal s₀.mem base P.base P.M.n < m) :
    WP isa (VG.Impl.EcKey.Compressed.AArch64.Chain.table P) s fun s' =>
      ChainSt P base size m s₀ s' ∧ TblC P base m (bv P base m s₀) 8 s' := by
  have hn := h.scr.nowrap
  have h8 := slot_mod8 P hL.tbl8
  have hle : ∀ i ≤ 8, P.slot i + 8 * P.M.n ≤ size := fun i hi => by
    have := slot_le P hi; have := hL.tbl; omega_arith
  have hin : ∀ i ≤ 8, P.tbl ≤ P.slot i ∧ P.slot i + 8 * P.M.n ≤ P.tbl + 9 * (8 * P.M.n) :=
    fun i hi => slot_le P hi
  have hb := h.base hL
  rw [VG.Impl.EcKey.Compressed.AArch64.Chain.table]
  refine WP.seq (WP.mono (copy_ok P.M.n h.scr (hle 0 (by decide)) hL.base (h8 0) hL.base8
    ((slot_base hL (i := 0) (by decide)).symm.imp (fun h => by omega_arith) id)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
  have S₁ := h.copy (Or.inr (hin 0 (by decide))) k₁ O₁ hL
  have b₁ := S₁.base hL
  refine WP.seq (WP.mono (mul_ok B S₁.scr S₁.mod hL.mod (hle 8 (Nat.le_refl _)) hL.base hL.base (h8 8) hL.base8
    hL.base8 (by rw [b₁]; exact hB) (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact .inr (.inr (hin 8 (by decide)))
      · exact .inr (.inl rfl)
      · exact .inr (.inl rfl))) fun s₂ ⟨k₂, lt₂, e₂⟩ => ?_)
  have S₂ := S₁.op hL (Or.inr (hin 8 (Nat.le_refl _))) k₂
  have v0 : ∀ {t : State}, Unch base [(P.slot 8, 8 * P.M.n), (P.M.tmp, 8 * P.M.n)] s₁.mem t.mem →
      wordsVal t.mem base (P.slot 0) P.M.n = wordsVal s.mem base P.base P.M.n := fun U => by
    rw [U.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact slot_apart P (by decide)
      · exact slot_tmp hL (by decide)) (by have := hle 0 (by decide); omega_arith), e₁]
  have T₂ : TblC P base m (bv P base m s₀) 1 s₂ := by
    refine ⟨fun i hi => ?_, lt₂, ?_⟩
    · obtain rfl : i = 0 := by omega_arith
      rw [v0 k₂.unch, hb]
      exact ⟨hB, by rw [Nat.mul_zero, Nat.zero_add, Lean.Grind.Semiring.pow_one]⟩
    · rw [toM_mul hm (e₂.trans (by rw [b₁])), Lean.Grind.Semiring.pow_two]
  refine WP.mono (oddPowers_ok (P := P) (N := 7)
    (fun k t => ChainSt P base size m s₀ t ∧ TblC P base m (bv P base m s₀) (k + 1) t)
    (fun k t hk ⟨St, Tt⟩ => ?_) 7 (Nat.le_refl _) s₂ ⟨S₂, T₂⟩) fun t h => h
  have Ti := Tt.1 k (by omega_arith)
  refine WP.mono (mul_ok B St.scr St.mod hL.mod (hle (k + 1) (by omega_arith)) (hle k (by omega_arith))
    (hle 8 (Nat.le_refl _)) (h8 _) (h8 _) (h8 _) Tt.2.1 (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> exact .inr (.inr (hin _ (by omega_arith))))) fun u ⟨ku, ltu, eu⟩ => ?_
  refine ⟨St.op hL (Or.inr (hin (k + 1) (by omega_arith))) ku, ?_⟩
  have e : ∀ j ≤ 8, j ≠ k + 1 →
      wordsVal u.mem base (P.slot j) P.M.n = wordsVal t.mem base (P.slot j) P.M.n := fun j hj hne =>
    ku.unch.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact slot_apart P hne
      · exact slot_tmp hL hj) (by have := hle j hj; omega_arith)
  refine ⟨fun i hi => ?_, by rw [e 8 (Nat.le_refl _) (by omega_arith)]; exact Tt.2.1,
    by rw [e 8 (Nat.le_refl _) (by omega_arith)]; exact Tt.2.2⟩
  rcases Nat.lt_or_ge i (k + 1) with h' | h'
  · rw [e i (by omega_arith) (by omega_arith)]; exact Tt.1 i h'
  · obtain rfl : i = k + 1 := by omega_arith
    refine ⟨ltu, ?_⟩
    rw [toM_mul hm eu, Ti.2, Tt.2.2, ← Lean.Grind.Semiring.pow_add]
    congr 1

/-- `acc = acc^(2^s)`, from `B^v`. -/
theorem squares_ok {P : ChainCfg} {base : Addr} {size m : Nat} [NeZero m] (hL : ChainLay P size) (B : Backend P m)
    (hm : UnitMod m (2 ^ (64 * P.M.n))) {s₀ s : State} {v k : Nat} (hs1 : 1 ≤ k) (hs : k < 2 ^ 16)
    (h : ChainSt P base size m s₀ s) (hT : TblC P base m (bv P base m s₀) 8 s)
    (hlt : wordsVal s.mem base P.acc P.M.n < m)
    (hv : toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.acc P.M.n) = bv P base m s₀ ^ v) :
    WP isa (VG.Impl.EcKey.Compressed.AArch64.Chain.squares P k) s fun s' => ChainSt P base size m s₀ s' ∧
      TblC P base m (bv P base m s₀) 8 s' ∧ wordsVal s'.mem base P.acc P.M.n < m ∧
      toM m (2 ^ (64 * P.M.n)) (wordsVal s'.mem base P.acc P.M.n) = bv P base m s₀ ^ (v * 2 ^ k) := by
  have hn := h.scr.nowrap
  rw [VG.Impl.EcKey.Compressed.AArch64.Chain.squares]
  refine WP.seq (WP.mono (setCounter_ok s hs) fun s₁ ⟨c₁, k₁⟩ => ?_)
  have keep₁ : KeepRegs (powClob P.M.n) s s₁ := (Keeps.regs k₁).mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [powClob]
  have S₁ : ChainSt P base size m s₀ s₁ :=
    ⟨h.scr.of_keeps k₁ (by decide), h.keep.trans keep₁, by rw [k₁.mem]; exact h.unch,
      by rw [k₁.mem]; exact h.mod⟩
  refine countLoop_ok (n := k) (by omega_arith) (Inv := fun j t => ChainSt P base size m s₀ t ∧
      TblC P base m (bv P base m s₀) 8 t ∧ t.gpr .x19 = BitVec.ofNat 64 j ∧
      wordsVal t.mem base P.acc P.M.n < m ∧
      toM m (2 ^ (64 * P.M.n)) (wordsVal t.mem base P.acc P.M.n) = bv P base m s₀ ^ (v * 2 ^ (k - j)))
    (fun j t h1 h2 ⟨St, Tt, xt, lt, vt⟩ => ?_) (fun t ⟨St, Tt, _, lt, vt⟩ => ⟨St, Tt, lt, by
      rw [vt, Nat.sub_zero]⟩) hs1
    ⟨S₁, by unfold TblC; rw [k₁.mem]; exact hT, c₁, by rw [k₁.mem]; exact hlt,
      by rw [k₁.mem, hv, Nat.sub_self, Nat.pow_zero, Nat.mul_one]⟩
  refine WP.seq (WP.mono (decCounter_ok t h1 (by omega_arith) xt) fun u ⟨xu, ku⟩ => ?_)
  have Su : ChainSt P base size m s₀ u :=
    ⟨St.scr.of_keeps ku (by decide), St.keep.trans ((Keeps.regs ku).mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp [powClob]), by rw [ku.mem]; exact St.unch,
      by rw [ku.mem]; exact St.mod⟩
  have mu : u.mem = t.mem := ku.mem
  refine WP.mono (mul_ok B Su.scr Su.mod hL.mod hL.acc hL.acc hL.acc hL.acc8 hL.acc8 hL.acc8
    (by rw [mu]; exact lt) (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> exact .inl rfl)) fun w ⟨kw, ltw, ew⟩ => ?_
  have hx : w.gpr .x19 = BitVec.ofNat 64 (j - 1) := by rw [kw.gpr _ (x19_not_clob _), xu]
  have Uw := kw.unch
  rw [mu] at Uw
  refine ⟨⟨Su.op hL (Or.inl rfl) kw, Tt.acc hL hn (Nat.le_refl _) Uw,
    hx, ltw, ?_⟩, hx⟩
  rw [toM_mul hm (ew.trans (by rw [mu])), vt, ← Lean.Grind.Semiring.pow_add]
  congr 1
  rw [← Nat.mul_add, ← Nat.two_mul, show k - (j - 1) = k - j + 1 by omega_arith, Nat.pow_succ]
  grind

/-- A step: `B^v` to `B^(v 2^s + d)`. -/
theorem step_ok {P : ChainCfg} {base : Addr} {size m : Nat} [NeZero m] (hL : ChainLay P size) (B : Backend P m)
    (hm : UnitMod m (2 ^ (64 * P.M.n))) {s₀ s : State} {v k d : Nat} (hs : k < 2 ^ 16)
    (hd : d = 0 ∨ (d % 2 = 1 ∧ d ≤ 15))
    (h : ChainSt P base size m s₀ s) (hT : TblC P base m (bv P base m s₀) 8 s)
    (hlt : wordsVal s.mem base P.acc P.M.n < m)
    (hv : toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.acc P.M.n) = bv P base m s₀ ^ v) :
    WP isa (VG.Impl.EcKey.Compressed.AArch64.Chain.step P (k, d)) s fun s' => ChainSt P base size m s₀ s' ∧
      TblC P base m (bv P base m s₀) 8 s' ∧ wordsVal s'.mem base P.acc P.M.n < m ∧
      toM m (2 ^ (64 * P.M.n)) (wordsVal s'.mem base P.acc P.M.n) = bv P base m s₀ ^ (v * 2 ^ k + d) := by
  have hn := h.scr.nowrap
  rw [VG.Impl.EcKey.Compressed.AArch64.Chain.step]
  have hsq : WP isa (if k = 0 then .block [] else VG.Impl.EcKey.Compressed.AArch64.Chain.squares P k) s fun s' =>
      ChainSt P base size m s₀ s' ∧ TblC P base m (bv P base m s₀) 8 s' ∧
      wordsVal s'.mem base P.acc P.M.n < m ∧
      toM m (2 ^ (64 * P.M.n)) (wordsVal s'.mem base P.acc P.M.n) = bv P base m s₀ ^ (v * 2 ^ k) := by
    split
    · rename_i h0; subst h0
      exact WP.block_nil ⟨h, hT, hlt, by rw [hv, Nat.pow_zero, Nat.mul_one]⟩
    · exact squares_ok hL B hm (by omega_arith) hs h hT hlt hv
  refine WP.seq (WP.mono hsq fun s₁ ⟨S₁, T₁, lt₁, v₁⟩ => ?_)
  split
  · rename_i h0; subst h0
    exact WP.block_nil ⟨S₁, T₁, lt₁, by rw [v₁, Nat.add_zero]⟩
  · rename_i h0
    have hd' : d % 2 = 1 ∧ d ≤ 15 := hd.resolve_left h0
    have hi : (d - 1) / 2 < 8 := by omega_arith
    have Ti := T₁.1 _ hi
    refine WP.mono (mul_ok B S₁.scr S₁.mod hL.mod hL.acc hL.acc
      (by have := slot_le P (i := (d - 1) / 2) (by omega_arith); have := hL.tbl; omega_arith) hL.acc8 hL.acc8
      (slot_mod8 P hL.tbl8 _) Ti.1 (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact .inl rfl
        · exact .inl rfl
        · exact .inr (.inr (slot_le P (by omega_arith))))) fun s₂ ⟨k₂, lt₂, e₂⟩ => ?_
    refine ⟨S₁.op hL (Or.inl rfl) k₂, T₁.acc hL hn (Nat.le_refl _) k₂.unch, lt₂, ?_⟩
    rw [toM_mul hm e₂, v₁, Ti.2, ← Lean.Grind.Semiring.pow_add]
    congr 1
    omega_arith

theorem steps_ok {P : ChainCfg} {base : Addr} {size m : Nat} [NeZero m] (hL : ChainLay P size) (B : Backend P m)
    (hm : UnitMod m (2 ^ (64 * P.M.n))) {s₀ : State} :
    ∀ (sts : List (Nat × Nat)) {s : State} {v : Nat},
      (∀ st ∈ sts, st.1 < 2 ^ 16 ∧ (st.2 = 0 ∨ (st.2 % 2 = 1 ∧ st.2 ≤ 15))) →
      ChainSt P base size m s₀ s → TblC P base m (bv P base m s₀) 8 s →
      wordsVal s.mem base P.acc P.M.n < m →
      toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.acc P.M.n) = bv P base m s₀ ^ v →
      WP isa (VG.Impl.EcKey.Compressed.AArch64.Chain.steps P sts) s fun s' => ChainSt P base size m s₀ s' ∧
        wordsVal s'.mem base P.acc P.M.n < m ∧
        toM m (2 ^ (64 * P.M.n)) (wordsVal s'.mem base P.acc P.M.n) = bv P base m s₀ ^ chainVal v sts
  | [], _, _, _, h, _, hlt, hv => WP.block_nil ⟨h, hlt, hv⟩
  | (k, d) :: rest, s, v, hst, h, hT, hlt, hv => by
    rw [VG.Impl.EcKey.Compressed.AArch64.Chain.steps]
    have h1 := hst (k, d) (List.mem_cons_self ..)
    exact WP.seq (WP.mono (step_ok hL B hm h1.1 h1.2 h hT hlt hv) fun s₁ ⟨S₁, T₁, lt₁, v₁⟩ =>
      steps_ok hL B hm rest (fun st hs => hst st (List.mem_cons_of_mem _ hs)) S₁ T₁ lt₁ v₁)

/-- `[acc] = [base]^e` in Montgomery form, for the exponent `e` of the chain;
only `powClob` and `chainW` change. -/
theorem chainPow_ok {P : ChainCfg} {base : Addr} {size m e : Nat} [NeZero m] (hL : ChainLay P size) (B : Backend P m)
    (hm : UnitMod m (2 ^ (64 * P.M.n))) {s : State} (hs : Scr s base size)
    (hM : ModOkA P.M size m s.mem base) (hB : wordsVal s.mem base P.base P.M.n < m) (hC : ChainOk P e) :
    WP isa (VG.Impl.EcKey.Compressed.AArch64.Chain.pow P) s fun s' => KeepRegs (powClob P.M.n) s s' ∧ Unch base (chainW P) s.mem s'.mem ∧
      wordsVal s'.mem base P.acc P.M.n < m ∧
      toM m (2 ^ (64 * P.M.n)) (wordsVal s'.mem base P.acc P.M.n) =
        toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.base P.M.n) ^ e := by
  have hn := hs.nowrap
  have S₀ : ChainSt P base size m s s := ⟨hs, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Unch.refl _ _ _, hM⟩
  rw [VG.Impl.EcKey.Compressed.AArch64.Chain.pow]
  refine WP.seq (WP.mono (table_ok hL B hm S₀ hB) fun s₁ ⟨S₁, T₁⟩ => ?_)
  have hi : (P.first - 1) / 2 < 8 := by have := hC.first; omega_arith
  have hle := slot_le P (i := (P.first - 1) / 2) (by omega_arith)
  refine WP.seq (WP.mono (copy_ok P.M.n S₁.scr hL.acc (by have := hL.tbl; omega_arith) hL.acc8
    (slot_mod8 P hL.tbl8 _) ((slot_acc hL (i := (P.first - 1) / 2) (by omega_arith)).symm.imp
      (fun h => by omega_arith) id)) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_)
  have S₂ := S₁.copy (Or.inl rfl) k₂ O₂ hL
  have T₂ : TblC P base m (bv P base m s) 8 s₂ :=
    T₁.acc hL hn (Nat.le_refl _) (O₂.unch.mono fun w hw => by simp at hw; simp [hw])
  have Ti := T₁.1 _ hi
  refine WP.mono (steps_ok hL B hm P.steps hC.steps S₂ T₂ (by rw [e₂]; exact Ti.1)
    (v := P.first) (by rw [e₂, Ti.2]; congr 1; have := hC.first; omega_arith)) fun s₃ ⟨S₃, lt₃, v₃⟩ =>
    ⟨S₃.keep, S₃.unch, lt₃, by rw [v₃, hC.val]⟩


end VG.Proof.EcKey.Compressed.AArch64.Chain

end

end


/-! # Root exponentiation reuses the existing field multiplication backend -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.AArch64
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Ecdsa.AArch64
open VG.Impl.EcKey.Compressed.AArch64
open VG.Impl.Ecdh.AArch64 (W2)
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

 def rootSlots : List Nat := [ACC, TMP, RX, RY, RZ, DX, DY, DZ, TX, TY, TZ]
 def rootWrites (c : Cfg) : List (Nat × Nat) :=
  [(c.sl ACC, 8 * c.n), (c.sl RX, 9 * (8 * c.n)), (VG.Impl.Weierstrass.AArch64.Mont.moAt c.n, 8 * c.n)]

/-- Every slot but `TMP` ends below the temporary area of `rootMod`. -/
 theorem sl_moAt (c : Cfg) (h7 : c.n < 10) {i : Nat} (hi : i < 45) (hT : i ≠ TMP) :
    c.sl i + 8 * c.n ≤ VG.Impl.Weierstrass.AArch64.Mont.moAt c.n := by
  have := sl_own c h7 hi hT
  simp only [VG.Proof.Weierstrass.AArch64.Mont.own, Impl.Weierstrass.Mont.ownAt,
    Impl.Weierstrass.Mont.ownBytes, VG.Impl.Weierstrass.AArch64.Mont.moAt] at this ⊢
  omega_using [this]

/-- If the root's products are calls (`Mont.callOf`), of a function computing
them modulo `p`. -/
 def RootCall (c : Cfg) : Prop :=
  ∀ f m', VG.Impl.Weierstrass.AArch64.Mont.rootCallOf (rootMod c) = some (f, m') →
    m' = c.C.p ∧ VG.Proof.Weierstrass.AArch64.Mont.ModOk c.n m'

/-- `RootCall` of a curve whose root's products are not calls. -/
 theorem rootCall_none {c : Cfg} (h : VG.Impl.Weierstrass.AArch64.Mont.rootCallOf (rootMod c) = none) :
    RootCall c := by
  intro f m hf; rw [h] at hf; cases hf

/-- `RootCall` of a curve of six, eight or nine words, whose `rootMod` is
`MP'` and whose products are calls exactly where `MP'`'s are. -/
 theorem rootCall_of {c : Cfg} (hc : BaseCfgOk c) (h : c.n = 6 ∨ c.n = 8 ∨ c.n = 9) :
    RootCall c := by
  intro f m hf
  have e : rootMod c = c.MP' := by
    unfold rootMod; rw [← sl_tmp c h]; rfl
  rw [e] at hf
  unfold VG.Impl.Weierstrass.AArch64.Mont.rootCallOf at hf
  split at hf
  · rename_i h'
    rw [Option.some.injEq] at hf
    subst hf
    exact hc.call_p f m h'
  · split at hf
    · have hn : (c.MP').n = c.n := rfl
      have h6 : (4 == c.n) = false := by simp only [beq_eq_false_iff_ne]; omega_using [h]
      have h5 : (5 == c.n) = false := by simp only [beq_eq_false_iff_ne]; omega_using [h]
      simp only [VG.Impl.Weierstrass.AArch64.Mont.rootFns, List.find?_cons, List.find?_nil,
        Impl.Weierstrass.Mont.brainpoolp320r1p, Impl.Weierstrass.Mont.brainpoolp256r1p,
        Impl.Weierstrass.Mont.secp256k1p, Impl.Weierstrass.Mont.p224p, hn, h5, h6,
        Bool.false_and, Option.map_none, reduceCtorEq] at hf
    · cases hf

/-- `rootMod` takes the modulus as `MP'` does, its temporary area apart. -/
 theorem rootMod_ok {c : Cfg} (hc : BaseCfgOk c) (hcall : RootCall c) {mem : Mem} {base : Addr}
    (hM : ModOkA c.MP' size c.C.p mem base) : ModOkA (rootMod c) size c.C.p mem base where
  n0 := hM.n0
  n10 := hM.n10
  mo := hM.mo
  tmp := by
    change VG.Impl.Weierstrass.AArch64.Mont.moAt c.n + 8 * c.n ≤ size
    have := hc.n10
    simp only [VG.Impl.Weierstrass.AArch64.Mont.moAt, size]; omega_using [this]
  sep := .inl (sl_moAt c hc.n10 (i := MP) (by decide) (by decide))
  val := hM.val
  inv := hM.inv
  red := hM.red
  call := fun f m h => (hcall f m (by
    unfold VG.Impl.Weierstrass.AArch64.Mont.rootCallOf; rw [h])).1

 theorem rootTable_end (c : Cfg) : c.sl RX + 9 * (8 * c.n) = c.sl T0 := by
  rw [sl_eq c RX (by decide), sl_eq c T0 (by decide)]
  simp only [RX, T0]
  omega_using []

 theorem fixedOk_rootWrites {c : Cfg} (hc : BaseCfgOk c) : FixedOk c (rootWrites c) := by
  intro w hw
  simp only [rootWrites, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_lt c (by decide : 12 < ACC)))
  · exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_lt c (by decide : 12 < RX)))
  · exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_moAt c hc.n10 (i := 12) (by decide) (by decide)))

 theorem apart_rootWrites {c : Cfg} (_hc : BaseCfgOk c) {i : Nat} (_hi : i < 45)
    (hw : i ∉ rootSlots) :
    ∀ w ∈ rootWrites c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  have ha : i ≠ ACC := fun h => hw (h ▸ (by simp [rootSlots]))
  have ht : i ≠ TMP := fun h => hw (h ▸ (by simp [rootSlots]))
  have htable : i < RX ∨ T0 ≤ i := by
    simp only [rootSlots, ACC, TMP, RX, RY, RZ, DX, DY, DZ, TX, TY, TZ,
      List.mem_cons, List.not_mem_nil, or_false, not_or] at hw
    change i < 14 ∨ 23 ≤ i
    omega_using [hw]
  intro w h
  simp only [rootWrites, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  · exact sl_apart c ha
  · rw [rootTable_end]
    rcases htable with h | h
    · exact .inl (sl_lt c h ht (by decide))
    · exact .inr (by
        rw [sl_eq c T0 (by decide), sl_eq c i ht]
        have := Nat.mul_le_mul_left (8 * c.n) h
        omega_using [this])
  · exact .inl (sl_moAt c _hc.n10 _hi ht)

 theorem rootChain_lay {c : Cfg} (hc : BaseCfgOk c) (e : Nat) :
    ChainLay (rootChain c e) size := by
  change ChainLay (ChainCfg.ofExp (rootMod c) (c.sl ACC) (c.sl W2) (c.sl RX) e) size
  dsimp only [ChainCfg.ofExp]
  have hA : ModA (rootMod c) := ⟨sl_mod8 c MP, by
    change VG.Impl.Weierstrass.AArch64.Mont.moAt c.n % 8 = 0
    simp only [VG.Impl.Weierstrass.AArch64.Mont.moAt]; have := hc.n10; omega_using [this]⟩
  refine ⟨hc.n0, sl_le c hc.n10 (i := ACC) (by decide), sl_le c hc.n10 (i := W2) (by decide), ?_,
    sl_mod8 c ACC, sl_mod8 c W2, sl_mod8 c RX, hA, sl_apart c (i := ACC) (j := W2) (by decide),
    ?_, ?_, .inl (sl_moAt c hc.n10 (i := ACC) (by decide) (by decide)),
    .inl (sl_moAt c hc.n10 (i := W2) (by decide) (by decide)),
    ?_, ?_, sl_apart c (i := W2) (j := MP) (by decide)⟩
  · change c.sl RX + 9 * (8 * c.n) ≤ size
    rw [rootTable_end]; have := sl_le c hc.n10 (i := T0) (by decide); omega_using [this]
  · exact .inr (by change c.sl RX + 9 * (8 * c.n) ≤ c.sl ACC; rw [rootTable_end]; exact Nat.le_trans (Nat.le_add_right _ _) (sl_lt c (by decide : T0 < ACC)))
  · exact .inr (by change c.sl RX + 9 * (8 * c.n) ≤ c.sl W2; rw [rootTable_end]; exact Nat.le_trans (Nat.le_add_right _ _) (sl_lt c (by decide : T0 < W2)))
  · left
    change c.sl RX + 9 * (8 * c.n) ≤ VG.Impl.Weierstrass.AArch64.Mont.moAt c.n
    rw [rootTable_end]
    exact Nat.le_trans (Nat.le_add_right _ _) (sl_moAt c hc.n10 (i := T0) (by decide) (by decide))
  · intro w hw
    change w ∈ rootWrites c at hw
    exact apart_rootWrites hc (i := MP) (by decide) (by decide) w hw

 theorem rootChain_backend {c : Cfg} (hc : BaseCfgOk c) (hcall : RootCall c) (e : Nat) :
    Chain.Backend (rootChain c e) c.C.p := by
  refine ⟨fun f m h => hcall f m h, .inr ⟨?_, ?_, ?_⟩⟩
  · exact sl_own_fn c hc.n10 (i := ACC) (by decide) (by decide)
  · exact sl_own_fn c hc.n10 (i := W2) (by decide) (by decide)
  · change c.sl RX + 9 * (8 * c.n) ≤ VG.Proof.Weierstrass.AArch64.Mont.own c.n
    rw [rootTable_end]
    exact Nat.le_trans (Nat.le_add_right _ _) (sl_own_fn c hc.n10 (i := T0) (by decide) (by decide))

 theorem rootPower_ok {c : Cfg} (hc : BaseCfgOk c) (hcall : RootCall c) {e : Nat}
    (hchain : ChainOk (rootChain c e) e) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkA c.MP' size c.C.p s.mem base)
    (hB : sv c base s W2 < c.C.p) :
    WP isa (rootPower c e) s fun t => KeepRegs (powClob c.n) s t ∧
      Unch base (rootWrites c) s.mem t.mem ∧ sv c base t ACC < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t ACC) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ e :=
  Chain.chainPow_ok (rootChain_lay hc e) (rootChain_backend hc hcall e)
    (unitMod_pow_two hc.p_odd _) hs (rootMod_ok hc hcall hM) hB hchain

end VG.Proof.EcKey.Compressed.AArch64

end

end

/-! # Shared refinement interface for coordinate-recovery algorithms -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Impl.Ecdh.AArch64 (W0 W2)
open VG.Impl.EcKey.Compressed.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

 def candidateSlots : List Nat := [ACC, T0, T1, T2, T3, T4, T5, W0, TMP, RX, RY, RZ, DX, DY, DZ, TX, TY, TZ]
 def candidateWrites (c : Cfg) : List (Nat × Nat) := rootWrites c ++ slW c candidateSlots

 structure CandidatePost (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C)
    (base : Addr) (s t : State) : Prop where
  keep : KeepRegs (powClob c.n) s t
  unch : Unch base (candidateWrites c) s.mem t.mem
  lt : sv c base t ACC < c.C.p
  val : toM c.C.p (2 ^ (64 * c.n)) (sv c base t ACC) =
    root (toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2))

 def CandidateCorrect (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C) : Prop :=
  ∀ (base : Addr) (s : State), Scr s base size →
    ModOkA c.MP' size c.C.p s.mem base → sv c base s W2 < c.C.p →
    sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p →
    WP isa (rootCandidate c) s (CandidatePost c root base s)

 theorem candidate_fixed {c : Cfg} (hc : BaseCfgOk c) : FixedOk c (candidateWrites c) :=
  (fixedOk_rootWrites hc).append (fixedOk_slW (l := candidateSlots) (by decide))

 theorem candidate_apart {c : Cfg} (hc : BaseCfgOk c) {i : Nat}
    (hi : i < 45) (hw : i ∉ ACC :: candidateSlots) :
    ∀ w ∈ candidateWrites c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  apply apart_append
  · exact apart_rootWrites hc hi (fun h => hw
      ((by decide : ∀ i ∈ rootSlots, i ∈ ACC :: candidateSlots) i h))
  · exact apart_slW (fun h => hw (List.mem_cons_of_mem _ h))
      (by omega_using [hi]) (by decide)

 theorem candidateThree_correct {c : Cfg} (hc : BaseCfgOk c) (hcall : RootCall c) (hp : c.C.p % 4 = 3)
    (hchain : ChainOk (rootChain c ((c.C.p + 1) / 4)) ((c.C.p + 1) / 4)) :
    CandidateCorrect c Impl.EcKey.Compressed.rootThreeModFour := by
  intro base s hs hM hB _
  rw [rootCandidate, ite_eq_left hp]
  refine WP.mono (rootPower_ok hc hcall hchain hs
    hM hB) fun t ⟨K, U, lt, v⟩ => ?_
  refine ⟨K, U.mono (by intro w hw; exact List.mem_append_left _ hw), lt, ?_⟩
  simpa only [Impl.EcKey.Compressed.rootThreeModFour, pow_eq_npow] using v

end VG.Proof.EcKey.Compressed.AArch64

end

end

/-! ### `EcKey.Compressed.AArch64.Select`, which only this module used -/

section

/-! # Leave Montgomery form and choose between the two canonical roots -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdh.AArch64 (QY W0)
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

structure SelectPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  mod : ModOkA c.MP' size c.C.p s'.mem base
  keep : KeepRegs (clob c.n) s s'
  unch : Unch base (slW c [QY, W0, TMP]) s.mem s'.mem
  lt : sv c base s' QY < c.C.p
  val : Fin.ofNat c.C.p (sv c base s' QY) =
    let y := toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)
    if y.val % 2 = (word s.mem base (c.sl D)).toNat % 2 then y else -y

theorem selectRoot_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkA c.MP' size c.C.p s.mem base)
    (hOne : sv c base s ONE = 1) (hZero : sv c base s ZERO = 0) :
    WP isa (Impl.EcKey.Compressed.AArch64.selectRoot c) s (SelectPost c base s) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hp3 := hc.p_ge
  obtain hY := sl_le c h7 (i := QY) (by decide)
  obtain hZ := sl_le c h7 (i := ZERO) (by decide)
  obtain hW := sl_le c h7 (i := W0) (by decide)
  obtain hD := sl_le c h7 (i := D) (by decide)
  obtain hMP := sl_le c h7 (i := MP) (by decide)
  change WP isa (.seq (opProg c.MP' (.mul (c.sl QY) (c.sl ACC) (c.sl ONE)))
    (.block (opCode c.MP' (.sub (c.sl W0) (c.sl ZERO) (c.sl QY)) ++
      Impl.EcKey.Compressed.AArch64.parityMask c ++ sel c.n (c.sl QY) (c.sl QY) (c.sl W0)))) s _
  rw [mulPP_eq_op _ _ _ (by
    intro h
    have := sl_inj c hc.n0 h
    contradiction)]
  refine WP.seq (WP.mono (slMulP_ok hc hs hM (o := QY) (a := ACC) (b := ONE)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [hOne]; omega_using [hp3]))
    fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_)
  obtain hs₁ := k₁.scr hs
  obtain hM₁ := hM.keepA64 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  obtain normal : Fin.ofNat c.C.p (sv c base s₁ QY) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) :=
    toM_one_mul (unitMod_pow_two hc.p_odd (64 * c.n)) (by simpa only [hOne] using e₁)
  obtain normalVal : sv c base s₁ QY =
      (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)).val := by
    simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt lt₁] using congrArg Fin.val normal
  obtain zero₁ : sv c base s₁ ZERO = 0 :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hZero
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (subOp_ok hs₁ hM₁ (MP'_A c) hW hZ hY (sl_mod8 c W0) (sl_mod8 c ZERO) (sl_mod8 c QY)
    (by change sv c base s₁ ZERO < c.C.p; rw [zero₁]; omega_using [hp3])
    lt₁) fun s₂ ⟨k₂, e₂⟩ => ?_
  change sv c base s₂ W0 = (sv c base s₁ ZERO + c.C.p - sv c base s₁ QY) % c.C.p at e₂
  obtain hs₂ := k₂.scr hs₁
  obtain hM₂ := hM₁.keepA64 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  obtain y₂ : sv c base s₂ QY = sv c base s₁ QY :=
    sv_keep (MP'_n c) rfl h7 hn k₂ (by decide) (by decide) (by decide)
  obtain negLt : sv c base s₂ W0 < c.C.p := by
    rw [e₂]
    exact Nat.mod_lt _ (by omega_using [hp3])
  obtain negVal : Fin.ofNat c.C.p (sv c base s₂ W0) = -(Fin.ofNat c.C.p (sv c base s₁ QY)) := by
    apply Fin.ext
    simp only [Fin.val_ofNat, Fin.neg_def]
    rw [show sv c base s₂ W0 = (sv c base s₁ ZERO + c.C.p - sv c base s₁ QY) % c.C.p from e₂,
      zero₁, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt lt₁]
  obtain U₁₂ : Unch base (slW c [QY, W0, TMP]) s.mem s₂.mem :=
    unch_same (unch_slots (MP'_n c) rfl k₁.unch (by simp) (by simp))
      (unch_slots (MP'_n c) rfl k₂.unch (by simp) (by simp))
  obtain tag₂ : word s₂.mem base (c.sl D) = word s.mem base (c.sl D) :=
    U₁₂.word (fun w hw => by
      have := (apart_slW (c := c) (by decide : D ∉ [QY, W0, TMP])) w hw
      omega_using [h0, this]) (by have := hs.nowrap; omega_using [h0, hn, hD])
  rw [WP.block_append_iff]
  refine WP.mono (parityMask_ok hs₂ h0 (by omega_using [h0, hY]) (by omega_using [h0, hD])) fun s₃ ⟨mask₃, k₃⟩ => ?_
  obtain hs₃ := hs₂.of_keeps k₃ (by decide)
  refine WP.mono (sel_ok (decide (sv c base s₂ QY % 2 ≠ (word s₂.mem base (c.sl D)).toNat % 2)) c.n hs₃
    (by simpa only [mask, decide_eq_true_eq] using mask₃)
    hY hY hW (sl_mod8 c QY) (sl_mod8 c QY) (sl_mod8 c W0) (Or.inl (Nat.le_refl _))
    (by have := sl_apart c (i := QY) (j := W0) (by decide); omega_using [this])) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  obtain hs₄ := hs₃.of_keepRegs k₄ (by decide)
  obtain hM₄ : ModOkA c.MP' size c.C.p s₄.mem base := modP_of hc (by
    rw [O₄.wordsVal (d := c.sl MP) (k := c.n)
      (sl_apart c (i := MP) (j := QY) (by decide)) (by omega_using [hn, hMP]), k₃.mem]
    exact hM₂.val)
  obtain e₄' : sv c base s₄ QY =
      if sv c base s₂ QY % 2 ≠ (word s₂.mem base (c.sl D)).toNat % 2 then
        sv c base s₂ W0 else sv c base s₂ QY := by
    simpa only [sv, k₃.mem, decide_eq_true_eq] using e₄
  refine ⟨hs₄, hM₄, ?_, ?_, ?_, ?_⟩
  · have k₁' : KeepRegs (clob c.n) s s₁ := ⟨k₁.gpr, k₁.rd, k₁.wr, k₁.sp⟩
    obtain k₂' : KeepRegs (clob c.n) s₁ s₂ := ⟨k₂.gpr, k₂.rd, k₂.wr, k₂.sp⟩
    exact ((k₁'.trans k₂').trans ((Keeps.regs k₃).mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [clob]))).trans
        (k₄.mono (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                     rcases hr with rfl | rfl <;> simp [clob]))
  · apply unch_same U₁₂
    rw [← k₃.mem]
    exact slot_frame (by simp) (Nat.le_refl _) O₄
  · rw [e₄']
    split
    · exact negLt
    · rw [y₂]
      exact lt₁
  · change Fin.ofNat c.C.p (sv c base s₄ QY) =
      if (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)).val % 2 =
        (word s.mem base (c.sl D)).toNat % 2 then _ else _
    rw [y₂, tag₂, normalVal] at e₄'
    by_cases hm : (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)).val % 2 =
        (word s.mem base (c.sl D)).toNat % 2
    · rw [ite_eq_left hm]
      rw [ite_eq_right (not_not_intro hm)] at e₄'
      rw [e₄']
      exact Fin.ext (Nat.mod_eq_of_lt (toM _ _ _).isLt)
    · rw [ite_eq_right hm]
      rw [ite_eq_left hm] at e₄'
      rw [e₄', negVal, normal]

end VG.Proof.EcKey.Compressed.AArch64

end

end

/-! ### `EcKey.Compressed.AArch64.Check`, which only this module used -/

section

/-! # Check the recovered root's square and parity -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdh.AArch64 (QY QYM R2P W1 W2 W3)
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdh.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)

def checkN : List FOp := [.mul QYM QY R2P, .mul W1 QYM QYM, .sub W3 W1 W2]
abbrev checkSlots : List Nat := [QY, R2P, W2, QYM, W1, W3]

theorem checkOps_eq (c : Cfg) : Impl.EcKey.Compressed.AArch64.checkRootOps c =
    checkN.map (FOp.rename c.sl) := rfl

theorem checkN_run {F : Type} [Lean.Grind.CommRing F] (e : Nat → F) :
    runOps checkN e W3 = (e QY * e R2P) * (e QY * e R2P) - e W2 := by
  simp only [checkN, runOps_cons, runOps_nil, FOp.run, Function.update_apply]
  simp only [QYM, QY, R2P, W1, W2, X, RR, DM, TT, SM, Nat.reduceEqDiff, ↓reduceIte]

theorem checkN_reads : readsOk checkN [QY, R2P, W2] = true := by decide
theorem checkN_slots : ∀ op ∈ checkN, ∀ x ∈ op.out :: op.ins, x ∈ checkSlots := by decide
theorem checkN_out : ∀ op ∈ checkN, op.out ∈ [QYM, W1, W3, TMP] := by decide

theorem raw_r2_mul {c : Cfg} (hc : BaseCfgOk c) (a : Nat) :
    toM c.C.p (2 ^ (64 * c.n)) a *
      toM c.C.p (2 ^ (64 * c.n)) (c.R * c.R % c.C.p) = Fin.ofNat c.C.p a := by
  change toM c.C.p (2 ^ (64 * c.n)) a * toM c.C.p (2 ^ (64 * c.n)) (c.mont c.R) = _
  rw [toM_cmont hc]
  unfold toM
  obtain hu := mul_rinv (unitMod_pow_two hc.p_odd (64 * c.n))
  change Fin.ofNat c.C.p c.R * rinv c.C.p (2 ^ (64 * c.n)) = 1 at hu
  grind

structure CheckPolyPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (clob c.n) s s'
  unch : Unch base (slW c [QYM, W1, W3, TMP]) s.mem s'.mem
  lt : sv c base s' W3 < c.C.p
  val : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' W3) =
    Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) -
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2)

theorem checkPoly_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkA c.MP' size c.C.p s.mem base)
    (hy : sv c base s QY < c.C.p) (hr : sv c base s W2 < c.C.p)
    (hr2 : sv c base s R2P = c.R * c.R % c.C.p) :
    WP isa (Impl.Weierstrass.AArch64.fprogB c.MP'
      (Impl.EcKey.Compressed.AArch64.checkRootOps c)) s (CheckPolyPost c base s) := by
  have h7 := hc.n10
  obtain hL : Lay c.MP' size (· ∈ checkSlots.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  obtain hAl : Aligned c.MP' (· ∈ checkSlots.map c.sl) := ⟨fun x hx => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact sl_mod8 c i, MP'_A c, fun f m h => (hc.call_p f m h).2⟩
  obtain I : Inv c.MP' base size c.C.p (· ∈ checkSlots.map c.sl) ([QY, R2P, W2].map c.sl)
      (fun o => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base o c.n)) s := by
    refine ⟨hs, hM, ?_, ?_, fun _ _ => rfl⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      obtain sub : ∀ i ∈ [QY, R2P, W2], i ∈ checkSlots := by decide
      exact List.mem_map_of_mem (sub i hi)
    · intro x hx
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact hy
      · show sv c base s R2P < _
        rw [hr2]
        exact Nat.mod_lt _ (by have := hc.p_ge; omega_arith)
      · exact hr
  rw [checkOps_eq]
  refine WP.mono (fprogB_ok hL hAl (unitMod_pow_two hc.p_odd (64 * c.n)) _ I
    (fun op hop x hx => ?_)
    (by
      intro op hop
      apply Low.of_call
      intro f m h x hx
      obtain ⟨op₀, hop₀, rfl⟩ := List.mem_map.mp hop
      obtain hx' : x ∈ (op₀.out :: op₀.ins).map c.sl := by
        cases op₀ <;> simpa [FOp.rename, FOp.out, FOp.ins] using hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
      obtain hi' := checkN_slots op₀ hop₀ i hi
      obtain H : ∀ i ∈ checkSlots, i < 45 ∧ i ≠ TMP := by decide
      exact sl_own_fn c h7 (H i hi').1 (H i hi').2)
    (readsOk_rename c.sl checkN_reads)) fun t ⟨PK, IT⟩ => ?_
  · obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
    obtain hx' : x ∈ (op₀.out :: op₀.ins).map c.sl := by
      cases op₀ <;> simpa [FOp.rename, FOp.out, FOp.ins] using hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    exact List.mem_map_of_mem (checkN_slots _ h₀ _ hi)
  obtain hw : c.sl W3 ∈ validAfter (checkN.map (FOp.rename c.sl)) ([QY, R2P, W2].map c.sl) :=
    (mem_validAfter _ _).mpr (Or.inr (by simp [checkN, FOp.rename, FOp.out]))
  obtain vt := IT.val _ hw
  obtain H : ∀ op ∈ checkN, op.out ≠ TMP ∧ op.out ≠ 54 ∧ op.out ≠ 61 ∧ op.out ≠ 82 := by decide
  rw [congrFun (runOps_rename c.sl checkN _ fun op hop y h =>
    sl_inj c hc.n0 h (.inr (H op hop).2) (.inl (H op hop).1)) W3, checkN_run] at vt
  refine ⟨PK.scr hs, ⟨PK.gpr, PK.rd, PK.wr, PK.sp⟩, ?_, IT.lt _ hw, ?_⟩
  · apply PK.unch.mono
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hw
      obtain ⟨op, hop, rfl⟩ := List.mem_map.mp ho
      obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
      exact List.mem_map.mpr ⟨op₀.out, checkN_out _ h₀, by rw [FOp.out_rename]; rfl⟩
    · obtain rfl := List.mem_singleton.mp hw
      exact List.mem_map_of_mem (by decide)
  · change toM c.C.p (2 ^ (64 * c.n)) (sv c base t W3) =
      (toM c.C.p (2 ^ (64 * c.n)) (sv c base s QY) *
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s R2P)) *
      (toM c.C.p (2 ^ (64 * c.n)) (sv c base s QY) *
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s R2P)) -
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) at vt
    simpa only [hr2, raw_r2_mul hc] using vt

structure CheckRootPost (c : Cfg) (base : Addr) (P : Prop) [Decidable P] (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (clob c.n) s s'
  unch : Unch base (slW c [QYM, W1, W3, TMP, FLAG]) s.mem s'.mem
  flag : word s'.mem base (c.sl FLAG) = mask
    ((P ∧ Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2)) ∧
      sv c base s QY % 2 = (word s.mem base (c.sl D)).toNat % 2)

theorem checkRoot_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkA c.MP' size c.C.p s.mem base)
    (hy : sv c base s QY < c.C.p) (hr : sv c base s W2 < c.C.p)
    (hr2 : sv c base s R2P = c.R * c.R % c.C.p) {P : Prop} [Decidable P]
    (hf : word s.mem base (c.sl FLAG) = mask P) :
    WP isa (Impl.EcKey.Compressed.AArch64.checkRoot c) s (CheckRootPost c base P s) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hsz : size = 8192 := rfl
  obtain hF := sl_le c h7 (i := FLAG) (by decide)
  obtain hW := sl_le c h7 (i := W3) (by decide)
  obtain hY := sl_le c h7 (i := QY) (by decide)
  obtain hD := sl_le c h7 (i := D) (by decide)
  change WP isa (.seq
    (Impl.Weierstrass.AArch64.fprogB c.MP' (Impl.EcKey.Compressed.AArch64.checkRootOps c))
    (.block (Impl.EcKey.Compressed.AArch64.checkRootChecks c))) s _
  refine WP.seq (WP.mono (checkPoly_ok hc hs hM hy hr hr2) fun s₁ I => ?_)
  obtain flag₁ : word s₁.mem base (c.sl FLAG) = mask P := by
    rw [flag_unch I.unch h7 h0 hn (by decide), hf]
  obtain hz : sv c base s₁ W3 = 0 ↔
      Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) := by
    rw [← toM_eq_zero_iff (unitMod_pow_two hc.p_odd (64 * c.n)) I.lt, I.val]
    constructor <;> intro h <;> grind
  rw [Impl.EcKey.Compressed.AArch64.checkRootChecks, WP.block_append_iff]
  refine WP.mono (checkZero_ok c I.scr h0 hW (by omega_arith) (sl_mod8 c W3) (sl_mod8 c FLAG)) fun s₂ ⟨f₂, k₂, O₂⟩ => ?_
  obtain hs₂ := I.scr.of_keepRegs k₂ (by decide)
  obtain flag₂ : word s₂.mem base (c.sl FLAG) = mask
      (P ∧ Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2)) := by
    rw [f₂, flag₁, show wordsVal s₁.mem base (c.sl W3) c.n = sv c base s₁ W3 from rfl, mask_and]
    simp only [mask, hz]
  obtain y₂ : sv c base s₂ QY = sv c base s QY := by
    rw [sv, sv_flag O₂ h0 h7 hn (by decide) (by decide)]
    exact sv_unch I.unch h7 hn (by decide) (apart_slW (by decide))
  obtain tag₂ : word s₂.mem base (c.sl D) = word s.mem base (c.sl D) := by
    rw [O₂.word (by have := sl_apart c (i := D) (j := FLAG) (by decide); omega_arith) (by omega_arith)]
    exact I.unch.word (fun w hw => by
      have := (apart_slW (c := c) (by decide : D ∉ [QYM, W1, W3, TMP])) w hw
      omega_arith) (by omega_arith)
  rw [WP.block_append_iff]
  refine WP.mono (parityMask_ok hs₂ h0 (by omega_arith) (by omega_arith)) fun s₃ ⟨mask₃, k₃⟩ => ?_
  rw [y₂, tag₂] at mask₃
  rw [WP.block_append_iff]
  refine WP.mono (invertMask_ok s₃ _ mask₃) fun s₄ ⟨mask₄, k₄⟩ => ?_
  obtain hs₄ := (hs₂.of_keeps k₃ (by decide)).of_keeps k₄ (by decide)
  refine WP.mono (andFlag_ok c hs₄ (by omega_arith) (sl_mod8 c FLAG)) fun s₅ ⟨flag₅, k₅, O₅⟩ => ?_
  refine ⟨hs₄.of_keepRegs k₅ (by decide), ?_, ?_, ?_⟩
  · exact (((I.keep.trans (k₂.mono (by simp [clob]))).trans
      ((Keeps.regs k₃).mono (by simp [clob]))).trans
      ((Keeps.regs k₄).mono (by simp [clob]))).trans (k₅.mono (by simp [clob]))
  · have U₁ : Unch base (slW c [QYM, W1, W3, TMP, FLAG]) s.mem s₁.mem := I.unch.mono (by
      intro w hw
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact List.mem_map_of_mem (List.mem_append_left [FLAG] hi))
    obtain U₂ : Unch base (slW c [QYM, W1, W3, TMP, FLAG]) s₁.mem s₄.mem := by
      rw [k₄.mem, k₃.mem]
      exact slot_frame (by simp) (by omega_arith) O₂
    exact unch_same (unch_same U₁ U₂) (slot_frame (by simp) (by omega_arith) O₅)
  · rw [flag₅, k₄.mem, k₃.mem, flag₂, mask₄]
    simp only [not_not]
    exact mask_and _ _

end VG.Proof.EcKey.Compressed.AArch64

end

end

/-! ### `EcKey.Compressed.AArch64.Peer`, which only this module used -/

section

/-! # Compressed tag, canonical x and curve constants -/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/AArch64/TagCheck.lean`, which only this module imported.
section

/-! # Accept precisely 02 and 03 and preserve their parity bit -/

section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Ecdh.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

 theorem tagRead_ok {s : State} {q : Addr} (hq : s.gpr .x6 = q)
    (hin : InRegions (s.rd ++ s.wr) q 1) :
    WP isa (.block [zero7, .ldrb .x1 .x6 0]) s fun t =>
      t.gpr .x1 = (s.mem q).setWidth 64 ∧ t.gpr .x7 = 0 ∧ Keeps [.x1, .x7] s t := by
  obtain ha : s.gpr .x6 + BitVec.ofNat 64 0 = q := by rw [hq, BitVec.add_zero]
  apply WP.of_runBlock
  simp only [zero7, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Nat.mod_one,
    show 0 < 4096 * 1 by decide, show 16 * 0 < Size.x.bits by decide, and_self, ite_true, Option.bind_some, State.load,
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq,
    reduceCtorEq, ite_false, ha, hin, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [read1_zext, RegUpd.mem_write], rfl, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

 theorem tagBits_ok (s : State) :
    WP isa (.block [.movz .x .x5 1 0, .logic .orr .x .x1 .x1 .x5,
      .movz .x .x5 3 0, .logic .eor .x .x1 .x1 .x5]) s fun t =>
      t.gpr .x1 = (s.gpr .x1 ||| 1) ^^^ 3 ∧ Keeps [.x1, .x5] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show 16 * 0 < Size.x.bits by decide, ite_true, RegUpd.gpr_write,
    BitVec.setWidth_eq, reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

 theorem decompressTag_ok {c : Cfg} {s : State} {base q : Addr}
    (hs : Scr s base size) (hq : s.gpr .x6 = q)
    (hin : InRegions (s.rd ++ s.wr) q 1) (hD : c.sl D + 8 ≤ size) :
    WP isa (.block (Impl.EcKey.Compressed.AArch64.decompressTag c)) s fun t =>
      t.gpr .x2 = mask (s.mem q = 2 ∨ s.mem q = 3) ∧
      word t.mem base (c.sl D) = (s.mem q).setWidth 64 ∧
      KeepRegs [.x1, .x2, .x5, .x7, .x16] s t ∧ Outside base (c.sl D) 8 s.mem t.mem := by
  change WP isa (.block ([zero7, .ldrb .x1 .x6 0] ++ ([st .x1 (c.sl D)] ++
    ([.movz .x .x5 1 0, .logic .orr .x .x1 .x1 .x5, .movz .x .x5 3 0,
      .logic .eor .x .x1 .x1 .x5] ++ Impl.Ecdh.AArch64.Cfg.isZero)))) s _
  rw [WP.block_append_iff]
  refine WP.mono (tagRead_ok hq hin) fun s₁ ⟨v₁, z₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (st_out (hs.of_keeps k₁ (by decide)) hD (sl_mod8 c D) .x1)
    fun s₂ ⟨m₂, k₂, g₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (tagBits_ok s₂) fun s₃ ⟨v₃, k₃⟩ => ?_
  refine WP.mono (isZero_ok s₃ (by rw [k₃.gpr _ (by decide), g₂, z₁]))
    fun s₄ ⟨v₄, k₄⟩ => ?_
  obtain m₄ : s₄.mem = s.mem.writeW (off base (c.sl D)) ((s.mem q).setWidth 64) := by
    rw [k₄.mem, k₃.mem, m₂, k₁.mem, v₁]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [v₄, v₃, g₂, v₁]
    obtain key : ∀ b : Byte, ((b.setWidth 64 ||| 1) ^^^ 3 = 0) = (b = 2 ∨ b = 3) := by decide
    simp only [mask, key]
  · rw [m₄, word_writeW_self]
  · exact (((Keeps.regs k₁).mono (by sub_regs)).trans (k₂.mono (by sub_regs))).trans
      (((Keeps.regs k₃).mono (by sub_regs)).trans ((Keeps.regs k₄).mono (by sub_regs)))
  · rw [m₄]
    exact writeW_outside _ _ _ (by have := hs.nowrap; omega)

end VG.Proof.EcKey.Compressed.AArch64
end

end

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdh.AArch64 (R2P BP)
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Ecdh.AArch64

theorem decompressPeer_eq (c : Cfg) : Impl.EcKey.Compressed.AArch64.decompressPeer c =
    setConst c.n (c.sl R2P) (c.R * c.R % c.C.p) ++
    (setConst c.n (c.sl BP) (c.mont c.C.b) ++
    (Impl.EcKey.Compressed.AArch64.decompressTag c ++
    (c.andFlag ++ Impl.Ecdh.AArch64.Cfg.checkLtP c (c.sl E)))) := by
  simp only [Impl.EcKey.Compressed.AArch64.decompressPeer, Impl.Ecdh.AArch64.Cfg.consts,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem decompressPeer_ok {c : Cfg} (hc : BaseCfgOk c) {base q : Addr} {s : State}
    (hs : Scr s base size) (hq : s.gpr .x6 = q)
    (hin : (⟨q, c.C.len + 1⟩ : Region) ∈ s.rd ++ s.wr)
    (hd : Region.Disjoint ⟨q, c.C.len + 1⟩ ⟨base, size⟩)
    (hmp : sv c base s MP = c.C.p) (hf : word s.mem base (c.sl FLAG) = BitVec.allOnes 64) :
    WP isa (.block (Impl.EcKey.Compressed.AArch64.decompressPeer c)) s fun s' =>
      Scr s' base size ∧ KeepRegs [.x1, .x2, .x5, .x7, .x16] s s' ∧
      Unch base (slW c [R2P, BP, D, FLAG]) s.mem s'.mem ∧
      sv c base s' R2P = c.R * c.R % c.C.p ∧ sv c base s' BP = c.mont c.C.b ∧
      word s'.mem base (c.sl D) = (s.mem q).setWidth 64 ∧
      word s'.mem base (c.sl FLAG) = mask ((s.mem q = 2 ∨ s.mem q = 3) ∧ sv c base s E < c.C.p) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hsz : size = 8192 := rfl
  obtain hR := sl_le c h7 (i := R2P) (by decide)
  obtain hB := sl_le c h7 (i := BP) (by decide)
  obtain hD := sl_le c h7 (i := D) (by decide)
  obtain hE := sl_le c h7 (i := E) (by decide)
  obtain hM := sl_le c h7 (i := MP) (by decide)
  obtain hF := sl_le c h7 (i := FLAG) (by decide)
  rw [decompressPeer_eq, WP.block_append_iff]
  refine WP.mono (setConst_ok hs hR (sl_mod8 c R2P) (Nat.lt_trans (Nat.mod_lt _ (by have := hc.p_ge; omega_using [this])) hc.p_lt))
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  obtain hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (setConst_ok hs₁ hB (sl_mod8 c BP) (show c.mont c.C.b < 2 ^ (64 * c.n) from
    Nat.lt_trans (Nat.mod_lt _ (by have := hc.p_ge; omega_using [this])) hc.p_lt)) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  obtain W₂ : Outside base 0 size s.mem s₂.mem :=
    (O₁.mono (Nat.zero_le _) hR).trans (O₂.mono (Nat.zero_le _) hB)
  obtain q₂ : s₂.mem q = s.mem q := by
    obtain h := keep_of_disjoint' W₂ hd (by omega_using [hn]) (i := 0) (by omega_using []) (by have := hc.len_hi; omega_using [h7, this])
    simpa only [BitVec.add_zero] using h
  rw [WP.block_append_iff]
  refine WP.mono (decompressTag_ok (c := c) (q := q) hs₂
    (by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), hq])
    (by
      exact ⟨_, by rw [k₂.rd, k₂.wr, k₁.rd, k₁.wr]; exact hin, by
        simpa using Offset.contains_base q (d := 0) (n := 1)
          (by omega_using [] : 0 + 1 ≤ c.C.len + 1) (by decide)⟩) (by omega_using [h0, hD])) fun s₃ ⟨mask₃, tag₃, k₃, O₃⟩ => ?_
  rw [q₂] at mask₃ tag₃
  obtain hs₃ := hs₂.of_keepRegs k₃ (by decide)
  obtain U₃ : Unch base (slW c [R2P, BP, D]) s.mem s₃.mem :=
    unch_same (unch_same (slot_frame (by simp) (Nat.le_refl _) O₁)
      (slot_frame (by simp) (Nat.le_refl _) O₂)) (slot_frame (by simp) (by omega_using [h0]) O₃)
  obtain flag₃ : word s₃.mem base (c.sl FLAG) = BitVec.allOnes 64 := by
    rw [U₃.word (fun w hw => by have := (apart_slW (c := c) (by decide : FLAG ∉ [R2P, BP, D])) w hw; omega_using [h0, this])
      (by omega_using [h0, hn, hF]), hf]
  rw [WP.block_append_iff]
  refine WP.mono (andFlag_ok c hs₃ (by omega_using [h0, hF]) (sl_mod8 c FLAG)) fun s₄ ⟨flag₄, k₄, O₄⟩ => ?_
  obtain hs₄ := hs₃.of_keepRegs k₄ (by decide)
  obtain U₄ : Unch base (slW c [R2P, BP, D, FLAG]) s.mem s₄.mem :=
    unch_same (U₃.mono (by
      intro w hw
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact List.mem_map_of_mem (List.mem_append_left [FLAG] hi)))
      (slot_frame (by simp) (by omega_using [h0]) O₄)
  have keep₄ {i : Nat} (hi : i < 45) (hm : i ∉ [R2P, BP, D, FLAG]) :
      sv c base s₄ i = sv c base s i := sv_unch U₄ h7 hn hi (apart_slW hm)
  refine WP.mono (checkLtP_ok c hs₄ h0 hE hM (by omega_using [h0, hF]) (sl_mod8 c E) (sl_mod8 c MP) (sl_mod8 c FLAG)) fun s₅ ⟨flag₅, k₅, O₅⟩ => ?_
  refine ⟨hs₄.of_keepRegs k₅ (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((((k₁.mono (by simp)).trans (k₂.mono (by simp))).trans (k₃.mono (by simp))).trans
      (k₄.mono (by simp))).trans (k₅.mono (by sub_regs))
  · exact unch_same U₄ (slot_frame (by simp) (by omega_using [h0]) O₅)
  · rw [sv, sv_flag O₅ h0 h7 hn (by decide) (by decide), sv_flag O₄ h0 h7 hn (by decide) (by decide),
      sv_out (O₃.mono (Nat.le_refl _) (by omega_using [h0] : c.sl D + 8 ≤ c.sl D + 8 * c.n)) h7 hn (by decide) (by decide),
      sv_out O₂ h7 hn (by decide) (by decide)]
    exact e₁
  · rw [sv, sv_flag O₅ h0 h7 hn (by decide) (by decide), sv_flag O₄ h0 h7 hn (by decide) (by decide),
      sv_out (O₃.mono (Nat.le_refl _) (by omega_using [h0] : c.sl D + 8 ≤ c.sl D + 8 * c.n)) h7 hn (by decide) (by decide)]
    exact e₂
  · rw [O₅.word (by have := sl_apart c (i := D) (j := FLAG) (by decide); omega_using [h0, this]) (by omega_using [h0, hn, hD]),
      O₄.word (by have := sl_apart c (i := D) (j := FLAG) (by decide); omega_using [h0, this]) (by omega_using [h0, hn, hD])]
    exact tag₃
  · rw [flag₅, flag₄, flag₃, mask₃, BitVec.allOnes_and,
      show wordsVal s₄.mem base (c.sl E) c.n = sv c base s₄ E from rfl,
      show wordsVal s₄.mem base (c.sl MP) c.n = sv c base s₄ MP from rfl,
      keep₄ (by decide) (by decide), keep₄ (by decide) (by decide), hmp, mask_and]

end VG.Proof.EcKey.Compressed.AArch64

end

end

/-! # Coordinate recovery and final checks preserve the parsed encoding -/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/AArch64/Start.lean`, which only this module imported.
section

/-! # Decode the compressed x coordinate with the existing EC setup -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

structure DecompressPre (c : Cfg) (s : State) : Prop where
  pk : (⟨s.gpr .x1, c.C.len + 1⟩ : Region) ∈ s.rd ++ s.wr
  ws : (⟨s.gpr .x2, size⟩ : Region) ∈ s.wr
  disjoint : Region.Disjoint ⟨s.gpr .x1, c.C.len + 1⟩ ⟨s.gpr .x2, size⟩
  fit : (s.gpr .x2).toNat + size ≤ 2 ^ 64

structure DecompressStart (c : Cfg) (s₀ : State) (g : Reg → BitVec 64) (s : State) : Prop where
  scr : Scr s (s₀.gpr .x2) size
  fixed : Fixed c (s₀.gpr .x2) g s.mem
  original : ∀ r ∈ Cfg.saved.map Prod.fst, g r = s₀.gpr r
  out : s.gpr .x20 = s₀.gpr .x0
  pk : s.gpr .x6 = s₀.gpr .x1
  x : sv c (s₀.gpr .x2) s E = keyX c s₀
  flag : word s.mem (s₀.gpr .x2) (c.sl FLAG) = BitVec.allOnes 64
  outside : Outside (s₀.gpr .x2) 0 size s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem decompressStart_ok {c : Cfg} (hc : BaseCfgOk c) {s₀ : State} (hp : DecompressPre c s₀)
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ g s, DecompressStart c s₀ g s → WP isa rest s Q) :
    WP isa (.seq (.block Impl.EcKey.Compressed.AArch64.args)
      (.seq (.block (c.setupWith none)) rest)) s₀ Q := by
  have hsz : size = 8192 := rfl
  have := hc.len8
  have := hc.len_hi
  have := hc.n10
  refine WP.seq (WP.mono (args_ok s₀) fun s₁ ⟨r8, r9, rcx, rsi, rdx, k₁⟩ => ?_)
  obtain rw₁ : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [k₁.rd, k₁.wr]
  obtain hsp : SetupPre c s₁ := by
    obtain hin : ∀ e, e + 8 ≤ c.C.len →
        InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x1 + 1 + BitVec.ofNat 64 e) 8 := by
      intro e he
      rw [BitVec.add_assoc, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]
      exact ⟨_, hp.pk, Offset.contains_base _ (by omega_using [he]) (by omega_arith)⟩
    obtain hd : Region.Disjoint ⟨s₀.gpr .x1 + 1, c.C.len⟩ ⟨s₀.gpr .x2, size⟩ :=
      hp.disjoint.sub_left (Offset.sub_base _ (d := 1) (by omega_using []))
    exact ⟨by rw [k₁.wr, r8]; exact hp.ws,
      by rw [rcx, rw₁]; exact hin, by rw [rsi, rw₁]; exact hin,
      by rw [rdx, rw₁]; exact hin, by rw [rsi, r8]; exact hd,
      by rw [rdx, r8]; exact hd, by rw [rcx, r8]; exact hd, by rw [r8]; exact hp.fit⟩
  refine WP.seq (WP.mono (setup_ok hc (hs := none) (.inl rfl) hsp) fun s₂ S => ?_)
  rw [r8] at S
  apply h s₁.gpr s₂
  refine ⟨S.scr, setup_fixed S,
    fun r hr => k₁.gpr r (by revert r; decide), S.x20.trans (k₁.gpr _ (by decide)),
    (S.keep.gpr _ (by decide)).trans r9, ?_, S.flag, ?_, ?_, ?_⟩
  · rw [S.e, shAt_none, Nat.shiftRight_zero, rdx, k₁.mem]
  · rw [← k₁.mem]
    exact S.unch.outside (by simp)
  · rw [S.keep.rd, k₁.rd]
  · rw [S.keep.wr, k₁.wr]

end VG.Proof.EcKey.Compressed.AArch64
end

end

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/AArch64/Rhs.lean`, which only this module imported.
section

/-! # The curve polynomial used by coordinate recovery -/

section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdh.AArch64 (R2P BP QXM QYM QY W0 W1 W2 W3)
open VG.Impl.EcKey.Compressed.AArch64 (rhsOps)
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Ecdh.AArch64

abbrev rhsSlots : List Nat := [QXM, AP, BP, W1, W2, W3]

def rhsTail : List FOp :=
  [.mul W1 QXM QXM, .mul W2 W1 QXM, .mul W1 AP QXM,
    .add W3 W2 W1, .add W2 W3 BP]

theorem rhsTail_run {F : Type} [Lean.Grind.CommRing F] (e : Nat → F) :
    runOps rhsTail e W2 = e QXM * e QXM * e QXM + e AP * e QXM + e BP := by
  simp only [rhsTail, runOps_cons, runOps_nil, FOp.run, Function.update_apply]
  simp only [W1, W2, W3, QXM, AP, BP, TT, SM, RM, XM, EM, Nat.reduceEqDiff, ↓reduceIte]

theorem rhsTail_reads : readsOk rhsTail [QXM, AP, BP] = true := by decide
theorem rhsTail_slots : ∀ op ∈ rhsTail, ∀ x ∈ op.out :: op.ins, x ∈ rhsSlots := by decide
theorem rhsTail_out : ∀ op ∈ rhsTail, op.out ∈ [W1, W2, W3, TMP] := by decide

structure RhsPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  mod : ModOkA c.MP' size c.C.p s'.mem base
  gpr : ∀ r, r ∉ clob c.n → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unch : Unch base (slW c [QXM, W1, W2, W3, TMP]) s.mem s'.mem
  lt : sv c base s' W2 < c.C.p
  val : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' W2) =
    let x := Fin.ofNat c.C.p (sv c base s E)
    x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b

theorem rhs_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkA c.MP' size c.C.p s.mem base)
    (hr2 : sv c base s R2P = c.R * c.R % c.C.p)
    (hap : sv c base s AP = c.mont c.C.a) (hbp : sv c base s BP = c.mont c.C.b) :
    WP isa (Impl.Weierstrass.AArch64.fprogB c.MP' (rhsOps c)) s (RhsPost c base s) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  change WP isa (.seq (VG.Impl.Weierstrass.AArch64.opProg c.MP'
    (.mul (c.sl QXM) (c.sl E) (c.sl R2P)))
    (VG.Impl.Weierstrass.AArch64.fprogB c.MP' (rhsTail.map (FOp.rename c.sl)))) s _
  obtain hneq : c.sl E ≠ c.sl R2P := by
    intro he
    have := sl_inj c hc.n0 he
    contradiction
  obtain first : VG.Impl.Weierstrass.AArch64.opProg c.MP' (.mul (c.sl QXM) (c.sl E) (c.sl R2P)) =
      c.mulPP (c.sl QXM) (c.sl E) (c.sl R2P) := by
    unfold VG.Impl.Weierstrass.AArch64.opProg Cfg.mulPP
    cases hh : VG.Impl.Weierstrass.AArch64.Mont.callOf c.MP' with
    | none => simp [VG.Impl.Weierstrass.AArch64.opCode, hneq]
    | some fm => obtain ⟨f, m⟩ := fm; simp [hneq, MP'_n]
  rw [first]
  refine WP.seq (WP.mono (slMulP_ok hc hs hM (o := QXM) (a := E) (b := R2P)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hr2]; exact Nat.mod_lt _ (by have := hc.p_ge; omega_using [this])))
    fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_)
  obtain hs₁ := k₁.scr hs
  obtain hM₁ := hM.keepA64 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  obtain v₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ QXM) = Fin.ofNat c.C.p (sv c base s E) :=
    toM_r2 hpR (by simpa only [hr2, Cfg.R] using e₁)
  obtain a₁ : sv c base s₁ AP = c.mont c.C.a :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hap
  obtain b₁ : sv c base s₁ BP = c.mont c.C.b :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hbp
  obtain hL : Lay c.MP' size (· ∈ rhsSlots.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  obtain hAl : Aligned c.MP' (· ∈ rhsSlots.map c.sl) := ⟨fun x hx => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact sl_mod8 c i, MP'_A c, fun f m h => (hc.call_p f m h).2⟩
  obtain I : Inv c.MP' base size c.C.p (· ∈ rhsSlots.map c.sl) ([QXM, AP, BP].map c.sl)
      (fun o => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₁.mem base o c.n)) s₁ := by
    refine ⟨hs₁, hM₁, ?_, ?_, fun _ _ => rfl⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      obtain sub : ∀ i ∈ [QXM, AP, BP], i ∈ rhsSlots := by decide
      exact List.mem_map_of_mem (sub i hi)
    · intro x hx
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact lt₁
      · show sv c base s₁ AP < _
        rw [a₁]
        exact Nat.mod_lt _ (by have := hc.p_ge; omega_using [lt₁])
      · show sv c base s₁ BP < _
        rw [b₁]
        exact Nat.mod_lt _ (by have := hc.p_ge; omega_using [lt₁])
  refine WP.mono (fprogB_ok hL hAl hpR _ I (fun op hop x hx => ?_)
    (by
      intro op hop
      apply Low.of_call
      intro f m h x hx
      obtain ⟨op₀, hop₀, rfl⟩ := List.mem_map.mp hop
      obtain hx' : x ∈ (op₀.out :: op₀.ins).map c.sl := by
        cases op₀ <;> simpa [FOp.rename, FOp.out, FOp.ins] using hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
      obtain hi' := rhsTail_slots op₀ hop₀ i hi
      obtain H : ∀ i ∈ rhsSlots, i < 45 ∧ i ≠ TMP := by decide
      exact sl_own_fn c h7 (H i hi').1 (H i hi').2)
    (readsOk_rename c.sl rhsTail_reads)) fun s₂ ⟨PK, I₂⟩ => ?_
  · obtain ⟨op₀, hop₀, rfl⟩ := List.mem_map.mp hop
    obtain hx' : x ∈ (op₀.out :: op₀.ins).map c.sl := by
      cases op₀ <;> simpa [FOp.rename, FOp.out, FOp.ins] using hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    exact List.mem_map_of_mem (rhsTail_slots _ hop₀ _ hi)
  obtain hw : c.sl W2 ∈ validAfter (rhsTail.map (FOp.rename c.sl)) ([QXM, AP, BP].map c.sl) :=
    (mem_validAfter _ _).mpr (Or.inr (by simp [rhsTail, FOp.rename, FOp.out]))
  obtain v₂ := I₂.val _ hw
  obtain H : ∀ op ∈ rhsTail, op.out ≠ TMP ∧ op.out ≠ 54 ∧ op.out ≠ 61 ∧ op.out ≠ 82 := by decide
  rw [congrFun (runOps_rename c.sl rhsTail _ fun op hop y h =>
    sl_inj c hc.n0 h (.inr (H op hop).2) (.inl (H op hop).1)) W2, rhsTail_run] at v₂
  obtain U₁ : Unch base (slW c [QXM, W1, W2, W3, TMP]) s.mem s₁.mem :=
    unch_slots (MP'_n c) rfl k₁.unch (by simp) (by simp)
  obtain U₂ : Unch base (slW c [QXM, W1, W2, W3, TMP]) s₁.mem s₂.mem := PK.unch.mono fun w hw => by
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hw
      obtain ⟨op, hop, rfl⟩ := List.mem_map.mp ho
      obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
      exact List.mem_map.mpr ⟨op₀.out, List.mem_cons_of_mem _ (rhsTail_out op₀ h₀), by
        rw [FOp.out_rename]; rfl⟩
    · obtain rfl := List.mem_singleton.mp hw
      exact List.mem_map_of_mem (by decide)
  refine ⟨PK.scr hs₁, I₂.mod, fun r hr => (PK.gpr r hr).trans (k₁.gpr r hr),
    PK.rd.trans k₁.rd, PK.wr.trans k₁.wr,
    (U₁.trans U₂).mono (by intro w hw; simpa only [List.mem_append, or_self] using hw), I₂.lt _ hw, ?_⟩
  simpa only [sv, MP'_n, a₁, b₁, toM_cmont hc, v₁] using v₂

end VG.Proof.EcKey.Compressed.AArch64
end

end

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/AArch64/DecompressFront.lean`, which only this module imported.
section

/-! # Prepare the polynomial and retain the compressed input's checks -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Impl.Ecdh.AArch64 (R2P BP QXM W1 W2 W3)
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Ecdh.AArch64

abbrev CompressedPrefix (c : Cfg) (s : State) : Prop :=
  (s.mem (s.gpr .x1) = 2 ∨ s.mem (s.gpr .x1) = 3) ∧ keyX c s < c.C.p

structure DecompressFront (c : Cfg) (s₀ : State) (g : Reg → BitVec 64) (s : State) : Prop where
  scr : Scr s (s₀.gpr .x2) size
  fixed : Fixed c (s₀.gpr .x2) g s.mem
  original : ∀ r ∈ Cfg.saved.map Prod.fst, g r = s₀.gpr r
  out : s.gpr .x20 = s₀.gpr .x0
  x : sv c (s₀.gpr .x2) s E = keyX c s₀
  tag : word s.mem (s₀.gpr .x2) (c.sl D) = (s₀.mem (s₀.gpr .x1)).setWidth 64
  r2 : sv c (s₀.gpr .x2) s R2P = c.R * c.R % c.C.p
  rhs_lt : sv c (s₀.gpr .x2) s W2 < c.C.p
  rhs : toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .x2) s W2) =
    let x := Fin.ofNat c.C.p (keyX c s₀)
    x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b
  flag : word s.mem (s₀.gpr .x2) (c.sl FLAG) = mask (CompressedPrefix c s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- Keep the input checks while a field-arithmetic phase writes other slots. -/
theorem DecompressFront.frame {c : Cfg} (hc : BaseCfgOk c) {s₀ s t : State}
    {g : Reg → BitVec 64} (F : DecompressFront c s₀ g s)
    (K : KeepRegs (powClob c.n) s t) {W : List (Nat × Nat)}
    (U : Unch (s₀.gpr .x2) W s.mem t.mem) (hW : FixedOk c W)
    (ha : ∀ i ∈ [E, D, R2P, W2, FLAG], ∀ w ∈ W,
      c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i) : DecompressFront c s₀ g t := by
  have hn := F.scr.nowrap
  have h0 := hc.n0
  have h7 := hc.n10
  have e {i : Nat} (hi : i < 45) (hm : i ∈ [E, D, R2P, W2, FLAG]) :
      sv c (s₀.gpr .x2) t i = sv c (s₀.gpr .x2) s i := sv_unch U h7 hn hi (ha i hm)
  have ew {i : Nat} (hi : i < 45) (hm : i ∈ [E, D, R2P, W2, FLAG]) :
      word t.mem (s₀.gpr .x2) (c.sl i) = word s.mem (s₀.gpr .x2) (c.sl i) :=
    U.word (fun w hw => by have := ha i hm w hw; omega_using [h0, this])
      (by have := sl_le c h7 hi; omega_using [hn, h0, this])
  refine ⟨F.scr.of_keepRegs K (x0_not_powClob _), F.fixed.unch h7 hn hW U, F.original,
    (K.gpr _ (x20_not_powClob _)).trans F.out,
    (e (by decide) (by simp)).trans F.x, (ew (by decide) (by simp)).trans F.tag,
    (e (by decide) (by simp)).trans F.r2, ?_, ?_, (ew (by decide) (by simp)).trans F.flag,
    K.rd.trans F.rd, K.wr.trans F.wr⟩
  · rw [e (by decide) (by simp)]; exact F.rhs_lt
  · rw [e (by decide) (by simp)]; exact F.rhs

theorem decompressFront_ok {c : Cfg} (hc : BaseCfgOk c) {s₀ : State} (hp : DecompressPre c s₀)
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ g s, DecompressFront c s₀ g s → WP isa rest s Q) :
    WP isa (.seq (.block Impl.EcKey.Compressed.AArch64.args)
      (.seq (.block (c.setupWith none))
      (.seq (.block (Impl.EcKey.Compressed.AArch64.decompressPeer c))
      (.seq (Impl.Weierstrass.AArch64.fprogB c.MP'
        (Impl.EcKey.Compressed.AArch64.rhsOps c)) rest)))) s₀ Q := by
  apply decompressStart_ok hc hp
  intro g s S
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := S.scr.nowrap
  refine WP.seq (WP.mono (decompressPeer_ok hc S.scr S.pk
    (by rw [S.rd, S.wr]; exact hp.pk) hp.disjoint S.fixed.mp S.flag)
    fun s₁ ⟨hs₁, k₁, U₁, r2₁, bp₁, tag₁, flag₁⟩ => ?_)
  obtain F₁ := S.fixed.unch h7 hn (fixedOk_slW (l := [R2P, BP, D, FLAG]) (by decide)) U₁
  obtain x₁ : sv c (s₀.gpr .x2) s₁ E = keyX c s₀ :=
    (sv_unch U₁ h7 hn (by decide) (apart_slW (by decide))).trans S.x
  obtain lead : s.mem (s₀.gpr .x1) = s₀.mem (s₀.gpr .x1) := by
    obtain e := keep_of_disjoint' S.outside hp.disjoint (by omega_using [hn]) (i := 0) (by omega_using [])
      (by have := hc.len_hi; omega_using [h7, this])
    simpa only [BitVec.add_zero] using e
  rw [lead, S.x] at flag₁
  rw [lead] at tag₁
  refine WP.seq (WP.mono (rhs_ok hc hs₁ (modP_of hc F₁.mp) r2₁ F₁.ap bp₁) fun s₂ R => ?_)
  obtain F₂ := F₁.unch h7 hn (fixedOk_slW (l := [QXM, W1, W2, W3, TMP]) (by decide)) R.unch
  have eq₂ {i : Nat} (hi : i < 45) (hw : i ∉ [QXM, W1, W2, W3, TMP]) :
      sv c (s₀.gpr .x2) s₂ i = sv c (s₀.gpr .x2) s₁ i :=
    sv_unch R.unch h7 hn hi (apart_slW hw)
  apply h g s₂
  refine ⟨R.scr, F₂, S.original, ?_, (eq₂ (by decide) (by decide)).trans x₁,
    ?_, (eq₂ (by decide) (by decide)).trans r2₁, R.lt, ?_, ?_, ?_, ?_⟩
  · rw [R.gpr _ (by intro h; exact (by decide : VG.AArch64.Reg.x20 ∉ VG.Proof.Mont.AArch64.clobAll) (VG.Proof.Mont.AArch64.mem_clobAll h)), k₁.gpr _ (by decide), S.out]
  · exact (R.unch.word (fun w hw => by
      have := (apart_slW (c := c) (by decide : D ∉ [QXM, W1, W2, W3, TMP])) w hw
      have := hc.n0
      omega_arith) (by have := sl_le c h7 (i := D) (by decide); omega_using [h0, hn, this])).trans tag₁
  · simpa only [x₁] using R.val
  · rw [flag_unch R.unch h7 hc.n0 hn (by decide), flag₁]
  · rw [R.rd, k₁.rd, S.rd]
  · rw [R.wr, k₁.wr, S.wr]

end VG.Proof.EcKey.Compressed.AArch64
end

end

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Impl.Ecdh.AArch64 (QY QYM R2P W0 W1 W2 W3)
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.EcKey.Compressed (chooseRoot)

def keyRhs (c : Cfg) (s : State) : Spec.Weierstrass.Fe c.C :=
  let x := Fin.ofNat c.C.p (keyX c s)
  x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b

def keyRoot (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C) (s : State) :=
  chooseRoot (root (keyRhs c s)) ((s.mem (s.gpr .x1)).toNat % 2)

def CompressedAccept (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C)
    (s : State) : Prop := CompressedPrefix c s ∧
  (keyRoot c root s * keyRoot c root s = keyRhs c s ∧
    (keyRoot c root s).val % 2 = (s.mem (s.gpr .x1)).toNat % 2)

instance (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C) (s : State) :
    Decidable (CompressedAccept c root s) := inferInstanceAs (Decidable (_ ∧ (_ ∧ _)))

structure DecompressChecked (c : Cfg)
    (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C)
    (s₀ : State) (g : Reg → BitVec 64) (s : State) : Prop where
  scr : Scr s (s₀.gpr .x2) size
  saved : Spill.Saved (s₀.gpr .x2) g Cfg.saved s.mem
  original : ∀ r ∈ Cfg.saved.map Prod.fst, g r = s₀.gpr r
  out : s.gpr .x20 = s₀.gpr .x0
  x : sv c (s₀.gpr .x2) s E = keyX c s₀
  y : sv c (s₀.gpr .x2) s QY = (keyRoot c root s₀).val
  flag : word s.mem (s₀.gpr .x2) (c.sl FLAG) = mask (CompressedAccept c root s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem decompressMiddle_ok {c : Cfg} (hc : BaseCfgOk c)
    {root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C} (hroot : CandidateCorrect c root)
    {s₀ s : State} {g : Reg → BitVec 64} (F : DecompressFront c s₀ g s) :
    WP isa (.seq (Impl.EcKey.Compressed.AArch64.rootCandidate c)
      (.seq (Impl.EcKey.Compressed.AArch64.selectRoot c)
        (Impl.EcKey.Compressed.AArch64.checkRoot c))) s (DecompressChecked c root s₀ g) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := F.scr.nowrap
  refine WP.seq (WP.mono (hroot _ s F.scr (modP_of hc F.fixed.mp) F.rhs_lt F.fixed.onep)
    fun s₁ C => ?_)
  obtain F₁ := F.frame hc C.keep C.unch (candidate_fixed hc) (by
    intro i hi
    obtain h : ∀ i ∈ [E, D, R2P, W2, FLAG], i < 45 ∧ i ∉ ACC :: candidateSlots := by decide
    exact candidate_apart hc (h i hi).1 (h i hi).2)
  obtain root₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .x2) s₁ ACC) = root (keyRhs c s₀) := by
    rw [C.val, F.rhs]; rfl
  refine WP.seq (WP.mono (selectRoot_ok hc F₁.scr (modP_of hc F₁.fixed.mp)
    F₁.fixed.one F₁.fixed.zero) fun s₂ S => ?_)
  obtain F₂ := F₁.frame hc (S.keep.mono (fun _ hr => List.mem_cons_of_mem _ hr)) S.unch
    (fixedOk_slW (l := [QY, W0, TMP]) (by decide)) (by
      intro i hi
      obtain h : ∀ i ∈ [E, D, R2P, W2, FLAG], i ∉ [QY, W0, TMP] := by decide
      exact apart_slW (h i hi) (by
        obtain H : ∀ i ∈ [E, D, R2P, W2, FLAG], i < 45 := by decide
        have := H i hi
        omega_using [this]) (by decide))
  obtain y₂ : Fin.ofNat c.C.p (sv c (s₀.gpr .x2) s₂ QY) = keyRoot c root s₀ := by
    rw [S.val, root₁, F₁.tag]
    simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show
      (s₀.mem (s₀.gpr .x1)).toNat < 2 ^ 64 from Nat.lt_trans (BitVec.isLt _) (by decide))]
    rfl
  obtain yval₂ : sv c (s₀.gpr .x2) s₂ QY = (keyRoot c root s₀).val := by
    simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt S.lt] using congrArg Fin.val y₂
  refine WP.mono (checkRoot_ok hc F₂.scr (modP_of hc F₂.fixed.mp) S.lt
    F₂.rhs_lt F₂.r2 F₂.flag) fun s₃ K => ?_
  obtain F₃ := F₂.fixed.unch h7 hn
    (fixedOk_slW (l := [QYM, W1, W3, TMP, FLAG]) (by decide)) K.unch
  have e₃ {i : Nat} (hi : i < 45) (hw : i ∉ [QYM, W1, W3, TMP, FLAG]) :
      sv c (s₀.gpr .x2) s₃ i = sv c (s₀.gpr .x2) s₂ i :=
    sv_unch K.unch h7 hn hi (apart_slW hw)
  refine ⟨K.scr, F₃.saved, F.original, (K.keep.gpr _ (by intro h; exact (by decide : VG.AArch64.Reg.x20 ∉ VG.Proof.Mont.AArch64.clobAll) (VG.Proof.Mont.AArch64.mem_clobAll h))).trans F₂.out,
    (e₃ (by decide) (by decide)).trans F₂.x,
    (e₃ (by decide) (by decide)).trans yval₂, ?_, K.keep.rd.trans F₂.rd, K.keep.wr.trans F₂.wr⟩
  rw [K.flag, y₂, yval₂, F₂.rhs, F₂.tag]
  simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show
    (s₀.mem (s₀.gpr .x1)).toNat < 2 ^ 64 from Nat.lt_trans (BitVec.isLt _) (by decide))]
  simp only [mask, CompressedAccept, keyRhs, and_assoc]

end VG.Proof.EcKey.Compressed.AArch64

end

end

/-! ### `EcKey.Compressed.AArch64.DecompressContract`, which this module and modules that import it used -/

section

/-! # Decompression's signature obligations on AArch64 -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64

def decompressContract (C : Spec.Weierstrass.Curve)
    (root : Spec.Weierstrass.Fe C → Spec.Weierstrass.Fe C) : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 2 * C.len + 1⟩
    let pk : Region := ⟨s.gpr .x1, C.len + 1⟩
    let ws : Region := ⟨s.gpr .x2, 8192⟩
    s.rd = [pk] ∧ s.wr = [out, ws] ∧
      pk.Disjoint out ∧ pk.Disjoint ws ∧ out.Disjoint ws ∧
      (s.gpr .x0).toNat + 2 * C.len + 1 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match Impl.EcKey.Compressed.decode C root (Spec.EcKey.bytesAt s.mem (s.gpr .x1) (C.len + 1)) with
    | some Q => (s'.gpr .x0).setWidth 32 = 1 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .x0) (2 * C.len + 1) = Spec.EcKey.encodePoint Q
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .x0) (2 * C.len + 1) = List.replicate (2 * C.len + 1) 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧
    s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2

theorem decompress_implies (I : Spec.EcKey.Instance)
    (root : Spec.Weierstrass.Fe I.curve → Spec.Weierstrass.Fe I.curve)
    (hf : RootFacts root)
    (hsat : ∃ s, (I.decompressPublicKeyContract abi 0).pre s) :
    (decompressContract I.curve root).Implies (I.decompressPublicKeyContract abi 0) where
  pre := by
    sig_implies_pre [Spec.EcKey.Instance.decompressPublicKeyContract,
      Spec.EcKey.Instance.decompressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, decompressContract]
  post := by
    intro s s' _ h
    sig_post [Spec.EcKey.Instance.decompressPublicKeyContract,
      Spec.EcKey.Instance.decompressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, decompressContract]
    cases he : Impl.EcKey.Compressed.decode I.curve root
        (Spec.EcKey.bytesAt s.mem (s.gpr .x1) (I.curve.len + 1)) with
    | none =>
      simp only [decompressContract, he] at h
      exact Or.inr ⟨h.1, (decode_none_iff hf _).mp he, h.2⟩
    | some Q =>
      simp only [decompressContract, he] at h
      exact Or.inl ⟨h.1, Q, decode_sound he, h.2⟩
  pub := by
    sig_implies_pub [Spec.EcKey.Instance.decompressPublicKeyContract,
      Spec.EcKey.Instance.decompressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, decompressContract]
  sat := hsat

def decompressSatState (len : Nat) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x8000 | _ => 0
  sp := 0x20000
  c := false
  mem _ := 0
  rd := [⟨0x2000, len + 1⟩]
  wr := [⟨0x1000, 2 * len + 1⟩, ⟨0x8000, 8192⟩]

end VG.Proof.EcKey.Compressed.AArch64

end

end

/-! # Decompression meets the merged API contract -/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/AArch64/DecompressFinish.lean`, which only this module imported.
section

/-! # Reuse public-key derivation's verified output encoder -/

section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass

 theorem decompressFinish_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) {out : Addr} (hout : s.gpr .x20 = out)
    (hw : (⟨out, 1 + 2 * c.C.len⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨out, 1 + 2 * c.C.len⟩ ⟨base, size⟩)
    (hfit : out.toNat + (1 + 2 * c.C.len) ≤ 2 ^ 64)
    {g : Reg → BitVec 64} (hsv : Spill.Saved base g Cfg.saved s.mem) (b : Bool)
    (hf : word s.mem base (c.sl FLAG) = if b then BitVec.allOnes 64 else 0) :
    WP isa (.block (Impl.EcKey.Compressed.AArch64.decompressFinish c)) s fun t =>
      Spec.Ecdsa.bytesAt t.mem out (1 + 2 * c.C.len) =
        (if b then 4 :: (toBytes c.C.len (sv c base s E) ++
          toBytes c.C.len (sv c base s Impl.Ecdh.AArch64.QY))
          else List.replicate (1 + 2 * c.C.len) 0) ∧
      (t.gpr .x0).setWidth 32 = (if b then 1 else 0) ∧
      (∀ r ∈ Cfg.saved.map Prod.fst, t.gpr r = g r) :=
  VG.Proof.EcKey.AArch64.pointFinish_ok hc (by decide) (by decide) hs hout hfit hw hd hsv b hf

end VG.Proof.EcKey.Compressed.AArch64
end

end

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass

theorem decompress_key (c : Cfg) (root : Fe c.C → Fe c.C) (s : State) :
    Impl.EcKey.Compressed.decode c.C root
      (Spec.EcKey.bytesAt s.mem (s.gpr .x1) (c.C.len + 1)) =
    if CompressedAccept c root s then
      some (.affine (Fin.ofNat c.C.p (keyX c s)) (keyRoot c root s)) else none := by
  have hb : Spec.Ecdsa.bytesAt s.mem (s.gpr .x1) (c.C.len + 1) =
      s.mem (s.gpr .x1) :: Spec.Ecdsa.bytesAt s.mem (s.gpr .x1 + 1) c.C.len := by
    rw [Nat.add_comm c.C.len 1, bytesAt_add]
    simp only [Spec.Ecdsa.bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero,
      List.cons_append, List.nil_append]
    rfl
  apply decode_checked_eq root (length_bytesAt _ _ _)
    (by change (Spec.Ecdsa.bytesAt _ _ _).head? = _; rw [hb]; rfl)
    (by change ofBytes ((Spec.Ecdsa.bytesAt _ _ _).drop 1) = _; rw [hb]; rfl)

theorem decompress_correct (c : Cfg) (hc : BaseCfgOk c)
    (root : Fe c.C → Fe c.C) (hroot : CandidateCorrect c root)
    (hn : CallsKeep (Impl.EcKey.Compressed.AArch64.decompress c))
    (hu : KeepsUntouched (Impl.EcKey.Compressed.AArch64.decompress c))
    (hv : (Impl.EcKey.Compressed.AArch64.decompress c).allInstrs keepsV = true)
    (s : State) (hs : (decompressContract c.C root).pre s) :
    ∃ t s', Exec isa (Impl.EcKey.Compressed.AArch64.decompress c) s t s' ∧
      abiPreserved s s' ∧ (decompressContract c.C root).post s s' := by
  obtain ⟨hrd, hwr, hpo, hpw, how, hfit, hwfit⟩ := hs
  have hp : DecompressPre c s :=
    ⟨by rw [hrd]; simp, by rw [hwr]; simp, hpw, hwfit⟩
  have hrun : WP isa (Impl.EcKey.Compressed.AArch64.decompress c) s fun s' =>
      (decompressContract c.C root).post s s' ∧ ∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s.gpr r := by
    apply decompressFront_ok hc hp
    intro g t F
    refine WP.seq (WP.mono (decompressMiddle_ok hc hroot F) fun u U => ?_)
    refine WP.mono (decompressFinish_ok hc U.scr U.out
      (by rw [U.wr, hwr, show 1 + 2 * c.C.len = 2 * c.C.len + 1 by omega_using []]; simp)
      (by simpa only [Nat.add_comm] using how)
      (by omega_using [hfit]) U.saved
      (decide (CompressedAccept c root s)) (by simp only [U.flag, mask, decide_eq_true_eq]))
      fun s' ⟨hout, hret, hsave⟩ => ?_
    refine ⟨?_, fun r hr => (hsave r hr).trans (U.original r hr)⟩
    dsimp only [decompressContract]
    rw [decompress_key]
    rw [U.x, U.y] at hout
    change Spec.EcKey.bytesAt s'.mem (s.gpr .x0) (1 + 2 * c.C.len) = _ at hout
    simp only [decide_eq_true_eq] at hret hout
    by_cases hk : CompressedAccept c root s
    · rw [ite_eq_left hk] at hret hout ⊢
      refine ⟨hret, ?_⟩
      change Spec.EcKey.bytesAt s'.mem (s.gpr .x0) (2 * c.C.len + 1) =
        4 :: (toBytes c.C.len (Fin.ofNat c.C.p (keyX c s)).val ++ toBytes c.C.len (keyRoot c root s).val)
      simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt hk.1.2, Nat.add_comm] using hout
    · rw [ite_eq_right hk] at hret hout ⊢
      exact ⟨hret, by simpa only [Nat.add_comm] using hout⟩
  obtain ⟨t, s', he, hpost, hsave⟩ := hrun
  exact ⟨t, s', he, abiPreserved_of he hn hu hv hsave, hpost⟩

end VG.Proof.EcKey.Compressed.AArch64
