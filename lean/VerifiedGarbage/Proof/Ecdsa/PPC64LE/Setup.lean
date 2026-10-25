module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.BytesLen
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Copy
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Mont.PPC64LE.Const
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# ECDSA on PPC64LE: the setup

`Cfg.setupWith A` saves `r14`, `r31` and `lr` at the start of the working
space (`saveCode_ok`), moves `out` to `r14` and the working space's base to
`r3`, reads `k`, `d` and the hash (`len` bytes each) big-endian into their
slots from the registers `A` names (`setupLoad_ok`), shifts the slot `A.hs`
holding a hash (`setupShift_ok`), stores the constants (`setupConsts_ok`, by
induction on the list) and sets the flag to all ones: `setup_ok`, the state
`SetupPost` describes. As on 32-bit ARM (`Proof/Ecdsa/Arm/Setup.lean`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Spec.Weierstrass

theorem exec_mov {s : State} {d r : Reg} : exec (mov d r) s = some (s.write d (s.gpr r)) := by
  rw [mov, exec_logic]; simp only [BitVec.or_self]

/-! ## The saves -/

theorem saveCode_eq (sc : Reg) : Cfg.saveCode sc =
    [.store .d .r14 sc 0, .store .d .r31 sc 8, .mflr .r0, .store .d .r0 sc 16, mov .r14 .r3, mov .r3 sc] := rfl

/-- `r14`, `r31` and `lr` to `[sc]`, `out` to `r14` and the working space's
base to `r3`. -/
theorem saveCode_ok {s : State} {base : Addr} {sc : Reg} (hsc : sc ∉ [.r0, .r3, .r14])
    (hb : s.gpr sc = base) (hw : (⟨base, size⟩ : Region) ∈ s.wr) (hfit : base.toNat + size ≤ 2 ^ 64) :
    WP isa (.block (Cfg.saveCode sc)) s fun t =>
      WsReg t base ∧ Kp [.r0, .r3, .r14] s t ∧ t.gpr .r14 = s.gpr .r3 ∧
      t.mem = ((s.mem.writeW (off base 0) (s.gpr .r14)).writeW (off base 8) (s.gpr .r31)).writeW
        (off base 16) s.lr := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hsc
  obtain ⟨hs0, hs3, hs14⟩ := hsc
  have hs : Ws s base size := ⟨⟨size, Nat.le_refl _, hw, hfit⟩, by decide⟩
  have ha : At s base sc 0 := by rw [At, hb, off]; exact (BitVec.add_zero _).symm
  rw [saveCode_eq]
  refine wp_step (std0_ok hs ha hs0 (by decide) (by decide)) ?_
  refine wp_step (std0_ok (hs.store _) (ha.store _) hs0 (by decide) (by decide)) ?_
  refine wp_step exec_mflr ?_
  refine wp_step (std0_ok ((hs.store _).store _ |>.write _ _) (((ha.store _).store _).write _ hs0)
    hs0 (by decide) (by decide)) ?_
  refine wp_step exec_mov ?_
  refine wp_step exec_mov (WP.block_nil ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩)
  · simp only [write_gpr, ite_true, hs14, hs0, ite_false]; exact hb
  · exact hw
  · exact hfit
  · exact ((((Kp.store _ _ _).trans (Kp.store _ _ _)).trans (Kp.write _ _ (by decide))).trans
      (Kp.store _ _ _) |>.trans (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))
  · simp only [write_gpr, ite_true, reduceCtorEq, ite_false]
  · simp only [write_mem, write_gpr, ite_true]

/-- What the saves leave in memory: the three words, and nothing changed
past them. -/
theorem saves_mem (m : Mem) (base : Addr) (hn : base.toNat + size ≤ 2 ^ 64) (a b c : BitVec 64) :
    Outside base 0 24 m (((m.writeW (off base 0) a).writeW (off base 8) b).writeW (off base 16) c) ∧
    word (((m.writeW (off base 0) a).writeW (off base 8) b).writeW (off base 16) c) base 0 = a ∧
    word (((m.writeW (off base 0) a).writeW (off base 8) b).writeW (off base 16) c) base 8 = b ∧
    word (((m.writeW (off base 0) a).writeW (off base 8) b).writeW (off base 16) c) base 16 = c := by
  have := hn
  have O₁ := writeW_outside m base (d := 0) a (by omega_arith)
  have O₂ := writeW_outside (m.writeW (off base 0) a) base (d := 8) b (by omega_arith)
  have O₃ := writeW_outside ((m.writeW (off base 0) a).writeW (off base 8) b) base (d := 16) c (by omega_arith)
  refine ⟨((O₁.mono (Nat.le_refl _) (by omega_arith)).trans (O₂.mono (by omega_arith) (by omega_arith))).trans
    (O₃.mono (by omega_arith) (by omega_arith)), ?_, ?_, word_writeW_self _ _ _ _⟩
  · rw [O₃.word (by omega_arith) (by omega_arith), O₂.word (by omega_arith) (by omega_arith), word_writeW_self]
  · rw [O₃.word (by omega_arith) (by omega_arith), word_writeW_self]

/-! ## Reading `k`, `d` and the hash -/

/-- The `len` bytes at `p` (readable, outside the working space, and so
unchanged since `s`) to slot `i`. -/
theorem setupLoad_ok {c : Cfg} (hc : CfgOk c) {s t : State} {base : Addr} {i : Nat} {src : Reg}
    {p : Addr} (hw : WsReg t base) (hi : i < 45) (hsrc : src ∉ [.r0, .r8, .r9]) (hp : t.gpr src = p)
    (hfit : p.toNat + c.C.len ≤ 2 ^ 64)
    (hin : ∀ e, e + 8 ≤ c.C.len → InRegions (t.rd ++ t.wr) (p + BitVec.ofNat 64 e) 8)
    (hd : Region.Disjoint ⟨p, c.C.len⟩ ⟨base, size⟩) (ho : Outside base 0 4096 s.mem t.mem) :
    WP isa (.block (loadBytes c.C.len c.n (c.sl i) src)) t fun t' =>
      wordsVal t'.mem base (c.sl i) c.n = ofBytes (Spec.Ecdsa.bytesAt s.mem p c.C.len) ∧
      Kp ldClob t t' ∧ Outside base (c.sl i) (8 * c.n) t.mem t'.mem := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hsrc
  have hsz : size = 8192 := rfl
  have hl := sl_le c hc.n10 hi
  have := hc.len_hi
  have := hc.len8
  have := hc.len_lo
  have hsub : Region.Sub ⟨base + BitVec.ofNat 64 (c.sl i), 8 * c.n⟩ ⟨base, size⟩ :=
    Offset.sub_base base (by omega_arith)
  refine WP.mono (loadBytes_ok hw.ws hw.at3 hsrc.1 hsrc.2.1 hsrc.2.2 (by omega_arith) (sl_al c i) (by omega_arith)
    (by omega_arith) hc.len_hi (by omega_arith) (by rw [hp]; exact hin) (by rw [hp]; exact hd.sub_right hsub))
    fun t' ⟨e, k, O⟩ => ⟨?_, k, O⟩
  have hd' := hd.sub_right (Region.sub_prefix (base := base) (show 4096 ≤ size by decide))
  have hb : Spec.Ecdsa.bytesAt t.mem p c.C.len = Spec.Ecdsa.bytesAt s.mem p c.C.len :=
    List.map_congr_left fun j hj =>
      keep_of_disjoint' ho hd' (by decide) (List.mem_range.mp hj) (by omega_arith)
  rw [e, hp, hb]

/-! ## The hash's shift -/

/-- The shift of slot `hs`, if any, by the bits of a hash that are not
`e`'s: only the slots of `k`, `d` and the hash change. -/
theorem setupShift_ok {c : Cfg} (hc : CfgOk c) {hs : Option Nat} (hhs : ShiftOk hs) {t : State}
    {base : Addr} (hw : WsReg t base) :
    WP isa (.block (c.shiftCode hs)) t fun t' =>
      wordsVal t'.mem base (c.sl K) c.n = wordsVal t.mem base (c.sl K) c.n >>> shAt c hs K ∧
      wordsVal t'.mem base (c.sl D) c.n = wordsVal t.mem base (c.sl D) c.n >>> shAt c hs D ∧
      wordsVal t'.mem base (c.sl E) c.n = wordsVal t.mem base (c.sl E) c.n >>> shAt c hs E ∧
      Kp shrClob t t' ∧ Outside base (c.sl K) (24 * c.n) t.mem t'.mem := by
  have hn := hw.nowrap
  have h7 := hc.n10
  have hKl := sl_le c h7 (i := K) (by decide)
  have hEl := sl_le c h7 (i := E) (by decide)
  have hKD : c.sl D = c.sl K + 8 * c.n := by rw [sl_eq, sl_eq]; simp only [D, K]; omega_arith
  have hKE : c.sl E = c.sl K + 16 * c.n := by rw [sl_eq, sl_eq]; simp only [E, K]; omega_arith
  have nil : WP isa (.block ([] : List Instr)) t fun t' =>
      wordsVal t'.mem base (c.sl K) c.n = wordsVal t.mem base (c.sl K) c.n >>> 0 ∧
      wordsVal t'.mem base (c.sl D) c.n = wordsVal t.mem base (c.sl D) c.n >>> 0 ∧
      wordsVal t'.mem base (c.sl E) c.n = wordsVal t.mem base (c.sl E) c.n >>> 0 ∧
      Kp shrClob t t' ∧ Outside base (c.sl K) (24 * c.n) t.mem t'.mem :=
    WP.block_nil ⟨Nat.shiftRight_zero.symm, Nat.shiftRight_zero.symm, Nat.shiftRight_zero.symm,
      Kp.refl _ _, Outside.refl _ _ _ _⟩
  rcases hhs with rfl | rfl | rfl
  · exact nil
  · have hDl := sl_le c h7 (i := D) (by decide)
    by_cases h0 : c.sh = 0
    · simp only [Cfg.shiftCode, h0, ite_true]
      rw [shAt_self, h0, shAt_D_K, shAt_D_E]; exact nil
    · simp only [Cfg.shiftCode, h0, ite_false]
      refine WP.mono (shrWords_ok hw.ws hw.at3 (o := c.sl D) (by omega_arith) (sl_al c D) (by omega_arith) hc.sh)
        fun t' ⟨e, k, O⟩ => ⟨?_, ?_, ?_, k, O.mono (by omega_arith) (by omega_arith)⟩
      · rw [shAt_D_K, Nat.shiftRight_zero]; exact O.wordsVal (by omega_arith) (by omega_arith)
      · rw [shAt_self]; exact e
      · rw [shAt_D_E, Nat.shiftRight_zero]; exact O.wordsVal (by omega_arith) (by omega_arith)
  · by_cases h0 : c.sh = 0
    · simp only [Cfg.shiftCode, h0, ite_true]
      rw [shAt_self, h0, shAt_E_D, shAt_E_K]; exact nil
    · simp only [Cfg.shiftCode, h0, ite_false]
      refine WP.mono (shrWords_ok hw.ws hw.at3 (o := c.sl E) (by omega_arith) (sl_al c E) (by omega_arith) hc.sh)
        fun t' ⟨e, k, O⟩ => ⟨?_, ?_, ?_, k, O.mono (by omega_arith) (by omega_arith)⟩
      · rw [shAt_E_K, Nat.shiftRight_zero]; exact O.wordsVal (by omega_arith) (by omega_arith)
      · rw [shAt_E_D, Nat.shiftRight_zero]; exact O.wordsVal (by omega_arith) (by omega_arith)
      · rw [shAt_self]; exact e

/-! ## The constants -/

/-- The constants of `l`, apart slots below `17`, each in its slot; only their
slots change. -/
theorem setupConsts_ok {c : Cfg} (hc : CfgOk c) {base : Addr} : ∀ (l : List (Nat × Nat)) {t : State},
    WsReg t base → (∀ ix ∈ l, ix.1 < 45 ∧ ix.2 < 2 ^ (64 * c.n)) → (l.map Prod.fst).Nodup →
    WP isa (.block (l.flatMap (fun (i, x) => VG.Impl.Mont.PPC64LE.setConst c.n (c.sl i) x))) t fun t' =>
      (∀ ix ∈ l, wordsVal t'.mem base (c.sl ix.1) c.n = ix.2) ∧ Kp [.r11] t t' ∧
      Unch base (l.map fun ix => (c.sl ix.1, 8 * c.n)) t.mem t'.mem
  | [], _, _, _, _ => WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, Kp.refl _ _, Unch.refl _ _ _⟩
  | (i, x) :: l, t, hw, hb, hnd => by
    rw [List.flatMap_cons]
    have hi := hb (i, x) List.mem_cons_self
    have hl := sl_le c hc.n10 (i := i) hi.1
    refine wp_append (WP.mono (setConst_ok hw.ws hw.at3 (o := c.sl i) (by omega_arith) hi.2) fun t₁ ⟨O₁, e₁, k₁⟩ => ?_)
    rw [← wordsVal_eq_val32] at e₁
    rw [List.map_cons, List.nodup_cons] at hnd
    refine WP.mono (setupConsts_ok hc l (hw.of_kp k₁) (fun ix h => hb ix (List.mem_cons_of_mem _ h)) hnd.2)
      fun t' ⟨e', k', U'⟩ => ⟨fun ix h => ?_, k₁.trans k',
        show Unch base ([(c.sl i, 8 * c.n)] ++ l.map fun ix => (c.sl ix.1, 8 * c.n)) t.mem t'.mem from
          O₁.unch.trans U'⟩
    rcases List.mem_cons.mp h with rfl | h
    · refine (U'.wordsVal (fun w hw' => ?_) (by have := hw.nowrap; dsimp only; omega_arith)).trans e₁
      obtain ⟨jy, hjy, rfl⟩ := List.mem_map.mp hw'
      exact sl_apart c fun heq => hnd.1 (heq ▸ List.mem_map_of_mem hjy)
    · exact e' ix h

theorem consts_fst (c : Cfg) :
    c.consts.map Prod.fst = [0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] := rfl

theorem consts_nodup (c : Cfg) : (c.consts.map Prod.fst).Nodup := by
  rw [consts_fst]; decide

theorem consts_bounds {c : Cfg} (hc : CfgOk c) :
    ∀ ix ∈ c.consts, ix.1 < 17 ∧ ix.2 < 2 ^ (64 * c.n) := by
  intro ix h
  refine ⟨?_, ?_⟩
  · have := List.mem_map_of_mem (f := Prod.fst) h
    rw [consts_fst] at this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    omega_arith
  · have hp0 : 0 < c.C.p := by have := hc.p_ge; omega_arith
    have hn0 : 0 < c.C.n := by have := hc.n_ge; omega_arith
    have hR : 1 < 2 ^ (64 * c.n) := Nat.one_lt_two_pow (by have := hc.n0; omega_arith)
    have hm : ∀ x, c.mont x < 2 ^ (64 * c.n) := fun x =>
      Nat.lt_trans (Nat.mod_lt (x * c.R) hp0) hc.p_lt
    have hn : ∀ x, x % c.C.n < 2 ^ (64 * c.n) := fun x => Nat.lt_trans (Nat.mod_lt x hn0) hc.n_lt
    have hp2 : c.C.p - 2 < 2 ^ (64 * c.n) := by have := hc.p_lt; omega_arith
    have hn2 : c.C.n - 2 < 2 ^ (64 * c.n) := by have := hc.n_lt; omega_arith
    simp only [Cfg.consts, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    · exact hc.p_lt
    · exact hc.n_lt
    · exact Nat.lt_trans Nat.one_pos hR
    · exact hR
    · exact hm 1
    · exact hm _
    · exact hm _
    · exact hm _
    · exact hm _
    · exact hn _
    · exact hn _
    · exact hp2
    · exact hn2
    · exact Nat.lt_trans Nat.one_pos hR
    · exact hm 1
    · exact Nat.lt_trans Nat.one_pos hR

/-! ## The whole setup -/

theorem setup_eq (c : Cfg) (A : Args) : c.setupWith A = Cfg.saveCode A.sc ++
    (loadBytes c.C.len c.n (c.sl K) A.k ++ (loadBytes c.C.len c.n (c.sl D) A.d ++
    (loadBytes c.C.len c.n (c.sl E) A.e ++ (c.shiftCode A.hs ++
    (c.consts.flatMap (fun (i, x) => VG.Impl.Mont.PPC64LE.setConst c.n (c.sl i) x) ++
    ([.li .r4 0, .subi .r4 .r4 1, .store .d .r4 wb (c.sl FLAG)] : List Instr)))))) := by
  simp only [Cfg.setupWith, List.append_assoc]

theorem allOnes_eq : BitVec.ofNat 64 0 - BitVec.ofNat 64 1 = BitVec.allOnes 64 := by decide

/-- The flag set to all ones. -/
theorem flag_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0) {o : Nat}
    (ho4 : o % 4 = 0) (ho : o + 8 ≤ size) :
    WP isa (.block [.li .r4 0, .subi .r4 .r4 1, .store .d .r4 wb o]) s fun t =>
      Kp [.r4] s t ∧ t.mem = s.mem.writeW (off base o) (BitVec.allOnes 64) := by
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step (exec_subi (by decide) (by decide)) ?_
  refine wp_step (std0_ok ((hs.write _ _).write _ _) ((h3.write _).write _) (by decide) ho4 ho)
    (WP.block_nil ⟨((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))).trans (Kp.store _ _ _), ?_⟩)
  simp only [write_mem, write_gpr, ite_true, allOnes_eq]

theorem setup_ok {c : Cfg} (hc : CfgOk c) {A : Args} {s : State} (hp : SetupPre c A s) :
    WP isa (.block (c.setupWith A)) s (SetupPost c A s (s.gpr A.sc)) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hsz : size = 8192 := rfl
  have hfit := hp.sc_fit
  have hk4 := hp.k_reg
  have hd4 := hp.d_reg
  have he4 := hp.e_reg
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk4 hd4 he4
  rw [setup_eq]
  -- The saves.
  refine wp_append (WP.mono (saveCode_ok hp.sc_reg rfl hp.wr hfit) fun s₁ ⟨w₁, K₁, r14₁, m₁⟩ => ?_)
  have hn := w₁.nowrap
  obtain ⟨O₁, sv₀, sv₈, sv₁₆⟩ := saves_mem s.mem (s.gpr A.sc) hn (s.gpr .r14) (s.gpr .r31) s.lr
  rw [← m₁] at O₁ sv₀ sv₈ sv₁₆
  have O₁' : Outside (s.gpr A.sc) 0 4096 s.mem s₁.mem := O₁.mono (Nat.le_refl _) (by omega_arith)
  -- `k`
  refine wp_append (WP.mono (setupLoad_ok hc (s := s) w₁ (i := K) (by decide)
    (by simp [hk4.1, hk4.2.2.1, hk4.2.2.2.1]) (K₁.gpr _ (by simp [hk4.1, hk4.2.1, hk4.2.2.2.2])) hp.k_fit
    (by rw [K₁.rd, K₁.wr]; exact hp.k_in) hp.k_sc O₁') fun s₂ ⟨e₂, k₂, O₂⟩ => ?_)
  have w₂ := w₁.of_kp k₂
  have K₂ : Kp [.r0, .r3, .r14, .r8, .r9] s s₂ := (K₁.mono (by decide)).trans (k₂.mono (by decide))
  have O₂' : Outside (s.gpr A.sc) 0 4096 s.mem s₂.mem :=
    O₁'.trans (O₂.mono (Nat.zero_le _) (by have := sl_le c h7 (i := K) (by decide); omega_arith))
  -- `d`
  refine wp_append (WP.mono (setupLoad_ok hc (s := s) w₂ (i := D) (by decide)
    (by simp [hd4.1, hd4.2.2.1, hd4.2.2.2.1]) (K₂.gpr _ (by simp [hd4.1, hd4.2.1, hd4.2.2.1, hd4.2.2.2.1, hd4.2.2.2.2]))
    hp.d_fit (by rw [K₂.rd, K₂.wr]; exact hp.d_in) hp.d_sc O₂') fun s₃ ⟨e₃, k₃, O₃⟩ => ?_)
  have w₃ := w₂.of_kp k₃
  have K₃ : Kp [.r0, .r3, .r14, .r8, .r9] s s₃ := K₂.trans (k₃.mono (by decide))
  have O₃' : Outside (s.gpr A.sc) 0 4096 s.mem s₃.mem :=
    O₂'.trans (O₃.mono (Nat.zero_le _) (by have := sl_le c h7 (i := D) (by decide); omega_arith))
  -- the hash
  refine wp_append (WP.mono (setupLoad_ok hc (s := s) w₃ (i := E) (by decide)
    (by simp [he4.1, he4.2.2.1, he4.2.2.2.1]) (K₃.gpr _ (by simp [he4.1, he4.2.1, he4.2.2.1, he4.2.2.2.1, he4.2.2.2.2]))
    hp.e_fit (by rw [K₃.rd, K₃.wr]; exact hp.e_in) hp.e_sc O₃') fun s₄ ⟨e₄, k₄, O₄⟩ => ?_)
  have w₄ := w₃.of_kp k₄
  -- the shift
  refine wp_append (WP.mono (setupShift_ok hc hp.shift w₄) fun sS ⟨fK, fD, fE, kS, OS⟩ => ?_)
  have wS := w₄.of_kp kS
  -- the constants
  refine wp_append (WP.mono (setupConsts_ok hc c.consts wS (fun ix h =>
    ⟨Nat.lt_trans (consts_bounds hc ix h).1 (by decide), (consts_bounds hc ix h).2⟩) (consts_nodup c)) fun s₇ ⟨e₇, k₇, U₇⟩ => ?_)
  have w₇ := wS.of_kp k₇
  have hsl0 : c.sl 0 = 64 := by rw [sl_eq]; omega_arith
  have O₇ : Outside (s.gpr A.sc) (c.sl 0) (8 * c.n * 17) sS.mem s₇.mem := U₇.outside fun w hw => by
    obtain ⟨ix, hix, rfl⟩ := List.mem_map.mp hw
    have := sl_lt c (consts_bounds hc ix hix).1
    have : c.sl 0 ≤ c.sl ix.1 := by rw [hsl0, sl_eq]; omega_arith
    exact ⟨this, by rw [sl_eq c 17] at *; omega_arith⟩
  -- the flag
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine WP.mono (flag_ok w₇.ws w₇.at3 (sl_al c FLAG) (by omega_arith)) fun s' ⟨K', m'⟩ => ?_
  have O' : Outside (s.gpr A.sc) (c.sl FLAG) 8 s₇.mem s'.mem := by
    rw [m']; exact writeW_outside _ _ _ (by omega_arith)
  -- Everything after the saves writes only in `[64, 4096)`.
  have h17 := sl_le c h7 (i := 17) (by decide)
  have hK := sl_le c h7 (i := K) (by decide)
  have hD := sl_le c h7 (i := D) (by decide)
  have hE := sl_le c h7 (i := E) (by decide)
  have hK17 := sl_lt c (i := 17) (j := K) (by decide)
  have hDK := sl_lt c (i := K) (j := D) (by decide)
  have hED := sl_lt c (i := D) (j := E) (by decide)
  have hFE := sl_lt c (i := E) (j := FLAG) (by decide)
  have h0' : c.sl 0 + 8 * c.n * 17 = c.sl 17 := by rw [sl_eq, sl_eq]; omega_arith
  have Ol : Outside (s.gpr A.sc) 64 (4096 - 64) s₁.mem s'.mem := by
    exact (((((O₂.mono (by omega_arith) (by omega_arith)).trans (O₃.mono (by omega_arith) (by omega_arith))).trans
      (O₄.mono (by omega_arith) (by omega_arith))).trans (OS.mono (by omega_arith) (by omega_arith))).trans
      (O₇.mono (by omega_arith) (by omega_arith))).trans (O'.mono (by omega_arith) (by omega_arith))
  have K'' : Kp setupClob s s' := ((((K₃.mono (by decide)).trans (k₄.mono (by decide))).trans (kS.mono (by decide))).trans
    (k₇.mono (by decide))).trans (K'.mono (by decide))
  refine ⟨w₇.of_kp K', K'', (O₁'.trans (Ol.mono (Nat.zero_le _) (by omega_arith))).unch, fun rd hrd => ?_, ?_,
    ?_, ?_, ?_, ?_, fun ix hix => ?_, ?_⟩
  · have hlt := saved_lt rd hrd
    rw [Ol.word (d := rd.2) (by omega_arith) (by omega_arith)]
    simp only [Cfg.saved, List.mem_cons, List.not_mem_nil, or_false] at hrd
    rcases hrd with rfl | rfl
    · exact sv₀
    · exact sv₈
  · rw [Ol.word (d := Cfg.lrAt) (by simp only [Cfg.lrAt]; omega_arith) (by simp only [Cfg.lrAt]; omega_arith)]; exact sv₁₆
  · rw [K'.g, k₇.g, kS.g, k₄.g, k₃.g, k₂.g, r14₁]
  · show wordsVal s'.mem _ _ _ = _
    rw [O'.wordsVal (by omega_arith) (by omega_arith), O₇.wordsVal (by omega_arith) (by omega_arith), fK,
      O₄.wordsVal (by omega_arith) (by omega_arith), O₃.wordsVal (by omega_arith) (by omega_arith), e₂]
  · show wordsVal s'.mem _ _ _ = _
    rw [O'.wordsVal (by omega_arith) (by omega_arith), O₇.wordsVal (by omega_arith) (by omega_arith), fD,
      O₄.wordsVal (by omega_arith) (by omega_arith), e₃]
  · show wordsVal s'.mem _ _ _ = _
    rw [O'.wordsVal (by omega_arith) (by omega_arith), O₇.wordsVal (by omega_arith) (by omega_arith), fE, e₄]
  · have := sl_lt c (consts_bounds hc ix hix).1
    have := sl_lt c (i := ix.1) (j := FLAG) (by have := (consts_bounds hc ix hix).1; show ix.1 < 44; omega_arith)
    have := sl_le c h7 (i := ix.1) (by have := (consts_bounds hc ix hix).1; omega_arith)
    show wordsVal s'.mem _ _ _ = _
    rw [O'.wordsVal (by omega_arith) (by omega_arith), e₇ ix hix]
  · rw [flagW, m', word_writeW_self]

end VG.Proof.Ecdsa.PPC64LE
