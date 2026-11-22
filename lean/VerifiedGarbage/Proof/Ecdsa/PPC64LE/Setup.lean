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
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith

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
  obtain hs : Ws s base size := ⟨⟨size, Nat.le_refl _, hw, hfit⟩, by decide⟩
  obtain ha : At s base sc 0 := by rw [At, hb, off]; exact (BitVec.add_zero _).symm
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
  obtain O₁ := writeW_outside m base (d := 0) a (by omega_arith)
  obtain O₂ := writeW_outside (m.writeW (off base 0) a) base (d := 8) b (by omega_arith)
  obtain O₃ := writeW_outside ((m.writeW (off base 0) a).writeW (off base 8) b) base (d := 16) c (by omega_arith)
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
  obtain hl := sl_le c hc.n10 hi
  have := hc.len_hi
  have := hc.len8
  have := hc.len_lo
  obtain hsub : Region.Sub ⟨base + BitVec.ofNat 64 (c.sl i), 8 * c.n⟩ ⟨base, size⟩ :=
    Offset.sub_base base (by omega_arith)
  refine WP.mono (loadBytes_ok hw.ws hw.at3 hsrc.1 hsrc.2.1 hsrc.2.2 (by omega_arith) (sl_al c i) (by omega_arith)
    (by omega_arith) hc.len_hi (by omega_arith) (by rw [hp]; exact hin) (by rw [hp]; exact hd.sub_right hsub))
    fun t' ⟨e, k, O⟩ => ⟨?_, k, O⟩
  obtain hd' := hd.sub_right (Region.sub_prefix (base := base) (show 4096 ≤ size by decide))
  obtain hb : Spec.Ecdsa.bytesAt t.mem p c.C.len = Spec.Ecdsa.bytesAt s.mem p c.C.len :=
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
  obtain hKl := sl_le c h7 (i := K) (by decide)
  obtain hEl := sl_le c h7 (i := E) (by decide)
  obtain hKD : c.sl D = c.sl K + 8 * c.n := by rw [sl_eq, sl_eq]; simp only [D, K]; omega_arith
  obtain hKE : c.sl E = c.sl K + 16 * c.n := by rw [sl_eq, sl_eq]; simp only [E, K]; omega_arith
  obtain nil : WP isa (.block ([] : List Instr)) t fun t' =>
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

/-! ## A table of constants copied into the working space -/

/-- What `copyTbl` may change: the table's address, the counter, its index
and the word in flight. -/
abbrev copyClob : List Reg := [.r4, .r8, .r9, .r11, .r31]

/-- `copyTbl`'s loop invariant, at `r31 = i`: the words from `i` up are
copied, `r4` holds the table's address, and only the copy's range changed. -/
structure CInv (base : Addr) (size : Nat) (sym : String) (tbl : List (BitVec 64)) (dst : Nat)
    (s₀ s : State) (i : Nat) : Prop where
  frame : Ws s base size
  r3 : At s base .r3 0
  r31 : s.gpr .r31 = BitVec.ofNat 64 i
  r4 : s.gpr .r4 = s₀.syms sym
  syms : s.syms = s₀.syms
  keep : Kp copyClob s₀ s
  mem : Outside base dst (8 * tbl.length) s₀.mem s.mem
  done : ∀ t, i ≤ t → t < tbl.length → word s.mem base (dst + 8 * t) = tbl.getD t 0

/-- `copyTbl sym (ws.length) dst`: word `i` of the working space's range at
`dst` is word `i` of the table `ws` at `sym`, which the code may read and
which the copy does not overwrite (`hv`, of any memory that agrees with this
one outside the range); nothing else changes but `copyClob`. -/
theorem copyTbl_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0)
    {sym : String} {ws : List (BitVec 64)} {dst : Nat} (hk : 0 < ws.length) (hk' : ws.length < 2 ^ 12)
    (hdst : dst + 8 * ws.length ≤ size) (hal : dst % 8 = 0)
    (hrd : ∀ i < ws.length, InRegions (s.rd ++ s.wr) (s.syms sym + BitVec.ofNat 64 (8 * i)) 8)
    (hv : ∀ m : Mem, Outside base dst (8 * ws.length) s.mem m →
      ∀ i < ws.length, m.readW (s.syms sym + BitVec.ofNat 64 (8 * i)) 64 = ws.getD i 0) :
    WP isa (copyTbl sym ws.length dst) s fun s' =>
      (∀ i < ws.length, word s'.mem base (dst + 8 * i) = ws.getD i 0) ∧ Kp copyClob s s' ∧
        Outside base dst (8 * ws.length) s.mem s'.mem := by
  have hs15 := hs.small
  have hn := hs.nowrap
  unfold copyTbl
  -- The table's address, with the link register kept in `r11` around it.
  refine WP.seq (wp_step exec_mflr (wp_step (exec_adrSym (d := .r4) (by decide))
    (wp_step exec_mtlr (wp_step (exec_li (by omega_arith)) (WP.block_nil ?_)))))
  generalize hs₁ : ({ ((s.write .r11 s.lr).write .r4 ((s.write .r11 s.lr).syms sym)) with lr := (s.write .r11 s.lr).unknowns 0, unknowns := fun n => (s.write .r11 s.lr).unknowns (n + 1) } : State) = s₁
  obtain K₁ : Kp copyClob s { s₁ with lr := s₁.gpr .r11 } := by
    rw [← hs₁]
    exact ⟨fun r hr => by
        simp only [write_gpr, ne_of_not_mem hr (x := .r4), ne_of_not_mem hr (x := .r11), ite_false], rfl, rfl, rfl,
      by simp only [write_gpr, reduceCtorEq, ite_false, ite_true]⟩
  obtain g₁ : s₁.gpr .r4 = s.syms sym := by rw [← hs₁]; simp only [write_gpr, ite_true]; rfl
  obtain y₁ : s₁.syms = s.syms := by rw [← hs₁]; rfl
  obtain m₁ : s₁.mem = s.mem := by rw [← hs₁]; rfl
  generalize hs₂ : ({ s₁ with lr := s₁.gpr .r11 } : State).write .r31 (BitVec.ofNat 64 ws.length) = s₂
  obtain I₂ : CInv base size sym ws dst s s₂ ws.length := by
    rw [← hs₂]
    exact ⟨(K₁.ws hs).write _ _, (K₁.at h3).write _, by simp only [write_gpr, ite_true],
      by simp only [write_gpr, reduceCtorEq, ite_false]; exact g₁, y₁,
      K₁.trans (Kp.write _ _ (by decide)), by rw [show (_ : State).mem = s₁.mem from rfl, m₁]; exact Outside.refl _ _ _ _,
      fun t ht ht' => absurd ht' (by omega_arith)⟩
  refine countLoop_ok (Inv := fun j t => CInv base size sym ws dst s t j) (n := ws.length)
    (fun j t hb => hb.r31) (fun j t h1 h2 hb => ?_) (fun t hb => ⟨fun i hi => hb.done i (Nat.zero_le _) hi,
      hb.keep, hb.mem⟩) hk (by omega_arith) I₂
  -- One word: `r31 = i + 1`.
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega_arith⟩
  simp only [copyTblBody]
  refine wp_decCounter (j := i + 1) (by omega_arith) hb.r31 ?_
  rw [Nat.add_sub_cancel]
  refine wp_step (exec_lsl (by decide)) ?_
  refine wp_step exec_add ?_
  generalize ht₁ : (((t.write .r31 (BitVec.ofNat 64 i)).write .r8
    ((t.write .r31 (BitVec.ofNat 64 i)).gpr .r31 <<< 3)).write .r9 _) = t₁
  obtain e8 : t₁.gpr .r8 = BitVec.ofNat 64 (8 * i) := by
    rw [← ht₁]; simp only [write_gpr, reduceCtorEq, ite_false, ite_true]; exact shl3 i
  obtain e9 : t₁.gpr .r9 = s.syms sym + BitVec.ofNat 64 (8 * i) := by
    rw [← ht₁]; simp only [write_gpr, reduceCtorEq, ite_false, ite_true]; rw [hb.r4, shl3 i]
  obtain k₁ : Kp copyClob t t₁ := by
    rw [← ht₁]
    exact ((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))
  obtain tm₁ : t₁.mem = t.mem := by rw [← ht₁]; rfl
  have hi : i < ws.length := by omega_arith
  obtain hrd₁ : InRegions (t₁.rd ++ t₁.wr) (t₁.gpr .r9 + BitVec.ofNat 64 0) 8 := by
    rw [e9, BitVec.add_zero, k₁.rd, k₁.wr, hb.keep.rd, hb.keep.wr]; exact hrd i hi
  refine wp_step (exec_ld (off := 0) (by decide) hrd₁) ?_
  refine wp_step exec_add ?_
  generalize ht₂ : ((t₁.write .r11 (t₁.mem.readW (t₁.gpr .r9 + BitVec.ofNat 64 0) 64)).write .r9
    ((t₁.write .r11 (t₁.mem.readW (t₁.gpr .r9 + BitVec.ofNat 64 0) 64)).gpr .r3 +
      (t₁.write .r11 (t₁.mem.readW (t₁.gpr .r9 + BitVec.ofNat 64 0) 64)).gpr .r8)) = t₂
  obtain k₂ : Kp copyClob t₁ t₂ := by
    rw [← ht₂]; exact (Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))
  obtain a₂ : At t₂ base .r9 (8 * i) := by
    rw [← ht₂]; simp only [At, write_gpr, reduceCtorEq, ite_false, ite_true]
    rw [(k₁.at hb.r3 : At t₁ base .r3 0), e8, off_add, Nat.zero_add]
  obtain v₂ : t₂.gpr .r11 = ws.getD i 0 := by
    rw [← ht₂]; simp only [write_gpr, reduceCtorEq, ite_false, ite_true]
    rw [e9, BitVec.add_zero, tm₁]; exact hv _ hb.mem i hi
  obtain w₂ : Ws t₂ base size := k₂.ws (k₁.ws hb.frame)
  refine wp_step (std_ok w₂ a₂ (by decide) (by omega_arith) (by omega_arith)) (WP.block_nil ?_)
  obtain tm₂ : t₂.mem = t.mem := by rw [← ht₂, ← tm₁]; rfl
  obtain O : Outside base (8 * i + dst) 8 t₂.mem (t₂.mem.writeW (off base (8 * i + dst)) (t₂.gpr .r11)) :=
    writeW_outside _ _ _ (by omega_arith)
  obtain c₂ : t₂.gpr .r31 = BitVec.ofNat 64 i := by
    rw [← ht₂, ← ht₁]; simp only [write_gpr, reduceCtorEq, ite_false, ite_true]
  obtain g₂ : t₂.gpr .r4 = s.syms sym := by
    rw [← ht₂, ← ht₁]; simp only [write_gpr, reduceCtorEq, ite_false]; exact hb.r4
  obtain y₂ : t₂.syms = s.syms := by rw [← ht₂, ← ht₁]; exact hb.syms
  refine ⟨w₂.store _, (k₂.at (k₁.at hb.r3)).store _, c₂, g₂, y₂,
    ((hb.keep.trans k₁).trans k₂).trans (Kp.store _ _ _),
    hb.mem.trans (by rw [← tm₂]; exact O.mono (by omega_arith) (by omega_arith)), fun t' ht' ht'' => ?_⟩
  show word (t₂.mem.writeW (off base (8 * i + dst)) (t₂.gpr .r11)) base (dst + 8 * t') = _
  rcases Nat.lt_or_ge i t' with h | h
  · rw [word_writeW_ne _ (by omega_arith) (by omega_arith) (by omega_arith), tm₂]
    exact hb.done t' (by omega_arith) ht''
  · obtain rfl : t' = i := by omega_arith
    rw [show dst + 8 * t' = 8 * t' + dst by omega_arith, word_writeW_self, v₂]

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
    obtain hi := hb (i, x) List.mem_cons_self
    obtain hl := sl_le c hc.n10 (i := i) hi.1
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
    obtain hn0 : 0 < c.C.n := by have := hc.n_ge; omega_arith
    obtain hR : 1 < 2 ^ (64 * c.n) := Nat.one_lt_two_pow (by have := hc.n0; omega_arith)
    obtain hm : ∀ x, c.mont x < 2 ^ (64 * c.n) := fun x =>
      Nat.lt_trans (Nat.mod_lt (x * c.R) hp0) hc.p_lt
    obtain hn : ∀ x, x % c.C.n < 2 ^ (64 * c.n) := fun x => Nat.lt_trans (Nat.mod_lt x hn0) hc.n_lt
    obtain hp2 : c.C.p - 2 < 2 ^ (64 * c.n) := by have := hc.p_lt; omega_arith
    obtain hn2 : c.C.n - 2 < 2 ^ (64 * c.n) := by have := hc.n_lt; omega_arith
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

theorem constTbl_length (c : Cfg) : c.constTbl.length = 17 * c.n := by
  simp only [Cfg.constTbl, List.length_map, List.length_range]

theorem constTbl_getD (c : Cfg) {k : Nat} (hk : k < 17 * c.n) :
    c.constTbl.getD k 0 = BitVec.ofNat 64 (c.slotVal (k / c.n) >>> (64 * (k % c.n))) := by
  simp only [Cfg.constTbl, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
    Option.map_some, Option.getD_some]

/-- `consts` gives each of its slots its value. -/
theorem slotVal_of_mem (c : Cfg) : ∀ ix ∈ c.consts, c.slotVal ix.1 = ix.2 := by
  intro ix h
  simp only [Cfg.consts, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The words the table gives the slot `i` are its value, `x < 2^(64 n)`. -/
theorem wordsVal_of_tbl {c : Cfg} {m : Mem} {base : Addr} {i x : Nat} (hi : i < 17) (hx : c.slotVal i = x)
    (hxl : x < 2 ^ (64 * c.n))
    (h : ∀ k < 17 * c.n, word m base (c.sl 0 + 8 * k) = c.constTbl.getD k 0) :
    wordsVal m base (c.sl i) c.n = x := by
  refine wordsVal_of_shifts m base _ _ _ hxl fun j hj => ?_
  have h0 : 0 < c.n := by omega_arith
  have hk : c.n * i + j < 17 * c.n := by
    have := Nat.mul_le_mul_left c.n (show i ≤ 16 by omega_arith); omega_arith
  rw [show c.sl i + 8 * j = c.sl 0 + 8 * (c.n * i + j) by
      rw [sl_eq, sl_eq, Nat.mul_zero, Nat.add_zero, Nat.mul_assoc, Nat.mul_add]; omega_arith, h _ hk, constTbl_getD c hk,
    show (c.n * i + j) / c.n = i by rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ h0, Nat.div_eq_of_lt hj,
      Nat.zero_add],
    show (c.n * i + j) % c.n = j by rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj], hx]

/-- The table of constants, under a contract that lists it
(`Abi.withConsts`, `ConstsOk`), as `SetupPre` takes it: readable word by word,
and apart from a working space at `sc`, so that its words survive the
setup's writes there. -/
theorem tbl_of_consts {c : Cfg} {K : List (String × List (BitVec 64))} {st : Nat} {s : State} {sc : Addr}
    (hk : ConstsOk K st s) (hc : (c.constSym, c.constTbl) ∈ K)
    (hd : Region.Disjoint ⟨s.syms c.constSym, 8 * c.constTbl.length⟩ ⟨sc, size⟩) : TblOk c sc s := by
  obtain hL := constTbl_length c
  obtain hfit := hk.fit hc
  refine ⟨fun i hi => hk.inRegions hc (by rw [hL]; omega_arith) (by decide) s.wr, fun m hm i hi => ?_⟩
  rw [← hk.readW hc (by rw [hL]; exact hi)]
  refine Mem.readW_congr fun j hj => hm _ (Or.inr ?_)
  -- The byte is in the table, so not in the working space.
  obtain hin : ((s.syms c.constSym + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j) - s.syms c.constSym).toNat + 1 ≤
      8 * c.constTbl.length := by
    rw [VG.Offset.add_add, VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by rw [hL] at hfit; omega_using [hfit, hi, hj])]
    rw [hL]; omega_using [hi, hj]
  obtain hn := hd _ hin
  simp only [Region.Contains, Nat.not_le] at hn
  simp only [ofs]
  have : size = 8192 := rfl
  omega_using [hn, this]

theorem setup_eq (c : Cfg) (A : Args) : c.setupWith A = .seq (.block (Cfg.saveCode A.sc ++
    (loadBytes c.C.len c.n (c.sl K) A.k ++ (loadBytes c.C.len c.n (c.sl D) A.d ++
    (loadBytes c.C.len c.n (c.sl E) A.e ++ c.shiftCode A.hs)))))
    (.seq (copyTbl c.constSym c.constTbl.length (c.sl 0))
      (.block [.li .r4 0, .subi .r4 .r4 1, .store .d .r4 wb (c.sl FLAG)])) := by
  simp only [Cfg.setupWith, List.append_assoc, constTbl_length]

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
    WP isa (c.setupWith A) s (SetupPost c A s (s.gpr A.sc)) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hsz : size = 8192 := rfl
  have hfit := hp.sc_fit
  have hk4 := hp.k_reg
  have hd4 := hp.d_reg
  have he4 := hp.e_reg
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk4 hd4 he4
  rw [setup_eq]
  refine WP.seq (WP.mono_syms (Q := fun t => t.syms = s.syms → _) ?_ fun t h hy => h hy)
  -- The saves.
  refine wp_append (WP.mono (saveCode_ok hp.sc_reg rfl hp.wr hfit) fun s₁ ⟨w₁, K₁, r14₁, m₁⟩ => ?_)
  have hn := w₁.nowrap
  obtain ⟨O₁, sv₀, sv₈, sv₁₆⟩ := saves_mem s.mem (s.gpr A.sc) hn (s.gpr .r14) (s.gpr .r31) s.lr
  rw [← m₁] at O₁ sv₀ sv₈ sv₁₆
  obtain O₁' : Outside (s.gpr A.sc) 0 4096 s.mem s₁.mem := O₁.mono (Nat.le_refl _) (by omega_arith)
  -- `k`
  refine wp_append (WP.mono (setupLoad_ok hc (s := s) w₁ (i := K) (by decide)
    (by simp [hk4.1, hk4.2.2.1, hk4.2.2.2.1]) (K₁.gpr _ (by simp [hk4.1, hk4.2.1, hk4.2.2.2.2])) hp.k_fit
    (by rw [K₁.rd, K₁.wr]; exact hp.k_in) hp.k_sc O₁') fun s₂ ⟨e₂, k₂, O₂⟩ => ?_)
  obtain w₂ := w₁.of_kp k₂
  obtain K₂ : Kp [.r0, .r3, .r14, .r8, .r9] s s₂ := (K₁.mono (by decide)).trans (k₂.mono (by decide))
  obtain O₂' : Outside (s.gpr A.sc) 0 4096 s.mem s₂.mem :=
    O₁'.trans (O₂.mono (Nat.zero_le _) (by have := sl_le c h7 (i := K) (by decide); omega_arith))
  -- `d`
  refine wp_append (WP.mono (setupLoad_ok hc (s := s) w₂ (i := D) (by decide)
    (by simp [hd4.1, hd4.2.2.1, hd4.2.2.2.1]) (K₂.gpr _ (by simp [hd4.1, hd4.2.1, hd4.2.2.1, hd4.2.2.2.1, hd4.2.2.2.2]))
    hp.d_fit (by rw [K₂.rd, K₂.wr]; exact hp.d_in) hp.d_sc O₂') fun s₃ ⟨e₃, k₃, O₃⟩ => ?_)
  obtain w₃ := w₂.of_kp k₃
  obtain K₃ : Kp [.r0, .r3, .r14, .r8, .r9] s s₃ := K₂.trans (k₃.mono (by decide))
  obtain O₃' : Outside (s.gpr A.sc) 0 4096 s.mem s₃.mem :=
    O₂'.trans (O₃.mono (Nat.zero_le _) (by have := sl_le c h7 (i := D) (by decide); omega_arith))
  -- the hash
  refine wp_append (WP.mono (setupLoad_ok hc (s := s) w₃ (i := E) (by decide)
    (by simp [he4.1, he4.2.2.1, he4.2.2.2.1]) (K₃.gpr _ (by simp [he4.1, he4.2.1, he4.2.2.1, he4.2.2.2.1, he4.2.2.2.2]))
    hp.e_fit (by rw [K₃.rd, K₃.wr]; exact hp.e_in) hp.e_sc O₃') fun s₄ ⟨e₄, k₄, O₄⟩ => ?_)
  obtain w₄ := w₃.of_kp k₄
  -- the shift
  refine WP.mono (setupShift_ok hc hp.shift w₄) fun sS ⟨fK, fD, fE, kS, OS⟩ hyS => ?_
  obtain wS := w₄.of_kp kS
  -- the constants, from their table
  obtain hsl0 : c.sl 0 = 64 := by rw [sl_eq]; omega_arith
  obtain hL := constTbl_length c
  obtain h17 := sl_le c h7 (i := 17) (by decide)
  obtain h0' : c.sl 0 + 8 * c.n * 17 = c.sl 17 := by rw [sl_eq, sl_eq]; omega_arith
  -- What the setup wrote before the copy is in the first `4096` bytes.
  obtain OS' : Outside (s.gpr A.sc) 0 4096 s.mem sS.mem :=
    ((O₃'.trans (O₄.mono (Nat.zero_le _) (by have := sl_le c h7 (i := E) (by decide); omega_arith))).trans
      (OS.mono (Nat.zero_le _) (by
        have := sl_le c h7 (i := E) (by decide); rw [sl_eq] at this ⊢; simp only [K, E] at this ⊢; omega_arith)))
  obtain hrS : sS.rd = s.rd ∧ sS.wr = s.wr ∧ sS.syms = s.syms :=
    ⟨by rw [kS.rd, k₄.rd, K₃.rd], by rw [kS.wr, k₄.wr, K₃.wr], hyS⟩
  refine WP.seq (WP.mono (copyTbl_ok wS.ws wS.at3 (sym := c.constSym) (ws := c.constTbl) (dst := c.sl 0)
    (by rw [hL]; omega_arith) (by rw [hL]; omega_arith) (by rw [hL]; omega_arith) (by rw [hsl0])
    (fun i hi => by rw [hrS.1, hrS.2.1, hrS.2.2]; exact hp.tbl.rd i (by rw [← hL]; exact hi))
    (fun m hm i hi => by
      rw [hrS.2.2]
      exact hp.tbl.val m (OS'.trans (hm.mono (Nat.zero_le _) (by rw [hL]; omega_arith))) i (by rw [← hL]; exact hi)))
    fun s₇ ⟨e₇, k₇, O₇⟩ => ?_)
  obtain w₇ := wS.of_kp k₇
  rw [hL, show 8 * (17 * c.n) = 8 * c.n * 17 by omega_arith] at O₇
  rw [hL] at e₇
  -- the flag
  obtain hF := sl_le c h7 (i := FLAG) (by decide)
  refine WP.mono (flag_ok w₇.ws w₇.at3 (sl_al c FLAG) (by omega_arith)) fun s' ⟨K', m'⟩ => ?_
  obtain O' : Outside (s.gpr A.sc) (c.sl FLAG) 8 s₇.mem s'.mem := by
    rw [m']; exact writeW_outside _ _ _ (by omega_arith)
  -- Everything after the saves writes only in `[64, 4096)`.
  obtain h17 := sl_le c h7 (i := 17) (by decide)
  obtain hK := sl_le c h7 (i := K) (by decide)
  obtain hD := sl_le c h7 (i := D) (by decide)
  obtain hE := sl_le c h7 (i := E) (by decide)
  obtain hK17 := sl_lt c (i := 17) (j := K) (by decide)
  obtain hDK := sl_lt c (i := K) (j := D) (by decide)
  obtain hED := sl_lt c (i := D) (j := E) (by decide)
  obtain hFE := sl_lt c (i := E) (j := FLAG) (by decide)
  obtain h0' : c.sl 0 + 8 * c.n * 17 = c.sl 17 := by rw [sl_eq, sl_eq]; omega_arith
  obtain Ol : Outside (s.gpr A.sc) 64 (4096 - 64) s₁.mem s'.mem := by
    exact (((((O₂.mono (by omega_arith) (by omega_arith)).trans (O₃.mono (by omega_arith) (by omega_arith))).trans
      (O₄.mono (by omega_arith) (by omega_arith))).trans (OS.mono (by omega_arith) (by omega_arith))).trans
      (O₇.mono (by omega_arith) (by omega_arith))).trans (O'.mono (by omega_arith) (by omega_arith))
  obtain K'' : Kp setupClob s s' := ((((K₃.mono (by decide)).trans (k₄.mono (by decide))).trans (kS.mono (by decide))).trans
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
    rw [O'.wordsVal (by omega_arith) (by omega_arith)]
    exact wordsVal_of_tbl (consts_bounds hc ix hix).1 (slotVal_of_mem c ix hix) (consts_bounds hc ix hix).2 e₇
  · rw [flagW, m', word_writeW_self]

end VG.Proof.Ecdsa.PPC64LE
