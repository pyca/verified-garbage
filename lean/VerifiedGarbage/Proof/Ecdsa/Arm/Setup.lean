module

public import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Weierstrass.Arm.BytesLen
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Arm.Reduce
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Weierstrass.Arm.Loop
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Rc2.PairMem

/-!
# ECDSA on 32-bit ARM: the setup

`Cfg.setupWith A` loads the working space's base from the stack argument
into `r12` (`wp_ldrSp`), saves `r4`–`r11` and `lr` at its start (`strs_ok`),
moves `out` to `lr`, reads `k`, `d` and the hash (`len` bytes each)
big-endian into their slots from the registers `A` names (`setupLoad_ok`),
shifts the slot `A.hs` holding a hash (`setupShift_ok`), stores the constants
(`constsCode_ok`: copied from their table, `copyTbl_ok`, a loop of a slot an
iteration counted down in `r11`) and
sets the flag to all ones: `setup_ok`, the state `SetupPost` describes.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_ldr wp_str wp_dp wp_mov op2_imm op2_reg dpVal)

/-- `ldr t, [sp, #off]`. -/
theorem wp_ldrSp {s : State} {is : List Instr} {Q : State → Prop} {t : Reg} {off : Nat} (ho : off < 4096)
    (hin : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 off)) 4)
    (k : ∀ s', Upd s s' t (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrSp t off :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (by simp only [reduceExec, ho, ite_true, State.load32, hin, Option.map_some])
    (k _ (Upd.setReg _ _ _))

/-! ## Reading `k`, `d` and the hash -/

/-- The `len` bytes at `p` (readable, outside the working space, and so
unchanged since `s`) to slot `i`. -/
theorem setupLoad_ok {c : Cfg} (hc : CfgOk c) {s t : State} {base : Addr} {i : Nat} {src : Reg}
    {p : BitVec 32} (hs : Scr t base size) (hi : i < 45) (hsrc : src ≠ .r4) (hp : t.gpr src = p)
    (hfit : p.toNat + c.C.len ≤ 2 ^ 32)
    (hin : ∀ e, e + 4 ≤ c.C.len → InRegions (t.rd ++ t.wr) (State.addr p + BitVec.ofNat 64 e) 4)
    (hd : Region.Disjoint ⟨State.addr p, c.C.len⟩ ⟨base, size⟩) (ho : Outside base 0 size s.mem t.mem) :
    WP isa (.block (loadBytes c.C.len c.n (c.sl i) src)) t fun t' =>
      wordsVal t'.mem base (c.sl i) c.n = ofBytes (Spec.Ecdsa.bytesAt s.mem (State.addr p) c.C.len) ∧
      Rest [.r4] t t' ∧ Outside base (c.sl i) (8 * c.n) t.mem t'.mem := by
  obtain hl := sl_le c hc.n10 hi
  have h7 := hc.n10
  have := hc.len_hi
  have := hc.len8
  obtain hsub : Region.Sub ⟨base + BitVec.ofNat 64 (c.sl i), 8 * c.n⟩ ⟨base, size⟩ := Offset.sub_base base hl
  refine WP.mono (loadBytes_ok hs hsrc hl (by rw [hp]; exact hfit) (by omega_arith) hc.len_hi (by rw [hp]; exact hin)
    (by rw [hp]; exact hd.sub_right hsub)) fun t' ⟨e, k, O⟩ => ⟨?_, k, O⟩
  obtain hb : Spec.Ecdsa.bytesAt t.mem (State.addr p) c.C.len = Spec.Ecdsa.bytesAt s.mem (State.addr p) c.C.len :=
    List.map_congr_left fun j hj =>
      keep_of_disjoint' ho hd (by decide) (List.mem_range.mp hj) (by omega_arith)
  rw [e, hp, hb]

/-! ## The hash's shift -/

/-- The shift of slot `hs`, if any, by the bits of a hash that are not
`e`'s: only the slots of `k`, `d` and the hash change. -/
theorem setupShift_ok {c : Cfg} (hc : CfgOk c) {hs : Option Nat} (hhs : ShiftOk hs) {t : State}
    {base : Addr} (hs' : Scr t base size) :
    WP isa (.block (c.shiftCode hs)) t fun t' =>
      wordsVal t'.mem base (c.sl K) c.n = wordsVal t.mem base (c.sl K) c.n >>> shAt c hs K ∧
      wordsVal t'.mem base (c.sl D) c.n = wordsVal t.mem base (c.sl D) c.n >>> shAt c hs D ∧
      wordsVal t'.mem base (c.sl E) c.n = wordsVal t.mem base (c.sl E) c.n >>> shAt c hs E ∧
      Rest [.r4, .r5] t t' ∧ Outside base (c.sl K) (24 * c.n) t.mem t'.mem := by
  have hn := hs'.nowrap
  have h7 := hc.n10
  obtain hKl := sl_le c h7 (i := K) (by decide)
  obtain hEl := sl_le c h7 (i := E) (by decide)
  obtain hKD : c.sl D = c.sl K + 8 * c.n := by rw [sl_eq, sl_eq]; show _ = _ + 8 * c.n; simp only [D, K]; omega_arith
  obtain hKE : c.sl E = c.sl K + 16 * c.n := by rw [sl_eq, sl_eq]; show _ = _ + 16 * c.n; simp only [E, K]; omega_arith
  obtain nil : WP isa (.block ([] : List Instr)) t fun t' =>
      wordsVal t'.mem base (c.sl K) c.n = wordsVal t.mem base (c.sl K) c.n >>> 0 ∧
      wordsVal t'.mem base (c.sl D) c.n = wordsVal t.mem base (c.sl D) c.n >>> 0 ∧
      wordsVal t'.mem base (c.sl E) c.n = wordsVal t.mem base (c.sl E) c.n >>> 0 ∧
      Rest [.r4, .r5] t t' ∧ Outside base (c.sl K) (24 * c.n) t.mem t'.mem :=
    WP.block_nil ⟨Nat.shiftRight_zero.symm, Nat.shiftRight_zero.symm, Nat.shiftRight_zero.symm,
      Rest.refl _ _, VG.Proof.Mont.Outside.refl _ _ _ _⟩
  rcases hhs with rfl | rfl | rfl
  · exact nil
  · have hDl := sl_le c h7 (i := D) (by decide)
    by_cases h0 : c.sh = 0
    · simp only [Cfg.shiftCode, h0, ite_true]
      rw [shAt_self, h0, shAt_D_K, shAt_D_E]; exact nil
    · simp only [Cfg.shiftCode, h0, ite_false]
      refine WP.mono (shrWords_ok hs' hDl (by omega_arith) hc.sh) fun t' ⟨e, k, O⟩ =>
        ⟨?_, ?_, ?_, k, O.mono (by omega_arith) (by omega_arith)⟩
      · rw [shAt_D_K, Nat.shiftRight_zero]; exact O.wordsVal (by omega_arith) (by omega_arith)
      · rw [shAt_self]; exact e
      · rw [shAt_D_E, Nat.shiftRight_zero]; exact O.wordsVal (by omega_arith) (by omega_arith)
  · by_cases h0 : c.sh = 0
    · simp only [Cfg.shiftCode, h0, ite_true]
      rw [shAt_self, h0, shAt_E_D, shAt_E_K]; exact nil
    · simp only [Cfg.shiftCode, h0, ite_false]
      refine WP.mono (shrWords_ok hs' hEl (by omega_arith) hc.sh) fun t' ⟨e, k, O⟩ =>
        ⟨?_, ?_, ?_, k, O.mono (by omega_arith) (by omega_arith)⟩
      · rw [shAt_E_K, Nat.shiftRight_zero]; exact O.wordsVal (by omega_arith) (by omega_arith)
      · rw [shAt_E_D, Nat.shiftRight_zero]; exact O.wordsVal (by omega_arith) (by omega_arith)
      · rw [shAt_self]; exact e

/-! ## A table of constants copied into the working space -/

/-- What `copyTbl` may change: the pointers, the counter and the words in
flight. -/
abbrev copyClob : List Reg := [.r4, .r5, .r9, .r10, .r11]

/-- The table `ws` at `A`, as `copyTbl` reads it into `[base + dst]`: the
range fits the working space and the address space, is readable, holds its
words in `s₀` and lies apart from the working space. -/
structure TblAt (s₀ : State) (base : Addr) (sz : Nat) (A : BitVec 32) (ws : List (BitVec 64)) (dst : Nat) :
    Prop where
  dst : dst + 8 * ws.length ≤ sz
  fit : A.toNat + 8 * ws.length ≤ 2 ^ 32
  rd : InRegions (s₀.rd ++ s₀.wr) (State.addr A) (8 * ws.length)
  words : ∀ i < ws.length, s₀.mem.readW (State.addr A + BitVec.ofNat 64 (8 * i)) 64 = ws.getD i 0
  sep : Region.Disjoint ⟨State.addr A, 8 * ws.length⟩ ⟨base, sz⟩

/-- `copyTbl`'s invariant, at `r11 = i`: `r10` and `r9` are `P` bytes into the
table and the working space, the words below `w` are copied, and only the
copy's range changed. -/
structure CInv (base : Addr) (sz : Nat) (A : BitVec 32) (ws : List (BitVec 64)) (dst : Nat)
    (s₀ s : State) (i P w : Nat) : Prop where
  scr : Scr s base sz
  r11 : s.gpr .r11 = BitVec.ofNat 32 i
  r10 : s.gpr .r10 = A + BitVec.ofNat 32 P
  r9 : s.gpr .r9 = s.gpr .r12 + BitVec.ofNat 32 P
  keep : Rest copyClob s₀ s
  mem : Outside base dst (8 * ws.length) s₀.mem s.mem
  done : ∀ t < w, word s.mem base (dst + 8 * t) = ws.getD t 0

/-- The invariant across an update that keeps `copyClob`'s other registers
and the memory. -/
theorem CInv.upd {base : Addr} {sz : Nat} {A : BitVec 32} {ws : List (BitVec 64)} {dst : Nat} {s₀ t t' : State}
    {i i' P P' w : Nat} (hI : CInv base sz A ws dst s₀ t i P w) (k : Rest copyClob t t') (hm : t'.mem = t.mem)
    (h11 : t'.gpr .r11 = BitVec.ofNat 32 i') (h10 : t'.gpr .r10 = A + BitVec.ofNat 32 P')
    (h9 : t'.gpr .r9 = t'.gpr .r12 + BitVec.ofNat 32 P') : CInv base sz A ws dst s₀ t' i' P' w :=
  ⟨hI.scr.of_rest k (by decide), h11, h10, h9, hI.keep.trans k, hm ▸ hI.mem, fun t ht => hm ▸ hI.done t ht⟩

/-- Word `j` of a slot (`copyWord`), word `w` of the table, with the pointers
`P = 8 (w - j)` bytes in: its two halves to `[base + dst + 8 w]`. -/
theorem copyWord_ok {s₀ t : State} {base : Addr} {sz : Nat} {A : BitVec 32} {ws : List (BitVec 64)}
    {dst i P w j : Nat} (hT : TblAt s₀ base sz A ws dst) (hI : CInv base sz A ws dst s₀ t i P w)
    (hw : w < ws.length) (hP : P + 8 * j = 8 * w) :
    WP isa (.block (copyWord dst j)) t fun t' => CInv base sz A ws dst s₀ t' i P (w + 1) := by
  have hn := hI.scr.nowrap
  have hsm := hI.scr.small
  have hdst := hT.dst
  have hfit := hT.fit
  simp only [copyWord]
  -- The table's word `w`, which the copy so far left as it was.
  obtain hv : t.mem.readW (State.addr A + BitVec.ofNat 64 (8 * w)) 64 = ws.getD w 0 := by
    rw [← hT.words w hw]
    exact readW_keep fun j hj => keep_of_disjoint' (hI.mem.mono (o' := 0) (n' := sz) (Nat.zero_le _)
      (by omega_arith)) hT.sep (by omega_arith) (by omega_arith) (by omega_arith)
  obtain ad0 : State.addr (t.gpr .r10 + BitVec.ofNat 32 (8 * j)) = State.addr A + BitVec.ofNat 64 (8 * w) := by
    rw [hI.r10, Offset.add_add, hP]; exact addr_add (by omega_arith)
  obtain rw₀ : t.rd ++ t.wr = s₀.rd ++ s₀.wr := by rw [hI.keep.rd, hI.keep.wr]
  obtain hl64 : 8 * ws.length < 2 ^ 64 := by omega_arith
  obtain hin0 : InRegions (s₀.rd ++ s₀.wr) (State.addr A + BitVec.ofNat 64 (8 * w)) 4 :=
    CallLay.inRegions_sub (off := 8 * w) (l := 4) hT.rd (by omega_arith) hl64
  obtain hin4 : InRegions (s₀.rd ++ s₀.wr) (State.addr A + BitVec.ofNat 64 (8 * w + 4)) 4 :=
    CallLay.inRegions_sub (off := 8 * w + 4) (l := 4) hT.rd (by omega_arith) hl64
  refine wp_ldr (by omega_arith) ad0 (by rw [rw₀]; exact hin0) fun t₃ u₃ => ?_
  refine wp_ldr (a := State.addr A + BitVec.ofNat 64 (8 * w) + BitVec.ofNat 64 4) (by omega_arith)
    (by rw [u₃.other _ (by decide), hI.r10, Offset.add_add, Offset.add_add,
          show P + (8 * j + 4) = 8 * w + 4 by omega_arith]; exact addr_add (by omega_arith))
    (by rw [u₃.rd, u₃.wr, rw₀, Offset.add_add]; exact hin4) fun t₄ u₄ => ?_
  obtain k₄ : Rest copyClob t t₄ := (u₃.rest (by simp)).trans (u₄.rest (by simp))
  obtain hs₄ := hI.scr.of_rest k₄ (by decide)
  obtain a₄ : t₄.gpr .r9 = t₄.gpr .r12 + BitVec.ofNat 32 P := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide)]
    exact hI.r9
  obtain v4 : t₄.gpr .r4 = t.mem.readW (State.addr A + BitVec.ofNat 64 (8 * w)) 32 := by
    rw [u₄.other _ (by decide), u₃.gpr]
  obtain v5 : t₄.gpr .r5 = t.mem.readW (State.addr A + BitVec.ofNat 64 (8 * w) + BitVec.ofNat 64 4) 32 := by
    rw [u₄.gpr, u₃.mem]
  obtain m₄ : t₄.mem = t.mem := by rw [u₄.mem, u₃.mem]
  refine wp_str (by omega_arith)
    (by rw [hs₄.ea_off a₄ (d := dst + 8 * j) (by omega_arith), show P + (dst + 8 * j) = 8 * w + dst by omega_arith])
    (hs₄.write (d := 8 * w + dst) (n := 4) (by omega_arith)) fun t₆ m₆ => ?_
  obtain hs₆ := hs₄.of_rest (m₆.rest []) (by decide)
  obtain a₆ : t₆.gpr .r9 = t₆.gpr .r12 + BitVec.ofNat 32 P := by rw [m₆.gpr]; exact a₄
  refine wp_str (by omega_arith)
    (by rw [hs₆.ea_off a₆ (d := dst + 8 * j + 4) (by omega_arith),
          show P + (dst + 8 * j + 4) = 8 * w + (dst + 4) by omega_arith])
    (hs₆.write (d := 8 * w + (dst + 4)) (n := 4) (by omega_arith)) fun t₇ m₇ => WP.block_nil ?_
  obtain M₇ : t₇.mem = (t.mem.writeW (off base (8 * w + dst)) (t.mem.readW (State.addr A + BitVec.ofNat 64 (8 * w)) 32)).writeW
      (off base (8 * w + (dst + 4))) (t.mem.readW (State.addr A + BitVec.ofNat 64 (8 * w) + BitVec.ofNat 64 4) 32) := by
    rw [m₇.mem, m₆.gpr, m₆.mem, m₄, v4, v5]
  obtain k₇ : Rest copyClob t t₇ := k₄.trans ((m₆.rest _).trans (m₇.rest _))
  obtain O₇ : Outside base (8 * w + dst) 8 t.mem t₇.mem := by
    rw [M₇]
    exact ((writeW32_outside _ _ (d := 8 * w + dst) _ (by omega_arith)).mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW32_outside _ _ (d := 8 * w + (dst + 4)) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  refine ⟨hI.scr.of_rest k₇ (by decide), ?_, ?_, ?_, hI.keep.trans k₇,
    hI.mem.trans (O₇.mono (by omega_arith) (by omega_arith)), fun t' h1 => ?_⟩
  · rw [m₇.gpr, m₆.gpr, u₄.other _ (by decide), u₃.other _ (by decide)]; exact hI.r11
  · rw [m₇.gpr, m₆.gpr, u₄.other _ (by decide), u₃.other _ (by decide)]; exact hI.r10
  · rw [m₇.gpr]; exact a₆
  rcases Nat.lt_or_ge t' w with h | h
  · rw [O₇.word (by omega_arith) (by omega_arith)]; exact hI.done t' h
  · rw [show t' = w by omega_arith]
    obtain hhi : t₇.mem.readW (off base (8 * w + dst) + BitVec.ofNat 64 4) 32 =
        t.mem.readW (State.addr A + BitVec.ofNat 64 (8 * w) + BitVec.ofNat 64 4) 32 := by
      rw [Offset.add_add (p := base), M₇, show 8 * w + dst + 4 = 8 * w + (dst + 4) by omega_arith,
        Mem.readW_writeW_self32]
    obtain hlo : t₇.mem.readW (off base (8 * w + dst)) 32 = t.mem.readW (State.addr A + BitVec.ofNat 64 (8 * w)) 32 := by
      apply BitVec.eq_of_toNat_eq
      show w32 t₇.mem base (8 * w + dst) = _
      rw [M₇, w32_write_ne (size := sz) hn (by omega_arith) (by omega_arith) (by omega_arith), w32_write_self]
    show t₇.mem.readW (off base (dst + 8 * w)) 64 = _
    rw [show dst + 8 * w = 8 * w + dst from Nat.add_comm _ _, Rc2.Word32.read64_pair t₇.mem, hhi, hlo,
      ← Rc2.Word32.read64_pair, hv]

/-- A slot's first `m` words (`copyWord`), from word `w₀` of the table, with
the pointers at it. -/
theorem copyWords_ok {s₀ : State} {base : Addr} {sz : Nat} {A : BitVec 32} {ws : List (BitVec 64)}
    {dst i w₀ : Nat} (hT : TblAt s₀ base sz A ws dst) :
    ∀ (m : Nat) {t : State}, CInv base sz A ws dst s₀ t i (8 * w₀) w₀ → w₀ + m ≤ ws.length →
      WP isa (.block ((List.range m).flatMap (copyWord dst))) t fun t' =>
        CInv base sz A ws dst s₀ t' i (8 * w₀) (w₀ + m)
  | 0, _, hI, _ => WP.block_nil hI
  | m + 1, _, hI, hm => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [← Nat.add_assoc]
    exact VG.Proof.X25519.Arm.WP.append (copyWords_ok hT m hI (by omega_arith)) fun t' h =>
      copyWord_ok (w := w₀ + m) (j := m) hT h (by omega_arith) (by omega_arith)

/-- One slot of `copyTbl`'s loop (`copyTblBody`), at `r11 = i + 1`, with the
pointers at word `w`: its `n` words, the pointers on by `8 n`, and `Z` iff
`i = 0`. -/
theorem copyTblBody_ok {s₀ t : State} {base : Addr} {sz : Nat} {A : BitVec 32} {ws : List (BitVec 64)}
    {dst i n w : Nat} (hT : TblAt s₀ base sz A ws dst) (hI : CInv base sz A ws dst s₀ t (i + 1) (8 * w) w)
    (hw : w + n ≤ ws.length) (hi : i + 1 < 2 ^ 32) (h8 : encodable (BitVec.ofNat 32 (8 * n)) = true) :
    WP isa (.block (copyTblBody n dst)) t fun t' =>
      CInv base sz A ws dst s₀ t' i (8 * (w + n)) (w + n) ∧ t'.z = decide (i = 0) := by
  simp only [copyTblBody, List.singleton_append]
  refine wp_decCounter (j := i + 1) (by omega_arith) hI.r11 fun t₁ u₁ => ?_
  obtain I₁ : CInv base sz A ws dst s₀ t₁ i (8 * w) w :=
    hI.upd (u₁.rest (by simp)) u₁.mem (by rw [u₁.gpr, Nat.add_sub_cancel])
      (by rw [u₁.other _ (by decide)]; exact hI.r10)
      (by rw [u₁.other _ (by decide), u₁.other _ (by decide)]; exact hI.r9)
  refine VG.Proof.X25519.Arm.WP.append (copyWords_ok hT n I₁ hw) fun t₂ I₂ => ?_
  refine wp_dp (op2_imm h8) fun t₃ u₃ => ?_
  refine wp_dp (op2_imm h8) fun t₄ u₄ => ?_
  obtain c₄ : t₄.gpr .r11 = BitVec.ofNat 32 i := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide)]; exact I₂.r11
  refine wp_testCounter (by omega_arith) c₄ fun t₅ f₅ z₅ => WP.block_nil ⟨?_, z₅⟩
  obtain e : 8 * w + 8 * n = 8 * (w + n) := by omega_arith
  refine I₂.upd ((u₃.rest (by simp)).trans ((u₄.rest (by simp)).trans (f₅.rest _)))
    (by rw [f₅.mem, u₄.mem, u₃.mem]) (by rw [f₅.gpr]; exact c₄) ?_ ?_
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.gpr, dpVal, I₂.r10, Offset.add_add, e]
  · rw [f₅.gpr, u₄.gpr, dpVal, u₄.other _ (by decide), u₃.other _ (by decide), I₂.r9, Offset.add_add, e,
      u₃.other _ (by decide)]

/-- `copyTbl sym n k dst`: word `i` of the working space's range at `dst` is
word `i` of the table `ws` of `k` slots of `n` words at `sym`, which the code
may read and which lies apart from the working space; nothing else changes
but `copyClob`. -/
theorem copyTbl_ok {s : State} {base : Addr} {sz : Nat} (hs : Scr s base sz) {sym : String}
    {ws : List (BitVec 64)} {n k dst : Nat} (hk : 0 < k) (hl : ws.length = n * k) (hk32 : k < 2 ^ 32)
    (henc : encodable (BitVec.ofNat 32 k) = true) (h8 : encodable (BitVec.ofNat 32 (8 * n)) = true)
    (hT : TblAt s base sz (s.syms sym) ws dst) :
    WP isa (copyTbl sym n k dst) s fun s' =>
      (∀ i < ws.length, word s'.mem base (dst + 8 * i) = ws.getD i 0) ∧ Rest copyClob s s' ∧
        Outside base dst (8 * ws.length) s.mem s'.mem := by
  unfold copyTbl
  refine WP.seq (VG.Proof.X25519.Arm.WP.cons exec_adrSym (wp_mov (op2_reg _ _) fun s₂ u₂ =>
    wp_mov (op2_imm henc) fun s₃ u₃ => WP.block_nil ?_))
  obtain u₁ := Upd.setReg s .r10 (s.syms sym)
  obtain K₃ : Rest copyClob s s₃ := (u₁.rest (by simp)).trans ((u₂.rest (by simp)).trans (u₃.rest (by simp)))
  obtain I₃ : CInv base sz (s.syms sym) ws dst s s₃ k (8 * (n * (k - k))) (n * (k - k)) := by
    rw [Nat.sub_self, Nat.mul_zero, Nat.mul_zero]
    refine ⟨hs.of_rest K₃ (by decide), u₃.gpr, ?_, ?_, K₃,
      by rw [u₃.mem, u₂.mem, u₁.mem]; exact VG.Proof.Mont.Outside.refl _ _ _ _,
      fun t ht => absurd ht (Nat.not_lt_zero _)⟩
    · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, BitVec.add_zero]
    · rw [u₃.other _ (by decide), u₂.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
        BitVec.add_zero]
  refine countLoop_ok (Inv := fun j t => CInv base sz (s.syms sym) ws dst s t j (8 * (n * (k - j))) (n * (k - j)))
    (n := k) (fun j t h1 h2 hb => ?_)
    (fun t hb => ⟨fun i hi => hb.done i (by rw [Nat.sub_zero, ← hl]; exact hi), hb.keep, hb.mem⟩) hk I₃
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega_arith⟩
  obtain hle : n * (k - (i + 1)) + n ≤ ws.length := by
    rw [← Nat.mul_succ, hl]; exact Nat.mul_le_mul_left _ (by omega_arith)
  rw [Nat.add_sub_cancel, show k - i = k - (i + 1) + 1 by omega_arith, Nat.mul_succ]
  exact copyTblBody_ok hT hb hle (by omega_arith) h8

/-! ## The constants -/

theorem consts_fst (c : Cfg) :
    c.consts.map Prod.fst = [0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] := rfl

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

/-! ## The constants, from their table -/

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

/-- The table, in a later state of the same readable regions and statics
whose memory changed only in the working space's first `size` bytes. -/
theorem ConstTblOk.mono {c : Cfg} {sc : Addr} {s t : State} (h : ConstTblOk c sc s) (hy : t.syms = s.syms)
    (hr : t.rd ++ t.wr = s.rd ++ s.wr) (ho : Outside sc 0 size s.mem t.mem) : ConstTblOk c sc t := by
  obtain hf := h.fit
  refine ⟨by rw [hy]; exact hf, by rw [hr, hy]; exact h.rd, fun i hi => ?_, by rw [hy]; exact h.sep⟩
  rw [hy, ← h.words i hi]
  exact readW_keep fun j hj => keep_of_disjoint' ho h.sep (by decide) (by omega_arith) (by omega_arith)

/-- Two tables of words, one after the other at `T`, for the witnesses that
a contract with both can be met. -/
theorem constMem_held₂ (T : Addr) (W₁ W₂ : List (BitVec 64)) (h : 8 * (W₁.length + W₂.length) ≤ 2 ^ 64) :
    (∀ i < W₁.length, (constMem T (W₁ ++ W₂)).readW (T + BitVec.ofNat 64 (8 * i)) 64 = W₁.getD i 0) ∧
    (∀ i < W₂.length, (constMem T (W₁ ++ W₂)).readW (T + BitVec.ofNat 64 (8 * W₁.length) + BitVec.ofNat 64 (8 * i)) 64 =
      W₂.getD i 0) := by
  obtain held := constMem_held T (W₁ ++ W₂) (by rw [List.length_append]; exact h)
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rw [held i (by rw [List.length_append]; omega_arith)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  · rw [Offset.add_add, ← Nat.mul_add, held _ (by rw [List.length_append]; omega_arith)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-! ## Witnesses of the contracts that list the table -/

/-- The table's region, `17 n` words at its symbol. -/
theorem constRegs_tbl (c : Cfg) (s : State) :
    constRegs c.constsK s = [⟨symAddr s c.constSym, 8 * (17 * c.n)⟩] := by
  simp only [Cfg.constsK, Abi.constRegions, List.map_cons, List.map_nil, constTbl_length]

theorem setWidth_toNat32 (T : BitVec 32) : (T.setWidth 64).toNat = T.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans T.isLt (by decide))]

/-- What a table at `T` of `len` bytes needs of a witness's regions. -/
theorem tblRegion_ok {s : State} {st : Nat} {T : BitVec 32} {len : Nat} (hfit : T.toNat + len ≤ 2 ^ 32)
    (hwr : ∀ r ∈ s.wr, Region.sep ⟨T.setWidth 64, len⟩ r = true)
    (hres : ∀ r ∈ abi.reserved st s, Region.sep ⟨T.setWidth 64, len⟩ r = true) :
    (⟨T.setWidth 64, len⟩ : Region).base.toNat + len ≤ 2 ^ 32 ∧
      (∀ r ∈ s.wr, (⟨T.setWidth 64, len⟩ : Region).Disjoint r) ∧
      ∀ r ∈ abi.reserved st s, (⟨T.setWidth 64, len⟩ : Region).Disjoint r :=
  ⟨by rw [setWidth_toNat32]; exact hfit, fun r hr => Region.disjoint_of_sep (hwr r hr),
    fun r hr => Region.disjoint_of_sep (hres r hr)⟩

/-- `ConstsOk` of a witness of a contract that lists only the table, which
it holds at `T` (`constMem`), apart from its writable regions and the stack
the contract reserves, as `sat_consts` asks. -/
theorem constsOk_tbl (c : Cfg) {s : State} {st : Nat} {T : BitVec 32} (hsy : s.syms c.constSym = T)
    (hm : s.mem = constMem (T.setWidth 64) c.constTbl) (hfit : T.toNat + 8 * (17 * c.n) ≤ 2 ^ 32)
    (hal : T.toNat % 64 = 0) (hwr : ∀ r ∈ s.wr, Region.sep ⟨T.setWidth 64, 8 * (17 * c.n)⟩ r = true)
    (hres : ∀ r ∈ abi.reserved st s, Region.sep ⟨T.setWidth 64, 8 * (17 * c.n)⟩ r = true) :
    ConstsOk c.constsK st { s with rd := s.rd ++ constRegs c.constsK s } := by
  obtain hA : symAddr s c.constSym = T.setWidth 64 := by rw [symAddr, hsy]
  refine constsOk_append (fun x hx i hi => ?_) (fun t ht => ?_) (fun t ht => ?_)
  · obtain rfl := List.mem_singleton.mp hx
    rw [hm, hA]
    exact constMem_held _ _ (by rw [constTbl_length]; omega_arith) i hi
  · rw [constRegs_tbl, hA] at ht
    obtain rfl := List.mem_singleton.mp ht
    exact tblRegion_ok hfit hwr hres
  · rw [constRegs_tbl, hA] at ht
    obtain rfl := List.mem_singleton.mp ht
    show (T.setWidth 64).toNat % 64 = 0
    rw [setWidth_toNat32]; exact hal

/-- The regions of the table `(n₁, W₁)` (the generator's comb) at `T` and
the curve's table at `T₂`. -/
theorem constRegs_two (c : Cfg) {n₁ : String} {W₁ : List (BitVec 64)} {s : State} {T T₂ : BitVec 32}
    (hsy₁ : s.syms n₁ = T) (hsy₂ : s.syms c.constSym = T₂) :
    constRegs ((n₁, W₁) :: c.constsK) s = [⟨T.setWidth 64, 8 * W₁.length⟩, ⟨T₂.setWidth 64, 8 * (17 * c.n)⟩] := by
  simp only [Abi.constRegions, List.map_cons, List.map_nil, Cfg.constsK, constTbl_length, symAddr, hsy₁, hsy₂]

/-- `ConstsOk` of a witness of a contract that lists the table `(n₁, W₁)`
(the generator's comb), then the curve's table: both in `constMem` at `T`,
the second at `T₂ = T + 8 |W₁|`, apart from the witness's writable regions
and the stack the contract reserves. -/
theorem constsOk_two (c : Cfg) {n₁ : String} {W₁ : List (BitVec 64)} {s : State} {st : Nat}
    {T T₂ : BitVec 32} (hsy₁ : s.syms n₁ = T) (hsy₂ : s.syms c.constSym = T₂)
    (hT₂ : T₂.toNat = T.toNat + 8 * W₁.length) (hm : s.mem = constMem (T.setWidth 64) (W₁ ++ c.constTbl))
    (hfit : T₂.toNat + 8 * (17 * c.n) ≤ 2 ^ 32) (hal₁ : T.toNat % 64 = 0) (hal₂ : T₂.toNat % 64 = 0)
    (hwr₁ : ∀ r ∈ s.wr, Region.sep ⟨T.setWidth 64, 8 * W₁.length⟩ r = true)
    (hwr₂ : ∀ r ∈ s.wr, Region.sep ⟨T₂.setWidth 64, 8 * (17 * c.n)⟩ r = true)
    (hres₁ : ∀ r ∈ abi.reserved st s, Region.sep ⟨T.setWidth 64, 8 * W₁.length⟩ r = true)
    (hres₂ : ∀ r ∈ abi.reserved st s, Region.sep ⟨T₂.setWidth 64, 8 * (17 * c.n)⟩ r = true) :
    ConstsOk ((n₁, W₁) :: c.constsK) st { s with rd := s.rd ++ constRegs ((n₁, W₁) :: c.constsK) s } := by
  obtain hA₁ : symAddr s n₁ = T.setWidth 64 := by rw [symAddr, hsy₁]
  obtain hA₂ : symAddr s c.constSym = T.setWidth 64 + BitVec.ofNat 64 (8 * W₁.length) := by
    rw [symAddr, hsy₂]
    apply BitVec.eq_of_toNat_eq
    rw [setWidth_toNat32, BitVec.toNat_add, setWidth_toNat32, BitVec.toNat_ofNat, hT₂]
    omega_arith
  obtain hR := constRegs_two c (W₁ := W₁) hsy₁ hsy₂
  obtain ⟨h₁, h₂⟩ := constMem_held₂ (T.setWidth 64) W₁ c.constTbl (by rw [constTbl_length]; omega_arith)
  refine constsOk_append (fun x hx i hi => ?_) (fun t ht => ?_) (fun t ht => ?_)
  · simp only [Cfg.constsK, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rw [hm, hA₁]; exact h₁ i hi
    · rw [hm, hA₂]; exact h₂ i hi
  · rw [hR] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact tblRegion_ok (by omega_arith) hwr₁ hres₁
    · exact tblRegion_ok hfit hwr₂ hres₂
  · rw [hR] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · show (T.setWidth 64).toNat % 64 = 0
      rw [setWidth_toNat32]; exact hal₁
    · show (T₂.setWidth 64).toNat % 64 = 0
      rw [setWidth_toNat32]; exact hal₂

/-- The table of constants, under a contract that lists it
(`Abi.withConsts`, `ConstsOk`), as `SetupPre` takes it, for the working
space at the start of the writable region `⟨sc, 8192⟩`. -/
theorem tbl_of_consts {c : Cfg} {K : List (String × List (BitVec 64))} {st : Nat} {s : State} {sc : Addr}
    (hk : ConstsOk K st s) (hc : (c.constSym, c.constTbl) ∈ K) (hw : (⟨sc, 8192⟩ : Region) ∈ s.wr) :
    ConstTblOk c sc s := by
  obtain hr : (⟨symAddr s c.constSym, 8 * c.constTbl.length⟩ : Region) ∈ constRegs K s :=
    List.mem_map_of_mem (f := fun c => (⟨symAddr s c.1, 8 * c.2.length⟩ : Region)) hc
  refine ⟨hk.fit hc, ⟨_, List.mem_append_left _ (List.mem_of_mem_drop (hk.1 ▸ hr)), Region.contains_self _ _⟩,
    fun i hi => hk.2.1 _ hc i hi, ?_⟩
  exact ((hk.2.2.1 _ hr).2.1 _ hw).sub_right (Region.sub_prefix (by decide))

/-- The constants into their slots (`Cfg.constsCode`), from their table,
which `ConstTblOk` gives. Only their slots change, and what `copyTbl` may
(`copyClob`). -/
theorem constsCode_ok {c : Cfg} (hc : CfgOk c) {t : State} {base : Addr} (hs : Scr t base size)
    (T : ConstTblOk c base t) :
    WP isa c.constsCode t fun t' =>
      (∀ ix ∈ c.consts, wordsVal t'.mem base (c.sl ix.1) c.n = ix.2) ∧ Rest copyClob t t' ∧
        Outside base (c.sl 0) (8 * c.n * 17) t.mem t'.mem := by
  have h7 := hc.n10
  have h0 := hc.n0
  obtain h17 := sl_le c h7 (i := 17) (by decide)
  obtain h0' : c.sl 0 + 8 * c.n * 17 = c.sl 17 := by rw [sl_eq, sl_eq]; omega_arith
  obtain hL := constTbl_length c
  obtain h8 : encodable (BitVec.ofNat 32 (8 * c.n)) = true := by
    have : ∀ n < 10, encodable (BitVec.ofNat 32 (8 * n)) = true := by decide
    exact this _ h7
  refine WP.mono (copyTbl_ok hs (sym := c.constSym) (ws := c.constTbl) (n := c.n) (k := 17) (dst := c.sl 0)
    (by decide) (by rw [hL, Nat.mul_comm]) (by decide) (by decide) h8
    ⟨by rw [hL]; omega_arith, T.fit, T.rd, T.words, T.sep⟩)
    fun t' ⟨e, k, O⟩ => ⟨fun ix hix => ?_, k,
      by rw [hL, show 8 * (17 * c.n) = 8 * c.n * 17 by omega_arith] at O; exact O⟩
  rw [hL] at e
  exact wordsVal_of_tbl (consts_bounds hc ix hix).1 (slotVal_of_mem c ix hix) (consts_bounds hc ix hix).2 e

/-! ## The whole setup -/

theorem saveCode_eq : Cfg.saveCode = Cfg.saved.map fun p => .str p.1 wb p.2 := rfl

theorem saved_pairwise : Cfg.saved.Pairwise (fun p q => p.2 + 4 ≤ q.2 ∨ q.2 + 4 ≤ p.2) := by decide

theorem saved_lt : ∀ p ∈ Cfg.saved, p.2 + 4 ≤ 36 := by decide

theorem saved_r12 : ∀ p ∈ Cfg.saved, p.1 ≠ .r12 ∧ p.1 ≠ .r0 := by decide

/-- The working space's base to `r12`. -/
theorem scStart_ok {A : Args} {s : State} {is : List Instr} {Q : State → Prop}
    (hin : A.sc = none → InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 4)
    (k : ∀ s₁, Upd s s₁ .r12 (scVal A s) → WP isa (.block is) s₁ Q) :
    WP isa (.block (Cfg.scStart A :: is)) s Q := by
  obtain ⟨ak, ad, ae, _ | r⟩ := A
  · have ha : State.addr (s.sp + BitVec.ofNat 32 0) = stackArgAddr s 0 := by simp [stackArgAddr]
    refine wp_ldrSp (by decide) (by rw [ha]; exact hin rfl) fun s₁ u₁ => k s₁ ?_
    rw [ha] at u₁
    exact u₁
  · exact wp_mov (op2_reg _ _) fun s₁ u₁ => k s₁ u₁

theorem setup_eq (c : Cfg) (A : Args) : c.setupWith A = .seq (.block (Cfg.scStart A :: (Cfg.saveCode ++
    (.mov .lr (.reg .r0) :: (loadBytes c.C.len c.n (c.sl K) A.k ++ (loadBytes c.C.len c.n (c.sl D) A.d ++
    (loadBytes c.C.len c.n (c.sl E) A.e ++ c.shiftCode A.hs)))))))
    (.seq c.constsCode (.block [.mov .r4 (.imm 0), .dp .sub .r4 .r4 (.imm 1), .str .r4 wb (c.sl FLAG)])) := by
  simp only [Cfg.setupWith, List.append_assoc, List.cons_append, List.nil_append]

theorem setup_ok {c : Cfg} (hc : CfgOk c) {A : Args} {s : State} (hp : SetupPre c A s) :
    WP isa (c.setupWith A) s (SetupPost c A s (scBase A s)) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hsz : size = 4096 := rfl
  have hfit := hp.sc_fit
  obtain ⟨hk4, hd4, he4⟩ := hp.args
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk4 hd4 he4
  rw [setup_eq]
  refine WP.seq (WP.mono_syms (Q := fun t => t.syms = s.syms → _) ?_ fun t h hy => h hy)
  -- The working space's base.
  refine scStart_ok hp.sc_in fun s₁ u₁ => ?_
  obtain hb₁ : State.addr (s₁.gpr .r12) = scBase A s := by rw [u₁.gpr]
  obtain hs₁ : Scr s₁ (scBase A s) size := ⟨hb₁, ⟨8192, by decide, by decide, by rw [u₁.wr]; exact hp.wr⟩,
    by simp only [scBase, State.addr, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]; omega_arith, by decide⟩
  have hn := hs₁.nowrap
  -- The saves.
  rw [saveCode_eq]
  refine VG.Proof.X25519.Arm.WP.append (strs_ok hs₁ Cfg.saved (fun p hp' => by have := saved_lt p hp'; omega_arith)
    saved_pairwise) fun s₂ ⟨K₂, O₂, V₂⟩ => ?_
  obtain hs₂ := hs₁.of_rest K₂ (by decide)
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => ?_
  obtain hs₃ := hs₂.of_rest (u₃.rest (ws := [.lr]) (by simp)) (by decide)
  obtain K₃ : Rest [.r12, .lr] s s₃ := (u₁.rest (by simp)).trans ((K₂.mono (by simp)).trans (u₃.rest (by simp)))
  obtain lr₃ : s₃.gpr .lr = s.gpr .r0 := by
    rw [u₃.gpr, K₂.gpr _ (by simp), u₁.other _ (by decide)]
  obtain O₂' : Outside (scBase A s) 0 36 s₁.mem s₂.mem := fun x hx => O₂ x fun w hw => by
    obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hw
    have := saved_lt p hp'
    dsimp only; omega_arith
  obtain O₃ : Outside (scBase A s) 0 size s.mem s₃.mem := by
    rw [← u₁.mem, u₃.mem]
    exact O₂'.mono (Nat.le_refl _) (by omega_arith)
  obtain RW₃ : s₃.rd ++ s₃.wr = s.rd ++ s.wr := by rw [K₃.rd, K₃.wr]
  -- `k`
  refine VG.Proof.X25519.Arm.WP.append (setupLoad_ok hc (s := s) hs₃ (i := K) (by decide) hk4.1
    (K₃.gpr _ (by simpa using hk4.2)) hp.k_fit (by rw [RW₃]; exact hp.k_in) hp.k_sc O₃) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  obtain hs₄ := hs₃.of_rest k₄ (by decide)
  obtain K₄ : Rest [.r4, .r12, .lr] s s₄ := (K₃.mono (by simp)).trans (k₄.mono (by simp))
  obtain O₄' : Outside (scBase A s) 0 size s.mem s₄.mem :=
    O₃.trans (O₄.mono (Nat.zero_le _) (by have := sl_le c h7 (i := K) (by decide); omega_arith))
  -- `d`
  refine VG.Proof.X25519.Arm.WP.append (setupLoad_ok hc (s := s) hs₄ (i := D) (by decide) hd4.1
    (K₄.gpr _ (by simpa using hd4)) hp.d_fit (by rw [K₄.rd, K₄.wr]; exact hp.d_in) hp.d_sc O₄')
    fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  obtain hs₅ := hs₄.of_rest k₅ (by decide)
  obtain K₅ : Rest [.r4, .r12, .lr] s s₅ := K₄.trans (k₅.mono (by simp))
  obtain O₅' : Outside (scBase A s) 0 size s.mem s₅.mem :=
    O₄'.trans (O₅.mono (Nat.zero_le _) (by have := sl_le c h7 (i := D) (by decide); omega_arith))
  -- the hash
  refine VG.Proof.X25519.Arm.WP.append (setupLoad_ok hc (s := s) hs₅ (i := E) (by decide) he4.1
    (K₅.gpr _ (by simpa using he4)) hp.e_fit (by rw [K₅.rd, K₅.wr]; exact hp.e_in) hp.e_sc O₅')
    fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  obtain hs₆ := hs₅.of_rest k₆ (by decide)
  -- the shift
  refine WP.mono (setupShift_ok hc hp.shift hs₆) fun sS ⟨fK, fD, fE, kS, OS⟩ hyS => ?_
  obtain hsS := hs₆.of_rest kS (by decide)
  -- the constants
  obtain OS' : Outside (scBase A s) 0 size s.mem sS.mem :=
    (O₅'.trans (O₆.mono (Nat.zero_le _) (by have := sl_le c h7 (i := E) (by decide); omega_arith))).trans
      (OS.mono (Nat.zero_le _) (by
        have := sl_le c h7 (i := E) (by decide); rw [sl_eq] at this ⊢; simp only [K, E] at this ⊢; omega_arith))
  refine WP.seq (WP.mono (constsCode_ok hc hsS (hp.tbl.mono hyS
    (by rw [kS.rd, kS.wr, k₆.rd, k₆.wr, K₅.rd, K₅.wr]) OS')) fun s₇ ⟨e₇, k₇, O₇⟩ => ?_)
  obtain hs₇ := hsS.of_rest k₇ (by decide)
  -- the flag
  refine wp_mov (op2_imm (by decide)) fun s₈ u₈ => ?_
  refine wp_dp (op2_imm (by decide)) fun s₉ u₉ => ?_
  obtain k₉ : Rest [.r4] s₇ s₉ := (u₈.rest (by simp)).trans (u₉.rest (by simp))
  obtain hs₉ := hs₇.of_rest k₉ (by decide)
  obtain hF := sl_le c h7 (i := FLAG) (by decide)
  refine wp_str (hs₁.off_lt (by omega_arith)) (hs₉.ea (d := c.sl FLAG) (by omega_arith))
    (hs₉.write (d := c.sl FLAG) (n := 4) (by omega_arith)) fun s' m' => WP.block_nil ?_
  obtain O' : Outside (scBase A s) (c.sl FLAG) 4 s₇.mem s'.mem := by
    rw [m'.mem, u₉.mem, u₈.mem]; exact writeW32_outside _ _ _ (by omega_arith)
  -- Everything after the saves writes only in `[64, size)`.
  obtain h17 := sl_le c h7 (i := 17) (by decide)
  obtain hK := sl_le c h7 (i := K) (by decide)
  obtain hD := sl_le c h7 (i := D) (by decide)
  obtain hE := sl_le c h7 (i := E) (by decide)
  obtain hK17 := sl_lt c (i := 17) (j := K) (by decide)
  obtain hDK := sl_lt c (i := K) (j := D) (by decide)
  obtain hED := sl_lt c (i := D) (j := E) (by decide)
  obtain hFE := sl_lt c (i := E) (j := FLAG) (by decide)
  obtain h0' : c.sl 0 + 8 * c.n * 17 = c.sl 17 := by rw [sl_eq, sl_eq]; omega_arith
  obtain hsl0 : c.sl 0 = 64 := by rw [sl_eq]; omega_arith
  obtain Ol : Outside (scBase A s) 64 (size - 64) s₃.mem s'.mem := by
    exact (((((O₄.mono (by omega_arith) (by omega_arith)).trans (O₅.mono (by omega_arith) (by omega_arith))).trans
      (O₆.mono (by omega_arith) (by omega_arith))).trans (OS.mono (by omega_arith) (by omega_arith))).trans
      (O₇.mono (by omega_arith) (by omega_arith))).trans (O'.mono (by omega_arith) (by omega_arith))
  obtain K' : Rest [.r4, .r5, .r9, .r10, .r11, .r12, .lr] s s' := ((K₅.mono (by simp)).trans (k₆.mono (by simp))).trans
    ((kS.mono (by simp)).trans ((k₇.mono (by simp)).trans ((k₉.mono (by simp)).trans (m'.rest _))))
  obtain K₃' : Rest [.r4, .r5, .r9, .r10, .r11, .r12] s₃ s' := ((k₄.mono (by simp)).trans (k₅.mono (by simp))).trans
    ((k₆.mono (by simp)).trans ((kS.mono (by simp)).trans ((k₇.mono (by simp)).trans
      ((k₉.mono (by simp)).trans (m'.rest _)))))
  refine ⟨hs₉.of_rest (m'.rest []) (by decide), ⟨by rw [K'.wr]; exact hp.wr,
    by simp only [scBase, State.addr, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]; omega_arith⟩, K', ?_, fun rd hrd => ?_, ?_, ?_, ?_, ?_, fun ix hix => ?_, ?_⟩
  · exact (O₃.trans (Ol.mono (Nat.zero_le _) (by omega_arith))).unch
  · have hlt := saved_lt rd hrd
    obtain hw32 := Ol.w32 (d := rd.2) (by omega_arith) (by omega_arith)
    rw [BitVec.eq_of_toNat_eq hw32, u₃.mem, V₂ rd hrd, u₁.other _ (saved_r12 rd hrd).1]
  · rw [K₃'.gpr _ (by decide), lr₃]
  · show wordsVal s'.mem _ _ _ = _
    rw [(O'.unch).wordsVal (fun w hw => by simp at hw; rw [hw]; simp; omega_arith) (by omega_arith),
      O₇.wordsVal (by omega_arith) (by omega_arith), fK, O₆.wordsVal (by omega_arith) (by omega_arith),
      O₅.wordsVal (by omega_arith) (by omega_arith), e₄]
  · show wordsVal s'.mem _ _ _ = _
    rw [(O'.unch).wordsVal (fun w hw => by simp at hw; rw [hw]; simp; omega_arith) (by omega_arith),
      O₇.wordsVal (by omega_arith) (by omega_arith), fD, O₆.wordsVal (by omega_arith) (by omega_arith), e₅]
  · show wordsVal s'.mem _ _ _ = _
    rw [(O'.unch).wordsVal (fun w hw => by simp at hw; rw [hw]; simp; omega_arith) (by omega_arith),
      O₇.wordsVal (by omega_arith) (by omega_arith), fE, e₆]
  · have := sl_lt c (consts_bounds hc ix hix).1
    have := sl_lt c (i := ix.1) (j := FLAG) (by have := (consts_bounds hc ix hix).1; show ix.1 < 44; omega_arith)
    have := sl_le c h7 (i := ix.1) (by have := (consts_bounds hc ix hix).1; omega_arith)
    show wordsVal s'.mem _ _ _ = _
    rw [(O'.unch).wordsVal (fun w hw => by simp at hw; rw [hw]; simp; omega_arith) (by omega_arith), e₇ ix hix]
  · rw [flagW, m'.mem, Mem.readW_writeW_self32, u₉.gpr, dpVal, u₈.gpr]; rfl

end VG.Proof.Ecdsa.Arm
