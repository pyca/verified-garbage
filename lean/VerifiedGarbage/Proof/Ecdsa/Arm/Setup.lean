module

public import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Weierstrass.Arm.BytesLen
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Proof.Weierstrass.Arm.Const
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
(`constsCode_ok`: as immediates, `setupConsts_ok`, by induction on the list,
or copied from their table, `copyTbl_ok`, a loop counted down in `r11`) and
sets the flag to all ones: `setup_ok`, the state `SetupPost` describes.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_ldr wp_str wp_dp wp_mov op2_imm op2_reg op2_lsl dpVal)

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

/-- What `copyTbl` may change: the table's address, the counter, the
addresses and the words in flight. -/
abbrev copyClob : List Reg := [.r4, .r5, .r9, .r10, .r11]

/-- `copyTbl`'s loop invariant, at `r11 = i`: the words from `i` up are
copied, `r10` holds the table's address `A`, and only the copy's range
changed. -/
structure CInv (base : Addr) (sz : Nat) (A : BitVec 32) (ws : List (BitVec 64)) (dst : Nat)
    (s₀ s : State) (i : Nat) : Prop where
  scr : Scr s base sz
  r11 : s.gpr .r11 = BitVec.ofNat 32 i
  r10 : s.gpr .r10 = A
  keep : Rest copyClob s₀ s
  mem : Outside base dst (8 * ws.length) s₀.mem s.mem
  done : ∀ t, i ≤ t → t < ws.length → word s.mem base (dst + 8 * t) = ws.getD t 0

/-- One word of `copyTbl`'s loop, at `r11 = i + 1`: word `i` of the table at
`A`, which the copy so far left as it was (it is apart from the working
space), to `[r12 + dst + 8 i]`, as its two halves. -/
theorem copyTblBody_ok {s₀ t : State} {base : Addr} {sz : Nat} {A : BitVec 32} {ws : List (BitVec 64)}
    {dst i : Nat} (hI : CInv base sz A ws dst s₀ t (i + 1)) (hi : i < ws.length)
    (hdst : dst + 8 * ws.length ≤ sz) (hfit : A.toNat + 8 * ws.length ≤ 2 ^ 32)
    (hrd : InRegions (s₀.rd ++ s₀.wr) (State.addr A) (8 * ws.length))
    (hw : ∀ i < ws.length, s₀.mem.readW (State.addr A + BitVec.ofNat 64 (8 * i)) 64 = ws.getD i 0)
    (hsep : Region.Disjoint ⟨State.addr A, 8 * ws.length⟩ ⟨base, sz⟩) :
    WP isa (.block (copyTblBody dst)) t fun t' => CInv base sz A ws dst s₀ t' i ∧ t'.z = decide (i = 0) := by
  have hn := hI.scr.nowrap
  have hsm := hI.scr.small
  simp only [copyTblBody]
  refine wp_decCounter (j := i + 1) (by omega_arith) hI.r11 fun t₁ u₁ => ?_
  obtain c₁ : t₁.gpr .r11 = BitVec.ofNat 32 i := by rw [u₁.gpr, Nat.add_sub_cancel]
  refine wp_dp (op2_lsl (by decide)) fun t₂ u₂ => ?_
  obtain a₂ : t₂.gpr .r5 = A + BitVec.ofNat 32 (8 * i) := by
    rw [u₂.gpr, dpVal, c₁, u₁.other _ (by decide), hI.r10]; exact rowAddr _ i
  -- The table's word `i`, which the copy so far left as it was.
  obtain hv : t.mem.readW (State.addr A + BitVec.ofNat 64 (8 * i)) 64 = ws.getD i 0 := by
    rw [← hw i hi]
    exact readW_keep fun j hj => keep_of_disjoint' (hI.mem.mono (o' := 0) (n' := sz) (Nat.zero_le _)
      (by omega_arith)) hsep (by omega_arith) (by omega_arith) (by omega_arith)
  obtain ad0 : State.addr (t₂.gpr .r5 + BitVec.ofNat 32 0) = State.addr A + BitVec.ofNat 64 (8 * i) := by
    rw [a₂, Offset.add_add, Nat.add_zero]; exact addr_add (by omega_arith)
  obtain ad4 : State.addr (A + BitVec.ofNat 32 (8 * i) + BitVec.ofNat 32 4) =
      State.addr A + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 4 := by
    rw [Offset.add_add, Offset.add_add]; exact addr_add (by omega_arith)
  obtain rw₂ : t₂.rd ++ t₂.wr = s₀.rd ++ s₀.wr := by
    rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, hI.keep.rd, hI.keep.wr]
  obtain hl64 : 8 * ws.length < 2 ^ 64 := by omega_arith
  obtain hin0 : InRegions (s₀.rd ++ s₀.wr) (State.addr A + BitVec.ofNat 64 (8 * i)) 4 :=
    CallLay.inRegions_sub (off := 8 * i) (l := 4) hrd (by omega_arith) hl64
  obtain hin4 : InRegions (s₀.rd ++ s₀.wr) (State.addr A + BitVec.ofNat 64 (8 * i + 4)) 4 :=
    CallLay.inRegions_sub (off := 8 * i + 4) (l := 4) hrd (by omega_arith) hl64
  refine wp_ldr (by decide) ad0 (by rw [rw₂]; exact hin0) fun t₃ u₃ => ?_
  refine wp_ldr (a := State.addr A + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 4) (by decide)
    (by rw [u₃.other _ (by decide), a₂]; exact ad4)
    (by rw [u₃.rd, u₃.wr, rw₂, Offset.add_add]; exact hin4) fun t₄ u₄ => ?_
  refine wp_dp (op2_lsl (by decide)) fun t₅ u₅ => ?_
  obtain c₄ : t₄.gpr .r11 = BitVec.ofNat 32 i := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), c₁]
  obtain k₅ : Rest copyClob t t₅ := (u₁.rest (by simp)).trans ((u₂.rest (by simp)).trans
    ((u₃.rest (by simp)).trans ((u₄.rest (by simp)).trans (u₅.rest (by simp)))))
  obtain hs₅ := hI.scr.of_rest k₅ (by decide)
  obtain a₅ : t₅.gpr .r9 = t₅.gpr .r12 + BitVec.ofNat 32 (8 * i) := by
    rw [u₅.gpr, dpVal, c₄, u₅.other .r12 (by decide)]; exact rowAddr _ i
  obtain v4 : t₅.gpr .r4 = t.mem.readW (State.addr A + BitVec.ofNat 64 (8 * i)) 32 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem]
  obtain v5 : t₅.gpr .r5 = t.mem.readW (State.addr A + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 4) 32 := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem, u₁.mem]
  obtain m₅ : t₅.mem = t.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine wp_str (by omega_arith) (hs₅.ea_off a₅ (d := dst) (by omega_arith))
    (hs₅.write (d := 8 * i + dst) (n := 4) (by omega_arith)) fun t₆ m₆ => ?_
  obtain hs₆ := hs₅.of_rest (m₆.rest []) (by decide)
  obtain a₆ : t₆.gpr .r9 = t₆.gpr .r12 + BitVec.ofNat 32 (8 * i) := by rw [m₆.gpr]; exact a₅
  refine wp_str (by omega_arith) (hs₆.ea_off a₆ (d := dst + 4) (by omega_arith))
    (hs₆.write (d := 8 * i + (dst + 4)) (n := 4) (by omega_arith)) fun t₇ m₇ => ?_
  obtain c₇ : t₇.gpr .r11 = BitVec.ofNat 32 i := by rw [m₇.gpr, m₆.gpr, u₅.other _ (by decide), c₄]
  refine wp_testCounter (by omega_arith) c₇ fun t₈ f₈ z₈ => WP.block_nil ⟨?_, z₈⟩
  obtain M₈ : t₈.mem = (t.mem.writeW (off base (8 * i + dst)) (t.mem.readW (State.addr A + BitVec.ofNat 64 (8 * i)) 32)).writeW
      (off base (8 * i + (dst + 4))) (t.mem.readW (State.addr A + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 4) 32) := by
    rw [f₈.mem, m₇.mem, m₆.gpr, m₆.mem, m₅, v4, v5]
  obtain k₈ : Rest copyClob t t₈ := k₅.trans ((m₆.rest _).trans ((m₇.rest _).trans (f₈.rest _)))
  obtain O₈ : Outside base (8 * i + dst) 8 t.mem t₈.mem := by
    rw [M₈]
    exact ((writeW32_outside _ _ (d := 8 * i + dst) _ (by omega_arith)).mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW32_outside _ _ (d := 8 * i + (dst + 4)) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  refine ⟨hI.scr.of_rest k₈ (by decide), by rw [f₈.gpr]; exact c₇, ?_, hI.keep.trans k₈,
    hI.mem.trans (O₈.mono (by omega_arith) (by omega_arith)), fun t' h1 h2 => ?_⟩
  · rw [f₈.gpr, m₇.gpr, m₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hI.r10]
  rcases Nat.lt_or_ge i t' with h | h
  · rw [O₈.word (by omega_arith) (by omega_arith)]; exact hI.done t' (by omega_arith) h2
  · rw [show t' = i by omega_arith]
    obtain hhi : t₈.mem.readW (off base (8 * i + dst) + BitVec.ofNat 64 4) 32 =
        t.mem.readW (State.addr A + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 4) 32 := by
      rw [Offset.add_add (p := base), M₈, show 8 * i + dst + 4 = 8 * i + (dst + 4) by omega_arith,
        Mem.readW_writeW_self32]
    obtain hlo : t₈.mem.readW (off base (8 * i + dst)) 32 = t.mem.readW (State.addr A + BitVec.ofNat 64 (8 * i)) 32 := by
      apply BitVec.eq_of_toNat_eq
      show w32 t₈.mem base (8 * i + dst) = _
      rw [M₈, w32_write_ne (size := sz) hn (by omega_arith) (by omega_arith) (by omega_arith), w32_write_self]
    show t₈.mem.readW (off base (dst + 8 * i)) 64 = _
    rw [show dst + 8 * i = 8 * i + dst from Nat.add_comm _ _, Rc2.Word32.read64_pair t₈.mem, hhi, hlo,
      ← Rc2.Word32.read64_pair, hv]

/-- `copyTbl sym (ws.length) dst`: word `i` of the working space's range at
`dst` is word `i` of the table `ws` at `sym`, which the code may read and
which lies apart from the working space; nothing else changes but
`copyClob`. -/
theorem copyTbl_ok {s : State} {base : Addr} {sz : Nat} (hs : Scr s base sz) {sym : String}
    {ws : List (BitVec 64)} {dst : Nat} (hk : 0 < ws.length) (henc : encodable (BitVec.ofNat 32 ws.length) = true)
    (hdst : dst + 8 * ws.length ≤ sz) (hfit : (s.syms sym).toNat + 8 * ws.length ≤ 2 ^ 32)
    (hrd : InRegions (s.rd ++ s.wr) (State.addr (s.syms sym)) (8 * ws.length))
    (hw : ∀ i < ws.length, s.mem.readW (State.addr (s.syms sym) + BitVec.ofNat 64 (8 * i)) 64 = ws.getD i 0)
    (hsep : Region.Disjoint ⟨State.addr (s.syms sym), 8 * ws.length⟩ ⟨base, sz⟩) :
    WP isa (copyTbl sym ws.length dst) s fun s' =>
      (∀ i < ws.length, word s'.mem base (dst + 8 * i) = ws.getD i 0) ∧ Rest copyClob s s' ∧
        Outside base dst (8 * ws.length) s.mem s'.mem := by
  unfold copyTbl
  refine WP.seq (VG.Proof.X25519.Arm.WP.cons exec_adrSym (wp_mov (op2_imm henc) fun s₂ u₂ => WP.block_nil ?_))
  obtain u₁ := Upd.setReg s .r10 (s.syms sym)
  obtain K₂ : Rest copyClob s s₂ := (u₁.rest (by simp)).trans (u₂.rest (by simp))
  obtain I₂ : CInv base sz (s.syms sym) ws dst s s₂ ws.length :=
    ⟨hs.of_rest K₂ (by decide), u₂.gpr, by rw [u₂.other _ (by decide), u₁.gpr], K₂,
      by rw [u₂.mem, u₁.mem]; exact VG.Proof.Mont.Outside.refl _ _ _ _,
      fun t ht ht' => absurd ht' (by omega_arith)⟩
  refine countLoop_ok (Inv := fun j t => CInv base sz (s.syms sym) ws dst s t j) (n := ws.length)
    (fun j t h1 h2 hb => ?_) (fun t hb => ⟨fun i hi => hb.done i (Nat.zero_le _) hi, hb.keep, hb.mem⟩) hk I₂
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega_arith⟩
  rw [Nat.add_sub_cancel]
  exact copyTblBody_ok hb (by omega_arith) hdst hfit hrd hw hsep

/-! ## The constants -/

/-- The constants of `l`, apart slots below `17`, each in its slot; only their
slots change. -/
theorem setupConsts_ok {c : Cfg} (hc : CfgOk c) {base : Addr} : ∀ (l : List (Nat × Nat)) {t : State},
    Scr t base size → (∀ ix ∈ l, ix.1 < 17 ∧ ix.2 < 2 ^ (64 * c.n)) → (l.map Prod.fst).Nodup →
    WP isa (.block (l.flatMap (fun (i, x) => setConst c.n (c.sl i) x))) t fun t' =>
      (∀ ix ∈ l, wordsVal t'.mem base (c.sl ix.1) c.n = ix.2) ∧ Rest [.r4] t t' ∧
      Unch base (l.map fun ix => (c.sl ix.1, 8 * c.n)) t.mem t'.mem
  | [], _, _, _, _ => WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, Rest.refl _ _,
      Unch.refl _ _ _⟩
  | (i, x) :: l, t, hs, hb, hnd => by
    rw [List.flatMap_cons]
    obtain hi := hb (i, x) List.mem_cons_self
    obtain hl := sl_le c hc.n10 (i := i) (by omega_arith)
    refine VG.Proof.X25519.Arm.WP.append (setConst_ok hs hl hi.2) fun t₁ ⟨e₁, k₁, O₁⟩ => ?_
    obtain hs₁ := hs.of_rest k₁ (by decide)
    rw [List.map_cons, List.nodup_cons] at hnd
    refine WP.mono (setupConsts_ok hc l hs₁ (fun ix h => hb ix (List.mem_cons_of_mem _ h)) hnd.2)
      fun t' ⟨e', k', U'⟩ => ⟨fun ix h => ?_, k₁.trans k',
        show Unch base ([(c.sl i, 8 * c.n)] ++ l.map fun ix => (c.sl ix.1, 8 * c.n)) t.mem t'.mem from
          O₁.unch.trans U'⟩
    rcases List.mem_cons.mp h with rfl | h
    · refine (U'.wordsVal (fun w hw => ?_) (by have := hs.nowrap; dsimp only; omega_arith)).trans e₁
      obtain ⟨jy, hjy, rfl⟩ := List.mem_map.mp hw
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

/-! ## The constants, from their table or as immediates -/

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

/-- The constants into their slots (`Cfg.constsCode`): from their table,
which `ConstTblOk` gives, or as immediates. Only their slots change, and what
`copyTbl` may (`copyClob`). -/
theorem constsCode_ok {c : Cfg} (hc : CfgOk c) {t : State} {base : Addr} (hs : Scr t base size)
    (hT : c.tbl = true → ConstTblOk c base t) :
    WP isa c.constsCode t fun t' =>
      (∀ ix ∈ c.consts, wordsVal t'.mem base (c.sl ix.1) c.n = ix.2) ∧ Rest copyClob t t' ∧
        Outside base (c.sl 0) (8 * c.n * 17) t.mem t'.mem := by
  have h7 := hc.n10
  obtain hsl0 : c.sl 0 = 64 := by rw [sl_eq]; omega_arith
  obtain h17 := sl_le c h7 (i := 17) (by decide)
  obtain h0' : c.sl 0 + 8 * c.n * 17 = c.sl 17 := by rw [sl_eq, sl_eq]; omega_arith
  unfold Cfg.constsCode
  cases htb : c.tbl
  · -- As immediates.
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.mono (setupConsts_ok hc c.consts hs (consts_bounds hc) (consts_nodup c))
      fun t' ⟨e, k, U⟩ => ⟨e, k.mono (by decide), U.outside fun w hw => ?_⟩
    obtain ⟨ix, hix, rfl⟩ := List.mem_map.mp hw
    have := sl_lt c (consts_bounds hc ix hix).1
    have : c.sl 0 ≤ c.sl ix.1 := by rw [hsl0, sl_eq]; omega_arith
    exact ⟨this, by rw [sl_eq c 17] at *; omega_arith⟩
  · -- From the table.
    simp only [↓reduceIte]
    obtain T := hT htb
    have h0 := hc.n0
    obtain hL := constTbl_length c
    obtain henc : encodable (BitVec.ofNat 32 c.constTbl.length) = true := by
      have : ∀ n < 10, encodable (BitVec.ofNat 32 (17 * n)) = true := by decide
      rw [hL]; exact this _ h7
    rw [← hL]
    refine WP.mono (copyTbl_ok hs (sym := c.constSym) (ws := c.constTbl) (dst := c.sl 0)
      (by rw [hL]; omega_arith) henc (by rw [hL]; omega_arith) T.fit T.rd T.words T.sep)
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
  refine WP.seq (WP.mono (constsCode_ok hc hsS fun h => (hp.tbl h).mono hyS
    (by rw [kS.rd, kS.wr, k₆.rd, k₆.wr, K₅.rd, K₅.wr]) OS') fun s₇ ⟨e₇, k₇, O₇⟩ => ?_)
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
