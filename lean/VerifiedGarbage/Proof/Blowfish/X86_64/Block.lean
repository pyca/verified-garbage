import VerifiedGarbage.Proof.Blowfish.X86_64.Round
import VerifiedGarbage.Proof.Blowfish.Blocks

/-!
# A block in and out of the halves

`loadBlock_run`: the big-endian words of the block at `rsi` into the halves;
`storeBlock_run`: the output block, xL (in `xR`) and xR (in `xL`), back to
`rsi`, through the working space at `rcx`.
-/

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Blowfish.X86_64 VG.Spec.Blowfish VG.Proof.Blowfish

theorem bswap32_byte (x : BitVec 32) {b : Nat} (hb : b < 4) :
    (bswap32 x).extractLsb' (8 * b) 8 = x.extractLsb' (8 * (3 - b)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, getLsbD_bswap32_block _ hb hi]
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> simp

/-- The big-endian word at offset `o` of the block at `q`. -/
theorem bswap_readW (m : Mem) (q : Addr) {o : Nat} (ho : o ≤ 4) :
    bswap32 (m.readW (q + BitVec.ofNat 64 o) 32) = decodeWord (blockAt m q) o := by
  refine word_ext fun b hb => ?_
  rw [bswap32_byte _ hb, decodeWord_byte _ _ hb, blockAt_getD _ _ (by omega),
    show 8 * (3 - b) = 8 * (3 - b) from rfl, ← Mem.readW_byte m _ (by omega), Offset.add_add]

theorem ea_mem (t : State) (r : Reg) (o : Nat) : t.ea (mem r o) = t.gpr r + BitVec.ofNat 64 o := by
  simp only [State.ea, mem, Rc2.X86_64.offset_nat]

theorem exec_bswap32 (s : State) (d : Reg) :
    exec (.bswap32 d) s = some (s.setReg32 d (bswap32 ((s.gpr d).setWidth 32))) := rfl

theorem loadBlock_run (t : State) (q : Addr) (hq : t.gpr .rsi = q)
    (hR : ∀ o ≤ 4, InRegions (t.rd ++ t.wr) (q + BitVec.ofNat 64 o) 4) :
    ∃ t', runBlock isa loadBlock t = some t' ∧
      dword (t'.xmm xL) 0 = decodeWord (blockAt t.mem q) 0 ∧ dword (t'.xmm xR) 0 = decodeWord (blockAt t.mem q) 4 ∧
      (∀ d, d ≠ xL → d ≠ xR → t'.xmm d = t.xmm d) ∧ (∀ g, g ≠ .r11 → t'.gpr g = t.gpr g) ∧ Upd t t' := by
  have r0 : InRegions (t.rd ++ t.wr) (t.ea (mem .rsi 0)) 4 := by rw [ea_mem, hq]; exact hR 0 (by omega)
  let w0 := t.mem.readW (t.ea (mem .rsi 0)) 32
  let t₁ := t.setReg32 .r11 w0
  let t₂ := t₁.setReg32 .r11 (bswap32 ((t₁.gpr .r11).setWidth 32))
  let t₃ := (XOp.movq xL .r11).exec t₂
  have r4 : InRegions (t₃.rd ++ t₃.wr) (t₃.ea (mem .rsi 4)) 4 := by
    rw [ea_mem]; simp only [t₃, t₂, t₁, XOp.exec, gpr_setXmm, State.setReg32, rd_setXmm, wr_setXmm, rd_setReg, wr_setReg,
      gpr_setReg_of_ne _ _ (show Reg.rsi ≠ Reg.r11 by decide), hq]; exact hR 4 (by omega)
  let w4 := t₃.mem.readW (t₃.ea (mem .rsi 4)) 32
  let t₄ := t₃.setReg32 .r11 w4
  let t₅ := t₄.setReg32 .r11 (bswap32 ((t₄.gpr .r11).setWidth 32))
  let t₆ := (XOp.movq xR .r11).exec t₅
  refine ⟨t₆, ?_, ?_, ?_, fun d h1 h2 => ?_, fun g h => ?_, ?_⟩
  · rw [loadBlock, runBlock_cons, exec_mov32_mem r0, runStep_some, runBlock_cons, exec_bswap32, runStep_some,
      runBlock_cons, exec_xop, runStep_some, runBlock_cons, exec_mov32_mem r4, runStep_some, runBlock_cons,
      exec_bswap32, runStep_some, runBlock_cons, exec_xop, runStep_some, runBlock_nil]
  · simp only [t₆, XOp.exec, xmm_setXmm_of_ne _ _ (show xL ≠ xR by decide), t₅, t₄, State.setReg32, xmm_setReg,
      t₃, xmm_setXmm_self]
    rw [dword_movq _ _ (bswap32 w0) (by simp only [t₂, t₁, State.setReg32, gpr_setReg_self, setWidth_setWidth_32]),
      ← bswap_readW _ _ (by omega)]
    simp only [w0, ea_mem, hq]
  · simp only [t₆, XOp.exec, xmm_setXmm_self]
    rw [dword_movq _ _ (bswap32 w4) (by simp only [t₅, t₄, State.setReg32, gpr_setReg_self, setWidth_setWidth_32]),
      ← bswap_readW _ _ (by omega)]
    simp only [w4, ea_mem, t₃, t₂, t₁, XOp.exec, gpr_setXmm, State.setReg32, mem_setXmm, mem_setReg,
      gpr_setReg_of_ne _ _ (show Reg.rsi ≠ Reg.r11 by decide), hq]
  · simp only [t₆, t₅, t₄, t₃, t₂, t₁, XOp.exec, State.setReg32, xmm_setXmm_of_ne _ _ h2, xmm_setReg,
      xmm_setXmm_of_ne _ _ h1]
  · simp only [t₆, t₅, t₄, t₃, t₂, t₁, XOp.exec, State.setReg32, gpr_setXmm, gpr_setReg_of_ne _ _ h]
  · unfold Upd; simp only [t₆, t₅, t₄, t₃, t₂, t₁, XOp.exec, State.setReg32, State.setXmm, State.setReg]

theorem exec_movdquStore {s : State} {m : MemOp} {r : XReg} (h : InRegions s.wr (s.ea m) 16) :
    exec (.movdquStore m r) s = some { s with mem := s.mem.writeW (s.ea m) (s.xmm r) } := by
  simp only [exec, State.store128, h, ite_true]

theorem exec_store32 {s : State} {m : MemOp} {r : Reg} (h : InRegions s.wr (s.ea m) 4) :
    exec (.store32 m r) s = some { s with mem := s.mem.writeW (s.ea m) ((s.gpr r).setWidth 32) } := by
  simp only [exec, State.store32, h, ite_true]

theorem writeW32_byte (m : Mem) (a : Addr) (v : BitVec 32) {b : Nat} (hb : b < 4) :
    m.writeW a v (a + BitVec.ofNat 64 b) = v.extractLsb' (8 * b) 8 := by
  rw [Mem.readW_byte (m.writeW a v) a hb, Mem.readW_writeW_self32]

theorem readW_writeW128_0 (m : Mem) (a : Addr) (v : BitVec 128) : (m.writeW a v).readW a 32 = dword v 0 := by
  have := readW_writeW128 m a v (j := 0) (by decide)
  rwa [Nat.mul_zero, BitVec.add_zero] at this

theorem writeW_sep {m : Mem} {a x : Addr} {w : Nat} (v : BitVec w) (h : ¬ (x - a).toNat < w / 8) :
    m.writeW a v x = m x := Mem.write_apply h

theorem inRegions_off {rs : List Region} {a : Addr} {N o n : Nat} (h : InRegions rs a N) (hon : o + n ≤ N) :
    InRegions rs (a + BitVec.ofNat 64 o) n := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, hr, ?_⟩
  simp only [Region.Contains] at hc ⊢
  have e : a + BitVec.ofNat 64 o - r.base = (a - r.base) + BitVec.ofNat 64 o := by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 o),
      ← BitVec.add_assoc]
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := Nat.mod_le ((a - r.base).toNat + o % 2 ^ 64) (2 ^ 64)
  have := Nat.mod_le o (2 ^ 64)
  omega

theorem inRegions_append_right {rs ws : List Region} {a : Addr} {n : Nat} (h : InRegions ws a n) :
    InRegions (rs ++ ws) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem sep_of_disjoint {a b : Addr} {n k : Nat} (h : (⟨a, n⟩ : Region).Disjoint ⟨b, k⟩) : Mem.Sep a n b k :=
  fun x h₁ h₂ => h x (by simp only [Region.Contains]; omega) (by simp only [Region.Contains]; omega)

/-- What a block store needs: the block and the working space writable, apart. -/
structure StoreEnv (q B : Addr) (t : State) : Prop where
  rsi : t.gpr .rsi = q
  rcx : t.gpr .rcx = B
  wq : InRegions t.wr q 8
  wB : InRegions t.wr B 16
  sep : Mem.Sep q 8 B 16
  sep' : Mem.Sep B 16 q 8

theorem storeBlock_run {q B : Addr} {t : State} (E : StoreEnv q B t) :
    ∃ t', runBlock isa storeBlock t = some t' ∧
      (∀ i < 8, t'.mem (q + BitVec.ofNat 64 i) =
        (encodeBlock (dword (t.xmm xR) 0) (dword (t.xmm xL) 0)).getD i 0) ∧
      Frame [⟨q, 8⟩, ⟨B, 16⟩] t.mem t'.mem ∧ (∀ g, g ≠ .r11 → t'.gpr g = t.gpr g) ∧
      t' = { t with gpr := t'.gpr, mem := t'.mem } := by
  let A := dword (t.xmm xR) 0
  let Bw := dword (t.xmm xL) 0
  let t₁ : State := { t with mem := t.mem.writeW (t.ea (mem .rcx 0)) (t.xmm xR) }
  let t₂ := t₁.setReg32 .r11 (t₁.mem.readW (t₁.ea (mem .rcx 0)) 32)
  let t₃ := t₂.setReg32 .r11 (bswap32 ((t₂.gpr .r11).setWidth 32))
  let t₄ : State := { t₃ with mem := t₃.mem.writeW (t₃.ea (mem .rsi 0)) ((t₃.gpr .r11).setWidth 32) }
  let t₅ : State := { t₄ with mem := t₄.mem.writeW (t₄.ea (mem .rcx 0)) (t₄.xmm xL) }
  let t₆ := t₅.setReg32 .r11 (t₅.mem.readW (t₅.ea (mem .rcx 0)) 32)
  let t₇ := t₆.setReg32 .r11 (bswap32 ((t₆.gpr .r11).setWidth 32))
  let t₈ : State := { t₇ with mem := t₇.mem.writeW (t₇.ea (mem .rsi 4)) ((t₇.gpr .r11).setWidth 32) }
  have g : ∀ u : State, u.gpr .rsi = q → u.gpr .rcx = B → (u.setReg32 .r11 0).gpr .rsi = q := fun u h _ => by
    simp only [State.setReg32, gpr_setReg_of_ne _ _ (show Reg.rsi ≠ Reg.r11 by decide), h]
  have gr : ∀ k : Nat, k < 8 → ∀ r, r ≠ Reg.r11 →
      ([t₁, t₂, t₃, t₄, t₅, t₆, t₇, t₈].getD k t).gpr r = t.gpr r := by
    intro k hk r hr
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.getD_cons_zero, List.getD_cons_succ, t₈, t₇, t₆, t₅, t₄, t₃, t₂, t₁, State.setReg32,
      gpr_setReg_of_ne _ _ hr]
  have eB : ∀ k < 8, ([t₁, t₂, t₃, t₄, t₅, t₆, t₇, t₈].getD k t).ea (mem .rcx 0) = B + BitVec.ofNat 64 0 :=
    fun k hk => by rw [ea_mem, gr k hk _ (by decide), E.rcx]
  have eq0 : ∀ k < 8, ([t₁, t₂, t₃, t₄, t₅, t₆, t₇, t₈].getD k t).ea (mem .rsi 0) = q + BitVec.ofNat 64 0 :=
    fun k hk => by rw [ea_mem, gr k hk _ (by decide), E.rsi]
  have eq4 : ([t₁, t₂, t₃, t₄, t₅, t₆, t₇, t₈].getD 6 t).ea (mem .rsi 4) = q + BitVec.ofNat 64 4 := by
    rw [ea_mem, gr 6 (by decide) _ (by decide), E.rsi]
  have et : t.ea (mem .rcx 0) = B + BitVec.ofNat 64 0 := by rw [ea_mem, E.rcx]
  have wr : ∀ u : State, u.wr = t.wr → InRegions u.wr (B + BitVec.ofNat 64 0) 16 := fun u h => by
    rw [h]; exact inRegions_off E.wB (by omega)
  have rB : ∀ u : State, u.wr = t.wr → InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 0) 4 := fun u h => by
    rw [h]; exact inRegions_append_right (inRegions_off E.wB (by omega))
  have wq : ∀ u : State, u.wr = t.wr → ∀ o, o ≤ 4 → InRegions u.wr (q + BitVec.ofNat 64 o) 4 := fun u h o ho => by
    rw [h]; exact inRegions_off E.wq (by omega)
  have run : runBlock isa storeBlock t = some t₈ := by
    rw [storeBlock, runBlock_cons, exec_movdquStore (by rw [et]; exact wr t rfl), runStep_some,
      runBlock_cons, exec_mov32_mem (by have h := rB t₁ rfl; rw [← (eB 0 (by decide) : t₁.ea _ = _)] at h; exact h), runStep_some,
      runBlock_cons, exec_bswap32, runStep_some,
      runBlock_cons, exec_store32 (by have h := wq t₃ rfl 0 (by omega); rw [← (eq0 2 (by decide) : t₃.ea _ = _)] at h; exact h),
      runStep_some,
      runBlock_cons, exec_movdquStore (by have h := wr t₄ rfl; rw [← (eB 3 (by decide) : t₄.ea _ = _)] at h; exact h), runStep_some,
      runBlock_cons, exec_mov32_mem (by have h := rB t₅ rfl; rw [← (eB 4 (by decide) : t₅.ea _ = _)] at h; exact h), runStep_some,
      runBlock_cons, exec_bswap32, runStep_some,
      runBlock_cons, exec_store32 (by have h := wq t₇ rfl 4 (by omega); rw [← (eq4 : t₇.ea _ = _)] at h; exact h), runStep_some,
      runBlock_nil]
  have x₄ : t₄.xmm = t.xmm := rfl
  have ea1 : t₁.ea (mem .rcx 0) = B + BitVec.ofNat 64 0 := eB 0 (by decide)
  have ea3 : t₃.ea (mem .rsi 0) = q + BitVec.ofNat 64 0 := eq0 2 (by decide)
  have ea4 : t₄.ea (mem .rcx 0) = B + BitVec.ofNat 64 0 := eB 3 (by decide)
  have ea5 : t₅.ea (mem .rcx 0) = B + BitVec.ofNat 64 0 := eB 4 (by decide)
  have ea7 : t₇.ea (mem .rsi 4) = q + BitVec.ofNat 64 4 := eq4
  have w3 : (t₃.gpr .r11).setWidth 32 = bswap32 A := by
    simp only [t₃, State.setReg32, gpr_setReg_self, setWidth_setWidth_32]
    rw [show (t₂.gpr .r11).setWidth 32 = t₁.mem.readW (t₁.ea (mem .rcx 0)) 32 by
      simp only [t₂, State.setReg32, gpr_setReg_self, setWidth_setWidth_32], ea1,
      show t₁.mem = t.mem.writeW (B + BitVec.ofNat 64 0) (t.xmm xR) by simp only [t₁, et],
      readW_writeW128_0]
  have w7 : (t₇.gpr .r11).setWidth 32 = bswap32 Bw := by
    simp only [t₇, State.setReg32, gpr_setReg_self, setWidth_setWidth_32]
    rw [show (t₆.gpr .r11).setWidth 32 = t₅.mem.readW (t₅.ea (mem .rcx 0)) 32 by
      simp only [t₆, State.setReg32, gpr_setReg_self, setWidth_setWidth_32], ea5,
      show t₅.mem = t₄.mem.writeW (B + BitVec.ofNat 64 0) (t.xmm xL) by simp only [t₅, ea4, x₄],
      readW_writeW128_0]
  have m8 : t₈.mem = (((t.mem.writeW (B + BitVec.ofNat 64 0) (t.xmm xR)).writeW (q + BitVec.ofNat 64 0)
      (bswap32 A)).writeW (B + BitVec.ofNat 64 0) (t.xmm xL)).writeW (q + BitVec.ofNat 64 4) (bswap32 Bw) := by
    show t₇.mem.writeW (t₇.ea (mem .rsi 4)) ((t₇.gpr .r11).setWidth 32) = _
    rw [ea7, w7]
    show (t₄.mem.writeW (t₄.ea (mem .rcx 0)) (t₄.xmm xL)).writeW _ _ = _
    rw [ea4, x₄]
    show ((t₃.mem.writeW (t₃.ea (mem .rsi 0)) ((t₃.gpr .r11).setWidth 32)).writeW _ _).writeW _ _ = _
    rw [ea3, w3]
    show (((t.mem.writeW (t.ea (mem .rcx 0)) (t.xmm xR)).writeW _ _).writeW _ _).writeW _ _ = _
    rw [et]
  refine ⟨t₈, run, fun i hi => ?_, ?_, fun g h => gr 7 (by decide) g h, ?_⟩
  · have hi64 : i < 2 ^ 64 := by omega
    rw [m8, encodeBlock_getD _ _ hi]
    by_cases h4 : i < 4
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h4)]
      rw [writeW_sep _ (Offset.sep q (d := i) (n := 1) (e := 4) (k := 4) (.inl (by omega)) (by omega) (by omega) _
        (by rw [BitVec.sub_self]; decide)), writeW_sep _ (by
          rw [BitVec.add_zero]; exact E.sep _ (by rw [Mem.sub_ofNat_toNat q hi64]; omega)),
        show q + BitVec.ofNat 64 i = q + BitVec.ofNat 64 0 + BitVec.ofNat 64 i by rw [BitVec.add_zero],
        writeW32_byte _ _ _ h4, bswap32_byte _ h4]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h4),
        show q + BitVec.ofNat 64 i = q + BitVec.ofNat 64 4 + BitVec.ofNat 64 (i - 4) by
          rw [Offset.add_add]; congr 2; omega,
        writeW32_byte _ _ _ (by omega), bswap32_byte _ (by omega)]
      congr 2; omega
  · have mq : (⟨q, 8⟩ : Region) ∈ [⟨q, 8⟩, ⟨B, 16⟩] := List.mem_cons_self
    have mB : (⟨B, 16⟩ : Region) ∈ [⟨q, 8⟩, ⟨B, 16⟩] := List.mem_cons_of_mem _ List.mem_cons_self
    rw [m8]
    exact ((((Frame.refl _ _).writeW mB _ (Offset.contains_base B (by decide) (by decide))).writeW mq _
      (Offset.contains_base q (by decide) (by decide))).writeW mB _
      (Offset.contains_base B (by decide) (by decide))).writeW mq _ (Offset.contains_base q (by decide) (by decide))
  · simp only [t₈, t₇, t₆, t₅, t₄, t₃, t₂, t₁, State.setReg32, State.setReg]



end VG.Proof.Blowfish.X86_64
