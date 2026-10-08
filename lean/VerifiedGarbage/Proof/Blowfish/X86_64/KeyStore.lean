import VerifiedGarbage.Proof.Blowfish.X86_64.KeyP

/-!
# Key expansion: an encryption's output into the schedule

The output's halves go to the working space at `rcx` (`scratchOut_run`),
from there to `r11` and back into the halves (`take_run`), and to the
P-array as words (`store32_idx_run`) or to the S-boxes' planes a byte at a
time (`storeEntry_run`).
-/

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Blowfish.X86_64 VG.Spec.Blowfish VG.Proof.Blowfish

theorem scratchOut_run {t : State} {B : Addr} (hB : t.gpr .rcx = B) (hw : InRegions t.wr B 32) :
    runBlock isa outWords t = some { t with mem :=
      (t.mem.writeW (B + BitVec.ofNat 64 0) (t.xmm xR)).writeW (B + BitVec.ofNat 64 16) (t.xmm xL) } := by
  let t₁ : State := { t with mem := t.mem.writeW (B + BitVec.ofNat 64 0) (t.xmm xR) }
  have e0 : t.ea (mem .rcx 0) = B + BitVec.ofNat 64 0 := by rw [ea_mem, hB]
  have e16 : t₁.ea (mem .rcx 16) = B + BitVec.ofNat 64 16 := by rw [ea_mem]; exact congrArg (· + _) hB
  have h₁ : exec (.movdquStore (mem .rcx 0) xR) t = some t₁ := by
    rw [exec_movdquStore (by rw [e0]; exact inRegions_off hw (by omega)), e0]
  let M := (t.mem.writeW (B + BitVec.ofNat 64 0) (t.xmm xR)).writeW (B + BitVec.ofNat 64 16) (t.xmm xL)
  have h₂ : exec (.movdquStore (mem .rcx 16) xL) t₁ = some { t with mem := M } := by
    rw [exec_movdquStore (by rw [e16]; exact inRegions_off hw (by omega)), e16]
  rw [outWords, runBlock_cons, h₁, runStep_some, runBlock_cons, h₂, runStep_some, runBlock_nil]

/-- The word at `rcx + o` into `r11` and the low doubleword of `d`. -/
theorem take_run {t : State} {B : Addr} (hB : t.gpr .rcx = B) {o : Nat}
    (hr : InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 o) 4) (d : XReg) :
    ∃ t', runBlock isa [.mov32 .r11 (.mem (mem .rcx o)), .xop (.movq d .r11)] t = some t' ∧
      t'.gpr .r11 = (t.mem.readW (B + BitVec.ofNat 64 o) 32).setWidth 64 ∧
      dword (t'.xmm d) 0 = t.mem.readW (B + BitVec.ofNat 64 o) 32 ∧
      (∀ d', d' ≠ d → t'.xmm d' = t.xmm d') ∧ (∀ g, g ≠ .r11 → t'.gpr g = t.gpr g) ∧ Upd t t' := by
  have e : t.ea (mem .rcx o) = B + BitVec.ofNat 64 o := by rw [ea_mem, hB]
  let t₁ := t.setReg32 .r11 (t.mem.readW (B + BitVec.ofNat 64 o) 32)
  have g₁ : t₁.gpr .r11 = (t.mem.readW (B + BitVec.ofNat 64 o) 32).setWidth 64 := by
    simp only [t₁, State.setReg32, gpr_setReg_self]
  refine ⟨(XOp.movq d .r11).exec t₁, ?_, ?_, ?_, fun d' h => ?_, fun g h => ?_, ?_⟩
  · rw [runBlock_cons, exec_mov32_mem (by rw [e]; exact hr), e, runStep_some, runBlock_cons, exec_xop, runStep_some,
      runBlock_nil]
  · simp only [XOp.exec, gpr_setXmm]; exact g₁
  · simp only [XOp.exec, xmm_setXmm_self]; exact dword_movq _ _ _ g₁
  · simp only [XOp.exec, xmm_setXmm_of_ne _ _ h, t₁, State.setReg32, xmm_setReg]
  · simp only [XOp.exec, gpr_setXmm, t₁, State.setReg32, gpr_setReg_of_ne _ _ h]
  · unfold Upd; simp only [XOp.exec, t₁, State.setReg32, State.setXmm, State.setReg]

/-- `r11`'s low doubleword at `rdx + rdi + o`. -/
theorem store32_idx_run {t : State} {S : Addr} {d o : Nat} (hS : t.gpr .rdx = S) (hd : t.gpr .rdi = BitVec.ofNat 64 d)
    (hw : InRegions t.wr (S + BitVec.ofNat 64 (o + d)) 4) :
    runBlock isa [.store32 { base := .rdx, index := some .rdi, disp := Int.ofNat o } .r11] t =
      some { t with mem := t.mem.writeW (S + BitVec.ofNat 64 (o + d)) ((t.gpr .r11).setWidth 32) } := by
  have e := ea_idx t .rdx .rdi S d o hS hd
  rw [runBlock_cons, exec_store32 (by rw [e]; exact hw), e, runStep_some, runBlock_nil]

theorem exec_store8 {s : State} {m : MemOp} {r : Reg} (h : InRegions s.wr (s.ea m) 1) :
    exec (.store8 m r) s = some { s with mem := s.mem.writeW (s.ea m) ((s.gpr r).setWidth 8) } := by
  simp only [exec, State.store8, h, ite_true]

theorem writeW8 (m : Mem) (a : Addr) (v : BitVec 8) : m.writeW a v = m.write a 1 v := by
  simp only [Mem.writeW, BitVec.setWidth_eq]

theorem shr_setWidth8 (x : BitVec 32) (k : Nat) : ((x >>> k).setWidth 64).setWidth 8 = x.extractLsb' k 8 := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), shr_byte]

/-- The bytes of `r11`'s low doubleword into the four planes of the entry at
`rdx + rdi + e`. -/
theorem storeEntry_run {t : State} {S : Addr} {d e : Nat} (hS : t.gpr .rdx = S) (hd : t.gpr .rdi = BitVec.ofNat 64 d)
    (hw : ∀ b < 4, InRegions t.wr (S + BitVec.ofNat 64 (256 * b + e + d)) 1) :
    ∃ t', runBlock isa (storeEntry e) t = some t' ∧
      t'.mem = (((t.mem.write (S + BitVec.ofNat 64 (e + d)) 1 (((t.gpr .r11).setWidth 32).extractLsb' 0 8)).write
        (S + BitVec.ofNat 64 (256 + e + d)) 1 (((t.gpr .r11).setWidth 32).extractLsb' 8 8)).write
        (S + BitVec.ofNat 64 (512 + e + d)) 1 (((t.gpr .r11).setWidth 32).extractLsb' 16 8)).write
        (S + BitVec.ofNat 64 (768 + e + d)) 1 (((t.gpr .r11).setWidth 32).extractLsb' 24 8) ∧
      (∀ g, g ≠ .r11 → t'.gpr g = t.gpr g) ∧ t'.xmm = t.xmm ∧ UpdM t t' := by
  let w := (t.gpr .r11).setWidth 32
  have ea : ∀ (u : State) (o : Nat), u.gpr .rdx = S → u.gpr .rdi = BitVec.ofNat 64 d →
      u.ea { base := .rdx, index := some .rdi, disp := Int.ofNat o } = S + BitVec.ofNat 64 (o + d) :=
    fun u o h1 h2 => ea_idx u .rdx .rdi S d o h1 h2
  let t₁ : State := { t with mem := t.mem.writeW (S + BitVec.ofNat 64 (e + d)) ((t.gpr .r11).setWidth 8) }
  obtain ⟨t₂, e₂, r₂, g₂, xx₂, u₂⟩ := shift32_run t₁ .shr .r11 8 (by decide) (by decide)
  let t₃ : State := { t₂ with mem := t₂.mem.writeW (S + BitVec.ofNat 64 (256 + e + d)) ((t₂.gpr .r11).setWidth 8) }
  obtain ⟨t₄, e₄, r₄, g₄, xx₄, u₄⟩ := shift32_run t₃ .shr .r11 8 (by decide) (by decide)
  let t₅ : State := { t₄ with mem := t₄.mem.writeW (S + BitVec.ofNat 64 (512 + e + d)) ((t₄.gpr .r11).setWidth 8) }
  obtain ⟨t₆, e₆, r₆, g₆, xx₆, u₆⟩ := shift32_run t₅ .shr .r11 8 (by decide) (by decide)
  let t₇ : State := { t₆ with mem := t₆.mem.writeW (S + BitVec.ofNat 64 (768 + e + d)) ((t₆.gpr .r11).setWidth 8) }
  have G : ∀ g, g ≠ .r11 → t₆.gpr g = t.gpr g := fun g h => by
    rw [g₆ _ h, show t₅.gpr = t₄.gpr from rfl, g₄ _ h, show t₃.gpr = t₂.gpr from rfl, g₂ _ h]
  have G₂ : ∀ g, g ≠ .r11 → t₂.gpr g = t.gpr g := fun g h => by rw [g₂ _ h]
  have G₄ : ∀ g, g ≠ .r11 → t₄.gpr g = t.gpr g := fun g h => by
    rw [g₄ _ h, show t₃.gpr = t₂.gpr from rfl, G₂ _ h]
  have W : ∀ u : State, UpdM t u → ∀ b < 4, InRegions u.wr (S + BitVec.ofNat 64 (256 * b + e + d)) 1 :=
    fun u hu b hb => by rw [hu]; exact hw b hb
  have U₂ : UpdM t t₂ := UpdM.trans (UpdM.of_upd u₂) (UpdM.store _)
  have U₄ : UpdM t t₄ := UpdM.trans (UpdM.of_upd u₄) (UpdM.trans (UpdM.store _) U₂)
  have U₆ : UpdM t t₆ := UpdM.trans (UpdM.of_upd u₆) (UpdM.trans (UpdM.store _) U₄)
  have v₂ : t₂.gpr .r11 = (w >>> 8).setWidth 64 := by rw [r₂]; simp only [reduceCtorEq, ↓reduceIte]; rfl
  have v₄ : t₄.gpr .r11 = (w >>> 16).setWidth 64 := by
    rw [r₄, show t₃.gpr = t₂.gpr from rfl, v₂]
    simp only [reduceCtorEq, ↓reduceIte, setWidth_setWidth_32, ← BitVec.shiftRight_add, Nat.reduceAdd]
  have v₆ : t₆.gpr .r11 = (w >>> 24).setWidth 64 := by
    rw [r₆, show t₅.gpr = t₄.gpr from rfl, v₄]
    simp only [reduceCtorEq, ↓reduceIte, setWidth_setWidth_32, ← BitVec.shiftRight_add, Nat.reduceAdd]
  have w1 : InRegions t₂.wr (S + BitVec.ofNat 64 (256 + e + d)) 1 := by
    have := W t₂ U₂ 1 (by decide); simpa using this
  have w2 : InRegions t₄.wr (S + BitVec.ofNat 64 (512 + e + d)) 1 := by
    have := W t₄ U₄ 2 (by decide); simpa using this
  have w3 : InRegions t₆.wr (S + BitVec.ofNat 64 (768 + e + d)) 1 := by
    have := W t₆ U₆ 3 (by decide); simpa using this
  refine ⟨t₇, ?_, ?_, fun g h => G g h, by show t₆.xmm = t.xmm; rw [xx₆]; show t₄.xmm = t.xmm; rw [xx₄]; exact xx₂,
    UpdM.trans (UpdM.store _) U₆⟩
  · rw [storeEntry, runBlock_cons,
      exec_store8 (by rw [ea t _ hS hd]; have := hw 0 (by decide); simpa using this), ea t _ hS hd, runStep_some,
      runBlock_cons, e₂, runStep_some, runBlock_cons,
      exec_store8 (by rw [ea t₂ _ ((G₂ _ (by decide)).trans hS) ((G₂ _ (by decide)).trans hd)]; exact w1),
      ea t₂ _ ((G₂ _ (by decide)).trans hS) ((G₂ _ (by decide)).trans hd), runStep_some,
      runBlock_cons, e₄, runStep_some, runBlock_cons,
      exec_store8 (by rw [ea t₄ _ ((G₄ _ (by decide)).trans hS) ((G₄ _ (by decide)).trans hd)]; exact w2),
      ea t₄ _ ((G₄ _ (by decide)).trans hS) ((G₄ _ (by decide)).trans hd), runStep_some,
      runBlock_cons, e₆, runStep_some, runBlock_cons,
      exec_store8 (by rw [ea t₆ _ ((G _ (by decide)).trans hS) ((G _ (by decide)).trans hd)]; exact w3),
      ea t₆ _ ((G _ (by decide)).trans hS) ((G _ (by decide)).trans hd), runStep_some, runBlock_nil]
  · show t₆.mem.writeW _ ((t₆.gpr .r11).setWidth 8) = _
    rw [v₆, shr_setWidth8, writeW8, show t₆.mem = t₅.mem by rw [u₆]]
    show (t₄.mem.writeW _ ((t₄.gpr .r11).setWidth 8)).write _ _ _ = _
    rw [v₄, shr_setWidth8, writeW8, show t₄.mem = t₃.mem by rw [u₄]]
    show ((t₂.mem.writeW _ ((t₂.gpr .r11).setWidth 8)).write _ _ _).write _ _ _ = _
    rw [v₂, shr_setWidth8, writeW8, show t₂.mem = t₁.mem by rw [u₂]]
    show (((t.mem.writeW _ ((t.gpr .r11).setWidth 8)).write _ _ _).write _ _ _).write _ _ _ = _
    rw [writeW8, show (t.gpr .r11).setWidth 8 = w.extractLsb' 0 8 by
      rw [show w = w >>> 0 by simp, ← shr_byte]; simp only [w, BitVec.ushiftRight_zero]
      rw [BitVec.setWidth_setWidth_of_le _ (by decide)]]

end VG.Proof.Blowfish.X86_64
