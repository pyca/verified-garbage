module

public import VerifiedGarbage.Proof.Pbkdf2.Sha1.RISCV64.Loop
public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.IterateMain
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Align
import VerifiedGarbage.Proof.Sha1.StateMem

/-!
# PBKDF2-HMAC-SHA-1's iteration on RISC-V: the prologue

Untrusted: everything here is checked by Lean. After the entry block, which
zero-extends `n` (`Proof/Pbkdf2/RISCV64/IterateMain.lean`): the frame
aligned and our caller's registers saved there; the key's inner and outer
hash values copied to the frame as words (`cpLE_ok`); `T`'s words to the
frame (`cpT_ok`) and `U`'s to `A` (`ldU_ok`), big-endian. That is the loop's
invariant with `n` steps left (`pro_ok`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Sha1.RISCV64

open VG VG.RISCV64 VG.Impl.Pbkdf2.Sha1.RISCV64
open VG.RISCV64.ByteLoad (beWord loadBE32_ok loadLE32_ok contains_byte)
open VG.Proof.Pbkdf2.RISCV64 (Pre Sizes Entry key up tp scr nn sc scR keyR uR tR sc_al sc_sub)
open VG.Proof.Pbkdf2.RISCV64.Sha1 (it)
open VG.Spec.Sha1 (HashValue Word)
open VG.Proof.Pbkdf2.Sha1Words (beWords wIter)

/-- A big-endian word in a region a frame keeps. -/
theorem beWord_frame {rs : List Region} {m m' : Mem} {R : Region} {p : Addr} {off : Nat}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, R.Disjoint r) (hc : R.Contains (p + BitVec.ofNat 64 off) 4) :
    beWord m' p off = beWord m p off := by
  have e (k : Nat) (hk : k < 4) : m' (p + BitVec.ofNat 64 (off + k)) = m (p + BitVec.ofNat 64 (off + k)) :=
    hf _ fun r hr hx => hd r hr _ (contains_byte hc (k := k) hk) hx
  have e0 := e 0 (by decide)
  rw [Nat.add_zero] at e0
  simp only [beWord, e0, e 1 (by decide), e 2 (by decide), e 3 (by decide)]

/-- What the prologue keeps. -/
structure PS (Wi : Nat) (s₀ s : State) : Prop where
  a0 : s.gpr .a0 = key s₀
  a1 : s.gpr .a1 = up s₀
  b : s.gpr B = sc s₀
  tp : s.gpr TP = tp s₀
  frame : Frame [scR Wi s₀] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem PS.keep {Wi : Nat} {s₀ s s' : State} (h : PS Wi s₀ s) (hg : ∀ r, r ≠ T1 → r ≠ KR → s'.gpr r = s.gpr r)
    (hf : Frame [scR Wi s₀] s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    PS Wi s₀ s' :=
  ⟨by rw [hg _ (by decide) (by decide), h.a0], by rw [hg _ (by decide) (by decide), h.a1],
    by rw [hg _ (by decide) (by decide), h.b], by rw [hg _ (by decide) (by decide), h.tp], h.frame.trans hf,
    hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp⟩

section
variable {Wi : Nat} {s₀ : State} (hp : Pre it Wi s₀) (hz : Sizes it Wi)
include hp hz

omit hp in
/-- A word stored in the frame, within `scR`. -/
theorem frame_word {m : Mem} {d : Nat} (hd : d + 4 ≤ 164) (v : Word) :
    Frame [scR Wi s₀] m (m.writeW (sc s₀ + BitVec.ofNat 64 d) v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (fc hz hd)

/-- The first `k` words of the hash value at `so(key)` copied to `fo` in the frame. -/
structure CI (so fo : Nat) (s₁ : State) (k : Nat) (s : State) : Prop where
  ps : PS Wi s₀ s
  done : ∀ j < k, fw s₀ s.mem (fo + 4 * j) = s₀.mem.readW (key s₀ + BitVec.ofNat 64 (so + 4 * j)) 32
  other : ∀ d, d + 4 ≤ fo ∨ fo + 20 ≤ d → d + 4 ≤ 164 → fw s₀ s.mem d = fw s₀ s₁.mem d
  saved : Spill.Saved (sc s₀) s₀.gpr saved s₁.mem → Spill.Saved (sc s₀) s₀.gpr saved s.mem
  gpr : ∀ r, r ≠ T1 → r ≠ KR → s.gpr r = s₁.gpr r

theorem cpLE_ok (so fo : Nat) (hso : so + 20 ≤ 168) (hso4 : so % 4 = 0) (hfo : 104 ≤ fo) (hfo' : fo + 20 ≤ 164)
    (hfa : fo % 4 = 0) (s₁ : State) (h₁ : PS Wi s₀ s₁) :
    WP isa (.block (cpLE so fo)) s₁ (CI (Wi := Wi) (s₀ := s₀) so fo s₁ 5) := by
  refine wp_range_flatMap (M := isa) (CI (Wi := Wi) (s₀ := s₀) so fo s₁) (fun k s hk h => ?_) 5 (Nat.le_refl _) s₁
    ⟨h₁, fun _ h => absurd h (by omega), fun _ _ _ => rfl, id, fun _ _ _ => rfl⟩
  rw [WP.block_append_iff]
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .a0 + BitVec.ofNat 64 (so + 4 * k)) 4 :=
    ⟨keyR it s₀, by rw [h.ps.rd, h.ps.wr, hp.rd, hp.wr]; simp,
      by rw [h.ps.a0]; exact Offset.contains_base _ (by simp only [it, Impl.Pbkdf2.RISCV64.It.S]; omega) (by omega)⟩
  refine WP.mono (loadLE32_ok (s := s) (d := T1) (tmp := KR) (n := .a0) (by decide) (by decide) (by decide)
    (by omega) hin) fun s₂ e₂ => ?_
  subst e₂
  refine wp_sw (a := sc s₀ + BitVec.ofNat 64 (fo + 4 * k)) (by omega)
    (by rw [RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide), h.ps.b])
    (fal s₀ (by omega)) (by exact fin hp hz h.ps.wr (by omega)) fun s₃ u₃ => WP.block_nil ?_
  have val : s.mem.readW (key s₀ + BitVec.ofNat 64 (so + 4 * k)) 32 =
      s₀.mem.readW (key s₀ + BitVec.ofNat 64 (so + 4 * k)) 32 :=
    h.ps.frame.readW (r := keyR it s₀) (Offset.contains_base _ (by simp only [it, Impl.Pbkdf2.RISCV64.It.S]; omega) (by omega))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.k_s) (by decide)
  have m₃ : s₃.mem = s.mem.writeW (sc s₀ + BitVec.ofNat 64 (fo + 4 * k))
      (s₀.mem.readW (key s₀ + BitVec.ofNat 64 (so + 4 * k)) 32) := by
    rw [u₃.mem, RegUpd.gpr_write_self, lo32_ext, RegUpd.mem_write, RegUpd.mem_write, h.ps.a0, val]
  have g₃ : ∀ r, r ≠ T1 → r ≠ KR → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.gpr, RegUpd.gpr_write_of_ne _ _ h1, RegUpd.gpr_write_of_ne _ _ h2]
  refine ⟨h.ps.keep g₃ (by rw [m₃]; exact frame_word hz (by omega) _) u₃.rd u₃.wr u₃.sp, fun j hj => ?_,
    fun d hd hd' => ?_, fun hsv => ?_, fun r h1 h2 => by rw [g₃ r h1 h2, h.gpr r h1 h2]⟩
  · rw [m₃]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [fw_write s₀ _ _ (by omega) (by omega) (by omega)]; exact h.done j hj
    · exact Mem.readW_writeW_self32 _ _ _
  · rw [m₃, fw_write s₀ _ _ (by omega) hd' (by omega)]; exact h.other d hd hd'
  · rw [m₃]; exact saved_write (h.saved hsv) _ (by omega) (by omega)

/-- The first `k` words of `T` copied to the frame. -/
structure TI (s₁ : State) (k : Nat) (s : State) : Prop where
  ps : PS Wi s₀ s
  done : ∀ j < k, fw s₀ s.mem (tO + 4 * j) = (beWords s₀.mem (tp s₀))[j]!
  other : ∀ d, d + 4 ≤ tO → fw s₀ s.mem d = fw s₀ s₁.mem d
  saved : Spill.Saved (sc s₀) s₀.gpr saved s₁.mem → Spill.Saved (sc s₀) s₀.gpr saved s.mem
  gpr : ∀ r, r ≠ T1 → r ≠ KR → s.gpr r = s₁.gpr r

omit hp hz in
theorem beWords_get (m : Mem) (p : Addr) {k : Nat} (hk : k < 5) : (beWords m p)[k]! = beWord m p (4 * k) := by
  rw [getElem!_pos _ k hk]; simp only [beWords, Vector.getElem_ofFn]; rfl

theorem cpT_ok (s₁ : State) (h₁ : PS Wi s₀ s₁) : WP isa (.block cpT) s₁ (TI (Wi := Wi) (s₀ := s₀) s₁ 5) := by
  refine wp_range_flatMap (M := isa) (TI (Wi := Wi) (s₀ := s₀) s₁) (fun k s hk h => ?_) 5 (Nat.le_refl _) s₁
    ⟨h₁, fun _ h => absurd h (by omega), fun _ _ => rfl, id, fun _ _ _ => rfl⟩
  rw [WP.block_append_iff]
  have hc : (tR it s₀).Contains (tp s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
    Offset.contains_base _ (by simp only [it]; omega) (by omega)
  have hin : InRegions (s.rd ++ s.wr) (s.gpr TP + BitVec.ofNat 64 (4 * k)) 4 :=
    ⟨tR it s₀, by rw [h.ps.rd, h.ps.wr, hp.rd, hp.wr]; simp, by rw [h.ps.tp]; exact hc⟩
  refine WP.mono (loadBE32_ok (s := s) (d := T1) (tmp := KR) (n := TP) (by decide) (by decide) (by decide)
    (by omega) hin) fun s₂ e₂ => ?_
  subst e₂
  refine wp_sw (a := sc s₀ + BitVec.ofNat 64 (tO + 4 * k)) (by simp only [tO]; omega)
    (by rw [RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide), h.ps.b])
    (fal s₀ (by simp only [tO]; omega)) (by exact fin hp hz h.ps.wr (by simp only [tO]; omega))
    fun s₃ u₃ => WP.block_nil ?_
  have val : beWord s.mem (s.gpr TP) (4 * k) = (beWords s₀.mem (tp s₀))[k]! := by
    rw [h.ps.tp, beWord_frame h.ps.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.t_s) hc, beWords_get _ _ hk]
  have m₃ : s₃.mem = s.mem.writeW (sc s₀ + BitVec.ofNat 64 (tO + 4 * k)) (beWords s₀.mem (tp s₀))[k]! := by
    rw [u₃.mem, RegUpd.gpr_write_self, lo32_ext, RegUpd.mem_write, RegUpd.mem_write, val]
  have g₃ : ∀ r, r ≠ T1 → r ≠ KR → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.gpr, RegUpd.gpr_write_of_ne _ _ h1, RegUpd.gpr_write_of_ne _ _ h2]
  refine ⟨h.ps.keep g₃ (by rw [m₃]; exact frame_word hz (by simp only [tO]; omega) _) u₃.rd u₃.wr u₃.sp,
    fun j hj => ?_, fun d hd => ?_, fun hsv => ?_, fun r h1 h2 => by rw [g₃ r h1 h2, h.gpr r h1 h2]⟩
  · rw [m₃]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [fw_write s₀ _ _ (by omega) (by simp only [tO]; omega) (by simp only [tO]; omega)]; exact h.done j hj
    · exact Mem.readW_writeW_self32 _ _ _
  · rw [m₃, fw_write s₀ _ _ (by omega) (by simp only [tO] at hd ⊢; omega) (by simp only [tO]; omega)]
    exact h.other d hd
  · rw [m₃]; exact saved_write (h.saved hsv) _ (by simp only [tO]; omega) (by simp only [tO]; omega)

omit hp hz in
theorem A_nodup : ∀ i < 5, ∀ j < 5, i ≠ j → A.getD i .t0 ≠ A.getD j .t0 := by decide
omit hp hz in
theorem A_sp : ∀ k < 5, A.getD k .t0 ≠ .a0 ∧ A.getD k .t0 ≠ .a1 ∧ A.getD k .t0 ≠ B ∧ A.getD k .t0 ≠ TP ∧
    A.getD k .t0 ≠ KR ∧ A.getD k .t0 ≠ N := by decide

/-- The first `k` words of `U` loaded into `A`. -/
structure UI (s₁ : State) (k : Nat) (s : State) : Prop where
  done : ∀ j < k, (s.gpr (A.getD j .t0)).setWidth 32 = (beWords s₀.mem (up s₀))[j]!
  gpr : ∀ r, (∀ j < 5, r ≠ A.getD j .t0) → r ≠ KR → s.gpr r = s₁.gpr r
  mem : s.mem = s₁.mem
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  sp : s.sp = s₁.sp

omit hz in
theorem ldU_ok (s₁ : State) (h₁ : PS Wi s₀ s₁) : WP isa (.block ldU) s₁ (UI (s₀ := s₀) s₁ 5) := by
  refine wp_range_flatMap (M := isa) (UI (s₀ := s₀) s₁) (fun k s hk h => ?_) 5 (Nat.le_refl _) s₁
    ⟨fun _ h => absurd h (by omega), fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  have an := A_sp k hk
  have a1 : s.gpr .a1 = up s₀ := by
    rw [h.gpr _ (fun j hj => (A_sp j hj).2.1.symm) (by decide), h₁.a1]
  have hc : (uR it s₀).Contains (up s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
    Offset.contains_base _ (by simp only [it]; omega) (by omega)
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .a1 + BitVec.ofNat 64 (4 * k)) 4 :=
    ⟨uR it s₀, by rw [h.rd, h.wr, h₁.rd, h₁.wr, hp.rd, hp.wr]; simp, by rw [a1]; exact hc⟩
  refine WP.mono (loadBE32_ok (s := s) (d := A.getD k .t0) (tmp := KR) (n := .a1) an.2.1 (by decide) an.2.2.2.2.1
    (by omega) hin) fun s₂ e₂ => ?_
  subst e₂
  have val : beWord s.mem (s.gpr .a1) (4 * k) = (beWords s₀.mem (up s₀))[k]! := by
    rw [a1, h.mem, beWord_frame h₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.u_s) hc, beWords_get _ _ hk]
  refine ⟨fun j hj => ?_, fun r hr h2 => ?_, by rw [RegUpd.mem_write, RegUpd.mem_write, h.mem],
    by rw [RegUpd.rd_write, RegUpd.rd_write, h.rd], by rw [RegUpd.wr_write, RegUpd.wr_write, h.wr],
    by rw [RegUpd.sp_write, RegUpd.sp_write, h.sp]⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [RegUpd.gpr_write_of_ne _ _ (A_nodup j (by omega) k hk (by omega)),
        RegUpd.gpr_write_of_ne _ _ (A_sp j (by omega)).2.2.2.2.1]
      exact h.done j hj
    · rw [RegUpd.gpr_write_self, lo32_ext, val]
  · rw [RegUpd.gpr_write_of_ne _ _ (hr k hk), RegUpd.gpr_write_of_ne _ _ h2]; exact h.gpr r hr h2

end

/-! ## The whole prologue -/

/-- The final `T`, from the arguments. -/
abbrev Rf (s₀ : State) : HashValue :=
  wIter (Hi s₀) (Ho s₀) (nn s₀) (beWords s₀.mem (up s₀)) (beWords s₀.mem (tp s₀))

theorem save_eq : save = ([.addi B B 7, .logicImm .and B B (-8)] : List Instr) ++ Spill.saveCode B saved := rfl

theorem saved_fits : Spill.Fits saved := by decide

section
variable {Wi : Nat} {s₀ : State} (hp : Pre it Wi s₀) (hz : Sizes it Wi)
include hp hz

theorem pro_ok {e : State} (he : Entry s₀ e) : WP isa (.block (save ++ setup)) e (LI Wi s₀ (Rf s₀) (nn s₀)) := by
  rw [save_eq, List.append_assoc, WP.block_append_iff]
  refine WP.mono (Q := fun (e₁ : State) => e₁ = e.write B (sc s₀)) ?_ fun e₁ he₁ => ?_
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addi (show imm12 7 by decide),
      exec_logicImm (show imm12 (-8) by decide), RegUpd.gpr_write_self, RegUpd.write_write, Align.align_eq,
      Option.some.injEq, exists_eq_left']
    rw [he.other _ (by decide)]; rfl
  subst he₁
  have b₁ : (e.write B (sc s₀)).gpr B = sc s₀ := RegUpd.gpr_write_self _ _ _
  have g₁ (r : Reg) (hr : r ≠ B) : (e.write B (sc s₀)).gpr r = e.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine Spill.save_ok (b := B) (l := saved) (by rw [b₁]; exact sc_al) (by decide) (fun q hq => ?_) ?_
  · rw [b₁]; exact fin hp hz (by rw [RegUpd.wr_write, he.wr]) (by have := saved_bound q hq; omega)
  generalize hs₂ : ({ (e.write B (sc s₀)) with
    mem := Spill.saveMem (e.write B (sc s₀)).mem ((e.write B (sc s₀)).gpr B) (e.write B (sc s₀)).gpr saved } :
      State) = s₂
  have gpr₂ (r : Reg) (hr : r ≠ B) : s₂.gpr r = e.gpr r := by rw [← hs₂]; exact g₁ r hr
  have b₂ : s₂.gpr B = sc s₀ := by rw [← hs₂]; exact b₁
  have mem₂ : s₂.mem = Spill.saveMem s₀.mem (sc s₀) (e.write B (sc s₀)).gpr saved := by
    rw [← hs₂]; show Spill.saveMem _ _ _ _ = _; rw [b₁, RegUpd.mem_write, he.mem]
  have ps₂ : PS Wi s₀ s₂ := by
    refine ⟨by rw [gpr₂ _ (by decide), he.other _ (by decide)], by rw [gpr₂ _ (by decide), he.other _ (by decide)],
      b₂, by rw [gpr₂ _ (by decide), he.other _ (by decide)]; rfl, ?_, by rw [← hs₂]; exact he.rd,
      by rw [← hs₂]; exact he.wr, by rw [← hs₂]; exact he.sp⟩
    rw [mem₂]
    refine (Spill.saveMem_frame_base (n := 104) (fun q hq => (saved_bound q hq).2) (by decide) _ _ _).sub
      fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨scR Wi s₀, by simp, ?_⟩
    have := sc_sub (Wi := Wi) (s₀ := s₀) (a := 0) (n := 104) (by have := hz.fits; simp only [it] at this; omega)
    rwa [Proof.Pbkdf2.RISCV64.sc0] at this
  have sv₂ : Spill.Saved (sc s₀) s₀.gpr saved s₂.mem := by
    rw [mem₂]
    intro q hq
    rw [Spill.saveMem_saved saved_fits _ _ _ q hq]
    have : q.1 ≠ B ∧ q.1 ≠ .a2 := by revert q; decide
    rw [g₁ _ this.1, he.other _ this.2]
  -- The four parts of the setup.
  unfold setup
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (cpLE_ok hp hz 0 hiO (by decide) (by decide) (by decide) (by decide) (by decide) s₂ ps₂)
    fun s₃ h₃ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cpLE_ok hp hz 84 hoO (by decide) (by decide) (by decide) (by decide) (by decide) s₃ h₃.ps)
    fun s₄ h₄ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cpT_ok hp hz s₄ h₄.ps) fun s₅ h₅ => ?_
  refine WP.mono (ldU_ok hp s₅ h₅.ps) fun s₆ h₆ => ?_
  have m₆ : s₆.mem = s₅.mem := h₆.mem
  have keepA (r : Reg) (hA : ∀ j < 5, r ≠ A.getD j .t0) (h1 : r ≠ T1) (h2 : r ≠ KR) : s₆.gpr r = s₂.gpr r := by
    rw [h₆.gpr r hA h2, h₅.gpr r h1 h2, h₄.gpr r h1 h2, h₃.gpr r h1 h2]
  have notA (r : Reg) (h : r = B ∨ r = N ∨ r = TP) : ∀ j < 5, r ≠ A.getD j .t0 := fun j hj e => by
    rcases h with rfl | rfl | rfl
    · exact (A_sp j hj).2.2.1 e.symm
    · exact (A_sp j hj).2.2.2.2.2 e.symm
    · exact (A_sp j hj).2.2.2.1 e.symm
  refine ⟨?_, ?_, ?_, ⟨beWords s₀.mem (up s₀), beWords s₀.mem (tp s₀), h₆.done, fun k hk => by
      rw [m₆]; exact h₅.done k hk, rfl⟩, ⟨fun k hk => ?_, fun k hk => ?_⟩, ?_, by rw [h₆.rd]; exact h₅.ps.rd,
    by rw [h₆.wr]; exact h₅.ps.wr, by rw [h₆.sp]; exact h₅.ps.sp, by rw [m₆]; exact h₅.ps.frame⟩
  · rw [keepA _ (notA _ (.inl rfl)) (by decide) (by decide), b₂]
  · rw [keepA _ (notA _ (.inr (.inl rfl))) (by decide) (by decide), gpr₂ _ (by decide)]; exact he.a2
  · rw [keepA _ (notA _ (.inr (.inr rfl))) (by decide) (by decide), gpr₂ _ (by decide), he.other _ (by decide)]; rfl
  · rw [m₆, h₅.other _ (by simp only [hiO, tO]; omega), h₄.other _ (.inl (by simp only [hiO, hoO]; omega))
      (by simp only [hiO]; omega), h₃.done k hk, Nat.zero_add, getElem!_pos _ k hk, Proof.Sha1.StateMem.stateAt_get _ _ hk]
  · rw [m₆, h₅.other _ (by simp only [hoO, tO]; omega), h₄.done k hk, getElem!_pos _ k hk,
      Proof.Sha1.StateMem.stateAt_get _ _ hk, Offset.add_add]
  · rw [m₆]; exact h₅.saved (h₄.saved (h₃.saved sv₂))

end

end VG.Proof.Pbkdf2.Sha1.RISCV64
