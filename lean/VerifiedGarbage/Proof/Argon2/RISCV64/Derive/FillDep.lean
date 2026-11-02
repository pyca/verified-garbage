module

public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillState
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Initial
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.MemoryInit
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Body
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Scratch
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Locals
public import VerifiedGarbage.Proof.Argon2.Contract

/-!
# Argon2 on RISC-V: the filling state, and data-dependent addressing

`FS.keep`: what keeps the filling state (`FS.of_only`, `FS.store`,
`FS.frame`). `dependentWord_ok`: J₁ and J₂, the halves of the previous
block's first doubleword, to the frame (`Rand`).
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_mv wp_ld wp_sd wp_xor)
open VG.Proof.Argon2.RISCV64 (wp_sll wp_srl wp_srlw wp_mul wp_mulhu wp_or wp_and wp_lwu wp_sw)
open VG.RISCV64.Wp (Upd Mupd)
open VG.Spec.Argon2 (Block zeroBlock FillState)
open VG.Proof.Argon2 (matrixCell Represents)
open VG.Impl.Argon2.RISCV64.Derive (j1Off j2Off)

/-- Doubleword `j` of a block. -/
theorem blockAt_get (m : Mem) (p : Addr) {j : Nat} (hj : j < 128) :
    (blockAt m p)[j] = m.readW (p + BitVec.ofNat 64 (8 * j)) 64 := by
  simp only [blockAt, Vector.getElem_ofFn, Mem.readW, BitVec.setWidth_eq]

/-- J₁ and J₂, the halves of the random word `w`, in the frame. -/
def Rand (s₀ s : State) (w : BitVec 64) : Prop :=
  lw s₀ s j1Off = w &&& 0xffffffff ∧ lw s₀ s j2Off = w >>> 32

theorem lo_ext (w : BitVec 64) : (w.setWidth 32).setWidth 64 = w &&& 0xffffffff := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and]
  rw [show (0xffffffff : BitVec 64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have := Nat.mod_lt w.toNat (show 0 < 2 ^ 32 by decide)
  omega

theorem hi_ext (w : BitVec 64) : (w.extractLsb' 32 32).setWidth 64 = w >>> 32 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  have := w.isLt
  have h32 : w.toNat / 2 ^ 32 < 2 ^ 32 := by omega
  rw [Nat.mod_eq_of_lt h32, Nat.mod_eq_of_lt (by omega)]

theorem FS.keep {s₀ s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (it : Inv s₀ t)
    (hl : ∀ d, 184 ≤ d → d + 8 ≤ 248 → lw s₀ t d = lw s₀ s d)
    (hc : blockAt t.mem (scrP s₀ + BitVec.ofNat 64 2048) = blockAt s.mem (scrP s₀ + BitVec.ofNat 64 2048))
    (hm : ∀ k < (prm s₀).blocks,
      blockAt t.mem (matrixCell (memP s₀) k) = blockAt s.mem (matrixCell (memP s₀) k)) :
    FS s₀ pass slice lane index ctr st t := by
  refine ⟨it, Prm.of_lw h.pr fun d h₁ h₂ => hl d (by omega) (by omega),
    h.pos.of_lw fun d h₁ h₂ => hl d (by omega) (by omega), ?_, Represents.keep h.mem hm⟩
  obtain ⟨c0, c1, c2 | ⟨c3, c4⟩⟩ := h.cache
  · exact ⟨c0, by rw [hl _ (by decide) (by decide)]; exact c1, .inl c2⟩
  · exact ⟨c0, by rw [hl _ (by decide) (by decide)]; exact c1, .inr ⟨c3, by rw [hc]; exact c4⟩⟩

/-- A step that writes only registers the invariant does not name keeps the
filling state. -/
theorem FS.of_only {s₀ s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) {ds : List Reg} (o : Only ds s t)
    (hd : ∀ r ∈ ds, Free r := by decide) : FS s₀ pass slice lane index ctr st t :=
  h.keep (h.inv.only o hd) (fun d _ _ => lw_mem o.mem d) (by rw [o.mem]) fun _ _ => by rw [o.mem]

/-- Regions a step of the filling loops may write without changing the filling state. -/
def Outside (s₀ : State) (r : Region) : Prop :=
  r.Disjoint ⟨at' s₀ 184, 64⟩ ∧ r.Disjoint ⟨scrP s₀ + BitVec.ofNat 64 2048, 1024⟩ ∧ r.Disjoint (memR s₀)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem FS.frame {s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (it : Inv s₀ t) {rs : List Region}
    (f : Frame rs s.mem t.mem) (ho : ∀ r ∈ rs, Outside s₀ r) : FS s₀ pass slice lane index ctr st t := by
  refine h.keep it (fun d h₁ h₂ => ?_) ?_ fun k hk => ?_
  · refine f.readW (r := ⟨E s₀ + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (fun r hr => (ho r hr).1.symm.sub_left ?_) (by decide)
    exact Offset.sub _ (by omega) (by omega)
  · exact blockAt_keep f fun r hr => (ho r hr).2.1.symm
  · have hk' : k < blocksN s₀ := by rw [hp.blocks]; exact hk
    exact blockAt_keep f fun r hr => (ho r hr).2.2.symm.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hk')

/-- A store to the frame outside the filling state's variables keeps the
filling state. -/
theorem FS.store {s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (it : Inv s₀ t) {d : Nat} (hd : 248 ≤ d)
    (hd' : d + 8 ≤ 320) {v : BitVec 64} (hm : t.mem = s.mem.writeW (E s₀ + BitVec.ofNat 64 d) v) :
    FS s₀ pass slice lane index ctr st t := by
  refine h.frame hp it (rs := [⟨E s₀ + BitVec.ofNat 64 d, 8⟩]) (by rw [hm]; exact frame_loc v)
    fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  refine ⟨Offset.disjoint _ (by omega) (by omega) (by omega), ?_, ?_⟩
  · exact (stk_disj hp (by omega) (scrR s₀) (by simp)).sub_right (scr_sub (by decide))
  · exact stk_disj hp (by omega) (memR s₀) (by simp)

theorem cell_al (c : Nat) {o : Nat} (ho : o % 4 = 0) :
    (matrixCell (memP s₀) c + BitVec.ofNat 64 o).toNat % 4 = 0 := by
  rw [matrixCell, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact al_add (by decide) (.inr (by have := hp.mem_al; omega)) (by omega)

theorem outside_scr {o n : Nat} (h : o + n ≤ 2048 ∨ (3072 ≤ o ∧ o + n ≤ 16384)) :
    Outside s₀ ⟨scrP s₀ + BitVec.ofNat 64 o, n⟩ := by
  have sub : Region.Sub ⟨scrP s₀ + BitVec.ofNat 64 o, n⟩ (scrR s₀) := Offset.sub_base _ (by omega)
  refine ⟨((stk_disj hp (d := 184) (n := 64) (by decide) (scrR s₀) (by simp)).symm.sub_left sub),
    Offset.disjoint _ (by omega) (by omega) (by omega), hp.mem_scr.symm.sub_left sub⟩

/-- `dependentWord`: J₁ and J₂ are the halves of the previous block's first doubleword. -/
theorem dependentWord_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) :
    WP isa Impl.Argon2.RISCV64.Derive.dependentWord s fun t => FS s₀ pass slice lane index ctr st t ∧
      Rand s₀ t (blockAt s.mem (matrixCell (memP s₀) (lane * (prm s₀).laneLen +
        (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) % (prm s₀).laneLen)))[0] := by
  have L8 := laneLen_ge hp
  obtain ⟨cl, cf⟩ := cell_fits hp hl
    (col := (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) % (prm s₀).laneLen)
    (Nat.mod_lt _ (by omega))
  unfold Impl.Argon2.RISCV64.Derive.dependentWord
  refine WP.seq ((prevPointer_ok hp h.inv h.pr h.pos hl hs hi).mono fun s₁ ⟨a₁, k₁⟩ => ?_)
  generalize (lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) %
    (prm s₀).laneLen) = c at cl cf a₁ ⊢
  have h₁ := h.of_only k₁
  have hb := blocks_lt' hp
  have inP : ∀ o, o + 4 ≤ 1024 → (memR s₀).Contains (matrixCell (memP s₀) c + BitVec.ofNat 64 o) 4 :=
    fun o ho => by
      rw [matrixCell, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact Offset.contains_base _ (by omega) (by omega)
  have mW : ∀ t, Inv s₀ t → memR s₀ ∈ t.wr := fun t it => by rw [it.wr]; exact mem_mem hp
  have hb := blocks_lt' hp
  have c0 : (memR s₀).Contains (matrixCell (memP s₀) c) 4 :=
    Offset.contains_base (memP s₀) (d := c * 1024) (n := 4) (k := blocksN s₀ * 1024)
      (Nat.le_trans (Nat.add_le_add_left (by decide) _) cf) (by omega)
  refine wp_lwu (a := matrixCell (memP s₀) c) (by decide) (by rw [a₁]; simp [matrixCell])
    (cell_al hp c (o := 0) (by decide) |> fun h => by simpa using h)
    ⟨_, List.mem_append_right _ (mW _ h₁.inv), c0⟩ fun s₂ u₂ => ?_
  have h₂ := h₁.of_only (Only.of_upd u₂)
  refine wp_stloc h₂.inv (d := j1Off) (by decide) fun s₃ i₃ v₃ o₃ g₃ m₃ => ?_
  have h₃ := h₂.store hp i₃ (d := j1Off) (by decide) (by decide) m₃
  refine wp_lwu (a := matrixCell (memP s₀) c + BitVec.ofNat 64 4) (by decide)
    (by rw [g₃, u₂.other _ (by decide), a₁]; rfl) (cell_al hp c (by decide))
    ⟨_, List.mem_append_right _ (mW _ h₃.inv), inP 4 (by decide)⟩ fun s₄ u₄ => ?_
  have h₄ := h₃.of_only (Only.of_upd u₄)
  refine wp_stloc h₄.inv (d := j2Off) (by decide) fun t it vt ot gt mt => WP.block_nil ⟨?_, ?_, ?_⟩
  · exact h₄.store hp it (d := j2Off) (by decide) (by decide) mt
  · have w0 : s.mem.readW (matrixCell (memP s₀) c) 64 = (blockAt s.mem (matrixCell (memP s₀) c))[0] := by
      rw [blockAt_get _ _ (by decide)]; simp
    rw [ot j1Off (by decide) (by decide), lw_mem u₄.mem, v₃, u₂.gpr, k₁.mem, Mem.readW_lo32 w0, lo_ext]
  · have sub : Region.Sub ⟨matrixCell (memP s₀) c, 8⟩ (memR s₀) :=
      Offset.sub_base (memP s₀) (d := c * 1024) (n := 8) (k := blocksN s₀ * 1024)
        (Nat.le_trans (Nat.add_le_add_left (by decide) _) cf)
    have w0 : s₃.mem.readW (matrixCell (memP s₀) c) 64 = (blockAt s.mem (matrixCell (memP s₀) c))[0] := by
      rw [m₃, (frame_loc _).readW (r := ⟨matrixCell (memP s₀) c, 8⟩) (Region.contains_self _ _)
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (loc_disj hp (d := j1Off) (by decide) (memR s₀) (by simp)).symm.sub_left sub)
        (by decide), u₂.mem, k₁.mem, blockAt_get _ _ (by decide)]
      simp
    rw [vt, u₄.gpr]
    exact (congrArg (BitVec.setWidth 64) (Mem.readW_hi32 w0)).trans (hi_ext _)

end

end VG.Proof.Argon2.RISCV64.Derive
