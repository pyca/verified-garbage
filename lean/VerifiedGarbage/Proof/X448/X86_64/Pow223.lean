import VerifiedGarbage.Proof.X448.X86_64.Inv
import VerifiedGarbage.Proof.Framework.X86_64.Spill
import VerifiedGarbage.Proof.Framework.X86_64.CallInline

/-!
# X448 on x86-64: the addition chain as a function

`pow223Fn` (`vg_gf448_r64_pow223`) saves `rbx`, `rbp` and `r12`–`r15` at
`SAVE` (bytes 1472–1519, which the chain never writes: it writes only the
slots 14–21 and the product's words), runs `chain223` of slot 12, and
restores them: it changes only `rax`, `rcx`, `rdx` and `r8`–`r11` and the
bytes `[960, 1648)`, and the slots as `chain223` does (`pow223Fn_ok`): slots 20
and 21 end as `c222` and `c223` of slot 12 (`chainEnv_20`, `chainEnv_21`).
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64 VG.Proof.X448

theorem powSaved_lt : ∀ rd ∈ powSaved, 1472 ≤ rd.2 ∧ rd.2 + 8 ≤ 1520 := by decide

/-- The registers the function changes. -/
def powClob : List Reg := [.rax, .rcx, .rdx, .r8, .r9, .r10, .r11]

theorem chainEnv_20 (e : Env) : chainEnv 12 e 20 = c222 (e 12) := by
  simp only [chainEnv, opMul, opSqn, Function.update_apply, c222]
  rfl

theorem chainEnv_21 (e : Env) : chainEnv 12 e 21 = c223 (e 12) := by
  simp only [↓reduceIte, chainEnv, opMul, opSqn, Function.update_apply, c223, c222]
  rfl

/-- `vg_gf448_r64_pow223`: what it keeps and computes. -/
theorem pow223Fn_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa pow223Fn s fun s' =>
      (∀ r, r ∉ powClob → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Outside base 960 688 s.mem s'.mem ∧ E s'.mem base = chainEnv 12 (E s.mem base) := by
  refine WP.seq (WP.mono (Spill.save_ok .rdi powSaved s fun p hp => ?_) fun s₁ ⟨g₁, rd₁, wr₁, m₁⟩ => ?_)
  · have := powSaved_lt p hp
    rw [hs.rdi]; exact ⟨_, hs.wr, contains_sc (by omega)⟩
  rw [hs.rdi] at m₁
  have hs₁ : Scr s₁ base := ⟨by rw [g₁]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
  have o₁ : Outside base 1472 48 s.mem s₁.mem := by
    rw [m₁]
    intro x hx
    refine Spill.saveMem_frame (r := ⟨base + BitVec.ofNat 64 1472, 48⟩) _ _ _ _
      (fun p hp => Offset.contains base (powSaved_lt p hp).1 (by have := powSaved_lt p hp; omega)
        (by decide)) x fun r hr hx' => ?_
    rw [List.mem_singleton.mp hr] at hx'
    simp only [Region.Contains] at hx'
    have := (Offset.lt_iff x base (d := 1472) (n := 48) (by decide)).mp (by omega)
    simp only [ofs] at hx
    omega
  have sv₁ : Spill.Saved s₁.mem base s.gpr powSaved := by
    rw [m₁]; exact Spill.saveMem_saved _ _ _ _ (by decide)
  refine WP.seq (WP.mono (chain223_spec baseline_ok base 12 s₁ hs₁) fun s₂ ⟨k₂, e₂⟩ => ?_)
  have hs₂ := k₂.scr hs₁
  have sv₂ : Spill.Saved s₂.mem base s.gpr powSaved := fun p hp => by
    have := powSaved_lt p hp
    exact (k₂.mem.word (d := p.2) (Or.inr (by omega)) (Or.inl (by simp only [ACC]; omega)) (by omega)).trans
      (sv₁ p hp)
  refine WP.mono (Spill.restore_ok .rdi powSaved s.gpr s₂ (by decide) (fun p hp => ?_)
    (by rw [hs₂.rdi]; exact sv₂)) fun s₃ ⟨h₁, h₂, m₃, rd₃, wr₃⟩ => ?_
  · have := powSaved_lt p hp
    rw [hs₂.rdi]; exact ⟨_, List.mem_append_right _ hs₂.wr, contains_sc (by omega)⟩
  have e₁ : E s₁.mem base = E s.mem base := by
    funext i
    have := i.isLt
    show toFe (mv s₁.mem base (slot i.val) 7) = toFe (mv s.mem base (slot i.val) 7)
    rw [o₁.mv (Or.inl (by simp only [slot]; omega)) (by simp only [slot]; omega)]
  refine ⟨fun r hr => ?_, rd₃.trans (k₂.rd.trans rd₁), wr₃.trans (k₂.wr.trans wr₁), ?_, ?_⟩
  · by_cases hm : r ∈ powSaved.map Prod.fst
    · exact h₁ r hm
    · rw [h₂ r hm, k₂.gpr r (by revert hr hm; cases r <;> decide) (by revert hm; cases r <;> decide), g₁]
  · intro x hx
    rw [m₃, k₂.out x hx, o₁ x (by omega)]
  · rw [m₃, e₂, e₁]

/-! ## Keeping words across the call -/

/-- Writing back the 8 bytes just read changes nothing. -/
theorem writeW_readW64 (m : Mem) (a : Addr) : m.writeW a (m.readW a 64) = m := by
  funext x
  by_cases h : (x - a).toNat < 8
  · simp only [Mem.writeW, Mem.write, Mem.readW, show (64 : Nat) / 8 = 8 from rfl, BitVec.setWidth_eq,
      h, ite_true]
    rw [Mem.extractLsb'_read m a h, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  · simp only [Mem.writeW, Mem.write, show (64 : Nat) / 8 = 8 from rfl, h, ite_false]

/-- Loads of the words at the offsets of `l` into its registers (distinct, and not `rdi`). -/
theorem loadsAt_ok {base : Addr} : ∀ (l : List (Reg × Nat)) (s : State), Scr s base →
    (∀ p ∈ l, p.1 ≠ .rdi ∧ p.2 + 8 ≤ 8192) → (l.map Prod.fst).Nodup →
    WP isa (.block (l.map fun (r, d) => .mov r (.mem (sc d)))) s fun s' =>
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ l.map Prod.fst → s'.gpr r = s.gpr r) ∧
      ∀ p ∈ l, s'.gpr p.1 = word s.mem base p.2
  | [], _, _, _, _ => WP.block_nil ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ h => by cases h⟩
  | (r, d) :: l, s, hs, hl, hnd => by
    obtain ⟨hr, hd⟩ := hl (r, d) List.mem_cons_self
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [List.map_cons, WP.block_cons_iff]
    refine ⟨s.setReg r (word s.mem base d), by
      simp only [exec, readSrc_sc hs (d := d) hd, Option.map_some], ?_⟩
    have hs1 : Scr (s.setReg r (word s.mem base d)) base :=
      ⟨by rw [RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hr)]; exact hs.rdi, hs.wr, hs.nowrap⟩
    refine WP.mono (loadsAt_ok l _ hs1 (fun p hp => hl p (List.mem_cons_of_mem _ hp)) hnd.2)
      fun s' ⟨m', rd', wr', g', v'⟩ => ⟨m', rd', wr', fun r' hr' => ?_, fun p hp => ?_⟩
    · simp only [List.map_cons, List.mem_cons, not_or] at hr'
      rw [g' r' hr'.2, RegUpd.gpr_setReg_of_ne _ _ hr'.1]
    · rcases List.mem_cons.mp hp with rfl | hp
      · rw [g' _ hnd.1]; exact RegUpd.gpr_setReg_self _ _ _
      · rw [v' p hp]; rfl

/-- Stores, at the offsets of `l`, of its registers, which hold the words there: nothing
changes. -/
theorem storesAt_ok {base : Addr} : ∀ (l : List (Reg × Nat)) (s : State), Scr s base →
    (∀ p ∈ l, p.2 + 8 ≤ 8192 ∧ s.gpr p.1 = word s.mem base p.2) →
    WP isa (.block (l.map fun (r, d) => .store (sc d) r)) s fun s' => s' = s
  | [], s, _, _ => WP.block_nil rfl
  | (r, d) :: l, s, hs, hl => by
    obtain ⟨hd, hv⟩ := hl (r, d) List.mem_cons_self
    rw [List.map_cons, WP.block_cons_iff]
    refine ⟨s, by
      have hw := hs.write (d := d) (n := 8) hd
      simp only [exec, ea_sc, hs.rdi, State.store64, hw, ite_true, hv, word, writeW_readW64], ?_⟩
    exact storesAt_ok l s hs fun p hp => hl p (List.mem_cons_of_mem _ hp)

theorem pow223Keep_inline (keep : List Nat) : (pow223Keep keep).inline =
    .seq (.block ((keepRegs.zip keep).map fun (r, d) => .mov r (.mem (sc d))))
      (.seq pow223Fn (.block ((keepRegs.zip keep).map fun (r, d) => .store (sc d) r))) := rfl

theorem keepRegs_zip_fst (keep : List Nat) : ∀ p ∈ keepRegs.zip keep, p.1 = .r12 ∨ p.1 = .r13 := by
  intro p hp
  have := List.of_mem_zip hp
  simpa [keepRegs] using this.1

/-- The call, keeping the words at `keep` (outside the function's bytes): as `pow223Fn_ok`,
but for `r12` and `r13`. -/
theorem pow223Keep_ok (keep : List Nat) (hk : ∀ d ∈ keep, d + 8 ≤ 960 ∨ (1648 ≤ d ∧ d + 8 ≤ 8192))
    {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (pow223Keep keep).inline s fun s' =>
      (∀ r, r ∉ powClob → r ≠ .r12 → r ≠ .r13 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ Outside base 960 688 s.mem s'.mem ∧ E s'.mem base = chainEnv 12 (E s.mem base) := by
  have hl : ∀ p ∈ keepRegs.zip keep, p.2 + 8 ≤ 960 ∨ (1648 ≤ p.2 ∧ p.2 + 8 ≤ 8192) :=
    fun p hp => hk p.2 (List.of_mem_zip hp).2
  have hnd : ((keepRegs.zip keep).map Prod.fst).Nodup := by
    rcases keep with _ | ⟨d, _ | ⟨e, _⟩⟩ <;> simp [keepRegs]
  rw [pow223Keep_inline]
  refine WP.seq (WP.mono (loadsAt_ok _ s hs (fun p hp => ⟨by rcases keepRegs_zip_fst keep p hp with h | h <;>
      rw [h] <;> decide, by rcases hl p hp with h | h <;> omega⟩) hnd)
    fun s₁ ⟨m₁, rd₁, wr₁, g₁, v₁⟩ => ?_)
  have hs₁ : Scr s₁ base := ⟨(g₁ _ (by rcases keep with _ | ⟨d, _ | ⟨e, _⟩⟩ <;> simp [keepRegs])).trans hs.rdi,
    wr₁ ▸ hs.wr, hs.nowrap⟩
  refine WP.seq (WP.mono (pow223Fn_ok hs₁) fun s₂ ⟨g₂, rd₂, wr₂, o₂, e₂⟩ => ?_)
  have hs₂ : Scr s₂ base := ⟨(g₂ _ (by decide)).trans hs₁.rdi, wr₂ ▸ hs₁.wr, hs₁.nowrap⟩
  refine WP.mono (storesAt_ok _ s₂ hs₂ fun p hp => ⟨by rcases hl p hp with h | h <;> omega, ?_⟩)
    fun s₃ e₃ => ?_
  · rw [g₂ _ (by rcases keepRegs_zip_fst keep p hp with h | h <;> rw [h] <;> decide), v₁ p hp,
      o₂.word (by rcases hl p hp with h | h <;> omega) (by rcases hl p hp with h | h <;> omega), m₁]
  · subst e₃
    refine ⟨fun r hr h12 h13 => ?_, rd₂.trans rd₁, wr₂.trans wr₁, ?_, ?_⟩
    · rw [g₂ r hr, g₁ r (fun h => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
        rcases keepRegs_zip_fst keep p hp with h | h
        · exact h12 h
        · exact h13 h)]
    · rw [← m₁]; exact o₂
    · rw [e₂, m₁]

end VG.Proof.X448.X86_64
