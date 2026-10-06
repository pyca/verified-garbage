import VerifiedGarbage.Proof.Aes.X86.AesNi.Imc
import VerifiedGarbage.Proof.Aes.X86.BlocksContract

/-!
# AES-NI on x86 (32-bit): the loops over whole blocks

The loops of `vg_aes_encrypt_blocks_aesni` and `vg_aes_decrypt_blocks_aesni`
are proven once for any transformation `f` of a list of block registers
that computes `F` on each, given what it needs of the state (`KP`, which
the loops keep): `aes` and `aesDec`. After `c` blocks, the first `c` data
blocks hold `F` of the original ones (`Inv`); the six-block and one-block
bodies are the same code for different lists of registers (`blocks_ok`).
-/

namespace VG.Proof.Aes.X86.AesNi

open VG VG.X86 VG.X86.RegUpd
open VG.Impl.Aes.X86.AesNi (at_ regs6 loadData storeData blocks6 blocks1 blocksTail)
open VG.Proof.Aes.X86 (BPre bSchP bRounds bDatP bN bScrP bSchR bDatR bScrR bArgR bRetR reg32 in_rd)

/-! ## Blocks as states -/

theorem stateAt_eq (m : Mem) (a : Addr) : Spec.Aes.stateAt m a = st (m.readW a 128) :=
  st_ext fun i hi => by
    rw [getD_st _ hi, VG.Proof.Gcm.X86.byte_readW _ _ hi]
    simp [Spec.Aes.stateAt, Vector.getD, hi]

theorem loadData_ok (regs : List XReg) (j : Nat) (s : State) (hnd : regs.Nodup)
    (hin : ∀ k < regs.length, InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) (16 * (j + k))) 16) :
    WP isa (.block (loadData regs j)) s fun s' =>
      (∀ k (h : k < regs.length),
        st (s'.xmm regs[k]) = Spec.Aes.stateAt s.mem (addr (s.gpr .esi) (16 * (j + k)))) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ regs → s'.xmm r = s.xmm r) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  | cons b bs ih =>
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    simp only [List.length_cons] at hin
    rw [loadData, ← List.singleton_append, WP.block_append_iff]
    have hin0 := hin 0 (by omega)
    rw [Nat.add_zero] at hin0
    refine WP.mono (Q := fun s₁ => s₁ = s.setXmm b (s.mem.readW (addr (s.gpr .esi) (16 * j)) 128)) ?_
      fun s₁ e₁ => ?_
    · apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.load128, ea_at, hin0,
        ↓reduceIte, Option.map_some, Option.some.injEq, exists_eq_left']
    subst e₁
    refine WP.mono (ih (j + 1) _ (List.nodup_cons.mp hnd).2 (fun k hk => by
        rw [rd_setXmm, wr_setXmm, gpr_setXmm, show j + 1 + k = j + (k + 1) by omega]
        exact hin (k + 1) (by omega)))
      fun s' ⟨hb, g, m, rd, wr, hx⟩ => ?_
    rw [gpr_setXmm, mem_setXmm] at hb
    refine ⟨fun k hk => ?_, g, m, rd, wr, fun r hr => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [hx b hbs, xmm_setXmm_self, stateAt_eq]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [hb k (by simpa using hk), show j + 1 + k = j + (k + 1) by omega]
    · simp only [List.mem_cons, not_or] at hr
      rw [hx r hr.2, xmm_setXmm_of_ne _ _ hr.1]

theorem addr_sep {p : BitVec 32} {a b n : Nat} (h : a + 16 ≤ b ∨ b + 16 ≤ a) (ha : p.toNat + a + 16 ≤ 2 ^ 32)
    (hb : p.toNat + b + 16 ≤ 2 ^ 32) (_hn : n = 16) : Mem.Sep (addr p a) n (addr p b) n := by
  subst _hn
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.sep _ h (by omega) (by omega)

theorem storeData_ok (regs : List XReg) (j : Nat) (s : State)
    (hin : ∀ k < regs.length, InRegions s.wr (addr (s.gpr .esi) (16 * (j + k))) 16)
    (hw : (s.gpr .esi).toNat + 16 * (j + regs.length) ≤ 2 ^ 32) :
    WP isa (.block (storeData regs j)) s fun s' =>
      (∀ k (h : k < regs.length), Spec.Aes.stateAt s'.mem (addr (s.gpr .esi) (16 * (j + k))) =
        st (s.xmm regs[k])) ∧
      Frame [⟨addr (s.gpr .esi) (16 * j), 16 * regs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, s'.xmm r = s.xmm r) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl, fun _ => rfl⟩
  | cons b bs ih =>
    simp only [List.length_cons] at hin hw
    rw [storeData, ← List.singleton_append, WP.block_append_iff]
    have hin0 := hin 0 (by omega)
    rw [Nat.add_zero] at hin0
    let s₁ : State := { s with mem := s.mem.writeW (addr (s.gpr .esi) (16 * j)) (s.xmm b) }
    refine WP.mono (Q := fun t => t = s₁) ?_ fun t e => ?_
    · apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.store128, ea_at, hin0,
        ↓reduceIte, Option.some.injEq, exists_eq_left']
      rfl
    subst e
    have ha0 : addr (s.gpr .esi) (16 * j) = (s.gpr .esi).setWidth 64 + BitVec.ofNat 64 (16 * j) :=
      addr_eq (by omega)
    refine WP.mono (ih (j + 1) s₁ (fun k hk => by
        rw [show j + 1 + k = j + (k + 1) by omega]; exact hin (k + 1) (by omega))
      (by show (s.gpr .esi).toNat + _ ≤ _; omega)) fun s' ⟨hb, hf, g, rd, wr, hx⟩ => ?_
    let R₀ : Region := ⟨(s.gpr .esi).setWidth 64 + BitVec.ofNat 64 (16 * j), 16 * (bs.length + 1)⟩
    -- The blocks after the first: apart from it, and within the whole run.
    have hrest : ∀ r ∈ [(⟨addr (s₁.gpr .esi) (16 * (j + 1)), 16 * bs.length⟩ : Region)],
        Region.Disjoint ⟨(s.gpr .esi).setWidth 64 + BitVec.ofNat 64 (16 * j), 16⟩ r ∧ Region.Sub r R₀ := by
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      by_cases hl : bs.length = 0
      · rw [hl]
        exact ⟨fun a _ h => by simp [Region.Contains] at h, fun a h => by simp [Region.Contains] at h⟩
      · rw [show s₁.gpr .esi = s.gpr .esi from rfl, addr_eq (by omega)]
        exact ⟨Offset.disjoint _ (.inl (by omega)) (by omega) (by omega), Offset.sub _ (by omega) (by omega)⟩
    refine ⟨fun k hk => ?_, ?_, g, rd, wr, hx⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [stateAt_eq, ha0, hf.readW (Region.contains_self _ _) (fun r hr => (hrest r hr).1) (by decide),
          ← ha0]
        exact congrArg st (Mem.readW_writeW_self _ _ 16 _ (by decide))
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [show j + (k + 1) = j + 1 + k by omega]
        exact hb k (by simpa using hk)
    · rw [ha0]
      have hm : R₀ ∈ [R₀] := List.mem_singleton_self _
      refine (Frame.writeW (Frame.refl _ s.mem) hm (s.xmm b) ?_).trans
        (hf.sub fun r hr => ⟨_, hm, (hrest r hr).2⟩)
      rw [ha0]; exact Offset.contains _ (Nat.le_refl _) (by omega) (by omega)

end VG.Proof.Aes.X86.AesNi
