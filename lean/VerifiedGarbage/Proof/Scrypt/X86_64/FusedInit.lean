import VerifiedGarbage.Proof.Scrypt.X86_64.FusedLoop
namespace VG.Proof.Scrypt.X86_64.Retained
open VG VG.X86_64 VG.Impl.Scrypt.X86_64

theorem access {rs : List Region} {p : Addr} {len off n : Nat}
    (h : InRegions rs p len) (ho : off + n ≤ len) (hn : off < 2 ^ 64 := by omega) :
    InRegions rs (bufAt p off) n :=
  Covers.one h _ _ ⟨_, by simp, contains_off ho hn⟩

theorem load_step {s₀ : State}
    (hi : InRegions (s₀.rd ++ s₀.wr) (bp s₀) 64)
    (hw : InRegions s₀.wr (sp s₀) 64)
    (hd : (bR (bp s₀)).Disjoint (scR (sp s₀)))
    {n : Nat} (hn : n < 16) {s : State} (h : LI s₀ s₀ n s) :
    WP isa (.block (loadWord n)) s (LI s₀ s₀ (n + 1)) := by
  have hr : readSrc32 s (.mem (at_ .rdi (4 * n))) = some (V s₀)[n] := by
    rw [mem_read (by rw [h.rdi, h.rd, h.wr]; exact access hi (by omega)), h.rdi]
    rw [h.frame.readW (r := bR (bp s₀)) (a := bufAt (bp s₀) (4 * n)) (w := 32) (contains_off (by omega) (by omega)) (fun R hR => by
      simp only [List.mem_singleton] at hR; subst R
      exact hd.sub_right (Region.sub_prefix (by decide))) (by decide)]
    simp only [V_get _ hn]
  unfold loadWord
  split
  · rename_i hn12
    refine wp_cons (mov32_upd (d := wreg n) hr) fun s' u => WP.block_nil ?_
    have ne := wreg_ne n hn12
    refine ⟨fun k hk hkn => ?_, fun k hk h12 hkn => ?_, u.mem ▸ h.frame, u.rd.trans h.rd,
      u.wr.trans h.wr, (u.other _ ne.2.1.symm).trans h.rsi, (u.other _ ne.2.2.1.symm).trans h.rdi,
      (u.other _ ne.2.2.2.symm).trans h.rsp⟩
    · by_cases e : k = n
      · subst e; exact u.gpr
      · rw [u.other _ fun h' => e (wreg_inj k hk n hn12 h'), h.regs k hk (by omega)]
    · rw [u.mem]; exact h.slots k hk h12 (by omega)
  · rename_i hn12
    refine wp_cons (mov32_upd (d := .rax) hr) fun s' u => ?_
    have hout : InRegions s'.wr (s'.ea (at_ .rsi (slotOff n))) 4 := by
      rw [ea_at, u.other _ (by decide), h.rsi, u.wr, h.wr]
      exact access hw (by simp only [slotOff]; omega) (by simp only [slotOff]; omega)
    refine WP.block_cons_iff.mpr ⟨_, store32_exec hout, WP.block_nil ?_⟩
    rw [ea_at, u.other _ (by decide), h.rsi, u.gpr, u.mem]
    have e : ((V s₀)[n].setWidth 64).setWidth 32 = (V s₀)[n] := by simp
    rw [e]
    refine ⟨fun k hk hkn => ?_, fun k hk h12 hkn => ?_, ?_, u.rd.trans h.rd, u.wr.trans h.wr,
      (u.other _ (by decide)).trans h.rsi, (u.other _ (by decide)).trans h.rdi,
      (u.other _ (by decide)).trans h.rsp⟩
    · rw [u.other _ (wreg_ne k hk).1]; exact h.regs k hk (by omega)
    · by_cases e : k = n
      · subst e; exact Mem.readW_writeW_self32 _ _ _
      · rw [readW_writeW_off _ _ _ (by omega) (by simp only [slotOff]; omega)
          (by simp only [slotOff]; omega) (by simp only [slotOff]; omega)]
        exact h.slots k hk h12 (by omega)
    · exact h.frame.writeW (List.mem_singleton_self _) _
        (contains_off (by simp only [slotOff]; omega) (by simp only [slotOff]; omega))


theorem load_ok {s : State}
    (hi : InRegions (s.rd ++ s.wr) (bp s) 64) (hw : InRegions s.wr (sp s) 64)
    (hd : (bR (bp s)).Disjoint (scR (sp s))) :
    WP isa (.block load) s fun t => Words (sp s) (memWords s.mem (bp s)) t ∧
      Frame [slotR (sp s)] s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.gpr .rdi = bp s ∧ t.gpr .rsp = s.gpr .rsp := by
  have ini : LI s s 0 s := ⟨fun _ _ h => by omega, fun _ _ _ h => by omega,
    Frame.refl _ _, rfl, rfl, rfl, rfl, rfl⟩
  exact WP.mono (wp_range_flatMap (M := isa) (f := loadWord) (N := 16) (LI s s)
    (fun _ _ hn h => load_step hi hw hd hn h) 16 (Nat.le_refl _) s ini) fun t h =>
    ⟨⟨fun k hk => h.regs k hk (by omega), fun k hk h12 => h.slots k hk h12 hk, h.rsi⟩,
      h.frame, h.rd, h.wr, h.rdi, h.rsp⟩
end VG.Proof.Scrypt.X86_64.Retained
