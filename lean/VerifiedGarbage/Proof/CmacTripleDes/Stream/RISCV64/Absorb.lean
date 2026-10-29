module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.AbsorbChain
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream

/-!
# Streaming TDEA-CMAC on RISC-V: `absorb`

The code saves the registers (`absSave_wp`), computes the number `h` of
bytes held back and whether the data fit in the `8 - h` bytes after them
(`flag_wp`); if they do, it copies them there (`Proof.CmacTripleDes.Stream.repr_fill`),
else it takes the chaining path (`chain_wp`, `repr_chain`); then it restores
the registers (`absorb_wp`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.CmacTripleDes.Stream.RISCV64
open VG.WriteBytes (writeBytes)
open VG.Proof.CmacTripleDes.Stream (held)

/-- What the paths leave, from the state `u` after the flag: the state then
represents the message followed by the data. -/
structure PDone (s₀ : State) (St D : Addr) (n L : Nat) (u s : State) : Prop where
  keep : ∀ r ∈ preserved, r ≠ .s3 → r ≠ .s4 → r ≠ .s5 → s.gpr r = u.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨St + BitVec.ofNat 64 400, 16⟩, ⟨s₀.sp - 944, 944⟩] u.mem s.mem
  repr : ∀ key msg, Spec.Cmac.tdesRepr u.mem St key msg → msg.length = n →
    Spec.Cmac.tdesRepr s.mem St key (msg ++ Spec.Aes.bytesAt u.mem D L)

/-- The first 400 bytes of the state, apart from what the paths write. -/
theorem keep400 {s₀ : State} {St : Addr} {m m' : Mem}
    (hstk : (⟨s₀.sp - 944, 944⟩ : Region).Disjoint ⟨St, 416⟩)
    (hf : Frame [⟨St + BitVec.ofNat 64 400, 16⟩, ⟨s₀.sp - 944, 944⟩] m m') :
    ∀ i < 400, m' (St + BitVec.ofNat 64 i) = m (St + BitVec.ofNat 64 i) := fun i hi =>
  hf _ fun r hr hc => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint St (d := i) (n := 1) (.inl (by omega)) (by omega) (by omega) _
        (Region.contains_self _ _) hc
    · exact hstk _ hc (Offset.contains_base _ (by omega) (by omega))

theorem paths_wp {s₀ s₁ u : State} {St D S : Addr} {n L : Nat} (hp : APre s₀ St D S n L)
    (h₁ : AMid s₀ St D S n L s₁) (hu : AFl St D S n L s₁ u) :
    WP isa (.ite (.nonzero .t2) chainPath fillPath) u (PDone s₀ St D n L u) := by
  have hL := hp.hL
  have hw := hp.wSt
  have hwd := hp.wD
  have hl := Proof.CmacTripleDes.Stream.held_le n
  have stW : (⟨St, 416⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  have dR : (⟨D, L⟩ : Region) ∈ s₀.rd := by rw [hp.rd]; simp
  have s1u : u.gpr .s1 = St := by rw [hu.keep _ (by decide) (by decide) (by decide), h₁.s1]
  have s2u : u.gpr .s2 = S := by rw [hu.keep _ (by decide) (by decide) (by decide), h₁.s2]
  have s3u : u.gpr .s3 = D := by rw [hu.keep _ (by decide) (by decide) (by decide), h₁.s3]
  have a3u : u.gpr .a3 = BitVec.ofNat 64 L := by rw [hu.keep _ (by decide) (by decide) (by decide), h₁.a3]
  have rdu : u.rd = s₀.rd := by rw [hu.rd, h₁.rd]
  have wru : u.wr = s₀.wr := by rw [hu.wr, h₁.wr]
  have spu : u.sp = s₀.sp := by rw [hu.sp, h₁.sp]
  have ev : isa.eval (.nonzero .t2) u = some (decide (8 - held n < L)) := by
    rw [eval_nonzero, hu.t2]; split <;> simp_all
  by_cases hc : 8 - held n < L
  · -- The data do not fit: chain.
    refine WP.ite true (by rw [ev]; simp [hc]) (fun _ => ?_) (fun h => by cases h)
    refine WP.mono (chain_wp hp ⟨s1u, s2u, s3u, a3u, hu.t0, hu.t1, hl, hc, rdu, wru, spu⟩) fun s hs => ?_
    refine ⟨hs.keep, hs.rd, hs.wr, hs.sp, hs.frame, fun key msg hr hn => ?_⟩
    subst hn
    have hsch : Spec.TripleDes.scheduleAt u.mem St = Spec.TripleDes.expandKey key := hr.2.1
    have dl : (Spec.Aes.bytesAt u.mem D L).length = L := Proof.Cmac.bytesAt_length _ _ _
    have hnb := Proof.CmacTripleDes.Stream.held_chain_pos (n := msg.length) (l := L) hc
    refine Proof.CmacTripleDes.Stream.repr_chain hr (keep400 hp.stk_st hs.frame) (by rw [dl]; exact hc) ?_ ?_
    · rw [dl, show St + 400 = St + BitVec.ofNat 64 400 from rfl, show St + 408 = St + BitVec.ofNat 64 408 from rfl,
        hs.cv, hsch, bytesAt_take u.mem D (by omega), bytesAt_drop_take u.mem D (by unfold Proof.CmacTripleDes.Stream.nblocks; omega),
        ← Proof.CmacTripleDes.Stream.blocksAt_eq]
      rfl
    · rw [dl, show St + 408 = St + BitVec.ofNat 64 408 from rfl, List.drop_drop,
        bytesAt_drop u.mem D (by unfold Proof.CmacTripleDes.Stream.nblocks; omega)]
      have e : L - (8 - held msg.length) - 8 * Proof.CmacTripleDes.Stream.nblocks msg.length L =
          tailOf L (8 - held msg.length) := rfl
      rw [e, hs.held]
      unfold tailOf nbOf Proof.CmacTripleDes.Stream.nblocks
      congr 1; omega
  · -- The data fit: copy them after the bytes held back.
    refine WP.ite false (by rw [ev]; simp [hc]) (fun h => by cases h) fun _ => ?_
    unfold fillPath toHeld mov
    refine WP.seq ?_
    refine wp_addi (imm := 408) (by decide) fun s₂ u₂ => wp_add fun s₃ u₃ => wp_mv fun s₄ u₄ =>
      wp_mv fun s₅ u₅ => WP.block_nil ?_
    have g₅ : ∀ r, r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → s₅.gpr r = u.gpr r := fun r a b c => by
      rw [u₅.other _ c, u₄.other _ b, u₃.other _ a, u₂.other _ a]
    refine WP.mono (wp_sp (copy_ok (tmp := .t6) (src := .t4) (dst := .t3) (cnt := .t5) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) s₅ (P := D)
      (C := St + BitVec.ofNat 64 408 + BitVec.ofNat 64 (held n)) (L := L) hL
      (by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), s3u])
      (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₂.other _ (by decide), s1u, hu.t0])
      (by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), a3u])
      (fun i hi => by
        rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, rdu, wru]
        exact ⟨_, List.mem_append_left _ dR, Offset.contains_base _ (by omega) (by omega)⟩)
      (fun i hi => by
        rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wru, Offset.add_add, Offset.add_add]
        exact ⟨_, stW, Offset.contains_base _ (by omega) (by omega)⟩)
      (by
        rw [Offset.add_add]
        exact (hp.st_d.sub_left (Offset.sub_base St (by omega))).symm))) fun s ⟨cs, sps⟩ => ?_
    have m₅ : s₅.mem = u.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
    have Fw : Frame [⟨St + BitVec.ofNat 64 400, 16⟩, ⟨s₀.sp - 944, 944⟩] u.mem s.mem := by
      rw [cs.mem, m₅]
      exact (WriteBytes.writeBytes_frame u.mem _ _ (R := ⟨St + BitVec.ofNat 64 400, 16⟩) (by
        rw [Proof.Cmac.bytesAt_length, Offset.add_add]
        exact Offset.contains St (by omega) (by omega) (by omega))).mono (by simp)
    refine ⟨fun r hr _ _ _ => ?_, by rw [cs.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rdu],
      by rw [cs.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wru], by rw [sps, u₅.sp, u₄.sp, u₃.sp, u₂.sp, spu], Fw,
      fun key msg hr hn => ?_⟩
    · obtain ⟨-, -, -, h3, h4, h5, h6, -⟩ := preserved_ne r hr
      rw [cs.other r h6 h4 h3 h5, g₅ r h3 h4 h5]
    subst hn
    have dl : (Spec.Aes.bytesAt u.mem D L).length = L := Proof.Cmac.bytesAt_length _ _ _
    refine Proof.CmacTripleDes.Stream.repr_fill hr (keep400 hp.stk_st Fw) (by rw [dl]; omega) ?_ ?_
    · rw [show St + 400 = St + BitVec.ofNat 64 400 from rfl]
      have Fw2 : Frame [⟨St + BitVec.ofNat 64 (408 + held msg.length), L⟩] u.mem s.mem := by
        rw [cs.mem, m₅, Offset.add_add]
        exact WriteBytes.writeBytes_frame _ _ _ (by
          rw [Proof.Cmac.bytesAt_length]; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
      exact Proof.Cmac.bytesAt_frame Fw2 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint St (.inl (by omega)) (by omega) (by omega)) (by decide)
    · rw [show St + 408 = St + BitVec.ofNat 64 408 from rfl, cs.mem, m₅]
      have := bytesAt_writeBytes u.mem (St + BitVec.ofNat 64 408) (held msg.length) (Spec.Aes.bytesAt u.mem D L)
        (by rw [dl]; omega)
      rw [dl] at this ⊢
      exact this


theorem absorb_wp {s₀ : State} (h0 : absorbRISCV64.pre s₀) :
    WP isa absorb s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
      s'.sp = s₀.sp ∧ absorbRISCV64.post s₀ s' := by
  have hp := APre.of h0
  generalize s₀.gpr .a0 = St at hp
  generalize s₀.gpr .a2 = D at hp
  generalize s₀.gpr .a4 = S at hp
  generalize (s₀.gpr .a1).toNat = n at hp
  generalize (s₀.gpr .a3).toNat = L at hp
  have hsw := hp.wS
  unfold absorb
  refine WP.seq (WP.mono (absSave_wp hp) fun s₁ h₁ => ?_)
  refine flag_wp (St := St) (D := D) (S := S) hp.hn hp.hL h₁.a1 h₁.a3 fun u hu => ?_
  refine WP.seq (WP.mono (paths_wp hp h₁ hu) fun s₂ h₂ => ?_)
  have s2₂ : s₂.gpr .s2 = S := by
    rw [h₂.keep _ (by decide) (by decide) (by decide) (by decide), hu.keep _ (by decide) (by decide) (by decide), h₁.s2]
  rw [restoreRegs, WP.block_append_iff]
  refine WP.mono (savePtr_ok .s2) fun s₃ e => ?_
  subst e
  rw [s2₂]
  have dSv (p : Reg × Nat) (hp' : p ∈ absSaved) (r : Region) (hr : r ∈ [⟨St + BitVec.ofNat 64 400, 16⟩,
      ⟨s₀.sp - 944, 944⟩]) : (⟨sv S + BitVec.ofNat 64 p.2, 8⟩ : Region).Disjoint r := by
    have hb := abs_bound p hp'
    have sub : Region.Sub ⟨sv S + BitVec.ofNat 64 p.2, 8⟩ ⟨S, 688⟩ := fun a ha =>
      Region.sub_prefix (by decide) a (sv_sub S (d := p.2) (n := 8) (by omega) a ha)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
    · exact hp.stk_s.symm.sub_left sub
  have F₂ : Frame [⟨St + BitVec.ofNat 64 400, 16⟩, ⟨s₀.sp - 944, 944⟩] s₁.mem s₂.mem := by
    have := h₂.frame; rwa [hu.mem] at this
  have sv₂ : Spill.Saved (sv S) (absG s₀ S) absSaved s₂.mem := by
    have sv₁ : Spill.Saved (sv S) (absG s₀ S) absSaved s₁.mem := by
      rw [h₁.mem]; exact Spill.saveMem_saved (by decide) s₀.mem (sv S) _
    exact sv₁.frame F₂ fun p hp' r hr => dSv p hp' r hr
  rw [show absSaved.map (fun (r, d) => Instr.load .d r .t0 d) = Spill.restoreCode .t0 absSaved from rfl]
  refine WP.mono (Spill.restore_wp (b := .t0) (l := absSaved) (B := sv S) (Align.align_al _)
    (RegUpd.gpr_write_self _ _ _) (by decide) (by decide) (fun p hp' => ?_) sv₂) fun s₄ r₄ => ?_
  · have := abs_bound p hp'
    show InRegions (s₂.rd ++ s₂.wr) _ 8
    rw [h₂.rd, h₂.wr, hp.rd, hp.wr]
    exact ⟨⟨S, 688⟩, by simp, sv_contains S (by omega) (by decide)⟩
  have g₀ (r : Reg) (hr : r ≠ .t0) : absG s₀ S r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · have h0 := (preserved_ne r hr).1
    rw [r₄.gpr_of (r := r) ?_, g₀ r h0]
    by_cases hv : r = .s1 ∨ r = .s2 ∨ r = .s3 ∨ r = .s4 ∨ r = .s5
    · left; rcases hv with rfl | rfl | rfl | rfl | rfl <;> decide
    · right
      obtain ⟨-, h1, h2, -⟩ := preserved_ne r hr
      rw [RegUpd.gpr_write_of_ne _ _ h0, h₂.keep r hr (fun e => hv (.inr (.inr (.inl e))))
        (fun e => hv (.inr (.inr (.inr (.inl e))))) (fun e => hv (.inr (.inr (.inr (.inr e))))),
        hu.keep r h0 h1 h2, h₁.other r hr (fun e => hv (.inl e)) (fun e => hv (.inr (.inl e)))
          (fun e => hv (.inr (.inr (.inl e)))), g₀ r h0]
  · rw [r₄.gpr (.ra, 0) (by decide), g₀ .ra (by decide)]
  · rw [r₄.sp, RegUpd.sp_write, h₂.sp]
  · intro key msg hr ha1 hlen
    rw [hp.a0] at hr ⊢
    rw [hp.a2] at ⊢
    rw [r₄.mem, RegUpd.mem_write]
    have hn : n = msg.length := by
      have := congrArg BitVec.toNat (hp.a1.symm.trans ha1)
      rwa [toNat_ofNat hp.hn, toNat_ofNat (by omega)] at this
    have hL : (s₀.gpr .a3).toNat = L := by rw [hp.a3, toNat_ofNat hp.hL]
    rw [hL]
    -- The state and the data on entry, through the saves.
    have f₁ : Frame [⟨sv S, 48⟩] s₀.mem u.mem := by
      rw [hu.mem, h₁.mem]
      exact Spill.saveMem_frame_base (l := absSaved) (n := 48) abs_bound (by decide) s₀.mem (sv S) (absG s₀ S)
    have dS : Region.Sub ⟨sv S, 48⟩ ⟨S, 688⟩ := by
      have := sv_sub S (d := 0) (n := 48) (by decide)
      rw [BitVec.add_zero] at this
      exact fun a ha => Region.sub_prefix (by decide) a (this a ha)
    have hru : Spec.Cmac.tdesRepr u.mem St key msg :=
      Proof.CmacTripleDes.Stream.repr_congr_416 (fun i hi => f₁ _ fun r hr hc => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.st_s _ (Offset.contains_base _ (by omega) (by omega)) (dS _ hc)) hr
    have hd : Spec.Aes.bytesAt u.mem D L = Spec.Aes.bytesAt s₀.mem D L :=
      Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.d_s.sub_right dS) (by have := hp.wD; omega)
    rw [← hd]
    exact h₂.repr key msg hru hn.symm

end VG.Proof.CmacTripleDes.Stream.RISCV64
