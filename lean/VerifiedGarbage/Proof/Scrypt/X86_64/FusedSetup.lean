import VerifiedGarbage.Proof.Scrypt.X86_64.FusedInvariant
namespace VG.Proof.Scrypt.X86_64.BlockMix.Fused
open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Proof.Scrypt.X86_64.Retained (Words Meta memWords)
open VG.Proof.MdStream.X86_64 (wp_mov)

def metaSaved : List (Reg × Nat) := [(.rbx, 16), (.rbp, 24), (.r12, 32), (.r14, 40)]

theorem memWords_frame {rs : List Region} {m m' : Mem} {p : Addr}
    (hf : Frame rs m m') (hd : ∀ R ∈ rs, Region.Disjoint ⟨p, 64⟩ R) :
    memWords m' p = memWords m p := by
  apply Vector.ext
  intro j hj
  simp only [memWords, Vector.getElem_ofFn]
  exact hf.readW (r := ⟨p, 64⟩) (contains_off (by omega) (by omega)) hd (by decide)

theorem setup_ok {s₀ s : State} (hp : Pre s₀) (h : BlockMix.Inv s₀ 0 s) :
    WP isa (.block fusedSetup) s (Inv s₀ 0) := by
  have pos := hp.pos
  have bound : ∀ p ∈ metaSaved, p.2 + 8 ≤ 64 := by decide
  change WP isa (.block (Spill.saveCode .r13 metaSaved ++
    [.mov .rsi (.reg .r13), .mov .rdi (.reg .r15)] ++ load)) s _
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Spill.save_ok .r13 metaSaved s (fun p hp' => by
    rw [h.r13, h.wr, hp.wr]
    exact ⟨scR s₀, by simp, in_s s₀ (by have := bound p hp'; omega)⟩)) fun a ⟨ga, ra, wa, ma⟩ => ?_
  rw [h.r13] at ma
  have fa : Frame [⟨sc s₀, 64⟩] s.mem a.mem := by
    rw [ma]; exact Spill.saveMem_frame_base s.mem (sc s₀) s.gpr metaSaved bound (by decide)
  have sa := Spill.saveMem_saved s.mem (sc s₀) s.gpr metaSaved (by decide)
  rw [← ma] at sa
  have metadata : Meta (sc s₀) (bB s₀ 0) (yE s₀ 0) (yO s₀ 0) (BitVec.ofNat 64 (rr s₀ - 0)) a.mem := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [Spill.slot, bufAt, ofInt_natCast, h.rbx] using sa (.rbx, 16) (by simp [metaSaved])
    · simpa only [Spill.slot, bufAt, ofInt_natCast, h.rbp] using sa (.rbp, 24) (by simp [metaSaved])
    · simpa only [Spill.slot, bufAt, ofInt_natCast, h.r12] using sa (.r12, 32) (by simp [metaSaved])
    · simpa only [Spill.slot, bufAt, ofInt_natCast, h.r14] using sa (.r14, 40) (by simp [metaSaved])
  refine wp_mov fun b ub _ _ => wp_mov fun c uc _ _ => WP.block_nil ?_
  have si : c.gpr .rsi = sc s₀ := by rw [uc.other _ (by decide), ub.gpr, ga, h.r13]
  have di : c.gpr .rdi = xP s₀ 0 := by rw [uc.gpr, ub.other _ (by decide), ga, h.r15]
  have rc : c.rd = s₀.rd := by rw [uc.rd, ub.rd, ra, h.rd]
  have wc : c.wr = s₀.wr := by rw [uc.wr, ub.wr, wa, h.wr]
  have mc : c.mem = a.mem := by rw [uc.mem, ub.mem]
  have spc : c.gpr .rsp = s.gpr .rsp := by rw [uc.other _ (by decide), ub.other _ (by decide), ga]
  have li : InRegions (c.rd ++ c.wr) (bp c) 64 := by
    rw [bp, di, rc, wc, hp.rd, hp.wr]
    exact ⟨bR s₀, by simp, in_b hp (by omega)⟩
  have ls : InRegions c.wr (sp c) 64 := by
    rw [sp, si, wc, hp.wr]; exact ⟨scR s₀, by simp, by simpa using in_s s₀ (o := 0) (n := 64) (by decide)⟩
  have ld : (VG.Proof.Scrypt.X86_64.bR (bp c)).Disjoint (VG.Proof.Scrypt.X86_64.scR (sp c)) := by
    rw [bp, sp, di, si]; exact x_s hp (by omega)
  refine WP.mono (Retained.load_ok li ls ld) fun t ⟨wt, ft, rt, wrt, _, spt⟩ => ?_
  simp only [sp, bp, si, di] at wt ft
  have mprev : memWords t.mem (xP s₀ 0) = memWords c.mem (xP s₀ 0) :=
    memWords_frame ft fun R hR => by
      simp only [List.mem_singleton] at hR; subst R
      exact (x_s hp (by omega)).sub_right (Region.sub_prefix (by decide))
  have f64 : Frame [⟨sc s₀, 64⟩] c.mem t.mem := ft.sub (sub_slot_sc _)
  have log := (Logical.of_old h).scratch hp (fa.trans (mc ▸ f64))
    (rt.trans (uc.rd.trans (ub.rd.trans ra))) (wrt.trans (uc.wr.trans (ub.wr.trans wa))) (spt.trans spc)
  refine ⟨log, ?_, ?_⟩
  · rw [mprev]; exact wt
  · have metac : Meta (sc s₀) (bB s₀ 0) (yE s₀ 0) (yO s₀ 0) (BitVec.ofNat 64 (rr s₀ - 0)) c.mem := mc ▸ metadata
    exact metac.frame (slot_s hp (o := 0) (by omega)) (ft.sub fun R hR => by
      simp only [List.mem_singleton] at hR; subst R
      exact ⟨slotR (sc s₀), by simp, fun _ h => h⟩)

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (bmPrologue ++ fusedSetup)) s₀ (Inv s₀ 0) := by
  rw [WP.block_append_iff]
  exact WP.mono (BlockMix.prologue_ok hp) fun s h => setup_ok hp h
end VG.Proof.Scrypt.X86_64.BlockMix.Fused
