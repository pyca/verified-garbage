module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitch.Chunk
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Loop
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Save
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Loop
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# ChaCha20 and Poly1305 together (AArch64): a chunk of the loop

`Stitch.body`, as `Mixed8.tbody_ok`: from the kernel's loop invariant
(`Mixed8.TInv`, the source at `x27` and the destination at `x1`) after `t`
chunks to the one after `t + 1`, relative to the entry state `rebase s₀ u`,
since the chunk changes the accumulator's registers.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.Stitch

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.Stitch VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20.AArch64 (Words not_words_x1 not_words_x0 not_words_preserved)
open VG.Proof.ChaCha20.AArch64.Mixed8 (CP ChunkedFrom SrcOK source sr scalarBuf dr TInv TSaved
  tcp_of_inv tnext_ok twin_sub swin_sub)
open VG.Proof.ChaCha20.AArch64.Xor (TPre st dp L bp tp stR dR tR bR S0 D0 T0 KS Dst Src)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt)
open VG.Spec.Poly1305 (bytesAt)
open VG.Proof.Poly1305 (absorbAll)

variable {sve : Bool}

@[simp] theorem rebase_x0 (s₀ u : State) : (rebase s₀ u).gpr .x0 = s₀.gpr .x0 := rebase_of (by decide)
@[simp] theorem rebase_x1 (s₀ u : State) : (rebase s₀ u).gpr .x1 = s₀.gpr .x1 := rebase_of (by decide)
@[simp] theorem rebase_x2 (s₀ u : State) : (rebase s₀ u).gpr .x2 = s₀.gpr .x2 := rebase_of (by decide)
@[simp] theorem rebase_x3 (s₀ u : State) : (rebase s₀ u).gpr .x3 = s₀.gpr .x3 := rebase_of (by decide)
@[simp] theorem rebase_x4 (s₀ u : State) : (rebase s₀ u).gpr .x4 = s₀.gpr .x4 := rebase_of (by decide)
@[simp] theorem rebase_x19 (s₀ u : State) : (rebase s₀ u).gpr .x19 = s₀.gpr .x19 := rebase_of (by decide)
@[simp] theorem rebase_x20 (s₀ u : State) : (rebase s₀ u).gpr .x20 = s₀.gpr .x20 := rebase_of (by decide)
@[simp] theorem rebase_x26 (s₀ u : State) : (rebase s₀ u).gpr .x26 = s₀.gpr .x26 := rebase_of (by decide)
@[simp] theorem rebase_x27 (s₀ u : State) : (rebase s₀ u).gpr .x27 = s₀.gpr .x27 := rebase_of (by decide)
@[simp] theorem rebase_v (s₀ u : State) : (rebase s₀ u).v = s₀.v := rfl

@[simp] theorem st_rebase (s₀ u : State) : st (rebase s₀ u) = st s₀ := rebase_x0 s₀ u
@[simp] theorem dp_rebase (s₀ u : State) : dp (rebase s₀ u) = dp s₀ := rebase_x1 s₀ u
@[simp] theorem tp_rebase (s₀ u : State) : tp (rebase s₀ u) = tp s₀ := rebase_x4 s₀ u
@[simp] theorem L_rebase (s₀ u : State) : L (rebase s₀ u) = L s₀ := by simp [L]
@[simp] theorem bp_rebase (s₀ u : State) : bp (rebase s₀ u) = bp s₀ := rebase_x3 s₀ u
@[simp] theorem stR_rebase (s₀ u : State) : stR (rebase s₀ u) = stR s₀ := by simp [stR]
@[simp] theorem dR_rebase (s₀ u : State) : dR (rebase s₀ u) = dR s₀ := by simp [dR]
@[simp] theorem tR_rebase (s₀ u : State) : tR (rebase s₀ u) = tR s₀ := by simp [tR]
@[simp] theorem bR_rebase (s₀ u : State) : bR (rebase s₀ u) = bR s₀ := by simp [bR]
@[simp] theorem S0_rebase (s₀ u : State) : S0 (rebase s₀ u) = S0 s₀ := by simp [S0]
@[simp] theorem D0_rebase (s₀ u : State) (k : Nat) : D0 (rebase s₀ u) k = D0 s₀ k := by simp [D0]
@[simp] theorem T0_rebase (s₀ u : State) (k : Nat) : T0 (rebase s₀ u) k = T0 s₀ k := by simp [T0]
@[simp] theorem KS_rebase (s₀ u : State) : KS (rebase s₀ u) = KS s₀ := by simp [KS]

theorem tpre_rebase {s₀ : State} (u : State) (hp : TPre s₀) : TPre (rebase s₀ u) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hp
  exact ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4,
    by simpa using h5, by simpa using h6, by simpa using h7, by simpa using h8, by simpa using h9,
    by simpa using h10⟩

theorem dst_rebase {s₀ : State} {n : Nat} {m : Mem} (h : Dst s₀ n m) (u : State) : Dst (rebase s₀ u) n m := by
  intro k hk; simpa using h k (by simpa using hk)

theorem src_rebase {s₀ : State} {n : Nat} {m : Mem} (h : Src s₀ n m) (u : State) : Src (rebase s₀ u) n m := by
  intro k hk hn; simpa using h k (by simpa using hk) hn

/-- The kernel's loop invariant, for states with the accumulator's registers
of `u`. -/
theorem tinv_rebase {s₀ s : State} {t : Nat} (h : TInv s₀ t s) (u : State) :
    TInv (rebase s₀ u) t (rebase s u) := by
  refine ⟨by simpa using h.x0, by simpa using h.x1, by simpa using h.x2, by simpa using h.x3,
    by simpa using h.x20, by simpa using h.x27, by simpa using h.le, ?_, by simpa using h.rd,
    by simpa using h.wr, by simpa using h.sp, by simpa using h.cnt, dst_rebase h.data u,
    src_rebase h.src u, fun p hp => ?_, by simpa using h.savedV⟩
  · intro r hr h19 h20 h27 h26
    by_cases ha : r ∈ accRegs
    · rw [rebase_acc ha, rebase_acc ha]
    · rw [rebase_of ha, rebase_of ha]; exact h.cs r hr h19 h20 h27 h26
  · have e := h.saved p hp
    have hp' : p.1 ∉ accRegs :=
      (show ∀ q ∈ VG.Impl.ChaCha20.AArch64.Mixed8.savedFrom, q.1 ∉ accRegs by decide) p hp
    simpa only [bp_rebase, rebase_mem, rebase_of hp'] using e

/-- The bulk's precondition: the stream's (`vg_chacha20_xor`'s), with its
working space 64 bytes after the state, as in the ChaCha20-Poly1305 context. -/
structure BPre (s₀ : State) : Prop extends TPre s₀ where
  bp : bp s₀ = st s₀ + 64#64

theorem BPre.rebase {s₀ : State} (h : BPre s₀) (u : State) : BPre (rebase s₀ u) :=
  ⟨tpre_rebase u h.toTPre, by simpa using h.bp⟩

theorem BPre.key_sub {s₀ : State} (h : BPre s₀) : (⟨st s₀ + 224#64, 16⟩ : Region).Sub (bR s₀) := by
  simp only [bR, h.bp]
  exact Offset.sub (st s₀) (e := 64) (k := 320) (d := 224) (n := 16) (by decide) (by decide)

theorem BPre.key_in {s₀ : State} (h : BPre s₀) {d : Nat} (hd : 224 ≤ d) (hd' : d + 8 ≤ 240) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 d) 8 := by
  rw [h.rd, h.wr]
  refine ⟨bR s₀, by simp, ?_⟩
  simp only [bR, h.bp]
  exact Offset.contains (st s₀) (e := 64) (k := 320) (by omega) (by omega) (by decide)

/-- A chunk of the loop, absorbing the 512 bytes at `dp s₀ + w`: the chunk's
source when decrypting, the output before it when encrypting (in place). -/
theorem body_ok (enc : Bool) {s₀ : State} (hp : BPre s₀) (hin : enc = true → tp s₀ = dp s₀) {t : Nat}
    (hge : 512 * t + 512 ≤ L s₀) {s : State} (h : TInv s₀ t s) {R a : Nat} {w : Nat}
    (hw : w + 512 ≤ L s₀)
    (hB : dp s₀ + BitVec.ofNat 64 (512 * t) = dataOf enc (dp s₀ + BitVec.ofNat 64 w))
    (ha : Acc R a s) :
    WP isa (body sve enc) s fun v =>
      (TInv (rebase s₀ v) (t + 1) v ∧
        v.gpr .x5 = BitVec.ofNat 64 (if L s₀ - 512 * (t + 1) < 512 then 1 else 0)) ∧
      Acc R (absorbAll R a (bytesAt s.mem (dp s₀ + BitVec.ofNat 64 w) 512)) v := by
  have hL := VG.Proof.ChaCha20.AArch64.Xor.L_lt s₀
  have hBin : (⟨dp s₀ + BitVec.ofNat 64 w, 512⟩ : Region).Sub (dR s₀) := Offset.sub_base _ hw
  have hx0 : s.gpr .x0 = st s₀ := h.x0
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have hwin : (⟨dp s₀ + BitVec.ofNat 64 w, 512⟩ : Region).Disjoint (stR s₀) ∧
      (⟨dp s₀ + BitVec.ofNat 64 w, 512⟩ : Region).Disjoint (bR s₀) :=
    ⟨hp.st_d.symm.sub_left hBin, hp.d_b.sub_left hBin⟩
  have hsb : (scalarBuf s).Sub (bR s₀) := by
    simp only [scalarBuf, h.x3]; exact Region.sub_prefix (by decide)
  have hkey : (keyR s).Sub (bR s₀) := by simp only [keyR, hx0]; exact hp.key_sub
  obtain ⟨hcp, hsrc⟩ := tcp_of_inv hp.toTPre h hge
  have hpre : ChunkPre enc (dp s₀ + BitVec.ofNat 64 w) s := by
    refine ⟨hcp, by rw [h.x20, hx0, hp.bp], h.x27.trans hB, fun he => by rw [h.x1, h.x27, hin he],
      hsrc, fun d hd => ?_, ?_, ?_, ?_, ?_⟩
    · rw [hrw, hp.rd, hp.wr]
      refine ⟨dR s₀, by simp, ?_⟩
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact Offset.contains_base _ (by omega) (by omega)
    · rw [hrw, hx0]; exact hp.key_in (by decide) (by decide)
    · rw [hrw, hx0]; exact hp.key_in (by decide) (by decide)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simpa only [sr, hx0] using hwin.1
      · exact hwin.2.sub_right hsb
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simpa only [sr, hx0] using (hp.st_b.symm.sub_left hkey)
      · simp only [keyR, scalarBuf, hx0, h.x3, hp.bp]
        exact Offset.disjoint (st s₀) (d := 224) (n := 16) (e := 64) (k := 128) (by decide)
          (by decide) (by decide)
      · simp only [dr, h.x1]
        exact (hp.t_b.symm.sub_left hkey).sub_right (twin_sub hge)
  unfold body
  apply WP.seq
  refine (chunk_ok enc s hpre ha).mono fun g ⟨hg, hag⟩ => ?_
  refine (tnext_ok (tpre_rebase g hp.toTPre) (by simpa using hge) (tinv_rebase h g) hg).mono
    fun v ⟨hv, h5, hf⟩ => ?_
  have hacc : ∀ r ∈ accRegs, v.gpr r = g.gpr r := fun r hr =>
    (hv.cs r (acc_preserved r hr).1 (by intro he; rw [he] at hr; exact absurd hr (by decide))
      (acc_preserved r hr).2.2.2 (by intro he; rw [he] at hr; exact absurd hr (by decide))
      (acc_preserved r hr).2.2.1).trans (rebase_acc hr)
  rw [rebase_congr s₀ hacc]
  refine ⟨⟨hv, by simpa using h5⟩, hag.frame (acc_regs_keep hacc) ?_⟩
  have hg0 : g.gpr .x0 = st s₀ := (hg.x0.trans (rebase_x0 _ _)).trans hx0
  refine rword_frame (by simpa using hf) (hv.x0.trans (by simp [hg0])) ?_
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  simp only [keyR, hg0]
  exact (hp.st_b.symm.sub_left hp.key_sub)

/-- Where `Mixed8.enterFrom` stores: `x20`, `x19`, `x26` and `x27` at
`buf[256, 288)`, and `v8` and `v9` at `buf[128, 160)`. -/
abbrev enterR (s : State) : List Region :=
  [⟨s.gpr .x3 + BitVec.ofNat 64 256, 32⟩, ⟨s.gpr .x3 + BitVec.ofNat 64 128, 32⟩]

theorem enter_frame (s : State)
    (ho : ∀ d n, d + n ≤ 320 → InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 d) n) :
    WP isa (.block VG.Impl.ChaCha20.AArch64.Mixed8.enterFrom) s fun u =>
      Frame (enterR s) s.mem u.mem := by
  rw [show VG.Impl.ChaCha20.AArch64.Mixed8.enterFrom =
    Spill.saveCode .x3 VG.Impl.ChaCha20.AArch64.Mixed8.savedFrom ++
    (.addImm .x .x20 .x3 0 :: (VG.Proof.ChaCha20.AArch64.Mixed8.saveV ++
      [.addImm .x .x27 .x1 0, .addImm .x .x1 .x4 0])) from rfl]
  refine Spill.save_ok (by decide) (fun p hp' => ho p.2 8 (by revert p; decide)) ?_
  let b : State := { s with mem := Spill.saveMem s.mem (s.gpr .x3) s.gpr VG.Impl.ChaCha20.AArch64.Mixed8.savedFrom }
  have f₁ : Frame (enterR s) s.mem b.mem :=
    (Spill.saveMem_frame (lo := 256) (n := 32) (by decide) (by decide) _ _ _).mono (by simp)
  apply WP.block_cons_iff.mpr
  let a := b.write .x .x20 (b.gpr .x3 + BitVec.ofNat 64 0)
  refine ⟨a, by simpa only [State.read, BitVec.setWidth_eq] using
    exec_addImm_x (s := b) (d := .x20) (n := .x3) (imm := 0) (by decide), ?_⟩
  have ha3 : a.gpr .x3 = s.gpr .x3 := RegUpd.gpr_write_of_ne _ .x _ (by decide)
  have haw : a.wr = s.wr := rfl
  refine WP.block_append_iff.mpr ((VG.Proof.ChaCha20.AArch64.Mixed8.saveV_ok a
    (by rw [haw, ha3]; exact ho 128 16 (by decide))
    (by rw [haw, ha3]; exact ho 144 16 (by decide))).mono fun c ⟨_, _, _, _, _, hf, _, _⟩ => ?_)
  simp only [VG.Proof.ChaCha20.AArch64.Mixed8.savedVR, ha3] at hf
  refine VG.Proof.ChaCha20.AArch64.Xor.wp_movS fun d ud _ _ =>
    VG.Proof.ChaCha20.AArch64.Xor.wp_movS fun e ue _ _ => WP.block_nil ?_
  rw [ue.mem, ud.mem]
  exact f₁.trans (hf.mono (by simp))

end VG.Proof.ChaCha20Poly1305.AArch64.Stitch
