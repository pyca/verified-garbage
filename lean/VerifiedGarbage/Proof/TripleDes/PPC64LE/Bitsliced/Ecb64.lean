module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.Ecb
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.SboxLit
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.SboxLit
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.Ecb

/-!
# Bitsliced Triple DES ECB on exactly 64 blocks on PPC64LE

`ecb64_wp`: `Bitslice.ecb64` does to the 64 blocks at `r4` what `ecb` does
(`Ecb.lean`), with the same setup, transpositions, passes and restores; its
copies are unrolled, each word at a fixed offset, and checked by evaluation
over the variable domain (`copy64_run`): the slots at the destination are
the external words at the source.
-/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Bitsliced

open VG VG.PPC64LE VG.PPC64LE.Straight VG.PPC64LE.RegUpd VG.Bitslice
open VG.Impl.TripleDes.PPC64LE.Bitslice VG.Spec.TripleDes
open VG.Proof.TripleDes.Bitslice (ipLane transposeW tdeaW blockOut wAt blockAt_frame)

/-! ## The copies -/

/-- The copy's memory: the 64 destination words, and the source's as external words. -/
def copyCfg (src dst : Reg) : Cfg := { base := dst, slots := 64, ext := src, exts := 64 }

/-- Source word `k` is variable `k`. -/
def copyExt (k : Nat) : Option Nat := if k < 64 then some (2 ^ k) else none

def copyEnv : Env Nat := { reg := fun _ => none, slot := fun _ => none }

def copyPost (e : Env Nat) : Bool := (List.range 64).all fun k => e.slot k == some (2 ^ k)

/-- What a copy writes: `r0`. -/
def onlyR0 (is : List Instr) : Bool := is.all fun i => dst i == none || dst i == some .r0

theorem copyIn_check :
    check (vars 64) (copyCfg .r4 .r10) copyExt copyIn64 copyEnv copyPost = true ∧ onlyR0 copyIn64 = true := by
  constructor <;> lit_decide

theorem copyOut_check :
    check (vars 64) (copyCfg .r10 .r4) copyExt copyOut64 copyEnv copyPost = true ∧ onlyR0 copyOut64 = true := by
  constructor <;> lit_decide

theorem sep_of_disjoint {a b : Addr} {n k : Nat} (h : (⟨a, n⟩ : Region).Disjoint ⟨b, k⟩) :
    Mem.Sep a n b k := fun x h₁ h₂ =>
  h x (by simp only [Region.Contains]; omega) (by simp only [Region.Contains]; omega)

/-- A copy of the 64 words at `src` to `dst`, apart, that evaluation checks. -/
theorem copy64_run {src dst : Reg} {is : List Instr} {s : State}
    (hchk : check (vars 64) (copyCfg src dst) copyExt is copyEnv copyPost = true ∧ onlyR0 is = true)
    (hin : Covers [⟨s.gpr src, 512⟩] (s.rd ++ s.wr)) (hout : Covers [⟨s.gpr dst, 512⟩] s.wr)
    (hsep : (⟨s.gpr dst, 512⟩ : Region).Disjoint ⟨s.gpr src, 512⟩) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ k < 64, s'.mem.readW (wordAddr (s.gpr dst) k) 64 = s.mem.readW (wordAddr (s.gpr src) k) 64) ∧
      (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.lr = s.lr ∧
      Frame [⟨s.gpr dst, 512⟩] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk.1
  let V : Nat → BitVec 64 := fun k => s.mem.readW (wordAddr (s.gpr src) k) 64
  have wsub : ∀ (p : Addr) k, k < 64 → Region.Sub ⟨wordAddr p k, 8⟩ ⟨p, 512⟩ := fun p k hk =>
    VG.Offset.sub_base _ (by omega)
  have hok : Ok (copyCfg src dst) s := {
    slotIn := fun k hk => hout _ _ ⟨_, List.mem_singleton_self _, slot_contains _ (n := 64) hk (by decide)⟩
    extIn := fun k hk => hin _ _ ⟨_, List.mem_singleton_self _, slot_contains _ (n := 64) hk (by decide)⟩
    slots := by show 8 * 64 < 2 ^ 64; decide
    sep := fun k hk j hj => sep_of_disjoint
      ((hsep.sub_left (wsub _ k hk)).sub_right (wsub _ j hj)) }
  have hrel : Rel (VarRel V 64) (copyCfg src dst) copyExt copyEnv s :=
    ⟨fun r a h => by simp [copyEnv] at h, fun k a _ h => by simp [copyEnv] at h, fun k a hk h => by
      have hk' : k < 64 := hk
      simp only [copyExt, hk', ite_true, Option.some.injEq] at h
      subst h
      simp only [VarRel]
      rw [xorSet_two_pow _ hk']
      rfl⟩
  obtain ⟨s', hs', p⟩ := run (vars_sound V 64) hok hrel he
  simp only [copyPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  refine ⟨s', hs', fun k hk => ?_, fun r hr => p.other r ?_, p.rd, p.wr, p.lr, p.frame⟩
  · have := p.rel.slot k _ hk (hpost k hk)
    simp only [VarRel] at this
    rw [xorSet_two_pow _ hk] at this
    rw [show s'.gpr (copyCfg src dst).base = s.gpr dst from p.base] at this
    exact this
  · have hd := List.all_eq_true.mp hchk.2
    have : is.all (fun i => Straight.dst i != some r) = true := List.all_eq_true.mpr fun i hi => by
      have := hd i hi
      simp only [Bool.or_eq_true, beq_iff_eq] at this
      rcases this with e | e <;> rw [e] <;> simp [Ne.symm hr]
    simp [this]

/-! ## The function -/

/-- What ECB on 64 blocks may assume: the schedule readable, the blocks and
the working space writable, apart from each other. -/
structure Ecb64Pre (s : State) : Prop where
  key : InRegions (s.rd ++ s.wr) (s.gpr .r3) 384
  data : Covers [⟨s.gpr .r4, 512⟩] s.wr
  buf : InRegions s.wr (s.gpr .r6) 1024
  keyData : (⟨s.gpr .r3, 384⟩ : Region).Disjoint ⟨s.gpr .r4, 512⟩
  keyBuf : (⟨s.gpr .r3, 384⟩ : Region).Disjoint ⟨s.gpr .r6, 1024⟩
  dataBuf : (⟨s.gpr .r4, 512⟩ : Region).Disjoint ⟨s.gpr .r6, 1024⟩

theorem ecb64_wp (d : Direction) {s : State} (h : Ecb64Pre s) :
    WP isa (ecb64 d) s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.lr = s.lr ∧
      s'.gpr .r10 = s.gpr .r6 ∧ s'.gpr .r7 = s.gpr .r3 ∧
      Frame [⟨s.gpr .r6, 1024⟩, ⟨s.gpr .r4, 512⟩] s.mem s'.mem ∧
      ∀ b < 64, blockAt s'.mem (wAt (s.gpr .r4) b) =
        blockOut (scheduleAt s.mem (s.gpr .r3)) d (blockAt s.mem (wAt (s.gpr .r4) b)) := by
  let D := s.gpr .r4
  let B := s.gpr .r6
  let K := scheduleAt s.mem (s.gpr .r3)
  have dataStR : (⟨D, 512⟩ : Region).Disjoint ⟨B, 512⟩ := h.dataBuf.sub_right (Region.sub_prefix (by decide))
  unfold ecb64
  apply WP.seq
  refine WP.mono (setup_ok ⟨h.buf⟩) fun v q => ?_
  have stv : stR v = ⟨B, 512⟩ := by rw [stR, q.r10]
  -- the copy in and the transposition
  apply WP.seq
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, c₁, g₁, rd₁, wr₁, lr₁, f₁⟩ := copy64_run (src := .r4) (dst := .r10) (s := v)
    copyIn_check
    (by rw [q.r4, q.rd, q.wr]; exact covers_rdwr h.data)
    (by rw [q.r10, q.wr]; exact Proof.Gather.PPC64LE.covers_prefix (covers_of_in h.buf) (by decide))
    (by rw [q.r10, q.r4]; exact dataStR.symm)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have s10₁ : s₁.gpr .r10 = B := (g₁ _ (by decide)).trans q.r10
  have fs₁ : Frame [stR v] v.mem s₁.mem := by
    rw [stv]; rw [q.r10] at f₁; exact f₁
  have h₁ : Room s₁ := q.room.congr (g₁ _ (by decide)) wr₁
  obtain ⟨s₂, run₂, w₂, rd₂, wr₂, -, lr₂, s10₂, k₂, f₂⟩ :=
    transpose_ok h₁ (masksAt_frame (g₁ _ (by decide)) fs₁ q.masks)
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have s10₂' : s₂.gpr .r10 = B := s10₂.trans s10₁
  have hc₂ : ∀ r ∈ transKept, s₂.gpr r = v.gpr r := fun r hr => by
    rw [k₂ r hr, g₁ r (by revert hr; decide +revert)]
  have fs₂ : Frame [⟨B, 512⟩] v.mem s₂.mem := by
    rw [← stv]; exact fs₁.trans (by rw [← stR_congr (g₁ _ (by decide))]; exact f₂)
  have w₁ : ∀ b < 64, words s₁ b = s.mem.readW (wAt D b) 64 := by
    intro b hb
    simp only [words, sl, s10₁]
    have := c₁ b hb
    rw [q.r10, q.r4] at this
    rw [this]
    exact (q.frame.readW (Region.contains_self _ 8) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.dataBuf.sub_left (VG.Offset.sub_base _ (by omega)))) (by decide))
  have hs₂ : Sched s₂ :=
    ⟨by rw [hc₂ .r7 (by decide), q.r7, rd₂, wr₂, rd₁, wr₁, q.rd, q.wr]; exact h.key,
      by simp only [frameR, hc₂ .r7 (by decide), q.r7, s10₂']; exact h.keyBuf⟩
  have ho₂ : Ones s₂ := by rw [Ones, hc₂ .r11 (by decide)]; exact q.ones
  have hR₂ : Room s₂ := h₁.congr s10₂ wr₂
  have keyF : ∀ {m : Mem}, Frame [⟨B, 1024⟩, ⟨D, 512⟩] s.mem m → scheduleAt m (s.gpr .r3) = K := fun hf =>
    VG.Proof.TripleDes.scheduleAt_eq_of_frame _ hf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.keyBuf
      · exact h.keyData
  have fB : ∀ {m m' : Mem}, Frame [⟨B, 512⟩] m m' → Frame [⟨B, 1024⟩, ⟨D, 512⟩] m m' := fun f =>
    f.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
  have fsv : Frame [⟨B, 1024⟩, ⟨D, 512⟩] s.mem v.mem := q.frame.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self
  have fs₂' : Frame [⟨B, 1024⟩, ⟨D, 512⟩] s.mem s₂.mem := fsv.trans (fB fs₂)
  have K₂ : scheduleAt s₂.mem (s₂.gpr .r7) = K := by
    rw [hc₂ .r7 (by decide), q.r7]; exact keyF fs₂'
  -- the passes
  apply WP.seq
  refine WP.mono (WP.rdwr (passes_ok d hR₂ hs₂ ho₂)) fun s₃ ⟨⟨w₃, k₃, rd₃, wr₃, _, lr₃, f₃⟩, _⟩ => ?_
  have s10₃ : s₃.gpr .r10 = B := (k₃ _ (by decide)).trans s10₂'
  have h₃ : Room s₃ := hR₂.congr (k₃ _ (by decide)) wr₃
  have fs₃ : Frame [⟨B, 512⟩] v.mem s₃.mem := fs₂.trans (by rw [stR, s10₂'] at f₃; exact f₃)
  -- the transposition back, the copy out and the registers back
  have q10 : s₃.gpr .r10 = v.gpr .r10 := s10₃.trans q.r10.symm
  rw [List.append_assoc, WP.block_append_iff]
  obtain ⟨s₄, run₄, w₄, rd₄, wr₄, -, lr₄, s10₄, k₄, f₄⟩ :=
    transpose_ok h₃ (masksAt_frame q10 (by rw [stv]; exact fs₃) q.masks)
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  have s10₄' : s₄.gpr .r10 = B := s10₄.trans s10₃
  have hc₄ : ∀ r ∈ [Reg.r4, .r7], s₄.gpr r = v.gpr r := fun r hr => by
    have h1 : r ∈ transKept ∧ r ∈ passKept := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide
    rw [k₄ r h1.1, k₃ r h1.2, hc₂ r h1.1]
  have fs₄ : Frame [⟨B, 512⟩] v.mem s₄.mem := fs₃.trans (by rw [stR, s10₃] at f₄; exact f₄)
  have wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂, wr₁, q.wr]
  have rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂, rd₁, q.rd]
  rw [WP.block_append_iff]
  obtain ⟨s₅, run₅, c₅, g₅, rd₅, wr₅, lr₅, f₅⟩ := copy64_run (src := .r10) (dst := .r4) (s := s₄)
    copyOut_check
    (by rw [s10₄', rd₄', wr₄']; exact covers_rdwr (Proof.Gather.PPC64LE.covers_prefix (covers_of_in h.buf) (by decide)))
    (by rw [hc₄ .r4 (by decide), q.r4, wr₄']; exact h.data)
    (by rw [hc₄ .r4 (by decide), q.r4, s10₄']; exact dataStR)
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have s10₅ : s₅.gpr .r10 = B := (g₅ _ (by decide)).trans s10₄'
  have r4₄ : s₄.gpr .r4 = D := (hc₄ .r4 (by decide)).trans q.r4
  have f₅' : Frame [⟨D, 512⟩] s₄.mem s₅.mem := by rw [← r4₄]; exact f₅
  have fs₅ : Frame [⟨B, 1024⟩, ⟨D, 512⟩] s.mem s₅.mem :=
    fsv.trans ((fB fs₄).trans (f₅'.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_of_mem _ List.mem_cons_self))
  have saved₅ : Spill.Saved B s.gpr savedL s₅.mem := by
    have sv₄ := q.saved.frame_in (lo := 560) (n := 152) (fun p hp => ⟨(savedL_le p hp).1, by
      have := (savedL_le p hp).2; omega⟩) fs₄ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact VG.Offset.disjoint_base _ (by omega) (by omega)
    exact sv₄.frame_in (lo := 560) (n := 152) (fun p hp => ⟨(savedL_le p hp).1, by
      have := (savedL_le p hp).2; omega⟩) f₅' fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (h.dataBuf.sub_right (VG.Offset.sub_base _ (by omega))).symm
  rw [finish_eq]
  refine WP.mono (Spill.restore_wp (b := .r10) (by decide) s10₅ savedL_fits.1 savedL_restorable
    (fun p hp => ?_) saved₅) fun y r => ⟨fun q' hq => r.gpr_of (.inl (preserved_saved q' hq)), ?_, ?_, ?_,
      by rw [r.mem]; exact fs₅, fun b hb => ?_⟩
  · rw [rd₅, wr₅, rd₄', wr₄']
    exact covers_rdwr (covers_of_in h.buf) _ _ ⟨_, List.mem_singleton_self _,
      VG.Offset.contains_base _ (by have := (savedL_le p hp).2; omega) (by have := (savedL_le p hp).2; omega)⟩
  · rw [r.lr, lr₅, lr₄, lr₃, lr₂, lr₁, q.lr]
  · rw [r.other _ (by decide), s10₅]
  · rw [r.other _ (by decide), g₅ _ (by decide), hc₄ .r7 (by decide), q.r7]
  · show blockAt y.mem (wAt D b) = blockOut K d (blockAt s.mem (wAt D b))
    have lane₂ : ipLane (words s₂) b = permute ip (decodeBlock (blockAt s.mem (wAt D b))) := by
      rw [VG.Proof.TripleDes.Bitslice.ipLane_congr w₂ b]
      refine VG.Proof.TripleDes.Bitslice.ipLane_transpose _ _ hb fun j hj => ?_
      rw [w₁ b hb]
      exact readW_bit s.mem (wAt D b) hj
    have word₅ : y.mem.readW (wAt D b) 64 = transposeW (words s₃) b := by
      rw [r.mem, ← w₄ b hb]
      have := c₅ b hb
      rw [r4₄, s10₄'] at this
      rw [show wAt D b = wordAddr D b from rfl, this]
      simp only [words, sl, s10₄']
    rw [VG.Proof.TripleDes.Bitslice.blockOut_cores]
    apply blockAt_of_readW
    intro j hj
    rw [word₅, VG.Proof.TripleDes.Bitslice.transpose_out _ _ j hj,
      VG.Proof.TripleDes.Bitslice.ipLane_congr w₃ b, VG.Proof.TripleDes.Bitslice.tdeaW_lane _ _ _ hb,
      lane₂, K₂]

end VG.Proof.TripleDes.PPC64LE.Bitsliced
