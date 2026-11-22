module

-- separate module: the core on 64 blocks, as `ModeCore.lean` is the core on one; it alone imports the bitsliced ECB
public import VerifiedGarbage.Proof.Modes.PPC64LE.Wide
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Modes.PPC64LE.Core
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Modes
public import VerifiedGarbage.Proof.TripleDes.CbcBlocks
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Ecb.Call
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.Ecb
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.SboxLit
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.SboxLit
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.Ecb

/-! ### `TripleDes.PPC64LE.Bitsliced.Ecb64`, which only this module used -/

section

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
  h x (by simp only [Region.Contains]; omega_using [h₁]) (by simp only [Region.Contains]; omega_using [h₂])

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
  obtain wsub : ∀ (p : Addr) k, k < 64 → Region.Sub ⟨wordAddr p k, 8⟩ ⟨p, 512⟩ := fun p k hk =>
    VG.Offset.sub_base _ (by omega_using [hk])
  obtain hok : Ok (copyCfg src dst) s := {
    slotIn := fun k hk => hout _ _ ⟨_, List.mem_singleton_self _, slot_contains _ (n := 64) hk (by decide)⟩
    extIn := fun k hk => hin _ _ ⟨_, List.mem_singleton_self _, slot_contains _ (n := 64) hk (by decide)⟩
    slots := by show 8 * 64 < 2 ^ 64; decide
    sep := fun k hk j hj => sep_of_disjoint
      ((hsep.sub_left (wsub _ k hk)).sub_right (wsub _ j hj)) }
  obtain hrel : Rel (VarRel V 64) (copyCfg src dst) copyExt copyEnv s :=
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
  obtain dataStR : (⟨D, 512⟩ : Region).Disjoint ⟨B, 512⟩ := h.dataBuf.sub_right (Region.sub_prefix (by decide))
  unfold ecb64
  apply WP.seq
  refine WP.mono (setup_ok ⟨h.buf⟩) fun v ⟨q, ql⟩ => ?_
  obtain stv : stR v = ⟨B, 512⟩ := by rw [stR, q.r10]
  -- the copy in and the transposition
  apply WP.seq
  obtain ⟨s₁, run₁, c₁, g₁, rd₁, wr₁, lr₁, f₁⟩ := copy64_run (src := .r4) (dst := .r10) (s := v)
    copyIn_check
    (by rw [q.r4, q.rd, q.wr]; exact covers_rdwr h.data)
    (by rw [q.r10, q.wr]; exact Proof.Gather.PPC64LE.covers_prefix (covers_of_in h.buf) (by decide))
    (by rw [q.r10, q.r4]; exact dataStR.symm)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain s10₁ : s₁.gpr .r10 = B := (g₁ _ (by decide)).trans q.r10
  obtain fs₁ : Frame [stR v] v.mem s₁.mem := by
    rw [stv]; rw [q.r10] at f₁; exact f₁
  obtain h₁ : Room s₁ := q.room.congr (g₁ _ (by decide)) wr₁
  obtain ho₁ : Ones s₁ := by rw [Ones, g₁ _ (by decide)]; exact q.ones
  apply WP.seq
  refine WP.mono (transposeCall_ok h₁ (masksAt_frame (g₁ _ (by decide)) fs₁ q.masks) ho₁)
    fun s₂ ⟨w₂, rd₂, wr₂, _, s10₂, k₂, f₂⟩ => ?_
  obtain s10₂' : s₂.gpr .r10 = B := s10₂.trans s10₁
  obtain hc₂ : ∀ r ∈ transKept, s₂.gpr r = v.gpr r := fun r hr => by
    rw [k₂ r hr, g₁ r (by revert hr; decide +revert)]
  obtain fs₂ : Frame [⟨B, 512⟩] v.mem s₂.mem := by
    rw [← stv]; exact fs₁.trans (by rw [← stR_congr (g₁ _ (by decide))]; exact f₂)
  obtain w₁ : ∀ b < 64, words s₁ b = s.mem.readW (wAt D b) 64 := by
    intro b hb
    simp only [words, sl, s10₁]
    have := c₁ b hb
    rw [q.r10, q.r4] at this
    rw [this]
    exact (q.frame.readW (Region.contains_self _ 8) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.dataBuf.sub_left (VG.Offset.sub_base _ (by omega_using [hb])))) (by decide))
  obtain hs₂ : Sched s₂ :=
    ⟨by rw [hc₂ .r7 (by decide), q.r7, rd₂, wr₂, rd₁, wr₁, q.rd, q.wr]; exact h.key,
      by simp only [frameR, hc₂ .r7 (by decide), q.r7, s10₂']; exact h.keyBuf⟩
  obtain ho₂ : Ones s₂ := by rw [Ones, hc₂ .r11 (by decide)]; exact q.ones
  obtain hR₂ : Room s₂ := h₁.congr s10₂ wr₂
  obtain keyF : ∀ {m : Mem}, Frame [⟨B, 1024⟩, ⟨D, 512⟩] s.mem m → scheduleAt m (s.gpr .r3) = K := fun hf =>
    VG.Proof.TripleDes.scheduleAt_eq_of_frame _ hf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.keyBuf
      · exact h.keyData
  obtain fB : ∀ {m m' : Mem}, Frame [⟨B, 512⟩] m m' → Frame [⟨B, 1024⟩, ⟨D, 512⟩] m m' := fun f =>
    f.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
  obtain fsv : Frame [⟨B, 1024⟩, ⟨D, 512⟩] s.mem v.mem := q.frame.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self
  obtain fs₂' : Frame [⟨B, 1024⟩, ⟨D, 512⟩] s.mem s₂.mem := fsv.trans (fB fs₂)
  obtain K₂ : scheduleAt s₂.mem (s₂.gpr .r7) = K := by
    rw [hc₂ .r7 (by decide), q.r7]; exact keyF fs₂'
  -- the passes
  apply WP.seq
  refine WP.mono (WP.rdwr (passes_ok d hR₂ hs₂ ho₂)) fun s₃ ⟨⟨w₃, k₃, rd₃, wr₃, _, f₃⟩, _⟩ => ?_
  obtain s10₃ : s₃.gpr .r10 = B := (k₃ _ (by decide)).trans s10₂'
  obtain h₃ : Room s₃ := hR₂.congr (k₃ _ (by decide)) wr₃
  obtain fs₃ : Frame [⟨B, 512⟩] v.mem s₃.mem := fs₂.trans (by rw [stR, s10₂'] at f₃; exact f₃)
  -- the transposition back, the copy out and the registers back
  obtain q10 : s₃.gpr .r10 = v.gpr .r10 := s10₃.trans q.r10.symm
  obtain ho₃ : Ones s₃ := by rw [Ones, k₃ _ (by decide)]; exact ho₂
  apply WP.seq
  refine WP.mono (transposeCall_ok h₃ (masksAt_frame q10 (by rw [stv]; exact fs₃) q.masks) ho₃)
    fun s₄ ⟨w₄, rd₄, wr₄, _, s10₄, k₄, f₄⟩ => ?_
  obtain s10₄' : s₄.gpr .r10 = B := s10₄.trans s10₃
  obtain hc₄ : ∀ r ∈ [Reg.r4, .r7], s₄.gpr r = v.gpr r := fun r hr => by
    obtain h1 : r ∈ transKept ∧ r ∈ passKept := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide
    rw [k₄ r h1.1, k₃ r h1.2, hc₂ r h1.1]
  obtain fs₄ : Frame [⟨B, 512⟩] v.mem s₄.mem := fs₃.trans (by rw [stR, s10₃] at f₄; exact f₄)
  obtain wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂, wr₁, q.wr]
  obtain rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂, rd₁, q.rd]
  rw [WP.block_append_iff]
  obtain ⟨s₅, run₅, c₅, g₅, rd₅, wr₅, lr₅, f₅⟩ := copy64_run (src := .r10) (dst := .r4) (s := s₄)
    copyOut_check
    (by rw [s10₄', rd₄', wr₄']; exact covers_rdwr (Proof.Gather.PPC64LE.covers_prefix (covers_of_in h.buf) (by decide)))
    (by rw [hc₄ .r4 (by decide), q.r4, wr₄']; exact h.data)
    (by rw [hc₄ .r4 (by decide), q.r4, s10₄']; exact dataStR)
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  obtain s10₅ : s₅.gpr .r10 = B := (g₅ _ (by decide)).trans s10₄'
  obtain r4₄ : s₄.gpr .r4 = D := (hc₄ .r4 (by decide)).trans q.r4
  obtain f₅' : Frame [⟨D, 512⟩] s₄.mem s₅.mem := by rw [← r4₄]; exact f₅
  obtain fs₅ : Frame [⟨B, 1024⟩, ⟨D, 512⟩] s.mem s₅.mem :=
    fsv.trans ((fB fs₄).trans (f₅'.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_of_mem _ List.mem_cons_self))
  obtain saved₅ : Spill.Saved B s.gpr savedL s₅.mem := by
    obtain sv₄ := q.saved.frame_in (lo := 560) (n := 152) (fun p hp => ⟨(savedL_le p hp).1, by
      have := (savedL_le p hp).2; omega_using [this]⟩) fs₄ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact VG.Offset.disjoint_base _ (by omega_using []) (by omega_using [])
    exact sv₄.frame_in (lo := 560) (n := 152) (fun p hp => ⟨(savedL_le p hp).1, by
      have := (savedL_le p hp).2; omega_using [this]⟩) f₅' fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (h.dataBuf.sub_right (VG.Offset.sub_base _ (by omega_using []))).symm
  obtain hl₅ : s₅.mem.readW (B + BitVec.ofNat 64 lrOff) 64 = s.lr := by
    rw [f₅'.readW (Region.contains_self _ 8) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (h.dataBuf.sub_right (VG.Offset.sub_base _ (by decide))).symm) (by decide),
      fs₄.readW (Region.contains_self _ 8) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact VG.Offset.disjoint_base _ (by decide) (by decide)) (by decide)]
    exact ql
  obtain inB : ∀ e, e + 8 ≤ 1024 → InRegions (s₅.rd ++ s₅.wr) (B + BitVec.ofNat 64 e) 8 := fun e he => by
    rw [rd₅, wr₅, rd₄', wr₄']
    exact covers_rdwr (covers_of_in h.buf) _ _ ⟨_, List.mem_singleton_self _,
      VG.Offset.contains_base _ he (by omega_using [he])⟩
  rw [finish, finish_eq, WP.block_append_iff]
  refine WP.mono (Spill.restore_wp (b := .r10) (by decide) s10₅ savedL_fits.1 savedL_restorable
    (fun p hp => inB _ (by have := (savedL_le p hp).2; omega_using [this])) saved₅) fun y r =>
    WP.mono (lrRestore_ok ((r.other _ (by decide)).trans s10₅) (by rw [r.rd, r.wr]; exact inB _ (by decide))
      (by rw [r.mem]; exact hl₅)) fun y' ⟨g', l', m', _⟩ =>
    ⟨fun q' hq => by rw [g' q' (by revert hq; decide +revert)]; exact r.gpr_of (.inl (preserved_saved q' hq)),
      l', ?_, ?_, by rw [m', r.mem]; exact fs₅, fun b hb => ?_⟩
  · rw [g' _ (by decide), r.other _ (by decide), s10₅]
  · rw [g' _ (by decide), r.other _ (by decide), g₅ _ (by decide), hc₄ .r7 (by decide), q.r7]
  · show blockAt y'.mem (wAt D b) = blockOut K d (blockAt s.mem (wAt D b))
    rw [m']
    obtain lane₂ : ipLane (words s₂) b = permute ip (decodeBlock (blockAt s.mem (wAt D b))) := by
      rw [VG.Proof.TripleDes.Bitslice.ipLane_congr w₂ b]
      refine VG.Proof.TripleDes.Bitslice.ipLane_transpose _ _ hb fun j hj => ?_
      rw [w₁ b hb]
      exact readW_bit s.mem (wAt D b) hj
    obtain word₅ : y.mem.readW (wAt D b) 64 = transposeW (words s₃) b := by
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

end

end

/-! ### `TripleDes.PPC64LE.ModeCore`, which this module and modules that import it used -/

section

/-!
# Triple DES's core for the modes on PPC64LE

`dirCoreSpec d`: Triple DES's core for the direction `d`
(`Impl.TripleDes.PPC64LE.dirCore d`) meets what the modes need of a core
(`Proof.Modes.PPC64LE.CoreSpec`), with the key a schedule, read in place
through `r3`, its cipher `Spec.TripleDes.cipher` for encryption and
`Spec.TripleDes.invCipher` for decryption. The schedule is readable and
apart from the regions the mode writes (`KeyArgs`), and from the scratch
buffer (`Ready`), so nothing the mode or the core writes changes it. The
block function's call is ECB's (`Ecb.call_ok`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Mode

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE
open VG.Impl.Modes.PPC64LE (sb)
open VG.Proof.Modes.PPC64LE (coreRegion blkRegion blkAddr slotA CoreSpec Layout ScrIn kept)
open VG.Spec.Aes (bytesAt)
open VG.Spec.TripleDes (Direction)
open VG.Proof.TripleDes (dirCipher bytesAt_eq ofFn_bytesAt scheduleAt_eq_of_frame)

/-- The schedule. -/
abbrev keyR (s : State) : Region := ⟨s.gpr .r3, 384⟩

/-- The schedule at `r3` is `k`, readable, and apart from the regions `rs`. -/
def KeyArgs (s : State) (rs : List Region) (k : Spec.TripleDes.Schedule) : Prop :=
  Spec.TripleDes.scheduleAt s.mem (s.gpr .r3) = k ∧ InRegions (s.rd ++ s.wr) (s.gpr .r3) 384 ∧
    ∀ r ∈ rs, (keyR s).Disjoint r

/-- The key's arguments, apart from the scratch buffer at `B` too. -/
def Ready (s : State) (B : Addr) (ws : List Region) (k : Spec.TripleDes.Schedule) : Prop :=
  KeyArgs s ws k ∧ (keyR s).Disjoint ⟨B, 8 * 72⟩

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.TripleDes.Schedule} (h : KeyArgs s rs k)
    (e : s'.gpr .r3 = s.gpr .r3) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) :
    KeyArgs s' rs k := by
  obtain ⟨hk, hin, hd⟩ := h
  refine ⟨?_, by rw [hrd, hwr, e]; exact hin, by rw [keyR, e]; exact hd⟩
  rw [e, scheduleAt_eq_of_frame _ hf hd, hk]

theorem ready_frame {s s' : State} {B : Addr} {ws : List Region} {k : Spec.TripleDes.Schedule}
    {rs : List Region} (h : Ready s B ws k) (e : s'.gpr .r3 = s.gpr .r3) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, ∃ r' ∈ ws, Region.Sub r r') :
    Ready s' B ws k := by
  obtain ⟨⟨hk, hin, hd⟩, hB⟩ := h
  have hd' : ∀ r ∈ rs, (keyR s).Disjoint r := fun r hr => by
    obtain ⟨r', hr', hsub⟩ := hs r hr
    exact (hd r' hr').sub_right hsub
  refine ⟨⟨?_, by rw [hrd, hwr, e]; exact hin, by rw [keyR, e]; exact hd⟩, by rw [keyR, e]; exact hB⟩
  rw [e, scheduleAt_eq_of_frame _ hf hd', hk]

theorem layout (d : Direction) : Layout (dirCore d) :=
  ⟨by cases d <;> decide, .inl rfl, by cases d <;> decide, by cases d <;> decide, by cases d <;> decide⟩

theorem prepare_wp (d : Direction) {s : State} {B : Addr} {rs : List Region} {k : Spec.TripleDes.Schedule}
    (_hB : s.gpr sb = B) (_hS : ScrIn s B (dirCore d).total) (hm : (⟨B, 8 * (dirCore d).total⟩ : Region) ∈ rs)
    (hk : KeyArgs s rs k) :
    WP isa (dirCore d).prepare s fun s' => Ready s' B rs k ∧ s'.gpr sb = B ∧
      (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr :=
  wp_nil ⟨⟨hk, hk.2.2 _ hm⟩, _hB, fun _ _ => rfl, Frame.refl _ _, rfl, rfl⟩

theorem dirCipher_bytes (d : Direction) (k : Spec.TripleDes.Schedule) (m : Mem) (p : Addr) :
    dirCipher d k (Spec.Aes.bytesAt m p 8) = (blockResult k d (Spec.TripleDes.blockAt m p)).toList := by
  cases d <;> simp only [dirCipher, Spec.TripleDes.cipher, Spec.TripleDes.invCipher, blockResult, ofFn_bytesAt]

/-- Ecb's kept registers and the callee-saved ones are the modes'. -/
theorem kept_sub : ∀ r ∈ kept, r ∈ Ecb.kept ∨ r ∈ preserved := by decide

theorem crypt_wp (d : Direction) {s : State} {B : Addr} {ws : List Region} {k : Spec.TripleDes.Schedule}
    (hB : s.gpr sb = B) (hS : ScrIn s B (dirCore d).total) (hR : Ready s B ws k) :
    WP isa (dirCore d).crypt s fun s' => s'.gpr sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Ready s' B ws k ∧ Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧
      (∀ j < (dirCore d).G, bytesAt s'.mem (blkAddr (dirCore d) B j) (4 * (dirCore d).bw) =
        dirCipher d k (bytesAt s.mem (blkAddr (dirCore d) B j) (4 * (dirCore d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfit : B.toNat + 8 * 72 ≤ 2 ^ 64 := hS.fit
  have hW : (⟨B, 8 * 72⟩ : Region) ∈ s.wr := hS.wr
  obtain ⟨⟨hk, hin, hd⟩, hkB⟩ := hR
  simp only [dirCore]
  refine WP.seq (wp_addi (n := sb) (by decide) (by decide) fun s₁ u₁ => wp_nil ?_)
  have r4₁ : s₁.gpr .r4 = B + BitVec.ofNat 64 512 := by rw [u₁.gpr, hB]; rfl
  have g₁ : ∀ r, r ≠ .r4 → s₁.gpr r = s.gpr r := u₁.other
  have m₁ : s₁.mem = s.mem := u₁.mem
  have rd₁ : s₁.rd = s.rd := u₁.rd
  have wr₁ : s₁.wr = s.wr := u₁.wr
  have r3₁ : s₁.gpr .r3 = s.gpr .r3 := g₁ _ (by decide)
  have r5₁ : s₁.gpr .r5 = B := by rw [g₁ _ (by decide)]; exact hB
  have cw : VG.Covers [⟨s₁.gpr .r4, 8⟩, ⟨s₁.gpr .r5, 512⟩] s₁.wr := VG.Covers.of_sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨B, 8 * 72⟩, by rw [wr₁]; exact hW, 512, r4₁, by show 512 + 8 ≤ 8 * 72; omega_using []⟩
    · exact ⟨⟨B, 8 * 72⟩, by rw [wr₁]; exact hW, 0, by simp [r5₁], by show 0 + 512 ≤ 8 * 72; omega_using []⟩
  have hp : Ecb.CallPre s₁ :=
    ⟨VG.Covers.cons (by rw [r3₁, rd₁, wr₁]; exact VG.Covers.one hin) (VG.Covers.right cw), cw,
      by rw [r3₁, r5₁]; exact hkB.sub_right (Region.sub_prefix (by decide)),
      by rw [r4₁, r5₁]; exact VG.Offset.disjoint_base _ (by decide) (by omega_using [hfit])⟩
  refine WP.mono (Ecb.call_ok d s₁ hp) fun s₂ h₂ => ?_
  have g₂ : ∀ r ∈ kept, s₂.gpr r = s.gpr r := fun r hr => by
    have h4 : r ≠ .r4 := by revert hr; decide +revert
    rcases kept_sub r hr with h | h
    · rw [h₂.reg r h, g₁ r h4]
    · rw [h₂.callee r h, g₁ r h4]
  have r3₂ : s₂.gpr .r3 = s.gpr .r3 := g₂ _ (by decide)
  have sub₂ : ∀ r ∈ [(⟨s₁.gpr .r4, 8⟩ : Region), ⟨s₁.gpr .r5, 512⟩], Region.Sub r ⟨B, 8 * 72⟩ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [r4₁]; exact VG.Offset.sub_base _ (by decide)
    · rw [r5₁]; exact Region.sub_prefix (by decide)
  have f₂ : Frame [⟨s₁.gpr .r4, 8⟩, ⟨s₁.gpr .r5, 512⟩] s.mem s₂.mem := by rw [← m₁]; exact h₂.mem
  have sched : Spec.TripleDes.scheduleAt s₂.mem (s₂.gpr .r3) = k := by
    rw [r3₂, scheduleAt_eq_of_frame _ f₂ fun r hr => hkB.sub_right (sub₂ r hr), hk]
  refine ⟨by rw [show sb = .r5 from rfl, h₂.reg _ (by decide), r5₁], g₂,
    ⟨⟨sched, by rw [h₂.rd, h₂.wr, rd₁, wr₁, r3₂]; exact hin, by rw [keyR, r3₂]; exact hd⟩,
      by rw [keyR, r3₂]; exact hkB⟩, f₂.sub fun r hr => ?_, fun j hj => ?_,
    by rw [h₂.rd, rd₁], by rw [h₂.wr, wr₁]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, by
        rw [r4₁]; exact VG.Offset.sub_base _ (by show 512 + 8 ≤ 8 * (bufSlot + 1); decide)⟩
    · exact ⟨_, List.mem_singleton_self _, by
        rw [r5₁]; exact Region.sub_prefix (by show 512 ≤ 8 * (bufSlot + 1); decide)⟩
  · obtain rfl : j = 0 := by omega_using [hj]
    have e : blkAddr (dirCore d) B 0 = s₁.gpr .r4 := by
      rw [r4₁]; simp [blkAddr, slotA, dirCore, bufSlot]
    simp only [dirCore] at e
    rw [e, bytesAt_eq, h₂.output, dirCipher_bytes, m₁, r3₁, hk]

/-- Triple DES's core for the direction `d` meets what the modes need. -/
def dirCoreSpec (d : Direction) : CoreSpec (dirCore d) where
  Key := Spec.TripleDes.Schedule
  cipher := dirCipher d
  KeyArgs := KeyArgs
  Ready := Ready
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.TripleDes.cipher, Spec.TripleDes.invCipher, dirCore]
  layout := layout d
  keyArgs_congr h e r w _ f := keyArgs_congr h e.r3 r w f
  ready_frame h e r w _ f hs _ := ready_frame h e.r3 r w f hs
  prepare_wp := prepare_wp d
  crypt_wp := crypt_wp d

end VG.Proof.TripleDes.PPC64LE.Mode

end

end

/-!
# Triple DES's core on 64 blocks for the modes on PPC64LE

`wideCoreSpec d`: the core of the bitsliced ECB on 64 blocks
(`Impl.TripleDes.PPC64LE.wideCore d`) meets what the modes need of a core
(`Proof.Modes.PPC64LE.CoreSpec`), as the core of one block does
(`ModeCore.lean`), with the same key and ciphers, its schedule apart from
its 200 slots. ECB on 64 blocks (`Bitsliced.ecb64_wp`) runs on the buffer, with the first
128 slots as its working space, and leaves the working space's and the
schedule's addresses in `r10` and `r7`, from which `sb` and `r3` come back.

`wideOne_ok d`: the block function on the buffer's first block
(`Impl.TripleDes.PPC64LE.wideOne d`) enciphers it as the core does
(`Proof.Modes.PPC64LE.OneOk`), for the blocks left after the groups of 64,
as the core of one block's code does (`crypt_wp`), with the block at slot
128 rather than 64.
-/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Mode

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE
open VG.Impl.Modes.PPC64LE (sb)
open VG.Proof.Modes.PPC64LE (coreRegion blkRegion blkAddr slotA CoreSpec Layout ScrIn kept OneOk)
open VG.Spec.Aes (bytesAt)
open VG.Spec.TripleDes (Direction)
open VG.Proof.TripleDes (dirCipher bytesAt_eq scheduleAt_eq_of_frame)

/-- The key's arguments, apart from the wide core's scratch buffer at `B` too. -/
def ReadyW (s : State) (B : Addr) (ws : List Region) (k : Spec.TripleDes.Schedule) : Prop :=
  KeyArgs s ws k ∧ (keyR s).Disjoint ⟨B, 8 * 200⟩

theorem readyW_frame {s s' : State} {B : Addr} {ws : List Region} {k : Spec.TripleDes.Schedule}
    {rs : List Region} (h : ReadyW s B ws k) (e : s'.gpr .r3 = s.gpr .r3) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, ∃ r' ∈ ws, Region.Sub r r') :
    ReadyW s' B ws k := by
  obtain ⟨⟨hk, hin, hd⟩, hB⟩ := h
  obtain hd' : ∀ r ∈ rs, (keyR s).Disjoint r := fun r hr => by
    obtain ⟨r', hr', hsub⟩ := hs r hr
    exact (hd r' hr').sub_right hsub
  refine ⟨⟨?_, by rw [hrd, hwr, e]; exact hin, by rw [keyR, e]; exact hd⟩, by rw [keyR, e]; exact hB⟩
  rw [e, scheduleAt_eq_of_frame _ hf hd', hk]

theorem layoutW (d : Direction) : Layout (wideCore d) :=
  ⟨by cases d <;> decide, .inl rfl, by cases d <;> decide, by cases d <;> decide, by cases d <;> decide⟩

theorem prepareW_wp (d : Direction) {s : State} {B : Addr} {rs : List Region} {k : Spec.TripleDes.Schedule}
    (hB : s.gpr sb = B) (_hS : ScrIn s B (wideCore d).total) (hm : (⟨B, 8 * (wideCore d).total⟩ : Region) ∈ rs)
    (hk : KeyArgs s rs k) :
    WP isa (wideCore d).prepare s fun s' => ReadyW s' B rs k ∧ s'.gpr sb = B ∧
      (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ Frame [coreRegion (wideCore d) B] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr :=
  wp_nil ⟨⟨hk, hk.2.2 _ hm⟩, hB, fun _ _ => rfl, Frame.refl _ _, rfl, rfl⟩

theorem blockOut_eq (k : Spec.TripleDes.Schedule) (d : Direction) (b : Spec.TripleDes.Block) :
    VG.Proof.TripleDes.Bitslice.blockOut k d b = blockResult k d b := by
  cases d <;> rfl

theorem ecb64Call_wp (d : Direction) {s : State} {Q : State → Prop}
    (h : WP isa (Bitslice.ecb64 d) s.callEntry fun s₂ => s₂.lr = s.callEntry.lr ∧ Q s₂) :
    WP isa (ecb64Call d) s Q := by
  cases d <;> exact Bitsliced.WP.callOf h

/-- `kept` but `r3`: the callee-saved registers. -/
theorem kept_cases : ∀ r ∈ kept, r = .r3 ∨ r ∈ preserved := by decide

theorem cryptW_wp (d : Direction) {s : State} {B : Addr} {ws : List Region} {k : Spec.TripleDes.Schedule}
    (hB : s.gpr sb = B) (hS : ScrIn s B (wideCore d).total) (hR : ReadyW s B ws k) :
    WP isa (wideCore d).crypt s fun s' => s'.gpr sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      ReadyW s' B ws k ∧ Frame [coreRegion (wideCore d) B] s.mem s'.mem ∧
      (∀ j < (wideCore d).G, bytesAt s'.mem (blkAddr (wideCore d) B j) (4 * (wideCore d).bw) =
        dirCipher d k (bytesAt s.mem (blkAddr (wideCore d) B j) (4 * (wideCore d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfit : B.toNat + 8 * 200 ≤ 2 ^ 64 := hS.fit
  have hW : (⟨B, 8 * 200⟩ : Region) ∈ s.wr := hS.wr
  obtain ⟨⟨hk, hin, hd⟩, hkB⟩ := hR
  simp only [wideCore]
  refine WP.seq (wp_mr fun s₁ u₁ => wp_addi (n := sb) (by decide) (by decide) fun s₃ u₃ => wp_nil ?_)
  obtain g₃ : ∀ r, r ≠ .r6 → r ≠ .r4 → s₃.gpr r = s.gpr r := fun r a b => by
    rw [u₃.other r b, u₁.other r a]
  obtain r6₃ : s₃.gpr .r6 = B := by rw [u₃.other _ (by decide), u₁.gpr]; exact hB
  obtain r4₃ : s₃.gpr .r4 = B + BitVec.ofNat 64 1024 := by
    rw [u₃.gpr, u₁.other _ (by decide), hB]; rfl
  obtain r3₃ : s₃.gpr .r3 = s.gpr .r3 := g₃ _ (by decide) (by decide)
  obtain m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₁.mem]
  obtain rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₁.rd]
  obtain wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₁.wr]
  obtain pre : Bitsliced.Ecb64Pre s₃ := by
    refine ⟨by rw [r3₃, rd₃, wr₃]; exact hin, ?_, ?_, ?_, ?_, ?_⟩
    · rw [r4₃, wr₃]
      exact Bitsliced.covers_of_sub hW (off := 1024) rfl (by show 1024 + 512 ≤ 8 * 200; omega_using [])
    · rw [r6₃, wr₃]
      exact ⟨_, hW, by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using []⟩
    · rw [r4₃, r3₃]; exact hkB.sub_right (VG.Offset.sub_base _ (by show 1024 + 512 ≤ 8 * 200; omega_using []))
    · rw [r6₃, r3₃]; exact hkB.sub_right (Region.sub_prefix (by show 1024 ≤ 8 * 200; omega_using []))
    · rw [r4₃, r6₃]; exact VG.Offset.disjoint_base _ (by omega_using []) (by omega_using [])
  -- the call: its entry changes only `r0`, `r11`, `r12` and the link register
  obtain ce : ∀ r, r ∉ linkRegs → s₃.callEntry.gpr r = s₃.gpr r := fun r h => State.callEntry_gpr s₃ h
  obtain e3 := ce .r3 (by decide)
  obtain e4 := ce .r4 (by decide)
  obtain e6 := ce .r6 (by decide)
  obtain pre' : Bitsliced.Ecb64Pre s₃.callEntry :=
    ⟨by rw [State.callEntry_rd, State.callEntry_wr, e3]; exact pre.key,
      by rw [State.callEntry_wr, e4]; exact pre.data, by rw [State.callEntry_wr, e6]; exact pre.buf,
      by rw [e3, e4]; exact pre.keyData, by rw [e3, e6]; exact pre.keyBuf, by rw [e4, e6]; exact pre.dataBuf⟩
  apply WP.seq
  refine ecb64Call_wp d (WP.mono (Bitsliced.WP.rdwr (Bitsliced.ecb64_wp d pre'))
    fun s₄ ⟨⟨p₄, l₄, r10₄, r7₄, f₄, b₄⟩, rd₄, wr₄, _⟩ => ⟨l₄, ?_⟩)
  simp only [State.callEntry_rd, State.callEntry_wr, State.callEntry_mem, e3, e4, e6] at rd₄ wr₄ f₄ b₄ r10₄ r7₄
  obtain p₄' : ∀ r ∈ preserved, s₄.gpr r = s₃.gpr r := fun r hr => by
    rw [p₄ r hr, ce r (preserved_not_link r hr)]
  refine wp_mr fun s₅ u₅ => wp_mr fun s₆ u₆ => wp_nil ?_
  rw [r10₄, r6₃] at u₅
  obtain r5₆ : s₆.gpr .r5 = B := by rw [u₆.other _ (by decide)]; exact u₅.gpr
  obtain r3₆ : s₆.gpr .r3 = s.gpr .r3 := by rw [u₆.gpr, u₅.other _ (by decide), r7₄, r3₃]
  obtain m₆ : s₆.mem = s₄.mem := by rw [u₆.mem, u₅.mem]
  obtain g₆ : ∀ r ∈ kept, s₆.gpr r = s.gpr r := fun r hr => by
    rcases kept_cases r hr with rfl | h
    · exact r3₆
    · have h3 : r ≠ .r3 := by revert h; decide +revert
      obtain h5 : r ≠ .r5 := by revert h; decide +revert
      obtain h4 : r ≠ .r4 := by revert h; decide +revert
      obtain h6 : r ≠ .r6 := by revert h; decide +revert
      rw [u₆.other r h3, u₅.other r h5, p₄' r h, g₃ r h6 h4]
  obtain sub : ∀ r ∈ [(⟨s₃.gpr .r6, 1024⟩ : Region), ⟨s₃.gpr .r4, 512⟩],
      Region.Sub r ⟨B, 8 * (wideBuf + 64)⟩ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [r6₃]; exact Region.sub_prefix (by decide)
    · rw [r4₃]; exact VG.Offset.sub_base _ (by decide)
  obtain f₆ : Frame [⟨s₃.gpr .r6, 1024⟩, ⟨s₃.gpr .r4, 512⟩] s.mem s₆.mem := by
    rw [m₆, ← m₃]; exact f₄
  obtain hkB' : ∀ r ∈ [(⟨s₃.gpr .r6, 1024⟩ : Region), ⟨s₃.gpr .r4, 512⟩],
      (keyR s).Disjoint r := fun r hr =>
      (hkB.sub_right (Region.sub_prefix (by decide))).sub_right (sub r hr)
  obtain sched : Spec.TripleDes.scheduleAt s₆.mem (s₆.gpr .r3) = k := by
    rw [r3₆, scheduleAt_eq_of_frame _ f₆ hkB', hk]
  refine ⟨r5₆, g₆, ⟨⟨sched, by rw [u₆.rd, u₅.rd, rd₄, rd₃, u₆.wr, u₅.wr, wr₄, wr₃, r3₆]; exact hin,
      by rw [keyR, r3₆]; exact hd⟩, by rw [keyR, r3₆]; exact hkB⟩,
    f₆.sub fun r hr => ⟨_, List.mem_singleton_self _, sub r hr⟩, fun j hj => ?_,
    by rw [u₆.rd, u₅.rd, rd₄, rd₃], by rw [u₆.wr, u₅.wr, wr₄, wr₃]⟩
  have hj64 : j < 64 := hj
  obtain e : blkAddr (wideCore d) B j = VG.Proof.TripleDes.Bitslice.wAt (s₃.gpr .r4) j := by
    rw [r4₃]; simp only [blkAddr, slotA, wideCore, wideBuf, VG.Proof.TripleDes.Bitslice.wAt]
  obtain b := b₄ j hj64
  simp only [wideCore] at e
  rw [e, bytesAt_eq, m₆, b, blockOut_eq, ← dirCipher_bytes, m₃, r3₃, hk]

/-- Triple DES's core on 64 blocks for the direction `d` meets what the modes need. -/
def wideCoreSpec (d : Direction) : CoreSpec (wideCore d) where
  Key := Spec.TripleDes.Schedule
  cipher := dirCipher d
  KeyArgs := KeyArgs
  Ready := ReadyW
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.TripleDes.cipher, Spec.TripleDes.invCipher, wideCore]
  layout := layoutW d
  keyArgs_congr h e r w _ f := keyArgs_congr h e.r3 r w f
  ready_frame h e r w _ f hs _ := readyW_frame h e.r3 r w f hs
  prepare_wp := prepareW_wp d
  crypt_wp := cryptW_wp d

/-- The block function on the wide core's first block. -/
theorem wideOne_ok (d : Direction) : OneOk (wideCoreSpec d) (wideOne d) := by
  intro s B ws (k : Spec.TripleDes.Schedule) hB hS hR
  have hfit : B.toNat + 8 * 200 ≤ 2 ^ 64 := hS.fit
  have hW : (⟨B, 8 * 200⟩ : Region) ∈ s.wr := hS.wr
  obtain ⟨⟨hk, hin, hd⟩, hkB⟩ := hR
  refine WP.seq (wp_addi (n := sb) (by decide) (by decide) fun s₁ u₁ => wp_nil ?_)
  obtain r4₁ : s₁.gpr .r4 = B + BitVec.ofNat 64 1024 := by rw [u₁.gpr, hB]; rfl
  have g₁ : ∀ r, r ≠ .r4 → s₁.gpr r = s.gpr r := u₁.other
  have m₁ : s₁.mem = s.mem := u₁.mem
  have rd₁ : s₁.rd = s.rd := u₁.rd
  have wr₁ : s₁.wr = s.wr := u₁.wr
  obtain r3₁ : s₁.gpr .r3 = s.gpr .r3 := g₁ _ (by decide)
  obtain r5₁ : s₁.gpr .r5 = B := by rw [g₁ _ (by decide)]; exact hB
  obtain cw : VG.Covers [⟨s₁.gpr .r4, 8⟩, ⟨s₁.gpr .r5, 512⟩] s₁.wr := VG.Covers.of_sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨B, 8 * 200⟩, by rw [wr₁]; exact hW, 1024, r4₁, by show 1024 + 8 ≤ 8 * 200; omega_using []⟩
    · exact ⟨⟨B, 8 * 200⟩, by rw [wr₁]; exact hW, 0, by simp [r5₁], by show 0 + 512 ≤ 8 * 200; omega_using []⟩
  obtain hp : Ecb.CallPre s₁ :=
    ⟨VG.Covers.cons (by rw [r3₁, rd₁, wr₁]; exact VG.Covers.one hin) (VG.Covers.right cw), cw,
      by rw [r3₁, r5₁]; exact hkB.sub_right (Region.sub_prefix (by decide)),
      by rw [r4₁, r5₁]; exact VG.Offset.disjoint_base _ (by decide) (by omega_using [hfit])⟩
  refine WP.mono (Ecb.call_ok d s₁ hp) fun s₂ h₂ => ?_
  obtain g₂ : ∀ r ∈ kept, s₂.gpr r = s.gpr r := fun r hr => by
    obtain h4 : r ≠ .r4 := by revert hr; decide +revert
    rcases kept_sub r hr with h | h
    · rw [h₂.reg r h, g₁ r h4]
    · rw [h₂.callee r h, g₁ r h4]
  obtain r3₂ : s₂.gpr .r3 = s.gpr .r3 := g₂ _ (by decide)
  obtain sub₂ : ∀ r ∈ [(⟨s₁.gpr .r4, 8⟩ : Region), ⟨s₁.gpr .r5, 512⟩], Region.Sub r ⟨B, 8 * 200⟩ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [r4₁]; exact VG.Offset.sub_base _ (by decide)
    · rw [r5₁]; exact Region.sub_prefix (by decide)
  obtain f₂ : Frame [⟨s₁.gpr .r4, 8⟩, ⟨s₁.gpr .r5, 512⟩] s.mem s₂.mem := by rw [← m₁]; exact h₂.mem
  obtain sched : Spec.TripleDes.scheduleAt s₂.mem (s₂.gpr .r3) = k := by
    rw [r3₂, scheduleAt_eq_of_frame _ f₂ fun r hr => hkB.sub_right (sub₂ r hr), hk]
  refine ⟨by rw [show sb = .r5 from rfl, h₂.reg _ (by decide), r5₁], g₂,
    ⟨⟨sched, by rw [h₂.rd, h₂.wr, rd₁, wr₁, r3₂]; exact hin, by rw [keyR, r3₂]; exact hd⟩,
      by rw [keyR, r3₂]; exact hkB⟩, f₂.sub fun r hr => ?_, ?_,
    by rw [h₂.rd, rd₁], by rw [h₂.wr, wr₁]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, by
        rw [r4₁]; exact VG.Offset.sub_base _ (by show 1024 + 8 ≤ 8 * (wideBuf + 64); decide)⟩
    · exact ⟨_, List.mem_singleton_self _, by
        rw [r5₁]; exact Region.sub_prefix (by show 512 ≤ 8 * (wideBuf + 64); decide)⟩
  · have e : blkAddr (wideCore d) B 0 = s₁.gpr .r4 := by
      rw [r4₁]; simp [blkAddr, slotA, wideCore, wideBuf]
    change bytesAt s₂.mem (blkAddr (wideCore d) B 0) 8 = dirCipher d k (bytesAt s.mem (blkAddr (wideCore d) B 0) 8)
    rw [e, bytesAt_eq, h₂.output, dirCipher_bytes, m₁, r3₁, hk]

end VG.Proof.TripleDes.PPC64LE.Mode
