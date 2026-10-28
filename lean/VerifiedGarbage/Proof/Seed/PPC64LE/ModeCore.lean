module

public import VerifiedGarbage.Proof.Modes.PPC64LE.Core
public import VerifiedGarbage.Impl.Seed.PPC64LE.Modes
public import VerifiedGarbage.Proof.Seed.ModeBytes
public import VerifiedGarbage.Proof.Seed.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Seed.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Seed.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# SEED's core for the modes on PPC64LE

`dirCoreSpec d`: SEED's core for the direction `d`
(`Impl.Seed.PPC64LE.dirCore d`) meets what the modes need of a core
(`Proof.Modes.PPC64LE.CoreSpec`), with the key a schedule, read in place
through `r3`, its cipher `Proof.Seed.dirCipher d`. The schedule is
readable and apart from the regions the mode writes (`KeyArgs`), and from
the scratch buffer (`Ready`), so nothing the mode or the core writes changes
it.

The core (`crypt_ok`) calls the blocks function on the buffer's block
(`WP.call`, with ECB's code, `blocks_correct`), which restores the
callee-saved registers, and leaves the working space's address in `r8` and
the key pointer at the first round's key (`EcbPost`), from which the core
takes `sb` and `r3` back.
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE.Mode

open VG VG.PPC64LE VG.Impl.Seed.PPC64LE VG.Proof.Seed.PPC64LE VG.PPC64LE.RegUpd
open VG.Proof.Modes.PPC64LE (coreRegion blkRegion blkAddr slotA CoreSpec Layout ScrIn kept)
open VG.Spec.Seed (Direction)
open VG.Spec.Aes (bytesAt)

/-- The schedule. -/
abbrev keyR (s : State) : Region := ⟨s.gpr .r3, 128⟩

/-- The schedule at `r3` is `k`, readable, and apart from the regions `rs`. -/
def KeyArgs (s : State) (rs : List Region) (k : Spec.Seed.Schedule) : Prop :=
  Spec.Seed.scheduleAt s.mem (s.gpr .r3) = k ∧ keyR s ∈ s.rd ∧ ∀ r ∈ rs, (keyR s).Disjoint r

/-- The key's arguments, apart from the scratch buffer at `B` too. -/
def Ready (s : State) (B : Addr) (ws : List Region) (k : Spec.Seed.Schedule) : Prop :=
  KeyArgs s ws k ∧ (keyR s).Disjoint ⟨B, 8 * (bufSlot + 8)⟩

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.Seed.Schedule} (h : KeyArgs s rs k)
    (e : s'.gpr .r3 = s.gpr .r3) (hrd : s'.rd = s.rd) (hf : Frame rs s.mem s'.mem) :
    KeyArgs s' rs k := by
  obtain ⟨hk, hin, hd⟩ := h
  refine ⟨?_, by rw [hrd, keyR, e]; exact hin, by rw [keyR, e]; exact hd⟩
  rw [e, Proof.Seed.scheduleAt_frame hf hd, hk]

theorem ready_frame {s s' : State} {B : Addr} {ws : List Region} {k : Spec.Seed.Schedule}
    {rs : List Region} (h : Ready s B ws k) (e : s'.gpr .r3 = s.gpr .r3) (hrd : s'.rd = s.rd)
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, ∃ r' ∈ ws, Region.Sub r r') :
    Ready s' B ws k := by
  obtain ⟨⟨hk, hin, hd⟩, hB⟩ := h
  have hd' : ∀ r ∈ rs, (keyR s).Disjoint r := fun r hr => by
    obtain ⟨r', hr', hsub⟩ := hs r hr
    exact (hd r' hr').sub_right hsub
  refine ⟨⟨?_, by rw [hrd, keyR, e]; exact hin, by rw [keyR, e]; exact hd⟩, by rw [keyR, e]; exact hB⟩
  rw [e, Proof.Seed.scheduleAt_frame hf hd', hk]

/-- The key stays ready through what the core writes, its slots. -/
theorem ready_core {s s' : State} {B : Addr} {ws : List Region} {k : Spec.Seed.Schedule}
    (h : Ready s B ws k) (e : s'.gpr .r3 = s.gpr .r3) (hrd : s'.rd = s.rd)
    (hf : Frame [⟨B, 8 * (bufSlot + 2)⟩] s.mem s'.mem) : Ready s' B ws k := by
  obtain ⟨⟨hk, hin, hd⟩, hB⟩ := h
  refine ⟨⟨?_, by rw [hrd, keyR, e]; exact hin, by rw [keyR, e]; exact hd⟩, by rw [keyR, e]; exact hB⟩
  rw [e, Proof.Seed.scheduleAt_frame hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hB.sub_right (Region.sub_prefix (by omega_arith)), hk]

theorem layout (d : Direction) : Layout (dirCore d) :=
  ⟨by cases d <;> decide, .inr rfl, by cases d <;> decide, by cases d <;> decide, by cases d <;> decide⟩

theorem prepare_wp (d : Direction) {s : State} {B : Addr} {rs : List Region} {k : Spec.Seed.Schedule}
    (hB : s.gpr .r5 = B) (_hS : ScrIn s B (dirCore d).total)
    (hm : (⟨B, 8 * (dirCore d).total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k) :
    WP isa (dirCore d).prepare s fun s' => Ready s' B rs k ∧ s'.gpr .r5 = B ∧
      (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr :=
  wp_nil ⟨⟨hk, hk.2.2 _ hm⟩, hB, fun _ _ => rfl, Frame.refl _ _, rfl, rfl⟩

/-! ## The block -/

/-- The buffer's address. -/
abbrev bufA (B : Addr) : Addr := B + BitVec.ofNat 64 (8 * bufSlot)

/-- The block function in the direction `d`, on the modes' blocks. -/
private theorem dirCipher_bytes (d : Direction) (k : Spec.Seed.Schedule) (m : Mem) (p : Addr) :
    Proof.Seed.dirCipher d k (bytesAt m p 16) = (cipher d k (Spec.Seed.blockAt m p)).toList := by
  have e : (Vector.ofFn fun i : Fin 16 => (Spec.Seed.blockAt m p).toList.getD i.val 0) =
      Spec.Seed.blockAt m p := by
    apply Vector.ext; intro i hi; simp
  cases d <;> simp only [Proof.Seed.dirCipher, Spec.Seed.cipher, Spec.Seed.invCipher, cipher,
    Proof.Seed.bytesAt_eq, e]

/-- What the core's call of the blocks function gives: ECB's code, with what
its proof gives beyond the blocks functions' contract (`EcbPost`). -/
def blocksCall (d : Direction) : Contract isa where
  pre := (contract d 1088).pre
  post := EcbPost d
  pub := (contract d 1088).pub

theorem blocks_correct (d : Direction) (s : State) (hs : (blocksCall d).pre s) :
    ∃ t s', Exec isa (ecb d) s t s' ∧ abiPreserved s s' ∧ (blocksCall d).post s s' := by
  obtain ⟨t, s', he, ha, -, hp⟩ := ecb_correct' d (n := 1088) (by decide) s hs
  exact ⟨t, s', he, ha, hp⟩

/-- A call of the blocks function in the direction `d`. -/
theorem blockCall_wp (d : Direction) {s : State} {rd wr : List Region}
    (hpre : (blocksCall d).pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Frame wr s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      (blocksCall d).post (s.callEntry.withRegions rd wr) (s'.withRegions rd wr) → Q s') :
    WP isa (blockCall d) s Q := by
  cases d
  · exact WP.call (blocks_correct .encrypt) hpre hc hw (fun s' a b c e f _ g => hQ s' a b c e f g)
      (by lit_decide)
  · exact WP.call (blocks_correct .decrypt) hpre hc hw (fun s' a b c e f _ g => hQ s' a b c e f g)
      (by lit_decide)

theorem not_head : ∀ r ∈ kept, r ≠ .r3 → r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ∈ preserved := by decide

/-- What the core does to its block, and keeps. -/
theorem crypt_ok (d : Direction) {s : State} {B : Addr} (hB : s.gpr .r5 = B)
    (hS : ScrIn s B (bufSlot + 8)) (hk : (keyR s).Disjoint ⟨B, 8 * (bufSlot + 8)⟩)
    (hkin : keyR s ∈ s.rd) :
    WP isa (dirCore d).crypt s fun s' => s'.gpr .r5 = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Frame [⟨B, 8 * (bufSlot + 2)⟩] s.mem s'.mem ∧
      bytesAt s'.mem (bufA B) 16 =
        Proof.Seed.dirCipher d (Spec.Seed.scheduleAt s.mem (s.gpr .r3)) (bytesAt s.mem (bufA B) 16) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hbs : bufSlot = 136 := rfl
  have hfit : B.toNat + 8 * (bufSlot + 8) ≤ 2 ^ 64 := hS.fit
  have hW : (⟨B, 8 * (bufSlot + 8)⟩ : Region) ∈ s.wr := hS.wr
  have hB' : s.gpr Impl.Modes.PPC64LE.sb = B := hB
  show WP isa (.seq (.block cryptHead) (.seq (blockCall d) (.block (cryptTail d)))) s _
  -- The arguments.
  refine WP.seq (wp_addi (by decide) (by decide) fun s₁ u₁ => wp_mr fun s₂ u₂ =>
    wp_li (by decide) fun s₃ u₃ => wp_nil ?_)
  have g₃ : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s₃.gpr r = s.gpr r := fun r a b c => by
    rw [u₃.other r b, u₂.other r c, u₁.other r a]
  have r3₃ : s₃.gpr .r3 = s.gpr .r3 := g₃ _ (by decide) (by decide) (by decide)
  have r4₃ : s₃.gpr .r4 = bufA B := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hB']
  have r6₃ : s₃.gpr .r6 = B := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hB']
  have r5₃ : s₃.gpr .r5 = BitVec.ofNat 64 1 := u₃.gpr
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  -- The call, on the buffer's block, with the working space in the first 136 slots.
  let wr : List Region := [⟨bufA B, 16⟩, ⟨B, 1088⟩]
  let E := s₃.callEntry.withRegions [keyR s] wr
  have c3 : E.gpr .r3 = s.gpr .r3 := by rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), r3₃]
  have c4 : E.gpr .r4 = bufA B := by rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), r4₃]
  have c5 : (E.gpr .r5).toNat = 1 := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), r5₃]; rfl
  have c6 : E.gpr .r6 = B := by rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), r6₃]
  have cm : E.mem = s.mem := by rw [State.withRegions_mem, State.callEntry_mem, m₃]
  have hP : (bufA B).toNat = B.toNat + 8 * bufSlot := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hcov : Covers wr s.wr := Covers.of_sub fun r hr => by
    simp only [wr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hW, 8 * bufSlot, rfl, by simp only; omega⟩
    · exact ⟨_, hW, 0, (BitVec.add_zero _).symm, by simp only; omega⟩
  refine WP.seq (blockCall_wp d (rd := [keyR s]) (wr := wr) ?_
    (Covers.append_left (Covers.left (Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [rd₃]; exact hkin))
      (Covers.right (by rw [wr₃]; exact hcov))) (by rw [wr₃]; exact hcov)
    (fun s' rd' wr' _ hf hp hpost => ?_))
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [State.withRegions_rd]; rw [c3]
    · simp only [State.withRegions_wr]; rw [c4, c5, c6]
    · rw [c3, c4, c5]
      exact hk.sub_right (Offset.sub_base _ (by omega))
    · rw [c3, c6]
      exact hk.sub_right (Region.sub_prefix (by omega))
    · rw [c4, c5, c6]
      exact Offset.disjoint_base B (by omega) (by omega)
    · rw [c4, c5, hP]; omega
  -- `sb` and `r3` back.
  have hm' : (s'.withRegions [keyR s] wr).mem = s'.mem := rfl
  have r8' : s'.gpr .r8 = B := by
    have := hpost.r8
    rwa [State.withRegions_gpr, c6] at this
  have r3' : s'.gpr .r3 = s.gpr .r3 + BitVec.ofNat 64 (keyStart d) := by
    have := hpost.r3
    rwa [State.withRegions_gpr, c3] at this
  refine wp_mr fun s₄ u₄ => wp_subi (by decide) (Nat.le_of_lt (keyStart_lt d)) fun s₅ u₅ => wp_nil ?_
  have rd₅ : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, rd', rd₃]
  have wr₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, wr', wr₃]
  have m₅ : s₅.mem = s'.mem := by rw [u₅.mem, u₄.mem]
  refine ⟨?_, fun r hr => ?_, ?_, ?_, rd₅, wr₅⟩
  · rw [u₅.other _ (by decide)]; exact u₄.gpr.trans r8'
  · by_cases e3 : r = .r3
    · subst e3
      rw [u₅.gpr, u₄.other _ (show Reg.r3 ≠ Impl.Modes.PPC64LE.sb by decide), r3', BitVec.add_sub_cancel]
    obtain ⟨h4, h5, h6, hp'⟩ := not_head r hr e3
    rw [u₅.other r e3, u₄.other r (show r ≠ Impl.Modes.PPC64LE.sb from h5), hp r hp', g₃ r h4 h5 h6]
  · rw [m₅, ← m₃]
    refine hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [wr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.sub_base _ (by omega)
    · exact Region.sub_prefix (by omega)
  · have e := hpost.done 0 (by rw [c5]; decide)
    rw [hm', cm, c3, c4, show bufA B + BitVec.ofNat 64 (16 * 0) = bufA B from BitVec.add_zero _] at e
    rw [m₅, dirCipher_bytes, Proof.Seed.bytesAt_eq, e]

/-- SEED's core meets what the modes need. -/
def dirCoreSpec (d : Direction) : CoreSpec (dirCore d) where
  Key := Spec.Seed.Schedule
  cipher := Proof.Seed.dirCipher d
  KeyArgs := KeyArgs
  Ready := Ready
  cipher_len _ _ := by cases d <;> simp [Proof.Seed.dirCipher, Spec.Seed.cipher, Spec.Seed.invCipher, dirCore]
  layout := layout d
  keyArgs_congr h e r _ _ f := keyArgs_congr h e.r3 r f
  ready_frame h e r _ _ f hs _ := ready_frame h e.r3 r f hs
  prepare_wp := prepare_wp d
  crypt_wp {s B ws k} hB hS hR := by
    refine WP.mono (crypt_ok d hB hS hR.2 hR.1.2.1) fun s' ⟨h5, hk, hf, hb, hrd, hwr⟩ => ?_
    refine ⟨h5, hk, ready_core hR (hk .r3 (by decide)) hrd hf, hf, fun j hj => ?_, hrd, hwr⟩
    obtain rfl : j = 0 := by simpa [dirCore] using hj
    have e : blkAddr (dirCore d) B 0 = bufA B := by simp [blkAddr, slotA, dirCore]
    rw [show 4 * (dirCore d).bw = 16 from rfl, e, hb, hR.1.1]

end VG.Proof.Seed.PPC64LE.Mode
