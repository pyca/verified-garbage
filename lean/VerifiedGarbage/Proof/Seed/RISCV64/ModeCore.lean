module

public import VerifiedGarbage.Proof.Modes.RISCV64.Core
public import VerifiedGarbage.Impl.Seed.RISCV64.Modes
public import VerifiedGarbage.Proof.Seed.ModeBytes
public import VerifiedGarbage.Proof.Seed.RISCV64.Ecb
import VerifiedGarbage.Proof.Seed.RISCV64.Batch
public import VerifiedGarbage.Proof.Seed.RISCV64.Setup
import VerifiedGarbage.Proof.Seed.Rounds
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# SEED's core for the modes on RISC-V

`dirCoreSpec d`: SEED's core for the direction `d`
(`Impl.Seed.RISCV64.dirCore d`) meets what the modes need of a core
(`Proof.Modes.RISCV64.CoreSpec`), with the key a schedule, read in place
through `a0`, its cipher `Proof.Seed.dirCipher d`, as on PPC64LE. The
schedule is readable and apart from the regions the mode writes (`KeyArgs`),
and from the frame (`Ready`), so nothing the mode or the core writes changes
it.

The core (`crypt_ok`) is ECB's prologue (`prologue_ok`), on ECB's scratch
buffer `ecbOff` bytes into the frame (at `E`), then ECB's batch taken apart
(`Batch.lean`): the copy in of one block (`copyIn_loop`), the rounds
(`rounds_ok`) and the copy out (`copyOut_loop`), and ECB's epilogue
(`Spill.restore_wp`). Around the block the modes' `s1`–`s3` wait in `a1`,
`a2` and `ra`, and `ra` in its slot.
-/

@[expose] public section

namespace VG.Proof.Seed.RISCV64.Mode

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Seed.RISCV64 VG.Proof.Seed.RISCV64
open VG.Impl.Aes.RISCV64 (sb movR t0 t1 t2)
open VG.Proof.Modes.RISCV64 (coreRegion blkRegion blkAddr slotA CoreSpec Layout ScrIn kept KeptBut)
open VG.Spec.Seed (Direction)
open VG.Spec.Aes (bytesAt)

/-- The schedule. -/
abbrev keyR (s : State) : Region := ⟨s.gpr .a0, 128⟩

/-- The schedule at `a0` is `k`, readable, and apart from the regions `rs`. -/
def KeyArgs (s : State) (rs : List Region) (k : Spec.Seed.Schedule) : Prop :=
  Spec.Seed.scheduleAt s.mem (s.gpr .a0) = k ∧ keyR s ∈ s.rd ++ s.wr ∧ ∀ r ∈ rs, (keyR s).Disjoint r

/-- The key's arguments, apart from the frame at `B` too. -/
def Ready (s : State) (B : Addr) (ws : List Region) (k : Spec.Seed.Schedule) : Prop :=
  KeyArgs s ws k ∧ (keyR s).Disjoint ⟨B, 1104⟩

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.Seed.Schedule} (h : KeyArgs s rs k)
    (e : s'.gpr .a0 = s.gpr .a0) (hrd : s'.rd = s.rd) (hwr : ∃ ws, s'.wr = ws ++ s.wr)
    (hf : Frame rs s.mem s'.mem) : KeyArgs s' rs k := by
  obtain ⟨hk, hin, hd⟩ := h
  obtain ⟨ws, hw⟩ := hwr
  refine ⟨?_, ?_, by rw [keyR, e]; exact hd⟩
  · rw [e, Proof.Seed.scheduleAt_frame hf hd, hk]
  · rw [hrd, hw, keyR, e]
    rcases List.mem_append.mp hin with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_append_right _ h)

theorem ready_frame {s s' : State} {B : Addr} {ws : List Region} {k : Spec.Seed.Schedule}
    {rs : List Region} (h : Ready s B ws k) (e : s'.gpr .a0 = s.gpr .a0) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, ∃ r' ∈ ws, Region.Sub r r') :
    Ready s' B ws k := by
  obtain ⟨⟨hk, hin, hd⟩, hB⟩ := h
  have hd' : ∀ r ∈ rs, (keyR s).Disjoint r := fun r hr => by
    obtain ⟨r', hr', hsub⟩ := hs r hr
    exact (hd r' hr').sub_right hsub
  refine ⟨⟨?_, by rw [hrd, hwr, keyR, e]; exact hin, by rw [keyR, e]; exact hd⟩, by rw [keyR, e]; exact hB⟩
  rw [e, Proof.Seed.scheduleAt_frame hf hd', hk]

theorem layout (d : Direction) : Layout (dirCore d) :=
  ⟨by cases d <;> decide, .inr rfl, by cases d <;> decide, by cases d <;> decide, by cases d <;> decide,
    by cases d <;> decide, by cases d <;> decide⟩

theorem prepare_wp (d : Direction) {s : State} {B : Addr} {rs : List Region} {k : Spec.Seed.Schedule}
    (hB : s.gpr Impl.Modes.RISCV64.sb = B) (_hS : ScrIn s B (dirCore d).total)
    (hm : (⟨B, 8 * (dirCore d).total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k) :
    WP isa (dirCore d).prepare s fun s' => Ready s' B rs k ∧ s'.gpr Impl.Modes.RISCV64.sb = B ∧
      (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr :=
  WP.block_nil ⟨⟨hk, hk.2.2 _ hm⟩, hB, fun _ _ => rfl, Frame.refl _ _, rfl, rfl⟩

/-! ## The block -/

/-- ECB's scratch buffer, the core's buffer and `ra`'s slot, in the frame at `B`. -/
abbrev ecbA (B : Addr) : Addr := B + BitVec.ofNat 64 48
abbrev bufA (B : Addr) : Addr := ecbA B + BitVec.ofNat 64 1032
abbrev raA (B : Addr) : Addr := ecbA B + BitVec.ofNat 64 1048

/-- The block function in the direction `d`, on the modes' blocks. -/
theorem dirCipher_bytes (d : Direction) (k : Spec.Seed.Schedule) (m : Mem) (p : Addr) :
    Proof.Seed.dirCipher d k (bytesAt m p 16) = (cipher d k (Spec.Seed.blockAt m p)).toList := by
  have e : (Vector.ofFn fun i : Fin 16 => (Spec.Seed.blockAt m p).toList.getD i.val 0) =
      Spec.Seed.blockAt m p := by
    apply Vector.ext; intro i hi; simp
  cases d <;> simp only [Proof.Seed.dirCipher, Spec.Seed.cipher, Spec.Seed.invCipher, cipher,
    Proof.Seed.bytesAt_eq, e]

/-- An 8-byte aligned offset in the frame. -/
theorem frame_al {B : Addr} (hal : B.toNat % 16 = 0) (hfit : B.toNat + 1104 ≤ 2 ^ 64) {k : Nat}
    (hk : k % 8 = 0) (hk' : k < 1104) : (B + BitVec.ofNat 64 k).toNat % 8 = 0 := by
  have h₁ : k < 2 ^ 64 := by omega
  have h₂ : B.toNat + k < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂]
  omega

theorem coreIn_eq (d : Direction) : coreIn d =
    ([.addi t0 Impl.Modes.RISCV64.sb (ecbOff : Int)] : List Instr) ++ prologue t0 ++ park ++ copyFrom d := rfl

theorem coreOut_eq (d : Direction) : coreOut d =
    ([.addi .a0 .a0 (-(keyStart d : Int))] : List Instr) ++ seedRestore ++
      ([.addi .s1 .a1 0, .addi .s2 .a2 0, .addi .s3 .ra 0, .load .d .ra sb raOff,
        .addi Impl.Modes.RISCV64.sb sb (-(ecbOff : Int))] : List Instr) := rfl

/-- The registers the prologue saves: all those the caller expects preserved. -/
theorem savedOffs_kept : ∀ r ∈ kept, r ≠ .a0 → r ≠ .ra → r ∈ savedOffs.map Prod.fst := by decide

/-- What the core does to its block, and keeps. -/
theorem crypt_ok (d : Direction) {s : State} {B : Addr} (hB : s.gpr .s4 = B)
    (hS : ScrIn s B (bufSlot + 3)) (hk : (keyR s).Disjoint ⟨B, 1104⟩)
    (hkin : keyR s ∈ s.rd ++ s.wr) :
    WP isa (coreCrypt d) s fun s' => s'.gpr .s4 = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Frame [⟨ecbA B, 1056⟩] s.mem s'.mem ∧
      bytesAt s'.mem (bufA B) 16 =
        Proof.Seed.dirCipher d (Spec.Seed.scheduleAt s.mem (s.gpr .a0)) (bytesAt s.mem (bufA B) 16) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  let E := ecbA B
  let P := bufA B
  have hfit : B.toNat + 1104 ≤ 2 ^ 64 := hS.fit
  have hal : B.toNat % 16 = 0 := hS.al
  have hW : (⟨B, 1104⟩ : Region) ∈ s.wr := hS.whole (by decide)
  have hEk : ∀ k, E + BitVec.ofNat 64 k = B + BitVec.ofNat 64 (48 + k) := fun k => Offset.add_add _ _ _
  have hin : ∀ k n, k + n ≤ 1056 → InRegions s.wr (E + BitVec.ofNat 64 k) n := fun k n h =>
    ⟨_, hW, by rw [hEk]; exact Offset.contains_base B (by omega) (by omega)⟩
  have hEal : E.toNat % 8 = 0 := frame_al hal hfit (by decide) (by decide)
  have hEsub : ∀ k n, k + n ≤ 1056 → Region.Sub ⟨E + BitVec.ofNat 64 k, n⟩ ⟨B, 1104⟩ :=
    fun k n h => by rw [hEk]; exact Offset.sub_base B (by omega)
  have hP : P = E + BitVec.ofNat 64 1032 := rfl
  have hRA : raA B = E + BitVec.ofNat 64 1048 := rfl
  have hscr : ∀ t : State, t.gpr sb = E → scratchR t = ⟨E, 8 * scratchSlots⟩ := fun t ht => by
    simp only [scratchR, ht]
  have harr : ∀ t : State, t.gpr sb = E → arraysR t = ⟨E + BitVec.ofNat 64 320, 512⟩ := fun t ht => by
    simp only [arraysR, ht]
  have hwork : ∀ t : State, t.gpr sb = E → workR t = ⟨E + BitVec.ofNat 64 0, 832⟩ := fun t ht => by
    simp only [workR, ht, BitVec.add_zero]
  -- ECB's base and prologue.
  rw [coreCrypt]
  apply WP.seq
  rw [coreIn_eq, WP.block_append_iff (M := isa), WP.block_append_iff (M := isa),
    WP.block_append_iff (M := isa)]
  refine wp_addi (by decide) fun s₀ u₀ => WP.block_nil ?_
  have t0₀ : s₀.gpr .t0 = E := u₀.gpr.trans (by show s.gpr .s4 + _ = _; rw [hB]; rfl)
  refine WP.mono (prologue_ok (r := t0) (by rw [show t0 = Reg.t0 from rfl, t0₀]; exact hEal)
    (by rw [show t0 = Reg.t0 from rfl, t0₀, u₀.wr]
        exact ⟨_, hW, Offset.contains_base B (d := 48) (by decide) (by decide)⟩))
    fun s₁ P₁ => ?_
  have G₁ : ∀ r, r ≠ .a5 → r ≠ .a3 → r ≠ .t0 → r ≠ .t1 → s₁.gpr r = s.gpr r := fun r a b c e => by
    rw [P₁.regs r a b c e, u₀.other r c]
  have sb₁ : s₁.gpr sb = E := by rw [P₁.base]; exact t0₀
  have wr₁ : s₁.wr = s.wr := by rw [P₁.wr, u₀.wr]
  have rd₁ : s₁.rd = s.rd := by rw [P₁.rd, u₀.rd]
  have sp₁ : s₁.sp = s.sp := by rw [P₁.sp, u₀.sp]
  have f₁ : Frame [⟨E, 8 * scratchSlots⟩] s.mem s₁.mem := by
    have := P₁.frame; rw [show s₀.gpr t0 = E from t0₀, u₀.mem] at this; exact this
  -- The modes' state parked, and `ra` in its slot.
  rw [park]
  refine wp_sd (a := raA B) (by decide) (by rw [sb₁]; rfl) (by rw [hRA, hEk]; exact frame_al hal hfit (by decide) (by decide))
    (by rw [wr₁, hRA]; exact hin _ _ (by decide)) fun s₂ m₂ => ?_
  simp only [movR]
  refine wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ => WP.block_nil ?_
  have G₅ : ∀ r, r ≠ .a1 → r ≠ .a2 → r ≠ .ra → s₅.gpr r = s₂.gpr r := fun r a b c => by
    rw [u₅.other r c, u₄.other r b, u₃.other r a]
  have st₅ : s₅.gpr .a1 = s.gpr .s1 ∧ s₅.gpr .a2 = s.gpr .s2 ∧ s₅.gpr .ra = s.gpr .s3 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, m₂.gpr,
        G₁ _ (by decide) (by decide) (by decide) (by decide)]
    · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), m₂.gpr,
        G₁ _ (by decide) (by decide) (by decide) (by decide)]
    · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr,
        G₁ _ (by decide) (by decide) (by decide) (by decide)]
  have mem₅ : s₅.mem = s₁.mem.writeW (raA B) (s.gpr .ra) := by
    rw [u₅.mem, u₄.mem, u₃.mem, m₂.mem, G₁ _ (by decide) (by decide) (by decide) (by decide)]
  have sb₅ : s₅.gpr sb = E := by rw [G₅ _ (by decide) (by decide) (by decide), m₂.gpr, sb₁]
  have wr₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, m₂.wr, wr₁]
  have rd₅ : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, m₂.rd, rd₁]
  have sp₅ : s₅.sp = s.sp := by rw [u₅.sp, u₄.sp, u₃.sp, m₂.sp, sp₁]
  -- The memory so far: ECB's scratch buffer and `ra`'s slot.
  have FA : Frame [⟨E, 8 * scratchSlots⟩, ⟨raA B, 8⟩] s.mem s₅.mem := by
    rw [mem₅]
    exact (f₁.mono (by simp)).writeW (r := ⟨raA B, 8⟩) (by simp) _ (Region.contains_self _ _)
  have FR : Frame [⟨raA B, 8⟩] s₁.mem s₅.mem := by
    rw [mem₅]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  -- The key pointer, and one block to copy in.
  rw [copyFrom]
  simp only [movR]
  refine wp_addi (keyStart_lt d) fun s₆ u₆ => ?_
  refine WP.cons (exec_li (d := t2) (imm := 1) (by decide)) ?_
  have u₇ := Upd.write s₆ t2 (BitVec.ofInt 64 1)
  generalize s₆.write t2 (BitVec.ofInt 64 1) = s₇ at u₇ ⊢
  refine wp_addi (by decide) fun s₈ u₈ => wp_mv fun s₉ u₉ => WP.block_nil ?_
  have G₉ : ∀ r, r ≠ .a0 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → s₉.gpr r = s₅.gpr r := fun r a b c e => by
    rw [u₉.other r e, u₈.other r c, u₇.other r b, u₆.other r a]
  have sb₉ : s₉.gpr sb = E := by
    rw [G₉ _ (by decide) (by decide) (by decide) (by decide), sb₅]
  have a0₉ : s₉.gpr .a0 = s.gpr .a0 + BitVec.ofNat 64 (keyStart d) := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr,
      G₅ _ (by decide) (by decide) (by decide), m₂.gpr, G₁ _ (by decide) (by decide) (by decide) (by decide)]
  have t3₉ : s₉.gpr .t3 = P := by
    rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), sb₅]; rfl
  have t4₉ : s₉.gpr .t4 = E := by
    rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), sb₅]
  have t2₉ : s₉.gpr .t2 = BitVec.ofNat 64 1 := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide)]; exact u₇.gpr
  have mem₉ : s₉.mem = s₅.mem := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  have wr₉ : s₉.wr = s.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅]
  have rd₉ : s₉.rd = s.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, rd₅]
  have sp₉ : s₉.sp = s.sp := by rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, sp₅]
  have room₉ : Room s₉ := room_congr P₁.room (by rw [sb₉, sb₁]) (by rw [wr₉, wr₁])
  have Pdat : ∀ w < 4, InRegions s.wr (P + BitVec.ofNat 64 (16 * 0 + 4 * w)) 4 := fun w hw => by
    rw [hP, Offset.add_add]; exact hin _ _ (by omega)
  have Parr : ∀ t : State, t.gpr sb = E → Region.Disjoint ⟨P, 16 * 1⟩ (arraysR t) := fun t ht => by
    rw [harr t ht, hP]; exact Offset.disjoint E (by omega) (by omega) (by omega)
  have pre₉ : CopyPre s₉ P 1 := by
    refine ⟨room₉, by omega, fun b hb w hw => ?_, Parr s₉ sb₉⟩
    obtain rfl : b = 0 := by omega
    obtain ⟨r, hr, hc⟩ := Pdat w hw
    exact ⟨r, by rw [rd₉, wr₉]; exact List.mem_append_right _ hr, hc⟩
  have inv₉ : CopyInInv s₉ P 1 (1 - 1) s₉ := by
    refine ⟨by omega, by rw [t3₉]; simp, by rw [t4₉, sb₉]; simp, by rw [t2₉], fun w _ b hb => by omega,
      Frame.refl _ _, fun _ _ => rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.mono (copyIn_loop pre₉ 1 s₉ inv₉ (by omega) (by omega)) fun s₁₀ i₁₀ => ?_)
  have sb₁₀ : s₁₀.gpr sb = E := (i₁₀.regs _ sb_copyRegs).trans sb₉
  have room₁₀ : Room s₁₀ := room_congr room₉ (by rw [sb₁₀, sb₉]) i₁₀.wr
  have f₁₀ : Frame [arraysR s₉] s₅.mem s₁₀.mem := by rw [← mem₉]; exact i₁₀.frame
  have hq₁₀ : quad s₁₀ 0 = decodeQ (Spec.Seed.blockAt s.mem P) := by
    rw [quad_of_lanes (m := s₉.mem) (p := P) fun w hw => i₁₀.lanes w hw 0 (by omega)]
    rw [show P + BitVec.ofNat 64 (16 * 0) = P by simp, mem₉, blockAt_frame FA fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint_base E (by unfold scratchSlots; omega) (by omega)
      · exact Offset.disjoint E (by omega) (by omega) (by omega)]
  -- The masks, and the keys.
  have masks₁₀ : Masks s₁₀ := by
    refine P₁.masks.frame' (rs := [⟨raA B, 8⟩, arraysR s₉]) (by rw [sb₁₀, sb₁])
      (by show s₁₀.gpr .a3 = s₁.gpr .a3; rw [i₁₀.regs _ cr_a3, G₉ _ (by decide) (by decide) (by decide) (by decide),
        G₅ _ (by decide) (by decide) (by decide), m₂.gpr])
      ((FR.mono (by simp)).trans (f₁₀.mono (by simp))) fun r hr => ?_
    have hm : masksR s₁ = ⟨E + BitVec.ofNat 64 832, 104⟩ := by rw [masksR, sb₁]; rfl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hm]
    rcases hr with rfl | rfl
    · exact Offset.disjoint E (by omega) (by omega) (by omega)
    · rw [harr s₉ sb₉]; exact Offset.disjoint E (by omega) (by omega) (by omega)
  have a0₁₀ : s₁₀.gpr .a0 = s.gpr .a0 + BitVec.ofNat 64 (keyStart d) := (i₁₀.regs _ cr_a0).trans a0₉
  have hkB : ∀ j < 16, Region.Disjoint ⟨s.gpr .a0 + BitVec.ofNat 64 (keyOff d j), 8⟩ ⟨B, 1104⟩ :=
    fun j hj => hk.sub_left (Offset.sub_base _ (keyOff_le d hj))
  have hEB : Region.Sub ⟨E, 8 * scratchSlots⟩ ⟨B, 1104⟩ := Offset.sub_base B (by decide)
  have keys₁₀ : KeysOk d s₁₀ (s₁₀.gpr .a0) := by
    intro j hj
    have hle := keyOff_le d hj
    have hkin' : keyR s ∈ s₁₀.rd ++ s₁₀.wr := by rw [i₁₀.rd, i₁₀.wr, rd₉, wr₉]; exact hkin
    rw [a0₁₀, hscr s₁₀ sb₁₀, kp_start _ _ hj]
    refine ⟨⟨_, hkin', Offset.contains_base _ (by omega) (by omega)⟩, ?_, (hkB j hj).sub_right hEB⟩
    rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add]
    exact ⟨_, hkin', Offset.contains_base _ (by omega) (by omega)⟩
  have FB : ∀ {m : Mem}, Frame [⟨E, 8 * scratchSlots⟩, ⟨raA B, 8⟩] s.mem m → Frame [⟨B, 1104⟩] s.mem m :=
    fun h => h.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_singleton_self _, hEB⟩
      · exact ⟨_, List.mem_singleton_self _, hEsub 1048 8 (by decide)⟩
  have hkeys : ∀ j < 16, keysAt d s₁₀.mem (s₁₀.gpr .a0) j =
      keysAt d s.mem (s.gpr .a0 + BitVec.ofNat 64 (keyStart d)) j := by
    intro j hj
    rw [a0₁₀]
    have f : Frame [⟨B, 1104⟩] s.mem s₁₀.mem :=
      (FB FA).trans (f₁₀.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        refine ⟨_, List.mem_singleton_self _, ?_⟩
        rw [harr s₉ sb₉]; exact hEsub 320 512 (by decide))
    refine keysAt_frame f fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    rw [kp_start _ _ hj]; exact hkB j hj
  -- The rounds.
  refine WP.seq (WP.mono (rounds_ok d room₁₀ masks₁₀ keys₁₀) fun s₁₁ ⟨q₁₁, room₁₁, _masks₁₁, rd₁₁, wr₁₁, sp₁₁, g₁₁, f₁₁⟩ => ?_)
  have hq₁₁ : quad s₁₁ 0 = roundsN (keysAt d s.mem (s.gpr .a0 + BitVec.ofNat 64 (keyStart d))) 16
      (decodeQ (Spec.Seed.blockAt s.mem P)) := by
    rw [q₁₁ 0 (by omega), roundsN_congr 16 _ hkeys, hq₁₀]
  have sb₁₁ : s₁₁.gpr sb = E := (g₁₁ _ (by simp [sb])).trans sb₁₀
  -- One block to copy out.
  apply WP.seq
  rw [copyTo]
  simp only [movR]
  refine WP.cons (exec_li (d := t2) (imm := 1) (by decide)) ?_
  have u₁₂ := Upd.write s₁₁ t2 (BitVec.ofInt 64 1)
  generalize s₁₁.write t2 (BitVec.ofInt 64 1) = s₁₂ at u₁₂ ⊢
  refine wp_addi (by decide) fun s₁₃ u₁₃ => wp_mv fun s₁₄ u₁₄ => WP.block_nil ?_
  have G₁₄ : ∀ r, r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → s₁₄.gpr r = s₁₁.gpr r := fun r a b c => by
    rw [u₁₄.other r c, u₁₃.other r b, u₁₂.other r a]
  have sb₁₄ : s₁₄.gpr sb = E := by rw [G₁₄ _ (by decide) (by decide) (by decide), sb₁₁]
  have mem₁₄ : s₁₄.mem = s₁₁.mem := by rw [u₁₄.mem, u₁₃.mem, u₁₂.mem]
  have wr₁₄ : s₁₄.wr = s.wr := by rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, wr₁₁, i₁₀.wr, wr₉]
  have rd₁₄ : s₁₄.rd = s.rd := by rw [u₁₄.rd, u₁₃.rd, u₁₂.rd, rd₁₁, i₁₀.rd, rd₉]
  have quad₁₄ : quad s₁₄ 0 = quad s₁₁ 0 := by simp only [quad, lv, laneA, mem₁₄, sb₁₄, sb₁₁]
  have pre₁₄ : CopyOutPre s₁₄ P 1 := by
    refine ⟨room_congr room₉ (by rw [sb₁₄, sb₉]) (by rw [wr₁₄, wr₉]), by omega, fun b hb w hw => ?_,
      Parr s₁₄ sb₁₄⟩
    obtain rfl : b = 0 := by omega
    rw [wr₁₄]; exact Pdat w hw
  have inv₁₄ : CopyOutInv s₁₄ P 1 (1 - 1) s₁₄ := by
    refine ⟨by omega, ?_, ?_, ?_, fun b hb => by omega, Frame.refl _ _, fun _ _ => rfl, rfl, rfl, rfl⟩
    · rw [u₁₄.other _ (by decide), u₁₃.gpr, u₁₂.other _ (by decide), sb₁₁]; simp; rfl
    · rw [u₁₄.gpr, u₁₃.other _ (by decide), u₁₂.other _ (by decide), sb₁₄, sb₁₁]; simp
    · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide)]; exact u₁₂.gpr
  refine WP.seq (WP.mono (copyOut_loop pre₁₄ 1 s₁₄ inv₁₄ (by omega) (by omega)) fun s₁₅ i₁₅ => ?_)
  -- The registers so far.
  have K₁₅ : ∀ r ∈ [Reg.ra, .a0, .a1, .a2, .a3, .a5], s₁₅.gpr r = s₉.gpr r := by
    intro r hr
    have hc : CopyRegs r := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> (unfold CopyRegs; decide)
    rw [i₁₅.regs r hc, G₁₄ r hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2, g₁₁ r hr, i₁₀.regs r hc]
  have sb₁₅ : s₁₅.gpr sb = E := (K₁₅ _ (by simp [sb])).trans sb₉
  -- The memory: ECB's work area and the buffer since `ra` was saved.
  have FW : Frame [⟨E, 832⟩, ⟨P, 16⟩] s₅.mem s₁₅.mem := by
    have a : Frame [⟨E, 832⟩, ⟨P, 16⟩] s₅.mem s₁₀.mem := f₁₀.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_cons_self, ?_⟩
      rw [harr s₉ sb₉]; exact Offset.sub_base E (by decide)
    have b : Frame [⟨E, 832⟩, ⟨P, 16⟩] s₁₀.mem s₁₁.mem := f₁₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_cons_self, ?_⟩
      rw [show workR s₁₀ = ⟨E, 832⟩ by simp only [workR, sb₁₀]]; exact fun _ h => h
    have c : Frame [⟨E, 832⟩, ⟨P, 16⟩] s₁₁.mem s₁₅.mem := by
      rw [← mem₁₄]; exact i₁₅.frame.mono (by simp)
    exact (a.trans b).trans c
  -- The key pointer back, the caller's registers restored.
  rw [coreOut_eq, WP.block_append_iff (M := isa), WP.block_append_iff (M := isa)]
  refine wp_subi (by have := keyStart_lt d; omega) fun s₁₆ u₁₆ => WP.block_nil ?_
  have sb₁₆ : s₁₆.gpr sb = E := by rw [u₁₆.other _ (by decide), sb₁₅]
  have wr₁₆ : s₁₆.wr = s.wr := by rw [u₁₆.wr, i₁₅.wr, wr₁₄]
  have rd₁₆ : s₁₆.rd = s.rd := by rw [u₁₆.rd, i₁₅.rd, rd₁₄]
  have room₁₆ : Room s₁₆ := room_congr room₉ (by rw [sb₁₆, sb₉]) (by rw [wr₁₆, wr₉])
  have sv₁₆ : Spill.Saved E s₀.gpr savedOffs s₁₆.mem := by
    have sv₁ : Spill.Saved E s₀.gpr savedOffs s₁.mem := by
      have := P₁.saved; rw [show s₀.gpr t0 = E from t0₀] at this; exact this
    rw [u₁₆.mem]
    refine sv₁.frame_in savedOffs_range
      (((FR.mono (by simp)).trans (FW.mono (by simp))) :
        Frame [⟨raA B, 8⟩, ⟨E, 832⟩, ⟨P, 16⟩] s₁.mem s₁₅.mem) fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint E (by omega) (by omega) (by omega)
    · exact Offset.disjoint_base E (by omega) (by omega)
    · exact Offset.disjoint E (by omega) (by omega) (by omega)
  rw [seedRestore_eq]
  refine WP.mono (Spill.restore_wp (B := E) hEal sb₁₆ savedOffs_ho savedOffs_restorable
    (fun q hq => room₁₆.rw ?_) sv₁₆) fun s₁₇ R => ?_
  · rw [hscr s₁₆ sb₁₆]
    have := savedOffs_range q hq
    exact Offset.contains_base E (by unfold scratchSlots; omega) (by omega)
  -- The modes' state, `ra` and the frame's base back.
  refine wp_mv fun s₁₈ u₁₈ => wp_mv fun s₁₉ u₁₉ => wp_mv fun s₂₀ u₂₀ => ?_
  have T₂₀ : ∀ r, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → s₂₀.gpr r = s₁₇.gpr r := fun r a b c => by
    rw [u₂₀.other r c, u₁₉.other r b, u₁₈.other r a]
  have wr₂₀ : s₂₀.wr = s.wr := by rw [u₂₀.wr, u₁₉.wr, u₁₈.wr, R.wr, wr₁₆]
  have rd₂₀ : s₂₀.rd = s.rd := by rw [u₂₀.rd, u₁₉.rd, u₁₈.rd, R.rd, rd₁₆]
  have mem₂₀ : s₂₀.mem = s₁₅.mem := by rw [u₂₀.mem, u₁₉.mem, u₁₈.mem, R.mem, u₁₆.mem]
  refine wp_ld (a := raA B) (by decide)
    (by rw [T₂₀ _ (by decide) (by decide) (by decide), R.other _ (by decide), sb₁₆]; rfl)
    (by rw [hRA, hEk]; exact frame_al hal hfit (by decide) (by decide))
    (by rw [rd₂₀, wr₂₀, hRA]; obtain ⟨r, hr, hc⟩ := hin 1048 8 (by decide)
        exact ⟨r, List.mem_append_right _ hr, hc⟩) fun s₂₁ u₂₁ => ?_
  refine wp_subi (by decide) fun s' u' => WP.block_nil ?_
  have T : ∀ r, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .ra → r ≠ .s4 → s'.gpr r = s₁₇.gpr r :=
    fun r a b c e f => by rw [u'.other r f, u₂₁.other r e, T₂₀ r a b c]
  have mem' : s'.mem = s₁₅.mem := by rw [u'.mem, u₂₁.mem, mem₂₀]
  have K : ∀ r ∈ [Reg.ra, .a1, .a2, .a5], s₁₇.gpr r = s₉.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [R.other _ (by decide), u₁₆.other _ (by decide), K₁₅ _ (by simp)]
  have s4' : s'.gpr .s4 = B := by
    refine u'.gpr.trans ?_
    rw [u₂₁.other _ (by decide), T₂₀ _ (by decide) (by decide) (by decide), R.other _ (by decide), sb₁₆]
    exact BitVec.add_sub_cancel _ _
  have ra' : s'.gpr .ra = s.gpr .ra := by
    rw [u'.other _ (by decide), u₂₁.gpr, mem₂₀, FW.readW (r := ⟨raA B, 8⟩) (Region.contains_self _ _)
      (fun r hr => ?_) (by decide), mem₅, Mem.readW_writeW_self64]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint_base E (by omega) (by omega)
    · exact Offset.disjoint E (by omega) (by omega) (by omega)
  refine ⟨s4', fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [kept, RISCV64.preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    have pres : ∀ r, r ∈ savedOffs.map Prod.fst → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 →
        s'.gpr r = s.gpr r := fun r hm a b c e => by
      rw [T r a b c (by rintro rfl; exact absurd hm (by decide)) e, R.gpr_of (Or.inl hm),
        u₀.other r (by rintro rfl; exact absurd hm (by decide))]
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [T _ (by decide) (by decide) (by decide) (by decide) (by decide), R.other _ (by decide), u₁₆.gpr,
        K₁₅ _ (by simp), a0₉, BitVec.add_sub_cancel]
    · exact ra'
    · exact pres _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [u'.other _ (by decide), u₂₁.other _ (by decide), u₂₀.other _ (by decide),
        u₁₉.other _ (by decide), u₁₈.gpr, K _ (by simp), G₉ _ (by decide) (by decide) (by decide) (by decide)]
      exact st₅.1
    · rw [u'.other _ (by decide), u₂₁.other _ (by decide), u₂₀.other _ (by decide), u₁₉.gpr,
        u₁₈.other _ (by decide), K _ (by simp), G₉ _ (by decide) (by decide) (by decide) (by decide)]
      exact st₅.2.1
    · rw [u'.other _ (by decide), u₂₁.other _ (by decide), u₂₀.gpr, u₁₉.other _ (by decide),
        u₁₈.other _ (by decide), K _ (by simp), G₉ _ (by decide) (by decide) (by decide) (by decide)]
      exact st₅.2.2
    · rw [s4', hB]
    all_goals exact pres _ (by decide) (by decide) (by decide) (by decide) (by decide)
  · -- Memory: within the core's slots.
    rw [mem']
    refine (FA.sub fun r hr => ?_).trans (FW.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_singleton_self _, Offset.sub_base E (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_singleton_self _, Offset.sub_base E (by decide)⟩
  · -- The block.
    rw [mem', dirCipher_bytes, Proof.Seed.bytesAt_eq]
    refine congrArg Vector.toList ?_
    rw [← crypt_keysAt, crypt_eq, ← hq₁₁, ← quad₁₄]
    refine blockAt_of_bytes fun i hi => ?_
    have e := i₁₅.done 0 (by omega) i hi
    rw [show P + BitVec.ofNat 64 (16 * 0 + i) = P + BitVec.ofNat 64 i by simp] at e
    rw [e, encodeSwapped_get _ _ hi]
  · rw [u'.rd, u₂₁.rd, rd₂₀]
  · rw [u'.wr, u₂₁.wr, wr₂₀]

/-- The key stays ready through what the core writes, its slots. -/
theorem ready_core {s s' : State} {B : Addr} {ws : List Region} {k : Spec.Seed.Schedule}
    (h : Ready s B ws k) (e : s'.gpr .a0 = s.gpr .a0) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hf : Frame [⟨ecbA B, 1056⟩] s.mem s'.mem) : Ready s' B ws k := by
  obtain ⟨⟨hk, hin, hd⟩, hB⟩ := h
  refine ⟨⟨?_, by rw [hrd, hwr, keyR, e]; exact hin, by rw [keyR, e]; exact hd⟩, by rw [keyR, e]; exact hB⟩
  rw [e, Proof.Seed.scheduleAt_frame hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hB.sub_right (Offset.sub_base B (by decide)), hk]

/-- SEED's core meets what the modes need. -/
def dirCoreSpec (d : Direction) : CoreSpec (dirCore d) where
  Key := Spec.Seed.Schedule
  cipher := Proof.Seed.dirCipher d
  KeyArgs := KeyArgs
  Ready := Ready
  cipher_len _ _ := by cases d <;> simp [Proof.Seed.dirCipher, Spec.Seed.cipher, Spec.Seed.invCipher, dirCore]
  layout := layout d
  keyArgs_congr h e r w _ f := keyArgs_congr h e.a0 r w f
  ready_frame h e r w _ f hs _ := ready_frame h e.a0 r w f hs
  prepare_wp := prepare_wp d
  crypt_wp {s B ws k} hB hS hR := by
    refine WP.mono (crypt_ok d hB hS hR.2 hR.1.2.1) fun s' ⟨h5, hk, hf, hb, hrd, hwr⟩ => ?_
    refine ⟨h5, hk, ready_core hR (hk .a0 (by decide)) hrd hwr hf, hf, fun j hj => ?_, hrd, hwr⟩
    obtain rfl : j = 0 := by simpa [dirCore] using hj
    have e : blkAddr (dirCore d) B 0 = bufA B := by
      show B + BitVec.ofNat 64 (8 * 135) + BitVec.ofNat 64 (16 * 0) = B + BitVec.ofNat 64 48 + BitVec.ofNat 64 1032
      rw [Offset.add_add, Offset.add_add]
    rw [show 4 * (dirCore d).bw = 16 from rfl, e, hb, hR.1.1]

end VG.Proof.Seed.RISCV64.Mode
