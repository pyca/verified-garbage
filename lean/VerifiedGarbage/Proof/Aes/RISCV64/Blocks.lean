module

public import VerifiedGarbage.Proof.Aes.RISCV64.Ecb
public import VerifiedGarbage.Proof.Aes.RISCV64.Prologue
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RISCV64.Align
public import VerifiedGarbage.Proof.Aes.RISCV64.Keys

/-!
# AES on whole blocks on RISC-V: the whole functions

As on PPC64LE (`Proof/Aes/PPC64LE/Blocks.lean`): `vg_aes_encrypt_blocks`
and `vg_aes_decrypt_blocks` are `blocks` around `encrypt4` and `decrypt4`,
and are proven at once, for any transformation of four blocks with
`CryptOk`: the prologue moves the scratch buffer, the count and the data,
rounds the scratch buffer up, saves the callee-saved registers, builds the
masks (`Prologue.lean`) and bitslices the round keys (`Keys.lean`); the
groups (`Ecb.lean`) do the rest; the epilogue restores the registers.
-/

@[expose] public section

namespace VG.Proof.Aes

open VG.RISCV64 in
/-- RISC-V contract for `vg_aes_encrypt_blocks(schedule: *const [u8; 240],
rounds: usize, data: *mut [u8; 16], n: usize, scratch: *mut [u64; 256])` (and
`vg_aes_decrypt_blocks`, with `f` the inverse cipher): replaces each of the
`n` blocks at `data` with `f rounds w` of it, for the key schedule `w`.

The code may read `schedule` (240 bytes) and read and write `data` (`16 n`
bytes) and `scratch` (2048 bytes, whose contents on exit are unspecified).
These may not overlap each other, and `data` may not wrap around the end of
the address space. `rounds` is 10, 12 or 14. The pointers, `rounds` and `n`
are public; the key schedule and the data are secret. -/
def blocksRISCV64 (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : Contract RISCV64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .a0, 240⟩
    let data : Region := ⟨s.gpr .a2, 16 * (s.gpr .a3).toNat⟩
    let scratch : Region := ⟨s.gpr .a4, 2048⟩
    s.rd = [sched] ∧ s.wr = [data, scratch] ∧
    sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
    (s.gpr .a2).toNat + 16 * (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
    ((s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14)
  post s s' :=
    Spec.Aes.statesAt s'.mem (s.gpr .a2) (s.gpr .a3).toNat =
      (Spec.Aes.statesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat).map
        (f (s.gpr .a1).toNat (Spec.Aes.bytesAt s.mem (s.gpr .a0) (16 * ((s.gpr .a1).toNat + 1))))
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.sp = s₂.sp

end VG.Proof.Aes

namespace VG.Proof.Aes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.Align VG.RISCV64.Steps VG.Bitslice
  VG.Impl.Aes.RISCV64 VG.Proof.Aes

theorem blocksSetup_wp {s : State} {P : State → Prop}
    (h : ∀ s', s'.gpr sb = s.gpr .a4 → s'.gpr .a4 = s.gpr .a3 → s'.gpr .a3 = s.gpr .a2 →
      (∀ r, r ≠ sb → r ≠ .a4 → r ≠ .a3 → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → s'.sp = s.sp → P s') :
    WP isa (.block blocksSetup) s P := by
  unfold blocksSetup movR
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => WP.block_nil ?_
  refine h s₃ ?_ ?_ (by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)])
    (fun r h1 h2 h3 => ?_) (by rw [u₃.mem, u₂.mem, u₁.mem])
    (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr]) (by rw [u₃.sp, u₂.sp, u₁.sp])
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]
  · rw [u₃.other _ h3, u₂.other _ h2, u₁.other _ h1]

/-- The data after the last group, as states. -/
theorem statesAt_of_ecbInv {m₀ m : Mem} {D : Addr} {n : Nat} {F : Nat → Spec.Aes.State}
    (h : EcbInv m₀ m D n n F) : Spec.Aes.statesAt m D n = (List.range n).map F := by
  simp only [Spec.Aes.statesAt]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  apply Vector.ext
  intro t ht
  simp only [Spec.Aes.stateAt, Vector.getElem_ofFn]
  rw [Offset.add_add, h _ (by omega_arith), ite_eq_left (show 16 * j + t < 16 * n by omega_arith),
    show (16 * j + t) / 16 = j by omega_arith, show (16 * j + t) % 16 = t by omega_arith, getD_eq _ ht]

/-- The registers the prologue writes before the key loop, besides `t0`, `t1`
and the key loop's. -/
theorem notKeyWrites : ∀ r ∈ [Reg.ra, .a3, .a4, .a5], r ∉ keyWrites := by decide

theorem correct_blocks {crypt4 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : CryptOk crypt4 f) {s₀ : State}
    (hp : (Proof.Aes.blocksRISCV64 f).pre s₀) :
    WP isa (blocks crypt4) s₀ fun s' =>
      (∀ r ∈ RISCV64.preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
        (Proof.Aes.blocksRISCV64 f).post s₀ s' := by
  obtain ⟨hrd, hwr, dSD, dSS, dDS, hwrap, hR⟩ := hp
  have hwD : (⟨s₀.gpr .a2, 16 * (s₀.gpr .a3).toNat⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have hwS : (⟨s₀.gpr .a4, 2048⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have hrS : (⟨s₀.gpr .a0, 240⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  let n := (s₀.gpr .a3).toNat
  have n16 : 16 * n < 2 ^ 64 := by
    refine Nat.lt_of_not_le fun hc => dDS (s₀.gpr .a4) ?_ (by simp [Region.Contains])
    simp only [Region.Contains]
    have := (s₀.gpr .a4 - s₀.gpr .a2).isLt
    omega_arith
  have hR14 : (s₀.gpr .a1).toNat ≤ 14 := by omega_arith
  let X := s₀.gpr .a4
  let b := X + BitVec.ofNat 64 (pad X)
  let D := s₀.gpr .a2
  let R := (s₀.gpr .a1).toNat
  let sc := s₀.gpr .a0
  -- The prologue.
  unfold blocks
  refine WP.seq ?_
  rw [WP.block_append_iff (M := isa), WP.block_append_iff (M := isa), WP.block_append_iff (M := isa),
    WP.block_append_iff (M := isa)]
  refine blocksSetup_wp fun s₁ a5₁ a4₁ a3₁ o₁ m₁ rd₁ wr₁ sp₁ => ?_
  refine roundSb_wp fun s₂ b₂ o₂ m₂ rd₂ wr₂ sp₂ => ?_
  have hb₂ : s₂.gpr sb = b := by rw [b₂, a5₁]
  have hscr₂ : Scr s₂ X 2048 := ⟨by rw [wr₂, wr₁]; exact hwS, hb₂⟩
  rw [saveRegs_eq]
  refine Spill.save_ok (rest := []) hscr₂.al savedOffs_ho (fun p hp => ⟨_, hscr₂.wr,
    hscr₂.contains (by have := savedOffs_range p hp; omega) (by decide)⟩) (WP.block_nil ?_)
  -- The registers' slots, which later code keeps.
  generalize hS : ({ s₂ with mem := Spill.saveMem s₂.mem (s₂.gpr sb) s₂.gpr savedOffs } : State) = s₂'
  have g₂' : s₂'.gpr = s₂.gpr := by rw [← hS]
  have mm₂ : s₂'.mem = Spill.saveMem s₂.mem (s₂.gpr sb) s₂.gpr savedOffs := by rw [← hS]
  have rd₂' : s₂'.rd = s₂.rd := by rw [← hS]
  have wr₂' : s₂'.wr = s₂.wr := by rw [← hS]
  have sp₂' : s₂'.sp = s₂.sp := by rw [← hS]
  have sv₂ : Spill.Saved b s₂.gpr savedOffs s₂'.mem := by
    rw [mm₂, ← hb₂]; exact Spill.saveMem_saved savedOffs_fits _ _ _
  have f₂ : Frame [⟨b + BitVec.ofNat 64 320, 96⟩] s₂.mem s₂'.mem := by
    rw [mm₂, ← hb₂]; exact Spill.saveMem_frame savedOffs_range (by decide) _ _ _
  have hscr₂' : Scr s₂' X 2048 := ⟨by rw [wr₂']; exact hscr₂.wr, by rw [g₂']; exact hscr₂.base⟩
  refine WP.mono (maskInit_ok hscr₂') fun s₃' ⟨mk₃, fm₃, g₃', rd₃', wr₃', sp₃'⟩ => ?_
  have b₃' : s₃'.gpr sb = b := by rw [g₃' _ (by decide) (by decide), g₂']; exact hb₂
  rw [show s₂'.gpr sb = b by rw [g₂']; exact hb₂] at mk₃ fm₃
  refine keySetup_wp (s := s₃') (R := R) (by
      rw [g₃' _ (by decide) (by decide), show s₂'.gpr .a1 = s₂.gpr .a1 by rw [g₂'],
        o₂ _ (by decide), o₁ _ (by decide) (by decide) (by decide)]; simp [R])
    hR14 fun s₃ a0₃ a2₃ a1₃ o₃ m₃ rd₃ wr₃ sp₃ => ?_
  have hb₃ : s₃.gpr sb = b := by
    rw [o₃ sb (by decide) (by decide) (by decide) (by decide)]; exact b₃'
  have hscr₃ : Scr s₃ X 2048 := ⟨by rw [wr₃, wr₃', wr₂']; exact hscr₂.wr, hb₃⟩
  -- The memory so far changed only in the scratch buffer.
  have f₀₃ : Frame [⟨X, 2048⟩] s₀.mem s₃.mem := by
    rw [m₃]
    have f12 : Frame [⟨X, 2048⟩] s₂.mem s₂'.mem := f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact scr_part X (by omega)⟩
    have f02 : Frame [⟨X, 2048⟩] s₀.mem s₂'.mem := fun x hx =>
      (f12 x hx).trans (congrFun (m₂.trans m₁) x)
    refine Frame.trans f02 ?_
    refine fm₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact scr_part X (by omega)
    · exact scr_part X (by omega)
  let w := Spec.Aes.bytesAt s₀.mem sc (16 * (R + 1))
  have hk : KSetup s₃ X b sc R w :=
    { scr := hscr₃
      base := hb₃
      masks := by rw [m₃]; exact mk₃
      sch := List.mem_append_left _ (by rw [rd₃, rd₃', rd₂', rd₂, rd₁]; exact hrS)
      sep := dSS
      rounds := hR14
      w := fun i hi => by
        simp only [w, Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hi, Option.map_some, Option.getD_some]
        refine (f₀₃.bytes (R := ⟨sc, 240⟩) (fun r hr => ?_) (by simp) (by simp only; omega_arith)).symm
        simp only [List.mem_singleton] at hr; subst hr
        exact dSS }
  have hi₃ : KInv s₃ b sc R w R s₃ :=
    { hj := Nat.le_refl _
      a1 := a1₃
      a0 := by
        rw [a0₃, g₃' _ (by decide) (by decide), show s₂'.gpr .a0 = s₂.gpr .a0 by rw [g₂'],
          o₂ _ (by decide), o₁ .a0 (by decide) (by decide) (by decide)]
      a2 := by rw [a2₃, b₃']; simp [keyAddr, lastKey]
      rd := rfl
      wr := rfl
      sp := rfl
      keep := fun _ _ => rfl
      frame := Frame.refl _ _
      done := fun i h1 h2 => absurd h2 (by omega_arith) }
  -- The key loop.
  refine WP.seq (WP.mono (keyLoop_ok hk hi₃) fun s₄ d₄ => ?_)
  refine WP.seq ?_
  unfold keyDone
  refine wp_addi (imm := 64) (by decide) fun s₅ u₅ => WP.block_nil ?_
  have g₅ : ∀ r ∈ [Reg.ra, .a3, .a4, .a5], s₅.gpr r = s₃.gpr r := fun r hr => by
    rw [u₅.other r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide),
      d₄.keep r (notKeyWrites r hr)]
  have k₃ : ∀ r, r ∉ [t0, t1, .a0, .a1, .a2, .a3, .a4, sb] → s₃.gpr r = s₀.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [o₃ r hr.1 hr.2.2.1 hr.2.2.2.2.1 hr.2.2.2.1, g₃' r hr.1 hr.2.1,
      show s₂'.gpr r = s₂.gpr r by rw [g₂'], o₂ r hr.2.2.2.2.2.2.2,
      o₁ r hr.2.2.2.2.2.2.2 hr.2.2.2.2.2.2.1 hr.2.2.2.2.2.1]
  have a4₅ : s₅.gpr .a4 = s₀.gpr .a3 := by
    rw [g₅ _ (by simp), o₃ _ (by decide) (by decide) (by decide) (by decide),
      g₃' _ (by decide) (by decide), show s₂'.gpr .a4 = s₂.gpr .a4 by rw [g₂'], o₂ _ (by decide)]
    exact a4₁
  have a3₅ : s₅.gpr .a3 = D := by
    rw [g₅ _ (by simp), o₃ _ (by decide) (by decide) (by decide) (by decide),
      g₃' _ (by decide) (by decide), show s₂'.gpr .a3 = s₂.gpr .a3 by rw [g₂'], o₂ _ (by decide)]
    exact a3₁
  have ra₅ : s₅.gpr .ra = s₀.gpr .ra := by rw [g₅ _ (by simp), k₃ _ (by decide)]
  have hb₅ : s₅.gpr sb = b := by rw [show sb = .a5 from rfl, g₅ _ (by simp)]; exact hb₃
  have hK0 : s₅.gpr .a0 = b + BitVec.ofNat 64 (1920 - 64 * R) := by
    rw [u₅.gpr, d₄.a2]; exact BitVec.sub_add_cancel _ _
  have fK : Frame (kRegions b) s₃.mem s₅.mem := u₅.mem ▸ d₄.frame
  have hs : ESetup s₅ X b D n R w :=
    { scr := ⟨by rw [u₅.wr, d₄.wr]; exact hscr₃.wr, hb₅⟩
      base := hb₅
      masks := by rw [u₅.mem]; exact masks_kept d₄.frame hk.masks
      dat := by rw [u₅.wr, d₄.wr, wr₃, wr₃', wr₂', wr₂, wr₁]; exact hwD
      hn := n16
      sep := dDS
      rounds := hR
      keys := fun j hj => keyRel_congr (d₄.keys j hj) fun k hk => by
        rw [u₅.mem, keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add, show 1920 - 64 * R + 64 * j =
          1920 - 64 * (R - j) by omega_arith] }
  have dK : ∀ r ∈ kRegions b, Region.Disjoint ⟨D, 16 * n⟩ r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dDS.sub_right (scr_base X (by omega))
    · exact dDS.sub_right (scr_part X (by omega))
  have data₅ : EcbInv s₀.mem s₅.mem D n 0 (ecbOut f s₀.mem D R w) :=
    ecbInv_frame fK dK n16
      (ecbInv_frame f₀₃ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dDS)
        n16 fun i hi => by simp)
  refine WP.seq (WP.mono (Q := EDone f s₀.mem s₅ b D n R w) ?_ fun s₆ gd => ?_)
  · refine WP.ite (decide (n = 0)) (eval_zero_ofNat _ _ (by omega_arith)
      (by rw [a4₅]; simp [n])) (fun h0 => ?_) (fun h0 => ?_)
    · have hn0 : n = 0 := by simpa using h0
      exact WP.block_nil ⟨hb₅, rfl, rfl, rfl, rfl, Frame.refl _ _, fun i hi => by omega_arith⟩
    · have hn0 : n ≠ 0 := by simpa using h0
      refine ecbGroups_ok hcr hs ⟨by omega_arith, ?_, ?_, hb₅, hK0, rfl, rfl, rfl, rfl, Frame.refl _ _,
        data₅⟩
      · rw [a3₅]; simp
      · rw [a4₅]; simp [n]
  -- The epilogue.
  have sv : Spill.Saved b s₂.gpr savedOffs s₆.mem := by
    have dS : ∀ r ∈ [(⟨b + BitVec.ofNat 64 416, 48⟩ : Region), ⟨b + BitVec.ofNat 64 512, 96⟩],
        Region.Disjoint ⟨b + BitVec.ofNat 64 320, 96⟩ r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint b (by omega) (by omega) (by omega)
      · exact Offset.disjoint b (by omega) (by omega) (by omega)
    have dK' : ∀ r ∈ kRegions b, Region.Disjoint ⟨b + BitVec.ofNat 64 320, 96⟩ r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint_base b (by omega) (by omega)
      · exact Offset.disjoint b (by omega) (by omega) (by omega)
    have dE : ∀ r ∈ eRegions b D n, Region.Disjoint ⟨b + BitVec.ofNat 64 320, 96⟩ r := fun r hr => by
      simp only [eRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint_base b (by omega) (by omega)
      · exact (dDS.sub_right (scr_part X (by omega))).symm
    have fK' : Frame (kRegions b) s₃'.mem s₅.mem := fun x hx => (fK x hx).trans (congrFun m₃ x)
    exact ((sv₂.frame_in savedOffs_range fm₃ dS).frame_in savedOffs_range fK' dK').frame_in
      savedOffs_range gd.frame dE
  have hscr₆ : Scr s₆ X 2048 := ⟨by rw [gd.wr, u₅.wr, d₄.wr]; exact hscr₃.wr, by rw [gd.base]⟩
  rw [restoreRegs_eq]
  refine WP.mono (Spill.restore_wp (B := b) (by rw [← hb₂]; exact hscr₂.al) gd.base savedOffs_ho
    savedOffs_restorable (fun p hp => ⟨_, List.mem_append_right _ hscr₆.wr, by
      rw [← gd.base]
      exact hscr₆.contains (by have := savedOffs_range p hp; omega) (by decide)⟩) sv)
    fun s₇ rs₇ => ?_
  have dR : ∀ r ∈ [(⟨b, 0⟩ : Region)], Region.Disjoint ⟨D, 16 * n⟩ r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    intro a _ h; simp [Region.Contains] at h
  refine ⟨fun r hr => ?_, ?_, ?_⟩
  · have hr' : r ∈ savedOffs.map Prod.fst := by rw [savedOffs_regs]; exact hr
    rw [rs₇.gpr_of (.inl hr')]
    have : r ∉ [t0, t1, .a0, .a1, .a2, .a3, .a4, sb] := by
      revert hr; revert r; decide
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this
    rw [o₂ r this.2.2.2.2.2.2.2, o₁ r this.2.2.2.2.2.2.2 this.2.2.2.2.2.2.1 this.2.2.2.2.2.1]
  · rw [rs₇.other _ not_saved_ra, gd.ra, ra₅]
  · show Spec.Aes.statesAt s₇.mem D n = _
    rw [rs₇.mem, statesAt_of_ecbInv gd.data]
    simp only [Spec.Aes.statesAt, List.map_map]
    rfl

end VG.Proof.Aes.RISCV64
