import VerifiedGarbage.Proof.TripleDes.X86_64.Pre
import VerifiedGarbage.Proof.Modes.X86_64.Core
import VerifiedGarbage.Proof.Modes.X86_64.Words
import VerifiedGarbage.Impl.TripleDes.X86_64.Cbc
import VerifiedGarbage.Proof.TripleDes.CbcBlocks

/-!
# Triple DES's core for the modes on x86-64

`dirCoreSpec d`: Triple DES's core for the direction `d`
(`Impl.TripleDes.X86_64.dirCore d`) meets what the modes need of a core of
one-word blocks (`Proof.Modes.X86_64.BlockSpec`), with the key a schedule,
its cipher `Spec.TripleDes.cipher` for encryption and
`Spec.TripleDes.invCipher` for decryption, and the key ready when its copy
in the core's slots is the schedule. `crypt` is the block function
(`block_ok`) on the buffer.
-/

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.TripleDes.X86_64
open VG.Impl.Aes.X86_64 (sb)
open VG.Proof.Modes (over over_at over_frame)
open VG.Proof.Modes.X86_64 (ScrIn coreRegion blkRegion blkAddr BlockSpec copyN_wp movR_ok addImm_ok
  signExtend_small runBlock_app addr_add)
open VG.Spec.TripleDes (Direction)

/-- The schedule's copy, with the scratch buffer at `B`. -/
abbrev schedAddr (B : Addr) : Addr := B + BitVec.ofNat 64 (8 * schedSlot)

/-- The schedule at `rdi`, outside the regions `rs`. -/
def KeyArgs (s : State) (rs : List Region) (k : Spec.TripleDes.Schedule) : Prop :=
  ∃ p : Addr, s.gpr .rdi = p ∧ k = Spec.TripleDes.scheduleAt s.mem p ∧ (⟨p, 384⟩ : Region) ∈ s.rd ∧
    p.toNat + 384 ≤ 2 ^ 64 ∧ ∀ r ∈ rs, Region.Disjoint ⟨p, 384⟩ r

/-- The schedule's copy is `k`. -/
def ReadyAt (m : Mem) (B : Addr) (k : Spec.TripleDes.Schedule) : Prop :=
  Spec.TripleDes.scheduleAt m (schedAddr B) = k

/-- The core's blocks are one word. -/
@[simp] theorem dirCore_bw (d : Direction) : (dirCore d).bw = 1 := rfl

theorem dirCipher_bytes (d : Direction) (k : Spec.TripleDes.Schedule) (m : Mem) (p : Addr) :
    dirCipher d k (Spec.Aes.bytesAt m p 8) = (blockResult k d (Spec.TripleDes.blockAt m p)).toList := by
  cases d <;> simp only [dirCipher, Spec.TripleDes.cipher, Spec.TripleDes.invCipher, blockResult, ofFn_bytesAt]

/-- The core's slots, its buffer and the schedule's copy. -/
theorem core_eq (d : Direction) (B : Addr) : coreRegion (dirCore d) B = ⟨B, 904⟩ := rfl
theorem blk_eq (d : Direction) (B : Addr) : blkRegion (dirCore d) B = ⟨B + BitVec.ofNat 64 512, 8⟩ := rfl
theorem total_eq (d : Direction) : (dirCore d).total = 121 := rfl

theorem sched_sub (B : Addr) : Region.Sub ⟨schedAddr B, 384⟩ ⟨B, 904⟩ := Offset.sub_base B (by decide)

theorem readyAt_frame {d : Direction} {m m' : Mem} {B : Addr} {k : Spec.TripleDes.Schedule} {rs : List Region}
    (h : ReadyAt m B k) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (dirCore d) B) r ∨ Region.Sub r (blkRegion (dirCore d) B)) :
    ReadyAt m' B k := by
  rw [ReadyAt, scheduleAt_eq_of_frame _ hf fun r hr => ?_]
  · exact h
  rcases hd r hr with h' | h'
  · rw [core_eq] at h'; exact h'.sub_left (sched_sub B)
  · rw [blk_eq] at h'
    exact (Offset.disjoint B (.inr (by decide)) (by decide) (by decide)).sub_right h'

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.TripleDes.Schedule} (h : KeyArgs s rs k)
    (hr : ∀ r ∈ [Reg.rdi], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (_ : s'.wr = s.wr)
    (hf : Frame rs s.mem s'.mem) : KeyArgs s' rs k := by
  obtain ⟨p, hp, hk, hin, hfit, hdis⟩ := h
  refine ⟨p, by rw [hr .rdi List.mem_cons_self, hp], ?_, by rw [hrd]; exact hin, hfit, hdis⟩
  rw [hk]
  exact (scheduleAt_eq_of_frame p hf hdis).symm

theorem prepare_wp (d : Direction) {s : State} {B : Addr} {rs : List Region} {k : Spec.TripleDes.Schedule}
    (hB : s.gpr sb = B) (hs : ScrIn s B (dirCore d).total) (hR : (⟨B, 8 * (dirCore d).total⟩ : Region) ∈ rs)
    (hk : KeyArgs s rs k) :
    WP isa (dirCore d).prepare s fun s' => ReadyAt s'.mem B k ∧ s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .r12 = s.gpr .r12 ∧ s'.gpr .r13 = s.gpr .r13 ∧
      Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hp, rfl, hin, hfit, hdis⟩ := hk
  have hfB := hs.fit
  rw [total_eq] at hfB
  have hsep : Region.Disjoint ⟨p, 384⟩ ⟨B, 904⟩ := (hdis _ hR).sub_right (Region.sub_prefix (by rw [total_eq]; decide))
  refine WP.mono (copyN_wp (k := 48) (P := schedAddr B) (Q := p) ⟨by rw [hB], by rw [hp]; simp, by decide,
    by decide, fun w hw => ⟨_, hs.wr, by
      rw [addr_add, total_eq]; exact Offset.contains_base B (by simp only [schedSlot]; omega) (by simp only [schedSlot]; omega)⟩,
    fun w hw => ⟨_, List.mem_append_left _ hin, Offset.contains_base p (by omega) (by omega)⟩,
    (hsep.sub_right (sched_sub B)).symm, by omega⟩) fun s' h => ?_
  refine ⟨scheduleAt_copy fun i hi => by rw [h.mem, over_at hi (by omega)], by rw [h.regs _ (by decide), hB],
    h.regs _ (by decide), h.regs _ (by decide), h.regs _ (by decide), ?_, h.rd, h.wr⟩
  rw [h.mem, core_eq]
  exact (over_frame _ _ _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, sched_sub B⟩

theorem crypt_wp (d : Direction) {s : State} {B : Addr} {k : Spec.TripleDes.Schedule} (hB : s.gpr sb = B)
    (hs : ScrIn s B (dirCore d).total) (hr : ReadyAt s.mem B k) :
    WP isa (dirCore d).crypt s fun s' => s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .r12 = s.gpr .r12 ∧ s'.gpr .r13 = s.gpr .r13 ∧ ReadyAt s'.mem B k ∧
      Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧
      (∀ j < (dirCore d).G, Spec.Aes.bytesAt s'.mem (blkAddr (dirCore d) B j) (8 * (dirCore d).bw) =
        dirCipher d k (Spec.Aes.bytesAt s.mem (blkAddr (dirCore d) B j) (8 * (dirCore d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfB := hs.fit
  rw [total_eq] at hfB
  have hss : schedSlot = 65 := rfl
  have hw := hs.wr
  rw [total_eq] at hw
  -- `rdi`, `rsi` and `rdx` to the schedule's copy, the buffer and the block function's slots.
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s .rdi sb
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := addImm_ok s₁ .rdi (BitVec.ofNat 32 (8 * schedSlot))
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := movR_ok s₂ .rsi sb
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := addImm_ok s₃ .rsi (BitVec.ofNat 32 (8 * cbcBuf))
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := movR_ok s₄ .rdx sb
  have g₅ : ∀ x, x ≠ .rdi → x ≠ .rsi → x ≠ .rdx → s₅.gpr x = s.gpr x := fun x h1 h2 h3 => by
    rw [o₅ x h3, o₄ x h2, o₃ x h2, o₂ x h1, o₁ x h1]
  have sb₅ : ∀ x, x ≠ sb → s₅.gpr sb = B := fun _ _ => by rw [g₅ _ (by decide) (by decide) (by decide), hB]
  have rdi₅ : s₅.gpr .rdi = schedAddr B := by
    rw [o₅ _ (by decide), o₄ _ (by decide), o₃ _ (by decide), r₂, r₁, hB, signExtend_small (by decide)]
  have rsi₅ : s₅.gpr .rsi = B + BitVec.ofNat 64 512 := by
    rw [o₅ _ (by decide), r₄, r₃, o₂ _ (by decide), o₁ _ (by decide), hB, signExtend_small (by decide)]; rfl
  have rdx₅ : s₅.gpr .rdx = B := by
    rw [r₅, o₄ _ (by decide), o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide), hB]
  have mem₅ : s₅.mem = s.mem := by rw [m₅, m₄, m₃, m₂, m₁]
  have rd₅' : s₅.rd = s.rd := by rw [rd₅, rd₄, rd₃, rd₂, rd₁]
  have wr₅' : s₅.wr = s.wr := by rw [wr₅, wr₄, wr₃, wr₂, wr₁]
  rw [show (dirCore d).crypt = .seq (.block [movR .rdi sb, .alu .add .rdi (.imm (BitVec.ofNat 32 (8 * schedSlot))),
      movR .rsi sb, .alu .add .rsi (.imm (BitVec.ofNat 32 (8 * cbcBuf))), movR .rdx sb])
      (.seq (block d) (.block [movR sb .rdx])) by cases d <;> rfl]
  refine WP.seq (WP.of_runBlock ⟨s₅, by
    rw [show ([movR .rdi sb, .alu .add .rdi (.imm (BitVec.ofNat 32 (8 * schedSlot))), movR .rsi sb,
        .alu .add .rsi (.imm (BitVec.ofNat 32 (8 * cbcBuf))), movR .rdx sb] : List Instr) =
        [Impl.Aes.X86_64.movR .rdi sb] ++ ([.alu .add .rdi (.imm (BitVec.ofNat 32 (8 * schedSlot)))] ++
        ([Impl.Aes.X86_64.movR .rsi sb] ++ ([.alu .add .rsi (.imm (BitVec.ofNat 32 (8 * cbcBuf)))] ++
        ([Impl.Aes.X86_64.movR .rdx sb] : List Instr)))) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some,
      runBlock_app, e₄, Option.bind_some, e₅], ?_⟩)
  -- The block.
  have inS : ∀ {t}, t + 8 ≤ 968 → InRegions s₅.wr (B + BitVec.ofNat 64 t) 8 := fun ht =>
    ⟨_, by rw [wr₅']; exact hw, Offset.contains_base B (by omega) (by omega)⟩
  have hp := headPre_of s₅ (fun i hi => by rw [rdx₅]; exact inS (by omega))
    (fun i hi => by
      rw [rdi₅, addr_add]
      obtain ⟨r, h1, h2⟩ := inS (t := 8 * schedSlot + 8 * i) (by simp only [schedSlot]; omega)
      exact ⟨r, List.mem_append_right _ h1, h2⟩)
    (by rw [rsi₅]; exact inS (by decide))
    (by rw [rdi₅, rdx₅]; exact Offset.disjoint_base B (by decide) (by omega))
    (by rw [rsi₅, rdx₅]; exact Offset.disjoint_base B (by decide) (by omega))
  rw [rdi₅, mem₅, hr] at hp
  refine WP.seq (WP.mono (block_ok k (schedAddr B) d s₅ hp (by rw [rsi₅]; exact inS (by decide)))
    fun s₆ h₆ => ?_)
  obtain ⟨s₇, e₇, r₇, o₇, m₇, rd₇, wr₇⟩ := movR_ok s₆ sb .rdx
  refine WP.of_runBlock ⟨s₇, by rw [show ([movR sb .rdx] : List Instr) = [Impl.Aes.X86_64.movR sb .rdx] from rfl,
    e₇], ?_⟩
  have rdx₆ : s₆.gpr .rdx = B := by rw [h₆.regs .rdx (by decide), rdx₅]
  have sv12 : s₇.gpr .r12 = s.gpr .r12 := by
    rw [o₇ _ (by decide), h₆.saved _ (by decide), g₅ _ (by decide) (by decide) (by decide)]
  have sv13 : s₇.gpr .r13 = s.gpr .r13 := by
    rw [o₇ _ (by decide), h₆.saved _ (by decide), g₅ _ (by decide) (by decide) (by decide)]
  have fB : Frame [⟨B, 904⟩] s₅.mem s₆.mem := h₆.frame.sub fun r hr => by
    simp only [blockRegions, rsi₅, rdx₅, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, Offset.sub_base B (by decide)⟩
    · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
  refine ⟨by rw [r₇, rdx₆], by rw [o₇ _ (by decide), h₆.regs .rsp (by decide), g₅ _ (by decide) (by decide)
    (by decide)], sv12, sv13, ?_, by rw [m₇, core_eq, ← mem₅]; exact fB,
    fun j hj => ?_, by rw [rd₇, h₆.rd, rd₅'], by rw [wr₇, h₆.wr, wr₅']⟩
  · rw [ReadyAt, m₇, scheduleAt_eq_of_frame _ h₆.frame fun r hr => ?_, mem₅, hr]
    simp only [blockRegions, rsi₅, rdx₅, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint B (.inr (by decide)) (by decide) (by decide)
    · exact Offset.disjoint_base B (by decide) (by omega)
  · have hj0 : j = 0 := by simp only [dirCore] at hj; omega
    subst hj0
    have ea : blkAddr (dirCore d) B 0 = s₅.gpr .rsi := by rw [rsi₅]; rfl
    rw [dirCore_bw, ea, dirCipher_bytes, bytesAt_eq, m₇, h₆.result, mem₅]

/-- Triple DES's core for the direction `d` meets what the modes need. -/
def dirCoreSpec (d : Direction) : BlockSpec (dirCore d) where
  Key := Spec.TripleDes.Schedule
  cipher := dirCipher d
  KeyArgs := KeyArgs
  Ready s B k := ReadyAt s.mem B k
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.TripleDes.cipher, Spec.TripleDes.invCipher]
  layout := ⟨by simp only [dirCore]; decide, by simp only [dirCore]; decide, by simp only [dirCore]; decide,
    by simp only [dirCore]; decide, by simp only [dirCore]; decide, by simp only [dirCore]; decide⟩
  keyRegs_ok := by simp only [dirCore]; decide
  regs_ok := by simp only [dirCore, Modes.X86_64.regsOk]; decide
  keyArgs_congr := keyArgs_congr
  ready_frame h hf hd _ := readyAt_frame h hf hd
  prepare_wp := prepare_wp d
  crypt_wp := crypt_wp d

end VG.Proof.TripleDes.X86_64
