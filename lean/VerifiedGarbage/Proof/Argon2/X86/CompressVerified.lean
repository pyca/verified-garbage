import VerifiedGarbage.Proof.Argon2.X86.CompressLit
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Argon2.X86.Compress

section

/-!
# Argon2 compression on x86 (32-bit): the whole function

`correct`: the prologue, the initialization, the rows and columns and the
epilogue, with the calling convention's obligations.
-/

namespace VG.Proof.Argon2.X86

open VG VG.X86 VG.Spec.Argon2
open VG.Impl.Argon2.X86 (prologue initWord finishWord epilogue savedOff)
open VG.Proof.Sha512.X86 (Acc rd64 ea_of)
open VG.Proof.Sha256.X86.Stream (contains_addr wp_movm)

section
variable {B : BitVec 32} (hfit : B.toNat + 4096 ≤ 2 ^ 32)
include hfit

theorem permR_sub : Region.Sub (permR B) ⟨B.setWidth 64, 4096⟩ := by
  show Region.Sub ⟨addr B 1024, 1024⟩ _
  rw [addr_off hfit (by decide)]
  exact Offset.sub_base _ (by decide)

/-- A word of `scratch` outside the permuted block is unchanged by its writes. -/
theorem outside_perm {m m' : Mem} (hf : Frame [permR B] m m') {d : Nat} (hd : d + 4 ≤ 4096)
    (ho : d + 4 ≤ 1024 ∨ 2048 ≤ d) : m'.readW (addr B d) 32 = m.readW (addr B d) 32 := by
  refine hf.readW (r := ⟨addr B d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq]
  show Region.Disjoint _ ⟨addr B 1024, 1024⟩
  rw [addr_off hfit (by omega), addr_off hfit (by decide)]
  exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem low_perm {m m' : Mem} (hf : Frame [permR B] m m') : blk m' B 0 = blk m B 0 := by
  apply Vector.ext
  intro j hj
  simp only [blk, Vector.getElem_ofFn, rd64]
  rw [outside_perm hfit hf (by omega) (by omega), outside_perm hfit hf (by omega) (by omega)]

end

theorem words_zero {m : Mem} {B : BitVec 32} {f : Nat → BitVec 32} (h : Words m B 0 f 256) :
    blk m B 0 = ofWords f := blk_of_words fun i hi => h i hi

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa Impl.Argon2.X86.compress s₀ fun t => abiPreserved s₀ t ∧ compressX86.post s₀ t := by
  have fits := hp.scr_fits
  unfold Impl.Argon2.X86.compress Impl.Argon2.X86.rounds
  refine WP.seq (WP.block_append ((prologue_ok hp).mono fun s₁ h₁ =>
    (init_ok hp h₁ 256 (Nat.le_refl _)).mono fun s₂ h₂ => ?_))
  have A₂ : At (scr s₀) s₂ := ⟨h₂.esi, hp.acc h₂.wr⟩
  refine WP.seq (WP.seq ((rounds_ok fits rowIndex Proof.Argon2.rowIndex_injective (List.finRange 8)
    A₂).mono fun s₃ st₃ => (rounds_ok fits colIndex Proof.Argon2.colIndex_injective
      (List.finRange 8) (A₂.of_step st₃)).mono fun s₄ st₄ => ?_))
  have k₄ := st₃.keep.trans st₄.keep
  have pf : Frame [permR (scr s₀)] s₂.mem s₄.mem := st₃.frame.trans st₄.frame
  have f₄ : Frame [outR s₀, scrR s₀] s₀.mem s₄.mem :=
    h₂.frame.trans (pf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, permR_sub fits⟩)
  have g₄ : ∀ r, r ≠ .eax → r ≠ .esi → r ≠ .ecx → r ≠ .edx → s₄.gpr r = s₀.gpr r := fun r h0 h6 h1 h2 =>
    (k₄.gpr r (by simp [temps, h0, h1, h2])).trans (h₂.regs r h0 h6 h1 h2)
  have sp₄ : s₄.gpr .esp = esp₀ s₀ := g₄ _ (by decide) (by decide) (by decide) (by decide)
  unfold epilogue
  simp only [List.cons_append]
  refine wp_movm (ea_of sp₄ 12) (by rw [k₄.rd, k₄.wr, h₂.rd, h₂.wr]; exact hp.in_arg rfl (by omega) (by omega))
    fun s₅ u₅ => ?_
  have h₅ : FinInv s₀ s₄ s₅ 0 :=
    ⟨by rw [u₅.other _ (by decide), k₄.esi, h₂.esi], by rw [u₅.gpr, hp.arg_frame f₄ (by omega) (by omega)]; rfl,
      fun r _ h1 => u₅.other r h1, by rw [u₅.rd, k₄.rd, h₂.rd], by rw [u₅.wr, k₄.wr, h₂.wr],
      by rw [u₅.mem]; exact Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  refine WP.block_append ((finish_ok hp h₅ 256 (Nat.le_refl _)).mono fun s₆ h₆ => ?_)
  refine wp_movm (ea_of h₆.esi savedOff) (hp.in_scr h₆.wr (by decide)) fun t u => WP.block_nil ?_
  have ft : Frame [outR s₀, scrR s₀] s₀.mem t.mem := by
    rw [u.mem]
    exact f₄.trans (h₆.frame.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
  have gt : ∀ r, r ≠ .eax → r ≠ .esi → r ≠ .ecx → r ≠ .edx → t.gpr r = s₀.gpr r := fun r h0 h6 h1 h2 => by
    rw [u.other r h6, h₆.regs r h0 h1, g₄ r h0 h6 h1 h2]
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact gt _ (by decide) (by decide) (by decide) (by decide)
    · rw [u.gpr, hp.scr_frame h₆.frame (by decide), outside_perm fits pf (by decide) (by decide)]
      exact h₂.saved
    · exact gt _ (by decide) (by decide) (by decide) (by decide)
    · exact gt _ (by decide) (by decide) (by decide) (by decide)
    · exact gt _ (by decide) (by decide) (by decide) (by decide)
  · refine ft.readW (r := retR s₀) (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hp.ret_out, hp.ret_scr⟩
  · -- The output.
    have R₂ : blk s₂.mem (scr s₀) 0 = ofWords (xy s₀) := words_zero h₂.low
    have W₂ : working s₂.mem (scr s₀) = ofWords (xy s₀) := by
      rw [working_eq]; exact blk_of_words fun i hi => h₂.high i hi
    have X : xorBlock (blockAt s₀.mem ((xp s₀).setWidth 64)) (blockAt s₀.mem ((yp s₀).setWidth 64)) =
        ofWords (xy s₀) := by
      rw [blockAt_eq hp.x_fits, blockAt_eq hp.y_fits,
        blk_of_words (f := fun i => s₀.mem.readW (addr (xp s₀) (4 * i)) 32)
          (fun i _ => by rw [Nat.zero_add]),
        blk_of_words (f := fun i => s₀.mem.readW (addr (yp s₀) (4 * i)) 32)
          (fun i _ => by rw [Nat.zero_add]), xor_words]
      rfl
    have O : blk t.mem (op s₀) 0 = xorBlock (working s₄.mem (scr s₀)) (blk s₄.mem (scr s₀) 0) := by
      rw [u.mem, words_zero h₆.out, working_eq,
        blk_of_words (f := fun i => s₄.mem.readW (addr (scr s₀) (1024 + 4 * i)) 32) (fun _ _ => rfl),
        blk_of_words (f := fun i => s₄.mem.readW (addr (scr s₀) (4 * i)) 32)
          (fun i _ => by rw [Nat.zero_add]), xor_words]
      rfl
    show blockAt t.mem ((op s₀).setWidth 64) = _
    rw [blockAt_eq hp.out_fits, O, low_perm fits pf, R₂, st₄.working, st₃.working, W₂, ← X]
    simp only [compress]

end VG.Proof.Argon2.X86

end

/-!
# Argon2 compression on x86 (32-bit): verified

Constant time, against `compressX86`; then `compressWide`, which lets the
code write its arguments (`Verified.narrowTo`: it only reads them), and the
shared contract `Spec.Argon2.compressContract`, which implies it.
-/

namespace VG.Proof.Argon2.X86

open VG VG.X86 VG.Spec.Argon2

/-! ## Constant time -/

/-- The taint analysis starts with the stack arguments public, and the words
holding `out` and `scratch` known to be the base addresses of the writable
regions. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [1024, 4096], argLen := 20,
    argBases := [(12, 0), (16, 1)] }

theorem wf₀ {s : State} (hp : Pre s) : VG.X86.Taint.Wf τ₀ s := by
  have ho := hp.out_fits; have hsc := hp.scr_fits; have hs := hp.esp_fits
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, τ₀], by simpa [hp.wr] using hp.out_scr, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_out hp.arg_out
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_scr hp.arg_scr
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem agree₀ {s₁ s₂ : State} (h₁ : compressX86.pre s₁) (h₂ : compressX86.pre s₂)
    (hpub : compressX86.pub s₁ s₂) : VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := pre_of _ h₁; have hp₂ := pre_of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [outR, scrR, op, scr, ha 2 (by decide), ha 3 (by decide)]
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by have := hp₁.esp_fits; omega) h4 hk,
      VG.X86.Taint.argByte_eq (by have := hp₂.esp_fits; omega) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

theorem compress_ct : ConstantTime isa compressX86.pre compressX86.pub Impl.Argon2.X86.compress :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hpub => agree₀ h₁ h₂ hpub) (by taint_decide)

/-! ## A state satisfying the precondition -/

/-- Memory holding the arguments `0x1000, 0x1400, 0x2000, 0x3000` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5005 then 0x10 else if a = 0x5009 then 0x14 else if a = 0x500D then 0x20 else
  if a = 0x5011 then 0x30 else 0

def satState : State where
  gpr r := match r with
    | .esp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x1000, 1024⟩, ⟨0x1400, 1024⟩, ⟨0x5004, 16⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 4096⟩]

theorem sat_pre : compressX86.pre satState := by
  have a0 : arg satState 0 = 0x1000 := by decide
  have a1 : arg satState 1 = 0x1400 := by decide
  have a2 : arg satState 2 = 0x2000 := by decide
  have a3 : arg satState 3 = 0x3000 := by decide
  have e : argAddr satState 0 = 0x5004 := by decide
  simp only [compressX86, a0, a1, a2, a3, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide,
    by decide⟩ <;>
  exact Region.disjoint_of_sep (by decide)

theorem compress_verified : Verified X86.target Impl.Argon2.X86.compress compressX86 :=
  ⟨fun s hs => correct (pre_of s hs), compress_ct, ⟨satState, sat_pre⟩⟩

/-! ## Writable arguments, and the shared contract -/

/-- `compressX86`, with the arguments writable, as `Sig.contract` lays the
regions out. -/
def compressWide : Contract X86.isa :=
  { compressX86 with
    pre := fun s =>
      let x : Region := ⟨(arg s 0).setWidth 64, 1024⟩
      let y : Region := ⟨(arg s 1).setWidth 64, 1024⟩
      let out : Region := ⟨(arg s 2).setWidth 64, 1024⟩
      let scratch : Region := ⟨(arg s 3).setWidth 64, 4096⟩
      let args : Region := ⟨argAddr s 0, 16⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      s.rd = [x, y] ∧ s.wr = [out, scratch, args] ∧
      out.Disjoint scratch ∧ x.Disjoint out ∧ x.Disjoint scratch ∧ y.Disjoint out ∧
      y.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧ ret.Disjoint out ∧
      ret.Disjoint scratch ∧
      (arg s 0).toNat + 1024 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 1024 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 1024 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 4096 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 4 + 16 ≤ 2 ^ 32 }

/-- A state satisfying `compressWide.pre`. -/
def satWide : State :=
  { satState with rd := [⟨0x1000, 1024⟩, ⟨0x1400, 1024⟩], wr := [⟨0x2000, 1024⟩, ⟨0x3000, 4096⟩, ⟨0x5004, 16⟩] }

macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [compressX86, compressWide, VG.X86.arg_withRegions, VG.X86.argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_mem, State.withRegions_rd, State.withRegions_wr] $(loc)?)

theorem compressWide_verified : Verified X86.target Impl.Argon2.X86.compress compressWide :=
  Verified.narrowTo compress_verified
    (fun s => [⟨(arg s 0).setWidth 64, 1024⟩, ⟨(arg s 1).setWidth 64, 1024⟩, ⟨argAddr s 0, 16⟩])
    (fun s => [⟨(arg s 2).setWidth 64, 1024⟩, ⟨(arg s 3).setWidth 64, 4096⟩])
    (fun _ h => by
      obtain ⟨_, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆⟩ := h
      narrow
      exact ⟨trivial, trivial, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅,
        by omega⟩)
    (fun _ h => by
      obtain ⟨h₁, h₂, _⟩ := h
      rw [h₁, h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_singleton_self _))), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp,
          by simp⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩)
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h)
    ⟨satWide, by
      have a0 : arg satWide 0 = 0x1000 := by decide
      have a1 : arg satWide 1 = 0x1400 := by decide
      have a2 : arg satWide 2 = 0x2000 := by decide
      have a3 : arg satWide 3 = 0x3000 := by decide
      have e : argAddr satWide 0 = 0x5004 := by decide
      simp only [compressWide, a0, a1, a2, a3, e]
      refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide,
        by decide, by decide⟩ <;>
      exact Region.disjoint_of_sep (by decide)⟩

theorem compress_implies : compressWide.Implies (Spec.Argon2.compressContract X86.abi) := by
  sig_implies [Spec.Argon2.compressContract, Spec.Argon2.compressSig, compressWide, compressX86,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [satWide, satState, satMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using satWide

/-- The emitted function, against the shared contract. -/
theorem compressShared_verified :
    Verified X86.target Impl.Argon2.X86.compress (Spec.Argon2.compressContract X86.abi) :=
  compressWide_verified.of_implies compress_implies

end VG.Proof.Argon2.X86
