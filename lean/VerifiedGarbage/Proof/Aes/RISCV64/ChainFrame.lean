module

public import VerifiedGarbage.Proof.Aes.RISCV64.Ecb
public import VerifiedGarbage.Proof.Aes.RISCV64.Prologue
public import VerifiedGarbage.Proof.Aes.RISCV64.Keys
public import VerifiedGarbage.Impl.Aes.RISCV64.Chain
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RISCV64.Align
import VerifiedGarbage.Proof.Aes.RISCV64.Blocks

/-!
# AES chaining on RISC-V: the frame

`chainFrame body pre post` (`Impl/Aes/RISCV64/Chain.lean`), the code of
`chain` and of the other chaining modes, with the arguments of
`vg_aes_ctr32`: as `vg_aes_ctr32`'s proof (`Ctr32.lean`), the prologue
rounds the scratch buffer up, saves the callee-saved registers and builds
the masks (`Prologue.lean`), the return address is stored in slot `raSlot`
and the state's address kept in `ra`, the key loop (`Keys.lean`) bitslices
the round keys and the state is loaded into the registers of block 0; then
each mode's `pre`, loop and `post` (`frame_wp`'s `hm`: from `FSetup`, what
holds then, to `FEnd`, which keeps what the epilogue needs, and the mode's
result); the epilogue stores the state and restores the registers.
`framePre wd len` is the precondition, with `len n` bytes of data for `n`
in `a4`, written if `wd`.
-/

@[expose] public section

namespace VG.Proof.Aes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.Align VG.RISCV64.Steps VG.Bitslice
  VG.Impl.Aes.RISCV64 VG.Proof.Aes

/-- The precondition of a chaining function with the arguments of
`vg_aes_ctr32`, `(schedule = a0, rounds = a1, state = a2, data = a3, n = a4,
scratch = a5)`, and `len n` bytes of data, which it writes if `wd`: as
`Proof.Aes.chainRISCV64`'s. -/
def framePre (wd : Bool) (len : Nat → Nat) (s : State) : Prop :=
  let sched : Region := ⟨s.gpr .a0, 240⟩
  let state : Region := ⟨s.gpr .a2, 16⟩
  let data : Region := ⟨s.gpr .a3, len (s.gpr .a4).toNat⟩
  let scratch : Region := ⟨s.gpr .a5, 2048⟩
  (if wd then s.rd = [sched] ∧ s.wr = [state, data, scratch]
    else s.rd = [sched, data] ∧ s.wr = [state, scratch]) ∧
  sched.Disjoint state ∧ sched.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
  state.Disjoint scratch ∧ (s.gpr .a2).toNat + 16 ≤ 2 ^ 64 ∧
  (s.gpr .a3).toNat + len (s.gpr .a4).toNat ≤ 2 ^ 64 ∧
  ((s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14)

/-- What a mode may write from the state its loop starts from: the S-box's
slots, two slots of its own (58 and 63, CFB8's input block), and the data. -/
abbrev fRegions (b D : Addr) (L : Nat) : List Region :=
  [⟨b, 320⟩, ⟨b + BitVec.ofNat 64 464, 8⟩, ⟨b + BitVec.ofNat 64 504, 8⟩, ⟨D, L⟩]

/-- What holds when a mode's `pre` runs, in `s₉`, for the call from `s₀`:
the scratch buffer `X` (rounded up to `b`), the masks, the bitsliced round
keys, the data and the state as `framePre` has them, the state in the
registers of block 0, its address in `ra`, and the memory changed only in
the scratch buffer. -/
structure FSetup (wd : Bool) (len : Nat → Nat) (s₀ s₉ : State) (X b : Addr) : Prop where
  X_eq : X = s₀.gpr .a5
  b_eq : b = X + BitVec.ofNat 64 (pad X)
  scr : Scr s₉ X 2048
  base : s₉.gpr sb = b
  masks : MasksAt s₉.mem b allKs
  keys : KeysAt s₉.mem (b + BitVec.ofNat 64 (1920 - 64 * (s₀.gpr .a1).toNat)) (s₀.gpr .a1).toNat
    (Spec.Aes.bytesAt s₀.mem (s₀.gpr .a0) (16 * ((s₀.gpr .a1).toNat + 1)))
  a0 : s₉.gpr .a0 = b + BitVec.ofNat 64 (1920 - 64 * (s₀.gpr .a1).toNat)
  rounds : (s₀.gpr .a1).toNat = 10 ∨ (s₀.gpr .a1).toNat = 12 ∨ (s₀.gpr .a1).toNat = 14
  rdD : (⟨s₀.gpr .a3, len (s₀.gpr .a4).toNat⟩ : Region) ∈ s₉.rd ++ s₉.wr
  dat : wd = true → (⟨s₀.gpr .a3, len (s₀.gpr .a4).toNat⟩ : Region) ∈ s₉.wr
  hn : len (s₀.gpr .a4).toNat < 2 ^ 64
  sep : Region.Disjoint ⟨s₀.gpr .a3, len (s₀.gpr .a4).toNat⟩ ⟨X, 2048⟩
  dSt : Region.Disjoint ⟨s₀.gpr .a3, len (s₀.gpr .a4).toNat⟩ ⟨s₀.gpr .a2, 16⟩
  stS : Region.Disjoint ⟨s₀.gpr .a2, 16⟩ ⟨X, 2048⟩
  hn0 : 0 < (s₀.gpr .a4).toNat
  a3 : s₉.gpr .a3 = s₀.gpr .a3
  a4 : s₉.gpr .a4 = s₀.gpr .a4
  ra : s₉.gpr .ra = s₀.gpr .a2
  stw : (⟨s₀.gpr .a2, 16⟩ : Region) ∈ s₉.wr
  st : regBlock (Q s₉) 0 = Spec.Aes.stateAt s₀.mem (s₀.gpr .a2)
  f₀ : Frame [⟨X, 2048⟩] s₀.mem s₉.mem
  rd : s₉.rd = s₀.rd
  wr : s₉.wr = s₀.wr

/-- What a mode's `post` leaves, from `s₉`: the scratch buffer's base, the
state's address, the regions it may access and the stack pointer as they
were, the memory changed only in `fRegions`, and its result `Res`. -/
structure FEnd (s₉ : State) (b D : Addr) (L : Nat) (Res : State → Prop) (s : State) : Prop where
  base : s.gpr sb = b
  ra : s.gpr .ra = s₉.gpr .ra
  rd : s.rd = s₉.rd
  wr : s.wr = s₉.wr
  sp : s.sp = s₉.sp
  frame : Frame (fRegions b D L) s₉.mem s.mem
  res : Res s

/-! ## The whole function -/

/-- The bytes stored by two `storeLE64`s, a doubleword each. -/
theorem bytesAt_writeW2 (m : Mem) (a : Addr) (v₁ v₂ : BitVec 64) {x : Spec.Aes.State}
    (hv : ∀ t < 16, (if t < 8 then v₁.extractLsb' (8 * t) 8 else v₂.extractLsb' (8 * (t - 8)) 8) =
      x.getD t 0) :
    Spec.Aes.bytesAt ((m.writeW a v₁).writeW (a + 8) v₂) a 16 = x.toList := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt])
  intro i h₁ h₂
  simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range]
  have hi : i < 16 := by simpa [Spec.Aes.bytesAt] using h₁
  rw [writeW2_apply, VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    ite_eq_left (show i < 16 from hi), hv i hi, getD_eq _ hi]
  simp

theorem stateAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {a : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨a, 16⟩ r) :
    Spec.Aes.stateAt m' a = Spec.Aes.stateAt m a := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Aes.stateAt, Vector.getElem_ofFn]
  exact hf.bytes (R := ⟨a, 16⟩) hd (by simp) hi

theorem not_chain_writes : ∀ r ∈ [Reg.ra, .a3, .a4, .a5], r ∉ keyWrites := by decide

/-- The frame: the callee-saved registers and the return address kept, and
either no blocks (`n = 0`: nothing changes) or the result of the mode's
loop, with the state stored back from the registers of block 0. -/
theorem frame_wp {body : Prog isa} {pre post : List Instr} {wd : Bool} {len : Nat → Nat} {s₀ : State}
    (hp : framePre wd len s₀) {Res : State → Prop}
    (hm : ∀ (s₉ : State) (X b : Addr), FSetup wd len s₀ s₉ X b →
      WP isa (.block pre) s₉ fun s => WP isa (.loop body (.nonzero .a4)) s fun s' =>
        WP isa (.block post) s' (FEnd s₉ b (s₀.gpr .a3) (len (s₀.gpr .a4).toNat) Res)) :
    WP isa (Impl.Aes.RISCV64.chainFrame body pre post) s₀ fun s' =>
      (∀ r ∈ RISCV64.preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
        ((s₀.gpr .a4).toNat = 0 ∧ s'.mem = s₀.mem ∨
          ∃ s, Res s ∧ s'.mem = (s.mem.writeW (s₀.gpr .a2) (s.gpr (q 0))).writeW (s₀.gpr .a2 + 8)
            (s.gpr (q 4))) := by
  obtain ⟨hrw, dSSt, dSS, dDSt, dDS, dStS, hwSt, hwrap, hR⟩ := hp
  have hrS : (⟨s₀.gpr .a0, 240⟩ : Region) ∈ s₀.rd := by
    cases wd <;> simp only [Bool.false_eq_true, ↓reduceIte] at hrw <;> rw [hrw.1] <;> simp
  have hwT : (⟨s₀.gpr .a2, 16⟩ : Region) ∈ s₀.wr := by
    cases wd <;> simp only [Bool.false_eq_true, ↓reduceIte] at hrw <;> rw [hrw.2] <;> simp
  have hwS : (⟨s₀.gpr .a5, 2048⟩ : Region) ∈ s₀.wr := by
    cases wd <;> simp only [Bool.false_eq_true, ↓reduceIte] at hrw <;> rw [hrw.2] <;> simp
  have hrD : (⟨s₀.gpr .a3, len (s₀.gpr .a4).toNat⟩ : Region) ∈ s₀.rd ++ s₀.wr := by
    cases wd <;> simp only [Bool.false_eq_true, ↓reduceIte] at hrw <;> rw [hrw.1, hrw.2] <;> simp
  have hwD : wd = true → (⟨s₀.gpr .a3, len (s₀.gpr .a4).toNat⟩ : Region) ∈ s₀.wr := by
    intro ho; subst ho; simp only [↓reduceIte] at hrw; rw [hrw.2]; simp
  let n := (s₀.gpr .a4).toNat
  have n16 : len n < 2 ^ 64 := by
    refine Nat.lt_of_not_le fun hc => dDSt (s₀.gpr .a2) ?_ (by simp [Region.Contains])
    simp only [Region.Contains]
    have := (s₀.gpr .a2 - s₀.gpr .a3).isLt
    simp only [n] at hc; omega
  have hR14 : (s₀.gpr .a1).toNat ≤ 14 := by omega
  let X := s₀.gpr .a5
  let b := X + BitVec.ofNat 64 (pad X)
  let R := (s₀.gpr .a1).toNat
  let St := s₀.gpr .a2
  let D := s₀.gpr .a3
  have dTb : Region.Disjoint ⟨St, 16⟩ ⟨b, 2040⟩ := dStS.sub_right (scr_base X (by omega))
  unfold Impl.Aes.RISCV64.chainFrame
  refine WP.ite (decide (n = 0)) (eval_zero_ofNat _ _ (by omega) (by simp [n])) (fun h0 => ?_)
    (fun h0 => ?_)
  · -- No blocks: nothing changes.
    have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨fun _ _ => rfl, rfl, .inl ⟨hn0, rfl⟩⟩
  have hn0 : n ≠ 0 := by simpa using h0
  -- The prologue.
  refine WP.seq ?_
  repeat rw [WP.block_append_iff (M := isa)]
  refine roundSb_wp fun s₁ b₁ o₁ m₁ rd₁ wr₁ sp₁ => ?_
  have hb₁ : s₁.gpr sb = b := b₁
  have hscr₁ : Scr s₁ X 2048 := ⟨by rw [wr₁]; exact hwS, hb₁⟩
  rw [saveRegs_eq]
  refine Spill.save_ok (rest := []) hscr₁.al savedOffs_ho (fun p hp => ⟨_, hscr₁.wr,
    hscr₁.contains (by have := savedOffs_range p hp; omega) (by decide)⟩) (WP.block_nil ?_)
  generalize hS : ({ s₁ with mem := Spill.saveMem s₁.mem (s₁.gpr sb) s₁.gpr savedOffs } : State) = s₁'
  have g₁' : s₁'.gpr = s₁.gpr := by rw [← hS]
  have mm₁ : s₁'.mem = Spill.saveMem s₁.mem (s₁.gpr sb) s₁.gpr savedOffs := by rw [← hS]
  have rd₁' : s₁'.rd = s₁.rd := by rw [← hS]
  have wr₁' : s₁'.wr = s₁.wr := by rw [← hS]
  have sv₁ : Spill.Saved b s₁.gpr savedOffs s₁'.mem := by
    rw [mm₁, ← hb₁]; exact Spill.saveMem_saved savedOffs_fits _ _ _
  have f₁ : Frame [⟨b + BitVec.ofNat 64 320, 96⟩] s₁.mem s₁'.mem := by
    rw [mm₁, ← hb₁]; exact Spill.saveMem_frame savedOffs_range (by decide) _ _ _
  have hscr₁' : Scr s₁' X 2048 := ⟨by rw [wr₁']; exact hscr₁.wr, by rw [g₁']; exact hscr₁.base⟩
  refine WP.mono (maskInit_ok hscr₁') fun s₂ ⟨mk₂, fm₂, g₂, rd₂, wr₂, sp₂⟩ => ?_
  have b₁' : s₁'.gpr sb = b := by rw [g₁']; exact hb₁
  rw [b₁'] at mk₂ fm₂
  have hb₂ : s₂.gpr sb = b := by rw [g₂ _ (by decide) (by decide)]; exact b₁'
  have hscr₂ : Scr s₂ X 2048 := ⟨by rw [wr₂]; exact hscr₁'.wr, hb₂⟩
  have k₂ : ∀ r, r ≠ t0 → r ≠ t1 → r ≠ sb → s₂.gpr r = s₀.gpr r := fun r h0 h1 h2 => by
    rw [g₂ r h0 h1, g₁', o₁ r h2]
  -- The return address in its slot, and the state's address in `ra`.
  have hslot : (⟨X, 2048⟩ : Region).Contains (b + BitVec.ofNat 64 496) 8 := by
    rw [← hb₂]; exact hscr₂.contains (by omega) (by decide)
  refine wp_sd (t := .ra) (n := sb) (off := 8 * raSlot) (a := b + BitVec.ofNat 64 496) (by decide)
    (by rw [hb₂]; rfl) (by rw [← hb₂]; exact Align.al_add (k := 8) hscr₂.al (by decide) (by decide))
    ⟨_, hscr₂.wr, hslot⟩ fun s₃₀ u₃₀ => ?_
  refine wp_mv fun s₃ v₃ => WP.block_nil ?_
  have g₃ : ∀ r, r ≠ .ra → s₃.gpr r = s₂.gpr r := fun r h => by rw [v₃.other r h, u₃₀.gpr]
  have ra₃ : s₃.gpr .ra = St := by rw [v₃.gpr, u₃₀.gpr, k₂ _ (by decide) (by decide) (by decide)]
  have m₃ : s₃.mem = s₂.mem.writeW (b + BitVec.ofNat 64 496) (s₀.gpr .ra) := by
    rw [v₃.mem, u₃₀.mem, k₂ _ (by decide) (by decide) (by decide)]
  have rd₃ : s₃.rd = s₂.rd := by rw [v₃.rd, u₃₀.rd]
  have wr₃ : s₃.wr = s₂.wr := by rw [v₃.wr, u₃₀.wr]
  have hscr₃ : Scr s₃ X 2048 := ⟨by rw [wr₃]; exact hscr₂.wr, by rw [g₃ _ (by decide)]; exact hscr₂.base⟩
  refine keySetup_wp (s := s₃) (R := R) (by
      rw [g₃ _ (by decide), k₂ _ (by decide) (by decide) (by decide)]; simp [R])
    hR14 fun s₄ a0₄ a2₄ a1₄ o₄ m₄ rd₄ wr₄ sp₄ => ?_
  have k₄ : ∀ r, r ≠ t0 → r ≠ t1 → r ≠ sb → r ≠ .a0 → r ≠ .a2 → r ≠ .a1 → r ≠ .ra →
      s₄.gpr r = s₀.gpr r :=
    fun r h0 h1 h2 h3 h4 h5 h6 => by rw [o₄ r h0 h3 h4 h5, g₃ r h6, k₂ r h0 h1 h2]
  have ra₄ : s₄.gpr .ra = St := by rw [o₄ _ (by decide) (by decide) (by decide) (by decide), ra₃]
  have hb₄ : s₄.gpr sb = b := by
    rw [o₄ sb (by decide) (by decide) (by decide) (by decide), g₃ _ (by decide)]; exact hb₂
  have hscr₄ : Scr s₄ X 2048 := ⟨by rw [wr₄, wr₃]; exact hscr₂.wr, hb₄⟩
  have fslot : Frame [⟨X, 2048⟩] s₂.mem s₄.mem := by
    rw [m₄, m₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hslot
  have f₀₄ : Frame [⟨X, 2048⟩] s₀.mem s₄.mem := by
    have f01 : Frame [⟨X, 2048⟩] s₀.mem s₁'.mem := fun x hx =>
      ((f₁.sub fun r hr => ⟨⟨X, 2048⟩, by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact scr_part X (by omega)⟩) x hx).trans
        (congrFun m₁ x)
    refine (f01.trans (fm₂.sub fun r hr => ⟨⟨X, 2048⟩, by simp, ?_⟩)).trans fslot
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact scr_part X (by omega)
    · exact scr_part X (by omega)
  have mk₄ : MasksAt s₄.mem b allKs := by
    rw [m₄, m₃]
    refine masks_frame ((Frame.refl [⟨b + BitVec.ofNat 64 496, 8⟩] _).writeW (List.mem_singleton_self _) _
      (Region.contains_self _ _)) (fun r hr => ?_) mk₂
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨Offset.disjoint b (by omega) (by omega) (by omega), Offset.disjoint b (by omega) (by omega) (by omega)⟩
  let w := Spec.Aes.bytesAt s₀.mem (s₀.gpr .a0) (16 * (R + 1))
  have hk : KSetup s₄ X b (s₀.gpr .a0) R w :=
    { scr := hscr₄
      base := hb₄
      masks := mk₄
      sch := List.mem_append_left _ (by rw [rd₄, rd₃, rd₂, rd₁', rd₁]; exact hrS)
      sep := dSS
      rounds := hR14
      w := fun i hi => by
        simp only [w, Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hi, Option.map_some, Option.getD_some]
        refine (f₀₄.bytes (R := ⟨s₀.gpr .a0, 240⟩) (fun r hr => ?_) (by simp) (by simp only; omega)).symm
        simp only [List.mem_singleton] at hr; subst hr; exact dSS }
  have hi₄ : KInv s₄ b (s₀.gpr .a0) R w R s₄ :=
    { hj := Nat.le_refl _
      a1 := a1₄
      a0 := by rw [a0₄, g₃ _ (by decide), k₂ _ (by decide) (by decide) (by decide)]
      a2 := by rw [a2₄, g₃ _ (by decide), hb₂]; simp [keyAddr, lastKey]
      rd := rfl
      wr := rfl
      sp := rfl
      keep := fun _ _ => rfl
      frame := Frame.refl _ _
      done := fun i h1 h2 => absurd h2 (by omega) }
  -- The key loop.
  refine WP.seq (WP.mono (keyLoop_ok hk hi₄) fun s₅ d₅ => ?_)
  refine WP.seq ?_
  rw [WP.block_append_iff (M := isa), WP.block_append_iff (M := isa)]
  unfold keyDone
  refine wp_addi (imm := 64) (by decide) fun s₆ u₆ => WP.block_nil ?_
  have g₆ : ∀ r ∈ [Reg.ra, .a3, .a4, .a5], s₆.gpr r = s₄.gpr r := fun r hr => by
    rw [u₆.other r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide),
      d₅.keep r (not_chain_writes r hr)]
  have hb₆ : s₆.gpr sb = b := by rw [show sb = .a5 from rfl, g₆ _ (by simp)]; exact hb₄
  have hK0 : s₆.gpr .a0 = b + BitVec.ofNat 64 (1920 - 64 * R) := by
    rw [u₆.gpr, d₅.a2]; exact BitVec.sub_add_cancel _ _
  have fK : Frame (kRegions b) s₄.mem s₆.mem := u₆.mem ▸ d₅.frame
  have kd : ∀ {x lx}, 320 ≤ x → x + lx ≤ 1024 → ∀ r ∈ kRegions b,
      Region.Disjoint ⟨b + BitVec.ofNat 64 x, lx⟩ r := by
    intro x lx h1 h2 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint_base _ h1 (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
  have slot₆ : s₆.mem.readW (b + BitVec.ofNat 64 496) 64 = s₀.gpr .ra := by
    rw [fK.readW (Region.contains_self _ _) (kd (by omega) (by omega)) (by decide), m₄, m₃,
      Mem.readW_writeW_self64]
  have hrd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, d₅.rd, rd₄, rd₃, rd₂, rd₁', rd₁]
  have hwr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, d₅.wr, wr₄, wr₃, wr₂, wr₁', wr₁]
  have ra₆ : s₆.gpr .ra = St := by rw [g₆ _ (by simp), ra₄]
  -- The state into the registers of block 0.
  unfold chainLoad
  repeat rw [WP.block_append_iff (M := isa)]
  obtain ⟨s₇, hs₇⟩ : ∃ s, s = s₆ := ⟨_, rfl⟩
  have u₇ : Upd s₆ s₇ .ra St := by subst hs₇; exact ⟨ra₆, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  rw [← hs₇]
  have hT : (⟨St, 16⟩ : Region) ∈ s₇.rd ++ s₇.wr :=
    List.mem_append_right _ (by rw [u₇.wr, hwr₆]; exact hwT)
  have hinT : ∀ d, d + 4 ≤ 16 → InRegions (s₇.rd ++ s₇.wr) (s₇.gpr .ra + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [u₇.gpr]; exact in_off hT (by omega) (by omega)
  refine WP.mono (Bytes.loadLE64_ok (d := q 0) (tmp := t0) (hi := t1) (n := .ra) (off := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simpa using hinT 0 (by omega)) (by simpa using hinT 4 (by omega)))
    fun s₈ ⟨e₈, g₈, m₈, rd₈, wr₈, sp₈⟩ => ?_
  have t2₈ : s₈.gpr .ra = St := by rw [g₈ _ (by decide) (by decide) (by decide), u₇.gpr]
  refine WP.mono (Bytes.loadLE64_ok (d := q 4) (tmp := t0) (hi := t1) (n := .ra) (off := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [t2₈, rd₈, wr₈, ← u₇.gpr]; exact hinT 8 (by omega))
    (by rw [t2₈, rd₈, wr₈, ← u₇.gpr]; exact hinT 12 (by omega)))
    fun s₉ ⟨e₉, g₉, m₉, rd₉, wr₉, sp₉⟩ => ?_
  have mem₉ : s₉.mem = s₆.mem := by rw [m₉, m₈, u₇.mem]
  have o₉ : ∀ r, r ≠ q 0 → r ≠ q 4 → r ≠ t0 → r ≠ t1 → r ≠ .ra → s₉.gpr r = s₆.gpr r :=
    fun r h0 h4 ht0 ht1 ht2 => by rw [g₉ r h4 ht0 ht1, g₈ r h0 ht0 ht1, u₇.other r ht2]
  -- The memory so far changed only in the scratch buffer.
  have f₀₉ : Frame [⟨X, 2048⟩] s₀.mem s₉.mem := by
    rw [mem₉]
    exact f₀₄.trans (fK.sub fun r hr => ⟨_, List.mem_singleton_self _, frame_regions hscr₄ hb₄ r hr⟩)
  have dT : ∀ r ∈ [(⟨X, 2048⟩ : Region)], Region.Disjoint ⟨St, 16⟩ r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dStS
  let iv := Spec.Aes.stateAt s₀.mem St
  have st₉ : regBlock (Q s₉) 0 = iv := by
    rw [regBlock_load (m := s₉.mem) (a := St) (c := 0) ?_ ?_, stateAt_frame f₀₉ dT]
    · show s₉.gpr (q 0) = _
      rw [g₉ _ (by decide) (by decide) (by decide), e₈, u₇.gpr, u₇.mem, ← mem₉]
      simp
    · show s₉.gpr (q 4) = _
      rw [e₉, t2₈, m₈, u₇.mem, ← mem₉]
      rfl
  have hb₉ : s₉.gpr sb = b := by
    rw [o₉ sb (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hb₆
  have a3₉ : s₉.gpr .a3 = D := by
    rw [o₉ .a3 (by decide) (by decide) (by decide) (by decide) (by decide), g₆ _ (by simp),
      k₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  have a4₉ : s₉.gpr .a4 = s₀.gpr .a4 := by
    rw [o₉ .a4 (by decide) (by decide) (by decide) (by decide) (by decide), g₆ _ (by simp),
      k₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  have ra₉ : s₉.gpr .ra = St := by
    rw [g₉ _ (by decide) (by decide) (by decide), g₈ _ (by decide) (by decide) (by decide), u₇.gpr]
  have hsF : FSetup wd len s₀ s₉ X b :=
    { X_eq := rfl
      b_eq := rfl
      scr := ⟨by rw [wr₉, wr₈, u₇.wr, hwr₆]; exact hwS, hb₉⟩
      base := hb₉
      masks := by rw [mem₉, u₆.mem]; exact masks_kept d₅.frame hk.masks
      keys := fun j hj => keyRel_congr (d₅.keys j hj) fun k hk => by
        rw [mem₉, u₆.mem, keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add, show 1920 - 64 * R + 64 * j =
          1920 - 64 * (R - j) by omega]
      a0 := by rw [o₉ .a0 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK0
      rounds := hR
      rdD := by rw [rd₉, rd₈, u₇.rd, wr₉, wr₈, u₇.wr, hrd₆, hwr₆]; exact hrD
      dat := fun ho => by rw [wr₉, wr₈, u₇.wr, hwr₆]; exact hwD ho
      hn := n16
      sep := dDS
      dSt := dDSt
      stS := dStS
      hn0 := by omega
      a3 := a3₉
      a4 := a4₉
      ra := ra₉
      stw := by rw [wr₉, wr₈, u₇.wr, hwr₆]; exact hwT
      st := st₉
      f₀ := f₀₉
      rd := by rw [rd₉, rd₈, u₇.rd, hrd₆]
      wr := by rw [wr₉, wr₈, u₇.wr, hwr₆] }
  -- The loop, between `pre` and `post`.
  refine WP.mono (hm s₉ X b hsF) fun s₉' hl => ?_
  refine WP.seq (WP.mono hl fun s₁₀' hpost => ?_)
  rw [WP.block_append_iff (M := isa), WP.block_append_iff (M := isa)]
  refine WP.mono hpost fun s₁₀ c₁₀ => ?_
  -- The epilogue: the state stored back, and the registers restored.
  have hb₁₀ : s₁₀.gpr sb = b := c₁₀.base
  have dE : ∀ {x lx}, 320 ≤ x → x + lx + 7 ≤ 2048 → (x + lx ≤ 464 ∨ 472 ≤ x) →
      (x + lx ≤ 504 ∨ 512 ≤ x) → ∀ r ∈ fRegions b D (len n),
      Region.Disjoint ⟨b + BitVec.ofNat 64 x, lx⟩ r := by
    intro x lx h1 h2 h3 h4 r hr
    simp only [fRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint_base _ h1 (by omega)
    · exact Offset.disjoint b (by omega) (by omega) (by omega)
    · exact Offset.disjoint b (by omega) (by omega) (by omega)
    · exact (dDS.sub_right (scr_part X h2)).symm
  have slot₁₀ : s₁₀.mem.readW (b + BitVec.ofNat 64 496) 64 = s₀.gpr .ra := by
    rw [c₁₀.frame.readW (Region.contains_self _ _) (dE (by omega) (by omega) (by omega) (by omega)) (by decide), mem₉, slot₆]
  have ra₁₀ : s₁₀.gpr .ra = St := c₁₀.ra.trans ra₉
  unfold chainStore
  repeat rw [WP.block_append_iff (M := isa)]
  obtain ⟨s₁₁, hs₁₁⟩ : ∃ s, s = s₁₀ := ⟨_, rfl⟩
  have u₁₁ : Upd s₁₀ s₁₁ .ra St := by subst hs₁₁; exact ⟨ra₁₀, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  rw [← hs₁₁]
  have hTw : (⟨St, 16⟩ : Region) ∈ s₁₁.wr := by rw [u₁₁.wr, c₁₀.wr, wr₉, wr₈, u₇.wr, hwr₆]; exact hwT
  have hinw : ∀ {t : State} (d : Nat), t.gpr .ra = St → t.wr = s₁₁.wr →
      d + 4 ≤ 16 → InRegions t.wr (t.gpr .ra + BitVec.ofNat 64 d) 4 := fun d ha hw hd => by
    rw [ha, hw]; exact in_off hTw (by omega) (by omega)
  refine WP.mono (Bytes.storeLE64_ok (v := q 0) (tmp := t0) (hi := t1) (n := .ra) (off := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simpa using hinw 0 u₁₁.gpr rfl (by omega)) (hinw 4 u₁₁.gpr rfl (by omega)))
    fun s₁₂ ⟨m₁₂, g₁₂, rd₁₂, wr₁₂, sp₁₂⟩ => ?_
  have t2₁₂ : s₁₂.gpr .ra = St := (g₁₂ _ (by decide) (by decide)).trans u₁₁.gpr
  refine WP.mono (Bytes.storeLE64_ok (v := q 4) (tmp := t0) (hi := t1) (n := .ra) (off := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (hinw 8 t2₁₂ wr₁₂ (by omega)) (hinw 12 t2₁₂ wr₁₂ (by omega)))
    fun s₁₃ ⟨m₁₃, g₁₃, rd₁₃, wr₁₃, sp₁₃⟩ => ?_
  have v₀ : s₁₁.gpr (q 0) = s₁₀.gpr (q 0) := u₁₁.other _ (by decide)
  have v₄ : s₁₂.gpr (q 4) = s₁₀.gpr (q 4) := by rw [g₁₂ _ (by decide) (by decide), u₁₁.other _ (by decide)]
  have hmem : s₁₃.mem = (s₁₀.mem.writeW St (s₁₀.gpr (q 0))).writeW (St + 8) (s₁₀.gpr (q 4)) := by
    have e12 : St + BitVec.ofNat 64 (8 + 4) = St + 8 + BitVec.ofNat 64 4 := (Offset.add_add _ _ _).symm
    rw [m₁₃, t2₁₂, v₄, m₁₂, u₁₁.gpr, v₀, u₁₁.mem, show St + BitVec.ofNat 64 0 = St by simp,
      show St + BitVec.ofNat 64 (0 + 4) = St + BitVec.ofNat 64 4 from rfl, Words64.writeW64_split,
      show St + BitVec.ofNat 64 8 = St + 8 from rfl, e12, Words64.writeW64_split]
  have fT : Frame [⟨St, 16⟩] s₁₀.mem s₁₃.mem := by
    rw [hmem]
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
    · simpa using Offset.contains_base St (d := 0) (n := 8) (k := 16) (by omega) (by omega)
    · exact Offset.contains_base St (d := 8) (n := 8) (k := 16) (by omega) (by omega)
  -- The saved registers are still in their slots.
  have sv : Spill.Saved b s₁.gpr savedOffs s₁₃.mem := by
    have dS : ∀ r ∈ [(⟨b + BitVec.ofNat 64 416, 48⟩ : Region), ⟨b + BitVec.ofNat 64 512, 96⟩],
        Region.Disjoint ⟨b + BitVec.ofNat 64 320, 96⟩ r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint b (by omega) (by omega) (by omega)
      · exact Offset.disjoint b (by omega) (by omega) (by omega)
    have dSl : ∀ r ∈ [(⟨b + BitVec.ofNat 64 496, 8⟩ : Region)],
        Region.Disjoint ⟨b + BitVec.ofNat 64 320, 96⟩ r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint b (by omega) (by omega) (by omega)
    have fSl : Frame [⟨b + BitVec.ofNat 64 496, 8⟩] s₂.mem s₄.mem := by
      rw [m₄, m₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have dT' : ∀ r ∈ [(⟨St, 16⟩ : Region)], Region.Disjoint ⟨b + BitVec.ofNat 64 320, 96⟩ r :=
      fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (dTb.sub_right (Offset.sub_base b (by omega))).symm
    have fK₉ : Frame (kRegions b) s₄.mem s₉.mem := by rw [mem₉]; exact fK
    exact (((((sv₁.frame_in savedOffs_range fm₂ dS).frame_in savedOffs_range fSl dSl).frame_in
      savedOffs_range fK₉ (kd (by omega) (by omega))).frame_in savedOffs_range c₁₀.frame
      (dE (by omega) (by omega) (by omega) (by omega))).frame_in savedOffs_range fT dT')
  have hb₁₃ : s₁₃.gpr sb = b := by
    rw [g₁₃ _ (by decide) (by decide), g₁₂ _ (by decide) (by decide), u₁₁.other _ (by decide), hb₁₀]
  have hscr₁₃ : Scr s₁₃ X 2048 :=
    ⟨by rw [wr₁₃, wr₁₂]; exact (u₁₁.wr ▸ c₁₀.wr ▸ hsF.scr.wr),
      by rw [g₁₃ _ (by decide) (by decide), g₁₂ _ (by decide) (by decide), u₁₁.other _ (by decide), hb₁₀]⟩
  -- The return address back from its slot.
  have slot₁₃ : s₁₃.mem.readW (b + BitVec.ofNat 64 496) 64 = s₀.gpr .ra := by
    rw [fT.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (dTb.sub_right (Offset.sub_base b (by omega))).symm) (by decide), slot₁₀]
  refine wp_ld (t := .ra) (n := sb) (off := 8 * raSlot) (a := b + BitVec.ofNat 64 496) (by decide)
    (by rw [hb₁₃]; rfl) (by rw [← hb₄]; exact Align.al_add (k := 8) hscr₄.al (by decide) (by decide))
    ⟨_, List.mem_append_right _ hscr₁₃.wr, hslot⟩ fun s₁₅ u₁₅ => WP.block_nil ?_
  rw [slot₁₃] at u₁₅
  have hb₁₅ : s₁₅.gpr sb = b := by rw [u₁₅.other _ (by decide), hb₁₃]
  have hscr₁₅ : Scr s₁₅ X 2048 := ⟨by rw [u₁₅.wr]; exact hscr₁₃.wr, by rw [u₁₅.other _ (by decide)]; exact hscr₁₃.base⟩
  rw [restoreRegs_eq]
  refine WP.mono (Spill.restore_wp (B := b) (by rw [← hb₁]; exact hscr₁.al) hb₁₅ savedOffs_ho
    savedOffs_restorable (fun p hp => ⟨_, List.mem_append_right _ hscr₁₅.wr, by
      rw [← hb₁₅]
      exact hscr₁₅.contains (by have := savedOffs_range p hp; omega) (by decide)⟩) (by rw [u₁₅.mem]; exact sv))
    fun s₁₄ rs₁₄ => ?_
  refine ⟨fun r hr => ?_, ?_, .inr ⟨s₁₀, c₁₀.res, by rw [rs₁₄.mem, u₁₅.mem, hmem]⟩⟩
  · have hr' : r ∈ savedOffs.map Prod.fst := by rw [savedOffs_regs]; exact hr
    rw [rs₁₄.gpr_of (.inl hr')]
    have : r ∉ [sb] := by revert hr; revert r; decide
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rw [o₁ r this]
  · rw [rs₁₄.other _ not_saved_ra, u₁₅.gpr]

end VG.Proof.Aes.RISCV64
