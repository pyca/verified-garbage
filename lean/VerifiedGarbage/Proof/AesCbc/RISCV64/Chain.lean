module

public import VerifiedGarbage.Proof.AesCbc.RISCV64.Loop
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.Loop
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
meta import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
meta import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Impl.Aes.RISCV64.Chain
public import VerifiedGarbage.Proof.Aes.RISCV64.Ecb
public import VerifiedGarbage.Proof.Aes.RISCV64.Prologue
public import VerifiedGarbage.Proof.Aes.RISCV64.Common
public import VerifiedGarbage.Spec.Cmac
public import VerifiedGarbage.Spec.Cbc.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RISCV64.Align
import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Proof.Aes.RISCV64.Blocks
meta import VerifiedGarbage.Proof.Aes.RISCV64.Ecb
meta import VerifiedGarbage.Proof.Aes.RISCV64.Prologue
meta import VerifiedGarbage.Proof.Aes.RISCV64.Common
meta import VerifiedGarbage.Impl.Aes.RISCV64.Chain
meta import VerifiedGarbage.Spec.Cmac
meta import VerifiedGarbage.Spec.Cbc.Contract
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
meta import VerifiedGarbage.Proof.Framework.RISCV64.Words64
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RISCV64.Align
meta import VerifiedGarbage.Proof.AesCbc.Spec
meta import VerifiedGarbage.Proof.Aes.RISCV64.Blocks

/-! ### `Aes.RISCV64.ChainVerified`, which this module and modules that import it used -/

section

/-! ### `Aes.RISCV64.Chain`, which this module and modules that import it used -/

section

/-! ### `Aes.RISCV64.ChainFrame`, which this module and modules that import it used -/

section

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
slots, slots of its own (58 and 63, CFB8's input block; 78–87, the state and
the blocks of `wide`, `Impl/Aes/RISCV64/Wide.lean`), and the data. -/
abbrev fRegions (b D : Addr) (L : Nat) : List Region :=
  [⟨b, 320⟩, ⟨b + BitVec.ofNat 64 464, 8⟩, ⟨b + BitVec.ofNat 64 504, 8⟩, ⟨b + BitVec.ofNat 64 624, 80⟩,
    ⟨D, L⟩]

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
  obtain hi : i < 16 := by simpa [Spec.Aes.bytesAt] using h₁
  rw [writeW2_apply, VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi]),
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
  obtain hrS : (⟨s₀.gpr .a0, 240⟩ : Region) ∈ s₀.rd := by
    cases wd <;> simp only [Bool.false_eq_true, ↓reduceIte] at hrw <;> rw [hrw.1] <;> simp
  obtain hwT : (⟨s₀.gpr .a2, 16⟩ : Region) ∈ s₀.wr := by
    cases wd <;> simp only [Bool.false_eq_true, ↓reduceIte] at hrw <;> rw [hrw.2] <;> simp
  obtain hwS : (⟨s₀.gpr .a5, 2048⟩ : Region) ∈ s₀.wr := by
    cases wd <;> simp only [Bool.false_eq_true, ↓reduceIte] at hrw <;> rw [hrw.2] <;> simp
  obtain hrD : (⟨s₀.gpr .a3, len (s₀.gpr .a4).toNat⟩ : Region) ∈ s₀.rd ++ s₀.wr := by
    cases wd <;> simp only [Bool.false_eq_true, ↓reduceIte] at hrw <;> rw [hrw.1, hrw.2] <;> simp
  obtain hwD : wd = true → (⟨s₀.gpr .a3, len (s₀.gpr .a4).toNat⟩ : Region) ∈ s₀.wr := by
    intro ho; subst ho; simp only [↓reduceIte] at hrw; rw [hrw.2]; simp
  let n := (s₀.gpr .a4).toNat
  obtain n16 : len n < 2 ^ 64 := by
    refine Nat.lt_of_not_le fun hc => dDSt (s₀.gpr .a2) ?_ (by simp [Region.Contains])
    simp only [Region.Contains]
    have := (s₀.gpr .a2 - s₀.gpr .a3).isLt
    simp only [n] at hc; omega_using [hc]
  obtain hR14 : (s₀.gpr .a1).toNat ≤ 14 := by omega_using [hR]
  let X := s₀.gpr .a5
  let b := X + BitVec.ofNat 64 (pad X)
  let R := (s₀.gpr .a1).toNat
  let St := s₀.gpr .a2
  let D := s₀.gpr .a3
  obtain dTb : Region.Disjoint ⟨St, 16⟩ ⟨b, 2040⟩ := dStS.sub_right (scr_base X (by omega_using []))
  unfold Impl.Aes.RISCV64.chainFrame
  refine WP.ite (decide (n = 0)) (eval_zero_ofNat _ _ (by omega_using []) (by simp [n])) (fun h0 => ?_)
    (fun h0 => ?_)
  · -- No blocks: nothing changes.
    obtain hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨fun _ _ => rfl, rfl, .inl ⟨hn0, rfl⟩⟩
  obtain hn0 : n ≠ 0 := by simpa using h0
  -- The prologue.
  refine WP.seq ?_
  repeat rw [WP.block_append_iff (M := isa)]
  refine roundSb_wp fun s₁ b₁ o₁ m₁ rd₁ wr₁ sp₁ => ?_
  have hb₁ : s₁.gpr sb = b := b₁
  obtain hscr₁ : Scr s₁ X 2048 := ⟨by rw [wr₁]; exact hwS, hb₁⟩
  rw [saveRegs_eq]
  refine Spill.save_ok (rest := []) hscr₁.al savedOffs_ho (fun p hp => ⟨_, hscr₁.wr,
    hscr₁.contains (by have := savedOffs_range p hp; omega_using [this]) (by decide)⟩) (WP.block_nil ?_)
  generalize hS : ({ s₁ with mem := Spill.saveMem s₁.mem (s₁.gpr sb) s₁.gpr savedOffs } : State) = s₁'
  obtain g₁' : s₁'.gpr = s₁.gpr := by rw [← hS]
  obtain mm₁ : s₁'.mem = Spill.saveMem s₁.mem (s₁.gpr sb) s₁.gpr savedOffs := by rw [← hS]
  obtain rd₁' : s₁'.rd = s₁.rd := by rw [← hS]
  obtain wr₁' : s₁'.wr = s₁.wr := by rw [← hS]
  obtain sv₁ : Spill.Saved b s₁.gpr savedOffs s₁'.mem := by
    rw [mm₁, ← hb₁]; exact Spill.saveMem_saved savedOffs_fits _ _ _
  obtain f₁ : Frame [⟨b + BitVec.ofNat 64 320, 96⟩] s₁.mem s₁'.mem := by
    rw [mm₁, ← hb₁]; exact Spill.saveMem_frame savedOffs_range (by decide) _ _ _
  obtain hscr₁' : Scr s₁' X 2048 := ⟨by rw [wr₁']; exact hscr₁.wr, by rw [g₁']; exact hscr₁.base⟩
  refine WP.mono (maskInit_ok hscr₁') fun s₂ ⟨mk₂, fm₂, g₂, rd₂, wr₂, sp₂⟩ => ?_
  obtain b₁' : s₁'.gpr sb = b := by rw [g₁']; exact hb₁
  rw [b₁'] at mk₂ fm₂
  obtain hb₂ : s₂.gpr sb = b := by rw [g₂ _ (by decide) (by decide)]; exact b₁'
  obtain hscr₂ : Scr s₂ X 2048 := ⟨by rw [wr₂]; exact hscr₁'.wr, hb₂⟩
  obtain k₂ : ∀ r, r ≠ t0 → r ≠ t1 → r ≠ sb → s₂.gpr r = s₀.gpr r := fun r h0 h1 h2 => by
    rw [g₂ r h0 h1, g₁', o₁ r h2]
  -- The return address in its slot, and the state's address in `ra`.
  obtain hslot : (⟨X, 2048⟩ : Region).Contains (b + BitVec.ofNat 64 496) 8 := by
    rw [← hb₂]; exact hscr₂.contains (by omega_using []) (by decide)
  refine wp_sd (t := .ra) (n := sb) (off := 8 * raSlot) (a := b + BitVec.ofNat 64 496) (by decide)
    (by rw [hb₂]; rfl) (by rw [← hb₂]; exact Align.al_add (k := 8) hscr₂.al (by decide) (by decide))
    ⟨_, hscr₂.wr, hslot⟩ fun s₃₀ u₃₀ => ?_
  refine wp_mv fun s₃ v₃ => WP.block_nil ?_
  obtain g₃ : ∀ r, r ≠ .ra → s₃.gpr r = s₂.gpr r := fun r h => by rw [v₃.other r h, u₃₀.gpr]
  obtain ra₃ : s₃.gpr .ra = St := by rw [v₃.gpr, u₃₀.gpr, k₂ _ (by decide) (by decide) (by decide)]
  obtain m₃ : s₃.mem = s₂.mem.writeW (b + BitVec.ofNat 64 496) (s₀.gpr .ra) := by
    rw [v₃.mem, u₃₀.mem, k₂ _ (by decide) (by decide) (by decide)]
  obtain rd₃ : s₃.rd = s₂.rd := by rw [v₃.rd, u₃₀.rd]
  obtain wr₃ : s₃.wr = s₂.wr := by rw [v₃.wr, u₃₀.wr]
  obtain hscr₃ : Scr s₃ X 2048 := ⟨by rw [wr₃]; exact hscr₂.wr, by rw [g₃ _ (by decide)]; exact hscr₂.base⟩
  refine keySetup_wp (s := s₃) (R := R) (by
      rw [g₃ _ (by decide), k₂ _ (by decide) (by decide) (by decide)]; simp [R])
    hR14 fun s₄ a0₄ a2₄ a1₄ o₄ m₄ rd₄ wr₄ sp₄ => ?_
  obtain k₄ : ∀ r, r ≠ t0 → r ≠ t1 → r ≠ sb → r ≠ .a0 → r ≠ .a2 → r ≠ .a1 → r ≠ .ra →
      s₄.gpr r = s₀.gpr r :=
    fun r h0 h1 h2 h3 h4 h5 h6 => by rw [o₄ r h0 h3 h4 h5, g₃ r h6, k₂ r h0 h1 h2]
  obtain ra₄ : s₄.gpr .ra = St := by rw [o₄ _ (by decide) (by decide) (by decide) (by decide), ra₃]
  obtain hb₄ : s₄.gpr sb = b := by
    rw [o₄ sb (by decide) (by decide) (by decide) (by decide), g₃ _ (by decide)]; exact hb₂
  obtain hscr₄ : Scr s₄ X 2048 := ⟨by rw [wr₄, wr₃]; exact hscr₂.wr, hb₄⟩
  obtain fslot : Frame [⟨X, 2048⟩] s₂.mem s₄.mem := by
    rw [m₄, m₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hslot
  obtain f₀₄ : Frame [⟨X, 2048⟩] s₀.mem s₄.mem := by
    obtain f01 : Frame [⟨X, 2048⟩] s₀.mem s₁'.mem := fun x hx =>
      ((f₁.sub fun r hr => ⟨⟨X, 2048⟩, by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact scr_part X (by omega_using [])⟩) x hx).trans
        (congrFun m₁ x)
    refine (f01.trans (fm₂.sub fun r hr => ⟨⟨X, 2048⟩, by simp, ?_⟩)).trans fslot
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact scr_part X (by omega_using [])
    · exact scr_part X (by omega_using [])
  obtain mk₄ : MasksAt s₄.mem b allKs := by
    rw [m₄, m₃]
    refine masks_frame ((Frame.refl [⟨b + BitVec.ofNat 64 496, 8⟩] _).writeW (List.mem_singleton_self _) _
      (Region.contains_self _ _)) (fun r hr => ?_) mk₂
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨Offset.disjoint b (by omega_using []) (by omega_using []) (by omega_using []), Offset.disjoint b (by omega_using []) (by omega_using []) (by omega_using [])⟩
  let w := Spec.Aes.bytesAt s₀.mem (s₀.gpr .a0) (16 * (R + 1))
  obtain hk : KSetup s₄ X b (s₀.gpr .a0) R w :=
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
  obtain hi₄ : KInv s₄ b (s₀.gpr .a0) R w R s₄ :=
    { hj := Nat.le_refl _
      a1 := a1₄
      a0 := by rw [a0₄, g₃ _ (by decide), k₂ _ (by decide) (by decide) (by decide)]
      a2 := by rw [a2₄, g₃ _ (by decide), hb₂]; simp [keyAddr, lastKey]
      rd := rfl
      wr := rfl
      sp := rfl
      keep := fun _ _ => rfl
      frame := Frame.refl _ _
      done := fun i h1 h2 => absurd h2 (by omega_using [h1]) }
  -- The key loop.
  refine WP.seq (WP.mono (keyLoop_ok hk hi₄) fun s₅ d₅ => ?_)
  refine WP.seq ?_
  rw [WP.block_append_iff (M := isa), WP.block_append_iff (M := isa)]
  unfold keyDone
  refine wp_addi (imm := 64) (by decide) fun s₆ u₆ => WP.block_nil ?_
  obtain g₆ : ∀ r ∈ [Reg.ra, .a3, .a4, .a5], s₆.gpr r = s₄.gpr r := fun r hr => by
    rw [u₆.other r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide),
      d₅.keep r (not_chain_writes r hr)]
  obtain hb₆ : s₆.gpr sb = b := by rw [show sb = .a5 from rfl, g₆ _ (by simp)]; exact hb₄
  obtain hK0 : s₆.gpr .a0 = b + BitVec.ofNat 64 (1920 - 64 * R) := by
    rw [u₆.gpr, d₅.a2]; exact BitVec.sub_add_cancel _ _
  obtain fK : Frame (kRegions b) s₄.mem s₆.mem := u₆.mem ▸ d₅.frame
  obtain kd : ∀ {x lx}, 320 ≤ x → x + lx ≤ 1024 → ∀ r ∈ kRegions b,
      Region.Disjoint ⟨b + BitVec.ofNat 64 x, lx⟩ r := by
    intro x lx h1 h2 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint_base _ h1 (by omega_using [h2])
    · exact Offset.disjoint _ (by omega_using [h2]) (by omega_using [h2]) (by omega_using [])
  obtain slot₆ : s₆.mem.readW (b + BitVec.ofNat 64 496) 64 = s₀.gpr .ra := by
    rw [fK.readW (Region.contains_self _ _) (kd (by omega_using []) (by omega_using [])) (by decide), m₄, m₃,
      Mem.readW_writeW_self64]
  obtain hrd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, d₅.rd, rd₄, rd₃, rd₂, rd₁', rd₁]
  obtain hwr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, d₅.wr, wr₄, wr₃, wr₂, wr₁', wr₁]
  obtain ra₆ : s₆.gpr .ra = St := by rw [g₆ _ (by simp), ra₄]
  -- The state into the registers of block 0.
  unfold chainLoad
  repeat rw [WP.block_append_iff (M := isa)]
  obtain ⟨s₇, hs₇⟩ : ∃ s, s = s₆ := ⟨_, rfl⟩
  obtain u₇ : Upd s₆ s₇ .ra St := by subst hs₇; exact ⟨ra₆, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  rw [← hs₇]
  obtain hT : (⟨St, 16⟩ : Region) ∈ s₇.rd ++ s₇.wr :=
    List.mem_append_right _ (by rw [u₇.wr, hwr₆]; exact hwT)
  obtain hinT : ∀ d, d + 4 ≤ 16 → InRegions (s₇.rd ++ s₇.wr) (s₇.gpr .ra + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [u₇.gpr]; exact in_off hT (by omega_using [hd]) (by omega_using [])
  refine WP.mono (Bytes.loadLE64_ok (d := q 0) (tmp := t0) (hi := t1) (n := .ra) (off := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simpa using hinT 0 (by omega_using [])) (by simpa using hinT 4 (by omega_using [])))
    fun s₈ ⟨e₈, g₈, m₈, rd₈, wr₈, sp₈⟩ => ?_
  obtain t2₈ : s₈.gpr .ra = St := by rw [g₈ _ (by decide) (by decide) (by decide), u₇.gpr]
  refine WP.mono (Bytes.loadLE64_ok (d := q 4) (tmp := t0) (hi := t1) (n := .ra) (off := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [t2₈, rd₈, wr₈, ← u₇.gpr]; exact hinT 8 (by omega_using []))
    (by rw [t2₈, rd₈, wr₈, ← u₇.gpr]; exact hinT 12 (by omega_using [])))
    fun s₉ ⟨e₉, g₉, m₉, rd₉, wr₉, sp₉⟩ => ?_
  obtain mem₉ : s₉.mem = s₆.mem := by rw [m₉, m₈, u₇.mem]
  obtain o₉ : ∀ r, r ≠ q 0 → r ≠ q 4 → r ≠ t0 → r ≠ t1 → r ≠ .ra → s₉.gpr r = s₆.gpr r :=
    fun r h0 h4 ht0 ht1 ht2 => by rw [g₉ r h4 ht0 ht1, g₈ r h0 ht0 ht1, u₇.other r ht2]
  -- The memory so far changed only in the scratch buffer.
  obtain f₀₉ : Frame [⟨X, 2048⟩] s₀.mem s₉.mem := by
    rw [mem₉]
    exact f₀₄.trans (fK.sub fun r hr => ⟨_, List.mem_singleton_self _, frame_regions hscr₄ hb₄ r hr⟩)
  obtain dT : ∀ r ∈ [(⟨X, 2048⟩ : Region)], Region.Disjoint ⟨St, 16⟩ r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dStS
  let iv := Spec.Aes.stateAt s₀.mem St
  obtain st₉ : regBlock (Q s₉) 0 = iv := by
    rw [regBlock_load (m := s₉.mem) (a := St) (c := 0) ?_ ?_, stateAt_frame f₀₉ dT]
    · show s₉.gpr (q 0) = _
      rw [g₉ _ (by decide) (by decide) (by decide), e₈, u₇.gpr, u₇.mem, ← mem₉]
      simp
    · show s₉.gpr (q 4) = _
      rw [e₉, t2₈, m₈, u₇.mem, ← mem₉]
      rfl
  obtain hb₉ : s₉.gpr sb = b := by
    rw [o₉ sb (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hb₆
  obtain a3₉ : s₉.gpr .a3 = D := by
    rw [o₉ .a3 (by decide) (by decide) (by decide) (by decide) (by decide), g₆ _ (by simp),
      k₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  obtain a4₉ : s₉.gpr .a4 = s₀.gpr .a4 := by
    rw [o₉ .a4 (by decide) (by decide) (by decide) (by decide) (by decide), g₆ _ (by simp),
      k₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  obtain ra₉ : s₉.gpr .ra = St := by
    rw [g₉ _ (by decide) (by decide) (by decide), g₈ _ (by decide) (by decide) (by decide), u₇.gpr]
  obtain hsF : FSetup wd len s₀ s₉ X b :=
    { X_eq := rfl
      b_eq := rfl
      scr := ⟨by rw [wr₉, wr₈, u₇.wr, hwr₆]; exact hwS, hb₉⟩
      base := hb₉
      masks := by rw [mem₉, u₆.mem]; exact masks_kept d₅.frame hk.masks
      keys := fun j hj => keyRel_congr (d₅.keys j hj) fun k hk => by
        rw [mem₉, u₆.mem, keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add, show 1920 - 64 * R + 64 * j =
          1920 - 64 * (R - j) by omega_using [hR, hj]]
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
  obtain dE : ∀ {x lx}, 320 ≤ x → x + lx + 7 ≤ 2048 → (x + lx ≤ 464 ∨ 472 ≤ x) →
      (x + lx ≤ 504 ∨ 512 ≤ x) → (x + lx ≤ 624 ∨ 704 ≤ x) → ∀ r ∈ fRegions b D (len n),
      Region.Disjoint ⟨b + BitVec.ofNat 64 x, lx⟩ r := by
    intro x lx h1 h2 h3 h4 h5 r hr
    simp only [fRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact Offset.disjoint_base _ h1 (by omega_using [h2])
    · exact Offset.disjoint b (by omega_using [h3]) (by omega_using [h2]) (by omega_using [])
    · exact Offset.disjoint b (by omega_using [h4]) (by omega_using [h2]) (by omega_using [])
    · exact Offset.disjoint b (by omega_using [h5]) (by omega_using [h2]) (by omega_using [])
    · exact (dDS.sub_right (scr_part X h2)).symm
  obtain slot₁₀ : s₁₀.mem.readW (b + BitVec.ofNat 64 496) 64 = s₀.gpr .ra := by
    rw [c₁₀.frame.readW (Region.contains_self _ _) (dE (by omega_using []) (by omega_using []) (by omega_using []) (by omega_using []) (by omega_using [])) (by decide), mem₉, slot₆]
  obtain ra₁₀ : s₁₀.gpr .ra = St := c₁₀.ra.trans ra₉
  unfold chainStore
  repeat rw [WP.block_append_iff (M := isa)]
  obtain ⟨s₁₁, hs₁₁⟩ : ∃ s, s = s₁₀ := ⟨_, rfl⟩
  obtain u₁₁ : Upd s₁₀ s₁₁ .ra St := by subst hs₁₁; exact ⟨ra₁₀, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  rw [← hs₁₁]
  obtain hTw : (⟨St, 16⟩ : Region) ∈ s₁₁.wr := by rw [u₁₁.wr, c₁₀.wr, wr₉, wr₈, u₇.wr, hwr₆]; exact hwT
  obtain hinw : ∀ {t : State} (d : Nat), t.gpr .ra = St → t.wr = s₁₁.wr →
      d + 4 ≤ 16 → InRegions t.wr (t.gpr .ra + BitVec.ofNat 64 d) 4 := fun d ha hw hd => by
    rw [ha, hw]; exact in_off hTw (by omega_using [hd]) (by omega_using [])
  refine WP.mono (Bytes.storeLE64_ok (v := q 0) (tmp := t0) (hi := t1) (n := .ra) (off := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simpa using hinw 0 u₁₁.gpr rfl (by omega_using [])) (hinw 4 u₁₁.gpr rfl (by omega_using [])))
    fun s₁₂ ⟨m₁₂, g₁₂, rd₁₂, wr₁₂, sp₁₂⟩ => ?_
  obtain t2₁₂ : s₁₂.gpr .ra = St := (g₁₂ _ (by decide) (by decide)).trans u₁₁.gpr
  refine WP.mono (Bytes.storeLE64_ok (v := q 4) (tmp := t0) (hi := t1) (n := .ra) (off := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (hinw 8 t2₁₂ wr₁₂ (by omega_using [])) (hinw 12 t2₁₂ wr₁₂ (by omega_using [])))
    fun s₁₃ ⟨m₁₃, g₁₃, rd₁₃, wr₁₃, sp₁₃⟩ => ?_
  obtain v₀ : s₁₁.gpr (q 0) = s₁₀.gpr (q 0) := u₁₁.other _ (by decide)
  obtain v₄ : s₁₂.gpr (q 4) = s₁₀.gpr (q 4) := by rw [g₁₂ _ (by decide) (by decide), u₁₁.other _ (by decide)]
  obtain hmem : s₁₃.mem = (s₁₀.mem.writeW St (s₁₀.gpr (q 0))).writeW (St + 8) (s₁₀.gpr (q 4)) := by
    obtain e12 : St + BitVec.ofNat 64 (8 + 4) = St + 8 + BitVec.ofNat 64 4 := (Offset.add_add _ _ _).symm
    rw [m₁₃, t2₁₂, v₄, m₁₂, u₁₁.gpr, v₀, u₁₁.mem, show St + BitVec.ofNat 64 0 = St by simp,
      show St + BitVec.ofNat 64 (0 + 4) = St + BitVec.ofNat 64 4 from rfl, Words64.writeW64_split,
      show St + BitVec.ofNat 64 8 = St + 8 from rfl, e12, Words64.writeW64_split]
  obtain fT : Frame [⟨St, 16⟩] s₁₀.mem s₁₃.mem := by
    rw [hmem]
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
    · simpa using Offset.contains_base St (d := 0) (n := 8) (k := 16) (by omega_using []) (by omega_using [])
    · exact Offset.contains_base St (d := 8) (n := 8) (k := 16) (by omega_using []) (by omega_using [])
  -- The saved registers are still in their slots.
  obtain sv : Spill.Saved b s₁.gpr savedOffs s₁₃.mem := by
    obtain dS : ∀ r ∈ [(⟨b + BitVec.ofNat 64 416, 48⟩ : Region), ⟨b + BitVec.ofNat 64 512, 96⟩],
        Region.Disjoint ⟨b + BitVec.ofNat 64 320, 96⟩ r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint b (by omega_using []) (by omega_using []) (by omega_using [])
      · exact Offset.disjoint b (by omega_using []) (by omega_using []) (by omega_using [])
    obtain dSl : ∀ r ∈ [(⟨b + BitVec.ofNat 64 496, 8⟩ : Region)],
        Region.Disjoint ⟨b + BitVec.ofNat 64 320, 96⟩ r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint b (by omega_using []) (by omega_using []) (by omega_using [])
    obtain fSl : Frame [⟨b + BitVec.ofNat 64 496, 8⟩] s₂.mem s₄.mem := by
      rw [m₄, m₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    obtain dT' : ∀ r ∈ [(⟨St, 16⟩ : Region)], Region.Disjoint ⟨b + BitVec.ofNat 64 320, 96⟩ r :=
      fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (dTb.sub_right (Offset.sub_base b (by omega_using []))).symm
    obtain fK₉ : Frame (kRegions b) s₄.mem s₉.mem := by rw [mem₉]; exact fK
    exact (((((sv₁.frame_in savedOffs_range fm₂ dS).frame_in savedOffs_range fSl dSl).frame_in
      savedOffs_range fK₉ (kd (by omega_using []) (by omega_using []))).frame_in savedOffs_range c₁₀.frame
      (dE (by omega_using []) (by omega_using []) (by omega_using []) (by omega_using []) (by omega_using []))).frame_in savedOffs_range fT dT')
  obtain hb₁₃ : s₁₃.gpr sb = b := by
    rw [g₁₃ _ (by decide) (by decide), g₁₂ _ (by decide) (by decide), u₁₁.other _ (by decide), hb₁₀]
  obtain hscr₁₃ : Scr s₁₃ X 2048 :=
    ⟨by rw [wr₁₃, wr₁₂]; exact (u₁₁.wr ▸ c₁₀.wr ▸ hsF.scr.wr),
      by rw [g₁₃ _ (by decide) (by decide), g₁₂ _ (by decide) (by decide), u₁₁.other _ (by decide), hb₁₀]⟩
  -- The return address back from its slot.
  obtain slot₁₃ : s₁₃.mem.readW (b + BitVec.ofNat 64 496) 64 = s₀.gpr .ra := by
    rw [fT.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (dTb.sub_right (Offset.sub_base b (by omega_using []))).symm) (by decide), slot₁₀]
  refine wp_ld (t := .ra) (n := sb) (off := 8 * raSlot) (a := b + BitVec.ofNat 64 496) (by decide)
    (by rw [hb₁₃]; rfl) (by rw [← hb₄]; exact Align.al_add (k := 8) hscr₄.al (by decide) (by decide))
    ⟨_, List.mem_append_right _ hscr₁₃.wr, hslot⟩ fun s₁₅ u₁₅ => WP.block_nil ?_
  rw [slot₁₃] at u₁₅
  obtain hb₁₅ : s₁₅.gpr sb = b := by rw [u₁₅.other _ (by decide), hb₁₃]
  obtain hscr₁₅ : Scr s₁₅ X 2048 := ⟨by rw [u₁₅.wr]; exact hscr₁₃.wr, by rw [u₁₅.other _ (by decide)]; exact hscr₁₃.base⟩
  rw [restoreRegs_eq]
  refine WP.mono (Spill.restore_wp (B := b) (by rw [← hb₁]; exact hscr₁.al) hb₁₅ savedOffs_ho
    savedOffs_restorable (fun p hp => ⟨_, List.mem_append_right _ hscr₁₅.wr, by
      rw [← hb₁₅]
      exact hscr₁₅.contains (by have := savedOffs_range p hp; omega_using [this]) (by decide)⟩) (by rw [u₁₅.mem]; exact sv))
    fun s₁₄ rs₁₄ => ?_
  refine ⟨fun r hr => ?_, ?_, .inr ⟨s₁₀, c₁₀.res, by rw [rs₁₄.mem, u₁₅.mem, hmem]⟩⟩
  · have hr' : r ∈ savedOffs.map Prod.fst := by rw [savedOffs_regs]; exact hr
    rw [rs₁₄.gpr_of (.inl hr')]
    have : r ∉ [sb] := by revert hr; revert r; decide
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rw [o₁ r this]
  · rw [rs₁₄.other _ not_saved_ra, u₁₅.gpr]

end VG.Proof.Aes.RISCV64

end

end

/-!
# AES chaining on RISC-V

`chain out` (`Impl/Aes/RISCV64/Chain.lean`) chains the `n` blocks at `data`
into the state at `state`, `C := CIPH_K(C ⊕ Mᵢ)` (`Spec.Cmac.chain`), and,
if `out`, writes each chaining value over its block, which is CBC
encryption (`Spec.Cbc.encrypt`) from the state as the IV. Its contract,
`chainRISCV64 out`, has the arguments of `vg_aes_ctr32`.

As `vg_aes_ctr32`'s proof (`Ctr32.lean`): the prologue rounds the scratch
buffer up, saves the callee-saved registers and builds the masks
(`Prologue.lean`), the return address is stored in slot `raSlot` and the
state's address kept in `ra`;
the key loop (`Keys.lean`) bitslices the round keys. Then the state is
loaded into the registers of block 0, whose bytes (`regBlock`, `Ecb.lean`)
are the chaining value `chainSt` before each block: the block is XORed
into them, and `encrypt4` (`Encrypt.lean`) enciphers them, the other three
blocks being whatever the registers hold. If `out`, the new state is stored
over the block, as `Ecb.lean`'s groups store theirs (`EcbInv`). The
epilogue stores the state and restores the registers.
-/

@[expose] public section

namespace VG.Proof.Aes

open VG.RISCV64 in
/-- RISC-V contract for `Impl.Aes.RISCV64.chain out`, with the arguments
`(schedule = a0, rounds = a1, state = a2, data = a3, n = a4, scratch = a5)`:
`state` becomes `Spec.Cmac.chain` of the `n` blocks at `data` from it, and,
if `out`, the blocks become their CBC encryption from it as the IV.

The code may read `schedule` (240 bytes), read and write `state` (16 bytes)
and `scratch` (2048 bytes, whose contents on exit are unspecified), and read
`data` (`16 n` bytes), or, if `out`, read and write it. `data`, `state` and
`scratch` may not overlap each other or the schedule (but `data` the
schedule, if it is only read), and `state` and `data` may not wrap around
the end of the address space. `rounds` is 10, 12 or 14. The pointers,
`rounds` and `n` are public; the key schedule, the state and the data are
secret. -/
def chainRISCV64 (out : Bool) : Contract RISCV64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .a0, 240⟩
    let state : Region := ⟨s.gpr .a2, 16⟩
    let data : Region := ⟨s.gpr .a3, 16 * (s.gpr .a4).toNat⟩
    let scratch : Region := ⟨s.gpr .a5, 2048⟩
    (if out then s.rd = [sched] ∧ s.wr = [state, data, scratch]
      else s.rd = [sched, data] ∧ s.wr = [state, scratch]) ∧
    sched.Disjoint state ∧ sched.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    state.Disjoint scratch ∧ (s.gpr .a2).toNat + 16 ≤ 2 ^ 64 ∧
    (s.gpr .a3).toNat + 16 * (s.gpr .a4).toNat ≤ 2 ^ 64 ∧
    ((s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14)
  post s s' :=
    let ciph := Spec.Cmac.aesWith (s.gpr .a1).toNat
      (Spec.Aes.bytesAt s.mem (s.gpr .a0) (16 * ((s.gpr .a1).toNat + 1)))
    Spec.Aes.bytesAt s'.mem (s.gpr .a2) 16 =
        Spec.Cmac.chain ciph (Spec.Aes.bytesAt s.mem (s.gpr .a2) 16)
          (Spec.Cmac.blocksAt s.mem (s.gpr .a3) 16 (s.gpr .a4).toNat) ∧
      (out = true → Spec.Cbc.blocksAt s'.mem (s.gpr .a3) (s.gpr .a4).toNat =
        Spec.Cbc.encrypt ciph (Spec.Aes.bytesAt s.mem (s.gpr .a2) 16)
          (Spec.Cbc.blocksAt s.mem (s.gpr .a3) (s.gpr .a4).toNat))
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
    s₁.sp = s₂.sp

end VG.Proof.Aes

namespace VG.Proof.Aes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.Align VG.RISCV64.Steps VG.Bitslice
  VG.Impl.Aes.RISCV64 VG.Proof.Aes

/-! ## The chaining values -/

/-- Two states XORed, byte by byte. -/
def vxor (x y : Spec.Aes.State) : Spec.Aes.State := Vector.ofFn fun i => x[i] ^^^ y[i]

/-- The chaining value after `k` of the blocks at `D` in `m₀`, from `iv`. -/
def chainSt (R : Nat) (w : List Byte) (m₀ : Mem) (D : Addr) (iv : Spec.Aes.State) : Nat → Spec.Aes.State
  | 0 => iv
  | k + 1 => Spec.Aes.cipher R w (vxor (chainSt R w m₀ D iv k) (Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * k))))

theorem toList_vxor (x y : Spec.Aes.State) : (vxor x y).toList = Spec.Cmac.xor x.toList y.toList := by
  apply List.ext_getElem (by simp [vxor, Spec.Cmac.xor])
  intro i h₁ h₂
  simp [vxor, Spec.Cmac.xor]

theorem ofFn_toList (v : Spec.Aes.State) : (Vector.ofFn fun i : Fin 16 => v.toList.getD i.1 0) = v := by
  apply Vector.ext
  intro i hi
  simp [List.getD_eq_getElem?_getD]

/-- `chainSt` is `Spec.Cmac.chain` over the first `k` blocks. -/
theorem chainSt_eq (R : Nat) (w : List Byte) (m₀ : Mem) (D : Addr) (iv : Spec.Aes.State) {n : Nat} :
    ∀ k ≤ n, (chainSt R w m₀ D iv k).toList =
      Spec.Cmac.chain (Spec.Cmac.aesWith R w) iv.toList ((Spec.Cmac.blocksAt m₀ D 16 n).take k)
  | 0, _ => by simp [chainSt, Spec.Cmac.chain]
  | k + 1, hk => by
    obtain ih := chainSt_eq R w m₀ D iv (n := n) k (by omega_using [hk])
    obtain ht : (Spec.Cmac.blocksAt m₀ D 16 n).take (k + 1) =
        (Spec.Cmac.blocksAt m₀ D 16 n).take k ++ [Spec.Aes.bytesAt m₀ (D + BitVec.ofNat 64 (16 * k)) 16] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cmac.blocksAt]; omega_using [hk])]
      simp [Spec.Cmac.blocksAt]
    simp only [Spec.Cmac.chain] at ih ⊢
    rw [ht, List.foldl_append, ← ih]
    simp only [List.foldl_cons, List.foldl_nil, chainSt, Spec.Cmac.aesWith]
    rw [AesCbc.bytesAt_toList, ← toList_vxor, ofFn_toList]

theorem cbcXor_comm (x y : List Byte) : Spec.Cbc.xor x y = Spec.Cmac.xor y x := by
  simp only [Spec.Cbc.xor, Spec.Cmac.xor]
  exact List.zipWith_comm_of_comm (fun a b => BitVec.xor_comm a b)

/-- CBC encryption: block `j` becomes the chaining value after it. -/
theorem encrypt_eq (ciph : Spec.Cmac.Cipher) :
    ∀ (xs : List (List Byte)) (c : List Byte), Spec.Cbc.encrypt ciph c xs =
      (List.range xs.length).map fun j => Spec.Cmac.chain ciph c (xs.take (j + 1))
  | [], _ => rfl
  | x :: xs, c => by
    rw [Spec.Cbc.encrypt, encrypt_eq ciph xs, List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    simp only [List.take_succ_cons, Spec.Cmac.chain, List.foldl_cons, Function.comp_def, List.take_zero,
      List.foldl_nil, cbcXor_comm]

/-! ## The registers of block 0 -/

theorem regBlock_xor {Q Q' : Nat → BitVec 64} {m : Mem} {a : Addr}
    (h₀ : Q' 0 = Q 0 ^^^ m.readW a 64) (h₄ : Q' 4 = Q 4 ^^^ m.readW (a + 8) 64) :
    regBlock Q' 0 = vxor (regBlock Q 0) (Spec.Aes.stateAt m a) := by
  apply Vector.ext
  intro i hi
  simp only [regBlock, vxor, Spec.Aes.stateAt, Vector.getElem_ofFn, Fin.getElem_fin, Nat.zero_add]
  refine byte_ext fun j hj => ?_
  simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and, BitVec.getLsbD_xor]
  by_cases h8 : i < 8
  · have e : 4 * (i / 8) = 0 := by omega_using [h8]
    rw [e, h₀, BitVec.getLsbD_xor, show i % 8 = i by omega_using [h8], readW_bit m a h8 hj]
  · have e : 4 * (i / 8) = 4 := by omega_using [hi, h8]
    rw [e, h₄, BitVec.getLsbD_xor, readW_bit m _ (show i % 8 < 8 by omega_using []) hj,
      show (8 : Addr) = BitVec.ofNat 64 8 from rfl, Offset.add_add, show 8 + i % 8 = i by omega_using [hi, h8]]

theorem regBlock_of_inRel {Q : Nat → BitVec 64} {T : Nat → Spec.Aes.State} (h : InRel Q T) {c : Nat}
    (hc : c < 4) : regBlock Q c = T c := by
  apply Vector.ext
  intro t ht
  simp only [regBlock, Vector.getElem_ofFn]
  rw [byte_of_inRel h hc ht, getD_eq _ ht]

theorem regBlock_congr {Q Q' : Nat → BitVec 64} (h₀ : Q' 0 = Q 0) (h₄ : Q' 4 = Q 4) :
    regBlock Q' 0 = regBlock Q 0 := by
  apply Vector.ext
  intro i hi
  simp only [regBlock, Vector.getElem_ofFn, Nat.zero_add]
  by_cases h8 : i < 8
  · rw [show i / 8 = 0 by omega_using [h8], Nat.mul_zero, h₀]
  · rw [show i / 8 = 1 by omega_using [hi, h8], Nat.mul_one, h₄]

/-- The bytes of the registers of block 0, as `ecbInv_step` takes them. -/
theorem regBlock_bytes {Q : Nat → BitVec 64} {v : Spec.Aes.State} (h : regBlock Q 0 = v) :
    ∀ t < 16, (if t < 8 then (Q 0).extractLsb' (8 * t) 8 else (Q 4).extractLsb' (8 * (t - 8)) 8) =
      v.getD t 0 := by
  intro t ht
  rw [← h, getD_eq _ ht]
  simp only [regBlock, Vector.getElem_ofFn, Nat.zero_add]
  by_cases h8 : t < 8
  · rw [ite_eq_left h8, show t / 8 = 0 by omega_using [h8], show t % 8 = t by omega_using [h8], Nat.mul_zero]
  · rw [ite_eq_right h8, show t / 8 = 1 by omega_using [ht, h8], show t % 8 = t - 8 by omega_using [ht, h8], Nat.mul_one]

/-! ## The loop -/

/-- What the loop runs with: `s₂` is the state after the round keys are
bitsliced, `X` the scratch buffer (rounded to `b`), `D` the data (`n`
blocks), which is written only if `out`. -/
structure ChSetup (out : Bool) (s₂ : State) (X b D : Addr) (n R : Nat) (w : List Byte) : Prop where
  scr : Scr s₂ X 2048
  base : s₂.gpr sb = b
  masks : MasksAt s₂.mem b allKs
  rdD : (⟨D, 16 * n⟩ : Region) ∈ s₂.rd ++ s₂.wr
  dat : out = true → (⟨D, 16 * n⟩ : Region) ∈ s₂.wr
  hn : 16 * n < 2 ^ 64
  sep : Region.Disjoint ⟨D, 16 * n⟩ ⟨X, 2048⟩
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  keys : KeysAt s₂.mem (b + BitVec.ofNat 64 (1920 - 64 * R)) R w
  a0 : s₂.gpr .a0 = b + BitVec.ofNat 64 (1920 - 64 * R)

/-- The chaining values, as `EcbInv` takes the blocks: block `j` becomes the
chaining value after it. -/
abbrev chainOutF (R : Nat) (w : List Byte) (m₀ : Mem) (D : Addr) (iv : Spec.Aes.State) (j : Nat) :
    Spec.Aes.State := chainSt R w m₀ D iv (j + 1)

/-- After `k` blocks. -/
structure CAt (out : Bool) (m₀ : Mem) (s₂ : State) (b D : Addr) (n R : Nat) (w : List Byte)
    (iv : Spec.Aes.State) (k : Nat) (s : State) : Prop where
  hk : k ≤ n
  a3 : s.gpr .a3 = D + BitVec.ofNat 64 (16 * k)
  a4 : s.gpr .a4 = BitVec.ofNat 64 (n - k)
  keep : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .a3 → r ≠ .a4 → s.gpr r = s₂.gpr r
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  sp : s.sp = s₂.sp
  frame : Frame (eRegions b D n) s₂.mem s.mem
  st : regBlock (Q s) 0 = chainSt R w m₀ D iv k
  data : EcbInv m₀ s.mem D n (if out then k else 0) (chainOutF R w m₀ D iv)

section Loop

variable {out : Bool} {m₀ : Mem} {s₂ : State} {X b D : Addr} {n R : Nat} {w : List Byte}
  {iv : Spec.Aes.State}

theorem ChSetup.d320 (hs : ChSetup out s₂ X b D n R w) : Region.Disjoint ⟨D, 16 * n⟩ ⟨b, 320⟩ := by
  refine hs.sep.sub_right ?_
  rw [← hs.base, hs.scr.base]
  exact Offset.sub_base X (by have := Align.pad_lt X; omega_using [this])

theorem ChSetup.keys_disj (hs : ChSetup out s₂ X b D n R w) :
    ∀ r ∈ eRegions b D n, Region.Disjoint ⟨b + 1024, 960⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact keys_disjoint b
  · refine (hs.sep.sub_right ?_).symm
    rw [← hs.base]
    exact hs.scr.sub (d := 1024) (n := 960) (by omega_using [])

theorem ChSetup.masks_disj (hs : ChSetup out s₂ X b D n R w) : ∀ r ∈ eRegions b D n,
    Region.Disjoint ⟨b + BitVec.ofNat 64 416, 48⟩ r ∧
      Region.Disjoint ⟨b + BitVec.ofNat 64 512, 96⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨Offset.disjoint_base b (by omega_using []) (by omega_using []), Offset.disjoint_base b (by omega_using []) (by omega_using [])⟩
  · rw [← hs.base]
    exact ⟨(hs.sep.sub_right (hs.scr.sub (by omega_using []))).symm,
      (hs.sep.sub_right (hs.scr.sub (by omega_using []))).symm⟩

theorem q04 : q 0 ≠ .a3 ∧ q 4 ≠ .a3 ∧ q 0 ≠ q 4 ∧ q 0 ≠ .t2 ∧ q 4 ≠ .t2 ∧ q 0 ≠ t0 ∧ q 0 ≠ t1 ∧
    q 4 ≠ t0 ∧ q 4 ≠ t1 := by decide

/-- One block: from after `k` blocks to after `k + 1`. -/
theorem chainBody_ok (hs : ChSetup out s₂ X b D n R w) {k : Nat} (hkn : k < n) {s : State}
    (hi : CAt out m₀ s₂ b D n R w iv k s) :
    WP isa (chainBody out) s fun s' =>
      isa.eval (.nonzero .a4) s' = some (decide (n - (k + 1) ≠ 0)) ∧
        CAt out m₀ s₂ b D n R w iv (k + 1) s' := by
  obtain hR : R ≤ 14 := by rcases hs.rounds with h | h | h <;> omega_using [h]
  have hn := hs.hn
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := q04
  obtain hA : ∀ d, s.gpr .a3 + BitVec.ofNat 64 d = D + BitVec.ofNat 64 (16 * k + d) := fun d => by
    rw [hi.a3, Offset.add_add]
  obtain hD : (⟨D, 16 * n⟩ : Region) ∈ s.rd ++ s.wr := by rw [hi.rd, hi.wr]; exact hs.rdD
  obtain hin : ∀ d, d + 4 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr .a3 + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [hA]; exact in_off hD (by omega_using [hkn, hd]) hn
  unfold chainBody chainXor
  refine WP.seq ?_
  repeat rw [WP.block_append_iff (M := isa)]
  -- The block XORed into the state.
  refine WP.mono (Bytes.loadLE64_ok (d := .t2) (tmp := t0) (hi := t1) (n := .a3) (off := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simpa using hin 0 (by omega_using [])) (by simpa using hin 4 (by omega_using [])))
    fun s₁ ⟨e₁, g₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
  refine wp_xor fun s₂' u₂ => WP.block_nil ?_
  obtain a₁ : s₂'.gpr .a3 = s.gpr .a3 := by rw [u₂.other _ (Ne.symm n1), g₁ _ (by decide) (by decide) (by decide)]
  refine WP.mono (Bytes.loadLE64_ok (d := .t2) (tmp := t0) (hi := t1) (n := .a3) (off := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [a₁, u₂.rd, u₂.wr, rd₁, wr₁]; exact hin 8 (by omega_using []))
    (by rw [a₁, u₂.rd, u₂.wr, rd₁, wr₁]; exact hin 12 (by omega_using [])))
    fun s₃ ⟨e₃, g₃, m₃, rd₃, wr₃, sp₃⟩ => ?_
  refine wp_xor fun s₄ u₄ => WP.block_nil ?_
  obtain o₄ : ∀ r, r ≠ q 0 → r ≠ q 4 → r ≠ .t2 → r ≠ t0 → r ≠ t1 → s₄.gpr r = s.gpr r :=
    fun r h0 h4 h2 ht0 ht1 => by
      rw [u₄.other _ h4, g₃ _ h2 ht0 ht1, u₂.other _ h0, g₁ _ h2 ht0 ht1]
  obtain mem₄ : s₄.mem = s.mem := by rw [u₄.mem, m₃, u₂.mem, m₁]
  obtain orig : Spec.Aes.stateAt s.mem (D + BitVec.ofNat 64 (16 * k)) =
      Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * k)) :=
    ecbInv_orig hi.data (by split <;> omega_using []) hkn
  obtain st₄ : regBlock (Q s₄) 0 =
      vxor (chainSt R w m₀ D iv k) (Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * k))) := by
    rw [← hi.st, ← orig]
    refine regBlock_xor (m := s.mem) ?_ ?_
    · show s₄.gpr (q 0) = s.gpr (q 0) ^^^ _
      rw [u₄.other _ n3, g₃ _ n4 n6 n7, u₂.gpr, e₁, g₁ _ n4 n6 n7]
      simpa using congrArg (s.mem.readW · 64) (hA 0)
    · show s₄.gpr (q 4) = s.gpr (q 4) ^^^ _
      rw [u₄.gpr, g₃ _ n5 n8 n9, e₃, u₂.other _ (Ne.symm n3), g₁ _ n5 n8 n9, u₂.mem, m₁, a₁, hA,
        add_off8]
  -- The state enciphered.
  obtain keep₄ : ∀ r, r ∉ sboxWrites → r ≠ kp → s₄.gpr r = s.gpr r := fun r h1 _ =>
    o₄ r (fun e => h1 (e ▸ by decide)) (fun e => h1 (e ▸ by decide)) (fun e => h1 (e ▸ by decide))
      (fun e => h1 (e ▸ by decide)) (fun e => h1 (e ▸ by decide))
  obtain hb₄ : s₄.gpr sb = b := by
    rw [keep₄ sb (by decide) (by decide), hi.keep sb (by decide) (by decide) (by decide) (by decide), hs.base]
  obtain a0₄ : s₄.gpr .a0 = b + BitVec.ofNat 64 (1920 - 64 * R) := by
    rw [keep₄ .a0 (by decide) (by decide), hi.keep .a0 (by decide) (by decide) (by decide) (by decide),
      hs.a0]
  obtain hp : EncPre s₄ X R w :=
    ⟨hs.scr.congr (by rw [u₄.wr, wr₃, u₂.wr, wr₁, hi.wr]) (by rw [hb₄, hs.base]),
      by rw [hb₄, mem₄]; exact masks_frame hi.frame hs.masks_disj hs.masks, hs.rounds,
      by rw [a0₄, hb₄],
      by rw [a0₄, mem₄]; exact keysAt_frame hR hi.frame hs.keys_disj hs.keys⟩
  refine WP.seq (WP.mono (encrypt4_ok hp (inRel_regBlock (Q s₄))) fun s₅ ⟨hc₅, hin₅⟩ => ?_)
  obtain st₅ : regBlock (Q s₅) 0 = chainSt R w m₀ D iv (k + 1) := by
    rw [regBlock_of_inRel hin₅ (by decide), st₄]; rfl
  obtain keep₅ : ∀ r, r ∉ sboxWrites → r ≠ kp → s₅.gpr r = s.gpr r := fun r h1 h2 =>
    (hc₅.keep r h1 h2).trans (keep₄ r h1 h2)
  obtain fr₅ : Frame [⟨b, 320⟩] s.mem s₅.mem := by
    have := hc₅.frame; rw [hb₄, mem₄] at this; exact this
  obtain rd₅ : s₅.rd = s₂.rd := by rw [hc₅.rd, u₄.rd, rd₃, u₂.rd, rd₁, hi.rd]
  obtain wr₅ : s₅.wr = s₂.wr := by rw [hc₅.wr, u₄.wr, wr₃, u₂.wr, wr₁, hi.wr]
  obtain sp₅ : s₅.sp = s₂.sp := by rw [hc₅.sp, u₄.sp, sp₃, u₂.sp, sp₁, hi.sp]
  obtain a3₅ : s₅.gpr .a3 = D + BitVec.ofNat 64 (16 * k) :=
    (keep₅ .a3 (by decide) (by decide)).trans hi.a3
  obtain a4₅ : s₅.gpr .a4 = BitVec.ofNat 64 (n - k) := (keep₅ .a4 (by decide) (by decide)).trans hi.a4
  obtain frame₅ : Frame (eRegions b D n) s₂.mem s₅.mem :=
    hi.frame.trans (fr₅.mono fun r hr => by simp at hr; simp [hr])
  -- On to the next block, after storing the state over this one if `out`.
  obtain next : ∀ {s₆ : State}, s₆.gpr .a3 = D + BitVec.ofNat 64 (16 * k) →
      s₆.gpr .a4 = BitVec.ofNat 64 (n - k) →
      (∀ r, r ∉ sboxWrites → r ≠ kp → s₆.gpr r = s.gpr r) →
      s₆.rd = s₂.rd → s₆.wr = s₂.wr → s₆.sp = s₂.sp → Frame (eRegions b D n) s₂.mem s₆.mem →
      regBlock (Q s₆) 0 = chainSt R w m₀ D iv (k + 1) →
      EcbInv m₀ s₆.mem D n (if out then k + 1 else 0) (chainOutF R w m₀ D iv) →
      WP isa (.block chainNext) s₆ fun s' =>
        isa.eval (.nonzero .a4) s' = some (decide (n - (k + 1) ≠ 0)) ∧
          CAt out m₀ s₂ b D n R w iv (k + 1) s' := by
    intro s₆ a3₆ a4₆ keep₆ rd₆ wr₆ sp₆ fr₆ st₆ data₆
    unfold chainNext
    refine wp_addi (imm := 16) (by decide) fun s₇ u₇ => wp_subi (imm := 1) (by decide)
      fun s₈ u₈ => WP.block_nil ?_
    obtain a4₈ : s₈.gpr .a4 = BitVec.ofNat 64 (n - (k + 1)) := by
      rw [u₈.gpr, u₇.other _ (by decide), a4₆, ofNat_sub_ofNat' (by omega_using [hkn]),
        show n - k - 1 = n - (k + 1) by omega_using []]
    refine ⟨Steps.eval_nonzero_ofNat s₈ .a4 (by omega_using [hn]) a4₈, ⟨by omega_using [hkn], ?_, a4₈, ?_,
      by rw [u₈.rd, u₇.rd, rd₆], by rw [u₈.wr, u₇.wr, wr₆], by rw [u₈.sp, u₇.sp, sp₆],
      by rw [u₈.mem, u₇.mem]; exact fr₆, ?_, by rw [u₈.mem, u₇.mem]; exact data₆⟩⟩
    · rw [u₈.other _ (by decide), u₇.gpr, a3₆, Offset.add_add, show 16 * k + 16 = 16 * (k + 1) by omega_using []]
    · intro r h1 h2 h3 h4
      rw [u₈.other _ h4, u₇.other _ h3, keep₆ r h1 h2,
        hi.keep r h1 h2 h3 h4]
    · rw [← st₆]
      refine regBlock_congr ?_ ?_
      · show s₈.gpr (q 0) = s₆.gpr (q 0)
        rw [u₈.other _ (by decide), u₇.other _ (by decide)]
      · show s₈.gpr (q 4) = s₆.gpr (q 4)
        rw [u₈.other _ (by decide), u₇.other _ (by decide)]
  cases out with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
    refine next a3₅ a4₅ keep₅ rd₅ wr₅ sp₅ frame₅ st₅ ?_
    simp only [Bool.false_eq_true, ↓reduceIte] at hi ⊢
    exact ecbInv_frame fr₅ (by simpa using hs.d320) hn hi.data
  | true =>
    simp only [↓reduceIte]
    unfold chainOut
    repeat rw [WP.block_append_iff (M := isa)]
    obtain hDw : (⟨D, 16 * n⟩ : Region) ∈ s₅.wr := by rw [wr₅]; exact hs.dat rfl
    obtain hinw : ∀ {t : State} (d : Nat), t.gpr .a3 = D + BitVec.ofNat 64 (16 * k) → t.wr = s₅.wr →
        d + 4 ≤ 16 → InRegions t.wr (t.gpr .a3 + BitVec.ofNat 64 d) 4 := fun d ha hw hd => by
      rw [ha, hw, Offset.add_add]; exact in_off hDw (by omega_using [hkn, hd]) hn
    refine WP.mono (Bytes.storeLE64_ok (v := q 0) (tmp := t0) (hi := t1) (n := .a3) (off := 0)
      (Ne.symm n6) (by decide) (by decide) (by decide) (by decide)
      (by simpa using hinw 0 a3₅ rfl (by omega_using [])) (hinw 4 a3₅ rfl (by omega_using [])))
      fun s₆ ⟨m₆, g₆, rd₆, wr₆, sp₆⟩ => ?_
    obtain a3₆ : s₆.gpr .a3 = D + BitVec.ofNat 64 (16 * k) := (g₆ _ (by decide) (by decide)).trans a3₅
    refine WP.mono (Bytes.storeLE64_ok (v := q 4) (tmp := t0) (hi := t1) (n := .a3) (off := 8)
      (Ne.symm n8) (by decide) (by decide) (by decide) (by decide)
      (hinw 8 a3₆ wr₆ (by omega_using [])) (hinw 12 a3₆ wr₆ (by omega_using [])))
      fun s₇ ⟨m₇, g₇, rd₇, wr₇, sp₇⟩ => ?_
    obtain v₄ : s₆.gpr (q 4) = s₅.gpr (q 4) := g₆ _ n8 n9
    obtain hm : s₇.mem = (s₅.mem.writeW (D + BitVec.ofNat 64 (16 * k)) (s₅.gpr (q 0))).writeW
        (D + BitVec.ofNat 64 (16 * k) + 8) (s₅.gpr (q 4)) := by
      generalize hD' : D + BitVec.ofNat 64 (16 * k) = D'
      obtain e12 : D' + BitVec.ofNat 64 (8 + 4) = D' + 8 + BitVec.ofNat 64 4 :=
        (Offset.add_add _ _ _).symm
      rw [m₇, a3₆, v₄, m₆, a3₅, hD', show D' + BitVec.ofNat 64 0 = D' by simp,
        show D' + BitVec.ofNat 64 (0 + 4) = D' + BitVec.ofNat 64 4 from rfl, Words64.writeW64_split,
        show D' + BitVec.ofNat 64 8 = D' + 8 from rfl, e12, Words64.writeW64_split]
    obtain hd₀ : EcbInv m₀ s₅.mem D n k (chainOutF R w m₀ D iv) := by
      have h := hi.data
      simp only [↓reduceIte] at h
      exact ecbInv_frame fr₅ (by simpa using hs.d320) hn h
    obtain hst := ecbInv_step (F := chainOutF R w m₀ D iv) (v₁ := s₅.gpr (q 0)) (v₂ := s₅.gpr (q 4))
      (by omega_using [hn]) hkn hd₀ (regBlock_bytes st₅)
    rw [← hm] at hst
    obtain o₇ : ∀ r, r ≠ t0 → r ≠ t1 → s₇.gpr r = s₅.gpr r := fun r h0 h1 => by
      rw [g₇ r h0 h1, g₆ r h0 h1]
    refine next (by rw [o₇ _ (by decide) (by decide)]; exact a3₅)
      (by rw [o₇ _ (by decide) (by decide)]; exact a4₅)
      (fun r h1 h2 => by rw [o₇ r (fun e => h1 (e ▸ by decide)) (fun e => h1 (e ▸ by decide))]; exact keep₅ r h1 h2)
      (by rw [rd₇, rd₆]; exact rd₅) (by rw [wr₇, wr₆]; exact wr₅) (by rw [sp₇, sp₆]; exact sp₅)
      (frame₅.trans (hst.2.mono fun r hr => by simp at hr; simp [hr]))
      (by rw [← st₅]; exact regBlock_congr (o₇ _ n6 n7) (o₇ _ n8 n9))
      (by simp only [↓reduceIte]; exact hst.1)

/-- The loop over the blocks. -/
theorem chainLoop_ok (hs : ChSetup out s₂ X b D n R w) (hn0 : 0 < n) {s : State}
    (hi : CAt out m₀ s₂ b D n R w iv 0 s) :
    WP isa (.loop (chainBody out) (.nonzero .a4)) s (CAt out m₀ s₂ b D n R w iv n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ CAt out m₀ s₂ b D n R w iv k s)
    (fun m s ⟨k, hm, hk, h⟩ => WP.mono (chainBody_ok hs hk h) fun s' ⟨ev, h'⟩ => ?_) n s
    ⟨0, by omega_using [], hn0, hi⟩
  by_cases hl : n - (k + 1) = 0
  · have e : k + 1 = n := by omega_using [hk, hl]
    exact .inl ⟨by rw [ev]; simp [hl], e ▸ h'⟩
  · exact .inr ⟨by rw [ev]; simp [hl], n - (k + 1), by omega_using [hm, hk], k + 1, rfl, by omega_using [hl], h'⟩

end Loop


/-! ## The whole function -/

/-- The memory after the state is stored back changed only there. -/
theorem frame_writeW2 (m : Mem) (St : Addr) (v₁ v₂ : BitVec 64) :
    Frame [⟨St, 16⟩] m ((m.writeW St v₁).writeW (St + 8) v₂) := by
  refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
  · simpa using Offset.contains_base St (d := 0) (n := 8) (k := 16) (by omega_using []) (by omega_using [])
  · exact Offset.contains_base St (d := 8) (n := 8) (k := 16) (by omega_using []) (by omega_using [])

theorem correct_chain {out : Bool} {s₀ : State} (hp : (Proof.Aes.chainRISCV64 out).pre s₀) :
    WP isa (Impl.Aes.RISCV64.chain out) s₀ fun s' =>
      (∀ r ∈ RISCV64.preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
        (Proof.Aes.chainRISCV64 out).post s₀ s' := by
  let n := (s₀.gpr .a4).toNat
  let R := (s₀.gpr .a1).toNat
  let St := s₀.gpr .a2
  let D := s₀.gpr .a3
  let w := Spec.Aes.bytesAt s₀.mem (s₀.gpr .a0) (16 * (R + 1))
  let iv := Spec.Aes.stateAt s₀.mem St
  have hp' : framePre out (16 * ·) s₀ := hp
  have dDSt : Region.Disjoint ⟨D, 16 * n⟩ ⟨St, 16⟩ := hp.2.2.2.1
  let Res : State → Prop := fun s => regBlock (Q s) 0 = chainSt R w s₀.mem D iv n ∧
    EcbInv s₀.mem s.mem D n (if out then n else 0) (chainOutF R w s₀.mem D iv)
  unfold Impl.Aes.RISCV64.chain
  refine WP.mono (frame_wp (Res := Res) hp' fun s₉ X b hsF => ?_) fun s' ⟨hg, hra, hm⟩ => ⟨hg, hra, ?_⟩
  · have hs : ChSetup out s₉ X b D n R w :=
      { scr := hsF.scr, base := hsF.base, masks := hsF.masks, rdD := hsF.rdD, dat := hsF.dat,
        hn := hsF.hn, sep := hsF.sep, rounds := hsF.rounds, keys := hsF.keys, a0 := hsF.a0 }
    obtain dD : ∀ r ∈ [(⟨X, 2048⟩ : Region)], Region.Disjoint ⟨D, 16 * n⟩ r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hsF.sep
    obtain ci₀ : CAt out s₀.mem s₉ b D n R w iv 0 s₉ :=
      { hk := Nat.zero_le _
        a3 := by rw [hsF.a3]; simp [D]
        a4 := by rw [hsF.a4]; simp [n]
        keep := fun _ _ _ _ _ => rfl
        rd := rfl
        wr := rfl
        sp := rfl
        frame := Frame.refl _ _
        st := hsF.st
        data := by
          have := ecbInv_frame (m₀ := s₀.mem) (m := s₀.mem) (k := 0) (F := chainOutF R w s₀.mem D iv)
            hsF.f₀ dD hsF.hn fun i hi => by simp
          rw [ite_self]; exact this }
    refine WP.block_nil (WP.mono (chainLoop_ok hs hsF.hn0 ci₀) fun s c => WP.block_nil ?_)
    exact { base := (c.keep sb (by decide) (by decide) (by decide) (by decide)).trans hsF.base
            ra := c.keep .ra (by decide) (by decide) (by decide) (by decide)
            rd := c.rd
            wr := c.wr
            sp := c.sp
            frame := c.frame.mono fun r hr => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
              rcases hr with rfl | rfl
              exacts [.inl rfl, .inr (.inr (.inr (.inr rfl)))]
            res := ⟨c.st, c.data⟩ }
  · rcases hm with ⟨hn0, hmem⟩ | ⟨s, ⟨hst, hdat⟩, hmem⟩
    · refine ⟨?_, fun _ => ?_⟩
      · show Spec.Aes.bytesAt s'.mem St 16 = Spec.Cmac.chain _ _ (Spec.Cmac.blocksAt s₀.mem D 16 n)
        rw [hmem, show n = 0 from hn0]; rfl
      · show Spec.Cbc.blocksAt s'.mem D n = Spec.Cbc.encrypt _ _ (Spec.Cbc.blocksAt s₀.mem D n)
        rw [hmem, show n = 0 from hn0]; rfl
    refine ⟨?_, fun ho => ?_⟩
    · show Spec.Aes.bytesAt s'.mem St 16 = Spec.Cmac.chain _ (Spec.Aes.bytesAt s₀.mem St 16)
        (Spec.Cmac.blocksAt s₀.mem D 16 n)
      rw [hmem, bytesAt_writeW2 _ _ _ _ (regBlock_bytes hst), chainSt_eq _ _ _ _ _ n (Nat.le_refl _),
        List.take_of_length_le (by simp [Spec.Cmac.blocksAt]), AesCbc.bytesAt_toList]
    · subst ho
      obtain n16 : 16 * n < 2 ^ 64 := by
        refine Nat.lt_of_not_le fun hc => dDSt St ?_ (by simp [Region.Contains])
        simp only [Region.Contains]
        have := (St - D).isLt
        omega_using [hc]
      obtain hd₁₄ : EcbInv s₀.mem s'.mem D n n (chainOutF R w s₀.mem D iv) := by
        simp only [↓reduceIte] at hdat
        rw [hmem]
        refine ecbInv_frame (frame_writeW2 _ _ _ _) (fun r hr => ?_) n16 hdat
        simp only [List.mem_singleton] at hr; subst hr; exact dDSt
      show Spec.Cbc.blocksAt s'.mem D n = Spec.Cbc.encrypt _ (Spec.Aes.bytesAt s₀.mem St 16)
        (Spec.Cbc.blocksAt s₀.mem D n)
      obtain hb : ∀ m : Mem, Spec.Cbc.blocksAt m D n = (Spec.Aes.statesAt m D n).map Vector.toList := by
        intro m
        simp only [Spec.Cbc.blocksAt, Spec.Aes.statesAt, List.map_map, Function.comp_def,
          AesCbc.bytesAt_toList]
      rw [hb, statesAt_of_ecbInv hd₁₄, encrypt_eq, Spec.Cbc.blocksAt, List.length_map, List.length_range,
        List.map_map]
      refine List.map_congr_left fun j hj => ?_
      obtain hj := List.mem_range.mp hj
      simp only [Function.comp_apply, chainOutF]
      rw [chainSt_eq _ _ _ _ _ (n := n) (j + 1) (by omega_using [hj]), AesCbc.bytesAt_toList]
      rfl

end VG.Proof.Aes.RISCV64

end

end

/-!
# AES chaining on RISC-V: correctness and constant time

Correctness (`Chain.lean`) and constant time (by taint tracking,
`taint_decide`: only the pointers, `rounds`, `n` and what is computed from
them reach addresses and branches), against `Proof.Aes.chainRISCV64`, as for
`vg_aes_ctr32` (`Ctr32Verified.lean`). `chain` has no `Api`: the functions
that call it are proven with these, through their calls of it.
-/

@[expose] public section

namespace VG.Proof.Aes.RISCV64

open VG VG.RISCV64 VG.Proof.Aes

theorem chain_correct (out : Bool) (s : State) (hs : (Proof.Aes.chainRISCV64 out).pre s) :
    ∃ t s', Exec isa (Impl.Aes.RISCV64.chain out) s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.chainRISCV64 out).post s s' := by
  obtain ⟨t, s', he, h₁, hra, h₂⟩ := correct_chain hs
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, hra⟩, h₂⟩

theorem chain_agree (out : Bool) :
    ∀ s₁ s₂, (Proof.Aes.chainRISCV64 out).pre s₁ → (Proof.Aes.chainRISCV64 out).pre s₂ →
      (Proof.Aes.chainRISCV64 out).pub s₁ s₂ →
      taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5]) s₁ s₂ := by
  rintro s₁ s₂ - - ⟨h0, h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4, h5]

theorem chain_ct (out : Bool) : ConstantTime isa (Proof.Aes.chainRISCV64 out).pre
    (Proof.Aes.chainRISCV64 out).pub (Impl.Aes.RISCV64.chain out) := by
  cases out
  · exact VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5])
      (chain_agree _) (by taint_decide_sum [Impl.Aes.RISCV64.encrypt4Sum])
  · exact VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5])
      (chain_agree _) (by taint_decide_sum [Impl.Aes.RISCV64.encrypt4Sum])

end VG.Proof.Aes.RISCV64

end

end

/-!
# AES on RISC-V: a call of a chain

`vg_aes_cbc_encrypt`, `vg_cmac_aes_update`, AES-CFB128 encryption, AES-OFB
and AES-CFB8 save the return address and `s1` at `sv` (`Spill.save_ok`),
keep the scratch buffer in `s1`, call a chain (`Impl.Aes.RISCV64.chain`,
`cfbChain`, `ofbChain`, `cfb8Chain`, as `chainWrap`) on their own arguments
and the first 2048 bytes of the scratch buffer, and restore the registers.

A chain `c` with the contract `k` (`ChainK out len k c`: its precondition
`framePre out len`'s, its data `len n` bytes, and its postcondition reading
only the arguments and the memory they point to) is proven once for all of
them. `wrap_wp`: from the callers' precondition (`WPre out len`, the
chain's with the scratch buffer of 2176 bytes), this meets `k` (through
`WP.call`), and keeps the callee-saved registers and the return address.
`wrap_ct`: it is constant time, the code around the call by taint tracking
(from the arguments, and then from `s1`) and the call by the chain's
`ChainK.ct`. `chain_k`: `chain out` is such a chain.
-/

@[expose] public section

namespace VG.Proof.AesCbc.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Align VG.Impl.AesCbc.RISCV64
open VG.Spec.Aes (bytesAt)

/-- The chain `c` called as `name`, with the return address and `s1` saved. -/
abbrev chainWrap (name : String) (c : Prog isa) : Prog isa :=
  .seq (.block encSave) (.seq (.call name c) (.block encRestore))

/-- The data: `len n` bytes, for the `n` in `a4`. -/
abbrev dataL (len : Nat → Nat) (s₀ : State) : Region := ⟨Dp s₀, len (N s₀)⟩

/-- The regions the chain reads: the schedule, and the data unless it writes them. -/
abbrev rdOf (out : Bool) (len : Nat → Nat) (s₀ : State) : List Region :=
  if out then [schR s₀] else [schR s₀, dataL len s₀]

/-- The regions the chain writes: the chaining value, the data if `out`, and `scr`. -/
abbrev wrOf (out : Bool) (len : Nat → Nat) (s₀ : State) (scr : Region) : List Region :=
  if out then [ivR s₀, dataL len s₀, scr] else [ivR s₀, scr]

/-- The callers' precondition: the chain's (`Proof.Aes.RISCV64.framePre out len`), with the
scratch buffer of 2176 bytes. -/
structure WPre (out : Bool) (len : Nat → Nat) (s₀ : State) : Prop where
  rd : s₀.rd = rdOf out len s₀
  wr : s₀.wr = wrOf out len s₀ (scrR s₀)
  sch_iv : (schR s₀).Disjoint (ivR s₀)
  sch_scr : (schR s₀).Disjoint (scrR s₀)
  data_iv : (dataL len s₀).Disjoint (ivR s₀)
  data_scr : (dataL len s₀).Disjoint (scrR s₀)
  iv_scr : (ivR s₀).Disjoint (scrR s₀)
  iv_wrap : (Iv s₀).toNat + 16 ≤ 2 ^ 64
  data_wrap : (Dp s₀).toNat + len (N s₀) ≤ 2 ^ 64
  scr_wrap : (S s₀).toNat + 2176 ≤ 2 ^ 64
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14

/-- The public part of the chains' arguments: all of them, and the stack pointer. -/
abbrev ChPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.sp = s₂.sp

/-- The registers saved, and their offsets from `sv`. -/
abbrev chSaved : List (Reg × Nat) := [(.ra, 16), (.s1, 24)]

/-- The memory after saving them. -/
abbrev chMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (sv s₀) (saveG s₀) chSaved

/-- Their slots. -/
abbrev chSlots (s₀ : State) : Region := ⟨sv s₀ + BitVec.ofNat 64 16, 16⟩

/-- A chain `c` with the contract `k`, whose precondition is
`framePre out len`'s and whose postcondition reads only the arguments, the
memory they point to (the schedule, the chaining value and the data) and
the memory on exit: what a call of it with `WPre` needs. -/
structure ChainK (out : Bool) (len : Nat → Nat) (k : Contract isa) (c : Prog isa) : Prop where
  pre : ∀ s, Proof.Aes.RISCV64.framePre out len s → k.pre s
  pub_of : ∀ s₁ s₂, ChPub s₁ s₂ → k.pub s₁ s₂
  correct : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s'
  ct : ConstantTime isa k.pre k.pub c
  noFrames : c.noFrames = true
  post : ∀ {s₀ s t t' : State}, WPre out len s₀ →
    (∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4], s.gpr r = s₀.gpr r) → s.mem = chMem s₀ → t'.mem = t.mem →
    k.post s t → k.post s₀ t'

theorem preserved_ne {r : Reg} (hr : r ∈ preserved) : r ≠ .t0 := by
  revert hr; cases r <;> decide

theorem chSaved_bound : ∀ p ∈ chSaved, 16 ≤ p.2 ∧ p.2 + 8 ≤ 32 := by decide

theorem chMem_frame (s₀ : State) : Frame [chSlots s₀] s₀.mem (chMem s₀) :=
  Spill.saveMem_frame (lo := 16) (n := 16) chSaved_bound (by decide) _ _ _

theorem chSlots_scr (s₀ : State) : Region.Sub (chSlots s₀) (scrR s₀) := by
  have := q_lt s₀
  rw [chSlots, sv_add]; exact UPre.scr_sub (by omega_using [this])

theorem slot_scr (s₀ : State) {p : Reg × Nat} (hp : p ∈ chSaved) :
    Region.Sub ⟨sv s₀ + BitVec.ofNat 64 p.2, 8⟩ (scrR s₀) := by
  have := q_lt s₀
  have := chSaved_bound p hp
  rw [sv_add]; exact UPre.scr_sub (by omega_arith)

theorem slot_ws {s₀ : State} {p : Reg × Nat} (hp : p ∈ chSaved) :
    Region.Disjoint ⟨sv s₀ + BitVec.ofNat 64 p.2, 8⟩ (wsR s₀) := by
  have := q_lt s₀
  have := chSaved_bound p hp
  rw [sv_add]; exact Offset.disjoint_base _ (by omega_using []) (by omega_arith)

/-- The blocks at `p`, unchanged by writes elsewhere. -/
theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 16 * n⟩ : Region).Disjoint r) :
    Spec.Cmac.blocksAt m' p 16 n = Spec.Cmac.blocksAt m p 16 n := by
  simp only [Spec.Cmac.blocksAt]
  refine List.map_congr_left fun i hi => Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega_using [])
  rw [List.mem_range] at hi
  exact (hd r hr).sub_left (Offset.sub_base _ (by omega_using [hi]))

theorem cov_self {r : Region} {rs : List Region} (h : r ∈ rs) :
    ∃ r' ∈ rs, ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len :=
  ⟨r, h, 0, by simp, by simp⟩

theorem cov_ws {s₀ : State} {rs : List Region} (h : scrR s₀ ∈ rs) :
    ∃ r' ∈ rs, ∃ off, (wsR s₀).base = r'.base + BitVec.ofNat 64 off ∧ off + (wsR s₀).len ≤ r'.len :=
  ⟨_, h, 0, by simp, by simp⟩

section
variable {out : Bool} {len : Nat → Nat} {s₀ : State} (h : WPre out len s₀)
include h

theorem WPre.scr_mem : scrR s₀ ∈ s₀.wr := by rw [h.wr]; cases out <;> simp [wrOf]

/-- What the chain writes, outside the slots. -/
theorem WPre.slots_disj {p : Reg × Nat} (hp : p ∈ chSaved) :
    ∀ r ∈ wrOf out len s₀ (wsR s₀), Region.Disjoint ⟨sv s₀ + BitVec.ofNat 64 p.2, 8⟩ r := by
  have hi := h.iv_scr.symm.sub_left (slot_scr s₀ hp)
  have hd := h.data_scr.symm.sub_left (slot_scr s₀ hp)
  have hs := slot_ws (s₀ := s₀) hp
  intro r hr
  cases out <;> simp only [wrOf, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil,
    or_false] at hr <;> rcases hr with rfl | rfl | rfl <;> with_reducible assumption

/-- The chain's regions, within the caller's. -/
theorem WPre.covers : Covers (rdOf out len s₀ ++ wrOf out len s₀ (wsR s₀)) (s₀.rd ++ s₀.wr) := by
  rw [h.rd, h.wr]
  refine Covers.of_sub fun r hr => ?_
  cases out <;>
    simp only [rdOf, wrOf, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr <;>
    rcases hr with rfl | rfl | rfl | rfl <;> first
      | (refine cov_self ?_; simp [rdOf, wrOf]; done)
      | (refine cov_ws ?_; simp [rdOf, wrOf]; done)

theorem WPre.covers_wr : Covers (wrOf out len s₀ (wsR s₀)) s₀.wr := by
  rw [h.wr]
  refine Covers.of_sub fun r hr => ?_
  cases out <;>
    simp only [wrOf, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hr <;>
    rcases hr with rfl | rfl | rfl <;> first
      | (refine cov_self ?_; simp [wrOf]; done)
      | (refine cov_ws ?_; simp [wrOf]; done)

/-- The schedule, unchanged by the saves. -/
theorem WPre.sch_eq : bytesAt (chMem s₀) (s₀.gpr .a0) (16 * ((s₀.gpr .a1).toNat + 1)) =
    bytesAt s₀.mem (s₀.gpr .a0) (16 * ((s₀.gpr .a1).toNat + 1)) := by
  have hRb : 16 * ((s₀.gpr .a1).toNat + 1) ≤ 240 := by
    have hr : (s₀.gpr .a1).toNat = 10 ∨ (s₀.gpr .a1).toNat = 12 ∨ (s₀.gpr .a1).toNat = 14 := h.rounds
    omega_using [hr]
  exact Proof.Cmac.bytesAt_frame (chMem_frame s₀) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.sch_scr.sub_right (chSlots_scr s₀)).sub_left (Region.sub_prefix hRb)) (by omega_using [hRb])

/-- The chaining value, unchanged by the saves. -/
theorem WPre.iv_eq : bytesAt (chMem s₀) (s₀.gpr .a2) 16 = bytesAt s₀.mem (s₀.gpr .a2) 16 :=
  Proof.Cmac.bytesAt_frame (chMem_frame s₀) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.iv_scr.sub_right (chSlots_scr s₀)) (by omega_using [])

/-- The data, unchanged by the saves. -/
theorem WPre.data_eq : bytesAt (chMem s₀) (s₀.gpr .a3) (len (s₀.gpr .a4).toNat) =
    bytesAt s₀.mem (s₀.gpr .a3) (len (s₀.gpr .a4).toNat) :=
  Proof.Cmac.bytesAt_frame (chMem_frame s₀) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.data_scr.sub_right (chSlots_scr s₀)) (by
      have : (s₀.gpr .a3).toNat + len (s₀.gpr .a4).toNat ≤ 2 ^ 64 := h.data_wrap
      omega_using [this])

end

/-- The data blocks, unchanged by the saves. -/
theorem WPre.blocks_eq {out : Bool} {s₀ : State} (h : WPre out (16 * ·) s₀) :
    Spec.Cmac.blocksAt (chMem s₀) (s₀.gpr .a3) 16 (s₀.gpr .a4).toNat =
      Spec.Cmac.blocksAt s₀.mem (s₀.gpr .a3) 16 (s₀.gpr .a4).toNat :=
  blocksAt_frame (chMem_frame s₀) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.data_scr.sub_right (chSlots_scr s₀)

/-- What saving the registers leaves. -/
structure WMid (s₀ s : State) : Prop where
  a0 : s.gpr .a0 = s₀.gpr .a0
  a1 : s.gpr .a1 = s₀.gpr .a1
  a2 : s.gpr .a2 = s₀.gpr .a2
  a3 : s.gpr .a3 = s₀.gpr .a3
  a4 : s.gpr .a4 = s₀.gpr .a4
  a5 : s.gpr .a5 = s₀.gpr .a5
  s1 : s.gpr .s1 = S s₀
  keep : ∀ r ∈ preserved, r ≠ .s1 → s.gpr r = s₀.gpr r
  mem : s.mem = chMem s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem save_wp {out : Bool} {len : Nat → Nat} {s₀ : State} (h : WPre out len s₀) :
    WP isa (.block encSave) s₀ (WMid s₀) := by
  rw [show encSave = savePtr .a5 ++ (Spill.saveCode .t0 chSaved ++ [mov .s1 .a5]) from rfl,
    WP.block_append_iff]
  refine WP.mono (savePtr_ok .a5) fun s₁ e => ?_
  subst e
  have t₀ : (s₀.write .t0 (sv s₀)).gpr .t0 = sv s₀ := RegUpd.gpr_write_self _ _ _
  have g₀ (r : Reg) (hr : r ≠ .t0) : (s₀.write .t0 (sv s₀)).gpr r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine Spill.save_ok (b := .t0) (l := chSaved) (by rw [t₀]; exact align_al _) (by decide)
    (fun p hp => ?_) ?_
  · rw [t₀]
    show InRegions s₀.wr _ 8
    have := q_lt s₀
    have := chSaved_bound p hp
    have := h.scr_wrap
    exact in_rw h.scr_mem (by rw [sv_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith))
  generalize ht : ({ (s₀.write .t0 (sv s₀)) with
    mem := Spill.saveMem (s₀.write .t0 (sv s₀)).mem ((s₀.write .t0 (sv s₀)).gpr .t0)
      (s₀.write .t0 (sv s₀)).gpr chSaved } : State) = t
  have memt : t.mem = chMem s₀ := by
    rw [← ht]; show Spill.saveMem _ _ _ _ = _; rw [t₀, RegUpd.mem_write]
  have gt (r : Reg) (hr : r ≠ .t0) : t.gpr r = s₀.gpr r := by rw [← ht]; exact g₀ r hr
  have rdt : t.rd = s₀.rd := by rw [← ht]; rfl
  have wrt : t.wr = s₀.wr := by rw [← ht]; rfl
  have spt : t.sp = s₀.sp := by rw [← ht]; rfl
  unfold mov
  refine wp_mv fun s₂ u₂ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr h1 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₂.other _ (by decide), gt _ (by decide)]
  · rw [u₂.other _ (by decide), gt _ (by decide)]
  · rw [u₂.other _ (by decide), gt _ (by decide)]
  · rw [u₂.other _ (by decide), gt _ (by decide)]
  · rw [u₂.other _ (by decide), gt _ (by decide)]
  · rw [u₂.other _ (by decide), gt _ (by decide)]
  · rw [u₂.gpr, gt _ (by decide)]
  · rw [u₂.other _ h1, gt _ (preserved_ne hr)]
  · rw [u₂.mem, memt]
  · rw [u₂.rd, rdt]
  · rw [u₂.wr, wrt]
  · rw [u₂.sp, spt]

/-- The chain's precondition, on entry to the call with its regions. -/
theorem WMid.chain_pre {out : Bool} {len : Nat → Nat} {s₀ s : State} (h : WPre out len s₀)
    (hm : WMid s₀ s) :
    Proof.Aes.RISCV64.framePre out len
      (s.callEntry.withRegions (rdOf out len s₀) (wrOf out len s₀ (wsR s₀))) := by
  simp only [Proof.Aes.RISCV64.framePre, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a4 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a5 ∉ linkRegs),
    hm.a0, hm.a1, hm.a2, hm.a3, hm.a4, hm.a5]
  refine ⟨?_, h.sch_iv, h.sch_scr.sub_right wsR_sub, h.data_iv, h.data_scr.sub_right wsR_sub,
    h.iv_scr.sub_right wsR_sub, h.iv_wrap, h.data_wrap, h.rounds⟩
  cases out
  · exact And.intro rfl rfl
  · exact And.intro rfl rfl

section
variable {out : Bool} {len : Nat → Nat} {k : Contract isa} {c : Prog isa} (hk : ChainK out len k c)
include hk

theorem wrap_call {name : String} {s₀ s : State} (h : WPre out len s₀) (hm : WMid s₀ s) :
    WP isa (.call name c) s fun s' =>
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      Frame (wrOf out len s₀ (wsR s₀)) s.mem s'.mem ∧
      k.post (s.callEntry.withRegions (rdOf out len s₀) (wrOf out len s₀ (wsR s₀)))
        (s'.withRegions (rdOf out len s₀) (wrOf out len s₀ (wsR s₀))) := by
  refine WP.call (k := k) hk.correct (hk.pre _ (hm.chain_pre h)) (by rw [hm.rd, hm.wr]; exact h.covers)
    (by rw [hm.wr]; exact h.covers_wr) ?_ hk.noFrames
  intro s' hrd hwr hsp hf hcs _ hpost
  exact ⟨hrd, hwr, hsp, hcs, hf, hpost⟩

theorem wrap_wp {name : String} {s₀ : State} (h : WPre out len s₀) :
    WP isa (chainWrap name c) s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.gpr .ra = s₀.gpr .ra ∧ s'.sp = s₀.sp ∧ k.post s₀ s' := by
  refine WP.seq (WP.mono (save_wp h) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (wrap_call hk (name := name) h h₁) fun s₂ ⟨rd₂, wr₂, sp₂, cs₂, f₂, hpost⟩ => ?_)
  have hsv : Spill.Saved (sv s₀) (saveG s₀) chSaved s₂.mem :=
    (Spill.saveMem_saved (by decide) s₀.mem (sv s₀) _).frame (by have := f₂; rw [h₁.mem] at this; exact this)
      fun p hp r hr => h.slots_disj hp r hr
  have s1₂ : s₂.gpr .s1 = S s₀ := by rw [cs₂ _ (by decide), h₁.s1]
  have rdwr₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [rd₂, wr₂, h₁.rd, h₁.wr]
  rw [show encRestore = savePtr .s1 ++ Spill.restoreCode .t0 chSaved from rfl, WP.block_append_iff]
  refine WP.mono (savePtr_ok .s1) fun s₃ e => ?_
  subst e
  rw [s1₂]
  refine WP.mono (Spill.restore_wp (b := .t0) (l := chSaved) (B := sv s₀) (align_al _)
    (RegUpd.gpr_write_self _ _ _) (by decide) (by decide) (fun p hp => ?_) hsv) fun s₄ r₄ => ?_
  · show InRegions (s₂.rd ++ s₂.wr) _ 8
    rw [rdwr₂]
    have := q_lt s₀
    have := chSaved_bound p hp
    have := h.scr_wrap
    exact in_rw (List.mem_append_right _ h.scr_mem)
      (by rw [sv_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith))
  have g₀ (r : Reg) (hr : r ≠ .t0) : saveG s₀ r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · have h0 := preserved_ne hr
    rw [r₄.gpr_of (r := r) ?_, g₀ r h0]
    by_cases h1 : r = .s1
    · left; subst h1; decide
    · right; rw [RegUpd.gpr_write_of_ne _ _ h0, cs₂ r hr, h₁.keep r hr h1, g₀ r h0]
  · rw [r₄.gpr (.ra, 16) (by decide), g₀ .ra (by decide)]
  · rw [r₄.sp, RegUpd.sp_write, sp₂, h₁.sp]
  -- The chain's postcondition, from the memory after the saves to the memory on entry.
  have m₄ : s₄.mem = s₂.mem := by rw [r₄.mem, RegUpd.mem_write]
  refine hk.post h (fun r hr => ?_) (by rw [State.withRegions_mem, State.callEntry_mem, h₁.mem])
    (by rw [m₄, State.withRegions_mem]) hpost
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [State.withRegions_gpr, State.callEntry_gpr s₁ (by decide : Reg.a0 ∉ linkRegs), h₁.a0]
  · rw [State.withRegions_gpr, State.callEntry_gpr s₁ (by decide : Reg.a1 ∉ linkRegs), h₁.a1]
  · rw [State.withRegions_gpr, State.callEntry_gpr s₁ (by decide : Reg.a2 ∉ linkRegs), h₁.a2]
  · rw [State.withRegions_gpr, State.callEntry_gpr s₁ (by decide : Reg.a3 ∉ linkRegs), h₁.a3]
  · rw [State.withRegions_gpr, State.callEntry_gpr s₁ (by decide : Reg.a4 ∉ linkRegs), h₁.a4]

/-! ## Constant time -/

theorem wrap_rel (name : String) {s₀ s₀' : State} (h0 : WPre out len s₀) (h0' : WPre out len s₀')
    (hq : ChPub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (chainWrap name c) fun _ _ => True := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6⟩ := hq
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5]) (.block encSave) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.s1]) (.block encRestore) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.a0, .a1, .a2, .a3, .a4, .a5]
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨q6, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := WMid s₀) (F₂ := WMid s₀') fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨save_wp h0, save_wp h0'⟩
  have er : rdOf out len s₀' = rdOf out len s₀ := by simp only [rdOf, schR, dataL, W, Dp, N, q0, q3, q4]
  have ew : wrOf out len s₀' (wsR s₀') = wrOf out len s₀ (wsR s₀) := by
    simp only [wrOf, ivR, dataL, wsR, Iv, Dp, N, S, q2, q3, q4, q5]
  have c := (RelCT.call (n := name) hk.correct hk.ct
    (P := fun s₁ s₂ => WMid s₀ s₁ ∧ WMid s₀' s₂) (rdOf out len s₀) (wrOf out len s₀ (wsR s₀)) fun s₁ s₂ hm => by
      have p₂ := hk.pre _ (hm.2.chain_pre h0')
      have c₂ := h0'.covers
      have w₂ := h0'.covers_wr
      rw [er, ew] at p₂ c₂
      rw [ew] at w₂
      refine ⟨hk.pre _ (hm.1.chain_pre h0), p₂, hk.pub_of _ _ ?_, by rw [hm.1.rd, hm.1.wr]; exact h0.covers,
        by rw [hm.1.wr]; exact h0.covers_wr, by rw [hm.2.rd, hm.2.wr]; exact c₂, by rw [hm.2.wr]; exact w₂⟩
      simp only [ChPub, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
        State.callEntry_gpr _ (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a1 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a3 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.a4 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a5 ∉ linkRegs),
        hm.1.a0, hm.1.a1, hm.1.a2, hm.1.a3, hm.1.a4, hm.1.a5, hm.2.a0, hm.2.a1, hm.2.a2, hm.2.a3, hm.2.a4,
        hm.2.a5, hm.1.sp, hm.2.sp]
      exact ⟨q0, q1, q2, q3, q4, q5, q6⟩).wp
    (F₁ := fun (s : State) => s.gpr .s1 = S s₀ ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .s1 = S s₀' ∧ s.sp = s₀'.sp) fun s₁ s₂ hm =>
      ⟨WP.mono (wrap_call hk (name := name) h0 hm.1) fun _ hc =>
        ⟨by rw [hc.2.2.2.1 .s1 (by decide), hm.1.s1], by rw [hc.2.2.1, hm.1.sp]⟩,
       WP.mono (wrap_call hk (name := name) h0' hm.2) fun _ hc =>
        ⟨by rw [hc.2.2.2.1 .s1 (by decide), hm.2.s1], by rw [hc.2.2.1, hm.2.sp]⟩⟩
  have b := taintRegs
    (P := fun s₁ s₂ => (s₁.gpr .s1 = S s₀ ∧ s₁.sp = s₀.sp) ∧ (s₂.gpr .s1 = S s₀' ∧ s₂.sp = s₀'.sp))
    [.s1] (fun s₁ s₂ h => ⟨by rw [h.1.2, h.2.2, q6], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.1, h.2.1, S, S, q5]⟩) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

theorem wrap_ct (name : String) : ConstantTime isa (WPre out len) ChPub (chainWrap name c) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (wrap_rel hk name h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end

/-- The chain, as such a chain. -/
theorem chain_k (out : Bool) :
    ChainK out (16 * ·) (Proof.Aes.chainRISCV64 out) (Impl.Aes.RISCV64.chain out) where
  pre _ h := h
  pub_of _ _ h := h
  correct := Proof.Aes.RISCV64.chain_correct out
  ct := Proof.Aes.RISCV64.chain_ct out
  noFrames := by cases out <;> rfl
  post {s₀ s t t'} h hg hm ht hp := by
    have g0 := hg .a0 (by simp)
    have g1 := hg .a1 (by simp)
    have g2 := hg .a2 (by simp)
    have g3 := hg .a3 (by simp)
    have g4 := hg .a4 (by simp)
    have edata' : Spec.Cbc.blocksAt (chMem s₀) (s₀.gpr .a3) (s₀.gpr .a4).toNat =
        Spec.Cbc.blocksAt s₀.mem (s₀.gpr .a3) (s₀.gpr .a4).toNat := h.blocks_eq
    simp only [Proof.Aes.chainRISCV64, g0, g1, g2, g3, g4, hm, ht] at hp ⊢
    rw [h.sch_eq, h.iv_eq, h.blocks_eq, edata'] at hp
    exact hp

/-! ## CBC encryption -/

/-- The chaining value after CBC encryption, the last ciphertext block, is
the CBC-MAC chain's. -/
theorem next_encrypt (ciph : Spec.Cmac.Cipher) :
    ∀ (xs : List (List Byte)) (c : List Byte),
      Spec.Cbc.next c (Spec.Cbc.encrypt ciph c xs) = Spec.Cmac.chain ciph c xs
  | [], _ => rfl
  | x :: xs, c => by
    rw [Spec.Cbc.encrypt, next_cons, next_encrypt ciph xs]
    simp only [Spec.Cmac.chain, List.foldl_cons, Proof.Aes.RISCV64.cbcXor_comm]

end VG.Proof.AesCbc.RISCV64
