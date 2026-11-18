module

public import VerifiedGarbage.Impl.CmacTripleDes.Stream.X86
public import VerifiedGarbage.Impl.StackScratch.X86
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.CmacTripleDes.X86.Lit
import VerifiedGarbage.Proof.CmacTripleDes.X86.RoundLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.SboxTables
public import VerifiedGarbage.Proof.CmacTripleDes.StreamScratch
meta import VerifiedGarbage.Proof.CmacTripleDes.StreamScratch
meta import VerifiedGarbage.Proof.CmacTripleDes.X86.RoundLit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.TripleDes.SboxTables
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Common
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Inline
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.CmacTripleDes.Words
import VerifiedGarbage.Proof.CmacTripleDes.X86.Update
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Common
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Inline
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.CmacTripleDes.Words
meta import VerifiedGarbage.Proof.CmacTripleDes.X86.Update
meta import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Contract
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Cmac.Stream
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.CmacTripleDes.Stream.X86
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Contract
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Cmac.Stream
meta import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Spec.Cmac.TripleDesContract
import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.Spec.Cmac.TripleDesContract
meta import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `CmacTripleDes.Stream.X86.Verified`, which only this module used -/

section

/-! ### `CmacTripleDes.Stream.X86.Implies`, which this module and modules that import it used -/

section

/-! ### `CmacTripleDes.StreamScratchW`, which this module and modules that import it used -/

section

/-!
# Streaming TDEA-CMAC's `finish` with a larger working space

`finishScratchContract`, with 688 bytes of working space (`absorb`'s) in
place of 640: on x86, `finish` keeps our caller's registers in it after the
working space of the code of `finalize` it runs, as `absorb` does. The
locality of the pre- and postconditions is `finishPost_local`'s, which does
not depend on the working space.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream

open VG.Spec.Cmac

/-- `vg_cmac_triple_des_finish` with `scratch: *mut [u64; 86]`. -/
def finishScratchSig86 : Sig where
  params := [("state", .array true .u64 52), ("count", .int .u64 true),
    ("out", .array true .u8 8), ("scratch", .array true .u64 86)]

/-- `tdesFinishContract`, whatever `scratch` is. -/
def finishScratchContract86 {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finishScratchSig86.contract A
    (post := fun state count out _scratch => tdesFinishPost A.ptrBits state count out)
    (stack := stack)

end VG.Proof.CmacTripleDes.Stream

end

end

/-!
# Streaming TDEA-CMAC on x86: the shared contracts imply ours

The shared contracts with the working space as an argument
(`Proof/CmacTripleDes/StreamScratch.lean`, `StreamScratchW.lean`), which
`Frame.lean` moves to the shared contracts of
`Spec/Cmac/TripleDesContract.lean`: with 20 bytes of stack for
`stream_init` and 24 for `absorb` and `finish` (the arguments they push).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86

open VG VG.X86

/-- A state satisfying `vg_cmac_triple_des_stream_init`'s precondition: the
state at `0x1000`, a 16-byte key at `0x3000` and the scratch buffer at
`0x4000`, as stack arguments at `0x8004`. -/
def initSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x30 else if a = 0x800c then 16
    else if a = 0x8011 then 0x40 else 0
  rd := [⟨0x3000, 16⟩, ⟨0x8004, 16⟩]
  wr := [⟨0x1000, 416⟩, ⟨0x4000, 640⟩]

theorem init_implies : initX86.Implies (streamInitScratchContract X86.abi 20) := by
  have a0 : arg initSat 0 = 0x1000 := by decide
  have a1 : arg initSat 1 = 0x3000 := by decide
  have a2 : arg initSat 2 = 16 := by decide
  have a3 : arg initSat 3 = 0x4000 := by decide
  have e : argAddr initSat 0 = 0x8004 := by decide
  have esp : initSat.gpr .esp = 0x8000 := rfl
  sig_implies [streamInitScratchContract, streamInitScratchSig, Spec.Cmac.tdesStreamInitPre,
    Spec.Cmac.tdesStreamInitPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, initX86]
    [a0, a1, a2, a3, e, esp] using initSat

/-- A state satisfying `vg_cmac_triple_des_absorb`'s precondition: the state
at `0x1000`, `count` 0, no data at `0x3000` and the scratch buffer at
`0x4000`, as stack arguments at `0x8004`. -/
def absorbSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8011 then 0x30 else if a = 0x8019 then 0x40 else 0
  rd := [⟨0x3000, 0⟩, ⟨0x8004, 24⟩]
  wr := [⟨0x1000, 416⟩, ⟨0x4000, 688⟩]

theorem absorb_implies : absorbX86.Implies (absorbScratchContract X86.abi 24) := by
  have a0 : arg absorbSat 0 = 0x1000 := by decide
  have a1 : arg absorbSat 1 = 0 := by decide
  have a2 : arg absorbSat 2 = 0 := by decide
  have a3 : arg absorbSat 3 = 0x3000 := by decide
  have a4 : arg absorbSat 4 = 0 := by decide
  have a5 : arg absorbSat 5 = 0x4000 := by decide
  have e : argAddr absorbSat 0 = 0x8004 := by decide
  have esp : absorbSat.gpr .esp = 0x8000 := rfl
  sig_implies [absorbScratchContract, absorbScratchSig, Spec.Cmac.tdesAbsorbPost, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, absorbX86, countX86] [a0, a1, a2, a3, a4, a5, e, esp] using absorbSat

/-- A state satisfying `vg_cmac_triple_des_finish`'s precondition: the state
at `0x1000`, `count` 0, `out` at `0x2000` and the scratch buffer at
`0x4000`, as stack arguments at `0x8004`. -/
def finishSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8011 then 0x20 else if a = 0x8015 then 0x40 else 0
  rd := [⟨0x8004, 20⟩]
  wr := [⟨0x1000, 416⟩, ⟨0x2000, 8⟩, ⟨0x4000, 688⟩]

theorem finish_implies : finishX86.Implies (finishScratchContract86 X86.abi 24) := by
  have a0 : arg finishSat 0 = 0x1000 := by decide
  have a1 : arg finishSat 1 = 0 := by decide
  have a2 : arg finishSat 2 = 0 := by decide
  have a3 : arg finishSat 3 = 0x2000 := by decide
  have a4 : arg finishSat 4 = 0x4000 := by decide
  have e : argAddr finishSat 0 = 0x8004 := by decide
  have esp : finishSat.gpr .esp = 0x8000 := rfl
  sig_implies [finishScratchContract86, finishScratchSig86, Spec.Cmac.tdesFinishPost, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, finishX86, countX86] [a0, a1, a2, a3, a4, e, esp] using finishSat

end VG.Proof.CmacTripleDes.Stream.X86

end

end

/-! ### `CmacTripleDes.Stream.X86.AbsorbCorrect`, which only this module used -/

section

/-! ### `CmacTripleDes.Stream.X86.Absorb`, which this module and modules that import it used -/

section

/-! ### `CmacTripleDes.Stream.X86.AbsorbBlocks`, which this module and modules that import it used -/

section

/-!
# Streaming TDEA-CMAC on x86: `vg_cmac_triple_des_absorb`'s straight-line code

The precondition by name (`APre`), what holds at every point of the code
outside the calls (`ACtx`: `esp`, the regions and the stack arguments are
those on entry), and what each piece of code between the copies and calls
computes, in terms of `count` (`c`) and `len` (`L`): the bytes held back `h =
held c`, the bytes copied after them `f = min L (8 - h)`, the data left `L -
f`, whether to chain the block held back (`b1`), the blocks chained after it
(`nb`), and the rest (`rest`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86

open VG VG.X86 VG.Impl.CmacTripleDes.Stream.X86

open VG.Proof.MdStream.X86 (Upd Fupd wp_mov wp_movi wp_addi wp_add wp_subi wp_sub wp_andi wp_cmp wp_shr eval_e
  eval_b ofNat_beq_zero sub_ofNat)
open VG.Proof.CmacTripleDes.Stream (held held_le)

/-! ## The numbers -/

/-- The bytes copied after the `held c` held back. -/
def fOf (c L : Nat) : Nat := min L (8 - held c)

/-- The data left after them. -/
def leftOf (c L : Nat) : Nat := L - fOf c L

/-- The number of blocks the first call chains: the block held back, if data is left. -/
def b1Of (c L : Nat) : Nat := if leftOf c L = 0 then 0 else 1

/-- The number of blocks the second call chains: those of the data left but its
last 1 to 8 bytes. -/
def nbOf (c L : Nat) : Nat := if leftOf c L = 0 then 0 else (leftOf c L - 1) / 8

/-- The bytes copied to the start of the bytes held back at the end. -/
def restOf (c L : Nat) : Nat := leftOf c L - 8 * nbOf c L

theorem f_le (c L : Nat) : fOf c L ≤ L ∧ fOf c L + held c ≤ 8 := by
  have := held_le c; unfold fOf; omega_arith

theorem nb_le (c L : Nat) : fOf c L + 8 * nbOf c L + restOf c L = L := by
  have := f_le c L; unfold restOf nbOf leftOf; split <;> omega_arith

theorem rest_le (c L : Nat) : restOf c L ≤ 8 := by unfold restOf nbOf leftOf; split <;> omega_arith

theorem rest_zero {c L : Nat} (h : leftOf c L = 0) : restOf c L = 0 := by simp [restOf, nbOf, h]

/-! ## Arithmetic on registers -/

/-- `8 nb` for the data left `x > 0`, as `sub 1; mov; and 7; sub` computes it. -/
theorem nb8_bv {x : Nat} (hx : 0 < x) (hx' : x < 2 ^ 32) :
    BitVec.ofNat 32 x - 1 - ((BitVec.ofNat 32 x - 1) &&& 7) = BitVec.ofNat 32 (8 * ((x - 1) / 8)) := by
  apply BitVec.eq_of_toNat_eq
  obtain e : (BitVec.ofNat 32 x - 1).toNat = x - 1 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]; omega_arith
  rw [BitVec.toNat_sub, and7, e, BitVec.toNat_ofNat]
  omega_arith

theorem shr3 {n : Nat} (hn : 8 * n < 2 ^ 32) :
    BitVec.ofNat 32 (8 * n) >>> 3 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_arith

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev aSt : BitVec 32 := arg s₀ 0
abbrev aD : BitVec 32 := arg s₀ 3
abbrev aL : Nat := (arg s₀ 4).toNat
abbrev aSc : BitVec 32 := arg s₀ 5
abbrev aE : BitVec 32 := s₀.gpr .esp
/-- `count`. -/
abbrev aC : Nat := (countX86 s₀).toNat
abbrev astR : Region := ⟨(aSt s₀).setWidth 64, 416⟩
abbrev adR : Region := ⟨(aD s₀).setWidth 64, aL s₀⟩
abbrev ascR : Region := ⟨(aSc s₀).setWidth 64, 688⟩
abbrev aaR : Region := ⟨argAddr s₀ 0, 24⟩

/-- Where the function writes: the state, the scratch buffer and the stack. -/
abbrev ABig : List Region := [astR s₀, ascR s₀, below (aE s₀) 24]

end

/-- The precondition, by name. -/
structure APre (s₀ : State) : Prop where
  rd : s₀.rd = [adR s₀, aaR s₀]
  wr : s₀.wr = [astR s₀, ascR s₀]
  st_d : (astR s₀).Disjoint (adR s₀)
  st_s : (astR s₀).Disjoint (ascR s₀)
  d_s : (adR s₀).Disjoint (ascR s₀)
  a_st : (aaR s₀).Disjoint (astR s₀)
  a_s : (aaR s₀).Disjoint (ascR s₀)
  ret_st : (⟨(aE s₀).setWidth 64, 4⟩ : Region).Disjoint (astR s₀)
  ret_s : (⟨(aE s₀).setWidth 64, 4⟩ : Region).Disjoint (ascR s₀)
  b_st' : (⟨(aE s₀).setWidth 64 - BitVec.ofNat 64 24, 24⟩ : Region).Disjoint (astR s₀)
  b_d' : (⟨(aE s₀).setWidth 64 - BitVec.ofNat 64 24, 24⟩ : Region).Disjoint (adR s₀)
  b_s' : (⟨(aE s₀).setWidth 64 - BitVec.ofNat 64 24, 24⟩ : Region).Disjoint (ascR s₀)
  fSt : (aSt s₀).toNat + 416 ≤ 2 ^ 32
  fD : (aD s₀).toNat + aL s₀ ≤ 2 ^ 32
  fS : (aSc s₀).toNat + 688 ≤ 2 ^ 32
  esp24 : 24 ≤ (aE s₀).toNat
  espfit : (aE s₀).toNat + 28 ≤ 2 ^ 32

theorem APre.of {s₀ : State} (h : absorbX86.pre s₀) : APre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q⟩

namespace APre
variable {s₀ : State} (hp : APre s₀)
include hp

theorem b_st : (below (aE s₀) 24).Disjoint (astR s₀) := by rw [below_eq hp.esp24]; exact hp.b_st'
theorem b_d : (below (aE s₀) 24).Disjoint (adR s₀) := by rw [below_eq hp.esp24]; exact hp.b_d'
theorem b_s : (below (aE s₀) 24).Disjoint (ascR s₀) := by rw [below_eq hp.esp24]; exact hp.b_s'

theorem fit : (s₀.gpr .esp).toNat + 4 + 4 * 6 ≤ 2 ^ 32 := by have := hp.espfit; omega_arith

theorem arg_in {i : Nat} (hi : i < 6) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 :=
  ⟨aaR s₀, by simp [hp.rd], arg_contains hp.fit hi⟩

/-- The stack arguments are unchanged where only `ABig` changes. -/
theorem keep {m : Mem} (hf : Frame (ABig s₀) s₀.mem m) {i : Nat} (hi : i < 6) :
    m.readW (argAddr s₀ i) 32 = arg s₀ i :=
  arg_keep hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.a_st.sub_left (arg_sub hp.fit hi)
    · exact hp.a_s.sub_left (arg_sub hp.fit hi)
    · exact (args_below hp.fit (by decide) hp.esp24).symm.sub_left (arg_sub hp.fit hi)

theorem argsOut : ArgsOut 6 s₀ := by
  refine ⟨by have := hp.espfit; omega_arith, ?_⟩
  rw [hp.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by have := hp.espfit; omega_arith) hp.ret_st hp.a_st
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by have := hp.espfit; omega_arith) hp.ret_s hp.a_s

end APre

theorem APre.lt {s₀ : State} (_hp : APre s₀) : aL s₀ < 2 ^ 32 := (arg s₀ 4).isLt

theorem APre.savedMem_big {s₀ : State} (_hp : APre s₀) : Frame (ABig s₀) s₀.mem (savedMem s₀ (aSc s₀)) :=
  (savedMem_frame _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨ascR s₀, by simp, Offset.sub_base _ (by decide)⟩

/-! ## Between the calls -/

/-- What holds at every point of the code outside the calls: `esp`, the
regions and the stack arguments are those on entry. -/
structure ACtx (s₀ s : State) : Prop where
  esp : s.gpr .esp = aE s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  args : ∀ i < 6, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i

theorem ACtx.of_frame {s₀ s : State} (hp : APre s₀) (hesp : s.gpr .esp = aE s₀) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hf : Frame (ABig s₀) s₀.mem s.mem) : ACtx s₀ s :=
  ⟨hesp, hrd, hwr, fun _ hi => hp.keep hf hi⟩

theorem ACtx.upd {s₀ s s' : State} {d : Reg} {v : BitVec 32} (h : ACtx s₀ s) (u : Upd s s' d v)
    (hd : d ≠ .esp) : ACtx s₀ s' :=
  ⟨by rw [u.other _ (Ne.symm hd), h.esp], by rw [u.rd, h.rd], by rw [u.wr, h.wr], by rw [u.mem]; exact h.args⟩

theorem ACtx.fupd {s₀ s s' : State} (h : ACtx s₀ s) (u : Fupd s s') : ACtx s₀ s' :=
  ⟨by rw [u.gpr, h.esp], by rw [u.rd, h.rd], by rw [u.wr, h.wr], by rw [u.mem]; exact h.args⟩

theorem ACtx.pt {s₀ s : State} (h : ACtx s₀ s) : Pt 6 s₀ s := ⟨h.esp, h.wr, h.args⟩

/-- `mov d, [esp + 4 + 4 i]`. -/
theorem ACtx.wp_arg {s₀ s : State} (hp : APre s₀) (h : ACtx s₀ s) {d : Reg} (hd : d ≠ .esp) {i : Nat} (hi : i < 6)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (arg s₀ i) → ACtx s₀ s' → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem (argOp i)) :: is)) s Q :=
  VG.Proof.CmacTripleDes.Stream.X86.wp_arg (s₀ := s₀) h.esp (by rw [h.rd, h.wr]; exact hp.arg_in hi) (h.args i hi)
    fun s' u => k s' u (h.upd u hd)

/-! ## `fill`: how many bytes to copy, and where -/

/-- What `fill` leaves. -/
structure Filled (s₀ s s' : State) : Prop where
  ctx : ACtx s₀ s'
  mem : s'.mem = s.mem
  ecx : s'.gpr .ecx = BitVec.ofNat 32 (fOf (aC s₀) (aL s₀))
  ebp : s'.gpr .ebp = BitVec.ofNat 32 (fOf (aC s₀) (aL s₀))
  esi : s'.gpr .esi = aD s₀
  edi : s'.gpr .edi = aSt s₀ + BitVec.ofNat 32 (408 + held (aC s₀))

theorem fill_wp {s₀ s : State} (hp : APre s₀) (h : ACtx s₀ s)
    (hax : s.gpr .eax = BitVec.ofNat 32 (held (aC s₀))) : WP isa fill s (Filled s₀ s) := by
  obtain hh := held_le (aC s₀)
  have hL := hp.lt
  have ⟨hfL, hfh⟩ := f_le (aC s₀) (aL s₀)
  unfold fill
  refine WP.seq (wp_movi fun s₁ u₁ => wp_sub fun s₂ u₂ _ => (h.upd u₁ (by decide)).upd u₂ (by decide) |>.wp_arg hp
    (by decide) (by decide) fun s₃ u₃ c₃ => wp_cmp fun s₄ f₄ cf₄ _ => WP.block_nil ?_)
  obtain ecx₂ : s₂.gpr .ecx = BitVec.ofNat 32 (8 - held (aC s₀)) := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), hax]; exact sub_ofNat hh
  obtain ecx₄ : s₄.gpr .ecx = BitVec.ofNat 32 (8 - held (aC s₀)) := by rw [f₄.gpr, u₃.other _ (by decide), ecx₂]
  obtain edx₄ : s₄.gpr .edx = BitVec.ofNat 32 (aL s₀) := by rw [f₄.gpr, u₃.gpr]; exact arg_ofNat s₀ 4
  obtain c₄ := c₃.fupd f₄
  obtain cf : s₄.cf = some (decide (aL s₀ < 8 - held (aC s₀))) := by
    rw [cf₄, u₃.gpr, u₃.other _ (by decide), ecx₂, toNat_ofNat32 (by omega_arith)]
  obtain eax₄ : s₄.gpr .eax = s.gpr .eax := by
    rw [f₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  obtain m₄ : s₄.mem = s.mem := by rw [f₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine WP.seq (WP.mono (Q := fun (s₅ : State) => ACtx s₀ s₅ ∧ s₅.mem = s.mem ∧
      s₅.gpr .ecx = BitVec.ofNat 32 (fOf (aC s₀) (aL s₀)) ∧ s₅.gpr .eax = s.gpr .eax) ?_ fun s₅ h₅ => ?_)
  · have ev : isa.eval .b s₄ = some (decide (aL s₀ < 8 - held (aC s₀))) := by
      show VG.X86.eval .b s₄ = _; rw [eval_b, cf]
    by_cases hl : aL s₀ < 8 - held (aC s₀)
    · refine WP.ite true (by rw [ev]; simp [hl]) (fun _ => wp_mov fun s₅ u₅ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨c₄.upd u₅ (by decide), by rw [u₅.mem, m₄], by rw [u₅.gpr, edx₄, fOf, Nat.min_eq_left (by omega_arith)],
        by rw [u₅.other _ (by decide), eax₄]⟩
    · refine WP.ite false (by rw [ev]; simp [hl]) (fun h => by cases h) fun _ => WP.block_nil ?_
      exact ⟨c₄, m₄, by rw [ecx₄, fOf, Nat.min_eq_right (by omega_arith)], eax₄⟩
  · obtain ⟨c₅, m₅, ecx₅, eax₅⟩ := h₅
    refine wp_mov fun s₆ u₆ => (c₅.upd u₆ (by decide)).wp_arg hp (by decide) (by decide) fun s₇ u₇ c₇ =>
      c₇.wp_arg hp (by decide) (by decide) fun s₈ u₈ c₈ => wp_addi fun s₉ u₉ => wp_add fun s₁₀ u₁₀ => WP.block_nil ?_
    have fSt : (aSt s₀).toNat + 416 ≤ 2 ^ 32 := hp.fSt
    refine ⟨(c₈.upd u₉ (by decide)).upd u₁₀ (by decide), by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅],
      ?_, ?_, ?_, ?_⟩
    · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.other _ (by decide), ecx₅]
    · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.gpr, ecx₅]
    · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr]
    · rw [u₁₀.gpr, u₉.gpr, u₉.other _ (by decide), u₈.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.other _ (by decide), eax₅, hax]
      exact Offset.add_add _ 408 _

/-! ## `chain1`: the arguments of the first call -/

/-- The arguments of a call of `vg_cmac_aes_update` on `n` blocks at `Dd`,
from a state with the regions and stack of `s₀`. -/
theorem APre.uargs {s₀ s : State} (hp : APre s₀) {Dd : BitVec 32} {n : Nat}
    (heax : s.gpr .eax = aSt s₀)
    (hedx : s.gpr .edx = aSt s₀ + BitVec.ofNat 32 400) (hebx : s.gpr .ebx = Dd)
    (hesi : s.gpr .esi = BitVec.ofNat 32 n) (hedi : s.gpr .edi = aSc s₀) (hesp : s.gpr .esp = aE s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hn : 8 * n < 2 ^ 32)
    (hdc : (⟨Dd.setWidth 64, 8 * n⟩ : Region).Disjoint ⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 400, 8⟩)
    (hds : (⟨Dd.setWidth 64, 8 * n⟩ : Region).Disjoint ⟨(aSc s₀).setWidth 64, 640⟩)
    (hstk : (below (aE s₀) 24).Disjoint ⟨Dd.setWidth 64, 8 * n⟩) (hfD : Dd.toNat + 8 * n ≤ 2 ^ 32)
    (hcov : ∃ r' ∈ s₀.rd ++ s₀.wr, ∃ off, Dd.setWidth 64 = r'.base + BitVec.ofNat 64 off ∧ off + 8 * n ≤ r'.len) :
    UArgs s (aSt s₀) (aSt s₀ + BitVec.ofNat 32 400) Dd (aSc s₀) n := by
  have fSt : (aSt s₀).toNat + 416 ≤ 2 ^ 32 := hp.fSt
  have fS : (aSc s₀).toNat + 688 ≤ 2 ^ 32 := hp.fS
  obtain p400 : (aSt s₀ + BitVec.ofNat 32 400).setWidth 64 = (aSt s₀).setWidth 64 + BitVec.ofNat 64 400 :=
    add_setWidth (by omega_arith)
  obtain c400 : Region.Sub ⟨(aSt s₀ + BitVec.ofNat 32 400).setWidth 64, 8⟩ (astR s₀) := by
    rw [p400]; exact Offset.sub_base _ (by decide)
  exact
  { eax := heax, edx := hedx, ebx := hebx, esi := hesi, edi := hedi, hn := hn
    esp := by rw [hesp]; exact hp.esp24
    wc := by rw [p400]; exact Offset.base_disjoint _ (by decide) (by omega_arith)
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    dc := by rw [p400]; exact hdc
    ds := hds
    cs := (hp.st_s.sub_left c400).sub_right (Region.sub_prefix (by decide))
    bW := by rw [hesp]; exact hp.b_st.sub_right (Region.sub_prefix (by decide))
    bD := by rw [hesp]; exact hstk
    bC := by rw [hesp]; exact hp.b_st.sub_right c400
    bS := by rw [hesp]; exact hp.b_s.sub_right (Region.sub_prefix (by decide))
    fW := by omega_arith
    fC := by rw [add_toNat (by omega_arith)]; omega_arith
    fD := hfD
    fS := by omega_arith
    reads := by
      rw [hrd, hwr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨astR s₀, by simp [hp.wr], 0, by simp, by simp⟩
      · exact hcov
    writes := by
      rw [hwr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨astR s₀, by simp, 400, p400, by simp⟩
      · exact ⟨ascR s₀, by simp, 0, by simp, by simp⟩ }

/-- What `chain1` leaves. -/
structure Chained₁ (s₀ s s' : State) : Prop where
  args : UArgs s' (aSt s₀) (aSt s₀ + BitVec.ofNat 32 400) (aSt s₀ + BitVec.ofNat 32 408) (aSc s₀)
    (b1Of (aC s₀) (aL s₀))
  ctx : ACtx s₀ s'
  ebp : s'.gpr .ebp = s.gpr .ebp
  mem : s'.mem = s.mem

theorem chain1_wp {s₀ s : State} (hp : APre s₀) (h : ACtx s₀ s)
    (hbp : s.gpr .ebp = BitVec.ofNat 32 (fOf (aC s₀) (aL s₀))) : WP isa chain1 s (Chained₁ s₀ s) := by
  have hL := hp.lt
  have ⟨hfL, _⟩ := f_le (aC s₀) (aL s₀)
  have fSt : (aSt s₀).toNat + 416 ≤ 2 ^ 32 := hp.fSt
  unfold chain1
  refine WP.seq (wp_movi fun s₁ u₁ => (h.upd u₁ (by decide)).wp_arg hp (by decide) (by decide) fun s₂ u₂ c₂ =>
    wp_sub fun s₃ u₃ z₃ => WP.block_nil ?_)
  obtain c₃ := c₂.upd u₃ (by decide)
  obtain z : s₃.zf = some (decide (leftOf (aC s₀) (aL s₀) = 0)) := by
    rw [z₃, u₂.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hbp, arg_ofNat s₀ 4, sub_ofNat hfL,
      ofNat_beq_zero (by omega_arith)]; rfl
  obtain ebp₃ : s₃.gpr .ebp = s.gpr .ebp := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  obtain m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => ACtx s₀ s₄ ∧ s₄.mem = s.mem ∧ s₄.gpr .ebp = s.gpr .ebp ∧
      s₄.gpr .esi = BitVec.ofNat 32 (b1Of (aC s₀) (aL s₀))) ?_ fun s₄ h₄ => ?_)
  · have ev : isa.eval .e s₃ = some (decide (leftOf (aC s₀) (aL s₀) = 0)) := by
      show VG.X86.eval .e s₃ = _; rw [eval_e, z]
    by_cases h0 : leftOf (aC s₀) (aL s₀) = 0
    · refine WP.ite true (by rw [ev]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨c₃, m₃, ebp₃, by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; simp only [b1Of, h0, ↓reduceIte]; rfl⟩
    · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => wp_movi fun s₄ u₄ => WP.block_nil ?_
      exact ⟨c₃.upd u₄ (by decide), by rw [u₄.mem, m₃], by rw [u₄.other _ (by decide), ebp₃],
        by rw [u₄.gpr]; simp only [b1Of, h0, ↓reduceIte]; rfl⟩
  · obtain ⟨c₄, m₄, ebp₄, esi₄⟩ := h₄
    refine c₄.wp_arg hp (by decide) (by decide) fun s₅ u₅ c₅ =>
      wp_mov fun s₇ u₇ => wp_addi fun s₈ u₈ => wp_mov fun s₉ u₉ => wp_addi fun s₁₀ u₁₀ =>
      ((((c₅.upd u₇ (by decide)).upd u₈ (by decide)).upd u₉ (by decide)).upd u₁₀ (by decide)).wp_arg hp
        (by decide) (by decide) fun s₁₁ u₁₁ c₁₁ => WP.block_nil ?_
    obtain eax₁₁ : s₁₁.gpr .eax = aSt s₀ := by
      rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₅.gpr]
    obtain hb1 : 8 * b1Of (aC s₀) (aL s₀) ≤ 8 := by unfold b1Of; split <;> omega_arith
    obtain p408 : (aSt s₀ + BitVec.ofNat 32 408).setWidth 64 = (aSt s₀).setWidth 64 + BitVec.ofNat 64 408 :=
      add_setWidth (by omega_arith)
    obtain c408 : Region.Sub ⟨(aSt s₀ + BitVec.ofNat 32 408).setWidth 64, 8 * b1Of (aC s₀) (aL s₀)⟩ (astR s₀) := by
      rw [p408]; exact Offset.sub_base _ (by omega_arith)
    refine ⟨hp.uargs eax₁₁ ?_ ?_ ?_ u₁₁.gpr c₁₁.esp c₁₁.rd c₁₁.wr (by omega_arith) ?_
      ((hp.st_s.sub_left c408).sub_right (Region.sub_prefix (by decide))) (hp.b_st.sub_right c408)
      (by rw [add_toNat (by omega_arith)]; omega_arith) ⟨astR s₀, by simp [hp.wr], 408, p408, by simp; omega_arith⟩,
      c₁₁, ?_, ?_⟩
    · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.gpr,
        u₅.gpr]; rfl
    · rw [u₁₁.other _ (by decide), u₁₀.gpr, u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
        u₅.gpr]; rfl
    · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₅.other _ (by decide), esi₄]
    · rw [p408]; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
    · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₅.other _ (by decide), ebp₄]
    · rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₅.mem, m₄]

/-! ## `chain2`: the arguments of the second call -/

/-- The data the second call reads: the data left, or, with none left, the
bytes held back (none of which it reads). -/
def d2Of (s₀ : State) : BitVec 32 :=
  if leftOf (aC s₀) (aL s₀) = 0 then aSt s₀ + BitVec.ofNat 32 408 else aD s₀ + BitVec.ofNat 32 (fOf (aC s₀) (aL s₀))

/-- What `chain2` leaves. -/
structure Chained₂ (s₀ s s' : State) : Prop where
  args : UArgs s' (aSt s₀) (aSt s₀ + BitVec.ofNat 32 400) (d2Of s₀) (aSc s₀) (nbOf (aC s₀) (aL s₀))
  ctx : ACtx s₀ s'
  ebp : s'.gpr .ebp = BitVec.ofNat 32 (fOf (aC s₀) (aL s₀) + 8 * nbOf (aC s₀) (aL s₀))
  mem : s'.mem = s.mem

theorem chain2_wp {s₀ s : State} (hp : APre s₀) (h : ACtx s₀ s)
    (hbp : s.gpr .ebp = BitVec.ofNat 32 (fOf (aC s₀) (aL s₀))) : WP isa chain2 s (Chained₂ s₀ s) := by
  have hL := hp.lt
  have ⟨hfL, _⟩ := f_le (aC s₀) (aL s₀)
  obtain hsum := nb_le (aC s₀) (aL s₀)
  have fSt : (aSt s₀).toNat + 416 ≤ 2 ^ 32 := hp.fSt
  have fD : (aD s₀).toNat + aL s₀ ≤ 2 ^ 32 := hp.fD
  unfold chain2
  refine WP.seq (wp_movi fun s₁ u₁ => (h.upd u₁ (by decide)).wp_arg hp (by decide) (by decide) fun s₂ u₂ c₂ =>
    wp_addi fun s₃ u₃ => (c₂.upd u₃ (by decide)).wp_arg hp (by decide) (by decide) fun s₄ u₄ c₄ =>
    wp_sub fun s₅ u₅ z₅ => WP.block_nil ?_)
  obtain c₅ := c₄.upd u₅ (by decide)
  obtain ebp₄ : s₄.gpr .ebp = s.gpr .ebp := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  obtain ebp₅ : s₅.gpr .ebp = s.gpr .ebp := by rw [u₅.other _ (by decide), ebp₄]
  obtain edx₅ : s₅.gpr .edx = BitVec.ofNat 32 (leftOf (aC s₀) (aL s₀)) := by
    rw [u₅.gpr, u₄.gpr, ebp₄, hbp, arg_ofNat s₀ 4, sub_ofNat hfL]; rfl
  obtain z : s₅.zf = some (decide (leftOf (aC s₀) (aL s₀) = 0)) := by
    rw [z₅, u₄.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hbp, arg_ofNat s₀ 4, sub_ofNat hfL, ofNat_beq_zero (by omega_arith)]; rfl
  obtain ecx₅ : s₅.gpr .ecx = BitVec.ofNat 32 0 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; rfl
  obtain ebx₅ : s₅.gpr .ebx = aSt s₀ + BitVec.ofNat 32 408 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr]; rfl
  obtain m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine WP.seq (WP.mono (Q := fun (s₆ : State) => ACtx s₀ s₆ ∧ s₆.mem = s.mem ∧ s₆.gpr .ebp = s.gpr .ebp ∧
      s₆.gpr .ecx = BitVec.ofNat 32 (8 * nbOf (aC s₀) (aL s₀)) ∧ s₆.gpr .ebx = d2Of s₀) ?_ fun s₆ h₆ => ?_)
  · have ev : isa.eval .e s₅ = some (decide (leftOf (aC s₀) (aL s₀) = 0)) := by
      show VG.X86.eval .e s₅ = _; rw [eval_e, z]
    by_cases h0 : leftOf (aC s₀) (aL s₀) = 0
    · refine WP.ite true (by rw [ev]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨c₅, m₅, ebp₅, by rw [ecx₅]; simp only [nbOf, h0, ↓reduceIte],
        by rw [ebx₅]; simp only [d2Of, h0, ↓reduceIte]⟩
    · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => ?_
      refine wp_mov fun s₆ u₆ => wp_subi fun s₇ u₇ _ => wp_mov fun s₈ u₈ => wp_andi fun s₉ u₉ => wp_sub fun s₁₀ u₁₀ _ =>
        (((((c₅.upd u₆ (by decide)).upd u₇ (by decide)).upd u₈ (by decide)).upd u₉ (by decide)).upd u₁₀
          (by decide)).wp_arg hp (by decide) (by decide) fun s₁₁ u₁₁ c₁₁ => wp_add fun s₁₂ u₁₂ => WP.block_nil ?_
      refine ⟨c₁₁.upd u₁₂ (by decide), ?_, ?_, ?_, ?_⟩
      · rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅]
      · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
          u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), ebp₅]
      · have ecx₇ : s₇.gpr .ecx = BitVec.ofNat 32 (leftOf (aC s₀) (aL s₀)) - 1 := by rw [u₇.gpr, u₆.gpr, edx₅]
        obtain ecx₉ : s₉.gpr .ecx = s₇.gpr .ecx := by rw [u₉.other _ (by decide), u₈.other _ (by decide)]
        obtain eax₉ : s₉.gpr .eax = s₇.gpr .ecx &&& 7 := by rw [u₉.gpr, u₈.gpr]
        rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, ecx₉, eax₉, ecx₇]
        simp only [nbOf, h0, ↓reduceIte]
        exact nb8_bv (by omega_arith) (by unfold leftOf; omega_arith)
      · rw [u₁₂.gpr, u₁₁.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
          u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), ebp₅, hbp]
        simp only [d2Of, h0, ↓reduceIte]
  · obtain ⟨c₆, m₆, ebp₆, ecx₆, ebx₆⟩ := h₆
    obtain hn8 : 8 * nbOf (aC s₀) (aL s₀) < 2 ^ 32 := by omega_arith
    refine wp_mov fun s₇ u₇ => wp_shr (by decide) fun s₈ u₈ => wp_add fun s₉ u₉ =>
      (((c₆.upd u₇ (by decide)).upd u₈ (by decide)).upd u₉ (by decide)).wp_arg hp (by decide) (by decide)
        fun s₁₀ u₁₀ c₁₀ => wp_mov fun s₁₂ u₁₂ =>
        wp_addi fun s₁₃ u₁₃ => ((c₁₀.upd u₁₂ (by decide)).upd u₁₃ (by decide)).wp_arg hp (by decide) (by decide)
        fun s₁₄ u₁₄ c₁₄ => WP.block_nil ?_
    obtain ebx₁₄ : s₁₄.gpr .ebx = d2Of s₀ := by
      rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide),
        u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), ebx₆]
    obtain hnb : nbOf (aC s₀) (aL s₀) = 0 ∨ 0 < leftOf (aC s₀) (aL s₀) := by
      unfold nbOf; split <;> omega_arith
    -- The data the call reads.
    obtain hn0 : leftOf (aC s₀) (aL s₀) = 0 → nbOf (aC s₀) (aL s₀) = 0 := fun h => by simp [nbOf, h]
    obtain hd2 : ((d2Of s₀).setWidth 64 = (aSt s₀).setWidth 64 + BitVec.ofNat 64 408 ∧ nbOf (aC s₀) (aL s₀) = 0) ∨
        ((d2Of s₀).setWidth 64 = (aD s₀).setWidth 64 + BitVec.ofNat 64 (fOf (aC s₀) (aL s₀)) ∧
          0 < leftOf (aC s₀) (aL s₀)) := by
      unfold d2Of
      split
      · exact .inl ⟨add_setWidth (by omega_arith), hn0 (by assumption)⟩
      · exact .inr ⟨add_setWidth (by unfold leftOf at *; omega_arith), by omega_arith⟩
    obtain dD : 0 < leftOf (aC s₀) (aL s₀) →
        Region.Sub ⟨(aD s₀).setWidth 64 + BitVec.ofNat 64 (fOf (aC s₀) (aL s₀)), 8 * nbOf (aC s₀) (aL s₀)⟩
          (adR s₀) := fun _ => Offset.sub_base _ (by omega_arith)
    refine ⟨hp.uargs ?_ ?_ ebx₁₄ ?_ u₁₄.gpr c₁₄.esp c₁₄.rd c₁₄.wr hn8 ?_ ?_ ?_ ?_ ?_, c₁₄, ?_, ?_⟩
    · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₀.gpr]
    · rw [u₁₄.other _ (by decide), u₁₃.gpr, u₁₂.gpr, u₁₀.gpr]; rfl
    · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide),
        u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.gpr, ecx₆]
      exact shr3 hn8
    · rcases hd2 with ⟨e, hn⟩ | ⟨e, hl⟩ <;> rw [e]
      · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
      · exact (hp.st_d.sub_left (Offset.sub_base _ (by decide))).symm.sub_left (dD hl)
    · rcases hd2 with ⟨e, hn⟩ | ⟨e, hl⟩ <;> rw [e]
      · exact (hp.st_s.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Region.sub_prefix (by decide))
      · exact (hp.d_s.sub_left (dD hl)).sub_right (Region.sub_prefix (by decide))
    · rcases hd2 with ⟨e, hn⟩ | ⟨e, hl⟩ <;> rw [e]
      · exact hp.b_st.sub_right (Offset.sub_base _ (by omega_arith))
      · exact hp.b_d.sub_right (dD hl)
    · unfold d2Of
      split
      · rw [add_toNat (by omega_arith)]; omega_arith
      · rw [add_toNat (by unfold leftOf at *; omega_arith)]; omega_arith
    · rcases hd2 with ⟨e, hn⟩ | ⟨e, hl⟩ <;> rw [e]
      · exact ⟨astR s₀, by simp [hp.wr], 408, rfl, by simp; omega_arith⟩
      · exact ⟨adR s₀, by simp [hp.rd], fOf (aC s₀) (aL s₀), rfl, by simp; omega_arith⟩
    · have ebp₈ : s₈.gpr .ebp = s.gpr .ebp := by
        rw [u₈.other _ (by decide), u₇.other _ (by decide), ebp₆]
      obtain ecx₈ : s₈.gpr .ecx = BitVec.ofNat 32 (8 * nbOf (aC s₀) (aL s₀)) := by
        rw [u₈.other _ (by decide), u₇.other _ (by decide), ecx₆]
      rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide),
        u₁₀.other _ (by decide), u₉.gpr, ebp₈, ecx₈, hbp]
      exact (BitVec.ofNat_add _ _).symm
    · rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, m₆]

/-! ## `rest`: the arguments of the last copy -/

/-- What `rest` leaves. -/
structure Rested (s₀ s s' : State) : Prop where
  ctx : ACtx s₀ s'
  mem : s'.mem = s.mem
  esi : s'.gpr .esi = aD s₀ + BitVec.ofNat 32 (fOf (aC s₀) (aL s₀) + 8 * nbOf (aC s₀) (aL s₀))
  edi : s'.gpr .edi = aSt s₀ + BitVec.ofNat 32 408
  ecx : s'.gpr .ecx = BitVec.ofNat 32 (restOf (aC s₀) (aL s₀))

theorem rest_wp {s₀ s : State} (hp : APre s₀) (h : ACtx s₀ s)
    (hbp : s.gpr .ebp = BitVec.ofNat 32 (fOf (aC s₀) (aL s₀) + 8 * nbOf (aC s₀) (aL s₀))) :
    WP isa (.block rest) s (Rested s₀ s) := by
  obtain hsum := nb_le (aC s₀) (aL s₀)
  have hsum' : fOf (aC s₀) (aL s₀) + 8 * nbOf (aC s₀) (aL s₀) + restOf (aC s₀) (aL s₀) = (arg s₀ 4).toNat := hsum
  unfold rest
  refine h.wp_arg hp (by decide) (by decide) fun s₁ u₁ c₁ => wp_add fun s₂ u₂ =>
    (c₁.upd u₂ (by decide)).wp_arg hp (by decide) (by decide) fun s₃ u₃ c₃ => wp_addi fun s₄ u₄ =>
    (c₃.upd u₄ (by decide)).wp_arg hp (by decide) (by decide) fun s₅ u₅ c₅ => wp_sub fun s₆ u₆ _ => WP.block_nil ?_
  refine ⟨c₅.upd u₆ (by decide), by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem], ?_, ?_, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.gpr, u₁.other _ (by decide), hbp]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr]; rfl
  · rw [u₆.gpr, u₅.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hbp, arg_ofNat s₀ 4, sub_ofNat (by omega_arith)]
    exact congrArg (BitVec.ofNat 32) (by unfold restOf leftOf; omega_arith)

end VG.Proof.CmacTripleDes.Stream.X86

end

end

/-!
# Streaming TDEA-CMAC on x86: `vg_cmac_triple_des_absorb` around the runs of `update`

The code saves the registers, computes the bytes held back `h`, copies `f =
min(len, 8 - h)` bytes after them, and sets up the first run of `update`,
which chains the block held back if data is left (`AMid₁`); after each run,
what the code that follows needs (`AAft`), and what `chain2` leaves for the
second run (`AMid₂`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86

open VG VG.X86 VG.Impl.CmacTripleDes.Stream.X86

open VG.WriteBytes

open VG.Proof.CmacTripleDes.Stream (held held_le)

/-- The memory after the saves and the first copy. -/
def m4 (s₀ : State) : Mem :=
  writeBytes (savedMem s₀ (aSc s₀)) ((aSt s₀).setWidth 64 + BitVec.ofNat 64 (408 + held (aC s₀)))
    (Spec.Aes.bytesAt (savedMem s₀ (aSc s₀)) ((aD s₀).setWidth 64) (fOf (aC s₀) (aL s₀)))

theorem m4_frame (s₀ : State) :
    Frame [⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 (408 + held (aC s₀)), fOf (aC s₀) (aL s₀)⟩]
      (savedMem s₀ (aSc s₀)) (m4 s₀) :=
  writeBytes_frame _ _ _ (by rw [Proof.Cmac.bytesAt_length]; exact Region.contains_self _ _)

theorem m4_big {s₀ : State} (hp : APre s₀) : Frame (ABig s₀) s₀.mem (m4 s₀) := by
  have := f_le (aC s₀) (aL s₀)
  exact hp.savedMem_big.trans ((m4_frame s₀).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨astR s₀, by simp, Offset.sub_base _ (by omega_using [this])⟩)

/-- The save. -/
theorem absSave_wp {s₀ : State} (hp : APre s₀) :
    WP isa (.block absSave) s₀ fun s => ACtx s₀ s ∧ s.mem = savedMem s₀ (aSc s₀) := by
  have fS : (arg s₀ 5).toNat + 688 ≤ 2 ^ 32 := hp.fS
  rw [show absSave = .mov .eax (.mem (argOp 5)) :: (save ++ []) from rfl]
  refine wp_arg (s₀ := s₀) rfl (hp.arg_in (by decide)) rfl fun s₁ u₁ => ?_
  refine save_wp (Sc := aSc s₀) u₁.gpr fS (by
      rw [u₁.wr, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨ascR s₀, by simp, 0, by simp, by simp⟩)
    fun s₂ g₂ rd₂ wr₂ m₂ => WP.block_nil ?_
  have hm₂ : s₂.mem = savedMem s₀ (aSc s₀) := by
    rw [m₂, u₁.mem, savedMem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (saved_ne_eax p hp')
  exact ⟨ACtx.of_frame hp (by rw [g₂, u₁.other _ (by decide)]) (by rw [rd₂, u₁.rd]) (by rw [wr₂, u₁.wr])
    (hm₂ ▸ hp.savedMem_big), hm₂⟩

/-- What the code before the first run of `update` leaves. -/
structure AMid₁ (s₀ s : State) : Prop where
  args : UArgs s (aSt s₀) (aSt s₀ + BitVec.ofNat 32 400) (aSt s₀ + BitVec.ofNat 32 408) (aSc s₀)
    (b1Of (aC s₀) (aL s₀))
  ctx : ACtx s₀ s
  ebp : s.gpr .ebp = BitVec.ofNat 32 (fOf (aC s₀) (aL s₀))
  mem : s.mem = m4 s₀

theorem absorbPre_wp {s₀ : State} (hp : APre s₀) : WP isa absorbPre s₀ (AMid₁ s₀) := by
  have hL := hp.lt
  have ⟨hfL, hfh⟩ := f_le (aC s₀) (aL s₀)
  have fSt : (aSt s₀).toNat + 416 ≤ 2 ^ 32 := hp.fSt
  have fD : (aD s₀).toNat + aL s₀ ≤ 2 ^ 32 := hp.fD
  unfold absorbPre
  refine WP.seq (WP.mono (absSave_wp hp) fun s₁ ⟨c₁, m₁⟩ => ?_)
  refine WP.seq (held_ok (r := .eax) (by decide) (by decide) c₁.esp (by rw [c₁.rd, c₁.wr]; exact hp.arg_in (by decide))
    (by rw [c₁.rd, c₁.wr]; exact hp.arg_in (by decide)) (c₁.args 1 (by decide)) (c₁.args 2 (by decide))
    fun s₂ eax₂ g₂ m₂ rd₂ wr₂ => ?_)
  have c₂ : ACtx s₀ s₂ := ⟨by rw [g₂ _ (by decide) (by decide), c₁.esp], by rw [rd₂, c₁.rd], by rw [wr₂, c₁.wr],
    by rw [m₂]; exact c₁.args⟩
  refine WP.seq (WP.mono (fill_wp hp c₂ eax₂) fun s₃ h₃ => ?_)
  have p408 : 0 < fOf (aC s₀) (aL s₀) → (aSt s₀ + BitVec.ofNat 32 (408 + held (aC s₀))).setWidth 64 =
      (aSt s₀).setWidth 64 + BitVec.ofNat 64 (408 + held (aC s₀)) := fun _ => add_setWidth (by omega_arith)
  refine WP.seq (WP.mono (copy_wp (L := fOf (aC s₀) (aL s₀)) (by omega_using [hfh]) h₃.esi h₃.edi h₃.ecx (fun _ => by omega_using [hfL, fD])
    (fun _ => by rw [add_toNat (by omega_arith)]; omega_using [hfh, fSt])
    (fun _ => by
      rw [h₃.ctx.rd, h₃.ctx.wr, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨adR s₀, by simp, 0, by simp, by simp; omega_using [hfL]⟩)
    (fun h0 => by
      rw [h₃.ctx.wr, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨astR s₀, by simp, 408 + held (aC s₀), p408 h0, by simp; omega_using [hfh]⟩)
    (fun h0 => by
      rw [p408 h0]
      exact (hp.st_d.sub_left (Offset.sub_base (d := 408 + held (aC s₀)) (n := fOf (aC s₀) (aL s₀)) _
        (by omega_using [hfh]))).symm.sub_left (Region.sub_prefix hfL))) fun s₄ h₄ => ?_)
  obtain ⟨m₄, g₄, rd₄, wr₄⟩ := h₄
  have hm₄ : s₄.mem = m4 s₀ := by
    rw [m₄, h₃.mem, m₂, m₁, m4]
    by_cases hf0 : fOf (aC s₀) (aL s₀) = 0
    · rw [hf0]; simp only [Spec.Aes.bytesAt, List.range_zero, List.map_nil, writeBytes_nil]
    · rw [p408 (by omega_using [hf0])]
  have c₄ : ACtx s₀ s₄ := ACtx.of_frame hp (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), h₃.ctx.esp])
    (by rw [rd₄, h₃.ctx.rd]) (by rw [wr₄, h₃.ctx.wr]) (hm₄ ▸ m4_big hp)
  refine WP.mono (chain1_wp hp c₄ (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), h₃.ebp]))
    fun s₅ h₅ => ⟨h₅.args, h₅.ctx, by rw [h₅.ebp, g₄ _ (by decide) (by decide) (by decide) (by decide), h₃.ebp],
      by rw [h₅.mem, hm₄]⟩

/-! ## After the runs of `update` -/

/-- What is known after a run of `update`. -/
structure AAft (s₀ : State) (v : Nat) (s : State) : Prop where
  ctx : ACtx s₀ s
  ebp : s.gpr .ebp = BitVec.ofNat 32 v
  frame : Frame (ABig s₀) s₀.mem s.mem

/-- A run of `update` keeps `AAft`. -/
theorem upd_aft {s₀ s s' : State} (hp : APre s₀) {Dd : BitVec 32} {n v : Nat}
    (hf : Frame (ABig s₀) s₀.mem s.mem) (hc : ACtx s₀ s) (hbp : s.gpr .ebp = BitVec.ofNat 32 v)
    (h : UPost s (aSt s₀) (aSt s₀ + BitVec.ofNat 32 400) Dd (aSc s₀) n s') : AAft s₀ v s' := by
  have fSt : (aSt s₀).toNat + 416 ≤ 2 ^ 32 := hp.fSt
  have fr := h.frame
  rw [hc.esp, add_setWidth (by omega_using [fSt])] at fr
  have F : Frame (ABig s₀) s₀.mem s'.mem := hf.trans (fr.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨astR s₀, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨ascR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩)
  exact ⟨ACtx.of_frame hp (by rw [h.saved .esp (by simp [calleeSaved]), hc.esp]) (by rw [h.rd, hc.rd])
    (by rw [h.wr, hc.wr]) F, by rw [h.saved .ebp (by simp [calleeSaved]), hbp], F⟩

theorem upd1_after {s₀ s : State} (hp : APre s₀) (h : AMid₁ s₀ s) :
    WP isa updFrame s (AAft s₀ (fOf (aC s₀) (aL s₀))) :=
  WP.mono (upd_wp h.args) fun _ h' => upd_aft hp (h.mem ▸ m4_big hp) h.ctx h.ebp h'

/-- What `chain2` leaves, for the second run. -/
structure AMid₂ (s₀ s : State) : Prop where
  args : UArgs s (aSt s₀) (aSt s₀ + BitVec.ofNat 32 400) (d2Of s₀) (aSc s₀) (nbOf (aC s₀) (aL s₀))
  aft : AAft s₀ (fOf (aC s₀) (aL s₀) + 8 * nbOf (aC s₀) (aL s₀)) s

theorem chain2_mid {s₀ s : State} (hp : APre s₀) (h : AAft s₀ (fOf (aC s₀) (aL s₀)) s) :
    WP isa chain2 s fun s' => AMid₂ s₀ s' ∧ s'.mem = s.mem :=
  WP.mono (chain2_wp hp h.ctx h.ebp) fun _ h' => ⟨⟨h'.args, h'.ctx, h'.ebp, h'.mem ▸ h.frame⟩, h'.mem⟩

theorem upd2_after {s₀ s : State} (hp : APre s₀) (h : AMid₂ s₀ s) :
    WP isa updFrame s (AAft s₀ (fOf (aC s₀) (aL s₀) + 8 * nbOf (aC s₀) (aL s₀))) :=
  WP.mono (upd_wp h.args) fun _ h' => upd_aft hp h.aft.frame h.aft.ctx h.aft.ebp h'

end VG.Proof.CmacTripleDes.Stream.X86

end

end

/-!
# Streaming TDEA-CMAC on x86: `vg_cmac_triple_des_absorb` is correct

After `absorbPre`, the first run of `update` chains the block held back if
data is left (`b1`), the second the whole blocks of the data left but its
last 1 to 8 bytes (`nb`), and the last copy holds those back. If no data is
left (`len ≤ 8 - h`), the runs chain nothing and the copy copies nothing,
and the data is appended to the bytes held back (`repr_fill`); otherwise
`repr_chain`.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86

open VG VG.X86 VG.Impl.CmacTripleDes.Stream.X86

open VG.WriteBytes

open VG.Proof.CmacTripleDes.Stream (held held_le)
open VG.Proof.CmacTripleDes.X86 (ciphAt scheduleAt_frame)

theorem frame_at {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hp : p.toNat + n ≤ 2 ^ 64) {i : Nat} (hi : i < n) :
    m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  hf _ fun r hr hc => hd r hr _ (Offset.contains_base p (by omega_using [hi]) (by omega_using [hp, hi])) hc

theorem blocksAt_zero (m : Mem) (p : Addr) : Spec.Cmac.blocksAt m p 8 0 = [] := rfl

theorem blocksAt_one (m : Mem) (p : Addr) :
    Spec.Cmac.blocksAt m p 8 1 = [Spec.Aes.bytesAt m p 8] := by
  simp [Spec.Cmac.blocksAt, k0]
where k0 : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

theorem bytesAt_zero (m : Mem) (p : Addr) : Spec.Aes.bytesAt m p 0 = [] := rfl

theorem absorb_wp {s₀ : State} (h0 : absorbX86.pre s₀) :
    WP isa absorb s₀ fun s' => abiPreserved s₀ s' ∧ absorbX86.post s₀ s' := by
  obtain hp := APre.of h0
  have hL := hp.lt
  have fSt : (aSt s₀).toNat + 416 ≤ 2 ^ 32 := hp.fSt
  have fD : (aD s₀).toNat + aL s₀ ≤ 2 ^ 32 := hp.fD
  have fS : (aSc s₀).toNat + 688 ≤ 2 ^ 32 := hp.fS
  have e24 := hp.esp24
  have ⟨hfL, hfh⟩ := f_le (aC s₀) (aL s₀)
  obtain hsum := nb_le (aC s₀) (aL s₀)
  obtain hrr := rest_le (aC s₀) (aL s₀)
  obtain hh := held_le (aC s₀)
  unfold absorb
  refine WP.seq (WP.mono (absorbPre_wp hp) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (upd_wp h₅.args) fun s₆ h₆ => ?_)
  obtain a₆ := upd_aft hp (h₅.mem ▸ m4_big hp) h₅.ctx h₅.ebp h₆
  refine WP.seq (WP.mono (chain2_mid hp a₆) fun s₇ ⟨h₇, m₇⟩ => ?_)
  refine WP.seq (WP.mono (upd_wp h₇.args) fun s₈ h₈ => ?_)
  obtain a₈ := upd_aft hp h₇.aft.frame h₇.aft.ctx h₇.aft.ebp h₈
  unfold absorbPost
  refine WP.seq (WP.mono (rest_wp hp a₈.ctx a₈.ebp) fun s₉ h₉ => ?_)
  -- The last copy.
  obtain hsrc : 0 < restOf (aC s₀) (aL s₀) →
      (aD s₀ + BitVec.ofNat 32 (fOf (aC s₀) (aL s₀) + 8 * nbOf (aC s₀) (aL s₀))).setWidth 64 =
        (aD s₀).setWidth 64 + BitVec.ofNat 64 (fOf (aC s₀) (aL s₀) + 8 * nbOf (aC s₀) (aL s₀)) :=
    fun _ => add_setWidth (by omega_arith)
  obtain p408 : (aSt s₀ + BitVec.ofNat 32 408).setWidth 64 = (aSt s₀).setWidth 64 + BitVec.ofNat 64 408 :=
    add_setWidth (by omega_using [fSt])
  refine WP.seq (WP.mono (copy_wp (L := restOf (aC s₀) (aL s₀)) (by omega_using [hrr]) h₉.esi h₉.edi h₉.ecx
    (fun _ => by rw [add_toNat (by omega_arith)]; omega_using [fD, hsum]) (fun _ => by rw [add_toNat (by omega_using [fSt])]; omega_using [fSt, hrr])
    (fun h => by
      rw [h₉.ctx.rd, h₉.ctx.wr, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨adR s₀, by simp, _, hsrc h, by simp; omega_using [hsum]⟩)
    (fun _ => by
      rw [h₉.ctx.wr, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨astR s₀, by simp, 408, p408, by simp; omega_using [hrr]⟩)
    (fun h => by
      rw [hsrc h, p408]
      exact (hp.st_d.sub_left (Offset.sub_base (d := 408) (n := restOf (aC s₀) (aL s₀)) _ (by omega_using [hrr]))).symm.sub_left
        (Offset.sub_base (d := fOf (aC s₀) (aL s₀) + 8 * nbOf (aC s₀) (aL s₀)) (n := restOf (aC s₀) (aL s₀)) _
          (by omega_using [hsum])))) fun s₁₀ h₁₀ => ?_)
  obtain ⟨m₁₀, g₁₀, rd₁₀, wr₁₀⟩ := h₁₀
  -- The frames.
  obtain f6 : Frame [⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 400, 8⟩, ⟨(aSc s₀).setWidth 64, 640⟩,
      below (aE s₀) 24] s₅.mem s₆.mem := by
    have := h₆.frame; rw [h₅.ctx.esp, add_setWidth (by omega_using [fSt])] at this; exact this
  obtain f8 : Frame [⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 400, 8⟩, ⟨(aSc s₀).setWidth 64, 640⟩,
      below (aE s₀) 24] s₆.mem s₈.mem := by
    have := h₈.frame; rw [h₇.aft.ctx.esp, add_setWidth (by omega_using [fSt]), m₇] at this; exact this
  obtain m₁₀' : s₁₀.mem = writeBytes s₈.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 408)
      (Spec.Aes.bytesAt s₈.mem ((aD s₀).setWidth 64 + BitVec.ofNat 64 (fOf (aC s₀) (aL s₀) + 8 * nbOf (aC s₀) (aL s₀)))
        (restOf (aC s₀) (aL s₀))) := by
    rw [m₁₀, h₉.mem, p408]
    by_cases hr0 : restOf (aC s₀) (aL s₀) = 0
    · rw [hr0, bytesAt_zero, bytesAt_zero]
    · rw [hsrc (by omega_using [hr0])]
  obtain hlr : (Spec.Aes.bytesAt s₈.mem ((aD s₀).setWidth 64 + BitVec.ofNat 64 (fOf (aC s₀) (aL s₀) +
      8 * nbOf (aC s₀) (aL s₀))) (restOf (aC s₀) (aL s₀))).length = restOf (aC s₀) (aL s₀) :=
    Proof.Cmac.bytesAt_length _ _ _
  obtain fC2 : Frame [⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 408, restOf (aC s₀) (aL s₀)⟩] s₈.mem s₁₀.mem := by
    rw [m₁₀']; exact writeBytes_frame _ _ _ (by rw [hlr]; exact Region.contains_self _ _)
  obtain fSv : Frame [⟨(aSc s₀).setWidth 64 + BitVec.ofNat 64 640, 16⟩] s₀.mem (savedMem s₀ (aSc s₀)) :=
    savedMem_frame _ _
  obtain fC1 : Frame [⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 (408 + held (aC s₀)), fOf (aC s₀) (aL s₀)⟩]
      (savedMem s₀ (aSc s₀)) s₅.mem := by rw [h₅.mem]; exact m4_frame s₀
  let K : List Region := [⟨(aSc s₀).setWidth 64 + BitVec.ofNat 64 640, 16⟩,
    ⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 (408 + held (aC s₀)), fOf (aC s₀) (aL s₀)⟩,
    ⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 400, 8⟩, ⟨(aSc s₀).setWidth 64, 640⟩, below (aE s₀) 24,
    ⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 408, restOf (aC s₀) (aL s₀)⟩]
  obtain F5 : Frame K s₀.mem s₅.mem := (fSv.mono (by simp [K])).trans (fC1.mono (by simp [K]))
  obtain F6 : Frame K s₀.mem s₆.mem := F5.trans (f6.mono (by simp [K]))
  obtain F8 : Frame K s₀.mem s₈.mem := F6.trans (f8.mono (by simp [K]))
  obtain F10 : Frame K s₀.mem s₁₀.mem := F8.trans (fC2.mono (by simp [K]))
  obtain KB : Frame (ABig s₀) s₀.mem s₁₀.mem := F10.sub fun r hr => by
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ascR s₀, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨astR s₀, by simp, Offset.sub_base _ (by omega_using [hfh])⟩
    · exact ⟨astR s₀, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨ascR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨astR s₀, by simp, Offset.sub_base _ (by omega_using [hrr])⟩
  -- The saved registers.
  obtain slots : ∀ r d, (r, d) ∈ saved →
      s₁₀.mem.readW ((aSc s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r := fun r d hrd => by
    obtain hb := saved_bound _ hrd
    obtain Fp : Frame K.tail (savedMem s₀ (aSc s₀)) s₁₀.mem :=
      ((fC1.mono (by simp [K])).trans (f6.mono (by simp [K]))).trans
        ((f8.mono (by simp [K])).trans (fC2.mono (by simp [K])))
    obtain sub : Region.Sub ⟨(aSc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩ (ascR s₀) := Offset.sub_base _ (by omega_using [hb])
    rw [Fp.readW (Region.contains_self _ _) (fun q hq => ?_) (by decide)]
    · exact saveMem_slot _ _ _ hrd
    simp only [K, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Offset.sub_base _ (by omega_using [hfh]))).symm.sub_left sub
    · exact (hp.st_s.sub_left (Offset.sub_base _ (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base _ (by omega_using [hb]) (by omega_using [hb])
    · exact hp.b_s.symm.sub_left sub
    · exact (hp.st_s.sub_left (Offset.sub_base _ (by omega_using [hrr]))).symm.sub_left sub
  obtain esp₁₀ : s₁₀.gpr .esp = aE s₀ := by
    rw [g₁₀ _ (by decide) (by decide) (by decide) (by decide), h₉.ctx.esp]
  refine WP.mono (restore_wp (s₀ := s₀) (i := 5) (Sc := aSc s₀) esp₁₀
    (by rw [rd₁₀, wr₁₀, h₉.ctx.rd, h₉.ctx.wr]; exact hp.arg_in (by decide)) (hp.keep KB (by decide)) fS (by
      rw [rd₁₀, wr₁₀, h₉.ctx.rd, h₉.ctx.wr, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨ascR s₀, by simp, 0, by simp, by simp⟩) slots)
    fun s₁₁ ⟨hcs, m₁₁⟩ => ?_
  obtain F11 : Frame K s₀.mem s₁₁.mem := m₁₁ ▸ F10
  -- The key, the data and the return address are in none of these.
  obtain dK : ∀ r ∈ K, (⟨(aSt s₀).setWidth 64, 400⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
    · exact Offset.base_disjoint _ (by omega_using []) (by omega_using [hfh])
    · exact Offset.base_disjoint _ (by omega_using []) (by omega_using [])
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    · exact (hp.b_st.sub_right (Region.sub_prefix (by decide))).symm
    · exact Offset.base_disjoint _ (by omega_using []) (by omega_using [hrr])
  obtain dDat : ∀ r ∈ K, (adR s₀).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp.d_s.sub_right (Offset.sub_base _ (by decide))
    · exact hp.st_d.symm.sub_right (Offset.sub_base _ (by omega_using [hfh]))
    · exact hp.st_d.symm.sub_right (Offset.sub_base _ (by decide))
    · exact hp.d_s.sub_right (Region.sub_prefix (by decide))
    · exact hp.b_d.symm
    · exact hp.st_d.symm.sub_right (Offset.sub_base _ (by omega_using [hrr]))
  obtain dRet : ∀ r ∈ K, (⟨(aE s₀).setWidth 64, 4⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp.ret_s.sub_right (Offset.sub_base _ (by decide))
    · exact hp.ret_st.sub_right (Offset.sub_base _ (by omega_using [hfh]))
    · exact hp.ret_st.sub_right (Offset.sub_base _ (by decide))
    · exact hp.ret_s.sub_right (Region.sub_prefix (by decide))
    · exact ret_below e24
    · exact hp.ret_st.sub_right (Offset.sub_base _ (by omega_using [hrr]))
  refine ⟨⟨hcs, F11.readW (r := ⟨(aE s₀).setWidth 64, 4⟩) (Region.contains_self _ _) dRet (by decide)⟩, ?_⟩
  intro key msg hr hcnt hlen
  show Spec.Cmac.tdesRepr s₁₁.mem ((aSt s₀).setWidth 64) key
    (msg ++ Spec.Aes.bytesAt s₀.mem ((aD s₀).setWidth 64) (aL s₀))
  obtain hcm : aC s₀ = msg.length := by
    show (countX86 s₀).toNat = _
    rw [hcnt, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hlen])
  obtain hsch := ((Proof.CmacTripleDes.Stream.repr_iff _ _ _ _).mp hr).1.2.1
  obtain ciph : ∀ m : Mem, Frame K s₀.mem m → ciphAt m ((aSt s₀).setWidth 64) = Spec.Cmac.tdes key := fun m hf => by
    simp only [ciphAt, Spec.Cmac.tdes]
    rw [scheduleAt_frame hf fun r hr => (dK r hr).sub_left (Region.sub_prefix (by decide)), hsch]
  -- The data, wherever it is read.
  obtain dat : ∀ m : Mem, Frame K s₀.mem m → ∀ a b : Nat, a + b ≤ aL s₀ →
      Spec.Aes.bytesAt m ((aD s₀).setWidth 64 + BitVec.ofNat 64 a) b =
        ((Spec.Aes.bytesAt s₀.mem ((aD s₀).setWidth 64) (aL s₀)).drop a).take b := fun m hf a b hab => by
    rw [Proof.Cmac.Stream.bytesAt_offset m _ hab, Proof.Cmac.bytesAt_frame hf dDat (by omega_using [fD])]
  obtain fS' : Frame K s₀.mem (savedMem s₀ (aSc s₀)) := fSv.mono (by simp [K])
  -- The chaining value.
  obtain cv5 : Spec.Aes.bytesAt s₅.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 400) 8 =
      Spec.Aes.bytesAt s₀.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 400) 8 := by
    rw [Proof.Cmac.bytesAt_frame fC1 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega_using []) (by omega_using []) (by omega_using [hfh]))
        (by decide),
      Proof.Cmac.bytesAt_frame fSv (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.st_s.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ (by decide)))
        (by decide)]
  obtain cv11 : Spec.Aes.bytesAt s₁₁.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 400) 8 =
      Spec.Aes.bytesAt s₈.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 400) 8 := by
    rw [m₁₁]
    exact Proof.Cmac.bytesAt_frame fC2 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega_using []) (by omega_using []) (by omega_using [hrr]))
      (by decide)
  have out6 := h₆.out
  rw [add_setWidth (by omega_using [fSt]), add_setWidth (by omega_using [fSt]), ciph _ F5] at out6
  have out8 := h₈.out
  rw [add_setWidth (by omega_using [fSt]), m₇, ciph _ F6] at out8
  obtain hk : ∀ i < 400, s₁₁.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 i) =
      s₀.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 i) :=
    fun i hi => frame_at F11 dK (by simp only [BitVec.toNat_setWidth]; omega_using []) hi
  obtain hdl : (Spec.Aes.bytesAt s₀.mem ((aD s₀).setWidth 64) (aL s₀)).length = aL s₀ :=
    Proof.Cmac.bytesAt_length _ _ _
  obtain hlf : (Spec.Aes.bytesAt (savedMem s₀ (aSc s₀)) ((aD s₀).setWidth 64) (fOf (aC s₀) (aL s₀))).length =
      fOf (aC s₀) (aL s₀) := Proof.Cmac.bytesAt_length _ _ _
  -- The bytes held back so far, and the first `f` bytes of data after them.
  obtain hb5 : Spec.Aes.bytesAt s₅.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 408)
      (held (aC s₀) + fOf (aC s₀) (aL s₀)) =
      Spec.Aes.bytesAt s₀.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 408) (held (aC s₀)) ++
        (Spec.Aes.bytesAt s₀.mem ((aD s₀).setWidth 64) (aL s₀)).take (fOf (aC s₀) (aL s₀)) := by
    obtain e := bytesAt_writeBytes (savedMem s₀ (aSc s₀)) ((aSt s₀).setWidth 64 + BitVec.ofNat 64 408) (held (aC s₀))
      (Spec.Aes.bytesAt (savedMem s₀ (aSc s₀)) ((aD s₀).setWidth 64) (fOf (aC s₀) (aL s₀))) (by rw [hlf]; omega_using [hfh])
    rw [hlf] at e
    rw [h₅.mem, m4, ← Offset.add_add, e,
      Proof.Cmac.bytesAt_frame fSv (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.st_s.sub_left (Offset.sub_base _ (by omega_using [hh]))).sub_right (Offset.sub_base _ (by decide)))
        (by omega_using [hh])]
    refine congrArg (_ ++ ·) ?_
    have := dat _ fS' 0 (fOf (aC s₀) (aL s₀)) (by omega_using [hsum])
    rwa [BitVec.add_zero, List.drop_zero] at this
  generalize hd : Spec.Aes.bytesAt s₀.mem ((aD s₀).setWidth 64) (aL s₀) = d at hdl hb5 dat ⊢
  by_cases hx : leftOf (aC s₀) (aL s₀) = 0
  · -- Everything fits in the block held back.
    obtain hfL' : fOf (aC s₀) (aL s₀) = aL s₀ := by unfold leftOf at hx; omega_using [hsum, hx]
    obtain hb : b1Of (aC s₀) (aL s₀) = 0 := by simp [b1Of, hx]
    obtain hn : nbOf (aC s₀) (aL s₀) = 0 := by simp [nbOf, hx]
    obtain hr0 : restOf (aC s₀) (aL s₀) = 0 := rest_zero hx
    obtain m118 : s₁₁.mem = s₈.mem := by
      rw [m₁₁, m₁₀', hr0, bytesAt_zero, writeBytes_nil]
    refine Proof.CmacTripleDes.Stream.repr_fill hr hk (by rw [hdl, ← hcm]; omega_using [hfh, hfL']) ?_ ?_
    · show Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 400) _ =
        Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 400) _
      rw [cv11, out8, hn, blocksAt_zero, out6, hb, blocksAt_zero]
      exact cv5
    · show Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 408) _ =
        Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 408) _ ++ _
      rw [← hcm, hdl]
      obtain sub : Region.Sub ⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 408, held (aC s₀) + aL s₀⟩ (astR s₀) :=
        Offset.sub_base _ (by omega_using [hfh, hfL'])
      obtain dj : ∀ r ∈ [⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 400, 8⟩, ⟨(aSc s₀).setWidth 64, 640⟩,
          below (aE s₀) 24], (⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 408, held (aC s₀) + aL s₀⟩ : Region).Disjoint r := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.disjoint _ (by omega_using []) (by omega_using [hfh, hfL']) (by omega_using [])
        · exact (hp.st_s.sub_left sub).sub_right (Region.sub_prefix (by decide))
        · exact (hp.b_st.sub_right sub).symm
      have hb5' := hb5
      rw [hfL', List.take_of_length_le (by rw [hdl])] at hb5'
      rw [m118, Proof.Cmac.bytesAt_frame f8 dj (by omega_using [hfh, hfL']), Proof.Cmac.bytesAt_frame f6 dj (by omega_using [hfh, hfL']), hb5']
  · -- The block held back is complete, and more blocks may follow.
    obtain hlt : 8 - held (aC s₀) < aL s₀ := by unfold leftOf fOf at hx; omega_using [hx]
    obtain hf' : fOf (aC s₀) (aL s₀) = 8 - held (aC s₀) := by unfold fOf; omega_using [hlt]
    obtain hb : b1Of (aC s₀) (aL s₀) = 1 := by simp [b1Of, hx]
    obtain hn : nbOf (aC s₀) (aL s₀) = Proof.CmacTripleDes.Stream.nblocks (aC s₀) (aL s₀) := by
      simp only [nbOf, hx, ↓reduceIte]
      unfold leftOf Proof.CmacTripleDes.Stream.nblocks
      rw [hf']
    obtain hd2 : (d2Of s₀).setWidth 64 = (aD s₀).setWidth 64 + BitVec.ofNat 64 (fOf (aC s₀) (aL s₀)) := by
      simp only [d2Of, hx, ↓reduceIte]; exact add_setWidth (by omega_using [fD, hlt, hf'])
    have hb5' := hb5
    rw [hf', Nat.add_sub_cancel' hh] at hb5'
    refine Proof.CmacTripleDes.Stream.repr_chain hr hk (by rw [hdl, ← hcm]; exact hlt) ?_ ?_
    · show Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 400) _ =
        Spec.Cmac.chain _ (Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 400) _)
          ([Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 408) _ ++ _] ++ _)
      rw [← hcm, hdl]
      rw [cv11, out8, out6, hb, blocksAt_one, cv5, Proof.Cmac.chain_append, hd2, Proof.CmacTripleDes.Stream.blocksAt_eq,
        dat _ F6 _ _ (by omega_using [hsum]), hb5', hf', hn]
    · show Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 408) _ = _
      rw [← hcm, hdl]
      obtain e := bytesAt_writeBytes_self s₈.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 408)
        (xs := Spec.Aes.bytesAt s₈.mem ((aD s₀).setWidth 64 + BitVec.ofNat 64 (fOf (aC s₀) (aL s₀) +
          8 * nbOf (aC s₀) (aL s₀))) (restOf (aC s₀) (aL s₀))) (by rw [hlr]; omega_using [hrr])
      rw [hlr] at e
      obtain hr' : aL s₀ - (8 - held (aC s₀)) - 8 * Proof.CmacTripleDes.Stream.nblocks (aC s₀) (aL s₀) =
          restOf (aC s₀) (aL s₀) := by
        rw [← hn, ← hf']; rfl
      rw [hr', m₁₁, m₁₀', e, dat _ F8 _ _ (by omega_using [hsum]),
        List.take_of_length_le (by simp only [List.length_drop, hdl]; unfold restOf leftOf; omega_using []),
        List.drop_drop, ← hn, hf']

end VG.Proof.CmacTripleDes.Stream.X86

end

end

/-! ### `CmacTripleDes.Stream.X86.Finish`, which only this module used -/

section

/-!
# Streaming TDEA-CMAC on x86: `vg_cmac_triple_des_finish`

The code saves the registers, copies the chaining value to `out`, computes
the number of bytes held back, and runs `finalize` with the state as its key
and `out` as its state: its result is the MAC of the message the state
represents (`repr_finish`). The code before the run is constant time by the
taint analysis, and the run by `finalize`'s own proof (`fin_rel`), its
arguments pinned by `HMid`.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86

open VG VG.X86 VG.Impl.CmacTripleDes.Stream.X86

open VG.WriteBytes

open VG.Impl.CmacTripleDes.X86 (at_)
open VG.Proof.MdStream.X86 (Upd wp_mov wp_movi wp_addi)
open VG.Proof.CmacTripleDes.X86 (ciphAt)
open VG.Proof.CmacTripleDes.Stream (held held_le)

section
variable (s₀ : State)

abbrev hSt : BitVec 32 := arg s₀ 0
abbrev hO : BitVec 32 := arg s₀ 3
abbrev hSc : BitVec 32 := arg s₀ 4
abbrev hE : BitVec 32 := s₀.gpr .esp
abbrev hstR : Region := ⟨(hSt s₀).setWidth 64, 416⟩
abbrev hoR : Region := ⟨(hO s₀).setWidth 64, 8⟩
abbrev hscR : Region := ⟨(hSc s₀).setWidth 64, 688⟩
abbrev haR : Region := ⟨argAddr s₀ 0, 20⟩
/-- The bytes held back. -/
abbrev hH : Nat := held (countX86 s₀).toNat

/-- Where the function writes: the state, `out`, the scratch buffer and the stack. -/
abbrev HBig : List Region := [hstR s₀, hoR s₀, hscR s₀, below (hE s₀) 24]

end

/-- The precondition, by name. -/
structure HPre (s₀ : State) : Prop where
  rd : s₀.rd = [haR s₀]
  wr : s₀.wr = [hstR s₀, hoR s₀, hscR s₀]
  st_o : (hstR s₀).Disjoint (hoR s₀)
  st_s : (hstR s₀).Disjoint (hscR s₀)
  o_s : (hoR s₀).Disjoint (hscR s₀)
  a_st : (haR s₀).Disjoint (hstR s₀)
  a_o : (haR s₀).Disjoint (hoR s₀)
  a_s : (haR s₀).Disjoint (hscR s₀)
  ret_st : (⟨(hE s₀).setWidth 64, 4⟩ : Region).Disjoint (hstR s₀)
  ret_o : (⟨(hE s₀).setWidth 64, 4⟩ : Region).Disjoint (hoR s₀)
  ret_s : (⟨(hE s₀).setWidth 64, 4⟩ : Region).Disjoint (hscR s₀)
  b_st' : (⟨(hE s₀).setWidth 64 - BitVec.ofNat 64 24, 24⟩ : Region).Disjoint (hstR s₀)
  b_o' : (⟨(hE s₀).setWidth 64 - BitVec.ofNat 64 24, 24⟩ : Region).Disjoint (hoR s₀)
  b_s' : (⟨(hE s₀).setWidth 64 - BitVec.ofNat 64 24, 24⟩ : Region).Disjoint (hscR s₀)
  fSt : (hSt s₀).toNat + 416 ≤ 2 ^ 32
  fO : (hO s₀).toNat + 8 ≤ 2 ^ 32
  fS : (hSc s₀).toNat + 688 ≤ 2 ^ 32
  esp24 : 24 ≤ (hE s₀).toNat
  espfit : (hE s₀).toNat + 24 ≤ 2 ^ 32

theorem HPre.of {s₀ : State} (h : finishX86.pre s₀) : HPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t⟩

namespace HPre
variable {s₀ : State} (hp : HPre s₀)
include hp

theorem b_st : (below (hE s₀) 24).Disjoint (hstR s₀) := by rw [below_eq hp.esp24]; exact hp.b_st'
theorem b_o : (below (hE s₀) 24).Disjoint (hoR s₀) := by rw [below_eq hp.esp24]; exact hp.b_o'
theorem b_s : (below (hE s₀) 24).Disjoint (hscR s₀) := by rw [below_eq hp.esp24]; exact hp.b_s'

theorem fit : (s₀.gpr .esp).toNat + 4 + 4 * 5 ≤ 2 ^ 32 := by have := hp.espfit; omega_arith

theorem arg_in {i : Nat} (hi : i < 5) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 :=
  ⟨haR s₀, by simp [hp.rd], arg_contains hp.fit hi⟩

/-- The stack arguments are unchanged where only `HBig` changes. -/
theorem keep {m : Mem} (hf : Frame (HBig s₀) s₀.mem m) {i : Nat} (hi : i < 5) :
    m.readW (argAddr s₀ i) 32 = arg s₀ i :=
  arg_keep hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.a_st.sub_left (arg_sub hp.fit hi)
    · exact hp.a_o.sub_left (arg_sub hp.fit hi)
    · exact hp.a_s.sub_left (arg_sub hp.fit hi)
    · exact (args_below hp.fit (by decide) hp.esp24).symm.sub_left (arg_sub hp.fit hi)

theorem argsOut : ArgsOut 5 s₀ := by
  refine ⟨by have := hp.espfit; omega_arith, ?_⟩
  rw [hp.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 20) (by have := hp.espfit; omega_arith) hp.ret_st hp.a_st
  · exact VG.X86.Taint.frame_disjoint (n := 20) (by have := hp.espfit; omega_arith) hp.ret_o hp.a_o
  · exact VG.X86.Taint.frame_disjoint (n := 20) (by have := hp.espfit; omega_arith) hp.ret_s hp.a_s

end HPre

theorem HPre.savedMem_big {s₀ : State} (_hp : HPre s₀) : Frame (HBig s₀) s₀.mem (savedMem s₀ (hSc s₀)) :=
  (savedMem_frame _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨hscR s₀, by simp, Offset.sub_base _ (by decide)⟩

/-! ## Before `finalize` -/

theorem finSave_eq : finSave = .mov .eax (.mem (argOp 4)) :: (save ++ ([.mov .esi (.mem (argOp 0)),
    .alu .add .esi (.imm 400), .mov .edi (.mem (argOp 3)), .mov .ecx (.imm 8)] : List Instr)) := rfl

/-- What `finSave` leaves. -/
structure HS₁ (s₀ s : State) : Prop where
  esi : s.gpr .esi = hSt s₀ + BitVec.ofNat 32 400
  edi : s.gpr .edi = hO s₀
  ecx : s.gpr .ecx = BitVec.ofNat 32 8
  esp : s.gpr .esp = hE s₀
  mem : s.mem = savedMem s₀ (hSc s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem finSave_wp {s₀ : State} (hp : HPre s₀) : WP isa (.block finSave) s₀ (HS₁ s₀) := by
  have fS : (arg s₀ 4).toNat + 688 ≤ 2 ^ 32 := hp.fS
  rw [finSave_eq]
  refine wp_arg (s₀ := s₀) rfl (hp.arg_in (by decide)) rfl fun s₁ u₁ => ?_
  refine save_wp (Sc := hSc s₀) u₁.gpr fS (by
      rw [u₁.wr, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨hscR s₀, by simp, 0, by simp, by simp⟩)
    fun s₂ g₂ rd₂ wr₂ m₂ => ?_
  obtain hm₂ : s₂.mem = savedMem s₀ (hSc s₀) := by
    rw [m₂, u₁.mem, savedMem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (saved_ne_eax p hp')
  obtain esp₂ : s₂.gpr .esp = hE s₀ := by rw [g₂, u₁.other _ (by decide)]
  obtain rd₂' : s₂.rd = s₀.rd := by rw [rd₂, u₁.rd]
  obtain wr₂' : s₂.wr = s₀.wr := by rw [wr₂, u₁.wr]
  obtain av : ∀ i < 5, s₂.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => by
    rw [hm₂]; exact hp.keep hp.savedMem_big hi
  refine wp_arg (s₀ := s₀) esp₂ (by rw [rd₂', wr₂']; exact hp.arg_in (by decide)) (av 0 (by decide))
    fun s₃ u₃ => wp_addi fun s₄ u₄ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₄.other _ (by decide), u₃.other _ (by decide), esp₂])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂', wr₂']; exact hp.arg_in (by decide))
    (by rw [u₄.mem, u₃.mem]; exact av 3 (by decide)) fun s₅ u₅ => wp_movi fun s₆ u₆ => WP.block_nil ?_
  exact ⟨by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr]; rfl,
    by rw [u₆.other _ (by decide), u₅.gpr], u₆.gpr,
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), esp₂],
    by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, hm₂], by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂'],
    by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂']⟩

/-- The memory after the saves and the copy of the chaining value. -/
def hMem (s₀ : State) : Mem :=
  writeBytes (savedMem s₀ (hSc s₀)) ((hO s₀).setWidth 64)
    (Spec.Aes.bytesAt (savedMem s₀ (hSc s₀)) ((hSt s₀).setWidth 64 + BitVec.ofNat 64 400) 8)

theorem hMem_out (s₀ : State) : Frame [hoR s₀] (savedMem s₀ (hSc s₀)) (hMem s₀) :=
  writeBytes_frame _ _ _ (R := hoR s₀) (by rw [Proof.Cmac.bytesAt_length]; exact Region.contains_self _ _)

theorem hMem_frame {s₀ : State} (hp : HPre s₀) : Frame (HBig s₀) s₀.mem (hMem s₀) :=
  hp.savedMem_big.trans ((hMem_out s₀).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨hoR s₀, by simp, fun _ h => h⟩)

/-- What the code before `finalize` leaves. -/
structure HMid (s₀ s : State) : Prop where
  args : FArgs s (hSt s₀) (hO s₀) (hSt s₀ + BitVec.ofNat 32 408) (hSc s₀) (hH s₀)
  esp : s.gpr .esp = hE s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = hMem s₀

theorem finPre_wp {s₀ : State} (hp : HPre s₀) : WP isa finPre s₀ (HMid s₀) := by
  have fS : (arg s₀ 4).toNat + 688 ≤ 2 ^ 32 := hp.fS
  have fSt : (arg s₀ 0).toNat + 416 ≤ 2 ^ 32 := hp.fSt
  have fO : (arg s₀ 3).toNat + 8 ≤ 2 ^ 32 := hp.fO
  have fSt₂ : (hSt s₀).toNat + 416 ≤ 2 ^ 32 := hp.fSt
  have fO₂ : (hO s₀).toNat + 8 ≤ 2 ^ 32 := hp.fO
  have fS₂ : (hSc s₀).toNat + 688 ≤ 2 ^ 32 := hp.fS
  have e24 := hp.esp24
  unfold finPre
  refine WP.seq (WP.mono (finSave_wp hp) fun s₁ h₁ => ?_)
  obtain p400 : ((hSt s₀ + BitVec.ofNat 32 400).setWidth 64) = (hSt s₀).setWidth 64 + BitVec.ofNat 64 400 :=
    add_setWidth (by omega_arith)
  obtain c400 : Region.Sub ⟨(hSt s₀ + BitVec.ofNat 32 400).setWidth 64, 8⟩ (hstR s₀) := by
    rw [p400]; exact Offset.sub_base _ (by decide)
  refine WP.seq (WP.mono (copy_wp (L := 8) (by decide) h₁.esi h₁.edi h₁.ecx
    (fun _ => by rw [add_toNat (by omega_arith)]; omega_arith) (fun _ => by omega_arith)
    (fun _ => by
      rw [h₁.rd, h₁.wr, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨hstR s₀, by simp, 400, p400, by simp⟩)
    (fun _ => by
      rw [h₁.wr, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨hoR s₀, by simp, 0, by simp, by simp⟩)
    (fun _ => hp.st_o.sub_left c400)) fun s₂ h₂ => ?_)
  obtain ⟨m₂, g₂, rd₂, wr₂⟩ := h₂
  obtain hm₂ : s₂.mem = hMem s₀ := by rw [m₂, h₁.mem, p400]; rfl
  obtain esp₂ : s₂.gpr .esp = hE s₀ := by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), h₁.esp]
  obtain rd₂' : s₂.rd = s₀.rd := by rw [rd₂, h₁.rd]
  obtain wr₂' : s₂.wr = s₀.wr := by rw [wr₂, h₁.wr]
  obtain av : ∀ i < 5, s₂.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => by
    rw [hm₂]; exact hp.keep (hMem_frame hp) hi
  refine WP.seq (held_ok (r := .esi) (by decide) (by decide) esp₂ (by rw [rd₂', wr₂']; exact hp.arg_in (by decide))
    (by rw [rd₂', wr₂']; exact hp.arg_in (by decide)) (av 1 (by decide)) (av 2 (by decide))
    fun s₃ esi₃ g₃ m₃ rd₃ wr₃ => ?_)
  obtain esp₃ : s₃.gpr .esp = hE s₀ := by rw [g₃ _ (by decide) (by decide), esp₂]
  obtain rw₃ : s₃.rd ++ s₃.wr = s₀.rd ++ s₀.wr := by rw [rd₃, wr₃, rd₂', wr₂']
  obtain av₃ : ∀ i < 5, s₃.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => by rw [m₃]; exact av i hi
  unfold finArgs
  refine wp_arg (s₀ := s₀) esp₃ (by rw [rw₃]; exact hp.arg_in (by decide)) (av₃ 0 (by decide)) fun s₄ u₄ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₄.other _ (by decide), esp₃])
    (by rw [u₄.rd, u₄.wr, rw₃]; exact hp.arg_in (by decide)) (by rw [u₄.mem]; exact av₃ 3 (by decide))
    fun s₅ u₅ => wp_mov fun s₆ u₆ => wp_addi fun s₇ u₇ => ?_
  refine wp_arg (s₀ := s₀)
    (by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), esp₃])
    (by rw [u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, rw₃]; exact hp.arg_in (by decide))
    (by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem]; exact av₃ 4 (by decide)) fun s₈ u₈ => WP.block_nil ?_
  obtain esp₈ : s₈.gpr .esp = hE s₀ := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), esp₃]
  obtain rd₈ : s₈.rd = s₀.rd := by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃, rd₂']
  obtain wr₈ : s₈.wr = s₀.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃, wr₂']
  obtain m₈ : s₈.mem = hMem s₀ := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃, hm₂]
  obtain hh : hH s₀ ≤ 8 := held_le (countX86 s₀).toNat
  obtain p408 : ((hSt s₀ + BitVec.ofNat 32 408).setWidth 64) = (hSt s₀).setWidth 64 + BitVec.ofNat 64 408 :=
    add_setWidth (by omega_arith)
  obtain cP : Region.Sub ⟨(hSt s₀ + BitVec.ofNat 32 408).setWidth 64, hH s₀⟩ (hstR s₀) := by
    rw [p408]; exact Offset.sub_base _ (by omega_arith)
  refine ⟨?_, esp₈, rd₈, wr₈, m₈⟩
  exact
  { eax := by
      rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]
    edx := by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
    ebx := by rw [u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.gpr]; rfl
    esi := by
      rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), esi₃]
    edi := u₈.gpr
    len := hh
    esp := by rw [esp₈]; exact e24
    kst := hp.st_o.sub_left (Region.sub_prefix (by decide))
    ks := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    pst := hp.st_o.sub_left cP
    ps := (hp.st_s.sub_left cP).sub_right (Region.sub_prefix (by decide))
    sts := hp.o_s.sub_right (Region.sub_prefix (by decide))
    bK := by rw [esp₈]; exact hp.b_st.sub_right (Region.sub_prefix (by decide))
    bP := by rw [esp₈]; exact hp.b_st.sub_right cP
    bSt := by rw [esp₈]; exact hp.b_o
    bS := by rw [esp₈]; exact hp.b_s.sub_right (Region.sub_prefix (by decide))
    fK := by omega_arith
    fSt := fO
    fP := by rw [add_toNat (by omega_arith)]; omega_arith
    fS := by omega_arith
    reads := by
      rw [rd₈, wr₈, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨hstR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨hstR s₀, by simp, 408, p408, by simp; omega_arith⟩
    writes := by
      rw [wr₈, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨hoR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨hscR s₀, by simp, 0, by simp, by simp⟩ }

/-! ## The whole function -/

theorem finish_wp {s₀ : State} (h0 : finishX86.pre s₀) :
    WP isa finish s₀ fun s' => abiPreserved s₀ s' ∧ finishX86.post s₀ s' := by
  obtain hp := HPre.of h0
  have fS : (arg s₀ 4).toNat + 688 ≤ 2 ^ 32 := hp.fS
  have fSt : (arg s₀ 0).toNat + 416 ≤ 2 ^ 32 := hp.fSt
  have fSt₂ : (hSt s₀).toNat + 416 ≤ 2 ^ 32 := hp.fSt
  have fS₂ : (hSc s₀).toNat + 688 ≤ 2 ^ 32 := hp.fS
  have e24 := hp.esp24
  unfold finish
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (fin_wp h₁.args) fun s₂ h₂ => ?_)
  obtain f₂ : Frame [hoR s₀, ⟨(hSc s₀).setWidth 64, 640⟩, below (hE s₀) 24] s₁.mem s₂.mem := by
    have := h₂.frame; rw [h₁.esp] at this; exact this
  obtain F₂ : Frame (HBig s₀) s₀.mem s₂.mem := (h₁.mem ▸ hMem_frame hp).trans (f₂.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨hoR s₀, by simp, fun _ h => h⟩
    · exact ⟨hscR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩)
  -- The saved registers.
  obtain slots : ∀ r d, (r, d) ∈ saved →
      s₂.mem.readW ((hSc s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r := fun r d hrd => by
    obtain hb := saved_bound _ hrd
    obtain sub : Region.Sub ⟨(hSc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩ (hscR s₀) := Offset.sub_base _ (by omega_arith)
    obtain c := Region.contains_self ((hSc s₀).setWidth 64 + BitVec.ofNat 64 d) 4
    rw [f₂.readW c (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl
        · exact hp.o_s.symm.sub_left sub
        · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
        · exact hp.b_s.symm.sub_left sub) (by decide),
      h₁.mem, (hMem_out s₀).readW c (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq; exact hp.o_s.symm.sub_left sub) (by decide)]
    exact saveMem_slot _ _ _ hrd
  refine WP.mono (restore_wp (s₀ := s₀) (i := 4) (Sc := hSc s₀)
    (by rw [h₂.saved .esp (by simp [calleeSaved]), h₁.esp])
    (by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]; exact hp.arg_in (by decide)) (hp.keep F₂ (by decide)) fS (by
      rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨hscR s₀, by simp, 0, by simp, by simp⟩) slots)
    fun s₃ ⟨hcs, m₃⟩ => ?_
  refine ⟨⟨hcs, ?_⟩, ?_⟩
  · rw [m₃]
    refine F₂.readW (r := ⟨(hE s₀).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.ret_st
    · exact hp.ret_o
    · exact hp.ret_s
    · exact ret_below e24
  · intro key msg hr hc hlen
    show Spec.Aes.bytesAt s₃.mem ((hO s₀).setWidth 64) 8 = _
    rw [m₃]
    obtain hn : (countX86 s₀).toNat = msg.length := by
      rw [hc, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlen
    -- The state, unchanged before `finalize`.
    obtain F₁ : Frame [⟨(hSc s₀).setWidth 64 + BitVec.ofNat 64 640, 16⟩, hoR s₀] s₀.mem s₁.mem := by
      rw [h₁.mem]
      exact ((savedMem_frame _ _).mono (by simp)).trans ((hMem_out s₀).mono (by simp))
    obtain hr₁ : Spec.Cmac.tdesRepr s₁.mem ((hSt s₀).setWidth 64) key msg :=
      Proof.CmacTripleDes.Stream.repr_congr_416 (fun i hi => F₁.bytes (R := hstR s₀) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.st_s.sub_right (Offset.sub_base _ (by decide))
        · exact hp.st_o) (by show 416 ≤ 2 ^ 64; decide) hi) hr
    obtain ⟨hm, hne, hst, happ⟩ := Proof.CmacTripleDes.Stream.repr_finish hr₁
    rw [Proof.CmacTripleDes.Stream.repr_iff] at hr₁
    obtain ⟨⟨_, hks, hsk⟩, -, -⟩ := hr₁
    obtain hciph : ciphAt s₁.mem ((hSt s₀).setWidth 64) = Spec.Cmac.tdes key := by
      simp only [ciphAt, hks, Spec.Cmac.tdes]
    obtain e₂ : Spec.Aes.bytesAt s₁.mem ((hO s₀).setWidth 64) 8 =
        Spec.Aes.bytesAt s₁.mem ((hSt s₀).setWidth 64 + 400) 8 := by
      rw [show (hSt s₀).setWidth 64 + 400 = (hSt s₀).setWidth 64 + BitVec.ofNat 64 400 from rfl, h₁.mem,
        Proof.Cmac.bytesAt_frame (hMem_out s₀) (p := (hSt s₀).setWidth 64 + BitVec.ofNat 64 400) (n := 8)
          (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hp.st_o.sub_left (Offset.sub_base _ (by decide))) (by decide), hMem]
      have := bytesAt_writeBytes_self (savedMem s₀ (hSc s₀)) ((hO s₀).setWidth 64)
        (xs := Spec.Aes.bytesAt (savedMem s₀ (hSc s₀)) ((hSt s₀).setWidth 64 + BitVec.ofNat 64 400) 8)
        (by rw [Proof.Cmac.bytesAt_length]; decide)
      rw [Proof.Cmac.bytesAt_length] at this
      exact this
    obtain out := h₂.out (by rw [hciph]; exact hsk) _ hm (by rw [hH, hn]; exact hne)
      (by rw [hciph, e₂]; exact hst)
    rw [out, hciph, add_setWidth (by omega_arith), hH, hn,
      show (hSt s₀).setWidth 64 + BitVec.ofNat 64 408 = (hSt s₀).setWidth 64 + 408 from rfl, happ,
      Proof.CmacTripleDes.Stream.tdesCmac_eq]

/-! ## Constant time -/

/-- What `finalize` leaves. -/
structure HAft (s₀ s : State) : Prop where
  esp : s.gpr .esp = hE s₀
  wr : s.wr = s₀.wr
  frame : Frame (HBig s₀) s₀.mem s.mem

theorem fin_after {s₀ s : State} (hp : HPre s₀) (h : HMid s₀ s) : WP isa finFrame s (HAft s₀) :=
  WP.mono (fin_wp h.args) fun s' h' => by
    have fr := h'.frame
    rw [h.esp] at fr
    refine ⟨by rw [h'.saved .esp (by simp [calleeSaved]), h.esp], by rw [h'.wr, h.wr],
      (h.mem ▸ hMem_frame hp).trans (fr.sub fun r hr => ?_)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨hoR s₀, by simp, fun _ h => h⟩
    · exact ⟨hscR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem finish_rel {s₀ s₀' : State} (h0 : finishX86.pre s₀) (h0' : finishX86.pre s₀')
    (hq : finishX86.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') finish fun _ _ => True := by
  obtain hp := HPre.of h0
  obtain hp' := HPre.of h0'
  obtain ⟨qE, qa⟩ := hq
  obtain e0 : hSt s₀ = hSt s₀' := qa 0 (by decide)
  obtain eH : hH s₀ = hH s₀' := by rw [hH, hH, countX86, countX86, qa 1 (by decide), qa 2 (by decide)]
  obtain e3 : hO s₀ = hO s₀' := qa 3 (by decide)
  obtain e4 : hSc s₀ = hSc s₀' := qa 4 (by decide)
  obtain ag : ∀ {a b : State}, Pt 5 s₀ a → Pt 5 s₀' b → VG.X86.Taint.Agree (argTaint [] (4 + 4 * 5)) a b :=
    fun h₁ h₂ => Pt.agree qE qa hp.argsOut hp'.argsOut h₁ h₂ fun r hr => by simp at hr
  obtain a := ((RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') (argTaint [] (4 + 4 * 5))
    (fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ag (Pt.refl _ _) (Pt.refl _ _))
    (c := finPre) (by taint_decide)).wp (F₁ := HMid s₀) (F₂ := HMid s₀')
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨finPre_wp hp, finPre_wp hp'⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  obtain c := ((fin_rel (E := hE s₀) (Q := fun a b => HMid s₀ a ∧ HMid s₀' b) fun a b h =>
      ⟨h.1.args, by rw [e0, eH, e3, e4]; exact h.2.args, h.1.esp, by rw [h.2.esp]; exact qE.symm⟩).wp
      (F₁ := HAft s₀) (F₂ := HAft s₀') fun _ _ h => ⟨fin_after hp h.1, fin_after hp' h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  obtain b := RelCT.taint (A := taint) (P := fun a b => HAft s₀ a ∧ HAft s₀' b) (argTaint [] (4 + 4 * 5))
    (fun _ _ h => ag ⟨h.1.esp, h.1.wr, fun _ hi => hp.keep h.1.frame hi⟩
      ⟨h.2.esp, h.2.wr, fun _ hi => hp'.keep h.2.frame hi⟩) (c := .block (restore 4)) (by taint_decide)
  exact a.seq (c.seq b)

theorem finish_ct : ConstantTime isa finishX86.pre finishX86.pub finish :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (finish_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacTripleDes.Stream.X86

end

end

/-! ### `CmacTripleDes.Stream.X86.Init`, which only this module used -/

section

/-!
# Streaming TDEA-CMAC on x86: `vg_cmac_triple_des_stream_init`

The code keeps `ebx` in the chaining value's place, runs `init` with the
state as its `out` (which writes the key schedule and the subkeys before
it), restores `ebx` and zeroes the chaining value: the state then
represents the empty message. The code around the run of `init` is constant
time by the taint analysis (from `esp` and the stack arguments), and the run
by `init`'s own proof (`init_rel`), its arguments pinned by `IMid₁`.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86

open VG VG.X86 VG.Impl.CmacTripleDes.Stream.X86
open VG.Impl.CmacTripleDes.X86 (at_)
open VG.Proof.MdStream.X86 (Upd Mupd wp_movi wp_movm wp_store)
open VG.Proof.CmacTripleDes.X86 (ea_at')

section
variable (s₀ : State)

abbrev iSt : BitVec 32 := arg s₀ 0
abbrev iKp : BitVec 32 := arg s₀ 1
abbrev iKL : Nat := (arg s₀ 2).toNat
abbrev iSc : BitVec 32 := arg s₀ 3
abbrev iE : BitVec 32 := s₀.gpr .esp
abbrev istR : Region := ⟨(iSt s₀).setWidth 64, 416⟩
abbrev ikR : Region := ⟨(iKp s₀).setWidth 64, iKL s₀⟩
abbrev iscR : Region := ⟨(iSc s₀).setWidth 64, 640⟩
abbrev iaR : Region := ⟨argAddr s₀ 0, 16⟩

/-- Where the function writes: the state, the scratch buffer and the stack. -/
abbrev IBig : List Region := [istR s₀, iscR s₀, below (iE s₀) 20]

/-- The memory with `ebx` kept in the chaining value's place. -/
def iMem : Mem := s₀.mem.writeW ((iSt s₀).setWidth 64 + BitVec.ofNat 64 400) (s₀.gpr .ebx)

end

/-- The precondition, by name. -/
structure IPre (s₀ : State) : Prop where
  rd : s₀.rd = [ikR s₀, iaR s₀]
  wr : s₀.wr = [istR s₀, iscR s₀]
  st_k : (istR s₀).Disjoint (ikR s₀)
  st_s : (istR s₀).Disjoint (iscR s₀)
  k_s : (ikR s₀).Disjoint (iscR s₀)
  a_st : (iaR s₀).Disjoint (istR s₀)
  a_s : (iaR s₀).Disjoint (iscR s₀)
  ret_st : (⟨(iE s₀).setWidth 64, 4⟩ : Region).Disjoint (istR s₀)
  ret_s : (⟨(iE s₀).setWidth 64, 4⟩ : Region).Disjoint (iscR s₀)
  b_st' : (⟨(iE s₀).setWidth 64 - BitVec.ofNat 64 20, 20⟩ : Region).Disjoint (istR s₀)
  b_k' : (⟨(iE s₀).setWidth 64 - BitVec.ofNat 64 20, 20⟩ : Region).Disjoint (ikR s₀)
  b_s' : (⟨(iE s₀).setWidth 64 - BitVec.ofNat 64 20, 20⟩ : Region).Disjoint (iscR s₀)
  fSt : (iSt s₀).toNat + 416 ≤ 2 ^ 32
  fK : (iKp s₀).toNat + iKL s₀ ≤ 2 ^ 32
  fS : (iSc s₀).toNat + 640 ≤ 2 ^ 32
  esp20 : 20 ≤ (iE s₀).toNat
  espfit : (iE s₀).toNat + 20 ≤ 2 ^ 32
  klen : Spec.TripleDes.validKey (iKL s₀)

theorem IPre.of {s₀ : State} (h : initX86.pre s₀) : IPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r⟩

namespace IPre
variable {s₀ : State} (hp : IPre s₀)
include hp

theorem b_st : (below (iE s₀) 20).Disjoint (istR s₀) := by rw [below_eq hp.esp20]; exact hp.b_st'
theorem b_k : (below (iE s₀) 20).Disjoint (ikR s₀) := by rw [below_eq hp.esp20]; exact hp.b_k'
theorem b_s : (below (iE s₀) 20).Disjoint (iscR s₀) := by rw [below_eq hp.esp20]; exact hp.b_s'

theorem fit : (s₀.gpr .esp).toNat + 4 + 4 * 4 ≤ 2 ^ 32 := by have := hp.espfit; omega

theorem arg_in {i : Nat} (hi : i < 4) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 :=
  ⟨iaR s₀, by simp [hp.rd], arg_contains hp.fit hi⟩

/-- The stack arguments are unchanged where only `IBig` changes. -/
theorem keep {m : Mem} (hf : Frame (IBig s₀) s₀.mem m) {i : Nat} (hi : i < 4) :
    m.readW (argAddr s₀ i) 32 = arg s₀ i :=
  arg_keep hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.a_st.sub_left (arg_sub hp.fit hi)
    · exact hp.a_s.sub_left (arg_sub hp.fit hi)
    · exact (args_below hp.fit (by decide) hp.esp20).symm.sub_left (arg_sub hp.fit hi)

theorem argsOut : ArgsOut 4 s₀ := by
  refine ⟨by have := hp.espfit; omega, ?_⟩
  rw [hp.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 16) (by have := hp.espfit; omega) hp.ret_st hp.a_st
  · exact VG.X86.Taint.frame_disjoint (n := 16) (by have := hp.espfit; omega) hp.ret_s hp.a_s

end IPre

theorem IPre.iMem_big {s₀ : State} (_hp : IPre s₀) : Frame (IBig s₀) s₀.mem (iMem s₀) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 4)).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨istR s₀, by simp, Offset.sub_base _ (by decide)⟩

/-! ## Before `init` -/

/-- What the code before `init` leaves. -/
structure IMid₁ (s₀ s : State) : Prop where
  args : IArgs s (iKp s₀) (iSt s₀) (iSc s₀) (iKL s₀)
  esp : s.gpr .esp = iE s₀
  mem : s.mem = iMem s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → s.gpr r = s₀.gpr r

theorem initPre_wp {s₀ : State} (hp : IPre s₀) : WP isa (.block initPre) s₀ (IMid₁ s₀) := by
  have fSt : (arg s₀ 0).toNat + 416 ≤ 2 ^ 32 := hp.fSt
  have fSt' : (iSt s₀).toNat + 416 ≤ 2 ^ 32 := hp.fSt
  have e20 := hp.esp20
  refine wp_arg (s₀ := s₀) rfl (hp.arg_in (by decide)) rfl fun s₁ u₁ => ?_
  refine wp_store (a := (iSt s₀).setWidth 64 + BitVec.ofNat 64 400)
    (by rw [ea_at', u₁.gpr]; exact addr_eq (by omega_using [fSt]))
    (by rw [u₁.wr, hp.wr]; exact ⟨istR s₀, by simp, Offset.contains_base _ (by decide) (by decide)⟩)
    fun s₂ v₂ => ?_
  have hm₂ : s₂.mem = iMem s₀ := by rw [v₂.mem, u₁.mem, u₁.other _ (by decide), iMem]
  have esp₂ : s₂.gpr .esp = iE s₀ := by rw [v₂.gpr, u₁.other _ (by decide)]
  have rd₂ : s₂.rd = s₀.rd := by rw [v₂.rd, u₁.rd]
  have wr₂ : s₂.wr = s₀.wr := by rw [v₂.wr, u₁.wr]
  have av : ∀ i < 4, s₂.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => by
    rw [hm₂]; exact hp.keep hp.iMem_big hi
  refine wp_arg (s₀ := s₀) esp₂ (by rw [rd₂, wr₂]; exact hp.arg_in (by decide)) (av 1 (by decide))
    fun s₃ u₃ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₃.other _ (by decide), esp₂])
    (by rw [u₃.rd, u₃.wr, rd₂, wr₂]; exact hp.arg_in (by decide)) (by rw [u₃.mem]; exact av 2 (by decide))
    fun s₄ u₄ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₄.other _ (by decide), u₃.other _ (by decide), esp₂])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂]; exact hp.arg_in (by decide))
    (by rw [u₄.mem, u₃.mem]; exact av 3 (by decide)) fun s₅ u₅ => WP.block_nil ?_
  have esp₅ : s₅.gpr .esp = iE s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), esp₂]
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, rd₂]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, wr₂]
  have oSt : Region.Sub ⟨(iSt s₀).setWidth 64, 400⟩ (istR s₀) := Region.sub_prefix (by decide)
  refine ⟨?_, esp₅, by rw [u₅.mem, u₄.mem, u₃.mem, hm₂], rd₅, wr₅, fun r h1 h2 h3 h4 => by
    rw [u₅.other _ h4, u₄.other _ h3, u₃.other _ h2, v₂.gpr, u₁.other _ h1]⟩
  exact
  { ebx := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
    ecx := by rw [u₅.other _ (by decide), u₄.gpr]; exact arg_ofNat s₀ 2
    eax := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.gpr]
    edx := u₅.gpr
    klen := hp.klen
    esp := by rw [esp₅]; exact e20
    ko := (hp.st_k.sub_left oSt).symm
    ks := hp.k_s
    os := hp.st_s.sub_left oSt
    bK := by rw [esp₅]; exact hp.b_k
    bO := by rw [esp₅]; exact hp.b_st.sub_right oSt
    bS := by rw [esp₅]; exact hp.b_s
    fK := hp.fK
    fO := by omega_using [fSt']
    fS := hp.fS
    reads := by
      rw [rd₅, wr₅, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨ikR s₀, by simp, 0, by simp, by simp⟩
    writes := by
      rw [wr₅, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨istR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨iscR s₀, by simp, 0, by simp, by simp⟩ }

/-! ## After `init` -/

/-- What is known after `init`. -/
structure IAft (s₀ s : State) : Prop where
  esp : s.gpr .esp = iE s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (IBig s₀) s₀.mem s.mem
  keep : ∀ r ∈ calleeSaved, r ≠ .ebx → s.gpr r = s₀.gpr r
  stash : s.mem.readW ((iSt s₀).setWidth 64 + BitVec.ofNat 64 400) 32 = s₀.gpr .ebx

theorem IAft.pt {s₀ s : State} (hp : IPre s₀) (h : IAft s₀ s) : Pt 4 s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.keep h.frame hi⟩

theorem calleeSaved_ne : ∀ r ∈ calleeSaved, r ≠ .eax ∧ r ≠ .ecx ∧ r ≠ .edx := by decide

theorem IMid₁.after {s₀ s s' : State} (hp : IPre s₀) (h : IMid₁ s₀ s)
    (h' : IPost s (iKp s₀) (iSt s₀) (iSc s₀) (iKL s₀) s') : IAft s₀ s' := by
  have fr := h'.frame
  rw [h.esp, h.mem] at fr
  have fSt := hp.fSt
  refine ⟨by rw [h'.saved .esp (by simp [calleeSaved]), h.esp], by rw [h'.rd, h.rd], by rw [h'.wr, h.wr],
    hp.iMem_big.trans (fr.sub fun r hr => ?_), fun r hr hb => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨istR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨iscR s₀, by simp, fun _ h => h⟩
    · exact ⟨below (iE s₀) 20, by simp, fun _ h => h⟩
  · obtain ⟨h1, h3, h4⟩ := calleeSaved_ne r hr
    rw [h'.saved r hr]; exact h.keep r h1 hb h3 h4
  · have sub : Region.Sub ⟨(iSt s₀).setWidth 64 + BitVec.ofNat 64 400, 4⟩ (istR s₀) :=
      Offset.sub_base _ (by decide)
    rw [fr.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.disjoint_base _ (by decide) (by decide)
        · exact hp.st_s.sub_left sub
        · exact hp.b_st.symm.sub_left sub) (by decide), iMem, Mem.readW_writeW_self32]

/-! ## After `init` -/

/-- The memory after zeroing the chaining value at `p`, a word at a time. -/
def zeroCv (m : Mem) (p : Addr) : Mem :=
  (m.writeW p (0 : BitVec 32)).writeW (p + BitVec.ofNat 64 4) (0 : BitVec 32)

theorem zeroCv_bytes (m : Mem) (p : Addr) : Spec.Aes.bytesAt (zeroCv m p) p 8 = Spec.Cmac.zeros 8 := by
  rw [zeroCv, ← Proof.Cmac.le8_readW, Proof.CmacTripleDes.readW64_split, Mem.readW_writeW_self32,
    Proof.CmacTripleDes.X86.readW_lo_of_hi]
  decide

theorem zeroCv_frame (m : Mem) (p : Addr) : Frame [⟨p, 8⟩] m (zeroCv m p) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
    simpa using Offset.contains_base p (d := 0) (n := 4) (k := 8) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base p (d := 4) (n := 4) (k := 8) (by decide) (by decide))

/-- `ebx` restored, and the chaining value zeroed. -/
theorem initPost_wp {s₀ s : State} (hp : IPre s₀) (h : IAft s₀ s) :
    WP isa (.block initPost) s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧
      s'.mem = zeroCv s.mem ((iSt s₀).setWidth 64 + BitVec.ofNat 64 400) := by
  have fSt : (arg s₀ 0).toNat + 416 ≤ 2 ^ 32 := hp.fSt
  have fSt' : (iSt s₀).toNat + 416 ≤ 2 ^ 32 := hp.fSt
  have rw₀ : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have inSt (d : Nat) (hd : d + 4 ≤ 416) : InRegions s₀.wr ((iSt s₀).setWidth 64 + BitVec.ofNat 64 d) 4 := by
    rw [hp.wr]; exact ⟨istR s₀, by simp, Offset.contains_base _ hd (by omega_using [hd])⟩
  refine wp_arg (s₀ := s₀) h.esp (by rw [rw₀]; exact hp.arg_in (by decide)) (hp.keep h.frame (by decide))
    fun s₁ u₁ => ?_
  refine wp_movm (a := (iSt s₀).setWidth 64 + BitVec.ofNat 64 400)
    (by rw [ea_at', u₁.gpr]; exact addr_eq (by omega_using [fSt]))
    (by
      rw [u₁.rd, u₁.wr, rw₀]
      obtain ⟨r, hr, hc⟩ := inSt 400 (by decide)
      exact ⟨r, List.mem_append_right _ hr, hc⟩) fun s₂ u₂ => wp_movi fun s₃ u₃ => ?_
  have eax₃ : s₃.gpr .eax = iSt s₀ := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  refine wp_store (a := (iSt s₀).setWidth 64 + BitVec.ofNat 64 400)
    (by rw [ea_at', eax₃]; exact addr_eq (by omega_using [fSt']))
    (by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]; exact inSt 400 (by decide)) fun s₄ v₄ => ?_
  refine wp_store (a := (iSt s₀).setWidth 64 + BitVec.ofNat 64 400 + BitVec.ofNat 64 4)
    (by rw [ea_at', v₄.gpr, eax₃, Offset.add_add]; exact addr_eq (by omega_using [fSt']))
    (by rw [v₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr, Offset.add_add]; exact inSt 404 (by decide))
    fun s₅ v₅ => WP.block_nil ⟨fun r hr => ?_, ?_⟩
  · rw [v₅.gpr, v₄.gpr]
    by_cases hb : r = .ebx
    · subst hb
      rw [u₃.other _ (by decide), u₂.gpr, u₁.mem]; exact h.stash
    · obtain ⟨h1, h3, -⟩ := calleeSaved_ne r hr
      rw [u₃.other _ h3, u₂.other _ hb, u₁.other _ h1]; exact h.keep r hr hb
  · rw [v₅.mem, v₄.gpr, v₄.mem, u₃.gpr, u₃.mem, u₂.mem, u₁.mem, zeroCv]

/-! ## The whole function -/

theorem init_wp {s₀ : State} (h0 : initX86.pre s₀) :
    WP isa streamInit s₀ fun s' => abiPreserved s₀ s' ∧ initX86.post s₀ s' := by
  have hp := IPre.of h0
  have fSt := hp.fSt
  have e20 := hp.esp20
  refine WP.seq (WP.mono (initPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (init_inline_wp h₁.args) fun s₂ h₂ => ?_)
  have a₂ := h₁.after hp h₂
  refine WP.mono (initPost_wp hp a₂) fun s₃ ⟨hcs, m₃⟩ => ?_
  have fz : Frame [⟨(iSt s₀).setWidth 64 + BitVec.ofNat 64 400, 8⟩] s₂.mem s₃.mem := by
    rw [m₃]; exact zeroCv_frame _ _
  have F₃ : Frame (IBig s₀) s₀.mem s₃.mem := a₂.frame.trans (fz.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨istR s₀, by simp, Offset.sub_base _ (by decide)⟩)
  refine ⟨⟨hcs, F₃.readW (r := ⟨(iE s₀).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_st
    · exact hp.ret_s
    · exact ret_below e20
  · show Spec.Cmac.tdesRepr s₃.mem ((iSt s₀).setWidth 64)
      (Spec.TripleDes.bytesAt s₀.mem ((iKp s₀).setWidth 64) (iKL s₀)) []
    rw [Proof.CmacTripleDes.Stream.repr_iff]
    have hkey : Spec.TripleDes.bytesAt s₁.mem ((iKp s₀).setWidth 64) (iKL s₀) =
        Spec.TripleDes.bytesAt s₀.mem ((iKp s₀).setWidth 64) (iKL s₀) := by
      rw [h₁.mem]
      simp only [Spec.TripleDes.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 4)).bytes
        (R := ikR s₀) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hp.st_k.symm.sub_right (Offset.sub_base _ (by decide)))
        (by show iKL s₀ ≤ 2 ^ 64; have := hp.fK; omega_using [this]) (List.mem_range.mp hi)
    have hlen : (Spec.TripleDes.bytesAt s₀.mem ((iKp s₀).setWidth 64) (iKL s₀)).length = iKL s₀ := by
      simp [Spec.TripleDes.bytesAt]
    obtain ⟨hs, hk⟩ := h₂.out
    rw [hkey] at hs hk
    refine ⟨⟨by rw [hlen]; exact hp.klen, ?_, ?_⟩, ?_, by
      simp [Proof.CmacTripleDes.Stream.held_zero, Spec.Aes.bytesAt]⟩
    · rw [Proof.CmacTripleDes.X86.scheduleAt_frame fz fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by decide) (by decide)]
      exact hs
    · rw [show (iSt s₀).setWidth 64 + 384 = (iSt s₀).setWidth 64 + BitVec.ofNat 64 384 from rfl,
        Proof.Cmac.bytesAt_frame fz (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega_using []) (by omega_using []) (by omega_using [])) (by decide)]
      exact hk
    · rw [show (iSt s₀).setWidth 64 + 400 = (iSt s₀).setWidth 64 + BitVec.ofNat 64 400 from rfl, m₃,
        zeroCv_bytes]
      rfl

/-! ## Constant time -/

theorem init_after {s₀ s : State} (hp : IPre s₀) (h : IMid₁ s₀ s) :
    WP isa initFrame s (IAft s₀) :=
  WP.mono (init_inline_wp h.args) fun _ h' => h.after hp h'

theorem streamInit_rel {s₀ s₀' : State} (h0 : initX86.pre s₀) (h0' : initX86.pre s₀')
    (hq : initX86.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') streamInit fun _ _ => True := by
  have hp := IPre.of h0
  have hp' := IPre.of h0'
  obtain ⟨qE, qa⟩ := hq
  have e0 : iSt s₀ = iSt s₀' := qa 0 (by decide)
  have e1 : iKp s₀ = iKp s₀' := qa 1 (by decide)
  have e2 : iKL s₀ = iKL s₀' := by rw [iKL, iKL, qa 2 (by decide)]
  have e3 : iSc s₀ = iSc s₀' := qa 3 (by decide)
  have ag : ∀ {a b : State}, Pt 4 s₀ a → Pt 4 s₀' b → VG.X86.Taint.Agree (argTaint [] (4 + 4 * 4)) a b :=
    fun h₁ h₂ => Pt.agree qE qa hp.argsOut hp'.argsOut h₁ h₂ fun r hr => by simp at hr
  have a := ((RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') (argTaint [] (4 + 4 * 4))
    (fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ag (Pt.refl _ _) (Pt.refl _ _))
    (c := .block initPre) (by taint_decide)).wp (F₁ := IMid₁ s₀) (F₂ := IMid₁ s₀')
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨initPre_wp hp, initPre_wp hp'⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  have e := ((init_rel (E := iE s₀) (P := fun a b => IMid₁ s₀ a ∧ IMid₁ s₀' b) fun a b h =>
      ⟨h.1.args, by rw [e0, e1, e2, e3]; exact h.2.args, h.1.esp, by rw [h.2.esp]; exact qE.symm⟩).wp
      (F₁ := IAft s₀) (F₂ := IAft s₀') fun _ _ h => ⟨init_after hp h.1, init_after hp' h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have p := RelCT.taint (A := taint) (P := fun a b => IAft s₀ a ∧ IAft s₀' b) (argTaint [] (4 + 4 * 4))
    (fun _ _ h => ag (h.1.pt hp) (h.2.pt hp')) (c := .block initPost) (by taint_decide)
  exact a.seq (e.seq p)

theorem init_ct : ConstantTime isa initX86.pre initX86.pub streamInit :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (streamInit_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacTripleDes.Stream.X86

end

end

/-!
# Streaming TDEA-CMAC on x86: `Verified`

Correctness, constant time and satisfiability under this target's contracts
(`Contract.lean`), and the shared contracts with the working space as an
argument (`Proof/CmacTripleDes/StreamScratch.lean`, `StreamScratchW.lean`),
which imply them: with 20 bytes of stack for `stream_init` and 24 for
`absorb` and `finish` (the arguments of the code they run inline, which they
push, and a word in the return address's place).

Two runs of `absorb` from states that agree on the public arguments are
related piece by piece (`RelCT`): the taint analysis covers the code between
the runs of `update`, from `esp`, the stack arguments and `ebp`, which the
correctness proof pins to a value of the public arguments (`AAft`), and each
run of `update`, in its frame, is constant time by its own proof
(`upd_rel`), its arguments pinned by `AMid₁` and `AMid₂`.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86

open VG VG.X86 VG.Impl.CmacTripleDes.Stream.X86

theorem absorb_rel {s₀ s₀' : State} (h0 : absorbX86.pre s₀) (h0' : absorbX86.pre s₀')
    (hq : absorbX86.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') absorb fun _ _ => True := by
  have hp := APre.of h0
  have hp' := APre.of h0'
  obtain ⟨qE, qa⟩ := hq
  have eSt : aSt s₀ = aSt s₀' := qa 0 (by decide)
  have eC : aC s₀ = aC s₀' := by rw [aC, aC, countX86, countX86, qa 1 (by decide), qa 2 (by decide)]
  have eD : aD s₀ = aD s₀' := qa 3 (by decide)
  have eL : aL s₀ = aL s₀' := by rw [aL, aL, qa 4 (by decide)]
  have eS : aSc s₀ = aSc s₀' := qa 5 (by decide)
  have e2 : d2Of s₀ = d2Of s₀' := by rw [d2Of, d2Of, eC, eL, eSt, eD]
  have ag : ∀ {rs : List Reg} {a b : State}, Pt 6 s₀ a → Pt 6 s₀' b → (∀ r ∈ rs, a.gpr r = b.gpr r) →
      VG.X86.Taint.Agree (argTaint rs (4 + 4 * 6)) a b :=
    fun h₁ h₂ hr => Pt.agree qE qa hp.argsOut hp'.argsOut h₁ h₂ hr
  have bp : ∀ {v v' : Nat} {a b : State}, v = v' → AAft s₀ v a → AAft s₀' v' b → ∀ r ∈ [Reg.ebp], a.gpr r = b.gpr r :=
    fun e h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ebp, h₂.ebp, e]
  have a := ((RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') (argTaint [] (4 + 4 * 6))
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ag (Pt.refl _ _) (Pt.refl _ _) fun r hr => by simp at hr)
    (c := absorbPre) (by taint_decide)).wp (F₁ := AMid₁ s₀) (F₂ := AMid₁ s₀')
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨absorbPre_wp hp, absorbPre_wp hp'⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  have c₁ := ((upd_rel (E := aE s₀) (P := fun a b => AMid₁ s₀ a ∧ AMid₁ s₀' b) fun a b h =>
      ⟨h.1.args, by rw [eSt, eS, eC, eL]; exact h.2.args, h.1.ctx.esp,
        by rw [h.2.ctx.esp]; exact qE.symm⟩).wp
      (F₁ := AAft s₀ (fOf (aC s₀) (aL s₀))) (F₂ := AAft s₀' (fOf (aC s₀') (aL s₀')))
      fun _ _ h => ⟨upd1_after hp h.1, upd1_after hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have m := ((RelCT.taint (A := taint) (P := fun a b => AAft s₀ (fOf (aC s₀) (aL s₀)) a ∧
      AAft s₀' (fOf (aC s₀') (aL s₀')) b) (argTaint [.ebp] (4 + 4 * 6))
    (fun _ _ h => ag h.1.ctx.pt h.2.ctx.pt (bp (by rw [eC, eL]) h.1 h.2))
    (c := chain2) (by taint_decide)).wp (F₁ := AMid₂ s₀) (F₂ := AMid₂ s₀')
    fun _ _ h => ⟨WP.mono (chain2_mid hp h.1) fun _ h => h.1, WP.mono (chain2_mid hp' h.2) fun _ h => h.1⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have c₂ := ((upd_rel (E := aE s₀) (P := fun a b => AMid₂ s₀ a ∧ AMid₂ s₀' b) fun a b h =>
      ⟨h.1.args, by rw [eSt, eS, eC, eL, e2]; exact h.2.args, h.1.aft.ctx.esp,
        by rw [h.2.aft.ctx.esp]; exact qE.symm⟩).wp
      (F₁ := AAft s₀ (fOf (aC s₀) (aL s₀) + 8 * nbOf (aC s₀) (aL s₀)))
      (F₂ := AAft s₀' (fOf (aC s₀') (aL s₀') + 8 * nbOf (aC s₀') (aL s₀')))
      fun _ _ h => ⟨upd2_after hp h.1, upd2_after hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have p := RelCT.taint (A := taint) (P := fun a b => AAft s₀ (fOf (aC s₀) (aL s₀) + 8 * nbOf (aC s₀) (aL s₀)) a ∧
      AAft s₀' (fOf (aC s₀') (aL s₀') + 8 * nbOf (aC s₀') (aL s₀')) b) (argTaint [.ebp] (4 + 4 * 6))
    (fun _ _ h => ag h.1.ctx.pt h.2.ctx.pt (bp (by rw [eC, eL]) h.1 h.2)) (c := absorbPost) (by taint_decide)
  exact a.seq (c₁.seq (m.seq (c₂.seq p)))

theorem absorb_ct : ConstantTime isa absorbX86.pre absorbX86.pub absorb :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (absorb_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `Verified` -/

theorem init_verified : Verified X86.target streamInit (streamInitScratchContract X86.abi 20) :=
  Verified.of_correct (fun _ hs => init_wp hs) init_ct init_implies

theorem absorb_verified : Verified X86.target absorb (absorbScratchContract X86.abi 24) :=
  Verified.of_correct (fun _ hs => absorb_wp hs) absorb_ct absorb_implies

theorem finish_verified : Verified X86.target finish (finishScratchContract86 X86.abi 24) :=
  Verified.of_correct (fun _ hs => finish_wp hs) finish_ct finish_implies

end VG.Proof.CmacTripleDes.Stream.X86

end

end

/-!
# Streaming TDEA-CMAC on x86, with its working space on the stack

The streaming functions run their code, proved with the working space as an
argument (`Verified.lean`), in a frame that allocates it and copies the
arguments passed on the stack (`Verified.stackScratch`): the return address,
the copied argument slots (three for `stream_init`, five for `absorb`, four
for `finish`) and the working space (640 bytes for `stream_init`, 688 for
the others). The copies are read only where the pre- and postconditions
read the buffers (`Proof/CmacTripleDes/StreamScratch.lean`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86

open VG VG.X86 VG.Impl.CmacTripleDes.Stream.X86

/-- A state satisfying `vg_cmac_triple_des_stream_init`'s precondition,
without the working space: the state at `0x1000` and a 16-byte key at
`0x3000`, as stack arguments at `0x8004`. -/
def initFrameSat : State :=
  { initSat with rd := [⟨0x3000, 16⟩, ⟨0x8004, 12⟩], wr := [⟨0x1000, 416⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.tdesStreamInitContract X86.abi 680).pre s := by
  implies_sat [Spec.Cmac.tdesStreamInitContract, Spec.Cmac.tdesStreamInitSig, Spec.Cmac.tdesStreamInitPre,
    Spec.Cmac.tdesStreamInitPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [initFrameSat, initSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using initFrameSat

/-- A state satisfying `vg_cmac_triple_des_absorb`'s precondition, without
the working space: as `absorbSat`. -/
def absorbFrameSat : State :=
  { absorbSat with rd := [⟨0x3000, 0⟩, ⟨0x8004, 20⟩], wr := [⟨0x1000, 416⟩] }

theorem absorbFrameSat_pre : ∃ s, (Spec.Cmac.tdesAbsorbContract X86.abi 740).pre s := by
  implies_sat [Spec.Cmac.tdesAbsorbContract, Spec.Cmac.tdesAbsorbSig, Spec.Cmac.tdesAbsorbPost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [absorbFrameSat, absorbSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using absorbFrameSat

/-- A state satisfying `vg_cmac_triple_des_finish`'s precondition, without
the working space: as `finishSat`. -/
def finishFrameSat : State :=
  { finishSat with rd := [⟨0x8004, 16⟩], wr := [⟨0x1000, 416⟩, ⟨0x2000, 8⟩] }

theorem finishFrameSat_pre : ∃ s, (Spec.Cmac.tdesFinishContract X86.abi 736).pre s := by
  implies_sat [Spec.Cmac.tdesFinishContract, Spec.Cmac.tdesFinishSig, Spec.Cmac.tdesFinishPost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finishFrameSat, finishSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using finishFrameSat

theorem init_framed : Verified X86.target (Impl.StackScratch.X86.withStackScratch 660 3 streamInit)
    (Spec.Cmac.tdesStreamInitContract X86.abi 680) :=
  X86.Verified.stackScratch (sig := Spec.Cmac.tdesStreamInitSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Cmac.tdesStreamInitPre X86.abi.ptrBits) (post := Spec.Cmac.tdesStreamInitPost X86.abi.ptrBits)
    (wa := false) (stack := 20) (bytes := 660) init_verified (by decide) (by lit_decide) (by lit_decide)
    (streamInitPre_local _) (streamInitPost_local _) (fun vs m m₁ m₂ r hl _ => streamInitPostOut_local _ vs m m₁ m₂ r hl) initFrameSat_pre

theorem absorb_framed : Verified X86.target (Impl.StackScratch.X86.withStackScratch 716 5 absorb)
    (Spec.Cmac.tdesAbsorbContract X86.abi 740) :=
  X86.Verified.stackScratch (sig := Spec.Cmac.tdesAbsorbSig) (nm := "scratch") (e := .u64) (n := 86)
    (post := Spec.Cmac.tdesAbsorbPost X86.abi.ptrBits)
    (wa := false) (stack := 24) (bytes := 716) absorb_verified (by decide) (by lit_decide) (by lit_decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (absorbPost_local _) (fun vs m m₁ m₂ r hl _ => absorbPostOut_local _ vs m m₁ m₂ r hl) absorbFrameSat_pre

theorem finish_framed : Verified X86.target (Impl.StackScratch.X86.withStackScratch 712 4 finish)
    (Spec.Cmac.tdesFinishContract X86.abi 736) :=
  X86.Verified.stackScratch (sig := Spec.Cmac.tdesFinishSig) (nm := "scratch") (e := .u64) (n := 86)
    (post := Spec.Cmac.tdesFinishPost X86.abi.ptrBits)
    (wa := false) (stack := 24) (bytes := 712) finish_verified (by decide) (by lit_decide) (by lit_decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (finishPost_local _) (fun vs m m₁ m₂ r hl _ => finishPostOut_local _ vs m m₁ m₂ r hl) finishFrameSat_pre

end VG.Proof.CmacTripleDes.Stream.X86
