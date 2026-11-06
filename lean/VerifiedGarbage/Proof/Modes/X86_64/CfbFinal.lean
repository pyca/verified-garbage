module

public import VerifiedGarbage.Proof.Modes.X86_64.CfbFinalCalls
public import VerifiedGarbage.Proof.Modes.X86_64.CfbFinalTail
public import VerifiedGarbage.Proof.Framework.X86_64.InlineCalls
public import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# CFB of a message's last piece on x86-64: the whole function

`cfbFinal_wp`: `cfbFinal a whole enc`, for inlined functions `whole` and
`enc` verified against contracts `kW` and `kE`, from a state `s₀` whose
data at `D` is `len` bytes long. It runs `whole` from the state `Call₁`
describes, then, if `r = len mod 2^lg ≠ 0`, `enc` from the state `Call₂`
describes, and XORs the first `r` bytes of the working block into the rest
of the data, at `R = D + 2^lg ⌊len / 2^lg⌋` (`FinalDone`). The caller's
proof (one per cipher) shows that each function's precondition holds there,
narrowed to its buffers, and reads the result off their postconditions with
`Proof.Modes.cfbEncFinal_of` and `cfbDecFinal_of`.
-/

@[expose] public section

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64

/-- The frame's `rsp`. -/
abbrev frameSp (s₀ : State) : Addr := s₀.gpr .rsp - BitVec.ofNat 64 80

/-- The rest of the data, after its whole blocks. -/
abbrev restAddr (a : FinalArgs) (D : Addr) (len : Nat) : Addr := D + BitVec.ofNat 64 (a.blk * (len / a.blk))

/-- The state `u'` the first function left, with what it ran from. -/
structure After₁ (a : FinalArgs) (s₀ : State) (len : Nat) (kW : Contract isa) (rdW wrW : List Region) (d : Nat)
    (u' : State) : Prop where
  run : ∃ u, Call₁ a s₀ len u ∧ kW.post (u.withRegions rdW wrW) (u'.withRegions rdW wrW) ∧
    Frame (wrW ++ [below (frameSp s₀) d]) u.mem u'.mem
  saved : ∀ i < a.regs.length, u'.gpr (FinalArgs.saved i) = s₀.gpr (a.arg i)
  rsp : u'.gpr .rsp = frameSp s₀
  slots : ∀ j < 6, u'.mem.readW (s₀.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64 = s₀.gpr (FinalArgs.saved j)
  rd : u'.rd = s₀.rd
  wr : u'.wr = frameRegion s₀ :: s₀.wr
  mx : u'.mxcsr.extractLsb' 6 10 = s₀.mxcsr.extractLsb' 6 10

/-- The state `u'` the second function left, after the first left `u₁'`, with
what it ran from. -/
structure After₂ (a : FinalArgs) (s₀ u₁' : State) (kE : Contract isa) (rdE wrE : List Region) (d : Nat)
    (u' : State) : Prop where
  run : ∃ u, Call₂ a s₀ u₁' u ∧ kE.post (u.withRegions rdE wrE) (u'.withRegions rdE wrE) ∧
    Frame (wrE ++ [below (frameSp s₀) d]) u.mem u'.mem
  saved : ∀ i < 6, u'.gpr (FinalArgs.saved i) = u₁'.gpr (FinalArgs.saved i)
  rsp : u'.gpr .rsp = frameSp s₀
  rd : u'.rd = u₁'.rd
  wr : u'.wr = u₁'.wr
  mx : u'.mxcsr.extractLsb' 6 10 = u₁'.mxcsr.extractLsb' 6 10

/-- What `cfbFinal` leaves (see above). -/
structure FinalDone (a : FinalArgs) (s₀ : State) (D : Addr) (len : Nat) (kW kE : Contract isa)
    (rdW wrW rdE wrE : List Region) (dW dE : Nat) (s' : State) : Prop where
  run : ∃ u₁', After₁ a s₀ len kW rdW wrW dW u₁' ∧
    (len % a.blk = 0 → s'.mem = u₁'.mem) ∧
    (len % a.blk ≠ 0 → ∃ u₂', After₂ a s₀ u₁' kE rdE wrE dE u₂' ∧
      (∀ q < len % a.blk, s'.mem (restAddr a D len + BitVec.ofNat 64 q) =
        u₂'.mem (restAddr a D len + BitVec.ofNat 64 q) ^^^ u₂'.mem (blockAddr s₀ + BitVec.ofNat 64 q)) ∧
      Frame [⟨restAddr a D len, len % a.blk⟩, ⟨blockAddr s₀, a.blk⟩] u₂'.mem s'.mem)
  cs : ∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r
  rd : s'.rd = s₀.rd
  wr : s'.wr = s₀.wr
  mx : s'.mxcsr.extractLsb' 6 10 = s₀.mxcsr.extractLsb' 6 10

/-- Slot `j`, at an offset of the frame's `rsp`. -/
theorem slot_eq_frame (s₀ : State) {j : Nat} (hj : j < 6) :
    s₀.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1)) = frameSp s₀ + BitVec.ofNat 64 (FinalArgs.savedOff j) :=
  (slot_addr s₀ hj).symm

/-- Slot `j` is in the slots' region. -/
theorem slot_sub (s₀ : State) {j : Nat} (hj : j < 6) :
    Region.Sub ⟨s₀.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1)), 8⟩ (slotsRegion s₀) := by
  rw [show s₀.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1)) = s₀.gpr .rsp - BitVec.ofNat 64 48 +
      BitVec.ofNat 64 (40 - 8 * j) by rw [sub_add_ofNat _ (by omega)]; congr 2; omega]
  exact VG.Offset.sub_base _ (by omega)

/-- Slot `j` lies above the `d` bytes below the frame's `rsp`. -/
theorem slot_below (s₀ : State) {j d : Nat} (hj : j < 6) (hd : d + 80 ≤ 2 ^ 64) :
    Region.Disjoint ⟨s₀.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1)), 8⟩ (below (frameSp s₀) d) := by
  rw [slot_eq_frame s₀ hj]
  exact VG.Offset.disjoint_below _ (by simp only [FinalArgs.savedOff]; omega)

/-- What a function inlined at `u` keeps of the slots, if it writes only `wr`
(each disjoint from the slots) and the `d` bytes below `rsp`. -/
theorem slots_keep {s₀ u u' : State} {wr : List Region} {d : Nat} (hsp : u.gpr .rsp = frameSp s₀)
    (hf : Frame (wr ++ [below (u.gpr .rsp) d]) u.mem u'.mem) (hs : ∀ r ∈ wr, r.Disjoint (slotsRegion s₀))
    (hd : d + 80 ≤ 2 ^ 64) {j : Nat} (hj : j < 6) :
    u'.mem.readW (s₀.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64 =
      u.mem.readW (s₀.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64 := by
  rw [hsp] at hf
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  · exact ((hs r hr).sub_right (slot_sub s₀ hj)).symm
  · simp only [List.mem_singleton] at hr; subst hr
    exact slot_below s₀ hj hd

/-- The frame's push, `entry ++ toBlocks` and the first function. -/
theorem first_wp {a : FinalArgs} (ha : FinalOk a) {whole : Prog isa} {kW : Contract isa}
    (hW : ∀ s, kW.pre s → ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ kW.post s s')
    (spW : SpSafe whole) (dW : whole.x86_64Depth + 80 ≤ 2 ^ 64) {s₀ : State} {len : Nat}
    (hL : s₀.gpr (a.arg a.lenIx) = BitVec.ofNat 64 len) (hlen : len < 2 ^ 64) (h80 : 80 ≤ (s₀.gpr .rsp).toNat)
    {rdW wrW : List Region}
    (preW : ∀ u, Call₁ a s₀ len u →
      kW.pre (u.withRegions rdW wrW) ∧ Covers (rdW ++ wrW) (u.rd ++ u.wr) ∧ Covers wrW u.wr)
    (slotsW : ∀ r ∈ wrW, r.Disjoint (slotsRegion s₀)) :
    WP isa (.seq (.block (a.entry ++ a.toBlocks)) whole) (pushed FinalArgs.pushRegs s₀)
      (After₁ a s₀ len kW rdW wrW whole.x86_64Depth) := by
  obtain ⟨u, e, hu⟩ := entry_ok ha hL hlen h80
  have hmx : u.mxcsr = s₀.mxcsr := by
    rw [runBlock_mxcsr _ _ _ (by
      intro i hi
      simp only [FinalArgs.entry, FinalArgs.toBlocks, List.mem_append, List.mem_map, List.mem_singleton] at hi
      rcases hi with ⟨_, _, rfl⟩ | rfl <;> rfl) e, pushed_mxcsr]
  obtain ⟨hpre, hc, hw⟩ := preW u hu
  refine WP.seq (WP.of_runBlock ⟨u, e, WP.inlineF hW spW (by omega) hpre hc hw fun s' rd' wr' ab f _ post => ?_⟩)
  have hd : whole.x86_64Depth + 80 ≤ 2 ^ 64 := dW
  refine ⟨⟨u, hu, post, by rw [hu.rsp] at f; exact f⟩, fun i hi => ?_, ?_, fun j hj => ?_, by rw [rd', hu.rd],
    by rw [wr', hu.wr], by rw [ab.2.2, hmx]⟩
  · rw [ab.1 _ (saved_mem i (by have := ha.length; omega)), hu.saved i hi]
  · rw [ab.1 _ (by decide), hu.rsp]
  · rw [slots_keep hu.rsp f slotsW hd hj, hu.slots j hj]

end VG.Proof.Modes.X86_64
