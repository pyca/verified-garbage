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
open VG.Impl.Aes.X86_64 (movR)

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

/-- The state `u'` the second function left, from a state made from `u₁'`
(the state `rest` leaves after the first function, whose memory, permissions
and MXCSR are those the first left), with what it ran from. -/
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
    (len % a.blk ≠ 0 → ∃ v u₂', v.mem = u₁'.mem ∧ v.rd = u₁'.rd ∧ v.wr = u₁'.wr ∧ v.mxcsr = u₁'.mxcsr ∧
      After₂ a s₀ v kE rdE wrE dE u₂' ∧
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

/-- What the tail leaves (see `tail_wp`). -/
structure TailDone (a : FinalArgs) (s₀ v : State) (D : Addr) (len : Nat) (kE : Contract isa)
    (rdE wrE : List Region) (dE : Nat) (w : State) : Prop where
  run : ∃ u₂', After₂ a s₀ v kE rdE wrE dE u₂' ∧
    (∀ q < len % a.blk, w.mem (restAddr a D len + BitVec.ofNat 64 q) =
      u₂'.mem (restAddr a D len + BitVec.ofNat 64 q) ^^^ u₂'.mem (blockAddr s₀ + BitVec.ofNat 64 q)) ∧
    Frame [⟨restAddr a D len, len % a.blk⟩, ⟨blockAddr s₀, a.blk⟩] u₂'.mem w.mem
  rsp : w.gpr .rsp = frameSp s₀
  slots : ∀ j < 6, w.mem.readW (s₀.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64 = s₀.gpr (FinalArgs.saved j)
  rd : w.rd = v.rd
  wr : w.wr = v.wr
  mx : w.mxcsr.extractLsb' 6 10 = v.mxcsr.extractLsb' 6 10

/-- The rest of the data lies within it. -/
theorem rest_sub (a : FinalArgs) (D : Addr) (len : Nat) :
    Region.Sub ⟨restAddr a D len, len % a.blk⟩ ⟨D, len⟩ := by
  have := Nat.div_add_mod len a.blk
  exact VG.Offset.sub_base D (by omega)

/-- The working block's first `k ≤ 72` bytes lie within the frame. -/
theorem block_sub (s₀ : State) {k : Nat} (hk : k ≤ 72) : Region.Sub ⟨blockAddr s₀, k⟩ (frameRegion s₀) := by
  have h : blockAddr s₀ = frameSp s₀ + BitVec.ofNat 64 8 := by
    rw [blockAddr, frameSp, sub_add_ofNat _ (by decide)]
  rw [h, frameRegion]
  exact VG.Offset.sub_base _ (by omega)

/-- The working block lies within the frame, outside the slots. -/
theorem block_slots (s₀ : State) {k : Nat} (hk : k ≤ 24) :
    Region.Disjoint ⟨blockAddr s₀, k⟩ (slotsRegion s₀) := by
  have h1 : blockAddr s₀ = frameSp s₀ + BitVec.ofNat 64 8 := by
    rw [blockAddr, frameSp, sub_add_ofNat _ (by decide)]
  have h2 : slotsRegion s₀ = ⟨frameSp s₀ + BitVec.ofNat 64 32, 48⟩ := by
    rw [slotsRegion, frameSp, sub_add_ofNat _ (by decide)]
  rw [h1, h2]
  exact VG.Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)

theorem zeroBlock_mxcsr (a : FinalArgs) : ∀ i ∈ a.zeroBlock, loadsMxcsr i = false := by
  intro i hi
  simp only [FinalArgs.zeroBlock, Impl.StackScratch.X86_64.wipe, Impl.StackScratch.X86_64.wipeStores,
    List.mem_cons, List.mem_map] at hi
  rcases hi with rfl | ⟨_, _, rfl⟩ <;> rfl

theorem oneBlock_mxcsr (a : FinalArgs) : ∀ i ∈ a.oneBlock, loadsMxcsr i = false := by
  intro i hi
  simp only [FinalArgs.oneBlock, FinalArgs.reload, List.mem_append, List.mem_cons, List.mem_map,
    List.not_mem_nil, or_false] at hi
  rcases hi with ⟨_, _, rfl⟩ | rfl | rfl | rfl <;> rfl

/-- The tail, from the state `v` that `rest` leaves when `r = len mod 2^lg`
bytes are left. -/
theorem tail_wp {a : FinalArgs} (ha : FinalOk a) {enc : Prog isa} {kE : Contract isa}
    (hE : ∀ s, kE.pre s → ∃ t s', Exec isa enc s t s' ∧ abiPreserved s s' ∧ kE.post s s')
    (spE : SpSafe enc) (dE : enc.x86_64Depth + 80 ≤ 2 ^ 64) {s₀ v : State} {D : Addr} {len : Nat}
    (hr : len % a.blk ≠ 0) (hwD : (⟨D, len⟩ : Region) ∈ s₀.wr) (hfitD : D.toNat + len ≤ 2 ^ 64)
    (hDF : Region.Disjoint ⟨D, len⟩ (frameRegion s₀)) (h80 : 80 ≤ (s₀.gpr .rsp).toNat)
    (vD : v.gpr (FinalArgs.saved a.dataIx) = restAddr a D len)
    (vL : v.gpr (FinalArgs.saved a.lenIx) = BitVec.ofNat 64 (len % a.blk))
    (vS : ∀ i < a.regs.length, i ≠ a.lenIx → i ≠ a.dataIx → v.gpr (FinalArgs.saved i) = s₀.gpr (a.arg i))
    (vsp : v.gpr .rsp = frameSp s₀) (vrd : v.rd = s₀.rd) (vwr : v.wr = frameRegion s₀ :: s₀.wr)
    (vslots : ∀ j < 6, v.mem.readW (s₀.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64 = s₀.gpr (FinalArgs.saved j))
    {rdE wrE : List Region}
    (preE : ∀ u, Call₂ a s₀ v u →
      kE.pre (u.withRegions rdE wrE) ∧ Covers (rdE ++ wrE) (u.rd ++ u.wr) ∧ Covers wrE u.wr)
    (slotsE : ∀ r ∈ wrE, r.Disjoint (slotsRegion s₀)) :
    WP isa (a.tail enc) v (TailDone a s₀ v D len kE rdE wrE enc.x86_64Depth) := by
  have hb := ha.blk_eq
  have hlen6 := ha.length
  have hDl := ha.data
  have hLl := ha.len
  have hrb : len % a.blk < a.blk := Nat.mod_lt _ (by omega)
  have hfr : frameRegion s₀ ∈ v.wr := by rw [vwr]; exact List.mem_cons_self
  -- The arguments for one block.
  obtain ⟨u, e, hu, hsav⟩ := tailSetup_ok ha vS vsp hfr
  have hmx : u.mxcsr = v.mxcsr :=
    runBlock_mxcsr _ _ _ (by
      intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact zeroBlock_mxcsr a i hi
      · exact oneBlock_mxcsr a i hi) e
  obtain ⟨hpre, hc, hw⟩ := preE u hu
  unfold FinalArgs.tail
  refine WP.seq (WP.of_runBlock ⟨u, e, ?_⟩)
  refine WP.seq (WP.inlineF hE spE (by omega) hpre hc hw fun u₂ rd₂ wr₂ ab f _ post => ?_)
  have rsp₂ : u₂.gpr .rsp = frameSp s₀ := by rw [ab.1 _ (by decide), hu.rsp]
  have sav₂ : ∀ i < 6, u₂.gpr (FinalArgs.saved i) = v.gpr (FinalArgs.saved i) := fun i hi => by
    rw [ab.1 _ (saved_mem i hi), hsav i hi]
  have hA₂ : After₂ a s₀ v kE rdE wrE enc.x86_64Depth u₂ :=
    ⟨⟨u, hu, post, by rw [hu.rsp] at f; exact f⟩, sav₂, rsp₂, by rw [rd₂, hu.rd], by rw [wr₂, hu.wr],
      by rw [ab.2.2, hmx]⟩
  -- The block's address to `rax`.
  obtain ⟨w₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok u₂ .rax .rsp
  obtain ⟨w₀, e₀, v₀, o₀, m₀, rd₀, wr₀⟩ := addImm_ok w₁ .rax 8
  have hK : w₀.gpr .rax = blockAddr s₀ := by
    rw [v₀, v₁, rsp₂, eight_signExtend]
    exact sub_add_ofNat (s₀.gpr .rsp) (a := 80) (b := 8) (by decide)
  have e₀₁ : runBlock isa ([.mov .rax (.reg .rsp), .alu .add .rax (.imm 8)] : List Instr) u₂ = some w₀ := by
    rw [show ([.mov .rax (.reg .rsp), .alu .add .rax (.imm 8)] : List Instr) = [movR .rax .rsp] ++
      [.alu .add .rax (.imm 8)] from rfl, runBlock_app, e₁, Option.bind_some]; exact e₀
  have hmx₀ : w₀.mxcsr = u₂.mxcsr := runBlock_mxcsr _ _ _ (by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> rfl) e₀₁
  refine WP.seq (WP.of_runBlock ⟨w₀, e₀₁, ?_⟩)
  -- The XOR loop.
  let Rd := FinalArgs.saved a.dataIx
  let Rl := FinalArgs.saved a.lenIx
  let R := restAddr a D len
  let K := blockAddr s₀
  let r := len % a.blk
  have hrax : ∀ x, x ≠ .rax → w₀.gpr x = u₂.gpr x := fun x h => by rw [o₀ x h, o₁ x h]
  have dD6 : a.dataIx < 6 := by omega
  have dL6 : a.lenIx < 6 := by omega
  have hRd : w₀.gpr Rd = R := by rw [hrax _ (saved_scratch _ dD6).1, sav₂ _ dD6, vD]
  have hRl : w₀.gpr Rl = BitVec.ofNat 64 r := by rw [hrax _ (saved_scratch _ dL6).1, sav₂ _ dL6, vL]
  have hRsub : Region.Sub ⟨R, r⟩ ⟨D, len⟩ := rest_sub a D len
  have hKsub : Region.Sub ⟨K, r⟩ (frameRegion s₀) := block_sub s₀ (by omega)
  have hKR : Region.Disjoint ⟨K, r⟩ ⟨R, r⟩ := ((hDF.sub_left hRsub).sub_right hKsub).symm
  have hRfit : R.toNat + r ≤ 2 ^ 64 := by
    have hq := Nat.div_add_mod len a.blk
    have : (D + BitVec.ofNat 64 (a.blk * (len / a.blk))).toNat = D.toNat + a.blk * (len / a.blk) := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    show (D + BitVec.ofNat 64 (a.blk * (len / a.blk))).toNat + len % a.blk ≤ 2 ^ 64
    omega
  have hKfit : K.toNat + r ≤ 2 ^ 64 := by
    have : K.toNat = (s₀.gpr .rsp).toNat - 72 := by
      show (s₀.gpr .rsp - BitVec.ofNat 64 72).toNat = _
      exact toNat_sub_ofNat (by omega)
    have := (s₀.gpr .rsp).isLt
    omega
  have rdw₀ : w₀.rd = s₀.rd := by rw [rd₀, rd₁, rd₂, hu.rd, vrd]
  have wrw₀ : w₀.wr = frameRegion s₀ :: s₀.wr := by rw [wr₀, wr₁, wr₂, hu.wr, vwr]
  have hp : XPre w₀ K R r Rd Rl :=
    { pos := by omega
      small := by omega
      fitK := hKfit
      fitR := hRfit
      disj := hKR
      rdK := fun q hq => ⟨frameRegion s₀, List.mem_append_right _ (by rw [wrw₀]; exact List.mem_cons_self),
        hKsub _ (VG.Offset.contains_base K (by omega) (by omega))⟩
      wrR := fun q hq => ⟨⟨D, len⟩, by rw [wrw₀]; exact List.mem_cons_of_mem _ hwD,
        hRsub _ (VG.Offset.contains_base R (by omega) (by omega))⟩
      dl := fun h => ha.dl (saved_inj _ dD6 _ dL6 h)
      dRax := ⟨(saved_scratch _ dD6).1, (saved_scratch _ dL6).1⟩
      dR10 := ⟨(saved_scratch _ dD6).2.1, (saved_scratch _ dL6).2.1⟩
      dR11 := ⟨(saved_scratch _ dD6).2.2, (saved_scratch _ dL6).2.2⟩ }
  have h0 : XInv w₀ K R r Rd Rl 0 w₀ :=
    { rax := by rw [hK]; exact (BitVec.add_zero _).symm
      dat := by rw [hRd]; exact (BitVec.add_zero _).symm
      left := by rw [hRl, Nat.sub_zero]
      lt := by omega
      data := fun q _ => by rw [ite_eq_right (Nat.not_lt_zero q)]
      frame := Frame.refl _ _
      rd := rfl
      wr := rfl
      gpr := fun _ _ _ _ _ _ => rfl
      mx := rfl }
  rw [xorByte_eq]
  refine WP.seq (WP.mono (xorLoop_wp hp h0) fun w₂ d₂ => ?_)
  -- The block zeroed again.
  have rsp₀ : w₀.gpr .rsp = frameSp s₀ := by rw [hrax _ (by decide), rsp₂]
  have rsp₂' : w₂.gpr .rsp = frameSp s₀ := by
    rw [d₂.gpr _ (by decide) (by decide) (by decide) (saved_ne_rsp _ dD6).symm (saved_ne_rsp _ dL6).symm, rsp₀]
  have hK8 : frameSp s₀ + BitVec.ofNat 64 8 = K := by
    rw [frameSp]; exact sub_add_ofNat (s₀.gpr .rsp) (a := 80) (b := 8) (by decide)
  have hfr₂ : frameRegion s₀ ∈ w₂.wr := by rw [d₂.wr, wrw₀]; exact List.mem_cons_self
  have hfrK : frameRegion s₀ = ⟨w₂.gpr .rsp, 80⟩ := by rw [frameRegion, rsp₂']
  obtain ⟨w, e₃, f₃, -, g₃, -, rd₃, wr₃⟩ := wipe_zero ⟨K, a.blk⟩ (frameRegion s₀) w₂ hfr₂ (a.blk / 8)
    (by omega) (fun k hk => by
      rw [rsp₂', ← VG.Offset.add_add, hK8]; exact VG.Offset.contains_base _ (by omega) (by omega))
    (fun k hk => by rw [hfrK]; exact VG.Offset.contains_base _ (by omega) (by omega))
  refine WP.of_runBlock ⟨w, e₃, ?_⟩
  have hmx₃ : w.mxcsr = w₂.mxcsr := runBlock_mxcsr _ _ _ (zeroBlock_mxcsr a) e₃
  have mem₀ : w₀.mem = u₂.mem := by rw [m₀, m₁]
  have dKR' : Region.Disjoint ⟨R, r⟩ ⟨K, a.blk⟩ :=
    (hDF.sub_left hRsub).sub_right (block_sub s₀ (by omega))
  have hslotsF : Region.Sub (slotsRegion s₀) (frameRegion s₀) := by
    rw [show slotsRegion s₀ = ⟨frameSp s₀ + BitVec.ofNat 64 32, 48⟩ by
      rw [slotsRegion, frameSp, sub_add_ofNat _ (by decide)], frameRegion]
    exact VG.Offset.sub_base _ (by omega)
  refine ⟨⟨u₂, hA₂, fun q hq => ?_, ?_⟩, by rw [g₃ _ (by decide), rsp₂'], fun j hj => ?_,
    by rw [rd₃, d₂.rd, rdw₀, vrd], by rw [wr₃, d₂.wr, wrw₀, vwr], by rw [hmx₃, d₂.mx, hmx₀]; exact hA₂.mx⟩
  · rw [f₃.bytes (R := ⟨R, r⟩) (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact dKR')
      (show r ≤ 2 ^ 64 by omega) hq, d₂.data q hq, mem₀]
  · rw [← mem₀]
    refine ((d₂.frame.mono fun x hx => ?_).trans (f₃.mono fun x hx => ?_))
    · simp only [List.mem_singleton] at hx; subst hx; exact List.mem_cons_self
    · simp only [List.mem_singleton] at hx; subst hx; exact List.mem_cons_of_mem _ List.mem_cons_self
  · have hsj := slot_sub s₀ hj
    have one : ∀ {X : Region} {m m' : Mem}, Frame [X] m m' → Region.Disjoint X (slotsRegion s₀) →
        m'.readW (s₀.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64 =
          m.readW (s₀.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64 := fun hf hd =>
      hf.readW (Region.contains_self _ _) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact (hd.sub_right hsj).symm) (by decide)
    have dRS : Region.Disjoint ⟨R, r⟩ (slotsRegion s₀) := (hDF.sub_left hRsub).sub_right hslotsF
    rw [one f₃ (block_slots s₀ (by omega)), one d₂.frame dRS, mem₀, slots_keep hu.rsp f slotsE dE hj,
      one hu.frame (block_slots s₀ (by omega)), vslots j hj]

end VG.Proof.Modes.X86_64
