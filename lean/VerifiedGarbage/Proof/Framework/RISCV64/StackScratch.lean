module

public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# A scratch buffer on the stack, wiped after use (RISC-V)

`Verified.stackScratchWiped`: code verified for a function whose last
argument, passed in a register, is a scratch buffer (its contract
`Sig.scratchContract`), runs as a function without that argument when
`withStackScratchWiped` allocates the buffer in a frame on the stack, with
`bytes` more bytes of stack, and zeroes its first `words` doublewords after
the code. As on PPC64LE (`Proof/Framework/PPC64LE/StackScratch.lean`,
`StackScratchWipe.lean`), the code runs from the state after the frame's
`alloc` and `addi r, sp, 0` with the permissions of the contract with the
argument (`narrow`), and its run there is its run from that state
(`Exec.widen`). The buffer is the whole frame, at the new stack pointer.

On RISC-V the frame's `alloc` writes no memory, so the code starts with the
memory on entry. The wipe stores only into the buffer (`wipe_run`), so the
postcondition holds of the memory after it if it reads the memory on return
only within the function's buffers (`hpostOut`), which are disjoint from the
frame.
-/

@[expose] public section

namespace VG.RISCV64

open VG.Impl.StackScratch.RISCV64

/-- The arguments of a function with signature `sig`, all in registers. -/
abbrev regArgs (sig : Sig) (s : State) : List (BitVec 64) :=
  (argRegs.take (sig.words abi.ptrBits).length).map s.gpr

theorem stackBelow_pos (sp : Addr) {n : Nat} (h : 0 < n) : stackBelow sp n = [below sp n] := by
  cases n with
  | zero => omega_arith
  | succ n => rfl

theorem toNat_sub_ofNat' {a : Addr} {k : Nat} (h : k ≤ a.toNat) :
    (a - BitVec.ofNat 64 k).toNat = a.toNat - k := by
  have := a.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega_arith),
    show 2 ^ 64 - k + a.toNat = (a.toNat - k) + 2 ^ 64 by omega_arith, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega_arith)]

/-- The stack below `sp - a`, within the stack below `sp`. -/
theorem below_below (sp : Addr) (a n : Nat) :
    Region.Sub (below (sp - BitVec.ofNat 64 a) n) (below sp (n + a)) := by
  intro x hx
  simp only [Region.Contains] at hx ⊢
  rw [show x - (sp - BitVec.ofNat 64 (n + a)) = x - (sp - BitVec.ofNat 64 a - BitVec.ofNat 64 n) by
    rw [BitVec.sub_sub sp, BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 n)]]
  omega_arith

theorem argRegs_take_succ (g : Reg → BitVec 64) :
    ∀ k < 8, (argRegs.take (k + 1)).map g = (argRegs.take k).map g ++ [g (argRegs.getD k .a0)]
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl
  | 6, _ => rfl | 7, _ => rfl
  | _ + 8, h => absurd h (by omega_arith)

theorem argRegs_scratch :
    ∀ k < 8, argRegs.getD k .a0 ∉ preserved ∧ argRegs.getD k .a0 ≠ .ra ∧
      ∀ q ∈ argRegs.take k, q ≠ argRegs.getD k .a0 := by
  decide

theorem regArgs_length (sig : Sig) (s : State) (hk : (sig.words abi.ptrBits).length ≤ 8) :
    (regArgs sig s).length = (sig.words abi.ptrBits).length := by
  simp only [regArgs, List.length_map, List.length_take, argRegs, List.length_cons, List.length_nil]
  omega_arith

/-- The precondition of a contract whose arguments are all in registers. -/
theorem pre_regs {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat} {s : State}
    (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true) :
    (sig.contract abi pre post wa stack).pre s ↔
      (s.sp.toNat % 16 = 0 ∧ (stack = 0 ∨ stack ≤ s.sp.toNat)) ∧
      s.rd = ((Sig.bufs sig.params (regArgs sig s)).filter (!·.2)).map (·.1) ∧
      s.wr = ((Sig.bufs sig.params (regArgs sig s)).filter (·.2)).map (·.1) ∧
      (Sig.bufs sig.params (regArgs sig s)).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) ∧
      (∀ r ∈ stackBelow s.sp stack, ∀ a ∈ Sig.bufs sig.params (regArgs sig s), r.Disjoint a.1) ∧
      (∀ a ∈ Sig.bufs sig.params (regArgs sig s), a.1.base.toNat + a.1.len ≤ 2 ^ 64) ∧
      Curry.apply (sig.words abi.ptrBits) pre (regArgs sig s) s.mem ∧
      ∀ p ∈ Sig.alignedBufs sig.params (regArgs sig s), p.1.toNat % p.2 = 0 := by
  have hk' : (sig.words 64).length ≤ argRegs.length := by
    have : (sig.words 64).length ≤ 8 := hk
    simpa [argRegs] using this
  have hz : (sig.words 64).length - argRegs.length = 0 := Nat.sub_eq_zero_of_le hk'
  have hL := fun vs => Sig.lists_of_noLists 64 s.mem sig.params vs hl
  simp only [Sig.contract, abi, List.length_map, hk', hz, ite_true, List.map_nil, List.append_nil, hL,
    Bool.cond_true]
  refine and_congr ?_ Iff.rfl
  cases stack <;> simp

/-- The postcondition of a contract whose arguments are all in registers. -/
theorem post_regs {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat} {s s' : State}
    (hk : (sig.words abi.ptrBits).length ≤ 8) :
    (sig.contract abi pre post wa stack).post s s' ↔
      Curry.apply (sig.words abi.ptrBits) post (regArgs sig s) s.mem s'.mem
        ((s'.gpr .a0).setWidth _) := by
  have hk' : (sig.words 64).length ≤ argRegs.length := by
    have : (sig.words 64).length ≤ 8 := hk
    simpa [argRegs] using this
  simp only [Sig.contract, abi, List.length_map, hk', ite_true]
  exact Iff.rfl

/-- The public data of a contract whose arguments are all in registers, and
which leaks nothing. -/
theorem pub_regs {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat} {s₁ s₂ : State}
    (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true) :
    (sig.contract abi pre post wa stack none).pub s₁ s₂ ↔
      s₁.sp = s₂.sp ∧
      ∀ i, (sig.params.flatMap (·.2.pubs)).getD i false = true →
        ((regArgs sig s₁).getD i 0).setWidth
            (((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64) =
          ((regArgs sig s₂).getD i 0).setWidth
            (((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64) := by
  have hk' : (sig.words 64).length ≤ argRegs.length := by
    have : (sig.words 64).length ≤ 8 := hk
    simpa [argRegs] using this
  have hD := fun vs => Sig.descs_of_noLists 64 sig.params vs hl
  simp only [Sig.contract, abi, List.length_map, hk', ite_true, hD, List.not_mem_nil, false_implies,
    implies_true, and_true]
  exact Iff.rfl

/-- The public data of a contract whose arguments are all in registers, with
its leak. -/
theorem pub_regsL {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat} {s₁ s₂ : State}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}
    (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true) :
    (sig.contract abi pre post wa stack leak).pub s₁ s₂ ↔
      (s₁.sp = s₂.sp ∧ leakAgree leak (regArgs sig s₁) s₁.mem (regArgs sig s₂) s₂.mem) ∧
      ∀ i, (sig.params.flatMap (·.2.pubs)).getD i false = true →
        ((regArgs sig s₁).getD i 0).setWidth
            (((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64) =
          ((regArgs sig s₂).getD i 0).setWidth
            (((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64) := by
  have hk' : (sig.words 64).length ≤ argRegs.length := by
    have : (sig.words 64).length ≤ 8 := hk
    simpa [argRegs] using this
  have hD := fun vs => Sig.descs_of_noLists 64 sig.params vs hl
  simp only [Sig.contract, abi, List.length_map, hk', ite_true, hD, List.not_mem_nil, false_implies,
    implies_true, and_true]
  cases leak with
  | none => simp only [leakAgree, and_true]; exact Iff.rfl
  | some f => exact Iff.rfl

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {stack bytes words : Nat}

/-- The register of the buffer's address, the last argument. -/
abbrev scratchReg (sig : Sig) : Reg := argRegs.getD (sig.words abi.ptrBits).length .a0

/-- The state after the frame's `alloc` and passing the buffer's address, the
new stack pointer, in the register of the last argument. -/
def scratchState (sig : Sig) (bytes : Nat) (s : State) : State :=
  (allocd bytes s).write (scratchReg sig) (s.sp - BitVec.ofNat 64 bytes)

/-- The state the code runs from, with the permissions of the contract with
the buffer: `scratchState`, which may read `s.rd` and write `s.wr` and the
buffer. -/
def narrow (sig : Sig) (e : Elem) (n bytes : Nat) (s : State) : State :=
  (scratchState sig bytes s).withRegions s.rd
    (s.wr ++ [⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩])

theorem narrow_gpr (s : State) (q : Reg) :
    (narrow sig e n bytes s).gpr q =
      if q = scratchReg sig then s.sp - BitVec.ofNat 64 bytes else s.gpr q := by
  simp only [narrow, scratchState, State.withRegions, allocd, State.write]

@[simp] theorem narrow_mem (s : State) : (narrow sig e n bytes s).mem = s.mem := rfl
@[simp] theorem narrow_rd (s : State) : (narrow sig e n bytes s).rd = s.rd := rfl
@[simp] theorem narrow_wr (s : State) :
    (narrow sig e n bytes s).wr = s.wr ++ [⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩] := rfl
@[simp] theorem narrow_sp (s : State) : (narrow sig e n bytes s).sp = s.sp - BitVec.ofNat 64 bytes :=
  rfl

theorem narrow_regArgs (hk : (sig.words abi.ptrBits).length < 8) (s : State) :
    regArgs (sig.withScratch nm e n) (narrow sig e n bytes s) =
      regArgs sig s ++ [s.sp - BitVec.ofNat 64 bytes] := by
  obtain ⟨-, -, hr⟩ := argRegs_scratch _ hk
  simp only [regArgs, Sig.words_withScratch, List.length_append, List.length_singleton]
  rw [argRegs_take_succ _ _ hk]
  congr 1
  · refine List.map_congr_left fun q hq => ?_
    simp only [narrow_gpr, hr q hq, ↓reduceIte]
  · simp only [narrow_gpr, ↓reduceIte]

/-- The buffer is within the stack below the stack pointer that the contract
without it gives. -/
theorem buf_sub (s : State) (hb : n * e.size ≤ bytes) :
    Region.Sub ⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩ (below s.sp (stack + bytes)) :=
  Offset.sub_below _ (by omega_arith) (by omega_arith)

/-- The precondition of the contract without the buffer gives the one with it
in `narrow`. -/
theorem narrow_pre (hk : (sig.words abi.ptrBits).length < 8)
    (hb : 0 < bytes ∧ bytes ≤ 4064 ∧ bytes % 16 = 0 ∧ n * e.size ≤ bytes)
    {s : State} (hs : (sig.contract abi pre post wa (stack + bytes)).pre s)
    (hl : Sig.noLists sig.params = true) :
    (Sig.scratchContract abi sig nm e n pre post wa stack).pre (narrow sig e n bytes s) := by
  obtain ⟨hb0, -, hb2, hb3⟩ := hb
  rw [pre_regs (by omega_arith) hl] at hs
  obtain ⟨⟨hal, hwf⟩, hrd, hwr, hpw, hres, hnw, hpr⟩ := hs
  have hsb : stack + bytes ≤ s.sp.toNat := by rcases hwf with h | h <;> omega_arith
  have hlen := regArgs_length sig s (by omega_arith)
  have hbufs : Sig.bufs (sig.withScratch nm e n).params
      (regArgs sig s ++ [s.sp - BitVec.ofNat 64 bytes]) =
      Sig.bufs sig.params (regArgs sig s) ++
        [(⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩, true)] :=
    Sig.bufs_append_array abi.ptrBits nm e n _ sig.params _ hlen
  have hbelow : below s.sp (stack + bytes) ∈ stackBelow s.sp (stack + bytes) := by
    rw [stackBelow_pos _ (by omega_arith)]; simp
  have hscrSub := buf_sub (stack := stack) (e := e) (n := n) s hb3
  have hscrD : ∀ a ∈ Sig.bufs sig.params (regArgs sig s),
      a.1.Disjoint ⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩ :=
    fun a ha => (Region.Disjoint.symm (hres _ hbelow a ha)).sub_right hscrSub
  have hbase : (s.sp - BitVec.ofNat 64 bytes).toNat = s.sp.toNat - bytes :=
    toNat_sub_ofNat' (by omega_arith)
  refine (pre_regs (sig := sig.withScratch nm e n)
    (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
    (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
    (by rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega_arith)
    (Sig.noLists_withScratch nm e n hl)).mpr ?_
  rw [narrow_regArgs hk, hbufs, narrow_sp]
  refine ⟨⟨by rw [hbase]; omega_arith, .inr (by rw [hbase]; omega_arith)⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [narrow_rd, hrd, List.filter_append, List.map_append]; simp
  · simp only [narrow_wr, hwr, List.filter_append, List.map_append]; simp
  · refine List.pairwise_append.mpr ⟨hpw, List.pairwise_singleton _ _, fun a ha b hb _ => ?_⟩
    simp only [List.mem_singleton] at hb; subst hb
    exact hscrD a ha
  · intro x hx a ha
    rcases Nat.eq_zero_or_pos stack with h0 | h0
    · subst h0; simp [stackBelow] at hx
    rw [stackBelow_pos _ h0, List.mem_singleton] at hx; subst hx
    rcases List.mem_append.mp ha with ha | ha
    · exact (hres _ hbelow a ha).sub_left (below_below _ bytes stack)
    · simp only [List.mem_singleton] at ha; subst ha
      exact (Offset.base_disjoint_below (s.sp - BitVec.ofNat 64 bytes) (n := stack) (k := n * e.size)
        (by have := s.sp.isLt; omega_arith)).symm
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hnw a ha
    · simp only [List.mem_singleton] at ha; subst ha
      show (s.sp - BitVec.ofNat 64 bytes).toNat + n * e.size ≤ 2 ^ 64
      have := s.sp.isLt
      rw [hbase]; omega_arith
  · obtain ⟨hpr, hu⟩ := hpr
    refine ⟨Eq.mpr (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params pre _ _ hlen) _) hpr,
      ?_⟩
    intro p hp
    rw [show (sig.withScratch nm e n).params = sig.params ++ [(nm, .array true e n)] from rfl,
      Sig.alignedBufs_append_array abi.ptrBits nm e n _ sig.params _ hlen] at hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hu p hp
    · split at hp
      · simp only [List.mem_singleton] at hp; subst hp
        refine Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Elem.align_dvd_eight e) (Nat.dvd_of_mod_eq_zero ?_))
        rw [hbase]; omega_arith
      · simp at hp

/-- The public data of the contract without the buffer is public in
`narrow` for the contract with it. -/
theorem narrow_pub (hk : (sig.words abi.ptrBits).length < 8) {s₁ s₂ : State}
    (hp : (sig.contract abi pre post wa (stack + bytes)).pub s₁ s₂) (hl : Sig.noLists sig.params = true) :
    (Sig.scratchContract abi sig nm e n pre post wa stack).pub (narrow sig e n bytes s₁)
      (narrow sig e n bytes s₂) := by
  rw [pub_regs (by omega_arith) hl] at hp
  obtain ⟨hsp, hpa⟩ := hp
  refine (pub_regs (sig := sig.withScratch nm e n)
    (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
    (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
    (by rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega_arith)
    (Sig.noLists_withScratch nm e n hl)).mpr ?_
  rw [narrow_regArgs hk, narrow_regArgs hk, narrow_sp, narrow_sp, hsp]
  refine ⟨rfl, fun i hi => ?_⟩
  have l₁ := regArgs_length sig s₁ (by omega_arith)
  have l₂ := regArgs_length sig s₂ (by omega_arith)
  have lp := Sig.pubs_length sig.params abi.ptrBits
  have hps : ((sig.withScratch nm e n).params.flatMap (·.2.pubs)) =
      sig.params.flatMap (·.2.pubs) ++ [true] := by
    simp [Sig.withScratch, Param.pubs]
  rw [hps] at hi
  by_cases hik : i < (sig.words abi.ptrBits).length
  · have hW : (((sig.withScratch nm e n).words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64 =
        ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64 := by
      rw [Sig.words_withScratch, List.map_append]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by rw [List.length_map]; exact hik)]
    rw [hW]
    simp only [List.getD_eq_getElem?_getD] at hi hpa ⊢
    rw [List.getElem?_append_left (by rw [l₁]; exact hik),
      List.getElem?_append_left (by rw [l₂]; exact hik)]
    rw [List.getElem?_append_left (by rw [lp]; exact hik)] at hi
    exact hpa i hi
  · simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega_arith), List.getElem?_append_right (by omega_arith), l₁, l₂]

/-- The public data of the contract without the buffer, with its leak, is
public in `narrow` for the contract with it: `narrow` keeps the memory, so
the leak is the same. -/
theorem narrow_pubL (hk : (sig.words abi.ptrBits).length < 8) {s₁ s₂ : State}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}
    (hp : (sig.contract abi pre post wa (stack + bytes) leak).pub s₁ s₂) (hl : Sig.noLists sig.params = true) :
    (Sig.scratchContract abi sig nm e n pre post wa stack leak).pub (narrow sig e n bytes s₁)
      (narrow sig e n bytes s₂) := by
  rw [pub_regsL (by omega_arith) hl] at hp
  obtain ⟨⟨hsp, hlk⟩, hpa⟩ := hp
  have hp' : (sig.contract abi pre post wa (stack + bytes)).pub s₁ s₂ :=
    (pub_regs (by omega_arith) hl).mpr ⟨hsp, hpa⟩
  have hn := (pub_regs (sig := sig.withScratch nm e n)
    (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
    (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
    (by rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega_arith)
    (Sig.noLists_withScratch nm e n hl)).mp (narrow_pub (nm := nm) hk hp' hl)
  refine (pub_regsL (sig := sig.withScratch nm e n)
    (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
    (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
    (by rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega_arith)
    (Sig.noLists_withScratch nm e n hl)).mpr ⟨⟨hn.1, ?_⟩, hn.2⟩
  have l₁ := regArgs_length sig s₁ (by omega_arith)
  have l₂ := regArgs_length sig s₂ (by omega_arith)
  rw [narrow_regArgs hk, narrow_regArgs hk, narrow_mem, narrow_mem]
  cases leak with
  | none => trivial
  | some f =>
    show Curry.apply _ (Curry.withScratch abi.ptrBits nm e n sig.params f) _ _ =
      Curry.apply _ (Curry.withScratch abi.ptrBits nm e n sig.params f) _ _
    rw [Curry.apply_withScratch abi.ptrBits nm e n sig.params f _ _ l₁,
      Curry.apply_withScratch abi.ptrBits nm e n sig.params f _ _ l₂]
    exact hlk

/-! ## The wipe -/

/-- The trace of `wipeStores words` from a state whose `t5` is `p`. -/
def wipeTrace (p : Addr) (words : Nat) : List Leak :=
  (List.range words).map fun k => .addr (p + BitVec.ofNat 64 (8 * k))

theorem wipeStores_succ (w : Nat) :
    wipeStores (w + 1) = wipeStores w ++ ([.store .d .t6 .t5 (8 * w)] : List Instr) := by
  simp only [wipeStores, List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- The stores of `wipeStores` change memory only in the region `R`, which
holds each of them and which `u` may write. -/
theorem wipeStores_run (R : Region) (u : State) (hR : R ∈ u.wr) (hal : (u.gpr .t5).toNat % 8 = 0) :
    ∀ words, 8 * words ≤ 2048 →
    (∀ k < words, R.Contains (u.gpr .t5 + BitVec.ofNat 64 (8 * k)) 8) →
    ∃ m', execBlock isa (wipeStores words) u =
        some ({ u with mem := m' }, wipeTrace (u.gpr .t5) words) ∧ Frame [R] u.mem m'
  | 0, _, _ => ⟨u.mem, rfl, Frame.refl _ _⟩
  | w + 1, hwb, hc => by
    obtain ⟨m', he, hf⟩ := wipeStores_run R u hR hal w (by omega_using [hwb])
      fun k hk => hc k (by omega_using [hk])
    have hin : InRegions ({ u with mem := m' } : State).wr (u.gpr .t5 + BitVec.ofNat 64 (8 * w)) 8 :=
      ⟨R, hR, hc w (by omega_using [])⟩
    refine ⟨m'.writeW (u.gpr .t5 + BitVec.ofNat 64 (8 * w)) (u.gpr .t6), ?_,
      hf.writeW (List.mem_singleton_self _) _ (hc w (by omega_using []))⟩
    rw [wipeStores_succ, execBlock_append, he]
    simp only [Option.bind_some, execBlock, isa,
      exec_store_d (s := { u with mem := m' }) (by omega_using [hwb])
        (Spill.al8 hal (by omega_using [])) hin,
      Option.map_some, addrs, List.map_cons, List.map_nil, List.append_nil, wipeTrace, List.range_succ,
      List.map_append]

theorem wipeTrace_add (p : Addr) (n w : Nat) :
    wipeTrace p (n + w) = wipeTrace p n ++ wipeTrace (p + BitVec.ofNat 64 (8 * n)) w := by
  rw [wipeTrace, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp_apply]
  rw [Offset.add_add, Nat.mul_add]

/-- `wipeChunks fuel words` from `u`, with the `words` doublewords at `t5`
in the region `R`, which `u` may write: it changes memory only in `R` and
of the registers only `t5`, with a trace of the addresses alone. -/
theorem wipeChunks_run (R : Region) : ∀ (fuel words : Nat) (u : State), R ∈ u.wr →
    (u.gpr .t5).toNat % 8 = 0 → words ≤ 256 * (fuel + 1) →
    (∀ k < words, R.Contains (u.gpr .t5 + BitVec.ofNat 64 (8 * k)) 8) →
    ∃ u', execBlock isa (wipeChunks fuel words) u = some (u', wipeTrace (u.gpr .t5) words) ∧
      Frame [R] u.mem u'.mem ∧ (∀ r, r ≠ .t5 → u'.gpr r = u.gpr r) ∧ u'.sp = u.sp ∧
      u'.rd = u.rd ∧ u'.wr = u.wr
  | 0, words, u, hR, hal, hw, hc => by
    obtain ⟨m', he, hf⟩ := wipeStores_run R u hR hal words (by omega_using [hw]) hc
    exact ⟨{ u with mem := m' }, he, hf, fun _ _ => rfl, rfl, rfl, rfl⟩
  | fuel + 1, words, u, hR, hal, hw, hc => by
    by_cases hle : words ≤ 256
    · obtain ⟨m', he, hf⟩ := wipeStores_run R u hR hal words (by omega_using [hle]) hc
      refine ⟨{ u with mem := m' }, ?_, hf, fun _ _ => rfl, rfl, rfl, rfl⟩
      simp only [wipeChunks, hle, ↓reduceIte]; exact he
    · obtain ⟨m', he, hf⟩ := wipeStores_run R u hR hal 256 (by decide) fun k hk => hc k (by omega_using [hk, hle])
      let u₁ : State := { u with mem := m' }
      let u₂ : State := u₁.write .t5 (u₁.gpr .t5 + BitVec.ofInt 64 1024)
      let u₃ : State := u₂.write .t5 (u₂.gpr .t5 + BitVec.ofInt 64 1024)
      have e₂ : execBlock isa ([.addi .t5 .t5 1024, .addi .t5 .t5 1024] : List Instr) u₁ = some (u₃, []) := by
        simp only [execBlock, isa, exec_addi (show imm12 (1024 : Int) by decide), addrs, List.map_nil,
          Option.map_some, List.nil_append]
        rfl
      have h5 : u₃.gpr .t5 = u.gpr .t5 + BitVec.ofNat 64 2048 := by
        simp only [u₃, u₂, u₁, RegUpd.gpr_write_self]
        rw [show BitVec.ofInt 64 1024 = BitVec.ofNat 64 1024 from rfl, Offset.add_add]
      have ho : ∀ r, r ≠ .t5 → u₃.gpr r = u.gpr r := fun r hr => by
        simp only [u₃, u₂, u₁, RegUpd.gpr_write_of_ne _ _ hr]
      obtain ⟨u', e', f', o', sp', rd', wr'⟩ := wipeChunks_run R fuel (words - 256) u₃ hR
        (by rw [h5]; exact Spill.al8 hal (by decide)) (by omega_using [hw])
        (fun k hk => by
          rw [h5, Offset.add_add, show 2048 + 8 * k = 8 * (256 + k) by omega]
          exact hc (256 + k) (by omega_using [hk]))
      refine ⟨u', ?_, (hf.trans f' : Frame [R] u.mem u'.mem), fun r hr => by rw [o' r hr, ho r hr],
        sp', rd', wr'⟩
      simp only [wipeChunks, hle, ↓reduceIte]
      rw [execBlock_append, execBlock_append, he]
      simp only [Option.bind_some]
      rw [e₂]
      simp only [Option.bind_some, Option.map_some, e', h5]
      rw [show words = 256 + (words - 256) by omega_using [hle], wipeTrace_add, Nat.add_sub_cancel_left,
        List.append_nil]

/-- `wipe words` from `u`, with the `words` doublewords at `sp` in the region
`R`, which `u` may write: it sets `t5` and `t6`, and changes memory only in
`R`, with a trace of the addresses alone. -/
theorem wipe_run (R : Region) (u : State) (words : Nat) (hR : R ∈ u.wr)
    (hal : u.sp.toNat % 8 = 0)
    (hc : ∀ k < words, R.Contains (u.sp + BitVec.ofNat 64 (8 * k)) 8) :
    ∃ u', execBlock isa (wipe words) u = some (u', wipeTrace u.sp words) ∧
      Frame [R] u.mem u'.mem ∧ (∀ r, r ≠ .t5 → r ≠ .t6 → u'.gpr r = u.gpr r) ∧ u'.sp = u.sp ∧
      u'.rd = u.rd ∧ u'.wr = u.wr := by
  have h5 : ((u.write .t5 (u.sp + BitVec.ofNat 64 0)).write .t6 (BitVec.ofInt 64 0)).gpr .t5 = u.sp := by
    simp [State.write]
  obtain ⟨u', he, hf, ho, sp', rd', wr'⟩ := wipeChunks_run R (words / 256) words
    ((u.write .t5 (u.sp + BitVec.ofNat 64 0)).write .t6 (BitVec.ofInt 64 0))
    (by simpa [State.write]) (by rw [h5]; exact hal) (by omega) (by rw [h5]; exact hc)
  refine ⟨u', ?_, by simpa [State.write] using hf, fun r h5' h6 => ?_, by rw [sp']; rfl,
    by rw [rd']; rfl, by rw [wr']; rfl⟩
  · simp only [wipe, execBlock, isa, exec, show (0 : Nat) < 2048 by decide, ↓reduceIte]
    simp only [show imm12 (0 : Int) = true by decide, ↓reduceIte, Option.map_some, he, h5, addrs,
      List.map_nil, List.nil_append]
  · rw [ho r h5']; simp [State.write, h5', h6]

/-- The state after the frame's `free`, from the state `s₄` the code and the
wipe end in (with the permissions of `narrow`) when they start in `s`. -/
def popState (bytes : Nat) (s s₄ : State) : State :=
  { s₄.withRegions s.rd (⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) with sp := s.sp, wr := s.wr }

/-- A run of the code and the wipe from `narrow s` is a run of
`withStackScratchWiped` from `s` (with the same trace), which keeps what the
calling convention requires, and whose memory and registers are those of
that run, from the one fact about `s` it needs: the frame fits below its
stack pointer. -/
theorem withStackScratch_runSp {c : Prog isa} (hk : (sig.words abi.ptrBits).length < 8)
    (hb : 0 < bytes ∧ bytes ≤ 4064 ∧ bytes % 16 = 0 ∧ n * e.size ≤ bytes) {s : State}
    (hsb : bytes ≤ s.sp.toNat) {t : List Leak} {s₄ : State}
    (he : Exec isa c (narrow sig e n bytes s) t s₄) (ha : abiPreserved (narrow sig e n bytes s) s₄) :
    Exec isa (withStackScratch bytes (scratchReg sig) c) s t (popState bytes s s₄) ∧
      abiPreserved s (popState bytes s s₄) ∧ (popState bytes s s₄).mem = s₄.mem ∧
      (popState bytes s s₄).gpr = s₄.gpr := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := hb
  obtain ⟨hr2, hra, -⟩ := argRegs_scratch _ hk
  have hpush : isa.push (.alloc bytes) s = some (allocd bytes s) := by
    show push (.alloc bytes) s = some (allocd bytes s)
    unfold push
    exact ite_eq_left_of_eq_true _ _ (eq_true ⟨hb0, hb1, hb2, by omega_arith⟩) |>.trans rfl
  have hblk : Exec isa (.block [.addSp (scratchReg sig) 0]) (allocd bytes s) [] (scratchState sig bytes s) :=
    .block (by
      simp only [execBlock, isa, exec_addSp (show (0 : Nat) < 2048 by decide), Option.map_some, addrs,
        List.map_nil, List.append_nil, scratchState, BitVec.add_zero]
      rfl)
  have hcov : Covers (s.wr ++ [⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩])
      (⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) := by
    rintro a k ⟨r, hr, hc⟩
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_cons_of_mem _ hr, hc⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., by simp only [Region.Contains] at hc ⊢; omega_arith⟩
  have hcov' : Covers (s.rd ++ (s.wr ++ [⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩]))
      (s.rd ++ (⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)) := by
    rintro a k ⟨r, hr, hc⟩
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, hc⟩
    · obtain ⟨r', hr', hc'⟩ := hcov a k ⟨r, hr, hc⟩
      exact ⟨r', List.mem_append_right _ hr', hc'⟩
  have hw := Exec.widen he (rd := s.rd) (wr := ⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) hcov' hcov
  rw [show (narrow sig e n bytes s).withRegions s.rd (⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) =
      scratchState sig bytes s from rfl] at hw
  have hsp₄ : s₄.sp = s.sp - BitVec.ofNat 64 bytes := ha.2.1.trans (narrow_sp s)
  have hpop : isa.pop (.free bytes) (allocd bytes s)
      (s₄.withRegions s.rd (⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)) =
        some (popState bytes s s₄) := by
    simp only [isa, pop, State.withRegions, allocd, hsp₄, List.head?_cons, List.tail_cons, hb0,
      hb1, hb2, and_self, ite_true, BitVec.sub_add_cancel]
    rfl
  have hex := Exec.frame hpush (Exec.seq hblk hw) hpop
  simp only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] at hex
  refine ⟨hex, ⟨fun q hq => ?_, rfl, ?_⟩, rfl, rfl⟩
  · have hqr : q ≠ scratchReg sig := fun h => hr2 (by subst h; exact hq)
    show s₄.gpr q = s.gpr q
    rw [ha.1 q hq, narrow_gpr]
    simp only [hqr, ↓reduceIte]
  · show s₄.gpr .ra = s.gpr .ra
    rw [ha.2.2, narrow_gpr]
    simp only [show Reg.ra ≠ scratchReg sig from fun h => hra h.symm, ↓reduceIte]

/-- `withStackScratch_runSp`, from the precondition. -/
theorem withStackScratch_run {c : Prog isa} (hk : (sig.words abi.ptrBits).length < 8)
    (hb : 0 < bytes ∧ bytes ≤ 4064 ∧ bytes % 16 = 0 ∧ n * e.size ≤ bytes) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes)).pre s) {t : List Leak} {s₄ : State}
    (he : Exec isa c (narrow sig e n bytes s) t s₄) (ha : abiPreserved (narrow sig e n bytes s) s₄)
    (hl : Sig.noLists sig.params = true) :
    Exec isa (withStackScratch bytes (scratchReg sig) c) s t (popState bytes s s₄) ∧
      abiPreserved s (popState bytes s s₄) ∧ (popState bytes s s₄).mem = s₄.mem ∧
      (popState bytes s s₄).gpr = s₄.gpr := by
  rw [pre_regs (by omega_using [hk]) hl] at hs
  obtain ⟨⟨-, hwf⟩, -, -, -, -, -, -⟩ := hs
  exact withStackScratch_runSp hk hb (by rcases hwf with h | h <;> omega_using [h, hb]) he ha

/-- Code verified for a function whose last argument, in a register, is a
scratch buffer of `n` elements `e`, with `stack` bytes of stack, is verified
for the function without it, which allocates the buffer in a frame of
`bytes` more bytes of stack and zeroes its first `words` doublewords after
the code (`withStackScratchWiped`), if its postcondition reads the memory on
return only within the function's buffers (`hpostOut`). -/
theorem Verified.stackScratchWiped {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack))
    (hk : (sig.words abi.ptrBits).length < 8)
    (hb : 0 < bytes ∧ bytes ≤ 4064 ∧ bytes % 16 = 0 ∧ n * e.size ≤ bytes)
    (hw : 8 * words ≤ n * e.size)
    (hpostOut : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes)).pre s)
    (hl : Sig.noLists sig.params = true := by decide) :
    Verified target (withStackScratchWiped bytes (scratchReg sig) words c)
      (sig.contract abi pre post wa (stack + bytes)) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hlen := regArgs_length sig
  -- The buffer, below the stack the contract without it reserves, so apart
  -- from the function's buffers.
  have hdisj : ∀ s, (sig.contract abi pre post wa (stack + bytes)).pre s →
      ∀ b ∈ Sig.bufs sig.params (regArgs sig s),
        b.1.Disjoint ⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩ := by
    intro s hs b hb'
    rw [pre_regs (by omega_using [hk]) hl] at hs
    obtain ⟨-, -, -, -, hres, -, -⟩ := hs
    have hbelow : below s.sp (stack + bytes) ∈ stackBelow s.sp (stack + bytes) := by
      rw [stackBelow_pos _ (by omega_using [hb])]; simp
    exact ((hres _ hbelow b hb').sub_left (buf_sub (stack := stack) s hb.2.2.2)).symm
  -- Every run is the code's run from `narrow`, then the wipe.
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes)).pre s → ∃ t s₃ s₄,
      Exec isa c (narrow sig e n bytes s) t s₃ ∧
      (Sig.scratchContract abi sig nm e n pre post wa stack).post (narrow sig e n bytes s) s₃ ∧
      Frame [⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩] s₃.mem s₄.mem ∧
      s₃.sp = s.sp - BitVec.ofNat 64 bytes ∧
      Exec isa (withStackScratchWiped bytes (scratchReg sig) words c) s
        (t ++ wipeTrace s₃.sp words) (popState bytes s s₄) ∧
      abiPreserved s (popState bytes s s₄) ∧ (popState bytes s s₄).mem = s₄.mem ∧
      (popState bytes s s₄).gpr .a0 = s₃.gpr .a0 := by
    intro s hs
    have hal : s.sp.toNat % 16 = 0 := ((pre_regs (by omega_using [hk]) hl).mp hs).1.1
    have hwf := ((pre_regs (by omega_using [hk]) hl).mp hs).1.2
    have hsb : bytes ≤ s.sp.toNat := by rcases hwf with h | h <;> omega_using [h, hb]
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrow_pre hk hb hs hl)
    have hsp₃ : s₃.sp = s.sp - BitVec.ofNat 64 bytes := ha.2.1.trans (narrow_sp s)
    have hwr₃ : s₃.wr = (narrow sig e n bytes s).wr := (Exec.rdwr he).2.1
    obtain ⟨u', hblk, hfr, hu', hsp', -⟩ := wipe_run ⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩ s₃ words
      (by rw [hwr₃, narrow_wr]; simp)
      (by rw [hsp₃, toNat_sub_ofNat' hsb]; omega_using [hal, hb])
      (fun k hk' => by
        rw [hsp₃]; exact Offset.contains_base _ (by omega_using [hw, hk']) (by omega_using [hb, hw, hk']))
    have he' := Exec.seq he (Exec.block hblk)
    have ha' : abiPreserved (narrow sig e n bytes s) u' := by
      refine ⟨fun q hq => ?_, hsp'.trans ha.2.1, ?_⟩
      · have h5 : q ≠ .t5 := by rintro rfl; simp [preserved] at hq
        have h6 : q ≠ .t6 := by rintro rfl; simp [preserved] at hq
        rw [hu' q h5 h6]
        exact ha.1 q hq
      · rw [hu' _ (by decide) (by decide)]
        exact ha.2.2
    obtain ⟨hex, habi, hm, hg⟩ := withStackScratch_run hk hb (by exact hs) he' ha' hl
    refine ⟨t, s₃, _, he, hq, hfr, hsp₃, hex, habi, hm, ?_⟩
    rw [hg]; exact hu' _ (by decide) (by decide)
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, s₄, -, hq, hfr, -, hex, ha, hm, hr0⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    rw [post_regs (by omega_using [hk])]
    have hq' := (post_regs (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
      (by rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega_using [hk])).mp hq
    rw [narrow_regArgs hk] at hq'
    rw [hm, hr0]
    have h₃ := Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params
      post _ _ (hlen s (by omega_using [hk]))) _) s₃.mem) _) hq'
    -- The memory on return: after the wipe, which writes only the buffer.
    refine hpostOut _ _ _ _ _ (hlen s (by omega_using [hk])) (fun b hb' a ha' => ?_) h₃
    exact (hfr a fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hdisj s hs b hb' a ha').symm
  · obtain ⟨u₁, _, _, f₁, _, _, p₁, x₁, _⟩ := hrun s₁ h₁
    obtain ⟨u₂, _, _, f₂, _, _, p₂, x₂, _⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1, p₁, p₂]
    have hsp₁₂ : s₁.sp = s₂.sp := ((pub_regs (by omega_using [hk]) hl).mp hp).1
    rw [hct _ _ _ _ _ _ (narrow_pre hk hb h₁ hl) (narrow_pre hk hb h₂ hl) (narrow_pub hk hp hl) f₁ f₂,
      hsp₁₂]

/-- Code verified for a function whose last argument, in a register, is a
scratch buffer of `n` elements `e`, with `stack` bytes of stack, is verified
for the function without it, which allocates the buffer in a frame of
`bytes` more bytes of stack (`withStackScratch`), with any leak: the frame's
`alloc` writes no memory, so the precondition, postcondition and leak see
the memory they do without it. -/
theorem Verified.stackScratchL {c : Prog isa}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack leak))
    (hk : (sig.words abi.ptrBits).length < 8)
    (hb : 0 < bytes ∧ bytes ≤ 4064 ∧ bytes % 16 = 0 ∧ n * e.size ≤ bytes)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes) leak).pre s)
    (hl : Sig.noLists sig.params = true := by decide) :
    Verified target (withStackScratch bytes (scratchReg sig) c)
      (sig.contract abi pre post wa (stack + bytes) leak) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hlen := regArgs_length sig
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes)).pre s → ∃ t s₃,
      Exec isa c (narrow sig e n bytes s) t s₃ ∧
      (Sig.scratchContract abi sig nm e n pre post wa stack).post (narrow sig e n bytes s) s₃ ∧
      Exec isa (withStackScratch bytes (scratchReg sig) c) s t (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr = s₃.gpr := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrow_pre hk hb hs hl)
    exact ⟨t, s₃, he, hq, withStackScratch_run hk hb hs he ha hl⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, -, hq, hex, ha, hm, hg⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    show (sig.contract abi pre post wa (stack + bytes)).post s _
    rw [post_regs (by omega_using [hk])]
    have hq' := (post_regs (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
      (by rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega_using [hk])).mp hq
    rw [narrow_regArgs hk] at hq'
    rw [hm, hg]
    exact Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params
      post _ _ (hlen s (by omega_using [hk]))) _) s₃.mem) _) hq'
  · obtain ⟨u₁, r₁, f₁, -, x₁, -⟩ := hrun s₁ h₁
    obtain ⟨u₂, r₂, f₂, -, x₂, -⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1]
    exact hct _ _ _ _ _ _ (narrow_pre (post := post) hk hb h₁ hl) (narrow_pre (post := post) hk hb h₂ hl) (narrow_pubL hk hp hl) f₁ f₂

end

end VG.RISCV64
