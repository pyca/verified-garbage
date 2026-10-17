module

public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchWipe
public import VerifiedGarbage.Impl.StackScratch.X86_64Slots

/-!
# A scratch buffer on the stack, chosen slots of it wiped after use (x86-64)

`Wiper.slots`: `wipeSlots`, which zeroes a register (`Zero.instr`, `zero_run`, which
writes nothing but vector registers) and stores it to slots of the buffer,
is a `Wiper`, whose trace is the slots' addresses; so
`Verified.stackArgScratchWipedSlots` is `Verified.stackArgScratchWipedBy`
for it.
-/

@[expose] public section

namespace VG.X86_64

open VG.Impl.StackScratch.X86_64

/-- Zeroing the register keeps all but the vector registers, and leaks
nothing. -/
theorem zero_run (z : Zero) (u : State) :
    ∃ u', execBlock isa [z.instr] u = some (u', []) ∧ u'.gpr = u.gpr ∧ u'.mem = u.mem ∧
      u'.mxcsr = u.mxcsr ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  cases z <;> exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The trace of the stores of `wipeSlots` from a state whose `rsp` is `sp`. -/
def slotsTrace (sp : Addr) (off : Nat) (ss : List Slot) : List Leak :=
  ss.map fun s => .addr (sp + BitVec.ofNat 64 (off + s.disp))

/-- A slot's store, inside a region `R` that `u` may write: it changes
memory only in `R`. -/
theorem Slot.instr_run (R : Region) (u : State) (off : Nat) (hR : R ∈ u.wr) (s : Slot)
    (hc : R.Contains (u.gpr .rsp + BitVec.ofNat 64 (off + s.disp)) s.size) :
    ∃ m', execBlock isa [s.instr off] u =
        some ({ u with mem := m' }, [.addr (u.gpr .rsp + BitVec.ofNat 64 (off + s.disp))]) ∧
      Frame [R] u.mem m' := by
  have hin : InRegions u.wr (u.gpr .rsp + BitVec.ofNat 64 (off + s.disp)) s.size := ⟨R, hR, hc⟩
  cases s with
  | x d =>
    refine ⟨u.mem.writeW (u.gpr .rsp + BitVec.ofNat 64 (off + d)) (u.xmm .xmm0), ?_,
      (Frame.refl [R] u.mem).writeW (List.mem_singleton_self _) _ hc⟩
    simp only [Slot.disp, Slot.size] at hin
    simp only [Slot.instr, Slot.disp, execBlock, isa, exec, State.store128, State.ea, BitVec.ofInt_natCast,
      hin, ↓reduceIte, Option.map_some, addrs, List.map_cons, List.map_nil, List.append_nil]
  | v16 d =>
    refine ⟨u.mem.writeW (u.gpr .rsp + BitVec.ofNat 64 (off + d)) (u.xmm .xmm0), ?_,
      (Frame.refl [R] u.mem).writeW (List.mem_singleton_self _) _ hc⟩
    simp only [Slot.disp, Slot.size] at hin
    simp only [Slot.instr, Slot.disp, execBlock, isa, exec, State.store128, State.ea, BitVec.ofInt_natCast,
      hin, ↓reduceIte, Option.map_some, addrs, List.map_cons, List.map_nil, List.append_nil]
  | v32 d =>
    refine ⟨u.mem.writeW (u.gpr .rsp + BitVec.ofNat 64 (off + d)) (u.ymm .xmm0), ?_,
      (Frame.refl [R] u.mem).writeW (List.mem_singleton_self _) _ hc⟩
    simp only [Slot.disp, Slot.size] at hin
    simp only [Slot.instr, Slot.disp, execBlock, isa, exec, State.store256, State.ea, BitVec.ofInt_natCast,
      hin, ↓reduceIte, Option.map_some, addrs, List.map_cons, List.map_nil, List.append_nil]
  | z d =>
    refine ⟨u.mem.writeW (u.gpr .rsp + BitVec.ofNat 64 (off + d)) (u.zmm .xmm0), ?_,
      (Frame.refl [R] u.mem).writeW (List.mem_singleton_self _) _ hc⟩
    simp only [Slot.disp, Slot.size] at hin
    simp only [Slot.instr, Slot.disp, execBlock, isa, exec, State.store512, State.ea, BitVec.ofInt_natCast,
      hin, ↓reduceIte, Option.map_some, addrs, List.map_cons, List.map_nil, List.append_nil]

/-- The stores of `wipeSlots`, each inside `R`. -/
theorem slots_run (R : Region) (u : State) (off : Nat) (hR : R ∈ u.wr) : ∀ ss : List Slot,
    (∀ s ∈ ss, R.Contains (u.gpr .rsp + BitVec.ofNat 64 (off + s.disp)) s.size) →
    ∃ m', execBlock isa (ss.map (·.instr off)) u =
        some ({ u with mem := m' }, slotsTrace (u.gpr .rsp) off ss) ∧ Frame [R] u.mem m'
  | [], _ => ⟨u.mem, rfl, Frame.refl _ _⟩
  | s :: ss, hc => by
    obtain ⟨m₁, he₁, hf₁⟩ := Slot.instr_run R u off hR s (hc s (List.mem_cons_self ..))
    obtain ⟨m', he, hf⟩ := slots_run R { u with mem := m₁ } off hR ss
      fun s' hs' => hc s' (List.mem_cons_of_mem _ hs')
    refine ⟨m', ?_, hf₁.trans hf⟩
    rw [List.map_cons, show ∀ (i : Instr) is, (i :: is) = [i] ++ is from fun _ _ => rfl,
      execBlock_append, he₁]
    simp only [Option.bind_some]
    rw [he]
    simp [slotsTrace]

/-- `wipeSlots`, for slots within the buffer's first `len` bytes. -/
def Wiper.slots (z : Zero) (ss : List Slot) (len : Nat) (h : ∀ s ∈ ss, s.disp + s.size ≤ len) : Wiper where
  code off := wipeSlots z off ss
  len := len
  trace sp off := slotsTrace sp off ss
  run R u off hR hc := by
    obtain ⟨u₁, he₁, g₁, m₁, x₁, rd₁, wr₁⟩ := zero_run z u
    obtain ⟨m', he, hf⟩ := slots_run R u₁ off (by rw [wr₁]; exact hR) ss fun s hs => by
      rw [g₁]; exact hc s.disp s.size (h s hs)
    refine ⟨{ u₁ with mem := m' }, ?_, by rw [← m₁]; exact hf, fun r _ => by simp [g₁], x₁, rd₁, wr₁⟩
    rw [wipeSlots, show ∀ (i : Instr) is, (i :: is) = [i] ++ is from fun _ _ => rfl, execBlock_append, he₁]
    simp only [Option.bind_some]
    rw [he, g₁]
    simp
  spSafe off := by
    simp only [wipeSlots, List.all_cons, List.all_map]
    cases z <;> simp [Zero.instr, Instr.dst, List.all_eq_true, Function.comp_def] <;>
      intro s _ <;> cases s <;> simp [Slot.instr]

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {stack bytes : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- `Verified.stackArgScratchWipedBy`, for `withStackArgScratchWipedSlots`,
whose slots lie in the buffer's first `len` bytes. -/
theorem Verified.stackArgScratchWipedSlots (z : Zero) (ss : List Slot) {len : Nat}
    (hss : ∀ s ∈ ss, s.disp + s.size ≤ len) {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack leak))
    (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + n * e.size ≤ bytes ∧ bytes < 4096 ∧ bytes % 8 = 0)
    (hst : stack + bytes + 8 ≤ 2 ^ 64)
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ stack)
    (hw : len ≤ n * e.size)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' r →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' r)
    (hpostOut : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes) leak).pre s)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak := by trivial) :
    Verified target (withStackArgScratchWipedSlots bytes (nStack sig) z ss c)
      (sig.contract abi pre post wa (stack + bytes) leak) :=
  Verified.stackArgScratchWipedBy (Wiper.slots z ss len hss) h hk hb hst hsp hd hw hpre hpost hpostOut hsat
    hleak

/-- `Verified.stackArgScratchWipedSlots`, for `withStackArgScratchSlots`:
with no slots, `Verified.stackArgScratch`. -/
theorem Verified.stackArgScratchSlots (z : Zero) (ss : List Slot) {len : Nat}
    (hss : ∀ s ∈ ss, s.disp + s.size ≤ len) {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack leak))
    (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + n * e.size ≤ bytes ∧ bytes < 4096 ∧ bytes % 8 = 0)
    (hst : stack + bytes + 8 ≤ 2 ^ 64)
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ stack)
    (hw : len ≤ n * e.size)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' r →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' r)
    (hpostOut : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes) leak).pre s)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak := by trivial) :
    Verified target (withStackArgScratchSlots bytes (nStack sig) z ss c)
      (sig.contract abi pre post wa (stack + bytes) leak) := by
  unfold withStackArgScratchSlots
  split
  · exact Verified.stackArgScratch h hk hb hst hsp hd hpre hpost hsat hleak
  · exact Verified.stackArgScratchWipedSlots z ss hss h hk hb hst hsp hd hw hpre hpost hpostOut hsat hleak

/-- `Verified.stackArgScratchSlots`, for a precondition and postcondition
that may also read the lists in memory (`Verified.stackArgScratchL`). -/
theorem Verified.stackArgScratchSlotsL (z : Zero) (ss : List Slot) {len : Nat}
    (hss : ∀ s ∈ ss, s.disp + s.size ≤ len) {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack leak))
    (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + n * e.size ≤ bytes ∧ bytes < 4096 ∧ bytes % 8 = 0)
    (hst : stack + bytes + 8 ≤ 2 ^ 64)
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ stack)
    (hw : len ≤ n * e.size)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      (∀ r ∈ Sig.lists abi.ptrBits m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      (∀ r ∈ Sig.lists abi.ptrBits m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' r →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' r)
    (hpostOut : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes) leak).pre s)
    (hleak : Sig.LeakLocalL abi.ptrBits sig leak := by trivial) :
    Verified target (withStackArgScratchSlots bytes (nStack sig) z ss c)
      (sig.contract abi pre post wa (stack + bytes) leak) := by
  unfold withStackArgScratchSlots
  split
  · exact Verified.stackArgScratchL h hk hb hst hsp hd hpre hpost hsat hleak
  · exact Verified.stackArgScratchWipedByL (Wiper.slots z ss len hss) h hk hb hst hsp hd hw hpre hpost hpostOut
      hsat hleak

/-- `withStackArgScratchWipedSlots` writes `rsp` only in its frame if its
code does. -/
theorem withStackArgScratchWipedSlots_spSafe {bytes m : Nat} {z : Zero} {ss : List Slot} {c : Prog isa}
    (h : c.all (fun i => !isa.writesSp i) = true) :
    (withStackArgScratchWipedSlots bytes m z ss c).all (fun i => !isa.writesSp i) = true :=
  withStackArgScratch_spSafe (by
    simp only [Code.all, h, Bool.true_and]
    exact (Wiper.slots z ss (ss.foldr (fun s l => max (s.disp + s.size) l) 0) fun s hs => by
      induction ss with
      | nil => cases hs
      | cons t ts ih =>
        simp only [List.foldr_cons]
        rcases List.mem_cons.mp hs with rfl | hs
        · exact Nat.le_max_left _ _
        · exact Nat.le_trans (ih hs) (Nat.le_max_right _ _)).spSafe _)

/-- So does `withStackArgScratchSlots`. -/
theorem withStackArgScratchSlots_spSafe {bytes m : Nat} {z : Zero} {ss : List Slot} {c : Prog isa}
    (h : c.all (fun i => !isa.writesSp i) = true) :
    (withStackArgScratchSlots bytes m z ss c).all (fun i => !isa.writesSp i) = true := by
  unfold withStackArgScratchSlots
  split
  · exact withStackArgScratch_spSafe h
  · exact withStackArgScratchWipedSlots_spSafe h

end

end VG.X86_64
