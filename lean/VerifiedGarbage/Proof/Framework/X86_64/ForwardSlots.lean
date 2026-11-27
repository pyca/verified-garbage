module

public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineN
public import VerifiedGarbage.Proof.Framework.X86_64.Inline
public import VerifiedGarbage.Proof.Framework.X86_64.ForwardCall
public import VerifiedGarbage.Impl.ForwardCall.X86_64Slots
public import VerifiedGarbage.TCB.Registration
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-!
# A function that calls its callees through slots (x86-64)

A function `c` whose calls of the functions `fns` are indirect calls of one
function each, through read-only slots `[rsp + disp]` above its stack
arguments (`Code.InlineOkNS`, `CallInlineN.lean`), can be shared by callers
that call different functions: each caller stores the addresses of its
callees in the slots.

`c`'s contract is `K.withSlots m fns`: `K`, for a function with `m` stack
arguments, with one more read-only region last in `rd`, the `8 * fns.length`
bytes above the stack arguments, holding the addresses of `fns`, on which
two runs agree. Its proof is `K`'s of `c.inlineAll` (`SlotVerified.of_inline`):
inlined, `c` reads no slot, so it runs from the state without the slots'
region (`dropSlot`) as it does with it (`Exec.widen`).

Its callers call it by `forwardS` (`Impl/ForwardCall/X86_64Slots.lean`),
which copies their stack arguments into a frame, as `forward` does
(`ForwardCall.lean`), and stores the addresses of `fns` above them:
`Verified.forwardS` gives the caller the callee's contract, for the stack the
frame adds, with the addresses of `fns` public (`Abi.withFns`), on which the
callee's constant time depends. The callee runs with its buffers, the copies
and the slots (`slotEntry`), the copies and slots read only.
-/

@[expose] public section

namespace VG.X86_64

/-! ## The slots' contract -/

/-- The slots of the functions `fns`, from the word above the `m` stack
arguments up. -/
def slotsOf (m : Nat) (fns : List String) : List (Int × String) :=
  fns.zipIdx.map fun p => (((8 * (m + 1 + p.2) : Nat) : Int), p.1)

/-- The slots' region: the `8 k` bytes above the `m` stack arguments. -/
def slotRegion (m k : Nat) (s : State) : Region := ⟨s.gpr .rsp + BitVec.ofNat 64 (8 * (m + 1)), 8 * k⟩

/-- `s` without its last read-only region, the slots'. -/
def dropSlot (s : State) : State := s.withRegions s.rd.dropLast s.wr

@[simp] theorem dropSlot_gpr (s : State) : (dropSlot s).gpr = s.gpr := rfl
@[simp] theorem dropSlot_mem (s : State) : (dropSlot s).mem = s.mem := rfl
@[simp] theorem dropSlot_mxcsr (s : State) : (dropSlot s).mxcsr = s.mxcsr := rfl
@[simp] theorem dropSlot_syms (s : State) : (dropSlot s).syms = s.syms := rfl
@[simp] theorem dropSlot_unknowns (s : State) : (dropSlot s).unknowns = s.unknowns := rfl

/-- `K` for a function that finds the addresses of `fns` in slots above its
`m` stack arguments, a read-only region last in `rd`. -/
def _root_.VG.Contract.withSlots (K : Contract isa) (m : Nat) (fns : List String) : Contract isa where
  pre s := s.rd.getLast? = some (slotRegion m fns.length s) ∧ K.pre (dropSlot s) ∧
    SlotsOk (slotsOf m fns) (s.gpr .rsp) s
  post s s' := K.post (dropSlot s) (dropSlot s')
  pub s₁ s₂ := K.pub (dropSlot s₁) (dropSlot s₂) ∧ ∀ n ∈ fns, s₁.syms n = s₂.syms n

/-- What a function verified against `K.withSlots m fns` gives: its runs, and
constant time. (Its contract need not be satisfiable: only its callers'
are.) -/
def SlotVerified (c : Prog isa) (K : Contract isa) (m : Nat) (fns : List String) : Prop :=
  (∀ s, (K.withSlots m fns).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧
    (K.withSlots m fns).post s s') ∧
  ConstantTime isa (K.withSlots m fns).pre (K.withSlots m fns).pub c

theorem dropLast_append_getLast {l : List Region} {r : Region} (h : l.getLast? = some r) :
    l = l.dropLast ++ [r] := by
  have hne : l ≠ [] := by rintro rfl; simp at h
  rw [List.getLast?_eq_some_getLast hne] at h
  obtain rfl := Option.some.inj h
  exact (List.dropLast_concat_getLast hne).symm

theorem dropSlot_widen (s : State) : (dropSlot s).withRegions s.rd s.wr = s := rfl

theorem covers_dropSlot (s : State) : Covers ((dropSlot s).rd ++ (dropSlot s).wr) (s.rd ++ s.wr) :=
  fun _ _ ⟨r, hr, hc⟩ => ⟨r, by
    rcases List.mem_append.mp hr with h | h
    · exact List.mem_append_left _ (List.dropLast_subset _ h)
    · exact List.mem_append_right _ h, hc⟩

theorem covers_refl (rs : List Region) : Covers rs rs := fun _ _ h => h

/-- The slots' region lies above the return address's hole. -/
theorem slotRegion_hole {m k : Nat} (s : State) (h : 8 + 8 * (m + 1) + 8 * k ≤ 2 ^ 64) :
    (slotRegion m k s).Disjoint (holeN (s.gpr .rsp) 1) :=
  Offset.disjoint_below _ (n := 8) (d := 8 * (m + 1)) (k := 8 * k) h

/-- The hole is clear of `s`'s regions if it is of `dropSlot s`'s and of the slots'. -/
theorem clear_of_dropSlot {s : State} {r : Region} (hl : s.rd.getLast? = some r)
    (hc : Clear (holeN (s.gpr .rsp) 1) (dropSlot s)) (hr : r.Disjoint (holeN (s.gpr .rsp) 1)) :
    Clear (holeN (s.gpr .rsp) 1) s := by
  intro q hq
  rw [dropLast_append_getLast hl] at hq
  simp only [List.mem_append, List.mem_singleton] at hq
  rcases hq with (hq | rfl) | hq
  · exact hc q (List.mem_append_left _ hq)
  · exact hr
  · exact hc q (List.mem_append_right _ hq)

/-- A run of `c.inlineAll` from `dropSlot s` is one from `s`. -/
theorem exec_of_dropSlot {c : Prog isa} {s b : State} {t : List Leak} (h : Exec isa c (dropSlot s) t b) :
    Exec isa c s t (b.withRegions s.rd s.wr) := by
  have := Exec.widen h (rd := s.rd) (wr := s.wr) (covers_dropSlot s) (covers_refl _)
  rwa [dropSlot_widen] at this

theorem dropSlot_withRegions {s b : State} (h : b.rd = (dropSlot s).rd) (hw : b.wr = s.wr) :
    dropSlot (b.withRegions s.rd s.wr) = b := by
  have h' : s.rd.dropLast = b.rd := h.symm
  simp only [dropSlot, State.withRegions_withRegions, State.withRegions_rd, State.withRegions_wr]
  rw [h', ← hw]
  rfl

/-- `SlotVerified` of `c` from the proofs of its inlined code against a
contract `k₀` that `K` implies: as `Verified.of_inlineAllS`, with one level
of calls. -/
theorem SlotVerified.of_inline {c : Prog isa} {m : Nat} {fns : List String}
    (hc : c.InlineOkNS (slotsOf m fns) 1 = true) (hm : 8 + 8 * (m + 1) + 8 * fns.length ≤ 2 ^ 64)
    {k₀ K : Contract isa}
    (hcor : ∀ s, k₀.pre s → ∃ t s', Exec isa c.inlineAll s t s' ∧ abiPreserved s s' ∧ k₀.post s s')
    (hct : ConstantTime isa k₀.pre k₀.pub c.inlineAll) (himp : k₀.Implies K)
    (hclear : ∀ s, K.pre s → Clear (holeN (s.gpr .rsp) 1) s)
    (hrsp : ∀ s₁ s₂, K.pre s₁ → K.pre s₂ → K.pub s₁ s₂ → s₁.gpr .rsp = s₂.gpr .rsp)
    (hpatch : ∀ s b hv u, k₀.pre s → Clear (holeN (s.gpr .rsp) 1) s → k₀.post s b →
      k₀.post s (b.patch (holeN (s.gpr .rsp) 1) hv u)) :
    SlotVerified c K m fns := by
  have hD : 8 * 1 < 2 ^ 64 := by decide
  -- Every state of the contract runs `c.inlineAll`, as from `dropSlot s`.
  have hrun : ∀ s, (K.withSlots m fns).pre s → ∃ t b, Exec isa c.inlineAll (dropSlot s) t b ∧
      abiPreserved (dropSlot s) b ∧ k₀.post (dropSlot s) b := fun s hs => hcor _ (himp.pre _ hs.2.1)
  have hcl : ∀ s, (K.withSlots m fns).pre s → Clear (holeN (s.gpr .rsp) 1) s := fun s hs =>
    clear_of_dropSlot hs.1 (hclear _ hs.2.1) (slotRegion_hole s hm)
  refine ⟨fun s hs => ?_, ?_⟩
  · obtain ⟨t, b, he, ha, hp⟩ := hrun s hs
    have hw := exec_of_dropSlot he
    obtain ⟨hv, u, ta, he', -, -⟩ := Exec.of_inlineAllS hc hD hw (hcl s hs) hs.2.2
    have hb := Exec.rdwr he
    refine ⟨ta, _, he', abiPreserved_patchN hD hv u ha, ?_⟩
    show K.post (dropSlot s) (dropSlot ((b.withRegions s.rd s.wr).patch _ hv u))
    have e : dropSlot ((b.withRegions s.rd s.wr).patch (holeN (s.gpr .rsp) 1) hv u) =
        b.patch (holeN ((dropSlot s).gpr .rsp) 1) hv u := by
      rw [← dropSlot_withRegions (s := s) (b := b) hb.1 hb.2]
      rfl
    rw [e]
    exact himp.post _ _ hs.2.1 (hpatch _ b hv u (himp.pre _ hs.2.1) (hclear _ hs.2.1) hp)
  · refine ConstantTime.of_inlineAllS hc hD (fun s hs => ?_) hcl (fun s hs => hs.2.2)
      (fun s₁ s₂ h₁ h₂ hp => hrsp (dropSlot s₁) (dropSlot s₂) h₁.2.1 h₂.2.1 hp.1)
      (fun s₁ s₂ _ _ hp q hq => hp.2 q.2 (by
        obtain ⟨⟨n, i⟩, hi, rfl⟩ := List.mem_map.mp hq
        exact List.fst_mem_of_mem_zipIdx hi))
      (fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_)
    · obtain ⟨t, b, he, -, -⟩ := hrun s hs
      exact ⟨t, _, exec_of_dropSlot he⟩
    · obtain ⟨u₁, b₁, f₁, -, -⟩ := hrun s₁ h₁
      obtain ⟨u₂, b₂, f₂, -, -⟩ := hrun s₂ h₂
      rw [(Exec.det e₁ (exec_of_dropSlot f₁)).1, (Exec.det e₂ (exec_of_dropSlot f₂)).1]
      exact hct _ _ _ _ _ _ (himp.pre _ h₁.2.1) (himp.pre _ h₂.2.1)
        (himp.pub _ _ h₁.2.1 h₂.2.1 hp.1) f₁ f₂

/-! ## Storing the addresses -/

open VG.Impl.ForwardCall.X86_64 in
/-- The state after `storeAddr j n` from `u`. -/
def storeState (j : Nat) (n : String) (u : State) : State :=
  { u.setReg .rax (u.syms n) with mem := u.mem.writeW (u.gpr .rsp + BitVec.ofNat 64 (8 * j)) (u.syms n) }

/-- The state after `storeAddrs j fns` from `u`. -/
def storedS (u : State) : Nat → List String → State
  | _, [] => u
  | j, n :: ns => storedS (storeState j n u) (j + 1) ns

/-- The addresses `storeAddrs j fns` accesses, from `rsp = sp`. -/
def storeTrace (sp : Addr) : Nat → List String → List Leak
  | _, [] => []
  | j, _ :: ns => .addr (sp + BitVec.ofNat 64 (8 * j)) :: storeTrace sp (j + 1) ns

@[simp] theorem storeState_rsp (j : Nat) (n : String) (u : State) : (storeState j n u).gpr .rsp = u.gpr .rsp := by
  simp [storeState, State.setReg]
@[simp] theorem storeState_rd (j : Nat) (n : String) (u : State) : (storeState j n u).rd = u.rd := rfl
@[simp] theorem storeState_wr (j : Nat) (n : String) (u : State) : (storeState j n u).wr = u.wr := rfl
@[simp] theorem storeState_mxcsr (j : Nat) (n : String) (u : State) : (storeState j n u).mxcsr = u.mxcsr := rfl
@[simp] theorem storeState_unknowns (j : Nat) (n : String) (u : State) :
    (storeState j n u).unknowns = u.unknowns := rfl
@[simp] theorem storeState_syms (j : Nat) (n : String) (u : State) : (storeState j n u).syms = u.syms := rfl
theorem storeState_gpr (j : Nat) (n : String) (u : State) {q : Reg} (h : q ≠ .rax) :
    (storeState j n u).gpr q = u.gpr q := by
  simp [storeState, State.setReg, h]

theorem storeAddr_run {j : Nat} {n : String} {u : State}
    (hw : InRegions u.wr (u.gpr .rsp + BitVec.ofNat 64 (8 * j)) 8) :
    execBlock isa (Impl.ForwardCall.X86_64.storeAddr j n) u =
      some (storeState j n u, [.addr (u.gpr .rsp + BitVec.ofNat 64 (8 * j))]) := by
  simp only [Impl.ForwardCall.X86_64.storeAddr, execBlock, isa, reduceExec, State.ea, ofInt_natCast, addrs,
    Option.map_some]
  simp [storeState, State.setReg, State.store64, hw]

section
variable (u : State)

@[simp] theorem storedS_rsp : ∀ j fns, (storedS u j fns).gpr .rsp = u.gpr .rsp := by
  intro j fns
  induction fns generalizing u j with
  | nil => rfl
  | cons n ns ih => rw [storedS, ih, storeState_rsp]
@[simp] theorem storedS_rd : ∀ j fns, (storedS u j fns).rd = u.rd := by
  intro j fns
  induction fns generalizing u j with
  | nil => rfl
  | cons n ns ih => rw [storedS, ih, storeState_rd]
@[simp] theorem storedS_wr : ∀ j fns, (storedS u j fns).wr = u.wr := by
  intro j fns
  induction fns generalizing u j with
  | nil => rfl
  | cons n ns ih => rw [storedS, ih, storeState_wr]
@[simp] theorem storedS_mxcsr : ∀ j fns, (storedS u j fns).mxcsr = u.mxcsr := by
  intro j fns
  induction fns generalizing u j with
  | nil => rfl
  | cons n ns ih => rw [storedS, ih, storeState_mxcsr]
@[simp] theorem storedS_unknowns : ∀ j fns, (storedS u j fns).unknowns = u.unknowns := by
  intro j fns
  induction fns generalizing u j with
  | nil => rfl
  | cons n ns ih => rw [storedS, ih, storeState_unknowns]
@[simp] theorem storedS_syms : ∀ j fns, (storedS u j fns).syms = u.syms := by
  intro j fns
  induction fns generalizing u j with
  | nil => rfl
  | cons n ns ih => rw [storedS, ih, storeState_syms]
theorem storedS_gpr {q : Reg} (h : q ≠ .rax) : ∀ j fns, (storedS u j fns).gpr q = u.gpr q := by
  intro j fns
  induction fns generalizing u j with
  | nil => rfl
  | cons n ns ih => rw [storedS, ih, storeState_gpr _ _ _ h]
end

theorem storesS_run : ∀ {u : State} {j : Nat} {fns : List String},
    (∀ i < fns.length, InRegions u.wr (u.gpr .rsp + BitVec.ofNat 64 (8 * (j + i))) 8) →
      execBlock isa (Impl.ForwardCall.X86_64.storeAddrs j fns) u =
        some (storedS u j fns, storeTrace (u.gpr .rsp) j fns)
  | _, _, [], _ => rfl
  | u, j, n :: ns, hw => by
    rw [Impl.ForwardCall.X86_64.storeAddrs, execBlock_append, storeAddr_run (by simpa using hw 0 (by simp))]
    simp only [Option.bind_some]
    rw [storesS_run (u := storeState j n u) (j := j + 1) (fns := ns) (fun i hi => by
      rw [storeState_rsp, storeState_wr, show j + 1 + i = j + (i + 1) by omega_using []]
      exact hw (i + 1) (by simp only [List.length_cons]; omega_using [hi]))]
    simp [storedS, storeTrace]

/-- The stores write only the words from `j` up, which then hold the addresses. -/
theorem storedS_mem : ∀ {u : State} {j : Nat} {fns : List String}, 8 * (j + fns.length) < 2 ^ 64 →
      Frame [⟨u.gpr .rsp + BitVec.ofNat 64 (8 * j), 8 * fns.length⟩] u.mem (storedS u j fns).mem ∧
      ∀ i (h : i < fns.length), (storedS u j fns).mem.readW (u.gpr .rsp + BitVec.ofNat 64 (8 * (j + i))) 64 =
        u.syms fns[i]
  | _, _, [], _ => ⟨Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | u, j, n :: ns, hfit => by
    have hfit' : 8 * (j + 1 + ns.length) < 2 ^ 64 := by simp only [List.length_cons] at hfit; omega_using [hfit]
    obtain ⟨f, hv⟩ := storedS_mem (u := storeState j n u) (j := j + 1) (fns := ns) hfit'
    rw [storeState_rsp, storeState_syms] at hv
    rw [storeState_rsp] at f
    simp only [List.length_cons] at hfit
    have hbig : (⟨u.gpr .rsp + BitVec.ofNat 64 (8 * j), 8 * (ns.length + 1)⟩ : Region).Contains
        (u.gpr .rsp + BitVec.ofNat 64 (8 * j)) 8 :=
      Offset.contains (u.gpr .rsp) (d := 8 * j) (n := 8) (e := 8 * j) (k := 8 * (ns.length + 1))
        (Nat.le_refl _) (by omega_using []) (by omega_using [hfit])
    have hsub : Region.Sub ⟨u.gpr .rsp + BitVec.ofNat 64 (8 * (j + 1)), 8 * ns.length⟩
        ⟨u.gpr .rsp + BitVec.ofNat 64 (8 * j), 8 * (ns.length + 1)⟩ :=
      Offset.sub (u.gpr .rsp) (by omega_using []) (by omega_using [])
    refine ⟨fun x hx => ?_, fun i hi => ?_⟩
    · rw [storedS, f x fun r hr hc => ?_]
      · show (u.mem.writeW _ _) x = _
        exact Mem.write_apply fun h' => hx _ (List.mem_singleton_self _) (hbig.byte h')
      · simp only [List.mem_singleton] at hr; subst hr
        exact hx _ (List.mem_singleton_self _) (hsub x hc)
    · rcases i with _ | i
      · rw [storedS]
        refine (f.readW (r := ⟨u.gpr .rsp + BitVec.ofNat 64 (8 * (j + 0)), 8⟩) (Region.contains_self _ _)
          (fun r hr => ?_) (by decide)).trans ?_
        · simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint (u.gpr .rsp) (d := 8 * (j + 0)) (n := 8) (e := 8 * (j + 1))
            (k := 8 * ns.length) (.inl (by omega_using [])) (by omega_using [hfit]) (by omega_using [hfit])
        · simp only [storeState, Nat.add_zero, List.getElem_cons_zero]
          exact Mem.readW_writeW_self64 _ _ _
      · rw [storedS, show j + (i + 1) = j + 1 + i by omega_using []]
        exact hv i (by simp only [List.length_cons] at hi; omega_using [hi])

/-! ## The callee's entry -/

theorem copiedD_syms (bytes : Nat) (u : State) : ∀ m, (copiedD bytes u m).syms = u.syms
  | 0 => rfl
  | m + 1 => by rw [copiedD, ← copiedD_syms bytes u m]; rfl

theorem fwdState_syms (sig : Sig) (bytes : Nat) (s : State) : (fwdState sig bytes s).syms = s.syms := by
  rw [fwdState, copiedD_syms]; rfl

/-- The callee's entry: after the frame's push, the copies, the stores and
the call, with the caller's permissions and the frame's. -/
def calleeS (sig : Sig) (bytes : Nat) (fns : List String) (s : State) : State :=
  (storedS (fwdState sig bytes s) (nStack sig) fns).callEntry

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack bytes : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}
  {fns : List String}

/-- What the callee's entry keeps of `s`, and what it holds. -/
theorem calleeS_facts (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 8 * (nStack sig + fns.length) ≤ bytes) (hb1 : bytes < 4096) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s) :
    (calleeS sig bytes fns s).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes - 8 ∧
      (∀ q, q ≠ .rax → q ≠ .rsp → (calleeS sig bytes fns s).gpr q = s.gpr q) ∧
      (calleeS sig bytes fns s).mxcsr = s.mxcsr ∧ (calleeS sig bytes fns s).syms = s.syms ∧
      (calleeS sig bytes fns s).rd = s.rd ∧
      (calleeS sig bytes fns s).wr = ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr ∧
      allArgs sig (calleeS sig bytes fns s) = allArgs sig s ∧
      Frame [⟨s.gpr .rsp - BitVec.ofNat 64 bytes - 8, bytes + 8⟩] s.mem (calleeS sig bytes fns s).mem ∧
      ∀ i (h : i < fns.length), (calleeS sig bytes fns s).mem.readW
        (s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (8 * (nStack sig + i))) 64 = s.syms fns[i] := by
  have hb' : 8 * nStack sig ≤ bytes := by omega_using [hb]
  obtain ⟨-, hrd', hwr', hmx, -, hgw, hfw, hv⟩ := fwdState_run hs hk hb' hb1
  have hsb : stack + bytes + 8 ≤ (s.gpr .rsp).toNat := by
    rw [pre_args hk] at hs; rcases hs.1.1 with h | h <;> omega_using [h]
  let w := fwdState sig bytes s
  have hwrsp : w.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes :=
    (hgw .rsp (by decide)).trans (allocState_rsp' _ _)
  obtain ⟨fz, hz⟩ := storedS_mem (u := w) (j := nStack sig) (fns := fns) (by omega_using [hb, hb1])
  rw [hwrsp] at fz hz
  have hF : s.gpr .rsp - BitVec.ofNat 64 bytes - 8 = s.gpr .rsp - BitVec.ofNat 64 (bytes + 8) := by
    rw [BitVec.ofNat_add, BitVec.sub_sub]; rfl
  have hA : s.gpr .rsp - BitVec.ofNat 64 bytes =
      s.gpr .rsp - BitVec.ofNat 64 (bytes + 8) + BitVec.ofNat 64 8 := by
    rw [← hF, show BitVec.ofNat 64 8 = (8 : BitVec 64) from rfl, BitVec.sub_add_cancel]
  -- The words of the frame, as offsets of the return address's.
  have hW : ∀ d, s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 d =
      s.gpr .rsp - BitVec.ofNat 64 (bytes + 8) + BitVec.ofNat 64 (8 + d) := fun d => by
    rw [hA, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have hcm : (calleeS sig bytes fns s).mem =
      (storedS w (nStack sig) fns).mem.writeW (s.gpr .rsp - BitVec.ofNat 64 bytes - 8)
        ((storedS w (nStack sig) fns).unknowns 0) := by
    simp only [calleeS, State.callEntry_mem, storedS_rsp]
    rw [hwrsp]
  -- The return address's word lies below the frame.
  have hret : ∀ d k, d + k ≤ bytes → Mem.Sep (s.gpr .rsp - BitVec.ofNat 64 bytes - 8) 8
      (s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 d) k := fun d k hdk => by
    rw [hF, hW]
    exact Offset.sep_base _ (n := 8) (e := 8 + d) (k := k) (by omega_using []) (by omega_using [hdk, hb1])
  have hgq : ∀ q, q ≠ .rax → q ≠ .rsp → (calleeS sig bytes fns s).gpr q = s.gpr q := fun q h₁ h₂ => by
    rw [calleeS, State.callEntry_gpr _ h₂, storedS_gpr _ h₁, hgw q h₁, allocState_gpr' _ _ h₂]
  refine ⟨by rw [calleeS, State.callEntry_rsp, storedS_rsp, hwrsp], hgq, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [calleeS, State.callEntry_mxcsr, storedS_mxcsr]; exact hmx
  · show (storedS w (nStack sig) fns).syms = s.syms
    rw [storedS_syms]; exact fwdState_syms sig bytes s
  · rw [calleeS, State.callEntry_rd, storedS_rd]; exact hrd'
  · rw [calleeS, State.callEntry_wr, storedS_wr]; exact hwr'
  · -- The arguments: the registers, and the copies.
    rw [allArgs, allArgs, argRegs_map_congr hgq]
    refine congrArg _ (List.map_congr_left fun j hj => ?_)
    have hj' : j < nStack sig := by simpa using hj
    show (calleeS sig bytes fns s).mem.readW
      ((calleeS sig bytes fns s).gpr .rsp + BitVec.ofNat 64 (8 * (j + 1))) 64 = _
    rw [show (calleeS sig bytes fns s).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes - 8 by
      rw [calleeS, State.callEntry_rsp, storedS_rsp, hwrsp], sub8_add_succ]
    rw [hcm]
    rw [Mem.readW_writeW_sep (fun x h₁ h₂ => hret (8 * j) 8 (by omega_using [hj', hb']) x h₂ h₁) (by decide)]
    rw [fz.readW (r := ⟨s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (8 * j), 8⟩)
      (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (d := 8 * j) (n := 8) (e := 8 * nStack sig) (k := 8 * fns.length)
          (.inl (by omega_using [hj'])) (by omega_using [hj', hb, hb1]) (by omega_using [hb, hb1])) (by decide)]
    rw [show s.gpr .rsp - BitVec.ofNat 64 bytes = (allocState bytes s).gpr .rsp from (allocState_rsp' _ _).symm]
    exact hv j hj'
  · -- The memory: the copies, the stores and the return address, all in the frame.
    have hfr : ∀ d k, d + k ≤ bytes → Region.Sub ⟨s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 d, k⟩
        ⟨s.gpr .rsp - BitVec.ofNat 64 bytes - 8, bytes + 8⟩ := fun d k hdk => by
      rw [hF, hW]
      exact Offset.sub_base _ (by omega_using [hdk])
    have f₁ : Frame [⟨s.gpr .rsp - BitVec.ofNat 64 bytes - 8, bytes + 8⟩] s.mem w.mem :=
      Frame.sub hfw fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        refine ⟨_, List.mem_singleton_self _, ?_⟩
        rw [allocState_rsp', hF, hA]
        exact Offset.sub_base _ (by omega_using [hb'])
    have f₂ : Frame [⟨s.gpr .rsp - BitVec.ofNat 64 bytes - 8, bytes + 8⟩] w.mem (storedS w (nStack sig) fns).mem :=
      Frame.sub fz fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, hfr _ _ (by omega_using [hb])⟩
    rw [hcm]
    refine (f₁.trans f₂).writeW (List.mem_singleton_self _) _ ?_
    exact Offset.contains_base _ (d := 0) (n := 8) (k := bytes + 8) (by omega_using []) (by omega_using [])
      |> fun h => by simpa using h
  · intro i hi
    rw [hcm]
    rw [Mem.readW_writeW_sep (fun x h₁ h₂ => hret (8 * (nStack sig + i)) 8 (by omega_using [hi, hb]) x h₂ h₁)
      (by decide)]
    rw [hz i hi, fwdState_syms]

/-- The callee's entry with the permissions of its contract without the
slots: its buffers and lists of slices, and the copies, read only. -/
def slotEntryK (sig : Sig) (bytes : Nat) (fns : List String) (s : State) : State :=
  (calleeS sig bytes fns s).withRegions
    (((allRegions sig (calleeS sig bytes fns s)).filter (!·.2)).map (·.1))
    (((allRegions sig (calleeS sig bytes fns s)).filter (·.2)).map (·.1))

/-- The state the callee runs from: `slotEntryK`, with the slots read only. -/
def slotEntry (sig : Sig) (bytes : Nat) (fns : List String) (s : State) : State :=
  (calleeS sig bytes fns s).withRegions
    ((slotEntryK sig bytes fns s).rd ++ [slotRegion (nStack sig) fns.length (calleeS sig bytes fns s)])
    (slotEntryK sig bytes fns s).wr

theorem dropSlot_slotEntry (sig : Sig) (bytes : Nat) (fns : List String) (s : State) :
    dropSlot (slotEntry sig bytes fns s) = slotEntryK sig bytes fns s := by
  simp only [dropSlot, slotEntry, State.withRegions_rd, State.withRegions_wr, List.dropLast_concat,
    State.withRegions_withRegions]
  rfl

/-- The buffers and the lists of slices lie apart from the frame and the
return address. -/
theorem calleeS_out (hk : 6 ≤ (sig.words abi.ptrBits).length) {s : State} (hs : (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s) :
    ∀ a ∈ bufRegions sig s, a.1.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 bytes - 8, bytes + 8⟩ := by
  have hF : s.gpr .rsp - BitVec.ofNat 64 bytes - 8 = s.gpr .rsp - BitVec.ofNat 64 (bytes + 8) := by
    rw [BitVec.ofNat_add, BitVec.sub_sub]; rfl
  intro a ha
  rw [hF]
  exact fwd_out hk hs a ha (by omega_using []) (by omega_using [])

/-- The memory of the callee's entry is `s`'s in the buffers and the lists. -/
theorem calleeS_agreeL (hk : 6 ≤ (sig.words abi.ptrBits).length) (hb : 8 * (nStack sig + fns.length) ≤ bytes)
    (hb1 : bytes < 4096) {s : State} (hs : (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s) :
    ∀ b ∈ bufRegions sig s, ∀ x, b.1.Contains x 1 → (calleeS sig bytes fns s).mem x = s.mem x := by
  obtain ⟨-, -, -, -, -, -, -, hf, -⟩ := calleeS_facts hk hb hb1 hs
  intro b hb' x hx
  refine hf x fun r hr hc => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact calleeS_out hk hs b hb' x hx hc

theorem calleeS_lists (hk : 6 ≤ (sig.words abi.ptrBits).length) (hb : 8 * (nStack sig + fns.length) ≤ bytes)
    (hb1 : bytes < 4096) {s : State} (hs : (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s) :
    Sig.lists 64 (calleeS sig bytes fns s).mem sig.params (allArgs sig s) =
      Sig.lists 64 s.mem sig.params (allArgs sig s) :=
  (Sig.lists_eq_of_agree 64 fun r hr x hx => (calleeS_agreeL hk hb hb1 hs (r, false)
    (List.mem_append_right _ (List.mem_map.mpr ⟨r, hr, rfl⟩)) x hx).symm).symm

theorem bufRegions_calleeS (hk : 6 ≤ (sig.words abi.ptrBits).length) (hb : 8 * (nStack sig + fns.length) ≤ bytes)
    (hb1 : bytes < 4096) {s : State} (hs : (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s) :
    bufRegions sig (calleeS sig bytes fns s) = bufRegions sig s := by
  obtain ⟨-, -, -, -, -, -, hargs, -, -⟩ := calleeS_facts hk hb hb1 hs
  rw [bufRegions, bufRegions, hargs]
  exact congrArg (_ ++ ·) (congrArg _ (calleeS_lists hk hb hb1 hs))

/-- The callee's argument area is the copies, if it has stack arguments. -/
theorem argArea_calleeS (hk : 6 ≤ (sig.words abi.ptrBits).length) (hb : 8 * (nStack sig + fns.length) ≤ bytes)
    (hb1 : bytes < 4096) {s : State} (hs : (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s) :
    ∀ a ∈ argArea sig (calleeS sig bytes fns s), a = (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, 8 * nStack sig⟩, false) := by
  obtain ⟨hrsp, -⟩ := calleeS_facts hk hb hb1 hs
  intro a ha
  simp only [argArea] at ha
  split at ha
  · simp at ha
  · simp only [List.mem_singleton] at ha
    subst ha
    simp only [stackArgAddr, hrsp]
    rw [sub8_add_succ]
    simp [nStack]

/-- The caller's precondition gives the callee's (without the slots), if the
precondition reads memory only within the buffers and the lists of slices. -/
theorem slotEntryK_pre (hk : 6 ≤ (sig.words abi.ptrBits).length) (hb : 8 * (nStack sig + fns.length) ≤ bytes)
    (hb1 : bytes < 4096)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      (∀ r ∈ Sig.lists abi.ptrBits m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s) :
    (sig.contract abi pre post wa stack leak).pre (slotEntryK sig bytes fns s) := by
  obtain ⟨hrsp, -, -, -, -, -, hargs, -⟩ := calleeS_facts hk hb hb1 hs
  have hbuf := bufRegions_calleeS hk hb hb1 hs
  have harea := argArea_calleeS hk hb hb1 hs
  have hagB := calleeS_agreeL hk hb hb1 hs
  have hout := fwd_out hk hs
  have hall : allRegions sig (slotEntryK sig bytes fns s) = bufRegions sig s ++ argArea sig (calleeS sig bytes fns s) := by
    show bufRegions sig (calleeS sig bytes fns s) ++ argArea sig (calleeS sig bytes fns s) = _
    rw [hbuf]
  rw [pre_args hk] at hs
  obtain ⟨⟨hst, -⟩, -, -, hpw, -, hnw, hpr⟩ := hs
  have hsb : stack + bytes + 8 ≤ (s.gpr .rsp).toNat := by rcases hst with h | h <;> omega_using [h]
  have hlen := allArgs_length sig s hk
  have hF : s.gpr .rsp - BitVec.ofNat 64 bytes - 8 = s.gpr .rsp - BitVec.ofNat 64 (bytes + 8) := by
    rw [BitVec.ofNat_add, BitVec.sub_sub]; rfl
  have hpwB : (bufRegions sig s).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) :=
    List.Pairwise.sublist (List.sublist_append_left _ _) hpw
  have hareaD : ∀ a ∈ bufRegions sig s, a.1.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, 8 * nStack sig⟩ :=
    fun a ha => hout a ha (by omega_using []) (by omega_using [hb])
  have hn : nStack sig = (sig.words abi.ptrBits).length - 6 := rfl
  have hrspN : (slotEntryK sig bytes fns s).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 (bytes + 8) := by
    rw [← hF]; exact hrsp
  refine (pre_args hk).mpr ⟨⟨.inr ?_, .inr ?_⟩, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [hrspN, toNat_sub_ofNat (by omega_using [hsb])]; omega_using [hsb]
  · rw [hrspN, toNat_sub_ofNat (by omega_using [hsb])]
    have := (s.gpr .rsp).isLt
    omega_using [hb, hsb, hn, this]
  · -- Pairwise disjoint.
    rw [hall]
    refine List.pairwise_append.mpr ⟨hpwB, ?_, fun a ha b hb' _ => by rw [harea b hb']; exact hareaD a ha⟩
    simp only [argArea]
    split <;> simp
  · -- The reserved stack: the return address and the stack below it.
    rw [hall, hrspN]
    intro r hr a ha
    have hr' : r = ⟨s.gpr .rsp - BitVec.ofNat 64 (bytes + 8), 8⟩ ∨
        (0 < stack ∧ r = below (s.gpr .rsp - BitVec.ofNat 64 (bytes + 8)) stack) := by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact .inl rfl
      · rcases Nat.eq_zero_or_pos stack with h0 | h0
        · subst h0; simp [stackBelow] at hr
        · rw [stackBelow_pos _ h0, List.mem_singleton] at hr; exact .inr ⟨h0, hr⟩
    rcases List.mem_append.mp ha with ha | ha
    · rcases hr' with rfl | ⟨-, rfl⟩
      · exact Region.Disjoint.symm (hout a ha (by omega_using []) (by omega_using []))
      · refine (Region.Disjoint.symm (hout a ha (x := stack + bytes + 8) (k := stack + bytes + 8)
          (by omega_using []) (by omega_using []))).sub_left ?_
        have := below_below (s.gpr .rsp) (bytes + 8) stack
        rwa [show stack + (bytes + 8) = stack + bytes + 8 by omega_using []] at this
    · rw [harea a ha]
      have hA : s.gpr .rsp - BitVec.ofNat 64 bytes =
          s.gpr .rsp - BitVec.ofNat 64 (bytes + 8) + BitVec.ofNat 64 8 := by
        rw [← hF, show BitVec.ofNat 64 8 = (8 : BitVec 64) from rfl, BitVec.sub_add_cancel]
      rcases hr' with rfl | ⟨h0, rfl⟩
      · show Region.Disjoint ⟨_, 8⟩ ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, 8 * nStack sig⟩
        rw [hA]
        exact Offset.base_disjoint _ (e := 8) (k := 8) (Nat.le_refl _) (by omega_using [hb, hb1])
      · show Region.Disjoint (below _ stack) ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, 8 * nStack sig⟩
        rw [hA]
        exact Region.Disjoint.symm (Offset.disjoint_below _ (n := stack) (d := 8)
          (k := 8 * nStack sig) (by omega_using [hb, hb1, hsb]))
  · show ∀ a ∈ bufRegions sig (calleeS sig bytes fns s), _
    rw [hbuf]; exact hnw
  · -- The precondition, which reads only the buffers and the lists.
    show Curry.apply _ pre (allArgs sig (calleeS sig bytes fns s)) (calleeS sig bytes fns s).mem
    rw [hargs]
    exact hpre _ _ _ hlen (fun b hb' x hx => (hagB b (List.mem_append_left _ hb') x hx).symm)
      (fun r hr x hx => (hagB (r, false) (List.mem_append_right _ (List.mem_map.mpr ⟨r, hr, rfl⟩)) x hx).symm) hpr

/-- The regions the callee may write: the caller's writable buffers. -/
theorem slotEntry_wr (hk : 6 ≤ (sig.words abi.ptrBits).length) (hb : 8 * (nStack sig + fns.length) ≤ bytes)
    (hb1 : bytes < 4096) {s : State} (hs : (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s)
    {r : Region} (hr : r ∈ (slotEntry sig bytes fns s).wr) : ∃ a ∈ bufRegions sig s, a.2 = true ∧ a.1 = r := by
  have hbuf := bufRegions_calleeS hk hb hb1 hs
  have harea := argArea_calleeS hk hb hb1 hs
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
  obtain ⟨ha, hf⟩ := List.mem_filter.mp ha
  rcases List.mem_append.mp ha with ha | ha
  · rw [hbuf] at ha; exact ⟨a, ha, hf, rfl⟩
  · rw [harea a ha] at hf; simp at hf

/-- The regions the callee may read: the caller's read-only buffers and lists,
the copies and the slots. -/
theorem slotEntry_rd (hk : 6 ≤ (sig.words abi.ptrBits).length) (hb : 8 * (nStack sig + fns.length) ≤ bytes)
    (hb1 : bytes < 4096) {s : State} (hs : (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s)
    {r : Region} (hr : r ∈ (slotEntry sig bytes fns s).rd) :
    (∃ a ∈ bufRegions sig s, a.2 = false ∧ a.1 = r) ∨
      r = ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, 8 * nStack sig⟩ ∨
      r = ⟨s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (8 * nStack sig), 8 * fns.length⟩ := by
  have hbuf := bufRegions_calleeS hk hb hb1 hs
  have harea := argArea_calleeS hk hb hb1 hs
  obtain ⟨hrsp, -⟩ := calleeS_facts hk hb hb1 hs
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf⟩ := List.mem_filter.mp ha
    rcases List.mem_append.mp ha with ha | ha
    · rw [hbuf] at ha; exact .inl ⟨a, ha, by simpa using hf, rfl⟩
    · rw [harea a ha]; exact .inr (.inl rfl)
  · simp only [List.mem_singleton] at hr
    subst hr
    refine .inr (.inr ?_)
    simp only [slotRegion, hrsp]
    rw [show 8 * (nStack sig + 1) = 8 * (nStack sig + 0 + 1) by omega_using [], sub8_add_succ]

/-- The callee's precondition with the slots, in `slotEntry`. -/
theorem slotEntry_pre (hk : 6 ≤ (sig.words abi.ptrBits).length) (hb : 8 * (nStack sig + fns.length) ≤ bytes)
    (hb1 : bytes < 4096)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      (∀ r ∈ Sig.lists abi.ptrBits m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s) :
    ((sig.contract abi pre post wa stack leak).withSlots (nStack sig) fns).pre (slotEntry sig bytes fns s) := by
  obtain ⟨hrsp, -, -, hsy, -, -, -, -, hslot⟩ := calleeS_facts hk hb hb1 hs
  have hout := calleeS_out hk hs
  refine ⟨by simp only [slotEntry, State.withRegions_rd, List.getLast?_concat]; rfl, by rw [dropSlot_slotEntry]; exact slotEntryK_pre hk hb hb1 hpre hs, ?_⟩
  intro p hp
  obtain ⟨⟨n, i⟩, hi, rfl⟩ := List.mem_map.mp hp
  have hil : i < fns.length := List.snd_lt_of_mem_zipIdx hi
  have hn : fns[i] = n := by
    have := List.mem_zipIdx_iff_getElem?.mp hi
    simp only at this
    rw [List.getElem?_eq_getElem hil] at this
    exact Option.some.inj this
  have hc : (slotEntry sig bytes fns s).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes - 8 := hrsp
  -- The slot's address, as an offset of the frame's.
  have ha : (slotEntry sig bytes fns s).gpr .rsp + BitVec.ofInt 64 ((8 * (nStack sig + 1 + i) : Nat) : Int) =
      s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (8 * (nStack sig + i)) := by
    rw [hc, ofInt_natCast, show 8 * (nStack sig + 1 + i) = 8 * (nStack sig + i + 1) by omega_using [],
      sub8_add_succ]
  have hF : s.gpr .rsp - BitVec.ofNat 64 bytes - 8 = s.gpr .rsp - BitVec.ofNat 64 (bytes + 8) := by
    rw [BitVec.ofNat_add, BitVec.sub_sub]; rfl
  have hA : s.gpr .rsp - BitVec.ofNat 64 bytes =
      s.gpr .rsp - BitVec.ofNat 64 (bytes + 8) + BitVec.ofNat 64 8 := by
    rw [← hF, show BitVec.ofNat 64 8 = (8 : BitVec 64) from rfl, BitVec.sub_add_cancel]
  have hin : (⟨s.gpr .rsp - BitVec.ofNat 64 bytes - 8, bytes + 8⟩ : Region).Contains
      (s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (8 * (nStack sig + i))) 8 := by
    rw [hF, hA, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact Offset.contains_base _ (by omega_using [hb, hil]) (by omega_using [hb, hil, hb1])
  refine ⟨?_, fun r hr => ?_⟩
  · have hreg : InRegions ((slotEntry sig bytes fns s).rd ++ (slotEntry sig bytes fns s).wr)
        (s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (8 * (nStack sig + i))) 8 := by
      refine ⟨_, List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _)), ?_⟩
      simp only [slotRegion, hrsp]
      rw [show 8 * (nStack sig + 1) = 8 * (nStack sig + 0 + 1) by omega_using [], sub8_add_succ]
      exact Offset.contains _ (by omega_using []) (by omega_using [hil]) (by omega_using [hb, hb1])
    simp only [State.load64, ha, hreg, ite_true]
    show some ((calleeS sig bytes fns s).mem.readW _ 64) = some ((calleeS sig bytes fns s).syms _)
    rw [hslot i hil, hsy, hn]
  · obtain ⟨a, ha', -, rfl⟩ := slotEntry_wr hk hb hb1 hs hr
    simp only [ha]
    exact fun x hx hx' => hout a ha' x hx' (Region.Contains.byte hin (by
      simp only [Region.Contains] at hx; omega_using [hx]))

/-- The addresses `forwardS` accesses, from `rsp = sp`, around its callee's `t`. -/
def fwdTraceS (bytes m : Nat) (fns : List String) (sp : Addr) (t : List Leak) : List Leak :=
  copyDTrace bytes (sp - BitVec.ofNat 64 bytes) m ++ storeTrace (sp - BitVec.ofNat 64 bytes) m fns ++
    ([.addr (sp - BitVec.ofNat 64 bytes - 8)] ++ t ++ [.addr (sp - BitVec.ofNat 64 bytes - 8)])

open VG.Impl.ForwardCall.X86_64 in
/-- A run of the callee from `slotEntry s` is a run of `forwardS` from `s`,
which keeps what the calling convention requires, whose memory is the
callee's with the frame's bytes lost, and whose `rax` is the callee's. -/
theorem forwardS_run {name : String} {body : Prog isa} (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 8 * (nStack sig + fns.length) ≤ bytes ∧ 0 < bytes ∧ bytes < 4096 ∧ bytes % 8 = 0)
    (hst : stack + bytes + 16 ≤ 2 ^ 64) (hsafe : SpSafe body) (hd : body.x86_64Depth ≤ stack) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s) {t : List Leak} {s₃ : State}
    (he : Exec isa body (slotEntry sig bytes fns s) t s₃) (ha : abiPreserved (slotEntry sig bytes fns s) s₃) :
    Exec isa (forwardS bytes (nStack sig) fns name body) s (fwdTraceS bytes (nStack sig) fns (s.gpr .rsp) t)
        (fwdFinal bytes s s₃) ∧
      abiPreserved s (fwdFinal bytes s s₃) ∧
      (fwdFinal bytes s s₃).mem = lose s₃.mem (s.gpr .rsp - BitVec.ofNat 64 bytes) bytes s₃.unknowns ∧
      (fwdFinal bytes s s₃).gpr .rax = s₃.gpr .rax := by
  obtain ⟨hb, hb0, hb1, hb2⟩ := hb
  have hb' : 8 * nStack sig ≤ bytes := by omega_using [hb]
  obtain ⟨hrun, hrd', hwr', -, -, hgw, -, -⟩ := fwdState_run hs hk hb' hb1
  obtain ⟨hrsp, hg, hmx, -, hcrd, hcwr, -, hf, -⟩ := calleeS_facts hk hb hb1 hs
  have hout := fwd_out hk hs
  obtain ⟨⟨hwf, -⟩, hrd, hwr, -, hres, -, -⟩ := (pre_args hk).mp hs
  have hsb : stack + bytes + 8 ≤ (s.gpr .rsp).toNat := by rcases hwf with h | h <;> omega_using [h]
  have hF : s.gpr .rsp - BitVec.ofNat 64 bytes - 8 = s.gpr .rsp - BitVec.ofNat 64 (bytes + 8) := by
    rw [BitVec.ofNat_add, BitVec.sub_sub]; rfl
  let w := fwdState sig bytes s
  have hwrsp : w.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes :=
    (hgw .rsp (by decide)).trans (allocState_rsp' _ _)
  let z := storedS w (nStack sig) fns
  -- The frame's push.
  have hpush : isa.push (.alloc bytes) s = some (allocState bytes s) := by
    simp only [isa, push, allocState]
    exact ite_eq_left ⟨hb0, hb1, hb2, by omega_using [hsb]⟩
  -- The copies, then the stores.
  have hframe : ∀ d k, d + k ≤ bytes → InRegions w.wr (s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 d) k :=
    fun d k hdk => ⟨_, by rw [hwr']; exact List.mem_cons_self .., Offset.contains_base _ hdk (by omega_using [hdk, hb1])⟩
  have hblock : execBlock isa (copies bytes (nStack sig) ++ storeAddrs (nStack sig) fns) (allocState bytes s) =
      some (z, copyDTrace bytes ((allocState bytes s).gpr .rsp) (nStack sig) ++
        storeTrace (s.gpr .rsp - BitVec.ofNat 64 bytes) (nStack sig) fns) := by
    rw [execBlock_append, hrun]
    simp only [Option.bind_some]
    rw [storesS_run (fun i hi => by rw [hwrsp]; exact hframe _ 8 (by omega_using [hb, hi])), hwrsp]
    rfl
  -- The callee's regions are within the caller's and the frame.
  have hbufR : ∀ a ∈ bufRegions sig s, a.2 = false → a.1 ∈ s.rd := fun a ha h => by
    rw [hrd]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ ha, by simp [h]⟩, rfl⟩
  have hbufW : ∀ a ∈ bufRegions sig s, a.2 = true → a.1 ∈ s.wr := fun a ha h => by
    rw [hwr]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ ha, h⟩, rfl⟩
  have hcovW : Covers (slotEntry sig bytes fns s).wr (calleeS sig bytes fns s).wr := by
    rw [hcwr]
    refine Covers.of_mem fun r hr => ?_
    obtain ⟨a, ha, h2, rfl⟩ := slotEntry_wr hk hb hb1 hs hr
    exact List.mem_cons_of_mem _ (hbufW a ha h2)
  have hcovR : Covers (slotEntry sig bytes fns s).rd
      ((calleeS sig bytes fns s).rd ++ (calleeS sig bytes fns s).wr) := by
    rw [hcrd, hcwr]
    refine Covers.of_forall fun r hr => ?_
    rcases slotEntry_rd hk hb hb1 hs hr with ⟨a, ha, h2, rfl⟩ | rfl | rfl
    · exact Covers.left (Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact hbufR a ha h2)
    · exact Covers.right (Covers.one (by
        have := hframe 0 (8 * nStack sig) (by omega_using [hb'])
        rw [hwr'] at this
        simpa [allocState] using this))
    · exact Covers.right (Covers.one (by
        have := hframe (8 * nStack sig) (8 * fns.length) (by omega_using [hb])
        rw [hwr'] at this
        exact this))
  have hw := Exec.widen he (rd := (calleeS sig bytes fns s).rd) (wr := (calleeS sig bytes fns s).wr)
    (Covers.append_left hcovR (Covers.right hcovW)) hcovW
  rw [show (slotEntry sig bytes fns s).withRegions (calleeS sig bytes fns s).rd (calleeS sig bytes fns s).wr =
      z.callEntry from rfl, hcrd, hcwr] at hw
  -- The return.
  have hrsp₃ : s₃.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes - 8 :=
    (ha.1 .rsp (by simp [calleeSaved])).trans hrsp
  have hzrsp : z.callEntry.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes - 8 := hrsp
  have hret : isa.ret z.callEntry (s₃.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)) =
      some ((s₃.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)).setReg .rsp (s₃.gpr .rsp + 8)) := by
    simp only [isa, ret, State.withRegions_gpr, State.withRegions_mem]
    refine ite_eq_left ⟨by rw [hrsp₃, hzrsp], ?_⟩
    have := ha.2.1
    rw [hrsp₃]
    simp only [slotEntry, State.withRegions_gpr, State.withRegions_mem] at this
    rw [hzrsp]
    rw [show (calleeS sig bytes fns s).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes - 8 from hrsp] at this
    exact this
  -- The pop.
  have hpop : isa.pop (.free bytes) (allocState bytes s)
      (((s₃.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)).setReg .rsp (s₃.gpr .rsp + 8))) = some (fwdFinal bytes s s₃) := by
    have h4 : ((s₃.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)).setReg .rsp (s₃.gpr .rsp + 8)).gpr .rsp =
        (allocState bytes s).gpr .rsp := by
      simp only [State.setReg, ite_true, hrsp₃, allocState_rsp', BitVec.sub_add_cancel]
    have h5 : ((s₃.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)).setReg .rsp (s₃.gpr .rsp + 8)).wr = (allocState bytes s).wr := by
      rfl
    have h6 : (allocState bytes s).wr.head? = some ⟨(allocState bytes s).gpr .rsp, bytes⟩ := by
      simp [allocState, State.setReg]
    simp only [isa, pop]
    rw [ite_eq_left ⟨hb0, hb1, hb2, h4, h5, h6⟩]
    simp only [fwdFinal, State.setReg, State.withRegions, ite_true]
    rfl
  have hex : Exec isa (forwardS bytes (nStack sig) fns name body) s _ _ :=
    Exec.frame hpush (Exec.seq (Exec.block hblock) (Exec.call (name := name) (call_callEntry z) hw hret)) hpop
  have hzrsp' : z.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes := by
    show (storedS w (nStack sig) fns).gpr .rsp = _
    rw [storedS_rsp, hwrsp]
  simp only [isa, addrs, List.map_nil, List.nil_append, List.append_nil, allocState_rsp',
    List.map_cons, State.withRegions_gpr, hrsp₃, hzrsp'] at hex
  have h8 : s₃.gpr .rsp + 8 = s.gpr .rsp - BitVec.ofNat 64 bytes := by
    rw [hrsp₃, BitVec.sub_add_cancel]
  refine ⟨?_, ⟨fun q hq => ?_, ?_, ?_⟩, by show lose _ (s₃.gpr .rsp + 8) _ _ = _; rw [h8], ?_⟩
  · simpa only [fwdTraceS, List.append_assoc] using hex
  · -- The callee-saved registers.
    simp only [fwdFinal, State.setReg, State.withRegions_gpr]
    by_cases hqs : q = .rsp
    · subst hqs; simp only [ite_true, hrsp₃]
      rw [BitVec.sub_add_cancel, BitVec.sub_add_cancel]
    · simp only [hqs, ite_false]
      have hqa : q ≠ .rax := fun h => by subst h; simp [calleeSaved] at hq
      rw [ha.1 q hq]
      exact hg q hqa hqs
  · -- The return address: the callee writes only its regions and below its `rsp`.
    have hfs := Exec.stackFrame hsafe he (by omega_using [hd, hst])
    show (lose s₃.mem (s₃.gpr .rsp + 8) bytes s₃.unknowns).readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64
    have hR : ∀ {x k : Nat}, x ≤ stack + bytes + 8 → stack + bytes + 8 - x + k ≤ stack + bytes + 8 →
        (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 x, k⟩ := fun hx hk' =>
      (Offset.base_disjoint_below _ (n := stack + bytes + 8) (k := 8) (by omega_using [hst])).sub_right
        (Offset.sub_below _ hx hk')
    rw [(lose_frame _ _ _ _).readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h8]
      exact hR (by omega_using []) (by omega_using [hb])) (by decide)]
    rw [hfs.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) ?_ (by decide)]
    · exact hf.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hF]
        exact hR (by omega_using []) (by omega_using [hb])) (by decide)
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨a, ha', -, rfl⟩ := slotEntry_wr hk hb hb1 hs hr
        exact hres _ (List.mem_cons_self ..) a (List.mem_append_left _ ha')
      · simp only [List.mem_singleton] at hr; subst hr
        rw [show (slotEntry sig bytes fns s).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes - 8 from hrsp, hF]
        show (⟨s.gpr .rsp, 8⟩ : Region).Disjoint
          ⟨s.gpr .rsp - BitVec.ofNat 64 (bytes + 8) - BitVec.ofNat 64 body.x86_64Depth, body.x86_64Depth⟩
        rw [BitVec.sub_sub, ← BitVec.ofNat_add]
        exact hR (by omega_using [hd]) (by omega_using [hd])
  · -- MXCSR.
    show s₃.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
    rw [ha.2.2]
    show (calleeS sig bytes fns s).mxcsr.extractLsb' 6 10 = _
    rw [hmx]
  · simp [fwdFinal, State.setReg]

/-- The caller's public data is the callee's, in `slotEntryK`. -/
theorem slotEntryK_pub (hk : 6 ≤ (sig.words abi.ptrBits).length) (hb : 8 * (nStack sig + fns.length) ≤ bytes)
    (hb1 : bytes < 4096) {s₁ s₂ : State}
    (h₁ : (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s₁)
    (h₂ : (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s₂)
    (hp : (sig.contract abi pre post wa (stack + bytes + 8) leak).pub s₁ s₂)
    (hleak : Sig.LeakLocalL abi.ptrBits sig leak := by trivial) :
    (sig.contract abi pre post wa stack leak).pub (slotEntryK sig bytes fns s₁) (slotEntryK sig bytes fns s₂) := by
  rw [pubL_args hk] at hp
  obtain ⟨⟨⟨hsp, hmx⟩, hlk⟩, hpa, hdesc⟩ := hp
  obtain ⟨e₁, -, m₁, -, -, -, a₁, -⟩ := calleeS_facts hk hb hb1 h₁
  obtain ⟨e₂, -, m₂, -, -, -, a₂, f₂, -⟩ := calleeS_facts hk hb hb1 h₂
  have l₁ := allArgs_length sig s₁ hk
  have hag₁ := calleeS_agreeL hk hb hb1 h₁
  have hag₂ := calleeS_agreeL hk hb hb1 h₂
  have ak₁ : allArgs sig (slotEntryK sig bytes fns s₁) = allArgs sig s₁ := a₁
  have ak₂ : allArgs sig (slotEntryK sig bytes fns s₂) = allArgs sig s₂ := a₂
  refine (pubL_args hk).mpr ?_
  rw [ak₁, ak₂]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hpa, fun r hr i hi => ?_⟩
  · show (calleeS sig bytes fns s₁).gpr .rsp = (calleeS sig bytes fns s₂).gpr .rsp
    rw [e₁, e₂, hsp]
  · show (calleeS sig bytes fns s₁).mxcsr = (calleeS sig bytes fns s₂).mxcsr
    rw [m₁, m₂, hmx]
  · cases leak with
    | none => trivial
    | some f =>
      have hL₁ : ∀ r ∈ Sig.lists abi.ptrBits (calleeS sig bytes fns s₁).mem sig.params (allArgs sig s₁),
          ∀ x, r.Contains x 1 → (calleeS sig bytes fns s₁).mem x = s₁.mem x := fun r hr =>
        hag₁ (r, false) (List.mem_append_right _ (List.mem_map.mpr ⟨r, (calleeS_lists hk hb hb1 h₁) ▸ hr, rfl⟩))
      have hL₂ : ∀ r ∈ Sig.lists abi.ptrBits (calleeS sig bytes fns s₂).mem sig.params (allArgs sig s₂),
          ∀ x, r.Contains x 1 → (calleeS sig bytes fns s₂).mem x = s₂.mem x := fun r hr =>
        hag₂ (r, false) (List.mem_append_right _ (List.mem_map.mpr ⟨r, (calleeS_lists hk hb hb1 h₂) ▸ hr, rfl⟩))
      show Curry.apply _ f (allArgs sig s₁) (calleeS sig bytes fns s₁).mem =
        Curry.apply _ f (allArgs sig s₂) (calleeS sig bytes fns s₂).mem
      rw [hleak _ _ _ l₁ (fun b hb' => hag₁ b (List.mem_append_left _ hb')) hL₁,
        hleak _ _ _ (allArgs_length sig s₂ hk) (fun b hb' => hag₂ b (List.mem_append_left _ hb')) hL₂]
      exact hlk
  · have hx : r.Contains (r.base + BitVec.ofNat 64 i) 1 := Region.contains_ofNat r.base hi
    have hr₁ : r ∈ Sig.lists 64 s₁.mem sig.params (allArgs sig s₁) := Sig.descs_sub_lists 64 _ _ _ r hr
    show (calleeS sig bytes fns s₁).mem _ = (calleeS sig bytes fns s₂).mem _
    rw [hag₁ (r, false) (List.mem_append_right _ (List.mem_map.mpr ⟨r, hr₁, rfl⟩)) _ hx, hdesc r hr i hi]
    refine (f₂ _ fun q hq hc => ?_).symm
    simp only [List.mem_singleton] at hq; subst hq
    rw [← hsp] at hc
    exact calleeS_out hk h₁ (r, false) (List.mem_append_right _ (List.mem_map.mpr ⟨r, hr₁, rfl⟩)) _ hx hc

/-- `Abi.withFns` makes only the functions' addresses public too. -/
theorem pub_withFns {x : String} {xs : List String} {st : Nat} {s₁ s₂ : State} :
    (sig.contract (abi.withFns (x :: xs)) pre post wa st leak).pub s₁ s₂ ↔
      (sig.contract abi pre post wa st leak).pub s₁ s₂ ∧ ∀ g ∈ x :: xs, s₁.syms g = s₂.syms g := by
  simp only [Sig.contract, Abi.withFns]
  split
  · exact ⟨False.elim, fun h => h.1.elim⟩
  · cases leak with
    | none =>
      exact ⟨fun ⟨⟨a, fa⟩, b, c⟩ => ⟨⟨a, b, c⟩, fa⟩, fun ⟨⟨a, b, c⟩, fa⟩ => ⟨⟨a, fa⟩, b, c⟩⟩
    | some f =>
      exact ⟨fun ⟨⟨⟨a, fa⟩, l⟩, b, c⟩ => ⟨⟨⟨a, l⟩, b, c⟩, fa⟩,
        fun ⟨⟨⟨a, l⟩, b, c⟩, fa⟩ => ⟨⟨⟨a, fa⟩, l⟩, b, c⟩⟩

open VG.Impl.ForwardCall.X86_64 in
/-- `Verified.forward` for `forwardS`: code verified against `sig.contract`,
for `stack` bytes of stack, with the addresses of `x :: xs` in slots above its
stack arguments (`SlotVerified`), is verified against the same contract with
those addresses public (`Abi.withFns`) and `stack + bytes + 8` bytes when
called by `forwardS`, which stores them there. -/
theorem Verified.forwardS {name x : String} {xs : List String} {body : Prog isa}
    (h : SlotVerified body (sig.contract abi pre post wa stack leak) (nStack sig) (x :: xs))
    (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 8 * (nStack sig + (x :: xs).length) ≤ bytes ∧ bytes < 4096 ∧ bytes % 8 = 0)
    (hst : stack + bytes + 16 ≤ 2 ^ 64)
    (hsp : body.all (fun i => !isa.writesSp i) = true) (hd : body.x86_64Depth ≤ stack)
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
      Curry.apply (sig.words abi.ptrBits) pre vs m →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      (∀ r ∈ Sig.lists abi.ptrBits m sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s)
    (hleak : Sig.LeakLocalL abi.ptrBits sig leak := by trivial) :
    Verified target (forwardS bytes (nStack sig) (x :: xs) name body)
      (sig.contract (abi.withFns (x :: xs)) pre post wa (stack + bytes + 8) leak) := by
  obtain ⟨hcor, hct⟩ := h
  have hsafe := SpSafe.of_all hsp
  obtain ⟨hb, hb1, hb2⟩ := hb
  have hb0 : 0 < bytes := by simp only [List.length_cons] at hb; omega_using [hb]
  -- The contract with the addresses public asks the same of a state.
  have hpreF : ∀ s, (sig.contract (abi.withFns (x :: xs)) pre post wa (stack + bytes + 8) leak).pre s ↔
      (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s := fun _ => Iff.rfl
  have hpostF : ∀ s s', (sig.contract (abi.withFns (x :: xs)) pre post wa (stack + bytes + 8) leak).post s s' ↔
      (sig.contract abi pre post wa (stack + bytes + 8) leak).post s s' := fun _ _ => Iff.rfl
  -- Every run is the copies and the stores, then the call of the callee's run from `slotEntry`.
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s → ∃ t s₃,
      Exec isa body (slotEntry sig bytes (x :: xs) s) t s₃ ∧
      ((sig.contract abi pre post wa stack leak).withSlots (nStack sig) (x :: xs)).post
        (slotEntry sig bytes (x :: xs) s) s₃ ∧
      Exec isa (Impl.ForwardCall.X86_64.forwardS bytes (nStack sig) (x :: xs) name body) s
        (fwdTraceS bytes (nStack sig) (x :: xs) (s.gpr .rsp) t) (fwdFinal bytes s s₃) ∧
      abiPreserved s (fwdFinal bytes s s₃) ∧
      Frame [⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩] s₃.mem (fwdFinal bytes s s₃).mem ∧
      (fwdFinal bytes s s₃).gpr .rax = s₃.gpr .rax := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (slotEntry_pre hk hb hb1 hpre hs)
    obtain ⟨hex, ha', hm', hr⟩ := forwardS_run hk ⟨hb, hb0, hb1, hb2⟩ hst hsafe hd hs he ha
    exact ⟨t, s₃, he, hq, hex, ha', by rw [hm']; exact lose_frame _ _ _ _, hr⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat.elim fun s hs => ⟨s, hs⟩⟩
  · rw [hpreF] at hs
    obtain ⟨t, s₃, -, hq, hex, ha, hmem, hrax⟩ := hrun s hs
    refine ⟨_, _, hex, ha, (hpostF _ _).mpr ?_⟩
    rw [post_args hk]
    change (sig.contract abi pre post wa stack leak).post (dropSlot (slotEntry sig bytes (x :: xs) s)) (dropSlot s₃) at hq
    rw [dropSlot_slotEntry] at hq
    rw [post_args hk] at hq
    obtain ⟨-, -, -, -, -, -, hargs, -, -⟩ := calleeS_facts hk hb hb1 hs
    have hargs' : allArgs sig (slotEntryK sig bytes (x :: xs) s) = allArgs sig s := hargs
    rw [hargs'] at hq
    rw [hrax]
    have hag := calleeS_agreeL hk hb hb1 hs
    have h₄ := hpost _ _ s.mem _ _ (allArgs_length sig s hk) (fun b hb' a ha' => hag b (List.mem_append_left _ hb') a ha')
      (fun r hr a ha' => hag (r, false) (List.mem_append_right _ (List.mem_map.mpr
        ⟨r, (calleeS_lists hk hb hb1 hs) ▸ hr, rfl⟩)) a ha') hq
    -- The memory on return: after the `free`, which loses only the frame.
    have hF : ∀ a ∈ bufRegions sig s, a.1.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :=
      fun a ha => fwd_out hk hs a ha (by omega_using []) (by omega_using [])
    refine hpostOut _ _ _ _ _ (allArgs_length sig s hk) ((pre_args hk).mp hs).2.2.2.2.2.2
      (fun b hb' a ha' => ?_) (fun r hr a ha' => ?_) h₄
    · exact (hmem a fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact hF b (List.mem_append_left _ hb') a ha').symm
    · exact (hmem a fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact hF (r, false) (List.mem_append_right _ (List.mem_map.mpr ⟨r, hr, rfl⟩)) a ha').symm
  · rw [hpreF] at h₁ h₂
    obtain ⟨hp, hfn⟩ := pub_withFns.mp hp
    obtain ⟨u₁, r₁, f₁, -, x₁, -⟩ := hrun s₁ h₁
    obtain ⟨u₂, r₂, f₂, -, x₂, -⟩ := hrun s₂ h₂
    obtain ⟨-, -, -, sy₁, -⟩ := calleeS_facts (fns := x :: xs) hk hb hb1 h₁
    obtain ⟨-, -, -, sy₂, -⟩ := calleeS_facts (fns := x :: xs) hk hb hb1 h₂
    have hpS : ((sig.contract abi pre post wa stack leak).withSlots (nStack sig) (x :: xs)).pub
        (slotEntry sig bytes (x :: xs) s₁) (slotEntry sig bytes (x :: xs) s₂) := by
      refine ⟨?_, fun n hn => ?_⟩
      · rw [dropSlot_slotEntry, dropSlot_slotEntry]
        exact slotEntryK_pub hk hb hb1 h₁ h₂ hp hleak
      · show (calleeS sig bytes (x :: xs) s₁).syms n = (calleeS sig bytes (x :: xs) s₂).syms n
        rw [sy₁, sy₂]; exact hfn n hn
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1, ((pubL_args hk).mp hp).1.1.1,
      hct _ _ _ _ _ _ (slotEntry_pre hk hb hb1 hpre h₁) (slotEntry_pre hk hb hb1 hpre h₂) hpS f₁ f₂]

open VG.Impl.ForwardCall.X86_64 in
/-- `forwardS` writes `rsp` only in its frame and its call if its callee does
only in its frames. -/
theorem forwardS_spSafe {bytes m : Nat} {fns : List String} {name : String} {body : Prog isa}
    (h : body.all (fun i => !isa.writesSp i) = true) :
    (Impl.ForwardCall.X86_64.forwardS bytes m fns name body).all (fun i => !isa.writesSp i) = true := by
  have hc : (copies bytes m).all (fun i => !isa.writesSp i) = true :=
    List.all_eq_true.mpr fun i hi => by
      obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hi
      simp only [copyDown, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl <;> rfl
  have hs : ∀ j, (storeAddrs j fns).all (fun i => !isa.writesSp i) = true := by
    induction fns with
    | nil => intro j; rfl
    | cons n ns ih => intro j; simp only [storeAddrs, List.all_append, ih, Bool.and_true]; rfl
  simp only [Impl.ForwardCall.X86_64.forwardS, Code.all, List.all_append, hc, hs, h, Bool.and_true]
  rfl

end

end VG.X86_64
