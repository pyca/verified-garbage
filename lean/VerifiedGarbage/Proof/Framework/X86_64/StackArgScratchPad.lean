module

public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchWipe
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.Offset

/-!
# A scratch buffer on the stack, after stack arguments, `pad` bytes up the frame (x86-64)

`Verified.stackArgScratchWipedXP`: `Verified.stackArgScratchWipedX`
(`StackArgScratch.lean`, `StackArgScratchWipe.lean`) for
`withStackArgScratchWipedXP`, whose buffer is `pad` bytes further up the
frame, at `rsp + 16 + 8m + pad`, so that code can keep it aligned as the
frame's own layout would not. The proofs are those of `pad` 0, with the
buffer's offset `16 + 8m + pad`; what does not depend on it is reused.
-/

@[expose] public section

namespace VG.X86_64.Pad

open VG VG.X86_64 VG.Impl.StackScratch.X86_64

variable {pad : Nat}

/-- `mov rax, rsp; add rax, 16 + 8m; mov [rsp + 8 + 8m], rax`: pass the buffer. -/
theorem tail_run {m : Nat} {w : State}
    (hw : InRegions w.wr (w.gpr .rsp + BitVec.ofNat 64 (8 + 8 * m)) 8) (hm : 16 + 8 * m + pad < 2 ^ 31) :
    ∃ w', execBlock isa [.mov .rax (.reg .rsp), .alu .add .rax (.imm (BitVec.ofNat 32 (16 + 8 * m + pad))),
        .store { base := .rsp, disp := ((8 + 8 * m : Nat) : Int) } .rax] w =
        some (w', [.addr (w.gpr .rsp + BitVec.ofNat 64 (8 + 8 * m))]) ∧
      w'.rd = w.rd ∧ w'.wr = w.wr ∧ w'.mxcsr = w.mxcsr ∧ (∀ q, q ≠ .rax → w'.gpr q = w.gpr q) ∧
      w'.mem = w.mem.writeW (w.gpr .rsp + BitVec.ofNat 64 (8 + 8 * m))
        (w.gpr .rsp + BitVec.ofNat 64 (16 + 8 * m + pad)) := by
  have hse : (BitVec.ofNat 32 (16 + 8 * m + pad)).signExtend 64 = BitVec.ofNat 64 (16 + 8 * m + pad) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_signExtend]
    have : (BitVec.ofNat 32 (16 + 8 * m + pad)).msb = false := by
      rw [BitVec.msb_eq_decide]; simp; omega_using [hm]
    simp [this]
    omega_using [hm]
  simp only [execBlock, isa, exec, readSrc, execAlu, Option.map_some, Option.bind_some, addrs,
    srcAddrs, State.store64, State.ea, ofInt_natCast]
  simp [State.setReg, arithFlags, State.setFlags, hw, hse]
  intro q hq; simp [hq]

/-- The state after `setArgsP bytes m pad` from `u`, if it runs. -/
def setArgsState (bytes m pad : Nat) (u : State) : State :=
  ((execBlock isa (setArgsP bytes m pad) u).map Prod.fst).getD u

/-- `setArgs`: the stack arguments copied into the frame, the buffer's
address after them; nothing else written, and only `rax` changed. -/
theorem setArgs_run {bytes m : Nat} {u : State}
    (hfit : bytes + 16 + 8 * m + pad ≤ 2 ^ 64) (hb : 8 * m + 8 ≤ bytes)
    (hm : 16 + 8 * m + pad < 2 ^ 31)
    (hr : ∀ j < m, InRegions (u.rd ++ u.wr) (u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * j)) 8)
    (hw : ∀ j ≤ m, InRegions u.wr (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * j)) 8) :
    execBlock isa (setArgsP bytes m pad) u = some (setArgsState bytes m pad u, setArgsTrace bytes (u.gpr .rsp) m) ∧
      (setArgsState bytes m pad u).rd = u.rd ∧ (setArgsState bytes m pad u).wr = u.wr ∧
      (setArgsState bytes m pad u).mxcsr = u.mxcsr ∧
      (∀ q, q ≠ .rax → (setArgsState bytes m pad u).gpr q = u.gpr q) ∧
      Frame [⟨u.gpr .rsp + 8, 8 * (m + 1)⟩] u.mem (setArgsState bytes m pad u).mem ∧
      (∀ j < m, (setArgsState bytes m pad u).mem.readW (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * j)) 64 =
        u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * j)) 64) ∧
      (setArgsState bytes m pad u).mem.readW (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * m)) 64 =
        u.gpr .rsp + BitVec.ofNat 64 (16 + 8 * m + pad) := by
  have hc := copies_run (bytes := bytes) (u := u) m hr (fun j hj => hw j (by omega_using [hj]))
  obtain ⟨f, hv⟩ := copiedState_mem (bytes := bytes) (u := u) m (by omega_using [hfit]) (by omega_using [hb])
  obtain ⟨w', ht, hrd, hwr, hmx, hg, hmem⟩ := tail_run (m := m) (w := copiedState bytes u m)
    (by simpa using hw m (Nat.le_refl _)) hm
  have hrun : execBlock isa (setArgsP bytes m pad) u = some (w', setArgsTrace bytes (u.gpr .rsp) m) := by
    rw [setArgsP, execBlock_append, hc]
    simp only [Option.bind_some, ht, Option.map_some, copiedState_rsp, setArgsTrace]
  have hst : setArgsState bytes m pad u = w' := by simp [setArgsState, hrun]
  rw [hst]
  have h8 : u.gpr .rsp + 8 = u.gpr .rsp + BitVec.ofNat 64 8 := rfl
  refine ⟨hrun, by rw [hrd, copiedState_rd], by rw [hwr, copiedState_wr],
    by rw [hmx, copiedState_mxcsr], fun q hq => ?_, ?_, fun j hj => ?_, ?_⟩
  · rw [hg q hq, copiedState_gpr _ _ hq]
  · rw [hmem, copiedState_rsp]
    refine (Frame.sub f fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_using [])⟩
    · rw [h8]
      exact Offset.contains _ (d := 8 + 8 * m) (e := 8) (k := 8 * (m + 1)) (by omega_using []) (by omega_using [])
        (by omega_using [hm])
  · rw [hmem, copiedState_rsp, Mem.readW_writeW_sep, hv j hj]
    · exact Offset.sep _ (d := 8 + 8 * j) (n := 8) (e := 8 + 8 * m) (k := 8) (by omega_using [hj]) (by omega_using [hm, hj])
        (by omega_using [hm])
    · decide
  · rw [hmem, copiedState_rsp, Mem.readW_writeW_self64]

/-! ## The run from `narrow` -/

/-- The regions of the contract with the buffer, from the state after
`setArgsP`: the buffers, the buffer, the lists of slices, and the copied stack
arguments. -/
def oldRegions (sig : Sig) (e : Elem) (n bytes pad : Nat) (s : State) : List (Region × Bool) :=
  (Sig.bufs sig.params (allArgs sig s) ++
    [(⟨s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (16 + 8 * nStack sig + pad), n * e.size⟩,
        true)]) ++
    (Sig.lists 64 s.mem sig.params (allArgs sig s)).map (fun r => (r, false)) ++
    [(⟨s.gpr .rsp - BitVec.ofNat 64 bytes + 8, 8 * (nStack sig + 1)⟩, false)]

/-- The state the code runs from, with the permissions of the contract with
the buffer: the state after the frame's push and `setArgs`, which may read
and write what the contract with the buffer lets it. -/
def narrowS (sig : Sig) (e : Elem) (n bytes pad : Nat) (s : State) : State :=
  (setArgsState bytes (nStack sig) pad (allocState bytes s)).withRegions
    (((oldRegions sig e n bytes pad s).filter (!·.2)).map (·.1))
    (((oldRegions sig e n bytes pad s).filter (·.2)).map (·.1))

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {stack bytes : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- What `setArgs` gives, from a state satisfying the contract without the
buffer. -/
theorem argsState_run {s : State} (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s)
    (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + pad + n * e.size ≤ bytes) (hb1 : bytes < 4096) :
    let u := allocState bytes s
    execBlock isa (setArgsP bytes (nStack sig) pad) u =
        some (setArgsState bytes (nStack sig) pad u, setArgsTrace bytes (u.gpr .rsp) (nStack sig)) ∧
      (setArgsState bytes (nStack sig) pad u).rd = u.rd ∧ (setArgsState bytes (nStack sig) pad u).wr = u.wr ∧
      (setArgsState bytes (nStack sig) pad u).mxcsr = s.mxcsr ∧
      (∀ q, q ≠ .rax → (setArgsState bytes (nStack sig) pad u).gpr q = u.gpr q) ∧
      Frame [⟨u.gpr .rsp + 8, 8 * (nStack sig + 1)⟩] s.mem (setArgsState bytes (nStack sig) pad u).mem ∧
      (∀ j < nStack sig, stackArg (setArgsState bytes (nStack sig) pad u) j = stackArg s j) ∧
      stackArg (setArgsState bytes (nStack sig) pad u) (nStack sig) =
        s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (16 + 8 * nStack sig + pad) := by
  intro u
  rw [pre_args hk] at hs
  obtain ⟨⟨hst, -⟩, hrd, -, -, -, -, -⟩ := hs
  have hsb : stack + bytes ≤ (s.gpr .rsp).toNat := by rcases hst with h | h <;> omega_using [h]
  have hesp : u.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes := allocState_rsp' _ _
  have hsrc : ∀ j, u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * j) = stackArgAddr s j := fun j => by
    rw [hesp, stackArgAddr, show bytes + 8 + 8 * j = bytes + 8 * (j + 1) by omega_using [], BitVec.ofNat_add,
      ← BitVec.add_assoc, BitVec.sub_add_cancel]
  -- The caller's stack arguments hold the sources.
  have hargs : ∀ j < nStack sig, InRegions (u.rd ++ u.wr) (stackArgAddr s j) 8 := fun j hj => by
    have h0 : ¬ (sig.words abi.ptrBits).length - 6 = 0 := by simp only [nStack] at hj; omega_using [hj]
    have hmem : (⟨stackArgAddr s 0, 8 * nStack sig⟩, false) ∈ allRegions sig s := by
      simp [allRegions, argArea, h0]
    have hc : (⟨stackArgAddr s 0, 8 * nStack sig⟩ : Region).Contains (stackArgAddr s j) 8 := by
      simp only [stackArgAddr]
      exact Offset.contains _ (d := 8 * (j + 1)) (n := 8) (e := 8 * (0 + 1)) (k := 8 * nStack sig)
        (by omega_using []) (by omega_using [hj]) (by omega_using [hb, hsb])
    refine ⟨_, List.mem_append_left _ ?_, hc⟩
    show _ ∈ s.rd
    rw [hrd]
    exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hmem, rfl⟩, rfl⟩
  have hframe : ∀ j ≤ nStack sig, InRegions u.wr (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * j)) 8 :=
    fun j hj => ⟨_, List.mem_cons_self .., by
      rw [hesp]; exact Offset.contains_base _ (by omega_using [hb, hj]) (by omega_using [hb, hsb, hj])⟩
  obtain ⟨hrun, hrd', hwr', hmx, hg, hf, hv, hlast⟩ := setArgs_run (bytes := bytes) (pad := pad)
    (m := nStack sig) (u := u) (by omega_using [hb, hb1]) (by omega_using [hb]) (by omega_using [hb, hb1])
    (fun j hj => by rw [hsrc]; exact hargs j hj) hframe
  have hrsp₂ : (setArgsState bytes (nStack sig) pad u).gpr .rsp = u.gpr .rsp := hg _ (by decide)
  refine ⟨hrun, hrd', hwr', hmx, hg, hf, fun j hj => ?_, ?_⟩
  · show (setArgsState bytes (nStack sig) pad u).mem.readW
      ((setArgsState bytes (nStack sig) pad u).gpr .rsp + BitVec.ofNat 64 (8 * (j + 1))) 64 = _
    rw [hrsp₂, show 8 * (j + 1) = 8 + 8 * j by omega_using [], hv j hj, hsrc]
    rfl
  · show (setArgsState bytes (nStack sig) pad u).mem.readW
      ((setArgsState bytes (nStack sig) pad u).gpr .rsp + BitVec.ofNat 64 (8 * (nStack sig + 1))) 64 = _
    rw [hrsp₂, show 8 * (nStack sig + 1) = 8 + 8 * nStack sig by omega_using [], hlast, hesp]





/-- What `narrowS` keeps of `s`, and what it holds. -/
theorem narrowS_facts (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + pad + n * e.size ≤ bytes) (hb1 : bytes < 4096) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) :
    (narrowS sig e n bytes pad s).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes ∧
      (∀ q, q ≠ .rax → q ≠ .rsp → (narrowS sig e n bytes pad s).gpr q = s.gpr q) ∧
      (narrowS sig e n bytes pad s).mxcsr = s.mxcsr ∧
      allArgs (sig.withScratch nm e n) (narrowS sig e n bytes pad s) =
        allArgs sig s ++ [s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (16 + 8 * nStack sig + pad)] ∧
      Frame [⟨s.gpr .rsp - BitVec.ofNat 64 bytes + 8, 8 * (nStack sig + 1)⟩]
        s.mem (narrowS sig e n bytes pad s).mem := by
  obtain ⟨-, -, -, hmx, hg, hf, hargs, hlast⟩ := argsState_run hs hk hb hb1
  have hg' : ∀ q, q ≠ .rax → q ≠ .rsp → (narrowS sig e n bytes pad s).gpr q = s.gpr q :=
    fun q h₁ h₂ => (hg q h₁).trans (allocState_gpr' _ _ h₂)
  refine ⟨(hg .rsp (by decide)).trans (allocState_rsp' _ _), hg', (by simpa only [narrowS, State.withRegions] using hmx), ?_, ?_⟩
  · rw [allArgs_withScratch sig nm e n hk s _ hg' fun j hj =>
      (stackArg_withRegions _ _ _ j).trans (hargs j hj)]
    exact congrArg (fun x => allArgs sig s ++ [x])
      ((stackArg_withRegions _ _ _ _).trans hlast)
  · rw [narrowS, State.withRegions_mem, ← allocState_rsp']
    exact hf


/-- The buffers and the lists of slices lie outside the copies of the stack
arguments. -/
theorem area_disj (hb : 16 + 8 * nStack sig + pad + n * e.size ≤ bytes) (hk : 6 ≤ (sig.words abi.ptrBits).length)
    {s : State} (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) :
    ∀ b ∈ bufRegions sig s, ∀ x, b.1.Contains x 1 →
      ¬ (⟨s.gpr .rsp - BitVec.ofNat 64 bytes + 8, 8 * (nStack sig + 1)⟩ : Region).Contains x 1 := by
  rw [pre_args hk] at hs
  obtain ⟨⟨hst, -⟩, -, -, -, hres, -, -⟩ := hs
  have hsb : stack + bytes ≤ (s.gpr .rsp).toNat := by rcases hst with h | h <;> omega_using [h]
  have hbelow : below (s.gpr .rsp) (stack + bytes) ∈
      (⟨s.gpr .rsp, 8⟩ :: stackBelow (s.gpr .rsp) (stack + bytes) : List Region) := by
    rw [stackBelow_pos _ (by omega_using [hb])]; simp
  intro b hb' x hx hc
  have harea : s.gpr .rsp - BitVec.ofNat 64 bytes + 8 = s.gpr .rsp - BitVec.ofNat 64 (bytes - 8) :=
    sub_add_ofNat _ (d := 8) (by omega_using [hb])
  rw [harea] at hc
  exact (Region.Disjoint.symm (hres _ hbelow b (List.mem_append_left _ hb'))).sub_right
    (Offset.sub_below _ (a := bytes - 8) (n := 8 * (nStack sig + 1)) (by omega_using []) (by omega_using [hb])) x hx hc

/-- The buffers and the lists of slices lie outside the frame: `narrowS`'s
memory is `s`'s there. -/
theorem narrowS_agreeL (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + pad + n * e.size ≤ bytes) (hb1 : bytes < 4096) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) :
    ∀ b ∈ bufRegions sig s, ∀ x, b.1.Contains x 1 → (narrowS sig e n bytes pad s).mem x = s.mem x := by
  obtain ⟨-, -, -, -, hf⟩ := narrowS_facts (nm := "") hk hb hb1 hs
  intro b hb' x hx
  refine hf x fun r hr hc => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact area_disj (n := n) (e := e) hb hk hs b hb' x hx hc

/-- The buffers lie outside the frame: `narrowS`'s memory is `s`'s there. -/
theorem narrowS_agree (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + pad + n * e.size ≤ bytes) (hb1 : bytes < 4096) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) :
    ∀ b ∈ Sig.bufs sig.params (allArgs sig s), ∀ x, b.1.Contains x 1 →
      (narrowS sig e n bytes pad s).mem x = s.mem x :=
  fun b hb' => narrowS_agreeL hk hb hb1 hs b (List.mem_append_left _ hb')

/-- The lists of slices lie outside the frame: `narrowS`'s memory is `s`'s
there. -/
theorem narrowS_agreeLists (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + pad + n * e.size ≤ bytes) (hb1 : bytes < 4096) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) :
    ∀ r ∈ Sig.lists 64 s.mem sig.params (allArgs sig s), ∀ x, r.Contains x 1 →
      (narrowS sig e n bytes pad s).mem x = s.mem x :=
  fun r hr => narrowS_agreeL hk hb hb1 hs (r, false)
    (List.mem_append_right _ (List.mem_map.mpr ⟨r, hr, rfl⟩))

/-- `narrowS`'s memory lists the same slices as `s`'s. -/
theorem narrowS_lists (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + pad + n * e.size ≤ bytes) (hb1 : bytes < 4096) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) :
    Sig.lists 64 (narrowS sig e n bytes pad s).mem sig.params (allArgs sig s) =
      Sig.lists 64 s.mem sig.params (allArgs sig s) :=
  (Sig.lists_eq_of_agree 64 fun r hr x hx => (narrowS_agreeLists hk hb hb1 hs r hr x hx).symm).symm

/-- The regions of the contract with the buffer, in `narrowS`, are
`oldRegions`. -/
theorem allRegions_narrowS (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + pad + n * e.size ≤ bytes) (hb1 : bytes < 4096) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) :
    allRegions (sig.withScratch nm e n) (narrowS sig e n bytes pad s) = oldRegions sig e n bytes pad s := by
  obtain ⟨hrsp, -, -, hargs, -⟩ := narrowS_facts (nm := nm) hk hb hb1 hs
  have hlen := allArgs_length sig s hk
  have h0 : ((sig.withScratch nm e n).words abi.ptrBits).length - 6 ≠ 0 := by
    rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega_using [hk]
  have hm : ((sig.withScratch nm e n).words abi.ptrBits).length - 6 = nStack sig + 1 :=
    nStack_withScratch sig nm e n hk
  rw [allRegions, bufRegions, hargs, argArea, ite_eq_right_of_eq_false _ _ (eq_false h0), hm,
    show (sig.withScratch nm e n).params = sig.params ++ [((nm, .array true e n) : String × Param)]
      from rfl, Sig.bufs_append_array abi.ptrBits nm e n _ sig.params _ hlen,
    Sig.lists_append_array 64 _ nm e n _ sig.params _ hlen, narrowS_lists hk hb hb1 hs]
  simp only [oldRegions, stackArgAddr, hrsp]
  rfl

/-- The precondition of the contract without the buffer gives the one with it
in `narrowS`, if the precondition reads memory only within the buffers and the
lists of slices. -/
theorem narrowS_pre (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + pad + n * e.size ≤ bytes) (hb1 : bytes < 4096)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      (∀ r ∈ Sig.lists abi.ptrBits m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) :
    (Sig.scratchContract abi sig nm e n pre post wa stack leak).pre (narrowS sig e n bytes pad s) := by
  obtain ⟨hrsp, -, -, hargs, -⟩ := narrowS_facts (nm := nm) hk hb hb1 hs
  have hall := allRegions_narrowS (nm := nm) hk hb hb1 hs
  have hagB := narrowS_agree (e := e) (n := n) hk hb hb1 hs
  have hagL := narrowS_agreeLists (e := e) (n := n) hk hb hb1 hs
  have hlists := narrowS_lists (e := e) (n := n) hk hb hb1 hs
  have hk' : 6 ≤ ((sig.withScratch nm e n).words abi.ptrBits).length := by
    rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega_using [hk]
  rw [pre_args hk] at hs
  obtain ⟨⟨hst, -⟩, -, -, hpw, hres, hnw, hpr⟩ := hs
  have hsb : stack + bytes ≤ (s.gpr .rsp).toNat := by rcases hst with h | h <;> omega_using [h]
  have hlen := allArgs_length sig s hk
  -- Addresses as offsets below `E`.
  have hscr : s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (16 + 8 * nStack sig + pad) =
      s.gpr .rsp - BitVec.ofNat 64 (bytes - (16 + 8 * nStack sig + pad)) := sub_add_ofNat _ (by omega_using [hb])
  have harea : s.gpr .rsp - BitVec.ofNat 64 bytes + 8 = s.gpr .rsp - BitVec.ofNat 64 (bytes - 8) :=
    sub_add_ofNat _ (d := 8) (by omega_using [hb])
  have hbelow : below (s.gpr .rsp) (stack + bytes) ∈
      (⟨s.gpr .rsp, 8⟩ :: stackBelow (s.gpr .rsp) (stack + bytes) : List Region) := by
    rw [stackBelow_pos _ (by omega_using [hb])]; simp
  -- The buffers and the lists lie outside the frame.
  have hout : ∀ a ∈ bufRegions sig s, ∀ {x k : Nat}, x ≤ stack + bytes →
      stack + bytes - x + k ≤ stack + bytes →
      a.1.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 x, k⟩ := fun a ha _ _ hx hk =>
    (Region.Disjoint.symm (hres _ hbelow a (List.mem_append_left _ ha))).sub_right
      (Offset.sub_below _ hx hk)
  have hB : ∀ a ∈ Sig.bufs sig.params (allArgs sig s), a ∈ bufRegions sig s :=
    fun a ha => List.mem_append_left _ ha
  have hL : ∀ a ∈ (Sig.lists 64 s.mem sig.params (allArgs sig s)).map (fun r => (r, false)),
      a ∈ bufRegions sig s := fun a ha => List.mem_append_right _ ha
  have hpwB : (bufRegions sig s).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) :=
    List.Pairwise.sublist (List.sublist_append_left _ _) hpw
  have hscrD : ∀ a ∈ bufRegions sig s, a.1.Disjoint
      ⟨s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (16 + 8 * nStack sig + pad), n * e.size⟩ :=
    fun a ha => by rw [hscr]; exact hout a ha (by omega_using []) (by omega_using [hb])
  have hareaD : ∀ a ∈ bufRegions sig s, a.1.Disjoint
      ⟨s.gpr .rsp - BitVec.ofNat 64 bytes + 8, 8 * (nStack sig + 1)⟩ :=
    fun a ha => by rw [harea]; exact hout a ha (by omega_using []) (by omega_using [hb])
  refine (pre_args (sig := sig.withScratch nm e n) (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
    (post := Curry.withScratch abi.ptrBits nm e n sig.params post) hk').mpr ?_
  rw [hall, hrsp, hargs]
  refine ⟨⟨.inr ?_, .inr ?_⟩, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [toNat_sub_ofNat (by omega_using [hsb])]; omega_using [hsb]
  · have hm := nStack_withScratch sig nm e n hk
    have hn : nStack sig = (sig.words abi.ptrBits).length - 6 := rfl
    simp only [nStack] at hm
    rw [toNat_sub_ofNat (by omega_using [hsb]), hm]; omega_using [hb, hsb, hn]
  · -- Pairwise disjoint.
    simp only [bufRegions, List.pairwise_append] at hpwB
    obtain ⟨pB, pL, pBL⟩ := hpwB
    have hsa : (⟨s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (16 + 8 * nStack sig + pad), n * e.size⟩ :
        Region).Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 bytes + 8, 8 * (nStack sig + 1)⟩ := by
      rw [show s.gpr .rsp - BitVec.ofNat 64 bytes + 8 =
        s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 8 from rfl]
      exact Offset.disjoint _ (d := 16 + 8 * nStack sig + pad) (n := n * e.size) (e := 8)
        (k := 8 * (nStack sig + 1)) (.inr (by omega_using [])) (by omega_using [hb, hsb]) (by omega_using [hb, hsb])
    simp only [oldRegions, List.pairwise_append, List.pairwise_singleton, List.mem_append,
      List.mem_singleton]
    refine ⟨⟨⟨pB, trivial, fun a ha b hb _ => ?_⟩, pL, fun a ha b hb hab => ?_⟩, trivial,
      fun a ha b hb _ => ?_⟩
    · subst hb; exact hscrD a (hB a ha)
    · rcases ha with ha | rfl
      · exact pBL a ha b hb hab
      · exact (hscrD b (hL b hb)).symm
    · subst hb
      rcases ha with (ha | rfl) | ha
      · exact hareaD a (hB a ha)
      · exact hsa
      · exact hareaD a (hL a ha)
  · -- The reserved stack: the frame's first quadword and the stack below it.
    intro r hr a ha
    have hr' : r = ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, 8⟩ ∨
        (0 < stack ∧ r = below (s.gpr .rsp - BitVec.ofNat 64 bytes) stack) := by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact .inl rfl
      · rcases Nat.eq_zero_or_pos stack with h0 | h0
        · subst h0; simp [stackBelow] at hr
        · rw [stackBelow_pos _ h0, List.mem_singleton] at hr; exact .inr ⟨h0, hr⟩
    have hold : ∀ a ∈ bufRegions sig s, r.Disjoint a.1 := fun a ha => by
      rcases hr' with rfl | ⟨-, rfl⟩
      · exact Region.Disjoint.symm (hout a ha (by omega_using []) (by omega_using [hb]))
      · exact (Region.Disjoint.symm (hout a ha (x := stack + bytes) (k := stack + bytes)
          (by omega_using []) (by omega_using []))).sub_left (below_below _ bytes stack)
    simp only [oldRegions, List.mem_append, List.mem_singleton] at ha
    rcases ha with ((ha | rfl) | ha) | rfl
    · exact hold a (hB a ha)
    · rcases hr' with rfl | ⟨h0, rfl⟩
      · exact Offset.base_disjoint _ (e := 16 + 8 * nStack sig + pad) (k := 8) (by omega_using []) (by omega_using [hb, hsb])
      · exact Region.Disjoint.symm (Offset.disjoint_below _ (n := stack) (d := 16 + 8 * nStack sig + pad)
          (k := n * e.size) (by omega_using [hb, hsb]))
    · exact hold a (hL a ha)
    · rw [show s.gpr .rsp - BitVec.ofNat 64 bytes + 8 =
        s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 8 from rfl]
      rcases hr' with rfl | ⟨h0, rfl⟩
      · exact Offset.base_disjoint _ (e := 8) (k := 8) (Nat.le_refl _) (by omega_using [hb, hsb])
      · exact Region.Disjoint.symm (Offset.disjoint_below _ (n := stack) (d := 8)
          (k := 8 * (nStack sig + 1)) (by omega_using [hb, hsb]))
  · -- No buffer or list wraps around.
    intro a ha
    rw [bufRegions, hargs, show (sig.withScratch nm e n).params = sig.params ++ [((nm, .array true e n) : String × Param)]
      from rfl, Sig.bufs_append_array abi.ptrBits nm e n _ sig.params _ hlen,
      Sig.lists_append_array 64 _ nm e n _ sig.params _ hlen, hlists] at ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · exact hnw a (hB a ha)
      · simp only [List.mem_singleton] at ha; subst ha
        show (s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (16 + 8 * nStack sig + pad)).toNat +
          n * e.size ≤ 2 ^ 64
        rw [hscr, toNat_sub_ofNat (by omega_using [hsb])]
        have := (s.gpr .rsp).isLt
        omega_using [hb, hsb]
    · exact hnw a (hL a ha)
  · -- The precondition, which reads only the buffers and the lists.
    refine Eq.mpr (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params pre _ _ hlen) _) ?_
    exact hpre _ _ _ hlen (fun b hb x hx => (hagB b hb x hx).symm)
      (fun r hr x hx => (hagL r hr x hx).symm) hpr

/-- The public data of the contract without the buffer is public in
`narrowS` for the contract with it. -/
theorem narrowS_pub (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + pad + n * e.size ≤ bytes) (hb1 : bytes < 4096) {s₁ s₂ : State}
    (h₁ : (sig.contract abi pre post wa (stack + bytes) leak).pre s₁)
    (h₂ : (sig.contract abi pre post wa (stack + bytes) leak).pre s₂)
    (hp : (sig.contract abi pre post wa (stack + bytes) leak).pub s₁ s₂)
    (hleak : Sig.LeakLocalL abi.ptrBits sig leak := by trivial) :
    (Sig.scratchContract abi sig nm e n pre post wa stack leak).pub (narrowS sig e n bytes pad s₁)
      (narrowS sig e n bytes pad s₂) := by
  have hk' : 6 ≤ ((sig.withScratch nm e n).words abi.ptrBits).length := by
    rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega_using [hk]
  rw [pubL_args hk] at hp
  obtain ⟨⟨hsp, hlk⟩, hpa, hdesc⟩ := hp
  obtain ⟨e₁, -, -, a₁, -⟩ := narrowS_facts (nm := nm) (e := e) (n := n) hk hb hb1 h₁
  obtain ⟨e₂, -, -, a₂, f₂⟩ := narrowS_facts (nm := nm) (e := e) (n := n) hk hb hb1 h₂
  have l₁ := allArgs_length sig s₁ hk
  have l₂ := allArgs_length sig s₂ hk
  have hL₁ : ∀ r ∈ Sig.lists abi.ptrBits (narrowS sig e n bytes pad s₁).mem sig.params (allArgs sig s₁),
      ∀ x, r.Contains x 1 → (narrowS sig e n bytes pad s₁).mem x = s₁.mem x := fun r hr =>
    narrowS_agreeLists hk hb hb1 h₁ r ((narrowS_lists hk hb hb1 h₁) ▸ hr)
  have hL₂ : ∀ r ∈ Sig.lists abi.ptrBits (narrowS sig e n bytes pad s₂).mem sig.params (allArgs sig s₂),
      ∀ x, r.Contains x 1 → (narrowS sig e n bytes pad s₂).mem x = s₂.mem x := fun r hr =>
    narrowS_agreeLists hk hb hb1 h₂ r ((narrowS_lists hk hb hb1 h₂) ▸ hr)
  refine (pubL_args (sig := sig.withScratch nm e n)
    (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
    (post := Curry.withScratch abi.ptrBits nm e n sig.params post) hk').mpr ?_
  rw [e₁, e₂, a₁, a₂, hsp,
    show (sig.withScratch nm e n).params = sig.params ++ [((nm, .array true e n) : String × Param)]
      from rfl, Sig.descs_append_array 64 nm e n _ sig.params _ l₁]
  refine ⟨⟨rfl, leakAgree_withScratchL hleak _ _ l₁ l₂ (narrowS_agree hk hb hb1 h₁) hL₁
    (narrowS_agree hk hb hb1 h₂) hL₂ hlk⟩, fun i hi => ?_, fun r hr i hi => ?_⟩
  rotate_left
  · have hx : r.Contains (r.base + BitVec.ofNat 64 i) 1 := Region.contains_ofNat r.base hi
    have hr' : r ∈ Sig.lists 64 s₁.mem sig.params (allArgs sig s₁) := Sig.descs_sub_lists 64 _ _ _ r hr
    rw [narrowS_agreeLists hk hb hb1 h₁ r hr' _ hx, hdesc r hr i hi]
    refine (f₂ _ fun q hq hc => ?_).symm
    simp only [List.mem_singleton] at hq; subst hq
    rw [← hsp] at hc
    exact area_disj (n := n) (e := e) hb hk h₁ (r, false)
      (List.mem_append_right _ (List.mem_map.mpr ⟨r, hr', rfl⟩)) _ hx hc
  have lp := Sig.pubs_length sig.params abi.ptrBits
  have hps : ((sig.params ++ [((nm, .array true e n) : String × Param)]).flatMap (·.2.pubs)) =
      sig.params.flatMap (·.2.pubs) ++ [true] := by
    simp [Param.pubs]
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
    rw [List.getElem?_append_right (by omega_using [l₁, hik]), List.getElem?_append_right (by omega_using [l₂, hik]), l₁, l₂]

/-- A run of the code from `narrowS s` is a run of `withStackArgScratch`
from `s`, after `setArgs`'s accesses, which keeps what the calling convention
requires, and whose memory and `rax` are those of the code's run. -/
theorem withStackArgScratch_run {c : Prog isa} (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + pad + n * e.size ≤ bytes ∧ bytes < 4096 ∧ bytes % 8 = 0)
    (hst : stack + bytes + 8 ≤ 2 ^ 64) (hsafe : SpSafe c) (hd : c.x86_64Depth ≤ stack) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) {t : List Leak} {s₃ : State}
    (he : Exec isa c (narrowS sig e n bytes pad s) t s₃) (ha : abiPreserved (narrowS sig e n bytes pad s) s₃) :
    Exec isa (withStackArgScratchP bytes (nStack sig) pad c) s
        (setArgsTrace bytes (s.gpr .rsp - BitVec.ofNat 64 bytes) (nStack sig) ++ t)
        (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr .rax = s₃.gpr .rax := by
  obtain ⟨hb, hb1, hb2⟩ := hb
  obtain ⟨hrun, hrd', hwr', -, -, -, -, -⟩ := argsState_run hs hk hb hb1
  obtain ⟨hrsp, hg, hmx, -, hf⟩ := narrowS_facts (nm := "") hk hb hb1 hs
  rw [pre_args hk] at hs
  obtain ⟨⟨hwf, -⟩, hrd, hwr, -, hres, -, -⟩ := hs
  have hsb : stack + bytes ≤ (s.gpr .rsp).toNat := by rcases hwf with h | h <;> omega_using [h]
  -- The frame's push and `setArgs`.
  have hpush : isa.push (.alloc bytes) s = some (allocState bytes s) := by
    simp only [isa, push, allocState]
    exact ite_eq_left ⟨by omega_using [hb], hb1, hb2, by omega_using [hsb]⟩
  -- The regions of `narrowS`: the buffers, and the frame's buffer and copies.
  have hF : ∀ {a k : Nat}, a ≤ bytes → bytes - a + k ≤ bytes →
      Covers [⟨s.gpr .rsp - BitVec.ofNat 64 a, k⟩] (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) :=
    fun ha hk => Covers.one ⟨_, List.mem_cons_self .., Offset.contains_below _ ha hk (by omega_using [hsb])⟩
  have hscr : s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (16 + 8 * nStack sig + pad) =
      s.gpr .rsp - BitVec.ofNat 64 (bytes - (16 + 8 * nStack sig + pad)) := sub_add_ofNat _ (by omega_using [hb])
  have harea : s.gpr .rsp - BitVec.ofNat 64 bytes + 8 = s.gpr .rsp - BitVec.ofNat 64 (bytes - 8) :=
    sub_add_ofNat _ (d := 8) (by omega_using [hb])
  have hbufR : ∀ a ∈ Sig.bufs sig.params (allArgs sig s), a.2 = false → a.1 ∈ s.rd := fun a ha h => by
    rw [hrd]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ ha),
      by simp [h]⟩, rfl⟩
  have hlistR : ∀ a ∈ (Sig.lists 64 s.mem sig.params (allArgs sig s)).map (fun r => (r, false)),
      a.1 ∈ s.rd := fun a ha => by
    rw [hrd]
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp ha
    exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_right _ ha),
      rfl⟩, rfl⟩
  have hbufW : ∀ a ∈ Sig.bufs sig.params (allArgs sig s), a.2 = true → a.1 ∈ s.wr := fun a ha h => by
    rw [hwr]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ ha), h⟩,
      rfl⟩
  have hcovW : Covers (((oldRegions sig e n bytes pad s).filter (·.2)).map (·.1))
      (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) := by
    refine Covers.of_forall fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    simp only [oldRegions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ((ha | rfl) | ha) | rfl
    · exact Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact List.mem_cons_of_mem _ (hbufW a ha hf')
    · rw [hscr]; exact hF (by omega_using []) (by omega_using [hb])
    · obtain ⟨r, -, rfl⟩ := List.mem_map.mp ha; simp at hf'
    · simp at hf'
  have hcovR : Covers (((oldRegions sig e n bytes pad s).filter (!·.2)).map (·.1))
      (s.rd ++ ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) := by
    refine Covers.of_forall fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    simp only [oldRegions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ((ha | rfl) | ha) | rfl
    · exact Covers.left (Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact hbufR a ha (by simpa using hf'))
    · simp at hf'
    · exact Covers.left (Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact hlistR a ha)
    · exact Covers.right (by rw [harea]; exact hF (by omega_using []) (by omega_using [hb]))
  have hw := Exec.widen he (rd := s.rd) (wr := ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)
    (Covers.append_left hcovR (Covers.right hcovW)) hcovW
  rw [show (narrowS sig e n bytes pad s).withRegions s.rd
      (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) =
      setArgsState bytes (nStack sig) pad (allocState bytes s) by
    rw [narrowS, State.withRegions_withRegions,
      show s.rd = (allocState bytes s).rd from rfl, ← hrd',
      show ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr = (allocState bytes s).wr from rfl,
      ← hwr', State.withRegions_self]] at hw
  -- The pop.
  have hrsp₃ : s₃.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes :=
    (ha.1 .rsp (by simp [calleeSaved])).trans hrsp
  have hpop : isa.pop (.free bytes) (allocState bytes s)
      (s₃.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)) =
      some (popState bytes s s₃) := by
    simp only [isa, pop, State.withRegions_gpr, State.withRegions_wr]
    refine ite_eq_left ⟨by omega_using [hb], hb1, hb2, ?_, rfl, ?_⟩
    · rw [hrsp₃]; simp [allocState, State.setReg]
    · simp [allocState, State.setReg]
  have hex := Exec.frame hpush (Exec.seq (Exec.block hrun) hw) hpop
  simp only [isa, addrs, List.map_nil, List.nil_append, List.append_nil, allocState_rsp'] at hex
  refine ⟨hex, ⟨fun q hq => ?_, ?_, ?_⟩, rfl, ?_⟩
  · -- The callee-saved registers.
    simp only [popState, State.setReg, State.withRegions_gpr]
    by_cases hqs : q = .rsp
    · subst hqs; simp only [ite_true, hrsp₃, BitVec.sub_add_cancel]
    · simp only [hqs, ite_false]
      have hqa : q ≠ .rax := fun h => by subst h; simp [calleeSaved] at hq
      rw [ha.1 q hq, hg q hqa hqs]
  · -- The return address: the code writes only its regions and below `rsp`.
    have hfs := Exec.stackFrame hsafe he (by omega_using [hd, hsb])
    show s₃.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64
    have hR : ∀ {x k : Nat}, x ≤ stack + bytes → stack + bytes - x + k ≤ stack + bytes →
        (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 x, k⟩ := fun hx hk =>
      (Offset.base_disjoint_below _ (n := stack + bytes) (k := 8) (by omega_using [hst])).sub_right
        (Offset.sub_below _ hx hk)
    rw [hfs.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) ?_ (by decide)]
    · exact hf.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [harea]; exact hR (by omega_using []) (by omega_using [hb]))
        (by decide)
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
        obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
        simp only [oldRegions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with ((ha | rfl) | ha) | rfl
        · exact hres _ (List.mem_cons_self ..) a (List.mem_append_left _ (List.mem_append_left _ ha))
        · rw [hscr]; exact hR (by omega_using []) (by omega_using [hb])
        · exact hres _ (List.mem_cons_self ..) a (List.mem_append_left _ (List.mem_append_right _ ha))
        · rw [harea]; exact hR (by omega_using []) (by omega_using [hb])
      · simp only [List.mem_singleton] at hr; subst hr
        rw [hrsp]
        show (⟨s.gpr .rsp, 8⟩ : Region).Disjoint
          ⟨s.gpr .rsp - BitVec.ofNat 64 bytes - BitVec.ofNat 64 c.x86_64Depth, c.x86_64Depth⟩
        rw [BitVec.sub_sub, ← BitVec.ofNat_add]
        exact hR (by omega_using [hd]) (by omega_using [hd])
  · -- MXCSR.
    show s₃.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
    rw [ha.2.2, hmx]
  · simp [popState, State.setReg]

/-- Code verified for a function whose last argument, a scratch buffer of `n`
elements `e`, is passed on the stack after the six argument registers and
`nStack sig` other stack arguments, with `stack` bytes of stack, is verified
for the function without it, which allocates the buffer in a frame of
`bytes` more bytes of stack (`withStackArgScratch`), if its precondition,
postcondition and leak read memory only within the function's buffers and its
lists of slices (`hpre`, `hpost`, `hleak`, which holds of no leak). -/
theorem Verified.stackArgScratchL {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack leak))
    (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + pad + n * e.size ≤ bytes ∧ bytes < 4096 ∧ bytes % 8 = 0)
    (hst : stack + bytes + 8 ≤ 2 ^ 64)
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ stack)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      (∀ r ∈ Sig.lists abi.ptrBits m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      (∀ r ∈ Sig.lists abi.ptrBits m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' r →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' r)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes)).pre s)
    (hleak : Sig.LeakLocalL abi.ptrBits sig leak := by trivial) :
    Verified target (withStackArgScratchP bytes (nStack sig) pad c)
      (sig.contract abi pre post wa (stack + bytes) leak) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hsafe := SpSafe.of_all hsp
  have hk' : 6 ≤ ((sig.withScratch nm e n).words abi.ptrBits).length := by
    rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega_using [hk]
  -- Every run is `setArgs`, then the code's run from `narrowS`.
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes) leak).pre s → ∃ t s₃,
      Exec isa c (narrowS sig e n bytes pad s) t s₃ ∧
      (Sig.scratchContract abi sig nm e n pre post wa stack leak).post (narrowS sig e n bytes pad s) s₃ ∧
      Exec isa (withStackArgScratchP bytes (nStack sig) pad c) s
        (setArgsTrace bytes (s.gpr .rsp - BitVec.ofNat 64 bytes) (nStack sig) ++ t)
        (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr .rax = s₃.gpr .rax := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrowS_pre hk hb.1 hb.2.1 hpre hs)
    exact ⟨t, s₃, he, hq, withStackArgScratch_run hk hb hst hsafe hd hs he ha⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, -, hq, hex, ha, hm, hrax⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    rw [post_args hk]
    have hq' := (post_args (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post) hk').mp hq
    obtain ⟨-, -, -, hargs, -⟩ := narrowS_facts (nm := nm) hk hb.1 hb.2.1 hs
    rw [hargs] at hq'
    rw [hm, hrax]
    have hq'' := Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n
      sig.params post _ _ (allArgs_length sig s hk)) _) s₃.mem) _) hq'
    exact hpost _ _ _ _ _ (allArgs_length sig s hk) (narrowS_agree hk hb.1 hb.2.1 hs)
      (fun r hr x hx => narrowS_agreeLists hk hb.1 hb.2.1 hs r ((narrowS_lists hk hb.1 hb.2.1 hs) ▸ hr) x hx) hq''
  · obtain ⟨u₁, r₁, f₁, -, x₁, -⟩ := hrun s₁ h₁
    obtain ⟨u₂, r₂, f₂, -, x₂, -⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1, ((pubL_args hk).mp hp).1.1,
      hct _ _ _ _ _ _ (narrowS_pre hk hb.1 hb.2.1 hpre h₁) (narrowS_pre hk hb.1 hb.2.1 hpre h₂)
        (narrowS_pub hk hb.1 hb.2.1 h₁ h₂ hp hleak) f₁ f₂]

/-- `Verified.stackArgScratchL`, for a precondition, postcondition and leak
that read memory only within the function's buffers. -/
theorem Verified.stackArgScratch {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack leak))
    (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + pad + n * e.size ≤ bytes ∧ bytes < 4096 ∧ bytes % 8 = 0)
    (hst : stack + bytes + 8 ≤ 2 ^ 64)
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ stack)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' r →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' r)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes)).pre s)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak := by trivial) :
    Verified target (withStackArgScratchP bytes (nStack sig) pad c)
      (sig.contract abi pre post wa (stack + bytes) leak) :=
  Verified.stackArgScratchL h hk hb hst hsp hd (fun vs m₁ m₂ hl hb _ => hpre vs m₁ m₂ hl hb)
    (fun vs m₁ m₂ m' r hl hb _ => hpost vs m₁ m₂ m' r hl hb) hsat hleak.toL

/-- `withStackArgScratch` writes `rsp` only in its frame if its code does. -/
theorem withStackArgScratchP_spSafe {bytes m : Nat} {c : Prog isa}
    (h : c.all (fun i => !isa.writesSp i) = true) :
    (withStackArgScratchP bytes m pad c).all (fun i => !isa.writesSp i) = true := by
  have hc : ((List.range m).flatMap (copyArg bytes)).all (fun i => !isa.writesSp i) = true :=
    List.all_eq_true.mpr fun i hi => by
      obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hi
      simp only [copyArg, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl <;> rfl
  simp only [withStackArgScratchP, setArgsP, Code.all, List.all_append, h, hc, Bool.and_true,
    Bool.true_and]
  rfl

end

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {stack bytes words : Nat}

/-- Code verified for a function whose last argument, a scratch buffer of `n`
elements `e`, is passed on the stack after the six argument registers and
`nStack sig` other stack arguments, with `stack` bytes of stack, is verified
for the function without it, which allocates the buffer in a frame of
`bytes` more bytes of stack and zeroes its first `w.len` bytes after the
code with the wipe `w`, if its precondition reads memory only within the
function's buffers (`hpre`), and its postcondition both the memory on entry
and the memory on return (`hpost`, `hpostOut`). -/
theorem Verified.stackArgScratchWipedBy (w : Wiper) {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack))
    (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + pad + n * e.size ≤ bytes ∧ bytes < 4096 ∧ bytes % 8 = 0)
    (hst : stack + bytes + 8 ≤ 2 ^ 64)
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ stack)
    (hw : w.len ≤ n * e.size)
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
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes)).pre s) :
    Verified target (withStackArgScratchP bytes (nStack sig) pad (.seq c (.block (w.code (16 + 8 * nStack sig + pad)))))
      (sig.contract abi pre post wa (stack + bytes)) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hsafe : SpSafe (.seq c (.block (w.code (16 + 8 * nStack sig + pad))) : Prog isa) :=
    SpSafe.of_all (by simp only [Code.all, hsp, w.spSafe, Bool.and_self])
  have hdep : (Code.seq c (.block (w.code (16 + 8 * nStack sig + pad))) : Prog isa).x86_64Depth ≤
      stack := by
    simp only [Code.x86_64Depth]; omega_using [hd]
  have hk' : 6 ≤ ((sig.withScratch nm e n).words abi.ptrBits).length := by
    rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega_using [hk]
  obtain ⟨hb0, hb1, hb2⟩ := hb
  -- The buffer, below the stack the contract without it reserves, so apart
  -- from its buffers.
  have hdisj : ∀ s, (sig.contract abi pre post wa (stack + bytes)).pre s →
      ∀ b ∈ Sig.bufs sig.params (allArgs sig s),
        b.1.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (16 + 8 * nStack sig + pad),
          n * e.size⟩ := by
    intro s hs b hb'
    rw [pre_args hk] at hs
    obtain ⟨⟨hwf, -⟩, -, -, -, hres, -, -⟩ := hs
    have hsb : stack + bytes ≤ (s.gpr .rsp).toNat := by rcases hwf with h | h <;> omega_using [h]
    have hbelow : below (s.gpr .rsp) (stack + bytes) ∈
        (⟨s.gpr .rsp, 8⟩ :: stackBelow (s.gpr .rsp) (stack + bytes) : List Region) := by
      rw [stackBelow_pos _ (by omega_using [hb0])]; simp
    rw [sub_add_ofNat _ (by omega_using [hb0])]
    exact (Region.Disjoint.symm (hres _ hbelow b (List.mem_append_left _ (List.mem_append_left _ hb')))).sub_right
      (Offset.sub_below _ (by omega_using []) (by omega_using [hb0]))
  -- Every run is `setArgs`, then the code's run from `narrowS`, then the wipe.
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes)).pre s → ∃ t s₃ u,
      Exec isa c (narrowS sig e n bytes pad s) t s₃ ∧
      (Sig.scratchContract abi sig nm e n pre post wa stack).post (narrowS sig e n bytes pad s) s₃ ∧
      Frame [⟨s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (16 + 8 * nStack sig + pad),
        n * e.size⟩] s₃.mem u.mem ∧
      Exec isa (withStackArgScratchP bytes (nStack sig) pad (.seq c (.block (w.code (16 + 8 * nStack sig + pad))))) s
        (setArgsTrace bytes (s.gpr .rsp - BitVec.ofNat 64 bytes) (nStack sig) ++
          (t ++ w.trace (s.gpr .rsp - BitVec.ofNat 64 bytes) (16 + 8 * nStack sig + pad)))
        (popState bytes s u) ∧
      abiPreserved s (popState bytes s u) ∧ (popState bytes s u).mem = u.mem ∧
      (popState bytes s u).gpr .rax = s₃.gpr .rax := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrowS_pre hk hb0 hb1 (fun vs m₁ m₂ hl hb _ => hpre vs m₁ m₂ hl hb) hs)
    obtain ⟨hrsp, -, -, -, -⟩ := narrowS_facts (nm := nm) hk hb0 hb1 hs
    have hrsp₃ : s₃.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes :=
      (ha.1 .rsp (by simp [calleeSaved])).trans hrsp
    have hwr₃ : s₃.wr = (narrowS sig e n bytes pad s).wr := (Exec.rdwr he).2
    have hbuf : (⟨s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (16 + 8 * nStack sig + pad),
        n * e.size⟩ : Region) ∈ s₃.wr := by
      rw [hwr₃]
      simp [narrowS, oldRegions, List.filter_append]
    obtain ⟨u, hblk, hfr, hg, hmx, -, -⟩ := w.run _ s₃ (16 + 8 * nStack sig + pad) hbuf
      (fun a k hak => by
        rw [hrsp₃]
        exact Offset.contains _ (by omega_using []) (by omega_using [hw, hak]) (by omega_using [hb0, hb1]))
    have he' := Exec.seq he (Exec.block hblk)
    rw [hrsp₃] at he'
    have ha' : abiPreserved (narrowS sig e n bytes pad s) u := by
      refine ⟨fun q hq => ?_, ?_, by rw [hmx]; exact ha.2.2⟩
      · rw [hg q (.inl hq)]
        exact ha.1 q hq
      · rw [hrsp]
        rw [hfr.readW (r := ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, 8⟩) (Region.contains_self _ _)
          (fun r' hr' => by
            simp only [List.mem_singleton] at hr'; subst hr'
            exact Offset.base_disjoint _ (e := 16 + 8 * nStack sig + pad) (k := 8) (by omega_using []) (by omega_using [hb0, hb1]))
          (by decide)]
        have h2 := ha.2.1
        rwa [hrsp] at h2
    obtain ⟨hex, habi, hm, hrax⟩ :=
      withStackArgScratch_run hk ⟨hb0, hb1, hb2⟩ hst hsafe hdep hs he' ha'
    exact ⟨t, s₃, u, he, hq, hfr, hex, habi, hm, by rw [hrax, hg .rax (.inr rfl)]⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, u, -, hq, hfr, hex, ha, hm, hrax⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    rw [post_args hk]
    have hq' := (post_args (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post) hk').mp hq
    obtain ⟨-, -, -, hargs, -⟩ := narrowS_facts (nm := nm) hk hb0 hb1 hs
    rw [hargs] at hq'
    rw [hm, hrax]
    have h₃ := Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n
      sig.params post _ _ (allArgs_length sig s hk)) _) s₃.mem) _) hq'
    have h₄ := hpost _ _ _ _ _ (allArgs_length sig s hk) (narrowS_agree hk hb0 hb1 hs) h₃
    refine hpostOut _ _ _ _ _ (allArgs_length sig s hk) (fun b hb' a ha' => ?_) h₄
    exact (hfr a fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hdisj s hs b hb' a ha').symm
  · obtain ⟨u₁, _, _, f₁, _, _, x₁, _⟩ := hrun s₁ h₁
    obtain ⟨u₂, _, _, f₂, _, _, x₂, _⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1]
    have hsp₁₂ : s₁.gpr .rsp = s₂.gpr .rsp := ((pub_args hk).mp hp).1
    rw [hct _ _ _ _ _ _ (narrowS_pre hk hb0 hb1 (fun vs m₁ m₂ hl hb _ => hpre vs m₁ m₂ hl hb) h₁)
      (narrowS_pre hk hb0 hb1 (fun vs m₁ m₂ hl hb _ => hpre vs m₁ m₂ hl hb) h₂)
      (narrowS_pub hk hb0 hb1 h₁ h₂ hp) f₁ f₂, hsp₁₂]


/-- `Verified.stackArgScratchWipedBy`, for `withStackArgScratchWipedX`, which
zeroes the first `k` 16-byte words of the buffer. -/
theorem Verified.stackArgScratchWipedXP {c : Prog isa} {k : Nat}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack))
    (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + pad + n * e.size ≤ bytes ∧ bytes < 4096 ∧ bytes % 8 = 0)
    (hst : stack + bytes + 8 ≤ 2 ^ 64)
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ stack)
    (hw : 16 * k ≤ n * e.size)
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
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes)).pre s) :
    Verified target (withStackArgScratchWipedXP bytes (nStack sig) pad k c)
      (sig.contract abi pre post wa (stack + bytes)) :=
  Verified.stackArgScratchWipedBy (.x k) h hk hb hst hsp hd hw hpre hpost hpostOut hsat

/-- So does `withStackArgScratchWipedX`. -/
theorem withStackArgScratchWipedXP_spSafe {bytes m k : Nat} {c : Prog isa}
    (h : c.all (fun i => !isa.writesSp i) = true) :
    (withStackArgScratchWipedXP bytes m pad k c).all (fun i => !isa.writesSp i) = true :=
  withStackArgScratchP_spSafe (by simp only [Code.all, h, wipeAtX_spSafe, Bool.and_self])

end

end VG.X86_64.Pad
