module

-- separate module: its proofs (about 5 s) build in parallel with `RefillCorrect`'s, which `RefillBackend` also imports

public import VerifiedGarbage.Proof.Dsa.ParameterPublic
public import VerifiedGarbage.Impl.Dsa.X86_64.ParameterSearch
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillContract
public import VerifiedGarbage.Proof.Framework.X86_64.ForwardCall
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.EntryBranch
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.TCB.Registration

/-! # The refillable-tape search by the public modulus width, on x86-64

`ParameterSearch.widths` (`Impl/Dsa/X86_64/ParameterSearch.lean`) loads
`state[1]`, the modulus's width, and calls the function for that width,
forwarding its arguments (`Verified.forward`, two of them on the stack): it is
verified against the search's contract from its width functions'
(`Refill.contract`, the search's contract with the width fixed), by choosing
on entry (`Verified.entryBranch`), as `Generation.Widths` does for
`vg_dsa_generate_parameters`. The width functions' stack `S` grows by the
forwarding frame's 56 octets and the call's return address: the search's
contract has `S + 64`.
-/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation.RefillWidths
open VG VG.X86_64
open VG.Spec.Rsa (bytesAt wordsAt)

/-! ## Memory a buffer holds -/

theorem bytesAt_congr {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) : bytesAt m₁ p n = bytesAt m₂ p n := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => h _ ?_
  have hi := List.mem_range.mp hi
  by_cases hw : i < 2 ^ 64
  · exact Offset.contains_base _ (by omega_arith) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega_arith

theorem readW_congr {m₁ m₂ : Mem} {p : Addr} {k : Nat} (hk : k + 8 ≤ 32)
    (h : ∀ a, Region.Contains ⟨p, 32⟩ a 1 → m₁ a = m₂ a) :
    m₁.readW (p + BitVec.ofNat 64 k) 64 = m₂.readW (p + BitVec.ofNat 64 k) 64 :=
  Mem.readW_congr fun i hi => h _ (by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith))

theorem readW_congr0 {m₁ m₂ : Mem} {p : Addr}
    (h : ∀ a, Region.Contains ⟨p, 32⟩ a 1 → m₁ a = m₂ a) : m₁.readW p 64 = m₂.readW p 64 := by
  have := readW_congr (k := 0) (by omega_arith) h
  rwa [show p + BitVec.ofNat 64 0 = p from BitVec.add_zero p] at this

theorem readW_congr8 {m₁ m₂ : Mem} {p : Addr}
    (h : ∀ a, Region.Contains ⟨p, 32⟩ a 1 → m₁ a = m₂ a) : m₁.readW (p + 8) 64 = m₂.readW (p + 8) 64 :=
  readW_congr (k := 8) (by omega_arith) h

theorem readW_congr16 {m₁ m₂ : Mem} {p : Addr}
    (h : ∀ a, Region.Contains ⟨p, 32⟩ a 1 → m₁ a = m₂ a) : m₁.readW (p + 16) 64 = m₂.readW (p + 16) 64 :=
  readW_congr (k := 16) (by omega_arith) h

theorem wordsAt_congr {m₁ m₂ : Mem} {p : Addr}
    (h : ∀ a, Region.Contains ⟨p, 32⟩ a 1 → m₁ a = m₂ a) : wordsAt m₁ p 4 = wordsAt m₂ p 4 := by
  simp only [wordsAt]
  exact List.map_congr_left fun i hi => readW_congr (by have := List.mem_range.mp hi; omega_arith) h

theorem setWidth_ptr (x : BitVec 64) : (BitVec.setWidth abi.ptrBits x).toNat = x.toNat :=
  congrArg BitVec.toNat (BitVec.setWidth_eq x)

theorem stackArgs_two (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

/-! ## Code that changes only `rax` and the flags -/

/-- `u` is `s` but for `rax`, `r10`, `r11` and the flags: every contract
built with `Sig.contract` under `abi` holds of one as of the other. -/
structure Agree (u s : State) : Prop where
  gpr : ∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → u.gpr r = s.gpr r
  mem : u.mem = s.mem
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  mxcsr : u.mxcsr = s.mxcsr
  syms : u.syms = s.syms

theorem argRegs_ne : ∀ r ∈ argRegs, r ≠ .rax ∧ r ≠ .r10 ∧ r ≠ .r11 := by decide

theorem Agree.rsp {u s : State} (h : Agree u s) : u.gpr .rsp = s.gpr .rsp :=
  h.gpr _ (by decide) (by decide) (by decide)

theorem Agree.stackArg {u s : State} (h : Agree u s) (i : Nat) : stackArg u i = stackArg s i := by
  simp only [VG.X86_64.stackArg, stackArgAddr, h.rsp, h.mem]

theorem Agree.args {u s : State} (h : Agree u s) {ws : List Nat} {f : State → List (BitVec 64)}
    (e : abi.args ws = some f) : f u = f s := by
  simp only [abi] at e
  split at e
  · cases e
    exact List.map_congr_left fun r hr =>
      have hn := argRegs_ne r (List.mem_of_mem_take hr); h.gpr r hn.1 hn.2.1 hn.2.2
  · cases e
    dsimp only
    rw [List.map_congr_left fun r hr => have hn := argRegs_ne r hr; h.gpr r hn.1 hn.2.1 hn.2.2,
      List.map_congr_left fun i _ => h.stackArg i]

theorem Agree.pre {u s : State} (h : Agree u s) {sig : Sig}
    {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
    {st : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} :
    (sig.contract abi pre post wa st leak).pre u ↔ (sig.contract abi pre post wa st leak).pre s := by
  simp only [Sig.contract]
  split
  · exact Iff.rfl
  · rename_i vals e
    rw [h.args e]
    simp only [abi, stackArgAddr, h.rsp, h.mem, h.rd, h.wr]

theorem Agree.post {u s s' : State} (h : Agree u s) {sig : Sig}
    {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
    {st : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} :
    (sig.contract abi pre post wa st leak).post u s' ↔ (sig.contract abi pre post wa st leak).post s s' := by
  simp only [Sig.contract]
  split
  · exact Iff.rfl
  · rename_i vals e
    rw [h.args e]
    simp only [abi, h.mem]

theorem Agree.pub {u u' s s' : State} (h : Agree u s) (h' : Agree u' s') {sig : Sig}
    {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
    {st : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} :
    (sig.contract abi pre post wa st leak).pub u u' ↔ (sig.contract abi pre post wa st leak).pub s s' := by
  simp only [Sig.contract]
  split
  · exact Iff.rfl
  · rename_i vals e
    rw [h.args e, h'.args e]
    simp only [abi, h.mem, h'.mem, h.rsp, h'.rsp, h.mxcsr, h'.mxcsr]

theorem Agree.abiPreserved {u s s' : State} (h : Agree u s) (a : target.abiPreserved u s') :
    target.abiPreserved s s' := by
  obtain ⟨a₁, a₂, a₃⟩ := a
  refine ⟨fun r hr => ?_, ?_, ?_⟩
  · rw [a₁ r hr, h.gpr r (by revert r; decide) (by revert r; decide) (by revert r; decide)]
  · rw [← h.rsp, a₂, h.mem]
  · rw [a₃, h.mxcsr]

theorem agree_flags (s : State) (c o z n : Option Bool) : Agree (s.setFlags c o z n) s :=
  ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The calling convention with the callees' addresses public -/

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {st : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}
  {x : String} {xs : List String}

/-- `Abi.withFns` makes only the functions' addresses public too. -/
theorem pub_withFns {s₁ s₂ : State} :
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

theorem Agree.preF {u s : State} (h : Agree u s) :
    (sig.contract (abi.withFns (x :: xs)) pre post wa st leak).pre u ↔
      (sig.contract (abi.withFns (x :: xs)) pre post wa st leak).pre s :=
  h.pre (pre := pre) (post := post) (wa := wa) (st := st) (leak := leak)

theorem Agree.postF {u s s' : State} (h : Agree u s) :
    (sig.contract (abi.withFns (x :: xs)) pre post wa st leak).post u s' ↔
      (sig.contract (abi.withFns (x :: xs)) pre post wa st leak).post s s' :=
  h.post (pre := pre) (post := post) (wa := wa) (st := st) (leak := leak)

theorem Agree.pubF {u u' s s' : State} (h : Agree u s) (h' : Agree u' s') :
    (sig.contract (abi.withFns (x :: xs)) pre post wa st leak).pub u u' ↔
      (sig.contract (abi.withFns (x :: xs)) pre post wa st leak).pub s s' := by
  rw [pub_withFns, pub_withFns, h.pub h', h.syms, h'.syms]

end

/-! ## Forwarding to a width's function with its callees' addresses

`ParameterSearch.width` is `forward`'s frame with three `lea`s after the
copies: the function runs with the addresses of the functions `u`, `f` and
`p` in `rax`, `r10` and `r11`, which no argument is in and the calling
convention does not preserve. -/

section
open VG.Impl.StackScratch.X86_64 VG.Impl.ForwardCall.X86_64

/-- `t` with the addresses of `u`, `f` and `p` in `rax`, `r10` and `r11`. -/
def fnState (u f p : String) (t : State) : State :=
  ((t.setReg .rax (t.syms u)).setReg .r10 (t.syms f)).setReg .r11 (t.syms p)

theorem fnAddrs_run (u f p : String) (t : State) :
    execBlock isa (Impl.Dsa.X86_64.ParameterSearch.fnAddrs u f p) t = some (fnState u f p t, []) := rfl

theorem fnState_gpr (u f p : String) (t : State) {r : Reg} (h₁ : r ≠ .rax) (h₂ : r ≠ .r10)
    (h₃ : r ≠ .r11) : (fnState u f p t).gpr r = t.gpr r := by
  rw [fnState, RegUpd.gpr_setReg_of_ne _ _ h₃, RegUpd.gpr_setReg_of_ne _ _ h₂, RegUpd.gpr_setReg_of_ne _ _ h₁]

theorem copiedD_syms (bytes : Nat) (u : State) : ∀ m, (copiedD bytes u m).syms = u.syms
  | 0 => rfl
  | m + 1 => copiedD_syms bytes u m

/-- The forwarding frame, the copies, then the code `fns`, then the call. -/
def forwardFns (bytes m : Nat) (fns : List Instr) (name : String) (body : Prog isa) : Prog isa :=
  .frame (.alloc bytes) (.seq (.block (copies bytes m ++ fns)) (.call name body)) (.free bytes)

/-- The state the callee runs from: `narrowF`'s, with the addresses. -/
def narrowFF (sig : Sig) (bytes : Nat) (u f p : String) (s : State) : State :=
  (fnState u f p (fwdState sig bytes s)).callEntry.withRegions
    (((fwdRegions sig bytes s).filter (!·.2)).map (·.1))
    (((fwdRegions sig bytes s).filter (·.2)).map (·.1))

theorem narrowFF_agree (sig : Sig) (bytes : Nat) (u f p : String) (s : State) :
    Agree (narrowFF sig bytes u f p s) (narrowF sig bytes s) := by
  have hsp : (fnState u f p (fwdState sig bytes s)).gpr .rsp = (fwdState sig bytes s).gpr .rsp :=
    fnState_gpr u f p _ (by decide) (by decide) (by decide)
  refine ⟨fun r h₁ h₂ h₃ => ?_, ?_, rfl, rfl, rfl, rfl⟩
  · by_cases hr : r = .rsp
    · subst hr
      rw [narrowFF, narrowF, State.withRegions_gpr, State.withRegions_gpr, State.callEntry_rsp,
        State.callEntry_rsp, hsp]
    · rw [narrowFF, narrowF, State.withRegions_gpr, State.withRegions_gpr, State.callEntry_gpr _ hr,
        State.callEntry_gpr _ hr, fnState_gpr u f p _ h₁ h₂ h₃]
  · rw [narrowFF, narrowF, State.withRegions_mem, State.withRegions_mem, State.callEntry_mem,
      State.callEntry_mem, hsp]
    rfl

theorem narrowFF_syms (sig : Sig) (bytes : Nat) (u f p : String) (s : State) :
    (narrowFF sig bytes u f p s).syms = s.syms :=
  copiedD_syms bytes (allocState bytes s) (nStack sig)

/-- The addresses are in their registers. -/
theorem narrowFF_fns (sig : Sig) (bytes : Nat) (u f p : String) (s : State) :
    (narrowFF sig bytes u f p s).gpr .rax = (narrowFF sig bytes u f p s).syms u ∧
      (narrowFF sig bytes u f p s).gpr .r10 = (narrowFF sig bytes u f p s).syms f ∧
      (narrowFF sig bytes u f p s).gpr .r11 = (narrowFF sig bytes u f p s).syms p := by
  simp only [narrowFF, State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.rax ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r10 ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r11 ≠ .rsp),
    fnState, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ (by decide : ¬ Reg.rax = .r11),
    RegUpd.gpr_setReg_of_ne _ _ (by decide : ¬ Reg.rax = .r10),
    RegUpd.gpr_setReg_of_ne _ _ (by decide : ¬ Reg.r10 = .r11)]
  exact ⟨rfl, rfl, rfl⟩

variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack bytes : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

theorem forwardFns_run {name u f p : String} {body : Prog isa} (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hm : 0 < nStack sig) (hb : 8 * nStack sig ≤ bytes ∧ bytes < 4096 ∧ bytes % 8 = 0)
    (hst : stack + bytes + 16 ≤ 2 ^ 64) (hsafe : SpSafe body) (hd : body.x86_64Depth ≤ stack) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s) {t : List Leak} {s₃ : State}
    (he : Exec isa body (narrowFF sig bytes u f p s) t s₃)
    (ha : abiPreserved (narrowFF sig bytes u f p s) s₃) :
    Exec isa (forwardFns bytes (nStack sig) (Impl.Dsa.X86_64.ParameterSearch.fnAddrs u f p) name body) s
        (fwdTrace bytes (nStack sig) (s.gpr .rsp) t) (fwdFinal bytes s s₃) ∧
      abiPreserved s (fwdFinal bytes s s₃) ∧
      (fwdFinal bytes s s₃).mem = lose s₃.mem (s.gpr .rsp - BitVec.ofNat 64 bytes) bytes s₃.unknowns ∧
      (fwdFinal bytes s s₃).gpr .rax = s₃.gpr .rax := by
  obtain ⟨hb, hb1, hb2⟩ := hb
  obtain ⟨hrun, hrd', hwr', -, -, hgw, hfw, -⟩ := fwdState_run hs hk hb hb1
  obtain ⟨hrsp0, hg0, hmx0, -, hf⟩ := narrowF_facts hk hb hb1 hs
  have ag := narrowFF_agree sig bytes u f p s
  have hrsp : (narrowFF sig bytes u f p s).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes - 8 :=
    ag.rsp.trans hrsp0
  have hg : ∀ q, q ≠ .rax → q ≠ .r10 → q ≠ .r11 → q ≠ .rsp → (narrowFF sig bytes u f p s).gpr q = s.gpr q :=
    fun q h₁ h₂ h₃ h₄ => (ag.gpr q h₁ h₂ h₃).trans (hg0 q h₁ h₄)
  have hmx : (narrowFF sig bytes u f p s).mxcsr = s.mxcsr := ag.mxcsr.trans hmx0
  rw [pre_args hk] at hs
  obtain ⟨⟨hwf, -⟩, hrd, hwr, -, hres, -, -⟩ := hs
  have hsb : stack + bytes + 8 ≤ (s.gpr .rsp).toNat := by rcases hwf with h | h <;> omega_using [h]
  have hF : s.gpr .rsp - BitVec.ofNat 64 bytes - 8 = s.gpr .rsp - BitVec.ofNat 64 (bytes + 8) := by
    rw [BitVec.ofNat_add, BitVec.sub_sub]; rfl
  let w := fwdState sig bytes s
  let w' := fnState u f p w
  have hwrsp : w.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes :=
    (hgw .rsp (by decide)).trans (allocState_rsp' _ _)
  have hw'rsp : w'.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes :=
    (fnState_gpr u f p w (by decide) (by decide) (by decide)).trans hwrsp
  have hrun' : execBlock isa (copies bytes (nStack sig) ++ Impl.Dsa.X86_64.ParameterSearch.fnAddrs u f p)
      (allocState bytes s) =
      some (w', copyDTrace bytes ((allocState bytes s).gpr .rsp) (nStack sig) ++ []) := by
    rw [execBlock_append, hrun]
    rfl
  -- The frame's push.
  have hpush : isa.push (.alloc bytes) s = some (allocState bytes s) := by
    simp only [isa, push, allocState]
    exact ite_eq_left ⟨by omega_using [hb, hm], hb1, hb2, by omega_using [hsb]⟩
  -- The callee's regions are within the caller's and the frame.
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
  have hcovW : Covers (((fwdRegions sig bytes s).filter (·.2)).map (·.1)) w.wr := by
    rw [hwr']
    refine Covers.of_forall fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    simp only [fwdRegions, bufRegions, List.mem_append, List.mem_singleton] at ha
    rcases ha with (ha | ha) | rfl
    · exact Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact List.mem_cons_of_mem _ (hbufW a ha hf')
    · obtain ⟨r, -, rfl⟩ := List.mem_map.mp ha; simp at hf'
    · simp at hf'
  have hcovR : Covers (((fwdRegions sig bytes s).filter (!·.2)).map (·.1)) (w.rd ++ w.wr) := by
    rw [hrd', hwr']
    refine Covers.of_forall fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    simp only [fwdRegions, bufRegions, List.mem_append, List.mem_singleton] at ha
    rcases ha with (ha | ha) | rfl
    · exact Covers.left (Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact hbufR a ha (by simpa using hf'))
    · exact Covers.left (Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact hlistR a ha)
    · exact Covers.right (Covers.one ⟨_, List.mem_cons_self .., Offset.contains_below _ (a := bytes)
        (b := bytes) (Nat.le_refl _) (by omega_using [hb]) (by omega_using [hb1])⟩)
  have hw := Exec.widen he (rd := w.rd) (wr := w.wr) (Covers.append_left hcovR (Covers.right hcovW)) hcovW
  rw [show (narrowFF sig bytes u f p s).withRegions w.rd w.wr = w'.callEntry from rfl,
    show w.rd = s.rd from hrd', show w.wr = (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) from hwr'] at hw
  -- The return.
  have hrsp₃ : s₃.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes - 8 :=
    (ha.1 .rsp (by simp [calleeSaved])).trans hrsp
  have hret : isa.ret w'.callEntry (s₃.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)) =
      some ((s₃.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)).setReg .rsp (s₃.gpr .rsp + 8)) := by
    simp only [isa, ret, State.withRegions_gpr, State.withRegions_mem]
    refine ite_eq_left ⟨by rw [hrsp₃, State.callEntry_rsp, hw'rsp], ?_⟩
    have := ha.2.1
    rw [hrsp₃]
    simp only [narrowFF, State.withRegions_gpr, State.withRegions_mem, State.callEntry_rsp] at this
    rw [State.callEntry_rsp, hw'rsp]
    rw [hw'rsp] at this
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
    rw [ite_eq_left ⟨by omega_using [hb, hm], hb1, hb2, h4, h5, h6⟩]
    simp only [fwdFinal, State.setReg, State.withRegions, ite_true]
    rfl
  have hex : Exec isa (forwardFns bytes (nStack sig) (Impl.Dsa.X86_64.ParameterSearch.fnAddrs u f p) name body)
      s _ _ :=
    Exec.frame hpush (Exec.seq (Exec.block hrun') (Exec.call (name := name) (call_callEntry w') hw hret)) hpop
  simp only [isa, addrs, List.map_nil, List.nil_append, List.append_nil, allocState_rsp',
    List.map_cons, State.withRegions_gpr, hrsp₃, hw'rsp] at hex
  have h8 : s₃.gpr .rsp + 8 = s.gpr .rsp - BitVec.ofNat 64 bytes := by
    rw [hrsp₃, BitVec.sub_add_cancel]
  refine ⟨hex, ⟨fun q hq => ?_, ?_, ?_⟩, by show lose _ (s₃.gpr .rsp + 8) _ _ = _; rw [h8], ?_⟩
  · -- The callee-saved registers.
    simp only [fwdFinal, State.setReg, State.withRegions_gpr]
    by_cases hqs : q = .rsp
    · subst hqs; simp only [ite_true, hrsp₃]
      rw [BitVec.sub_add_cancel, BitVec.sub_add_cancel]
    · simp only [hqs, ite_false]
      have hqa : q ≠ .rax := fun h => by subst h; simp [calleeSaved] at hq
      have hq10 : q ≠ .r10 := fun h => by subst h; simp [calleeSaved] at hq
      have hq11 : q ≠ .r11 := fun h => by subst h; simp [calleeSaved] at hq
      rw [ha.1 q hq, hg q hqa hq10 hq11 hqs]
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
    rw [hfs.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) ?_ (by decide), ag.mem]
    · exact hf.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hF]
        exact hR (by omega_using []) (by omega_using [hb])) (by decide)
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
        obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
        simp only [fwdRegions, List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | rfl
        · exact hres _ (List.mem_cons_self ..) a (List.mem_append_left _ ha)
        · simp at hf'
      · simp only [List.mem_singleton] at hr; subst hr
        rw [hrsp, hF]
        show (⟨s.gpr .rsp, 8⟩ : Region).Disjoint
          ⟨s.gpr .rsp - BitVec.ofNat 64 (bytes + 8) - BitVec.ofNat 64 body.x86_64Depth, body.x86_64Depth⟩
        rw [BitVec.sub_sub, ← BitVec.ofNat_add]
        exact hR (by omega_using [hd]) (by omega_using [hd])
  · -- MXCSR.
    show s₃.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
    rw [ha.2.2, hmx]
  · simp [fwdFinal, State.setReg]

/-- `Verified.forward` for `forwardFns` with the three `lea`s: the callee's
contract `K` is the forwarded one with the addresses in `rax`, `r10` and
`r11`, for runs that agree on them, and the caller's makes them public
(`Abi.withFns`). -/
theorem forwardFns_verified {name u f p x : String} {xs : List String} {body : Prog isa}
    {K C : Contract isa} (hc : C = sig.contract abi pre post wa stack leak)
    (h : Verified target body K)
    (hKpre : ∀ t, C.pre t → t.gpr .rax = t.syms u → t.gpr .r10 = t.syms f → t.gpr .r11 = t.syms p → K.pre t)
    (hKpost : ∀ t t', K.post t t' → C.post t t')
    (hKpub : ∀ t₁ t₂, C.pub t₁ t₂ → t₁.syms u = t₂.syms u → t₁.syms f = t₂.syms f → t₁.syms p = t₂.syms p →
      K.pub t₁ t₂)
    (hfns : u ∈ x :: xs ∧ f ∈ x :: xs ∧ p ∈ x :: xs)
    (hk : 6 ≤ (sig.words abi.ptrBits).length) (hm : 0 < nStack sig)
    (hb : 8 * nStack sig ≤ bytes ∧ bytes < 4096 ∧ bytes % 8 = 0)
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
    Verified target (forwardFns bytes (nStack sig) (Impl.Dsa.X86_64.ParameterSearch.fnAddrs u f p) name body)
      (sig.contract (abi.withFns (x :: xs)) pre post wa (stack + bytes + 8) leak) := by
  subst hc
  obtain ⟨hcor, hct, -⟩ := h
  have hsafe := SpSafe.of_all hsp
  have hb0 := hb.1
  have hb1 := hb.2.1
  have kpre : ∀ s, (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s →
      K.pre (narrowFF sig bytes u f p s) := fun s hs =>
    have hn := narrowFF_fns sig bytes u f p s
    hKpre _ ((narrowFF_agree sig bytes u f p s).pre.mpr (narrowF_pre hk hm hb0 hb1 hpre hs)) hn.1 hn.2.1 hn.2.2
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s → ∃ t s₃,
      Exec isa body (narrowFF sig bytes u f p s) t s₃ ∧
      (sig.contract abi pre post wa stack leak).post (narrowF sig bytes s) s₃ ∧
      Exec isa (forwardFns bytes (nStack sig) (Impl.Dsa.X86_64.ParameterSearch.fnAddrs u f p) name body) s
        (fwdTrace bytes (nStack sig) (s.gpr .rsp) t) (fwdFinal bytes s s₃) ∧
      abiPreserved s (fwdFinal bytes s s₃) ∧
      Frame [⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩] s₃.mem (fwdFinal bytes s s₃).mem ∧
      (fwdFinal bytes s s₃).gpr .rax = s₃.gpr .rax := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (kpre s hs)
    obtain ⟨hex, ha', hm', hr⟩ := forwardFns_run hk hm hb hst hsafe hd hs he ha
    exact ⟨t, s₃, he, (narrowFF_agree sig bytes u f p s).post.mp (hKpost _ _ hq), hex, ha',
      by rw [hm']; exact lose_frame _ _ _ _, hr⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · have hs : (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s := hs
    obtain ⟨t, s₃, -, hq, hex, ha, hmem, hrax⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    show (sig.contract abi pre post wa (stack + bytes + 8) leak).post s _
    rw [post_args hk]
    rw [post_args hk] at hq
    obtain ⟨-, -, -, hargs, -⟩ := narrowF_facts hk hb0 hb1 hs
    rw [hargs] at hq
    rw [hrax]
    have h₄ := hpost _ _ _ _ _ (allArgs_length sig s hk) (narrowF_agree hk hb0 hb1 hs)
      (fun r hr x hx => narrowF_agreeLists hk hb0 hb1 hs r ((narrowF_lists hk hb0 hb1 hs) ▸ hr) x hx) hq
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
  · have h₁ : (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s₁ := h₁
    have h₂ : (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s₂ := h₂
    obtain ⟨hp', hy⟩ := pub_withFns.mp hp
    obtain ⟨u₁, r₁, f₁, -, x₁, -⟩ := hrun s₁ h₁
    obtain ⟨u₂, r₂, f₂, -, x₂, -⟩ := hrun s₂ h₂
    have hpn : K.pub (narrowFF sig bytes u f p s₁) (narrowFF sig bytes u f p s₂) := by
      refine hKpub _ _ (((narrowFF_agree sig bytes u f p s₁).pub (narrowFF_agree sig bytes u f p s₂)).mpr
        (narrowF_pub hk hb0 hb1 h₁ h₂ hp' hleak)) ?_ ?_ ?_
      all_goals rw [narrowFF_syms, narrowFF_syms]
      · exact hy u hfns.1
      · exact hy f hfns.2.1
      · exact hy p hfns.2.2
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1, ((pubL_args hk).mp hp').1.1.1,
      hct _ _ _ _ _ _ (kpre _ h₁) (kpre _ h₂) hpn f₁ f₂]

/-- `forwardFns` writes `rsp` only in its frame and its call if its callee
does only in its frames. -/
theorem forwardFns_spSafe {bytes m : Nat} {u f p name : String} {body : Prog isa}
    (h : body.all (fun i => !isa.writesSp i) = true) :
    (forwardFns bytes m (Impl.Dsa.X86_64.ParameterSearch.fnAddrs u f p) name body).all
      (fun i => !isa.writesSp i) = true := by
  have hc : (copies bytes m).all (fun i => !isa.writesSp i) = true :=
    List.all_eq_true.mpr fun i hi => by
      obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hi
      simp only [copyDown, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl <;> rfl
  simp only [forwardFns, Code.all, List.all_append, hc, h, Bool.and_true, Bool.true_and]
  rfl

end

/-! ## Forwarding to a width's function -/

/-- `K` is `Refill.contract p abi S` with the addresses of `u`, `f` and `q`
in `rax`, `r10` and `r11`, for runs that agree on them (`Refill.contractF`). -/
structure FnContract (u f q : String) (p S : Nat) (K : Contract isa) : Prop where
  pre : ∀ t, (Refill.contract p abi S).pre t → t.gpr .rax = t.syms u → t.gpr .r10 = t.syms f →
    t.gpr .r11 = t.syms q → K.pre t
  post : ∀ t t', K.post t t' → (Refill.contract p abi S).post t t'
  pub : ∀ t₁ t₂, (Refill.contract p abi S).pub t₁ t₂ → t₁.syms u = t₂.syms u → t₁.syms f = t₂.syms f →
    t₁.syms q = t₂.syms q → K.pub t₁ t₂

theorem forward_refill (p S : Nat) (hS : S + 72 ≤ 2 ^ 64) {name u f q x : String} {xs : List String}
    {body : Prog isa} {K : Contract isa} (h : Verified target body K) (hK : FnContract u f q p S K)
    (hfns : u ∈ x :: xs ∧ f ∈ x :: xs ∧ q ∈ x :: xs)
    (hsp : body.all (fun i => !isa.writesSp i) = true) (hd : body.x86_64Depth ≤ S)
    (hsat : ∃ s, (Refill.contract p abi (S + 64)).pre s) :
    Verified target (Impl.Dsa.X86_64.ParameterSearch.width (Impl.Dsa.X86_64.ParameterSearch.fnAddrs u f q)
      name body) (Refill.contract p (abi.withFns (x :: xs)) (S + 64)) := by
  refine forwardFns_verified (sig := Spec.Dsa.parameterSearchSig) (bytes := 56) (C := Refill.contract p abi S) rfl
    h hK.pre hK.post hK.pub hfns
    (by decide) (by decide) (by decide) (by omega_arith) hsp hd ?_ ?_ ?_ hsat ?_
  · intro vs m₁ m₂ hl hb _ hpr
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 7) hl
    replace hl := Nat.succ.inj hl
    iterate 6
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
      replace hl := Nat.succ.inj hl
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    replace hl := Nat.succ.inj hl
    obtain rfl := List.eq_nil_of_length_eq_zero hl
    simp only [Spec.Dsa.parameterSearchSig, Sig.bufs_nil, Sig.bufs_slice, Sig.bufs_array,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size,
      Nat.mul_one, Nat.reduceMul] at hb
    obtain ⟨-, -, -, -, b5⟩ := hb
    change Curry.apply (α := Mem → Prop) [ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.addr,
      ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr] _ _ m₁ at hpr
    change Curry.apply (α := Mem → Prop) [ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.addr,
      ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr] _ _ m₂
    dsimp only [Curry.apply, ArgWord.ofRaw] at hpr ⊢
    rwa [← readW_congr0 b5, ← readW_congr8 b5, ← readW_congr16 b5]
  · intro vs m₁ m₂ m' r hl hb _ hq
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 7) hl
    replace hl := Nat.succ.inj hl
    iterate 2
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
      replace hl := Nat.succ.inj hl
    obtain ⟨rand, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    replace hl := Nat.succ.inj hl
    obtain ⟨randLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    replace hl := Nat.succ.inj hl
    iterate 2
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
      replace hl := Nat.succ.inj hl
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    replace hl := Nat.succ.inj hl
    obtain rfl := List.eq_nil_of_length_eq_zero hl
    simp only [Spec.Dsa.parameterSearchSig, Sig.bufs_nil, Sig.bufs_slice, Sig.bufs_array,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size,
      Nat.mul_one, Nat.reduceMul] at hb
    obtain ⟨-, -, b3, -, b5⟩ := hb
    rw [← setWidth_ptr randLen] at b3
    change Curry.apply (α := Mem → Mem → BitVec (Spec.Dsa.parameterSearchSig.retBits abi.ptrBits) → Prop)
      [ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.addr,
      ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr] _ _ m₁ m' r at hq
    change Curry.apply (α := Mem → Mem → BitVec (Spec.Dsa.parameterSearchSig.retBits abi.ptrBits) → Prop)
      [ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.addr,
      ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr] _ _ m₂ m' r
    dsimp only [Curry.apply, ArgWord.ofRaw] at hq ⊢
    rw [← readW_congr0 b5, ← readW_congr8 b5]
    erw [← bytesAt_congr b3]
    exact hq
  · -- The memory on return: `out`, `used` and `state`.
    intro vs m m₁ m₂ r hl _ hb _ hq
    obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 7) hl
    replace hl := Nat.succ.inj hl
    obtain ⟨outLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    replace hl := Nat.succ.inj hl
    obtain ⟨used, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    replace hl := Nat.succ.inj hl
    iterate 4
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
      replace hl := Nat.succ.inj hl
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    replace hl := Nat.succ.inj hl
    obtain rfl := List.eq_nil_of_length_eq_zero hl
    simp only [Spec.Dsa.parameterSearchSig, Sig.bufs_nil, Sig.bufs_slice, Sig.bufs_array,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size,
      Nat.mul_one, Nat.reduceMul] at hb
    obtain ⟨b1, b2, -, -, b5⟩ := hb
    rw [← setWidth_ptr outLen] at b1
    change Curry.apply (α := Mem → Mem → BitVec (Spec.Dsa.parameterSearchSig.retBits abi.ptrBits) → Prop)
      [ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.addr,
      ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr] _ _ m m₁ r at hq
    change Curry.apply (α := Mem → Mem → BitVec (Spec.Dsa.parameterSearchSig.retBits abi.ptrBits) → Prop)
      [ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.addr,
      ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr] _ _ m m₂ r
    dsimp only [Curry.apply, ArgWord.ofRaw] at hq ⊢
    obtain ⟨h1, h2, h3, req, h4, h5⟩ := hq
    refine ⟨h1, (bytesAt_congr b1).symm.trans h2, ?_, req, (wordsAt_congr b5).symm.trans h4, h5⟩
    rw [← h3]
    simp only [wordsAt]
    refine List.map_congr_left fun i hi => ?_
    have := List.mem_range.mp hi
    exact (Mem.readW_congr fun j hj => b2 _ (by
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith))).symm
  · intro vs m₁ m₂ hl hb _
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 7) hl
    replace hl := Nat.succ.inj hl
    iterate 2
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
      replace hl := Nat.succ.inj hl
    obtain ⟨rand, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    replace hl := Nat.succ.inj hl
    obtain ⟨randLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    replace hl := Nat.succ.inj hl
    iterate 2
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
      replace hl := Nat.succ.inj hl
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    replace hl := Nat.succ.inj hl
    obtain rfl := List.eq_nil_of_length_eq_zero hl
    simp only [Spec.Dsa.parameterSearchSig, Sig.bufs_nil, Sig.bufs_slice, Sig.bufs_array,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size,
      Nat.mul_one, Nat.reduceMul] at hb
    obtain ⟨-, -, b3, -, b5⟩ := hb
    rw [← setWidth_ptr randLen] at b3
    change Curry.apply (α := Mem → List Nat) [ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.addr,
      ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr] _ _ m₁ =
      Curry.apply (α := Mem → List Nat) [ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.addr,
      ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr] _ _ m₂
    dsimp only [Curry.apply, ArgWord.ofRaw]
    rw [wordsAt_congr b5]
    erw [bytesAt_congr b3]
    rfl


/-! ## The width -/

/-- `state[1]`, the modulus's width. -/
abbrev widthWord (s : State) : BitVec 64 := s.mem.readW (stackArg s 1 + 8) 64

theorem sub_beq_zero (a b : BitVec 64) : (a - b == 0) = (a == b) :=
  Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq]; bv_omega)

theorem widthOf_run (n : Nat) (hn : BitVec.signExtend 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n)
    (s : State) (h₁ : InRegions (s.rd ++ s.wr) (stackArgAddr s 1) 8)
    (h₂ : InRegions (s.rd ++ s.wr) (stackArg s 1 + 8) 8) :
    ∃ u, execBlock isa (Impl.Dsa.X86_64.ParameterSearch.widthOf n) s =
        some (u, [.addr (stackArgAddr s 1), .addr (stackArg s 1 + 8)]) ∧
      Agree u s ∧ u.gpr .rax = widthWord s ∧ isa.eval .e u = some (widthWord s == BitVec.ofNat 64 n) := by
  have ea₁ : s.ea { base := .rsp, disp := 16 } = stackArgAddr s 1 := rfl
  have e₁ : exec (.mov .rax (.mem { base := .rsp, disp := 16 })) s = some (s.setReg .rax (stackArg s 1)) := by
    simp only [exec, readSrc, State.load64, ea₁, h₁, ite_true, Option.map_some]; rfl
  have ea₂ : (s.setReg .rax (stackArg s 1)).ea { base := .rax, disp := 8 } = stackArg s 1 + 8 := rfl
  have e₂ : exec (.mov .rax (.mem { base := .rax, disp := 8 })) (s.setReg .rax (stackArg s 1)) =
      some ((s.setReg .rax (stackArg s 1)).setReg .rax (widthWord s)) := by
    have h₂' : InRegions ((s.setReg .rax (stackArg s 1)).rd ++ (s.setReg .rax (stackArg s 1)).wr)
        (stackArg s 1 + 8) 8 := h₂
    simp only [exec, readSrc, State.load64, ea₂, h₂', ite_true, Option.map_some]; rfl
  obtain ⟨u, e₃⟩ : ∃ u, exec (.alu .cmp .rax (.imm (BitVec.ofNat 32 n)))
      ((s.setReg .rax (stackArg s 1)).setReg .rax (widthWord s)) = some u := ⟨_, rfl⟩
  have hu : u = ((s.setReg .rax (stackArg s 1)).setReg .rax (widthWord s)).setFlags _ _
      (some ((widthWord s - BitVec.signExtend 64 (BitVec.ofNat 32 n)) == 0)) _ :=
    (Option.some.inj e₃).symm
  refine ⟨u, ?_, ⟨fun r hr _ _ => ?_, by rw [hu]; rfl, by rw [hu]; rfl, by rw [hu]; rfl, by rw [hu]; rfl,
    by rw [hu]; rfl⟩, by rw [hu]; rfl, ?_⟩
  · simp only [Impl.Dsa.X86_64.ParameterSearch.widthOf, execBlock, isa, e₁, e₂, e₃]
    rfl
  · rw [hu]
    show (if r = .rax then _ else if r = .rax then _ else s.gpr r) = s.gpr r
    simp only [hr, ite_false]
  · rw [hu]
    show some ((widthWord s - BitVec.signExtend 64 (BitVec.ofNat 32 n)) == 0) = _
    rw [hn, sub_beq_zero]

theorem cmp_run (v : BitVec 32) (s : State) :
    ∃ u, execBlock isa [.alu .cmp .rax (.imm v)] s = some (u, []) ∧ Agree u s ∧
      isa.eval .e u = some ((s.gpr .rax - BitVec.signExtend 64 v) == 0) :=
  ⟨_, rfl, agree_flags s _ _ _ _, rfl⟩

/-! ## The contracts the choice passes through -/

/-- The search's contract for the two larger widths, with the width in `rax`. -/
def largeContract (A : Abi isa) (S : Nat) : Contract isa where
  pre s := (Proof.Dsa.parameterSearchAskedContract A S).pre s ∧ s.gpr .rax = widthWord s ∧
    (widthWord s).toNat ≠ 128
  post := (Proof.Dsa.parameterSearchAskedContract A S).post
  pub := (Proof.Dsa.parameterSearchAskedContract A S).pub

theorem refill_of_search {p S : Nat} {s : State} (h : (Proof.Dsa.parameterSearchAskedContract abi S).pre s)
    (hw : (widthWord s).toNat = p) : (Refill.contract p abi S).pre s := by
  sig_pre [Proof.Dsa.parameterSearchAskedContract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackArgs_two] at h
  sig_pre [Proof.Dsa.parameterSearchAskedContract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackArgs_two] at h
  sig_split h
  sig_pre [Refill.contract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackArgs_two]
  sig_pre [Refill.contract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackArgs_two]
  sig_and_intros
  all_goals with_reducible assumption

theorem valid_of_search {S : Nat} {s : State} (h : (Proof.Dsa.parameterSearchAskedContract abi S).pre s) :
    Spec.Dsa.generationPLenValid (widthWord s).toNat = true := by
  sig_pre [Proof.Dsa.parameterSearchAskedContract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackArgs_two] at h
  sig_pre [Proof.Dsa.parameterSearchAskedContract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackArgs_two] at h
  sig_split h
  with_reducible assumption

theorem search_in {S : Nat} {s : State} (h : (Proof.Dsa.parameterSearchAskedContract abi S).pre s) :
    InRegions (s.rd ++ s.wr) (stackArgAddr s 1) 8 ∧ InRegions (s.rd ++ s.wr) (stackArg s 1 + 8) 8 := by
  sig_pre [Proof.Dsa.parameterSearchAskedContract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackArgs_two] at h
  sig_pre [Proof.Dsa.parameterSearchAskedContract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackArgs_two] at h
  sig_split h
  refine ⟨⟨⟨stackArgAddr s 0, 16⟩, ?_, ?_⟩, ⟨⟨stackArg s 1, 32⟩, ?_, ?_⟩⟩
  · rw [‹s.rd = _›]
    exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · have e : stackArgAddr s 1 = stackArgAddr s 0 + BitVec.ofNat 64 8 := by
      simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    rw [e]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  · rw [‹s.wr = _›]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))
  · exact Offset.contains_base (stackArg s 1) (d := 8) (n := 8) (k := 32) (by omega_arith) (by omega_arith)

theorem wordsAt_four (m : Mem) (p : Addr) : (wordsAt m p 4).map (·.toNat) =
    [(m.readW (p + BitVec.ofNat 64 0) 64).toNat, (m.readW (p + 8) 64).toNat, (m.readW (p + 16) 64).toNat,
      (m.readW (p + 24) 64).toNat] := rfl

theorem search_pub {S : Nat} {s s' : State} (h : (Proof.Dsa.parameterSearchAskedContract abi S).pub s s') :
    s.gpr .rsp = s'.gpr .rsp ∧ stackArg s 1 = stackArg s' 1 ∧ widthWord s = widthWord s' := by
  sig_pub [Proof.Dsa.parameterSearchAskedContract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackArgs_two] at h
  obtain ⟨hsp, hl, -, -, -, -, -, -, -, h₇⟩ := h
  have hst : stackArg s 1 = stackArg s' 1 := h₇
  refine ⟨hsp, hst, ?_⟩
  rw [wordsAt_four, wordsAt_four] at hl
  have hw := (List.append_inj hl (Eq.refl 4)).1
  simp only [List.cons.injEq] at hw
  exact BitVec.eq_of_toNat_eq hw.2.1

/-! ## The choice -/

/-! What `large_verified` and `widths_verified` use of the contracts, whose
conditions on a state the elaborator would otherwise evaluate wherever it
elaborates a proof of one. -/

section
variable {p S : Nat} {x : String} {xs : List String} {s s' u u' : State}

private theorem refill_pre (ag : Agree u s) (h : (Refill.contract p abi S).pre s) :
    (Refill.contract p (abi.withFns (x :: xs)) S).pre u := ag.preF.mpr h

private theorem asked_pre_abi (h : (Proof.Dsa.parameterSearchAskedContract (abi.withFns (x :: xs)) S).pre s) :
    (Proof.Dsa.parameterSearchAskedContract abi S).pre s := h

private theorem asked_pre (ag : Agree u s) (h : (Proof.Dsa.parameterSearchAskedContract (abi.withFns (x :: xs)) S).pre s) :
    (Proof.Dsa.parameterSearchAskedContract (abi.withFns (x :: xs)) S).pre u := ag.preF.mpr h

private theorem refill_post (ag : Agree u s) (h : (Refill.contract p (abi.withFns (x :: xs)) S).post u s') :
    (Proof.Dsa.parameterSearchAskedContract (abi.withFns (x :: xs)) S).post s s' := ag.postF.mp h

private theorem asked_post (ag : Agree u s)
    (h : (Proof.Dsa.parameterSearchAskedContract (abi.withFns (x :: xs)) S).post u s') :
    (Proof.Dsa.parameterSearchAskedContract (abi.withFns (x :: xs)) S).post s s' := ag.postF.mp h

private theorem asked_pub (ag : Agree u s) (ag' : Agree u' s')
    (h : (Proof.Dsa.parameterSearchAskedContract (abi.withFns (x :: xs)) S).pub s s') :
    (Proof.Dsa.parameterSearchAskedContract (abi.withFns (x :: xs)) S).pub u u' := (ag.pubF ag').mpr h

private theorem refill_pub (h : (Proof.Dsa.parameterSearchAskedContract (abi.withFns (x :: xs)) S).pub s s') :
    (Refill.contract p (abi.withFns (x :: xs)) S).pub s s' := h

private theorem asked_pub_abi (h : (Proof.Dsa.parameterSearchAskedContract (abi.withFns (x :: xs)) S).pub s s') :
    (Proof.Dsa.parameterSearchAskedContract abi S).pub s s' := (pub_withFns.mp h).1

end

section
-- The elaborator would evaluate the contracts' conditions on a state wherever it
-- elaborates a proof of one.
attribute [local irreducible] Proof.Dsa.parameterSearchAskedContract Refill.contract

theorem large_verified (S : Nat) {x : String} {xs : List String} {f₂₅₆ f₃₈₄ : List Instr}
    {n₂₅₆ n₃₈₄ : String} {c₂₅₆ c₃₈₄ : Prog isa}
    (h₂₅₆ : Verified target (Impl.Dsa.X86_64.ParameterSearch.width f₂₅₆ n₂₅₆ c₂₅₆)
      (Refill.contract 256 (abi.withFns (x :: xs)) S))
    (h₃₈₄ : Verified target (Impl.Dsa.X86_64.ParameterSearch.width f₃₈₄ n₃₈₄ c₃₈₄)
      (Refill.contract 384 (abi.withFns (x :: xs)) S))
    (hsat : ∃ s, (largeContract (abi.withFns (x :: xs)) S).pre s) :
    Verified target (.seq (.block [.alu .cmp .rax (.imm 256)])
      (Code.iteCold .e (Impl.Dsa.X86_64.ParameterSearch.width f₂₅₆ n₂₅₆ c₂₅₆)
        (Impl.Dsa.X86_64.ParameterSearch.width f₃₈₄ n₃₈₄ c₃₈₄))) (largeContract (abi.withFns (x :: xs)) S) := by
  refine Verified.entryBranch (p := fun s => s.gpr .rax == 256) (fun _ => []) h₂₅₆ h₃₈₄
    (fun s hs => ?_) ?_ hsat
  · obtain ⟨u, e, ag, ev⟩ := cmp_run 256 s
    obtain ⟨hk, hrax, h128⟩ := hs
    refine ⟨u, e, ?_, fun hp => ⟨refill_pre ag (refill_of_search (asked_pre_abi hk) ?_), fun s' a q => ⟨ag.abiPreserved a, refill_post ag q⟩⟩,
      fun hp => ⟨refill_pre ag (refill_of_search (asked_pre_abi hk) ?_), fun s' a q => ⟨ag.abiPreserved a, refill_post ag q⟩⟩⟩
    · rw [ev, show BitVec.signExtend 64 (256 : BitVec 32) = 256 from by decide, sub_beq_zero]
    · rw [← hrax, beq_iff_eq.mp hp]; rfl
    · have hv := valid_of_search (asked_pre_abi hk)
      simp only [Spec.Dsa.generationPLenValid, Bool.or_eq_true, beq_iff_eq] at hv
      have h256 : (widthWord s).toNat ≠ 256 := fun h => by
        rw [← hrax] at h
        have : s.gpr .rax = 256 := BitVec.eq_of_toNat_eq h
        simp [this] at hp
      omega_arith
  · intro s s' u u' hs hs' hq e e'
    obtain ⟨u₀, e₀, ag, -⟩ := cmp_run 256 s
    obtain ⟨u₀', e₀', ag', -⟩ := cmp_run 256 s'
    rw [e₀] at e; rw [e₀'] at e'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e')
    have pu : (Proof.Dsa.parameterSearchAskedContract (abi.withFns (x :: xs)) S).pub u₀ u₀' := asked_pub ag ag' hq
    obtain ⟨-, -, hw⟩ := search_pub (S := S)
      (asked_pub_abi (show (Proof.Dsa.parameterSearchAskedContract (abi.withFns (x :: xs)) S).pub s s' from hq))
    exact ⟨rfl, by simp only [hs.2.1, hs'.2.1, hw], fun _ => refill_pub pu, fun _ => refill_pub pu⟩

theorem widths_verified (S : Nat) {x : String} {xs : List String} {f₁₂₈ f₂₅₆ f₃₈₄ : List Instr}
    {n₁₂₈ n₂₅₆ n₃₈₄ : String} {c₁₂₈ c₂₅₆ c₃₈₄ : Prog isa}
    (h₁₂₈ : Verified target (Impl.Dsa.X86_64.ParameterSearch.width f₁₂₈ n₁₂₈ c₁₂₈)
      (Refill.contract 128 (abi.withFns (x :: xs)) S))
    (h₂₅₆ : Verified target (Impl.Dsa.X86_64.ParameterSearch.width f₂₅₆ n₂₅₆ c₂₅₆)
      (Refill.contract 256 (abi.withFns (x :: xs)) S))
    (h₃₈₄ : Verified target (Impl.Dsa.X86_64.ParameterSearch.width f₃₈₄ n₃₈₄ c₃₈₄)
      (Refill.contract 384 (abi.withFns (x :: xs)) S))
    (hsatL : ∃ s, (largeContract (abi.withFns (x :: xs)) S).pre s)
    (hsat : ∃ s, (Proof.Dsa.parameterSearchAskedContract (abi.withFns (x :: xs)) S).pre s) :
    Verified target (Impl.Dsa.X86_64.ParameterSearch.widths f₁₂₈ f₂₅₆ f₃₈₄ n₁₂₈ n₂₅₆ n₃₈₄ c₁₂₈ c₂₅₆ c₃₈₄)
      (Proof.Dsa.parameterSearchAskedContract (abi.withFns (x :: xs)) S) := by
  refine Verified.entryBranch (p := fun s => widthWord s == 128)
    (fun s => [.addr (stackArgAddr s 1), .addr (stackArg s 1 + 8)]) h₁₂₈
    (large_verified S h₂₅₆ h₃₈₄ hsatL) (fun s hs => ?_) ?_ hsat
  · obtain ⟨i₁, i₂⟩ := search_in (asked_pre_abi hs)
    obtain ⟨u, e, ag, hrax, ev⟩ := widthOf_run 128 (by decide) s i₁ i₂
    have hw : widthWord u = widthWord s := by simp only [widthWord, ag.mem, ag.stackArg]
    refine ⟨u, e, ev, fun hp => ⟨refill_pre ag (refill_of_search (asked_pre_abi hs) ?_), fun s' a q => ⟨ag.abiPreserved a, refill_post ag q⟩⟩,
      fun hp => ⟨⟨asked_pre ag hs, by rw [hrax, hw], ?_⟩, fun s' a q => ⟨ag.abiPreserved a, asked_post ag q⟩⟩⟩
    · rw [beq_iff_eq.mp hp]; rfl
    · rw [hw]
      intro h
      have : widthWord s = 128 := BitVec.eq_of_toNat_eq h
      simp [this] at hp
  · intro s s' u u' hs hs' hq e e'
    obtain ⟨i₁, i₂⟩ := search_in (asked_pre_abi hs)
    obtain ⟨i₁', i₂'⟩ := search_in (asked_pre_abi hs')
    obtain ⟨u₀, e₀, ag, -, -⟩ := widthOf_run 128 (by decide) s i₁ i₂
    obtain ⟨u₀', e₀', ag', -, -⟩ := widthOf_run 128 (by decide) s' i₁' i₂'
    rw [e₀] at e; rw [e₀'] at e'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e')
    have pu : (Proof.Dsa.parameterSearchAskedContract (abi.withFns (x :: xs)) S).pub u₀ u₀' := asked_pub ag ag' hq
    obtain ⟨hsp, hst, hw⟩ := search_pub (asked_pub_abi hq)
    exact ⟨by simp only [stackArgAddr, hsp, hst], by simp only [hw], fun _ => refill_pub pu, fun _ => pu⟩

end

/-! ## Satisfiable with the forwarding frame's stack -/

/-- The memory of `satState`: `scratch_len` and `state` on the stack, and
`state`'s words `[0, p, 32769 p, 0]`. -/
def satMem (p : Nat) : Mem :=
  Mem.writeW (Mem.writeW (Mem.writeW (Mem.writeW (fun _ => 0) (0x1000000000008 : Addr) (25600 : BitVec 64))
    (0x1000000000010 : Addr) (0x4000 : BitVec 64)) (0x4008 : Addr) (BitVec.ofNat 64 p))
    (0x4010 : Addr) (BitVec.ofNat 64 (Spec.Dsa.parameterEntropy p))

/-- A search for width `p`, with the width in `rax` too. -/
def satState (p : Nat) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => BitVec.ofNat 64 (2 * p + Spec.Dsa.generationQLen p) | .rdx => 0x2000
    | .rcx => 0x3000 | .r9 => 0x10000 | .rsp => 0x1000000000000 | .rax => BitVec.ofNat 64 p | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem p
  rd := [⟨0x3000, 0⟩, ⟨0x1000000000008, 16⟩]
  wr := [⟨0x1000, 2 * p + Spec.Dsa.generationQLen p⟩, ⟨0x2000, 8⟩, ⟨0x10000, 204800⟩, ⟨0x4000, 32⟩]

/-- The stack below `satState`'s return address is apart from every region
below `2 ^ 47` or above the return address. -/
theorem below_disjoint {S : Nat} (hS : S ≤ 2 ^ 40) {r : Region}
    (hr : decide (r.base.toNat + r.len ≤ 2 ^ 47 ∨
      (2 ^ 48 ≤ r.base.toNat ∧ r.base.toNat + r.len ≤ 2 ^ 64)) = true) :
    Region.Disjoint ⟨(0x1000000000000 : Addr) - BitVec.ofNat 64 (S + 63 + 1), S + 63 + 1⟩ r := by
  have hr := of_decide_eq_true hr
  have ht : ((0x1000000000000 : Addr) - BitVec.ofNat 64 (S + 63 + 1)).toNat = 2 ^ 48 - (S + 64) := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, show (0x1000000000000 : Addr).toNat = 2 ^ 48 from rfl]
    omega_arith
  refine Region.disjoint_of_le ?_ ?_ ?_
  · simp only [ht]
    omega_arith
  · simp only [ht]
    omega_arith
  · omega_arith

theorem search_sat {p S : Nat} (hp : p = 128 ∨ p = 256 ∨ p = 384) (hS : S ≤ 2 ^ 40) :
    (Proof.Dsa.parameterSearchAskedContract abi (S + 64)).pre (satState p) := by
  rcases hp with rfl | rfl | rfl
  all_goals sig_pre [Proof.Dsa.parameterSearchAskedContract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackArgs_two]
  all_goals sig_and_intros
  all_goals first
    | decide +kernel
    | exact Region.disjoint_of_sep (by decide +kernel)
    | exact below_disjoint hS (by decide +kernel)
    | exact Nat.le_trans (Nat.add_le_add_right hS 64) (by decide +kernel)

theorem refill_satState {p S : Nat} (hp : p = 128 ∨ p = 256 ∨ p = 384) (hS : S ≤ 2 ^ 40) :
    (Refill.contract p abi (S + 64)).pre (satState p) :=
  refill_of_search (search_sat hp hS) (by rcases hp with rfl | rfl | rfl <;> decide +kernel)

theorem refill_sat {p S : Nat} (hp : p = 128 ∨ p = 256 ∨ p = 384) (hS : S ≤ 2 ^ 40) :
    ∃ s, (Refill.contract p abi (S + 64)).pre s :=
  ⟨satState p, refill_satState hp hS⟩

/-- `satState p` with `rax`, `r10` and `r11` zero, where every function is. -/
def satFns (p : Nat) : State := (((satState p).setReg .rax 0).setReg .r10 0).setReg .r11 0

/-- A width's function with the addresses of `u`, `f` and `q` in `rax`,
`r10` and `r11` is satisfiable. -/
theorem refill_satFns {p S : Nat} (hp : p = 128 ∨ p = 256 ∨ p = 384) (hS : S ≤ 2 ^ 40) (u f q : String) :
    ∃ s, (Refill.contract p abi (S + 64)).pre s ∧ s.gpr .rax = s.syms u ∧ s.gpr .r10 = s.syms f ∧
      s.gpr .r11 = s.syms q := by
  have ag : Agree (satFns p) (satState p) :=
    ⟨fun r h₁ h₂ h₃ => by
      rw [satFns, RegUpd.gpr_setReg_of_ne _ _ h₃, RegUpd.gpr_setReg_of_ne _ _ h₂, RegUpd.gpr_setReg_of_ne _ _ h₁],
      rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨satFns p, ag.pre.mpr (refill_satState hp hS), rfl, rfl, rfl⟩

theorem large_sat {S : Nat} (hS : S ≤ 2 ^ 40) {x : String} {xs : List String} :
    ∃ s, (largeContract (abi.withFns (x :: xs)) (S + 64)).pre s :=
  ⟨satState 256, search_sat (.inr (.inl rfl)) hS, by decide +kernel, by decide +kernel⟩

theorem full_sat {S : Nat} (hS : S ≤ 2 ^ 40) {x : String} {xs : List String} :
    ∃ s, (Proof.Dsa.parameterSearchAskedContract (abi.withFns (x :: xs)) (S + 64)).pre s :=
  ⟨satState 128, search_sat (.inl rfl) hS⟩

/-! ## The search -/

/-- `vg_dsa_parameter_search` by the functions for each width, each verified
against the search's contract with its width fixed and `S` octets of stack,
with the addresses of the functions it calls in `rax`, `r10` and `r11`
(`FnContract`), which the search's contract makes public: the choice and the
forwarding frame (56 octets and the return address) need 64 more. -/
theorem refillWidths_verified (S : Nat) (hS : S ≤ 2 ^ 40) {x : String} {xs : List String}
    {u₁₂₈ f₁₂₈ q₁₂₈ u₂₅₆ f₂₅₆ q₂₅₆ u₃₈₄ f₃₈₄ q₃₈₄ n₁₂₈ n₂₅₆ n₃₈₄ : String}
    {c₁₂₈ c₂₅₆ c₃₈₄ : Prog isa} {K₁₂₈ K₂₅₆ K₃₈₄ : Contract isa}
    (h₁₂₈ : Verified target c₁₂₈ K₁₂₈) (h₂₅₆ : Verified target c₂₅₆ K₂₅₆) (h₃₈₄ : Verified target c₃₈₄ K₃₈₄)
    (k₁₂₈ : FnContract u₁₂₈ f₁₂₈ q₁₂₈ 128 S K₁₂₈) (k₂₅₆ : FnContract u₂₅₆ f₂₅₆ q₂₅₆ 256 S K₂₅₆)
    (k₃₈₄ : FnContract u₃₈₄ f₃₈₄ q₃₈₄ 384 S K₃₈₄)
    (i₁₂₈ : u₁₂₈ ∈ x :: xs ∧ f₁₂₈ ∈ x :: xs ∧ q₁₂₈ ∈ x :: xs)
    (i₂₅₆ : u₂₅₆ ∈ x :: xs ∧ f₂₅₆ ∈ x :: xs ∧ q₂₅₆ ∈ x :: xs)
    (i₃₈₄ : u₃₈₄ ∈ x :: xs ∧ f₃₈₄ ∈ x :: xs ∧ q₃₈₄ ∈ x :: xs)
    (s₁₂₈ : c₁₂₈.all (fun i => !isa.writesSp i) = true) (s₂₅₆ : c₂₅₆.all (fun i => !isa.writesSp i) = true)
    (s₃₈₄ : c₃₈₄.all (fun i => !isa.writesSp i) = true)
    (d₁₂₈ : c₁₂₈.x86_64Depth ≤ S) (d₂₅₆ : c₂₅₆.x86_64Depth ≤ S) (d₃₈₄ : c₃₈₄.x86_64Depth ≤ S) :
    Verified target (Impl.Dsa.X86_64.ParameterSearch.widths
      (Impl.Dsa.X86_64.ParameterSearch.fnAddrs u₁₂₈ f₁₂₈ q₁₂₈) (Impl.Dsa.X86_64.ParameterSearch.fnAddrs u₂₅₆ f₂₅₆ q₂₅₆)
      (Impl.Dsa.X86_64.ParameterSearch.fnAddrs u₃₈₄ f₃₈₄ q₃₈₄) n₁₂₈ n₂₅₆ n₃₈₄ c₁₂₈ c₂₅₆ c₃₈₄)
      (Proof.Dsa.parameterSearchAskedContract (abi.withFns (x :: xs)) (S + 64)) :=
  have hS' : S + 72 ≤ 2 ^ 64 := by omega_arith
  widths_verified (S + 64)
    (forward_refill 128 S hS' h₁₂₈ k₁₂₈ i₁₂₈ s₁₂₈ d₁₂₈ (refill_sat (.inl rfl) hS))
    (forward_refill 256 S hS' h₂₅₆ k₂₅₆ i₂₅₆ s₂₅₆ d₂₅₆ (refill_sat (.inr (.inl rfl)) hS))
    (forward_refill 384 S hS' h₃₈₄ k₃₈₄ i₃₈₄ s₃₈₄ d₃₈₄ (refill_sat (.inr (.inr rfl)) hS))
    (large_sat hS) (full_sat hS)

theorem width_spSafe {u f q name : String} {body : Prog isa} (h : body.all (fun i => !isa.writesSp i) = true) :
    (Impl.Dsa.X86_64.ParameterSearch.width (Impl.Dsa.X86_64.ParameterSearch.fnAddrs u f q) name body).all
      (fun i => !isa.writesSp i) = true :=
  forwardFns_spSafe (bytes := 56) (m := 2) h

/-- The choice writes `rsp` only in frames and calls, if its bodies do. -/
theorem refillWidths_spSafe {u₁₂₈ f₁₂₈ q₁₂₈ u₂₅₆ f₂₅₆ q₂₅₆ u₃₈₄ f₃₈₄ q₃₈₄ n₁₂₈ n₂₅₆ n₃₈₄ : String}
    {c₁₂₈ c₂₅₆ c₃₈₄ : Prog isa}
    (s₁₂₈ : c₁₂₈.all (fun i => !isa.writesSp i) = true) (s₂₅₆ : c₂₅₆.all (fun i => !isa.writesSp i) = true)
    (s₃₈₄ : c₃₈₄.all (fun i => !isa.writesSp i) = true) :
    (Impl.Dsa.X86_64.ParameterSearch.widths
      (Impl.Dsa.X86_64.ParameterSearch.fnAddrs u₁₂₈ f₁₂₈ q₁₂₈) (Impl.Dsa.X86_64.ParameterSearch.fnAddrs u₂₅₆ f₂₅₆ q₂₅₆)
      (Impl.Dsa.X86_64.ParameterSearch.fnAddrs u₃₈₄ f₃₈₄ q₃₈₄) n₁₂₈ n₂₅₆ n₃₈₄ c₁₂₈ c₂₅₆ c₃₈₄).all
      (fun i => !isa.writesSp i) = true := by
  simp only [Impl.Dsa.X86_64.ParameterSearch.widths, Code.iteCold, Code.all, width_spSafe s₁₂₈,
    width_spSafe s₂₅₆, width_spSafe s₃₈₄, Bool.and_true]
  rfl

end VG.Proof.Dsa.X86_64.Generation.RefillWidths
