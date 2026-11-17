module

public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Proof.Framework.X86_64.ForwardCall
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchWipe
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.Offset

/-!
# What code leaves in the frames it runs in (x86-64)

`StackLeaves` (`Scrub.lean`) asks what a function leaves on the stack below
its stack pointer, run by run. Code verified against a contract and run in a
frame, `withStackArgScratch` (`framed_leaves`) or `forward` (`forward_leaves`),
leaves there what it leaves from the state it is called in, `narrowS` or
`narrowF`, which these lemmas relate to the frame's entry state
(`narrowS_args`; `narrowF_facts`). In a frame of `withStackArgScratchWipedX`
(`framedW_leaves`), it leaves zeros where the frame wipes (`wipeAtX_zero`),
and elsewhere what it leaves from `narrowS`.
-/

@[expose] public section

namespace VG.X86_64

open VG.Impl.StackScratch.X86_64 VG.Impl.ForwardCall.X86_64

/-- What code leaves in its frame of `withStackArgScratch` (`L`, at the
state `narrowS` it runs from), from what it leaves run by run from the
states its contract's precondition implies `P` of. -/
theorem framed_leaves {sig : Sig} {nm : String} {e : Elem} {n bytes stack : Nat}
    {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {c : Prog isa} {P : State → Prop}
    {R : State → Region} {L : State → Addr → Option (BitVec 8)}
    (hv : Verified X86_64.target c (Sig.scratchContract abi sig nm e n pre post wa stack leak))
    (hP : ∀ s, (Sig.scratchContract abi sig nm e n pre post wa stack leak).pre s → P s)
    (hl : ∀ s t s', P s → Exec isa c s t s' → ∀ x, (R s).Contains x 1 → s'.mem x = (L s x).getD (s.mem x))
    (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + n * e.size ≤ bytes ∧ bytes < 4096 ∧ bytes % 8 = 0)
    (hst : stack + bytes + 8 ≤ 2 ^ 64) (hsp : c.all (fun i => !isa.writesSp i) = true)
    (hd : c.x86_64Depth ≤ stack)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) {t : List Leak} {u : State}
    (he : Exec isa (withStackArgScratch bytes (nStack sig) c) s t u) :
    ∀ x, (R (narrowS sig e n bytes s)).Contains x 1 →
      u.mem x = (L (narrowS sig e n bytes s) x).getD ((narrowS sig e n bytes s).mem x) := by
  have hn := narrowS_pre (nm := nm) hk hb.1 hb.2.1 (fun vs m₁ m₂ hl hb _ => hpre vs m₁ m₂ hl hb) hs
  obtain ⟨t₃, s₃, he₃, ha, -⟩ := hv.1 _ hn
  obtain ⟨hex, -, hm, -⟩ := withStackArgScratch_runMem hk hb hst (SpSafe.of_all hsp) hd hs he₃ ha
  obtain ⟨-, rfl⟩ := Exec.det he hex
  intro x hx
  rw [hm]
  exact hl _ _ _ (hP _ hn) he₃ x hx

/-- The stores of `wipeStoresAtX off n`, with `xmm0` zero, zero the `16n`
bytes at `rsp + off` and leave the rest of memory as it was. -/
theorem wipeStoresAtX_zero (R : Region) (u : State) (off : Nat) (hR : R ∈ u.wr) (hx : u.xmm .xmm0 = 0) :
    ∀ n, off + 16 * n < 2 ^ 64 →
    (∀ k < n, R.Contains (u.gpr .rsp + BitVec.ofNat 64 (off + 16 * k)) 16) →
    ∃ m', execBlock isa (wipeStoresAtX off n) u =
        some ({ u with mem := m' }, wipeAtXTrace (u.gpr .rsp) off n) ∧
      ∀ x, m' x = if off ≤ (x - u.gpr .rsp).toNat ∧ (x - u.gpr .rsp).toNat < off + 16 * n then 0 else u.mem x
  | 0, _, _ => ⟨u.mem, rfl, fun x => (Scrub.ite_f fun h => by omega_using [h]).symm⟩
  | w + 1, hb, hc => by
    obtain ⟨m', he, hz⟩ := wipeStoresAtX_zero R u off hR hx w (by omega_using [hb])
      fun k hk => hc k (by omega_using [hk])
    have hin : InRegions u.wr (u.gpr .rsp + BitVec.ofNat 64 (off + 16 * w)) 16 :=
      ⟨R, hR, hc w (by omega_using [])⟩
    refine ⟨m'.writeW (u.gpr .rsp + BitVec.ofNat 64 (off + 16 * w)) (u.xmm .xmm0), ?_, fun x => ?_⟩
    · rw [wipeStoresAtX_succ, execBlock_append, he]
      simp only [Option.bind_some, execBlock, isa, exec, State.store128, State.ea, BitVec.ofInt_natCast,
        hin, ↓reduceIte, Option.map_some, addrs, List.map_cons, List.map_nil, List.append_nil,
        wipeAtXTrace, List.range_succ, List.map_append]
    · simp only [hx, Scrub.writeW_zero128, Scrub.off_lt _ _ _ _ (show off + 16 * w + 16 < 2 ^ 64 by omega_using [hb])]
      rw [hz x]
      by_cases h₁ : off + 16 * w ≤ (x - u.gpr .rsp).toNat ∧ (x - u.gpr .rsp).toNat < off + 16 * w + 16
      · rw [Scrub.ite_t h₁, Scrub.ite_t ⟨by omega_using [h₁], by omega_using [h₁]⟩]
      · rw [Scrub.ite_f h₁]
        by_cases h₂ : off ≤ (x - u.gpr .rsp).toNat ∧ (x - u.gpr .rsp).toNat < off + 16 * w
        · rw [Scrub.ite_t h₂, Scrub.ite_t ⟨by omega_using [h₂], by omega_using [h₂]⟩]
        · rw [Scrub.ite_f h₂, Scrub.ite_f fun h => by omega_using [h, h₁, h₂]]

/-- `wipeAtX off n` zeroes the `16n` bytes at `rsp + off` and leaves the
rest of memory as it was. -/
theorem wipeAtX_zero (R : Region) (u : State) (off n : Nat) (hR : R ∈ u.wr) (hb : off + 16 * n < 2 ^ 64)
    (hc : ∀ k < n, R.Contains (u.gpr .rsp + BitVec.ofNat 64 (off + 16 * k)) 16) {m' : Mem} {t : List Leak}
    (he : execBlock isa (wipeAtX off n) u = some ({ u.setXmm .xmm0 0 with mem := m' }, t)) (x : Addr) :
    m' x = if off ≤ (x - u.gpr .rsp).toNat ∧ (x - u.gpr .rsp).toNat < off + 16 * n then 0 else u.mem x := by
  have hx : XOp.exec (.bin .pxor .xmm0 .xmm0) u = u.setXmm .xmm0 0 := by
    simp [XOp.exec, reduceXBinOpEval]
  obtain ⟨m'', he', hz⟩ := wipeStoresAtX_zero R (u.setXmm .xmm0 0) off (by simpa [State.setXmm])
    (by simp [State.setXmm]) n hb (by simpa [State.setXmm] using hc)
  have e : execBlock isa (wipeAtX off n) u =
      some ({ u.setXmm .xmm0 0 with mem := m'' }, wipeAtXTrace (u.gpr .rsp) off n) := by
    simp only [wipeAtX, execBlock, isa, exec, hx]
    rw [he']
    simp [addrs, State.setXmm]
  rw [he] at e
  have hm : m' = m'' := congrArg (fun p : State × List Leak => p.1.mem) (Option.some.inj e)
  rw [hm, hz x]
  rfl

/-- What code leaves in its frame of `withStackArgScratchWipedX`: zeros in
the `16k` bytes it wipes, at the buffer, and elsewhere in `R` (at the state
`narrowS` it runs from) what `L` says, as in `framed_leaves`. -/
theorem framedW_leaves {sig : Sig} {nm : String} {e : Elem} {n bytes stack k : Nat}
    {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {c : Prog isa} {P : State → Prop}
    {R : State → Region} {L : State → Addr → Option (BitVec 8)}
    (hv : Verified X86_64.target c (Sig.scratchContract abi sig nm e n pre post wa stack leak))
    (hP : ∀ s, (Sig.scratchContract abi sig nm e n pre post wa stack leak).pre s → P s)
    (hl : ∀ s t s', P s → Exec isa c s t s' → ∀ x, (R s).Contains x 1 → s'.mem x = (L s x).getD (s.mem x))
    (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 16 + 8 * nStack sig + n * e.size ≤ bytes ∧ bytes < 4096 ∧ bytes % 8 = 0)
    (hst : stack + bytes + 8 ≤ 2 ^ 64) (hsp : c.all (fun i => !isa.writesSp i) = true)
    (hd : c.x86_64Depth ≤ stack) (hw : 16 * k ≤ n * e.size)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) {t : List Leak} {u : State}
    (he : Exec isa (withStackArgScratchWipedX bytes (nStack sig) k c) s t u) :
    (∀ x, (⟨s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (16 + 8 * nStack sig), 16 * k⟩ : Region).Contains
        x 1 → u.mem x = 0) ∧
    ∀ x, (R (narrowS sig e n bytes s)).Contains x 1 →
      ¬ (⟨s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (16 + 8 * nStack sig), 16 * k⟩ : Region).Contains
        x 1 →
      u.mem x = (L (narrowS sig e n bytes s) x).getD ((narrowS sig e n bytes s).mem x) := by
  obtain ⟨hb0, hb1, hb2⟩ := hb
  have hn := narrowS_pre (nm := nm) hk hb0 hb1 (fun vs m₁ m₂ hl hb _ => hpre vs m₁ m₂ hl hb) hs
  obtain ⟨t₃, s₃, he₃, ha, -⟩ := hv.1 _ hn
  obtain ⟨hrsp, -, -, -, -⟩ := narrowS_facts (nm := nm) hk hb0 hb1 hs
  have hrsp₃ : s₃.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes :=
    (ha.1 .rsp (by simp [calleeSaved])).trans hrsp
  have hwr₃ : s₃.wr = (narrowS sig e n bytes s).wr := (Exec.rdwr he₃).2
  have hbuf : (⟨s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (16 + 8 * nStack sig),
      n * e.size⟩ : Region) ∈ s₃.wr := by
    rw [hwr₃]
    simp [narrowS, oldRegions, List.filter_append]
  have hcov : ∀ j < k, (⟨s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (16 + 8 * nStack sig),
      n * e.size⟩ : Region).Contains (s₃.gpr .rsp + BitVec.ofNat 64 (16 + 8 * nStack sig + 16 * j)) 16 :=
    fun j hj => by
      rw [hrsp₃]
      exact Offset.contains _ (by omega_using []) (by omega_using [hw, hj]) (by omega_using [hb0, hb1])
  obtain ⟨m', hblk, hfr⟩ := wipeAtX_run _ s₃ (16 + 8 * nStack sig) k hbuf hcov
  have hz := wipeAtX_zero _ s₃ (16 + 8 * nStack sig) k hbuf (by omega_using [hw, hb0, hb1]) hcov hblk
  have he' := Exec.seq he₃ (Exec.block hblk)
  have ha' : abiPreserved (narrowS sig e n bytes s) { s₃.setXmm .xmm0 0 with mem := m' } := by
    refine ⟨fun q hq => ha.1 q hq, ?_, ha.2.2⟩
    rw [hrsp]
    show m'.readW _ 64 = _
    rw [hfr.readW (r := ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, 8⟩) (Region.contains_self _ _)
      (fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact Offset.base_disjoint _ (e := 16 + 8 * nStack sig) (k := 8) (by omega_using []) (by omega_using [hb0, hb1]))
      (by decide)]
    have h2 := ha.2.1
    rwa [hrsp] at h2
  obtain ⟨hex, -, hm, -⟩ :=
    withStackArgScratch_runMem hk ⟨hb0, hb1, hb2⟩ hst
      (SpSafe.of_all (by simp only [Code.all, hsp, wipeAtX_spSafe, Bool.and_self]))
      (by simp only [Code.x86_64Depth]; omega_using [hd]) hs he' ha'
  obtain ⟨-, rfl⟩ := Exec.det he hex
  have hm' : (popState bytes s { s₃.setXmm .xmm0 0 with mem := m' }).mem = m' := hm
  rw [hm']
  have hlt := fun x => Scrub.off_lt x (s.gpr .rsp - BitVec.ofNat 64 bytes) (16 + 8 * nStack sig) (16 * k)
    (by omega_using [hw, hb0, hb1])
  refine ⟨fun x hx => ?_, fun x hx hnw => ?_⟩
  · rw [hz x, hrsp₃, Scrub.ite_t ((hlt x).1 (by simp only [Region.Contains] at hx; omega_using [hx]))]
  · rw [hz x, hrsp₃, Scrub.ite_f fun h => hnw (by
      simp only [Region.Contains]; have := (hlt x).2 h; omega_using [this])]
    exact hl _ _ _ (hP _ hn) he₃ x hx

/-- What `narrowS` keeps of `s`: the registers but `rax` and `rsp`, the
stack arguments, the buffer after them, and the memory outside the copies. -/
theorem narrowS_args {sig : Sig} {e : Elem} {n bytes stack : Nat}
    {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}
    (hk : 6 ≤ (sig.words abi.ptrBits).length) (hb : 16 + 8 * nStack sig + n * e.size ≤ bytes)
    (hb1 : bytes < 4096) {s : State} (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) :
    (∀ q, q ≠ .rax → q ≠ .rsp → (narrowS sig e n bytes s).gpr q = s.gpr q) ∧
      (∀ j < nStack sig, stackArg (narrowS sig e n bytes s) j = stackArg s j) ∧
      stackArg (narrowS sig e n bytes s) (nStack sig) =
        s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (16 + 8 * nStack sig) ∧
      Frame [⟨s.gpr .rsp - BitVec.ofNat 64 bytes + 8, 8 * (nStack sig + 1)⟩]
        s.mem (narrowS sig e n bytes s).mem := by
  obtain ⟨-, hg, -, -, hf⟩ := narrowS_facts (nm := "") hk hb hb1 hs
  obtain ⟨-, -, -, -, -, -, ha, hl⟩ := argsState_run hs hk hb hb1
  have e (j : Nat) : stackArg (narrowS sig e n bytes s) j =
      stackArg (setArgsState bytes (nStack sig) (allocState bytes s)) j := by
    simp only [stackArg, stackArgAddr, narrowS, State.withRegions_mem, State.withRegions_gpr]
  exact ⟨hg, fun j hj => (e j).trans (ha j hj), (e _).trans hl, hf⟩

/-- What the callee of `forward` leaves (`L`, at the state `narrowF` it runs
from), from what it leaves run by run from the states its contract's
precondition implies `P` of. -/
theorem forward_leaves {sig : Sig} {bytes stack : Nat} {name : String}
    {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {c : Prog isa} {P : State → Prop}
    {R : State → Region} {L : State → Addr → Option (BitVec 8)}
    (hv : Verified X86_64.target c (sig.contract abi pre post wa stack leak))
    (hP : ∀ s, (sig.contract abi pre post wa stack leak).pre s → P s)
    (hl : ∀ s t s', P s → Exec isa c s t s' → ∀ x, (R s).Contains x 1 → s'.mem x = (L s x).getD (s.mem x))
    (hk : 6 ≤ (sig.words abi.ptrBits).length) (hm : 0 < nStack sig)
    (hb : 8 * nStack sig ≤ bytes ∧ bytes < 4096 ∧ bytes % 8 = 0)
    (hst : stack + bytes + 16 ≤ 2 ^ 64) (hsp : c.all (fun i => !isa.writesSp i) = true)
    (hd : c.x86_64Depth ≤ stack)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      (∀ r ∈ Sig.lists abi.ptrBits m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract abi pre post wa (stack + bytes + 8) leak).pre s) {t : List Leak} {u : State}
    (he : Exec isa (forward bytes (nStack sig) name c) s t u) :
    ∀ x, (R (narrowF sig bytes s)).Contains x 1 →
      u.mem x = (L (narrowF sig bytes s) x).getD ((narrowF sig bytes s).mem x) := by
  have hn := narrowF_pre hk hm hb.1 hb.2.1 hpre hs
  obtain ⟨t₃, s₃, he₃, ha, -⟩ := hv.1 _ hn
  obtain ⟨hex, -, hmem, -⟩ := forward_run hk hm hb hst (SpSafe.of_all hsp) hd hs he₃ ha
  obtain ⟨-, rfl⟩ := Exec.det he hex
  intro x hx
  rw [hmem]
  exact hl _ _ _ (hP _ hn) he₃ x hx

end VG.X86_64
