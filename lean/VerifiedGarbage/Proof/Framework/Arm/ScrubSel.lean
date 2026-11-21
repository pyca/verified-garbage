module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Proof.Framework.Arm.ResidueTaintSound
public import VerifiedGarbage.Impl.Scrub.Arm.Sel
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Clearing only the words of the stack that may hold secrets (ARMv7)

`Impl.Scrub.Arm.scrubSel rb n ws c` is `c`, then a frame of the `n` bytes
below the stack pointer in which only the words `ws` are zeroed (none, and no
frame, for no word), then `tail rb`. Its run after `c` leaves the registers
the calling convention preserves, the result's `rb` bits, and the memory
outside that frame as they were (`scrubSel_run`), and leaks only addresses
that are a function of the stack pointer, so it meets `c`'s contract
(`Verified.scrubSel`), as `scrubAll` does (`Verified.scrubAllS`). It returns
without secret residue when the residue analysis (`Arm.rtaint`) of the whole
of it, from where the contract starts it, ends in `RTaint.done`
(`RTaint.noResidue_of_verified`): the analysis sees the cleanup's stores, and
that they leave no byte of the window secret.

`verifiedScrubbedSel` is the theorem a registration binds
(`verified := .scrubbed …`), as `verifiedScrubbedAll` is for `scrubAll`
(`ScrubProved.lean`): of the code with its cleanup, from the function's
`Verified`, the side condition on `n` and `ws` (`selSide`, by `decide`), and
the analysis's result (`taint_decide_ct`).
-/

@[expose] public section

namespace VG.Arm.Scrub

open VG.Impl.Scrub.Arm VG.Arm.FrameStack

/-! ## The cleanup's run -/

/-- The trace of `wipeWords ws` from a state whose `r12` is `q`. -/
def wipeWordsTr (q : BitVec 32) (ws : List Nat) : List Leak :=
  ws.map fun k => .addr (State.addr (q + BitVec.ofNat 32 (4 * k)))

/-- The trace of `wipeSel n ws` from a state whose stack pointer is `p`. -/
def wipeSelTr (p : BitVec 32) (n : Nat) : List Nat → List Leak
  | [] => []
  | k :: ws => wipeWordsTr (p - BitVec.ofNat 32 n) (k :: ws)

/-- The stores of `wipeWords ws`, of `r2` at `r12 = q`, change memory only in
the region `R`, the `n` bytes at `q`, which holds each of them. -/
theorem wipeWords_run (q : BitVec 32) (n : Nat) (hn : n ≤ 4096) (hq : q.toNat + n ≤ 2 ^ 32) :
    ∀ (ws : List Nat) (u : State), (⟨State.addr q, n⟩ : Region) ∈ u.wr → u.gpr .r12 = q →
      (∀ k ∈ ws, 4 * k + 4 ≤ n) →
      ∃ m', execBlock isa (wipeWords ws) u = some ({ u with mem := m' }, wipeWordsTr q ws) ∧
        Frame [⟨State.addr q, n⟩] u.mem m'
  | [], u, _, _, _ => ⟨u.mem, rfl, Frame.refl _ _⟩
  | k :: ws, u, hR, h12, hws => by
    have hk := hws k List.mem_cons_self
    have hc : (⟨State.addr q, n⟩ : Region).Contains (State.addr (q + BitVec.ofNat 32 (4 * k))) 4 := by
      rw [addr_add (by omega_using [hq, hk])]
      exact Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk, hn])
    let u₁ : State := { u with mem := u.mem.writeW (State.addr (q + BitVec.ofNat 32 (4 * k))) (u.gpr .r2) }
    obtain ⟨m', he, hf⟩ := wipeWords_run q n hn hq ws u₁ hR h12 fun k hk => hws k (List.mem_cons_of_mem _ hk)
    refine ⟨m', ?_, ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ hc).trans hf⟩
    have hex : exec (.str .r2 .r12 (4 * k)) u = some u₁ := by
      simp only [exec, show 4 * k < 4096 by omega_using [hk, hn], ↓reduceIte, State.store32, h12,
        show InRegions u.wr (State.addr (q + BitVec.ofNat 32 (4 * k))) 4 from ⟨_, hR, hc⟩]
      rfl
    simp only [wipeWords, List.map_cons]
    simp only [wipeWords] at he
    simp only [execBlock, isa, hex, he, Option.map_some, addrs, h12, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, wipeWordsTr]
    rfl

/-- `wipeSel n ws` zeroes words of the `n` bytes below the stack pointer, in
a frame it then releases, and changes no other byte, with a trace that is a
function of the stack pointer; it keeps the regions, the stack pointer and
every register but `r2` and `r12`. -/
theorem wipeSel_run {n : Nat} (hn : FrameOk n) (ws : List Nat) (hws : ∀ k ∈ ws, 4 * k + 4 ≤ n)
    (w : State) (hsp : n ≤ w.sp.toNat) :
    ∃ u, Exec isa (wipeSel n ws) w (wipeSelTr w.sp n ws) u ∧ u.rd = w.rd ∧ u.wr = w.wr ∧
      u.sp = w.sp ∧ (∀ r, r ≠ .r12 → r ≠ .r2 → u.gpr r = w.gpr r) ∧ Frame [belowA w.sp n] w.mem u.mem := by
  cases ws with
  | nil => exact ⟨w, .block rfl, rfl, rfl, rfl, fun _ _ _ => rfl, Frame.refl _ _⟩
  | cons k ws =>
    obtain ⟨h0, h1, h8, henc⟩ := hn
    have hsub : (w.sp - BitVec.ofNat 32 n).toNat = w.sp.toNat - n := sub_toNat' hsp
    have hlt := w.sp.isLt
    let a := allocated n w
    have ha : isa.push (.alloc n) w = some a := by
      simp only [isa, push, h0, h1, h8, henc, hsp, and_self, ite_true]
      rfl
    let u₀ := (a.setReg .r12 (a.sp + BitVec.ofNat 32 0)).setReg .r2 0
    have h12 : u₀.gpr .r12 = w.sp - BitVec.ofNat 32 n := by
      show ((a.setReg .r12 (a.sp + BitVec.ofNat 32 0)).setReg .r2 0).gpr .r12 = _
      rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_self]
      exact BitVec.add_zero _
    have hset : execBlock isa [.addSp .r12 0, .mov .r2 (.imm 0)] a = some (u₀, []) := by
      simp only [execBlock, isa, exec, show (0 : Nat) < 256 by decide, ↓reduceIte, Op2.eval,
        show encodable (0 : BitVec 32) = true by decide, Option.map_some, addrs, List.map_nil, List.append_nil]
      rfl
    obtain ⟨m', hw, hf⟩ := wipeWords_run (w.sp - BitVec.ofNat 32 n) n (by omega_using [h1])
      (by rw [hsub]; omega_using [hsp, hlt]) (k :: ws) u₀ (by simp [u₀, a, allocated, State.setReg]) h12 hws
    have hblk : execBlock isa (.addSp .r12 0 :: .mov .r2 (.imm 0) :: wipeWords (k :: ws)) a =
        some ({ u₀ with mem := m' }, wipeWordsTr (w.sp - BitVec.ofNat 32 n) (k :: ws)) := by
      have e := execBlock_append (M := isa) [.addSp .r12 0, .mov .r2 (.imm 0)] (wipeWords (k :: ws)) a
      rw [hset, Option.bind_some, hw] at e
      simpa using e
    let v : State := { u₀ with mem := m' }
    have hfr : isa.pop (.free n) a v = some { v with
        sp := v.sp + BitVec.ofNat 32 n, wr := v.wr.tail,
        mem := lose v.mem (State.addr v.sp) n v.unknowns, unknowns := fun k => v.unknowns (k + n / 2) } := by
      simp only [isa, pop, h0, h1, h8, henc, v, u₀, a, allocated, RegUpd.sp_setReg, RegUpd.wr_setReg,
        List.head?_cons, and_self, ite_true]
    refine ⟨_, by simpa [addrs, wipeSel, wipeSelTr] using Exec.frame ha (Exec.block hblk) hfr,
      ?_, ?_, ?_, fun r h12' h2' => ?_, ?_⟩
    · simp [v, u₀, a, allocated, State.setReg]
    · simp [v, u₀, a, allocated, State.setReg]
    · simp [v, u₀, a, allocated, State.setReg, BitVec.sub_add_cancel]
    · simp [v, u₀, a, allocated, State.setReg, h12', h2']
    · have hm : Frame [belowA w.sp n] w.mem m' := by simpa [u₀, a, allocated, State.setReg] using hf
      exact hm.trans (by simpa [v, u₀, a, allocated, State.setReg] using lose_frame m' _ n _)

/-- A run of `scrubSel rb n ws c` from `s`, after `c`'s run to `w`: what it
leaks after `c`'s trace is a function of the stack pointer, and it leaves
what `tail rb` leaves, and every byte outside the `n` bytes below the stack
pointer as `c` left it. -/
theorem scrubSel_run {rb n : Nat} (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) (hn : FrameOk n) {ws : List Nat}
    (hws : ∀ k ∈ ws, 4 * k + 4 ≤ n) {c : Prog isa} {s w : State} {t : List Leak}
    (hsp : n ≤ s.sp.toNat) (he : Exec isa c s t w) :
    ∃ u, Exec isa (scrubSel rb n ws c) s (t ++ (wipeSelTr s.sp n ws ++ [])) u ∧
      u.sp = s.sp ∧ (∀ r ∈ preserved, u.gpr r = w.gpr r) ∧
      (u.gpr .r1 ++ u.gpr .r0).setWidth rb = (w.gpr .r1 ++ w.gpr .r0).setWidth rb ∧
      ∀ x, ¬ (belowA s.sp n).Contains x 1 → u.mem x = w.mem x := by
  obtain ⟨-, -, hp⟩ := Exec.rdwr he
  obtain ⟨v, hv, -, -, vsp, vreg, vf⟩ := wipeSel_run hn ws hws w (hp ▸ hsp)
  obtain ⟨u, hb, hm, -, -, usp, upres, -, -, -, -, -, -, -, -, hret⟩ := tail_run hrb v
  rw [hp] at hv vf
  refine ⟨u, .seq he (.seq hv (.block hb)), usp.trans (vsp.trans hp), fun r hr => ?_, ?_, fun x hx => ?_⟩
  · rw [upres r hr]
    exact vreg r (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr)
  · rw [hret, vreg .r1 (by decide) (by decide), vreg .r0 (by decide) (by decide)]
  · rw [hm]; exact vf x fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hx

/-! ## Verified -/

/-- `scrubSel rb n ws c` meets the contract of `c`, whose postcondition reads
the memory on return only within the buffers, for a frame of `n` bytes,
within the stack the contract reserves, holding the words `ws`. -/
theorem Verified.scrubSel {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {c : Prog isa}
    (hv : Verified target c (sig.contract A pre post wa stack leak)) {n : Nat} (hn : FrameOk n)
    (hns : n ≤ stack) {ws : List Nat} (hws : ∀ k ∈ ws, 4 * k + 4 ≤ n) {rb : Nat}
    (e : rb = sig.retBits A.ptrBits) (hpost : PostOut (sig.contract A pre post wa stack leak) rb) :
    Verified target (Impl.Scrub.Arm.scrubSel rb n ws c) (sig.contract A pre post wa stack leak) := by
  have hrb : rb = 0 ∨ rb = 32 ∨ rb = 64 := by rw [e, hA.ptrBits]; exact retBits_cases sig
  have h0 : stack ≠ 0 := by have := hn.1; omega_using [this, hns]
  have hsp : ∀ {s : State}, (sig.contract A pre post wa stack leak).pre s → n ≤ s.sp.toNat := fun hs => by
    have := (contract_pre_scrub hA hs h0).1; omega_using [this, hns]
  -- Every run is `c`'s run, then the cleanup.
  have run : ∀ {s u : State} {T : List Leak}, (sig.contract A pre post wa stack leak).pre s →
      Exec isa (Impl.Scrub.Arm.scrubSel rb n ws c) s T u →
        ∃ t w, Exec isa c s t w ∧ T = t ++ (wipeSelTr s.sp n ws ++ []) := by
    intro s u T hs h
    cases h with
    | seq a b =>
      rename_i w t₁ t₂
      obtain ⟨u', hu', -⟩ := scrubSel_run hrb hn hws (hsp hs) a
      obtain ⟨hT, rfl⟩ := Exec.det (Exec.seq a b) hu'
      exact ⟨t₁, w, a, hT⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ u₁ u₂ p₁ p₂ hp e₁ e₂ => ?_, hv.2.2⟩
  · obtain ⟨t, w, he, habi, hq⟩ := hv.1 s hs
    obtain ⟨hst, hdis⟩ := contract_pre_scrub hA hs h0
    obtain ⟨u, hu, usp, upres, hret, hkeep⟩ := scrubSel_run hrb hn hws (hsp hs) he
    refine ⟨_, u, hu, ⟨fun r hr => (upres r hr).trans (habi.1 r hr), usp⟩,
      hpost s w u hs hq (fun x ⟨r, hr, hx⟩ => hkeep x fun hb => hdis r hr x (belowA_sub hns hst x hb) hx) hret⟩
  · obtain ⟨a₁, w₁, x₁, rfl⟩ := run p₁ e₁
    obtain ⟨a₂, w₂, x₂, rfl⟩ := run p₂ e₂
    rw [hv.2.1 s₁ s₂ a₁ a₂ w₁ w₂ p₁ p₂ hp x₁ x₂, contract_pub_sp hA hp]

/-! ## The theorem a registration binds -/

/-- What `scrubSel rb n ws` needs of its frame, within a stack of `stack`
bytes: a frame size of the model (`FrameOk`), within the stack, and holding
each word of `ws`. -/
def selSide (n : Nat) (ws : List Nat) (stack : Nat) : Bool :=
  decide (FrameOk n) && decide (n ≤ stack) && ws.all fun k => decide (4 * k + 4 ≤ n)

theorem of_selSide {n stack : Nat} {ws : List Nat} (h : selSide n ws stack = true) :
    FrameOk n ∧ n ≤ stack ∧ ∀ k ∈ ws, 4 * k + 4 ≤ n := by
  simp only [selSide, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- Where the residue analysis of a function starts (`RTaint.init W bp0`)
holds of the states its contract, with `W` bytes of stack, starts from: the
window is apart from every region, and so from the `e.2` bytes from what each
register `e.1` of `bp0` holds, if they are in a region (`hbp`). -/
theorem sel_pre {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {W : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} (hW : W ≠ 0) (bp0 : List (Reg × Nat))
    (hbp : ∀ s, (sig.contract A pre post wa W leak).pre s → ∀ e ∈ bp0, ∀ i < e.2, ∃ g ∈ s.rd ++ s.wr,
      g.Contains (State.addr (s.gpr e.1 + BitVec.ofNat 32 i)) 1) :
    ∀ s, (sig.contract A pre post wa W leak).pre s → W ≤ s.sp.toNat ∧
      (∀ g ∈ s.rd ++ s.wr, ∀ x, g.Contains x 1 → ¬ (x - State.addr (s.sp - BitVec.ofNat 32 W)).toNat < W) ∧
      ∀ e ∈ bp0, ∀ i < e.2,
        ¬ (State.addr (s.gpr e.1 + BitVec.ofNat 32 i) - State.addr (s.sp - BitVec.ofNat 32 W)).toNat < W := by
  intro s hs
  obtain ⟨hst, hdis⟩ := contract_pre_scrub hA hs hW
  have hout : ∀ g ∈ s.rd ++ s.wr, ∀ x, g.Contains x 1 →
      ¬ (x - State.addr (s.sp - BitVec.ofNat 32 W)).toNat < W :=
    fun g hg x hx hb => hdis g hg x (show (x - State.addr (s.sp - BitVec.ofNat 32 W)).toNat + 1 ≤ W by
      omega_using [hb]) hx
  refine ⟨hst, hout, fun e he i hi => ?_⟩
  obtain ⟨g, hg, hc⟩ := hbp s hs e he i hi
  exact hout g hg _ hc

/-- `sel_pre`'s `hbp` for no buffer (`bp0 = []`). -/
theorem hbp_nil {k : Contract isa} :
    ∀ s, k.pre s → ∀ q ∈ ([] : List (Reg × Nat)), ∀ i < q.2, ∃ g ∈ s.rd ++ s.wr,
      g.Contains (State.addr (s.gpr q.1 + BitVec.ofNat 32 i)) 1 :=
  fun _ _ _ hq => nomatch hq

/-- `r`'s code `code` with its cleanup of only the words `ws` of a frame of
`n` bytes (`scrubSel`, with a result of `rb` bits) meets `r`'s contract in
constant time and returns without secret residue, if its postcondition reads
the memory on return only within the buffers (`PostOut`), the frame is one
the model accepts within the `W` bytes of stack the contract reserves and
holds the words (`selSide`, by `decide`), and the residue analysis of the
code with its cleanup (`Arm.rtaint`, from a state where the `e.2` bytes from
what each register `e.1` of `bp0` holds are buffers of the contract's: `hbp`)
ends in `done` (`hres`, which the kernel evaluates where the theorem is used:
`⟨_, by taint_decide_ct⟩`), stated of `code`, `W` and `rb`: the theorem
about the code that a registration binds (`verified := .scrubbed …`). -/
theorem verifiedScrubbedSel {api : Api} (r : Unscrubbed api target) {n W rb : Nat} (ws : List Nat)
    (bp0 : List (Reg × Nat)) {code : Prog isa} (hpost : PostOut r.contract rb) (hs : selSide n ws W = true)
    (hbp : ∀ s, r.contract.pre s → ∀ e ∈ bp0, ∀ i < e.2, ∃ g ∈ s.rd ++ s.wr,
      g.Contains (State.addr (s.gpr e.1 + BitVec.ofNat 32 i)) 1)
    (hres : ∃ hc, (rtaint.check (RTaint.init W bp0) (scrubSel rb n ws code) hc).any (RTaint.done rb) = true)
    (hc : r.code = code := by rfl) (hW : r.stack = W := by rfl)
    (hb : api.sig.retBits target.abi.ptrBits = rb := by rfl) :
    VerifiedScrubbed target (scrubSel rb n ws code) r.contract rb := by
  subst hc
  obtain ⟨hn, hns, hws⟩ := of_selSide hs
  have e := (retBits_abi r).trans hb
  rw [← hW] at hns hres
  rw [← e] at hpost ⊢
  rw [← e] at hres
  obtain ⟨pre, post, leak, ec⟩ := r.ofSig
  have hv := r.verified
  rw [ec] at hv hpost hbp ⊢
  have hA := ScrubAbi.of r.consts api.sig r.tables
  have hv' := Verified.scrubSel hA hv hn hns hws rfl hpost
  have h0 : r.stack ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le hn.1 hns)
  exact ⟨hv', RTaint.noResidue_of_verified hv' (sel_pre hA h0 bp0 hbp) hres⟩

end VG.Arm.Scrub
