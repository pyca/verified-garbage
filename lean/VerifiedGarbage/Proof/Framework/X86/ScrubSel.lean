module

public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.X86.ResidueTaintSound
public import VerifiedGarbage.Impl.Scrub.X86.Sel
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Framework.X86.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Clearing only the doublewords of the stack that may hold secrets (x86, 32-bit)

`Impl.Scrub.X86.scrubSel rb n ws c` is `c`, then a frame of the `n` bytes
below `esp` in which only the doublewords `ws` are zeroed (none, and no
frame, for no doubleword), then `tail rb`, as on ARMv7
(`Proof/Framework/Arm/ScrubSel.lean`). Its run after `c` leaves the
callee-saved registers, the result's `rb` bits, and the memory outside that
frame as they were (`scrubSel_run`), and leaks only addresses that are a
function of `esp`, so it meets `c`'s contract (`Verified.scrubSel`), as
`scrubAll` does (`Verified.scrubAllT`). It returns without secret residue
when the residue analysis (`X86.rtaint`) of the whole of it, from where the
contract starts it, ends in `RTaint.done` (`RTaint.noResidue_of_verified`):
the analysis sees the cleanup's stores, and that they leave no byte of the
window secret.

`verifiedScrubbedSel` is the theorem a registration binds
(`verified := …`), as `verifiedScrubbedAll` is for `scrubAll`
(`ScrubProved.lean`): of the code with its cleanup, from the function's
`Verified`, the side condition on `n` and `ws` (`selSide`, by `decide`), and
the analysis's result (`taint_decide_ct`). The analysis starts knowing none
of the arguments (`RTaint.init W 0`): the code reads them into registers
and frames it then knows as secret, which is enough where the frames that
hold them are the code's own and are wiped.
-/

@[expose] public section

namespace VG.X86.Scrub

open VG.Impl.Scrub.X86

/-! ## The cleanup's run -/

/-- The trace of `wipeWords ws` from a state whose `esp` is `q`. -/
def wipeWordsTr (q : BitVec 32) (ws : List Nat) : List Leak :=
  ws.map fun k => .addr ((q + BitVec.ofNat 32 (4 * k)).setWidth 64)

/-- The trace of `wipeSel n ws` from a state whose `esp` is `e`. -/
def wipeSelTr (e : BitVec 32) (n : Nat) : List Nat → List Leak
  | [] => []
  | k :: ws => wipeWordsTr (e - BitVec.ofNat 32 n) (k :: ws)

/-- The stores of `wipeWords ws`, of `ecx` at `esp = q`, change memory only
in the region `R`, the `n` bytes at `q`, which holds each of them. -/
theorem wipeWords_run (q : BitVec 32) (n : Nat) (hq : q.toNat + n ≤ 2 ^ 32) :
    ∀ (ws : List Nat) (u : State), (⟨q.setWidth 64, n⟩ : Region) ∈ u.wr → u.gpr .esp = q →
      (∀ k ∈ ws, 4 * k + 4 ≤ n) →
      ∃ m', execBlock isa (wipeWords ws) u = some ({ u with mem := m' }, wipeWordsTr q ws) ∧
        Frame [⟨q.setWidth 64, n⟩] u.mem m'
  | [], u, _, _, _ => ⟨u.mem, rfl, Frame.refl _ _⟩
  | k :: ws, u, hR, hsp, hws => by
    have hk := hws k List.mem_cons_self
    have ha : (q + BitVec.ofNat 32 (4 * k)).setWidth 64 = q.setWidth 64 + BitVec.ofNat 64 (4 * k) :=
      addr_eq (by omega_using [hq, hk])
    have hc : (⟨q.setWidth 64, n⟩ : Region).Contains ((q + BitVec.ofNat 32 (4 * k)).setWidth 64) 4 := by
      rw [ha]; exact Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk, hq])
    let u₁ : State := { u with mem := u.mem.writeW ((q + BitVec.ofNat 32 (4 * k)).setWidth 64) (u.gpr .ecx) }
    obtain ⟨m', he, hf⟩ := wipeWords_run q n hq ws u₁ hR hsp fun k hk => hws k (List.mem_cons_of_mem _ hk)
    refine ⟨m', ?_, ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ hc).trans hf⟩
    have hex : exec (.store ⟨.esp, 4 * k⟩ .ecx) u = some u₁ := by
      simp only [reduceExec, State.store32, State.ea, hsp, show InRegions u.wr ((q + BitVec.ofNat 32 (4 * k)).setWidth 64) 4
        from ⟨_, hR, hc⟩, ite_true]
      rfl
    simp only [wipeWords, List.map_cons]
    simp only [wipeWords] at he
    simp only [execBlock, isa, hex, he, Option.map_some, addrs, State.ea, hsp, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, wipeWordsTr]
    rfl

/-- `wipeSel n ws` zeroes doublewords of the `n` bytes below `esp`, in a
frame it then releases, and changes no other byte, with a trace that is a
function of `esp`; it keeps the regions, `esp` and every register but
`ecx`, and the MMX state, MXCSR and the MCDT frames. -/
theorem wipeSel_run {n : Nat} (hn : 0 < n ∧ n < 4096 ∧ n % 4 = 0) (ws : List Nat)
    (hws : ∀ k ∈ ws, 4 * k + 4 ≤ n) (w : State) (hsp : n ≤ (w.gpr .esp).toNat) :
    ∃ u, Exec isa (wipeSel n ws) w (wipeSelTr (w.gpr .esp) n ws) u ∧ u.rd = w.rd ∧ u.wr = w.wr ∧
      (∀ r, r ≠ .ecx → u.gpr r = w.gpr r) ∧ u.mm = w.mm ∧ u.mmx = w.mmx ∧ u.mxcsr = w.mxcsr ∧
      u.mcdt = w.mcdt ∧ Frame [below (w.gpr .esp) n] w.mem u.mem := by
  cases ws with
  | nil => exact ⟨w, .block rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | cons k ws =>
    obtain ⟨h0, h1, h4⟩ := hn
    have hsub : (w.gpr .esp - BitVec.ofNat 32 n).toNat = (w.gpr .esp).toNat - n := RTaint.sub_toNat' hsp
    have hlt := (w.gpr .esp).isLt
    let a : State := { w.setReg .esp (w.gpr .esp - BitVec.ofNat 32 n) with
      wr := ⟨(w.gpr .esp - BitVec.ofNat 32 n).setWidth 64, n⟩ :: w.wr }
    have ha : isa.push (.alloc n) w = some a := by
      simp only [isa, X86.push, h0, h1, h4, hsp, and_self, ite_true]; rfl
    let u₀ := a.setReg .ecx 0
    have hesp : u₀.gpr .esp = w.gpr .esp - BitVec.ofNat 32 n := by simp [u₀, a, State.setReg]
    have hset : execBlock isa [.mov .ecx (.imm 0)] a = some (u₀, []) := rfl
    obtain ⟨m', hw, hf⟩ := wipeWords_run (w.gpr .esp - BitVec.ofNat 32 n) n
      (by rw [hsub]; omega_using [hsp, hlt]) (k :: ws) u₀ (by simp [u₀, a, State.setReg]) hesp hws
    have hblk : execBlock isa (.mov .ecx (.imm 0) :: wipeWords (k :: ws)) a =
        some ({ u₀ with mem := m' }, wipeWordsTr (w.gpr .esp - BitVec.ofNat 32 n) (k :: ws)) := by
      have e := execBlock_append (M := isa) [.mov .ecx (.imm 0)] (wipeWords (k :: ws)) a
      rw [hset, Option.bind_some, hw] at e
      simpa using e
    let v : State := { u₀ with mem := m' }
    have hfr : isa.pop (.free n) a v = some { v.setReg .esp (v.gpr .esp + BitVec.ofNat 32 n) with
        wr := v.wr.tail, mem := lose v.mem ((v.gpr .esp).setWidth 64) n v.unknowns,
        unknowns := fun k => v.unknowns (k + n / 2) } := by
      simp only [isa, X86.pop, h0, h1, h4, v, u₀, a, RegUpd.gpr_setReg_of_ne _ _ (show Reg.esp ≠ .ecx by decide),
        RegUpd.wr_setReg, List.head?_cons, and_self, ite_true, RegUpd.gpr_setReg_self]
    refine ⟨_, by simpa [addrs, wipeSel, wipeSelTr] using Exec.frame ha (Exec.block hblk) hfr,
      ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [v, u₀, a, State.setReg]
    · simp [v, u₀, a, State.setReg]
    · by_cases hre : r = .esp
      · subst hre; simp [v, u₀, a, State.setReg, BitVec.sub_add_cancel]
      · simp [v, u₀, a, State.setReg, hr, hre]
    · simp [v, u₀, a, State.setReg]
    · simp [v, u₀, a, State.setReg]
    · simp [v, u₀, a, State.setReg]
    · simp [v, u₀, a, State.setReg]
    · have hm : Frame [below (w.gpr .esp) n] w.mem m' := by simpa [u₀, a, State.setReg] using hf
      exact hm.trans (by simpa [v, u₀, a, State.setReg] using lose_frame m' _ n _)

/-- What a run of `scrubSel rb n ws c` leaves, after `c`'s run to `w`, from `s`. -/
structure SelOk (rb n : Nat) (s w u : State) : Prop where
  tail : ∃ v, TailOk rb v u ∧ v.rd = w.rd ∧ v.wr = w.wr ∧ (∀ r, r ≠ .ecx → v.gpr r = w.gpr r) ∧
    Frame [below (s.gpr .esp) n] w.mem v.mem

/-- A run of `scrubSel rb n ws c` from `s`, after `c`'s run to `w`, which
leaves `esp` as it was: what it leaks after `c`'s trace is a function of
`esp`. -/
theorem scrubSel_run {rb n : Nat} (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) (hn : 0 < n ∧ n < 4096 ∧ n % 4 = 0)
    {ws : List Nat} (hws : ∀ k ∈ ws, 4 * k + 4 ≤ n) {c : Prog isa} {s w : State} {t : List Leak}
    (hsp : n ≤ (s.gpr .esp).toNat) (he : Exec isa c s t w) (hp : w.gpr .esp = s.gpr .esp) :
    ∃ u, Exec isa (scrubSel rb n ws c) s (t ++ (wipeSelTr (s.gpr .esp) n ws ++ [])) u ∧ SelOk rb n s w u := by
  obtain ⟨v, hv, vrd, vwr, vreg, -, -, -, -, vf⟩ := wipeSel_run hn ws hws w (hp ▸ hsp)
  obtain ⟨u, hb, ok⟩ := tail_run hrb v
  rw [hp] at hv vf
  exact ⟨u, .seq he (.seq hv (.block hb)), ⟨v, ok, vrd, vwr, vreg, vf⟩⟩

/-- The `n` bytes below `e` are among the `m` below it. -/
theorem below_sub {e : BitVec 32} {n m : Nat} (hnm : n ≤ m) (hm : m ≤ e.toNat) {x : Addr}
    (hx : (below e n).Contains x 1) : (below e m).Contains x 1 := by
  simp only [Region.Contains, Taint.sub_setWidth hm, Taint.sub_setWidth (Nat.le_trans hnm hm)] at hx ⊢
  have he := e.isLt
  generalize e.setWidth 64 = E at *
  simp only [Offset.sub_sub_eq, Offset.toNat_add_ofNat] at hx ⊢
  have := (x - E).isLt
  rw [Nat.mod_eq_of_lt (a := n) (by omega_using [hnm, hm, he]), Nat.mod_eq_of_lt (a := m) (by omega_using [hm, he])]
    at *
  omega_using [hx, hnm]

/-! ## Verified -/

/-- `scrubSel rb n ws c` meets the contract of `c`, whose postcondition
reads the memory on return only within the buffers, for a frame of `n`
bytes, within the stack the contract reserves, holding the doublewords `ws`. -/
theorem Verified.scrubSel {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {c : Prog isa}
    (hv : Verified target c (sig.contract A pre post wa stack leak)) {n : Nat}
    (hn : 0 < n ∧ n < 4096 ∧ n % 4 = 0) (hns : n ≤ stack) {ws : List Nat} (hws : ∀ k ∈ ws, 4 * k + 4 ≤ n)
    {rb : Nat} (e : rb = sig.retBits A.ptrBits) (hpost : PostOut (sig.contract A pre post wa stack leak) rb) :
    Verified target (Impl.Scrub.X86.scrubSel rb n ws c) (sig.contract A pre post wa stack leak) := by
  have hrb : rb = 0 ∨ rb = 32 ∨ rb = 64 := by rw [e, hA.ptrBits]; exact retBits_cases sig
  have h0 : stack ≠ 0 := by have := hn.1; omega_using [this, hns]
  have hsp : ∀ {s : State}, (sig.contract A pre post wa stack leak).pre s → n ≤ (s.gpr .esp).toNat := fun hs => by
    have := (contract_pre_scrub hA hs h0).1; omega_using [this, hns]
  -- `c`'s run keeps `esp`.
  have hesp : ∀ {s w : State} {t : List Leak}, (sig.contract A pre post wa stack leak).pre s →
      Exec isa c s t w → w.gpr .esp = s.gpr .esp := by
    intro s w t hs he
    obtain ⟨t', w', he', habi, -⟩ := hv.1 s hs
    obtain ⟨-, rfl⟩ := Exec.det he he'
    exact habi.1 .esp (by simp [calleeSaved])
  -- Every run is `c`'s run, then the cleanup.
  have run : ∀ {s u : State} {T : List Leak}, (sig.contract A pre post wa stack leak).pre s →
      Exec isa (Impl.Scrub.X86.scrubSel rb n ws c) s T u →
        ∃ t w, Exec isa c s t w ∧ T = t ++ (wipeSelTr (s.gpr .esp) n ws ++ []) := by
    intro s u T hs h
    cases h with
    | seq a b =>
      rename_i w t₁ t₂
      obtain ⟨u', hu', -⟩ := scrubSel_run hrb hn hws (hsp hs) a (hesp hs a)
      obtain ⟨hT, rfl⟩ := Exec.det (Exec.seq a b) hu'
      exact ⟨t₁, w, a, hT⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ u₁ u₂ p₁ p₂ hp e₁ e₂ => ?_, hv.2.2⟩
  · obtain ⟨t, w, he, habi, hq⟩ := hv.1 s hs
    obtain ⟨hst, hdis⟩ := contract_pre_scrub hA hs h0
    obtain ⟨u, hu, ⟨v, ok, -, -, vreg, vf⟩⟩ := scrubSel_run hrb hn hws (hsp hs) he (hesp hs he)
    have hsp' := hsp hs
    refine ⟨_, u, hu, ⟨fun r hr => ?_, ?_⟩, hpost s w u hs hq (fun x ⟨r, hr, hx⟩ => ?_) ?_⟩
    · obtain ⟨h0, h1, h2⟩ := saved_ne hr
      rw [ok.gpr r h0 h1 h2, vreg r h1]; exact habi.1 r hr
    · rw [ok.mem, vf.readW (Region.contains_self _ _) (ret_slot_disjoint hsp') (by decide)]
      exact habi.2
    · rw [ok.mem]; exact vf x fun r' hr' hb => by
        rw [List.mem_singleton.mp hr'] at hb; exact hdis r hr x (below_sub hns hst hb) hx
    · rw [ok.lo, vreg .edx (by decide), vreg .eax (by decide)]
  · obtain ⟨a₁, w₁, x₁, rfl⟩ := run p₁ e₁
    obtain ⟨a₂, w₂, x₂, rfl⟩ := run p₂ e₂
    rw [hv.2.1 s₁ s₂ a₁ a₂ w₁ w₂ p₁ p₂ hp x₁ x₂, contract_pub_sp hA hp]

/-! ## The theorem a registration binds -/

/-- What `scrubSel rb n ws` needs of its frame, within a stack of `stack`
bytes: a frame size of the model, within the stack, and holding each
doubleword of `ws`. -/
def selSide (n : Nat) (ws : List Nat) (stack : Nat) : Bool :=
  decide (0 < n) && decide (n < 4096) && n % 4 == 0 && decide (n ≤ stack) && ws.all fun k => decide (4 * k + 4 ≤ n)

theorem of_selSide {n stack : Nat} {ws : List Nat} (h : selSide n ws stack = true) :
    (0 < n ∧ n < 4096 ∧ n % 4 = 0) ∧ n ≤ stack ∧ ∀ k ∈ ws, 4 * k + 4 ≤ n := by
  simp only [selSide, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
  exact ⟨⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2⟩, h.1.2, h.2⟩

/-- The calling convention of every x86 artifact asks of `esp` that its
return address is within the address space. -/
theorem wf_top {cs : List (String × List (BitVec 64))} {sig : Sig} {ts : List (String × List FnTable)}
    {ws : List Nat} {n : Nat} {s : State} (hn : n ≠ 0) (h : ((abi.withConsts cs).withTables sig ts).wf ws n s) :
    (s.gpr .esp).toNat + 4 ≤ 2 ^ 32 := by
  have h1 : (abi.withConsts cs).wf ws n s := by
    cases ts with
    | nil => exact h
    | cons t ts => exact h.1
  have h2 : abi.wf ws n s := by
    cases cs with
    | nil => exact h1
    | cons c cs => exact h1.1
  cases n with
  | zero => exact absurd rfl hn
  | succ n => have := h2.2; omega_using [this]

/-- Where the residue analysis of a function starts (`RTaint.init W 0`)
holds of the states its contract, with `W` bytes of stack, starts from: the
window is apart from every region, and within the address space with the
return address above it. -/
theorem sel_pre {A : Abi isa} (hA : ScrubAbi A)
    (htop : ∀ ws n s, n ≠ 0 → A.wf ws n s → (s.gpr .esp).toNat + 4 ≤ 2 ^ 32) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)} {post : sig.Post A.ptrBits} {wa : Bool} {W : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} (hW : W ≠ 0) :
    ∀ s, (sig.contract A pre post wa W leak).pre s →
      W ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 + 0 ≤ 2 ^ 32 ∧
      ∀ g ∈ s.rd ++ s.wr, ∀ x, g.Contains x 1 → ¬ (x - (s.gpr .esp - BitVec.ofNat 32 W).setWidth 64).toNat < W := by
  intro s hs
  obtain ⟨hst, hdis⟩ := contract_pre_scrub hA hs hW
  refine ⟨hst, ?_, fun g hg x hx hb => hdis g hg x (show (x - (s.gpr .esp - BitVec.ofNat 32 W).setWidth 64).toNat + 1 ≤ W by
      omega_using [hb]) hx⟩
  have hs' := hs
  simp only [Sig.contract] at hs'
  split at hs'
  · exact hs'.elim
  · exact htop _ _ _ hW hs'.1

/-- `r`'s code `code` with its cleanup of only the doublewords `ws` of a
frame of `n` bytes (`scrubSel`, with a result of `rb` bits) meets `r`'s
contract in constant time and returns without secret residue, if its
postcondition reads the memory on return only within the buffers
(`PostOut`), the frame is one the model accepts within the `W` bytes of
stack the contract reserves and holds the doublewords (`selSide`, by
`decide`), and the residue analysis of the code with its cleanup
(`X86.rtaint`, from `RTaint.init W 0`) ends in `done` (`hres`, which the
kernel evaluates where the theorem is used: `⟨_, by taint_decide_ct⟩`),
stated of `code`, `W` and `rb`: the theorem about the code that a
registration binds (`verified := …`). -/
theorem verifiedScrubbedSel {api : Api} (r : Unscrubbed api target) {n W rb : Nat} (ws : List Nat)
    {code : Prog isa} (hpost : PostOut r.contract (retBitsOf r)) (hs : selSide n ws W = true)
    (hres : ∃ hc, (rtaint.check (RTaint.init W 0) (scrubSel rb n ws code) hc).any (RTaint.done rb) = true)
    (hc : r.code = code := by rfl) (hW : r.stack = W := by rfl) (hb : retBitsOf r = rb := by rfl) :
    VerifiedScrubbed target (scrubSel rb n ws code) r.contract rb := by
  subst hc hb
  obtain ⟨hn, hns, hws⟩ := of_selSide hs
  rw [← hW] at hns hres
  obtain ⟨pre, post, leak, ec⟩ := r.ofSig
  have hv := r.verified
  have hp := hpost
  unfold retBitsOf at hp hres ⊢
  rw [ec] at hv hp ⊢
  have hA := ScrubAbi.of r.consts api.sig r.tables
  have hv' := Verified.scrubSel hA hv hn hns hws rfl hp
  have h0 : r.stack ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le hn.1 hns)
  exact ⟨hv', RTaint.noResidue_of_verified hv' (sel_pre hA (fun _ _ _ hn h => wf_top hn h) h0)
    (fun _ _ _ _ _ _ _ hj => absurd hj (Nat.not_lt_zero _)) hres⟩

end VG.X86.Scrub
