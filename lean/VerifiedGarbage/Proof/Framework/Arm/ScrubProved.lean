module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub

/-!
# Scrubbed code with its facts proved (ARMv7)

`verifiedScrubbed` and `verifiedScrubbedF` are `Verified.scrub` and
`Verified.scrubFS` of a function's proof (`Unscrubbed`), as theorems about
the code with its cleanup (`Impl.Residue.Arm.scrub rb c` and `scrubF rb n c`,
which `Impl/` defines as the function): the proof a registration binds
(`verified := .scrubbed …`), whose code is that definition. The stack and the result's bits are
arguments (literals at the call site), and what the cleanup needs of the
code is one Boolean, whose proof the call site gives and the kernel checks
when its module is built: `Code.noFrames` for `scrub` (the code writes memory
only in its buffers), `scrubSideF` for `scrubF` (its frames are within the
`n` bytes it zeroes, `n` is a frame size of the model, and it calls
indirectly only the functions of its tables). The tail clears every
register a callee may change whatever the code writes, so nothing is asked
of the registers.

For code that calls an implementation chosen among several, `CodeOk` is what
the cleanup needs of each piece: each implementation proves it of its own
code where it is defined (by `lit_decide`), the function proves its own
instructions once for any implementation (`CodeOk.call`, `CodeOk.seq`, …),
and `scrubSideF_of` joins them.
-/

@[expose] public section

namespace VG.Arm.Scrub

open VG.Arm.FrameStack VG.Impl.Residue.Arm

/-- What `scrubF rb n c` needs of code `c` with the tables `ts`: its frames
use at most the `n` bytes it zeroes, `n` is a frame size of the model
(`FrameOk`), and `c` calls indirectly only the functions of `ts`. -/
def scrubSideF (c : Prog isa) (n : Nat) (ts : List (String × List FnTable)) : Bool :=
  decide (armStack c ≤ n) && decide (FrameOk n) && tablesCall c ts

theorem of_scrubSideF {c : Prog isa} {n : Nat} {ts : List (String × List FnTable)}
    (h : scrubSideF c n ts = true) : armStack c ≤ n ∧ FrameOk n ∧ tablesCall c ts = true := by
  simp only [scrubSideF, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- Code whose frames use at most `n` bytes and that makes no indirect call:
what `scrubF` needs of a piece of a function's code, which an implementation
a function calls proves of its own code. -/
abbrev CodeOk (c : Prog isa) (n : Nat) : Prop := armStack c ≤ n ∧ noIcall c = true

theorem CodeOk.block (is : List Instr) : CodeOk (.block is) 0 := ⟨Nat.le_refl 0, rfl⟩

theorem CodeOk.mono {c : Prog isa} {n n' : Nat} (h : CodeOk c n) (hn : n ≤ n') : CodeOk c n' :=
  ⟨Nat.le_trans h.1 hn, h.2⟩

theorem CodeOk.seq {a b : Prog isa} {n : Nat} (ha : CodeOk a n) (hb : CodeOk b n) :
    CodeOk (.seq a b) n :=
  ⟨Nat.max_le.mpr ⟨ha.1, hb.1⟩, by simp only [noIcall, ha.2, hb.2, Bool.and_self]⟩

theorem CodeOk.ite {cc : Cond} {t e : Prog isa} {n : Nat} (ht : CodeOk t n) (he : CodeOk e n) :
    CodeOk (.ite cc t e) n :=
  ⟨Nat.max_le.mpr ⟨ht.1, he.1⟩, by simp only [noIcall, ht.2, he.2, Bool.and_self]⟩

theorem CodeOk.loop {b : Prog isa} {cc : Cond} {n : Nat} (hb : CodeOk b n) : CodeOk (.loop b cc) n :=
  ⟨hb.1, by simp only [noIcall, hb.2]⟩

theorem CodeOk.call {name : String} {b : Prog isa} {n : Nat} (hb : CodeOk b n) :
    CodeOk (.call name b) n :=
  ⟨hb.1, by simp only [noIcall, hb.2]⟩

theorem CodeOk.alloc {b : Prog isa} {k n : Nat} {j : Instr} (hb : CodeOk b n) :
    CodeOk (.frame (.alloc k) b j) (n + k) :=
  ⟨by simp only [armStack]; exact Nat.add_le_add_right hb.1 k, by simp only [noIcall, hb.2]⟩

theorem CodeOk.push {b : Prog isa} {rs : List Reg} {j : Instr} {n : Nat} (hb : CodeOk b n) :
    CodeOk (.frame (.push rs) b j) (n + 4 * rs.length) :=
  ⟨by simp only [armStack]; exact Nat.add_le_add_right hb.1 _, by simp only [noIcall, hb.2]⟩

/-- `scrubSideF` of code from `CodeOk` of it, which the function's own
instructions and the implementations it calls give together. -/
theorem scrubSideF_of {c : Prog isa} {n : Nat} (h : CodeOk c n) (hn : FrameOk n)
    (ts : List (String × List FnTable)) : scrubSideF c n ts = true := by
  simp only [scrubSideF, h.1, decide_eq_true hn, tablesCall_of_noIcall h.2, decide_true, Bool.and_self]

/-- The result's bits of `r`'s contract, at the target's pointer width,
which the calling conventions with tables of constants and of functions
keep. -/
theorem retBits_abi {api : Api} (r : Unscrubbed api target) :
    api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits =
      api.sig.retBits target.abi.ptrBits := by
  rw [(ScrubAbi.of r.consts api.sig r.tables).ptrBits]; rfl

/-- `r`'s code, which has no frames, with its cleanup (`scrub`, the result's
`rb` bits kept) meets `r`'s contract in constant time and returns without
secret residue (`Verified.scrub`): the theorem about the code that a
registration binds (`verified := .scrubbed …`). -/
theorem verifiedScrubbed {api : Api} (r : Unscrubbed api target) {rb : Nat}
    (hs : r.code.noFrames = true) (hb : api.sig.retBits target.abi.ptrBits = rb := by rfl) :
    VerifiedScrubbed target (scrub rb r.code) r.contract rb := by
  have h : VerifiedScrubbed target
      (scrub (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits) r.code)
      r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits) := by
    obtain ⟨pre, post, leak, e⟩ := r.ofSig
    have hv := r.verified
    rw [e] at hv ⊢
    obtain ⟨h₁, h₂⟩ := Verified.scrub (ScrubAbi.of r.consts api.sig r.tables) hv hs rfl
    exact ⟨h₁, h₂⟩
  rw [retBits_abi, hb] at h
  exact h

/-- `r`'s code, whose frames use at most the `n` bytes of stack its contract
reserves (`scrubSideF`), with its cleanup (`scrubF`: those bytes zeroed, the
result's `rb` bits kept) meets `r`'s contract in constant time and returns
without secret residue, if its postcondition reads the memory on return only
within the buffers (`PostOut`; `Verified.scrubFS`, whose functions called
indirectly are those of the tables, `tablesCall_pub`): the theorem about the
code that a registration binds (`verified := .scrubbed …`). -/
theorem verifiedScrubbedF {api : Api} (r : Unscrubbed api target) {n rb : Nat}
    (hpost : PostOut r.contract rb) (hs : scrubSideF r.code n r.tables = true)
    (hW : r.stack = n := by rfl) (hb : api.sig.retBits target.abi.ptrBits = rb := by rfl) :
    VerifiedScrubbed target (scrubF rb n r.code) r.contract rb := by
  obtain ⟨hd, hn, htc⟩ := of_scrubSideF hs
  have e := (retBits_abi r).trans hb
  rw [← hW] at hd hn ⊢
  rw [← e] at hpost ⊢
  obtain ⟨pre, post, leak, ec⟩ := r.ofSig
  have hv := r.verified
  rw [ec] at hv hpost ⊢
  obtain ⟨h₁, h₂⟩ := Verified.scrubFS (ScrubAbi.of r.consts api.sig r.tables) hv hd (tablesCall_pub htc) hn
    rfl hpost
  exact ⟨h₁, h₂⟩

end VG.Arm.Scrub
