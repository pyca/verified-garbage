module

public import VerifiedGarbage.TCB.Arm.Residue
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Arm.RegUpd

/-!
# Returning without secret residue: code without frames (ARMv7)

`NoResidue` (`TCB/Arm/Residue.lean`) asks that two runs of a function that
agree on its public data and on everything outside its buffers end agreeing
on everything outside the buffers but the result: the registers, the
condition flags, and the memory outside the buffers.

Code without frames (`Code.noFrames`) writes memory only within the regions
its state permits (`Exec.regions`), which are the function's buffers, and the
calling convention restores `r4`–`r11`, `lr` and `sp` (`abiPreserved`). What
is left are the registers a callee may change, `r0`–`r3` and `r12`, and the
flags. `scrub rb c` is `c` followed by instructions that set them to
constants (`tail`): `r2`, `r3` and `r12` to zero, the flags to those of
comparing zero with itself, and of the result `r1 ++ r0` what is above its
`rb` bits to zero (`r1` for a result of 32 bits, both for no result; ARM's
results are of 0, 32 or 64 bits, `retBits_cases`). They read no memory and
leak nothing, so `scrub rb c` meets `c`'s contract (`Verified.scrub`), and
every run of it ends with the same values there: it returns without secret
residue.

`scrubReg` is a registration with its code scrubbed, which proves it.
-/

@[expose] public section

namespace VG.Arm.Scrub

/-- Zero what of the result `r1 ++ r0` is above its `rb` bits. -/
def retFix (rb : Nat) : List Instr :=
  if rb = 0 then [.mov .r0 (.imm 0), .mov .r1 (.imm 0)]
  else if rb ≤ 32 then [.mov .r1 (.imm 0)] else []

/-- Set the registers a callee may change, but the result, and the flags to
constants. -/
def tail (rb : Nat) : List Instr :=
  retFix rb ++ [.mov .r2 (.imm 0), .mov .r3 (.imm 0), .mov .r12 (.imm 0), .cmp .r2 (.reg .r2)]

/-- `c`, then `tail rb`. -/
def scrub (rb : Nat) (c : Prog isa) : Prog isa := .seq c (.block (tail rb))

/-- A result on ARM is of 0, 32 or 64 bits. -/
theorem retBits_cases (sig : Sig) : sig.retBits 32 = 0 ∨ sig.retBits 32 = 32 ∨ sig.retBits 32 = 64 := by
  unfold Sig.retBits
  cases sig.ret with
  | none => exact .inl rfl
  | some ty => cases ty <;> simp [IntTy.bits]

theorem append_shr32 (a : BitVec 32) : (0#32 ++ a) >>> 32 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  have := a.isLt
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_append, BitVec.toNat_ofNat, Nat.zero_mod,
    Nat.zero_shiftLeft, Nat.zero_or, Nat.shiftRight_eq_div_pow]
  omega

theorem append_low32 (a b : BitVec 32) : BitVec.setWidth 32 (0#32 ++ a) = BitVec.setWidth 32 (b ++ a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_append]
  simp only [hi, decide_true, Bool.true_and, ↓reduceIte]

theorem shr64 (x : BitVec 64) : x >>> 64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.zero_mod, Nat.shiftRight_eq_div_pow]
  omega

/-- What `tail rb` leaves: it leaks nothing, keeps the memory, the regions,
the stack pointer, the registers the calling convention preserves and the
`rb` bits of the result, and leaves constants in the others and the flags. -/
theorem tail_run {rb : Nat} (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) (u : State) :
    ∃ u', execBlock isa (tail rb) u = some (u', []) ∧ u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      u'.sp = u.sp ∧ (∀ r ∈ preserved, u'.gpr r = u.gpr r) ∧
      u'.gpr .r2 = 0 ∧ u'.gpr .r3 = 0 ∧ u'.gpr .r12 = 0 ∧
      u'.n = false ∧ u'.z = true ∧ u'.c = true ∧ u'.v = false ∧
      (u'.gpr .r1 ++ u'.gpr .r0) >>> rb = 0 ∧
      (u'.gpr .r1 ++ u'.gpr .r0).setWidth rb = (u.gpr .r1 ++ u.gpr .r0).setWidth rb := by
  rcases hrb with rfl | rfl | rfl
  · refine ⟨_, by simp [tail, retFix, execBlock, isa, exec, Op2.eval, addrs]; rfl, ?_⟩
    simp only [subFlags, preserved, State.setReg]
    simp
    exact (BitVec.eq_nil _).trans (BitVec.eq_nil _).symm
  · refine ⟨_, by simp [tail, retFix, execBlock, isa, exec, Op2.eval, addrs]; rfl, ?_⟩
    simp only [subFlags, preserved, State.setReg]
    simp
    exact ⟨append_shr32 _, append_low32 _ _⟩
  · refine ⟨_, by simp [tail, retFix, execBlock, isa, exec, Op2.eval, addrs]; rfl, ?_⟩
    simp only [subFlags, preserved, State.setReg]
    simp
    exact shr64 _

/-- What `Verified.scrub` needs of the calling convention a contract is for:
`abi`'s memory, result and pointer width. -/
structure ScrubAbi (A : Abi isa) : Prop where
  ptrBits : A.ptrBits = 32
  mem : ∀ s, A.mem s = s.mem
  ret : ∀ s, A.ret s = s.gpr .r1 ++ s.gpr .r0

theorem ScrubAbi.plain : ScrubAbi abi := ⟨rfl, fun _ => rfl, fun _ => rfl⟩

theorem ScrubAbi.consts (cs : List (String × List (BitVec 64))) : ScrubAbi (abi.withConsts cs) := by
  cases cs with
  | nil => exact ScrubAbi.plain
  | cons c cs => exact ⟨rfl, fun _ => rfl, fun _ => rfl⟩

theorem ScrubAbi.tables {A : Abi isa} (hA : ScrubAbi A) (sig : Sig) (ts : List (String × List FnTable)) :
    ScrubAbi (A.withTables sig ts) := by
  cases ts with
  | nil => exact hA
  | cons t ts => exact ⟨hA.ptrBits, hA.mem, hA.ret⟩

theorem withMode_ptrBits (A : Abi isa) (b : Bool) : (A.withMode b).ptrBits = A.ptrBits := by
  cases b <;> rfl

theorem ScrubAbi.mode {A : Abi isa} (hA : ScrubAbi A) (b : Bool) : ScrubAbi (A.withMode b) := by
  cases b with
  | false => exact hA
  | true => exact ⟨hA.ptrBits, hA.mem, hA.ret⟩

/-- The calling convention of every ARM artifact (`Api.artifact`). -/
theorem ScrubAbi.of (cs : List (String × List (BitVec 64))) (sig : Sig) (ts : List (String × List FnTable))
    (b : Bool) : ScrubAbi (((abi.withConsts cs).withTables sig ts).withMode b) :=
  ((ScrubAbi.consts cs).tables sig ts).mode b

/-- A postcondition of `Sig.contract` reads of the state on return its
memory and the bits of its result. -/
theorem contract_post_scrub {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {s u u' : State}
    (h : (sig.contract A pre post wa stack leak).post s u) (hm : u'.mem = u.mem)
    (hr : (u'.gpr .r1 ++ u'.gpr .r0).setWidth (sig.retBits A.ptrBits) =
      (u.gpr .r1 ++ u.gpr .r0).setWidth (sig.retBits A.ptrBits)) :
    (sig.contract A pre post wa stack leak).post s u' := by
  simp only [Sig.contract] at h ⊢
  split at h
  · exact h.elim
  · rename_i vals hv
    simp only [hA.mem, hA.ret] at h ⊢
    rw [hm, hr]
    exact h

/-- Running `scrub rb c` is running `c`, then `tail rb`. -/
theorem exec_scrub {rb : Nat} (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) {c : Prog isa} {s u' : State}
    {t : List Leak} (h : Exec isa (scrub rb c) s t u') :
    ∃ u, Exec isa c s t u ∧ execBlock isa (tail rb) u = some (u', []) := by
  cases h with
  | seq a b =>
    cases b with
    | block hb =>
      rename_i u t₁ t₂
      obtain ⟨w, hw, -⟩ := tail_run hrb u
      rw [hw, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact ⟨u, by simpa using a, hw⟩

/-- `scrub rb c` meets the contract of `c`, code without frames, and returns
without secret residue. -/
theorem Verified.scrub {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {c : Prog isa}
    (hv : Verified target c (sig.contract A pre post wa stack leak)) (hn : c.noFrames = true)
    {rb : Nat} (e : rb = sig.retBits A.ptrBits) :
    Verified target (scrub rb c) (sig.contract A pre post wa stack leak) ∧
      NoResidue (scrub rb c) (sig.contract A pre post wa stack leak) rb := by
  have hrb : rb = 0 ∨ rb = 32 ∨ rb = 64 := by rw [e, hA.ptrBits]; exact retBits_cases sig
  refine ⟨⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ u₁ u₂ p₁ p₂ hp e₁ e₂ => ?_, hv.2.2⟩, ?_⟩
  · obtain ⟨t, u, he, habi, hpost⟩ := hv.1 s hs
    obtain ⟨u', hb, hm, -, -, hsp, hpres, -, -, -, -, -, -, -, -, hret⟩ := tail_run hrb u
    refine ⟨t ++ [], u', .seq he (.block hb), ⟨fun r hr => (hpres r hr).trans (habi.1 r hr),
      hsp.trans habi.2⟩, contract_post_scrub hA hpost hm (e ▸ hret)⟩
  · obtain ⟨w₁, a₁, -⟩ := exec_scrub hrb e₁
    obtain ⟨w₂, a₂, -⟩ := exec_scrub hrb e₂
    exact hv.2.1 s₁ s₂ t₁ t₂ w₁ w₂ p₁ p₂ hp a₁ a₂
  · intro s₁ s₂ t₁ t₂ u₁ u₂ p₁ p₂ _ ho _ e₁ e₂
    obtain ⟨w₁, a₁, b₁⟩ := exec_scrub hrb e₁
    obtain ⟨w₂, a₂, b₂⟩ := exec_scrub hrb e₂
    -- Each run keeps what the calling convention preserves, and the memory outside its buffers.
    have keep : ∀ {s w u : State} {t : List Leak}, (sig.contract A pre post wa stack leak).pre s →
        Exec isa c s t w → execBlock isa (tail rb) w = some (u, []) →
        u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧ (∀ r ∈ preserved, u.gpr r = s.gpr r) ∧
          Frame s.wr s.mem u.mem ∧ u.gpr .r2 = 0 ∧ u.gpr .r3 = 0 ∧ u.gpr .r12 = 0 ∧
          u.n = false ∧ u.z = true ∧ u.c = true ∧ u.v = false ∧ (u.gpr .r1 ++ u.gpr .r0) >>> rb = 0 := by
      intro s w u t hs a b
      obtain ⟨t', w', a', habi, -⟩ := hv.1 s hs
      obtain ⟨-, rfl⟩ := Exec.det a a'
      obtain ⟨hrd, hwr, hsp, hf⟩ := Exec.regions a hn
      obtain ⟨u', hb, hm, hrd', hwr', hsp', hpres, h2, h3, h12, fn, fz, fc, fv, hsh, -⟩ := tail_run hrb w
      rw [hb, Option.some.injEq, Prod.mk.injEq] at b
      obtain ⟨rfl, -⟩ := b
      exact ⟨hrd'.trans hrd, hwr'.trans hwr, hsp'.trans hsp, fun r hr => (hpres r hr).trans (habi.1 r hr),
        hm ▸ hf, h2, h3, h12, fn, fz, fc, fv, hsh⟩
    obtain ⟨rd₁, wr₁, sp₁, pr₁, f₁, x2, x3, x12, n₁, z₁, c₁, v₁, r₁⟩ := keep p₁ a₁ b₁
    obtain ⟨rd₂, wr₂, sp₂, pr₂, f₂, y2, y3, y12, n₂, z₂, c₂, v₂, r₂⟩ := keep p₂ a₂ b₂
    obtain ⟨ord, owr, oreg, -, osp, -, -, -, -, omem⟩ := ho
    refine ⟨rd₁.trans (ord.trans rd₂.symm), wr₁.trans (owr.trans wr₂.symm), fun r h0 h1 => ?_,
      r₁.trans r₂.symm, sp₁.trans (osp.trans sp₂.symm), n₁.trans n₂.symm, z₁.trans z₂.symm,
      c₁.trans c₂.symm, v₁.trans v₂.symm, fun x hx => ?_⟩
    · by_cases hr : r ∈ preserved
      · rw [pr₁ r hr, pr₂ r hr]; exact oreg r h0 h1
      · cases r <;> simp_all [preserved]
    · rw [rd₁, wr₁] at hx
      rw [f₁ x fun r hr => hx r (List.mem_append_right _ hr),
        f₂ x fun r hr => hx r (List.mem_append_right _ (owr ▸ hr))]
      exact omem x hx

/-- A function that writes at most the first bytes of some of its buffers
still does when the state on return is replaced by one with its memory. -/
theorem writtenWithin_mem {sig : Sig} {written : List (String × Nat)} {s u u' : State}
    (h : Sig.writtenWithin abi sig written s u) (hm : u'.mem = u.mem) :
    Sig.writtenWithin abi sig written s u' := by
  cases written with
  | nil => exact True.intro
  | cons w ws =>
    simp only [Sig.writtenWithin] at h ⊢
    split
    · exact True.intro
    · rename_i vals hv
      rw [hv] at h
      intro w hw b hb hbw i hi hl
      have := h w hw b hb hbw i hi hl
      simp only [abi] at this ⊢
      rw [hm]; exact this

/-- `r`, a registration of code without frames, scrubbed: its code followed
by `tail`, which returns without secret residue. -/
def scrubReg {api : Api} (r : Registration api target) (hn : r.code.noFrames = true) :
    Registration api target where
  suffix := r.suffix
  consts := r.consts
  tables := r.tables
  stack := r.stack
  code := scrub (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits) r.code
  contract := r.contract
  verified := by
    obtain ⟨pre, post, leak, e⟩ := r.ofSig
    have hv := r.verified
    rw [e] at hv ⊢
    exact (Verified.scrub (ScrubAbi.of r.consts api.sig r.tables api.pubMode) hv hn
      (by rw [withMode_ptrBits])).1
  ofApi := r.ofApi
  ofSig := r.ofSig
  spSafe := by
    have := r.spSafe
    simp only [scrub, Code.all, this, Bool.true_and]
    exact List.all_eq_true.mpr fun _ _ => rfl
  written := r.written
  writtenOk := by
    intro s t u' hs he
    have hrb := retBits_cases api.sig
    obtain ⟨u, a, b⟩ := exec_scrub (rb := api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
      (by rw [(ScrubAbi.tables (ScrubAbi.consts r.consts) api.sig r.tables).ptrBits]; exact hrb) he
    obtain ⟨w, hw, hm, -⟩ := tail_run (rb := api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
      (by rw [(ScrubAbi.tables (ScrubAbi.consts r.consts) api.sig r.tables).ptrBits]; exact hrb) u
    rw [hw, Option.some.injEq, Prod.mk.injEq] at b
    obtain ⟨rfl, -⟩ := b
    exact writtenWithin_mem (r.writtenOk s t u hs a) hm
  extra := r.extra
  vendor := r.vendor
  notWith := r.notWith
  residue := some ⟨by
    obtain ⟨pre, post, leak, e⟩ := r.ofSig
    have hv := r.verified
    rw [e] at hv ⊢
    exact (Verified.scrub (ScrubAbi.of r.consts api.sig r.tables api.pubMode) hv hn
      (by rw [withMode_ptrBits])).2⟩

end VG.Arm.Scrub
