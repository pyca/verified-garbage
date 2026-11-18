module

public import VerifiedGarbage.Spec.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.Contract
import VerifiedGarbage.Proof.Sha512.X86.Rounds
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Blake2.X86.Blake2b
import VerifiedGarbage.Proof.Blake2.X86.LitB
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha256.X86.Lit
meta import VerifiedGarbage.Spec.Argon2.Contract
meta import VerifiedGarbage.Proof.Sha512.X86.Rounds
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Blake2.X86.Blake2b
meta import VerifiedGarbage.Proof.Blake2.X86.LitB
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha256.X86.Lit
import VerifiedGarbage.Proof.Sha256.X86.Compress
meta import VerifiedGarbage.Proof.Sha256.X86.Compress
public import VerifiedGarbage.Proof.Argon2.X86.HPrime.Finish
meta import VerifiedGarbage.Proof.Argon2.X86.HPrime.Finish
import VerifiedGarbage.Proof.Argon2.X86.HPrime.Next
public import VerifiedGarbage.Proof.Argon2.X86.HPrime.CallsCT
import VerifiedGarbage.Proof.Sha256.X86.Stream.Common
meta import VerifiedGarbage.Proof.Argon2.X86.HPrime.Next
meta import VerifiedGarbage.Proof.Argon2.X86.HPrime.CallsCT
meta import VerifiedGarbage.Proof.Sha256.X86.Stream.Common

/-! ### `Argon2.X86.HPrime.FinishCT`, which this module and modules that import it used -/

section

/-! ### `Argon2.X86.HPrime.HashCT`, which this module and modules that import it used -/

section

/-!
# Argon2 H′ on x86 (32-bit): the hash macros, in two runs

`absorbFixed_rel` and `next_rel`: hashing a fixed buffer of `scratch`, and
the digest, leak the same trace in two runs with the same `scratch` and
stack pointer.
-/

@[expose] public section

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (init update finalize absorbFixed next)
open VG.Proof.Sha256.X86.Stream (Upd wp_movi wp_mov wp_addi)

/-- The instructions before `absorbFixed`'s call of `update`. -/
theorem absorbFixed_blk {B E : BitVec 32} {s : State} (c : Ctx B E s) {offset size : Nat}
    (ho : B.toNat + offset + size ≤ 2 ^ 32) (hs : 0 < size) (hlt : size < 2 ^ 32)
    (hcov : Covers [⟨B.setWidth 64 + BitVec.ofNat 64 offset, size⟩] s.wr) :
    WP isa (.block [.mov .ecx (.imm 0), .mov .edx (.imm 0), .mov .esi (.reg .ebx),
      .alu .add .esi (.imm (BitVec.ofNat 32 offset)), .mov .edi (.imm (BitVec.ofNat 32 size))]) s
      (UpdateIn B E (B + BitVec.ofNat 32 offset) size 0 0) := by
  have hfit := c.fits
  refine wp_movi fun s₁ u₁ => wp_movi fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_addi fun s₄ u₄ =>
    wp_movi fun s₅ u₅ => WP.block_nil ?_
  have o : ∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .edi → s₅.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₅.other _ h4, u₄.other _ h3, u₃.other _ h3, u₂.other _ h2, u₁.other _ h1]
  have w : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine ⟨c.of_regs (o _ (by decide) (by decide) (by decide) (by decide))
    (o _ (by decide) (by decide) (by decide) (by decide)) w, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), c.ebx]
  · rw [u₅.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hlt])]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [setWidth_add (by omega_using [ho, hs]), show s₅.rd ++ s₅.wr = s.rd ++ s.wr by
      rw [w, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]]
    exact Covers.right hcov

/-- What `absorbFixed` needs: the context, and the buffer writable. -/
def FixedIn (B E : BitVec 32) (offset size : Nat) (s : State) : Prop :=
  Ctx B E s ∧ Covers [⟨B.setWidth 64 + BitVec.ofNat 64 offset, size⟩] s.wr

theorem absorbFixed_rel {B E : BitVec 32} {offset size : Nat} (ho : B.toNat + offset + size ≤ 2 ^ 32)
    (hlo : 768 ≤ offset) (hs : 0 < size)
    (hstk : (below E 60).Disjoint ⟨B.setWidth 64 + BitVec.ofNat 64 offset, size⟩)
    (hc : ∃ hc, (VG.Taint.check taint (τr [.esp, .ebx]) (.block [.mov .ecx (.imm 0), .mov .edx (.imm 0),
      .mov .esi (.reg .ebx), .alu .add .esi (.imm (BitVec.ofNat 32 offset)),
      .mov .edi (.imm (BitVec.ofNat 32 size))]) hc).isSome = true) :
    RelCT isa (fun s₁ s₂ => FixedIn B E offset size s₁ ∧ FixedIn B E offset size s₂)
      (absorbFixed offset size) fun _ _ => True := by
  have eD : (B + BitVec.ofNat 32 offset).setWidth 64 = B.setWidth 64 + BitVec.ofNat 64 offset :=
    setWidth_add (by omega_using [ho, hs])
  have dTo : (B + BitVec.ofNat 32 offset).toNat = B.toNat + offset := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := offset) (by omega_using [ho, hs])]; omega_using [ho, hs]
  unfold absorbFixed
  refine RelCT.seq (rel_taint [.esp, .ebx] (fun s₁ s₂ ⟨c₁, _⟩ ⟨c₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [c₁.esp, c₂.esp]
      · rw [c₁.ebx, c₂.ebx]) hc
    (fun s ⟨c, h⟩ => absorbFixed_blk c ho hs (by omega_using [ho, hlo]) h) (fun s ⟨c, h⟩ => absorbFixed_blk c ho hs (by omega_using [ho, hlo]) h))
    (update_rel (by rw [dTo]; omega_using [ho]) (by rw [eD]; exact Offset.disjoint_base _ hlo (by omega_using [ho]))
      (by rw [eD]; exact hstk))

/-- The instructions before `absorbFixed`'s call, from `esp` and `ebx` public. -/
abbrev FixedCheck (offset size : Nat) : Prop :=
  ∃ hc, (VG.Taint.check taint (τr [.esp, .ebx]) (.block [.mov .ecx (.imm 0), .mov .edx (.imm 0),
      .mov .esi (.reg .ebx), .alu .add .esi (.imm (BitVec.ofNat 32 offset)),
      .mov .edi (.imm (BitVec.ofNat 32 size))]) hc).isSome = true

theorem fixed_check_768 : FixedCheck 768 64 := ⟨_, by taint_decide⟩
theorem fixed_check_832 : FixedCheck 832 4 := ⟨_, by taint_decide⟩

/-- `next`, from the context and the digest length in `edx`. -/
theorem next_rel {B E : BitVec 32} {n : Nat} (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) :
    RelCT isa (fun s₁ s₂ => InitIn B E n s₁ ∧ InitIn B E n s₂) next fun _ _ => True := by
  have st : ∀ s, InitIn B E n s → WP isa init s fun t =>
      Repr b (Spec.Blake2.init b n 0) t.mem (B.setWidth 64) [] ∧ Ctx B E t := fun s ⟨c, e⟩ =>
    (init_ok c e hn₁ hn₂).mono fun t ⟨r, cs, _, wr, _⟩ =>
      ⟨r, c.of_regs (cs _ (by decide)) (cs _ (by decide)) wr⟩
  have fx : ∀ s, Repr b (Spec.Blake2.init b n 0) s.mem (B.setWidth 64) [] ∧ Ctx B E s →
      WP isa (absorbFixed 768 64) s fun t => Ctx B E t := fun s ⟨r, c⟩ =>
    (absorbFixed_ok c (offset := 768) (size := 64) (by have := c.fits; omega_using [this]) (by decide) (by decide)
      (c.cov (by decide)) (c.stk_sub (by decide) (by decide)) r).mono fun t ⟨_, k⟩ => k.ctx c
  have fin : ∀ s, Ctx B E s → WP isa (.block [.mov .ecx (.imm 64), .mov .edx (.imm 0)]) s
      (FinalizeIn B E 64 0) := fun s c =>
    wp_movi fun s₁ u₁ => wp_movi fun s₂ u₂ => WP.block_nil
      ⟨c.of_regs (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
        (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]) (by rw [u₂.wr, u₁.wr]),
       by rw [u₂.other _ (by decide), u₁.gpr], u₂.gpr⟩
  unfold next
  refine RelCT.seq (rel_wp (init_rel hn₁ hn₂) st st)
    (RelCT.seq (R := fun s₁ s₂ => Ctx B E s₁ ∧ Ctx B E s₂) ?_
      (RelCT.seq (R := fun s₁ s₂ => FinalizeIn B E 64 0 s₁ ∧ FinalizeIn B E 64 0 s₂) ?_ finalize_rel))
  · refine rel_wp (RelCT.of_pre fun s₁ _ ⟨⟨_, c₁⟩, _⟩ =>
      (absorbFixed_rel (B := B) (E := E) (offset := 768) (size := 64) (by have := c₁.fits; omega_using [this])
        (by decide) (by decide) (c₁.stk_sub (by decide) (by decide)) fixed_check_768).mono
      (fun s₁ s₂ ⟨⟨_, c₁⟩, ⟨_, c₂⟩⟩ => ⟨⟨c₁, c₁.cov (by decide)⟩, ⟨c₂, c₂.cov (by decide)⟩⟩)
      fun _ _ h => h) fx fx
  · exact rel_taint [.esp, .ebx] (fun s₁ s₂ c₁ c₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [c₁.esp, c₂.esp]
      · rw [c₁.ebx, c₂.ebx]) ⟨_, by taint_decide⟩ fin fin

end VG.Proof.Argon2.X86.HPrime

end

end

@[expose] public section

section

/-!
# Argon2 H′ on x86 (32-bit): the output, in two runs

Two runs of H′ with the same public data (`Same`: the stack pointer and the
arguments) write their output through the same addresses: `copy_rel`,
`emit_rel` and `copyRemaining_rel`, from states with the same number of
output bytes written.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (copy emitPrefix copyRemaining outOff leftOff)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_movi wp_mov wp_addi wp_movm contains_addr)

/-- The public data of two runs. -/
structure Same (s₀ s₀' : State) : Prop where
  esp : esp₀ s₀' = esp₀ s₀
  args : ∀ i < 5, arg s₀' i = arg s₀ i

theorem Same.of_pub {s₀ s₀' : State} (h : hPrimeX86.pub s₀ s₀') : Same s₀ s₀' :=
  ⟨h.1.symm, fun i hi => (h.2 i hi).symm⟩

section
variable {s₀ s₀' : State} (q : Same s₀ s₀')
include q

theorem Same.scr_eq : scr s₀' = scr s₀ := q.args 4 (by decide)
theorem Same.op_eq : op s₀' = op s₀ := q.args 2 (by decide)
theorem Same.ol_eq : ol s₀' = ol s₀ := by
  show (arg s₀' 3).toNat = (arg s₀ 3).toNat; rw [q.args 3 (by decide)]
theorem Same.inp_eq : inp s₀' = inp s₀ := q.args 0 (by decide)
theorem Same.inl_eq : inl s₀' = inl s₀ := by
  show (arg s₀' 1).toNat = (arg s₀ 1).toNat; rw [q.args 1 (by decide)]

end

/-! ## `copy` -/

/-- What `copy` needs: the body, `k` bytes of output written, and `n` to copy. -/
def CopyIn (s₀ : State) (k n : Nat) (s : State) : Prop :=
  Body s₀ s ∧ OutPtr s₀ s k ∧ s.gpr .esi = BitVec.ofNat 32 n

/-- The registers after `copy`'s first instructions. -/
def CopyRegs (s₀ : State) (k n : Nat) (t : State) : Prop :=
  t.gpr .esp = esp₀ s₀ ∧ t.gpr .ebx = scr s₀ ∧ t.gpr .edx = scr s₀ + 768 ∧
    t.gpr .edi = op s₀ + BitVec.ofNat 32 k ∧ t.gpr .esi = BitVec.ofNat 32 n

theorem copy_blk {s₀ : State} (hp : Pre s₀) {k n : Nat} {s : State} (h : CopyIn s₀ k n s) :
    WP isa (.block [.mov .edx (.reg .ebx), .alu .add .edx (.imm 768), .mov .edi (.mem (VG.Impl.Sha512.X86.at_ .ebx outOff))])
      s (CopyRegs s₀ k n) := by
  obtain ⟨b, hk, hn⟩ := h
  have hs := hp.scr_fits
  refine wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => wp_movm
    (VG.Proof.Sha512.X86.ea_of (B := scr s₀) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), b.ebx])
      outOff)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, b.rd, b.wr]
        exact ⟨scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩)
    fun s₃ u₃ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), b.esp]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), b.ebx]
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, b.ebx]
  · rw [u₃.gpr, u₂.mem, u₁.mem]; exact hk
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hn]

theorem copy_rel {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (q : Same s₀ s₀') {k n : Nat} :
    RelCT isa (fun t₁ t₂ => CopyIn s₀ k n t₁ ∧ CopyIn s₀' k n t₂) copy fun _ _ => True := by
  unfold copy
  refine RelCT.seq (rel_taint [.ebx] (fun _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [h₁.1.ebx, h₂.1.ebx, q.scr_eq]) ⟨_, by taint_decide⟩
    (fun s h => copy_blk hp h) (fun s h => copy_blk hp' h)) ?_
  exact RelCT.taint (A := taint) (τr [.esp, .ebx, .edx, .edi, .esi])
    (fun t₁ t₂ ⟨⟨a₁, b₁, c₁, d₁, e₁⟩, ⟨a₂, b₂, c₂, d₂, e₂⟩⟩ => agree_regs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [a₁, a₂, q.esp]
      · rw [b₁, b₂, q.scr_eq]
      · rw [c₁, c₂, q.scr_eq]
      · rw [d₁, d₂, q.op_eq]
      · rw [e₁, e₂]) (by taint_decide)

/-- Steps that keep memory, the permissions, `ebx` and `esp` keep the body. -/
theorem Body.same {s₀ s t : State} (b : Body s₀ s) (hb : t.gpr .ebx = s.gpr .ebx)
    (he : t.gpr .esp = s.gpr .esp) (hm : t.mem = s.mem) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) :
    Body s₀ t :=
  ⟨hb.trans b.ebx, he.trans b.esp, hrd.trans b.rd, hwr.trans b.wr, hm ▸ b.frame,
    fun q hq => hm ▸ b.saved q hq, hm ▸ b.pfx⟩

/-- The body, with `L` output bytes written. -/
def OutAt (s₀ : State) (L : Nat) (s : State) : Prop :=
  Body s₀ s ∧ ∃ xs, Out s₀ s xs ∧ xs.length = L

theorem emit_blk {s₀ : State} {L : Nat} {s : State} (h : OutAt s₀ L s) :
    WP isa (.block [.mov .esi (.imm 32)]) s (CopyIn s₀ L 32) := by
  obtain ⟨b, xs, o, hx⟩ := h
  refine wp_movi fun s₁ u₁ => WP.block_nil ⟨b.same (u₁.other _ (by decide)) (u₁.other _ (by decide))
    u₁.mem u₁.rd u₁.wr, ?_, u₁.gpr⟩
  show _ = _; rw [u₁.mem, ← hx]; exact o.ptr

theorem emit_rel {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (q : Same s₀ s₀') {L : Nat}
    (hL : L + 32 ≤ ol s₀) :
    RelCT isa (fun t₁ t₂ => OutAt s₀ L t₁ ∧ OutAt s₀' L t₂) emitPrefix fun _ _ => True := by
  have hL' : L + 32 ≤ ol s₀' := by rw [q.ol_eq]; exact hL
  have cp : ∀ {s₀ : State}, Pre s₀ → L + 32 ≤ ol s₀ → ∀ s, CopyIn s₀ L 32 s → WP isa copy s (Body s₀) :=
    fun hp hL s ⟨b, k, n⟩ => (copy_ok hp b k n (by decide) (by decide) hL).mono fun _ h => h.1
  unfold emitPrefix
  refine RelCT.seq (rel_taint [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
    (fun _ h => emit_blk h) (fun _ h => emit_blk h))
    (RelCT.seq (rel_wp (copy_rel hp hp' q) (cp hp hL) (cp hp' hL')) ?_)
  exact RelCT.taint (A := taint) (τr [.esp, .ebx])
    (fun t₁ t₂ ⟨b₁, b₂⟩ => agree_regs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [b₁.esp, b₂.esp, q.esp]
      · rw [b₁.ebx, b₂.ebx, q.scr_eq]) (by taint_decide)

theorem rem_blk {s₀ : State} (hp : Pre s₀) {L : Nat} {s : State} (h : OutAt s₀ L s) :
    WP isa (.block [.mov .esi (.mem (VG.Impl.Sha512.X86.at_ .ebx leftOff))]) s
      (CopyIn s₀ L (ol s₀ - L)) := by
  obtain ⟨b, xs, o, hx⟩ := h
  have hs := hp.scr_fits
  refine wp_movm (VG.Proof.Sha512.X86.ea_of b.ebx leftOff)
    (by rw [b.rd, b.wr]; exact ⟨scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩)
    fun s₁ u₁ => WP.block_nil ⟨b.same (u₁.other _ (by decide)) (u₁.other _ (by decide))
      u₁.mem u₁.rd u₁.wr, ?_, ?_⟩
  · show _ = _; rw [u₁.mem, ← hx]; exact o.ptr
  · rw [u₁.gpr, o.left, hx]

theorem copyRemaining_rel {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (q : Same s₀ s₀') {L : Nat} :
    RelCT isa (fun t₁ t₂ => OutAt s₀ L t₁ ∧ OutAt s₀' L t₂) copyRemaining fun _ _ => True := by
  unfold copyRemaining
  refine RelCT.seq (rel_taint [.ebx] (fun _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [h₁.1.ebx, h₂.1.ebx, q.scr_eq]) ⟨_, by taint_decide⟩
    (fun _ h => rem_blk hp h) (fun _ h => rem_blk hp' h)) ?_
  rw [q.ol_eq]
  exact copy_rel hp hp' q

end VG.Proof.Argon2.X86.HPrime

end

/-!
# Argon2 H′ on x86 (32-bit): the output from the first digest, in two runs

`finishOutput_rel`: two runs with the same public data take the same
branches (the output length decides them) and the same number of chain
iterations, and write the output through the same addresses.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (next emitPrefix cmpLeft chain extendDigest finishOutput copyRemaining
  leftOff)
open VG.Proof.Sha256.X86.Stream (Upd wp_movi wp_movm contains_addr)
open VG.Proof.Argon2 (chainDigest chainPrefixes)

/-- `ChainInv`, for some digest `V`. -/
def ChainAt (s₀ : State) (e : BitVec 32) (j : Nat) (s : State) : Prop :=
  ∃ V : List Byte, V.length = 64 ∧ ChainInv s₀ e V j s

theorem ChainAt.outAt {s₀ : State} {e : BitVec 32} {j : Nat} {s : State} (h : ChainAt s₀ e j s) :
    OutAt s₀ (32 + 32 * j) s :=
  let ⟨_, hV, i⟩ := h
  ⟨i.body, _, i.out, chainOut_length hV j⟩

theorem cf_true {t : State} {p : Prop} [Decidable p] (h : t.cf = some (decide p))
    (e : isa.eval .b t = some true) : p := by
  have e' : t.cf = some true := e
  rw [h] at e'; simpa using e'

theorem cf_false {t : State} {p : Prop} [Decidable p] (h : t.cf = some (decide p))
    (e : isa.eval .b t = some false) : ¬ p := by
  have e' : t.cf = some false := e
  rw [h] at e'; simpa using e'

/-- The two runs agree on `esp` and `ebx`. -/
theorem agree_body {s₀ s₀' : State} (q : Same s₀ s₀') {t₁ t₂ : State} (b₁ : Body s₀ t₁)
    (b₂ : Body s₀' t₂) : ∀ r ∈ [Reg.esp, .ebx], t₁.gpr r = t₂.gpr r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [b₁.esp, b₂.esp, q.esp]
  · rw [b₁.ebx, b₂.ebx, q.scr_eq]

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (q : Same s₀ s₀')

/-! ## `next`, keeping the output -/

include hp in
theorem next_out_ok {n L : Nat} (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) {s : State}
    (h : InitIn (scr s₀) (esp₀ s₀) n s ∧ OutAt s₀ L s) : WP isa next s (OutAt s₀ L) := by
  obtain ⟨⟨c, e⟩, b, xs, o, hx⟩ := h
  exact (next_ok c e hn₁ hn₂).mono fun t ⟨_, k⟩ => ⟨b.keeps hp k, xs, o.keeps hp k, hx⟩

include hp hp' q in
theorem next_out_rel {n L : Nat} (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) :
    RelCT isa (fun t₁ t₂ => (InitIn (scr s₀) (esp₀ s₀) n t₁ ∧ OutAt s₀ L t₁) ∧
      (InitIn (scr s₀) (esp₀ s₀) n t₂ ∧ OutAt s₀' L t₂)) next
      fun t₁ t₂ => OutAt s₀ L t₁ ∧ OutAt s₀' L t₂ :=
  rel_wp ((next_rel hn₁ hn₂).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h)
    (fun _ h => next_out_ok hp hn₁ hn₂ h)
    (fun _ h => next_out_ok hp' hn₁ hn₂ ⟨by rw [q.scr_eq, q.esp]; exact h.1, h.2⟩)

/-! ## The chain -/

include hp in
/-- Setting `edx` keeps the body and the output. -/
theorem edx_blk {L n : Nat} {s : State} (h : OutAt s₀ L s) :
    WP isa (.block [.mov .edx (.imm (BitVec.ofNat 32 n))]) s fun t =>
      InitIn (scr s₀) (esp₀ s₀) n t ∧ OutAt s₀ L t := by
  obtain ⟨b, xs, o, hx⟩ := h
  refine wp_movi fun s₁ u₁ => WP.block_nil ?_
  have b₁ := b.same (u₁.other _ (by decide)) (u₁.other _ (by decide)) u₁.mem u₁.rd u₁.wr
  exact ⟨⟨b₁.ctx hp, u₁.gpr⟩, b₁, xs, o.same u₁.mem, hx⟩

include hp in
theorem emit_body {L : Nat} (hL : L + 32 ≤ ol s₀) {s : State} (h : OutAt s₀ L s) :
    WP isa emitPrefix s (Body s₀) := by
  obtain ⟨b, xs, o, hx⟩ := h
  exact (emit_ok hp b o (by rw [hx]; exact hL)).mono fun _ h => h.1

include hp hp' q in
/-- One iteration of the chain. -/
theorem body_rel {j : Nat} (hl : 32 + 32 * j + 32 ≤ ol s₀) {e e' : BitVec 32} :
    RelCT isa (fun t₁ t₂ => ChainAt s₀ e j t₁ ∧ ChainAt s₀' e' j t₂)
      (.seq (.block [.mov .edx (.imm 64)]) (.seq next (.seq emitPrefix (.block cmpLeft))))
      fun _ _ => True := by
  have hl' : 32 + 32 * j + 32 ≤ ol s₀' := by rw [q.ol_eq]; exact hl
  refine RelCT.seq (rel_taint [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
    (fun _ h => edx_blk (n := 64) hp h.outAt)
    (fun _ h => (edx_blk (n := 64) hp' h.outAt).mono fun _ h => ⟨by rw [← q.scr_eq, ← q.esp]; exact h.1, h.2⟩))
    (RelCT.seq (next_out_rel hp hp' q (by decide) (by decide))
      (RelCT.seq (rel_wp (emit_rel hp hp' q hl) (fun _ h => emit_body hp hl h)
        (fun _ h => emit_body hp' hl' h)) ?_))
  exact RelCT.taint (A := taint) (τr [.esp, .ebx])
    (fun _ _ h => agree_regs (agree_body q h.1 h.2)) (by taint_decide)

/-- What the chain leaves: `j` iterations, and 33 to 64 bytes left. -/
def ChainDone (s₀ s₀' : State) (e e' : BitVec 32) (t₁ t₂ : State) : Prop :=
  ∃ j, ChainAt s₀ e j t₁ ∧ ChainAt s₀' e' j t₂ ∧ 33 ≤ ol s₀ - (32 + 32 * j) ∧
    ol s₀ - (32 + 32 * j) ≤ 64 ∧ 32 + 32 * j ≤ ol s₀

include hp hp' q in
theorem chain_rel {e e' : BitVec 32} :
    RelCT isa (fun t₁ t₂ => ∃ j, 65 ≤ ol s₀ - (32 + 32 * j) ∧ ChainAt s₀ e j t₁ ∧ ChainAt s₀' e' j t₂)
      chain (ChainDone s₀ s₀' e e') := by
  have ho := q.ol_eq
  refine fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨j, h65, h₁, h₂⟩ e₁ e₂ =>
    RelCT.loop (M := isa) (Q := ChainDone s₀ s₀' e e')
      (fun m t₁ t₂ => ∃ j, m = ol s₀ - (32 + 32 * j) ∧ 65 ≤ m ∧ ChainAt s₀ e j t₁ ∧ ChainAt s₀' e' j t₂)
      (fun m => ?_) _ s₁ s₂ t₁ t₂ s₁' s₂' ⟨j, rfl, h65, h₁, h₂⟩ e₁ e₂
  refine RelCT.of_pre fun _ _ ⟨j, hm, h65, _, _⟩ => ?_
  subst hm
  have it := (body_rel hp hp' q (j := j) (by omega_arith) (e := e) (e' := e')).wp
    (F₁ := fun (t : State) => ChainAt s₀ e (j + 1) t ∧ t.cf = some (decide (ol s₀ - (32 + 32 * (j + 1)) < 65)))
    (F₂ := fun (t : State) => ChainAt s₀' e' (j + 1) t ∧ t.cf = some (decide (ol s₀' - (32 + 32 * (j + 1)) < 65)))
    fun t₁ t₂ ⟨⟨V, hV, i₁⟩, ⟨V', hV', i₂⟩⟩ =>
      ⟨(iter_ok hp hV i₁ (by omega_arith)).mono fun _ h => ⟨⟨V, hV, h.1⟩, h.2⟩,
       (iter_ok hp' hV' i₂ (by omega_arith)).mono fun _ h => ⟨⟨V', hV', h.1⟩, h.2⟩⟩
  refine it.mono (fun t₁ t₂ ⟨j', hj, _, a₁, a₂⟩ => ?_) fun t₁ t₂ ⟨_, ⟨c₁, f₁⟩, ⟨c₂, f₂⟩⟩ => ?_
  · have : j' = j := by omega_arith
    subst this; exact ⟨a₁, a₂⟩
  · rw [ho] at f₂
    have ev : isa.eval .ae t₁ = isa.eval .ae t₂ := by
      show t₁.cf.map (!·) = t₂.cf.map (!·); rw [f₁, f₂]
    refine ⟨ev, fun hf => ?_, fun ht => ?_⟩
    · have : ol s₀ - (32 + 32 * (j + 1)) < 65 := by
        have hf' : t₁.cf.map (!·) = some false := hf
        rw [f₁] at hf'; simpa using hf'
      exact ⟨j + 1, c₁, c₂, by omega_arith, by omega_arith, by omega_arith⟩
    · have : ¬ ol s₀ - (32 + 32 * (j + 1)) < 65 := by
        have ht' : t₁.cf.map (!·) = some true := ht
        rw [f₁] at ht'; simpa using ht'
      exact ⟨_, by omega_arith, j + 1, rfl, by omega_arith, c₁, c₂⟩

/-! ## Extending the digest -/

/-- The state `finishOutput` starts from. -/
def ExtIn (s₀ s : State) : Prop := Body s₀ s ∧ Out s₀ s [] ∧ s.gpr .ebp = s₀.gpr .ebp

include hp in
theorem ext_emit {s : State} (h : ExtIn s₀ s) (hol : 32 ≤ ol s₀) :
    WP isa emitPrefix s (ChainAt s₀ (s₀.gpr .ebp) 0) := by
  obtain ⟨b, o, e⟩ := h
  refine (emit_ok hp b o (by simp only [List.length_nil]; omega_arith)).mono fun t ⟨bt, et, ot, dt⟩ =>
    ⟨digest s₀ s, by simp [digest, bytesAt], bt, et.trans e, ?_, ?_⟩
  · rw [List.nil_append] at ot
    simpa [chainOut, chainPrefixes] using ot
  · exact dt

include hp in
theorem ChainAt.keeps {e : BitVec 32} {j : Nat} {s t : State} (h : ChainAt s₀ e j s)
    (k : Keeps (scr s₀) (esp₀ s₀) s t) (m : t.mem = s.mem) : ChainAt s₀ e j t :=
  let ⟨V, hV, i⟩ := h
  ⟨V, hV, i.body.keeps hp k, k.ebp.trans i.ebp, i.out.keeps hp k,
    by show bytesAt _ _ _ = _; rw [m]; exact i.digest⟩

include hp in
theorem chain_cmp {e : BitVec 32} {j : Nat} {s : State} (h : ChainAt s₀ e j s) :
    WP isa (.block cmpLeft) s fun t => ChainAt s₀ e j t ∧
      t.cf = some (decide (ol s₀ - (32 + 32 * j) < 65)) := by
  obtain ⟨V, hV, i⟩ := h
  refine (cmp_ok hp i.body i.out).mono fun t ⟨cf, k, m⟩ => ⟨ChainAt.keeps hp ⟨V, hV, i⟩ k m, ?_⟩
  rw [cf, chainOut_length hV]

include hp in
theorem left_blk {e : BitVec 32} {j : Nat} {s : State} (h : ChainAt s₀ e j s) :
    WP isa (.block [.mov .edx (.mem (VG.Impl.Sha512.X86.at_ .ebx leftOff))]) s fun t =>
      InitIn (scr s₀) (esp₀ s₀) (ol s₀ - (32 + 32 * j)) t ∧ OutAt s₀ (32 + 32 * j) t := by
  obtain ⟨b, xs, o, hx⟩ := h.outAt
  have hs := hp.scr_fits
  refine wp_movm (VG.Proof.Sha512.X86.ea_of b.ebx leftOff)
    (by rw [b.rd, b.wr]; exact ⟨scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩)
    fun s₁ u₁ => WP.block_nil ?_
  have b₁ := b.same (u₁.other _ (by decide)) (u₁.other _ (by decide)) u₁.mem u₁.rd u₁.wr
  exact ⟨⟨b₁.ctx hp, by rw [u₁.gpr, o.left, hx]⟩, b₁, xs, o.same u₁.mem, hx⟩

/-- `L` bytes written, and at most 64 left. -/
def Last (s₀ s₀' : State) (t₁ t₂ : State) : Prop :=
  ∃ L, OutAt s₀ L t₁ ∧ OutAt s₀' L t₂ ∧ L < ol s₀ ∧ ol s₀ - L ≤ 64

include hp hp' q in
theorem last_rel {e e' : BitVec 32} :
    RelCT isa (ChainDone s₀ s₀' e e')
      (.seq (.block [.mov .edx (.mem (VG.Impl.Sha512.X86.at_ .ebx leftOff))]) next) (Last s₀ s₀') := by
  have ho := q.ol_eq
  refine RelCT.of_pre fun _ _ ⟨j, _, _, l₁, l₂, l₃⟩ => ?_
  refine (RelCT.seq (rel_taint [.ebx] (F₁ := ChainAt s₀ e j) (F₂ := ChainAt s₀' e' j)
      (fun _ _ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
        obtain ⟨_, _, i₁⟩ := h₁; obtain ⟨_, _, i₂⟩ := h₂
        rw [i₁.body.ebx, i₂.body.ebx, q.scr_eq]) ⟨_, by taint_decide⟩
      (fun _ h => left_blk hp h)
      (fun _ h => (left_blk hp' h).mono fun _ h => ⟨by rw [← q.scr_eq, ← q.esp, ← ho]; exact h.1, h.2⟩))
    (next_out_rel hp hp' q (n := ol s₀ - (32 + 32 * j)) (by omega_arith) l₂)).mono ?_ ?_
  · intro t₁ t₂ ⟨j', c₁, c₂, m₁, m₂, m₃⟩
    have : j' = j := by omega_arith
    subst this; exact ⟨c₁, c₂⟩
  · intro t₁ t₂ ⟨o₁, o₂⟩
    exact ⟨_, o₁, o₂, by omega_arith, by omega_arith⟩

include hp hp' q in
theorem extend_rel (hol : 65 ≤ ol s₀) :
    RelCT isa (fun t₁ t₂ => ExtIn s₀ t₁ ∧ ExtIn s₀' t₂) extendDigest (Last s₀ s₀') := by
  have ho := q.ol_eq
  have hol' : 65 ≤ ol s₀' := by rw [ho]; exact hol
  unfold extendDigest
  refine RelCT.seq (rel_wp ((emit_rel hp hp' q (L := 0) (by omega_arith)).mono
      (fun _ _ ⟨⟨b₁, o₁, _⟩, ⟨b₂, o₂, _⟩⟩ => ⟨⟨b₁, [], o₁, rfl⟩, ⟨b₂, [], o₂, rfl⟩⟩) fun _ _ h => h)
      (fun _ h => ext_emit hp h (by omega_arith)) (fun _ h => ext_emit hp' h (by omega_arith))) ?_
  refine RelCT.seq (rel_taint [.esp, .ebx] (fun _ _ ⟨_, _, i₁⟩ ⟨_, _, i₂⟩ => agree_body q i₁.body i₂.body)
    ⟨_, by taint_decide⟩ (fun _ h => chain_cmp hp h) (fun _ h => chain_cmp hp' h)) ?_
  refine RelCT.seq (RelCT.ite (fun t₁ t₂ ⟨⟨_, f₁⟩, ⟨_, f₂⟩⟩ => by
      show t₁.cf = t₂.cf; rw [f₁, f₂, ho])
    (RelCT.nil fun _ _ ⟨⟨⟨c₁, f₁⟩, ⟨c₂, _⟩⟩, ht⟩ => ⟨0, c₁, c₂, by have := cf_true f₁ ht; omega_arith⟩)
    ((chain_rel hp hp' q).mono (fun _ _ ⟨⟨⟨c₁, f₁⟩, ⟨c₂, _⟩⟩, hf⟩ =>
      ⟨0, by have := cf_false f₁ hf; omega_arith, c₁, c₂⟩) fun _ _ h => h))
    (last_rel hp hp' q)


include hp in
theorem ext_cmp {s : State} (h : ExtIn s₀ s) :
    WP isa (.block cmpLeft) s fun t => ExtIn s₀ t ∧ t.cf = some (decide (ol s₀ < 65)) := by
  obtain ⟨b, o, e⟩ := h
  refine (cmp_ok hp b o).mono fun t ⟨cf, k, _⟩ => ⟨⟨b.keeps hp k, o.keeps hp k, k.ebp.trans e⟩, ?_⟩
  rw [cf]; simp

include hp hp' q in
theorem finishOutput_rel :
    RelCT isa (fun t₁ t₂ => ExtIn s₀ t₁ ∧ ExtIn s₀' t₂) finishOutput fun _ _ => True := by
  have ho := q.ol_eq
  have hpos := hp.ol_pos
  unfold finishOutput
  refine RelCT.seq (rel_taint [.esp, .ebx] (fun _ _ ⟨b₁, _⟩ ⟨b₂, _⟩ => agree_body q b₁ b₂)
    ⟨_, by taint_decide⟩ (fun _ h => ext_cmp hp h) (fun _ h => ext_cmp hp' h)) ?_
  refine RelCT.seq (R := Last s₀ s₀') (RelCT.ite (fun t₁ t₂ ⟨⟨_, f₁⟩, ⟨_, f₂⟩⟩ => by
      show t₁.cf = t₂.cf; rw [f₁, f₂, ho])
    (RelCT.nil fun _ _ ⟨⟨⟨⟨b₁, o₁, _⟩, f₁⟩, ⟨⟨b₂, o₂, _⟩, _⟩⟩, ht⟩ =>
      ⟨0, ⟨b₁, [], o₁, rfl⟩, ⟨b₂, [], o₂, rfl⟩, by have := cf_true f₁ ht; omega_arith,
        by have := cf_true f₁ ht; omega_arith⟩)
    (RelCT.of_pre fun _ _ ⟨⟨⟨_, f₁⟩, _⟩, hf⟩ => (extend_rel hp hp' q (by have := cf_false f₁ hf; omega_arith)).mono
      (fun _ _ ⟨⟨⟨e₁, _⟩, ⟨e₂, _⟩⟩, _⟩ => ⟨e₁, e₂⟩) fun _ _ h => h)) ?_
  exact RelCT.mono (RelCT.exists_ fun L => (copyRemaining_rel hp hp' q (L := L)).mono
    (fun _ _ h => ⟨h.1, h.2.1⟩) fun _ _ h => h) (fun _ _ ⟨L, h⟩ => ⟨L, h⟩) fun _ _ h => h


end

end VG.Proof.Argon2.X86.HPrime

end

end

@[expose] public section

section

/-!
# Argon2 H′ on x86 (32-bit): correctness

`setup_ok` saves the caller's registers and lays out the output pointer, the
bytes left and the length prefix in `scratch`; `correct` composes it with
`first_ok`, `finish_ok` and the restore of the registers.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (setup restore first finishOutput saved outOff leftOff)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_mov wp_movm wp_store readW_writeW_addr contains_addr)
open VG.Proof.Sha512.X86 (ea_of)

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem arg_in_rd {s : State} (hrd : s.rd = s₀.rd) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) (4 + 4 * i)) 4 := by
  refine ⟨argR s₀, by simp [hrd, hp.rd], ?_⟩
  show Region.Contains ⟨addr (esp₀ s₀) (4 + 4 * 0), 20⟩ _ _
  rw [arg_addr hp hi, arg_addr hp (by decide)]
  exact Offset.contains _ (by omega_using []) (by omega_using [hi]) (by omega_using [])

theorem arg_frame {m : Mem} (f : Frame [scrR s₀] s₀.mem m) {i : Nat} (hi : i < 5) :
    m.readW (addr (esp₀ s₀) (4 + 4 * i)) 32 = arg s₀ i := by
  refine f.readW (r := ⟨addr (esp₀ s₀) (4 + 4 * i), 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact hp.arg_scr.sub_left (arg_sub hp hi)

theorem scr_in {s : State} (hwr : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 16384) :
    InRegions s.wr (addr (scr s₀) d) 4 := by
  rw [hwr, hp.wr]
  exact ⟨scrR s₀, by simp, contains_addr hd (by decide) hp.scr_fits⟩

theorem scr_frame {m : Mem} (f : Frame [scrR s₀] s₀.mem m) {d : Nat} (hd : d + 4 ≤ 16384)
    (v : BitVec 32) : Frame [scrR s₀] s₀.mem (m.writeW (addr (scr s₀) d) v) :=
  f.writeW (List.mem_singleton_self _) v (contains_addr hd (by decide) hp.scr_fits)

/-- The state after `setup`. -/
theorem setup_ok : WP isa (.block setup) s₀ fun t => Body s₀ t ∧ Out s₀ t [] ∧
    t.gpr .ebp = s₀.gpr .ebp ∧ Frame [scrR s₀] s₀.mem t.mem := by
  have hs := hp.scr_fits
  have esp : s₀.gpr .esp = esp₀ s₀ := rfl
  unfold setup
  simp only [saved, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  refine wp_movm (ea_of esp 20) (arg_in_rd hp (i := 4) rfl (by decide)) fun t₁ u₁ => ?_
  have a₁ : t₁.gpr .eax = scr s₀ := u₁.gpr
  refine wp_store (ea_of a₁ 840) (scr_in hp u₁.wr (by decide)) fun t₂ u₂ => ?_
  obtain a₂ : t₂.gpr .eax = scr s₀ := by rw [u₂.gpr, a₁]
  refine wp_store (ea_of a₂ 844) (scr_in hp (by rw [u₂.wr, u₁.wr]) (by decide)) fun t₃ u₃ => ?_
  obtain a₃ : t₃.gpr .eax = scr s₀ := by rw [u₃.gpr, a₂]
  refine wp_store (ea_of a₃ 848) (scr_in hp (by rw [u₃.wr, u₂.wr, u₁.wr]) (by decide)) fun t₄ u₄ => ?_
  refine wp_mov fun t₅ u₅ => ?_
  obtain b₅ : t₅.gpr .ebx = scr s₀ := by rw [u₅.gpr, u₄.gpr, a₃]
  obtain g₅ : ∀ r, r ≠ .ebx → r ≠ .eax → t₅.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [u₅.other _ h1, u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ h2]
  obtain rd₅ : t₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain wr₅ : t₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  obtain F₅ : Frame [scrR s₀] s₀.mem t₅.mem := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
    exact scr_frame hp (scr_frame hp (scr_frame hp (by rw [u₁.mem]; exact Frame.refl _ _) (by decide) _)
      (by decide) _) (by decide) _
  refine wp_movm (ea_of (by rw [g₅ _ (by decide) (by decide)]) 12)
    (arg_in_rd hp (i := 2) (by rw [rd₅]) (by decide)) fun t₆ u₆ => ?_
  refine wp_store (ea_of (by rw [u₆.other _ (by decide), b₅]) outOff)
    (scr_in hp (by rw [u₆.wr, wr₅]) (by decide)) fun t₇ u₇ => ?_
  refine wp_movm (ea_of (by rw [u₇.gpr, u₆.other _ (by decide), g₅ _ (by decide) (by decide)]) 16)
    (arg_in_rd hp (i := 3) (by rw [u₇.rd, u₆.rd, rd₅]) (by decide)) fun t₈ u₈ => ?_
  refine wp_store (ea_of (by rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), b₅]) leftOff)
    (scr_in hp (by rw [u₈.wr, u₇.wr, u₆.wr, wr₅]) (by decide)) fun t₉ u₉ => ?_
  refine wp_store (ea_of (by rw [u₉.gpr, u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), b₅]) 832)
    (scr_in hp (by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅]) (by decide)) fun t u => WP.block_nil ?_
  -- Values.
  obtain v₆ : t₆.gpr .eax = op s₀ := by rw [u₆.gpr, arg_frame hp F₅ (i := 2) (by decide)]
  obtain F₇ : Frame [scrR s₀] s₀.mem t₇.mem := by
    rw [u₇.mem, u₆.mem]; exact scr_frame hp F₅ (by decide) _
  obtain v₈ : t₈.gpr .eax = arg s₀ 3 := by rw [u₈.gpr, arg_frame hp F₇ (i := 3) (by decide)]
  obtain rds : t.rd = s₀.rd := by rw [u.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, rd₅]
  obtain wrs : t.wr = s₀.wr := by rw [u.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅]
  obtain gt : ∀ r, r ≠ .ebx → r ≠ .eax → t.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [u.gpr, u₉.gpr, u₈.other _ h2, u₇.gpr, u₆.other _ h2, g₅ _ h1 h2]
  obtain bt : t.gpr .ebx = scr s₀ := by
    rw [u.gpr, u₉.gpr, u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), b₅]
  obtain m₉ : t₉.mem = (t₇.mem.writeW (addr (scr s₀) leftOff) (arg s₀ 3)) := by
    rw [u₉.mem, u₈.mem, v₈]
  obtain mt : t.mem = (t₇.mem.writeW (addr (scr s₀) leftOff) (arg s₀ 3)).writeW (addr (scr s₀) 832)
      (arg s₀ 3) := by
    rw [u.mem, m₉, u₉.gpr, v₈]
  obtain m₇ : t₇.mem = t₅.mem.writeW (addr (scr s₀) outOff) (op s₀) := by
    rw [u₇.mem, u₆.mem, v₆]
  obtain Ft : Frame [scrR s₀] s₀.mem t.mem := by
    rw [mt]; exact scr_frame hp (scr_frame hp F₇ (by decide) _) (by decide) _
  -- Reads of `scratch` after the last writes.
  obtain R : ∀ (m : Mem) (v : BitVec 32) (d e : Nat), d + 4 ≤ 16384 → e + 4 ≤ 16384 →
      (d + 4 ≤ e ∨ e + 4 ≤ d) →
      (m.writeW (addr (scr s₀) e) v).readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 :=
    fun m v d e hd he h => readW_writeW_addr m v (by omega_using [hs, hd]) (by omega_using [hs, he]) h
  obtain keep7 : ∀ d, d + 4 ≤ 16384 → (d + 4 ≤ 832 ∨ 864 ≤ d ∨ (836 ≤ d ∧ d + 4 ≤ 856)) →
      t.mem.readW (addr (scr s₀) d) 32 = t₅.mem.readW (addr (scr s₀) d) 32 := fun d hd h => by
    rw [mt, R _ _ d 832 hd (by decide) (by omega_using [h]), R _ _ d leftOff hd (by decide) (by simp only [leftOff]; omega_using [h]),
      m₇, R _ _ d outOff hd (by decide) (by simp only [outOff]; omega_using [h])]
  obtain m₅ : t₅.mem = ((s₀.mem.writeW (addr (scr s₀) 840) (s₀.gpr .ebx)).writeW (addr (scr s₀) 844)
      (s₀.gpr .esi)).writeW (addr (scr s₀) 848) (s₀.gpr .edi) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.gpr, u₁.other .ebx (by decide),
      u₁.other .esi (by decide), u₁.other .edi (by decide)]
  refine ⟨⟨bt, by rw [gt _ (by decide) (by decide)], rds, wrs,
      Ft.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩, fun q hq => ?_, ?_⟩,
    ⟨?_, ?_, rfl, Nat.zero_le _⟩, gt _ (by decide) (by decide), Ft⟩
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · rw [keep7 _ (by decide) (by decide), m₅, R _ _ 840 848 (by decide) (by decide) (by decide),
        R _ _ 840 844 (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
    · rw [keep7 _ (by decide) (by decide), m₅, R _ _ 844 848 (by decide) (by decide) (by decide),
        Mem.readW_writeW_self32]
    · rw [keep7 _ (by decide) (by decide), m₅, Mem.readW_writeW_self32]
  · rw [← Proof.Blake2.wordBytes_readW (w := 32) _ _ (.inl rfl), show P s₀ + 832 = addr (scr s₀) 832 from
      (scr_addr hp (d := 832) (by decide)).symm, mt, Mem.readW_writeW_self32, Spec.Argon2.le32,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · show _ = _
    rw [mt, R _ _ outOff 832 (by decide) (by decide) (by decide),
      R _ _ outOff leftOff (by decide) (by decide) (by decide), m₇, Mem.readW_writeW_self32]
    simp
  · rw [mt, R _ _ leftOff 832 (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
    simp [ol]

theorem scr_rd {s : State} (b : Body s₀ s) {d : Nat} (hd : d + 4 ≤ 16384) :
    InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 := by
  rw [b.rd, b.wr]
  exact ⟨scrR s₀, by simp [hp.wr], contains_addr hd (by decide) hp.scr_fits⟩

theorem correct : WP isa Impl.Argon2.X86.HPrime.code s₀ fun t => abiPreserved s₀ t ∧ hPrimeX86.post s₀ t := by
  have hif := hp.in_fits
  unfold Impl.Argon2.X86.HPrime.code
  refine WP.seq ((setup_ok hp).mono fun s₁ ⟨b₁, o₁, e₁, F₁⟩ => ?_)
  obtain hin : bytesAt s₁.mem ((inp s₀).setWidth 64) (inl s₀) = bytesAt s₀.mem ((inp s₀).setWidth 64) (inl s₀) :=
    Proof.Blake2.bytesAt_congr fun i hi => F₁.bytes (R := inR s₀) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.in_scr) (by simp; omega_using [hif]) hi
  refine WP.seq ((first_ok hp ⟨b₁, o₁, e₁, hin⟩).mono fun s₂ ⟨⟨b₂, o₂, e₂, _⟩, d₂⟩ => ?_)
  refine WP.seq ((finish_ok hp b₂ o₂ d₂).mono fun s₃ ⟨b₃, e₃, h₃⟩ => ?_)
  unfold restore
  refine wp_movm (ea_of b₃.ebx 848) (scr_rd hp b₃ (by decide)) fun s₄ u₄ => ?_
  refine wp_movm (ea_of (by rw [u₄.other _ (by decide), b₃.ebx]) 844)
    (by rw [u₄.rd, u₄.wr]; exact scr_rd hp b₃ (by decide)) fun s₅ u₅ => ?_
  refine wp_movm (ea_of (by rw [u₅.other _ (by decide), u₄.other _ (by decide), b₃.ebx]) 840)
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact scr_rd hp b₃ (by decide)) fun t u => WP.block_nil ?_
  obtain mt : t.mem = s₃.mem := by rw [u.mem, u₅.mem, u₄.mem]
  have sv := b₃.saved
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at sv
  obtain ⟨sb, ss, sd⟩ := sv
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [u.gpr, u₅.mem, u₄.mem]; exact sb
    · rw [u.other _ (by decide), u₅.gpr, u₄.mem]; exact ss
    · rw [u.other _ (by decide), u₅.other _ (by decide), u₄.gpr]; exact sd
    · rw [u.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), e₃, e₂]
    · rw [u.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), b₃.esp]
  · rw [mt]
    refine b₃.frame.readW (r := retR s₀) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_out
    · exact hp.ret_scr
    · show Region.Disjoint _ ⟨(esp₀ s₀ - BitVec.ofNat 32 60).setWidth 64, 60⟩
      rw [Taint.sub_setWidth hp.esp_lo]
      exact Offset.base_disjoint_below _ (by omega_using [])
  · show bytesAt t.mem _ _ = _
    rw [mt]; exact h₃

end

end VG.Proof.Argon2.X86.HPrime

end

/-!
# Argon2 H′ on x86 (32-bit): verified

Constant time, by relating two runs with the same public data piece by piece
(`code_ct`): the setup is checked by the taint analysis from the arguments,
`first` and `finishOutput` by their pieces; then `hPrime_verified` against the
contract with the arguments read only.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (setup restore first finishOutput chooseLength absorbInput finishInput
  absorbFixed leftOff)
open VG.Proof.Sha256.X86.Stream (Upd wp_movm wp_cmpi contains_addr)

/-! ## The setup -/

/-- The taint analysis of the setup starts with the stack arguments public,
and the word holding `scratch` known to be the base of the second writable
region. -/
def τS : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 16384], argLen := 24, argBases := [(20, 1)] }

theorem wfS {s : State} (hp : Pre s) : VG.X86.Taint.Wf τS s := by
  obtain ho := hp.out_fits; have hsc := hp.scr_fits; have hs := hp.esp_hi
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, τS], by simpa [hp.wr] using hp.out_scr, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_arith
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.ret_out hp.arg_out
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.ret_scr hp.arg_scr
  · intro p hp'
    simp only [τS, List.mem_cons, List.not_mem_nil, or_false] at hp'
    subst hp'
    refine ⟨by decide, ?_⟩
    simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem agreeS {s₁ s₂ : State} (hp₁ : Pre s₁) (hp₂ : Pre s₂) (q : Same s₁ s₂) :
    VG.X86.Taint.Agree τS s₁ s₂ := by
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wfS hp₁, wfS hp₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => q.esp.symm,
    fun k h4 hk => ?_⟩
  · simp only [τS, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact q.esp.symm
  · rw [hp₁.wr, hp₂.wr]
    simp only [outR, scrR, P, op, ol, scr, q.args 2 (by decide), q.args 3 (by decide),
      q.args 4 (by decide)]
  · simp only [τS] at hk
    rw [show VG.X86.Taint.depth τS.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by have := hp₁.esp_hi; omega) h4 hk,
      VG.X86.Taint.argByte_eq (by have := hp₂.esp_hi; omega) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega_using [])), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega_using []))]
    exact congrArg _ (q.args _ (by omega_using [hk])).symm

theorem setup_F0 {s₀ : State} (hp : Pre s₀) : WP isa (.block setup) s₀ (F0 s₀) := by
  have hif := hp.in_fits
  refine (setup_ok hp).mono fun t ⟨b, o, e, f⟩ => ⟨b, o, e, ?_⟩
  exact Proof.Blake2.bytesAt_congr fun i hi => f.bytes (R := inR s₀) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.in_scr) (by simp; omega_using [hif]) hi

theorem setup_rel {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (q : Same s₀ s₀') :
    RelCT isa (fun t₁ t₂ => t₁ = s₀ ∧ t₂ = s₀') (.block setup) fun t₁ t₂ => F0 s₀ t₁ ∧ F0 s₀' t₂ :=
  ((RelCT.taint (A := taint) τS (fun _ _ ⟨e₁, e₂⟩ => by subst e₁ e₂; exact agreeS hp hp' q)
    (by taint_decide)).wp fun _ _ ⟨e₁, e₂⟩ =>
      ⟨by subst e₁; exact setup_F0 hp, by subst e₂; exact setup_F0 hp'⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-! ## `first` -/

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (q : Same s₀ s₀')

include hp in
theorem choose_blk {s : State} (h : F0 s₀ s) :
    WP isa (.block [.mov .edx (.mem (VG.Impl.Sha512.X86.at_ .ebx leftOff)), .alu .cmp .edx (.imm 65)]) s
      fun t => t.cf = some (decide (ol s₀ < 65)) := by
  have hs := hp.scr_fits
  obtain hol : ol s₀ < 2 ^ 32 := (arg s₀ 3).isLt
  refine wp_movm (VG.Proof.Sha512.X86.ea_of h.body.ebx leftOff)
    (by rw [h.body.rd, h.body.wr]
        exact ⟨scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩) fun s₁ u₁ =>
    wp_cmpi fun s₂ _ cf₂ _ => WP.block_nil ?_
  rw [cf₂, u₁.gpr, h.out.left, List.length_nil, Nat.sub_zero,
    Proof.Sha256.X86.Stream.toNat_ofNat_lt hol]; rfl

include hp hp' q in
theorem choose_rel :
    RelCT isa (fun t₁ t₂ => F0 s₀ t₁ ∧ F0 s₀' t₂) chooseLength fun _ _ => True := by
  unfold chooseLength
  refine RelCT.seq (rel_taint [.ebx] (fun _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [h₁.body.ebx, h₂.body.ebx, q.scr_eq]) ⟨_, by taint_decide⟩
    (fun _ h => choose_blk hp h) (fun _ h => choose_blk hp' h)) ?_
  exact RelCT.ite (fun t₁ t₂ ⟨f₁, f₂⟩ => by show t₁.cf = t₂.cf; rw [f₁, f₂, q.ol_eq])
    (RelCT.nil fun _ _ _ => trivial)
    (RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs fun _ h => nomatch h) (by taint_decide))

include hp hp' q in
theorem first_rel :
    RelCT isa (fun t₁ t₂ => F0 s₀ t₁ ∧ F0 s₀' t₂) first fun t₁ t₂ =>
      (F0 s₀ t₁ ∧ (digest s₀ t₁).take (nF s₀) = Spec.Argon2.H (nF s₀) (Spec.Argon2.le32 (ol s₀) ++ inB s₀)) ∧
      (F0 s₀' t₂ ∧ (digest s₀' t₂).take (nF s₀') =
        Spec.Argon2.H (nF s₀') (Spec.Argon2.le32 (ol s₀') ++ inB s₀')) := by
  have hs := hp.scr_fits
  have hif := hp.in_fits
  obtain nE : nF s₀' = nF s₀ := by simp only [nF, q.ol_eq]
  unfold first
  refine RelCT.seq (rel_wp (choose_rel hp hp' q) (fun _ h => first_choose hp h)
    (fun _ h => first_choose hp' h)) ?_
  refine RelCT.seq (rel_wp ((init_rel (B := scr s₀) (E := esp₀ s₀) (n := nF s₀) (nF_pos hp)
      (Nat.min_le_right _ _)).mono (fun _ _ ⟨⟨f₁, e₁⟩, ⟨f₂, e₂⟩⟩ =>
        ⟨⟨f₁.body.ctx hp, e₁⟩, by
          obtain c := f₂.body.ctx hp'
          rw [q.scr_eq, q.esp] at c
          exact ⟨c, by rw [e₂, nE]⟩⟩) fun _ _ h => h)
    (fun _ h => first_init hp h) (fun _ h => first_init hp' h)) ?_
  refine RelCT.seq (rel_wp ((absorbFixed_rel (B := scr s₀) (E := esp₀ s₀) (offset := 832) (size := 4)
      (by omega_using [hs]) (by decide) (by decide) (hp.stk_scr.sub_right (Offset.sub_base _ (by decide)))
      fixed_check_832).mono (fun _ _ ⟨⟨f₁, _⟩, ⟨f₂, _⟩⟩ =>
        ⟨⟨f₁.body.ctx hp, pfx_cov hp f₁.body⟩, by
          obtain c := f₂.body.ctx hp'
          obtain v := pfx_cov hp' f₂.body
          simp only [P] at v
          rw [q.scr_eq, q.esp] at c; rw [q.scr_eq] at v
          exact ⟨c, v⟩⟩) fun _ _ h => h)
    (fun _ h => first_fixed hp h) (fun _ h => first_fixed hp' h)) ?_
  refine RelCT.seq (rel_wp ?_ (fun _ h => first_input hp h) (fun _ h => first_input hp' h))
    (rel_wp ?_ (fun _ h => first_finish hp h) (fun _ h => first_finish hp' h))
  · unfold absorbInput
    refine RelCT.seq (rel_taint [.esp, .ebx] (fun _ _ h₁ h₂ => agree_body q h₁.1.body h₂.1.body)
      ⟨_, by taint_decide⟩ (fun _ h => (absorbInput_blk hp h.1).mono fun _ h => h.1)
      (fun _ h => (absorbInput_blk hp' h.1).mono fun _ h => by
        have h := h.1
        rw [q.scr_eq, q.esp, q.inp_eq, q.inl_eq] at h; exact h)) ?_
    exact update_rel hif (hp.in_scr.sub_right (Region.sub_prefix (by decide))) hp.stk_in
  · unfold finishInput
    refine RelCT.seq (rel_taint [.esp, .ebx] (fun _ _ h₁ h₂ => agree_body q h₁.1.body h₂.1.body)
      ⟨_, by taint_decide⟩ (fun _ h => (finishInput_blk hp h.1).mono fun _ h => h.1)
      (fun _ h => (finishInput_blk hp' h.1).mono fun _ h => by
        have h := h.1
        rw [q.scr_eq, q.esp, cntLo, cntHi, q.inl_eq] at h; exact h)) ?_
    exact finalize_rel

end

/-! ## Constant time -/

theorem code_ct : ConstantTime isa hPrimeX86.pre hPrimeX86.pub Impl.Argon2.X86.HPrime.code := by
  refine RelCT.constantTime (Q := fun _ _ => True)
    fun s₀ s₀' t₁ t₂ r₁ r₂ ⟨h₀, h₀', hq⟩ e₁ e₂ => ?_
  obtain hp := pre_of s₀ h₀
  obtain hp' := pre_of s₀' h₀'
  obtain q := Same.of_pub hq
  suffices h : RelCT isa (fun t₁ t₂ => t₁ = s₀ ∧ t₂ = s₀') Impl.Argon2.X86.HPrime.code fun _ _ => True from
    h s₀ s₀' t₁ t₂ r₁ r₂ ⟨rfl, rfl⟩ e₁ e₂
  unfold Impl.Argon2.X86.HPrime.code
  refine RelCT.seq (setup_rel hp hp' q) (RelCT.seq (first_rel hp hp' q)
    (RelCT.seq (R := fun t₁ t₂ => Body s₀ t₁ ∧ Body s₀' t₂) ?_ ?_))
  · exact rel_wp ((finishOutput_rel hp hp' q).mono (fun _ _ ⟨⟨f₁, _⟩, ⟨f₂, _⟩⟩ =>
      ⟨⟨f₁.body, f₁.out, f₁.ebp⟩, ⟨f₂.body, f₂.out, f₂.ebp⟩⟩) fun _ _ h => h)
      (fun _ ⟨f, d⟩ => (finish_ok hp f.body f.out d).mono fun _ h => h.1)
      (fun _ ⟨f, d⟩ => (finish_ok hp' f.body f.out d).mono fun _ h => h.1)
  · exact RelCT.taint (A := taint) (τr [.ebx]) (fun _ _ ⟨b₁, b₂⟩ => agree_regs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [b₁.ebx, b₂.ebx, q.scr_eq]) (by taint_decide)

/-! ## A state satisfying the precondition -/

/-- Memory holding the arguments `0x1000, 1, 0x2000, 1, 0x10000` at `0x5004`. -/
def hSatMem : Mem := fun a =>
  if a = 0x5005 then 0x10 else if a = 0x5008 then 1 else if a = 0x500D then 0x20 else
  if a = 0x5010 then 1 else if a = 0x5016 then 1 else 0

def hSatState : State where
  gpr r := match r with
    | .esp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := hSatMem
  rd := [⟨0x1000, 1⟩, ⟨0x5004, 20⟩]
  wr := [⟨0x2000, 1⟩, ⟨0x10000, 16384⟩]

theorem hSat_pre : hPrimeX86.pre hSatState := by
  obtain a0 : arg hSatState 0 = 0x1000 := by decide
  obtain a1 : arg hSatState 1 = 1 := by decide
  obtain a2 : arg hSatState 2 = 0x2000 := by decide
  obtain a3 : arg hSatState 3 = 1 := by decide
  obtain a4 : arg hSatState 4 = 0x10000 := by decide
  obtain e : argAddr hSatState 0 = 0x5004 := by decide
  simp only [hPrimeX86, a0, a1, a2, a3, a4, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide,
    by decide, by decide⟩ <;>
  exact Region.disjoint_of_sep (by decide)

theorem hPrime_verified : Verified X86.target Impl.Argon2.X86.HPrime.code hPrimeX86 :=
  ⟨fun s hs => correct (pre_of s hs), code_ct, ⟨hSatState, hSat_pre⟩⟩

end VG.Proof.Argon2.X86.HPrime
