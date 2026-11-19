module

public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.Writes
public import VerifiedGarbage.TCB.PPC64LE.Residue
public import VerifiedGarbage.TCB.Registration
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms

/-!
# Returning without secret residue (64-bit little-endian PowerPC)

`Verified.scrub`: code verified against a contract that `Sig.contract`
derives, whose frames use at most the contract's `stack` bytes
(`Code.ppc64leDepth`), followed by `Impl.Scrub.PPC64LE.scrubTail`
(`scrub`), is verified against the same contract and returns without secret
residue (`NoResidue`), as on RISC-V (`Proof/Framework/RISCV64/Scrub.lean`).
The proof of the code is used as it is: what `scrub` adds is checked once,
here, for all code. The clearing clears only the volatile registers the code
may write (`Clear.of`, `Proof/Framework/PPC64LE/Writes.lean`): one it never
writes holds on return what it held on entry, on which the two runs of
`NoResidue` agree (`Clear.Keeps`). The code must use no more stack than its contract
reserves, call indirectly only the functions of its tables of functions,
whose addresses two runs agree on (`tablesCall`), as on RISC-V, and its
postcondition read the memory on return only within the buffers (`PostOut`).

A frame's region starts 32 bytes above its stack pointer, past a header no
frame makes writable, so neither the code nor the clearing can write the
bottom 32 bytes of the stack its frames use; what is there is not a secret,
but it is not zero either. So the proof is about two runs rather than one:
two runs of the code with the same trace (`ConstantTime`), from states that
agree outside the buffers, end with memories that agree outside the buffers
but in the stack its frames' regions may cover (`InZ`), `Exec.agree`.
Their writes outside that are the same in both: the back chain each frame's
push stores is the stack pointer, the same in both runs, and a released
frame's bytes are `lose`'s, the same function of the same bytes and the
same unknowns. The clearing then zeroes that stack (`wipeM_agree`), and
leaves what it does not zero as a function of what agrees.
-/

@[expose] public section

open VG.Impl.Scrub.PPC64LE

namespace VG.PPC64LE

/-! ## Stack depth -/

/-- The bytes a frame's push moves `r1` down by. -/
def frameBytes : Instr → Nat
  | .push _ => 48
  | .alloc n => n
  | _ => 0

/-- How much stack below `r1` code uses at once, in bytes: its frames, of a
register (`push`) or of buffers (`alloc`). A call leaves its return address
in `LR`, not in memory. -/
def _root_.VG.Code.ppc64leDepth : Prog isa → Nat
  | .block _ => 0
  | .seq a b => max a.ppc64leDepth b.ppc64leDepth
  | .ite _ t e => max t.ppc64leDepth e.ppc64leDepth
  | .loop b _ => b.ppc64leDepth
  | .call _ b => b.ppc64leDepth
  | .frame i b _ => b.ppc64leDepth + frameBytes i
  | .icall _ _ b n => max b.ppc64leDepth n.ppc64leDepth

namespace Scrub

/-- The functions `c` may call indirectly. -/
def inames : Prog isa → List String
  | .block _ => []
  | .seq a b => inames a ++ inames b
  | .ite _ t e => inames t ++ inames e
  | .loop b _ => inames b
  | .call _ b => inames b
  | .frame _ b _ => inames b
  | .icall _ n b nx => n :: inames b ++ inames nx

/-- Code without indirect calls (`Code.icall`). -/
def icallFree : Prog isa → Bool
  | .block _ => true
  | .seq a b => icallFree a && icallFree b
  | .ite _ t e => icallFree t && icallFree e
  | .loop b _ => icallFree b
  | .call _ b => icallFree b
  | .frame _ b _ => icallFree b
  | .icall .. => false

/-- Code without indirect calls calls no function indirectly. -/
theorem inames_of_icallFree : ∀ {c : Prog isa}, icallFree c = true → inames c = []
  | .block _, _ => rfl
  | .seq a b, h => by
    simp only [icallFree, Bool.and_eq_true] at h
    simp only [inames, inames_of_icallFree h.1, inames_of_icallFree h.2, List.append_nil]
  | .ite _ t e, h => by
    simp only [icallFree, Bool.and_eq_true] at h
    simp only [inames, inames_of_icallFree h.1, inames_of_icallFree h.2, List.append_nil]
  | .loop b _, h => inames_of_icallFree (c := b) h
  | .call _ b, h => inames_of_icallFree (c := b) h
  | .frame _ b _, h => inames_of_icallFree (c := b) h
  | .icall .., h => by simp [icallFree] at h

/-- The functions the tables `ts` name. -/
def tableFns (ts : List (String × List FnTable)) : List String := ts.flatMap fun t => t.2.flatMap (·.fns)

/-- The code calls indirectly only the functions of the tables `ts`, whose
addresses two runs agree on (`tables_pub_syms`). -/
def tablesCall (c : Prog isa) (ts : List (String × List FnTable)) : Bool :=
  (inames c).all fun f => decide (f ∈ tableFns ts)

/-! ## Two runs agree but in the stack their frames may write -/

/-- Byte `x` is in the stack that frames between `L` and `T` may write:
from 32 bytes above `L`, past the header of a frame whose stack pointer is
`L`, to `T`. -/
def InZ (L T x : Addr) : Prop := L.toNat + 32 ≤ x.toNat ∧ x.toNat < T.toNat

/-- The memories agree outside the regions `R` and the stack `InZ L T`. -/
def Agr (R : List Region) (L T : Addr) (m₁ m₂ : Mem) : Prop :=
  ∀ x, (∀ r ∈ R, ¬ r.Contains x 1) → ¬ InZ L T x → m₁ x = m₂ x

/-- Each writable region is one of `R` or within the stack `InZ L T`. -/
def WrOk (R : List Region) (L T : Addr) (wr : List Region) : Prop :=
  ∀ r ∈ wr, r ∈ R ∨ ∀ x, r.Contains x 1 → InZ L T x

section
variable {R : List Region} {L T : Addr}

theorem Agr.frame {m₁ m₂ m₁' m₂' : Mem} {wr : List Region} (h : Agr R L T m₁ m₂) (hw : WrOk R L T wr)
    (f₁ : Frame wr m₁ m₁') (f₂ : Frame wr m₂ m₂') : Agr R L T m₁' m₂' := by
  intro x hx hz
  have hn : ∀ r ∈ wr, ¬ r.Contains x 1 := fun r hr hc => by
    rcases hw r hr with hr | hr
    · exact hx r hr hc
    · exact hz (hr x hc)
  rw [f₁ x hn, f₂ x hn]
  exact h x hx hz

theorem Agr.write {m₁ m₂ : Mem} (h : Agr R L T m₁ m₂) (a : Addr) (n : Nat) (v : BitVec (8 * n)) :
    Agr R L T (m₁.write a n v) (m₂.write a n v) := by
  intro x hx hz
  simp only [Mem.write]
  split
  · rfl
  · exact h x hx hz

/-- Writes of different values within the stack `InZ L T`. -/
theorem Agr.writeZ {m₁ m₂ : Mem} (h : Agr R L T m₁ m₂) {a : Addr} {n : Nat}
    (ha : ∀ x, (x - a).toNat < n → InZ L T x) (v₁ v₂ : BitVec (8 * n)) :
    Agr R L T (m₁.write a n v₁) (m₂.write a n v₂) := by
  intro x hx hz
  have hn : ¬ (x - a).toNat < n := fun hc => hz (ha x hc)
  rw [Mem.write_apply hn, Mem.write_apply hn]
  exact h x hx hz

theorem Agr.lose {m₁ m₂ : Mem} (h : Agr R L T m₁ m₂) (a : Addr) (n : Nat) (u : Nat → BitVec 64) :
    Agr R L T (VG.PPC64LE.lose m₁ a n u) (VG.PPC64LE.lose m₂ a n u) := by
  intro x hx hz
  simp only [VG.PPC64LE.lose]
  split
  · split
    · exact h x hx hz
    · rfl
  · exact h x hx hz

end

/-- A byte `d < n` bytes above `a`, where `a` and its `n` bytes do not wrap
around, is at `a.toNat + d`. -/
theorem toNat_of_sub_lt {a x : Addr} {n : Nat} (hn : a.toNat + n ≤ 2 ^ 64) (h : (x - a).toNat < n) :
    x.toNat = a.toNat + (x - a).toNat := by
  have e : x = a + (x - a) := by bv_omega
  have he := congrArg BitVec.toNat e
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega_using [hn, h])] at he
  exact he

theorem toNat_sub_ofNat (p : Addr) (b : Nat) (h : b ≤ p.toNat) :
    (p - BitVec.ofNat 64 b).toNat = p.toNat - b := by
  have := p.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := b) (by omega_using [h]),
    show 2 ^ 64 - b + p.toNat = (p.toNat - b) + 2 ^ 64 by omega_using [h], Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega_using [])]

theorem toNat_add_ofNat (q : Addr) (o : Nat) (h : q.toNat + o < 2 ^ 64) :
    (q + BitVec.ofNat 64 o).toNat = q.toNat + o := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_using [h]),
    Nat.mod_eq_of_lt h]

/-- The region of a frame of `b` bytes pushed at `sp`, whose stack pointer
is at least `L`, is in the stack `InZ L T`. -/
theorem frame_inZ {L T sp : Addr} {b : Nat} (hb : 32 < b) (hL : L.toNat + b ≤ sp.toNat)
    (hT : sp.toNat ≤ T.toNat) (x : Addr)
    (hx : (x - (sp - BitVec.ofNat 64 b + 32)).toNat < b - 32) : InZ L T x := by
  have h1 : (sp - BitVec.ofNat 64 b).toNat = sp.toNat - b := toNat_sub_ofNat sp b (by omega_using [hL])
  have h2 : (sp - BitVec.ofNat 64 b + 32).toNat = sp.toNat - b + 32 := by
    rw [show (32 : Addr) = BitVec.ofNat 64 32 from rfl, toNat_add_ofNat _ _ (by
      have := sp.isLt; omega_using [h1, hb, hL])]
    rw [h1]
  have := sp.isLt
  have hx' := toNat_of_sub_lt (n := b - 32) (by omega_using [h2, hb, hL]) hx
  rw [h2] at hx'
  simp only [InZ]; omega_using [hx', hx, hb, hL, hT]

/-! ### The steps of a run -/

/-- The unknowns an instruction uses. -/
def instrK : Instr → Nat
  | .mtvsrd .. | .adrSym .. => 1
  | _ => 0

theorem exec_unknowns {i : Instr} {s s' : State} (h : exec i s = some s') :
    s'.unknowns = fun n => s.unknowns (n + instrK i) := by
  cases i
  case loadRev sz t a b =>
    cases sz <;> simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h <;>
      (obtain ⟨_, -, _, -, rfl⟩ := h; rfl)
  case storeRev sz t a b =>
    cases sz <;> simp only [exec, Option.bind_eq_some_iff, State.store] at h <;>
      (obtain ⟨_, -, h⟩ := h; split at h <;> first | (cases h; rfl) | cases h)
  all_goals
    simp only [exec] at h
    first
    | (cases h; rfl)
    | (split at h <;> first | (cases h; rfl) | cases h)
    | (cases e : VOp.eval _ _ with
        | none => rw [e] at h; cases h
        | some p => rw [e] at h; cases h; rfl)
    | (simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
       obtain ⟨_, -, _, -, rfl⟩ := h; rfl)
    | (simp only [Option.bind_eq_some_iff, State.store] at h
       obtain ⟨_, -, h⟩ := h
       split at h <;> first | (cases h; rfl) | cases h)
    | cases h

theorem addrs_length (i : Instr) (s s' : State) : (addrs i s).length = (addrs i s').length := by
  cases i <;> rfl

/-- Two runs of a block from the same unknowns leave traces of the same
length and the same unknowns. -/
theorem execBlock_unknowns : ∀ {is : List Instr} {s₁ s₂ a b : State} {t₁ t₂ : List Leak},
    execBlock isa is s₁ = some (a, t₁) → execBlock isa is s₂ = some (b, t₂) →
      s₁.unknowns = s₂.unknowns → t₁.length = t₂.length ∧ a.unknowns = b.unknowns
  | [], _, _, _, _, _, _, h₁, h₂, hu => by
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
    obtain ⟨rfl, rfl⟩ := h₁; obtain ⟨rfl, rfl⟩ := h₂; exact ⟨rfl, hu⟩
  | i :: is, s₁, s₂, a, b, t₁, t₂, h₁, h₂, hu => by
    simp only [execBlock] at h₁ h₂
    cases e₁ : exec i s₁ with
    | none => rw [e₁] at h₁; cases h₁
    | some u₁ =>
      cases e₂ : exec i s₂ with
      | none => rw [e₂] at h₂; cases h₂
      | some u₂ =>
        rw [e₁] at h₁; rw [e₂] at h₂
        obtain ⟨p₁, hp₁, hq₁⟩ := Option.map_eq_some_iff.mp h₁
        obtain ⟨p₂, hp₂, hq₂⟩ := Option.map_eq_some_iff.mp h₂
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq₁
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq₂
        obtain ⟨hl, hu'⟩ := execBlock_unknowns (s₁ := u₁) (s₂ := u₂) (by rw [hp₁]) (by rw [hp₂])
          (by rw [exec_unknowns e₁, exec_unknowns e₂, hu])
        refine ⟨?_, hu'⟩
        simp only [List.length_append, List.length_map, hl, addrs_length i s₁ s₂]

/-- A frame's push on two states with the same stack pointer, writable
regions and unknowns, whose memories agree, gives two such states, whose
new region is in the stack `InZ L T` if the frame is. -/
theorem push_agr {R : List Region} {L T : Addr} {i : Instr} {s s' s₁ s₁' : State}
    (h : isa.push i s = some s₁) (h' : isa.push i s' = some s₁') (hsp : s.sp = s'.sp)
    (hw : s.wr = s'.wr) (hu : s.unknowns = s'.unknowns) (hA : Agr R L T s.mem s'.mem)
    (hL : L.toNat + frameBytes i ≤ s.sp.toNat) (hT : s.sp.toNat ≤ T.toNat) :
    s₁.sp = s₁'.sp ∧ s₁.wr = s₁'.wr ∧ s₁.unknowns = s₁'.unknowns ∧ Agr R L T s₁.mem s₁'.mem ∧
      s₁.sp = s.sp - BitVec.ofNat 64 (frameBytes i) ∧
      ∃ f, s₁.wr = f :: s.wr ∧ ∀ x, f.Contains x 1 → InZ L T x := by
  cases i <;> simp only [isa, push, reduceCtorEq] at h h' <;> rw [← hsp, ← hw, ← hu] at h'
  · split at h <;> [rename_i hc; cases h]
    cases h; rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h'; cases h'
    refine ⟨rfl, rfl, rfl, (hA.write _ _ _).writeZ (fun x hx => ?_) _ _, rfl, _, rfl, fun x hx => ?_⟩
    · exact frame_inZ (b := 48) (by decide) hL hT x (Nat.lt_of_lt_of_le hx (by decide))
    · simp only [Region.Contains] at hx
      exact frame_inZ (b := 48) (by decide) hL hT x hx
  · split at h <;> [rename_i hc; cases h]
    cases h; rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h'; cases h'
    refine ⟨rfl, rfl, rfl, hA.write _ _ _, rfl, _, rfl, fun x hx => ?_⟩
    simp only [Region.Contains] at hx
    exact frame_inZ hc.1 hL hT x hx

/-- The unknowns a frame's release uses. -/
def popK : Instr → Nat
  | .pop _ => 12
  | .free b => b / 4
  | _ => 0

/-- A frame's release, on two states with the same stack pointer and
unknowns, whose memories agree, gives memories that agree. -/
theorem pop_agr {R : List Region} {L T : Addr} {j : Instr} {s₁ s₂ s' s₁' s₂' s'' : State}
    (h : isa.pop j s₁ s₂ = some s') (h' : isa.pop j s₁' s₂' = some s'') (hsp : s₂.sp = s₂'.sp)
    (hu : s₂.unknowns = s₂'.unknowns) (hA : Agr R L T s₂.mem s₂'.mem) :
    s'.unknowns = (fun n => s₂.unknowns (n + popK j)) ∧
      s''.unknowns = (fun n => s₂'.unknowns (n + popK j)) ∧ Agr R L T s'.mem s''.mem := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h h' <;> split at h <;> cases h <;>
    split at h' <;> cases h'
  all_goals
    refine ⟨rfl, rfl, ?_⟩
    show Agr R L T (lose _ _ _ _) (lose _ _ _ _)
    rw [hsp, hu]
    exact hA.lose _ _ _

theorem branch_ne {r₁ r₂ : List Leak} : Leak.branch true :: r₁ ≠ Leak.branch false :: r₂ := by
  intro h; cases h

/-- The trace of an indirect call: the addresses its instruction reads, then
the address it calls. -/
theorem icall_trace {i : Instr} {n : String} {b nx : Prog isa} {s s' : State} {t : List Leak}
    (e : Exec isa (.icall i n b nx) s t s') :
    ∃ a rest, isa.icall i s = some a ∧ t = (isa.addrs i s).map .addr ++ .addr a :: rest := by
  cases e with
  | icall h₁ _ _ _ => exact ⟨_, _, h₁, rfl⟩
  | icallNext _ _ e' => exact icall_trace e'

/-- Two runs of code from states with the same stack pointer, writable
regions, unknowns and addresses of the functions the code calls indirectly
(`inames`), whose memories agree outside the
regions `R` and the stack `InZ L T` (`Agr`), and one of whose traces is a
prefix of the other's continued, have the same trace, and end with the same
unknowns and memories that agree, if the stack the code's frames use is
between `L` and `T` and its writable regions are `R`'s or within that stack
(`WrOk`). -/
theorem Exec.agree {R : List Region} {L T : Addr} {c : Prog isa} {s₁ s₁' : State} {t₁ : List Leak}
    (e₁ : Exec isa c s₁ t₁ s₁') :
    ∀ {s₂ s₂' : State} {t₂ : List Leak} (r₁ r₂ : List Leak), Exec isa c s₂ t₂ s₂' →
      (∀ n ∈ inames c, s₁.syms n = s₂.syms n) → s₁.sp = s₂.sp → s₁.wr = s₂.wr → s₁.unknowns = s₂.unknowns → WrOk R L T s₁.wr →
      L.toNat + c.ppc64leDepth ≤ s₁.sp.toNat → s₁.sp.toNat ≤ T.toNat →
      Agr R L T s₁.mem s₂.mem → t₁ ++ r₁ = t₂ ++ r₂ →
      t₁ = t₂ ∧ s₁'.unknowns = s₂'.unknowns ∧ Agr R L T s₁'.mem s₂'.mem := by
  induction e₁ with
  | @block is s₁ _ _ h₁ =>
    intro _ _ _ r₁ r₂ e₂ _ _ hw hu hwr _ _ hA ht
    cases e₂ with
    | block h₂ =>
      obtain ⟨hl, hu'⟩ := execBlock_unknowns h₁ h₂ hu
      obtain ⟨-, -, -, f₁⟩ := execBlock_regions h₁
      obtain ⟨-, -, -, f₂⟩ := execBlock_regions h₂
      exact ⟨(List.append_inj ht hl).1, hu', hA.frame hwr f₁ (hw ▸ f₂)⟩
  | @seq c₁ c₂ _ s₂ _ _ _ h₁ _ ih₁ ih₂ =>
    intro _ _ _ r₁ r₂ e₂ hf hsp hw hu hwr hL hT hA ht
    simp only [inames, List.mem_append] at hf
    simp only [Code.ppc64leDepth] at hL
    cases e₂ with
    | seq a₂ b₂ =>
      rw [List.append_assoc, List.append_assoc] at ht
      obtain ⟨rfl, hu', hA'⟩ := ih₁ _ _ a₂ (fun n hn => hf n (.inl hn)) hsp hw hu hwr (by omega_using [hL]) hT hA ht
      obtain ⟨-, w₁, p₁⟩ := Exec.rdwr h₁
      obtain ⟨-, w₂, p₂⟩ := Exec.rdwr a₂
      obtain ⟨rfl, hu'', hA''⟩ := ih₂ _ _ b₂
        (fun n hn => by rw [Exec.syms h₁, Exec.syms a₂]; exact hf n (.inr hn)) (by rw [p₁, p₂, hsp]) (by rw [w₁, w₂, hw]) hu'
        (by rw [w₁]; exact hwr) (by rw [p₁]; omega_using [hL]) (by rw [p₁]; exact hT) hA'
        (List.append_cancel_left ht)
      exact ⟨rfl, hu'', hA''⟩
  | iteT _ _ ih =>
    intro _ _ _ r₁ r₂ e₂ hf hsp hw hu hwr hL hT hA ht
    simp only [inames, List.mem_append] at hf
    simp only [Code.ppc64leDepth] at hL
    cases e₂ with
    | iteT _ a₂ =>
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      obtain ⟨rfl, hu', hA'⟩ := ih _ _ a₂ (fun n hn => hf n (.inl hn)) hsp hw hu hwr (by omega_using [hL]) hT hA ht
      exact ⟨rfl, hu', hA'⟩
    | iteF _ _ => exact absurd ht branch_ne
  | iteF _ _ ih =>
    intro _ _ _ r₁ r₂ e₂ hf hsp hw hu hwr hL hT hA ht
    simp only [inames, List.mem_append] at hf
    simp only [Code.ppc64leDepth] at hL
    cases e₂ with
    | iteT _ _ => exact absurd ht.symm branch_ne
    | iteF _ a₂ =>
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      obtain ⟨rfl, hu', hA'⟩ := ih _ _ a₂ (fun n hn => hf n (.inr hn)) hsp hw hu hwr (by omega_using [hL]) hT hA ht
      exact ⟨rfl, hu', hA'⟩
  | loopExit _ _ ih =>
    intro _ _ _ r₁ r₂ e₂ hf hsp hw hu hwr hL hT hA ht
    cases e₂ with
    | loopExit b₂ _ =>
      rw [List.append_assoc, List.append_assoc] at ht
      obtain ⟨rfl, hu', hA'⟩ := ih _ _ b₂ hf hsp hw hu hwr hL hT hA ht
      exact ⟨rfl, hu', hA'⟩
    | loopNext b₂ _ _ =>
      rw [List.append_assoc, List.append_assoc] at ht
      obtain ⟨rfl, -⟩ := ih _ _ b₂ hf hsp hw hu hwr hL hT hA ht
      exact absurd (List.append_cancel_left ht).symm branch_ne
  | @loopNext _ _ _ s' _ _ _ h₁ _ _ ih₁ ih₂ =>
    intro _ _ _ r₁ r₂ e₂ hf hsp hw hu hwr hL hT hA ht
    cases e₂ with
    | loopExit b₂ _ =>
      rw [List.append_assoc, List.append_assoc] at ht
      obtain ⟨rfl, -⟩ := ih₁ _ _ b₂ hf hsp hw hu hwr hL hT hA ht
      exact absurd (List.append_cancel_left ht) branch_ne
    | loopNext b₂ _ n₂ =>
      rw [List.append_assoc, List.append_assoc] at ht
      obtain ⟨rfl, hu', hA'⟩ := ih₁ _ _ b₂ hf hsp hw hu hwr hL hT hA ht
      have ht' := List.append_cancel_left ht
      simp only [List.cons_append, List.cons.injEq, true_and] at ht'
      obtain ⟨-, w₁, p₁⟩ := Exec.rdwr h₁
      obtain ⟨-, w₂, p₂⟩ := Exec.rdwr b₂
      obtain ⟨rfl, hu'', hA''⟩ := ih₂ _ _ n₂ (by rw [Exec.syms h₁, Exec.syms b₂]; exact hf) (by rw [p₁, p₂, hsp]) (by rw [w₁, w₂, hw]) hu'
        (by rw [w₁]; exact hwr) (by rw [p₁]; exact hL) (by rw [p₁]; exact hT) hA' ht'
      exact ⟨rfl, hu'', hA''⟩
  | call hc₁ _ hr ih =>
    intro _ _ _ r₁ r₂ e₂ hf hsp hw hu hwr hL hT hA ht
    simp only [Code.ppc64leDepth] at hL
    cases e₂ with
    | call hc₂ b₂ hr₂ =>
      simp only [List.map_nil, List.nil_append, List.append_nil] at ht
      simp only [isa, call, Option.some.injEq] at hc₁ hc₂
      subst hc₁ hc₂
      obtain ⟨rfl, hu', hA'⟩ := ih _ _ b₂ hf hsp hw (by simp only [hu]) hwr hL hT hA ht
      rw [ret_eq hr, ret_eq hr₂]
      exact ⟨rfl, hu', hA'⟩
  | @frame i j _ s₀ sf s₂ _ _ hp b₁ hq ih =>
    intro s₀' _ _ r₁ r₂ e₂ hfs hsp hw hu hwr hL hT hA ht
    simp only [Code.ppc64leDepth] at hL
    cases e₂ with
    | @frame _ _ _ _ sf' s₂' _ _ hp₂ b₂ hq₂ =>
      rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc] at ht
      have hl : (List.map Leak.addr (isa.addrs i s₀)).length = (List.map Leak.addr (isa.addrs i s₀')).length := by
        simp only [List.length_map, addrs_length i s₀ s₀']
      obtain ⟨h₀, ht'⟩ := List.append_inj ht hl
      obtain ⟨sp₁, w₁, u₁, hA₁, hsp₁, f, hwf, hf⟩ :=
        push_agr hp hp₂ hsp hw hu hA (by omega_using [hL]) hT
      have hwr₁ : WrOk R L T sf.wr := by
        rw [hwf]; intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact .inr hf
        · exact hwr r hr
      have hfb : frameBytes i ≤ s₀.sp.toNat := by omega_using [hL]
      have hsp' := toNat_sub_ofNat _ _ hfb
      obtain ⟨rfl, hu', hA'⟩ := ih _ _ b₂ (by rw [push_syms hp, push_syms hp₂]; exact hfs) sp₁ w₁ u₁ hwr₁
        (by rw [hsp₁, hsp']; omega_using [hL, hfb]) (by rw [hsp₁, hsp']; omega_using [hT, hfb]) hA₁ ht'
      have hl' : (List.map Leak.addr (isa.addrs j s₂)).length = (List.map Leak.addr (isa.addrs j s₂')).length := by
        simp only [List.length_map, addrs_length j s₂ s₂']
      have h₃ := (List.append_inj (List.append_cancel_left ht') hl').1
      obtain ⟨-, -, p₂⟩ := Exec.rdwr b₁
      obtain ⟨-, -, p₂'⟩ := Exec.rdwr b₂
      obtain ⟨q₁, q₂, hA''⟩ := pop_agr hq hq₂ (by rw [p₂, p₂', sp₁]) hu' hA'
      refine ⟨by rw [h₀, h₃], by rw [q₁, q₂, hu'], hA''⟩
  | @icall i _ _ _ s₀ _ s₂ _ _ hi₁ hc₁ _ hr₁ ih =>
    intro s₀' _ _ r₁ r₂ e₂ hf hsp hw hu hwr hL hT hA ht
    have hn := hf _ (List.mem_cons_self ..)
    cases e₂ with
    | @icall _ _ _ _ _ _ s₂' _ _ hi₂ hc₂ x₂ hr₂ =>
      simp only [List.append_assoc, List.cons_append] at ht
      have hl : (List.map Leak.addr (isa.addrs i s₀)).length = (List.map Leak.addr (isa.addrs i s₀')).length := by
        simp only [List.length_map, addrs_length i s₀ s₀']
      obtain ⟨h₀, ht'⟩ := List.append_inj ht hl
      simp only [List.cons.injEq] at ht'
      obtain ⟨ha, ht'⟩ := ht'
      simp only [List.map_nil, List.nil_append, List.append_nil] at ht' ⊢
      simp only [isa, call, Option.some.injEq] at hc₁ hc₂
      subst hc₁ hc₂
      obtain ⟨rfl, hu', hA'⟩ := ih _ _ x₂ (fun m hm => hf m (by simp [inames, hm])) hsp hw
        (by simp only [hu]) hwr (Nat.le_trans (Nat.add_le_add_left (Nat.le_max_left _ _) _) hL) hT hA ht'
      refine ⟨by rw [h₀, ha], ?_⟩
      rw [ret_eq hr₁, ret_eq hr₂]
      exact ⟨hu', hA'⟩
    | icallNext hi₂ hne₂ x₂ =>
      exfalso
      obtain ⟨a₂, rest, hi₂', ht₂⟩ := icall_trace x₂
      rw [hi₂] at hi₂'; cases hi₂'
      rw [ht₂] at ht
      simp only [List.append_assoc, List.cons_append] at ht
      obtain ⟨-, ht⟩ := List.append_inj ht (by simp only [List.length_map]; exact addrs_length _ _ _)
      simp only [List.cons.injEq, Leak.addr.injEq] at ht
      apply hne₂
      rw [← ht.1]; exact hn
  | icallNext hi₁ hne₁ x₁ ih =>
    intro _ _ _ r₁ r₂ e₂ hf hsp hw hu hwr hL hT hA ht
    cases e₂ with
    | icallNext hi₂ hne₂ x₂ =>
      exact ih _ _ x₂ (fun m hm => hf m (List.mem_cons_of_mem _ (List.mem_append_right _ hm))) hsp hw hu
        hwr (Nat.le_trans (Nat.add_le_add_left (Nat.le_max_right _ _) _) hL) hT hA ht
    | icall hi₂ hc₂ x₂ hr₂ =>
      exfalso
      obtain ⟨a₁, rest, hi₁', ht₁⟩ := icall_trace x₁
      rw [hi₁] at hi₁'; cases hi₁'
      rw [ht₁] at ht
      simp only [List.append_assoc, List.cons_append] at ht
      obtain ⟨-, ht⟩ := List.append_inj ht (by simp only [List.length_map]; exact addrs_length _ _ _)
      simp only [List.cons.injEq, Leak.addr.injEq] at ht
      apply hne₁
      rw [ht.1]; exact (hf _ (List.mem_cons_self ..)).symm

/-! ## The clearing's run -/

/-- `d` bytes above `a` is within `n` bytes of it, where `a` and its `n`
bytes do not wrap around, as natural numbers. -/
theorem sub_lt_iff {a x : Addr} {n : Nat} (hn : a.toNat + n ≤ 2 ^ 64) :
    (x - a).toNat < n ↔ a.toNat ≤ x.toNat ∧ x.toNat < a.toNat + n := by
  constructor
  · intro h
    have := toNat_of_sub_lt hn h
    omega_using [this, h]
  · rintro ⟨h₁, h₂⟩
    rw [BitVec.toNat_sub]
    have := a.isLt
    rw [show 2 ^ 64 - a.toNat + x.toNat = (x.toNat - a.toNat) + 2 ^ 64 by omega_using [h₁, this],
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_using [h₁, h₂, hn])]
    omega_using [h₁, h₂]

/-- `m` with the bytes at offsets `lo` to `hi - 1` from `q` zeroed. -/
def zeroOn (q : Addr) (lo hi : Nat) (m : Mem) : Mem :=
  fun x => if lo ≤ (x - q).toNat ∧ (x - q).toNat < hi then 0 else m x

theorem off_lt (x p : Addr) (o n : Nat) (ho : o + n < 2 ^ 64) :
    (x - (p + BitVec.ofNat 64 o)).toNat < n ↔ o ≤ (x - p).toNat ∧ (x - p).toNat < o + n := by
  have e : (x - (p + BitVec.ofNat 64 o)) + BitVec.ofNat 64 o = x - p := by bv_omega
  have e' := congrArg BitVec.toNat e
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_using [ho])] at e'
  have h1 := (x - (p + BitVec.ofNat 64 o)).isLt
  have h2 := (x - p).isLt
  generalize (x - (p + BitVec.ofNat 64 o)).toNat = r at *
  generalize (x - p).toNat = d at *
  by_cases hc : r + o < 2 ^ 64
  · rw [Nat.mod_eq_of_lt hc] at e'; omega_using [e']
  · rw [show r + o = (r + o - 2 ^ 64) + 2 ^ 64 by omega_using [hc], Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega_using [ho, h1])] at e'
    omega_using [ho, h1, e', hc]

/-- The trace of `stores k n` from `r12 = q`. -/
def storesTr (q : Addr) : Nat → Nat → List Leak
  | _, 0 => []
  | k, n + 1 => .addr (q + BitVec.ofNat 64 (8 * k)) :: storesTr q (k + 1) n

/-- `stores k n` zeroes the doublewords at offsets `8k` to `8(k + n) - 1`
from `r12 = q`, in a writable region `⟨q, B⟩`. -/
theorem stores_run (q : Addr) (B : Nat) (hB : B < 4096) (hqB : q.toNat + B ≤ 2 ^ 64) :
    ∀ (n k : Nat) (u : State), 8 * (k + n) ≤ B → u.gpr .r0 = 0 → u.gpr .r12 = q → ⟨q, B⟩ ∈ u.wr →
      execBlock isa (stores k n) u = some ({ u with mem := zeroOn q (8 * k) (8 * (k + n)) u.mem },
        storesTr q k n)
  | 0, k, u, _, _, _, _ => by
    simp only [stores, execBlock, storesTr]
    congr
    cases u; simp only [State.mk.injEq, and_true, true_and]
    funext x; simp only [zeroOn, Nat.add_zero]; split
    · next h => omega_using [h.1, h.2]
    · rfl
  | n + 1, k, u, hk, h0, h1, hw => by
    have hlt : q.toNat + 8 * k < 2 ^ 64 := by omega_using [hk, hqB]
    have hc : InRegions u.wr (u.gpr .r12 + BitVec.ofNat 64 (8 * k)) 8 := by
      refine ⟨_, hw, ?_⟩
      simp only [Region.Contains]
      rw [h1, show q + BitVec.ofNat 64 (8 * k) - q = BitVec.ofNat 64 (8 * k) by bv_omega,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hlt])]
      omega_using [hk]
    simp only [stores, execBlock, exec_store_d (show Reg.r12 ≠ .r0 by decide)
      ⟨by omega_using [hk, hB], by omega_using []⟩ hc]
    rw [stores_run q B hB hqB n (k + 1) { u with mem := u.mem.writeW (u.gpr .r12 + BitVec.ofNat 64 (8 * k)) (u.gpr .r0) }
      (by omega_using [hk]) h0 h1 hw]
    have hm : zeroOn q (8 * (k + 1)) (8 * (k + 1 + n))
        (u.mem.writeW (u.gpr .r12 + BitVec.ofNat 64 (8 * k)) (u.gpr .r0)) =
        zeroOn q (8 * k) (8 * (k + (n + 1))) u.mem := by
      funext x
      have e := off_lt x q (8 * k) 8 (by omega_using [hk, hB])
      simp only [zeroOn, Mem.writeW, Mem.write, h0, h1, Nat.reduceDiv, Nat.reduceMul]
      generalize (x - (q + BitVec.ofNat 64 (8 * k))).toNat = r at e ⊢
      generalize (x - q).toNat = d at e ⊢
      repeat' split
      all_goals first | (exfalso; omega) | rfl | (simp; done)
    simp only [Option.map_some, isa, addrs, h1, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, storesTr]
    rw [h1] at hm
    rw [hm]

/-- What `wipeFrame b` leaves in memory from `r1 = p`, the unknowns `U` and
the memory `m`: the back chain `p` at `p - b`, the region above the header
zeroed, then the frame released. -/
def frameM (b : Nat) (p : Addr) (U : Nat → BitVec 64) (m : Mem) : Mem :=
  lose (zeroOn (p - BitVec.ofNat 64 b + 32) 0 (b - 32) (m.write (p - BitVec.ofNat 64 b) 8 p))
    (p - BitVec.ofNat 64 b) b U

/-- The trace of `wipeFrame b` from `r1 = p`. -/
def frameTr (b : Nat) (p : Addr) : List Leak :=
  [.addr (p - BitVec.ofNat 64 b)] ++ ([] ++ storesTr (p - BitVec.ofNat 64 b + 32) 0 ((b - 32) / 8)) ++ []

/-- A valid frame of the wipe. -/
def FrameOk (b : Nat) : Prop := 32 < b ∧ b < 4096 ∧ b % 16 = 0

theorem frame_push {b : Nat} (hb : FrameOk b) (u : State) (hs : b ≤ u.sp.toNat) :
    isa.push (.alloc b) u = some { u with
      sp := u.sp - BitVec.ofNat 64 b,
      mem := u.mem.write (u.sp - BitVec.ofNat 64 b) 8 u.sp,
      wr := ⟨u.sp - BitVec.ofNat 64 b + 32, b - 32⟩ :: u.wr } := by
  obtain ⟨h1, h2, h3⟩ := hb
  simp only [isa, push, h1, h2, h3, hs, and_self, ite_true]

theorem frame_pop {b : Nat} (hb : FrameOk b) {s₁ s₃ : State} (hsp : s₃.sp = s₁.sp) (hw : s₃.wr = s₁.wr)
    (hh : s₁.wr.head? = some ⟨s₁.sp + 32, b - 32⟩) :
    isa.pop (.free b) s₁ s₃ = some { s₃ with
      sp := s₃.sp + BitVec.ofNat 64 b, wr := s₃.wr.tail,
      mem := lose s₃.mem s₃.sp b s₃.unknowns, unknowns := fun n => s₃.unknowns (n + b / 4) } := by
  obtain ⟨h1, h2, h3⟩ := hb
  simp only [isa, pop, h1, h2, h3, hsp, hw, hh, and_self, ite_true]

/-- `wipeFrame b` from `r1 = p`: it leaves `frameM` in memory, uses `b / 4`
unknowns, and changes no register but `r12`. -/
theorem wipeFrame_run {b : Nat} (hb : FrameOk b) (u : State) (hs : b ≤ u.sp.toNat) (h0 : u.gpr .r0 = 0) :
    Exec isa (wipeFrame b) u (frameTr b u.sp)
      { u.write .r12 (u.sp - BitVec.ofNat 64 b + 32) with
          mem := frameM b u.sp u.unknowns u.mem, unknowns := fun n => u.unknowns (n + b / 4) } := by
  have hp := u.sp.isLt
  obtain ⟨hb1, hb2, hb3⟩ := hb
  have hq : (u.sp - BitVec.ofNat 64 b).toNat = u.sp.toNat - b := toNat_sub_ofNat _ _ hs
  have hq32 : (u.sp - BitVec.ofNat 64 b + 32).toNat = u.sp.toNat - b + 32 := by
    rw [show (32 : Addr) = BitVec.ofNat 64 32 from rfl, toNat_add_ofNat _ _ (by omega_using [hq, hb1, hs, hp]), hq]
  generalize hs₁ : ({ u with
      sp := u.sp - BitVec.ofNat 64 b,
      mem := u.mem.write (u.sp - BitVec.ofNat 64 b) 8 u.sp,
      wr := ⟨u.sp - BitVec.ofNat 64 b + 32, b - 32⟩ :: u.wr } : State) = s₁
  have hpush := frame_push ⟨hb1, hb2, hb3⟩ u hs
  rw [hs₁] at hpush
  have hs₁sp : s₁.sp = u.sp - BitVec.ofNat 64 b := by rw [← hs₁]
  have hs₁wr : s₁.wr = ⟨u.sp - BitVec.ofNat 64 b + 32, b - 32⟩ :: u.wr := by rw [← hs₁]
  have hs₁g : s₁.gpr = u.gpr := by rw [← hs₁]
  have hst := stores_run (u.sp - BitVec.ofNat 64 b + 32) (b - 32) (by omega_using [hb2])
    (by omega_using [hq32, hs, hp]) ((b - 32) / 8) 0 (s₁.write .r12 (s₁.sp + BitVec.ofNat 64 32))
    (by omega_using [hb3, hb1]) (by rw [RegUpd.gpr_write_of_ne _ _ (by decide), hs₁g, h0])
    (by rw [RegUpd.gpr_write_self, hs₁sp]; rfl)
    (by rw [RegUpd.wr_write, hs₁wr]; exact List.mem_cons_self)
  have hblk : execBlock isa (.addSp .r12 32 :: stores 0 ((b - 32) / 8)) s₁ =
      some ({ s₁.write .r12 (s₁.sp + BitVec.ofNat 64 32) with
        mem := zeroOn (u.sp - BitVec.ofNat 64 b + 32) (8 * 0) (8 * (0 + (b - 32) / 8)) s₁.mem },
        [] ++ storesTr (u.sp - BitVec.ofNat 64 b + 32) 0 ((b - 32) / 8)) := by
    simp only [execBlock, isa, exec, show 32 < 2 ^ 15 by decide, ite_true, hst, Option.map_some, addrs,
      List.map_nil, RegUpd.mem_write]
  generalize hs₃ : ({ s₁.write .r12 (s₁.sp + BitVec.ofNat 64 32) with
    mem := zeroOn (u.sp - BitVec.ofNat 64 b + 32) (8 * 0) (8 * (0 + (b - 32) / 8)) s₁.mem } : State) = s₃
    at hblk
  have hpop := frame_pop (s₁ := s₁) (s₃ := s₃) ⟨hb1, hb2, hb3⟩ (by rw [← hs₃]; rfl) (by rw [← hs₃]; rfl)
    (by rw [hs₁wr, hs₁sp]; rfl)
  have ef := Exec.frame (M := isa) (i := Instr.alloc b) (j := Instr.free b) hpush (.block hblk) hpop
  have et : (List.map Leak.addr (isa.addrs (.alloc b) u) ++
      ([] ++ storesTr (u.sp - BitVec.ofNat 64 b + 32) 0 ((b - 32) / 8)) ++
      List.map Leak.addr (isa.addrs (.free b) s₃)) = frameTr b u.sp := by
    simp only [addrs, List.map_cons, List.map_nil, frameTr]
  rw [et] at ef
  have es : ({ s₃ with
      sp := s₃.sp + BitVec.ofNat 64 b, wr := s₃.wr.tail,
      mem := lose s₃.mem s₃.sp b s₃.unknowns, unknowns := fun n => s₃.unknowns (n + b / 4) } : State) =
      { u.write .r12 (u.sp - BitVec.ofNat 64 b + 32) with
          mem := frameM b u.sp u.unknowns u.mem, unknowns := fun n => u.unknowns (n + b / 4) } := by
    subst hs₃ hs₁
    simp only [Nat.mul_zero, Nat.zero_add, show 8 * ((b - 32) / 8) = b - 32 by omega_using [hb3, hb1]]
    cases u
    simp only [State.write, List.tail_cons, BitVec.sub_add_cancel, State.mk.injEq, and_true, frameM]
    all_goals first | rfl | exact ⟨rfl, rfl⟩
  rw [es] at ef
  exact ef

/-- The levels of the wipe are valid: each frame is (with the frame of 32
bytes more that zeroes it, but the last), and each but the first is at least
64 bytes, so that its region covers the header of the frame above. -/
def ChunksOk (cs : List Nat) : Prop :=
  (∀ b ∈ cs, 32 < b ∧ b ≤ 4048 ∧ b % 16 = 0) ∧ ∀ b ∈ cs.tail, 64 ≤ b

theorem ChunksOk.tail {c : Nat} {cs : List Nat} (h : ChunksOk (c :: cs)) : ChunksOk cs := by
  refine ⟨fun b hb => h.1 b (List.mem_cons_of_mem _ hb), fun b hb => h.2 b ?_⟩
  cases cs with
  | nil => simp at hb
  | cons c' cs => exact List.mem_cons_of_mem _ hb

theorem ChunksOk.frame {c : Nat} {cs : List Nat} (h : ChunksOk (c :: cs)) : FrameOk c := by
  obtain ⟨h1, h2, h3⟩ := h.1 c List.mem_cons_self
  exact ⟨h1, by omega_using [h2], h3⟩

theorem ChunksOk.frame32 {c : Nat} {cs : List Nat} (h : ChunksOk (c :: cs)) : FrameOk (c + 32) := by
  obtain ⟨h1, h2, h3⟩ := h.1 c List.mem_cons_self
  exact ⟨by omega_using [h1], by omega_using [h2], by omega_using [h3]⟩

/-- The trace of `wipe cs` from `r1 = p`. -/
def wipeTr : List Nat → Addr → List Leak
  | [], _ => []
  | [c], p => frameTr c p
  | c :: c' :: cs, p =>
    frameTr (c + 32) p ++ ([.addr (p - BitVec.ofNat 64 c)] ++ wipeTr (c' :: cs) (p - BitVec.ofNat 64 c) ++ [])

/-- How many unknowns the frames of `wipe cs` use when they are released. -/
def wipeK : List Nat → Nat
  | [] => 0
  | [c] => c / 4
  | c :: c' :: cs => (c + 32) / 4 + wipeK (c' :: cs) + c / 4

/-- What `wipe cs` leaves in memory from `r1 = p`, the unknowns `U` and the
memory `m`. -/
def wipeM : List Nat → Addr → (Nat → BitVec 64) → Mem → Mem
  | [], _, _, m => m
  | [c], p, U, m => frameM c p U m
  | c :: c' :: cs, p, U, m =>
    lose (wipeM (c' :: cs) (p - BitVec.ofNat 64 c) (fun n => U (n + (c + 32) / 4))
        ((frameM (c + 32) p U m).write (p - BitVec.ofNat 64 c) 8 p))
      (p - BitVec.ofNat 64 c) c (fun n => U (n + (c + 32) / 4 + wipeK (c' :: cs)))

/-- `wipe cs` leaves `wipeM` in memory, uses `wipeK cs` unknowns, and
changes no register but `r12`, and none without levels. -/
theorem wipe_run : ∀ (cs : List Nat) (u : State), ChunksOk cs → cs.sum ≤ u.sp.toNat → cs = [] ∨ u.gpr .r0 = 0 →
    ∃ g : Reg → BitVec 64, (∀ r, r ≠ .r12 ∨ cs = [] → g r = u.gpr r) ∧
      Exec isa (wipe cs) u (wipeTr cs u.sp)
        { u with
          gpr := g, mem := wipeM cs u.sp u.unknowns u.mem,
          unknowns := fun n => u.unknowns (n + wipeK cs) }
  | [], u, _, _, _ => by
    refine ⟨u.gpr, fun _ _ => rfl, ?_⟩
    have : ({ u with
        gpr := u.gpr, mem := wipeM [] u.sp u.unknowns u.mem,
        unknowns := fun n => u.unknowns (n + wipeK []) } : State) = u := by
      cases u; rfl
    simp only [wipe, wipeTr]
    rw [this]; exact .block rfl
  | [c], u, hv, hs, h0 => by
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at hs
    exact ⟨_, fun r hr => RegUpd.gpr_write_of_ne _ _ (hr.resolve_right (by simp)),
      wipeFrame_run hv.frame u hs (h0.resolve_left (by simp))⟩
  | c :: c' :: cs, u, hv, hs, h0 => by
    replace h0 := h0.resolve_left (by simp)
    have hp := u.sp.isLt
    have hfc := hv.frame
    have hf32 := hv.frame32
    have hc' := (hv.1 c' (by simp)).1
    simp only [List.sum_cons] at hs
    have e₁ := wipeFrame_run hf32 u (by omega_using [hs, hc']) h0
    generalize hu₁ : ({ u.write .r12 (u.sp - BitVec.ofNat 64 (c + 32) + 32) with
        mem := frameM (c + 32) u.sp u.unknowns u.mem,
        unknowns := fun n => u.unknowns (n + (c + 32) / 4) } : State) = u₁ at e₁
    have hu₁sp : u₁.sp = u.sp := by rw [← hu₁]; rfl
    have hu₁wr : u₁.wr = u.wr := by rw [← hu₁]; rfl
    have hu₁r0 : u₁.gpr .r0 = 0 := by rw [← hu₁]; exact (RegUpd.gpr_write_of_ne u (u.sp - BitVec.ofNat 64 (c + 32) + 32) (show ¬ Reg.r0 = .r12 by decide)).trans h0
    have hpush := frame_push hfc u₁ (by rw [hu₁sp]; omega_using [hs, hc'])
    generalize hs₁ : ({ u₁ with
        sp := u₁.sp - BitVec.ofNat 64 c,
        mem := u₁.mem.write (u₁.sp - BitVec.ofNat 64 c) 8 u₁.sp,
        wr := ⟨u₁.sp - BitVec.ofNat 64 c + 32, c - 32⟩ :: u₁.wr } : State) = s₁ at hpush
    have hs₁sp : s₁.sp = u.sp - BitVec.ofNat 64 c := by rw [← hs₁, hu₁sp]
    have hq : (u.sp - BitVec.ofNat 64 c).toNat = u.sp.toNat - c := toNat_sub_ofNat _ _ (by omega_using [hs, hc'])
    obtain ⟨g, hg, e₂⟩ := wipe_run (c' :: cs) s₁ hv.tail
      (by rw [hs₁sp, hq, List.sum_cons]; omega_using [hs, hc']) (.inr (by rw [← hs₁]; exact hu₁r0))
    generalize hs₃ : ({ s₁ with
        gpr := g, mem := wipeM (c' :: cs) s₁.sp s₁.unknowns s₁.mem,
        unknowns := fun n => s₁.unknowns (n + wipeK (c' :: cs)) } : State) = s₃ at e₂
    have hpop := frame_pop (s₁ := s₁) (s₃ := s₃) hfc (by rw [← hs₃]) (by rw [← hs₃])
      (by rw [← hs₁]; rfl)
    have ef := Exec.seq e₁ (Exec.frame (M := isa) (i := Instr.alloc c) (j := Instr.free c) hpush e₂ hpop)
    refine ⟨g, fun r hr => ?_, ?_⟩
    · replace hr := hr.resolve_right (by simp)
      rw [hg r (.inl hr), ← hs₁, ← hu₁]; exact RegUpd.gpr_write_of_ne _ _ hr
    · have et : frameTr (c + 32) u.sp ++ (List.map Leak.addr (isa.addrs (.alloc c) u₁) ++
          wipeTr (c' :: cs) s₁.sp ++ List.map Leak.addr (isa.addrs (.free c) s₃)) =
          wipeTr (c :: c' :: cs) u.sp := by
        simp only [addrs, List.map_cons, List.map_nil, wipeTr, hs₁sp, hu₁sp]
      rw [et] at ef
      have es : ({ s₃ with
          sp := s₃.sp + BitVec.ofNat 64 c, wr := s₃.wr.tail,
          mem := lose s₃.mem s₃.sp c s₃.unknowns, unknowns := fun n => s₃.unknowns (n + c / 4) } : State) =
          { u with
            gpr := g, mem := wipeM (c :: c' :: cs) u.sp u.unknowns u.mem,
            unknowns := fun n => u.unknowns (n + wipeK (c :: c' :: cs)) } := by
        subst hs₃ hs₁ hu₁
        cases u
        simp only [State.write, List.tail_cons, BitVec.sub_add_cancel, State.mk.injEq, true_and, and_true,
          wipeM, wipeK]
        constructor
        · congr 1; funext n; congr 1; omega
        · funext n; congr 1; omega
      rw [es] at ef
      exact ef

/-! ### What the wipe leaves -/

theorem lose_out {m : Mem} {a x : Addr} {n : Nat} (u : Nat → BitVec 64) (h : ¬ (x - a).toNat < n) :
    lose m a n u x = m x := by
  simp only [lose, h, ite_false]

/-- `lose` is a function of each byte: of the byte, and the unknowns. -/
theorem lose_congr {m₁ m₂ : Mem} {a x : Addr} {n : Nat} (u : Nat → BitVec 64) (h : m₁ x = m₂ x) :
    lose m₁ a n u x = lose m₂ a n u x := by
  simp only [lose]; split
  · split
    · exact h
    · rfl
  · exact h

theorem write_congr {m₁ m₂ : Mem} {a x : Addr} {n : Nat} (v : BitVec (8 * n)) (h : m₁ x = m₂ x) :
    m₁.write a n v x = m₂.write a n v x := by
  simp only [Mem.write]; split
  · rfl
  · exact h

/-- A byte of the region `frameM b p` zeroes is the same whatever the memory
was; any other byte is a function of the byte. -/
theorem frameM_congr {b : Nat} (hb : 32 < b) {p x : Addr} (hs : b ≤ p.toNat) (U : Nat → BitVec 64)
    {m₁ m₂ : Mem} (h : (p.toNat - b + 32 ≤ x.toNat ∧ x.toNat < p.toNat) ∨ m₁ x = m₂ x) :
    frameM b p U m₁ x = frameM b p U m₂ x := by
  unfold frameM
  rcases h with h | h
  · have hp := p.isLt
    have hq : (p - BitVec.ofNat 64 b + 32).toNat = p.toNat - b + 32 := by
      rw [show (32 : Addr) = BitVec.ofNat 64 32 from rfl,
        toNat_add_ofNat _ _ (by rw [toNat_sub_ofNat _ _ hs]; omega_using [hp, hb, hs]), toNat_sub_ofNat _ _ hs]
    have hz : (x - (p - BitVec.ofNat 64 b + 32)).toNat < b - 32 :=
      (sub_lt_iff (by omega_using [hq, hs, hp, hb])).mpr (by rw [hq]; omega_using [h.1, h.2, hb, hs])
    simp only [lose, zeroOn, Nat.zero_le, true_and, hz, ite_true]
  · exact lose_congr _ (by simp only [zeroOn]; split
                           · rfl
                           · exact write_congr _ h)

/-- `frameM b p` changes no byte outside the `b` bytes below `p`. -/
theorem frameM_out {b : Nat} (hb : 32 < b) {p x : Addr} (hs : b ≤ p.toNat) (U : Nat → BitVec 64) (m : Mem)
    (h : ¬ (p.toNat - b ≤ x.toNat ∧ x.toNat < p.toNat)) : frameM b p U m x = m x := by
  have hp := p.isLt
  have hq := toNat_sub_ofNat p b hs
  have h₁ : ¬ (x - (p - BitVec.ofNat 64 b)).toNat < b := by
    rw [sub_lt_iff (by omega_using [hq, hs, hp])]; rw [hq]; omega_using [h, hs]
  have h₂ : ¬ (x - (p - BitVec.ofNat 64 b)).toNat < 8 := fun h' => h₁ (by omega_using [h', hb])
  have h₃ : ¬ (0 ≤ (x - (p - BitVec.ofNat 64 b + 32)).toNat ∧ (x - (p - BitVec.ofNat 64 b + 32)).toNat < b - 32) := by
    rintro ⟨-, h'⟩
    have e := (off_lt x (p - BitVec.ofNat 64 b) 32 (b - 32) (by omega_using [hb, hp, hs])).mp
    rw [show (32 : Addr) = BitVec.ofNat 64 32 from rfl] at h'
    have := e h'
    exact h₁ (by omega_using [this, hb])
  simp only [frameM, lose_out _ h₁, zeroOn, h₃, ite_false, Mem.write_apply h₂]

/-- A byte `x` the wipe of `cs` from `p` zeroes: from 32 bytes above the
bottom of its `cs.sum` bytes, up to `p`. -/
def Cover (cs : List Nat) (p x : Addr) : Prop := p.toNat - cs.sum + 32 ≤ x.toNat ∧ x.toNat < p.toNat

/-- What the wipe leaves in a byte it zeroes is the same whatever the memory
was; in any other byte, it is a function of the byte. -/
theorem wipeM_congr : ∀ (cs : List Nat) (p : Addr) (U : Nat → BitVec 64) (m₁ m₂ : Mem) (x : Addr),
    ChunksOk cs → cs.sum ≤ p.toNat → (Cover cs p x ∨ m₁ x = m₂ x) →
      wipeM cs p U m₁ x = wipeM cs p U m₂ x
  | [], _, _, _, _, x, _, _, h => by
    rcases h with h | h
    · simp only [Cover, List.sum_nil, Nat.sub_zero] at h; omega_using [h.1, h.2]
    · exact h
  | [c], p, U, m₁, m₂, x, hv, hs, h => by
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at hs
    exact frameM_congr hv.frame.1 hs U (by simpa [Cover] using h)
  | c :: c' :: cs, p, U, m₁, m₂, x, hv, hs, h => by
    have hfc := hv.frame
    have hc' := (hv.1 c' (by simp)).1
    simp only [List.sum_cons] at hs
    have hq : (p - BitVec.ofNat 64 c).toNat = p.toNat - c := toNat_sub_ofNat _ _ (by omega_using [hs, hc'])
    simp only [wipeM]
    refine lose_congr _ (wipeM_congr (c' :: cs) _ _ _ _ x hv.tail (by rw [hq, List.sum_cons]; omega_using [hs, hc']) ?_)
    by_cases hx : p.toNat - c ≤ x.toNat ∧ x.toNat < p.toNat
    · exact .inr (write_congr _ (frameM_congr (b := c + 32) (by omega_using [hfc.1]) (by omega_using [hs, hc']) U
        (.inl (by omega_using [hx.1, hx.2, hs, hc']))))
    · rcases h with h | h
      · refine .inl ?_
        simp only [Cover, List.sum_cons] at h ⊢
        rw [hq]; omega_using [h.1, h.2, hx, hs, hc']
      · exact .inr (write_congr _ (frameM_congr (b := c + 32) (by omega_using [hfc.1]) (by omega_using [hs, hc']) U (.inr h)))

/-- The wipe changes no byte outside the `cs.sum` bytes below `p`. -/
theorem wipeM_out : ∀ (cs : List Nat) (p : Addr) (U : Nat → BitVec 64) (m : Mem) (x : Addr),
    ChunksOk cs → cs.sum ≤ p.toNat → ¬ (p.toNat - cs.sum ≤ x.toNat ∧ x.toNat < p.toNat) →
      wipeM cs p U m x = m x
  | [], _, _, _, _, _, _, _ => rfl
  | [c], p, U, m, x, hv, hs, h => by
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at hs h
    exact frameM_out hv.frame.1 hs U m h
  | c :: c' :: cs, p, U, m, x, hv, hs, h => by
    have hfc := hv.frame
    have hc' := (hv.1 c' (by simp)).1
    have hp := p.isLt
    simp only [List.sum_cons] at hs h
    have hq : (p - BitVec.ofNat 64 c).toNat = p.toNat - c := toNat_sub_ofNat _ _ (by omega_using [hs, hc'])
    have h₁ : ¬ (x - (p - BitVec.ofNat 64 c)).toNat < c := by
      rw [sub_lt_iff (by omega_using [hq, hs, hp])]; rw [hq]; omega_using [h, hs, hc']
    have h₂ : ¬ (x - (p - BitVec.ofNat 64 c)).toNat < 8 := fun h' => h₁ (by omega_using [h', hfc.1])
    simp only [wipeM, lose_out _ h₁]
    rw [wipeM_out (c' :: cs) _ _ _ x hv.tail (by rw [hq, List.sum_cons]; omega_using [hs, hc'])
      (by rw [hq, List.sum_cons]; omega_using [h, hs, hc']), Mem.write_apply h₂]
    exact frameM_out (b := c + 32) (by omega_using [hfc.1]) (by omega_using [hs, hc']) U m
      (by omega_using [h, hs, hc'])

/-! ### The registers -/

/-- What `retFix rb` leaves in `r3`. -/
def fixA (rb : Nat) (x : BitVec 64) : BitVec 64 :=
  if rb = 0 then 0 else if rb < 64 then (x <<< (64 - rb)) >>> (64 - rb) else x

theorem fixA_low {rb : Nat} (hrb : rb ≤ 64) (x : BitVec 64) : (fixA rb x).setWidth rb = x.setWidth rb := by
  unfold fixA
  split
  · next h => subst h; exact BitVec.eq_nil _ |>.trans (BitVec.eq_nil _).symm
  · split
    · ext i hi
      simp only [BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
      simp
      omega
    · next h₁ h₂ => rfl

theorem fixA_hi {rb : Nat} (hrb : rb ≤ 64) (x : BitVec 64) : fixA rb x >>> rb = 0 := by
  unfold fixA
  split
  · simp
  · split
    · ext i hi
      simp only [BitVec.getElem_ushiftRight, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
      simp
      omega
    · next h₁ h₂ =>
      obtain rfl : rb = 64 := by omega
      ext i hi; simp

/-- The general-purpose registers after the clearing `cl`, from `g`. -/
def finG (rb : Nat) (cl : Clear) (g : Reg → BitVec 64) : Reg → BitVec 64 :=
  fun r => if cl.Zeroes r then 0 else if r = .r3 ∧ cl.r3 = true then fixA rb (g .r3) else g r

theorem zeroRs_run : ∀ (rs : List Reg) (u : State),
    execBlock isa (rs.map zeroR) u = some ({ u with gpr := fun r => if r ∈ rs then 0 else u.gpr r }, [])
  | [], u => by simp only [List.map_nil, execBlock, List.not_mem_nil, ite_false]
  | r :: rs, u => by
    simp only [List.map_cons, execBlock, zeroR, isa, exec_li (show 0 < 2 ^ 15 by decide)]
    rw [zeroRs_run rs]
    simp only [Option.map_some, addrs, List.map_nil, List.nil_append, Option.some.injEq, Prod.mk.injEq,
      and_true]
    cases u
    simp only [State.write, State.mk.injEq, and_true]
    funext r'
    by_cases h₁ : r' ∈ rs
    · simp [h₁]
    · by_cases h₂ : r' = r
      · subst h₂; simp
      · simp [h₁, h₂]

theorem zeroVs_run : ∀ (vs : List VReg) (u : State),
    execBlock isa (vs.map zeroV) u = some ({ u with vpr := fun v => if v ∈ vs then 0 else u.vpr v }, [])
  | [], u => by simp only [List.map_nil, execBlock, List.not_mem_nil, ite_false]
  | v :: vs, u => by
    simp only [List.map_cons, execBlock, zeroV, isa, exec, VOp.eval, Option.map_some, BitVec.xor_self]
    rw [zeroVs_run vs]
    simp only [Option.map_some, addrs, List.map_nil, List.nil_append, Option.some.injEq, Prod.mk.injEq,
      and_true]
    cases u
    simp only [State.writeV, State.mk.injEq, and_true, true_and]
    funext v'
    by_cases h₁ : v' ∈ vs
    · simp [h₁]
    · by_cases h₂ : v' = v
      · subst h₂; simp
      · simp [h₁, h₂]

theorem retFix_run {rb : Nat} (u : State) :
    execBlock isa (retFix rb) u =
      some ({ u with gpr := fun r => if r = .r3 then fixA rb (u.gpr .r3) else u.gpr r }, []) := by
  unfold retFix fixA
  split
  · next h =>
    rw [show [zeroR .r3] = [Reg.r3].map zeroR from rfl, zeroRs_run]
    simp only [List.mem_singleton]
  · split
    · next h₁ h₂ =>
      simp only [execBlock, isa, exec_lsl (show 64 - rb < 64 by omega), exec_lsr_d (show 64 - rb < 64 by omega),
        Option.map_some, addrs, List.map_nil, List.nil_append, Option.some.injEq, Prod.mk.injEq, and_true]
      cases u
      simp only [State.write, State.mk.injEq, and_true, ite_true]
      funext r'
      by_cases h : r' = .r3 <;> simp [h]
    · next h₁ h₂ =>
      simp only [execBlock, Option.some.injEq, Prod.mk.injEq, and_true]
      cases u
      simp only [State.mk.injEq, and_true]
      funext r'
      by_cases h : r' = .r3
      · subst h; rfl
      · simp [h]

/-- The last block: CA cleared (by `addc` of `r0`, zero), then the vector
registers `vs`. -/
theorem last_run (u : State) (ca : Bool) (vs : List VReg) (h0 : ca = true → u.gpr .r0 = 0) :
    execBlock isa ((if ca then [.addc .r0 .r0 .r0] else []) ++ vs.map zeroV) u =
      some ({ u with vpr := fun v => if v ∈ vs then 0 else u.vpr v, ca := if ca then false else u.ca },
        []) := by
  cases ca with
  | false =>
    simp only [Bool.false_eq_true, ite_false, List.nil_append]
    rw [zeroVs_run]
  | true =>
    have h0 := h0 rfl
    simp only [ite_true, List.cons_append, List.nil_append, execBlock, isa, exec_addc, h0]
    rw [zeroVs_run]
    simp only [Option.map_some, addrs, List.map_nil, List.nil_append, Option.some.injEq, Prod.mk.injEq,
      and_true]
    cases u
    simp only [State.writeCarry, State.write, State.mk.injEq, true_and]
    refine ⟨?_, by decide⟩
    funext r; split
    · next h => subst h; simpa using h0.symm
    · rfl

/-- The state after the clearing `cl` of the levels `cs` below `p`, from
`u`. -/
def finState (rb : Nat) (cs : List Nat) (cl : Clear) (p : Addr) (u : State) : State :=
  { u with
    gpr := finG rb cl u.gpr, vpr := fun v => if v ∈ cl.vs then 0 else u.vpr v,
    ca := if cl.ca then false else u.ca, mem := wipeM cs p u.unknowns u.mem,
    unknowns := fun n => u.unknowns (n + wipeK cs) }

/-- The trace of `scrubTail rb cs cl` from `r1 = p`: a function of `p`. -/
def tailTr (cs : List Nat) (p : Addr) : List Leak := [] ++ (wipeTr cs p ++ ([] ++ ([] ++ [])))

theorem zeroR0_run (u : State) (b : Bool) :
    execBlock isa (if b then [zeroR .r0] else []) u =
      some ({ u with gpr := fun r => if r = .r0 ∧ b = true then 0 else u.gpr r }, []) := by
  cases b with
  | false => cases u; simp only [Bool.false_eq_true, ite_false, and_false, execBlock]
  | true =>
    simp only [ite_true, and_true]
    rw [show [zeroR .r0] = [Reg.r0].map zeroR from rfl, zeroRs_run]
    simp only [List.mem_singleton]

theorem retFixIf_run {rb : Nat} (u : State) (b : Bool) :
    execBlock isa (if b then retFix rb else []) u =
      some ({ u with gpr := fun r => if r = .r3 ∧ b = true then fixA rb (u.gpr .r3) else u.gpr r }, []) := by
  cases b with
  | false => cases u; simp only [Bool.false_eq_true, ite_false, and_false, execBlock]
  | true => simp only [ite_true, and_true]; exact retFix_run u

/-- The clearing's run, from a state with `cs.sum` bytes below `r1`. -/
theorem tail_run {rb : Nat} {cs : List Nat} {cl : Clear} (hv : ChunksOk cs) (hwf : cl.WF cs) (u : State)
    (hs : cs.sum ≤ u.sp.toNat) :
    Exec isa (scrubTail rb cs cl) u (tailTr cs u.sp) (finState rb cs cl u.sp u) := by
  have h₀ := zeroR0_run u cl.r0
  generalize hu₁ : ({ u with gpr := fun r => if r = .r0 ∧ cl.r0 = true then 0 else u.gpr r } : State) = u₁
    at h₀
  have hsp : u₁.sp = u.sp := by rw [← hu₁]
  have hg₁ : ∀ r, r ≠ .r0 → u₁.gpr r = u.gpr r := fun r hr => by rw [← hu₁]; simp [hr]
  have h0₁ : cl.r0 = true → u₁.gpr .r0 = 0 := fun h => by rw [← hu₁]; simp [h]
  have hcs : cs = [] ∨ u₁.gpr .r0 = 0 := by
    by_cases hc : cs = []
    · exact .inl hc
    · exact .inr (h0₁ (hwf.r0 (.inl hc)))
  obtain ⟨g, hg, hw⟩ := wipe_run cs u₁ hv (hsp ▸ hs) hcs
  generalize hu₂ : ({ u₁ with
      gpr := g, mem := wipeM cs u₁.sp u₁.unknowns u₁.mem,
      unknowns := fun n => u₁.unknowns (n + wipeK cs) } : State) = u₂ at hw
  obtain ⟨u₃, hu₃⟩ : ∃ u₃ : State, u₃ = { u₂ with
      gpr := fun (r : Reg) => if r = Reg.r3 ∧ cl.r3 = true then fixA rb (u₂.gpr .r3) else u₂.gpr r } :=
    ⟨_, rfl⟩
  have h₃ : execBlock isa (if cl.r3 then retFix rb else []) u₂ = some (u₃, []) := by
    rw [hu₃]; exact retFixIf_run u₂ cl.r3
  obtain ⟨u₄, hu₄⟩ : ∃ u₄ : State, u₄ = { u₃ with
      gpr := fun (r : Reg) => if r ∈ cl.gs then 0 else u₃.gpr r } := ⟨_, rfl⟩
  have h₄ : execBlock isa (cl.gs.map zeroR) u₃ = some (u₄, []) := by rw [hu₄]; exact zeroRs_run _ u₃
  have hr0gs : Reg.r0 ∉ cl.gs := fun h => absurd (hwf.gs _ h) (by decide)
  have hr3gs : Reg.r3 ∉ cl.gs := fun h => absurd (hwf.gs _ h) (by decide)
  have h40 : cl.ca = true → u₄.gpr .r0 = 0 := by
    intro hc
    rw [hu₄, hu₃, ← hu₂]
    simp only [hr0gs, ite_false, show Reg.r0 ≠ .r3 by decide, false_and]
    exact (hg .r0 (.inl (by decide))).trans (h0₁ (hwf.r0 (.inr hc)))
  have h₅ := last_run u₄ cl.ca cl.vs h40
  have e := Exec.seq (.block h₀) (.seq hw (.seq (.block h₃) (.seq (.block h₄) (.block h₅))))
  have et : ([] ++ (wipeTr cs u₁.sp ++ ([] ++ ([] ++ [])))) = tailTr cs u.sp := by
    simp only [hsp, tailTr]
  rw [et] at e
  have es : ({ u₄ with
      vpr := fun v => if v ∈ cl.vs then 0 else u₄.vpr v
      ca := if cl.ca then false else u₄.ca } : State) = finState rb cs cl u.sp u := by
    subst hu₄ hu₃ hu₂ hu₁
    simp only [finState]
    congr 1
    funext r
    simp only [finG, Clear.Zeroes]
    by_cases h : r ∈ cl.gs
    · simp [h]
    · by_cases h0 : r = .r0
      · subst h0
        by_cases hb : cl.r0 = true
        · simp [hb, hg .r0 (.inl (by decide))]
        · simp [hb, hg .r0 (.inl (by decide))]
      · have hgr : g r = u.gpr r ∧ g .r3 = u.gpr .r3 := by
          refine ⟨?_, ?_⟩
          · by_cases h12 : r = .r12
            · subst h12
              have hc : cs = [] := by
                by_contra hc; exact h (hwf.r12 hc)
              rw [hg _ (.inr hc)]; simp [h0]
            · rw [hg r (.inl h12)]; simp [h0]
          · rw [hg .r3 (.inl (by decide))]; simp
        simp [h, h0, hgr.1, hgr.2]
  rw [es] at e
  exact e

/-! ### The levels -/

theorem chunksAux_spec : ∀ f n, n / 3968 < f → n % 16 = 0 →
    (chunksAux f n).sum = n ∧ (∀ b ∈ chunksAux f n, min n 64 ≤ b ∧ b ≤ 4048 ∧ b % 16 = 0) ∧
      ∀ b ∈ (chunksAux f n).tail, 64 ≤ b
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _, _ => ⟨rfl, fun _ h => by simp [chunksAux] at h, fun _ h => by simp [chunksAux] at h⟩
  | f + 1, n + 1, h, h16 => by
    simp only [chunksAux]
    split
    · exact ⟨by simp, fun b hb => by simp at hb; subst hb; omega_arith, fun _ hb => by simp at hb⟩
    · split
      · obtain ⟨hs, hv, -⟩ := chunksAux_spec f (n + 1 - 4032) (by omega_arith) (by omega_arith)
        refine ⟨by rw [List.sum_cons, hs]; omega_arith, fun b hb => ?_, fun b hb => ?_⟩
        · rcases List.mem_cons.mp hb with rfl | hb
          · omega_arith
          · have := hv b hb; omega_arith
        · simp only [List.tail_cons] at hb; have := hv b hb; omega_arith
      · obtain ⟨hs, hv, -⟩ := chunksAux_spec f (n + 1 - 3968) (by omega_arith) (by omega_arith)
        refine ⟨by rw [List.sum_cons, hs]; omega_arith, fun b hb => ?_, fun b hb => ?_⟩
        · rcases List.mem_cons.mp hb with rfl | hb
          · omega_arith
          · have := hv b hb; omega_arith
        · simp only [List.tail_cons] at hb; have := hv b hb; omega_arith

theorem chunks_sum {n : Nat} (h16 : n % 16 = 0) : (chunks n).sum = n :=
  (chunksAux_spec (n / 3968 + 1) n (by omega_using []) h16).1

theorem chunks_ok {n : Nat} (h16 : n % 16 = 0) (h48 : n = 0 ∨ 48 ≤ n) : ChunksOk (chunks n) := by
  obtain ⟨-, hv, ht⟩ := chunksAux_spec (n / 3968 + 1) n (by omega_using []) h16
  refine ⟨fun b hb => ?_, ht⟩
  have := hv b hb
  rcases h48 with rfl | h48
  · simp [chunks, chunksAux] at hb
  · omega_using [this, h48]

/-! ## What `Sig.contract` gives -/

/-- What `Verified.scrub` needs of the calling convention a contract is for:
`abi`'s, possibly with tables of constants (`Abi.withConsts`), which add
readable regions apart from the stack the function uses, and with tables of
functions (`Abi.withTables`). -/
structure ScrubAbi (A : Abi isa) : Prop where
  ptrBits : A.ptrBits = 64
  reserved : A.reserved = abi.reserved
  wr : ∀ s, A.wr s = s.wr
  wf : ∀ ws n s, A.wf ws n s → (n = 0 ∨ n ≤ s.sp.toNat) ∧
    ∀ r ∈ s.rd, r ∉ A.rd s → ∀ q ∈ abi.reserved n s, q.Disjoint r
  pub : ∀ s₁ s₂, A.pub s₁ s₂ → s₁.sp = s₂.sp
  mem : ∀ s, A.mem s = s.mem
  ret : ∀ s, A.ret s = s.gpr .r3
  rdSub : ∀ s r, r ∈ A.rd s → r ∈ s.rd
  argsLen : ∀ ws f, A.args ws = some f → ∀ s, (f s).length = ws.length

theorem abi_args_len (ws : List Nat) (f : State → List (BitVec 64)) (h : abi.args ws = some f) (s : State) :
    (f s).length = ws.length := by
  have h8 : argRegs.length = 8 := rfl
  simp only [abi] at h
  split at h
  · next hl => cases h; simp only [List.length_map, List.length_take]; omega_using [hl, h8]
  · next hl =>
    split at h
    · cases h; simp only [List.length_append, List.length_map, List.length_range]; omega_using [hl, h8]
    · cases h

theorem abi_wf_stack {ws : List Nat} {n : Nat} {s : State} (h : abi.wf ws n s) :
    n = 0 ∨ n ≤ s.sp.toNat := by
  simp only [abi] at h
  split at h
  · cases n with
    | zero => exact .inl rfl
    | succ n => exact .inr h
  · cases n with
    | zero => exact .inl rfl
    | succ n => exact .inr h.1

theorem ScrubAbi.plain : ScrubAbi abi :=
  ⟨rfl, rfl, fun _ => rfl, fun _ _ _ h => ⟨abi_wf_stack h, fun _ hr hn => absurd hr hn⟩,
    fun _ _ h => h, fun _ => rfl, fun _ => rfl, fun _ _ h => h, abi_args_len⟩

theorem ScrubAbi.consts (cs : List (String × List (BitVec 64))) : ScrubAbi (abi.withConsts cs) := by
  cases cs with
  | nil => exact ScrubAbi.plain
  | cons c cs =>
    refine ⟨rfl, rfl, fun _ => rfl, fun ws n s h => ?_, fun _ _ h => h.1, fun _ => rfl, fun _ => rfl,
      fun _ _ h => List.mem_of_mem_take h, abi_args_len⟩
    obtain ⟨hw, hdrop, -, hdis, -⟩ := h
    refine ⟨abi_wf_stack hw, fun r hr hn q hq => ?_⟩
    have hr' : r ∈ (abi.rd s).drop ((abi.rd s).length - (c :: cs).length) := by
      change r ∈ abi.rd s at hr
      rw [← List.take_append_drop ((abi.rd s).length - (c :: cs).length) (abi.rd s)] at hr
      rcases List.mem_append.mp hr with h | h
      · exact absurd h hn
      · exact h
    rw [hdrop] at hr'
    exact ((hdis r hr').2.2 q hq).symm

theorem ScrubAbi.tables {A : Abi isa} (hA : ScrubAbi A) (sig : Sig) (ts : List (String × List FnTable)) :
    ScrubAbi (A.withTables sig ts) := by
  cases ts with
  | nil => exact hA
  | cons t ts =>
    exact ⟨hA.ptrBits, hA.reserved, hA.wr, fun ws n s h => hA.wf ws n s h.1,
      fun s₁ s₂ h => hA.pub s₁ s₂ h.1, hA.mem, hA.ret, hA.rdSub, hA.argsLen⟩

/-- The calling convention of every PPC64LE artifact (`Api.artifact`). -/
theorem ScrubAbi.of (cs : List (String × List (BitVec 64))) (sig : Sig) (ts : List (String × List FnTable)) :
    ScrubAbi ((abi.withConsts cs).withTables sig ts) :=
  (ScrubAbi.consts cs).tables sig ts

section
variable {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
  {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
  {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}

/-- The stack the function may use does not wrap around, and is apart from
every region it may access. -/
theorem contract_pre_scrub (hA : ScrubAbi A) {s : State}
    (h : (sig.contract A pre post wa stack leak).pre s) :
    (stack = 0 ∨ stack ≤ s.sp.toNat) ∧
      ∀ r ∈ s.rd ++ s.wr, stack ≠ 0 → (below s.sp stack).Disjoint r := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  rename_i vals _
  obtain ⟨hwf, hrd, hwr, -, hres, -⟩ := h
  obtain ⟨hst, hcon⟩ := hA.wf _ _ _ hwf
  have hres' : ∀ r ∈ abi.reserved stack s, ∀ a ∈ (Sig.bufs sig.params (vals s) ++
      (Sig.lists A.ptrBits (A.mem s) sig.params (vals s)).map fun r => (r, false)) ++
      (A.argArea ((sig.words A.ptrBits).map (·.bits A.ptrBits)) s).map
        (fun (r, w) => (r, w && wa)), r.Disjoint a.1 := by
    rw [← hA.reserved]; exact hres
  have key : ∀ r ∈ s.rd ++ s.wr, ∀ q ∈ abi.reserved stack s, q.Disjoint r := by
    intro r hr q hq
    rcases List.mem_append.mp hr with hr | hr
    · by_cases hn : r ∈ A.rd s
      · rw [hrd] at hn
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hn
        exact hres' q hq a (List.mem_filter.mp ha).1
      · exact hcon r hr hn q hq
    · rw [← hA.wr, hwr] at hr
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      exact hres' q hq a (List.mem_filter.mp ha).1
  refine ⟨hst, fun r hr hn => key r hr _ ?_⟩
  cases stack with
  | zero => exact absurd rfl hn
  | succ n => simp [abi, stackBelow]

theorem contract_pub_sp (hA : ScrubAbi A) {s₁ s₂ : State}
    (h : (sig.contract A pre post wa stack leak).pub s₁ s₂) : s₁.sp = s₂.sp := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  · cases leak with
    | none => exact hA.pub _ _ h.1
    | some f => exact hA.pub _ _ h.1.1

end

/-! ## The result -/

/-- A postcondition that reads the memory on return only within the
buffers, and of the result only its `rb` bits. -/
def PostOut (k : Contract isa) (rb : Nat) : Prop :=
  ∀ s u u', k.pre s → k.post s u →
    (∀ x, (∃ r ∈ s.rd ++ s.wr, r.Contains x 1) → u'.mem x = u.mem x) →
    (u'.gpr .r3).setWidth rb = (u.gpr .r3).setWidth rb → k.post s u'

/-- `PostOut` of a contract `Sig.contract` derives, from its postcondition's
reading the memory on return only within the buffers. -/
theorem postOut_of_local {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    (hl : ∀ vs m m₁ m₂ r, vs.length = (sig.words A.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words A.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words A.ptrBits) post vs m m₂ r) :
    PostOut (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits) := by
  intro s u u' hs hp hm hr
  simp only [Sig.contract] at hs hp ⊢
  revert hs hp
  cases hargs : A.args ((sig.words A.ptrBits).map (·.bits A.ptrBits)) with
  | none => intro hs; exact hs.elim
  | some vals =>
    intro hs hp
    simp only at hs hp ⊢
    obtain ⟨-, hrd, hwr, -⟩ := hs
    rw [hA.ret, hA.mem, hA.mem] at hp ⊢
    rw [hr]
    refine hl (vals s) _ _ _ _ (by rw [hA.argsLen _ _ hargs s, List.length_map]) (fun b hb a ha => ?_) hp
    have hin : b.1 ∈ s.rd ++ s.wr := by
      cases hw : b.2
      · apply List.mem_append_left; apply hA.rdSub; rw [hrd]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          by simp [hw]⟩, rfl⟩
      · apply List.mem_append_right; rw [← hA.wr, hwr]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          hw⟩, rfl⟩
    exact (hm a ⟨b.1, hin, ha⟩).symm

theorem not_scratch_preserved : ∀ r ∈ preserved, ¬ (r = .r0 ∨ r ∈ scratchRegs) ∧ r ≠ .r3 := by decide

/-- A clearing zeroes no register the contract preserves, nor `r3`. -/
theorem Clear.not_zeroes {cl : Clear} {cs : List Nat} (hwf : cl.WF cs) {r : Reg}
    (h : r ∈ preserved ∨ r = .r3) : ¬ cl.Zeroes r := by
  rintro (⟨rfl, -⟩ | hg)
  · rcases h with h | h
    · exact (not_scratch_preserved _ h).1 (.inl rfl)
    · exact absurd h (by decide)
  · have hs := hwf.gs r hg
    rcases h with h | rfl
    · exact (not_scratch_preserved _ h).1 (.inr hs)
    · exact absurd hs (by decide)

/-- The registers the clearing leaves as they were are the ones the
contract preserves. -/
theorem kept_preserved (r : Reg) (h₁ : ¬ (r = .r0 ∨ r ∈ scratchRegs)) (h₂ : r ≠ .r3) : r ∈ preserved := by
  revert h₁ h₂; cases r <;> decide

/-- A byte of a buffer, which is apart from the stack the function may use,
is not in the `d ≤ stack` bytes below `sp`. -/
theorem out_below {sp x : Addr} {stack d : Nat} (hd : d ≤ stack) (hs : stack ≤ sp.toNat) {r : Region}
    (hdis : (below sp stack).Disjoint r) (hx : r.Contains x 1) :
    ¬ (sp.toNat - d ≤ x.toNat ∧ x.toNat < sp.toNat) := by
  intro h
  have hp := sp.isLt
  have hq := toNat_sub_ofNat sp stack hs
  refine hdis x ?_ hx
  simp only [Region.Contains]
  have := (sub_lt_iff (a := sp - BitVec.ofNat 64 stack) (x := x) (n := stack) (by omega_using [hq, hs, hp])).mpr
    (by rw [hq]; omega_using [h, hd, hs])
  omega_using [this]

/-- Code `c` verified against a contract that `Sig.contract` derives,
followed by the clearing of the volatile registers and of the stack below
`r1` in the levels `cs` (`scrubTail`), within the contract's stack: verified
against the same contract, and without secret residue, if the postcondition
reads the memory on return only within the buffers (`hpost`) and two runs
of `c` that may differ only in what the contract keeps secret leave the same
unknowns and memories that agree outside the buffers and the stack the
clearing zeroes (`hag`). `Verified.scrub` gives `hag` for code whose frames
the clearing wipes whole (`Exec.agree`); code that clears its own frames
needs none wiped (`cs = []`). -/
theorem Verified.scrubOf {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {c : Prog isa} {cs : List Nat}
    {cl : Clear}
    (hA : ScrubAbi A) (h : Verified target c (sig.contract A pre post wa stack leak))
    (hv : ChunksOk cs) (hcs : cs.sum ≤ stack) (hwf : cl.WF cs) (hk : cl.Keeps c)
    (hrb : sig.retBits A.ptrBits ≤ 64)
    (hpost : PostOut (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits))
    (hag : ∀ s₁ s₂ t₁ t₂ u₁ u₂, (sig.contract A pre post wa stack leak).pre s₁ →
      (sig.contract A pre post wa stack leak).pre s₂ → (sig.contract A pre post wa stack leak).pub s₁ s₂ →
      Outside 0 s₁ s₂ → s₁.unknowns = s₂.unknowns → Exec isa c s₁ t₁ u₁ → Exec isa c s₂ t₂ u₂ →
      u₁.unknowns = u₂.unknowns ∧
        ∀ x, (∀ r ∈ s₁.rd ++ s₁.wr, ¬ r.Contains x 1) → ¬ Cover cs s₁.sp x → u₁.mem x = u₂.mem x) :
    Verified target (.seq c (scrubTail (sig.retBits A.ptrBits) cs cl)) (sig.contract A pre post wa stack leak) ∧
      NoResidue (.seq c (scrubTail (sig.retBits A.ptrBits) cs cl))
        (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits) := by
  obtain ⟨hcor, hct, hsat⟩ := h
  -- The stack the clearing wipes does not wrap around.
  have hD : ∀ s, (sig.contract A pre post wa stack leak).pre s → cs.sum ≤ s.sp.toNat := by
    intro s hs
    rcases (contract_pre_scrub hA hs).1 with h0 | h0
    · omega_using [h0, hcs]
    · omega_using [h0, hcs]
  -- What a run of `c` gives.
  have run : ∀ s t u, (sig.contract A pre post wa stack leak).pre s → Exec isa c s t u →
      abiPreserved s u ∧ (sig.contract A pre post wa stack leak).post s u ∧ u.sp = s.sp := by
    intro s t u hs he
    obtain ⟨t', u', he', ha, hp⟩ := hcor s hs
    obtain ⟨-, rfl⟩ := Exec.det he he'
    exact ⟨ha, hp, ha.2.1⟩
  -- The clearing's run after it.
  have tail : ∀ s t u, (sig.contract A pre post wa stack leak).pre s → Exec isa c s t u →
      Exec isa (scrubTail (sig.retBits A.ptrBits) cs cl) u (tailTr cs s.sp)
        (finState (sig.retBits A.ptrBits) cs cl s.sp u) := by
    intro s t u hs he
    obtain ⟨-, -, hsp⟩ := run s t u hs he
    have e := tail_run (rb := sig.retBits A.ptrBits) hv hwf u (by rw [hsp]; exact hD s hs)
    rw [hsp] at e
    exact e
  -- The buffers are apart from the stack the clearing wipes.
  have outB : ∀ s, (sig.contract A pre post wa stack leak).pre s → ∀ x,
      (∃ r ∈ s.rd ++ s.wr, r.Contains x 1) →
        ¬ (s.sp.toNat - cs.sum ≤ x.toNat ∧ x.toNat < s.sp.toNat) := by
    intro s hs x ⟨r, hr, hx⟩
    obtain ⟨hst, hdis⟩ := contract_pre_scrub hA hs
    by_cases h0 : stack = 0
    · intro h'; omega_using [h', hcs, h0]
    · exact out_below hcs (by omega_using [hst, h0]) (hdis r hr h0) hx
  refine ⟨⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩,
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp ho hun hund e₁ e₂ => ?_⟩
  · -- Correctness.
    obtain ⟨t, u, he, -⟩ := hcor s hs
    obtain ⟨ha, hq, hsp⟩ := run s t u hs he
    refine ⟨_, _, .seq he (tail s t u hs he), ⟨fun r hr => ?_, hsp, ha.2.2⟩, ?_⟩
    · simp only [finState, finG, Clear.not_zeroes hwf (.inl hr), ite_false,
        (not_scratch_preserved r hr).2, false_and]
      exact ha.1 r hr
    · refine hpost s u _ hs hq (fun x hx => ?_) ?_
      · show wipeM cs s.sp u.unknowns u.mem x = u.mem x
        exact wipeM_out _ _ _ _ _ hv (hD s hs) (outB s hs x hx)
      · show (finG (sig.retBits A.ptrBits) cl u.gpr .r3).setWidth _ = _
        simp only [finG, Clear.not_zeroes hwf (.inr rfl), ite_false, true_and]
        split
        · exact fixA_low hrb _
        · rfl
  · -- Constant time.
    cases e₁ with | seq a₁ b₁ =>
    cases e₂ with | seq a₂ b₂ =>
    obtain ⟨rfl, -⟩ := Exec.det b₁ (tail s₁ _ _ h₁ a₁)
    obtain ⟨rfl, -⟩ := Exec.det b₂ (tail s₂ _ _ h₂ a₂)
    rw [hct _ _ _ _ _ _ h₁ h₂ hp a₁ a₂, contract_pub_sp hA hp]
  · -- No residue.
    cases e₁ with | seq a₁ b₁ =>
    cases e₂ with | seq a₂ b₂ =>
    rename_i u₁ _ _ u₂ _ _
    obtain ⟨-, rfl⟩ := Exec.det b₁ (tail s₁ _ _ h₁ a₁)
    obtain ⟨-, rfl⟩ := Exec.det b₂ (tail s₂ _ _ h₂ a₂)
    obtain ⟨ha₁, -, hsp₁⟩ := run s₁ _ _ h₁ a₁
    obtain ⟨ha₂, -, hsp₂⟩ := run s₂ _ _ h₂ a₂
    obtain ⟨hU, hA'⟩ := hag s₁ s₂ _ _ _ _ h₁ h₂ hp ho hun a₁ a₂
    obtain ⟨hg₁, -, hv₁, hc₁⟩ := hk s₁ _ _ a₁
    obtain ⟨hg₂, -, hv₂, hc₂⟩ := hk s₂ _ _ a₂
    have hk3 := fun h => And.intro ((hk s₁ _ _ a₁).2.1 h) ((hk s₂ _ _ a₂).2.1 h)
    obtain ⟨hrd, hwr, hg, hr3, hvp, hlr, hsp, hca, -⟩ := ho
    obtain ⟨rd₁, wr₁, -⟩ := Exec.rdwr a₁
    obtain ⟨rd₂, wr₂, -⟩ := Exec.rdwr a₂
    refine ⟨show u₁.rd = u₂.rd by simp only [rd₁, rd₂, hrd], show u₁.wr = u₂.wr by simp only [wr₁, wr₂, hwr],
      fun r hr => ?_, ?_, ?_, show u₁.lr = u₂.lr by rw [ha₁.2.2, ha₂.2.2, hlr],
      show u₁.sp = u₂.sp by rw [hsp₁, hsp₂, hsp], ?_, fun x hx => ?_⟩
    · show finG _ cl u₁.gpr r = finG _ cl u₂.gpr r
      simp only [finG, hr, false_and, ite_false]
      split
      · rfl
      · next hz =>
        by_cases hv : r = .r0 ∨ r ∈ scratchRegs
        · rw [hg₁ r hr hv hz, hg₂ r hr hv hz]; exact hg r hr
        · have hk := kept_preserved r hv hr
          rw [ha₁.1 r hk, ha₂.1 r hk]; exact hg r hr
    · show finG _ cl u₁.gpr .r3 >>> _ = finG _ cl u₂.gpr .r3 >>> _
      simp only [finG, Clear.not_zeroes hwf (.inr rfl), ite_false, true_and]
      split
      · rw [fixA_hi hrb, fixA_hi hrb]
      · next h3 =>
        obtain ⟨e₁, e₂⟩ := hk3 (by simpa using h3)
        rw [e₁, e₂]
        simp only [BitVec.ushiftRight_zero] at hr3
        rw [hr3]
    · show (fun v => if v ∈ cl.vs then 0 else u₁.vpr v) = fun v => if v ∈ cl.vs then 0 else u₂.vpr v
      funext v
      split
      · rfl
      · next hv => rw [hv₁ v hv, hv₂ v hv, hvp]
    · show (if cl.ca then false else u₁.ca) = if cl.ca then false else u₂.ca
      split
      · rfl
      · next hc => rw [hc₁ (by simpa using hc), hc₂ (by simpa using hc), hca]
    · show wipeM cs s₁.sp u₁.unknowns u₁.mem x = wipeM cs s₂.sp u₂.unknowns u₂.mem x
      rw [← hsp, hU]
      have hx' : ∀ r ∈ s₁.rd ++ s₁.wr, ¬ r.Contains x 1 := by
        have := hx; simp only [finState, rd₁, wr₁] at this; exact this
      refine wipeM_congr _ _ _ _ _ x hv (hD s₁ h₁) ?_
      by_cases hz : Cover cs s₁.sp x
      · exact .inl hz
      · exact .inr (hA' x hx' hz)

/-- Code verified against a contract that `Sig.contract` derives, whose
frames use at most `stack` bytes, run by `scrub`, which clears the stack its
frames may have written and the volatile registers: verified against the
same contract, and without secret residue, if the postcondition reads the
memory on return only within the buffers (`hpost`). -/
theorem Verified.scrub {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {c : Prog isa}
    (hA : ScrubAbi A) (h : Verified target c (sig.contract A pre post wa stack leak))
    (hd : c.ppc64leDepth ≤ stack) (h16 : c.ppc64leDepth % 16 = 0)
    (h48 : c.ppc64leDepth = 0 ∨ 48 ≤ c.ppc64leDepth)
    (hsy : ∀ s₁ s₂, (sig.contract A pre post wa stack leak).pub s₁ s₂ →
      ∀ n ∈ inames c, s₁.syms n = s₂.syms n) (hrb : sig.retBits A.ptrBits ≤ 64)
    (hpost : PostOut (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits)) :
    Verified target (Impl.Scrub.PPC64LE.scrub (sig.retBits A.ptrBits) c.ppc64leDepth
          (Clear.of c (chunks c.ppc64leDepth)) c)
        (sig.contract A pre post wa stack leak) ∧
      NoResidue (Impl.Scrub.PPC64LE.scrub (sig.retBits A.ptrBits) c.ppc64leDepth
          (Clear.of c (chunks c.ppc64leDepth)) c)
        (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits) := by
  have hsum := chunks_sum h16
  refine Verified.scrubOf hA h (chunks_ok h16 h48) (by rw [hsum]; exact hd) (Clear.of_wf _ _)
    (Clear.of_keep _ _) hrb hpost ?_
  -- The two runs of `c` have the same trace, end with the same unknowns, and
  -- leave memories that agree but in the stack their frames may write.
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp ho hun a₁ a₂
  have hD₁ : c.ppc64leDepth ≤ s₁.sp.toNat := by
    rcases (contract_pre_scrub hA h₁).1 with h0 | h0
    · omega_using [h0, hd]
    · omega_using [h0, hd]
  have hL : (s₁.sp - BitVec.ofNat 64 c.ppc64leDepth).toNat = s₁.sp.toNat - c.ppc64leDepth :=
    toNat_sub_ofNat _ _ hD₁
  obtain ⟨-, hwr, -, -, -, -, hsp, -, hm⟩ := ho
  obtain ⟨-, hU, hA'⟩ := Exec.agree (R := s₁.rd ++ s₁.wr) (L := s₁.sp - BitVec.ofNat 64 c.ppc64leDepth)
    (T := s₁.sp) a₁ [] [] a₂ (hsy _ _ hp) hsp hwr hun (fun r hr => .inl (List.mem_append_right _ hr))
    (by rw [hL]; omega_using [hD₁]) (Nat.le_refl _) (fun x hx _ => hm x hx)
    (by rw [List.append_nil, List.append_nil]; exact (h.2.1) _ _ _ _ _ _ h₁ h₂ hp a₁ a₂)
  refine ⟨hU, fun x hx hc => hA' x hx fun hz => hc ?_⟩
  simp only [Cover, hsum]; simp only [InZ, hL] at hz; exact hz

/-! ## Registering scrubbed code -/

/-- No modelled instruction writes `r1` but as a frame's push or pop. -/
theorem spSafe_all (c : Prog isa) : c.all (fun i => !isa.writesSp i) = true := by
  induction c <;> simp_all [Code.all]

/-- The result's width, of `r`'s function. -/
abbrev retBitsOf {api : Api} (r : Registration api target) : Nat :=
  api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits

theorem contract_pub {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {s₁ s₂ : State}
    (h : (sig.contract A pre post wa stack leak).pub s₁ s₂) : A.pub s₁ s₂ := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  · cases leak with
    | none => exact h.1
    | some f => exact h.1.1

/-- The functions of the tables have the same addresses in two runs that
agree on what is public. -/
theorem tables_pub_syms {A : Abi isa} {sig : Sig} {ts : List (String × List FnTable)}
    {s₁ s₂ : State} (h : (A.withTables sig ts).pub s₁ s₂) :
    ∀ f ∈ tableFns ts, s₁.syms f = s₂.syms f := by
  intro f hf
  cases ts with
  | nil => simp [tableFns] at hf
  | cons t ts => exact h.2.1 f hf

/-- `r`'s code, scrubbed, is verified against `r`'s contract and returns
without secret residue. -/
theorem scrubCode_ok {api : Api} (r : Registration api target)
    (hd : r.code.ppc64leDepth ≤ r.stack) (h16 : r.code.ppc64leDepth % 16 = 0)
    (h48 : r.code.ppc64leDepth = 0 ∨ 48 ≤ r.code.ppc64leDepth) (htc : tablesCall r.code r.tables = true)
    (hrb : retBitsOf r ≤ 64) (hpost : PostOut r.contract (retBitsOf r)) :
    Verified target (scrub (retBitsOf r) r.code.ppc64leDepth
        (Clear.of r.code (chunks r.code.ppc64leDepth)) r.code) r.contract ∧
      NoResidue (scrub (retBitsOf r) r.code.ppc64leDepth
        (Clear.of r.code (chunks r.code.ppc64leDepth)) r.code) r.contract (retBitsOf r) := by
  obtain ⟨pre, post, leak, e⟩ := r.ofSig
  have hv := r.verified
  have hp := hpost
  unfold retBitsOf at hrb hp ⊢
  rw [e] at hv hp ⊢
  have hrb' := hrb
  refine Verified.scrub (ScrubAbi.of r.consts api.sig r.tables) hv hd h16 h48
    (fun s₁ s₂ hp n hn => tables_pub_syms (contract_pub hp) n ?_) hrb' hp
  simpa using List.all_eq_true.mp htc n hn

/-- `r`, scrubbed: its code followed by the clearing (`scrub`) of the stack
its frames use and its volatile registers. -/
def scrubReg {api : Api} (r : Registration api target)
    (hd : r.code.ppc64leDepth ≤ r.stack) (h16 : r.code.ppc64leDepth % 16 = 0)
    (h48 : r.code.ppc64leDepth = 0 ∨ 48 ≤ r.code.ppc64leDepth) (htc : tablesCall r.code r.tables = true)
    (hrb : retBitsOf r ≤ 64) (hpost : PostOut r.contract (retBitsOf r)) (hw : r.written = []) :
    Registration api target where
  suffix := r.suffix
  tables := r.tables
  code := scrub (retBitsOf r) r.code.ppc64leDepth (Clear.of r.code (chunks r.code.ppc64leDepth)) r.code
  contract := r.contract
  verified := (scrubCode_ok r hd h16 h48 htc hrb hpost).1
  consts := r.consts
  stack := r.stack
  ofApi := r.ofApi
  ofSig := r.ofSig
  spSafe := spSafe_all _
  written := r.written
  writtenOk := by rw [hw]; exact fun _ _ _ _ _ => True.intro
  extra := r.extra
  vendor := r.vendor
  notWith := r.notWith
  residue := some ⟨(scrubCode_ok r hd h16 h48 htc hrb hpost).2⟩

/-- `r`, returning without secret residue (`scrubReg`) if `scrub`'s side
conditions hold: its frames use at most `r.stack` bytes, it calls
indirectly only the functions of its tables (`tablesCall`), and it states
no `written`; otherwise `r` itself, which then has no proof (`Registration.residue`), as the emitter
allows only of what `ci/residue_allowlist.txt` lists. -/
def withScrub {api : Api} (r : Registration api target) (hpost : PostOut r.contract (retBitsOf r)) :
    Registration api target :=
  if hd : r.code.ppc64leDepth ≤ r.stack then
  if h16 : r.code.ppc64leDepth % 16 = 0 then
  if h48 : r.code.ppc64leDepth = 0 ∨ 48 ≤ r.code.ppc64leDepth then
  if htc : tablesCall r.code r.tables = true then
  if hrb : retBitsOf r ≤ 64 then
  if hw : r.written = [] then scrubReg r hd h16 h48 htc hrb hpost hw
  else r else r else r else r else r else r

end Scrub

end VG.PPC64LE
