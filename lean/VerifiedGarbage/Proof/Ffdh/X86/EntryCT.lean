module

public import VerifiedGarbage.Proof.Ffdh.X86.Entry
public import VerifiedGarbage.Proof.Bignum.X86.PublicArgumentTiming
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeBase
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.EntryTiming
import VerifiedGarbage.Proof.Bignum.X86.CrtEntryTiming
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Syms
public import VerifiedGarbage.Proof.Framework.X86.Taint

/-!
# FFDH on i686: the trace of the entry and the return

`wrap_trace`: two runs of `wrap a body` from entry states with the same
arguments and `esp` leak the same trace when the runs of `body` from the
states it starts in (`BodyAt`) do. The entry's load of the working space is
`Crt.entry`'s, the frame's filling reads and writes at offsets of `esp`
only (checked by the taint analysis from `esp`), and the return restores
the registers from the working space, at the same `edi` in both runs.

The synthetic arguments lie in the frame, which is writable, so the taint
analysis would not take them as public: the body's runs are related from
states whose permissions are narrowed to the working space (`narrow_body`),
on which `ArgsOk` holds (`BodyAt.argsOk`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.CrtRt (In)
open VG.Impl.Ffdh.X86 (Args argsFrame fill entry wrap)
open VG.Proof.Dsa.X86 (argumentPointer stackValue wp_result scratchArgument_relCT checkedProgramChange)

/-- What `body` runs from in `wrap a body`, entered at `s`. -/
def BodyAt (Ex : List Region → List Region → Prop) (a : Args) (s f : State) : Prop :=
  In Ex (wsBase a s) (wsSize a s) (pLenOf a s) (synth a (arg s)) f ∧
    f.gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame ∧ f.rd = s.rd ∧
    f.wr = ⟨frameAt s, argsFrame⟩ :: s.wr ∧
    Frame [⟨wsBase a s, wsSize a s⟩, ⟨frameAt s, argsFrame⟩] s.mem f.mem

theorem entry_relCT (a : Args) :
    RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ stackValue s a.ws = stackValue t a.ws ∧
      readSrc s (.mem (PublicFn.argument a.ws)) = some (stackValue s a.ws) ∧
      readSrc t (.mem (PublicFn.argument a.ws)) = some (stackValue t a.ws))
      (.block (entry a)) (VG.X86.Taint.Agree argumentTaint) := by
  unfold entry
  rw [List.append_assoc]
  apply VG.RelCT.block_append
  exact VG.RelCT.seq (scratchArgument_relCT a.ws)
    (checkedProgramChange (τ' := { argumentTaint with regs := .ofList [.esp, .edi, .eax] })
      (hint := .block []) rfl rfl)

theorem freed_of_pop {bytes : Nat} {s₁ s₂ s₃ : State} (h : isa.pop (.free bytes) s₁ s₂ = some s₃) :
    s₃ = freed bytes s₂ := by
  simp only [isa, pop] at h
  split at h <;> [cases h; cases h]
  rfl

/-- Two runs of `wrap a body` leak the same trace when the runs of `body` do, from states that name
the statics where the entry's do. -/
theorem wrap_trace_syms {a : Args} {n : Nat} {s t : State} (A : WrapABI a n s) (B : WrapABI a n t)
    (args : ∀ i < n, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp) {body : Prog isa}
    {Ex₁ Ex₂ : List Region → List Region → Prop} (hx₁ : Ex₁ s.rd (⟨frameAt s, argsFrame⟩ :: s.wr))
    (hx₂ : Ex₂ t.rd (⟨frameAt t, argsFrame⟩ :: t.wr))
    (hfill : (VG.Taint.check taint (τr [.esp]) (.block (fill a)) (.block [])).isSome = true)
    (hw₁ : ∀ f, BodyAt Ex₁ a s f → f.syms = s.syms →
      WP isa body f fun u => Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] f u)
    (hw₂ : ∀ f, BodyAt Ex₂ a t f → f.syms = t.syms →
      WP isa body f fun u => Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] f u)
    (hb : RelCT isa (fun f g => (BodyAt Ex₁ a s f ∧ f.syms = s.syms) ∧ (BodyAt Ex₂ a t g ∧ g.syms = t.syms)) body
      fun _ _ => True)
    {tr ur : List Leak} {sf tf : State} (E : Exec isa (wrap a body) s tr sf)
    (F : Exec isa (wrap a body) t ur tf) : tr = ur := by
  have ws := args a.ws (by have := A.below.ws; omega)
  have wsl := args (a.ws + 1) (by have := A.below.ws; omega)
  have baseEq : wsBase a s = wsBase a t := by simp only [wsBase, argumentPointer, ws]
  unfold wrap at E F
  cases E with
  | @seq _ _ _ u _ _ _ E1 Erest =>
    cases F with
    | @seq _ _ _ v _ _ _ F1 Frest =>
      have T1 := (entry_relCT a _ _ _ _ _ _ ⟨SP, ws,
        (A.argument (i := a.ws) (by have := A.below.ws; omega)).readSrc,
        (B.argument (i := a.ws) (by have := B.below.ws; omega)).readSrc⟩ E1 F1).1
      obtain ⟨Su, -, Ku, Ou⟩ := wp_result (entry_ok A) E1
      obtain ⟨Sv, -, Kv, Ov⟩ := wp_result (entry_ok B) F1
      cases Erest with
      | @seq _ _ _ w _ _ _ E2 E3 =>
        cases Frest with
        | @seq _ _ _ z _ _ _ F2 F3 =>
          cases E2 with
          | frame p₁ b₁ q₁ =>
            cases F2 with
            | frame p₂ b₂ q₂ =>
              have ea := alloc_some p₁
              have eb := alloc_some p₂
              subst ea eb
              have fw := freed_of_pop q₁
              have fz := freed_of_pop q₂
              cases b₁ with
              | @seq _ _ _ f₁ _ _ _ B1 B2 =>
                cases b₂ with
                | @seq _ _ _ f₂ _ _ _ C1 C2 =>
                  have T2 := (RelCT.taint (A := taint) (τr [.esp]) (P := fun x y => x.gpr .esp = y.gpr .esp)
                    (fun x y h => agree_regs fun r hr => by
                      obtain rfl := List.mem_singleton.mp hr; exact h) hfill _ _ _ _ _ _
                    (show (allocFrame argsFrame u).gpr .esp = (allocFrame argsFrame v).gpr .esp by
                      rw [allocFrame_esp, allocFrame_esp, Ku.1 _ (by decide), Kv.1 _ (by decide), SP]) B1 C1).1
                  have body₁ : WP isa (.block (fill a ++ [])) (allocFrame argsFrame u) fun f =>
                      BodyAt Ex₁ a s f ∧ f.gpr .edi = u.gpr .edi :=
                    frameIn_ok A Su Ku Ou hx₁ fun f I espf rdf wrf Ft _ regs =>
                      WP.block_nil ⟨⟨I, espf, rdf, wrf, Ft⟩, regs _ (by decide) (by decide) (by decide)⟩
                  have body₂ : WP isa (.block (fill a ++ [])) (allocFrame argsFrame v) fun f =>
                      BodyAt Ex₂ a t f ∧ f.gpr .edi = v.gpr .edi :=
                    frameIn_ok B Sv Kv Ov hx₂ fun f I espf rdf wrf Ft _ regs =>
                      WP.block_nil ⟨⟨I, espf, rdf, wrf, Ft⟩, regs _ (by decide) (by decide) (by decide)⟩
                  rw [List.append_nil] at body₁ body₂
                  obtain ⟨Bf₁, E₁⟩ := wp_result body₁ B1
                  obtain ⟨Bf₂, E₂⟩ := wp_result body₂ C1
                  have sy₁ : f₁.syms = s.syms :=
                    ((Exec.syms B1).trans (show (allocFrame argsFrame u).syms = u.syms from rfl)).trans (Exec.syms E1)
                  have sy₂ : f₂.syms = t.syms :=
                    ((Exec.syms C1).trans (show (allocFrame argsFrame v).syms = v.syms from rfl)).trans (Exec.syms F1)
                  have T3 := (hb _ _ _ _ _ _ ⟨⟨Bf₁, sy₁⟩, ⟨Bf₂, sy₂⟩⟩ B2 C2).1
                  have K₁ := wp_result (hw₁ f₁ Bf₁ sy₁) B2
                  have K₂ := wp_result (hw₂ f₂ Bf₂ sy₂) C2
                  have Edi : w.gpr .edi = z.gpr .edi := by
                    rw [fw, fz, freed_gpr _ _ (by decide), freed_gpr _ _ (by decide), K₁.1 .edi (by decide),
                      K₂.1 .edi (by decide), E₁, E₂]
                    have h₁ := congrArg BitVec.toNat Su.edi
                    have h₂ := congrArg BitVec.toNat Sv.edi
                    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide))] at h₁ h₂
                    apply BitVec.eq_of_toNat_eq
                    rw [h₁, h₂, baseEq]
                  have T4 := (Crt.restore_relCT _ _ _ _ _ _
                    (agree_regs (rs := [.edi]) fun r hr => by
                      obtain rfl := List.mem_singleton.mp hr; exact Edi) E3 F3).1
                  rw [T1, T2, T3, T4]
                  rfl

/-- Two runs of `wrap a body` leak the same trace when the runs of `body` do. -/
theorem wrap_trace {a : Args} {n : Nat} {s t : State} (A : WrapABI a n s) (B : WrapABI a n t)
    (args : ∀ i < n, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp) {body : Prog isa}
    {Ex₁ Ex₂ : List Region → List Region → Prop} (hx₁ : Ex₁ s.rd (⟨frameAt s, argsFrame⟩ :: s.wr))
    (hx₂ : Ex₂ t.rd (⟨frameAt t, argsFrame⟩ :: t.wr))
    (hfill : (VG.Taint.check taint (τr [.esp]) (.block (fill a)) (.block [])).isSome = true)
    (hw₁ : ∀ f, BodyAt Ex₁ a s f → WP isa body f fun u => Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] f u)
    (hw₂ : ∀ f, BodyAt Ex₂ a t f → WP isa body f fun u => Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] f u)
    (hb : RelCT isa (fun f g => BodyAt Ex₁ a s f ∧ BodyAt Ex₂ a t g) body fun _ _ => True)
    {tr ur : List Leak} {sf tf : State} (E : Exec isa (wrap a body) s tr sf)
    (F : Exec isa (wrap a body) t ur tf) : tr = ur :=
  wrap_trace_syms A B args SP hx₁ hx₂ hfill (fun f B _ => hw₁ f B) (fun f B _ => hw₂ f B) (hb.mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h) E F

/-- The synthetic arguments of runs with the same arguments. -/
theorem synth_congr {a : Args} {n : Nat} (B : Below a n) {f g : Nat → BitVec 32} (h : ∀ i < n, f i = g i) :
    synth a f = synth a g := by
  have opt : ∀ {o : Option Nat}, (∀ j, o = some j → j < n) → optArg f o = optArg g o := by
    intro o ho
    cases e : o with
    | none => rfl
    | some j => exact h j (ho j e)
  have hd := h _ B.dom
  have hp := h _ B.plen
  have hl := h _ B.dlen
  have hw := h _ (show a.ws < n by have := B.ws; omega)
  have hw1 := h _ B.ws
  have ho := opt B.out
  have hy := opt B.y
  have hy' := opt (o := a.y.map fun _ => a.plen) fun j e => by
    cases ey : a.y with
    | none => rw [ey] at e; cases e
    | some k => rw [ey] at e; cases e; exact B.plen
  have hx := opt (o := a.x) fun j e => by have := B.x j e; omega
  have hx' := opt (o := a.x.map (· + 1)) fun j e => by
    cases ex : a.x with
    | none => rw [ex] at e; cases e
    | some k => rw [ex] at e; cases e; exact B.x k ex
  funext i
  match i with
  | 0 => exact ho
  | 1 => exact hp
  | 2 => exact hd
  | 3 => exact hp
  | 4 => show f a.dom + f a.plen = g a.dom + g a.plen; rw [hd, hp]
  | 5 => exact hp
  | 6 => show f a.dom + f a.plen + f a.plen = g a.dom + g a.plen + g a.plen; rw [hd, hp]
  | 7 => exact hp
  | 8 => exact hy
  | 9 => exact hy'
  | 10 => exact hx
  | 11 => exact hx'
  | 12 => exact hl
  | 13 => rfl
  | 14 => rfl
  | 15 => rfl
  | 16 => exact hw
  | 17 => exact hw1
  | _ + 18 => rfl

/-! ## The body's narrowed runs -/

/-- A state with everything readable and only the working space (and the regions `Out`) writable. -/
abbrev narrowed (base : Addr) (bytes : Nat) (f : State) (Out : List Region := []) : State :=
  f.withRegions (f.rd ++ f.wr) (⟨base, bytes⟩ :: Out)

theorem In.narrow {Ex Ex' : List Region → List Region → Prop} {base : Addr} {bytes len : Nat}
    {args : Nat → BitVec 32} {f : State} {Out : List Region} (h : In Ex base bytes len args f)
    (hx : Ex' (f.rd ++ f.wr) (⟨base, bytes⟩ :: Out)) : In Ex' base bytes len args (narrowed base bytes f Out) := by
  refine ⟨⟨h.scratch.edi, List.mem_cons_self .., h.scratch.nowrap, h.scratch.stk⟩, h.lower, h.upper,
    fun i hi => ⟨⟨?_, (h.stack i hi).stack.apart⟩, (h.stack i hi).value⟩, h.outLen, h.room, h.top, h.need,
    h.hbase, h.hbytes, hx⟩
  obtain ⟨r, hr, hc⟩ := (h.stack i hi).stack.read
  exact ⟨r, List.mem_append_left _ hr, hc⟩

section
variable {a : Args} {n : Nat} {s : State} {Ex : List Region → List Region → Prop} {f : State}

/-- The frame of the synthetic arguments lies apart from the working space. -/
theorem WrapABI.frameWs (A : WrapABI a n s) :
    Region.Disjoint ⟨frameAt s, argsFrame⟩ ⟨wsBase a s, wsSize a s⟩ := by
  have low := A.stackLow
  have st' : stack = 172 := rfl
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by simp only [argsFrame]; omega)
  exact A.belowScratch.sub_left (by rw [FA]; exact Offset.sub_below _ (by decide) (by decide))

theorem BodyAt.argsOk (A : WrapABI a n s) (B : BodyAt Ex a s f) {Out : List Region}
    (hOut : ∀ r ∈ Out, Region.Disjoint ⟨frameAt s, argsFrame⟩ r := by simp) :
    CrtRt.ArgsOk (narrowed (wsBase a s) (wsSize a s) f Out) := by
  have low := A.stackLow
  have st' : stack = 172 := rfl
  refine ⟨B.1.top, fun r hr => ?_⟩
  show Region.Disjoint ⟨(f.gpr .esp).setWidth 64, 76⟩ _
  rw [B.2.1]
  rcases List.mem_cons.mp hr with rfl | hr
  · exact A.frameWs
  · exact hOut r hr

theorem BodyAt.covers (B : BodyAt Ex a s f) {Out : List Region} (hOut : ∀ r ∈ Out, r ∈ f.wr) :
    Covers ((f.rd ++ f.wr) ++ (⟨wsBase a s, wsSize a s⟩ :: Out)) (f.rd ++ f.wr) ∧
      Covers (⟨wsBase a s, wsSize a s⟩ :: Out) f.wr := by
  have c : Covers (⟨wsBase a s, wsSize a s⟩ :: Out) f.wr := Covers.of_mem fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact B.1.scratch.wr
    · exact hOut r hr
  exact ⟨Covers.append_left (Covers.refl _) (Covers.right c), c⟩

end

/-- The body's runs, related from the narrowed states. -/
theorem narrow_body {a : Args} {s t : State} {Ex₁ Ex₂ : List Region → List Region → Prop} {body : Prog isa}
    {Pn : State → State → Prop} {Out : List Region} (hws : wsBase a s = wsBase a t) (hwz : wsSize a s = wsSize a t)
    (hw₁ : ∀ f, BodyAt Ex₁ a s f → ∃ F, WP isa body (narrowed (wsBase a s) (wsSize a s) f Out) F)
    (hw₂ : ∀ g, BodyAt Ex₂ a t g → ∃ F, WP isa body (narrowed (wsBase a t) (wsSize a t) g Out) F)
    (hpn : ∀ f g, BodyAt Ex₁ a s f → BodyAt Ex₂ a t g →
      Pn (narrowed (wsBase a s) (wsSize a s) f Out) (narrowed (wsBase a t) (wsSize a t) g Out))
    (h : RelCT isa Pn body fun _ _ => True)
    (ho₁ : ∀ f, BodyAt Ex₁ a s f → ∀ r ∈ Out, r ∈ f.wr := by simp)
    (ho₂ : ∀ g, BodyAt Ex₂ a t g → ∀ r ∈ Out, r ∈ g.wr := by simp) :
    RelCT isa (fun f g => BodyAt Ex₁ a s f ∧ BodyAt Ex₂ a t g) body fun _ _ => True := by
  refine VG.Proof.Bignum.X86.PublicRt.relCT_narrow (fun f => f.rd ++ f.wr)
    (fun _ => ⟨wsBase a s, wsSize a s⟩ :: Out) (fun f g ⟨B₁, B₂⟩ => ?_) h
  have c₁ := B₁.covers (ho₁ f B₁)
  have c₂ := B₂.covers (ho₂ g B₂)
  have w₂ := hw₂ g B₂
  have p := hpn f g B₁ B₂
  rw [← hws, ← hwz] at c₂ w₂ p
  exact ⟨c₁.1, c₁.2, c₂.1, c₂.2, hw₁ f B₁, w₂, p⟩

end VG.Proof.Ffdh.X86
