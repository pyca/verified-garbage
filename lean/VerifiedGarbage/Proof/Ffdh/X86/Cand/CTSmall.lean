module

import VerifiedGarbage.Proof.Ffdh.X86.Cand.Divides
import VerifiedGarbage.Proof.Ffdh.X86.Cand.CTBase
import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialLoopTiming
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStack
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeBase
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Impl.Ffdh.X86.Candidate
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ffdh.X86.Stages
import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
public import VerifiedGarbage.Impl.Ffdh.X86.Candidate
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Base
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeBase
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialReadControl

/-!
# The FFDH candidate on i686: the timing of a division by a small prime

`divides` stores the number's end in its frame, which RSA's trial division
compares with its pointer: its loop runs for as many words as the number
has, the same in runs of the same length (`divides_trace`, through RSA's
`divisor_trace_bounded`). Everything else it does addresses the stack.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Ffdh.X86
open VG.Proof.Bignum.X86.PublicRt (Both relCT_both)
open VG.Impl.Ffdh.X86.Candidate
open VG.Proof.RsaKeyGen.X86.Sieve (Geometry StackContext ReadControl)

variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32}

/-- A frame of the stack ends where it began. -/
theorem frame_esp {bytes : Nat} {body : Prog isa} {s s' : State} {t : List Leak}
    (e : Exec isa (.frame (.alloc bytes) body (.free bytes)) s t s') : s'.gpr .esp = s.gpr .esp := by
  cases e with
  | frame p b q =>
    obtain rfl := alloc_some p
    simp only [isa, pop] at q
    split at q
    · rename_i hc
      cases q
      simp only [State.setReg, ↓reduceIte]
      rw [hc.2.2.2.1, allocFrame_esp, BitVec.sub_add_cancel]
    · cases q

/-- Runs of a frame whose bodies leak alike end with `esp` where it was. -/
theorem relCT_frame {bytes : Nat} {body : Prog isa} {P : State → Prop}
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, Both P s₁ s₂ ∧ a = allocFrame bytes s₁ ∧ b = allocFrame bytes s₂) body
      fun _ _ => True) :
    RelCT isa (Both P) (.frame (.alloc bytes) body (.free bytes)) fun a b => ∃ x y, Both P x y ∧
      a.gpr .esp = x.gpr .esp ∧ b.gpr .esp = y.gpr .esp :=
  fun x y _ _ _ _ hp e₁ e₂ => ⟨(RelCT.frameAlloc hb _ _ _ _ _ _ hp e₁ e₂).1, x, y, hp, frame_esp e₁, frame_esp e₂⟩

theorem restoreEdi_trace {Q : State → State → Prop} (hq : ∀ x y, Q x y → x.gpr .esp = y.gpr .esp) :
    RelCT isa Q (.block restoreEdi) fun _ _ => True :=
  (VG.Proof.Dsa.X86.checkedBlockInvariant (τ := τr [.esp]) rfl rfl).mono
    (fun x y h => agree_regs fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hq x y h) fun _ _ _ => trivial

/-- The frame's words for a division: the number's end at `esp + 4`, the prime and its inverse. -/
abbrev divSetup (prime inv : Nat) : List Instr :=
  [.mov .edi (.reg .eax), .store (VG.Impl.RsaKeyGen.X86.Sieve.slot 4) .ecx, .mov .ebx (.imm (BitVec.ofNat 32 prime)),
    .mov .esi (.imm (BitVec.ofNat 32 inv)), .mov .ebp (.imm 0)]

/-- The number's address. -/
abbrev slotPtr (base : Addr) (len j : Nat) : BitVec 32 := BitVec.ofNat 32 (base.toNat + lo len (.slot .wide j))

/-- The geometry RSA's trial division reads the number of wide slot `j` with, below `sp`. -/
abbrev divGeo (base : Addr) (len j : Nat) (sp : BitVec 32) : Geometry :=
  ⟨sp - BitVec.ofNat 32 20, slotPtr base len j, 0, mw len, 0⟩

/-- `bounds`: the address of wide slot `j` in `eax`, its end in `ecx`. -/
abbrev Bounded (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (j : Nat) (u : State) : Prop :=
  Run Ex base bytes len args sp u ∧ u.gpr .eax = slotPtr base len j ∧
    u.gpr .ecx = slotPtr base len j + BitVec.ofNat 32 (bc len .wide)

theorem bounds_run {j : Nat} (hj : j ≤ 27) {x : State} (R : Run Ex base bytes len args sp x) :
    WP isa (.block (bounds (.slot .wide j))) x (Bounded Ex base bytes len args sp j) := by
  have h := R.1
  have f := slot_fit1 h hj
  rw [cb1] at f
  have nw := h.scratch.nowrap
  have := bounds_ok (is := []) (Q := Bounded Ex base bytes len args sp j) h hj fun u mu Ku au cu => by
    have e : u.gpr .eax = slotPtr base len j := by
      apply BitVec.eq_of_toNat_eq; rw [au, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact WP.block_nil ⟨⟨h.regs Ku mu, R.2.1.keep Ku, (Ku.1 _ (by decide)).trans R.2.2⟩, e, by rw [cu, e]⟩
  rwa [List.append_nil] at this

theorem divSetup_ok {j : Nat} (hj : j ≤ 27) {prime inv : Nat} {u : State} (B : Bounded Ex base bytes len args sp j u) :
    WP isa (.block (divSetup prime inv)) (allocFrame 20 u) (ReadControl (divGeo base len j sp) 0) := by
  have h := B.1.1
  have f := slot_fit1 h hj
  rw [cb1] at f
  have nw := h.scratch.nowrap
  have low := h.room.low
  have bl := h.bytes_lt
  have c2 := cwc_two len
  have bw := bc_eq_cwc len .wide
  have spu : u.gpr .esp = sp := B.1.2.2
  have lw := h.lower'
  have mwp : 8 ≤ mw len := by simp only [mw, Spec.Rsa.modulusWords]; omega
  have SC : StackContext (sp - BitVec.ofNat 32 20) (allocFrame 20 u) := by
    refine ⟨⟨?_, ?_⟩, by rw [allocFrame_esp, spu]⟩
    · rw [allocFrame_wr, spu]; exact List.mem_cons_self ..
    · rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (sp - BitVec.ofNat 32 20).isLt; omega),
        VG.X86.sub_toNat (by rw [← spu]; omega)]
      rw [← spu]; omega
  have PA : (slotPtr base len j).setWidth 64 = off base (lo len (.slot .wide j)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [off, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := base.isLt
    omega
  refine wp_mov fun a₁ U₁ => ?_
  refine (WP.block_append_iff (M := isa) (l₁ := [Instr.store (VG.Impl.RsaKeyGen.X86.Sieve.slot 4) .ecx])
    (l₂ := [.mov .ebx (.imm (BitVec.ofNat 32 prime)), .mov .esi (.imm (BitVec.ofNat 32 inv)), .mov .ebp (.imm 0)])).mpr
    (WP.mono ((SC.keep U₁.keeps (by decide)).store 4 (by decide) .ecx) fun a₂ ⟨M₂, _, K₂, S₂⟩ => ?_)
  refine wp_movi fun a₃ U₃ => wp_movi fun a₄ U₄ => wp_movi fun a₅ U₅ => WP.block_nil ?_
  have K : Keeps [.ebx, .esi, .ebp] a₂ a₅ :=
    ((U₃.keeps.mono (by decide)).trans (U₄.keeps.mono (by decide))).trans (U₅.keeps.mono (by decide))
  have m : a₅.mem = a₂.mem := by rw [U₅.mem, U₄.mem, U₃.mem]
  refine ⟨S₂.keep K (by decide), fun k hk => ?_, ?_, ?_⟩
  · have Ws₅ : Ws a₅ base bytes := ⟨by
      rw [K.2.2, K₂.2.2, U₁.keeps.2.2, allocFrame_wr]; exact List.mem_cons_of_mem _ h.ws.wr, nw⟩
    show InRegions _ (off ((slotPtr base len j).setWidth 64) (4 * k)) 4
    rw [PA, off, VG.Offset.add_add, ← off]
    exact ws_read Ws₅ (by have : k < 2 * mw len := hk; omega)
  · show a₅.mem.readW _ 32 = slotPtr base len j + BitVec.ofNat 32 (8 * mw len)
    rw [m, M₂, Mem.readW_writeW_self32, U₁.other _ (by decide), allocFrame_gpr _ _ (by decide), B.2.2]
    rfl
  · rw [U₅.other _ (by decide), U₄.other _ (by decide), U₃.other _ (by decide), K₂.1 _ (by simp), U₁.gpr,
      allocFrame_gpr _ _ (by decide), B.2.1]
    simp

/-- The taint analysis passes `p` with only the registers `rs` public. -/
abbrev RCheck (rs : List Reg) (p : Prog isa) : Prop :=
  (VG.Taint.check taint (τr rs) p (VG.Taint.hintOf taint (τr rs) p)).isSome = true

/-- Runs of a division by a small prime of wide slot `j`. -/
theorem divides_trace {j : Nat} (hj : j ≤ 27) {prime inv : Nat} (hc₁ : ACheck (.block (bounds (.slot .wide j))))
    (hc₂ : RCheck [.esp, .eax] (.block (divSetup prime inv))) {P : State → Prop}
    (hP : ∀ x, P x → Run Ex base bytes len args sp x) :
    RelCT isa (Both P) (divides (.slot .wide j) prime inv) fun _ _ => True := by
  refine relCT_of_imp (A := 0 < mw len ∧ mw len ≤ 128 ∧ (slotPtr base len j).toNat + 8 * mw len ≤ 2 ^ 32)
    (fun ⟨pos, wb, fit⟩ => ?_) fun x _ h => by
      have h := (hP x h.1).1
      have f := slot_fit1 h hj
      rw [cb1] at f
      have nw := h.scratch.nowrap
      have lw := h.lower'
      have up := h.upper'
      have : 8 ≤ mw len ∧ mw len ≤ 128 := by simp only [mw, Spec.Rsa.modulusWords]; omega
      refine ⟨by omega, this.2, ?_⟩
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have : bc len .wide = 8 * mw len := rfl; omega)]
      have : bc len .wide = 8 * mw len := rfl
      omega
  unfold divides
  refine RelCT.seq (aRel (F := Bounded Ex base bytes len args sp j) (fun x h => hP x h) hc₁
    fun x h => bounds_run hj (hP x h)) ?_
  refine RelCT.seq (relCT_frame ?_) (restoreEdi_trace fun x y ⟨x₀, y₀, ⟨B₀, B₁⟩, ex, ey⟩ => by
    rw [ex, ey, B₀.1.2.2, B₁.1.2.2])
  refine RelCT.seq (((RelCT.taint (A := taint) (τr [.esp, .eax]) (fun a b h => ?_) hc₂).wp
    (F₁ := ReadControl (divGeo base len j sp) 0) (F₂ := ReadControl (divGeo base len j sp) 0)
    fun a b ⟨s₁, s₂, ⟨B₁, B₂⟩, ea, eb⟩ => ⟨ea ▸ divSetup_ok hj B₁, eb ▸ divSetup_ok hj B₂⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2)
    ((VG.Proof.RsaKeyGen.X86.Sieve.divisor_trace_bounded pos wb fit).mono (fun _ _ h => h) fun _ _ _ => trivial)
  obtain ⟨s₁, s₂, ⟨B₁, B₂⟩, rfl, rfl⟩ := h
  refine agree_regs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [allocFrame_esp, allocFrame_esp, B₁.1.2.2, B₂.1.2.2]
  · rw [allocFrame_gpr _ _ (by decide), allocFrame_gpr _ _ (by decide), B₁.2.1, B₂.2.1]

end VG.Proof.Ffdh.X86.Cand
