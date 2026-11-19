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
public import VerifiedGarbage.Proof.Argon2.X86.HPrime.Next
import VerifiedGarbage.Proof.Sha256.X86.Stream.Common
meta import VerifiedGarbage.Proof.Argon2.X86.HPrime.Next
meta import VerifiedGarbage.Proof.Sha256.X86.Stream.Common
import VerifiedGarbage.Proof.MdStream.X86.Common
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Blake2.X86.Stream.Common
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Blake2.X86.CompressB.Body
public import VerifiedGarbage.Proof.Argon2.HPrime
import VerifiedGarbage.Proof.Argon2.Initial
import VerifiedGarbage.Proof.Blake2.X86.Stream.Verified
public import VerifiedGarbage.Proof.Argon2.X86.HPrime.Calls
public import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Argon2.X86.HPrime.Calls
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Blake2.X86.Stream.Verified
meta import VerifiedGarbage.Proof.MdStream.X86.Common
meta import VerifiedGarbage.Proof.Blake2.X86.Stream.Common
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Blake2.X86.CompressB.Body
meta import VerifiedGarbage.Proof.Argon2.HPrime
meta import VerifiedGarbage.Proof.Argon2.Initial

/-! ### `Argon2.X86.HPrime.Finish`, which this module and modules that import it used -/

section

/-! ### `Argon2.X86.HPrime.CallsCT`, which this module and modules that import it used -/

section

/-!
# Argon2 H′ on x86 (32-bit): the calls, in two runs

The macros calling the BLAKE2b functions leak the same trace in two runs that
pass them the same arguments (`init_rel`, `update_rel`, `finalize_rel`):
the instructions before each call are checked by the taint analysis, and the
call is related by the callee's constant time (`RelCT.callWith`), from the
callee's precondition in both runs (`init_pre`, `update_pre`,
`finalize_pre`). `rel_taint` and `rel_wp` add what each run satisfies by
correctness.
-/

@[expose] public section

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (init update finalize initCode updateCode finalizeCode)
open VG.Proof.Blake2 (initX86 updateX86 finalizeX86)
open VG.Proof.Sha256.X86.Stream (Upd wp_movi wp_mov wp_addi)

/-! ## Two runs -/

/-- Two runs, each described by `WP`, of code the taint analysis proves
constant time from the registers `rs` public. -/
theorem rel_taint {F₁ F₂ G₁ G₂ : State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s₁ s₂, F₁ s₁ → F₂ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (VG.Taint.check taint (τr rs) c hc).isSome = true)
    (hw₁ : ∀ s, F₁ s → WP isa c s G₁) (hw₂ : ∀ s, F₂ s → WP isa c s G₂) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) c fun t₁ t₂ => G₁ t₁ ∧ G₂ t₂ := by
  obtain ⟨_, hc⟩ := hc
  exact ((RelCT.taint (A := taint) (τr rs) (fun s₁ s₂ h => agree_regs (hag s₁ s₂ h.1 h.2)) hc).wp
    fun s₁ s₂ h => ⟨hw₁ s₁ h.1, hw₂ s₂ h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- What each run satisfies, added to two runs that leak the same trace. -/
theorem rel_wp {F₁ F₂ G₁ G₂ : State → Prop} {c : Prog isa}
    (hct : RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) c fun _ _ => True)
    (hw₁ : ∀ s, F₁ s → WP isa c s G₁) (hw₂ : ∀ s, F₂ s → WP isa c s G₂) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) c fun t₁ t₂ => G₁ t₁ ∧ G₂ t₂ :=
  (hct.wp fun s₁ s₂ h => ⟨hw₁ s₁ h.1, hw₂ s₂ h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- A relation proved from facts of the related states. -/
theorem RelCT.of_pre {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ s₁ s₂, P s₁ s₂ → RelCT isa P c Q) : RelCT isa P c Q :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂ => h s₁ s₂ hp s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂

/-- The callee's public data, `esp` and its first `n` arguments, agree in
two runs that agree on `esp` and on the registers pushed. -/
theorem call_pub {rs : List Reg} (hrs : Reg.esp ∉ rs) {s₁ s₂ : State}
    (fit : 4 * rs.length + 4 ≤ (s₁.gpr .esp).toNat) (hsp : s₁.gpr .esp = s₂.gpr .esp)
    (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) (rd wr : List Region) :
    ((pushed rs s₁).callEntry.withRegions rd wr).gpr .esp =
      ((pushed rs s₂).callEntry.withRegions rd wr).gpr .esp ∧
    ∀ i < rs.length, arg ((pushed rs s₁).callEntry.withRegions rd wr) i =
      arg ((pushed rs s₂).callEntry.withRegions rd wr) i := by
  refine ⟨?_, fun i hi => ?_⟩
  · simp only [State.withRegions_gpr, callEntry_esp', hsp]
  · simp only [arg_withRegions]
    exact callEntry_arg_eq hrs fit hsp hr hi

/-! ## `init` -/

theorem init_pre {B E : BitVec 32} {s : State} (h : Ctx B E s) {n : Nat}
    (hn : s.gpr .edx = BitVec.ofNat 32 n) (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) (ha : s.gpr .eax = 0)
    (hc : s.gpr .ecx = B) :
    CallPre (initX86 b) [.eax, .ecx, .edx, .ebx]
      [⟨B.setWidth 64, 0⟩, ⟨(E - BitVec.ofNat 32 16).setWidth 64, 16⟩] [⟨B.setWidth 64, 192⟩] s := by
  obtain hrs : Reg.esp ∉ [Reg.eax, .ecx, .edx, .ebx] := by decide
  have esp₂ : s.gpr .esp = E := h.esp
  obtain fit : 4 * [Reg.eax, .ecx, .edx, .ebx].length + 4 ≤ (s.gpr .esp).toNat := by
    rw [esp₂]; have := h.lo; simp only [List.length_cons, List.length_nil]; omega_arith
  let sE := (pushed [Reg.eax, .ecx, .edx, .ebx] s).callEntry
  try rewrite [show (pushed [Reg.eax, .ecx, .edx, .ebx] s).callEntry = sE from rfl] at *
  have hsE : sE = (pushed [Reg.eax, .ecx, .edx, .ebx] s).callEntry := rfl
  obtain a0 : arg sE 0 = B := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [h.ebx]
  obtain a1 : arg sE 1 = BitVec.ofNat 32 n := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hn]
  obtain a2 : arg sE 2 = B := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hc]
  obtain a3 : arg sE 3 = 0 := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [ha]
  obtain eA : argAddr sE 0 = (E - BitVec.ofNat 32 16).setWidth 64 := by
    rw [hsE, callEntry_argAddr0, esp₂]; rfl
  obtain eSp : sE.gpr .esp = E - BitVec.ofNat 32 20 := by
    rw [hsE, callEntry_esp', esp₂]; rfl
  obtain stR : Region.Sub ⟨B.setWidth 64, 192⟩ ⟨B.setWidth 64, 832⟩ := Region.sub_prefix (by decide)
  obtain d20 : (below E 20).Disjoint ⟨B.setWidth 64, 192⟩ :=
    (h.stk.sub_right stR).sub_left (below_sub (by decide) h.lo)
  refine ⟨?_, ?_, ?_⟩
  · rw [← hsE]
    simp only [initX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp]
    obtain mb : (64 : Nat) ≤ b.maxBytes := by decide
    refine ⟨rfl, rfl, fun _ h₁ _ => by simp [Region.Contains] at h₁, ?_, ?_,
      by simp only [Proof.Blake2.bufOff, blockBytes]; have := h.fits; omega_arith,
      by simp; have := B.isLt; omega_arith, ?_, by simp [BitVec.toNat_ofNat]; omega_arith,
      by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith, by simp⟩
    · exact d20.sub_left (below_sub (by decide) (by have := h.lo; omega_arith))
    · refine d20.sub_left ?_
      have := below_inner (sp := E) (a := 4) (b := 20) (k := 16) (by omega_arith) (by have := h.lo; omega_arith)
      rw [show E - BitVec.ofNat 32 20 = E - BitVec.ofNat 32 16 - BitVec.ofNat 32 4 by
        rw [← VG.Offset.sub_add_eq]; rfl]
      exact this
    · rw [sub_toNat (by have := h.lo; omega_arith)]; have := E.isLt; omega_arith
  · rw [esp₂]
    refine Covers.append_left (Covers.cons ?_ (Covers.cons ?_ Covers.nil)) ?_
    · intro a k ⟨r, hr, hc⟩
      simp only [List.mem_singleton] at hr; subst hr
      obtain ⟨r', hr', hc'⟩ := h.wr a k ⟨_, List.mem_singleton_self _, by
        simp only [Region.Contains] at hc ⊢; omega_arith⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
    · intro a k ⟨r, hr, hc⟩
      simp only [List.mem_singleton] at hr; subst hr
      refine InRegions_append_cons.mpr (.inl ?_)
      simpa using hc
    · exact (Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, 0, by simp, by simp⟩).trans
        ((h.wr.trans fun a k hi => let ⟨r', hr', hc'⟩ := hi
          InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)))
  · rw [esp₂]
    exact (Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, 0, by simp, by simp⟩).trans
      (h.wr.trans fun a k ⟨r', hr', hc'⟩ => ⟨r', List.mem_cons_of_mem _ hr', hc'⟩)

/-- What `init` needs: the state's context, and the digest length in `edx`. -/
def InitIn (B E : BitVec 32) (n : Nat) (s : State) : Prop :=
  Ctx B E s ∧ s.gpr .edx = BitVec.ofNat 32 n

theorem init_rel {B E : BitVec 32} {n : Nat} (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) :
    RelCT isa (fun s₁ s₂ => InitIn B E n s₁ ∧ InitIn B E n s₂) Impl.Argon2.X86.HPrime.init
      fun _ _ => True := by
  obtain blk : ∀ s, InitIn B E n s → WP isa (.block [.mov .eax (.imm 0), .mov .ecx (.reg .ebx)]) s
      fun t => Ctx B E t ∧ t.gpr .edx = BitVec.ofNat 32 n ∧ t.gpr .eax = 0 ∧ t.gpr .ecx = B :=
    fun s ⟨c, e⟩ => wp_movi fun s₁ u₁ => wp_mov fun s₂ u₂ => WP.block_nil
      ⟨c.of_regs (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
        (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]) (by rw [u₂.wr, u₁.wr]),
       by rw [u₂.other _ (by decide), u₁.other _ (by decide), e],
       by rw [u₂.other _ (by decide), u₁.gpr],
       by rw [u₂.gpr, u₁.other _ (by decide), c.ebx]⟩
  unfold Impl.Argon2.X86.HPrime.init
  refine RelCT.seq (rel_taint [.esp, .ebx, .edx] (fun s₁ s₂ ⟨c₁, e₁⟩ ⟨c₂, e₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [c₁.esp, c₂.esp]
      · rw [c₁.ebx, c₂.ebx]
      · rw [e₁, e₂]) ⟨_, by taint_decide⟩ blk blk) ?_
  refine RelCT.callWith (k := initX86 b) init_correct Proof.Blake2.X86.B.init_ct
    [⟨B.setWidth 64, 0⟩, ⟨(E - BitVec.ofNat 32 16).setWidth 64, 16⟩] [⟨B.setWidth 64, 192⟩]
    fun s₁ s₂ ⟨⟨c₁, e₁, a₁, x₁⟩, ⟨c₂, e₂, a₂, x₂⟩⟩ => ?_
  obtain fit : 4 * [Reg.eax, .ecx, .edx, .ebx].length + 4 ≤ (s₁.gpr .esp).toNat := by
    rw [c₁.esp]; have := c₁.lo; simp only [List.length_cons, List.length_nil]; omega_arith
  obtain hsp : s₁.gpr .esp = s₂.gpr .esp := c₁.esp.trans c₂.esp.symm
  obtain ⟨p₁, p₂⟩ := call_pub (by decide) fit hsp (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [a₁, a₂]
    · rw [x₁, x₂]
    · rw [e₁, e₂]
    · rw [c₁.ebx, c₂.ebx]) [⟨B.setWidth 64, 0⟩, ⟨(E - BitVec.ofNat 32 16).setWidth 64, 16⟩]
    [⟨B.setWidth 64, 192⟩]
  exact ⟨init_pre c₁ e₁ hn₁ hn₂ a₁ x₁, init_pre c₂ e₂ hn₁ hn₂ a₂ x₂, hsp, p₁, p₂⟩

/-! ## `update` -/

theorem update_pre {B E : BitVec 32} {s : State} (h : Ctx B E s) {D : BitVec 32} {L : Nat}
    (hD : s.gpr .esi = D) (hL : (s.gpr .edi).toNat = L) (hDfit : D.toNat + L ≤ 2 ^ 32)
    (hDc : Covers [⟨D.setWidth 64, L⟩] (s.rd ++ s.wr))
    (hDs : Region.Disjoint ⟨D.setWidth 64, L⟩ ⟨B.setWidth 64, 768⟩)
    (hDk : (below E 60).Disjoint ⟨D.setWidth 64, L⟩) (ha : s.gpr .eax = B + 192) :
    CallPre (updateX86 b) [.eax, .edi, .esi, .edx, .ecx, .ebx]
      [⟨D.setWidth 64, L⟩, ⟨(E - BitVec.ofNat 32 24).setWidth 64, 24⟩]
      [⟨B.setWidth 64, 192⟩, ⟨B.setWidth 64 + 192, 576⟩] s := by
  obtain hrs : Reg.esp ∉ [Reg.eax, .edi, .esi, .edx, .ecx, .ebx] := by decide
  have esp₂ : s.gpr .esp = E := h.esp
  have hlo := h.lo
  obtain fit : 4 * [Reg.eax, .edi, .esi, .edx, .ecx, .ebx].length + 4 ≤ (s.gpr .esp).toNat := by
    rw [esp₂]; simp only [List.length_cons, List.length_nil]; omega_arith
  let sE := (pushed [Reg.eax, .edi, .esi, .edx, .ecx, .ebx] s).callEntry
  try rewrite [show (pushed [Reg.eax, .edi, .esi, .edx, .ecx, .ebx] s).callEntry = sE from rfl] at *
  have hsE : sE = (pushed [Reg.eax, .edi, .esi, .edx, .ecx, .ebx] s).callEntry := rfl
  obtain a0 : arg sE 0 = B := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [h.ebx]
  obtain a3 : arg sE 3 = D := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hD]
  obtain a4 : (arg sE 4).toNat = L := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hL]
  obtain a5 : arg sE 5 = B + 192 := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [ha]
  obtain eA : argAddr sE 0 = (E - BitVec.ofNat 32 24).setWidth 64 := by
    rw [hsE, callEntry_argAddr0, esp₂]; rfl
  obtain eSp : sE.gpr .esp = E - BitVec.ofNat 32 28 := by
    rw [hsE, callEntry_esp', esp₂]; rfl
  have hfit := h.fits
  obtain e192 : (B + 192).setWidth 64 = B.setWidth 64 + 192 := setWidth_add (d := 192) (by omega_arith)
  obtain stR : (below E 60).Disjoint ⟨B.setWidth 64, 192⟩ :=
    h.stk.sub_right (Region.sub_prefix (by decide))
  obtain scR : (below E 60).Disjoint ⟨B.setWidth 64 + 192, 576⟩ := h.stk_sub (d := 192) (by decide) (Nat.le_refl _)
  obtain stk60 : ∀ {k : Nat} {r : Region}, k ≤ 60 → (below E 60).Disjoint r → (below E k).Disjoint r :=
    fun hk d => d.sub_left (below_sub hk hlo)
  obtain retSub : Region.Sub ⟨(E - BitVec.ofNat 32 28).setWidth 64, 4⟩ (below E 60) := by
    have := below_inner (sp := E) (a := 4) (b := 60) (k := 24) (by omega_arith) hlo
    rw [show E - BitVec.ofNat 32 28 = E - BitVec.ofNat 32 24 - BitVec.ofNat 32 4 by
      rw [← VG.Offset.sub_add_eq]; rfl]
    exact this
  obtain calleeStk : Region.Sub ⟨(E - BitVec.ofNat 32 28).setWidth 64 - 32, 32⟩ (below E 60) := by
    have := below_inner (sp := E) (a := 32) (b := 60) (k := 28) (by omega_arith) hlo
    obtain e : (E - BitVec.ofNat 32 28 - BitVec.ofNat 32 32).setWidth 64 =
        (E - BitVec.ofNat 32 28).setWidth 64 - 32 :=
      Taint.sub_setWidth (m := 32) (by rw [sub_toNat (by omega_arith)]; omega_arith)
    show Region.Sub ⟨_, 32⟩ _
    rw [← e]; exact this
  obtain argSub : Region.Sub ⟨(E - BitVec.ofNat 32 24).setWidth 64, 24⟩ (below E 60) :=
    below_sub (by decide) hlo
  obtain b192 : (B + 192).toNat = B.toNat + 192 := by
    rw [BitVec.toNat_add, show (192 : BitVec 32).toNat = 192 from rfl]; omega_arith
  refine ⟨?_, ?_, ?_⟩
  · rw [← hsE]
    simp only [updateX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a3, a4, a5, eA, eSp, e192, Proof.Blake2.bufOff,
      blockBytes, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd]
    refine ⟨trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Offset.base_disjoint _ (by decide) (by decide)
    · exact hDs.sub_right (Region.sub_prefix (by decide))
    · exact hDs.sub_right (Offset.sub_base _ (by decide))
    · exact stR.sub_left argSub
    · exact scR.sub_left argSub
    · exact stR.sub_left retSub
    · exact scR.sub_left retSub
    · exact stR.sub_left calleeStk
    · exact scR.sub_left calleeStk
    · exact hDk.sub_left calleeStk
    · omega_arith
    · omega_arith
    · rw [b192]; omega_arith
    · rw [sub_toNat (by omega_arith)]; omega_arith
    · rw [sub_toNat (by omega_arith)]; have := E.isLt; omega_arith
  · rw [esp₂]
    refine Covers.append_left (Covers.cons (covers_ins _ hDc) (Covers.cons (covers_frame rfl _)
      Covers.nil)) (covers_ins _ (Covers.right ((h.cov0 (by decide)).pair (h.cov (d := 192) (by decide)))))
  · rw [esp₂]
    exact covers_cons _ ((h.cov0 (by decide)).pair (h.cov (d := 192) (by decide)))

/-- What `update` needs: the state's context, the data at `D`, of `L` bytes,
and the count in `edx:ecx`. -/
def UpdateIn (B E D : BitVec 32) (L : Nat) (lo hi : BitVec 32) (s : State) : Prop :=
  Ctx B E s ∧ s.gpr .esi = D ∧ (s.gpr .edi).toNat = L ∧ s.gpr .ecx = lo ∧ s.gpr .edx = hi ∧
    Covers [⟨D.setWidth 64, L⟩] (s.rd ++ s.wr)

theorem update_rel {B E D : BitVec 32} {L : Nat} {lo hi : BitVec 32} (hDfit : D.toNat + L ≤ 2 ^ 32)
    (hDs : Region.Disjoint ⟨D.setWidth 64, L⟩ ⟨B.setWidth 64, 768⟩)
    (hDk : (below E 60).Disjoint ⟨D.setWidth 64, L⟩) :
    RelCT isa (fun s₁ s₂ => UpdateIn B E D L lo hi s₁ ∧ UpdateIn B E D L lo hi s₂) update
      fun _ _ => True := by
  obtain blk : ∀ s, UpdateIn B E D L lo hi s →
      WP isa (.block [.mov .eax (.reg .ebx), .alu .add .eax (.imm 192)]) s
      fun t => UpdateIn B E D L lo hi t ∧ t.gpr .eax = B + 192 :=
    fun s ⟨c, e1, e2, e3, e4, cv⟩ => wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => WP.block_nil
      ⟨⟨c.of_regs (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
        (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]) (by rw [u₂.wr, u₁.wr]),
       by rw [u₂.other _ (by decide), u₁.other _ (by decide), e1],
       by rw [u₂.other _ (by decide), u₁.other _ (by decide), e2],
       by rw [u₂.other _ (by decide), u₁.other _ (by decide), e3],
       by rw [u₂.other _ (by decide), u₁.other _ (by decide), e4],
       by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact cv⟩,
       by rw [u₂.gpr, u₁.gpr, c.ebx]⟩
  unfold update
  refine RelCT.seq (rel_taint [.esp, .ebx, .esi, .edi, .ecx, .edx]
    (fun s₁ s₂ ⟨c₁, d₁, l₁, x₁, y₁, _⟩ ⟨c₂, d₂, l₂, x₂, y₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [c₁.esp, c₂.esp]
      · rw [c₁.ebx, c₂.ebx]
      · rw [d₁, d₂]
      · exact BitVec.eq_of_toNat_eq (l₁.trans l₂.symm)
      · rw [x₁, x₂]
      · rw [y₁, y₂]) ⟨_, by taint_decide⟩ blk blk) ?_
  refine RelCT.callWith (k := updateX86 b) update_correct Proof.Blake2.X86.B.update_ct
    [⟨D.setWidth 64, L⟩, ⟨(E - BitVec.ofNat 32 24).setWidth 64, 24⟩]
    [⟨B.setWidth 64, 192⟩, ⟨B.setWidth 64 + 192, 576⟩]
    fun s₁ s₂ ⟨⟨⟨c₁, d₁, l₁, x₁, y₁, v₁⟩, a₁⟩, ⟨⟨c₂, d₂, l₂, x₂, y₂, v₂⟩, a₂⟩⟩ => ?_
  obtain fit : 4 * [Reg.eax, .edi, .esi, .edx, .ecx, .ebx].length + 4 ≤ (s₁.gpr .esp).toNat := by
    rw [c₁.esp]; have := c₁.lo; simp only [List.length_cons, List.length_nil]; omega_arith
  obtain hsp : s₁.gpr .esp = s₂.gpr .esp := c₁.esp.trans c₂.esp.symm
  obtain ⟨p₁, p₂⟩ := call_pub (by decide) fit hsp (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [a₁, a₂]
    · exact BitVec.eq_of_toNat_eq (l₁.trans l₂.symm)
    · rw [d₁, d₂]
    · rw [y₁, y₂]
    · rw [x₁, x₂]
    · rw [c₁.ebx, c₂.ebx]) [⟨D.setWidth 64, L⟩, ⟨(E - BitVec.ofNat 32 24).setWidth 64, 24⟩]
    [⟨B.setWidth 64, 192⟩, ⟨B.setWidth 64 + 192, 576⟩]
  exact ⟨update_pre c₁ d₁ l₁ hDfit v₁ hDs hDk a₁, update_pre c₂ d₂ l₂ hDfit v₂ hDs hDk a₂, hsp, p₁, p₂⟩

/-! ## `finalize` -/

theorem finalize_pre {B E : BitVec 32} {s : State} (h : Ctx B E s) (ha : s.gpr .eax = B + 192)
    (hi : s.gpr .esi = B + 768) :
    CallPre (finalizeX86 b) [.eax, .esi, .edx, .ecx, .ebx] [⟨(E - BitVec.ofNat 32 20).setWidth 64, 20⟩]
      [⟨B.setWidth 64, 192⟩, ⟨B.setWidth 64 + 768, 64⟩, ⟨B.setWidth 64 + 192, 576⟩] s := by
  obtain hrs : Reg.esp ∉ [Reg.eax, .esi, .edx, .ecx, .ebx] := by decide
  have esp₄ : s.gpr .esp = E := h.esp
  have hlo := h.lo
  have hfit := h.fits
  obtain fit : 4 * [Reg.eax, .esi, .edx, .ecx, .ebx].length + 4 ≤ (s.gpr .esp).toNat := by
    rw [esp₄]; simp only [List.length_cons, List.length_nil]; omega_arith
  let sE := (pushed [Reg.eax, .esi, .edx, .ecx, .ebx] s).callEntry
  try rewrite [show (pushed [Reg.eax, .esi, .edx, .ecx, .ebx] s).callEntry = sE from rfl] at *
  have hsE : sE = (pushed [Reg.eax, .esi, .edx, .ecx, .ebx] s).callEntry := rfl
  obtain a0 : arg sE 0 = B := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [h.ebx]
  obtain a3 : arg sE 3 = B + 768 := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hi]
  obtain a4 : arg sE 4 = B + 192 := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [ha]
  obtain eA : argAddr sE 0 = (E - BitVec.ofNat 32 20).setWidth 64 := by
    rw [hsE, callEntry_argAddr0, esp₄]; rfl
  obtain eSp : sE.gpr .esp = E - BitVec.ofNat 32 24 := by
    rw [hsE, callEntry_esp', esp₄]; rfl
  obtain e192 : (B + 192).setWidth 64 = B.setWidth 64 + 192 := setWidth_add (d := 192) (by omega_arith)
  obtain e768 : (B + 768).setWidth 64 = B.setWidth 64 + 768 := setWidth_add (d := 768) (by omega_arith)
  obtain stR : (below E 60).Disjoint ⟨B.setWidth 64, 192⟩ :=
    (h.stk.sub_right (Region.sub_prefix (by decide)))
  obtain scR : (below E 60).Disjoint ⟨B.setWidth 64 + 192, 576⟩ := h.stk_sub (d := 192) (by decide) (Nat.le_refl _)
  obtain dgR : (below E 60).Disjoint ⟨B.setWidth 64 + 768, 64⟩ := h.stk_sub (d := 768) (by decide) (Nat.le_refl _)
  obtain argSub : Region.Sub ⟨(E - BitVec.ofNat 32 20).setWidth 64, 20⟩ (below E 60) :=
    below_sub (by decide) hlo
  obtain retSub : Region.Sub ⟨(E - BitVec.ofNat 32 24).setWidth 64, 4⟩ (below E 60) := by
    have := below_inner (sp := E) (a := 4) (b := 60) (k := 20) (by omega_arith) hlo
    rw [show E - BitVec.ofNat 32 24 = E - BitVec.ofNat 32 20 - BitVec.ofNat 32 4 by
      rw [← VG.Offset.sub_add_eq]; rfl]
    exact this
  obtain calleeStk : Region.Sub ⟨(E - BitVec.ofNat 32 24).setWidth 64 - 32, 32⟩ (below E 60) := by
    have := below_inner (sp := E) (a := 32) (b := 60) (k := 24) (by omega_arith) hlo
    obtain e : (E - BitVec.ofNat 32 24 - BitVec.ofNat 32 32).setWidth 64 =
        (E - BitVec.ofNat 32 24).setWidth 64 - 32 :=
      Taint.sub_setWidth (m := 32) (by rw [sub_toNat (by omega_arith)]; omega_arith)
    show Region.Sub ⟨_, 32⟩ _
    rw [← e]; exact this
  obtain b192 : (B + 192).toNat = B.toNat + 192 := by
    rw [BitVec.toNat_add, show (192 : BitVec 32).toNat = 192 from rfl]; omega_arith
  obtain b768 : (B + 768).toNat = B.toNat + 768 := by
    rw [BitVec.toNat_add, show (768 : BitVec 32).toNat = 768 from rfl]; omega_arith
  refine ⟨?_, ?_, ?_⟩
  · rw [← hsE]
    simp only [finalizeX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a3, a4, eA, eSp, e192, e768, Proof.Blake2.bufOff,
      blockBytes, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd]
    refine ⟨trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Offset.base_disjoint _ (by decide) (by decide)
    · exact Offset.base_disjoint _ (by decide) (by decide)
    · exact Offset.disjoint _ (by decide) (by decide) (by decide)
    · exact stR.sub_left argSub
    · exact dgR.sub_left argSub
    · exact scR.sub_left argSub
    · exact stR.sub_left retSub
    · exact dgR.sub_left retSub
    · exact scR.sub_left retSub
    · exact stR.sub_left calleeStk
    · exact dgR.sub_left calleeStk
    · exact scR.sub_left calleeStk
    · omega_arith
    · rw [b768]; omega_arith
    · rw [b192]; omega_arith
    · rw [sub_toNat (by omega_arith)]; omega_arith
    · rw [sub_toNat (by omega_arith)]; have := E.isLt; omega_arith
  · rw [esp₄]
    refine Covers.append_left (Covers.cons (covers_frame rfl _) Covers.nil)
      (covers_ins _ (Covers.right ((h.cov0 (by decide)).cons ((h.cov (d := 768) (by decide)).pair
        (h.cov (d := 192) (by decide))))))
  · rw [esp₄]
    exact covers_cons _ ((h.cov0 (by decide)).cons ((h.cov (d := 768) (by decide)).pair
      (h.cov (d := 192) (by decide))))

/-- What `finalize` needs: the state's context and the count in `edx:ecx`. -/
def FinalizeIn (B E lo hi : BitVec 32) (s : State) : Prop :=
  Ctx B E s ∧ s.gpr .ecx = lo ∧ s.gpr .edx = hi

theorem finalize_rel {B E lo hi : BitVec 32} :
    RelCT isa (fun s₁ s₂ => FinalizeIn B E lo hi s₁ ∧ FinalizeIn B E lo hi s₂) finalize
      fun _ _ => True := by
  obtain blk : ∀ s, FinalizeIn B E lo hi s → WP isa (.block [.mov .eax (.reg .ebx), .alu .add .eax (.imm 192),
      .mov .esi (.reg .ebx), .alu .add .esi (.imm 768)]) s
      fun t => FinalizeIn B E lo hi t ∧ t.gpr .eax = B + 192 ∧ t.gpr .esi = B + 768 :=
    fun s ⟨c, e3, e4⟩ => wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_addi fun s₄ u₄ =>
      WP.block_nil
      ⟨⟨c.of_regs (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide)])
        (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)])
        (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]),
       by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), e3],
       by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), e4]⟩,
       by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr, c.ebx],
       by rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), c.ebx]⟩
  unfold finalize
  refine RelCT.seq (rel_taint [.esp, .ebx, .ecx, .edx]
    (fun s₁ s₂ ⟨c₁, x₁, y₁⟩ ⟨c₂, x₂, y₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [c₁.esp, c₂.esp]
      · rw [c₁.ebx, c₂.ebx]
      · rw [x₁, x₂]
      · rw [y₁, y₂]) ⟨_, by taint_decide⟩ blk blk) ?_
  refine RelCT.callWith (k := finalizeX86 b) finalize_correct Proof.Blake2.X86.B.finalize_ct
    [⟨(E - BitVec.ofNat 32 20).setWidth 64, 20⟩]
    [⟨B.setWidth 64, 192⟩, ⟨B.setWidth 64 + 768, 64⟩, ⟨B.setWidth 64 + 192, 576⟩]
    fun s₁ s₂ ⟨⟨⟨c₁, x₁, y₁⟩, a₁, i₁⟩, ⟨⟨c₂, x₂, y₂⟩, a₂, i₂⟩⟩ => ?_
  obtain fit : 4 * [Reg.eax, .esi, .edx, .ecx, .ebx].length + 4 ≤ (s₁.gpr .esp).toNat := by
    rw [c₁.esp]; have := c₁.lo; simp only [List.length_cons, List.length_nil]; omega_arith
  obtain hsp : s₁.gpr .esp = s₂.gpr .esp := c₁.esp.trans c₂.esp.symm
  obtain ⟨p₁, p₂⟩ := call_pub (by decide) fit hsp (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [a₁, a₂]
    · rw [i₁, i₂]
    · rw [y₁, y₂]
    · rw [x₁, x₂]
    · rw [c₁.ebx, c₂.ebx]) [⟨(E - BitVec.ofNat 32 20).setWidth 64, 20⟩]
    [⟨B.setWidth 64, 192⟩, ⟨B.setWidth 64 + 768, 64⟩, ⟨B.setWidth 64 + 192, 576⟩]
  exact ⟨finalize_pre c₁ a₁ i₁, finalize_pre c₂ a₂ i₂, hsp, p₁, p₂⟩

end VG.Proof.Argon2.X86.HPrime

end

end

/-! ### `Argon2.X86.HPrime.Output`, which only this module used -/

section

@[expose] public section

section

/-!
# Argon2 H′ on x86 (32-bit): the state of the body

`Body s₀ s`: between H′'s setup and its restore, `ebx` points to `scratch`,
`esp` is as on entry, memory has changed only in the output, `scratch` and
the stack below `esp`, and the caller's registers and the length prefix are
kept in `scratch`. `Out s₀ s k`: the output pointer and the bytes left, after
`k` output bytes. `copy_ok`: copying digest bytes to the output.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (copy outOff leftOff saved)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_mov wp_addi wp_movm wp_store contains_addr)
open VG.WriteBytes

theorem bytesAt_writeBytes (m : Mem) (p : Addr) (xs : List Byte) (hn : xs.length < 2 ^ 64) :
    bytesAt (writeBytes m p xs) p xs.length = xs := by
  apply List.ext_getElem (by simp only [bytesAt, List.length_map, List.length_range])
  intro i _ hi
  simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes,
    Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith : i < 2 ^ 64),
    hi, ite_true, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem bytesAt_take (m : Mem) (p : Addr) (n k : Nat) (hn : n ≤ k) :
    (bytesAt m p k).take n = bytesAt m p n := by
  simp only [bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left hn]

/-- The state of the body. -/
structure Body (s₀ s : State) : Prop where
  ebx : s.gpr .ebx = scr s₀
  esp : s.gpr .esp = esp₀ s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [outR s₀, scrR s₀, stkR s₀] s₀.mem s.mem
  saved : ∀ p ∈ saved, s.mem.readW (addr (scr s₀) p.2) 32 = s₀.gpr p.1
  pfx : bytesAt s.mem (P s₀ + 832) 4 = Spec.Argon2.le32 (ol s₀)

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem Body.ctx {s : State} (h : Body s₀ s) : Ctx (scr s₀) (esp₀ s₀) s :=
  ⟨h.ebx, h.esp, by have := hp.scr_fits; omega_arith, hp.esp_lo, by have := hp.esp_hi; omega_arith,
    (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp [h.wr, hp.wr], 0, by simp, by simp⟩),
    hp.stk_scr.sub_right (Region.sub_prefix (by decide))⟩

/-- A word of `scratch` from offset 832 on is kept by the hash macros. -/
theorem keeps_word {s t : State} (k : Keeps (scr s₀) (esp₀ s₀) s t) {d : Nat} (hd : 832 ≤ d)
    (hd' : d + 4 ≤ 16384) : t.mem.readW (addr (scr s₀) d) 32 = s.mem.readW (addr (scr s₀) d) 32 := by
  refine k.frame.readW (r := ⟨addr (scr s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  obtain e := scr_addr hp (d := d) (by omega_arith)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [e]; exact Offset.disjoint_base _ hd (by omega_arith)
  · rw [e]
    exact (hp.stk_scr.sub_right (Offset.sub_base _ (show d + 4 ≤ 16384 from hd'))).symm

theorem Body.keeps {s t : State} (h : Body s₀ s) (k : Keeps (scr s₀) (esp₀ s₀) s t) : Body s₀ t := by
  refine ⟨k.ebx.trans h.ebx, k.esp.trans h.esp, k.rd.trans h.rd, k.wr.trans h.wr,
    h.frame.trans (k.frame.sub fun r hr => ?_), fun q hq => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  · have hb : 832 ≤ q.2 ∧ q.2 + 4 ≤ 16384 := by
      simp only [Impl.Argon2.X86.HPrime.saved, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> decide
    rw [keeps_word hp k hb.1 hb.2]; exact h.saved q hq
  · rw [← h.pfx]
    exact k.bytes (R := ⟨P s₀ + 832, 4⟩) (by simp) (Offset.disjoint_base _ (by decide) (by decide))
      (hp.stk_scr.sub_right (Offset.sub_base _ (by decide))).symm

end

/-! ## Copying digest bytes -/

/-- The output pointer after `k` output bytes. -/
def OutPtr (s₀ s : State) (k : Nat) : Prop :=
  s.mem.readW (addr (scr s₀) outOff) 32 = op s₀ + BitVec.ofNat 32 k

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem copy_ok {s : State} (h : Body s₀ s) {k n : Nat} (hk : OutPtr s₀ s k)
    (hn : s.gpr .esi = BitVec.ofNat 32 n) (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) (hkn : k + n ≤ ol s₀) :
    WP isa copy s fun t => Body s₀ t ∧ OutPtr s₀ t (k + n) ∧
      bytesAt t.mem ((op s₀).setWidth 64 + BitVec.ofNat 64 k) n = bytesAt s.mem (P s₀ + 768) n ∧
      t.gpr .ebp = s.gpr .ebp ∧
      Frame [⟨(op s₀).setWidth 64 + BitVec.ofNat 64 k, n⟩, ⟨P s₀ + BitVec.ofNat 64 outOff, 4⟩]
        s.mem t.mem := by
  have hs := hp.scr_fits
  have ho := hp.out_fits
  unfold copy
  refine WP.seq (wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => wp_movm
    (VG.Proof.Sha512.X86.ea_of (B := scr s₀) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.ebx])
      outOff)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd, h.wr]
        exact ⟨scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩)
    fun s₃ u₃ => WP.block_nil ?_)
  obtain mem₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain edx₃ : s₃.gpr .edx = scr s₀ + 768 := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, h.ebx]
  obtain edi₃ : s₃.gpr .edi = op s₀ + BitVec.ofNat 32 k := by
    rw [u₃.gpr, u₂.mem, u₁.mem]; exact hk
  obtain esi₃ : s₃.gpr .esi = BitVec.ofNat 32 n := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hn]
  obtain rd₃ : s₃.rd = s₀.rd := by rw [u₃.rd, u₂.rd, u₁.rd, h.rd]
  obtain wr₃ : s₃.wr = s₀.wr := by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]
  obtain e768 : (scr s₀ + 768).setWidth 64 = P s₀ + 768 := setWidth_add (d := 768) (by omega_arith)
  obtain b768 : (scr s₀ + 768).toNat = (scr s₀).toNat + 768 := by
    rw [BitVec.toNat_add, show (768 : BitVec 32).toNat = 768 from rfl]; omega_arith
  obtain bk : (op s₀ + BitVec.ofNat 32 k).toNat = (op s₀).toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega_arith)]; omega_arith
  obtain eOut : addr (op s₀ + BitVec.ofNat 32 k) 0 = (op s₀).setWidth 64 + BitVec.ofNat 64 k := by
    rw [MdStream.X86.addr_add_ofNat (by omega_arith), Nat.add_zero]
  refine WP.seq (Proof.Blake2.X86.Stream.copyLoop_ok (w := 0) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (k := n) hn₁ (by omega_arith) (by rw [b768]; omega_arith)
    (by simp only [Proof.Blake2.bufOff, Nat.reduceDiv, Nat.mul_zero, Nat.add_zero]; rw [bk]; omega_arith)
    edx₃ edi₃ esi₃ (fun i hi => ?_) (fun i hi => ?_) ?_ fun t ht => ?_)
  · have : i < 64 := by omega_arith
    rw [rd₃, wr₃, e768, show P s₀ + 768 + BitVec.ofNat 64 i = P s₀ + BitVec.ofNat 64 (768 + i) by
      rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl]
    refine ⟨scrR s₀, by simp [hp.wr], ?_⟩
    exact Offset.contains_base _ (d := 768 + i) (n := 1) (k := 16384) (by omega_arith) (by omega_arith)
  · rw [wr₃]
    simp only [Proof.Blake2.bufOff, Nat.reduceDiv, Nat.mul_zero, eOut]
    refine ⟨outR s₀, by simp [hp.wr], ?_⟩
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact Offset.contains_base _ (d := k + i) (n := 1) (k := ol s₀) (by omega_arith) (by omega_arith)
  · rw [e768]
    simp only [Proof.Blake2.bufOff, Nat.reduceDiv, Nat.mul_zero, eOut]
    exact (hp.out_scr.sub_left (Offset.sub_base _ (d := k) (n := n) (k := ol s₀) (by omega_arith))).sub_right
      (Offset.sub_base (P s₀) (d := 768) (n := n) (k := 16384) (by omega_arith)) |>.symm
  -- The store of the output pointer.
  obtain o : ∀ x, x ≠ .edx → x ≠ .edi → x ≠ .esi → x ≠ .eax → t.gpr x = s.gpr x := fun x a b c d => by
    rw [ht.other x a b c d, u₃.other _ b, u₂.other _ a, u₁.other _ a]
  obtain ebxT : t.gpr .ebx = scr s₀ := by rw [o _ (by decide) (by decide) (by decide) (by decide), h.ebx]
  obtain wrT : t.wr = s₀.wr := ht.wr.trans wr₃
  have dstE : addr (op s₀ + BitVec.ofNat 32 k) (Proof.Blake2.bufOff 0) =
      (op s₀).setWidth 64 + BitVec.ofNat 64 k := eOut
  obtain lenL : (bytesAt s.mem (P s₀ + 768) n).length = n := by simp [bytesAt]
  obtain memT : t.mem = writeBytes s.mem ((op s₀).setWidth 64 + BitVec.ofNat 64 k)
      (bytesAt s.mem (P s₀ + 768) n) := by
    rw [ht.mem, dstE, e768, mem₃, List.take_of_length_le (by rw [lenL])]
  refine wp_store (VG.Proof.Sha512.X86.ea_of ebxT outOff)
    (by rw [wrT]; exact ⟨scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩)
    fun t' u => WP.block_nil ?_
  obtain eslot : addr (scr s₀) outOff = P s₀ + BitVec.ofNat 64 outOff := scr_addr hp (by decide)
  obtain F : Frame [⟨(op s₀).setWidth 64 + BitVec.ofNat 64 k, n⟩, ⟨P s₀ + BitVec.ofNat 64 outOff, 4⟩]
      s.mem t'.mem := by
    rw [u.mem, memT, eslot]
    refine ((writeBytes_frame s.mem _ _ (R := ⟨(op s₀).setWidth 64 + BitVec.ofNat 64 k, n⟩)
      (by rw [lenL]; exact Region.contains_self _ _)).mono (by simp)).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (Region.contains_self _ _)
  obtain outSub : Region.Sub ⟨(op s₀).setWidth 64 + BitVec.ofNat 64 k, n⟩ (outR s₀) :=
    Offset.sub_base _ (by omega_arith)
  obtain slotSub : Region.Sub ⟨P s₀ + BitVec.ofNat 64 outOff, 4⟩ (scrR s₀) :=
    Offset.sub_base _ (by decide)
  obtain keep : ∀ d, d + 4 ≤ 16384 → (d + 4 ≤ outOff ∨ outOff + 4 ≤ d) →
      t'.mem.readW (addr (scr s₀) d) 32 = s.mem.readW (addr (scr s₀) d) 32 := fun d hd hd' => by
    refine F.readW (r := ⟨addr (scr s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    rw [scr_addr hp (by omega_arith)]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ((hp.out_scr.sub_left outSub).sub_right (Offset.sub_base _ hd)).symm
    · exact Offset.disjoint _ hd' (by omega_arith) (by simp only [outOff]; omega_arith)
  refine ⟨⟨by rw [u.gpr, ebxT], by rw [u.gpr, o _ (by decide) (by decide) (by decide) (by decide), h.esp],
      by rw [u.rd, ht.rd, rd₃], by rw [u.wr, wrT], ?_, fun q hq => ?_, ?_⟩, ?_, ?_,
    by rw [u.gpr, o _ (by decide) (by decide) (by decide) (by decide)], F⟩
  · exact h.frame.trans (F.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨outR s₀, by simp, outSub⟩
      · exact ⟨scrR s₀, by simp, slotSub⟩)
  · have hb : 832 ≤ q.2 ∧ q.2 + 4 ≤ outOff := by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> decide
    rw [keep _ (by simp only [outOff] at hb; omega_arith) (.inl hb.2)]; exact h.saved q hq
  · rw [← h.pfx]
    refine Proof.Blake2.bytesAt_congr fun i hi => F.bytes (R := ⟨P s₀ + 832, 4⟩) (fun r hr => ?_)
      (by simp) hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ((hp.out_scr.sub_left outSub).sub_right
        (Offset.sub_base (P s₀) (d := 832) (n := 4) (k := 16384) (by decide))).symm
    · exact Offset.disjoint (P s₀) (d := 832) (n := 4) (e := outOff) (k := 4) (by decide) (by decide)
        (by decide)
  · show _ = _
    rw [u.mem, Mem.readW_writeW_self32, ht.dstV, BitVec.add_assoc, BitVec.ofNat_add]
  · have wb : bytesAt t.mem ((op s₀).setWidth 64 + BitVec.ofNat 64 k) n = bytesAt s.mem (P s₀ + 768) n := by
      rw [memT]
      have := bytesAt_writeBytes s.mem ((op s₀).setWidth 64 + BitVec.ofNat 64 k)
        (bytesAt s.mem (P s₀ + 768) n) (by rw [lenL]; omega_arith)
      rwa [lenL] at this
    rw [← wb, u.mem]
    refine Proof.Blake2.bytesAt_congr fun i hi =>
      ((Frame.refl [⟨addr (scr s₀) outOff, 4⟩] t.mem).writeW (List.mem_singleton_self _) _
        (Region.contains_self _ _)).bytes (R := ⟨(op s₀).setWidth 64 + BitVec.ofNat 64 k, n⟩) ?_ (by simp; omega_arith) hi
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    rw [eslot]
    exact (hp.out_scr.sub_left outSub).sub_right slotSub

end

end VG.Proof.Argon2.X86.HPrime

end

/-!
# Argon2 H′ on x86 (32-bit): the output

`Out s₀ s xs`: the output so far, `xs`, its pointer and the bytes left.
`emit_ok` writes a 32-byte prefix of the digest, `copyRemaining_ok` the last
bytes.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (copy outOff leftOff emitPrefix copyRemaining)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_movi wp_movm wp_store wp_subi contains_addr)

/-- The output so far. -/
structure Out (s₀ s : State) (xs : List Byte) : Prop where
  ptr : OutPtr s₀ s xs.length
  left : s.mem.readW (addr (scr s₀) leftOff) 32 = BitVec.ofNat 32 (ol s₀ - xs.length)
  bytes : bytesAt s.mem ((op s₀).setWidth 64) xs.length = xs
  len : xs.length ≤ ol s₀

/-- The digest. -/
abbrev digest (s₀ s : State) : List Byte := bytesAt s.mem (P s₀ + 768) 64

section
variable {s₀ : State} (hp : Pre s₀)
include hp

/-- The output and its slots are kept by the hash macros. -/
theorem Out.keeps {s t : State} {xs : List Byte} (h : Out s₀ s xs)
    (k : Keeps (scr s₀) (esp₀ s₀) s t) : Out s₀ t xs := by
  refine ⟨?_, ?_, ?_, h.len⟩
  · show _ = _; rw [keeps_word hp k (by decide) (by decide)]; exact h.ptr
  · rw [keeps_word hp k (by decide) (by decide)]; exact h.left
  · have kb := k.bytes (R := ⟨(op s₀).setWidth 64, xs.length⟩)
      (by have := h.len; have := hp.out_fits; simp; omega_arith)
      ((hp.out_scr.sub_left (Region.sub_prefix h.len)).sub_right (Region.sub_prefix (by decide)))
      ((hp.stk_out.sub_right (Region.sub_prefix h.len)).symm)
    simp only at kb
    rw [kb]; exact h.bytes

/-- A word of `scratch` outside the output pointer's slot is kept by `copy`. -/
theorem copy_word {s t : State} {k n : Nat} (hkn : k + n ≤ ol s₀)
    (f : Frame [⟨(op s₀).setWidth 64 + BitVec.ofNat 64 k, n⟩, ⟨P s₀ + BitVec.ofNat 64 outOff, 4⟩]
      s.mem t.mem) {d : Nat} (hd : d + 4 ≤ 16384) (hd' : d + 4 ≤ outOff ∨ outOff + 4 ≤ d) :
    t.mem.readW (addr (scr s₀) d) 32 = s.mem.readW (addr (scr s₀) d) 32 := by
  have ho := hp.out_fits
  refine f.readW (r := ⟨addr (scr s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  rw [scr_addr hp (by omega_arith)]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ((hp.out_scr.sub_left (Offset.sub_base _ (by omega_arith))).sub_right
      (Offset.sub_base _ hd)).symm
  · exact Offset.disjoint _ hd' (by omega_arith) (by simp only [outOff]; omega_arith)

/-- Emit `n` digest bytes after the output `xs`. -/
theorem copyOut_ok {s : State} (b : Body s₀ s) {xs : List Byte} (h : Out s₀ s xs) {n : Nat}
    (hn : s.gpr .esi = BitVec.ofNat 32 n) (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) (hkn : xs.length + n ≤ ol s₀) :
    WP isa copy s fun t => Body s₀ t ∧ t.gpr .ebp = s.gpr .ebp ∧
      bytesAt t.mem ((op s₀).setWidth 64) (xs.length + n) = xs ++ (digest s₀ s).take n ∧
      OutPtr s₀ t (xs.length + n) ∧
      t.mem.readW (addr (scr s₀) leftOff) 32 = s.mem.readW (addr (scr s₀) leftOff) 32 ∧
      digest s₀ t = digest s₀ s := by
  have ho := hp.out_fits
  refine (copy_ok hp b h.ptr hn hn₁ hn₂ hkn).mono ?_
  rintro t ⟨bt, pt, bytes, ebp, f⟩
  refine ⟨bt, ebp, ?_, pt, copy_word hp hkn f (by decide) (by decide), ?_⟩
  swap
  · refine Proof.Blake2.bytesAt_congr fun i hi => f.bytes (R := ⟨P s₀ + 768, 64⟩) (fun r hr => ?_)
      (by simp) hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ((hp.out_scr.sub_left (Offset.sub_base _ (d := xs.length) (n := n) (k := ol s₀) (by omega_arith))).sub_right
        (Offset.sub_base (P s₀) (d := 768) (n := 64) (k := 16384) (by decide))).symm
    · exact Offset.disjoint (P s₀) (d := 768) (n := 64) (e := outOff) (k := 4) (by decide) (by decide)
        (by decide)
  obtain old : bytesAt t.mem ((op s₀).setWidth 64) xs.length = bytesAt s.mem ((op s₀).setWidth 64) xs.length := by
    refine Proof.Blake2.bytesAt_congr fun i hi => f.bytes (R := ⟨(op s₀).setWidth 64, xs.length⟩)
      (fun r hr => ?_) (by have := h.len; simp; omega_arith) hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.base_disjoint _ (by omega_arith) (by omega_arith)
    · exact (hp.out_scr.sub_left (Region.sub_prefix (by omega_arith))).sub_right
        (Offset.sub_base _ (by decide))
  rw [Proof.Blake2.bytesAt_add, bytes, bytesAt_take _ _ _ _ hn₂, old, h.bytes]

/-- Emit a 32-byte prefix of the digest. -/
theorem emit_ok {s : State} (b : Body s₀ s) {xs : List Byte} (h : Out s₀ s xs)
    (hkn : xs.length + 32 ≤ ol s₀) :
    WP isa emitPrefix s fun t => Body s₀ t ∧ t.gpr .ebp = s.gpr .ebp ∧
      Out s₀ t (xs ++ (digest s₀ s).take 32) ∧ digest s₀ t = digest s₀ s := by
  have ho := hp.out_fits
  have hs := hp.scr_fits
  unfold emitPrefix
  refine WP.seq (wp_movi fun s₁ u₁ => WP.block_nil ?_)
  obtain b₁ : Body s₀ s₁ := ⟨by rw [u₁.other _ (by decide), b.ebx], by rw [u₁.other _ (by decide), b.esp],
    by rw [u₁.rd, b.rd], by rw [u₁.wr, b.wr], by rw [u₁.mem]; exact b.frame,
    fun q hq => by rw [u₁.mem]; exact b.saved q hq, by rw [u₁.mem]; exact b.pfx⟩
  obtain h₁ : Out s₀ s₁ xs := ⟨by show _ = _; rw [u₁.mem]; exact h.ptr, by rw [u₁.mem]; exact h.left,
    by rw [u₁.mem]; exact h.bytes, h.len⟩
  refine WP.seq ((copyOut_ok hp b₁ h₁ u₁.gpr (by decide) (by decide) hkn).mono
    fun s₂ ⟨b₂, e₂, by₂, p₂, l₂, d₂⟩ => ?_)
  obtain rl : InRegions (s₂.rd ++ s₂.wr) (addr (scr s₀) leftOff) 4 := by
    rw [b₂.rd, b₂.wr]; exact ⟨scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩
  refine wp_movm (VG.Proof.Sha512.X86.ea_of b₂.ebx leftOff) rl fun s₃ u₃ => wp_subi fun s₄ u₄ _ => ?_
  obtain ebx₄ : s₄.gpr .ebx = scr s₀ := by rw [u₄.other _ (by decide), u₃.other _ (by decide), b₂.ebx]
  obtain wl : InRegions s₄.wr (addr (scr s₀) leftOff) 4 := by
    rw [u₄.wr, u₃.wr, b₂.wr]; exact ⟨scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩
  refine wp_store (VG.Proof.Sha512.X86.ea_of ebx₄ leftOff) wl fun s₅ u₅ => WP.block_nil ?_
  obtain m₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  obtain d₁ : digest s₀ s₁ = digest s₀ s := by simp only [digest, u₁.mem]
  obtain v₄ : s₄.gpr .eax = BitVec.ofNat 32 (ol s₀ - (xs.length + 32)) := by
    rw [u₄.gpr, u₃.gpr, l₂, u₁.mem, h.left]
    exact (Proof.Sha256.X86.Stream.sub_ofNat (a := ol s₀ - xs.length) (b := 32) (by omega_arith)).trans
      (by congr 1)
  obtain e₅ : s₅.mem = s₂.mem.writeW (P s₀ + BitVec.ofNat 64 leftOff) (BitVec.ofNat 32 (ol s₀ - (xs.length + 32))) := by
    rw [u₅.mem, m₄, v₄, scr_addr hp (by decide)]
  obtain F : Frame [⟨P s₀ + BitVec.ofNat 64 leftOff, 4⟩] s₂.mem s₅.mem := by
    rw [e₅]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain keepW : ∀ d, d + 4 ≤ 16384 → (d + 4 ≤ leftOff ∨ leftOff + 4 ≤ d) →
      s₅.mem.readW (addr (scr s₀) d) 32 = s₂.mem.readW (addr (scr s₀) d) 32 := fun d hd hd' => by
    rw [e₅, scr_addr hp (by omega_arith)]
    exact Mem.readW_writeW_sep (Offset.sep _ hd' (by omega_arith) (by simp only [leftOff]; omega_arith)) (by decide)
  obtain keepB : ∀ R : Region, R.len ≤ 2 ^ 64 → R.Disjoint ⟨P s₀ + BitVec.ofNat 64 leftOff, 4⟩ →
      bytesAt s₅.mem R.base R.len = bytesAt s₂.mem R.base R.len := fun R hR hd =>
    Proof.Blake2.bytesAt_congr fun i hi => F.bytes (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hd) hR hi
  obtain slotScr : Region.Sub ⟨P s₀ + BitVec.ofNat 64 leftOff, 4⟩ (scrR s₀) := Offset.sub_base _ (by decide)
  obtain len' : (xs ++ (digest s₀ s).take 32).length = xs.length + 32 := by
    simp [digest, bytesAt]
  refine ⟨⟨by rw [u₅.gpr, ebx₄], by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), b₂.esp],
      by rw [u₅.rd, u₄.rd, u₃.rd, b₂.rd], by rw [u₅.wr, u₄.wr, u₃.wr, b₂.wr],
      b₂.frame.trans (F.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, slotScr⟩),
      fun q hq => ?_, ?_⟩,
    by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), e₂, u₁.other _ (by decide)], ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · have hb : 832 ≤ q.2 ∧ q.2 + 4 ≤ leftOff := by
      simp only [Impl.Argon2.X86.HPrime.saved, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> decide
    rw [keepW _ (by simp only [leftOff] at hb; omega_arith) (.inl hb.2)]; exact b₂.saved q hq
  · rw [keepB ⟨P s₀ + 832, 4⟩ (by simp) (Offset.disjoint (P s₀) (d := 832) (n := 4) (e := leftOff) (k := 4)
      (by decide) (by decide) (by decide))]
    exact b₂.pfx
  · show _ = _
    rw [len', keepW _ (by decide) (by decide)]; exact p₂
  · rw [len', e₅, scr_addr hp (by decide), Mem.readW_writeW_self32]
  · rw [len']
    obtain k₁ := keepB ⟨(op s₀).setWidth 64, xs.length + 32⟩ (by simp; omega_arith)
      ((hp.out_scr.sub_left (Region.sub_prefix (by omega_arith))).sub_right slotScr)
    simp only at k₁
    rw [k₁, by₂, d₁]
  · rw [len']; exact hkn
  · have k₂ := keepB ⟨P s₀ + 768, 64⟩ (by simp) (Offset.disjoint (P s₀) (d := 768) (n := 64)
      (e := leftOff) (k := 4) (by decide) (by decide) (by decide))
    simp only at k₂
    show bytesAt _ _ _ = bytesAt _ _ _
    rw [k₂]; exact d₂.trans d₁

/-- Copy the bytes left. -/
theorem copyRemaining_ok {s : State} (b : Body s₀ s) {xs : List Byte} (h : Out s₀ s xs)
    (hn₁ : xs.length < ol s₀) (hn₂ : ol s₀ - xs.length ≤ 64) :
    WP isa copyRemaining s fun t => Body s₀ t ∧ t.gpr .ebp = s.gpr .ebp ∧
      bytesAt t.mem ((op s₀).setWidth 64) (ol s₀) = xs ++ (digest s₀ s).take (ol s₀ - xs.length) := by
  have hs := hp.scr_fits
  unfold copyRemaining
  obtain rl : InRegions (s.rd ++ s.wr) (addr (scr s₀) leftOff) 4 := by
    rw [b.rd, b.wr]; exact ⟨scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩
  refine WP.seq (wp_movm (VG.Proof.Sha512.X86.ea_of b.ebx leftOff) rl fun s₁ u₁ => WP.block_nil ?_)
  obtain b₁ : Body s₀ s₁ := ⟨by rw [u₁.other _ (by decide), b.ebx], by rw [u₁.other _ (by decide), b.esp],
    by rw [u₁.rd, b.rd], by rw [u₁.wr, b.wr], by rw [u₁.mem]; exact b.frame,
    fun q hq => by rw [u₁.mem]; exact b.saved q hq, by rw [u₁.mem]; exact b.pfx⟩
  obtain h₁ : Out s₀ s₁ xs := ⟨by show _ = _; rw [u₁.mem]; exact h.ptr, by rw [u₁.mem]; exact h.left,
    by rw [u₁.mem]; exact h.bytes, h.len⟩
  refine (copyOut_ok hp b₁ h₁ (n := ol s₀ - xs.length) (by rw [u₁.gpr, h.left]) (by omega_arith) hn₂
    (by omega_arith)).mono fun t ⟨bt, et, byt, _, _, _⟩ => ⟨bt, by rw [et, u₁.other _ (by decide)], ?_⟩
  rw [show xs.length + (ol s₀ - xs.length) = ol s₀ by omega_arith] at byt
  rw [byt]; simp only [digest, u₁.mem]

end

end VG.Proof.Argon2.X86.HPrime

end

end


@[expose] public section

section

section

/-!
# Argon2 H′ on x86 (32-bit): the first digest

`first_ok`: `first` leaves H(min(out_len, 64), LE32(out_len) ‖ input) at the
start of the digest, `scratch[768, 832)`. The input is read before anything
is written to the output, so the two may overlap.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (init update finalize absorbFixed chooseLength absorbInput finishInput
  first leftOff)
open VG.Proof.Sha256.X86.Stream (Upd Fupd wp_movi wp_movm wp_cmpi)
open VG.Proof.Blake2.X86.CompressB (wp_addC wp_adcC)
open VG.Impl.Sha512.X86 (at_)

/-- Steps that keep memory, the permissions, `ebx`, `ebp` and `esp`. -/
theorem Keeps.same {B E : BitVec 32} {s t : State} (hb : t.gpr .ebx = s.gpr .ebx)
    (hp : t.gpr .ebp = s.gpr .ebp) (hs : t.gpr .esp = s.gpr .esp) (hm : t.mem = s.mem)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : Keeps B E s t :=
  ⟨hb, hp, hs, hrd, hwr, hm ▸ Frame.refl _ _⟩

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem arg_addr {i : Nat} (hi : i < 5) :
    addr (esp₀ s₀) (4 + 4 * i) = (esp₀ s₀).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
  addr_eq (by have := hp.esp_hi; omega_arith)

theorem arg_sub {i : Nat} (hi : i < 5) : Region.Sub ⟨addr (esp₀ s₀) (4 + 4 * i), 4⟩ (argR s₀) := by
  show Region.Sub _ ⟨addr (esp₀ s₀) (4 + 4 * 0), 20⟩
  rw [arg_addr hp hi, arg_addr hp (by decide)]
  exact Offset.sub _ (by omega_arith) (by omega_arith)

/-- The arguments are kept in the body. -/
theorem Body.arg {s : State} (b : Body s₀ s) {i : Nat} (hi : i < 5) :
    s.mem.readW (addr (esp₀ s₀) (4 + 4 * i)) 32 = arg s₀ i := by
  have he := hp.esp_hi
  have hl := hp.esp_lo
  refine b.frame.readW (r := ⟨addr (esp₀ s₀) (4 + 4 * i), 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.arg_out.sub_left (arg_sub hp hi)
  · exact hp.arg_scr.sub_left (arg_sub hp hi)
  · show Region.Disjoint _ ⟨(esp₀ s₀ - BitVec.ofNat 32 60).setWidth 64, 60⟩
    rw [arg_addr hp hi, Taint.sub_setWidth hl]
    exact Offset.disjoint_below _ (by omega_arith)

theorem Body.arg_in {s : State} (b : Body s₀ s) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) (4 + 4 * i)) 4 := by
  refine ⟨argR s₀, by simp [b.rd, hp.rd], ?_⟩
  show Region.Contains ⟨addr (esp₀ s₀) (4 + 4 * 0), 20⟩ _ _
  rw [arg_addr hp hi, arg_addr hp (by decide)]
  exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)

omit hp in
theorem Out.same {s t : State} {xs : List Byte} (h : Out s₀ s xs) (hm : t.mem = s.mem) : Out s₀ t xs :=
  ⟨by show _ = _; rw [hm]; exact h.ptr, by rw [hm]; exact h.left, by rw [hm]; exact h.bytes, h.len⟩

/-- `edx := min(out_len, 64)`. -/
theorem choose_ok {s : State} (b : Body s₀ s) (o : Out s₀ s []) :
    WP isa chooseLength s fun t => t.gpr .edx = BitVec.ofNat 32 (min (ol s₀) 64) ∧
      Keeps (scr s₀) (esp₀ s₀) s t := by
  have hs := hp.scr_fits
  obtain hol := (arg s₀ 3).isLt
  unfold chooseLength
  obtain rl : InRegions (s.rd ++ s.wr) (addr (scr s₀) leftOff) 4 := by
    rw [b.rd, b.wr]
    exact ⟨scrR s₀, by simp [hp.wr], Proof.Sha256.X86.Stream.contains_addr (by decide) (by decide) hs⟩
  refine WP.seq (wp_movm (VG.Proof.Sha512.X86.ea_of b.ebx leftOff) rl fun s₁ u₁ =>
    wp_cmpi fun s₂ f₂ cf₂ _ => WP.block_nil ?_)
  obtain e₁ : s₁.gpr .edx = BitVec.ofNat 32 (ol s₀) := by rw [u₁.gpr, o.left]; rfl
  have k₂ : Keeps (scr s₀) (esp₀ s₀) s s₂ := Keeps.same
    (by rw [f₂.gpr, u₁.other _ (by decide)]) (by rw [f₂.gpr, u₁.other _ (by decide)])
    (by rw [f₂.gpr, u₁.other _ (by decide)]) (by rw [f₂.mem, u₁.mem]) (by rw [f₂.rd, u₁.rd])
    (by rw [f₂.wr, u₁.wr])
  refine WP.ite (decide (ol s₀ < 65)) (by
      show s₂.cf = _
      rw [cf₂, e₁, Proof.Sha256.X86.Stream.toNat_ofNat_lt hol]; rfl)
    (fun h => WP.block_nil ⟨?_, k₂⟩) (fun h => wp_movi fun s₃ u₃ => WP.block_nil ⟨?_, ?_⟩)
  · have : ol s₀ ≤ 64 := by simp only [decide_eq_true_eq] at h; omega_arith
    rw [f₂.gpr, e₁, Nat.min_eq_left this]
  · have : 64 ≤ ol s₀ := by simp only [decide_eq_false_iff_not] at h; omega_arith
    rw [u₃.gpr, Nat.min_eq_right this]; rfl
  · exact k₂.trans (Keeps.same (u₃.other _ (by decide)) (u₃.other _ (by decide)) (u₃.other _ (by decide))
      u₃.mem u₃.rd u₃.wr)

end

/-! ## The steps of `first` -/

/-- The state before and between the steps of `first`: the body, no output
yet, `ebp` and the input kept. -/
structure F0 (s₀ s : State) : Prop where
  body : Body s₀ s
  out : Out s₀ s []
  ebp : s.gpr .ebp = s₀.gpr .ebp
  input : bytesAt s.mem ((inp s₀).setWidth 64) (inl s₀) = bytesAt s₀.mem ((inp s₀).setWidth 64) (inl s₀)

/-- The length of the first digest. -/
abbrev nF (s₀ : State) : Nat := min (ol s₀) 64

/-- The input, on entry. -/
abbrev inB (s₀ : State) : List Byte := bytesAt s₀.mem ((inp s₀).setWidth 64) (inl s₀)

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem F0.keeps {s t : State} (h : F0 s₀ s) (k : Keeps (scr s₀) (esp₀ s₀) s t) : F0 s₀ t := by
  refine ⟨h.body.keeps hp k, h.out.keeps hp k, k.ebp.trans h.ebp, ?_⟩
  have hif := hp.in_fits
  have := k.bytes (R := inR s₀) (by simp; omega_arith)
    (hp.in_scr.sub_right (Region.sub_prefix (by decide))) hp.stk_in.symm
  simp only at this
  rw [this, h.input]

theorem nF_pos : 1 ≤ nF s₀ := by have := hp.ol_pos; simp only [nF]; omega_arith

theorem first_choose {s : State} (h : F0 s₀ s) :
    WP isa chooseLength s fun t => F0 s₀ t ∧ t.gpr .edx = BitVec.ofNat 32 (nF s₀) :=
  (choose_ok hp h.body h.out).mono fun _ ⟨e, k⟩ => ⟨h.keeps hp k, e⟩

theorem first_init {s : State} (h : F0 s₀ s ∧ s.gpr .edx = BitVec.ofNat 32 (nF s₀)) :
    WP isa init s fun t => F0 s₀ t ∧
      Repr b (Spec.Blake2.init b (nF s₀) 0) t.mem (P s₀) [] := by
  obtain c := h.1.body.ctx hp
  refine (init_ok c h.2 (nF_pos hp) (Nat.min_le_right _ _)).mono fun t ⟨r, cs, rd, wr, f⟩ => ⟨?_, r⟩
  refine h.1.keeps hp (Keeps.of_call (of_callee cs) rd wr f fun r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, below_sub (by decide) c.lo⟩

theorem pfx_cov {s : State} (b : Body s₀ s) : Covers [⟨P s₀ + BitVec.ofNat 64 832, 4⟩] s.wr := by
  rw [b.wr, hp.wr]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s₀, by simp, 832, rfl, by simp⟩

theorem first_fixed {s : State}
    (h : F0 s₀ s ∧ Repr b (Spec.Blake2.init b (nF s₀) 0) s.mem (P s₀) []) :
    WP isa (absorbFixed 832 4) s fun t => F0 s₀ t ∧
      Repr b (Spec.Blake2.init b (nF s₀) 0) t.mem (P s₀) (Spec.Argon2.le32 (ol s₀)) := by
  have hs := hp.scr_fits
  refine (absorbFixed_ok (h.1.body.ctx hp) (offset := 832) (size := 4) (by omega_arith) (by decide)
    (by decide) (pfx_cov hp h.1.body) (hp.stk_scr.sub_right (Offset.sub_base _ (by decide))) h.2).mono
    fun t ⟨r, k⟩ => ⟨h.1.keeps hp k, ?_⟩
  rw [show BitVec.ofNat 64 832 = (832 : Addr) from rfl, h.1.body.pfx] at r
  exact r

/-- The instructions before `absorbInput`'s call of `update`. -/
theorem absorbInput_blk {s : State} (h : F0 s₀ s) :
    WP isa (.block [.mov .ecx (.imm 4), .mov .edx (.imm 0), .mov .esi (.mem (at_ .esp 4)),
      .mov .edi (.mem (at_ .esp 8))]) s fun t =>
      UpdateIn (scr s₀) (esp₀ s₀) (inp s₀) (inl s₀) 4 0 t ∧ Keeps (scr s₀) (esp₀ s₀) s t ∧ t.mem = s.mem := by
  have b := h.body
  refine wp_movi fun s₄ u₄ => wp_movi fun s₅ u₅ =>
    wp_movm (VG.Proof.Sha512.X86.ea_of (by rw [u₅.other _ (by decide), u₄.other _ (by decide), b.esp])
      4) (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact b.arg_in hp (i := 0) (by decide)) fun s₆ u₆ =>
    wp_movm (VG.Proof.Sha512.X86.ea_of (by
        rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), b.esp]) 8)
      (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact b.arg_in hp (i := 1) (by decide)) fun s₇ u₇ =>
    WP.block_nil ?_
  obtain m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  obtain o₇ : ∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .edi → s₇.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₇.other _ h4, u₆.other _ h3, u₅.other _ h2, u₄.other _ h1]
  obtain k₇ : Keeps (scr s₀) (esp₀ s₀) s s₇ := Keeps.same (o₇ _ (by decide) (by decide) (by decide) (by decide))
    (o₇ _ (by decide) (by decide) (by decide) (by decide)) (o₇ _ (by decide) (by decide) (by decide) (by decide))
    m₇ (by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd]) (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr])
  obtain b₇ := b.keeps hp k₇
  refine ⟨⟨b₇.ctx hp, ?_, ?_, ?_, ?_, ?_⟩, k₇, m₇⟩
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem]; exact b.arg hp (i := 0) (by decide)
  · rw [u₇.gpr, u₆.mem, u₅.mem, u₄.mem, b.arg hp (i := 1) (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
  · rw [b₇.rd, b₇.wr, hp.rd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨inR s₀, by simp, 0, by simp, by simp⟩

theorem first_input {s : State}
    (h : F0 s₀ s ∧ Repr b (Spec.Blake2.init b (nF s₀) 0) s.mem (P s₀) (Spec.Argon2.le32 (ol s₀))) :
    WP isa absorbInput s fun t => F0 s₀ t ∧
      Repr b (Spec.Blake2.init b (nF s₀) 0) t.mem (P s₀) (Spec.Argon2.le32 (ol s₀) ++ inB s₀) := by
  have hif := hp.in_fits
  obtain hil := (arg s₀ 1).isLt
  unfold absorbInput
  refine WP.seq ((absorbInput_blk hp h.1).mono fun s₇ ⟨⟨c₇, esi₇, edi₇, x₇, y₇, hDc⟩, k₇, m₇⟩ => ?_)
  obtain cnt₇ : s₇.gpr .edx ++ s₇.gpr .ecx = BitVec.ofNat 64 (Spec.Argon2.le32 (ol s₀)).length := by
    rw [Proof.Argon2.le32_length, x₇, y₇]; rfl
  obtain F₇ := h.1.keeps hp k₇
  refine (update_ok c₇ (h0 := Spec.Blake2.init Spec.Blake2.b (nF s₀) 0) esi₇ edi₇ hif hDc
    (hp.in_scr.sub_right (Region.sub_prefix (by decide))) hp.stk_in (by rw [m₇]; exact h.2) cnt₇
    (by rw [Proof.Argon2.le32_length]; omega_arith)).mono fun s₈ ⟨r₈, cs₈, rd₈, wr₈, f₈⟩ => ?_
  rw [F₇.input] at r₈
  refine ⟨F₇.keeps hp (Keeps.of_call (of_callee cs₈) rd₈ wr₈ f₈ fun r hr => ?_), r₈⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩

/-- The count of the prefix and the input, as `finishInput` passes it. -/
abbrev cntLo (s₀ : State) : BitVec 32 := BitVec.ofNat 32 (inl s₀ + 4)
abbrev cntHi (s₀ : State) : BitVec 32 := BitVec.ofNat 32 ((inl s₀ + 4) / 2 ^ 32)

/-- The instructions before `finishInput`'s call of `finalize`. -/
theorem finishInput_blk {s : State} (h : F0 s₀ s) :
    WP isa (.block [.mov .ecx (.mem (at_ .esp 8)), .mov .edx (.imm 0), .alu .add .ecx (.imm 4),
      .alu .adc .edx (.imm 0)]) s fun t =>
      FinalizeIn (scr s₀) (esp₀ s₀) (cntLo s₀) (cntHi s₀) t ∧ Keeps (scr s₀) (esp₀ s₀) s t ∧
        t.mem = s.mem := by
  obtain hil := (arg s₀ 1).isLt
  have b := h.body
  refine wp_movm (VG.Proof.Sha512.X86.ea_of b.esp 8) (b.arg_in hp (i := 1) (by decide))
    fun s₉ u₉ => wp_movi fun s₁₀ u₁₀ => wp_addC fun s₁₁ u₁₁ cf₁₁ => wp_adcC cf₁₁ fun s₁₂ u₁₂ _ =>
    WP.block_nil ?_
  obtain m₁₂ : s₁₂.mem = s.mem := by rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem]
  obtain o₁₂ : ∀ r, r ≠ .ecx → r ≠ .edx → s₁₂.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₁₂.other _ h2, u₁₁.other _ h1, u₁₀.other _ h2, u₉.other _ h1]
  obtain k₁₂ : Keeps (scr s₀) (esp₀ s₀) s s₁₂ := Keeps.same (o₁₂ _ (by decide) (by decide))
    (o₁₂ _ (by decide) (by decide)) (o₁₂ _ (by decide) (by decide)) m₁₂
    (by rw [u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd]) (by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr])
  obtain ecx₉ : s₉.gpr .ecx = BitVec.ofNat 32 (inl s₀) := by
    rw [u₉.gpr, b.arg hp (i := 1) (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨⟨(b.keeps hp k₁₂).ctx hp, ?_, ?_⟩, k₁₂, m₁₂⟩
  · show _ = BitVec.ofNat 32 (inl s₀ + 4)
    rw [u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide), ecx₉, BitVec.ofNat_add]; rfl
  · show _ = BitVec.ofNat 32 ((inl s₀ + 4) / 2 ^ 32)
    rw [u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.gpr, u₁₀.other _ (by decide), ecx₉]
    rw [← Proof.Blake2.X86.Stream.carry_ofNat (inl s₀) 4 (by decide), Nat.div_eq_of_lt hil]
    rfl

theorem first_finish {s : State}
    (h : F0 s₀ s ∧ Repr b (Spec.Blake2.init b (nF s₀) 0) s.mem (P s₀) (Spec.Argon2.le32 (ol s₀) ++ inB s₀)) :
    WP isa finishInput s fun t => F0 s₀ t ∧
      (digest s₀ t).take (nF s₀) = Spec.Argon2.H (nF s₀) (Spec.Argon2.le32 (ol s₀) ++ inB s₀) := by
  have hif := hp.in_fits
  unfold finishInput
  refine WP.seq ((finishInput_blk hp h.1).mono fun s₁₂ ⟨⟨c₁₂, x₁₂, y₁₂⟩, k₁₂, m₁₂⟩ => ?_)
  obtain cnt : s₁₂.gpr .edx ++ s₁₂.gpr .ecx =
      BitVec.ofNat 64 (Spec.Argon2.le32 (ol s₀) ++ inB s₀).length := by
    rw [x₁₂, y₁₂, List.length_append, Proof.Argon2.le32_length]
    simp only [inB, bytesAt, List.length_map, List.length_range]
    apply BitVec.eq_of_toNat_eq
    rw [Proof.Blake2.X86.Stream.append_ofNat (by omega_arith), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  obtain F₁₂ := h.1.keeps hp k₁₂
  refine (finalize_ok c₁₂ (by rw [m₁₂]; exact h.2) cnt
    (by simp only [List.length_append, Proof.Argon2.le32_length, inB, bytesAt, List.length_map,
      List.length_range]; omega_arith)).mono ?_
  rintro t ⟨d, cs, rd, wr, f⟩
  refine ⟨F₁₂.keeps hp (Keeps.of_call (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> exact cs _ (by decide) (by decide)) rd wr f fun r hr => ?_), ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  · show (bytesAt t.mem ((scr s₀).setWidth 64 + 768) 64).take _ = _
    rw [d, Proof.Argon2.H_stream]

/-- `first` hashes the length prefix and the input. -/
theorem first_ok {s : State} (h : F0 s₀ s) :
    WP isa first s fun t => F0 s₀ t ∧
      (digest s₀ t).take (nF s₀) = Spec.Argon2.H (nF s₀) (Spec.Argon2.le32 (ol s₀) ++ inB s₀) := by
  unfold first
  exact WP.seq ((first_choose hp h).mono fun _ h₁ => WP.seq ((first_init hp h₁).mono fun _ h₂ =>
    WP.seq ((first_fixed hp h₂).mono fun _ h₃ => WP.seq ((first_input hp h₃).mono fun _ h₄ =>
      first_finish hp h₄))))

end

end VG.Proof.Argon2.X86.HPrime

end

/-!
# Argon2 H′ on x86 (32-bit): the chain of 64-byte hashes

`chain_ok`: after the first prefix V₁[0, 32) of a long output, each iteration
hashes the digest again and emits the prefix of the new one, while more than
64 bytes are left. The output is then V₁[0, 32) ‖ `chainPrefixes j V₁` and the
digest `chainDigest j V₁`, with 33 to 64 bytes left.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (next emitPrefix cmpLeft chain leftOff)
open VG.Proof.Sha256.X86.Stream (Upd Fupd wp_movi wp_movm wp_cmpi)
open VG.Proof.Argon2 (chainDigest chainPrefixes)

theorem chainDigest_succ' (j : Nat) (v : List Byte) :
    chainDigest (j + 1) v = Spec.Argon2.H 64 (chainDigest j v) := by
  induction j generalizing v with
  | zero => rfl
  | succ j ih => exact ih (Spec.Argon2.H 64 v)

theorem chainPrefixes_succ' (j : Nat) (v : List Byte) :
    chainPrefixes (j + 1) v = chainPrefixes j v ++ (Spec.Argon2.H 64 (chainDigest j v)).take 32 := by
  induction j generalizing v with
  | zero => simp [chainPrefixes, chainDigest]
  | succ j ih =>
    rw [chainPrefixes, ih, chainPrefixes, chainDigest, List.append_assoc]

theorem finalHash_length (h0 : HashValue 64) (d : List Byte) : (finalHash b h0 d).length = 64 := by
  simp only [finalHash, Proof.Argon2.wordList_length, Vector.length_toList]

/-- The output after `j` iterations. -/
abbrev chainOut (V : List Byte) (j : Nat) : List Byte := V.take 32 ++ chainPrefixes j V

theorem chainOut_length {V : List Byte} (hV : V.length = 64) (j : Nat) :
    (chainOut V j).length = 32 + 32 * j := by
  simp only [chainOut, List.length_append, List.length_take, hV, Proof.Argon2.chainPrefixes_length]
  omega_arith

section
variable {s₀ : State} (hp : Pre s₀)
include hp

/-- `cmpLeft`: CF is whether fewer than 65 bytes are left. -/
theorem cmp_ok {s : State} (b : Body s₀ s) {xs : List Byte} (o : Out s₀ s xs) :
    WP isa (.block cmpLeft) s fun t => t.cf = some (decide (ol s₀ - xs.length < 65)) ∧
      Keeps (scr s₀) (esp₀ s₀) s t ∧ t.mem = s.mem := by
  have hs := hp.scr_fits
  obtain hol : ol s₀ < 2 ^ 32 := (arg s₀ 3).isLt
  unfold cmpLeft
  obtain rl : InRegions (s.rd ++ s.wr) (addr (scr s₀) leftOff) 4 := by
    rw [b.rd, b.wr]
    exact ⟨scrR s₀, by simp [hp.wr], Proof.Sha256.X86.Stream.contains_addr (by decide) (by decide) hs⟩
  refine wp_movm (VG.Proof.Sha512.X86.ea_of b.ebx leftOff) rl fun s₁ u₁ =>
    wp_cmpi fun s₂ f₂ cf₂ _ => WP.block_nil ⟨?_, ?_, by rw [f₂.mem, u₁.mem]⟩
  · rw [cf₂, u₁.gpr, o.left, Proof.Sha256.X86.Stream.toNat_ofNat_lt (by omega_arith)]; rfl
  · exact Keeps.same (by rw [f₂.gpr, u₁.other _ (by decide)]) (by rw [f₂.gpr, u₁.other _ (by decide)])
      (by rw [f₂.gpr, u₁.other _ (by decide)]) (by rw [f₂.mem, u₁.mem]) (by rw [f₂.rd, u₁.rd])
      (by rw [f₂.wr, u₁.wr])

/-- What the chain keeps between iterations. -/
structure ChainInv (s₀ : State) (e : BitVec 32) (V : List Byte) (j : Nat) (s : State) : Prop where
  body : Body s₀ s
  ebp : s.gpr .ebp = e
  out : Out s₀ s (chainOut V j)
  digest : digest s₀ s = chainDigest j V

/-- One iteration. -/
theorem iter_ok {e : BitVec 32} {V : List Byte} (hV : V.length = 64) {j : Nat} {s : State}
    (h : ChainInv s₀ e V j s) (hl : 32 + 32 * j + 32 ≤ ol s₀) :
    WP isa (.seq (.block [.mov .edx (.imm 64)]) (.seq next (.seq emitPrefix (.block cmpLeft)))) s
      fun t => ChainInv s₀ e V (j + 1) t ∧
        t.cf = some (decide (ol s₀ - (32 + 32 * (j + 1)) < 65)) := by
  refine WP.seq (wp_movi fun s₁ u₁ => WP.block_nil ?_)
  obtain k₁ : Keeps (scr s₀) (esp₀ s₀) s s₁ := Keeps.same (u₁.other _ (by decide)) (u₁.other _ (by decide))
    (u₁.other _ (by decide)) u₁.mem u₁.rd u₁.wr
  obtain b₁ := h.body.keeps hp k₁
  refine WP.seq ((next_ok (b₁.ctx hp) (n := 64) u₁.gpr (by decide) (by decide)).mono
    fun s₂ ⟨d₂, k₂⟩ => ?_)
  obtain K₂ := k₁.trans k₂
  obtain b₂ := h.body.keeps hp K₂
  obtain o₂ := h.out.keeps hp K₂
  obtain hlen := chainOut_length hV j
  refine WP.seq ((emit_ok hp b₂ o₂ (by rw [hlen]; exact hl)).mono fun s₃ ⟨b₃, e₃, o₃, d₃⟩ => ?_)
  obtain dg : digest s₀ s₂ = chainDigest (j + 1) V := by
    rw [chainDigest_succ', ← h.digest, Proof.Argon2.H_stream,
      List.take_of_length_le (by rw [finalHash_length])]
    rw [u₁.mem] at d₂
    exact d₂
  obtain xs₃ : chainOut V j ++ (digest s₀ s₂).take 32 = chainOut V (j + 1) := by
    rw [dg, chainDigest_succ', chainOut, chainOut, chainPrefixes_succ', List.append_assoc]
  rw [xs₃] at o₃
  refine (cmp_ok hp b₃ o₃).mono fun t ⟨cf, k, m⟩ => ⟨⟨b₃.keeps hp k, ?_, o₃.keeps hp k, ?_⟩, ?_⟩
  · rw [k.ebp, e₃, K₂.ebp, h.ebp]
  · show bytesAt _ _ _ = _
    rw [m]
    exact d₃.trans dg
  · rw [cf, chainOut_length hV]

/-- The chain: iterations while more than 64 bytes are left. -/
theorem chain_ok {e : BitVec 32} {V : List Byte} (hV : V.length = 64) {j : Nat} {s : State}
    (h : ChainInv s₀ e V j s) (hl : 65 ≤ ol s₀ - (32 + 32 * j)) :
    WP isa chain s fun t => ∃ j', ChainInv s₀ e V j' t ∧ 33 ≤ ol s₀ - (32 + 32 * j') ∧
      ol s₀ - (32 + 32 * j') ≤ 64 ∧ 32 + 32 * j' ≤ ol s₀ := by
  unfold chain
  refine WP.loop (M := isa) (fun (m : Nat) (t : State) => ∃ j', m = ol s₀ - (32 + 32 * j') ∧ ChainInv s₀ e V j' t ∧ 65 ≤ m)
    ?_ (ol s₀ - (32 + 32 * j)) s ⟨j, rfl, h, hl⟩
  rintro m t ⟨j', rfl, hi, hm⟩
  refine (iter_ok hp hV hi (by omega_arith)).mono fun u ⟨hu, cf⟩ => ?_
  by_cases hc : ol s₀ - (32 + 32 * (j' + 1)) < 65
  · refine .inl ⟨?_, j' + 1, hu, by omega_arith, by omega_arith, by omega_arith⟩
    show u.cf.map (!·) = some false
    rw [cf]; simp [hc]
  · refine .inr ⟨?_, _, by omega_arith, j' + 1, rfl, hu, by omega_arith⟩
    show u.cf.map (!·) = some true
    rw [cf]; simp [hc]

end

end VG.Proof.Argon2.X86.HPrime

end

/-!
# Argon2 H′ on x86 (32-bit): the output from the first digest

`finish_ok`: `finishOutput` writes H′ to the output, from the first digest:
the digest itself for at most 64 bytes, and otherwise its prefix, the chain
and the last hash (`extend_ok`), of the 33 to 64 bytes left.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (next emitPrefix cmpLeft chain extendDigest finishOutput leftOff)
open VG.Proof.Sha256.X86.Stream (Upd wp_movm)
open VG.Proof.Argon2 (chainDigest chainPrefixes)

section
variable {s₀ : State} (hp : Pre s₀)
include hp

/-- What the chain leaves: the output after `j` iterations and the last hash. -/
def Extended (s₀ : State) (e : BitVec 32) (V : List Byte) (t : State) : Prop :=
  ∃ j, Body s₀ t ∧ t.gpr .ebp = e ∧ Out s₀ t (chainOut V j) ∧
    (digest s₀ t).take (ol s₀ - (32 + 32 * j)) =
      Spec.Argon2.H (ol s₀ - (32 + 32 * j)) (chainDigest j V) ∧
    33 ≤ ol s₀ - (32 + 32 * j) ∧ ol s₀ - (32 + 32 * j) ≤ 64 ∧ 32 + 32 * j ≤ ol s₀

theorem extend_ok {s : State} (b : Body s₀ s) (o : Out s₀ s []) (hol : 65 ≤ ol s₀) :
    WP isa extendDigest s (Extended s₀ (s.gpr .ebp) (digest s₀ s)) := by
  have hs := hp.scr_fits
  obtain hV : (digest s₀ s).length = 64 := by simp [digest, bytesAt]
  unfold extendDigest
  refine WP.seq ((emit_ok hp b o (by simp only [List.length_nil]; omega_arith)).mono
    fun s₁ ⟨b₁, e₁, o₁, d₁⟩ => ?_)
  rw [List.nil_append, show (digest s₀ s).take 32 = chainOut (digest s₀ s) 0 by
    simp [chainOut, chainPrefixes]] at o₁
  obtain i₁ : ChainInv s₀ (s.gpr .ebp) (digest s₀ s) 0 s₁ := ⟨b₁, e₁, o₁, d₁⟩
  refine WP.seq ((cmp_ok hp b₁ o₁).mono fun s₂ ⟨cf₂, k₂, m₂⟩ => ?_)
  rw [chainOut_length hV] at cf₂
  obtain i₂ : ChainInv s₀ (s.gpr .ebp) (digest s₀ s) 0 s₂ :=
    ⟨b₁.keeps hp k₂, k₂.ebp.trans e₁, o₁.keeps hp k₂, by show bytesAt _ _ _ = _; rw [m₂]; exact d₁⟩
  obtain hIte : WP isa (.ite .b (.block []) chain) s₂ fun t => ∃ j, ChainInv s₀ (s.gpr .ebp) (digest s₀ s) j t ∧
      33 ≤ ol s₀ - (32 + 32 * j) ∧ ol s₀ - (32 + 32 * j) ≤ 64 ∧ 32 + 32 * j ≤ ol s₀ := by
    refine WP.ite (decide (ol s₀ - (32 + 32 * 0) < 65)) cf₂ (fun h => WP.block_nil ⟨0, i₂, ?_⟩)
      (fun h => (chain_ok hp hV i₂ ?_).mono fun t h => h)
    · simp only [decide_eq_true_eq] at h; omega_arith
    · simp only [decide_eq_false_iff_not] at h; omega_arith
  refine WP.seq (hIte.mono fun s₃ ⟨j, i₃, l₁, l₂, l₃⟩ => ?_)
  obtain rl : InRegions (s₃.rd ++ s₃.wr) (addr (scr s₀) leftOff) 4 := by
    rw [i₃.body.rd, i₃.body.wr]
    exact ⟨scrR s₀, by simp [hp.wr], Proof.Sha256.X86.Stream.contains_addr (by decide) (by decide) hs⟩
  refine WP.seq (wp_movm (VG.Proof.Sha512.X86.ea_of i₃.body.ebx leftOff) rl fun s₄ u₄ => WP.block_nil ?_)
  obtain k₄ : Keeps (scr s₀) (esp₀ s₀) s₃ s₄ := Keeps.same (u₄.other _ (by decide)) (u₄.other _ (by decide))
    (u₄.other _ (by decide)) u₄.mem u₄.rd u₄.wr
  obtain b₄ := i₃.body.keeps hp k₄
  obtain edx₄ : s₄.gpr .edx = BitVec.ofNat 32 (ol s₀ - (32 + 32 * j)) := by
    rw [u₄.gpr, i₃.out.left, chainOut_length hV]
  refine (next_ok (b₄.ctx hp) edx₄ (by omega_arith) l₂).mono fun t ⟨d, k⟩ => ?_
  obtain K := k₄.trans k
  refine ⟨j, i₃.body.keeps hp K, by rw [K.ebp, i₃.ebp], i₃.out.keeps hp K, ?_, l₁, l₂, l₃⟩
  rw [Proof.Argon2.H_stream, ← i₃.digest]
  rw [u₄.mem] at d
  exact congrArg (List.take _) d

/-- `finishOutput` writes H′ of the input `I` from its first digest. -/
theorem finish_ok {s : State} (b : Body s₀ s) (o : Out s₀ s []) {I : List Byte}
    (hd : (digest s₀ s).take (min (ol s₀) 64) =
      Spec.Argon2.H (min (ol s₀) 64) (Spec.Argon2.le32 (ol s₀) ++ I)) :
    WP isa finishOutput s fun t => Body s₀ t ∧ t.gpr .ebp = s.gpr .ebp ∧
      bytesAt t.mem ((op s₀).setWidth 64) (ol s₀) = Spec.Argon2.hPrime (ol s₀) I := by
  have hpos := hp.ol_pos
  obtain hV : (digest s₀ s).length = 64 := by simp [digest, bytesAt]
  unfold finishOutput
  refine WP.seq ((cmp_ok hp b o).mono fun s₁ ⟨cf₁, k₁, m₁⟩ => ?_)
  simp only [List.length_nil, Nat.sub_zero] at cf₁
  obtain b₁ := b.keeps hp k₁
  obtain o₁ := o.keeps hp k₁
  obtain d₁ : digest s₀ s₁ = digest s₀ s := by show bytesAt _ _ _ = _; rw [m₁]
  obtain hIte : WP isa (.ite .b (.block []) extendDigest) s₁ fun t => Body s₀ t ∧ t.gpr .ebp = s.gpr .ebp ∧
      ∃ xs, Out s₀ t xs ∧ xs.length < ol s₀ ∧ ol s₀ - xs.length ≤ 64 ∧
        xs ++ (digest s₀ t).take (ol s₀ - xs.length) = Spec.Argon2.hPrime (ol s₀) I := by
    refine WP.ite (decide (ol s₀ < 65)) cf₁ (fun h => WP.block_nil ?_) (fun h => ?_)
    · simp only [decide_eq_true_eq] at h
      refine ⟨b₁, k₁.ebp, [], o₁, by simp only [List.length_nil]; omega_arith,
        by simp only [List.length_nil]; omega_arith, ?_⟩
      rw [Nat.min_eq_left (by omega_arith)] at hd
      rw [List.nil_append, List.length_nil, Nat.sub_zero, d₁, hd]
      simp only [Spec.Argon2.hPrime, eq_true (by omega_arith : ol s₀ ≤ 64), ite_true]
    · simp only [decide_eq_false_iff_not] at h
      refine (extend_ok hp b₁ o₁ (by omega_arith)).mono fun t ⟨j, bt, et, ot, dt, l₁, l₂, l₃⟩ =>
        ⟨bt, et.trans k₁.ebp, _, ot, ?_, ?_, ?_⟩
      · rw [chainOut_length (by rw [d₁]; exact hV)]; omega_arith
      · rw [chainOut_length (by rw [d₁]; exact hV)]; omega_arith
      · have V₁ : digest s₀ s₁ = Spec.Argon2.H 64 (Spec.Argon2.le32 (ol s₀) ++ I) := by
          rw [d₁, ← List.take_of_length_le (l := digest s₀ s) (i := 64) (by rw [hV]),
            ← Nat.min_eq_right (by omega_arith : 64 ≤ ol s₀), hd]
        rw [chainOut_length (by rw [d₁]; exact hV), dt, chainOut, ← Proof.Argon2.longHash_chain, V₁]
        obtain hr : (ol s₀ + 31) / 32 - 2 = j + 1 := by omega_arith
        simp only [Spec.Argon2.hPrime, eq_false (by omega_arith : ¬ ol s₀ ≤ 64), ite_false]
        rw [hr, show ol s₀ - 32 * (j + 1) = ol s₀ - (32 + 32 * j) by omega_arith]
  refine WP.seq (hIte.mono fun s₂ ⟨b₂, e₂, xs, o₂, l₁, l₂, h₂⟩ => ?_)
  refine (copyRemaining_ok hp b₂ o₂ l₁ l₂).mono fun t ⟨bt, et, ht⟩ => ⟨bt, et.trans e₂, ?_⟩
  rw [ht, h₂]

end

end VG.Proof.Argon2.X86.HPrime

end

end

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
