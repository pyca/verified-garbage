module

public import VerifiedGarbage.Impl.ForwardCall.X86_64ViaSlots
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineN
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubChecks
public import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Calls of functions through slots, from the proofs of the calls (x86-64)

`Code.viaSlots slots d c` (`Impl/ForwardCall/X86_64ViaSlots.lean`) is `c`
with each of its calls of a function of `slots` made through the word that
holds its address, `off` bytes above the stack pointer on entry (`E`), which
`c` reads as `[rsp + off + d]` when `d` bytes below it. Where those words
hold the addresses (`SlotsOk slots E`) and no region `c` may write overlaps
them, each run of `c` is one of `c` made so, from the same state to the same
state (`Exec.toSlots`): the call through a slot enters its callee from the
state the direct call does. The words stay as they were along the run
(`SlotInv.exec`): `c` writes only its regions and the stack below `rsp`
(`Exec.frameSp`), which is below `E` (`rsp = E - d`), and a frame it pushes is
below `rsp`. So proofs of `c`, whatever they say of its calls, are proofs of
`c` made so (`SlotVerified.of_verified`), constant time included: a run of
`c` made so leaks what the run of `c` does, with the slot's address and the
callee's at each call made so (`Exec.ofSlots₂`).
-/

@[expose] public section

namespace VG.X86_64

open VG.Impl.ForwardCall.X86_64

/-! ## The depth -/

theorem depth_le_x86_64Depth : ∀ c : Prog isa, 8 * c.depth ≤ c.x86_64Depth
  | .block _ => by simp [Code.depth, Code.x86_64Depth]
  | .seq a b => by
    have := depth_le_x86_64Depth a; have := depth_le_x86_64Depth b
    simp only [Code.depth, Code.x86_64Depth]; omega
  | .ite _ a b => by
    have := depth_le_x86_64Depth a; have := depth_le_x86_64Depth b
    simp only [Code.depth, Code.x86_64Depth]; omega
  | .loop b _ => by have := depth_le_x86_64Depth b; simp only [Code.depth, Code.x86_64Depth]; omega
  | .call _ b => by have := depth_le_x86_64Depth b; simp only [Code.depth, Code.x86_64Depth]; omega
  | .frame _ b _ => by have := depth_le_x86_64Depth b; simp only [Code.depth, Code.x86_64Depth]; omega
  | .icall _ _ b n => by
    have := depth_le_x86_64Depth b; have := depth_le_x86_64Depth n
    simp only [Code.depth, Code.x86_64Depth]; omega

theorem pushBytes_eq (i : Instr) : pushBytes i = i.frameBytes := by
  cases i <;> rfl

/-! ## The slots along a run -/

/-- The slots, `off` bytes above `E` each, are within `D` bytes of stack of
the end of the address space: what `c` writes below `E` misses them. -/
def SlotsFit (slots : List (Int × String)) (D : Nat) : Prop :=
  ∀ p ∈ slots, 0 ≤ p.1 ∧ D + p.1.toNat + 8 ≤ 2 ^ 64

/-- `d` bytes below the entry's stack pointer `E`, the slots hold their
functions' addresses. -/
def SlotInv (slots : List (Int × String)) (E : Addr) (d : Nat) (s : State) : Prop :=
  s.gpr .rsp = E - BitVec.ofNat 64 d ∧ SlotsOk slots E s

theorem slot_addr {off : Int} (h : 0 ≤ off) (E : Addr) :
    E + BitVec.ofInt 64 off = E + BitVec.ofNat 64 off.toNat := by
  congr 1
  rw [show off = ((off.toNat : Nat) : Int) from (Int.toNat_of_nonneg h).symm, BitVec.ofInt_natCast,
    Int.toNat_natCast]

/-- A slot misses the `k` bytes below `E - d`. -/
theorem slot_below {E : Addr} {off : Int} {d k : Nat} (h₀ : 0 ≤ off) (h : d + k + off.toNat + 8 ≤ 2 ^ 64) :
    (⟨E + BitVec.ofInt 64 off, 8⟩ : Region).Disjoint (below (E - BitVec.ofNat 64 d) k) := by
  rw [slot_addr h₀]
  have e : E - BitVec.ofNat 64 d - BitVec.ofNat 64 k = E - BitVec.ofNat 64 (d + k) := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add, Nat.add_comm]
  show Region.Disjoint _ ⟨E - BitVec.ofNat 64 d - BitVec.ofNat 64 k, k⟩
  rw [e]
  exact (Offset.disjoint_below E (n := d + k) (d := off.toNat) (k := 8) (by omega)).sub_right
    (Region.sub_prefix (by omega))

/-- The slots keep their words where memory changes only within `s`'s
writable regions and below its stack pointer, and the regions do not change. -/
theorem SlotsOk.of_frame {slots : List (Int × String)} {E : Addr} {d k D : Nat} {s s' : State}
    (hs : SlotsOk slots E s) (hfit : SlotsFit slots D) (hdk : d + k ≤ D) (hsp : s.gpr .rsp = E - BitVec.ofNat 64 d)
    (hf : Frame (s.wr ++ [below (s.gpr .rsp) k]) s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hy : s'.syms = s.syms) :
    SlotsOk slots E s' := by
  intro p hp
  obtain ⟨hl, hd⟩ := hs p hp
  obtain ⟨h₀, hD⟩ := hfit p hp
  refine ⟨?_, by rw [hwr]; exact hd⟩
  have hr : s'.mem.readW (E + BitVec.ofInt 64 p.1) 64 = s.mem.readW (E + BitVec.ofInt 64 p.1) 64 :=
    hf.readW (r := ⟨E + BitVec.ofInt 64 p.1, 8⟩) (Region.contains_self _ _) (fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact hd r hr
      · simp only [List.mem_singleton] at hr; subst hr; rw [hsp]
        exact slot_below h₀ (by omega)) (by decide)
  simp only [State.load64, hrd, hwr] at hl ⊢
  rw [hr, hy]; exact hl

/-- **The slots along a run**: code that writes `rsp` only in its frames
keeps the stack pointer, and the slots, which it may not write. -/
theorem SlotInv.exec {slots : List (Int × String)} {E : Addr} {d D : Nat} {c : Prog isa}
    {s s' : State} {t : List Leak} (e : Exec isa c s t s') (hn : NoSp c) (hsp : SpSafe c)
    (hfit : SlotsFit slots D) (hdD : d + c.x86_64Depth ≤ D) (hD : D + 16 ≤ 2 ^ 64)
    (h : SlotInv slots E d s) : SlotInv slots E d s' := by
  have hk := depth_le_x86_64Depth c
  obtain ⟨hrd, hwr⟩ := Exec.rdwr e
  refine ⟨by rw [Exec.rsp hsp e]; exact h.1, ?_⟩
  exact h.2.of_frame hfit (k := 8 * c.depth) (by omega) h.1 (Exec.frameSp e hn (by omega)) hrd hwr (Exec.syms e)

/-! ## The pieces of code -/

theorem NoSp.seq₁ {a b : Prog isa} (h : NoSp (.seq a b)) : NoSp a := fun i hi => h i (List.mem_append_left _ hi)
theorem NoSp.seq₂ {a b : Prog isa} (h : NoSp (.seq a b)) : NoSp b := fun i hi => h i (List.mem_append_right _ hi)
theorem NoSp.ite₁ {cd : Cond} {a b : Prog isa} (h : NoSp (.ite cd a b)) : NoSp a :=
  fun i hi => h i (List.mem_append_left _ hi)
theorem NoSp.ite₂ {cd : Cond} {a b : Prog isa} (h : NoSp (.ite cd a b)) : NoSp b :=
  fun i hi => h i (List.mem_append_right _ hi)
theorem NoSp.frame {i j : Instr} {b : Prog isa} (h : NoSp (.frame i b j)) : NoSp b :=
  fun i' hi => h i' (by simp [instrs, hi])
theorem SpSafe.seq₁ {a b : Prog isa} (h : SpSafe (.seq a b)) : SpSafe a := fun i hi => h i (List.mem_append_left _ hi)
theorem SpSafe.seq₂ {a b : Prog isa} (h : SpSafe (.seq a b)) : SpSafe b := fun i hi => h i (List.mem_append_right _ hi)
theorem SpSafe.ite₁ {cd : Cond} {a b : Prog isa} (h : SpSafe (.ite cd a b)) : SpSafe a :=
  fun i hi => h i (List.mem_append_left _ hi)
theorem SpSafe.ite₂ {cd : Cond} {a b : Prog isa} (h : SpSafe (.ite cd a b)) : SpSafe b :=
  fun i hi => h i (List.mem_append_right _ hi)
theorem SpSafe.frame {i j : Instr} {b : Prog isa} (h : SpSafe (.frame i b j)) : SpSafe b :=
  fun i' hi => h i' (by simp [instrs, hi])

/-- The slots after a frame's push, `fb` bytes deeper. -/
theorem SlotInv.push {slots : List (Int × String)} {E : Addr} {d D : Nat} {i : Instr} {s s₁ : State}
    (hp : isa.push i s = some s₁) (hfit : SlotsFit slots D) (hdD : d + i.frameBytes ≤ D)
    (h : SlotInv slots E d s) : SlotInv slots E (d + pushBytes i) s₁ := by
  obtain ⟨hsp₁, hwr₁, -, hf⟩ := push_frame hp
  obtain ⟨-, hrd₁, -, -, -⟩ := push_eq hp
  rw [pushBytes_eq]
  refine ⟨by rw [hsp₁, h.1, BitVec.sub_sub, ← BitVec.ofNat_add], fun p hp' => ?_⟩
  obtain ⟨hl, hd⟩ := h.2 p hp'
  obtain ⟨h₀, hD⟩ := hfit p hp'
  have hdis : (⟨E + BitVec.ofInt 64 p.1, 8⟩ : Region).Disjoint (below (s.gpr .rsp) i.frameBytes) := by
    rw [h.1]; exact slot_below h₀ (by omega)
  refine ⟨?_, fun r hr => ?_⟩
  · have hr : s₁.mem.readW (E + BitVec.ofInt 64 p.1) 64 = s.mem.readW (E + BitVec.ofInt 64 p.1) 64 :=
      hf.readW (r := ⟨E + BitVec.ofInt 64 p.1, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hdis) (by decide)
    simp only [State.load64] at hl ⊢
    split at hl
    · rename_i hin
      rw [ite_eq_left (by
        obtain ⟨q, hq, hc⟩ := hin
        refine ⟨q, ?_, hc⟩
        rw [hrd₁, hwr₁]
        rcases List.mem_append.mp hq with hq | hq
        · exact List.mem_append_left _ hq
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ hq)), hr, push_syms hp]
      exact hl
    · cases hl
  · rw [hwr₁] at hr
    rcases List.mem_cons.mp hr with rfl | hr
    · rw [hsp₁]; exact hdis
    · exact hd r hr

/-- The slot `off` of `n` is in `slots`. -/
theorem slotOff_mem {slots : List (Int × String)} {n : String} {off : Int} (h : slotOff slots n = some off) :
    (off, n) ∈ slots := by
  unfold slotOff at h
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
  have hm := List.mem_of_find?_eq_some hp
  have hn := List.find?_some hp
  simp only [beq_iff_eq] at hn
  rw [← hn]; exact hm

/-- The call through the slot of `n` reads `n`'s address. -/
theorem slot_icall {slots : List (Int × String)} {E : Addr} {d : Nat} {n : String} {off : Int} {s : State}
    (h : SlotInv slots E d s) (ho : slotOff slots n = some off) :
    isa.icall (.callm { base := .rsp, disp := off + d }) s = some (isa.fnAddr s n) ∧
      s.ea { base := .rsp, disp := off + d } = E + BitVec.ofInt 64 off := by
  have hea : s.ea { base := .rsp, disp := off + d } = E + BitVec.ofInt 64 off := by
    simp only [State.ea, h.1, BitVec.ofInt_add, BitVec.ofInt_natCast]
    rw [BitVec.add_comm (BitVec.ofInt 64 off), ← BitVec.add_assoc, BitVec.sub_add_cancel]
  refine ⟨?_, hea⟩
  show s.load64 (s.ea _) = some (s.syms n)
  rw [hea]
  exact (h.2 _ (slotOff_mem ho)).1

/-! ## Runs of the code are runs of the code made so -/

/-- **A run of `c` is a run of `c` made to call through the slots**, from and
to the same states. -/
theorem Exec.toSlots {slots : List (Int × String)} {E : Addr} {D : Nat} (hfit : SlotsFit slots D)
    (hD : D + 16 ≤ 2 ^ 64) {c : Prog isa} {s s' : State} {t : List Leak} (e : Exec isa c s t s') :
    ∀ {d : Nat}, NoSp c → SpSafe c → d + c.x86_64Depth ≤ D → SlotInv slots E d s →
      ∃ t', Exec isa (Code.viaSlots slots d c) s t' s' := by
  induction e with
  | block h => intro _ _ _ _ _; exact ⟨_, Exec.block h⟩
  | @seq a b _ _ _ _ _ e₁ _ ih₁ ih₂ =>
    intro d hn hsp hdD hi
    simp only [Code.x86_64Depth] at hdD
    obtain ⟨_, e₁'⟩ := ih₁ hn.seq₁ hsp.seq₁ (by omega) hi
    obtain ⟨_, e₂'⟩ := ih₂ hn.seq₂ hsp.seq₂ (by omega)
      (SlotInv.exec e₁ hn.seq₁ hsp.seq₁ hfit (by omega) hD hi)
    exact ⟨_, Exec.seq e₁' e₂'⟩
  | iteT hc _ ih =>
    intro d hn hsp hdD hi
    simp only [Code.x86_64Depth] at hdD
    obtain ⟨_, e'⟩ := ih hn.ite₁ hsp.ite₁ (by omega) hi
    exact ⟨_, Exec.iteT hc e'⟩
  | iteF hc _ ih =>
    intro d hn hsp hdD hi
    simp only [Code.x86_64Depth] at hdD
    obtain ⟨_, e'⟩ := ih hn.ite₂ hsp.ite₂ (by omega) hi
    exact ⟨_, Exec.iteF hc e'⟩
  | loopExit _ hc ih =>
    intro d hn hsp hdD hi
    obtain ⟨_, e'⟩ := ih hn hsp hdD hi
    exact ⟨_, Exec.loopExit e' hc⟩
  | loopNext e₁ hc _ ih₁ ih₂ =>
    intro d hn hsp hdD hi
    obtain ⟨_, e₁'⟩ := ih₁ hn hsp hdD hi
    obtain ⟨_, e₂'⟩ := ih₂ hn hsp hdD (SlotInv.exec e₁ hn hsp hfit hdD hD hi)
    exact ⟨_, Exec.loopNext e₁' hc e₂'⟩
  | @call m b _ _ _ _ _ hc eb hr _ =>
    intro d _ _ _ hi
    cases ho : slotOff slots m with
    | none => exact ⟨_, by simp only [Code.viaSlots, ho]; exact Exec.call hc eb hr⟩
    | some off =>
      obtain ⟨hic, -⟩ := slot_icall hi ho
      exact ⟨_, by simp only [Code.viaSlots, ho, slotCall, Code.icalls]; exact Exec.icall hic hc eb hr⟩
  | @frame i j b _ _ _ _ _ hp _ hq ih =>
    intro d hn hsp hdD hi
    simp only [Code.x86_64Depth] at hdD
    obtain ⟨_, e'⟩ := ih hn.frame hsp.frame (by rw [pushBytes_eq]; omega) (hi.push hp hfit (by omega))
    exact ⟨_, Exec.frame hp e' hq⟩
  | icall h₁ h₂ e h₃ _ => intro _ _ _ _ _; exact ⟨_, Exec.icall h₁ h₂ e h₃⟩
  | icallNext h₁ h₂ e _ => intro _ _ _ _ _; exact ⟨_, Exec.icallNext h₁ h₂ e⟩

/-! ## Where a run's leaks end -/

/-- Whether code makes no indirect call. -/
def Code.icallFree : Prog isa → Bool
  | .block _ => true
  | .seq a b => icallFree a && icallFree b
  | .ite _ a b => icallFree a && icallFree b
  | .loop b _ => icallFree b
  | .call _ b => icallFree b
  | .frame _ b _ => icallFree b
  | .icall .. => false

theorem execBlock_length₂ {is : List Instr} {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak}
    (h₁ : execBlock isa is s₁ = some (s₁', t₁)) (h₂ : execBlock isa is s₂ = some (s₂', t₂)) :
    t₁.length = t₂.length := by
  rw [execBlock_length h₁, execBlock_length h₂]

theorem append3_inj {a₁ a₂ b₁ b₂ c₁ c₂ u₁ u₂ : List Leak} (ha : a₁.length = a₂.length)
    (hb : ∀ {v₁ v₂ : List Leak}, b₁ ++ v₁ = b₂ ++ v₂ → b₁ = b₂) (hc : c₁.length = c₂.length)
    (h : a₁ ++ b₁ ++ c₁ ++ u₁ = a₂ ++ b₂ ++ c₂ ++ u₂) : a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂ ∧ u₁ = u₂ := by
  simp only [List.append_assoc] at h
  obtain ⟨rfl, h⟩ := List.append_inj h ha
  have h := List.append_cancel_left h
  have hB := hb h
  subst hB
  obtain ⟨rfl, rfl⟩ := List.append_inj (List.append_cancel_left h) hc
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem append3_inj' {a₁ a₂ b₁ b₂ c₁ c₂ : List Leak} (ha : a₁.length = a₂.length)
    (hb : ∀ {v₁ v₂ : List Leak}, b₁ ++ v₁ = b₂ ++ v₂ → b₁ = b₂) (hc : c₁.length = c₂.length)
    (h : a₁ ++ b₁ ++ c₁ = a₂ ++ b₂ ++ c₂) : a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂ :=
  let ⟨h1, h2, h3, _⟩ := append3_inj (u₁ := []) (u₂ := []) ha hb hc (by rw [List.append_nil, List.append_nil]; exact h)
  ⟨h1, h2, h3⟩

/-- **What a run of code without indirect calls leaks tells where it ends**:
of two runs, whose leaks followed by others are the same, the two leak the
same. -/
theorem Exec.prefix {c : Prog isa} (hc : Code.icallFree c = true) {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak}
    (e₁ : Exec isa c s₁ t₁ s₁') (e₂ : Exec isa c s₂ t₂ s₂') {u₁ u₂ : List Leak} (h : t₁ ++ u₁ = t₂ ++ u₂) :
    t₁ = t₂ := by
  induction e₁ generalizing s₂ s₂' t₂ u₁ u₂ with
  | block h₁ =>
    cases e₂ with
    | block h₂ => exact (List.append_inj h (execBlock_length₂ h₁ h₂)).1
  | seq _ _ ih₁ ih₂ =>
    simp only [Code.icallFree, Bool.and_eq_true] at hc
    cases e₂ with
    | seq f₁ f₂ =>
      rw [List.append_assoc, List.append_assoc] at h
      have ha := ih₁ hc.1 f₁ h
      rw [ha] at h
      rw [ha, ih₂ hc.2 f₂ (List.append_cancel_left h)]
  | iteT _ _ ih =>
    simp only [Code.icallFree, Bool.and_eq_true] at hc
    cases e₂ with
    | iteT _ f => simp only [List.cons_append, List.cons.injEq, true_and] at h; rw [ih hc.1 f h]
    | iteF _ _ => simp only [List.cons_append, List.cons.injEq, Leak.branch.injEq] at h; exact absurd h.1 (by decide)
  | iteF _ _ ih =>
    simp only [Code.icallFree, Bool.and_eq_true] at hc
    cases e₂ with
    | iteT _ _ => simp only [List.cons_append, List.cons.injEq, Leak.branch.injEq] at h; exact absurd h.1 (by decide)
    | iteF _ f => simp only [List.cons_append, List.cons.injEq, true_and] at h; rw [ih hc.2 f h]
  | loopExit _ _ ih =>
    simp only [Code.icallFree] at hc
    cases e₂ with
    | loopExit f _ =>
      simp only [List.append_assoc, List.singleton_append] at h
      rw [ih hc f h]
    | loopNext f _ _ =>
      simp only [List.append_assoc, List.cons_append] at h
      have hb := ih hc f h
      rw [hb] at h
      simp only [List.append_cancel_left_eq, List.cons.injEq, Leak.branch.injEq] at h
      exact absurd h.1 (by decide)
  | loopNext _ _ _ ih₁ ih₂ =>
    have hc' := hc
    simp only [Code.icallFree] at hc
    cases e₂ with
    | loopExit f _ =>
      simp only [List.append_assoc, List.cons_append] at h
      have hb := ih₁ hc f h
      rw [hb] at h
      simp only [List.append_cancel_left_eq, List.cons.injEq, Leak.branch.injEq] at h
      exact absurd h.1 (by decide)
    | loopNext f _ f' =>
      simp only [List.append_assoc, List.cons_append] at h
      have hb := ih₁ hc f h
      rw [hb] at h
      simp only [List.append_cancel_left_eq, List.cons.injEq, true_and] at h
      rw [hb, ih₂ hc' f' h]
  | call _ _ _ ih =>
    simp only [Code.icallFree] at hc
    cases e₂ with
    | call _ f _ =>
      obtain ⟨h1, h2, h3, -⟩ := append3_inj (by simp) (fun hv => ih hc f hv) (by simp) h
      rw [h1, h2, h3]
  | frame _ _ _ ih =>
    simp only [Code.icallFree] at hc
    cases e₂ with
    | frame _ f _ =>
      obtain ⟨h1, h2, h3, -⟩ := append3_inj (by simp only [List.length_map]; exact addrs_length _ _ _)
        (fun hv => ih hc f hv) (by simp only [List.length_map]; exact addrs_length _ _ _) h
      rw [h1, h2, h3]
  | icall => simp only [Code.icallFree, Bool.false_eq_true] at hc
  | icallNext => simp only [Code.icallFree, Bool.false_eq_true] at hc

/-! ## Runs of the code made so are runs of the code -/

/-- A run of the call through a slot: the call, its address leaked first. -/
theorem Exec.slotCall_inv {disp : Int} {n : String} {b : Prog isa} {s s' : State} {t : List Leak}
    (e : Exec isa (slotCall disp n b) s t s') :
    ∃ s₁ s₂ tb, isa.call s = some s₁ ∧ Exec isa b s₁ tb s₂ ∧ isa.ret s₁ s₂ = some s' ∧
      t = .addr (s.ea { base := .rsp, disp := disp }) :: .addr (isa.fnAddr s n) ::
        ((isa.callAddrs s).map .addr ++ tb ++ (isa.retAddrs s₂).map .addr) := by
  change Exec isa (.icall (.callm { base := .rsp, disp := disp }) n b (.block [])) s t s' at e
  cases e with
  | icall _ hc fb hr => exact ⟨_, _, _, hc, fb, hr, rfl⟩

/-- **A run of `c` made to call through the slots is a run of `c`**, from and
to the same states. -/
theorem Exec.ofSlots₁ {slots : List (Int × String)} {E : Addr} {D : Nat} (hfit : SlotsFit slots D)
    (hD : D + 16 ≤ 2 ^ 64) : ∀ (c : Prog isa) (d : Nat), Code.icallFree c = true → NoSp c → SpSafe c →
    d + c.x86_64Depth ≤ D → ∀ {s s' : State} {t' : List Leak},
    Exec isa (Code.viaSlots slots d c) s t' s' → SlotInv slots E d s → ∃ t, Exec isa c s t s'
  | .block is, _, _, _, _, _, _, _, _, e, _ => ⟨_, e⟩
  | .seq a b, d, hc, hn, hsp, hdD, _, _, _, e, hd => by
    simp only [Code.icallFree, Bool.and_eq_true] at hc
    simp only [Code.x86_64Depth] at hdD
    cases e with
    | seq e₁ e₂ =>
      obtain ⟨_, o₁⟩ := Exec.ofSlots₁ hfit hD a d hc.1 hn.seq₁ hsp.seq₁ (by omega) e₁ hd
      obtain ⟨_, o₂⟩ := Exec.ofSlots₁ hfit hD b d hc.2 hn.seq₂ hsp.seq₂ (by omega) e₂
        (SlotInv.exec o₁ hn.seq₁ hsp.seq₁ hfit (by omega) hD hd)
      exact ⟨_, Exec.seq o₁ o₂⟩
  | .ite cd a b, d, hc, hn, hsp, hdD, _, _, _, e, hd => by
    simp only [Code.icallFree, Bool.and_eq_true] at hc
    simp only [Code.x86_64Depth] at hdD
    cases e with
    | iteT h e =>
      obtain ⟨_, o⟩ := Exec.ofSlots₁ hfit hD a d hc.1 hn.ite₁ hsp.ite₁ (by omega) e hd
      exact ⟨_, Exec.iteT h o⟩
    | iteF h e =>
      obtain ⟨_, o⟩ := Exec.ofSlots₁ hfit hD b d hc.2 hn.ite₂ hsp.ite₂ (by omega) e hd
      exact ⟨_, Exec.iteF h o⟩
  | .loop b cd, d, hc, hn, hsp, hdD, s, s', t', e, hd => by
    simp only [Code.icallFree] at hc
    have hdD' : d + b.x86_64Depth ≤ D := hdD
    have hn' : NoSp b := hn
    have hsp' : SpSafe b := hsp
    change Exec isa (.loop (Code.viaSlots slots d b) cd) s t' s' at e
    have ihb := fun {s s' : State} {t' : List Leak} (e : Exec isa (Code.viaSlots slots d b) s t' s')
      (hd : SlotInv slots E d s) => Exec.ofSlots₁ hfit hD b d hc hn' hsp' hdD' e hd
    generalize hL : (Code.loop (Code.viaSlots slots d b) cd : Prog isa) = L at e
    induction e with
    | loopExit f h =>
      cases hL
      obtain ⟨_, o⟩ := ihb f hd
      exact ⟨_, Exec.loopExit o h⟩
    | loopNext f h _ _ ihr =>
      cases hL
      obtain ⟨_, o⟩ := ihb f hd
      obtain ⟨_, r⟩ := ihr (SlotInv.exec o hn' hsp' hfit hdD' hD hd) rfl
      exact ⟨_, Exec.loopNext o h r⟩
    | _ => cases hL
  | .call m b, d, _, _, _, _, s, s', t', e, hd => by
    cases ho : slotOff slots m with
    | none =>
      have e' : Exec isa (.call m b) s t' s' := by simp only [Code.viaSlots, ho] at e; exact e
      exact ⟨_, e'⟩
    | some off =>
      have e' : Exec isa (slotCall (off + d) m b) s t' s' := by simp only [Code.viaSlots, ho] at e; exact e
      obtain ⟨_, _, _, hcall, fb, hr, -⟩ := Exec.slotCall_inv e'
      exact ⟨_, Exec.call hcall fb hr⟩
  | .frame i b j, d, hc, hn, hsp, hdD, _, _, _, e, hd => by
    simp only [Code.icallFree] at hc
    simp only [Code.x86_64Depth] at hdD
    cases e with
    | frame hp fb hq =>
      obtain ⟨_, o⟩ := Exec.ofSlots₁ hfit hD b (d + pushBytes i) hc hn.frame hsp.frame
        (by rw [pushBytes_eq]; omega) fb (hd.push hp hfit (by omega))
      exact ⟨_, Exec.frame hp o hq⟩
  | .icall .., _, hc, _, _, _, _, _, _, _, _ => by simp only [Code.icallFree, Bool.false_eq_true] at hc

theorem Exec.ofSlots_det {slots : List (Int × String)} {E : Addr} {D : Nat} (hfit : SlotsFit slots D)
    (hD : D + 16 ≤ 2 ^ 64) {c : Prog isa} {d : Nat} (hc : Code.icallFree c = true) (hn : NoSp c)
    (hsp : SpSafe c) (hdD : d + c.x86_64Depth ≤ D) {s s' s'' : State} {t' t : List Leak}
    (e : Exec isa (Code.viaSlots slots d c) s t' s') (o : Exec isa c s t s'') (hd : SlotInv slots E d s) :
    s'' = s' := by
  obtain ⟨_, x⟩ := Exec.ofSlots₁ hfit hD c d hc hn hsp hdD e hd
  exact (Exec.det o x).2

/-! ## Two runs leak the same if the runs of the code do -/

/-- Two states agree on the addresses of the slots' functions. -/
def SymsAgree (slots : List (Int × String)) (a b : State) : Prop := ∀ p ∈ slots, a.syms p.2 = b.syms p.2

theorem SymsAgree.of {slots : List (Int × String)} {a b a' b' : State} (h : SymsAgree slots a b)
    (ha : a'.syms = a.syms) (hb : b'.syms = b.syms) : SymsAgree slots a' b' := fun p hp => by
  rw [ha, hb]; exact h p hp

/-- **Two runs of `c` made to call through the slots leak the same if the
runs of `c` do**: each leaks what that run of `c` does, with the slot's
address and the callee's at each call made so, which the two agree on. -/
theorem Exec.ofSlots₂ {slots : List (Int × String)} {E : Addr} {D : Nat} (hfit : SlotsFit slots D)
    (hD : D + 16 ≤ 2 ^ 64) : ∀ (c : Prog isa) (d : Nat), Code.icallFree c = true → NoSp c → SpSafe c →
    d + c.x86_64Depth ≤ D → ∀ {s₁ s₂ s₁' s₂' : State} {t₁' t₂' t₁ t₂ : List Leak},
    Exec isa (Code.viaSlots slots d c) s₁ t₁' s₁' → Exec isa (Code.viaSlots slots d c) s₂ t₂' s₂' →
    SlotInv slots E d s₁ → SlotInv slots E d s₂ → SymsAgree slots s₁ s₂ →
    Exec isa c s₁ t₁ s₁' → Exec isa c s₂ t₂ s₂' → t₁ = t₂ → t₁' = t₂'
  | .block is, _, _, _, _, _, _, _, _, _, _, _, _, _, e₁, e₂, _, _, _, o₁, o₂, h => by
    rw [(Exec.det e₁ o₁).1, (Exec.det e₂ o₂).1]; exact h
  | .seq a b, d, hc, hn, hsp, hdD, _, _, _, _, _, _, _, _, e₁, e₂, hd₁, hd₂, hy, o₁, o₂, h => by
    simp only [Code.icallFree, Bool.and_eq_true] at hc
    simp only [Code.x86_64Depth] at hdD
    cases e₁ with
    | seq f₁ g₁ =>
    cases e₂ with
    | seq f₂ g₂ =>
    cases o₁ with
    | seq p₁ q₁ =>
    cases o₂ with
    | seq p₂ q₂ =>
    obtain rfl := Exec.ofSlots_det hfit hD hc.1 hn.seq₁ hsp.seq₁ (by omega) f₁ p₁ hd₁
    obtain rfl := Exec.ofSlots_det hfit hD hc.1 hn.seq₁ hsp.seq₁ (by omega) f₂ p₂ hd₂
    have hA := Exec.prefix hc.1 p₁ p₂ h
    rw [hA] at h
    have hB := List.append_cancel_left h
    rw [Exec.ofSlots₂ hfit hD a d hc.1 hn.seq₁ hsp.seq₁ (by omega) f₁ f₂ hd₁ hd₂ hy p₁ p₂ hA,
      Exec.ofSlots₂ hfit hD b d hc.2 hn.seq₂ hsp.seq₂ (by omega) g₁ g₂
        (SlotInv.exec p₁ hn.seq₁ hsp.seq₁ hfit (by omega) hD hd₁)
        (SlotInv.exec p₂ hn.seq₁ hsp.seq₁ hfit (by omega) hD hd₂)
        (hy.of (Exec.syms p₁) (Exec.syms p₂)) q₁ q₂ hB]
  | .ite cd a b, d, hc, hn, hsp, hdD, _, _, _, _, _, _, _, _, e₁, e₂, hd₁, hd₂, hy, o₁, o₂, h => by
    simp only [Code.icallFree, Bool.and_eq_true] at hc
    simp only [Code.x86_64Depth] at hdD
    cases e₁ with
    | iteT c₁ f₁ =>
      cases o₁ with
      | iteF c₁' _ => rw [c₁] at c₁'; cases c₁'
      | iteT _ p₁ =>
        cases e₂ with
        | iteF c₂ _ =>
          cases o₂ with
          | iteT c₂' _ => rw [c₂] at c₂'; cases c₂'
          | iteF _ _ => simp only [List.cons.injEq, Leak.branch.injEq] at h; exact absurd h.1 (by decide)
        | iteT c₂ f₂ =>
          cases o₂ with
          | iteF c₂' _ => rw [c₂] at c₂'; cases c₂'
          | iteT _ p₂ =>
            simp only [List.cons.injEq, true_and] at h ⊢
            exact Exec.ofSlots₂ hfit hD a d hc.1 hn.ite₁ hsp.ite₁ (by omega) f₁ f₂ hd₁ hd₂ hy p₁ p₂ h
    | iteF c₁ f₁ =>
      cases o₁ with
      | iteT c₁' _ => rw [c₁] at c₁'; cases c₁'
      | iteF _ p₁ =>
        cases e₂ with
        | iteT c₂ _ =>
          cases o₂ with
          | iteF c₂' _ => rw [c₂] at c₂'; cases c₂'
          | iteT _ _ => simp only [List.cons.injEq, Leak.branch.injEq] at h; exact absurd h.1 (by decide)
        | iteF c₂ f₂ =>
          cases o₂ with
          | iteT c₂' _ => rw [c₂] at c₂'; cases c₂'
          | iteF _ p₂ =>
            simp only [List.cons.injEq, true_and] at h ⊢
            exact Exec.ofSlots₂ hfit hD b d hc.2 hn.ite₂ hsp.ite₂ (by omega) f₁ f₂ hd₁ hd₂ hy p₁ p₂ h
  | .loop b cd, d, hc, hn, hsp, hdD, s₁, s₂, s₁', s₂', t₁', t₂', t₁, t₂, e₁, e₂, hd₁, hd₂, hy, o₁, o₂, h => by
    simp only [Code.icallFree] at hc
    have hdD' : d + b.x86_64Depth ≤ D := hdD
    have hn' : NoSp b := hn
    have hsp' : SpSafe b := hsp
    have ihb := fun {s₁ s₂ s₁' s₂' : State} {t₁' t₂' t₁ t₂ : List Leak}
      (e₁ : Exec isa (Code.viaSlots slots d b) s₁ t₁' s₁') (e₂ : Exec isa (Code.viaSlots slots d b) s₂ t₂' s₂')
      (hd₁ : SlotInv slots E d s₁) (hd₂ : SlotInv slots E d s₂) (hy : SymsAgree slots s₁ s₂)
      (o₁ : Exec isa b s₁ t₁ s₁') (o₂ : Exec isa b s₂ t₂ s₂') (h : t₁ = t₂) =>
      Exec.ofSlots₂ hfit hD b d hc hn' hsp' hdD' e₁ e₂ hd₁ hd₂ hy o₁ o₂ h
    change Exec isa (.loop (Code.viaSlots slots d b) cd) s₁ t₁' s₁' at e₁
    change Exec isa (.loop (Code.viaSlots slots d b) cd) s₂ t₂' s₂' at e₂
    generalize hL : (Code.loop (Code.viaSlots slots d b) cd : Prog isa) = L at e₁ e₂
    induction e₁ generalizing s₂ s₂' t₂' t₁ t₂ with
    | loopExit f₁ c₁ =>
      cases hL
      cases o₁ with
      | loopNext p₁ c₁' _ =>
        rw [Exec.ofSlots_det hfit hD hc hn' hsp' hdD' f₁ p₁ hd₁, c₁] at c₁'; cases c₁'
      | loopExit p₁ _ =>
        cases e₂ with
        | loopExit f₂ c₂ =>
          cases o₂ with
          | loopNext p₂ c₂' _ => rw [Exec.ofSlots_det hfit hD hc hn' hsp' hdD' f₂ p₂ hd₂, c₂] at c₂'; cases c₂'
          | loopExit p₂ _ =>
            have hb := Exec.prefix hc p₁ p₂ h
            rw [ihb f₁ f₂ hd₁ hd₂ hy p₁ p₂ hb]
        | loopNext f₂ c₂ _ =>
          cases o₂ with
          | loopExit p₂ c₂' => rw [Exec.ofSlots_det hfit hD hc hn' hsp' hdD' f₂ p₂ hd₂, c₂] at c₂'; cases c₂'
          | loopNext p₂ _ _ =>
            have hb := Exec.prefix hc p₁ p₂ h
            rw [hb, List.append_cancel_left_eq] at h
            simp at h
      | _ => skip
    | loopNext f₁ c₁ r₁ _ ihr =>
      cases hL
      cases o₁ with
      | loopExit p₁ c₁' =>
        rw [Exec.ofSlots_det hfit hD hc hn' hsp' hdD' f₁ p₁ hd₁, c₁] at c₁'; cases c₁'
      | loopNext p₁ _ q₁ =>
        obtain rfl := Exec.ofSlots_det hfit hD hc hn' hsp' hdD' f₁ p₁ hd₁
        cases e₂ with
        | loopExit f₂ c₂ =>
          cases o₂ with
          | loopNext p₂ c₂' _ => rw [Exec.ofSlots_det hfit hD hc hn' hsp' hdD' f₂ p₂ hd₂, c₂] at c₂'; cases c₂'
          | loopExit p₂ _ =>
            have hb := Exec.prefix hc p₁ p₂ h
            rw [hb, List.append_cancel_left_eq] at h
            simp at h
        | loopNext f₂ c₂ r₂ =>
          cases o₂ with
          | loopExit p₂ c₂' => rw [Exec.ofSlots_det hfit hD hc hn' hsp' hdD' f₂ p₂ hd₂, c₂] at c₂'; cases c₂'
          | loopNext p₂ _ q₂ =>
            obtain rfl := Exec.ofSlots_det hfit hD hc hn' hsp' hdD' f₂ p₂ hd₂
            have hb := Exec.prefix hc p₁ p₂ h
            rw [hb, List.append_cancel_left_eq, List.cons.injEq] at h
            rw [ihb f₁ f₂ hd₁ hd₂ hy p₁ p₂ hb,
              ihr _ _ _ _ _ (SlotInv.exec p₁ hn' hsp' hfit hdD' hD hd₁) (SlotInv.exec p₂ hn' hsp' hfit hdD' hD hd₂)
                (hy.of (Exec.syms p₁) (Exec.syms p₂)) q₁ q₂ h.2 rfl r₂]
    | _ => cases hL
  | .call m b, d, _, _, _, _, s₁, s₂, s₁', s₂', t₁', t₂', t₁, t₂, e₁, e₂, hd₁, hd₂, hy, o₁, o₂, h => by
    cases ho : slotOff slots m with
    | none =>
      have e₁' : Exec isa (.call m b) s₁ t₁' s₁' := by simp only [Code.viaSlots, ho] at e₁; exact e₁
      have e₂' : Exec isa (.call m b) s₂ t₂' s₂' := by simp only [Code.viaSlots, ho] at e₂; exact e₂
      rw [(Exec.det e₁' o₁).1, (Exec.det e₂' o₂).1]; exact h
    | some off =>
      have e₁' : Exec isa (slotCall (off + d) m b) s₁ t₁' s₁' := by simp only [Code.viaSlots, ho] at e₁; exact e₁
      have e₂' : Exec isa (slotCall (off + d) m b) s₂ t₂' s₂' := by simp only [Code.viaSlots, ho] at e₂; exact e₂
      obtain ⟨r₁, q₁, tb₁, hc₁, fb₁, hr₁, rfl⟩ := Exec.slotCall_inv e₁'
      obtain ⟨r₂, q₂, tb₂, hc₂, fb₂, hr₂, rfl⟩ := Exec.slotCall_inv e₂'
      have k₁ : t₁ = (isa.callAddrs s₁).map .addr ++ tb₁ ++ (isa.retAddrs q₁).map .addr :=
        (Exec.det o₁ (Exec.call hc₁ fb₁ hr₁)).1
      have k₂ : t₂ = (isa.callAddrs s₂).map .addr ++ tb₂ ++ (isa.retAddrs q₂).map .addr :=
        (Exec.det o₂ (Exec.call hc₂ fb₂ hr₂)).1
      have hm := slotOff_mem ho
      rw [(slot_icall hd₁ ho).2, (slot_icall hd₂ ho).2,
        show isa.fnAddr s₁ m = isa.fnAddr s₂ m from hy _ hm, ← k₁, ← k₂, h]
  | .frame i b j, d, hc, hn, hsp, hdD, s₁, s₂, s₁', s₂', t₁', t₂', t₁, t₂, e₁, e₂, hd₁, hd₂, hy, o₁, o₂, h => by
    simp only [Code.icallFree] at hc
    simp only [Code.x86_64Depth] at hdD
    cases e₁ with
    | frame hp₁ fb₁ hq₁ =>
    cases e₂ with
    | frame hp₂ fb₂ hq₂ =>
    cases o₁ with
    | frame hpo₁ p₁ hqo₁ =>
    cases o₂ with
    | frame hpo₂ p₂ hqo₂ =>
    rw [hp₁, Option.some.injEq] at hpo₁
    rw [hp₂, Option.some.injEq] at hpo₂
    subst hpo₁ hpo₂
    have hi₁ := hd₁.push hp₁ hfit (by omega)
    have hi₂ := hd₂.push hp₂ hfit (by omega)
    have hdb : d + pushBytes i + b.x86_64Depth ≤ D := by rw [pushBytes_eq]; omega
    obtain rfl := Exec.ofSlots_det hfit hD hc hn.frame hsp.frame hdb fb₁ p₁ hi₁
    obtain rfl := Exec.ofSlots_det hfit hD hc hn.frame hsp.frame hdb fb₂ p₂ hi₂
    obtain ⟨hA, hT, hR⟩ := append3_inj' (by simp only [List.length_map]; exact addrs_length _ _ _)
      (fun hv => Exec.prefix hc p₁ p₂ hv) (by simp only [List.length_map]; exact addrs_length _ _ _) h
    rw [hA, hR, Exec.ofSlots₂ hfit hD b (d + pushBytes i) hc hn.frame hsp.frame hdb fb₁ fb₂ hi₁ hi₂
      (hy.of (push_syms hp₁) (push_syms hp₂)) p₁ p₂ hT]
  | .icall .., _, hc, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    simp only [Code.icallFree, Bool.false_eq_true] at hc

end VG.X86_64
