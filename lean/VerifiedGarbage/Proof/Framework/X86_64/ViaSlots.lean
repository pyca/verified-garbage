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

end VG.X86_64
