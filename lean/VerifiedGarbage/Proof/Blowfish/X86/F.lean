module

public import VerifiedGarbage.Proof.Blowfish.X86.Lookup
import VerifiedGarbage.Proof.Blowfish.X86.Run
import VerifiedGarbage.Proof.Blowfish.Schedule

/-!
# Blowfish on x86 (32-bit): F

`f_run`: F of xL (at `ebp + 16`) into `ebp + 24`, one S-box at a time (`fAcc`).
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86

open VG VG.X86 VG.Impl.Blowfish.X86 VG.Spec.Blowfish VG.Proof.Blowfish
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

/-- What F needs besides a lookup's: F's slot writable, apart from the
schedule, xL's slot and the schedule's address on the stack. -/
structure FEnv (sch : Nat) (S : BitVec 32) (s : State) : Prop extends LookEnv sch S s where
  fw : InRegions s.wr (addr (s.gpr .ebp) fOff) 4
  fS : Region.Disjoint ⟨addr (s.gpr .ebp) fOff, 4⟩ ⟨S.setWidth 64, 4168⟩
  fX : Mem.Sep (addr (s.gpr .ebp) xlOff) 4 (addr (s.gpr .ebp) fOff) 4
  fA : Mem.Sep (addr (s.gpr .esp) sch) 4 (addr (s.gpr .ebp) fOff) 4

theorem FEnv.keep {sch : Nat} {S : BitVec 32} {s t : State} (E : FEnv sch S s) {rs : List Reg}
    (h : Keep rs s t) (hm : t.mem = s.mem) (hsp : Reg.esp ∉ rs) (hbp : Reg.ebp ∉ rs) : FEnv sch S t :=
  { E.toLookEnv.keep h hm hsp hbp with
    fw := by rw [h.2.2, h.gpr hbp]; exact E.fw
    fS := by rw [h.gpr hbp]; exact E.fS
    fX := by rw [h.gpr hbp]; exact E.fX
    fA := by rw [h.gpr hbp, h.gpr hsp]; exact E.fA }

theorem sep_symm {a b : Addr} {n k : Nat} (h : Mem.Sep a n b k) : Mem.Sep b k a n :=
  fun x h₁ h₂ => h x h₂ h₁

/-- `FEnv` after a write of F's slot. -/
theorem FEnv.write {sch : Nat} {S : BitVec 32} {s t : State} (E : FEnv sch S s) {rs : List Reg} {v : BitVec 32}
    (h : Keep rs s t) (hsp : Reg.esp ∉ rs) (hbp : Reg.ebp ∉ rs)
    (hm : t.mem = s.mem.writeW (addr (s.gpr .ebp) fOff) (v : BitVec 32)) : FEnv sch S t := by
  have r := keep_reads h
  have esp := h.gpr hsp
  have ebp := h.gpr hbp
  refine ⟨⟨?_, ?_, E.fit, fun o ho => ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [r, esp]; exact E.schRd
  · rw [hm, esp, Mem.readW_writeW_sep E.fA (by decide)]; exact E.schVal
  · rw [r]; exact E.rd o ho
  · rw [r, ebp]; exact E.xl
  · rw [h.2.2, ebp]; exact E.fw
  · rw [ebp]; exact E.fS
  · rw [ebp]; exact E.fX
  · rw [ebp, esp]; exact E.fA

theorem writeW_writeW32 (m : Mem) (a : Addr) (v v' : BitVec 32) :
    (m.writeW a v).writeW a v' = m.writeW a v' := by
  funext x
  simp only [Mem.writeW, Mem.write]
  split <;> rfl

/-- A write of F's slot leaves the schedule as it was. -/
theorem scheduleAt_writeF {S F : Addr} (h : Region.Disjoint ⟨F, 4⟩ ⟨S, 4168⟩) (m : Mem) (v : BitVec 32) :
    scheduleAt (m.writeW F v) S = scheduleAt m S :=
  scheduleAt_eq_of_frame S (rs := [⟨F, 4⟩])
    ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self F 4))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.symm)

theorem combine_run (u : State) {j : Nat} (hj : j < 4) (hw : InRegions u.wr (addr (u.gpr .ebp) fOff) 4) :
    WP isa (.block (combine j)) u fun t =>
      t.mem = u.mem.writeW (addr (u.gpr .ebp) fOff) (if j = 0 then u.gpr .edi
        else if j = 2 then u.mem.readW (addr (u.gpr .ebp) fOff) 32 ^^^ u.gpr .edi
        else u.mem.readW (addr (u.gpr .ebp) fOff) 32 + u.gpr .edi) := by
  have hr := region_in (rs := u.rd) hw
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    simp only [fOff] at hw hr ⊢ <;> brun [combine, hw, hr]

/-- S-box `j`'s lookup, then its accumulation into F's slot, which holds
`fAcc … (j - 1)` (or what it did, for `j = 0`). -/
theorem step_run {sch : Nat} {S : BitVec 32} {s₀ : State} (E : FEnv sch S s₀) {j : Nat} (hj : j < 4)
    {u : State} (k : Keep lookRegs s₀ u)
    (hm : u.mem = if j = 0 then s₀.mem else s₀.mem.writeW (addr (s₀.gpr .ebp) fOff)
      (fAcc (scheduleAt s₀.mem (S.setWidth 64)) (s₀.mem.readW (addr (s₀.gpr .ebp) xlOff) 32) (j - 1)))
    {Q : State → Prop}
    (hQ : ∀ t, Keep lookRegs s₀ t → t.mem = s₀.mem.writeW (addr (s₀.gpr .ebp) fOff)
      (fAcc (scheduleAt s₀.mem (S.setWidth 64)) (s₀.mem.readW (addr (s₀.gpr .ebp) xlOff) 32) j) → Q t) :
    WP isa (.seq (lookup sch j) (.block (combine j))) u Q := by
  have ebp : u.gpr .ebp = s₀.gpr .ebp := k.gpr (by decide)
  have Eu : FEnv sch S u := by
    by_cases h0 : j = 0
    · simp only [h0, ↓reduceIte] at hm; exact E.keep k hm (by decide) (by decide)
    · simp only [h0, ↓reduceIte] at hm; exact E.write k (by decide) (by decide) hm
  have hx : u.mem.readW (addr (u.gpr .ebp) xlOff) 32 = s₀.mem.readW (addr (s₀.gpr .ebp) xlOff) 32 := by
    rw [ebp, hm]; split
    · rfl
    · exact Mem.readW_writeW_sep E.fX (by decide)
  have hK : scheduleAt u.mem (S.setWidth 64) = scheduleAt s₀.mem (S.setWidth 64) := by
    rw [hm]; split
    · rfl
    · exact scheduleAt_writeF E.fS _ _
  apply WP.seq
  refine WP.mono (lookup_run Eu.toLookEnv hj hx) fun v ⟨v7, vk, vm⟩ => ?_
  have vbp : v.gpr .ebp = s₀.gpr .ebp := (vk.gpr (by decide)).trans ebp
  have hw : InRegions v.wr (addr (v.gpr .ebp) fOff) 4 := by rw [vk.2.2, vk.gpr (by decide)]; exact Eu.fw
  refine WP.mono (WP.keep [.ecx] (combine_run v hj hw) (by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> decide))
    fun t ⟨tm, tk⟩ => hQ t ((k.trans vk).trans tk |>.mono (by decide)) ?_
  rw [tm, vm, vbp, v7, hK]
  -- For any `j`, with `fAcc_step`: a case split on `j` would have the kernel
  -- compare `fAcc … (1 - 1)` with `fAcc … 0` by evaluating the S-boxes.
  have hprev : 0 < j → u.mem.readW (addr (s₀.gpr .ebp) fOff) 32 =
      fAcc (scheduleAt s₀.mem (S.setWidth 64)) (s₀.mem.readW (addr (s₀.gpr .ebp) xlOff) 32) (j - 1) :=
    fun h => by
      rw [hm]; split
      · omega
      · exact Mem.readW_writeW_self32 _ _ _
  have hmem : ∀ v, u.mem.writeW (addr (s₀.gpr .ebp) fOff) v = s₀.mem.writeW (addr (s₀.gpr .ebp) fOff) v :=
    fun v => by
      rw [hm]; split
      · rfl
      · exact writeW_writeW32 _ _ _ _
  rw [hmem]
  exact congrArg _ (fAcc_step _ _ hj _ hprev)

theorem f_run {sch : Nat} {S : BitVec 32} {s : State} (E : FEnv sch S s) :
    WP isa (Impl.Blowfish.X86.f sch) s fun t =>
      Keep lookRegs s t ∧ t.mem = s.mem.writeW (addr (s.gpr .ebp) fOff)
        (Spec.Blowfish.f (scheduleAt s.mem (S.setWidth 64)) (s.mem.readW (addr (s.gpr .ebp) xlOff) 32)) := by
  unfold Impl.Blowfish.X86.f
  apply WP.reassoc; apply WP.seq
  refine step_run E (j := 0) (by decide) (Keep.refl _ _) rfl fun t0 k0 m0 => ?_
  apply WP.reassoc; apply WP.seq
  refine step_run E (j := 1) (by decide) k0 m0 fun t1 k1 m1 => ?_
  apply WP.reassoc; apply WP.seq
  refine step_run E (j := 2) (by decide) k1 m1 fun t2 k2 m2 => ?_
  refine step_run E (j := 3) (by decide) k2 m2 fun t3 k3 m3 => ⟨k3, ?_⟩
  rw [m3, fAcc_three]

end VG.Proof.Blowfish.X86
