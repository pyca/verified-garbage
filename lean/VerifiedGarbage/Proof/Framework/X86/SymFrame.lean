import VerifiedGarbage.Proof.Framework.X86.Call

/-! # Obtaining a static address with a balanced four-byte CALL frame -/
namespace VG.X86
open VG

/-- The state after the symbol-address frame's push. -/
def symPushed (name : String) (s : State) : State :=
  let pc := s.unknowns 0
  let delta := s.syms name - pc
  let t := arithFlags s (s.syms name) (2^32 ≤ pc.toNat + delta.toNat)
    (addOverflow pc delta (s.syms name))
  { (t.setReg .esp (s.gpr .esp - 4)).setReg .eax (s.syms name) with
    mem := s.mem.writeW ((s.gpr .esp - 4).setWidth 64) (s.unknowns 0)
    unknowns := fun n => s.unknowns (n+1)
    wr := below (s.gpr .esp) 4 :: s.wr }

/-- The saved EIP is discarded into ECX, leaving the static address in EAX. -/
def symPopped (name : String) (s : State) : State :=
  { popReg (symPushed name s) .ecx 1 with wr := s.wr }

/-- The address result, preserved calling convention, and four-byte write. -/
structure SymAddrPost (name : String) (s t : State) : Prop where
  addr : t.gpr .eax = s.syms name
  gpr : ∀ r, r ∉ [.eax, .ecx] → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [below (s.gpr .esp) 4] s.mem t.mem
  syms : t.syms = s.syms

/-- The balanced frame preserves cdecl argument words above ESP. -/
theorem SymAddrPost.arg {name : String} {s t : State} (h : SymAddrPost name s t)
    {j : Nat} (h₁ : 4 ≤ (s.gpr .esp).toNat)
    (h₂ : (s.gpr .esp).toNat + 8 + 4 * j ≤ 2 ^ 32) : arg t j = arg s j := by
  have he := h.gpr .esp (by decide)
  simp only [VG.X86.arg, VG.X86.argAddr, he]
  change t.mem.readW ((s.gpr .esp + BitVec.ofNat 32 (4 + 4 * j)).setWidth 64) 32 = _
  refine Frame.readW (rs := [below (s.gpr .esp) 4]) (r := ⟨(s.gpr .esp).setWidth 64 +
    BitVec.ofNat 64 (4 + 4 * j), 4⟩) h.frame ?_ ?_ (by decide)
  · simp only [Region.Contains, Nat.reduceDiv]
    rw [show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * j)).setWidth 64 = _ from
      addr_eq (x := s.gpr .esp) (k := 4 + 4 * j) (by omega)]
    simp
  · simp only [List.mem_singleton]
    rintro r rfl x hx hx'
    simp only [Region.Contains] at hx hx'
    rw [Taint.sub_setWidth h₁] at hx'
    exact Offset.disjoint_below_above _ (m := 4) (a := 4 + 4 * j) (l := 4) (by omega) x hx' hx

/-- The return address above the CALL frame is untouched. -/
theorem SymAddrPost.ret {name : String} {s t : State} (h : SymAddrPost name s t)
    (h₁ : 4 ≤ (s.gpr .esp).toNat) (_h₂ : (s.gpr .esp).toNat + 4 ≤ 2 ^ 32) :
    t.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
  refine Frame.readW (rs := [below (s.gpr .esp) 4])
    (r := ⟨(s.gpr .esp).setWidth 64, 4⟩) h.frame (by simp [Region.Contains]) ?_ (by decide)
  simp only [List.mem_singleton]
  rintro r rfl x hx hx'
  simp only [Region.Contains] at hx hx'
  rw [Taint.sub_setWidth h₁] at hx'
  exact Offset.disjoint_below_above _ (m := 4) (a := 0) (l := 4) (by omega) x hx' (by
    change (x - ((s.gpr .esp).setWidth 64 + 0)).toNat + 1 ≤ 4
    have hz : (s.gpr .esp).setWidth 64 + (0 : BitVec 64) = (s.gpr .esp).setWidth 64 := BitVec.add_zero _
    rw [hz]; exact hx)

theorem symFrame_ok (name : String) (s : State) (hsp : 4 ≤ (s.gpr .esp).toNat) :
    WP isa (.frame (.symPush .eax name) (.block []) (.pop .ecx 1)) s (SymAddrPost name s) := by
  have hp : isa.push (.symPush .eax name) s = some (symPushed name s) := by
    simp [isa, push, symPushed, hsp, below]
  have hq : isa.pop (.pop .ecx 1) (symPushed name s) (symPushed name s) = some (symPopped name s) := by
    simp [isa, pop, symPushed, symPopped, State.setReg, arithFlags, below]
  refine ⟨_, _, Exec.frame hp (Exec.block rfl) hq, ?_, ?_, rfl, rfl, ?_, rfl⟩
  · simp [symPopped, popReg, symPushed, State.setReg, arithFlags]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    by_cases h : r = .esp
    · subst r; simp [symPopped, popReg, symPushed, State.setReg, State.setFlags, arithFlags, BitVec.sub_add_cancel]
    · simp [symPopped, popReg, symPushed, State.setReg, State.setFlags, arithFlags, hr.1, hr.2, h]
  · exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
      (below_top (Nat.le_refl 4) hsp (by decide))

/-- The balanced address prefix accesses only the word below public ESP. -/
theorem symFrame_trace {name : String} {s s' : State} {tr : List Leak}
    (hsp : 4 ≤ (s.gpr .esp).toNat)
    (he : Exec isa (.frame (.symPush .eax name) (.block []) (.pop .ecx 1)) s tr s') :
    tr = List.replicate 3 (.addr ((s.gpr .esp - 4).setWidth 64)) := by
  have hp : isa.push (.symPush .eax name) s = some (symPushed name s) := by
    simp [isa, push, symPushed, hsp, below]
  have hq : isa.pop (.pop .ecx 1) (symPushed name s) (symPushed name s) = some (symPopped name s) := by
    simp [isa, pop, symPushed, symPopped, State.setReg, arithFlags, below]
  have hc := Exec.frame hp (Exec.block (is := []) rfl) hq
  have ht := (Exec.det he hc).1
  simpa [isa, addrs, symPushed, State.setReg, arithFlags] using ht

end VG.X86
