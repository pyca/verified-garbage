module

public import VerifiedGarbage.Proof.Rsa.Arm.KcBody
public import VerifiedGarbage.Proof.Rsa.Arm.CvLoad
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Contract
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The checks of an RSA key on ARMv7: the arguments

Both functions take `n`, `n_len`, `e` and `e_len` in `r0`–`r3` and the
others on the stack: `nA` words of them, the working space at word `iS` (its
length in `u64`s after it), and the numbers `ins` (the word of each pointer,
its length after it, and its array). `FnPre nA iS ins s`: what their
contracts say of the arguments, in those terms; `FnBase σ s`: what every
step keeps of the initial state `σ` (the stack pointer, the regions, memory
outside the working space, and the registers saved in its header).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck
open VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm
open VG.Proof.Rsa.Arm.CrtValues (reg)

section
variable (nA iS : Nat) (ins : List (Nat × Nat))

/-- The working space. -/
abbrev rS (s : State) : Region := reg (stackArg s iS) ((stackArg s (iS + 1)).toNat * 8)
/-- The stack arguments. -/
abbrev rA (s : State) : Region := ⟨stackArgAddr s 0, 4 * nA⟩
/-- An input on the stack. -/
abbrev rIn (s : State) (i : Nat) : Region := reg (stackArg s i) (stackArg s (i + 1)).toNat

/-- The modulus' length. -/
abbrev fK (s : State) : Nat := (s.gpr .r1).toNat

/-- The working space and the modulus' length. -/
abbrev geo (s : State) : Geo := ⟨stackArg s iS, (stackArg s (iS + 1)).toNat * 8, fK s⟩

structure FnPre (s : State) : Prop where
  sp : s.sp.toNat + 4 * nA ≤ 2 ^ 32
  rdN : reg (s.gpr .r0) (s.gpr .r1).toNat ∈ s.rd
  rdE : reg (s.gpr .r2) (s.gpr .r3).toNat ∈ s.rd
  rdA : rA nA s ∈ s.rd
  rdIns : ∀ p ∈ ins, rIn s p.1 ∈ s.rd
  wr : s.wr = [rS iS s]
  nS : (reg (s.gpr .r0) (s.gpr .r1).toNat).Disjoint (rS iS s)
  eS : (reg (s.gpr .r2) (s.gpr .r3).toNat).Disjoint (rS iS s)
  insS : ∀ p ∈ ins, (rIn s p.1).Disjoint (rS iS s)
  sA : (rS iS s).Disjoint (rA nA s)
  fN : (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32
  fE : (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32
  fIns : ∀ p ∈ ins, (stackArg s p.1).toNat + (stackArg s (p.1 + 1)).toNat ≤ 2 ^ 32
  fS : (stackArg s iS).toNat + (stackArg s (iS + 1)).toNat * 8 ≤ 2 ^ 32
  valid : Spec.Rsa.lenValid (fK s)
  e1 : 1 ≤ (s.gpr .r3).toNat
  e2 : (s.gpr .r3).toNat ≤ fK s
  ins1 : ∀ p ∈ ins, 1 ≤ (stackArg s (p.1 + 1)).toNat ∧ (stackArg s (p.1 + 1)).toNat ≤ fK s
  scr : Spec.Rsa.scratchWords (fK s) ≤ (stackArg s (iS + 1)).toNat
  hS : iS + 1 < nA
  hA : 4 * nA ≤ 4096
  hIns : ∀ p ∈ ins, p.1 + 1 < nA ∧ p.2 < nArr ∧ p.2 ≠ aN ∧ p.2 ≠ aE

/-- The registers saved at bytes `20 + 4 i` of the header: `r4`–`r11`, `lr`,
and `e` and `e_len`. -/
def savedReg : Nat → Reg
  | 0 => .r4 | 1 => .r5 | 2 => .r6 | 3 => .r7 | 4 => .r8 | 5 => .r9 | 6 => .r10 | 7 => .r11 | 8 => .lr
  | 9 => .r2 | _ => .r3

/-- What every step keeps. -/
structure FnBase (σ s : State) : Prop where
  pre : FnPre nA iS ins σ
  sp : s.sp = σ.sp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  frame : Frame [rS iS σ] σ.mem s.mem
  saved : ∀ i < 11, slot s.mem (geo iS σ).B (20 + 4 * i) = (σ.gpr (savedReg i)).toNat

variable {nA iS ins}

theorem FnPre.kb {s : State} (h : FnPre nA iS ins s) : 64 ≤ fK s ∧ fK s ≤ 1024 := h.valid

theorem FnPre.w16 {s : State} (h : FnPre nA iS ins s) : 16 ≤ (geo iS s).w ∧ (geo iS s).w ≤ 256 := by
  have := h.valid; simp only [Spec.Rsa.lenValid] at this
  simp only [Geo.w]
  omega

/-- The working space is large enough for the arrays. -/
theorem FnPre.fits {s : State} (h : FnPre nA iS ins s) : arr (geo iS s).w nArr ≤ (geo iS s).Z := by
  have := h.valid; have := h.scr
  simp only [Spec.Rsa.lenValid, Spec.Rsa.scratchWords, fK] at *
  simp only [arr, S, hdr, nArr, Geo.w, fK]
  omega

theorem FnBase.of_rest {σ s t : State} (h : FnBase nA iS ins σ s) {ws : List Reg} (r : Rest ws s t)
    (m : t.mem = s.mem) : FnBase nA iS ins σ t :=
  ⟨h.pre, r.sp.trans h.sp, r.rd.trans h.rd, r.wr.trans h.wr, m ▸ h.frame, fun i hi => m ▸ h.saved i hi⟩

/-- Memory outside the working space, by the offset from its base. -/
theorem out_of_ofs {σ : State} {x : Addr} (hx : ¬ (rS iS σ).Contains x 1) :
    (geo iS σ).Z ≤ ofs (State.addr (geo iS σ).B) x := by
  simp only [Region.Contains] at hx
  simp only [ofs]
  omega

theorem FnBase.keep {σ s t : State} (h : FnBase nA iS ins σ s) {js ds : List Nat}
    (k : Keep (geo iS σ).B (geo iS σ).w js ds s.mem t.mem) (hjs : ∀ j ∈ js, j < nArr)
    (hds : ∀ d ∈ ds, d + 4 ≤ 20 ∨ 64 ≤ d) (hdh : ∀ d ∈ ds, d + 4 ≤ hdr)
    (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : FnBase nA iS ins σ t := by
  have fits := h.pre.fits
  refine ⟨h.pre, sp.trans h.sp, rd.trans h.rd, wr.trans h.wr, ?_, fun i hi => ?_⟩
  · refine h.frame.trans fun x hx => k.out (Z := (geo iS σ).Z) (fun j hj => ?_) (fun d hd => ?_)
      (out_of_ofs (by simpa using hx))
    · exact Nat.le_trans (arr_end (hjs j hj)) fits
    · exact Nat.le_trans (hdh d hd) (Nat.le_trans (Nat.le_add_right _ _) fits)
  · rw [k.slot (by simp only [hdr]; omega) (fun d hd => by rcases hds d hd with e | e <;> omega)]
    exact h.saved i hi

/-- A store outside the header's saved words. -/
theorem FnBase.outside {σ s t : State} (h : FnBase nA iS ins σ s) {o n : Nat}
    (hf : Outside (State.addr (geo iS σ).B) o n s.mem t.mem) (ho : o + n ≤ 20 ∨ 64 ≤ o)
    (hn : o + n ≤ (geo iS σ).Z) (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) :
    FnBase nA iS ins σ t := by
  have fS := h.pre.fS
  refine ⟨h.pre, sp.trans h.sp, rd.trans h.rd, wr.trans h.wr, h.frame.trans fun x hx => ?_, fun i hi => ?_⟩
  · exact hf x (.inr (Nat.le_trans hn (out_of_ofs (by simpa using hx))))
  · rw [← h.saved i hi]
    exact hf.w32 (d := 20 + 4 * i) (by omega) (by omega)

/-- A stack argument. -/
theorem FnBase.arg {σ s : State} (h : FnBase nA iS ins σ s) {i : Nat} (hi : i < nA) :
    stackArg s i = stackArg σ i := by
  have sp := h.pre.sp
  unfold stackArg
  have ea : stackArgAddr s i = stackArgAddr σ i := by simp only [stackArgAddr, h.sp]
  rw [ea]
  refine h.frame.readW (r := rA nA σ) ?_ (fun r hr => ?_) (by decide)
  · simp only [Region.Contains, stackArgAddr]
    rw [addr_add (by omega), addr_add (by omega), Nat.mul_zero, BitVec.add_zero, Offset.add_sub_cancel_left,
      BitVec.toNat_ofNat]
    omega
  · simp only [List.mem_singleton] at hr; subst hr; exact h.pre.sA.symm

theorem FnBase.rA_mem {σ s : State} (h : FnBase nA iS ins σ s) : rA nA s ∈ s.rd := by
  rw [h.rd]; simpa [rA, stackArgAddr, h.sp] using h.pre.rdA

/-- `ldr t, [sp, #4i]` of a stack argument. -/
theorem wp_ldrSpA {s : State} (hrd : rA nA s ∈ s.rd) (sp : s.sp.toNat + 4 * nA ≤ 2 ^ 32) {i : Nat}
    (hi : i < nA) (h4 : 4 * i < 4096) {t : Reg} {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' t (stackArg s i) → WP isa (.block rest) s' Q) :
    WP isa (.block (.ldrSp t (4 * i) :: rest)) s Q := by
  refine WP.cons (s' := s.setReg t (stackArg s i)) ?_ (k _ (Upd.setReg _ _ _))
  have hin : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 (4 * i))) 4 := by
    refine ⟨rA nA s, List.mem_append_left _ hrd, ?_⟩
    simp only [Region.Contains, stackArgAddr]
    rw [addr_add (by omega), addr_add (by omega), Nat.mul_zero, BitVec.add_zero,
      Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    omega
  simp only [exec, h4, ↓reduceIte, State.load32, hin, Option.map_some]
  rfl

theorem FnBase.ldrSp {σ s : State} (h : FnBase nA iS ins σ s) {i : Nat} (hi : i < nA) (h4 : 4 * i < 4096)
    {t : Reg} {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', FnBase nA iS ins σ s' → Upd s s' t (stackArg σ i) → WP isa (.block rest) s' Q) :
    WP isa (.block (.ldrSp t (4 * i) :: rest)) s Q :=
  wp_ldrSpA h.rA_mem (by rw [h.sp]; exact h.pre.sp) hi h4 fun s' u =>
    k s' (h.of_rest (u.rest (ws := [t]) (by simp)) u.mem) (by rw [← h.arg hi]; exact u)

end

end VG.Proof.Rsa.Arm.KeyCheck
