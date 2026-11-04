module
public import VerifiedGarbage.Impl.RsaPss.X86_64
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Core

import VerifiedGarbage.Proof.Framework.X86_64.CallFrame

/-!
# RSASSA-PSS on x86-64: no writes to `rsp`, no loads of MXCSR

Every instruction of `ctHash` (and of what it calls) neither writes `rsp`
(`SpSafe`) nor loads MXCSR (`ctHash_safe`), given that of every function its
calls through the tables' slots may reach (`MdFnsSafe`, `FnsSafe`), and how
much stack each piece uses (`ctHash_xd`, `mgfXor_xd`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

/-- Neither writes `rsp` nor loads MXCSR. -/
def safeI (i : Instr) : Bool := !isa.writesSp i && !loadsMxcsr i

theorem allInstrs_and (f g : Instr → Bool) (c : Prog isa) :
    c.allInstrs (fun i => f i && g i) = (c.allInstrs f && c.allInstrs g) := by
  simp only [Code.allInstrs_eq]
  induction instrs c with
  | nil => rfl
  | cons i is ih =>
    simp only [List.all_cons, ih]
    cases f i <;> cases g i <;> simp

theorem safeI_eq : safeI = fun i => !isa.writesSp i && !loadsMxcsr i := rfl

theorem safe_sp {c : Prog isa} (h : c.allInstrs safeI = true) : SpSafe c := by
  rw [Code.allInstrs_eq] at h
  intro i hi
  have := List.all_eq_true.mp h i hi
  simp only [safeI, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
  exact this.1

theorem safe_mx {c : Prog isa} (h : c.allInstrs safeI = true) : c.allInstrs (fun i => !loadsMxcsr i) = true := by
  rw [safeI_eq, allInstrs_and] at h
  simp only [Bool.and_eq_true] at h
  exact h.2

theorem rec_all (p : Instr → Bool) (l : List Instr) :
    List.rec (motive := fun _ => Bool) true (fun i _ ih => p i && ih) l = l.all p := by
  induction l with
  | nil => rfl
  | cons i is ih => simp only [List.all_cons, ← ih]

/-! ## The calls through the tables' slots -/

/-- Every function of `ts` is `safeI` and uses at most `d` bytes of stack. -/
def FSafe (ts : List (String × Prog isa)) (d : Nat) : Prop :=
  ∀ q ∈ ts, q.2.allInstrs safeI = true ∧ q.2.x86_64Depth ≤ d

theorem icalls_safe {d : Nat} : ∀ {ts : List (String × Prog isa)}, FSafe ts d →
    (Code.icalls (.callr .r11) ts).allInstrs safeI = true ∧ (Code.icalls (.callr .r11) ts).x86_64Depth ≤ d + 8
  | [], _ => ⟨rfl, Nat.zero_le _⟩
  | q :: ts, h => by
    have hq := h q (List.mem_cons_self ..)
    have ih := icalls_safe (ts := ts) fun r hr => h r (List.mem_cons_of_mem _ hr)
    refine ⟨?_, ?_⟩
    · simp only [Code.icalls, Code.allInstrs, hq.1, ih.1, Bool.and_true]; rfl
    · simp only [Code.icalls, Code.x86_64Depth, Nat.max_le]; omega

theorem scall_safe {d s : Nat} {ts : List (String × Prog isa)} (h : FSafe ts d) :
    (scall s ts).allInstrs safeI = true ∧ (scall s ts).x86_64Depth ≤ d + 8 := by
  have := icalls_safe h
  refine ⟨?_, ?_⟩
  · simp only [scall, Code.allInstrs, this.1, Bool.and_true]; rfl
  · simp only [scall, Code.x86_64Depth, Nat.max_le]; omega

/-- The functions the calls through the slots of the table of `MdHash` reach
use no stack. -/
structure MdFnsSafe (f : MdFns) : Prop where
  init : FSafe f.init 0
  comp : FSafe f.comp 0
  dig : FSafe f.dig 0

/-- And those through the slots of the table of `Hash` at most 8 bytes. -/
structure FnsSafe (g : Impl.Mgf1.X86_64.Table.Fns) : Prop where
  init : FSafe g.init 8
  upd : FSafe g.upd 8
  fin : FSafe g.fin 8

variable {H : Hash} (hH : HashOK H) {f : MdFns} (hf : MdFnsSafe f) {g : Impl.Mgf1.X86_64.Table.Fns}
  (hg : FnsSafe g)

include hH hf in
theorem ctHashWith_safe {padding : Prog isa} (hp : padding.allInstrs safeI = true) :
    (ctHashWith f H padding).allInstrs safeI = true := by
  have hl : H.P.len.all safeI = true := hH.taints.lenSafe
  simp only [ctHashWith, hp, seqs, ctInit, lenLoop, compLoop, select, Code.allInstrs, (scall_safe hf.init).1,
    (scall_safe hf.comp).1, (scall_safe hf.dig).1, rec_all, lenField, digestOut, digestAt, List.all_append, hl,
    byteLoop, step, Bool.and_true, Bool.true_and]
  rfl

include hH hf in
theorem ctHash_safe : (ctHash f H).allInstrs safeI = true := ctHashWith_safe hH hf rfl

include hf in
theorem ctHashWith_xd {padding : Prog isa} (hp : padding.x86_64Depth = 0) :
    (ctHashWith f H padding).x86_64Depth ≤ 8 := by
  have := (scall_safe (s := sIniH) hf.init).2
  have := (scall_safe (s := sCmpH) hf.comp).2
  have := (scall_safe (s := sDigH) hf.dig).2
  simp only [ctHashWith, hp, seqs, ctInit, lenLoop, compLoop, select, digestOut, digestAt, byteLoop,
    Code.x86_64Depth, Nat.max_le]
  omega

include hf in
theorem ctHash_xd : (ctHash f H).x86_64Depth ≤ 8 := ctHashWith_xd hf rfl

theorem copyWords64_safe (src dst : Reg) (so doff n : Nat) :
    (copyWords64 src dst so doff n).all safeI = true := by
  simp only [copyWords64, List.all_flatMap]
  apply List.all_eq_true.mpr
  intro j _
  rfl

theorem directLen_safe : (directLen H).allInstrs safeI = true := by
  unfold directLen
  split
  · simp only [Code.allInstrs, rec_all, copyWords64_safe, Bool.and_true]
    rfl
  · rfl

theorem directLen_xd : (directLen H).x86_64Depth = 0 := by
  unfold directLen
  split <;> rfl

theorem lenLast_safe : (lenLast H).allInstrs safeI = true := by
  unfold lenLast
  split
  · simp only [Code.allInstrs, rec_all, copyWords64_safe, List.all_append, Bool.and_true]
    rfl
  · rfl

theorem lenLast_xd : (lenLast H).x86_64Depth = 0 := by
  unfold lenLast
  split <;> rfl

include hH hf in
theorem fixedHash_safe : (fixedHash f H).allInstrs safeI = true := by
  have hl : H.P.len.all safeI = true := hH.taints.lenSafe
  simp only [fixedHash, seqs, ctInit, lenLast_safe (H := H), compAll, Code.allInstrs, (scall_safe hf.init).1,
    (scall_safe hf.comp).1, (scall_safe hf.dig).1, rec_all, lenField, digestAt, List.all_append, hl, Bool.and_true]
  rfl

include hf in
theorem fixedHash_xd : (fixedHash f H).x86_64Depth ≤ 8 := by
  have := (scall_safe (s := sIniH) hf.init).2
  have := (scall_safe (s := sCmpH) hf.comp).2
  have := (scall_safe (s := sDigH) hf.dig).2
  simp only [fixedHash, seqs, ctInit, lenLast_xd (H := H), compAll, digestAt, Code.x86_64Depth, Nat.max_le]
  omega

include hg in
theorem mgfXor_safe : (mgfXor H g).allInstrs safeI = true := by
  simp only [mgfXor, mgfRound, mgfSeed, seqs, Code.allInstrs, (scall_safe hg.init).1, (scall_safe hg.upd).1,
    (scall_safe hg.fin).1, Impl.Mgf1.X86_64.Table.xorOut, Impl.Mgf1.X86_64.seqs, Impl.Mgf1.X86_64.byteLoop,
    rec_all, List.all_append, Bool.and_true, Bool.true_and]
  rfl

include hg in
theorem mgfXor_xd : (mgfXor H g).x86_64Depth ≤ 16 := by
  have := (scall_safe (s := sIniG) hg.init).2
  have := (scall_safe (s := sUpdG) hg.upd).2
  have := (scall_safe (s := sFinG) hg.fin).2
  simp only [mgfXor, mgfRound, seqs, Impl.Mgf1.X86_64.Table.xorOut, Impl.Mgf1.X86_64.seqs,
    Impl.Mgf1.X86_64.byteLoop, Code.x86_64Depth, Nat.max_le]
  omega

include hH hf hg in
theorem signEnc_safe : (signEnc f H g).allInstrs safeI = true := by
  simp only [signEnc, seqs, clearY, copyDigest, copySaltY, clearEm, putSalt, putH, Code.allInstrs,
    ctHash_safe hH hf, mgfXor_safe hg, rec_all, List.all_append, byteLoop, step, Bool.and_true, Bool.true_and]
  rfl

include hf hg in
theorem signEnc_xd : (signEnc f H g).x86_64Depth ≤ 16 := by
  have := ctHash_xd (H := H) hf
  have := mgfXor_xd (H := H) hg
  simp only [signEnc, seqs, clearY, copyDigest, copySaltY, clearEm, putSalt, putH, byteLoop, Code.x86_64Depth,
    Nat.max_le]
  omega

/-- Code that is `safeI` and uses at most 16 bytes of stack keeps memory
outside the writable regions and the 16 bytes below `rsp`. -/
theorem WP.keepIn {c : Prog isa} (hc : c.allInstrs safeI = true) (hd : c.x86_64Depth ≤ 16) {u : State}
    {Q : State → Prop} (h : WP isa c u Q) :
    WP isa c u fun v => Q v ∧ ∀ a, (∀ r ∈ u.wr, ¬ r.Contains a 1) → ¬ (below (u.gpr .rsp) 16).Contains a 1 →
      v.mem a = u.mem a := by
  refine WP.mono (X86_64.WP.stackFrame (safe_sp hc) (by omega) h) fun v ⟨hq, hf⟩ => ⟨hq, fun a h1 h2 => ?_⟩
  refine Frame.below_mono hf hd (by decide) a fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · exact h1 r hr
  · simp only [List.mem_singleton] at hr; subst hr; exact h2

end VG.Proof.RsaPss.X86_64
