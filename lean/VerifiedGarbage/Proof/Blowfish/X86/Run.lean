module

public import VerifiedGarbage.Impl.Blowfish.X86
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.MlDsa.X86.Pack.Run
import VerifiedGarbage.Proof.Rc4.Dword
public import VerifiedGarbage.TCB.Mem

/-!
# Blowfish on x86 (32-bit): running blocks

`brun [facts]` steps a block (ML-DSA's `xrun`, `Proof/MlDsa/X86/Pack/Run.lean`),
with the memory operands of the Blowfish code, `at_ b d`, at `addr (s.gpr b) d`.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86

open VG VG.X86 VG.Impl.Blowfish.X86
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

theorem eaAt (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

/-- Steps a block of the Blowfish code, from a state whose accesses the hypotheses permit. -/
tactic_template "brun" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
      try unfold imm at *
      xrun [eaAt, xlOff, xrOff, fOff, ppOff, ptrOff, cntOff, List.cons_append, List.nil_append, $ls,*]))
/-- `brun` with no extra lemmas. -/
macro "brun" : tactic => `(tactic| brun [])

/-- `WP.keep` for `Keep` into a larger list. -/
theorem Keep.trans_sub {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keep rs s₁ s₂)
    (h₂ : Keep rs' s₂ s₃) (hs : rs'.all (rs.contains ·) = true) : Keep rs s₁ s₃ :=
  (h₁.trans h₂).mono fun r hr => by
    rcases List.mem_append.mp hr with h | h
    · exact h
    · have := List.all_eq_true.mp hs r h
      simpa only [List.contains_iff_mem] using this

theorem keep_reads {s t : State} {rs : List Reg} (k : Keep rs s t) : t.rd ++ t.wr = s.rd ++ s.wr := by
  rw [k.2.1, k.2.2]

theorem WP.reassoc {a b c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a b) c) s Q) : WP isa (.seq a (.seq b c)) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)

/-- The branch conditions. -/
theorem eval_ne (s : State) : isa.eval .ne s = s.zf.map (!·) := rfl
theorem eval_e (s : State) : isa.eval .e s = s.zf := rfl

theorem region_in {rs ws : List Region} {a : Addr} {n : Nat} (h : InRegions ws a n) :
    InRegions (rs ++ ws) a n := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem inRegions_off {rs : List Region} {a : Addr} {N o n : Nat} (h : InRegions rs a N) (hon : o + n ≤ N) :
    InRegions rs (a + BitVec.ofNat 64 o) n := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, hr, ?_⟩
  simp only [Region.Contains] at hc ⊢
  have e : a + BitVec.ofNat 64 o - r.base = (a - r.base) + BitVec.ofNat 64 o := by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 o),
      ← BitVec.add_assoc]
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := Nat.mod_le ((a - r.base).toNat + o % 2 ^ 64) (2 ^ 64)
  have := Nat.mod_le o (2 ^ 64)
  omega

theorem inRegions_pre {rs : List Region} {a : Addr} {N n : Nat} (h : InRegions rs a N) (hn : n ≤ N) :
    InRegions rs a n := by
  have := inRegions_off (o := 0) (n := n) h (by omega)
  rwa [BitVec.add_zero] at this

/-! ## Offsets from a pointer -/

theorem ofs_add (S : BitVec 32) (a b : Nat) :
    S + BitVec.ofNat 32 a + BitVec.ofNat 32 b = S + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem ofs_sub (S : BitVec 32) {a b : Nat} (h : b ≤ a) :
    S + BitVec.ofNat 32 a - BitVec.ofNat 32 b = S + BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The schedule's address less a pointer `a` bytes into it. -/
theorem ofs_neg (S : BitVec 32) (a : Nat) :
    S - (S + BitVec.ofNat 32 a) = BitVec.ofNat 32 (2 ^ 32 - a % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := S.isLt
  omega

theorem ofNat_sub_beq {a c : Nat} (ha : a < 2 ^ 32) (hc : c < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 c == 0#32) = decide (a = c) := by
  by_cases h : a = c
  · subst h; simp
  · have : BitVec.ofNat 32 a - BitVec.ofNat 32 c ≠ 0#32 := by
      intro e
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
      omega
    simp [this, h]

theorem ofNat_sub_beq' {a c : Nat} (ha : a < 2 ^ 32) (hc : c < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 c == 0) = decide (a = c) := ofNat_sub_beq ha hc

end VG.Proof.Blowfish.X86
