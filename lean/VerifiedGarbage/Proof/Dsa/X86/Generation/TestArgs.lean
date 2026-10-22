module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Words
import VerifiedGarbage.Proof.Dsa.X86.Generation.Hash

/-! # The arguments of a probable-prime test

The working space at `sPP`, its 64-bit words, the witnesses left (from
`fUsed` on) and the word `fUsedOut` for the octets the test reads. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)

/-- The registers a test's call pushes: `ws`, `ws_len`, `rand`, `rand_len`
and `used`, from the state words. -/
structure TestArgs (base : Addr) (W : BitVec 32) (witLen used : Nat) (s t : State) : Prop where
  eax : t.gpr .eax = s.gpr .edi + BitVec.ofNat 32 sPP
  ecx : t.gpr .ecx = BitVec.ofNat 32 ppWords
  edx : t.gpr .edx = W + BitVec.ofNat 32 used
  ebx : t.gpr .ebx = BitVec.ofNat 32 (witLen - used)
  ebp : t.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 fUsedOut
  other : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .ebp → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

theorem testArgs_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (hsz : sPP ≤ size)
    {W : BitVec 32} {witLen used : Nat} (hW : s.mem.readW (off base fWit) 32 = W)
    (hWL : s.mem.readW (off base fWitLen) 32 = BitVec.ofNat 32 witLen)
    (hU : s.mem.readW (off base fUsed) 32 = BitVec.ofNat 32 used) (hu : used ≤ witLen)
    (hwl : witLen < 2 ^ 32) {is : List Instr}
    {Q : State → Prop} (k : ∀ t, TestArgs base W witLen used s t → WP isa (.block is) t Q) :
    WP isa (.block (([.mov .ecx (.mem (sc fUsed)), .mov .edx (.mem (sc fWit)), .alu .add .edx (.reg .ecx),
      .mov .ebx (.mem (sc fWitLen)), .alu .sub .ebx (.reg .ecx)] ++ scr .eax sPP ++
      [.mov .ecx (.imm (BitVec.ofNat 32 ppWords))] ++ scr .ebp fUsedOut) ++ is)) s Q := by
  have szs : fWitLen + 4 ≤ size ∧ fUsed + 4 ≤ size ∧ fWit + 4 ≤ size := by
    simp only [fWitLen, fUsed, fWit, hdr, sPP] at hsz ⊢; omega
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine ld_ok hs (by omega) fun s₁ u₁ => ld_ok (Scr.of_eq hs (u₁.other _ (by decide))
    (u₁.other _ (by decide)) u₁.wr) (by omega) fun s₂ u₂ => wp_add fun s₃ u₃ _ => ?_
  refine ld_ok (Scr.of_eq hs (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [u₃.wr, u₂.wr, u₁.wr])) (by omega) fun s₄ u₄ => wp_sub fun s₅ u₅ _ => ?_
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have edi₅ : s₅.gpr .edi = s.gpr .edi := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide)]
  refine scr_ok fun s₆ e₆ g₆ m₆ rd₆ wr₆ sy₆ => wp_movi fun s₇ u₇ => scr_ok fun s₈ e₈ g₈ m₈ rd₈ wr₈ sy₈ => ?_
  have c₂ : s₂.gpr .ecx = BitVec.ofNat 32 used := by rw [u₂.other _ (by decide), u₁.gpr, hU]
  have d₂ : s₂.gpr .edx = W := by rw [u₂.gpr, u₁.mem, hW]
  have d₃ : s₃.gpr .edx = W + BitVec.ofNat 32 used := by rw [u₃.gpr, d₂, c₂]
  have b₅ : s₅.gpr .ebx = BitVec.ofNat 32 (witLen - used) := by
    rw [u₅.gpr, u₄.gpr, u₄.other _ (by decide), u₃.other _ (by decide), c₂, u₃.mem, u₂.mem, u₁.mem, hWL,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) hu]
  refine k s₈ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g₈ _ (by decide), u₇.other _ (by decide), e₆, edi₅]
  · rw [g₈ _ (by decide), u₇.gpr]
  · rw [g₈ _ (by decide), u₇.other _ (by decide), g₆ _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), d₃]
  · rw [g₈ _ (by decide), u₇.other _ (by decide), g₆ _ (by decide), b₅]
  · rw [e₈, u₇.other _ (by decide), g₆ _ (by decide), edi₅]
  · intro r a b c d e
    rw [g₈ r e, u₇.other r c, g₆ r a, u₅.other r b, u₄.other r b, u₃.other r d, u₂.other r d, u₁.other r c]
  · rw [m₈, u₇.mem, m₆, m₅]
  · rw [rd₈, u₇.rd, rd₆, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [wr₈, u₇.wr, wr₆, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [sy₈, u₇.syms, sy₆, u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms]

end VG.Proof.Dsa.X86.Generation
