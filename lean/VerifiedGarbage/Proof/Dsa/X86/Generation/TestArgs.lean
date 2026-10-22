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

/-- The witnesses left: from `used` on, or the start of the tape once none
is left (so that the pointer stays within the tape). -/
def randPtr (W : BitVec 32) (witLen used : Nat) : BitVec 32 :=
  if witLen - used = 0 then W else W + BitVec.ofNat 32 used

/-- The registers a test's call pushes: `ws`, `ws_len`, `rand`, `rand_len`
and `used`, from the state words. -/
structure TestArgs (base : Addr) (W : BitVec 32) (witLen used : Nat) (s t : State) : Prop where
  eax : t.gpr .eax = s.gpr .edi + BitVec.ofNat 32 sPP
  ecx : t.gpr .ecx = BitVec.ofNat 32 ppWords
  edx : t.gpr .edx = randPtr W witLen used
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
    (hwl : witLen < 2 ^ 32) :
    WP isa (.seq (.block [.mov .ecx (.mem (sc fUsed)), .mov .edx (.mem (sc fWit)), .alu .add .edx (.reg .ecx),
        .mov .ebx (.mem (sc fWitLen)), .alu .sub .ebx (.reg .ecx)])
      (.seq (.ite .e (.block [.mov .edx (.mem (sc fWit))]) (.block []))
        (.block (scr .eax sPP ++ [.mov .ecx (.imm (BitVec.ofNat 32 ppWords))] ++ scr .ebp fUsedOut)))) s
      (TestArgs base W witLen used s) := by
  have szs : fWitLen + 4 ≤ size ∧ fUsed + 4 ≤ size ∧ fWit + 4 ≤ size := by
    simp only [fWitLen, fUsed, fWit, hdr, sPP] at hsz ⊢; omega
  refine WP.seq (ld_ok hs (by omega) fun s₁ u₁ => ld_ok (Scr.of_eq hs (u₁.other _ (by decide))
    (u₁.other _ (by decide)) u₁.wr) (by omega) fun s₂ u₂ => wp_add fun s₃ u₃ _ => ?_)
  have edi₃ : s₃.gpr .edi = s.gpr .edi := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  refine ld_ok (Scr.of_eq hs edi₃
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [u₃.wr, u₂.wr, u₁.wr])) (by omega) fun s₄ u₄ => wp_sub fun s₅ u₅ z₅ => WP.block_nil ?_
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have edi₅ : s₅.gpr .edi = s.gpr .edi := by rw [u₅.other _ (by decide), u₄.other _ (by decide), edi₃]
  have sp₅ : s₅.gpr .esp = s.gpr .esp := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide)]
  have wr₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have c₂ : s₂.gpr .ecx = BitVec.ofNat 32 used := by rw [u₂.other _ (by decide), u₁.gpr, hU]
  have d₂ : s₂.gpr .edx = W := by rw [u₂.gpr, u₁.mem, hW]
  have b₅ : s₅.gpr .ebx = BitVec.ofNat 32 (witLen - used) := by
    rw [u₅.gpr, u₄.gpr, u₄.other _ (by decide), u₃.other _ (by decide), c₂, u₃.mem, u₂.mem, u₁.mem, hWL,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) hu]
  have d₅ : s₅.gpr .edx = W + BitVec.ofNat 32 used := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, d₂, c₂]
  have z : s₅.zf = some (decide (witLen - used = 0)) := by
    rw [z₅, ← u₅.gpr, b₅, ofNat_beq_zero (by omega)]
  have hs₅ : Scr s₅ base size := Scr.of_eq hs edi₅ sp₅ wr₅
  have tail : ∀ x : State, x.gpr .edi = s.gpr .edi → x.gpr .edx = randPtr W witLen used →
      x.gpr .ebx = BitVec.ofNat 32 (witLen - used) →
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .ebp → x.gpr r = s.gpr r) →
      x.mem = s.mem → x.rd = s.rd → x.wr = s.wr → x.syms = s.syms →
      WP isa (.block (scr .eax sPP ++ [.mov .ecx (.imm (BitVec.ofNat 32 ppWords))] ++ scr .ebp fUsedOut)) x
        (TestArgs base W witLen used s) := by
    intro x xd xdx xbx xo xm xrd xwr xsy
    simp only [List.append_assoc]
    refine scr_ok fun s₆ e₆ g₆ m₆ rd₆ wr₆ sy₆ => wp_movi fun s₇ u₇ => scr_ok fun s₈ e₈ g₈ m₈ rd₈ wr₈ sy₈ => ?_
    refine WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [g₈ _ (by decide), u₇.other _ (by decide), e₆, xd]
    · rw [g₈ _ (by decide), u₇.gpr]
    · rw [g₈ _ (by decide), u₇.other _ (by decide), g₆ _ (by decide), xdx]
    · rw [g₈ _ (by decide), u₇.other _ (by decide), g₆ _ (by decide), xbx]
    · rw [e₈, u₇.other _ (by decide), g₆ _ (by decide), xd]
    · intro r a b c d e
      rw [g₈ r e, u₇.other r c, g₆ r a, xo r a b c d e]
    · rw [m₈, u₇.mem, m₆, xm]
    · rw [rd₈, u₇.rd, rd₆, xrd]
    · rw [wr₈, u₇.wr, wr₆, xwr]
    · rw [sy₈, u₇.syms, sy₆, xsy]
  have o₅ : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .ebp → s₅.gpr r = s.gpr r := by
    intro r a b c d e
    rw [u₅.other r b, u₄.other r b, u₃.other r d, u₂.other r d, u₁.other r c]
  have rd₅ : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have sy₅ : s₅.syms = s.syms := by rw [u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms]
  refine WP.seq (WP.ite (decide (witLen - used = 0)) z (fun hz => ld_ok hs₅ (by omega) fun s₆ u₆ =>
    WP.block_nil (tail s₆ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)) (fun hz => WP.block_nil (tail s₅ edi₅ ?_ b₅ o₅ m₅ rd₅ wr₅ sy₅)))
  · rw [u₆.other _ (by decide), edi₅]
  · have h0 : witLen - used = 0 := by simpa using hz
    rw [u₆.gpr, m₅, hW]; simp only [randPtr, h0, ↓reduceIte]
  · rw [u₆.other _ (by decide), b₅]
  · intro r a b c d e; rw [u₆.other r d, o₅ r a b c d e]
  · rw [u₆.mem, m₅]
  · rw [u₆.rd, rd₅]
  · rw [u₆.wr, wr₅]
  · rw [u₆.syms, sy₅]
  · have h0 : ¬ witLen - used = 0 := by simpa using hz
    rw [d₅]; simp only [randPtr, h0, ↓reduceIte]

end VG.Proof.Dsa.X86.Generation
