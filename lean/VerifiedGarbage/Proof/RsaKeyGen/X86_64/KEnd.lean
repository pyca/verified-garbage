import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Fin

/-!
# A candidate on x86-64: how it ends

`KEnd`: the status, `used`, `out` (the prime, or unchanged), the saved
registers restored and memory outside the scratch space, `out` and `used`
unchanged. `finUsed_end` and `finNone_end`: the ends that leave `out`.
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- The octets of `out`. -/
abbrev outBytes (m : Mem) (op : Addr) (k : Nat) : List Byte := (List.range k).map fun i => m (op + BitVec.ofNat 64 i)

/-- How a candidate ends, from `s`: status `st`, `u` to `used`, and `out`
the `k` octets of `c` if `outv = some c`, else unchanged. -/
structure KEnd (s t : State) (B : Addr) (Z : Nat) (op up : Addr) (k st u : Nat) (outv : Option Nat) : Prop where
  rax : t.gpr .rax = BitVec.ofNat 64 st
  used : t.mem.readW up 64 = BitVec.ofNat 64 u
  out : outBytes t.mem op k = match outv with
    | some c => Spec.Rsa.i2osp c k
    | none => outBytes s.mem op k
  saved : ∀ i < 6, t.gpr (saved.getD i .rax) = word s.mem B (8 * i)
  frame : ∀ x, Z ≤ ofs B x → (∀ b < 8, x ≠ up + BitVec.ofNat 64 b) → (∀ j < k, x ≠ op + BitVec.ofNat 64 j) →
    t.mem x = s.mem x
  keep : Keep mmRegs s t

/-- The facts about `out` and `used` every end needs. -/
structure OutUp (s : State) (B : Addr) (Z : Nat) (op up : Addr) (k : Nat) : Prop where
  upw : InRegions s.wr up 8
  upZ : ∀ b < 8, Z ≤ ofs B (up + BitVec.ofNat 64 b)
  outw : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1
  outZ : ∀ j < k, Z ≤ ofs B (op + BitVec.ofNat 64 j)
  ou : ∀ j < k, ∀ b < 8, op + BitVec.ofNat 64 j ≠ up + BitVec.ofNat 64 b

theorem OutUp.congr {s t : State} {B : Addr} {Z : Nat} {op up : Addr} {k : Nat} (h : OutUp s B Z op up k)
    (hw : t.wr = s.wr) : OutUp t B Z op up k :=
  ⟨by rw [hw]; exact h.upw, h.upZ, fun j hj => by rw [hw]; exact h.outw j hj, h.outZ, h.ou⟩

theorem KEnd.of_fin {s t : State} {B : Addr} {Z : Nat} {op up : Addr} {k st u : Nat} (ho : OutUp s B Z op up k)
    (h : FinPost s t B Z up st u) : KEnd s t B Z op up k st u none :=
  ⟨h.rax, h.used, List.map_congr_left fun i hi => h.frame _ (ho.outZ i (List.mem_range.mp hi))
    fun b hb => ho.ou i (List.mem_range.mp hi) b hb, h.saved, fun x hx hx' _ => h.frame x hx hx', h.keep⟩

/-- `KEnd` from a state with the same memory below `Z` and the same
registers but `mmRegs`. -/
theorem KEnd.trans_pre {s₀ s t : State} {B : Addr} {Z : Nat} {op up : Addr} {k st u : Nat} {outv : Option Nat}
    (h : KEnd s t B Z op up k st u outv) (hlo : ∀ i < 6, word s.mem B (8 * i) = word s₀.mem B (8 * i))
    (hhi : ∀ x, Z ≤ ofs B x → s.mem x = s₀.mem x) (k₀ : Keep mmRegs s₀ s)
    (hoZ : ∀ j < k, Z ≤ ofs B (op + BitVec.ofNat 64 j)) :
    KEnd s₀ t B Z op up k st u outv := by
  refine ⟨h.rax, h.used, ?_, fun i hi => (h.saved i hi).trans (hlo i hi), fun x hx hx' hx'' =>
    (h.frame x hx hx' hx'').trans (hhi x hx), (k₀.trans h.keep).mono (by decide)⟩
  rw [h.out]
  cases outv
  · exact List.map_congr_left fun i hi => hhi _ (hoZ i (List.mem_range.mp hi))
  · rfl

end VG.Proof.RsaKeyGen.X86_64
