import VerifiedGarbage.Proof.Rsa.X86_64.RpHalf

/-!
# `vg_rsa_recover_primes` on x86-64: what the pieces change

`rg w js hs`: the arrays `js` and the header slots `hs`, as ranges of the
working space. A piece changes only some of them (`Frm B (rg w js hs)`), and
an array or a slot that is not listed keeps its value (`Frm.rg_wv`,
`Frm.rg_word`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem rg_rmut {w : Nat} {js hs : List Nat} (h : ∀ i ∈ hs, rSlot i = true) : ∀ r ∈ rg w js hs, RMut r := by
  intro r hr
  simp only [rg, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨j, _, rfl⟩ | ⟨i, hi, rfl⟩
  · exact RMut.ofSlot _ _ _
  · exact RMut.hdr (h i hi)

theorem Ws.congrG {s t : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {js hs : List Nat}
    (hf : Frm B (rg w js hs) s.mem t.mem) (hhs : ∀ i ∈ hs, rSlot i = true) {regs : List Reg} (k : Keep regs s t)
    (hr : .rdi ∉ regs) : Ws t B Z w :=
  h.congrR hf (rg_rmut hhs) k hr

end VG.Proof.Rsa.X86_64
