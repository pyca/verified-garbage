module

public import VerifiedGarbage.Impl.Ffdh.X86_64.GenerateKey
import VerifiedGarbage.Proof.Ffdh.X86_64.Scan
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
public import VerifiedGarbage.Proof.Ffdh.KeyScalar
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Front

/-! # FFDH on x86-64: scanning the public scalar bound -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The public bound is q when present and p otherwise. -/
def boundPtr (dp : Addr) (k : Nat) (dom : List Byte) : Addr :=
  if dom.length = 3 * k then off dp (2 * k) else dp

/-- The bound scan returns its first significant octet and remaining width. -/
theorem bound_ok {s : State} {B dp : Addr} {Z k dl : Nat} {dom : List Byte}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : 256 ≤ Z)
    (hk1 : 1 ≤ k) (hk : k < 2 ^ 30) (hd : dl = 2 * k ∨ dl = 3 * k) (hl : dom.length = dl)
    (hD : word s.mem B (8 * sDom) = dp) (hQ : word s.mem B (8 * sQ) = off dp (2 * k))
    (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hDl : word s.mem B (8 * sDomLen) = BitVec.ofNat 64 dl) (hsrc : Src s B Z dp dom) :
    WP isa (seqs bound) s fun t => ∃ hne : KeyScalar.bnd k dom ≠ [],
      word t.mem B (8 * sEp) = off (boundPtr dp k dom) (lead (KeyScalar.bnd k dom)) ∧
      word t.mem B (8 * sEl) = BitVec.ofNat 64 (k - lead (KeyScalar.bnd k dom)) ∧
      t.gpr .rax = ((KeyScalar.bnd k dom)[lead (KeyScalar.bnd k dom)]'(lead_lt hne)).setWidth 64 ∧
      Frm B [(8 * sEp, 8), (8 * sEl, 8)] s.mem t.mem ∧
      Keep [.rsi, .rcx, .rax, .rbp, .rdx] s t := by
  have hlen := KeyScalar.bnd_length (k := k) (dom := dom) (by rw [hl]; exact hd)
  have hne : KeyScalar.bnd k dom ≠ [] := by intro he; rw [he] at hlen; simp at hlen; omega
  have h2 : 2 * k ≤ dl := by rcases hd with h | h <;> omega
  have hdl : dl < 2 ^ 32 := by rcases hd with h | h <;> omega
  unfold bound
  change WP isa (.seq (.block qTest) (.ite .e (seqs (scan sDom)) (seqs (scan sQ)))) s _
  refine WP.seq (WP.mono (qTest_ok hs hdi hZ hDl hK h2 hdl) fun u ⟨_, hz, hm, ku⟩ => ?_)
  have hsu := hs.congr ku.2.2
  have hdu : u.gpr .rdi = B := (ku.gpr (by decide)).trans hdi
  have hsrcu : Src u B Z dp dom := hsrc.congrK (by intro a _; rw [hm]) ku
  have run (sp : Nat) (hsp : sp < 32) (he : (if dl = 3 * k then sQ else sDom) = sp) :
      WP isa (seqs (scan sp)) u fun t => ∃ hne : KeyScalar.bnd k dom ≠ [],
        word t.mem B (8 * sEp) = off (boundPtr dp k dom) (lead (KeyScalar.bnd k dom)) ∧
        word t.mem B (8 * sEl) = BitVec.ofNat 64 (k - lead (KeyScalar.bnd k dom)) ∧
        t.gpr .rax = ((KeyScalar.bnd k dom)[lead (KeyScalar.bnd k dom)]'(lead_lt hne)).setWidth 64 ∧
        Frm B [(8 * sEp, 8), (8 * sEl, 8)] s.mem t.mem ∧
        Keep [.rsi, .rcx, .rax, .rbp, .rdx] s t := by
    have hp : word u.mem B (8 * sp) = boundPtr dp k dom := by
      rw [hm]
      unfold boundPtr
      rw [hl]
      by_cases h3 : dl = 3 * k
      · rw [ite_eq_left h3] at he ⊢
        rw [← he]; exact hQ
      · rw [ite_eq_right h3] at he ⊢
        rw [← he]; exact hD
    have src : Src u B Z (boundPtr dp k dom) (KeyScalar.bnd k dom) := by
      unfold boundPtr KeyScalar.bnd
      rw [hl]
      split
      · exact (hsrcu.drop (2 * k)).take k
      · exact hsrcu.take k
    refine WP.mono (scan_raw_ok (B := B) (Z := Z) (sp := sp) (p := boundPtr dp k dom)
      (bs := KeyScalar.bnd k dom) hsu hdu hZ hsp hp (by rw [hlen, hm]; exact hK) hne (by omega) src)
      fun t ⟨hEp, hEl, hax, hf, kt⟩ => ?_
    exact ⟨hne, hEp, by rwa [hlen] at hEl, hax, fun a ha => by rw [hf a ha, hm],
      (ku.trans kt).mono (by decide)⟩
  refine WP.ite (decide (dl = 2 * k)) (by simp [eval, hz]) (fun he => ?_) (fun he => ?_)
  · have hno := of_decide_eq_true he
    exact run sDom (by decide) (ite_eq_right (by omega))
  · have hno := of_decide_eq_false he
    have hq : dl = 3 * k := by rcases hd with h | h <;> omega
    exact run sQ (by decide) (ite_eq_left hq)

end VG.Proof.Ffdh.X86_64.GenerateKey
