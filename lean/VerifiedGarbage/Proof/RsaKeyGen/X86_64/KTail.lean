module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.KEnd
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Proof.RsaKeyGen.Generate
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrShift
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrMain
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll

/-!
# A candidate on x86-64: Montgomery setup, Miller–Rabin and the result

`mrResult_ok`: the end from `kStat`, as the primality test's result ends a
candidate (`TestEnd`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- How a primality test's result ends a candidate `c`. -/
def TestEnd (s t : State) (B : Addr) (Z : Nat) (op up : Addr) (k : Nat) (r : List Byte) (c : Nat) :
    Option (Bool × List Byte) → Prop
  | none => KEnd s t B Z op up k 0 0 none
  | some (true, rest) => KEnd s t B Z op up k 1 (r.length - rest.length) (some c)
  | some (false, rest) => KEnd s t B Z op up k 3 (r.length - rest.length) none

/-- `mrResult`, after Miller–Rabin ended with `res`. -/
theorem mrResult_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c : Nat} {op up : Addr} {r : List Byte}
    {res : Option (Bool × List Byte)} (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 27)
    (hn : wv s.mem B (slot w aN) w = c) (ho : OutUp s B Z op up (8 * w))
    (hO : word s.mem B (8 * kOut) = op) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hU : word s.mem B (8 * kUsedP) = up)
    (h0 : res = none → word s.mem B (8 * kStat) = BitVec.ofNat 64 0)
    (h1 : ∀ b rest, res = some (b, rest) → word s.mem B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 3) ∧
      word s.mem B (8 * kUsed) = BitVec.ofNat 64 (r.length - rest.length)) :
    WP isa mrResult s fun t => TestEnd s t B Z op up (8 * w) r c res := by
  have hn' := hg.scr.nowrap
  have h8 : 8 * 32 ≤ Z := by have := hdr_lt_slot w 8 (show 31 < 32 by decide); omega_arith
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * kStat)) 8 :=
    hg.scr.ld (by have := hdr_lt_slot w 8 (show kStat < 32 by decide); omega_arith)
  unfold mrResult
  rcases hres : res with _ | ⟨b, rest⟩
  · have hS := h0 hres
    refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some true ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hS]) rfl) fun s₁ ⟨⟨hz, hm⟩, k₁⟩ => ?_)
    refine WP.ite true (by simp [eval, hz]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.mono (finNone_ok (hg.scr.congr k₁.2.2) ((k₁.gpr (by decide)).trans hg.rdi) h8 (by rw [hm]; exact hU)
      (by rw [k₁.2.2]; exact ho.upw) ho.upZ) fun t h => ?_
    exact (KEnd.of_fin (ho.congr k₁.2.2) h).trans_pre (fun i _ => by rw [hm]) (fun x _ => by rw [hm])
      (k₁.mono (by decide)) ho.outZ
  · obtain ⟨hS, hu⟩ := h1 b rest hres
    have hv : (if b then 1 else 3 : Nat) < 2 ^ 63 := by cases b <;> decide
    refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some false ∧
        t.gpr .rax = BitVec.ofNat 64 (if b then 1 else 3) ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hS, BitVec.and_self]; cases b <;> decide) rfl)
      fun s₁ ⟨⟨hz, hax₁, hm⟩, k₁⟩ => ?_)
    refine WP.ite false (by simp [eval, hz]) (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some b ∧ t.mem = s.mem) (by
      xrun [hax₁, hm]; cases b <;> decide) rfl) fun s₂ ⟨⟨hz₂, hm₂⟩, k₂⟩ => ?_)
    have hs₂ := (hg.scr.congr k₁.2.2).congr k₂.2.2
    have hdi₂ : s₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hg.rdi)
    have ho₂ := (ho.congr k₁.2.2).congr k₂.2.2
    have k12 : Keep mmRegs s s₂ := (k₁.trans k₂).mono (by decide)
    refine WP.ite b (by simp [eval, hz₂]) (fun hb => ?_) (fun hb => ?_)
    · subst hb
      have hg₂ : Good s₂ B Z w mi := ⟨hs₂, hdi₂, by rw [hm₂]; exact hg.hdr⟩
      refine WP.mono (finPrime_ok (u := r.length - rest.length) hg₂ hZ hw hw' (by rw [hm₂]; exact hu) (by rw [hm₂]; exact hO)
        (by rw [hm₂]; exact hK) (by rw [hm₂]; exact hU) ho₂.upw ho₂.upZ ho₂.outw ho₂.outZ ho₂.ou)
        fun t ⟨hb, hax, hus, hsv, hfr, k⟩ => ?_
      refine ⟨hax, hus, by rw [hm₂, hn] at hb; exact hb, fun i hi => by rw [hsv i hi, hm₂],
        fun x hx hx' hx'' => by rw [hfr x hx hx' hx'', hm₂], (k12.trans k).mono (by decide)⟩
    · subst hb
      refine WP.mono (finUsed_ok (u := r.length - rest.length) hs₂ hdi₂ h8 (by decide) (by rw [hm₂]; exact hu) (by rw [hm₂]; exact hU)
        ho₂.upw ho₂.upZ) fun t h => ?_
      exact (KEnd.of_fin ho₂ h).trans_pre (fun i _ => by rw [hm₂]) (fun x _ => by rw [hm₂]) k12 ho.outZ

end VG.Proof.RsaKeyGen.X86_64
