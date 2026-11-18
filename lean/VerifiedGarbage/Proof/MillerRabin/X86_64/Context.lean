module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSq
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnVerified
import VerifiedGarbage.Proof.Bignum.CrtExp
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Stack
import VerifiedGarbage.Proof.MillerRabin.X86_64.StackContext

/-! ### `MillerRabin.X86_64.StageContext`, which the modules that import this one used -/

section

/-! ### `MillerRabin.X86_64.StackPrepared`, which the modules that import this one used -/

section

/-! # The Montgomery and exponent contexts survive the saved frame -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.X86_64
open VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.RsaKeyGen.X86_64.Candidate

private theorem dim_read {B : Addr} {Z w j k : Nat} (h : MrDims B Z w)
    (hj : j ≤ 26) (hk : k ≤ w + 2) : slot w j + 8 * k ≤ Z := by
  have hm := VG.Proof.Bignum.slot_mono w hj
  have hx := h.x
  change slot w 26 + 8 * (w + 2) ≤ Z at hx
  omega_arith

theorem entered_ctx {s : State} {B : Addr} {Z w c bm : Nat} {mi : BitVec 64}
    (hc : MrCtx s B Z w mi c bm) (h : MrDims B Z w)
    (hs : 120 ≤ (s.gpr .rsp).toNat)
    (hd : Region.Disjoint ⟨s.gpr .rsp - 112#64, 112⟩ ⟨B, Z⟩) :
    MrCtx (entered s) B Z w mi c bm := by
  have hn := hc.good.scr.nowrap
  refine ⟨entered_good hc.good h.z hs hd, ?_, ?_, ?_, ?_, ?_⟩
  · rw [entered_word hs hn hd (dim_read h (by decide : aN ≤ 26) (by omega_arith : 1 ≤ w + 2))]
    exact hc.inv
  · rw [entered_wv hs hn hd (dim_read h (by decide : aN ≤ 26) (by omega_arith))]
    exact hc.n
  · rw [entered_wv hs hn hd (dim_read h (by decide : aB ≤ 26) (by omega_arith))]
    exact hc.b
  · rw [entered_wv hs hn hd (dim_read h (by decide : aR1 ≤ 26) (by omega_arith))]
    exact hc.r1
  · rw [entered_wv hs hn hd (dim_read h (by decide : aRm1 ≤ 26) (by omega_arith))]
    exact hc.rm1

theorem entered_exp {s : State} {B : Addr} {Z w c : Nat}
    (he : ECtx s.mem B w c) (h : MrDims B Z w)
    (hs : 120 ≤ (s.gpr .rsp).toNat) (hn : B.toNat + Z ≤ 2 ^ 64)
    (hd : Region.Disjoint ⟨s.gpr .rsp - 112#64, 112⟩ ⟨B, Z⟩) :
    ECtx (entered s).mem B w c := by
  refine ⟨?_, ?_⟩
  · rw [entered_wv hs hn hd (dim_read h (by decide : aE ≤ 26) (by omega_arith))]
    exact he.e
  · rw [entered_word hs hn hd (by have := dim_read (j := aE) (k := w + 1) h (by decide) (by omega_arith); omega_arith)]
    exact he.l

end VG.Proof.MillerRabin.X86_64

end

end

/-! # Staging saved words does not change the prepared workspace -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaKeyGen.X86_64
open VG.Proof.MlKem.X86_64

theorem staged_context {s t : State} {B : Addr} {Z w c bm : Nat} {mi : BitVec 64}
    (hc : MrCtx s B Z w mi c bm) (he : ECtx s.mem B w c)
    (hm : t.mem = s.mem) (hk : Keep [.rsi, .rdx, .rcx, .r8, .r9, .rax, .r10, .r11] s t) :
    MrCtx t B Z w mi c bm ∧ ECtx t.mem B w c := by
  refine ⟨⟨⟨hc.good.scr.congr hk.2.2, (hk.gpr (by decide)).trans hc.good.rdi, ?_⟩,
    ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hm]; exact hc.good.hdr
  · rw [hm]; exact hc.inv
  · rw [hm]; exact hc.n
  · rw [hm]; exact hc.b
  · rw [hm]; exact hc.r1
  · rw [hm]; exact hc.rm1
  · rw [hm]; exact he

end VG.Proof.MillerRabin.X86_64

end

end

/-! # A prepared x86-64 workspace supplies the shared round's context -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Impl.Bignum VG.Impl.Bignum.Public
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum.X86_64.MontFn (numAt_eq)

theorem initial_ctx {s : State} (h : roundPre s) :
    let B := s.gpr .rdi
    let Z := (s.gpr .rsi).toNat * 8
    let w := Proof.Rsa.Mont.wOf s.mem B
    let c := Proof.Rsa.Mont.numAt s.mem B w 0
    MrDims B Z w ∧ ∃ bm, MrCtx s B Z w (word s.mem B (8 * sMinv)) c bm ∧
      ECtx s.mem B w c ∧ c % 2 = 1 ∧ 3 ≤ c ∧ wv s.mem B (slot w aXm) w < c := by
  rcases h with ⟨-, hwr, hn, -, -, -, hL, hp⟩
  dsimp only [Proof.MillerRabin.Round.Layout, Proof.MillerRabin.Round.extended] at hL
  rcases hL with ⟨-, hm, h4, h128, hspace, -⟩
  rcases hm with ⟨-, -, -, harr⟩
  dsimp only [Proof.MillerRabin.Round.Prepared, Proof.MillerRabin.Round.extended] at hp
  rcases hp with ⟨h3, hodd, hinv, hxm, hr1, hrm1, he, hl⟩
  dsimp only
  let B := s.gpr .rdi
  let Z := (s.gpr .rsi).toNat * 8
  let w := Proof.Rsa.Mont.wOf s.mem B
  let c := Proof.Rsa.Mont.numAt s.mem B w 0
  have hs : Scr s B Z := Scr.of_mem (by rw [hwr]; simp [B, Z]) hn
  have h27 : slot w 27 ≤ Z := by
    change slot w 27 ≤ 8 * (s.gpr .rsi).toNat at hspace
    simpa only [Z, Nat.mul_comm] using hspace
  have hz : slot w 8 ≤ Z := Nat.le_trans (VG.Proof.Bignum.slot_mono w (by decide : 8 ≤ 27)) h27
  have hd : MrDims B Z w := ⟨hz, by
    change slot w 26 + 8 * (w + 2) ≤ Z
    rw [← VG.Proof.Bignum.slot_succ w 26]
    exact h27, h4, h128⟩
  have hg : Good s B Z w (word s.mem B (8 * sMinv)) := by
    refine ⟨hs, rfl, ?_, rfl, ?_⟩
    · simp only [w, Proof.Rsa.Mont.wOf, Proof.Rsa.Mont.wordAt, Proof.Rsa.Mont.wWord, VG.Proof.Bignum.word, sW, off]
      simp
    · intro j hj
      exact harr j hj
  refine ⟨hd, wv s.mem B (slot w aB) w, ⟨hg, hinv, ?_, rfl, ?_, ?_⟩,
    ⟨?_, ?_⟩, hodd, h3, ?_⟩
  · exact (numAt_eq s.mem B w 0).symm
  · rw [← numAt_eq s.mem B w aR1]
    exact hr1
  · rw [← numAt_eq s.mem B w aRm1]
    exact hrm1
  · rw [← numAt_eq s.mem B w aE]
    simpa only [Proof.MillerRabin.Round.exponent, Proof.MillerRabin.Round.shift, mrE, mrSig, sigOf, mrA, aE, B, w, c] using he
  · exact hl
  · rw [← numAt_eq s.mem B w aXm]
    exact hxm

end VG.Proof.MillerRabin.X86_64
