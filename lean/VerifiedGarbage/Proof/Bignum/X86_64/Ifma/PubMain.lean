module

import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.PubExp
public import VerifiedGarbage.Proof.Bignum.X86_64.FoldedMain
public import VerifiedGarbage.Impl.Rsa.X86_64.PubIfma
public import VerifiedGarbage.Proof.Bignum.Amm52
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedExp
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcMain
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import Mathlib.Tactic.TermCongr
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Set

/-!
# The public operation with AVX512_IFMA on x86-64: the dispatch

`pubExp`: for `e = 65537` and a modulus of 32, 48 or 64 words, the vector
code (`exp65537_ok`), and otherwise the ADX code's (`phasesCore_ok`);
`rest_ok`, as `FoldedPublic.rest_ok`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma.Pub

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.FoldedPublic
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.PubIfma (cmpW pubExp exp65537 adxExp pay2048 pay3072 pay4096)

/-- `cmp w, n`, `w` from the header. -/
theorem cmpW_ok {t : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (n : Nat) (hg : VG.Proof.Bignum.X86_64.Good t B Z w mi)
    (hZ : slot w 8 ≤ Z) (hn : n < 2 ^ 31) (hw : w < 2 ^ 31) :
    WP isa (cmpW n) t fun u => u.zf = some (decide (w = n)) ∧ u.mem = t.mem ∧ Keep [.rax] t u := by
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.zf = some (decide (w = n)) ∧ u.mem = t.mem) (by
    unfold cmpW
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hg.hdr.hw, AmmSym.se_ofNat hn]
    and_intros
    rw [ofNat_sub_beq (by omega) (by omega)]) rfl) fun u ⟨⟨z, m⟩, k⟩ => ⟨z, m, k⟩

/-- `pubExp`. -/
theorem pubExp_ok (M : Mont) {s : State} {B : Addr} {Z k : Nat} {op ep ip : Addr}
    {L : Nat} {eb xb : List Byte} {N R : Nat}
    (h : PdPre s B Z k op ep ip L eb xb N R) (a : State) (mi : BitVec 64)
    (so : SetupOut a B Z ((k+7)/8) mi N (Spec.Rsa.os2ip xb)) (fa : Frm B (pdAll ((k+7)/8)) s.mem a.mem)
    (ka : Keep mmRegs s a) (rra : wv a.mem B (slot ((k+7)/8) aR2) ((k+7)/8) = R)
    (hmx : (seqs (phases M)).allInstrs (fun i => !loadsMxcsr i) = true) :
    WP isa (seqs [pubExp M.mm]) a (ExpOut B Z ((k+7)/8) mi N R (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip eb) a) := by
  have hk1 := h.k1
  have hk2 := h.k2
  have hL2 := h.L2
  have hZ := h.z
  have hle : ∀ r ∈ pdAll ((k+7)/8), r.1+r.2 ≤ Z :=
    fun r hr => (pdAll_le _ r hr).trans hZ
  have xa := Fixed.of_frm fa (pdAll_fixed _)
  have hsrc := h.e.congrK (InScr.of_frm fa hle) ka
  rw [seqs_one]
  unfold pubExp
  refine WP.seq (WP.mono_mx (by decide +kernel) (is65537_ok so.good hZ (by rw [xa sE (by decide)]; exact h.hE)
    (by rw [xa sElen (by decide)]; exact h.hL) hsrc h.el h.L1 (by omega)) fun u ⟨zu, mu, ku⟩ xu => ?_)
  have gu : VG.Proof.Bignum.X86_64.Good u B Z ((k+7)/8) mi := ⟨so.good.scr.congr ku.2.2, (ku.gpr (by decide)).trans so.good.rdi,
    by rw [mu]; exact so.good.hdr⟩
  -- The ADX code's, from a state with `a`'s memory.
  have adx : ∀ v : State, v.mem = a.mem → Keep [.rax, .r8, .r9, .r10, .r11] a v → v.mxcsr = a.mxcsr →
      WP isa (adxExp M.mm) v (ExpOut B Z ((k+7)/8) mi N R (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip eb) a) :=
    fun v mv kv xv => by
    have gv : VG.Proof.Bignum.X86_64.Good v B Z ((k+7)/8) mi := ⟨so.good.scr.congr kv.2.2, (kv.gpr (by decide)).trans so.good.rdi,
      by rw [mv]; exact so.good.hdr⟩
    refine WP.mono (phasesCore_ok M h v mi gv (by rw [mv]; exact so.n) (by rw [mv]; exact so.inv)
      (by rw [mv]; exact so.x) (by rw [mv]; exact fa) ((ka.trans kv).mono (by decide)) (by rw [mv]; exact rra) hmx)
      fun d ⟨y, hy, gd, yd, fd, kd, xd⟩ => ⟨y, hy, gd, yd, by rw [← mv]; exact fd, (kv.trans kd).mono (by decide),
        by rw [xd, xv]⟩
  -- The vector code, for a layout of `(k+7)/8` words.
  have ifma : ∀ (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay), PubOk l → l.W = (k+7)/8 → Spec.Rsa.os2ip eb = 65537 →
      ∀ v : State, v.mem = a.mem → Keep [.rax, .r8, .r9, .r10, .r11] a v → v.mxcsr = a.mxcsr →
      WP isa (exp65537 l) v (ExpOut B Z ((k+7)/8) mi N R (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip eb) a) :=
    fun l hl hW he v mv kv xv => by
    have gv : VG.Proof.Bignum.X86_64.Good v B Z ((k+7)/8) mi := ⟨so.good.scr.congr kv.2.2, (kv.gpr (by decide)).trans so.good.rdi,
      by rw [mv]; exact so.good.hdr⟩
    rw [← hW] at gv hZ ⊢
    refine WP.mono (exp65537_ok hl (N := N) (X := Spec.Rsa.os2ip xb) (R := R) gv
      (by rw [mv, hW]; exact so.n) (by rw [mv, hW]; exact so.inv) (by rw [mv, hW]; exact so.x) hZ
      (by rw [mv, hW]; exact rra) h.rlt h.odd (by rw [hW]; exact h.big) he)
      fun d ⟨gd, vd, fd, kd, xd⟩ => ⟨VG.Proof.Bignum.wv d.mem B (VG.Proof.Bignum.slot l.W aY) l.W,
        vd, gd, rfl,
        by rw [← mv]; exact fd, (kv.trans kd).mono (by decide), by rw [xd, xv]⟩
  have hw : (k+7)/8 < 2 ^ 31 := by omega
  refine WP.ite (decide (Spec.Rsa.os2ip eb = 65537)) (by simp [eval, zu]) (fun hb => ?_) (fun _ => adx u mu ku xu)
  have he : Spec.Rsa.os2ip eb = 65537 := by simpa using hb
  refine WP.seq (WP.mono_mx (by decide +kernel) (cmpW_ok 32 gu hZ (by decide) hw) fun u₁ ⟨z₁, m₁, k₁⟩ x₁ => ?_)
  have g₁ : VG.Proof.Bignum.X86_64.Good u₁ B Z ((k+7)/8) mi := ⟨gu.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans gu.rdi, by rw [m₁]; exact gu.hdr⟩
  refine WP.ite (decide ((k+7)/8 = 32)) (by simp [eval, z₁]) (fun hb => ?_) (fun _ => ?_)
  · exact ifma pay2048 (.inl rfl) (of_decide_eq_true hb).symm he u₁ (by rw [m₁, mu]) ((ku.trans k₁).mono (by decide))
      (by rw [x₁, xu])
  refine WP.seq (WP.mono_mx (by decide +kernel) (cmpW_ok 48 g₁ hZ (by decide) hw) fun u₂ ⟨z₂, m₂, k₂⟩ x₂ => ?_)
  have g₂ : VG.Proof.Bignum.X86_64.Good u₂ B Z ((k+7)/8) mi := ⟨g₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans g₁.rdi, by rw [m₂]; exact g₁.hdr⟩
  refine WP.ite (decide ((k+7)/8 = 48)) (by simp [eval, z₂]) (fun hb => ?_) (fun _ => ?_)
  · exact ifma pay3072 (.inr (.inl rfl)) (of_decide_eq_true hb).symm he u₂ (by rw [m₂, m₁, mu])
      (((ku.trans k₁).trans k₂).mono (by decide)) (by rw [x₂, x₁, xu])
  refine WP.seq (WP.mono_mx (by decide +kernel) (cmpW_ok 64 g₂ hZ (by decide) hw) fun u₃ ⟨z₃, m₃, k₃⟩ x₃ => ?_)
  refine WP.ite (decide ((k+7)/8 = 64)) (by simp [eval, z₃]) (fun hb => ?_) (fun _ => ?_)
  · exact ifma pay4096 (.inr (.inr rfl)) (of_decide_eq_true hb).symm he u₃ (by rw [m₃, m₂, m₁, mu])
      ((((ku.trans k₁).trans k₂).trans k₃).mono (by decide)) (by rw [x₃, x₂, x₁, xu])
  · exact adx u₃ (by rw [m₃, m₂, m₁, mu]) ((((ku.trans k₁).trans k₂).trans k₃).mono (by decide))
      (by rw [x₃, x₂, x₁, xu])

theorem rest_eq (M : Mont) :
    PubIfma.rest M.mm = seqs ((wordIn ++ restStepsWith VG.Impl.Rsa.X86_64.Compare8.code) ++
      ([pubExp M.mm] ++ wordOutStepsArr aY)) := rfl

/-- `rest` with `pubExp`: as `FoldedPublic.rest_ok`. -/
theorem rest_ok (M : Mont) {s : State} {B : Addr} {Z k : Nat} {op ep ip : Addr}
    {L : Nat} {eb xb : List Byte} {N R : Nat}
    (h : PdPre s B Z k op ep ip L eb xb N R)
    (hmx : (seqs (phases M)).allInstrs (fun i => !loadsMxcsr i) = true) :
    WP isa (PubIfma.rest M.mm) s fun t => ∃ y : Nat,
      (R % N = 2^(64*((k+7)/8)) * 2^(64*((k+7)/8)) % N →
        y = Spec.Rsa.os2ip xb ^ Spec.Rsa.os2ip eb % N) ∧
      MainPost s t B Z k op (if Spec.Rsa.os2ip xb < N then y else 0)
        (decide (Spec.Rsa.os2ip xb < N)) ∧ t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  rw [rest_eq]
  exact restWith_ok [pubExp M.mm] (by simp) h fun a mi so fa ka rra => pubExp_ok M h a mi so fa ka rra hmx

end VG.Proof.Bignum.X86_64.Ifma.Pub
