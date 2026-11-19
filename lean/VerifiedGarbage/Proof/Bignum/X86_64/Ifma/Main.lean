module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Ws
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Comp
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtBack
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Pre
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtContract
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCode
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.CrtP
public import VerifiedGarbage.Impl.Rsa.X86_64.CrtIfma
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtUnit
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Bignum.Amm52

/-! ### `Bignum.X86_64.Ifma.Post`, which this module and modules that import it used -/

section

/-!
# RSA with AVX512_IFMA on x86-64: after the exponentiations

`post` is `p`'s phase after its exponentiation, in `p`'s workspace:
`R_p² mod p` from `n`'s `R_n² mod n` (`redc`), `m_q R_p mod p` from `q`'s
result, and `h = (m_p - m_q) qInv mod p` (`hTail_ok`, as `pPhase`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- `post` after its start: `m_q` into `aChunk`, `m_q R_p`, `h`. -/
def postRest (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  .block [.mov .rax (.mem (hdr sLink)), .mov .rax (.mem (ws .rax sWsQ)),
      .mov .rsi (.mem (ws .rax (sArr Public.aY))), .mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aChunk)))] ::
    copyWords :: mul aChunk aChunk aXc :: (copyArr aXc aChunk ++
  ((subModArr aT Public.aY aXc ++ loadArr aChunk sQinv sPlen ++ maskArr aChunk ++
    ([mul Public.aY aT aChunk] : List (Prog isa))) ++ ([.block [leave]] : List (Prog isa))))

theorem postP_eq (mul : Nat → Nat → Nat → Prog isa) :
    CrtIfma.postP mul = (([.block [.mov .rdi (.mem (hdr sWsP))]] : List (Prog isa)) ++ CrtIfma.r2X false aXc) ++
      postRest mul := by
  simp only [CrtIfma.postP, postRest, enterP, List.append_assoc, List.cons_append, List.nil_append]

/-- What `post`'s start leaves, from `s` in `n`'s workspace: `p`'s workspace
entered, `R_p²` modulo `p` (when `p ∣ N`) in its `aXc`, its `aY` and mask
kept. -/
abbrev PostHead (s : State) (B : Addr) (Z w : Nat) (mx : BitVec 64) (N X op wx : Nat) (s₁ : State) : Prop :=
  SubCtx s₁ B Z op w wx mx ∧ XVals s₁ B op wx mx X ∧ wv s₁.mem (off B op) (slot wx aXc) wx < X ∧
    (X ∣ N → wv s₁.mem (off B op) (slot wx aXc) wx % X = 2 ^ (64 * wx * 2) % X) ∧
    Frm B [xRange op wx] s.mem s₁.mem ∧
    wv s₁.mem (off B op) (slot wx Public.aY) wx = wv s.mem (off B op) (slot wx Public.aY) wx ∧
    word s₁.mem (off B op) (8 * sMaskX) = word s.mem (off B op) (8 * sMaskX) ∧
    Keep (mmRegs ++ ([.rdi] : List Reg)) s s₁

/-- What `post` leaves. -/
abbrev PostPost (s : State) (B : Addr) (Z w : Nat) (minv mx : BitVec 64) (X oq op wx m1 : Nat) (qib : List Byte)
    (c : Bool) (t : State) : Prop :=
  Good t B Z w minv ∧ WsAt t.mem B op wx mx ∧
    XVals t B op wx mx X ∧ wv t.mem (off B op) (slot wx Public.aY) wx < X ∧
    (c = true → ∃ a b, a % X = m1 * 2 ^ (64 * wx) % X ∧
      b % X = wv s.mem (off B oq) (slot wx Public.aY) wx * 2 ^ (64 * wx) % X ∧ b < X ∧
      wv t.mem (off B op) (slot wx Public.aY) wx * 2 ^ (64 * wx) % X = (a + X - b) % X * Spec.Rsa.os2ip qib % X) ∧
    Frm B (gRanges w ++ [(slot w Public.aX, 8 * (w + 2)), xRange op wx]) s.mem t.mem ∧ Keep mmRegs s t

/-- `post` with its start `c₀` (`hc₀`): with `q`'s result in its `aY`,
`p`'s `aY := h` as `pPhase` leaves it. Only `p`'s workspace changes. -/
theorem postWith_ok (M : Mont) {c₀ : List (Prog isa)} (hc₀ : c₀ ≠ []) {s : State} {B : Addr} {Z w : Nat}
    {minv mx mq : BitVec 64} {N X oq op wx m1 : Nat} {qp : Addr} {qib : List Byte} {c : Bool}
    (hg : Good s B Z w minv) (hw28 : w < 2 ^ 28) (hw2 : w = 2 * wx)
    (hq : word s.mem B (8 * sWsQ) = off B oq) (hwsq : WsAt s.mem B oq wx mq)
    (hhiq : oq + slot wx 8 + wsTab wx ≤ Z)
    (hlo : slot w 8 ≤ op) (hhi : op + slot wx 8 + wsTab wx ≤ oq) (hwx2 : 2 ≤ wx)
    (hXodd : X % 2 = 1)
    (hyl : wv s.mem (off B op) (slot wx Public.aY) wx < X)
    (hyc : X ∣ N → wv s.mem (off B op) (slot wx Public.aY) wx % X = m1 * 2 ^ (64 * wx) % X)
    (hmask : word s.mem (off B op) (8 * sMaskX) = mask c) (hc : c = true → X ∣ N)
    (hqp : word s.mem B (8 * sQinv) = qp) (hql : word s.mem B (8 * sPlen) = BitVec.ofNat 64 qib.length)
    (hqs : Src s B Z qp qib) (hq1 : 1 ≤ qib.length) (hq2 : qib.length < 2 ^ 31) (hqw : (qib.length + 7) / 8 ≤ wx)
    (hqi : c = true → Spec.Rsa.os2ip qib < X)
    (hhead : WP isa (seqs c₀) s (PostHead s B Z w mx N X op wx)) :
    WP isa (seqs (c₀ ++ postRest M.mm)) s (PostPost s B Z w minv mx X oq op wx m1 qib c) := by
  have hs := hg.scr
  have hn := hs.nowrap
  obtain h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  obtain hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  obtain hz : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_using [hhiq, hlo, hhi, hn]
  obtain ho64 : op < 2 ^ 64 := by omega_using [hhiq, hhi, hn, hX8]
  obtain hoL : op + slot wx 8 ≤ 2 ^ 64 := by omega_using [hhiq, hhi, hn]
  obtain hwx : wx ≤ w := by omega_using [hw2]
  obtain hRx : Nat.Coprime (2 ^ (64 * wx)) X := VG.Proof.Bignum.coprime_pow2 hXodd _
  obtain lY := slot_le (w := wx) (show Public.aY < 8 by decide)
  obtain lC := slot_le (w := wx) (show aChunk < 8 by decide)
  obtain hC0 := hdr_lt_slot wx aChunk (show 31 < 32 by decide)
  -- `aXc := R_p²`.
  refine wp_seqs_append hc₀ (by simp [postRest]) (WP.mono hhead fun s₁ ⟨hc₁, hX₁, hlt₁, hv₁, f₁, hY₁, hk₁, k₁⟩ => ?_)
  obtain hb₁ : ∀ d, d + 8 ≤ op → word s₁.mem B d = word s.mem B d := fun d hd => f₁.x_below hd ho64
  obtain hab₁ : ∀ d, op + slot wx 8 + wsTab wx ≤ d → d + 8 ≤ 2 ^ 64 → word s₁.mem B d = word s.mem B d :=
    fun d hd hd' => f₁.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [xRange]; omega_using [lC, hC0, hd]) hd'
  obtain hs₁ := hs.congr k₁.2.2
  have hsP := hc₁.good.scr
  have hdi₁ := hc₁.rdi
  obtain hldq := (hs₁.sub (o := oq) (n := slot wx 8) (by omega_using [hhiq]) (by omega_using [lC])).ld (d := 8 * sArr Public.aY)
    (by unfold sArr Public.aY; omega_using [lC, hC0])
  obtain hqa : word s₁.mem (off B oq) (8 * sArr Public.aY) = off (off B oq) (slot wx Public.aY) := by
    rw [word_off, hab₁ (oq + 8 * sArr Public.aY) (by omega_using [hhi])
        (by unfold sArr Public.aY; omega_using [hhiq, hn, lC, hC0]), ← word_off]
    exact hwsq.hdr.harr Public.aY (by decide)
  -- `m_q` into `aChunk`.
  refine WP.seq (WP.mono (WP.keep [.rax, .rsi, .r12, .rbx] (Q := fun t =>
      t.gpr .rsi = off (off B oq) (slot wx Public.aY) ∧ t.gpr .r12 = BitVec.ofNat 64 wx ∧
      t.gpr .rbx = off (off B op) (slot wx aChunk) ∧ t.mem = s₁.mem)
    (by xrun [State.ea, hdr, ws, hdi₁, hdrOff, hsP.ld (d := 8 * sLink) (by unfold sLink sFn; omega_using [lC, hC0]), hc₁.link,
      hs₁.ld (d := 8 * sWsQ) (by unfold sWsQ sFn; omega_using [hhiq, lC, hC0]),
          hb₁ (8 * sWsQ) (by unfold sWsQ sFn; omega_using [hlo, h8]), hq,
      hldq, hqa, hsP.ld (d := 8 * sW) (by unfold sW; omega_using [lC, hC0]), hc₁.hdr.hw,
      hsP.ld (d := 8 * sArr aChunk) (by unfold sArr aChunk; omega_using [lC, hC0]), hc₁.hdr.harr aChunk (by decide)]) rfl)
    fun s₂ ⟨⟨hsi₂, h12₂, hbx₂, hm₂⟩, k₂⟩ => ?_)
  obtain hs₂ := hs₁.congr k₂.2.2
  obtain hsP₂ := hsP.congr k₂.2.2
  obtain hsi₂' : s₂.gpr .rsi = off B (oq + slot wx Public.aY) := by rw [hsi₂, off_off]
  refine WP.seq (WP.mono (copyWords_ok (S := B) (eS := oq + slot wx Public.aY) (D := off B op) (eD := slot wx aChunk)
    (w := wx) hsi₂' hbx₂ h12₂ (by omega_using [hq1, hqw]) (by omega_using [hw28, hwx]) (by omega_using [hoL, lC])
        (fun j hj => hs₂.ld (by omega_using [hhiq, lY, hj]))
    (fun j hj => hsP₂.st (by omega_using [lC, hj])) (fun j hj b hb => Or.inr (by
      rw [show off B (oq + slot wx Public.aY + 8 * j) = off (off B op) (oq + slot wx Public.aY + 8 * j - op) by
        rw [off_off]; congr 1; omega_using [hhi],
            ofs_off (off B op) (by omega_using [hhiq, hn, lY, hj, hb])]; omega_using [hhi,
            lC]))) fun s₃ ⟨hv₃, _, ho₃, k₃⟩ => ?_)
  rw [hm₂] at ho₃
  obtain hz₁ : (off B op).toNat + slot wx 8 ≤ 2 ^ 64 := by have := hc₁.good.scr.nowrap; omega_using [this]
  obtain hX₃ : XVals s₃ B op wx mx X := hX₁.of_outside ho₃ (by decide) (by decide) (by decide) (by omega_using []) hz₁
  obtain fo₃ : Frm (off B op) [(slot wx aChunk, 8 * wx)] s₁.mem s₃.mem := Frm.of_outside ho₃ (by simp)
  obtain hc₃ : SubCtx s₃ B Z op w wx mx := hc₁.of_frm fo₃ (fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only; omega_using [lC, hC0]) (k₂.trans k₃).2.2 ((k₂.trans k₃).gpr (by decide))
  obtain fx₃ : Frm B [xRange op wx] s₁.mem s₃.mem :=
    fo₃.to_x (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_using [lC, hC0]) hoL (List.mem_singleton_self _)
  obtain hC₃ : wv s₃.mem (off B op) (slot wx aChunk) wx = wv s.mem (off B oq) (slot wx Public.aY) wx := by
    rw [hv₃, hm₂, wv_off]
    exact wv_congr fun i hi => hab₁ _ (by omega_using [hhi]) (by omega_using [hhiq, hn, lY, hi])
  obtain hxc₃ : wv s₃.mem (off B op) (slot wx aXc) wx = wv s₁.mem (off B op) (slot wx aXc) wx := by
    have := slot_sep (w := wx) (show aXc ≠ aChunk by decide)
    have := slot_le (w := wx) (show aXc < 8 by decide)
    exact ho₃.wv (by omega_arith) (by omega_using [hz₁, this])
  -- `aChunk := m_q R_p² R_p^-1 = m_q R_p`.
  refine WP.seq (WP.mono (M.mm_ok (o := aChunk) (a := aChunk) (b := aXc) hc₃.good (Nat.le_refl _) hwx2
    (by omega_using [hw28, hwx]) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hX₃.inv
    (by rw [hX₃.n, hxc₃]; exact hlt₁)) fun s₄₀ ⟨_, hlt₄, hm₄, ha₄, k₄₀⟩ => ?_)
  rw [hX₃.n] at hlt₄ hm₄
  obtain ⟨hc₄₀, hX₄₀, fx₄₀⟩ := hc₃.of_arrays hX₃ ha₄ (by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> decide) k₄₀.2.2 (k₄₀.gpr (by decide)) (by omega_using [hq1, hqw])
  have hz₄ : (off B op).toNat + slot wx 8 ≤ 2 ^ 64 := hz₁
  -- `aXc := aChunk`.
  refine wp_seqs_append (by simp [copyArr]) (by simp [subModArr]) (WP.mono (copyArr_ok hc₄₀.good (Nat.le_refl _)
    (by omega_using [hq1, hqw]) (by omega_using [hw28, hwx]) (o := aXc) (a := aChunk) (by decide) (by decide) (by decide))
    fun s₄ ⟨hv₄c, ho₄c, k₄c⟩ => ?_)
  obtain lX := slot_le (w := wx) (show aXc < 8 by decide)
  obtain hX0 := hdr_lt_slot wx aXc (show 31 < 32 by decide)
  obtain hc₄ := hc₄₀.of_frm (rs := [(slot wx aXc, 8 * wx)]) (Frm.of_outside ho₄c (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only; omega_using [lX, hX0]) k₄c.2.2 (k₄c.gpr (by decide))
  obtain hX₄ : XVals s₄ B op wx mx X := hX₄₀.of_outside ho₄c (by decide) (by decide) (by decide) (by omega_using []) hz₄
  have fx₄ : Frm B [xRange op wx] s₃.mem s₄.mem := fx₄₀.trans
    ((ho₄c.mono (o' := slot wx aXc) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega_using [])).to_x
      (by decide) hoL (List.mem_singleton_self _))
  obtain k₄ := k₄₀.trans k₄c
  obtain hY₄ : wv s₄.mem (off B op) (slot wx Public.aY) wx = wv s.mem (off B op) (slot wx Public.aY) wx := by
    have := slot_sep (w := wx) (show Public.aY ≠ aXc by decide)
    rw [ho₄c.wv (by omega_using [this]) (by omega_using [lY, hz₄]), ha₄.wv_of_not_mem (by decide) (by decide) hz₄]
    have := slot_sep (w := wx) (show Public.aY ≠ aChunk by decide)
    rw [ho₃.wv (by omega_using [this]) (by omega_using [lY, hz₄]), hY₁]
  obtain hM₄ : word s₄.mem (off B op) (8 * sMaskX) = mask c := by
    obtain hmx : 8 * sMaskX + 8 ≤ 8 * 31 + 8 := by unfold sMaskX sFn; omega_using []
    rw [ho₄c.word (.inl (by omega_arith)) (by omega_arith), ha₄.hslot (by decide), ho₃.word (.inl (by omega_arith)) (by omega_arith),
      hk₁]; exact hmask
  obtain hlt₄' : wv s₄.mem (off B op) (slot wx aXc) wx < X := by rw [hv₄c]; exact hlt₄
  obtain f04 : Frm B [xRange op wx] s.mem s₄.mem := (f₁.trans fx₃).trans fx₄
  obtain hb₄ : ∀ d, d + 8 ≤ op → word s₄.mem B d = word s.mem B d := fun d hd => f04.x_below hd ho64
  obtain i04 : InScr B Z s.mem s₄.mem :=
    InScr.of_frm f04 fun r hr => by rw [List.mem_singleton.mp hr]; simp only [xRange]; omega_arith
  -- `h`.
  refine wp_seqs_append (by simp [subModArr]) (by simp) (WP.mono (hTail_ok M hc₄ (by omega_arith) hX₄ hw28 hwx2 hwx
    (by rw [hY₄]; exact hyl) hlt₄' hM₄ (by rw [hb₄ _ (by unfold sQinv sFn; omega_arith)]; exact hqp)
    (by rw [hb₄ _ (by unfold sPlen sFn; omega_arith)]; exact hql)
    (hqs.congrK i04 (((k₁.trans k₂).trans k₃).trans k₄)) hq1 hq2 hqw hqi)
    fun s₅ ⟨hc₅, hX₅, hlt₅, hh₅, fx₅, k₅, _⟩ => ?_)
  refine WP.mono (leaveBack_ok hg hc₅ (f04.trans fx₅) hlo) fun t ⟨hg', hm', k'⟩ => ?_
  obtain kall := ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k'
  refine ⟨hg', by rw [hm']; exact hc₅.ws, ?_, by rw [hm']; exact hlt₅, fun hct => ?_,
    by rw [hm']; exact (f04.trans fx₅).mono fun r hr => by rw [List.mem_singleton.mp hr]; simp,
    ⟨fun r hr => ?_, kall.2⟩⟩
  · rw [show t = { t with mem := s₅.mem } by rw [← hm']]; exact ⟨hX₅.n, hX₅.inv, hX₅.one⟩
  · refine ⟨wv s.mem (off B op) (slot wx Public.aY) wx, wv s₄.mem (off B op) (slot wx aXc) wx,
      hyc (hc hct), ?_, hlt₄', by rw [hm', hh₅ hct, hY₄]⟩
    -- `aXc₁ = R_p²`, so `aXc₄ R_p ≡ m_q R_p²`.
    obtain h1 := hv₁ (hc hct)
    apply VG.Proof.Bignum.mont_cancel hRx
    rw [hv₄c, hm₄, hC₃, hxc₃, Nat.mul_mod, h1, ← Nat.mul_mod, Nat.mul_assoc _ (2 ^ (64 * wx)), ← Nat.pow_add]
    congr 3; omega_arith
  · by_cases h : r = .rdi
    · subst h; rw [hg'.rdi, hg.rdi]
    · exact kall.1 r (by simp only [mmRegs, List.mem_cons, List.mem_append] at hr ⊢; simp_all)

/-- `postP`: `post` with `R_p² mod p` from `pre`'s words from `r2XOff false`
(whose value `V` is it where `n`'s mask `c` is set; where it is clear the
prime is 3). -/
theorem postP_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mx mq : BitVec 64}
    {N X oq op wx m1 V : Nat} {qp : Addr} {qib : List Byte} {c : Bool}
    (hg : Good s B Z w minv) (hw28 : w < 2 ^ 28) (hw2 : w = 2 * wx)
    (hq : word s.mem B (8 * sWsQ) = off B oq) (hwsq : WsAt s.mem B oq wx mq)
    (hhiq : oq + slot wx 8 + wsTab wx ≤ Z)
    (hlo : slot w 8 ≤ op) (hhi : op + slot wx 8 + wsTab wx ≤ oq) (hwx2 : 2 ≤ wx)
    (hsp : word s.mem B (8 * sWsP) = off B op) (hws : WsAt s.mem B op wx mx) (hX : XVals s B op wx mx X)
    (hXodd : X % 2 = 1)
    (hyl : wv s.mem (off B op) (slot wx Public.aY) wx < X)
    (hyc : X ∣ N → wv s.mem (off B op) (slot wx Public.aY) wx % X = m1 * 2 ^ (64 * wx) % X)
    (hmask : word s.mem (off B op) (8 * sMaskX) = mask c) (hc : c = true → X ∣ N)
    (hqp : word s.mem B (8 * sQinv) = qp) (hql : word s.mem B (8 * sPlen) = BitVec.ofNat 64 qib.length)
    (hqs : Src s B Z qp qib) (hq1 : 1 ≤ qib.length) (hq2 : qib.length < 2 ^ 31) (hqw : (qib.length + 7) / 8 ≤ wx)
    (hqi : c = true → Spec.Rsa.os2ip qib < X)
    (hM : word s.mem B (8 * Public.sMask) = mask c) (hp : PreW s B Z (r2XOff false wx) wx V)
    (hc3 : c = false → X = 3) (hV : c = true → V % X = 2 ^ (64 * wx * 2) % X) (hVl : c = true → V < X) :
    WP isa (seqs (CrtIfma.postP M.mm)) s (PostPost s B Z w minv mx X oq op wx m1 qib c) := by
  have hn := hg.scr.nowrap
  obtain hoL : op + slot wx 8 ≤ 2 ^ 64 := by omega_using [hhiq, hhi, hn]
  obtain hwx : wx ≤ w := by omega_using [hw2]
  obtain lY := slot_le (w := wx) (show Public.aY < 8 by decide)
  obtain lC := slot_le (w := wx) (show aXc < 8 by decide)
  obtain hC0 := hdr_lt_slot wx aXc (show 31 < 32 by decide)
  obtain sYC := slot_sep (w := wx) (show Public.aY ≠ aXc by decide)
  obtain hmx : 8 * sMaskX + 8 ≤ 8 * 31 + 8 := by unfold sMaskX sFn; omega_using []
  rw [postP_eq]
  refine postWith_ok M (by simp) hg hw28 hw2 hq hwsq hhiq hlo hhi hwx2 hXodd hyl hyc hmask hc hqp hql hqs hq1 hq2 hqw hqi ?_
  refine wp_seqs_append (by simp) (by simp [CrtIfma.r2X, CrtIfma.r2XBlk])
    (WP.mono (enter_ok hg hlo (by omega_using [hhiq, hhi]) (by decide) hsp hws hX) fun s₁ ⟨hc₁, hX₁, hm₁, k₁⟩ => ?_)
  obtain hp₁ : PreW s₁ B Z (r2XOff false wx) wx V :=
    hp.congr (fun x _ => by rw [hm₁]) (k₁.gpr (by decide)) k₁.2.1 k₁.2.2
  refine WP.mono (r2X_ok (j := aXc) (c := c) (by decide) hc₁ hwx2 hwx (by omega_using [hw28]) (by rw [hm₁]; exact hM) hp₁)
    fun s₂ ⟨hc₂, hv₂, f₂, k₂⟩ => ?_
  obtain ho₂ : Outside (off B op) (slot wx aXc) (8 * (wx + 2)) s₁.mem s₂.mem := fun x hx =>
    f₂ x fun r hr => by rw [List.mem_singleton.mp hr]; exact hx
  rw [hm₁] at f₂ ho₂
  obtain hz₁ : (off B op).toNat + slot wx 8 ≤ 2 ^ 64 := by have := hc₁.good.scr.nowrap; omega_using [this]
  refine ⟨hc₂, hX₁.of_outside (by rw [hm₁]; exact ho₂) (by decide) (by decide) (by decide) (Nat.le_refl _) hz₁,
    ?_, fun _ => ?_, f₂.to_x (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_using [lC, hC0]) hoL
      (List.mem_singleton_self _),
    ho₂.wv (by omega_using [sYC]) (by omega_using [lY, hz₁]),
    f₂.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_using [hC0, hmx]) (by omega_using [hz₁, hmx]),
    (k₁.trans k₂).mono (by decide)⟩
  · rw [hv₂]
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte]; rw [hc3 rfl]; decide
    · simp only [↓reduceIte]; exact hVl rfl
  · rw [hv₂]
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hc3 rfl, two_pow_mod_three]
    · simp only [↓reduceIte]
      exact hV rfl

end VG.Proof.Bignum.X86_64

end

end

/-! ### `Bignum.X86_64.Ifma.Branch`, which only this module used -/

section

/-!
# RSA with AVX512_IFMA on x86-64, any size: the IFMA branch

From the checks (`CrtReady`) of a modulus of
`2 W` words and primes of `W`, `pre`, `ifma` and `post` leave what `qPart`
and `pPart` leave (`PDone`), and MXCSR's bits 15:0.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64 (NSafe nsafe_word above_nsafe preRanges_nsafe APost exists_mont')

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- After `pre` and `ifma`: `q`'s result `C^dq mod q` and `p`'s `C^dp R_p`. -/
structure IDone (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s t : State) (B : Addr) (Z w op oq a : Nat) (minv mp mq : BitVec 64) (N C P Q : Nat)
    (dpp dqp qip : Addr) (pl ql : Nat) (dpb dqb : List Byte) (Mk : Bool) : Prop where
  good : VG.Proof.Bignum.X86_64.Good t B Z w minv
  nv : NVals t B w minv N
  msk : word t.mem B (8 * Public.sMask) = mask Mk
  im : IMem l t.mem B w op oq a minv mp mq (mask Mk) (if Mk then P else 3) (if Mk then Q else 3) dpp dqp pl ql
  qlt : wv t.mem (off B oq) (slot l.W Public.aY) l.W < if Mk then Q else 3
  qval : Mk = true → wv t.mem (off B oq) (slot l.W Public.aY) l.W = C ^ Spec.Rsa.os2ip dqb % Q
  plt : wv t.mem (off B op) (slot l.W Public.aY) l.W < if Mk then P else 3
  pval : Mk = true → wv t.mem (off B op) (slot l.W Public.aY) l.W % P = C ^ Spec.Rsa.os2ip dpb * 2 ^ (64 * l.W) % P
  qi : word t.mem B (8 * sQinv) = qip
  hfix : HFix B s.mem t.mem
  iscr : InScr B Z s.mem t.mem
  keep : Keep mmRegs s t

theorem ifmaR_ge {op oq a : Nat} (hpq : op ≤ oq) (hqa : oq ≤ a) : ∀ r ∈ ifmaR l op oq a, op ≤ r.1 := by
  simp only [ifmaR, shiftRanges, k1Ranges, resRanges, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only <;> omega_arith

/-- `ifma`, after `pre`. -/
theorem branchA2_ok (hl : LayOk l) {s t₀ s₁ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (_hw32 : (k + 7) / 8 = 2 * l.W) (hpl : wsWords pl = l.W) (hql : wsWords ql = l.W)
    (hZa : offQ ((k + 7) / 8) pl + slot l.W 8 + wsTab l.W + 2 * l.D + 8 ≤ Z)
    (hA : APost t₀ s₁ B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) l.W minv mp mq
      (Spec.Rsa.os2ip nb) (if Mk then Spec.Rsa.os2ip pb else 3) (if Mk then Spec.Rsa.os2ip qb else 3)
      (Spec.Rsa.os2ip xb)) :
    WP isa (seqs (ifma l)) s₁ fun t =>
      IDone l s t B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl)
        (offQ ((k + 7) / 8) pl + slot l.W 8 + wsTab l.W) minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) dpp dqp qip pl ql dpb dqb Mk ∧
      t.mxcsr = s₁.mxcsr := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  have hk1 := h.k1
  have hpl1 := h.pl1
  have hql1 := h.ql1
  have hZq := h.z
  generalize Spec.Rsa.os2ip nb = N at *
  generalize Spec.Rsa.os2ip xb = C at *
  generalize Spec.Rsa.os2ip pb = P at *
  generalize Spec.Rsa.os2ip qb = Q at *
  generalize Spec.Rsa.os2ip qib = QI at *
  obtain ⟨hMk', hP', hQ'⟩ := mask_facts hMk hodd hPN hQN
  have hn := hr.good.scr.nowrap
  obtain h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  obtain h16 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  obtain hT : wsTab l.W = 256 * (l.W + 2) := by unfold wsTab tabBytes; omega_using []
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨hDb1, hDb2⟩ := hl.D_bounds
  obtain ⟨hW1, hW2⟩ := W_bounds hl
  have hEW : l.E = 8 * l.W := rfl
  obtain hpl' : pl ≤ l.E := by unfold wsWords at hpl; omega_using [hpl, hEW]
  obtain hql' : ql ≤ l.E := by unfold wsWords at hql; omega_using [hql, hEW]
  have hop : offP ((k + 7) / 8) = slot ((k + 7) / 8) 8 := rfl
  obtain hoq : offQ ((k + 7) / 8) pl = slot ((k + 7) / 8) 8 + slot l.W 8 + wsTab l.W := by
    unfold offQ; rw [hpl]
  rw [hql] at hZq
  have pws := hr.pws
  have pxv := hr.pxv
  have qws := hr.qws
  have qxv := hr.qxv
  rw [hpl] at pws pxv
  rw [hql] at qws qxv
  have hh₀ : ∀ i < 32, hFixed i = true → word t₀.mem B (8 * i) = word s.mem B (8 * i) := hr.hfix
  obtain ⟨hg₁, hN₁, rp, rq, f₁, k₁, mk₁⟩ := hA
  obtain ns₁ := preRanges_nsafe (w := (k + 7) / 8) (wp := l.W) (wq := l.W) (Nat.le_refl (offP ((k + 7) / 8)))
    (show slot ((k + 7) / 8) 8 ≤ offQ ((k + 7) / 8) pl by rw [hoq]; omega_using [])
  obtain hz : slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega_arith
  obtain hpr : ∀ r ∈ preRanges ((k + 7) / 8) (offP ((k + 7) / 8)) l.W (offQ ((k + 7) / 8) pl) l.W,
      r.1 + r.2 ≤ offQ ((k + 7) / 8) pl + slot l.W 8 + wsTab l.W := fun r hr => by
    simp only [preRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with hr | rfl | rfl | rfl
    · have := (gRanges_lt _ r hr).2; rw [hoq]; omega_using [this]
    · have := slot_le (w := (k + 7) / 8) (show Public.aX < 8 by decide); rw [hoq]; simp only; omega_using [this]
    · simp only [xRange]; omega_using [hT]
    · simp only [xRange]; rw [hoq, hop]; omega_using [hT]
  obtain i₀₁ : InScr B Z t₀.mem s₁.mem := InScr.of_frm f₁ fun r hr => by have := hpr r hr; omega_using [hZq, this]
  obtain hb₁ : ∀ i < 32, i ≠ Crt.sD → i ≠ Public.sCnt → word s₁.mem B (8 * i) = word t₀.mem B (8 * i) :=
    fun i hi h1 h2 => nsafe_word f₁ ns₁ hi h1 h2
  obtain hf₁ : ∀ i < 32, hFixed i = true → word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi hf => by
    obtain h1 : i ≠ Crt.sD := by rintro rfl; revert hf; decide
    obtain h2 : i ≠ Public.sCnt := by rintro rfl; revert hf; decide
    rw [hb₁ i hi h1 h2, hh₀ i hi hf]
  obtain kk₁ := hr.keep.trans k₁
  obtain ip : IPre l s₁.mem B ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) minv mp mq (mask Mk)
      (if Mk then P else 3) (if Mk then Q else 3) dpp dqp dpb.length dqb.length :=
    ⟨hg₁.hdr, by rw [hb₁ _ (by decide) (by decide) (by decide)]; exact hr.wsP,
      by rw [hb₁ _ (by decide) (by decide) (by decide)]; exact hr.wsQ, rp.ws, rq.ws, rp.x.n, rp.x.inv, rp.x.one,
      rq.x.n, rq.x.inv, rq.x.one, mk₁.trans hr.pmask, by rw [hf₁ _ (by decide) (by decide)]; exact h.hDp,
      by rw [hf₁ _ (by decide) (by decide), h.dpl]; exact h.hPl, by rw [hf₁ _ (by decide) (by decide)]; exact h.hDq,
      by rw [hf₁ _ (by decide) (by decide), h.dql]; exact h.hQl⟩
  -- `ifma`.
  refine WP.mono (ifma_ok hl (K := (if Mk then P else 3) ∣ N ∧ (if Mk then Q else 3) ∣ N) (wp := l.W) hg₁.scr hg₁.rdi
    ip (Nat.le_refl _) (by rw [hoq, hop]) rfl (by omega_using [hZa]) rfl hP'.2 hQ'.2 rp.ylt rq.ylt rp.clt rq.clt
    (fun hK => rp.cv hK.1) (fun hK => rq.cv hK.2) (fun hK => rp.yv hK.1) (fun hK => rq.yv hK.2)
    (h.dp.congrK (hr.iscr.trans i₀₁) kk₁) (h.dq.congrK (hr.iscr.trans i₀₁) kk₁) (by rw [h.dpl]; exact hpl1)
    (by rw [h.dpl]; exact hpl') (by rw [h.dql]; exact hql1) (by rw [h.dql]; exact hql'))
    fun t ⟨m₂, qlt, qv, plt, pv, f₂, d₂, k₂, mx₂⟩ => ?_
  obtain hge : ∀ r ∈ [(offP ((k + 7) / 8) + 8 * sIfma, 8), (offQ ((k + 7) / 8) pl + 8 * sIfma, 8)] ++
      ifmaR l (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) (offQ ((k + 7) / 8) pl + slot l.W 8 + wsTab l.W),
      offP ((k + 7) / 8) ≤ r.1 := fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only; omega_using []
      · simp only; rw [hoq, hop]; omega_using []
    · exact ifmaR_ge (by rw [hoq, hop]; omega_using []) (by omega_using []) r hr
  obtain hlZ : ∀ r ∈ [(offP ((k + 7) / 8) + 8 * sIfma, 8), (offQ ((k + 7) / 8) pl + 8 * sIfma, 8)] ++
      ifmaR l (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) (offQ ((k + 7) / 8) pl + slot l.W 8 + wsTab l.W),
      r.1 + r.2 ≤ Z := fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have hZa' := hZa
      rw [hoq] at hZa'
      rcases hr with rfl | rfl
      · simp only [sIfma, sFn]; rw [hop]; omega_using [o10, hW1, hEW, hZa', (lay_P hl.amm).1, (lay_P hl.amm).2.1, (lay_P hl.amm).2.2.1]
      · simp only [sIfma, sFn]; rw [hoq]; omega_using [o10, hW1, hEW, hZa', (lay_P hl.amm).1, (lay_P hl.amm).2.1, (lay_P hl.amm).2.2.1]
    · have := ifmaR_le (by rw [hoq, hop]) (Nat.le_refl _) r hr; omega_using [hZa, this]
  obtain hb₂ : ∀ d, d + 8 ≤ offP ((k + 7) / 8) → word t.mem B d = word s₁.mem B d := fun d hd =>
    word_below_frm f₂ hge hd (by omega_using [hop, hz])
  obtain hMK : Mk = true → (if Mk then P else 3) ∣ N ∧ (if Mk then Q else 3) ∣ N := fun hm => by
    obtain ⟨_, hpq, _⟩ := hMk' hm
    simp only [hm, ↓reduceIte]
    exact ⟨⟨Q, hpq.symm⟩, ⟨P, by rw [← hpq, Nat.mul_comm]⟩⟩
  rw [h.dpl, h.dql] at m₂
  refine ⟨⟨⟨hg₁.scr.congr k₂.2.2, d₂, m₂.nh⟩, hN₁.of_nsafe f₂ (above_nsafe (Nat.le_refl _) hge) hz (by omega_using [hk1]),
    by rw [hb₂ _ (by unfold Public.sMask sFn; omega_using [h8, hop]), hb₁ _ (by decide) (by decide) (by decide)]; exact hr.msk,
    m₂, qlt, fun hm => ?_, plt, fun hm => ?_,
    by rw [hb₂ _ (by unfold sQinv sFn; omega_using [h8, hop]), hf₁ _ (by decide) (by decide)]; exact h.hQi,
    fun i hi hf => by rw [hb₂ _ (by have := hdr_lt_slot ((k + 7) / 8) 8 hi; omega_using [hop, this]), hf₁ i hi hf],
    (hr.iscr.trans i₀₁).trans (InScr.of_frm f₂ hlZ), (kk₁.trans k₂).mono (by decide)⟩,
    mx₂⟩
  · have := qv (hMK hm); simp only [hm, ↓reduceIte] at this; exact this
  · have := pv (hMK hm); simp only [hm, ↓reduceIte] at this; exact this


theorem primeWords_eq (len : Nat) : Spec.Rsa.primeWords len = wsWords len := by
  unfold Spec.Rsa.primeWords Spec.Rsa.modulusWords wsWords; rfl

/-- A prime's `R_X² mod X` from `pre`, as `prepP` and `postP` take it: for the
prime `M ? X : 3`. -/
theorem preV_mask {X wx : Nat} {Mk : Bool} (hX : Mk = true → 0 < X) :
    (Mk = true → 2 ^ (128 * wx) % X % (if Mk then X else 3) = 2 ^ (64 * wx * 2) % (if Mk then X else 3)) ∧
      (Mk = true → 2 ^ (128 * wx) % X < if Mk then X else 3) := by
  refine ⟨fun hm => ?_, fun hm => ?_⟩
  · simp only [hm, ↓reduceIte]; rw [Nat.mod_mod, show 128 * wx = 64 * wx * 2 by omega_using []]
  · simp only [hm, ↓reduceIte]; exact Nat.mod_lt _ (hX hm)

/-- `preP`, from the checks, for the layout `l` of the key's sizes, with
`R_p² mod p` and `R_q² mod q` in `pre` after `n`'s values. -/
theorem branchA1P_ok (hl : LayOk l) (M : Mont) {s t₀ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (hw32 : (k + 7) / 8 = 2 * l.W) (hpl : wsWords pl = l.W) (hql : wsWords ql = l.W)
    (hpP : PreW t₀ B Z (2 * ((k + 7) / 8)) (Spec.Rsa.primeWords pl)
      (2 ^ (128 * Spec.Rsa.primeWords pl) % Spec.Rsa.os2ip pb))
    (hpQ : PreW t₀ B Z (2 * ((k + 7) / 8) + Spec.Rsa.primeWords pl) (Spec.Rsa.primeWords ql)
      (2 ^ (128 * Spec.Rsa.primeWords ql) % Spec.Rsa.os2ip qb))
    (hpre : (seqs (CrtIfma.preP M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    WP isa (seqs (CrtIfma.preP M.mm)) t₀ fun s₁ =>
      APost t₀ s₁ B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) l.W minv mp mq
        (Spec.Rsa.os2ip nb) (if Mk then Spec.Rsa.os2ip pb else 3) (if Mk then Spec.Rsa.os2ip qb else 3)
        (Spec.Rsa.os2ip xb) ∧ s₁.mxcsr = t₀.mxcsr := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  have hk1 := h.k1
  have hpl1 := h.pl1
  have hql1 := h.ql1
  have hZq := h.z
  rw [primeWords_eq, hpl, hw32, show 2 * (2 * l.W) = r2XOff false l.W by simp only [r2XOff, Bool.false_eq_true, ↓reduceIte]; omega_using []] at hpP
  rw [primeWords_eq, primeWords_eq, hpl, hql, hw32, show 2 * (2 * l.W) + l.W = r2XOff true l.W by
    simp only [r2XOff, ↓reduceIte]; omega_using []] at hpQ
  generalize Spec.Rsa.os2ip nb = N at *
  generalize Spec.Rsa.os2ip xb = C at *
  generalize Spec.Rsa.os2ip pb = P at *
  generalize Spec.Rsa.os2ip qb = Q at *
  generalize Spec.Rsa.os2ip qib = QI at *
  obtain ⟨hMk', hP', hQ'⟩ := mask_facts hMk hodd hPN hQN
  obtain hP0 : Mk = true → 0 < P := fun hm => by
    obtain ⟨_, hpq, _⟩ := hMk' hm
    exact Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.zero_mul] at hpq; omega_using [hpq, hodd]
  obtain hQ0 : Mk = true → 0 < Q := fun hm => by
    obtain ⟨_, hpq, _⟩ := hMk' hm
    exact Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at hpq; omega_using [hpq, hodd]
  have hn := hr.good.scr.nowrap
  obtain h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  obtain h16 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  obtain hT : wsTab l.W = 256 * (l.W + 2) := by unfold wsTab tabBytes; omega_using []
  obtain ⟨hW1, hW2⟩ := W_bounds hl
  obtain hoq : offQ ((k + 7) / 8) pl = slot ((k + 7) / 8) 8 + slot l.W 8 + wsTab l.W := by
    unfold offQ; rw [hpl]
  rw [hql] at hZq
  have pws := hr.pws
  have pxv := hr.pxv
  have qws := hr.qws
  have qxv := hr.qxv
  rw [hpl] at pws pxv
  rw [hql] at qws qxv
  exact WP.mono_mx hpre
    (preP_ok M (wp := l.W) (c := Mk) hr.good (by omega_using [hw32, hW2]) (Nat.le_refl _) (by rw [hoq])
      (by omega_using [hZq]) (by omega_using [hW1]) (by omega_using [hw32]) hr.wsP hr.wsQ pws qws hr.nv hr.xm
      pxv hP'.1 hP'.2 qxv hQ'.1 hQ'.2 hr.msk hpP hpQ (fun hm => by simp [hm]) (preV_mask hP0).1
      (fun hm => by simp [hm]) (preV_mask hQ0).1)
    fun s₁ hA mx₁ => ⟨hA, mx₁⟩

/-- `postP`, after `preP` and `ifma`: what `pPart` leaves, with `R_p² mod p` in
`pre` after `n`'s values. -/
theorem branchBP_ok (hl : LayOk l) (M : Mont) {s t₁ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hd : IDone l s t₁ B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl)
        (offQ ((k + 7) / 8) pl + slot l.W 8 + wsTab l.W) minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) dpp dqp qip pl ql dpb dqb Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (hw32 : (k + 7) / 8 = 2 * l.W) (hpl : wsWords pl = l.W) (hql : wsWords ql = l.W)
    (hpP : PreW t₁ B Z (2 * ((k + 7) / 8)) (Spec.Rsa.primeWords pl)
      (2 ^ (128 * Spec.Rsa.primeWords pl) % Spec.Rsa.os2ip pb))
    (hpost : (seqs (CrtIfma.postP M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    WP isa (seqs (CrtIfma.postP M.mm)) t₁ fun t => PDone s t B Z ((k + 7) / 8) pl ql minv mp mq
      (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib) dpb dqb Mk ∧
      t.mxcsr = t₁.mxcsr := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  have hk1 := h.k1
  have hpl1 := h.pl1
  have hql1 := h.ql1
  have hZq := h.z
  have hqil := h.qil
  rw [primeWords_eq, hw32, show 2 * (2 * l.W) = r2XOff false (wsWords pl) by
    simp only [r2XOff, Bool.false_eq_true, ↓reduceIte]; omega_using [hpl]] at hpP
  generalize Spec.Rsa.os2ip nb = N at *
  generalize Spec.Rsa.os2ip xb = C at *
  generalize Spec.Rsa.os2ip pb = P at *
  generalize Spec.Rsa.os2ip qb = Q at *
  generalize hQIe : Spec.Rsa.os2ip qib = QI at *
  obtain ⟨hMk', hP', hQ'⟩ := mask_facts hMk hodd hPN hQN
  obtain hP0 : Mk = true → 0 < P := fun hm => by
    obtain ⟨_, hpq, _⟩ := hMk' hm
    exact Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.zero_mul] at hpq; omega_using [hpq, hodd]
  have hn := hd.good.scr.nowrap
  obtain h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  obtain ⟨hW1, hW2⟩ := W_bounds hl
  have hEW : l.E = 8 * l.W := rfl
  obtain hpl' : pl ≤ l.E := by unfold wsWords at hpl; omega_using [hpl, hEW]
  have hop : offP ((k + 7) / 8) = slot ((k + 7) / 8) 8 := rfl
  have hoq : offQ ((k + 7) / 8) pl = slot ((k + 7) / 8) 8 + slot (wsWords pl) 8 + wsTab (wsWords pl) := rfl
  obtain hW8 : 256 ≤ slot (wsWords pl) 8 := by unfold slot hdrBytes; omega_using []
  have hm := hd.im
  -- The multiplier of `R_p` in `p`'s `aY`: `C^dp` for a key that passed the checks.
  obtain ⟨x0, hx0⟩ := exists_mont' (VG.Proof.Bignum.coprime_pow2 hP'.2 (64 * wsWords pl)) hP'.1
    (wv t₁.mem (off B (offP ((k + 7) / 8))) (slot (wsWords pl) Public.aY) (wsWords pl))
  refine WP.mono_mx hpost (postP_ok M (wx := wsWords pl) (op := offP ((k + 7) / 8))
    (oq := offQ ((k + 7) / 8) pl) (mx := mp) (mq := mq) (X := if Mk then P else 3)
    (m1 := if Mk then C ^ Spec.Rsa.os2ip dpb else x0) (c := Mk) (qib := qib) hd.good (by omega_using [hw32, hW2])
    (by rw [hpl]; omega_using [hw32]) hm.wsQ (by rw [hpl]; exact hm.qws) (by have := hZq; rw [hql] at this; rw [hpl]; exact this)
    (Nat.le_refl _) (by rw [hoq, hop]) (by rw [hpl]; omega_arith) hm.wsP
    (by rw [hpl]; exact hm.pws) (by rw [hpl]; exact ⟨hm.pn, hm.pinv, hm.pone⟩) hP'.2
    (by rw [hpl]; exact hd.plt) (fun _ => ?_) hm.pmk
    (fun hm' => by obtain ⟨_, hpq, _⟩ := hMk' hm'; simp only [hm', ↓reduceIte]; exact ⟨Q, hpq.symm⟩) hd.qi
    (by rw [hqil]; exact hm.pl) (h.qi.congrK hd.iscr hd.keep) (by rw [hqil]; exact hpl1) (by rw [hqil]; omega_using [hW2, hEW, hpl'])
    (by rw [hqil, hpl]; omega_using [hEW, hpl'])
    (fun hm' => by obtain ⟨_, _, hqi⟩ := hMk' hm'; simp only [hm', ↓reduceIte, hQIe]; exact hqi)
    hd.msk hpP (fun hm' => by simp [hm']) (preV_mask hP0).1 (preV_mask hP0).2)
    fun t ⟨hg', hws', hX', hlt', hh', f', k'⟩ mx' => ?_
  · by_cases hmk : Mk
    · simp only [hmk, ↓reduceIte]
      rw [hpl]
      exact hd.pval hmk
    · simp only [hmk, Bool.false_eq_true, ↓reduceIte] at hx0 ⊢
      exact hx0
  obtain hz : slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega_using [hZq, hn, hoq]
  obtain ns : NSafe ((k + 7) / 8) (gRanges ((k + 7) / 8) ++
      [(slot ((k + 7) / 8) Public.aX, 8 * ((k + 7) / 8 + 2)), xRange (offP ((k + 7) / 8)) (wsWords pl)]) :=
    fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact .inl hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inr (.inl rfl)
        · exact .inr (.inr (by simp only [xRange]; omega_using [hop]))
  obtain hqZ : offQ ((k + 7) / 8) pl + slot l.W 8 ≤ 2 ^ 64 := by
    have := hZq; rw [hql] at this; omega_using [hn, this]
  obtain h16 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  obtain hqk : ∀ d, offQ ((k + 7) / 8) pl ≤ d → d + 8 ≤ 2 ^ 64 → word t.mem B d = word t₁.mem B d :=
    fun d hd' hd'' => f'.word_eq (fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact .inr (by have := (gRanges_lt _ r hr).2; rw [hoq] at hd'; omega_using [hd', this])
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · have := slot_le (w := (k + 7) / 8) (show Public.aX < 8 by decide); simp only; rw [hoq] at hd'; omega_using [hd', this]
        · simp only [xRange]; rw [hoq] at hd'; omega_using [hop, hW8, hd']) hd''
  obtain hqv : ∀ d n, d + 8 * n ≤ slot l.W 8 → wv t.mem (off B (offQ ((k + 7) / 8) pl)) d n =
      wv t₁.mem (off B (offQ ((k + 7) / 8) pl)) d n := fun d n hdn => by
    rw [wv_off, wv_off]; exact wv_congr fun i hi => hqk _ (by omega_using []) (by omega_using [hqZ, hdn, hi])
  obtain hY8 := slot_le (w := l.W) (show Public.aY < 8 by decide)
  obtain hN8 := slot_le (w := l.W) (show Public.aN < 8 by decide)
  refine ⟨⟨hg', by rw [nsafe_word f' ns (by decide) (by decide) (by decide)]; exact hd.msk,
    by rw [nsafe_word f' ns (by decide) (by decide) (by decide)]; exact hm.wsP,
    by rw [nsafe_word f' ns (by decide) (by decide) (by decide)]; exact hm.wsQ, hws',
    (show WsAt t₁.mem B (offQ ((k + 7) / 8) pl) (wsWords ql) mq by rw [hql]; exact hm.qws).of_words fun i hi => by
      rw [word_off, word_off]; exact hqk _ (by omega_using []) (by omega_using [hqZ, h16, hi]),
    by rw [hql, hqv _ _ (by omega_using [hN8])]; exact hm.qn, by rw [hql, hqv _ _ (by omega_using [hY8])]; exact hd.qlt,
    fun hmk => by rw [hql, hqv _ _ (by omega_using [hY8])]; exact hd.qval hmk, hlt', fun hmk => ?_,
    hd.hfix.trans fun i hi hf => by
      obtain h1 : i ≠ Crt.sD := by rintro rfl; revert hf; decide
      obtain h2 : i ≠ Public.sCnt := by rintro rfl; revert hf; decide
      exact nsafe_word f' ns hi h1 h2,
    hd.iscr.trans (InScr.of_frm f' fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · have := (gRanges_lt _ r hr).2; omega_using [hZq, hoq, this]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · have := slot_le (w := (k + 7) / 8) (show Public.aX < 8 by decide); simp only; omega_using [hZq, hoq, this]
        · simp only [xRange]; rw [hoq] at hZq; rw [hop]; omega_using [hZq, hW8]),
    (hd.keep.trans k').mono (by decide)⟩, mx'⟩
  obtain ⟨a, b, ha, hb, hbP, hh⟩ := hh' hmk
  simp only [hmk, ↓reduceIte] at ha hb hbP hh
  rw [show wv t₁.mem (off B (offQ ((k + 7) / 8) pl)) (slot (wsWords pl) Public.aY) (wsWords pl) =
    wv t₁.mem (off B (offQ ((k + 7) / 8) pl)) (slot l.W Public.aY) l.W by rw [hpl], hd.qval hmk] at hb
  exact ⟨a, b, ha, hb, hbP, by rw [hh, hQIe]⟩

end VG.Proof.Bignum.X86_64.Ifma

end

end


/-!
# RSA with AVX512_IFMA on x86-64, any size: the computation

`main` runs `vg_rsa_private_crt`'s
front, then the IFMA branch of the first layout whose sizes the key has
(`branch`, `sizes`), the CRT one if none, and its finish (`main_ok`); `code`
writes `privateCrt` of its inputs (`code_correct`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64.CrtIfma (Lay lay2048 lay2048z lay3072 lay4096 sizes ifma)
open VG.Proof.Bignum.X86_64 (ofNat_eq_iff CrtReady.of_regs)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- `(len + 7) / 8 = v`, for the workspace of a prime of `len` bytes. -/
theorem sz_iff {n v : Nat} (hn : n < 2 ^ 60) (hv : v < 2 ^ 31) :
    ((BitVec.ofNat 64 n + 7) >>> 3 ^^^ BitVec.ofNat 64 v = 0#64) ↔ (n + 7) / 8 = v := by
  obtain h7 : ((BitVec.ofNat 64 n + 7) >>> 3).toNat = (n + 7) / 8 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      show (7 : BitVec 64).toNat = 7 from rfl, Nat.mod_eq_of_lt (a := n) (by omega_arith),
      Nat.mod_eq_of_lt (a := n + 7) (by omega_arith)]
  rw [BitVec.xor_eq_zero_iff, ← BitVec.toNat_inj, h7, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := v) (by omega_arith)]

/-- `sizes l`: ZF exactly if `n` has `2 W` words and `p` and `q` `W`. -/
theorem sizes_ok (hl : LayOk l) {t : State} {B : Addr} {Z w pl ql : Nat} {minv : BitVec 64}
    (hg : VG.Proof.Bignum.X86_64.Good t B Z w minv) (hpl : word t.mem B (8 * sPlen) = BitVec.ofNat 64 pl)
    (hql : word t.mem B (8 * sQlen) = BitVec.ofNat 64 ql) (hZ : 8 * 32 ≤ Z) (hw : w < 2 ^ 64)
    (hpl' : pl < 2 ^ 60) (hql' : ql < 2 ^ 60) :
    WP isa (.block (sizes l)) t fun t' =>
      t'.zf = some (decide (w = 2 * l.W ∧ (pl + 7) / 8 = l.W ∧ (ql + 7) / 8 = l.W)) ∧ t'.mem = t.mem ∧
        Keep [.rax, .rdx] t t' := by
  have hs := hg.scr
  have hn := hs.nowrap
  obtain ⟨hW1, hW2⟩ := W_bounds hl
  obtain h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  obtain hl' : ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega_arith)
  obtain sx7 : BitVec.signExtend 64 (7 : BitVec 32) = 7 := by decide
  obtain sxW := VG.Proof.Bignum.X86_64.AmmSym.se_ofNat (show l.W < 2 ^ 31 by omega_arith)
  obtain sx2W := VG.Proof.Bignum.X86_64.AmmSym.se_ofNat (show 2 * l.W < 2 ^ 31 by omega_arith)
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t' =>
    t'.zf = some (decide (w = 2 * l.W ∧ (pl + 7) / 8 = l.W ∧ (ql + 7) / 8 = l.W)) ∧ t'.mem = t.mem) (by
      xrun [sizes, State.ea, hdr, hg.rdi, hdrOff, hl' sW (by decide), hl' sPlen (by decide),
        hl' sQlen (by decide), hg.hdr.hw, hpl, hql, sxW, sx2W]
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, show (0 : BitVec 64) = 0#64 from rfl,
        BitVec.or_eq_zero_iff, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff,
        ofNat_eq_iff hw (by omega_arith), sx7, sz_iff hpl' (by omega_arith), sz_iff hql' (by omega_arith), and_assoc]) rfl)
    fun t' ⟨⟨a, b⟩, k⟩ => ⟨a, b, k⟩

/-- The IFMA area fits in the working space the contract asks for. -/
theorem ifmaZ_of (hl : LayOk l) {Z k pl : Nat} (hzk : 128 * k ≤ Z) (hw : (k + 7) / 8 = 2 * l.W)
    (hp : wsWords pl = l.W) : offQ ((k + 7) / 8) pl + slot l.W 8 + wsTab l.W + 2 * l.D + 8 ≤ Z := by
  rcases hl with rfl | rfl | rfl | rfl <;>
    simp only [VG.Impl.Rsa.X86_64.CrtIfma.lay2048, VG.Impl.Rsa.X86_64.CrtIfma.lay3072,
      VG.Impl.Rsa.X86_64.CrtIfma.lay4096, VG.Impl.Rsa.X86_64.CrtIfma.lay2048z] at hw hp ⊢ <;>
    unfold offQ slot wsWords hdrBytes wsTab tabBytes at * <;>
    simp only [VG.Impl.Rsa.X86_64.CrtIfma.Lay.D, VG.Impl.Rsa.X86_64.CrtIfma.Lay.oFin,
      VG.Impl.Rsa.X86_64.CrtIfma.Lay.oV, VG.Impl.Rsa.X86_64.CrtIfma.Lay.oK1, VG.Impl.Rsa.X86_64.CrtIfma.Lay.oE,
      VG.Impl.Rsa.X86_64.CrtIfma.Lay.oTab, VG.Impl.Rsa.X86_64.CrtIfma.Lay.oS, VG.Impl.Rsa.X86_64.CrtIfma.Lay.oX,
      VG.Impl.Rsa.X86_64.CrtIfma.Lay.oY, VG.Impl.Rsa.X86_64.CrtIfma.Lay.NB,
      VG.Impl.Rsa.X86_64.CrtIfma.Lay.T, VG.Impl.Rsa.X86_64.CrtIfma.Lay.XE, VG.Impl.Rsa.X86_64.CrtIfma.Lay.P,
      VG.Impl.Rsa.X86_64.CrtIfma.Lay.ND, VG.Impl.Rsa.X86_64.CrtIfma.Lay.E, VG.Impl.Rsa.X86_64.CrtIfma.Lay.zx,
      Nat.reduceEqDiff, ↓reduceIte, Bool.false_eq_true] at * <;> omega_arith

/-- What `main` leaves after the front, for a valid modulus. -/
abbrev MainQ (s : State) (B : Addr) (Z k pl ql : Nat) (minv mp mq : BitVec 64) (nb xb pb qb qib dpb dqb : List Byte)
    (t : State) : Prop :=
  PDone s t B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib) dpb dqb
      (keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
        (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) ∧ t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10

theorem sizes_mx (hl : LayOk l) : ((.block (sizes l)) : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by
  rcases hl with rfl | rfl | rfl | rfl <;> decide

/-- The key's sizes are those of the layout `l`. -/
abbrev SizesOf (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (w pl ql : Nat) : Prop :=
  w = 2 * l.W ∧ (pl + 7) / 8 = l.W ∧ (ql + 7) / 8 = l.W

/-- Both have the sizes of `lay2048`. -/
theorem Lay2.sizes {l2 : VG.Impl.Rsa.X86_64.CrtIfma.Lay} (h2 : Lay2 l2) (w pl ql : Nat) :
    SizesOf l2 w pl ql ↔ SizesOf lay2048 w pl ql := by
  rcases h2 with rfl | rfl <;> exact Iff.rfl

/-- At most one layout of a function has given sizes. -/
theorem sizesOf_eq {l2 l l' : VG.Impl.Rsa.X86_64.CrtIfma.Lay} (h2 : Lay2 l2) (hl : LayOf l2 l) (hl' : LayOf l2 l')
    {w pl ql : Nat} (h : SizesOf l w pl ql) (h' : SizesOf l' w pl ql) : l = l' := by
  obtain e := h.1.symm.trans h'.1
  rcases h2 with rfl | rfl <;> rcases hl with rfl | rfl | rfl <;> rcases hl' with rfl | rfl | rfl <;>
    first | rfl | exact absurd e (by decide)

/-- `sizes l` after the checks: ZF says whether the key has `l`'s sizes. -/
theorem sizesR_ok (hl : LayOk l) {s t₀ : State} {B : Addr} {Z k : Nat}
    {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    {minv mp mq : BitVec 64} {N C P Q : Nat} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq N C P Q Mk) :
    WP isa (.block (sizes l)) t₀ fun t₁ => t₁.zf = some (decide (SizesOf l ((k + 7) / 8) pl ql)) ∧
      CrtReady s t₁ B Z ((k + 7) / 8) pl ql minv mp mq N C P Q Mk ∧ t₁.mxcsr = t₀.mxcsr := by
  have hn := hr.good.scr.nowrap
  obtain h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hZq := h.z
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hql2 := h.ql2
  exact WP.mono_mx (sizes_mx hl) (sizes_ok hl (pl := pl) (ql := ql) hr.good
    (by rw [hr.hfix _ (by decide) (by decide)]; exact h.hPl) (by rw [hr.hfix _ (by decide) (by decide)]; exact h.hQl)
    (by unfold offQ at hZq; omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun t₁ ⟨zf, me, k₁⟩ mx₁ => ⟨zf, hr.of_regs me k₁, mx₁⟩

/-- `anySizes`: ZF says whether the key has the sizes of one of the layouts. -/
theorem anySizes_ok {s t₀ : State} {B : Addr} {Z k : Nat}
    {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    {minv mp mq : BitVec 64} {N C P Q : Nat} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq N C P Q Mk) :
    WP isa CrtIfma.anySizes t₀ fun t₁ => t₁.zf = some (decide (SizesOf lay2048 ((k + 7) / 8) pl ql ∨
        SizesOf lay3072 ((k + 7) / 8) pl ql ∨ SizesOf lay4096 ((k + 7) / 8) pl ql)) ∧
      CrtReady s t₁ B Z ((k + 7) / 8) pl ql minv mp mq N C P Q Mk ∧ t₁.mxcsr = t₀.mxcsr := by
  unfold CrtIfma.anySizes
  refine WP.seq (WP.mono (sizesR_ok (Or.inl rfl) h hr) fun t₁ ⟨z₁, r₁, x₁⟩ => ?_)
  refine WP.ite _ z₁ (fun hb => WP.block_nil
    ⟨by rw [z₁, hb, decide_eq_true (Or.inl (of_decide_eq_true hb))], r₁, x₁⟩) (fun hb => ?_)
  simp only [decide_eq_false_iff_not] at hb
  refine WP.seq (WP.mono (sizesR_ok (Or.inr (Or.inl rfl)) h r₁) fun t₂ ⟨z₂, r₂, x₂⟩ => ?_)
  refine WP.ite _ z₂ (fun hb' => WP.block_nil
    ⟨by rw [z₂, hb', decide_eq_true (Or.inr (Or.inl (of_decide_eq_true hb')))], r₂, x₂.trans x₁⟩) (fun hb' => ?_)
  simp only [decide_eq_false_iff_not] at hb'
  refine WP.mono (sizesR_ok (Or.inr (Or.inr (Or.inl rfl))) h r₂) fun t₃ ⟨z₃, r₃, x₃⟩ => ⟨?_, r₃, x₃.trans (x₂.trans x₁)⟩
  rw [z₃]
  congr 1
  exact decide_eq_decide.mpr ⟨fun h => .inr (.inr h), fun h => h.resolve_left hb |>.resolve_left hb'⟩

/-- `APost` after an instruction that changes only `rax`, `rdx` and the flags. -/
theorem APost.of_regs {s t t' : State} {B : Addr} {Z w op oq wp : Nat} {minv mp mq : BitVec 64} {N P Q C : Nat}
    (h : APost s t B Z w op oq wp minv mp mq N P Q C) (hm : t'.mem = t.mem) (k : Keep [.rax, .rdx] t t') :
    APost s t' B Z w op oq wp minv mp mq N P Q C := by
  obtain ⟨hg, hN, hp, hq, hf, hk, hw⟩ := h
  obtain hx : ∀ {X : Nat} {o wx : Nat} {mx : BitVec 64}, XVals t B o wx mx X → XVals t' B o wx mx X :=
    fun hx => by rw [show t' = { t' with mem := t.mem } by rw [← hm]]; exact ⟨hx.n, hx.inv, hx.one⟩
  obtain hpr : ∀ {o wx : Nat} {mx : BitVec 64} {X : Nat}, PrimeRdy t B o wx mx N X C → PrimeRdy t' B o wx mx N X C :=
    fun hp => ⟨hm ▸ hp.ws, hx hp.x, hm ▸ hp.ylt, hm ▸ hp.yv, hm ▸ hp.clt, hm ▸ hp.cv⟩
  refine ⟨⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, hm ▸ hg.hdr⟩, ?_, hpr hp, hpr hq, hm ▸ hf,
    (hk.trans k).mono (by decide), hm ▸ hw⟩
  rw [show t' = { t' with mem := t.mem } by rw [← hm]]
  exact ⟨hN.n, hN.inv, hN.r2, hN.r2lt, hN.one⟩

/-- `sizes l'` after `pre`: ZF says whether the key has `l'`'s sizes. -/
theorem sizesA_ok (hl' : LayOk l) {s t₀ s₁ : State} {B : Addr} {Z k : Nat}
    {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    {minv mp mq : BitVec 64} {N C P Q : Nat} {Mk : Bool} {wp : Nat} {N' P' Q' C' : Nat}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq N C P Q Mk)
    (hA : APost t₀ s₁ B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) wp minv mp mq N' P' Q' C') :
    WP isa (.block (sizes l)) s₁ fun s₂ => s₂.zf = some (decide (SizesOf l ((k + 7) / 8) pl ql)) ∧
      APost t₀ s₂ B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) wp minv mp mq N' P' Q' C' ∧
      s₂.mxcsr = s₁.mxcsr := by
  have hn := hr.good.scr.nowrap
  obtain h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hZq := h.z
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hql2 := h.ql2
  obtain hns := preRanges_nsafe (w := (k + 7) / 8) (wp := wp) (wq := wp) (op := offP ((k + 7) / 8))
    (oq := offQ ((k + 7) / 8) pl) (Nat.le_refl _) (by unfold offQ; omega_arith)
  obtain hpw : word s₁.mem B (8 * sPlen) = BitVec.ofNat 64 pl := by
    rw [nsafe_word hA.2.2.2.2.1 hns (by decide) (by decide) (by decide), hr.hfix _ (by decide) (by decide)]
    exact h.hPl
  obtain hqw : word s₁.mem B (8 * sQlen) = BitVec.ofNat 64 ql := by
    rw [nsafe_word hA.2.2.2.2.1 hns (by decide) (by decide) (by decide), hr.hfix _ (by decide) (by decide)]
    exact h.hQl
  exact WP.mono_mx (sizes_mx hl') (sizes_ok hl' (pl := pl) (ql := ql) hA.1 hpw hqw
    (by unfold offQ at hZq; omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun s₂ ⟨zf, me, k₂⟩ mx₂ => ⟨zf, APost.of_regs hA me k₂, mx₂⟩

/-- `ifmaAny` after `pre`, for the layout `l` of the key's sizes: `ifma l`. -/
theorem ifmaAny_ok {l2 : VG.Impl.Rsa.X86_64.CrtIfma.Lay} (h2 : Lay2 l2) (hl2 : LayOf l2 l) {s t₀ s₁ : State} {B : Addr} {Z k : Nat}
    {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (hs : SizesOf l ((k + 7) / 8) pl ql)
    (hA : APost t₀ s₁ B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) l.W minv mp mq
      (Spec.Rsa.os2ip nb) (if Mk then Spec.Rsa.os2ip pb else 3) (if Mk then Spec.Rsa.os2ip qb else 3)
      (Spec.Rsa.os2ip xb)) :
    WP isa (CrtIfma.ifmaAny l2) s₁ fun t =>
      IDone l s t B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl)
        (offQ ((k + 7) / 8) pl + slot l.W 8 + wsTab l.W) minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) dpp dqp qip pl ql dpb dqb Mk ∧
      t.mxcsr = s₁.mxcsr := by
  obtain hl : LayOk l := hl2.ok h2
  obtain ⟨hW1, -⟩ := W_bounds hl
  have hw := hs.1
  obtain hp : wsWords pl = l.W := by unfold wsWords; omega
  obtain hq : wsWords ql = l.W := by unfold wsWords; omega
  -- The vector code of the layout `l'` that the tests choose, which is `l`.
  obtain last : ∀ {l' : VG.Impl.Rsa.X86_64.CrtIfma.Lay} {s₂ : State}, l = l' →
      APost t₀ s₂ B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) l.W minv mp mq
        (Spec.Rsa.os2ip nb) (if Mk then Spec.Rsa.os2ip pb else 3) (if Mk then Spec.Rsa.os2ip qb else 3)
        (Spec.Rsa.os2ip xb) → s₂.mxcsr = s₁.mxcsr →
      WP isa (seqs (ifma l')) s₂ fun t =>
        IDone l s t B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl)
          (offQ ((k + 7) / 8) pl + slot l.W 8 + wsTab l.W) minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
          (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) dpp dqp qip pl ql dpb dqb Mk ∧
        t.mxcsr = s₁.mxcsr := by
    intro l' s₂ e a₂ x₂
    subst e
    exact WP.mono (branchA2_ok hl h hv hr hMk hw hp hq (ifmaZ_of hl h.zk hw hp) a₂) fun t ⟨hd, mx⟩ =>
      ⟨hd, by rw [mx, x₂]⟩
  unfold CrtIfma.ifmaAny
  refine WP.seq (WP.mono (sizesA_ok (l := lay2048) (Or.inl rfl) h hr hA) fun s₂ ⟨z₂, a₂, x₂⟩ => ?_)
  refine WP.ite _ z₂ (fun hb => last (sizesOf_eq h2 hl2 (Or.inl rfl) hs
    ((h2.sizes _ _ _).2 (of_decide_eq_true hb))) a₂ x₂) (fun hb => ?_)
  refine WP.seq (WP.mono (sizesA_ok (l := lay3072) (Or.inr (Or.inl rfl)) h hr a₂) fun s₃ ⟨z₃, a₃, x₃⟩ => ?_)
  refine WP.ite _ z₃ (fun hb' => last
    (sizesOf_eq h2 hl2 (Or.inr (Or.inl rfl)) hs (of_decide_eq_true hb')) a₃ (x₃.trans x₂)) (fun hb' => ?_)
  refine last ?_ a₃ (x₃.trans x₂)
  rcases hl2 with rfl | rfl | rfl
  · exact absurd ((h2.sizes _ _ _).1 hs) (of_decide_eq_false hb)
  · exact absurd hs (of_decide_eq_false hb')
  · rfl

/-- What `main` leaves, from `s` (`CrtPre`): `privateCrt`'s result as
`vg_rsa_private_crt` leaves it, and MXCSR's control bits. -/
abbrev MainOut (s : State) (B : Addr) (Z k : Nat) (op : Addr) (nb xb pb qb dpb dqb qib : List Byte) (t : State) : Prop :=
  (∃ Mk : Bool, MainPost s t B Z k op
    (if Mk then crtResult (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip dpb) (Spec.Rsa.os2ip dqb)
      (Spec.Rsa.os2ip qib) (Spec.Rsa.os2ip xb) else 0) Mk ∧
    (Mk = true ↔ Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb =
      Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip qib < Spec.Rsa.os2ip pb)) ∧
    t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10

end VG.Proof.Bignum.X86_64.Ifma
