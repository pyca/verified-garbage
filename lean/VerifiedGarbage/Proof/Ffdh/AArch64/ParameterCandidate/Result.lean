module
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Mr

import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Fin
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrMain

/-!
# An FFDH parameter candidate on AArch64: the results of the tests

`pResult_ok` and `qResult_ok`: the status and `used` from how Miller–Rabin
ended (`MrEnd`), and `p` to `out` (`finPrimeL_ok`, RSA's `finPrime` for
`out_len` octets of fewer than `8 w`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-- `finPrime`: `c` (`aN`) to the `L` octets of `out`, `kUsed` to `used`,
status 1. -/
theorem finPrimeL_ok {s : State} {B : Addr} {Z w : Nat} {op up : Addr} {u c L : Nat} (h : Ws s B Z w)
    (hL1 : 1 ≤ L) (hLw : L ≤ 8 * w) (hu : word s.mem B (8 * kUsed) = BitVec.ofNat 64 u)
    (hO : word s.mem B (8 * kOut) = op) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 L)
    (hU : word s.mem B (8 * kUsedP) = up) (hM : word s.mem B (8 * Public.sMask) = mask true)
    (ho : OutUp s B Z op up L) (hn : wv s.mem B (slot w aN) ((L + 7) / 8) = c) :
    WP isa finPrime s fun t => KEnd s t op up L 1 u (some c) := by
  have hs := h.scr
  have hnw := hs.nowrap
  have h256 := h.h256
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  unfold finPrime
  rw [List.append_assoc]
  refine wp_seqs_append (by simp) (by simp [storeA]) ?_
  rw [seqs_one]
  refine WP.mono (WP.keep [.x3, .x2] (Q := fun t => t.mem = s.mem.writeW up (BitVec.ofNat 64 u)) (by
    have hup : up + BitVec.ofNat 64 0 = up := off_zero up
    brun [h.x0, hdr_enc (show kUsed < 32 by decide), hdr_enc (show kUsedP < 32 by decide), hl kUsed (by decide),
      hl kUsedP (by decide), hu, hU, hup, ho.upw]) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨hm₁, k₁⟩ => ?_
  have f₁ : Frm B [(Z, 2 ^ 64)] s.mem s₁.mem := by rw [hm₁]; exact frm_up ho.upZ _ _
  have h₁ : Ws s₁ B Z w := h.congr' f₁ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact KMut.past h256 _) k₁ (by decide)
  have hw₁ : ∀ i < 32, word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    f₁.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega)) (by omega)
  have hn₁ : wv s₁.mem B (slot w aN) ((L + 7) / 8) = c := by
    rw [f₁.wv_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (by have := h₁.sl (show aN < 16 by decide); omega))
      (by have := h₁.sl (show aN < 16 by decide); omega)]; exact hn
  refine wp_seqs_append (by simp [storeA]) (by simp) ?_
  refine WP.mono (storeA_ok h₁ (j := aN) (sPtr := kOut) (sLen := kLen) (sMsk := Public.sMask) (c := true)
    (by decide) (by decide) (by decide) (by decide) (by rw [hw₁ _ (by decide)]; exact hO)
    (by rw [hw₁ _ (by decide)]; exact hK) (by rw [hw₁ _ (by decide)]; exact hM) hL1 hLw
    (fun i hi => by rw [k₁.wr]; exact ho.outw i hi) ho.outZ) fun s₂ ⟨hb₂, hx₂, hwr₂, _, k₂⟩ => ?_
  rw [seqs_one]
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 1 ∧ t.mem = s₂.mem) (by brun) (by decide) (by decide)
    (by decide +kernel)) fun t ⟨⟨hx, hm⟩, k₃⟩ => ?_
  simp only [hn₁, ↓reduceIte] at hb₂
  refine ⟨hx, ?_, by rw [hm]; exact hb₂, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  rw [hm]
  refine (Mem.readW_congr fun b hb => hx₂ _ fun i hi he => ho.ou i hi b hb ?_).trans ?_
  · exact he.symm
  · rw [hm₁]; exact Mem.readW_writeW_self64 _ _ _

/-- How a test ended, from `s`. -/
def PTEnd (s t : State) (op up : Addr) (k : Nat) (r : List Byte) (c : Nat) :
    Option (Bool × List Byte) → Prop
  | none => KEnd s t op up k 0 0 none
  | some (true, rest) => KEnd s t op up k 1 (r.length - rest.length) (some c)
  | some (false, rest) => KEnd s t op up k 2 (r.length - rest.length) none

/-- The status words of `MrEnd`. -/
theorem MrEnd.stat {p : PP} {w N mb K : Nat} {s₀ s : State} {res : Option (Bool × List Byte)}
    (h : MrEnd p w N mb K s₀ res s) :
    (res = none → word s.mem p.B (8 * kStat) = BitVec.ofNat 64 0) ∧
    (∀ b rest, res = some (b, rest) → word s.mem p.B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 2) ∧
      word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 (p.r.length - rest.length)) := by
  refine ⟨h.2.1, fun b rest hr => ?_⟩
  obtain ⟨hs, u, hu, rfl, hU⟩ := h.2.2.1 b rest hr
  refine ⟨hs, ?_⟩
  rw [hU, List.length_drop]; congr 1; omega

/-- `pResult`, after `p`'s Miller–Rabin ended with `res`. -/
theorem pResult_ok {s : State} {B : Addr} {Z w c L : Nat} {op up : Addr} {r : List Byte}
    {res : Option (Bool × List Byte)} (h : Ws s B Z w) (hL1 : 1 ≤ L) (hLw : L ≤ 8 * w)
    (hn : wv s.mem B (slot w aN) ((L + 7) / 8) = c) (ho : OutUp s B Z op up L)
    (hO : word s.mem B (8 * kOut) = op) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 L)
    (hU : word s.mem B (8 * kUsedP) = up) (hM : word s.mem B (8 * Public.sMask) = mask true)
    (h0 : res = none → word s.mem B (8 * kStat) = BitVec.ofNat 64 0)
    (h1 : ∀ b rest, res = some (b, rest) → word s.mem B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 2) ∧
      word s.mem B (8 * kUsed) = BitVec.ofNat 64 (r.length - rest.length)) :
    WP isa pResult s fun t => PTEnd s t op up L r c res := by
  have hs := h.scr
  have hnw := hs.nowrap
  have h256 := h.h256
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * kStat)) 8 := hs.ld (by simp only [kStat, sFn]; omega)
  unfold pResult
  have hfirst : ∀ v : Nat, word s.mem B (8 * kStat) = BitVec.ofNat 64 v →
      WP isa (.block [ldh .x3 kStat]) s fun t => (t.gpr .x3 = BitVec.ofNat 64 v ∧ t.mem = s.mem) ∧ Keep [.x3] s t :=
    fun v hv => WP.keep [.x3] (by brun [h.x0, hdr_enc (show kStat < 32 by decide), hl, hv]) (by decide) (by decide)
      (by decide +kernel)
  rcases hres : res with _ | ⟨b, rest⟩
  · refine WP.seq (WP.mono (hfirst 0 (h0 hres)) fun s₁ ⟨⟨h3, hm⟩, k₁⟩ => ?_)
    refine WP.ite true (by rw [eval_zero, h3]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.mono (finNone_ok (up := up) (hs.congr k₁.wr) ((k₁.gpr .x0 (by decide)).trans h.x0) h256 (by rw [hm]; exact hU)
      (by rw [k₁.wr]; exact ho.upw)) fun t ht => ?_
    exact (KEnd.of_fin (ho.congr k₁.wr) ht).trans_pre (by rw [hm]) (k₁.mono (by decide))
  · obtain ⟨hS, hu⟩ := h1 b rest hres
    refine WP.seq (WP.mono (hfirst _ hS) fun s₁ ⟨⟨h3, hm⟩, k₁⟩ => ?_)
    refine WP.ite false (by rw [eval_zero, h3]; cases b <;> rfl) (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.seq (WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 (if b then 0 else 1) ∧
      t.mem = s₁.mem) (by brun [h3]; cases b <;> rfl) (by decide) (by decide) (by decide +kernel))
      fun s₂ ⟨⟨h3₂, hm₂⟩, k₂⟩ => ?_)
    have k12 := k₁.trans k₂
    have hm12 : s₂.mem = s.mem := hm₂.trans hm
    have ho₂ := ho.congr k12.wr
    refine WP.ite b (by rw [eval_zero, h3₂]; cases b <;> rfl) (fun hb => ?_) (fun hb => ?_)
    · subst hb
      have h₂ : Ws s₂ B Z w := h.congr' (rs := []) (fun x _ => by rw [hm12]) (by simp) k12 (by decide)
      refine WP.mono (finPrimeL_ok (u := r.length - rest.length) (c := c) (up := up) (op := op) h₂ hL1 hLw
        (by rw [hm12]; exact hu) (by rw [hm12]; exact hO) (by rw [hm12]; exact hK) (by rw [hm12]; exact hU)
        (by rw [hm12]; exact hM) ho₂ (by rw [hm12]; exact hn)) fun t ht => ?_
      exact ht.trans_pre (by rw [hm12]) (k12.mono (by decide))
    · subst hb
      refine WP.mono (finUsed_ok (u := r.length - rest.length) (up := up) (hs.congr k12.wr)
        ((k12.gpr .x0 (by decide)).trans h.x0) h256 (by decide) (by rw [hm12]; exact hu) (by rw [hm12]; exact hU)
        ho₂.upw) fun t ht => ?_
      exact (KEnd.of_fin ho₂ ht).trans_pre (by rw [hm12]) (k12.mono (by decide))

/-- `qResult`, after `q`'s Miller–Rabin ended with `res`, not passing. -/
theorem qResult_ok {s : State} {B : Addr} {Z w c L : Nat} {op up : Addr} {r : List Byte}
    {res : Option (Bool × List Byte)} (h : Ws s B Z w) (ho : OutUp s B Z op up L)
    (hU : word s.mem B (8 * kUsedP) = up)
    (hnp : ∀ rest, res ≠ some (true, rest))
    (h0 : res = none → word s.mem B (8 * kStat) = BitVec.ofNat 64 0)
    (h1 : ∀ b rest, res = some (b, rest) → word s.mem B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 2) ∧
      word s.mem B (8 * kUsed) = BitVec.ofNat 64 (r.length - rest.length)) :
    WP isa qResult s fun t => PTEnd s t op up L r c res := by
  have hs := h.scr
  have hnw := hs.nowrap
  have h256 := h.h256
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * kStat)) 8 := hs.ld (by simp only [kStat, sFn]; omega)
  unfold qResult
  have hfirst : ∀ v : Nat, word s.mem B (8 * kStat) = BitVec.ofNat 64 v →
      WP isa (.block [ldh .x3 kStat]) s fun t => (t.gpr .x3 = BitVec.ofNat 64 v ∧ t.mem = s.mem) ∧ Keep [.x3] s t :=
    fun v hv => WP.keep [.x3] (by brun [h.x0, hdr_enc (show kStat < 32 by decide), hl, hv]) (by decide) (by decide)
      (by decide +kernel)
  rcases hres : res with _ | ⟨b, rest⟩
  · refine WP.seq (WP.mono (hfirst 0 (h0 hres)) fun s₁ ⟨⟨h3, hm⟩, k₁⟩ => ?_)
    refine WP.ite true (by rw [eval_zero, h3]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.mono (finNone_ok (up := up) (hs.congr k₁.wr) ((k₁.gpr .x0 (by decide)).trans h.x0) h256 (by rw [hm]; exact hU)
      (by rw [k₁.wr]; exact ho.upw)) fun t ht => ?_
    exact (KEnd.of_fin (ho.congr k₁.wr) ht).trans_pre (by rw [hm]) (k₁.mono (by decide))
  · cases b
    · obtain ⟨hS, hu⟩ := h1 false rest hres
      refine WP.seq (WP.mono (hfirst _ hS) fun s₁ ⟨⟨h3, hm⟩, k₁⟩ => ?_)
      refine WP.ite false (by rw [eval_zero, h3]; rfl) (fun h => absurd h (by decide)) (fun _ => ?_)
      refine WP.mono (finUsed_ok (u := r.length - rest.length) (up := up) (hs.congr k₁.wr)
        ((k₁.gpr .x0 (by decide)).trans h.x0) h256 (by decide) (by rw [hm]; exact hu) (by rw [hm]; exact hU)
        (by rw [k₁.wr]; exact ho.upw)) fun t ht => ?_
      exact (KEnd.of_fin (ho.congr k₁.wr) ht).trans_pre (by rw [hm]) (k₁.mono (by decide))
    · exact absurd hres (hnp rest)

end VG.Proof.Ffdh.AArch64.ParameterCandidate
