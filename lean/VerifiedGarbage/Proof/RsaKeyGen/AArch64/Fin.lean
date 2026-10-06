import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Front

/-!
# A candidate on AArch64: the ends after Miller–Rabin

`finPrime_ok`: `kUsed` to `used`, `c` to `out`, status 1. `mrResult_ok`:
the end from `kStat`, as `TestEnd` of the primality test's result.
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Bignum.Public (aN)

/-- A store of 8 octets past the scratch space changes memory there only. -/
theorem frm_up {B up : Addr} {Z : Nat} (hupZ : ∀ b < 8, Z ≤ ofs B (up + BitVec.ofNat 64 b)) (m : Mem)
    (v : BitVec 64) : Frm B [(Z, 2 ^ 64)] m (m.writeW up v) := fun x hx => by
  have hx' : ofs B x < Z := by
    have := hx (Z, 2 ^ 64) (List.mem_singleton_self _)
    have : ofs B x < 2 ^ 64 := BitVec.isLt _
    omega
  exact writeW64_other v fun b hb he => by have := hupZ b hb; rw [← he] at this; omega

theorem KMut.past {Z : Nat} (h : 8 * 32 ≤ Z) (n : Nat) : KMut (Z, n) := Or.inl h

/-- `finPrime`: `c` (`aN`) to the `8 w` octets of `out`, `kUsed` to `used`,
status 1. -/
theorem finPrime_ok {s : State} {B : Addr} {Z w : Nat} {op up : Addr} {u c : Nat} (h : Ws s B Z w)
    (hw64 : w ≤ 64) (hu : word s.mem B (8 * kUsed) = BitVec.ofNat 64 u) (hO : word s.mem B (8 * kOut) = op)
    (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w)) (hU : word s.mem B (8 * kUsedP) = up)
    (hM : word s.mem B (8 * Public.sMask) = mask true) (ho : OutUp s B Z op up (8 * w))
    (hn : wv s.mem B (slot w aN) w = c) :
    WP isa finPrime s fun t => KEnd s t op up (8 * w) 1 u (some c) := by
  have hs := h.scr
  have hnw := hs.nowrap
  have h256 := h.h256
  have hw2 := h.w1
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
  have hn₁ : wv s₁.mem B (slot w aN) w = c := by
    rw [f₁.wv_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (by have := h₁.sl (show aN < 16 by decide); omega))
      (by have := h₁.sl (show aN < 16 by decide); omega)]; exact hn
  refine wp_seqs_append (by simp [storeA]) (by simp) ?_
  refine WP.mono (storeA_ok h₁ (j := aN) (sPtr := kOut) (sLen := kLen) (sMsk := Public.sMask) (c := true)
    (by decide) (by decide) (by decide) (by decide) (by rw [hw₁ _ (by decide)]; exact hO)
    (by rw [hw₁ _ (by decide)]; exact hK) (by rw [hw₁ _ (by decide)]; exact hM) (by omega) (Nat.le_refl _)
    (fun i hi => by rw [k₁.wr]; exact ho.outw i hi) ho.outZ) fun s₂ ⟨hb₂, hx₂, hwr₂, _, k₂⟩ => ?_
  rw [seqs_one]
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 1 ∧ t.mem = s₂.mem) (by brun) (by decide) (by decide)
    (by decide +kernel)) fun t ⟨⟨hx, hm⟩, k₃⟩ => ?_
  have hk : (8 * w + 7) / 8 = w := by omega
  simp only [hk, hn₁, ↓reduceIte] at hb₂
  refine ⟨hx, ?_, by rw [hm]; exact hb₂, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  rw [hm]
  refine (Mem.readW_congr fun b hb => hx₂ _ fun i hi he => ho.ou i hi b hb ?_).trans ?_
  · exact he.symm
  · rw [hm₁]; exact Mem.readW_writeW_self64 _ _ _

/-- How a primality test's result ends a candidate `c`. -/
def TestEnd (s t : State) (op up : Addr) (k : Nat) (r : List Byte) (c : Nat) :
    Option (Bool × List Byte) → Prop
  | none => KEnd s t op up k 0 0 none
  | some (true, rest) => KEnd s t op up k 1 (r.length - rest.length) (some c)
  | some (false, rest) => KEnd s t op up k 3 (r.length - rest.length) none

/-- `mrResult`, after `millerRabin` ended with `res`. -/
theorem mrResult_ok {s : State} {B : Addr} {Z w c : Nat} {op up : Addr} {r : List Byte}
    {res : Option (Bool × List Byte)} (h : Ws s B Z w) (hw64 : w ≤ 64)
    (hn : wv s.mem B (slot w aN) w = c) (ho : OutUp s B Z op up (8 * w))
    (hO : word s.mem B (8 * kOut) = op) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hU : word s.mem B (8 * kUsedP) = up) (hM : word s.mem B (8 * Public.sMask) = mask true)
    (h0 : res = none → word s.mem B (8 * kStat) = BitVec.ofNat 64 0)
    (h1 : ∀ b rest, res = some (b, rest) → word s.mem B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 3) ∧
      word s.mem B (8 * kUsed) = BitVec.ofNat 64 (r.length - rest.length)) :
    WP isa mrResult s fun t => TestEnd s t op up (8 * w) r c res := by
  have hs := h.scr
  have hnw := hs.nowrap
  have h256 := h.h256
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * kStat)) 8 := hs.ld (by simp only [kStat, sFn]; omega)
  unfold mrResult
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
    refine WP.seq (WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 (if b then 0 else 2) ∧
      t.mem = s₁.mem) (by brun [h3]; cases b <;> rfl) (by decide) (by decide) (by decide +kernel))
      fun s₂ ⟨⟨h3₂, hm₂⟩, k₂⟩ => ?_)
    have k12 := k₁.trans k₂
    have hm12 : s₂.mem = s.mem := hm₂.trans hm
    have ho₂ := ho.congr k12.wr
    refine WP.ite b (by rw [eval_zero, h3₂]; cases b <;> rfl) (fun hb => ?_) (fun hb => ?_)
    · subst hb
      have h₂ : Ws s₂ B Z w := h.congr' (rs := []) (fun x _ => by rw [hm12]) (by simp) k12 (by decide)
      refine WP.mono (finPrime_ok (u := r.length - rest.length) (c := c) (up := up) (op := op) h₂ hw64 (by rw [hm12]; exact hu)
        (by rw [hm12]; exact hO) (by rw [hm12]; exact hK) (by rw [hm12]; exact hU) (by rw [hm12]; exact hM) ho₂
        (by rw [hm12]; exact hn)) fun t ht => ?_
      exact ht.trans_pre (by rw [hm12]) (k12.mono (by decide))
    · subst hb
      refine WP.mono (finUsed_ok (u := r.length - rest.length) (up := up) (hs.congr k12.wr)
        ((k12.gpr .x0 (by decide)).trans h.x0) h256 (by decide) (by rw [hm12]; exact hu) (by rw [hm12]; exact hU)
        ho₂.upw) fun t ht => ?_
      exact (KEnd.of_fin ho₂ ht).trans_pre (by rw [hm12]) (k12.mono (by decide))

end VG.Proof.RsaKeyGen.AArch64
