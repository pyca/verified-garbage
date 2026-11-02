module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.RoundCall
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFn
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Minv
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Slot
public import VerifiedGarbage.Impl.MillerRabin.PPC64LE.Search

/-!
# A candidate on PPC64LE: the states the round is called from

For the constant time of the witnesses' loop, what the correctness proofs
compose in one step is needed at the points in between: `preCall_wp`, the
round's arguments before its call (`CallIn`), whose contract then holds
(`CallIn.pre`) and agrees between two runs (`CallIn.pub`); `call_wp`, the
call keeping `r31`; `load1_wp`, the addresses of a witness's octets.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (Env arr RoundImpl)
open VG.Proof.MillerRabin.PPC64LE.Search (Prep Kept keeps_word r12_inv)
open VG.Proof.Bignum (slot)

/-- The state the round is called from. -/
structure CallIn (s : State) (B : Addr) (L w c : Nat) : Prop where
  prep : Prep s B L w c
  r3 : s.gpr .r3 = B
  r4 : s.gpr .r4 = BitVec.ofNat 64 L
  a5 : arr s.mem B w 5 < c
  wr : (⟨B, 8 * L⟩ : Region) ∈ s.wr
  sp : 176 ≤ s.sp.toNat
  stk : (below s.sp 176).Disjoint ⟨B, 8 * L⟩

/-- The round's arguments, after its witness in Montgomery form. -/
abbrev preCall : Prog isa :=
  .seq (.seq (.block minv32) (PublicChecked.montOp 5 4 1)) (.block [.addi .r3 .r31 0, ldh .r4 hWsLen])

theorem preCall_wp {s : State} {B : Addr} {L w c : Nat} (h : Prep s B L w c) (hwr : (⟨B, 8 * L⟩ : Region) ∈ s.wr)
    (hsp : 176 ≤ s.sp.toNat) (hstk : (below s.sp 176).Disjoint ⟨B, 8 * L⟩) :
    WP isa preCall s fun t => CallIn t B L w c := by
  have e := h.env
  have hnw := e.hs.nowrap
  have hZ := e.hZ
  have hw4 := e.hw
  have hw128 := e.hw'
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have hZ' : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := by rw [← es]; exact hZ
  have hR : Nat.Coprime (2 ^ (64 * w)) c := VG.Proof.Bignum.coprime_pow2 h.odd _
  have l56 : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 56) 8 := e.hs.ld (d := 56) (by omega)
  refine WP.seq (WP.seq (WP.mono (WP.keep [.r12] (Q := fun u => u.gpr .r12 = (word s.mem B 56 <<< 32) >>> 32 ∧
      u.mem = s.mem) (by simp only [minv32, ldh, hMinv]; prun [e.h31, l56]) (by decide))
    fun u ⟨⟨u12, um⟩, ku⟩ => ?_))
  have hu : Prep u B L w c := h.transfer (e.keep ku (by decide)) (fun d _ _ => by rw [um])
    (fun j _ _ => by rw [um])
  have eu := hu.env
  obtain ⟨i12, iinv⟩ := r12_inv h.inv
  refine WP.mono (Pub.montOp_ok eu.hs (o := 5) (a := 4) (b := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by omega) (by omega) (by simp only [es]; omega) eu.h10 eu.h29
    eu.h11 (by rw [u12]; exact i12) (by rw [u12, um, w32_eq_mod]; exact iinv)
    (by show arr u.mem B w 1 < arr u.mem B w 0; rw [hu.r1, hu.n]; exact Nat.mod_lt _ (by have := h.c3; omega)))
    fun s₁ ⟨⟨lt₁, eq₁, o₁⟩, k₁⟩ => ?_
  have hn0 : val32 u.mem B (slot w 0) (2 * w) = c := hu.n
  rw [hn0] at lt₁
  have sep₁ : ∀ d k, 0 < k → (∀ i, d ≤ i → i < d + k → Kept w i) → ∀ r ∈ [(slot w 2, 8 * (w + 2)),
      (slot w 3, 8 * (w + 2)), (slot w 5, 8 * (w + 2))], d + k ≤ r.1 ∨ r.1 + r.2 ≤ d := by
    intro d k hk0 hk r hr
    have hj : ∃ j ∈ [2, 3, 5, 6, 8], r = (slot w j, 8 * (w + 2)) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [⟨2, by simp, rfl⟩, ⟨3, by simp, rfl⟩, ⟨5, by simp, rfl⟩]
    obtain ⟨j, hjm, rfl⟩ := hj
    show d + k ≤ slot w j ∨ slot w j + 8 * (w + 2) ≤ d
    by_contra hc
    simp only [not_or, Nat.not_le] at hc
    by_cases hd : d ≤ slot w j
    · have := (hk (slot w j) hd (by omega)).2.1 j hjm; omega
    · have := (hk d (Nat.le_refl _) (by omega)).2.1 j hjm; omega
  have w₁ : ∀ d, d + 8 ≤ 8 * L → (∀ i, d ≤ i → i < d + 8 → Kept w i) → word s₁.mem B d = word u.mem B d :=
    fun d hd hk => Outs.word o₁ (sep₁ d 8 (by decide) hk) (by omega)
  have v₁ : ∀ j, slot w j + 8 * w ≤ 8 * L → (∀ i, slot w j ≤ i → i < slot w j + 8 * w → Kept w i) →
      val32 s₁.mem B (slot w j) (2 * w) = val32 u.mem B (slot w j) (2 * w) :=
    fun j hd hk => Outs.val32 o₁ (by have := sep₁ _ _ (by omega) hk; simpa only [show 4 * (2 * w) = 8 * w by omega])
      (by omega)
  have p₁ : Prep s₁ B L w c := hu.transfer (eu.keep k₁ (by decide)) w₁ v₁
  have h31₁ : s₁.gpr .r31 = B := (k₁.gpr .r31 (by decide)).trans eu.h31
  have l0 : InRegions (s₁.rd ++ s₁.wr) B 8 := by
    have := (eu.hs.congr k₁.wr).ld (d := 0) (n := 8) (by omega)
    simpa only [off, BitVec.add_zero] using this
  have r0 : s₁.mem.readW B 64 = BitVec.ofNat 64 L := by
    have := p₁.len
    simpa only [word, off, BitVec.add_zero] using this
  refine WP.mono (WP.keep [.r3, .r4] (Q := fun t => t.gpr .r3 = B ∧ t.gpr .r4 = BitVec.ofNat 64 L ∧
      t.mem = s₁.mem) (by simp only [ldh, hWsLen]; prun [h31₁, BitVec.add_zero, l0, r0]) (by decide))
    fun t ⟨⟨r3, r4, m⟩, k⟩ => ?_
  have K := (ku.trans k₁).trans k
  exact ⟨p₁.transfer (p₁.env.keep k (by decide)) (fun d _ _ => by rw [m]) (fun j _ _ => by rw [m]), r3, r4,
    by show val32 t.mem B (slot w 5) (2 * w) < c; rw [m]; exact lt₁, by rw [K.wr]; exact hwr,
    by rw [K.sp]; exact hsp, by rw [K.sp]; exact hstk⟩

/-- The round's contract holds where it is called. -/
theorem CallIn.pre {s : State} {B : Addr} {L w c : Nat} (h : CallIn s B L w c) :
    (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 176).pre
      (s.callEntry.withRegions [] [⟨B, 8 * L⟩]) := by
  have e := h.prep.env
  have hnw := e.hs.nowrap
  have hZ := e.hZ
  have hw4 := e.hw
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have hZ' : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := by rw [← es]; exact hZ
  have hL64 : L < 2 ^ 64 := by omega
  have hsp := h.sp
  have hstk := h.stk
  sig_pre [Proof.MillerRabin.Round.roundContract, Proof.MillerRabin.Round.roundSig, PPC64LE.abi, PPC64LE.argRegs]
  simp only [h.r3, h.r4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hL64, Nat.mul_comm L 8]
  exact ⟨hsp, trivial, hstk, by omega, h.prep.layout, h.prep.prepared h.a5⟩

/-- Two runs' calls agree on the round's public data. -/
theorem CallIn.pub {s₁ s₂ : State} {B : Addr} {L w c₁ c₂ : Nat} (h₁ : CallIn s₁ B L w c₁)
    (h₂ : CallIn s₂ B L w c₂) (hsp : s₁.sp = s₂.sp) :
    (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 176).pub
      (s₁.callEntry.withRegions [] [⟨B, 8 * L⟩]) (s₂.callEntry.withRegions [] [⟨B, 8 * L⟩]) := by
  sig_pub [Proof.MillerRabin.Round.roundContract, Proof.MillerRabin.Round.roundSig, PPC64LE.abi, PPC64LE.argRegs]
  rw [h₁.r3, h₂.r3, h₁.r4, h₂.r4, h₁.prep.width, h₂.prep.width]
  exact ⟨hsp, rfl, rfl, rfl⟩

/-- The round's call, keeping `r31`. -/
theorem call_wp (R : RoundImpl) {s : State} {B : Addr} {L w c : Nat} (h : CallIn s B L w c) :
    WP isa (.call R.name R.code) s fun t => t.gpr .r31 = s.gpr .r31 := by
  refine WP.callAny (k := Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 176) R.verified.1
    (rd := []) (wr := [⟨B, 8 * L⟩]) h.pre ?_ ?_ (fun s₃ _ _ _ _ hcs _ => hcs .r31 (by decide))
    (by have := R.stack; omega)
  · exact fun x n ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ (by
      simp only [List.nil_append, List.mem_singleton] at hr; rw [hr]; exact h.wr), hc⟩
  · exact fun x n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton] at hr; rw [hr]; exact h.wr, hc⟩

/-- `load`'s first block. -/
abbrev load1 : List Instr :=
  [ldh .r12 hRand, ldh .r3 hUsed, .add .r12 .r12 .r3, ldh .r6 hK, .add .r3 .r3 .r6, sth .r3 hUsed] ++
    PublicChecked.base .r10 4

theorem load1_wp {s : State} {B R : Addr} {Z w u : Nat} (h : Env s B Z w) (hR : word s.mem B (8 * hRand) = R)
    (hu : word s.mem B (8 * hUsed) = BitVec.ofNat 64 u) (hk : word s.mem B (8 * hK) = BitVec.ofNat 64 (8 * w)) :
    WP isa (.block load1) s fun t => t.gpr .r12 = off R u ∧ t.gpr .r6 = BitVec.ofNat 64 (8 * w) ∧
      t.gpr .r10 = off B (slot w 4) ∧ t.gpr .r11 = s.gpr .r11 ∧ t.gpr .r31 = s.gpr .r31 := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hZ := h.hZ
  rw [slot_lin] at hZ
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r3, .r6, .r12] (Q := fun t => t.gpr .r12 = off R u ∧
      t.gpr .r6 = BitVec.ofNat 64 (8 * w)) ?_ (by decide)) fun t₁ ⟨⟨a12, a6⟩, k₁⟩ => ?_
  · simp only [ldh, sth, hRand, hUsed, hK] at hR hu hk ⊢
    prun [h.h31, hs.ld (d := 136) (n := 8) (by omega), hs.ld (d := 152) (n := 8) (by omega),
      hs.ld (d := 216) (n := 8) (by omega), hs.st (d := 152) (n := 8) (by omega), hR, hu, hk]
  refine WP.mono (Pub.base_ok (rd := .r10) (by decide) (by decide) ((k₁.gpr _ (by decide)).trans h.h10)
    ((k₁.gpr _ (by decide)).trans h.h29) 4) fun t₂ ⟨⟨a10, _⟩, k₂⟩ => ?_
  exact ⟨(k₂.gpr _ (by decide)).trans a12, (k₂.gpr _ (by decide)).trans a6, a10,
    (k₂.gpr _ (by decide)).trans (k₁.gpr _ (by decide)), (k₂.gpr _ (by decide)).trans (k₁.gpr _ (by decide))⟩

end VG.Proof.RsaKeyGen.PPC64LE.Cand
