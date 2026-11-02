module

public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtMid
public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtPower
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCore
import VerifiedGarbage.Proof.Bignum.CrtResult
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The RSA private-key operation on RISC-V: the powers

`mid1_ok`: after the front, `X` loaded and checked, the input loaded again,
then `m₁ = c^dP mod p` and `m₂ = c^dQ mod q` in the primes' working spaces
(`M1`), with `p`, `q` and `qInv` masked.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Crt

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot Arrays Frm)
open VG.Proof.Bignum.RISCV64.Win (power_ok le_nChunks_mul nChunks_mul_lt nChunks PFr)

/-! ## Numbers of the entry state -/

abbrev vN (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .a2) (ck s₀))
abbrev vC (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .a4) (ck s₀))
abbrev vP (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .a6) (cpL s₀))
abbrev vQ (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (stackArg s₀ 0) (cqL s₀))
abbrev vDP (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (stackArg s₀ 2) (cpL s₀))
abbrev vDQ (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (stackArg s₀ 4) (cqL s₀))
abbrev vQI (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (stackArg s₀ 6) (cpL s₀))
/-- The mask. -/
abbrev cb (s₀ : State) : Bool := crtMask (vN s₀) (ck s₀) (vC s₀) (vP s₀) (vQ s₀) (vQI s₀)
/-- The masked `p`, `q` and `qInv`. -/
abbrev mP (s₀ : State) : Nat := if cb s₀ then vP s₀ else 3
abbrev mQ (s₀ : State) : Nat := if cb s₀ then vQ s₀ else 3
abbrev mQI (s₀ : State) : Nat := if cb s₀ then vQI s₀ else 0
/-- The primes' working spaces' words, and their offsets in the scratch. -/
abbrev cwP (s₀ : State) : Nat := wordsOf (cpL s₀)
abbrev cwQ (s₀ : State) : Nat := wordsOf (cqL s₀)
abbrev oPa (s₀ : State) : Nat := slot (cwX s₀) 8
abbrev oQa (s₀ : State) : Nat := slot (cwX s₀) 8 + slot (cwP s₀) 24
/-- `m₁` and `m₂`. -/
abbrev vm1 (s₀ : State) : Nat := vC s₀ ^ vDP s₀ % mP s₀
abbrev vm2 (s₀ : State) : Nat := vC s₀ ^ vDQ s₀ % mQ s₀

theorem mask_true {nb cb pb qb ib : List Byte} {k : Nat} (hk : 64 ≤ k) (hpl : pb.length < k)
    (hql : qb.length < k)
    (h : crtMask (Spec.Rsa.os2ip nb) k (Spec.Rsa.os2ip cb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
      (Spec.Rsa.os2ip ib) = true) :
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true ∧ Spec.Rsa.os2ip cb < Spec.Rsa.os2ip nb ∧
      Spec.Rsa.os2ip ib < Spec.Rsa.os2ip pb ∧ Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb ∧
      1 < Spec.Rsa.os2ip pb ∧ Spec.Rsa.os2ip pb % 2 = 1 ∧ 1 < Spec.Rsa.os2ip qb ∧ Spec.Rsa.os2ip qb % 2 = 1 := by
  simp only [crtMask, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hv, hc⟩, hi⟩, hpq⟩ := h
  obtain ⟨hodd, _, hP, hQ⟩ := VG.Proof.Bignum.crt_bounds_of hv hk rfl hpl rfl hql
  obtain ⟨hq1, hqo⟩ := VG.Proof.Bignum.factor_facts hpq hP hodd
  obtain ⟨hp1, hpo⟩ := VG.Proof.Bignum.factor_facts (by rw [Nat.mul_comm]; exact hpq) hQ hodd
  exact ⟨hv, hc, hi, hpq, hp1, hpo, hq1, hqo⟩

theorem pow256_le {L w : Nat} (h : L ≤ 8 * w) : 256 ^ L ≤ 2 ^ (64 * w) := by
  rw [VG.Proof.Bignum.pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by omega_arith)

theorem os2ip_lt' (bs : List Byte) {L : Nat} (h : bs.length = L) : Spec.Rsa.os2ip bs < 256 ^ L := by
  have := VG.Proof.Bignum.os2ip_lt bs; rwa [h] at this

theorem three_lt_pow {L : Nat} (h : 1 ≤ L) : 3 < 256 ^ L :=
  Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (n := 256) (by decide) h)

/-- What the masked numbers satisfy. -/
theorem masked_facts {s₀ : State} (hP : PF s₀) :
    1 < mP s₀ ∧ mP s₀ % 2 = 1 ∧ 1 < mQ s₀ ∧ mQ s₀ % 2 = 1 ∧ mP s₀ < 256 ^ cpL s₀ ∧
      mQ s₀ < 256 ^ cqL s₀ ∧ mQI s₀ < mP s₀ ∧ mQI s₀ < 256 ^ cpL s₀ := by
  have h3p := three_lt_pow hP.p1
  have h3q := three_lt_pow hP.q1
  unfold mP mQ mQI
  cases hb : cb s₀
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨by decide, by decide, by decide, by decide, h3p, h3q, by decide, by omega_arith⟩
  · simp only [↓reduceIte]
    obtain ⟨_, _, hi, _, hp1, hpo, hq1, hqo⟩ := mask_true hP.k64
      (by rw [VG.Proof.Bignum.bytesAt_length]; exact hP.pk) (by rw [VG.Proof.Bignum.bytesAt_length]; exact hP.qk) hb
    exact ⟨hp1, hpo, hq1, hqo, os2ip_lt' _ (VG.Proof.Bignum.bytesAt_length _ _ _),
      os2ip_lt' _ (VG.Proof.Bignum.bytesAt_length _ _ _), hi, os2ip_lt' _ (VG.Proof.Bignum.bytesAt_length _ _ _)⟩

/-! ## Working spaces in the scratch -/

/-- A number of `W` words below `2^(64 n)`, `n ≤ W`, is its first `n` words. -/
theorem wordsVal_trunc {m : Mem} {B : Addr} {d W n v : Nat} (h : wordsVal m B d W = v) (hv : v < 2 ^ (64 * n))
    (hn : n ≤ W) : wordsVal m B d n = v := by
  rw [Pre.wordsVal_eq_wv] at h ⊢
  have e := VG.Proof.Bignum.wv_add m B d n (W - n)
  rw [Nat.add_sub_cancel' hn, h] at e
  by_cases h0 : VG.Proof.Bignum.wv m B (d + 8 * n) (W - n) = 0
  · rw [h0, Nat.mul_zero, Nat.add_zero] at e; exact e.symm
  · have : 2 ^ (64 * n) ≤ 2 ^ (64 * n) * VG.Proof.Bignum.wv m B (d + 8 * n) (W - n) :=
      Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h0)
    omega_arith

theorem Scr.sub {s : State} {B : Addr} {Z d n : Nat} (hs : Scr s B Z) (h : d + n ≤ Z) (h8 : d % 8 = 0) (hn0 : 0 < n) :
    Scr s (Mont.off B d) n := by
  have hn := hs.nowrap
  have ha := hs.al
  obtain ⟨B₀, o, L, hm, hb, hL, hL'⟩ := hs.wr
  have e : (Mont.off B d).toNat = B.toNat + d := by
    simp only [Mont.off, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := d) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  refine ⟨⟨B₀, o + d, L, hm, ?_, ?_, hL'⟩, ?_, ?_⟩
  · rw [hb]; simp only [Mont.off, BitVec.add_assoc, BitVec.ofNat_add]
  · exact Nat.le_trans (by rw [Nat.add_assoc]; exact Nat.add_le_add_left h o) hL
  · rw [e]; omega
  · rw [e]; omega

theorem Scr.le {s : State} {B : Addr} {Z n : Nat} (hs : Scr s B Z) (h : n ≤ Z) : Scr s B n :=
  ⟨let ⟨B₀, o, L, hm, hb, hL, hL'⟩ := hs.wr; ⟨B₀, o, L, hm, hb, by omega_arith, hL'⟩,
    by have := hs.nowrap; omega_arith, hs.al⟩

theorem ofs_reb (S x : Addr) {b : Nat} (hb : b < 2 ^ 64) :
    (b ≤ (x - S).toNat ∧ (x - Mont.off S b).toNat = (x - S).toNat - b) ∨
      ((x - S).toNat < b ∧ 2 ^ 64 - b ≤ (x - Mont.off S b).toNat) :=
  VG.Proof.Bignum.ofs_rebase S x hb

/-- The scratch's first `n` bytes are apart from its `k` at `b`. -/
theorem sepXB {S : Addr} {n b k : Nat} (h : n ≤ b) (hb : b + k ≤ 2 ^ 64) (hk : 0 < k) :
    ∀ x, ofs S x < n → k ≤ ofs (Mont.off S b) x := fun x hx => by
  change (x - S).toNat < n at hx
  change k ≤ (x - Mont.off S b).toNat
  rcases ofs_reb S x (b := b) (by omega) with ⟨_, _⟩ | ⟨_, h2⟩ <;> omega

theorem sepBX {S : Addr} {n b k : Nat} (h : n ≤ b) (hb : b + k ≤ 2 ^ 64) (hk : 0 < k) :
    ∀ x, ofs (Mont.off S b) x < k → n ≤ ofs S x := fun x hx => by
  change (x - Mont.off S b).toNat < k at hx
  change n ≤ (x - S).toNat
  rcases ofs_reb S x (b := b) (by omega) with ⟨_, _⟩ | ⟨_, h2⟩ <;> omega

theorem sepBB {S : Addr} {a n b k : Nat} (h : a + n ≤ b) (hb : b + k ≤ 2 ^ 64) (hk : 0 < k) :
    ∀ x, ofs (Mont.off S a) x < n → k ≤ ofs (Mont.off S b) x := fun x hx => by
  change (x - Mont.off S a).toNat < n at hx
  change k ≤ (x - Mont.off S b).toNat
  rcases ofs_reb S x (b := a) (by omega) with ⟨_, h1⟩ | ⟨_, h1⟩ <;>
    rcases ofs_reb S x (b := b) (by omega) with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega

theorem sepBB' {S : Addr} {a n b k : Nat} (h : a + n ≤ b) (hb : b + k ≤ 2 ^ 64) (hk : 0 < k) :
    ∀ x, ofs (Mont.off S b) x < k → n ≤ ofs (Mont.off S a) x := fun x hx => by
  change (x - Mont.off S b).toNat < k at hx
  change n ≤ (x - Mont.off S a).toNat
  rcases ofs_reb S x (b := a) (by omega) with ⟨_, h1⟩ | ⟨_, h1⟩ <;>
    rcases ofs_reb S x (b := b) (by omega) with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega

/-- A byte within `k` of `b` is within the scratch's `Z`. -/
theorem sepIn {S : Addr} {b k Z : Nat} (h : b + k ≤ Z) (hZ : Z ≤ 2 ^ 64) (hk : 0 < k) :
    ∀ x, ofs (Mont.off S b) x < k → ofs S x < Z := fun x hx => by
  change (x - Mont.off S b).toNat < k at hx
  change (x - S).toNat < Z
  rcases ofs_reb S x (b := b) (by omega) with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega

theorem out_reb {S : Addr} {a o n : Nat} {m m' : Mem} (h : Mont.Outside (Mont.off S a) o n m m')
    (h' : a + o + n ≤ 2 ^ 64) (hn : 0 < n) : Mont.Outside S (a + o) n m m' := fun x hx => h x (by
  change (x - S).toNat < a + o ∨ a + o + n ≤ (x - S).toNat at hx
  change (x - Mont.off S a).toNat < o ∨ o + n ≤ (x - Mont.off S a).toNat
  rcases ofs_reb S x (b := a) (by omega) with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega)

theorem word_off' (m : Mem) (S : Addr) (a d : Nat) : Mont.word m (Mont.off S a) d = Mont.word m S (a + d) := by
  simp only [Mont.word, Mont.off, BitVec.add_assoc, BitVec.ofNat_add]

theorem wordsVal_off (m : Mem) (S : Addr) (a : Nat) : ∀ d k,
    wordsVal m (Mont.off S a) d k = wordsVal m S (a + d) k
  | _, 0 => rfl
  | d, k + 1 => by
    rw [wordsVal, wordsVal, word_off', wordsVal_off m S a (d + 8) k, show a + (d + 8) = a + d + 8 by omega]

theorem wordsOf_le_of {l k : Nat} (h : l ≤ k) (hk : 9 ≤ k) : wordsOf l ≤ (k + 7) / 8 := by
  unfold wordsOf; split <;> omega_arith

/-! ## What the middle changes -/

/-- What the middle changes: the mask's word and the arrays. -/
abbrev midR (Z : Nat) : List (Nat × Nat) := [(oMask, 8), (256, Z - 256)]

/-- Every register but `s6` and `s11`. -/
def crtRegs : List Reg :=
  [.ra, .t0, .t1, .t2, .s0, .s1, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .s2, .s3, .s4, .s5, .s7, .s8, .s9, .s10,
    .t3, .t4, .t5, .t6]

theorem frm_mid {S : Addr} {Z o n : Nat} {m m' : Mem} (h : Mont.Outside S o n m m') (h1 : 256 ≤ o)
    (h2 : o + n ≤ Z) : Frm S (midR Z) m m' :=
  Frm.widen (Frm.of_outside h (List.mem_singleton_self _)) fun r hr => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), h1, by simp only; omega_arith⟩

theorem frm_mid_chk {S : Addr} {Z w : Nat} {m m' : Mem} (h : Frm S (chkR w) m m') (hZ : slot w 8 ≤ Z) :
    Frm S (midR Z) m m' :=
  Frm.widen h fun r hr => by
    have e2 : slot w 2 = 256 + 2 * (8 * (w + 2)) := rfl
    have e8 : slot w 8 = 256 + 8 * (8 * (w + 2)) := rfl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), by simp only; omega_arith,
        by simp only; omega_arith⟩

theorem hdr_mid {S : Addr} {Z : Nat} {m m' : Mem} (h : Frm S (midR Z) m m') (hZ : 256 ≤ Z) {d : Nat}
    (hd : d + 8 ≤ oMask ∨ (oMask + 8 ≤ d ∧ d + 8 ≤ 256)) :
    Mont.word m' S d = Mont.word m S d :=
  have hm : oMask = 88 := rfl
  h.word_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_arith)

theorem inscr_bytes {S A : Addr} {Z L : Nat} {m m' : Mem} (h : VG.Proof.Bignum.InScr S Z m m')
    (hsep : ∀ i < L, ∀ x, ofs S x < Z → Mont.off A i ≠ x) :
    Spec.Rsa.bytesAt m' A L = Spec.Rsa.bytesAt m A L := by
  rw [VG.Proof.Bignum.bytesAt_eq, VG.Proof.Bignum.bytesAt_eq]
  refine List.map_congr_left fun i hi => h _ ?_
  have hi := List.mem_range.mp hi
  by_contra hc
  exact hsep i hi (A + BitVec.ofNat 64 i) (by simp only [VG.Proof.Bignum.ofs] at hc ⊢; omega) rfl

theorem inscr_of {s₀ s t : State} (hF : Front s₀ s) (h : Frm (cS s₀) (midR (cZ s₀)) s.mem t.mem)
    (hZ : 256 ≤ cZ s₀) : VG.Proof.Bignum.InScr (cS s₀) (cZ s₀) s₀.mem t.mem :=
  have hm : oMask = 88 := rfl
  (VG.Proof.Bignum.InScr.of_outside hF.mem hZ).trans (VG.Proof.Bignum.InScr.of_frm h fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith)

/-- After the powers, from the state `s` the front leaves. -/
structure M1 (s₀ s t : State) : Prop where
  s6 : t.gpr .s6 = cS s₀
  s11 : t.gpr .s11 = BitVec.ofNat 64 (8 * (cwX s₀ + 2))
  a7 : t.gpr .a7 = Mont.off (Mont.off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 0)
  s5 : t.gpr .s5 = BitVec.ofNat 64 (8 * (cwQ s₀ + 2))
  x0 : wordsVal t.mem (cS s₀) (slot (cwX s₀) 0) (cwX s₀) = 2 ^ (64 * cwX s₀) - 1
  x5 : wordsVal t.mem (cS s₀) (slot (cwX s₀) 5) (cwX s₀) = mQ s₀
  x7 : wordsVal t.mem (cS s₀) (slot (cwX s₀) 7) (cwX s₀) = mQI s₀
  p0 : wordsVal t.mem (Mont.off (cS s₀) (oPa s₀)) (slot (cwP s₀) 0) (cwP s₀) = mP s₀
  p4 : wordsVal t.mem (Mont.off (cS s₀) (oPa s₀)) (slot (cwP s₀) 4) (cwP s₀) = vm1 s₀
  q4 : wordsVal t.mem (Mont.off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 4) (cwQ s₀) = vm2 s₀
  msk : Mont.word t.mem (cS s₀) oMask = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if cb s₀ then 1 else 0)
  fr : Frm (cS s₀) (midR (cZ s₀)) s.mem t.mem
  keep : Keep crtRegs s t

theorem mid1_ok {s₀ s : State} {c : Prog isa} {Q : State → Prop} (hP : PF s₀) (hF : Front s₀ s)
    (hc : ∀ t, M1 s₀ s t → WP isa c t Q) :
    WP isa (.seq loadX (.seq checks (.seq loadIn (.seq (.block (setupP oBP oPLen)) (.seq (power 4 oDP oPLen)
      (.seq (.block (setupP oBQ oQLen)) (.seq (power 5 oDQ oQLen) c))))))) s Q := by
  have hn := hP.nw
  have room := hP.room
  have k64 := hP.k64; have k1024 := hP.k1024; have p1 := hP.p1; have pk := hP.pk; have q1 := hP.q1
  have qk := hP.qk
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have eX0 := e (cwX s₀) 0; have eX1 := e (cwX s₀) 1; have eX4 := e (cwX s₀) 4; have eX5 := e (cwX s₀) 5
  have eX6 := e (cwX s₀) 6; have eX7 := e (cwX s₀) 7; have eX8 := e (cwX s₀) 8; have eX2 := e (cwX s₀) 2
  have eP0 := e (cwP s₀) 0; have eP4 := e (cwP s₀) 4; have eP24 := e (cwP s₀) 24
  have eQ0 := e (cwQ s₀) 0; have eQ4 := e (cwQ s₀) 4; have eQ24 := e (cwQ s₀) 24
  have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
  have doP : oPa s₀ = slot (cwX s₀) 8 := rfl
  have dP : cwP s₀ = wordsOf (cpL s₀) := rfl
  have dQ : cwQ s₀ = wordsOf (cqL s₀) := rfl
  have doQ : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 24 := rfl
  have room' : oPa s₀ + slot (cwP s₀) 24 + slot (cwQ s₀) 24 ≤ cZ s₀ := room
  have hwP2 : 2 ≤ cwP s₀ := two_le_wordsOf
  have hwQ2 : 2 ≤ cwQ s₀ := two_le_wordsOf
  have hwPK : cwP s₀ ≤ (ck s₀ + 7) / 8 := wordsOf_le_of (Nat.le_of_lt pk) (by omega_arith)
  have hwQK : cwQ s₀ ≤ (ck s₀ + 7) / 8 := wordsOf_le_of (Nat.le_of_lt qk) (by omega_arith)
  have hpw : cpL s₀ ≤ 8 * cwP s₀ := by have := wordsOf_ge (l := cpL s₀); omega_arith
  have hqw : cqL s₀ ≤ 8 * cwQ s₀ := by have := wordsOf_ge (l := cqL s₀); omega_arith
  have hwX : cwX s₀ < 2 ^ 31 := by omega_arith
  have hZ256 : 256 ≤ cZ s₀ := by omega_arith
  have hS256 : (cS s₀).toNat + 256 ≤ 2 ^ 64 := by omega_arith
  obtain ⟨mP1, mPo, mQ1, mQo, mPb, mQb, mQIP, mQIb⟩ := masked_facts hP
  have k0 := hF.keep
  have rd0 : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [k0.2.1, k0.2.2]
  have hb0 : ∀ {A : Addr} {L : Nat}, (∀ i < L, ∀ x, ofs (cS s₀) x < cZ s₀ → Mont.off A i ≠ x) →
      Spec.Rsa.bytesAt s.mem A L = Spec.Rsa.bytesAt s₀.mem A L := fun hs' => bytesAt_out hF.mem hZ256 hs'
  -- `X`'s arrays.
  refine WP.seq (WP.mono (loadX_ok (Na := s₀.gpr .a2) (Pa := s₀.gpr .a6) (Qa := stackArg s₀ 0) (Ia := s₀.gpr .a4)
    (QIa := stackArg s₀ 6) hF.scr (by omega_arith) (by omega_arith) hwX (by rw [hF.s6]; exact z0 _) hF.a7 hF.ra hF.s5
    hF.t0 hF.hN hF.hNL hF.hP hF.hPL hF.hQ hF.hQL hF.hIn hF.hQI (by omega_arith) (by omega_arith) p1
    (by omega_arith) q1 (by omega_arith)
    ⟨by rw [rd0]; exact hP.rN, hP.sN⟩ ⟨by rw [rd0]; exact hP.rP, hP.sP⟩ ⟨by rw [rd0]; exact hP.rQ, hP.sQ⟩
    ⟨by rw [rd0]; exact hP.rI, hP.sI⟩ ⟨by rw [rd0]; exact hP.rQI, hP.sQI⟩)
    fun t₁ ⟨⟨v0, w0, v1, v4, v5, v6, v7, t1, t4, t5, t6, t7, O1, a7₁⟩, k1⟩ => ?_)
  rw [hb0 hP.sN, hb0 hP.sP, hb0 hP.sQ, hb0 hP.sI, hb0 hP.sQI] at *
  have F1 : Frm (cS s₀) (midR (cZ s₀)) s.mem t₁.mem := frm_mid O1 (Nat.le_refl _) (by omega_arith)
  have I1 := inscr_of hF F1 hZ256
  have hd1 : ∀ d, d + 8 ≤ oMask ∨ (oMask + 8 ≤ d ∧ d + 8 ≤ 256) → Mont.word t₁.mem (cS s₀) d = Mont.word s.mem (cS s₀) d :=
    fun d hd => hdr_mid F1 hZ256 hd
  have hQb := os2ip_lt' (Spec.Rsa.bytesAt s₀.mem (stackArg s₀ 0) (cqL s₀)) (VG.Proof.Bignum.bytesAt_length _ _ _)
  have hPb := os2ip_lt' (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .a6) (cpL s₀)) (VG.Proof.Bignum.bytesAt_length _ _ _)
  have hw16 : 16 * ck s₀ ≤ 64 * cwX s₀ := by omega_arith
  -- The checks.
  refine WP.seq (WP.mono (checks_ok (Na := s₀.gpr .a2) (k := ck s₀) (nb := Spec.Rsa.bytesAt s₀.mem (s₀.gpr .a2) (ck s₀))
    (hF.scr.congr k1.2.2) (by omega_arith) (by omega_arith) hwX ((k1.gpr (by decide)).trans hF.s6) a7₁
    ((k1.gpr (by decide)).trans hF.ra) ((k1.gpr (by decide)).trans hF.s5) ((k1.gpr (by decide)).trans hF.t0)
    (by rw [hd1 _ (by unfold oN oMask; omega_arith)]; exact hF.hN)
    (by rw [hd1 _ (by unfold oNLen oMask; omega_arith)]; exact hF.hNL) k64 k1024
    (VG.Proof.Bignum.bytesAt_length _ _ _) (fun i hi => by rw [k1.2.1, k1.2.2, rd0]; exact hP.rN i hi)
    (fun i hi => by
      rw [I1 (Mont.off (s₀.gpr .a2) i) (by by_contra hc; exact hP.sN i hi (Mont.off (s₀.gpr .a2) i) (by omega_arith) rfl)]
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range])
    v0 w0 v1 t1 t6 t7
    (by rw [v5]; have := pq_lt (P := 1) (pL := 1) (by
        rw [VG.Proof.Bignum.pow256_eq]; exact Nat.one_lt_two_pow (by omega_arith)) hQb (by omega_arith) qk hw16
        omega_arith)
    (by rw [v4, v5]; exact pq_lt hPb hQb pk qk hw16))
    fun t₂ ⟨X2, k2⟩ => ?_)
  rw [v6, v4, v5, v7] at X2
  have k12 := k1.trans k2
  have F2 : Frm (cS s₀) (midR (cZ s₀)) s.mem t₂.mem := F1.trans (frm_mid_chk X2.fr (by omega_arith))
  have I2 := inscr_of hF F2 hZ256
  have hd2 : ∀ d, d + 8 ≤ oMask ∨ (oMask + 8 ≤ d ∧ d + 8 ≤ 256) → Mont.word t₂.mem (cS s₀) d = Mont.word s.mem (cS s₀) d :=
    fun d hd => hdr_mid F2 hZ256 hd
  have hwo : ∀ {m m' : Mem} {o n : Nat}, Mont.Outside (cS s₀) o n m m' → ∀ {j}, j < 8 →
      (slot (cwX s₀) j + 8 * cwX s₀ ≤ o ∨ o + n ≤ slot (cwX s₀) j) →
      wordsVal m' (cS s₀) (slot (cwX s₀) j) (cwX s₀) = wordsVal m (cS s₀) (slot (cwX s₀) j) (cwX s₀) :=
    fun h j hj hd => Mont.Outside.wordsVal h hd (by have := VG.Proof.Bignum.slot_le (w := cwX s₀) hj; omega_arith)
  -- The input again.
  refine WP.seq (WP.mono (loadOne_ok (j := 6) (A := s₀.gpr .a4) (L := ck s₀) (oA := oIn) (oL := oNLen)
    (hF.scr.congr k12.2.2) (by omega_arith) (by decide) hwX (by rw [k12.gpr (by decide), hF.s6]; exact z0 _) X2.a7
    ((k12.gpr (by decide)).trans hF.ra) ((k12.gpr (by decide)).trans hF.s5) ((k12.gpr (by decide)).trans hF.t0)
    (by decide) (by decide) (by rw [hd2 _ (by unfold oIn oMask; omega_arith)]; exact hF.hIn)
    (by rw [hd2 _ (by unfold oNLen oMask; omega_arith)]; exact hF.hNL) (by omega_arith) (by omega_arith)
    ⟨by rw [k12.2.1, k12.2.2, rd0]; exact hP.rI, hP.sI⟩)
    fun t₃ ⟨⟨v6', _, O3, a7₃⟩, k3⟩ => ?_)
  rw [inscr_bytes I2 hP.sI] at v6'
  have k13 := k12.trans k3
  have F3 : Frm (cS s₀) (midR (cZ s₀)) s.mem t₃.mem := F2.trans (frm_mid O3 (by omega_arith) (by omega_arith))
  have I3 := inscr_of hF F3 hZ256
  have hd3 : ∀ d, d + 8 ≤ oMask ∨ (oMask + 8 ≤ d ∧ d + 8 ≤ 256) → Mont.word t₃.mem (cS s₀) d = Mont.word s.mem (cS s₀) d :=
    fun d hd => hdr_mid F3 hZ256 hd
  -- `p`'s working space.
  refine WP.seq (WP.mono (setupP_ok (l := cpL s₀) (Bp := Mont.off (cS s₀) (oPa s₀)) (hF.scr.congr k13.2.2)
    (by rw [k13.gpr (by decide), hF.s6]; exact z0 _) (by unfold oBP; omega_arith) (by decide) (by decide)
    (by unfold oPLen; omega_arith) (by decide) (by decide) (by rw [hd3 _ (by unfold oBP oMask; omega_arith)]; exact hF.hBP)
    (by rw [hd3 _ (by unfold oPLen oMask; omega_arith)]; exact hF.hPL) p1 (by omega_arith))
    fun t₄ ⟨⟨p7, pra, p5, p0', _, m4⟩, k4⟩ => ?_)
  have k14 := k13.trans k4
  have hK : 1 ≤ (ck s₀ + 7) / 8 := by omega_arith
  have nP1 := le_nChunks_mul (K := (ck s₀ + 7) / 8) (w := cwP s₀) (by omega_arith)
  have nP2 := nChunks_mul_lt (K := (ck s₀ + 7) / 8) (w := cwP s₀) (by omega_arith) hK
  have nQ1 := le_nChunks_mul (K := (ck s₀ + 7) / 8) (w := cwQ s₀) (by omega_arith)
  have nQ2 := nChunks_mul_lt (K := (ck s₀ + 7) / 8) (w := cwQ s₀) (by omega_arith) hK
  rw [Nat.mul_comm] at nP1 nP2 nQ1 nQ2
  have hCb : vC s₀ < 2 ^ (64 * ((ck s₀ + 7) / 8)) :=
    Nat.lt_of_lt_of_le (os2ip_lt' _ (VG.Proof.Bignum.bytesAt_length _ _ _)) (pow256_le (by omega_arith))
  have hS4 : Scr t₄ (Mont.off (cS s₀) (oPa s₀)) (slot (cwP s₀) 24) :=
    Scr.sub (hF.scr.congr k14.2.2) (by omega_arith) (slot_al _ _) (by omega_arith)
  -- `m₁`.
  refine WP.seq (WP.mono (power_ok (xj := 4) (k := ck s₀) (L := cpL s₀) (Pv := mP s₀) (Cv := vC s₀)
    (D := stackArg s₀ 2) hS4 hwP2 (by omega_arith) (Nat.le_refl _) p7 pra p5 p0'
    (Scr.le (hF.scr.congr k14.2.2) (show slot (cwX s₀) 8 ≤ cZ s₀ by omega_arith))
    (sepXB (Nat.le_refl _) (by omega_arith) (by omega_arith)) ((k14.gpr (by decide)).trans hF.s6)
    ((k14.gpr (by decide)).trans hF.s11) (by omega_arith)
    (wordsVal_trunc (by rw [m4, hwo O3 (j := 4) (by decide) (Or.inl (by omega_arith)), X2.v4, v4])
      (Nat.lt_of_lt_of_le mPb (pow256_le hpw)) (by omega_arith)) mP1 mPo
    (by rw [m4, hd3 _ (by unfold oNLen oMask; omega_arith)]; exact hF.hNL) (by omega_arith) (by omega_arith)
    (by omega_arith)
    (wordsVal_trunc (by rw [m4]; exact v6') (Nat.lt_of_lt_of_le hCb (Nat.pow_le_pow_right (by decide)
      (by omega_arith))) (by omega_arith))
    (by unfold oDP; omega_arith) (by decide) (by decide) (by unfold oPLen; omega_arith) (by decide) (by decide)
    (by rw [m4, hd3 _ (by unfold oDP oMask; omega_arith)]; exact hF.hDP)
    (by rw [m4, hd3 _ (by unfold oPLen oMask; omega_arith)]; exact hF.hPL) p1 (by omega_arith)
    (by rw [k14.2.1, k14.2.2, rd0]; exact hP.rDP)
    (fun i hi x hx => hP.sDP i hi x (sepIn (show oPa s₀ + slot (cwP s₀) 24 ≤ cZ s₀ by omega_arith) (by omega_arith)
      (by omega_arith) x hx)))
    fun t₅ ⟨⟨m1v, p0v, PF5, a7₅⟩, k5⟩ => ?_)
  rw [m4, inscr_bytes I3 hP.sDP] at m1v
  have k15 := k14.trans k5
  have O5 : Mont.Outside (cS s₀) (oPa s₀ + slot (cwP s₀) 0) (24 * (8 * (cwP s₀ + 2))) t₄.mem t₅.mem :=
    out_reb PF5 (by omega_arith) (by omega_arith)
  rw [m4] at O5
  have F5 : Frm (cS s₀) (midR (cZ s₀)) s.mem t₅.mem := F3.trans (frm_mid O5 (by omega_arith) (by omega_arith))
  have I5 := inscr_of hF F5 hZ256
  have hd5 : ∀ d, d + 8 ≤ oMask ∨ (oMask + 8 ≤ d ∧ d + 8 ≤ 256) → Mont.word t₅.mem (cS s₀) d = Mont.word s.mem (cS s₀) d :=
    fun d hd => hdr_mid F5 hZ256 hd
  -- `q`'s working space.
  refine WP.seq (WP.mono (setupP_ok (l := cqL s₀) (Bp := Mont.off (cS s₀) (oQa s₀)) (hF.scr.congr k15.2.2)
    (by rw [k15.gpr (by decide), hF.s6]; exact z0 _) (by unfold oBQ; omega_arith) (by decide) (by decide)
    (by unfold oQLen; omega_arith) (by decide) (by decide) (by rw [hd5 _ (by unfold oBQ oMask; omega_arith)]; exact hF.hBQ)
    (by rw [hd5 _ (by unfold oQLen oMask; omega_arith)]; exact hF.hQL) q1 (by omega_arith))
    fun t₆ ⟨⟨q7, qra, q5, q0', _, m6⟩, k6⟩ => ?_)
  have k16 := k15.trans k6
  have hS6 : Scr t₆ (Mont.off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 24) :=
    Scr.sub (hF.scr.congr k16.2.2) (by omega_arith) (by have := slot_al (cwX s₀) 8; have := slot_al (cwP s₀) 24; omega_arith)
      (by omega_arith)
  -- `m₂`.
  refine WP.seq (WP.mono (power_ok (xj := 5) (k := ck s₀) (L := cqL s₀) (Pv := mQ s₀) (Cv := vC s₀)
    (D := stackArg s₀ 4) hS6 hwQ2 (by omega_arith) (Nat.le_refl _) q7 qra q5 q0'
    (Scr.le (hF.scr.congr k16.2.2) (show slot (cwX s₀) 8 ≤ cZ s₀ by omega_arith))
    (sepXB (by omega_arith) (by omega_arith) (by omega_arith)) ((k16.gpr (by decide)).trans hF.s6)
    ((k16.gpr (by decide)).trans hF.s11) (by omega_arith)
    (wordsVal_trunc (by rw [m6, hwo O5 (j := 5) (by decide) (Or.inl (by omega_arith)),
        hwo O3 (j := 5) (by decide) (Or.inl (by omega_arith)), X2.v5, v5])
      (Nat.lt_of_lt_of_le mQb (pow256_le hqw)) (by omega_arith)) mQ1 mQo
    (by rw [m6, hd5 _ (by unfold oNLen oMask; omega_arith)]; exact hF.hNL) (by omega_arith) (by omega_arith)
    (by omega_arith)
    (wordsVal_trunc (by rw [m6, hwo O5 (j := 6) (by decide) (Or.inl (by omega_arith))]; exact v6')
      (Nat.lt_of_lt_of_le hCb (Nat.pow_le_pow_right (by decide) (by omega_arith))) (by omega_arith))
    (by unfold oDQ; omega_arith) (by decide) (by decide) (by unfold oQLen; omega_arith) (by decide) (by decide)
    (by rw [m6, hd5 _ (by unfold oDQ oMask; omega_arith)]; exact hF.hDQ)
    (by rw [m6, hd5 _ (by unfold oQLen oMask; omega_arith)]; exact hF.hQL) q1 (by omega_arith)
    (by rw [k16.2.1, k16.2.2, rd0]; exact hP.rDQ)
    (fun i hi x hx => hP.sDQ i hi x (sepIn (show oQa s₀ + slot (cwQ s₀) 24 ≤ cZ s₀ by omega_arith) (by omega_arith)
      (by omega_arith) x hx)))
    fun t₇ ⟨⟨m2v, _, PF7, a7₇⟩, k7⟩ => ?_)
  rw [m6, inscr_bytes I5 hP.sDQ] at m2v
  have k17 := k16.trans k7
  have O7 : Mont.Outside (cS s₀) (oQa s₀ + slot (cwQ s₀) 0) (24 * (8 * (cwQ s₀ + 2))) t₆.mem t₇.mem :=
    out_reb PF7 (by omega_arith) (by omega_arith)
  rw [m6] at O7
  have F7 : Frm (cS s₀) (midR (cZ s₀)) s.mem t₇.mem := F5.trans (frm_mid O7 (by omega_arith) (by omega_arith))
  have hm : oMask = 88 := rfl
  refine hc t₇ ⟨(k17.gpr (by decide)).trans hF.s6, (k17.gpr (by decide)).trans hF.s11, a7₇,
    (k7.gpr (by decide)).trans q5, ?_, ?_, ?_, ?_, ?_, m2v, ?_, F7, k17.mono (by decide)⟩
  · rw [hwo O7 (j := 0) (by decide) (Or.inl (by omega_arith)), hwo O5 (j := 0) (by decide) (Or.inl (by omega_arith)),
      hwo O3 (j := 0) (by decide) (Or.inl (by omega_arith)),
      frm_wordsVal X2.fr (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_arith)]
    exact v0
  · rw [hwo O7 (j := 5) (by decide) (Or.inl (by omega_arith)), hwo O5 (j := 5) (by decide) (Or.inl (by omega_arith)),
      hwo O3 (j := 5) (by decide) (Or.inl (by omega_arith)), X2.v5, v5]
  · rw [hwo O7 (j := 7) (by decide) (Or.inl (by omega_arith)), hwo O5 (j := 7) (by decide) (Or.inl (by omega_arith)),
      hwo O3 (j := 7) (by decide) (Or.inr (by omega_arith)), X2.v7, v7]
  · rw [wordsVal_off, Mont.Outside.wordsVal O7 (Or.inl (by omega_arith)) (by omega_arith), ← wordsVal_off]
    exact p0v
  · rw [wordsVal_off, Mont.Outside.wordsVal O7 (Or.inl (by omega_arith)) (by omega_arith), ← wordsVal_off]
    exact m1v
  · rw [Mont.Outside.word O7 (Or.inl (by omega_arith)) (by omega_arith),
      Mont.Outside.word O5 (Or.inl (by omega_arith)) (by omega_arith),
      Mont.Outside.word O3 (Or.inl (by omega_arith)) (by omega_arith)]
    exact X2.msk

end VG.Proof.Bignum.RISCV64.Crt
