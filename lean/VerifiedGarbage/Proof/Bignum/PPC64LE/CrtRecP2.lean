module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtRecP1
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtAdd
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCheck
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The RSA private-key operation on PPC64LE: `m₁ - m₂ mod p`

`recP2a_ok`: in `p`'s working space, `(m₁ + p - b) mod p` into array 3, for
`m₁` in array 4 and `b` in array 1, both below `p`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- A subtraction with its borrow, and the modulus added back under it. -/
theorem subAdd_val {A B P T T' N c : Nat} (hA : A < P) (hB : B < P) (hP : P < 2 ^ N) (hc : c ≤ 1)
    (hT : T < 2 ^ N) (h : T + B = A + 2 ^ N * c) (h' : T' = (T + (if 0 < c then P else 0)) % 2 ^ N) :
    T' = (A + P - B) % P := by
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
  · simp only [Nat.lt_irrefl, ite_false, Nat.add_zero] at h'
    rw [Nat.mul_zero, Nat.add_zero] at h
    rw [h', Nat.mod_eq_of_lt hT, show A + P - B = (A - B) + P by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
    omega
  · simp only [Nat.zero_lt_one, ite_true] at h'
    rw [Nat.mul_one] at h
    rw [h', show T + P = (A + P - B) + 2 ^ N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]

/-- `recombineP`'s middle: `(m₁ + p - b) mod p` into array 3, changing only
arrays 3 and 4 (above `m₁`). -/
theorem recP2a_ok {s : State} {B : Addr} {Z w Pv m1 b : Nat} {c : Prog isa} {Q : State → Prop}
    (hs : Scr s B Z) (hZ : slot w 8 ≤ Z) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (h10 : s.gpr .r10 = off B (slot w 0)) (h21 : s.gpr .r21 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hP : val32 s.mem B (slot w 0) (2 * w) = Pv) (hb : val32 s.mem B (slot w 1) (2 * w) = b)
    (hm1 : val32 s.mem B (slot w 4) (2 * w) = m1) (hbP : b < Pv) (hm1P : m1 < Pv)
    (hc : ∀ t, val32 t.mem B (slot w 3) (2 * w) = (m1 + Pv - b) % Pv →
      Outs B [(slot w 3, 8 * (w + 2)), (slot w 4, 8 * (w + 2))] s.mem t.mem →
      t.gpr .r10 = off B (slot w 0) → Keep [.r0, .r3, .r8, .r9, .r10, .r14, .r15, .r16, .r17, .r20, .r24] s t → WP isa c t Q) :
    WP isa (.seq (.block (PublicChecked.base .r14 4 ++ [.add .r14 .r14 .r29, .subi .r14 .r14 16, .li .r0 0,
      .store .d .r0 .r14 0] ++ PublicChecked.base .r8 4 ++ PublicChecked.base .r9 3 ++
      PublicChecked.base .r10 1)) (.seq subMod (.seq (.block ([.addi .r10 .r21 0] ++
      PublicChecked.base .r15 3 ++ PublicChecked.base .r16 0)) (.seq addMask c)))) s Q := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e3 := e 3; have e4 := e 4; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) h10 h29 4) fun s₁ ⟨⟨a14, m1'⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r14, .r0] (Q := fun t =>
    t.mem = s₁.mem.writeW (off B (slot w 4 + 8 * w)) (0 : BitVec 64)) ?_ (by decide)) fun s₂ ⟨m2', k2⟩ => ?_
  · have e16 : off B (slot w 4 + 8 * (w + 2)) - BitVec.ofNat 64 16 = off B (slot w 4 + 8 * w) := by
      rw [off, VG.Offset.add_ofNat_sub B (show 16 ≤ slot w 4 + 8 * (w + 2) by omega)]; congr 2
    prun [a14, (k1.gpr .r29 (by decide)).trans h29, off_add, e16,
      (hs.congr k1.wr).st (show slot w 4 + 8 * w + 8 ≤ Z by omega)]
    rfl
  have k12 := k1.trans k2
  rw [m1'] at m2'
  have ow := writeW_outside s.mem B (d := slot w 4 + 8 * w) (0 : BitVec 64) (by omega)
  have ow' : Mont.Outside B (slot w 4 + 8 * w) 8 s.mem s₂.mem := by rw [m2']; exact fun x hx => ow x hx
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r8) (by decide) (by decide) ((k12.gpr _ (by decide)).trans h10)
    ((k12.gpr _ (by decide)).trans h29) 4) fun s₃ ⟨⟨a8, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r9) (by decide) (by decide) ((k13.gpr _ (by decide)).trans h10)
    ((k13.gpr _ (by decide)).trans h29) 3) fun s₄ ⟨⟨a9, m4⟩, k4⟩ => ?_
  have k14 := k13.trans k4
  refine WP.mono (Pub.base_ok (rd := .r10) (by decide) (by decide) ((k14.gpr _ (by decide)).trans h10)
    ((k14.gpr _ (by decide)).trans h29) 1) fun s₅ ⟨⟨a10, m5⟩, k5⟩ => ?_
  have k15 := k14.trans k5
  have hm5 : s₅.mem = s₂.mem := by rw [m5, m4, m3]
  refine WP.seq (WP.mono (subMod_ok (n := 2 * w) (dA := slot w 4) (dT := slot w 3) (dM := slot w 1)
    (hs.congr k15.wr) ((k5.gpr _ (by decide)).trans ((k4.gpr _ (by decide)).trans a8))
    ((k5.gpr _ (by decide)).trans a9) a10
    ((k15.gpr _ (by decide)).trans h11) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)) fun s₆ ⟨⟨cc, hcc, hD, h20⟩, out6, k6⟩ => ?_)
  have k16 := k15.trans k6
  rw [hm5] at hD h20 out6
  have v1 : val32 s₂.mem B (slot w 1) (2 * w) = b := by rw [ow'.val32 (Or.inl (by omega)) (by omega), hb]
  have v4 : val32 s₂.mem B (slot w 4) (2 * w) = m1 := by rw [ow'.val32 (Or.inl (by omega)) (by omega), hm1]
  have v0 : val32 s₂.mem B (slot w 0) (2 * w) = Pv := by rw [ow'.val32 (Or.inl (by omega)) (by omega), hP]
  have h0 : w32 s₂.mem B (slot w 4 + 4 * (2 * w)) = 0 := by
    have := word_eq_w32 s₂.mem B (slot w 4 + 8 * w)
    rw [show Mont.word s₂.mem B (slot w 4 + 8 * w) = 0 by rw [m2']; exact word_writeW_self _ _ _ _,
      show (0 : BitVec 64).toNat = 0 from rfl, show slot w 4 + 8 * w = slot w 4 + 4 * (2 * w) by omega] at this
    omega
  rw [v1, v4] at hD
  rw [h0] at h20
  have out6' : Mont.Outside B (slot w 3) (4 * (2 * w)) s₂.mem s₆.mem := fun x hx => out6 x hx
  have v0' : val32 s₆.mem B (slot w 0) (2 * w) = Pv := by rw [out6'.val32 (Or.inl (by omega)) (by omega), v0]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r10] (Q := fun t => t.gpr .r10 = off B (slot w 0) ∧ t.mem = s₆.mem)
    (by prun [(k16.gpr .r21 (by decide)).trans h21]) (by decide)) fun s₇ ⟨⟨a10', m7⟩, k7⟩ => ?_
  have k17 := k16.trans k7
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r15) (by decide) (by decide) a10' ((k17.gpr _ (by decide)).trans h29) 3)
    fun s₈ ⟨⟨a15, m8⟩, k8⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .r16) (by decide) (by decide) ((k8.gpr _ (by decide)).trans a10')
    (((k17.trans k8).gpr _ (by decide)).trans h29) 0) fun s₉ ⟨⟨a16, m9⟩, k9⟩ => ?_
  have k19 := (k17.trans k8).trans k9
  have hm9 : s₉.mem = s₆.mem := by rw [m9, m8, m7]
  refine WP.seq (WP.mono (addMask_ok (b := decide (0 < cc)) (n := 2 * w) (dT := slot w 3) (dM := slot w 0)
    (hs.congr k19.wr) ((k9.gpr _ (by decide)).trans a15) a16 ((k19.gpr _ (by decide)).trans h11)
    (by rw [k9.gpr _ (by decide), k8.gpr _ (by decide), k7.gpr _ (by decide), h20]; simp only [decide_eq_true_eq])
    (by omega) (by omega) (by omega) (by omega) (by omega)) fun t ⟨hT, outT, kT⟩ => ?_)
  rw [hm9, v0'] at hT
  rw [hm9] at outT
  have hval : val32 t.mem B (slot w 3) (2 * w) = (m1 + Pv - b) % Pv := by
    refine subAdd_val hm1P hbP (by rw [← v0]; exact val32_lt _ _ _ _) hcc (val32_lt _ _ _ _) hD ?_
    rw [hT]; simp only [decide_eq_true_eq]
  refine hc t hval ?_ ((kT.gpr _ (by decide)).trans ((k9.gpr _ (by decide)).trans ((k8.gpr _ (by decide)).trans a10')))
    (k19.trans kT).mono
  intro x hx
  have h3 := hx _ (List.mem_cons_self ..)
  have h4 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have h3' : ofs B x < slot w 3 ∨ slot w 3 + 8 * (w + 2) ≤ ofs B x := h3
  have h4' : ofs B x < slot w 4 ∨ slot w 4 + 8 * (w + 2) ≤ ofs B x := h4
  rw [outT x (by omega), out6 x (by omega), m2', ow x (by omega)]

end VG.Proof.Bignum.PPC64LE.Crt
