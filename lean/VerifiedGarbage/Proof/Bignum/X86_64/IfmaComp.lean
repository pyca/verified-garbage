import VerifiedGarbage.Proof.Bignum.X86_64.IfmaGlue
import VerifiedGarbage.Proof.Bignum.X86_64.IfmaVecR

/-!
# RSA with AVX512_IFMA on x86-64: `ifma`

`ifma_ok`: the IFMA area after `q`'s workspace, both regions, the vector
code, and the results back in the primes' workspaces.

`IMem` gathers what holds throughout: `n`'s header, the primes' headers
(their workspace slots, `sMaskX` and `sIfma`), moduli and ones, and `n`'s
slots for the exponents; `IMem.of_frm` keeps it across any change within
`ifmaR`, the ranges `ifma` writes.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.CrtIfma (D oM oK0 oK1 oX oY oE oFin sIfma mask52)

/-- The ranges `ifma` writes, but its first two stores. -/
def ifmaR (op oq a : Nat) : List (Nat × Nat) :=
  shiftRanges op (k1Ranges 16 ++ resRanges) ++ shiftRanges oq (k1Ranges 16 ++ resRanges) ++ [(a, 2 * D + 8)]

/-- What `ifma` keeps. -/
structure IMem (m : Mem) (B : Addr) (w op oq a : Nat) (minv mp mq mk : BitVec 64) (P Q : Nat) (ep eq : Addr)
    (lp lq : Nat) : Prop where
  nh : Hdr m B w minv
  wsP : word m B (8 * sWsP) = off B op
  wsQ : word m B (8 * sWsQ) = off B oq
  pws : WsAt m B op 16 mp
  qws : WsAt m B oq 16 mq
  pn : wv m (off B op) (slot 16 Public.aN) 16 = P
  pinv : ((word m (off B op) (slot 16 Public.aN)).toNat * mp.toNat + 1) % 2 ^ 64 = 0
  pone : wv m (off B op) (slot 16 Public.aOne) 16 = 1
  qn : wv m (off B oq) (slot 16 Public.aN) 16 = Q
  qinv : ((word m (off B oq) (slot 16 Public.aN)).toNat * mq.toNat + 1) % 2 ^ 64 = 0
  qone : wv m (off B oq) (slot 16 Public.aOne) 16 = 1
  pia : word m (off B op) (8 * sIfma) = off B a
  qia : word m (off B oq) (8 * sIfma) = off B a
  pmk : word m (off B op) (8 * sMaskX) = mk
  dp : word m B (8 * sDp) = ep
  pl : word m B (8 * sPlen) = BitVec.ofNat 64 lp
  dq : word m B (8 * sDq) = eq
  ql : word m B (8 * sQlen) = BitVec.ofNat 64 lq

/-- What `IMem` reads: below `p`'s workspace, the first 30 slots of a
prime's header, and its modulus and one. -/
def IKept (op oq d n : Nat) : Prop :=
  d + n ≤ op ∨ (op ≤ d ∧ d + n ≤ op + 8 * 30) ∨ (d = op + slot 16 Public.aN ∧ n ≤ 128) ∨
    (d = op + slot 16 Public.aOne ∧ n ≤ 128) ∨ (oq ≤ d ∧ d + n ≤ oq + 8 * 30) ∨
    (d = oq + slot 16 Public.aN ∧ n ≤ 128) ∨ (d = oq + slot 16 Public.aOne ∧ n ≤ 128)

theorem ifmaR_disj {op oq a d n : Nat} (hpq : op + slot 16 8 + tabBytes 16 ≤ oq)
    (hqa : oq + slot 16 8 + tabBytes 16 ≤ a) (h : IKept op oq d n) :
    ∀ r ∈ ifmaR op oq a, d + n ≤ r.1 ∨ r.1 + r.2 ≤ d := by
  have hT : tabBytes 16 = 2304 := rfl
  have hs : ∀ j, slot 16 j = 256 + j * 144 := fun j => by unfold slot hdrBytes; omega
  simp only [IKept, Public.aN, Public.aOne, hs] at h
  simp only [ifmaR, shiftRanges, k1Ranges, resRanges, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, CrtIfma.sCtr, sFn, hs,
    Public.aAcc, Public.aTmp, Public.aY, aT] at hpq hqa ⊢
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only <;> omega

theorem IMem.of_frm {m m' : Mem} {B : Addr} {w op oq a : Nat} {minv mp mq mk : BitVec 64} {P Q : Nat}
    {ep eq : Addr} {lp lq : Nat} (h : IMem m B w op oq a minv mp mq mk P Q ep eq lp lq)
    (hf : Frm B (ifmaR op oq a) m m') (hlo : slot w 8 ≤ op) (hpq : op + slot 16 8 + tabBytes 16 ≤ oq)
    (hqa : oq + slot 16 8 + tabBytes 16 ≤ a) (hz : a + 2 * D + 8 ≤ 2 ^ 64) :
    IMem m' B w op oq a minv mp mq mk P Q ep eq lp lq := by
  have hD : D = 3712 := rfl
  have hT : tabBytes 16 = 2304 := rfl
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have h16 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have := slot_le (w := 16) (show Public.aN < 8 by decide)
  have := slot_le (w := 16) (show Public.aOne < 8 by decide)
  have hW : ∀ d, IKept op oq d 8 → word m' B d = word m B d := fun d hk =>
    hf.word_eq (ifmaR_disj hpq hqa hk) (by unfold IKept at hk; unfold slot hdrBytes at h16; omega)
  have hV : ∀ d, IKept op oq d 128 → wv m' B d 16 = wv m B d 16 := fun d hk =>
    hf.wv_eq (ifmaR_disj hpq hqa hk) (by unfold IKept at hk; unfold slot hdrBytes at h16; omega)
  have hn : ∀ i < 32, word m' B (8 * i) = word m B (8 * i) := fun i hi => hW _ (.inl (by omega))
  have hp : ∀ i < 30, word m' (off B op) (8 * i) = word m (off B op) (8 * i) := fun i hi => by
    rw [word_off, word_off]; exact hW _ (.inr (.inl ⟨by omega, by omega⟩))
  have hq : ∀ i < 30, word m' (off B oq) (8 * i) = word m (off B oq) (8 * i) := fun i hi => by
    rw [word_off, word_off]; exact hW _ (.inr (.inr (.inr (.inr (.inl ⟨by omega, by omega⟩)))))
  have hpn : wv m' (off B op) (slot 16 Public.aN) 16 = wv m (off B op) (slot 16 Public.aN) 16 := by
    rw [wv_off, wv_off]; exact hV _ (.inr (.inr (.inl ⟨rfl, le_refl _⟩)))
  have hqn : wv m' (off B oq) (slot 16 Public.aN) 16 = wv m (off B oq) (slot 16 Public.aN) 16 := by
    rw [wv_off, wv_off]; exact hV _ (.inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, le_refl _⟩))))))
  refine ⟨⟨(hn _ (by decide)).trans h.nh.hw, (hn _ (by decide)).trans h.nh.hminv,
      fun j hj => (hn _ (by unfold sArr; omega)).trans (h.nh.harr j hj)⟩,
    (hn _ (by decide)).trans h.wsP, (hn _ (by decide)).trans h.wsQ,
    h.pws.of_words fun i hi => hp i (by omega), h.qws.of_words fun i hi => hq i (by omega),
    hpn.trans h.pn, ?_, ?_, hqn.trans h.qn, ?_, ?_, (hp _ (by decide)).trans h.pia,
    (hq _ (by decide)).trans h.qia, (hp _ (by decide)).trans h.pmk, (hn _ (by decide)).trans h.dp,
    (hn _ (by decide)).trans h.pl, (hn _ (by decide)).trans h.dq, (hn _ (by decide)).trans h.ql⟩
  · rw [word_off, hW _ (.inr (.inr (.inl ⟨rfl, by decide⟩))), ← word_off]; exact h.pinv
  · rw [wv_off, hV _ (.inr (.inr (.inr (.inl ⟨rfl, le_refl _⟩)))), ← wv_off]; exact h.pone
  · rw [word_off, hW _ (.inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, by decide⟩)))))), ← word_off]; exact h.qinv
  · rw [wv_off, hV _ (.inr (.inr (.inr (.inr (.inr (.inr ⟨rfl, le_refl _⟩)))))), ← wv_off]; exact h.qone

end VG.Proof.Bignum.X86_64
