module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Verify
import VerifiedGarbage.Proof.Framework.Offset

/-!
# DSA on PPC64LE: the pointers

Each block (`ptrP`, `ptrQ`, …) computes a pointer into `r12` and a length
into `r6` from the registers `Regs` describes.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Verify

theorem off_off (p : Addr) (a b : Nat) : off (off p a) b = off p (a + b) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

theorem off_ofNat_add (p : Addr) (a b : Nat) : p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = off p (a + b) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

/-- `ptrP`: the key, `p_len`. -/
theorem ptrP_ok {s : State} {L : Lay} {key sig dig : Addr} (hr : Regs s L key sig dig) :
    WP isa (.block ptrP) s fun t =>
      (t.gpr .r12 = key ∧ t.gpr .r6 = BitVec.ofNat 64 L.pl ∧ t.mem = s.mem) ∧ Keep [.r6, .r12] s t := by
  refine WP.keep _ ?_ (by decide)
  unfold ptrP getP
  prun [hr.r27, Regs.p_eq hr, BitVec.add_zero]

/-- `ptrQ`: the key plus `p_len`, `q_len`. -/
theorem ptrQ_ok {s : State} {L : Lay} {key sig dig : Addr} (hr : Regs s L key sig dig) :
    WP isa (.block ptrQ) s fun t =>
      (t.gpr .r12 = off key L.pl ∧ t.gpr .r6 = BitVec.ofNat 64 L.ql ∧ t.mem = s.mem) ∧
        Keep [.r0, .r6, .r12] s t := by
  refine WP.keep _ ?_ (by decide)
  unfold ptrQ getP getQ
  prun [hr.r27, Regs.p_eq hr, Regs.q_eq hr, off]

/-- `ptrG`: the key plus `p_len + q_len`, `p_len`. -/
theorem ptrG_ok {s : State} {L : Lay} {key sig dig : Addr} (hr : Regs s L key sig dig) :
    WP isa (.block ptrG) s fun t =>
      (t.gpr .r12 = off key (L.pl + L.ql) ∧ t.gpr .r6 = BitVec.ofNat 64 L.pl ∧ t.mem = s.mem) ∧
        Keep [.r0, .r6, .r12] s t := by
  refine WP.keep _ ?_ (by decide)
  unfold ptrG getP getQ
  prun [hr.r27, Regs.p_eq hr, Regs.q_eq hr, off_ofNat_add]

/-- `ptrY`: the key plus `2 p_len + q_len`, `p_len`. -/
theorem ptrY_ok {s : State} {L : Lay} {key sig dig : Addr} (hr : Regs s L key sig dig) :
    WP isa (.block ptrY) s fun t =>
      (t.gpr .r12 = off key (2 * L.pl + L.ql) ∧ t.gpr .r6 = BitVec.ofNat 64 L.pl ∧ t.mem = s.mem) ∧
        Keep [.r0, .r6, .r12] s t := by
  unfold ptrY
  rw [WP.block_append_iff]
  refine WP.mono (ptrG_ok hr) fun t ⟨⟨a12, a6, m⟩, k⟩ => ?_
  refine WP.mono (WP.keep [.r12] (Q := fun u => u.gpr .r12 = off key (2 * L.pl + L.ql) ∧ u.mem = t.mem) ?_
    (by decide)) fun u ⟨⟨b12, mu⟩, ku⟩ =>
    ⟨⟨b12, (ku.gpr .r6 (by decide)).trans a6, mu.trans m⟩, (k.trans ku).mono (by decide)⟩
  prun [a12, a6]
  rw [off, show L.pl + L.ql + L.pl = 2 * L.pl + L.ql by omega]

/-- `ptrR`: the signature, `q_len`. -/
theorem ptrR_ok {s : State} {L : Lay} {key sig dig : Addr} (hr : Regs s L key sig dig) :
    WP isa (.block ptrR) s fun t =>
      (t.gpr .r12 = sig ∧ t.gpr .r6 = BitVec.ofNat 64 L.ql ∧ t.mem = s.mem) ∧ Keep [.r6, .r12] s t := by
  refine WP.keep _ ?_ (by decide)
  unfold ptrR getQ
  prun [hr.r28, Regs.q_eq hr, BitVec.add_zero]

/-- `ptrS`: the signature plus `q_len`, `q_len`. -/
theorem ptrS_ok {s : State} {L : Lay} {key sig dig : Addr} (hr : Regs s L key sig dig) :
    WP isa (.block ptrS) s fun t =>
      (t.gpr .r12 = off sig L.ql ∧ t.gpr .r6 = BitVec.ofNat 64 L.ql ∧ t.mem = s.mem) ∧
        Keep [.r6, .r12] s t := by
  unfold ptrS
  rw [WP.block_append_iff]
  refine WP.mono (ptrR_ok hr) fun t ⟨⟨a12, a6, m⟩, k⟩ => ?_
  refine WP.mono (WP.keep [.r12] (Q := fun u => u.gpr .r12 = off sig L.ql ∧ u.mem = t.mem) ?_
    (by decide)) fun u ⟨⟨b12, mu⟩, ku⟩ =>
    ⟨⟨b12, (ku.gpr .r6 (by decide)).trans a6, mu.trans m⟩, (k.trans ku).mono (by decide)⟩
  prun [a12, a6, off]

/-- `bufBase rd t`: `rd :=` the buffer. -/
theorem bufBase_ok {s : State} {L : Lay} {key sig dig : Addr} (hL : L.Ok) (hr : Regs s L key sig dig) {rd t : Reg}
    (hp : (rd, t) ∈ qPairs) :
    WP isa (.block (bufBase rd t)) s fun u => (u.gpr rd = L.Buf ∧ u.mem = s.mem) ∧ Keep [rd, t] s u := by
  have hb : L.Q + BitVec.ofNat 64 1600 = L.Buf := by
    simp only [Lay.Buf, Lay.Q, Lay.bOff, off, BitVec.add_assoc, BitVec.ofNat_add]
  unfold bufBase
  rw [WP.block_append_iff]
  refine WP.mono (qBase_ok hL hr hp) fun v ⟨⟨a, mv⟩, kv⟩ => ?_
  simp only [qPairs, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hp
  refine WP.mono (WP.keep [rd] (Q := fun u => u.gpr rd = L.Buf ∧ u.mem = v.mem) ?_ ?_)
    fun u ⟨⟨b, mu⟩, ku⟩ => ⟨⟨b, by rw [mu, mv]⟩, (kv.trans ku).mono ?_⟩ <;>
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> first | decide | prun [a, hb]

/-- `ptrBuf`: the buffer, `q_len`. -/
theorem ptrBuf_ok {s : State} {L : Lay} {key sig dig : Addr} (hL : L.Ok) (hr : Regs s L key sig dig) :
    WP isa (.block ptrBuf) s fun t =>
      (t.gpr .r12 = L.Buf ∧ t.gpr .r6 = BitVec.ofNat 64 L.ql ∧ t.mem = s.mem) ∧ Keep [.r0, .r6, .r12] s t := by
  unfold ptrBuf
  rw [WP.block_append_iff]
  refine WP.mono (bufBase_ok hL hr (by decide)) fun t ⟨⟨a12, m⟩, k⟩ => ?_
  refine WP.mono (getQ_ok (hr.keep k) .r6) fun u ⟨⟨b6, mu⟩, ku⟩ =>
    ⟨⟨(ku.gpr .r12 (by decide)).trans a12, b6, mu.trans m⟩, (k.trans ku).mono (by decide)⟩

/-- `ptrBuf2`: the buffer plus `q_len`, `q_len`. -/
theorem ptrBuf2_ok {s : State} {L : Lay} {key sig dig : Addr} (hL : L.Ok) (hr : Regs s L key sig dig) :
    WP isa (.block ptrBuf2) s fun t =>
      (t.gpr .r12 = off L.Buf L.ql ∧ t.gpr .r6 = BitVec.ofNat 64 L.ql ∧ t.mem = s.mem) ∧
        Keep [.r0, .r6, .r12] s t := by
  unfold ptrBuf2
  rw [WP.block_append_iff]
  refine WP.mono (ptrBuf_ok hL hr) fun t ⟨⟨a12, a6, m⟩, k⟩ => ?_
  refine WP.mono (WP.keep [.r12] (Q := fun u => u.gpr .r12 = off L.Buf L.ql ∧ u.mem = t.mem) ?_
    (by decide)) fun u ⟨⟨b12, mu⟩, ku⟩ =>
    ⟨⟨b12, (ku.gpr .r6 (by decide)).trans a6, mu.trans m⟩, (k.trans ku).mono (by decide)⟩
  prun [a12, a6, off]

end VG.Proof.Dsa.PPC64LE
