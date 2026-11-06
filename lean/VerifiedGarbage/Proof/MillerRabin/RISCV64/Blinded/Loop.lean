module

public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.Witness
public import VerifiedGarbage.Proof.RsaKeyGen.MrLoopAt
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCore

/-!
# The blinded Miller–Rabin loop on RISC-V

As on PPC64LE (`Proof/MillerRabin/PPC64LE/Blinded/Loop.lean`), the loop's
pieces: a draw's `witnessBytes c` octets (`witnessBytes_eq`) and its witness's
range (`witness_lt`), the status stored in `hStat` (`setStat_ok`), the loop's
test of it (`tail_ok`), and the changes within the working space and the
round's stack (`frm_widen`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.RISCV64.Blinded

open VG VG.RISCV64 VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.MillerRabin.RISCV64.Search VG.Impl.MillerRabin.RISCV64.Blinded
open VG.Proof.MillerRabin.RISCV64 (Env A RoundImpl)
open VG.Proof.MillerRabin.RISCV64.Search (Prep RcPost Kept keeps_word)
open VG.Proof.Bignum (slot Frm word off wv writeW_outside word_writeW_self)

/-- A change within ranges each inside one of `rs'`. -/
theorem frm_widen {B : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m')
    (hr : ∀ r ∈ rs, ∃ r' ∈ rs', r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2) : Frm B rs' m m' :=
  fun x hx => h x fun r hmem => by
    obtain ⟨r', h', h1, h2⟩ := hr r hmem
    have := hx r' h'
    omega_arith

open VG.Spec.RsaKeyGen (Rand loop mrStep witnessBytes)
open VG.Proof.RsaKeyGen (MrLoopAt mrSB wit seg)

/-- A witness's octets: `8 (t + 1)` for `c − 1` of `64 t + b` bits. -/
theorem witnessBytes_eq {c t b : Nat} (shape : Spec.RsaKeyGen.bitLength (c - 1) = 64 * t + b) (hb1 : 1 ≤ b)
    (hb : b ≤ 64) : witnessBytes c = 8 * (t + 1) := by
  unfold witnessBytes
  rw [shape]
  congr 1
  omega_arith

/-- A witness is below the candidate. -/
theorem witness_lt {c X l : Nat} (shape : Spec.RsaKeyGen.bitLength (c - 1) = l) (hl : 2 ≤ l) :
    (Spec.RsaKeyGen.witness (c - 1) X).1 < c := by
  have hb : 2 ^ (l - 1) ≤ c - 1 ∧ c - 1 < 2 ^ l :=
    (VG.Proof.Dsa.bitLength_iff_bounds (v := c - 1) (by omega_arith)).mp shape
  unfold Spec.RsaKeyGen.witness
  rw [shape]
  dsimp only
  split
  · omega_arith
  · exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (by omega_arith)

/-- `hStat := v` by `li t2 v` and its store. -/
theorem setStat_ok {s : State} {B : Addr} {Z w v : Nat} (e : Env s B Z w) (hv : imm12 (v : Int)) :
    WP isa (.block [.li .t2 v, sth .t2 hStat]) s fun s' =>
      (s'.mem = s.mem.writeW (off B (8 * hStat)) (BitVec.ofNat 64 v) ∧ s'.sp = s.sp) ∧ Keep [.t2] s s' := by
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ Z := e.hZ
  refine WP.mono (WP.rdwr (WP.keep [.t2] (Q := fun x => x.mem = s.mem.writeW (off B (8 * hStat)) (BitVec.ofNat 64 v))
    (by simp only [sth, hStat]
        brun [exec_li hv, e.s6, e.hs.st (d := 160) (n := 8) (by omega_arith),
          e.hs.al8 (d := 160) (by omega_arith) (by decide)]
        rfl) (by rfl) (by rfl))) fun x ⟨⟨xm, kx⟩, _, _, xsp⟩ => ⟨⟨xm, xsp⟩, kx⟩

/-- The loop goes on exactly when `hStat − 4` is zero. -/
theorem eval_sub4 {t : State} {v : Nat} (h : t.gpr .t2 = BitVec.ofNat 64 v - BitVec.ofNat 64 4) (hv : v < 2 ^ 64) :
    isa.eval (.zero .t2) t = some (decide (v = 4)) := by
  rw [Steps.eval_zero, h]
  refine congrArg some ?_
  by_cases h4 : v = 4
  · subst h4; decide
  · rw [decide_eq_false h4]
    apply beq_false_of_ne
    intro h0
    have h1 := BitVec.sub_eq_iff_eq_add.mp h0
    rw [show (0 : BitVec 64) + 4#64 = 4#64 from by decide] at h1
    have := congrArg BitVec.toNat h1
    simp only [BitVec.toNat_ofNat] at this
    omega_arith

/-- `t2 := hStat − 4`. -/
theorem tail_ok {s : State} {B : Addr} {Z w v : Nat} (e : Env s B Z w)
    (hv : word s.mem B (8 * hStat) = BitVec.ofNat 64 v) (hv' : v < 2 ^ 64) :
    WP isa (.block [ldh .t2 hStat, .addi .t2 .t2 (-4)]) s fun s' =>
      ((isa.eval (.zero .t2) s' = some (decide (v = 4)) ∧ s'.mem = s.mem ∧ s'.sp = s.sp) ∧ s'.rd = s.rd ∧
        s'.wr = s.wr) ∧ Keep [.t2] s s' := by
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ Z := e.hZ
  have r160 : s.mem.readW (B + 160#64) 64 = BitVec.ofNat 64 v := hv
  have hb : WP isa (.block [ldh .t2 hStat, .addi .t2 .t2 (-4)]) s fun (s' : State) =>
      (s'.gpr .t2 = BitVec.ofNat 64 v - BitVec.ofNat 64 4 ∧ s'.mem = s.mem) ∧ Keep [.t2] s s' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    simp only [ldh, hStat]
    brun [e.s6, e.hs.ld (d := 160) (n := 8) (by omega_arith), e.hs.al8 (d := 160) (by omega_arith) (by decide),
      r160]
  exact WP.mono (WP.rdwr hb) fun s' ⟨⟨⟨h3, hm⟩, k⟩, rd, wr, sp⟩ => ⟨⟨⟨eval_sub4 h3 hv', hm, sp⟩, rd, wr⟩, k⟩

theorem lt_flag {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (if BitVec.ofNat 64 x < BitVec.ofNat 64 y then (1 : BitVec 64) else 0) = BitVec.ofNat 64 (if x < y then 1 else 0) := by
  have e : (BitVec.ofNat 64 x < BitVec.ofNat 64 y) ↔ x < y := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  by_cases h : x < y
  · simp only [e.mpr h, h, ↓reduceIte]; rfl
  · have : ¬ BitVec.ofNat 64 x < BitVec.ofNat 64 y := fun h' => h (e.mp h')
    simp only [this, h, ↓reduceIte]; rfl

end VG.Proof.MillerRabin.RISCV64.Blinded
