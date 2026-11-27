module

public import VerifiedGarbage.Proof.RsaKeyGen.CandLeak
public import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Gcd
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.MontPrep
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.RoundCall
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Hyp
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Backend
import VerifiedGarbage.Proof.RsaKeyGen.Generate
import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.Loop
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Fin
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Setup
public import VerifiedGarbage.Proof.RsaKeyGen.MrLoopAt
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCore
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.Witness
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Ctx
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Prep
public import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.Witness
import VerifiedGarbage.Proof.RsaKeyGen.WitnessBits
import VerifiedGarbage.Proof.RsaKeyGen.CandMath
import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Frame

/-! ### `RsaKeyGen.RISCV64.Cand.Main`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.RISCV64.Cand.Args`, which only this module used -/

section

/-!
# A candidate on RISC-V: the test's inputs

As on PPC64LE (`Proof/RsaKeyGen/PPC64LE/Cand/Args.lean`): `testArgs_ok`,
`rand`, its length, the octets read and a witness's octets (`out_len`) from
the frame into the header, with the uniform witnesses needed (`checksW w`)
and the table entries trial division tries (512, or 1024 above 1024 bits).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Cand

open VG VG.RISCV64 VG.Proof.Bignum.RISCV64
open VG.Impl.RsaKeyGen.RISCV64.Candidate (checksIf testArgs hTrial ldf oRand oRandLen oRead oOutLen)
open VG.Impl.MillerRabin.RISCV64.Search (ldh sth hRand hRandLen hUsed hK hChecks)
open VG.Proof.MillerRabin.RISCV64 (Env)
open VG.Proof.Bignum (word off Outside writeW_outside word_writeW_self)

theorem xor_sel1 (x y : BitVec 64) : x ^^^ (y ^^^ x) &&& ((1 : BitVec 64) - 1#64) = x := by
  rw [show (1 : BitVec 64) - 1#64 = 0#64 by decide, BitVec.and_zero, BitVec.xor_zero]

theorem xor_sel0 (x y : BitVec 64) : x ^^^ (y ^^^ x) &&& ((0 : BitVec 64) - 1#64) = y := by
  rw [show (0 : BitVec 64) - 1#64 = BitVec.allOnes 64 by decide, BitVec.and_allOnes, BitVec.xor_comm y x,
    ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- `checksIf k v`: `s0 := v` if `k ≤ w`, for `w` in `t0`. -/
theorem checksIf_ok {s : State} {w a k v : Nat} (h0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (h5 : s.gpr .s0 = BitVec.ofNat 64 a) (hw : w < 2 ^ 63) (hk : k < 2 ^ 11) (hv : v < 2 ^ 11) :
    WP isa (.block (checksIf k v)) s fun t =>
      (t.gpr .s0 = BitVec.ofNat 64 (if k ≤ w then v else a) ∧ t.mem = s.mem) ∧ Keep [.t3, .t4, .s0] s t := by
  refine WP.keep _ ?_ rfl rfl
  obtain ik : imm12 (k : Int) := by unfold imm12; omega_using [hk]
  obtain iv : imm12 (v : Int) := by unfold imm12; omega_using [hv]
  obtain lt := sltu_val (BitVec.ofNat 64 w) (BitVec.ofNat 64 k)
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hw]), Nat.mod_eq_of_lt (by omega_using [hk])] at lt
  brun [checksIf, h0, h5, exec_li ik, exec_li iv, BitVec.ofInt_natCast, lt]
  by_cases hk' : k ≤ w
  · rw [ite_eq_right (show ¬ w < k by omega_using [hk']), ite_eq_left hk']
    exact xor_sel0 _ _
  · rw [ite_eq_left (show w < k by omega_using [hk']), ite_eq_right hk']
    exact xor_sel1 _ _

/-- The table entries trial division tries. -/
abbrev nTrial (w : Nat) : Nat := if w ≤ 16 then 512 else 1024

/-- What `testArgs` writes in the header, from the frame of `s0`. -/
structure ArgsOut (s0 s : State) (B : Addr) (w : Nat) (m : Mem) : Prop where
  rand : word m B (8 * hRand) = s.mem.readW (fw s0 oRand) 64
  randLen : word m B (8 * hRandLen) = s.mem.readW (fw s0 oRandLen) 64
  used : word m B (8 * hUsed) = s.mem.readW (fw s0 oRead) 64
  k : word m B (8 * hK) = s.mem.readW (fw s0 oOutLen) 64
  checks : word m B (8 * hChecks) = BitVec.ofNat 64 (VG.Proof.RsaKeyGen.checksW w)
  trial : word m B (8 * hTrial) = BitVec.ofNat 64 (nTrial w)

theorem checks_eq (w : Nat) :
    (if 59 ≤ w then 3 else if 22 ≤ w then 4 else if 8 ≤ w then 5 else if 7 ≤ w then 6 else
      if 6 ≤ w then 7 else if 5 ≤ w then 8 else 27) = VG.Proof.RsaKeyGen.checksW w := by
  unfold VG.Proof.RsaKeyGen.checksW
  -- the range of `w`, once: `split` on the two sides' `if`s visited every combination of them
  rcases (by omega : w < 5 ∨ w = 5 ∨ w = 6 ∨ w = 7 ∨ (8 ≤ w ∧ w < 22) ∨ (22 ≤ w ∧ w < 59) ∨ 59 ≤ w) with
    h | rfl | rfl | rfl | h | h | h <;>
  simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]

theorem nTrial_val {w : Nat} (hw : w < 2 ^ 63) :
    (BitVec.ofNat 64 (if 16 < w then 1 else 0) <<< 9) + BitVec.ofNat 64 512 = BitVec.ofNat 64 (nTrial w) := by
  unfold nTrial
  by_cases h : 16 < w
  · rw [ite_eq_left h, ite_eq_right (by omega)]; decide
  · rw [ite_eq_right h, ite_eq_left (by omega_using [h])]; decide

theorem testArgs_ok {s0 s : State} {w : Nat} (hf : Fr s0 s) (h : Env s (stackArg s0 1) (8 * sL s0) w) :
    WP isa (.block testArgs) s fun t =>
      (ArgsOut s0 s (stackArg s0 1) w t.mem ∧ Outside (stackArg s0 1) 128 96 s.mem t.mem) ∧
        Keep [.t2, .t3, .t4, .s0] s t := by
  have hp := hf.pre
  generalize hB : stackArg s0 1 = B at h
  have hs := h.hs
  have hnw := hs.nowrap
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * sL s0 := h.hZ
  have hw4 := h.hw
  have hw128 := h.hw'
  obtain al : ∀ o, o % 8 = 0 → (fb s0 + BitVec.ofNat 64 o).toNat % 8 = 0 := fun o h8 => fw_al hp h8
  obtain inr : ∀ o, o + 8 ≤ 192 → InRegions (s.rd ++ s.wr) (fb s0 + BitVec.ofNat 64 o) 8 := fun o ho =>
    ⟨kF s0, List.mem_append_right _ (by rw [hf.wr]; exact List.mem_cons_self), kF_contains ho⟩
  -- A store to the header keeps the frame's words.
  obtain stF : ∀ (m : Mem) (d : Nat) (v : BitVec 64), d + 8 ≤ 256 →
      ∀ o, o + 8 ≤ 192 → (m.writeW (off B d) v).readW (fw s0 o) 64 = m.readW (fw s0 o) 64 := fun m d v hd o ho =>
    ((Frame.refl [cS s0] m).writeW (r := cS s0) List.mem_cons_self _ (by
      rw [← hB]
      exact Offset.contains_base (stackArg s0 1) (d := d) (n := 8) (k := (stackArg s0 2).toNat * 8)
        (by simp only [sL] at hZ; omega_arith) (by simp only [sL] at hZ; omega_arith))).readW
      (r := ⟨fw s0 o, 8⟩) (Region.contains_self _ _) (fun ρ hρ => by
        simp only [List.mem_singleton] at hρ; subst hρ; exact hp.FS.sub_left (fw_sub s0 ho)) (by decide)
  generalize hR : s.mem.readW (fw s0 oRand) 64 = vR
  generalize hL : s.mem.readW (fw s0 oRandLen) 64 = vL
  generalize hU : s.mem.readW (fw s0 oRead) 64 = vU
  generalize hK' : s.mem.readW (fw s0 oOutLen) 64 = vK
  obtain r1 : (s.mem.writeW (off B 136) vR).readW (fb s0 + 168#64) 64 = vL := by
    rw [← hL]; exact stF _ 136 _ (by decide) 168 (by decide)
  obtain r2 : ((s.mem.writeW (off B 136) vR).writeW (off B 144) vL).readW (fb s0 + 176#64) 64 = vU := by
    rw [← hU, stF _ 144 _ (by decide) 176 (by decide)]; exact stF _ 136 _ (by decide) 176 (by decide)
  obtain r3 : (((s.mem.writeW (off B 136) vR).writeW (off B 144) vL).writeW (off B 152) vU).readW
      (fb s0 + 112#64) 64 = vK := by
    rw [← hK', stF _ 152 _ (by decide) 112 (by decide), stF _ 144 _ (by decide) 112 (by decide)]
    exact stF _ 136 _ (by decide) 112 (by decide)
  have r0 : s.mem.readW (fb s0 + 160#64) 64 = vR := hR
  unfold testArgs
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t2, .s0] (Q := fun t => t.mem = (((s.mem.writeW (off B 136) vR).writeW (off B 144) vL).writeW
      (off B 152) vU).writeW (off B 216) vK ∧ t.gpr .s0 = BitVec.ofNat 64 27) (by
    simp only [ldf, sth, oRand, oRandLen, oRead, oOutLen, hRand, hRandLen, hUsed, hK]
    brun [hf.s11, h.s6, al 160 (by decide), al 168 (by decide), al 176 (by decide), al 112 (by decide),
      inr 160 (by decide), inr 168 (by decide), inr 176 (by decide), inr 112 (by decide), r0, r1, r2, r3,
      hs.st (d := 136) (n := 8) (by omega_using [hZ]), hs.al8 (d := 136) (by omega_using [hZ]) (by decide),
      hs.st (d := 144) (n := 8) (by omega_using [hZ]), hs.al8 (d := 144) (by omega_using [hZ]) (by decide),
      hs.st (d := 152) (n := 8) (by omega_using [hZ]), hs.al8 (d := 152) (by omega_using [hZ]) (by decide),
      hs.st (d := 216) (n := 8) (by omega_using [hZ]), hs.al8 (d := 216) (by omega_using [hZ]) (by decide),
      exec_li (show imm12 27 by decide)]) (by decide)) fun t₁ ⟨⟨m₁, a₁⟩, k₁⟩ => ?_
  obtain e₁ := h.keep k₁ (by decide)
  obtain hw63 : w < 2 ^ 63 := by omega_using [hw128]
  rw [WP.block_append_iff]
  refine WP.mono (checksIf_ok e₁.t0 a₁ hw63 (by decide) (by decide)) fun t₂ ⟨⟨a₂, m₂⟩, k₂⟩ => ?_
  obtain e₂ := e₁.keep k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (checksIf_ok e₂.t0 a₂ hw63 (by decide) (by decide)) fun t₃ ⟨⟨a₃, m₃⟩, k₃⟩ => ?_
  obtain e₃ := e₂.keep k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (checksIf_ok e₃.t0 a₃ hw63 (by decide) (by decide)) fun t₄ ⟨⟨a₄, m₄⟩, k₄⟩ => ?_
  obtain e₄ := e₃.keep k₄ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (checksIf_ok e₄.t0 a₄ hw63 (by decide) (by decide)) fun t₅ ⟨⟨a₅, m₅⟩, k₅⟩ => ?_
  obtain e₅ := e₄.keep k₅ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (checksIf_ok e₅.t0 a₅ hw63 (by decide) (by decide)) fun t₆ ⟨⟨a₆, m₆⟩, k₆⟩ => ?_
  obtain e₆ := e₅.keep k₆ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (checksIf_ok e₆.t0 a₆ hw63 (by decide) (by decide)) fun t₇ ⟨⟨a₇, m₇⟩, k₇⟩ => ?_
  obtain e₇ := e₆.keep k₇ (by decide)
  have hs₇ := e₇.hs
  rw [checks_eq] at a₇
  obtain lt := sltu_val (BitVec.ofNat 64 16) (BitVec.ofNat 64 w)
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using [hw128])] at lt
  obtain m₇' : t₇.mem = (((s.mem.writeW (off B 136) vR).writeW (off B 144) vL).writeW (off B 152) vU).writeW
      (off B 216) vK := by rw [m₇, m₆, m₅, m₄, m₃, m₂, m₁]
  refine WP.mono (WP.keep [.t2] (Q := fun t => t.mem = (t₇.mem.writeW (off B 168)
      (BitVec.ofNat 64 (VG.Proof.RsaKeyGen.checksW w))).writeW (off B 128) (BitVec.ofNat 64 (nTrial w))) (by
    simp only [sth, hChecks, hTrial]
    brun [e₇.s6, e₇.t0, a₇, lt, nTrial_val hw63, exec_li (show imm12 16 by decide),
      hs₇.st (d := 168) (n := 8) (by omega_using [hZ]), hs₇.al8 (d := 168) (by omega_using [hZ]) (by decide),
      hs₇.st (d := 128) (n := 8) (by omega_using [hZ]), hs₇.al8 (d := 128) (by omega_using [hZ]) (by decide)]) (by decide))
    fun t ⟨tm, kt⟩ => ?_
  obtain K := ((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans kt
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, K.mono (by decide)⟩
  all_goals rw [tm, m₇']
  all_goals try simp only [hRand, hRandLen, hUsed, hK, hChecks, hTrial]
  · rw [(writeW_outside _ B _ (d := 128) (by omega_using [])).word (d := 136) (by omega_using []) (by omega_using []),
      (writeW_outside _ B _ (d := 168) (by omega_using [])).word (d := 136) (by omega_using []) (by omega_using []),
      (writeW_outside _ B _ (d := 216) (by omega_using [])).word (d := 136) (by omega_using []) (by omega_using []),
      (writeW_outside _ B _ (d := 152) (by omega_using [])).word (d := 136) (by omega_using []) (by omega_using []),
      (writeW_outside _ B _ (d := 144) (by omega_using [])).word (d := 136) (by omega_using []) (by omega_using []), word_writeW_self, hR]
  · rw [(writeW_outside _ B _ (d := 128) (by omega_using [])).word (d := 144) (by omega_using []) (by omega_using []),
      (writeW_outside _ B _ (d := 168) (by omega_using [])).word (d := 144) (by omega_using []) (by omega_using []),
      (writeW_outside _ B _ (d := 216) (by omega_using [])).word (d := 144) (by omega_using []) (by omega_using []),
      (writeW_outside _ B _ (d := 152) (by omega_using [])).word (d := 144) (by omega_using []) (by omega_using []), word_writeW_self, hL]
  · rw [(writeW_outside _ B _ (d := 128) (by omega_using [])).word (d := 152) (by omega_using []) (by omega_using []),
      (writeW_outside _ B _ (d := 168) (by omega_using [])).word (d := 152) (by omega_using []) (by omega_using []),
      (writeW_outside _ B _ (d := 216) (by omega_using [])).word (d := 152) (by omega_using []) (by omega_using []), word_writeW_self, hU]
  · rw [(writeW_outside _ B _ (d := 128) (by omega_using [])).word (d := 216) (by omega_using []) (by omega_using []),
      (writeW_outside _ B _ (d := 168) (by omega_using [])).word (d := 216) (by omega_using []) (by omega_using []), word_writeW_self, hK']
  · rw [(writeW_outside _ B _ (d := 128) (by omega_using [])).word (d := 168) (by omega_using []) (by omega_using []), word_writeW_self]
  · rw [word_writeW_self]
  · have ow : ∀ (m : Mem) (d : Nat) (v : BitVec 64), 128 ≤ d → d + 8 ≤ 224 →
        Outside B 128 96 m (m.writeW (off B d) v) := fun m d v h1 h2 =>
      (writeW_outside m B v (d := d) (by omega_using [h2])).mono h1 (by omega_using [h2])
    exact (((((ow _ 136 _ (by omega_using []) (by omega_using [])).trans (ow _ 144 _ (by omega_using []) (by omega_using []))).trans
      (ow _ 152 _ (by omega_using []) (by omega_using []))).trans (ow _ 216 _ (by omega_using []) (by omega_using []))).trans
      (ow _ 168 _ (by omega_using []) (by omega_using []))).trans (ow _ 128 _ (by omega_using []) (by omega_using []))

end VG.Proof.RsaKeyGen.RISCV64.Cand

end

end

/-! ### `RsaKeyGen.RISCV64.Cand.WLoop`, which only this module used -/

section

/-! ### `RsaKeyGen.RISCV64.Cand.WWit`, which only this module used -/

section

/-! ### `RsaKeyGen.RISCV64.Cand.WRound`, which this module and modules that import it used -/

section

/-!
# A candidate on RISC-V: a witness's round

As on PPC64LE (`Proof/RsaKeyGen/PPC64LE/Cand/WRound.lean`): `passed_ok`, after
a passing round, one more witness (`hIdx`), and `hStat := 1` once there are at
least 17 (from 1) of them and `hChecks` uniform ones (`hUni`), else 4;
`round_ok`, the round (`roundCall_ok`) and its outcome, `hStat := 2` for a
failure.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Cand

open VG VG.RISCV64 VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.MillerRabin.RISCV64.Search
open VG.Impl.RsaKeyGen.RISCV64.Witness (hUni passed)
open VG.Proof.MillerRabin.RISCV64 (Env A RoundImpl)
open VG.Proof.MillerRabin.RISCV64.Search (ge_val Prep RcPost Kept keeps_word keeps_byte)
open VG.Proof.Bignum (slot Frm word off ofs writeW_outside word_writeW_self)

/-- The status after a passing round, from `I` witnesses of which `U` uniform. -/
abbrev statOf (I U ch : Nat) : Nat := if 17 ≤ I + 1 ∧ ch ≤ U then 1 else 4

/-- The registers `passed` writes. -/
def psRegs : List Reg := [.t2, .t3, .t4, .t5]

/-- After a passing round, from `I` witnesses of which `U` uniform. -/
theorem passed_ok {s : State} {B : Addr} {Z w I U ch : Nat} (e : Env s B Z w)
    (hk : word s.mem B (8 * hIdx) = BitVec.ofNat 64 I) (hu : word s.mem B (8 * hUni) = BitVec.ofNat 64 U)
    (hch : word s.mem B (8 * hChecks) = BitVec.ofNat 64 ch) (hk' : I + 1 < 2 ^ 63) (hu' : U < 2 ^ 63)
    (hch' : ch < 2 ^ 63) :
    WP isa (.block passed) s fun s' =>
      (s'.mem = (s.mem.writeW (off B (8 * hIdx)) (BitVec.ofNat 64 (I + 1))).writeW (off B (8 * hStat))
          (BitVec.ofNat 64 (statOf I U ch))) ∧ Keep psRegs s s' := by
  have hs := e.hs
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ Z := e.hZ
  refine WP.keep _ ?_ (by rfl) (by rfl)
  have r176 : s.mem.readW (B + 176#64) 64 = BitVec.ofNat 64 I := hk
  obtain o176 := writeW_outside s.mem B (BitVec.ofNat 64 (I + 1)) (d := 176) (by omega_using [])
  obtain r16 : (s.mem.writeW (B + 176#64) (BitVec.ofNat 64 (I + 1))).readW (B + 16#64) 64 = BitVec.ofNat 64 U :=
    (o176.word (by omega_using []) (by omega_using [])).trans hu
  obtain r168 : (s.mem.writeW (B + 176#64) (BitVec.ofNat 64 (I + 1))).readW (B + 168#64) 64 = BitVec.ofNat 64 ch :=
    (o176.word (by omega_using []) (by omega_using [])).trans hch
  obtain ek : BitVec.ofNat 64 I + 1#64 = BitVec.ofNat 64 (I + 1) := by rw [← BitVec.ofNat_add]
  obtain g1 := ge_val (BitVec.ofNat 64 (I + 1)) (BitVec.ofNat 64 17)
  obtain g2 := ge_val (BitVec.ofNat 64 U) (BitVec.ofNat 64 ch)
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using [hk'])] at g1
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hch']), Nat.mod_eq_of_lt (by omega_using [hu'])] at g2
  simp only [passed, geFlag, ldh, sth, hIdx, hUni, hChecks, hStat]
  brun [e.s6, hs.ld (d := 176) (n := 8) (by omega_using [hZ]), hs.al8 (d := 176) (by omega_using [hZ]) (by decide),
    hs.st (d := 176) (n := 8) (by omega_using [hZ]), hs.ld (d := 16) (n := 8) (by omega_using [hZ]), hs.al8 (d := 16) (by omega_using [hZ]) (by decide),
    hs.ld (d := 168) (n := 8) (by omega_using [hZ]), hs.al8 (d := 168) (by omega_using [hZ]) (by decide),
    hs.st (d := 160) (n := 8) (by omega_using [hZ]), hs.al8 (d := 160) (by omega_using [hZ]) (by decide),
    r176, exec_li (show imm12 17 by decide), exec_li (show imm12 3 by decide),
    exec_li (show imm12 4 by decide)]
  simp only [ek, r16, r168]
  rw [show (1#64 : BitVec 64) = BitVec.ofInt 64 1 from rfl, g1, g2]
  obtain hv : BitVec.ofNat 64 4 - (BitVec.ofNat 64 (if ch ≤ U then 1 else 0) &&&
      BitVec.ofNat 64 (if 17 ≤ I + 1 then 1 else 0)) * BitVec.ofNat 64 3 =
      BitVec.ofNat 64 (statOf I U ch) := by
    by_cases h1 : ch ≤ U <;> by_cases h2 : 17 ≤ I + 1 <;> simp [statOf, h1, h2] <;> decide
  rw [hv]

/-- A byte the round and its outcome keep: one the round keeps, outside
`hStat` and `hIdx`. -/
def RKept (w i : Nat) : Prop := Kept w i ∧ ∀ k ∈ [20, 22], i < 8 * k ∨ 8 * k + 8 ≤ i

/-- What a witness's round leaves. -/
structure RdPost (s : State) (B : Addr) (L w c a I U ch : Nat) (t : State) : Prop where
  prep : Prep t B L w c
  stat : word t.mem B (8 * hStat) =
    BitVec.ofNat 64 (if Proof.MillerRabin.Round.round c a then statOf I U ch else 2)
  idx : word t.mem B (8 * hIdx) = BitVec.ofNat 64 (if Proof.MillerRabin.Round.round c a then I + 1 else I)
  kept : ∀ i, i < 8 * L → RKept w i → t.mem (B + BitVec.ofNat 64 i) = s.mem (B + BitVec.ofNat 64 i)
  frame : Frame [⟨B, 8 * L⟩, below s.sp 96] s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  cs : ∀ r ∈ preserved, r ∉ Pub.montRegs → r ∉ psRegs → t.gpr r = s.gpr r

/-- A word whose bytes are all `RKept`. -/
theorem RdPost.word {s t : State} {B : Addr} {L w c a I U ch d : Nat} (h : RdPost s B L w c a I U ch t)
    (hd : d + 8 ≤ 8 * L) (hk : ∀ i, d ≤ i → i < d + 8 → RKept w i) : word t.mem B d = word s.mem B d :=
  (Mem.readW_congr fun i hi => by
    rw [show off B d + BitVec.ofNat 64 i = B + BitVec.ofNat 64 (d + i) by
      simp only [off, BitVec.add_assoc, BitVec.ofNat_add]]
    exact (h.kept _ (by omega_arith) (hk _ (by omega_arith) (by omega_arith))).symm).symm

/-- A change only at offsets below `e` keeps memory outside the `8 L` bytes at
`B`, for `e ≤ 8 L`. -/
theorem frame_of_low {B : Addr} {L e : Nat} {m m' : Mem} (h : ∀ x, e ≤ ofs B x → m' x = m x) (he : e ≤ 8 * L)
    (rs : List Region) : Frame (⟨B, 8 * L⟩ :: rs) m m' := by
  intro x hx
  obtain hb := hx _ (List.mem_cons_self ..)
  simp only [Region.Contains, Nat.not_le] at hb
  exact h x (by show e ≤ (x - B).toNat; omega_using [he, hb])

/-- Array `j ≤ 27` of the working space lies past the header and inside its
`8 L` bytes. -/
theorem slot_bounds {w L j : Nat} (hL : 256 + 28 * (8 * (w + 2)) ≤ 8 * L) (hj : j ≤ 27) :
    256 ≤ slot w j ∧ slot w j + 8 * (w + 2) ≤ 8 * L := by
  have e : slot w j = 256 + j * (8 * (w + 2)) := rfl
  obtain hm : j * (8 * (w + 2)) ≤ 27 * (8 * (w + 2)) := Nat.mul_le_mul_right _ hj
  rw [e]
  omega_using [hL, hm]

theorem ofs_byte (B : Addr) {i : Nat} (hi : i < 2 ^ 64) : ofs B (B + BitVec.ofNat 64 i) = i := by
  simp only [VG.Proof.Bignum.ofs]
  rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]

theorem round_ok (R : RoundImpl) {s : State} {B : Addr} {L w c a I U ch : Nat} (h : Prep s B L w c)
    (ha : A s.mem B w 4 = a) (hac : a < c)
    (hal : s.sp.toNat % 16 = 0) (hsp : 96 ≤ s.sp.toNat) (hstk : (below s.sp 96).Disjoint ⟨B, 8 * L⟩)
    (hI : word s.mem B (8 * hIdx) = BitVec.ofNat 64 I) (hU : word s.mem B (8 * hUni) = BitVec.ofNat 64 U)
    (hch : word s.mem B (8 * hChecks) = BitVec.ofNat 64 ch) (hI' : I + 1 < 2 ^ 63) (hU' : U < 2 ^ 63)
    (hch' : ch < 2 ^ 63) :
    WP isa (VG.Impl.RsaKeyGen.RISCV64.Witness.round R.name R.code) s (RdPost s B L w c a I U ch) := by
  have e := h.env
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := e.hZ
  unfold VG.Impl.RsaKeyGen.RISCV64.Witness.round
  refine WP.seq (WP.mono (VG.Proof.MillerRabin.RISCV64.Search.roundCall_ok R h ha hac hal hsp hstk)
    fun u hu => ?_)
  obtain kw : ∀ d, d + 8 ≤ 256 → (∀ i, d ≤ i → i < d + 8 → Kept w i) → word u.mem B d = word s.mem B d :=
    fun d hd hk => keeps_word hu.keeps (by omega_arith) hk
  have hsu := hu.prep.env.hs
  have hnw := hsu.nowrap
  have hL : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := hu.prep.env.hZ
  -- A store to `hStat` or `hIdx` keeps `Prep`, the round's bytes and the frame.
  obtain keepP : ∀ (t : State), (∀ x, (ofs B x < 160 ∨ 168 ≤ ofs B x) → (ofs B x < 176 ∨ 184 ≤ ofs B x) →
      t.mem x = u.mem x) → Env t B (8 * L) w → t.gpr .t1 = u.gpr .t1 →
      Prep t B L w c ∧ (∀ i, i < 8 * L → RKept w i → t.mem (B + BitVec.ofNat 64 i) = s.mem (B + BitVec.ofNat 64 i)) ∧
        Frame [⟨B, 8 * L⟩, below s.sp 96] s.mem t.mem := by
    intro t hb et ht1
    obtain wq : ∀ d, d + 8 ≤ 8 * L → (d + 8 ≤ 160 ∨ 168 ≤ d) → (d + 8 ≤ 176 ∨ 184 ≤ d) →
        word t.mem B d = word u.mem B d := fun d hd h1 h2 =>
      Mem.readW_congr fun i hi => hb _ (by rw [VG.Proof.Bignum.ofs_off B (by omega_arith)]; omega_using [h1, hi])
        (by rw [VG.Proof.Bignum.ofs_off B (by omega_arith)]; omega_using [h2, hi])
    refine ⟨hu.prep.keep et (hu.prep.t1_of ht1) (fun d hd => ?_) (fun j hj => ?_), fun i hi hk => ?_, ?_⟩
    · obtain ⟨s0, s0'⟩ := slot_bounds (j := 0) hL (by decide)
      obtain ⟨s27', s27⟩ := slot_bounds (j := 27) hL (by decide)
      rcases hd with rfl | rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl | rfl
      all_goals exact wq _ (by omega_arith) (by omega_arith) (by omega_arith)
    · simp only [A, VG.Proof.Bignum.RISCV64.Pre.wordsVal_eq_wv]
      obtain ⟨sj, sj'⟩ := slot_bounds (j := j) hL (by rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide)
      exact VG.Proof.Bignum.wv_congr fun i hi => wq _ (by omega_using [sj', hi]) (by omega_using [sj]) (by omega_using [sj])
    · have h20 := hk.2 20 (by simp)
      obtain h22 := hk.2 22 (by simp)
      obtain hi' : i < 2 ^ 64 := by omega_arith
      rw [hb _ (by rw [ofs_byte B hi']; omega_using [h20]) (by rw [ofs_byte B hi']; omega_using [h22])]
      exact keeps_byte hu.keeps hi hk.1
    · exact hu.frame.trans (frame_of_low (e := 184) (fun x hx => hb x (by omega_using [hx]) (by omega_using [hx])) (by omega_using [hZ]) _)
  refine WP.ite _ (Steps.eval_zero_ofNat _ _ (by split <;> decide) hu.a0) (fun hz => ?_) (fun hz => ?_)
  · have hr : Proof.MillerRabin.Round.round c a = false := by
      by_contra hc; simp [hc] at hz
    obtain st := hsu.st (d := 160) (n := 8) (by omega_using [hZ])
    refine WP.mono (WP.rdwr <| WP.keep [.t2] (Q := fun t => t.mem = u.mem.writeW (off B (8 * hStat)) (BitVec.ofNat 64 2)) (by
      simp only [sth, hStat]
      brun [hu.prep.env.s6, st, hsu.al8 (d := 160) (by omega_using [hZ]) (by decide), exec_li (show imm12 2 by decide)])
      (by decide)) fun t ⟨⟨tm, kt⟩, trd, twr, tsp⟩ => ?_
    obtain et := hu.prep.env.keep kt (by decide)
    obtain wo := writeW_outside u.mem B (d := 8 * hStat) (BitVec.ofNat 64 2) (by simp only [hStat]; omega_using [])
    obtain ⟨p, kk, fr⟩ := keepP t (fun x h1 _ => by rw [tm]; exact wo x (by simpa only [hStat] using h1)) et
      (kt.gpr (by decide))
    refine ⟨p, ?_, ?_, kk, fr, trd.trans hu.rd, twr.trans hu.wr, tsp.trans hu.sp, fun r hr h1 h2 => ?_⟩
    · rw [tm, hr]; exact word_writeW_self _ _ _ _
    · rw [tm, hr, (writeW_outside _ _ _ (by simp only [hStat]; omega_using [])).word (by simp only [hStat, hIdx]; omega_using [])
        (by simp only [hIdx]; omega_using []), kw _ (by simp only [hIdx]; omega_using []) (by simp only [hIdx]; kept_tac), hI]
      rfl
    · rw [kt.gpr (fun hm => h2 (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; subst hm; decide)),
        hu.cs r hr h1]
  · have hr : Proof.MillerRabin.Round.round c a = true := by
      by_contra hc; simp [hc] at hz
    obtain kI : word u.mem B (8 * hIdx) = BitVec.ofNat 64 I := by
      rw [kw _ (by simp only [hIdx]; omega_using []) (by simp only [hIdx]; kept_tac), hI]
    obtain kU : word u.mem B (8 * hUni) = BitVec.ofNat 64 U := by
      rw [kw _ (by simp only [hUni]; omega_using []) (by simp only [hUni]; kept_tac), hU]
    obtain kC : word u.mem B (8 * hChecks) = BitVec.ofNat 64 ch := by
      rw [kw _ (by simp only [hChecks]; omega_using []) (by simp only [hChecks]; kept_tac), hch]
    refine WP.mono (WP.rdwr (passed_ok hu.prep.env kI kU kC hI' hU' hch')) fun t ⟨⟨tm, kt⟩, trd, twr, tsp⟩ => ?_
    obtain et := hu.prep.env.keep kt (by decide)
    obtain wo1 := writeW_outside u.mem B (d := 8 * hIdx) (BitVec.ofNat 64 (I + 1)) (by simp only [hIdx]; omega_using [])
    obtain wo2 := writeW_outside (u.mem.writeW (off B (8 * hIdx)) (BitVec.ofNat 64 (I + 1))) B (d := 8 * hStat)
      (BitVec.ofNat 64 (statOf I U ch)) (by simp only [hStat]; omega_using [])
    obtain ⟨p, kk, fr⟩ := keepP t (fun x h1 h2 => by
      rw [tm]; exact (wo2 x (by simpa only [hStat] using h1)).trans (wo1 x (by simpa only [hIdx] using h2))) et
      (kt.gpr (by decide))
    refine ⟨p, ?_, ?_, kk, fr, trd.trans hu.rd, twr.trans hu.wr, tsp.trans hu.sp, fun r hr h1 h2 => ?_⟩
    · rw [tm, hr]; exact word_writeW_self _ _ _ _
    · rw [tm, hr, (writeW_outside _ _ _ (by simp only [hStat]; omega_using [])).word (by simp only [hStat, hIdx]; omega_using [])
        (by simp only [hIdx]; omega_using [])]
      exact word_writeW_self _ _ _ _
    · rw [kt.gpr h2, hu.cs r hr h1]

end VG.Proof.RsaKeyGen.RISCV64.Cand

end

end

/-!
# A candidate on RISC-V: a witness from a draw

As on PPC64LE (`Proof/RsaKeyGen/PPC64LE/Cand/{WUni,WForced,WSel}.lean`):
`uniform_ok`, `s9 := 1` if the draw `x` in array 4 is uniform (`x ≥ 2` and
`(x | 1) < c`), else 0; `forced_ok`, `x` copied to array 3 with bit 1 set and
its top bit cleared, `(x | 2) mod 2^(64 w − 1)`; `witness_ok`, the draw
becomes `Spec.RsaKeyGen.witness (c − 1) x`'s witness, selected under the
flag's mask, and the flag added to `hUni`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Cand

open VG VG.RISCV64 VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.MillerRabin.RISCV64.Search
open VG.Impl.Bignum.RISCV64.PublicChecked (base)
open VG.Impl.RsaKeyGen.RISCV64.Witness (hUni uniform forced witness)
open VG.Proof.MillerRabin.RISCV64 (Env A MCtx mask)
open VG.Proof.Bignum (slot Frm word off ofs Outside writeW_outside word_writeW_self)

/-- The registers `uniform` writes. -/
def uniRegs : List Reg := [.a3, .t2, .t3, .t5, .s9, .a0, .t4, .s0, .s1, .s2, .s3, .s4, .a5, .a6]

theorem uniform_ok {s : State} {B : Addr} {Z w c : Nat} (e : Env s B Z w) (hc : A s.mem B w 0 = c) :
    WP isa uniform s fun t =>
      (t.gpr .s9 = BitVec.ofNat 64 (if decide (2 ≤ A s.mem B w 4) && decide ((A s.mem B w 4 ||| 1) < c) then 1 else 0) ∧
        Frm B [(slot w 3, 8 * (w + 2)), (slot w 6, 8 * (w + 2))] s.mem t.mem) ∧ Keep uniRegs s t := by
  unfold uniform
  refine WP.seq (WP.mono (VG.Proof.MillerRabin.RISCV64.Blinded.atLeast2_ok e) fun t1 ⟨⟨a3, tm⟩, k1⟩ => ?_)
  obtain e1 : Env t1 B Z w := e.keep k1 (by decide)
  refine WP.seq (WP.mono (WP.keep [.t2, .s9] (Q := fun t => t.gpr .s9 =
      BitVec.ofNat 64 (if 2 ≤ A s.mem B w 4 then 1 else 0) ∧ t.mem = t1.mem) (by
    obtain hv : (if (0#64 : BitVec 64) < t1.gpr .a3 then (1 : BitVec 64) else 0) =
        BitVec.ofNat 64 (if 2 ≤ A s.mem B w 4 then 1 else 0) := by
      by_cases h2 : 2 ≤ A s.mem B w 4
      · have : t1.gpr .a3 ≠ 0#64 := fun h0 => by have := a3.mp h0; omega_using [h2, this]
        rw [ite_eq_left (by rw [BitVec.lt_def]; have := (BitVec.toNat_ne_iff_ne).mpr this; simp at this ⊢; omega_using [this]),
          ite_eq_left h2]; rfl
      · have : t1.gpr .a3 = 0#64 := a3.mpr (by omega_using [h2])
        rw [this, ite_eq_right (by decide), ite_eq_right h2]; rfl
    brun [exec_li (show imm12 0 by decide), hv]) (by decide)) fun t2 ⟨⟨a9, m2⟩, k2⟩ => ?_)
  obtain e2 : Env t2 B Z w := e1.keep k2 (by decide)
  refine WP.seq (WP.mono (VG.Proof.MillerRabin.RISCV64.Blinded.ltN_ok (c := c) e2 (by rw [m2, tm]; exact hc))
    fun t3 ⟨⟨a4, f3⟩, k3⟩ => ?_)
  refine WP.mono (WP.keep [.s9] (Q := fun t => t.gpr .s9 = t3.gpr .s9 &&& t3.gpr .s4 ∧ t.mem = t3.mem)
    (by brun) (by decide)) fun t ⟨⟨a9', m⟩, k⟩ => ⟨⟨?_, ?_⟩, (((k1.trans k2).trans k3).trans k).mono (by decide)⟩
  · rw [a9', k3.gpr (by decide), a9, a4, m2, tm]
    by_cases h1 : 2 ≤ A s.mem B w 4 <;> by_cases h2 : (A s.mem B w 4 ||| 1) < c <;> simp [h1, h2] <;> decide
  · rw [m]; rw [m2, tm] at f3; exact f3

/-- The registers `forced` writes. -/
def fdRegs : List Reg := [.t2, .t3, .t4, .t5, .s0]

theorem forced_ok {s : State} {B : Addr} {Z w : Nat} (e : Env s B Z w) :
    WP isa forced s fun t =>
      (A t.mem B w 3 = (A s.mem B w 4 ||| 2) % 2 ^ (64 * w - 1) ∧
        Frm B [(slot w 3, 8 * (w + 2))] s.mem t.mem) ∧ Keep fdRegs s t := by
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ Z := e.hZ
  have hw4 := e.hw
  have hw128 := e.hw'
  have hnw := e.hs.nowrap
  obtain es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  obtain h3 : slot w 3 + 8 * (w + 2) ≤ Z := by rw [es]; omega_using [hZ]
  obtain h4 : slot w 4 + 8 * (w + 2) ≤ Z := by rw [es]; omega_using [hZ]
  unfold forced
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (e.base (rd := .t3) (by decide) 3) fun y ⟨⟨y3, ym⟩, ky⟩ => ?_
  obtain ey : Env y B Z w := e.keep ky (by decide)
  refine WP.mono (ey.base (rd := .t4) (by decide) 4) fun y' ⟨⟨y4, ym'⟩, ky'⟩ => ?_
  obtain ey' : Env y' B Z w := ey.keep ky' (by decide)
  refine WP.seq (WP.mono (VG.Proof.MillerRabin.RISCV64.Search.copyWithin_ok ey'.hs (dS := slot w 4) (dD := slot w 3)
    y4 ((ky'.gpr (by decide)).trans y3) ey'.t0 (by omega_using [hw4]) (by omega_using [hw128]) (by omega_using [h4]) (by omega_using [h3]) (by rw [es]; omega_using [])
    (by rw [es]; omega_using []) (by simp only [es]; omega_using [])) fun z ⟨⟨_, zw, zo⟩, kz⟩ => ?_)
  obtain ez : Env z B Z w := ey'.keep kz (by decide)
  have hz := ez.hs
  -- `m₁`: memory after the copy; the stores follow.
  generalize hm1 : z.mem = m1 at zw zo
  rw [WP.block_append_iff]
  refine WP.mono (ez.base (rd := .t3) (by decide) 3) fun a ⟨⟨a3, am⟩, ka⟩ => ?_
  obtain ea : Env a B Z w := ez.keep ka (by decide)
  have ha := ea.hs
  obtain d0 : slot w 3 + 8 ≤ Z := by omega_using [h3]
  obtain dt : slot w 3 + 8 * (w - 1) + 8 ≤ Z := by omega_using [h3]
  obtain al0 : (slot w 3) % 8 = 0 := by rw [es]; omega_using []
  obtain alt : (slot w 3 + 8 * (w - 1)) % 8 = 0 := by rw [es]; omega_using []
  obtain o1 := writeW_outside m1 B (word m1 B (slot w 3) ||| 2#64) (d := slot w 3) (by omega_using [hnw, h3])
  obtain rt : (m1.writeW (off B (slot w 3)) (word m1 B (slot w 3) ||| 2#64)).readW (off B (slot w 3 + 8 * (w - 1))) 64 =
      word m1 B (slot w 3 + 8 * (w - 1)) := o1.word (by omega_using [hw4]) (by omega_using [hnw, h3])
  obtain adr : off B (slot w 3 + 8 * w) - BitVec.ofNat 64 8 = off B (slot w 3 + 8 * (w - 1)) := by
    rw [off_sub B (by omega_using [hw4]), show slot w 3 + 8 * w - 8 = slot w 3 + 8 * (w - 1) by omega_using [hw4]]
  obtain msk : BitVec.ofInt 64 (-1) >>> 1 = BitVec.ofNat 64 (2 ^ (64 - 1) - 1) := by decide
  obtain msk' : (-1#64 : BitVec 64) >>> 1 = BitVec.ofNat 64 (2 ^ (64 - 1) - 1) := by decide
  refine WP.mono (WP.keep [.t2, .t3, .t4] (Q := fun t => t.mem =
      (m1.writeW (off B (slot w 3)) (word m1 B (slot w 3) ||| 2#64)).writeW (off B (slot w 3 + 8 * (w - 1)))
        (word m1 B (slot w 3 + 8 * (w - 1)) &&& BitVec.ofNat 64 (2 ^ (64 - 1) - 1))) (by
    brun [a3, am, hm1, (ka.gpr (by decide)).trans ez.t0, ha.ld (d := slot w 3) (n := 8) d0,
      ha.al8 (d := slot w 3) d0 al0, ha.st (d := slot w 3) (n := 8) d0, VG.Proof.MillerRabin.RISCV64.shl3_w w, adr,
      ha.ld (d := slot w 3 + 8 * (w - 1)) (n := 8) dt, ha.al8 (d := slot w 3 + 8 * (w - 1)) dt alt,
      ha.st (d := slot w 3 + 8 * (w - 1)) (n := 8) dt, exec_li (show imm12 (-1) by decide), msk, msk', rt,
      BitVec.add_zero]) (by decide)) fun t ⟨tm, kt⟩ => ?_
  obtain o2 := writeW_outside (m1.writeW (off B (slot w 3)) (word m1 B (slot w 3) ||| 2#64)) B
    (word m1 B (slot w 3 + 8 * (w - 1)) &&& BitVec.ofNat 64 (2 ^ (64 - 1) - 1)) (d := slot w 3 + 8 * (w - 1)) (by omega_using [hnw, h3])
  obtain hx1 : VG.Proof.Bignum.wv m1 B (slot w 3) w = A s.mem B w 4 := by
    simp only [A, Pre.wordsVal_eq_wv]
    rw [ym', ym] at zw
    exact VG.Proof.Bignum.wv_congr2 fun i hi => zw i hi
  obtain hV : VG.Proof.Bignum.wv m1 B (slot w 3) w < 2 ^ (64 * (w - 1) + 64) := by
    rw [show 64 * (w - 1) + 64 = 64 * w by omega_using [hw4]]; exact VG.Proof.Bignum.wv_lt _ _ _ _
  obtain fb := VG.Proof.RsaKeyGen.wv_fallback (m := m1) (m' := t.mem) (p := B) (d := slot w 3) (n := w) (t := w - 1)
    (b := 64) (by omega_using [hw4]) (by omega_using [hw4]) (by decide) (by decide)
    (by rw [tm, o2.word (by omega_using [hw4]) (by omega_using [hnw, h3]), word_writeW_self])
    (by rw [tm, word_writeW_self])
    (fun j hj hj0 hjt => by rw [tm, o2.word (by omega_using [hjt]) (by omega_using [hZ, hw4, hw128, hnw, h3, h4, d0, dt, al0, alt, hj, hj0, hjt]), o1.word (by omega_using [hj0]) (by omega_using [hZ, hw4, hw128, hnw, h3, h4, d0, dt, al0, alt, hj, hj0, hjt])]) hV
  refine ⟨⟨?_, ?_⟩, ((((ky.trans ky').trans kz).trans ka).trans kt).mono (by decide)⟩
  · simp only [A, Pre.wordsVal_eq_wv]
    rw [fb, hx1, show 64 * (w - 1) + 64 - 1 = 64 * w - 1 by omega_using [hw4]]
    simp only [A, Pre.wordsVal_eq_wv]
  · rw [ym', ym] at zo
    refine Frm.trans (Frm.of_outside (o := slot w 3) (n := 8 * (w + 2)) (zo.mono (by omega_using []) (by omega_using [])) (by simp)) ?_
    rw [tm]
    exact Frm.trans (Frm.of_outside (o := slot w 3) (n := 8 * (w + 2)) (o1.mono (by omega_using []) (by omega_using [])) (by simp))
      (Frm.of_outside (o := slot w 3) (n := 8 * (w + 2)) (o2.mono (by omega_using []) (by omega_using [])) (by simp))

theorem or1_nat (a : Nat) : a ||| 1 = a + (1 - a % 2) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or]
  rcases i with _ | i
  · simp [Nat.testBit_zero]; omega_using []
  · rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    simp
    congr 1; omega_using []

theorem neg_flag (P : Bool) : BitVec.ofNat 64 0 - BitVec.ofNat 64 (if P then 1 else 0) = mask P := by
  cases P <;> decide

/-- `MCtx` from `Env`, the inverse and the candidate. -/
theorem mctx_of {s : State} {B : Addr} {Z w N : Nat} (e : Env s B Z w)
    (hinv : ((Mont.word s.mem B (slot w 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0)
    (hn : A s.mem B w 0 = N) : MCtx s B Z w N :=
  ⟨e.hs, e.hw, e.hw', e.hZ, e.a7, e.s5, e.t0, hinv, hn⟩

/-- The registers `witness` writes. -/
def witRegs : List Reg := [.a0, .a2, .a3, .a5, .a6, .t2, .t3, .t4, .t5, .s0, .s1, .s2, .s3, .s4, .s9]

/-- The arrays `witness` changes: 3, 4 and 6. -/
def arrR (w : Nat) : List (Nat × Nat) :=
  [(slot w 3, 8 * (w + 2)), (slot w 4, 8 * (w + 2)), (slot w 6, 8 * (w + 2))]

/-- What `witness` changes: arrays 3, 4 and 6, and `hUni`. -/
def witRanges (w : Nat) : List (Nat × Nat) :=
  [(8 * hUni, 8), (slot w 3, 8 * (w + 2)), (slot w 4, 8 * (w + 2)), (slot w 6, 8 * (w + 2))]

theorem witness_ok {s : State} {B : Addr} {Z w c u : Nat} (h : MCtx s B Z w c) (h6 : s.gpr .s6 = B)
    (hc2 : c % 2 = 1) (hcb : Spec.RsaKeyGen.bitLength (c - 1) = 64 * w)
    (hu : word s.mem B (8 * hUni) = BitVec.ofNat 64 u) :
    WP isa witness s fun t =>
      (A t.mem B w 4 = (Spec.RsaKeyGen.witness (c - 1) (A s.mem B w 4)).1 ∧
        word t.mem B (8 * hUni) = BitVec.ofNat 64
          (u + if (Spec.RsaKeyGen.witness (c - 1) (A s.mem B w 4)).2 then 1 else 0) ∧
        Frm B (witRanges w) s.mem t.mem) ∧ Keep witRegs s t := by
  obtain e := h.env h6
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ Z := e.hZ
  have hw4 := e.hw
  have hnw := e.hs.nowrap
  obtain es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  generalize hx : A s.mem B w 4 = x
  obtain hxR : x < 2 ^ (64 * w) := by
    rw [← hx]; simp only [A, Pre.wordsVal_eq_wv]; exact VG.Proof.Bignum.wv_lt _ _ _ _
  rw [VG.Proof.RsaKeyGen.witness_eq hc2 hcb hxR]
  generalize hP : (decide (2 ≤ x) && decide (x + (1 - x % 2) < c)) = P
  unfold witness
  -- The words and numbers a step outside arrays 3, 4 and 6 keeps.
  obtain frw : ∀ {m m' : Mem}, Frm B (arrR w) m m' → ∀ d, d + 8 ≤ slot w 3 →
      word m' B d = word m B d := fun f d hd => f.word_eq (fun r hr => by
    simp only [arrR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [es] at hd ⊢ <;> omega_using [hd])
    (by rw [es] at hd; omega_using [hZ, hnw, hd])
  obtain frA0 : ∀ {m m' : Mem}, Frm B (arrR w) m m' → A m' B w 0 = A m B w 0 := fun f => by
    simp only [A, Pre.wordsVal_eq_wv]
    exact f.wv_eq (fun r hr => by
      simp only [arrR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [es] <;> omega_using []) (by rw [es]; omega_using [hZ, hnw])
  obtain fr1 : ∀ {m m' : Mem} {rs : List (Nat × Nat)}, Frm B rs m m' → (∀ r ∈ rs, r ∈ arrR w) →
      Frm B (arrR w) m m' := fun f hs => f.mono hs
  refine WP.seq (WP.mono (uniform_ok e h.n) fun t₁ ⟨⟨a9, o₁⟩, k₁⟩ => ?_)
  rw [hx] at a9
  obtain e₁ := e.keep k₁ (by decide)
  obtain o₁' := fr1 o₁ (by simp [arrR])
  obtain x₁ : A t₁.mem B w 4 = x := by
    rw [← hx]; simp only [A, Pre.wordsVal_eq_wv]
    exact o₁.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [es] <;> omega_using []) (by rw [es]; omega_using [hZ, hnw])
  refine WP.seq (WP.mono (forced_ok e₁) fun t₂ ⟨⟨f3, o₂⟩, k₂⟩ => ?_)
  rw [x₁] at f3
  obtain e₂ := e₁.keep k₂ (by decide)
  obtain o₂' := fr1 o₂ (by simp [arrR])
  obtain x₂ : A t₂.mem B w 4 = x := by
    rw [← x₁]; simp only [A, Pre.wordsVal_eq_wv]
    exact o₂.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; simp only [es]; omega_using []) (by rw [es]; omega_using [hZ, hnw])
  obtain s9₂ : t₂.gpr .s9 = BitVec.ofNat 64 (if P then 1 else 0) := by
    rw [k₂.gpr (by decide), a9, ← hP, or1_nat]
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t2, .s4] (Q := fun t => t.gpr .s4 = mask P ∧ t.mem = t₂.mem) (by
    brun [exec_li (show imm12 0 by decide), s9₂, neg_flag]) (by decide)) fun t₃ ⟨⟨a4, m₃⟩, k₃⟩ => ?_
  obtain e₃ := e₂.keep k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (e₃.base (rd := .a5) (by decide) 4) fun t₄ ⟨⟨a5, m₄⟩, k₄⟩ => ?_
  obtain e₄ := e₃.keep k₄ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (e₄.base (rd := .a6) (by decide) 3) fun t₅ ⟨⟨a6, m₅⟩, k₅⟩ => ?_
  obtain e₅ := e₄.keep k₅ (by decide)
  refine WP.mono (e₅.base (rd := .a2) (by decide) 6) fun t₆ ⟨⟨a2, m₆⟩, k₆⟩ => ?_
  obtain e₆ := e₅.keep k₆ (by decide)
  obtain m₆' : t₆.mem = t₂.mem := by rw [m₆, m₅, m₄, m₃]
  obtain K₆ := (((k₁.trans k₂).trans k₃).trans k₄).trans k₅ |>.trans k₆
  obtain o₆ : Frm B (arrR w) s.mem t₆.mem := by rw [m₆']; exact o₁'.trans o₂'
  obtain w0 : ∀ {m m' : Mem}, Frm B (arrR w) m m' → Mont.word m' B (slot w 0) = Mont.word m B (slot w 0) :=
    fun f => frw f (slot w 0) (by simp only [es]; omega_using [])
  obtain inv₆ : ((Mont.word t₆.mem B (slot w 0)).toNat * (t₆.gpr .t1).toNat + 1) % 2 ^ 64 = 0 := by
    rw [w0 o₆, K₆.gpr (by decide)]; exact h.inv
  obtain c₆ : MCtx t₆ B Z w c := mctx_of e₆ inv₆ ((frA0 o₆).trans h.n)
  obtain a4₆ : t₆.gpr .s4 = mask P := by rw [k₆.gpr (by decide), k₅.gpr (by decide), k₄.gpr (by decide), a4]
  obtain a5₆ : t₆.gpr .a5 = off B (slot w 4) := by rw [k₆.gpr (by decide), k₅.gpr (by decide), a5]
  obtain a6₆ : t₆.gpr .a6 = off B (slot w 3) := by rw [k₆.gpr (by decide), a6]
  refine WP.seq (WP.mono (VG.Proof.MillerRabin.RISCV64.sel_ok c₆ (b := P) (o := 6) (a := 4) (t := 3) (by decide)
    (by decide) (by decide) (by decide) (by decide) a2 a5₆ a6₆ a4₆) fun t₇ ⟨⟨v₇, o₇⟩, k₇⟩ => ?_)
  obtain e₇ := e₆.keep k₇ (by decide)
  obtain o₇' : Frm B (arrR w) t₆.mem t₇.mem :=
    Frm.of_outside (o := slot w 6) (n := 8 * (w + 2)) (o₇.mono (by omega_using []) (by omega_using [])) (by simp [arrR])
  obtain c₇ : MCtx t₇ B Z w c := mctx_of e₇ (by
      rw [w0 o₇', k₇.gpr (by decide)]; exact inv₆)
    ((frA0 o₇').trans c₆.n)
  refine WP.seq (WP.mono (VG.Proof.MillerRabin.RISCV64.copy_ok c₇ (o := 4) (a := 6) (by decide) (by decide)
    (by decide)) fun t₈ ⟨⟨v₈, o₈⟩, k₈⟩ => ?_)
  obtain e₈ := e₇.keep k₈ (by decide)
  obtain o₈' : Frm B (arrR w) t₇.mem t₈.mem :=
    Frm.of_outside (o := slot w 4) (n := 8 * (w + 2)) (o₈.mono (by omega_using []) (by omega_using [])) (by simp [arrR])
  have hs₈ := e₈.hs
  obtain s9₈ : t₈.gpr .s9 = BitVec.ofNat 64 (if P then 1 else 0) := by
    rw [k₈.gpr (by decide), k₇.gpr (by decide), k₆.gpr (by decide),
      k₅.gpr (by decide), k₄.gpr (by decide), k₃.gpr (by decide), s9₂]
  obtain u₈ : word t₈.mem B 16 = BitVec.ofNat 64 u := by
    have := frw ((o₆.trans o₇').trans o₈') 16 (by simp only [es]; omega_using [])
    simp only [hUni] at hu; rw [this, hu]
  refine WP.mono (WP.keep [.t2] (Q := fun t => t.mem = t₈.mem.writeW (off B (8 * hUni))
      (BitVec.ofNat 64 (u + if P then 1 else 0))) (by
    simp only [ldh, sth, hUni]
    have r16 : t₈.mem.readW (B + 16#64) 64 = BitVec.ofNat 64 u := u₈
    brun [e₈.s6, r16, s9₈, hs₈.ld (d := 16) (n := 8) (by omega_using [hZ]), hs₈.al8 (d := 16) (by omega_using [hZ]) (by decide),
      hs₈.st (d := 16) (n := 8) (by omega_using [hZ]), BitVec.ofNat_add_ofNat]) (by decide)) fun t ⟨tm, kt⟩ => ?_
  obtain K := (((K₆.trans k₇).trans k₈).trans kt)
  obtain ou := writeW_outside t₈.mem B (d := 8 * hUni) (BitVec.ofNat 64 (u + if P then 1 else 0))
    (by simp only [hUni]; omega_using [])
  refine ⟨⟨?_, ?_, ?_⟩, K.mono (by simp [witRegs, uniRegs, fdRegs, VG.Proof.MillerRabin.RISCV64.copyRegs])⟩
  · rw [tm]
    have : A (t₈.mem.writeW (off B (8 * hUni)) (BitVec.ofNat 64 (u + if P then 1 else 0))) B w 4 = A t₈.mem B w 4 := by
      simp only [A, Pre.wordsVal_eq_wv]
      exact (Frm.of_outside (rs := [(8 * hUni, 8)]) ou (by simp)).wv_eq (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; simp only [hUni, es]; omega_using []) (by rw [es]; omega_using [hZ, hnw])
    rw [this, v₈, v₇]
    obtain hm4 : A t₆.mem B w 4 = x := by rw [m₆']; exact x₂
    obtain hm3 : A t₆.mem B w 3 = (x ||| 2) % 2 ^ (64 * w - 1) := by rw [m₆']; exact f3
    rw [hm4, hm3]
  · rw [tm]; exact word_writeW_self _ _ _ _
  · rw [tm]
    exact (((o₆.trans o₇').trans o₈').mono (by simp [arrR, witRanges])).trans
      (Frm.of_outside ou (by simp [witRanges]))

end VG.Proof.RsaKeyGen.RISCV64.Cand

end

end

/-!
# A candidate on RISC-V: the witnesses' loop

As on PPC64LE (`Proof/RsaKeyGen/PPC64LE/Cand/{WLoad,WDraw,WLoop,WBody}.lean`),
over RISC-V's blinded loop (`Proof/MillerRabin/RISCV64/Blinded/Loop.lean`):
`millerRabin_ok`, from a prepared candidate `c` of `w` words (`KCtx`) and the
tape `r` at `R`, after the candidate's `8 w` octets, `Witness.millerRabin`
leaves in `hStat` and `hUsed` what `primalityTest c (r.drop (8 w))` says
(`MOut`): 0 if the tape ran out, else 1 (probably prime) or 2 (composite), and
the octets read. Witness by witness (`MrLoopAt` from offset `8 w`): each draw
is the next `8 w` octets (`load_ok`), its witness (`witness_ok`) and its round
(`round_ok`). `res_ok`: the test's result (`testResult`) from them.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Cand

open VG VG.RISCV64 VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum
open VG.Impl.MillerRabin.RISCV64.Search (ldh sth hRand hRandLen hUsed hK hIdx hChecks hStat loadDraw tapeShort)
open VG.Impl.RsaKeyGen.RISCV64.Witness (hUni)
open VG.Proof.MillerRabin.RISCV64 (Env A RoundImpl)
open VG.Proof.MillerRabin.RISCV64.Search (Prep Kept)
open VG.Proof.Bignum (slot Frm word off ofs writeW_outside word_writeW_self)
open VG.Spec.RsaKeyGen (Rand loop mrStep witnessBytes)
open VG.Proof.RsaKeyGen (MrLoopAt mrSB wit seg)

/-! ## What the loop writes, and what it reads -/

/-- The ranges of the working space the loop's loads, witnesses and counts
write: `hUni`, `hUsed` and `hStat`, `hIdx`, and arrays 3–6. -/
def kgR (w : Nat) : List (Nat × Nat) :=
  [(8 * hUni, 8), (8 * hUsed, 16), (8 * hIdx, 8), (slot w 3, 4 * (8 * (w + 2)))]

/-- The prepared candidate survives a change of memory within `kgR` that
keeps `t1`. -/
theorem Prep.ofKgR {s t : State} {B : Addr} {L w c : Nat} (h : Prep s B L w c) (env : Env t B (8 * L) w)
    (ht1 : t.gpr .t1 = s.gpr .t1) (hf : Frm B (kgR w) s.mem t.mem) : Prep t B L w c := by
  have hZ' : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := env.hZ
  have hnw := env.hs.nowrap
  refine h.keep env (h.t1_of ht1) (fun d hd => hf.word_eq ?_ (by
    rcases hd with rfl | rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl | rfl <;> (try simp only [slot, hdrBytes]) <;> omega_arith))
    (fun j hj => ?_)
  · intro r hr
    simp only [kgR, hUni, hUsed, hIdx, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hd with rfl | rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl | rfl <;>
      rcases hr with rfl | rfl | rfl | rfl <;> (try simp only [slot, hdrBytes]) <;> omega_arith
  · have hj27 : j ≤ 27 := by rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide
    obtain hb : slot w j + 8 * w ≤ 2 ^ 64 := by
      have := Nat.mul_le_mul_right (8 * (w + 2)) hj27
      simp only [slot, hdrBytes]
      omega_using [hZ', hnw, this]
    simp only [A, Pre.wordsVal_eq_wv]
    refine hf.wv_eq (fun r hr => ?_) hb
    simp only [kgR, hUni, hUsed, hIdx, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hr with rfl | rfl | rfl | rfl <;> (try simp only [slot, hdrBytes]) <;> omega_using []

/-- A change within `kgR` keeps memory outside the working space. -/
theorem frame_of_kgR {B : Addr} {L w : Nat} {m m' : Mem} (hf : Frm B (kgR w) m m')
    (hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L) (rs : List Region) : Frame (⟨B, 8 * L⟩ :: rs) m m' := by
  intro x hx
  obtain hb := hx _ (List.mem_cons_self ..)
  simp only [Region.Contains, Nat.not_le] at hb
  refine hf x fun r hr => Or.inr ?_
  obtain hr' : r.1 + r.2 ≤ 8 * L := by
    simp only [kgR, hUni, hUsed, hIdx, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only [slot, hdrBytes] <;> omega_using [hZ]
  show r.1 + r.2 ≤ (x - B).toNat
  exact Nat.le_trans hr' (Nat.lt_succ_iff.mp hb)

/-- What the loop reads and never writes: the prepared candidate `c` of `w`
words, the tape at `R` (`rl` octets, readable, apart from the working space
and the round's stack), the stack pointer (aligned, the round's 96 bytes
below it apart from the working space), and in the header a witness's octets
`8 w` and the uniform witnesses needed `ch`. -/
structure KCtx (s : State) (B : Addr) (L w c : Nat) (R : Addr) (rl ch : Nat) : Prop where
  prep : Prep s B L w c
  rand : word s.mem B (8 * hRand) = R
  randLen : word s.mem B (8 * hRandLen) = BitVec.ofNat 64 rl
  k : word s.mem B (8 * hK) = BitVec.ofNat 64 (8 * w)
  checks : word s.mem B (8 * hChecks) = BitVec.ofNat 64 ch
  cb : Spec.RsaKeyGen.bitLength (c - 1) = 64 * w
  ch63 : ch < 2 ^ 63
  rl64 : rl < 2 ^ 64
  rdR : ∀ i < rl, InRegions (s.rd ++ s.wr) (R + BitVec.ofNat 64 i) 1
  sepR : ∀ i < rl, ∀ x, ofs B x < 8 * L → R + BitVec.ofNat 64 i ≠ x
  sp16 : s.sp.toNat % 16 = 0
  sp : 96 ≤ s.sp.toNat
  stk : (below s.sp 96).Disjoint ⟨B, 8 * L⟩
  stkR : ∀ i < rl, ¬ (below s.sp 96).Contains (R + BitVec.ofNat 64 i) 1

/-- A witness's octets: `8 w`. -/
theorem KCtx.wb {s : State} {B R : Addr} {L w c rl ch : Nat} (h : KCtx s B L w c R rl ch) :
    witnessBytes c = 8 * w := by
  have hw4 := h.prep.env.hw
  obtain e := VG.Proof.MillerRabin.RISCV64.Blinded.witnessBytes_eq (c := c) (t := w - 1) (b := 64)
    (by rw [h.cb]; omega_arith) (by decide) (by decide)
  rw [e]; omega_arith

/-- `KCtx` in another state: the same prepared candidate, header words,
regions and stack pointer. -/
theorem KCtx.keep {s t : State} {B R : Addr} {L w c rl ch : Nat} (h : KCtx s B L w c R rl ch)
    (prep : Prep t B L w c)
    (hw : ∀ d, (d = 8 * hRand ∨ d = 8 * hRandLen ∨ d = 8 * hK ∨ d = 8 * hChecks) →
      word t.mem B d = word s.mem B d)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.sp = s.sp) : KCtx t B L w c R rl ch :=
  ⟨prep, (hw _ (by simp)).trans h.rand, (hw _ (by simp)).trans h.randLen, (hw _ (by simp)).trans h.k,
    (hw _ (by simp)).trans h.checks, h.cb, h.ch63, h.rl64, by rw [rd, wr]; exact h.rdR, h.sepR,
    by rw [sp]; exact h.sp16, by rw [sp]; exact h.sp, by rw [sp]; exact h.stk, by rw [sp]; exact h.stkR⟩

/-- A change within `kgR` that keeps `t1` keeps `KCtx`. -/
theorem KCtx.ofKgR {s t : State} {B R : Addr} {L w c rl ch : Nat} (h : KCtx s B L w c R rl ch)
    (env : Env t B (8 * L) w) (ht1 : t.gpr .t1 = s.gpr .t1) (hf : Frm B (kgR w) s.mem t.mem)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.sp = s.sp) : KCtx t B L w c R rl ch := by
  have hZ' : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := env.hZ
  have hnw := env.hs.nowrap
  refine h.keep (Prep.ofKgR h.prep env ht1 hf) (fun d hd => hf.word_eq (fun r hr => ?_) ?_) rd wr sp
  · simp only [kgR, hUni, hUsed, hIdx, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [hRand, hRandLen, hK, hChecks] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl <;>
      simp only [slot, hdrBytes] <;> omega_using []
  · simp only [hRand, hRandLen, hK, hChecks] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> omega_using []

/-- The tape survives a change of memory within the working space and the
round's stack. -/
theorem KCtx.bytes_frame {s : State} {B R : Addr} {L w c rl ch : Nat} (h : KCtx s B L w c R rl ch)
    {m m' : Mem} (F : Frame [⟨B, 8 * L⟩, below s.sp 96] m m') :
    Spec.Rsa.bytesAt m' R rl = Spec.Rsa.bytesAt m R rl := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  refine F _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have := Nat.le_of_not_lt fun hlt => h.sepR i hi _ hlt rfl
    change 8 * L ≤ (R + BitVec.ofNat 64 i - B).toNat at this
    simp only [Region.Contains]
    omega_arith
  · exact h.stkR i hi

/-! ## A draw's octets -/

/-- The registers `loadDraw` writes. -/
def kLoadRegs : List Reg := [.s7, .t2, .s8, .a7, .a0, .s0, .t3, .t4, .t5]

/-- The tape's address at `used` (`s7`), `hUsed := used + 8 w`, `8 w` in `s8`
and array 4's base in `a7`. -/
theorem loadA_ok {s : State} {B R : Addr} {L w c rl ch used : Nat} (h : KCtx s B L w c R rl ch)
    (hu : word s.mem B (8 * hUsed) = BitVec.ofNat 64 used) :
    WP isa (.block ([ldh .s7 hRand, ldh .t2 hUsed, .add .s7 .s7 .t2, ldh .s8 hK, .add .t2 .t2 .s8,
        sth .t2 hUsed] ++ VG.Impl.Bignum.RISCV64.PublicChecked.base .a7 4)) s fun u =>
      (u.gpr .s7 = R + BitVec.ofNat 64 used ∧ u.gpr .s8 = BitVec.ofNat 64 (8 * w) ∧
        u.gpr .a7 = off B (slot w 4) ∧
        u.mem = s.mem.writeW (off B (8 * hUsed)) (BitVec.ofNat 64 (used + 8 * w))) ∧
      Keep [.s7, .t2, .s8, .a7] s u := by
  have e := h.prep.env
  have hs := e.hs
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := e.hZ
  refine WP.keep _ ?_ (by rfl) (by rfl)
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (u₁ : State) => (u₁.gpr .s7 = R + BitVec.ofNat 64 used ∧
      u₁.gpr .s8 = BitVec.ofNat 64 (8 * w) ∧
      u₁.mem = s.mem.writeW (off B (8 * hUsed)) (BitVec.ofNat 64 (used + 8 * w))) ∧
      Keep [.s7, .t2, .s8] s u₁) (WP.keep _ ?_ (by rfl) (by rfl)) fun u₁ ⟨⟨a7', a8, am⟩, k1⟩ => ?_
  · have r136 : s.mem.readW (B + 136#64) 64 = R := h.rand
    have r152 : s.mem.readW (B + 152#64) 64 = BitVec.ofNat 64 used := hu
    have r216 : s.mem.readW (B + 216#64) 64 = BitVec.ofNat 64 (8 * w) := h.k
    simp only [ldh, sth, hRand, hUsed, hK]
    brun [e.s6, hs.ld (d := 136) (n := 8) (by omega_using [hZ]), hs.al8 (d := 136) (by omega_using [hZ]) (by decide),
      hs.ld (d := 152) (n := 8) (by omega_using [hZ]), hs.al8 (d := 152) (by omega_using [hZ]) (by decide),
      hs.ld (d := 216) (n := 8) (by omega_using [hZ]), hs.al8 (d := 216) (by omega_using [hZ]) (by decide),
      hs.st (d := 152) (n := 8) (by omega_using [hZ]), r136, r152, r216]
    rw [← BitVec.ofNat_add]
  · have e1 : Env u₁ B (8 * L) w := e.keep k1 (by decide)
    refine WP.mono (e1.base (rd := .a7) (by decide) 4) fun u₂ ⟨⟨b7, bm⟩, k2⟩ => ?_
    exact ⟨(k2.gpr (by decide)).trans a7', (k2.gpr (by decide)).trans a8, b7, bm.trans am⟩

/-- A draw from `used`: the next `8 w` octets of the tape into array 4,
`hUsed := used + 8 w`, and `a7` back at array 0. -/
theorem load_ok {s : State} {B R : Addr} {L w c rl ch used : Nat} (h : KCtx s B L w c R rl ch)
    (hu : word s.mem B (8 * hUsed) = BitVec.ofNat 64 used) (hav : used + 8 * w ≤ rl) :
    WP isa loadDraw s fun s' =>
      (A s'.mem B w 4 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (R + BitVec.ofNat 64 used) (8 * w)) ∧
        word s'.mem B (8 * hUsed) = BitVec.ofNat 64 (used + 8 * w) ∧
        Frm B [(8 * hUsed, 8), (slot w 4, 8 * (w + 2))] s.mem s'.mem ∧ s'.gpr .a7 = off B (slot w 0)) ∧
      Keep kLoadRegs s s' := by
  have e := h.prep.env
  have hs := e.hs
  have hnw := hs.nowrap
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := e.hZ
  have hw4 := e.hw
  have hw128 := e.hw'
  unfold loadDraw
  -- The tape's address, `hUsed`, and array 4's base.
  refine WP.seq (WP.mono (loadA_ok h hu) fun u ⟨⟨u7, u8, ua7, um⟩, ku⟩ => ?_)
  obtain hu' : Scr u B (8 * L) := hs.congr ku.2.2
  obtain hNr : ∀ i < 8 * w, InRegions (u.rd ++ u.wr) (off (R + BitVec.ofNat 64 used) i) 1 := fun i hi => by
    rw [ku.2.1, ku.2.2, show off (R + BitVec.ofNat 64 used) i = R + BitVec.ofNat 64 used + BitVec.ofNat 64 i from rfl,
      Offset.add_add]; exact h.rdR _ (by omega_using [hav, hi])
  obtain hNs : ∀ i < 8 * w, ∀ x, ofs B x < 8 * L → off (R + BitVec.ofNat 64 used) i ≠ x := fun i hi x hx => by
    rw [show off (R + BitVec.ofNat 64 used) i = R + BitVec.ofNat 64 used + BitVec.ofNat 64 i from rfl,
      Offset.add_add]; exact h.sepR _ (by omega_using [hav, hi]) x hx
  refine WP.seq (WP.mono (loadN_ok (k := 8 * w) hu' ua7
    (by rw [u7]; exact (BitVec.add_zero _).symm) u8 ((ku.gpr (by decide)).trans e.t0) (by omega_using [hw4]) (Nat.le_refl _)
    (by omega_using [hw128]) (by simp only [slot, hdrBytes]; omega_using []) (by simp only [slot, hdrBytes]; omega_using [])
    (by simp only [slot, hdrBytes]; omega_using [hZ]) hNr hNs)
    fun v ⟨vv, vo, kv⟩ => ?_)
  -- The memory so far: `hUsed` and array 4.
  obtain fu : Frm B [(8 * hUsed, 8), (slot w 4, 8 * (w + 2))] s.mem v.mem := by
    refine Frm.trans (Frm.of_outside (o := 8 * hUsed) (n := 8) ?_ (by simp))
      (Frm.of_outside (o := slot w 4) (n := 8 * (w + 2))
        (fun x hx => vo x (by simp only [VG.Proof.Mont.ofs, VG.Proof.Bignum.ofs] at hx ⊢; omega_using [hx])) (by simp))
    rw [um]; exact writeW_outside _ _ _ (by simp only [hUsed]; omega_using [])
  obtain bytes : Spec.Rsa.bytesAt u.mem (R + BitVec.ofNat 64 used) (8 * w) =
      Spec.Rsa.bytesAt s.mem (R + BitVec.ofNat 64 used) (8 * w) := by
    rw [um]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    rw [List.mem_range] at hi
    rw [Offset.add_add]
    refine writeW_outside _ _ _ (by simp only [hUsed]; omega_using []) _ ?_
    have := Nat.le_of_not_lt fun hlt => h.sepR (used + i) (by omega_using [hav, hi]) _ hlt rfl
    simp only [hUsed]; omega
  obtain kvu := ku.trans kv
  obtain v6 : v.gpr .s6 = B := (kvu.gpr (by decide)).trans e.s6
  -- `a7` back.
  refine WP.mono (WP.keep [.a7] (Q := fun (y : State) => y.gpr .a7 = off B (slot w 0) ∧ y.mem = v.mem)
      (by brun [v6, hdrBytes]; simp only [slot, hdrBytes, Nat.zero_mul, Nat.add_zero]) (by rfl) (by rfl))
    fun y ⟨⟨y7, ym⟩, ky⟩ => ?_
  refine ⟨⟨?_, ?_, by rw [ym]; exact fu, y7⟩, (kvu.trans ky).mono (by decide)⟩
  · simp only [A]
    rw [ym, vv, bytes]
  · have hv1 : word v.mem B (8 * hUsed) = word u.mem B (8 * hUsed) :=
      vo.word (by simp only [hUsed, slot, hdrBytes]; omega_using []) (by simp only [hUsed]; omega_using [])
    rw [ym, hv1, um]
    exact word_writeW_self _ _ _ _

/-! ## The loop's state -/

/-- What every state the loop reaches keeps from its entry `σ`. -/
structure LKeep (σ s : State) (B : Addr) (L w c : Nat) : Prop where
  prep : Prep s B L w c
  frame : Frame [⟨B, 8 * L⟩, below σ.sp 96] σ.mem s.mem
  sp : s.sp = σ.sp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  s11 : s.gpr .s11 = σ.gpr .s11

/-- The loop after `k` witnesses passed, with `n + 1` iterations left, from
the entry state `σ`: the `k`-th witness is drawn at offset `8 w + 8 w k`. -/
structure LInv (σ s : State) (B R : Addr) (L w c rl ch : Nat) (r : Rand) (k n : Nat) : Prop where
  ctx : KCtx s B L w c R rl ch
  used : word s.mem B (8 * hUsed) = BitVec.ofNat 64 (8 * w + 8 * w * k)
  idx : word s.mem B (8 * hIdx) = BitVec.ofNat 64 (k + 1)
  uni : word s.mem B (8 * hUni) = BitVec.ofNat 64 (mrSB c (8 * w) (8 * w) r k).2
  stat : word s.mem B (8 * hStat) = BitVec.ofNat 64 4
  tape : Spec.Rsa.bytesAt s.mem R rl = r
  frame : Frame [⟨B, 8 * L⟩, below σ.sp 96] σ.mem s.mem
  sp : s.sp = σ.sp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  s11 : s.gpr .s11 = σ.gpr .s11
  mr : MrLoopAt c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2 (8 * w) (8 * w) r k n

theorem LInv.keep {σ s : State} {B R : Addr} {L w c rl ch : Nat} {r : Rand} {k n : Nat}
    (h : LInv σ s B R L w c rl ch r k n) : LKeep σ s B L w c :=
  ⟨h.ctx.prep, h.frame, h.sp, h.rd, h.wr, h.s11⟩

/-- `LKeep` through a step within `kgR` that keeps the registers it reads. -/
theorem LKeep.ofKgR {σ s t : State} {B : Addr} {L w c : Nat} {rs : List Reg} (h : LKeep σ s B L w c)
    (k : Keep rs s t) (hf : Frm B (kgR w) s.mem t.mem) (sp : t.sp = s.sp)
    (he : ∀ r ∈ VG.Proof.MillerRabin.RISCV64.envRegs, r ∉ rs := by decide) (h1 : Reg.t1 ∉ rs := by decide)
    (h11 : Reg.s11 ∉ rs := by decide) : LKeep σ t B L w c :=
  ⟨Prep.ofKgR h.prep (h.prep.env.keep k he) (k.gpr h1) hf, h.frame.trans (frame_of_kgR hf h.prep.env.hZ _),
    sp.trans h.sp, k.2.1.trans h.rd, k.2.2.trans h.wr, (k.gpr h11).trans h.s11⟩

/-- `LInv` through a step that keeps memory and the registers it reads. -/
theorem LInv.ofMem {σ s t : State} {B R : Addr} {L w c rl ch : Nat} {r : Rand} {k n : Nat} {rs : List Reg}
    (h : LInv σ s B R L w c rl ch r k n) (hm : t.mem = s.mem) (k' : Keep rs s t) (sp : t.sp = s.sp)
    (he : ∀ r ∈ VG.Proof.MillerRabin.RISCV64.envRegs, r ∉ rs := by decide) (h1 : Reg.t1 ∉ rs := by decide)
    (h11 : Reg.s11 ∉ rs := by decide) : LInv σ t B R L w c rl ch r k n :=
  ⟨h.ctx.ofKgR (h.ctx.prep.env.keep k' he) (k'.gpr h1) (by rw [hm]; exact Frm.refl _ _ _) k'.2.1 k'.2.2 sp,
    by rw [hm]; exact h.used, by rw [hm]; exact h.idx, by rw [hm]; exact h.uni, by rw [hm]; exact h.stat,
    by rw [hm]; exact h.tape, by rw [hm]; exact h.frame, sp.trans h.sp, k'.2.1.trans h.rd, k'.2.2.trans h.wr,
    (k'.gpr h11).trans h.s11, h.mr⟩

/-- `RKept` for a range outside the round's and `hStat`, `hIdx`, by `omega` on
its offsets. -/
syntax "rkept_tac" : tactic
macro_rules
  | `(tactic| rkept_tac) => `(tactic| (
      intro i h1 h2
      simp only [RKept, Kept, slot, hdrBytes, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        at h1 h2 ⊢
      and_intros <;> omega_arith))

/-- The outcome of one draw from `k` witnesses: composite or probably prime
(with the loop's result), or one more witness and the loop goes on. -/
def DOut (σ s : State) (B R : Addr) (L w c rl ch : Nat) (r : Rand) (k n : Nat) : Prop :=
  LKeep σ s B L w c ∧ word s.mem B (8 * hUsed) = BitVec.ofNat 64 (8 * w + 8 * w * (k + 1)) ∧
    ((n = 0 ∧ word s.mem B (8 * hStat) = BitVec.ofNat 64 2 ∧
        loop (mrStep c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2) (1, 0) (r.drop (8 * w)) =
          some (false, r.drop (8 * w + 8 * w * (k + 1)))) ∨
      (n = 0 ∧ word s.mem B (8 * hStat) = BitVec.ofNat 64 1 ∧
        loop (mrStep c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2) (1, 0) (r.drop (8 * w)) =
          some (true, r.drop (8 * w + 8 * w * (k + 1)))) ∨
      (0 < n ∧ LInv σ s B R L w c rl ch r (k + 1) (n - 1)))

/-! ## A draw -/

/-- One draw: its octets, its witness, its round and the outcome. -/
theorem draw_ok (Ri : RoundImpl) {σ s : State} {B R : Addr} {L w c rl ch : Nat} {r : Rand} {k n : Nat}
    (h : LInv σ s B R L w c rl ch r k n) (hav : 8 * w + 8 * w * k + 8 * w ≤ rl) :
    WP isa (VG.Impl.RsaKeyGen.RISCV64.Witness.draw Ri.name Ri.code) s fun s' =>
      DOut σ s' B R L w c rl ch r k n := by
  have ctx := h.ctx
  have e := ctx.prep.env
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := e.hZ
  have hw4 := e.hw
  have hw128 := e.hw'
  have hnw := e.hs.nowrap
  obtain es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have hwb := ctx.wb
  obtain hrl : r.length = rl := by rw [← h.tape]; exact VG.Proof.RsaKeyGen.rand_bytes_length _ _ _
  obtain hk8 : 8 * k ≤ 8 * w * k := Nat.mul_le_mul_right k (by omega_arith)
  have hrl64 := ctx.rl64
  unfold VG.Impl.RsaKeyGen.RISCV64.Witness.draw
  -- The draw's octets.
  refine WP.seq (WP.mono (WP.rdwr (load_ok ctx h.used hav)) fun s1 ⟨⟨⟨v1, u1, f1, a71⟩, k1⟩, rd1, wr1, sp1⟩ => ?_)
  obtain f1' : Frm B (kgR w) s.mem s1.mem := VG.Proof.MillerRabin.RISCV64.Blinded.frm_widen f1 (by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨(8 * hUsed, 16), by simp [kgR], Nat.le_refl _, by omega_arith⟩
    · exact ⟨(slot w 3, 4 * (8 * (w + 2))), by simp [kgR], by rw [es, es]; omega_arith, by rw [es, es]; omega_arith⟩)
  obtain e1 : Env s1 B (8 * L) w := ⟨e.hs.congr k1.2.2, a71, (k1.gpr (by decide)).trans e.s5,
    (k1.gpr (by decide)).trans e.t0, (k1.gpr (by decide)).trans e.s6, e.hw, e.hw', e.hZ⟩
  obtain p1 : Prep s1 B L w c := Prep.ofKgR ctx.prep e1 (k1.gpr (by decide)) f1'
  obtain hx1 : A s1.mem B w 4 = Spec.Rsa.os2ip (seg r (8 * w + 8 * w * k) (8 * w)) := by
    rw [v1, ← h.tape, VG.Proof.RsaKeyGen.seg_bytesAt s.mem R hav]
  -- Words a step keeps.
  obtain w1 : ∀ d, d + 8 ≤ 256 → d ≠ 8 * hUsed → d % 8 = 0 → word s1.mem B d = word s.mem B d := fun d hd hn h8 =>
    f1.word_eq (fun q hq => by
      simp only [hUsed, List.mem_cons, List.not_mem_nil, or_false] at hq hn
      rcases hq with rfl | rfl <;> simp only [es] <;> omega_arith) (by omega_arith)
  obtain u1' : word s1.mem B (8 * hUni) = BitVec.ofNat 64 (mrSB c (8 * w) (8 * w) r k).2 :=
    (w1 _ (by simp only [hUni]; omega_arith) (by simp [hUni, hUsed]) (by simp [hUni])).trans h.uni
  -- The witness.
  refine WP.seq (WP.mono (WP.rdwr (witness_ok (mctx_of e1 p1.t1 p1.n) e1.s6 ctx.prep.odd ctx.cb u1'))
    fun s2 ⟨⟨⟨a42, u2, f2⟩, k2⟩, rd2, wr2, sp2⟩ => ?_)
  rw [hx1] at a42 u2
  change A s2.mem B w 4 = (wit c (8 * w) r (8 * w + 8 * w * k)).1 at a42
  change word s2.mem B (8 * hUni) = BitVec.ofNat 64 ((mrSB c (8 * w) (8 * w) r k).2 +
    if (wit c (8 * w) r (8 * w + 8 * w * k)).2 then 1 else 0) at u2
  obtain e2 : Env s2 B (8 * L) w := e1.keep k2 (by decide)
  obtain f12 : Frm B (kgR w) s.mem s2.mem := f1'.trans (VG.Proof.MillerRabin.RISCV64.Blinded.frm_widen f2 (by
    intro q hq
    simp only [witRanges, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [kgR], Nat.le_refl _, Nat.le_refl _⟩
    all_goals exact ⟨(slot w 3, 4 * (8 * (w + 2))), by simp [kgR], by (try rw [es, es]); (try dsimp only); omega_arith,
      by (try rw [es, es]); (try dsimp only); omega_arith⟩))
  obtain t12 : s2.gpr .t1 = s.gpr .t1 := (k2.gpr (by decide)).trans (k1.gpr (by decide))
  obtain p2 : Prep s2 B L w c := Prep.ofKgR ctx.prep e2 t12 f12
  obtain w2 : ∀ d, d + 8 ≤ 256 → d ≠ 8 * hUsed → d ≠ 8 * hUni → d % 8 = 0 →
      word s2.mem B d = word s.mem B d := fun d hd hn hn' h8 =>
    (f2.word_eq (fun q hq => by
      simp only [witRanges, hUni, List.mem_cons, List.not_mem_nil, or_false] at hq hn'
      rcases hq with rfl | rfl | rfl | rfl <;> simp only [es] <;> omega_arith) (by omega_arith)).trans (w1 d hd hn h8)
  obtain sp12 : s2.sp = s.sp := sp2.trans sp1
  obtain hac : (wit c (8 * w) r (8 * w + 8 * w * k)).1 < c :=
    VG.Proof.MillerRabin.RISCV64.Blinded.witness_lt ctx.cb (by omega_arith)
  obtain hk63 : k + 1 + 1 < 2 ^ 63 := by omega_arith
  obtain hUle : (mrSB c (8 * w) (8 * w) r k).2 + (if (wit c (8 * w) r (8 * w + 8 * w * k)).2 then 1 else 0) < 2 ^ 63 := by
    have := VG.Proof.RsaKeyGen.mrSB_uniform_le c (8 * w) (8 * w) r k
    split <;> omega_arith
  -- The round and its outcome.
  refine WP.mono (round_ok Ri p2 a42 hac (by rw [sp12]; exact ctx.sp16) (by rw [sp12]; exact ctx.sp)
    (by rw [sp12]; exact ctx.stk)
    ((w2 _ (by simp only [hIdx]; omega_arith) (by simp [hIdx, hUsed]) (by simp [hIdx, hUni]) (by simp [hIdx])).trans h.idx)
    u2 ((w2 _ (by simp only [hChecks]; omega_arith) (by simp [hChecks, hUsed]) (by simp [hChecks, hUni])
      (by simp [hChecks])).trans ctx.checks) hk63 hUle ctx.ch63) fun s3 h3 => ?_
  obtain hL8 : 256 ≤ 8 * L := by omega_arith
  obtain used3 : word s3.mem B (8 * hUsed) = BitVec.ofNat 64 (8 * w + 8 * w * (k + 1)) := by
    rw [h3.word (by simp only [hUsed]; omega_arith) (by simp only [hUsed]; rkept_tac)]
    rw [f2.word_eq (fun q hq => by
      simp only [witRanges, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> simp only [hUni, hUsed, es] <;> omega_arith)
      (by simp only [hUsed]; omega_arith), u1]
    exact congrArg _ (by rw [Nat.mul_succ]; omega_arith)
  obtain hUeq : (mrSB c (8 * w) (8 * w) r k).2 + (if (wit c (8 * w) r (8 * w + 8 * w * k)).2 then 1 else 0) =
      (mrSB c (8 * w) (8 * w) r (k + 1)).2 := by
    rw [VG.Proof.RsaKeyGen.mrSB_uniform_next]
    cases (wit c (8 * w) r (8 * w + 8 * w * k)).2 <;> rfl
  obtain uni3 : word s3.mem B (8 * hUni) = BitVec.ofNat 64 (mrSB c (8 * w) (8 * w) r (k + 1)).2 := by
    rw [h3.word (by simp only [hUni]; omega_arith) (by simp only [hUni]; rkept_tac), u2, hUeq]
  obtain frame3 : Frame [⟨B, 8 * L⟩, below σ.sp 96] σ.mem s3.mem := by
    refine h.frame.trans ((frame_of_kgR f12 hZ _).trans ?_)
    have := h3.frame
    rwa [sp12, h.sp] at this
  obtain sp3 : s3.sp = σ.sp := (h3.sp.trans sp12).trans h.sp
  obtain rd3 : s3.rd = σ.rd := ((h3.rd.trans rd2).trans rd1).trans h.rd
  obtain wr3 : s3.wr = σ.wr := ((h3.wr.trans wr2).trans wr1).trans h.wr
  obtain s113 : s3.gpr .s11 = σ.gpr .s11 :=
    (((h3.cs .s11 (by decide) (by decide) (by decide)).trans (k2.gpr (by decide))).trans (k1.gpr (by decide))).trans h.s11
  obtain lk : LKeep σ s3 B L w c := ⟨h3.prep, frame3, sp3, rd3, wr3, s113⟩
  obtain hav' : 8 * w + 8 * w * k + 8 * w ≤ r.length := by rw [hrl]; exact hav
  obtain hD : 8 * w + 8 * w * k + 8 * w = 8 * w + 8 * w * (k + 1) := by rw [Nat.mul_succ]; omega_arith
  have hround : Proof.MillerRabin.Round.round c (wit c (8 * w) r (8 * w + 8 * w * k)).1 =
      Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2
        (wit c (8 * w) r (8 * w + 8 * w * k)).1 := rfl
  have st3 := h3.stat
  have id3 := h3.idx
  cases hr : Proof.MillerRabin.Round.round c (wit c (8 * w) r (8 * w + 8 * w * k)).1
  · -- The witness proves `c` composite.
    rw [hr] at hround st3
    obtain ⟨hn0, hl⟩ := VG.Proof.RsaKeyGen.mrLoopAt_fail h.mr hwb (by omega_arith) hav' hround.symm
    rw [hD] at hl
    exact ⟨lk, used3, .inl ⟨hn0, st3, hl⟩⟩
  · rw [hr] at hround st3 id3
    simp only [↓reduceIte] at st3 id3
    rw [hUeq] at st3
    obtain hfirst := VG.Proof.RsaKeyGen.mrSB_first c (8 * w) (8 * w) r (k + 1)
    by_cases hd : 17 ≤ k + 1 + 1 ∧ ch ≤ (mrSB c (8 * w) (8 * w) r (k + 1)).2
    · have hg : ¬ VG.Proof.RsaKeyGen.goS ch (mrSB c (8 * w) (8 * w) r (k + 1)) := by
        unfold VG.Proof.RsaKeyGen.goS Spec.RsaKeyGen.blindedChecks
        omega_arith
      obtain ⟨hn0, hl⟩ := VG.Proof.RsaKeyGen.mrLoopAt_done h.mr hwb (by omega_arith) hav' hround.symm hg
      rw [hD] at hl
      exact ⟨lk, used3, .inr (.inl ⟨hn0, by rw [st3]; simp only [statOf, hd, and_self, ↓reduceIte], hl⟩)⟩
    · have hg : VG.Proof.RsaKeyGen.goS ch (mrSB c (8 * w) (8 * w) r (k + 1)) := by
        unfold VG.Proof.RsaKeyGen.goS Spec.RsaKeyGen.blindedChecks
        omega_arith
      obtain ⟨hn, mr'⟩ := VG.Proof.RsaKeyGen.mrLoopAt_next h.mr hwb (by omega_arith) hav' hround.symm hg
      obtain w3 : ∀ d, (d = 8 * hRand ∨ d = 8 * hRandLen ∨ d = 8 * hK ∨ d = 8 * hChecks) →
          word s3.mem B d = word s.mem B d := fun d hd' => by
        simp only [hRand, hRandLen, hK, hChecks] at hd'
        rcases hd' with rfl | rfl | rfl | rfl <;>
          (rw [h3.word (by omega_arith) (by rkept_tac)]
           exact w2 _ (by omega_arith) (by simp [hUsed]) (by simp [hUni]) (by omega_arith))
      obtain ctx3 : KCtx s3 B L w c R rl ch := ctx.keep h3.prep w3 (h3.rd.trans (rd2.trans rd1))
        (h3.wr.trans (wr2.trans wr1)) (h3.sp.trans sp12)
      obtain tape3 : Spec.Rsa.bytesAt s3.mem R rl = r := by
        obtain b3 := ctx.bytes_frame (m := σ.mem) (m' := s3.mem) (by rw [h.sp]; exact frame3)
        obtain b0 := ctx.bytes_frame (m := σ.mem) (m' := s.mem) (by rw [h.sp]; exact h.frame)
        rw [b3, ← b0, h.tape]
      exact ⟨lk, used3, .inr (.inr ⟨hn, ⟨ctx3, used3, id3, uni3,
        by rw [st3]; simp only [statOf, hd, ↓reduceIte], tape3, frame3, sp3, rd3, wr3, s113, mr'⟩⟩)⟩

/-! ## The loop -/

/-- What the loop leaves: what `primalityTest c (r.drop (8 w))` says, in
`hStat` and, unless the tape ran out, `hUsed`. -/
def MOut (σ s : State) (B : Addr) (L w c rl : Nat) (r : Rand) : Prop :=
  LKeep σ s B L w c ∧
    match Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) with
    | none => word s.mem B (8 * hStat) = BitVec.ofNat 64 0
    | some (b, rest) => word s.mem B (8 * hStat) = BitVec.ofNat 64 (if b then 1 else 2) ∧
        word s.mem B (8 * hUsed) = BitVec.ofNat 64 (rl - rest.length)

/-- The loop's check: `t4 :=` 1 if fewer than a draw's octets are left, else 0. -/
theorem check_ok {σ s : State} {B R : Addr} {L w c rl ch : Nat} {r : Rand} {k n : Nat}
    (h : LInv σ s B R L w c rl ch r k n) :
    WP isa (.block tapeShort) s
      fun u => ((u.gpr .t4 = BitVec.ofNat 64 (if rl - (8 * w + 8 * w * k) < 8 * w then 1 else 0) ∧
        u.mem = s.mem ∧ u.sp = s.sp) ∧ u.rd = s.rd ∧ u.wr = s.wr) ∧ Keep [.t2, .t3, .t4] s u := by
  have ctx := h.ctx
  have e := ctx.prep.env
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := e.hZ
  obtain hrl : r.length = rl := by rw [← h.tape]; exact VG.Proof.RsaKeyGen.rand_bytes_length _ _ _
  have hu : 8 * w + 8 * w * k ≤ r.length := h.mr.used
  rw [hrl] at hu
  have r144 : s.mem.readW (B + 144#64) 64 = BitVec.ofNat 64 rl := ctx.randLen
  have r152 : s.mem.readW (B + 152#64) 64 = BitVec.ofNat 64 (8 * w + 8 * w * k) := h.used
  have r216 : s.mem.readW (B + 216#64) 64 = BitVec.ofNat 64 (8 * w) := ctx.k
  have hrl64 := ctx.rl64
  obtain esub : BitVec.ofNat 64 rl - BitVec.ofNat 64 (8 * w + 8 * w * k) =
      BitVec.ofNat 64 (rl - (8 * w + 8 * w * k)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith
  obtain hD : 8 * w < 2 ^ 64 := by have := e.hw'; omega_arith
  refine WP.mono (WP.rdwr (WP.keep _ (Q := fun u =>
      u.gpr .t4 = BitVec.ofNat 64 (if rl - (8 * w + 8 * w * k) < 8 * w then 1 else 0) ∧ u.mem = s.mem) ?_
    (by rfl) (by rfl))) fun u ⟨⟨⟨u4, um⟩, ku⟩, rd, wr, sp⟩ => ⟨⟨⟨u4, um, sp⟩, rd, wr⟩, ku⟩
  simp only [tapeShort, ldh, hRandLen, hUsed, hK]
  brun [e.s6, e.hs.ld (d := 144) (n := 8) (by omega_arith), e.hs.al8 (d := 144) (by omega_arith) (by decide),
    e.hs.ld (d := 152) (n := 8) (by omega_arith), e.hs.al8 (d := 152) (by omega_arith) (by decide),
    e.hs.ld (d := 216) (n := 8) (by omega_arith), e.hs.al8 (d := 216) (by omega_arith) (by decide),
    r144, r152, r216, esub,
    VG.Proof.MillerRabin.RISCV64.Blinded.lt_flag (show rl - (8 * w + 8 * w * k) < 2 ^ 64 by omega_arith) hD]

/-- One iteration of the loop, from `k` witnesses with `n + 1` iterations
left: it ends with `MOut`, or goes on from `k + 1` with fewer left. -/
theorem body_ok (Ri : RoundImpl) {σ s : State} {B R : Addr} {L w c rl ch : Nat} {r : Rand} {k n : Nat}
    (h : LInv σ s B R L w c rl ch r k n)
    (hpt : Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) =
      loop (mrStep c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2) (1, 0) (r.drop (8 * w))) :
    WP isa (.seq (.block tapeShort)
        (.seq (.ite (.nonzero .t4) (.block [.li .t2 0, sth .t2 hStat])
            (VG.Impl.RsaKeyGen.RISCV64.Witness.draw Ri.name Ri.code))
          (.block [ldh .t2 hStat, .addi .t2 .t2 (-4)]))) s fun s' =>
      (isa.eval (.zero .t2) s' = some false ∧ n = 0 ∧ MOut σ s' B L w c rl r) ∨
      (isa.eval (.zero .t2) s' = some true ∧ 0 < n ∧ LInv σ s' B R L w c rl ch r (k + 1) (n - 1)) := by
  have ctx := h.ctx
  have e := ctx.prep.env
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := e.hZ
  have hw4 := e.hw
  have hwb := ctx.wb
  obtain hrl : r.length = rl := by rw [← h.tape]; exact VG.Proof.RsaKeyGen.rand_bytes_length _ _ _
  have hu : 8 * w + 8 * w * k ≤ r.length := h.mr.used
  rw [hrl] at hu
  -- How many octets are left.
  refine WP.seq (WP.mono (check_ok h) fun u ⟨⟨⟨u4, um, usp⟩, urd, uwr⟩, ku⟩ => ?_)
  obtain hu' : LInv σ u B R L w c rl ch r k n := h.ofMem um ku usp
  have eu : Env u B (8 * L) w := hu'.ctx.prep.env
  refine WP.seq (WP.ite _ (Steps.eval_nonzero u .t4) (fun hz => ?_) (fun hz => ?_))
  · -- Too few octets left.
    obtain hn : ¬ 8 * w ≤ rl - (8 * w + 8 * w * k) := fun hp => by
      rw [u4] at hz; simp only [Nat.not_lt.mpr hp, ↓reduceIte] at hz; exact absurd hz (by decide)
    obtain ⟨hn0, hl⟩ := VG.Proof.RsaKeyGen.mrLoopAt_short h.mr hwb (by omega_arith) (by rw [hrl]; omega_arith)
    refine WP.mono (WP.rdwr (VG.Proof.MillerRabin.RISCV64.Blinded.setStat_ok (v := 0) eu (by decide)))
      fun x ⟨⟨⟨xm, xsp⟩, kx⟩, _, _, _⟩ => ?_
    obtain fx : Frm B (kgR w) u.mem x.mem := by
      rw [xm]
      refine VG.Proof.MillerRabin.RISCV64.Blinded.frm_widen (rs := [(8 * hStat, 8)])
        (Frm.of_outside (o := 8 * hStat) (n := 8) (writeW_outside _ _ _ (by simp only [hStat]; omega_arith)) (by simp))
        ?_
      intro q hq
      simp only [List.mem_singleton] at hq
      subst hq
      exact ⟨(8 * hUsed, 16), by simp [kgR], by simp only [hUsed, hStat]; omega_arith,
        by simp only [hUsed, hStat]; omega_arith⟩
    obtain lx := hu'.keep.ofKgR kx fx xsp
    refine WP.mono (VG.Proof.MillerRabin.RISCV64.Blinded.tail_ok (v := 0) lx.prep.env
        (by rw [xm]; exact word_writeW_self _ _ _ _) (by decide))
      fun y ⟨⟨⟨yev, ym, ysp⟩, yrd, ywr⟩, ky⟩ => ?_
    refine .inl ⟨by rw [yev]; rfl, hn0, lx.ofKgR ky (by rw [ym]; exact Frm.refl _ _ _) ysp, ?_⟩
    show match Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) with
      | none => word y.mem B (8 * hStat) = BitVec.ofNat 64 0
      | some (b, rest) => word y.mem B (8 * hStat) = BitVec.ofNat 64 (if b then 1 else 2) ∧
          word y.mem B (8 * hUsed) = BitVec.ofNat 64 (rl - rest.length)
    rw [hpt, hl, ym, xm]
    exact word_writeW_self _ _ _ _
  · -- A draw.
    obtain hp : 8 * w ≤ rl - (8 * w + 8 * w * k) := by
      by_contra hp
      rw [u4] at hz; simp only [Nat.lt_of_not_le hp, ↓reduceIte] at hz; exact absurd hz (by decide)
    refine WP.mono (draw_ok Ri hu' (by omega_arith)) fun x ⟨lk, ux, hcase⟩ => ?_
    obtain hdrop : rl - (r.drop (8 * w + 8 * w * (k + 1))).length = 8 * w + 8 * w * (k + 1) := by
      rw [List.length_drop, hrl]
      have : 8 * w * (k + 1) = 8 * w * k + 8 * w := Nat.mul_succ _ _
      omega_arith
    rcases hcase with ⟨hn0, st2, hl⟩ | ⟨hn0, st1, hl⟩ | ⟨hn, li⟩
    · refine WP.mono (VG.Proof.MillerRabin.RISCV64.Blinded.tail_ok (v := 2) lk.prep.env st2 (by decide))
        fun y ⟨⟨⟨yev, ym, ysp⟩, yrd, ywr⟩, ky⟩ => ?_
      refine .inl ⟨by rw [yev]; rfl, hn0, lk.ofKgR ky (by rw [ym]; exact Frm.refl _ _ _) ysp, ?_⟩
      show match Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) with
        | none => word y.mem B (8 * hStat) = BitVec.ofNat 64 0
        | some (b, rest) => word y.mem B (8 * hStat) = BitVec.ofNat 64 (if b then 1 else 2) ∧
            word y.mem B (8 * hUsed) = BitVec.ofNat 64 (rl - rest.length)
      rw [hpt, hl, ym]
      exact ⟨st2, by rw [hdrop]; exact ux⟩
    · refine WP.mono (VG.Proof.MillerRabin.RISCV64.Blinded.tail_ok (v := 1) lk.prep.env st1 (by decide))
        fun y ⟨⟨⟨yev, ym, ysp⟩, yrd, ywr⟩, ky⟩ => ?_
      refine .inl ⟨by rw [yev]; rfl, hn0, lk.ofKgR ky (by rw [ym]; exact Frm.refl _ _ _) ysp, ?_⟩
      show match Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) with
        | none => word y.mem B (8 * hStat) = BitVec.ofNat 64 0
        | some (b, rest) => word y.mem B (8 * hStat) = BitVec.ofNat 64 (if b then 1 else 2) ∧
            word y.mem B (8 * hUsed) = BitVec.ofNat 64 (rl - rest.length)
      rw [hpt, hl, ym]
      exact ⟨st1, by rw [hdrop]; exact ux⟩
    · refine WP.mono (VG.Proof.MillerRabin.RISCV64.Blinded.tail_ok (v := 4) li.ctx.prep.env li.stat (by decide))
        fun y ⟨⟨⟨yev, ym, ysp⟩, yrd, ywr⟩, ky⟩ => .inr ⟨by rw [yev]; rfl, hn, li.ofMem ym ky ysp⟩

/-- The loop's first iteration count: one less than the iterations of the
specification's loop from the octets after the candidate. -/
def iters0 (c ch w : Nat) (r : Rand) : Nat :=
  VG.Proof.RsaKeyGen.itersOf (8 * w) r.length
    (VG.Proof.RsaKeyGen.shapeOf (loop (mrStep c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2)
      (1, 0) (r.drop (8 * w)))) (8 * w) - 1

/-- The loop's counts, `hIdx := 1`, `hUni := 0` and `hStat := 4`: the
invariant from no witnesses. -/
theorem init_ok {σ : State} {B R : Addr} {L w c rl ch : Nat} {r : Rand}
    (h : KCtx σ B L w c R rl ch) (hu : word σ.mem B (8 * hUsed) = BitVec.ofNat 64 (8 * w))
    (htape : Spec.Rsa.bytesAt σ.mem R rl = r) (h8 : 8 * w ≤ rl) :
    WP isa (.block [.li .t2 1, sth .t2 hIdx, .li .t2 0, sth .t2 hUni, .li .t2 4, sth .t2 hStat]) σ fun s0 =>
      LInv σ s0 B R L w c rl ch r 0 (iters0 c ch w r) := by
  have e := h.prep.env
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := e.hZ
  have hw4 := e.hw
  have hwb := h.wb
  obtain hrl : r.length = rl := by rw [← htape]; exact VG.Proof.RsaKeyGen.rand_bytes_length _ _ _
  refine WP.mono (WP.rdwr (WP.keep [.t2] (Q := fun s0 => s0.mem = ((σ.mem.writeW (off B (8 * hIdx)) (BitVec.ofNat 64 1)).writeW
      (off B (8 * hUni)) (BitVec.ofNat 64 0)).writeW (off B (8 * hStat)) (BitVec.ofNat 64 4))
    (by simp only [sth, hIdx, hUni, hStat]
        brun [exec_li (show imm12 1 by decide), exec_li (show imm12 0 by decide), exec_li (show imm12 4 by decide),
          e.s6, e.hs.st (d := 176) (n := 8) (by omega_arith), e.hs.al8 (d := 176) (by omega_arith) (by decide),
          e.hs.st (d := 16) (n := 8) (by omega_arith), e.hs.al8 (d := 16) (by omega_arith) (by decide),
          e.hs.st (d := 160) (n := 8) (by omega_arith), e.hs.al8 (d := 160) (by omega_arith) (by decide)])
      (by rfl) (by rfl))) fun s0 ⟨⟨m0, k0⟩, rd0, wr0, sp0⟩ => ?_
  obtain o1 := writeW_outside σ.mem B (BitVec.ofNat 64 1) (d := 8 * hIdx) (by simp only [hIdx]; omega_arith)
  obtain o2 := writeW_outside (σ.mem.writeW (off B (8 * hIdx)) (BitVec.ofNat 64 1)) B (BitVec.ofNat 64 0)
    (d := 8 * hUni) (by simp only [hUni]; omega_arith)
  obtain o3 := writeW_outside ((σ.mem.writeW (off B (8 * hIdx)) (BitVec.ofNat 64 1)).writeW (off B (8 * hUni))
    (BitVec.ofNat 64 0)) B (BitVec.ofNat 64 4) (d := 8 * hStat) (by simp only [hStat]; omega_arith)
  obtain f0 : Frm B (kgR w) σ.mem s0.mem := by
    rw [m0]
    refine Frm.trans (Frm.trans (Frm.of_outside o1 (by simp [kgR])) (Frm.of_outside o2 (by simp [kgR])))
      (VG.Proof.MillerRabin.RISCV64.Blinded.frm_widen (rs := [(8 * hStat, 8)]) (Frm.of_outside o3 (by simp)) ?_)
    intro q hq
    simp only [List.mem_singleton] at hq
    subst hq
    exact ⟨(8 * hUsed, 16), by simp [kgR], by simp only [hUsed, hStat]; omega_arith,
      by simp only [hUsed, hStat]; omega_arith⟩
  obtain e0 : Env s0 B (8 * L) w := e.keep k0 (by decide)
  obtain ctx0 := h.ofKgR e0 (k0.gpr (by decide)) f0 rd0 wr0 sp0
  obtain fr0 : Frame [⟨B, 8 * L⟩, below σ.sp 96] σ.mem s0.mem := frame_of_kgR f0 hZ _
  obtain hd := fun d (h1 : d + 8 ≤ 8 * hIdx ∨ 8 * hIdx + 8 ≤ d) (h2 : d + 8 ≤ 8 * hUni ∨ 8 * hUni + 8 ≤ d)
      (h3 : d + 8 ≤ 8 * hStat ∨ 8 * hStat + 8 ≤ d) (h4 : d + 8 ≤ 2 ^ 64) =>
    (o3.word h3 h4).trans ((o2.word h2 h4).trans (o1.word h1 h4))
  refine ⟨ctx0, ?_, ?_, ?_, ?_, ?_, fr0, sp0, rd0, wr0, k0.gpr (by decide),
    VG.Proof.RsaKeyGen.mrLoopAt_zero hwb (by omega_arith) (by rw [hrl]; exact h8)⟩
  · rw [m0, hd _ (by simp only [hUsed, hIdx]; omega_arith) (by simp only [hUsed, hUni]; omega_arith)
      (by simp only [hUsed, hStat]; omega_arith) (by simp only [hUsed]; omega_arith), hu, Nat.mul_zero, Nat.add_zero]
  · rw [m0, o3.word (by simp only [hIdx, hStat]; omega_arith) (by simp only [hIdx]; omega_arith),
      o2.word (by simp only [hIdx, hUni]; omega_arith) (by simp only [hIdx]; omega_arith)]
    exact word_writeW_self _ _ _ _
  · rw [m0, o3.word (by simp only [hUni, hStat]; omega_arith) (by simp only [hUni]; omega_arith)]
    exact word_writeW_self _ _ _ _
  · rw [m0]; exact word_writeW_self _ _ _ _
  · rw [← htape]
    exact h.bytes_frame fr0

/-- RSA's witnesses, after the candidate's `8 w` octets: `MOut`. -/
theorem millerRabin_ok (Ri : RoundImpl) {σ : State} {B R : Addr} {L w c rl ch : Nat} {r : Rand}
    (h : KCtx σ B L w c R rl ch) (hu : word σ.mem B (8 * hUsed) = BitVec.ofNat 64 (8 * w))
    (htape : Spec.Rsa.bytesAt σ.mem R rl = r) (h8 : 8 * w ≤ rl)
    (hpt : Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) =
      loop (mrStep c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2) (1, 0) (r.drop (8 * w))) :
    WP isa (VG.Impl.RsaKeyGen.RISCV64.Witness.millerRabin Ri.name Ri.code) σ fun s' => MOut σ s' B L w c rl r := by
  unfold VG.Impl.RsaKeyGen.RISCV64.Witness.millerRabin
  refine WP.seq (WP.mono (init_ok h hu htape h8) fun s0 l0 => ?_)
  refine WP.loop (Q := fun s' => MOut σ s' B L w c rl r)
    (fun n s => ∃ k, LInv σ s B R L w c rl ch r k n) (fun n s ⟨k, hk⟩ => ?_) _ s0 ⟨0, l0⟩
  exact WP.mono (body_ok Ri hk hpt) fun s' hs => hs.elim (fun ⟨ev, _, q⟩ => .inl ⟨ev, q⟩)
    (fun ⟨ev, hn, li⟩ => .inr ⟨ev, n - 1, by omega_arith, k + 1, li⟩)

/-! ## The test's result -/

/-- The test's result from the status and octets read the witnesses left in
the header: 0 if the tape ran out, the probable prime, or 3. -/
theorem res_ok {s0 u : State} {w c : Nat} (hc : Ctx s0 u) (hp : Prep u (stackArg s0 1) (sL s0) w c)
    (hw : oL s0 = 8 * w)
    (hres : match Spec.RsaKeyGen.primalityTest c ((Spec.Rsa.bytesAt s0.mem (s0.gpr .a7) (rL s0)).drop (8 * w)) with
      | none => word u.mem (stackArg s0 1) (8 * hStat) = BitVec.ofNat 64 0
      | some (b, rest) => word u.mem (stackArg s0 1) (8 * hStat) = BitVec.ofNat 64 (if b then 1 else 2) ∧
          word u.mem (stackArg s0 1) (8 * hUsed) = BitVec.ofNat 64 (rL s0 - rest.length))
    (hop : cOp s0 = (Spec.RsaKeyGen.primalityTest c
        ((Spec.Rsa.bytesAt s0.mem (s0.gpr .a7) (rL s0)).drop (8 * w))).map
      fun pr => (if pr.1 then .prime c else .rejected, pr.2)) :
    WP isa VG.Impl.RsaKeyGen.RISCV64.Candidate.testResult u fun t => Fr s0 t ∧ CQ s0 (t.gpr .a0) t.mem := by
  have hf := hc.fr
  have hP := hf.pre
  have e := hp.env
  obtain hcS : (cO s0).Disjoint ⟨stackArg s0 1, 8 * sL s0⟩ := by
    have := hP.oS; simp only [cS, sL] at this ⊢; rwa [Nat.mul_comm]
  generalize hB : stackArg s0 1 = B at hp e hres hcS
  have hs := e.hs
  have hnw := hs.nowrap
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * sL s0 := e.hZ
  -- A store to the octets read keeps the scratch.
  obtain keepS : ∀ (m : Mem) (v : BitVec 64) (d : Nat), d + 8 ≤ 8 * sL s0 →
      (m.writeW (fw s0 VG.Impl.RsaKeyGen.RISCV64.Candidate.oRead) v).readW (off B d) 64 = m.readW (off B d) 64 :=
    fun m v d hd =>
      ((Frame.refl [rdW s0] m).writeW (r := rdW s0) (List.mem_singleton_self _) v (Region.contains_self _ _)).readW
        (r := ⟨off B d, 8⟩) (Region.contains_self _ _) (fun ρ hρ => by
          simp only [List.mem_singleton] at hρ; subst hρ
          refine (hP.FS.sub_left (fw_sub s0 (o := VG.Impl.RsaKeyGen.RISCV64.Candidate.oRead) (n := 8)
            (by decide))).symm.sub_left ?_
          rw [← hB]
          have := Offset.sub_base (stackArg s0 1) (d := d) (n := 8) (k := (stackArg s0 2).toNat * 8)
            (by simp only [sL] at hd; omega_arith)
          exact this) (by decide)
  obtain al : ∀ o, o % 8 = 0 → (fb s0 + BitVec.ofNat 64 o).toNat % 8 = 0 := fun o h8 => fw_al hP h8
  obtain hW : InRegions u.wr (fb s0 + BitVec.ofNat 64 176) 8 :=
    ⟨kF s0, by rw [hf.wr]; exact List.mem_cons_self, kF_contains (by decide)⟩
  obtain r160 : (u.mem.writeW (fb s0 + 176#64) (u.mem.readW (B + 152#64) 64)).readW (B + 160#64) 64 =
      u.mem.readW (B + 160#64) 64 := keepS _ _ 160 (by omega_arith)
  unfold VG.Impl.RsaKeyGen.RISCV64.Candidate.testResult
  refine WP.seq (WP.mono (WP.rdwr (WP.keep [.t2] (Q := fun t =>
      t.mem = u.mem.writeW (fw s0 VG.Impl.RsaKeyGen.RISCV64.Candidate.oRead) (word u.mem B (8 * hUsed)) ∧
        t.gpr .t2 = word u.mem B (8 * hStat)) (by
    simp only [ldh, hUsed, hStat, VG.Impl.RsaKeyGen.RISCV64.Candidate.stf,
      VG.Impl.RsaKeyGen.RISCV64.Candidate.oRead]
    brun [e.s6, hf.s11, hs.ld (d := 152) (n := 8) (by omega_arith), hs.al8 (d := 152) (by omega_arith) (by decide),
      hs.ld (d := 160) (n := 8) (by omega_arith), hs.al8 (d := 160) (by omega_arith) (by decide),
      al 176 (by decide), hW, r160]) (by rfl) (by rfl))) fun t₁ ⟨⟨⟨m₁, a₁⟩, k₁⟩, rd₁, wr₁, sp₁⟩ => ?_)
  obtain c₁ : Ctx s0 t₁ := hc.step sp₁ k₁.2.1 k₁.2.2 (k₁.gpr (by decide)) (by
    rw [m₁]
    exact (Frame.refl _ _).writeW (r := rdW s0) (w := 64) (by simp) _ (Region.contains_self _ _))
  obtain hus₁ : t₁.mem.readW (fw s0 VG.Impl.RsaKeyGen.RISCV64.Candidate.oRead) 64 = word u.mem B (8 * hUsed) := by
    rw [m₁]; exact Mem.readW_writeW_self64 _ _ _
  generalize hpt : Spec.RsaKeyGen.primalityTest c ((Spec.Rsa.bytesAt s0.mem (s0.gpr .a7) (rL s0)).drop (8 * w)) = pt
    at hres hop
  rcases pt with _ | ⟨b, rest⟩
  · refine WP.ite _ (Steps.eval_zero_ofNat _ _ (by decide) (a₁.trans hres)) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact finNone_post c₁ (by rw [hop]; rfl)
  · obtain ⟨hst, hus⟩ := hres
    refine WP.ite _ (Steps.eval_zero_ofNat _ _ (by split <;> decide) (a₁.trans hst))
      (fun h => absurd h (by cases b <;> decide)) (fun _ => ?_)
    refine WP.seq (WP.mono (WP.rdwr (WP.keep [.t2] (Q := fun t => t.gpr .t2 = BitVec.ofNat 64 (if b then 0 else 1) ∧
        t.mem = t₁.mem) (by
      brun [a₁, hst]
      cases b <;> rfl) (by rfl) (by rfl))) fun t₂ ⟨⟨⟨b₂, m₂⟩, k₂⟩, rd₂, wr₂, sp₂⟩ => ?_)
    obtain c₂ : Ctx s0 t₂ := c₁.step sp₂ k₂.2.1 k₂.2.2 (k₂.gpr (by decide)) (by rw [m₂]; exact Frame.refl _ _)
    refine WP.ite _ (Steps.eval_zero_ofNat _ _ (by split <;> decide) b₂) (fun h => ?_) (fun h => ?_)
    · have hb : b = true := by revert h; cases b <;> decide
      subst hb
      obtain hs₂ : Scr t₂ B (8 * sL s0) := hs.congr (k₂.2.2.trans k₁.2.2)
      obtain e0 : slot w 0 = 256 := by simp [slot, hdrBytes]
      obtain h7 : t₂.gpr .a7 = VG.Proof.Mont.off B 256 := by
        rw [k₂.gpr (by decide), k₁.gpr (by decide), e.a7, e0]
      refine finPrime_post c₂ hs₂ h7
        (by rw [hw]; omega_arith) hw hcS ?_ (by rw [hop]; rfl) (by rw [m₂, hus₁, hus])
      obtain hv : A t₂.mem B w 0 = c := by
        rw [← hp.n]; simp only [A, Pre.wordsVal_eq_wv]; rw [m₂, m₁]
        exact VG.Proof.Bignum.wv_congr fun i hi => keepS _ _ _ (by simp only [slot, hdrBytes]; omega_arith)
      simp only [A, e0] at hv
      exact hv
    · have hb : b = false := by revert h; cases b <;> decide
      subst hb
      exact fin_ok 3 (by decide) c₂ (by rw [hop]; rfl) (by rw [outOf, hop]; rfl)
        (by rw [m₂, hus₁, hus, usedOf, hop]; rfl)

end VG.Proof.RsaKeyGen.RISCV64.Cand

end

end

/-!
# A candidate on RISC-V: the body

As on PPC64LE (`Proof/RsaKeyGen/PPC64LE/Cand/{Main,Tail,Body}.lean`), what the
body between the entry and the restore leaves (`mid_ok`), and so the whole
function (`code_correct`): the contract's results (`CQ`).

* `out` zeroed (`zeroOut_ok`), then 0 if `rand` is shorter than `out_len`;
* otherwise (`main_ok`) the working space set up (`setup_ok`) and the
  candidate drawn (`loadC_ok`); 2 if it is too close to `p`
  (`closeCheck_ok`); 3 unless `gcd(c − 1, e) = 1` (`gcdCheck_ok`);
* then (`test_ok`) the test's arguments in the header (`testArgs_ok`), trial
  division (`DivOk`), 3 if it finds a divisor, and otherwise the working
  space prepared (`prep_ok`), the witnesses (`millerRabin_ok`) and the result
  (`res_ok`).

The octets read are in the frame (`oRead`), not a register: each stage
carries them.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Cand

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot)
open VG.Proof.Mont (off ofs word Outside Outs)
open VG.Proof.MillerRabin.RISCV64 (Env A RoundImpl)
open VG.Proof.MillerRabin.RISCV64.Search (Prep)
open VG.Impl.RsaKeyGen.RISCV64.Candidate (main setup loadC closeCheck gcdCheck test testArgs testResult finish
  finNone nArr aP aBnd aCm1 hTrial oRead oRandLen oOutLen ldf)
open VG.Impl.MillerRabin.RISCV64.Search (hUsed hStat hRand hRandLen hK hChecks)
open VG.Impl.RsaKeyGen (TrialTable32.symbol TrialTable32.packed)

/-! ## The working space prepared for the round -/

section
open VG.Proof.Mont
open VG.Impl.MillerRabin.RISCV64.Search (montPrepHi)
open VG.Proof.MillerRabin.RISCV64.Search (montPrepHi_ok mpRanges mpRegs)

theorem prep_ok {s : State} {B : Addr} {L w c : Nat} (h : Env s B (8 * L) w) (hl : Lay s.mem B L w)
    (hn : A s.mem B w 0 = c) (hodd : c % 2 = 1) (h3 : 3 ≤ c) (hct : 2 ^ (64 * (w - 1)) < c) :
    WP isa montPrepHi s fun t => (Prep t B L w c ∧ Outs B (mpRanges w) s.mem t.mem) ∧ Keep mpRegs s t := by
  have hnw := h.hs.nowrap
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := h.hZ
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  refine WP.mono (montPrepHi_ok h hn hodd h3 hct) fun t ⟨⟨e, n, inv, t1, r1, r9, r10, ee, l, o⟩, k⟩ => ⟨⟨?_, o⟩, k⟩
  have ow : ∀ d, d + 8 ≤ 56 ∨ (64 ≤ d ∧ d + 8 ≤ 256) →
      VG.Proof.Bignum.word t.mem B d = VG.Proof.Bignum.word s.mem B d := fun d hd =>
    (show VG.Proof.Bignum.Frm B (mpRanges w) s.mem t.mem from o).word_eq (fun x hx => by
      simp only [mpRanges, VG.Impl.MillerRabin.RISCV64.aE, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp only [es] <;> omega_using [hd]) (by omega_using [hd])
  exact ⟨e, (ow 0 (by omega_using [])).trans hl.len, (ow 48 (by omega_using [])).trans hl.wW, (ow 224 (by omega_using [])).trans hl.strideW,
    fun j hj => (ow _ (by omega_using [hj])).trans (hl.arrW j hj), n, h3, hodd, inv, t1, r1, r9, r10, ee, l⟩

end

/-! ## Helpers -/

theorem slot_lin (w j : Nat) : slot w j = 256 + j * (8 * w) + j * 16 := by
  show VG.Impl.Bignum.hdrBytes + j * (8 * (w + 2)) = _
  rw [Nat.mul_add 8 w 2, Nat.mul_add, ← Nat.add_assoc]; rfl

theorem bytesAt_len (m : Mem) (a : Addr) (n : Nat) : (Spec.Rsa.bytesAt m a n).length = n := by
  simp [Spec.Rsa.bytesAt]

theorem take_bytesAt (m : Mem) (a : Addr) {k n : Nat} (h : k ≤ n) :
    (Spec.Rsa.bytesAt m a n).take k = Spec.Rsa.bytesAt m a k := by
  unfold Spec.Rsa.bytesAt
  rw [← List.map_take, List.take_range, Nat.min_eq_left h]

theorem bv_ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

section
variable {s0 : State}

/-- The candidate's words. -/
abbrev cw (s0 : State) : Nat := oL s0 / 8

/-- The candidate. -/
abbrev candOf (s0 : State) : Nat :=
  Spec.RsaKeyGen.candidate (64 * cw s0) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .a7) (8 * cw s0)))

/-- `p`'s octets. -/
abbrev pB (s0 : State) : List Byte := Spec.Rsa.bytesAt s0.mem (s0.gpr .a5) (s0.gpr .a6).toNat

/-- `rand`'s octets. -/
abbrev rB (s0 : State) : List Byte := Spec.Rsa.bytesAt s0.mem (s0.gpr .a7) (rL s0)

theorem cw_facts (hp : CIn s0) : oL s0 = 8 * cw s0 ∧ 4 ≤ cw s0 ∧ cw s0 ≤ 64 := by
  have hv := hp.valid
  simp only [Spec.RsaKeyGen.primeLenValid] at hv
  simp only [cw, oL]
  omega_using [hv]

/-- What the contract asks, from the candidate in the first `8 w` octets. -/
theorem cOp_cand (hp : CIn s0) (hav : oL s0 ≤ rL s0) :
    cOp s0 = VG.Proof.RsaKeyGen.afterDraw (64 * cw s0) (eV s0) (Spec.RsaKeyGen.otherPrime (pB s0)) (candOf s0)
      ((rB s0).drop (8 * cw s0)) := by
  obtain ⟨hw, hw4, _⟩ := cw_facts hp
  unfold cOp Spec.RsaKeyGen.candidateOp
  rw [hw, VG.Proof.RsaKeyGen.candidateStep_eq _ _ _ _ (by omega_using [hw4]), show 8 * (8 * cw s0) = 64 * cw s0 by omega_using [],
    VG.Proof.RsaKeyGen.ite_t (by rw [bytesAt_len]; omega_using [hav, hw])]
  unfold VG.Proof.RsaKeyGen.seg
  rw [List.drop_zero, take_bytesAt _ _ (by omega_using [hav, hw])]

/-- Too few octets for a candidate. -/
theorem cOp_none (hp : CIn s0) (h : ¬ oL s0 ≤ rL s0) : cOp s0 = none := by
  obtain ⟨hw, hw4, _⟩ := cw_facts hp
  unfold cOp Spec.RsaKeyGen.candidateOp
  rw [hw, VG.Proof.RsaKeyGen.candidateStep_eq _ _ _ _ (by omega_using [hw4]),
    VG.Proof.RsaKeyGen.ite_f (by rw [bytesAt_len]; omega_using [h, hw])]

theorem hlen_drop (w : Nat) : ((rB s0).drop (8 * w)).length = rL s0 - 8 * w := by
  rw [List.length_drop, bytesAt_len]

/-! ## The table of trial division -/

/-- The table of trial division, from the call's start. -/
structure TabOk (s0 : State) : Prop where
  fit : (s0.syms TrialTable32.symbol).toNat + 8 * 1024 ≤ 2 ^ 64
  al : (s0.syms TrialTable32.symbol).toNat % 8 = 0
  rd : (⟨s0.syms TrialTable32.symbol, 8 * 1024⟩ : Region) ∈ s0.rd
  held : ∀ i < 1024, s0.mem.readW (s0.syms TrialTable32.symbol + BitVec.ofNat 64 (8 * i)) 64 =
    TrialTable32.packed.getD i 0
  dj : ∀ ρ ∈ [cO s0, cU s0, cS s0, cF s0], (⟨s0.syms TrialTable32.symbol, 8 * 1024⟩ : Region).Disjoint ρ

/-- The table's words through the body. -/
theorem TabOk.held_at (h : TabOk s0) {s : State} (hf : Fr s0 s) {i : Nat} (hi : i < 1024) :
    s.mem.readW (s0.syms TrialTable32.symbol + BitVec.ofNat 64 (8 * i)) 64 = TrialTable32.packed.getD i 0 := by
  rw [hf.out.readW (r := ⟨s0.syms TrialTable32.symbol, 8 * 1024⟩)
    (Offset.contains_base _ (by omega_using [hi]) (by have := h.fit; omega_using [hi])) h.dj (by decide)]
  exact h.held i hi

/-! ## Keeping the body's state -/

/-- `Ctx` through code that keeps memory, the regions, the stack pointer and
`s11`. -/
theorem Ctx.keep {s t : State} {rs : List Reg} (h : Ctx s0 s) (k : Keep rs s t) (hm : t.mem = s.mem)
    (sp : t.sp = s.sp) (h11 : .s11 ∉ rs := by decide) : Ctx s0 t :=
  h.step sp k.2.1 k.2.2 (k.gpr h11) (by rw [hm]; exact Frame.refl _ _)

/-- What changes only within `scratch` keeps the body's state. -/
theorem frame4 {m m' : Mem} (f : Frame [cS s0] m m') : Frame [cU s0, cS s0, rF s0, rdW s0] m m' :=
  f.mono (by simp)

/-- The octets read survive what changes only `scratch`. -/
theorem rd_keep (hp : CIn s0) {m m' : Mem} (f : Frame [cS s0] m m') :
    m'.readW (fw s0 oRead) 64 = m.readW (fw s0 oRead) 64 :=
  f.readW (r := ⟨fw s0 oRead, 8⟩) (Region.contains_self _ _) (fun ρ hρ => by
    simp only [List.mem_singleton] at hρ; subst hρ
    exact hp.FS.sub_left (fw_sub s0 (by decide))) (by decide)

end

/-! ## Once `rand` has the candidate's octets -/

section
variable {s0 : State}

/-- The body's state once `rand` has the candidate's octets. -/
structure MIn (s0 s : State) : Prop where
  ctx : Ctx s0 s
  s6 : s.gpr .s6 = stackArg s0 1
  hav : oL s0 ≤ rL s0
  syms : s.syms = s0.syms
  tab : TabOk s0

/-- After `setup`. -/
structure M1 (s0 s : State) : Prop where
  ctx : Ctx s0 s
  env : Env s (stackArg s0 1) (8 * sL s0) (cw s0)
  lay : Lay s.mem (stackArg s0 1) (sL s0) (cw s0)
  zs : ∀ i < nArr * (cw s0 + 2), word s.mem (stackArg s0 1) (256 + 8 * i) = 0
  hav : oL s0 ≤ rL s0
  syms : s.syms = s0.syms
  tab : TabOk s0

theorem setupS {s : State} (h : MIn s0 s) : WP isa setup s (M1 s0) := by
  have hp := h.ctx.fr.pre
  obtain ⟨hw, _, _⟩ := cw_facts hp
  refine WP.mono_syms (setup_ok h.ctx h.s6 hw) fun t ⟨⟨c₁, e₁, l₁, z₁, _⟩, _⟩ sy => ?_
  exact ⟨c₁, e₁, l₁, z₁, h.hav, sy.trans h.syms, h.tab⟩

/-- After `loadC`. -/
structure M2 (s0 s : State) : Prop where
  ctx : Ctx s0 s
  env : Env s (stackArg s0 1) (8 * sL s0) (cw s0)
  lay : Lay s.mem (stackArg s0 1) (sL s0) (cw s0)
  zs : ∀ i, cw s0 ≤ i → i < nArr * (cw s0 + 2) → word s.mem (stackArg s0 1) (256 + 8 * i) = 0
  v : A s.mem (stackArg s0 1) (cw s0) 0 = candOf s0
  rd8 : s.mem.readW (fw s0 oRead) 64 = BitVec.ofNat 64 (8 * cw s0)
  hav : oL s0 ≤ rL s0
  syms : s.syms = s0.syms
  tab : TabOk s0

theorem loadCS {s : State} (h : M1 s0 s) : WP isa loadC s (M2 s0) := by
  have hp := h.ctx.fr.pre
  obtain ⟨hw, hw4, hw64⟩ := cw_facts hp
  have hZ := h35_of hp hw
  have hnw := h.env.hs.nowrap
  simp only [nArr, slot_lin] at hZ
  refine WP.mono_syms (loadC_ok h.ctx h.env hw h.hav) fun t ⟨⟨c₂, e₂, v₂, r₂, ow⟩, _⟩ sy => ?_
  have ow' : ∀ d, d + 8 ≤ 256 → word t.mem (stackArg s0 1) d = word s.mem (stackArg s0 1) d := fun d hd =>
    ow d (by omega_using [hZ, hd]) (.inl (by rw [slot_lin]; omega_using [hd]))
  refine ⟨c₂, e₂, ⟨(ow' 0 (by omega_using [])).trans h.lay.len, (ow' 48 (by omega_using [])).trans h.lay.wW,
      (ow' 224 (by omega_using [])).trans h.lay.strideW, fun j hj => (ow' _ (by omega_using [hj])).trans (h.lay.arrW j hj)⟩,
    fun i h1 h2 => ?_, v₂, r₂, h.hav, sy.trans h.syms, h.tab⟩
  have h2' := h2
  simp only [nArr] at h2'
  rw [ow _ (by omega_using [hZ, h2']) (.inr (by rw [slot_lin]; omega_using [h1])), h.zs i h2]

/-- After `closeCheck`. -/
structure M3 (s0 s : State) : Prop where
  ctx : Ctx s0 s
  env : Env s (stackArg s0 1) (8 * sL s0) (cw s0)
  lay : Lay s.mem (stackArg s0 1) (sL s0) (cw s0)
  v : A s.mem (stackArg s0 1) (cw s0) 0 = candOf s0
  f : s.gpr .s9 = BitVec.ofNat 64
    (if Spec.RsaKeyGen.tooClose (64 * cw s0) (Spec.RsaKeyGen.otherPrime (pB s0)) (candOf s0) then 1 else 0)
  rd8 : s.mem.readW (fw s0 oRead) 64 = BitVec.ofNat 64 (8 * cw s0)
  hav : oL s0 ≤ rL s0
  syms : s.syms = s0.syms
  tab : TabOk s0

theorem closeS {s : State} (h : M2 s0 s) : WP isa closeCheck s (M3 s0) := by
  have hp := h.ctx.fr.pre
  obtain ⟨hw, hw4, hw64⟩ := cw_facts hp
  have hZ := h35_of hp hw
  have hnw := h.env.hs.nowrap
  simp only [nArr, slot_lin] at hZ
  refine WP.mono_syms (WP.rdwr (closeCheck_ok h.ctx h.env hw h.v
    (by rw [show slot (cw s0) 0 + 8 * cw s0 = 256 + 8 * cw s0 by rw [slot_lin]; omega_using []]
        exact h.zs (cw s0) (by omega_using []) (by simp only [nArr]; omega_using []))
    (by rw [show slot (cw s0) aP + 8 * cw s0 = 256 + 8 * (28 * (cw s0 + 2) + cw s0) by
          simp only [aP, slot_lin]; omega_using []]
        exact h.zs _ (by omega_using []) (by simp only [nArr]; omega_using []))
    (fun i hi => by
      rw [show slot (cw s0) aBnd + 8 * i = 256 + 8 * (32 * (cw s0 + 2) + i) by simp only [aBnd, slot_lin]; omega_using []]
      exact h.zs _ (by omega_using []) (by simp only [nArr]; omega_using [hi]))))
    fun t ⟨⟨⟨c₃, e₃, f₃, o₃⟩, _⟩, _, _, _⟩ sy => ?_
  have fS := out_frame (by simp only [aP, slot_lin]; omega_using [hZ]) o₃
  have ow : ∀ d, d + 8 ≤ 256 → word t.mem (stackArg s0 1) d = word s.mem (stackArg s0 1) d := fun d hd =>
    o₃.word (.inl (by simp only [aP, slot_lin]; omega_using [hd])) (by omega_using [hd])
  refine ⟨c₃, e₃, ⟨(ow 0 (by omega_using [])).trans h.lay.len, (ow 48 (by omega_using [])).trans h.lay.wW,
      (ow 224 (by omega_using [])).trans h.lay.strideW, fun j hj => (ow _ (by omega_using [hj])).trans (h.lay.arrW j hj)⟩,
    ?_, f₃, (rd_keep hp fS).trans h.rd8, h.hav, sy.trans h.syms, h.tab⟩
  rw [← h.v]
  exact o₃.wordsVal (.inl (by simp only [aP, slot_lin]; omega_using [])) (by rw [slot_lin]; omega_using [hw64])

/-- An end with the octets of the candidate read. -/
theorem drawnFin (k : Nat) (hk : k < 2048) {s : State} (hc : Ctx s0 s)
    (r8 : s.mem.readW (fw s0 oRead) 64 = BitVec.ofNat 64 (8 * cw s0)) (hav : oL s0 ≤ rL s0)
    {x : Spec.RsaKeyGen.Candidate} (hop : cOp s0 = some (x, (rB s0).drop (8 * cw s0)))
    (hout : outOf s0 = List.replicate (oL s0) 0) (hst : Spec.RsaKeyGen.candidateStatus (cOp s0) = k) :
    WP isa (finish k) s fun t => Fr s0 t ∧ CQ s0 (t.gpr .a0) t.mem := by
  obtain ⟨hw, _, _⟩ := cw_facts hc.fr.pre
  refine fin_ok k hk hc hst hout ?_
  rw [r8, usedOf, hop]
  simp only [hlen_drop]
  congr 1; omega_using [hav, hw]

/-- Too close to `p`. -/
theorem closeFin {s : State} (h : M3 s0 s)
    (hcl : Spec.RsaKeyGen.tooClose (64 * cw s0) (Spec.RsaKeyGen.otherPrime (pB s0)) (candOf s0) = true) :
    WP isa (finish 2) s fun t => Fr s0 t ∧ CQ s0 (t.gpr .a0) t.mem := by
  have hop := cOp_cand h.ctx.fr.pre h.hav
  rw [VG.Proof.RsaKeyGen.afterDraw, hcl] at hop
  simp only [↓reduceIte] at hop
  exact drawnFin 2 (by decide) h.ctx h.rd8 h.hav hop (by rw [outOf, hop]) (by rw [hop]; rfl)

/-- After `gcdCheck`. -/
structure M4 (s0 s : State) : Prop where
  ctx : Ctx s0 s
  env : Env s (stackArg s0 1) (8 * sL s0) (cw s0)
  lay : Lay s.mem (stackArg s0 1) (sL s0) (cw s0)
  v : A s.mem (stackArg s0 1) (cw s0) 0 = candOf s0
  ncl : Spec.RsaKeyGen.tooClose (64 * cw s0) (Spec.RsaKeyGen.otherPrime (pB s0)) (candOf s0) = false
  g : s.gpr .s9 = 0 ↔ Nat.gcd (candOf s0 - 1) (eV s0) = 1
  rd8 : s.mem.readW (fw s0 oRead) 64 = BitVec.ofNat 64 (8 * cw s0)
  hav : oL s0 ≤ rL s0
  syms : s.syms = s0.syms
  tab : TabOk s0

theorem gcdS {s : State} (h : M3 s0 s)
    (hncl : Spec.RsaKeyGen.tooClose (64 * cw s0) (Spec.RsaKeyGen.otherPrime (pB s0)) (candOf s0) = false) :
    WP isa gcdCheck s (M4 s0) := by
  have hp := h.ctx.fr.pre
  obtain ⟨hw, hw4, hw64⟩ := cw_facts hp
  have hZ := h35_of hp hw
  have hZ' := hZ
  have hnw := h.env.hs.nowrap
  simp only [nArr, slot_lin] at hZ'
  have hshape : VG.Proof.RsaKeyGen.PrimeShape (64 * cw s0) (candOf s0) :=
    VG.Proof.RsaKeyGen.candidate_shape (by omega_using [hw4]) _
  refine WP.mono_syms (WP.rdwr (gcdCheck_ok h.ctx.fr h.env hZ h.v hshape.1))
    fun t ⟨⟨⟨g₄, o₄⟩, k₄⟩, _, _, sp₄⟩ sy => ?_
  have fS := out_frame (by simp only [aCm1, slot_lin]; omega_using [hZ']) o₄
  have ow : ∀ d, d + 8 ≤ 256 → word t.mem (stackArg s0 1) d = word s.mem (stackArg s0 1) d := fun d hd =>
    o₄.word (.inl (by simp only [aCm1, slot_lin]; omega_using [hd])) (by omega_using [hd])
  refine ⟨h.ctx.step sp₄ k₄.2.1 k₄.2.2 (k₄.gpr (by decide)) (frame4 fS), h.env.keep k₄ (by decide),
    ⟨(ow 0 (by omega_using [])).trans h.lay.len, (ow 48 (by omega_using [])).trans h.lay.wW,
      (ow 224 (by omega_using [])).trans h.lay.strideW, fun j hj => (ow _ (by omega_using [hj])).trans (h.lay.arrW j hj)⟩,
    ?_, hncl, g₄, (rd_keep hp fS).trans h.rd8, h.hav, sy.trans h.syms, h.tab⟩
  rw [← h.v]
  exact o₄.wordsVal (.inl (by simp only [aCm1, slot_lin]; omega_using [])) (by rw [slot_lin]; omega_using [hw64])

/-- `gcd(c − 1, e) ≠ 1`. -/
theorem gcdFin {s : State} (h : M4 s0 s) (hg : ¬ Nat.gcd (candOf s0 - 1) (eV s0) = 1) :
    WP isa (finish 3) s fun t => Fr s0 t ∧ CQ s0 (t.gpr .a0) t.mem := by
  have hop := cOp_cand h.ctx.fr.pre h.hav
  have hgb : (Nat.gcd (candOf s0 - 1) (eV s0) == 1) = false := by simp [hg]
  rw [VG.Proof.RsaKeyGen.afterDraw, h.ncl] at hop
  simp only [hgb, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hop
  exact drawnFin 3 (by decide) h.ctx h.rd8 h.hav hop (by rw [outOf, hop]) (by rw [hop]; rfl)


/-! ## The test -/

/-- The scratch region, as `Prep` states it. -/
theorem cS_eq (s0 : State) : cS s0 = ⟨stackArg s0 1, 8 * sL s0⟩ := by simp only [cS, sL, Nat.mul_comm]

/-- The round's frame: the 96 bytes below the body's stack pointer. -/
theorem below_fb (s0 : State) : VG.RISCV64.below (fb s0) 96 = rF s0 := by
  simp only [VG.RISCV64.below, rF, fb_eq, BitVec.add_sub_cancel]

/-- What holds of the call throughout the test, for the candidate `c` of `w`
words. -/
structure TC (s0 : State) (w c : Nat) : Prop where
  h35 : slot w nArr ≤ 8 * sL s0
  shape : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c
  hw : oL s0 = 8 * w
  hw4 : 4 ≤ w
  hw64 : w ≤ 64
  h8 : 8 * w ≤ rL s0
  tab : TabOk s0
  hop : cOp s0 = if Spec.RsaKeyGen.obviouslyComposite (64 * w) c then some (.rejected, (rB s0).drop (8 * w))
    else (Spec.RsaKeyGen.primalityTest c ((rB s0).drop (8 * w))).map
      fun pr => (if pr.1 then .prime c else .rejected, pr.2)

theorem TC.c8 {w c : Nat} (h : TC s0 w c) : 8161 < c := by
  have := h.shape.2.1
  have : 2 ^ 14 ≤ 2 ^ (64 * w - 2) := Nat.pow_le_pow_right (by decide) (by have := h.hw4; omega_using [this])
  omega_arith

/-- The facts once `gcd(c − 1, e) = 1`. -/
structure TIn (s0 s : State) (w c : Nat) : Prop where
  ctx : Ctx s0 s
  env : Env s (stackArg s0 1) (8 * sL s0) w
  lay : Lay s.mem (stackArg s0 1) (sL s0) w
  arr0 : A s.mem (stackArg s0 1) w 0 = c
  rd8 : s.mem.readW (fw s0 oRead) 64 = BitVec.ofNat 64 (8 * w)
  syms : s.syms = s0.syms
  tc : TC s0 w c

/-- The test's arguments in the header. -/
structure THdr (s0 : State) (w : Nat) (m : Mem) : Prop where
  rand : word m (stackArg s0 1) (8 * hRand) = s0.gpr .a7
  randLen : word m (stackArg s0 1) (8 * hRandLen) = BitVec.ofNat 64 (rL s0)
  used : word m (stackArg s0 1) (8 * hUsed) = BitVec.ofNat 64 (8 * w)
  kk : word m (stackArg s0 1) (8 * hK) = BitVec.ofNat 64 (8 * w)
  checks : word m (stackArg s0 1) (8 * hChecks) = BitVec.ofNat 64 (VG.Proof.RsaKeyGen.checksW w)

theorem THdr.keep {w : Nat} {m m' : Mem} (h : THdr s0 w m)
    (ow : ∀ d, 128 ≤ d → d + 8 ≤ 224 → word m' (stackArg s0 1) d = word m (stackArg s0 1) d) : THdr s0 w m' :=
  ⟨(ow _ (by simp only [hRand]; omega_using []) (by simp only [hRand]; omega_using [])).trans h.rand,
    (ow _ (by simp only [hRandLen]; omega_using []) (by simp only [hRandLen]; omega_using [])).trans h.randLen,
    (ow _ (by simp only [hUsed]; omega_using []) (by simp only [hUsed]; omega_using [])).trans h.used,
    (ow _ (by simp only [hK]; omega_using []) (by simp only [hK]; omega_using [])).trans h.kk,
    (ow _ (by simp only [hChecks]; omega_using []) (by simp only [hChecks]; omega_using [])).trans h.checks⟩

/-- After `testArgs`. -/
structure T1 (s0 : State) (w c : Nat) (s : State) : Prop where
  ctx : Ctx s0 s
  env : Env s (stackArg s0 1) (8 * sL s0) w
  lay : Lay s.mem (stackArg s0 1) (sL s0) w
  arr0 : A s.mem (stackArg s0 1) w 0 = c
  hdr : THdr s0 w s.mem
  trial : word s.mem (stackArg s0 1) (8 * hTrial) = BitVec.ofNat 64 (nTrial w)
  rd8 : s.mem.readW (fw s0 oRead) 64 = BitVec.ofNat 64 (8 * w)
  syms : s.syms = s0.syms
  tc : TC s0 w c

theorem argsS {s : State} {w c : Nat} (h : TIn s0 s w c) : WP isa (.block testArgs) s (T1 s0 w c) := by
  have hf := h.ctx.fr
  have hp := hf.pre
  have hZ := h.tc.h35
  have hnw := h.env.hs.nowrap
  simp only [nArr, slot_lin] at hZ
  refine WP.mono_syms (WP.rdwr (testArgs_ok hf h.env)) fun t ⟨⟨⟨ao, o₁⟩, k₁⟩, _, _, sp₁⟩ sy => ?_
  have fS := out_frame (by omega_using [hZ]) o₁
  have ow : ∀ d, d + 8 ≤ 128 ∨ 224 ≤ d → d + 8 ≤ 8 * sL s0 →
      word t.mem (stackArg s0 1) d = word s.mem (stackArg s0 1) d :=
    fun d hd hd' => o₁.word hd (by omega_using [hnw, hd'])
  refine ⟨h.ctx.step sp₁ k₁.2.1 k₁.2.2 (k₁.gpr (by decide)) (frame4 fS), h.env.keep k₁ (by decide),
    ⟨(ow 0 (by omega_using []) (by omega_using [hZ])).trans h.lay.len, (ow 48 (by omega_using []) (by omega_using [hZ])).trans h.lay.wW,
      (ow 224 (by omega_using []) (by omega_using [hZ])).trans h.lay.strideW,
      fun j hj => (ow _ (by omega_using [hj]) (by omega_using [hZ, hj])).trans (h.lay.arrW j hj)⟩, ?_,
    ⟨ao.rand.trans hf.wRand, ao.randLen.trans (hf.rl.trans (bv_ofNat_toNat _).symm), ao.used.trans h.rd8,
      ao.k.trans (hf.wOutLen.trans (by rw [← h.tc.hw]; exact (bv_ofNat_toNat _).symm)),
      ao.checks⟩, ao.trial, (rd_keep hp fS).trans h.rd8, sy.trans h.syms, h.tc⟩
  rw [← h.arr0]
  exact (show VG.Proof.Mont.Outside _ _ _ s.mem t.mem from o₁).wordsVal (.inr (by rw [slot_lin]; omega_using []))
    (by rw [slot_lin]; omega_using [hnw, hZ])

/-- Trial division's start. -/
theorem T1.divIn {s : State} {w c : Nat} (h : T1 s0 w c s) : DivIn s (stackArg s0 1) (8 * sL s0) w (nTrial w) :=
  ⟨h.env, h.trial, by unfold nTrial; split <;> decide, by unfold nTrial; split <;> decide,
    by rw [h.syms]; exact h.tc.tab.fit, by rw [h.syms]; exact h.tc.tab.al,
    by rw [h.syms, h.ctx.fr.rd]; exact h.tc.tab.rd, fun i hi => by rw [h.syms]; exact h.tc.tab.held_at h.ctx.fr hi⟩

/-- After trial division. -/
structure T2 (s0 : State) (w c : Nat) (s : State) : Prop where
  ctx : Ctx s0 s
  env : Env s (stackArg s0 1) (8 * sL s0) w
  lay : Lay s.mem (stackArg s0 1) (sL s0) w
  arr0 : A s.mem (stackArg s0 1) w 0 = c
  hdr : THdr s0 w s.mem
  f : s.gpr .a4 = BitVec.ofNat 64 (if Spec.RsaKeyGen.obviouslyComposite (64 * w) c then 1 else 0)
  rd8 : s.mem.readW (fw s0 oRead) 64 = BitVec.ofNat 64 (8 * w)
  syms : s.syms = s0.syms
  tc : TC s0 w c

theorem trialS {trial : Prog isa} (D : DivOk trial) {s : State} {w c : Nat} (h : T1 s0 w c s) :
    WP isa trial s (T2 s0 w c) := by
  refine WP.mono (D.ok h.divIn) fun t ⟨f₂, m₂, g₂, rd₂, wr₂, sp₂, sy₂⟩ => ?_
  rw [h.arr0, show nTrial w = if w ≤ 16 then 512 else 1024 from rfl,
    VG.Proof.RsaKeyGen.trialPrefix_spec h.tc.c8] at f₂
  have k : Keep tdRegs s t := ⟨g₂, rd₂, wr₂⟩
  refine ⟨h.ctx.keep k m₂ sp₂, h.env.keep k (by decide), by rw [m₂]; exact h.lay, by rw [m₂]; exact h.arr0,
    by rw [m₂]; exact h.hdr, f₂, by rw [m₂]; exact h.rd8, sy₂.trans h.syms, h.tc⟩

/-- A divisor: rejected. -/
theorem compFin {s : State} {w c : Nat} (h : T2 s0 w c s)
    (hoc : Spec.RsaKeyGen.obviouslyComposite (64 * w) c = true) :
    WP isa (finish 3) s fun t => Fr s0 t ∧ CQ s0 (t.gpr .a0) t.mem := by
  have hop := h.tc.hop
  rw [hoc] at hop
  simp only [↓reduceIte] at hop
  have hw := h.tc.hw
  have h8 := h.tc.h8
  refine fin_ok 3 (by decide) h.ctx (by rw [hop]; rfl) (by rw [outOf, hop]) ?_
  rw [h.rd8, usedOf, hop]
  simp only [hlen_drop]
  congr 1; omega_using [h8]

/-- The working space prepared. -/
structure T3 (s0 : State) (w c : Nat) (s : State) : Prop where
  ctx : Ctx s0 s
  kc : KCtx s (stackArg s0 1) (sL s0) w c (s0.gpr .a7) (rL s0) (VG.Proof.RsaKeyGen.checksW w)
  hu0 : word s.mem (stackArg s0 1) (8 * hUsed) = BitVec.ofNat 64 (8 * w)
  tc : TC s0 w c
  noc : Spec.RsaKeyGen.obviouslyComposite (64 * w) c = false

theorem prepS {s : State} {w c : Nat} (h : T2 s0 w c s)
    (hoc : Spec.RsaKeyGen.obviouslyComposite (64 * w) c = false) :
    WP isa VG.Impl.MillerRabin.RISCV64.Search.montPrepHi s (T3 s0 w c) := by
  have hf := h.ctx.fr
  have hp := hf.pre
  have hZ := h.tc.h35
  have hnw := h.env.hs.nowrap
  have hw4 := h.tc.hw4
  have hw64 := h.tc.hw64
  simp only [nArr, slot_lin] at hZ
  have hfS := hp.fS
  refine WP.mono (WP.rdwr (prep_ok h.env h.lay h.arr0 h.tc.shape.1 (by have := h.tc.c8; omega_using [this]) (by
    have := h.tc.shape.2.1
    have : 2 ^ (64 * (w - 1)) < 2 ^ (64 * w - 2) := Nat.pow_lt_pow_right (by decide) (by omega_using [hw4])
    omega_arith))) fun t ⟨⟨⟨p₃, o₃⟩, k₃⟩, rd₃, wr₃, sp₃⟩ => ?_
  have hr : ∀ x ∈ VG.Proof.MillerRabin.RISCV64.Search.mpRanges w, x.1 + x.2 ≤ 8 * sL s0 := fun x hx => by
    simp only [VG.Proof.MillerRabin.RISCV64.Search.mpRanges, VG.Impl.MillerRabin.RISCV64.aE, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp only [slot_lin] <;> omega_using [hZ]
  have fS : Frame [cS s0] s.mem t.mem := fun x hx => o₃ x fun r hr' => .inr (by
    have := hx _ List.mem_cons_self
    have := hr r hr'
    simp only [Region.Contains, cS, sL, ofs] at *
    omega_arith)
  have c₃ := h.ctx.step sp₃ k₃.2.1 k₃.2.2 (k₃.gpr (by decide)) (frame4 fS)
  have ow₃ : ∀ d, 64 ≤ d → d + 8 ≤ 256 → word t.mem (stackArg s0 1) d = word s.mem (stackArg s0 1) d :=
    fun d h1 h3 => (show VG.Proof.Bignum.Frm _ (VG.Proof.MillerRabin.RISCV64.Search.mpRanges w) s.mem t.mem
      from o₃).word_eq (fun x hx => by
      simp only [VG.Proof.MillerRabin.RISCV64.Search.mpRanges, VG.Impl.MillerRabin.RISCV64.aE, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp only [slot_lin] <;> omega_arith) (by omega_using [h3])
  have hd := h.hdr.keep (m' := t.mem) fun d h1 h2 => ow₃ d (by omega_using [h1]) (by omega_using [h2])
  have hrl : rL s0 < 2 ^ 64 := (stackArg s0 0).isLt
  have hfr := hp.fr
  have sp₃' : t.sp = fb s0 := sp₃.trans hf.sp
  have hbF : VG.RISCV64.below t.sp 96 = rF s0 := by rw [sp₃']; exact below_fb s0
  have spN : (fb s0).toNat = s0.sp.toNat - 192 := fb_toNat hp
  have hsp16 := hp.sp16
  have hspLo := hp.spLo
  refine ⟨c₃, ⟨p₃, hd.rand, hd.randLen, hd.kk, hd.checks,
    (VG.Proof.RsaKeyGen.cand_bits (by omega_using [hw4]) h.tc.shape).2.1,
    by have := VG.Proof.RsaKeyGen.checksW_le w; omega_using [this], hrl,
    fun i hi => ⟨cR s0, List.mem_append_left _ (by rw [rd₃, hf.rd]; exact hp.rR),
      Offset.contains_base _ (by simp only [rL] at hi; omega_using [hi]) (by omega_using [hrl, hi])⟩,
    fun i hi x hx e => ?_, by rw [sp₃', spN]; omega_using [hsp16], by rw [sp₃', spN]; omega_using [hspLo],
    by rw [hbF, ← cS_eq]; exact hp.FS.sub_left (rF_sub s0), fun i hi hc => ?_⟩, hd.used, h.tc, hoc⟩
  · refine hp.rS _ (Offset.contains_base _ (d := i) (by simp only [rL] at hi; omega_using [hi]) (by omega_using [hrl, hi])) ?_
    show Region.Contains _ (s0.gpr .a7 + BitVec.ofNat 64 i) 1
    rw [e]
    show (x - stackArg s0 1).toNat + 1 ≤ (stackArg s0 2).toNat * 8
    have : (x - stackArg s0 1).toNat < 8 * (stackArg s0 2).toNat := hx
    omega_using [this]
  · rw [hbF] at hc
    exact hp.Fr _ ((rF_sub s0) _ hc) (Offset.contains_base _ (d := i) (by simp only [rL] at hi; omega_using [hi]) (by omega_using [hrl, hi]))

/-- After the witnesses. -/
structure T4 (s0 : State) (w c : Nat) (s : State) : Prop where
  ctx : Ctx s0 s
  prep : Prep s (stackArg s0 1) (sL s0) w c
  res : match Spec.RsaKeyGen.primalityTest c ((rB s0).drop (8 * w)) with
    | none => word s.mem (stackArg s0 1) (8 * hStat) = BitVec.ofNat 64 0
    | some (b, rest) => word s.mem (stackArg s0 1) (8 * hStat) = BitVec.ofNat 64 (if b then 1 else 2) ∧
        word s.mem (stackArg s0 1) (8 * hUsed) = BitVec.ofNat 64 (rL s0 - rest.length)
  tc : TC s0 w c
  noc : Spec.RsaKeyGen.obviouslyComposite (64 * w) c = false

theorem mrStage {s : State} {w c : Nat} (R : RoundImpl) (h : T3 s0 w c s) :
    WP isa (VG.Impl.RsaKeyGen.RISCV64.Witness.millerRabin R.name R.code) s (T4 s0 w c) := by
  have hf := h.ctx.fr
  have hp := hf.pre
  have hrl : rL s0 < 2 ^ 64 := (stackArg s0 0).isLt
  have htape : Spec.Rsa.bytesAt s.mem (s0.gpr .a7) (rL s0) = rB s0 := bytes_keep hf.out hrl fun ρ hρ => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl | rfl | rfl
    · exact hp.oR.symm
    · exact hp.uR.symm
    · exact hp.rS
    · exact hp.Fr.symm
  have hpt := VG.Proof.RsaKeyGen.primalityTest_cand (by have := h.tc.hw4; omega_using [this]) h.tc.shape ((rB s0).drop (8 * w))
  rw [VG.Proof.RsaKeyGen.checksW_eq w (by have := h.tc.hw64; omega_using [this]) h.tc.hw4] at hpt
  refine WP.mono (millerRabin_ok R h.kc h.hu0 htape h.tc.h8 hpt) fun t ⟨lk, res⟩ => ?_
  have hbF : VG.RISCV64.below s.sp 96 = rF s0 := by rw [hf.sp]; exact below_fb s0
  have f₄ : Frame [cU s0, cS s0, rF s0, rdW s0] s.mem t.mem := by
    have := lk.frame
    rw [hbF, ← cS_eq] at this
    exact this.mono (by simp)
  exact ⟨h.ctx.step lk.sp lk.rd lk.wr lk.s11 f₄, lk.prep, res, h.tc, h.noc⟩

theorem T4.result_ok {s : State} {w c : Nat} (h : T4 s0 w c s) :
    WP isa testResult s fun t => Fr s0 t ∧ CQ s0 (t.gpr .a0) t.mem := by
  have hop := h.tc.hop
  rw [h.noc] at hop
  simp only [Bool.false_eq_true, ↓reduceIte] at hop
  exact res_ok h.ctx h.prep h.tc.hw h.res hop

/-- Once `gcd(c − 1, e) = 1`: trial division, then Miller–Rabin. -/
theorem test_ok {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) {s : State} {w c : Nat}
    (h : TIn s0 s w c) :
    WP isa (test trial R.name R.code) s fun t => Fr s0 t ∧ CQ s0 (t.gpr .a0) t.mem := by
  unfold test
  simp only [VG.Impl.RsaKeyGen.RISCV64.Candidate.seqs]
  refine WP.seq (WP.mono (argsS h) fun t₁ h₁ => ?_)
  refine WP.seq (WP.mono (trialS D h₁) fun t₂ h₂ => ?_)
  refine WP.ite _ (VG.RISCV64.Steps.eval_nonzero_ofNat _ _ (by split <;> decide) h₂.f) (fun hz => ?_)
    (fun hz => ?_)
  · exact compFin h₂ (by revert hz; cases Spec.RsaKeyGen.obviouslyComposite (64 * w) c <;> decide)
  · have hoc : Spec.RsaKeyGen.obviouslyComposite (64 * w) c = false := by
      revert hz; cases Spec.RsaKeyGen.obviouslyComposite (64 * w) c <;> decide
    refine WP.seq (WP.mono (prepS h₂ hoc) fun t₃ h₃ => ?_)
    exact WP.seq (WP.mono (mrStage R h₃) fun t₄ h₄ => h₄.result_ok)

/-! ## The body -/

theorem toTIn {s : State} (h : M4 s0 s) (hg : Nat.gcd (candOf s0 - 1) (eV s0) = 1) :
    TIn s0 s (cw s0) (candOf s0) := by
  have hp := h.ctx.fr.pre
  obtain ⟨hw, hw4, hw64⟩ := cw_facts hp
  have hop := cOp_cand hp h.hav
  have hgb : (Nat.gcd (candOf s0 - 1) (eV s0) == 1) = true := by simp [hg]
  rw [VG.Proof.RsaKeyGen.afterDraw, h.ncl] at hop
  simp only [hgb, Bool.and_true, Bool.false_eq_true, ↓reduceIte] at hop
  refine ⟨h.ctx, h.env, h.lay, h.v, h.rd8, h.syms,
    ⟨h35_of hp hw, VG.Proof.RsaKeyGen.candidate_shape (by omega_using [hw4]) _, hw, hw4, hw64, by have := h.hav; omega_using [hw, this], h.tab,
      ?_⟩⟩
  rw [hop]
  cases Spec.RsaKeyGen.obviouslyComposite (64 * cw s0) (candOf s0) <;> rfl

theorem main_ok {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) {s : State} (h : MIn s0 s) :
    WP isa (main trial R.name R.code) s fun t => Fr s0 t ∧ CQ s0 (t.gpr .a0) t.mem := by
  unfold main
  simp only [VG.Impl.RsaKeyGen.RISCV64.Candidate.seqs]
  refine WP.seq (WP.mono (setupS h) fun t₁ h₁ => ?_)
  refine WP.seq (WP.mono (loadCS h₁) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (closeS h₂) fun t₃ h₃ => ?_)
  refine WP.ite _ (VG.RISCV64.Steps.eval_nonzero_ofNat _ _ (by split <;> decide) h₃.f) (fun hz => ?_)
    (fun hz => ?_)
  · exact closeFin h₃ (by revert hz; cases Spec.RsaKeyGen.tooClose _ _ (candOf s0) <;> decide)
  · have hncl : Spec.RsaKeyGen.tooClose (64 * cw s0) (Spec.RsaKeyGen.otherPrime (pB s0)) (candOf s0) = false := by
      revert hz; cases Spec.RsaKeyGen.tooClose _ _ (candOf s0) <;> decide
    refine WP.seq (WP.mono (gcdS h₃ hncl) fun t₄ h₄ => ?_)
    refine WP.ite _ (VG.RISCV64.Steps.eval_nonzero _ _) (fun hz => ?_) (fun hz => ?_)
    · exact gcdFin h₄ fun e => by rw [h₄.g.mpr e] at hz; exact absurd hz (by decide)
    · exact test_ok D R (toTIn h₄ (h₄.g.mp (by simpa using hz)))

/-- The flag of `rand`'s length: whether it has the candidate's octets. -/
theorem flagI {s : State} (hf : Fr s0 s) :
    WP isa (.block ([ldf .t3 oRandLen, ldf .t4 oOutLen] ++ VG.Impl.MillerRabin.RISCV64.Search.geFlag .t2 .t3 .t4))
      s fun t => t.gpr .t2 = BitVec.ofNat 64 (if oL s0 ≤ rL s0 then 1 else 0) ∧ t.mem = s.mem := by
  rw [WP.block_append_iff]
  refine WP.block_cons_iff.mpr ⟨_, hf.load (r := .t3) (o := oRandLen) (by decide) (by decide), ?_⟩
  have h1 : Fr s0 (s.write .t3 (s.mem.readW (fw s0 oRandLen) 64)) :=
    hf.step (sp_write _ _ _) (rd_write _ _ _) (wr_write _ _ _) (by rw [gpr_write_of_ne _ _ (by decide)])
      (by rw [mem_write]; exact Frame.refl _ _)
  refine WP.block_cons_iff.mpr ⟨_, h1.load (r := .t4) (o := oOutLen) (by decide) (by decide), WP.block_nil ?_⟩
  refine WP.mono (VG.Proof.MillerRabin.RISCV64.Search.geFlag_ok (d := .t2) (x := rL s0) (y := oL s0) ?_ ?_
    (stackArg s0 0).isLt (s0.gpr .a1).isLt) fun t ⟨⟨t2, tm⟩, _⟩ => ⟨t2, by rw [tm]; simp only [mem_write]⟩
  · rw [gpr_write_of_ne _ _ (by decide), gpr_write_self, hf.rl, bv_ofNat_toNat]
  · rw [gpr_write_self, mem_write, hf.wOutLen, bv_ofNat_toNat]

/-- The body between the entry and the restore. -/
theorem mid_ok {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) (hT : TabOk s0) {s : State} (hf : Fr s0 s)
    (h6 : s.gpr .s6 = stackArg s0 1) (sy : s.syms = s0.syms) :
    WP isa (mid trial R.name R.code) s fun u => Fr s0 u ∧ CQ s0 (u.gpr .a0) u.mem := by
  have hp := hf.pre
  unfold mid
  refine WP.seq (WP.mono_syms (WP.rdwr (zeroOut_ok hf)) fun t₁ ⟨⟨c₁, _, k₁⟩, _, _, sp₁⟩ sy₁ => ?_)
  refine WP.seq (WP.mono_syms (WP.rdwr (WP.keep [.t3, .t4, .t2] (flagI c₁.fr) (by rfl) (by rfl)))
    fun t₂ ⟨⟨⟨f₂, m₂⟩, k₂⟩, _, _, sp₂⟩ sy₂ => ?_)
  have c₂ := c₁.keep k₂ m₂ sp₂
  refine WP.ite _ (VG.RISCV64.Steps.eval_zero_ofNat _ _ (by split <;> decide) f₂) (fun hz => ?_) (fun hz => ?_)
  · have hav : ¬ oL s0 ≤ rL s0 := by
      intro hc; simp only [hc, ↓reduceIte] at hz; exact absurd hz (by decide)
    exact finNone_post c₂ (cOp_none hp hav)
  · have hav : oL s0 ≤ rL s0 := by
      by_contra hc; simp only [hc, ↓reduceIte] at hz; exact absurd hz (by decide)
    exact main_ok D R ⟨c₂, (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans h6), hav,
      sy₂.trans (sy₁.trans sy), hT⟩

/-- The whole function: its results are the contract's. -/
theorem code_correct {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) (h : CIn s0) (hT : TabOk s0) :
    WP isa (VG.Impl.RsaKeyGen.RISCV64.Candidate.code trial R.name R.code) s0
      fun t => abiPreserved s0 t ∧ CQ s0 (t.gpr .a0) t.mem :=
  code_ok h (fun _ hf h6 _ sy => mid_ok D R hT hf h6 sy) fun r m m' fl ⟨hr, hb, hw⟩ => by
    obtain fs : Region.Sub ⟨s0.sp - BitVec.ofNat 64 192, 192⟩ (cF s0) :=
      Offset.sub_below s0.sp (a := 192) (b := 288) (n := 192) (m := 288) (by decide) (by decide)
    refine ⟨hr, ?_, ?_⟩
    · rw [← hb]
      exact List.map_congr_left fun i hi => lost_byte fl (R := cO s0) (h.Fo.sub_left fs).symm (List.mem_range.mp hi)
    · simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero] at hw ⊢
      rw [← hw, fl.readW (r := cU s0) (by simp only [Region.Contains]; rw [BitVec.sub_self]; decide)
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact (h.Fu.sub_left fs).symm) (by decide)]
end

end VG.Proof.RsaKeyGen.RISCV64.Cand

end

end

-- separate module: the constant-time proofs (still to come) import what two runs share without the contract's
-- proof

/-!
# A candidate on RISC-V: what two runs share

As on PPC64LE (`Proof/RsaKeyGen/PPC64LE/Cand/CTBase.lean`). Two runs from
states the contract relates agree on `pubOf`: the argument
registers, the arguments on the stack, the table's address, `e`'s octets and
what the candidate leaks (`candidateLeak`). With enough random octets for a
candidate, they then take the same branches (`schedOf_eq`): the candidate is
too close to `p` in both or neither (`close_agree`), and so on; a candidate
rejected in both was read from the same octets (`rej_take`), so the branches
that follow a rejection agree too (`gcd_agree`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Cand

open VG VG.RISCV64
open VG.Spec.RsaKeyGen (Candidate)
open VG.Proof.RsaKeyGen (schedOf leakOf seg afterDraw)

/-- `e`'s octets. -/
abbrev eB (s0 : State) : List Byte := Spec.Rsa.bytesAt s0.mem (s0.gpr .a3) (s0.gpr .a4).toNat

theorem eV_eq (s0 : State) : eV s0 = Spec.Rsa.os2ip (eB s0) := rfl

/-- What two runs share. -/
structure CD where
  regs : List (BitVec 64)
  stk : List (BitVec 64)
  sym : Addr
  e : List Byte
  lk : List Nat

/-- The public data of the call from `s0`. -/
def pubOf (s0 : State) : CD :=
  ⟨argRegs.map s0.gpr, (List.range 3).map (stackArg s0), s0.syms VG.Impl.RsaKeyGen.TrialTable32.symbol,
    eB s0, Spec.RsaKeyGen.candidateLeak (oL s0) (eB s0) (pB s0) (rB s0)⟩

/-- A call the contract allows, with the public data `a`. -/
def KRel (a : CD) (s0 : State) : Prop := CIn s0 ∧ TabOk s0 ∧ pubOf s0 = a

theorem KRel.reg {a : CD} {s₁ s₂ : State} (h₁ : KRel a s₁) (h₂ : KRel a s₂) {r : Reg} (hr : r ∈ argRegs) :
    s₁.gpr r = s₂.gpr r :=
  List.map_inj_left.mp ((congrArg CD.regs h₁.2.2).trans (congrArg CD.regs h₂.2.2).symm) r hr

theorem KRel.arg {a : CD} {s₁ s₂ : State} (h₁ : KRel a s₁) (h₂ : KRel a s₂) {i : Nat} (hi : i < 3) :
    stackArg s₁ i = stackArg s₂ i :=
  List.map_inj_left.mp ((congrArg CD.stk h₁.2.2).trans (congrArg CD.stk h₂.2.2).symm) i (List.mem_range.mpr hi)

theorem KRel.sym {a : CD} {s₁ s₂ : State} (h₁ : KRel a s₁) (h₂ : KRel a s₂) :
    s₁.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = s₂.syms VG.Impl.RsaKeyGen.TrialTable32.symbol :=
  (congrArg CD.sym h₁.2.2).trans (congrArg CD.sym h₂.2.2).symm

theorem KRel.e {a : CD} {s₁ s₂ : State} (h₁ : KRel a s₁) (h₂ : KRel a s₂) : eB s₁ = eB s₂ :=
  (congrArg CD.e h₁.2.2).trans (congrArg CD.e h₂.2.2).symm

theorem KRel.lk {a : CD} {s₁ s₂ : State} (h₁ : KRel a s₁) (h₂ : KRel a s₂) :
    Spec.RsaKeyGen.candidateLeak (oL s₁) (eB s₁) (pB s₁) (rB s₁) =
      Spec.RsaKeyGen.candidateLeak (oL s₂) (eB s₂) (pB s₂) (rB s₂) :=
  (congrArg CD.lk h₁.2.2).trans (congrArg CD.lk h₂.2.2).symm

theorem KRel.oL_eq {a : CD} {s₁ s₂ : State} (h₁ : KRel a s₁) (h₂ : KRel a s₂) : oL s₁ = oL s₂ := by
  show (s₁.gpr .a1).toNat = (s₂.gpr .a1).toNat
  rw [h₁.reg h₂ (r := .a1) (by decide)]

theorem KRel.rL_eq {a : CD} {s₁ s₂ : State} (h₁ : KRel a s₁) (h₂ : KRel a s₂) : rL s₁ = rL s₂ := by
  show (stackArg s₁ 0).toNat = (stackArg s₂ 0).toNat
  rw [h₁.arg h₂ (i := 0) (by decide)]

/-- The branches of the call from `s0`. -/
def schedS (s0 : State) : VG.Proof.RsaKeyGen.Sched :=
  schedOf (oL s0) (Spec.Rsa.os2ip (eB s0)) (Spec.RsaKeyGen.otherPrime (pB s0)) (rB s0)

theorem KRel.sched {a : CD} {s₁ s₂ : State} (h₁ : KRel a s₁) (h₂ : KRel a s₂) (hk : oL s₁ ≤ rL s₁) :
    schedS s₁ = schedS s₂ := by
  have hp := h₁.1
  have hv := hp.valid
  simp only [Spec.RsaKeyGen.primeLenValid] at hv
  have eo := h₁.oL_eq h₂
  have er := h₁.rL_eq h₂
  have hl := h₁.lk h₂
  rw [VG.Proof.RsaKeyGen.candidateLeak_eq, VG.Proof.RsaKeyGen.candidateLeak_eq, h₁.e h₂, eo] at hl
  unfold Spec.RsaKeyGen.candidateOp at hl
  unfold schedS
  rw [h₁.e h₂, eo]
  have h0 : 0 < oL s₂ := by rw [← eo]; simp only [oL]; omega_using [hv]
  exact VG.Proof.RsaKeyGen.schedOf_eq h0 (by rw [bytesAt_len, bytesAt_len, er])
    (by rw [bytesAt_len, ← eo]; exact hk) hl

/-- A rejected candidate was read from at least its own octets. -/
theorem rej_take {L e : Nat} {p : Option Nat} {r rest : Spec.RsaKeyGen.Rand} (hL : 0 < L)
    (h : Spec.RsaKeyGen.candidateStep (8 * L) e p r = some (.rejected, rest)) : L ≤ r.length - rest.length := by
  rw [VG.Proof.RsaKeyGen.candidateStep_eq _ _ _ _ hL] at h
  split at h
  · rename_i hk
    unfold afterDraw at h
    split at h
    · cases h
    · split at h
      · rename_i _ _
        rcases hp : Spec.RsaKeyGen.primalityTest (Spec.RsaKeyGen.candidate (8 * L) (Spec.Rsa.os2ip (seg r 0 L)))
            (r.drop L) with _ | ⟨b, rest'⟩
        · rw [hp] at h; cases h
        · rw [hp] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          have := VG.Proof.RsaKeyGen.primalityTest_rest hp
          rw [← h.2]
          simp only [List.length_drop] at this
          omega_using [hk, this]
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2, List.length_drop]
        omega_using [hk]
  · cases h

/-- Two candidates rejected with the same leak were read from the same
octets. -/
theorem rej_same {L e : Nat} {p₁ p₂ : Option Nat} {r₁ r₂ rest₁ rest₂ : Spec.RsaKeyGen.Rand} (hL : 0 < L)
    (h₁ : Spec.RsaKeyGen.candidateStep (8 * L) e p₁ r₁ = some (.rejected, rest₁))
    (h₂ : Spec.RsaKeyGen.candidateStep (8 * L) e p₂ r₂ = some (.rejected, rest₂))
    (h : leakOf r₁ (Spec.RsaKeyGen.candidateStep (8 * L) e p₁ r₁) =
      leakOf r₂ (Spec.RsaKeyGen.candidateStep (8 * L) e p₂ r₂)) :
    r₁.take L = r₂.take L := by
  have t₁ := rej_take hL h₁
  have t₂ := rej_take hL h₂
  rw [h₁, h₂] at h
  simp only [leakOf, List.cons.injEq, true_and] at h
  obtain ⟨hu, he⟩ := VG.Proof.RsaKeyGen.take_eq_of_map (by omega_using []) (by omega_using []) h
  have := congrArg (List.take L) he
  rw [VG.Proof.RsaKeyGen.take_take_of_le t₁, VG.Proof.RsaKeyGen.take_take_of_le (hu ▸ t₁)] at this
  exact this

/-- The candidate, as `schedOf` reads it. -/
abbrev candS (s0 : State) : Nat :=
  Spec.RsaKeyGen.candidate (8 * oL s0) (Spec.Rsa.os2ip ((rB s0).take (oL s0)))

theorem leak_step {a : CD} {s₁ s₂ : State} (h₁ : KRel a s₁) (h₂ : KRel a s₂) :
    leakOf (rB s₁) (Spec.RsaKeyGen.candidateStep (8 * oL s₁) (Spec.Rsa.os2ip (eB s₁))
        (Spec.RsaKeyGen.otherPrime (pB s₁)) (rB s₁)) =
      leakOf (rB s₂) (Spec.RsaKeyGen.candidateStep (8 * oL s₂) (Spec.Rsa.os2ip (eB s₂))
        (Spec.RsaKeyGen.otherPrime (pB s₂)) (rB s₂)) := by
  have hl := h₁.lk h₂
  rw [VG.Proof.RsaKeyGen.candidateLeak_eq, VG.Proof.RsaKeyGen.candidateLeak_eq] at hl
  exact hl

theorem close_agree {a : CD} {s₁ s₂ : State} (h₁ : KRel a s₁) (h₂ : KRel a s₂) (hk : oL s₁ ≤ rL s₁) :
    Spec.RsaKeyGen.tooClose (8 * oL s₁) (Spec.RsaKeyGen.otherPrime (pB s₁)) (candS s₁) =
      Spec.RsaKeyGen.tooClose (8 * oL s₂) (Spec.RsaKeyGen.otherPrime (pB s₂)) (candS s₂) := by
  have e := congrArg VG.Proof.RsaKeyGen.Sched.close (h₁.sched h₂ hk)
  unfold schedS at e
  rwa [VG.Proof.RsaKeyGen.sched_close, VG.Proof.RsaKeyGen.sched_close] at e

theorem comp_agree {a : CD} {s₁ s₂ : State} (h₁ : KRel a s₁) (h₂ : KRel a s₂) (hk : oL s₁ ≤ rL s₁)
    (hc : Spec.RsaKeyGen.tooClose (8 * oL s₁) (Spec.RsaKeyGen.otherPrime (pB s₁)) (candS s₁) = false) :
    Spec.RsaKeyGen.obviouslyComposite (8 * oL s₁) (candS s₁) =
      Spec.RsaKeyGen.obviouslyComposite (8 * oL s₂) (candS s₂) := by
  have hc₂ := (close_agree h₁ h₂ hk).symm.trans hc
  have e := congrArg VG.Proof.RsaKeyGen.Sched.comp (h₁.sched h₂ hk)
  unfold schedS at e
  rwa [VG.Proof.RsaKeyGen.sched_comp hc, VG.Proof.RsaKeyGen.sched_comp hc₂] at e

/-- A candidate trial division rejects is rejected. -/
theorem step_comp {L e : Nat} {p : Option Nat} {r : Spec.RsaKeyGen.Rand} (hL : 0 < L) (hk : L ≤ r.length)
    (hc : Spec.RsaKeyGen.tooClose (8 * L) p
      (Spec.RsaKeyGen.candidate (8 * L) (Spec.Rsa.os2ip (r.take L))) = false)
    (ho : Spec.RsaKeyGen.obviouslyComposite (8 * L)
      (Spec.RsaKeyGen.candidate (8 * L) (Spec.Rsa.os2ip (r.take L))) = true) :
    Spec.RsaKeyGen.candidateStep (8 * L) e p r = some (.rejected, r.drop L) := by
  rw [VG.Proof.RsaKeyGen.candidateStep_eq _ _ _ _ hL, VG.Proof.RsaKeyGen.ite_t hk]
  unfold afterDraw seg
  rw [List.drop_zero, hc, ho]
  rfl

/-- Candidates trial division rejects are the same. -/
theorem comp_same {a : CD} {s₁ s₂ : State} (h₁ : KRel a s₁) (h₂ : KRel a s₂) (hk : oL s₁ ≤ rL s₁)
    (hc : Spec.RsaKeyGen.tooClose (8 * oL s₁) (Spec.RsaKeyGen.otherPrime (pB s₁)) (candS s₁) = false)
    (ho : Spec.RsaKeyGen.obviouslyComposite (8 * oL s₁) (candS s₁) = true) : candS s₁ = candS s₂ := by
  have hp := h₁.1
  have hv := hp.valid
  simp only [Spec.RsaKeyGen.primeLenValid] at hv
  have eo := h₁.oL_eq h₂
  have er := h₁.rL_eq h₂
  have hc₂ := (close_agree h₁ h₂ hk).symm.trans hc
  have ho₂ := (comp_agree h₁ h₂ hk hc).symm.trans ho
  have h0 : 0 < oL s₁ := by simp only [oL]; omega_using [hv]
  have t := rej_same (L := oL s₁) h0
    (step_comp h0 (by rw [bytesAt_len]; exact hk) hc ho)
    (eo ▸ step_comp (eo ▸ h0) (by rw [bytesAt_len, ← eo, ← er]; exact hk) hc₂ ho₂)
    (by have := leak_step h₁ h₂; rw [← eo, ← h₁.e h₂] at this; exact this)
  unfold candS
  rw [← eo, t]

theorem gcd_agree {a : CD} {s₁ s₂ : State} (h₁ : KRel a s₁) (h₂ : KRel a s₂) (hk : oL s₁ ≤ rL s₁)
    (hc : Spec.RsaKeyGen.tooClose (8 * oL s₁) (Spec.RsaKeyGen.otherPrime (pB s₁)) (candS s₁) = false) :
    Nat.gcd (candS s₁ - 1) (Spec.Rsa.os2ip (eB s₁)) = 1 ↔ Nat.gcd (candS s₂ - 1) (Spec.Rsa.os2ip (eB s₂)) = 1 := by
  rw [h₁.e h₂]
  cases ho : Spec.RsaKeyGen.obviouslyComposite (8 * oL s₁) (candS s₁)
  · have hc₂ := (close_agree h₁ h₂ hk).symm.trans hc
    have ho₂ := (comp_agree h₁ h₂ hk hc).symm.trans ho
    have e := congrArg VG.Proof.RsaKeyGen.Sched.gbad (h₁.sched h₂ hk)
    unfold schedS at e
    rw [VG.Proof.RsaKeyGen.sched_gbad hc ho, VG.Proof.RsaKeyGen.sched_gbad hc₂ ho₂, h₁.e h₂] at e
    constructor
    · intro hg; simp [hg] at e; simpa using e
    · intro hg; simp [hg] at e; simpa using e
  · rw [comp_same h₁ h₂ hk hc ho]

theorem shape_agree {a : CD} {s₁ s₂ : State} (h₁ : KRel a s₁) (h₂ : KRel a s₂) (hk : oL s₁ ≤ rL s₁)
    (hc : Spec.RsaKeyGen.tooClose (8 * oL s₁) (Spec.RsaKeyGen.otherPrime (pB s₁)) (candS s₁) = false)
    (ho : Spec.RsaKeyGen.obviouslyComposite (8 * oL s₁) (candS s₁) = false)
    (hg : Nat.gcd (candS s₁ - 1) (Spec.Rsa.os2ip (eB s₁)) = 1) :
    VG.Proof.RsaKeyGen.shapeOf (Spec.RsaKeyGen.primalityTest (candS s₁) ((rB s₁).drop (oL s₁))) =
      VG.Proof.RsaKeyGen.shapeOf (Spec.RsaKeyGen.primalityTest (candS s₂) ((rB s₂).drop (oL s₂))) := by
  have hc₂ := (close_agree h₁ h₂ hk).symm.trans hc
  have ho₂ := (comp_agree h₁ h₂ hk hc).symm.trans ho
  have hg₂ := (gcd_agree h₁ h₂ hk hc).mp hg
  have e := congrArg VG.Proof.RsaKeyGen.Sched.mr (h₁.sched h₂ hk)
  unfold schedS at e
  rwa [VG.Proof.RsaKeyGen.sched_mr hc ho (by simp [hg]), VG.Proof.RsaKeyGen.sched_mr hc₂ ho₂ (by simp [hg₂])] at e

end VG.Proof.RsaKeyGen.RISCV64.Cand
