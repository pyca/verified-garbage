module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Frame
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Setup
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Prep
public import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Gcd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

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
  have ik : imm12 (k : Int) := by unfold imm12; omega
  have iv : imm12 (v : Int) := by unfold imm12; omega
  have lt := sltu_val (BitVec.ofNat 64 w) (BitVec.ofNat 64 k)
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at lt
  brun [checksIf, h0, h5, exec_li ik, exec_li iv, BitVec.ofInt_natCast, lt]
  by_cases hk' : k ≤ w
  · rw [ite_eq_right (show ¬ w < k by omega), ite_eq_left hk']
    exact xor_sel0 _ _
  · rw [ite_eq_left (show w < k by omega), ite_eq_right hk']
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
  repeat' split
  all_goals omega

theorem nTrial_val {w : Nat} (hw : w < 2 ^ 63) :
    (BitVec.ofNat 64 (if 16 < w then 1 else 0) <<< 9) + BitVec.ofNat 64 512 = BitVec.ofNat 64 (nTrial w) := by
  unfold nTrial
  by_cases h : 16 < w
  · rw [ite_eq_left h, ite_eq_right (by omega)]; decide
  · rw [ite_eq_right h, ite_eq_left (by omega)]; decide

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
  have al : ∀ o, o % 8 = 0 → (fb s0 + BitVec.ofNat 64 o).toNat % 8 = 0 := fun o h8 => fw_al hp h8
  have inr : ∀ o, o + 8 ≤ 192 → InRegions (s.rd ++ s.wr) (fb s0 + BitVec.ofNat 64 o) 8 := fun o ho =>
    ⟨kF s0, List.mem_append_right _ (by rw [hf.wr]; exact List.mem_cons_self), kF_contains ho⟩
  -- A store to the header keeps the frame's words.
  have stF : ∀ (m : Mem) (d : Nat) (v : BitVec 64), d + 8 ≤ 256 →
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
  have r1 : (s.mem.writeW (off B 136) vR).readW (fb s0 + 168#64) 64 = vL := by
    rw [← hL]; exact stF _ 136 _ (by decide) 168 (by decide)
  have r2 : ((s.mem.writeW (off B 136) vR).writeW (off B 144) vL).readW (fb s0 + 176#64) 64 = vU := by
    rw [← hU, stF _ 144 _ (by decide) 176 (by decide)]; exact stF _ 136 _ (by decide) 176 (by decide)
  have r3 : (((s.mem.writeW (off B 136) vR).writeW (off B 144) vL).writeW (off B 152) vU).readW
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
      hs.st (d := 136) (n := 8) (by omega), hs.al8 (d := 136) (by omega) (by decide),
      hs.st (d := 144) (n := 8) (by omega), hs.al8 (d := 144) (by omega) (by decide),
      hs.st (d := 152) (n := 8) (by omega), hs.al8 (d := 152) (by omega) (by decide),
      hs.st (d := 216) (n := 8) (by omega), hs.al8 (d := 216) (by omega) (by decide),
      exec_li (show imm12 27 by decide)]) (by decide)) fun t₁ ⟨⟨m₁, a₁⟩, k₁⟩ => ?_
  have e₁ := h.keep k₁ (by decide)
  have hw63 : w < 2 ^ 63 := by omega
  rw [WP.block_append_iff]
  refine WP.mono (checksIf_ok e₁.t0 a₁ hw63 (by decide) (by decide)) fun t₂ ⟨⟨a₂, m₂⟩, k₂⟩ => ?_
  have e₂ := e₁.keep k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (checksIf_ok e₂.t0 a₂ hw63 (by decide) (by decide)) fun t₃ ⟨⟨a₃, m₃⟩, k₃⟩ => ?_
  have e₃ := e₂.keep k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (checksIf_ok e₃.t0 a₃ hw63 (by decide) (by decide)) fun t₄ ⟨⟨a₄, m₄⟩, k₄⟩ => ?_
  have e₄ := e₃.keep k₄ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (checksIf_ok e₄.t0 a₄ hw63 (by decide) (by decide)) fun t₅ ⟨⟨a₅, m₅⟩, k₅⟩ => ?_
  have e₅ := e₄.keep k₅ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (checksIf_ok e₅.t0 a₅ hw63 (by decide) (by decide)) fun t₆ ⟨⟨a₆, m₆⟩, k₆⟩ => ?_
  have e₆ := e₅.keep k₆ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (checksIf_ok e₆.t0 a₆ hw63 (by decide) (by decide)) fun t₇ ⟨⟨a₇, m₇⟩, k₇⟩ => ?_
  have e₇ := e₆.keep k₇ (by decide)
  have hs₇ := e₇.hs
  rw [checks_eq] at a₇
  have lt := sltu_val (BitVec.ofNat 64 16) (BitVec.ofNat 64 w)
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at lt
  have m₇' : t₇.mem = (((s.mem.writeW (off B 136) vR).writeW (off B 144) vL).writeW (off B 152) vU).writeW
      (off B 216) vK := by rw [m₇, m₆, m₅, m₄, m₃, m₂, m₁]
  refine WP.mono (WP.keep [.t2] (Q := fun t => t.mem = (t₇.mem.writeW (off B 168)
      (BitVec.ofNat 64 (VG.Proof.RsaKeyGen.checksW w))).writeW (off B 128) (BitVec.ofNat 64 (nTrial w))) (by
    simp only [sth, hChecks, hTrial]
    brun [e₇.s6, e₇.t0, a₇, lt, nTrial_val hw63, exec_li (show imm12 16 by decide),
      hs₇.st (d := 168) (n := 8) (by omega), hs₇.al8 (d := 168) (by omega) (by decide),
      hs₇.st (d := 128) (n := 8) (by omega), hs₇.al8 (d := 128) (by omega) (by decide)]) (by decide))
    fun t ⟨tm, kt⟩ => ?_
  have K := ((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans kt
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, K.mono (by decide)⟩
  all_goals rw [tm, m₇']
  all_goals try simp only [hRand, hRandLen, hUsed, hK, hChecks, hTrial]
  · rw [(writeW_outside _ B _ (d := 128) (by omega)).word (d := 136) (by omega) (by omega),
      (writeW_outside _ B _ (d := 168) (by omega)).word (d := 136) (by omega) (by omega),
      (writeW_outside _ B _ (d := 216) (by omega)).word (d := 136) (by omega) (by omega),
      (writeW_outside _ B _ (d := 152) (by omega)).word (d := 136) (by omega) (by omega),
      (writeW_outside _ B _ (d := 144) (by omega)).word (d := 136) (by omega) (by omega), word_writeW_self, hR]
  · rw [(writeW_outside _ B _ (d := 128) (by omega)).word (d := 144) (by omega) (by omega),
      (writeW_outside _ B _ (d := 168) (by omega)).word (d := 144) (by omega) (by omega),
      (writeW_outside _ B _ (d := 216) (by omega)).word (d := 144) (by omega) (by omega),
      (writeW_outside _ B _ (d := 152) (by omega)).word (d := 144) (by omega) (by omega), word_writeW_self, hL]
  · rw [(writeW_outside _ B _ (d := 128) (by omega)).word (d := 152) (by omega) (by omega),
      (writeW_outside _ B _ (d := 168) (by omega)).word (d := 152) (by omega) (by omega),
      (writeW_outside _ B _ (d := 216) (by omega)).word (d := 152) (by omega) (by omega), word_writeW_self, hU]
  · rw [(writeW_outside _ B _ (d := 128) (by omega)).word (d := 216) (by omega) (by omega),
      (writeW_outside _ B _ (d := 168) (by omega)).word (d := 216) (by omega) (by omega), word_writeW_self, hK']
  · rw [(writeW_outside _ B _ (d := 128) (by omega)).word (d := 168) (by omega) (by omega), word_writeW_self]
  · rw [word_writeW_self]
  · have ow : ∀ (m : Mem) (d : Nat) (v : BitVec 64), 128 ≤ d → d + 8 ≤ 224 →
        Outside B 128 96 m (m.writeW (off B d) v) := fun m d v h1 h2 =>
      (writeW_outside m B v (d := d) (by omega)).mono h1 (by omega)
    exact (((((ow _ 136 _ (by omega) (by omega)).trans (ow _ 144 _ (by omega) (by omega))).trans
      (ow _ 152 _ (by omega) (by omega))).trans (ow _ 216 _ (by omega) (by omega))).trans
      (ow _ 168 _ (by omega) (by omega))).trans (ow _ 128 _ (by omega) (by omega))

end VG.Proof.RsaKeyGen.RISCV64.Cand
