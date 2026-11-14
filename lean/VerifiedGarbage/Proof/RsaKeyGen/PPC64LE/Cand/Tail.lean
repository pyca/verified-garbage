module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Fin
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Hyp
public import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Slot
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Bits
import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Witness
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.RoundCall
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.GeFlag
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.WLoad
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Sel
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Ctx
public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Candidate
public import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.WUni
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Gcd
import VerifiedGarbage.Proof.RsaKeyGen.Bits
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaKeyGen.CandMath
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Table
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Out
public import VerifiedGarbage.Proof.RsaKeyGen.MrIter
public import VerifiedGarbage.Proof.RsaKeyGen.Generate
import VerifiedGarbage.Proof.RsaKeyGen.MrLoopAt
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.MontPrep
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Setup
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms

/-! ### `RsaKeyGen.PPC64LE.Cand.Args`, which only this module used -/

section

/-!
# A candidate on PPC64LE: the test's inputs, and trial division

`testArgs_ok`: `rand`, its length, the octets read and a witness's octets
into the header, with the uniform witnesses needed (`checksW w`) and the
table entries trial division tries (512, or 1024 above 1024 bits).
`trialDiv_ok`: trial division, by `DivOk`, with `out` and `out_len` saved
around it in the header.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Candidate (checksIf testArgs trialDiv hTrial hOut hOutLen)
open VG.Impl.MillerRabin.PPC64LE.Search (ldh sth hRand hRandLen hUsed hK hW hChecks)
open VG.Proof.MillerRabin.PPC64LE (Env)

theorem flag_mask (w k : Nat) (hw : w < 2 ^ 63) (hk : k < 2 ^ 63) :
    (BitVec.ofNat 64 w - BitVec.ofNat 64 k) >>> 63 - BitVec.ofNat 64 1 =
      BitVec.ofNat 64 0 - BitVec.ofNat 64 (if k ≤ w then 1 else 0) := by
  rw [borrow63_val hw hk]
  by_cases h : w < k
  · rw [ite_eq_left h, ite_eq_right (by omega_using [h])]; decide
  · rw [ite_eq_right h, ite_eq_left (by omega_using [h])]

/-- `checksIf k v`: `r5 := v` if `k ≤ w`. -/
theorem checksIf_ok {s : State} {w a k v : Nat} (h3 : s.gpr .r3 = BitVec.ofNat 64 w)
    (h5 : s.gpr .r5 = BitVec.ofNat 64 a) (hw : w < 2 ^ 63) (hk : k < 2 ^ 15) (hv : v < 2 ^ 15) :
    WP isa (.block (checksIf k v)) s fun t =>
      (t.gpr .r5 = BitVec.ofNat 64 (if k ≤ w then v else a) ∧ t.gpr .r3 = s.gpr .r3 ∧ t.mem = s.mem) ∧
        Keep [.r4, .r5, .r6] s t := by
  refine WP.keep _ ?_ rfl rfl
  have hk' : k ≤ 2 ^ 15 := by omega_using [hk]
  prun [checksIf, h3, h5, exec_subi (show Reg.r3 ≠ .r0 by decide) hk', exec_li hv,
    flag_mask w k hw (by omega_using [hk]), sel_mask]
  split <;> rfl

end VG.Proof.RsaKeyGen.PPC64LE.Cand

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Candidate (checksIf testArgs trialDiv hTrial hOut hOutLen)
open VG.Impl.MillerRabin.PPC64LE.Search (ldh sth hRand hRandLen hUsed hK hW hChecks)
open VG.Proof.MillerRabin.PPC64LE (Env)

/-- The table entries trial division tries. -/
abbrev nTrial (w : Nat) : Nat := if w ≤ 16 then 512 else 1024

/-- What `testArgs` writes in the header. -/
structure ArgsOut (s : State) (B : Addr) (w : Nat) (m : Mem) : Prop where
  rand : word m B (8 * hRand) = s.gpr .r26
  randLen : word m B (8 * hRandLen) = s.gpr .r27
  used : word m B (8 * hUsed) = s.gpr .r28
  k : word m B (8 * hK) = s.gpr .r24
  checks : word m B (8 * hChecks) = BitVec.ofNat 64 (VG.Proof.RsaKeyGen.checksW w)
  trial : word m B (8 * hTrial) = BitVec.ofNat 64 (nTrial w)

theorem rdw (m : Mem) (B : Addr) {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    word (m.writeW (off B e) v) B d = word m B d :=
  Mem.readW_writeW_sep (Offset.sep B h hd he) (by decide)

theorem testArgs_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) (h48 : word s.mem B 48 = BitVec.ofNat 64 w)
    (hw64 : w ≤ 64) :
    WP isa (.block testArgs) s fun t =>
      (ArgsOut s B w t.mem ∧ Outside B 128 96 s.mem t.mem ∧ t.gpr .r3 = BitVec.ofNat 64 w) ∧
        Keep [.r3, .r4, .r5, .r6] s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hZ := h.hZ
  have hZ' : 256 ≤ Z := by rw [slot_lin] at hZ; omega_using [hZ]
  unfold testArgs
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r3, .r5] (Q := fun t => t.mem = (((s.mem.writeW (off B 136) (s.gpr .r26)).writeW
      (off B 144) (s.gpr .r27)).writeW (off B 152) (s.gpr .r28)).writeW (off B 216) (s.gpr .r24) ∧
      t.gpr .r3 = BitVec.ofNat 64 w ∧ t.gpr .r5 = BitVec.ofNat 64 27) ?_ (by decide)) fun t₁ ⟨⟨m₁, a3, a5⟩, k₁⟩ => ?_
  · simp only [sth, ldh, hRand, hRandLen, hUsed, hK, hW]
    prun [h.h31, h48, hs.st (d := 136) (n := 8) (by omega_using [hZ']), hs.st (d := 144) (n := 8) (by omega_using [hZ']),
      hs.st (d := 152) (n := 8) (by omega_using [hZ']), hs.st (d := 216) (n := 8) (by omega_using [hZ']), hs.ld (d := 48) (n := 8) (by omega_using [hZ']),
      rdw _ B _ (show 48 + 8 ≤ 216 ∨ 216 + 8 ≤ 48 by decide) (by decide) (by decide),
      rdw _ B _ (show 48 + 8 ≤ 152 ∨ 152 + 8 ≤ 48 by decide) (by decide) (by decide),
      rdw _ B _ (show 48 + 8 ≤ 144 ∨ 144 + 8 ≤ 48 by decide) (by decide) (by decide),
      rdw _ B _ (show 48 + 8 ≤ 136 ∨ 136 + 8 ≤ 48 by decide) (by decide) (by decide)]
    done
  have hw' : w < 2 ^ 63 := by omega_using [hw64]
  refine WP.mono (checksIf_ok a3 a5 hw' (by decide) (by decide)) fun t₂ ⟨⟨b5, b3, m₂⟩, k₂⟩ => ?_
  refine WP.mono (checksIf_ok (b3.trans a3) b5 hw' (by decide) (by decide)) fun t₃ ⟨⟨c5, c3, m₃⟩, k₃⟩ => ?_
  refine WP.mono (checksIf_ok ((c3.trans b3).trans a3) c5 hw' (by decide) (by decide)) fun t₄ ⟨⟨d5, d3, m₄⟩, k₄⟩ => ?_
  refine WP.mono (checksIf_ok (((d3.trans c3).trans b3).trans a3) d5 hw' (by decide) (by decide))
    fun t₅ ⟨⟨e5, e3, m₅⟩, k₅⟩ => ?_
  refine WP.mono (checksIf_ok ((((e3.trans d3).trans c3).trans b3).trans a3) e5 hw' (by decide) (by decide))
    fun t₆ ⟨⟨f5, f3, m₆⟩, k₆⟩ => ?_
  refine WP.mono (checksIf_ok (((((f3.trans e3).trans d3).trans c3).trans b3).trans a3) f5 hw' (by decide)
    (by decide)) fun t₇ ⟨⟨g5, g3, m₇⟩, k₇⟩ => ?_
  have h3₇ : t₇.gpr .r3 = BitVec.ofNat 64 w := (((((g3.trans f3).trans e3).trans d3).trans c3).trans b3).trans a3
  have hm₇ : t₇.mem = t₁.mem := by rw [m₇, m₆, m₅, m₄, m₃, m₂]
  have hs₇ := hs.congr ((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).wr
  have h31 : t₇.gpr .r31 = B := by
    rw [(((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇)).gpr _ (by decide)]; exact h.h31
  have hck : (if 59 ≤ w then 3 else if 22 ≤ w then 4 else if 8 ≤ w then 5 else if 7 ≤ w then 6 else
      if 6 ≤ w then 7 else if 5 ≤ w then 8 else 27) = VG.Proof.RsaKeyGen.checksW w :=
    (show ∀ w ≤ 64, (if 59 ≤ w then 3 else if 22 ≤ w then 4 else if 8 ≤ w then 5 else if 7 ≤ w then 6 else
      if 6 ≤ w then 7 else if 5 ≤ w then 8 else 27) = VG.Proof.RsaKeyGen.checksW w by decide) w hw64
  have htr : (BitVec.ofNat 64 16 - BitVec.ofNat 64 w) >>> 63 * BitVec.ofNat 64 512 + BitVec.ofNat 64 512 =
      BitVec.ofNat 64 (nTrial w) := by
    rw [borrow63_val (by decide) hw']
    unfold nTrial
    by_cases e : 16 < w
    · rw [ite_eq_left e, ite_eq_right (by omega_using [e])]; decide
    · rw [ite_eq_right e, ite_eq_left (by omega_using [e])]; decide
  refine WP.mono (WP.keep [.r4, .r5] (Q := fun t => t.mem = (t₇.mem.writeW (off B 168)
      (BitVec.ofNat 64 (VG.Proof.RsaKeyGen.checksW w))).writeW (off B 128) (BitVec.ofNat 64 (nTrial w)) ∧
      t.gpr .r3 = t₇.gpr .r3) ?_ (by decide)) fun t ⟨⟨tm, t3⟩, kt⟩ => ?_
  · simp only [sth, hChecks, hTrial]
    prun [h31, g5, h3₇, hs₇.st (d := 168) (n := 8) (by omega_using [hZ']), hs₇.st (d := 128) (n := 8) (by omega_using [hZ']), htr]
    rw [hck]
  · have K := ((((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans kt))
    have hz : 224 ≤ Z := by omega_using [hZ']
    rw [hm₇, m₁] at tm
    refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, by rw [t3, h3₇]⟩, K.mono (by simp)⟩
    · simp only [hRand]; rw [tm, rdw _ _ _ (by omega_using []) (by omega_using []) (by omega_using []), rdw _ _ _ (by omega_using []) (by omega_using []) (by omega_using []),
        rdw _ _ _ (by omega_using []) (by omega_using []) (by omega_using []), rdw _ _ _ (by omega_using []) (by omega_using []) (by omega_using []),
        rdw _ _ _ (by omega_using []) (by omega_using []) (by omega_using []), word_writeW_self]
    · simp only [hRandLen]; rw [tm, rdw _ _ _ (by omega_using []) (by omega_using []) (by omega_using []), rdw _ _ _ (by omega_using []) (by omega_using []) (by omega_using []),
        rdw _ _ _ (by omega_using []) (by omega_using []) (by omega_using []), rdw _ _ _ (by omega_using []) (by omega_using []) (by omega_using []), word_writeW_self]
    · simp only [hUsed]; rw [tm, rdw _ _ _ (by omega_using []) (by omega_using []) (by omega_using []), rdw _ _ _ (by omega_using []) (by omega_using []) (by omega_using []),
        rdw _ _ _ (by omega_using []) (by omega_using []) (by omega_using []), word_writeW_self]
    · simp only [hK]; rw [tm, rdw _ _ _ (by omega_using []) (by omega_using []) (by omega_using []), rdw _ _ _ (by omega_using []) (by omega_using []) (by omega_using []),
        word_writeW_self]
    · simp only [hChecks]; rw [tm, rdw _ _ _ (by omega_using []) (by omega_using []) (by omega_using []), word_writeW_self]
    · simp only [hTrial]; rw [tm, word_writeW_self]
    · rw [tm]
      have o : ∀ (m : Mem) (d : Nat) (v : BitVec 64), 128 ≤ d → d + 8 ≤ 224 → Outside B 128 96 m (m.writeW (off B d) v) :=
        fun m d v h1 h2 => (writeW_outside m B (d := d) v (by omega_using [h2])).mono h1 (by omega_using [h2])
      exact ((((((o _ 136 _ (by omega_using []) (by omega_using [])).trans (o _ 144 _ (by omega_using []) (by omega_using []))).trans
        (o _ 152 _ (by omega_using []) (by omega_using []))).trans (o _ 216 _ (by omega_using []) (by omega_using []))).trans
        (o _ 168 _ (by omega_using []) (by omega_using []))).trans (o _ 128 _ (by omega_using []) (by omega_using [])))

end VG.Proof.RsaKeyGen.PPC64LE.Cand

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Candidate (trialDiv hTrial hOut hOutLen)
open VG.Impl.MillerRabin.PPC64LE.Search (ldh sth)
open VG.Impl.RsaKeyGen (TrialTable32.symbol)
open VG.Proof.MillerRabin.PPC64LE (Env arr)

/-- `DivIn` through a write of a word of the header that is not the count. -/
theorem DivIn.write {s : State} {B : Addr} {Z w n : Nat} (h : DivIn s B Z w n) {d : Nat} (v : BitVec 64)
    (hd : d + 8 ≤ 256) (hd' : d + 8 ≤ 8 * hTrial ∨ 8 * hTrial + 8 ≤ d)
    (htab : Region.Disjoint ⟨s.syms TrialTable32.symbol, 8 * 1024⟩ ⟨B, Z⟩) :
    DivIn { s with mem := s.mem.writeW (off B d) v } B Z w n := by
  have hnw := h.env.hs.nowrap
  have hZ := h.env.hZ
  rw [slot_lin] at hZ
  refine ⟨⟨h.env.hs.congr rfl, h.env.h10, h.env.h29, h.env.h11, h.env.h31, h.env.hw, h.env.hw', h.env.hZ⟩, ?_, h.n1, h.n2,
    h.fit, h.tab, fun i hi => ?_⟩
  · show (s.mem.writeW (off B d) v).readW (off B (8 * hTrial)) 64 = _
    rw [Mem.readW_writeW_sep (Offset.sep B hd'.symm (by simp only [hTrial]; omega_using []) (by omega_using [hd])) (by decide)]
    exact h.cnt
  · have hf := h.fit
    have c1 : (⟨s.syms TrialTable32.symbol, 8 * 1024⟩ : Region).Contains
        (s.syms TrialTable32.symbol + BitVec.ofNat 64 (8 * i)) 8 :=
      Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])
    have c2 : (⟨B, Z⟩ : Region).Contains (off B d) 8 := Offset.contains_base _ (by omega_using [hd, hZ]) (by omega_using [hd])
    have sp : Mem.Sep (s.syms TrialTable32.symbol + BitVec.ofNat 64 (8 * i)) (64 / 8) (off B d) (64 / 8) :=
      htab.sep c1 c2
    show (s.mem.writeW (off B d) v).readW _ 64 = _
    rw [Mem.readW_writeW_sep sp (by decide)]
    exact h.held i hi

/-- `trialDiv`: trial division, with `out` and `out_len` (`r23`, `r24`) saved
in header words `hOut` and `hOutLen` around it. -/
theorem trialDiv_ok {trial : Prog isa} (D : DivOk trial) {s : State} {B : Addr} {Z w n : Nat} (h : DivIn s B Z w n)
    (htab : Region.Disjoint ⟨s.syms TrialTable32.symbol, 8 * 1024⟩ ⟨B, Z⟩) :
    WP isa (trialDiv trial) s fun t =>
      t.gpr .r22 = BitVec.ofNat 64 (if VG.Proof.RsaKeyGen.trialPrefix (arr s.mem B w 0) n then 1 else 0) ∧
        t.mem = (s.mem.writeW (off B 24) (s.gpr .r23)).writeW (off B 40) (s.gpr .r24) ∧
        (∀ r, r ∉ tdRegs → t.gpr r = s.gpr r) ∧ t.gpr .r23 = s.gpr .r23 ∧ t.gpr .r24 = s.gpr .r24 ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have e := h.env
  have hs := e.hs
  have hnw := hs.nowrap
  have hZ := e.hZ
  rw [slot_lin] at hZ
  unfold trialDiv
  have hst : WP isa (.block [sth .r23 hOut, sth .r24 hOutLen]) s fun u =>
      u = { s with mem := (s.mem.writeW (off B 24) (s.gpr .r23)).writeW (off B 40) (s.gpr .r24) } := by
    simp only [sth, hOut, hOutLen]
    prun [e.h31, hs.st (d := 24) (n := 8) (by omega_using [hZ]), hs.st (d := 40) (n := 8) (by omega_using [hZ])]
  refine WP.seq (WP.mono hst fun u hu => ?_)
  subst hu
  have h1 := h.write (s.gpr .r23) (d := 24) (by omega_using []) (by simp only [hTrial]; omega_using []) htab
  have h2 := h1.write (s.gpr .r24) (d := 40) (by omega_using []) (by simp only [hTrial]; omega_using []) htab
  have ha : arr ((s.mem.writeW (off B 24) (s.gpr .r23)).writeW (off B 40) (s.gpr .r24)) B w 0 = arr s.mem B w 0 := by
    have o := ((writeW_outside s.mem B (d := 24) (s.gpr .r23) (by omega_using [])).mono (o' := 24) (n' := 24) (by omega_using [])
      (by omega_using [])).trans ((writeW_outside (s.mem.writeW (off B 24) (s.gpr .r23)) B (d := 40) (s.gpr .r24) (by omega_using [])).mono
        (o' := 24) (n' := 24) (by omega_using []) (by omega_using []))
    exact o.val32 (by rw [slot_lin]; omega_using []) (by rw [slot_lin]; omega_using [hnw, hZ])
  refine WP.seq (WP.mono (D.ok h2) fun v ⟨v22, vm, vk, vrd, vwr, vsp⟩ => ?_)
  have hsv := hs.congr vwr
  have h31 : v.gpr .r31 = B := (vk .r31 (by decide)).trans e.h31
  have rd24 : v.mem.readW (off B 24) 64 = s.gpr .r23 := by
    rw [vm]; show ((s.mem.writeW (off B 24) (s.gpr .r23)).writeW (off B 40) (s.gpr .r24)).readW _ 64 = _
    rw [Mem.readW_writeW_sep (Offset.sep B (by omega_using []) (by omega_using []) (by omega_using [])) (by decide), Mem.readW_writeW_self64]
  have rd40 : v.mem.readW (off B 40) 64 = s.gpr .r24 := by
    rw [vm]; exact Mem.readW_writeW_self64 _ _ _
  refine WP.mono (WP.keep [.r23, .r24] (Q := fun t => t.gpr .r23 = s.gpr .r23 ∧ t.gpr .r24 = s.gpr .r24 ∧
      t.mem = v.mem ∧ t.gpr .r22 = v.gpr .r22) (by
    simp only [ldh, hOut, hOutLen]
    prun [h31, hsv.ld (d := 24) (n := 8) (by omega_using [hZ]), hsv.ld (d := 40) (n := 8) (by omega_using [hZ]), rd24, rd40]) (by decide))
    fun t ⟨⟨t23, t24, tm, t22⟩, kt⟩ => ⟨?_, by rw [tm, vm], fun r hr => ?_, t23, t24, kt.rd.trans vrd,
      kt.wr.trans vwr, kt.sp.trans vsp⟩
  · rw [t22, v22]
    show BitVec.ofNat 64 (if VG.Proof.RsaKeyGen.trialPrefix (arr ((s.mem.writeW (off B 24) (s.gpr .r23)).writeW
      (off B 40) (s.gpr .r24)) B w 0) n then 1 else 0) = _
    rw [ha]
  · have h23 : r ≠ .r23 := fun e => by subst e; exact hr (by decide)
    have h24 : r ≠ .r24 := fun e => by subst e; exact hr (by decide)
    rw [kt.gpr r (by simp [h23, h24]), vk r hr]

end VG.Proof.RsaKeyGen.PPC64LE.Cand

end

end

/-! ### `RsaKeyGen.PPC64LE.Cand.WBody`, which only this module used -/

section

/-! ### `RsaKeyGen.PPC64LE.Cand.WLoop`, which only this module used -/

section

/-! ### `RsaKeyGen.PPC64LE.Cand.WDraw`, which only this module used -/

section

/-! ### `RsaKeyGen.PPC64LE.Cand.WRound`, which only this module used -/

section

/-!
# A candidate on PPC64LE: a witness's round

`passed_ok`: after a passing round, one more witness (`hIdx`), and
`hStat := 1` once there are at least 17 (from 1) of them and `hChecks`
uniform ones, else 4. `round_ok`: the round (`roundCall_ok`) and its outcome,
`hStat := 2` for a failure.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Witness (passed hUni)
open VG.Impl.MillerRabin.PPC64LE.Search (ldh sth hIdx hChecks hStat)
open VG.Proof.MillerRabin.PPC64LE.Search (geFlag_ok Prep RcPost Kept keeps_word roundCall_ok)
open VG.Proof.MillerRabin.PPC64LE (RoundImpl arr)
open VG.Proof.Bignum (slot)

/-- The status after a passing round. -/
abbrev statOf (I U ch : Nat) : Nat := if 17 ≤ I + 1 ∧ ch ≤ U then 1 else 4

theorem stat_val (a b : Nat) (ha : a ≤ 1) (hb : b ≤ 1) :
    BitVec.ofNat 64 4 - (BitVec.ofNat 64 b &&& BitVec.ofNat 64 a) * BitVec.ofNat 64 3 =
      BitVec.ofNat 64 (if a = 1 ∧ b = 1 then 1 else 4) := by
  rcases (show a = 0 ∨ a = 1 by omega_using [ha]) with rfl | rfl <;> rcases (show b = 0 ∨ b = 1 by omega_using [hb]) with rfl | rfl <;>
    decide

/-- The registers `passed` writes. -/
def psRegs : List Reg := [.r0, .r3, .r4, .r5, .r7]

/-- `passed`: `hIdx := I + 1`, and `hStat := statOf I U ch` for `U` uniform
witnesses of `ch` needed. -/
theorem passed_ok {s : State} {B : Addr} {Z I U ch : Nat} (hs : Scr s B Z) (h31 : s.gpr .r31 = B) (hZ : 256 ≤ Z)
    (hI : word s.mem B (8 * hIdx) = BitVec.ofNat 64 I) (hU : word s.mem B (8 * hUni) = BitVec.ofNat 64 U)
    (hch : word s.mem B (8 * hChecks) = BitVec.ofNat 64 ch) (hI' : I + 1 < 2 ^ 63) (hU' : U < 2 ^ 63)
    (hch' : ch < 2 ^ 63) :
    WP isa (.block passed) s fun t =>
      (t.mem = (s.mem.writeW (off B (8 * hIdx)) (BitVec.ofNat 64 (I + 1))).writeW (off B (8 * hStat))
        (BitVec.ofNat 64 (statOf I U ch))) ∧ Keep psRegs s t := by
  have hnw := hs.nowrap
  unfold passed
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  simp only [hIdx, hUni, hChecks, hStat] at hI hU hch ⊢
  refine WP.mono (WP.keep [.r3, .r4] (Q := fun t => t.gpr .r3 = BitVec.ofNat 64 (I + 1) ∧
      t.gpr .r4 = BitVec.ofNat 64 17 ∧ t.mem = s.mem.writeW (off B 176) (BitVec.ofNat 64 (I + 1))) (by
    simp only [ldh, sth]
    prun [h31, hI, hs.ld (d := 176) (n := 8) (by omega_using [hZ]), hs.st (d := 176) (n := 8) (by omega_using [hZ]),
      BitVec.ofNat_add_ofNat]) (by decide)) fun t₁ ⟨⟨a3, a4, m₁⟩, k₁⟩ => ?_
  refine WP.mono (geFlag_ok a3 a4 (by omega_using [hI']) (by decide)) fun t₂ ⟨⟨b5, m₂⟩, k₂⟩ => ?_
  have hs₂ := hs.congr (k₁.trans k₂).wr
  have h31₂ : t₂.gpr .r31 = B := by rw [(k₁.trans k₂).gpr _ (by decide), h31]
  have rU : t₂.mem.readW (off B 16) 64 = BitVec.ofNat 64 U := by
    rw [m₂, m₁, Mem.readW_writeW_sep (Offset.sep B (by omega_using []) (by omega_using []) (by omega_using [])) (by decide)]; exact hU
  have rC : t₂.mem.readW (off B 168) 64 = BitVec.ofNat 64 ch := by
    rw [m₂, m₁, Mem.readW_writeW_sep (Offset.sep B (by omega_using []) (by omega_using []) (by omega_using [])) (by decide)]; exact hch
  refine WP.mono (WP.keep [.r3, .r4, .r7] (Q := fun t => t.gpr .r3 = BitVec.ofNat 64 U ∧
      t.gpr .r4 = BitVec.ofNat 64 ch ∧ t.gpr .r7 = t₂.gpr .r5 ∧ t.mem = t₂.mem) (by
    simp only [ldh]
    prun [h31₂, hs₂.ld (d := 16) (n := 8) (by omega_using [hZ]), hs₂.ld (d := 168) (n := 8) (by omega_using [hZ]), rU, rC]
    exact BitVec.add_zero _) (by decide)) fun t₃ ⟨⟨c3, c4, c7, m₃⟩, k₃⟩ => ?_
  refine WP.mono (geFlag_ok c3 c4 (by omega_using [hU']) hch') fun t₄ ⟨⟨d5, m₄⟩, k₄⟩ => ?_
  have K := ((k₁.trans k₂).trans k₃).trans k₄
  have hs₄ := hs.congr K.wr
  have h31₄ : t₄.gpr .r31 = B := by rw [K.gpr _ (by decide), h31]
  have d7 : t₄.gpr .r7 = BitVec.ofNat 64 (if 17 ≤ I + 1 then 1 else 0) := by
    rw [k₄.gpr _ (by decide), c7, b5]
  refine WP.mono (WP.keep [.r4, .r5] (Q := fun t => t.mem = t₄.mem.writeW (off B 160)
      (BitVec.ofNat 64 (statOf I U ch))) (by
    simp only [sth]
    prun [h31₄, d5, d7, hs₄.st (d := 160) (n := 8) (by omega_using [hZ])]
    have e : (4#64 - (BitVec.ofNat 64 (if ch ≤ U then 1 else 0) &&& BitVec.ofNat 64 (if 16 ≤ I then 1 else 0)) *
        3#64 : BitVec 64) = BitVec.ofNat 64 (statOf I U ch) := by
      rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, show (3#64 : BitVec 64) = BitVec.ofNat 64 3 from rfl,
        stat_val _ _ (by split <;> omega_using []) (by split <;> omega_using [])]
      unfold statOf
      by_cases e1 : 16 ≤ I <;> by_cases e2 : ch ≤ U <;> simp [e1, e2] <;> omega
    rw [e]) (by decide)) fun t ⟨tm, kt⟩ => ⟨?_, (K.trans kt).mono (by simp [psRegs])⟩
  rw [tm, m₄, m₃, m₂, m₁]

/-- A header word the round keeps. -/
theorem kept_hdr {w d : Nat} (hd : d + 8 ≤ 256) (hk : ∀ k ∈ [23, 26, 29, 30, 1], d + 8 ≤ 8 * k ∨ 8 * k + 8 ≤ d) :
    ∀ i, d ≤ i → i < d + 8 → Kept w i := by
  intro i h1 h2
  refine ⟨fun k hk' => by have := hk k hk'; omega_using [h1, h2, this], fun j hj => .inl ?_, .inl ?_⟩
  · have : 256 ≤ slot w j := by rw [slot_lin]; omega_using []
    omega_using [hd, h2, this]
  · have : 256 ≤ slot w 11 := by rw [slot_lin]; omega_using []
    omega_using [hd, h2, this]

/-- What a witness's round leaves. -/
structure RdPost (s : State) (B : Addr) (L w c a I U ch : Nat) (t : State) : Prop where
  prep : Prep t B L w c
  stat : word t.mem B (8 * hStat) =
    BitVec.ofNat 64 (if Proof.MillerRabin.Round.round c a then statOf I U ch else 2)
  idx : word t.mem B (8 * hIdx) = BitVec.ofNat 64 (if Proof.MillerRabin.Round.round c a then I + 1 else I)
  hdr : ∀ d, d + 8 ≤ 256 → (∀ k ∈ [23, 26, 29, 30, 1, 20, 22], d + 8 ≤ 8 * k ∨ 8 * k + 8 ≤ d) →
    word t.mem B d = word s.mem B d
  frame : Frame [⟨B, 8 * L⟩, below s.sp 176] s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  cs : ∀ r ∈ preserved, r ∉ Pub.montRegs → r ∉ psRegs → t.gpr r = s.gpr r

theorem round_ok (R : RoundImpl) {s : State} {B : Addr} {L w c a I U ch : Nat} (h : Prep s B L w c)
    (ha : arr s.mem B w 4 = a) (hac : a < c)
    (hsp : 176 ≤ s.sp.toNat) (hstk : (below s.sp 176).Disjoint ⟨B, 8 * L⟩)
    (hI : word s.mem B (8 * hIdx) = BitVec.ofNat 64 I) (hU : word s.mem B (8 * hUni) = BitVec.ofNat 64 U)
    (hch : word s.mem B (8 * hChecks) = BitVec.ofNat 64 ch) (hI' : I + 1 < 2 ^ 63) (hU' : U < 2 ^ 63)
    (hch' : ch < 2 ^ 63) :
    WP isa (VG.Impl.RsaKeyGen.PPC64LE.Witness.round R.name R.code) s (RdPost s B L w c a I U ch) := by
  have e := h.env
  have hZ := e.hZ
  rw [slot_lin] at hZ
  unfold VG.Impl.RsaKeyGen.PPC64LE.Witness.round
  refine WP.seq (WP.mono (roundCall_ok R h ha hac hsp hstk) fun u hu => ?_)
  have kw : ∀ d, d + 8 ≤ 256 → (∀ k ∈ [23, 26, 29, 30, 1], d + 8 ≤ 8 * k ∨ 8 * k + 8 ≤ d) →
      word u.mem B d = word s.mem B d := fun d hd hk => keeps_word hu.keeps (by omega_using [hZ, hd]) (kept_hdr hd hk)
  have hsu := e.hs.congr hu.wr
  have h31 : u.gpr .r31 = B := hu.prep.env.h31
  refine WP.ite _ (eval_zero_ofNat _ _ (by split <;> decide) hu.r3) (fun hz => ?_) (fun hz => ?_)
  · have hr : Proof.MillerRabin.Round.round c a = false := by
      by_contra hc; simp [hc] at hz
    refine WP.mono (WP.keep [.r3] (Q := fun t => t.mem = u.mem.writeW (off B (8 * hStat)) (BitVec.ofNat 64 2)) (by
      simp only [sth, hStat]; prun [h31, hsu.st (d := 160) (n := 8) (by omega_using [hZ])]) (by decide)) fun t ⟨tm, kt⟩ => ?_
    have wo := writeW_outside u.mem B (d := 8 * hStat) (BitVec.ofNat 64 2) (by simp only [hStat]; omega_using [])
    have hL := hu.prep.env.hZ
    rw [slot_lin] at hL
    have hnw := hsu.nowrap
    refine ⟨hu.prep.keep (hu.prep.env.keep kt (by decide)) (fun d hd => ?_) (fun j hj => ?_), ?_, ?_, ?_, ?_,
      kt.rd.trans hu.rd, kt.wr.trans hu.wr, kt.sp.trans hu.sp, fun r hr h1 h2 => ?_⟩
    · rw [tm]
      have s0 : 256 ≤ slot w 0 := by rw [slot_lin]; omega_using []
      have s0' : slot w 0 + 8 ≤ 8 * L := by rw [slot_lin]; omega_using [hZ]
      have s27 : 256 ≤ slot w 27 := by rw [slot_lin]; omega_using []
      have s27' : slot w 27 + 8 * w + 8 ≤ 8 * L := by rw [slot_lin]; omega_using [hZ]
      rcases hd with rfl | rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl | rfl
      all_goals exact wo.word (by simp only [hStat]; omega_arith) (by omega_arith)
    · rw [tm]
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        exact wo.val32 (by simp only [hStat]; rw [slot_lin]; omega_using []) (by rw [slot_lin]; omega_using [hZ, hnw])
    · rw [tm, hr]; exact word_writeW_self _ _ _ _
    · rw [tm, hr, wo.word (by simp only [hStat, hIdx]; omega_using []) (by simp only [hIdx]; omega_using []),
        kw _ (by simp only [hIdx]; omega_using []) (by simp only [hIdx]; decide), hI]; rfl
    · intro d hd hk
      rw [tm, wo.word (by have := hk 20 (by simp); simp only [hStat]; omega_using [this]) (by omega_using [hd]),
        kw d hd (fun k hk' => hk k (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk' ⊢; omega_using [hk']))]
    · rw [tm]
      exact hu.frame.writeW (r := ⟨B, 8 * L⟩) (by simp) _
        (Offset.contains_base _ (by simp only [hStat]; omega_using [hZ]) (by simp only [hStat]; omega_using []))
    · have h3 : r ≠ .r3 := fun e => by subst e; exact h2 (by decide)
      rw [kt.gpr r (by simp [h3]), hu.cs r hr h1]
  · have hr : Proof.MillerRabin.Round.round c a = true := by
      by_contra hc; simp [hc] at hz
    have hL := hu.prep.env.hZ
    rw [slot_lin] at hL
    have hnw := hsu.nowrap
    have kI : word u.mem B (8 * hIdx) = BitVec.ofNat 64 I := by
      rw [kw _ (by simp only [hIdx]; omega_using []) (by simp only [hIdx]; decide), hI]
    have kU : word u.mem B (8 * hUni) = BitVec.ofNat 64 U := by
      rw [kw _ (by simp only [hUni]; omega_using []) (by simp only [hUni]; decide), hU]
    have kC : word u.mem B (8 * hChecks) = BitVec.ofNat 64 ch := by
      rw [kw _ (by simp only [hChecks]; omega_using []) (by simp only [hChecks]; decide), hch]
    refine WP.mono (passed_ok hsu h31 (by omega_using [hZ]) kI kU kC hI' hU' hch') fun t ⟨tm, kt⟩ => ?_
    have wo1 := writeW_outside u.mem B (d := 8 * hIdx) (BitVec.ofNat 64 (I + 1)) (by simp only [hIdx]; omega_using [])
    have wo2 := writeW_outside (u.mem.writeW (off B (8 * hIdx)) (BitVec.ofNat 64 (I + 1))) B (d := 8 * hStat)
      (BitVec.ofNat 64 (statOf I U ch)) (by simp only [hStat]; omega_using [])
    refine ⟨hu.prep.keep (hu.prep.env.keep kt (by decide)) (fun d hd => ?_) (fun j hj => ?_), ?_, ?_, ?_, ?_,
      kt.rd.trans hu.rd, kt.wr.trans hu.wr, kt.sp.trans hu.sp, fun r hr h1 h2 => ?_⟩
    · rw [tm]
      have s0 : 256 ≤ slot w 0 := by rw [slot_lin]; omega_using []
      have s0' : slot w 0 + 8 ≤ 8 * L := by rw [slot_lin]; omega_using [hZ]
      have s27 : 256 ≤ slot w 27 := by rw [slot_lin]; omega_using []
      have s27' : slot w 27 + 8 * w + 8 ≤ 8 * L := by rw [slot_lin]; omega_using [hZ]
      rcases hd with rfl | rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl | rfl
      all_goals rw [wo2.word (by simp only [hStat]; omega_arith) (by omega_arith)]
      all_goals exact wo1.word (by simp only [hIdx]; omega_arith) (by omega_arith)
    · rw [tm]
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rw [wo2.val32 (by simp only [hStat]; rw [slot_lin]; omega_using []) (by rw [slot_lin]; omega_using [hZ, hnw])] <;>
        exact wo1.val32 (by simp only [hIdx]; rw [slot_lin]; omega_using []) (by rw [slot_lin]; omega_using [hZ, hnw])
    · rw [tm, hr]; exact word_writeW_self _ _ _ _
    · rw [tm, hr, wo2.word (by simp only [hStat, hIdx]; omega_using []) (by simp only [hIdx]; omega_using [])]
      exact word_writeW_self _ _ _ _
    · intro d hd hk
      have h20 := hk 20 (by simp)
      have h22 := hk 22 (by simp)
      rw [tm, wo2.word (by simp only [hStat]; omega_using [h20]) (by omega_using [hd]), wo1.word (by simp only [hIdx]; omega_using [h22]) (by omega_using [hd]),
        kw d hd (fun k hk' => hk k (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk' ⊢; omega_using [hk']))]
    · rw [tm]
      exact (hu.frame.writeW (r := ⟨B, 8 * L⟩) (by simp) _
        (Offset.contains_base _ (by simp only [hIdx]; omega_using [hZ]) (by simp only [hIdx]; omega_using []))).writeW
        (r := ⟨B, 8 * L⟩) (by simp) _
        (Offset.contains_base _ (by simp only [hStat]; omega_using [hZ]) (by simp only [hStat]; omega_using []))
    · rw [kt.gpr r h2, hu.cs r hr h1]

end VG.Proof.RsaKeyGen.PPC64LE.Cand

end

end

/-! ### `RsaKeyGen.PPC64LE.Cand.WSel`, which only this module used -/

section

/-! ### `RsaKeyGen.PPC64LE.Cand.WForced`, which only this module used -/

section

/-!
# A candidate on PPC64LE: the forced witness

`forced_ok`: the draw `x` in array 4 copied to array 3, bit 1 set and the top
bit cleared: `(x | 2) mod 2^(64 w − 1)` (`wv_forced`), as
`RsaKeyGen.witness` forces a draw out of range.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Witness (forced)
open VG.Impl.Bignum.PPC64LE.PublicChecked (base)
open VG.Proof.MillerRabin.PPC64LE (Env)

/-- Setting bit 1 of the low word and clearing the top bit of the top word of
a number of `w ≥ 2` words. -/
theorem wv_forced {m m' : Mem} {p : Addr} {d w : Nat} (hw : 2 ≤ w)
    (h0 : word m' p d = word m p d ||| BitVec.ofNat 64 2)
    (htop : word m' p (d + 8 * (w - 1)) = word m p (d + 8 * (w - 1)) &&& BitVec.ofNat 64 (2 ^ 63 - 1))
    (hmid : ∀ j, 0 < j → j < w - 1 → word m' p (d + 8 * j) = word m p (d + 8 * j)) :
    wv m' p d w = (wv m p d w ||| 2) % 2 ^ (64 * w - 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_or]
  by_cases hi : i < 64 * w
  · rw [VG.Proof.RsaKeyGen.testBit_wv m' p d w i hi, VG.Proof.RsaKeyGen.testBit_wv m p d w i hi]
    by_cases hj0 : i / 64 = 0
    · rw [hj0, Nat.mul_zero, Nat.add_zero, h0, BitVec.toNat_or, Nat.testBit_or, BitVec.toNat_ofNat,
        show i % 64 = i by omega_using [hj0], decide_eq_true (show i < 64 * w - 1 by omega_using [hw, hj0])]
      simp
    · have h2 : Nat.testBit 2 i = false := by
        rw [show (2 : Nat) = 2 ^ 1 from rfl, Nat.testBit_two_pow]; simp; omega_using [hj0]
      rw [h2, Bool.or_false]
      by_cases hjt : i / 64 = w - 1
      · rw [hjt, htop, BitVec.toNat_and, Nat.testBit_and, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show 2 ^ 63 - 1 < 2 ^ 64 by decide), Nat.testBit_two_pow_sub_one]
        by_cases h63 : i % 64 < 63
        · rw [decide_eq_true h63, decide_eq_true (show i < 64 * w - 1 by omega_using [hi, h63])]
          rw [show i % 64 = i - 64 * (w - 1) by omega_using [hjt]]
          simp only [Bool.and_true, Bool.true_and]
        · rw [decide_eq_false h63, decide_eq_false (show ¬ i < 64 * w - 1 by omega_using [hjt, h63])]
          simp
      · rw [hmid (i / 64) (by omega_using [hj0]) (by omega_using [hi, hjt]), decide_eq_true (show i < 64 * w - 1 by omega_using [hi, hjt])]
        simp
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (wv_lt m' p d w) (Nat.pow_le_pow_right (by decide) (by omega_using [hi]))),
      decide_eq_false (show ¬ i < 64 * w - 1 by omega_using [hi])]
    simp

theorem mask63 : (BitVec.ofNat 64 0 - BitVec.ofNat 64 1) >>> 1 = BitVec.ofNat 64 (2 ^ 63 - 1) := by decide

/-- The registers `forced` writes. -/
def fdRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r14, .r15, .r17]

/-- `forced`: array 3 := `(x | 2) mod 2^(64 w − 1)` for the draw `x` in array
4, its word `w` zero. -/
theorem forced_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) :
    WP isa forced s fun t =>
      (wv t.mem B (slot w 3) w = (wv s.mem B (slot w 4) w ||| 2) % 2 ^ (64 * w - 1) ∧
        word t.mem B (slot w 3 + 8 * w) = 0 ∧ VG.Proof.Mont.Outside B (slot w 3) (8 * w + 8) s.mem t.mem ∧
        Env t B Z w) ∧ Keep fdRegs s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hw4 := h.hw
  have hw128 := h.hw'
  have hZ := h.hZ
  rw [slot_lin] at hZ
  unfold forced
  refine WP.seq (WP.mono (toThree_ok h) fun t₁ ⟨⟨c3, z3, o₁, e₁⟩, k₁⟩ => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (e₁.base (rd := .r5) (by decide) (by decide) 3) fun t₂ ⟨⟨a5, m₂⟩, k₂⟩ => ?_
  have e₂ := e₁.keep k₂ (by decide)
  have e8 : off B (slot w 3) + BitVec.ofNat 64 (2 * w) <<< 2 - BitVec.ofNat 64 8 = off B (slot w 3 + 8 * (w - 1)) := by
    rw [show BitVec.ofNat 64 (2 * w) <<< 2 = BitVec.ofNat 64 (8 * w) by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega_using [], off_add, Offset.add_ofNat_sub _ (show 8 ≤ slot w 3 + 8 * w by omega_using [hw4]),
      show slot w 3 + 8 * w - 8 = slot w 3 + 8 * (w - 1) by omega_using [hw4]]
  have sep : ∀ (m : Mem) (x : BitVec 64), (m.writeW (off B (slot w 3)) x).readW (off B (slot w 3 + 8 * (w - 1))) 64 =
      m.readW (off B (slot w 3 + 8 * (w - 1))) 64 := fun m x =>
    Mem.readW_writeW_sep (Offset.sep B (by omega_using [hw4]) (by rw [slot_lin]; omega_using [hw128]) (by rw [slot_lin]; omega_using [hw128])) (by decide)
  refine WP.mono (WP.keep [.r3, .r4, .r5, .r6] (Q := fun t => t.mem =
      (t₂.mem.writeW (off B (slot w 3)) (word t₂.mem B (slot w 3) ||| BitVec.ofNat 64 2)).writeW
        (off B (slot w 3 + 8 * (w - 1))) (word t₂.mem B (slot w 3 + 8 * (w - 1)) &&& BitVec.ofNat 64 (2 ^ 63 - 1)))
    (by
      prun [a5, e₂.h11, e8, mask63, sep, e₂.hs.ld (d := slot w 3) (n := 8) (by rw [slot_lin]; omega_using [hZ]),
        e₂.hs.st (d := slot w 3) (n := 8) (by rw [slot_lin]; omega_using [hZ]),
        e₂.hs.ld (d := slot w 3 + 8 * (w - 1)) (n := 8) (by rw [slot_lin]; omega_using [hZ]),
        e₂.hs.st (d := slot w 3 + 8 * (w - 1)) (n := 8) (by rw [slot_lin]; omega_using [hZ])]
      done)
    (by decide)) fun t ⟨tm, kt⟩ => ?_
  have K := (k₁.trans k₂).trans kt
  have rd : ∀ d e : Nat, d + 8 ≤ e ∨ e + 8 ≤ d → d + 8 ≤ Z → e + 8 ≤ Z → ∀ (m : Mem) (x : BitVec 64),
      word (m.writeW (off B e) x) B d = word m B d := fun d e h1 h2 h3 m x =>
    Mem.readW_writeW_sep (Offset.sep B h1 (by omega_using [hnw, h2]) (by omega_using [hnw, h3])) (by decide)
  have hb3 : slot w 3 + 8 * w + 8 ≤ Z := by rw [slot_lin]; omega_using [hZ]
  have hx : wv t₂.mem B (slot w 3) w = wv s.mem B (slot w 4) w := by
    rw [m₂]; exact wv_shift' fun i hi => c3 i hi
  refine ⟨⟨?_, ?_, ?_, e₂.keep kt (by decide)⟩, K.mono (by simp [fdRegs])⟩
  · rw [← hx]
    refine wv_forced (by omega_using [hw4]) ?_ ?_ ?_
    · rw [tm, rd _ _ (by omega_using [hw4]) (by omega_using [hb3]) (by omega_using [hb3]), word_writeW_self]
    · rw [tm, word_writeW_self]
    · intro j h1 h2
      rw [tm, rd _ _ (by omega_using [h2]) (by omega_using [hb3, h2]) (by omega_using [hb3]), rd _ _ (by omega_using [h1]) (by omega_using [hb3, h2]) (by omega_using [hb3])]
  · rw [tm, rd _ _ (by omega_using [hw4]) (by omega_using [hb3]) (by omega_using [hb3]), rd _ _ (by omega_using [hw4]) (by omega_using [hb3]) (by omega_using [hb3]), m₂]; exact z3
  · rw [tm]
    have w1 := VG.Proof.Mont.writeW_outside t₂.mem B (d := slot w 3) (word t₂.mem B (slot w 3) ||| BitVec.ofNat 64 2)
      (by omega_using [hnw, hb3])
    have w2 := VG.Proof.Mont.writeW_outside (t₂.mem.writeW (off B (slot w 3)) (word t₂.mem B (slot w 3) |||
      BitVec.ofNat 64 2)) B (d := slot w 3 + 8 * (w - 1))
      (word t₂.mem B (slot w 3 + 8 * (w - 1)) &&& BitVec.ofNat 64 (2 ^ 63 - 1)) (by omega_using [hnw, hb3])
    rw [m₂] at w1 w2 ⊢
    exact (o₁.trans (w1.mono (by omega_using []) (by omega_using []))).trans (w2.mono (by omega_using []) (by omega_using []))

end VG.Proof.RsaKeyGen.PPC64LE.Cand

end

end


/-!
# A candidate on PPC64LE: a witness from a draw

`witness_ok`: the draw `x` in array 4 becomes `RsaKeyGen.witness (c − 1) x`'s
witness, `x` if it is uniform, else the forced one (`witness_eq`), selected
under the mask of the flag; the flag is added to the uniform witnesses so far
(`hUni`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Witness (witness hUni)
open VG.Impl.MillerRabin.PPC64LE.Search (ldh sth)
open VG.Proof.MillerRabin.PPC64LE (Env arr)
open VG.Proof.Bignum (slot wv)

/-- The registers `witness` writes. -/
def witRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r8, .r9, .r14, .r15, .r16, .r17, .r20, .r21]

/-- What `witness` changes: arrays 3, 4 and 6, and `hUni`. -/
def witRanges (w : Nat) : List (Nat × Nat) :=
  [(8 * hUni, 8), (slot w 3, 8 * (w + 2)), (slot w 4, 8 * (w + 2)), (slot w 6, 8 * (w + 2))]

theorem witness_ok {s : State} {B : Addr} {Z w c u : Nat} (h : Env s B Z w)
    (h35 : slot w VG.Impl.RsaKeyGen.PPC64LE.Candidate.nArr ≤ Z) (hc : wv s.mem B (slot w 0) w = c)
    (hc2 : c % 2 = 1) (hcb : Spec.RsaKeyGen.bitLength (c - 1) = 64 * w) (hcR : c < 2 ^ (64 * w))
    (hu : VG.Proof.Mont.word s.mem B (8 * hUni) = BitVec.ofNat 64 u) :
    WP isa witness s fun t =>
      (arr t.mem B w 4 = (Spec.RsaKeyGen.witness (c - 1) (wv s.mem B (slot w 4) w)).1 ∧
        VG.Proof.Mont.word t.mem B (8 * hUni) = BitVec.ofNat 64
          (u + if (Spec.RsaKeyGen.witness (c - 1) (wv s.mem B (slot w 4) w)).2 then 1 else 0) ∧
        Env t B Z w ∧ VG.Proof.Mont.Outs B (witRanges w) s.mem t.mem) ∧ Keep witRegs s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hw4 := h.hw
  have hw128 := h.hw'
  have hZ := h35
  simp only [VG.Impl.RsaKeyGen.PPC64LE.Candidate.nArr] at hZ
  rw [slot_lin] at hZ
  generalize hx : wv s.mem B (slot w 4) w = x
  have hxR : x < 2 ^ (64 * w) := by rw [← hx]; exact VG.Proof.Bignum.wv_lt _ _ _ _
  rw [VG.Proof.RsaKeyGen.witness_eq hc2 hcb hxR]
  generalize hP : (decide (2 ≤ x) && decide (x + (1 - x % 2) < c)) = P
  unfold witness
  refine WP.seq (WP.mono (uniform_ok h h35 hc hcR) fun t₁ ⟨⟨a21, e₁, o₁⟩, k₁⟩ => ?_)
  rw [hx] at a21
  have hx₁ : wv t₁.mem B (slot w 4) w = x := by
    rw [← hx, ← Pre.val32_eq_wv, ← Pre.val32_eq_wv]
    exact o₁.val32 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [] <;> rw [slot_lin, slot_lin] <;> omega_using []) (by rw [slot_lin]; omega_using [hw128])
  refine WP.seq (WP.mono (forced_ok e₁) fun t₂ ⟨⟨f3, z3, o₂, e₂⟩, k₂⟩ => ?_)
  rw [hx₁] at f3
  have r21₂ : t₂.gpr .r21 = BitVec.ofNat 64 (if P then 1 else 0) := by
    rw [k₂.gpr _ (by decide), a21, ← hP]
    by_cases e1 : 2 ≤ x <;> by_cases e2 : x + (1 - x % 2) < c <;> simp [e1, e2]
  refine WP.seq (WP.mono (WP.keep [.r0, .r20] (Q := fun t => t.gpr .r20 = BitVec.ofNat 64 0 -
      BitVec.ofNat 64 (if P then 1 else 0) ∧ t.mem = t₂.mem) (by prun [r21₂]) (by decide))
    fun t₃ ⟨⟨a20, m₃⟩, k₃⟩ => ?_)
  have e₃ := e₂.keep k₃ (by decide)
  refine WP.seq (WP.mono (VG.Proof.MillerRabin.PPC64LE.sel_ok e₃ (b := P) (o := 6) (a := 4) (t := 3) (by decide)
    (by decide) (by decide) (by decide) (by decide) a20) fun t₄ ⟨⟨v₄, o₄⟩, k₄⟩ => ?_)
  have e₄ := e₃.keep k₄ (by decide)
  refine WP.seq (WP.mono (VG.Proof.MillerRabin.PPC64LE.copy_ok e₄ (o := 4) (a := 6) (by decide) (by decide)
    (by decide)) fun t₅ ⟨⟨v₅, o₅⟩, k₅⟩ => ?_)
  have e₅ := e₄.keep k₅ (by decide)
  have r21₅ : t₅.gpr .r21 = BitVec.ofNat 64 (if P then 1 else 0) := by
    rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), r21₂]
  have s3 : 256 ≤ slot w 3 := by rw [slot_lin]; omega_using []
  have s4 : 256 ≤ slot w 4 := by rw [slot_lin]; omega_using []
  have s6 : 256 ≤ slot w 6 := by rw [slot_lin]; omega_using []
  have u₅ : VG.Proof.Mont.word t₅.mem B (8 * hUni) = BitVec.ofNat 64 u := by
    simp only [hUni] at hu ⊢
    rw [o₅.word (by omega_using [s4]) (by omega_using []), o₄.word (by omega_using [s6]) (by omega_using []), m₃, o₂.word (by omega_using [s3]) (by omega_using []),
      VG.Proof.Mont.Outs.word o₁ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only [] <;> omega_arith) (by omega_using []), hu]
  have hs₅ := e₅.hs
  refine WP.mono (WP.keep [.r3] (Q := fun t => t.mem = t₅.mem.writeW (VG.Proof.Mont.off B (8 * hUni))
      (BitVec.ofNat 64 (u + if P then 1 else 0))) (by
    simp only [ldh, sth, hUni] at u₅ ⊢
    prun [e₅.h31, u₅, r21₅, hs₅.ld (d := 16) (n := 8) (by omega_using [hZ]), hs₅.st (d := 16) (n := 8) (by omega_using [hZ]),
      BitVec.ofNat_add_ofNat]) (by decide)) fun t ⟨tm, kt⟩ => ?_
  have K := ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans kt
  have hm4 : VG.Proof.Mont.val32 t₃.mem B (slot w 4) (2 * w) = x := by
    rw [m₃, Pre.val32_eq_wv, ← hx₁, ← Pre.val32_eq_wv, ← Pre.val32_eq_wv]
    exact o₂.val32 (by rw [slot_lin, slot_lin]; omega_using []) (by rw [slot_lin]; omega_using [hw128])
  have hm3 : VG.Proof.Mont.val32 t₃.mem B (slot w 3) (2 * w) = (x ||| 2) % 2 ^ (64 * w - 1) := by
    rw [m₃, Pre.val32_eq_wv, f3]
  refine ⟨⟨?_, ?_, e₅.keep kt (by decide), ?_⟩, K.mono (by simp [witRegs, uniRegs, fdRegs,
    VG.Proof.MillerRabin.PPC64LE.selRegs, VG.Proof.MillerRabin.PPC64LE.copyRegs])⟩
  · show VG.Proof.Mont.val32 t.mem B (slot w 4) (2 * w) = _
    rw [tm, (VG.Proof.Mont.writeW_outside t₅.mem B (d := 8 * hUni) _ (by simp only [hUni]; omega_using [])).val32
      (by simp only [hUni]; omega_using [s4]) (by rw [slot_lin]; omega_using [hw128])]
    show arr t₅.mem B w 4 = _
    rw [v₅]; show VG.Proof.Mont.val32 t₄.mem B (slot w 6) (2 * w) = _
    rw [v₄, hm4, hm3]
  · rw [tm]; exact VG.Proof.Mont.word_writeW_self _ _ _ _
  · intro y hy
    simp only [witRanges, hUni, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hy
    obtain ⟨y1, y3, y4, y6⟩ := hy
    rw [tm, VG.Proof.Mont.writeW_outside t₅.mem B (d := 8 * hUni) _ (by simp only [hUni]; omega_using []) y
      (by simp only [hUni]; omega_using [y1]), o₅ y y4, o₄ y y6, m₃,
      o₂ y (by omega_using [y3]), o₁ y (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only [] <;> omega_arith)]

end VG.Proof.RsaKeyGen.PPC64LE.Cand

end

end


/-!
# A candidate on PPC64LE: one draw

`draw_ok`: the next `8 w` octets of `rand` (`load_ok`), the witness from
them (`witness_ok`), and its round (`round_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Witness (draw hUni)
open VG.Impl.MillerRabin.PPC64LE.Search (hRand hUsed hK hIdx hChecks hStat)
open VG.Proof.MillerRabin.PPC64LE.Search (Prep)
open VG.Proof.MillerRabin.PPC64LE (RoundImpl arr Env)
open VG.Proof.Bignum (slot)

/-- A witness is below the candidate. -/
theorem witness_lt {c x w : Nat} (hc : c % 2 = 1) (hb : Spec.RsaKeyGen.bitLength (c - 1) = 64 * w) (hw : 1 ≤ w)
    (hx : x < 2 ^ (64 * w)) : (Spec.RsaKeyGen.witness (c - 1) x).1 < c := by
  rw [VG.Proof.RsaKeyGen.witness_eq hc hb hx]
  have h0 : c - 1 ≠ 0 := fun e => by
    rw [e] at hb; simp [Spec.RsaKeyGen.bitLength] at hb; omega_using [hw, hb]
  have hl : (c - 1).log2 = 64 * w - 1 := by
    unfold Spec.RsaKeyGen.bitLength at hb; simp only [h0, ↓reduceIte] at hb; omega_using [hb]
  have hp : 2 ^ (64 * w - 1) ≤ c - 1 := hl ▸ Nat.log2_self_le h0
  split
  · rename_i h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; omega_using [h]
  · have := Nat.mod_lt (x ||| 2) (Nat.two_pow_pos (64 * w - 1)); omega_using [hp]

/-- The header words `draw` changes, as numbers of words. -/
def drWords : List Nat := [23, 26, 29, 30, 1, 20, 22, 19, 2]

/-- What a draw leaves: the witness `x` from the octets at `R + u`. -/
structure DrPost (s : State) (B R : Addr) (L w c u I U ch : Nat) (t : State) : Prop where
  prep : Prep t B L w c
  stat : word t.mem B (8 * hStat) = BitVec.ofNat 64
    (if Proof.MillerRabin.Round.round c (Spec.RsaKeyGen.witness (c - 1)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off R u) (8 * w)))).1 then
      statOf I (U + if (Spec.RsaKeyGen.witness (c - 1)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off R u) (8 * w)))).2 then 1 else 0) ch else 2)
  idx : word t.mem B (8 * hIdx) = BitVec.ofNat 64
    (if Proof.MillerRabin.Round.round c (Spec.RsaKeyGen.witness (c - 1)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off R u) (8 * w)))).1 then I + 1 else I)
  uni : word t.mem B (8 * hUni) = BitVec.ofNat 64 (U + if (Spec.RsaKeyGen.witness (c - 1)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off R u) (8 * w)))).2 then 1 else 0)
  used : word t.mem B (8 * hUsed) = BitVec.ofNat 64 (u + 8 * w)
  hdr : ∀ d, d + 8 ≤ 256 → (∀ k ∈ drWords, d + 8 ≤ 8 * k ∨ 8 * k + 8 ≤ d) → word t.mem B d = word s.mem B d
  frame : Frame [⟨B, 8 * L⟩, below s.sp 176] s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  cs : ∀ r ∈ preserved, r ∉ Pub.montRegs → r ∉ psRegs → r ∉ ldRegs → r ∉ witRegs → t.gpr r = s.gpr r

/-- The ranges `load` and `witness` change. -/
def lwRanges (w : Nat) : List (Nat × Nat) :=
  [(8 * hUsed, 8), (8 * hUni, 8), (slot w 3, 8 * (w + 2)), (slot w 4, 8 * (w + 2)), (slot w 6, 8 * (w + 2))]

/-- What a draw starts from. -/
structure DrIn (s : State) (B Ra : Addr) (L w c u I U ch : Nat) : Prop where
  prep : Prep s B L w c
  h35 : slot w VG.Impl.RsaKeyGen.PPC64LE.Candidate.nArr ≤ 8 * L
  cb : Spec.RsaKeyGen.bitLength (c - 1) = 64 * w
  cR : c < 2 ^ (64 * w)
  rand : word s.mem B (8 * hRand) = Ra
  used : word s.mem B (8 * hUsed) = BitVec.ofNat 64 u
  kk : word s.mem B (8 * hK) = BitVec.ofNat 64 (8 * w)
  rN : ∀ i < 8 * w, InRegions (s.rd ++ s.wr) (off Ra (u + i)) 1
  rsep : ∀ i < 8 * w, ∀ x, ofs B x < 8 * L → off Ra (u + i) ≠ x
  wr : (⟨B, 8 * L⟩ : Region) ∈ s.wr
  sp : 176 ≤ s.sp.toNat
  stk : (below s.sp 176).Disjoint ⟨B, 8 * L⟩
  idx : word s.mem B (8 * hIdx) = BitVec.ofNat 64 I
  uni : word s.mem B (8 * hUni) = BitVec.ofNat 64 U
  chk : word s.mem B (8 * hChecks) = BitVec.ofNat 64 ch
  bI : I + 1 < 2 ^ 63
  bU : U + 1 < 2 ^ 63
  bch : ch < 2 ^ 63

/-- The witness drawn at `R + u`. -/
abbrev drX (m : Mem) (Ra : Addr) (w c u : Nat) : Nat × Bool :=
  Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (off Ra u) (8 * w)))

/-- What `load` leaves. -/
abbrev DrL (sD : State) (B Ra : Addr) (L w u : Nat) (s : State) : Prop :=
  (val32 s.mem B (slot w 4) (2 * w) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt sD.mem (off Ra u) (8 * w)) ∧
    word s.mem B (8 * hUsed) = BitVec.ofNat 64 (u + 8 * w) ∧ Env s B (8 * L) w ∧
    Outs B [(8 * hUsed, 8), (slot w 4, 8 * w)] sD.mem s.mem) ∧ Keep ldRegs sD s

theorem loadS {sD : State} {B Ra : Addr} {L w c u I U ch : Nat} (h : DrIn sD B Ra L w c u I U ch) :
    WP isa VG.Impl.RsaKeyGen.PPC64LE.Witness.load sD (DrL sD B Ra L w u) :=
  load_ok h.prep.env h.rand h.used h.kk h.rN h.rsep

/-- The round's start. -/
structure PreRd (sD : State) (B Ra : Addr) (L w c u I U ch : Nat) (s : State) : Prop where
  prep : Prep s B L w c
  a4 : arr s.mem B w 4 = (drX sD.mem Ra w c u).1
  ac : (drX sD.mem Ra w c u).1 < c
  wr : (⟨B, 8 * L⟩ : Region) ∈ s.wr
  sp : 176 ≤ s.sp.toNat
  stk : (below s.sp 176).Disjoint ⟨B, 8 * L⟩
  idx : word s.mem B (8 * hIdx) = BitVec.ofNat 64 I
  uni : word s.mem B (8 * hUni) = BitVec.ofNat 64 (U + if (drX sD.mem Ra w c u).2 then 1 else 0)
  chk : word s.mem B (8 * hChecks) = BitVec.ofNat 64 ch
  used : word s.mem B (8 * hUsed) = BitVec.ofNat 64 (u + 8 * w)
  hdr : ∀ d, d + 8 ≤ 256 → (∀ k ∈ drWords, d + 8 ≤ 8 * k ∨ 8 * k + 8 ≤ d) → word s.mem B d = word sD.mem B d
  outs : Outs B (lwRanges w) sD.mem s.mem
  keep : Keep (ldRegs ++ witRegs) sD s

theorem witS {sD s₁ : State} {B Ra : Addr} {L w c u I U ch : Nat} (h : DrIn sD B Ra L w c u I U ch)
    (hl : DrL sD B Ra L w u s₁) :
    WP isa VG.Impl.RsaKeyGen.PPC64LE.Witness.witness s₁ (PreRd sD B Ra L w c u I U ch) := by
  obtain ⟨⟨v₁, u₁, e₁, o₁⟩, k₁⟩ := hl
  have e := h.prep.env
  have hnw := e.hs.nowrap
  have hZ := e.hZ
  have hw4 := e.hw
  rw [slot_lin] at hZ
  have hc0 : VG.Proof.Bignum.wv s₁.mem B (slot w 0) w = c := by
    rw [← Pre.val32_eq_wv, ← h.prep.n]
    exact o₁.val32 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [hUsed, slot_lin] <;> omega_using [])
      (by rw [slot_lin]; omega_using [hnw, hZ])
  have hU₁ : word s₁.mem B (8 * hUni) = BitVec.ofNat 64 U := by
    rw [o₁.word (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [hUsed, hUni, slot_lin] <;> omega_using [])
      (by simp only [hUni]; omega_using []), h.uni]
  refine WP.mono (witness_ok e₁ h.h35 hc0 h.prep.odd h.cb h.cR hU₁) fun s₂ ⟨⟨a₂, u₂, e₂, o₂⟩, k₂⟩ => ?_
  rw [← Pre.val32_eq_wv, v₁] at a₂ u₂
  have hXc : (drX sD.mem Ra w c u).1 < c := by
    refine witness_lt h.prep.odd h.cb (by omega_using [hw4]) ?_
    rw [← v₁, Pre.val32_eq_wv]; exact VG.Proof.Bignum.wv_lt _ _ _ _
  have o₁₂ : Outs B (lwRanges w) sD.mem s₂.mem := by
    refine (o₁.cover (fun r hr => ?_)).trans (o₂.cover (fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp [lwRanges], Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨(slot w 4, 8 * (w + 2)), by simp [lwRanges], Nat.le_refl _, by simp only []; omega_using []⟩
    · refine ⟨r, ?_, Nat.le_refl _, Nat.le_refl _⟩
      simp only [witRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [lwRanges]
  have ap : ∀ d, (d + 8 ≤ 256 ∧ (d + 8 ≤ 152 ∨ 160 ≤ d) ∧ (d + 8 ≤ 16 ∨ 24 ≤ d)) ∨ slot w 0 = d ∨
      slot w 27 + 8 * w = d → word s₂.mem B d = word sD.mem B d := by
    intro d hd
    refine o₁₂.word (fun r hr => ?_) (by rcases hd with hd | rfl | rfl <;> rw [slot_lin] at * <;> omega_arith)
    simp only [lwRanges, hUsed, hUni, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rcases hd with hd | rfl | rfl <;> simp only [slot_lin] at * <;> omega_arith
  have K₁₂ := k₁.trans k₂
  have p₂ : Prep s₂ B L w c := by
    refine h.prep.keep e₂ (fun d hd => ?_) (fun j hj => ?_)
    · refine ap d ?_
      rcases hd with rfl | rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl | rfl
      iterate 5 exact .inl (by omega_arith)
      · exact .inr (.inl rfl)
      · exact .inr (.inr rfl)
    · refine o₁₂.val32 (fun r hr => ?_) (by rcases hj with rfl | rfl | rfl | rfl | rfl <;> rw [slot_lin] <;> omega_using [hnw, hZ])
      simp only [lwRanges, hUsed, hUni, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp only [slot_lin] <;> omega_using []
  refine ⟨p₂, a₂, hXc, by rw [K₁₂.wr]; exact h.wr, by rw [K₁₂.sp]; exact h.sp, by rw [K₁₂.sp]; exact h.stk,
    (ap _ (.inl (by simp only [hIdx]; omega_using []))).trans h.idx, u₂,
    (ap _ (.inl (by simp only [hChecks]; omega_using []))).trans h.chk, ?_,
    fun d hd hk => ap d (.inl ⟨hd, hk 19 (by simp [drWords]), hk 2 (by simp [drWords])⟩), o₁₂, K₁₂⟩
  rw [o₂.word (fun r hr => by
    simp only [witRanges, hUni, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only [hUsed, slot_lin] <;> omega_using []) (by simp only [hUsed]; omega_using []), u₁]

theorem roundS (R : RoundImpl) {sD s : State} {B Ra : Addr} {L w c u I U ch : Nat}
    (hD : DrIn sD B Ra L w c u I U ch) (h : PreRd sD B Ra L w c u I U ch s) :
    WP isa (VG.Impl.RsaKeyGen.PPC64LE.Witness.round R.name R.code) s (DrPost sD B Ra L w c u I U ch) := by
  have e := h.prep.env
  have hnw := e.hs.nowrap
  have hZ := e.hZ
  rw [slot_lin] at hZ
  refine WP.mono (round_ok R h.prep h.a4 h.ac h.sp h.stk h.idx h.uni h.chk hD.bI
    (by have := hD.bU; split <;> omega_using [this]) hD.bch) fun t ht => ?_
  have hd' : ∀ d, d + 8 ≤ 256 → (∀ k ∈ [23, 26, 29, 30, 1, 20, 22], d + 8 ≤ 8 * k ∨ 8 * k + 8 ≤ d) →
      word t.mem B d = word s.mem B d := ht.hdr
  refine ⟨ht.prep, ht.stat, ht.idx, ?_, ?_, fun d hd hk => ?_, ?_, ht.rd.trans h.keep.rd, ht.wr.trans h.keep.wr,
    ht.sp.trans h.keep.sp, fun r hr h1 h2 h3 h4 => ?_⟩
  · rw [hd' _ (by simp only [hUni]; omega_using []) (by simp only [hUni]; decide), h.uni]
  · rw [hd' _ (by simp only [hUsed]; omega_using []) (by simp only [hUsed]; decide), h.used]
  · rw [hd' d hd (fun k hk' => hk k (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk'
      rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [drWords])), h.hdr d hd hk]
  · have fr := ht.frame
    rw [h.keep.sp] at fr
    refine (Frame.mono (frame_of_outs h.outs (Z := 8 * L) (fun r hr => ?_)) (by simp)).trans fr
    simp only [lwRanges, hUsed, hUni, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [slot_lin] <;> omega_using [hZ]
  · rw [ht.cs r hr h1 h2, h.keep.gpr r (by simp [h3, h4])]

theorem draw_ok (R : RoundImpl) {s : State} {B Ra : Addr} {L w c u I U ch : Nat}
    (h : DrIn s B Ra L w c u I U ch) :
    WP isa (draw R.name R.code) s (DrPost s B Ra L w c u I U ch) := by
  unfold draw
  exact WP.seq (WP.mono (loadS h) fun s₁ hl => WP.seq (WP.mono (witS h hl) fun s₂ hp => roundS R h hp))

end VG.Proof.RsaKeyGen.PPC64LE.Cand

end

end


/-!
# A candidate on PPC64LE: the witnesses' loop

`millerRabin_ok`: `Witness.millerRabin` leaves `hStat` and `hUsed` as
`primalityTest c` of the tape after the candidate's octets says: 0 if it ran
out of octets, else 1 (probably prime) or 2 (composite), and the octets used.
Its invariant, after `k` witnesses passed, is `MrAt` (`MrIter.lean`) and the
header's counts (`St`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Witness (draw hUni)
open VG.Impl.MillerRabin.PPC64LE.Search (ldh sth geFlag hRand hRandLen hUsed hK hIdx hChecks hStat)
open VG.Proof.MillerRabin.PPC64LE.Search (Prep geFlag_ok)
open VG.Proof.MillerRabin.PPC64LE (RoundImpl arr)
open VG.Proof.Bignum (slot)
open VG.Proof.RsaKeyGen (MrAt mrS goS wit)

/-- The registers the loop writes. -/
def lpRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12, .r14, .r15, .r16, .r17, .r20, .r21]

theorem not_mem_of_sub {xs ys : List Reg} (h : ∀ r ∈ xs, r ∈ ys) {r : Reg} (hr : r ∉ ys) : r ∉ xs :=
  fun e => hr (h r e)

/-- The header words the loop changes, as numbers of words. -/
def lpWords : List Nat := [23, 26, 29, 30, 1, 20, 22, 19, 2]

/-- What the loop keeps of its start `s`: the header words but the ones it
counts in, the memory but the working space and the stack below, the
regions, and the registers it does not write. -/
structure LKeep (s : State) (B : Addr) (L : Nat) (t : State) : Prop where
  hdr : ∀ d, d + 8 ≤ 256 → (∀ k ∈ lpWords, d + 8 ≤ 8 * k ∨ 8 * k + 8 ≤ d) → word t.mem B d = word s.mem B d
  frame : Frame [⟨B, 8 * L⟩, below s.sp 176] s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  cs : ∀ r ∈ preserved, r ∉ Pub.montRegs → r ∉ lpRegs → t.gpr r = s.gpr r

theorem LKeep.keep {s t t' : State} {B : Addr} {L : Nat} {rs : List Reg} (h : LKeep s B L t) (K : Keep rs t t')
    (hm : t'.mem = t.mem) (hr : ∀ x ∈ rs, x ∈ lpRegs) : LKeep s B L t' :=
  ⟨fun d hd hk => by rw [hm]; exact h.hdr d hd hk, by rw [hm]; exact h.frame, K.rd.trans h.rd, K.wr.trans h.wr,
    K.sp.trans h.sp, fun x hx h1 h2 => (K.gpr x (not_mem_of_sub hr h2)).trans (h.cs x hx h1 h2)⟩

/-- The loop after `k` witnesses passed. -/
structure St (s : State) (B : Addr) (L w c : Nat) (r : Spec.RsaKeyGen.Rand) (k : Nat) (t : State) : Prop
    extends LKeep s B L t where
  prep : Prep t B L w c
  used : word t.mem B (8 * hUsed) = BitVec.ofNat 64 (8 * w * (k + 1))
  idx : word t.mem B (8 * hIdx) = BitVec.ofNat 64 (mrS c (8 * w) r k).1
  uni : word t.mem B (8 * hUni) = BitVec.ofNat 64 (mrS c (8 * w) r k).2
  stat : word t.mem B (8 * hStat) = BitVec.ofNat 64 4

/-- What the loop leaves. -/
structure MrOut (s : State) (B : Addr) (L w c rl : Nat) (r : Spec.RsaKeyGen.Rand) (t : State) : Prop
    extends LKeep s B L t where
  prep : Prep t B L w c
  res : match Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) with
    | none => word t.mem B (8 * hStat) = BitVec.ofNat 64 0
    | some (b, rest) => word t.mem B (8 * hStat) = BitVec.ofNat 64 (if b then 1 else 2) ∧
        word t.mem B (8 * hUsed) = BitVec.ofNat 64 (rl - rest.length)

/-- The loop's facts about its start. -/
structure LIn (s : State) (B Ra : Addr) (L w c rl ch : Nat) (r : Spec.RsaKeyGen.Rand) : Prop where
  h35 : slot w VG.Impl.RsaKeyGen.PPC64LE.Candidate.nArr ≤ 8 * L
  shape : PrimeShape (64 * w) c
  hch : ch = Spec.RsaKeyGen.checksForSize (64 * w)
  hch' : ch < 2 ^ 63
  rand : word s.mem B (8 * hRand) = Ra
  rlen : word s.mem B (8 * hRandLen) = BitVec.ofNat 64 rl
  kk : word s.mem B (8 * hK) = BitVec.ofNat 64 (8 * w)
  chk : word s.mem B (8 * hChecks) = BitVec.ofNat 64 ch
  hrl : rl < 2 ^ 64
  tape : Spec.Rsa.bytesAt s.mem Ra rl = r
  rN : ∀ i < rl, InRegions (s.rd ++ s.wr) (off Ra i) 1
  rD : ∀ ρ ∈ [(⟨B, 8 * L⟩ : Region), below s.sp 176], (⟨Ra, rl⟩ : Region).Disjoint ρ
  wr : (⟨B, 8 * L⟩ : Region) ∈ s.wr
  hsp : 176 ≤ s.sp.toNat
  hstk : (below s.sp 176).Disjoint ⟨B, 8 * L⟩

theorem mrS_fst (c L : Nat) (r : Spec.RsaKeyGen.Rand) (k : Nat) : (mrS c L r k).1 = k + 1 := by
  rw [← VG.Proof.RsaKeyGen.mrSB_eq_mrS]; exact VG.Proof.RsaKeyGen.mrSB_first _ _ _ _ _

theorem mrS_snd (c L : Nat) (r : Spec.RsaKeyGen.Rand) (k : Nat) : (mrS c L r k).2 ≤ k := by
  rw [← VG.Proof.RsaKeyGen.mrSB_eq_mrS]; exact VG.Proof.RsaKeyGen.mrSB_uniform_le _ _ _ _ _

theorem round_eq (c x : Nat) :
    Proof.MillerRabin.Round.round c x =
      Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2 x := rfl

theorem statOf_eq {c L ch : Nat} {r : Spec.RsaKeyGen.Rand} {k : Nat} (b : Bool) :
    statOf (mrS c L r k).1 ((mrS c L r k).2 + if b then 1 else 0) ch =
      if (mrS c L r k).1 + 1 ≤ Spec.RsaKeyGen.blindedChecks ∨ (mrS c L r k).2 + (if b then 1 else 0) < ch
      then 4 else 1 := by
  generalize (mrS c L r k).1 = I
  generalize (mrS c L r k).2 + (if b then 1 else 0) = U
  unfold statOf Spec.RsaKeyGen.blindedChecks
  split <;> split <;> omega_arith

theorem St.keep {s t t' : State} {B : Addr} {L w c : Nat} {r : Spec.RsaKeyGen.Rand} {k : Nat} {rs : List Reg}
    (h : St s B L w c r k t) (K : Keep rs t t') (hm : t'.mem = t.mem)
    (hr : ∀ x ∈ rs, x ∈ lpRegs := by decide)
    (he : ∀ x ∈ VG.Proof.MillerRabin.PPC64LE.envRegs, x ∉ rs := by decide) : St s B L w c r k t' :=
  ⟨h.toLKeep.keep K hm hr, h.prep.keep (h.prep.env.keep K he) (fun _ _ => by rw [hm]) (fun _ _ => by rw [hm]),
    by rw [hm]; exact h.used, by rw [hm]; exact h.idx, by rw [hm]; exact h.uni, by rw [hm]; exact h.stat⟩

theorem MrOut.keep {s t t' : State} {B : Addr} {L w c rl : Nat} {r : Spec.RsaKeyGen.Rand} {rs : List Reg}
    (h : MrOut s B L w c rl r t) (K : Keep rs t t') (hm : t'.mem = t.mem)
    (hr : ∀ x ∈ rs, x ∈ lpRegs := by decide)
    (he : ∀ x ∈ VG.Proof.MillerRabin.PPC64LE.envRegs, x ∉ rs := by decide) : MrOut s B L w c rl r t' :=
  ⟨h.toLKeep.keep K hm hr, h.prep.keep (h.prep.env.keep K he) (fun _ _ => by rw [hm]) (fun _ _ => by rw [hm]),
    by rw [hm]; exact h.res⟩

/-- A draw keeps what the loop keeps. -/
theorem LKeep.draw {s t t' : State} {B Ra : Addr} {L w c u I U ch : Nat} (h : LKeep s B L t)
    (hd : DrPost t B Ra L w c u I U ch t') : LKeep s B L t' :=
  ⟨fun d hd' hk => (hd.hdr d hd' hk).trans (h.hdr d hd' hk), h.frame.trans (by have := hd.frame; rwa [h.sp] at this),
    hd.rd.trans h.rd, hd.wr.trans h.wr, hd.sp.trans h.sp, fun x hx h1 h2 =>
      (hd.cs x hx h1 (not_mem_of_sub (by decide) h2) (not_mem_of_sub (by decide) h2)
        (not_mem_of_sub (by decide) h2)).trans (h.cs x hx h1 h2)⟩

/-- A write of a header word the loop counts in. -/
theorem LKeep.write {s t t' : State} {B : Addr} {L : Nat} {rs : List Reg} (h : LKeep s B L t) {d : Nat}
    (hd : d ∈ lpWords) (hL : 256 ≤ 8 * L) {v : BitVec 64} (K : Keep rs t t')
    (hm : t'.mem = t.mem.writeW (off B (8 * d)) v) (hr : ∀ x ∈ rs, x ∈ lpRegs) : LKeep s B L t' := by
  have hd' : d < 31 := by simp only [lpWords, List.mem_cons, List.not_mem_nil, or_false] at hd; omega_using [hd]
  refine ⟨fun e he hk => ?_, by
    rw [hm]; exact h.frame.writeW (r := ⟨B, 8 * L⟩) (by simp) _ (Offset.contains_base _ (by omega_using [hL, hd']) (by omega_using [hd'])),
    K.rd.trans h.rd, K.wr.trans h.wr, K.sp.trans h.sp,
    fun x hx h1 h2 => (K.gpr x (not_mem_of_sub hr h2)).trans (h.cs x hx h1 h2)⟩
  rw [← h.hdr e he hk, hm]
  exact writeW_outside t.mem B (d := 8 * d) v (by omega_using [hd']) |>.word (hk d hd) (by omega_using [he])

/-- Whether `hK` octets are left: `rand_len − used ≥ hK`. -/
theorem avail_ok {t : State} {B : Addr} {Z rl u w : Nat} (hs : Scr t B Z) (h31 : t.gpr .r31 = B) (hZ : 256 ≤ Z)
    (hrl : word t.mem B (8 * hRandLen) = BitVec.ofNat 64 rl) (hu : word t.mem B (8 * hUsed) = BitVec.ofNat 64 u)
    (hk : word t.mem B (8 * hK) = BitVec.ofNat 64 (8 * w)) (hul : u ≤ rl) (hrl' : rl < 2 ^ 64) (hw : 8 * w < 2 ^ 63) :
    WP isa (.block ([ldh .r3 hRandLen, ldh .r4 hUsed, .sub .r3 .r3 .r4, ldh .r4 hK] ++ geFlag .r5 .r3 .r4)) t
      fun t' => (t'.gpr .r5 = BitVec.ofNat 64 (if 8 * w ≤ rl - u then 1 else 0) ∧ t'.mem = t.mem) ∧
        Keep [.r3, .r4, .r5, .r0] t t' := by
  have hnw := hs.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r3, .r4] (Q := fun t' => t'.gpr .r3 = BitVec.ofNat 64 rl - BitVec.ofNat 64 u ∧
      t'.gpr .r4 = BitVec.ofNat 64 (8 * w) ∧ t'.mem = t.mem) (by
    simp only [ldh, hRandLen, hUsed, hK] at hrl hu hk ⊢
    prun [h31, hs.ld (d := 144) (n := 8) (by omega_using [hZ]), hs.ld (d := 152) (n := 8) (by omega_using [hZ]),
      hs.ld (d := 216) (n := 8) (by omega_using [hZ]), hrl, hu, hk]) (by decide)) fun t₁ ⟨⟨a3, a4, m₁⟩, k₁⟩ => ?_
  refine WP.mono (geFlag_ok (a3.trans (Offset.ofNat_sub_ofNat hul)) a4 (by omega_using [hrl']) hw) fun t₂ ⟨⟨b5, m₂⟩, k₂⟩ => ?_
  exact ⟨⟨b5, m₂.trans m₁⟩, (k₁.trans k₂).mono⟩

/-- The loop's test: `hStat − 4`, zero to go on. -/
theorem tail_ok {t : State} {B : Addr} {Z v : Nat} (hs : Scr t B Z) (h31 : t.gpr .r31 = B) (hZ : 256 ≤ Z)
    (hst : word t.mem B (8 * hStat) = BitVec.ofNat 64 v) (hv : v ≤ 4) :
    WP isa (.block [ldh .r3 hStat, .subi .r3 .r3 4]) t
      fun t' => (isa.eval (.zero .d .r3) t' = some (decide (v = 4)) ∧ t'.mem = t.mem) ∧ Keep [.r3] t t' := by
  have hnw := hs.nowrap
  refine WP.mono (WP.keep [.r3] (Q := fun t' => t'.gpr .r3 = BitVec.ofNat 64 v - BitVec.ofNat 64 4 ∧
      t'.mem = t.mem) (by
    simp only [ldh, hStat] at hst ⊢
    prun [h31, hs.ld (d := 160) (n := 8) (by omega_using [hZ]), hst]) (by decide)) fun t' ⟨⟨a3, m⟩, k⟩ => ⟨⟨?_, m⟩, k⟩
  rw [eval_zero, a3]
  rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 by omega_using [hv]) with rfl | rfl | rfl | rfl | rfl <;> rfl

end VG.Proof.RsaKeyGen.PPC64LE.Cand

end

end


/-!
# A candidate on PPC64LE: the witnesses' loop, iteration by iteration

`mid_ok`: an iteration's draw, or `hStat := 0` when too few octets are left;
`body_ok`: the iteration and its test; `millerRabin_ok`: the loop
(`MrOut`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Witness (draw hUni)
open VG.Impl.MillerRabin.PPC64LE.Search (ldh sth geFlag hRand hRandLen hUsed hK hIdx hChecks hStat)
open VG.Proof.MillerRabin.PPC64LE.Search (Prep)
open VG.Proof.MillerRabin.PPC64LE (RoundImpl arr)
open VG.Proof.Bignum (slot)
open VG.Proof.RsaKeyGen (MrAt mrS goS wit)

/-- The loop's invariant, `n + 1` iterations left. -/
def Inv (s : State) (B : Addr) (L w c ch : Nat) (r : Spec.RsaKeyGen.Rand) (n : Nat) (t : State) : Prop :=
  ∃ k, MrAt c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2 (8 * w) r k n ∧
    St s B L w c r k t

/-- Whether the loop goes on after the iteration that draws at offset
`8 w (k + 1)`, with `n + 1` iterations left: enough octets, the witness
passes, and more iterations are left. -/
def MC (c w : Nat) (r : Spec.RsaKeyGen.Rand) (k n : Nat) : Prop :=
  8 * w * (k + 1) + 8 * w ≤ r.length ∧ Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1
    (Spec.Rsa.splitTwos (c - 1)).2 (wit c (8 * w) r (8 * w * (k + 1))).1 = true ∧ 0 < n

/-- After an iteration from `k` witnesses passed, before its test. -/
def Mid (s : State) (B : Addr) (L w c rl ch : Nat) (r : Spec.RsaKeyGen.Rand) (k n : Nat) (t : State) : Prop :=
  (MC c w r k n ∧ MrAt c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2 (8 * w) r (k + 1) (n - 1) ∧
      St s B L w c r (k + 1) t) ∨
    (¬ MC c w r k n ∧ ∃ v < 4, word t.mem B (8 * hStat) = BitVec.ofNat 64 v ∧ MrOut s B L w c rl r t)

theorem used_succ (w k : Nat) : 8 * w * (k + 1) + 8 * w = 8 * w * (k + 1 + 1) := by
  rw [Nat.mul_add (8 * w) (k + 1) 1, Nat.mul_one]

theorem tape_len {s : State} {B Ra : Addr} {L w c rl ch : Nat} {r : Spec.RsaKeyGen.Rand}
    (P : LIn s B Ra L w c rl ch r) : r.length = rl := by
  rw [← P.tape]; simp [Spec.Rsa.bytesAt]

theorem drIn_of {s t : State} {B Ra : Addr} {L w c rl ch k : Nat} {r : Spec.RsaKeyGen.Rand}
    (P : LIn s B Ra L w c rl ch r) (hi : St s B L w c r k t) (hav : 8 * w * (k + 1) + 8 * w ≤ r.length) :
    DrIn t B Ra L w c (8 * w * (k + 1)) (mrS c (8 * w) r k).1 (mrS c (8 * w) r k).2 ch := by
  have e := hi.prep.env
  have hnw := e.hs.nowrap
  have hZ := e.hZ
  have hw4 := e.hw
  rw [slot_lin] at hZ
  obtain ⟨_, hb1, _⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega_using [hw4] : 1 ≤ w) P.shape
  have hrl := tape_len P
  have hrl' := P.hrl
  have hk1 : 32 * (k + 1) ≤ 8 * w * (k + 1) := Nat.mul_le_mul_right _ (by omega_using [hw4])
  have hsn := mrS_snd c (8 * w) r k
  have hwd : ∀ d, d < 31 → d ∉ lpWords → word t.mem B (8 * d) = word s.mem B (8 * d) := fun d h1 h2 =>
    hi.hdr _ (by omega_using [h1]) (fun j hj => by
      have : j ≠ d := fun e => h2 (e ▸ hj)
      simp only [lpWords, List.mem_cons, List.not_mem_nil, or_false] at hj; omega_using [this])
  exact ⟨hi.prep, P.h35, hb1, P.shape.2.2, (hwd hRand (by decide) (by decide)).trans P.rand, hi.used,
    (hwd hK (by decide) (by decide)).trans P.kk,
    fun i hi' => by rw [hi.rd, hi.wr]; exact P.rN _ (by omega_using [hav, hrl, hi']),
    fun i hi' x hx hxe => P.rD ⟨B, 8 * L⟩ (by simp) _
      (Offset.contains_base Ra (d := 8 * w * (k + 1) + i) (by omega_using [hav, hrl, hi']) (by omega_using [hav, hrl, hrl', hi']))
      (by show Region.Contains _ (off Ra (8 * w * (k + 1) + i)) 1
          rw [hxe]; simp only [Region.Contains]; simp only [ofs] at hx; omega_using [hx]),
    by rw [hi.wr]; exact P.wr, by rw [hi.sp]; exact P.hsp, by rw [hi.sp]; exact P.hstk, hi.idx, hi.uni,
    (hwd hChecks (by decide) (by decide)).trans P.chk, by rw [mrS_fst]; omega_using [hav, hrl, hrl', hk1], by omega_using [hav, hrl, hrl', hk1, hsn], P.hch'⟩

/-- The witness drawn is the tape's. -/
theorem drX_eq {s t : State} {B Ra : Addr} {L w c rl ch k : Nat} {r : Spec.RsaKeyGen.Rand}
    (P : LIn s B Ra L w c rl ch r) (hi : St s B L w c r k t) (hav : 8 * w * (k + 1) + 8 * w ≤ r.length) :
    Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (off Ra (8 * w * (k + 1)))
      (8 * w))) = wit c (8 * w) r (8 * w * (k + 1)) := by
  have hrl := tape_len P
  have hrl' := P.hrl
  unfold wit
  rw [← seg_eq t.mem Ra (n := rl) (by omega_using [hav, hrl]), bytes_keep hi.frame (by omega_using [hrl']) P.rD, P.tape]

theorem mid_ok (R : RoundImpl) {s t : State} {B Ra : Addr} {L w c rl ch k n : Nat} {r : Spec.RsaKeyGen.Rand}
    (P : LIn s B Ra L w c rl ch r)
    (ha : MrAt c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2 (8 * w) r k n)
    (hi : St s B L w c r k t)
    (h5 : t.gpr .r5 = BitVec.ofNat 64 (if 8 * w ≤ rl - 8 * w * (k + 1) then 1 else 0)) :
    WP isa (.ite (.zero .d .r5) (.block [.li .r3 0, sth .r3 hStat]) (draw R.name R.code)) t
      (Mid s B L w c rl ch r k n) := by
  have e := hi.prep.env
  have hs := e.hs
  have hnw := hs.nowrap
  have hZ := e.hZ
  have hw4 := e.hw
  rw [slot_lin] at hZ
  obtain ⟨_, hb1, hwb⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega_using [hw4] : 1 ≤ w) P.shape
  have hL : 0 < 8 * w := by omega_using [hw4]
  have hrl := tape_len P
  have hrl' := P.hrl
  have hu := ha.used
  refine WP.ite _ (eval_zero_ofNat _ _ (by split <;> decide) h5) (fun hz => ?_) (fun hz => ?_)
  · have hav : ¬ 8 * w * (k + 1) + 8 * w ≤ r.length := by
      intro hc; simp only [decide_eq_true_eq] at hz; split at hz <;> first | exact absurd hz (by decide) | omega_arith
    obtain ⟨_, hpt⟩ := VG.Proof.RsaKeyGen.mrAt_short ha hwb hL hav
    refine WP.mono (WP.keep [.r3] (Q := fun t' => t'.mem = t.mem.writeW (off B (8 * hStat)) (BitVec.ofNat 64 0)) (by
      simp only [sth, hStat]; prun [e.h31, hs.st (d := 160) (n := 8) (by omega_using [hZ])]) (by decide)) fun t' ⟨tm, kt⟩ => ?_
    have st0 : word t'.mem B (8 * hStat) = BitVec.ofNat 64 0 := by rw [tm]; exact word_writeW_self _ _ _ _
    have wo := writeW_outside t.mem B (d := 8 * hStat) (BitVec.ofNat 64 0) (by simp only [hStat]; omega_using [])
    refine .inr ⟨fun h => hav h.1, 0, by decide, st0, hi.toLKeep.write (d := hStat) (by simp [lpWords, hStat]) (by omega_using [hZ]) kt tm
      (by decide), hi.prep.keep (e.keep kt (by decide)) (fun d hd => ?_) (fun j hj => ?_), ?_⟩
    · have s0' : slot w 0 + 8 ≤ 8 * L := by rw [slot_lin]; omega_using [hZ]
      have s27' : slot w 27 + 8 * w + 8 ≤ 8 * L := by rw [slot_lin]; omega_using [hZ]
      have s0 : 256 ≤ slot w 0 := by rw [slot_lin]; omega_using []
      have s27 : 256 ≤ slot w 27 := by rw [slot_lin]; omega_using []
      rw [tm]
      rcases hd with rfl | rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl | rfl
      all_goals exact wo.word (by simp only [hStat]; omega_arith) (by omega_arith)
    · rw [tm]
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        exact wo.val32 (by simp only [hStat]; rw [slot_lin]; omega_using []) (by rw [slot_lin]; omega_using [hnw, hZ])
    · show match Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) with
        | none => word t'.mem B (8 * hStat) = BitVec.ofNat 64 0
        | some (b, rest) => word t'.mem B (8 * hStat) = BitVec.ofNat 64 (if b then 1 else 2) ∧
            word t'.mem B (8 * hUsed) = BitVec.ofNat 64 (rl - rest.length)
      rw [hpt]; exact st0
  · have hav : 8 * w * (k + 1) + 8 * w ≤ r.length := by
      simp only [decide_eq_false_iff_not] at hz
      split at hz <;> first | omega | exact absurd rfl hz
    refine WP.mono (draw_ok R (drIn_of P hi hav)) fun t₂ hd => ?_
    have hX := drX_eq P hi hav
    have hst := hd.stat
    have hid := hd.idx
    have hun := hd.uni
    rw [hX] at hst hid hun
    have K := hi.toLKeep.draw hd
    by_cases hp : Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2
        (wit c (8 * w) r (8 * w * (k + 1))).1 = true
    · have hr : Proof.MillerRabin.Round.round c (wit c (8 * w) r (8 * w * (k + 1))).1 = true := by rw [round_eq]; exact hp
      simp only [hr, ↓reduceIte] at hst hid
      rw [statOf_eq] at hst
      by_cases hg : goS ch (mrS c (8 * w) r (k + 1))
      · obtain ⟨hn, ha'⟩ := VG.Proof.RsaKeyGen.mrAt_next ha hwb hL hav hp hg
        have hg' : (mrS c (8 * w) r k).1 + 1 ≤ Spec.RsaKeyGen.blindedChecks ∨
            (mrS c (8 * w) r k).2 + (if (wit c (8 * w) r (8 * w * (k + 1))).2 then 1 else 0) < ch := hg
        simp only [hg', ↓reduceIte] at hst
        refine .inl ⟨⟨hav, hp, hn⟩, ha', K, hd.prep, ?_, hid, hun, hst⟩
        rw [hd.used, used_succ]
      · obtain ⟨hn0, hpt⟩ := VG.Proof.RsaKeyGen.mrAt_done ha hwb hL hav hp hg
        have hg' : ¬ ((mrS c (8 * w) r k).1 + 1 ≤ Spec.RsaKeyGen.blindedChecks ∨
            (mrS c (8 * w) r k).2 + (if (wit c (8 * w) r (8 * w * (k + 1))).2 then 1 else 0) < ch) := hg
        simp only [hg', ↓reduceIte] at hst
        refine .inr ⟨fun h => by have := h.2.2; omega_arith, 1, by decide, hst, K, hd.prep, ?_⟩
        rw [hpt]
        refine ⟨hst, ?_⟩
        rw [hd.used, List.length_drop]
        congr 1; omega_using [hrl, hav]
    · have hp' : Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2
          (wit c (8 * w) r (8 * w * (k + 1))).1 = false := by simpa using hp
      have hr : Proof.MillerRabin.Round.round c (wit c (8 * w) r (8 * w * (k + 1))).1 = false := by
        rw [round_eq]; exact hp'
      obtain ⟨_, hpt⟩ := VG.Proof.RsaKeyGen.mrAt_fail ha hwb hL hav hp'
      simp only [hr, Bool.false_eq_true, ↓reduceIte] at hst
      refine .inr ⟨fun h => hp h.2.1, 2, by decide, hst, K, hd.prep, ?_⟩
      rw [hpt]
      refine ⟨hst, ?_⟩
      rw [hd.used, List.length_drop]
      congr 1; omega_using [hrl, hav]

/-- The loop's test of octets left. -/
abbrev availB : List Instr := [ldh .r3 hRandLen, ldh .r4 hUsed, .sub .r3 .r3 .r4, ldh .r4 hK] ++ geFlag .r5 .r3 .r4

/-- The loop's draw, or its end for want of octets. -/
abbrev drawI (R : RoundImpl) : Prog isa := .ite (.zero .d .r5) (.block [.li .r3 0, sth .r3 hStat]) (draw R.name R.code)

/-- The loop's test of its status. -/
abbrev tailB : List Instr := [ldh .r3 hStat, .subi .r3 .r3 4]

/-- What the loop leaves for the result. -/
abbrev mrLoop (R : RoundImpl) : Prog isa :=
  .loop (.seq (.block availB) (.seq (drawI R) (.block tailB))) (.zero .d .r3)

theorem availS {s t : State} {B Ra : Addr} {L w c rl ch k n : Nat} {r : Spec.RsaKeyGen.Rand}
    (P : LIn s B Ra L w c rl ch r)
    (ha : MrAt c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2 (8 * w) r k n)
    (hi : St s B L w c r k t) :
    WP isa (.block availB) t fun t₁ => St s B L w c r k t₁ ∧
      t₁.gpr .r5 = BitVec.ofNat 64 (if 8 * w ≤ rl - 8 * w * (k + 1) then 1 else 0) := by
  have e := hi.prep.env
  have hZ := e.hZ
  have hw4 := e.hw
  have hw' := e.hw'
  rw [slot_lin] at hZ
  have hrl := tape_len P
  have hrl' := P.hrl
  have hu := ha.used
  have hwd : ∀ d, d < 31 → d ∉ lpWords → word t.mem B (8 * d) = word s.mem B (8 * d) := fun d h1 h2 =>
    hi.hdr _ (by omega_using [h1]) (fun j hj => by
      have : j ≠ d := fun e => h2 (e ▸ hj)
      simp only [lpWords, List.mem_cons, List.not_mem_nil, or_false] at hj; omega_using [this])
  exact WP.mono (avail_ok e.hs e.h31 (by omega_using [hZ]) ((hwd hRandLen (by decide) (by decide)).trans P.rlen)
    hi.used ((hwd hK (by decide) (by decide)).trans P.kk) (by omega_using [hrl, hu]) (by omega_using [hrl']) (by omega_using [hw']))
    fun t₁ ⟨⟨a5, m₁⟩, k₁⟩ => ⟨hi.keep k₁ m₁, a5⟩

/-- After the loop's test. -/
def Tl (s : State) (B : Addr) (L w c rl ch : Nat) (r : Spec.RsaKeyGen.Rand) (k n : Nat) (t : State) : Prop :=
  (MC c w r k n ∧ isa.eval (.zero .d .r3) t = some true ∧
      MrAt c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2 (8 * w) r (k + 1) (n - 1) ∧
      St s B L w c r (k + 1) t) ∨
    (¬ MC c w r k n ∧ isa.eval (.zero .d .r3) t = some false ∧ MrOut s B L w c rl r t)

theorem tailS {s t : State} {B : Addr} {L w c rl ch k n : Nat} {r : Spec.RsaKeyGen.Rand}
    (hm : Mid s B L w c rl ch r k n t) : WP isa (.block tailB) t (Tl s B L w c rl ch r k n) := by
  rcases hm with ⟨hc, ha', hi'⟩ | ⟨hc, v, hv, hst, ho⟩
  · have e' := hi'.prep.env
    have hZ' := e'.hZ
    rw [slot_lin] at hZ'
    exact WP.mono (tail_ok e'.hs e'.h31 (by omega_using [hZ']) hi'.stat (by decide)) fun t₃ ⟨⟨ev, m₃⟩, k₃⟩ =>
      .inl ⟨hc, ev, ha', hi'.keep k₃ m₃⟩
  · have e' := ho.prep.env
    have hZ' := e'.hZ
    rw [slot_lin] at hZ'
    exact WP.mono (tail_ok e'.hs e'.h31 (by omega_using [hZ']) hst (by omega_using [hv])) fun t₃ ⟨⟨ev, m₃⟩, k₃⟩ =>
      .inr ⟨hc, by rw [ev, decide_eq_false (by omega_using [hv])], ho.keep k₃ m₃⟩

theorem loop_ok (R : RoundImpl) {s t : State} {B Ra : Addr} {L w c rl ch n : Nat} {r : Spec.RsaKeyGen.Rand}
    (P : LIn s B Ra L w c rl ch r) (hI : Inv s B L w c ch r n t) :
    WP isa (mrLoop R) t (MrOut s B L w c rl r) := by
  refine WP.loop (M := isa) (Q := MrOut s B L w c rl r) (Inv s B L w c ch r) ?_ n t hI
  intro n t hI
  obtain ⟨k, ha, hi⟩ := hI
  refine WP.seq (WP.mono (availS P ha hi) fun t₁ ⟨h₁, a5⟩ => ?_)
  refine WP.seq (WP.mono (mid_ok R P ha h₁ a5) fun t₂ hm => ?_)
  refine WP.mono (tailS hm) fun t₃ ht => ?_
  rcases ht with ⟨hc, ev, ha', hi'⟩ | ⟨-, ev, ho⟩
  · exact .inr ⟨ev, n - 1, by have := hc.2.2; omega_using [this], k + 1, ha', hi'⟩
  · exact .inl ⟨ev, ho⟩

/-- The loop's counts set up. -/
abbrev mrInit : List Instr :=
  [.li .r3 1, sth .r3 hIdx, .li .r3 0, sth .r3 hUni, .li .r3 4, sth .r3 hStat]

theorem init_ok {s : State} {B : Addr} {L w c : Nat} {r : Spec.RsaKeyGen.Rand} (hp : Prep s B L w c)
    (hu0 : word s.mem B (8 * hUsed) = BitVec.ofNat 64 (8 * w)) :
    WP isa (.block mrInit) s (St s B L w c r 0) := by
  have e := hp.env
  have hs := e.hs
  have hnw := hs.nowrap
  have hZ := e.hZ
  have hw4 := e.hw
  rw [slot_lin] at hZ
  refine (WP.mono (WP.keep [.r3] (Q := fun t => t.mem =
      ((s.mem.writeW (off B (8 * hIdx)) (BitVec.ofNat 64 1)).writeW (off B (8 * hUni)) (BitVec.ofNat 64 0)).writeW
        (off B (8 * hStat)) (BitVec.ofNat 64 4)) (by
    simp only [mrInit, sth, hIdx, hUni, hStat]
    prun [e.h31, hs.st (d := 176) (n := 8) (by omega_using [hZ]), hs.st (d := 16) (n := 8) (by omega_using [hZ]),
      hs.st (d := 160) (n := 8) (by omega_using [hZ])]) (by decide)) fun t₀ ⟨tm, k₀⟩ => ?_)
  have o : Outs B [(8 * hIdx, 8), (8 * hUni, 8), (8 * hStat, 8)] s.mem t₀.mem := by
    rw [tm]
    exact ((Outs.of_outside (writeW_outside _ B (d := 8 * hIdx) _ (by simp only [hIdx]; omega_using [])) (by simp)).trans
      (Outs.of_outside (writeW_outside _ B (d := 8 * hUni) _ (by simp only [hUni]; omega_using [])) (by simp))).trans
      (Outs.of_outside (writeW_outside _ B (d := 8 * hStat) _ (by simp only [hStat]; omega_using [])) (by simp))
  have ow : ∀ d, d + 8 ≤ 2 ^ 64 → (d + 8 ≤ 16 ∨ 24 ≤ d) → (d + 8 ≤ 160 ∨ 168 ≤ d) → (d + 8 ≤ 176 ∨ 184 ≤ d) →
      word t₀.mem B d = word s.mem B d := fun d h0 h1 h2 h3 =>
    o.word (fun x hx => by
      simp only [hIdx, hUni, hStat, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp only [] <;> omega_arith) h0
  refine ⟨⟨fun d hd hk => ow d (by omega_using [hd]) (hk 2 (by decide)) (hk 20 (by decide)) (hk 22 (by decide)),
    Frame.mono (frame_of_outs o (Z := 8 * L) (fun x hx => by
      simp only [hIdx, hUni, hStat, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp only [] <;> omega_using [hZ])) (by simp),
    k₀.rd, k₀.wr, k₀.sp, fun x _ _ h2 => k₀.gpr x (not_mem_of_sub (by decide) h2)⟩,
    hp.keep (e.keep k₀ (by decide)) (fun d hd => ?_) (fun j hj => ?_), ?_, ?_, ?_, ?_⟩
  · have s0' : slot w 0 + 8 ≤ 8 * L := by rw [slot_lin]; omega_using [hZ]
    have s27' : slot w 27 + 8 * w + 8 ≤ 8 * L := by rw [slot_lin]; omega_using [hZ]
    have s0 : 256 ≤ slot w 0 := by rw [slot_lin]; omega_using []
    have s27 : 256 ≤ slot w 27 := by rw [slot_lin]; omega_using []
    rcases hd with rfl | rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl | rfl
    all_goals exact ow _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
  · refine o.val32 (fun x hx => ?_) (by rcases hj with rfl | rfl | rfl | rfl | rfl <;> rw [slot_lin] <;> omega_using [hnw, hZ])
    simp only [hIdx, hUni, hStat, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp only [slot_lin] <;> omega_using []
  · rw [ow _ (by simp only [hUsed]; omega_using []) (by simp only [hUsed]; omega_using []) (by simp only [hUsed]; omega_using [])
      (by simp only [hUsed]; omega_using []), hu0, Nat.zero_add, Nat.mul_one]
  · rw [tm, (writeW_outside _ B (d := 8 * hStat) _ (by simp only [hStat]; omega_using [])).word
      (by simp only [hStat, hIdx]; omega_using []) (by simp only [hIdx]; omega_using []),
      (writeW_outside _ B (d := 8 * hUni) _ (by simp only [hUni]; omega_using [])).word
      (by simp only [hUni, hIdx]; omega_using []) (by simp only [hIdx]; omega_using []), word_writeW_self]
    rfl
  · rw [tm, (writeW_outside _ B (d := 8 * hStat) _ (by simp only [hStat]; omega_using [])).word
      (by simp only [hStat, hUni]; omega_using []) (by simp only [hUni]; omega_using []), word_writeW_self]
    rfl
  · rw [tm, word_writeW_self]


theorem millerRabin_ok (R : RoundImpl) {s : State} {B Ra : Addr} {L w c rl ch : Nat} {r : Spec.RsaKeyGen.Rand}
    (P : LIn s B Ra L w c rl ch r) (hp : Prep s B L w c)
    (hu0 : word s.mem B (8 * hUsed) = BitVec.ofNat 64 (8 * w)) (h8 : 8 * w ≤ rl) :
    WP isa (VG.Impl.RsaKeyGen.PPC64LE.Witness.millerRabin R.name R.code) s (MrOut s B L w c rl r) := by
  have hw4 := hp.env.hw
  obtain ⟨_, _, hwb⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega_using [hw4] : 1 ≤ w) P.shape
  have hrl := tape_len P
  have hc := VG.Proof.RsaKeyGen.primalityTest_cand (by omega_using [hw4]) P.shape (r.drop (8 * w))
  rw [← P.hch] at hc
  have h0 := VG.Proof.RsaKeyGen.mrAt_zero (ch := ch) hc hwb (by omega_using [hw4]) (by omega_using [h8, hrl])
  unfold VG.Impl.RsaKeyGen.PPC64LE.Witness.millerRabin
  exact WP.seq (WP.mono (init_ok hp hu0) fun t ht => loop_ok R P ⟨0, h0, ht⟩)

end VG.Proof.RsaKeyGen.PPC64LE.Cand

end

end

/-! ### `RsaKeyGen.PPC64LE.Cand.MontP`, which only this module used -/

section

/-!
# A candidate on PPC64LE: the candidate prepared

`prep_ok`: `montPrepHi` (`montPrepHi_ok`) on the layout `setup` wrote (`Lay`)
leaves the working space `Prep`ared for the rounds.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search (montPrepHi)
open VG.Proof.MillerRabin.PPC64LE.Search (Prep montPrepHi_ok mpRanges mpRegs)
open VG.Proof.MillerRabin.PPC64LE (Env arr)
open VG.Proof.Bignum (slot)

theorem prep_ok {s : State} {B : Addr} {L w c : Nat} (h : Env s B (8 * L) w) (hl : Lay s.mem B L w)
    (hn : arr s.mem B w 0 = c) (hodd : c % 2 = 1) (h3 : 3 ≤ c) (hct : 2 ^ (64 * (w - 1)) < c) :
    WP isa montPrepHi s fun t => (Prep t B L w c ∧ Outs B (mpRanges w) s.mem t.mem) ∧ Keep mpRegs s t := by
  have hnw := h.hs.nowrap
  have hZ := h.hZ
  rw [slot_lin] at hZ
  refine WP.mono (montPrepHi_ok h hn hodd h3 hct) fun t ⟨⟨e, n, inv, _, _, r1, r9, r10, ee, l, o⟩, k⟩ => ⟨⟨?_, o⟩, k⟩
  have ow : ∀ d, d + 8 ≤ 56 ∨ (64 ≤ d ∧ d + 8 ≤ 256) → word t.mem B d = word s.mem B d := fun d hd =>
    o.word (fun x hx => by
      simp only [mpRanges, VG.Impl.MillerRabin.PPC64LE.aE, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp only [slot_lin] <;> omega_using [hd]) (by omega_using [hd])
  exact ⟨e, (ow 0 (by omega_using [])).trans hl.len, (ow 48 (by omega_using [])).trans hl.wW, (ow 224 (by omega_using [])).trans hl.strideW,
    fun j hj => (ow _ (by omega_using [hj])).trans (hl.arrW j hj), n, h3, hodd, inv, r1, r9, r10, ee, l⟩

end VG.Proof.RsaKeyGen.PPC64LE.Cand

end

end


/-!
# A candidate on PPC64LE: trial division and Miller–Rabin

`test_ok`: once `gcd(c − 1, e) = 1`, the test's arguments into the header
(`testArgs_ok`), trial division (`DivOk`), and unless it finds a divisor, the
working space prepared (`prep_ok`), the witnesses (`millerRabin_ok`) and the
result (`testResult`): each way it ends gives the contract's results.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Candidate (test testResult trialDiv finish finNone finPrime nArr hTrial testArgs)
open VG.Impl.MillerRabin.PPC64LE.Search (ldh sth hUsed hStat hRand hRandLen hK hChecks)
open VG.Impl.RsaKeyGen (TrialTable32.symbol TrialTable32.packed)
open VG.Proof.MillerRabin.PPC64LE.Search (Prep)
open VG.Proof.MillerRabin.PPC64LE (RoundImpl Env arr)
open VG.Proof.Bignum (slot)

/-- The table of trial division, from the call's start. -/
structure TabOk (s0 : State) : Prop where
  fit : (s0.syms TrialTable32.symbol).toNat + 8 * 1024 ≤ 2 ^ 64
  rd : (⟨s0.syms TrialTable32.symbol, 8 * 1024⟩ : Region) ∈ s0.rd
  held : ∀ i < 1024, s0.mem.readW (s0.syms TrialTable32.symbol + BitVec.ofNat 64 (8 * i)) 64 =
    TrialTable32.packed.getD i 0
  dj : ∀ ρ ∈ [cO s0, cU s0, cS s0, cF s0], (⟨s0.syms TrialTable32.symbol, 8 * 1024⟩ : Region).Disjoint ρ

/-- The scratch region, as the proofs state it. -/
abbrev sB (s0 : State) : Addr := PPC64LE.stackArg s0 1

/-- The scratch's length in words. -/
abbrev sL (s0 : State) : Nat := (PPC64LE.stackArg s0 2).toNat

theorem cS_eq (s0 : State) : cS s0 = ⟨sB s0, 8 * sL s0⟩ := by simp only [cS, Nat.mul_comm]

/-- What changes within the scratch, from `Ctx`'s view. -/
theorem frame_scr {s0 : State} {m m' : Mem} (h : Frame [(⟨sB s0, 8 * sL s0⟩ : Region)] m m') :
    Frame [cS s0, below (off (cB s0) 176) 176] m m' := h.mono (by rw [cS_eq]; simp)

/-- `Outs` within the scratch. -/
theorem frame_outs {s0 : State} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs (sB s0) rs m m')
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ 8 * sL s0) : Frame [cS s0, below (off (cB s0) 176) 176] m m' :=
  frame_scr (frame_of_outs h hr)

/-- The table's words through `Bx`. -/
theorem TabOk.held_at {s0 s : State} (h : TabOk s0) (hb : Bx s0 s) {i : Nat} (hi : i < 1024) :
    s.mem.readW (s0.syms TrialTable32.symbol + BitVec.ofNat 64 (8 * i)) 64 = TrialTable32.packed.getD i 0 := by
  rw [hb.out.readW (r := ⟨s0.syms TrialTable32.symbol, 8 * 1024⟩)
    (Offset.contains_base _ (by omega_using [hi]) (by have := h.fit; omega_using [hi])) h.dj (by decide)]
  exact h.held i hi

/-- Octets of an input through `Bx`. -/
theorem bytes_bx {s0 s : State} (hb : Bx s0 s) {A : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (hd : ∀ ρ ∈ [cO s0, cU s0, cS s0, cF s0], (⟨A, n⟩ : Region).Disjoint ρ) :
    Spec.Rsa.bytesAt s.mem A n = Spec.Rsa.bytesAt s0.mem A n :=
  bytes_keep hb.out hn hd

/-- The facts once `gcd(c − 1, e) = 1`, for the candidate `c` of `w` words. -/
structure TIn (s0 s : State) (w c : Nat) : Prop where
  ctx : Ctx s0 s
  env : Env s (sB s0) (8 * sL s0) w
  lay : Lay s.mem (sB s0) (sL s0) w
  h35 : slot w nArr ≤ 8 * sL s0
  arr0 : arr s.mem (sB s0) w 0 = c
  shape : PrimeShape (64 * w) c
  hw : oL s0 = 8 * w
  hw64 : w ≤ 64
  r26 : s.gpr .r26 = s0.gpr .r10
  r27 : s.gpr .r27 = PPC64LE.stackArg s0 0
  r28 : s.gpr .r28 = BitVec.ofNat 64 (8 * w)
  h8 : 8 * w ≤ rL s0
  syms : s.syms = s0.syms
  tab : TabOk s0
  hop : cOp s0 = if Spec.RsaKeyGen.obviouslyComposite (64 * w) c then
      some (.rejected, (Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (rL s0)).drop (8 * w))
    else (Spec.RsaKeyGen.primalityTest c ((Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (rL s0)).drop (8 * w))).map
      fun pr => (if pr.1 then .prime c else .rejected, pr.2)

/-- `Ctx` through code that keeps memory, the regions and `r2`, `r23`–`r25`. -/
theorem Ctx.keep {s0 s t : State} {rs : List Reg} (h : Ctx s0 s) (k : Keep rs s t) (hm : t.mem = s.mem)
    (hr : ∀ r ∈ [Reg.r2, .r23, .r24, .r25], r ∉ rs := by decide) : Ctx s0 t :=
  h.step k.sp k.rd k.wr (by rw [hm]; exact Frame.refl _ _) (k.gpr _ (hr _ (by simp)))
    (k.gpr _ (hr _ (by simp))) (k.gpr _ (hr _ (by simp))) (k.gpr _ (hr _ (by simp)))

/-- The test's result from the status and octets used the witnesses left. -/
theorem res_ok {s0 u : State} {w c : Nat} (hc : Ctx s0 u) (hp : Prep u (sB s0) (sL s0) w c)
    (hw : oL s0 = 8 * w) (hres : match Spec.RsaKeyGen.primalityTest c
        ((Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (rL s0)).drop (8 * w)) with
      | none => word u.mem (sB s0) (8 * hStat) = BitVec.ofNat 64 0
      | some (b, rest) => word u.mem (sB s0) (8 * hStat) = BitVec.ofNat 64 (if b then 1 else 2) ∧
          word u.mem (sB s0) (8 * hUsed) = BitVec.ofNat 64 (rL s0 - rest.length))
    (hop : cOp s0 = (Spec.RsaKeyGen.primalityTest c
        ((Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (rL s0)).drop (8 * w))).map
      fun pr => (if pr.1 then .prime c else .rejected, pr.2)) :
    WP isa testResult u fun t => Bx s0 t ∧ CQ s0 (t.gpr .r3) t.mem := by
  have e := hp.env
  have hs := e.hs
  have hnw := hs.nowrap
  have hZ := e.hZ
  have hw4 := e.hw
  rw [slot_lin] at hZ
  have hcS : (cO s0).Disjoint ⟨sB s0, 8 * sL s0⟩ := by rw [← cS_eq]; exact hc.bx.pre.oS
  generalize hpt : Spec.RsaKeyGen.primalityTest c ((Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (rL s0)).drop (8 * w)) = pt
    at hres hop
  unfold testResult
  refine WP.seq (WP.mono (WP.keep [.r28, .r3] (Q := fun t => t.gpr .r28 = word u.mem (sB s0) (8 * hUsed) ∧
      t.gpr .r3 = word u.mem (sB s0) (8 * hStat) ∧ t.mem = u.mem) (by
    simp only [ldh, hUsed, hStat]
    prun [e.h31, hs.ld (d := 152) (n := 8) (by omega_using [hZ]), hs.ld (d := 160) (n := 8) (by omega_using [hZ])]) (by decide)) fun t₁ ⟨⟨a28, a3, m₁⟩, k₁⟩ => ?_)
  have c₁ := hc.keep k₁ m₁
  rcases pt with _ | ⟨b, rest⟩
  · refine WP.ite _ (eval_zero_ofNat _ _ (by decide) (a3.trans hres)) (fun _ => ?_) (fun h => absurd h (by decide))
    exact finNone_post c₁ (by rw [hop]; rfl)
  · obtain ⟨hst, hus⟩ := hres
    refine WP.ite _ (eval_zero_ofNat _ _ (by split <;> decide) (a3.trans hst))
      (fun h => absurd h (by cases b <;> decide)) (fun _ => ?_)
    refine WP.seq (WP.mono (WP.keep [.r3] (Q := fun t => t.gpr .r3 = BitVec.ofNat 64 (if b then 0 else 1) ∧
        t.mem = t₁.mem) (by
      prun [a3, hst]
      cases b <;> rfl) (by decide)) fun t₂ ⟨⟨b3, m₂⟩, k₂⟩ => ?_)
    have c₂ := c₁.keep k₂ m₂
    refine WP.ite _ (eval_zero_ofNat _ _ (by split <;> decide) b3) (fun h => ?_) (fun h => ?_)
    · have hb : b = true := by revert h; cases b <;> decide
      subst hb
      have p₂ := hp.keep (e.keep (k₁.trans k₂) (by decide)) (fun _ _ => by rw [m₂, m₁]) (fun _ _ => by rw [m₂, m₁])
      refine finPrime_post c₂ p₂.env.hs p₂.env.h31 (by rw [hw]; omega_using [hZ]) hw (by omega_using [hw4]) hcS ?_ (by rw [hop]; rfl)
        (by rw [k₂.gpr _ (by decide), a28, hus])
      rw [← slot0 (w := w)]; exact p₂.n
    · have hb : b = false := by revert h; cases b <;> decide
      subst hb
      refine fin_ok 3 (by decide) c₂ (by rw [hop]; rfl) (by rw [outOf, hop]; rfl)
        (by rw [k₂.gpr _ (by decide), a28, hus, usedOf, hop]; rfl)

theorem bytesAt_length (m : Mem) (A : Addr) (n : Nat) : (Spec.Rsa.bytesAt m A n).length = n := by
  simp [Spec.Rsa.bytesAt]

theorem hR_dj {s0 : State} (hp : CIn s0) : ∀ r ∈ [cO s0, cU s0, cS s0, cF s0], (cR s0).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.oR.symm
  · exact hp.uR.symm
  · exact hp.rS
  · exact hp.Fr.symm

theorem hP_dj {s0 : State} (hp : CIn s0) : ∀ r ∈ [cO s0, cU s0, cS s0, cF s0], (cP s0).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.oP.symm
  · exact hp.uP.symm
  · exact hp.pS
  · exact hp.Fp.symm

theorem hE_dj {s0 : State} (hp : CIn s0) : ∀ r ∈ [cO s0, cU s0, cS s0, cF s0], (cE s0).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.oE.symm
  · exact hp.uE.symm
  · exact hp.eS
  · exact hp.Fe.symm

/-- What holds of the call throughout the test. -/
structure TC (s0 : State) (w c : Nat) : Prop where
  h35 : slot w nArr ≤ 8 * sL s0
  shape : PrimeShape (64 * w) c
  hw : oL s0 = 8 * w
  hw64 : w ≤ 64
  h8 : 8 * w ≤ rL s0
  tab : TabOk s0
  hop : cOp s0 = if Spec.RsaKeyGen.obviouslyComposite (64 * w) c then
      some (.rejected, (Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (rL s0)).drop (8 * w))
    else (Spec.RsaKeyGen.primalityTest c ((Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (rL s0)).drop (8 * w))).map
      fun pr => (if pr.1 then .prime c else .rejected, pr.2)

theorem TIn.tc {s0 s : State} {w c : Nat} (h : TIn s0 s w c) : TC s0 w c :=
  ⟨h.h35, h.shape, h.hw, h.hw64, h.h8, h.tab, h.hop⟩

theorem TC.c8 {s0 : State} {w c : Nat} (h : TC s0 w c) (hw4 : 4 ≤ w) : 8161 < c := by
  have := h.shape.2.1
  have : 2 ^ 14 ≤ 2 ^ (64 * w - 2) := Nat.pow_le_pow_right (by decide) (by omega_using [hw4])
  omega_arith

/-- The test's arguments in the header. -/
structure THdr (s0 : State) (w : Nat) (m : Mem) : Prop where
  rand : word m (sB s0) (8 * hRand) = s0.gpr .r10
  randLen : word m (sB s0) (8 * hRandLen) = PPC64LE.stackArg s0 0
  used : word m (sB s0) (8 * hUsed) = BitVec.ofNat 64 (8 * w)
  kk : word m (sB s0) (8 * hK) = BitVec.ofNat 64 (8 * w)
  checks : word m (sB s0) (8 * hChecks) = BitVec.ofNat 64 (VG.Proof.RsaKeyGen.checksW w)

theorem THdr.keep {s0 : State} {w : Nat} {m m' : Mem} (h : THdr s0 w m)
    (ow : ∀ d, 128 ≤ d → d + 8 ≤ 224 → word m' (sB s0) d = word m (sB s0) d) : THdr s0 w m' :=
  ⟨(ow _ (by simp only [hRand]; omega_using []) (by simp only [hRand]; omega_using [])).trans h.rand,
    (ow _ (by simp only [hRandLen]; omega_using []) (by simp only [hRandLen]; omega_using [])).trans h.randLen,
    (ow _ (by simp only [hUsed]; omega_using []) (by simp only [hUsed]; omega_using [])).trans h.used,
    (ow _ (by simp only [hK]; omega_using []) (by simp only [hK]; omega_using [])).trans h.kk,
    (ow _ (by simp only [hChecks]; omega_using []) (by simp only [hChecks]; omega_using [])).trans h.checks⟩

/-- After `testArgs`. -/
structure T1 (s0 : State) (w c : Nat) (s : State) : Prop where
  ctx : Ctx s0 s
  env : Env s (sB s0) (8 * sL s0) w
  lay : Lay s.mem (sB s0) (sL s0) w
  arr0 : arr s.mem (sB s0) w 0 = c
  hdr : THdr s0 w s.mem
  trial : word s.mem (sB s0) (8 * hTrial) = BitVec.ofNat 64 (nTrial w)
  r28 : s.gpr .r28 = BitVec.ofNat 64 (8 * w)
  syms : s.syms = s0.syms
  tc : TC s0 w c

theorem argsS {s0 s : State} {w c : Nat} (h : TIn s0 s w c) : WP isa (.block testArgs) s (T1 s0 w c) := by
  have hp := h.ctx.bx.pre
  have e := h.env
  have hnw := e.hs.nowrap
  have hZ := e.hZ
  have hw4 := e.hw
  rw [slot_lin] at hZ
  refine WP.mono_syms (testArgs_ok e h.lay.wW h.hw64) fun t₁ ⟨⟨ao, o₁, _⟩, k₁⟩ sy₁ => ?_
  have ow : ∀ d, d + 8 ≤ 128 ∨ 224 ≤ d → d + 8 ≤ 8 * sL s0 → word t₁.mem (sB s0) d = word s.mem (sB s0) d :=
    fun d hd hd' => o₁.word hd (by omega_using [hnw, hd'])
  refine ⟨h.ctx.step k₁.sp k₁.rd k₁.wr (frame_scr (frame_of_outside o₁ (by omega_using [hZ]))) (k₁.gpr _ (by decide))
    (k₁.gpr _ (by decide)) (k₁.gpr _ (by decide)) (k₁.gpr _ (by decide)), e.keep k₁ (by decide),
    ⟨(ow 0 (by omega_using []) (by omega_using [hZ])).trans h.lay.len, (ow 48 (by omega_using []) (by omega_using [hZ])).trans h.lay.wW,
      (ow 224 (by omega_using []) (by omega_using [hZ])).trans h.lay.strideW,
      fun j hj => (ow _ (by omega_using [hj]) (by omega_using [hZ, hj])).trans (h.lay.arrW j hj)⟩,
    by rw [← h.arr0]; exact o₁.val32 (by rw [slot_lin]; omega_using []) (by rw [slot_lin]; omega_using [hnw, hZ]),
    ⟨ao.rand.trans h.r26, ao.randLen.trans h.r27, ao.used.trans h.r28,
      ao.k.trans (by rw [h.ctx.r24, ← h.hw]; exact (ofNat_toNat64 _).symm), ao.checks⟩, ao.trial,
    (k₁.gpr _ (by decide)).trans h.r28, sy₁.trans h.syms, h.tc⟩

/-- Trial division's start. -/
theorem T1.divIn {s0 s : State} {w c : Nat} (h : T1 s0 w c s) : DivIn s (sB s0) (8 * sL s0) w (nTrial w) :=
  ⟨h.env, h.trial, by unfold nTrial; split <;> decide, by unfold nTrial; split <;> decide,
    by rw [h.syms]; exact h.tc.tab.fit, by rw [h.syms, h.ctx.bx.rd]; exact h.tc.tab.rd,
    fun i hi => by rw [h.syms]; exact h.tc.tab.held_at h.ctx.bx hi⟩

theorem T1.tabDj {s0 s : State} {w c : Nat} (h : T1 s0 w c s) :
    Region.Disjoint ⟨s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol, 8 * 1024⟩ ⟨sB s0, 8 * sL s0⟩ := by
  rw [h.syms, ← cS_eq]; exact h.tc.tab.dj _ (by simp)

/-- After trial division. -/
structure T2 (s0 : State) (w c : Nat) (s : State) : Prop where
  ctx : Ctx s0 s
  env : Env s (sB s0) (8 * sL s0) w
  lay : Lay s.mem (sB s0) (sL s0) w
  arr0 : arr s.mem (sB s0) w 0 = c
  hdr : THdr s0 w s.mem
  f : s.gpr .r22 = BitVec.ofNat 64 (if Spec.RsaKeyGen.obviouslyComposite (64 * w) c then 1 else 0)
  r28 : s.gpr .r28 = BitVec.ofNat 64 (8 * w)
  tc : TC s0 w c

theorem trialS {trial : Prog isa} (D : DivOk trial) {s0 s : State} {w c : Nat} (h : T1 s0 w c s) :
    WP isa (trialDiv trial) s (T2 s0 w c) := by
  have hp := h.ctx.bx.pre
  have e := h.env
  have hnw := e.hs.nowrap
  have hZ := e.hZ
  have hw4 := e.hw
  rw [slot_lin] at hZ
  refine WP.mono (trialDiv_ok D h.divIn h.tabDj) fun t₂ ⟨f₂, m₂, g₂, r23₂, r24₂, rd₂, wr₂, sp₂⟩ => ?_
  rw [h.arr0, show nTrial w = if w ≤ 16 then 512 else 1024 from rfl, trialPrefix_spec (h.tc.c8 hw4)] at f₂
  have w₂ : Frame [cS s0, below (off (cB s0) 176) 176] s.mem t₂.mem := by
    rw [m₂]
    refine frame_scr (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW
      (List.mem_singleton_self _) _ ?_) <;> exact Offset.contains_base _ (by omega_using [hZ]) (by omega_using [])
  have o₂ : Outs (sB s0) [(24, 8), (40, 8)] s.mem t₂.mem := by
    rw [m₂]
    exact (Outs.of_outside (writeW_outside _ _ (d := 24) _ (by omega_using [])) (by simp)).trans
      (Outs.of_outside (writeW_outside _ _ (d := 40) _ (by omega_using [])) (by simp))
  have ow : ∀ d, d + 8 ≤ 24 ∨ (32 ≤ d ∧ d + 8 ≤ 40) ∨ 48 ≤ d → d + 8 ≤ 8 * sL s0 →
      word t₂.mem (sB s0) d = word s.mem (sB s0) d := fun d hd hd' =>
    o₂.word (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp only [] <;> omega_using [hd]) (by omega_using [hnw, hd'])
  refine ⟨h.ctx.step sp₂ rd₂ wr₂ w₂ (g₂ _ (by decide)) r23₂ r24₂ (g₂ _ (by decide)),
    ⟨e.hs.congr wr₂, (g₂ _ (by decide)).trans e.h10, (g₂ _ (by decide)).trans e.h29,
      (g₂ _ (by decide)).trans e.h11, (g₂ _ (by decide)).trans e.h31, e.hw, e.hw', e.hZ⟩,
    ⟨(ow 0 (by omega_using []) (by omega_using [hZ])).trans h.lay.len, (ow 48 (by omega_using []) (by omega_using [hZ])).trans h.lay.wW,
      (ow 224 (by omega_using []) (by omega_using [hZ])).trans h.lay.strideW,
      fun j hj => (ow _ (by omega_using []) (by omega_using [hZ, hj])).trans (h.lay.arrW j hj)⟩, ?_,
    h.hdr.keep fun d h1 h2 => ow d (by omega_using [h1]) (by omega_using [hZ, h2]), f₂, (g₂ _ (by decide)).trans h.r28, h.tc⟩
  rw [← h.arr0]
  exact o₂.val32 (fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp only [slot_lin] <;> omega_using []) (by rw [slot_lin]; omega_using [hnw, hZ])

/-- A divisor: rejected. -/
theorem compFin {s0 s : State} {w c : Nat} (h : T2 s0 w c s)
    (hoc : Spec.RsaKeyGen.obviouslyComposite (64 * w) c = true) :
    WP isa (finish 3) s fun t => Bx s0 t ∧ CQ s0 (t.gpr .r3) t.mem := by
  have hop := h.tc.hop
  have h8 := h.tc.h8
  rw [hoc] at hop
  simp only [↓reduceIte] at hop
  refine fin_ok 3 (by decide) h.ctx (by rw [hop]; rfl) (by rw [outOf, hop]) ?_
  rw [h.r28, usedOf, hop]
  simp only [List.length_drop, bytesAt_length]
  congr 1; omega_using [h8]

/-- The working space prepared. -/
structure T3 (s0 : State) (w c : Nat) (s : State) : Prop where
  ctx : Ctx s0 s
  prep : Prep s (sB s0) (sL s0) w c
  lin : LIn s (sB s0) (s0.gpr .r10) (sL s0) w c (rL s0) (VG.Proof.RsaKeyGen.checksW w)
    (Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (rL s0))
  hu0 : word s.mem (sB s0) (8 * hUsed) = BitVec.ofNat 64 (8 * w)
  tc : TC s0 w c
  noc : Spec.RsaKeyGen.obviouslyComposite (64 * w) c = false

theorem prepS {s0 s : State} {w c : Nat} (h : T2 s0 w c s)
    (hoc : Spec.RsaKeyGen.obviouslyComposite (64 * w) c = false) :
    WP isa VG.Impl.MillerRabin.PPC64LE.Search.montPrepHi s (T3 s0 w c) := by
  have hp := h.ctx.bx.pre
  have e := h.env
  have hnw := e.hs.nowrap
  have hZ := e.hZ
  have hw4 := e.hw
  have h35 := h.tc.h35
  simp only [nArr] at h35
  rw [slot_lin] at hZ h35
  have hfS := hp.fS
  have hcB := cB_fit hp
  have hrl := (PPC64LE.stackArg s0 0).isLt
  refine WP.mono (prep_ok e h.lay h.arr0 h.tc.shape.1 (by have := h.tc.c8 hw4; omega_using [this]) (by
    have := h.tc.shape.2.1
    have : 2 ^ (64 * (w - 1)) < 2 ^ (64 * w - 2) := Nat.pow_lt_pow_right (by decide) (by omega_using [hw4])
    omega_arith)) fun t₃ ⟨⟨p₃, o₃⟩, k₃⟩ => ?_
  have c₃ := h.ctx.step k₃.sp k₃.rd k₃.wr (frame_outs o₃ (fun x hx => by
    simp only [VG.Proof.MillerRabin.PPC64LE.Search.mpRanges, VG.Impl.MillerRabin.PPC64LE.aE, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp only [slot_lin] <;> omega_using [hZ])) (k₃.gpr _ (by decide))
    (k₃.gpr _ (by decide)) (k₃.gpr _ (by decide)) (k₃.gpr _ (by decide))
  have ow₃ : ∀ d, 64 ≤ d → d + 8 ≤ 256 → word t₃.mem (sB s0) d = word s.mem (sB s0) d := fun d h1 h3 =>
    o₃.word (fun x hx => by
      simp only [VG.Proof.MillerRabin.PPC64LE.Search.mpRanges, VG.Impl.MillerRabin.PPC64LE.aE, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp only [slot_lin] <;> omega_arith) (by omega_using [h3])
  have hd := h.hdr.keep (m' := t₃.mem) fun d h1 h2 => ow₃ d (by omega_using [h1]) (by omega_using [h2])
  have bF : below (off (cB s0) 176) 176 = ⟨cB s0, 176⟩ := by
    simp only [below, off, BitVec.add_sub_cancel]
  have sp₃ : t₃.sp = off (cB s0) 176 := c₃.bx.sp
  have P : LIn t₃ (sB s0) (s0.gpr .r10) (sL s0) w c (rL s0) (VG.Proof.RsaKeyGen.checksW w)
      (Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (rL s0)) := {
    h35 := h.tc.h35
    shape := h.tc.shape
    hch := (VG.Proof.RsaKeyGen.checksW_eq w (by have := h.tc.hw64; omega_using [this]) hw4).symm
    hch' := by have := VG.Proof.RsaKeyGen.checksW_le w; omega_using [this]
    rand := hd.rand
    rlen := hd.randLen.trans (ofNat_toNat64 _).symm
    kk := hd.kk
    chk := hd.checks
    hrl := hrl
    tape := bytes_bx c₃.bx hrl (hR_dj hp)
    rN := fun i hi => ⟨cR s0, List.mem_append_left _ (by rw [c₃.bx.rd]; exact hp.rR),
      Offset.contains_base _ (by simp only [rL] at hi; omega_using [hi]) (by have := hp.fr; simp only [rL] at hi; omega_using [hi])⟩
    rD := by
      intro ρ hρ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
      rcases hρ with rfl | rfl
      · rw [← cS_eq]; exact hp.rS
      · rw [sp₃, bF]; exact (hp.Fr.sub_left (Region.sub_prefix (by decide))).symm
    wr := by rw [c₃.bx.wr, bodyWr, hp.wr, ← cS_eq]; simp
    hsp := by rw [sp₃]; simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [hcB]
    hstk := by rw [sp₃, bF, ← cS_eq]; exact hp.FS.sub_left (Region.sub_prefix (by decide)) }
  exact ⟨c₃, p₃, P, hd.used, h.tc, hoc⟩

/-- After the witnesses. -/
structure T4 (s0 : State) (w c : Nat) (s : State) : Prop where
  ctx : Ctx s0 s
  prep : Prep s (sB s0) (sL s0) w c
  res : match Spec.RsaKeyGen.primalityTest c ((Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (rL s0)).drop (8 * w)) with
    | none => word s.mem (sB s0) (8 * hStat) = BitVec.ofNat 64 0
    | some (b, rest) => word s.mem (sB s0) (8 * hStat) = BitVec.ofNat 64 (if b then 1 else 2) ∧
        word s.mem (sB s0) (8 * hUsed) = BitVec.ofNat 64 (rL s0 - rest.length)
  tc : TC s0 w c
  noc : Spec.RsaKeyGen.obviouslyComposite (64 * w) c = false

theorem mrStage {s0 s : State} {w c : Nat} (R : RoundImpl) (h : T3 s0 w c s) :
    WP isa (VG.Impl.RsaKeyGen.PPC64LE.Witness.millerRabin R.name R.code) s (T4 s0 w c) := by
  have hp := h.ctx.bx.pre
  have hcB := cB_fit hp
  have bF : below (off (cB s0) 176) 176 = ⟨cB s0, 176⟩ := by
    simp only [below, off, BitVec.add_sub_cancel]
  refine WP.mono (millerRabin_ok R h.lin h.prep h.hu0 h.tc.h8) fun t₄ ho => ?_
  have f₄ := ho.frame
  rw [h.ctx.bx.sp, ← cS_eq] at f₄
  have cs₄ : ∀ r ∈ [Reg.r2, .r23, .r24, .r25], t₄.gpr r = s.gpr r := fun r hr =>
    ho.cs r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;>
      decide) (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;>
      decide) (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;>
      decide)
  exact ⟨h.ctx.step ho.sp ho.rd ho.wr f₄ (cs₄ _ (by simp)) (cs₄ _ (by simp)) (cs₄ _ (by simp)) (cs₄ _ (by simp)),
    ho.prep, ho.res, h.tc, h.noc⟩

theorem T4.result_ok {s0 s : State} {w c : Nat} (h : T4 s0 w c s) :
    WP isa testResult s fun t => Bx s0 t ∧ CQ s0 (t.gpr .r3) t.mem := by
  have hop := h.tc.hop
  rw [h.noc] at hop
  simp only [Bool.false_eq_true, ↓reduceIte] at hop
  exact res_ok h.ctx h.prep h.tc.hw h.res hop

/-- Once `gcd(c − 1, e) = 1`: trial division, then Miller–Rabin. -/
theorem test_ok {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) {s0 s : State} {w c : Nat}
    (h : TIn s0 s w c) :
    WP isa (test trial R.name R.code) s fun t => Bx s0 t ∧ CQ s0 (t.gpr .r3) t.mem := by
  unfold test
  simp only [VG.Impl.RsaKeyGen.PPC64LE.Candidate.seqs]
  refine WP.seq (WP.mono (argsS h) fun t₁ h₁ => ?_)
  refine WP.seq (WP.mono (trialS D h₁) fun t₂ h₂ => ?_)
  refine WP.ite _ (eval_nonzero_ofNat' _ _ (by split <;> decide) h₂.f) (fun hz => ?_) (fun hz => ?_)
  · exact compFin h₂ (by revert hz; cases Spec.RsaKeyGen.obviouslyComposite (64 * w) c <;> decide)
  · have hoc : Spec.RsaKeyGen.obviouslyComposite (64 * w) c = false := by
      revert hz; cases Spec.RsaKeyGen.obviouslyComposite (64 * w) c <;> decide
    refine WP.seq (WP.mono (prepS h₂ hoc) fun t₃ h₃ => ?_)
    exact WP.seq (WP.mono (mrStage R h₃) fun t₄ h₄ => h₄.result_ok)

end VG.Proof.RsaKeyGen.PPC64LE.Cand
