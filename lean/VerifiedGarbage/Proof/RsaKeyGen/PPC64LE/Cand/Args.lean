module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Hyp
public import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Slot
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Bits
import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

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
  · rw [ite_eq_left h, ite_eq_right (by omega)]; decide
  · rw [ite_eq_right h, ite_eq_left (by omega)]

/-- `checksIf k v`: `r5 := v` if `k ≤ w`. -/
theorem checksIf_ok {s : State} {w a k v : Nat} (h3 : s.gpr .r3 = BitVec.ofNat 64 w)
    (h5 : s.gpr .r5 = BitVec.ofNat 64 a) (hw : w < 2 ^ 63) (hk : k < 2 ^ 15) (hv : v < 2 ^ 15) :
    WP isa (.block (checksIf k v)) s fun t =>
      (t.gpr .r5 = BitVec.ofNat 64 (if k ≤ w then v else a) ∧ t.gpr .r3 = s.gpr .r3 ∧ t.mem = s.mem) ∧
        Keep [.r4, .r5, .r6] s t := by
  refine WP.keep _ ?_ rfl rfl
  have hk' : k ≤ 2 ^ 15 := by omega
  prun [checksIf, h3, h5, exec_subi (show Reg.r3 ≠ .r0 by decide) hk', exec_li hv,
    flag_mask w k hw (by omega), sel_mask]
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
  have hZ' : 256 ≤ Z := by rw [slot_lin] at hZ; omega
  unfold testArgs
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r3, .r5] (Q := fun t => t.mem = (((s.mem.writeW (off B 136) (s.gpr .r26)).writeW
      (off B 144) (s.gpr .r27)).writeW (off B 152) (s.gpr .r28)).writeW (off B 216) (s.gpr .r24) ∧
      t.gpr .r3 = BitVec.ofNat 64 w ∧ t.gpr .r5 = BitVec.ofNat 64 27) ?_ (by decide)) fun t₁ ⟨⟨m₁, a3, a5⟩, k₁⟩ => ?_
  · simp only [sth, ldh, hRand, hRandLen, hUsed, hK, hW]
    prun [h.h31, h48, hs.st (d := 136) (n := 8) (by omega), hs.st (d := 144) (n := 8) (by omega),
      hs.st (d := 152) (n := 8) (by omega), hs.st (d := 216) (n := 8) (by omega), hs.ld (d := 48) (n := 8) (by omega),
      rdw _ B _ (show 48 + 8 ≤ 216 ∨ 216 + 8 ≤ 48 by decide) (by decide) (by decide),
      rdw _ B _ (show 48 + 8 ≤ 152 ∨ 152 + 8 ≤ 48 by decide) (by decide) (by decide),
      rdw _ B _ (show 48 + 8 ≤ 144 ∨ 144 + 8 ≤ 48 by decide) (by decide) (by decide),
      rdw _ B _ (show 48 + 8 ≤ 136 ∨ 136 + 8 ≤ 48 by decide) (by decide) (by decide)]
    done
  have hw' : w < 2 ^ 63 := by omega
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
    · rw [ite_eq_left e, ite_eq_right (by omega)]; decide
    · rw [ite_eq_right e, ite_eq_left (by omega)]; decide
  refine WP.mono (WP.keep [.r4, .r5] (Q := fun t => t.mem = (t₇.mem.writeW (off B 168)
      (BitVec.ofNat 64 (VG.Proof.RsaKeyGen.checksW w))).writeW (off B 128) (BitVec.ofNat 64 (nTrial w)) ∧
      t.gpr .r3 = t₇.gpr .r3) ?_ (by decide)) fun t ⟨⟨tm, t3⟩, kt⟩ => ?_
  · simp only [sth, hChecks, hTrial]
    prun [h31, g5, h3₇, hs₇.st (d := 168) (n := 8) (by omega), hs₇.st (d := 128) (n := 8) (by omega), htr]
    rw [hck]
  · have K := ((((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans kt))
    have hz : 224 ≤ Z := by omega
    rw [hm₇, m₁] at tm
    refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, by rw [t3, h3₇]⟩, K.mono (by simp)⟩
    · simp only [hRand]; rw [tm, rdw _ _ _ (by omega) (by omega) (by omega), rdw _ _ _ (by omega) (by omega) (by omega),
        rdw _ _ _ (by omega) (by omega) (by omega), rdw _ _ _ (by omega) (by omega) (by omega),
        rdw _ _ _ (by omega) (by omega) (by omega), word_writeW_self]
    · simp only [hRandLen]; rw [tm, rdw _ _ _ (by omega) (by omega) (by omega), rdw _ _ _ (by omega) (by omega) (by omega),
        rdw _ _ _ (by omega) (by omega) (by omega), rdw _ _ _ (by omega) (by omega) (by omega), word_writeW_self]
    · simp only [hUsed]; rw [tm, rdw _ _ _ (by omega) (by omega) (by omega), rdw _ _ _ (by omega) (by omega) (by omega),
        rdw _ _ _ (by omega) (by omega) (by omega), word_writeW_self]
    · simp only [hK]; rw [tm, rdw _ _ _ (by omega) (by omega) (by omega), rdw _ _ _ (by omega) (by omega) (by omega),
        word_writeW_self]
    · simp only [hChecks]; rw [tm, rdw _ _ _ (by omega) (by omega) (by omega), word_writeW_self]
    · simp only [hTrial]; rw [tm, word_writeW_self]
    · rw [tm]
      have o : ∀ (m : Mem) (d : Nat) (v : BitVec 64), 128 ≤ d → d + 8 ≤ 224 → Outside B 128 96 m (m.writeW (off B d) v) :=
        fun m d v h1 h2 => (writeW_outside m B (d := d) v (by omega)).mono h1 (by omega)
      exact ((((((o _ 136 _ (by omega) (by omega)).trans (o _ 144 _ (by omega) (by omega))).trans
        (o _ 152 _ (by omega) (by omega))).trans (o _ 216 _ (by omega) (by omega))).trans
        (o _ 168 _ (by omega) (by omega))).trans (o _ 128 _ (by omega) (by omega)))

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
    rw [Mem.readW_writeW_sep (Offset.sep B hd'.symm (by simp only [hTrial]; omega) (by omega)) (by decide)]
    exact h.cnt
  · have hf := h.fit
    have c1 : (⟨s.syms TrialTable32.symbol, 8 * 1024⟩ : Region).Contains
        (s.syms TrialTable32.symbol + BitVec.ofNat 64 (8 * i)) 8 :=
      Offset.contains_base _ (by omega) (by omega)
    have c2 : (⟨B, Z⟩ : Region).Contains (off B d) 8 := Offset.contains_base _ (by omega) (by omega)
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
    prun [e.h31, hs.st (d := 24) (n := 8) (by omega), hs.st (d := 40) (n := 8) (by omega)]
  refine WP.seq (WP.mono hst fun u hu => ?_)
  subst hu
  have h1 := h.write (s.gpr .r23) (d := 24) (by omega) (by simp only [hTrial]; omega) htab
  have h2 := h1.write (s.gpr .r24) (d := 40) (by omega) (by simp only [hTrial]; omega) htab
  have ha : arr ((s.mem.writeW (off B 24) (s.gpr .r23)).writeW (off B 40) (s.gpr .r24)) B w 0 = arr s.mem B w 0 := by
    have o := ((writeW_outside s.mem B (d := 24) (s.gpr .r23) (by omega)).mono (o' := 24) (n' := 24) (by omega)
      (by omega)).trans ((writeW_outside (s.mem.writeW (off B 24) (s.gpr .r23)) B (d := 40) (s.gpr .r24) (by omega)).mono
        (o' := 24) (n' := 24) (by omega) (by omega))
    exact o.val32 (by rw [slot_lin]; omega) (by rw [slot_lin]; omega)
  refine WP.seq (WP.mono (D.ok h2) fun v ⟨v22, vm, vk, vrd, vwr, vsp⟩ => ?_)
  have hsv := hs.congr vwr
  have h31 : v.gpr .r31 = B := (vk .r31 (by decide)).trans e.h31
  have rd24 : v.mem.readW (off B 24) 64 = s.gpr .r23 := by
    rw [vm]; show ((s.mem.writeW (off B 24) (s.gpr .r23)).writeW (off B 40) (s.gpr .r24)).readW _ 64 = _
    rw [Mem.readW_writeW_sep (Offset.sep B (by omega) (by omega) (by omega)) (by decide), Mem.readW_writeW_self64]
  have rd40 : v.mem.readW (off B 40) 64 = s.gpr .r24 := by
    rw [vm]; exact Mem.readW_writeW_self64 _ _ _
  refine WP.mono (WP.keep [.r23, .r24] (Q := fun t => t.gpr .r23 = s.gpr .r23 ∧ t.gpr .r24 = s.gpr .r24 ∧
      t.mem = v.mem ∧ t.gpr .r22 = v.gpr .r22) (by
    simp only [ldh, hOut, hOutLen]
    prun [h31, hsv.ld (d := 24) (n := 8) (by omega), hsv.ld (d := 40) (n := 8) (by omega), rd24, rd40]) (by decide))
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
