module

public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Tests
import VerifiedGarbage.Proof.Ffdh.X86.Cand.Spec
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Load
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.X86.Cand.Halve
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Sieve
public import VerifiedGarbage.Spec.Ffdh.SievedCandidate
import VerifiedGarbage.Proof.Ffdh.X86.Cand.Divides
public import VerifiedGarbage.Proof.Ffdh.Contract

/-!
# The FFDH candidate on i686: p's checks and tests

`shape`: p from the tape's first `L` octets, cut to `bits` bits with its
top and lowest bits set (`shape_ok`); its generator's congruences
(`congruences_ok`); q (`half_ok`); and `main`: a rejection unless they hold,
q is odd and RSA's sieve passes p and q, else the tests (`main_ok`): the
result of `sievedParameterCandidate`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Ffdh.X86 VG.Proof.Ffdh.X86.KeyGen
open VG.Impl.Ffdh.X86.Candidate
open VG.Impl.Bignum.X86.PublicRt (argAt)

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- The tape's first `L` octets. -/
theorem bytesAt_take (m : Mem) (p : Addr) {L n : Nat} (h : L ≤ n) :
    Spec.Rsa.bytesAt m p L = (Spec.Rsa.bytesAt m p n).take L := by
  have := bytesAt_offset m p (a := 0) (b := L) (n := n) (by omega_arith)
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, List.drop_zero] using this

/-- p from the tape: `candidateOf bits x` for the integer `x` of its first `L` octets; the cursor
past them, and `bits` as the cut's width. -/
theorem shape_ok (h : In Ex base bytes len args s) {T : List Byte}
    (G : TapeGeo Ex args base bytes (s.gpr .esp) T.length)
    (hT : Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) T.length = T) (h3 : args 3 = BitVec.ofNat 32 len)
    (hL : len ≤ T.length) {bits : Nat} (hb : w32 s.mem base bitsOff = bits) (hbl : len = (bits + 7) / 8)
    (hb1 : 512 ≤ bits) (hb2 : bits ≤ 8192) :
    WP isa shape s fun t => Step Ex base bytes len args s t ∧
      sv t.mem base len .wide 9 = Spec.Ffdh.candidateOf bits (Spec.Rsa.os2ip (T.take len)) ∧
      w32 t.mem base curOff = len ∧ Kept base len [9] [curOff, kOff] s.mem t.mem := by
  have bl := h.bytes_lt
  have f9 := slot_fit1 h (j := 9) (by decide)
  have c1 := cb1 len
  have w1 := cw1 len
  have lb := len_le_bc len
  have lo' := h.lower'
  have bw := bc_eq_cwc len .wide
  have fit := G.fit
  have small := G.small
  unfold shape
  refine WP.seq (WP.mono (load_ok h (one_ok .wide) f9 (p := 2) (l := 3) (L := len) (by decide) (by decide) h3
    (by omega_arith) (by omega_arith) (by omega_arith)
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      VG.CallLay.inRegions_sub (off := 0) (G.rd _ _ h.extra) (by omega_arith : 0 + len ≤ T.length) (by omega_arith))
    (G.apart.sub_left (Region.sub_prefix hL))) fun u₁ ⟨V₁, O₁, K₁⟩ => ?_)
  rw [c1] at O₁
  rw [w1, bytesAt_take _ _ hL, hT] at V₁
  have S₁ : Step Ex base bytes len args s u₁ := Step.slot h (by decide) O₁ K₁
  have k₁ := kept_slot h O₁
  have h₁ := S₁.inp
  refine WP.seq (wp_movS (h₁.arg (i := 3) (by decide)) fun u₂ U₂ _ => ?_)
  refine hdr_store (h₁.regs U₂.keeps U₂.mem) hdr_cur fun u₃ S₃ W₃ k₃ O₃ g₃ _ _ => ?_
  refine wp_movS (hdr_read S₃.inp hdr_bits) fun u₄ U₄ _ => ?_
  refine hdr_store (S₃.inp.regs U₄.keeps U₄.mem) hdr_k fun u₅ S₅ W₅ k₅ O₅ _ _ _ => WP.block_nil ?_
  have S₂₅ : Step Ex base bytes len args u₁ u₅ :=
    (Step.regs h₁ U₂.mem U₂.keeps).trans (S₃.trans ((Step.regs S₃.inp U₄.mem U₄.keeps).trans S₅))
  have k₂₅ : Kept base len [] [curOff, kOff] u₁.mem u₅.mem :=
    (by rw [U₂.mem]; exact (Kept.refl _).mono : Kept base len [] [curOff, kOff] u₁.mem u₂.mem).trans
      (k₃.mono.trans ((by rw [U₄.mem]; exact (Kept.refl _).mono : Kept base len [] [curOff, kOff] u₃.mem u₄.mem).trans
        k₅.mono))
  have kw₅ : w32 u₅.mem base kOff = bits := by
    rw [W₅, U₄.gpr, k₃.word_eq, U₂.mem, k₁.word_eq, hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  have cw₅ : w32 u₅.mem base curOff = len := by
    rw [k₅.word_eq, U₄.mem, W₃, U₂.gpr, h3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  generalize hx : Spec.Rsa.os2ip (T.take len) = x at V₁
  have xl : x < 2 ^ (8 * len) := by
    have := VG.Proof.Bignum.os2ip_lt (T.take len)
    rw [List.length_take, Nat.min_eq_left hL, VG.Proof.Bignum.pow256_eq, hx] at this
    exact this
  have sv₅ : sv u₅.mem base len .wide 9 = x := by rw [k₂₅.slot_eq, ← V₁]
  refine WP.seq (WP.mono (cut_ok S₂₅.inp (j := 9) (by decide) true (k := bits) kw₅ (by omega_arith) (by omega_arith)
    (by rw [sv₅]; exact Nat.lt_of_lt_of_le xl (Nat.pow_le_pow_right (by decide) (by omega_arith))))
    fun u₆ ⟨h₆, O₆, V₆, K₆⟩ => ?_)
  simp only [↓reduceIte] at V₆
  rw [sv₅] at V₆
  have S₆ : Step Ex base bytes len args u₅ u₆ := Step.slot S₂₅.inp (by decide) O₆ K₆
  rw [← List.append_nil (setLow _)]
  refine setLow_ok h₆ (j := 9) (by decide) fun u₇ h₇ O₇ V₇ K₇ => WP.block_nil ?_
  have O₇' : Outside base (lo len (.slot .wide 9)) (bc len .wide) u₆.mem u₇.mem := O₇.mono (Nat.le_refl _) (by omega_arith)
  have S₇ : Step Ex base bytes len args u₆ u₇ := Step.slot h₆ (by decide) O₇' K₇
  refine ⟨S₁.trans (S₂₅.trans (S₆.trans S₇)), ?_, ?_, ?_⟩
  · rw [V₇, V₆]; rfl
  · rw [(kept_slot h₆ O₇').word_eq, (kept_slot S₂₅.inp O₆).word_eq, cw₅]
  · exact k₁.mono.trans (k₂₅.mono.trans ((kept_slot S₂₅.inp O₆).mono.trans (kept_slot h₆ O₇').mono))

theorem hdr_gen : Hdr genOff := ⟨.inl ⟨by decide, by decide⟩, by decide⟩
theorem hdr_ok : Hdr okOff := ⟨.inr ⟨by decide, by decide⟩, by decide⟩

/-- `p − t` into slot 12, through `t` in slot 16. -/
theorem minus_ok (h : In Ex base bytes len args s) {p t : Nat} (hp : sv s.mem base len .wide 9 = p) (ht : t ≤ p)
    (htl : t < 2 ^ 32) :
    WP isa (minus t) s fun u => Step Ex base bytes len args s u ∧ sv u.mem base len .wide 12 = p - t ∧
      Kept base len [12, 16] [] s.mem u.mem := by
  unfold minus
  refine WP.seq (WP.mono (setW_ok h (a := 16) (v := t) (by decide) htl) fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
  have S₁ : Step Ex base bytes len args s u₁ := Step.slot h (by decide) O₁ K₁
  have p₁ : sv u₁.mem base len .wide 9 = p := by rw [slotKeep h (by decide) (by decide) O₁, hp]
  refine WP.mono (subW_ok S₁.inp (o := 12) (a := 9) (b := 16) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by rw [V₁, p₁]; exact ht)) fun u ⟨S, V, k, _, _⟩ => ⟨S₁.trans S, by rw [V, V₁, p₁], ?_⟩
  exact (kept_slot h O₁).mono.trans k.mono

/-- A divisibility test, as a stage. -/
theorem dividesS_ok (h : In Ex base bytes len args s) {j : Nat} (hj : j ≤ 27) {prime inv : Nat}
    (p3 : 3 ≤ prime) (p65 : prime ≤ 65537) (podd : prime % 2 = 1) (pinv : (prime * inv + 1) % 2 ^ 32 = 0)
    (invl : inv < 2 ^ 32) :
    WP isa (divides (.slot .wide j) prime inv) s fun t => Step Ex base bytes len args s t ∧
      t.gpr .eax = BitVec.ofNat 32 (decide (sv s.mem base len .wide j % prime = 0)).toNat ∧
      Kept base len [] [] s.mem t.mem :=
  WP.mono (divides_ok h hj p3 p65 podd pinv invl) fun _ ⟨I, F, E, K⟩ =>
    ⟨⟨I, frameR_mono F (fun _ hp => nomatch hp), K⟩, E, kept_out h (r := below (s.gpr .esp) 96) F h.room.apart.symm⟩

/-- p's congruences for its generator `g` (2 or 5): `eax` its `generationShape`. -/
theorem congruences_ok (h : In Ex base bytes len args s) {p g bits : Nat} (hp : sv s.mem base len .wide 9 = p)
    (hp3 : 3 ≤ p) (hpo : p % 2 = 1) (hbl : Spec.RsaKeyGen.bitLength p = bits) (hb : 512 ≤ bits ∧ bits ≤ 8192)
    (hg : w32 s.mem base genOff = g) (hg25 : g = 2 ∨ g = 5) :
    WP isa congruences s fun t => Step Ex base bytes len args s t ∧
      t.gpr .eax = BitVec.ofNat 32 (Spec.Ffdh.generationShape bits g p).toNat ∧
      Kept base len [12, 16] [okOff] s.mem t.mem := by
  unfold congruences
  refine WP.seq (wp_movS (hdr_read h hdr_gen) fun u₁ U₁ _ => wp_cmpi fun u₂ F₂ _ z₂ => WP.block_nil ?_)
  have m₂ : u₂.mem = s.mem := by rw [F₂.mem, U₁.mem]
  have S₂ : Step Ex base bytes len args s u₂ := Step.regs h m₂ (U₁.keeps.trans (F₂.keeps _))
  have h₂ := S₂.inp
  have p₂ : sv u₂.mem base len .wide 9 = p := by rw [m₂, hp]
  have k₂ : Kept base len [12, 16] [okOff] s.mem u₂.mem := by rw [m₂]; exact (Kept.refl _).mono
  have gl : g < 2 ^ 32 := by omega_arith
  refine WP.ite (decide (g = 2)) (by
      show u₂.zf = _
      rw [z₂, U₁.gpr, hg, show (2 : BitVec 32) = BitVec.ofNat 32 2 from rfl, sub_beq gl (by decide)])
    (fun e => ?_) fun e => ?_
  · obtain rfl : g = 2 := by simpa using e
    rw [gen2_eq hb hbl (by omega_arith)]
    unfold gen2
    refine WP.seq (lowWord_ok h₂ (j := 9) (by decide) fun u₃ m₃ K₃ e₃ => wp_andi fun u₄ U₄ =>
      wp_cmpi fun u₅ F₅ _ z₅ => WP.block_nil ?_)
    have m₅ : u₅.mem = s.mem := by rw [F₅.mem, U₄.mem, m₃, m₂]
    have S₅ : Step Ex base bytes len args s u₅ :=
      S₂.trans (Step.regs h₂ (by rw [m₅, m₂]) ((K₃.trans (U₄.keeps.mono (by decide))).trans (F₅.keeps _)))
    have e₄ : u₄.gpr .eax = BitVec.ofNat 32 (p % 8) := by
      rw [U₄.gpr, e₃, p₂]
      apply BitVec.eq_of_toNat_eq
      have e8 : p % 2 ^ 32 % 8 = p % 8 := Nat.mod_mod_of_dvd p (by decide)
      rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide)),
        show (7 : BitVec 32).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, e8,
        Nat.mod_eq_of_lt (by omega_arith : p % 8 < 2 ^ 32)]
    refine WP.ite (decide (p % 8 = 3)) (by
        show u₅.zf = _
        rw [z₅, e₄, show (3 : BitVec 32) = BitVec.ofNat 32 3 from rfl, sub_beq (by omega_arith) (by decide)])
      (fun e₈ => ?_) fun e₈ => ?_
    · have p8 : p % 8 = 3 := by simpa using e₈
      refine WP.seq (WP.mono (minus_ok S₅.inp (p := p) (t := 2) (by rw [m₅, hp]) (by omega_arith) (by decide))
        fun u₆ ⟨S₆, V₆, k₆⟩ => ?_)
      refine WP.mono (dividesS_ok S₆.inp (j := 12) (prime := 3) (inv := inv3) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) fun t ⟨S, E, k⟩ => ⟨S₅.trans (S₆.trans S), ?_, ?_⟩
      · rw [E, V₆]; simp [p8]
      · exact (by rw [m₅]; exact (Kept.refl _).mono : Kept base len [12, 16] [okOff] s.mem u₅.mem).trans
          (k₆.mono.trans k.mono)
    · have p8 : ¬ p % 8 = 3 := by simpa using e₈
      refine wp_movi fun t U => WP.block_nil ⟨S₅.trans (Step.regs S₅.inp U.mem U.keeps), ?_, ?_⟩
      · rw [U.gpr]; simp [p8]
      · rw [U.mem, m₅]; exact (Kept.refl _).mono
  · have g5 : g = 5 := by
      have : ¬ g = 2 := by simpa using e
      omega_arith
    subst g5
    rw [gen5_eq hb hbl hp3 hpo]
    unfold gen5
    refine WP.seq (WP.mono (minus_ok h₂ (p := p) (t := 2) p₂ (by omega_arith) (by decide)) fun u₃ ⟨S₃, V₃, k₃⟩ => ?_)
    refine WP.seq (WP.mono (dividesS_ok S₃.inp (j := 12) (prime := 5) (inv := inv5) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)) fun u₄ ⟨S₄, E₄, k₄⟩ => ?_)
    rw [V₃] at E₄
    refine WP.seq (hdr_store S₄.inp hdr_ok fun u₅ S₅ W₅ k₅ _ g₅ _ _ => WP.block_nil ?_)
    have p₅ : sv u₅.mem base len .wide 9 = p := by rw [k₅.slot_eq, k₄.slot_eq, k₃.slot_eq, p₂]
    refine WP.seq (WP.mono (minus_ok S₅.inp (p := p) (t := 3) p₅ (by omega_arith) (by decide)) fun u₆ ⟨S₆, V₆, k₆⟩ => ?_)
    refine WP.seq (WP.mono (dividesS_ok S₆.inp (j := 12) (prime := 5) (inv := inv5) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)) fun u₇ ⟨S₇, E₇, k₇⟩ => ?_)
    rw [V₆] at E₇
    refine wp_orS (hdr_read S₇.inp hdr_ok) fun t U => WP.block_nil ⟨?_, ?_, ?_⟩
    · exact S₂.trans (S₃.trans (S₄.trans (S₅.trans (S₆.trans (S₇.trans (Step.regs S₇.inp U.mem U.keeps))))))
    · rw [U.gpr, E₇, k₇.word_eq, k₆.word_eq, W₅, E₄]
      cases decide ((p - 2) % 5 = 0) <;> cases decide ((p - 3) % 5 = 0) <;> rfl
    · exact k₂.trans (k₃.mono.trans (k₄.mono.trans (k₅.mono.trans (k₆.mono.trans (k₇.mono.trans
        (by rw [U.mem]; exact (Kept.refl _).mono))))))

/-- The specification's screen of p and q, in the machine's checks. -/
theorem screen_eq {bits g p : Nat} (hp : 8161 < p) (hpo : p % 2 = 1) (hq : 8161 < (p - 1) / 2) :
    (Spec.Ffdh.generationShape bits g p && Spec.Ffdh.primeShape p && Spec.Ffdh.primeShape ((p - 1) / 2) &&
      !Spec.RsaKeyGen.obviouslyComposite bits p && !Spec.RsaKeyGen.obviouslyComposite bits ((p - 1) / 2)) =
    (Spec.Ffdh.generationShape bits g p && decide ((p - 1) / 2 % 2 = 1) &&
      !VG.Proof.RsaKeyGen.trialPrefix p (sieveCount bits) &&
      !VG.Proof.RsaKeyGen.trialPrefix ((p - 1) / 2) (sieveCount bits)) := by
  rw [sieve_shape hp hpo]
  by_cases qo : (p - 1) / 2 % 2 = 1
  · rw [sieve_shape hq qo]
    simp only [qo, decide_true, Bool.and_true]
    cases Spec.Ffdh.generationShape bits g p <;> cases Spec.Ffdh.primeShape p <;>
      cases Spec.Ffdh.primeShape ((p - 1) / 2) <;> cases Spec.RsaKeyGen.obviouslyComposite bits p <;>
      cases Spec.RsaKeyGen.obviouslyComposite bits ((p - 1) / 2) <;> rfl
  · have : Spec.Ffdh.primeShape ((p - 1) / 2) = false := by
      unfold Spec.Ffdh.primeShape
      simp [show ¬ (p - 1) / 2 % 2 = 1 from qo]
    simp [this, qo]

/-- The octets used and the output of a candidate's result. -/
def candUsed (T : List Byte) : Option (Option Nat × Spec.RsaKeyGen.Rand) → Nat
  | some (_, rest) => T.length - rest.length
  | none => 0

def candOut (len : Nat) : Option (Option Nat × Spec.RsaKeyGen.Rand) → List Byte
  | some (some p, _) => Spec.Rsa.i2osp p len
  | _ => List.replicate len 0

theorem res_map (T : List Byte) (p len : Nat) (A : Option (Bool × Spec.RsaKeyGen.Rand)) :
    resStatus A = Proof.Ffdh.candidateStatus (A.map fun x => (if x.1 then some p else none, x.2)) ∧
      resUsed T A = candUsed T (A.map fun x => (if x.1 then some p else none, x.2)) ∧
      resOut p len A = candOut len (A.map fun x => (if x.1 then some p else none, x.2)) := by
  rcases A with _ | ⟨⟨⟩ | ⟨⟩, r⟩ <;> exact ⟨rfl, rfl, rfl⟩

/-- RSA's table after a stage. -/
theorem Table.step {Tb : BitVec 32} (TT : Table Tb (s.gpr .esp) s) {t : State}
    (S : Step Ex base bytes len args s t) (sy : t.syms = s.syms)
    (TA : Region.Disjoint ⟨Tb.setWidth 64, 8192⟩ ⟨base, bytes⟩) : Table Tb (t.gpr .esp) t := by
  have h := S.inp
  have fit := fR_fit h
  have bl := h.bytes_lt
  have tf := TT.fit
  refine ⟨by rw [sy]; exact TT.sym, fun i hi d hd => by rw [S.keeps.2.1, S.keeps.2.2]; exact TT.read i hi d hd,
    fun i hi => ?_, TT.fit, by rw [S.esp]; exact TT.far⟩
  rw [← TT.words i hi]
  refine S.frame.readW (r := ⟨Tb.setWidth 64, 8192⟩) (w := 64)
    (Offset.contains_base _ (by omega_arith : 8 * i + 8 ≤ 8192) (by omega_arith)) (fun r hr => ?_) (by decide)
  rw [frameR, List.mem_cons, List.mem_map] at hr
  rcases hr with rfl | ⟨q, hq, rfl⟩
  · exact TT.far
  · have := fit q hq
    exact TA.sub_right (Offset.sub_base _ (by omega_arith))

/-- `q = p >> 1` into slot 10. -/
theorem half_ok (h : In Ex base bytes len args s) {p : Nat} (hp : sv s.mem base len .wide 9 = p) :
    WP isa half s fun t => Step Ex base bytes len args s t ∧ sv t.mem base len .wide 10 = p / 2 ∧
      Kept base len [10] [] s.mem t.mem := by
  unfold half
  refine WP.seq (WP.mono (copyO_ok h (a := 9) (b := 10) (by decide) (by decide) (by decide))
    fun u ⟨S₁, V₁, k₁, _, _⟩ => ?_)
  refine WP.mono (halve_ok S₁.inp (j := 10) (by decide)) fun t ⟨_, O, V, K⟩ =>
    ⟨S₁.trans (Step.slot S₁.inp (by decide) O K), by rw [V, V₁, hp], k₁.trans (kept_slot S₁.inp O)⟩

/-- `test eax, eax` of a flag: ZF its negation. -/
theorem testEax_ok {b : Bool} (he : s.gpr .eax = BitVec.ofNat 32 b.toNat) :
    WP isa testEax s fun t => t.mem = s.mem ∧ Keeps [] s t ∧ isa.eval .e t = some (!b) :=
  wp_testS rfl fun t F z => WP.block_nil ⟨F.mem, F.keeps [], by
    show t.zf = _; rw [z, he]; cases b <;> rfl⟩

/-- q's lowest bit: ZF if q is even. -/
theorem oddQ_ok (h : In Ex base bytes len args s) {q : Nat} (hq : sv s.mem base len .wide 10 = q) :
    WP isa (.block (lowWord (.slot .wide 10) ++ ([.alu .and .eax (.imm 1)] : List Instr))) s fun t =>
      Step Ex base bytes len args s t ∧ t.mem = s.mem ∧ isa.eval .e t = some (decide (q % 2 = 0)) :=
  lowWord_ok h (j := 10) (by decide) fun u m K e => wp_andZ fun t U z => WP.block_nil
    ⟨Step.regs h (by rw [U.mem, m]) (K.trans (U.keeps.mono (by decide))), by rw [U.mem, m], by
      show t.zf = _
      rw [z, e, and_one_zero _ (Nat.mod_lt _ (by decide)), hq, Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 2 ^ 32)]⟩

/-- RSA's sieve, as a stage. -/
theorem sieveS_ok (h : In Ex base bytes len args s) {j : Nat} (hj : j ≤ 27) {Tb : BitVec 32}
    (TT : Table Tb (s.gpr .esp) s) {bits : Nat} (hb : w32 s.mem base bitsOff = bits) :
    WP isa (sieve (.slot .wide j)) s fun t => Step Ex base bytes len args s t ∧
      t.gpr .eax = BitVec.ofNat 32 (VG.Proof.RsaKeyGen.trialPrefix (sv s.mem base len .wide j) (sieveCount bits)).toNat ∧
      Kept base len [] [] s.mem t.mem :=
  WP.mono (sieve_ok h hj TT hb) fun _ ⟨I, F, E, K⟩ =>
    ⟨⟨I, frameR_mono F (fun _ hp => nomatch hp), K⟩, E, kept_out h (r := below (s.gpr .esp) 96) F h.room.apart.symm⟩

/-- p's checks and tests: the result of `sievedParameterCandidate` for a tape of at least `L`
octets. -/
theorem main_ok (h : In Ex base bytes len args s) {T : List Byte}
    (G : TapeGeo Ex args base bytes (s.gpr .esp) T.length)
    (hT : Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) T.length = T)
    (Ox : OutAt args base bytes len 0 (s.gpr .esp) s.wr) {up : BitVec 32}
    (U : UsedAt base bytes up (s.gpr .esp) ⟨byteAddr (args 0), len⟩ s.wr) (hu : w32 s.mem base usedOff = up.toNat)
    (h3 : args 3 = BitVec.ofNat 32 len) (hL : len ≤ T.length) {bits g : Nat} (hb : w32 s.mem base bitsOff = bits)
    (hbl : len = (bits + 7) / 8) (hb1 : 512 ≤ bits) (hb2 : bits ≤ 8192) (hg : w32 s.mem base genOff = g)
    (hg25 : g = 2 ∨ g = 5) {Tb : BitVec 32} (TT : Table Tb (s.gpr .esp) s)
    (TA : Region.Disjoint ⟨Tb.setWidth 64, 8192⟩ ⟨base, bytes⟩) :
    WP isa main s (Fin base len args up s
      (Proof.Ffdh.candidateStatus (Spec.Ffdh.sievedParameterCandidate bits g T))
      (candUsed T (Spec.Ffdh.sievedParameterCandidate bits g T))
      (candOut len (Spec.Ffdh.sievedParameterCandidate bits g T))) := by
  have hL' : (bits + 7) / 8 ≤ T.length := by omega_arith
  -- The candidate and q.
  generalize hx : Spec.Rsa.os2ip (T.take len) = x
  obtain ⟨hpo, hpl, hpu⟩ := ParameterCandidate.candidate_shape (bits := bits) (by omega_arith) x
  obtain ⟨hbp', hbp⟩ := ParameterCandidate.candidate_bitLength (bits := bits) (by omega_arith) x
  have hbq' := ParameterCandidate.half_bitLength (bits := bits) (by omega_arith) x
  generalize hp : Spec.Ffdh.candidateOf bits x = p at hpo hpl hpu hbp' hbp hbq'
  have big : 2 ^ 20 ≤ 2 ^ (bits - 1) := Nat.pow_le_pow_right (by decide) (by omega_arith)
  have p8 : p < 2 ^ (8 * len) := Nat.lt_of_lt_of_le hpu (Nat.pow_le_pow_right (by decide) (by omega_arith))
  have screen := screen_eq (bits := bits) (g := g) (p := p) (by omega_arith) hpo (by omega_arith)
  -- A rejection, from a stage of `s` that keeps the cursor and `used`.
  have rej : ∀ u, Step Ex base bytes len args s u → w32 u.mem base curOff = len →
      w32 u.mem base usedOff = up.toNat →
      (Spec.Ffdh.generationShape bits g p && decide ((p - 1) / 2 % 2 = 1) &&
        !VG.Proof.RsaKeyGen.trialPrefix p (sieveCount bits) &&
        !VG.Proof.RsaKeyGen.trialPrefix ((p - 1) / 2) (sieveCount bits)) = false →
      WP isa reject u (Fin base len args up s
        (Proof.Ffdh.candidateStatus (Spec.Ffdh.sievedParameterCandidate bits g T))
        (candUsed T (Spec.Ffdh.sievedParameterCandidate bits g T))
        (candOut len (Spec.Ffdh.sievedParameterCandidate bits g T))) := by
    intro u Su hc hu' e
    rw [sieved_reject hL' (by rw [← hbl, hx, hp, screen, e])]
    refine WP.mono (reject_ok Su.inp (by rw [Su.esp]; exact Ox.keep rfl Su.keeps)
      (by rw [Su.esp]; exact U.keep rfl Su.keeps) hu' hc) fun t R => ?_
    have := R.after Su
    simp only [Proof.Ffdh.candidateStatus, candUsed, candOut, List.length_drop,
      show T.length - (T.length - (bits + 7) / 8) = len by omega_arith]
    exact this
  unfold main
  -- p.
  refine WP.seq (WP.mono_syms (shape_ok h G hT h3 hL hb hbl hb1 hb2) fun u₁ ⟨S₁, P₁, C₁, k₁⟩ sy₁ => ?_)
  rw [hx, hp] at P₁
  -- Its congruences.
  refine WP.seq (WP.mono_syms (congruences_ok S₁.inp P₁ (by omega_arith) hpo hbp' ⟨hb1, hb2⟩ (by rw [k₁.word_eq, hg])
    hg25) fun u₂ ⟨S₂, E₂, k₂⟩ sy₂ => ?_)
  refine WP.seq (WP.mono_syms (testEax_ok E₂) fun u₃ ⟨m₃, K₃, z₃⟩ sy₃ => ?_)
  have S₃ : Step Ex base bytes len args s u₃ := S₁.trans (S₂.trans (Step.regs S₂.inp m₃ K₃))
  have cur₃ : w32 u₃.mem base curOff = len := by rw [m₃, k₂.word_eq, C₁]
  have used₃ : w32 u₃.mem base usedOff = up.toNat := by rw [m₃, k₂.word_eq, k₁.word_eq, hu]
  have p₃ : sv u₃.mem base len .wide 9 = p := by rw [m₃, k₂.slot_eq, P₁]
  have bits₃ : w32 u₃.mem base bitsOff = bits := by rw [m₃, k₂.word_eq, k₁.word_eq, hb]
  refine WP.ite _ z₃ (fun e => rej u₃ S₃ cur₃ used₃ (by
    have : Spec.Ffdh.generationShape bits g p = false := by simpa using e
    simp [this])) fun e => ?_
  have gt : Spec.Ffdh.generationShape bits g p = true := by simpa using e
  -- q, odd.
  refine WP.seq (WP.mono_syms (half_ok S₃.inp p₃) fun u₄ ⟨S₄, Q₄, k₄⟩ sy₄ => ?_)
  rw [show p / 2 = (p - 1) / 2 by omega_arith] at Q₄
  refine WP.seq (WP.mono_syms (oddQ_ok S₄.inp Q₄) fun u₅ ⟨S₅, m₅, z₅⟩ sy₅ => ?_)
  have S₀₅ : Step Ex base bytes len args s u₅ := S₃.trans (S₄.trans S₅)
  have cur₅ : w32 u₅.mem base curOff = len := by rw [m₅, k₄.word_eq, cur₃]
  have used₅ : w32 u₅.mem base usedOff = up.toNat := by rw [m₅, k₄.word_eq, used₃]
  refine WP.ite _ z₅ (fun e => rej u₅ S₀₅ cur₅ used₅ (by
    have : ¬ (p - 1) / 2 % 2 = 1 := by simp at e; omega_arith
    simp [this])) fun e => ?_
  have qo : (p - 1) / 2 % 2 = 1 := by simp at e; omega_arith
  have hbq := ParameterCandidate.half_pred_bitLength (bits := bits) (by omega_arith) x (by rw [hp]; exact qo)
  rw [hp] at hbq
  -- RSA's sieve on p.
  have sy₀₅ : u₅.syms = s.syms := sy₅.trans (sy₄.trans (sy₃.trans (sy₂.trans sy₁)))
  refine WP.seq (WP.mono_syms (sieveS_ok S₀₅.inp (j := 9) (bits := bits) (by decide) (TT.step S₀₅ sy₀₅ TA)
    (by rw [m₅, k₄.word_eq, bits₃])) fun u₆ ⟨S₆, E₆, k₆⟩ sy₆ => ?_)
  rw [m₅, k₄.slot_eq, p₃] at E₆
  refine WP.seq (WP.mono_syms (testEax_ok E₆) fun u₇ ⟨m₇, K₇, z₇⟩ sy₇ => ?_)
  have S₀₇ : Step Ex base bytes len args s u₇ := S₀₅.trans (S₆.trans (Step.regs S₆.inp m₇ K₇))
  have cur₇ : w32 u₇.mem base curOff = len := by rw [m₇, k₆.word_eq, cur₅]
  have used₇ : w32 u₇.mem base usedOff = up.toNat := by rw [m₇, k₆.word_eq, used₅]
  have ne₇ : isa.eval .ne u₇ = some (VG.Proof.RsaKeyGen.trialPrefix p (sieveCount bits)) := by
    show u₇.zf.map (!·) = _
    rw [show u₇.zf = _ from z₇]; simp
  refine WP.ite _ ne₇ (fun e => rej u₇ S₀₇ cur₇ used₇ (by simp [e])) fun e => ?_
  -- RSA's sieve on q.
  have sy₀₇ : u₇.syms = s.syms := sy₇.trans (sy₆.trans sy₀₅)
  refine WP.seq (WP.mono_syms (sieveS_ok S₀₇.inp (j := 10) (bits := bits) (by decide) (TT.step S₀₇ sy₀₇ TA)
    (by rw [m₇, k₆.word_eq, m₅, k₄.word_eq, bits₃])) fun u₈ ⟨S₈, E₈, k₈⟩ sy₈ => ?_)
  rw [m₇, k₆.slot_eq, m₅, Q₄] at E₈
  refine WP.seq (WP.mono_syms (testEax_ok E₈) fun u₉ ⟨m₉, K₉, z₉⟩ sy₉ => ?_)
  have S₀₉ : Step Ex base bytes len args s u₉ := S₀₇.trans (S₈.trans (Step.regs S₈.inp m₉ K₉))
  have cur₉ : w32 u₉.mem base curOff = len := by rw [m₉, k₈.word_eq, cur₇]
  have used₉ : w32 u₉.mem base usedOff = up.toNat := by rw [m₉, k₈.word_eq, used₇]
  have ne₉ : isa.eval .ne u₉ = some (VG.Proof.RsaKeyGen.trialPrefix ((p - 1) / 2) (sieveCount bits)) := by
    show u₉.zf.map (!·) = _
    rw [show u₉.zf = _ from z₉]; simp
  refine WP.ite _ ne₉ (fun e' => rej u₉ S₀₉ cur₉ used₉ (by simp [e'])) fun e' => ?_
  -- The tests.
  have pass : (Spec.Ffdh.generationShape bits g p && decide ((p - 1) / 2 % 2 = 1) &&
      !VG.Proof.RsaKeyGen.trialPrefix p (sieveCount bits) &&
      !VG.Proof.RsaKeyGen.trialPrefix ((p - 1) / 2) (sieveCount bits)) = true := by simp [gt, qo, e, e']
  rw [sieved_tests hL' (by rw [← hbl, hx, hp, screen, pass])]
  rw [← hbl, hx, hp]
  obtain ⟨e₁, e₂, e₃⟩ := res_map T p len (ParameterCandidate.screenedChecks p ((p - 1) / 2) (T.drop len))
  rw [← e₁, ← e₂, ← e₃]
  have k₀₉ : Kept base len [9, 10, 12, 16] [curOff, kOff, okOff] s.mem u₉.mem :=
    k₁.mono.trans (k₂.mono.trans ((by rw [m₃]; exact (Kept.refl _).mono : Kept base len [9, 10, 12, 16]
      [curOff, kOff, okOff] u₂.mem u₃.mem).trans (k₄.mono.trans ((by rw [m₅]; exact (Kept.refl _).mono :
        Kept base len [9, 10, 12, 16] [curOff, kOff, okOff] u₄.mem u₅.mem).trans (k₆.mono.trans
          ((by rw [m₇]; exact (Kept.refl _).mono : Kept base len [9, 10, 12, 16] [curOff, kOff, okOff] u₆.mem
            u₇.mem).trans (k₈.mono.trans (by rw [m₉]; exact (Kept.refl _).mono))))))))
  refine WP.mono (tests_ok S₀₉.inp (by rw [S₀₉.esp]; exact G) (by rw [tape_keep G S₀₉, hT])
    (by rw [S₀₉.esp]; exact Ox.keep rfl S₀₉.keeps) (by rw [S₀₉.esp]; exact U.keep rfl S₀₉.keeps) used₉
    (by rw [k₀₉.word_eq, hb]) hb1 hb2 (by rw [m₉, k₈.slot_eq, m₇, k₆.slot_eq, m₅, k₄.slot_eq, p₃])
    (by rw [m₉, k₈.slot_eq, m₇, k₆.slot_eq, m₅, Q₄]) (by omega_arith) hpo (by omega_arith) qo hbp hbp' hbq hbq' p8 cur₉ hL)
    fun t R => R.after S₀₉

end VG.Proof.Ffdh.X86.Cand
