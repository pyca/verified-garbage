module

import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Copy
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.KeyBits32
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.MontPrep
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Prep
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.RelCTChain
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Phase
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.RoundCall
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Base
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Mem
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.WordCut
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream
public import VerifiedGarbage.Proof.MillerRabin.Contract
import VerifiedGarbage.Proof.Ffdh.MillerRabin

/-! ### `Ffdh.PPC64LE.ParameterCandidate.Witnesses`, which this module and modules that import it used -/

section

/-!
# An FFDH parameter candidate on PPC64LE: the witnesses, one draw at a time

`cw_short` and `cw_step`: `checkWitnesses` of a modulus `N` of `mb + 1`
bits (`bitLength (N − 1) = mb`) unfolded by one draw of `⌈mb / 8⌉` octets
at `u`, the witness `wA mb r u`, as the machine draws it.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses drawWitness_eq)

/-- The witness drawn at offset `u` of the tape, for a modulus of `mb` bits. -/
def wA (mb : Nat) (r : List Byte) (u : Nat) : Nat := Spec.Rsa.os2ip ((r.drop u).take ((mb + 7) / 8)) % 2 ^ mb

theorem mr_round_eq {N : Nat} (a : Nat) (hN : 3 ≤ N) (ho : N % 2 = 1) :
    Proof.MillerRabin.Round.round N a = Spec.Ffdh.mrRound N a := by
  simpa only [Proof.MillerRabin.Round.round] using VG.Proof.Ffdh.rsa_round_eq a hN ho

theorem cw_short {N mb n : Nat} (hbl : Spec.RsaKeyGen.bitLength (N - 1) = mb) (hm : 1 ≤ mb) {r : List Byte} {u : Nat}
    (h : r.length < u + (mb + 7) / 8) : checkWitnesses N (n + 1) (r.drop u) = none := by
  have hw : Spec.Ffdh.witnessOctets N = (mb + 7) / 8 := by simp only [Spec.Ffdh.witnessOctets, hbl]
  have hd : Spec.Ffdh.drawWitness N (r.drop u) = none := by
    rw [drawWitness_eq (by rw [hw]; omega_arith), hw]
    have : ¬((mb + 7) / 8 ≤ (r.drop u).length) := by rw [List.length_drop]; omega_arith
    simp only [this, ↓reduceIte]
  simp only [checkWitnesses, hd, Option.bind_eq_bind, Option.bind_none]

theorem cw_step {N mb n : Nat} (hbl : Spec.RsaKeyGen.bitLength (N - 1) = mb) (hm : 1 ≤ mb) {r : List Byte} {u : Nat}
    (h : u + (mb + 7) / 8 ≤ r.length) :
    checkWitnesses N (n + 1) (r.drop u) =
      if 2 ≤ wA mb r u ∧ wA mb r u < N - 1 then
        (if Spec.Ffdh.mrRound N (wA mb r u) then checkWitnesses N n (r.drop (u + (mb + 7) / 8))
          else some (false, r.drop (u + (mb + 7) / 8)))
      else checkWitnesses N (n + 1) (r.drop (u + (mb + 7) / 8)) := by
  have hw : Spec.Ffdh.witnessOctets N = (mb + 7) / 8 := by simp only [Spec.Ffdh.witnessOctets, hbl]
  have hl : (mb + 7) / 8 ≤ (r.drop u).length := by rw [List.length_drop]; omega_arith
  have hd := drawWitness_eq (w := N) (by rw [hw]; omega_arith) (r.drop u)
  rw [hw, hbl] at hd
  simp only [hl, ↓reduceIte, List.drop_drop] at hd
  have ha : Spec.Rsa.os2ip ((r.drop u).take ((mb + 7) / 8)) % 2 ^ mb = wA mb r u := rfl
  rw [ha] at hd
  by_cases hr : 2 ≤ wA mb r u ∧ wA mb r u < N - 1
  · simp only [hr, and_self, ↓reduceIte] at hd ⊢
    simp only [checkWitnesses, hd, Option.bind_eq_bind, Option.bind_some]
  · simp only [hr, ↓reduceIte] at hd ⊢
    simp only [checkWitnesses, hd, Option.bind_eq_bind]

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end

/-! ### `Ffdh.PPC64LE.ParameterCandidate.Draw`, which only this module used -/

section

/-!
# An FFDH parameter candidate on PPC64LE: drawing a witness

`dHead_ok`: the next `K = ⌈mb / 8⌉` octets of the tape at `used = u` into
array 4, `used := u + K`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Impl.Bignum.PPC64LE.PublicChecked (base)
open VG.Impl.Bignum.PPC64LE.Precompute (loadN)
open VG.Proof.Mont (val32)

/-- Before a draw of a witness for the modulus `N` of `mb` bits, `u`
octets of the tape read. -/
structure DPre (p : PP) (mb N u C : Nat) (s : State) : Prop where
  st : St p s
  ph : Ph p mb C s
  prep : Prep s p.B p.n (wOf mb) N
  used : word s.mem p.B (8 * hUsed) = BitVec.ofNat 64 u
  room : u + (mb + 7) / 8 ≤ p.r.length
  mb1 : 511 ≤ mb
  mb2 : mb ≤ p.bits

/-- The head of a draw: the octets' address in `r12`, their count in `r6`,
array 4's in `r10`, and `used` advanced. -/
theorem dHead_ok {C : Nat} {p : PP} {mb N u : Nat} {s : State} (h : DPre p mb N u C s) :
    WP isa (.block ([ldh .r12 hRand, ldh .r3 hUsed, .add .r12 .r12 .r3, ldh .r6 hK, .add .r3 .r3 .r6,
        sth .r3 hUsed] ++ base .r10 4)) s fun t =>
      (t.gpr .r12 = p.rp + BitVec.ofNat 64 u ∧ t.gpr .r6 = BitVec.ofNat 64 ((mb + 7) / 8) ∧
        t.gpr .r10 = off p.B (slot (wOf mb) 4) ∧
        t.mem = s.mem.writeW (p.B + BitVec.ofNat 64 152) (BitVec.ofNat 64 (u + (mb + 7) / 8))) ∧
      Keep [.r3, .r6, .r12, .r10] s t := by
  rw [WP.block_append_iff]
  have hk := h.ph.kW
  have hu := h.used
  simp only [word, off, hK, hUsed, Nat.reduceMul] at hk hu
  refine WP.mono (WP.keep [.r3, .r6, .r12] (Q := fun u' => u'.gpr .r12 = p.rp + BitVec.ofNat 64 u ∧
      u'.gpr .r6 = BitVec.ofNat 64 ((mb + 7) / 8) ∧
      u'.mem = s.mem.writeW (p.B + BitVec.ofNat 64 152) (BitVec.ofNat 64 (u + (mb + 7) / 8))) ?_ (by decide))
    fun t₁ ⟨⟨a12, a6, am⟩, k₁⟩ => ?_
  · simp only [ldh, sth, hRand, hUsed, hK]
    prun [h.st.r31, h.st.ld (d := 136) (by decide), h.st.ld (d := 152) (by decide),
      h.st.ld (d := 216) (by decide), h.st.st (d := 152) (by decide), h.st.args.rand', hk, hu]
    simp only [BitVec.ofNat_add]
  refine WP.mono (Pub.base_ok (rd := .r10) (by decide) (by decide)
    ((k₁.gpr .r10 (by decide)).trans h.ph.r10) ((k₁.gpr .r29 (by decide)).trans h.ph.r29) 4)
    fun t ⟨⟨a10, m⟩, k⟩ => ⟨⟨(k.gpr .r12 (by decide)).trans a12, (k.gpr .r6 (by decide)).trans a6, a10,
      m.trans am⟩, (k₁.trans k).mono (by decide)⟩

/-- After the head of a draw. -/
def DHead (p : PP) (mb u : Nat) (s t : State) : Prop :=
  (t.gpr .r12 = p.rp + BitVec.ofNat 64 u ∧ t.gpr .r6 = BitVec.ofNat 64 ((mb + 7) / 8) ∧
    t.gpr .r10 = off p.B (slot (wOf mb) 4) ∧
    t.mem = s.mem.writeW (p.B + BitVec.ofNat 64 152) (BitVec.ofNat 64 (u + (mb + 7) / 8))) ∧
  Keep [.r3, .r6, .r12, .r10] s t

/-- The load, after the head: the witness's octets in array 4. -/
theorem dLoadN_ok {C : Nat} {p : PP} {mb N u : Nat} {s t : State} (h : DPre p mb N u C s) (ht : DHead p mb u s t) :
    WP isa loadN t fun t₂ =>
      (val32 t₂.mem p.B (slot (wOf mb) 4) (2 * wOf mb) = Spec.Rsa.os2ip ((p.r.drop u).take ((mb + 7) / 8)) ∧
        t₂.gpr .r10 = off p.B (slot (wOf mb) 4) ∧
        Frm p.B [(152, 8), (slot (wOf mb) 4, 8 * wOf mb)] s.mem t₂.mem ∧
        t₂.mem.readW (p.B + BitVec.ofNat 64 152) 64 = BitVec.ofNat 64 (u + (mb + 7) / 8)) ∧
      Keep (([.r3, .r6, .r12, .r10] : List Reg) ++ ([.r0, .r14, .r15, .r16, .r17] : List Reg)) s t₂ := by
  obtain ⟨⟨a12, a6, a10, am⟩, k₁⟩ := ht
  have hb1 := h.st.dims.b1
  have hb2 := h.st.dims.b2
  have hn := h.st.dims.n
  have hnw := h.st.scr.nowrap
  have hm1 := h.mb1
  have hm2 := h.mb2
  have hroom := h.room
  have h11 := h.ph.r11
  generalize hwd : wOf mb = w at *
  have hw8 : 8 ≤ w := by simp only [wOf] at hwd; omega_arith
  have hw128 : w ≤ 128 := by simp only [wOf] at hwd; omega_arith
  have hKw : (mb + 7) / 8 ≤ 8 * w := by simp only [wOf] at hwd; omega_arith
  have hZ : slot w 4 + 8 * w ≤ p.Z := by simp only [slot, hdrBytes, PP.Z, PP.L] at hn ⊢; omega_arith
  generalize hKd : (mb + 7) / 8 = K at *
  have hK1 : 1 ≤ K := by omega_arith
  rw [hKd, hwd] at *
  have ho : Outside p.B 152 8 s.mem t.mem := by rw [am]; exact writeW_outside _ _ _ (by omega_arith)
  have hbr : Spec.Rsa.bytesAt t.mem p.rp p.r.length = p.r := by
    rw [bytes_frm (Frm.of_outside (rs := [(152, 8)]) ho (List.mem_singleton_self _)) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; simp only [PP.Z]; omega_arith) h.st.bufs.sepR]
    exact h.st.bufs.bR
  have e : ∀ i, VG.Proof.Mont.off (p.rp + BitVec.ofNat 64 u) i = off p.rp (u + i) := fun i => off_off p.rp u i
  refine WP.mono (loadN_ok (N := p.rp + BitVec.ofNat 64 u) (h.st.scr.congr k₁.wr) a10
    (by rw [a12]; simp only [BitVec.add_zero]) a6 ((k₁.gpr .r11 (by decide)).trans h11) hK1 hKw
    (by omega_arith) (by simp only [slot, hdrBytes]; omega_arith) hZ
    (fun i hi => by
      rw [k₁.rd, k₁.wr, e]
      exact h.st.bufs.rdR _ (by omega_arith))
    (fun i hi x hx => by
      rw [e]
      exact h.st.bufs.sepR _ (by omega_arith) x hx)) fun t₂ ⟨v₂, o₂, k₂⟩ => ?_
  refine ⟨⟨?_, (k₂.gpr .r10 (by decide)).trans a10, ?_, ?_⟩, k₁.trans k₂⟩
  · rw [v₂, ← VG.Proof.Dsa.bytesAt_slice t.mem p.rp (total := p.r.length) (by omega_arith), hbr]
  · exact (Frm.of_outside ho (List.mem_cons_self)).trans
      (Frm.of_outside o₂ (List.mem_cons_of_mem _ List.mem_cons_self))
  · rw [show t₂.mem.readW (p.B + BitVec.ofNat 64 152) 64 = word t₂.mem p.B 152 from rfl,
      Outside.word o₂ (by simp only [slot, hdrBytes]; omega_arith) (by omega_arith), am]
    exact Mem.readW_writeW_self64 _ _ _


/-- The cut: array 4's top word and'ed with `hTop`, so it holds its number
modulo `2^mb`; then `r24 :=` its low word halved, for the scan of the rest
(`r5`, `r6`), and `r10 :=` array 0. -/
theorem dCut_ok {p : PP} {mb : Nat} {s : State} (h : St p s) (hm1 : 511 ≤ mb) (hm2 : mb ≤ p.bits)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * wOf mb)) (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (wOf mb + 2)))
    (htop : word s.mem p.B (8 * hTop) = BitVec.ofNat 64 (2 ^ (mb + 64 - 64 * wOf mb) - 1)) :
    WP isa (.block (([.addi .r10 .r31 hdrBytes] : List Instr) ++ base .r5 4 ++ ([.lsl .r6 .r11 2,
        .add .r5 .r5 .r6, .subi .r5 .r5 8, ldh .r4 hTop, .load .d .r6 .r5 0, .logic .and .r6 .r6 .r4,
        .store .d .r6 .r5 0] : List Instr) ++ base .r5 4 ++ ([.load .d .r24 .r5 0, .lsr .d .r24 .r24 1,
        .addi .r5 .r5 8, .lsr .d .r6 .r11 1, .subi .r6 .r6 1] : List Instr))) s fun t =>
      (wv t.mem p.B (slot (wOf mb) 4) (wOf mb) = wv s.mem p.B (slot (wOf mb) 4) (wOf mb) % 2 ^ mb ∧
        t.gpr .r24 = word t.mem p.B (slot (wOf mb) 4) >>> 1 ∧ t.gpr .r5 = off p.B (slot (wOf mb) 4 + 8) ∧
        t.gpr .r6 = BitVec.ofNat 64 (wOf mb - 1) ∧ t.gpr .r10 = off p.B (slot (wOf mb) 0) ∧
        Frm p.B [(slot (wOf mb) 4, 8 * wOf mb)] s.mem t.mem) ∧ Keep [.r10, .r5, .r6, .r4, .r24] s t := by
  have hb2 := h.dims.b2
  have hn := h.dims.n
  have hnw := h.scr.nowrap
  generalize hwd : wOf mb = w at *
  have hw8 : 8 ≤ w := by simp only [wOf] at hwd; omega_arith
  have hw128 : w ≤ 128 := by simp only [wOf] at hwd; omega_arith
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have hZ : slot w 4 + 8 * w ≤ p.Z := by
    simp only [es, PP.Z] at hn ⊢; simp only [PP.L] at hn; omega_arith
  have hk1 : 1 ≤ mb + 64 - 64 * w := by simp only [wOf] at hwd; omega_arith
  have hk2 : mb + 64 - 64 * w ≤ 64 := by simp only [wOf] at hwd; omega_arith
  have hb : 64 * (w - 1) + (mb + 64 - 64 * w) = mb := by simp only [wOf] at hwd; omega_arith
  generalize hkd : mb + 64 - 64 * w = k at htop hk1 hk2 hb
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r10] (Q := fun u => u.gpr .r10 = off p.B (slot w 0) ∧ u.mem = s.mem)
    (by prun [h.r31, hdrBytes]; simp only [es, Nat.zero_mul, Nat.add_zero]) (by decide))
    fun u ⟨⟨u10, um⟩, ku⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r5) (by decide) (by decide) u10 ((ku.gpr .r29 (by decide)).trans h29) 4)
    fun v ⟨⟨v5, vm⟩, kv⟩ => ?_
  have kuv := ku.trans kv
  rw [WP.block_append_iff]
  have e5 : off p.B (slot w 4 + 8 * w) - BitVec.ofNat 64 8 = off p.B (slot w 4 + 8 * (w - 1)) := by
    simp only [off]; rw [Offset.add_ofNat_sub _ (by omega_arith)]; congr 2; omega_arith
  have sT : InRegions v.wr (off p.B (slot w 4 + 8 * (w - 1))) 8 := by
    rw [kuv.wr]; exact h.scr.st (by omega_arith)
  have lT : InRegions (v.rd ++ v.wr) (off p.B (slot w 4 + 8 * (w - 1))) 8 := by
    rw [kuv.rd, kuv.wr]; exact h.scr.ld (by omega_arith)
  have l192 : InRegions (v.rd ++ v.wr) (p.B + BitVec.ofNat 64 192) 8 := by
    rw [kuv.rd, kuv.wr]; exact h.ld (d := 192) (by decide)
  have tv : s.mem.readW (p.B + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (2 ^ k - 1) := htop
  refine WP.mono (WP.keep [.r4, .r5, .r6] (Q := fun t => t.gpr .r5 = off p.B (slot w 4 + 8 * (w - 1)) ∧
      t.mem = s.mem.writeW (off p.B (slot w 4 + 8 * (w - 1)))
        (s.mem.readW (off p.B (slot w 4 + 8 * (w - 1))) 64 &&& BitVec.ofNat 64 (2 ^ k - 1))) ?_ (by decide))
    fun t₁ ⟨⟨t5₁, tm₁⟩, k₁⟩ => ?_
  · simp only [ldh, hTop]
    prun [v5, (kuv.gpr .r11 (by decide)).trans h11, (kuv.gpr .r31 (by decide)).trans h.r31,
      Proof.MillerRabin.PPC64LE.shl2_ofNat, e5, sT, lT, l192, tv, BitVec.add_zero, vm, um]
  have k₁' := kuv.trans k₁
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r5) (by decide) (by decide) ((k₁.gpr .r10 (by decide)).trans ((kv.gpr .r10 (by decide)).trans u10))
    ((k₁'.gpr .r29 (by decide)).trans h29) 4) fun t₂ ⟨⟨b5, m₂⟩, k₂⟩ => ?_
  have k₂' := k₁'.trans k₂
  have hsh : BitVec.ofNat 64 (2 * w) >>> 1 = BitVec.ofNat 64 w := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega_arith
  have hsub : BitVec.ofNat 64 w - 1#64 = BitVec.ofNat 64 (w - 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith
  have l4 : InRegions (t₂.rd ++ t₂.wr) (off p.B (slot w 4)) 8 := by
    rw [k₂'.rd, k₂'.wr]; exact h.scr.ld (by omega_arith)
  refine WP.mono (WP.keep [.r24, .r5, .r6] (Q := fun t => t.gpr .r24 = t₂.mem.readW (off p.B (slot w 4)) 64 >>> 1 ∧
      t.gpr .r5 = off p.B (slot w 4 + 8) ∧ t.gpr .r6 = BitVec.ofNat 64 (w - 1) ∧ t.mem = t₂.mem) ?_ (by decide))
    fun t ⟨⟨t24, t5, t6, tm⟩, kt⟩ => ?_
  · prun [b5, BitVec.add_zero, l4, (k₂'.gpr .r11 (by decide)).trans h11, hsh, hsub]
  have e0 : t.mem = s.mem.writeW (off p.B (slot w 4 + 8 * (w - 1)))
      (s.mem.readW (off p.B (slot w 4 + 8 * (w - 1))) 64 &&& BitVec.ofNat 64 (2 ^ k - 1)) := by rw [tm, m₂, tm₁]
  refine ⟨⟨?_, by rw [t24, tm, m₂], t5, t6, (kt.gpr .r10 (by decide)).trans ((k₂.gpr .r10 (by decide)).trans
    ((k₁.gpr .r10 (by decide)).trans ((kv.gpr .r10 (by decide)).trans u10))), ?_⟩, (k₂'.trans kt).mono (by decide)⟩
  · rw [← hb]
    refine Proof.Ffdh.ParameterCandidate.wv_cut (by omega_arith) hk2 ?_ fun j hj => ?_
    · simp only [word, off] at e0 ⊢; rw [e0, rw_self]
    · simp only [word, off] at e0 ⊢; rw [e0, rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
  · rw [e0]
    exact frm_writeW (Frm.refl _ _ _) _ ⟨_, List.mem_singleton_self _, by dsimp only; omega_arith,
      by dsimp only; omega_arith⟩ (by omega_arith)

theorem wv_lt_two {m : Mem} {B : Addr} {d w : Nat} (hw : 1 ≤ w) :
    wv m B d w < 2 ↔ word m B d >>> 1 = 0#64 ∧ ∀ j, 1 ≤ j → j < w → word m B (d + 8 * j) = 0#64 := by
  have e := wv_add m B d 1 (w - 1)
  rw [show 1 + (w - 1) = w by omega_arith] at e
  simp only [wv, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.pow_zero, Nat.one_mul, Nat.mul_one] at e
  have hz := wv_eq_zero_iff m B (d + 8) (w - 1)
  have hsh : word m B d >>> 1 = 0#64 ↔ (word m B d).toNat < 2 := by
    rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]; omega_arith
  rw [e, hsh]
  constructor
  · intro hl
    have h0 : wv m B (d + 8) (w - 1) = 0 := by
      by_contra hc; have : 1 ≤ wv m B (d + 8) (w - 1) := Nat.one_le_iff_ne_zero.mpr hc; omega_arith
    refine ⟨by omega_arith, fun j hj1 hj2 => ?_⟩
    have := hz.mp h0 (j - 1) (by omega_arith)
    rwa [show d + 8 + 8 * (j - 1) = d + 8 * j by omega_arith] at this
  · rintro ⟨hl, hr⟩
    have h0 : wv m B (d + 8) (w - 1) = 0 := hz.mpr fun q hq => by
      rw [show d + 8 + 8 * q = d + 8 * (q + 1) by omega_arith]; exact hr _ (by omega_arith) (by omega_arith)
    omega_arith

/-- The scan: `r24 = 0` exactly when the number in array 4 is below 2. -/
theorem dScan_ok {s : State} {B : Addr} {Z d w : Nat} (hs : Scr s B Z) (h5 : s.gpr .r5 = off B (d + 8))
    (h6 : s.gpr .r6 = BitVec.ofNat 64 (w - 1)) (h24 : s.gpr .r24 = word s.mem B d >>> 1) (hw : 2 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : d + 8 * w ≤ Z) :
    WP isa (countLoop .r6 [.load .d .r3 .r5 0, .logic .or .r24 .r24 .r3, .addi .r5 .r5 8]) s fun t =>
      ((t.gpr .r24 = 0#64 ↔ wv s.mem B d w < 2) ∧ t.mem = s.mem) ∧ Keep [.r3, .r5, .r6, .r24] s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    (t.gpr .r5 = off B (d + 8 * (i + 1)) ∧
      (t.gpr .r24 = 0#64 ↔ word s.mem B d >>> 1 = 0#64 ∧ ∀ j, 1 ≤ j → j ≤ i → word s.mem B (d + 8 * j) = 0#64) ∧
      t.mem = s.mem) ∧ Keep [.r3, .r5, .r6, .r24] s t
  refine WP.mono (wp_countdown (cnt := .r6) (N := w - 1) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨⟨t5, t24, tm⟩, kt⟩ _ => ?_)
    ⟨⟨by rw [h5], by rw [h24]; exact ⟨fun h => ⟨h, fun j h1 h2 => absurd h2 (by omega_arith)⟩, fun h => h.1⟩, rfl⟩,
      Keep.refl _ _⟩ h6) fun t ⟨⟨_, t24, tm⟩, kt⟩ => ⟨⟨?_, tm⟩, kt⟩
  · have l : InRegions (t.rd ++ t.wr) (off B (d + 8 * (i + 1))) 8 := by
      rw [kt.rd, kt.wr]; exact hs.ld (by omega_arith)
    have rv : t.mem.readW (off B (d + 8 * (i + 1))) 64 = word s.mem B (d + 8 * (i + 1)) := by rw [tm]
    refine WP.mono (WP.keep [.r3, .r5, .r6, .r24] (Q := fun u =>
        u.gpr .r5 = off B (d + 8 * (i + 1 + 1)) ∧
        u.gpr .r24 = t.gpr .r24 ||| word s.mem B (d + 8 * (i + 1)) ∧ u.mem = t.mem ∧
        u.gpr .r6 = t.gpr .r6 - BitVec.ofNat 64 1) ?_ (by decide))
      fun u ⟨⟨u5, u24, um, u6⟩, ku⟩ => ⟨⟨⟨u5, ?_, um.trans tm⟩, (kt.trans ku).mono (by decide)⟩, u6⟩
    · prun [t5, BitVec.add_zero, l, rv]
      rw [show d + 8 * (i + 1) + 8 = d + 8 * (i + 1 + 1) by omega_arith]
    · rw [u24, BitVec.or_eq_zero_iff, t24]
      constructor
      · rintro ⟨⟨a, b⟩, c⟩
        exact ⟨a, fun j h1 h2 => by
          rcases Nat.lt_or_ge j (i + 1) with hj | hj
          · exact b j h1 (by omega_arith)
          · rw [show j = i + 1 by omega_arith]; exact c⟩
      · rintro ⟨a, b⟩
        exact ⟨⟨a, fun j h1 h2 => b j h1 (by omega_arith)⟩, b _ (by omega_arith) (Nat.le_refl _)⟩
  · rw [t24, wv_lt_two (by omega_arith)]
    exact ⟨fun ⟨a, b⟩ => ⟨a, fun j h1 h2 => b j h1 (by omega_arith)⟩, fun ⟨a, b⟩ => ⟨a, fun j h1 h2 => b j h1 (by omega_arith)⟩⟩

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end

/-! ### `Ffdh.PPC64LE.ParameterCandidate.Keep`, which this module and modules that import it used -/

section

/-! ### `Ffdh.PPC64LE.ParameterCandidate.Round`, which this module and modules that import it used -/

section

/-!
# An FFDH parameter candidate on PPC64LE: a witness's round

`roundCount_ok`: the round of a witness `a` (`roundCall_ok`), then `hStat`
2 if it failed, else the passing witnesses `hIdx` counted and `hStat` 1 once
there are `hChecks` of them, 4 before.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (arr RoundImpl)
open VG.Proof.Mont (word off)

theorem stat_eq {i K : Nat} (hi : i < 2 ^ 62) (hK : K < 2 ^ 62) :
    BitVec.ofNat 64 4 - (BitVec.ofNat 64 K - BitVec.ofNat 64 (i + 1) - BitVec.ofNat 64 1) >>> 63 * BitVec.ofNat 64 3 =
      BitVec.ofNat 64 (if i + 1 < K then 4 else 1) := by
  have e1 : BitVec.ofNat 64 K - BitVec.ofNat 64 (i + 1) - BitVec.ofNat 64 1 =
      BitVec.ofNat 64 (if i + 1 < K then K - (i + 2) else 2 ^ 64 - (i + 2 - K)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    split <;> omega_arith
  have e2 : ∀ n, n < 2 ^ 64 → BitVec.ofNat 64 n >>> 63 = BitVec.ofNat 64 (n / 2 ^ 63) := fun n hn => by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega_arith)]
  rw [e1]
  split
  · rw [e2 _ (by omega_arith), Nat.div_eq_of_lt (by omega_arith)]; rfl
  · rw [e2 _ (by omega_arith), show (2 ^ 64 - (i + 2 - K)) / 2 ^ 63 = 1 by omega_arith]; rfl

/-- What `round` leaves: the round's state `u` (`RcPost`), and the status
and count stored over it. -/
def RdPost (s : State) (B : Addr) (L w c a i K : Nat) (t : State) : Prop :=
  ∃ u, RcPost s B L w c a u ∧ (t.mem = if Proof.MillerRabin.Round.round c a then
      (u.mem.writeW (B + BitVec.ofNat 64 176) (BitVec.ofNat 64 (i + 1))).writeW (B + BitVec.ofNat 64 160)
        (BitVec.ofNat 64 (if i + 1 < K then 4 else 1))
    else u.mem.writeW (B + BitVec.ofNat 64 160) (BitVec.ofNat 64 2)) ∧ Keep [.r3, .r4, .r5] u t

theorem roundCount_ok (R : RoundImpl) {s : State} {B : Addr} {L w c a i K : Nat} (h : Prep s B L w c)
    (ha : arr s.mem B w 4 = a) (hac : a < c)
    (hsp : 176 ≤ s.sp.toNat) (hstk : (below s.sp 176).Disjoint ⟨B, 8 * L⟩)
    (hI : word s.mem B 176 = BitVec.ofNat 64 i) (hK : word s.mem B 168 = BitVec.ofNat 64 K)
    (hi : i < 2 ^ 62) (hK' : K < 2 ^ 62) :
    WP isa (round R.name R.code) s (RdPost s B L w c a i K) := by
  have hnw := h.env.hs.nowrap
  have hZ := h.env.hZ
  have es : ∀ j, VG.Proof.Bignum.slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have hZ' : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := by rw [← es]; exact hZ
  unfold round
  refine WP.seq (WP.mono (roundCall_ok R h ha hac hsp hstk) fun u hu => ?_)
  have hs : Scr u B (8 * L) := hu.prep.env.hs
  have h31 : u.gpr .r31 = B := hu.prep.env.h31
  have l160 : InRegions u.wr (B + BitVec.ofNat 64 160) 8 := hs.st (d := 160) (by omega_arith)
  refine WP.ite (decide ((if Proof.MillerRabin.Round.round c a then 1 else 0) = 0))
    (eval_zero_ofNat u .r3 (by split <;> decide) hu.r3) (fun hb => ?_) (fun hb => ?_)
  · have hf : Proof.MillerRabin.Round.round c a = false := by
      cases hr : Proof.MillerRabin.Round.round c a <;> simp_all
    refine WP.mono (WP.keep [.r3] (Q := fun t => t.mem = u.mem.writeW (B + BitVec.ofNat 64 160)
      (BitVec.ofNat 64 2)) ?_ (by decide)) fun t ⟨tm, kt⟩ => ⟨u, hu, by rw [tm, hf]; rfl, kt.mono (by decide)⟩
    simp only [sth, hStat]
    prun [h31, l160]
  · have ht : Proof.MillerRabin.Round.round c a = true := by
      cases hr : Proof.MillerRabin.Round.round c a <;> simp_all
    have rI : u.mem.readW (B + BitVec.ofNat 64 176) 64 = BitVec.ofNat 64 i :=
      (keeps_word hu.keeps (d := 176) (by omega_arith) (by kept_tac)).trans hI
    have rK : u.mem.readW (B + BitVec.ofNat 64 168) 64 = BitVec.ofNat 64 K :=
      (keeps_word hu.keeps (d := 168) (by omega_arith) (by kept_tac)).trans hK
    have l176 : InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 176) 8 := hs.ld (d := 176) (by omega_arith)
    have l168 : InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 168) 8 := hs.ld (d := 168) (by omega_arith)
    have s176 : InRegions u.wr (B + BitVec.ofNat 64 176) 8 := hs.st (d := 176) (by omega_arith)
    refine WP.mono (WP.keep [.r3, .r4, .r5] (Q := fun t => t.mem =
      (u.mem.writeW (B + BitVec.ofNat 64 176) (BitVec.ofNat 64 (i + 1))).writeW (B + BitVec.ofNat 64 160)
        (BitVec.ofNat 64 (if i + 1 < K then 4 else 1))) ?_ (by decide))
      fun t ⟨tm, kt⟩ => ⟨u, hu, by rw [tm, ht]; rfl, kt⟩
    simp only [ldh, sth, hStat, hIdx, hChecks]
    prun [h31, l160, l176, l168, s176, rI, rK, ← BitVec.ofNat_add, stat_eq hi hK']

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end

/-! ### `Ffdh.PPC64LE.ParameterCandidate.StCall`, which this module and modules that import it used -/

section

/-!
# An FFDH parameter candidate on PPC64LE: the invariant across a round

`St.call`: `St` survives the shared round, which changes the working space
only where its `Keeps` allows (none of the argument words) and memory
outside it only on the stack below `sp`, apart from the tape.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search

/-- A header word the round keeps. -/
theorem keeps_hdr {m m' : Mem} {B : Addr} {n w i : Nat}
    (h : Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.compact B n w m m') (hi : i < 32)
    (hk : i ≠ 1 ∧ i ≠ 23 ∧ i ≠ 26 ∧ i ≠ 29 ∧ i ≠ 30) (hn : 256 ≤ 8 * n) :
    word m' B (8 * i) = word m B (8 * i) :=
  keeps_word h (by omega_arith) fun j h1 h2 => by
    simp only [Kept, slot, hdrBytes, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros <;> omega_arith

theorem St.call {p : PP} {s t : State} {w : Nat} (h : St p s)
    (hk : Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.compact p.B p.n w s.mem t.mem)
    (hf : Frame [⟨p.B, p.Z⟩, below p.sp 176] s.mem t.mem) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hsp : t.sp = s.sp) (h31 : t.gpr .r31 = p.B) (hw : slot w 28 + saveBytes ≤ p.Z) (h2 : t.gpr .r2 = s.gpr .r2) : St p t := by
  have hn := h.dims.n
  have e : ∀ {i : Nat}, i < 32 → i ≠ 1 ∧ i ≠ 23 ∧ i ≠ 26 ∧ i ≠ 29 ∧ i ≠ 30 →
      word t.mem p.B (8 * i) = word s.mem p.B (8 * i) := fun hi hk' =>
    keeps_hdr hk hi hk' (by simp only [PP.L] at hn; omega_arith)
  have ha := h.args
  refine ⟨h.scr.congr hwr, h31, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, h.bufs.sepR, ?_, ?_, h.bufs.scrO.congr hwr,
    h.bufs.sepO, h.bufs.scrU.congr hwr, h.bufs.sepU, h.bufs.stkR, h.bufs.stkO, h.bufs.stkU, h.bufs.dOU⟩, h.dims,
    by rw [hwr]; exact h.ws, hsp.trans h.sp, h.stk, h.stkB, fun i hi => ?_, h2.trans h.r2⟩
  · rw [e (by decide) (by decide)]; exact ha.wsLen
  · rw [e (by decide) (by decide)]; exact ha.out
  · rw [e (by decide) (by decide)]; exact ha.len
  · rw [e (by decide) (by decide)]; exact ha.usedP
  · rw [e (by decide) (by decide)]; exact ha.bits
  · rw [e (by decide) (by decide)]; exact ha.gen
  · rw [e (by decide) (by decide)]; exact ha.rand
  · rw [e (by decide) (by decide)]; exact ha.rlen
  · rw [hrd, hwr]; exact h.bufs.rdR
  · refine Eq.trans ?_ h.bufs.bR
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => hf _ fun r hr => ?_
    have hi' : i < p.r.length := List.mem_range.mp hi
    have hc : (⟨p.rp, p.r.length⟩ : Region).Contains (p.rp + BitVec.ofNat 64 i) 1 := by
      have := h.dims.rl
      have e0 := VG.Proof.Mont.ofs_off0 p.rp (d := i) (by omega_arith)
      simp only [VG.Proof.Mont.ofs, VG.Proof.Mont.off] at e0
      simp only [Region.Contains]; omega_arith
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · intro hc'
      have := h.bufs.sepR i hi' (p.rp + BitVec.ofNat 64 i) (by
        simp only [Region.Contains] at hc'; simp only [ofs]; omega_arith)
      exact this rfl
    · exact fun hc' => h.bufs.stkR _ hc' hc
  · refine Eq.trans ?_ h.bufs.bO
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => hf _ fun r hr => ?_
    have hi' : i < p.L := List.mem_range.mp hi
    have hnw := h.bufs.scrO.nowrap
    have ho : ofs p.op (p.op + BitVec.ofNat 64 i) = i := by simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by omega_arith)]
    have hc : (⟨p.op, p.L⟩ : Region).Contains (p.op + BitVec.ofNat 64 i) 1 := by
      simp only [Region.Contains]; simp only [ofs] at ho; omega_arith
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · intro hc'
      have := h.bufs.sepO _ (by rw [ho]; exact hi')
      simp only [Region.Contains, ofs] at hc' this; omega_arith
    · exact fun hc' => h.bufs.stkO _ hc' hc

  · have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
    have := es 2; have := es 3; have := es 5; have := es 6; have := es 8; have := es 11; have := es 27
    have := es 28
    simp only [PP.Z, saveBytes] at hw
    refine (keeps_word hk (by simp only [saveBytes]; omega_arith) fun j h1 h2 => ?_).trans (h.save i hi)
    simp only [Kept, saveBytes, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h1 ⊢
    and_intros <;> omega_arith

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end

/-!
# An FFDH parameter candidate on PPC64LE: the tests' state

`MSt`: between the witnesses of a modulus `N` of `mb` bits, the candidate's
invariant (`St`), the modulus's header (`Ph`) and its Montgomery constants
(`Prep`). `MSt.frm`: it survives a change of `Free` ranges (the draw's
header words and working arrays); `MSt.call`: and the round.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search

structure MSt (p : PP) (mb N C : Nat) (s : State) : Prop where
  st : St p s
  ph : Ph p mb C s
  prep : Prep s p.B p.n (wOf mb) N
  mb1 : 511 ≤ mb
  mb2 : mb ≤ p.bits

/-- The words `Ph` and `Prep` read. -/
def Read (w d : Nat) : Prop :=
  d = 0 ∨ d = 48 ∨ d = 56 ∨ d = 168 ∨ d = 192 ∨ d = 216 ∨ d = 224 ∨ d = 248 ∨ (∃ j < 8, d = 8 * (8 + j)) ∨
    d = slot w 0 ∨ d = slot w 27 + 8 * w

theorem Read.arr {w j : Nat} (hj : j < 8) : Read w (8 * (8 + j)) := by
  unfold Read; right; right; right; right; right; right; right; right; left; exact ⟨j, hj, rfl⟩

theorem Ph.keep {C : Nat} {p : PP} {mb : Nat} {s t : State} (h : Ph p mb C s)
    (r10 : t.gpr .r10 = s.gpr .r10) (r11 : t.gpr .r11 = s.gpr .r11) (r29 : t.gpr .r29 = s.gpr .r29)
    (hw : ∀ d, Read (wOf mb) d → word t.mem p.B d = word s.mem p.B d) : Ph p mb C t :=
  ⟨r10.trans h.r10, r11.trans h.r11, r29.trans h.r29, (hw 248 (by simp [Read])).trans h.mbW,
    (hw 216 (by simp [Read])).trans h.kW, (hw 48 (by simp [Read])).trans h.wW,
    (hw 224 (by simp [Read])).trans h.strideW,
    fun j hj => (hw _ (Read.arr hj)).trans (h.arrW j hj),
    (hw 168 (by simp [Read])).trans h.checksW, h.k1, h.k2, (hw 192 (by simp [Read])).trans h.topW⟩

/-- A range the draw or the round's bookkeeping changes: the header words
`hUsed`, `hStat`, `hIdx` and `hBad`, or arrays 2 to 6. -/
def Free (w : Nat) (r : Nat × Nat) : Prop :=
  ((r.1 = 152 ∨ r.1 = 160 ∨ r.1 = 176 ∨ r.1 = 200) ∧ r.2 = 8) ∨
    (∃ j, 2 ≤ j ∧ j ≤ 6 ∧ r.1 = slot w j ∧ r.2 ≤ 8 * (w + 2))

theorem Free.word {w d : Nat} {r : Nat × Nat} (h : Free w r) (hd : Read w d) :
    d + 8 ≤ r.1 ∨ r.1 + r.2 ≤ d := by
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  unfold Read at hd
  rcases h with ⟨h1, h2⟩ | ⟨j, hj1, hj2, h1, h2⟩
  · rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨k, hk, rfl⟩ | rfl | rfl <;>
      (try rw [es]) <;> omega_arith
  · rw [h1]
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨k, hk, rfl⟩ | rfl | rfl <;>
      simp only [es] <;> (try have := Nat.mul_le_mul_right (8 * (w + 2)) hj2) <;>
      (try have := Nat.mul_le_mul_right (8 * (w + 2)) hj1) <;> omega_arith

theorem Free.arr {w j : Nat} {r : Nat × Nat} (h : Free w r) (hj : j = 0 ∨ j = 1 ∨ j = 9 ∨ j = 10 ∨ j = 27) :
    slot w j + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := by
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  rcases h with ⟨h1, h2⟩ | ⟨k, hk1, hk2, h1, h2⟩
  · right; rcases hj with rfl | rfl | rfl | rfl | rfl <;> rw [es] <;> omega_arith
  · rw [h1]
    have a := Nat.mul_le_mul_right (8 * (w + 2)) hk2
    have b := Nat.mul_le_mul_right (8 * (w + 2)) hk1
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp only [es] <;> omega_arith

theorem MSt.w {C : Nat} {p : PP} {mb N : Nat} {s : State} (h : MSt p mb N C s) :
    2 ≤ wOf mb ∧ wOf mb ≤ 128 ∧ slot (wOf mb) 28 + saveBytes ≤ p.Z := by
  have hn := h.st.dims.n
  have hb := h.st.dims.b2
  have := h.mb1; have := h.mb2
  simp only [wOf, slot, hdrBytes, saveBytes, PP.Z, PP.L] at hn ⊢
  omega_arith

theorem Free.mut {C : Nat} {p : PP} {mb N : Nat} {s : State} (h : MSt p mb N C s) {r : Nat × Nat} (hr : Free (wOf mb) r) :
    InMut p.n r := by
  obtain ⟨hw2, -, hZ⟩ := h.w
  have es : ∀ j, slot (wOf mb) j = 256 + j * (8 * (wOf mb + 2)) := fun _ => rfl
  rcases hr with ⟨h1, h2⟩ | ⟨j, hj1, hj2, h1, h2⟩
  · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), ?_, ?_⟩ <;> dsimp only <;>
      omega_arith
  · refine InMut.arrays (by rw [h1, es]; omega_arith) ?_
    simp only [es, PP.Z] at hZ h1 ⊢
    have := Nat.mul_le_mul_right (8 * (wOf mb + 2)) hj2
    rw [h1]; omega_arith

theorem Read.le {w d : Nat} (hd : Read w d) : d + 8 ≤ slot w 28 := by
  have e0 : slot w 0 = 256 := by simp [slot, hdrBytes]
  have e27 : slot w 27 = 256 + 27 * (8 * (w + 2)) := rfl
  have e28 : slot w 28 = 256 + 28 * (8 * (w + 2)) := rfl
  unfold Read at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨k, hk, rfl⟩ | rfl | rfl <;> omega_arith

theorem MSt.frm {C : Nat} {p : PP} {mb N : Nat} {s t : State} (h : MSt p mb N C s) {rs : List (Nat × Nat)}
    (hf : Frm p.B rs s.mem t.mem) (hr : ∀ r ∈ rs, Free (wOf mb) r) {regs : List Reg} (k : Keep regs s t)
    (h31 : Reg.r31 ∉ regs) (r10 : t.gpr .r10 = s.gpr .r10) (r11 : t.gpr .r11 = s.gpr .r11)
    (r29 : t.gpr .r29 = s.gpr .r29) (h2 : Reg.r2 ∉ regs := by decide) : MSt p mb N C t := by
  obtain ⟨hw2, hw128, hZ⟩ := h.w
  have hnw := h.st.scr.nowrap
  have es : ∀ j, slot (wOf mb) j = 256 + j * (8 * (wOf mb + 2)) := fun _ => rfl
  have hZ' : 256 + 28 * (8 * (wOf mb + 2)) + saveBytes ≤ p.Z := by rw [← es]; exact hZ
  have hw : ∀ d, Read (wOf mb) d → word t.mem p.B d = word s.mem p.B d := fun d hd =>
    hf.word_eq (fun r hr' => (hr r hr').word hd) (by have := hd.le; omega_arith)
  refine ⟨h.st.step (Frm.toMut hf fun r hr' => Free.mut h (hr r hr')) k h31 h2,
    h.ph.keep r10 r11 r29 hw, ?_, h.mb1, h.mb2⟩
  refine h.prep.keep ⟨h.prep.env.hs.congr k.wr, r10.trans h.prep.env.h10,
    r29.trans h.prep.env.h29, r11.trans h.prep.env.h11,
    (k.gpr _ h31).trans h.prep.env.h31, h.prep.env.hw, h.prep.env.hw', h.prep.env.hZ⟩
    (fun d hd => hw d (by
      rcases hd with rfl | rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl | rfl
      · unfold Read; simp
      · unfold Read; simp
      · unfold Read; simp
      · unfold Read; simp
      · exact Read.arr hj
      · unfold Read; simp
      · unfold Read; simp)) (fun j hj => ?_)
  rw [Pre.val32_eq_wv, Pre.val32_eq_wv]
  exact hf.wv_eq (fun r hr' => (hr r hr').arr hj) (by
    have := es 0; have := es 1; have := es 9; have := es 10; have := es 27
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp only [saveBytes] at hZ' <;> omega_arith)

theorem Read.kept {w d : Nat} (hd : Read w d) : ∀ i, d ≤ i → i < d + 8 → Kept w i := by
  intro i h1 h2
  have e0 : slot w 0 = 256 := by simp [slot, hdrBytes]
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have := es 2; have := es 3; have := es 5; have := es 6; have := es 8; have := es 11; have := es 27
  unfold Read at hd
  refine ⟨fun k hk => ?_, fun j hj => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨k, hk, rfl⟩ | rfl | rfl <;> omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨k, hk, rfl⟩ | rfl | rfl <;> omega_arith
  · rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨k, hk, rfl⟩ | rfl | rfl <;> omega_arith

/-- `MSt` survives a witness's round. -/
theorem MSt.round {C : Nat} {p : PP} {mb N a i K : Nat} {s t : State} (h : MSt p mb N C s)
    (hR : RdPost s p.B p.n (wOf mb) N a i K t) : MSt p mb N C t := by
  obtain ⟨u, hu, tm, kt⟩ := hR
  obtain ⟨hw2, -, hZ⟩ := h.w
  have stu : St p u := h.st.call hu.keeps (by have := hu.frame; rw [h.st.sp] at this; exact this) hu.rd hu.wr
    hu.sp hu.prep.env.h31 hZ (hu.cs .r2 (by decide) (by decide))
  have phu : Ph p mb C u := h.ph.keep (hu.prep.env.h10.trans h.ph.r10.symm) (hu.prep.env.h11.trans h.ph.r11.symm)
    (hu.prep.env.h29.trans h.ph.r29.symm) fun d hd => keeps_word hu.keeps (by
      have := hd.le; simp only [PP.Z, saveBytes] at hZ; omega_arith) hd.kept
  have mu : MSt p mb N C u := ⟨stu, phu, hu.prep, h.mb1, h.mb2⟩
  have hf : Frm p.B [(176, 8), (160, 8)] u.mem t.mem := by
    rw [tm]
    split
    · exact frm_writeW (a := 160) (frm_writeW (a := 176) (Frm.refl _ _ _) _
        ⟨_, List.mem_cons_self, by decide, by decide⟩ (by decide)) _
        ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by decide, by decide⟩ (by decide)
    · exact frm_writeW (a := 160) (Frm.refl _ _ _) _
        ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by decide, by decide⟩ (by decide)
  exact mu.frm hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Or.inl ⟨by simp, rfl⟩) kt (by decide) (kt.gpr _ (by decide))
    (kt.gpr _ (by decide)) (kt.gpr _ (by decide))

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end

/-! ### `Ffdh.PPC64LE.ParameterCandidate.DrawRange`, which only this module used -/

section

/-!
# An FFDH parameter candidate on PPC64LE: a witness's upper bound

`dRange_ok`: with the witness `x` in array 4 and the odd modulus `N` in
array 0, `x | 1` into array 3 (its word `w` zeroed) and `x | 1 − N` into
array 6: `r20`, the borrow, is nonzero exactly when `x < N − 1`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Impl.Bignum.PPC64LE.PublicChecked (base)
open VG.Impl.Bignum.PPC64LE.Precompute (copyWords)
open VG.Proof.Mont (val32 w32)

/-- The number with its low word or'ed with 1. -/
theorem wv_or1 {m m' : Mem} {B : Addr} {d w : Nat} (hw : 1 ≤ w)
    (h0 : word m' B d = word m B d ||| 1#64) (hr : ∀ j, 1 ≤ j → j < w → word m' B (d + 8 * j) = word m B (d + 8 * j)) :
    wv m' B d w = wv m B d w + (1 - wv m B d w % 2) := by
  obtain e := fun mm => wv_add mm B d 1 (w - 1)
  rw [show 1 + (w - 1) = w by omega_arith] at e
  rw [e m, e m']
  simp only [wv, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.pow_zero, Nat.one_mul, Nat.mul_one]
  obtain hrest : wv m' B (d + 8) (w - 1) = wv m B (d + 8) (w - 1) := wv_congr fun i hi => by
    rw [show d + 8 + 8 * i = d + 8 * (i + 1) by omega_arith]; exact hr _ (by omega_arith) (by omega_arith)
  rw [hrest, h0]
  obtain hor : (word m B d ||| 1#64).toNat = (word m B d).toNat + (1 - (word m B d).toNat % 2) := by
    rw [BitVec.toNat_or, show (1#64).toNat = 1 from rfl, VG.Proof.Rsa.KeyBits32.or_one]
    omega_arith
  rw [hor]
  have : (2 ^ 64 * wv m B (d + 8) (w - 1)) % 2 = 0 := by
    rw [Nat.mul_mod, show 2 ^ 64 % 2 = 0 from rfl, Nat.zero_mul, Nat.zero_mod]
  omega_arith

/-- The registers `dRange` writes. -/
def drRegs : List Reg := [.r14, .r15, .r0, .r17, .r5, .r3, .r4, .r6, .r8, .r9, .r16, .r20]

theorem dRange_ok {s : State} {B : Addr} {Z w N x : Nat} (hs : Scr s B Z) (h10 : s.gpr .r10 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hw : 2 ≤ w) (hw' : w ≤ 128) (hZ : slot w 7 ≤ Z) (hN : wv s.mem B (slot w 0) w = N) (hodd : N % 2 = 1)
    (hx : wv s.mem B (slot w 4) w = x) :
    WP isa (.seq (.block (base .r14 3 ++ base .r15 4)) (.seq copyWords (.seq (.block (base .r5 3 ++
        ([.load .d .r3 .r5 0, .li .r4 1, .logic .or .r3 .r3 .r4, .store .d .r3 .r5 0, .lsl .r6 .r11 2,
          .add .r5 .r5 .r6, .li .r0 0, .store .d .r0 .r5 0] : List Instr) ++ base .r8 3 ++ base .r9 6)) subMod)))
      s fun t =>
      ((t.gpr .r20 = 0#64 ↔ ¬ x < N - 1) ∧
        Frm B [(slot w 3, 8 * (w + 2)), (slot w 6, 8 * (w + 2))] s.mem t.mem) ∧ Keep drRegs s t := by
  have hnw := hs.nowrap
  obtain es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  obtain hZ' : 256 + 7 * (8 * (w + 2)) ≤ Z := by rw [← es]; exact hZ
  -- Array 4 copied to array 3.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) h10 h29 3) fun s₁ ⟨⟨a14, m₁⟩, k₁⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .r15) (by decide) (by decide) ((k₁.gpr .r10 (by decide)).trans h10)
    ((k₁.gpr .r29 (by decide)).trans h29) 4) fun s₂ ⟨⟨a15, m₂⟩, k₂⟩ => ?_
  obtain k12 := k₁.trans k₂
  refine WP.seq (WP.mono (copyWithin_ok (hs.congr k12.wr) a15 ((k₂.gpr .r14 (by decide)).trans a14)
    ((k12.gpr .r11 (by decide)).trans h11) (by omega_arith) (by omega_arith) (by simp only [es]; omega_arith)
    (by simp only [es]; omega_arith) (by simp only [es]; omega_arith)) fun s₃ ⟨⟨_, cp, o₃⟩, k₃⟩ => ?_)
  obtain k13 := k12.trans k₃
  rw [m₂, m₁] at cp o₃
  -- Its low bit set and its word `w` zeroed.
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  obtain h10₃ : s₃.gpr .r10 = off B (slot w 0) := (k13.gpr .r10 (by decide)).trans h10
  obtain h29₃ : s₃.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)) := (k13.gpr .r29 (by decide)).trans h29
  refine WP.mono (Pub.base_ok (rd := .r5) (by decide) (by decide) h10₃ h29₃ 3) fun s₄ ⟨⟨a5, m₄⟩, k₄⟩ => ?_
  obtain k14 := k13.trans k₄
  obtain hs₄ : Scr s₄ B Z := hs.congr k14.wr
  obtain l3 : InRegions (s₄.rd ++ s₄.wr) (off B (slot w 3)) 8 := hs₄.ld (by simp only [es]; omega_arith)
  obtain st3 : InRegions s₄.wr (off B (slot w 3)) 8 := hs₄.st (by simp only [es]; omega_arith)
  obtain st3w : InRegions s₄.wr (off B (slot w 3 + 8 * w)) 8 := hs₄.st (by simp only [es]; omega_arith)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r3, .r4, .r6, .r5, .r0] (Q := fun u => u.mem =
      (s₄.mem.writeW (off B (slot w 3)) (s₄.mem.readW (off B (slot w 3)) 64 ||| 1#64)).writeW
        (off B (slot w 3 + 8 * w)) 0#64) ?_ (by decide)) fun s₅ ⟨m₅, k₅⟩ => ?_
  · prun [a5, BitVec.add_zero, l3, st3, st3w, (k14.gpr .r11 (by decide)).trans h11,
      Proof.MillerRabin.PPC64LE.shl2_ofNat]
  obtain k15 := k14.trans k₅
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r8) (by decide) (by decide) ((k₅.gpr .r10 (by decide)).trans
    ((k₄.gpr .r10 (by decide)).trans h10₃)) ((k15.gpr .r29 (by decide)).trans h29) 3) fun s₆ ⟨⟨a8, m₆⟩, k₆⟩ => ?_
  obtain k16 := k15.trans k₆
  refine WP.mono (Pub.base_ok (rd := .r9) (by decide) (by decide) ((k16.gpr .r10 (by decide)).trans h10)
    ((k16.gpr .r29 (by decide)).trans h29) 6) fun s₇ ⟨⟨a9, m₇⟩, k₇⟩ => ?_
  obtain k17 := k16.trans k₇
  -- `x | 1 − N`.
  refine WP.mono (subMod_ok (hs.congr k17.wr) ((k₇.gpr .r8 (by decide)).trans a8) a9
    ((k17.gpr .r10 (by decide)).trans h10) ((k17.gpr .r11 (by decide)).trans h11) (by omega_arith) (by omega_arith)
    (by simp only [es]; omega_arith) (by simp only [es]; omega_arith) (by simp only [es]; omega_arith) (by simp only [es]; omega_arith)
    (by simp only [es]; omega_arith)) fun t ⟨⟨c, hc, hsub, h20⟩, o₈, k₈⟩ => ?_
  obtain m37 : s₇.mem = (s₃.mem.writeW (off B (slot w 3)) (s₃.mem.readW (off B (slot w 3)) 64 ||| 1#64)).writeW
      (off B (slot w 3 + 8 * w)) 0#64 := by rw [m₇, m₆, m₅, m₄]
  -- What changed before `subMod`: array 3.
  obtain f₇ : Frm B [(slot w 3, 8 * (w + 2))] s.mem s₇.mem := by
    rw [m37]
    refine frm_writeW (a := slot w 3 + 8 * w) (frm_writeW (a := slot w 3) (Frm.of_outside (o₃.mono (o' := slot w 3) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_arith))
      (List.mem_singleton_self _)) _ ⟨_, List.mem_singleton_self _, by dsimp only; omega_arith,
        by dsimp only; omega_arith⟩ (by simp only [es]; omega_arith)) _
      ⟨_, List.mem_singleton_self _, by dsimp only; omega_arith, by dsimp only; omega_arith⟩ (by simp only [es]; omega_arith)
  obtain n₇ : val32 s₇.mem B (slot w 0) (2 * w) = N := by
    rw [Pre.val32_eq_wv, f₇.wv_eq (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; dsimp only; simp only [es]; omega_arith) (by simp only [es]; omega_arith), hN]
  obtain x₃ : wv s₃.mem B (slot w 3) w = x := by
    rw [← hx]; exact wv_shift fun i hi => cp i hi
  obtain a₇ : val32 s₇.mem B (slot w 3) (2 * w) = x + (1 - x % 2) := by
    rw [Pre.val32_eq_wv, ← x₃]
    refine wv_or1 (by omega_arith) ?_ fun j h1 h2 => ?_
    · simp only [word, off] at m37 ⊢
      rw [m37, rw_off _ _ _ (by omega_arith) (by simp only [es]; omega_arith) (by simp only [es]; omega_arith), rw_self]
    · simp only [word, off] at m37 ⊢
      rw [m37, rw_off _ _ _ (by omega_arith) (by simp only [es]; omega_arith) (by simp only [es]; omega_arith),
        rw_off _ _ _ (by omega_arith) (by simp only [es]; omega_arith) (by simp only [es]; omega_arith)]
  obtain z₇ : w32 s₇.mem B (slot w 3 + 4 * (2 * w)) = 0 := by
    obtain e := VG.Proof.Mont.word_eq_w32 s₇.mem B (slot w 3 + 8 * w)
    obtain e0 : (VG.Proof.Mont.word s₇.mem B (slot w 3 + 8 * w)).toNat = 0 := by
      simp only [VG.Proof.Mont.word, VG.Proof.Mont.off] at m37 ⊢; rw [m37, rw_self]; rfl
    rw [show slot w 3 + 4 * (2 * w) = slot w 3 + 8 * w by omega_arith]; omega_arith
  rw [n₇, a₇, show 32 * (2 * w) = 64 * w by omega_arith] at hsub
  rw [z₇] at h20
  obtain hT : val32 t.mem B (slot w 6) (2 * w) < 2 ^ (64 * w) := by rw [Pre.val32_eq_wv]; exact wv_lt _ _ _ _
  obtain hX : x < 2 ^ (64 * w) := by rw [← hx]; exact wv_lt _ _ _ _
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [h20]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl
    · simp only [Nat.lt_irrefl, ↓reduceIte]
      constructor
      · intro _ hlt; omega_arith
      · intro _; rfl
    · simp only [Nat.zero_lt_one, ↓reduceIte]
      constructor
      · intro h; exact absurd h (by decide)
      · intro hn; exfalso; apply hn; omega_arith
  · exact (f₇.mono fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self).trans
      (Frm.of_outside (o₈.mono (o' := slot w 6) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_arith)) (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact ((k17.trans k₈).mono (by decide))

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end


/-!
# An FFDH parameter candidate on PPC64LE: a draw

`draw_ok`: the witness `a = wA mb r u` drawn at `used = u`, its range
checked, and, in range, its round (`roundCount_ok`): `hStat` and `hIdx` as
`dStat` and `dIdx` say, `used` advanced, and `MSt` kept.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (RoundImpl arr)
open VG.Proof.Mont (val32)
open VG.Impl.Bignum.PPC64LE.PublicChecked (base)
open VG.Impl.Bignum.PPC64LE.Precompute (loadN copyWords)


/-- `hStat` after a draw of `a`, from 4. -/
def dStat (N K i a : Nat) : Nat :=
  if 2 ≤ a ∧ a < N - 1 then (if Proof.MillerRabin.Round.round N a then (if i + 1 < K then 4 else 1) else 2) else 4

/-- `hIdx` after a draw of `a`. -/
def dIdx (N i a : Nat) : Nat := if 2 ≤ a ∧ a < N - 1 ∧ Proof.MillerRabin.Round.round N a = true then i + 1 else i

theorem wp_then3 {a b c d e : Prog isa} {s : State} {P Q : State → Prop}
    (h : WP isa (.seq a (.seq b (.seq c d))) s P) (k : ∀ t, P t → WP isa e t Q) :
    WP isa (.seq a (.seq b (.seq c (.seq d e)))) s Q := by
  rw [WP.seq_iff] at h ⊢
  refine WP.mono h fun t ht => ?_
  rw [WP.seq_iff] at ht ⊢
  refine WP.mono ht fun t ht => ?_
  rw [WP.seq_iff] at ht ⊢
  exact WP.mono ht fun t ht => WP.seq (WP.mono ht k)

theorem WP.chain {l : List (Prog isa)} {rest : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (Prog.chain l (.block [])) rest) s Q) : WP isa (Prog.chain l rest) s Q := by
  induction l generalizing s with
  | nil => rw [Prog.chain, WP.seq_iff, WP.block_nil_iff] at h; exact h
  | cons a l ih => exact WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc h)) fun _ h => ih h)

/-- The draw's pieces between its head and its branches. -/
def drawMid : List (Prog isa) :=
  [loadN, .block (([.addi .r10 .r31 hdrBytes] : List Instr) ++ base .r5 4 ++ ([.lsl .r6 .r11 2,
    .add .r5 .r5 .r6, .subi .r5 .r5 8, ldh .r4 hTop, .load .d .r6 .r5 0, .logic .and .r6 .r6 .r4,
    .store .d .r6 .r5 0] : List Instr) ++ base .r5 4 ++ ([.load .d .r24 .r5 0, .lsr .d .r24 .r24 1,
    .addi .r5 .r5 8, .lsr .d .r6 .r11 1, .subi .r6 .r6 1] : List Instr)),
   countLoop .r6 [.load .d .r3 .r5 0, .logic .or .r24 .r24 .r3, .addi .r5 .r5 8],
   .block (base .r14 3 ++ base .r15 4), copyWords,
   .block (base .r5 3 ++ ([.load .d .r3 .r5 0, .li .r4 1, .logic .or .r3 .r3 .r4, .store .d .r3 .r5 0,
     .lsl .r6 .r11 2, .add .r5 .r5 .r6, .li .r0 0, .store .d .r0 .r5 0] : List Instr) ++ base .r8 3 ++ base .r9 6),
   subMod]

/-- The draw's branches: on the witness below 2, on its range, and the round. -/
def drawBranch (name : String) (roundCode : Prog isa) : Prog isa :=
  .ite (.zero .d .r24) (.block []) (.ite (.zero .d .r20) (.block []) (round name roundCode))

theorem draw_eq (name : String) (roundCode : Prog isa) :
    draw name roundCode = .seq (.block ([ldh .r12 hRand, ldh .r3 hUsed, .add .r12 .r12 .r3, ldh .r6 hK,
      .add .r3 .r3 .r6, sth .r3 hUsed] ++ base .r10 4)) (Prog.chain drawMid (drawBranch name roundCode)) := rfl

/-- Before the draw's branches: the witness `wA mb p.r u` in array 4, `r24`
zero exactly when it is below 2, `r20` exactly when it is not below
`N − 1`. -/
structure DMid (p : PP) (mb N u i C : Nat) (t : State) : Prop where
  m : MSt p mb N C t
  used : word t.mem p.B 152 = BitVec.ofNat 64 (u + (mb + 7) / 8)
  stat : word t.mem p.B 160 = BitVec.ofNat 64 4
  idx : word t.mem p.B 176 = BitVec.ofNat 64 i
  z24 : t.gpr .r24 = 0#64 ↔ wA mb p.r u < 2
  z20 : t.gpr .r20 = 0#64 ↔ ¬ wA mb p.r u < N - 1
  a4 : arr t.mem p.B (wOf mb) 4 = wA mb p.r u

theorem drawRest_ok {C : Nat} {p : PP} {mb N u i : Nat} {s t : State} (h : MSt p mb N C s)
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hroom : u + (mb + 7) / 8 ≤ p.r.length)
    (hI : word s.mem p.B 176 = BitVec.ofNat 64 i) (hS : word s.mem p.B 160 = BitVec.ofNat 64 4)
    (ht : DHead p mb u s t) :
    WP isa (Prog.chain drawMid (.block [])) t (DMid p mb N u i C) := by
  obtain ⟨hw2, hw128, hZ⟩ := h.w
  have hnw := h.st.scr.nowrap
  obtain es : ∀ j, slot (wOf mb) j = 256 + j * (8 * (wOf mb + 2)) := fun _ => rfl
  obtain hZ' : 256 + 28 * (8 * (wOf mb + 2)) + saveBytes ≤ p.Z := by rw [← es]; exact hZ
  simp only [saveBytes] at hZ'
  obtain hD : DPre p mb N u C s := ⟨h.st, h.ph, h.prep, hu, hroom, h.mb1, h.mb2⟩
  unfold drawMid
  refine WP.seq (WP.mono (dLoadN_ok hD ht) fun t₁ ⟨⟨v₁, a10₁, f₁, u₁⟩, k₁⟩ => ?_)
  obtain fr : ∀ r ∈ [(152, 8), (slot (wOf mb) 4, 8 * wOf mb), (slot (wOf mb) 3, 8 * (wOf mb + 2)),
      (slot (wOf mb) 6, 8 * (wOf mb + 2))], Free (wOf mb) r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Or.inl ⟨by simp, rfl⟩
    · exact Or.inr ⟨4, by decide, by decide, rfl, by dsimp only; omega_arith⟩
    · exact Or.inr ⟨3, by decide, by decide, rfl, Nat.le_refl _⟩
    · exact Or.inr ⟨6, by decide, by decide, rfl, Nat.le_refl _⟩
  obtain s28 := es 28
  obtain wr : ∀ {m m' : Mem} {rs : List (Nat × Nat)}, Frm p.B rs m m' →
      (∀ r ∈ rs, r ∈ [(152, 8), (slot (wOf mb) 4, 8 * wOf mb), (slot (wOf mb) 3, 8 * (wOf mb + 2)),
        (slot (wOf mb) 6, 8 * (wOf mb + 2))]) →
      ∀ d, Read (wOf mb) d → word m' p.B d = word m p.B d := fun hf hs d hd =>
    hf.word_eq (fun r hr => (fr r (hs r hr)).word hd) (by have := hd.le; omega_arith)
  obtain st₁ : St p t₁ := h.st.step (Frm.toMut f₁ fun r hr => Free.mut h (fr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp))) k₁
  obtain sub1 : ∀ r ∈ [(152, 8), (slot (wOf mb) 4, 8 * wOf mb)], r ∈ [(152, 8), (slot (wOf mb) 4, 8 * wOf mb),
      (slot (wOf mb) 3, 8 * (wOf mb + 2)), (slot (wOf mb) 6, 8 * (wOf mb + 2))] := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp
  obtain top₁ : word t₁.mem p.B (8 * hTop) = BitVec.ofNat 64 (2 ^ (mb + 64 - 64 * wOf mb) - 1) :=
    (wr f₁ sub1 192 (by simp [Read])).trans h.ph.topW
  -- The cut.
  refine WP.seq (WP.mono (dCut_ok st₁ h.mb1 h.mb2 ((k₁.gpr .r11 (by decide)).trans h.ph.r11)
    ((k₁.gpr .r29 (by decide)).trans h.ph.r29) top₁) fun t₂ ⟨⟨wv₂, r24₂, r5₂, r6₂, r10₂, f₂⟩, k₂⟩ => ?_)
  obtain ha₂ : wv t₂.mem p.B (slot (wOf mb) 4) (wOf mb) = wA mb p.r u := by
    rw [wv₂, ← Pre.val32_eq_wv, v₁]; rfl
  -- The scan.
  obtain k12 := k₁.trans k₂
  refine WP.seq (WP.mono (dScan_ok (h.st.scr.congr k12.wr) r5₂ r6₂ r24₂ hw2 (by omega_arith) (by have := es 4; omega_arith))
    fun t₃ ⟨⟨z₃, m₃⟩, k₃⟩ => ?_)
  rw [ha₂] at z₃
  obtain k13 := k12.trans k₃
  obtain fs : ∀ {m m' : Mem} {rs : List (Nat × Nat)}, Frm p.B rs m m' →
      (∀ r ∈ rs, r ∈ [(152, 8), (slot (wOf mb) 4, 8 * wOf mb), (slot (wOf mb) 3, 8 * (wOf mb + 2)),
        (slot (wOf mb) 6, 8 * (wOf mb + 2))]) → ∀ j, (j = 0 ∨ j = 1 ∨ j = 9 ∨ j = 10 ∨ j = 27) →
      wv m' p.B (slot (wOf mb) j) (wOf mb) = wv m p.B (slot (wOf mb) j) (wOf mb) := fun hf hs j hj =>
    hf.wv_eq (fun r hr => (fr r (hs r hr)).arr hj) (by
      have := es 0; have := es 1; have := es 9; have := es 10; have := es 27
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> omega_arith)
  obtain sub2 : ∀ r ∈ [(slot (wOf mb) 4, 8 * wOf mb)], r ∈ [(152, 8), (slot (wOf mb) 4, 8 * wOf mb),
      (slot (wOf mb) 3, 8 * (wOf mb + 2)), (slot (wOf mb) 6, 8 * (wOf mb + 2))] := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl <;> simp
  obtain hN₃ : wv t₃.mem p.B (slot (wOf mb) 0) (wOf mb) = N := by
    rw [m₃, fs f₂ sub2 0 (by simp), fs f₁ sub1 0 (by simp), ← Pre.val32_eq_wv]; exact h.prep.n
  obtain hx₃ : wv t₃.mem p.B (slot (wOf mb) 4) (wOf mb) = wA mb p.r u := by rw [m₃]; exact ha₂
  obtain r10₃ : t₃.gpr .r10 = off p.B (slot (wOf mb) 0) := (k₃.gpr .r10 (by decide)).trans r10₂
  -- The range, and the round of a witness in it.
  refine wp_then3 (dRange_ok (h.st.scr.congr k13.wr) r10₃ ((k13.gpr .r29 (by decide)).trans h.ph.r29)
    ((k13.gpr .r11 (by decide)).trans h.ph.r11) hw2 hw128 (by have := es 7; omega_arith) hN₃ h.prep.odd hx₃)
    fun t₄ ⟨⟨z₄, f₄⟩, k₄⟩ => ?_
  rw [m₃] at f₄
  obtain sub4 : ∀ r ∈ [(slot (wOf mb) 3, 8 * (wOf mb + 2)), (slot (wOf mb) 6, 8 * (wOf mb + 2))],
      r ∈ [(152, 8), (slot (wOf mb) 4, 8 * wOf mb), (slot (wOf mb) 3, 8 * (wOf mb + 2)),
        (slot (wOf mb) 6, 8 * (wOf mb + 2))] := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp
  obtain F : Frm p.B [(152, 8), (slot (wOf mb) 4, 8 * wOf mb), (slot (wOf mb) 3, 8 * (wOf mb + 2)),
      (slot (wOf mb) 6, 8 * (wOf mb + 2))] s.mem t₄.mem :=
    ((f₁.mono sub1).trans (f₂.mono sub2)).trans (f₄.mono sub4)
  obtain k14 := k13.trans k₄
  obtain r10₄ : t₄.gpr .r10 = s.gpr .r10 := ((k₄.gpr .r10 (by decide)).trans r10₃).trans h.ph.r10.symm
  obtain M₄ : MSt p mb N C t₄ := h.frm F fr k14 (by decide) r10₄ (k14.gpr .r11 (by decide))
    (k14.gpr .r29 (by decide))
  -- The header words the draw and the round read and write.
  obtain hdr : ∀ {d}, (d = 160 ∨ d = 176) → word t₄.mem p.B d = word s.mem p.B d := fun hd =>
    F.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have := es 3; have := es 4; have := es 6
      rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith)
  obtain u₄ : word t₄.mem p.B 152 = BitVec.ofNat 64 (u + (mb + 7) / 8) := by
    rw [← u₁]
    obtain G : Frm p.B [(slot (wOf mb) 4, 8 * wOf mb), (slot (wOf mb) 3, 8 * (wOf mb + 2)),
        (slot (wOf mb) 6, 8 * (wOf mb + 2))] t₁.mem t₄.mem :=
      (f₂.mono fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; simp [hr]).trans
        (f₄.mono fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)
    exact G.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have := es 3; have := es 4; have := es 6
      rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith)
  obtain r24₄ : t₄.gpr .r24 = t₃.gpr .r24 := k₄.gpr .r24 (by decide)
  rw [Prog.chain, WP.block_nil_iff]
  refine ⟨M₄, u₄, (hdr (Or.inl rfl)).trans hS, (hdr (Or.inr rfl)).trans hI, ?_, ?_, ?_⟩
  · rw [r24₄]; exact z₃
  · exact z₄
  · show val32 _ _ _ _ = _
    rw [Pre.val32_eq_wv, ← ha₂]
    exact f₄.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have := es 3; have := es 4; have := es 6
      rcases hr with rfl | rfl <;> dsimp only <;> omega_arith) (by have := es 4; omega_arith)

theorem drawTail_ok {C : Nat} (R : RoundImpl) {p : PP} {mb N u i : Nat} {t₄ : State} (h : DMid p mb N u i C t₄)
    (hi : i < 2 ^ 62) :
    WP isa (drawBranch R.name R.code) t₄ fun t => MSt p mb N C t ∧
      word t.mem p.B 152 = BitVec.ofNat 64 (u + (mb + 7) / 8) ∧
      word t.mem p.B 160 = BitVec.ofNat 64 (dStat N C i (wA mb p.r u)) ∧
      word t.mem p.B 176 = BitVec.ofNat 64 (dIdx N i (wA mb p.r u)) := by
  obtain ⟨M₄, u₄, hS, hI, z₃, z₄, ha₄⟩ := h
  obtain ⟨hw2, hw128, hZ⟩ := M₄.w
  obtain es : ∀ j, slot (wOf mb) j = 256 + j * (8 * (wOf mb + 2)) := fun _ => rfl
  have hnw := M₄.st.scr.nowrap
  obtain hZ' : 256 + 28 * (8 * (wOf mb + 2)) + saveBytes ≤ p.Z := by rw [← es]; exact hZ
  simp only [saveBytes] at hZ'
  obtain out : ¬ (2 ≤ wA mb p.r u ∧ wA mb p.r u < N - 1) → MSt p mb N C t₄ ∧
      word t₄.mem p.B 152 = BitVec.ofNat 64 (u + (mb + 7) / 8) ∧
      word t₄.mem p.B 160 = BitVec.ofNat 64 (dStat N C i (wA mb p.r u)) ∧
      word t₄.mem p.B 176 = BitVec.ofNat 64 (dIdx N i (wA mb p.r u)) := fun hn =>
    ⟨M₄, u₄, by rw [hS, dStat, ite_eq_right hn], by
      rw [hI, dIdx, ite_eq_right fun ⟨a, b, _⟩ => hn ⟨a, b⟩]⟩
  unfold drawBranch
  refine WP.ite (t₄.gpr .r24 == 0) (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · rw [WP.block_nil_iff]
    obtain h0 : t₄.gpr .r24 = 0#64 := beq_iff_eq.mp hb
    exact out fun ⟨a, _⟩ => by have := z₃.mp h0; omega_arith
  refine WP.ite (t₄.gpr .r20 == 0) (eval_zero _ _) (fun hb' => ?_) (fun hb' => ?_)
  · rw [WP.block_nil_iff]
    exact out fun ⟨_, b⟩ => z₄.mp (beq_iff_eq.mp hb') b
  -- A witness in range: its round.
  obtain ha2 : 2 ≤ wA mb p.r u := by
    by_contra hc
    have : (t₄.gpr .r24 == 0) = true := beq_iff_eq.mpr (z₃.mpr (by omega_arith))
    rw [hb] at this; exact absurd this (by decide)
  obtain haN : wA mb p.r u < N - 1 := by
    by_contra hc
    have : (t₄.gpr .r20 == 0) = true := beq_iff_eq.mpr (z₄.mpr hc)
    rw [hb'] at this; exact absurd this (by decide)
  obtain hK : C < 2 ^ 62 := by have := M₄.ph.k2; omega_arith
  have hsp₄ := M₄.st.sp
  refine WP.mono (roundCount_ok R M₄.prep ha₄ (show wA mb p.r u < N by omega_using [haN]) (by rw [hsp₄]; exact M₄.st.stk)
    (by rw [hsp₄]; exact M₄.st.stkB) hI M₄.ph.checksW hi hK)
    fun t ht => ⟨M₄.round ht, ?_⟩
  obtain ⟨v, hv, tm, -⟩ := ht
  have hn₄ : 8 * p.n = p.Z := rfl
  obtain u₅ : word v.mem p.B 152 = BitVec.ofNat 64 (u + (mb + 7) / 8) :=
    (keeps_hdr (i := 19) hv.keeps (by decide) (by decide) (by omega_arith)).trans u₄
  simp only [word, off] at u₅ ⊢
  obtain ht2 : 2 ≤ wA mb p.r u ∧ wA mb p.r u < N - 1 := ⟨ha2, haN⟩
  cases hr : Proof.MillerRabin.Round.round N (wA mb p.r u) <;> simp only [hr, Bool.false_eq_true, ↓reduceIte] at tm <;>
    rw [tm] <;> refine ⟨?_, ?_, ?_⟩
  · rw [rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]; exact u₅
  · rw [rw_self, dStat, ite_eq_left ht2, hr]; rfl
  · rw [rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), dIdx, ite_eq_right (by simp [hr])]
    exact (keeps_hdr (i := 22) hv.keeps (by decide) (by decide) (by omega_arith)).trans hI
  · rw [rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]; exact u₅
  · rw [rw_self, dStat, ite_eq_left ht2, hr]; rfl
  · rw [rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), rw_self, dIdx, ite_eq_left ⟨ha2, haN, hr⟩]


theorem draw_ok {C : Nat} (R : RoundImpl) {p : PP} {mb N u i : Nat} {s : State} (h : MSt p mb N C s)
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hroom : u + (mb + 7) / 8 ≤ p.r.length)
    (hI : word s.mem p.B 176 = BitVec.ofNat 64 i) (hS : word s.mem p.B 160 = BitVec.ofNat 64 4)
    (hi : i < 2 ^ 62) :
    WP isa (draw R.name R.code) s fun t => MSt p mb N C t ∧
      word t.mem p.B 152 = BitVec.ofNat 64 (u + (mb + 7) / 8) ∧
      word t.mem p.B 160 = BitVec.ofNat 64 (dStat N C i (wA mb p.r u)) ∧
      word t.mem p.B 176 = BitVec.ofNat 64 (dIdx N i (wA mb p.r u)) := by
  obtain hD : DPre p mb N u C s := ⟨h.st, h.ph, h.prep, hu, hroom, h.mb1, h.mb2⟩
  rw [draw_eq]
  exact WP.seq (WP.mono (dHead_ok hD) fun t ht => WP.chain (WP.seq (WP.mono (drawRest_ok h hu hroom hI hS ht)
    fun t₄ h₄ => drawTail_ok R h₄ hi)))

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
