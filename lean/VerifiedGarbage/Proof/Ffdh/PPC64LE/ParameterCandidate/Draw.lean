module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Phase
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.RoundCall
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.WordCut
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Prep
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

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
structure DPre (p : PP) (mb N u : Nat) (s : State) : Prop where
  st : St p s
  ph : Ph p mb s
  prep : Prep s p.B p.n (wOf mb) N
  used : word s.mem p.B (8 * hUsed) = BitVec.ofNat 64 u
  room : u + (mb + 7) / 8 ≤ p.r.length
  mb1 : 511 ≤ mb
  mb2 : mb ≤ p.bits

/-- The head of a draw: the octets' address in `r12`, their count in `r6`,
array 4's in `r10`, and `used` advanced. -/
theorem dHead_ok {p : PP} {mb N u : Nat} {s : State} (h : DPre p mb N u s) :
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

/-- The head and the load: the witness's octets in array 4. -/
theorem dLoad_ok {p : PP} {mb N u : Nat} {s : State} (h : DPre p mb N u s) :
    WP isa (.seq (.block ([ldh .r12 hRand, ldh .r3 hUsed, .add .r12 .r12 .r3, ldh .r6 hK, .add .r3 .r3 .r6,
        sth .r3 hUsed] ++ base .r10 4)) loadN) s fun t =>
      (val32 t.mem p.B (slot (wOf mb) 4) (2 * wOf mb) = Spec.Rsa.os2ip ((p.r.drop u).take ((mb + 7) / 8)) ∧
        t.gpr .r10 = off p.B (slot (wOf mb) 4) ∧
        Frm p.B [(152, 8), (slot (wOf mb) 4, 8 * wOf mb)] s.mem t.mem ∧
        t.mem.readW (p.B + BitVec.ofNat 64 152) 64 = BitVec.ofNat 64 (u + (mb + 7) / 8)) ∧
      Keep (([.r3, .r6, .r12, .r10] : List Reg) ++ ([.r0, .r14, .r15, .r16, .r17] : List Reg)) s t := by
  have hb1 := h.st.dims.b1
  have hb2 := h.st.dims.b2
  have hn := h.st.dims.n
  have hnw := h.st.scr.nowrap
  have hm1 := h.mb1
  have hm2 := h.mb2
  have hroom := h.room
  have h11 := h.ph.r11
  generalize hwd : wOf mb = w at *
  have hw8 : 8 ≤ w := by simp only [wOf] at hwd; omega
  have hw128 : w ≤ 128 := by simp only [wOf] at hwd; omega
  have hKw : (mb + 7) / 8 ≤ 8 * w := by simp only [wOf] at hwd; omega
  have hZ : slot w 4 + 8 * w ≤ p.Z := by simp only [slot, hdrBytes, PP.Z, PP.L] at hn ⊢; omega
  generalize hKd : (mb + 7) / 8 = K at *
  have hK1 : 1 ≤ K := by omega
  refine WP.seq (WP.mono (dHead_ok h) fun t ⟨⟨a12, a6, a10, am⟩, k₁⟩ => ?_)
  rw [hKd, hwd] at *
  have ho : Outside p.B 152 8 s.mem t.mem := by rw [am]; exact writeW_outside _ _ _ (by omega)
  have hbr : Spec.Rsa.bytesAt t.mem p.rp p.r.length = p.r := by
    rw [bytes_frm (Frm.of_outside (rs := [(152, 8)]) ho (List.mem_singleton_self _)) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; simp only [PP.Z]; omega) h.st.bufs.sepR]
    exact h.st.bufs.bR
  have e : ∀ i, VG.Proof.Mont.off (p.rp + BitVec.ofNat 64 u) i = off p.rp (u + i) := fun i => off_off p.rp u i
  refine WP.mono (loadN_ok (N := p.rp + BitVec.ofNat 64 u) (h.st.scr.congr k₁.wr) a10
    (by rw [a12]; simp only [BitVec.add_zero]) a6 ((k₁.gpr .r11 (by decide)).trans h11) hK1 hKw
    (by omega) (by simp only [slot, hdrBytes]; omega) hZ
    (fun i hi => by
      rw [k₁.rd, k₁.wr, e]
      exact h.st.bufs.rdR _ (by omega))
    (fun i hi x hx => by
      rw [e]
      exact h.st.bufs.sepR _ (by omega) x hx)) fun t₂ ⟨v₂, o₂, k₂⟩ => ?_
  refine ⟨⟨?_, (k₂.gpr .r10 (by decide)).trans a10, ?_, ?_⟩, k₁.trans k₂⟩
  · rw [v₂, ← VG.Proof.Dsa.bytesAt_slice t.mem p.rp (total := p.r.length) (by omega), hbr]
  · exact (Frm.of_outside ho (List.mem_cons_self)).trans
      (Frm.of_outside o₂ (List.mem_cons_of_mem _ List.mem_cons_self))
  · rw [show t₂.mem.readW (p.B + BitVec.ofNat 64 152) 64 = word t₂.mem p.B 152 from rfl,
      Outside.word o₂ (by simp only [slot, hdrBytes]; omega) (by omega), am]
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
  have hw8 : 8 ≤ w := by simp only [wOf] at hwd; omega
  have hw128 : w ≤ 128 := by simp only [wOf] at hwd; omega
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have hZ : slot w 4 + 8 * w ≤ p.Z := by
    simp only [es, PP.Z] at hn ⊢; simp only [PP.L] at hn; omega
  have hk1 : 1 ≤ mb + 64 - 64 * w := by simp only [wOf] at hwd; omega
  have hk2 : mb + 64 - 64 * w ≤ 64 := by simp only [wOf] at hwd; omega
  have hb : 64 * (w - 1) + (mb + 64 - 64 * w) = mb := by simp only [wOf] at hwd; omega
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
    simp only [off]; rw [Offset.add_ofNat_sub _ (by omega)]; congr 2; omega
  have sT : InRegions v.wr (off p.B (slot w 4 + 8 * (w - 1))) 8 := by
    rw [kuv.wr]; exact h.scr.st (by omega)
  have lT : InRegions (v.rd ++ v.wr) (off p.B (slot w 4 + 8 * (w - 1))) 8 := by
    rw [kuv.rd, kuv.wr]; exact h.scr.ld (by omega)
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
    omega
  have hsub : BitVec.ofNat 64 w - 1#64 = BitVec.ofNat 64 (w - 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  have l4 : InRegions (t₂.rd ++ t₂.wr) (off p.B (slot w 4)) 8 := by
    rw [k₂'.rd, k₂'.wr]; exact h.scr.ld (by omega)
  refine WP.mono (WP.keep [.r24, .r5, .r6] (Q := fun t => t.gpr .r24 = t₂.mem.readW (off p.B (slot w 4)) 64 >>> 1 ∧
      t.gpr .r5 = off p.B (slot w 4 + 8) ∧ t.gpr .r6 = BitVec.ofNat 64 (w - 1) ∧ t.mem = t₂.mem) ?_ (by decide))
    fun t ⟨⟨t24, t5, t6, tm⟩, kt⟩ => ?_
  · prun [b5, BitVec.add_zero, l4, (k₂'.gpr .r11 (by decide)).trans h11, hsh, hsub]
  have e0 : t.mem = s.mem.writeW (off p.B (slot w 4 + 8 * (w - 1)))
      (s.mem.readW (off p.B (slot w 4 + 8 * (w - 1))) 64 &&& BitVec.ofNat 64 (2 ^ k - 1)) := by rw [tm, m₂, tm₁]
  refine ⟨⟨?_, by rw [t24, tm, m₂], t5, t6, (kt.gpr .r10 (by decide)).trans ((k₂.gpr .r10 (by decide)).trans
    ((k₁.gpr .r10 (by decide)).trans ((kv.gpr .r10 (by decide)).trans u10))), ?_⟩, (k₂'.trans kt).mono (by decide)⟩
  · rw [← hb]
    refine Proof.Ffdh.ParameterCandidate.wv_cut (by omega) hk2 ?_ fun j hj => ?_
    · simp only [word, off] at e0 ⊢; rw [e0, rw_self]
    · simp only [word, off] at e0 ⊢; rw [e0, rw_off _ _ _ (by omega) (by omega) (by omega)]
  · rw [e0]
    exact frm_writeW (Frm.refl _ _ _) _ ⟨_, List.mem_singleton_self _, by dsimp only; omega,
      by dsimp only; omega⟩ (by omega)

theorem wv_lt_two {m : Mem} {B : Addr} {d w : Nat} (hw : 1 ≤ w) :
    wv m B d w < 2 ↔ word m B d >>> 1 = 0#64 ∧ ∀ j, 1 ≤ j → j < w → word m B (d + 8 * j) = 0#64 := by
  have e := wv_add m B d 1 (w - 1)
  rw [show 1 + (w - 1) = w by omega] at e
  simp only [wv, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.pow_zero, Nat.one_mul, Nat.mul_one] at e
  have hz := wv_eq_zero_iff m B (d + 8) (w - 1)
  have hsh : word m B d >>> 1 = 0#64 ↔ (word m B d).toNat < 2 := by
    rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]; omega
  rw [e, hsh]
  constructor
  · intro hl
    have h0 : wv m B (d + 8) (w - 1) = 0 := by
      by_contra hc; have : 1 ≤ wv m B (d + 8) (w - 1) := Nat.one_le_iff_ne_zero.mpr hc; omega
    refine ⟨by omega, fun j hj1 hj2 => ?_⟩
    have := hz.mp h0 (j - 1) (by omega)
    rwa [show d + 8 + 8 * (j - 1) = d + 8 * j by omega] at this
  · rintro ⟨hl, hr⟩
    have h0 : wv m B (d + 8) (w - 1) = 0 := hz.mpr fun q hq => by
      rw [show d + 8 + 8 * q = d + 8 * (q + 1) by omega]; exact hr _ (by omega) (by omega)
    omega

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
  refine WP.mono (wp_countdown (cnt := .r6) (N := w - 1) (by omega) (by omega) Inv
    (fun i hi t ⟨⟨t5, t24, tm⟩, kt⟩ _ => ?_)
    ⟨⟨by rw [h5], by rw [h24]; exact ⟨fun h => ⟨h, fun j h1 h2 => absurd h2 (by omega)⟩, fun h => h.1⟩, rfl⟩,
      Keep.refl _ _⟩ h6) fun t ⟨⟨_, t24, tm⟩, kt⟩ => ⟨⟨?_, tm⟩, kt⟩
  · have l : InRegions (t.rd ++ t.wr) (off B (d + 8 * (i + 1))) 8 := by
      rw [kt.rd, kt.wr]; exact hs.ld (by omega)
    have rv : t.mem.readW (off B (d + 8 * (i + 1))) 64 = word s.mem B (d + 8 * (i + 1)) := by rw [tm]
    refine WP.mono (WP.keep [.r3, .r5, .r6, .r24] (Q := fun u =>
        u.gpr .r5 = off B (d + 8 * (i + 1 + 1)) ∧
        u.gpr .r24 = t.gpr .r24 ||| word s.mem B (d + 8 * (i + 1)) ∧ u.mem = t.mem ∧
        u.gpr .r6 = t.gpr .r6 - BitVec.ofNat 64 1) ?_ (by decide))
      fun u ⟨⟨u5, u24, um, u6⟩, ku⟩ => ⟨⟨⟨u5, ?_, um.trans tm⟩, (kt.trans ku).mono (by decide)⟩, u6⟩
    · prun [t5, BitVec.add_zero, l, rv]
      rw [show d + 8 * (i + 1) + 8 = d + 8 * (i + 1 + 1) by omega]
    · rw [u24, BitVec.or_eq_zero_iff, t24]
      constructor
      · rintro ⟨⟨a, b⟩, c⟩
        exact ⟨a, fun j h1 h2 => by
          rcases Nat.lt_or_ge j (i + 1) with hj | hj
          · exact b j h1 (by omega)
          · rw [show j = i + 1 by omega]; exact c⟩
      · rintro ⟨a, b⟩
        exact ⟨⟨a, fun j h1 h2 => b j h1 (by omega)⟩, b _ (by omega) (Nat.le_refl _)⟩
  · rw [t24, wv_lt_two (by omega)]
    exact ⟨fun ⟨a, b⟩ => ⟨a, fun j h1 h2 => b j h1 (by omega)⟩, fun ⟨a, b⟩ => ⟨a, fun j h1 h2 => b j h1 (by omega)⟩⟩

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
