module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Tail
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Setup
public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Candidate
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Sel
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.RsaKeyGen.Bits
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Close
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Gcd
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Slot
import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
import VerifiedGarbage.Proof.RsaKeyGen.Generate
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.RangeCover

/-! ### `RsaKeyGen.PPC64LE.Cand.LoadC`, which only this module used -/

section

/-!
# A candidate on PPC64LE: drawing the candidate

`loadC_ok`: the first `8 w` octets of `rand` (at `R`, in `r26`) into array 0,
most significant first, its low bit and its two top bits set: array 0 holds
`RsaKeyGen.candidate (64 w) x` (`wv_candidate`), and `r28 := 8 w`, the octets
read.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Candidate (loadC)
open VG.Proof.MillerRabin.PPC64LE (Env)
open VG.Proof.Bignum (slot wv)

/-- The registers `loadC` writes. -/
def lcRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r12, .r14, .r15, .r16, .r17, .r28]

theorem top2_eq : (BitVec.signExtend 64 ((49152 : BitVec 16) ++ (0 : BitVec 16)) <<< 32 : BitVec 64) =
    13835058055282163712#64 := by
  decide

theorem loadC_ok {s : State} {B R : Addr} {Z w : Nat} (h : Env s B Z w) (h26 : s.gpr .r26 = R)
    (h24 : s.gpr .r24 = BitVec.ofNat 64 (8 * w)) (hR : ∀ i < 8 * w, InRegions (s.rd ++ s.wr) (off R i) 1)
    (hsep : ∀ i < 8 * w, ∀ x, ofs B x < Z → off R i ≠ x) :
    WP isa loadC s fun t =>
      (wv t.mem B (slot w 0) w = Spec.RsaKeyGen.candidate (64 * w)
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem R (8 * w))) ∧
        t.gpr .r28 = BitVec.ofNat 64 (8 * w) ∧ Outside B (slot w 0) (8 * w) s.mem t.mem) ∧
        Keep lcRegs s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hw4 := h.hw
  have hw128 := h.hw'
  have hZ := h.hZ
  obtain es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  obtain h0 : slot w 0 = 256 := by rw [es, Nat.zero_mul, Nat.add_zero]
  obtain hZ' : 256 + 28 * (8 * (w + 2)) ≤ Z := by rw [← es]; exact hZ
  unfold loadC
  refine WP.seq ?_
  obtain hpre : WP isa (.block [.addi .r12 .r26 0, .addi .r6 .r24 0]) s fun u =>
      (u.gpr .r12 = off R 0 ∧ u.gpr .r6 = BitVec.ofNat 64 (8 * w) ∧ u.mem = s.mem) ∧ Keep [.r6, .r12] s u := by
    refine WP.keep _ ?_ (by decide)
    prun [h26, h24]
    exact BitVec.add_zero _
  refine WP.mono hpre fun u ⟨⟨u12, u6, um⟩, ku⟩ => ?_
  obtain eu := h.keep ku (by decide)
  refine WP.seq (WP.mono (loadN_ok eu.hs eu.h10 u12 u6 eu.h11 (by omega_using [hw4]) (Nat.le_refl _) (by omega_using [hw128])
    (by rw [h0]; decide) (by rw [h0]; omega_using [hZ']) (fun i hi => by rw [ku.rd, ku.wr]; exact hR i hi) hsep)
    fun v ⟨vv, vout, kv⟩ => ?_)
  rw [um] at vv vout
  obtain ev := eu.keep kv (by decide)
  have hsv := ev.hs
  -- The candidate's bits.
  obtain hw0 := hsv.ld (d := slot w 0) (n := 8) (by omega_using [h0, hZ'])
  obtain hwt := hsv.ld (d := slot w 0 + 8 * (w - 1)) (n := 8) (by omega_using [h0, hZ'])
  obtain hs0 := hsv.st (d := slot w 0) (n := 8) (by omega_using [h0, hZ'])
  obtain hst := hsv.st (d := slot w 0 + 8 * (w - 1)) (n := 8) (by omega_using [h0, hZ'])
  obtain e5 : (BitVec.ofNat 64 (2 * w) <<< 2) + off B (slot w 0) - BitVec.ofNat 64 8 = off B (slot w 0 + 8 * (w - 1)) := by
    obtain e8 : BitVec.ofNat 64 (2 * w) <<< 2 = BitVec.ofNat 64 (8 * w) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega_using []
    rw [e8, BitVec.add_comm, off_add, Offset.add_ofNat_sub _ (show 8 ≤ slot w 0 + 8 * w by omega_using [hw4]),
      show slot w 0 + 8 * w - 8 = slot w 0 + 8 * (w - 1) by omega_using [hw4]]
  obtain r24 : v.gpr .r24 = BitVec.ofNat 64 (8 * w) := by rw [kv.gpr _ (by decide), ku.gpr _ (by decide), h24]
  refine WP.mono (WP.keep [.r3, .r4, .r5, .r28] (Q := fun t =>
      t.mem = (v.mem.writeW (off B (slot w 0)) (word v.mem B (slot w 0) ||| BitVec.ofNat 64 1)).writeW
        (off B (slot w 0 + 8 * (w - 1))) (word v.mem B (slot w 0 + 8 * (w - 1)) ||| BitVec.ofNat 64 (3 * 2 ^ 62)) ∧
      t.gpr .r28 = BitVec.ofNat 64 (8 * w)) ?_ (by decide)) fun t ⟨⟨tm, t28⟩, kt⟩ => ⟨⟨?_, t28, ?_⟩, ?_⟩
  · prun [ev.h10, ev.h11, r24, hw0, hs0, e5, hwt, hst, exec_lis, top2_eq]
    refine ⟨?_, BitVec.add_zero _⟩
    rw [Mem.readW_writeW_sep (Offset.sep B (d := slot w 0 + 8 * (w - 1)) (n := 8) (e := slot w 0) (k := 8)
      (by omega_using [hw4]) (by omega_using [hw128, h0]) (by omega_using [h0])) (by decide)]
  · have sep : ∀ d e : Nat, d + 8 ≤ e ∨ e + 8 ≤ d → d + 8 ≤ Z → e + 8 ≤ Z → ∀ (m : Mem) (x : BitVec 64),
        (m.writeW (off B e) x).readW (off B d) 64 = m.readW (off B d) 64 := fun d e h1 h2 h3 m x =>
      Mem.readW_writeW_sep (Offset.sep B h1 (by omega_using [hnw, h2]) (by omega_using [hnw, h3])) (by decide)
    rw [VG.Proof.RsaKeyGen.wv_candidate (m := v.mem) (by omega_using [hw4]) ?_ ?_ ?_, ← Pre.val32_eq_wv, vv]
    · show t.mem.readW _ 64 = _
      rw [tm, sep _ _ (by omega_using [hw4]) (by omega_using [h0, hZ']) (by omega_using [h0, hZ']), Mem.readW_writeW_self64]; rfl
    · show t.mem.readW _ 64 = _
      rw [tm, Mem.readW_writeW_self64]
    · intro j hj0 hj
      show t.mem.readW _ 64 = v.mem.readW _ 64
      rw [tm, sep _ _ (by omega_using [hj]) (by omega_using [h0, hZ', hj]) (by omega_using [h0, hZ']), sep _ _ (by omega_using [hj0]) (by omega_using [h0, hZ', hj]) (by omega_using [h0, hZ'])]
  · have o1 := writeW_outside v.mem B (d := slot w 0) (word v.mem B (slot w 0) ||| BitVec.ofNat 64 1) (by omega_using [h0])
    obtain o2 := writeW_outside (v.mem.writeW (off B (slot w 0)) (word v.mem B (slot w 0) ||| BitVec.ofNat 64 1)) B
      (d := slot w 0 + 8 * (w - 1)) (word v.mem B (slot w 0 + 8 * (w - 1)) ||| BitVec.ofNat 64 (3 * 2 ^ 62))
      (by omega_using [hw128, h0])
    rw [tm]
    exact (vout.trans (o1.mono (by omega_using []) (by omega_using [hw4]))).trans (o2.mono (by omega_using []) (by omega_using [hw4]))
  · exact ((ku.trans kv).trans kt).mono (by simp [lcRegs])

end VG.Proof.RsaKeyGen.PPC64LE.Cand

end

end


/-!
# A candidate on PPC64LE: once `rand` holds the candidate's octets

`cOp_eq`: what the contract asks, as `afterDraw` of the candidate from the
first `out_len` octets. `main_ok`: the working space set up, the candidate
loaded, then too close to `p`, `gcd(c − 1, e) ≠ 1`, or the test
(`test_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Candidate (main setup loadC closeCheck gcdCheck finish nArr aP aBnd aCm1)
open VG.Proof.MillerRabin.PPC64LE (RoundImpl Env arr)
open VG.Proof.Bignum (slot)

theorem take_bytesAt (m : Mem) (A : Addr) {k n : Nat} (h : k ≤ n) :
    (Spec.Rsa.bytesAt m A n).take k = Spec.Rsa.bytesAt m A k := by
  unfold Spec.Rsa.bytesAt
  rw [← List.map_take, List.take_range, Nat.min_eq_left h]

/-- What the contract asks, from the candidate in the first `8 w` octets. -/
theorem cOp_eq {s0 : State} {w : Nat} (hw : oL s0 = 8 * w) (hw1 : 1 ≤ w) (hav : oL s0 ≤ rL s0) :
    cOp s0 = VG.Proof.RsaKeyGen.afterDraw (64 * w)
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r6) (s0.gpr .r7).toNat))
      (Spec.RsaKeyGen.otherPrime (Spec.Rsa.bytesAt s0.mem (s0.gpr .r8) (s0.gpr .r9).toNat))
      (Spec.RsaKeyGen.candidate (64 * w) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (8 * w))))
      ((Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (rL s0)).drop (8 * w)) := by
  unfold cOp Spec.RsaKeyGen.candidateOp
  rw [hw, VG.Proof.RsaKeyGen.candidateStep_eq _ _ _ _ (by omega_using [hw1]), show 8 * (8 * w) = 64 * w by omega_using [],
    VG.Proof.RsaKeyGen.ite_t (by rw [bytesAt_length]; omega_using [hw, hav])]
  unfold VG.Proof.RsaKeyGen.seg
  rw [List.drop_zero, take_bytesAt _ _ (by omega_using [hw, hav])]

/-- Bytes of a readable region. -/
theorem rd_bytes {s : State} {A : Addr} {n k : Nat} (hm : (⟨A, n⟩ : Region) ∈ s.rd) (hA : A.toNat + n ≤ 2 ^ 64)
    (hk : k ≤ n) : ∀ i < k, InRegions (s.rd ++ s.wr) (off A i) 1 := fun i hi =>
  ⟨_, List.mem_append_left _ hm, Offset.contains_base _ (by omega_using [hk, hi]) (by omega_using [hA, hk, hi])⟩

/-- Bytes of a region apart from the working space. -/
theorem sep_bytes {A B : Addr} {n k Z : Nat} (hd : (⟨A, n⟩ : Region).Disjoint ⟨B, Z⟩) (hA : A.toNat + n ≤ 2 ^ 64)
    (hk : k ≤ n) : ∀ i < k, ∀ x, ofs B x < Z → off A i ≠ x := fun i hi x hx e => by
  refine hd _ (Offset.contains_base _ (d := i) (by omega_using [hk, hi]) (by omega_using [hA, hk, hi])) ?_
  show Region.Contains _ (off A i) 1
  rw [e]; simp only [Region.Contains]; simp only [ofs] at hx; omega_using [hx]

/-- An input's octets through `Bx`, for an input apart from what the body
writes. -/
theorem in_bytes {s0 s : State} (hb : Bx s0 s) {ρ : Region}
    (hd : ∀ r ∈ [cO s0, cU s0, cS s0, cF s0], ρ.Disjoint r) {k : Nat} (hk : k ≤ ρ.len) (hk' : k < 2 ^ 64) :
    Spec.Rsa.bytesAt s.mem ρ.base k = Spec.Rsa.bytesAt s0.mem ρ.base k :=
  bytes_bx hb hk' fun r hr => (hd r hr).sub_left (Region.sub_prefix hk)


/-- The body's state once `rand` has the candidate's octets. -/
structure MIn (s0 s : State) : Prop where
  ctx : Ctx s0 s
  r21 : s.gpr .r21 = s0.gpr .r6
  r30 : s.gpr .r30 = s0.gpr .r7
  r18 : s.gpr .r18 = s0.gpr .r8
  r19 : s.gpr .r19 = s0.gpr .r9
  r26 : s.gpr .r26 = s0.gpr .r10
  r27 : s.gpr .r27 = PPC64LE.stackArg s0 0
  r31 : s.gpr .r31 = sB s0
  r11 : s.gpr .r11 = PPC64LE.stackArg s0 2
  hav : oL s0 ≤ rL s0
  syms : s.syms = s0.syms
  tab : TabOk s0

theorem w32_zero {m : Mem} {B : Addr} {d : Nat} (h : word m B d = 0) : w32 m B d = 0 := by
  have := word_eq_w32 m B d
  rw [h] at this
  simp at this
  omega_using [this]

/-- The candidate's words. -/
abbrev cw (s0 : State) : Nat := oL s0 / 8

/-- The candidate. -/
abbrev candOf (s0 : State) : Nat :=
  Spec.RsaKeyGen.candidate (64 * cw s0) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (8 * cw s0)))

theorem cw_facts {s0 : State} (hp : CIn s0) : oL s0 = 8 * cw s0 ∧ 4 ≤ cw s0 ∧ cw s0 ≤ 64 := by
  have hv := hp.valid
  simp only [Spec.RsaKeyGen.primeLenValid] at hv
  simp only [cw, oL]
  omega_using [hv]

theorem scr_fit {s0 : State} (hp : CIn s0) : slot (cw s0) nArr ≤ 8 * sL s0 := by
  have hscr := hp.scr
  simp only [Spec.Rsa.scratchWords] at hscr
  have := cw_facts hp
  simp only [nArr, slot_lin, sL, oL] at this hscr ⊢
  omega_using [hscr, this]

/-- After `setup`. -/
structure M1 (s0 s : State) : Prop where
  ctx : Ctx s0 s
  env : Env s (sB s0) (8 * sL s0) (cw s0)
  lay : Lay s.mem (sB s0) (sL s0) (cw s0)
  zs : ∀ i < nArr * (cw s0 + 2), word s.mem (sB s0) (256 + 8 * i) = 0
  r18 : s.gpr .r18 = s0.gpr .r8
  r19 : s.gpr .r19 = s0.gpr .r9
  r21 : s.gpr .r21 = s0.gpr .r6
  r30 : s.gpr .r30 = s0.gpr .r7
  r26 : s.gpr .r26 = s0.gpr .r10
  r27 : s.gpr .r27 = PPC64LE.stackArg s0 0
  hav : oL s0 ≤ rL s0
  syms : s.syms = s0.syms
  tab : TabOk s0

theorem setupS {s0 s : State} (h : MIn s0 s) : WP isa setup s (M1 s0) := by
  have hp := h.ctx.bx.pre
  obtain ⟨hw, hw4, hw64⟩ := cw_facts hp
  have hfS := hp.fS
  have eO : oL s0 = (s0.gpr .r4).toNat := rfl
  have eL : sL s0 = (PPC64LE.stackArg s0 2).toNat := rfl
  have eSB : (sB s0).toNat = (PPC64LE.stackArg s0 1).toNat := rfl
  obtain hZ := scr_fit hp
  obtain hS : Scr s (sB s0) (8 * sL s0) :=
    Scr.of_mem (by rw [h.ctx.bx.wr, bodyWr, hp.wr, ← cS_eq]; simp) (by omega_using [hfS, eL, eSB])
  obtain h24 : s.gpr .r24 = BitVec.ofNat 64 (8 * cw s0) := by rw [h.ctx.r24, ← hw, eO, ofNat_toNat64]
  refine WP.mono_syms (setup_ok hS h.r31 (by rw [h.r11, eL, ofNat_toNat64]) h24 hw4 hw64 hZ)
    fun t₁ ⟨⟨e₁, lay₁, zs, o₁⟩, k₁⟩ sy₁ => ?_
  refine ⟨h.ctx.step k₁.sp k₁.rd k₁.wr (frame_outs o₁ (fun x hx => by
      simp only [setupRanges, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · simp only [nArr, slot_lin] at hZ; omega_using [hZ]
      · have : 256 + nArr * (8 * (cw s0 + 2)) = slot (cw s0) nArr := rfl
        exact this ▸ hZ)) (k₁.gpr _ (by decide))
    (k₁.gpr _ (by decide)) (k₁.gpr _ (by decide)) (k₁.gpr _ (by decide)), e₁, lay₁, zs,
    (k₁.gpr _ (by decide)).trans h.r18, (k₁.gpr _ (by decide)).trans h.r19, (k₁.gpr _ (by decide)).trans h.r21,
    (k₁.gpr _ (by decide)).trans h.r30, (k₁.gpr _ (by decide)).trans h.r26, (k₁.gpr _ (by decide)).trans h.r27,
    h.hav, sy₁.trans h.syms, h.tab⟩

/-- After `loadC`. -/
structure M2 (s0 s : State) : Prop where
  ctx : Ctx s0 s
  env : Env s (sB s0) (8 * sL s0) (cw s0)
  lay : Lay s.mem (sB s0) (sL s0) (cw s0)
  zs : ∀ i, cw s0 ≤ i → i < nArr * (cw s0 + 2) → word s.mem (sB s0) (256 + 8 * i) = 0
  v : VG.Proof.Bignum.wv s.mem (sB s0) (slot (cw s0) 0) (cw s0) = candOf s0
  r28 : s.gpr .r28 = BitVec.ofNat 64 (8 * cw s0)
  r18 : s.gpr .r18 = s0.gpr .r8
  r19 : s.gpr .r19 = s0.gpr .r9
  r21 : s.gpr .r21 = s0.gpr .r6
  r30 : s.gpr .r30 = s0.gpr .r7
  r26 : s.gpr .r26 = s0.gpr .r10
  r27 : s.gpr .r27 = PPC64LE.stackArg s0 0
  hav : oL s0 ≤ rL s0
  syms : s.syms = s0.syms
  tab : TabOk s0

theorem loadCS {s0 s : State} (h : M1 s0 s) : WP isa loadC s (M2 s0) := by
  have hp := h.ctx.bx.pre
  obtain ⟨hw, hw4, hw64⟩ := cw_facts hp
  have hfS := hp.fS
  have hfr := hp.fr
  have hav := h.hav
  have eO : oL s0 = (s0.gpr .r4).toNat := rfl
  have eR : rL s0 = (PPC64LE.stackArg s0 0).toNat := rfl
  obtain hZ := scr_fit hp
  have hZ' := hZ
  simp only [nArr, slot_lin] at hZ'
  obtain h24 : s.gpr .r24 = BitVec.ofNat 64 (8 * cw s0) := by rw [h.ctx.r24, ← hw, eO, ofNat_toNat64]
  obtain bR : Spec.Rsa.bytesAt s.mem (s0.gpr .r10) (8 * cw s0) =
      Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (8 * cw s0) :=
    in_bytes h.ctx.bx (ρ := cR s0) (hR_dj hp) (by show 8 * cw s0 ≤ (PPC64LE.stackArg s0 0).toNat; omega)
      (by omega_using [hw64])
  refine WP.mono_syms (loadC_ok h.env h.r26 h24
    (rd_bytes (n := rL s0) (by rw [h.ctx.bx.rd]; exact hp.rR) hfr (by omega_using [hw, hav]))
    (sep_bytes (n := rL s0) (by rw [← cS_eq]; exact hp.rS) hfr (by omega_using [hw, hav])))
    fun t₂ ⟨⟨v₂, r28₂, o₂⟩, k₂⟩ sy₂ => ?_
  rw [bR] at v₂
  refine ⟨h.ctx.step k₂.sp k₂.rd k₂.wr (frame_scr (frame_of_outside o₂ (by rw [slot_lin]; omega_using [hZ'])))
    (k₂.gpr _ (by decide)) (k₂.gpr _ (by decide)) (k₂.gpr _ (by decide)) (k₂.gpr _ (by decide)),
    h.env.keep k₂ (by decide), ?_, fun i h1 h2 => ?_, v₂, r28₂, (k₂.gpr _ (by decide)).trans h.r18,
    (k₂.gpr _ (by decide)).trans h.r19, (k₂.gpr _ (by decide)).trans h.r21, (k₂.gpr _ (by decide)).trans h.r30,
    (k₂.gpr _ (by decide)).trans h.r26, (k₂.gpr _ (by decide)).trans h.r27, hav, sy₂.trans h.syms, h.tab⟩
  · have ow : ∀ d, d + 8 ≤ 256 → word t₂.mem (sB s0) d = word s.mem (sB s0) d := fun d hd =>
      o₂.word (by rw [slot_lin]; omega_using [hd]) (by omega_using [hd])
    exact ⟨(ow 0 (by omega_using [])).trans h.lay.len, (ow 48 (by omega_using [])).trans h.lay.wW,
      (ow 224 (by omega_using [])).trans h.lay.strideW, fun j hj => (ow _ (by omega_using [hj])).trans (h.lay.arrW j hj)⟩
  · have h2' := h2
    simp only [nArr] at h2'
    rw [o₂.word (by rw [slot_lin]; omega_using [h1]) (by omega_using [hw64, h2']), h.zs i h2]

/-- After `closeCheck`. -/
structure M3 (s0 s : State) : Prop where
  ctx : Ctx s0 s
  env : Env s (sB s0) (8 * sL s0) (cw s0)
  lay : Lay s.mem (sB s0) (sL s0) (cw s0)
  arr0 : val32 s.mem (sB s0) (slot (cw s0) 0) (2 * cw s0) = candOf s0
  f : s.gpr .r22 = BitVec.ofNat 64
    (if Spec.RsaKeyGen.tooClose (64 * cw s0) (Spec.RsaKeyGen.otherPrime (pB s0)) (candOf s0) then 1 else 0)
  r28 : s.gpr .r28 = BitVec.ofNat 64 (8 * cw s0)
  r21 : s.gpr .r21 = s0.gpr .r6
  r30 : s.gpr .r30 = s0.gpr .r7
  r26 : s.gpr .r26 = s0.gpr .r10
  r27 : s.gpr .r27 = PPC64LE.stackArg s0 0
  hav : oL s0 ≤ rL s0
  syms : s.syms = s0.syms
  tab : TabOk s0

theorem closeS {s0 s : State} (h : M2 s0 s) : WP isa closeCheck s (M3 s0) := by
  have hp := h.ctx.bx.pre
  obtain ⟨hw, hw4, hw64⟩ := cw_facts hp
  have hfS := hp.fS
  have hfp := hp.fp
  have hplv := hp.plv
  obtain hZ := scr_fit hp
  have hZ' := hZ
  simp only [nArr, slot_lin] at hZ'
  have eO : oL s0 = (s0.gpr .r4).toNat := rfl
  obtain h24 : s.gpr .r24 = BitVec.ofNat 64 (8 * cw s0) := by rw [h.ctx.r24, ← hw, eO, ofNat_toNat64]
  obtain bP : Spec.Rsa.bytesAt s.mem (s0.gpr .r8) (s0.gpr .r9).toNat = pB s0 :=
    in_bytes h.ctx.bx (ρ := cP s0) (hP_dj hp) (Nat.le_refl _) (by omega_using [])
  obtain hcv : val32 s.mem (sB s0) (slot (cw s0) 0) (2 * cw s0) = candOf s0 := by
    rw [Pre.val32_eq_wv]; exact h.v
  refine WP.mono_syms (closeCheck_ok h.env hZ hcv
    (w32_zero (by rw [slot0]; exact h.zs (cw s0) (by omega_using []) (by simp only [nArr]; omega_using [])))
    (w32_zero (by
      rw [show slot (cw s0) aP + 8 * cw s0 = 256 + 8 * (28 * (cw s0 + 2) + cw s0) by simp only [aP, slot_lin]; omega_using []]
      exact h.zs _ (by omega_using []) (by simp only [nArr]; omega_using [])))
    (fun i hi => by
      rw [show slot (cw s0) aBnd + 8 * i = 256 + 8 * (32 * (cw s0 + 2) + i) by simp only [aBnd, slot_lin]; omega_using []]
      exact h.zs _ (by omega_using []) (by simp only [nArr]; omega_using [hi]))
    h.r18 (h.r19.trans (ofNat_toNat64 _).symm) (by simp only [oL] at hw; omega_using [hw, hplv]) h24
    (fun hpl => rd_bytes (n := (s0.gpr .r9).toNat) (by rw [h.ctx.bx.rd]; exact hp.rP) hfp (by omega_using [hpl]))
    (fun hpl => sep_bytes (n := (s0.gpr .r9).toNat) (by rw [← cS_eq]; exact hp.pS) hfp (by omega_using [hpl])))
    fun t₃ ⟨⟨f₃, e₃, o₃⟩, k₃⟩ sy₃ => ?_
  rw [bP] at f₃
  obtain ow : ∀ d, d + 8 ≤ 256 → word t₃.mem (sB s0) d = word s.mem (sB s0) d := fun d hd =>
    o₃.word (by simp only [aP, slot_lin]; omega_using [hd]) (by omega_using [hd])
  refine ⟨h.ctx.step k₃.sp k₃.rd k₃.wr (frame_scr (frame_of_outside o₃ (by simp only [aP, slot_lin]; omega_using [hZ'])))
    (k₃.gpr _ (by decide)) (k₃.gpr _ (by decide)) (k₃.gpr _ (by decide)) (k₃.gpr _ (by decide)), e₃,
    ⟨(ow 0 (by omega_using [])).trans h.lay.len, (ow 48 (by omega_using [])).trans h.lay.wW,
      (ow 224 (by omega_using [])).trans h.lay.strideW, fun j hj => (ow _ (by omega_using [hj])).trans (h.lay.arrW j hj)⟩,
    by rw [o₃.val32 (by simp only [aP, slot_lin]; omega_using []) (by rw [slot_lin]; omega_using [hw64])]; exact hcv, f₃,
    (k₃.gpr _ (by decide)).trans h.r28, (k₃.gpr _ (by decide)).trans h.r21, (k₃.gpr _ (by decide)).trans h.r30,
    (k₃.gpr _ (by decide)).trans h.r26, (k₃.gpr _ (by decide)).trans h.r27, h.hav, sy₃.trans h.syms, h.tab⟩

theorem hlen_drop {s0 : State} (w : Nat) :
    ((Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (rL s0)).drop (8 * w)).length = rL s0 - 8 * w := by
  rw [List.length_drop, bytesAt_length]

/-- What the contract asks, the candidate being `candOf`. -/
theorem cOp_cand {s0 : State} (hp : CIn s0) (hav : oL s0 ≤ rL s0) :
    cOp s0 = VG.Proof.RsaKeyGen.afterDraw (64 * cw s0) (Spec.Rsa.os2ip (eB s0))
      (Spec.RsaKeyGen.otherPrime (pB s0)) (candOf s0) ((rB s0).drop (8 * cw s0)) := by
  obtain ⟨hw, hw4, _⟩ := cw_facts hp
  exact cOp_eq hw (by omega_using [hw4]) hav

/-- Too close to `p`. -/
theorem closeFin {s0 s : State} (h : M3 s0 s)
    (hcl : Spec.RsaKeyGen.tooClose (64 * cw s0) (Spec.RsaKeyGen.otherPrime (pB s0)) (candOf s0) = true) :
    WP isa (finish 2) s fun t => Bx s0 t ∧ CQ s0 (t.gpr .r3) t.mem := by
  have hp := h.ctx.bx.pre
  obtain ⟨hw, hw4, _⟩ := cw_facts hp
  have hav := h.hav
  obtain hop := cOp_cand hp hav
  rw [VG.Proof.RsaKeyGen.afterDraw, hcl] at hop
  simp only [↓reduceIte] at hop
  refine fin_ok 2 (by decide) h.ctx (by rw [hop]; rfl) (by rw [outOf, hop]) ?_
  rw [h.r28, usedOf, hop]
  simp only [hlen_drop]
  congr 1; omega_using [hw, hav]

/-- After `gcdCheck`. -/
structure M4 (s0 s : State) : Prop where
  ctx : Ctx s0 s
  env : Env s (sB s0) (8 * sL s0) (cw s0)
  lay : Lay s.mem (sB s0) (sL s0) (cw s0)
  arr0 : val32 s.mem (sB s0) (slot (cw s0) 0) (2 * cw s0) = candOf s0
  ncl : Spec.RsaKeyGen.tooClose (64 * cw s0) (Spec.RsaKeyGen.otherPrime (pB s0)) (candOf s0) = false
  g : s.gpr .r22 = 0 ↔ Nat.gcd (candOf s0 - 1) (Spec.Rsa.os2ip (eB s0)) = 1
  r28 : s.gpr .r28 = BitVec.ofNat 64 (8 * cw s0)
  r26 : s.gpr .r26 = s0.gpr .r10
  r27 : s.gpr .r27 = PPC64LE.stackArg s0 0
  hav : oL s0 ≤ rL s0
  syms : s.syms = s0.syms
  tab : TabOk s0

theorem gcdS {s0 s : State} (h : M3 s0 s)
    (hncl : Spec.RsaKeyGen.tooClose (64 * cw s0) (Spec.RsaKeyGen.otherPrime (pB s0)) (candOf s0) = false) :
    WP isa gcdCheck s (M4 s0) := by
  have hp := h.ctx.bx.pre
  obtain ⟨hw, hw4, hw64⟩ := cw_facts hp
  have hfS := hp.fS
  have hfe := hp.fe
  have hel1 := hp.el1
  have hel2 := hp.el2
  obtain hZ := scr_fit hp
  have hZ' := hZ
  simp only [nArr, slot_lin] at hZ'
  obtain hshape : PrimeShape (64 * cw s0) (candOf s0) := VG.Proof.RsaKeyGen.candidate_shape (by omega_using [hw4]) _
  obtain bE : Spec.Rsa.bytesAt s.mem (s0.gpr .r6) (s0.gpr .r7).toNat = eB s0 :=
    in_bytes h.ctx.bx (ρ := cE s0) (hE_dj hp) (Nat.le_refl _) (by omega_using [])
  obtain hc : VG.Proof.Bignum.wv s.mem (sB s0) (slot (cw s0) 0) (cw s0) = candOf s0 := by
    rw [← Pre.val32_eq_wv]; exact h.arr0
  refine WP.mono_syms (gcdCheck_ok h.env hZ hc hshape.1 (h.r21.trans (BitVec.add_zero _).symm)
    (h.r30.trans (ofNat_toNat64 _).symm) hel1 hel2
    (rd_bytes (n := (s0.gpr .r7).toNat) (by rw [h.ctx.bx.rd]; exact hp.rE) hfe (by omega_using [])))
    fun t₄ ⟨⟨g₄, o₄⟩, k₄⟩ sy₄ => ?_
  rw [bE] at g₄
  obtain o₄ : Outside (sB s0) (slot (cw s0) aCm1) (8 * cw s0) s.mem t₄.mem := fun x hx => o₄ x hx
  obtain ow : ∀ d, d + 8 ≤ 256 → word t₄.mem (sB s0) d = word s.mem (sB s0) d := fun d hd =>
    o₄.word (by simp only [aCm1, slot_lin]; omega_using [hd]) (by omega_using [hd])
  refine ⟨h.ctx.step k₄.sp k₄.rd k₄.wr (frame_scr (frame_of_outside o₄ (by simp only [aCm1, slot_lin]; omega_using [hZ'])))
    (k₄.gpr _ (by decide)) (k₄.gpr _ (by decide)) (k₄.gpr _ (by decide)) (k₄.gpr _ (by decide)),
    h.env.keep k₄ (by decide), ⟨(ow 0 (by omega_using [])).trans h.lay.len, (ow 48 (by omega_using [])).trans h.lay.wW,
      (ow 224 (by omega_using [])).trans h.lay.strideW, fun j hj => (ow _ (by omega_using [hj])).trans (h.lay.arrW j hj)⟩,
    by rw [o₄.val32 (by simp only [aCm1, slot_lin]; omega_using []) (by rw [slot_lin]; omega_using [hw64])]; exact h.arr0, hncl, g₄,
    (k₄.gpr _ (by decide)).trans h.r28, (k₄.gpr _ (by decide)).trans h.r26, (k₄.gpr _ (by decide)).trans h.r27,
    h.hav, sy₄.trans h.syms, h.tab⟩

/-- `gcd(c − 1, e) ≠ 1`. -/
theorem gcdFin {s0 s : State} (h : M4 s0 s) (hg : ¬ Nat.gcd (candOf s0 - 1) (Spec.Rsa.os2ip (eB s0)) = 1) :
    WP isa (finish 3) s fun t => Bx s0 t ∧ CQ s0 (t.gpr .r3) t.mem := by
  have hp := h.ctx.bx.pre
  obtain ⟨hw, hw4, _⟩ := cw_facts hp
  have hav := h.hav
  obtain hop := cOp_cand hp hav
  obtain hgb : (Nat.gcd (candOf s0 - 1) (Spec.Rsa.os2ip (eB s0)) == 1) = false := by simp [hg]
  rw [VG.Proof.RsaKeyGen.afterDraw, h.ncl] at hop
  simp only [hgb, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hop
  refine fin_ok 3 (by decide) h.ctx (by rw [hop]; rfl) (by rw [outOf, hop]) ?_
  rw [h.r28, usedOf, hop]
  simp only [hlen_drop]
  congr 1; omega_using [hw, hav]

theorem toTIn {s0 s : State} (h : M4 s0 s) (hg : Nat.gcd (candOf s0 - 1) (Spec.Rsa.os2ip (eB s0)) = 1) :
    TIn s0 s (cw s0) (candOf s0) := by
  have hp := h.ctx.bx.pre
  obtain ⟨hw, hw4, hw64⟩ := cw_facts hp
  have hav := h.hav
  obtain hop := cOp_cand hp hav
  obtain hgb : (Nat.gcd (candOf s0 - 1) (Spec.Rsa.os2ip (eB s0)) == 1) = true := by simp [hg]
  rw [VG.Proof.RsaKeyGen.afterDraw, h.ncl] at hop
  simp only [hgb, Bool.and_true, Bool.false_eq_true, ↓reduceIte] at hop
  refine ⟨h.ctx, h.env, h.lay, scr_fit hp, h.arr0, VG.Proof.RsaKeyGen.candidate_shape (by omega_using [hw4]) _, hw, hw64,
    h.r26, h.r27, h.r28, by omega_using [hw, hav], h.syms, h.tab, ?_⟩
  rw [hop]
  cases Spec.RsaKeyGen.obviouslyComposite (64 * cw s0) (candOf s0) <;> rfl

theorem main_ok {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) {s0 s : State} (h : MIn s0 s) :
    WP isa (main trial R.name R.code) s fun t => Bx s0 t ∧ CQ s0 (t.gpr .r3) t.mem := by
  unfold main
  simp only [VG.Impl.RsaKeyGen.PPC64LE.Candidate.seqs]
  refine WP.seq (WP.mono (setupS h) fun t₁ h₁ => ?_)
  refine WP.seq (WP.mono (loadCS h₁) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (closeS h₂) fun t₃ h₃ => ?_)
  refine WP.ite _ (eval_nonzero_ofNat' _ _ (by split <;> decide) h₃.f) (fun hz => ?_) (fun hz => ?_)
  · exact closeFin h₃ (by revert hz; cases Spec.RsaKeyGen.tooClose _ _ (candOf s0) <;> decide)
  · have hncl : Spec.RsaKeyGen.tooClose (64 * cw s0) (Spec.RsaKeyGen.otherPrime (pB s0)) (candOf s0) = false := by
      revert hz; cases Spec.RsaKeyGen.tooClose _ _ (candOf s0) <;> decide
    refine WP.seq (WP.mono (gcdS h₃ hncl) fun t₄ h₄ => ?_)
    refine WP.ite _ (VG.PPC64LE.eval_nonzero _ _) (fun hz => ?_) (fun hz => ?_)
    · exact gcdFin h₄ fun e => by rw [h₄.g.mpr e] at hz; exact absurd hz (by decide)
    · exact test_ok D R (toTIn h₄ (h₄.g.mp (by simpa using hz)))

end VG.Proof.RsaKeyGen.PPC64LE.Cand
