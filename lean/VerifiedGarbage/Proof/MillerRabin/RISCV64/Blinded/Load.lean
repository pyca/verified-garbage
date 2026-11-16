module

public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.Ctx
public import VerifiedGarbage.Spec.Rsa.Contract
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.RsaKeyGen.WitnessBits
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCore
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# The blinded Miller–Rabin loop on RISC-V: a draw

As on PPC64LE (`Proof/MillerRabin/PPC64LE/Blinded/Load.lean`): `load_ok`,
the next `D = 8 (t + 1)` octets of the tape, from `used`, into array 4
(`loadN`), `hUsed := used + D`, and the array's word `t` and'ed with
`2^b − 1`: the array holds the draw `x` cut to its low `64 t + b` bits
(`wv_cut`), the bits of `c − 1`.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.RISCV64.Blinded

open VG VG.RISCV64 VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.MillerRabin.RISCV64.Search VG.Impl.MillerRabin.RISCV64.Blinded
open VG.Proof.MillerRabin.RISCV64 (Env A)
open VG.Proof.MillerRabin.RISCV64.Search (Prep)
open VG.Proof.Bignum (slot Frm wv word off ofs writeW_outside word_writeW_self)

/-- The tape's octets lie beyond the working space. -/
theorem BCtx.tape_out {s : State} {B R : Addr} {L w c rl t b ch : Nat} (h : BCtx s B L w c R rl t b ch) {i : Nat}
    (hi : i < rl) : 8 * L ≤ ofs B (R + BitVec.ofNat 64 i) := by
  exact Nat.le_of_not_lt fun hlt => h.sepR i hi _ hlt rfl

/-- A change of memory within the working space keeps the tape's octets. -/
theorem BCtx.bytes_keep {s : State} {B R : Addr} {L w c rl t b ch : Nat} (h : BCtx s B L w c R rl t b ch)
    {m : Mem} (hm : ∀ x, 8 * L ≤ ofs B x → m x = s.mem x) {u n : Nat} (hun : u + n ≤ rl) :
    Spec.Rsa.bytesAt m (R + BitVec.ofNat 64 u) n = Spec.Rsa.bytesAt s.mem (R + BitVec.ofNat 64 u) n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  rw [Offset.add_add]
  exact hm _ (h.tape_out (by omega))

/-- The registers `load` writes. -/
def loadRegs : List Reg := [.s7, .t2, .s8, .a7, .a0, .s0, .t3, .t4, .t5]

/-- The tape's address at `used` (`s7`), `hUsed := used + D`, `D` in `s8`
and array 4's base in `a7`. -/
theorem loadA_ok {s : State} {B R : Addr} {L w c rl t b ch used : Nat} (h : BCtx s B L w c R rl t b ch)
    (hu : word s.mem B (8 * hUsed) = BitVec.ofNat 64 used) :
    WP isa (.block ([ldh .s7 hRand, ldh .t2 hUsed, .add .s7 .s7 .t2, ldh .s8 hK, .add .t2 .t2 .s8,
        sth .t2 hUsed] ++ PublicChecked.base .a7 4)) s fun u =>
      (u.gpr .s7 = R + BitVec.ofNat 64 used ∧ u.gpr .s8 = BitVec.ofNat 64 (8 * (t + 1)) ∧
        u.gpr .a7 = off B (slot w 4) ∧
        u.mem = s.mem.writeW (off B (8 * hUsed)) (BitVec.ofNat 64 (used + 8 * (t + 1)))) ∧
      Keep [.s7, .t2, .s8, .a7] s u := by
  have e := h.prep.env
  have hs := e.hs
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := e.hZ
  refine WP.keep _ ?_ (by rfl) (by rfl)
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (u₁ : State) => (u₁.gpr .s7 = R + BitVec.ofNat 64 used ∧
      u₁.gpr .s8 = BitVec.ofNat 64 (8 * (t + 1)) ∧
      u₁.mem = s.mem.writeW (off B (8 * hUsed)) (BitVec.ofNat 64 (used + 8 * (t + 1)))) ∧
      Keep [.s7, .t2, .s8] s u₁) (WP.keep _ ?_ (by rfl) (by rfl)) fun u₁ ⟨⟨a7', a8, am⟩, k1⟩ => ?_
  · have r136 : s.mem.readW (B + 136#64) 64 = R := h.rand
    have r152 : s.mem.readW (B + 152#64) 64 = BitVec.ofNat 64 used := hu
    have r216 : s.mem.readW (B + 216#64) 64 = BitVec.ofNat 64 (8 * (t + 1)) := h.k
    simp only [ldh, sth, hRand, hUsed, hK]
    brun [e.s6, hs.ld (d := 136) (n := 8) (by omega), hs.al8 (d := 136) (by omega) (by decide),
      hs.ld (d := 152) (n := 8) (by omega), hs.al8 (d := 152) (by omega) (by decide),
      hs.ld (d := 216) (n := 8) (by omega), hs.al8 (d := 216) (by omega) (by decide),
      hs.st (d := 152) (n := 8) (by omega), r136, r152, r216]
    rw [← BitVec.ofNat_add]
  · have e1 : Env u₁ B (8 * L) w := e.keep k1 (by decide)
    refine WP.mono (e1.base (rd := .a7) (by decide) 4) fun u₂ ⟨⟨b7, bm⟩, k2⟩ => ?_
    exact ⟨(k2.gpr (by decide)).trans a7', (k2.gpr (by decide)).trans a8, b7, bm.trans am⟩

/-- A draw from `used`, cut to `64 t + b` bits. -/
theorem load_ok {s : State} {B R : Addr} {L w c rl t b ch used : Nat} (h : BCtx s B L w c R rl t b ch)
    (hu : word s.mem B (8 * hUsed) = BitVec.ofNat 64 used) (hav : used + 8 * (t + 1) ≤ rl) :
    WP isa load s fun s' =>
      (A s'.mem B w 4 =
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (R + BitVec.ofNat 64 used) (8 * (t + 1))) % 2 ^ (64 * t + b) ∧
        word s'.mem B (8 * hUsed) = BitVec.ofNat 64 (used + 8 * (t + 1)) ∧
        Frm B [(8 * hUsed, 8), (slot w 4, 8 * (w + 2))] s.mem s'.mem ∧ s'.gpr .a7 = off B (slot w 0)) ∧
      Keep loadRegs s s' := by
  have e := h.prep.env
  have hs := e.hs
  have hnw := hs.nowrap
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := e.hZ
  have htw := h.tw
  have hw4 := e.hw
  have hw128 := e.hw'
  have hD : 8 * (t + 1) ≤ 8 * w := by omega
  unfold load loadDraw
  -- The tape's address, `hUsed`, and array 4's base.
  refine WP.assoc' (WP.seq (WP.mono (loadA_ok h hu) fun u ⟨⟨u7, u8, ua7, um⟩, ku⟩ => ?_))
  have hu' : Scr u B (8 * L) := hs.congr ku.2.2
  have hNr : ∀ i < 8 * (t + 1), InRegions (u.rd ++ u.wr) (off (R + BitVec.ofNat 64 used) i) 1 := fun i hi => by
    rw [ku.2.1, ku.2.2, show off (R + BitVec.ofNat 64 used) i = R + BitVec.ofNat 64 used + BitVec.ofNat 64 i from rfl,
      Offset.add_add]; exact h.rdR _ (by omega)
  have hNs : ∀ i < 8 * (t + 1), ∀ x, ofs B x < 8 * L → off (R + BitVec.ofNat 64 used) i ≠ x := fun i hi x hx => by
    rw [show off (R + BitVec.ofNat 64 used) i = R + BitVec.ofNat 64 used + BitVec.ofNat 64 i from rfl,
      Offset.add_add]; exact h.sepR _ (by omega) x hx
  refine WP.assoc' (WP.seq (WP.mono (loadN_ok (k := 8 * (t + 1)) hu' ua7
    (by rw [u7]; exact (BitVec.add_zero _).symm) u8 ((ku.gpr (by decide)).trans e.t0) (by omega) hD (by omega)
    (by simp only [slot, hdrBytes]; omega) (by simp only [slot, hdrBytes]; omega)
    (by simp only [slot, hdrBytes]; omega) hNr hNs)
    fun v ⟨vv, vo, kv⟩ => ?_))
  -- The memory so far: `hUsed` and array 4.
  have fu : Frm B [(8 * hUsed, 8), (slot w 4, 8 * (w + 2))] s.mem v.mem := by
    refine Frm.trans (Frm.of_outside (o := 8 * hUsed) (n := 8) ?_ (by simp))
      (Frm.of_outside (o := slot w 4) (n := 8 * (w + 2)) (fun x hx => vo x (by simp only [VG.Proof.Mont.ofs, VG.Proof.Bignum.ofs] at hx ⊢; omega)) (by simp))
    rw [um]; exact writeW_outside _ _ _ (by simp only [hUsed]; omega)
  have bytes : Spec.Rsa.bytesAt u.mem (R + BitVec.ofNat 64 used) (8 * (t + 1)) =
      Spec.Rsa.bytesAt s.mem (R + BitVec.ofNat 64 used) (8 * (t + 1)) := by
    rw [um]
    refine h.bytes_keep (fun x hx => writeW_outside _ _ _ (by simp only [hUsed]; omega) x (by simp only [hUsed]; omega)) hav
  have hval : wv v.mem B (slot w 4) w = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (R + BitVec.ofNat 64 used) (8 * (t + 1))) := by
    rw [← Pre.wordsVal_eq_wv, vv, bytes]
  have hlt : wv v.mem B (slot w 4) w < 2 ^ (64 * (t + 1)) := by
    rw [hval]
    have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem (R + BitVec.ofNat 64 used) (8 * (t + 1)))
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at this
    rwa [show (256 : Nat) ^ (8 * (t + 1)) = 2 ^ (64 * (t + 1)) by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; congr 1; omega] at this
  -- Header words the draw reads.
  have kvu := ku.trans kv
  have v6 : v.gpr .s6 = B := (kvu.gpr (by decide)).trans e.s6
  have v5 : v.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)) := (kvu.gpr (by decide)).trans e.s5
  have vw : ∀ d, d + 8 ≤ 256 → d % 8 = 0 → d ≠ 8 * hUsed → word v.mem B d = word s.mem B d := fun d hd h8 hn =>
    fu.word_eq (fun r hr => by
      simp only [hUsed, List.mem_cons, List.not_mem_nil, or_false] at hr hn
      rcases hr with rfl | rfl <;> simp only [slot, hdrBytes] <;> omega) (by omega)
  have hv : Scr v B (8 * L) := hs.congr kvu.2.2
  have r128 : v.mem.readW (B + 128#64) 64 = BitVec.ofNat 64 (8 * t) :=
    (vw 128 (by omega) (by decide) (by simp [hUsed])).trans h.topOff
  have r192 : v.mem.readW (B + 192#64) 64 = BitVec.ofNat 64 (2 ^ b - 1) :=
    (vw 192 (by omega) (by decide) (by simp [hUsed])).trans h.top
  have es4 : slot w 4 = 256 + 4 * (8 * (w + 2)) := rfl
  -- `a7` back, then the top word's mask.
  refine WP.seq (WP.mono (WP.keep [.a7] (Q := fun (y : State) => y.gpr .a7 = off B (slot w 0) ∧ y.mem = v.mem)
      (by brun [v6, hdrBytes]; simp only [slot, hdrBytes, Nat.zero_mul, Nat.add_zero]) (by rfl) (by rfl))
    fun y ⟨⟨y7, ym⟩, ky⟩ => ?_)
  have ey : Env y B (8 * L) w := ⟨hv.congr ky.2.2, y7, (ky.gpr (by decide)).trans v5,
    (ky.gpr (by decide)).trans ((kvu.gpr (by decide)).trans e.t0),
    (ky.gpr (by decide)).trans v6, hw4, hw128, e.hZ⟩
  refine WP.mono (WP.keep [.t2, .t3, .t4] (Q := fun x =>
      x.mem = v.mem.writeW (off B (slot w 4 + 8 * t))
        (word v.mem B (slot w 4 + 8 * t) &&& BitVec.ofNat 64 (2 ^ b - 1)) ∧ x.gpr .a7 = off B (slot w 0))
    ?_ (by rfl) (by rfl)) fun x ⟨⟨xm, x7⟩, kx⟩ => ?_
  · simp only [topAddr, List.append_assoc]
    rw [WP.block_append_iff]
    refine WP.mono (ey.base (rd := .t3) (by decide) 4) fun z ⟨⟨z3, zm⟩, kz⟩ => ?_
    have z6 : z.gpr .s6 = B := (kz.gpr (by decide)).trans ey.s6
    have hz : Scr z B (8 * L) := ey.hs.congr kz.2.2
    have z7 : z.gpr .a7 = off B (slot w 0) := (kz.gpr (by decide)).trans y7
    simp only [ldh, hTopOff, hTop]
    have ha : slot w 4 + 8 * t + 8 ≤ 8 * L := by simp only [slot, hdrBytes]; omega
    have ha8 : (slot w 4 + 8 * t) % 8 = 0 := by simp only [slot, hdrBytes]; omega
    brun [z6, z3, zm, ym, r128, r192, hz.ld (d := 128) (n := 8) (by omega), hz.al8 (d := 128) (by omega) (by decide),
      hz.ld (d := 192) (n := 8) (by omega), hz.al8 (d := 192) (by omega) (by decide),
      hz.ld (d := slot w 4 + 8 * t) (n := 8) ha, hz.al8 (d := slot w 4 + 8 * t) ha ha8,
      hz.st (d := slot w 4 + 8 * t) (n := 8) ha]
    exact z7
  · refine ⟨⟨?_, ?_, ?_, x7⟩, ((kvu.trans ky).trans kx).mono (by decide)⟩
    · have ha : slot w 4 + 8 * t + 8 ≤ 2 ^ 64 := by simp only [slot, hdrBytes]; omega
      simp only [A, Pre.wordsVal_eq_wv]
      rw [xm, ← hval]
      refine VG.Proof.RsaKeyGen.wv_cut h.b64 (word_writeW_self _ _ _ _) (fun j hj hjt => ?_) hlt
      exact (writeW_outside _ _ _ ha).word (by omega) (by simp only [slot, hdrBytes]; omega)
    · rw [xm, (writeW_outside _ _ _ (by simp only [slot, hdrBytes]; omega)).word
        (by simp only [hUsed, slot, hdrBytes]; omega) (by simp only [hUsed]; omega)]
      have hv1 : word v.mem B (8 * hUsed) = word u.mem B (8 * hUsed) :=
        vo.word (by simp only [hUsed, slot, hdrBytes]; omega) (by simp only [hUsed]; omega)
      rw [hv1, um]
      exact word_writeW_self _ _ _ _
    · refine fu.trans (Frm.of_outside (o := slot w 4) (n := 8 * (w + 2)) ?_ (by simp))
      rw [xm]
      exact (writeW_outside _ _ _ (by simp only [slot, hdrBytes]; omega)).mono (by omega) (by omega)

end VG.Proof.MillerRabin.RISCV64.Blinded
