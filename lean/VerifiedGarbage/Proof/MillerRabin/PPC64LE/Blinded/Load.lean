module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Blinded.Ctx
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.RsaKeyGen.WitnessBits
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# The blinded Miller–Rabin loop on PPC64LE: a draw

`load_ok`: the next `D = 8 (t + 1)` octets of the tape, from `used`, into
array 4 (`loadN`), `hUsed := used + D`, and the array's word `t` and'ed with
`2^b − 1`: the array holds the draw `x` cut to its low `64 t + b` bits
(`wv_cut`), the bits of `c − 1`.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE.Blinded

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.MillerRabin.PPC64LE.Search VG.Impl.MillerRabin.PPC64LE.Blinded
open VG.Proof.MillerRabin.PPC64LE (Env arr)
open VG.Proof.MillerRabin.PPC64LE.Search (Prep)
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
def loadRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r10, .r12, .r14, .r15, .r16, .r17]

/-- The tape's address at `used` (`r12`), `hUsed := used + D`, `D` in `r6`
and array 4's base in `r10`. -/
theorem loadA_ok {s : State} {B R : Addr} {L w c rl t b ch used : Nat} (h : BCtx s B L w c R rl t b ch)
    (hu : word s.mem B (8 * hUsed) = BitVec.ofNat 64 used) :
    WP isa (.block ([ldh .r12 hRand, ldh .r3 hUsed, .add .r12 .r12 .r3, ldh .r6 hK, .add .r3 .r3 .r6,
        sth .r3 hUsed] ++ PublicChecked.base .r10 4)) s fun u =>
      (u.gpr .r12 = R + BitVec.ofNat 64 used ∧ u.gpr .r6 = BitVec.ofNat 64 (8 * (t + 1)) ∧
        u.gpr .r10 = off B (slot w 4) ∧
        u.mem = s.mem.writeW (off B (8 * hUsed)) (BitVec.ofNat 64 (used + 8 * (t + 1)))) ∧
      Keep [.r3, .r6, .r10, .r12] s u := by
  have e := h.prep.env
  have hs := e.hs
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := e.hZ
  refine WP.keep _ ?_ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (u₁ : State) => (u₁.gpr .r12 = R + BitVec.ofNat 64 used ∧
      u₁.gpr .r6 = BitVec.ofNat 64 (8 * (t + 1)) ∧
      u₁.mem = s.mem.writeW (off B (8 * hUsed)) (BitVec.ofNat 64 (used + 8 * (t + 1)))) ∧
      Keep [.r3, .r6, .r12] s u₁) (WP.keep _ ?_ (by decide)) fun u₁ ⟨⟨a12, a6, am⟩, k1⟩ => ?_
  · simp only [ldh, sth, hRand, hUsed, hK]
    prun [e.h31, hs.ld (d := 136) (n := 8) (by omega), hs.ld (d := 152) (n := 8) (by omega),
      hs.ld (d := 216) (n := 8) (by omega), hs.st (d := 152) (n := 8) (by omega)]
    have r136 : s.mem.readW (B + 136#64) 64 = R := h.rand
    have r152 : s.mem.readW (B + 152#64) 64 = BitVec.ofNat 64 used := hu
    have r216 : s.mem.readW (B + 216#64) 64 = BitVec.ofNat 64 (8 * (t + 1)) := h.k
    rw [r136, r152, r216, ← BitVec.ofNat_add]
    exact ⟨rfl, rfl, rfl⟩
  · have e1 : Env u₁ B (8 * L) w := e.keep k1 (by decide)
    refine WP.mono (e1.base (rd := .r10) (by decide) (by decide) 4) fun u₂ ⟨⟨b10, bm⟩, k2⟩ => ?_
    exact ⟨(k2.gpr .r12 (by decide)).trans a12, (k2.gpr .r6 (by decide)).trans a6, b10, bm.trans am⟩

/-- A draw from `used`, cut to `64 t + b` bits. -/
theorem load_ok {s : State} {B R : Addr} {L w c rl t b ch used : Nat} (h : BCtx s B L w c R rl t b ch)
    (hu : word s.mem B (8 * hUsed) = BitVec.ofNat 64 used) (hav : used + 8 * (t + 1) ≤ rl) :
    WP isa load s fun s' =>
      (wv s'.mem B (slot w 4) w =
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (R + BitVec.ofNat 64 used) (8 * (t + 1))) % 2 ^ (64 * t + b) ∧
        word s'.mem B (8 * hUsed) = BitVec.ofNat 64 (used + 8 * (t + 1)) ∧
        Frm B [(8 * hUsed, 8), (slot w 4, 8 * (w + 2))] s.mem s'.mem ∧ s'.gpr .r10 = off B (slot w 0)) ∧
      Keep loadRegs s s' := by
  have e := h.prep.env
  have hs := e.hs
  have hnw := hs.nowrap
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := e.hZ
  have htw := h.tw
  have hw4 := e.hw
  have hw128 := e.hw'
  have hD : 8 * (t + 1) ≤ 8 * w := by omega
  unfold load
  -- The tape's address, `hUsed`, and array 4's base.
  refine WP.seq (WP.mono (loadA_ok h hu) fun u ⟨⟨u12, u6, u10, um⟩, ku⟩ => ?_)
  have hu' : Scr u B (8 * L) := hs.congr ku.wr
  have hNr : ∀ i < 8 * (t + 1), InRegions (u.rd ++ u.wr) (off (R + BitVec.ofNat 64 used) i) 1 := fun i hi => by
    rw [ku.rd, ku.wr, show off (R + BitVec.ofNat 64 used) i = R + BitVec.ofNat 64 used + BitVec.ofNat 64 i from rfl,
      Offset.add_add]; exact h.rdR _ (by omega)
  have hNs : ∀ i < 8 * (t + 1), ∀ x, ofs B x < 8 * L → off (R + BitVec.ofNat 64 used) i ≠ x := fun i hi x hx => by
    rw [show off (R + BitVec.ofNat 64 used) i = R + BitVec.ofNat 64 used + BitVec.ofNat 64 i from rfl,
      Offset.add_add]; exact h.sepR _ (by omega) x hx
  refine WP.seq (WP.mono (VG.Proof.Bignum.PPC64LE.loadN_ok (k := 8 * (t + 1)) hu' u10
    (by rw [u12]; exact (BitVec.add_zero _).symm) u6 ((ku.gpr .r11 (by decide)).trans e.h11) (by omega) hD (by omega)
    (by simp only [slot, hdrBytes]; omega) (by simp only [slot, hdrBytes]; omega) hNr hNs)
    fun v ⟨vv, vo, kv⟩ => ?_)
  -- The memory so far: `hUsed` and array 4.
  have fu : Frm B [(8 * hUsed, 8), (slot w 4, 8 * (w + 2))] s.mem v.mem := by
    refine Frm.trans (Frm.of_outside (o := 8 * hUsed) (n := 8) ?_ (by simp)) (Frm.of_outside (o := slot w 4) (n := 8 * (w + 2)) (vo.mono ?_ ?_) (by simp))
    · rw [um]; exact writeW_outside _ _ _ (by simp only [hUsed]; omega)
    · simp only [Nat.le_refl]
    · omega
  have bytes : Spec.Rsa.bytesAt u.mem (R + BitVec.ofNat 64 used) (8 * (t + 1)) =
      Spec.Rsa.bytesAt s.mem (R + BitVec.ofNat 64 used) (8 * (t + 1)) := by
    rw [um]
    refine h.bytes_keep (fun x hx => writeW_outside _ _ _ (by simp only [hUsed]; omega) x (by simp only [hUsed]; omega)) hav
  have hval : wv v.mem B (slot w 4) w = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (R + BitVec.ofNat 64 used) (8 * (t + 1))) := by
    rw [← VG.Proof.Bignum.PPC64LE.Pre.val32_eq_wv, vv, bytes]
  have hlt : wv v.mem B (slot w 4) w < 2 ^ (64 * (t + 1)) := by
    rw [hval]
    have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem (R + BitVec.ofNat 64 used) (8 * (t + 1)))
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at this
    rwa [show (256 : Nat) ^ (8 * (t + 1)) = 2 ^ (64 * (t + 1)) by rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; congr 1; omega] at this
  -- Header words the draw reads.
  have kvu := ku.trans kv
  have v31 : v.gpr .r31 = B := (kvu.gpr .r31 (by decide)).trans e.h31
  have v29 : v.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)) := (kvu.gpr .r29 (by decide)).trans e.h29
  have vw : ∀ d, d + 8 ≤ 256 → d % 8 = 0 → d ≠ 8 * hUsed → word v.mem B d = word s.mem B d := fun d hd h8 hn =>
    fu.word_eq (fun r hr => by
      simp only [hUsed, List.mem_cons, List.not_mem_nil, or_false] at hr hn
      rcases hr with rfl | rfl <;> simp only [slot, hdrBytes] <;> omega) (by omega)
  have hv : Scr v B (8 * L) := hs.congr kvu.wr
  have r128 : v.mem.readW (B + 128#64) 64 = BitVec.ofNat 64 (8 * t) := (vw 128 (by omega) (by decide) (by simp [hUsed])).trans h.topOff
  have r192 : v.mem.readW (B + 192#64) 64 = BitVec.ofNat 64 (2 ^ b - 1) := (vw 192 (by omega) (by decide) (by simp [hUsed])).trans h.top
  have es4 : slot w 4 = 256 + 4 * (8 * (w + 2)) := rfl
  refine WP.mono (WP.keep [.r4, .r5, .r6, .r10] (Q := fun x =>
      x.mem = v.mem.writeW (off B (slot w 4 + 8 * t))
        (word v.mem B (slot w 4 + 8 * t) &&& BitVec.ofNat 64 (2 ^ b - 1)) ∧ x.gpr .r10 = off B (slot w 0))
    ?_ (by decide)) fun x ⟨⟨xm, x10⟩, kx⟩ => ?_
  · rw [WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (Q := fun (y : State) => (y.gpr .r10 = off B (slot w 0) ∧ y.mem = v.mem) ∧ Keep [.r10] v y)
      (WP.keep (Q := fun (y : State) => y.gpr .r10 = off B (slot w 0) ∧ y.mem = v.mem) _
        (by prun [v31, hdrBytes]; simp only [slot, hdrBytes, Nat.zero_mul, Nat.add_zero]) (by decide)) fun y ⟨⟨y10, ym⟩, ky⟩ => ?_
    have ey : Env y B (8 * L) w := ⟨hv.congr ky.wr, y10, (ky.gpr .r29 (by decide)).trans v29,
      (ky.gpr .r11 (by decide)).trans ((kvu.gpr .r11 (by decide)).trans e.h11),
      (ky.gpr .r31 (by decide)).trans v31, hw4, hw128, e.hZ⟩
    refine WP.mono (ey.base (rd := .r5) (by decide) (by decide) 4) fun z ⟨⟨z5, zm⟩, kz⟩ => ?_
    have z31 : z.gpr .r31 = B := (kz.gpr .r31 (by decide)).trans ey.h31
    have hz : Scr z B (8 * L) := ey.hs.congr kz.wr
    have z10 : z.gpr .r10 = off B (slot w 0) := (kz.gpr .r10 (by decide)).trans y10
    simp only [ldh, hTopOff, hTop]
    have ha : slot w 4 + 8 * t + 8 ≤ 8 * L := by simp only [slot, hdrBytes]; omega
    prun [z31, z5, zm, ym, r128, r192, hz.ld (d := 128) (n := 8) (by omega), hz.ld (d := 192) (n := 8) (by omega),
      hz.ld (d := slot w 4 + 8 * t) (n := 8) ha, hz.st (d := slot w 4 + 8 * t) (n := 8) ha]
    exact z10
  · refine ⟨⟨?_, ?_, ?_, x10⟩, (kvu.trans kx).mono (by decide)⟩
    · have ha : slot w 4 + 8 * t + 8 ≤ 2 ^ 64 := by simp only [slot, hdrBytes]; omega
      rw [xm, ← hval]
      refine VG.Proof.RsaKeyGen.wv_cut h.b64 (word_writeW_self _ _ _ _) (fun j hj hjt => ?_) hlt
      exact (writeW_outside _ _ _ ha).word (by omega) (by simp only [slot, hdrBytes]; omega)
    · rw [xm, (writeW_outside _ _ _ (by simp only [slot, hdrBytes]; omega)).word
        (by simp only [hUsed, slot, hdrBytes]; omega) (by simp only [hUsed]; omega)]
      exact (vo.word (by simp only [hUsed, slot, hdrBytes]; omega) (by simp only [hUsed]; omega)).trans
        (by rw [um]; exact word_writeW_self _ _ _ _)
    · refine fu.trans (Frm.of_outside (o := slot w 4) (n := 8 * (w + 2)) ?_ (by simp))
      rw [xm]
      exact (writeW_outside _ _ _ (by simp only [slot, hdrBytes]; omega)).mono (by omega) (by omega)

end VG.Proof.MillerRabin.PPC64LE.Blinded
