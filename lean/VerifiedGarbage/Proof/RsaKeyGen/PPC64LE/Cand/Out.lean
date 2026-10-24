module

public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Candidate
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.ReverseEncoding
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# A candidate on PPC64LE: the outputs

`zeroOut_ok`: `out` zeroed; `finish_ok`: the octets read to `used` and the
result; `finPrime_ok`: `c`, from array 0, to `out`, most significant octet
first (`bytes_of_copy`). `frame_of_outside`: what changes only within a
range of a region changes nothing outside the region.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Candidate (zeroOut finish finNone finPrime)

/-- A change within `[o, o + n)` of `B` is outside the region of `Z ≥ o + n`
bytes at `B`. -/
theorem frame_of_outside {B : Addr} {o n Z : Nat} {m m' : Mem} (h : Outside B o n m m') (hZ : o + n ≤ Z) :
    Frame [⟨B, Z⟩] m m' := fun x hx => h x (Or.inr (by
  have := hx _ List.mem_cons_self
  simp only [Region.Contains, ofs] at this ⊢
  omega))

/-- A change within ranges `[o, o + n)` of `B` is outside the region of
`Z` bytes at `B` that holds them. -/
theorem frame_of_outs {B : Addr} {rs : List (Nat × Nat)} {Z : Nat} {m m' : Mem} (h : Outs B rs m m')
    (hZ : ∀ r ∈ rs, r.1 + r.2 ≤ Z) : Frame [⟨B, Z⟩] m m' := fun x hx => h x fun r hr => Or.inr (by
  have h1 := hx _ List.mem_cons_self
  have h2 := hZ r hr
  simp only [Region.Contains] at h1
  simp only [ofs]
  omega)

/-- A write of a word within a region of the frame's list. -/
theorem frame_writeW {rs : List Region} {r : Region} (hr : r ∈ rs) (m : Mem) {a : Addr} (v : BitVec 64)
    (ha : r.Contains a 8) : Frame rs m (m.writeW a v) :=
  (Frame.refl rs m).writeW hr v ha

/-- `zeroOut`: the `L` bytes at `O` (`r23`, `L` in `r24`) := 0. -/
theorem zeroOut_ok {s : State} {O : Addr} {L : Nat} (h23 : s.gpr .r23 = O)
    (h24 : s.gpr .r24 = BitVec.ofNat 64 L) (hL : 1 ≤ L) (hL' : L < 2 ^ 32)
    (hO : ∀ i < L, InRegions s.wr (off O i) 1) (hOw : O.toNat + L ≤ 2 ^ 64) :
    WP isa zeroOut s fun t => (∀ c < L, t.mem (off O c) = 0) ∧ Outside O 0 L s.mem t.mem ∧
      Keep [.r0, .r14, .r17] s t := by
  rw [zeroOut, WP.seq_iff]
  have hb : WP isa (.block [.addi .r14 .r23 0, .addi .r17 .r24 0, .li .r0 0]) s fun u =>
      (u.gpr .r0 = 0 ∧ u.gpr .r14 = off O 0 ∧ u.gpr .r17 = BitVec.ofNat 64 L ∧ u.mem = s.mem) ∧
        Keep [.r0, .r14, .r17] s u := by
    refine WP.keep _ ?_ (by decide)
    prun [h23, h24]
    exact ⟨rfl, by simp⟩
  refine WP.mono hb fun u ⟨⟨u0, u14, u17, um⟩, ku⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off O i ∧ t.gpr .r0 = 0 ∧ Outside O 0 i s.mem t.mem ∧ (∀ c < i, t.mem (off O c) = 0) ∧
      Keep [.r0, .r14, .r17] s t
  refine WP.mono (wp_countdown (body := .block ([.stb .r0 .r14 0, .addi .r14 .r14 1] ++
      ([.subi .r17 .r17 1] : List Instr))) (cnt := .r17) (N := L) (by omega) (by omega) Inv
    (fun i hi t ⟨t14, t0, tout, tz, tk⟩ _ => ?_)
    ⟨u14, u0, by rw [um]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega), ku⟩ u17)
    fun t ⟨_, _, tout, tz, tk⟩ => ⟨tz, tout, tk⟩
  have hst : WP isa (.block [.stb .r0 .r14 0, .addi .r14 .r14 1, .subi .r17 .r17 1]) t fun t' =>
      (t'.gpr .r14 = off O (i + 1) ∧ t'.gpr .r0 = 0 ∧ t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.write (off O i) 1 0) ∧ Keep [.r14, .r17] t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [t14, t0, exec_stb (show Reg.r14 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
      (by rw [tk.wr]; exact hO i hi : InRegions t.wr (off O i) 1)]
    rfl
  refine WP.mono hst fun t' ⟨⟨l14, l0, l17, lm⟩, lk⟩ => ⟨⟨l14, l0, ?_, ?_, tk.trans' lk.mono⟩, l17⟩
  · have hw1 := write1_outside t.mem O (d := i) 0 (by omega)
    rw [lm]; exact (tout.mono (o' := 0) (n' := i + 1) (by omega) (by omega)).trans
      (hw1.mono (o' := 0) (n' := i + 1) (by omega) (by omega))
  · have hw1 := write1_outside t.mem O (d := i) 0 (by omega)
    intro c hc
    rw [lm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | rfl
    · rw [hw1 _ (by rw [Mont.ofs_off0 O (by omega)]; omega)]; exact tz c hc
    · rw [write1_self]

/-- `finish r`: `used := r28` (at `U`, in `r25`), and the result `r`. -/
theorem finish_ok (r : Nat) {s : State} {U : Addr} (h25 : s.gpr .r25 = U) (hU : InRegions s.wr U 8)
    (hr : r < 2 ^ 15) :
    WP isa (finish r) s fun t =>
      (t.mem = s.mem.writeW U (s.gpr .r28) ∧ t.gpr .r3 = BitVec.ofNat 64 r) ∧ Keep [.r3] s t := by
  refine WP.keep _ ?_ rfl rfl
  have hU' : InRegions s.wr (s.gpr .r25 + BitVec.ofNat 64 0) 8 := by rw [h25, BitVec.add_zero]; exact hU
  prun [finish, exec_store_d (show Reg.r25 ≠ .r0 by decide) (show 0 < 2 ^ 15 ∧ 0 % 4 = 0 by decide) hU',
    h25, exec_li hr]
  rw [BitVec.add_zero]

/-- `finNone`: `used := 0` and the result 0. -/
theorem finNone_ok {s : State} {U : Addr} (h25 : s.gpr .r25 = U) (hU : InRegions s.wr U 8) :
    WP isa finNone s fun t =>
      (t.mem = s.mem.writeW U (0 : BitVec 64) ∧ t.gpr .r3 = BitVec.ofNat 64 0 ∧ t.gpr .r28 = 0) ∧
        Keep [.r28, .r3] s t := by
  rw [finNone, WP.seq_iff]
  have hb : WP isa (.block [.li .r28 0]) s fun u => (u.gpr .r28 = 0 ∧ u.mem = s.mem ∧ u.gpr .r25 = U) ∧
      Keep [.r28] s u := by
    refine WP.keep _ ?_ (by decide)
    prun [h25]
    rfl
  refine WP.mono hb fun u ⟨⟨u28, um, u25⟩, ku⟩ => ?_
  refine WP.mono (finish_ok 0 u25 (by rw [ku.wr]; exact hU) (by decide)) fun t ⟨⟨tm, t3⟩, kt⟩ =>
    ⟨⟨by rw [tm, um, u28], t3, by rw [kt.gpr _ (by decide)]; exact u28⟩, ku.trans kt⟩

/-- The `L` octets at `O` reversed from the `L` octets at `d` of `B`: their
number, most significant first. -/
theorem bytes_of_copy {m m' : Mem} {B O : Addr} {d w L : Nat} (hL : L = 8 * w)
    (hb : ∀ c < L, m' (off O c) = m (off B (d + (L - 1 - c)))) :
    Spec.Rsa.bytesAt m' O L = Spec.Rsa.i2osp (val32 m B d (2 * w)) L := by
  have hr := VG.Proof.Bignum.reversed_read m' m O (off B d) L fun c hc => by
    rw [off_add]
    have := hb (L - 1 - c) (by omega)
    rw [show L - 1 - (L - 1 - c) = c by omega] at this
    rw [← this]
  have e := VG.Proof.Bignum.read_eq_val32 m B (2 * w) d
  rw [show 4 * (2 * w) = L by omega] at e
  rw [← e, hr]
  have hl : (Spec.Rsa.bytesAt m' O L).length = L := by simp [Spec.Rsa.bytesAt]
  have e2 := VG.Proof.Rsa.i2osp_os2ip (Spec.Rsa.bytesAt m' O L)
  rw [hl] at e2
  exact e2.symm

/-- The copy of `finPrime`: the `L` octets at `256` of `B` (`r31`, `L` in
`r24`), reversed, to the `L` octets at `O` (`r23`). -/
theorem copyOut_ok {s : State} {B O : Addr} {Z L : Nat} (hs : Scr s B Z) (h31 : s.gpr .r31 = B)
    (h23 : s.gpr .r23 = O) (h24 : s.gpr .r24 = BitVec.ofNat 64 L) (hL : 1 ≤ L) (hZ : 256 + L ≤ Z)
    (hO : ∀ i < L, InRegions s.wr (off O i) 1) (hOw : O.toNat + L ≤ 2 ^ 64)
    (hsep : ∀ i < L, ∀ x, ofs B x < Z → off O i ≠ x) :
    WP isa (.seq (.block [.addi .r10 .r31 VG.Impl.Bignum.hdrBytes, .add .r15 .r10 .r24, .subi .r15 .r15 1,
        .addi .r16 .r23 0, .addi .r17 .r24 0])
      (VG.Impl.Bignum.PPC64LE.Precompute.countLoop .r17 [.lbz .r0 .r15 0, .stb .r0 .r16 0, .addi .r16 .r16 1,
        .subi .r15 .r15 1])) s fun t =>
      (∀ c < L, t.mem (off O c) = s.mem (off B (256 + (L - 1 - c)))) ∧ Outside O 0 L s.mem t.mem ∧
        Keep [.r0, .r10, .r15, .r16, .r17] s t := by
  have hnw := hs.nowrap
  rw [WP.seq_iff]
  have hb : WP isa (.block [.addi .r10 .r31 VG.Impl.Bignum.hdrBytes, .add .r15 .r10 .r24, .subi .r15 .r15 1,
        .addi .r16 .r23 0, .addi .r17 .r24 0]) s fun u =>
      (u.gpr .r15 = off B (256 + L - 1) ∧ u.gpr .r16 = off O 0 ∧ u.gpr .r17 = BitVec.ofNat 64 L ∧
        u.mem = s.mem) ∧ Keep [.r10, .r15, .r16, .r17] s u := by
    refine WP.keep _ ?_ (by decide)
    prun [h31, h23, h24, VG.Impl.Bignum.hdrBytes]
    refine ⟨?_, by simp⟩
    rw [off_sub1 _ (by omega)]
  refine WP.mono hb fun u ⟨⟨u15, u16, u17, um⟩, ku⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r15 = off B (256 + L - 1 - i) ∧ t.gpr .r16 = off O i ∧ Outside O 0 i s.mem t.mem ∧
      (∀ c < i, t.mem (off O c) = s.mem (off B (256 + (L - 1 - c)))) ∧ Keep [.r0, .r10, .r15, .r16, .r17] s t
  refine WP.mono (wp_countdown (body := .block ([.lbz .r0 .r15 0, .stb .r0 .r16 0, .addi .r16 .r16 1,
      .subi .r15 .r15 1] ++ ([.subi .r17 .r17 1] : List Instr))) (cnt := .r17) (N := L) (by omega) (by omega) Inv
    (fun i hi t ⟨t15, t16, tout, tb, tk⟩ _ => ?_)
    ⟨by rw [u15]; rfl, u16, by rw [um]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega), ku.mono⟩ u17)
    fun t ⟨_, _, tout, tb, tk⟩ => ⟨tb, tout, tk⟩
  have hst : WP isa (.block [.lbz .r0 .r15 0, .stb .r0 .r16 0, .addi .r16 .r16 1, .subi .r15 .r15 1,
      .subi .r17 .r17 1]) t fun t' =>
        (t'.gpr .r15 = off B (256 + L - 1 - i) - BitVec.ofNat 64 1 ∧ t'.gpr .r16 = off O (i + 1) ∧
          t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 ∧
          t'.mem = t.mem.write (off O i) 1 (t.mem (off B (256 + L - 1 - i)))) ∧
        Keep [.r0, .r15, .r16, .r17] t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [t15, t16, exec_lbz' (show Reg.r15 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
      exec_stb (show Reg.r16 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
      (hs.congr tk.wr).ld (d := 256 + L - 1 - i) (n := 1) (by omega),
      (by rw [tk.wr]; exact hO i hi : InRegions t.wr (off O i) 1), read_one']
  refine WP.mono hst fun t' ⟨⟨l15, l16, l17, lm⟩, lk⟩ => ⟨⟨?_, l16, ?_, ?_, tk.trans' lk.mono⟩, l17⟩
  · rw [l15, off_sub1 _ (by omega), show 256 + L - 1 - i - 1 = 256 + L - 1 - (i + 1) by omega]
  · have hw1 := write1_outside t.mem O (d := i) (t.mem (off B (256 + L - 1 - i))) (by omega)
    rw [lm]; exact (tout.mono (o' := 0) (n' := i + 1) (by omega) (by omega)).trans
      (hw1.mono (o' := 0) (n' := i + 1) (by omega) (by omega))
  · have hw1 := write1_outside t.mem O (d := i) (t.mem (off B (256 + L - 1 - i))) (by omega)
    intro c hc
    rw [lm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | rfl
    · rw [hw1 _ (by rw [Mont.ofs_off0 O (by omega)]; omega)]; exact tb c hc
    · rw [write1_self, show 256 + (L - 1 - c) = 256 + L - 1 - c by omega]
      refine tout _ (Or.inr ?_)
      by_contra hlt
      have hx : off O (ofs O (off B (256 + L - 1 - c))) = off B (256 + L - 1 - c) := by
        simp only [off, ofs, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        rw [BitVec.add_comm]; exact BitVec.sub_add_cancel _ _
      exact hsep _ (by omega) _ (by rw [Mont.ofs_off0 B (by omega)]; omega) hx

end VG.Proof.RsaKeyGen.PPC64LE.Cand
