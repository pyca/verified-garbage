module

public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.RsaKeyGen.CandidateContract
public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Candidate
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBase
import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.ReverseEncoding
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Block

/-! ### `RsaKeyGen.PPC64LE.Cand.Out`, which this module and modules that import it used -/

section

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
  omega_using [hZ, this]))

/-- A change within ranges `[o, o + n)` of `B` is outside the region of
`Z` bytes at `B` that holds them. -/
theorem frame_of_outs {B : Addr} {rs : List (Nat × Nat)} {Z : Nat} {m m' : Mem} (h : Outs B rs m m')
    (hZ : ∀ r ∈ rs, r.1 + r.2 ≤ Z) : Frame [⟨B, Z⟩] m m' := fun x hx => h x fun r hr => Or.inr (by
  have h1 := hx _ List.mem_cons_self
  have h2 := hZ r hr
  simp only [Region.Contains] at h1
  simp only [ofs]
  omega_using [h1, h2])

/-- Octets survive what keeps their bytes. -/
theorem bytes_keep {rs : List Region} {m m' : Mem} (f : Frame rs m m') {Ra : Addr} {rl : Nat} (hrl : rl < 2 ^ 64)
    (hd : ∀ ρ ∈ rs, (⟨Ra, rl⟩ : Region).Disjoint ρ) : Spec.Rsa.bytesAt m' Ra rl = Spec.Rsa.bytesAt m Ra rl := by
  unfold Spec.Rsa.bytesAt
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  exact f _ fun ρ hρ => hd ρ hρ _ (Offset.contains_base Ra (by omega_using [hi]) (by omega_using [hrl, hi]))

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
      ([.subi .r17 .r17 1] : List Instr))) (cnt := .r17) (N := L) (by omega_using [hL']) (by omega_using [hL]) Inv
    (fun i hi t ⟨t14, t0, tout, tz, tk⟩ _ => ?_)
    ⟨u14, u0, by rw [um]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega_using []), ku⟩ u17)
    fun t ⟨_, _, tout, tz, tk⟩ => ⟨tz, tout, tk⟩
  have hst : WP isa (.block [.stb .r0 .r14 0, .addi .r14 .r14 1, .subi .r17 .r17 1]) t fun t' =>
      (t'.gpr .r14 = off O (i + 1) ∧ t'.gpr .r0 = 0 ∧ t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.write (off O i) 1 0) ∧ Keep [.r14, .r17] t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [t14, t0, exec_stb (show Reg.r14 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
      (by rw [tk.wr]; exact hO i hi : InRegions t.wr (off O i) 1)]
    rfl
  refine WP.mono hst fun t' ⟨⟨l14, l0, l17, lm⟩, lk⟩ => ⟨⟨l14, l0, ?_, ?_, tk.trans' lk.mono⟩, l17⟩
  · have hw1 := write1_outside t.mem O (d := i) 0 (by omega_using [hL', hi])
    rw [lm]; exact (tout.mono (o' := 0) (n' := i + 1) (by omega_using []) (by omega_using [])).trans
      (hw1.mono (o' := 0) (n' := i + 1) (by omega_using []) (by omega_using []))
  · have hw1 := write1_outside t.mem O (d := i) 0 (by omega_using [hL', hi])
    intro c hc
    rw [lm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | rfl
    · rw [hw1 _ (by rw [Mont.ofs_off0 O (by omega_arith)]; omega_using [hc])]; exact tz c hc
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
    have := hb (L - 1 - c) (by omega_using [hc])
    rw [show L - 1 - (L - 1 - c) = c by omega_using [hc]] at this
    rw [← this]
  have e := VG.Proof.Bignum.read_eq_val32 m B (2 * w) d
  rw [show 4 * (2 * w) = L by omega_using [hL]] at e
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
    rw [off_sub1 _ (by omega_using [])]
  refine WP.mono hb fun u ⟨⟨u15, u16, u17, um⟩, ku⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r15 = off B (256 + L - 1 - i) ∧ t.gpr .r16 = off O i ∧ Outside O 0 i s.mem t.mem ∧
      (∀ c < i, t.mem (off O c) = s.mem (off B (256 + (L - 1 - c)))) ∧ Keep [.r0, .r10, .r15, .r16, .r17] s t
  refine WP.mono (wp_countdown (body := .block ([.lbz .r0 .r15 0, .stb .r0 .r16 0, .addi .r16 .r16 1,
      .subi .r15 .r15 1] ++ ([.subi .r17 .r17 1] : List Instr))) (cnt := .r17) (N := L) (by omega_using [hZ, hnw]) (by omega_using [hL]) Inv
    (fun i hi t ⟨t15, t16, tout, tb, tk⟩ _ => ?_)
    ⟨by rw [u15]; rfl, u16, by rw [um]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega_using []), ku.mono⟩ u17)
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
      (hs.congr tk.wr).ld (d := 256 + L - 1 - i) (n := 1) (by omega_using [hZ]),
      (by rw [tk.wr]; exact hO i hi : InRegions t.wr (off O i) 1), read_one']
  refine WP.mono hst fun t' ⟨⟨l15, l16, l17, lm⟩, lk⟩ => ⟨⟨?_, l16, ?_, ?_, tk.trans' lk.mono⟩, l17⟩
  · rw [l15, off_sub1 _ (by omega_using [hi]), show 256 + L - 1 - i - 1 = 256 + L - 1 - (i + 1) by omega_using []]
  · have hw1 := write1_outside t.mem O (d := i) (t.mem (off B (256 + L - 1 - i))) (by omega_using [hOw, hi])
    rw [lm]; exact (tout.mono (o' := 0) (n' := i + 1) (by omega_using []) (by omega_using [])).trans
      (hw1.mono (o' := 0) (n' := i + 1) (by omega_using []) (by omega_using []))
  · have hw1 := write1_outside t.mem O (d := i) (t.mem (off B (256 + L - 1 - i))) (by omega_using [hOw, hi])
    intro c hc
    rw [lm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | rfl
    · rw [hw1 _ (by rw [Mont.ofs_off0 O (by omega_arith)]; omega_using [hc])]; exact tb c hc
    · rw [write1_self, show 256 + (L - 1 - c) = 256 + L - 1 - c by omega_using [hi]]
      refine tout _ (Or.inr ?_)
      by_contra hlt
      have hx : off O (ofs O (off B (256 + L - 1 - c))) = off B (256 + L - 1 - c) := by
        simp only [off, ofs, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        rw [BitVec.add_comm]; exact BitVec.sub_add_cancel _ _
      exact hsep _ (by omega_using [hi, hlt]) _ (by rw [Mont.ofs_off0 B (by omega_using [hZ, hnw])]; omega_using [hZ]) hx

end VG.Proof.RsaKeyGen.PPC64LE.Cand

end

end

/-! ### `RsaKeyGen.PPC64LE.Cand.Frame`, which only this module used -/

section

/-! ### `RsaKeyGen.PPC64LE.Cand.Pre`, which only this module used -/

section

/-!
# A candidate on PPC64LE: the contract's arguments

`CIn s`: the shared contract's precondition (`Proof.RsaKeyGen.candidateContract`,
with 400 bytes of stack), without the table of small primes, as the proof
uses it: `(out, out_len, used, e, e_len, p, p_len, rand)` in
`r3`–`r10`, and `rand_len`, `scratch` and `scratch_len` the stack arguments
0–2.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE

/-- The arguments' regions. -/
abbrev cO (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
abbrev cU (s : State) : Region := ⟨s.gpr .r5, 8⟩
abbrev cE (s : State) : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
abbrev cP (s : State) : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
abbrev cR (s : State) : Region := ⟨s.gpr .r10, (PPC64LE.stackArg s 0).toNat⟩
abbrev cS (s : State) : Region := ⟨PPC64LE.stackArg s 1, (PPC64LE.stackArg s 2).toNat * 8⟩
abbrev cA (s : State) : Region := ⟨stackArgAddr s 0, 24⟩
/-- The stack the code uses: its frames and the round's. -/
abbrev cF (s : State) : Region := below s.sp 400

/-- The contract's precondition. -/
structure CIn (s : State) : Prop where
  spLo : 400 ≤ s.sp.toNat
  spHi : s.sp.toNat + 32 + 8 * 11 ≤ 2 ^ 64
  rE : cE s ∈ s.rd
  rP : cP s ∈ s.rd
  rR : cR s ∈ s.rd
  rA : cA s ∈ s.rd
  wr : s.wr = [cO s, cU s, cS s]
  oU : (cO s).Disjoint (cU s)
  oE : (cO s).Disjoint (cE s)
  oP : (cO s).Disjoint (cP s)
  oR : (cO s).Disjoint (cR s)
  oS : (cO s).Disjoint (cS s)
  oA : (cO s).Disjoint (cA s)
  uE : (cU s).Disjoint (cE s)
  uP : (cU s).Disjoint (cP s)
  uR : (cU s).Disjoint (cR s)
  uS : (cU s).Disjoint (cS s)
  uA : (cU s).Disjoint (cA s)
  eS : (cE s).Disjoint (cS s)
  pS : (cP s).Disjoint (cS s)
  rS : (cR s).Disjoint (cS s)
  SA : (cS s).Disjoint (cA s)
  Fo : (cF s).Disjoint (cO s)
  Fu : (cF s).Disjoint (cU s)
  Fe : (cF s).Disjoint (cE s)
  Fp : (cF s).Disjoint (cP s)
  Fr : (cF s).Disjoint (cR s)
  FS : (cF s).Disjoint (cS s)
  FA : (cF s).Disjoint (cA s)
  fo : (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64
  fu : (s.gpr .r5).toNat + 8 ≤ 2 ^ 64
  fe : (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64
  fp : (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64
  fr : (s.gpr .r10).toNat + (PPC64LE.stackArg s 0).toNat ≤ 2 ^ 64
  fS : (PPC64LE.stackArg s 1).toNat + (PPC64LE.stackArg s 2).toNat * 8 ≤ 2 ^ 64
  valid : Spec.RsaKeyGen.primeLenValid (s.gpr .r4).toNat
  el1 : 1 ≤ (s.gpr .r7).toNat
  el2 : (s.gpr .r7).toNat ≤ 8
  plv : (s.gpr .r9).toNat = 0 ∨ (s.gpr .r9).toNat = (s.gpr .r4).toNat
  scr : Spec.Rsa.scratchWords (s.gpr .r4).toNat ≤ (PPC64LE.stackArg s 2).toNat

theorem stackArgs_three (s : State) :
    List.map (PPC64LE.stackArg s) (List.range 3) = [PPC64LE.stackArg s 0, PPC64LE.stackArg s 1,
      PPC64LE.stackArg s 2] := rfl

end VG.Proof.RsaKeyGen.PPC64LE.Cand

end

end


/-!
# A candidate on PPC64LE: the frames and the entry

The 400 bytes below the stack pointer on entry, from `cB s0` up: the 176
bytes the round's calls use, then the frame of 176 bytes from `cB + 176`
(the stack pointer of the body: its back chain and header, then `r14`–`r31`
saved from `cB + 208`), then the frame of 48 bytes holding the return
address (at `cB + 384`). `Bx s0 s`: what holds through the body, from the
initial state `s0`: the stack pointer and the permissions, the return address
and the saved registers in the frames, and memory elsewhere but in `out`,
`used`, `scratch` and the stack as `s0`'s. `entry_ok`: the entry's saves and
moves.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Candidate (entry saved frameBytes)

/-- The lowest byte of the stack used. -/
abbrev cB (s0 : State) : Addr := s0.sp - BitVec.ofNat 64 400

/-- The `i`-th register saved. -/
def savedR (i : Nat) : Reg := saved.getD i .r14

/-- The state the body starts from: the return address in `r0`, pushed, and
the frame allocated. -/
def started (s0 : State) : State := allocated 176 (pushed .r0 (s0.write .r0 s0.lr))

/-- The writable regions of the body. -/
abbrev bodyWr (s0 : State) : List Region :=
  ⟨off (cB s0) 208, 144⟩ :: ⟨off (cB s0) 384, 16⟩ :: s0.wr

/-- What holds through the body. -/
structure Bx (s0 s : State) : Prop where
  pre : CIn s0
  sp : s.sp = off (cB s0) 176
  rd : s.rd = s0.rd
  wr : s.wr = bodyWr s0
  out : Frame [cO s0, cU s0, cS s0, cF s0] s0.mem s.mem
  lr : s.mem.readW (off (cB s0) 384) 64 = s0.lr
  sv : ∀ i < 18, s.mem.readW (off (cB s0) (208 + 8 * i)) 64 = s0.gpr (savedR i)
  r2 : s.gpr .r2 = s0.gpr .r2


theorem entry_eq : entry = ([.addSp .r11 0, .store .d .r14 .r11 32, .store .d .r15 .r11 40,
    .store .d .r16 .r11 48, .store .d .r17 .r11 56, .store .d .r18 .r11 64, .store .d .r19 .r11 72,
    .store .d .r20 .r11 80, .store .d .r21 .r11 88, .store .d .r22 .r11 96, .store .d .r23 .r11 104,
    .store .d .r24 .r11 112, .store .d .r25 .r11 120, .store .d .r26 .r11 128, .store .d .r27 .r11 136,
    .store .d .r28 .r11 144, .store .d .r29 .r11 152, .store .d .r30 .r11 160, .store .d .r31 .r11 168,
    .addi .r23 .r3 0, .addi .r24 .r4 0, .addi .r25 .r5 0, .addi .r21 .r6 0, .addi .r30 .r7 0,
    .addi .r18 .r8 0, .addi .r19 .r9 0, .addi .r26 .r10 0] : List Instr) ++
    ([.addSp .r27 320, .load .d .r27 .r27 0, .addSp .r31 328, .load .d .r31 .r31 0, .addSp .r11 336,
      .load .d .r11 .r11 0, .li .r28 0] : List Instr) := rfl

/-- What holds when the body starts. -/
structure St0 (s0 s : State) : Prop where
  pre : CIn s0
  sp : s.sp = off (cB s0) 176
  rd : s.rd = s0.rd
  wr : s.wr = bodyWr s0
  out : Frame [cF s0] s0.mem s.mem
  lr : s.mem.readW (off (cB s0) 384) 64 = s0.lr
  gpr : ∀ r, r ≠ .r0 → s.gpr r = s0.gpr r

/-- The memory after the first `k` saves. -/
def saveMem (s0 : State) (m : Mem) : Nat → Mem
  | 0 => m
  | k + 1 => (saveMem s0 m k).writeW (off (cB s0) (208 + 8 * k)) (s0.gpr (savedR k))

theorem cB_fit {s0 : State} (h : CIn s0) : (cB s0).toNat + 400 ≤ 2 ^ 64 := by
  have := h.spLo
  simp only [cB, BitVec.toNat_sub_of_le (show BitVec.ofNat 64 400 ≤ s0.sp by
    rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [this]), BitVec.toNat_ofNat]
  have := s0.sp.isLt
  omega_using []

/-- A word at an offset of the frames, through a write of another. -/
theorem fr_sep (m : Mem) (B : Addr) {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (off B e) v).readW (off B d) 64 = m.readW (off B d) 64 :=
  Mem.readW_writeW_sep (Offset.sep B h hd he) (by decide)

theorem saveMem_sv (s0 : State) (m : Mem) :
    ∀ k ≤ 18, ∀ i < k, (saveMem s0 m k).readW (off (cB s0) (208 + 8 * i)) 64 = s0.gpr (savedR i)
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | k + 1, hk, i, hi => by
    rw [saveMem]
    by_cases e : i = k
    · subst e; exact Mem.readW_writeW_self64 _ _ _
    · rw [fr_sep _ _ _ (by omega_using [e]) (by omega_using [hk, hi]) (by omega_using [hk])]
      exact saveMem_sv s0 m k (by omega_using [hk]) i (by omega_using [hi, e])

theorem saveMem_rd (s0 : State) (m : Mem) {d : Nat} (hd : 352 ≤ d) (hd' : d + 8 ≤ 2 ^ 64) :
    ∀ k ≤ 18, (saveMem s0 m k).readW (off (cB s0) d) 64 = m.readW (off (cB s0) d) 64
  | 0, _ => rfl
  | k + 1, hk => by
    rw [saveMem, fr_sep _ _ _ (by omega_using [hd, hk]) hd' (by omega_using [hk])]
    exact saveMem_rd s0 m hd hd' k (by omega_using [hk])

theorem saveMem_frame {s0 : State} (h : CIn s0) (m : Mem) : ∀ k ≤ 18, Frame [cF s0] m (saveMem s0 m k)
  | 0, _ => Frame.refl _ _
  | k + 1, hk => by
    have := cB_fit h
    rw [saveMem]
    exact (saveMem_frame h m k (by omega_using [hk])).writeW (r := cF s0) (by simp) _
      (by show (⟨cB s0, 400⟩ : Region).Contains (cB s0 + BitVec.ofNat 64 (208 + 8 * k)) 8
          exact Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk]))

/-- The stack argument `i < 3` is readable, at `cB + 496 + 8 i`. -/
theorem argAddr (s0 : State) (i : Nat) : stackArgAddr s0 i = off (cB s0) (496 + 8 * i) := by
  show s0.sp + BitVec.ofNat 64 (32 + 8 * (8 + i)) = s0.sp - BitVec.ofNat 64 400 + BitVec.ofNat 64 (496 + 8 * i)
  rw [show 496 + 8 * i = 400 + (32 + 8 * (8 + i)) by omega_using []]
  rw [show BitVec.ofNat 64 (400 + (32 + 8 * (8 + i))) = BitVec.ofNat 64 400 + BitVec.ofNat 64 (32 + 8 * (8 + i))
    from (BitVec.ofNat_add_ofNat _ _).symm, ← BitVec.add_assoc, BitVec.sub_add_cancel]

/-- The pointers and lengths after the entry. -/
structure Regs (s0 s : State) : Prop where
  r23 : s.gpr .r23 = s0.gpr .r3
  r24 : s.gpr .r24 = s0.gpr .r4
  r25 : s.gpr .r25 = s0.gpr .r5
  r21 : s.gpr .r21 = s0.gpr .r6
  r30 : s.gpr .r30 = s0.gpr .r7
  r18 : s.gpr .r18 = s0.gpr .r8
  r19 : s.gpr .r19 = s0.gpr .r9
  r26 : s.gpr .r26 = s0.gpr .r10
  r27 : s.gpr .r27 = PPC64LE.stackArg s0 0
  r31 : s.gpr .r31 = PPC64LE.stackArg s0 1
  r11 : s.gpr .r11 = PPC64LE.stackArg s0 2
  r28 : s.gpr .r28 = 0

theorem entry_ok {s0 s : State} (h : St0 s0 s) :
    WP isa (.block entry) s fun t => Bx s0 t ∧ Regs s0 t := by
  have hp := h.pre
  obtain hf := cB_fit hp
  obtain hw : ∀ d, 208 ≤ d → d + 8 ≤ 352 → InRegions s.wr (off (cB s0) d) 8 := fun d h1 h2 =>
    ⟨_, by rw [h.wr]; exact List.mem_cons_self, Offset.contains _ h1 (by omega_using [h2]) (by omega_using [])⟩
  rw [entry_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.r11, .r18, .r19, .r21, .r23, .r24, .r25, .r26, .r30] (Q := fun t =>
      t.mem = saveMem s0 s.mem 18 ∧ t.gpr .r23 = s0.gpr .r3 ∧ t.gpr .r24 = s0.gpr .r4 ∧
      t.gpr .r25 = s0.gpr .r5 ∧ t.gpr .r21 = s0.gpr .r6 ∧ t.gpr .r30 = s0.gpr .r7 ∧ t.gpr .r18 = s0.gpr .r8 ∧
      t.gpr .r19 = s0.gpr .r9 ∧ t.gpr .r26 = s0.gpr .r10) ?_ (by decide))
    fun t ⟨⟨m, a23, a24, a25, a21, a30, a18, a19, a26⟩, k⟩ => ?_
  · prun [VG.Proof.Rsa.PPC64LE.CrtValues.exec_addSp, h.sp, BitVec.add_zero, hw 208 (by decide) (by decide),
      hw 216 (by decide) (by decide),
      hw 224 (by decide) (by decide),
      hw 232 (by decide) (by decide),
      hw 240 (by decide) (by decide),
      hw 248 (by decide) (by decide),
      hw 256 (by decide) (by decide),
      hw 264 (by decide) (by decide),
      hw 272 (by decide) (by decide),
      hw 280 (by decide) (by decide),
      hw 288 (by decide) (by decide),
      hw 296 (by decide) (by decide),
      hw 304 (by decide) (by decide),
      hw 312 (by decide) (by decide),
      hw 320 (by decide) (by decide),
      hw 328 (by decide) (by decide),
      hw 336 (by decide) (by decide),
      hw 344 (by decide) (by decide)]
    rw [h.gpr .r14 (by decide), h.gpr .r15 (by decide), h.gpr .r16 (by decide), h.gpr .r17 (by decide), h.gpr .r18 (by decide), h.gpr .r19 (by decide), h.gpr .r20 (by decide), h.gpr .r21 (by decide), h.gpr .r22 (by decide), h.gpr .r23 (by decide), h.gpr .r24 (by decide), h.gpr .r25 (by decide), h.gpr .r26 (by decide), h.gpr .r27 (by decide), h.gpr .r28 (by decide), h.gpr .r29 (by decide), h.gpr .r30 (by decide), h.gpr .r31 (by decide), h.gpr .r3 (by decide), h.gpr .r4 (by decide), h.gpr .r5 (by decide), h.gpr .r6 (by decide), h.gpr .r7 (by decide), h.gpr .r8 (by decide), h.gpr .r9 (by decide), h.gpr .r10 (by decide)]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain hsp : t.sp = off (cB s0) 176 := k.sp.trans h.sp
  obtain hrd : t.rd = s0.rd := k.rd.trans h.rd
  have fA : (cA s0).Disjoint (cF s0) := hp.FA.symm
  obtain hA : cA s0 = ⟨off (cB s0) 496, 24⟩ := by rw [cA, argAddr, Nat.mul_zero, Nat.add_zero]
  obtain ra : ∀ i < 3, InRegions (t.rd ++ t.wr) (off (cB s0) (496 + 8 * i)) 8 := fun i hi =>
    ⟨cA s0, List.mem_append_left _ (by rw [hrd]; exact hp.rA),
      by rw [hA]; exact Offset.contains _ (by omega_using []) (by omega_using [hi]) (by omega_using [])⟩
  obtain va : ∀ i < 3, t.mem.readW (off (cB s0) (496 + 8 * i)) 64 = PPC64LE.stackArg s0 i := fun i hi => by
    rw [m, saveMem_rd s0 s.mem (by omega_using []) (by omega_using [hi]) 18 (by decide), PPC64LE.stackArg, argAddr]
    exact h.out.readW (r := cA s0) (by rw [hA]; exact Offset.contains _ (by omega_using []) (by omega_using [hi]) (by omega_using []))
      (by simp only [List.mem_singleton, forall_eq]; exact fA) (by decide)
  obtain va0 := va 0 (by decide)
  obtain va1 := va 1 (by decide)
  obtain va2 := va 2 (by decide)
  obtain ra0 := ra 0 (by decide)
  obtain ra1 := ra 1 (by decide)
  obtain ra2 := ra 2 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul, Nat.reduceAdd] at va0 va1 va2 ra0 ra1 ra2
  refine WP.mono (WP.keep [.r27, .r31, .r11, .r28] (Q := fun u => u.mem = t.mem ∧
      u.gpr .r27 = PPC64LE.stackArg s0 0 ∧ u.gpr .r31 = PPC64LE.stackArg s0 1 ∧
      u.gpr .r11 = PPC64LE.stackArg s0 2 ∧ u.gpr .r28 = 0) ?_ (by decide))
    fun u ⟨⟨um, u27, u31, u11, u28⟩, ku⟩ => ?_
  · prun [VG.Proof.Rsa.PPC64LE.CrtValues.exec_addSp, hsp, BitVec.add_zero, ra0, ra1, ra2, va0, va1, va2]
    rfl
  · have ks := ku.sp.trans hsp
    refine ⟨⟨hp, ks, ku.rd.trans hrd, ku.wr.trans (k.wr.trans h.wr), ?_, ?_, fun i hi => ?_, ?_⟩,
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, u27, u31, u11, u28⟩⟩
    · rw [um, m]
      exact (h.out.trans (saveMem_frame hp s.mem 18 (by decide))).mono (by simp)
    · rw [um, m, saveMem_rd s0 s.mem (by omega_using []) (by omega_using []) 18 (by decide)]; exact h.lr
    · rw [um, m]; exact saveMem_sv s0 s.mem 18 (by decide) i hi
    · rw [ku.gpr _ (by decide), k.gpr _ (by decide), h.gpr _ (by decide)]
    all_goals first
      | (rw [ku.gpr _ (by decide)]; with_reducible assumption)

/-! ## The frames -/

theorem write8 (m : Mem) (a : Addr) (v : BitVec 64) : m.write a 8 v = m.writeW a v := by
  simp only [Mem.writeW, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]

theorem read8 (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp only [Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq]

theorem started_mem (s0 : State) : (started s0).mem =
    ((s0.mem.writeW (off (cB s0) 352) s0.sp).writeW (off (cB s0) 384) s0.lr).writeW (off (cB s0) 176)
      (s0.sp - 48) := by
  show ((s0.mem.write (s0.sp - 48) 8 s0.sp).write (s0.sp - 48 + 32) 8 s0.lr).write
    (s0.sp - 48 - BitVec.ofNat 64 176) 8 (s0.sp - 48) = _
  obtain h₁ : s0.sp - 48 = off (cB s0) 352 := by simp only [off, cB]; bv_omega
  obtain h₂ : s0.sp - 48 + 32 = off (cB s0) 384 := by simp only [off, cB]; bv_omega
  obtain h₃ : s0.sp - 48 - BitVec.ofNat 64 176 = off (cB s0) 176 := by simp only [off, cB]; bv_omega
  rw [h₃, h₂, write8, write8, write8, ← h₁]

theorem started_ok {s0 : State} (h : CIn s0) : St0 s0 (started s0) := by
  obtain hf := cB_fit h
  obtain inF : ∀ d, d + 8 ≤ 400 → (cF s0).Contains (off (cB s0) d) (64 / 8) := fun d hd =>
    Offset.contains_base _ (by omega_using [hd]) (by omega_using [hd])
  refine ⟨h, ?_, rfl, ?_, ?_, ?_, fun r hr => ?_⟩
  · show s0.sp - 48 - BitVec.ofNat 64 176 = off (cB s0) 176
    simp only [off, cB]; bv_omega
  · show (⟨s0.sp - 48 - BitVec.ofNat 64 176 + 32, 176 - 32⟩ : Region) :: ⟨s0.sp - 48 + 32, 16⟩ :: s0.wr = _
    obtain h₁ : s0.sp - 48 - BitVec.ofNat 64 176 + 32 = off (cB s0) 208 := by simp only [off, cB]; bv_omega
    obtain h₂ : s0.sp - 48 + 32 = off (cB s0) 384 := by simp only [off, cB]; bv_omega
    rw [h₁, h₂]
  · rw [started_mem]
    exact (((Frame.refl _ _).writeW (r := cF s0) (by simp) _ (inF 352 (by decide))).writeW (r := cF s0) (by simp) _
      (inF 384 (by decide))).writeW (r := cF s0) (by simp) _ (inF 176 (by decide))
  · rw [started_mem, fr_sep _ _ _ (by omega_using []) (by omega_using []) (by omega_using []), Mem.readW_writeW_self64]
  · show (s0.write .r0 s0.lr).gpr r = s0.gpr r
    simp [State.write, hr]

/-- `Bx` through code that keeps the stack pointer and the permissions, and
writes only `out`, `used`, `scratch` and the stack below the frame. -/
theorem Bx.step {s0 s t : State} (h : Bx s0 s) (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (f : Frame [cO s0, cU s0, cS s0, below (off (cB s0) 176) 176] s.mem t.mem) (r2 : t.gpr .r2 = s.gpr .r2) :
    Bx s0 t := by
  have hp := h.pre
  obtain hf := cB_fit hp
  obtain bF : below (off (cB s0) 176) 176 = ⟨cB s0, 176⟩ := by
    simp only [below, off, BitVec.add_sub_cancel]
  obtain dF : ∀ d, 176 ≤ d → d + 8 ≤ 400 → ∀ r ∈ [cO s0, cU s0, cS s0, below (off (cB s0) 176) 176],
      Region.Disjoint ⟨off (cB s0) d, 8⟩ r := by
    intro d h1 h2 r hr
    obtain sub : Region.Sub ⟨off (cB s0) d, 8⟩ (cF s0) := Offset.sub_base _ (by omega_using [h2])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.Fo.sub_left sub
    · exact hp.Fu.sub_left sub
    · exact hp.FS.sub_left sub
    · rw [bF]; exact Offset.disjoint_base _ (by omega_using [h1]) (by omega_using [h2])
  obtain rdW : ∀ d, 176 ≤ d → d + 8 ≤ 400 → t.mem.readW (off (cB s0) d) 64 = s.mem.readW (off (cB s0) d) 64 :=
    fun d h1 h2 => f.readW (Region.contains_self _ _) (dF d h1 h2) (by decide)
  refine ⟨hp, sp.trans h.sp, rd.trans h.rd, wr.trans h.wr, ?_, ?_, fun i hi => ?_, r2.trans h.r2⟩
  · refine h.out.trans (f.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨cF s0, by simp, by rw [bF]; exact Region.sub_prefix (by decide)⟩
  · rw [rdW 384 (by decide) (by decide)]; exact h.lr
  · rw [rdW _ (by omega_using []) (by omega_using [hi])]; exact h.sv i hi

theorem restore_eq : VG.Impl.RsaKeyGen.PPC64LE.Candidate.restore = ([.addSp .r11 0, .load .d .r14 .r11 32, .load .d .r15 .r11 40, .load .d .r16 .r11 48, .load .d .r17 .r11 56, .load .d .r18 .r11 64, .load .d .r19 .r11 72, .load .d .r20 .r11 80, .load .d .r21 .r11 88, .load .d .r22 .r11 96, .load .d .r23 .r11 104, .load .d .r24 .r11 112, .load .d .r25 .r11 120, .load .d .r26 .r11 128, .load .d .r27 .r11 136, .load .d .r28 .r11 144, .load .d .r29 .r11 152, .load .d .r30 .r11 160, .load .d .r31 .r11 168] : List Instr) := rfl

/-- `restore`: the saved registers from the frame. -/
theorem restore_ok {s0 s : State} (h : Bx s0 s) :
    WP isa (.block VG.Impl.RsaKeyGen.PPC64LE.Candidate.restore) s fun t =>
      (∀ i < 18, t.gpr (savedR i) = s0.gpr (savedR i)) ∧ t.mem = s.mem ∧ t.gpr .r3 = s.gpr .r3 ∧
        t.gpr .r2 = s.gpr .r2 ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.lr = s.lr := by
  obtain hf := cB_fit h.pre
  obtain rd : ∀ d, 208 ≤ d → d + 8 ≤ 352 → InRegions (s.rd ++ s.wr) (off (cB s0) d) 8 := fun d h1 h2 =>
    ⟨_, List.mem_append_right _ (by rw [h.wr]; exact List.mem_cons_self), Offset.contains _ h1 (by omega_using [h2]) (by omega_using [])⟩
  obtain sv0 : s.mem.readW (off (cB s0) 208) 64 = s0.gpr .r14 := h.sv 0 (by decide)
  obtain sv1 : s.mem.readW (off (cB s0) 216) 64 = s0.gpr .r15 := h.sv 1 (by decide)
  obtain sv2 : s.mem.readW (off (cB s0) 224) 64 = s0.gpr .r16 := h.sv 2 (by decide)
  obtain sv3 : s.mem.readW (off (cB s0) 232) 64 = s0.gpr .r17 := h.sv 3 (by decide)
  obtain sv4 : s.mem.readW (off (cB s0) 240) 64 = s0.gpr .r18 := h.sv 4 (by decide)
  obtain sv5 : s.mem.readW (off (cB s0) 248) 64 = s0.gpr .r19 := h.sv 5 (by decide)
  obtain sv6 : s.mem.readW (off (cB s0) 256) 64 = s0.gpr .r20 := h.sv 6 (by decide)
  obtain sv7 : s.mem.readW (off (cB s0) 264) 64 = s0.gpr .r21 := h.sv 7 (by decide)
  obtain sv8 : s.mem.readW (off (cB s0) 272) 64 = s0.gpr .r22 := h.sv 8 (by decide)
  obtain sv9 : s.mem.readW (off (cB s0) 280) 64 = s0.gpr .r23 := h.sv 9 (by decide)
  obtain sv10 : s.mem.readW (off (cB s0) 288) 64 = s0.gpr .r24 := h.sv 10 (by decide)
  obtain sv11 : s.mem.readW (off (cB s0) 296) 64 = s0.gpr .r25 := h.sv 11 (by decide)
  obtain sv12 : s.mem.readW (off (cB s0) 304) 64 = s0.gpr .r26 := h.sv 12 (by decide)
  obtain sv13 : s.mem.readW (off (cB s0) 312) 64 = s0.gpr .r27 := h.sv 13 (by decide)
  obtain sv14 : s.mem.readW (off (cB s0) 320) 64 = s0.gpr .r28 := h.sv 14 (by decide)
  obtain sv15 : s.mem.readW (off (cB s0) 328) 64 = s0.gpr .r29 := h.sv 15 (by decide)
  obtain sv16 : s.mem.readW (off (cB s0) 336) 64 = s0.gpr .r30 := h.sv 16 (by decide)
  obtain sv17 : s.mem.readW (off (cB s0) 344) 64 = s0.gpr .r31 := h.sv 17 (by decide)
  refine WP.mono (WP.keep [.r11, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31] (Q := fun t =>
      (∀ i < 18, t.gpr (savedR i) = s0.gpr (savedR i)) ∧ t.mem = s.mem) ?_ (by decide))
    fun t ⟨⟨a, b⟩, k⟩ => ⟨a, b, k.gpr _ (by decide), k.gpr _ (by decide), k.sp, k.rd, k.wr, k.lr⟩
  rw [restore_eq]
  prun [VG.Proof.Rsa.PPC64LE.CrtValues.exec_addSp, h.sp, BitVec.add_zero, rd 208 (by decide) (by decide), rd 216 (by decide) (by decide), rd 224 (by decide) (by decide), rd 232 (by decide) (by decide), rd 240 (by decide) (by decide), rd 248 (by decide) (by decide), rd 256 (by decide) (by decide), rd 264 (by decide) (by decide), rd 272 (by decide) (by decide), rd 280 (by decide) (by decide), rd 288 (by decide) (by decide), rd 296 (by decide) (by decide), rd 304 (by decide) (by decide), rd 312 (by decide) (by decide), rd 320 (by decide) (by decide), rd 328 (by decide) (by decide), rd 336 (by decide) (by decide), rd 344 (by decide) (by decide), sv0, sv1, sv2, sv3, sv4, sv5, sv6, sv7, sv8, sv9, sv10, sv11, sv12, sv13, sv14, sv15, sv16, sv17]
  intro i hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 by omega_using [hi]) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The body between the entry and the restore. -/
def mid (trial : Prog isa) (name : String) (round : Prog isa) : Prog isa :=
  .seq VG.Impl.RsaKeyGen.PPC64LE.Candidate.zeroOut
    (.seq (.block (VG.Impl.MillerRabin.PPC64LE.Search.geFlag .r5 .r27 .r24))
      (.ite (.zero .d .r5) VG.Impl.RsaKeyGen.PPC64LE.Candidate.finNone
        (VG.Impl.RsaKeyGen.PPC64LE.Candidate.main trial name round)))

theorem wp_seq3 {a b c d : Prog isa} {s : State} {P Q : State → Prop} (h : WP isa (.seq a (.seq b c)) s P)
    (k : ∀ u, P u → WP isa d u Q) : WP isa (.seq a (.seq b (.seq c d))) s Q := by
  rw [WP.seq_iff] at h ⊢
  refine WP.mono h fun x hx => ?_
  rw [WP.seq_iff] at hx ⊢
  refine WP.mono hx fun y hy => ?_
  rw [WP.seq_iff]
  exact WP.mono hy k

/-- The whole function, from what the body between the entry and the
restore does. -/
theorem code_ok {s0 : State} (h : CIn s0) {trial round : Prog isa} {name : String} {Q : BitVec 64 → Mem → Prop}
    (hm : ∀ s, Bx s0 s → Regs s0 s → s.syms = s0.syms →
      WP isa (mid trial name round) s fun u => Bx s0 u ∧ Q (u.gpr .r3) u.mem) :
    WP isa (VG.Impl.RsaKeyGen.PPC64LE.Candidate.code trial name round) s0
      fun t => abiPreserved s0 t ∧ Q (t.gpr .r3) t.mem := by
  obtain st := started_ok h
  have hlo := h.spLo
  obtain hf := cB_fit h
  unfold VG.Impl.RsaKeyGen.PPC64LE.Candidate.code
  refine WP.seq (WP.of_runBlock ⟨s0.write .r0 s0.lr,
    (by simp only [runBlock_cons, runStep_some, runBlock_nil, exec_mflr]), ?_⟩)
  refine WP.seq (WP.frame (by show 48 ≤ s0.sp.toNat; omega_using [hlo]) (WP.alloc (by decide)
    (by show 176 ≤ (s0.sp - 48).toNat
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; show 48 ≤ s0.sp.toNat; omega_using [hlo])]
        show 176 ≤ s0.sp.toNat - 48; omega_using [hlo]) ?_))
  show WP isa (.seq (.block VG.Impl.RsaKeyGen.PPC64LE.Candidate.entry) (.seq _ (.seq _ (.seq _ _)))) (started s0) _
  refine WP.seq (WP.mono_syms (entry_ok st) fun s ⟨bs, rs⟩ sy => ?_)
  refine wp_seq3 (hm s bs rs sy) fun u ⟨bu, qu⟩ => ?_
  refine WP.mono (restore_ok bu) fun v ⟨sv, vm, v3, v2, vsp, _, _, _⟩ => ?_
  -- The frames' pops and `mtlr`.
  refine WP.of_runBlock ⟨_, (by simp only [runBlock_cons, runStep_some, runBlock_nil, exec_mtlr]; rfl), ?_⟩
  obtain spv : v.sp = off (cB s0) 176 := vsp.trans bu.sp
  obtain e1 : (freed 176 v).sp = off (cB s0) 352 := by
    show v.sp + BitVec.ofNat 64 176 = _; rw [spv, off_add]
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · have h0 : r ≠ .r0 := fun e => by subst e; exact absurd hr (by decide)
    show ((freed 176 v).write .r0 _).gpr r = _
    simp only [State.write, h0, ↓reduceIte]
    show v.gpr r = s0.gpr r
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · rw [v2]; exact bu.r2
    all_goals first
      | exact sv 0 (by decide) | exact sv 1 (by decide) | exact sv 2 (by decide) | exact sv 3 (by decide)
      | exact sv 4 (by decide) | exact sv 5 (by decide) | exact sv 6 (by decide) | exact sv 7 (by decide)
      | exact sv 8 (by decide) | exact sv 9 (by decide) | exact sv 10 (by decide) | exact sv 11 (by decide)
      | exact sv 12 (by decide) | exact sv 13 (by decide) | exact sv 14 (by decide) | exact sv 15 (by decide)
      | exact sv 16 (by decide) | exact sv 17 (by decide)
  · show (freed 176 v).sp + 48 = s0.sp
    rw [e1]; simp only [off, cB]; bv_omega
  · show (freed 176 v).mem.read ((freed 176 v).sp + 32) 8 = s0.lr
    rw [e1, show off (cB s0) 352 + 32 = off (cB s0) 384 from off_add _ _ 32, read8]
    show v.mem.readW _ 64 = _
    rw [vm]; exact bu.lr
  · show Q (((freed 176 v).write .r0 ((freed 176 v).mem.read ((freed 176 v).sp + 32) 8)).gpr .r3) (freed 176 v).mem
    simp only [State.write, show Reg.r3 ≠ Reg.r0 by decide, ↓reduceIte]
    show Q (v.gpr .r3) v.mem
    rw [vm, v3]; exact qu

end VG.Proof.RsaKeyGen.PPC64LE.Cand

end

end


/-!
# A candidate on PPC64LE: the results

`cOp s0`: what the contract asks of the call from `s0`, `CQ`: its results.
`Ctx`: the body's state with `out` still zero; `fin_ok`, `finNone_post`,
`finPrime_post`: each way the body ends gives the contract's results.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Candidate (finish finNone finPrime)

/-- `out_len`. -/
abbrev oL (s0 : State) : Nat := (s0.gpr .r4).toNat

/-- `rand_len`. -/
abbrev rL (s0 : State) : Nat := (PPC64LE.stackArg s0 0).toNat

/-- `e`'s octets. -/
abbrev eB (s0 : State) : List Byte := Spec.Rsa.bytesAt s0.mem (s0.gpr .r6) (s0.gpr .r7).toNat

/-- `p`'s octets. -/
abbrev pB (s0 : State) : List Byte := Spec.Rsa.bytesAt s0.mem (s0.gpr .r8) (s0.gpr .r9).toNat

/-- `rand`'s octets. -/
abbrev rB (s0 : State) : List Byte := Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (rL s0)

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- What the call computes. -/
def cOp (s0 : State) : Option (Spec.RsaKeyGen.Candidate × Spec.RsaKeyGen.Rand) :=
  Spec.RsaKeyGen.candidateOp (oL s0) (Spec.Rsa.bytesAt s0.mem (s0.gpr .r6) (s0.gpr .r7).toNat)
    (Spec.Rsa.bytesAt s0.mem (s0.gpr .r8) (s0.gpr .r9).toNat) (Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (rL s0))

/-- What `out` holds at the end. -/
def outOf (s0 : State) : List Byte :=
  match cOp s0 with
  | some (.prime c, _) => Spec.Rsa.i2osp c (oL s0)
  | _ => List.replicate (oL s0) 0

/-- What `used` holds at the end. -/
def usedOf (s0 : State) : Nat :=
  match cOp s0 with
  | some (_, rest) => rL s0 - rest.length
  | none => 0

/-- The contract's results. -/
def CQ (s0 : State) (r : BitVec 64) (m : Mem) : Prop :=
  r.toNat = Spec.RsaKeyGen.candidateStatus (cOp s0) ∧ Spec.Rsa.bytesAt m (s0.gpr .r3) (oL s0) = outOf s0 ∧
    Spec.Rsa.wordsAt m (s0.gpr .r5) 1 = [BitVec.ofNat 64 (usedOf s0)]

/-- The body's state, `out` still zero. -/
structure Ctx (s0 s : State) : Prop where
  bx : Bx s0 s
  r23 : s.gpr .r23 = s0.gpr .r3
  r24 : s.gpr .r24 = s0.gpr .r4
  r25 : s.gpr .r25 = s0.gpr .r5
  zero : Spec.Rsa.bytesAt s.mem (s0.gpr .r3) (oL s0) = List.replicate (oL s0) 0

theorem oL_lt {s0 : State} (hp : CIn s0) : oL s0 ≤ 512 := hp.valid.2.1

/-- `Ctx` through code that writes only `scratch` and the stack below the
frame. -/
theorem Ctx.step {s0 s t : State} (h : Ctx s0 s) (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (f : Frame [cS s0, below (off (cB s0) 176) 176] s.mem t.mem) (r2 : t.gpr .r2 = s.gpr .r2)
    (r23 : t.gpr .r23 = s.gpr .r23) (r24 : t.gpr .r24 = s.gpr .r24) (r25 : t.gpr .r25 = s.gpr .r25) :
    Ctx s0 t := by
  have hp := h.bx.pre
  obtain hf := cB_fit hp
  obtain bF : below (off (cB s0) 176) 176 = ⟨cB s0, 176⟩ := by
    simp only [below, off, BitVec.add_sub_cancel]
  refine ⟨h.bx.step sp rd wr (f.mono (by simp)) r2, r23.trans h.r23, r24.trans h.r24, r25.trans h.r25, ?_⟩
  rw [bytes_keep f (by have := oL_lt hp; omega_using [this]) (fun ρ hρ => ?_)]
  · exact h.zero
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl | rfl
  · exact hp.oS
  · rw [bF]; exact (hp.Fo.sub_left (Region.sub_prefix (by decide))).symm

theorem wordsAt_one (m : Mem) (U : Addr) (v : BitVec 64) : Spec.Rsa.wordsAt (m.writeW U v) U 1 = [v] := by
  simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
    Mem.readW_writeW_self64]

/-- The end through `finish k`, `used` from `r28`, `out` still zero. -/
theorem fin_ok (k : Nat) (hk : k < 2 ^ 15) {s0 u : State} (hc : Ctx s0 u)
    (hst : Spec.RsaKeyGen.candidateStatus (cOp s0) = k) (hout : outOf s0 = List.replicate (oL s0) 0)
    (hus : u.gpr .r28 = BitVec.ofNat 64 (usedOf s0)) :
    WP isa (finish k) u fun t => Bx s0 t ∧ CQ s0 (t.gpr .r3) t.mem := by
  have hp := hc.bx.pre
  obtain hU : InRegions u.wr (s0.gpr .r5) 8 :=
    ⟨cU s0, by rw [hc.bx.wr, bodyWr, hp.wr]; simp, Region.contains_self _ _⟩
  refine WP.mono (finish_ok k hc.r25 hU hk) fun t ⟨⟨tm, t3⟩, kt⟩ => ?_
  obtain fu : Frame [cU s0] u.mem t.mem := by
    rw [tm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.bx.step kt.sp kt.rd kt.wr (fu.mono (by simp)) (kt.gpr _ (by decide)), ?_, ?_, ?_⟩
  · rw [t3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hk]), hst]
  · rw [bytes_keep fu (by have := oL_lt hp; omega_using [this]) (fun ρ hρ => by
      simp only [List.mem_singleton] at hρ; subst hρ; exact hp.oU), hc.zero, hout]
  · rw [tm, hus]; exact wordsAt_one _ _ _

/-- The end through `finNone`, when `rand` is too short. -/
theorem finNone_post {s0 u : State} (hc : Ctx s0 u) (hres : cOp s0 = none) :
    WP isa finNone u fun t => Bx s0 t ∧ CQ s0 (t.gpr .r3) t.mem := by
  have hp := hc.bx.pre
  obtain hU : InRegions u.wr (s0.gpr .r5) 8 :=
    ⟨cU s0, by rw [hc.bx.wr, bodyWr, hp.wr]; simp, Region.contains_self _ _⟩
  refine WP.mono (finNone_ok hc.r25 hU) fun t ⟨⟨tm, t3, _⟩, kt⟩ => ?_
  obtain fu : Frame [cU s0] u.mem t.mem := by
    rw [tm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.bx.step kt.sp kt.rd kt.wr (fu.mono (by simp)) (kt.gpr _ (by decide)), ?_, ?_, ?_⟩
  · rw [t3, hres]; rfl
  · rw [bytes_keep fu (by have := oL_lt hp; omega_using [this]) (fun ρ hρ => by
      simp only [List.mem_singleton] at hρ; subst hρ; exact hp.oU), hc.zero, outOf, hres]
  · rw [tm, usedOf, hres]; exact wordsAt_one _ _ _

/-- The end through `finPrime`: the probable prime `c`, of `w` words, from
array 0 to `out`. -/
theorem finPrime_post {s0 u : State} {B : Addr} {Z w c : Nat} {rest : Spec.RsaKeyGen.Rand} (hc : Ctx s0 u)
    (hs : Scr u B Z) (h31 : u.gpr .r31 = B) (hZ : 256 + oL s0 ≤ Z) (hw : oL s0 = 8 * w) (hw1 : 1 ≤ w)
    (hd : (cO s0).Disjoint ⟨B, Z⟩) (hval : val32 u.mem B 256 (2 * w) = c)
    (hres : cOp s0 = some (.prime c, rest)) (hus : u.gpr .r28 = BitVec.ofNat 64 (rL s0 - rest.length)) :
    WP isa finPrime u fun t => Bx s0 t ∧ CQ s0 (t.gpr .r3) t.mem := by
  have hp := hc.bx.pre
  have hfo := hp.fo
  have hnw := hs.nowrap
  obtain hL := oL_lt hp
  simp only [oL] at hL hZ hw
  obtain hO : ∀ i < (s0.gpr .r4).toNat, InRegions u.wr (off (s0.gpr .r3) i) 1 := fun i hi =>
    ⟨cO s0, by rw [hc.bx.wr, bodyWr, hp.wr]; simp, Offset.contains_base _ (d := i) (by omega_using [hi]) (by omega_using [hi])⟩
  obtain hsep : ∀ i < (s0.gpr .r4).toNat, ∀ x, ofs B x < Z → off (s0.gpr .r3) i ≠ x := fun i hi x hx e => by
    refine hd _ (Offset.contains_base _ (d := i) (by omega_using [hi]) (by omega_using [hi])) ?_
    show Region.Contains _ (off (s0.gpr .r3) i) 1
    rw [e]; simp only [Region.Contains]; simp only [ofs] at hx; omega_using [hx]
  unfold finPrime
  obtain cp := copyOut_ok hs h31 hc.r23 (by rw [hc.r24]; simp) (by omega_using [hw, hw1]) hZ hO (by omega_using [hfo]) hsep
  rw [WP.seq_iff] at cp
  rw [WP.seq_iff]
  refine WP.mono cp fun t₁ h₁ => ?_
  rw [WP.seq_iff]
  refine WP.mono h₁ fun t₂ ⟨hb, ho, k₂⟩ => ?_
  obtain fo : Frame [cO s0] u.mem t₂.mem := frame_of_outside ho (by omega_using [])
  obtain b₂ := hc.bx.step k₂.sp k₂.rd k₂.wr (fo.mono (by simp)) (k₂.gpr _ (by decide))
  obtain hU : InRegions t₂.wr (s0.gpr .r5) 8 :=
    ⟨cU s0, by rw [b₂.wr, bodyWr, hp.wr]; simp, Region.contains_self _ _⟩
  refine WP.mono (finish_ok 1 ((k₂.gpr _ (by decide)).trans hc.r25) hU (by decide)) fun t ⟨⟨tm, t3⟩, kt⟩ => ?_
  obtain fu : Frame [cU s0] t₂.mem t.mem := by
    rw [tm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨b₂.step kt.sp kt.rd kt.wr (fu.mono (by simp)) (kt.gpr _ (by decide)), ?_, ?_, ?_⟩
  · rw [t3, hres]; rfl
  · rw [bytes_keep fu (by simp only [oL]; omega_using []) (fun ρ hρ => by
      simp only [List.mem_singleton] at hρ; subst hρ; exact hp.oU), bytes_of_copy hw hb, hval, outOf, hres]
  · rw [tm, (k₂.gpr _ (by decide)).trans hus, usedOf, hres]; exact wordsAt_one _ _ _

end VG.Proof.RsaKeyGen.PPC64LE.Cand
