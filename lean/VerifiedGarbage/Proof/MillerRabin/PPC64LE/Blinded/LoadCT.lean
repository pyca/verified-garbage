module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Blinded.CTBase
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Blinded.Load
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Blinded.CTBase
meta import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Blinded.Load
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The blinded Miller–Rabin loop on PPC64LE: constant time of a draw's load

`load_ct`: two runs of `load` from the same octets `used` of the tape leak
the same trace. The tape's address at `used` and the octets of a draw
(`loadA_ok`), loaded from the header, fix `loadN`'s addresses and count; the
top word's offset, loaded from the header, fixes the address of the mask's
load and store (`loadC1_ok`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE.Blinded

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.MillerRabin.PPC64LE.Search VG.Impl.MillerRabin.PPC64LE.Blinded
open VG.Proof.MillerRabin.PPC64LE (Env arr)
open VG.Proof.Bignum (slot Frm wv word off ofs writeW_outside word_writeW_self)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Two Pins two_post two_taint two_ite)

/-- A draw's start: the context, and `used` octets read with a draw left. -/
def LS (a : BD × Nat) (s : State) : Prop :=
  Ctx a.1 s ∧ word s.mem a.1.B (8 * hUsed) = BitVec.ofNat 64 a.2 ∧ a.2 + 8 * (a.1.t + 1) ≤ a.1.rl

/-- The first block of `load`. -/
abbrev loadA : List Instr :=
  [ldh .r12 hRand, ldh .r3 hUsed, .add .r12 .r12 .r3, ldh .r6 hK, .add .r3 .r3 .r6, sth .r3 hUsed] ++
    PublicChecked.base .r10 4

/-- After it. -/
def LA (a : BD × Nat) (s : State) : Prop :=
  ∃ s₀, LS a s₀ ∧ (s.gpr .r12 = a.1.R + BitVec.ofNat 64 a.2 ∧ s.gpr .r6 = BitVec.ofNat 64 (8 * (a.1.t + 1)) ∧
    s.gpr .r10 = off a.1.B (slot a.1.w 4) ∧
    s.mem = s₀.mem.writeW (off a.1.B (8 * hUsed)) (BitVec.ofNat 64 (a.2 + 8 * (a.1.t + 1)))) ∧
    Keep [.r3, .r6, .r10, .r12] s₀ s

/-- After `loadN`. -/
def LN (a : BD × Nat) (s : State) : Prop :=
  ∃ u, LA a u ∧ VG.Proof.Bignum.Outside a.1.B (slot a.1.w 4) (8 * a.1.w) u.mem s.mem ∧
    Keep [.r0, .r14, .r15, .r16, .r17] u s

/-- The first part of the last block: the top word's address in `r5`. -/
abbrev loadC1 : List Instr :=
  [.addi .r10 .r31 hdrBytes] ++ PublicChecked.base .r5 4 ++ [ldh .r6 hTopOff, .add .r5 .r5 .r6]

/-- The rest: the mask. -/
abbrev loadC2 : List Instr := [ldh .r4 hTop, .load .d .r6 .r5 0, .logic .and .r6 .r6 .r4, .store .d .r6 .r5 0]

/-- After `loadC1`. -/
def LC1 (a : BD × Nat) (s : State) : Prop :=
  s.gpr .r5 = off a.1.B (slot a.1.w 4 + 8 * a.1.t) ∧ s.gpr .r31 = a.1.B ∧ s.sp = a.1.sp

theorem loadC1_ok {v : State} {B : Addr} {L w t : Nat} (hv : Scr v B (8 * L))
    (v31 : v.gpr .r31 = B) (v29 : v.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)))
    (v11 : v.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw4 : 4 ≤ w) (hw128 : w ≤ 128)
    (hZ : slot w 28 ≤ 8 * L) (r128 : v.mem.readW (B + 128#64) 64 = BitVec.ofNat 64 (8 * t)) :
    WP isa (.block loadC1) v fun x => x.gpr .r5 = off B (slot w 4 + 8 * t) ∧ x.gpr .r31 = B ∧ x.sp = v.sp := by
  have hZ' : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := hZ
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Q := fun (y : State) => (y.gpr .r10 = off B (slot w 0) ∧ y.mem = v.mem) ∧ Keep [.r10] v y)
    (WP.keep (Q := fun (y : State) => y.gpr .r10 = off B (slot w 0) ∧ y.mem = v.mem) _
      (by prun [v31, hdrBytes]; simp only [slot, hdrBytes, Nat.zero_mul, Nat.add_zero]) (by decide))
    fun y ⟨⟨y10, ym⟩, ky⟩ => ?_
  have ey : Env y B (8 * L) w := ⟨hv.congr ky.wr, y10, (ky.gpr .r29 (by decide)).trans v29,
    (ky.gpr .r11 (by decide)).trans v11, (ky.gpr .r31 (by decide)).trans v31, hw4, hw128, hZ⟩
  refine WP.mono (ey.base (rd := .r5) (by decide) (by decide) 4) fun z ⟨⟨z5, zm⟩, kz⟩ => ?_
  have z31 : z.gpr .r31 = B := (kz.gpr .r31 (by decide)).trans ey.h31
  have hz : Scr z B (8 * L) := ey.hs.congr kz.wr
  simp only [ldh, hTopOff]
  prun [z31, z5, zm, ym, r128, hz.ld (d := 128) (n := 8) (by omega)]
  exact kz.sp.trans ky.sp

theorem LA.regs {a : BD × Nat} {s : State} (h : LA a s) :
    s.gpr .r10 = off a.1.B (slot a.1.w 4) ∧ s.gpr .r11 = BitVec.ofNat 64 (2 * a.1.w) ∧
      s.gpr .r12 = a.1.R + BitVec.ofNat 64 a.2 ∧ s.gpr .r6 = BitVec.ofNat 64 (8 * (a.1.t + 1)) ∧
      s.gpr .r29 = BitVec.ofNat 64 (8 * (a.1.w + 2)) ∧ s.gpr .r31 = a.1.B ∧ s.sp = a.1.sp := by
  obtain ⟨s₀, ⟨⟨c, -, sp⟩, -, -⟩, ⟨h12, h6, h10, -⟩, k⟩ := h
  have e := c.prep.env
  exact ⟨h10, (k.gpr _ (by decide)).trans e.h11, h12, h6, (k.gpr _ (by decide)).trans e.h29,
    (k.gpr _ (by decide)).trans e.h31, k.sp.trans sp⟩

theorem LN.regs {a : BD × Nat} {s : State} (h : LN a s) :
    s.gpr .r11 = BitVec.ofNat 64 (2 * a.1.w) ∧ s.gpr .r29 = BitVec.ofNat 64 (8 * (a.1.w + 2)) ∧
      s.gpr .r31 = a.1.B ∧ s.sp = a.1.sp := by
  obtain ⟨u, hu, -, k⟩ := h
  obtain ⟨-, h11, -, -, h29, h31, sp⟩ := hu.regs
  exact ⟨(k.gpr _ (by decide)).trans h11, (k.gpr _ (by decide)).trans h29, (k.gpr _ (by decide)).trans h31,
    k.sp.trans sp⟩

theorem load_stA (a : BD × Nat) (s : State) (h : LS a s) : WP isa (.block loadA) s (LA a) :=
  WP.mono (loadA_ok h.1.1 h.2.1) fun _ hu => ⟨s, h, hu⟩

theorem load_stN (a : BD × Nat) (s : State) (h : LA a s) : WP isa Precompute.loadN s (LN a) := by
  obtain ⟨s₀, ⟨⟨ctx, -, sp⟩, hu, hav⟩, ⟨u12, u6, u10, um⟩, ku⟩ := id h
  have e := ctx.prep.env
  have hnw := e.hs.nowrap
  have hZ : 256 + 28 * (8 * (a.1.w + 2)) ≤ 8 * a.1.L := e.hZ
  have htw := ctx.tw
  have hw128 := e.hw'
  have hNr : ∀ i < 8 * (a.1.t + 1), InRegions (s.rd ++ s.wr) (off (a.1.R + BitVec.ofNat 64 a.2) i) 1 := fun i hi => by
    rw [ku.rd, ku.wr, show off (a.1.R + BitVec.ofNat 64 a.2) i = a.1.R + BitVec.ofNat 64 a.2 + BitVec.ofNat 64 i
      from rfl, Offset.add_add]; exact ctx.rdR _ (by omega)
  have hNs : ∀ i < 8 * (a.1.t + 1), ∀ x, ofs a.1.B x < 8 * a.1.L → off (a.1.R + BitVec.ofNat 64 a.2) i ≠ x :=
    fun i hi x hx => by
      rw [show off (a.1.R + BitVec.ofNat 64 a.2) i = a.1.R + BitVec.ofNat 64 a.2 + BitVec.ofNat 64 i from rfl,
        Offset.add_add]; exact ctx.sepR _ (by omega) x hx
  exact WP.mono (VG.Proof.Bignum.PPC64LE.loadN_ok (k := 8 * (a.1.t + 1)) (e.hs.congr ku.wr) u10
    (by rw [u12]; exact (BitVec.add_zero _).symm) u6 ((ku.gpr .r11 (by decide)).trans e.h11) (by omega)
    (by omega) (by omega) (by simp only [slot, hdrBytes]; omega) (by simp only [slot, hdrBytes]; omega) hNr hNs)
    fun v ⟨_, vo, kv⟩ => ⟨s, h, vo, kv⟩

theorem load_stC1 (a : BD × Nat) (s : State) (h : LN a s) : WP isa (.block loadC1) s (LC1 a) := by
  obtain ⟨u, ⟨s₀, ⟨⟨ctx, -, sp⟩, -, -⟩, ⟨-, -, -, um⟩, ku⟩, vo, kv⟩ := id h
  obtain ⟨h11, h29, h31, hsp⟩ := h.regs
  have e := ctx.prep.env
  have hnw := e.hs.nowrap
  have hZ : 256 + 28 * (8 * (a.1.w + 2)) ≤ 8 * a.1.L := e.hZ
  have r128 : s.mem.readW (a.1.B + 128#64) 64 = BitVec.ofNat 64 (8 * a.1.t) := by
    refine ((vo.word (d := 128) (by simp only [slot, hdrBytes]; omega) (by omega)).trans ?_).trans ctx.topOff
    rw [um]
    exact (writeW_outside _ _ _ (by simp only [hUsed]; omega)).word (by simp only [hUsed]; omega) (by omega)
  exact WP.mono (loadC1_ok (e.hs.congr (kv.wr.trans ku.wr)) h31 h29 h11 e.hw e.hw' e.hZ r128)
    fun x ⟨x5, x31, xsp⟩ => ⟨x5, x31, xsp.trans hsp⟩

theorem load_ct : RelCT isa (Two LS) load fun _ _ => True := by
  have pS : Pins LS [.r10, .r11, .r29, .r31] := pins_env (fun a => a.1) fun a s h => ⟨h.1.1.prep.env, h.1.2.2⟩
  have pA : Pins LA [.r10, .r11, .r12, .r6, .r29, .r31] := by
    intro a s₁ s₂ h₁ h₂
    obtain ⟨a10, a11, a12, a6, a29, a31, asp⟩ := h₁.regs
    obtain ⟨b10, b11, b12, b6, b29, b31, bsp⟩ := h₂.regs
    refine ⟨asp.trans bsp.symm, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [a10, b10]
    · rw [a11, b11]
    · rw [a12, b12]
    · rw [a6, b6]
    · rw [a29, b29]
    · rw [a31, b31]
  have pN : Pins LN [.r29, .r31] := by
    intro a s₁ s₂ h₁ h₂
    obtain ⟨-, a29, a31, asp⟩ := h₁.regs
    obtain ⟨-, b29, b31, bsp⟩ := h₂.regs
    refine ⟨asp.trans bsp.symm, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [a29, b29]
    · rw [a31, b31]
  have pC : Pins LC1 [.r5, .r31] := by
    intro a s₁ s₂ ⟨a5, a31, asp⟩ ⟨b5, b31, bsp⟩
    refine ⟨asp.trans bsp.symm, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [a5, b5]
    · rw [a31, b31]
  unfold load
  refine RelCT.seq (two_post (two_taint _ pS (by taint_decide)) load_stA)
    (RelCT.seq (two_post (two_taint _ pA (by taint_decide)) load_stN) ?_)
  rw [show [Instr.addi .r10 .r31 hdrBytes] ++ PublicChecked.base .r5 4 ++ [ldh .r6 hTopOff, .add .r5 .r5 .r6,
      ldh .r4 hTop, .load .d .r6 .r5 0, .logic .and .r6 .r6 .r4, .store .d .r6 .r5 0] = loadC1 ++ loadC2 by
    simp only [loadC1, loadC2, List.append_assoc, List.cons_append, List.nil_append]]
  exact RelCT.block_append (RelCT.seq (two_post (two_taint _ pN (by taint_decide)) load_stC1)
    (two_taint _ pC (by taint_decide)))

end VG.Proof.MillerRabin.PPC64LE.Blinded
