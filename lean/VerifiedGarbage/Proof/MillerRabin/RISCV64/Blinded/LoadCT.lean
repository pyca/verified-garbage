module

public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.CTBase
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.Load
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
meta import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.CTBase
meta import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.Load
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The blinded Miller–Rabin loop on RISC-V: constant time of a draw's load

As on PPC64LE (`Proof/MillerRabin/PPC64LE/Blinded/LoadCT.lean`): `load_ct`,
two runs of `load` from the same octets `used` of the tape leak the same
trace. The tape's address at `used` and the octets of a draw (`loadA_ok`),
loaded from the header, fix `loadN`'s addresses and count; the top word's
offset, loaded from the header, fixes the address of the mask's load and
store (`loadC1_ok`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.RISCV64.Blinded

open VG VG.RISCV64 VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.MillerRabin.RISCV64.Search VG.Impl.MillerRabin.RISCV64.Blinded
open VG.Proof.MillerRabin.RISCV64 (Env A)
open VG.Proof.Bignum (slot Frm wv word off ofs writeW_outside word_writeW_self)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Two Pins two_post two_taint two_ite)

/-- A draw's start: the context, and `used` octets read with a draw left. -/
def LS (a : BD × Nat) (s : State) : Prop :=
  Ctx a.1 s ∧ word s.mem a.1.B (8 * hUsed) = BitVec.ofNat 64 a.2 ∧ a.2 + 8 * (a.1.t + 1) ≤ a.1.rl

/-- The first block of `load`. -/
abbrev loadA : List Instr :=
  [ldh .s7 hRand, ldh .t2 hUsed, .add .s7 .s7 .t2, ldh .s8 hK, .add .t2 .t2 .s8, sth .t2 hUsed] ++
    PublicChecked.base .a7 4

/-- After it. -/
def LA (a : BD × Nat) (s : State) : Prop :=
  ∃ s₀, LS a s₀ ∧ (s.gpr .s7 = a.1.R + BitVec.ofNat 64 a.2 ∧ s.gpr .s8 = BitVec.ofNat 64 (8 * (a.1.t + 1)) ∧
    s.gpr .a7 = off a.1.B (slot a.1.w 4) ∧
    s.mem = s₀.mem.writeW (off a.1.B (8 * hUsed)) (BitVec.ofNat 64 (a.2 + 8 * (a.1.t + 1)))) ∧
    Keep [.s7, .t2, .s8, .a7] s₀ s ∧ s.sp = s₀.sp

/-- After `loadN`. -/
def LN (a : BD × Nat) (s : State) : Prop :=
  ∃ u, LA a u ∧ VG.Proof.Mont.Outside a.1.B (slot a.1.w 4) (8 * a.1.w) u.mem s.mem ∧
    Keep [.a0, .s0, .t3, .t4, .t5] u s ∧ s.sp = u.sp

/-- After `a7` back: the working space's registers and the top word's offset. -/
def LB (a : BD × Nat) (s : State) : Prop :=
  Env s a.1.B (8 * a.1.L) a.1.w ∧ word s.mem a.1.B (8 * hTopOff) = BitVec.ofNat 64 (8 * a.1.t) ∧ s.sp = a.1.sp

/-- After `topAddr`: the top word's address in `t3`. -/
def LC1 (a : BD × Nat) (s : State) : Prop :=
  s.gpr .t3 = off a.1.B (slot a.1.w 4 + 8 * a.1.t) ∧ s.gpr .s6 = a.1.B ∧ s.sp = a.1.sp

/-- The rest of `load`'s last block: the mask. -/
abbrev loadC2 : List Instr := [ldh .t4 hTop, .load .d .t2 .t3 0, .logic .and .t2 .t2 .t4, .store .d .t2 .t3 0]

theorem topAddr_ok {v : State} {B : Addr} {L w t : Nat} (e : Env v B (8 * L) w)
    (hoff : word v.mem B (8 * hTopOff) = BitVec.ofNat 64 (8 * t)) :
    WP isa (.block topAddr) v fun x => x.gpr .t3 = off B (slot w 4 + 8 * t) ∧ x.gpr .s6 = B ∧ x.sp = v.sp := by
  have hZ' : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := e.hZ
  unfold topAddr
  rw [WP.block_append_iff]
  refine WP.mono (WP.rdwr (e.base (rd := .t3) (by decide) 4)) fun z ⟨⟨⟨z3, zm⟩, kz⟩, _, _, zsp⟩ => ?_
  have z6 : z.gpr .s6 = B := (kz.gpr (by decide)).trans e.s6
  have hz : Scr z B (8 * L) := e.hs.congr kz.2.2
  have r128 : z.mem.readW (B + 128#64) 64 = BitVec.ofNat 64 (8 * t) := by rw [zm]; exact hoff
  refine WP.mono (WP.rdwr (WP.keep [.t2, .t3] (Q := fun x => x.gpr .t3 = off B (slot w 4 + 8 * t) ∧ x.gpr .s6 = B)
    (by
      simp only [ldh, hTopOff]
      brun [z6, z3, r128, hz.ld (d := 128) (n := 8) (by omega), hz.al8 (d := 128) (by omega) (by decide)])
      (by rfl) (by rfl))) fun x ⟨⟨⟨x3, x6⟩, _⟩, _, _, xsp⟩ =>
    ⟨x3, x6, xsp.trans zsp⟩

theorem LA.regs {a : BD × Nat} {s : State} (h : LA a s) :
    s.gpr .a7 = off a.1.B (slot a.1.w 4) ∧ s.gpr .t0 = BitVec.ofNat 64 a.1.w ∧
      s.gpr .s7 = a.1.R + BitVec.ofNat 64 a.2 ∧ s.gpr .s8 = BitVec.ofNat 64 (8 * (a.1.t + 1)) ∧
      s.gpr .s5 = BitVec.ofNat 64 (8 * (a.1.w + 2)) ∧ s.gpr .s6 = a.1.B ∧ s.sp = a.1.sp := by
  obtain ⟨s₀, ⟨⟨c, -, sp⟩, -, -⟩, ⟨h7, h8, ha7, -⟩, k, hsp⟩ := h
  have e := c.prep.env
  exact ⟨ha7, (k.gpr (by decide)).trans e.t0, h7, h8, (k.gpr (by decide)).trans e.s5,
    (k.gpr (by decide)).trans e.s6, hsp.trans sp⟩

theorem LN.regs {a : BD × Nat} {s : State} (h : LN a s) :
    s.gpr .t0 = BitVec.ofNat 64 a.1.w ∧ s.gpr .s5 = BitVec.ofNat 64 (8 * (a.1.w + 2)) ∧
      s.gpr .s6 = a.1.B ∧ s.sp = a.1.sp := by
  obtain ⟨u, hu, -, k, hsp⟩ := h
  obtain ⟨-, h0, -, -, h5, h6, sp⟩ := hu.regs
  exact ⟨(k.gpr (by decide)).trans h0, (k.gpr (by decide)).trans h5, (k.gpr (by decide)).trans h6, hsp.trans sp⟩

theorem load_stA (a : BD × Nat) (s : State) (h : LS a s) : WP isa (.block loadA) s (LA a) :=
  WP.mono (WP.rdwr (loadA_ok h.1.1 h.2.1)) fun _ ⟨hu, _, _, sp⟩ => ⟨s, h, hu.1, hu.2, sp⟩

theorem load_stN (a : BD × Nat) (s : State) (h : LA a s) : WP isa Precompute.loadN s (LN a) := by
  obtain ⟨s₀, ⟨⟨ctx, -, sp⟩, hu, hav⟩, ⟨u7, u8, ua7, um⟩, ku, _⟩ := id h
  have e := ctx.prep.env
  have hnw := e.hs.nowrap
  have hZ : 256 + 28 * (8 * (a.1.w + 2)) ≤ 8 * a.1.L := e.hZ
  have htw := ctx.tw
  have hw128 := e.hw'
  have hNr : ∀ i < 8 * (a.1.t + 1), InRegions (s.rd ++ s.wr) (off (a.1.R + BitVec.ofNat 64 a.2) i) 1 :=
    fun i hi => by
      rw [ku.2.1, ku.2.2, show off (a.1.R + BitVec.ofNat 64 a.2) i = a.1.R + BitVec.ofNat 64 a.2 + BitVec.ofNat 64 i
        from rfl, Offset.add_add]; exact ctx.rdR _ (by omega)
  have hNs : ∀ i < 8 * (a.1.t + 1), ∀ x, ofs a.1.B x < 8 * a.1.L → off (a.1.R + BitVec.ofNat 64 a.2) i ≠ x :=
    fun i hi x hx => by
      rw [show off (a.1.R + BitVec.ofNat 64 a.2) i = a.1.R + BitVec.ofNat 64 a.2 + BitVec.ofNat 64 i from rfl,
        Offset.add_add]; exact ctx.sepR _ (by omega) x hx
  exact WP.mono (WP.rdwr (loadN_ok (k := 8 * (a.1.t + 1)) (e.hs.congr ku.2.2) ua7
    (by rw [u7]; exact (BitVec.add_zero _).symm) u8 ((ku.gpr (by decide)).trans e.t0) (by omega)
    (by omega) (by omega) (by simp only [slot, hdrBytes]; omega) (by simp only [slot, hdrBytes]; omega)
    (by simp only [slot, hdrBytes]; omega) hNr hNs))
    fun v ⟨⟨_, vo, kv⟩, _, _, vsp⟩ => ⟨s, h, vo, kv, vsp⟩

theorem load_stB (a : BD × Nat) (s : State) (h : LN a s) :
    WP isa (.block [.addi .a7 .s6 hdrBytes]) s (LB a) := by
  obtain ⟨u, ⟨s₀, ⟨⟨ctx, -, sp⟩, -, -⟩, ⟨-, -, -, um⟩, ku, _⟩, vo, kv, _⟩ := id h
  obtain ⟨h0, h5, h6, hsp⟩ := h.regs
  have e := ctx.prep.env
  have hnw := e.hs.nowrap
  have hZ : 256 + 28 * (8 * (a.1.w + 2)) ≤ 8 * a.1.L := e.hZ
  have r128 : word s.mem a.1.B (8 * hTopOff) = BitVec.ofNat 64 (8 * a.1.t) := by
    refine ((vo.word (d := 128) (by simp only [slot, hdrBytes]; omega) (by omega)).trans ?_).trans ctx.topOff
    rw [um]
    exact (writeW_outside _ _ _ (by simp only [hUsed]; omega)).word (by simp only [hUsed]; omega) (by omega)
  refine WP.mono (WP.rdwr (WP.keep [.a7] (Q := fun y => y.gpr .a7 = off a.1.B (slot a.1.w 0) ∧ y.mem = s.mem)
    (by brun [h6, hdrBytes]; simp only [slot, hdrBytes, Nat.zero_mul, Nat.add_zero]) (by rfl) (by rfl)))
    fun y ⟨⟨⟨y7, ym⟩, ky⟩, _, _, ysp⟩ => ⟨⟨e.hs.congr ((ky.2.2.trans kv.2.2).trans ku.2.2), y7,
      (ky.gpr (by decide)).trans h5, (ky.gpr (by decide)).trans h0, (ky.gpr (by decide)).trans h6, e.hw, e.hw', e.hZ⟩,
      by rw [ym]; exact r128, ysp.trans hsp⟩

theorem load_ct : RelCT isa (Two LS) load fun _ _ => True := by
  have pS : Pins LS [.a7, .s5, .t0, .s6] := pins_env (fun a => a.1) fun a s h => ⟨h.1.1.prep.env, h.1.2.2⟩
  have pA : Pins LA [.a7, .t0, .s7, .s8, .s5, .s6] := by
    intro a s₁ s₂ h₁ h₂
    obtain ⟨a7, a0, a17, a8, a5, a6, asp⟩ := h₁.regs
    obtain ⟨b7, b0, b17, b8, b5, b6, bsp⟩ := h₂.regs
    refine ⟨asp.trans bsp.symm, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [a7, b7]
    · rw [a0, b0]
    · rw [a17, b17]
    · rw [a8, b8]
    · rw [a5, b5]
    · rw [a6, b6]
  have pN : Pins LN [.t0, .s5, .s6] := by
    intro a s₁ s₂ h₁ h₂
    obtain ⟨a0, a5, a6, asp⟩ := h₁.regs
    obtain ⟨b0, b5, b6, bsp⟩ := h₂.regs
    refine ⟨asp.trans bsp.symm, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [a0, b0]
    · rw [a5, b5]
    · rw [a6, b6]
  have pB : Pins LB [.a7, .s5, .t0, .s6] := pins_env (fun a => a.1) fun a s h => ⟨h.1, h.2.2⟩
  have pC : Pins LC1 [.t3, .s6] := by
    intro a s₁ s₂ ⟨a3, a6, asp⟩ ⟨b3, b6, bsp⟩
    refine ⟨asp.trans bsp.symm, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [a3, b3]
    · rw [a6, b6]
  unfold load loadDraw
  refine RelCT.seq (RelCT.seq (two_post (two_taint _ pS (by taint_decide)) load_stA)
    (RelCT.seq (two_post (two_taint _ pA (by taint_decide)) load_stN)
      (two_post (two_taint _ pN (by taint_decide)) load_stB))) ?_
  exact RelCT.block_append (RelCT.seq (two_post (Ψ := LC1) (two_taint _ pB (by taint_decide)) fun a s h =>
      WP.mono (topAddr_ok h.1 h.2.1) fun x ⟨x3, x6, xsp⟩ => ⟨x3, x6, xsp.trans h.2.2⟩)
    (two_taint (c := .block loadC2) _ pC (by taint_decide)))

end VG.Proof.MillerRabin.RISCV64.Blinded
