module

public import VerifiedGarbage.Impl.Dsa.RISCV64.ProbablePrime
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Prep
public import VerifiedGarbage.Proof.Bignum.Layout
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Setup
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.TrialOk
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.Loop
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.MontPrep
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Dsa.Generation.Primality
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Mont.OutsFrame
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# DSA's probable-prime test on RISC-V: correctness

As on PPC64LE (`Proof/Dsa/PPC64LE/Prime/*.lean`). `CIn bits s`: the
contract's precondition (with the table's region readable too), as the
proofs use it (`cin_of_pre`); `Shape`: what the code needs of each width
(`shape_of`). `entry_ok`: our caller's registers saved in `ws` from
`saveOff` (`Spill.save_ok`), the round's registers and the header's values
(`values_ok`), stored (`Spill.save_ok` again), and the arrays' addresses
(RSA's `Cand.hdrs_ok`): `EntryPost`, with the header `Hdr`.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.Prime
open VG VG.RISCV64 VG.Proof.Bignum.RISCV64
open VG.Impl.Dsa.RISCV64.ProbablePrime
open VG.Impl.MillerRabin.RISCV64.Search
open VG.Impl.MillerRabin.RISCV64.Blinded (hTopOff)
open VG.Impl.RsaKeyGen.RISCV64.Candidate (hTrial)
open VG.Impl.Bignum (hdrBytes)
open VG.Proof.Bignum (word off slot Outside ofs Frm)
open VG.Proof.MillerRabin.RISCV64 (Env A RoundImpl)
open VG.Proof.MillerRabin.RISCV64.Search (Prep)
open VG.Proof.MillerRabin.RISCV64.Blinded (BCtx MOut millerRabin_ok)
open VG.Impl.RsaKeyGen (TrialTable32.symbol TrialTable32.packed)

/-! ## The precondition -/

/-- The widths of DSA's primes. -/
abbrev Bits (bits : Nat) : Prop := bits = 160 ∨ bits = 256 ∨ bits = 1024 ∨ bits = 2048 ∨ bits = 3072

/-- The arguments' regions, and the stack the test may use (the round's,
`below sp 96`, is part of it, `sub96`). -/
abbrev cW (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat * 8⟩
abbrev cR (s : State) : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
abbrev cU (s : State) : Region := ⟨s.gpr .a4, 8⟩
abbrev cS (s : State) : Region := ⟨s.sp - 512#64, 512⟩

theorem sub96 (s : State) : Region.Sub (below s.sp 96) (cS s) := below_sub (by decide) (by decide)

/-- The contract's precondition. -/
structure CIn (bits : Nat) (s : State) : Prop where
  sp16 : s.sp.toNat % 16 = 0
  spLo : 512 ≤ s.sp.toNat
  rd : cR s ∈ s.rd
  wr : s.wr = [cW s, cU s]
  wR : (cW s).Disjoint (cR s)
  wU : (cW s).Disjoint (cU s)
  rU : (cR s).Disjoint (cU s)
  sW : (cS s).Disjoint (cW s)
  sR : (cS s).Disjoint (cR s)
  sU : (cS s).Disjoint (cU s)
  fw : (s.gpr .a0).toNat + (s.gpr .a1).toNat * 8 ≤ 2 ^ 64
  fr : (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64
  fu : (s.gpr .a4).toNat + 8 ≤ 2 ^ 64
  size : keyOff + 8 * keyWords bits ≤ 8 * (s.gpr .a1).toNat
  odd : Proof.Dsa.ProbablePrime.candidateAt (layout bits) s.mem (s.gpr .a0) % 2 = 1
  bl : Spec.Dsa.bitLength (Proof.Dsa.ProbablePrime.candidateAt (layout bits) s.mem (s.gpr .a0)) = bits
  alW : (s.gpr .a0).toNat % 8 = 0
  alU : (s.gpr .a4).toNat % 8 = 0

theorem cin_of_pre (bits : Nat) (s : State) (h : (Proof.Dsa.ProbablePrime.contract (layout bits) abi 512).pre s) :
    CIn bits s := by
  sig_pre [Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi, argRegs] at h
  obtain ⟨sp16, spLo, rd, wr, wR, wU, rU, sW, sR, sU, fw, fr, fu, size, odd, bl, alW, alU⟩ := h
  exact ⟨sp16, spLo, by rw [rd]; exact List.mem_singleton_self _, wr, wR, wU, rU, sW, sR, sU, fw, fr, fu, size,
    odd, bl, alW, alU⟩

/-- What the code needs of a width: the immediates fit, and the witness's
top word is word `t` with `b` bits. -/
structure Shape (bits : Nat) : Prop where
  w4 : 4 ≤ words bits
  w48 : words bits ≤ 48
  kw : keyWords bits < 2048
  hlen : len bits = bits / 8
  hlen8 : 8 * len bits = bits
  hlenw : len bits ≤ 8 * words bits
  hlen1 : 1 ≤ len bits
  t0 : 0 < (bits - 1) / 64
  tw : (bits - 1) / 64 < words bits
  b1 : 1 ≤ topBits bits
  b64 : topBits bits ≤ 64
  bt : bits = 64 * ((bits - 1) / 64) + topBits bits
  hdraw : draw bits = 8 * ((bits - 1) / 64 + 1)
  hoff : topOff bits = 8 * ((bits - 1) / 64)
  hchecks : checks bits = Spec.Dsa.primeChecks bits
  hcount : count bits = if words bits ≤ 16 then 512 else 1024
  stride : 8 * (words bits + 2) < 2048
  big : 13 ≤ bits - 1
  key : keyWords bits = 32 + 28 * (words bits + 2)
  maskb : 64 - topBits bits < 64
  cnt : count bits < 2048
  chk : checks bits < 2048
  drw : draw bits < 2048
  toff : topOff bits < 2048
  cnt1 : 1 ≤ count bits
  cnt2 : count bits ≤ 1024
  ch63 : checks bits < 2 ^ 63

theorem shape_of {bits : Nat} (hb : Bits bits) : Shape bits := by
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

/-! ## The entry -/

/-- The working space's base. -/
abbrev wsB (σ : State) : Addr := σ.gpr .a0 + BitVec.ofNat 64 keyOff

/-- The registers `values` writes. -/
def valRegs : List Reg := [.s6, .a7, .t0, .s5, .t1, .t2, .t3, .t4, .t5, .t6]

theorem mask_val {b : Nat} (hb1 : 1 ≤ b) (hb : b ≤ 64) :
    (BitVec.ofNat 64 0 - BitVec.ofNat 64 1) >>> (64 - b) = BitVec.ofNat 64 (2 ^ b - 1) := by
  apply BitVec.eq_of_toNat_eq
  have h2 : 2 ^ b ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hb
  have h3 : (2 : Nat) ^ 64 = 2 ^ b * 2 ^ (64 - b) := by rw [← Nat.pow_add]; congr 1; omega
  have e1 : (BitVec.ofNat 64 0 - BitVec.ofNat 64 1).toNat = 2 ^ 64 - 1 := by decide
  rw [BitVec.toNat_ushiftRight, e1, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]
  have hX1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have hP1 : 1 ≤ 2 ^ (64 - b) := Nat.one_le_two_pow
  rw [h3]
  generalize 2 ^ b = X at *
  generalize 2 ^ (64 - b) = P at *
  have hXP : P ≤ X * P := Nat.le_mul_of_pos_left _ (by omega)
  apply Nat.div_eq_of_lt_le
  · rw [Nat.sub_mul, Nat.one_mul]; omega
  · rw [Nat.sub_add_cancel hX1]; omega

/-- The header's values in the registers, for the working space at `ws`. -/
structure HRegs (bits : Nat) (ws : Addr) (g : Reg → BitVec 64) : Prop where
  s6 : g .s6 = ws + BitVec.ofNat 64 keyOff
  a7 : g .a7 = off (ws + BitVec.ofNat 64 keyOff) (slot (words bits) 0)
  t0 : g .t0 = BitVec.ofNat 64 (words bits)
  s5 : g .s5 = BitVec.ofNat 64 (8 * (words bits + 2))
  t1 : g .t1 = BitVec.ofNat 64 (keyWords bits)
  t2 : g .t2 = BitVec.ofNat 64 0
  t3 : g .t3 = BitVec.ofNat 64 (checks bits)
  t4 : g .t4 = BitVec.ofNat 64 (count bits)
  t5 : g .t5 = BitVec.ofNat 64 (draw bits)
  t6 : g .t6 = BitVec.ofNat 64 (2 ^ topBits bits - 1)

/-- The header's values into registers. -/
theorem values_ok {bits : Nat} (hs : Shape bits) (s : State) :
    WP isa (.block (values bits)) s fun v => (HRegs bits (s.gpr .a0) v.gpr ∧ v.mem = s.mem) ∧ Keep valRegs s v := by
  have hkw := hs.kw
  have hst := hs.stride
  have hcnt := hs.cnt
  have hchk := hs.chk
  have hdrw := hs.drw
  have hw : words bits < 2048 := by have := hs.w48; omega
  have hmk := hs.maskb
  refine WP.keep _ ?_ (by rfl) (by rfl)
  simp only [values, keyOff, hdrBytes]
  brun [hkw, hst, hcnt, hchk, hdrw, hw, hmk, exec_shift_d, exec_li]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> gsimp
  · rfl
  · simp only [off, slot, hdrBytes, keyOff, Nat.zero_mul, Nat.add_zero, Offset.add_add]
  · exact mask_val hs.b1 hs.b64

/-- The working space is writable and does not wrap. -/
theorem scr_of {bits : Nat} {σ s : State} (h : CIn bits σ) (hwr : s.wr = σ.wr) :
    Scr s (wsB σ) (8 * keyWords bits) := by
  have hsz := h.size
  have hfw := h.fw
  refine ⟨⟨σ.gpr .a0, keyOff, (σ.gpr .a1).toNat * 8, by rw [hwr, h.wr]; exact List.mem_cons_self, rfl,
    by omega, by omega⟩, ?_, Spill.al8 h.alW (by decide)⟩
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := Nat.mod_le ((σ.gpr .a0).toNat + keyOff % 2 ^ 64) (2 ^ 64)
  simp only [keyOff] at *
  omega

/-- The header's words. -/
structure Hdr (bits : Nat) (B R : Addr) (rl : BitVec 64) (m : Mem) : Prop where
  len : word m B 0 = BitVec.ofNat 64 (keyWords bits)
  w : word m B 48 = BitVec.ofNat 64 (words bits)
  arr : ∀ j < 8, word m B (8 * (8 + j)) = off B (slot (words bits) j)
  rand : word m B (8 * hRand) = R
  randLen : word m B (8 * hRandLen) = rl
  used : word m B (8 * hUsed) = BitVec.ofNat 64 0
  checks : word m B (8 * hChecks) = BitVec.ofNat 64 (checks bits)
  top : word m B (8 * hTop) = BitVec.ofNat 64 (2 ^ topBits bits - 1)
  k : word m B (8 * hK) = BitVec.ofNat 64 (draw bits)
  stride : word m B 224 = BitVec.ofNat 64 (8 * (words bits + 2))

/-- The header's word offsets. -/
def hdrWords : List Nat := [0, 48, 64, 72, 80, 88, 96, 104, 112, 120, 136, 144, 152, 168, 192, 216, 224]

theorem arr8 {j : Nat} (hj : j < 8) : 8 * (8 + j) ∈ hdrWords := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- A change of memory that keeps the header's words keeps `Hdr`. -/
theorem Hdr.keep {bits : Nat} {B R : Addr} {rl : BitVec 64} {m m' : Mem} (h : Hdr bits B R rl m)
    (hw : ∀ d ∈ hdrWords, word m' B d = word m B d) : Hdr bits B R rl m' :=
  ⟨(hw _ (by decide)).trans h.len, (hw _ (by decide)).trans h.w,
    fun j hj => (hw _ (arr8 hj)).trans (h.arr j hj), (hw _ (by decide)).trans h.rand,
    (hw _ (by decide)).trans h.randLen, (hw _ (by decide)).trans h.used, (hw _ (by decide)).trans h.checks,
    (hw _ (by decide)).trans h.top, (hw _ (by decide)).trans h.k, (hw _ (by decide)).trans h.stride⟩

/-- After the entry. -/
structure EntryPost (bits : Nat) (σ s : State) : Prop where
  s6 : s.gpr .s6 = wsB σ
  a7 : s.gpr .a7 = off (wsB σ) (slot (words bits) 0)
  t0 : s.gpr .t0 = BitVec.ofNat 64 (words bits)
  s5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (words bits + 2))
  a0 : s.gpr .a0 = σ.gpr .a0
  svd : Spill.Saved (σ.gpr .a0) σ.gpr savedSlots s.mem
  hdr : Hdr bits (wsB σ) (σ.gpr .a2) (σ.gpr .a3) s.mem
  cnt : word s.mem (wsB σ) (8 * hTrial) = BitVec.ofNat 64 (count bits)
  frame : Frame [⟨σ.gpr .a0 + BitVec.ofNat 64 saveOff, 112⟩, ⟨wsB σ, 256⟩] σ.mem s.mem
  sp : s.sp = σ.sp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  syms : s.syms = σ.syms

theorem savedSlots_fits : Spill.Fits savedSlots := by decide
theorem hdrSlots_fits : Spill.Fits hdrSlots := by decide
theorem savedSlots_in : ∀ p ∈ savedSlots, saveOff ≤ p.2 ∧ p.2 + 8 ≤ saveOff + 112 := by decide
theorem hdrSlots_in : ∀ p ∈ hdrSlots, 0 ≤ p.2 ∧ p.2 + 8 ≤ 0 + 256 := by decide
theorem hdrSlots_out : ∀ p ∈ hdrSlots, p.2 + 8 ≤ 64 ∨ 64 + 8 * 8 ≤ p.2 := by decide

/-- A change of bytes `[d, d + n)` of a region of `Z ≥ d + n` bytes at `B`. -/
theorem frame_outside {B : Addr} {Z d n : Nat} {rs : List Region} {m m' : Mem}
    (ho : Outside B d n m m') (hd : d + n ≤ Z) : Frame (⟨B, Z⟩ :: rs) m m' := fun x hx => by
  have := hx _ List.mem_cons_self
  simp only [Region.Contains] at this
  exact ho x (.inr (by simp only [ofs]; omega))

/-- The state after `c` has the stack pointer and the addresses of statics
it had before. -/
theorem wp_sp_syms {c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa c s fun s' => s'.sp = s.sp → s'.syms = s.syms → Q s') : WP isa c s Q := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq (RISCV64.Exec.sp he) (RISCV64.Exec.syms he)⟩

/-- The entry: the registers saved, the round's registers and the header. -/
theorem entry_ok {bits : Nat} (hs : Shape bits) {σ : State} (h : CIn bits σ) :
    WP isa (.block (setup bits)) σ (EntryPost bits σ) := by
  have hsz := h.size
  have hfw := h.fw
  have hkey := hs.key
  have hw48 := hs.w48
  have hw4 := hs.w4
  have hwsW : cW σ ∈ σ.wr := by rw [h.wr]; exact List.mem_cons_self
  have inWs : ∀ d, d + 8 ≤ (σ.gpr .a1).toNat * 8 → InRegions σ.wr (σ.gpr .a0 + BitVec.ofNat 64 d) 8 :=
    fun d hd => ⟨_, hwsW, by
      simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]; omega⟩
  refine wp_sp_syms ?_
  rw [setup, List.append_assoc, List.append_assoc, show save = Spill.saveCode .a0 savedSlots from rfl,
    show hdrSlots.map (fun (r, d) => Instr.store .d r .s6 d) = Spill.saveCode .s6 hdrSlots from rfl]
  refine Spill.save_ok (b := .a0) (l := savedSlots) h.alW savedSlots_fits.1 (fun p hp =>
    inWs _ (by have := savedSlots_in p hp; simp only [saveOff, keyOff] at *; omega)) ?_
  generalize hM : Spill.saveMem σ.mem (σ.gpr .a0) σ.gpr savedSlots = M
  rw [WP.block_append_iff]
  refine WP.mono (values_ok hs _) fun v ⟨⟨hr, vm⟩, kv⟩ => ?_
  have v6 : v.gpr .s6 = wsB σ := hr.s6
  have vwr : v.wr = σ.wr := kv.2.2
  refine Spill.save_ok (b := .s6) (l := hdrSlots) (by rw [v6]; exact Spill.al8 h.alW (by decide))
    hdrSlots_fits.1 (fun p hp => by
      rw [vwr, v6, Offset.add_add]
      exact inWs _ (by have := hdrSlots_in p hp; simp only [keyOff] at *; omega)) ?_
  generalize hM2 : Spill.saveMem v.mem (v.gpr .s6) v.gpr hdrSlots = M2
  have sc : Scr { v with mem := M2 } (wsB σ) (8 * keyWords bits) := scr_of h vwr
  have hZ : 128 ≤ 8 * keyWords bits := by omega
  refine WP.mono (VG.Proof.RsaKeyGen.RISCV64.Cand.hdrs_ok sc v6 hr.a7 hr.s5 hZ 8 (Nat.le_refl _))
    fun t ⟨⟨tw, tout⟩, kt⟩ tsp tsy => ?_
  have tg : ∀ r, r ≠ .t2 → t.gpr r = v.gpr r := fun r hr => kt.gpr (by simp [hr])
  have nw : (wsB σ).toNat + 256 ≤ 2 ^ 64 := by have := sc.nowrap; omega
  -- The header.
  have sv : ∀ r d, (r, d) ∈ hdrSlots → word t.mem (wsB σ) d = v.gpr r := fun r d hm => by
    have ho := hdrSlots_out (r, d) hm
    have hi := hdrSlots_in (r, d) hm
    dsimp only at ho hi
    refine (tout.word ho (by omega)).trans ?_
    show M2.readW _ 64 = _
    rw [← hM2, ← v6]
    exact Spill.saveMem_saved hdrSlots_fits _ _ _ (r, d) hm
  have hd : Hdr bits (wsB σ) (σ.gpr .a2) (σ.gpr .a3) t.mem :=
    ⟨(sv .t1 _ (by decide)).trans hr.t1, (sv .t0 _ (by decide)).trans hr.t0, tw,
      (sv .a2 _ (by decide)).trans (kv.gpr (by decide)), (sv .a3 _ (by decide)).trans (kv.gpr (by decide)),
      (sv .t2 _ (by decide)).trans hr.t2, (sv .t3 _ (by decide)).trans hr.t3, (sv .t6 _ (by decide)).trans hr.t6,
      (sv .t5 _ (by decide)).trans hr.t5, (sv .s5 _ (by decide)).trans hr.s5⟩
  -- What changed.
  have f₁ : Frame [⟨σ.gpr .a0 + BitVec.ofNat 64 saveOff, 112⟩] σ.mem M := by
    rw [← hM]; exact Spill.saveMem_frame savedSlots_in (by decide) _ _ _
  have f₂ : Frame [⟨wsB σ, 256⟩] M M2 := by
    have vm' : v.mem = M := vm
    rw [← hM2, vm', v6]
    have := Spill.saveMem_frame (lo := 0) (n := 256) hdrSlots_in (by decide) M (wsB σ) v.gpr
    rwa [BitVec.add_zero] at this
  have f₃ : Frame [⟨wsB σ, 256⟩] M2 t.mem := frame_outside tout (by omega)
  have dSK : Region.Disjoint ⟨σ.gpr .a0 + BitVec.ofNat 64 saveOff, 112⟩ ⟨wsB σ, 256⟩ :=
    Offset.disjoint _ (.inl (by decide)) (by simp only [saveOff, keyOff] at *; omega)
      (by simp only [keyOff] at *; omega)
  refine ⟨(tg _ (by decide)).trans v6, (tg _ (by decide)).trans hr.a7, (tg _ (by decide)).trans hr.t0,
    (tg _ (by decide)).trans hr.s5, (tg _ (by decide)).trans (kv.gpr (by decide)), ?_, hd,
    (sv .t4 _ (by decide)).trans hr.t4, ?_, tsp, kt.2.1.trans kv.2.1, kt.2.2.trans vwr, tsy⟩
  · have s₀ : Spill.Saved (σ.gpr .a0) σ.gpr savedSlots M := by
      rw [← hM]; exact Spill.saveMem_saved savedSlots_fits _ _ _
    exact s₀.frame_in (lo := saveOff) (n := 112) savedSlots_in (f₂.trans f₃) fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact dSK
  · exact (f₁.mono (by simp)).trans ((f₂.trans f₃).mono (by simp))

/-! ## The candidate -/

/-- The candidate, the tape and the test's result. -/
abbrev cand (bits : Nat) (σ : State) : Nat := Proof.Dsa.ProbablePrime.candidateAt (layout bits) σ.mem (σ.gpr .a0)
abbrev tape (σ : State) : Spec.RsaKeyGen.Rand := Spec.Rsa.bytesAt σ.mem (σ.gpr .a2) (σ.gpr .a3).toNat
abbrev res (bits : Nat) (σ : State) : Option (Bool × Spec.RsaKeyGen.Rand) :=
  Spec.Dsa.probablePrime (cand bits σ) (tape σ)

/-- After the entry, the Montgomery arithmetic's registers. -/
theorem env_of {bits : Nat} (hs : Shape bits) {σ s : State} (h : CIn bits σ) (ep : EntryPost bits σ s) :
    Env s (wsB σ) (8 * keyWords bits) (words bits) :=
  ⟨scr_of h ep.wr, ep.a7, ep.s5, ep.t0, ep.s6, hs.w4, by have := hs.w48; omega,
    by rw [hs.key]; simp only [slot, hdrBytes]; omega⟩

/-- A byte of the working space lies in `ws`. -/
theorem inW {bits : Nat} {σ : State} (h : CIn bits σ) {x : Addr}
    (hx : ofs (wsB σ) x < 8 * keyWords bits) : (cW σ).Contains x 1 := by
  have hsz := h.size
  have hfw := h.fw
  simp only [Region.Contains, ofs, wsB, keyOff] at hx hsz ⊢
  have : (x - σ.gpr .a0).toNat = (x - (σ.gpr .a0 + BitVec.ofNat 64 512)).toNat + 512 := by bv_omega
  omega

/-- The candidate's bytes lie below the working space. -/
theorem cand_sep {bits : Nat} {σ : State} (h : CIn bits σ) {i : Nat} (hi : i < 384) {x : Addr}
    (hx : ofs (wsB σ) x < 8 * keyWords bits) : off (σ.gpr .a0) i ≠ x := by
  rintro rfl
  have hsz := h.size
  have hfw := h.fw
  simp only [ofs, wsB, keyOff, off] at hx hsz
  have : (σ.gpr .a0 + BitVec.ofNat 64 i - (σ.gpr .a0 + BitVec.ofNat 64 512)).toNat = 2 ^ 64 - 512 + i := by
    bv_omega
  omega

/-- The candidate's bytes are unchanged by the entry. -/
theorem cand_keep {bits : Nat} {σ s : State} (ep : EntryPost bits σ s) {n : Nat} (hn : n ≤ 384) :
    Spec.Rsa.bytesAt s.mem (σ.gpr .a0) n = Spec.Rsa.bytesAt σ.mem (σ.gpr .a0) n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  refine ep.frame _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp only [Region.Contains, Offset.add_sub_add_left] <;> intro hc
  · exact Offset.not_lt_sub_ofNat (d := saveOff) (n := 112) (k := i) (Or.inl (by simp only [saveOff]; omega))
      (by omega) (by decide) (by decide) (by omega)
  · exact Offset.not_lt_sub_ofNat (d := keyOff) (n := 256) (k := i) (Or.inl (by simp only [keyOff]; omega))
      (by omega) (by decide) (by decide) (by omega)

/-- The candidate into array 0. -/
theorem loadC_ok {bits : Nat} (hs : Shape bits) {σ s : State} (h : CIn bits σ) (ep : EntryPost bits σ s) :
    WP isa (loadC bits) s fun t =>
      (A t.mem (wsB σ) (words bits) 0 = cand bits σ ∧
        Outside (wsB σ) (slot (words bits) 0) (8 * words bits) s.mem t.mem) ∧
      Keep [.s7, .s8, .a0, .s0, .t3, .t4, .t5] s t := by
  have e := env_of hs h ep
  have hlen := hs.hlenw
  have hlen1 := hs.hlen1
  have hw48 := hs.w48
  have hl384 : len bits ≤ 384 := by omega
  have hfw := h.fw
  have hsz := h.size
  have hl2 : len bits < 2048 := by omega
  unfold loadC
  refine WP.seq (WP.mono (WP.keep [.s7, .s8] (Q := fun (u : State) => u.gpr .s7 = off (σ.gpr .a0) 0 ∧
      u.gpr .s8 = BitVec.ofNat 64 (len bits) ∧ u.mem = s.mem) (by brun [ep.a0, hl2]) (by rfl) (by rfl))
    fun u ⟨⟨u7, u8, um⟩, ku⟩ => ?_)
  have eu : Env u (wsB σ) (8 * keyWords bits) (words bits) := e.keep ku (by decide)
  refine WP.mono (loadN_ok (k := len bits) eu.hs eu.a7 u7 u8 eu.t0 hlen1 hlen (by omega) (by simp only [slot, hdrBytes]; omega)
    (by simp only [slot, hdrBytes]; omega) (by have := eu.hZ; simp only [slot, hdrBytes] at *; omega)
    (fun i hi => ⟨_, by rw [ku.2.1, ku.2.2, ep.rd, ep.wr, h.wr]; exact List.mem_append_right _ List.mem_cons_self, by
      simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]; have := hs.key; omega⟩)
    (fun i hi x hx => cand_sep h (by omega) hx)) fun t ⟨tv, to, kt⟩ => ?_
  refine ⟨⟨?_, by rw [← um]; exact to⟩, (ku.trans kt).mono (by decide)⟩
  show Mont.wordsVal t.mem (wsB σ) (slot (words bits) 0) (words bits) = _
  rw [tv, um, cand_keep ep hl384]
  simp only [cand, Proof.Dsa.ProbablePrime.candidateAt, layout, BitVec.add_zero, ← hs.hlen]
  rfl

/-! ## The table -/

/-- The trial table. -/
abbrev K : List (String × List (BitVec 64)) := VG.Impl.RsaKeyGen.TrialTable32.consts

/-- The table, as trial division reads it. -/
structure Tab (s : State) : Prop where
  fit : (s.syms TrialTable32.symbol).toNat + 8 * 1024 ≤ 2 ^ 64
  al : (s.syms TrialTable32.symbol).toNat % 8 = 0
  rd : (⟨s.syms TrialTable32.symbol, 8 * 1024⟩ : Region) ∈ s.rd
  held : ∀ i < 1024, s.mem.readW (s.syms TrialTable32.symbol + BitVec.ofNat 64 (8 * i)) 64 =
    TrialTable32.packed.getD i 0
  wr : ∀ r ∈ s.wr, Region.Disjoint ⟨s.syms TrialTable32.symbol, 8 * 1024⟩ r

theorem tab_of {σ : State} (hk : ConstsOk K 512 σ) : Tab σ := by
  have hm : (TrialTable32.symbol, TrialTable32.packed) ∈ K := List.mem_cons_self
  have hl := VG.Proof.RsaKeyGen.TrialTable32.packed_length
  refine ⟨hl ▸ hk.fit hm, by have := hk.aligned hm; omega, hl ▸ hk.mem_rd hm,
    fun i hi => hk.readW hm (by rw [hl]; exact hi), hl ▸ hk.wr1⟩

/-- A change of memory apart from the table keeps it. -/
theorem Tab.frame {s t : State} (h : Tab s) {rs : List Region} (hf : Frame rs s.mem t.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨s.syms TrialTable32.symbol, 8 * 1024⟩ r) (sy : t.syms = s.syms)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : Tab t := by
  have hfit := h.fit
  refine ⟨sy ▸ h.fit, sy ▸ h.al, by rw [sy, hrd]; exact h.rd, fun i hi => ?_, by rw [sy, hwr]; exact h.wr⟩
  rw [sy, hf.readW (r := ⟨s.syms TrialTable32.symbol, 8 * 1024⟩) (Offset.contains_base _ (by omega) (by omega))
    hd (by decide)]
  exact h.held i hi

/-! ## The body -/

/-- What the body reads. -/
structure BIn (bits : Nat) (σ s : State) : Prop where
  hb : Bits bits
  cin : CIn bits σ
  env : Env s (wsB σ) (8 * keyWords bits) (words bits)
  hdr : Hdr bits (wsB σ) (σ.gpr .a2) (σ.gpr .a3) s.mem
  cnt : word s.mem (wsB σ) (8 * hTrial) = BitVec.ofNat 64 (count bits)
  cand : A s.mem (wsB σ) (words bits) 0 = cand bits σ
  tab : Tab s
  tape : Spec.Rsa.bytesAt s.mem (σ.gpr .a2) (σ.gpr .a3).toNat = tape σ
  syms : s.syms = σ.syms
  sp : s.sp = σ.sp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr

/-- After the body. -/
structure BOut (bits : Nat) (σ s t : State) : Prop where
  s6 : t.gpr .s6 = wsB σ
  stat : word t.mem (wsB σ) (8 * hStat) = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status (res bits σ))
  used : ∀ b rest, res bits σ = some (b, rest) →
    word t.mem (wsB σ) (8 * hUsed) = BitVec.ofNat 64 ((σ.gpr .a3).toNat - rest.length)
  frame : Frame [⟨wsB σ, 8 * keyWords bits⟩, below σ.sp 96] s.mem t.mem
  sp : t.sp = σ.sp
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr

/-- Trial division by the width's entries is RSA's. -/
theorem trial_spec {bits c : Nat} (hb : Bits bits) (large : 8161 < c) :
    VG.Proof.RsaKeyGen.trialPrefix c (count bits) = Spec.RsaKeyGen.obviouslyComposite bits c := by
  have := VG.Proof.RsaKeyGen.trialPrefix_spec (w := words bits) large
  rw [(shape_of hb).hcount, this]
  rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    simp [Spec.RsaKeyGen.obviouslyComposite, Spec.RsaKeyGen.trialPrimes, words]

/-- The candidate's facts the tests need. -/
theorem cand_facts {bits : Nat} {σ : State} (hb : Bits bits) (h : CIn bits σ) :
    8161 < cand bits σ ∧ 3 ≤ cand bits σ ∧ cand bits σ % 2 = 1 ∧
      Spec.RsaKeyGen.bitLength (cand bits σ - 1) = bits := by
  have hbl := h.bl
  have hodd := h.odd
  have hbig := (shape_of hb).big
  obtain ⟨hlo, -⟩ := (VG.Proof.Dsa.bitLength_iff_bounds (by omega)).mp hbl
  have : 2 ^ 13 ≤ 2 ^ (bits - 1) := Nat.pow_le_pow_right (by decide) hbig
  dsimp only [cand]
  exact ⟨by omega, by omega, hodd, VG.Proof.Dsa.Generation.predecessor_bits (by omega) hodd hbl⟩

/-- The header's word at `8 i` := `v` (`li` of `v` into `t2`, and `sth`). -/
theorem setHdr_ok {s : State} {B : Addr} {Z w v i : Nat} (e : Env s B Z w) (hv : v < 2048) (hi : i < 32) :
    WP isa (.block [.li .t2 v, sth .t2 i]) s fun x =>
      (x.mem = s.mem.writeW (off B (8 * i)) (BitVec.ofNat 64 v)) ∧ Keep [.t2] s x := by
  have hsc := e.hs
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ Z := e.hZ
  refine WP.keep _ ?_ (by rfl) (by rfl)
  simp only [sth]
  brun [e.s6, hv, show 8 * i < 2048 by omega, hsc.st (d := 8 * i) (n := 8) (by omega),
    hsc.al8 (d := 8 * i) (by omega) (by omega)]

/-- A composite: `hStat := 2`. -/
theorem comp_ok {bits : Nat} {σ s : State} (h : BIn bits σ s)
    (hc : Spec.RsaKeyGen.obviouslyComposite bits (cand bits σ) = true) :
    WP isa (.block [.li .t2 2, sth .t2 hStat]) s (BOut bits σ s) := by
  have e := h.env
  have hnw := e.hs.nowrap
  have hZ : 256 + 28 * (8 * (words bits + 2)) ≤ 8 * keyWords bits := e.hZ
  obtain ⟨hbig, -, hodd, -⟩ := cand_facts h.hb h.cin
  have hres : res bits σ = some (false, tape σ) := by
    rw [res, VG.Proof.Dsa.Generation.probablePrime_large (by omega) hodd, h.cin.bl, hc]; rfl
  refine wp_sp_syms (WP.mono (setHdr_ok (v := 2) (i := hStat) e (by decide) (by decide))
    fun x ⟨xm, kx⟩ xsp _ => ?_)
  have ho := VG.Proof.Bignum.writeW_outside s.mem (wsB σ) (d := 8 * hStat) (BitVec.ofNat 64 2)
    (by simp only [hStat]; omega)
  refine ⟨(kx.gpr (by decide)).trans e.s6, by rw [xm, VG.Proof.Bignum.word_writeW_self, hres]; rfl,
    fun b rest hr => ?_, by rw [xm]; exact frame_outside ho (by simp only [hStat]; omega), xsp.trans h.sp,
    kx.2.1.trans h.rd, kx.2.2.trans h.wr⟩
  rw [hres] at hr
  cases hr
  rw [xm, ho.word (by simp only [hStat, hUsed]; omega) (by simp only [hUsed]; omega), h.hdr.used]
  simp only [tape, Spec.Rsa.bytesAt, List.length_map, List.length_range, Nat.sub_self]

/-- The header's words lie apart from what `montPrep` writes. -/
theorem hdr_apart (w : Nat) :
    ∀ d ∈ 128 :: hdrWords, ∀ r ∈ VG.Proof.MillerRabin.RISCV64.Search.mpRanges w, d + 8 ≤ r.1 ∨ r.1 + r.2 ≤ d := by
  intro d hd r hr
  have hd' : (d + 8 ≤ 56 ∨ 64 ≤ d) ∧ d + 8 ≤ 256 := by revert d; decide
  simp only [VG.Proof.MillerRabin.RISCV64.Search.mpRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [slot, hdrBytes] <;> omega

/-- What `montPrep` writes lies within the working space. -/
theorem mp_within (w : Nat) :
    ∀ r ∈ VG.Proof.MillerRabin.RISCV64.Search.mpRanges w, r.1 + r.2 ≤ 256 + 28 * (8 * (w + 2)) := by
  intro r hr
  simp only [VG.Proof.MillerRabin.RISCV64.Search.mpRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [slot, hdrBytes, VG.Impl.MillerRabin.RISCV64.aE] <;>
    omega

/-- A byte of the tape lies outside the working space. -/
theorem tape_out {bits : Nat} {σ : State} (h : CIn bits σ) {i : Nat} (hi : i < (σ.gpr .a3).toNat) :
    ¬ ofs (wsB σ) (σ.gpr .a2 + BitVec.ofNat 64 i) < 8 * keyWords bits := fun hx =>
  h.wR _ (inW h hx) (by
    simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by have := (σ.gpr .a3).isLt; omega)]; omega)

/-- After the offset of a witness's top word is stored, from the body's
state `s`. -/
structure MP (bits : Nat) (σ s x : State) : Prop where
  hb : Bits bits
  cin : CIn bits σ
  env : Env x (wsB σ) (8 * keyWords bits) (words bits)
  cand : A x.mem (wsB σ) (words bits) 0 = cand bits σ
  hdr : Hdr bits (wsB σ) (σ.gpr .a2) (σ.gpr .a3) x.mem
  top : word x.mem (wsB σ) (8 * hTopOff) = BitVec.ofNat 64 (topOff bits)
  tape : Spec.Rsa.bytesAt x.mem (σ.gpr .a2) (σ.gpr .a3).toNat = tape σ
  sp : x.sp = σ.sp
  rd : x.rd = σ.rd
  wr : x.wr = σ.wr
  frame : Frame [⟨wsB σ, 8 * keyWords bits⟩, below σ.sp 96] s.mem x.mem

/-- The offset of a witness's top word, in the word trial division read its
count from. -/
theorem topOff_ok {bits : Nat} {σ s : State} (h : BIn bits σ s) :
    WP isa (.block [.li .t2 (topOff bits), sth .t2 hTopOff]) s (MP bits σ s) := by
  have e := h.env
  have sh := shape_of h.hb
  have cin := h.cin
  have hnw := e.hs.nowrap
  have hZ : 256 + 28 * (8 * (words bits + 2)) ≤ 8 * keyWords bits := e.hZ
  refine wp_sp_syms (WP.mono (setHdr_ok (v := topOff bits) (i := hTopOff) e sh.toff (by decide))
    fun x ⟨xm, kx⟩ xsp _ => ?_)
  have ho := VG.Proof.Mont.writeW_outside s.mem (wsB σ) (d := 8 * hTopOff) (BitVec.ofNat 64 (topOff bits))
    (by simp only [hTopOff]; omega)
  rw [← xm] at ho
  refine ⟨h.hb, cin, e.keep kx (by decide), ?_, h.hdr.keep fun d hd => ho.word (by
      have : d + 8 ≤ 128 ∨ 136 ≤ d := by revert d; decide
      simp only [hTopOff]; omega) (by have : d + 8 ≤ 256 := by revert d; decide
                                      omega),
    by rw [xm]; exact VG.Proof.Bignum.word_writeW_self _ _ _ _, ?_, xsp.trans h.sp, kx.2.1.trans h.rd,
    kx.2.2.trans h.wr, frame_outside ho (by simp only [hTopOff]; omega)⟩
  · rw [← h.cand]
    exact ho.wordsVal (.inr (by simp only [slot, hdrBytes, hTopOff]; omega))
      (by simp only [slot, hdrBytes]; omega)
  · rw [← h.tape]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    rw [List.mem_range] at hi
    exact ho _ (.inr (by have := tape_out cin hi; simp only [hTopOff, ofs, VG.Proof.Mont.ofs] at this ⊢; omega))

/-- After `montPrep`: the blinded loop's context, no octets read, the tape,
and memory changed only in the working space. -/
theorem montPrep_ctx {bits : Nat} {σ s x : State} (h : MP bits σ s x) :
    WP isa montPrep x fun v =>
      BCtx v (wsB σ) (keyWords bits) (words bits) (cand bits σ) (σ.gpr .a2) (σ.gpr .a3).toNat
        ((bits - 1) / 64) (topBits bits) (checks bits) ∧
      word v.mem (wsB σ) (8 * hUsed) = BitVec.ofNat 64 0 ∧
      Spec.Rsa.bytesAt v.mem (σ.gpr .a2) (σ.gpr .a3).toNat = tape σ ∧ v.sp = σ.sp ∧ v.rd = σ.rd ∧
      v.wr = σ.wr ∧ Frame [⟨wsB σ, 8 * keyWords bits⟩, below σ.sp 96] s.mem v.mem := by
  have sh := shape_of h.hb
  have cin := h.cin
  have hZ : 256 + 28 * (8 * (words bits + 2)) ≤ 8 * keyWords bits := h.env.hZ
  obtain ⟨hbig, h3, hodd, hbl1⟩ := cand_facts h.hb cin
  have hch := sh.ch63
  refine wp_sp_syms (WP.mono (VG.Proof.MillerRabin.RISCV64.Search.montPrep_ok h.env h.cand hodd h3)
    fun v ⟨⟨ev, v0, vinv, vt1, v1, v9, v10, vE, vl, vO⟩, kv⟩ vsp _ => ?_)
  have vw : ∀ d ∈ 128 :: hdrWords, word v.mem (wsB σ) d = word x.mem (wsB σ) d := fun d hd =>
    VG.Proof.Mont.Outs.word vO (hdr_apart _ d hd) (by
      have : d + 8 ≤ 256 := by revert d; decide
      omega)
  have hd : Hdr bits (wsB σ) (σ.gpr .a2) (σ.gpr .a3) v.mem :=
    h.hdr.keep fun d hdm => vw d (List.mem_cons_of_mem _ hdm)
  have vt : word v.mem (wsB σ) (8 * hTopOff) = BitVec.ofNat 64 (topOff bits) :=
    (vw _ List.mem_cons_self).trans h.top
  have prep : Prep v (wsB σ) (keyWords bits) (words bits) (cand bits σ) :=
    ⟨ev, hd.len, hd.w, hd.stride, hd.arr, v0, h3, hodd, vinv, vt1, v1, v9, v10, vE, vl⟩
  have vsp' : v.sp = σ.sp := vsp.trans h.sp
  have vrd : v.rd = σ.rd := kv.2.1.trans h.rd
  have vwr : v.wr = σ.wr := kv.2.2.trans h.wr
  have bc : BCtx v (wsB σ) (keyWords bits) (words bits) (cand bits σ) (σ.gpr .a2) (σ.gpr .a3).toNat
      ((bits - 1) / 64) (topBits bits) (checks bits) := by
    refine ⟨prep, hd.rand, by rw [hd.randLen, BitVec.ofNat_toNat, BitVec.setWidth_eq], by rw [hd.k, sh.hdraw],
      hd.top, by rw [vt, sh.hoff], hd.checks, sh.t0, sh.tw, sh.b1, sh.b64, by rw [hbl1]; exact sh.bt, hch,
      (σ.gpr .a3).isLt, fun i hi => ⟨_, List.mem_append_left _ (vrd ▸ cin.rd), ?_⟩,
      fun i hi y hy he => tape_out cin hi (he ▸ hy), by rw [vsp']; exact cin.sp16,
      by rw [vsp']; have := cin.spLo; omega,
      fun a ha hb => cin.sW a (sub96 σ a (by rw [vsp'] at ha; exact ha))
        (inW cin (by simp only [Region.Contains] at hb; exact hb)),
      fun i hi hc => cin.sR _ (sub96 σ _ (by rw [vsp'] at hc; exact hc)) ?_⟩ <;>
    · simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by have := (σ.gpr .a3).isLt; omega)]; omega
  have vtape : Spec.Rsa.bytesAt v.mem (σ.gpr .a2) (σ.gpr .a3).toNat = tape σ := by
    rw [← h.tape]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    rw [List.mem_range] at hi
    refine vO _ fun r hr => .inr ?_
    have h1 := tape_out cin hi
    have h2 := mp_within _ r hr
    change r.1 + r.2 ≤ ofs (wsB σ) _
    omega
  exact ⟨bc, hd.used, vtape, vsp', vrd, vwr, h.frame.trans
    ((VG.Proof.Mont.Outs.frame vO fun r hr => Nat.le_trans (mp_within _ r hr) hZ).mono (by simp))⟩

/-- The test's result, past trial division. -/
theorem res_mr {bits : Nat} {σ : State} (hb : Bits bits) (cin : CIn bits σ)
    (hc : Spec.RsaKeyGen.obviouslyComposite bits (cand bits σ) = false) :
    res bits σ = Spec.RsaKeyGen.loop (Spec.RsaKeyGen.mrStep (cand bits σ) (checks bits)
      (Spec.Rsa.splitTwos (cand bits σ - 1)).1 (Spec.Rsa.splitTwos (cand bits σ - 1)).2) (1, 0) (tape σ) := by
  obtain ⟨hbig, -, hodd, -⟩ := cand_facts hb cin
  rw [res, VG.Proof.Dsa.Generation.probablePrime_large (by omega) hodd, cin.bl, hc, (shape_of hb).hchecks]; rfl

/-- No small prime divides: the offset of a witness's top word, `montPrep`
and the blinded Miller–Rabin loop. -/
theorem mr_ok (Ri : RoundImpl) {bits : Nat} {σ s : State} (h : BIn bits σ s)
    (hc : Spec.RsaKeyGen.obviouslyComposite bits (cand bits σ) = false) :
    WP isa (.seq (.block [.li .t2 (topOff bits), sth .t2 hTopOff])
      (.seq montPrep (VG.Impl.MillerRabin.RISCV64.Blinded.millerRabin Ri.name Ri.code))) s (BOut bits σ s) := by
  refine WP.seq (WP.mono (topOff_ok h) fun x hx => ?_)
  refine WP.seq (WP.mono (montPrep_ctx hx) fun v ⟨bc, hu, ht, vsp, vrd, vwr, fv⟩ => ?_)
  refine WP.mono (millerRabin_ok Ri bc hu ht) fun t mo => ?_
  have hres := res_mr h.hb h.cin hc
  have f₃ : Frame [⟨wsB σ, 8 * keyWords bits⟩, below σ.sp 96] v.mem t.mem := by
    rw [← vsp]; exact mo.1.frame
  exact ⟨mo.1.prep.env.s6, by rw [hres]; exact mo.2.1, fun b rest hr => mo.2.2 b rest (hres ▸ hr),
    fv.trans f₃, mo.1.sp.trans vsp, mo.1.rd.trans vrd, mo.1.wr.trans vwr⟩

/-- Trial division's start. -/
theorem BIn.div {bits : Nat} {σ s : State} (h : BIn bits σ s) :
    VG.Proof.RsaKeyGen.RISCV64.Cand.DivIn s (wsB σ) (8 * keyWords bits) (words bits) (count bits) :=
  ⟨h.env, h.cnt, (shape_of h.hb).cnt1, (shape_of h.hb).cnt2, h.tab.fit, h.tab.al, h.tab.rd, h.tab.held⟩

/-- Trial division keeps the body's context. -/
theorem bin_after_trial {bits : Nat} {σ s u : State} (h : BIn bits σ s) (um : u.mem = s.mem)
    (ug : ∀ r, r ∉ VG.Proof.RsaKeyGen.RISCV64.Cand.tdRegs → u.gpr r = s.gpr r) (urd : u.rd = s.rd)
    (uwr : u.wr = s.wr) (usp : u.sp = s.sp) (usy : u.syms = s.syms) : BIn bits σ u :=
  ⟨h.hb, h.cin, h.env.keep ⟨ug, urd, uwr⟩ (by decide), by rw [um]; exact h.hdr, by rw [um]; exact h.cnt,
    by rw [um]; exact h.cand,
    h.tab.frame (rs := []) (by rw [um]; exact Frame.refl _ _) (fun _ h => absurd h List.not_mem_nil) usy urd uwr,
    by rw [um]; exact h.tape, usy.trans h.syms, usp.trans h.sp, urd.trans h.rd, uwr.trans h.wr⟩

/-- The body. -/
theorem body_ok (Ri : RoundImpl) {bits : Nat} {σ s : State} (h : BIn bits σ s) :
    WP isa (body bits Ri.name Ri.code) s (BOut bits σ s) := by
  obtain ⟨hbig, -, -, -⟩ := cand_facts h.hb h.cin
  unfold body
  refine WP.seq (WP.mono (VG.Proof.RsaKeyGen.RISCV64.Cand.TrialOk.trial_divOk.ok h.div)
    fun u ⟨u4, um, ug, urd, uwr, usp, usy⟩ => ?_)
  have hu : BIn bits σ u := bin_after_trial h um ug urd uwr usp usy
  rw [h.cand, trial_spec h.hb hbig] at u4
  have fr : ∀ t, BOut bits σ u t → BOut bits σ s t := fun t o =>
    ⟨o.s6, o.stat, o.used, by rw [← um]; exact o.frame, o.sp, o.rd, o.wr⟩
  refine WP.ite _ (Steps.eval_zero_ofNat u .a4 (by split <;> decide) u4) (fun hz => ?_) (fun hz => ?_)
  · have hc : Spec.RsaKeyGen.obviouslyComposite bits (cand bits σ) = false := by
      revert hz; cases Spec.RsaKeyGen.obviouslyComposite bits (cand bits σ) <;> simp
    exact WP.mono (mr_ok Ri hu hc) fr
  · have hc : Spec.RsaKeyGen.obviouslyComposite bits (cand bits σ) = true := by
      revert hz; cases Spec.RsaKeyGen.obviouslyComposite bits (cand bits σ) <;> simp
    exact WP.mono (comp_ok hu hc) fr

/-! ## The exit -/

theorem status_le (x : Option (Bool × Spec.RsaKeyGen.Rand)) : Proof.Dsa.ProbablePrime.status x ≤ 2 := by
  rcases x with _ | ⟨_ | _, _⟩ <;> simp [Proof.Dsa.ProbablePrime.status]

theorem status_eq_zero {x : Option (Bool × Spec.RsaKeyGen.Rand)} (h : Proof.Dsa.ProbablePrime.status x = 0) :
    x = none := by
  rcases x with _ | ⟨_ | _, _⟩ <;> first | rfl | cases h

theorem savedSlots_restorable : Spill.Restorable .t3 savedSlots := by decide
theorem savedSlots_regs : savedSlots.map Prod.fst =
    [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11, .ra, .a4] := by decide

/-- After the exit's first block: the calling convention's registers back,
the status in `a0`, `hUsed` in `t2` and `used` in `a4`. -/
def XMid (bits : Nat) (σ t f : State) : Prop :=
  abiPreserved σ f ∧ f.gpr .a0 = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status (res bits σ)) ∧
    f.gpr .t2 = word t.mem (wsB σ) (8 * hUsed) ∧ f.gpr .a4 = σ.gpr .a4 ∧ f.mem = t.mem ∧ f.wr = t.wr

theorem exitA_ok {bits : Nat} {σ s t : State} (h : CIn bits σ) (o : BOut bits σ s t)
    (svd : Spill.Saved (σ.gpr .a0) σ.gpr savedSlots t.mem) :
    WP isa (.block ([ldh .a0 hStat, ldh .t2 hUsed, .addi .t3 .s6 (-(keyOff : Int))] ++ restore)) t
      (XMid bits σ t) := by
  have hsc : Scr t (wsB σ) (8 * keyWords bits) := scr_of h o.wr
  have hsz := h.size
  have hfw := h.fw
  have hst := status_le (res bits σ)
  have hkw : 32 ≤ keyWords bits := by unfold keyWords; omega
  have hwsW : cW σ ∈ t.wr := by rw [o.wr, h.wr]; exact List.mem_cons_self
  have inWs : ∀ d, d + 8 ≤ (σ.gpr .a1).toNat * 8 → InRegions (t.rd ++ t.wr) (σ.gpr .a0 + BitVec.ofNat 64 d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hwsW, by
      simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]; omega⟩
  rw [WP.block_append_iff]
  have s6 := o.s6
  refine wp_sp_syms (WP.mono (WP.keep [.a0, .t2, .t3] (Q := fun (u : State) =>
      u.gpr .a0 = word t.mem (wsB σ) (8 * hStat) ∧ u.gpr .t2 = word t.mem (wsB σ) (8 * hUsed) ∧
      u.gpr .t3 = σ.gpr .a0 ∧ u.mem = t.mem) ?_ (by rfl) (by rfl)) fun u ⟨⟨u0, u2, u3, um⟩, ku⟩ usp _ => ?_)
  · have e3 : wsB σ - BitVec.ofNat 64 keyOff = σ.gpr .a0 := BitVec.add_sub_cancel _ _
    generalize wsB σ = B at hsc s6 e3 ⊢
    simp only [ldh, hStat, hUsed]
    brun [s6, show keyOff ≤ 2048 by decide, e3, hsc.ld (d := 160) (n := 8) (by omega),
      hsc.al8 (d := 160) (by omega) (by decide), hsc.ld (d := 152) (n := 8) (by omega),
      hsc.al8 (d := 152) (by omega) (by decide)]
  refine WP.mono (Spill.restore_wp (b := .t3) (B := σ.gpr .a0) h.alW u3 savedSlots_fits.1 savedSlots_restorable
    (fun p hp => by
      rw [ku.2.1, ku.2.2]
      exact inWs _ (by have := savedSlots_in p hp; simp only [saveOff, keyOff] at *; omega))
    (by rw [um]; exact svd)) fun f hf => ?_
  have hpres : ∀ r ∈ preserved, r ∈ savedSlots.map Prod.fst := by rw [savedSlots_regs]; decide
  have o0 : f.gpr .a0 = u.gpr .a0 := hf.other _ (by rw [savedSlots_regs]; decide)
  have o2 : f.gpr .t2 = u.gpr .t2 := hf.other _ (by rw [savedSlots_regs]; decide)
  refine ⟨⟨fun r hr => hf.gpr_of (.inl (hpres r hr)), hf.sp.trans (usp.trans o.sp),
      hf.gpr_of (.inl (by rw [savedSlots_regs]; decide))⟩, ?_, ?_,
    hf.gpr_of (.inl (by rw [savedSlots_regs]; decide)), hf.mem.trans um, hf.wr.trans ku.2.2⟩
  · rw [o0, u0]; exact o.stat
  · rw [o2, u2]

/-- What the exit leaves. -/
structure XOut (bits : Nat) (σ t f : State) : Prop where
  abi : abiPreserved σ f
  a0 : f.gpr .a0 = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status (res bits σ))
  frame : Frame [cU σ] t.mem f.mem
  used : ∀ b rest, res bits σ = some (b, rest) →
    Spec.Rsa.wordsAt f.mem (σ.gpr .a4) 1 = [BitVec.ofNat 64 ((σ.gpr .a3).toNat - rest.length)]

theorem exit_ok {bits : Nat} {σ s t : State} (h : CIn bits σ) (o : BOut bits σ s t)
    (svd : Spill.Saved (σ.gpr .a0) σ.gpr savedSlots t.mem) :
    WP isa exit t (XOut bits σ t) := by
  have hst := status_le (res bits σ)
  unfold exit
  refine WP.seq (WP.mono (exitA_ok h o svd) fun f ⟨fa, f0, f2, f4, fm, fwr⟩ => ?_)
  refine WP.ite _ (Steps.eval_zero_ofNat f .a0 (by omega) f0) (fun hz => ?_) (fun hz => ?_)
  · have h0 : Proof.Dsa.ProbablePrime.status (res bits σ) = 0 := by simpa using hz
    exact WP.block_nil ⟨fa, f0, by rw [fm]; exact Frame.refl _ _, fun b rest hr => by
      rw [status_eq_zero h0] at hr; cases hr⟩
  · have hU : InRegions f.wr (f.gpr .a4 + BitVec.ofNat 64 0) 8 := ⟨cU σ, by rw [fwr, o.wr, h.wr]; simp, by
      rw [f4]; simp only [Region.Contains, BitVec.add_zero, BitVec.sub_self, BitVec.toNat_zero]; omega⟩
    refine Steps.WP.cons (exec_store_d (by decide) (by rw [f4, BitVec.add_zero]; exact h.alU) hU)
      (WP.block_nil ⟨fa, f0, ?_, fun b rest hr => ?_⟩)
    · rw [f4, fm, BitVec.add_zero]
      exact (Frame.refl _ _).writeW List.mem_cons_self _ (by
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
    · simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero]
      rw [f4, Mem.readW_writeW_self64, f2, o.used b rest hr]

/-! ## The function -/

/-- A byte at offset `i` of `p` lies outside a region at offset `e`. -/
theorem not_in (p : Addr) {i e k : Nat} (h : i + 1 ≤ e ∨ e + k ≤ i) (hi : i + 1 ≤ 2 ^ 64) (he : e + k ≤ 2 ^ 64) :
    ¬ (⟨p + BitVec.ofNat 64 e, k⟩ : Region).Contains (p + BitVec.ofNat 64 i) 1 := fun hc =>
  Offset.disjoint p h hi he _ (Region.contains_self _ _) hc

/-- A region at offset `d` of `ws` lies in `ws`. -/
theorem sub_ws {σ : State} {d n : Nat} (h : d + n ≤ (σ.gpr .a1).toNat * 8) :
    Region.Sub ⟨σ.gpr .a0 + BitVec.ofNat 64 d, n⟩ (cW σ) :=
  Offset.sub_base _ h

/-- What the function leaves. -/
structure COut (bits : Nat) (σ f : State) : Prop where
  abi : abiPreserved σ f
  a0 : f.gpr .a0 = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status (res bits σ))
  keeps : Proof.Dsa.ModPow.Keeps (σ.gpr .a0) (σ.gpr .a1).toNat (layout bits).scratch σ.mem f.mem
  used : ∀ b rest, res bits σ = some (b, rest) →
    Spec.Rsa.wordsAt f.mem (σ.gpr .a4) 1 = [BitVec.ofNat 64 ((σ.gpr .a3).toNat - rest.length)]

/-- The bytes of `ws` the test keeps. -/
def Kept (bits : Nat) (σ : State) (m : Mem) : Prop :=
  ∀ i, i < 8 * (σ.gpr .a1).toNat → i < 384 ∨ 384 + (512 - 384 + 8 * keyWords bits) ≤ i →
    m (σ.gpr .a0 + BitVec.ofNat 64 i) = σ.mem (σ.gpr .a0 + BitVec.ofNat 64 i)

/-- After the entry and the candidate's load: the body's context, the saved
registers, and the bytes of `ws` kept. -/
theorem after_loadC {bits : Nat} (hb : Bits bits) {σ s₁ s₂ : State} (h : CIn bits σ) (hk : ConstsOk K 512 σ)
    (ep : EntryPost bits σ s₁)
    (hl : (A s₂.mem (wsB σ) (words bits) 0 = cand bits σ ∧
        Outside (wsB σ) (slot (words bits) 0) (8 * words bits) s₁.mem s₂.mem) ∧
      Keep [.s7, .s8, .a0, .s0, .t3, .t4, .t5] s₁ s₂) (sp₂ : s₂.sp = s₁.sp) (sy₂ : s₂.syms = s₁.syms) :
    BIn bits σ s₂ ∧ Spill.Saved (σ.gpr .a0) σ.gpr savedSlots s₂.mem ∧ Kept bits σ s₂.mem := by
  obtain ⟨⟨c₂, o₂⟩, k₂⟩ := hl
  have hs := shape_of hb
  have hsz := h.size
  have hfw := h.fw
  have hkey := hs.key
  have hw48 := hs.w48
  have hW : cW σ ∈ σ.wr := by rw [h.wr]; exact List.mem_cons_self
  have hslot : slot (words bits) 0 + 8 * words bits ≤ 8 * keyWords bits := by
    simp only [slot, VG.Impl.Bignum.hdrBytes]; omega
  have f₁ : Frame [cW σ] σ.mem s₁.mem := ep.frame.sub fun r hr => ⟨cW σ, List.mem_cons_self, by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact sub_ws (by simp only [saveOff, keyOff] at *; omega)⟩
  have f₂ : Frame [⟨wsB σ, 8 * keyWords bits⟩] s₁.mem s₂.mem := frame_outside o₂ hslot
  have f₂' : Frame [cW σ] s₁.mem s₂.mem := f₂.sub fun r hr => ⟨cW σ, List.mem_cons_self, by
    rw [List.mem_singleton] at hr; subst hr; exact sub_ws (by simp only [keyOff] at *; omega)⟩
  have fW := f₁.trans f₂'
  have bin : BIn bits σ s₂ := by
    refine ⟨hb, h, (env_of hs h ep).keep k₂ (by decide), ep.hdr.keep fun d hd => ?_, ?_, c₂,
      (tab_of hk).frame fW (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact (tab_of hk).wr _ hW)
        (sy₂.trans ep.syms) (k₂.2.1.trans ep.rd) (k₂.2.2.trans ep.wr), ?_, sy₂.trans ep.syms,
      sp₂.trans ep.sp, k₂.2.1.trans ep.rd, k₂.2.2.trans ep.wr⟩
    · have : d + 8 ≤ 256 := by revert d; decide
      exact o₂.word (.inl (by simp only [slot, VG.Impl.Bignum.hdrBytes]; omega)) (by
        have := (env_of hs h ep).hs.nowrap; omega)
    · rw [o₂.word (.inl (by simp only [slot, VG.Impl.Bignum.hdrBytes, hTrial]; omega)) (by
        have := (env_of hs h ep).hs.nowrap; simp only [hTrial]; omega)]
      exact ep.cnt
    · simp only [Spec.Rsa.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      rw [List.mem_range] at hi
      exact fW.bytes (R := cR σ) (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact h.wR.symm)
        (by have := (σ.gpr .a3).isLt; exact Nat.le_of_lt this) hi
  refine ⟨bin, ep.svd.frame_in (lo := saveOff) (n := 112) savedSlots_in f₂ fun r hr => ?_, fun i hi hout => ?_⟩
  · rw [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl (show saveOff + 112 ≤ keyOff by decide)) (by simp only [saveOff] at *; omega)
      (by simp only [keyOff] at *; omega)
  simp only [keyOff] at hsz
  have e₁ : s₂.mem (σ.gpr .a0 + BitVec.ofNat 64 i) = s₁.mem (σ.gpr .a0 + BitVec.ofNat 64 i) :=
    f₂ _ fun r hr hc => by
      rw [List.mem_singleton] at hr; subst hr
      exact not_in _ (e := keyOff) (by simp only [keyOff]; omega) (by omega) (by simp only [keyOff]; omega) hc
  have e₀ : s₁.mem (σ.gpr .a0 + BitVec.ofNat 64 i) = σ.mem (σ.gpr .a0 + BitVec.ofNat 64 i) :=
    ep.frame _ fun r hr hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact not_in _ (e := saveOff) (by simp only [saveOff]; omega) (by omega) (by simp only [saveOff]; omega) hc
      · exact not_in _ (e := keyOff) (by simp only [keyOff]; omega) (by omega) (by simp only [keyOff]; omega) hc
  rw [e₁, e₀]

/-- The saved registers survive the body. -/
theorem saved_body {bits : Nat} {σ s t : State} (h : CIn bits σ) (bo : BOut bits σ s t)
    (sv : Spill.Saved (σ.gpr .a0) σ.gpr savedSlots s.mem) :
    Spill.Saved (σ.gpr .a0) σ.gpr savedSlots t.mem := by
  have hsz := h.size
  have hfw := h.fw
  refine sv.frame_in (lo := saveOff) (n := 112) savedSlots_in bo.frame fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ (.inl (show saveOff + 112 ≤ keyOff by decide)) (by simp only [saveOff] at *; omega)
      (by simp only [keyOff] at *; omega)
  · exact ((h.sW.sub_left (sub96 σ)).symm.sub_left (sub_ws (by simp only [saveOff, keyOff] at *; omega)))

/-- The body and the exit, from the body's context. -/
theorem tail_ok (Ri : RoundImpl) {bits : Nat} {σ s₂ : State} (h : CIn bits σ) (bin : BIn bits σ s₂)
    (sv₂ : Spill.Saved (σ.gpr .a0) σ.gpr savedSlots s₂.mem) (kept : Kept bits σ s₂.mem) :
    WP isa (.seq (body bits Ri.name Ri.code) exit) s₂ (COut bits σ) := by
  have hsz := h.size
  have hfw := h.fw
  refine WP.seq (WP.mono (body_ok Ri bin) fun t bo => ?_)
  refine WP.mono (exit_ok h bo (saved_body h bo sv₂)) fun f xo => ⟨xo.abi, xo.a0, fun i hi hout => ?_, xo.used⟩
  simp only [layout, List.mem_singleton, forall_eq, saveOff, keyOff] at hout hsz
  have inW : (cW σ).Contains (σ.gpr .a0 + BitVec.ofNat 64 i) 1 := Offset.contains_base _ (by omega) (by omega)
  have e₃ : f.mem (σ.gpr .a0 + BitVec.ofNat 64 i) = t.mem (σ.gpr .a0 + BitVec.ofNat 64 i) :=
    xo.frame _ fun r hr hc => by rw [List.mem_singleton] at hr; subst hr; exact h.wU _ inW hc
  have e₂ : t.mem (σ.gpr .a0 + BitVec.ofNat 64 i) = s₂.mem (σ.gpr .a0 + BitVec.ofNat 64 i) :=
    bo.frame _ fun r hr hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact not_in _ (e := keyOff) (by simp only [keyOff]; omega) (by omega) (by simp only [keyOff]; omega) hc
      · exact h.sW _ (sub96 σ _ hc) inW
  rw [e₃, e₂, kept i hi (by omega)]

theorem code_ok (Ri : RoundImpl) {bits : Nat} (hb : Bits bits) {σ : State} (h : CIn bits σ)
    (hk : ConstsOk K 512 σ) : WP isa (code bits Ri.name Ri.code) σ (COut bits σ) := by
  have hs := shape_of hb
  unfold code
  refine WP.seq (WP.mono (entry_ok hs h) fun s₁ ep => ?_)
  refine WP.seq (wp_sp_syms (WP.mono (loadC_ok hs h ep) fun s₂ hl sp₂ sy₂ => ?_))
  obtain ⟨bin, sv₂, kept⟩ := after_loadC hb h hk ep hl sp₂ sy₂
  exact tail_ok Ri h bin sv₂ kept

end VG.Proof.Dsa.RISCV64.Prime
