import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Ctx
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.LoadC
import VerifiedGarbage.Proof.Bignum.AArch64.HdrPairs

/-!
# An RSA key from its primes on AArch64: the entry and the head

`entry` stores the arguments in the header, with its base in `x0`
(`keyEntry_ok`); `Keys.head` sets up the working space for `W = n_len / 8`
(`kHead_ok`); together they leave `KS` (`keyStart_k`).
-/

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (kE kElen)

theorem keyEntry_eq : entry = ([.ldrSp .x8 64, .str .x .x0 .x8 (8 * kNo), .str .x .x1 .x8 (8 * kNl),
    .str .x .x2 .x8 (8 * kDo), .str .x .x4 .x8 (8 * kPp), .str .x .x5 .x8 (8 * kPl),
    .str .x .x6 .x8 (8 * kQp)] : List Instr) ++
    (hdrPairs [(0, kDp), (2, kDq), (4, kQi), (6, kE), (7, kElen)] ++ ([mov .x0 .x8] : List Instr)) := rfl

/-- The header after the stores from registers. -/
def keyEntryMemA (m : Mem) (B : Addr) (vno vnl vdo vpp vpl vqp : BitVec 64) : Mem :=
  (((((m.writeW (off B (8 * kNo)) vno).writeW (off B (8 * kNl)) vnl).writeW (off B (8 * kDo)) vdo).writeW
    (off B (8 * kPp)) vpp).writeW (off B (8 * kPl)) vpl).writeW (off B (8 * kQp)) vqp

/-- The header after the entry's stores. -/
def keyEntryMem (m : Mem) (B : Addr) (vno vnl vdo vpp vpl vqp vdp vdq vqi ve vel : BitVec 64) : Mem :=
  (((((keyEntryMemA m B vno vnl vdo vpp vpl vqp).writeW (off B (8 * kDp)) vdp).writeW (off B (8 * kDq)) vdq).writeW
    (off B (8 * kQi)) vqi).writeW (off B (8 * kE)) ve).writeW (off B (8 * kElen)) vel

theorem keyEntryMemA_outside (m : Mem) (B : Addr) (vno vnl vdo vpp vpl vqp : BitVec 64) :
    Outside B 0 (8 * 32) m (keyEntryMemA m B vno vnl vdo vpp vpl vqp) := by
  unfold keyEntryMemA
  repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _)

/-- The header words the entry stores. -/
structure EntryArgs (m : Mem) (B : Addr) (vno vnl vdo vpp vpl vqp vdp vdq vqi ve vel : BitVec 64) : Prop where
  no : word m B (8 * kNo) = vno
  nl : word m B (8 * kNl) = vnl
  dd : word m B (8 * kDo) = vdo
  pp : word m B (8 * kPp) = vpp
  pl : word m B (8 * kPl) = vpl
  qp : word m B (8 * kQp) = vqp
  dp : word m B (8 * kDp) = vdp
  dq : word m B (8 * kDq) = vdq
  qi : word m B (8 * kQi) = vqi
  e : word m B (8 * kE) = ve
  el : word m B (8 * kElen) = vel

theorem keyEntryMem_facts (m : Mem) (B : Addr) (vno vnl vdo vpp vpl vqp vdp vdq vqi ve vel : BitVec 64) :
    EntryArgs (keyEntryMem m B vno vnl vdo vpp vpl vqp vdp vdq vqi ve vel) B vno vnl vdo vpp vpl vqp vdp vdq vqi ve
        vel ∧
      Outside B 0 (8 * 32) m (keyEntryMem m B vno vnl vdo vpp vpl vqp vdp vdq vqi ve vel) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> unfold keyEntryMem keyEntryMemA
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

/-- What `entry` leaves, from the state `s` on entry. -/
structure KeyEntryPost (s t : State) (B : Addr) : Prop where
  x0 : t.gpr .x0 = B
  args : EntryArgs t.mem B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (stackArg s 0)
    (stackArg s 2) (stackArg s 4) (stackArg s 6) (stackArg s 7)
  frame : Outside B 0 (8 * 32) s.mem t.mem
  keep : Keep [.x0, .x8, .x9] s t

/-- `entry`: the header, from the arguments, and the working space's base
(stack argument 8) in `x0`. -/
theorem keyEntry_ok {s : State} {B : Addr} (hB : stackArg s 8 = B)
    (hw : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8)
    (ha : ∀ j < 10, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8)
    (hsep : ∀ j < 10, ∀ m', Outside B 0 (8 * 32) s.mem m' → m'.readW (stackArgAddr s j) 64 = stackArg s j) :
    WP isa (.block entry) s (KeyEntryPost s · B) := by
  have hB' : s.mem.readW (s.sp + BitVec.ofNat 64 64) 64 = B := hB
  have ha8 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 64) 8 := ha 8 (by decide)
  have ho : 64 % 8 = 0 ∧ 64 < 32768 := ⟨rfl, by decide⟩
  rw [keyEntry_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.x8] (Q := fun t => t.gpr .x8 = B ∧
      t.mem = keyEntryMemA s.mem B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6)) ?_
      (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨h8, hm₁⟩, k₁⟩ => ?_
  · brun [exec_ldrSp ho ha8, hB', hdr_enc (show kNo < 32 by decide), hdr_enc (show kNl < 32 by decide),
      hdr_enc (show kDo < 32 by decide), hdr_enc (show kPp < 32 by decide), hdr_enc (show kPl < 32 by decide),
      hdr_enc (show kQp < 32 by decide), hw kNo (by decide), hw kNl (by decide), hw kDo (by decide),
      hw kPp (by decide), hw kPl (by decide), hw kQp (by decide)]
    rfl
  rw [WP.block_append_iff]
  refine WP.mono (hdrPairs_ok _ t₁ ?_ h8 k₁.sp k₁.rd k₁.wr
    (by rw [hm₁]; exact keyEntryMemA_outside _ _ _ _ _ _ _ _)) fun t₂ ⟨hm₂, k₂⟩ => ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, by decide, ha _ (by decide), hsep _ (by decide), hw _ (by decide)⟩
  have h8₂ : t₂.gpr .x8 = B := (k₂.gpr .x8 (by decide)).trans h8
  have k12 := k₁.trans k₂
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = B ∧ t.mem = t₂.mem) (by brun [h8₂])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h0, hm⟩, k₃⟩ => ?_
  have hmem : t.mem = keyEntryMem s.mem B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x4) (s.gpr .x5)
      (s.gpr .x6) (stackArg s 0) (stackArg s 2) (stackArg s 4) (stackArg s 6) (stackArg s 7) := by
    rw [hm, hm₂, hm₁]; rfl
  obtain ⟨hA, ho'⟩ := keyEntryMem_facts s.mem B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x4) (s.gpr .x5)
    (s.gpr .x6) (stackArg s 0) (stackArg s 2) (stackArg s 4) (stackArg s 6) (stackArg s 7)
  rw [← hmem] at hA ho'
  exact ⟨h0, hA, ho', (k12.trans k₃).mono (by decide)⟩

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The working space set up: `KS` from the state on entry, after `entry`
and `Keys.head`. -/
theorem keyStart_k {s : State} (c : KCtx s) :
    WP isa (.block (entry ++ VG.Impl.Rsa.AArch64.Keys.head)) s fun t => KS (keyIn s) s t := by
  have hs := c.hs
  have hn := hs.nowrap
  have hZ := c.hZ
  have L := c.L
  have hpl1 := L.pl1
  have hpl2 := L.pl2
  have hpl8 := L.pl8
  have hx1 := c.x1
  have epl : (keyIn s).pl = (s.gpr .x5).toNat := rfl
  have eWk : (keyIn s).W = 2 * (s.gpr .x5).toNat / 8 := rfl
  rw [WP.block_append_iff]
  refine WP.mono (keyEntry_ok rfl (fun i hi => hs.st (by omega)) c.ha c.hsep) fun t₁ he => ?_
  have hs₁ := hs.congr he.keep.wr
  have hnl : word t₁.mem (arg s 8) (8 * Public.sK) = BitVec.ofNat 64 (2 * (s.gpr .x5).toNat) := by
    rw [show Public.sK = kNl from rfl, he.args.nl, ← hx1, ofNat_toNat64]
  refine WP.mono (kHead_ok hs₁ he.x0 (by omega) (by omega) (by omega) hnl) fun t₂ ⟨hw₂, _, hf₂, k₂⟩ => ?_
  have ew : wk (2 * (s.gpr .x5).toNat) = (keyIn s).W := by simp only [wk, KIn.W, keyIn]; omega
  rw [ew] at hw₂
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have eS : sStride = 28 := rfl
  have eM : Public.sMask = 22 := rfl
  have hi₁ : InScr (arg s 8) ((arg s 9).toNat * 8) s.mem t₁.mem := InScr.of_outside he.frame (by omega)
  have hi₂ : InScr (arg s 8) ((arg s 9).toNat * 8) t₁.mem t₂.mem := InScr.of_frm hf₂ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl) <;> dsimp only <;> omega)
  have hi := hi₁.trans hi₂
  have kk := he.keep.trans k₂
  have hA₁ : KArgs t₁.mem (keyIn s) :=
    ⟨he.args.no, (he.args.nl.trans (by rw [← hx1, ofNat_toNat64]) :
        word t₁.mem (arg s 8) (8 * kNl) = BitVec.ofNat 64 (2 * (s.gpr .x5).toNat)), he.args.dd, he.args.pp,
      (he.args.pl.trans (ofNat_toNat64 _).symm : word t₁.mem (arg s 8) (8 * kPl) = BitVec.ofNat 64 (s.gpr .x5).toNat),
      he.args.qp, he.args.dp, he.args.dq, he.args.qi, he.args.e,
      (he.args.el.trans (ofNat_toNat64 _).symm : word t₁.mem (arg s 8) (8 * kElen) = BitVec.ofNat 64 (arg s 7).toNat)⟩
  exact ⟨hw₂, hA₁.congr fun i hi' => hf₂.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> omega) (by omega),
    c.p.congrK hi kk, c.q.congrK hi kk, c.e.congrK hi kk, hi, kk.wr, kk.mono (by decide)⟩

end VG.Proof.RsaKeyGen.AArch64.Key
