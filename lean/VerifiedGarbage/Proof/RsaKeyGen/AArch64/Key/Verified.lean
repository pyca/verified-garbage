module

public import VerifiedGarbage.Proof.Rsa.AArch64.InvLaw
public import VerifiedGarbage.Proof.RsaKeyGen.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.CTTail
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Ctx
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Shared
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Front
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.RsaKeyGen.KeyOp
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.State
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.CTLcm
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.DPart
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.CTSmall
import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Contract
public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Key
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.CTBase
import VerifiedGarbage.Proof.Rsa.AArch64.CvCT
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Pieces
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.CTBase
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Front
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvCT
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Pieces
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.LoadC
public import VerifiedGarbage.Proof.Bignum.AArch64.HdrPairs
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Front
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Ctx
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.LoadC
meta import VerifiedGarbage.Proof.Bignum.AArch64.HdrPairs
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Front

/-! ### `RsaKeyGen.AArch64.Key.CTFront`, which only this module used -/

section

/-! ### `RsaKeyGen.AArch64.Key.Entry`, which this module and modules that import it used -/

section

/-!
# An RSA key from its primes on AArch64: the entry and the head

`entry` stores the arguments in the header, with its base in `x0`
(`keyEntry_ok`); `Keys.head` sets up the working space for `W = n_len / 8`
(`kHead_ok`); together they leave `KS` (`keyStart_k`).
-/

@[expose] public section

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
  refine WP.mono (keyEntry_ok rfl (fun i hi => hs.st (by omega_using [hZ, hpl1, hx1, epl, hi])) c.ha c.hsep) fun t₁ he => ?_
  have hs₁ := hs.congr he.keep.wr
  have hnl : word t₁.mem (arg s 8) (8 * Public.sK) = BitVec.ofNat 64 (2 * (s.gpr .x5).toNat) := by
    rw [show Public.sK = kNl from rfl, he.args.nl, ← hx1, ofNat_toNat64]
  refine WP.mono (kHead_ok hs₁ he.x0 (by omega_using [hpl1, epl]) (by omega_using [hpl2, epl]) (by omega_using [hZ, hx1]) hnl) fun t₂ ⟨hw₂, _, hf₂, k₂⟩ => ?_
  have ew : wk (2 * (s.gpr .x5).toNat) = (keyIn s).W := by simp only [wk, KIn.W, keyIn]; omega_using [hpl8, epl]
  rw [ew] at hw₂
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have eS : sStride = 28 := rfl
  have eM : Public.sMask = 22 := rfl
  have hi₁ : InScr (arg s 8) ((arg s 9).toNat * 8) s.mem t₁.mem := InScr.of_outside he.frame (by omega_using [hZ, hpl1, hx1, epl])
  have hi₂ : InScr (arg s 8) ((arg s 9).toNat * 8) t₁.mem t₂.mem := InScr.of_frm hf₂ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl) <;> dsimp only <;> omega_using [hZ, hpl1, hx1, epl, eW, eA, eS, eM])
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
      rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> omega_using [eW, hi', eA, eS, eM]) (by omega_using [hi']),
    c.p.congrK hi kk, c.q.congrK hi kk, c.e.congrK hi kk, hi, kk.wr, kk.mono (by decide)⟩

end VG.Proof.RsaKeyGen.AArch64.Key

end

end

/-!
# An RSA key from its primes on AArch64: constant time, the entry, the loads, the order and `p − 1`, `q − 1`

`start_ct`: `entry` and `Keys.head`, from the stack pointer and then from
the working space's base (stack argument 8), which correctness pins to the
public data. The loads take the pointer and the length from the header,
which correctness pins too (`loadA_ct0`, `loadE_ct0`); the rest are pieces
of the key routines. Each stage is checked with no postcondition, the facts
between its parts from their correctness (`kg_app0`), and the facts after
it from the correctness of the whole stage: `loads_k`, `order_k`,
`decTo_k`, and `front_k` for all of them (`front_ct`, to `KG PF`).

`keyCT_of`: runs the contract relates (`keyPub`) have the same public data
(`kpubOf_eq`), so the contract's `ConstantTime` follows from the code's
constant time in `Two KRel`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-! ## The entry -/

/-- A state the contract allows, with the public data `p`. -/
def KRel (p : KP) (s : State) : Prop := keyPre s ∧ (keyIn s).pub = p.q ∧ (keyIn s).st = p.st

/-- After `entry`'s first instruction: the working space's base in `x8`. -/
def KC1 (p : KP) (t : State) : Prop :=
  ∃ s, KRel p s ∧ t.gpr .x8 = p.q.B ∧ WP isa (.block (entry.drop 1 ++ VG.Impl.Rsa.AArch64.Keys.head)) t
    (KS (keyIn s) s)

theorem keyEntry_split : entry ++ VG.Impl.Rsa.AArch64.Keys.head = ([.ldrSp .x8 64] : List Instr) ++
    (entry.drop 1 ++ VG.Impl.Rsa.AArch64.Keys.head) := rfl

/-- `entry` and `Keys.head`. -/
theorem start_ct : RelCT isa (Two KRel) (.block (entry ++ VG.Impl.Rsa.AArch64.Keys.head)) (Two (KG NF)) := by
  rw [keyEntry_split]
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := KC1) [] (fun _ _ _ _ _ _ hr => by simp at hr)
    (by taint_decide) ?_)
    (two_piece [.x8] (fun p s₁ s₂ ⟨_, _, a₁, _⟩ ⟨_, _, a₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [a₁, a₂]) (by taint_decide)
      fun p t ⟨s, ⟨hpre, he, hst⟩, _, hw⟩ => WP.mono hw fun u hu =>
        ⟨keyIn s, s, he, hst, hu, (keyCtx_of hpre).L, (keyCtx_of hpre).O, trivial⟩))
  intro p s ⟨hpre, he, hst⟩
  have c := keyCtx_of hpre
  have hh : WP isa (.block (([.ldrSp .x8 64] : List Instr) ++ (entry.drop 1 ++ VG.Impl.Rsa.AArch64.Keys.head))) s
      (KS (keyIn s) s) := by
    rw [← keyEntry_split]; exact keyStart_k c
  have hB' : s.mem.readW (s.sp + BitVec.ofNat 64 64) 64 = stackArg s 8 := rfl
  have ha8 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 64) 8 := c.ha 8 (by decide)
  have ho : 64 % 8 = 0 ∧ 64 < 32768 := ⟨rfl, by decide⟩
  refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.x8] (Q := fun t => t.gpr .x8 = stackArg s 8)
    (by brun [exec_ldrSp ho ha8, hB']) (by decide) (by decide) (by decide +kernel))) fun t ⟨hw, h8, _⟩ =>
      ⟨s, ⟨hpre, he, hst⟩, h8.trans (congrArg KQ.B he), hw⟩

/-! ## The loads -/

/-- `loadA j sPtr sLen`, for the number whose pointer and length (functions
of the public inputs) are in the header slots `sPtr` and `sLen`. -/
theorem loadA_ct0 {F : KIn → State → Prop} {j sPtr sLen : Nat} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32)
    (ptr : KQ → Addr) (len : KQ → Nat)
    (hA : ∀ I s₀ s, KS I s₀ s → word s.mem I.B (8 * sPtr) = ptr I.pub ∧
      word s.mem I.B (8 * sLen) = BitVec.ofNat 64 (len I.pub))
    {hc₁ hc₂ hc₃ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base j .x8 ++ ([movi .x7 0] : List Instr)))
      zeroAcc) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base j .x8 ++ ([ldh .x1 sPtr, ldh .x2 sLen] :
      List Instr))) hc₂).isSome = true)
    (ht₃ : (taint.check (Taint.ofRegs [.x0, .x8, .x1, .x2]) loadBE hc₃).isSome = true) :
    RelCT isa (Two (KG F)) (seqs (loadA j sPtr sLen)) fun _ _ => True := by
  show RelCT isa _ (.seq (zeroA j) (.seq (.block (ws ++ base j .x8 ++ ([ldh .x1 sPtr, ldh .x2 sLen] :
    List Instr))) loadBE)) _
  refine RelCT.assoc (kpin_seq0 [.x0, .x8, .x1, .x2]
    (fun p : KP => ioVal p.q.B (off p.q.B (slot p.q.W j)) (ptr p.q) (len p.q))
    (RelCT.seq (kg_ct (G := NF) (zeroA_ct0 ht₁) fun I _ s h _ _ => WP.mono (zeroA_k h hj) fun _ ⟨ht, _⟩ =>
      ⟨ht, trivial⟩) (two_taint [.x0] (pins_kg NF) ht₂)) (fun p s h => ?_) ht₃)
  obtain ⟨I, s₀, he, -, hk, -⟩ := h
  rw [← he]
  refine WP.seq (WP.mono (zeroA_k hk hj) fun t ⟨ht, _⟩ => ?_)
  obtain ⟨hp, hl⟩ := hA I s₀ t ht
  exact loadBlk_ok ht.ws hP hL hp hl

/-- `loadA j sPtr sLen` changes array `j`. -/
theorem loadA_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {j sPtr sLen len : Nat} {ptr : Addr} {bs : List Byte}
    (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (hp : word s.mem I.B (8 * sPtr) = ptr)
    (hl : word s.mem I.B (8 * sLen) = BitVec.ofNat 64 len) (hsrc : Src s I.B I.Z ptr bs) (hlen : bs.length = len)
    (hl1 : 1 ≤ len) (hlw : len ≤ 8 * I.W) :
    WP isa (seqs (loadA j sPtr sLen)) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr j] s.mem t.mem :=
  WP.mono (loadA_ok h.ws hj hP hL hp hl hsrc hlen hl1 hlw) fun _ ⟨_, o, _, _, k⟩ =>
    have f := KF.arr1 (B := I.B) (W := I.W) (j := j) o (Nat.le_refl _) (Nat.le_refl _)
    ⟨h.step f (all_mut_arr hj) k, f⟩

/-- `e`'s pointer and length, and the working space's base. -/
def eVal (q : KQ) : Reg → BitVec 64
  | .x0 => q.B
  | .x1 => q.pE
  | .x2 => BitVec.ofNat 64 q.el
  | _ => 0

theorem loadE_eq : seqs (loadE ++ ([.block [sth .x3 kEv]] : List (Prog isa))) =
    .seq (.block [ldh .x1 kE, ldh .x2 kElen, movi .x3 0])
      (.seq (countLoop .x2 [.lsl .x .x3 .x3 8, .ldrb .x4 .x1 0, .add .x .x3 .x3 .x4, .addImm .x .x1 .x1 1])
        (.block [sth .x3 kEv])) := rfl

/-- `e`'s load and its store into `kEv`. -/
theorem loadE_ct0 {F : KIn → State → Prop} :
    RelCT isa (Two (KG F)) (seqs (loadE ++ ([.block [sth .x3 kEv]] : List (Prog isa)))) fun _ _ => True := by
  rw [loadE_eq]
  refine kpin_seq0 [.x0, .x1, .x2] (fun p : KP => eVal p.q) (two_taint [.x0] (pins_kg F) (by taint_decide))
    (fun p s h => ?_) (by taint_decide)
  obtain ⟨I, s₀, he, -, hk, -⟩ := h
  rw [← he]
  have hw := hk.ws
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off I.B (8 * i)) 8 := fun i hi => hw.scr.ld (by omega_using [h256, hi])
  refine WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t => t.gpr .x1 = I.pE ∧ t.gpr .x2 = BitVec.ofNat 64 I.el)
    (by brun [hw.x0, hdr_enc (show kE < 32 by decide), hdr_enc (show kElen < 32 by decide), hl kE (by decide),
      hl kElen (by decide), hk.args.e, hk.args.el]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h1, h2⟩, k⟩ r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (k.gpr .x0 (by decide)).trans hw.x0
  · exact h1
  · exact h2

/-- The three loads. -/
abbrev loadsL : List (Prog isa) :=
  loadA aPa kPp kPl ++ (loadA aQa kQp kPl ++ (loadE ++ ([.block [sth .x3 kEv]] : List (Prog isa))))

theorem loads_ct0 : RelCT isa (Two (KG NF)) (seqs loadsL) fun _ _ => True := by
  have pl8 : ∀ {I : KIn}, KLens I → I.pl ≤ 8 * I.W ∧ 1 ≤ I.pl := fun L => by
    have := L.W; have := L.pl1; have := L.pl8; omega_arith
  refine kg_app0 (G := NF) (by simp [loadA]) (by simp [loadA]) (loadA_ct0 (by decide) (by decide) (by decide)
    KQ.pP KQ.pl (fun _ _ _ h => ⟨h.args.pp, h.args.pl⟩) (by taint_decide) (by taint_decide) (by taint_decide))
    (fun I _ s h L _ => WP.mono (loadA_k h (j := aPa) (by decide) (by decide) (by decide) h.args.pp h.args.pl h.p
      L.pbl (pl8 L).2 (pl8 L).1) fun _ ⟨ht, _⟩ => ⟨ht, trivial⟩) ?_
  refine kg_app0 (G := NF) (by simp [loadA]) (by simp [loadE]) (loadA_ct0 (by decide) (by decide) (by decide)
    KQ.pQ KQ.pl (fun _ _ _ h => ⟨h.args.qp, h.args.pl⟩) (by taint_decide) (by taint_decide) (by taint_decide))
    (fun I _ s h L _ => WP.mono (loadA_k h (j := aQa) (by decide) (by decide) (by decide) h.args.qp h.args.pl h.q
      L.qbl (pl8 L).2 (pl8 L).1) fun _ ⟨ht, _⟩ => ⟨ht, trivial⟩) loadE_ct0

/-! ## The order -/

theorem order_eq : order = ltA aPa aQa ++ ([.block (ws ++ (([mov .x14 .x12] : List Instr) ++
    (base aPa .x16 ++ base aQa .x17))), countLoop .x14 cswapBody] : List (Prog isa)) := by
  simp only [order, List.append_assoc]

theorem order_ct0 : RelCT isa (Two (KG NF)) (seqs order) fun _ _ => True := by
  rw [order_eq]
  exact rs_app (by simp [ltA, cmpA]) (by simp) (ltA_ct (G := NF) (by decide) (by decide)
    (fun _ _ _ _ _ _ _ _ => trivial) (by taint_decide)) (kg_ws0 (by taint_decide))

/-! ## Minus one -/

theorem decTo_eq (o j : Nat) : decTo o j = [zeroA o, copyA o j] ++ (constA 0 ++ (neMask j aC ++ (constA 1 ++
    ([.block (ws ++ (([movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] : List Instr) ++ (base o .x16 ++
      (base aC .x17 ++ base o .x8)))), countLoop .x14 subMBody] : List (Prog isa))))) := by
  simp only [decTo, List.append_assoc]

/-- `decTo o j`, with no postcondition. -/
theorem decTo_ct0 {o j : Nat} (ho : o < 16) (hj : j < 16) (hoj : o ≠ j)
    {h₁ h₂ h₃ h₄ h₅ h₆ h₇ : VG.Taint.Hint VG.AArch64.Taint.T}
    (t₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base o .x8 ++ ([movi .x7 0] : List Instr)))
      zeroAcc) h₁).isSome = true)
    (t₂ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base j .x16 ++ base o .x17)) copyWords)
      h₂).isSome = true)
    (t₃ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base aC .x8 ++ ([movi .x7 0] : List Instr)))
      zeroAcc) h₃).isSome = true)
    (t₄ : (taint.check (Taint.ofRegs [.x0, .x12, .x11])
      (.block (base aC .x16 ++ ([movi .x3 0, st .x3 .x16] : List Instr))) h₄).isSome = true)
    (t₅ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block ([movi .x9 0, mov .x14 .x12] : List Instr))
      (.seq (.block (base j .x16 ++ base aC .x17)) (.seq (countLoop .x14 xorBody) (.block nonzeroMask)))) h₅).isSome =
      true)
    (t₆ : (taint.check (Taint.ofRegs [.x0, .x12, .x11])
      (.block (base aC .x16 ++ ([movi .x3 1, st .x3 .x16] : List Instr))) h₆).isSome = true)
    (t₇ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (([movi .x7 0, mov .x14 .x12,
      .subs .x .x3 .x7 .x7] : List Instr) ++ (base o .x16 ++ (base aC .x17 ++ base o .x8)))) (countLoop .x14 subMBody))
      h₇).isSome = true) :
    RelCT isa (Two (KG NF)) (seqs (decTo o j)) fun _ _ => True := by
  rw [decTo_eq]
  refine rs_app (by simp) (by simp [constA]) (show RelCT isa _ (seqs [zeroA o, copyA o j]) _ from
    RelCT.seq (zeroA_ct ho (stab_nf _ _) t₁) (copyA_ct ho hj hoj (stab_nf _ _) t₂)) ?_
  refine rs_app (by simp [constA]) (by simp [neMask, eqA]) (constA_ct 0 (by decide) (stab_nf _ _) t₃ t₄) ?_
  refine rs_app (by simp [neMask, eqA]) (by simp [constA]) (neMask_ct (G := NF) hj (by decide)
    (fun _ _ _ _ _ _ _ _ => trivial) t₅) ?_
  exact rs_app (by simp [constA]) (by simp) (constA_ct 1 (by decide) (stab_nf _ _) t₃ t₆) (kg_ws0 t₇)

theorem decP_ct0 : RelCT isa (Two (KG NF)) (seqs (decTo aPm aPa)) fun _ _ => True :=
  decTo_ct0 (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)

theorem decQ_ct0 : RelCT isa (Two (KG NF)) (seqs (decTo aQm aQa)) fun _ _ => True :=
  decTo_ct0 (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)

/-! ## The front -/

/-- The front: the loads, the order, `p − 1` and `q − 1`. -/
abbrev frontL : List (Prog isa) :=
  loadA aPa kPp kPl ++ (loadA aQa kQp kPl ++ (loadE ++
    (([.block [sth .x3 kEv]] : List (Prog isa)) ++ (order ++ (decTo aPm aPa ++ decTo aQm aQa)))))

theorem frontL_eq : frontL = loadsL ++ (order ++ (decTo aPm aPa ++ decTo aQm aQa)) := by
  simp only [frontL, loadsL, List.append_assoc]

/-- The front leaks the same in runs with the same public data, and leaves
`PF` (`front_k`). -/
theorem front_ct : RelCT isa (Two (KG NF)) (seqs frontL) (Two (KG PF)) := by
  refine kg_ct ?_ fun I _ s h L _ => WP.mono (front_k h L) fun _ ⟨P, _, t1, t2⟩ =>
    ⟨P.ks, P.vP, P.vQ, P.vPm, P.vQm, P.ev, t1, t2⟩
  rw [frontL_eq]
  refine kg_app0 (G := NF) (by simp [loadA]) (by simp [order, ltA, cmpA]) loads_ct0
    (fun I _ s h L _ => WP.mono (loads_k h L) fun _ ⟨ht, _⟩ => ⟨ht, trivial⟩) ?_
  refine kg_app0 (G := NF) (by simp [order, ltA, cmpA]) (by simp [decTo]) order_ct0
    (fun I _ s h _ _ => WP.mono (order_k h) fun _ ⟨ht, _⟩ => ⟨ht, trivial⟩) ?_
  exact kg_app0 (G := NF) (by simp [decTo]) (by simp [decTo]) decP_ct0
    (fun I _ s h _ _ => WP.mono (decTo_k h (o := aPm) (j := aPa) (by decide) (by decide) (by decide) (by decide)
      (by decide)) fun _ ⟨ht, _⟩ => ⟨ht, trivial⟩) decQ_ct0

/-! ## From the contract -/

/-- Byte lists with the same values. -/
theorem kbytes_eq_of_toNat : ∀ {a b : List Byte}, a.map (·.toNat) = b.map (·.toNat) → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: a, y :: b, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, kbytes_eq_of_toNat h.2]

/-- The public data of a state. -/
def kpubOf (s : State) : KP := ⟨(keyIn s).pub, (keyIn s).st⟩

/-- Runs that the contract relates (`keyPub`) have the same public data. -/
theorem kpubOf_eq {s₁ s₂ : State} (h₁ : keyPre s₁) (h₂ : keyPre s₂) (hp : keyPub s₁ s₂) :
    KRel (kpubOf s₁) s₂ := by
  obtain ⟨hr, -, ha, hl⟩ := hp
  simp only [keyLeak] at hl
  have hlen : ((Spec.Rsa.bytesAt s₁.mem (arg s₁ 6) (arg s₁ 7).toNat).map (·.toNat)).length =
      ((Spec.Rsa.bytesAt s₂.mem (arg s₂ 6) (arg s₂ 7).toNat).map (·.toNat)).length := by
    simp only [List.length_map, bytesAt_length, ha 7 (by decide)]
  obtain ⟨he, hs⟩ := List.append_inj hl hlen
  simp only [List.cons.injEq, and_true] at hs
  refine ⟨h₂, ?_, hs.symm⟩
  have hwr : s₂.wr = s₁.wr := by
    have w₁ := h₁.2.2.1
    have w₂ := h₂.2.2.1
    rw [w₁, w₂]
    simp only [hr .x0 (by decide), hr .x1 (by decide), hr .x2 (by decide), hr .x3 (by decide), hr .x4 (by decide),
      hr .x5 (by decide), hr .x6 (by decide), hr .x7 (by decide), ha 0 (by decide), ha 1 (by decide),
      ha 2 (by decide), ha 3 (by decide), ha 4 (by decide), ha 5 (by decide), ha 8 (by decide), ha 9 (by decide)]
  simp only [kpubOf, keyIn, KIn.pub, KQ.mk.injEq]
  exact ⟨(ha 8 (by decide)).symm, by rw [ha 9 (by decide)], by rw [hr .x5 (by decide)], (hr .x0 (by decide)).symm,
    (hr .x2 (by decide)).symm, (hr .x4 (by decide)).symm, (hr .x6 (by decide)).symm, (ha 0 (by decide)).symm,
    (ha 2 (by decide)).symm, (ha 4 (by decide)).symm, (ha 6 (by decide)).symm, by rw [ha 7 (by decide)],
    (kbytes_eq_of_toNat he).symm, hwr⟩

/-- The contract's constant time, from that of the code in runs with the same
public data. -/
theorem keyCT_of {c : Prog isa} (h : RelCT isa (Two KRel) c fun _ _ => True) :
    ConstantTime isa keyA.pre keyA.pub c :=
  RelCT.constantTime (h.mono (fun _ _ ⟨h₁, h₂, hp⟩ => ⟨kpubOf _, ⟨h₁, rfl, rfl⟩, kpubOf_eq h₁ h₂ hp, hp.2.1⟩)
    fun _ _ h => h)

end VG.Proof.RsaKeyGen.AArch64.Key

end

end

/-! ### `RsaKeyGen.AArch64.Key.Code`, which only this module used -/

section

/-! ### `RsaKeyGen.AArch64.Key.Res`, which only this module used -/

section

/-! ### `RsaKeyGen.AArch64.Key.Tail`, which only this module used -/

section

/-!
# An RSA key from its primes on AArch64: the key

`keyPart`, once `d` is not too small or does not exist: `qInv`, `dP`, `dQ`,
`n`, the final mask, the stores and the status (`keyPart_k`); and the zeros
and the status 2 otherwise (`zerosPart_k`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-- The stores. -/
def storeL (I : KIn) : List St :=
  [⟨aQt, kNo, kNl, I.pN, 2 * I.pl⟩, ⟨aDd, kDo, kNl, I.pD, 2 * I.pl⟩, ⟨aPa, kPp, kPl, I.pP, I.pl⟩,
    ⟨aQa, kQp, kPl, I.pQ, I.pl⟩, ⟨aX₁, kDp, kPl, I.pDp, I.pl⟩, ⟨aV, kDq, kPl, I.pDq, I.pl⟩,
    ⟨aX₂, kQi, kPl, I.pQi, I.pl⟩]

theorem storeL_outs (I : KIn) : (storeL I).map (fun e => (e.out, e.len)) = outsL I := rfl

theorem storeL_pairwise {I : KIn} (O : KOuts I) :
    (storeL I).Pairwise fun a b => Apart a.out a.len b.out b.len := by
  have := O.apart
  rw [← storeL_outs, List.pairwise_map] at this
  exact this

theorem st_ok {I : KIn} {s₀ t : State} (h : KS I s₀ t) (O : KOuts I) {j p l : Nat} {out : Addr}
    {len : Nat} (hj : j < 16) (hp : p < 32) (hl : l < 32) (hpv : word t.mem I.B (8 * p) = out)
    (hlv : word t.mem I.B (8 * l) = BitVec.ofNat 64 len) (hl1 : 1 ≤ len) (hlw : len ≤ 8 * I.W)
    (ho : (out, len) ∈ outsL I) : (⟨j, p, l, out, len⟩ : St).Ok t I.B I.Z I.W :=
  ⟨hj, hp, hl, hpv, hlv, hl1, hlw, fun i hi => by rw [h.wr]; exact O.wr _ ho i hi, O.sep _ ho⟩

theorem storeL_ok {I : KIn} {s₀ t : State} (h : KS I s₀ t) (L : KLens I) (O : KOuts I) :
    ∀ e ∈ storeL I, e.Ok t I.B I.Z I.W := by
  have hW := L.W
  have hpl := L.pl1
  have h8 := L.pl8
  intro e he
  simp only [storeL, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.no h.args.nl (by omega_using [hpl]) (by omega_using [hW, h8]) (by simp [outsL])
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.dd h.args.nl (by omega_using [hpl]) (by omega_using [hW, h8]) (by simp [outsL])
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.pp h.args.pl (by omega_using [hpl]) (by omega_using [hW, h8]) (by simp [outsL])
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.qp h.args.pl (by omega_using [hpl]) (by omega_using [hW, h8]) (by simp [outsL])
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.dp h.args.pl (by omega_using [hpl]) (by omega_using [hW, h8]) (by simp [outsL])
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.dq h.args.pl (by omega_using [hpl]) (by omega_using [hW, h8]) (by simp [outsL])
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.qi h.args.pl (by omega_using [hpl]) (by omega_using [hW, h8]) (by simp [outsL])

theorem outputs_eq (I : KIn) : outputs = storesK (storeL I) ++ ([.block retOk] : List (Prog isa)) := rfl

theorem zeros_eq (I : KIn) (st : Nat) :
    zeros st = seqs (zerosK (storeL I) ++ ([.block [movi .x0 st]] : List (Prog isa))) := rfl

theorem keyPart_eq (I : KIn) : keyPart = seqs (qinvPart ++ (crtPart ++ (nPart ++
    (([.block finalMask] : List (Prog isa)) ++ (storesK (storeL I) ++ ([.block retOk] : List (Prog isa))))))) := by
  rw [keyPart, ← outputs_eq I]; simp only [List.append_assoc]

/-- A number below `2^(64 v)` read from `v ≤ W` words. -/
theorem wv_of_av {I : KIn} {m : Mem} {j v x : Nat} (hv : v ≤ I.W) (h : av I m j = x) (hx : x < 2 ^ (64 * v)) :
    wv m I.B (slot I.W j) v = x := by
  rw [← h]; exact wv_low_of_lt hv (by rw [show wv m I.B (slot I.W j) I.W = av I m j from rfl, h]; exact hx)

/-- Two states that keep the registers of one before both. -/
theorem keep_of_common {rs : List Reg} {s₀ s t : State} (a : Keep rs s₀ s) (b : Keep rs s₀ t) : Keep rs s t :=
  ⟨fun r hr => (b.gpr r hr).trans (a.gpr r hr).symm, b.rd.trans a.rd.symm, b.wr.trans a.wr.symm,
    b.sp.trans a.sp.symm, fun r hr => (b.vcs r hr).trans (a.vcs r hr).symm⟩

/-- What `keyPart` leaves, from `KFront` and `kOk` the mask of `ok`. -/
def TailPost (I : KIn) (s t : State) (ok : Bool) : Prop :=
  ∃ x : Nat, ((qMod I.P : Nat) : Int) ∣ (x : Int) * I.Q - Nat.gcd I.Q (qMod I.P) ∧ x < qMod I.P ∧
    (let c := finalOk I.W (I.P * I.Q) I.P I.Q I.E (decide (Nat.gcd I.Q (qMod I.P) = 1) && ok)
     t.gpr .x0 = BitVec.ofNat 64 c.toNat ∧
     Spec.Rsa.bytesAt t.mem I.pN (2 * I.pl) = Spec.Rsa.i2osp (if c then I.P * I.Q else 0) (2 * I.pl) ∧
     Spec.Rsa.bytesAt t.mem I.pD (2 * I.pl) = Spec.Rsa.i2osp (if c then av I s.mem aDd else 0) (2 * I.pl) ∧
     Spec.Rsa.bytesAt t.mem I.pP I.pl = Spec.Rsa.i2osp (if c then I.P else 0) I.pl ∧
     Spec.Rsa.bytesAt t.mem I.pQ I.pl = Spec.Rsa.i2osp (if c then I.Q else 0) I.pl ∧
     Spec.Rsa.bytesAt t.mem I.pDp I.pl = Spec.Rsa.i2osp (if c then av I s.mem aDd % dv (I.P - 1) else 0) I.pl ∧
     Spec.Rsa.bytesAt t.mem I.pDq I.pl = Spec.Rsa.i2osp (if c then av I s.mem aDd % dv (I.Q - 1) else 0) I.pl ∧
     Spec.Rsa.bytesAt t.mem I.pQi I.pl = Spec.Rsa.i2osp (if c then x else 0) I.pl) ∧
    (∀ y, I.Z ≤ ofs I.B y → (∀ o ∈ outsL I, ∀ i < o.2, y ≠ o.1 + BitVec.ofNat 64 i) → t.mem y = s.mem y) ∧
    Keep kRegs s t

/-- `keyPart`. -/
theorem keyPart_k [VG.Proof.Rsa.AArch64.InvLaw] {I : KIn} {s₀ s : State} (h : KFront I s₀ s) (L : KLens I) (O : KOuts I) {ok : Bool}
    (hok : word s.mem I.B (8 * kOk) = mask ok) :
    WP isa keyPart s (fun t => TailPost I s t ok) := by
  have hk := h.ks
  have hZ := hk.hZ
  have hW := L.W
  have hPw := L.P_lt
  have hQw := L.Q_lt
  rw [keyPart_eq I]
  -- `qInv`.
  refine wp_seqs_append (by simp [qinvPart]) (by simp [crtPart, divisorOf]) (WP.mono (qinvPart_k hk L h.vP h.vQ hPw hQw hok)
    fun s₁ ⟨h₁, f₁, ok₁, hdv₁, hx₁⟩ => ?_)
  generalize hx : av I s₁.mem aX₂ = x at hdv₁ hx₁
  obtain hokQ : csQ.all Rc.ok = true := by decide
  -- `dP`, `dQ`.
  refine wp_seqs_append (by simp [crtPart, divisorOf]) (by simp [nPart]) (WP.mono (crtPart_k h₁
    (d := av I s.mem aDd) (a := I.P - 1) (b := I.Q - 1) (by rw [f₁.av hokQ (by decide) (by decide) hZ])
    (by rw [f₁.av hokQ (by decide) (by decide) hZ, h.vPm]) (by rw [f₁.av hokQ (by decide) (by decide) hZ, h.vQm]))
    fun s₂ ⟨h₂, f₂, dP₂, dQ₂⟩ => ?_)
  obtain hokC : csC.all Rc.ok = true := by decide
  -- `n`.
  refine wp_seqs_append (by simp [nPart, mulTo]) (by simp) (WP.mono (nPart_k h₂ hW
    (by rw [f₂.av hokC (by decide) (by decide) hZ, f₁.av hokQ (by decide) (by decide) hZ]; exact h.vP)
    (by rw [f₂.av hokC (by decide) (by decide) hZ, f₁.av hokQ (by decide) (by decide) hZ]; exact h.vQ) hPw hQw)
    fun s₃ ⟨h₃, f₃, n₃⟩ => ?_)
  obtain hn : I.P * I.Q < 2 ^ (64 * I.W) := by
    rw [hW, show 64 * (2 * (I.pl / 8)) = 64 * (I.pl / 8) + 64 * (I.pl / 8) by omega_using [], Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le hPw (by omega_using [hQw]) (Nat.two_pow_pos _)
  obtain hokN : [Rc.arr aQt].all Rc.ok = true := by decide
  obtain vN₃ : av I s₃.mem aQt = I.P * I.Q := av_of_full n₃ hn
  obtain vP₃ : av I s₃.mem aPa = I.P := by
    rw [f₃.av hokN (by decide) (by decide) hZ, f₂.av hokC (by decide) (by decide) hZ,
      f₁.av hokQ (by decide) (by decide) hZ, h.vP]
  obtain vQ₃ : av I s₃.mem aQa = I.Q := by
    rw [f₃.av hokN (by decide) (by decide) hZ, f₂.av hokC (by decide) (by decide) hZ,
      f₁.av hokQ (by decide) (by decide) hZ, h.vQ]
  obtain ev₃ : word s₃.mem I.B (8 * kEv) = BitVec.ofNat 64 I.E := by
    rw [f₃.word hokN (by decide) (by decide), f₂.word hokC (by decide) (by decide),
      f₁.word hokQ (by decide) (by decide), h.ev]
  obtain ok₃ : word s₃.mem I.B (8 * kOk) = mask (decide (Nat.gcd I.Q (qMod I.P) = 1) && ok) := by
    rw [f₃.word hokN (by decide) (by decide), f₂.word hokC (by decide) (by decide), ok₁]
  -- The final mask.
  refine wp_seqs_append (by simp) (by simp [storesK, storeL, storeA]) ?_
  simp only [seqs]
  refine WP.mono (finalMask_k h₃ vN₃ vP₃ vQ₃ L.E_lt ev₃ ok₃) fun s₄ ⟨h₄, f₄, ok₄⟩ => ?_
  generalize hc : finalOk I.W (I.P * I.Q) I.P I.Q I.E (decide (Nat.gcd I.Q (qMod I.P) = 1) && ok) = cv at ok₄
  obtain hokO : [Rc.hdr kOk].all Rc.ok = true := by decide
  obtain v4 : ∀ j, j < 16 → Rc.arr j ∉ [Rc.arr aQt] → Rc.arr j ∉ csC → Rc.arr j ∉ csQ →
      av I s₄.mem j = av I s.mem j := fun j hj h1 h2 h3 => by
    rw [f₄.av hokO hj (by simp) hZ, f₃.av hokN hj h1 hZ, f₂.av hokC hj h2 hZ, f₁.av hokQ hj h3 hZ]
  -- The stores and the status.
  refine stores_ok (Q := fun t => TailPost I s t ok) (storeL I) _ s₄ (by simp) h₄.ws ok₄ (storeL_ok h₄ L O)
    (storeL_pairwise O) fun t ht ft bt xt kt => ?_
  simp only [seqs]
  refine WP.mono (keyExit_ok ht (c := cv) (by rw [frm_word ft ht.h256 (by decide)]; exact ok₄))
    fun u ⟨⟨hax, hmu⟩, ku⟩ => ?_
  obtain b := fun e he => (bt e he)
  simp only [storeL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at b
  obtain ⟨bN, bD, bP, bQ, bDp, bDq, bQi⟩ := b
  obtain hlen : (I.pl + 7) / 8 = I.pl / 8 := by have := L.pl8; omega_using [this]
  obtain hlen2 : (2 * I.pl + 7) / 8 = I.W := by have := L.pl8; simp only [KIn.W]; omega_using [this]
  obtain hv : I.pl / 8 ≤ I.W := by omega_using [hlen2]
  obtain hdvw : ∀ a, a ≤ I.P → dv a < 2 ^ (64 * (I.pl / 8)) := fun a ha => by
    unfold dv; split
    · exact Nat.one_lt_two_pow (by have := L.pl1; omega_using [this])
    · omega_using [hPw, ha]
  obtain hdvwq : ∀ a, a ≤ I.Q → dv a < 2 ^ (64 * (I.pl / 8)) := fun a ha => by
    unfold dv; split
    · exact Nat.one_lt_two_pow (by have := L.pl1; omega_using [this])
    · omega_using [hQw, ha]
  obtain hdv0 : ∀ a, 0 < dv a := fun a => by unfold dv; split <;> omega_arith
  obtain hqm : qMod I.P < 2 ^ (64 * (I.pl / 8)) := by
    unfold qMod; split
    · exact hPw
    · exact Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) (show 2 ≤ 64 * (I.pl / 8) by
        have := L.pl1; omega_using [this]))
  obtain iv : ∀ {len v : Nat} {o : Addr} {w' : Nat},
      (List.range len).map (fun i => t.mem (o + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if cv then w' else 0) len → w' = v →
      Spec.Rsa.bytesAt u.mem o len = Spec.Rsa.i2osp (if cv = true then v else 0) len := fun hb hw => by
    simp only [Spec.Rsa.bytesAt]; rw [hmu, hb, hw]
  refine ⟨x, hdv₁, hx₁, ?_, fun y hy hny => ?_, ?_⟩
  · dsimp only
    rw [hc]
    refine ⟨hax, iv bN ?_, iv bD ?_, iv bP ?_, iv bQ ?_, iv bDp ?_, iv bDq ?_, iv bQi ?_⟩
    · rw [hlen2]; show av I s₄.mem aQt = _; rw [f₄.av hokO (by decide) (by decide) hZ, vN₃]
    · rw [hlen2]; exact v4 aDd (by decide) (by decide) (by decide) (by decide)
    · rw [hlen]; exact wv_of_av hv (v4 aPa (by decide) (by decide) (by decide) (by decide) |>.trans h.vP) hPw
    · rw [hlen]; exact wv_of_av hv (v4 aQa (by decide) (by decide) (by decide) (by decide) |>.trans h.vQ) hQw
    · rw [hlen]
      refine wv_of_av hv (by rw [f₄.av hokO (by decide) (by decide) hZ, f₃.av hokN (by decide) (by decide) hZ, dP₂])
        (Nat.lt_of_lt_of_le (Nat.mod_lt _ (hdv0 _)) (Nat.le_of_lt (hdvw _ (by omega_using []))))
    · rw [hlen]
      refine wv_of_av hv (by rw [f₄.av hokO (by decide) (by decide) hZ, f₃.av hokN (by decide) (by decide) hZ, dQ₂])
        (Nat.lt_of_lt_of_le (Nat.mod_lt _ (hdv0 _)) (Nat.le_of_lt (hdvwq _ (by omega_using []))))
    · rw [hlen]
      refine wv_of_av hv (by rw [f₄.av hokO (by decide) (by decide) hZ, f₃.av hokN (by decide) (by decide) hZ,
        f₂.av hokC (by decide) (by decide) hZ, hx]) (by omega_using [hx₁, hqm])
  · have hy' : ∀ e ∈ storeL I, ∀ i < e.len, y ≠ e.out + BitVec.ofNat 64 i := fun e he i hi =>
      hny (e.out, e.len) (by rw [← storeL_outs]; exact List.mem_map_of_mem he) i hi
    rw [hmu, xt y hy', h₄.inScr y hy, hk.inScr y hy]
  · exact (((keep_of_common hk.keep h₄.keep).trans kt).trans ku).mono (by decide)

/-- What `zeros 2` leaves. -/
def ZerosPost (I : KIn) (s t : State) : Prop :=
  t.gpr .x0 = BitVec.ofNat 64 2 ∧ (∀ o ∈ outsL I, Spec.Rsa.bytesAt t.mem o.1 o.2 = List.replicate o.2 0) ∧
    (∀ y, I.Z ≤ ofs I.B y → (∀ o ∈ outsL I, ∀ i < o.2, y ≠ o.1 + BitVec.ofNat 64 i) → t.mem y = s.mem y) ∧
    Keep kRegs s t

/-- `zeros 2`: zeros to the outputs, and the status 2. -/
theorem zerosPart_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) (L : KLens I) (O : KOuts I) :
    WP isa (zeros 2) s (ZerosPost I s) := by
  rw [zeros_eq I]
  refine zeros_ok (storeL I) _ s (by simp) h.ws (storeL_ok h L O) (storeL_pairwise O)
    fun t ht ft zt xt kt => ?_
  simp only [seqs]
  refine WP.mono (WP.keep [.x0] (Q := fun u => u.gpr .x0 = BitVec.ofNat 64 2 ∧ u.mem = t.mem) (by brun)
    (by decide) (by decide) (by decide +kernel)) fun u ⟨⟨hax, hmu⟩, ku⟩ =>
      ⟨hax, fun o ho => ?_, fun y hy hny => ?_, (kt.trans ku).mono (by decide)⟩
  · rw [← storeL_outs] at ho
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho
    refine List.eq_replicate_iff.mpr ⟨by simp [Spec.Rsa.bytesAt], fun b hb => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    rw [hmu]; exact zt e he i (List.mem_range.mp hi)
  · have hy' : ∀ e ∈ storeL I, ∀ i < e.len, y ≠ e.out + BitVec.ofNat 64 i := fun e he i hi =>
      hny (e.out, e.len) (by rw [← storeL_outs]; exact List.mem_map_of_mem he) i hi
    rw [hmu, xt y hy']

end VG.Proof.RsaKeyGen.AArch64.Key

end

end


/-!
# An RSA key from its primes on AArch64: the results, against `keyOp`

What the zeros (`outsRes_zeros`) and `keyPart` (`outsRes_tail`) leave is
`keyOp`'s status and outputs.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)
open VG.Spec.RsaKeyGen (keyFromPrimes)
open VG.Proof.RsaKeyGen (keyOp keyStatus)

/-- The status and the outputs `keyOp` gives. -/
def OutsRes (I : KIn) (m : Mem) (x0 : BitVec 64) : Prop :=
  (x0.setWidth 32).toNat = Proof.RsaKeyGen.keyStatus (Proof.RsaKeyGen.keyOp I.pl I.eb I.pb I.qb) ∧
    match Proof.RsaKeyGen.keyOp I.pl I.eb I.pb I.qb with
    | .inl (.ok ys) => (outsL I).map (fun o => Spec.Rsa.bytesAt m o.1 o.2) = ys
    | _ => ∀ o ∈ outsL I, Spec.Rsa.bytesAt m o.1 o.2 = List.replicate o.2 0

theorem keyOp_inr_k {pl : Nat} {eB pB qB : List Byte}
    (h : keyFromPrimes (16 * pl) (Spec.Rsa.os2ip eB) (Spec.Rsa.os2ip pB) (Spec.Rsa.os2ip qB) = .inr ()) :
    keyOp pl eB pB qB = .inr () := by
  unfold keyOp; rw [h]

theorem keyOp_error_k {pl : Nat} {eB pB qB : List Byte} {f : Spec.RsaKeyGen.Failure}
    (h : keyFromPrimes (16 * pl) (Spec.Rsa.os2ip eB) (Spec.Rsa.os2ip pB) (Spec.Rsa.os2ip qB) =
      .inl (.error f)) :
    keyOp pl eB pB qB = .inl (.error f) := by
  unfold keyOp; rw [h]

theorem keyOp_ok_k {pl : Nat} {eB pB qB : List Byte} {k : Spec.RsaKeyGen.Key}
    (h : keyFromPrimes (16 * pl) (Spec.Rsa.os2ip eB) (Spec.Rsa.os2ip pB) (Spec.Rsa.os2ip qB) =
      .inl (.ok k)) :
    keyOp pl eB pB qB = .inl (.ok [Spec.Rsa.i2osp k.n (2 * pl), Spec.Rsa.i2osp k.d (2 * pl),
      Spec.Rsa.i2osp k.p pl, Spec.Rsa.i2osp k.q pl, Spec.Rsa.i2osp k.dP pl,
      Spec.Rsa.i2osp k.dQ pl, Spec.Rsa.i2osp k.qInv pl]) := by
  unfold keyOp; rw [h]

theorem setWidth32_k (n : Nat) (h : n < 2 ^ 32) : ((BitVec.ofNat 64 n).setWidth 32).toNat = n := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega_using [h]),
    Nat.mod_eq_of_lt h]

/-- The zeros and the status 2, for `d ≤ 2^(8 pl)`. -/
theorem outsRes_zeros {I : KIn} {s t : State} {d : Nat}
    (hd : Spec.Rsa.inverse I.E I.L = some d) (hsm : d ≤ 2 ^ (8 * I.pl)) (Z : ZerosPost I s t) :
    OutsRes I t.mem (t.gpr .x0) := by
  obtain hr : keyFromPrimes (16 * I.pl) I.E I.P₀ I.Q₀ = .inr () := by
    unfold keyFromPrimes
    obtain hswap : (if I.P₀ < I.Q₀ then (I.Q₀, I.P₀) else (I.P₀, I.Q₀)) = (I.P, I.Q) := by
      by_cases h : I.P₀ < I.Q₀ <;> simp [KIn.P, KIn.Q, h]
    rw [hswap]
    dsimp only
    rw [show Nat.lcm (I.P - 1) (I.Q - 1) = I.L from rfl, hd, show 16 * I.pl / 2 = 8 * I.pl by omega_using []]
    dsimp only
    rw [ite_eq_left hsm]
  rw [OutsRes, keyOp_inr_k hr, Z.1]
  exact ⟨by decide, Z.2.1⟩

theorem i2osp_zero_k (k : Nat) : Spec.Rsa.i2osp 0 k = List.replicate k 0 := by
  simp [Spec.Rsa.i2osp, List.map_const']

/-- The outputs and the status of `keyPart`, for `d > 2^(8 pl)` or no `d`. -/
theorem outsRes_tail {I : KIn} {s t : State} (L : KLens I) {ok : Bool}
    (hok : (∃ d, Spec.Rsa.inverse I.E I.L = some d) ↔ ok = true)
    (hdd : ∀ d, Spec.Rsa.inverse I.E I.L = some d → av I s.mem aDd = d)
    (hb : (decide (av I s.mem aDd ≤ 2 ^ (8 * I.pl)) && ok) = false) (T : TailPost I s t ok) :
    OutsRes I t.mem (t.gpr .x0) := by
  obtain ⟨x, hx, hxl, ⟨hax, hN, hD, hP, hQ, hDp, hDq, hQi⟩, -⟩ := T
  obtain hk := keyFromPrimes_code (x := x) L.pl1 L.pl2 (lt_of_os2ip_len L.pbl) (lt_of_os2ip_len L.qbl) L.E_lt hx hxl
  obtain hW : 64 * I.W - 1 = 16 * I.pl - 1 := by rw [L.W]; have := L.pl8; omega_using [this]
  simp only [finalOk, hW] at hax hN hD hP hQ hDp hDq hQi
  obtain hstat : ∀ c : Bool, ((BitVec.ofNat 64 c.toNat).setWidth 32).toNat = c.toNat := fun c =>
    setWidth32_k _ (by cases c <;> decide)
  rcases hi : Spec.Rsa.inverse I.E I.L with _ | d
  · have hok' : ok = false := by
      cases ok
      · rfl
      · obtain ⟨d, hd⟩ := hok.mpr rfl; rw [hi] at hd; cases hd
    subst hok'
    simp only [Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, i2osp_zero_k] at hax hN hD hP
    simp only [Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, i2osp_zero_k] at hQ hDp hDq hQi
    simp only [KIn.L] at hi hk
    rw [hi] at hk
    rw [OutsRes, keyOp_error_k hk, hax, hstat]
    refine ⟨rfl, ?_⟩
    simp only [outsL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hN, hD, hP, hQ, hDp, hDq, hQi⟩
  · have hok' : ok = true := hok.mp ⟨d, hi⟩
    subst hok'
    obtain hd := hdd d hi
    rw [hd, Bool.and_true, decide_eq_false_iff_not] at hb
    obtain hd2 : 2 ≤ d := by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 1 ≤ 8 * I.pl by have := L.pl1; omega_using [this])
      omega_using [hb, this]
    obtain hqp : I.Q ≤ I.P := by simp only [KIn.P, KIn.Q]; split <;> omega_arith
    obtain ⟨hP3, hQ2, -⟩ := primes_of_inverse hqp hi hd2
    obtain hdvP : dv (I.P - 1) = I.P - 1 := by simp only [dv]; rw [ite_eq_right_iff]; omega_using [hP3]
    obtain hdvQ : dv (I.Q - 1) = I.Q - 1 := by simp only [dv]; rw [ite_eq_right_iff]; omega_using [hQ2]
    simp only [Bool.and_true, KIn.L] at hax hN hD hP hQ hDp hDq hQi hi hk
    rw [hi] at hk
    simp only [ite_eq_right_iff.mpr (fun h => absurd h hb)] at hk
    simp only [hd, hdvP, hdvQ] at hD hDp hDq
    generalize hc : (decide (2 ^ (16 * I.pl - 1) ≤ I.P * I.Q) && decide (Nat.gcd I.Q (qMod I.P) = 1) &&
      decide (I.P % 2 = 1) && decide (I.Q % 2 = 1) && Spec.Rsa.exponentValid I.E) = c
      at hax hN hD hP hQ hDp hDq hQi
    have hc' : (decide (2 ^ (16 * I.pl - 1) ≤ I.P * I.Q) && decide (Nat.gcd I.Q (qModP I.P) = 1) &&
      decide (I.P % 2 = 1) && decide (I.Q % 2 = 1) && Spec.Rsa.exponentValid I.E) = c := hc
    rw [hc'] at hk
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte] at hk
      rw [OutsRes, keyOp_error_k hk, hax, hstat]
      refine ⟨rfl, ?_⟩
      simp only [outsL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      simp only [Bool.false_eq_true, ↓reduceIte, i2osp_zero_k] at hN hD hP hQ hDp hDq hQi
      exact ⟨hN, hD, hP, hQ, hDp, hDq, hQi⟩
    · simp only [↓reduceIte] at hk hN hD hP hQ hDp hDq hQi
      rw [OutsRes, keyOp_ok_k hk, hax, hstat]
      refine ⟨rfl, ?_⟩
      simp only [outsL, List.map_cons, List.map_nil, hN, hD, hP, hQ, hDp, hDq, hQi]

end VG.Proof.RsaKeyGen.AArch64.Key

end

end

/-! ### `RsaKeyGen.AArch64.Key.Main`, which only this module used -/

section

/-!
# An RSA key from its primes on AArch64: from the primes to `smallMask`

`front2_k`: after `p − 1` and `q − 1` (`KPrimes`), `L = lcm(p − 1, q − 1)`,
`d` and `x15` the mask of `d` too small (`KFront`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-- From `KPrimes` to `KFront`: `lcmPart`, `dPart` and `smallMask`. -/
theorem front2_k [VG.Proof.Rsa.AArch64.InvLaw] {I : KIn} {s₀ s : State} (h : KPrimes I s₀ s) (L : KLens I) :
    WP isa (seqs (lcmPart ++ ([dPart] ++ smallMask))) s (KFront I s₀) := by
  have hk := h.ks
  have hZ := hk.hZ
  have hW := L.W
  obtain hw8 : 8 * I.pl = 64 * (I.pl / 8) := by have := L.pl8; omega_using [this]
  -- `L`.
  refine wp_seqs_append (by simp [lcmPart, phi, mulTo]) (by simp) (WP.mono (lcm_k hk hW h.vPm h.vQm
    (Nat.lt_of_le_of_lt (Nat.sub_le _ _) L.P_lt) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) L.Q_lt))
    fun s₅ ⟨h₅, f₅, vL₅⟩ => ?_)
  obtain hokL : csL.all Rc.ok = true := by decide
  obtain ev₅ : word s₅.mem I.B (8 * kEv) = BitVec.ofNat 64 I.E := by
    rw [f₅.word hokL (by decide) (by decide), h.ev]
  -- `d`.
  refine wp_seqs_append (a := [dPart]) (by simp) (by simp [smallMask, constA]) ?_
  refine WP.mono (dPart_k h₅ L.E_lt ev₅ vL₅ L.L_lt) fun s₆ ⟨h₆, f₆, d₆⟩ => ?_
  obtain ⟨ok, ok₆, iff₆, dd₆⟩ := d₆
  -- `x15`.
  refine WP.mono (smallMask_k h₆ hW ok₆) fun t ⟨ht, f₇, x15₇⟩ => ?_
  obtain hokD : csD.all Rc.ok = true := by decide
  obtain hok7 : [Rc.arr aC].all Rc.ok = true := by decide
  obtain pres : ∀ j, j < 16 → Rc.arr j ∉ csD → Rc.arr j ∉ [Rc.arr aC] → Rc.arr j ∉ csL →
      av I t.mem j = av I s.mem j := fun j hj h1 h2 h3 => by
    rw [f₇.av hok7 hj h2 hZ, f₆.av hokD hj h1 hZ, f₅.av hokL hj h3 hZ]
  obtain okt : word t.mem I.B (8 * kOk) = mask ok := by rw [f₇.word hok7 (by decide) (by decide), ok₆]
  obtain hD : av I t.mem aDd = av I s₆.mem aDd := f₇.av hok7 (by decide) (by decide) hZ
  refine ⟨ht, ?_, ?_, ?_, ?_, ?_, ⟨ok, okt, iff₆, fun d hd => by rw [hD]; exact dd₆ d hd⟩,
    ⟨ok, okt, iff₆, by rw [x15₇, hD, hw8]⟩⟩
  · rw [pres aPa (by decide) (by decide) (by decide) (by decide), h.vP]
  · rw [pres aQa (by decide) (by decide) (by decide) (by decide), h.vQ]
  · rw [pres aPm (by decide) (by decide) (by decide) (by decide), h.vPm]
  · rw [pres aQm (by decide) (by decide) (by decide) (by decide), h.vQm]
  · rw [f₇.word hok7 (by decide) (by decide), f₆.word hokD (by decide) (by decide), ev₅]

end VG.Proof.RsaKeyGen.AArch64.Key

end

end


/-!
# An RSA key from its primes on AArch64: correctness

`code`, from a state `keyA` allows, ends as `keyOp` (`keyCode_wp`,
`keyCode_correct`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

theorem code_eq : code = seqs (([.block (entry ++ VG.Impl.Rsa.AArch64.Keys.head)] : List (Prog isa)) ++
    ((loadA aPa kPp kPl ++ (loadA aQa kQp kPl ++ (loadE ++ (([.block [sth .x3 kEv]] : List (Prog isa)) ++
      (order ++ (decTo aPm aPa ++ decTo aQm aQa)))))) ++
    ((lcmPart ++ ([dPart] ++ smallMask)) ++ ([.ite (.nonzero .x .x15) (zeros 2) keyPart] : List (Prog isa))))) := by
  simp only [code, List.append_assoc]

/-- The postcondition, from the results against `keyOp`. -/
theorem keyPost_of {s t : State} (c : KCtx s) (R : OutsRes (keyIn s) t.mem (t.gpr .x0)) : keyPost s t := by
  obtain ho : keyOuts s = outsL (keyIn s) := by simp only [keyOuts, outsL, keyIn, c.x1]
  unfold keyPost keyRes
  rw [ho]
  exact R

theorem mask_bne_k (b : Bool) : (mask b != 0) = b := by cases b <;> decide

/-- `code` computes `keyOp`. -/
theorem keyCode_wp [VG.Proof.Rsa.AArch64.InvLaw] (s : State) (h : keyPre s) : WP isa code s fun t => abiPreserved s t ∧ keyPost s t := by
  obtain c := keyCtx_of h
  rw [code_eq]
  refine wp_seqs_append (by simp) (by simp [loadA]) (WP.mono (keyStart_k c) fun t₁ k₁ => ?_)
  refine wp_seqs_append (by simp [loadA]) (by simp [lcmPart, phi, mulTo])
    (WP.mono (front_k k₁ c.L) fun t₂ P => ?_)
  refine wp_seqs_append (by simp [lcmPart, phi, mulTo]) (by simp) (WP.mono (front2_k P.1 c.L) fun t₃ F => ?_)
  obtain ⟨ok, hok, hiff, hx15⟩ := F.x15
  obtain ⟨ok', hok', -, hdd⟩ := F.d
  obtain hoo : ok' = ok := by
    rw [hok] at hok'
    cases ok <;> cases ok' <;> first | rfl | exact absurd hok' (by decide)
  subst hoo
  refine WP.ite (decide (av (keyIn s) t₃.mem aDd ≤ 2 ^ (8 * (keyIn s).pl)) && ok')
    (by rw [VG.Proof.MlKem.AArch64.eval_nonzero, hx15, mask_bne_k]) (fun hb => ?_) (fun hb => ?_)
  · -- `d ≤ 2^(8 pl)`: zeros, the status 2.
    rw [Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨d, hd⟩ := hiff.mpr hb.2
    obtain hsm := hdd d hd ▸ hb.1
    exact WP.mono (zerosPart_k F.ks c.L c.O) fun t Z =>
      ⟨abiPreserved_of_keep ((F.ks.keep.trans Z.2.2.2).mono (by decide)), keyPost_of c (outsRes_zeros hd hsm Z)⟩
  · refine WP.mono (keyPart_k F c.L c.O hok) fun t T => ?_
    obtain R := outsRes_tail c.L hiff hdd hb T
    obtain ⟨_, _, _, _, _, kt⟩ := T
    exact ⟨abiPreserved_of_keep ((F.ks.keep.trans kt).mono (by decide)), keyPost_of c R⟩

/-- `vg_rsa_keygen_key`. -/
theorem keyCode_correct [VG.Proof.Rsa.AArch64.InvLaw] (s : State) (h : keyA.pre s) :
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ keyA.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := keyCode_wp s h
  exact ⟨t, s', he, hg, hp⟩

end VG.Proof.RsaKeyGen.AArch64.Key

end

end

/-! ### `RsaKeyGen.AArch64.Key.CTCode`, which only this module used -/

section

/-!
# `vg_rsa_keygen_key` on AArch64: constant time

The pieces leak the same in runs with the same public data (`KP`): the
front, the lcm, `d` (whose branches depend on `e` alone), the mask of a
small `d`, and the branch on it (`branch_ct`: status 2, the leak's), to the
zeros or to the key and its outputs (`keyCode_ct`); hence the contract's
`ConstantTime` (`keyCode_constantTime`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

theorem code_ct_eq : code = seqs (([.block (entry ++ VG.Impl.Rsa.AArch64.Keys.head)] : List (Prog isa)) ++
    (frontL ++ (lcmPart ++ (([dPart] : List (Prog isa)) ++ (smallMask ++
      ([.ite (.nonzero .x .x15) (zeros 2) keyPart] : List (Prog isa))))))) := by
  simp only [code, frontL, List.append_assoc]

/-- The branch on a small `d`, status 2 (the leak's). -/
theorem branch_ct [VG.Proof.Rsa.AArch64.InvLaw] : RelCT isa (Two (KG FF)) (.ite (.nonzero .x .x15) (zeros 2) keyPart) fun _ _ => True :=
  kg_ite (kg_nonzero_eq (g := fun p => mask (decide (p.st = 2))) fun _ _ hf => hf.x15)
    (zeros2_ct.mono (fun _ _ ⟨p, h₁, h₂, hsp⟩ =>
      ⟨p, EG.of_kg (h₁.imp fun _ _ => trivial), EG.of_kg (h₂.imp fun _ _ => trivial), hsp⟩)
      fun _ _ h => h)
    (keyPart_ct.mono (fun _ _ h => two_kg (fun _ _ ⟨⟨hp, _, ok, hok, _⟩, _⟩ => ⟨hp, ok, hok⟩) h) fun _ _ h => h)

/-- `vg_rsa_keygen_key` leaks the same in runs with the same public data. -/
theorem keyCode_ct [VG.Proof.Rsa.AArch64.InvLaw] : RelCT isa (Two KRel) code fun _ _ => True := by
  rw [code_ct_eq]
  refine rs_app (by simp) (by simp [frontL, loadA]) Key.start_ct ?_
  refine rs_app (by simp [frontL, loadA]) (by simp [lcmPart, phi, mulTo]) front_ct ?_
  refine rs_app (by simp [lcmPart, phi, mulTo]) (by simp) lcmPart_ct ?_
  refine rs_app (by simp) (by simp [smallMask, constA]) dPart_ct ?_
  exact rs_app (by simp [smallMask, constA]) (by simp) smallMask_ct branch_ct

/-- `vg_rsa_keygen_key` is constant time but for the lengths, `e`, and
whether `d` is too small. -/
theorem keyCode_constantTime [VG.Proof.Rsa.AArch64.InvLaw] : ConstantTime isa keyA.pre keyA.pub code := keyCT_of keyCode_ct

end VG.Proof.RsaKeyGen.AArch64.Key

end

end

/-! ### `RsaKeyGen.AArch64.Key.Implies`, which only this module used -/

section

/-!
# An RSA key from its primes on AArch64: the shared contract implies `keyA`
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64

theorem stackArgs_ten (s : State) :
    List.map (stackArg s) (List.range 10) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9] := rfl

/-- A state meeting the precondition: 32-byte primes, a one-byte `e`, the
stack arguments at `0x9000`. -/
def keySat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 64 | .x4 => 0x3000 | .x5 => 32 | .x6 => 0x4000
    | .x7 => 32 | _ => 0
  sp := 0x9000
  mem a := if a = 0x9048 then 0x20
    else if a = 0x9001 then 0x50 else if a = 0x9008 then 0x20 else if a = 0x9011 then 0x60 else
    if a = 0x9018 then 0x20 else if a = 0x9021 then 0x70 else if a = 0x9028 then 0x20 else
    if a = 0x9031 then 0x80 else if a = 0x9038 then 0x01 else if a = 0x9042 then 0x01 else
    if a = 0x9049 then 0x04 else 0
  rd := [⟨0x8000, 1⟩, ⟨0x9000, 80⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩, ⟨0x3000, 32⟩, ⟨0x4000, 32⟩, ⟨0x5000, 32⟩, ⟨0x6000, 32⟩, ⟨0x7000, 32⟩,
    ⟨0x10000, 8448⟩]

theorem key_implies : keyA.Implies (Proof.RsaKeyGen.keyContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig, abi, argRegs, keyA, keyPre,
      stackArgs_ten, List.append_eq] at h
    sig_pre [Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig, abi, argRegs, keyA, keyPre,
      stackArgs_ten, List.append_eq] at h
    sig_split h
    sig_reduce [Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig, abi, argRegs, keyA, keyPre,
      stackArgs_ten, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by
    intro s s' _ h
    sig_post [Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig, abi, argRegs, keyA, keyPre, keyPost, keyRes,
      keyOuts, stackArgs_ten, List.append_eq]
    sig_reduce [Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig, abi, argRegs, keyA, keyPre, keyPost, keyRes,
      keyOuts, stackArgs_ten, List.append_eq] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨h1, ?_⟩
    revert h2
    simp only [arg]
    generalize Proof.RsaKeyGen.keyOp _ _ _ _ = r
    rcases r with (f | ys) | u <;> first | exact id | simp
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig, abi, argRegs, keyA, keyPub,
      keyLeak, keyRes, stackArgs_ten, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
    refine ⟨?_, hsp, fun i hi => ?_, hl⟩
    · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩
    · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 by omega_using [hi]) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact a0
      · exact a1
      · exact a2
      · exact a3
      · exact a4
      · exact a5
      · exact a6
      · exact a7
      · exact a8
      · exact a9
  sat := by sig_implies_sat [Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig, abi, argRegs,
    keyA, keyPre, stackArgs_ten, List.append_eq] [keySat, stackArg, stackArgAddr, Mem.readW, Mem.read] using keySat

end VG.Proof.RsaKeyGen.AArch64.Key

end

end


/-!
# `vg_rsa_keygen_key` on AArch64: verified against the shared contract

With correctness (`keyCode_correct`), constant time (`keyCode_constantTime`)
and the shared contract's implication (`key_implies`), `code` is verified
(`key_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64

instance keyProof [VG.Proof.Rsa.AArch64.InvLaw] : KeyProof := ⟨keyCode_correct, keyCode_constantTime⟩

/-- `vg_rsa_keygen_key`. -/
theorem key_verified [VG.Proof.Rsa.AArch64.InvLaw] :
    Verified target VG.Impl.RsaKeyGen.AArch64.Key.code (Proof.RsaKeyGen.keyContract abi) :=
  Verified.of_correct keyCode_correct keyCode_constantTime key_implies

end VG.Proof.RsaKeyGen.AArch64.Key
