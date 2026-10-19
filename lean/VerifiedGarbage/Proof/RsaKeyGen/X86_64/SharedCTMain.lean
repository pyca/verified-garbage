module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedCTRound
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedMain
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMrLoop
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMrLoop
meta import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedRanges
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Exp
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubR2
import VerifiedGarbage.Proof.Bignum.X86_64.R2
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Template
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineRel
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.MillerRabin.X86_64.Body
import VerifiedGarbage.Proof.MillerRabin.X86_64.BodyKeeps
import VerifiedGarbage.Proof.MillerRabin.X86_64.CT
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallBody
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallCT
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallCorrect
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallStack
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallTemplate
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerContext
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerEntry
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerKept
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerRestore
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerResult
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerRound
import VerifiedGarbage.Proof.MillerRabin.X86_64.Context
import VerifiedGarbage.Proof.MillerRabin.X86_64.CoreFrame
import VerifiedGarbage.Proof.MillerRabin.X86_64.Correct
import VerifiedGarbage.Proof.MillerRabin.X86_64.CorrectMath
import VerifiedGarbage.Proof.MillerRabin.X86_64.ExitRegisters
import VerifiedGarbage.Proof.MillerRabin.X86_64.Finish
import VerifiedGarbage.Proof.MillerRabin.X86_64.Frame
import VerifiedGarbage.Proof.MillerRabin.X86_64.FramedBody
import VerifiedGarbage.Proof.MillerRabin.X86_64.FramedCall
import VerifiedGarbage.Proof.MillerRabin.X86_64.Frames
import VerifiedGarbage.Proof.MillerRabin.X86_64.Keeps
import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizeCT
import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizeContext
import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizeValues
import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizedPublic
import VerifiedGarbage.Proof.MillerRabin.X86_64.Prepared
import VerifiedGarbage.Proof.MillerRabin.X86_64.RoundCT
import VerifiedGarbage.Proof.MillerRabin.X86_64.Stage
import VerifiedGarbage.Proof.MillerRabin.X86_64.Verified
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.RsaKeyGen.Bits
import VerifiedGarbage.Proof.RsaKeyGen.CandMath
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.RsaKeyGen.Primes
import VerifiedGarbage.Proof.RsaKeyGen.TrialMath
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Copy
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdStep
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.ModE
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontRest
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrExp
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSel
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSelW
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrWit
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Trial
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Exp
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubR2
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.RsaKeyGen.Bits
meta import VerifiedGarbage.Proof.RsaKeyGen.CandMath
meta import VerifiedGarbage.Proof.RsaKeyGen.MrMont
meta import VerifiedGarbage.Proof.RsaKeyGen.Primes
meta import VerifiedGarbage.Proof.RsaKeyGen.TrialMath
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Copy
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdStep
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.ModE
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontRest
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrExp
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSel
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSelW
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrWit
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Trial
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop

/-! # Constant time of RSA's loop with a callable shared round -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.MillerRabin.X86_64
open VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen (shapeOf itersOf passS)

/-- `SharedMrSt` survives changes to registers Montgomery multiplication may
change, and none to memory. -/
theorem SharedMrSt.congr {B sp : Addr} {Z w : Nat} {mi : BitVec 64} {c ch : Nat} {rp : Addr} {r : List Byte} {s₀ : State}
    {res : Option (Bool × List Byte)} {i uni used : Nat} {s t : State} {rs : List Reg}
    (h : SharedMrSt B sp Z w mi c ch rp r s₀ res i uni used s) (hd : MrDims B Z w) (hm : t.mem = s.mem) (k : Keep rs s t)
    (hrs : ∀ r ∈ rs, r ∈ mmRegs) : SharedMrSt B sp Z w mi c ch rp r s₀ res i uni used t := by
  obtain ⟨⟨bm, hc⟩, hE, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, henv⟩ := h
  refine ⟨⟨bm, hc.of_frm hd (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (hc.good.scr.congr k.2.2)
    ((k.gpr (by intro h; have := hrs _ h; simp [mmRegs] at this)).trans hc.good.rdi) (by simp) (by simp) (by simp)
    (by simp) (by simp)⟩, by rw [hm]; exact hE, by rw [hm]; exact h1, by rw [hm]; exact h2, by rw [hm]; exact h3, by rw [hm]; exact h4,
    by rw [hm]; exact h5, h6.congrK (by rw [hm]; exact InScr.refl _ _ _) k, by rw [hm]; exact h7, by rw [hm]; exact h8,
    by rw [hm]; exact h9, h10, h11, h12, h13, h14, by rw [hm]; exact h15, (h16.trans k).mono (fun r hr => ?_), henv.kept k (fun h => by have := hrs _ h; simp [mmRegs] at this)⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact hr
  · exact hrs r hr

structure SharedLPub extends LPub where
  sp : Addr
  z28 : slot p.w 28 ≤ p.Z

abbrev SharedLPub.u (a : SharedLPub) (j : Nat) : Nat := a.toLPub.u j
abbrev SharedLPub.N (a : SharedLPub) : Nat := a.toLPub.N

/-- At the head of iteration `j`. -/
def SharedLoopI (a : SharedLPub) (j : Nat) (s : State) : Prop :=
  KW a.p.B a.p.wr ∧ MrDims a.p.B a.p.Z a.p.w ∧ a.p.ch < 2 ^ 62 ∧ a.p.rl < 2 ^ 64 ∧
    ∃ (mi : BitVec 64) (c : Nat) (r : List Byte) (s₀ : State) (res : Option (Bool × List Byte)) (uni : Nat),
      SharedMrSt a.p.B a.sp a.p.Z a.p.w mi c a.p.ch a.p.rP r s₀ res (j + 1) uni (a.u j) s ∧ shapeOf res = a.S ∧
      r.length = a.p.rl ∧ 1 < c ∧ VG.Proof.RsaKeyGen.PrimeShape (64 * a.p.w) c ∧
      word s₀.mem a.p.B (8 * kOut) = a.p.op ∧ word s₀.mem a.p.B (8 * kUsedP) = a.p.up ∧
      word s₀.mem a.p.B (8 * kLen) = BitVec.ofNat 64 (8 * a.p.w) ∧ s₀.wr = a.p.wr ∧
      itersOf (8 * a.p.w) a.p.rl a.S (a.u j) = a.N - j

/-- The header at the head of an iteration. -/
theorem SharedLoopI.hp {a : SharedLPub} {j : Nat} {s : State} (h : SharedLoopI a j s) :
    HP a.p.B a.p.wr (a.p.vs (j + 1) (a.u j)) s := by
  obtain ⟨-, hd, -, -, mi, c, r, s₀, res, uni, hI, -, hrl, -, -, hout, hup, -, hw, -⟩ := h
  obtain ⟨bm, hc⟩ := hI.ctx
  have hf := hI.frm
  have e : ∀ k, k = kOut ∨ k = kUsedP → word s.mem a.p.B (8 * k) = word s₀.mem a.p.B (8 * k) := fun k hk => by
    rcases hk with rfl | rfl
    · exact SharedFrame.word hf hI.env (sharedRoundRanges_hdr _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (by have := hdr_lt_slot a.p.w 28 (show kOut < 32 by decide); have := a.z28; omega_arith) hc.good.scr.nowrap
    · exact SharedFrame.word hf hI.env (sharedRoundRanges_hdr _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))) (by have := hdr_lt_slot a.p.w 28 (show kUsedP < 32 by decide); have := a.z28; omega_arith) hc.good.scr.nowrap
  have := mr_hp (ex := []) (i := j + 1) (u := a.u j) hc.good (hI.keep.2.2.trans hw)
    ⟨(e _ (Or.inl rfl)).trans hout, hI.len, (e _ (Or.inr rfl)).trans hup, hI.rand, by rw [hI.rlen, hrl], hI.chk,
      hI.ki, hI.kused⟩ (by simp)
  rwa [List.append_nil] at this

/-- Before the branch on `rand`'s length. -/
def SharedAvI (p : SharedLPub × Nat) (s : State) : Prop :=
  SharedLoopI p.1 p.2 s ∧ s.cf = some (decide (p.1.p.rl < p.1.u p.2 + 8 * p.1.p.w))

/-- What a round needs, at the head of an iteration with the witness's octets. -/
theorem sharedAvI_r0 {p : SharedLPub × Nat} {s : State} (h : SharedAvI p s) (hb : isa.eval .b s = some false) :
    SharedR0 (⟨p.1.p, p.2 + 1, p.1.u p.2, passS (8 * p.1.p.w) p.1.p.rl p.1.S (p.1.u p.2)⟩, p.1.sp) s := by
  have hp := h.1.hp
  obtain ⟨⟨hk, hd, hch, hrl, mi, c, r, s₀, res, uni, hI, hS, hrlen, hc1, hsh, -⟩, hcf⟩ := h
  simp only [eval, hcf, Option.some.injEq, decide_eq_false_iff_not, Nat.not_lt] at hb
  obtain ⟨bm, hc⟩ := hI.ctx
  have hw4 := hd.w4
  obtain ⟨_, _, hwb⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega) hsh
  have hiu := hI.iu
  have hul := hI.ul
  have hi : 32 * (p.2 + 1) ≤ 8 * p.1.p.w * (p.2 + 1) := Nat.mul_le_mul_right _ (by omega)
  have hj : p.2 + 1 < 2 ^ 59 := by omega
  have hun := hI.unii
  refine ⟨⟨hk, hp, hd, mi, c, bm, r, uni, hc, hI.ex, hI.r2, hc1, hsh, hI.src, hrlen, by rw [hrlen]; exact hb, hI.kuni,
    show p.2 + 1 < 2 ^ 61 by omega, by omega, hch, ?_⟩, p.1.z28, hI.env⟩
  rw [← hS, ← hI.rest, ← hrlen]
  exact (VG.Proof.RsaKeyGen.mr_pass hI.go hwb (by omega) (by rw [hrlen]; exact hb)).symm

/-- Where the loop ends. -/
def SharedLoopEnd (a : SharedLPub) (s : State) : Prop :=
  KW a.p.B a.p.wr ∧ MrDims a.p.B a.p.Z a.p.w ∧
    ∃ (mi : BitVec 64) (c : Nat) (r : List Byte) (s₀ : State) (res : Option (Bool × List Byte)),
      SharedMrEnd a.p.B a.sp a.p.Z a.p.w mi c r s₀ res s ∧ shapeOf res = a.S ∧ r.length = a.p.rl ∧
      word s₀.mem a.p.B (8 * kOut) = a.p.op ∧ word s₀.mem a.p.B (8 * kUsedP) = a.p.up ∧
      word s₀.mem a.p.B (8 * kLen) = BitVec.ofNat 64 (8 * a.p.w) ∧ s₀.wr = a.p.wr ∧ SharedEnv a.p.B a.p.Z a.sp s₀

/-- Miller–Rabin's loop leaks the same in runs that agree on the public data
and on the shape of the result. -/
theorem sharedMrLoop_ct (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) (R : Kernel) :
    RelCT isa (Two fun (a : SharedLPub) s => 0 < a.N ∧ SharedLoopI a 0 s)
      (.loop (seqs [
        .block [.mov .rcx (.mem (hdr kRandLen)), .mov .rax (.mem (hdr kUsed)), .alu .sub .rcx (.reg .rax),
          .mov .rax (.mem (hdr kLen)), .alu .cmp .rcx (.reg .rax)],
        .ite .b (.block [.mov32 .rax (.imm 0), .store (hdr kStat) .rax]) (seqs (mrRoundWith mm R.run)),
        .block [.mov .rax (.mem (hdr kStat)), .alu .cmp .rax (.imm 4)]]) .e) (Two SharedLoopEnd) := by
  refine two_loop (Φ := SharedLoopI) SharedLPub.N ?_ ?_
  · simp only [seqs]
    refine RelCT.seq (R := Two SharedAvI) (kt_piece (fun p : SharedLPub × Nat => p.1.p.B) (fun p => p.1.p.wr) mrS
      (fun p => p.1.p.vs (p.2 + 1) (p.1.u p.2)) [] (by decide) (fun p => vs_fst0 _ _ _)
      (fun _ _ h => ⟨h.2.1, h.2.hp⟩) (pins_nil _) (by taint_decide) ?_)
      (two_ite_seq (fun _ _ _ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ ?_)
    · rintro ⟨a, j⟩ s ⟨hj, h⟩
      have h' := h
      obtain ⟨hk, hd, hch, hrl, mi, c, r, s₀, res, uni, hI, hS, hrlen, hc1, hsh, ho, hu, hl0, hw, hit⟩ := h'
      obtain ⟨bm, hc⟩ := hI.ctx
      refine WP.mono (availCmp_ok hc.good hd.z (hI.rlen.trans (by rw [hrlen])) hI.kused hI.len (by rw [← hrlen]; exact hI.ul)
        hrl (by have := hd.w128; omega)) fun t ⟨hcf, hm, k⟩ =>
          ⟨⟨hk, hd, hch, hrl, mi, c, r, s₀, res, uni, hI.congr hd hm k (by decide), hS, hrlen, hc1, hsh, ho, hu, hl0, hw,
            hit⟩, hcf⟩
    · exact kt_ct (fun p : SharedLPub × Nat => p.1.p.B) (fun p => p.1.p.wr) [] (fun _ => []) [] (by decide)
        (fun _ => rfl) (fun _ _ h => ⟨h.1.1.1, hp_nil h.1.1.hp⟩) (pins_nil _) (by taint_decide)
    · refine RelCT.seq (R := Two fun (p : SharedLPub × Nat) s => KW p.1.p.B p.1.p.wr ∧ HP p.1.p.B p.1.p.wr [] s)
        (two_post (two_map (fun p : SharedLPub × Nat =>
          ((⟨p.1.p, p.2 + 1, p.1.u p.2, passS (8 * p.1.p.w) p.1.p.rl p.1.S (p.1.u p.2)⟩ : RPub), p.1.sp))
          (fun _ _ h => sharedAvI_r0 h.1 h.2) (sharedRound_ct M hmc R)) ?_)
        (kt_ct (fun p : SharedLPub × Nat => p.1.p.B) (fun p => p.1.p.wr) [] (fun _ => []) [] (by decide)
          (fun _ => rfl) (fun _ _ h => h) (pins_nil _) (by taint_decide))
      rintro p s ⟨h, hb⟩
      have hr := sharedAvI_r0 h hb
      obtain ⟨⟨hk, hp, hd, mi, c, bm, r, uni, hc, hE, hR2, hc1, hsh, hsrc, -, hlen, hun, hi, huni, hch, -⟩, hz, henv⟩ := hr
      have hm := (hp0 hp).mrh
      exact WP.mono (sharedRound_ok M hmc R hd hz henv hc hE hR2 hc1 hsh hm.rand hm.used hm.len hsrc hlen hm.ki hun hm.chk hi huni hch)
        fun t ⟨⟨_, hc'⟩, _, _, _, _, _, _, k⟩ => ⟨hk, hc'.good.rdi, k.2.2.trans hp.wr, fun _ he => absurd he (List.not_mem_nil)⟩
  · rintro a j s hj ⟨hk, hd, hch, hrl, mi, c, r, s₀, res, uni, hI, hS, hrlen, hc1, hsh, ho, hu, hl0, hw, hit⟩
    have hw4 := hd.w4
    obtain ⟨_, _, hwb⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega) hsh
    refine WP.mono (sharedMrIter_ok M hmc R hd a.z28 hc1 hsh (by omega) hch s hI) fun t ht => ?_
    rcases ht with ⟨he, hend, hnone, hsome⟩ | ⟨he, uni', hI'⟩
    · have h1 : itersOf (8 * a.p.w) a.p.rl a.S (a.u j) = 1 := by
        rcases hres : res with _ | ⟨b, rest⟩
        · rw [← hS, hres]; exact VG.Proof.RsaKeyGen.iters_end_none (by omega) (by rw [← hrlen]; exact hnone hres)
        · rw [← hS, hres]
          exact VG.Proof.RsaKeyGen.iters_end_some (by omega) (by rw [← hrlen]; exact hsome b rest hres)
      refine ⟨by rw [he]; simp only [Option.some.injEq, Bool.false_eq, decide_eq_false_iff_not, Nat.not_lt]; omega,
        fun h => absurd h (by omega), fun _ => ⟨hk, hd, mi, c, r, s₀, res, hend, hS, hrlen, ho, hu, hl0, hw, hI.env.back hI.keep (by decide)⟩⟩
    · have hu' : a.u (j + 1) = a.u j + 8 * a.p.w := by simp only [SharedLPub.u, LPub.u]; rw [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
      have hc := VG.Proof.RsaKeyGen.iters_cont (L := 8 * a.p.w) (r := r) (a := (Spec.Rsa.splitTwos (c - 1)).1)
        (m := (Spec.Rsa.splitTwos (c - 1)).2) hI'.go hwb (by omega) (by omega) hI'.ul
      have hr' : Spec.RsaKeyGen.loop (Spec.RsaKeyGen.mrStep c a.p.ch (Spec.Rsa.splitTwos (c - 1)).1
          (Spec.Rsa.splitTwos (c - 1)).2) (j + 1 + 1, uni') (List.drop (a.u j + 8 * a.p.w) r) = res := hI'.rest
      rw [show a.u j + 8 * a.p.w - 8 * a.p.w = a.u j by omega, hr', hS, hrlen] at hc
      refine ⟨by rw [he]; exact congrArg some (decide_eq_true (by omega)).symm, fun _ => ?_, fun h => absurd h (by omega)⟩
      rw [← hu'] at hI'
      exact ⟨hk, hd, hch, hrl, mi, c, r, s₀, res, uni', hI', hS, hrlen, hc1, hsh, ho, hu, hl0, hw, by rw [hu']; omega⟩

/-- What `millerRabin` needs (`millerRabin_ok`'s hypotheses), for the shape
of its result. -/
def SharedMrPre (a : SharedLPub) (s : State) : Prop :=
  KW a.p.B a.p.wr ∧ HP a.p.B a.p.wr [] s ∧ MrDims a.p.B a.p.Z a.p.w ∧ a.p.ch < 2 ^ 62 ∧ a.p.rl < 2 ^ 64 ∧
    ∃ (mi : BitVec 64) (c bm : Nat) (r : List Byte), MrCtx s a.p.B a.p.Z a.p.w mi c bm ∧ ECtx s.mem a.p.B a.p.w c ∧
      wv s.mem a.p.B (slot a.p.w aR2) a.p.w = 2 ^ (64 * a.p.w) * 2 ^ (64 * a.p.w) % c ∧ 1 < c ∧
      VG.Proof.RsaKeyGen.PrimeShape (64 * a.p.w) c ∧ word s.mem a.p.B (8 * kOut) = a.p.op ∧
      word s.mem a.p.B (8 * kUsedP) = a.p.up ∧ word s.mem a.p.B (8 * kRand) = a.p.rP ∧
      word s.mem a.p.B (8 * kLen) = BitVec.ofNat 64 (8 * a.p.w) ∧
      word s.mem a.p.B (8 * kRandLen) = BitVec.ofNat 64 r.length ∧ r.length = a.p.rl ∧
      word s.mem a.p.B (8 * kChecks) = BitVec.ofNat 64 a.p.ch ∧ Src s a.p.B a.p.Z a.p.rP r ∧
      word s.mem a.p.B (8 * kUsed) = BitVec.ofNat 64 a.u0 ∧ 8 * a.p.w ≤ a.u0 ∧ a.u0 ≤ r.length ∧
      shapeOf (mrRest c a.p.ch r 1 0 a.u0) = a.S ∧ SharedEnv a.p.B a.p.Z a.sp s

/-- `millerRabin` leaks the same in runs that agree on the public data and on
the shape of the result. -/
theorem sharedMillerRabin_ct (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) (R : Kernel) : RelCT isa (Two SharedMrPre) (seqs (millerRabinWith mm R.run)) (Two SharedLoopEnd) := by
  unfold millerRabinWith
  simp only [seqs]
  refine RelCT.seq (kt_piece (fun a : SharedLPub => a.p.B) (fun a => a.p.wr) [] (fun _ => []) [] (by decide)
    (fun _ => rfl) (fun _ _ h => ⟨h.1, h.2.1⟩) (pins_nil _) (by taint_decide) ?_) (sharedMrLoop_ct M hmc R)
  rintro a s ⟨hk, hp, hd, hch, hrl, mi, c, bm, r, hc, hE, hr2, hc1, hsh, ho, hup, hR, hK, hRL, hrlen, hC, hsrc, hU, hu1,
    hu2, hS, henv⟩
  have hw4 := hd.w4
  obtain ⟨_, _, hwb⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega) hsh
  have hN : 1 ≤ a.N := by
    have := (VG.Proof.RsaKeyGen.iters_cont (L := 8 * a.p.w) (r := r) (a := (Spec.Rsa.splitTwos (c - 1)).1)
      (m := (Spec.Rsa.splitTwos (c - 1)).2) (ch := a.p.ch) (i := 1) (uni := 0) (Or.inl (by decide)) hwb (by omega) hu1
      hu2).2
    have hr' : Spec.RsaKeyGen.loop (Spec.RsaKeyGen.mrStep c a.p.ch (Spec.Rsa.splitTwos (c - 1)).1
        (Spec.Rsa.splitTwos (c - 1)).2) (1, 0) (List.drop a.u0 r) = mrRest c a.p.ch r 1 0 a.u0 := rfl
    rwa [hr', hS, hrlen] at this
  refine WP.mono (sharedMrInit_ok hd a.z28 henv hc hE hr2 hR hK hRL hC hsrc hU hu1 hu2) fun t hI => ⟨hN, hk, hd, hch, hrl, mi, c, r, s,
    _, 0, by simpa [SharedLPub.u, LPub.u] using hI, hS, hrlen, hc1, hsh, ho, hup, hK, hp.wr, by simp [SharedLPub.u, LPub.u]⟩

end VG.Proof.RsaKeyGen.X86_64
