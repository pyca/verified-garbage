module

import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.X86_64.FrameAlloc
import VerifiedGarbage.Proof.RsaPss.SignCases
public import VerifiedGarbage.Proof.RsaPss.X86_64.Params
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.RsaPss.Params
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignPro
import Batteries.Logic
public import VerifiedGarbage.Proof.RsaPss.X86_64.Loops
import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha256.X86_64.Lit
import Mathlib.Order.Defs.PartialOrder
import VerifiedGarbage.Proof.Rsa.X86_64.PubChecked
import Mathlib.Tactic.Set
import Mathlib.Data.Int.GCD
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame

/-! ### `RsaPss.X86_64.SignCall`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS signing on x86-64: the call of `vg_rsa_private_checked`

With its stack arguments in the frame's first 14 words (`EM` at
`scratch + oEm` as the input, the private key, the rest of `scratch`),
`vg_rsa_private_checked` runs under its contract (`priv_pre`), and returns
with `out` written as it says, the frame and our working space kept
(`priv_call`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (chkContract)

variable {tsH tsG : List FnTable}

/-- `out`, and the caller's working space. -/
def outR (s : State) : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
def scrR (s : State) : Region := ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩

/-- What the private-key operation reads: `n`, `e`, `EM`, the private key and
its stack arguments. -/
def pRd (s : State) : List Region :=
  [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨off (stackArg s 14) oEm, (s.gpr .rcx).toNat⟩,
    ⟨stackArg s 0, (stackArg s 1).toNat⟩, ⟨stackArg s 2, (stackArg s 3).toNat⟩,
    ⟨stackArg s 4, (stackArg s 5).toNat⟩, ⟨stackArg s 6, (stackArg s 7).toNat⟩,
    ⟨stackArg s 8, (stackArg s 9).toNat⟩, ⟨fb s, 112⟩]

/-- What it writes: `out`, and the rest of the working space. -/
def pWr (s : State) : List Region :=
  [⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩,
    ⟨off (stackArg s 14) oRsa, (stackArg s 15 - BitVec.ofNat 64 1024).toNat * 8⟩]

/-- Its stack arguments. -/
def pArg (s : State) (i : Nat) : BitVec 64 :=
  match i with
  | 0 => off (stackArg s 14) oEm
  | 1 => s.gpr .rcx
  | 12 => off (stackArg s 14) oRsa
  | 13 => stackArg s 15 - BitVec.ofNat 64 1024
  | i => stackArg s (i - 2)

theorem fb_sub8' {s : State} (hp : SPre tsH tsG s) : (fb s - 8).toNat = (fb s).toNat - 8 := by
  obtain hF := fb_toNat hp; have := hp.sp1
  rw [BitVec.toNat_sub]; unfold signStack Proof.Rsa.X86_64.stackBytes frameBytes at *
  rw [show (8 : BitVec 64).toNat = 8 from rfl]; omega_using [hF, this]

/-- A stack argument of a function called from the frame is a word of it. -/
theorem stackArg_call {s t : State} (hp : SPre tsH tsG s) (hsp : t.gpr .rsp = fb s) (rd wr : List Region) {i : Nat}
    (hi : i < 16) : stackArg (t.callEntry.withRegions rd wr) i = word t.mem (fb s) (8 * i) := by
  obtain hF := fb_toNat hp
  have := hp.sp1; have := hp.sp2
  obtain hsep := Offset.sep (fb s - 8) (d := 8 * (i + 1)) (n := 8) (e := 0) (k := 8) (by omega_using []) (by omega_using [hi])
    (by omega_using [])
  rw [show fb s - 8 + BitVec.ofNat 64 0 = fb s - 8 from BitVec.add_zero _] at hsep
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_mem, hsp]
  rw [Mem.readW_writeW_sep hsep (by decide)]
  show _ = t.mem.readW (off (fb s) (8 * i)) 64
  obtain ea : fb s - 8 + BitVec.ofNat 64 (8 * (i + 1)) = off (fb s) (8 * i) := by
    simp only [off]
    rw [show 8 * (i + 1) = 8 + 8 * i by omega_using [], ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc,
      show BitVec.ofNat 64 8 = 8 from rfl, BitVec.sub_add_cancel]
  rw [ea]

theorem stackArgAddr_call {s t : State} (hsp : t.gpr .rsp = fb s) (rd wr : List Region) :
    stackArgAddr (t.callEntry.withRegions rd wr) 0 = fb s := by
  simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hsp]
  exact BitVec.sub_add_cancel _ _

theorem stackArgAddr_callj {s t : State} (hsp : t.gpr .rsp = fb s) (rd wr : List Region) (j : Nat) :
    stackArgAddr (t.callEntry.withRegions rd wr) j = off (fb s) (8 * j) := by
  simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hsp, off]
  rw [show 8 * (j + 1) = 8 + 8 * j by omega_using [], ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc,
    show BitVec.ofNat 64 8 = 8 from rfl, BitVec.sub_add_cancel]

theorem priv_pre {s t : State} (hp : SPre tsH tsG s) (hsp : t.gpr .rsp = fb s)
    (hargs : ∀ i < 14, word t.mem (fb s) (8 * i) = pArg s i) (hdi : t.gpr .rdi = s.gpr .rdi)
    (hsi : t.gpr .rsi = s.gpr .rcx) (hdx : t.gpr .rdx = s.gpr .rdx) (hcx : t.gpr .rcx = s.gpr .rcx)
    (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9) :
    chkContract.pre (t.callEntry.withRegions (pRd s) (pWr s)) := by
  obtain hE : ∀ i < 14, stackArg (t.callEntry.withRegions (pRd s) (pWr s)) i = pArg s i :=
    fun i hi => (stackArg_call hp hsp _ _ (by omega_using [hi])).trans (hargs i hi)
  simp only [chkContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
    hdi, hsi, hdx, hcx, h8, h9, hsp, stackArgAddr_call hsp, hE 0 (by decide), hE 1 (by decide),
    hE 2 (by decide), hE 3 (by decide), hE 4 (by decide), hE 5 (by decide), hE 6 (by decide), hE 7 (by decide),
    hE 8 (by decide), hE 9 (by decide), hE 10 (by decide), hE 11 (by decide), hE 12 (by decide), hE 13 (by decide),
    pArg, Nat.reduceSub]
  obtain hF := fb_toNat hp
  have := hp.sp1; have := hp.sp2
  obtain hk1 := hp.k1; have hk2 := hp.k2
  obtain hsl := hp.hsl; have wS := hp.wS
  have h392 : frameBytes = 392 := rfl
  have hss : signStack = 3656 := rfl
  have hsb : Rsa.X86_64.stackBytes = 3256 := rfl
  have c1 : oEm = 2560 := rfl
  have c2 : oRsa = 8192 := rfl
  have hsi := hp.hsi
  obtain h8 := fb_sub8' hp
  obtain hsc : (stackArg s 15 - 1024#64).toNat = (stackArg s 15).toNat - 1024 := by
    rw [BitVec.toNat_sub, show (1024#64).toNat = 1024 from rfl]; omega_using [hsl]
  obtain toNat_off : ∀ {p : Addr} {d : Nat}, p.toNat + d < 2 ^ 64 → (off p d).toNat = p.toNat + d := fun h => by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [h]
  -- `out`, with the length `n_len`.
  obtain ho : ∀ {R : Region}, (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint R →
      (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint R := fun h => by rw [← hsi]; exact h
  obtain hKo : (stkR s).Disjoint ⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ := by rw [← hsi]; exact hp.dKo
  -- What lies in what.
  obtain sI : Region.Sub ⟨off (stackArg s 14) oEm, (s.gpr .rcx).toNat⟩ ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩ :=
    Offset.sub_base _ (by omega_using [hsl, c1])
  obtain sR : Region.Sub ⟨off (stackArg s 14) oRsa, (stackArg s 15 - 1024#64).toNat * 8⟩
      ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩ := Offset.sub_base _ (by rw [hsc]; omega_using [hsl, c2])
  obtain sA : Region.Sub ⟨fb s, 112⟩ (stkR s) := fun a h => frame_sub s a (Region.sub_prefix (by decide) a h)
  obtain sRet : Region.Sub ⟨fb s - 8, 8⟩ (stkR s) := ret8_sub s
  obtain sStk : Region.Sub ⟨fb s - 8 - BitVec.ofNat 64 Rsa.X86_64.stackBytes, Rsa.X86_64.stackBytes⟩ (stkR s) := by
    simp only [stkR, fb, show (8 : Addr) = BitVec.ofNat 64 8 from rfl, sub_sub']
    exact Offset.sub_below _ (by decide) (by decide)
  obtain dRA : (⟨fb s - 8, 8⟩ : Region).Disjoint ⟨fb s, 112⟩ :=
    (Offset.base_disjoint_below (fb s) (n := 8) (k := 112) (by omega_using [])).symm
  obtain dKA : (⟨fb s - 8 - BitVec.ofNat 64 Rsa.X86_64.stackBytes, Rsa.X86_64.stackBytes⟩ : Region).Disjoint
      ⟨fb s, 112⟩ := by
    refine Region.Disjoint.sub_left (Offset.base_disjoint_below (fb s) (n := 3264) (k := 112) (by omega_using [])).symm ?_
    simp only [show (8 : Addr) = BitVec.ofNat 64 8 from rfl, sub_sub']
    exact Offset.sub_below _ (by decide) (by decide)
  obtain dIR : (⟨off (stackArg s 14) oEm, (s.gpr .rcx).toNat⟩ : Region).Disjoint
      ⟨off (stackArg s 14) oRsa, (stackArg s 15 - 1024#64).toNat * 8⟩ :=
    Offset.disjoint _ (.inl (by omega_using [hk2, c1, c2])) (by omega_using [hsl, c1]) (by rw [hsc]; omega_using [wS, c2])
  obtain hsA : (⟨stackArg s 14, (stackArg s 15).toNat * 8⟩ : Region).Disjoint ⟨fb s, 112⟩ := (hp.dKs.sub_left sA).symm
  refine ⟨by omega_arith, by omega_using [hF, h392, h8], rfl, rfl, ho hp.dOn, ho hp.dOe, (ho hp.dOs).sub_right sI, ho hp.dOp, ho hp.dOq,
    ho hp.dOdp, ho hp.dOdq, ho hp.dOqi, (ho hp.dOs).sub_right sR, (hKo.sub_left sA).symm,
    hp.dns.sub_right sR, hp.des.sub_right sR, dIR, hp.dps.sub_right sR, hp.dqs.sub_right sR, hp.ddps.sub_right sR,
    hp.ddqs.sub_right sR, hp.dqis.sub_right sR, hsA.sub_left sR,
    hKo.sub_left sRet, hp.dKn.sub_left sRet, hp.dKe.sub_left sRet, (hp.dKs.sub_left sRet).sub_right sI,
    hp.dKp.sub_left sRet, hp.dKq.sub_left sRet, hp.dKdp.sub_left sRet, hp.dKdq.sub_left sRet, hp.dKqi.sub_left sRet,
    (hp.dKs.sub_left sRet).sub_right sR, dRA,
    hKo.sub_left sStk, hp.dKn.sub_left sStk, hp.dKe.sub_left sStk, (hp.dKs.sub_left sStk).sub_right sI,
    hp.dKp.sub_left sStk, hp.dKq.sub_left sStk, hp.dKdp.sub_left sStk, hp.dKdq.sub_left sStk, hp.dKqi.sub_left sStk,
    (hp.dKs.sub_left sStk).sub_right sR, dKA,
    by rw [← hsi]; exact hp.wO, hp.wN, hp.wE, by rw [toNat_off (by omega_using [hsl, wS, c1])]; omega_using [hsl, wS, c1], hp.wP, hp.wQ, hp.wDp, hp.wDq,
    hp.wQi, by rw [toNat_off (by omega_using [hk1, hsl, wS, c2]), hsc]; omega_using [hsl, wS, c2], ⟨hk1, hk2⟩, trivial, trivial, hp.L1, hp.L2, hp.pl1, hp.pl2,
    hp.ql1, hp.ql2, hp.hdpl, hp.hqil, hp.hdql, by unfold Spec.Rsa.scratchWords; rw [hsc]; omega_using [hsl]⟩

/-- Bytes apart from a frame's regions. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {len : Nat}
    (hd : ∀ r ∈ rs, (⟨p, len⟩ : Region).Disjoint r) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p len = Spec.Rsa.bytesAt m p len := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) hd hl (List.mem_range.mp hi)

/-- The three regions the function writes. -/
abbrev wrR (s : State) : List Region := [stkR s, outR s, scrR s]

/-- An input, apart from them. -/
theorem in_apart {s : State} {R : Region} (hK : (stkR s).Disjoint R) (hO : (outR s).Disjoint R)
    (hS : R.Disjoint (scrR s)) : ∀ r ∈ wrR s, R.Disjoint r := by
  intro r hr
  simp only [wrR, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hK.symm
  · exact hO.symm
  · exact hS

/-- The call of a function that writes what `vg_rsa_private_checked` does
(`hk`), under its contract `k`, which the call meets (`hpre`, `hc`, `hw`)
with the regions `rds` read. -/
theorem privWith_call {privN : String} {privC : Prog isa} {k : Contract isa}
    (hk : ∀ a b, k.post a b → chkContract.post a b)
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa privC s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : SpSafe privC) (hd : privC.x86_64Depth ≤ Rsa.X86_64.stackBytes)
    {s t : State} (hp : SPre tsH tsG s) (hst : t.gpr .rsp = fb s)
    (hM : Frame (wrR s) s.mem t.mem)
    (hargs : ∀ i < 14, word t.mem (fb s) (8 * i) = pArg s i) (hdi : t.gpr .rdi = s.gpr .rdi)
    (hdx : t.gpr .rdx = s.gpr .rdx) (hcx : t.gpr .rcx = s.gpr .rcx)
    (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9) {rds : List Region}
    (hpre : k.pre (t.callEntry.withRegions rds (pWr s))) (hc : Covers (rds ++ pWr s) (t.rd ++ t.wr))
    (hw : Covers (pWr s) t.wr) :
    WP isa (.call privN privC) t fun t' => t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 ∧
      Frame (wrR s) s.mem t'.mem ∧
      (∀ x, ((frR s).Contains x 1 ∨ (⟨stackArg s 14, oRsa⟩ : Region).Contains x 1) → t'.mem x = t.mem x) ∧
      Spec.Rsa.writtenOutcome t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((t'.gpr .rax).setWidth 32)
        (Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
          (Spec.Rsa.bytesAt t.mem (off (stackArg s 14) oEm) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat)) := by
  have hsb : Rsa.X86_64.stackBytes = 3256 := rfl
  refine X86_64.WP.callF hv hsp (by omega_using [hd, hsb]) hpre hc hw ?_
  intro t' hrd' hwr' hcs hf ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  replace hpost := hk _ _ hpost
  obtain hF := fb_toNat hp
  have := hp.sp1; have := hp.sp2
  obtain hk1 := hp.k1; have hk2 := hp.k2; have hsl := hp.hsl; have wS := hp.wS
  have h392 : frameBytes = 392 := rfl
  have hss : signStack = 3656 := rfl
  have c2 : oRsa = 8192 := rfl
  have c1 : oEm = 2560 := rfl
  obtain hsc : (stackArg s 15 - 1024#64).toNat = (stackArg s 15).toNat - 1024 := by
    rw [BitVec.toNat_sub, show (1024#64).toNat = 1024 from rfl]; omega_using [hsl]
  rw [hst] at hf
  -- What the call writes, within what the function may write.
  obtain sOut : Region.Sub ⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ (outR s) := by
    rw [outR, hp.hsi]; exact fun _ h => h
  obtain sScr : Region.Sub ⟨off (stackArg s 14) oRsa, (stackArg s 15 - 1024#64).toNat * 8⟩ (scrR s) :=
    Offset.sub_base _ (by rw [hsc]; omega_using [hsl, c2])
  obtain sBel : Region.Sub (below (fb s) (privC.x86_64Depth + 8)) (stkR s) := by
    simp only [below, fb, stkR, sub_sub']
    exact Offset.sub_below _ (by omega_using [hd, hsb, h392, hss]) (by omega_using [hd, hsb, hss])
  refine ⟨hrd', hwr', hcs, hmx, hM.trans (hf.sub fun r hr => ?_), fun x hx => hf x fun r hr hc => ?_, ?_⟩
  · simp only [pWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sOut⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), sScr⟩
    · exact ⟨_, List.mem_cons_self .., sBel⟩
  · simp only [pWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain dFb : (frR s).Disjoint (below (fb s) (privC.x86_64Depth + 8)) :=
      Offset.base_disjoint_below (fb s) (by omega_using [hd, hsb, h392])
    rcases hx with hx | hx <;> rcases hr with rfl | rfl | rfl
    · exact (hp.dKo.sub_left (frame_sub s)) x hx (sOut x hc)
    · exact (hp.dKs.sub_left (frame_sub s)) x hx (sScr x hc)
    · exact dFb x hx hc
    · exact (hp.dOs.symm.sub_left (Region.sub_prefix (by omega_using [hsl, c2]))) x hx (sOut x hc)
    · exact (Offset.base_disjoint (stackArg s 14) (e := oRsa) (n := (stackArg s 15 - 1024#64).toNat * 8)
        (k := oRsa) (le_refl _) (by rw [hsc]; omega_using [wS, c2])) x hx hc
    · exact ((hp.dKs.sub_left sBel).symm.sub_left (Region.sub_prefix (by omega_using [hsl, c2]))) x hx hc
  · have hE : ∀ i < 14, stackArg (t.callEntry.withRegions rds (pWr s)) i = pArg s i :=
      fun i hi => (stackArg_call hp hst _ _ (by omega_using [hi])).trans (hargs i hi)
    obtain fE : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
      rw [State.callEntry_mem, hst]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
    obtain fSE : Frame (wrR s) s.mem t.callEntry.mem := hM.trans (fE.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., ret8_sub s⟩)
    obtain b : ∀ {R : Region}, (stkR s).Disjoint R → (outR s).Disjoint R → R.Disjoint (scrR s) → R.len ≤ 2 ^ 64 →
        Spec.Rsa.bytesAt t.callEntry.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len :=
      fun hK hO hS hl => bytesAt_frame fSE (in_apart hK hO hS) hl
    obtain bEm : Spec.Rsa.bytesAt t.callEntry.mem (off (stackArg s 14) oEm) (s.gpr .rcx).toNat =
        Spec.Rsa.bytesAt t.mem (off (stackArg s 14) oEm) (s.gpr .rcx).toNat :=
      bytesAt_frame fE (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact ((hp.dKs.sub_left (ret8_sub s)).symm.sub_left (Offset.sub_base _ (by omega_using [hsl, c1])))) (by omega_using [])
    simp only [chkContract, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
      hdi, hdx, hcx, h8, h9, hE 0 (by decide), hE 2 (by decide), hE 3 (by decide), hE 4 (by decide),
      hE 5 (by decide), hE 6 (by decide), hE 8 (by decide), hE 10 (by decide), pArg, Nat.reduceSub, hm₂,
      hg₂ .rax (by decide)] at hpost
    rw [b (R := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩) hp.dKn hp.dOn hp.dns (by have := hp.wN; dsimp only; omega_using []),
      b (R := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩) hp.dKe hp.dOe hp.des (by have := hp.wE; dsimp only; omega_using []),
      bEm,
      b (R := ⟨stackArg s 0, (stackArg s 1).toNat⟩) hp.dKp hp.dOp hp.dps (by have := hp.wP; dsimp only; omega_using []),
      b (R := ⟨stackArg s 2, (stackArg s 3).toNat⟩) hp.dKq hp.dOq hp.dqs (by have := hp.wQ; dsimp only; omega_using []),
      b (R := ⟨stackArg s 4, (stackArg s 1).toNat⟩) (by rw [← hp.hdpl]; exact hp.dKdp) (by rw [← hp.hdpl]; exact hp.dOdp)
        (by rw [← hp.hdpl]; exact hp.ddps) (by have := hp.wDp; have := hp.hdpl; dsimp only; omega_using []),
      b (R := ⟨stackArg s 6, (stackArg s 3).toNat⟩) (by rw [← hp.hdql]; exact hp.dKdq) (by rw [← hp.hdql]; exact hp.dOdq)
        (by rw [← hp.hdql]; exact hp.ddqs) (by have := hp.wDq; have := hp.hdql; dsimp only; omega_using []),
      b (R := ⟨stackArg s 8, (stackArg s 1).toNat⟩) (by rw [← hp.hqil]; exact hp.dKqi) (by rw [← hp.hqil]; exact hp.dOqi)
        (by rw [← hp.hqil]; exact hp.dqis) (by have := hp.wQi; have := hp.hqil; dsimp only; omega_using [])] at hpost
    exact hpost

/-! ## The stack arguments -/

/-- Stack argument `j` (of ours) to word `j + 2` of the frame. -/
def cpyArg (j : Nat) : List Instr := [.mov .rax (.mem (arg j)), .store (sp (16 + 8 * j)) .rax]

def privTail : List Instr :=
  scr .rax oEm ++ ([.store (sp 0) .rax, .mov .rax (.mem (sp sK)), .store (sp 8) .rax] : List Instr) ++
  scr .rax oRsa ++ ([.store (sp 96) .rax, .mov .rax (.mem (sp sScrLen)), .alu .sub .rax (.imm 1024),
    .store (sp 104) .rax] : List Instr) ++
  ([.mov .rdi (.mem (sp sOut)), .mov .rsi (.mem (sp sK)), .mov .rdx (.mem (sp sN)), .mov .rcx (.mem (sp sK)),
    .mov .r8 (.mem (sp sE)), .mov .r9 (.mem (sp sEl))] : List Instr)

theorem privArgs_eq : privArgs = (List.range 10).flatMap cpyArg ++ privTail := rfl

/-- Our stack arguments, still where they were. -/
def ArgsKept (s : State) (m : Mem) : Prop := ∀ j < 18, m.readW (stackArgAddr s j) 64 = stackArg s j

theorem ArgsKept.write {s : State} (hp : SPre tsH tsG s) {m : Mem} (h : ArgsKept s m) {d : Nat}
    (hd : d + 8 ≤ frameBytes) (v : BitVec 64) : ArgsKept s (m.writeW (off (fb s) d) v) := fun j hj => by
  obtain hF := fb_toNat hp
  have := hp.sp2
  rw [← argAddr, Mem.readW_writeW_sep (Offset.sep _ (.inr (by unfold frameBytes at *; omega_using [hd])) (by omega_using [hj, hF, this])
    (by omega_using [hd, hF])) (by decide)]
  exact (congrArg (fun a => m.readW a 64) (argAddr s j)).trans (h j hj)

theorem cpyArg_ok {s : State} (hp : SPre tsH tsG s) {u : State} {S : Addr} (L : Lay u (fb s) S) (hrd : u.rd = s.rd)
    (hA : ArgsKept s u.mem) {j : Nat} (hj : j < 10) :
    WP isa (.block (cpyArg j)) u fun u' => Keep [.rax] u u' ∧
      u'.mem = u.mem.writeW (off (fb s) (16 + 8 * j)) (stackArg s j) := by
  obtain hF := fb_toNat hp
  have := hp.sp2
  obtain hin : InRegions (u.rd ++ u.wr) (off (fb s) (frameBytes + 8 + 8 * j)) 8 := by
    rw [argAddr]; exact hp.argIn hrd (by omega_using [hj])
  refine WP.keep [.rax] (Q := fun u' => u'.mem = u.mem.writeW (off (fb s) (16 + 8 * j)) (stackArg s j)) ?_ rfl
    |> WP.mono <| fun u' ⟨hm, k⟩ => ⟨k, hm⟩
  obtain hv : u.mem.readW (off (fb s) (frameBytes + 8 + 8 * j)) 64 = stackArg s j := by
    rw [argAddr]; exact hA j (by omega_using [hj])
  xrun [cpyArg, arg, ea_sp, L.rsp, hin, hv, L.st (d := 16 + 8 * j) (by unfold frameBytes; omega_arith)]

/-- The words the copies leave. -/
def cpW (s : State) (W : Nat → BitVec 64) (n : Nat) (i : Nat) : BitVec 64 :=
  if 2 ≤ i ∧ i < 2 + n then stackArg s (i - 2) else W i

theorem cpys_ok {s : State} (hp : SPre tsH tsG s) {S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} :
    ∀ n ≤ 10, ∀ u : State, Lay u (fb s) S → u.rd = s.rd → ArgsKept s u.mem → Rep u.mem (fb s) S V W →
    WP isa (.block ((List.range n).flatMap cpyArg)) u fun u' => Keep [.rax] u u' ∧ Lay u' (fb s) S ∧
      ArgsKept s u'.mem ∧ Rep u'.mem (fb s) S V (cpW s W n)
  | 0, _, u, L, _, hA, R => WP.block_nil ⟨Keep.refl _ _, L, hA, by
      refine (congrArg (fun W' => Rep u.mem (fb s) S V W') (funext fun i => ?_)).mp R
      simp only [cpW]; rw [ifn (by omega_using [])]⟩
  | n + 1, hn, u, L, hrd, hA, R => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (cpys_ok hp n (by omega_using [hn]) u L hrd hA R) fun u1 ⟨k1, L1, hA1, R1⟩ => ?_
    refine WP.mono (cpyArg_ok hp L1 (k1.2.1.trans hrd) hA1 (j := n) (by omega_using [hn])) fun u2 ⟨k2, hm2⟩ => ?_
    obtain R2 := R1.wf L1.geo (k := n + 2) (by unfold nW frameBytes; omega_using [hn]) (stackArg s n)
    rw [show off (fb s) (8 * (n + 2)) = off (fb s) (16 + 8 * n) by congr 1; omega_using [], ← hm2] at R2
    obtain R2' : Rep u2.mem (fb s) S V (cpW s W (n + 1)) := by
      refine (congrArg (fun W' => Rep u2.mem (fb s) S V W') (funext fun i => ?_)).mp R2
      simp only [upd, cpW]
      by_cases hi : i = n + 2
      · subst hi; rw [ifp rfl, ifp (by omega_using []), show n + 2 - 2 = n by omega_using []]
      · rw [ifn hi]
        by_cases h' : 2 ≤ i ∧ i < 2 + n
        · rw [ifp h', ifp (by omega_using [h'])]
        · rw [ifn h', ifn (by omega_using [hi, h'])]
    refine ⟨(k1.trans k2).mono (by decide), L1.of_rep' R1 R2'
        (by simp only [cpW]; rw [ifn (by omega_using [hn]), ifn (by omega_arith)]) (k2.gpr (by decide)) k2.2.2,
      by rw [hm2]; exact hA1.write hp (by unfold frameBytes; omega_using [hn]) _, R2'⟩

theorem off_zero (p : Addr) : off p 0 = p := BitVec.add_zero p

/-- The private-key operation's arguments: its stack arguments in the
frame's first words, the rest of ours kept, and its registers. -/
theorem privArgs_ok {s : State} (hp : SPre tsH tsG s) {u : State} (L : Lay u (fb s) (stackArg s 14)) (hrd : u.rd = s.rd)
    (hA : ArgsKept s u.mem) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem (fb s) (stackArg s 14) V W)
    (h16 : W 16 = s.gpr .rdi) (h17 : W 17 = s.gpr .rcx) (h18 : W 18 = s.gpr .rdx) (h19 : W 19 = s.gpr .r8)
    (h20 : W 20 = s.gpr .r9) (h22 : W 22 = stackArg s 15) :
    WP isa (.block privArgs) u fun u' => Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] u u' ∧
      Lay u' (fb s) (stackArg s 14) ∧
      (∃ W', Rep u'.mem (fb s) (stackArg s 14) V W' ∧ (∀ i < 14, W' i = pArg s i) ∧ (∀ i < nW, 14 ≤ i → W' i = W i)) ∧
      u'.gpr .rdi = s.gpr .rdi ∧ u'.gpr .rsi = s.gpr .rcx ∧ u'.gpr .rdx = s.gpr .rdx ∧ u'.gpr .rcx = s.gpr .rcx ∧
      u'.gpr .r8 = s.gpr .r8 ∧ u'.gpr .r9 = s.gpr .r9 := by
  rw [privArgs_eq, WP.block_append_iff]
  refine WP.mono (cpys_ok hp 10 (le_refl _) u L hrd hA R) fun u1 ⟨k1, L1, _, R1⟩ => ?_
  have G' := L1.geo
  set W1 := cpW s W 10 with hW1
  obtain c : ∀ i, 14 ≤ i → W1 i = W i := fun i hi => by simp only [hW1, cpW]; rw [ifn (by omega_using [hi])]
  have hs : u1.mem.readW (off (fb s) sScr) 64 = stackArg s 14 := L1.slot
  set S := stackArg s 14
  obtain Ra := R1.wf G' (k := 0) (by decide) (off S oEm)
  obtain Rb := Ra.wf G' (k := 1) (by decide) (s.gpr .rcx)
  obtain Rc := Rb.wf G' (k := 12) (by decide) (off S oRsa)
  obtain Rd := Rc.wf G' (k := 13) (by decide) (stackArg s 15 - BitVec.ofNat 64 1024)
  simp only [Nat.reduceMul, off_zero] at Ra Rb Rc Rd
  obtain hst0 : InRegions u1.wr (fb s) 8 := by simpa only [off_zero] using L1.st (d := 0) (by decide)
  obtain f1 : (u1.mem.writeW (fb s) (off S oEm)).readW (off (fb s) sK) 64 = s.gpr .rcx := by
    rw [Ra.rd (d := sK) 17 rfl (by decide)]; simp [upd, c, h17]
  obtain f2 : ((u1.mem.writeW (fb s) (off S oEm)).writeW (off (fb s) 8) (s.gpr .rcx)).readW
      (off (fb s) sScr) 64 = S := by
    rw [Rb.rd (d := sScr) 21 rfl (by decide)]; simp only [upd, Nat.reduceEqDiff, ite_false]
    exact (R1.rd (d := sScr) 21 rfl (by decide)).symm.trans hs
  obtain f3 : (((u1.mem.writeW (fb s) (off S oEm)).writeW (off (fb s) 8) (s.gpr .rcx)).writeW
      (off (fb s) 96) (off S oRsa)).readW (off (fb s) sScrLen) 64 = stackArg s 15 := by
    rw [Rc.rd (d := sScrLen) 22 rfl (by decide)]; simp [upd, c, h22]
  set m4 := ((((u1.mem.writeW (fb s) (off S oEm)).writeW (off (fb s) 8) (s.gpr .rcx)).writeW
      (off (fb s) 96) (off S oRsa)).writeW (off (fb s) 104) (stackArg s 15 - BitVec.ofNat 64 1024)) with hm4
  obtain g : ∀ k, 14 ≤ k → k < nW → m4.readW (off (fb s) (8 * k)) 64 = W k := fun k hk hk' => by
    refine (Rd.fr k hk').trans ?_; simp only [upd]; rw [ifn (by omega_using [hk]), ifn (by omega_using [hk]),
        ifn (by omega_using [hk]), ifn (by omega_arith), c k hk]
  refine WP.mono (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] (Q := fun u' => u'.mem = m4 ∧
      u'.gpr .rdi = s.gpr .rdi ∧ u'.gpr .rsi = s.gpr .rcx ∧ u'.gpr .rdx = s.gpr .rdx ∧ u'.gpr .rcx = s.gpr .rcx ∧
      u'.gpr .r8 = s.gpr .r8 ∧ u'.gpr .r9 = s.gpr .r9) ?_ rfl) fun u2 ⟨⟨hm, h1, h2, h3, h4, h5, h6⟩, k2⟩ => ?_
  · xrun [privTail, scr, List.cons_append, List.nil_append, ea_sp, L1.rsp, L1.ld (d := sScr) (by decide), hs,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oEm < 2 ^ 31 by decide), off_plus, hst0,
      L1.st (d := 8) (by decide), L1.st (d := 96) (by decide), L1.st (d := 104) (by decide),
      L1.ld (d := sK) (by decide), L1.ld (d := sScrLen) (by decide), L1.ld (d := sOut) (by decide),
      L1.ld (d := sN) (by decide), L1.ld (d := sE) (by decide), L1.ld (d := sEl) (by decide), f1, f2, f3,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oRsa < 2 ^ 31 by decide),
      VG.Proof.MlKem.X86_64.sx_ofNat (show 1024 < 2 ^ 31 by decide),
      show m4.readW (off (fb s) sOut) 64 = s.gpr .rdi from (g 16 (by decide) (by decide)).trans h16,
      show m4.readW (off (fb s) sK) 64 = s.gpr .rcx from (g 17 (by decide) (by decide)).trans h17,
      show m4.readW (off (fb s) sN) 64 = s.gpr .rdx from (g 18 (by decide) (by decide)).trans h18,
      show m4.readW (off (fb s) sE) 64 = s.gpr .r8 from (g 19 (by decide) (by decide)).trans h19,
      show m4.readW (off (fb s) sEl) 64 = s.gpr .r9 from (g 20 (by decide) (by decide)).trans h20]
    rw [show BitVec.signExtend 64 (1024 : BitVec 32) = BitVec.ofNat 64 1024 by decide]
    exact ⟨rfl, (g 16 (by decide) (by decide)).trans h16, (g 17 (by decide) (by decide)).trans h17,
      (g 18 (by decide) (by decide)).trans h18, (g 17 (by decide) (by decide)).trans h17,
      (g 19 (by decide) (by decide)).trans h19, (g 20 (by decide) (by decide)).trans h20⟩
  obtain R2 : Rep u2.mem (fb s) S V _ := hm ▸ Rd
  refine ⟨(k1.trans k2).mono (by decide), L1.of_rep' R1 R2 (by simp [upd]) (k2.gpr (by decide)) k2.2.2,
    ⟨_, R2, fun i hi => ?_, fun i hi h14 => ?_⟩, h1, h2, h3, h4, h5, h6⟩
  · simp only [upd, hW1, cpW, pArg]
    rcases (show i = 0 ∨ i = 1 ∨ (2 ≤ i ∧ i < 12) ∨ i = 12 ∨ i = 13 by omega_using [hi]) with h | h | h | h | h
    · subst h; simp; rfl
    · subst h; simp
    · rw [ifn (by omega_using [h]), ifn (by omega_using [h]), ifn (by omega_using [h]), ifn (by omega_using [h]), ifp h]
      match i, h with
      | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ => rfl
    · subst h; simp; rfl
    · subst h; simp
  · simp only [upd]
    rw [ifn (by omega_arith), ifn (by omega_using [h14]), ifn (by omega_arith), ifn (by omega_using [h14]), c i h14]

end VG.Proof.RsaPss.X86_64

end

end

/-! ### `RsaPss.X86_64.SignFail`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS signing on x86-64: refusing

`signFail` writes zeros to `out` and returns 0 (`signFail_ok`), changing
nothing else of the working space or the frame.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)

/-- `Rep` across changes outside the working space and the frame. -/
theorem Rep.of_outside {m m' : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep m F S V W)
    {O : Region} (hm : ∀ x, ¬ O.Contains x 1 → m' x = m x) (hS : O.Disjoint ⟨S, oRsa⟩)
    (hF : O.Disjoint ⟨F, frameBytes⟩) (G : Geo F S) : Rep m' F S V W where
  scr o ho := by
    rw [hm _ fun h => hS _ h (Offset.contains_base _ (by omega_using [ho]) (by unfold oRsa at *; omega_using [ho])), R.scr o ho]
  fr k hk := by
    rw [← R.fr k hk]
    refine Mem.readW_congr fun i hi => hm _ fun h => hF _ h ?_
    have := G.Fw
    rw [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact Offset.contains_base _ (by unfold nW frameBytes at *; omega_using [hk, hi]) (by unfold nW frameBytes at *; omega_using [hk, hi])

structure ZI (u₀ : State) (p : Addr) (j : Nat) (v : State) : Prop where
  keep : Keep [.r8] u₀ v
  r8 : v.gpr .r8 = BitVec.ofNat 64 j
  mem : ∀ x, v.mem x = if (⟨p, j⟩ : Region).Contains x 1 then 0 else u₀.mem x

/-- Zeros to the `n` bytes at `p` (`rdi`), a byte at a time. -/
theorem zeroOut_ok {u₀ : State} {p : Addr} {n : Nat} {cnt : Src} (hs : StepOk cnt n u₀ [.r8]) (hn : 0 < n)
    (hpn : p.toNat + n ≤ 2 ^ 64) (hw : (⟨p, n⟩ : Region) ∈ u₀.wr)
    (hdi : u₀.gpr .rdi = p) (hax : u₀.gpr .rax = 0) (h8 : u₀.gpr .r8 = BitVec.ofNat 64 0) :
    WP isa (byteLoop [.store8 (ix .rdi .r8) .rax] cnt) u₀ fun u' => Keep [.r8] u₀ u' ∧
      ∀ x, u'.mem x = if (⟨p, n⟩ : Region).Contains x 1 then 0 else u₀.mem x := by
  refine WP.mono (byteLoop_ok hn hs (ZI u₀ p) ?_ (u := u₀)
    ⟨Keep.refl _ _, h8, fun x => by simp [Region.Contains]⟩) fun u' I => ⟨I.keep, I.mem⟩
  intro j hj v I
  have hdv : v.gpr .rdi = p := (I.keep.gpr (by decide)).trans hdi
  have hav : v.gpr .rax = 0 := (I.keep.gpr (by decide)).trans hax
  have hea : p + BitVec.ofNat 64 j + BitVec.ofNat 64 0 = p + BitVec.ofNat 64 j := by
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
  have hin : InRegions v.wr (p + BitVec.ofNat 64 j) 1 :=
    ⟨_, I.keep.2.2 ▸ hw, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hpn, hj])⟩
  refine WP.mono (WP.keep [] (Q := fun v' => v'.gpr .r8 = BitVec.ofNat 64 j ∧
      v'.mem = v.mem.writeW (p + BitVec.ofNat 64 j) (0 : Byte)) ?_ rfl)
    fun v' ⟨⟨h8', hm⟩, k⟩ => ⟨(I.keep.trans k).mono (by decide), h8', fun v'' k' hm' h8'' => ?_⟩
  · xrun [ea_ix, hdv, I.r8, hea, hin, hav]
    rfl
  refine ⟨(I.keep.trans (k.trans k')).mono (by decide), h8'', fun x => ?_⟩
  rw [hm', hm, VG.WriteBytes.writeW8_apply, I.mem x]
  have hx : (x - p).toNat < 2 ^ 64 := (x - p).isLt
  by_cases he : x = p + BitVec.ofNat 64 j
  · subst he
    rw [ifp rfl]
    exact (ifp (show (⟨p, j + 1⟩ : Region).Contains (p + BitVec.ofNat 64 j) 1 from
      Offset.contains_base _ (by omega_using []) (by omega_using [hpn, hj])) _ _).symm
  · rw [ifn he]
    have hne : (x - p).toNat ≠ j := fun h => he (by
      rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel])
    have iff : (⟨p, j + 1⟩ : Region).Contains x 1 ↔ (⟨p, j⟩ : Region).Contains x 1 := by
      simp only [Region.Contains]; omega_using [hne]
    by_cases h1 : (⟨p, j⟩ : Region).Contains x 1
    · rw [ifp h1, ifp (iff.mpr h1)]
    · rw [ifn h1, ifn (fun h => h1 (iff.mp h))]

/-- Zeros to `out` (`k` bytes) and 0 in `rax`. -/
theorem signFail_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {out : Addr} {k : Nat} (ho : W 16 = out) (hk : W 17 = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk2 : k ≤ 1024) (hw : (⟨out, k⟩ : Region) ∈ u.wr) (hpn : out.toNat + k ≤ 2 ^ 64)
    (hS : (⟨out, k⟩ : Region).Disjoint ⟨S, oRsa⟩) (hF : (⟨out, k⟩ : Region).Disjoint ⟨F, frameBytes⟩) :
    WP isa signFail u fun u' => Lay u' F S ∧ Keep [.rdi, .r10, .rax, .r8] u u' ∧ Rep u'.mem F S V W ∧
      u'.gpr .rax = 0 ∧ Spec.Rsa.bytesAt u'.mem out k = List.replicate k 0 ∧
      (∀ x, ¬ (⟨out, k⟩ : Region).Contains x 1 → u'.mem x = u.mem x) := by
  refine WP.seq (WP.mono (WP.keep [.rdi, .r10, .rax, .r8] (Q := fun v => v.gpr .rdi = out ∧
      v.gpr .r10 = BitVec.ofNat 64 k ∧ v.gpr .rax = 0 ∧ v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl)
    fun v ⟨⟨h₁, h₁₀, h₂, h₃, hm⟩, hkv⟩ => ?_)
  · xrun [signFail, ea_sp, L.rsp, L.ld (d := sOut) (by decide), L.ld (d := sK) (by decide),
      R.rd (d := sOut) 16 rfl (by decide), R.rd (d := sK) 17 rfl (by decide), ho, hk]
  refine WP.mono (zeroOut_ok (stepR_ok (by omega_using [hk2]) v (show Reg.r10 ∉ [Reg.r8] by decide) (by decide) h₁₀)
    (by omega_using [hk1]) hpn (by rw [hkv.2.2]; exact hw) h₁ h₂ h₃) fun w ⟨kw, hmw⟩ => ?_
  have hout : ∀ x, ¬ (⟨out, k⟩ : Region).Contains x 1 → w.mem x = u.mem x := fun x hx => by
    rw [hmw, ifn hx, hm]
  have Rw : Rep w.mem F S V W := R.of_outside hout hS hF L.geo
  refine ⟨L.of_rep R Rw ((kw.gpr (by decide)).trans (hkv.gpr (by decide))) (kw.2.2.trans hkv.2.2),
    (hkv.trans kw).mono (by decide), Rw, (kw.gpr (by decide)).trans h₂, ?_, hout⟩
  simp only [Spec.Rsa.bytesAt]
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
  rw [hmw, ifp (Offset.contains_base _ (by simp at h₁; omega_using [h₁]) (by simp at h₁; omega_using [hk2, h₁]))]

end VG.Proof.RsaPss.X86_64

end

end

/-!
# RSASSA-PSS signing on x86-64: correctness

`sign_body`: from the entry state, the body of the frame leaves `out` and
`rax` as `RsaPss.sign` says, with the callee-saved registers restored.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (chkContract)

variable {tsH tsG : List FnTable}

theorem bytesAt_cons (m : Mem) (p : Addr) {k : Nat} (hk : 1 ≤ k) :
    Spec.Rsa.bytesAt m p k = m p :: Spec.Rsa.bytesAt m (p + 1) (k - 1) := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega_arith⟩
  simp only [Spec.Rsa.bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_sub_cancel]
  refine congrArg₂ _ (by simp) (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp, BitVec.add_assoc]
  rw [show (1 : Addr) + BitVec.ofNat 64 i = BitVec.ofNat 64 (i + 1) by
    rw [BitVec.add_comm, ← BitVec.ofNat_add_ofNat]; rfl]

/-- `Rep` across a change that keeps the frame and our working space. -/
theorem Rep.of_keep {m m' : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep m F S V W)
    (G' : Geo F S) (hk : ∀ x, ((⟨F, frameBytes⟩ : Region).Contains x 1 ∨ (⟨S, oRsa⟩ : Region).Contains x 1) →
      m' x = m x) : Rep m' F S V W where
  scr o ho := by rw [hk _ (.inr (Offset.contains_base _ (by omega_arith) (by unfold oRsa at *; omega_arith))), R.scr o ho]
  fr k hk' := by
    rw [← R.fr k hk']
    refine Mem.readW_congr fun i hi => hk _ (.inl ?_)
    have := G'.Fw
    rw [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact Offset.contains_base _ (by unfold nW frameBytes at *; omega_arith) (by unfold nW frameBytes at *; omega_arith)

/-- Memory changed only in the frame. -/
theorem frame_wrR {s : State} {m : Mem} (h : Frame [frR s] s.mem m) : Frame (wrR s) s.mem m :=
  h.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_sub s⟩

/-- Memory changed only in the writable regions and below the frame. -/
theorem frame_keep {s u v : State} (hp : SPre tsH tsG s) (hw : u.wr = frR s :: s.wr) (hsp : u.gpr .rsp = fb s)
    (hM : Frame (wrR s) s.mem u.mem)
    (hk : ∀ a, (∀ r ∈ u.wr, ¬ r.Contains a 1) → ¬ (below (u.gpr .rsp) 16).Contains a 1 → v.mem a = u.mem a) :
    Frame (wrR s) s.mem v.mem := by
  intro x hx
  refine (hk x (fun r hr hc => ?_) (fun hc => ?_)).trans (hM x hx)
  · rw [hw, hp.hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hx _ (List.mem_cons_self ..) (frame_sub s x hc)
    · exact hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hc
    · exact hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) hc
  · rw [hsp] at hc; exact hx _ (List.mem_cons_self ..) (ret_sub s x hc)

/-- The outcome `signK.post` asks for, with the hash functions `H` and `G`
the tables name. -/
def signOut (H G : Spec.Mgf1.Hash) (s : State) : Spec.Rsa.Outcome :=
  Spec.RsaPss.sign H G (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 10) H.len)
    (Spec.Rsa.bytesAt s.mem (stackArg s 12) (stackArg s 13).toNat)

/-- Before the epilogue: the outcome written, the saved registers in their
slots. -/
structure SDone (s t : State) : Prop where
  L : Lay t (fb s) (stackArg s 14)
  wr : t.wr = frR s :: s.wr
  cs : ∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r
  rbx : t.mem.readW (off (fb s) sRbx) 64 = s.gpr .rbx
  rbp : t.mem.readW (off (fb s) sRbp) 64 = s.gpr .rbp
  r12 : t.mem.readW (off (fb s) sR12) 64 = s.gpr .r12
  out : ∀ H G, Spec.MdHashTable.hashAt 64 s.mem (stackArg s 16) = some H →
    Spec.MdHashTable.hashAt 64 s.mem (stackArg s 17) = some G →
    Spec.Rsa.writtenOutcome t.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((t.gpr .rax).setWidth 32) (signOut H G s)
  /-- MXCSR's control bits. -/
  mx : t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10

theorem fail_done {s t : State} (hp : SPre tsH tsG s) {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay t (fb s) (stackArg s 14)) (R : Rep t.mem (fb s) (stackArg s 14) V W) (hw : t.wr = frR s :: s.wr)
    (hcs : ∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r)
    (h16 : W 16 = s.gpr .rdi) (h17 : W 17 = s.gpr .rcx) (h41 : W 41 = s.gpr .rbx) (h42 : W 42 = s.gpr .rbp)
    (h43 : W 43 = s.gpr .r12) (hinv : ∀ H G, Spec.MdHashTable.hashAt 64 s.mem (stackArg s 16) = some H →
      Spec.MdHashTable.hashAt 64 s.mem (stackArg s 17) = some G → signOut H G s = .invalid)
    (hmx : t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10) :
    WP isa signFail t (SDone s) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hout : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region) ∈ t.wr := by
    rw [hw, hp.hwr, ← hp.hsi]; simp
  have hO : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint (stkR s) := by rw [← hp.hsi]; exact hp.dKo.symm
  refine WP.mono_mx (by decide) (signFail_ok L R (out := s.gpr .rdi) (k := (s.gpr .rcx).toNat) h16
    (by rw [h17, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega_arith) hk2 hout (by rw [← hp.hsi]; exact hp.wO)
    ((by rw [← hp.hsi]; exact hp.dOs : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint
      ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩).sub_right (Region.sub_prefix (by have := hp.hsl; unfold oRsa; omega_arith)))
    (hO.sub_right (frame_sub s))) fun t' ⟨L', k', R', hax, hz, _⟩ hm => ?_
  refine ⟨L', k'.2.2.trans hw, fun r hr => (k'.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> decide)).trans
    (hcs r hr), ?_, ?_, ?_, ?_, by rw [hm]; exact hmx⟩
  · rw [R'.rd (d := sRbx) 41 rfl (by decide), h41]
  · rw [R'.rd (d := sRbp) 42 rfl (by decide), h42]
  · rw [R'.rd (d := sR12) 43 rfl (by decide), h43]
  · intro H G hH hG; rw [hinv H G hH hG]; exact ⟨by rw [hax]; rfl, hz⟩

/-- Stack arguments, kept where the function does not write. -/
theorem argsKept_of {s : State} (hp : SPre tsH tsG s) {m : Mem} (hM : Frame (wrR s) s.mem m) : ArgsKept s m := by
  intro j hj
  refine hM.readW (r := ⟨stackArgAddr s 0, 144⟩) ?_ (in_apart hp.dKa hp.dOa hp.dsa.symm) (by decide)
  rw [show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
    simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega_arith]
  have := hp.sp2
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

variable {H : Impl.Pbkdf2.Md.X86_64.Hash} (hH : Pbkdf2.Md.X86_64.HashOK H) (K : Pbkdf2.Md.X86_64.Callees H)

/-- The state after the frame's pop. -/
def freedF (s₂ : State) : State :=
  { s₂.setReg .rsp (s₂.gpr .rsp + BitVec.ofNat 64 frameBytes) with wr := s₂.wr.tail }

/-- The frame, whose bytes hold whatever they hold once released (`alloc_frame_ok`). -/
theorem wp_frame {body : Prog isa} {s : State} {Q : State → Prop} (hsp : frameBytes ≤ (s.gpr .rsp).toNat)
    (hb : WP isa body (allocState frameBytes s) fun s₂ => s₂.gpr .rsp = fb s ∧
      s₂.wr = (allocState frameBytes s).wr ∧ ∀ m u, Frame [⟨fb s, frameBytes⟩] s₂.mem m →
        Q { freedF s₂ with mem := m, unknowns := u }) :
    WP isa (.frame (.alloc frameBytes) body (.free frameBytes)) s Q :=
  alloc_frame_ok (by decide) hsp hb

theorem zext8 (b : Byte) : BitVec.setWidth 64 b = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- The modulus' first byte. -/
theorem n0_ok {s t : State} (hp : SPre tsH tsG s) (L : Lay t (fb s) (stackArg s 14)) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep t.mem (fb s) (stackArg s 14) V W) (h18 : W 18 = s.gpr .rdx) (hrd : t.rd = s.rd)
    (hf : Frame (wrR s) s.mem t.mem) :
    WP isa (.block n0) t fun t' => Keep [.rsi, .rax] t t' ∧ t'.mem = t.mem ∧
      t'.gpr .rax = BitVec.ofNat 64 (s.mem (s.gpr .rdx)).toNat ∧
      t'.zf = some (decide ((s.mem (s.gpr .rdx)).toNat = 0)) := by
  have hk1 := hp.k1
  have hn : t.mem (s.gpr .rdx) = s.mem (s.gpr .rdx) := by
    have := hf.bytes (R := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩) (in_apart hp.dKn hp.dOn hp.dns) (by dsimp only; have := hp.wN; omega_arith)
      (i := 0) (by dsimp only; omega_arith)
    simpa using this
  have hin : InRegions (t.rd ++ t.wr) (s.gpr .rdx) 1 :=
    ⟨⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, hp.rdIn hrd (by simp), by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith⟩
  refine WP.mono (WP.keep [.rsi, .rax] (Q := fun t' => t'.mem = t.mem ∧
      t'.gpr .rax = BitVec.ofNat 64 (s.mem (s.gpr .rdx)).toNat ∧
      t'.zf = some (decide ((s.mem (s.gpr .rdx)).toNat = 0))) ?_ rfl) fun t' ⟨h, k⟩ => ⟨k, h⟩
  xrun [n0, ea_sp, ea_at0, L.rsp, L.ld (d := sN) (by decide), R.rd (d := sN) 18 rfl (by decide), h18, hin, hn]
  rw [zext8, BitVec.and_self, ofNat_beq_zero (by have := (s.mem (s.gpr .rdx)).isLt; omega_arith)]
  exact ⟨rfl, rfl⟩

theorem restore_ok {s t : State} (hp : SPre tsH tsG s) (D : SDone s t) :
    WP isa (.block restoreRegs) t fun t' => t'.gpr .rsp = fb s ∧ t'.wr = (allocState frameBytes s).wr ∧
      ∀ m u, Frame [⟨fb s, frameBytes⟩] t'.mem m →
        (∀ r ∈ calleeSaved, ({ freedF t' with mem := m, unknowns := u } : State).gpr r = s.gpr r) ∧ (signK tsH tsG).post s ({ freedF t' with mem := m, unknowns := u } : State) ∧
        ({ freedF t' with mem := m, unknowns := u } : State).mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  have hF := fb_toNat hp
  refine WP.mono_mx (by decide) (WP.keep [.rbx, .rbp, .r12] (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .rbx = s.gpr .rbx ∧
      t'.gpr .rbp = s.gpr .rbp ∧ t'.gpr .r12 = s.gpr .r12) ?_ rfl) fun t' ⟨⟨hm, h1, h2, h3⟩, k⟩ hmx => ?_
  · xrun [restoreRegs, ea_sp, D.L.rsp, D.L.ld (d := sRbx) (by decide), D.L.ld (d := sRbp) (by decide),
      D.L.ld (d := sR12) (by decide), D.rbx, D.rbp, D.r12]
  have hsp : t'.gpr .rsp = fb s := (k.gpr (by decide)).trans D.L.rsp
  refine ⟨hsp, k.2.2.trans D.wr, fun m u fm => ⟨fun r hr => ?_, ?_,
    by show t'.mxcsr.extractLsb' 6 10 = _; rw [hmx]; exact D.mx⟩⟩
  · show (freedF t').gpr r = s.gpr r
    simp only [freedF, State.setReg]
    by_cases hr' : r = .rsp
    · subst hr'; simp only [ite_true, hsp, fb]; exact BitVec.sub_add_cancel _ _
    · simp only [hr', ite_false]
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact absurd rfl hr'
      · exact h3
      · rw [k.gpr (by decide)]; exact D.cs _ (by simp)
      · rw [k.gpr (by decide)]; exact D.cs _ (by simp)
      · rw [k.gpr (by decide)]; exact D.cs _ (by simp)
  · intro H G hH hG
    show Spec.Rsa.writtenOutcome m _ _ ((t'.gpr .rax).setWidth 32) _
    have hsi := hp.hsi
    refine Proof.Rsa.writtenOutcome_frame fm (s.gpr .rcx).isLt (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      have := (hp.dKo.sub_left (frame_sub s)).symm
      rwa [hsi] at this) ?_
    rw [hm, k.gpr (show Reg.rax ∉ [Reg.rbx, .rbp, .r12] by decide)]
    exact D.out H G hH hG

end VG.Proof.RsaPss.X86_64
