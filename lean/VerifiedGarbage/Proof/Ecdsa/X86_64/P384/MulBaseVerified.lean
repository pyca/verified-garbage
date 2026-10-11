import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Verified
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.VerifiedAdx
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.MulBaseLit
import VerifiedGarbage.Proof.Weierstrass.PointFacts
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Spec.Weierstrass.MulBase

/-!
# `vg_p384_mul_base` on x86-64: `Verified`

The facts of `Spec.Weierstrass.MulBase.p384.mulBaseContract` for x86-64,
with the comb's tables (`Abi.withConsts p384.combConsts`), by name (`mbK`):
`ws` in `rdi`, the static `VG_P384_COMB` readable and holding the tables,
`p` and zero at their slots. `mulBaseFn_ok` gives `[k]G` in `R`'s slots,
which are `P`'s, the callee-saved registers restored, and every byte of `ws`
kept but those of its slots, `ACC`'s and the table of bits, the own working
space (`mb_correct`). The coordinates the specification decodes are the
proofs' (`dec_eq`, given Fermat's little theorem from the group law), and
`Represents` is `Rep`. Constant time by taint tracking with the static's
address public, as the signature (`mb_ct`).
-/

namespace VG.Proof.Ecdsa.X86_64.P384.MulBase

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P384

/-- P-384's curve of `Spec/Weierstrass/MulBase.lean`. -/
abbrev C : Spec.Weierstrass.MulBase.Curve := Spec.Weierstrass.MulBase.p384

/-- The configuration of `vg_p384_mul_base` (`adx` false) or `_adx`. -/
abbrev cfg (adx : Bool) : Cfg := if adx then p384x else p384

/-- The function's contract on x86-64. -/
def mbK : Contract isa where
  pre s :=
    let ws : Region := ⟨s.gpr .rdi, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [⟨s.syms "VG_P384_COMB", 8 * p384W.length⟩] ∧ s.wr = [ws] ∧ ret.Disjoint ws ∧
      (s.gpr .rdi).toNat + 8192 ≤ 2 ^ 64 ∧ TblHeld s [ws, ret] ∧ C.ConstsOk (s.gpr .rdi) s.mem
  post s s' := C.Result (mul (C.scalar (s.gpr .rdi) s.mem) (G C.W)) (s.gpr .rdi) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧
    s₁.syms "VG_P384_COMB" = s₂.syms "VG_P384_COMB"

/-- The coordinate at an offset below `2³²` is the number `wordsVal` reads. -/
theorem coordAt_eq (P : Spec.Weierstrass.Point.Curve) (m : Mem) (ws : Addr) {o : Nat} (ho : o < 2 ^ 32) :
    P.coordAt m ws o = wordsVal m ws o P.k := by
  unfold Spec.Weierstrass.Point.Curve.coordAt Spec.Weierstrass.Mont.numAt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
  exact read_eq_wordsVal m ws P.k o

/-- `Represents` is the proofs' `Rep`. -/
theorem represents_of_rep {W : Spec.Weierstrass.Curve} {X Y Z : Fe W} {P : Point W}
    (h : Rep W X Y Z P) : Spec.Weierstrass.MulBase.Represents X Y Z P := by
  cases P <;> exact h

/-- The result, for any curve, from the proofs' facts about the slots of
`P`: their numbers below `p` and representing `P` (`Rep`), and `Keeps`. -/
theorem result_of {M : Spec.Weierstrass.MulBase.Curve} (hFe : Point.Fermat M.toPoint.p)
    (h1 : (1 : Fin M.toPoint.p) ≠ 0) (hu : UnitMod M.toPoint.p (2 ^ (64 * M.k))) {m m' : Mem} {ws : Addr}
    {P : Point M.W} {n : Nat} (hn : n = M.k) (ho : M.pAt + 16 * M.k < 2 ^ 32)
    (hx : wordsVal m' ws M.pAt n < M.W.p) (hy : wordsVal m' ws (M.pAt + 8 * M.k) n < M.W.p)
    (hz : wordsVal m' ws (M.pAt + 16 * M.k) n < M.W.p)
    (hR : Rep M.W (toM M.W.p (2 ^ (64 * n)) (wordsVal m' ws M.pAt n))
      (toM M.W.p (2 ^ (64 * n)) (wordsVal m' ws (M.pAt + 8 * M.k) n))
      (toM M.W.p (2 ^ (64 * n)) (wordsVal m' ws (M.pAt + 16 * M.k) n)) P)
    (hK : M.Keeps ws m m') : M.Result P ws m m' := by
  subst hn
  have dq := Point.dec_eq M.toPoint h1 hFe hu
  have hk : M.toPoint.k = M.k := rfl
  have e8 : Spec.Weierstrass.Point.elemBytes M.k = 8 * M.k := rfl
  have e16 : 2 * (8 * M.k) = 16 * M.k := by omega
  refine ⟨?_, ?_, hK⟩
  · simp only [Spec.Weierstrass.Point.Curve.Below, Spec.Weierstrass.Point.Curve.pointAt, hk, e8, e16]
    rw [coordAt_eq _ _ _ (by omega), coordAt_eq _ _ _ (by omega), coordAt_eq _ _ _ (by omega), hk]
    exact ⟨hx, hy, hz⟩
  · simp only [Spec.Weierstrass.Point.Curve.pointAt, hk, e8, e16]
    rw [dq, dq, dq, coordAt_eq _ _ _ (by omega), coordAt_eq _ _ _ (by omega), coordAt_eq _ _ _ (by omega), hk]
    exact represents_of_rep hR

theorem cfg_n (adx : Bool) : (cfg adx).n = 6 := by cases adx <;> rfl
theorem cfg_C (adx : Bool) : (cfg adx).C = Spec.P384.curve := by cases adx <;> rfl
theorem cfg_sl (adx : Bool) (i : Nat) : (cfg adx).sl i = p384.sl i := by cases adx <;> rfl

theorem cfg_ok (hI : InvSounds) (adx : Bool) : CfgOk (cfg adx) := by
  cases adx
  · exact p384_ok hI
  · exact p384x_ok hI

theorem cfg_mulBase (adx : Bool) : MulBaseOk (cfg adx) := by
  cases adx
  · exact p384_mulBase
  · exact p384x_mulBase

theorem cfg_tbls (hT : CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (adx : Bool) : CombTbls (cfg adx) := by
  cases adx
  · exact p384_tbls hT
  · exact p384x_tbls hT

theorem cfg_combConsts (adx : Bool) : (cfg adx).combConsts = [("VG_P384_COMB", p384W)] := by
  cases adx
  · exact p384_combConsts
  · exact p384x_combConsts

/-- What `vg_p384_mul_base` writes, as offsets: `R`'s slots (`P`'s) and the
own working space. -/
theorem gWA_eq (adx : Bool) : gWA (cfg adx) = [(736, 48), (784, 48), (832, 48), (1024, 48),
    (1072, 48), (1120, 48), (1504, 48), (1168, 48), (1216, 48), (1264, 48), (1312, 48), (1360, 48),
    (1408, 48), (880, 48), (928, 48), (976, 48), (4048, 48), (1984, 48), (2224, 392), (1456, 48)] := by
  cases adx <;> decide

theorem keeps_of_unch {ws : Addr} {m m' : Mem} (adx : Bool) (hu : Unch ws (gWA (cfg adx)) m m') :
    C.Keeps ws m m' := by
  intro i hi hown hp
  have h8 : Spec.Weierstrass.Mont.wsBytes = 8192 := rfl
  refine hu _ fun w hw => ?_
  show (ws + BitVec.ofNat 64 i - ws).toNat < _ ∨ _ ≤ (ws + BitVec.ofNat 64 i - ws).toNat
  rw [Mem.sub_ofNat_toNat ws (by omega)]
  simp only [Spec.Weierstrass.MulBase.Curve.Own, Spec.Weierstrass.MulBase.Curve.slot,
    Spec.Weierstrass.MulBase.Curve.tmpAt, Spec.Weierstrass.MulBase.Curve.bitsAt,
    Spec.Weierstrass.MulBase.Curve.pAt, Spec.Weierstrass.MulBase.Curve.ptBytes, C,
    Spec.Weierstrass.MulBase.p384] at hown hp
  rw [gWA_eq] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega

/-- The sign's table facts, from the function's. -/
theorem tbls_of {s : State} (adx : Bool) (hrd : s.rd = [⟨s.syms "VG_P384_COMB", 8 * p384W.length⟩])
    (hwr : s.wr = [⟨s.gpr .rdi, 8192⟩]) (ht : TblHeld s [⟨s.gpr .rdi, 8192⟩, ⟨s.gpr .rsp, 8⟩]) :
    TblMem s (s.syms "VG_P384_COMB") ((cfg adx).combWords ⟨7, Impl.P384.p384Comb7, Impl.P384.p384Comb7Start,
      "VG_P384_COMB", false⟩) ∧ ∀ i < ((cfg adx).combWords ⟨7, Impl.P384.p384Comb7,
      Impl.P384.p384Comb7Start, "VG_P384_COMB", false⟩).length, ∀ b < 8,
      size ≤ ofs (s.gpr .rdi) (s.syms "VG_P384_COMB" + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b) := by
  obtain ⟨held, fit, hdw⟩ := ht
  have hcd : (cfg adx).comb = some ⟨7, Impl.P384.p384Comb7, Impl.P384.p384Comb7Start, "VG_P384_COMB", false⟩ := by
    cases adx <;> rfl
  refine tbl_of_held hcd (s₀ := s) ?_ (by rw [hwr]; simp) (fun r hr => ?_) (Unch.refl _ _ _)
  · rw [TblsHeld, cfg_combConsts, Abi.constRegions_cons, Abi.constRegions_nil, Sig.forall_mem_const_single]
    refine ⟨fun c hc => ?_, fit, fun r hr => hdw r ?_⟩
    · simp only [List.mem_singleton] at hc; subst hc; exact held
    · rw [hwr] at hr; simp only [List.mem_singleton] at hr; simp [hr]
  · rw [cfg_combConsts, Abi.constRegions_cons, Abi.constRegions_nil, List.mem_singleton] at hr
    rw [hrd, hr]; simp

/-- The comb of P-384's configurations. -/
abbrev comb7 : CombData := ⟨7, Impl.P384.p384Comb7, Impl.P384.p384Comb7Start, "VG_P384_COMB", false⟩

theorem cfg_comb (adx : Bool) : (cfg adx).comb = some comb7 := by cases adx <;> rfl

/-- P-384's prime, as `C`'s points and the group law have it: equal without
evaluating it, which unifying the two would. -/
theorem toPoint_p : C.toPoint.p = Spec.P384.curve.p := by
  simp only [Spec.Weierstrass.MulBase.Curve.toPoint]; rfl

theorem fermat_congr {p q : Nat} [NeZero p] [NeZero q] (h : p = q) (hf : Point.Fermat q) :
    Point.Fermat p := by
  subst h; exact hf

theorem mxcsr_ok (adx : Bool) : (cfg adx).mulBaseFn.allInstrs (fun i => !loadsMxcsr i) = true := by
  cases adx <;> lit_decide

theorem mb_correct (hL : Law Spec.P384.curve)
    (hT : CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start) (hI : InvSounds)
    (adx : Bool) (s : State) (hs : mbK.pre s) :
    ∃ t s', Exec isa (cfg adx).mulBaseFn s t s' ∧ abiPreserved s s' ∧ mbK.post s s' := by
  obtain ⟨hrd, hwr, hret, hfit, ht, hmp, hz⟩ := hs
  have hc := cfg_ok hI adx
  obtain ⟨d, hcd, hj, h6, hnc⟩ := cfg_mulBase adx (by cases adx <;> rfl)
  obtain rfl : d = comb7 := Option.some.inj (hcd.symm.trans (cfg_comb adx))
  have hS : Scr s (s.gpr .rdi) size := ⟨rfl, by rw [hwr]; simp, hfit⟩
  have hn := cfg_n adx
  have hmp' : wordsVal s.mem (s.gpr .rdi) ((cfg adx).sl MP) (cfg adx).n = (cfg adx).C.p := by
    rw [hn, cfg_sl, cfg_C]; rw [coordAt_eq _ _ _ (by decide)] at hmp; exact hmp
  have hz' : wordsVal s.mem (s.gpr .rdi) ((cfg adx).sl ZERO) (cfg adx).n = 0 := by
    rw [hn, cfg_sl]; rw [coordAt_eq _ _ _ (by decide)] at hz; exact hz
  obtain ⟨hTM, hout⟩ := tbls_of adx hrd hwr ht
  have W := mulBaseFn_ok hc.toBaseCfgOk h6 (cfg_C adx ▸ hL) (cfg_tbls hT adx) hcd hj hS hmp' hz' hTM hout
  rw [Code.inline_of_noCalls hnc] at W
  obtain ⟨t, s', he, g', sv', rd', wr', sy', U', M', L', R'⟩ := W
  refine ⟨t, s', he, abiPreserved_of_exec (mxcsr_ok adx) he ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sv' _ (by decide)
    · exact sv' _ (by decide)
    · exact g' _ (by rw [hn]; decide)
    · exact sv' _ (by decide)
    · exact sv' _ (by decide)
    · exact sv' _ (by decide)
    · exact sv' _ (by decide)
  · have F := (Exec.regions he hnc).2.2
    rw [hwr] at F
    exact F.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r rfl; exact hret) (by decide)
  · have hFe : Point.Fermat C.toPoint.p := fermat_congr toPoint_p (Point.fermat_of_law hL)
    have hodd : C.toPoint.p % 2 = 1 := by rw [toPoint_p]; decide +kernel
    have h1 : (1 : Fin C.toPoint.p) ≠ 0 := by decide +kernel
    have hu : UnitMod C.toPoint.p (2 ^ (64 * C.k)) := unitMod_pow_two hodd (64 * C.k)
    have hsc : C.scalar (s.gpr .rdi) s.mem = wordsVal s.mem (s.gpr .rdi) 1552 6 :=
      coordAt_eq _ _ _ (by decide)
    show C.Result (mul (C.scalar (s.gpr .rdi) s.mem) (G C.W)) (s.gpr .rdi) s.mem s'.mem
    rw [hsc]
    have hC : (cfg adx).C = C.W := by cases adx <;> rfl
    have L₁ := hC ▸ L'
    have R₁ := hC ▸ R'
    cases adx
    · exact result_of hFe h1 hu (by rfl) (by decide) (L₁ _ (by decide)) (L₁ _ (by decide)) (L₁ _ (by decide)) R₁
        (keeps_of_unch false U')
    · exact result_of hFe h1 hu (by rfl) (by decide) (L₁ _ (by decide)) (L₁ _ (by decide)) (L₁ _ (by decide)) R₁
        (keeps_of_unch true U')

/-- Constant time by taint tracking, `rdi`, `rsp` and the static's address
public. -/
theorem mb_ct (adx : Bool) : ConstantTime isa mbK.pre mbK.pub (cfg adx).mulBaseFn := by
  cases adx
  · exact VG.Taint.constantTime_mapBlocks (c' := mulBaseErased) (taintSym_eraseInv ["VG_P384_COMB"])
      (Taint.ofRegs [.rdi, .rsp]) rfl
      (fun _ _ _ _ ⟨h0, h1, hsy⟩ => ⟨Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h1
        · exact h0, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩)
      rfl (by taint_decide)
  · exact VG.Taint.constantTime_mapBlocks (c' := mulBaseErasedAdx) (taintSym_eraseInv ["VG_P384_COMB"])
      (Taint.ofRegs [.rdi, .rsp]) rfl
      (fun _ _ _ _ ⟨h0, h1, hsy⟩ => ⟨Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h1
        · exact h0, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩)
      rfl (by taint_decide)

/-- The memory of `satState`: P-384's `p` at `ws + 64` for `ws = 0x1000`,
zeros elsewhere below `0x100000`, and P-384's tables from there. -/
@[irreducible] def satMbMem : Mem := fun a =>
  if 0x1040 ≤ a.toNat ∧ a.toNat < 0x1070 then
    BitVec.ofNat 8 (Spec.P384.curve.p >>> (8 * (a.toNat - 0x1040)))
  else if a.toNat < 0x100000 then 0 else satMem a

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMbMem
  rd := [⟨0x100000, 337920⟩]
  wr := [⟨0x1000, 8192⟩]
  syms _ := 0x100000

theorem satMb_held : ∀ i < p384W.length,
    satMbMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = p384W.getD i 0 := by
  intro i hi
  rw [← satMem_held i hi]
  refine Mem.readW_congr fun j hj => ?_
  have hl := p384W_length
  have : (0x100000 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j).toNat = 0x100000 + 8 * i + j := by
    rw [hl] at hi; bv_omega
  unfold satMbMem
  split
  · omega
  split
  · omega
  rfl

theorem sat_consts : C.ConstsOk 0x1000 satMbMem := by
  unfold Spec.Weierstrass.MulBase.Curve.ConstsOk
  exact ⟨by decide +kernel, by decide +kernel⟩

theorem sat_pre : (C.mulBaseContract (X86_64.abi.withConsts p384.combConsts)).pre satState := by
  have held : ∀ i < p384W.length, satState.mem.readW (satState.syms "VG_P384_COMB" +
      BitVec.ofNat 64 (8 * i)) 64 = p384W.getD i 0 := satMb_held
  sig_pre [Spec.Weierstrass.MulBase.Curve.mulBaseContract, Spec.Weierstrass.MulBase.sig,
    X86_64.abi, X86_64.argRegs, p384_combConsts, Abi.withConsts, p384_constRegions, Abi.constsHeld,
    stackBelow]
  sig_and_intros
  all_goals first | exact Region.disjoint_of_sep (by decide) | exact held | exact sat_consts |
    (rw [p384W_length]; rfl) | rfl | decide

theorem implies : mbK.Implies (C.mulBaseContract (X86_64.abi.withConsts p384.combConsts)) where
  pre s h := by
    sig_pre [Spec.Weierstrass.MulBase.Curve.mulBaseContract, Spec.Weierstrass.MulBase.sig,
      X86_64.abi, X86_64.argRegs, p384_combConsts, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
      stackBelow] at h
    obtain ⟨hd, hheld, hfit, hdw, hdr, ht, hw, hret, hws, hco⟩ := h
    refine ⟨?_, hw, hret, hws, ⟨hheld, hfit, fun r hr => ?_⟩, hco⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hdr
  post := by
    sig_implies_post [Spec.Weierstrass.MulBase.Curve.mulBaseContract, Spec.Weierstrass.MulBase.sig,
      X86_64.abi, X86_64.argRegs, p384_combConsts, Abi.withConsts, mbK]
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Weierstrass.MulBase.Curve.mulBaseContract, Spec.Weierstrass.MulBase.sig,
      X86_64.abi, X86_64.argRegs, p384_combConsts, Abi.withConsts] at h
    exact ⟨h.1, h.2.2, h.2.1⟩
  sat := ⟨satState, sat_pre⟩

theorem mb_verified (hL : Law Spec.P384.curve)
    (hT : CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start) (hI : InvSounds)
    (adx : Bool) :
    Verified X86_64.target (cfg adx).mulBaseFn (C.mulBaseContract (X86_64.abi.withConsts p384.combConsts)) :=
  Verified.of_correct (mb_correct hL hT hI adx) (mb_ct adx) implies

end VG.Proof.Ecdsa.X86_64.P384.MulBase
