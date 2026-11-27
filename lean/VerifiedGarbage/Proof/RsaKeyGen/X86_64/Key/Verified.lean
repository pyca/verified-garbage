module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.CTLcm
public import VerifiedGarbage.Proof.RsaKeyGen.Contract
import VerifiedGarbage.Proof.Rsa.X86_64.InvInstance
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.CTD
import VerifiedGarbage.Proof.Rsa.X86_64.CvCT
import VerifiedGarbage.Proof.Rsa.X86_64.CvFail
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.CTLcm
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.CTD
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvFail
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.Loops
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Lcm
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Lcm
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Contract
meta import VerifiedGarbage.Proof.RsaKeyGen.Contract
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Contract

/-! ### `RsaKeyGen.X86_64.Key.Implies`, which only this module used -/

section

/-!
# An RSA key from its primes on x86-64: the shared contract implies `keyCtr`
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64

theorem stackArgs_twelve (s : State) :
    List.map (stackArg s) (List.range 12) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11] := rfl

/-- A state meeting the precondition: 32-byte primes, a one-byte `e`, the
stack arguments at `0x9008`. -/
def keySat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 64 | .r8 => 0x3000 | .r9 => 32
    | .rsp => 0x9000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x9060 then 0x20
    else if a = 0x9009 then 0x40 else if a = 0x9010 then 0x20 else if a = 0x9019 then 0x50 else
    if a = 0x9020 then 0x20 else if a = 0x9029 then 0x60 else if a = 0x9030 then 0x20 else
    if a = 0x9039 then 0x70 else if a = 0x9040 then 0x20 else if a = 0x9049 then 0x80 else
    if a = 0x9050 then 0x01 else if a = 0x905a then 0x01 else if a = 0x9061 then 0x04 else 0
  rd := [⟨0x8000, 1⟩, ⟨0x9008, 96⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩, ⟨0x3000, 32⟩, ⟨0x4000, 32⟩, ⟨0x5000, 32⟩, ⟨0x6000, 32⟩, ⟨0x7000, 32⟩,
    ⟨0x10000, 8448⟩]

theorem key_implies : keyCtr.Implies (Proof.RsaKeyGen.keyContract abi) where
  pre := by
    intro s h
    sig_pre [Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig, abi, argRegs, keyCtr, keyPre,
      stackArgs_twelve, List.append_eq, List.range, List.range.loop] at h
    sig_pre [Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig, abi, argRegs, keyCtr, keyPre,
      stackArgs_twelve, List.append_eq, List.range, List.range.loop] at h
    sig_split h
    sig_reduce [Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig, abi, argRegs, keyCtr, keyPre,
      stackArgs_twelve, List.append_eq, List.range, List.range.loop]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by
    intro s s' _ h
    sig_post [Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig, abi, argRegs, keyCtr, keyPre, keyPost, keyRes,
      keyOuts, stackArgs_twelve, List.append_eq, List.range, List.range.loop]
    sig_reduce [Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig, abi, argRegs, keyCtr, keyPre, keyPost, keyRes,
      keyOuts, stackArgs_twelve, List.append_eq, List.range, List.range.loop] at h
    sig_simp [Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig, abi, argRegs, keyCtr, keyPre, keyPost, keyRes,
      keyOuts, stackArgs_twelve, List.append_eq] [] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨h1, ?_⟩
    revert h2
    simp only [arg]
    generalize Proof.RsaKeyGen.keyOp _ _ _ _ = r
    rcases r with (f | ys) | u <;> first | exact id | simp
  pub := by
    intro s₁ s₂ _ _ h
    sig_pub [Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig, abi, argRegs, keyCtr, keyPub,
      keyLeak, keyRes, stackArgs_twelve, List.append_eq, List.range, List.range.loop] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h
    refine ⟨hdi, hsi, hdx, hcx, h8, h9, hsp, fun i hi => ?_, hl⟩
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11
      by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact a10
    · exact a11
  sat := by sig_implies_sat [Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig, abi, argRegs,
    keyCtr, keyPre, stackArgs_twelve, List.append_eq] [keySat, stackArg, stackArgAddr, Mem.readW, Mem.read] using keySat

end VG.Proof.RsaKeyGen.X86_64.Key

end

end

/-! ### `RsaKeyGen.X86_64.Key.CTTail`, which only this module used -/

section

/-!
# An RSA key from its primes on x86-64: constant time, the tail

`smallMask`; then `qInv`, `dP`, `dQ`, `n` and the final mask (keeping a mask
in `kOk`, which `storeA` needs), the stores and the exit; or the zeros and
the exit. The stores and the zeros write the outputs, among them `p` and
`q`, so from there on the runs are related by what the header and the
working space say (`EG`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Bignum.X86_64.Public (exit)

/-! ## `smallMask` -/

abbrev smallBlk : List Instr :=
  base aC .rbx ++ ([.mov .rax (.reg .r12), .shift .shr .rax 1, .mov32 .rdx (.imm 1), .store (ix .rbx .rax) .rdx] :
    List Instr)

theorem smallBlk_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (L : KLens I) :
    WP isa (.block (ws ++ smallBlk)) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aC] s.mem t.mem := by
  have hW := L.W
  have hn := h.ws.scr.nowrap
  have hw1 := h.ws.w1
  have hw2 := h.ws.w2
  have sC := h.ws.sl (j := aC) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono h.ws.ws_ok fun u₁ ⟨h12, h9, mu₁, ku₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aC (r := .rbx) (by decide) ((ku₁.gpr (by decide)).trans h.ws.rdi) h9)
    fun u₂ ⟨hbx, mu₂, ku₂⟩ => ?_
  have hs₂ := h.ws.scr.congr (ku₁.trans ku₂).2.2
  have h12₂ : u₂.gpr .r12 = BitVec.ofNat 64 I.W := (ku₂.gpr (by decide)).trans h12
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.mem = s.mem.writeW (off I.B (slot I.W aC + 8 * (I.pl / 8)))
      (1 : BitVec 64)) (by
    have ew : BitVec.ofNat 64 I.W >>> 1 = BitVec.ofNat 64 (I.pl / 8) := by
      rw [ofNat_shr1 (by omega_using [hw2])]; congr 1; omega_using [hW]
    xrun [State.ea, ix, h12₂, ew, addr0 hbx rfl, hs₂.st (d := slot I.W aC + 8 * (I.pl / 8)) (by omega_using [hW, sC]), mu₂, mu₁]
    rfl) rfl) fun t ⟨hm, k⟩ => ?_
  have o := writeW_outside s.mem I.B (1 : BitVec 64) (d := slot I.W aC + 8 * (I.pl / 8)) (by omega_using [hW, hn, sC])
  rw [← hm] at o
  have f := KF.arr1 (I := I) (j := aC) o (by omega_using []) (by omega_using [hW])
  exact ⟨h.step f (all_mut_arr (by decide)) ((ku₁.trans ku₂).trans k) (by decide), f⟩

theorem smallMask_eq : smallMask = constA 1 ++ (([.block (ws ++ smallBlk)] : List (Prog isa)) ++ (ltA aDd aC ++
    ([.block [.alu .and .rbp (.mem (hdr kOk)), .alu .test .rbp (.reg .rbp)]] : List (Prog isa)))) := by
  simp only [smallMask, smallBlk, List.append_assoc]

theorem smallMask_ct : RelCT isa (Two (KG NF)) (seqs smallMask) (Two (KG NF)) := by
  rw [smallMask_eq]
  refine rs_app (by simp [constA]) (by simp) (constA_ct 1 (stab_nf _ _) (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp) (by simp [ltA]) (show RelCT isa _ (seqs [.block (ws ++ smallBlk)]) _ from
    kg_wsb (by taint_decide) fun I _ s h L _ => WP.mono (smallBlk_k h L) fun t ⟨ht, _⟩ => ⟨ht, trivial⟩) ?_
  refine rs_app (by simp [ltA]) (by simp) (ltA_ct (G := NF) (by decide) (by decide)
    (fun _ _ _ _ _ _ _ _ => trivial) (by taint_decide)) ?_
  exact kg_rdi (by taint_decide) fun I _ s h _ _ => by
    have hld := h.ws.scr.ld (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega_using [this])
    refine WP.mono (WP.keep [.rbp] (Q := fun t => t.mem = s.mem) (by xrun [State.ea, hdr, h.ws.rdi, hdrOff, hld])
      rfl) fun t ⟨hm, k⟩ => ⟨h.same hm k (by decide), trivial⟩

/-! ## The final mask -/

/-- `finalMask`'s first part, after `ws`: the masks of `n`'s top bit and `kOk`. -/
abbrev fm1 : List Instr :=
  base aQt .rbx ++ ([.mov .rax (.mem (ix .rbx .r12 (-8))), .shift .shr .rax 63, .mov32 .rdx (.imm 0),
    .alu .sub .rdx (.reg .rax), .alu .and .rdx (.mem (hdr kOk)), .mov .rcx (.reg .rdx)] : List Instr)

/-- `finalMask`'s second part: and `p` odd. -/
abbrev fm2 : List Instr := oddMask aPa ++ ([.alu .and .rcx (.reg .rax)] : List Instr)

/-- `finalMask`'s last part: and `q` odd and `e` valid, into `kOk`. -/
abbrev fm3 : List Instr := oddMask aQa ++ ([.alu .and .rcx (.reg .rax),
    .mov .rax (.mem (hdr kEv)), .alu .and .rax (.imm 1), .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax),
    .alu .and .rcx (.reg .rdx),
    .mov .rax (.mem (hdr kEv)), .alu .cmp .rax (.imm 3), .alu .sbb .rdx (.reg .rdx),
    .alu .xor .rdx (.imm (BitVec.ofInt 32 (-1))), .alu .and .rcx (.reg .rdx),
    .mov .rax (.mem (hdr kEv)), .shift .shr .rax 33, .alu .cmp .rax (.imm 1), .alu .sbb .rdx (.reg .rdx),
    .alu .and .rcx (.reg .rdx), .store (hdr kOk) .rcx] : List Instr)

theorem finalMask_eq3 : finalMask = (ws ++ fm1) ++ (fm2 ++ fm3) := by
  simp only [finalMask, fm1, fm2, fm3, oddMask, List.append_assoc, List.cons_append, List.nil_append]

/-- A mask in `rcx`. -/
abbrev RcxM : KIn → State → Prop := fun _ t => ∃ c, t.gpr .rcx = mask c

theorem fm1_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (hk : KokM I s) :
    WP isa (.block (ws ++ fm1)) s fun t => t.mem = s.mem ∧ Keep [.r12, .r9, .rbx, .rax, .rdx, .rcx] s t ∧
      RcxM I t := by
  obtain ⟨ok, hok⟩ := hk
  have hnw := h.ws.scr.nowrap
  have hw1 : 1 ≤ I.W := by have := h.ws.w1; omega_using [this]
  have sN := h.ws.sl (j := aQt) (by decide)
  refine WP.block_append_iff.mpr (WP.mono h.ws.ws_ok fun u₁ ⟨h12, h9, mu₁, ku₁⟩ => WP.block_append_iff.mpr ?_)
  have hdi₁ : u₁.gpr .rdi = I.B := (ku₁.gpr (by decide)).trans h.ws.rdi
  refine WP.mono (base_ok aQt (r := .rbx) (by decide) hdi₁ h9) fun u₂ ⟨hbx, mu₂, ku₂⟩ => ?_
  have hs₂ := h.ws.scr.congr (ku₁.trans ku₂).2.2
  have h12₂ : u₂.gpr .r12 = BitVec.ofNat 64 I.W := (ku₂.gpr (by decide)).trans h12
  have hmu₂ : u₂.mem = s.mem := by rw [mu₂, mu₁]
  refine WP.mono (WP.keep [.rax, .rdx, .rcx] (Q := fun t => t.gpr .rcx = mask
      (decide ((s.mem.readW (off I.B (slot I.W aQt + 8 * (I.W - 1))) 64).toNat / 2 ^ 63 = 1) && ok) ∧
    t.mem = s.mem) (by
      have hok₂ : word u₂.mem I.B (8 * kOk) = mask ok := by rw [hmu₂, hok]
      xrun [State.ea, ix, hdr, hdrOff, h12₂, addr_last hbx hw1, hs₂.ld (d := slot I.W aQt + 8 * (I.W - 1)) (by omega_using [sN]),
        ((ku₁.trans ku₂).gpr (by decide)).trans h.ws.rdi, hs₂.ld (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega_using [this]),
        shr63_mask, hok₂, mask_and', hmu₂]
      have hok' : s.mem.readW (off I.B (8 * kOk)) 64 = mask ok := hok
      rw [hok', mask_and']) rfl) fun t ⟨⟨hcx, hm⟩, k⟩ => ⟨hm, ((ku₁.trans ku₂).trans k).mono (by decide), _, hcx⟩

theorem fm2_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (hc : RcxM I s) :
    WP isa (.block fm2) s fun t => t.mem = s.mem ∧ Keep [.r12, .r9, .rbx, .rax, .rdx, .rcx] s t ∧ RcxM I t := by
  obtain ⟨c, hcx⟩ := hc
  refine WP.block_append_iff.mpr (WP.mono (oddMask_k h (j := aPa) (by decide)) fun u₄ ⟨mu₄, hax₄, _, _, ku₄⟩ => ?_)
  have hcx₄ : u₄.gpr .rcx = mask c := by rw [ku₄.gpr (by decide), hcx]
  refine WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = mask (c && decide (av I s.mem aPa % 2 = 1)) ∧
    t.mem = u₄.mem) (by xrun [hax₄, hcx₄, mask_and']) rfl) fun t ⟨⟨hcx₅, mu₅⟩, ku₅⟩ =>
      ⟨by rw [mu₅, mu₄], (ku₄.trans ku₅).mono (by decide), _, hcx₅⟩

theorem fm3_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (hc : RcxM I s) :
    WP isa (.block fm3) s fun t => KS I m₀ t ∧ KF I.B I.W [.hdr kOk] s.mem t.mem ∧ KokM I t ∧
      Keep [.r12, .r9, .rbx, .rax, .rdx, .rcx] s t := by
  obtain ⟨c, hcx⟩ := hc
  have hw1 : 1 ≤ I.W := by have := h.ws.w1; omega_using [this]
  refine WP.block_append_iff.mpr (WP.mono (oddMask_k h (j := aQa) (by decide)) fun u₆ ⟨mu₆, hax₆, _, _, ku₆⟩ => ?_)
  have hcx₆ : u₆.gpr .rcx = mask c := by rw [ku₆.gpr (by decide), hcx]
  have hs₆ := h.ws.scr.congr ku₆.2.2
  have hdi₆ : u₆.gpr .rdi = I.B := (ku₆.gpr (by decide)).trans h.ws.rdi
  generalize he : (word s.mem I.B (8 * kEv)).toNat = e
  have he64 : e < 2 ^ 64 := by rw [← he]; exact BitVec.isLt _
  have hev : word s.mem I.B (8 * kEv) = BitVec.ofNat 64 e := by rw [← he, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hev₆ : u₆.mem.readW (off I.B (8 * kEv)) 64 = BitVec.ofNat 64 e := by rw [mu₆]; exact hev
  refine WP.mono (WP.keep [.rax, .rcx, .rdx] (Q := fun t => t.mem = s.mem.writeW (off I.B (8 * kOk))
    (mask (c && decide (av I s.mem aQa % 2 = 1) && Spec.Rsa.exponentValid e))) (by
      xrun [State.ea, hdr, hdi₆, hdrOff, hs₆.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega_using [this]),
        hs₆.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega_using [this]), hev₆, hax₆, hcx₆, mask_and', mask_low,
        sxM1, maskNot, mu₆]
      have hev' : s.mem.readW (off I.B (8 * kEv)) 64 = BitVec.ofNat 64 e := hev
      have hT : ((BitVec.ofNat 64 e) >>> 33).toNat = e / 2 ^ 33 := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64]
      have hsub : ∀ c : Bool, 0#64 - BitVec.setWidth 64 (BitVec.ofBool c) = mask c := fun _ => rfl
      rw [hev', BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64, hT, hsub, hsub, maskNot, mask_and', mask_and',
        show BitVec.toNat (3 : BitVec 64) = 3 from rfl, show BitVec.toNat (1 : BitVec 64) = 1 from rfl]
      have e1 : (decide (e % 2 = 1) && !decide (e < 3) && decide (e / 2 ^ 33 < 1)) = Spec.Rsa.exponentValid e := by
        unfold Spec.Rsa.exponentValid
        rw [Bool.eq_iff_iff]
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq]
        omega_using []
      refine congrArg (fun v => s.mem.writeW (off I.B (8 * kOk)) (mask v)) ?_
      rw [← e1]
      simp only [Bool.and_assoc]) rfl) fun t ⟨mt, kt⟩ => ?_
  obtain ⟨ht, ft, okt⟩ := h.hdrW (i := kOk) (by unfold kOk sFn; omega_using []) mt (ku₆.trans kt) (by decide)
  exact ⟨ht, ft, ⟨_, okt⟩, (ku₆.trans kt).mono (by decide)⟩

theorem finalMask_ct {F : KIn → State → Prop} (hF : Stab F [.hdr kOk] allR) :
    RelCT isa (Two (KG fun I t => F I t ∧ KokM I t)) (.block finalMask) (Two (KG fun I t => F I t ∧ KokM I t)) := by
  rw [finalMask_eq3]
  refine RelCT.block_append (RelCT.seq (kg_wsb (G := fun I t => F I t ∧ RcxM I t) (by taint_decide)
    fun I _ s h _ ⟨hf, hk⟩ => WP.mono (fm1_k h hk) fun t ⟨hm, k, hc⟩ =>
      ⟨h.same hm k (by decide), hF I s t h.hZ hf (kf_eq hm) (k.mono (by decide)), hc⟩) ?_)
  refine RelCT.block_append (RelCT.seq (R := Two (KG fun I t => F I t ∧ RcxM I t)) ?_ ?_)
  · have e : fm2 = ws ++ (base aPa .rbx ++ ([.mov .rax (.mem (at0 .rbx)), .alu .and .rax (.imm 1),
        .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax), .mov .rax (.reg .rdx), .alu .and .rcx (.reg .rax)] :
        List Instr)) := by
      simp only [fm2, oddMask, List.append_assoc, List.cons_append, List.nil_append]
    rw [e]
    exact kg_wsb (G := fun I t => F I t ∧ RcxM I t) (by taint_decide) fun I _ s h _ ⟨hf, hc⟩ => by
      rw [← e]
      exact WP.mono (fm2_k h hc) fun t ⟨hm, k, hc'⟩ =>
        ⟨h.same hm k (by decide), hF I s t h.hZ hf (kf_eq hm) (k.mono (by decide)), hc'⟩
  · have e : fm3 = ws ++ (base aQa .rbx ++ ([.mov .rax (.mem (at0 .rbx)), .alu .and .rax (.imm 1),
        .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax), .mov .rax (.reg .rdx), .alu .and .rcx (.reg .rax),
        .mov .rax (.mem (hdr kEv)), .alu .and .rax (.imm 1), .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax),
        .alu .and .rcx (.reg .rdx),
        .mov .rax (.mem (hdr kEv)), .alu .cmp .rax (.imm 3), .alu .sbb .rdx (.reg .rdx),
        .alu .xor .rdx (.imm (BitVec.ofInt 32 (-1))), .alu .and .rcx (.reg .rdx),
        .mov .rax (.mem (hdr kEv)), .shift .shr .rax 33, .alu .cmp .rax (.imm 1), .alu .sbb .rdx (.reg .rdx),
        .alu .and .rcx (.reg .rdx), .store (hdr kOk) .rcx] : List Instr)) := by
      simp only [fm3, oddMask, List.append_assoc, List.cons_append, List.nil_append]
    rw [e]
    exact kg_wsb (by taint_decide) fun I _ s h _ ⟨hf, hc⟩ => by
      rw [← e]
      exact WP.mono (fm3_k h hc) fun t ⟨ht, f, hk, k⟩ => ⟨ht, hF I s t h.hZ hf f (k.mono (by decide)), hk⟩

/-! ## `qInv` -/

/-- `qinvPart`'s mask of `p` odd and at least 3, after `ws`. -/
abbrev qBlk : List Instr :=
  base aPa .rbx ++ ([.mov .rax (.mem (at0 .rbx)), .alu .and .rax (.imm 1), .mov32 .rdx (.imm 0),
    .alu .sub .rdx (.reg .rax), .mov .rax (.reg .rdx), .alu .and .rax (.reg .rcx), .mov .rbp (.reg .rax)] : List Instr)

theorem qBlk_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {c : Bool} (hcx : s.gpr .rcx = mask c) :
    WP isa (.block (ws ++ qBlk)) s fun t => t.mem = s.mem ∧ RbpM I t ∧ Keep [.r12, .r9, .rbx, .rax, .rdx, .rbp] s t := by
  have e : ws ++ qBlk = oddMask aPa ++ [.alu .and .rax (.reg .rcx), .mov .rbp (.reg .rax)] := by
    simp only [qBlk, oddMask, List.append_assoc, List.cons_append, List.nil_append]
  rw [e]
  refine WP.block_append_iff.mpr (WP.mono (oddMask_k h (j := aPa) (by decide)) fun s₁ ⟨m₁, hax, _, _, k₁⟩ => ?_)
  have hcx₁ : s₁.gpr .rcx = mask c := (k₁.gpr (by decide)).trans hcx
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t => t.mem = s₁.mem ∧ ∃ c', t.gpr .rbp = mask c') (by
      xrun [hax, hcx₁, mask_and']
      exact ⟨_, rfl⟩) rfl) fun t ⟨⟨hm, hbp⟩, k₂⟩ => ⟨by rw [hm, m₁], hbp, (k₁.trans k₂).mono (by decide)⟩

/-- `gcdIsOne`, keeping a mask in `kOk`. -/
theorem gcdIsOneK_ct {F : KIn → State → Prop} (hF : Stab F [.arr aC, .hdr kOk] allR) :
    RelCT isa (Two (KG fun I t => F I t ∧ KokM I t)) (seqs gcdIsOne) (Two (KG fun I t => F I t ∧ KokM I t)) := by
  unfold gcdIsOne
  simp only [List.append_assoc]
  refine rs_app (by simp [constA]) (by simp [eqMask, eqA]) (constA_ct 1 (stab_and (hF.mono (by decide) (by simp))
    (stab_kok _ (by decide) (by decide))).sub (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp [eqMask, eqA]) (by simp) (eqMask_ct (G := fun I t => (F I t ∧ KokM I t) ∧ RbpM I t)
    (by decide) (by decide) (fun I s t hZ hf hm k hbp => ⟨(stab_and (hF.mono (cs' := []) (by simp) (by simp))
      (stab_kok (cs := []) _ (by decide) (by decide)) : Stab _ [] allR) I s t hZ hf (kf_eq hm) (k.mono (by decide)),
      _, hbp⟩) (by taint_decide)) ?_
  exact kg_rdi (by taint_decide) fun I _ s h _ ⟨⟨hf, c, hok⟩, c', hbp⟩ => by
    have hst := h.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega_using [this])
    have hld := h.ws.scr.ld (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega_using [this])
    refine WP.mono (WP.keep [.rbp] (Q := fun t => t.mem = s.mem.writeW (off I.B (8 * kOk)) (mask (c' && c))) (by
      xrun [State.ea, hdr, h.ws.rdi, hdrOff, hst, hld, hbp, hok, mask_and']) rfl) fun t ⟨hm, k⟩ => ?_
    obtain ⟨ht, f, hw⟩ := h.hdrW (i := kOk) (by unfold kOk sFn; omega_using []) hm k (by decide)
    exact ⟨ht, hF I s t h.hZ hf (f.mono (by decide)) (k.mono (by decide)), _, hw⟩

theorem qinvPart_eq2 : qinvPart = [zeroA aU, copyA aU aQa] ++ (constA 3 ++ (ltA aPa aC ++
    (([.block (([.mov .rcx (.reg .rbp), .alu .xor .rcx (.imm (BitVec.ofInt 32 (-1)))] : List Instr) ++ (ws ++ qBlk))] : List (Prog isa)) ++
    ([zeroA aM, copyA aM aPa] ++ (selC aM ++ ([inverseK kHalf aU aV aX₂ aM] ++ gcdIsOne)))))) := by
  simp only [qinvPart, qBlk, oddMask, gcdIsOne, List.append_assoc, List.cons_append, List.nil_append]

/-- `qinvPart`, keeping a mask in `kOk`. -/
theorem qinvPart_ct [InvLaw] : RelCT isa (Two (KG fun I t => NF I t ∧ KokM I t)) (seqs qinvPart)
    (Two (KG fun I t => NF I t ∧ KokM I t)) := by
  have sK : ∀ (cs : List Rc), cs.all Rc.ok = true → .hdr kOk ∉ cs →
      Stab (fun I t => NF I t ∧ KokM I t) cs allR := fun cs h1 h2 => stab_and (stab_nf _ _) (stab_kok _ h1 h2)
  have sKT : ∀ (cs : List Rc), cs.all Rc.ok = true → .hdr kOk ∉ cs → .arr aU ∉ cs →
      Stab (fun I t => (NF I t ∧ KokM I t) ∧ TopZ aU I t) cs allR :=
    fun cs h1 h2 h3 => stab_and (sK cs h1 h2) (stab_top _ (by decide) h1 h3)
  rw [qinvPart_eq2]
  refine rs_app (by simp) (by simp [constA]) (show RelCT isa _ (seqs [zeroA aU, copyA aU aQa]) _ from
    zc_ct (by decide) (by decide) (by decide) (sK _ (by decide) (by decide)) (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp [constA]) (by simp [ltA]) (constA_ct 3 (sKT [.arr aC] (by decide) (by decide)
    (by decide)).sub (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp [ltA]) (by simp) (ltA_ct (G := fun I t => ((NF I t ∧ KokM I t) ∧ TopZ aU I t) ∧ RbpM I t)
    (by decide) (by decide) (fun I s t hZ hf hm k hbp => ⟨sKT [] (by decide) (by decide) (by decide) I s t hZ hf
      (kf_eq hm) (k.mono (by decide)), _, hbp⟩) (by taint_decide)) ?_
  refine rs_app (by simp) (by simp) (show RelCT isa _ (seqs [.block ([.mov .rcx (.reg .rbp),
    .alu .xor .rcx (.imm (BitVec.ofInt 32 (-1)))] ++ (ws ++ qBlk))]) _ from RelCT.block_append (RelCT.seq
      (kg_regs (G := fun I t => ((NF I t ∧ KokM I t) ∧ TopZ aU I t) ∧ RcxM I t) (rs := [.rcx]) (by decide)
        (by taint_decide) fun I s hZ ⟨hf, c, hbp⟩ => WP.mono (WP.keep [.rcx] (Q := fun t =>
          t.gpr .rcx = mask (!c) ∧ t.mem = s.mem) (by xrun [hbp, sxM1, maskNot]) rfl) fun t ⟨⟨hcx, hm⟩, k⟩ =>
            ⟨hm, k, sKT [] (by decide) (by decide) (by decide) I s t hZ hf (kf_eq hm) (k.mono (by decide)), _, hcx⟩)
      (kg_wsb (G := fun I t => ((NF I t ∧ KokM I t) ∧ TopZ aU I t) ∧ RbpM I t) (by taint_decide)
        fun I _ s h _ ⟨hf, c, hcx⟩ => WP.mono (qBlk_k h hcx) fun t ⟨hm, hbp, k⟩ =>
          ⟨h.same hm k (by decide), sKT [] (by decide) (by decide) (by decide) I s t h.hZ hf (kf_eq hm)
            (k.mono (by decide)), hbp⟩))) ?_
  refine rs_app (by simp) (by simp [selC]) (show RelCT isa _ (seqs [zeroA aM, copyA aM aPa]) _ from
    RelCT.seq (zeroA_ct (by decide) (stab_and (sKT [.arr aM] (by decide) (by decide) (by decide)).sub
      (stab_rbp (by decide))) (by taint_decide))
      (copyA_ct (by decide) (by decide) (by decide) (stab_and (sKT [.arr aM] (by decide) (by decide)
        (by decide)).sub (stab_rbp (by decide))) (by taint_decide))) ?_
  refine rs_app (by simp [selC]) (by simp) (selC_ct (by decide) (by decide)
    (sKT [.arr aM] (by decide) (by decide) (by decide)).sub (by taint_decide)) ?_
  refine rs_app (by simp) (by simp [gcdIsOne, constA]) (invK_ct (fun hF ht => inverseHalf_ct (by decide) (by decide)
    (by decide) (by decide) (by decide) hF ht) (sK _ (by decide) (by decide)) (by taint_decide)) ?_
  exact gcdIsOneK_ct (stab_nf _ _)

/-! ## `dP`, `dQ` and `n` -/

/-- `divisorOf`'s `[aM] := [j]`, or 1 for `[j] = 0`, after `ws`. -/
abbrev dvBlk : List Instr :=
  base aM .rbx ++ ([.mov .rax (.mem (at0 .rbx)), .alu .and .rbp (.imm 1), .alu .or .rax (.reg .rbp),
    .store (at0 .rbx) .rax] : List Instr)

theorem dvBlk_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) :
    WP isa (.block (ws ++ dvBlk)) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aM] s.mem t.mem ∧
      Keep [.r12, .r9, .rbx, .rax, .rbp] s t := by
  have hn := h.ws.scr.nowrap
  have sM := h.ws.sl (j := aM) (by decide)
  refine WP.block_append_iff.mpr (WP.mono h.ws.ws_ok fun u₁ ⟨_, h9, mu₁, ku₁⟩ => WP.block_append_iff.mpr ?_)
  have hdi₁ : u₁.gpr .rdi = I.B := (ku₁.gpr (by decide)).trans h.ws.rdi
  refine WP.mono (base_ok aM (r := .rbx) (by decide) hdi₁ h9) fun u₂ ⟨hbx, mu₂, ku₂⟩ => ?_
  have hmu : u₂.mem = s.mem := by rw [mu₂, mu₁]
  have hs₂ := h.ws.scr.congr (ku₁.trans ku₂).2.2
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t =>
    ∃ v : BitVec 64, t.mem = s.mem.writeW (off I.B (slot I.W aM)) v) (by
      xrun [State.ea, at0, hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
        hs₂.ld (d := slot I.W aM) (by omega_using [sM]), hs₂.st (d := slot I.W aM) (by omega_using [sM]), hmu]
      exact ⟨_, rfl⟩) rfl) fun t ⟨hm, k⟩ => ?_
  have kk := (ku₁.trans ku₂).trans k
  obtain ⟨ht, f⟩ := h.arrSome (by decide) hm kk (by decide)
  exact ⟨ht, f, kk.mono (by decide)⟩

theorem divisorOf_eq2 (j : Nat) : divisorOf j = [zeroA aM, copyA aM j] ++ (constA 0 ++ (eqMask j aC ++
    ([.block (ws ++ dvBlk)] : List (Prog isa)))) := by
  simp only [divisorOf, dvBlk, List.append_assoc]

/-- `divisorOf j`, for facts its changes keep. -/
theorem divisorOf_ct {F : KIn → State → Prop} {j : Nat} (hj : j < 16) (hjM : j ≠ aM)
    (hF : Stab F [.arr aM, .arr aC] allR) {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .rsi ++ base aM .rbx))
      Impl.Rsa.X86_64.copyWords) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .rbx ++ (base aC .r10 ++
      ([.mov32 .rbp (.imm 0)] : List Instr)))) (.seq (wordLoop 0 xorBody) (.block isZero))) hc₂).isSome = true) :
    RelCT isa (Two (KG F)) (seqs (divisorOf j)) (Two (KG F)) := by
  rw [divisorOf_eq2]
  refine rs_app (by simp) (by simp [constA]) (show RelCT isa _ (seqs [zeroA aM, copyA aM j]) _ from
    RelCT.seq (zeroA_ct (by decide) (hF.mono (by decide) (by simp)).sub (by taint_decide))
      (copyA_ct (by decide) hj hjM.symm (hF.mono (by decide) (by simp)).sub ht₁)) ?_
  refine rs_app (by simp [constA]) (by simp [eqMask, eqA]) (constA_ct 0 (hF.mono (by decide) (by simp)).sub
    (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp [eqMask, eqA]) (by simp) (eqMask_ct (G := F) hj (by decide)
    (fun I s t hZ hf hm k _ => hF I s t hZ hf (kf_eq hm) (k.mono (by decide))) ht₂) ?_
  exact kg_wsb (by taint_decide) fun I _ s h _ hf => WP.mono (dvBlk_k h) fun t ⟨ht, f, k⟩ =>
    ⟨ht, hF I s t h.hZ hf (f.mono (by decide)) (k.mono (by decide))⟩

theorem crtPart_eq2 : crtPart = divisorOf aPm ++ ([zeroA aU, copyA aU aDd, divmod aU aV aM aT, zeroA aX₁,
    copyA aX₁ aV] ++ (divisorOf aQm ++ [zeroA aU, copyA aU aDd, divmod aU aV aM aT])) := by
  simp only [crtPart, List.append_assoc]

/-- `crtPart`, keeping a mask in `kOk`. -/
theorem crtPart_ct : RelCT isa (Two (KG fun I t => NF I t ∧ KokM I t)) (seqs crtPart)
    (Two (KG fun I t => NF I t ∧ KokM I t)) := by
  have sK : ∀ (cs : List Rc), cs.all Rc.ok = true → .hdr kOk ∉ cs →
      Stab (fun I t => NF I t ∧ KokM I t) cs allR := fun cs h1 h2 => stab_and (stab_nf _ _) (stab_kok _ h1 h2)
  have tail : RelCT isa (Two (KG fun I t => NF I t ∧ KokM I t)) (seqs [zeroA aU, copyA aU aDd, divmod aU aV aM aT])
      (Two (KG fun I t => NF I t ∧ KokM I t)) :=
    RelCT.seq (zeroA_ct (by decide) (sK _ (by decide) (by decide)).sub (by taint_decide))
      (RelCT.seq (copyA_ct (by decide) (by decide) (by decide) (sK _ (by decide) (by decide)).sub (by taint_decide))
        (divmod_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (sK [.arr aU, .arr aV, .arr aT] (by decide) (by decide)).sub (by taint_decide)))
  rw [crtPart_eq2]
  refine rs_app (by simp [divisorOf]) (by simp) (divisorOf_ct (by decide) (by decide) (sK _ (by decide) (by decide))
    (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp) (by simp [divisorOf]) (show RelCT isa _ (seqs ([zeroA aU, copyA aU aDd, divmod aU aV aM aT] ++
    [zeroA aX₁, copyA aX₁ aV])) _ from rs_app (by simp) (by simp) tail
      (RelCT.seq (zeroA_ct (by decide) (sK _ (by decide) (by decide)).sub (by taint_decide))
        (copyA_ct (by decide) (by decide) (by decide) (sK _ (by decide) (by decide)).sub (by taint_decide)))) ?_
  exact rs_app (by simp [divisorOf]) (by simp) (divisorOf_ct (by decide) (by decide) (sK _ (by decide) (by decide))
    (by taint_decide) (by taint_decide)) tail

theorem nPart_eq : seqs nPart = .seq (zeroA aQt) (.seq (.block (ws ++ mulBlk aPa aQa aQt))
    Impl.Rsa.X86_64.Crt.mulRows) := by
  simp only [nPart, seqs, mulBlk, List.append_assoc]

theorem nPart_ct : RelCT isa (Two (KG fun I t => NF I t ∧ KokM I t)) (seqs nPart)
    (Two (KG fun I t => NF I t ∧ KokM I t)) := by
  rw [nPart_eq]
  exact mul_ct (by decide) (by decide) (by decide) (by decide) (by decide)
    (stab_and (stab_nf _ _) (stab_kok _ (by decide) (by decide))) (by taint_decide) (by taint_decide)

end VG.Proof.RsaKeyGen.X86_64.Key

end

end

/-! ## CTOut -/

@[expose] public section

section

/-!
# An RSA key from its primes on x86-64: constant time, the outputs

The zeros and the stores take each output's pointer and length from the
header, which correctness pins to the public data (`zeroOutK_ct`,
`storeAK_ct`), and leave the header and the working space as they were
(`EG`); the exit reads the header.
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Bignum.X86_64.Public (exit)

/-- From the outputs on: the header and the working space of some inputs
with the public data `p`, with the facts `M`. -/
def EG (M : KIn → State → Prop) (p : KP) (s : State) : Prop :=
  ∃ I, I.pub = p.q ∧ Ws s I.B I.Z I.W ∧ KArgs s.mem I ∧ s.wr = I.Wr ∧ KLens I ∧ KOuts I ∧ M I s

theorem pins_EG (M : KIn → State → Prop) : Pins (EG M) [.rdi] := fun _ _ _ ⟨I₁, e₁, w₁, _⟩ ⟨I₂, e₂, w₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [w₁.rdi, w₂.rdi]
  exact (congrArg KQ.B e₁).trans (congrArg KQ.B e₂).symm

theorem EG.of_kg {M : KIn → State → Prop} {p : KP} {s : State} (h : KG M p s) : EG M p s :=
  let ⟨I, _, he, _, hk, L, O, hM⟩ := h
  ⟨I, he, hk.ws, hk.args, hk.wr, L, O, hM⟩

/-- Where an output is, in the header. -/
abbrev OutHdr (sPtr sLen : Nat) (ptr : KQ → Addr) (len : KQ → Nat) : Prop :=
  ∀ I (m : Mem), KArgs m I → KLens I → word m I.B (8 * sPtr) = ptr I.pub ∧
    word m I.B (8 * sLen) = BitVec.ofNat 64 (len I.pub) ∧ (ptr I.pub, len I.pub) ∈ outsL I ∧ 1 ≤ len I.pub ∧
    len I.pub ≤ 8 * I.W

/-- Facts of the header. -/
abbrev HdrStab (M : KIn → State → Prop) : Prop :=
  ∀ I s t, M I s → (∀ i < 32, word t.mem I.B (8 * i) = word s.mem I.B (8 * i)) → M I t

theorem EG.after {M : KIn → State → Prop} (hM : HdrStab M) {I : KIn} {s t : State} (hw : Ws s I.B I.Z I.W)
    (ha : KArgs s.mem I) (hW : s.wr = I.Wr) (hm : M I s) (hf : Frm I.B [(I.Z, 2 ^ 64)] s.mem t.mem) {rs : List Reg}
    (k : Keep rs s t) (hr : .rdi ∉ rs) :
    Ws t I.B I.Z I.W ∧ KArgs t.mem I ∧ t.wr = I.Wr ∧ M I t := by
  have h256 := hw.h256
  have fw : ∀ i < 32, word t.mem I.B (8 * i) = word s.mem I.B (8 * i) := fun i hi => frm_word hf h256 hi
  exact ⟨hw.congr hf (fun r hr' => by rw [List.mem_singleton.mp hr']; exact Or.inl (by omega)) k hr,
    ha.congr fun i hi => fw i (by omega_using [hi]), k.2.2.trans hW, hM I s t hm fw⟩

/-- `zeroOut`'s loop's registers. -/
def zoVal (ptr : Addr) (len : Nat) : Reg → BitVec 64
  | .rsi => ptr
  | .rcx => BitVec.ofNat 64 len
  | _ => 0

theorem zeroOutK_ct {M : KIn → State → Prop} (hM : HdrStab M) {sPtr sLen : Nat} (hP : sPtr < 32) (hL : sLen < 32)
    (ptr : KQ → Addr) (len : KQ → Nat) (hA : OutHdr sPtr sLen ptr len) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rsi (.mem (hdr sPtr)), .mov .rcx (.mem (hdr sLen)),
      .mov32 .rax (.imm 0)]) hc).isSome = true) :
    RelCT isa (Two (EG M)) (zeroOut sPtr sLen) (Two (EG M)) :=
  pin_ct [.rdi] [.rsi, .rcx] (fun p : KP => zoVal (ptr p.q) (len p.q)) (pins_EG M) ht
    (fun p s h => by
      obtain ⟨I, he, hw, ha, -, L, -⟩ := h
      obtain ⟨hp, hl, -⟩ := hA I s.mem ha L
      rw [he] at hp hl
      have hl' : ∀ i < 32, InRegions (s.rd ++ s.wr) (off I.B (8 * i)) 8 := fun i hi =>
        hw.scr.ld (by have := hw.h256; omega_using [hi, this])
      refine WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t => t.gpr .rsi = ptr p.q ∧
        t.gpr .rcx = BitVec.ofNat 64 (len p.q)) (by
        xrun [State.ea, hdr, hw.rdi, hdrOff, hl' sPtr hP, hl' sLen hL]
        exact ⟨hp, hl⟩) rfl) fun t ⟨⟨h1, h2⟩, _⟩ r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h1
      · exact h2)
    (by taint_decide) fun p s h => by
      obtain ⟨I, he, hw, ha, hW, L, O, hm⟩ := h
      obtain ⟨hp, hl, ho, hl1, hlw⟩ := hA I s.mem ha L
      have hw2 := hw.w2
      refine WP.mono (zeroOut_ok hw.scr hw.rdi hw.h256 hP hL hp hl hl1 (by omega_using [hlw, hw2])
        ⟨fun i hi => by rw [hW]; exact O.wr _ ho i hi, O.sep _ ho⟩) fun t ⟨_, hx, k⟩ => ?_
      obtain ⟨a, b, c, d⟩ := EG.after hM hw ha hW hm (frm_scr (O.sep _ ho) hx) k (by decide)
      exact ⟨I, he, a, b, c, L, O, d⟩

/-- The block before `storeBE`, with `kOk` the mask. -/
theorem storeBlkK_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j sPtr sLen len : Nat} {ptr : Addr}
    (hP : sPtr < 32) (hL : sLen < 32) (hp : word s.mem B (8 * sPtr) = ptr)
    (hl : word s.mem B (8 * sLen) = BitVec.ofNat 64 len) :
    WP isa (.block (ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)), .mov .rcx (.mem (hdr sLen)),
      .mov .r15 (.mem (hdr kOk))] : List Instr)))
      s fun t => t.gpr .rbx = off B (slot w j) ∧ t.gpr .rsi = ptr ∧ t.gpr .rcx = BitVec.ofNat 64 len ∧
        t.gpr .rdi = B := by
  refine WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₂ ⟨_, h9, m₂, k₂⟩ =>
    WP.mono (base_ok j (r := .rbx) (by decide) ((k₂.gpr (by decide)).trans h.rdi) h9) fun s₃ ⟨hbx, m₃, k₃⟩ =>
      WP.mono (WP.keep [.rsi, .rcx, .r15] (Q := fun t => t.gpr .rsi = ptr ∧ t.gpr .rcx = BitVec.ofNat 64 len) (by
          have hdi₃ : s₃.gpr .rdi = B := ((k₂.trans k₃).gpr (by decide)).trans h.rdi
          have hs₃ := h.scr.congr (k₂.trans k₃).2.2
          have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (off B (8 * i)) 8 := fun i hi =>
            hs₃.ld (by have := h.h256; omega_using [hi, this])
          xrun [State.ea, hdr, hdi₃, hdrOff, m₃, m₂, hl₃ sPtr hP, hl₃ sLen hL, hl₃ kOk (by decide), hp, hl]) rfl)
      fun _ ⟨⟨hsi, hcx⟩, k₄⟩ => ⟨(k₄.gpr (by decide)).trans hbx, hsi, hcx,
        ((k₂.trans k₃).trans k₄ |>.gpr (by decide)).trans h.rdi⟩))

theorem storeAK_ct {j sPtr sLen : Nat} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (ptr : KQ → Addr)
    (len : KQ → Nat) (hA : OutHdr sPtr sLen ptr len) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block (ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)),
      .mov .rcx (.mem (hdr sLen)), .mov .r15 (.mem (hdr kOk))] : List Instr))) hc).isSome = true) :
    RelCT isa (Two (EG KokM)) (seqs (storeA j sPtr sLen kOk)) (Two (EG KokM)) :=
  pin_ct [.rdi] [.rdi, .rbx, .rsi, .rcx]
    (fun p : KP => ioVal p.q.B (off p.q.B (slot (2 * p.q.pl / 8) j)) (ptr p.q) (len p.q)) (pins_EG KokM) ht
    (fun p s h => by
      obtain ⟨I, he, hw, ha, -, L, -⟩ := h
      obtain ⟨hp, hl, -⟩ := hA I s.mem ha L
      rw [← he]
      exact WP.mono (storeBlkK_ok hw hP hL hp hl) fun t ⟨hbx, hsi, hcx, hdi⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hdi
        · exact hbx
        · exact hsi
        · exact hcx)
    (by taint_decide) fun p s h => by
      obtain ⟨I, he, hw, ha, hW, L, O, c, hm⟩ := h
      obtain ⟨hp, hl, ho, hl1, hlw⟩ := hA I s.mem ha L
      refine WP.mono (storeK_ws hw hj hP hL hp hl hm hl1 hlw (fun i hi => by rw [hW]; exact O.wr _ ho i hi)
        (O.sep _ ho)) fun t ⟨_, _, ht, hf, k⟩ => ?_
      have h256 := hw.h256
      have fw : ∀ i < 32, word t.mem I.B (8 * i) = word s.mem I.B (8 * i) := fun i hi => frm_word hf h256 hi
      exact ⟨I, he, ht, ha.congr fun i hi => fw i (by omega_using [hi]), k.2.2.trans hW, L, O, c, (fw _ (by decide)).trans hm⟩

/-! ## The outputs' places -/

theorem outN : OutHdr kNo kNl KQ.pN (fun q => 2 * q.pl) := fun I _ ha L =>
  ⟨ha.no, ha.nl, by simp [outsL, KIn.pub], by have := L.pl1; simp only [KIn.pub]; omega_using [this],
    by simp only [KIn.pub]; rw [L.W]; have := L.pl8; omega_using [this]⟩

theorem outD : OutHdr kDo kNl KQ.pD (fun q => 2 * q.pl) := fun I _ ha L =>
  ⟨ha.dd, ha.nl, by simp [outsL, KIn.pub], by have := L.pl1; simp only [KIn.pub]; omega_using [this],
    by simp only [KIn.pub]; rw [L.W]; have := L.pl8; omega_using [this]⟩

theorem outP : OutHdr kPp kPl KQ.pP KQ.pl := fun I _ ha L =>
  ⟨ha.pp, ha.pl, by simp [outsL, KIn.pub], by have := L.pl1; simp only [KIn.pub]; omega_using [this],
    by simp only [KIn.pub]; rw [L.W]; have := L.pl8; omega_using [this]⟩

theorem outQ : OutHdr kQp kPl KQ.pQ KQ.pl := fun I _ ha L =>
  ⟨ha.qp, ha.pl, by simp [outsL, KIn.pub], by have := L.pl1; simp only [KIn.pub]; omega_using [this],
    by simp only [KIn.pub]; rw [L.W]; have := L.pl8; omega_using [this]⟩

theorem outDp : OutHdr kDp kPl KQ.pDp KQ.pl := fun I _ ha L =>
  ⟨ha.dp, ha.pl, by simp [outsL, KIn.pub], by have := L.pl1; simp only [KIn.pub]; omega_using [this],
    by simp only [KIn.pub]; rw [L.W]; have := L.pl8; omega_using [this]⟩

theorem outDq : OutHdr kDq kPl KQ.pDq KQ.pl := fun I _ ha L =>
  ⟨ha.dq, ha.pl, by simp [outsL, KIn.pub], by have := L.pl1; simp only [KIn.pub]; omega_using [this],
    by simp only [KIn.pub]; rw [L.W]; have := L.pl8; omega_using [this]⟩

theorem outQi : OutHdr kQi kPl KQ.pQi KQ.pl := fun I _ ha L =>
  ⟨ha.qi, ha.pl, by simp [outsL, KIn.pub], by have := L.pl1; simp only [KIn.pub]; omega_using [this],
    by simp only [KIn.pub]; rw [L.W]; have := L.pl8; omega_using [this]⟩

/-! ## The zeros and the stores -/

theorem zeros_ct : RelCT isa (Two (EG NF)) (zeros 2) fun _ _ => True := by
  have hM : HdrStab NF := fun _ _ _ _ _ => trivial
  unfold zeros
  simp only [seqs]
  exact RelCT.seq (zeroOutK_ct hM (by decide) (by decide) _ _ outN (by taint_decide))
    (RelCT.seq (zeroOutK_ct hM (by decide) (by decide) _ _ outD (by taint_decide))
    (RelCT.seq (zeroOutK_ct hM (by decide) (by decide) _ _ outP (by taint_decide))
    (RelCT.seq (zeroOutK_ct hM (by decide) (by decide) _ _ outQ (by taint_decide))
    (RelCT.seq (zeroOutK_ct hM (by decide) (by decide) _ _ outDp (by taint_decide))
    (RelCT.seq (zeroOutK_ct hM (by decide) (by decide) _ _ outDq (by taint_decide))
    (RelCT.seq (zeroOutK_ct hM (by decide) (by decide) _ _ outQi (by taint_decide))
      (two_taint [.rdi] (pins_EG NF) (by taint_decide))))))))

theorem outputs_eq2 : outputs = storeA aQt kNo kNl kOk ++ (storeA aDd kDo kNl kOk ++ (storeA aPa kPp kPl kOk ++
    (storeA aQa kQp kPl kOk ++ (storeA aX₁ kDp kPl kOk ++ (storeA aV kDq kPl kOk ++ (storeA aX₂ kQi kPl kOk ++
    ([.block (([.mov .rax (.mem (hdr kOk)), .alu .and .rax (.imm 1)] : List Instr) ++ exit)] : List (Prog isa)))))))) := by
  simp only [outputs, List.append_assoc]

theorem outputs_ct : RelCT isa (Two (EG KokM)) (seqs outputs) fun _ _ => True := by
  rw [outputs_eq2]
  refine rs_app (by simp [storeA]) (by simp [storeA]) (storeAK_ct (by decide) (by decide) (by decide) _ _ outN
    (by taint_decide)) ?_
  refine rs_app (by simp [storeA]) (by simp [storeA]) (storeAK_ct (by decide) (by decide) (by decide) _ _ outD
    (by taint_decide)) ?_
  refine rs_app (by simp [storeA]) (by simp [storeA]) (storeAK_ct (by decide) (by decide) (by decide) _ _ outP
    (by taint_decide)) ?_
  refine rs_app (by simp [storeA]) (by simp [storeA]) (storeAK_ct (by decide) (by decide) (by decide) _ _ outQ
    (by taint_decide)) ?_
  refine rs_app (by simp [storeA]) (by simp [storeA]) (storeAK_ct (by decide) (by decide) (by decide) _ _ outDp
    (by taint_decide)) ?_
  refine rs_app (by simp [storeA]) (by simp [storeA]) (storeAK_ct (by decide) (by decide) (by decide) _ _ outDq
    (by taint_decide)) ?_
  refine rs_app (by simp [storeA]) (by simp) (storeAK_ct (by decide) (by decide) (by decide) _ _ outQi
    (by taint_decide)) ?_
  exact two_taint [.rdi] (pins_EG KokM) (by taint_decide)

/-- `keyPart`, from a mask in `kOk`. -/
theorem keyPart_ct : RelCT isa (Two (KG fun I t => NF I t ∧ KokM I t)) keyPart fun _ _ => True := by
  rw [keyPart]
  simp only [List.append_assoc]
  refine rs_app (by simp [qinvPart]) (by simp [crtPart, divisorOf]) qinvPart_ct ?_
  refine rs_app (by simp [crtPart, divisorOf]) (by simp [nPart]) crtPart_ct ?_
  refine rs_app (by simp [nPart]) (by simp) nPart_ct ?_
  refine rs_app (by simp) (by simp [outputs, storeA]) (finalMask_ct (stab_nf _ _)) ?_
  exact outputs_ct.mono (fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, EG.of_kg (h₁.imp fun _ h => h.2), EG.of_kg (h₂.imp fun _ h => h.2)⟩)
    fun _ _ h => h

end VG.Proof.RsaKeyGen.X86_64.Key

end

/-! ## CTCode -/
section

/-!
# An RSA key from its primes on x86-64: constant time

Runs that agree on the arguments, `e` and the status leak the same
(`keyCode_constantTime`): the entry from `rsp`, the stack arguments and the
working space's base; the pieces from there (`front_ct`); and the branch on
`d` too small, whose condition correctness ties to the status (`front_zf`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate (loadE)
open VG.Spec.Rsa (bytesAt)

/-- A state the contract allows, with the public data `p`. -/
def KRel (p : KP) (s : State) : Prop := keyPre s ∧ (keyIn s).pub = p.q ∧ (keyIn s).st = p.st

/-- After `entry`'s first instruction. -/
def KC1 (p : KP) (t : State) : Prop :=
  ∃ s, KRel p s ∧ t.gpr .r11 = p.q.B ∧ t.gpr .rsp = p.q.sp ∧
    WP isa (.block (entry.drop 1 ++ head)) t (KS (keyIn s) s.mem)

theorem keyEntry_split : entry ++ head = ([.mov .r11 (.mem { base := .rsp, disp := 88 })] : List Instr) ++
    (entry.drop 1 ++ head) := rfl

/-- `entry` and `head`. -/
theorem start_ct : RelCT isa (Two KRel) (.block (entry ++ head)) (Two (KG NF)) := by
  rw [keyEntry_split]
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := KC1) [.rsp] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (congrArg KQ.sp h₁.2.1).trans (congrArg KQ.sp h₂.2.1).symm) (by taint_decide) ?_)
    (two_piece [.r11, .rsp] (fun p s₁ s₂ ⟨_, _, a₁, b₁, _⟩ ⟨_, _, a₂, b₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]) (by taint_decide) fun p t ⟨s, ⟨hpre, he, hst⟩, _, _, hw⟩ => WP.mono hw fun u hu =>
        ⟨keyIn s, s.mem, he, hst, hu, (keyCtx_of hpre).L, (keyCtx_of hpre).O, trivial⟩))
  intro p s ⟨hpre, he, hst⟩
  have c := keyCtx_of hpre
  have hh : WP isa (.block ([.mov .r11 (.mem { base := .rsp, disp := 88 })] ++ (entry.drop 1 ++ head))) s
      (KS (keyIn s) s.mem) := by
    rw [← keyEntry_split]; exact keyStart_k c
  have e10 : s.gpr .rsp + BitVec.ofInt 64 88 = stackArgAddr s 10 := rfl
  have hB' : s.mem.readW (stackArgAddr s 10) 64 = stackArg s 10 := rfl
  refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.r11] (Q := fun t => t.gpr .r11 = stackArg s 10)
    (by xrun [State.ea, e10, c.ha 10 (by decide), hB']) rfl)) fun t ⟨hw, h11, k⟩ =>
      ⟨s, ⟨hpre, he, hst⟩, h11.trans (congrArg KQ.B he), (k.gpr (by decide)).trans (congrArg KQ.sp he), hw⟩

/-- From the loads to `smallMask`. -/
theorem front_ct : RelCT isa (Two (KG NF))
    (seqs ((loadA aPa kPp kPl ++ (loadA aQa kQp kPl ++ (loadE ++ ([.block [.store (hdr kEv) .rbx]] : List (Prog isa))))) ++
      (order ++ (decTo aPm aPa ++ (decTo aQm aQa ++ (lcmPart ++ ([dPart] ++ smallMask)))))))
    (Two (KG NF)) := by
  refine rs_app (R := Two (KG EvOK)) (by simp [loadA]) (by simp [order, ltA]) ?_ ?_
  · refine rs_app (by simp [loadA]) (by simp [loadA]) loadAP_ct ?_
    exact rs_app (by simp [loadA]) (by simp [loadE]) loadAQ_ct loadE_ct
  refine rs_app (by simp [order, ltA]) (by simp [decTo]) order_ct ?_
  refine rs_app (by simp [decTo]) (by simp [decTo]) decP_ct ?_
  refine rs_app (by simp [decTo]) (by simp [lcmPart, phi]) decQ_ct ?_
  refine rs_app (by simp [lcmPart, phi]) (by simp) lcmPart_ct ?_
  exact rs_app (by simp) (by simp [smallMask, constA]) dPart_ct smallMask_ct

/-- `WP` for every `a` of a family, from one: runs are deterministic. -/
theorem wp_all {c : Prog isa} {s : State} {α : Type} {P : α → Prop} {Q : α → State → Prop} (a₀ : α) (h₀ : P a₀)
    (h : ∀ a, P a → WP isa c s (Q a)) : WP isa c s fun t => ∀ a, P a → Q a t := by
  obtain ⟨tr, t, e, -⟩ := h a₀ h₀
  refine ⟨tr, t, e, fun a ha => ?_⟩
  obtain ⟨_, _, e', q⟩ := h a ha
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact q

/-- After `smallMask`: a mask in `kOk`, and ZF clear exactly for the status 2. -/
abbrev Zf : KIn → State → Prop := fun I t => KokM I t ∧ t.zf = some (!decide (I.st = 2))

/-- `smallMask`'s ZF, from correctness: clear exactly when `d ≤ 2^(8 pl)`,
the status 2. -/
theorem front_zf {I : KIn} {m₀ : Mem} {t : State} (F : Front I m₀ t) :
    KS I m₀ t ∧ Zf I t := by
  refine ⟨F.ks, ?_⟩
  obtain ⟨ok, hok, hiff, hzf⟩ := F.zf
  obtain ⟨ok', hok', -, hdd⟩ := F.d
  refine ⟨⟨ok, hok⟩, ?_⟩
  rw [hzf]
  refine congrArg (fun b => some (!b)) ?_
  have hW : 8 * I.pl = 16 * I.pl / 2 := by omega_using []
  have hst : I.st = 2 ↔ ∃ d, Spec.Rsa.inverse I.E I.L = some d ∧ d ≤ 2 ^ (8 * I.pl) := by
    simp only [KIn.st]
    constructor
    · intro h2
      unfold Proof.RsaKeyGen.keyOp at h2
      generalize hk : Spec.RsaKeyGen.keyFromPrimes (16 * I.pl) (Spec.Rsa.os2ip I.eb) (Spec.Rsa.os2ip I.pb)
        (Spec.Rsa.os2ip I.qb) = r at h2
      unfold Spec.RsaKeyGen.keyFromPrimes at hk
      have hswap : (if I.P₀ < I.Q₀ then (I.Q₀, I.P₀) else (I.P₀, I.Q₀)) = (I.P, I.Q) := by
        by_cases h : I.P₀ < I.Q₀ <;> simp [KIn.P, KIn.Q, h]
      rw [hswap] at hk
      dsimp only at hk
      rw [show Nat.lcm (I.P - 1) (I.Q - 1) = I.L from rfl, ← hW] at hk
      rcases hi : Spec.Rsa.inverse I.E I.L with _ | d
      · rw [hi] at hk; subst hk; simp [Proof.RsaKeyGen.keyStatus] at h2
      · rw [hi] at hk
        dsimp only at hk
        by_cases hd : d ≤ 2 ^ (8 * I.pl)
        · exact ⟨d, rfl, hd⟩
        · rw [ite_eq_right_iff.mpr (fun h => absurd h hd)] at hk
          obtain ⟨x, rfl⟩ : ∃ x, r = .inl x := by
            rw [← hk]
            split
            · exact ⟨_, rfl⟩
            · split <;> exact ⟨_, rfl⟩
          cases x <;> simp [Proof.RsaKeyGen.keyStatus] at h2
    · rintro ⟨d, hd, hsm⟩
      rw [keyOp_inr (by
        unfold Spec.RsaKeyGen.keyFromPrimes
        have hswap : (if I.P₀ < I.Q₀ then (I.Q₀, I.P₀) else (I.P₀, I.Q₀)) = (I.P, I.Q) := by
          by_cases h : I.P₀ < I.Q₀ <;> simp [KIn.P, KIn.Q, h]
        rw [hswap]
        dsimp only
        rw [show Nat.lcm (I.P - 1) (I.Q - 1) = I.L from rfl, hd, ← hW]
        dsimp only
        rw [ite_eq_left hsm])]
      rfl
  have hoo : ok' = ok := by
    rw [hok] at hok'
    cases ok <;> cases ok' <;> first | rfl | exact absurd hok' (by decide)
  subst hoo
  rw [show (8 * I.pl) = 8 * I.pl from rfl]
  cases hc : ok'
  · rw [hc] at hiff
    rw [Bool.and_false]
    refine (decide_eq_false fun h => ?_).symm
    obtain ⟨d, hd, _⟩ := hst.mp h
    exact absurd (hiff.mp ⟨d, hd⟩) (by simp)
  · rw [hc] at hiff
    obtain ⟨d, hd⟩ := hiff.mpr rfl
    rw [Bool.and_true, hdd d hd]
    exact decide_eq_decide.mpr ⟨fun h => hst.mpr ⟨d, hd, h⟩, fun h => by
      obtain ⟨d', hd', h'⟩ := hst.mp h
      rw [hd] at hd'; cases hd'; exact h'⟩

/-- The whole code. -/
theorem keyCode_ct : RelCT isa (Two KRel) code fun _ _ => True := by
  rw [code_eq]
  refine rs_app (R := Two (KG NF)) (by simp) (by simp [loadA]) start_ct ?_
  refine rs_app (R := Two (KG Zf)) (by simp [loadA]) (by simp) ?_ ?_
  · -- The front, and ZF from correctness.
    refine (RelCT.wpDep front_ct (F := fun σ t => ∀ a : KIn × Mem, (KS a.1 a.2 σ ∧ KLens a.1) →
        KS a.1 a.2 t ∧ Zf a.1 t) fun s₁ s₂ ⟨p, h₁, h₂⟩ => ⟨?_, ?_⟩).mono (fun _ _ h => h)
      fun t₁ t₂ ⟨_, σ₁, σ₂, ⟨p, h₁, h₂⟩, f₁, f₂⟩ => ?_
    · obtain ⟨I, m₀, -, -, hk, L, -⟩ := h₁
      exact wp_all (I, m₀) ⟨hk, L⟩ fun a ⟨hk', L'⟩ => WP.mono (front_k hk' L') fun t ⟨F, _⟩ => front_zf F
    · obtain ⟨I, m₀, -, -, hk, L, -⟩ := h₂
      exact wp_all (I, m₀) ⟨hk, L⟩ fun a ⟨hk', L'⟩ => WP.mono (front_k hk' L') fun t ⟨F, _⟩ => front_zf F
    obtain ⟨I₁, m₁, he₁, hs₁, hk₁, L₁, O₁, -⟩ := h₁
    obtain ⟨I₂, m₂, he₂, hs₂, hk₂, L₂, O₂, -⟩ := h₂
    obtain ⟨k₁, z₁⟩ := f₁ (I₁, m₁) ⟨hk₁, L₁⟩
    obtain ⟨k₂, z₂⟩ := f₂ (I₂, m₂) ⟨hk₂, L₂⟩
    exact ⟨p, ⟨I₁, m₁, he₁, hs₁, k₁, L₁, O₁, z₁⟩, ⟨I₂, m₂, he₂, hs₂, k₂, L₂, O₂, z₂⟩⟩
  -- The branch on the status 2.
  simp only [seqs]
  refine two_ite (fun p s₁ s₂ h₁ h₂ => ?_) ?_ ?_
  · obtain ⟨I₁, _, _, hs₁, _, _, _, -, z₁⟩ := h₁
    obtain ⟨I₂, _, _, hs₂, _, _, _, -, z₂⟩ := h₂
    simp only [eval, z₁, z₂, hs₁, hs₂]
  · exact zeros_ct.mono (fun _ _ ⟨p, ⟨h₁, _⟩, ⟨h₂, _⟩⟩ =>
      ⟨p, EG.of_kg (h₁.imp fun _ _ => trivial), EG.of_kg (h₂.imp fun _ _ => trivial)⟩) fun _ _ h => h
  · exact keyPart_ct.mono (fun _ _ ⟨p, ⟨h₁, _⟩, ⟨h₂, _⟩⟩ =>
      ⟨p, h₁.imp fun _ h => ⟨trivial, h.1⟩, h₂.imp fun _ h => ⟨trivial, h.1⟩⟩) fun _ _ h => h

/-- Byte lists with the same values. -/
theorem bytes_eq_of_toNat : ∀ {a b : List Byte}, a.map (·.toNat) = b.map (·.toNat) → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: a, y :: b, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, bytes_eq_of_toNat h.2]

/-- The public data of a state. -/
def kpubOf (s : State) : KP := ⟨(keyIn s).pub, (keyIn s).st⟩

/-- `vg_rsa_keygen_key` is constant time but for `e` and the status. -/
theorem keyCode_constantTime : ConstantTime isa keyCtr.pre keyCtr.pub code := by
  refine RelCT.constantTime (keyCode_ct.mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨kpubOf s₁, ⟨h₁, rfl, rfl⟩, h₂, ?_, ?_⟩)
    fun _ _ h => h)
  · obtain ⟨hdi, hsi, hdx, hcx, h8, h9, hsp, ha, hl⟩ := hp
    simp only [keyLeak] at hl
    have hlen : ((bytesAt s₁.mem (arg s₁ 8) (arg s₁ 9).toNat).map (·.toNat)).length =
        ((bytesAt s₂.mem (arg s₂ 8) (arg s₂ 9).toNat).map (·.toNat)).length := by
      simp only [List.length_map, bytesAt_length, ha 9 (by decide)]
    obtain ⟨he, -⟩ := List.append_inj hl hlen
    have hwr : s₂.wr = s₁.wr := by
      have w₁ := h₁.2.2.1
      have w₂ := h₂.2.2.1
      rw [w₁, w₂]
      simp only [hdi, hsi, hdx, hcx, h8, h9, ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide),
        ha 4 (by decide), ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 10 (by decide), ha 11 (by decide)]
    simp only [kpubOf, keyIn, KIn.pub, KQ.mk.injEq]
    exact ⟨(ha 10 (by decide)).symm, by rw [ha 11 (by decide)], by rw [h9], hdi.symm, hdx.symm, h8.symm,
      (ha 0 (by decide)).symm, (ha 2 (by decide)).symm, (ha 4 (by decide)).symm, (ha 6 (by decide)).symm,
      (ha 8 (by decide)).symm, by rw [ha 9 (by decide)], (bytes_eq_of_toNat he).symm, hwr, hsp.symm⟩
  · obtain ⟨-, -, -, -, -, -, -, ha, hl⟩ := hp
    simp only [keyLeak] at hl
    have hlen : ((bytesAt s₁.mem (arg s₁ 8) (arg s₁ 9).toNat).map (·.toNat)).length =
        ((bytesAt s₂.mem (arg s₂ 8) (arg s₂ 9).toNat).map (·.toNat)).length := by
      simp only [List.length_map, bytesAt_length, ha 9 (by decide)]
    obtain ⟨-, hs⟩ := List.append_inj hl hlen
    simp only [List.cons.injEq, and_true] at hs
    exact hs.symm

end VG.Proof.RsaKeyGen.X86_64.Key

end

/-! ## Verified -/
section

/-!
# An RSA key from its primes on x86-64: verified against the shared contract

With correctness (`keyCode_wp`), constant time (`keyCode_constantTime`) and
the shared contract's implication (`key_implies`), `code` is verified
(`key_verified`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem keyCode_correct (hmx : VG.Impl.RsaKeyGen.X86_64.Key.code.allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : keyCtr.pre s) :
    ∃ t s', Exec isa VG.Impl.RsaKeyGen.X86_64.Key.code s t s' ∧ abiPreserved s s' ∧ keyCtr.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := keyCode_wp s h
  exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hp⟩

instance keyProof : KeyProof := ⟨keyCode_correct, keyCode_constantTime⟩

/-- `vg_rsa_keygen_key`, given that its code never loads MXCSR (which the
registration file evaluates). -/
theorem key_verified
    (hmx : VG.Impl.RsaKeyGen.X86_64.Key.code.allInstrs (fun i => !loadsMxcsr i) = true := by decide +kernel) :
    Verified target VG.Impl.RsaKeyGen.X86_64.Key.code (Proof.RsaKeyGen.keyContract abi) :=
  Verified.of_correct (keyCode_correct hmx) keyCode_constantTime key_implies

end VG.Proof.RsaKeyGen.X86_64.Key

end
