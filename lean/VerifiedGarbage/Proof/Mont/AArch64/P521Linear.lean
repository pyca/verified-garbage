module

public import VerifiedGarbage.Impl.Mont.AArch64.P521Linear
public import VerifiedGarbage.Proof.Mont.AArch64.Chain
public import VerifiedGarbage.Proof.Mont.AArch64.Ops
import VerifiedGarbage.Proof.Mont.AArch64.Csub
import VerifiedGarbage.Proof.Ed25519.Word64
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! # P-521 linear arithmetic: carry chains and canonical reduction -/

@[expose] public section

namespace VG.Proof.Mont.AArch64.P521Linear

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Linear
open VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
open VG.Proof.Ed25519.Word64 (addCarry carryOut addCarry_value)

theorem supported_mod {M : Mod} {m : Nat} (h : supported M = true) (hm : M.ok m = true) :
    M.n = 9 ∧ m+1 = 512*(2^64)^8 := by
  simp only [supported,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  have hr := M.ok_red hm
  rw [h.2] at hr
  simp only [reduction,Red.ok,Bool.and_eq_true,beq_iff_eq] at hr
  have hd := hr.1.2
  have hl := hr.1.1.2
  change 512*(2^64)^7 = (m+1)/2^64 at hd
  have hrem := Nat.mod_add_div m (2^64)
  have he : 2^64*(512*(2^64)^7) = 512*(2^64)^8 := by decide +kernel
  exact ⟨h.1,by omega_using [hl, hd]⟩

/-- Two small products and the incoming limb carry fit in a double word. -/
private theorem cms_word_value (a b c d k : BitVec 64)
    (hc : c.toNat ≤ 16) (hd : d.toNat ≤ 16) (hk : k.toNat < 64) :
    let loA := a*c
    let hiA := BitVec.ofNat 64 (a.toNat*c.toNat/2^64)
    let loB := b*d
    let hiB := BitVec.ofNat 64 (b.toNat*d.toNat/2^64)
    let lo := addCarry loA loB false
    let hi := addCarry hiA hiB (carryOut loA loB false)
    let out := addCarry lo k false
    let carry := addCarry hi 0 (carryOut lo k false)
    out.toNat + 2^64*carry.toNat = a.toNat*c.toNat+b.toNat*d.toNat+k.toNat ∧
      carry.toNat < 64 := by
  intro loA hiA loB hiB lo hi out carry
  have hpa := Nat.mul_le_mul_left a.toNat hc
  have hpb := Nat.mul_le_mul_left b.toNat hd
  have ha := a.isLt
  have hb := b.isLt
  have hdivA : a.toNat*c.toNat/2^64 < 16 := by omega_using [hpa]
  have hdivB : b.toNat*d.toNat/2^64 < 16 := by omega_using [hpb]
  have hloA : loA.toNat = a.toNat*c.toNat%2^64 := BitVec.toNat_mul _ _
  have hloB : loB.toNat = b.toNat*d.toNat%2^64 := BitVec.toNat_mul _ _
  have hhiA : hiA.toNat = a.toNat*c.toNat/2^64 := by
    exact Nat.mod_eq_of_lt (by omega_using [hpa])
  have hhiB : hiB.toNat = b.toNat*d.toNat/2^64 := by
    exact Nat.mod_eq_of_lt (by omega_using [hpb])
  have e0 := addCarry_value loA loB false
  have e1 := addCarry_value hiA hiB (carryOut loA loB false)
  have e2 := addCarry_value lo k false
  have e3 := addCarry_value hi 0 (carryOut lo k false)
  have h0 := Bool.toNat_le (carryOut loA loB false)
  have h1 := Bool.toNat_le (carryOut lo k false)
  have hu := out.isLt
  have hv := carry.isLt
  have hh := hi.isLt
  simp only [Bool.toNat_false, Nat.add_zero, show (0 : BitVec 64).toNat = 0 from rfl,
    hloA,hloB,hhiA,hhiB] at e0 e1 e2 e3
  change lo.toNat + _ = _ at e0
  change hi.toNat + _ = _ at e1
  change out.toNat + _ = _ at e2
  change carry.toNat + _ = _ at e3
  have hhi : hi.toNat < 32 := by omega_using [hc, hd, hpa, hpb, ha, hb, hdivA, hdivB, hloA, hloB, hhiA, hhiB, h0, h1, hv, hh, e0, e1, e2, e3]
  constructor <;> omega_arith

/-- Execute one double-product limb, with the next carry bounded independently
of the secret operand words. -/
theorem cmsMul_ok (s : State) {r : Reg} (hr : r ∈ regs) (hz : s.gpr .x7 = 0)
    (hc : (s.gpr .x23).toNat ≤ 16) (hd : (s.gpr .x22).toNat ≤ 16)
    (hk : (s.gpr .x5).toNat < 64) :
    WP isa (.block (cmsMul r)) s fun t =>
      (t.gpr r).toNat + 2^64*(t.gpr .x5).toNat =
        (s.gpr .x1).toNat*(s.gpr .x23).toNat +
        (s.gpr .x2).toNat*(s.gpr .x22).toNat + (s.gpr .x5).toNat ∧
      (t.gpr .x5).toNat < 64 ∧ Keeps [r,.x4,.x6,.x17,.x5] s t := by
  have hn : r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x4 ∧ r ≠ .x5 ∧ r ≠ .x6 ∧
      r ≠ .x7 ∧ r ≠ .x17 ∧ r ≠ .x22 ∧ r ≠ .x23 :=
    (by decide : ∀ r ∈ regs, r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x4 ∧ r ≠ .x5 ∧ r ≠ .x6 ∧
      r ≠ .x7 ∧ r ≠ .x17 ∧ r ≠ .x22 ∧ r ≠ .x23) r hr
  rcases hn with ⟨h1,h2,h4,h5,h6,h7,h17,h22,h23⟩
  apply WP.of_runBlock
  simp only [cmsMul, runBlock_cons, runStep_some, runBlock_nil, reduceExec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, Size.bits, ite_true, ite_false,
    reduceCtorEq, h4,h5,h6,h17,
    Ne.symm h1,Ne.symm h2,Ne.symm h4,Ne.symm h5,Ne.symm h6,Ne.symm h7,
    Ne.symm h17,Ne.symm h22,Ne.symm h23, hz,
    Option.some.injEq, exists_eq_left']
  have hv := cms_word_value (s.gpr .x1) (s.gpr .x2) (s.gpr .x23) (s.gpr .x22)
    (s.gpr .x5) hc hd hk
  refine ⟨?_,?_,⟨?_,?_,?_,?_,?_⟩⟩
  · exact hv.1
  · exact hv.2
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hq.1,hq.2.1,hq.2.2.1,
      hq.2.2.2.1,hq.2.2.2.2,ite_false]
  · simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry]
  · simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry]
  · simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry]
  · simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]

def complementedWord (last : Bool) (x : BitVec 64) : BitVec 64 :=
  if last then (~~~x) &&& 511 else ~~~x

private theorem rotateZero (x : BitVec 64) : x.rotateRight 0 = x := by
  ext i hi
  simp [BitVec.getElem_rotateRight, hi]

theorem cmsComplement_ok (s : State) (last : Bool)
    (h16 : s.gpr .x16 = -1) (h24 : s.gpr .x24 = 511) :
    WP isa (.block (cmsComplement last)) s fun t =>
      t.gpr .x2 = complementedWord last (s.gpr .x2) ∧ Keeps [.x2] s t := by
  apply WP.of_runBlock
  cases last <;>
    simp only [cmsComplement, complementedWord, Bool.false_eq_true,
      ite_true, ite_false, List.append_nil, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, reduceExec, read_x,
      RegUpd.gpr_write, BitVec.setWidth_eq, Size.bits, Nat.reduceLT,
      reduceCtorEq, h16,h24,
      show (-1 : BitVec 64) = BitVec.allOnes 64 by decide, rotateZero,
      BitVec.allOnes_and, Option.some.injEq, exists_eq_left']
  all_goals
    refine ⟨True.intro,⟨?_,?_,?_,?_,?_⟩⟩
    · intro q hq
      simp only [List.mem_singleton] at hq
      simp only [RegUpd.gpr_write_of_ne _ _ _ hq]
    · simp only [RegUpd.mem_write]
    · simp only [RegUpd.rd_write]
    · simp only [RegUpd.wr_write]
    · simp only [RegUpd.sp_write]

/-- Load both input words before changing the result register. -/
theorem cmsRow_ok {s : State} {base : Addr} {size a b : Nat} (hs : Scr s base size)
    (ha : a+8 ≤ size) (hb : b+8 ≤ size) (ha8 : a%8 = 0) (hb8 : b%8 = 0)
    {r : Reg} (hr : r ∈ regs) (last : Bool)
    (hz : s.gpr .x7 = 0) (h16 : s.gpr .x16 = -1) (h24 : s.gpr .x24 = 511)
    (hc : (s.gpr .x23).toNat ≤ 16) (hd : (s.gpr .x22).toNat ≤ 16)
    (hk : (s.gpr .x5).toNat < 64) :
    WP isa (.block (cmsRow r last a b)) s fun t =>
      (t.gpr r).toNat + 2^64*(t.gpr .x5).toNat =
        (word s.mem base a).toNat*(s.gpr .x23).toNat +
        (complementedWord last (word s.mem base b)).toNat*(s.gpr .x22).toNat +
        (s.gpr .x5).toNat ∧
      (t.gpr .x5).toNat < 64 ∧ Keeps [.x1,.x2,r,.x4,.x6,.x17,.x5] s t := by
  rw [cmsRow, List.append_assoc, show ([ld .x1 a,ld .x2 b] : List Instr) =
    [ld .x1 a] ++ [ld .x2 b] from rfl]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ldR_ok hs.ptr ha ha8 .x1) fun u ⟨hu,ku,_⟩ => ?_
  have hs1 := hs.of_keeps ku (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ldR_ok hs1.ptr hb hb8 .x2) fun v ⟨hv,kv,_⟩ => ?_
  have h16v : v.gpr .x16 = -1 :=
    (kv.gpr .x16 (by decide)).trans ((ku.gpr .x16 (by decide)).trans h16)
  have h24v : v.gpr .x24 = 511 :=
    (kv.gpr .x24 (by decide)).trans ((ku.gpr .x24 (by decide)).trans h24)
  rw [WP.block_append_iff]
  refine WP.mono (cmsComplement_ok v last h16v h24v) fun w ⟨hw,kw⟩ => ?_
  have hz1 : w.gpr .x7 = 0 :=
    (kw.gpr .x7 (by decide)).trans ((kv.gpr .x7 (by decide)).trans
      ((ku.gpr .x7 (by decide)).trans hz))
  have hc1 : w.gpr .x23 = s.gpr .x23 :=
    (kw.gpr .x23 (by decide)).trans ((kv.gpr .x23 (by decide)).trans (ku.gpr .x23 (by decide)))
  have hd1 : w.gpr .x22 = s.gpr .x22 :=
    (kw.gpr .x22 (by decide)).trans ((kv.gpr .x22 (by decide)).trans (ku.gpr .x22 (by decide)))
  have hk1 : w.gpr .x5 = s.gpr .x5 :=
    (kw.gpr .x5 (by decide)).trans ((kv.gpr .x5 (by decide)).trans (ku.gpr .x5 (by decide)))
  refine WP.mono (cmsMul_ok w hr hz1 (hc1 ▸ hc) (hd1 ▸ hd) (hk1 ▸ hk))
    fun t ⟨ht,hkt,kt⟩ => ?_
  rw [kw.gpr .x1 (by decide), kv.gpr .x1 (by decide), hu, hw,hv,
    ku.mem,hc1,hd1,hk1] at ht
  exact ⟨ht,hkt,(ku.mono (by sub_regs)).trans ((kv.mono (by sub_regs)).trans
    ((kw.mono (by sub_regs)).trans (kt.mono (by sub_regs))))⟩

def complementedValue (m : Mem) (base : Addr) (b : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => (complementedWord (k == 0) (word m base b)).toNat +
      2^64*complementedValue m base (b+8) k

def cmsScratch : List Reg := [.x1,.x2,.x4,.x6,.x17,.x5]

theorem cmsInit_ok (s : State) {C D : Nat} (hC : C ≤ 16) (hD : D ≤ 16) :
    WP isa (.block (cmsInit C D)) s fun t =>
      t.gpr .x7 = 0 ∧ t.gpr .x16 = -1 ∧ t.gpr .x5 = 0 ∧
      (t.gpr .x23).toNat = C ∧ (t.gpr .x22).toNat = D ∧ t.gpr .x24 = 511 ∧
      Keeps [.x7,.x16,.x5,.x23,.x22,.x24] s t := by
  apply WP.of_runBlock
  simp only [cmsInit, runBlock_cons, runStep_some, runBlock_nil, reduceExec, read_x,
    RegUpd.gpr_write, BitVec.setWidth_eq, Size.bits, Nat.reduceMul,
    Nat.reduceLT, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨by decide,by decide,by decide,?_,?_,by decide,⟨?_,?_,?_,?_,?_⟩⟩
  · simp only [BitVec.shiftLeft_zero,BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    omega_using [hC]
  · simp only [BitVec.shiftLeft_zero,BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    omega_using [hD]
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hq
    simp only [RegUpd.gpr_write, hq.1,hq.2.1,hq.2.2.1,hq.2.2.2.1,hq.2.2.2.2.1,
      hq.2.2.2.2.2,ite_false]
  · simp only [RegUpd.mem_write]
  · simp only [RegUpd.rd_write]
  · simp only [RegUpd.wr_write]
  · simp only [RegUpd.sp_write]

theorem cmsRows_ok {size : Nat} : ∀ (rs : List Reg) {s : State} {base : Addr} {a b : Nat},
    Scr s base size → a+8*rs.length ≤ size → b+8*rs.length ≤ size →
    a%8 = 0 → b%8 = 0 → rs.Nodup → (∀ r ∈ rs, r ∈ regs) →
    s.gpr .x7 = 0 → s.gpr .x16 = -1 → s.gpr .x24 = 511 →
    (s.gpr .x23).toNat ≤ 16 → (s.gpr .x22).toNat ≤ 16 → (s.gpr .x5).toNat < 64 →
    WP isa (.block (cmsRows rs a b)) s fun t =>
      regsVal t rs + (2^64)^rs.length*(t.gpr .x5).toNat =
        wordsVal s.mem base a rs.length*(s.gpr .x23).toNat +
        complementedValue s.mem base b rs.length*(s.gpr .x22).toNat + (s.gpr .x5).toNat ∧
      (t.gpr .x5).toNat < 64 ∧ Keeps (cmsScratch++rs) s t
  | [], s, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk =>
    WP.block_nil ⟨by simp [regsVal,wordsVal,complementedValue],hk,
      ⟨fun _ _ => rfl,rfl,rfl,rfl,rfl⟩⟩
  | r::rs, s, base, a, b, hs, ha, hb, ha8, hb8, hnd, hregs, hz, h16, h24, hc, hd, hk => by
    have hr := hregs r (List.mem_cons_self ..)
    have htail : ∀ q ∈ rs, q ∈ regs := fun q hq => hregs q (List.mem_cons_of_mem _ hq)
    have hkeep : ∀ q ∈ [Reg.x0,.x7,.x16,.x24,.x23,.x22],
        q ∉ [.x1,.x2,r,.x4,.x6,.x17,.x5] := by
      have hn : ∀ q ∈ [Reg.x0,.x7,.x16,.x24,.x23,.x22], q ≠ r :=
        (by decide : ∀ r ∈ regs, ∀ q ∈ [Reg.x0,.x7,.x16,.x24,.x23,.x22], q ≠ r) r hr
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(by decide : ∀ q ∈ [Reg.x0,.x7,.x16,.x24,.x23,.x22], q ≠ .x1) q hq,
        (by decide : ∀ q ∈ [Reg.x0,.x7,.x16,.x24,.x23,.x22], q ≠ .x2) q hq,
        hn q hq,
        (by decide : ∀ q ∈ [Reg.x0,.x7,.x16,.x24,.x23,.x22], q ≠ .x4) q hq,
        (by decide : ∀ q ∈ [Reg.x0,.x7,.x16,.x24,.x23,.x22], q ≠ .x6) q hq,
        (by decide : ∀ q ∈ [Reg.x0,.x7,.x16,.x24,.x23,.x22], q ≠ .x17) q hq,
        (by decide : ∀ q ∈ [Reg.x0,.x7,.x16,.x24,.x23,.x22], q ≠ .x5) q hq⟩
    rw [cmsRows, WP.block_append_iff]
    refine WP.mono (cmsRow_ok hs (by simp only [List.length_cons] at ha; omega_arith)
      (by simp only [List.length_cons] at hb; omega_arith) ha8 hb8 hr rs.isEmpty
      hz h16 h24 hc hd hk) fun u ⟨hu,hku,ku⟩ => ?_
    have hs1 := hs.of_keeps ku (hkeep .x0 (by decide))
    have hc1 := ku.gpr .x23 (hkeep .x23 (by decide))
    have hd1 := ku.gpr .x22 (hkeep .x22 (by decide))
    refine WP.mono (cmsRows_ok rs hs1
      (by simp only [List.length_cons] at ha; omega_arith)
      (by simp only [List.length_cons] at hb; omega_arith) (by omega_arith) (by omega_arith)
      (List.nodup_cons.mp hnd).2 htail
      ((ku.gpr .x7 (hkeep .x7 (by decide))).trans hz)
      ((ku.gpr .x16 (hkeep .x16 (by decide))).trans h16)
      ((ku.gpr .x24 (hkeep .x24 (by decide))).trans h24)
      (hc1 ▸ hc) (hd1 ▸ hd) hku) fun t ⟨ht,hkt,kt⟩ => ?_
    have hrn : r ∉ cmsScratch :=
      (by decide : ∀ r ∈ regs, r ∉ cmsScratch) r hr
    have hr1 : t.gpr r = u.gpr r := kt.gpr r (by
      simp only [List.mem_append,not_or]; exact ⟨hrn,(List.nodup_cons.mp hnd).1⟩)
    have hlast : rs.isEmpty = (rs.length == 0) := by cases rs <;> rfl
    simp only [ku.mem,hc1,hd1] at ht
    refine ⟨?_,hkt,(ku.mono (by unfold cmsScratch; sub_regs)).trans (kt.mono (by sub_regs))⟩
    simp only [List.length_cons, regsVal,wordsVal,complementedValue,hr1,← hlast]
    rw [Nat.pow_succ' (m := 2^64) (n := rs.length)]
    have e := congrArg (fun n => 2^64*n) ht
    simp only [Nat.mul_add] at e
    simp only [Nat.add_mul, Nat.mul_assoc]
    omega_using [hu, ht]

theorem adcReg_ok (s : State) (r : Reg) (hz : s.gpr .x7 = 0) :
    WP isa (.block [.adcs .x r r .x7]) s fun t =>
      (t.gpr r).toNat + 2^64*t.c.toNat = (s.gpr r).toNat+s.c.toNat ∧
      Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,
    RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,BitVec.setWidth_eq,
    ite_true,hz,Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨?_,?_,?_,?_,?_⟩⟩
  · simpa only [Size.bits,addCarry,carryOut,
      show (0 : BitVec 64).toNat = 0 from rfl,Nat.add_zero] using
      addCarry_value (s.gpr r) 0 s.c
  · intro q hq
    simp only [List.mem_singleton] at hq
    simp only [RegUpd.gpr_addWithCarry,hq,ite_false]
  · simp only [RegUpd.mem_addWithCarry]
  · simp only [RegUpd.rd_addWithCarry]
  · simp only [RegUpd.wr_addWithCarry]
  · simp only [RegUpd.sp_addWithCarry]

theorem carryRegs_ok : ∀ (rs : List Reg) (s : State), rs.Nodup → .x7 ∉ rs →
    s.gpr .x7 = 0 →
    WP isa (.block (rs.map fun r => .adcs .x r r .x7)) s fun t =>
      regsVal t rs+(2^64)^rs.length*t.c.toNat = regsVal s rs+s.c.toNat ∧ Keeps rs s t
  | [], s, _, _, _ => WP.block_nil ⟨by simp [regsVal],⟨fun _ _ => rfl,rfl,rfl,rfl,rfl⟩⟩
  | r::rs, s, hnd, h7, hz => by
    rw [List.map_cons,show (.adcs .x r r .x7 :: rs.map (fun q => .adcs .x q q .x7) : List Instr) =
      ([.adcs .x r r .x7] : List Instr) ++ rs.map (fun q => .adcs .x q q .x7) from rfl,WP.block_append_iff]
    refine WP.mono (adcReg_ok s r hz) fun u ⟨hu,ku⟩ => ?_
    have h7r : .x7 ≠ r := fun e => h7 (List.mem_cons.mpr (Or.inl e))
    have h7rs : .x7 ∉ rs := fun h => h7 (List.mem_cons_of_mem _ h)
    refine WP.mono (carryRegs_ok rs u (List.nodup_cons.mp hnd).2 h7rs
      ((ku.gpr .x7 (by simpa only [List.mem_singleton] using h7r)).trans hz))
      fun t ⟨ht,kt⟩ => ?_
    have hr : t.gpr r = u.gpr r := kt.gpr r (List.nodup_cons.mp hnd).1
    have hrest : regsVal u rs = regsVal s rs := regsVal_congr fun q hq => ku.gpr q (by
      simp only [List.mem_singleton]
      exact fun e => (List.nodup_cons.mp hnd).1 (e ▸ hq))
    rw [hrest] at ht
    refine ⟨?_,(ku.mono (by sub_regs)).trans (kt.mono (by sub_regs))⟩
    simp only [regsVal,List.length_cons,hr]
    rw [Nat.pow_succ' (m := 2^64) (n := rs.length),Nat.mul_assoc]
    have he := congrArg (fun n => 2^64*n) ht
    simp only [Nat.mul_add] at he
    omega_using [hu, ht]

/-- A word is corrected by the borrow and stored, preserving all other registers. -/
theorem correctStep_ok {s : State} {base : Addr} {size o : Nat} (hs : Scr s base size)
    (r : Reg) (hr0 : r ≠ .x0) (hz : s.gpr .x7 = 0)
    (ho : o + 8 ≤ size) (ho8 : o % 8 = 0) :
    WP isa (.block [.sbcs .x r r .x7, st r o]) s fun t =>
      (word t.mem base o).toNat + (!s.c).toNat =
        (s.gpr r).toNat + 2^64 * (!t.c).toNat ∧
      KeepRegs [r] s t ∧ Outside base o 8 s.mem t.mem := by
  rw [show ([.sbcs .x r r .x7, st r o] : List Instr) =
    [.sbcs .x r r .x7] ++ [st r o] from rfl, WP.block_append_iff]
  refine WP.mono (subc_ok s r r .x7 false rfl) fun u ⟨hu,hc,hk⟩ => ?_
  have hs' := hs.of_keeps hk (by simp [Ne.symm hr0])
  refine WP.mono (stR_ok hs'.ptrW (d := o) ho ho8 r) fun t ht => ?_
  simp only [Bool.false_eq_true, ite_false] at hu hc
  have eq := sub_borrow (s.gpr r) (s.gpr .x7) s.c
  rw [← hu, ← hc, hz, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at eq
  refine ⟨?_, ?_, ?_⟩
  · rw [ht, word_writeW_self]
    exact eq
  · refine ⟨fun q hq => ?_, ?_, ?_, ?_⟩
    · rw [ht]
      exact hk.gpr q hq
    · rw [ht]; exact hk.rd
    · rw [ht]; exact hk.wr
    · rw [ht]; exact hk.sp
  · rw [ht, hk.mem]
    exact writeW_outside _ _ _ (by have := hs.nowrap; omega_arith)

/-- A correction chain, with the outgoing borrow, changes only its output array. -/
theorem correctStore_ok {size : Nat} : ∀ (rs : List Reg) {s : State} {base : Addr} {o : Nat},
    Scr s base size → o + 8 * rs.length ≤ size → o % 8 = 0 → rs.Nodup →
    .x0 ∉ rs → .x7 ∉ rs → s.gpr .x7 = 0 →
    WP isa (.block (correctStore rs o)) s fun t =>
      wordsVal t.mem base o rs.length + (!s.c).toNat =
        regsVal s rs + 2^(64*rs.length) * (!t.c).toNat ∧
      KeepRegs rs s t ∧ Outside base o (8*rs.length) s.mem t.mem
  | [], s, base, o, _, _, _, _, _, _, _ =>
    WP.block_nil ⟨by simp [wordsVal, regsVal],
      ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | r :: rs, s, base, o, hs, ho, ho8, hnd, h0, h7, hz => by
    have hn := hs.nowrap
    simp only [List.length_cons] at ho
    simp only [List.mem_cons, not_or] at h0 h7
    rw [correctStore, WP.block_append_iff]
    refine WP.mono (correctStep_ok hs r (Ne.symm h0.1) hz
      (by omega_arith) ho8) fun u ⟨hu,ku,Ou⟩ => ?_
    have hs' := hs.of_keepRegs ku (by simpa using h0.1)
    have hz' : u.gpr .x7 = 0 := (ku.gpr .x7 (by simpa using h7.1)).trans hz
    refine WP.mono (correctStore_ok rs hs' (o := o+8) (by omega_arith)
      (by omega_arith) (List.nodup_cons.mp hnd).2 h0.2 h7.2 hz') fun t ⟨ht,kt,Ot⟩ => ?_
    have hr : regsVal u rs = regsVal s rs := regsVal_congr fun q hq => ku.gpr q (by
      simp only [List.mem_singleton]; exact fun e => (List.nodup_cons.mp hnd).1 (e ▸ hq))
    rw [hr] at ht
    refine ⟨?_, (ku.mono (by sub_regs)).trans (kt.mono (by sub_regs)), ?_⟩
    · rw [List.length_cons, wordsVal, Ot.word (by omega_arith) (by omega_arith), regsVal]
      simp only [pow64_succ]
      rw [Nat.mul_assoc]
      omega_arith
    · intro x hx
      simp only [List.length_cons] at hx
      rw [Ot x (by omega_arith), Ou x (by omega_arith)]

theorem mask511_value (x : BitVec 64) : (x &&& 511).toNat = x.toNat % 512 := by
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 9

def limbCapacity : Nat → Nat
  | 0 => 1
  | 1 => 512
  | k+2 => 2^64*limbCapacity (k+1)

theorem complementedValue_eq (m : Mem) (base : Addr) : ∀ (k b : Nat),
    wordsVal m base b k < limbCapacity k →
    complementedValue m base b k + wordsVal m base b k = limbCapacity k-1
  | 0, _, _ => by simp [wordsVal,complementedValue,limbCapacity]
  | 1, b, h => by
    have hw : (word m base b).toNat < 512 := by
      simpa only [wordsVal,limbCapacity,Nat.mul_zero,Nat.add_zero] using h
    simp only [complementedValue,complementedWord,wordsVal,limbCapacity,
      beq_self_eq_true,ite_true,Nat.mul_zero,Nat.add_zero,mask511_value,BitVec.toNat_not]
    omega_using [hw]
  | k+2, b, h => by
    have ht : wordsVal m base (b+8) (k+1) < limbCapacity (k+1) := by
      change (word m base b).toNat + 2^64*wordsVal m base (b+8) (k+1) <
        2^64*limbCapacity (k+1) at h
      omega_using [h]
    have he := complementedValue_eq m base (k+1) (b+8) ht
    have hw := (word m base b).isLt
    have hn : ((k+1) == 0) = false := by simp
    rw [complementedValue,wordsVal]
    simp only [hn,complementedWord,Bool.false_eq_true,ite_false,BitVec.toNat_not]
    change _ = 2^64*limbCapacity (k+1)-1
    omega_using [ht, he]

theorem mask512_value (x : BitVec 64) (hx : x.toNat < 1024) :
    (x &&& 512).toNat = 512 * (x.toNat / 512) := by
  have he := BitVec.and_twoPow x 9
  rw [show BitVec.twoPow 64 9 = (512 : BitVec 64) from rfl] at he
  rw [he,BitVec.getLsbD,Nat.testBit_eq_decide_div_mod_eq]
  rcases (show x.toNat / 512 = 0 ∨ x.toNat / 512 = 1 by omega_using [hx]) with hq | hq
  · simp [hq]
  · simp [hq]

theorem mask512_carry (x : BitVec 64) (hx : x.toNat < 1024) :
    (VG.Proof.Ed25519.Word64.carryOut (x &&& 512) (~~~512) true).toNat = x.toNat / 512 := by
  rw [VG.Proof.Ed25519.Word64.carryOut, mask512_value x hx]
  rcases (show x.toNat / 512 = 0 ∨ x.toNat / 512 = 1 by omega_using [hx]) with hq | hq
  · rw [hq]; decide
  · rw [hq]; decide

private theorem power512 : 2^(64*8) = (2^64)^8 := by decide +kernel

theorem regs_split (s : State) :
    regsVal s regs = regsVal s (regs.take 8) + (2^64)^8 * (s.gpr .x21).toNat := by
  have er : regs = regs.take 8 ++ [.x21] := by decide
  have one : regsVal s [.x21] = (s.gpr .x21).toNat := by
    simp only [regsVal, Nat.mul_zero, Nat.add_zero]
  have h := regsVal_append s (regs.take 8) [.x21]
  have hp : 2^(64*(regs.take 8).length) = (2^64)^8 :=
    (congrArg (fun n => 2^(64*n)) (show (regs.take 8).length = 8 by decide)).trans
      power512
  have ht := (congrArg (fun a : Nat => regsVal s (regs.take 8) + a*regsVal s [.x21]) hp).trans
    (congrArg (fun b : Nat => regsVal s (regs.take 8) + (2^64)^8*b) one)
  exact (congrArg (regsVal s) er).trans (h.trans ht)

/-- The short canonical prefix, executed once without expanding register updates. -/
theorem canonicalPrefix_raw (s : State) :
    WP isa (.block canonicalPrefix) s fun t =>
      t.gpr .x21 = s.gpr .x21 &&& 511 ∧
      t.c = VG.Proof.Ed25519.Word64.carryOut (s.gpr .x21 &&& 512) (~~~512) true ∧
      Keeps [.x2,.x3,.x21] s t := by
  apply WP.of_runBlock
  simp only [canonicalPrefix, runBlock_cons, runStep_some, runBlock_nil, reduceExec,
    read_x, RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    RegUpd.c_write, BitVec.setWidth_eq, Size.bits, Nat.reduceMul, Nat.reduceLT,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write_of_ne _ _ _ hr.2.2,
      RegUpd.gpr_write_of_ne _ _ _ hr.2.1,
      RegUpd.gpr_addWithCarry, hr.1, ite_false,
      RegUpd.gpr_write_of_ne _ _ _ hr.1]
  · simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry]
  · simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry]
  · simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry]
  · simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]

theorem regs_low_lt (s : State) : regsVal s (regs.take 8) < (2^64)^8 := by
  have hp : 2^(64*(regs.take 8).length) = (2^64)^8 :=
    (congrArg (fun n => 2^(64*n)) (show (regs.take 8).length = 8 by decide)).trans power512
  exact lt_of_lt_of_eq (regsVal_lt s (regs.take 8)) hp

theorem cmsFoldPrefix_ok (s : State) (h24 : s.gpr .x24 = 511) :
    WP isa (.block cmsFoldPrefix) s fun t =>
      (t.gpr .x8).toNat + 2^64*t.c.toNat =
        (s.gpr .x8).toNat+(s.gpr .x21).toNat/512+1 ∧
      (t.gpr .x21).toNat = (s.gpr .x21).toNat%512 ∧ Keeps [.x2,.x21,.x8] s t := by
  apply WP.of_runBlock
  simp only [cmsFoldPrefix,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,BitVec.setWidth_eq,
    Size.bits,Nat.reduceLT,ite_true,ite_false,reduceCtorEq,h24,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,mask511_value _,⟨?_,?_,?_,?_,?_⟩⟩
  · have hq : ((s.gpr .x21) >>> 9).toNat = (s.gpr .x21).toNat/512 := by
      rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
    have hi := (s.gpr .x21).isLt
    have he := addCarry_value (s.gpr .x8) (((s.gpr .x21) >>> 9)+1) false
    simp only [addCarry,carryOut,Bool.toNat_false,Nat.add_zero,BitVec.add_zero,
      BitVec.toNat_add,hq,show (1 : BitVec 64).toNat = 1 from rfl] at he
    simp only [BitVec.toNat_add,hq,show (1#64).toNat = 1 from rfl,
      Bool.toNat_false,BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero,Nat.mod_mod,
      Nat.mod_eq_of_lt (show (s.gpr .x21).toNat/512+1 < 2^64 by omega_using [])] at he ⊢
    omega_using [he]
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hq
    simp only [RegUpd.gpr_write,RegUpd.gpr_addWithCarry,hq.1,hq.2.1,hq.2.2,ite_false]
  · simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry]
  · simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry]
  · simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry]
  · simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]

/-- The prefix partitions a value below bit 522 into bit 521 and its low part. -/
theorem canonicalPrefix_ok (s : State) (hbound : regsVal s regs < 1024*(2^64)^8) :
    WP isa (.block canonicalPrefix) s fun t =>
      regsVal t regs + (512*(2^64)^8)*t.c.toNat = regsVal s regs ∧
      regsVal t regs < 512*(2^64)^8 ∧ Keeps [.x2,.x3,.x21] s t := by
  have htop : (s.gpr .x21).toNat < 1024 := by
    rw [regs_split s] at hbound
    omega_using [hbound]
  refine WP.mono (canonicalPrefix_raw s) fun t ⟨h21,hc,hk⟩ => ?_
  have hlow : regsVal t (regs.take 8) = regsVal s (regs.take 8) :=
    regsVal_congr fun r hr => hk.gpr r ((show ∀ r ∈ regs.take 8, r ∉ [Reg.x2,.x3,.x21] by decide) r hr)
  have hl := regs_low_lt s
  have hm := Nat.mod_lt (s.gpr .x21).toNat (by decide : 0 < 512)
  refine ⟨?_, ?_, hk⟩
  · rw [regs_split t, hlow, h21, mask511_value, hc, mask512_carry _ htop, regs_split s]
    omega_using []
  · rw [regs_split t, hlow, h21, mask511_value]
    omega_using [hl]

/-- The final borrow chain canonically reduces a folded Mersenne sum.
The statement is independent of the word width and the particular prime. -/
theorem canonical_correction {p R n v w : Nat} {c d : Bool}
    (hn : n < 2*p) (hv : v < p+1) (hw : w < R)
    (ev : v + (p+1)*c.toNat = n+1)
    (ew : w + (!c).toNat = v + R*(!d).toNat) :
    w = n % p ∧ w < p := by
  cases c <;> cases d <;>
    simp only [Bool.toNat_false, Bool.toNat_true, Bool.not_false, Bool.not_true,
      Nat.mul_zero, Nat.mul_one, Nat.add_zero] at *
  · omega_using [hw, ev, ew]
  · have en : w = n := by omega_using [ev, ew]
    have hwp : w < p := by omega_using [hv, ew]
    exact ⟨en ▸ (Nat.mod_eq_of_lt (en ▸ hwp)).symm, hwp⟩
  · omega_using [hw, ew]
  · have en : n = w+p := by omega_using [ev, ew]
    have hwp : w < p := by omega_using [hn, ev, ew]
    refine ⟨?_, hwp⟩
    rw [en, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hwp]

/-- Canonical storage after a sum or a Mersenne fold. Aliasing is unrestricted:
all input words are already in registers when this block starts. -/
theorem canonicalStore_ok {s : State} {base : Addr} {size o p n : Nat}
    (hs : Scr s base size) (ho : o+72 ≤ size) (ho8 : o%8 = 0)
    (hm : p+1 = 512*(2^64)^8) (hn : n < 2*p)
    (hval : regsVal s regs = n+1) (hz : s.gpr .x7 = 0) :
    WP isa (.block (canonicalStore o)) s fun t =>
      wordsVal t.mem base o 9 = n%p ∧ wordsVal t.mem base o 9 < p ∧
      KeepRegs (([.x2,.x3,.x21] : List Reg) ++ regs) s t ∧ Outside base o 72 s.mem t.mem := by
  have hbound : regsVal s regs < 1024*(2^64)^8 := by rw [hval]; omega_using [hm, hn]
  rw [canonicalStore, WP.block_append_iff]
  refine WP.mono (canonicalPrefix_ok s hbound) fun u ⟨ep,hv,hk⟩ => ?_
  have hs' := hs.of_keeps hk (by decide)
  have hz' : u.gpr .x7 = 0 := (hk.gpr .x7 (by decide)).trans hz
  have hlen : regs.length = 9 := by decide
  refine WP.mono (correctStore_ok regs hs' (o := o) (by rw [hlen]; omega_arith)
    ho8 (by decide) (by decide) (by decide) hz') fun t ⟨hout,kt,Ot⟩ => ?_
  rw [←hm, hval] at ep
  have hv' : regsVal u regs < p+1 := lt_of_lt_of_eq hv hm.symm
  have hw := wordsVal_lt t.mem base o regs.length
  have hc := canonical_correction hn hv' hw ep hout
  refine ⟨hc.1, hc.2, ?_, ?_⟩
  · have kp : KeepRegs [.x2,.x3,.x21] s u := ⟨hk.gpr,hk.rd,hk.wr,hk.sp⟩
    exact (kp.mono (by sub_regs)).trans (kt.mono (by sub_regs))
  · rw [hlen, hk.mem] at Ot
    exact Ot

theorem addInit_ok (s : State) :
    WP isa (.block addInit) s fun t => t.gpr .x7 = 0 ∧ t.c = true ∧ Keeps [.x7] s t := by
  apply WP.of_runBlock
  simp only [addInit, zero7, runBlock_cons, runStep_some, runBlock_nil, reduceExec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, BitVec.setWidth_eq,
    Size.bits, Nat.reduceMul, Nat.reduceLT, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨by decide, by decide, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro r hr
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_addWithCarry, hr, ite_false, RegUpd.gpr_write_of_ne _ _ _ hr]
  · simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry]
  · simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry]
  · simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry]
  · simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]

theorem subtraction_correction {p R a b d w : Nat} {c co : Bool}
    (ha : a < p) (hb : b < p) (hR : p+1 ≤ R) (hmod : R%(p+1) = 0)
    (hd : d < R) (hw : w < R)
    (ed : d+b = a+R*(!c).toNat)
    (ew : w+(!c).toNat = d+R*(!co).toNat) :
    w%(p+1) = (a+p-b)%p ∧ w%(p+1) < p := by
  cases c <;> cases co <;>
    simp only [Bool.toNat_false, Bool.toNat_true, Bool.not_false, Bool.not_true,
      Nat.mul_zero, Nat.mul_one, Nat.add_zero] at *
  · omega_using [hb, hR, hw, ed, ew]
  · let z := a+p-b
    have hz : z < p := by dsimp only [z]; omega_using [ha, hd, ed]
    have e : w = (R-(p+1))+z := by dsimp only [z]; omega_using [hb, hR, ed, ew]
    have hm : (R-(p+1))%(p+1) = 0 := (Nat.mod_eq_sub_mod hR).symm.trans hmod
    have hmz : w%(p+1) = z := by
      rw [e, Nat.add_mod, hm, Nat.zero_add, Nat.mod_mod,
        Nat.mod_eq_of_lt (show z < p+1 by omega_using [hz])]
    exact ⟨hmz.trans (Nat.mod_eq_of_lt hz).symm, by rw [hmz]; exact hz⟩
  · omega_using [hw, ew]
  · have hwp : w < p := by omega_using [ha, ed, ew]
    have e : a+p-b = w+p := by omega_using [ed, ew]
    have hm : w%(p+1) = w := Nat.mod_eq_of_lt (by omega_using [hwp])
    have hn : (a+p-b)%p = w := by
      rw [e, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hwp]
    exact ⟨hm.trans hn.symm, by rw [hm]; exact hwp⟩

private theorem power_regs9 : 2^(64*regs.length) = (2^64)^9 := by decide +kernel
private theorem radix_gap : 1024*(2^64)^8 < (2^64)^9 := by decide +kernel

theorem maskTop_ok (s : State) :
    WP isa (.block [.movz .x .x3 511 0, .logic .and .x .x21 .x21 .x3]) s fun t =>
      t.gpr .x21 = s.gpr .x21 &&& 511 ∧ Keeps [.x3,.x21] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, read_x,
    RegUpd.gpr_write, BitVec.setWidth_eq, Size.bits, Nat.reduceMul, Nat.reduceLT,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_write_of_ne _ _ _ hr.2, RegUpd.gpr_write_of_ne _ _ _ hr.1]
  · simp only [RegUpd.mem_write]
  · simp only [RegUpd.rd_write]
  · simp only [RegUpd.wr_write]
  · simp only [RegUpd.sp_write]

theorem maskStoreTop_ok {s : State} {base : Addr} {size o : Nat}
    (hs : Scr s base size) (ho : o+8 ≤ size) (ho8 : o%8 = 0) :
    WP isa (.block (maskStoreTop o)) s fun t =>
      (word t.mem base o).toNat = (s.gpr .x21).toNat%512 ∧
      KeepRegs [.x3,.x21] s t ∧ Outside base o 8 s.mem t.mem := by
  rw [maskStoreTop, show ([.movz .x .x3 511 0, .logic .and .x .x21 .x21 .x3,
    st .x21 o] : List Instr) =
    [.movz .x .x3 511 0, .logic .and .x .x21 .x21 .x3] ++ [st .x21 o] from rfl,
    WP.block_append_iff]
  refine WP.mono (maskTop_ok s) fun u ⟨hu,ku⟩ => ?_
  have hs1 := hs.of_keeps ku (by decide)
  refine WP.mono (stR_ok hs1.ptrW (d := o) ho ho8 .x21) fun t ht => ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [ht, word_writeW_self, hu, mask511_value]
  · refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
    · rw [ht]; exact ku.gpr r hr
    · rw [ht]; exact ku.rd
    · rw [ht]; exact ku.wr
    · rw [ht]; exact ku.sp
  · rw [ht, ku.mem]
    exact writeW_outside _ _ _ (by have := hs.nowrap; omega_arith)

theorem masked_value {B lo hi : Nat} (hlo : lo < B) :
    (lo+B*hi)%(512*B) = lo+B*(hi%512) := by
  have hm := Nat.mod_lt hi (by decide : 0 < 512)
  have he : lo+B*hi = (lo+B*(hi%512)) + (512*B)*(hi/512) := by
    have hd := Nat.mod_add_div hi 512
    rw [Nat.mul_comm 512 B, Nat.mul_assoc]
    rw [Nat.add_assoc, ← Nat.mul_add, hd]
  rw [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  have hb := Nat.mul_le_mul_left B (show hi%512 ≤ 511 by omega_using [])
  omega_using [hlo, hb]

private theorem wordsVal_lt_radix (m : Mem) (base : Addr) (o k : Nat) :
    wordsVal m base o k < (2^64)^k := by
  have h := wordsVal_lt m base o k
  rw [Nat.pow_mul] at h
  exact h

private theorem wordsVal_top_radix (m : Mem) (base : Addr) (o k : Nat) :
    wordsVal m base o (k+1) =
      wordsVal m base o k + (2^64)^k*(word m base (o+8*k)).toNat := by
  rw [wordsVal_succ_top, Nat.pow_mul]

/-- Propagate a subtraction borrow, masking only the most significant word. -/
theorem subtractStore_ok {s : State} {base : Addr} {size o : Nat}
    (hs : Scr s base size) (ho : o+72 ≤ size) (ho8 : o%8 = 0)
    (hz : s.gpr .x7 = 0) :
    WP isa (.block (correctStore (regs.take 8) o ++
      ([.sbcs .x .x21 .x21 .x7] : List Instr) ++ maskStoreTop (o+64))) s fun t =>
      ∃ w co, w < (2^64)^9 ∧
        w+(!s.c).toNat = regsVal s regs + (2^64)^9*(!co).toNat ∧
        wordsVal t.mem base o 9 = w%(512*(2^64)^8) ∧
        KeepRegs (clob 9) s t ∧ Outside base o 72 s.mem t.mem := by
  have hl : (regs.take 8).length = 8 := by decide
  have hp : 2^(64*(regs.take 8).length) = (2^64)^8 :=
    (congrArg (fun n => 2^(64*n)) hl).trans power512
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (correctStore_ok (regs.take 8) hs
    (by rw [hl]; omega_arith) ho8 (by decide) (by decide) (by decide) hz)
    fun u ⟨hu,ku,Ou⟩ => ?_
  rw [hp, hl] at hu
  have hs1 := hs.of_keepRegs ku (by decide)
  have hz1 : u.gpr .x7 = 0 := (ku.gpr .x7 (by decide)).trans hz
  have htop : u.gpr .x21 = s.gpr .x21 := ku.gpr .x21 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (subc_ok u .x21 .x21 .x7 false rfl) fun v ⟨hv,hc,kv⟩ => ?_
  simp only [Bool.false_eq_true, ite_false] at hv hc
  have he := sub_borrow (u.gpr .x21) (u.gpr .x7) u.c
  rw [← hv, ← hc, hz1, show (0 : BitVec 64).toNat = 0 from rfl,
    Nat.add_zero, htop] at he
  have hs2 := hs1.of_keeps kv (by decide)
  refine WP.mono (maskStoreTop_ok hs2 (o := o+64) (by omega_arith) (by omega_arith))
    fun t ⟨ht,kt,Ot⟩ => ?_
  let w := wordsVal u.mem base o 8 + (2^64)^8*(v.gpr .x21).toNat
  have hlo := wordsVal_lt_radix u.mem base o 8
  have hhi := (v.gpr .x21).isLt
  have hw : w < (2^64)^9 := by
    have hp9 : (2^64)^9 = (2^64)^8*2^64 := by decide +kernel
    dsimp only [w]
    rw [hp9]
    omega_using [hlo]
  have hew : w+(!s.c).toNat = regsVal s regs + (2^64)^9*(!v.c).toNat := by
    rw [regs_split]
    have hp9 : (2^64)^9 = (2^64)^8*2^64 := by decide +kernel
    dsimp only [w]
    rw [hp9, Nat.mul_assoc]
    omega_using [hu, he]
  refine ⟨w,v.c,hw,hew,?_,?_,?_⟩
  · have hspl := wordsVal_top_radix t.mem base o 8
    rw [show o+8*8 = o+64 by omega_arith] at hspl
    rw [hspl, ht,
      Ot.wordsVal (d := o) (k := 8) (by omega_arith) (by have := hs.nowrap; omega_arith),
      kv.mem]
    exact (masked_value hlo).symm
  · exact (ku.mono (by decide)).trans
      (((Keeps.regs kv).mono (by decide)).trans (kt.mono (by decide)))
  · intro x hx
    rw [Ot x (by omega_arith), kv.mem, Ou x (by rw [hl]; omega_arith)]

/-- The specialized addition, including aliases of either input. -/
theorem add_ok {s : State} {base : Addr} {size o a b p : Nat}
    (hs : Scr s base size) (ho : o+72 ≤ size) (ha : a+72 ≤ size) (hb : b+72 ≤ size)
    (ho8 : o%8 = 0) (ha8 : a%8 = 0) (hb8 : b%8 = 0)
    (hm : p+1 = 512*(2^64)^8)
    (hAB : wordsVal s.mem base a 9 + wordsVal s.mem base b 9 < 2*p) :
    WP isa (.block (VG.Impl.Mont.AArch64.P521Linear.add o a b)) s fun t =>
      wordsVal t.mem base o 9 = (wordsVal s.mem base a 9 + wordsVal s.mem base b 9)%p ∧
      wordsVal t.mem base o 9 < p ∧ KeepRegs (clob 9) s t ∧ Outside base o 72 s.mem t.mem := by
  have hlen : regs.length = 9 := by decide
  have hFresh : Fresh regs := (fresh_top_low_lt 9 (by decide)).tail
  rw [VG.Impl.Mont.AArch64.P521Linear.add]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (addInit_ok s) fun u ⟨hz,hc,ku⟩ => ?_
  have hs1 := hs.of_keeps ku (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok regs hs1 (a := a) (by rw [hlen]; omega_arith) ha8 hFresh)
    fun v ⟨hv,kv,cv⟩ => ?_
  have hs2 := hs1.of_keeps kv (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (chainAdcs_ok regs hs2 (b := b) (by rw [hlen]; omega_arith) hb8 hFresh)
    fun w ⟨hw,kw⟩ => ?_
  rw [hv, kv.mem, ku.mem, cv, hc, power_regs9] at hw
  simp only [hlen, Bool.toNat_true] at hw
  have hbnd : wordsVal s.mem base a 9 + wordsVal s.mem base b 9 + 1 < (2^64)^9 := by
    have hgap := radix_gap
    omega_using [hm, hAB]
  have he : regsVal w regs = wordsVal s.mem base a 9 + wordsVal s.mem base b 9 + 1 := by
    cases hf : w.c
    · simpa only [hf, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] using hw
    · simp only [hf, Bool.toNat_true, Nat.mul_one] at hw
      omega_using [hbnd, hw]
  have hs3 := hs2.of_keeps kw (by decide)
  have hz1 : w.gpr .x7 = 0 := (kw.gpr .x7 (by decide)).trans ((kv.gpr .x7 (by decide)).trans hz)
  refine WP.mono (canonicalStore_ok hs3 ho ho8 hm hAB he hz1) fun t ⟨eq,lt,kt,Ot⟩ => ?_
  refine ⟨eq,lt,?_,?_⟩
  · have k0 : KeepRegs (clob 9) s u :=
      ⟨fun r hr => ku.gpr r (fun h => hr ((by decide : ∀ x ∈ [Reg.x7], x ∈ clob 9) r h)),
        ku.rd,ku.wr,ku.sp⟩
    have k1 : KeepRegs (clob 9) u v :=
      ⟨fun r hr => kv.gpr r (fun h => hr ((by decide : ∀ x ∈ regs, x ∈ clob 9) r h)),
        kv.rd,kv.wr,kv.sp⟩
    have k2 : KeepRegs (clob 9) v w :=
      ⟨fun r hr => kw.gpr r (fun h => hr ((by decide : ∀ x ∈ Reg.x2 :: regs, x ∈ clob 9) r h)),
        kw.rd,kw.wr,kw.sp⟩
    exact k0.trans (k1.trans (k2.trans (kt.mono (by decide))))
  · rw [kw.mem, kv.mem, ku.mem] at Ot
    exact Ot

private theorem radix_multiple : (2^64)^9%(512*(2^64)^8) = 0 := by decide +kernel

/-- Canonical field subtraction, including aliases of either input. -/
theorem sub_ok {s : State} {base : Addr} {size o a b p : Nat}
    (hs : Scr s base size) (ho : o+72 ≤ size) (ha : a+72 ≤ size) (hb : b+72 ≤ size)
    (ho8 : o%8 = 0) (ha8 : a%8 = 0) (hb8 : b%8 = 0)
    (hm : p+1 = 512*(2^64)^8)
    (hA : wordsVal s.mem base a 9 < p) (hB : wordsVal s.mem base b 9 < p) :
    WP isa (.block (VG.Impl.Mont.AArch64.P521Linear.sub o a b)) s fun t =>
      wordsVal t.mem base o 9 = (wordsVal s.mem base a 9+p-wordsVal s.mem base b 9)%p ∧
      wordsVal t.mem base o 9 < p ∧ KeepRegs (clob 9) s t ∧ Outside base o 72 s.mem t.mem := by
  have hlen : regs.length = 9 := by decide
  have hFresh : Fresh regs := (fresh_top_low_lt 9 (by decide)).tail
  rw [VG.Impl.Mont.AArch64.P521Linear.sub]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero7_ok s) fun u ⟨hz,ku⟩ => ?_
  have hs1 := hs.of_keeps ku (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok regs hs1 (a := a) (by rw [hlen]; omega_arith) ha8 hFresh)
    fun v ⟨hv,kv,_⟩ => ?_
  have hs2 := hs1.of_keeps kv (by decide)
  rw [WP.block_append_iff]
  have hchain := chainSubs_ok hs2 (t := .x8) (ts := regs.drop 1) (b := b)
    (by change b+72 ≤ size; exact hb) hb8 hFresh
  refine WP.mono hchain fun w ⟨hw,kw⟩ => ?_
  have er : regs = .x8 :: regs.drop 1 := by decide
  rw [← er] at hw kw
  rw [hv, kv.mem, ku.mem, power_regs9] at hw
  rw [hlen] at hw
  have hs3 := hs2.of_keeps kw (by decide)
  have hz1 : w.gpr .x7 = 0 :=
    (kw.gpr .x7 (by decide)).trans ((kv.gpr .x7 (by decide)).trans hz)
  refine WP.mono (subtractStore_ok hs3 ho ho8 hz1) fun t ⟨y,co,hy,hey,ht,kt,Ot⟩ => ?_
  have hd := regsVal_lt w regs
  rw [power_regs9] at hd
  have hR : p+1 ≤ (2^64)^9 := by have hg := radix_gap; omega_using [hm]
  have hmod : (2^64)^9%(p+1) = 0 :=
    (congrArg (fun z => (2^64)^9%z) hm).trans radix_multiple
  have hc := subtraction_correction hA hB hR hmod hd hy hw hey
  rw [hm, ← ht] at hc
  refine ⟨hc.1,hc.2,?_,?_⟩
  · have k0 : KeepRegs (clob 9) s u := (Keeps.regs ku).mono (by decide)
    have k1 : KeepRegs (clob 9) u v := (Keeps.regs kv).mono (by decide)
    have k2 : KeepRegs (clob 9) v w := (Keeps.regs kw).mono (by decide)
    exact k0.trans (k1.trans (k2.trans kt))
  · rw [kw.mem, kv.mem, ku.mem] at Ot
    exact Ot

private theorem split_div {B lo hi : Nat} (hlo : lo < B) :
    (lo+B*hi)/(512*B) = hi/512 := by
  have hm := Nat.mod_lt hi (by decide : 0 < 512)
  have he : lo+B*hi = (lo+B*(hi%512)) + (512*B)*(hi/512) := by
    have hd := Nat.mod_add_div hi 512
    rw [Nat.mul_comm 512 B,Nat.mul_assoc,Nat.add_assoc,← Nat.mul_add,hd]
  have hb := Nat.mul_le_mul_left B (show hi%512 ≤ 511 by omega_using [])
  have hsmall : lo+B*(hi%512) < 512*B := by omega_using [hlo, hb]
  rw [he,Nat.add_mul_div_left _ _ (by omega_using [hlo]),Nat.div_eq_of_lt hsmall,Nat.zero_add]

theorem cmsFold_ok (s : State) (hz : s.gpr .x7 = 0) (h24 : s.gpr .x24 = 511) :
    WP isa (.block cmsFold) s fun t =>
      regsVal t regs+(2^64)^9*t.c.toNat =
        regsVal s regs%(512*(2^64)^8)+regsVal s regs/(512*(2^64)^8)+1 ∧
      Keeps (.x2::regs) s t := by
  rw [cmsFold,WP.block_append_iff]
  refine WP.mono (cmsFoldPrefix_ok s h24) fun u ⟨hu,h21,ku⟩ => ?_
  have hz1 : u.gpr .x7 = 0 := (ku.gpr .x7 (by decide)).trans hz
  refine WP.mono (carryRegs_ok (regs.drop 1) u (by decide) (by decide) hz1)
    fun t ⟨ht,kt⟩ => ?_
  have hlen : (regs.drop 1).length = 8 := by decide
  rw [hlen] at ht
  have e8 : regs.take 8 = .x8::(regs.take 8).drop 1 := by decide
  have hmid : regsVal u ((regs.take 8).drop 1) = regsVal s ((regs.take 8).drop 1) :=
    regsVal_congr fun r hr => ku.gpr r
      ((by decide : ∀ r ∈ (regs.take 8).drop 1, r ∉ [Reg.x2,.x21,.x8]) r hr)
  have hlow : regsVal u (regs.take 8)+2^64*u.c.toNat =
      regsVal s (regs.take 8)+(s.gpr .x21).toNat/512+1 := by
    rw [e8]
    simp only [regsVal,hmid]
    omega_using [hu]
  have hp : regsVal u regs+2^64*u.c.toNat =
      regsVal s regs%(512*(2^64)^8)+regsVal s regs/(512*(2^64)^8)+1 := by
    rw [regs_split s,masked_value (regs_low_lt s),split_div (regs_low_lt s),regs_split u,h21]
    omega_using [hlow]
  have er : regs = .x8::regs.drop 1 := by decide
  have h8 : t.gpr .x8 = u.gpr .x8 := kt.gpr .x8 (by decide)
  have hpow : (2^64)^9 = 2^64*(2^64)^8 := by decide +kernel
  refine ⟨?_,(ku.mono (by decide)).trans (kt.mono (by decide))⟩
  have he := congrArg (fun n => 2^64*n) ht
  simp only [Nat.mul_add] at he
  have hf : regsVal t regs+(2^64)^9*t.c.toNat = regsVal u regs+2^64*u.c.toNat := by
    rw [er]
    simp only [regsVal,h8]
    rw [hpow,Nat.mul_assoc]
    omega_using [ht]
  exact hf.trans hp

private theorem fold_math {p n : Nat} (hp : 32 < p) (hn : n < 32*p) :
    n%(p+1)+n/(p+1) < 2*p ∧
      (n%(p+1)+n/(p+1))%p = n%p := by
  have hq : n/(p+1) < 32 := (Nat.div_lt_iff_lt_mul (by omega_using [])).mpr (by omega_using [hn])
  have hr := Nat.mod_lt n (show 0 < p+1 by omega_using [])
  refine ⟨by omega_using [hp, hq, hr],?_⟩
  have he : n = (n%(p+1)+n/(p+1)) + p*(n/(p+1)) := by
    have h := Nat.mod_add_div n (p+1)
    rw [Nat.add_mul,Nat.one_mul] at h
    omega_using [h]
  exact ((congrArg (fun x => x%p) he).trans (Nat.add_mul_mod_self_left _ _ _)).symm

private theorem capacity9 : limbCapacity 9 = 512*(2^64)^8 := by decide +kernel
private theorem cms_radix_gap : 16384*(2^64)^8 < (2^64)^9 := by decide +kernel

/-- A fused small linear combination with a single final Mersenne reduction.
Both operands are completely read before the first output store. -/
theorem cms_ok {s : State} {base : Addr} {size o C a D b p : Nat}
    (hs : Scr s base size) (ho : o+72 ≤ size) (ha : a+72 ≤ size) (hb : b+72 ≤ size)
    (ho8 : o%8 = 0) (ha8 : a%8 = 0) (hb8 : b%8 = 0)
    (hm : p+1 = 512*(2^64)^8) (hC : C ≤ 16) (hD : D ≤ 16)
    (hA : wordsVal s.mem base a 9 < p) (hB : wordsVal s.mem base b 9 < p) :
    WP isa (.block (cms o C a D b)) s fun t =>
      wordsVal t.mem base o 9 =
        (wordsVal s.mem base a 9*C+(p-wordsVal s.mem base b 9)*D)%p ∧
      wordsVal t.mem base o 9 < p ∧ KeepRegs (clob 9) s t ∧ Outside base o 72 s.mem t.mem := by
  let n := wordsVal s.mem base a 9*C+(p-wordsVal s.mem base b 9)*D
  have hn : n < 32*p := by
    have hc := Nat.mul_le_mul_left (wordsVal s.mem base a 9) hC
    have hd := Nat.mul_le_mul_left (p-wordsVal s.mem base b 9) hD
    dsimp only [n]
    omega_using [hA, hc, hd]
  have hbig : 32 < p := by omega_using [hm]
  have hfold := fold_math hbig hn
  have hradix : n < (2^64)^9 := by have hg := cms_radix_gap; omega_using [hm, hn]
  have hcomp := complementedValue_eq s.mem base 9 b (by rw [capacity9]; omega_using [hm, hB])
  rw [capacity9,← hm] at hcomp
  have hce : complementedValue s.mem base b 9 = p-wordsVal s.mem base b 9 := by omega_using [hcomp]
  rw [cms]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (cmsInit_ok s hC hD) fun u ⟨hz,h16,hk,hc,hd,h24,ku⟩ => ?_
  have hs1 := hs.of_keeps ku (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (cmsRows_ok regs hs1 (a := a) (b := b)
    (by change a+72 ≤ size; exact ha) (by change b+72 ≤ size; exact hb) ha8 hb8
    (by decide) (fun _ h => h) hz h16 h24 (hc ▸ hC) (hd ▸ hD) (by rw [hk]; decide))
    fun v ⟨hv,hkv,kv⟩ => ?_
  have hlen : regs.length = 9 := by decide
  simp only [hlen,ku.mem,hc,hd,hk,show (0 : BitVec 64).toNat = 0 from rfl,
    Nat.add_zero,hce] at hv
  have he : regsVal v regs = n := by
    have hv0 : (2^64)^9*(v.gpr .x5).toNat = 0 := by omega_using [hm, hC, hD, hA, hB, hn, hbig, hfold, hcomp, hc, hd, hkv, hv]
    rw [hv0,Nat.add_zero] at hv
    exact hv
  have hz1 : v.gpr .x7 = 0 := (kv.gpr .x7 (by decide)).trans hz
  have h241 : v.gpr .x24 = 511 := (kv.gpr .x24 (by decide)).trans h24
  rw [WP.block_append_iff]
  refine WP.mono (cmsFold_ok v hz1 h241) fun w ⟨hw,kw⟩ => ?_
  rw [he,← hm] at hw
  have hew : regsVal w regs = n%(p+1)+n/(p+1)+1 := by
    cases hcw : w.c
    · simpa only [hcw,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] using hw
    · simp only [hcw,Bool.toNat_true,Nat.mul_one] at hw
      have hg := cms_radix_gap
      omega_using [hm, hfold, hw]
  have hs2 := hs1.of_keeps kv (by decide)
  have hs3 := hs2.of_keeps kw (by decide)
  have hz2 : w.gpr .x7 = 0 := (kw.gpr .x7 (by decide)).trans hz1
  refine WP.mono (canonicalStore_ok hs3 ho ho8 hm hfold.1 hew hz2)
    fun t ⟨ht,hlt,kt,Ot⟩ => ?_
  refine ⟨ht.trans hfold.2,hlt,?_,?_⟩
  · exact ((Keeps.regs ku).mono (by decide)).trans
      (((Keeps.regs kv).mono (by decide)).trans
        (((Keeps.regs kw).mono (by decide)).trans (kt.mono (by decide))))
  · rw [kw.mem,kv.mem,ku.mem] at Ot
    exact Ot

end VG.Proof.Mont.AArch64.P521Linear
