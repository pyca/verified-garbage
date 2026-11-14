module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombDigit
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Code
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.LookupCode
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowSignedY

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Ed25519.AArch64

 def windowHorner : Nat → Nat → List Instr
  | _,0 => [.movz .x .x2 0 0]
  | d,1 => [.ldrb .x2 .x16 d]
  | d,k+2 => windowHorner (d+1) (k+1)++[.add .x .x2 .x2 .x2,.ldrb .x4 .x16 d,.add .x .x2 .x2 .x4]

 theorem window_horner_ok {v : Nat → Nat} (hv : ∀ i,v i≤1) :
    ∀(k d : Nat) {s : State},k<64 → d+k≤4096 →
      (∀i<k,InRegions (s.rd++s.wr) (s.gpr .x16+BitVec.ofNat 64 (d+i)) 1 ∧
        s.mem (s.gpr .x16+BitVec.ofNat 64 (d+i))=BitVec.ofNat 8 (v (d+i))) →
      WP isa (.block (windowHorner d k)) s fun t =>
        t.gpr .x2=BitVec.ofNat 64 (hornerVal v d k) ∧ Keeps [.x2,.x4] s t
  | 0,d,s,hk,hd,hb => hornerBits_ok hv 0 d hk hd hb
  | 1,d,s,_,hd,hb => by
    obtain ⟨hr,hm⟩ := hb 0 (by decide)
    simp only [Nat.add_zero] at hr hm
    apply WP.of_runBlock
    simp only [windowHorner,runBlock_cons,runStep_some,runBlock_nil,exec,State.load,addr,
      Size.bits,Nat.mod_one,show d<4096*1 by omega_arith,and_self,ite_true,hr,read1_zext,hm,
      RegUpd.gpr_write_self,Option.map_some,Option.bind_some,Option.some.injEq,exists_eq_left']
    refine ⟨?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
    · apply BitVec.eq_of_toNat_eq
      have := hv d
      simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat,hornerVal,Nat.mul_zero]
      omega_arith
    · simp only [List.mem_cons,not_or] at hr
      exact RegUpd.gpr_write_of_ne _ _ _ hr.1
  | k + 2, d, s, hk, hd, hb => by
    rw [windowHorner, WP.block_append_iff]
    refine WP.mono (window_horner_ok hv (k+1) (d + 1) (by omega_arith) (by omega_arith) fun i hi => by
      rw [show d + 1 + i = d + (i + 1) by omega_arith]; exact hb (i + 1) (by omega_arith)) fun s₁ ⟨e₁, k₁⟩ => ?_
    have h16 : s₁.gpr .x16 = s.gpr .x16 := k₁.gpr _ (by decide)
    obtain ⟨hr, hm⟩ := hb 0 (by omega_arith)
    rw [Nat.add_zero] at hr hm
    have hlt := hornerVal_lt hv (d + 1) (k+1)
    have hk2 : 2 ^ (k+1) < 2 ^ 63 := Nat.pow_lt_pow_right (by decide) (by omega_arith)
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, State.load, addr,
      Size.bits, Nat.mod_one, show d < 4096 * 1 by omega_arith, and_self, ite_true, h16,
      k₁.rd, k₁.wr, k₁.mem, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
      hr, read1_zext, hm, BitVec.setWidth_eq, ite_false, reduceCtorEq, e₁, Option.map_some,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨?_, ⟨fun r hr' => ?_, k₁.mem, k₁.rd, k₁.wr, k₁.sp⟩⟩
    · apply BitVec.eq_of_toNat_eq
      have := hv d
      rw [show hornerVal v d (k+2)=2*hornerVal v (d+1) (k+1)+v d from rfl]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
      rw [Nat.mod_eq_of_lt (by omega_arith : v d % 2 ^ 8 < 2 ^ 64), Nat.mod_eq_of_lt (by omega_arith : v d < 2 ^ 8),
        Nat.mod_eq_of_lt (by omega_arith : hornerVal v (d + 1) (k+1) < 2 ^ 64)]
      omega_arith
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      simp only [RegUpd.gpr_write, hr'.1, hr'.2, ite_false]
      exact k₁.gpr r (by simpa using hr')

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Ed25519.AArch64
open VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass.AArch64.P521Native

 def windowDigit : List Instr := winIndex 5++windowHorner 3304 5++magnitudeH 16

 theorem window_digit_source : (outerBlock142.drop 54).take 22=windowDigit := by decide

 theorem window_digit_ok {s : State} {base : Addr} {size k j : Nat}
    (hs : Scr s base size) (room : 3829≤size) (hj : j<105)
    (counter : s.gpr .x19=BitVec.ofNat 64 j)
    (bits : ∀t<525,s.mem (off base (3304+t))=if k.testBit t then 1 else 0) :
    WP isa (.block windowDigit) s fun t =>
      t.gpr .x2=BitVec.ofNat 64 (magH 16 (combWin 5 k j)) ∧ Keeps [.x2,.x3,.x4,.x9,.x16] s t := by
  have hn := hs.nowrap
  rw [windowDigit, List.append_assoc, WP.block_append_iff]
  refine WP.mono (winIndex_ok s hs (by omega_arith) counter) fun a ⟨a16, ka⟩ => ?_
  rw [WP.block_append_iff]
  have hv : ∀ i, (fun t => (k.testBit (5 * j + (t - 3304))).toNat) i ≤ 1 := fun _ => Bool.toNat_le _
  refine WP.mono (window_horner_ok hv 5 3304 (s := a) (by omega_arith) (by decide) fun i hi => ?_)
    fun b ⟨b2, kb⟩ => ?_
  · have he : a.gpr .x16 + BitVec.ofNat 64 (3304 + i) = off base (3304 + (5 * j + i)) := by
      rw [a16, off, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact congrArg (base + ·) (congrArg _ (by omega_arith))
    refine ⟨by rw [he]; exact ⟨_, List.mem_append_right _ (ka.wr ▸ hs.wr), hs.contains (by omega_arith) (by decide)⟩, ?_⟩
    rw [he, ka.mem, bits _ (by omega_arith), show 3304 + i - 3304 = i by omega_arith]
    cases k.testBit (5 * j + i) <;> rfl
  · have hw' : hornerVal (fun t => (k.testBit (5 * j + (t - 3304))).toNat) 3304 5 = combWin 5 k j := by
      have := hornerVal_eq k 5 j 5 (Nat.le_refl _)
      rw [Nat.sub_self, Nat.add_zero] at this
      rw [combWin, ← this]
      exact hornerVal_congr fun i _ => by simp only [show 3304 + i - 3304 = i by omega_arith]
    have hlt := combWin_lt 5 k j
    refine WP.mono (magnitudeH_ok b (by decide : 5<9) hlt (by rw [b2, hw'])) fun t ⟨t2, kt⟩ =>
      ⟨t2, ((Keeps.regs ka).mono (by decide)).trans ((Keeps.regs kb).mono (by decide)) |>.trans
        ((Keeps.regs kt).mono (by decide)) |> fun h => ⟨h.gpr, kt.mem.trans (kb.mem.trans ka.mem), h.rd, h.wr, h.sp⟩⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.P521Native

def windowLookupCode : List Instr := windowDigit++lookupCode++windowSignedY

theorem window_lookup_source : (outerBlock142.drop 54).take 693=windowLookupCode := by
  rw [windowLookupCode,←window_digit_source,lookupCode,←window_signed_y_source]
  have h1 : outerBlock142.drop 76=(outerBlock142.drop 54).drop 22 := by rw [List.drop_drop]
  have h2 : outerBlock142.drop 640=(outerBlock142.drop 54).drop 586 := by rw [List.drop_drop]
  rw [h1,h2,←List.take_add,←List.take_add]

end VG.Proof.Weierstrass.AArch64.P521Native
