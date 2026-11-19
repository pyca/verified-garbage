module

public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Ffdh.Arm.ValueChecks
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.PowerArgs
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
public import VerifiedGarbage.Impl.Ffdh.Arm.Arithmetic
public import VerifiedGarbage.Proof.Ffdh.Arm.Octets
public import VerifiedGarbage.Proof.Ffdh.Arm.Power
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.Arm.PublicScan
public import VerifiedGarbage.Proof.Ffdh.Lead
import VerifiedGarbage.Proof.Ffdh.Arm.KeyScan
import VerifiedGarbage.Proof.Ffdh.Arm.Block

/-! ### `Ffdh.Arm.PublicScan`, which this module and modules that import it used -/

section

/-! Reuse the key generator's checked public-bound scan for subgroup exponents. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)

namespace PublicScan
open VG.Impl.Ffdh.Arm.PublicScan

theorem enter_ok (s : State) : WP isa (.block enter) s fun t =>
    (t.gpr .r4 = s.gpr .r1 ∧ t.gpr .r6 = s.gpr .r2 ∧
      t.gpr .r8 = s.gpr .r4 ∧ t.gpr .r9 = s.gpr .r6 ∧ t.mem = s.mem) ∧
    Rest [.r4,.r6,.r8,.r9] s t := by
  refine withRest_all [.r4,.r6,.r8,.r9] ?_ (by rfl) (by rfl)
  unfold enter
  ffrun []

theorem leave_ok (s : State) : WP isa (.block leave) s fun t =>
    (t.gpr .r1 = s.gpr .r4 ∧ t.gpr .r2 = s.gpr .r6 ∧
      t.gpr .r4 = s.gpr .r8 ∧ t.gpr .r6 = s.gpr .r9 ∧ t.mem = s.mem) ∧
    Rest [.r1,.r2,.r4,.r6] s t := by
  refine withRest_all [.r1,.r2,.r4,.r6] ?_ (by rfl) (by rfl)
  unfold leave
  ffrun []

theorem code_ok (s : State) {base src : BitVec 32} {len : Nat} {bs : List Byte}
    (source : Octets base src len bs s) (positive : 0 < bs.length) (fits : bs.length < 2^32)
    (ptr : s.gpr .r1 = src) (count : s.gpr .r2 = BitVec.ofNat 32 bs.length) :
    WP isa code s fun t =>
      t.gpr .r1 = src + BitVec.ofNat 32 (VG.Proof.Ffdh.lead bs) ∧
      t.gpr .r2 = BitVec.ofNat 32 (bs.length - VG.Proof.Ffdh.lead bs) ∧
      t.gpr .r4 = s.gpr .r4 ∧ t.gpr .r6 = s.gpr .r6 ∧
      t.mem = s.mem ∧ Rest [.r1,.r2,.r3,.r4,.r6,.r8,.r9,.r11] s t := by
  rw [code, WP.seq_iff]
  refine WP.mono (enter_ok s) ?_
  rintro u ⟨⟨p4,p6,p8,p9,memU⟩,restU⟩
  have frameU : Frame [] s.mem u.mem := by rw [memU]; exact Frame.refl _ _
  have sourceU := source.after_frame frameU restU (by simp)
  have scan_ok : WP isa scan u fun v =>
      v.gpr .r4 = src + BitVec.ofNat 32 (VG.Proof.Ffdh.lead bs) ∧
      v.gpr .r6 = BitVec.ofNat 32 (bs.length - VG.Proof.Ffdh.lead bs) ∧
      v.gpr .r3 = (bs.getD (VG.Proof.Ffdh.lead bs) 0).setWidth 32 ∧
      v.mem = u.mem ∧ Rest [.r3,.r4,.r6,.r11] u v :=
    keyScan_ok u sourceU positive fits (p4.trans ptr) (p6.trans count)
  rw [WP.seq_iff]
  refine WP.mono scan_ok ?_
  rintro v ⟨v4,v6,_,memV,restV⟩
  refine WP.mono (leave_ok v) ?_
  rintro t ⟨⟨t1,t2,t4,t6,memT⟩,restT⟩
  exact ⟨t1.trans v4,t2.trans v6,
    t4.trans ((restV.gpr .r8 (by simp)).trans p8),
    t6.trans ((restV.gpr .r9 (by simp)).trans p9),
    memT.trans (memV.trans memU),
    ((restU.mono (by simp)).trans (restV.mono (by simp))).trans (restT.mono (by simp))⟩

end PublicScan
end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.PublicPowerInput`, which this module and modules that import it used -/

section

/-! The retained public exponent suffix has the same integer value. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

namespace PublicScan

theorem input_ok (s : State) {base src ep : BitVec 32} {len w M : Nat} {bb eb : List Byte}
    (h : PowerInput base src ep len w M bb eb s) :
    WP isa VG.Impl.Ffdh.Arm.PublicScan.code s fun t =>
      PowerInput base src (ep + BitVec.ofNat 32 (VG.Proof.Ffdh.lead eb)) len w M bb
        (eb.drop (VG.Proof.Ffdh.lead eb)) t ∧ t.mem = s.mem ∧
      Rest [.r1,.r2,.r3,.r4,.r6,.r8,.r9,.r11] s t := by
  refine WP.mono (code_ok s h.exponentBytes h.exponentPositive h.exponentFits h.exponent h.exponentCount) ?_
  rintro t ⟨epT,countT,sourceT,baseCountT,mem,rest⟩
  have frame : Frame [⟨State.addr base,8*len⟩] s.mem t.mem := by rw [mem];exact Frame.refl _ _
  have leadLt := VG.Proof.Ffdh.lead_lt (bs:=eb) (by intro e;rw [e] at h; have := h.exponentPositive; simp at this)
  have exponent := (h.exponentBytes.after_workspace frame rest).slice
    (d:=VG.Proof.Ffdh.lead eb) (k:=eb.length-VG.Proof.Ffdh.lead eb) (by omega_using [leadLt]) (by omega_using [leadLt])
  rw [List.take_of_length_le (by simp)] at exponent
  exact ⟨⟨h.ready.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ready.ptr),
    by rw [mem];exact h.modulus,h.odd,by rw [mem];exact h.r2,
    h.baseBytes.after_workspace frame rest,exponent,h.basePositive,h.baseFits,
    by simp only [List.length_drop];omega_using [leadLt],
    by simp only [List.length_drop];have := h.exponentFits;omega_using [this],
    sourceT.trans h.source,baseCountT.trans h.count,epT,by simpa only [List.length_drop] using countT⟩,
    mem,rest⟩

/-- Any region disjoint from the full public exponent remains disjoint from
its retained suffix, including the shared Montgomery helper's stack. -/
theorem suffix_separate {base ep : BitVec 32} {len : Nat} {eb : List Byte} {s : State}
    (source : Octets base ep len eb s) (positive : 0 < eb.length) {region : Region}
    (separate : Region.Disjoint ⟨State.addr ep,eb.length⟩ region) :
    Region.Disjoint
      ⟨State.addr (ep+BitVec.ofNat 32 (VG.Proof.Ffdh.lead eb)),
        (eb.drop (VG.Proof.Ffdh.lead eb)).length⟩ region := by
  have leadLt := VG.Proof.Ffdh.lead_lt (bs:=eb) (by intro e;rw [e] at positive;simp at positive)
  have bound : ep.toNat + VG.Proof.Ffdh.lead eb < 2^32 := by have := source.fits;omega_using [leadLt, this]
  rw [VG.Arm.addr_add bound,List.length_drop]
  exact separate.sub_left (Offset.sub_base _ (by omega_using [leadLt]))

end PublicScan
end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.PublicPowerAt`, which this module and modules that import it used -/

section

/-! A power from saved FFDH base and exponent buffers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem publicPowerAt_ok (s : State) {p : Inputs} {slots : List Nat} (bs es ec : Nat)
    {bb eb : List Byte} {M : Nat} (h : Context p slots s) (stable : stableSlots slots = true)
    (hb : bs ∈ slots) (he : es ∈ slots) (hc : ec ∈ slots) (hk : 32 ∈ slots)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = M) (odd : M % 2 = 1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % M)
    (baseBytes : Octets p.base (p.slotValue bs) p.len bb s) (baseLength : bb.length = p.k)
    (exponentBytes : Octets p.base (p.slotValue es) p.len eb s) (exponentPositive : 0 < eb.length)
    (exponentFits : eb.length < 2 ^ 32) (exponentLength : p.slotValue ec = BitVec.ofNat 32 eb.length) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.publicPowerAt bs es ec) s fun t => Context p slots t ∧
      ArithmeticReady p.base p.len p.w t ∧
      numAt t.mem (State.addr p.base) p.w 6 = Spec.Rsa.powMod (Spec.Rsa.os2ip bb) (Spec.Rsa.os2ip eb) M ∧
      numAt t.mem (State.addr p.base) p.w 0 = M ∧
      numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % M ∧
      numAt t.mem (State.addr p.base) p.w 7 = 1 ∧
      Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.Domain.publicPowerAt, WP.seq_iff]
  refine WP.mono (powerArgs_ok s bs es ec h stable hb he hc hk) ?_
  rintro u ⟨⟨source, count, exponent, exponentCount, mem⟩, restU⟩
  have frameU : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem u.mem := by rw [mem]; exact Frame.refl _ _
  have readyU := ready.of_mem mem restU ((restU.gpr .r0 (by simp)).trans ready.ptr)
  have baseU := baseBytes.after_workspace frameU restU
  have exponentU := exponentBytes.after_workspace frameU restU
  have input : PowerInput p.base (p.slotValue bs) (p.slotValue es) p.len p.w M bb eb u :=
    ⟨readyU, by rw [mem]; exact modulus, odd, by rw [mem]; exact r2,
      baseU, exponentU, by rw [baseLength]; have := p.minLength; omega_using [this],
      by rw [baseLength]; exact p.width.2.2.2.1, exponentPositive, exponentFits,
      source, by rw [baseLength]; exact count, exponent, exponentCount.trans exponentLength⟩
  rw [WP.seq_iff]
  refine WP.mono (PublicScan.input_ok u input) ?_
  rintro v ⟨inputV,memV,restV⟩
  have initial : Frame [⟨State.addr p.base,8*p.len⟩] s.mem v.mem := by rw [memV];exact frameU
  refine WP.mono (power_ok v inputV p.width.2.2.1) ?_
  rintro t ⟨readyT, value, modT, r2T, oneT, frameT, restT⟩
  have frame := initial.trans frameT
  have rest : Rest roundClobbers s t := ((restU.mono (by simp [roundClobbers])).trans (restV.mono (by simp [roundClobbers]))).trans restT
  exact ⟨h.after_workspace frame rest readyT.ptr (fun d hd => (stableSlots_at stable hd).1),
    readyT, by simpa only [VG.Proof.Ffdh.os2ip_drop_lead] using value, modT, r2T, oneT, frame, rest⟩

end VG.Proof.Ffdh.Arm

end

end

/-! Subgroup membership is a native power followed by a fixed-width equality. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem subgroup_ok (s : State) {p : Inputs} {slots : List Nat} (slot : Nat) {bb : List Byte}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (hb : slot ∈ slots) (h60 : 60 ∈ slots) (h32 : 32 ∈ slots) (hasQ : p.hasQ = true)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P) (odd : p.P % 2 = 1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P)
    (baseBytes : Octets p.base (p.slotValue slot) p.len bb s) (baseLength : bb.length = p.k) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.subgroup slot) s fun t => Context p slots t ∧
      ArithmeticReady p.base p.len p.w t ∧
      t.gpr .r11 = (if Spec.Rsa.powMod (Spec.Rsa.os2ip bb) p.Q p.P = 1 then 1 else 0) ∧
      numAt t.mem (State.addr p.base) p.w 0 = p.P ∧
      numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P ∧
      Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.Domain.subgroup, WP.seq_iff]
  refine WP.mono (publicPowerAt_ok s slot 60 32 h stable hb h60 h32 h32 ready modulus odd r2 baseBytes baseLength
    (h.qBytes hasQ) (by rw [p.qLength hasQ]; have := p.minLength; omega_using [this])
    (by rw [p.qLength hasQ]; have := p.maxLength; omega_using [this]) (by change BitVec.ofNat 32 p.k = _; rw [p.qLength hasQ])) ?_
  rintro u ⟨contextU, readyU, power, modU, r2U, _, frameU, restU⟩
  refine WP.mono (isOne_ok u readyU (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 6) (by decide)) ?_
  rintro t ⟨readyT, flag, arraysT, frameT, restT⟩
  rw [power] at flag
  have frame := frameU.trans frameT
  have rest := restU.trans restT
  exact ⟨h.after_workspace frame rest readyT.ptr (fun d hd => (stableSlots_at stable hd).1), readyT,
    flag, (arraysT 0 (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)).trans modU,
    (arraysT 4 (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)).trans r2U,
    frame, rest⟩

end VG.Proof.Ffdh.Arm
