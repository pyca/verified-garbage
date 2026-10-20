module

public import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsState
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsLoop
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Complete read-only vetted-domain recognition in an FFDH frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedGroups
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Ffdh.Arm.VettedGroups
open VG.Proof.X25519.Arm (Rest)

 theorem entry_raw_ok (s : State) {p : Inputs} {slots : List Nat} (h : Context p slots s)
    (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) :
    WP isa (.block entry) s fun t =>
      ((t.gpr .r4 = s.syms tableSym ∧ t.gpr .r7 = 10 ∧
        t.gpr .r6 = BitVec.ofNat 32 p.k ∧ t.gpr .r9 = p.domain ∧
        t.gpr .r10 = BitVec.ofNat 32 p.dom.length) ∧ t.gpr .r8 = p.base ∧ t.mem = s.mem) ∧
      Rest [.r4, .r6, .r7, .r8, .r9, .r10] s t := by
  refine withRest [.r4, .r6, .r7, .r8, .r9, .r10] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block entry : Prog isa)).all (fun i => !(VG.Arm.clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have hf := List.all_eq_true.mp checked i hi
    cases hc : VG.Arm.clobbers i r <;> simp_all) (by rfl)
  have addr (d : Nat) (hd : d + 4 ≤ 72) :
      State.addr (s.sp + BitVec.ofNat 32 d) = VG.Proof.Mont.off (State.addr s.sp) d :=
    VG.Arm.addr_add (by have := h.locals.space.nowrap; omega)
  have r24 := h.locals.read (d := 24) (by decide)
  have r28 := h.locals.read (d := 28) (by decide)
  have r32 := h.locals.read (d := 32) (by decide)
  have v24 := h.saved 24 h24
  have v28 := h.saved 28 h28
  have v32 := h.saved 32 h32
  unfold entry
  ffrun [exec, State.load32, addr 24 (by decide), addr 28 (by decide), addr 32 (by decide),
    r24, r28, r32, v24, v28, v32, Inputs.slotValue, h.ptr, BitVec.ofNat_eq_ofNat]
  rfl

 theorem entry_ok (s : State) {p : Inputs} {slots : List Nat} (h : Context p slots s)
    (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) :
    WP isa (.block entry) s fun t =>
      (Cursor (s.syms tableSym) p.domain p.k p.dom groups t ∧ t.gpr .r8 = p.base ∧ t.mem = s.mem) ∧
      Rest [.r4, .r6, .r7, .r8, .r9, .r10] s t := by
  refine WP.mono (entry_raw_ok s h h24 h28 h32) ?_
  rintro t ⟨⟨⟨ptr, count, width, source, length⟩, saved, mem⟩, rest⟩
  exact ⟨⟨⟨ptr, count, width, source, length⟩, saved, mem⟩, rest⟩

 theorem restore_ok (s : State) :
    WP isa (.block [.mov .r0 (.reg .r8)]) s fun t =>
      (t.gpr .r0 = s.gpr .r8 ∧ t.mem = s.mem) ∧ Rest [.r0] s t := by
  refine withRest [.r0] ?_ (by
    intro r hr i hi
    simp only [instrs, List.mem_singleton] at hi
    subst i
    cases r <;> simp_all [VG.Arm.clobbers, VG.Arm.dstOf]) (by rfl)
  ffrun []

 theorem code_ok (s : State) {p : Inputs} {slots : List Nat} (h : Context p slots s)
    (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (table : TableAt (s.syms tableSym) groups s) :
    WP isa code s fun t => Context p slots t ∧
      t.gpr .r11 = BitVec.ofNat 32 (recognize groups p.k p.dom) ∧
      t.mem = s.mem ∧ Rest VG.Proof.Bignum.Arm.roundClobbers s t := by
  rw [code, WP.seq_iff]
  refine WP.mono (entry_ok s h h24 h28 h32) ?_
  rintro u ⟨⟨cursor, saved, memU⟩, restU⟩
  have source : Source p.domain p.k p.dom u :=
    ⟨by rw [p.domainLength]; split <;> have := p.minLength <;> omega,
      h.domain.fits, by rw [restU.rd, restU.wr]; exact h.domain.readable,
      by rw [memU]; exact h.domain.bytes, by rw [p.domainLength]; split <;> simp⟩
  rw [WP.seq_iff]
  refine WP.mono (loop_ok u source (table.after memU restU) cursor (by decide)
    (by have := p.maxLength; omega) (by decide)) ?_
  rintro v ⟨cap, memV, restV⟩
  refine WP.mono (restore_ok v) ?_
  rintro t ⟨⟨ptr, memT⟩, restT⟩
  have ptrT : t.gpr .r0 = p.base := ptr.trans ((restV.gpr .r8 (by simp [clobbers])).trans saved)
  have mem : t.mem = s.mem := memT.trans (memV.trans memU)
  have rest : Rest VG.Proof.Bignum.Arm.roundClobbers s t :=
    (restU.mono (by simp [VG.Proof.Bignum.Arm.roundClobbers])).trans
      ((restV.mono (by simp [clobbers, VG.Proof.Bignum.Arm.roundClobbers])).trans
        (restT.mono (by simp [VG.Proof.Bignum.Arm.roundClobbers])))
  exact ⟨h.of_mem mem rest ptrT, (restT.gpr .r11 (by simp)).trans cap, mem, rest⟩

end VG.Proof.Ffdh.Arm.VettedGroups
