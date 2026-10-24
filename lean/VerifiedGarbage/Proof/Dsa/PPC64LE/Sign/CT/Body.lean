module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Key
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.CT.Entry
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.CT.Pre
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Key
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.CT.Entry
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.CT.Pre
import VerifiedGarbage.Proof.Dsa.DomainWidths
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd

/-!
# DSA signing on PPC64LE: constant time after the check of the key

`sbody_rel`: two runs of `Sign.body` from the state the checks of the key
leave (`K9`), for the same signing public data (`SG`), leak the same trace.
The body branches on nothing but the lengths, so the taint analysis checks it
in two segments: up to `output`'s load of `out` from the header's word
`hOut`, which it treats as secret, and after it, from the phase `Mid` in
which both runs hold `out` there (`spre_ok`). `zero_rel`: the same for
`zeroOut`, which loads `out` too, after a key that fails the checks.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Sign
open VG.Proof.Bignum (slot)

/-- `out`, for signing's public data. -/
def VD.o (v : VD) : Addr := v.out.getD 0

theorem Base.hOut {v : VD} {s : State} (h : Base v s) (hg : SG v) : word s.mem v.L.S hOut = v.o := by
  unfold SG at hg
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hg
  rw [VD.o, ho]
  exact h.hdr o (by rw [ho]; rfl)

/-- The registers the body fixes after the load of `out`. -/
def midL (v : VD) : List (Reg × BitVec 64) :=
  [(.r12, v.o), (.r6, BitVec.ofNat 64 v.L.ql), (.r10, off v.L.Q (slot 4 0)), (.r29, BitVec.ofNat 64 (8 * (4 + 2)))]

/-- After the load of `out`. -/
def Mid : VD → State → Prop := Ph VD.qb fun v s => FixL (midL v) s ∧ True

theorem pins_Mid : Pins Mid (coreRegs ++ ([.r12, .r6, .r10, .r29] : List Reg)) := pins_fixL _ _ fun _ => rfl

/-- What the checks of the key leave: `checkKey_ok`'s `Checked` and `KeyOk`. -/
theorem k9_checked {v : VD} {s : State} (h : K9 v s) (h3 : 3 * v.L.pl + v.L.ql ≤ v.kn) :
    KeyOk s.mem v.L v.key ∧ Checked s s v.L v.key v.sig v.dig v.d := by
  obtain ⟨B, r2, -, ⟨ip, p0, ptop, p8, q0, qtop⟩, ⟨km, hg⟩, hy⟩ := h
  have bd := km.1.bounds
  have ep : pOf s.mem v.L v.key = v.p := B.p
  have eq : qOf s.mem v.L v.key = v.q := B.q
  have eg : gOf s.mem v.L v.key = v.e (v.L.pl + v.L.ql) := B.g
  have ey : yOf s.mem v.L v.key = v.e (2 * v.L.pl + v.L.ql) := B.y h3
  refine ⟨?_, ⟨ip, B.scr, B.regs, p0.trans ep.symm, ptop, by rw [ep]; exact p8, q0.trans eq.symm, qtop, ?_⟩⟩
  · unfold KeyOk
    rw [ep, eq, eg, ey]
    exact ⟨⟨km.1.1, km.1.2.2, km.1.2.1⟩, ⟨⟨hg.1.1, hg.1.2⟩, hy.1.1, hy.1.2⟩,
      (pmod_iff (by omega) (by omega)).mpr km.2, hg.2, hy.2⟩
  · have e : Spec.Dsa.bitLength (qOf s.mem v.L v.key) / 8 = v.qb := by
      rw [eq, VD.q, VG.Proof.Dsa.subgroup_scan_width (p := v.pB) (q := v.qB) km.1.1, Nat.mul_div_cancel_left _
        (by decide)]
      rfl
    rw [e]; exact r2

/-- The body up to the load of `out`, to `Mid`. -/
theorem k9_mid {v : VD} {s : State} (h : K9 v s ∧ SG v) : WP isa spre s (Mid v) := by
  obtain ⟨hk9, sg⟩ := h
  have B := hk9.1
  have r2 := hk9.2.1
  have hL := B.ok
  obtain ⟨ekl, esl, ekn⟩ := B.sgn sg
  obtain ⟨hK, hc⟩ := k9_checked hk9 (Nat.le_of_eq ekn.symm)
  have hx : Src s v.L v.key (3 * v.L.pl + 2 * v.L.ql) := by rw [← ekl]; exact B.hx
  have hn : Src s v.L v.sig v.L.ql := by rw [← esl]; exact B.hsg
  have hd : v.d < 2 ^ 16 := by have := Nat.min_le_right v.dl 64; simp only [VD.d] at this ⊢; omega
  refine WP.mono (spre_ok hL hK hc (Kept.refl _ _) hx hn hd B.hdg (B.hOut sg))
    fun t ⟨⟨Qt, Kt, ht, t12, t6⟩, kt⟩ => ?_
  refine ⟨⟨hL, Qt.regs, Qt.scr, B.hk.keep kt.rd kt.wr, B.hsg.keep kt.rd kt.wr, B.hdg.keep kt.rd kt.wr,
    (B.hk.kept Kt.out).trans B.kb, B.hx.keep kt.rd kt.wr, fun o ho => ?_, B.sgn, B.kn⟩,
    (kt.gpr .r2 (by decide)).trans r2, ?_, trivial⟩
  · rw [ht]
    have := B.hdr o ho
    rw [← this, B.hOut sg]
  · simp only [FixL, midL, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
    exact ⟨t12, t6, Qt.inq.env.h10, Qt.inq.env.h29⟩

/-- The body starts in the P space the checks of the key leave. -/
theorem pins_K9 : Pins (fun v s => K9 v s ∧ SG v) (coreRegs ++ envRegs') := by
  intro v s₁ s₂ h₁ h₂ r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact (pins_fixL _ _ fun _ => rfl : Pins K9 (coreRegs ++ [])) v s₁ s₂ h₁.1 h₂.1 r
      (List.mem_append_left _ hr)
  · rw [show envRegs' = (envP v).map Prod.fst from rfl] at hr
    obtain ⟨p, hm, rfl⟩ := List.mem_map.mp hr
    rw [envP_of h₁.1.2.2.2.1.1 p hm, envP_of h₂.1.2.2.2.1.1 p hm]

theorem sbody_rel : RelCT isa (Two fun v s => K9 v s ∧ SG v) Sign.body (Two End) := by
  refine rel_end ?_ (fun _ _ h => h.1.1.regs.r21) (by rw [← Code.allInstrs_eq]; decide +kernel)
    (by decide +kernel)
  unfold Sign.body Sign.output
  iterate 13 refine RelCT.assoc ?_
  refine RelCT.seq (two_post (two_taint _ pins_K9 (by taint_decide))
    fun _ _ h => ?_) (two_taint _ pins_Mid (by taint_decide))
  iterate 12 refine WP.assoc' ?_
  exact k9_mid h

/-! ## A key that fails the checks -/

/-- `out` and its length doubled, to zero `out`. -/
def zL (v : VD) : List (Reg × BitVec 64) :=
  [(.r16, v.o), (.r17, BitVec.ofNat 64 (2 * v.L.ql)), (.r21, v.L.S)]

theorem pins_zL : Pins (fun v s => FixL (zL v) s) [.r16, .r17, .r21] := by
  intro v s₁ s₂ h₁ h₂ r hr
  rw [show [Reg.r16, .r17, .r21] = (zL v).map Prod.fst from rfl] at hr
  obtain ⟨p, hm, rfl⟩ := List.mem_map.mp hr
  rw [h₁ p hm, h₂ p hm]

theorem pins_r21 {Φ : VD → State → Prop} (h : ∀ v s, Φ v s → Base v s) : Pins Φ [.r21] := by
  intro v s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  rw [(h v _ h₁).regs.r21, (h v _ h₂).regs.r21]

theorem zfront_ok {v : VD} {s : State} (h : Base v s) (sg : SG v) :
    WP isa (.block (([.load .d .r16 .r21 hOut] : List Instr) ++ getQ .r17 ++
        ([.add .r17 .r17 .r17, .li .r0 0] : List Instr))) s
      fun t => FixL (zL v) t := by
  have hZ := h.ok.z256
  rw [WP.block_append_iff, WP.block_append_iff]
  have hld : InRegions (s.rd ++ s.wr) (s.gpr .r21 + BitVec.ofNat 64 hOut) 8 := by
    rw [h.regs.r21]; exact h.scr.ld (show hOut + 8 ≤ v.L.Z by simp only [hOut]; omega)
  refine WP.mono (WP.keep [.r16] (Q := fun u => u.gpr .r16 = v.o ∧ u.mem = s.mem)
    (by prun [exec_ld (by decide) hld]; rw [h.regs.r21]; exact h.hOut sg) (by decide)) fun s₁ ⟨⟨a16, _⟩, k1⟩ => ?_
  refine WP.mono (getQ_ok (h.regs.keep k1) .r17) fun s₂ ⟨⟨a17, _⟩, k2⟩ => ?_
  refine WP.mono (WP.keep [.r0, .r17] (Q := fun u => u.gpr .r16 = v.o ∧
      u.gpr .r17 = BitVec.ofNat 64 (2 * v.L.ql)) (by
      prun [a17, (k2.gpr .r16 (by decide)).trans a16]
      rw [BitVec.ofNat_add_ofNat, Nat.two_mul]) (by decide)) fun t ⟨⟨b16, b17⟩, k3⟩ => ?_
  simp only [FixL, zL, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
  exact ⟨b16, b17, (((k1.trans k2).trans k3).gpr .r21 (by decide)).trans h.regs.r21⟩

theorem zero_rel {Φ : VD → State → Prop} (h : ∀ v s, Φ v s → Base v s ∧ SG v) :
    RelCT isa (Two Φ) Sign.zeroOut (Two End) := by
  refine rel_end ?_ (fun v s hs => (h v s hs).1.regs.r21) (by decide) (by decide)
  unfold Sign.zeroOut
  exact RelCT.seq (two_post (two_taint _ (pins_r21 fun v s hs => (h v s hs).1) (by taint_decide))
    fun v s hs => zfront_ok (h v s hs).1 (h v s hs).2) (two_taint _ pins_zL (by taint_decide))

end VG.Proof.Dsa.PPC64LE
