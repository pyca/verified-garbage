module

public import VerifiedGarbage.Proof.Dsa.RISCV64.RSCTFin
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
meta import VerifiedGarbage.Proof.Dsa.RISCV64.RSCTFin
import VerifiedGarbage.Proof.Dsa.RISCV64.RSFn
public import VerifiedGarbage.Proof.Dsa.RISCV64.RSAttempt
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.RISCV64.RSSpec
import VerifiedGarbage.Proof.Dsa.RISCV64.RSFinish
import VerifiedGarbage.Proof.Dsa.RISCV64.SignCTB
import VerifiedGarbage.Proof.Dsa.RISCV64.SignFn
import VerifiedGarbage.Proof.Dsa.RISCV64.Sizes
import VerifiedGarbage.Proof.Dsa.RandomSignTrace
import VerifiedGarbage.Proof.Dsa.RandomSignTraceResult
import VerifiedGarbage.Proof.Dsa.RandomTraceResult
import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Dsa.RISCV64.RSFn
meta import VerifiedGarbage.Proof.Dsa.RISCV64.RSAttempt
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Dsa.RISCV64.RSSpec
meta import VerifiedGarbage.Proof.Dsa.RISCV64.RSFinish
meta import VerifiedGarbage.Proof.Dsa.RISCV64.SignCTB
meta import VerifiedGarbage.Proof.Dsa.RISCV64.SignFn
meta import VerifiedGarbage.Proof.Dsa.RISCV64.Sizes
meta import VerifiedGarbage.Proof.Dsa.RandomSignTrace
meta import VerifiedGarbage.Proof.Dsa.RandomSignTraceResult
meta import VerifiedGarbage.Proof.Dsa.RandomTraceResult
meta import VerifiedGarbage.Proof.Dsa.RandomSignResult
meta import VerifiedGarbage.Proof.Dsa.PackedBytes
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# Randomized DSA signing on RISC-V: constant time

As on PPC64LE (`Proof/Dsa/PPC64LE/RandomSign/CT.lean`). `randomSign_ct`:
two runs from states that satisfy `rsContract` and agree on its public
data (the arguments, the key's public octets, and the result's status,
octets consumed and trace) leak the same trace. The runs are followed
together (`SameTrace`): the pieces the taint analysis checks from the
registers both runs agree on (`st_taint`), cut after the loads whose
results the code uses as addresses (the scan's length; `out` and `used`,
`RSCTFin.lean`), the calls of `vg_dsa_sign`, constant time
(`CT.sign_ct`) for the key's public octets and the call's success, which
the trace declassifies (`call_st`), and the branches on public data: q,
the sampling decisions (`sample_st`), the attempts' statuses, with the
callee's `u32` result zero-extended.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.RS

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Impl.Dsa.RISCV64.RandomSign
open VG.Proof.Mont
open VG.Proof.Dsa.RISCV64.Rnd
open VG.Proof.Dsa (RandomSignInput randomSignDraw randomSignRemaining randomSignAttemptStatus)
open VG.Proof.Dsa.Random (sampleStatus)

/-! ## The public data -/

/-- The key's public octets, as the contract declassifies them. -/
abbrev keyLeak (s₀ : State) : List Nat :=
  Spec.Dsa.publicBytesLeak (rlOf s₀).pl (rlOf s₀).ql (Spec.Rsa.bytesAt s₀.mem (rlOf s₀).key (rlOf s₀).kl)

theorem pre_kl {s₀ : State} (h : rsContract.pre s₀) : (rlOf s₀).kl = (s₀.gpr .a4).toNat := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, hkl, -⟩ := h
  simp only [RL.kl, rlOf]; omega

theorem bytesAt_take (m : Mem) (p : Addr) {n k : Nat} (h : n ≤ k) :
    (Spec.Rsa.bytesAt m p k).take n = Spec.Rsa.bytesAt m p n := by
  have := VG.Proof.Dsa.bytesAt_slice m p (offset := 0) (len := n) (total := k) (by omega)
  rwa [List.drop_zero, show p + BitVec.ofNat 64 0 = p from BitVec.add_zero p] at this

/-- What the public data fix: the call's data, the key's public octets, and
the result's status and trace. -/
theorem pub_facts {s₁ s₂ : State} (h₁ : rsContract.pre s₁) (h₂ : rsContract.pre s₂) (hp : rsContract.pub s₁ s₂) :
    rlOf s₁ = rlOf s₂ ∧ keyLeak s₁ = keyLeak s₂ ∧ (resOf s₁).status = (resOf s₂).status ∧
      (resOf s₁).trace = (resOf s₂).trace := by
  have k₁ := pre_kl h₁
  have k₂ := pre_kl h₂
  obtain ⟨hsp, e0, -, e2, e3, e4, e5, e6, e7, a0, a1, a2, a3, a4, hl⟩ := hp
  have eL : rlOf s₁ = rlOf s₂ := by
    simp only [rlOf, hsp, e0, e2, e3, e5, e6, e7, a0, a1, a2, a3, a4]
  have hlen : (Spec.Dsa.publicBytesLeak (s₁.gpr .a5).toNat (s₁.gpr .a6).toNat
      (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a3) (s₁.gpr .a4).toNat) ++ [(rsRes s₁).status, (rsRes s₁).used]).length =
      (Spec.Dsa.publicBytesLeak (s₂.gpr .a5).toNat (s₂.gpr .a6).toNat
      (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a3) (s₂.gpr .a4).toNat) ++ [(rsRes s₂).status, (rsRes s₂).used]).length := by
    simp only [Spec.Dsa.publicBytesLeak, List.length_append, List.length_map, List.length_take,
      VG.Proof.Bignum.bytesAt_length, e4, e5, e6, List.length_cons, List.length_nil]
  obtain ⟨e1, e2⟩ := List.append_inj hl hlen
  obtain ⟨e3, e4⟩ := List.append_inj' e1 rfl
  have est := (List.cons.inj e4).1
  rw [rsRes_eq h₁, rsRes_eq h₂] at est e2
  refine ⟨eL, ?_, est, e2⟩
  simp only [keyLeak]
  rw [k₁, k₂]
  exact e3

/-- q's octets are within the key's public part. -/
theorem qb_eq {s₁ s₂ : State} (h₁ : rsContract.pre s₁) (eL : rlOf s₁ = rlOf s₂) (ek : keyLeak s₁ = keyLeak s₂) :
    qbOf (rlOf s₁) s₁.mem = qbOf (rlOf s₁) s₂.mem := by
  have hL := rlOf_ok h₁
  have hq := hL.ql
  simp only [keyLeak, Spec.Dsa.publicBytesLeak, ← eL] at ek
  have e := (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp ek
  rw [bytesAt_take _ _ (by simp only [RL.kl]; omega), bytesAt_take _ _ (by simp only [RL.kl]; omega)] at e
  have := VG.Proof.Dsa.bytesAt_slice s₁.mem (rlOf s₁).key (offset := (rlOf s₁).pl) (len := (rlOf s₁).ql)
    (total := 3 * (rlOf s₁).pl + (rlOf s₁).ql) (by omega)
  rw [e, VG.Proof.Dsa.bytesAt_slice s₂.mem (rlOf s₁).key (by omega)] at this
  exact this.symm

/-! ## The scan of q -/

/-- The first instructions of the scan: q's address and length. -/
theorem qargs_ok {s₀ t : State} (h : rsContract.pre s₀) (hc : Ctx (rlOf s₀) s₀ t) :
    WP isa (.block (lenP .t3 ++ ([.add .s7 .s1 .t3] : List Instr) ++ lenQ .s8)) t fun t₁ =>
      ((t₁.gpr .s7 = off (rlOf s₀).key (rlOf s₀).pl ∧ t₁.gpr .s8 = BitVec.ofNat 64 (rlOf s₀).ql ∧
        t₁.mem = t.mem) ∧ Keep [.t3, .s7, .s8] t t₁) ∧ t₁.sp = t.sp := by
  have hL := rlOf_ok h
  have hq := hL.ql
  have hp := hL.pl
  have e1 := lenP_eq (pl := (rlOf s₀).pl) (ql := (rlOf s₀).ql) (by omega) (by omega)
  have e2 := lenQ_eq (pl := (rlOf s₀).pl) (ql := (rlOf s₀).ql) (by omega) (by omega)
  exact wp_sp (WP.keep [.t3, .s7, .s8] (by brun [lenP, lenQ, hc.s1, hc.s2, e1, e2]) (by decide) (by rfl))

/-- q's octets, and the one after, are readable. -/
theorem q_in {s₀ t : State} (h : rsContract.pre s₀) (hc : Ctx (rlOf s₀) s₀ t) :
    ∀ i ≤ (rlOf s₀).ql, InRegions (t.rd ++ t.wr) (off (off (rlOf s₀).key (rlOf s₀).pl) i) 1 := by
  have hL := rlOf_ok h
  have hq := hL.ql
  have hp := hL.pl
  have hk := hL.nwKey
  have ekl : (rlOf s₀).kl = 3 * (rlOf s₀).pl + 2 * (rlOf s₀).ql := rfl
  obtain ⟨hrd, -⟩ := regions_eq h
  intro i hi
  rw [hc.rd, off_off]
  exact ⟨(rlOf s₀).keyR, List.mem_append_left _ (by rw [hrd]; exact List.mem_cons_self ..),
    VG.Offset.contains_base _ (by omega) (by omega)⟩

theorem prepareQ_st {s₁ s₂ t₁ t₂ : State} (h₁ : rsContract.pre s₁) (h₂ : rsContract.pre s₂)
    (eL : rlOf s₁ = rlOf s₂) (eq : qbOf (rlOf s₁) s₁.mem = qbOf (rlOf s₁) s₂.mem)
    (c₁ : Ctx (rlOf s₁) s₁ t₁) (c₂ : Ctx (rlOf s₂) s₂ t₂) : SameTrace isa prepareQ t₁ t₂ := by
  have hsp := (ctx_eq eL c₁ c₂).1
  have hr := (ctx_eq eL c₁ c₂).2
  have hq₁ := (rlOf_ok h₁).ql
  have hq₂ := (rlOf_ok h₂).ql
  unfold prepareQ prepare
  refine SameTrace.seq (st_taint [.s1, .s2] hsp hr.sub (by taint_decide)) (qargs_ok h₁ c₁)
    (qargs_ok h₂ c₂) fun u₁ u₂ ⟨⟨⟨a7, a8, m1⟩, k1⟩, sp1⟩ ⟨⟨⟨b7, b8, m2⟩, k2⟩, sp2⟩ => ?_
  have usp : u₁.sp = u₂.sp := by rw [sp1, sp2, hsp]
  have e7 : u₁.gpr .s7 = u₂.gpr .s7 := by rw [a7, b7, eL]
  have e8 : u₁.gpr .s8 = u₂.gpr .s8 := by rw [a8, b8, eL]
  refine SameTrace.seq (st_taint [.s7, .s8] usp ⟨e7, e8⟩ (by taint_decide))
    (wp_sp (sigLen_ok a7 a8 (by omega) (by omega) fun i hi => by
      rw [k1.2.1, k1.2.2]; exact q_in h₁ c₁ i (by omega)))
    (wp_sp (sigLen_ok b7 b8 (by omega) (by omega) fun i hi => by
      rw [k2.2.1, k2.2.2]; exact q_in h₂ c₂ i (by omega)))
    fun v₁ v₂ ⟨⟨⟨x1, _⟩, kv1⟩, spv1⟩ ⟨⟨⟨y1, _⟩, kv2⟩, spv2⟩ => ?_
  rw [m1, c₁.qb (rlOf_ok h₁)] at x1
  rw [m2, c₂.qb (rlOf_ok h₂), ← eL, ← eq] at y1
  exact st_taint [.s7, .s8, .a1] (by rw [spv1, spv2, usp])
    ⟨by rw [kv1.gpr (by decide), kv2.gpr (by decide), e7], by rw [kv1.gpr (by decide), kv2.gpr (by decide), e8],
      EqRegs.single (by rw [x1, y1])⟩ (by taint_decide)

/-! ## A call of `vg_dsa_sign` -/

/-- The state `vg_dsa_sign` is entered in, after `callArgs`. -/
theorem narrow_vals {s₀ w : State} (A : Args (rlOf s₀) s₀ w) (rd wr : List Region) :
    (w.callEntry.withRegions rd wr).sp = (rlOf s₀).F ∧
      (w.callEntry.withRegions rd wr).gpr .a0 = (rlOf s₀).out ∧
      (w.callEntry.withRegions rd wr).gpr .a1 = BitVec.ofNat 64 (2 * (rlOf s₀).ql) ∧
      (w.callEntry.withRegions rd wr).gpr .a2 = (rlOf s₀).key ∧
      (w.callEntry.withRegions rd wr).gpr .a3 = BitVec.ofNat 64 (rlOf s₀).kl ∧
      (w.callEntry.withRegions rd wr).gpr .a4 = BitVec.ofNat 64 (rlOf s₀).pl ∧
      (w.callEntry.withRegions rd wr).gpr .a5 = off (rlOf s₀).F oNonce ∧
      (w.callEntry.withRegions rd wr).gpr .a6 = BitVec.ofNat 64 (rlOf s₀).ql ∧
      (w.callEntry.withRegions rd wr).gpr .a7 = (rlOf s₀).dig ∧
      stackArg (w.callEntry.withRegions rd wr) 0 = BitVec.ofNat 64 (rlOf s₀).dl ∧
      stackArg (w.callEntry.withRegions rd wr) 1 = (rlOf s₀).scr ∧
      stackArg (w.callEntry.withRegions rd wr) 2 = BitVec.ofNat 64 (rlOf s₀).sl := by
  have hc := A.ctx
  refine ⟨hc.sp, (entry_gpr w rd wr (by decide)).trans A.a0, (entry_gpr w rd wr (by decide)).trans A.a1,
    (entry_gpr w rd wr (by decide)).trans A.a2, (entry_gpr w rd wr (by decide)).trans A.a3,
    (entry_gpr w rd wr (by decide)).trans A.a4, (entry_gpr w rd wr (by decide)).trans A.a5,
    (entry_gpr w rd wr (by decide)).trans A.a6, (entry_gpr w rd wr (by decide)).trans A.a7, ?_, ?_, ?_⟩
  · rw [entry_stackArg, hc.sp]; exact hc.a0
  · rw [entry_stackArg, hc.sp]; exact hc.a1
  · rw [entry_stackArg, hc.sp]; exact hc.a2

/-- What a call declassifies: the key's public octets and the call's success. -/
theorem leak_eq {s₀ w : State} (h : rsContract.pre s₀) (A : Args (rlOf s₀) s₀ w) :
    Spec.Dsa.publicBytesLeak ((w.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))).gpr .a4).toNat
        ((w.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))).gpr .a6).toNat
        (Spec.Rsa.bytesAt (w.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))).mem
          ((w.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))).gpr .a2)
          ((w.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))).gpr .a3).toNat) ++
      [Spec.Dsa.signStatus (sRes (w.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))))] =
    keyLeak s₀ ++ [Spec.Dsa.signStatus (sresOf (rlOf s₀) w.mem)] := by
  have hL := rlOf_ok h
  have hp := hL.pl
  have hq := hL.ql
  obtain ⟨-, -, -, g2, g3, g4, -, g6, -⟩ := narrow_vals A (signRd (rlOf s₀)) (signWr (rlOf s₀))
  rw [sres_eq h A, g2, g3, g4, g6, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := (rlOf s₀).pl) (by omega), Nat.mod_eq_of_lt (a := (rlOf s₀).ql) (by omega),
    Nat.mod_eq_of_lt (a := (rlOf s₀).kl) (by simp only [RL.kl]; omega)]
  show Spec.Dsa.publicBytesLeak _ _ (Spec.Rsa.bytesAt w.mem _ _) ++ _ = _
  rw [A.ctx.key]

theorem call_st {s₁ s₂ w₁ w₂ : State} (h₁ : rsContract.pre s₁) (h₂ : rsContract.pre s₂) (eL : rlOf s₁ = rlOf s₂)
    (ek : keyLeak s₁ = keyLeak s₂) (A₁ : Args (rlOf s₁) s₁ w₁) (A₂ : Args (rlOf s₂) s₂ w₂)
    (hs : Spec.Dsa.signStatus (sresOf (rlOf s₁) w₁.mem) = Spec.Dsa.signStatus (sresOf (rlOf s₂) w₂.mem)) :
    SameTrace isa (.call "vg_dsa_sign" Impl.Dsa.RISCV64.Sign.sign) w₁ w₂ := by
  refine SameTrace.of_relCT (RelCT.callEx (k := sContract) sign_correct CT.sign_ct
    (P := fun a b => a = w₁ ∧ b = w₂) fun _ _ ⟨e₁, e₂⟩ => ?_) ⟨rfl, rfl⟩
  subst e₁ e₂
  obtain ⟨c₁, cw₁⟩ := sign_cov h₁ A₁.ctx
  obtain ⟨c₂, cw₂⟩ := sign_cov h₂ A₂.ctx
  refine ⟨_, _, _, _, sign_pre h₁ A₁, sign_pre h₂ A₂, ?_, c₁, cw₁, c₂, cw₂⟩
  obtain ⟨p0, p3, p4, p5, p6, p7, p8, p9, p10, q0, q1, q2⟩ := narrow_vals A₁ (signRd (rlOf s₁)) (signWr (rlOf s₁))
  obtain ⟨r0, r3, r4, r5, r6, r7, r8, r9, r10, u0, u1, u2⟩ := narrow_vals A₂ (signRd (rlOf s₂)) (signWr (rlOf s₂))
  refine ⟨by rw [p0, r0, eL], by rw [p3, r3, eL], by rw [p4, r4, eL], by rw [p5, r5, eL], by rw [p6, r6, eL],
    by rw [p7, r7, eL], by rw [p8, r8, eL], by rw [p9, r9, eL], by rw [p10, r10, eL], by rw [q0, u0, eL],
    by rw [q1, u1, eL], by rw [q2, u2, eL], ?_⟩
  rw [leak_eq h₁ A₁, leak_eq h₂ A₂, ek, hs]

/-- After the call: the status, from the result's low word zero-extended, and the attempts left. -/
theorem callFinish_st {v₁ v₂ : State} (hsp : v₁.sp = v₂.sp) (h6 : v₁.gpr .s6 = v₂.gpr .s6) {st₁ st₂ : Nat}
    (h₁ : ((v₁.gpr .a0).setWidth 32).toNat = st₁) (h₂ : ((v₂.gpr .a0).setWidth 32).toNat = st₂)
    (hs : st₁ = st₂) : SameTrace isa callFinish v₁ v₂ := by
  have W : ∀ {y : State}, WP isa (.block [.shift .sll .d .a0 .a0 32, .shift .srl .d .a0 .a0 32]) y fun z =>
      ((z.mem = y.mem ∧ z.gpr .a0 = (y.gpr .a0 <<< 32) >>> 32) ∧ Keep [.a0] y z) ∧ z.sp = y.sp :=
    fun {_} => wp_sp (WP.keep [.a0] (by brun) (by decide) (by rfl))
  unfold callFinish
  refine SameTrace.seq (st_taint [] hsp trivial (by taint_decide)) W W
    fun u₁ u₂ ⟨⟨⟨_, a0⟩, k1⟩, sp1⟩ ⟨⟨⟨_, b0⟩, k2⟩, sp2⟩ => ?_
  have usp : u₁.sp = u₂.sp := by rw [sp1, sp2, hsp]
  exact SameTrace.ite (by rw [Steps.eval_zero, Steps.eval_zero, a0, b0, zx_beq_zero h₁, zx_beq_zero h₂, hs])
    (fun _ => by
      exact st_taint [.s6] usp (EqRegs.single (by rw [k1.gpr (by decide), k2.gpr (by decide), h6]))
        (by taint_decide))
    (fun _ => by exact st_taint [] usp trivial (by taint_decide))

/-! ## The attempts -/

/-- The sampler's data and q agree. -/
theorem same_q {s₁ s₂ : State} (eL : rlOf s₁ = rlOf s₂) (eq : qbOf (rlOf s₁) s₁.mem = qbOf (rlOf s₁) s₂.mem) :
    qOf s₂ = qOf s₁ ∧ eOf s₂ = eOf s₁ := by
  refine ⟨?_, ?_⟩
  · show Spec.Dsa.decodeBE (qbOf (rlOf s₂) s₂.mem) = Spec.Dsa.decodeBE (qbOf (rlOf s₁) s₁.mem)
    rw [← eL, ← eq]
  · show seOf (rlOf s₂) (qbOf (rlOf s₂) s₂.mem) = seOf (rlOf s₁) (qbOf (rlOf s₁) s₁.mem)
    rw [← eL, ← eq]

/-- The signature a call computes, from an accepted draw `k` in the nonce. -/
theorem sres_draw {s₀ t w : State} (hc : Ctx (rlOf s₀) s₀ t) (hw : w.mem = t.mem)
    {k : Nat} (hn : Spec.Rsa.bytesAt t.mem (off (rlOf s₀).F oNonce) (rlOf s₀).ql = Spec.Dsa.encodeBE (rlOf s₀).ql k) :
    sresOf (rlOf s₀) w.mem = Spec.Dsa.signBytes (inpOf (rlOf s₀) s₀.mem).pLen (inpOf (rlOf s₀) s₀.mem).qLen
      (inpOf (rlOf s₀) s₀.mem).key (Spec.Dsa.encodeBE (inpOf (rlOf s₀) s₀.mem).qLen k)
      (inpOf (rlOf s₀) s₀.mem).digest := by
  simp only [sresOf, inpOf]
  rw [hw, hc.key, hc.digB, hn]

theorem attempt_st {s₁ s₂ x₁ x₂ : State} {a u : Nat} (h₁ : rsContract.pre s₁) (h₂ : rsContract.pre s₂)
    (eL : rlOf s₁ = rlOf s₂) (ek : keyLeak s₁ = keyLeak s₂) (hq : 1 < qOf s₁) (A₁ : AttInv s₁ a u x₁)
    (A₂ : AttInv s₂ a u x₂)
    (ht : (randomSignRemaining (inpOf (rlOf s₁) s₁.mem) u a).trace =
      (randomSignRemaining (inpOf (rlOf s₂) s₂.mem) u a).trace) :
    SameTrace isa attempt x₁ x₂ := by
  have eq := qb_eq h₁ eL ek
  have hL₁ := rlOf_ok h₁
  have hL₂ := rlOf_ok h₂
  obtain ⟨eQ, eE⟩ := same_q eL eq
  have hq₂ : 1 < qOf s₂ := eQ ▸ hq
  have hE₁ : (eOf s₁).Ok := seOf_ok hL₁ s₁.mem hq
  have hE₂ : (eOf s₂).Ok := seOf_ok hL₂ s₂.mem hq₂
  have hQ₁ := seOf_Q (L := rlOf s₁) s₁.mem hq
  have hQ₂ := seOf_Q (L := rlOf s₂) s₂.mem hq₂
  have env₁ := A₁.sc.env h₁ hq
  have env₂ := A₂.sc.env h₂ hq₂
  have env₂' : SEnv (eOf s₁) (randOf (rlOf s₂) s₂.mem) x₂ := eE ▸ env₂
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by have := A₁.ha1; omega⟩
  have tD : (randomSignDraw (inpOf (rlOf s₁) s₁.mem) u).trace = (randomSignDraw (inpOf (rlOf s₂) s₂.mem) u).trace := by
    rw [← VG.Proof.Dsa.random_sign_trace_draw _ u a', ← VG.Proof.Dsa.random_sign_trace_draw _ u a', ht]
  have dq₁ : Spec.Dsa.Random.sample (qOf s₁) 128 ((randOf (rlOf s₁) s₁.mem).drop u) =
      randomSignDraw (inpOf (rlOf s₁) s₁.mem) u := (draw_eq hL₁ s₁.mem u).symm
  have dq₂ : Spec.Dsa.Random.sample (qOf s₂) 128 ((randOf (rlOf s₂) s₂.mem).drop u) =
      randomSignDraw (inpOf (rlOf s₂) s₂.mem) u := (draw_eq hL₂ s₂.mem u).symm
  have tS : (Spec.Dsa.Random.sample (qOf s₁) 128 ((randOf (rlOf s₁) s₁.mem).drop u)).trace =
      (Spec.Dsa.Random.sample (qOf s₁) 128 ((randOf (rlOf s₂) s₂.mem).drop u)).trace := by
    rw [dq₁, ← eQ, dq₂]; exact tD
  have eSt : sampleStatus (randomSignDraw (inpOf (rlOf s₁) s₁.mem) u) =
      sampleStatus (randomSignDraw (inpOf (rlOf s₂) s₂.mem) u) := by
    have := (VG.Proof.Dsa.Random.sample_trace_agree tS).2.2
    rwa [dq₁, ← eQ, dq₂] at this
  unfold attempt
  refine SameTrace.seq (sample_st hE₁ hQ₁ env₁ env₂' A₁.s5 A₂.s5 A₁.hu tS) (sample_ok hE₁ hQ₁ env₁ A₁.s5 A₁.hu)
    (sample_ok hE₂ hQ₂ env₂ A₂.s5 A₂.hu) fun y₁ y₂ so₁ so₂ => ?_
  rw [dq₁] at so₁
  rw [dq₂] at so₂
  obtain ⟨sc₁, nz₁⟩ := sampled h₁ A₁.sc A₁.zero so₁ hq
  obtain ⟨sc₂, nz₂⟩ := sampled h₂ A₂.sc A₂.zero so₂ hq₂
  have ysp : y₁.sp = y₂.sp := by rw [sc₁.ctx.sp, sc₂.ctx.sp, eL]
  have W : ∀ {y : State}, WP isa (.block [.addi .a0 .s10 (-1)]) y fun z =>
      ((z.mem = y.mem ∧ z.gpr .a0 = y.gpr .s10 - BitVec.ofNat 64 1) ∧ Keep [.a0] y z) ∧ z.sp = y.sp :=
    fun {_} => wp_sp (WP.keep [.a0] (by brun) (by decide) (by rfl))
  refine SameTrace.seq (st_taint [] ysp trivial (by taint_decide)) W W
    fun z₁ z₂ ⟨⟨⟨m1, a3⟩, k1⟩, sp1⟩ ⟨⟨⟨m2, b3⟩, k2⟩, sp2⟩ => ?_
  have zsp : z₁.sp = z₂.sp := by rw [sp1, sp2, ysp]
  have hst₁ := sampleStatus_le (randomSignDraw (inpOf (rlOf s₁) s₁.mem) u)
  have hst₂ := sampleStatus_le (randomSignDraw (inpOf (rlOf s₂) s₂.mem) u)
  have ev₁ : isa.eval (.zero .a0) z₁ =
      some (decide (sampleStatus (randomSignDraw (inpOf (rlOf s₁) s₁.mem) u) = 1)) := by
    rw [Steps.eval_zero, a3, so₁.s10, sub1_beq _ (by omega)]
  have ev₂ : isa.eval (.zero .a0) z₂ =
      some (decide (sampleStatus (randomSignDraw (inpOf (rlOf s₂) s₂.mem) u) = 1)) := by
    rw [Steps.eval_zero, b3, so₂.s10, sub1_beq _ (by omega)]
  refine SameTrace.ite (by rw [ev₁, ev₂, eSt]) (fun hc => ?_) (fun _ => SameTrace.block_nil)
  rw [ev₁, Option.some.injEq, decide_eq_true_eq] at hc
  obtain ⟨k₁, hk₁⟩ := Option.isSome_iff_exists.mp (sampleStatus_some.mp hc)
  obtain ⟨k₂, hk₂⟩ := Option.isSome_iff_exists.mp (sampleStatus_some.mp (eSt ▸ hc))
  have cz₁ := (sc₁.keep hL₁ k1 sp1 m1).ctx
  have cz₂ := (sc₂.keep hL₂ k2 sp2 m2).ctx
  have nn₁ : Spec.Rsa.bytesAt z₁.mem (off (rlOf s₁).F oNonce) (rlOf s₁).ql = Spec.Dsa.encodeBE (rlOf s₁).ql k₁ := by
    rw [m1]; exact nonce_eq (W := (eOf s₁).W) hE₁.Wq nz₁ (so₁.cand k₁ hk₁)
  have nn₂ : Spec.Rsa.bytesAt z₂.mem (off (rlOf s₂).F oNonce) (rlOf s₂).ql = Spec.Dsa.encodeBE (rlOf s₂).ql k₂ := by
    rw [m2]; exact nonce_eq (W := (eOf s₂).W) hE₂.Wq nz₂ (so₂.cand k₂ hk₂)
  have hr := (ctx_eq eL cz₁ cz₂).2
  refine SameTrace.seq (st_taint [.s1, .s2] zsp hr.sub (by taint_decide))
    (callArgs_ok hL₁ rfl cz₁) (callArgs_ok hL₂ rfl cz₂) fun w₁ w₂ ⟨⟨A₁', mw₁, kw₁⟩, _⟩ ⟨⟨A₂', mw₂, kw₂⟩, _⟩ => ?_
  have hsi := VG.Proof.Dsa.random_sign_trace_call ht hk₁ hk₂
  have hs : Spec.Dsa.signStatus (sresOf (rlOf s₁) w₁.mem) = Spec.Dsa.signStatus (sresOf (rlOf s₂) w₂.mem) := by
    rw [sres_draw cz₁ mw₁ nn₁, sres_draw cz₂ mw₂ nn₂]
    simp only [Spec.Dsa.signStatus, hsi]
  have w6 : ∀ {s₀ x y z w : State} {S : Spec.Dsa.Random.Sample}, AttInv s₀ (a' + 1) u x →
      SampleOut (eOf s₀) (randOf (rlOf s₀) s₀.mem) u S x y → Keep [.a0] y z → Keep argRegs' z w →
      w.gpr .s6 = BitVec.ofNat 64 (a' + 1) := fun A so k kw =>
    (kw.gpr (by decide)).trans ((k.gpr (by decide)).trans ((so.keep.gpr (by decide)).trans A.s6))
  refine SameTrace.seq (call_st h₁ h₂ eL ek A₁' A₂' hs) (sign_ok h₁ A₁') (sign_ok h₂ A₂') fun v₁ v₂ S₁ S₂ => ?_
  exact callFinish_st (by rw [S₁.ctx.sp, S₂.ctx.sp, eL])
    (by rw [S₁.pres _ (by decide), S₂.pres _ (by decide), w6 A₁ so₁ k1 kw₁, w6 A₂ so₂ k2 kw₂]) S₁.a0 S₂.a0 hs

/-- The attempts' loop: both runs with the same attempts left, octets
consumed and trace from there. -/
def AI (s₁ s₂ : State) (n : Nat) (x₁ x₂ : State) : Prop :=
  ∃ u, AttInv s₁ n u x₁ ∧ AttInv s₂ n u x₂ ∧
    (randomSignRemaining (inpOf (rlOf s₁) s₁.mem) u n).trace = (randomSignRemaining (inpOf (rlOf s₂) s₂.mem) u n).trace

/-- Two draws with the same trace consume as much, and agree on acceptance and status. -/
theorem draw_agree {s₁ s₂ : State} {u fuel : Nat} (h₁ : rsContract.pre s₁) (h₂ : rsContract.pre s₂)
    (eL : rlOf s₁ = rlOf s₂) (ek : keyLeak s₁ = keyLeak s₂)
    (ht : (randomSignRemaining (inpOf (rlOf s₁) s₁.mem) u (fuel + 1)).trace =
      (randomSignRemaining (inpOf (rlOf s₂) s₂.mem) u (fuel + 1)).trace) :
    (randomSignDraw (inpOf (rlOf s₁) s₁.mem) u).used = (randomSignDraw (inpOf (rlOf s₂) s₂.mem) u).used ∧
      (randomSignDraw (inpOf (rlOf s₁) s₁.mem) u).scalar.isSome =
        (randomSignDraw (inpOf (rlOf s₂) s₂.mem) u).scalar.isSome ∧
      sampleStatus (randomSignDraw (inpOf (rlOf s₁) s₁.mem) u) =
        sampleStatus (randomSignDraw (inpOf (rlOf s₂) s₂.mem) u) := by
  obtain ⟨eQ, -⟩ := same_q eL (qb_eq h₁ eL ek)
  have tD : (randomSignDraw (inpOf (rlOf s₁) s₁.mem) u).trace = (randomSignDraw (inpOf (rlOf s₂) s₂.mem) u).trace := by
    rw [← VG.Proof.Dsa.random_sign_trace_draw _ u fuel, ← VG.Proof.Dsa.random_sign_trace_draw _ u fuel, ht]
  have dq₁ : Spec.Dsa.Random.sample (qOf s₁) 128 ((randOf (rlOf s₁) s₁.mem).drop u) =
      randomSignDraw (inpOf (rlOf s₁) s₁.mem) u := (draw_eq (rlOf_ok h₁) s₁.mem u).symm
  have dq₂ : Spec.Dsa.Random.sample (qOf s₂) 128 ((randOf (rlOf s₂) s₂.mem).drop u) =
      randomSignDraw (inpOf (rlOf s₂) s₂.mem) u := (draw_eq (rlOf_ok h₂) s₂.mem u).symm
  have tS : (Spec.Dsa.Random.sample (qOf s₁) 128 ((randOf (rlOf s₁) s₁.mem).drop u)).trace =
      (Spec.Dsa.Random.sample (qOf s₁) 128 ((randOf (rlOf s₂) s₂.mem).drop u)).trace := by
    rw [dq₁, ← eQ, dq₂]; exact tD
  have := VG.Proof.Dsa.Random.sample_trace_agree tS
  rwa [dq₁, ← eQ, dq₂] at this

theorem attempts_st {s₁ s₂ : State} (h₁ : rsContract.pre s₁) (h₂ : rsContract.pre s₂) (eL : rlOf s₁ = rlOf s₂)
    (ek : keyLeak s₁ = keyLeak s₂) (hq : 1 < qOf s₁) {n : Nat} {x₁ x₂ : State} (hi : AI s₁ s₂ n x₁ x₂) :
    SameTrace isa attempts x₁ x₂ := by
  have hq₂ : 1 < qOf s₂ := (same_q eL (qb_eq h₁ eL ek)).1 ▸ hq
  unfold attempts
  refine st_loop (AI s₁ s₂) (fun n x₁ x₂ ⟨u, A₁, A₂, ht⟩ => ?_) hi
  have xsp : x₁.sp = x₂.sp := by rw [A₁.sc.ctx.sp, A₂.sc.ctx.sp, eL]
  refine ⟨SameTrace.seq (attempt_st h₁ h₂ eL ek hq A₁ A₂ ht) (WP.of_seq (attempt_ok h₁ hq A₁))
    (WP.of_seq (attempt_ok h₂ hq₂ A₂)) fun y₁ y₂ e₁ e₂ => by
      exact st_taint [] (by rw [e₁, e₂, xsp]) trivial (by taint_decide), _, _, attempt_ok h₁ hq A₁,
    attempt_ok h₂ hq₂ A₂, fun t₁ t₂ ⟨ev₁, _, c₁⟩ ⟨ev₂, _, c₂⟩ => ?_⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := A₁.ha1; omega⟩
  obtain ⟨eU, eS, eSt⟩ := draw_agree h₁ h₂ eL ek ht
  have hst := VG.Proof.Dsa.random_sign_attempt_status_agree ht eS eSt
  refine ⟨by rw [ev₁, ev₂, hst], fun hc => ?_⟩
  rw [ev₁, Option.some.injEq, decide_eq_true_eq] at hc
  obtain ⟨hn, i₁⟩ := c₁ hc
  obtain ⟨-, i₂⟩ := c₂ (hst ▸ hc)
  rw [Nat.add_sub_cancel] at i₁ i₂
  refine ⟨n', by omega, _, i₁, eU ▸ i₂, ?_⟩
  have := VG.Proof.Dsa.random_sign_attempt_next_trace ht hc (hst ▸ hc)
  rw [← eU] at this
  exact this

/-! ## The function -/

/-- The attempts' first state. -/
theorem att_init {s₀ t₁ t₂ : State} (h : rsContract.pre s₀) (hq : 1 < qOf s₀) (he : Entered (rlOf s₀) s₀ t₁)
    (sc : Scanned (rlOf s₀) s₀ t₂) (m2 : t₂.mem = t₁.mem)
    (k2 : Keep (([.t3, .s7, .s8] : List Reg) ++ prepRegs) t₁ t₂) :
    AttInv s₀ 8 0 t₂ := by
  have hL := rlOf_ok h
  refine ⟨sc, (k2.gpr (by decide)).trans he.s5, by omega, (k2.gpr (by decide)).trans he.s6, by decide,
    by decide, fun j hj => ?_, VG.Proof.Dsa.RandomSignResultRel.refl _ _ _⟩
  rw [m2]
  have hE : (eOf s₀).Ok := seOf_ok hL s₀.mem hq
  have := hE.Wq
  have := hL.ql
  have e2 : (eOf s₀).ql = (rlOf s₀).ql := rfl
  exact he.nonce j (by omega)

theorem randomSign_ct : ConstantTime isa rsContract.pre rsContract.pub Impl.Dsa.RISCV64.RandomSign.code := by
  refine SameTrace.constantTime fun s₁ s₂ h₁ h₂ hp => ?_
  obtain ⟨eL, ek, est, etr⟩ := pub_facts h₁ h₂ hp
  have eq := qb_eq h₁ eL ek
  obtain ⟨eQ, -⟩ := same_q eL eq
  have hL₁ := rlOf_ok h₁
  have hL₂ := rlOf_ok h₂
  have hsp : s₁.sp = s₂.sp := hp.1
  unfold Impl.Dsa.RISCV64.RandomSign.code
  refine st_alloc ?_
  unfold Impl.Dsa.RISCV64.RandomSign.body
  refine SameTrace.seq (st_taint [] (by simp only [allocd, hsp]) trivial (by taint_decide))
    (entry_ok h₁) (entry_ok h₂) fun t₁ t₂ E₁ E₂ => ?_
  refine SameTrace.seq (prepareQ_st h₁ h₂ eL eq E₁.ctx E₂.ctx) (prepareQ_ok h₁ E₁.ctx) (prepareQ_ok h₂ E₂.ctx)
    fun u₁ u₂ ⟨⟨sc₁, z₁, m₁, k₁⟩, _⟩ ⟨⟨sc₂, z₂, m₂, k₂⟩, _⟩ => ?_
  have usp := (ctx_eq eL sc₁.ctx sc₂.ctx).1
  have z₂' : u₂.gpr .a0 = 0 ↔ ¬ 1 < qOf s₁ := by rw [← eQ]; exact z₂
  refine SameTrace.seq_ite (by rw [Steps.eval_zero, Steps.eval_zero, beq_of_iff z₁, beq_of_iff z₂'])
    (fun _ => ?_) (fun hc => ?_)
  · -- q ≤ 1: no attempt.
    have W : ∀ {s₀ y : State}, (rlOf s₀).Ok → Ctx (rlOf s₀) s₀ y → WP isa (.block [.li .s10 0]) y fun z =>
        Ctx (rlOf s₀) s₀ z ∧ z.gpr .s10 = BitVec.ofNat 64 0 := fun {s₀ y} hL hc =>
      WP.mono (wp_sp (WP.keep (c := .block [.li .s10 0]) [.s10]
        (Q := fun z => z.mem = y.mem ∧ z.gpr .s10 = BitVec.ofNat 64 0) (by brun [exec_li_zero]; rfl) (by decide)
          (by rfl)))
        fun z ⟨⟨⟨mz, az⟩, kz⟩, spz⟩ => ⟨hc.step hL spz kz.2.1 kz.2.2
          (fun r hr => kz.1 r (by revert r hr; decide)) (by rw [mz]; exact Frame.refl _ _), az⟩
    exact SameTrace.seq (st_taint [] usp trivial (by taint_decide)) (W hL₁ sc₁.ctx) (W hL₂ sc₂.ctx)
      fun y₁ y₂ ⟨cy₁, a10⟩ ⟨cy₂, b10⟩ => finish_st h₁ h₂ eL cy₁ cy₂ a10 b10
  · -- q > 1: the attempts.
    rw [Steps.eval_zero, beq_of_iff z₁, Option.some.injEq, decide_eq_false_iff_not, Decidable.not_not] at hc
    have hq₂ : 1 < qOf s₂ := eQ ▸ hc
    have i₁ := att_init h₁ hc E₁ sc₁ m₁ k₁
    have i₂ := att_init h₂ hq₂ E₂ sc₂ m₂ k₂
    exact SameTrace.seq (attempts_st h₁ h₂ eL ek hc ⟨0, i₁, i₂, etr⟩) (attempts_ok h₁ hc 8 0 u₁ i₁)
      (attempts_ok h₂ hq₂ 8 0 u₂ i₂) fun x₁ x₂ o₁ o₂ =>
        finish_st h₁ h₂ eL o₁.sc.ctx o₂.sc.ctx o₁.s10 (o₂.s10.trans (by rw [est]))

end VG.Proof.Dsa.RISCV64.RS
