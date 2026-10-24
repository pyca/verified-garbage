module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Fn
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.CT
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Fn
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.CT
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.CT
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Fn
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sizes
import VerifiedGarbage.Proof.Dsa.RandomSignTrace
import VerifiedGarbage.Proof.Dsa.RandomTraceResult
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Call
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Front
public import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Call
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Front

/-!
# Randomized DSA signing on PPC64LE: constant time

`randomSign_ct`: two runs from states that satisfy `rsContract` and agree on
its public data (the arguments, the key's public part, and the result's
status, octets consumed and trace) leak the same trace. The runs are
followed together (`SameTrace`), as the correctness proof follows each:
every piece the taint analysis checks from the registers both runs agree on
(`st_taint`), and every branch it cannot is decided by public data: q, the
sampling decisions (`sample_st`), and the success of each call of
`vg_dsa_sign` (`random_sign_trace_call`), whose own run is constant time
(`sign_ct`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.RS

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random
open VG.Impl.Dsa.PPC64LE.RandomSign
open VG.Proof.Mont
open VG.Proof.Dsa.PPC64LE.Rnd
open VG.Proof.Dsa (RandomSignInput randomSignDraw randomSignRemaining randomSignAttemptStatus)
open VG.Proof.Dsa.Random (sampleStatus)

/-! ## The public data -/

/-- The key's public octets, as the contract declassifies them. -/
abbrev keyLeak (s₀ : State) : List Nat :=
  Spec.Dsa.publicBytesLeak (rlOf s₀).pl (rlOf s₀).ql (Spec.Rsa.bytesAt s₀.mem (rlOf s₀).key (rlOf s₀).kl)

theorem pre_kl {s₀ : State} (h : rsContract.pre s₀) : (rlOf s₀).kl = (s₀.gpr .r7).toNat := by
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
  obtain ⟨hsp, h3, -, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, hl⟩ := hp
  have eL : rlOf s₁ = rlOf s₂ := by
    simp only [rlOf, hsp, h3, h5, h6, h8, h9, h10, a0, a1, a2, a3, a4]
  have hlen : (Spec.Dsa.publicBytesLeak (s₁.gpr .r8).toNat (s₁.gpr .r9).toNat
      (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r6) (s₁.gpr .r7).toNat) ++ [(rsRes s₁).status, (rsRes s₁).used]).length =
      (Spec.Dsa.publicBytesLeak (s₂.gpr .r8).toNat (s₂.gpr .r9).toNat
      (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r6) (s₂.gpr .r7).toNat) ++ [(rsRes s₂).status, (rsRes s₂).used]).length := by
    simp only [Spec.Dsa.publicBytesLeak, List.length_append, List.length_map, List.length_take,
      VG.Proof.Bignum.bytesAt_length, h7, h8, h9, List.length_cons, List.length_nil]
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

/-! ## The frame and the scan of q -/

theorem st_alloc {n : Nat} {body : Prog isa} {s₁ s₂ : State} (hsp : s₁.sp = s₂.sp)
    (h : SameTrace isa body (allocated n s₁) (allocated n s₂)) :
    SameTrace isa (.frame (.alloc n) body (.free n)) s₁ s₂ :=
  SameTrace.of_relCT (RelCT.alloc (P := fun a b => a = s₁ ∧ b = s₂) (fun _ _ ⟨e₁, e₂⟩ => by subst e₁ e₂; exact hsp)
    (h.to_relCT.mono (fun a b ⟨_, _, ⟨e₁, e₂⟩, ea, eb⟩ => by subst e₁ e₂; exact ⟨ea, eb⟩) fun _ _ h => h))
    ⟨rfl, rfl⟩

/-- Two states of the body with the same call's data agree on its registers. -/
theorem ctx_eq {s₁ s₂ t₁ t₂ : State} (eL : rlOf s₁ = rlOf s₂) (c₁ : Ctx (rlOf s₁) s₁ t₁)
    (c₂ : Ctx (rlOf s₂) s₂ t₂) :
    t₁.sp = t₂.sp ∧ EqRegs t₁ t₂ [.r18, .r19, .r20, .r21, .r22, .r23, .r24, .r30] :=
  ⟨by rw [c₁.sp, c₂.sp, eL], by rw [c₁.r18, c₂.r18, eL], by rw [c₁.r19, c₂.r19, eL], by rw [c₁.r20, c₂.r20, eL],
    by rw [c₁.r21, c₂.r21, eL], by rw [c₁.r22, c₂.r22, eL], by rw [c₁.r23, c₂.r23, eL], by rw [c₁.r24, c₂.r24, eL],
    EqRegs.single (by rw [c₁.r30, c₂.r30, eL])⟩

theorem EqRegs.sub {s₁ s₂ : State} {rs : List Reg} (h : EqRegs s₁ s₂ rs) {rs' : List Reg}
    (hs : ∀ r ∈ rs', r ∈ rs := by decide) : EqRegs s₁ s₂ rs' := by
  induction rs' with
  | nil => trivial
  | cons r rs' ih =>
    cases rs' with
    | nil => exact h.mem r (hs r (List.mem_singleton_self r))
    | cons r' rs'' =>
      exact ⟨h.mem r (hs r (List.mem_cons_self ..)), ih fun x hx => hs x (List.mem_cons_of_mem _ hx)⟩

/-- The first instructions of the scan: q's address and length. -/
theorem qargs_ok {s₀ t : State} (hc : Ctx (rlOf s₀) s₀ t) :
    WP isa (.block [.add .r12 .r19 .r20, .addi .r6 .r21 0]) t fun t₁ =>
      (t₁.gpr .r12 = off (rlOf s₀).key (rlOf s₀).pl ∧ t₁.gpr .r6 = BitVec.ofNat 64 (rlOf s₀).ql ∧
        t₁.mem = t.mem) ∧ Keep [.r6, .r12] t t₁ :=
  WP.keep [.r6, .r12] (by prun [hc.r19, hc.r20, hc.r21, add0]) (by decide)

/-- q's octets, and the one after, are readable. -/
theorem q_in {s₀ t : State} (h : rsContract.pre s₀) (hc : Ctx (rlOf s₀) s₀ t) :
    ∀ i ≤ (rlOf s₀).ql, InRegions (t.rd ++ t.wr) (off (off (rlOf s₀).key (rlOf s₀).pl) i) 1 := by
  have hL := rlOf_ok h
  have hq := hL.ql
  have hp := hL.pl
  have ekl : (rlOf s₀).kl = 3 * (rlOf s₀).pl + 2 * (rlOf s₀).ql := rfl
  obtain ⟨hrd, -⟩ := regions_eq h
  intro i hi
  rw [hc.rd, off_off]
  exact ⟨(rlOf s₀).keyR, List.mem_append_left _ (by rw [hrd]; exact List.mem_cons_self ..),
    VG.Offset.contains_base _ (by omega) (by omega)⟩

/-- The significant octets of q, which `sigLen` counts. -/
theorem sig_eq {s₀ t u : State} (h : rsContract.pre s₀) (hc : Ctx (rlOf s₀) s₀ t) (hm : u.mem = t.mem) :
    Spec.Rsa.bytesAt u.mem (off (rlOf s₀).key (rlOf s₀).pl) (rlOf s₀).ql = qbOf (rlOf s₀) s₀.mem := by
  rw [hm]; exact hc.qb (rlOf_ok h)

theorem prepareQ_st {s₁ s₂ t₁ t₂ : State} (h₁ : rsContract.pre s₁) (h₂ : rsContract.pre s₂)
    (eL : rlOf s₁ = rlOf s₂) (eq : qbOf (rlOf s₁) s₁.mem = qbOf (rlOf s₁) s₂.mem)
    (c₁ : Ctx (rlOf s₁) s₁ t₁) (c₂ : Ctx (rlOf s₂) s₂ t₂) : SameTrace isa prepareQ t₁ t₂ := by
  have hsp := (ctx_eq eL c₁ c₂).1
  have hr := (ctx_eq eL c₁ c₂).2
  have hq₁ := (rlOf_ok h₁).ql
  have hq₂ := (rlOf_ok h₂).ql
  unfold prepareQ prepare
  refine SameTrace.seq (st_taint [.r19, .r20, .r21] hsp (EqRegs.sub hr) (by taint_decide)) (qargs_ok c₁)
    (qargs_ok c₂) fun u₁ u₂ ⟨⟨a12, a6, m1⟩, k1⟩ ⟨⟨b12, b6, m2⟩, k2⟩ => ?_
  have usp : u₁.sp = u₂.sp := by rw [k1.sp, k2.sp, hsp]
  have e12 : u₁.gpr .r12 = u₂.gpr .r12 := by rw [a12, b12, eL]
  have e6 : u₁.gpr .r6 = u₂.gpr .r6 := by rw [a6, b6, eL]
  refine SameTrace.seq (st_taint [.r12, .r6] usp ⟨e12, e6⟩ (by taint_decide))
    (sigLen_ok a12 a6 (by omega) (by omega) fun i hi => by rw [k1.rd, k1.wr]; exact q_in h₁ c₁ i (by omega))
    (sigLen_ok b12 b6 (by omega) (by omega) fun i hi => by rw [k2.rd, k2.wr]; exact q_in h₂ c₂ i (by omega))
    fun v₁ v₂ ⟨⟨x16, n1⟩, kv1⟩ ⟨⟨y16, n2⟩, kv2⟩ => ?_
  rw [sig_eq h₁ c₁ m1] at x16
  rw [sig_eq h₂ c₂ m2, ← eL, ← eq] at y16
  exact st_taint [.r12, .r6, .r16] (by rw [kv1.sp, kv2.sp, usp])
    ⟨by rw [kv1.gpr _ (by decide), kv2.gpr _ (by decide), e12], by rw [kv1.gpr _ (by decide), kv2.gpr _ (by decide), e6],
      EqRegs.single (by rw [x16, y16])⟩ (by taint_decide)

/-! ## A call of `vg_dsa_sign` -/

/-- The state `vg_dsa_sign` is entered in, after `callArgs`. -/
theorem narrow_vals {s₀ w : State} (A : Args (rlOf s₀) s₀ w) (rd wr : List Region) :
    (w.callEntry.withRegions rd wr).sp = (rlOf s₀).F ∧
      (w.callEntry.withRegions rd wr).gpr .r3 = (rlOf s₀).out ∧
      (w.callEntry.withRegions rd wr).gpr .r4 = BitVec.ofNat 64 (2 * (rlOf s₀).ql) ∧
      (w.callEntry.withRegions rd wr).gpr .r5 = (rlOf s₀).key ∧
      (w.callEntry.withRegions rd wr).gpr .r6 = BitVec.ofNat 64 (rlOf s₀).kl ∧
      (w.callEntry.withRegions rd wr).gpr .r7 = BitVec.ofNat 64 (rlOf s₀).pl ∧
      (w.callEntry.withRegions rd wr).gpr .r8 = off (rlOf s₀).F oNonce ∧
      (w.callEntry.withRegions rd wr).gpr .r9 = BitVec.ofNat 64 (rlOf s₀).ql ∧
      (w.callEntry.withRegions rd wr).gpr .r10 = (rlOf s₀).dig ∧
      stackArg (w.callEntry.withRegions rd wr) 0 = BitVec.ofNat 64 (rlOf s₀).dl ∧
      stackArg (w.callEntry.withRegions rd wr) 1 = (rlOf s₀).scr ∧
      stackArg (w.callEntry.withRegions rd wr) 2 = BitVec.ofNat 64 (rlOf s₀).sl := by
  have hc := A.ctx
  refine ⟨hc.sp, (entry_gpr w rd wr (by decide)).trans A.r3, (entry_gpr w rd wr (by decide)).trans A.r4,
    (entry_gpr w rd wr (by decide)).trans A.r5, (entry_gpr w rd wr (by decide)).trans A.r6,
    (entry_gpr w rd wr (by decide)).trans A.r7, (entry_gpr w rd wr (by decide)).trans A.r8,
    (entry_gpr w rd wr (by decide)).trans A.r9, (entry_gpr w rd wr (by decide)).trans A.r10, ?_, ?_, ?_⟩
  · rw [entry_stackArg, hc.sp]; exact hc.a0
  · rw [entry_stackArg, hc.sp]; exact hc.a1
  · rw [entry_stackArg, hc.sp]; exact hc.a2

/-- What a call declassifies: the key's public octets and the call's success. -/
theorem leak_eq {s₀ w : State} (h : rsContract.pre s₀) (A : Args (rlOf s₀) s₀ w) :
    Spec.Dsa.publicBytesLeak ((w.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))).gpr .r7).toNat
        ((w.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))).gpr .r9).toNat
        (Spec.Rsa.bytesAt (w.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))).mem
          ((w.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))).gpr .r5)
          ((w.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))).gpr .r6).toNat) ++
      [Spec.Dsa.signStatus (sRes (w.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))))] =
    keyLeak s₀ ++ [Spec.Dsa.signStatus (sresOf (rlOf s₀) w.mem)] := by
  have hL := rlOf_ok h
  have hp := hL.pl
  have hq := hL.ql
  obtain ⟨-, -, -, g5, g6, g7, -, g9, -⟩ := narrow_vals A (signRd (rlOf s₀)) (signWr (rlOf s₀))
  rw [sres_eq h A, g5, g6, g7, g9, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := (rlOf s₀).pl) (by omega), Nat.mod_eq_of_lt (a := (rlOf s₀).ql) (by omega),
    Nat.mod_eq_of_lt (a := (rlOf s₀).kl) (by simp only [RL.kl]; omega)]
  show Spec.Dsa.publicBytesLeak _ _ (Spec.Rsa.bytesAt w.mem _ _) ++ _ = _
  rw [A.ctx.key]

theorem call_st {s₁ s₂ w₁ w₂ : State} (h₁ : rsContract.pre s₁) (h₂ : rsContract.pre s₂) (eL : rlOf s₁ = rlOf s₂)
    (ek : keyLeak s₁ = keyLeak s₂) (A₁ : Args (rlOf s₁) s₁ w₁) (A₂ : Args (rlOf s₂) s₂ w₂)
    (hs : Spec.Dsa.signStatus (sresOf (rlOf s₁) w₁.mem) = Spec.Dsa.signStatus (sresOf (rlOf s₂) w₂.mem)) :
    SameTrace isa (.call "vg_dsa_sign" Impl.Dsa.PPC64LE.Sign.sign) w₁ w₂ := by
  refine SameTrace.of_relCT (RelCT.callEx (k := sContract) sign_correct sign_ct
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

/-- After the call: the status, from the result's low word, and the attempts left. -/
theorem callFinish_st {v₁ v₂ : State} (hsp : v₁.sp = v₂.sp) (h26 : v₁.gpr .r26 = v₂.gpr .r26)
    (h3 : ((v₁.gpr .r3).setWidth 32 == 0) = ((v₂.gpr .r3).setWidth 32 == 0)) : SameTrace isa callFinish v₁ v₂ := by
  unfold callFinish
  exact SameTrace.ite (by rw [eval_zero_w, eval_zero_w, h3])
    (fun _ => by exact st_taint [.r26] hsp h26 (by taint_decide))
    (fun _ => by exact st_taint [] hsp trivial (by taint_decide))

/-! ## The attempts -/

/-- The sampler's data and q agree. -/
theorem same_q {s₁ s₂ : State} (eL : rlOf s₁ = rlOf s₂) (eq : qbOf (rlOf s₁) s₁.mem = qbOf (rlOf s₁) s₂.mem) :
    qOf s₂ = qOf s₁ ∧ eOf s₂ = eOf s₁ := by
  refine ⟨?_, ?_⟩
  · show Spec.Dsa.decodeBE (qbOf (rlOf s₂) s₂.mem) = Spec.Dsa.decodeBE (qbOf (rlOf s₁) s₁.mem)
    rw [← eL, ← eq]
  · show seOf (rlOf s₂) (qbOf (rlOf s₂) s₂.mem) = seOf (rlOf s₁) (qbOf (rlOf s₁) s₁.mem)
    rw [← eL, ← eq]

/-- `Ctx` after code that writes only `r3`. -/
theorem ctx_r3_step {s₀ t t' : State} (h : rsContract.pre s₀) (hc : Ctx (rlOf s₀) s₀ t) (k : Keep [.r3] t t')
    (hm : t'.mem = t.mem) : Ctx (rlOf s₀) s₀ t' :=
  hc.step (rlOf_ok h) k.sp k.rd k.wr (fun r hr => k.gpr r (ctx_r3 r hr)) (by rw [hm]; exact Frame.refl _ _)

/-- The signature a call computes, from an accepted draw `k` in the nonce. -/
theorem sres_draw {s₀ t w : State} (hc : Ctx (rlOf s₀) s₀ t) (hw : w.mem = t.mem)
    {k : Nat} (hn : Spec.Rsa.bytesAt t.mem (off (rlOf s₀).F oNonce) (rlOf s₀).ql = Spec.Dsa.encodeBE (rlOf s₀).ql k) :
    sresOf (rlOf s₀) w.mem = Spec.Dsa.signBytes (inpOf (rlOf s₀) s₀.mem).pLen (inpOf (rlOf s₀) s₀.mem).qLen
      (inpOf (rlOf s₀) s₀.mem).key (Spec.Dsa.encodeBE (inpOf (rlOf s₀) s₀.mem).qLen k)
      (inpOf (rlOf s₀) s₀.mem).digest := by
  simp only [sresOf, inpOf]
  rw [hw, hc.key, hc.dig, hn]

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
  have xsp : x₁.sp = x₂.sp := by rw [A₁.sc.ctx.sp, A₂.sc.ctx.sp, eL]
  unfold attempt
  refine SameTrace.seq (sample_st hE₁ hQ₁ env₁ env₂' A₁.r25 A₂.r25 A₁.hu tS) (sample_ok hE₁ hQ₁ env₁ A₁.r25 A₁.hu)
    (sample_ok hE₂ hQ₂ env₂ A₂.r25 A₂.hu) fun y₁ y₂ so₁ so₂ => ?_
  rw [dq₁] at so₁
  rw [dq₂] at so₂
  obtain ⟨sc₁, nz₁⟩ := sampled h₁ A₁.sc A₁.zero so₁ hq
  obtain ⟨sc₂, nz₂⟩ := sampled h₂ A₂.sc A₂.zero so₂ hq₂
  have ysp : y₁.sp = y₂.sp := by rw [sc₁.ctx.sp, sc₂.ctx.sp, eL]
  have W : ∀ {y : State}, WP isa (.block [.subi .r3 .r31 1]) y fun z =>
      (z.mem = y.mem ∧ z.gpr .r3 = y.gpr .r31 - BitVec.ofNat 64 1) ∧ Keep [.r3] y z :=
    fun {_} => WP.keep [.r3] (by prun) (by decide)
  refine SameTrace.seq (st_taint [] ysp trivial (by taint_decide)) W W fun z₁ z₂ ⟨⟨m1, a3⟩, k1⟩ ⟨⟨m2, b3⟩, k2⟩ => ?_
  have zsp : z₁.sp = z₂.sp := by rw [k1.sp, k2.sp, ysp]
  have hst₁ := sampleStatus_le (randomSignDraw (inpOf (rlOf s₁) s₁.mem) u)
  have hst₂ := sampleStatus_le (randomSignDraw (inpOf (rlOf s₂) s₂.mem) u)
  have ev₁ : isa.eval (.zero .d .r3) z₁ =
      some (decide (sampleStatus (randomSignDraw (inpOf (rlOf s₁) s₁.mem) u) = 1)) := by
    rw [VG.PPC64LE.eval_zero, a3, so₁.r31, sub1_beq _ (by omega)]
  have ev₂ : isa.eval (.zero .d .r3) z₂ =
      some (decide (sampleStatus (randomSignDraw (inpOf (rlOf s₂) s₂.mem) u) = 1)) := by
    rw [VG.PPC64LE.eval_zero, b3, so₂.r31, sub1_beq _ (by omega)]
  refine SameTrace.ite (by rw [ev₁, ev₂, eSt]) (fun hc => ?_) (fun _ => by exact st_taint [] zsp trivial (by taint_decide))
  rw [ev₁, Option.some.injEq, decide_eq_true_eq] at hc
  obtain ⟨k₁, hk₁⟩ := Option.isSome_iff_exists.mp (sampleStatus_some.mp hc)
  obtain ⟨k₂, hk₂⟩ := Option.isSome_iff_exists.mp (sampleStatus_some.mp (eSt ▸ hc))
  have cz₁ := ctx_r3_step h₁ sc₁.ctx k1 m1
  have cz₂ := ctx_r3_step h₂ sc₂.ctx k2 m2
  have nn₁ : Spec.Rsa.bytesAt z₁.mem (off (rlOf s₁).F oNonce) (rlOf s₁).ql = Spec.Dsa.encodeBE (rlOf s₁).ql k₁ := by
    rw [m1]; exact nonce_eq (W := (eOf s₁).W) hE₁.Wq nz₁ (so₁.cand k₁ hk₁)
  have nn₂ : Spec.Rsa.bytesAt z₂.mem (off (rlOf s₂).F oNonce) (rlOf s₂).ql = Spec.Dsa.encodeBE (rlOf s₂).ql k₂ := by
    rw [m2]; exact nonce_eq (W := (eOf s₂).W) hE₂.Wq nz₂ (so₂.cand k₂ hk₂)
  have hr := (ctx_eq eL cz₁ cz₂).2
  refine SameTrace.seq (st_taint [.r18, .r19, .r20, .r21, .r22] zsp (EqRegs.sub hr) (by taint_decide))
    (callArgs_ok hL₁ cz₁) (callArgs_ok hL₂ cz₂) fun w₁ w₂ ⟨A₁', mw₁, kw₁⟩ ⟨A₂', mw₂, kw₂⟩ => ?_
  have hsi := VG.Proof.Dsa.random_sign_trace_call ht hk₁ hk₂
  have hs : Spec.Dsa.signStatus (sresOf (rlOf s₁) w₁.mem) = Spec.Dsa.signStatus (sresOf (rlOf s₂) w₂.mem) := by
    rw [sres_draw cz₁ mw₁ nn₁, sres_draw cz₂ mw₂ nn₂]
    simp only [Spec.Dsa.signStatus, hsi]
  have w26 : ∀ {s₀ x y z w : State} {S : Spec.Dsa.Random.Sample}, AttInv s₀ (a' + 1) u x →
      SampleOut (eOf s₀) (randOf (rlOf s₀) s₀.mem) u S x y → Keep [.r3] y z → Keep argRegs' z w →
      w.gpr .r26 = BitVec.ofNat 64 (a' + 1) := fun A so k kw =>
    (kw.gpr _ (by decide)).trans ((k.gpr _ (by decide)).trans ((so.keep.gpr _ (by decide)).trans A.r26))
  refine SameTrace.seq (call_st h₁ h₂ eL ek A₁' A₂' hs) (sign_ok h₁ A₁') (sign_ok h₂ A₂') fun v₁ v₂ S₁ S₂ => ?_
  refine callFinish_st (by rw [S₁.ctx.sp, S₂.ctx.sp, eL])
    (by rw [S₁.pres _ (by decide), S₂.pres _ (by decide), w26 A₁ so₁ k1 kw₁, w26 A₂ so₂ k2 kw₂]) ?_
  rw [setWidth_beq_zero S₁.r3, setWidth_beq_zero S₂.r3, hs]

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

theorem beq_of_iff {x : BitVec 64} {P : Prop} [Decidable P] (h : x = 0 ↔ P) : (x == 0) = decide P := by
  by_cases hp : P
  · simp [h.mpr hp, hp]
  · rw [decide_eq_false hp]
    exact beq_eq_false_iff_ne.mpr fun e => hp (h.mp e)

/-- The attempts' first state. -/
theorem att_init {s₀ t₁ t₂ : State} (h : rsContract.pre s₀) (hq : 1 < qOf s₀) (he : Entered (rlOf s₀) s₀ t₁)
    (sc : Scanned (rlOf s₀) s₀ t₂) (m2 : t₂.mem = t₁.mem)
    (k2 : Keep (([.r6, .r12] : List Reg) ++ prepRegs) t₁ t₂) :
    AttInv s₀ 8 0 t₂ := by
  have hL := rlOf_ok h
  refine ⟨sc, (k2.gpr _ (by decide)).trans he.r25, by omega, (k2.gpr _ (by decide)).trans he.r26, by decide,
    by decide, fun j hj => ?_, VG.Proof.Dsa.RandomSignResultRel.refl _ _ _⟩
  rw [m2]
  have hE : (eOf s₀).Ok := seOf_ok hL s₀.mem hq
  have := hE.Wq
  have := hL.ql
  have e2 : (eOf s₀).ql = (rlOf s₀).ql := rfl
  exact he.nonce j (by omega)

theorem randomSign_ct : ConstantTime isa rsContract.pre rsContract.pub Impl.Dsa.PPC64LE.RandomSign.code := by
  refine SameTrace.constantTime fun s₁ s₂ h₁ h₂ hp => ?_
  obtain ⟨eL, ek, est, etr⟩ := pub_facts h₁ h₂ hp
  have eq := qb_eq h₁ eL ek
  obtain ⟨eQ, -⟩ := same_q eL eq
  obtain ⟨hsp, e3, -, e5, e6, -, e8, e9, e10, -⟩ := hp
  unfold Impl.Dsa.PPC64LE.RandomSign.code
  refine st_alloc hsp ?_
  unfold Impl.Dsa.PPC64LE.RandomSign.body
  refine SameTrace.seq (st_taint [.r3, .r5, .r6, .r8, .r9, .r10] (by simp only [allocated, hsp])
    ⟨e3, e5, e6, e8, e9, e10⟩ (by taint_decide)) (entry_ok h₁) (entry_ok h₂) fun t₁ t₂ E₁ E₂ => ?_
  refine SameTrace.seq (prepareQ_st h₁ h₂ eL eq E₁.ctx E₂.ctx) (prepareQ_ok h₁ E₁.ctx) (prepareQ_ok h₂ E₂.ctx)
    fun u₁ u₂ ⟨sc₁, z₁, m₁, k₁⟩ ⟨sc₂, z₂, m₂, k₂⟩ => ?_
  have usp := (ctx_eq eL sc₁.ctx sc₂.ctx).1
  have hr := (ctx_eq eL sc₁.ctx sc₂.ctx).2
  have z₂' : u₂.gpr .r0 = 0 ↔ ¬ 1 < qOf s₁ := by rw [← eQ]; exact z₂
  refine SameTrace.seq_ite (by rw [VG.PPC64LE.eval_zero, VG.PPC64LE.eval_zero, beq_of_iff z₁, beq_of_iff z₂'])
    (fun _ => by exact st_taint [.r18, .r21, .r30] usp (EqRegs.sub hr) (by taint_decide)) (fun hc => ?_)
  rw [VG.PPC64LE.eval_zero, beq_of_iff z₁, Option.some.injEq, decide_eq_false_iff_not, Decidable.not_not] at hc
  have hq₂ : 1 < qOf s₂ := eQ ▸ hc
  have i₁ := att_init h₁ hc E₁ sc₁ m₁ k₁
  have i₂ := att_init h₂ hq₂ E₂ sc₂ m₂ k₂
  refine SameTrace.seq (attempts_st h₁ h₂ eL ek hc ⟨0, i₁, i₂, etr⟩) (attempts_ok h₁ hc 8 0 u₁ i₁)
    (attempts_ok h₂ hq₂ 8 0 u₂ i₂) fun x₁ x₂ o₁ o₂ => ?_
  have xr := (ctx_eq eL o₁.sc.ctx o₂.sc.ctx).2
  exact st_taint [.r18, .r21, .r30, .r31] (ctx_eq eL o₁.sc.ctx o₂.sc.ctx).1
    ⟨xr.mem _ (by decide), xr.mem _ (by decide), xr.mem _ (by decide), EqRegs.single (by rw [o₁.r31, o₂.r31, est])⟩
    (by taint_decide)

end VG.Proof.Dsa.PPC64LE.RS
