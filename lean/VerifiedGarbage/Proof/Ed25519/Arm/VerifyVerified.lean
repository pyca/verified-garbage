import VerifiedGarbage.Impl.Ed25519.Arm.PointTableIO
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseVerified
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarMulAddVerified
import VerifiedGarbage.Impl.Ed25519.Arm.Verify
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTRhs`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.VerifyHeaders`. -/
section

/-! Merged from `Proof.Ed25519.Arm.VerifyContext`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyFrame`. -/
section
/-! Merged from `Proof.Ed25519.Arm.PointTableIO`. -/
section
/-! Save and reload the verification equation's packed points. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scratchAddr_ok {b : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (o : Nat) (ho : o < 8192) :
    WP isa (.block (scratchAddr o)) s fun t => Rest [.r12] s t ∧ t.mem = s.mem ∧
      t.gpr .r12 = b + BitVec.ofNat 32 o := by
  refine wp_movw fun u hu => wp_dp (op2_reg _ _) fun t ht => WP.block_nil ?_
  refine ⟨(hu.rest (by decide)).trans (ht.rest (by decide)), by rw [ht.mem, hu.mem], ?_⟩
  rw [ht.gpr]
  change u.gpr .r0 + u.gpr .r12 = _
  rw [hu.other _ (by decide), hc.r0, hu.gpr]
  refine congrArg (b + ·) (BitVec.eq_of_toNat_eq ?_)
  rw [movw_nat (by omega), toNat_imm (by omega)]

theorem pointTableWrite_ok {b : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hl : AllLim s.mem b)
    (o : Nat) (ho : 1600 ≤ o) (hn : o + 128 ≤ 8192) :
    WP isa (.block (pointTableWrite o)) s fun t => PowersKeep b o 128 s t ∧ AllLim t.mem b ∧
      env t.mem b = env s.mem b ∧ tablePoint t.mem b o = point (env s.mem b) 0 1 2 3 := by
  unfold pointTableWrite
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.Arm.scratchAddr_ok hc o (by omega)) fun u ⟨ur, um, up⟩ => ?_
  refine WP.mono (pointToTable_ok (hc.of_rest ur (by decide)) (um ▸ hl) up ho hn) fun t ⟨tp, tk⟩ => ?_
  exact ⟨⟨(ur.mono (by decide)).trans (tk.rest.mono (by decide)), by rw [← um]; exact TableFrame.table tk.frame⟩,
    tk.lim ho hn (um ▸ hl), (tk.env ho hn).trans (congrArg (fun m => env m b) um),
    tp.trans (congrArg (fun m => point (env m b) 0 1 2 3) um)⟩

theorem pointTableRead_ok {b : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hl : AllLim s.mem b)
    (o : Nat) (ho : 1600 ≤ o) (hn : o + 128 ≤ 8192) :
    WP isa (.block (pointTableRead o)) s fun t => AccKeep b s t ∧ AllLim t.mem b ∧
      point (env t.mem b) 0 1 2 3 = tablePoint s.mem b o ∧
      ∀ i : Slot, 4 ≤ i.val → env t.mem b i = env s.mem b i := by
  unfold pointTableRead
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.Arm.scratchAddr_ok hc o (by omega)) fun u ⟨ur, um, up⟩ => ?_
  refine WP.mono (pointFromTable_ok (hc.of_rest ur (by decide)) (um ▸ hl) up ho hn) fun t ⟨tp, tl, tk⟩ => ?_
  refine ⟨(AccKeep.of_rest ur (by decide) um).trans (AccKeep.of_table tk (by decide) (by decide)), tl,
    tp.trans (congrArg (fun m => tablePoint m b o) um), fun i hi => ?_⟩
  exact (tk.high i hi).trans (congrArg (fun m => env m b i) um)

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarCompare`. -/
section
/-! A canonical-scalar check for the public verification inputs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scalarCompare_ok {b : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s)
    (hl : Lim s.mem (State.addr b) SR) :
    WP isa (.block scalarCompare) s fun t =>
      Rest [.r2, .r3, .r4, .r5, .r6] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 SD, 64⟩] s.mem t.mem ∧
      (t.gpr .r5).toNat = if V s.mem (State.addr b) SR < Spec.Ed25519.L then 0 else 1 := by
  unfold scalarCompare
  simp only [List.cons_append, List.nil_append]
  refine wp_movw fun u hu => wp_mov (op2_imm (by decide)) fun v hv => ?_
  have kv : Rest [.r5, .r6] s v := (hu.rest (by decide)).trans (hv.rest (by decide))
  have mv : v.mem = s.mem := by rw [hv.mem, hu.mem]
  have hcv := hc.of_rest kv (by decide)
  refine WP.mono (scalarSubtractPass_ok hcv (mv ▸ hl) (by rw [hv.gpr]; rfl)
    (by rw [hv.other _ (by decide), hu.gpr])) fun t ht => ?_
  refine ⟨(kv.mono (by decide)).trans (ht.rest.mono (by decide)), ?_, ?_⟩
  · have hf := ht.frame; rwa [hcv.r0, mv] at hf
  · rw [ht.r5, mv, scalarCompare_carry (V_lt hl)]
    rfl

end VG.Proof.Ed25519.Arm
end

/-! Verification preserves the ABI saves and all public input headers. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

abbrev verifyRegion (b : BitVec 32) : Region := ⟨State.addr b + BitVec.ofNat 64 32, 8096⟩
structure VerifyKeep (b : BitVec 32) (s t : State) : Prop where
  rest : Rest powersClob s t
  frame : Frame [VG.Proof.Ed25519.Arm.verifyRegion b] s.mem t.mem

theorem VerifyKeep.refl (b : BitVec 32) (s : State) : VG.Proof.Ed25519.Arm.VerifyKeep b s s := ⟨Rest.refl _ _, Frame.refl _ _⟩
theorem VerifyKeep.ctx {b : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.Arm.VerifyKeep b s t) (hc : VG.Proof.Ed25519.Arm.Ctx b s) : VG.Proof.Ed25519.Arm.Ctx b t :=
  hc.of_rest h.rest (by decide)
theorem VerifyKeep.trans {b : BitVec 32} {s t u : State} (h : VG.Proof.Ed25519.Arm.VerifyKeep b s t) (k : VG.Proof.Ed25519.Arm.VerifyKeep b t u) :
    VG.Proof.Ed25519.Arm.VerifyKeep b s u := ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩
theorem VerifyKeep.of_small {b : BitVec 32} {s t : State} {o n : Nat} {ws : List Reg}
    (hr : Rest ws s t) (hw : ∀ r ∈ ws, r ∈ powersClob)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, n⟩] s.mem t.mem) (ho : 32 ≤ o) (hn : o + n ≤ 8128) :
    VG.Proof.Ed25519.Arm.VerifyKeep b s t := ⟨hr.mono hw, hf.sub fun r hm => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hm]; exact Offset.sub _ ho hn⟩⟩
theorem VerifyKeep.of_point {b : BitVec 32} {s t : State} (h : PointKeep b s t) : VG.Proof.Ed25519.Arm.VerifyKeep b s t := by
  refine ⟨h.rest, h.frame.sub fun r hr => ?_⟩
  simp only [pointRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
theorem VerifyKeep.of_powers {b : BitVec 32} {o n : Nat} {s t : State}
    (h : PowersKeep b o n s t) (ho : 32 ≤ o) (hn : o + n ≤ 8128) : VG.Proof.Ed25519.Arm.VerifyKeep b s t := by
  refine ⟨h.rest, h.frame.sub fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨_, List.mem_singleton_self _, Offset.sub _ ho hn⟩
theorem VerifyKeep.of_keep {b : BitVec 32} {s t : State} (h : Keep b s t) : VG.Proof.Ed25519.Arm.VerifyKeep b s t :=
  VerifyKeep.of_point (PointKeep.of_keep h)
theorem VerifyKeep.of_acc {b : BitVec 32} {s t : State} (h : AccKeep b s t) : VG.Proof.Ed25519.Arm.VerifyKeep b s t :=
  VerifyKeep.of_powers (PowersKeep.of_acc h) (o := 1600) (n := 0) (by decide) (by decide)
theorem VerifyKeep.of_decode {b : BitVec 32} {s t : State} (h : DecodeKeep b s t) : VG.Proof.Ed25519.Arm.VerifyKeep b s t := by
  refine ⟨h.rest.mono (by decide), h.frame.sub fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
theorem VerifyKeep.of_rest {b : BitVec 32} {s t : State} {ws : List Reg}
    (hr : Rest ws s t) (hw : ∀ r ∈ ws, r ∈ powersClob) (hm : t.mem = s.mem) : VG.Proof.Ed25519.Arm.VerifyKeep b s t :=
  ⟨hr.mono hw, by rw [hm]; exact Frame.refl _ _⟩

theorem VerifyKeep.header {b : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.Arm.VerifyKeep b s t)
    (d : Nat) (hd : 8128 ≤ d) (hn : d + 4 ≤ 8192) :
    t.mem.readW (State.addr b + BitVec.ofNat 64 d) 32 = s.mem.readW (State.addr b + BitVec.ofNat 64 d) 32 := by
  apply BitVec.eq_of_toNat_eq
  exact wd_frame h.frame fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inr (by omega)) (by omega) (by decide)

end VG.Proof.Ed25519.Arm
end

/-! Readable public inputs remain outside all verification writes. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

structure VerifyInput (b ptr : BitVec 32) (len : Nat) (s : State) : Prop where
  fit : ptr.toNat + len ≤ 2 ^ 32
  readable : ∀ i < len, InRegions (s.rd ++ s.wr) (State.addr ptr + BitVec.ofNat 64 i) 1
  separate : (⟨State.addr ptr, len⟩ : Region).Disjoint ⟨State.addr b, 8192⟩

theorem VerifyInput.keep {b ptr : BitVec 32} {len : Nat} {s t : State}
    (h : VG.Proof.Ed25519.Arm.VerifyInput b ptr len s) (hk : VG.Proof.Ed25519.Arm.VerifyKeep b s t) : VG.Proof.Ed25519.Arm.VerifyInput b ptr len t :=
  ⟨h.fit, fun i hi => by rw [hk.rest.rd, hk.rest.wr]; exact h.readable i hi, h.separate⟩

theorem VerifyInput.bytes {b ptr : BitVec 32} {len : Nat} {s t : State}
    (h : VG.Proof.Ed25519.Arm.VerifyInput b ptr len s) (hk : VG.Proof.Ed25519.Arm.VerifyKeep b s t) :
    Spec.Ed25519.bytesAt t.mem (State.addr ptr) len = Spec.Ed25519.bytesAt s.mem (State.addr ptr) len := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => hk.frame.bytes (R := ⟨State.addr ptr, len⟩)
    (fun r hr => ?_) (by have := h.fit; omega : len ≤ 2 ^ 64) (List.mem_range.mp hi)
  rw [List.mem_singleton.mp hr]
  exact h.separate.sub_right (Offset.sub_base _ (by decide))

theorem VerifyInput.prefix {b ptr : BitVec 32} {len n : Nat} {s : State}
    (h : VG.Proof.Ed25519.Arm.VerifyInput b ptr len s) (hn : n ≤ len) : VG.Proof.Ed25519.Arm.VerifyInput b ptr n s :=
  ⟨by have := h.fit; omega, fun i hi => h.readable i (by omega), h.separate.sub_left (Region.sub_prefix hn)⟩

theorem VerifyInput.suffix32 {b ptr : BitVec 32} {s : State} (h : VG.Proof.Ed25519.Arm.VerifyInput b ptr 64 s) :
    VG.Proof.Ed25519.Arm.VerifyInput b (ptr + 32) 32 s := by
  have en : (ptr + (32 : BitVec 32)).toNat = ptr.toNat + 32 := by
    rw [toNat_add_lt (by have := h.fit; change ptr.toNat + 32 < 2 ^ 32; omega)]
    rfl
  have ep : State.addr (ptr + (32 : BitVec 32)) = State.addr ptr + BitVec.ofNat 64 32 := addr_add (k := 32) (by have := h.fit; omega)
  refine ⟨by rw [en]; have := h.fit; omega, ?_, ?_⟩
  · intro i hi
    rw [ep, Offset.add_add]
    exact h.readable (32 + i) (by omega)
  · rw [ep]
    exact h.separate.sub_left (Offset.sub_base _ (by decide))

structure VerifyContext (b pk sig challenge : BitVec 32) (s : State) : Prop where
  ctx : VG.Proof.Ed25519.Arm.Ctx b s
  pkInput : VG.Proof.Ed25519.Arm.VerifyInput b pk 32 s
  sigInput : VG.Proof.Ed25519.Arm.VerifyInput b sig 64 s
  challengeInput : VG.Proof.Ed25519.Arm.VerifyInput b challenge 64 s
  pkHeader : s.mem.readW (State.addr b + BitVec.ofNat 64 8128) 32 = pk
  sigHeader : s.mem.readW (State.addr b + BitVec.ofNat 64 8132) 32 = sig
  challengeHeader : s.mem.readW (State.addr b + BitVec.ofNat 64 8136) 32 = challenge

theorem VerifyContext.keep {b pk sig challenge : BitVec 32} {s t : State}
    (h : VG.Proof.Ed25519.Arm.VerifyContext b pk sig challenge s) (hk : VG.Proof.Ed25519.Arm.VerifyKeep b s t) : VG.Proof.Ed25519.Arm.VerifyContext b pk sig challenge t :=
  ⟨hk.ctx h.ctx, h.pkInput.keep hk, h.sigInput.keep hk, h.challengeInput.keep hk,
    (hk.header _ (by decide) (by decide)).trans h.pkHeader,
    (hk.header _ (by decide) (by decide)).trans h.sigHeader,
    (hk.header _ (by decide) (by decide)).trans h.challengeHeader⟩

end VG.Proof.Ed25519.Arm
end

/-! Load a public argument pointer from the protected header area. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem loadHeader_ok {b : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (d : Nat) (hd : d + 4 ≤ 8192) :
    WP isa (.block (loadHeader d)) s fun t => Rest [.r12] s t ∧ t.mem = s.mem ∧
      t.gpr .r12 = s.mem.readW (State.addr b + BitVec.ofNat 64 d) 32 := by
  unfold loadHeader
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.Arm.scratchAddr_ok hc d (by omega)) fun u ⟨ur, um, up⟩ => ?_
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 d) (by decide)
    (by rw [up]; exact (congrArg State.addr (BitVec.add_zero _)).trans (hc.ptr_addr (by omega)))
    (by rw [ur.rd, ur.wr]; exact in_base (List.mem_append_right _ hc.wr) hd (by omega))
    fun t ht => WP.block_nil ⟨ur.trans (ht.rest (by decide)), ht.mem.trans um, ?_⟩
  rw [ht.gpr, um]

theorem addInput32_ok (s : State) :
    WP isa (.block [.dp .add .r12 .r12 (.imm 32)]) s fun t => Rest [.r12] s t ∧ t.mem = s.mem ∧
      t.gpr .r12 = s.gpr .r12 + 32 := by
  refine wp_dp (op2_imm (by decide)) fun t ht => WP.block_nil ⟨ht.rest (by decide), ht.mem, ht.gpr⟩

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.DecodedThen`. -/
section

/-! Branch only on the public point-decoding result. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem decodedThen_ok {s : State} {next : Prog isa} {P : State → Prop} (flag : Bool)
    (hv : s.gpr .r9 = BitVec.ofNat 32 flag.toNat)
    (hy : flag = true → ∀ u, Rest [] s u → u.mem = s.mem → WP isa next u P)
    (hn : flag = false → ∀ u, Rest [] s u → u.mem = s.mem → WP isa recoverInvalid u P) :
    WP isa (decodedThen next) s P := by
  refine WP.seq (wp_cmp (op2_imm (by decide)) fun u hu hz => WP.block_nil ?_)
  have he : VG.Arm.eval .ne u = some flag := by
    rw [VG.Arm.eval, hz, hv]
    cases flag <;> rfl
  apply WP.ite flag he
  · intro h; exact hy h u (hu.rest []) hu.mem
  · intro h; exact hn h u (hu.rest []) hu.mem

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTPublic`. -/
section

/-! Merged from `Proof.Ed25519.Arm.VerifyBody`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyDecodeR`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyPoints`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyRhs`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyCombine`. -/
section
/-! Combine R + [k]A and load [S]B for the final point comparison. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifyCombine_ok {b : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hl : AllLim s.mem b)
    (hd : env s.mem b 16 = Spec.Ed25519.d) :
    WP isa verifyCombine s fun t => AccKeep b s t ∧ AllLim t.mem b ∧
      point (env t.mem b) 0 1 2 3 = tablePoint s.mem b 8000 ∧
      point (env t.mem b) 4 5 6 7 = Spec.Ed25519.pointAdd (tablePoint s.mem b 7872)
        (point (env s.mem b) 0 1 2 3) := by
  refine WP.seq (WP.mono (fieldCode_ok copyPointToQOps hc hl) fun a ⟨ak, al, ae⟩ => ?_)
  have aq := (congrArg (fun e => point e 4 5 6 7) ae).trans (copyPointToQ_eval _)
  have ad : env a.mem b 16 = Spec.Ed25519.d := by rw [ae, copyPointToQ_d, hd]
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.pointTableRead_ok (ak.ctx hc) al 7872 (by decide) (by decide))
    fun c ⟨ck, cl, cp, ch⟩ => ?_)
  have kc := (AccKeep.of_keep ak).trans ck
  have cq : point (env c.mem b) 4 5 6 7 = point (env s.mem b) 0 1 2 3 :=
    (point_congr _ _ _ _ (ch 4 (by decide)) (ch 5 (by decide)) (ch 6 (by decide)) (ch 7 (by decide))).trans aq
  have cp' := cp.trans (workspace_tablePoint ak.frame (by decide) (by decide))
  refine WP.seq (WP.mono (pointAdd_ok (kc.ctx hc) cl ((ch 16 (by decide)).trans ad))
    fun d ⟨dk, dl, dp, _⟩ => ?_)
  have kd := kc.trans (AccKeep.of_keep dk)
  have dp' := dp.trans (congrArg₂ Spec.Ed25519.pointAdd cp' cq)
  refine WP.seq (WP.mono (fieldCode_ok copyPointToQOps (kd.ctx hc) dl) fun e ⟨ek, el, ee⟩ => ?_)
  have ke := kd.trans (AccKeep.of_keep ek)
  have eqp := ((congrArg (fun f => point f 4 5 6 7) ee).trans (copyPointToQ_eval _)).trans dp'
  refine WP.mono (VG.Proof.Ed25519.Arm.pointTableRead_ok (ke.ctx hc) el 8000 (by decide) (by decide))
    fun t ⟨tk, tl, tp, th⟩ => ?_
  exact ⟨ke.trans tk, tl, tp.trans (workspace_tablePoint ke.frame (by decide) (by decide)),
    (point_congr _ _ _ _ (th 4 (by decide)) (th 5 (by decide)) (th 6 (by decide)) (th 7 (by decide))).trans eqp⟩

end VG.Proof.Ed25519.Arm
end

/-! The right side reads all 512 challenge bits before the strict equation. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifyRhs_ok {b pk sig challenge : BitVec 32} {s : State}
    (hc : VG.Proof.Ed25519.Arm.VerifyContext b pk sig challenge s) (hl : AllLim s.mem b) :
    WP isa verifyRhs s fun t => VG.Proof.Ed25519.Arm.VerifyKeep b s t ∧ AllLim t.mem b ∧
      t.gpr .r9 = BitVec.ofNat 32 (Spec.Ed25519.pointEqual (tablePoint s.mem b 8000)
        (Spec.Ed25519.pointAdd (tablePoint s.mem b 7872)
          (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr challenge) 64))
            (tablePoint s.mem b 7744)))).toNat := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.Arm.pointTableRead_ok hc.ctx hl 7744 (by decide) (by decide)) fun a ⟨ak, al, ap, _⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.Arm.loadHeader_ok (ak.ctx hc.ctx) 8136 (by decide)) fun c ⟨cr, cm, cp⟩ => ?_
  have kc := ak.trans (AccKeep.of_rest cr (by decide) cm)
  have cpk : PointKeep b s c := PointKeep.of_mul (MulKeep.of_powers (PowersKeep.of_acc kc))
  have cc := hc.keep (VerifyKeep.of_acc kc)
  have cp' : c.gpr .r12 = challenge := cp.trans (hc.keep (VerifyKeep.of_acc ak)).challengeHeader
  have capp : point (env c.mem b) 0 1 2 3 = tablePoint s.mem b 7744 :=
    (congrArg (fun m => point (env m b) 0 1 2 3) cm).trans ap
  refine WP.seq (WP.mono (pointFromScalar_ok cc.ctx (cm ▸ al) cp' 32 (by decide) (by decide)
    cc.challengeInput.fit cc.challengeInput.readable cc.challengeInput.separate) fun d ⟨dk, dl, dd, dp⟩ => ?_)
  have kd := cpk.trans dk
  have dp' : point (env d.mem b) 0 1 2 3 = Spec.Ed25519.pointMul
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr challenge) 64)) (tablePoint s.mem b 7744) := by
    rw [hc.challengeInput.bytes (VerifyKeep.of_acc kc), capp] at dp
    exact dp
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.verifyCombine_ok (kd.ctx hc.ctx) dl dd) fun e ⟨ek, el, ep, eqp⟩ => ?_)
  have ep' := ep.trans (kd.table (by decide) (by decide))
  have eqp' := eqp.trans (congrArg₂ Spec.Ed25519.pointAdd (kd.table (by decide) (by decide)) dp')
  refine WP.mono (pointEqual_ok (ek.ctx (kd.ctx hc.ctx)) el) fun t ⟨tk, tl, tv⟩ => ?_
  refine ⟨((VerifyKeep.of_point kd).trans (VerifyKeep.of_acc ek)).trans (VerifyKeep.of_keep tk), tl, ?_⟩
  exact tv.trans (congrArg (fun v : Bool => BitVec.ofNat 32 v.toNat)
    (congrArg₂ Spec.Ed25519.pointEqual ep' eqp'))

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.VerifyLhs`. -/
section
/-! The left side of the equation is [S]B, retaining A and R. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifyLhs_ok {b pk sig challenge : BitVec 32} {s : State}
    (hc : VG.Proof.Ed25519.Arm.VerifyContext b pk sig challenge s) (hl : AllLim s.mem b) :
    WP isa verifyLhs s fun t => VG.Proof.Ed25519.Arm.VerifyKeep b s t ∧ AllLim t.mem b ∧
      tablePoint t.mem b 8000 = Spec.Ed25519.pointMul
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr (sig + 32)) 32)) Spec.Ed25519.basePoint ∧
      tablePoint t.mem b 7744 = tablePoint s.mem b 7744 ∧
      tablePoint t.mem b 7872 = tablePoint s.mem b 7872 := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.Arm.loadHeader_ok hc.ctx 8132 (by decide)) fun a ⟨ar, am, ap⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.Arm.addInput32_ok a) fun c ⟨cr, cm, cp⟩ => ?_
  have kc : PointKeep b s c := ⟨(ar.mono (by decide)).trans (cr.mono (by decide)), by
    rw [cm, am]; exact Frame.refl _ _⟩
  refine WP.seq (WP.mono (fieldCode_ok (constPointOps Spec.Ed25519.basePoint) (kc.ctx hc.ctx)
    (by rw [cm, am]; exact hl)) fun d ⟨dk, dl, de⟩ => ?_)
  have kd := kc.trans (PointKeep.of_keep dk)
  have dc := hc.keep (VerifyKeep.of_point kd)
  have di := dc.sigInput.suffix32
  have dp : d.gpr .r12 = sig + 32 := by rw [dk.rest.gpr _ (by decide), cp, ap, hc.sigHeader]
  have dpoint : point (env d.mem b) 0 1 2 3 = Spec.Ed25519.basePoint :=
    (congrArg (fun e => point e 0 1 2 3) de).trans (constPoint_eval _ _)
  refine WP.seq (WP.mono (pointFromScalar_ok dc.ctx dl dp 16 (by decide) (by decide)
    di.fit di.readable di.separate) fun e ⟨ek, el, _, ep⟩ => ?_)
  have ke := kd.trans ek
  have ep' : point (env e.mem b) 0 1 2 3 = Spec.Ed25519.pointMul
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr (sig + 32)) 32)) Spec.Ed25519.basePoint := by
    rw [(hc.sigInput.suffix32).bytes (VerifyKeep.of_point kd), dpoint] at ep
    exact ep
  refine WP.mono (VG.Proof.Ed25519.Arm.pointTableWrite_ok (ke.ctx hc.ctx) el 8000 (by decide) (by decide))
    fun t ⟨tk, tl, _, tp⟩ => ?_
  refine ⟨(VerifyKeep.of_point ke).trans (VerifyKeep.of_powers tk (by decide) (by decide)), tl,
    tp.trans ep', ?_, ?_⟩
  · exact (tk.frame.point (by decide) (.inl (by decide)) (by decide) (by decide)).trans
      (ke.table (by decide) (by decide))
  · exact (tk.frame.point (by decide) (.inl (by decide)) (by decide) (by decide)).trans
      (ke.table (by decide) (by decide))

end VG.Proof.Ed25519.Arm
end

/-! Compose both sides of the exact, uncofactored verification equation. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def equationResult (m : Mem) (sig challenge : BitVec 32) (a r : Spec.Ed25519.Point) : Bool :=
  Spec.Ed25519.pointEqual
    (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr (sig + 32)) 32)) Spec.Ed25519.basePoint)
    (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr challenge) 64)) a))

theorem verifyEquationPoints_ok {b pk sig challenge : BitVec 32} {s : State}
    (hc : VG.Proof.Ed25519.Arm.VerifyContext b pk sig challenge s) (hl : AllLim s.mem b) :
    WP isa verifyEquationPoints s fun t => VG.Proof.Ed25519.Arm.VerifyKeep b s t ∧ AllLim t.mem b ∧
      t.gpr .r9 = BitVec.ofNat 32 (VG.Proof.Ed25519.Arm.equationResult s.mem sig challenge
        (tablePoint s.mem b 7744) (tablePoint s.mem b 7872)).toNat := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.verifyLhs_ok hc hl) fun u ⟨uk, ul, up, ua, ur⟩ => ?_)
  refine WP.mono (VG.Proof.Ed25519.Arm.verifyRhs_ok (hc.keep uk) ul) fun t ⟨tk, tl, tv⟩ => ?_
  refine ⟨uk.trans tk, tl, ?_⟩
  rw [up, ua, ur, hc.challengeInput.bytes uk] at tv
  exact tv

end VG.Proof.Ed25519.Arm
end

/-! Strict decoding of R precedes the full verification equation. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def equationWithR (m : Mem) (sig challenge : BitVec 32) (a : Spec.Ed25519.Point) : Bool :=
  match Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m (State.addr sig) 32) with
  | none => false
  | some r => VG.Proof.Ed25519.Arm.equationResult m sig challenge a r

theorem equationResult_keep {b pk sig challenge : BitVec 32} {s t : State}
    (hc : VG.Proof.Ed25519.Arm.VerifyContext b pk sig challenge s) (hk : VG.Proof.Ed25519.Arm.VerifyKeep b s t) (a r : Spec.Ed25519.Point) :
    VG.Proof.Ed25519.Arm.equationResult t.mem sig challenge a r = VG.Proof.Ed25519.Arm.equationResult s.mem sig challenge a r := by
  unfold VG.Proof.Ed25519.Arm.equationResult
  rw [(hc.sigInput.suffix32).bytes hk, hc.challengeInput.bytes hk]

theorem DecodeKeep.table {b : BitVec 32} {s t : State} (h : DecodeKeep b s t) {d : Nat}
    (hd : 1600 ≤ d) (hn : d + 128 ≤ 8192) : tablePoint t.mem b d = tablePoint s.mem b d := by
  refine tablePoint_frame h.frame fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Offset.disjoint _ (.inr (by omega)) (by omega) (by decide)

theorem verifyDecodeR_ok {b pk sig challenge : BitVec 32} {s : State}
    (hc : VG.Proof.Ed25519.Arm.VerifyContext b pk sig challenge s) (hl : AllLim s.mem b) :
    WP isa verifyDecodeR s fun t => VG.Proof.Ed25519.Arm.VerifyKeep b s t ∧
      t.gpr .r9 = BitVec.ofNat 32 (VG.Proof.Ed25519.Arm.equationWithR s.mem sig challenge (tablePoint s.mem b 7744)).toNat := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.loadHeader_ok hc.ctx 8132 (by decide)) fun u ⟨ur, um, up⟩ => ?_)
  have ku : VG.Proof.Ed25519.Arm.VerifyKeep b s u := VerifyKeep.of_rest ur (by decide) um
  have uc := hc.keep ku
  have ui := uc.sigInput.prefix (n := 32) (by decide)
  refine WP.seq (WP.mono (pointDecode_ok uc.ctx (um ▸ hl) (up.trans hc.sigHeader)
    ui.fit ui.readable ui.separate) fun v hv => ?_)
  have vk := hv.1
  have vl := hv.2.1
  have kv := ku.trans (VerifyKeep.of_decode vk)
  have va : tablePoint v.mem b 7744 = tablePoint s.mem b 7744 :=
    (vk.table (by decide) (by decide)).trans (congrArg (fun m => tablePoint m b 7744) um)
  cases dec : Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem (State.addr sig) 32) with
  | none =>
    have vr : v.gpr .r9 = 0 := by
      change DecodeResult b none v
      with_reducible exact Eq.mp (congrArg (fun q => DecodeResult b q v)
        ((congrArg (fun m => Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m (State.addr sig) 32)) um).trans dec)) hv.2.2
    refine VG.Proof.Ed25519.Arm.decodedThen_ok false vr ?_ ?_
    · intro h; exact Bool.noConfusion h
    · intro _ w wr wm
      have kw := kv.trans (VerifyKeep.of_rest wr (by decide) wm)
      refine WP.mono (recoverInvalid_ok w b) fun t ⟨tk, _, tv⟩ => ?_
      refine ⟨kw.trans (VerifyKeep.of_keep tk), ?_⟩
      simp only [VG.Proof.Ed25519.Arm.equationWithR, dec, Bool.toNat_false]
      exact tv
  | some r =>
    have result : v.gpr .r9 = 1 ∧ point (env v.mem b) 0 1 2 3 = r := by
      change DecodeResult b (some r) v
      with_reducible exact Eq.mp (congrArg (fun q => DecodeResult b q v)
        ((congrArg (fun m => Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m (State.addr sig) 32)) um).trans dec)) hv.2.2
    rcases result with ⟨vr, vp⟩
    refine VG.Proof.Ed25519.Arm.decodedThen_ok true vr ?_ ?_
    · intro _ w wr wm
      have kw := kv.trans (VerifyKeep.of_rest wr (by decide) wm)
      refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.pointTableWrite_ok (kw.ctx hc.ctx) (wm ▸ vl) 7872 (by decide) (by decide))
        fun x ⟨xk, xl, _, xp⟩ => ?_)
      have kx := kw.trans (VerifyKeep.of_powers xk (by decide) (by decide))
      have xr : tablePoint x.mem b 7872 = r :=
        xp.trans ((congrArg (fun m => point (env m b) 0 1 2 3) wm).trans vp)
      have xa : tablePoint x.mem b 7744 = tablePoint s.mem b 7744 :=
        (xk.frame.point (by decide) (.inl (by decide)) (by decide) (by decide)).trans
          ((congrArg (fun m => tablePoint m b 7744) wm).trans va)
      refine WP.mono (VG.Proof.Ed25519.Arm.verifyEquationPoints_ok (hc.keep kx) xl) fun t ⟨tk, _, tv⟩ => ?_
      refine ⟨kx.trans tk, ?_⟩
      rw [xa, xr, VG.Proof.Ed25519.Arm.equationResult_keep hc kx] at tv
      simp only [VG.Proof.Ed25519.Arm.equationWithR, dec]
      exact tv
    · intro h; exact Bool.noConfusion h

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.VerifyDecodeA`. -/
section
/-! Both public points use the strict decoder. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def decodedEquation (m : Mem) (pk sig challenge : BitVec 32) : Bool :=
  match Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m (State.addr pk) 32) with
  | none => false
  | some a => VG.Proof.Ed25519.Arm.equationWithR m sig challenge a

theorem equationWithR_keep {b pk sig challenge : BitVec 32} {s t : State}
    (hc : VG.Proof.Ed25519.Arm.VerifyContext b pk sig challenge s) (hk : VG.Proof.Ed25519.Arm.VerifyKeep b s t) (a : Spec.Ed25519.Point) :
    VG.Proof.Ed25519.Arm.equationWithR t.mem sig challenge a = VG.Proof.Ed25519.Arm.equationWithR s.mem sig challenge a := by
  unfold VG.Proof.Ed25519.Arm.equationWithR
  rw [(hc.sigInput.prefix (n := 32) (by decide)).bytes hk]
  split
  · rfl
  · exact VG.Proof.Ed25519.Arm.equationResult_keep hc hk _ _

theorem decodedEquation_keep {b pk sig challenge : BitVec 32} {s t : State}
    (hc : VG.Proof.Ed25519.Arm.VerifyContext b pk sig challenge s) (hk : VG.Proof.Ed25519.Arm.VerifyKeep b s t) :
    VG.Proof.Ed25519.Arm.decodedEquation t.mem pk sig challenge = VG.Proof.Ed25519.Arm.decodedEquation s.mem pk sig challenge := by
  unfold VG.Proof.Ed25519.Arm.decodedEquation
  rw [hc.pkInput.bytes hk]
  split
  · rfl
  · exact VG.Proof.Ed25519.Arm.equationWithR_keep hc hk _

theorem verifyDecodeA_ok {b pk sig challenge : BitVec 32} {s : State}
    (hc : VG.Proof.Ed25519.Arm.VerifyContext b pk sig challenge s) (hl : AllLim s.mem b) :
    WP isa verifyDecodeA s fun t => VG.Proof.Ed25519.Arm.VerifyKeep b s t ∧
      t.gpr .r9 = BitVec.ofNat 32 (VG.Proof.Ed25519.Arm.decodedEquation s.mem pk sig challenge).toNat := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.loadHeader_ok hc.ctx 8128 (by decide)) fun u ⟨ur, um, up⟩ => ?_)
  have ku : VG.Proof.Ed25519.Arm.VerifyKeep b s u := VerifyKeep.of_rest ur (by decide) um
  have uc := hc.keep ku
  refine WP.seq (WP.mono (pointDecode_ok uc.ctx (um ▸ hl) (up.trans hc.pkHeader)
    uc.pkInput.fit uc.pkInput.readable uc.pkInput.separate) fun v hv => ?_)
  have vk := hv.1
  have vl := hv.2.1
  have kv := ku.trans (VerifyKeep.of_decode vk)
  cases dec : Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem (State.addr pk) 32) with
  | none =>
    have vr : v.gpr .r9 = 0 := by
      change DecodeResult b none v
      with_reducible exact Eq.mp (congrArg (fun q => DecodeResult b q v)
        ((congrArg (fun m => Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m (State.addr pk) 32)) um).trans dec)) hv.2.2
    refine VG.Proof.Ed25519.Arm.decodedThen_ok false vr ?_ ?_
    · intro h; exact Bool.noConfusion h
    · intro _ w wr wm
      have kw := kv.trans (VerifyKeep.of_rest wr (by decide) wm)
      refine WP.mono (recoverInvalid_ok w b) fun t ⟨tk, _, tv⟩ => ?_
      refine ⟨kw.trans (VerifyKeep.of_keep tk), ?_⟩
      simp only [VG.Proof.Ed25519.Arm.decodedEquation, dec, Bool.toNat_false]
      exact tv
  | some a =>
    have result : v.gpr .r9 = 1 ∧ point (env v.mem b) 0 1 2 3 = a := by
      change DecodeResult b (some a) v
      with_reducible exact Eq.mp (congrArg (fun q => DecodeResult b q v)
        ((congrArg (fun m => Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m (State.addr pk) 32)) um).trans dec)) hv.2.2
    rcases result with ⟨vr, vp⟩
    refine VG.Proof.Ed25519.Arm.decodedThen_ok true vr ?_ ?_
    · intro _ w wr wm
      have kw := kv.trans (VerifyKeep.of_rest wr (by decide) wm)
      refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.pointTableWrite_ok (kw.ctx hc.ctx) (wm ▸ vl) 7744 (by decide) (by decide))
        fun x ⟨xk, xl, _, xp⟩ => ?_)
      have kx := kw.trans (VerifyKeep.of_powers xk (by decide) (by decide))
      have xa : tablePoint x.mem b 7744 = a :=
        xp.trans ((congrArg (fun m => point (env m b) 0 1 2 3) wm).trans vp)
      refine WP.mono (VG.Proof.Ed25519.Arm.verifyDecodeR_ok (hc.keep kx) xl) fun t ⟨tk, tv⟩ => ?_
      refine ⟨kx.trans tk, ?_⟩
      rw [xa, VG.Proof.Ed25519.Arm.equationWithR_keep hc kx] at tv
      simp only [VG.Proof.Ed25519.Arm.decodedEquation, dec]
      exact tv
    · intro h; exact Bool.noConfusion h

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.VerifyScalar`. -/
section
/-! The signature's scalar is checked canonically, before point decoding. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifyScalar_ok {b pk sig challenge : BitVec 32} {s : State}
    (hc : VG.Proof.Ed25519.Arm.VerifyContext b pk sig challenge s) :
    WP isa (.block verifyScalar) s fun t => VG.Proof.Ed25519.Arm.VerifyKeep b s t ∧
      t.z = decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr (sig + 32)) 32) < Spec.Ed25519.L) := by
  unfold verifyScalar
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.Arm.loadHeader_ok hc.ctx 8132 (by decide)) fun a ⟨ar, am, ap⟩ => ?_
  have ak : VG.Proof.Ed25519.Arm.VerifyKeep b s a := VerifyKeep.of_rest ar (by decide) am
  refine WP.mono (VG.Proof.Ed25519.Arm.addInput32_ok a) fun c ⟨cr, cm, cp⟩ => ?_
  have ck : VG.Proof.Ed25519.Arm.VerifyKeep b s c := ak.trans (VerifyKeep.of_rest cr (by decide) cm)
  have ci := (hc.keep ck).sigInput.suffix32
  have cptr : c.gpr .r12 = sig + 32 := by rw [cp, ap, hc.sigHeader]
  refine WP.mono (unpackField_ok (ck.ctx hc.ctx) (o := SR) (src := 0) (by decide) (by decide)
    cptr (by simpa using ci.fit) (by simpa using ci.readable)
    (by simpa using ci.separate.sub_right (Offset.sub_base _ (by decide : SR + 64 ≤ 8192))))
    fun d ⟨dr, df, dl, dv⟩ => ?_
  have dk : VG.Proof.Ed25519.Arm.VerifyKeep b s d := ck.trans (VerifyKeep.of_small dr (by decide) df (by decide) (by decide))
  have val : V d.mem (State.addr b) SR =
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr (sig + 32)) 32) := by
    have dv' : V d.mem (State.addr b) SR = packedV c.mem (State.addr (sig + 32)) := by simpa only [BitVec.add_zero] using dv
    rw [dv', ← scalar_packed_decode, (hc.sigInput.suffix32).bytes ck]
  refine WP.mono (VG.Proof.Ed25519.Arm.scalarCompare_ok (dk.ctx hc.ctx) dl) fun e ⟨er, ef, ev⟩ => ?_
  have ek := dk.trans (VerifyKeep.of_small er (by decide) ef (by decide) (by decide))
  refine wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ⟨
    ek.trans (VerifyKeep.of_rest (ht.rest []) (by decide) ht.mem), ?_⟩
  rw [hz]
  change decide (e.gpr .r5 - (0 : BitVec 32) = 0) = _
  have es : e.gpr .r5 - (0 : BitVec 32) = e.gpr .r5 := BitVec.sub_zero _
  rw [es]
  have e0 : (e.gpr .r5 = 0) ↔ (e.gpr .r5).toNat = 0 := by
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact BitVec.eq_of_toNat_eq h
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, e0, ev, val]
  split <;> simp_all

end VG.Proof.Ed25519.Arm
end

/-! The complete verifier body implements the reviewed strict equation. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Ed25519.bytesAt m p n).length = n := by
  simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]

theorem verifyEquation_bytes (m : Mem) (pk sig challenge : BitVec 32) (hs : sig.toNat + 64 ≤ 2 ^ 32) :
    Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt m (State.addr pk) 32)
      (Spec.Ed25519.bytesAt m (State.addr sig) 64) (Spec.Ed25519.bytesAt m (State.addr challenge) 64) =
      (decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr (sig + 32)) 32) < Spec.Ed25519.L) &&
        VG.Proof.Ed25519.Arm.decodedEquation m pk sig challenge) := by
  have ep : State.addr (sig + (32 : BitVec 32)) = State.addr sig + BitVec.ofNat 64 32 := addr_add (k := 32) (by omega)
  rw [Spec.Ed25519.verifyEquation]
  simp only [VG.Proof.Ed25519.Arm.bytesAt_length, bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ite_false,
    signatureBytes_take, signatureBytes_drop, ← ep]
  unfold VG.Proof.Ed25519.Arm.decodedEquation VG.Proof.Ed25519.Arm.equationWithR VG.Proof.Ed25519.Arm.equationResult
  cases Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m (State.addr pk) 32) <;>
    cases Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m (State.addr sig) 32) <;>
    simp only [Bool.and_false]

theorem verifyBody_ok {b pk sig challenge : BitVec 32} {s : State}
    (hc : VG.Proof.Ed25519.Arm.VerifyContext b pk sig challenge s) :
    WP isa verifyBody s fun t => VG.Proof.Ed25519.Arm.VerifyKeep b s t ∧ t.gpr .r9 = BitVec.ofNat 32
      (Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt s.mem (State.addr pk) 32)
        (Spec.Ed25519.bytesAt s.mem (State.addr sig) 64) (Spec.Ed25519.bytesAt s.mem (State.addr challenge) 64)).toNat := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.verifyScalar_ok hc) fun u ⟨uk, uz⟩ => ?_)
  apply WP.ite _ (congrArg some uz)
  · intro hy
    refine WP.seq (WP.mono (initFields_ok (uk.ctx hc.ctx)) fun v ⟨vk, vl, _⟩ => ?_)
    have kv := uk.trans (VerifyKeep.of_keep vk)
    refine WP.mono (VG.Proof.Ed25519.Arm.verifyDecodeA_ok (hc.keep kv) vl) fun t ⟨tk, tv⟩ => ?_
    refine ⟨kv.trans tk, ?_⟩
    rw [VG.Proof.Ed25519.Arm.decodedEquation_keep hc kv] at tv
    rw [VG.Proof.Ed25519.Arm.verifyEquation_bytes _ _ _ _ hc.sigInput.fit, hy, Bool.true_and]
    exact tv
  · intro hn
    refine WP.mono (recoverInvalid_ok u b) fun t ⟨tk, _, tv⟩ => ?_
    refine ⟨uk.trans (VerifyKeep.of_keep tk), ?_⟩
    rw [VG.Proof.Ed25519.Arm.verifyEquation_bytes _ _ _ _ hc.sigInput.fit, hn, Bool.false_and]
    exact tv

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.VerifyContract`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyStoreHeaders`. -/
section
/-! Preserve the three input pointers beyond the verification workspace. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifyHeaders_ok {s : State} {b : BitVec 32} (hb : s.gpr .r3 = b)
    (hfit : b.toNat + 8192 ≤ 2 ^ 32) (hw : (⟨State.addr b, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block verifyHeaders) s fun t => VG.Proof.Ed25519.Arm.Ctx b t ∧ Rest [.r0, .r12] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 8128, 12⟩] s.mem t.mem ∧
      t.mem.readW (State.addr b + BitVec.ofNat 64 8128) 32 = s.gpr .r0 ∧
      t.mem.readW (State.addr b + BitVec.ofNat 64 8132) 32 = s.gpr .r1 ∧
      t.mem.readW (State.addr b + BitVec.ofNat 64 8136) 32 = s.gpr .r2 := by
  refine wp_movw fun a ha => wp_dp (op2_reg _ _) fun c hc => ?_
  have cp : c.gpr .r12 = b + BitVec.ofNat 32 8128 := by
    rw [hc.gpr]
    change a.gpr .r3 + a.gpr .r12 = _
    rw [ha.other _ (by decide), hb, ha.gpr]
    rfl
  have cr : Rest [.r12] s c := (ha.rest (by decide)).trans (hc.rest (by decide))
  have cm : c.mem = s.mem := hc.mem.trans ha.mem
  have ca (k : Nat) (hk : k + 8128 < 8192) :
      State.addr (c.gpr .r12 + BitVec.ofNat 32 k) = State.addr b + BitVec.ofNat 64 (8128 + k) := by
    rw [cp, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact addr_add (by omega)
  refine wp_str (a := State.addr b + BitVec.ofNat 64 8128) (by decide)
    (by simpa only [Nat.add_zero] using ca 0 (by decide))
    (by rw [cr.wr]; exact in_base hw (by decide) (by decide)) fun d hd => ?_
  refine wp_str (a := State.addr b + BitVec.ofNat 64 8132) (by decide)
    (by rw [hd.gpr]; exact ca 4 (by decide))
    (by rw [hd.wr, cr.wr]; exact in_base hw (by decide) (by decide)) fun e he => ?_
  refine wp_str (a := State.addr b + BitVec.ofNat 64 8136) (by decide)
    (by rw [he.gpr, hd.gpr]; exact ca 8 (by decide))
    (by rw [he.wr, hd.wr, cr.wr]; exact in_base hw (by decide) (by decide)) fun f hf => ?_
  refine wp_mov (op2_reg _ _) fun t ht => WP.block_nil ?_
  have kt : Rest [.r0, .r12] s t := (cr.mono (by decide)).trans
    ((hd.rest _).trans ((he.rest _).trans ((hf.rest _).trans (ht.rest (by decide)))))
  have mt : t.mem = ((s.mem.writeW (State.addr b + BitVec.ofNat 64 8128) (s.gpr .r0)).writeW
      (State.addr b + BitVec.ofNat 64 8132) (s.gpr .r1)).writeW
      (State.addr b + BitVec.ofNat 64 8136) (s.gpr .r2) := by
    rw [ht.mem, hf.mem, he.mem, hd.mem, cm, he.gpr, hd.gpr,
      cr.gpr .r2 (by decide), cr.gpr .r1 (by decide), cr.gpr .r0 (by decide)]
  refine ⟨⟨?_, hfit, by rw [kt.wr]; exact hw⟩, kt, ?_, ?_, ?_, ?_⟩
  · rw [ht.gpr, hf.gpr, he.gpr, hd.gpr, cr.gpr .r3 (by decide), hb]
  · rw [mt]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by decide) (by decide) (by decide))
  · rw [mt, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]
  · rw [mt, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]
  · rw [mt, Mem.readW_writeW_self32]

end VG.Proof.Ed25519.Arm
end

/-! Untrusted local contract for the four-register verification ABI. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def verifyLocal : Contract Arm.isa where
  pre s :=
    let pk : Region := ⟨State.addr (s.gpr .r0), 32⟩
    let sig : Region := ⟨State.addr (s.gpr .r1), 64⟩
    let challenge : Region := ⟨State.addr (s.gpr .r2), 64⟩
    let ws : Region := ⟨State.addr (s.gpr .r3), 8192⟩
    s.rd = [pk, sig, challenge] ∧ s.wr = [ws] ∧ pk.Disjoint ws ∧ sig.Disjoint ws ∧
      challenge.Disjoint ws ∧ (s.gpr .r0).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .r1).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 64 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32
  post s t := (t.gpr .r0).toNat = if Spec.Ed25519.verifyEquation
    (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r0)) 32)
    (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 64)
    (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 64) then 1 else 0
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧
    s.gpr .r2 = t.gpr .r2 ∧ s.gpr .r3 = t.gpr .r3 ∧
    (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r0)) 32 ++
      Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 64 ++
      Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 64).map (·.toNat) =
    (Spec.Ed25519.bytesAt t.mem (State.addr (t.gpr .r0)) 32 ++
      Spec.Ed25519.bytesAt t.mem (State.addr (t.gpr .r1)) 64 ++
      Spec.Ed25519.bytesAt t.mem (State.addr (t.gpr .r2)) 64).map (·.toNat)

structure VerifyPre (s : State) : Prop where
  rd : s.rd = [⟨State.addr (s.gpr .r0), 32⟩, ⟨State.addr (s.gpr .r1), 64⟩, ⟨State.addr (s.gpr .r2), 64⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r3), 8192⟩]
  pk_ws : (⟨State.addr (s.gpr .r0), 32⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 8192⟩
  sig_ws : (⟨State.addr (s.gpr .r1), 64⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 8192⟩
  challenge_ws : (⟨State.addr (s.gpr .r2), 64⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 8192⟩
  f0 : (s.gpr .r0).toNat + 32 ≤ 2 ^ 32
  f1 : (s.gpr .r1).toNat + 64 ≤ 2 ^ 32
  f2 : (s.gpr .r2).toNat + 64 ≤ 2 ^ 32
  f3 : (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32

theorem VerifyPre.of {s : State} (h : verifyLocal.pre s) : VG.Proof.Ed25519.Arm.VerifyPre s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.VerifyMain`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyFinish`. -/
section
/-! Return the result and restore every callee-saved register. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifyFinish_ok {s : State} {b : BitVec 32} {g : Reg → BitVec 32}
    (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hs : ScalarSaved (State.addr b) g s.mem) :
    WP isa (.block verifyFinish) s fun t =>
      (∀ i < 8, t.gpr (scalarSavedReg i) = g (scalarSavedReg i)) ∧
      Rest [.r0, .r1, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s t ∧
      t.mem = s.mem ∧ t.gpr .r0 = s.gpr .r9 := by
  unfold verifyFinish
  rw [WP.block_append_iff, WP.block_append_iff]
  refine wp_mov (op2_reg _ _) fun u hu => WP.block_nil ?_
  refine WP.mono (scalarRestore_ok (hc.of_rest (hu.rest (ws := [Reg.r1]) (by decide)) (by decide)) (hu.mem ▸ hs))
    fun v ⟨vg, vr, vm⟩ => ?_
  refine wp_mov (op2_reg _ _) fun t ht => WP.block_nil ?_
  refine ⟨fun i hi => ?_, (hu.rest (by decide)).trans ((vr.mono (by decide)).trans (ht.rest (by decide))),
    ht.mem.trans (vm.trans hu.mem), ?_⟩
  · rw [ht.other _ (by
      have h : ∀ i < 8, scalarSavedReg i ≠ Reg.r0 := by decide
      exact h i hi)]
    exact vg i hi
  · rw [ht.gpr, vr.gpr _ (by decide), hu.gpr]

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.VerifySetup`. -/
section
/-! Save registers, install public headers, and establish the verifier context. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifySetup_ok {s : State} (h : VG.Proof.Ed25519.Arm.VerifyPre s) :
    WP isa (.block verifySetup) s fun t =>
      VG.Proof.Ed25519.Arm.VerifyContext (s.gpr .r3) (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) t ∧
      ScalarSaved (State.addr (s.gpr .r3)) s.gpr t.mem ∧ Rest [.r0, .r12] s t ∧
      Frame [⟨State.addr (s.gpr .r3), 8192⟩] s.mem t.mem := by
  have hw : (⟨State.addr (s.gpr .r3), 8192⟩ : Region) ∈ s.wr := by rw [h.wr]; exact List.mem_singleton_self _
  unfold verifySetup
  rw [WP.block_append_iff]
  refine WP.mono (scalarSave_ok rfl h.f3 hw) fun u ⟨us, uf, ug, uk⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.Arm.verifyHeaders_ok (by rw [ug]) h.f3 (by rw [uk.wr]; exact hw))
    fun t ⟨tc, tk, tf, tp, ts, th⟩ => ?_
  have kt := (uk.mono (by decide)).trans tk
  have ft : Frame [⟨State.addr (s.gpr .r3), 8192⟩] s.mem t.mem :=
    (uf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩).trans
    (tf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by decide)⟩)
  have ip (r : Reg) (n : Nat) (hn : (s.gpr r).toNat + n ≤ 2 ^ 32)
      (hi : (⟨State.addr (s.gpr r), n⟩ : Region) ∈ s.rd)
      (hd : (⟨State.addr (s.gpr r), n⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 8192⟩) :
      VG.Proof.Ed25519.Arm.VerifyInput (s.gpr .r3) (s.gpr r) n t := by
    refine ⟨hn, fun i hb => ?_, hd⟩
    rw [kt.rd, kt.wr]
    exact in_base (List.mem_append_left _ hi) (by omega) (by omega)
  refine ⟨⟨tc, ip .r0 32 h.f0 (by rw [h.rd]; simp) h.pk_ws,
    ip .r1 64 h.f1 (by rw [h.rd]; simp) h.sig_ws,
    ip .r2 64 h.f2 (by rw [h.rd]; simp) h.challenge_ws,
    tp.trans (congrFun ug .r0), ts.trans (congrFun ug .r1), th.trans (congrFun ug .r2)⟩,
    ?_, kt, ft⟩
  exact us.frame tf fun r hr i hi => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)

end VG.Proof.Ed25519.Arm
end

/-! The complete ARM verification equation restores the ABI and returns the specified flag. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifyEquation_correct {s : State} (h : VG.Proof.Ed25519.Arm.VerifyPre s) :
    WP isa verifyEquation s fun t => abiPreserved s t ∧ verifyLocal.post s t := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.verifySetup_ok h) fun u ⟨uc, us, uk, uf⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.verifyBody_ok uc) fun v ⟨vk, vv⟩ => ?_)
  have vs : ScalarSaved (State.addr (s.gpr .r3)) s.gpr v.mem := us.frame vk.frame fun r hr i hi => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)
  refine WP.mono (VG.Proof.Ed25519.Arm.verifyFinish_ok (vk.ctx uc.ctx) vs) fun t ⟨tg, tk, _, tv⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [tk.sp, vk.rest.sp, uk.sp]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tg 0 (by decide)
    · exact tg 1 (by decide)
    · exact tg 2 (by decide)
    · exact tg 3 (by decide)
    · exact tg 4 (by decide)
    · exact tg 5 (by decide)
    · exact tg 6 (by decide)
    · exact tg 7 (by decide)
    · rw [tk.gpr _ (by decide), vk.rest.gpr _ (by decide), uk.gpr _ (by decide)]
  · have bytes (p : BitVec 32) (n : Nat) (hn : n ≤ 64)
        (hd : (⟨State.addr p, n⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 8192⟩) :
        Spec.Ed25519.bytesAt u.mem (State.addr p) n = Spec.Ed25519.bytesAt s.mem (State.addr p) n := by
      unfold Spec.Ed25519.bytesAt
      refine List.map_congr_left fun i hi => uf.bytes (R := ⟨State.addr p, n⟩)
        (fun r hr => ?_) (by omega : n ≤ 2 ^ 64) (List.mem_range.mp hi)
      rw [List.mem_singleton.mp hr]
      exact hd
    rw [bytes _ _ (by decide) h.pk_ws, bytes _ _ (by decide) h.sig_ws,
      bytes _ _ (by decide) h.challenge_ws] at vv
    change (t.gpr .r0).toNat = _
    rw [tv, vv]
    cases Spec.Ed25519.verifyEquation
      (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r0)) 32)
      (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 64)
      (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 64) <;> rfl

end VG.Proof.Ed25519.Arm
end

/-! Verifier inputs are public and unchanged throughout the computation. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

structure VerifyPublic (m : Mem) (b pk sig challenge : BitVec 32) (s : State) : Prop where
  ctx : VG.Proof.Ed25519.Arm.VerifyContext b pk sig challenge s
  pkBytes : Spec.Ed25519.bytesAt s.mem (State.addr pk) 32 = Spec.Ed25519.bytesAt m (State.addr pk) 32
  sigBytes : Spec.Ed25519.bytesAt s.mem (State.addr sig) 64 = Spec.Ed25519.bytesAt m (State.addr sig) 64
  challengeBytes : Spec.Ed25519.bytesAt s.mem (State.addr challenge) 64 = Spec.Ed25519.bytesAt m (State.addr challenge) 64

theorem VerifyPublic.keep {m : Mem} {b pk sig challenge : BitVec 32} {s t : State}
    (h : VG.Proof.Ed25519.Arm.VerifyPublic m b pk sig challenge s) (hk : VG.Proof.Ed25519.Arm.VerifyKeep b s t) : VG.Proof.Ed25519.Arm.VerifyPublic m b pk sig challenge t :=
  ⟨h.ctx.keep hk, (h.ctx.pkInput.bytes hk).trans h.pkBytes,
    (h.ctx.sigInput.bytes hk).trans h.sigBytes, (h.ctx.challengeInput.bytes hk).trans h.challengeBytes⟩

theorem VerifyPublic.rBytes {m : Mem} {b pk sig challenge : BitVec 32} {s : State}
    (h : VG.Proof.Ed25519.Arm.VerifyPublic m b pk sig challenge s) :
    Spec.Ed25519.bytesAt s.mem (State.addr sig) 32 = Spec.Ed25519.bytesAt m (State.addr sig) 32 := by
  have he := congrArg (List.take 32) h.sigBytes
  simpa only [signatureBytes_take] using he

theorem VerifyPublic.sBytes {m : Mem} {b pk sig challenge : BitVec 32} {s : State}
    (h : VG.Proof.Ed25519.Arm.VerifyPublic m b pk sig challenge s) :
    Spec.Ed25519.bytesAt s.mem (State.addr (sig + 32)) 32 = Spec.Ed25519.bytesAt m (State.addr (sig + 32)) 32 := by
  have ep : State.addr (sig + (32 : BitVec 32)) = State.addr sig + BitVec.ofNat 64 32 :=
    addr_add (k := 32) (by have := h.ctx.sigInput.fit; omega)
  rw [ep]
  have he := congrArg (List.drop 32) h.sigBytes
  simpa only [signatureBytes_drop] using he

theorem VerifyPublic.eqResult {m : Mem} {b pk sig challenge : BitVec 32} {s : State}
    (h : VG.Proof.Ed25519.Arm.VerifyPublic m b pk sig challenge s) (a r : Spec.Ed25519.Point) :
    VG.Proof.Ed25519.Arm.equationResult s.mem sig challenge a r = VG.Proof.Ed25519.Arm.equationResult m sig challenge a r := by
  unfold VG.Proof.Ed25519.Arm.equationResult
  rw [h.sBytes, h.challengeBytes]

theorem VerifyPublic.withR {m : Mem} {b pk sig challenge : BitVec 32} {s : State}
    (h : VG.Proof.Ed25519.Arm.VerifyPublic m b pk sig challenge s) (a : Spec.Ed25519.Point) :
    VG.Proof.Ed25519.Arm.equationWithR s.mem sig challenge a = VG.Proof.Ed25519.Arm.equationWithR m sig challenge a := by
  unfold VG.Proof.Ed25519.Arm.equationWithR
  rw [h.rBytes]
  split
  · rfl
  · exact h.eqResult _ _

theorem VerifyPublic.decoded {m : Mem} {b pk sig challenge : BitVec 32} {s : State}
    (h : VG.Proof.Ed25519.Arm.VerifyPublic m b pk sig challenge s) : VG.Proof.Ed25519.Arm.decodedEquation s.mem pk sig challenge = VG.Proof.Ed25519.Arm.decodedEquation m pk sig challenge := by
  unfold VG.Proof.Ed25519.Arm.decodedEquation
  rw [h.pkBytes]
  split
  · rfl
  · exact h.withR _

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTRhs`. -/
section

/-! Merged from `Proof.Ed25519.Arm.PointEqualCT`. -/
section
/-! Point comparison branches depend only on the public projective points. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

def EqualCTPre (base : BitVec 32) (p q : Spec.Ed25519.Point) (s : State) : Prop :=
  VG.Proof.Ed25519.Arm.Ctx base s ∧ AllLim s.mem base ∧ point (env s.mem base) 0 1 2 3 = p ∧ point (env s.mem base) 4 5 6 7 = q

theorem equalFirstCT_ok {s : State} {base : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx base s) (hl : AllLim s.mem base) :
    WP isa (.seq (fieldCode pointEqualOps) (fieldEqual 8 9)) s fun t =>
      Keep base s t ∧ AllLim t.mem base ∧
      t.z = decide (env s.mem base 0 * env s.mem base 6 = env s.mem base 4 * env s.mem base 2) ∧
      env t.mem base 10 = env s.mem base 1 * env s.mem base 6 ∧
      env t.mem base 11 = env s.mem base 5 * env s.mem base 2 := by
  refine WP.seq (WP.mono (fieldCode_ok pointEqualOps hc hl) fun a ⟨ka, la, va⟩ => ?_)
  refine WP.mono (fieldEqual_ok (ka.ctx hc) la 8 9) fun t ⟨kt, lt, te, tz⟩ => ?_
  refine ⟨ka.trans kt, lt, ?_, ?_, ?_⟩
  · rw [tz, va, (equalOps_eval _).1, (equalOps_eval _).2.1]
  · rw [te 10 (by decide), va, (equalOps_eval _).2.2.1]
  · rw [te 11 (by decide), va, (equalOps_eval _).2.2.2]

theorem equalSecond_ct (base : BitVec 32) (u v : Spec.X25519.Fe) :
    CT (fun s t => (VG.Proof.Ed25519.Arm.Ctx base s ∧ AllLim s.mem base ∧ env s.mem base 10 = u ∧ env s.mem base 11 = v) ∧
      (VG.Proof.Ed25519.Arm.Ctx base t ∧ AllLim t.mem base ∧ env t.mem base 10 = u ∧ env t.mem base 11 = v))
      (.seq (fieldEqual 10 11) (.ite .eq (.block [.mov .r9 (.imm 1)]) recoverInvalid)) (fun _ _ => True) := by
  have ht : CT (fun s t => (VG.Proof.Ed25519.Arm.Ctx base s ∧ AllLim s.mem base ∧ env s.mem base 10 = u ∧ env s.mem base 11 = v) ∧
      (VG.Proof.Ed25519.Arm.Ctx base t ∧ AllLim t.mem base ∧ env t.mem base 10 = u ∧ env t.mem base 11 = v))
      (fieldEqual 10 11) (fun _ _ => True) := by
    apply ctRegs [.r0] _ (by taint_decide)
    exact fun _ _ h => r0_agree h.1.1.r0 h.2.1.r0
  have hw (s : State) (h : VG.Proof.Ed25519.Arm.Ctx base s ∧ AllLim s.mem base ∧ env s.mem base 10 = u ∧ env s.mem base 11 = v) :
      WP isa (fieldEqual 10 11) s fun t => t.z = decide (u = v) := by
    refine WP.mono (fieldEqual_ok h.1 h.2.1 10 11) fun t ⟨_, _, _, hz⟩ => ?_
    rw [hz, h.2.2.1, h.2.2.2]
  refine RelCT.seq (ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)) (RelCT.ite ?_ ?_ ?_)
  · intro s t h
    exact congrArg some (h.2.1.trans h.2.2.symm)
  · exact (returnFlag_ct true).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem pointEqual_ct (base : BitVec 32) (p q : Spec.Ed25519.Point) :
    CT (fun s t => VG.Proof.Ed25519.Arm.EqualCTPre base p q s ∧ VG.Proof.Ed25519.Arm.EqualCTPre base p q t)
      Impl.Ed25519.Arm.pointEqual (fun _ _ => True) := by
  have ht : CT (fun s t => VG.Proof.Ed25519.Arm.EqualCTPre base p q s ∧ VG.Proof.Ed25519.Arm.EqualCTPre base p q t)
      (.seq (fieldCode pointEqualOps) (fieldEqual 8 9)) (fun _ _ => True) := by
    apply ctRegs [.r0] _ (by taint_decide)
    exact fun _ _ h => r0_agree h.1.1.r0 h.2.1.r0
  have hw (s : State) (h : VG.Proof.Ed25519.Arm.EqualCTPre base p q s) :
      WP isa (.seq (fieldCode pointEqualOps) (fieldEqual 8 9)) s fun t =>
        VG.Proof.Ed25519.Arm.Ctx base t ∧ AllLim t.mem base ∧ t.z = decide (p.X * q.Z = q.X * p.Z) ∧
          env t.mem base 10 = p.Y * q.Z ∧ env t.mem base 11 = q.Y * p.Z := by
    refine WP.mono (VG.Proof.Ed25519.Arm.equalFirstCT_ok h.1 h.2.1) fun t ⟨kt, lt, tz, tu, tv⟩ => ?_
    refine ⟨kt.ctx h.1, lt, ?_, ?_, ?_⟩
    · rw [tz, ← h.2.2.1, ← h.2.2.2]; rfl
    · rw [tu, ← h.2.2.1, ← h.2.2.2]; rfl
    · rw [tv, ← h.2.2.1, ← h.2.2.2]; rfl
  rw [Impl.Ed25519.Arm.pointEqual]
  apply ctSeqAssoc
  refine RelCT.seq (ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)) (RelCT.ite ?_ ?_ ?_)
  · intro s t h
    exact congrArg some (h.2.1.2.2.1.trans h.2.2.2.2.1.symm)
  · exact (VG.Proof.Ed25519.Arm.equalSecond_ct base (p.Y * q.Z) (q.Y * p.Z)).mono
      (fun _ _ h => ⟨⟨h.1.2.1.1, h.1.2.1.2.1, h.1.2.1.2.2.2⟩,
        ⟨h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.2⟩⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.VerifyCTMul`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyCTLhs`. -/
section
/-! Both scalar pointer reload and [S]B have a public trace. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem fromCTPre_keep {b ptr : BitVec 32} {count : Nat} {s t : State}
    (h : FromCTPre b ptr count s) (hk : Keep b s t) (hl : AllLim t.mem b) : FromCTPre b ptr count t :=
  ⟨hk.ctx h.1, hl, (hk.rest.gpr _ (by decide)).trans h.2.2.1, h.2.2.2.1,
    fun i hi => by rw [hk.rest.rd, hk.rest.wr]; exact h.2.2.2.2.1 i hi, h.2.2.2.2.2⟩

theorem verifyLoadScalar_ct (b pk sig challenge : BitVec 32) :
    CT (fun s t => (VG.Proof.Ed25519.Arm.VerifyContext b pk sig challenge s ∧ AllLim s.mem b) ∧
      (VG.Proof.Ed25519.Arm.VerifyContext b pk sig challenge t ∧ AllLim t.mem b))
      (.block (loadHeader 8132 ++ ([.dp .add .r12 .r12 (.imm 32)] : List Instr)))
      (fun s t => FromCTPre b (sig + 32) 16 s ∧ FromCTPre b (sig + 32) 16 t) := by
  apply ctBoth
  · apply ctRegs [.r0] _ (by taint_decide)
    intro s t h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.1.ctx.r0.trans h.2.1.ctx.r0.symm
  · intro s ⟨hc, hl⟩
    rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed25519.Arm.loadHeader_ok hc.ctx 8132 (by decide)) fun u ⟨ur, um, up⟩ => ?_
    refine WP.mono (VG.Proof.Ed25519.Arm.addInput32_ok u) fun t ⟨tr, tm, tp⟩ => ?_
    have kt : VG.Proof.Ed25519.Arm.VerifyKeep b s t := (VerifyKeep.of_rest ur (by decide) um).trans
      (VerifyKeep.of_rest tr (by decide) tm)
    have hi := (hc.keep kt).sigInput.suffix32
    exact ⟨kt.ctx hc.ctx, by rw [tm, um]; exact hl, by rw [tp, up, hc.sigHeader],
      hi.fit, hi.readable, hi.separate⟩

theorem verifyConstBase_ct (b ptr : BitVec 32) :
    CT (fun s t => FromCTPre b ptr 16 s ∧ FromCTPre b ptr 16 t)
      (constPoint Spec.Ed25519.basePoint) (fun s t => FromCTPre b ptr 16 s ∧ FromCTPre b ptr 16 t) := by
  apply ctBoth
  · apply ctRegs [.r0] _ (by taint_decide)
    intro s t h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.1.r0.trans h.2.1.r0.symm
  · intro s hs
    refine WP.mono (fieldCode_ok (constPointOps Spec.Ed25519.basePoint) hs.1 hs.2.1) fun t ⟨tk, tl, _⟩ => ?_
    exact VG.Proof.Ed25519.Arm.fromCTPre_keep hs tk tl

theorem verifyLhs_ct (b pk sig challenge : BitVec 32) :
    CT (fun s t => (VG.Proof.Ed25519.Arm.VerifyContext b pk sig challenge s ∧ AllLim s.mem b) ∧
      (VG.Proof.Ed25519.Arm.VerifyContext b pk sig challenge t ∧ AllLim t.mem b)) verifyLhs (fun _ _ => True) := by
  have hm := (pointFromScalar_ct b (sig + 32) 16 (.inl rfl)).wp
    (fun s t h => ⟨WP.mono (pointFromScalar_ok h.1.1 h.1.2.1 h.1.2.2.1 16 (by decide) (by decide)
        h.1.2.2.2.1 h.1.2.2.2.2.1 h.1.2.2.2.2.2) (fun _ v => (v.1.ctx h.1.1).r0),
      WP.mono (pointFromScalar_ok h.2.1 h.2.2.1 h.2.2.2.1 16 (by decide) (by decide)
        h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2) (fun _ v => (v.1.ctx h.2.1).r0)⟩)
  refine RelCT.seq (VG.Proof.Ed25519.Arm.verifyLoadScalar_ct b pk sig challenge)
    (RelCT.seq (VG.Proof.Ed25519.Arm.verifyConstBase_ct b (sig + 32)) (RelCT.seq hm ?_))
  apply ctRegs [.r0] _ (by taint_decide)
  intro s t h r hr
  rw [List.mem_singleton] at hr
  subst r
  exact h.2.1.trans h.2.2.symm

end VG.Proof.Ed25519.Arm
end

/-! Verification multiplies A by every public challenge bit. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def verifyRhsMul : Prog isa :=
  .seq (.block (pointTableRead 7744 ++ loadHeader 8136)) (pointFromScalar 32)

theorem verifyLoadChallenge_ct (b pk sig challenge : BitVec 32) :
    CT (fun s t => (VG.Proof.Ed25519.Arm.VerifyContext b pk sig challenge s ∧ AllLim s.mem b) ∧
      (VG.Proof.Ed25519.Arm.VerifyContext b pk sig challenge t ∧ AllLim t.mem b))
      (.block (pointTableRead 7744 ++ loadHeader 8136))
      (fun s t => FromCTPre b challenge 32 s ∧ FromCTPre b challenge 32 t) := by
  apply ctBoth
  · apply ctRegs [.r0] _ (by taint_decide)
    intro s t h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.1.ctx.r0.trans h.2.1.ctx.r0.symm
  · intro s ⟨hc, hl⟩
    rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed25519.Arm.pointTableRead_ok hc.ctx hl 7744 (by decide) (by decide)) fun u ⟨uk, ul, _, _⟩ => ?_
    refine WP.mono (VG.Proof.Ed25519.Arm.loadHeader_ok (uk.ctx hc.ctx) 8136 (by decide)) fun t ⟨tr, tm, tp⟩ => ?_
    have ku := VerifyKeep.of_acc uk
    have kt := ku.trans (VerifyKeep.of_rest tr (by decide) tm)
    have hi := (hc.keep kt).challengeInput
    exact ⟨kt.ctx hc.ctx, tm ▸ ul, tp.trans (hc.keep ku).challengeHeader, hi.fit, hi.readable, hi.separate⟩

theorem verifyRhsMul_ct (b pk sig challenge : BitVec 32) :
    CT (fun s t => (VG.Proof.Ed25519.Arm.VerifyContext b pk sig challenge s ∧ AllLim s.mem b) ∧
      (VG.Proof.Ed25519.Arm.VerifyContext b pk sig challenge t ∧ AllLim t.mem b)) VG.Proof.Ed25519.Arm.verifyRhsMul (fun _ _ => True) :=
  RelCT.seq (VG.Proof.Ed25519.Arm.verifyLoadChallenge_ct b pk sig challenge) (pointFromScalar_ct b challenge 32 (.inr rfl))

theorem verifyRhsMul_ok {b pk sig challenge : BitVec 32} {s : State}
    (hc : VG.Proof.Ed25519.Arm.VerifyContext b pk sig challenge s) (hl : AllLim s.mem b) :
    WP isa VG.Proof.Ed25519.Arm.verifyRhsMul s fun t => PointKeep b s t ∧ AllLim t.mem b ∧ env t.mem b 16 = Spec.Ed25519.d ∧
      point (env t.mem b) 0 1 2 3 = Spec.Ed25519.pointMul
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr challenge) 64)) (tablePoint s.mem b 7744) := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.Arm.pointTableRead_ok hc.ctx hl 7744 (by decide) (by decide)) fun a ⟨ak, al, ap, _⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.Arm.loadHeader_ok (ak.ctx hc.ctx) 8136 (by decide)) fun c ⟨cr, cm, cp⟩ => ?_
  have kc := ak.trans (AccKeep.of_rest cr (by decide) cm)
  have cpk := PointKeep.of_mul (MulKeep.of_powers (PowersKeep.of_acc kc))
  have cc := hc.keep (VerifyKeep.of_acc kc)
  have cp' : c.gpr .r12 = challenge := cp.trans (hc.keep (VerifyKeep.of_acc ak)).challengeHeader
  have capp : point (env c.mem b) 0 1 2 3 = tablePoint s.mem b 7744 :=
    (congrArg (fun m => point (env m b) 0 1 2 3) cm).trans ap
  refine WP.mono (pointFromScalar_ok cc.ctx (cm ▸ al) cp' 32 (by decide) (by decide)
    cc.challengeInput.fit cc.challengeInput.readable cc.challengeInput.separate) fun t ⟨tk, tl, td, tp⟩ => ?_
  refine ⟨cpk.trans tk, tl, td, ?_⟩
  rw [hc.challengeInput.bytes (VerifyKeep.of_acc kc), capp] at tp
  exact tp

end VG.Proof.Ed25519.Arm
end

/-! Verification branches only on points determined by the public inputs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def RhsCTPre (m : Mem) (b pk sig challenge : BitVec 32) (a r lhs : Spec.Ed25519.Point) (s : State) : Prop :=
  VG.Proof.Ed25519.Arm.VerifyPublic m b pk sig challenge s ∧ AllLim s.mem b ∧ tablePoint s.mem b 7744 = a ∧
    tablePoint s.mem b 7872 = r ∧ tablePoint s.mem b 8000 = lhs

def CombineCTPre (b : BitVec 32) (ka r lhs : Spec.Ed25519.Point) (s : State) : Prop :=
  VG.Proof.Ed25519.Arm.Ctx b s ∧ AllLim s.mem b ∧ env s.mem b 16 = Spec.Ed25519.d ∧
    point (env s.mem b) 0 1 2 3 = ka ∧ tablePoint s.mem b 7872 = r ∧ tablePoint s.mem b 8000 = lhs

theorem verifyMul_public_ct (m : Mem) (b pk sig challenge : BitVec 32) (a r lhs : Spec.Ed25519.Point) :
    CT (fun s t => VG.Proof.Ed25519.Arm.RhsCTPre m b pk sig challenge a r lhs s ∧ VG.Proof.Ed25519.Arm.RhsCTPre m b pk sig challenge a r lhs t)
      VG.Proof.Ed25519.Arm.verifyRhsMul (fun s t =>
        VG.Proof.Ed25519.Arm.CombineCTPre b (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr challenge) 64)) a) r lhs s ∧
        VG.Proof.Ed25519.Arm.CombineCTPre b (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr challenge) 64)) a) r lhs t) := by
  apply ctBoth
  · exact (VG.Proof.Ed25519.Arm.verifyRhsMul_ct b pk sig challenge).mono (fun _ _ h =>
      ⟨⟨h.1.1.ctx, h.1.2.1⟩, ⟨h.2.1.ctx, h.2.2.1⟩⟩) (fun _ _ h => h)
  · intro s ⟨hp, hl, ha, hr, hh⟩
    refine WP.mono (VG.Proof.Ed25519.Arm.verifyRhsMul_ok hp.ctx hl) fun t ⟨tk, tl, td, tp⟩ => ?_
    refine ⟨tk.ctx hp.ctx.ctx, tl, td, ?_, (tk.table (by decide) (by decide)).trans hr,
      (tk.table (by decide) (by decide)).trans hh⟩
    exact tp.trans (congrArg₂ Spec.Ed25519.pointMul (congrArg Spec.Ed25519.decodeLE hp.challengeBytes) ha)

theorem verifyCombine_ct (b : BitVec 32) (ka r lhs : Spec.Ed25519.Point) :
    CT (fun s t => VG.Proof.Ed25519.Arm.CombineCTPre b ka r lhs s ∧ VG.Proof.Ed25519.Arm.CombineCTPre b ka r lhs t)
      verifyCombine (fun s t => VG.Proof.Ed25519.Arm.EqualCTPre b lhs (Spec.Ed25519.pointAdd r ka) s ∧
        VG.Proof.Ed25519.Arm.EqualCTPre b lhs (Spec.Ed25519.pointAdd r ka) t) := by
  apply ctBoth
  · apply ctRegs [.r0] _ (by taint_decide)
    intro s t h reg hr
    rw [List.mem_singleton] at hr
    subst reg
    exact h.1.1.r0.trans h.2.1.r0.symm
  · intro s ⟨hc, hl, hd, hp, hr, hh⟩
    refine WP.mono (VG.Proof.Ed25519.Arm.verifyCombine_ok hc hl hd) fun t ⟨tk, tl, tp, tq⟩ => ?_
    exact ⟨tk.ctx hc, tl, tp.trans hh, tq.trans (congrArg₂ Spec.Ed25519.pointAdd hr hp)⟩

theorem verifyRhs_ct (m : Mem) (b pk sig challenge : BitVec 32) (a r lhs : Spec.Ed25519.Point) :
    CT (fun s t => VG.Proof.Ed25519.Arm.RhsCTPre m b pk sig challenge a r lhs s ∧ VG.Proof.Ed25519.Arm.RhsCTPre m b pk sig challenge a r lhs t)
      verifyRhs (fun _ _ => True) := by
  apply ctSeqAssoc
  exact RelCT.seq (VG.Proof.Ed25519.Arm.verifyMul_public_ct m b pk sig challenge a r lhs)
    (RelCT.seq (VG.Proof.Ed25519.Arm.verifyCombine_ct b _ r lhs) (VG.Proof.Ed25519.Arm.pointEqual_ct b lhs _))

end VG.Proof.Ed25519.Arm

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.VerifyVerified`. -/
section

/-! Merged from `Proof.Ed25519.Arm.VerifyCT`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyCTDecodeR`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyCTPoints`. -/
section
/-! The strict equation has identical traces for identical public inputs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

def EquationCTPre (m : Mem) (b pk sig challenge : BitVec 32) (a r : Spec.Ed25519.Point) (s : State) : Prop :=
  VerifyPublic m b pk sig challenge s ∧ AllLim s.mem b ∧ tablePoint s.mem b 7744 = a ∧ tablePoint s.mem b 7872 = r

theorem verifyLhs_public_ct (m : Mem) (b pk sig challenge : BitVec 32) (a r : Spec.Ed25519.Point) :
    CT (fun s t => EquationCTPre m b pk sig challenge a r s ∧ EquationCTPre m b pk sig challenge a r t)
      verifyLhs (fun s t => RhsCTPre m b pk sig challenge a r
        (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr (sig + 32)) 32)) Spec.Ed25519.basePoint) s ∧
        RhsCTPre m b pk sig challenge a r
        (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr (sig + 32)) 32)) Spec.Ed25519.basePoint) t) := by
  apply ctBoth
  · exact (verifyLhs_ct b pk sig challenge).mono (fun _ _ h =>
      ⟨⟨h.1.1.ctx, h.1.2.1⟩, ⟨h.2.1.ctx, h.2.2.1⟩⟩) (fun _ _ h => h)
  · intro s ⟨hp, hl, ha, hr⟩
    refine WP.mono (verifyLhs_ok hp.ctx hl) fun t ⟨tk, tl, tp, ta, tr⟩ => ?_
    exact ⟨hp.keep tk, tl, ta.trans ha, tr.trans hr,
      tp.trans (congrArg (fun bs => Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE bs) Spec.Ed25519.basePoint) hp.sBytes)⟩

theorem verifyEquationPoints_ct (m : Mem) (b pk sig challenge : BitVec 32) (a r : Spec.Ed25519.Point) :
    CT (fun s t => EquationCTPre m b pk sig challenge a r s ∧ EquationCTPre m b pk sig challenge a r t)
      verifyEquationPoints (fun _ _ => True) :=
  RelCT.seq (verifyLhs_public_ct m b pk sig challenge a r) (verifyRhs_ct m b pk sig challenge a r _)

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.VerifyCTDecodeSupport`. -/
section
/-! Merged from `Proof.Ed25519.Arm.DecodedThenCT`. -/
section
/-! The success branch follows the public decoder flag. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem decodedThen_ct {P : State → Prop} {next : Prog isa} (flag : Bool)
    (hp : ∀ s, P s → s.gpr .r9 = BitVec.ofNat 32 flag.toNat)
    (keep : ∀ s t, P s → Rest [] s t → t.mem = s.mem → P t)
    (yes : flag = true → CT (fun s t => P s ∧ P t) next (fun _ _ => True)) :
    CT (fun s t => P s ∧ P t) (decodedThen next) (fun _ _ => True) := by
  have hc : CT (fun s t => P s ∧ P t) (.block [.cmp .r9 (.imm 0)])
      (fun s t => (P s ∧ VG.Arm.eval .ne s = some flag) ∧ (P t ∧ VG.Arm.eval .ne t = some flag)) := by
    apply ctBoth
    · exact ctRegs [] (fun _ _ _ _ hr => (List.not_mem_nil hr).elim) (by taint_decide)
    · intro s hs
      refine wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ⟨keep s t hs (ht.rest []) ht.mem, ?_⟩
      rw [VG.Arm.eval, hz, hp s hs]
      cases flag <;> rfl
  refine RelCT.seq hc (RelCT.ite (fun _ _ h => h.1.2.trans h.2.2.symm) ?_ ?_)
  · intro s t ts tt u v h ex ey
    have hy : flag = true := Option.some.inj (h.1.1.2.symm.trans h.2)
    exact yes hy _ _ _ _ _ _ ⟨h.1.1.1, h.1.2.1⟩ ex ey
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.PointDecodeCT`. -/
section
/-! Strict point decoding leaks only its public encoded bytes and pointers. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

def DecodeCTPre (base ptr : BitVec 32) (bs : List Byte) (s : State) : Prop :=
  Ctx base s ∧ AllLim s.mem base ∧ s.gpr .r12 = ptr ∧ ptr.toNat + 32 ≤ 2 ^ 32 ∧
    (∀ i < 32, InRegions (s.rd ++ s.wr) (State.addr ptr + BitVec.ofNat 64 i) 1) ∧
    (⟨State.addr ptr, 32⟩ : Region).Disjoint ⟨State.addr base, 8192⟩ ∧
    Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32 = bs

theorem pointDecode_ct (base ptr : BitVec 32) (bs : List Byte) :
    CT (fun s t => DecodeCTPre base ptr bs s ∧ DecodeCTPre base ptr bs t) pointDecode (fun _ _ => True) := by
  let b := Spec.Ed25519.decodeLE bs / 2 ^ 255 == 1
  let y := VG.Proof.X25519.toFe (Spec.Ed25519.decodeLE bs % 2 ^ 255)
  have ht : CT (fun s t => DecodeCTPre base ptr bs s ∧ DecodeCTPre base ptr bs t)
      pointDecodeLoad (fun _ _ => True) := by
    apply ctRegs [.r0, .r12] _ (by taint_decide)
    intro s t h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.r0.trans h.2.1.r0.symm
    · exact h.1.2.2.1.trans h.2.2.2.1.symm
  have hw (s : State) (h : DecodeCTPre base ptr bs s) :
      WP isa pointDecodeLoad s fun t => RecoverCTPre base b y t ∧
        t.z = decide (Spec.Ed25519.decodeLE bs % 2 ^ 255 < Spec.X25519.P) := by
    obtain ⟨hc, hl, hp, hf, hr, hsep, hbs⟩ := h
    refine WP.mono (pointDecodeLoad_ok hc hl hp hf hr hsep) fun t ⟨kt, lt, tb, ty, tz⟩ => ?_
    refine ⟨⟨kt.ctx hc, lt, ?_, ?_⟩, ?_⟩
    · rw [tb, hbs]
    · rw [ty, hbs]
    · rw [tz, hbs]
  rw [pointDecode]
  refine RelCT.seq (ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)) (RelCT.ite ?_ ?_ ?_)
  · exact fun _ _ h => congrArg some (h.2.1.2.trans h.2.2.2.symm)
  · exact (recoverPoint_ct base b y).mono (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem decodeResult_flag {base : BitVec 32} {p : Option Spec.Ed25519.Point} {s : State}
    (h : DecodeResult base p s) : s.gpr .r9 = BitVec.ofNat 32 p.isSome.toNat := by
  cases p with
  | none => exact h
  | some p => exact h.1

end VG.Proof.Ed25519.Arm
end

/-! Reload and decode either public point, retaining the equation's packed points. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem decodeResult_congr {b : BitVec 32} {p q : Option Spec.Ed25519.Point} {s : State}
    (he : p = q) (h : DecodeResult b p s) : DecodeResult b q s := he ▸ h

theorem decodeResult_rest {b : BitVec 32} {p : Option Spec.Ed25519.Point} {s t : State}
    (hr : Rest [] s t) (hm : t.mem = s.mem) (h : DecodeResult b p s) : DecodeResult b p t := by
  cases p with
  | none => exact (hr.gpr _ (by decide)).trans h
  | some p => exact ⟨(hr.gpr _ (by decide)).trans h.1,
      (congrArg (fun m => point (env m b) 0 1 2 3) hm).trans h.2⟩

def LoadDecodePre (b ptr : BitVec 32) (bs : List Byte) (d : Nat) (s : State) : Prop :=
  Ctx b s ∧ AllLim s.mem b ∧ s.mem.readW (State.addr b + BitVec.ofNat 64 d) 32 = ptr ∧
    VerifyInput b ptr 32 s ∧ Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32 = bs

theorem loadDecode_ct (b ptr : BitVec 32) (bs : List Byte) (d : Nat) (hd : d = 8128 ∨ d = 8132) :
    CT (fun s t => LoadDecodePre b ptr bs d s ∧ LoadDecodePre b ptr bs d t)
      (.seq (.block (loadHeader d)) pointDecode) (fun _ _ => True) := by
  have trace : CT (fun s t => s.gpr .r0 = t.gpr .r0) (.block (loadHeader d)) (fun _ _ => True) := by
    rcases hd with rfl | rfl
    all_goals
      apply ctRegs [.r0] _ (by taint_decide)
      intro s t h r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h
  have head : CT (fun s t => LoadDecodePre b ptr bs d s ∧ LoadDecodePre b ptr bs d t)
      (.block (loadHeader d)) (fun s t => DecodeCTPre b ptr bs s ∧ DecodeCTPre b ptr bs t) := by
    apply ctBoth
    · exact trace.mono (fun _ _ h => h.1.1.r0.trans h.2.1.r0.symm) (fun _ _ h => h)
    · intro s ⟨hc, hl, hh, hi, hb⟩
      refine WP.mono (loadHeader_ok hc d (by omega)) fun t ⟨tr, tm, tp⟩ => ?_
      exact ⟨hc.of_rest tr (by decide), tm ▸ hl, tp.trans hh, hi.fit,
        fun i hn => by rw [tr.rd, tr.wr]; exact hi.readable i hn, hi.separate,
        (congrArg (fun m => Spec.Ed25519.bytesAt m (State.addr ptr) 32) tm).trans hb⟩
  exact RelCT.seq head (pointDecode_ct b ptr bs)

theorem loadDecode_ok {b ptr : BitVec 32} {bs : List Byte} {d : Nat} {s : State}
    (h : LoadDecodePre b ptr bs d s) (hd : d + 4 ≤ 8192) :
    WP isa (.seq (.block (loadHeader d)) pointDecode) s fun t =>
      VerifyKeep b s t ∧ AllLim t.mem b ∧ DecodeResult b (Spec.Ed25519.decodePoint bs) t ∧
        ∀ k, 1600 ≤ k → k + 128 ≤ 8192 → tablePoint t.mem b k = tablePoint s.mem b k := by
  obtain ⟨hc, hl, hh, hi, hb⟩ := h
  refine WP.seq (WP.mono (loadHeader_ok hc d (by omega)) fun u ⟨ur, um, up⟩ => ?_)
  have ku : VerifyKeep b s u := VerifyKeep.of_rest ur (by decide) um
  have ui := hi.keep ku
  refine WP.mono (pointDecode_ok (ku.ctx hc) (um ▸ hl) (up.trans hh) ui.fit ui.readable ui.separate)
    fun t ht => ?_
  refine ⟨ku.trans (VerifyKeep.of_decode ht.1), ht.2.1, ?_, fun k hk hn => ?_⟩
  · with_reducible exact decodeResult_congr (congrArg Spec.Ed25519.decodePoint
      ((congrArg (fun m => Spec.Ed25519.bytesAt m (State.addr ptr) 32) um).trans hb)) ht.2.2
  · exact (ht.1.table hk hn).trans (congrArg (fun m => tablePoint m b k) um)

end VG.Proof.Ed25519.Arm
end

/-! Untrusted: R decoding and its success branch are determined by public inputs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def RDecodeCTPre (m : Mem) (b pk sig challenge : BitVec 32) (a : Spec.Ed25519.Point) (s : State) : Prop :=
  VerifyPublic m b pk sig challenge s ∧ AllLim s.mem b ∧ tablePoint s.mem b 7744 = a

def RDecodedCTPre (m : Mem) (b pk sig challenge : BitVec 32) (a : Spec.Ed25519.Point)
    (q : Option Spec.Ed25519.Point) (s : State) : Prop :=
  RDecodeCTPre m b pk sig challenge a s ∧ DecodeResult b q s

theorem verifyAfterR_ct (m : Mem) (b pk sig challenge : BitVec 32) (a : Spec.Ed25519.Point) (q : Option Spec.Ed25519.Point) :
    CT (fun s t => RDecodedCTPre m b pk sig challenge a q s ∧ RDecodedCTPre m b pk sig challenge a q t)
      (decodedThen (.seq (.block (pointTableWrite 7872)) verifyEquationPoints)) (fun _ _ => True) := by
  apply decodedThen_ct q.isSome
  · exact fun _ h => decodeResult_flag h.2
  · intro s t h tr tm
    have kt : VerifyKeep b s t := VerifyKeep.of_rest tr (by decide) tm
    exact ⟨⟨h.1.1.keep kt, tm ▸ h.1.2.1, (congrArg (fun mem => tablePoint mem b 7744) tm).trans h.1.2.2⟩,
      decodeResult_rest tr tm h.2⟩
  · intro yes
    cases q with
    | none => exact Bool.noConfusion yes
    | some r =>
      have hw : CT (fun s t => RDecodedCTPre m b pk sig challenge a (some r) s ∧ RDecodedCTPre m b pk sig challenge a (some r) t)
          (.block (pointTableWrite 7872)) (fun s t => EquationCTPre m b pk sig challenge a r s ∧ EquationCTPre m b pk sig challenge a r t) := by
        apply ctBoth
        · apply ctRegs [.r0] _ (by taint_decide)
          intro s t h reg hr
          rw [List.mem_singleton] at hr
          subst reg
          exact h.1.1.1.ctx.ctx.r0.trans h.2.1.1.ctx.ctx.r0.symm
        · intro s ⟨⟨hp, hl, ha⟩, _, hpoint⟩
          refine WP.mono (pointTableWrite_ok hp.ctx.ctx hl 7872 (by decide) (by decide)) fun t ⟨tk, tl, _, tp⟩ => ?_
          exact ⟨hp.keep (VerifyKeep.of_powers tk (by decide) (by decide)), tl,
            (tk.frame.point (by decide) (.inl (by decide)) (by decide) (by decide)).trans ha, tp.trans hpoint⟩
      exact RelCT.seq hw (verifyEquationPoints_ct m b pk sig challenge a r)

theorem verifyDecodeR_ct (m : Mem) (b pk sig challenge : BitVec 32) (a : Spec.Ed25519.Point) :
    CT (fun s t => RDecodeCTPre m b pk sig challenge a s ∧ RDecodeCTPre m b pk sig challenge a t)
      verifyDecodeR (fun _ _ => True) := by
  have loadPre (s : State) (h : RDecodeCTPre m b pk sig challenge a s) :
      LoadDecodePre b sig (Spec.Ed25519.bytesAt m (State.addr sig) 32) 8132 s :=
    ⟨h.1.ctx.ctx, h.2.1, h.1.ctx.sigHeader, h.1.ctx.sigInput.prefix (by decide), h.1.rBytes⟩
  have hd : CT (fun s t => RDecodeCTPre m b pk sig challenge a s ∧ RDecodeCTPre m b pk sig challenge a t)
      (.seq (.block (loadHeader 8132)) pointDecode)
      (fun s t => RDecodedCTPre m b pk sig challenge a (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m (State.addr sig) 32)) s ∧
        RDecodedCTPre m b pk sig challenge a (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m (State.addr sig) 32)) t) := by
    apply ctBoth
    · exact (loadDecode_ct b sig _ 8132 (by decide)).mono (fun s t h => ⟨loadPre s h.1, loadPre t h.2⟩) (fun _ _ h => h)
    · intro s hs
      refine WP.mono (loadDecode_ok (loadPre s hs) (by decide)) fun t ht => ?_
      refine ⟨⟨hs.1.keep ht.1, ht.2.1, (ht.2.2.2 7744 (by decide) (by decide)).trans hs.2.2⟩, ?_⟩
      with_reducible exact ht.2.2.1
  exact ctSeqAssoc (RelCT.seq hd (verifyAfterR_ct m b pk sig challenge a _))

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.VerifyCTBody`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyCTDecodeA`. -/
section
/-! Untrusted: A decoding and its success branch are determined by public inputs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def ADecodedCTPre (m : Mem) (b pk sig challenge : BitVec 32)
    (q : Option Spec.Ed25519.Point) (s : State) : Prop :=
  VerifyPublic m b pk sig challenge s ∧ AllLim s.mem b ∧ DecodeResult b q s

theorem verifyAfterA_ct (m : Mem) (b pk sig challenge : BitVec 32) (q : Option Spec.Ed25519.Point) :
    CT (fun s t => ADecodedCTPre m b pk sig challenge q s ∧ ADecodedCTPre m b pk sig challenge q t)
      (decodedThen (.seq (.block (pointTableWrite 7744)) verifyDecodeR)) (fun _ _ => True) := by
  apply decodedThen_ct q.isSome
  · exact fun _ h => decodeResult_flag h.2.2
  · intro s t h tr tm
    have kt : VerifyKeep b s t := VerifyKeep.of_rest tr (by decide) tm
    exact ⟨h.1.keep kt, tm ▸ h.2.1, decodeResult_rest tr tm h.2.2⟩
  · intro yes
    cases q with
    | none => exact Bool.noConfusion yes
    | some a =>
      have hw : CT (fun s t => ADecodedCTPre m b pk sig challenge (some a) s ∧ ADecodedCTPre m b pk sig challenge (some a) t)
          (.block (pointTableWrite 7744)) (fun s t => RDecodeCTPre m b pk sig challenge a s ∧ RDecodeCTPre m b pk sig challenge a t) := by
        apply ctBoth
        · apply ctRegs [.r0] _ (by taint_decide)
          intro s t h reg hr
          rw [List.mem_singleton] at hr
          subst reg
          exact h.1.1.ctx.ctx.r0.trans h.2.1.ctx.ctx.r0.symm
        · intro s ⟨hp, hl, _, hpoint⟩
          refine WP.mono (pointTableWrite_ok hp.ctx.ctx hl 7744 (by decide) (by decide)) fun t ⟨tk, tl, _, tp⟩ => ?_
          exact ⟨hp.keep (VerifyKeep.of_powers tk (by decide) (by decide)), tl, tp.trans hpoint⟩
      exact RelCT.seq hw (verifyDecodeR_ct m b pk sig challenge a)

theorem verifyDecodeA_ct (m : Mem) (b pk sig challenge : BitVec 32) :
    CT (fun s t => (VerifyPublic m b pk sig challenge s ∧ AllLim s.mem b) ∧
      (VerifyPublic m b pk sig challenge t ∧ AllLim t.mem b)) verifyDecodeA (fun _ _ => True) := by
  have loadPre (s : State) (h : VerifyPublic m b pk sig challenge s ∧ AllLim s.mem b) :
      LoadDecodePre b pk (Spec.Ed25519.bytesAt m (State.addr pk) 32) 8128 s :=
    ⟨h.1.ctx.ctx, h.2, h.1.ctx.pkHeader, h.1.ctx.pkInput, h.1.pkBytes⟩
  have hd : CT (fun s t => (VerifyPublic m b pk sig challenge s ∧ AllLim s.mem b) ∧
      (VerifyPublic m b pk sig challenge t ∧ AllLim t.mem b))
      (.seq (.block (loadHeader 8128)) pointDecode)
      (fun s t => ADecodedCTPre m b pk sig challenge (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m (State.addr pk) 32)) s ∧
        ADecodedCTPre m b pk sig challenge (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m (State.addr pk) 32)) t) := by
    apply ctBoth
    · exact (loadDecode_ct b pk _ 8128 (by decide)).mono (fun s t h => ⟨loadPre s h.1, loadPre t h.2⟩) (fun _ _ h => h)
    · intro s hs
      refine WP.mono (loadDecode_ok (loadPre s hs) (by decide)) fun t ht => ?_
      refine ⟨hs.1.keep ht.1, ht.2.1, ?_⟩
      with_reducible exact ht.2.2.1
  exact ctSeqAssoc (RelCT.seq hd (verifyAfterA_ct m b pk sig challenge _))

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.VerifyCTScalar`. -/
section
/-! Canonical scalar checking loads through the public signature pointer. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifyScalar_ct (b pk sig challenge : BitVec 32) :
    CT (fun s t => VerifyContext b pk sig challenge s ∧ VerifyContext b pk sig challenge t)
      (.block verifyScalar) (fun _ _ => True) := by
  have head : CT (fun s t => VerifyContext b pk sig challenge s ∧ VerifyContext b pk sig challenge t)
      (.block (loadHeader 8132 ++ ([.dp .add .r12 .r12 (.imm 32)] : List Instr)))
      (fun s t => (s.gpr .r0 = b ∧ s.gpr .r12 = sig + 32) ∧ (t.gpr .r0 = b ∧ t.gpr .r12 = sig + 32)) := by
    apply ctBoth
    · apply ctRegs [.r0] _ (by taint_decide)
      intro s t h r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.1.ctx.r0.trans h.2.ctx.r0.symm
    · intro s hc
      rw [WP.block_append_iff]
      refine WP.mono (loadHeader_ok hc.ctx 8132 (by decide)) fun u ⟨ur, um, up⟩ => ?_
      refine WP.mono (addInput32_ok u) fun t ⟨tr, _, tp⟩ => ?_
      exact ⟨(tr.gpr _ (by decide)).trans ((ur.gpr _ (by decide)).trans hc.ctx.r0), by rw [tp, up, hc.sigHeader]⟩
  have tail : CT (fun s t => (s.gpr .r0 = b ∧ s.gpr .r12 = sig + 32) ∧ (t.gpr .r0 = b ∧ t.gpr .r12 = sig + 32))
      (.block (unpackField SR 0 ++ scalarCompare ++ ([.cmp .r5 (.imm 0)] : List Instr))) (fun _ _ => True) := by
    apply ctRegs [.r0, .r12] _ (by taint_decide)
    intro s t h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.trans h.2.1.symm
    · exact h.1.2.trans h.2.2.symm
  simpa only [verifyScalar, List.append_assoc] using ctBlockAppend head tail

theorem verifyScalar_public_ct (m : Mem) (b pk sig challenge : BitVec 32) :
    CT (fun s t => VerifyPublic m b pk sig challenge s ∧ VerifyPublic m b pk sig challenge t)
      (.block verifyScalar) (fun s t =>
        (VerifyPublic m b pk sig challenge s ∧ s.z = decide (Spec.Ed25519.decodeLE
          (Spec.Ed25519.bytesAt m (State.addr (sig + 32)) 32) < Spec.Ed25519.L)) ∧
        (VerifyPublic m b pk sig challenge t ∧ t.z = decide (Spec.Ed25519.decodeLE
          (Spec.Ed25519.bytesAt m (State.addr (sig + 32)) 32) < Spec.Ed25519.L))) := by
  apply ctBoth
  · exact (verifyScalar_ct b pk sig challenge).mono (fun _ _ h => ⟨h.1.ctx, h.2.ctx⟩) (fun _ _ h => h)
  · intro s hs
    refine WP.mono (verifyScalar_ok hs.ctx) fun t ⟨tk, tz⟩ => ?_
    exact ⟨hs.keep tk, tz.trans (congrArg (fun bs => decide (Spec.Ed25519.decodeLE bs < Spec.Ed25519.L)) hs.sBytes)⟩

end VG.Proof.Ed25519.Arm
end

/-! The complete strict verifier leaks only its declared public inputs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

theorem verifyInit_ct (m : Mem) (b pk sig challenge : BitVec 32) :
    CT (fun s t => VerifyPublic m b pk sig challenge s ∧ VerifyPublic m b pk sig challenge t)
      (.block initFields) (fun s t => (VerifyPublic m b pk sig challenge s ∧ AllLim s.mem b) ∧
        (VerifyPublic m b pk sig challenge t ∧ AllLim t.mem b)) := by
  apply ctBoth
  · apply ctRegs [.r0] _ (by taint_decide)
    intro s t h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.ctx.ctx.r0.trans h.2.ctx.ctx.r0.symm
  · intro s hs
    refine WP.mono (initFields_ok hs.ctx.ctx) fun t ⟨tk, tl, _⟩ => ?_
    exact ⟨hs.keep (VerifyKeep.of_keep tk), tl⟩

theorem verifyBody_ct (m : Mem) (b pk sig challenge : BitVec 32) :
    CT (fun s t => VerifyPublic m b pk sig challenge s ∧ VerifyPublic m b pk sig challenge t)
      verifyBody (fun _ _ => True) := by
  refine RelCT.seq (verifyScalar_public_ct m b pk sig challenge) (RelCT.ite ?_ ?_ ?_)
  · exact fun _ _ h => congrArg some (h.1.2.trans h.2.2.symm)
  · exact (RelCT.seq (verifyInit_ct m b pk sig challenge) (verifyDecodeA_ct m b pk sig challenge)).mono
      (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.Arm
end

/-! The verifier's ABI wrapper preserves the public input relation. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

private theorem byteMap_inj : ∀ {xs ys : List Byte}, xs.map (·.toNat) = ys.map (·.toNat) → xs = ys
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, byteMap_inj h.2]

structure VerifyWrapPublic (m : Mem) (b pk sig challenge : BitVec 32) (s : State) : Prop where
  pre : verifyLocal.pre s
  r0 : s.gpr .r0 = pk
  r1 : s.gpr .r1 = sig
  r2 : s.gpr .r2 = challenge
  r3 : s.gpr .r3 = b
  pkBytes : Spec.Ed25519.bytesAt s.mem (State.addr pk) 32 = Spec.Ed25519.bytesAt m (State.addr pk) 32
  sigBytes : Spec.Ed25519.bytesAt s.mem (State.addr sig) 64 = Spec.Ed25519.bytesAt m (State.addr sig) 64
  challengeBytes : Spec.Ed25519.bytesAt s.mem (State.addr challenge) 64 = Spec.Ed25519.bytesAt m (State.addr challenge) 64

theorem verifySetup_ct (m : Mem) (b pk sig challenge : BitVec 32) :
    CT (fun x y => VerifyWrapPublic m b pk sig challenge x ∧ VerifyWrapPublic m b pk sig challenge y)
      (.block verifySetup) (fun x y => VerifyPublic m b pk sig challenge x ∧ VerifyPublic m b pk sig challenge y) := by
  apply ctBoth
  · apply ctRegs [.r0, .r1, .r2, .r3] _ (by taint_decide)
    intro x y h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.1.r0.trans h.2.r0.symm
    · exact h.1.r1.trans h.2.r1.symm
    · exact h.1.r2.trans h.2.r2.symm
    · exact h.1.r3.trans h.2.r3.symm
  · intro s h
    have hp := VerifyPre.of h.pre
    refine WP.mono (verifySetup_ok hp) fun t ⟨tc, _, _, tf⟩ => ?_
    have tc' : VerifyContext b pk sig challenge t := by rw [h.r0, h.r1, h.r2, h.r3] at tc; exact tc
    have bytes (p : BitVec 32) (n : Nat) (hn : n ≤ 64)
        (hd : (⟨State.addr p, n⟩ : Region).Disjoint ⟨State.addr b, 8192⟩) :
        Spec.Ed25519.bytesAt t.mem (State.addr p) n = Spec.Ed25519.bytesAt s.mem (State.addr p) n := by
      unfold Spec.Ed25519.bytesAt
      refine List.map_congr_left fun i hi => tf.bytes (R := ⟨State.addr p, n⟩)
        (fun r hr => ?_) (by omega : n ≤ 2 ^ 64) (List.mem_range.mp hi)
      rw [List.mem_singleton.mp hr, h.r3]
      exact hd
    exact ⟨tc', (bytes pk 32 (by decide) tc'.pkInput.separate).trans h.pkBytes,
      (bytes sig 64 (by decide) tc'.sigInput.separate).trans h.sigBytes,
      (bytes challenge 64 (by decide) tc'.challengeInput.separate).trans h.challengeBytes⟩

theorem verify_ct_of_body
    (bodyCT : ∀ (m : Mem) (b pk sig challenge : BitVec 32),
      CT (fun s t => VerifyPublic m b pk sig challenge s ∧ VerifyPublic m b pk sig challenge t)
        verifyBody (fun _ _ => True)) :
    ConstantTime isa verifyLocal.pre verifyLocal.pub verifyEquation := by
  have hct (m : Mem) (b pk sig challenge : BitVec 32) :
      CT (fun x y => VerifyWrapPublic m b pk sig challenge x ∧ VerifyWrapPublic m b pk sig challenge y)
        verifyEquation (fun _ _ => True) := by
    have hb := (bodyCT m b pk sig challenge).wpDep (fun x y h => ⟨verifyBody_ok h.1.ctx, verifyBody_ok h.2.ctx⟩)
    have hb' := hb.mono (fun _ _ h => h) (fun x y ⟨_, a, c, h, hx, hy⟩ =>
      And.intro (hx.1.ctx h.1.ctx.ctx).r0 (hy.1.ctx h.2.ctx.ctx).r0)
    refine RelCT.seq (verifySetup_ct m b pk sig challenge) (RelCT.seq hb' ?_)
    apply ctRegs [.r0] _ (by taint_decide)
    intro x y h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.trans h.2.symm
  intro s t tx ty u v hs ht ⟨_, h0, h1, h2, h3, hbytes⟩ ex ey
  have hb := byteMap_inj hbytes
  obtain ⟨first, last⟩ := List.append_inj' hb (by simp only [bytesAt_length])
  obtain ⟨first, middle⟩ := List.append_inj' first (by simp only [bytesAt_length])
  rw [← h0] at first
  rw [← h1] at middle
  rw [← h2] at last
  exact (hct s.mem (s.gpr .r3) (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) _ _ _ _ _ _
    ⟨⟨hs, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨ht, h0.symm, h1.symm, h2.symm, h3.symm, first.symm, middle.symm, last.symm⟩⟩ ex ey).1

theorem verify_ct : ConstantTime isa verifyLocal.pre verifyLocal.pub verifyEquation :=
  verify_ct_of_body verifyBody_ct

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.VerifyLit`. -/
section
namespace VG.Impl.Ed25519.Arm
materialize_code verifyEquation
end VG.Impl.Ed25519.Arm
end

/-! The verification equation meets the reviewed contract and preserves the ARM ABI. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

def verifySatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 64⟩, ⟨0x3000, 64⟩]
  wr := [⟨0x4000, 8192⟩]

theorem verify_ok (s : State) (hs : verifyLocal.pre s) :
    ∃ t s', Exec isa verifyEquation s t s' ∧ abiPreserved s s' ∧ verifyLocal.post s s' :=
  verifyEquation_correct (VerifyPre.of hs)

private theorem returnFlag_value (v : BitVec 32) (b : Bool)
    (h : v.toNat = if b then 1 else 0) : v = if b then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  cases b <;> exact h

theorem verify_implies : verifyLocal.Implies (Spec.Ed25519.verifyEquationContract Arm.abi) where
  pre := by
    sig_implies_pre [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, verifyLocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
  post := by
    intro s t _ h
    sig_post [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
    exact (e _ _).trans (returnFlag_value _ _ h)
  pub := by
    sig_implies_pub [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, verifyLocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
  sat := by
    sig_implies_sat [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, verifyLocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [verifySatState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using verifySatState

theorem verify_verified : Verified Arm.target verifyEquation (Spec.Ed25519.verifyEquationContract Arm.abi) :=
  Verified.of_correct verify_ok verify_ct verify_implies

end VG.Proof.Ed25519.Arm

end
