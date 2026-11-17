module

import VerifiedGarbage.Proof.Ed25519.Arm.LrSlot
public import VerifiedGarbage.Proof.Ed25519.Arm.PointKeep
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarPass
public import VerifiedGarbage.Impl.Ed25519.Arm.Verify
public import VerifiedGarbage.Proof.Ed25519.Arm.DecodeKeep
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Ed25519.Arm.PointDecode
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarCodec
import VerifiedGarbage.Proof.Ed25519.Arm.InitFields
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
import VerifiedGarbage.Proof.Ed25519.Bytes
public import VerifiedGarbage.Proof.Ed25519.Arm.ScalarABI
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Ed25519.Arm.RecoverSign
import VerifiedGarbage.Proof.Ed25519.Arm.PointEqual
import VerifiedGarbage.Proof.Ed25519.Arm.UnpackField
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTMul
import VerifiedGarbage.Proof.Ed25519.Arm.PointFromScalar
import VerifiedGarbage.Proof.Ed25519.Arm.Points

/-! ### `Ed25519.Arm.VerifyHeaders`, which only this module used -/

section

/-! Merged from `Proof.Ed25519.Arm.VerifyContext`. -/

@[expose] public section

section
/-! Merged from `Proof.Ed25519.Arm.VerifyFrame`. -/
section
/-! Merged from `Proof.Ed25519.Arm.PointTableIO`. -/
section
/-! Save and reload the verification equation's packed points. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem pointTableWrite_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (hl : AllLim s.mem b)
    (o : Nat) (ho : 1632 ≤ o) (hn : o + 128 ≤ 8192) :
    WP isa (.block (pointTableWrite o)) s fun t => PowersKeep b o 128 s t ∧ AllLim t.mem b ∧
      env t.mem b = env s.mem b ∧ tablePoint t.mem b o = point (env s.mem b) 0 1 2 3 := by
  unfold pointTableWrite
  rw [WP.block_append_iff]
  refine WP.mono (scratchAddr_ok hc o (by omega_using [hn])) fun u ⟨ur, um, up⟩ => ?_
  refine WP.mono (pointToTable_ok (hc.of_rest ur (by decide)) (um ▸ hl) up ho hn) fun t ⟨tp, tk⟩ => ?_
  exact ⟨⟨(ur.mono (by decide)).trans (tk.rest.mono (by decide)), by rw [← um]; exact TableFrame.table tk.frame⟩,
    tk.lim ho hn (um ▸ hl), (tk.env ho hn).trans (congrArg (fun m => env m b) um),
    tp.trans (congrArg (fun m => point (env m b) 0 1 2 3) um)⟩

theorem pointTableRead_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (hl : AllLim s.mem b)
    (o : Nat) (ho : 1632 ≤ o) (hn : o + 128 ≤ 8192) :
    WP isa (.block (pointTableRead o)) s fun t => AccKeep b s t ∧ AllLim t.mem b ∧
      point (env t.mem b) 0 1 2 3 = tablePoint s.mem b o ∧
      ∀ i : Slot, 4 ≤ i.val → env t.mem b i = env s.mem b i := by
  unfold pointTableRead
  rw [WP.block_append_iff]
  refine WP.mono (scratchAddr_ok hc o (by omega_using [hn])) fun u ⟨ur, um, up⟩ => ?_
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

theorem scalarCompare_ok {b : BitVec 32} {s : State} (hc : Ctx b s)
    (hl : Lim s.mem (State.addr b) SR) :
    WP isa (.block scalarCompare) s fun t =>
      Rest [.r2, .r3, .r4, .r5, .r6] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 SD, 64⟩] s.mem t.mem ∧
      (t.gpr .r5).toNat = if V s.mem (State.addr b) SR < Spec.Ed25519.L then 0 else 1 := by
  unfold scalarCompare
  simp only [List.cons_append, List.nil_append]
  refine wp_movw fun u hu => wp_mov (op2_imm (by decide)) fun v hv => ?_
  obtain kv : Rest [.r5, .r6] s v := (hu.rest (by decide)).trans (hv.rest (by decide))
  obtain mv : v.mem = s.mem := by rw [hv.mem, hu.mem]
  obtain hcv := hc.of_rest kv (by decide)
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

abbrev verifyRegion (b : BitVec 32) : Region := ⟨State.addr b + BitVec.ofNat 64 32, 8128⟩
structure VerifyKeep (b : BitVec 32) (s t : State) : Prop where
  rest : Rest powersClob s t
  frame : Frame [verifyRegion b] s.mem t.mem

theorem VerifyKeep.ctx {b : BitVec 32} {s t : State} (h : VerifyKeep b s t) (hc : Ctx b s) : Ctx b t :=
  hc.of_rest h.rest (by decide)
theorem VerifyKeep.trans {b : BitVec 32} {s t u : State} (h : VerifyKeep b s t) (k : VerifyKeep b t u) :
    VerifyKeep b s u := ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩
theorem VerifyKeep.of_small {b : BitVec 32} {s t : State} {o n : Nat} {ws : List Reg}
    (hr : Rest ws s t) (hw : ∀ r ∈ ws, r ∈ powersClob)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, n⟩] s.mem t.mem) (ho : 32 ≤ o) (hn : o + n ≤ 8160) :
    VerifyKeep b s t := ⟨hr.mono hw, hf.sub fun r hm => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hm]; exact Offset.sub _ ho hn⟩⟩
theorem VerifyKeep.of_point {b : BitVec 32} {s t : State} (h : PointKeep b s t) : VerifyKeep b s t := by
  refine ⟨h.rest, h.frame.sub fun r hr => ?_⟩
  simp only [pointRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
theorem VerifyKeep.of_powers {b : BitVec 32} {o n : Nat} {s t : State}
    (h : PowersKeep b o n s t) (ho : 32 ≤ o) (hn : o + n ≤ 8160) : VerifyKeep b s t := by
  refine ⟨h.rest, h.frame.sub fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨_, List.mem_singleton_self _, Offset.sub _ ho hn⟩
theorem VerifyKeep.of_keep {b : BitVec 32} {s t : State} (h : Keep b s t) : VerifyKeep b s t :=
  VerifyKeep.of_point (PointKeep.of_keep h)
theorem VerifyKeep.of_acc {b : BitVec 32} {s t : State} (h : AccKeep b s t) : VerifyKeep b s t :=
  VerifyKeep.of_powers (PowersKeep.of_acc h) (o := 1632) (n := 0) (by decide) (by decide)
theorem VerifyKeep.of_decode {b : BitVec 32} {s t : State} (h : DecodeKeep b s t) : VerifyKeep b s t := by
  refine ⟨h.rest.mono (by decide), h.frame.sub fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
theorem VerifyKeep.of_rest {b : BitVec 32} {s t : State} {ws : List Reg}
    (hr : Rest ws s t) (hw : ∀ r ∈ ws, r ∈ powersClob) (hm : t.mem = s.mem) : VerifyKeep b s t :=
  ⟨hr.mono hw, by rw [hm]; exact Frame.refl _ _⟩

theorem VerifyKeep.header {b : BitVec 32} {s t : State} (h : VerifyKeep b s t)
    (d : Nat) (hd : 8160 ≤ d) (hn : d + 4 ≤ 8192) :
    t.mem.readW (State.addr b + BitVec.ofNat 64 d) 32 = s.mem.readW (State.addr b + BitVec.ofNat 64 d) 32 := by
  apply BitVec.eq_of_toNat_eq
  exact wd_frame h.frame fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inr (by omega_using [hd])) (by omega_using [hn]) (by decide)

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
    (h : VerifyInput b ptr len s) (hk : VerifyKeep b s t) : VerifyInput b ptr len t :=
  ⟨h.fit, fun i hi => by rw [hk.rest.rd, hk.rest.wr]; exact h.readable i hi, h.separate⟩

theorem VerifyInput.bytes {b ptr : BitVec 32} {len : Nat} {s t : State}
    (h : VerifyInput b ptr len s) (hk : VerifyKeep b s t) :
    Spec.Ed25519.bytesAt t.mem (State.addr ptr) len = Spec.Ed25519.bytesAt s.mem (State.addr ptr) len := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => hk.frame.bytes (R := ⟨State.addr ptr, len⟩)
    (fun r hr => ?_) (by have := h.fit; omega_using [this] : len ≤ 2 ^ 64) (List.mem_range.mp hi)
  rw [List.mem_singleton.mp hr]
  exact h.separate.sub_right (Offset.sub_base _ (by decide))

theorem VerifyInput.prefix {b ptr : BitVec 32} {len n : Nat} {s : State}
    (h : VerifyInput b ptr len s) (hn : n ≤ len) : VerifyInput b ptr n s :=
  ⟨by have := h.fit; omega_using [hn, this], fun i hi => h.readable i (by omega_using [hn, hi]), h.separate.sub_left (Region.sub_prefix hn)⟩

theorem VerifyInput.suffix32 {b ptr : BitVec 32} {s : State} (h : VerifyInput b ptr 64 s) :
    VerifyInput b (ptr + 32) 32 s := by
  obtain en : (ptr + (32 : BitVec 32)).toNat = ptr.toNat + 32 := by
    rw [toNat_add_lt (by have := h.fit; change ptr.toNat + 32 < 2 ^ 32; omega_using [this])]
    rfl
  obtain ep : State.addr (ptr + (32 : BitVec 32)) = State.addr ptr + BitVec.ofNat 64 32 := addr_add (k := 32) (by have := h.fit; omega_using [en])
  refine ⟨by rw [en]; have := h.fit; omega_using [this], ?_, ?_⟩
  · intro i hi
    rw [ep, Offset.add_add]
    exact h.readable (32 + i) (by omega_using [hi])
  · rw [ep]
    exact h.separate.sub_left (Offset.sub_base _ (by decide))

structure VerifyContext (b pk sig challenge : BitVec 32) (s : State) : Prop where
  ctx : Ctx b s
  pkInput : VerifyInput b pk 32 s
  sigInput : VerifyInput b sig 64 s
  challengeInput : VerifyInput b challenge 64 s
  pkHeader : s.mem.readW (State.addr b + BitVec.ofNat 64 8160) 32 = pk
  sigHeader : s.mem.readW (State.addr b + BitVec.ofNat 64 8164) 32 = sig
  challengeHeader : s.mem.readW (State.addr b + BitVec.ofNat 64 8168) 32 = challenge
  challengeTop : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr challenge) 64) < 2 ^ 256

theorem VerifyContext.keep {b pk sig challenge : BitVec 32} {s t : State}
    (h : VerifyContext b pk sig challenge s) (hk : VerifyKeep b s t) : VerifyContext b pk sig challenge t :=
  ⟨hk.ctx h.ctx, h.pkInput.keep hk, h.sigInput.keep hk, h.challengeInput.keep hk,
    (hk.header _ (by decide) (by decide)).trans h.pkHeader,
    (hk.header _ (by decide) (by decide)).trans h.sigHeader,
    (hk.header _ (by decide) (by decide)).trans h.challengeHeader,
    by rw [h.challengeInput.bytes hk]; exact h.challengeTop⟩

/-- A challenge below `2²⁵⁶` is its first 32 bytes. -/
theorem decodeLE_low {m : Mem} {p : Addr}
    (h : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p 64) < 2 ^ 256) :
    Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p 32) = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p 64) := by
  have hs : Spec.Ed25519.bytesAt m p (32 + 32) =
      Spec.Ed25519.bytesAt m p 32 ++ Spec.Ed25519.bytesAt m (p + BitVec.ofNat 64 32) 32 :=
    Proof.X25519.bytesAt_add m p 32 32
  have hl : (Spec.Ed25519.bytesAt m p 32).length = 32 := by simp [Spec.Ed25519.bytesAt]
  rw [show 64 = 32 + 32 from rfl, hs, Proof.Ed25519.decodeLE_append, hl] at h ⊢
  have hz : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (p + BitVec.ofNat 64 32) 32) = 0 := by
    refine Nat.eq_zero_of_not_pos fun hp => ?_
    have := Nat.mul_le_mul_left (256 ^ 32) hp
    omega_using [h, this]
  rw [hz, Nat.mul_zero, Nat.add_zero]

/-- The challenge's bytes, which a frame of the working space keeps. -/
theorem challenge_frame {m m' : Mem} {b challenge : BitVec 32}
    (hf : Frame [⟨State.addr b, 8192⟩] m m')
    (hd : (⟨State.addr challenge, 64⟩ : Region).Disjoint ⟨State.addr b, 8192⟩) :
    Spec.Ed25519.bytesAt m' (State.addr challenge) 64 = Spec.Ed25519.bytesAt m (State.addr challenge) 64 := by
  unfold Spec.Ed25519.bytesAt
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨State.addr challenge, 64⟩)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (by change 64 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)

end VG.Proof.Ed25519.Arm
end

/-! Load a public argument pointer from the protected header area. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem loadHeader_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (d : Nat) (hd : d + 4 ≤ 8192) :
    WP isa (.block (loadHeader d)) s fun t => Rest [.r12] s t ∧ t.mem = s.mem ∧
      t.gpr .r12 = s.mem.readW (State.addr b + BitVec.ofNat 64 d) 32 := by
  unfold loadHeader
  rw [WP.block_append_iff]
  refine WP.mono (scratchAddr_ok hc d (by omega_using [hd])) fun u ⟨ur, um, up⟩ => ?_
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 d) (by decide)
    (by rw [up]; exact (congrArg State.addr (BitVec.add_zero _)).trans (hc.ptr_addr (by omega_using [hd])))
    (by rw [ur.rd, ur.wr]; exact in_base (List.mem_append_right _ hc.wr) hd (by omega_using [hd]))
    fun t ht => WP.block_nil ⟨ur.trans (ht.rest (by decide)), ht.mem.trans um, ?_⟩
  rw [ht.gpr, um]

theorem addInput32_ok (s : State) :
    WP isa (.block [.dp .add .r12 .r12 (.imm 32)]) s fun t => Rest [.r12] s t ∧ t.mem = s.mem ∧
      t.gpr .r12 = s.gpr .r12 + 32 := by
  refine wp_dp (op2_imm (by decide)) fun t ht => WP.block_nil ⟨ht.rest (by decide), ht.mem, ht.gpr⟩

end VG.Proof.Ed25519.Arm

end

end


/-! Merged from `Proof.Ed25519.Arm.VerifyBody`. -/

@[expose] public section

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

theorem verifyCombine_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (hl : AllLim s.mem b)
    (hd : env s.mem b 16 = Spec.Ed25519.d) :
    WP isa verifyCombine s fun t => AccKeep b s t ∧ AllLim t.mem b ∧
      point (env t.mem b) 0 1 2 3 = tablePoint s.mem b 8032 ∧
      point (env t.mem b) 4 5 6 7 = Spec.Ed25519.pointAdd (tablePoint s.mem b 7904)
        (point (env s.mem b) 0 1 2 3) := by
  refine WP.seq (WP.mono (fieldCode_ok copyPointToQOps hc hl) fun a ⟨ak, al, ae⟩ => ?_)
  obtain aq := (congrArg (fun e => point e 4 5 6 7) ae).trans (copyPointToQ_eval _)
  obtain ad : env a.mem b 16 = Spec.Ed25519.d := by rw [ae, copyPointToQ_d, hd]
  refine WP.seq (WP.mono (pointTableRead_ok (ak.ctx hc) al 7904 (by decide) (by decide))
    fun c ⟨ck, cl, cp, ch⟩ => ?_)
  obtain kc := (AccKeep.of_keep ak).trans ck
  obtain cq : point (env c.mem b) 4 5 6 7 = point (env s.mem b) 0 1 2 3 :=
    (point_congr _ _ _ _ (ch 4 (by decide)) (ch 5 (by decide)) (ch 6 (by decide)) (ch 7 (by decide))).trans aq
  obtain cp' := cp.trans (workspace_tablePoint ak.frame (by decide) (by decide))
  refine WP.seq (WP.mono (pointAdd_ok (kc.ctx hc) cl ((ch 16 (by decide)).trans ad))
    fun d ⟨dk, dl, dp, _⟩ => ?_)
  obtain kd := kc.trans (AccKeep.of_keep dk)
  obtain dp' := dp.trans (congrArg₂ Spec.Ed25519.pointAdd cp' cq)
  refine WP.seq (WP.mono (fieldCode_ok copyPointToQOps (kd.ctx hc) dl) fun e ⟨ek, el, ee⟩ => ?_)
  obtain ke := kd.trans (AccKeep.of_keep ek)
  obtain eqp := ((congrArg (fun f => point f 4 5 6 7) ee).trans (copyPointToQ_eval _)).trans dp'
  refine WP.mono (pointTableRead_ok (ke.ctx hc) el 8032 (by decide) (by decide))
    fun t ⟨tk, tl, tp, th⟩ => ?_
  exact ⟨ke.trans tk, tl, tp.trans (workspace_tablePoint ke.frame (by decide) (by decide)),
    (point_congr _ _ _ _ (th 4 (by decide)) (th 5 (by decide)) (th 6 (by decide)) (th 7 (by decide))).trans eqp⟩

end VG.Proof.Ed25519.Arm
end

/-! The right side reads all 512 challenge bits before the strict equation. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifyRhs_ok {b pk sig challenge : BitVec 32} {s : State}
    (hc : VerifyContext b pk sig challenge s) (hl : AllLim s.mem b) :
    WP isa verifyRhs s fun t => VerifyKeep b s t ∧ AllLim t.mem b ∧
      t.gpr .r9 = BitVec.ofNat 32 (Spec.Ed25519.pointEqual (tablePoint s.mem b 8032)
        (Spec.Ed25519.pointAdd (tablePoint s.mem b 7904)
          (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr challenge) 64))
            (tablePoint s.mem b 7776)))).toNat := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (pointTableRead_ok hc.ctx hl 7776 (by decide) (by decide)) fun a ⟨ak, al, ap, _⟩ => ?_
  refine WP.mono (loadHeader_ok (ak.ctx hc.ctx) 8168 (by decide)) fun c ⟨cr, cm, cp⟩ => ?_
  obtain kc := ak.trans (AccKeep.of_rest cr (by decide) cm)
  obtain cpk : PointKeep b s c := PointKeep.of_mul (MulKeep.of_powers (PowersKeep.of_acc kc))
  obtain cc := hc.keep (VerifyKeep.of_acc kc)
  obtain cp' : c.gpr .r12 = challenge := cp.trans (hc.keep (VerifyKeep.of_acc ak)).challengeHeader
  obtain capp : point (env c.mem b) 0 1 2 3 = tablePoint s.mem b 7776 :=
    (congrArg (fun m => point (env m b) 0 1 2 3) cm).trans ap
  obtain ci := cc.challengeInput.prefix (n := 32) (by decide)
  refine WP.seq (WP.mono (pointFromScalar_ok cc.ctx (cm ▸ al) cp' 16 (by decide) (by decide)
    ci.fit ci.readable ci.separate) fun d ⟨dk, dl, dd, dp⟩ => ?_)
  obtain kd := cpk.trans dk
  obtain dp' : point (env d.mem b) 0 1 2 3 = Spec.Ed25519.pointMul
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr challenge) 64)) (tablePoint s.mem b 7776) := by
    rw [show 2 * 16 = 32 from rfl, decodeLE_low cc.challengeTop,
      hc.challengeInput.bytes (VerifyKeep.of_acc kc), capp] at dp
    exact dp
  refine WP.seq (WP.mono (verifyCombine_ok (kd.ctx hc.ctx) dl dd) fun e ⟨ek, el, ep, eqp⟩ => ?_)
  obtain ep' := ep.trans (kd.table (by decide) (by decide))
  obtain eqp' := eqp.trans (congrArg₂ Spec.Ed25519.pointAdd (kd.table (by decide) (by decide)) dp')
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
    (hc : VerifyContext b pk sig challenge s) (hl : AllLim s.mem b) :
    WP isa verifyLhs s fun t => VerifyKeep b s t ∧ AllLim t.mem b ∧
      tablePoint t.mem b 8032 = Spec.Ed25519.pointMul
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr (sig + 32)) 32)) Spec.Ed25519.basePoint ∧
      tablePoint t.mem b 7776 = tablePoint s.mem b 7776 ∧
      tablePoint t.mem b 7904 = tablePoint s.mem b 7904 := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadHeader_ok hc.ctx 8164 (by decide)) fun a ⟨ar, am, ap⟩ => ?_
  refine WP.mono (addInput32_ok a) fun c ⟨cr, cm, cp⟩ => ?_
  obtain kc : PointKeep b s c := ⟨(ar.mono (by decide)).trans (cr.mono (by decide)), by
    rw [cm, am]; exact Frame.refl _ _⟩
  refine WP.seq (WP.mono (fieldCodeFree_ok (constPointOps Spec.Ed25519.basePoint) rfl (kc.ctx hc.ctx)
    (by rw [cm, am]; exact hl)) fun d ⟨dk, dr, _, dl, de⟩ => ?_)
  obtain kd := kc.trans (PointKeep.of_keep dk)
  obtain dc := hc.keep (VerifyKeep.of_point kd)
  have di := dc.sigInput.suffix32
  obtain dp : d.gpr .r12 = sig + 32 := by rw [dr.gpr _ (by decide), cp, ap, hc.sigHeader]
  obtain dpoint : point (env d.mem b) 0 1 2 3 = Spec.Ed25519.basePoint :=
    (congrArg (fun e => point e 0 1 2 3) de).trans (constPoint_eval _ _)
  refine WP.seq (WP.mono (pointFromScalar_ok dc.ctx dl dp 16 (by decide) (by decide)
    di.fit di.readable di.separate) fun e ⟨ek, el, _, ep⟩ => ?_)
  obtain ke := kd.trans ek
  obtain ep' : point (env e.mem b) 0 1 2 3 = Spec.Ed25519.pointMul
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr (sig + 32)) 32)) Spec.Ed25519.basePoint := by
    rw [(hc.sigInput.suffix32).bytes (VerifyKeep.of_point kd), dpoint] at ep
    exact ep
  refine WP.mono (pointTableWrite_ok (ke.ctx hc.ctx) el 8032 (by decide) (by decide))
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
    (hc : VerifyContext b pk sig challenge s) (hl : AllLim s.mem b) :
    WP isa verifyEquationPoints s fun t => VerifyKeep b s t ∧ AllLim t.mem b ∧
      t.gpr .r9 = BitVec.ofNat 32 (equationResult s.mem sig challenge
        (tablePoint s.mem b 7776) (tablePoint s.mem b 7904)).toNat := by
  refine WP.seq (WP.mono (verifyLhs_ok hc hl) fun u ⟨uk, ul, up, ua, ur⟩ => ?_)
  refine WP.mono (verifyRhs_ok (hc.keep uk) ul) fun t ⟨tk, tl, tv⟩ => ?_
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
  | some r => equationResult m sig challenge a r

theorem equationResult_keep {b pk sig challenge : BitVec 32} {s t : State}
    (hc : VerifyContext b pk sig challenge s) (hk : VerifyKeep b s t) (a r : Spec.Ed25519.Point) :
    equationResult t.mem sig challenge a r = equationResult s.mem sig challenge a r := by
  unfold equationResult
  rw [(hc.sigInput.suffix32).bytes hk, hc.challengeInput.bytes hk]

theorem DecodeKeep.table {b : BitVec 32} {s t : State} (h : DecodeKeep b s t) {d : Nat}
    (hd : 1632 ≤ d) (hn : d + 128 ≤ 8192) : tablePoint t.mem b d = tablePoint s.mem b d := by
  refine tablePoint_frame h.frame fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by decide)

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
  | some a => equationWithR m sig challenge a

theorem equationWithR_keep {b pk sig challenge : BitVec 32} {s t : State}
    (hc : VerifyContext b pk sig challenge s) (hk : VerifyKeep b s t) (a : Spec.Ed25519.Point) :
    equationWithR t.mem sig challenge a = equationWithR s.mem sig challenge a := by
  unfold equationWithR
  rw [(hc.sigInput.prefix (n := 32) (by decide)).bytes hk]
  split
  · rfl
  · exact equationResult_keep hc hk _ _

theorem decodedEquation_keep {b pk sig challenge : BitVec 32} {s t : State}
    (hc : VerifyContext b pk sig challenge s) (hk : VerifyKeep b s t) :
    decodedEquation t.mem pk sig challenge = decodedEquation s.mem pk sig challenge := by
  unfold decodedEquation
  rw [hc.pkInput.bytes hk]
  split
  · rfl
  · exact equationWithR_keep hc hk _

/-! ### `A` and `R` decoded by one loop

`decodeBoth` decodes `A`, then `R`, with one copy of the decoding: the encoding's pointer, the
table entry's offset and the AND of the results are words of the working space (`DPTR`,
`DTAB`, `DOK`, `DecAt`). -/

/-- The pointer of input `k`: `A`'s, then `R`'s. -/
def inPtr (pk sig : BitVec 32) (k : Nat) : BitVec 32 := if k = 0 then pk else sig

/-- The decoding of input `k`. -/
def inPoint (m : Mem) (pk sig : BitVec 32) (k : Nat) : Option Spec.Ed25519.Point :=
  Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m (State.addr (inPtr pk sig k)) 32)

/-- The AND of the first `k` decodings' successes. -/
def decOk (m : Mem) (pk sig : BitVec 32) : Nat → Bool
  | 0 => true
  | k + 1 => decOk m pk sig k && (inPoint m pk sig k).isSome

theorem decOk_succ (m : Mem) (pk sig : BitVec 32) (k : Nat) :
    decOk m pk sig (k + 1) = (decOk m pk sig k && (inPoint m pk sig k).isSome) := rfl

theorem decOk_two (m : Mem) (pk sig : BitVec 32) :
    decOk m pk sig 2 = ((inPoint m pk sig 0).isSome && (inPoint m pk sig 1).isSome) := by
  simp only [decOk, Bool.true_and]

/-- A word of the working space. -/
abbrev lw (m : Mem) (b : BitVec 32) (d : Nat) : BitVec 32 := m.readW (State.addr b + BitVec.ofNat 64 d) 32

/-- Before the decoding `k` (`A`'s, then `R`'s), from the state `s₀` before the loop. -/
structure DecAt (s₀ : State) (b pk sig : BitVec 32) (k : Nat) (s : State) : Prop where
  keep : VerifyKeep b s₀ s
  lim : AllLim s.mem b
  ptr : k < 2 → lw s.mem b DPTR = inPtr pk sig k
  tab : lw s.mem b DTAB = BitVec.ofNat 32 (7776 + 128 * k)
  ok : lw s.mem b DOK = BitVec.ofNat 32 (decOk s₀.mem pk sig k).toNat
  pts : ∀ j < k, ∀ p, inPoint s₀.mem pk sig j = some p → tablePoint s.mem b (7776 + 128 * j) = p

theorem flag_and (x y : Bool) :
    BitVec.ofNat 32 x.toNat &&& BitVec.ofNat 32 y.toNat = BitVec.ofNat 32 (x && y).toNat := by
  cases x <;> cases y <;> rfl

theorem ldrLow_ok {b : BitVec 32} {s : State} (hc : Ctx b s) {d : Nat} (hd : d + 4 ≤ 64) (r : Reg)
    {is : List Instr} {Q : State → Prop} (k : ∀ t, Upd s t r (lw s.mem b d) → WP isa (.block is) t Q) :
    WP isa (.block (.ldr r .r0 d :: is)) s Q :=
  wp_ldr (a := State.addr b + BitVec.ofNat 64 d) (by omega_arith) (by rw [hc.r0]; exact hc.ptr_addr (by omega_arith))
    (in_base (List.mem_append_right _ hc.wr) (by omega_arith) (by omega_arith)) k

theorem strLow_ok {b : BitVec 32} {s : State} (hc : Ctx b s) {d : Nat} (hd : d + 4 ≤ 64) (r : Reg)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Mupd s t (s.mem.writeW (State.addr b + BitVec.ofNat 64 d) (s.gpr r)) → WP isa (.block is) t Q) :
    WP isa (.block (.str r .r0 d :: is)) s Q :=
  wp_str (a := State.addr b + BitVec.ofNat 64 d) (by omega_arith) (by rw [hc.r0]; exact hc.ptr_addr (by omega_arith))
    (in_base hc.wr (by omega_arith) (by omega_arith)) k

/-- A word after a store to another word, or to it. -/
theorem lw_write (m : Mem) (b : BitVec 32) (w : BitVec 32) {d e : Nat} (hd : d + 4 ≤ 8192) (he : e + 4 ≤ 8192)
    (h : d = e ∨ d + 4 ≤ e ∨ e + 4 ≤ d) :
    lw (m.writeW (State.addr b + BitVec.ofNat 64 e) w) b d = if d = e then w else lw m b d := by
  rcases h with rfl | h
  · rw [ite_eq_left rfl]; exact Mem.readW_writeW_self32 _ _ _
  · rw [ite_eq_right (by omega_arith)]
    exact Mem.readW_writeW_sep (Offset.sep _ h (by omega_arith) (by omega_arith)) (by decide)

/-- A word outside a frame of one range. -/
theorem lw_frame {m m' : Mem} {b : BitVec 32} {o n d : Nat}
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, n⟩] m m') (h : d + 4 ≤ o ∨ o + n ≤ d)
    (hn : o + n ≤ 8192) (hd : d + 4 ≤ 8192) : lw m' b d = lw m b d :=
  hf.readW (Region.contains_self _ _) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ h (by omega_arith) (by omega_arith)) (by decide)

/-- The stores of the loop's words, between bytes 32 and 44. -/
theorem loopFrame_write {m m' : Mem} {b : BitVec 32} (hf : Frame [⟨State.addr b + BitVec.ofNat 64 32, 12⟩] m m')
    {d : Nat} (hd : 32 ≤ d) (hd' : d + 4 ≤ 44) (w : BitVec 32) :
    Frame [⟨State.addr b + BitVec.ofNat 64 32, 12⟩] m (m'.writeW (State.addr b + BitVec.ofNat 64 d) w) :=
  hf.writeW (List.mem_singleton_self _) _ (Offset.contains _ hd hd' (by decide))

/-- The input `k`'s place, from the context. -/
theorem VerifyContext.input {b pk sig challenge : BitVec 32} {s : State}
    (hc : VerifyContext b pk sig challenge s) {k : Nat} (hk : k < 2) : VerifyInput b (inPtr pk sig k) 32 s := by
  rcases (by omega_arith : k = 0 ∨ k = 1) with rfl | rfl
  · exact hc.pkInput
  · exact hc.sigInput.prefix (by decide)

theorem decodeStart_ok {b pk sig challenge : BitVec 32} {s : State}
    (hc : VerifyContext b pk sig challenge s) (hl : AllLim s.mem b) :
    WP isa (.block decodeStart) s (DecAt s b pk sig 0) := by
  unfold decodeStart
  rw [WP.block_append_iff]
  refine WP.mono (loadHeader_ok hc.ctx 8160 (by decide)) fun u ⟨ur, um, up⟩ => ?_
  obtain cu : Ctx b u := hc.ctx.of_rest ur (by decide)
  refine strLow_ok cu (d := DPTR) (by decide) .r12 fun u1 h1 => ?_
  obtain c1 : Ctx b u1 := cu.of_rest (h1.rest []) (by decide)
  refine wp_movw fun u2 h2 => ?_
  obtain c2 : Ctx b u2 := c1.of_rest (h2.rest (ws := [.r3]) (by decide)) (by decide)
  refine strLow_ok c2 (d := DTAB) (by decide) .r3 fun u3 h3 => ?_
  obtain c3 : Ctx b u3 := c2.of_rest (h3.rest []) (by decide)
  refine wp_mov (op2_imm (by decide)) fun u4 h4 => ?_
  obtain c4 : Ctx b u4 := c3.of_rest (h4.rest (ws := [.r3]) (by decide)) (by decide)
  refine strLow_ok c4 (d := DOK) (by decide) .r3 fun t ht => WP.block_nil ?_
  obtain pk' : u.gpr .r12 = pk := up.trans hc.pkHeader
  obtain mt : t.mem = ((s.mem.writeW (State.addr b + BitVec.ofNat 64 DPTR) pk).writeW
      (State.addr b + BitVec.ofNat 64 DTAB) ((7776 : BitVec 16).setWidth 32)).writeW
      (State.addr b + BitVec.ofNat 64 DOK) (1 : BitVec 32) := by
    rw [ht.mem, h4.gpr, h4.mem, h3.mem, h2.gpr, h2.mem, h1.mem, pk', um]
  obtain hf : Frame [⟨State.addr b + BitVec.ofNat 64 32, 12⟩] s.mem t.mem := by
    rw [mt]
    exact loopFrame_write (loopFrame_write (loopFrame_write (Frame.refl _ _) (by decide) (by decide) _)
      (by decide) (by decide) _) (by decide) (by decide) _
  obtain rt : Rest [.r12, .r3] s t :=
    (((((ur.mono (by decide)).trans (h1.rest _)).trans (h2.rest (by decide))).trans (h3.rest _)).trans
      (h4.rest (by decide))).trans (ht.rest _)
  refine ⟨VerifyKeep.of_small rt (by decide) hf (by decide) (by decide), smallFrame_lim hf (by decide) hl,
    fun _ => ?_, ?_, ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  · rw [mt, lw_write _ _ _ (by decide) (by decide) (by decide), ite_eq_right (by decide),
      lw_write _ _ _ (by decide) (by decide) (by decide), ite_eq_right (by decide),
      lw_write _ _ _ (by decide) (by decide) (by decide), ite_eq_left rfl]
    rfl
  · rw [mt, lw_write _ _ _ (by decide) (by decide) (by decide), ite_eq_right (by decide),
      lw_write _ _ _ (by decide) (by decide) (by decide), ite_eq_left rfl]
    decide
  · rw [mt, lw_write _ _ _ (by decide) (by decide) (by decide), ite_eq_left rfl]
    rfl

theorem decodeNext_eq : decodeNext = ([.ldr .r3 .r0 DOK, .dp .and .r3 .r3 (.reg .r9), .str .r3 .r0 DOK,
    .ldr .r12 .r0 DTAB, .dp .add .r12 .r0 (.reg .r12)] : List Instr) ++ (pointToTable ++ (loadHeader 8164 ++
    ([.str .r12 .r0 DPTR, .ldr .r3 .r0 DTAB, .dp .add .r3 .r3 (.imm 128), .str .r3 .r0 DTAB,
      .movw .r2 8032, .cmp .r3 (.reg .r2)] : List Instr))) := by
  simp only [decodeNext, List.append_assoc]

/-- The result ANDed into `DOK`, the point to the table at `[DTAB]` (`o = 7776 + 128 k`), `R`'s
pointer and the next entry. -/
theorem decodeNext_ok {b pk sig challenge : BitVec 32} {s : State} (hc : VerifyContext b pk sig challenge s)
    (hl : AllLim s.mem b) {k : Nat} (hk : k < 2) {p : Option Spec.Ed25519.Point}
    (hflag : s.gpr .r9 = BitVec.ofNat 32 p.isSome.toNat)
    (hpt : ∀ q, p = some q → point (env s.mem b) 0 1 2 3 = q)
    (htab : lw s.mem b DTAB = BitVec.ofNat 32 (7776 + 128 * k)) :
    WP isa (.block decodeNext) s fun t => VerifyKeep b s t ∧ AllLim t.mem b ∧
      lw t.mem b DOK = (lw s.mem b DOK &&& BitVec.ofNat 32 p.isSome.toNat) ∧
      lw t.mem b DPTR = sig ∧
      lw t.mem b DTAB = BitVec.ofNat 32 (7776 + 128 * (k + 1)) ∧
      (∀ q, p = some q → tablePoint t.mem b (7776 + 128 * k) = q) ∧
      (∀ o, 1632 ≤ o → o + 128 ≤ 7776 + 128 * k → tablePoint t.mem b o = tablePoint s.mem b o) ∧
      t.z = decide (k = 1) := by
  have cs := hc.ctx
  obtain ho : 1632 ≤ 7776 + 128 * k := by omega_arith
  obtain hn : 7776 + 128 * k + 128 ≤ 8192 := by omega_arith
  rw [decodeNext_eq, WP.block_append_iff]
  refine ldrLow_ok cs (d := DOK) (by decide) .r3 fun u1 h1 => ?_
  obtain c1 : Ctx b u1 := cs.of_rest (h1.rest (ws := [.r3]) (by decide)) (by decide)
  refine wp_dp (op2_reg _ _) fun u2 h2 => ?_
  obtain c2 : Ctx b u2 := c1.of_rest (h2.rest (ws := [.r3]) (by decide)) (by decide)
  refine strLow_ok c2 (d := DOK) (by decide) .r3 fun u3 h3 => ?_
  obtain c3 : Ctx b u3 := c2.of_rest (h3.rest []) (by decide)
  refine ldrLow_ok c3 (d := DTAB) (by decide) .r12 fun u4 h4 => ?_
  obtain c4 : Ctx b u4 := c3.of_rest (h4.rest (ws := [.r12]) (by decide)) (by decide)
  refine wp_dp (op2_reg _ _) fun u5 h5 => WP.block_nil ?_
  obtain c5 : Ctx b u5 := c4.of_rest (h5.rest (ws := [.r12]) (by decide)) (by decide)
  obtain dok : u2.gpr .r3 = lw s.mem b DOK &&& BitVec.ofNat 32 p.isSome.toNat := by
    rw [h2.gpr]
    change u1.gpr .r3 &&& u1.gpr .r9 = _
    rw [h1.gpr, h1.other _ (by decide), hflag]
  obtain m3 : u3.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 DOK) (lw s.mem b DOK &&& BitVec.ofNat 32 p.isSome.toNat) := by
    rw [h3.mem, h2.mem, h1.mem, dok]
  obtain m5 : u5.mem = u3.mem := by rw [h5.mem, h4.mem]
  obtain f5 : Frame [⟨State.addr b + BitVec.ofNat 64 32, 12⟩] s.mem u5.mem := by
    rw [m5, m3]; exact loopFrame_write (Frame.refl _ _) (by decide) (by decide) _
  obtain l5 : AllLim u5.mem b := smallFrame_lim f5 (by decide) hl
  obtain e5 : env u5.mem b = env s.mem b := smallFrame_env f5 (by decide)
  obtain r5 : u5.gpr .r12 = b + BitVec.ofNat 32 (7776 + 128 * k) := by
    rw [h5.gpr]
    change u4.gpr .r0 + u4.gpr .r12 = _
    rw [h4.gpr, h4.other _ (by decide), c3.r0, m3, lw_write _ _ _ (by decide) (by decide) (by decide),
      ite_eq_right (by decide), htab]
  rw [WP.block_append_iff]
  refine WP.mono (pointToTable_ok c5 l5 r5 ho hn) fun x ⟨xp, xk⟩ => ?_
  obtain cx : Ctx b x := xk.ctx c5
  obtain lx : AllLim x.mem b := xk.lim ho hn l5
  obtain kx : VerifyKeep b s x :=
    (VerifyKeep.of_small (((((h1.rest (ws := [.r3, .r12]) (by decide)).trans (h2.rest (by decide))).trans
      (h3.rest _)).trans (h4.rest (by decide))).trans (h5.rest (by decide))) (by decide) f5 (by decide) (by decide)).trans
      (VerifyKeep.of_powers ⟨xk.rest.mono (by decide), TableFrame.table xk.frame⟩ (by omega_arith) (by omega_arith))
  rw [WP.block_append_iff]
  refine WP.mono (loadHeader_ok cx 8164 (by decide)) fun y ⟨yr, ym, yp⟩ => ?_
  obtain cy : Ctx b y := cx.of_rest yr (by decide)
  obtain sig' : y.gpr .r12 = sig := by rw [yp, kx.header 8164 (by decide) (by decide)]; exact hc.sigHeader
  refine strLow_ok cy (d := DPTR) (by decide) .r12 fun y1 g1 => ?_
  obtain d1 : Ctx b y1 := cy.of_rest (g1.rest []) (by decide)
  refine ldrLow_ok d1 (d := DTAB) (by decide) .r3 fun y2 g2 => ?_
  obtain d2 : Ctx b y2 := d1.of_rest (g2.rest (ws := [.r3]) (by decide)) (by decide)
  refine wp_dp (op2_imm (by decide)) fun y3 g3 => ?_
  obtain d3 : Ctx b y3 := d2.of_rest (g3.rest (ws := [.r3]) (by decide)) (by decide)
  refine strLow_ok d3 (d := DTAB) (by decide) .r3 fun y4 g4 => ?_
  obtain d4 : Ctx b y4 := d3.of_rest (g4.rest []) (by decide)
  refine wp_movw fun y5 g5 => wp_cmp (op2_reg _ _) fun t ht hz => WP.block_nil ?_
  -- What the stores leave.
  obtain lwx : ∀ d, d + 4 ≤ 64 → lw x.mem b d = lw u5.mem b d := fun d hd =>
    lw_frame xk.frame (Or.inl (by omega_arith)) hn (by omega_arith)
  obtain tab3 : y3.gpr .r3 = BitVec.ofNat 32 (7776 + 128 * (k + 1)) := by
    rw [g3.gpr]
    change y2.gpr .r3 + (128 : BitVec 32) = _
    rw [g2.gpr, g1.mem, ym, lw_write _ _ _ (by decide) (by decide) (by decide), ite_eq_right (by decide),
      lwx DTAB (by decide), m5, m3, lw_write _ _ _ (by decide) (by decide) (by decide), ite_eq_right (by decide), htab]
    rcases (by omega_arith : k = 0 ∨ k = 1) with rfl | rfl <;> decide
  obtain mt : t.mem = (x.mem.writeW (State.addr b + BitVec.ofNat 64 DPTR) sig).writeW
      (State.addr b + BitVec.ofNat 64 DTAB) (BitVec.ofNat 32 (7776 + 128 * (k + 1))) := by
    rw [ht.mem, g5.mem, g4.mem, tab3, g3.mem, g2.mem, g1.mem, sig', ym]
  obtain ft : Frame [⟨State.addr b + BitVec.ofNat 64 32, 12⟩] x.mem t.mem := by
    rw [mt]; exact loopFrame_write (loopFrame_write (Frame.refl _ _) (by decide) (by decide) _) (by decide) (by decide) _
  obtain rt : Rest [.r12, .r3, .r2] x t :=
    ((((((yr.mono (by decide)).trans (g1.rest _)).trans (g2.rest (by decide))).trans (g3.rest (by decide))).trans
      (g4.rest _)).trans (g5.rest (by decide))).trans (ht.rest _)
  obtain tpt : ∀ o, o + 128 ≤ 8192 → 1632 ≤ o → tablePoint t.mem b o = tablePoint x.mem b o := fun o h1 h2 =>
    tablePoint_frame ft fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (Or.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  refine ⟨kx.trans (VerifyKeep.of_small rt (by decide) ft (by decide) (by decide)), smallFrame_lim ft (by decide) lx,
    ?_, ?_, ?_, fun q hq => ?_, fun o h1 h2 => ?_, ?_⟩
  · rw [mt, lw_write _ _ _ (by decide) (by decide) (by decide), ite_eq_right (by decide),
      lw_write _ _ _ (by decide) (by decide) (by decide), ite_eq_right (by decide), lwx DOK (by decide), m5, m3,
      lw_write _ _ _ (by decide) (by decide) (by decide), ite_eq_left rfl]
  · rw [mt, lw_write _ _ _ (by decide) (by decide) (by decide), ite_eq_right (by decide),
      lw_write _ _ _ (by decide) (by decide) (by decide), ite_eq_left rfl]
  · rw [mt, lw_write _ _ _ (by decide) (by decide) (by decide), ite_eq_left rfl]
  · rw [tpt _ hn ho, xp, e5]; exact hpt q hq
  · rw [tpt _ (by omega_arith) h1]
    refine (tablePoint_frame xk.frame fun r hr => ?_).trans ?_
    · rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (Or.inl h2) (by omega_arith) (by omega_arith)
    · exact tablePoint_frame f5 fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (Or.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  · rw [hz, g5.other _ (by decide), g5.gpr, g4.gpr, tab3]
    rcases (by omega_arith : k = 0 ∨ k = 1) with rfl | rfl <;> decide

theorem decodeFlagA {b : BitVec 32} {p p' : Option Spec.Ed25519.Point} {s : State}
    (h : DecodeResult b p s) (he : p = p') : s.gpr .r9 = BitVec.ofNat 32 p'.isSome.toNat := by
  subst he
  cases p with
  | none => exact h
  | some q => exact h.1

theorem decodePtA {b : BitVec 32} {p p' : Option Spec.Ed25519.Point} {s : State}
    (h : DecodeResult b p s) (he : p = p') : ∀ q, p' = some q → point (env s.mem b) 0 1 2 3 = q := by
  subst he
  intro q hq
  subst hq
  exact h.2

/-- One iteration: the input `k` decoded, its result ANDed into `DOK`, and its point in the
table. -/
theorem decodeBody_ok {s₀ : State} {b pk sig challenge : BitVec 32}
    (hc : VerifyContext b pk sig challenge s₀) {k : Nat} (hk : k < 2) {s : State}
    (hs : DecAt s₀ b pk sig k s) :
    WP isa decodeBody s fun t => DecAt s₀ b pk sig (k + 1) t ∧ t.z = decide (k = 1) := by
  obtain cs := (hc.keep hs.keep).ctx
  refine WP.seq (ldrLow_ok cs (d := DPTR) (by decide) .r12 fun u hu => WP.block_nil ?_)
  obtain ku : VerifyKeep b s₀ u := hs.keep.trans (VerifyKeep.of_rest (hu.rest (ws := [.r12]) (by decide)) (by decide) hu.mem)
  obtain hcu := hc.keep ku
  obtain hi := hcu.input hk
  obtain up : u.gpr .r12 = inPtr pk sig k := by rw [hu.gpr]; exact hs.ptr hk
  refine WP.seq (WP.mono (pointDecode_ok hcu.ctx (hu.mem ▸ hs.lim) up hi.fit hi.readable hi.separate) fun v hv => ?_)
  have vk := hv.1
  obtain kv := ku.trans (VerifyKeep.of_decode vk)
  obtain hbytes : Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt u.mem (State.addr (inPtr pk sig k)) 32) =
      inPoint s₀.mem pk sig k := congrArg Spec.Ed25519.decodePoint ((hc.input hk).bytes ku)
  obtain vt : lw v.mem b DTAB = BitVec.ofNat 32 (7776 + 128 * k) := by
    rw [show lw v.mem b DTAB = lw u.mem b DTAB from (vk.frame.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (Or.inl (by decide)) (by decide) (by decide)) (by decide)),
      hu.mem]
    exact hs.tab
  -- `with_reducible`: unfolding `DecodeResult` would evaluate the decoding.
  obtain vflag : v.gpr .r9 = BitVec.ofNat 32 (inPoint s₀.mem pk sig k).isSome.toNat := by
    with_reducible exact decodeFlagA hv.2.2 hbytes
  obtain vpt : ∀ q, inPoint s₀.mem pk sig k = some q → point (env v.mem b) 0 1 2 3 = q := by
    with_reducible exact decodePtA hv.2.2 hbytes
  refine WP.mono (decodeNext_ok (hc.keep kv) hv.2.1 hk vflag vpt vt)
    fun t hn => ⟨⟨kv.trans hn.1, hn.2.1, fun hk1 => ?_, hn.2.2.2.2.1, ?_, fun j hj q hq => ?_⟩, hn.2.2.2.2.2.2.2⟩
  · obtain rfl : k = 0 := by omega_arith
    exact hn.2.2.2.1
  · have vok : lw v.mem b DOK = lw s.mem b DOK := by
      rw [show lw v.mem b DOK = lw u.mem b DOK from (vk.frame.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact Offset.disjoint _ (Or.inl (by decide)) (by decide) (by decide)) (by decide)),
        hu.mem]
    rw [hn.2.2.1, vok, hs.ok, flag_and, decOk_succ]
  · rcases (by omega_arith : j = k ∨ j < k) with rfl | hj'
    · exact hn.2.2.2.2.2.1 q hq
    · rw [hn.2.2.2.2.2.2.1 _ (by omega_arith) (by omega_arith), vk.table (by omega_arith) (by omega_arith), hu.mem]
      exact hs.pts j hj' q hq

/-- `A` and `R` decoded, by the loop. -/
theorem decodeBoth_ok {b pk sig challenge : BitVec 32} {s : State}
    (hc : VerifyContext b pk sig challenge s) (hl : AllLim s.mem b) :
    WP isa decodeBoth s (DecAt s b pk sig 2) := by
  refine WP.seq (WP.mono (decodeStart_ok hc hl) fun a ha => ?_)
  refine WP.loop (M := isa) (Inv := fun m t => ∃ k, k + m = 2 ∧ k < 2 ∧ DecAt s b pk sig k t) ?_ 2 a
    ⟨0, rfl, by decide, ha⟩
  intro m u ⟨k, hkm, hk, hu⟩
  refine WP.mono (decodeBody_ok hc hk hu) fun t ⟨ht, zt⟩ => ?_
  rcases (by omega_arith : k = 0 ∨ k = 1) with rfl | rfl
  · exact .inr ⟨by show some (!t.z) = _; rw [zt]; rfl, 1, by omega_arith, 1, rfl, by decide, ht⟩
  · exact .inl ⟨by show some (!t.z) = _; rw [zt]; rfl, ht⟩

/-- Both decoded, and the equation if both are points. -/
theorem verifyDecode_ok {b pk sig challenge : BitVec 32} {s : State}
    (hc : VerifyContext b pk sig challenge s) (hl : AllLim s.mem b) :
    WP isa verifyDecode s fun t => VerifyKeep b s t ∧
      t.gpr .r9 = BitVec.ofNat 32 (decodedEquation s.mem pk sig challenge).toNat := by
  refine WP.seq (WP.mono (decodeBoth_ok hc hl) fun a ha => ?_)
  obtain ca := (hc.keep ha.keep).ctx
  refine WP.seq (ldrLow_ok ca (d := DOK) (by decide) .r9 fun c hc' => wp_cmp (op2_imm (by decide)) fun d hd hz =>
    WP.block_nil ?_)
  obtain kd : VerifyKeep b s d := ha.keep.trans (VerifyKeep.of_rest ((hc'.rest (ws := [.r9]) (by decide)).trans
    (hd.rest _)) (by decide) (by rw [hd.mem, hc'.mem]))
  obtain md : d.mem = a.mem := by rw [hd.mem, hc'.mem]
  apply WP.ite (decOk s.mem pk sig 2) (by
    show some (!d.z) = _
    rw [hz]
    rw [hc'.gpr, ha.ok]
    cases decOk s.mem pk sig 2 <;> rfl)
  · intro hok
    rw [decOk_two, Bool.and_eq_true] at hok
    obtain ⟨a0, ha0⟩ := Option.isSome_iff_exists.mp hok.1
    obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.mp hok.2
    obtain tA : tablePoint d.mem b 7776 = a0 := by rw [md]; exact ha.pts 0 (by decide) a0 ha0
    obtain tR : tablePoint d.mem b 7904 = r0 := by rw [md]; exact ha.pts 1 (by decide) r0 hr0
    refine WP.mono (verifyEquationPoints_ok (hc.keep kd) (by rw [md]; exact ha.lim)) fun t ⟨tk, _, tv⟩ =>
      ⟨kd.trans tk, ?_⟩
    rw [tv, tA, tR, equationResult_keep hc kd]
    have h0 : Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem (State.addr pk) 32) = some a0 := ha0
    have h1 : Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem (State.addr sig) 32) = some r0 := hr0
    simp only [decodedEquation, equationWithR, h0, h1]
  · intro hok
    refine WP.mono (recoverInvalid_ok d b) fun t ⟨tk, _, tv⟩ => ⟨kd.trans (VerifyKeep.of_keep tk), ?_⟩
    rw [decOk_two] at hok
    change t.gpr .r9 = 0 at tv
    rw [tv]
    have h0 : inPoint s.mem pk sig 0 = Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem (State.addr pk) 32) := rfl
    have h1 : inPoint s.mem pk sig 1 = Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem (State.addr sig) 32) := rfl
    cases e0 : Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem (State.addr pk) 32) with
    | none => simp only [decodedEquation, e0]; rfl
    | some a0 =>
      cases e1 : Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem (State.addr sig) 32) with
      | none => simp only [decodedEquation, equationWithR, e0, e1]; rfl
      | some r0 => rw [h0, h1, e0, e1] at hok; simp at hok

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.VerifyScalar`. -/
section
/-! The signature's scalar is checked canonically, before point decoding. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifyScalar_ok {b pk sig challenge : BitVec 32} {s : State}
    (hc : VerifyContext b pk sig challenge s) :
    WP isa (.block verifyScalar) s fun t => VerifyKeep b s t ∧
      t.z = decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr (sig + 32)) 32) < Spec.Ed25519.L) := by
  unfold verifyScalar
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (loadHeader_ok hc.ctx 8164 (by decide)) fun a ⟨ar, am, ap⟩ => ?_
  obtain ak : VerifyKeep b s a := VerifyKeep.of_rest ar (by decide) am
  refine WP.mono (addInput32_ok a) fun c ⟨cr, cm, cp⟩ => ?_
  obtain ck : VerifyKeep b s c := ak.trans (VerifyKeep.of_rest cr (by decide) cm)
  obtain ci := (hc.keep ck).sigInput.suffix32
  obtain cptr : c.gpr .r12 = sig + 32 := by rw [cp, ap, hc.sigHeader]
  refine WP.mono (unpackField_ok (ck.ctx hc.ctx) (o := SR) (src := 0) (by decide) (by decide)
    cptr (by simpa using ci.fit) (by simpa using ci.readable)
    (by simpa using ci.separate.sub_right (Offset.sub_base _ (by decide : SR + 64 ≤ 8192))))
    fun d ⟨dr, df, dl, dv⟩ => ?_
  obtain dk : VerifyKeep b s d := ck.trans (VerifyKeep.of_small dr (by decide) df (by decide) (by decide))
  obtain val : V d.mem (State.addr b) SR =
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr (sig + 32)) 32) := by
    obtain dv' : V d.mem (State.addr b) SR = packedV c.mem (State.addr (sig + 32)) := by simpa only [BitVec.add_zero] using dv
    rw [dv', ← scalar_packed_decode, (hc.sigInput.suffix32).bytes ck]
  refine WP.mono (scalarCompare_ok (dk.ctx hc.ctx) dl) fun e ⟨er, ef, ev⟩ => ?_
  obtain ek := dk.trans (VerifyKeep.of_small er (by decide) ef (by decide) (by decide))
  refine wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ⟨
    ek.trans (VerifyKeep.of_rest (ht.rest []) (by decide) ht.mem), ?_⟩
  rw [hz]
  change decide (e.gpr .r5 - (0 : BitVec 32) = 0) = _
  obtain es : e.gpr .r5 - (0 : BitVec 32) = e.gpr .r5 := BitVec.sub_zero _
  rw [es]
  obtain e0 : (e.gpr .r5 = 0) ↔ (e.gpr .r5).toNat = 0 := by
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
        decodedEquation m pk sig challenge) := by
  obtain ep : State.addr (sig + (32 : BitVec 32)) = State.addr sig + BitVec.ofNat 64 32 := addr_add (k := 32) (by omega_arith)
  rw [Spec.Ed25519.verifyEquation]
  simp only [bytesAt_length, bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ite_false,
    signatureBytes_take, signatureBytes_drop, ← ep]
  unfold decodedEquation equationWithR equationResult
  cases Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m (State.addr pk) 32) <;>
    cases Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m (State.addr sig) 32) <;>
    simp only [Bool.and_false]

theorem verifyBody_ok {b pk sig challenge : BitVec 32} {s : State}
    (hc : VerifyContext b pk sig challenge s) :
    WP isa verifyBody s fun t => VerifyKeep b s t ∧ t.gpr .r9 = BitVec.ofNat 32
      (Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt s.mem (State.addr pk) 32)
        (Spec.Ed25519.bytesAt s.mem (State.addr sig) 64) (Spec.Ed25519.bytesAt s.mem (State.addr challenge) 64)).toNat := by
  refine WP.seq (WP.mono (verifyScalar_ok hc) fun u ⟨uk, uz⟩ => ?_)
  apply WP.ite _ (congrArg some uz)
  · intro hy
    refine WP.seq (WP.mono (initFields_ok (uk.ctx hc.ctx)) fun v ⟨vk, vl, _⟩ => ?_)
    obtain kv := uk.trans (VerifyKeep.of_keep vk)
    refine WP.mono (verifyDecode_ok (hc.keep kv) vl) fun t ⟨tk, tv⟩ => ?_
    refine ⟨kv.trans tk, ?_⟩
    rw [decodedEquation_keep hc kv] at tv
    rw [verifyEquation_bytes _ _ _ _ hc.sigInput.fit, hy, Bool.true_and]
    exact tv
  · intro hn
    refine WP.mono (recoverInvalid_ok u b) fun t ⟨tk, _, tv⟩ => ?_
    refine ⟨uk.trans (VerifyKeep.of_keep tk), ?_⟩
    rw [verifyEquation_bytes _ _ _ _ hc.sigInput.fit, hn, Bool.false_and]
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
    WP isa (.block verifyHeaders) s fun t => Ctx b t ∧ Rest [.r0, .r12] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 8160, 12⟩] s.mem t.mem ∧
      t.mem.readW (State.addr b + BitVec.ofNat 64 8160) 32 = s.gpr .r0 ∧
      t.mem.readW (State.addr b + BitVec.ofNat 64 8164) 32 = s.gpr .r1 ∧
      t.mem.readW (State.addr b + BitVec.ofNat 64 8168) 32 = s.gpr .r2 := by
  refine wp_movw fun a ha => wp_dp (op2_reg _ _) fun c hc => ?_
  obtain cp : c.gpr .r12 = b + BitVec.ofNat 32 8160 := by
    rw [hc.gpr]
    change a.gpr .r3 + a.gpr .r12 = _
    rw [ha.other _ (by decide), hb, ha.gpr]
    rfl
  obtain cr : Rest [.r12] s c := (ha.rest (by decide)).trans (hc.rest (by decide))
  obtain cm : c.mem = s.mem := hc.mem.trans ha.mem
  have ca (k : Nat) (hk : k + 8160 < 8192) :
      State.addr (c.gpr .r12 + BitVec.ofNat 32 k) = State.addr b + BitVec.ofNat 64 (8160 + k) := by
    rw [cp, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact addr_add (by omega_arith)
  refine wp_str (a := State.addr b + BitVec.ofNat 64 8160) (by decide)
    (by simpa only [Nat.add_zero] using ca 0 (by decide))
    (by rw [cr.wr]; exact in_base hw (by decide) (by decide)) fun d hd => ?_
  refine wp_str (a := State.addr b + BitVec.ofNat 64 8164) (by decide)
    (by rw [hd.gpr]; exact ca 4 (by decide))
    (by rw [hd.wr, cr.wr]; exact in_base hw (by decide) (by decide)) fun e he => ?_
  refine wp_str (a := State.addr b + BitVec.ofNat 64 8168) (by decide)
    (by rw [he.gpr, hd.gpr]; exact ca 8 (by decide))
    (by rw [he.wr, hd.wr, cr.wr]; exact in_base hw (by decide) (by decide)) fun f hf => ?_
  refine wp_mov (op2_reg _ _) fun t ht => WP.block_nil ?_
  obtain kt : Rest [.r0, .r12] s t := (cr.mono (by decide)).trans
    ((hd.rest _).trans ((he.rest _).trans ((hf.rest _).trans (ht.rest (by decide)))))
  obtain mt : t.mem = ((s.mem.writeW (State.addr b + BitVec.ofNat 64 8160) (s.gpr .r0)).writeW
      (State.addr b + BitVec.ofNat 64 8164) (s.gpr .r1)).writeW
      (State.addr b + BitVec.ofNat 64 8168) (s.gpr .r2) := by
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
      (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32 ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 64) < 2 ^ 256
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
  top : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 64) < 2 ^ 256

theorem VerifyPre.of {s : State} (h : verifyLocal.pre s) : VerifyPre s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩

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
    (hc : Ctx b s) (hs : ScalarSaved (State.addr b) g s.mem) :
    WP isa (.block verifyFinish) s fun t =>
      (∀ i < 8, t.gpr (scalarSavedReg i) = g (scalarSavedReg i)) ∧
      Rest [.r0, .r1, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr] s t ∧
      t.mem = s.mem ∧ t.gpr .r0 = s.gpr .r9 ∧
      t.gpr .lr = s.mem.readW (State.addr b + BitVec.ofNat 64 LRS) 32 := by
  show WP isa (.block (([.mov .r1 (.reg .r9)] : List Instr) ++ ((scratchAddr LRS ++ ([.ldr .lr .r12 0] : List Instr)) ++
    (scalarRestore ++ ([.mov .r0 (.reg .r1)] : List Instr))))) s _
  rw [WP.block_append_iff]
  refine wp_mov (op2_reg _ _) fun u hu => WP.block_nil ?_
  obtain hcu : Ctx b u := hc.of_rest (hu.rest (ws := [Reg.r1]) (by decide)) (by decide)
  refine WP.append (loadLr_ok hcu) fun u' ⟨r', m', l'⟩ => ?_
  rw [WP.block_append_iff]
  obtain hs' : ScalarSaved (State.addr b) g u'.mem := by rw [m', hu.mem]; exact hs
  refine WP.mono (scalarRestore_ok (hcu.of_rest r' (by decide)) hs')
    fun v ⟨vg, vr, vm⟩ => ?_
  refine wp_mov (op2_reg _ _) fun t ht => WP.block_nil ?_
  refine ⟨fun i hi => ?_, (hu.rest (by decide)).trans ((r'.mono (by decide)).trans ((vr.mono (by decide)).trans
    (ht.rest (by decide)))), ht.mem.trans (vm.trans (m'.trans hu.mem)), ?_, ?_⟩
  · rw [ht.other _ (by
      obtain h : ∀ i < 8, scalarSavedReg i ≠ Reg.r0 := by decide
      exact h i hi)]
    exact vg i hi
  · rw [ht.gpr, vr.gpr _ (by decide), r'.gpr _ (by decide), hu.gpr]
  · rw [ht.other _ (by decide), vr.gpr _ (by decide), l', hu.mem]

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.VerifySetup`. -/
section
/-! Save registers, install public headers, and establish the verifier context. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifyHeadersSaved_ok {s : State} (h : VerifyPre s) :
    WP isa (.block (scalarSave .r3 ++ verifyHeaders)) s fun t =>
      VerifyContext (s.gpr .r3) (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) t ∧
      ScalarSaved (State.addr (s.gpr .r3)) s.gpr t.mem ∧ Rest [.r0, .r12] s t ∧
      Frame [⟨State.addr (s.gpr .r3), 8192⟩] s.mem t.mem := by
  obtain hw : (⟨State.addr (s.gpr .r3), 8192⟩ : Region) ∈ s.wr := by rw [h.wr]; exact List.mem_singleton_self _
  rw [WP.block_append_iff]
  refine WP.mono (scalarSave_ok rfl h.f3 hw) fun u ⟨us, uf, ug, uk⟩ => ?_
  refine WP.mono (verifyHeaders_ok (by rw [ug]) h.f3 (by rw [uk.wr]; exact hw))
    fun t ⟨tc, tk, tf, tp, ts, th⟩ => ?_
  obtain kt := (uk.mono (by decide)).trans tk
  obtain ft : Frame [⟨State.addr (s.gpr .r3), 8192⟩] s.mem t.mem :=
    (uf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩).trans
    (tf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by decide)⟩)
  have ip (r : Reg) (n : Nat) (hn : (s.gpr r).toNat + n ≤ 2 ^ 32)
      (hi : (⟨State.addr (s.gpr r), n⟩ : Region) ∈ s.rd)
      (hd : (⟨State.addr (s.gpr r), n⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 8192⟩) :
      VerifyInput (s.gpr .r3) (s.gpr r) n t := by
    refine ⟨hn, fun i hb => ?_, hd⟩
    rw [kt.rd, kt.wr]
    exact in_base (List.mem_append_left _ hi) (by omega_arith) (by omega_arith)
  refine ⟨⟨tc, ip .r0 32 h.f0 (by rw [h.rd]; simp) h.pk_ws,
    ip .r1 64 h.f1 (by rw [h.rd]; simp) h.sig_ws,
    ip .r2 64 h.f2 (by rw [h.rd]; simp) h.challenge_ws,
    tp.trans (congrFun ug .r0), ts.trans (congrFun ug .r1), th.trans (congrFun ug .r2),
    by rw [challenge_frame ft h.challenge_ws]; exact h.top⟩,
    ?_, kt, ft⟩
  exact us.frame tf fun r hr i hi => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by decide)

theorem verifySetup_ok {s : State} (h : VerifyPre s) :
    WP isa (.block verifySetup) s fun t =>
      VerifyContext (s.gpr .r3) (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) t ∧
      ScalarSaved (State.addr (s.gpr .r3)) s.gpr t.mem ∧
      t.mem.readW (State.addr (s.gpr .r3) + BitVec.ofNat 64 LRS) 32 = s.gpr .lr ∧ Rest [.r0, .r12] s t ∧
      Frame [⟨State.addr (s.gpr .r3), 8192⟩] s.mem t.mem := by
  show WP isa (.block ((scalarSave .r3 ++ verifyHeaders) ++
    (scratchAddr LRS ++ ([.str .lr .r12 0] : List Instr)))) s _
  refine WP.append (verifyHeadersSaved_ok h) fun u ⟨uc, us, uk, uf⟩ => ?_
  refine WP.mono (saveLr_ok uc.ctx) fun t ⟨tr, tm⟩ => ?_
  have hS : LRS = 8172 := rfl
  obtain sep : ∀ d, d + 4 ≤ 8172 → t.mem.readW (State.addr (s.gpr .r3) + BitVec.ofNat 64 d) 32 =
      u.mem.readW (State.addr (s.gpr .r3) + BitVec.ofNat 64 d) 32 := fun d hd => by
    rw [tm]
    exact Mem.readW_writeW_sep (Offset.sep _ (d := d) (e := LRS) (n := 4) (k := 4) (by omega_arith) (by omega_arith)
      (by omega_arith)) (by decide)
  have inp {p : BitVec 32} {n : Nat} (hi : VerifyInput (s.gpr .r3) p n u) : VerifyInput (s.gpr .r3) p n t :=
    ⟨hi.fit, fun i hn => by rw [tr.rd, tr.wr]; exact hi.readable i hn, hi.separate⟩
  refine ⟨⟨uc.ctx.of_rest tr (by decide), inp uc.pkInput, inp uc.sigInput, inp uc.challengeInput,
      (sep 8160 (by decide)).trans uc.pkHeader, (sep 8164 (by decide)).trans uc.sigHeader,
      (sep 8168 (by decide)).trans uc.challengeHeader,
      by
        rw [challenge_frame (b := s.gpr .r3) (by
          rw [tm]
          exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
            (Offset.contains_base _ (by decide) (by decide))) uc.challengeInput.separate]
        exact uc.challengeTop⟩,
    fun i hi => (sep (4 * i) (by omega_arith)).trans (us i hi), ?_, (uk.mono (by decide)).trans (tr.mono (by decide)), ?_⟩
  · rw [tm, Mem.readW_writeW_self32, uk.gpr _ (by decide)]
  · rw [tm]; exact uf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))

end VG.Proof.Ed25519.Arm
end

/-! The complete ARM verification equation restores the ABI and returns the specified flag. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifyEquation_correct {s : State} (h : VerifyPre s) :
    WP isa verifyEquation s fun t => abiPreserved s t ∧ verifyLocal.post s t := by
  refine WP.seq (WP.mono (verifySetup_ok h) fun u ⟨uc, us, ul, uk, uf⟩ => ?_)
  refine WP.seq (WP.mono (verifyBody_ok uc) fun v ⟨vk, vv⟩ => ?_)
  obtain vs : ScalarSaved (State.addr (s.gpr .r3)) s.gpr v.mem := us.frame vk.frame fun r hr i hi => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by decide)
  obtain lv : v.mem.readW (State.addr (s.gpr .r3) + BitVec.ofNat 64 LRS) 32 = s.gpr .lr := by
    refine (BitVec.eq_of_toNat_eq (wd_frame vk.frame fun r hr => ?_)).trans ul
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
  refine WP.mono (verifyFinish_ok (vk.ctx uc.ctx) vs) fun t ⟨tg, tk, _, tv, tl⟩ => ?_
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
    · rw [tl, lv]
  · have bytes (p : BitVec 32) (n : Nat) (hn : n ≤ 64)
        (hd : (⟨State.addr p, n⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 8192⟩) :
        Spec.Ed25519.bytesAt u.mem (State.addr p) n = Spec.Ed25519.bytesAt s.mem (State.addr p) n := by
      unfold Spec.Ed25519.bytesAt
      refine List.map_congr_left fun i hi => uf.bytes (R := ⟨State.addr p, n⟩)
        (fun r hr => ?_) (by omega_arith : n ≤ 2 ^ 64) (List.mem_range.mp hi)
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
  ctx : VerifyContext b pk sig challenge s
  pkBytes : Spec.Ed25519.bytesAt s.mem (State.addr pk) 32 = Spec.Ed25519.bytesAt m (State.addr pk) 32
  sigBytes : Spec.Ed25519.bytesAt s.mem (State.addr sig) 64 = Spec.Ed25519.bytesAt m (State.addr sig) 64
  challengeBytes : Spec.Ed25519.bytesAt s.mem (State.addr challenge) 64 = Spec.Ed25519.bytesAt m (State.addr challenge) 64

theorem VerifyPublic.keep {m : Mem} {b pk sig challenge : BitVec 32} {s t : State}
    (h : VerifyPublic m b pk sig challenge s) (hk : VerifyKeep b s t) : VerifyPublic m b pk sig challenge t :=
  ⟨h.ctx.keep hk, (h.ctx.pkInput.bytes hk).trans h.pkBytes,
    (h.ctx.sigInput.bytes hk).trans h.sigBytes, (h.ctx.challengeInput.bytes hk).trans h.challengeBytes⟩

theorem VerifyPublic.rBytes {m : Mem} {b pk sig challenge : BitVec 32} {s : State}
    (h : VerifyPublic m b pk sig challenge s) :
    Spec.Ed25519.bytesAt s.mem (State.addr sig) 32 = Spec.Ed25519.bytesAt m (State.addr sig) 32 := by
  obtain he := congrArg (List.take 32) h.sigBytes
  simpa only [signatureBytes_take] using he

theorem VerifyPublic.sBytes {m : Mem} {b pk sig challenge : BitVec 32} {s : State}
    (h : VerifyPublic m b pk sig challenge s) :
    Spec.Ed25519.bytesAt s.mem (State.addr (sig + 32)) 32 = Spec.Ed25519.bytesAt m (State.addr (sig + 32)) 32 := by
  obtain ep : State.addr (sig + (32 : BitVec 32)) = State.addr sig + BitVec.ofNat 64 32 :=
    addr_add (k := 32) (by have := h.ctx.sigInput.fit; omega_arith)
  rw [ep]
  obtain he := congrArg (List.drop 32) h.sigBytes
  simpa only [signatureBytes_drop] using he

end VG.Proof.Ed25519.Arm
