module

import VerifiedGarbage.Proof.Ed25519.Arm.LrSlot
public import VerifiedGarbage.Proof.Ed25519.Arm.PointKeep
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarPass
public import VerifiedGarbage.Impl.Ed25519.Arm.Verify
public import VerifiedGarbage.Proof.Ed25519.Arm.PointDecode
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
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
import VerifiedGarbage.Proof.Ed25519.Arm.Points
import VerifiedGarbage.Proof.Ed25519.Arm.FnCall
import VerifiedGarbage.Proof.Ed25519.Group.Decode
import VerifiedGarbage.Proof.Ed25519.Group.Double
import VerifiedGarbage.Proof.Ed25519.ScalarBytes
public import VerifiedGarbage.Proof.Ed25519.Arm.CombLoop
public import VerifiedGarbage.Proof.Ed25519.SlidingDigits
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Arm.Syms

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

/-- The comb's tables at `T`, the static's address, outside the working space. -/
structure VerifyTbl (b T : BitVec 32) (s : State) : Prop where
  tbl : TblAt s T
  apart : (TBL T).Disjoint ⟨State.addr b, 8192⟩
  sym : s.syms combSym = T

theorem VerifyTbl.keep {b T : BitVec 32} {s t : State} (h : VerifyTbl b T s) (hk : VerifyKeep b s t)
    (hsy : t.syms = s.syms) : VerifyTbl b T t :=
  ⟨h.tbl.of_frame (by rw [hk.rest.rd, hk.rest.wr]) hk.frame fun r hr => by
      rw [List.mem_singleton.mp hr]; exact h.apart.sub_right (Offset.sub_base _ (by decide)),
    h.apart, (congrFun hsy _).trans h.sym⟩

/-- The projective comparison's first test reads only what `p` represents. -/
theorem rep_cross_x {p q : Spec.Ed25519.Point} {a : Edwards.EPoint Proof.Ed25519.dZ} (hp : Proof.Ed25519.Rep p a) :
    p.X * q.Z = q.X * p.Z ↔ a.x * Proof.Ed25519.toZ q.Z = Proof.Ed25519.toZ q.X := by
  constructor
  · intro h
    have e : Proof.Ed25519.toZ (p.X * q.Z) = Proof.Ed25519.toZ (q.X * p.Z) := congrArg Proof.Ed25519.toZ h
    rw [Proof.Ed25519.toZ_mul, Proof.Ed25519.toZ_mul, hp.x] at e
    exact mul_right_cancel₀ hp.z (by linear_combination e)
  · intro h
    exact Proof.Ed25519.toZ_inj.mp (by
      rw [Proof.Ed25519.toZ_mul, Proof.Ed25519.toZ_mul, hp.x]; linear_combination Proof.Ed25519.toZ p.Z * h)

/-- Its second test, likewise. -/
theorem rep_cross_y {p q : Spec.Ed25519.Point} {a : Edwards.EPoint Proof.Ed25519.dZ} (hp : Proof.Ed25519.Rep p a) :
    p.Y * q.Z = q.Y * p.Z ↔ a.y * Proof.Ed25519.toZ q.Z = Proof.Ed25519.toZ q.Y := by
  constructor
  · intro h
    have e : Proof.Ed25519.toZ (p.Y * q.Z) = Proof.Ed25519.toZ (q.Y * p.Z) := congrArg Proof.Ed25519.toZ h
    rw [Proof.Ed25519.toZ_mul, Proof.Ed25519.toZ_mul, hp.y] at e
    exact mul_right_cancel₀ hp.z (by linear_combination e)
  · intro h
    exact Proof.Ed25519.toZ_inj.mp (by
      rw [Proof.Ed25519.toZ_mul, Proof.Ed25519.toZ_mul, hp.y]; linear_combination Proof.Ed25519.toZ p.Z * h)

/-- The comparison is the same for other representatives of its two points. -/
theorem pointEqual_rep_both {p p' q q' : Spec.Ed25519.Point} {a b : Edwards.EPoint Proof.Ed25519.dZ}
    (hp : Proof.Ed25519.Rep p a) (hp' : Proof.Ed25519.Rep p' a) (hq : Proof.Ed25519.Rep q b)
    (hq' : Proof.Ed25519.Rep q' b) : Spec.Ed25519.pointEqual p q = Spec.Ed25519.pointEqual p' q' := by
  rw [Bool.eq_iff_iff, Proof.Ed25519.pointEqual_rep hp hq, Proof.Ed25519.pointEqual_rep hp' hq']

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

variable {umaal : Bool}

theorem verifyCombine_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (hl : AllLim s.mem b)
    (hd : env s.mem b 16 = Spec.Ed25519.d) :
    WP isa (verifyCombine umaal) s fun t => AccKeep b s t ∧ AllLim t.mem b ∧
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

section
/-! `[k]A` with a sliding window on `k`, which is public: `k`'s digits (`recode`), the table of
`A`'s odd multiples (`oddTable`), and the sum, from the top digit's multiple (`topDigit`,
`slideStart`), doubled for each digit below it, with the digit's multiple added where the digit
is not zero (`slideStep`). The doubling is the dedicated one (`Proof.Ed25519.dblPoint`), of
`X : Y : Z` (`dblXYZ`): its `T` is computed where an addition reads it (`doubleT_ok`). -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

variable {umaal : Bool}

/-- A word of the working space. -/
abbrev lw (m : Mem) (b : BitVec 32) (d : Nat) : BitVec 32 := m.readW (State.addr b + BitVec.ofNat 64 d) 32

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

theorem ofNat_succ_sub_one (m : Nat) : BitVec.ofNat 32 (m + 1) - 1#32 = BitVec.ofNat 32 m := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_arith

/-- Bit `8 j + t` of `K` is bit `t` of its byte `j`. -/
theorem byte_bit (K j : Nat) {t : Nat} (ht : t < 8) :
    K / 2 ^ (8 * j + t) % 2 = K / 256 ^ j % 256 / 2 ^ t % 2 := by
  have e : (2 : Nat) ^ (8 * j + t) = 256 ^ j * 2 ^ t := by rw [Nat.pow_add, Nat.pow_mul]
  rw [e, ← Nat.div_div_eq_div_mul]
  generalize K / 256 ^ j = X
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by omega_using [ht]
  all_goals omega_arith

theorem pointAdd_q (e : Env) : point (evalOps pointAddOps e) 4 5 6 7 = point e 4 5 6 7 :=
  point_congr _ _ _ _ (evalOps_unchanged _ _ _ (by decide)) (evalOps_unchanged _ _ _ (by decide))
    (evalOps_unchanged _ _ _ (by decide)) (evalOps_unchanged _ _ _ (by decide))

/-- `c`, `n` times from step `i`, each step keeping the invariant. -/
theorem repeatThen_wp {c k : Prog isa} {I : Nat → State → Prop} {Q : State → Prop} :
    ∀ (n i : Nat) (s : State), I i s → (∀ i' s', i ≤ i' → i' < i + n → I i' s' → WP isa c s' (I (i' + 1))) →
      (∀ t, I (i + n) t → WP isa k t Q) → WP isa (repeatThen n c k) s Q
  | 0, i, s, hs, _, hk => hk s hs
  | n + 1, i, s, hs, hc, hk => by
    rw [repeatThen]
    refine WP.seq (WP.mono (hc i s (Nat.le_refl _) (by omega_arith) hs) fun u hu => ?_)
    exact repeatThen_wp n (i + 1) u hu (fun i' s' h1 h2 => hc i' s' (by omega_using [h1]) (by omega_using [h2]))
      (fun t ht => hk t (by rw [show i + (n + 1) = i + 1 + n by omega_arith]; exact ht))

/-! ### What the code computes -/

/-- `[2m + 1]a`, as the table's entries are computed: `a`, and `[2]a`, by the dedicated doubling,
added to the entry before. -/
def oddMul (a : Spec.Ed25519.Point) : Nat → Spec.Ed25519.Point
  | 0 => a
  | m + 1 => Spec.Ed25519.pointAdd (oddMul a m) (Proof.Ed25519.dblPoint a)

theorem oddMul_rep {a : Spec.Ed25519.Point} {A : Edwards.EPoint Proof.Ed25519.dZ} (ha : Proof.Ed25519.Rep a A) :
    ∀ m, Proof.Ed25519.Rep (oddMul a m) ((2 * m + 1) • A)
  | 0 => by simpa only [oddMul, Nat.mul_zero, Nat.zero_add, one_nsmul] using ha
  | m + 1 => by
    have h := Proof.Ed25519.pointAdd_rep (oddMul_rep ha m) (Proof.Ed25519.dblPoint_rep ha.proj)
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 by omega_arith, add_nsmul, add_nsmul, one_nsmul, add_assoc]
    exact h

/-- The sum over the digits `D` from position `p₀ - n` up to the top one's, `p₀`, as the code
computes it: the top digit's entry (the identity if that digit is zero), and then, for each digit
below, the sum doubled and the digit's entry added to it where the digit is not zero. The
doubling is of `X : Y : Z` (`dblXYZ`), with its `T` (`dblPoint`) before an addition and after
digit 0. -/
def slideVal (a : Spec.Ed25519.Point) (D : Nat → Nat) (p₀ : Nat) : Nat → Spec.Ed25519.Point
  | 0 => if D p₀ = 0 then Spec.Ed25519.identity else oddMul a ((D p₀ - 1) / 2)
  | n + 1 =>
    if D (p₀ - 1 - n) = 0 then
      if p₀ - 1 - n = 0 then Proof.Ed25519.dblPoint (slideVal a D p₀ n) else dblXYZ (slideVal a D p₀ n)
    else Spec.Ed25519.pointAdd (oddMul a ((D (p₀ - 1 - n) - 1) / 2))
      (Proof.Ed25519.dblPoint (slideVal a D p₀ n))

theorem slideVal_zero (a : Spec.Ed25519.Point) (D : Nat → Nat) (p₀ : Nat) :
    slideVal a D p₀ 0 = if D p₀ = 0 then Spec.Ed25519.identity else oddMul a ((D p₀ - 1) / 2) := rfl

/-- The sum at position `p` below the top, from the sum at the position above. -/
theorem slideVal_at (a : Spec.Ed25519.Point) (D : Nat → Nat) {p₀ p : Nat} (hp : p < p₀) :
    slideVal a D p₀ (p₀ - p) =
      if D p = 0 then
        if p = 0 then Proof.Ed25519.dblPoint (slideVal a D p₀ (p₀ - (p + 1)))
        else dblXYZ (slideVal a D p₀ (p₀ - (p + 1)))
      else Spec.Ed25519.pointAdd (oddMul a ((D p - 1) / 2))
        (Proof.Ed25519.dblPoint (slideVal a D p₀ (p₀ - (p + 1)))) := by
  obtain ⟨n, hn⟩ : ∃ n, p₀ - (p + 1) = n := ⟨_, rfl⟩
  rw [show p₀ - p = n + 1 by omega_using [hp, hn], hn, slideVal, show p₀ - 1 - n = p by omega_using [hp, hn]]

/-- The doubling of `X : Y : Z` represents the double, but for `T`. -/
private theorem dblXYZ_repP {p : Spec.Ed25519.Point} {A : Edwards.EPoint Proof.Ed25519.dZ}
    (h : Proof.Ed25519.RepP p A) : Proof.Ed25519.RepP (dblXYZ p) (A + A) :=
  have r := (Proof.Ed25519.dblPoint_rep h).proj
  ⟨r.z, r.x, r.y⟩

/-- The sum's `X : Y : Z` represent the multiple by the digits taken, if those above the top
one's position `p₀` are zero. -/
private theorem slideVal_repP {a : Spec.Ed25519.Point} {A : Edwards.EPoint Proof.Ed25519.dZ} (ha : Proof.Ed25519.Rep a A)
    {D : Nat → Nat} (hD : ∀ q, D q = 0 ∨ (D q % 2 = 1 ∧ D q < 16)) {p₀ : Nat} (hp : p₀ < 256)
    (hz : ∀ q, p₀ < q → q < 256 → D q = 0) :
    ∀ n ≤ p₀, (Proof.Ed25519.RepP (slideVal a D p₀ n)
        (Proof.Ed25519.Slide.wsum D (p₀ - n) (256 - (p₀ - n)) • A)) ∧
      (n = p₀ → Proof.Ed25519.Rep (slideVal a D p₀ n)
        (Proof.Ed25519.Slide.wsum D (p₀ - n) (256 - (p₀ - n)) • A))
  | 0, _ => by
    rw [slideVal, Nat.sub_zero, show 256 - p₀ = (255 - p₀) + 1 by omega_using [hp],
      Proof.Ed25519.Slide.wsum_succ,
      Proof.Ed25519.Slide.wsum_eq_zero (fun j h1 h2 => hz j (by omega_using [h1]) (by omega_using [h2, hp])),
      Nat.mul_zero, Nat.add_zero]
    suffices h : Proof.Ed25519.Rep (if D p₀ = 0 then Spec.Ed25519.identity else oddMul a ((D p₀ - 1) / 2))
        (D p₀ • A) from ⟨h.proj, fun _ => h⟩
    rcases hD p₀ with h0 | ⟨h1, _⟩
    · rw [ite_eq_left h0, h0, zero_nsmul]
      exact Proof.Ed25519.identity_rep
    · rw [ite_eq_right (by omega_using [h1])]
      have hm := oddMul_rep ha ((D p₀ - 1) / 2)
      rwa [show 2 * ((D p₀ - 1) / 2) + 1 = D p₀ by omega_using [h1]] at hm
  | n + 1, hn => by
    have ih := (slideVal_repP ha hD hp hz n (by omega_using [hn])).1
    have hd := Proof.Ed25519.dblPoint_rep ih
    obtain ⟨p, hpe⟩ : ∃ p, p₀ - 1 - n = p := ⟨_, rfl⟩
    rw [show p₀ - n = p + 1 by omega_using [hn, hpe], show 256 - (p + 1) = 255 - p by omega_using []] at ih hd
    rw [show p₀ - (n + 1) = p by omega_using [hn, hpe], show 256 - p = (255 - p) + 1 by omega_using [hn, hpe, hp],
      Proof.Ed25519.Slide.wsum_succ]
    generalize Proof.Ed25519.Slide.wsum D (p + 1) (255 - p) = x at ih hd ⊢
    rw [slideVal, hpe]
    rcases hD p with h0 | ⟨h1, _⟩
    · rw [ite_eq_left h0, h0, Nat.zero_add, two_mul, add_nsmul]
      by_cases hp0 : p = 0
      · rw [ite_eq_left hp0]
        exact ⟨hd.proj, fun _ => hd⟩
      · rw [ite_eq_right hp0]
        exact ⟨dblXYZ_repP ih, fun e => absurd (by omega_using [e, hpe] : p = 0) hp0⟩
    · rw [ite_eq_right (by omega_using [h1])]
      have hm := oddMul_rep ha ((D p - 1) / 2)
      rw [show 2 * ((D p - 1) / 2) + 1 = D p by omega_using [h1]] at hm
      rw [add_nsmul, two_mul, add_nsmul]
      exact ⟨(Proof.Ed25519.pointAdd_rep hm hd).proj, fun _ => Proof.Ed25519.pointAdd_rep hm hd⟩

/-- `[K]a` as `publicMul` computes it, on the digits of `K` from the top one that is not zero. -/
def slide (a : Spec.Ed25519.Point) (K : Nat) : Spec.Ed25519.Point :=
  slideVal a (Proof.Ed25519.Slide.digits 256 K) (Proof.Ed25519.Slide.topPos (Proof.Ed25519.Slide.digits 256 K) 256)
    (Proof.Ed25519.Slide.topPos (Proof.Ed25519.Slide.digits 256 K) 256)

/-- The whole sum represents `[K]A`, with its `T`. -/
theorem slide_rep {a : Spec.Ed25519.Point} {A : Edwards.EPoint Proof.Ed25519.dZ} (ha : Proof.Ed25519.Rep a A)
    {K : Nat} (hK : K < 2 ^ 256) : Proof.Ed25519.Rep (slide a K) (K • A) := by
  have h := (slideVal_repP ha (Proof.Ed25519.Slide.digits_odd 256 K)
    (Proof.Ed25519.Slide.topPos_lt _ (by decide : 0 < 256))
    (fun q h1 h2 => Proof.Ed25519.Slide.topPos_zero _ _ _ h1 h2) _ (Nat.le_refl _)).2 rfl
  rwa [Nat.sub_self, Nat.sub_zero, Proof.Ed25519.Slide.digits_sum hK] at h

/-! ### The digits -/

/-- The digits' bytes in the working space. -/
abbrev digR (b : BitVec 32) : Region := ⟨State.addr b + BitVec.ofNat 64 DIG, 256⟩

/-- A digit's byte, outside a frame apart from the digits. -/
theorem dig_frame {rs : List Region} {m m' : Mem} {b : BitVec 32} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (digR b).Disjoint r) {q : Nat} (hq : q < 256) :
    m' (State.addr b + BitVec.ofNat 64 (DIG + q)) = m (State.addr b + BitVec.ofNat 64 (DIG + q)) := by
  rw [← Offset.add_add]
  exact hf.bytes (R := digR b) hd (show (256 : Nat) ≤ 2 ^ 64 by decide) hq

theorem ofNat_add_one (n : Nat) : BitVec.ofNat 32 n + 1 = BitVec.ofNat 32 (n + 1) :=
  (BitVec.ofNat_add n 1).symm

private theorem rec_bit_fact : ∀ v < 256,
    (BitVec.ofNat 32 v &&& (1 : BitVec 32)) = BitVec.ofNat 32 (v % 2) ∧
      BitVec.ofNat 32 v >>> 1 = BitVec.ofNat 32 (v / 2) := by decide +kernel

private theorem rec_open_fact : ∀ v < 2, BitVec.ofNat 32 v <<< 1 = BitVec.ofNat 32 (2 * v) := by decide

private theorem rec_grow_fact : ∀ v < 2, ∀ m < 16,
    ((0 : BitVec 32) - BitVec.ofNat 32 v) &&& BitVec.ofNat 32 m = BitVec.ofNat 32 (m * v) ∧
      (BitVec.ofNat 32 m <<< 1) &&& (15 : BitVec 32) = BitVec.ofNat 32 (2 * m % 16) ∧
      (BitVec.ofNat 32 m - (0 : BitVec 32) == 0) = decide (m = 0) := by decide

private theorem rec_byte_fact : ∀ j < 32, BitVec.ofNat 32 (8 * j) >>> 3 = BitVec.ofNat 32 j := by decide

/-- The registers the recoding changes. -/
abbrev recClob : List Reg := [.r1, .r2, .r3, .r6, .r7, .r8, .r9, .r10]

/-- After bit `i` of `K`: the automaton's state (`Slide.run`) in `r6`–`r9`, and the digits of the
bits read. -/
structure RecAt (K : Nat) (b ptr : BitVec 32) (i : Nat) (s : State) : Prop where
  ctx : Ctx b s
  ptr : lw s.mem b 52 = ptr
  r9 : s.gpr .r9 = BitVec.ofNat 32 i
  r8 : s.gpr .r8 = BitVec.ofNat 32 (Proof.Ed25519.Slide.run K i).m
  r7 : s.gpr .r7 = BitVec.ofNat 32 (Proof.Ed25519.Slide.run K i).w
  r6 : s.gpr .r6 = b + BitVec.ofNat 32 (Proof.Ed25519.Slide.run K i).p
  dig : ∀ q < i, s.mem (State.addr b + BitVec.ofNat 64 (DIG + q)) =
    BitVec.ofNat 8 ((Proof.Ed25519.Slide.run K i).u q)

theorem recOpen_ok {b : BitVec 32} {s : State} (hc : Ctx b s) {i v : Nat} (hi : i < 256) (hv : v < 2)
    (h3 : s.gpr .r3 = b + BitVec.ofNat 32 i) (h1 : s.gpr .r1 = BitVec.ofNat 32 v) :
    WP isa (.block recOpen) s fun t => Rest [.r6, .r7, .r8] s t ∧
      t.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 (DIG + i)) (BitVec.ofNat 8 v) ∧
      t.gpr .r8 = BitVec.ofNat 32 (2 * v) ∧ t.gpr .r7 = BitVec.ofNat 32 v ∧
      t.gpr .r6 = b + BitVec.ofNat 32 i := by
  have hfb := hc.fit
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_lsl (by decide)) fun s₂ u₂ =>
    wp_mov (op2_reg _ _) fun s₃ u₃ => ?_
  obtain g6 : s₃.gpr .r6 = b + BitVec.ofNat 32 i := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h3]
  obtain g7 : s₃.gpr .r7 = BitVec.ofNat 32 v := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h1]
  obtain g8 : s₃.gpr .r8 = BitVec.ofNat 32 (2 * v) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h1]
    exact rec_open_fact v hv
  obtain r3 : Rest [.r6, .r7, .r8] s s₃ :=
    (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans (u₃.rest (by decide)))
  refine wp_strb (a := State.addr b + BitVec.ofNat 64 (DIG + i)) (by decide)
    (by rw [g6, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm i DIG]
        exact addr_add (by simp only [DIG]; omega_using [hfb, hi]))
    (by rw [r3.wr]; exact in_base hc.wr (by simp only [DIG]; omega_using [hi]) (by simp only [DIG]; omega_using [hi]))
    fun t ut => WP.block_nil ⟨r3.trans (ut.rest _), ?_, by rw [ut.gpr]; exact g8, by rw [ut.gpr]; exact g7,
      by rw [ut.gpr]; exact g6⟩
  rw [ut.mem, g7, byte_eq (toNat_imm (by omega_using [hv])), u₃.mem, u₂.mem, u₁.mem]

theorem recGrow_ok {b : BitVec 32} {s : State} (hc : Ctx b s) {i p v m w : Nat} (hi : i < 256) (hp : p < 256)
    (hv : v < 2) (hm : m < 16) (hw : w < 16)
    (h3 : s.gpr .r3 = b + BitVec.ofNat 32 i) (h1 : s.gpr .r1 = BitVec.ofNat 32 v)
    (h6 : s.gpr .r6 = b + BitVec.ofNat 32 p) (h7 : s.gpr .r7 = BitVec.ofNat 32 w)
    (h8 : s.gpr .r8 = BitVec.ofNat 32 m) :
    WP isa (.block recGrow) s fun t => Rest [.r2, .r7, .r8] s t ∧
      t.mem = (s.mem.writeW (State.addr b + BitVec.ofNat 64 (DIG + i)) (0 : BitVec 8)).writeW
        (State.addr b + BitVec.ofNat 64 (DIG + p)) (BitVec.ofNat 8 (w + m * v)) ∧
      t.gpr .r8 = BitVec.ofNat 32 (2 * m % 16) ∧ t.gpr .r7 = BitVec.ofNat 32 (w + m * v) := by
  have hfb := hc.fit
  obtain gf := rec_grow_fact v hv m hm
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
  refine wp_strb (a := State.addr b + BitVec.ofNat 64 (DIG + i)) (by decide)
    (by rw [u₁.other _ (by decide), h3, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm i DIG]
        exact addr_add (by simp only [DIG]; omega_using [hfb, hi]))
    (by rw [u₁.wr]; exact in_base hc.wr (by simp only [DIG]; omega_using [hi]) (by simp only [DIG]; omega_using [hi]))
    fun s₂ u₂ => ?_
  refine wp_dp (op2_reg _ _) fun s₃ u₃ => wp_dp (op2_reg _ _) fun s₄ u₄ => wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  obtain g7 : s₅.gpr .r7 = BitVec.ofNat 32 (w + m * v) := by
    simp (disch := decide) only [u₅.gpr, dpVal, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₁.gpr, u₁.other,
      h1, h7, h8]
    rw [gf.1, ← BitVec.ofNat_add]
  obtain g6 : s₅.gpr .r6 = b + BitVec.ofNat 32 p := by
    simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.other, h6]
  obtain g8 : s₅.gpr .r8 = BitVec.ofNat 32 m := by
    simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.other, h8]
  refine wp_strb (a := State.addr b + BitVec.ofNat 64 (DIG + p)) (by decide)
    (by rw [g6, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm p DIG]
        exact addr_add (by simp only [DIG]; omega_using [hfb, hp]))
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
        exact in_base hc.wr (by simp only [DIG]; omega_using [hp]) (by simp only [DIG]; omega_using [hp]))
    fun s₆ u₆ => wp_mov (op2_lsl (by decide)) fun s₇ u₇ => wp_dp (op2_imm (by decide)) fun t ut =>
      WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · exact (u₁.rest (by decide)).trans ((u₂.rest _).trans ((u₃.rest (by decide)).trans ((u₄.rest (by decide)).trans
      ((u₅.rest (by decide)).trans ((u₆.rest _).trans ((u₇.rest (by decide)).trans (ut.rest (by decide))))))))
  · rw [ut.mem, u₇.mem, u₆.mem, g7, byte_eq (toNat_imm (by
      have : m * v ≤ m := by rcases (by omega_using [hv] : v = 0 ∨ v = 1) with rfl | rfl <;> omega_arith
      omega_using [hm, hw, this])), u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, u₁.mem]
    rfl
  · rw [ut.gpr, dpVal, u₇.gpr, u₆.gpr, g8]
    exact gf.2.1
  · rw [ut.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g7]

/-- One bit: bit `t` of byte `j` of `K`, the low bit of `r10`. -/
theorem recBit_ok {K : Nat} {b ptr : BitVec 32} {j t : Nat} {s : State} (h : RecAt K b ptr (8 * j + t) s)
    (hj : j < 32) (ht : t < 8) (h10 : s.gpr .r10 = BitVec.ofNat 32 (K / 256 ^ j % 256 / 2 ^ t)) :
    WP isa recBit s fun u => Rest recClob s u ∧ Frame [digR b] s.mem u.mem ∧
      RecAt K b ptr (8 * j + t + 1) u ∧ u.gpr .r10 = BitVec.ofNat 32 (K / 256 ^ j % 256 / 2 ^ (t + 1)) := by
  obtain hbit : Proof.Ed25519.Slide.bit K (8 * j + t) = K / 256 ^ j % 256 / 2 ^ t % 2 := byte_bit K j ht
  obtain hB : K / 256 ^ j % 256 / 2 ^ t < 256 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (by decide))
  rw [show K / 256 ^ j % 256 / 2 ^ (t + 1) = K / 256 ^ j % 256 / 2 ^ t / 2 by
    rw [Nat.pow_succ, Nat.div_div_eq_div_mul]]
  generalize K / 256 ^ j % 256 / 2 ^ t = v at h10 hbit hB ⊢
  obtain hi : 8 * j + t < 256 := by omega_using [hj, ht]
  generalize 8 * j + t = i at h hi hbit ⊢
  obtain G := Proof.Ed25519.Slide.run_good K i
  obtain Si := Proof.Ed25519.Slide.run_i K i
  obtain hS := Proof.Ed25519.Slide.run_succ K i
  obtain ⟨hc, hptr, h9, h8, h7, h6, hdig⟩ := h
  generalize Proof.Ed25519.Slide.run K i = S at G Si hS h8 h7 h6 hdig
  obtain bf := rec_bit_fact v hB
  obtain hm16 : S.m < 16 := by rcases G.m_cases with e | e | e | e <;> rw [e] <;> decide
  obtain hv2 : v % 2 < 2 := Nat.mod_lt _ (by decide)
  rw [recBit]
  refine WP.seq (wp_dp (op2_reg _ _) fun s₁ u₁ => wp_dp (op2_imm (by decide)) fun s₂ u₂ =>
    wp_cmp (op2_imm (by decide)) fun s₃ f₃ z₃ => WP.block_nil ?_)
  obtain r3 : Rest [.r1, .r3] s s₃ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans (f₃.rest _))
  obtain m3 : s₃.mem = s.mem := by rw [f₃.mem, u₂.mem, u₁.mem]
  obtain c3 : Ctx b s₃ := hc.of_rest r3 (by decide)
  obtain g3 : s₃.gpr .r3 = b + BitVec.ofNat 32 i := by
    rw [f₃.gpr, u₂.other _ (by decide), u₁.gpr, dpVal, hc.r0, h9]
  obtain g1 : s₃.gpr .r1 = BitVec.ofNat 32 (v % 2) := by
    rw [f₃.gpr, u₂.gpr, dpVal, u₁.other _ (by decide), h10]
    exact bf.1
  obtain g6 : s₃.gpr .r6 = b + BitVec.ofNat 32 S.p := (r3.gpr _ (by decide)).trans h6
  obtain g7 : s₃.gpr .r7 = BitVec.ofNat 32 S.w := (r3.gpr _ (by decide)).trans h7
  obtain g8 : s₃.gpr .r8 = BitVec.ofNat 32 S.m := (r3.gpr _ (by decide)).trans h8
  obtain hz : isa.eval .eq s₃ = some (decide (S.m = 0)) := by
    rw [eval_eq, z₃, u₂.other _ (by decide), u₁.other _ (by decide), h8]
    exact congrArg some (rec_grow_fact 0 (by decide) S.m hm16).2.2
  have mid : WP isa (.ite .eq (.block recOpen) (.block recGrow)) s₃ fun x =>
      Rest [.r2, .r6, .r7, .r8] s₃ x ∧ Frame [digR b] s₃.mem x.mem ∧
      x.gpr .r8 = BitVec.ofNat 32 (Proof.Ed25519.Slide.step K S).m ∧
      x.gpr .r7 = BitVec.ofNat 32 (Proof.Ed25519.Slide.step K S).w ∧
      x.gpr .r6 = b + BitVec.ofNat 32 (Proof.Ed25519.Slide.step K S).p ∧
      ∀ q < i + 1, x.mem (State.addr b + BitVec.ofNat 64 (DIG + q)) =
        BitVec.ofNat 8 ((Proof.Ed25519.Slide.step K S).u q) := by
    apply WP.ite (decide (S.m = 0)) hz
    · intro h0
      obtain h0 : S.m = 0 := of_decide_eq_true h0
      obtain ⟨em, ew, ep, eu⟩ := Proof.Ed25519.Slide.step_idle (K := K) h0
      rw [Si, hbit] at em ew eu
      rw [Si] at ep
      refine WP.mono (recOpen_ok c3 hi hv2 g3 g1) fun x ⟨rx, mx, x8, x7, x6⟩ => ?_
      refine ⟨rx.mono (by decide), ?_, by rw [x8, em], by rw [x7, ew], by rw [x6, ep], fun q hq => ?_⟩
      · rw [mx]
        exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (Offset.contains _ (by omega_using []) (by omega_using [hi]) (by simp only [DIG]; omega_using []))
      · rw [mx, VG.WriteBytes.writeW8_apply, eu]
        by_cases hqi : q = i
        · rw [hqi, ite_eq_left rfl, Proof.Ed25519.Slide.upd_self]
        · rw [ite_eq_right (Offset.add_ofNat_ne _ (by simp only [DIG]; omega_using [hq, hi])
            (by simp only [DIG]; omega_using [hi]) (by omega_using [hqi])), Proof.Ed25519.Slide.upd_ne _ _ hqi, m3]
          exact hdig q (by omega_using [hq, hqi])
    · intro h0
      obtain h0 : S.m ≠ 0 := of_decide_eq_false h0
      obtain ⟨em, ew, ep, eu⟩ := Proof.Ed25519.Slide.step_grow (K := K) h0
      rw [Si, hbit] at ew eu
      obtain ⟨hp1, -⟩ := G.m.resolve_left h0
      rw [Si] at hp1
      refine WP.mono (recGrow_ok c3 hi (by omega_using [hp1, hi]) hv2 hm16 G.w g3 g1 g6 g7 g8)
        fun x ⟨rx, mx, x8, x7⟩ => ?_
      refine ⟨rx.mono (by decide), ?_, by rw [x8, em], by rw [x7, ew],
        by rw [rx.gpr _ (by decide), g6, ep], fun q hq => ?_⟩
      · rw [mx]
        exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (Offset.contains _ (by omega_using []) (by omega_using [hi]) (by simp only [DIG]; omega_using []))).writeW
          (List.mem_singleton_self _) _
          (Offset.contains _ (by omega_using []) (by omega_using [hp1, hi]) (by simp only [DIG]; omega_using []))
      · rw [mx, VG.WriteBytes.writeW8_apply, VG.WriteBytes.writeW8_apply, eu]
        by_cases hqp : q = S.p
        · rw [hqp, ite_eq_left rfl, Proof.Ed25519.Slide.upd_self]
        · rw [ite_eq_right (Offset.add_ofNat_ne _ (by simp only [DIG]; omega_using [hq, hi])
            (by simp only [DIG]; omega_using [hp1, hi]) (by omega_using [hqp])), Proof.Ed25519.Slide.upd_ne _ _ hqp]
          by_cases hqi : q = i
          · rw [hqi, ite_eq_left rfl, Proof.Ed25519.Slide.upd_self]
            rfl
          · rw [ite_eq_right (Offset.add_ofNat_ne _ (by simp only [DIG]; omega_using [hq, hi])
              (by simp only [DIG]; omega_using [hi]) (by omega_using [hqi])), Proof.Ed25519.Slide.upd_ne _ _ hqi, m3]
            exact hdig q (by omega_using [hq, hqi])
  refine WP.seq (WP.mono mid fun x ⟨rx, fx, x8, x7, x6, xd⟩ => ?_)
  refine wp_mov (op2_lsr (by decide)) fun y uy => wp_dp (op2_imm (by decide)) fun u uu => WP.block_nil ?_
  obtain ru : Rest recClob s u :=
    (r3.mono (by decide)).trans ((rx.mono (by decide)).trans ((uy.rest (by decide)).trans (uu.rest (by decide))))
  obtain mu : u.mem = x.mem := by rw [uu.mem, uy.mem]
  rw [← m3]
  refine ⟨ru, by rw [mu]; exact fx, ⟨hc.of_rest ru (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [mu, lw_frame fx (.inl (by decide)) (by decide) (by decide), m3]
    exact hptr
  · rw [uu.gpr, dpVal, uy.other _ (by decide), rx.gpr _ (by decide), r3.gpr _ (by decide), h9]
    exact ofNat_add_one i
  · rw [uu.other _ (by decide), uy.other _ (by decide), x8, hS]
  · rw [uu.other _ (by decide), uy.other _ (by decide), x7, hS]
  · rw [uu.other _ (by decide), uy.other _ (by decide), x6, hS]
  · intro q hq
    rw [mu, hS]
    exact xd q hq
  · rw [uu.other _ (by decide), uy.gpr, rx.gpr _ (by decide), r3.gpr _ (by decide), h10]
    exact bf.2

/-- The address of the byte of `k` that holds the bits from `8 j`. -/
theorem recAddr_ok {K : Nat} {b ptr : BitVec 32} {j : Nat} {s : State} (h : RecAt K b ptr (8 * j) s)
    (hj : j < 32) :
    WP isa (.block recAddr) s fun t => (t.gpr .r0 = b ∧ t.gpr .r3 = ptr + BitVec.ofNat 32 j) ∧
      Rest [.r2, .r3] s t ∧ t.mem = s.mem := by
  refine ldrLow_ok h.ctx (d := 52) (by decide) .r3 fun s₁ u₁ => wp_mov (op2_lsr (by decide)) fun s₂ u₂ =>
    wp_dp (op2_reg _ _) fun s₃ u₃ => WP.block_nil ?_
  obtain r3 : Rest [.r2, .r3] s s₃ :=
    (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans (u₃.rest (by decide)))
  refine ⟨⟨(r3.gpr _ (by decide)).trans h.ctx.r0, ?_⟩, r3, by rw [u₃.mem, u₂.mem, u₁.mem]⟩
  rw [u₃.gpr, dpVal, u₂.other _ (by decide), u₁.gpr, h.ptr, u₂.gpr, u₁.other _ (by decide), h.r9]
  exact congrArg (ptr + ·) (rec_byte_fact j hj)

/-- The byte of `k` that holds the bits from `8 j`. -/
theorem recLoad_ok {K : Nat} {b ptr : BitVec 32} {j : Nat} {s : State} (h : RecAt K b ptr (8 * j) s)
    (hj : j < 32) (hin : VerifyInput b ptr 32 s)
    (hK : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) = K) :
    WP isa (.block recLoad) s fun t => Rest [.r2, .r3, .r10] s t ∧ t.mem = s.mem ∧
      t.gpr .r10 = BitVec.ofNat 32 (K / 256 ^ j % 256) := by
  rw [recLoad, WP.block_append_iff]
  refine WP.mono (recAddr_ok h hj) fun s₃ ⟨⟨_, g3⟩, r3, m3⟩ => ?_
  refine wp_ldrb (a := State.addr ptr + BitVec.ofNat 64 j) (by decide)
    (by rw [g3, show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.add_zero]
        exact addr_add (by have := hin.fit; omega_using [hj, this]))
    (by rw [r3.rd, r3.wr]; exact hin.readable j hj) fun t ut => WP.block_nil ?_
  refine ⟨(r3.mono (by decide)).trans (ut.rest (by decide)), by rw [ut.mem, m3], ?_⟩
  rw [ut.gpr, m3, ← hK, Proof.Ed25519.decodeLE_byte]
  have hg : (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32).getD j 0 =
      s.mem (State.addr ptr + BitVec.ofNat 64 j) := by
    simp [Spec.Ed25519.bytesAt, List.getD_eq_getElem?_getD, hj]
  rw [hg]
  apply BitVec.eq_of_toNat_eq
  rw [toNat_setWidth8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide))]

/-- A byte of `k`: its eight bits. -/
theorem recByte_ok {K : Nat} {b ptr : BitVec 32} {j : Nat} {s : State} (h : RecAt K b ptr (8 * j) s)
    (hj : j < 32) (hin : VerifyInput b ptr 32 s)
    (hK : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) = K) :
    WP isa recByte s fun t => Rest recClob s t ∧ Frame [digR b] s.mem t.mem ∧
      RecAt K b ptr (8 * (j + 1)) t ∧ t.z = decide (j + 1 = 32) := by
  rw [recByte]
  refine WP.seq (WP.mono (recLoad_ok h hj hin hK) fun u ⟨ru, mu, u10⟩ => ?_)
  refine repeatThen_wp (I := fun t x => Rest recClob s x ∧ Frame [digR b] s.mem x.mem ∧
      RecAt K b ptr (8 * j + t) x ∧ x.gpr .r10 = BitVec.ofNat 32 (K / 256 ^ j % 256 / 2 ^ t)) 8 0 u
    ⟨ru.mono (by decide), by rw [mu]; exact Frame.refl _ _,
      ⟨h.ctx.of_rest ru (by decide), by rw [mu]; exact h.ptr, (ru.gpr _ (by decide)).trans h.r9,
        (ru.gpr _ (by decide)).trans h.r8, (ru.gpr _ (by decide)).trans h.r7, (ru.gpr _ (by decide)).trans h.r6,
        fun q hq => by rw [mu]; exact h.dig q hq⟩,
      by rw [u10, Nat.pow_zero, Nat.div_one]⟩
    (fun t x _ h2 ⟨rx, fx, ax, x10⟩ => WP.mono (recBit_ok ax hj (by omega_using [h2]) x10)
      fun y ⟨ry, fy, ay, y10⟩ => ⟨rx.trans ry, fx.trans fy, ay, y10⟩) fun v ⟨rv, fv, av, _⟩ => ?_
  rw [show 8 * j + (0 + 8) = 8 * (j + 1) by omega_arith] at av
  refine wp_cmp (op2_imm (by decide)) fun t ft zt => WP.block_nil
    ⟨rv.trans (ft.rest _), by rw [ft.mem]; exact fv,
      ⟨av.ctx.of_rest (ft.rest []) (by decide), by rw [ft.mem]; exact av.ptr, by rw [ft.gpr]; exact av.r9,
        by rw [ft.gpr]; exact av.r8, by rw [ft.gpr]; exact av.r7, by rw [ft.gpr]; exact av.r6,
        fun q hq => by rw [ft.mem]; exact av.dig q hq⟩, ?_⟩
  rw [zt, av.r9]
  show (BitVec.ofNat 32 (8 * (j + 1)) - BitVec.ofNat 32 256 == 0) = _
  rw [sub_beq_zero_nat (by omega_using [hj]) (by decide)]
  exact decide_eq_decide.mpr (by omega_arith)

/-- `k`'s digits, for `k`'s pointer at word 52. -/
theorem recode_ok {b ptr : BitVec 32} {s : State} (hc : Ctx b s) (hp : lw s.mem b 52 = ptr)
    (hin : VerifyInput b ptr 32 s) :
    WP isa recode s fun t => Rest recClob s t ∧ Frame [digR b] s.mem t.mem ∧
      ∀ q < 256, t.mem (State.addr b + BitVec.ofNat 64 (DIG + q)) = BitVec.ofNat 8
        (Proof.Ed25519.Slide.digits 256 (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32)) q) := by
  generalize hK : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) = K
  rw [recode]
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ =>
    wp_mov (op2_imm (by decide)) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => WP.block_nil ?_)
  obtain r4 : Rest recClob s s₄ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans
    ((u₃.rest (by decide)).trans (u₄.rest (by decide))))
  obtain m4 : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain a4 : RecAt K b ptr (8 * (32 - 32)) s₄ :=
    ⟨hc.of_rest r4 (by decide), by rw [m4]; exact hp,
      by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; rfl,
      by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]; rfl,
      by rw [u₄.other _ (by decide), u₃.gpr]; rfl,
      by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hc.r0]
         exact (BitVec.add_zero b).symm,
      fun q hq => absurd hq (Nat.not_lt_zero _)⟩
  refine WP.loop (M := isa) (Inv := fun n t => 0 < n ∧ n ≤ 32 ∧ Rest recClob s t ∧ Frame [digR b] s.mem t.mem ∧
    RecAt K b ptr (8 * (32 - n)) t) ?_ 32 s₄ ⟨by decide, le_rfl, r4, by rw [m4]; exact Frame.refl _ _, a4⟩
  intro n x ⟨n0, n32, rx, fx, ax⟩
  obtain kx : VerifyKeep b s x := VerifyKeep.of_small rx (by decide) fx (by decide) (by decide)
  refine WP.mono (recByte_ok ax (by omega_using [n0]) (hin.keep kx) (by rw [hin.bytes kx]; exact hK))
    fun t ⟨rt, ft, at', zt⟩ => ?_
  by_cases h1 : n = 1
  · subst h1
    rw [show 8 * (32 - 1 + 1) = 256 from rfl] at at'
    exact .inl ⟨by show some (!t.z) = _; rw [zt]; rfl, rx.trans rt, fx.trans ft, fun q hq => by
      rw [Proof.Ed25519.Slide.digits_eq]; exact at'.dig q hq⟩
  · refine .inr ⟨by show some (!t.z) = _; rw [zt, decide_eq_false (by omega_using [h1, n0])]; rfl, n - 1,
      by omega_using [n0], by omega_using [h1, n0], by omega_using [n32], rx.trans rt, fx.trans ft, ?_⟩
    rw [show 32 - (n - 1) = 32 - n + 1 by omega_using [n0, n32]]
    exact at'

/-! ### The table -/

private theorem entry_fact : ∀ m < 8,
    (BitVec.ofNat 16 TBA).setWidth 32 + (BitVec.ofNat 32 m <<< 7) = BitVec.ofNat 32 (TBA + 128 * m) := by decide

private theorem digit_fact : ∀ d < 16, d % 2 = 1 →
    (BitVec.ofNat 16 (TBA - 64)).setWidth 32 + (BitVec.ofNat 32 d <<< 6) =
      BitVec.ofNat 32 (TBA + 128 * ((d - 1) / 2)) := by decide

theorem entryAddr_ok {b : BitVec 32} {s : State} (hc : Ctx b s) {m : Nat} (hm : m < 8)
    (h11 : s.gpr .r11 = BitVec.ofNat 32 m) :
    WP isa (.block entryAddr) s fun t => Rest [.r12] s t ∧ t.mem = s.mem ∧
      t.gpr .r12 = b + BitVec.ofNat 32 (TBA + 128 * m) := by
  refine wp_movw fun s₁ u₁ => wp_dp (op2_lsl (by decide)) fun s₂ u₂ => wp_dp (op2_reg _ _) fun t ut =>
    WP.block_nil ?_
  refine ⟨(u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans (ut.rest (by decide))),
    by rw [ut.mem, u₂.mem, u₁.mem], ?_⟩
  simp (disch := decide) only [ut.gpr, dpVal, u₂.gpr, u₂.other, u₁.gpr, u₁.other, hc.r0, h11]
  exact congrArg (b + ·) (entry_fact m hm)

theorem digitAddr_ok {b : BitVec 32} {s : State} (hc : Ctx b s) {d : Nat} (hd : d < 16) (ho : d % 2 = 1)
    (h10 : s.gpr .r10 = BitVec.ofNat 32 d) :
    WP isa (.block digitAddr) s fun t => Rest [.r12] s t ∧ t.mem = s.mem ∧
      t.gpr .r12 = b + BitVec.ofNat 32 (TBA + 128 * ((d - 1) / 2)) := by
  refine wp_movw fun s₁ u₁ => wp_dp (op2_lsl (by decide)) fun s₂ u₂ => wp_dp (op2_reg _ _) fun t ut =>
    WP.block_nil ?_
  refine ⟨(u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans (ut.rest (by decide))),
    by rw [ut.mem, u₂.mem, u₁.mem], ?_⟩
  simp (disch := decide) only [ut.gpr, dpVal, u₂.gpr, u₂.other, u₁.gpr, u₁.other, hc.r0, h10]
  exact congrArg (b + ·) (digit_fact d hd ho)

/-- What is written above the field area and below the verification's points, as `MulKeep`. -/
theorem MulKeep.of_high {b : BitVec 32} {s t : State} {o n : Nat} {ws : List Reg} (hr : Rest ws s t)
    (hw : ∀ r ∈ ws, r ∈ powersClob) (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, n⟩] s.mem t.mem)
    (ho : 1632 ≤ o) (hn : o + n ≤ 7776) : MulKeep b 1632 6144 s t :=
  ⟨hr.mono hw, hf.sub fun r hm => ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_singleton_self _))), by rw [List.mem_singleton.mp hm]; exact Offset.sub _ ho hn⟩⟩

/-- A table entry, outside a frame of the field area. -/
theorem tab_keep {b : BitVec 32} {m m' : Mem} (h : Frame [FA b] m m') {j : Nat} (hj : j < 8) :
    tablePoint m' b (TBA + 128 * j) = tablePoint m b (TBA + 128 * j) :=
  workspace_tablePoint h (by simp only [TBA]; omega_using []) (by simp only [TBA]; omega_using [hj])

/-- A digit's byte, outside a frame of the field area. -/
theorem dig_keep {b : BitVec 32} {m m' : Mem} (h : Frame [FA b] m m') {q : Nat} (hq : q < 256) :
    m' (State.addr b + BitVec.ofNat 64 (DIG + q)) = m (State.addr b + BitVec.ofNat 64 (DIG + q)) :=
  dig_frame h (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)) hq

/-- The table, and what the additions need of the field's slots. -/
def TabDone (a : Spec.Ed25519.Point) (b : BitVec 32) (m : Mem) : Prop :=
  AllLim m b ∧ env m b 16 = Spec.Ed25519.d ∧ ∀ j < 8, tablePoint m b (TBA + 128 * j) = oddMul a j

/-- The digits are apart from the table and from the field's slots. -/
theorem TabDone.digits {a : Spec.Ed25519.Point} {b : BitVec 32} {m m' : Mem} (h : TabDone a b m)
    (hf : Frame [digR b] m m') : TabDone a b m' := by
  obtain apart : ∀ sl : Slot, ∀ k < 16,
      (⟨State.addr b + BitVec.ofNat 64 (offset sl + 4 * k), 4⟩ : Region).Disjoint (digR b) := fun sl =>
    slot_apart sl (.inr (by simp only [offset, DIG]; have := sl.isLt; omega_using [this])) (by decide)
  refine ⟨fun sl => (env_frame hf sl (apart sl)).2 (h.1 sl), by rw [(env_frame hf 16 (apart 16)).1]; exact h.2.1,
    fun j hj => ?_⟩
  rw [tablePoint_frame hf fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inr (by simp only [TBA, DIG]; omega_using [])) (by simp only [TBA]; omega_using [hj])
      (by decide)]
  exact h.2.2 j hj

/-- The doubling's `T` (`doubleTOps`), after the doubling of `X : Y : Z` of `p`
(`vg_ed25519_r16_point_double`), which left `E` and `H` in slots 11 and 14. -/
theorem doubleT_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (hl : AllLim s.mem b) {p : Spec.Ed25519.Point}
    (hp : point (env s.mem b) 0 1 2 3 = dblXYZ p)
    (ht : env s.mem b 11 * env s.mem b 14 = (Proof.Ed25519.dblPoint p).T) :
    WP isa (fieldCode umaal doubleTOps) s fun t => Keep b s t ∧ AllLim t.mem b ∧
      point (env t.mem b) 0 1 2 3 = Proof.Ed25519.dblPoint p ∧
      ∀ i : Slot, i ≠ 3 → env t.mem b i = env s.mem b i := by
  refine WP.mono (fieldCode_ok _ hc hl) fun t ⟨tk, tl, te⟩ => ⟨tk, tl, ?_, fun i hi => ?_⟩
  · rw [te, ← dblXYZ_t p, ← hp, ← ht]
    rfl
  · rw [te]
    exact Function.update_of_ne hi _ _

/-- Before entry `m` of the table: the entries below it, the entry before it in slots 0–3 and
`[2]A` in slots 4–7. -/
structure TabAt (a : Spec.Ed25519.Point) (b : BitVec 32) (m : Nat) (s : State) : Prop where
  ctx : Ctx b s
  lim : AllLim s.mem b
  d : env s.mem b 16 = Spec.Ed25519.d
  q : point (env s.mem b) 4 5 6 7 = Proof.Ed25519.dblPoint a
  acc : point (env s.mem b) 0 1 2 3 = oddMul a (m - 1)
  r11 : s.gpr .r11 = BitVec.ofNat 32 m
  tab : ∀ j < m, tablePoint s.mem b (TBA + 128 * j) = oddMul a j

theorem oddTableInit_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (hl : AllLim s.mem b) :
    WP isa (oddTableInit umaal) s fun t => MulKeep b 1632 6144 s t ∧
      TabAt (point (env s.mem b) 0 1 2 3) b 1 t := by
  rw [oddTableInit]
  refine WP.seq (WP.mono (fieldCode_ok _ hc hl) fun u ⟨uk, ul, ue⟩ => ?_)
  obtain cu := uk.ctx hc
  obtain ud : env u.mem b 16 = Spec.Ed25519.d := by rw [ue]; rfl
  obtain up : point (env u.mem b) 0 1 2 3 = point (env s.mem b) 0 1 2 3 := by rw [ue]; rfl
  refine WP.seq (WP.mono (pointTableWrite_ok cu ul TBA (by decide) (by decide)) fun v ⟨vk, vl, ve, vt⟩ => ?_)
  obtain cv := vk.ctx cu
  obtain vd : env v.mem b 16 = Spec.Ed25519.d := by rw [ve]; exact ud
  refine WP.seq (WP.mono (doubleCall_ok cv vl) fun w ⟨wk, wl, we⟩ => ?_)
  obtain cw₀ := wk.ctx cv
  obtain wp₀ : point (env w.mem b) 0 1 2 3 = dblXYZ (point (env s.mem b) 0 1 2 3) := by
    rw [we, pointDouble_eval, ve, up]
  obtain wt₀ : env w.mem b 11 * env w.mem b 14 = (Proof.Ed25519.dblPoint (point (env s.mem b) 0 1 2 3)).T := by
    rw [we, pointDouble_t, ve, up]
  obtain wd₀ : env w.mem b 16 = Spec.Ed25519.d := by rw [we, pointDouble_high _ _ (by decide)]; exact vd
  refine WP.seq (WP.mono (doubleT_ok cw₀ wl wp₀ wt₀) fun w' ⟨tk, tl, wp, wo⟩ => ?_)
  obtain cw := tk.ctx cw₀
  obtain wd : env w'.mem b 16 = Spec.Ed25519.d := (wo 16 (by decide)).trans wd₀
  refine WP.seq (WP.mono (fieldCode_ok copyPointToQOps cw tl) fun x ⟨xk, xl, xe⟩ => ?_)
  obtain cx := xk.ctx cw
  obtain xq := ((congrArg (fun e => point e 4 5 6 7) xe).trans (copyPointToQ_eval _)).trans wp
  obtain xd : env x.mem b 16 = Spec.Ed25519.d := by rw [xe, copyPointToQ_d]; exact wd
  obtain xt : tablePoint x.mem b TBA = point (env s.mem b) 0 1 2 3 := by
    rw [workspace_tablePoint xk.frame (by decide) (by decide), workspace_tablePoint tk.frame (by decide) (by decide),
      workspace_tablePoint wk.frame (by decide) (by decide), vt, up]
  rw [WP.block_append_iff]
  refine WP.mono (pointTableRead_ok cx xl TBA (by decide) (by decide)) fun y ⟨yk, yl, yp, yh⟩ => ?_
  refine wp_mov (op2_imm (by decide)) fun t ut => WP.block_nil ?_
  obtain kt : MulKeep b 1632 6144 y t := MulKeep.of_rest (ut.rest (ws := [.r11]) (by decide)) (by decide) ut.mem
  refine ⟨(MulKeep.of_powers (PowersKeep.of_keep uk)).trans ((MulKeep.of_powers (vk.mono (by decide) (by decide))).trans
    ((MulKeep.of_powers (PowersKeep.of_keep wk)).trans ((MulKeep.of_powers (PowersKeep.of_keep tk)).trans
    ((MulKeep.of_powers (PowersKeep.of_keep xk)).trans ((MulKeep.of_powers (PowersKeep.of_acc yk)).trans kt))))),
    ⟨kt.ctx (yk.ctx cx), by rw [ut.mem]; exact yl, by rw [ut.mem, yh 16 (by decide)]; exact xd, ?_, ?_, ut.gpr,
      fun j hj => ?_⟩⟩
  · rw [ut.mem, point_congr _ _ _ _ (yh 4 (by decide)) (yh 5 (by decide)) (yh 6 (by decide)) (yh 7 (by decide))]
    exact xq
  · rw [ut.mem, yp]
    exact xt
  · obtain rfl : j = 0 := by omega_using [hj]
    rw [ut.mem]
    exact (workspace_tablePoint yk.frame (by decide) (by decide)).trans xt

theorem oddTableStep_ok {a : Spec.Ed25519.Point} {b : BitVec 32} {m : Nat} {s : State} (h : TabAt a b m s)
    (h1 : 1 ≤ m) (h8 : m < 8) :
    WP isa (oddTableStep umaal) s fun t => MulKeep b 1632 6144 s t ∧ TabAt a b (m + 1) t ∧
      t.z = decide (m + 1 = 8) := by
  rw [oddTableStep]
  refine WP.seq (WP.mono (addCall_ok h.ctx h.lim) fun u ⟨uk, ul, ue⟩ => ?_)
  obtain cu := uk.ctx h.ctx
  obtain ud : env u.mem b 16 = Spec.Ed25519.d := by rw [ue, pointAdd_high _ _ (by decide)]; exact h.d
  obtain uq : point (env u.mem b) 4 5 6 7 = Proof.Ed25519.dblPoint a := by rw [ue, pointAdd_q]; exact h.q
  obtain up : point (env u.mem b) 0 1 2 3 = oddMul a m := by
    rw [ue, pointAdd_eval _ h.d, h.acc, h.q]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega_using [h1]⟩
    rfl
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (entryAddr_ok cu h8 ((uk.rest.gpr _ (by decide)).trans h.r11)) fun v ⟨vr, vm, vp⟩ => ?_
  obtain cv := cu.of_rest vr (by decide)
  obtain ho : 1632 ≤ TBA + 128 * m := by simp only [TBA]; omega_using []
  obtain hn : TBA + 128 * m + 128 ≤ 7776 := by simp only [TBA]; omega_using [h8]
  refine WP.mono (pointToTable_ok cv (by rw [vm]; exact ul) vp ho (by omega_using [hn])) fun w ⟨wt, wk⟩ => ?_
  obtain cw := wk.ctx cv
  obtain we : env w.mem b = env u.mem b :=
    (wk.env ho (by omega_using [hn])).trans (congrArg (fun m => env m b) vm)
  refine wp_dp (op2_imm (by decide)) fun x ux => wp_cmp (op2_imm (by decide)) fun t ft zt => WP.block_nil ?_
  obtain mt : t.mem = w.mem := by rw [ft.mem, ux.mem]
  obtain rt : Rest [.r11] w t := (ux.rest (by decide)).trans (ft.rest _)
  obtain g11 : x.gpr .r11 = BitVec.ofNat 32 (m + 1) := by
    rw [ux.gpr, dpVal, wk.rest.gpr _ (by decide), vr.gpr _ (by decide), uk.rest.gpr _ (by decide), h.r11]
    exact ofNat_add_one m
  refine ⟨(MulKeep.of_powers (PowersKeep.of_keep uk)).trans ((MulKeep.of_rest vr (by decide) vm).trans
      ((MulKeep.of_high wk.rest (by decide) wk.frame ho hn).trans (MulKeep.of_rest rt (by decide) mt))),
    ⟨cw.of_rest rt (by decide), by rw [mt]; exact wk.lim ho (by omega_using [hn]) (by rw [vm]; exact ul),
      by rw [mt, we]; exact ud, by rw [mt, we]; exact uq, by rw [mt, we, Nat.add_sub_cancel]; exact up,
      by rw [ft.gpr]; exact g11, fun j hj => ?_⟩, ?_⟩
  · rw [mt]
    rcases (by omega_using [hj] : j = m ∨ j < m) with rfl | hj'
    · rw [wt, vm]
      exact up
    · rw [tablePoint_frame wk.frame (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (.inl (by omega_using [hj'])) (by simp only [TBA]; omega_using [hj', h8])
          (by omega_using [hn])), vm, tab_keep uk.frame (by omega_using [hj', h8])]
      exact h.tab j hj'
  · rw [zt, g11]
    show (BitVec.ofNat 32 (m + 1) - BitVec.ofNat 32 8 == 0) = _
    exact sub_beq_zero_nat (by omega_using [h8]) (by decide)

/-- Entries `j < 8` of the table are `[2 j + 1]A`, for `A` in slots 0–3. -/
theorem oddTable_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (hl : AllLim s.mem b) :
    WP isa (oddTable umaal) s fun t => MulKeep b 1632 6144 s t ∧ TabAt (point (env s.mem b) 0 1 2 3) b 8 t := by
  rw [oddTable]
  refine WP.seq (WP.mono (oddTableInit_ok hc hl) fun u ⟨uk, ut⟩ => ?_)
  refine WP.loop (M := isa) (Inv := fun n t => 0 < n ∧ n ≤ 7 ∧ MulKeep b 1632 6144 u t ∧
    TabAt (point (env s.mem b) 0 1 2 3) b (8 - n) t) ?_ 7 u
    ⟨by decide, le_rfl, MulKeep.refl _ _ _ _, (show TabAt _ b (8 - 7) u from ut)⟩
  intro n x ⟨n0, n7, xk, xt⟩
  refine WP.mono (oddTableStep_ok xt (by omega_using [n7]) (by omega_using [n0])) fun t ⟨tk, tt, tz⟩ => ?_
  by_cases h1 : n = 1
  · subst h1
    exact .inl ⟨by show some (!t.z) = _; rw [tz]; rfl, uk.trans (xk.trans tk), tt⟩
  · refine .inr ⟨by show some (!t.z) = _; rw [tz, decide_eq_false (by omega_using [h1, n0])]; rfl, n - 1,
      by omega_using [n0], by omega_using [h1, n0], by omega_using [n7], xk.trans tk, ?_⟩
    rw [show 8 - (n - 1) = 8 - n + 1 by omega_using [n0, n7]]
    exact tt

/-! ### The sum -/

/-- Before the digit below `p`: the sum over the digits from `p` up to the top one's at `p₀`, the
table and the digits. -/
structure SlideAt (a : Spec.Ed25519.Point) (D : Nat → Nat) (b : BitVec 32) (p₀ p : Nat) (s : State) : Prop where
  ctx : Ctx b s
  lim : AllLim s.mem b
  d : env s.mem b 16 = Spec.Ed25519.d
  acc : point (env s.mem b) 0 1 2 3 = slideVal a D p₀ (p₀ - p)
  r11 : s.gpr .r11 = BitVec.ofNat 32 p
  tab : ∀ j < 8, tablePoint s.mem b (TBA + 128 * j) = oddMul a j
  dig : ∀ q < 256, s.mem (State.addr b + BitVec.ofNat 64 (DIG + q)) = BitVec.ofNat 8 (D q)

/-- After the doubling of `X : Y : Z` for digit `p`, which is in `r10`: the doubling's `E` and `H`
are in slots 11 and 14. -/
structure HeadAt (a : Spec.Ed25519.Point) (D : Nat → Nat) (b : BitVec 32) (p₀ p : Nat) (s : State) : Prop where
  ctx : Ctx b s
  lim : AllLim s.mem b
  d : env s.mem b 16 = Spec.Ed25519.d
  acc : point (env s.mem b) 0 1 2 3 = dblXYZ (slideVal a D p₀ (p₀ - (p + 1)))
  eh : env s.mem b 11 * env s.mem b 14 = (Proof.Ed25519.dblPoint (slideVal a D p₀ (p₀ - (p + 1)))).T
  r11 : s.gpr .r11 = BitVec.ofNat 32 p
  r10 : s.gpr .r10 = BitVec.ofNat 32 (D p)
  tab : ∀ j < 8, tablePoint s.mem b (TBA + 128 * j) = oddMul a j
  dig : ∀ q < 256, s.mem (State.addr b + BitVec.ofNat 64 (DIG + q)) = BitVec.ofNat 8 (D q)

/-- The digit at position `r11`, of value `d`, into `r10`; Z is set if it is zero. -/
theorem digitLoad_ok {b : BitVec 32} {p d : Nat} {s : State} (hc : Ctx b s) (hp : p < 256)
    (h11 : s.gpr .r11 = BitVec.ofNat 32 p)
    (hg : s.mem (State.addr b + BitVec.ofNat 64 (DIG + p)) = BitVec.ofNat 8 d) (hd : d < 16) :
    WP isa (.block digitLoad) s fun t => Rest [.r3, .r10] s t ∧ t.mem = s.mem ∧
      t.gpr .r10 = BitVec.ofNat 32 d ∧ t.z = decide (d = 0) := by
  have hfb := hc.fit
  refine wp_dp (op2_reg _ _) fun w uw => ?_
  obtain g3 : w.gpr .r3 = b + BitVec.ofNat 32 p := by rw [uw.gpr, dpVal, hc.r0, h11]
  refine wp_ldrb (a := State.addr b + BitVec.ofNat 64 (DIG + p)) (by decide)
    (by rw [g3, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm p DIG]
        exact addr_add (by simp only [DIG]; omega_using [hfb, hp]))
    (by rw [uw.rd, uw.wr]
        exact in_base (List.mem_append_right _ hc.wr) (by simp only [DIG]; omega_using [hp])
          (by simp only [DIG]; omega_using [hp]))
    fun x ux => wp_cmp (op2_imm (by decide)) fun t ft zt => WP.block_nil ?_
  obtain g10 : x.gpr .r10 = BitVec.ofNat 32 d := by
    rw [ux.gpr, uw.mem, hg]
    apply BitVec.eq_of_toNat_eq
    rw [toNat_setWidth8, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hd]),
      Nat.mod_eq_of_lt (by omega_using [hd])]
  refine ⟨(uw.rest (by decide)).trans ((ux.rest (by decide)).trans (ft.rest _)), by rw [ft.mem, ux.mem, uw.mem],
    by rw [ft.gpr]; exact g10, ?_⟩
  rw [zt, g10]
  show (BitVec.ofNat 32 d - 0#32 == 0#32) = _
  rw [BitVec.sub_zero]
  exact ofNat_beq_zero (by omega_using [hd])

theorem slideHead_ok {a : Spec.Ed25519.Point} {D : Nat → Nat} {b : BitVec 32} {p₀ p : Nat} {s : State}
    (h : SlideAt a D b p₀ (p + 1) s) (hp : p < 256) (hD : D p < 16) :
    WP isa (slideHead umaal) s fun t => MulKeep b 1632 6144 s t ∧ HeadAt a D b p₀ p t ∧
      t.z = decide (D p = 0) := by
  rw [slideHead]
  refine WP.seq (wp_dp (op2_imm (by decide)) fun u uu => WP.block_nil ?_)
  obtain ru : Rest [.r11] s u := uu.rest (by decide)
  obtain cu : Ctx b u := h.ctx.of_rest ru (by decide)
  obtain u11 : u.gpr .r11 = BitVec.ofNat 32 p := by
    rw [uu.gpr, dpVal, h.r11]
    exact ofNat_succ_sub_one p
  refine WP.seq (WP.mono (doubleCall_ok cu (by rw [uu.mem]; exact h.lim)) fun v ⟨vk, vl, ve⟩ => ?_)
  obtain cv := vk.ctx cu
  obtain fv : Frame [FA b] s.mem v.mem := by
    have := vk.frame
    rwa [uu.mem] at this
  obtain vd : env v.mem b 16 = Spec.Ed25519.d := by
    rw [ve, pointDouble_high _ _ (by decide), uu.mem]
    exact h.d
  obtain vp : point (env v.mem b) 0 1 2 3 = dblXYZ (slideVal a D p₀ (p₀ - (p + 1))) := by
    rw [ve, pointDouble_eval, uu.mem, h.acc]
  obtain vt : env v.mem b 11 * env v.mem b 14 =
      (Proof.Ed25519.dblPoint (slideVal a D p₀ (p₀ - (p + 1)))).T := by
    rw [ve, pointDouble_t, uu.mem, h.acc]
  refine WP.mono (digitLoad_ok cv hp ((vk.rest.gpr _ (by decide)).trans u11)
    ((dig_keep fv hp).trans (h.dig p hp)) hD) fun t ⟨rt, mt, t10, tz⟩ => ?_
  refine ⟨(MulKeep.of_rest ru (by decide) uu.mem).trans ((MulKeep.of_powers (PowersKeep.of_keep vk)).trans
      (MulKeep.of_rest rt (by decide) mt)),
    ⟨cv.of_rest rt (by decide), by rw [mt]; exact vl, by rw [mt]; exact vd, by rw [mt]; exact vp,
      by rw [mt]; exact vt, ?_, t10,
      fun j hj => by rw [mt, tab_keep fv hj]; exact h.tab j hj,
      fun q hq => by rw [mt, dig_keep fv hq]; exact h.dig q hq⟩, tz⟩
  rw [rt.gpr _ (by decide), vk.rest.gpr _ (by decide)]
  exact u11

/-- The entry of the digit `d` in `r10` added to the sum `q`, which has its `T`. -/
theorem addEntry_ok {a q : Spec.Ed25519.Point} {b : BitVec 32} {d : Nat} {s : State} (hc : Ctx b s)
    (hl : AllLim s.mem b) (hd : env s.mem b 16 = Spec.Ed25519.d) (hq : point (env s.mem b) 0 1 2 3 = q)
    (h10 : s.gpr .r10 = BitVec.ofNat 32 d)
    (ht : ∀ j < 8, tablePoint s.mem b (TBA + 128 * j) = oddMul a j) (ho : d % 2 = 1) (hD : d < 16) :
    WP isa (addEntry umaal) s fun t => AccKeep b s t ∧ AllLim t.mem b ∧ env t.mem b 16 = Spec.Ed25519.d ∧
      point (env t.mem b) 0 1 2 3 = Spec.Ed25519.pointAdd (oddMul a ((d - 1) / 2)) q := by
  rw [addEntry]
  refine WP.seq (WP.mono (fieldCode_ok copyPointToQOps hc hl) fun u ⟨uk, ul, ue⟩ => ?_)
  obtain cu := uk.ctx hc
  obtain uq := ((congrArg (fun e => point e 4 5 6 7) ue).trans (copyPointToQ_eval _)).trans hq
  obtain ud : env u.mem b 16 = Spec.Ed25519.d := by rw [ue, copyPointToQ_d]; exact hd
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (digitAddr_ok cu hD ho ((uk.rest.gpr _ (by decide)).trans h10)) fun v ⟨vr, vm, vp⟩ => ?_
  obtain cv := cu.of_rest vr (by decide)
  obtain hj : (d - 1) / 2 < 8 := by omega_using [hD]
  refine WP.mono (pointFromTable_ok cv (by rw [vm]; exact ul) vp (by simp only [TBA]; omega_using [])
    (by simp only [TBA]; omega_using [hj])) fun w ⟨wp, wl, wk⟩ => ?_
  obtain cw := wk.ctx cv
  obtain wp' : point (env w.mem b) 0 1 2 3 = oddMul a ((d - 1) / 2) := by
    rw [wp, vm, tab_keep uk.frame hj]
    exact ht _ hj
  obtain wq : point (env w.mem b) 4 5 6 7 = q := by
    rw [point_congr _ _ _ _ (wk.high 4 (by decide)) (wk.high 5 (by decide)) (wk.high 6 (by decide))
      (wk.high 7 (by decide)), vm]
    exact uq
  obtain wd : env w.mem b 16 = Spec.Ed25519.d := by rw [wk.high 16 (by decide), vm]; exact ud
  refine WP.mono (addCall_ok cw wl) fun t ⟨tk, tl, te⟩ => ?_
  refine ⟨(AccKeep.of_keep uk).trans ((AccKeep.of_rest vr (by decide) vm).trans
      ((AccKeep.of_table wk (by decide) (by decide)).trans (AccKeep.of_keep tk))), tl,
    by rw [te, pointAdd_high _ _ (by decide)]; exact wd, ?_⟩
  rw [te, pointAdd_eval _ wd, wp', wq]

/-- After the doubling, by the digit: the doubling's `T` and the digit's entry added, the `T`
alone after digit 0, or nothing. -/
theorem slideTail_ok {a : Spec.Ed25519.Point} {D : Nat → Nat} {b : BitVec 32} {p₀ p : Nat} {s : State}
    (h : HeadAt a D b p₀ p s) (hz : s.z = decide (D p = 0)) (hp₀ : p < p₀) (hp : p < 256)
    (hD : ∀ q, D q = 0 ∨ (D q % 2 = 1 ∧ D q < 16)) :
    WP isa (slideTail umaal) s fun t => AccKeep b s t ∧ AllLim t.mem b ∧ env t.mem b 16 = Spec.Ed25519.d ∧
      point (env t.mem b) 0 1 2 3 = slideVal a D p₀ (p₀ - p) := by
  obtain hDp : D p < 16 := by rcases hD p with e | e <;> omega_using [e]
  rw [slideTail]
  apply WP.ite (!decide (D p = 0)) (by show some (!s.z) = _; rw [hz])
  · intro hb
    obtain hne : D p ≠ 0 := by simpa using hb
    obtain ⟨ho, _⟩ := (hD p).resolve_left hne
    refine WP.seq (WP.mono (doubleT_ok h.ctx h.lim h.acc h.eh) fun u ⟨uk, ul, up, uo⟩ => ?_)
    refine WP.mono (addEntry_ok (a := a) (uk.ctx h.ctx) ul ((uo 16 (by decide)).trans h.d) up
      ((uk.rest.gpr _ (by decide)).trans h.r10) (fun j hj => by rw [tab_keep uk.frame hj]; exact h.tab j hj) ho hDp)
      fun t ⟨tk, tl, td, tp⟩ => ⟨(AccKeep.of_keep uk).trans tk, tl, td, ?_⟩
    rw [tp, slideVal_at a D hp₀, ite_eq_right hne]
  · intro hb
    obtain h0 : D p = 0 := by simpa using hb
    refine WP.seq (wp_cmp (op2_imm (by decide)) fun u fu zu => WP.block_nil ?_)
    obtain ku : AccKeep b s u := AccKeep.of_rest (fu.rest []) (by decide) fu.mem
    obtain ez : isa.eval .eq u = some (decide (p = 0)) := by
      rw [eval_eq, zu, h.r11]
      show some (BitVec.ofNat 32 p - 0#32 == 0#32) = _
      rw [BitVec.sub_zero]
      exact congrArg some (ofNat_beq_zero (by omega_using [hp]))
    apply WP.ite (decide (p = 0)) ez
    · intro hp0
      refine WP.mono (doubleT_ok (p := slideVal a D p₀ (p₀ - (p + 1))) (ku.ctx h.ctx) (by rw [fu.mem]; exact h.lim)
        (by rw [fu.mem]; exact h.acc)
        (by rw [fu.mem]; exact h.eh)) fun t ⟨tk, tl, tp, tu⟩ =>
        ⟨ku.trans (AccKeep.of_keep tk), tl, by rw [tu 16 (by decide), fu.mem]; exact h.d, ?_⟩
      rw [tp, slideVal_at a D hp₀, ite_eq_left h0, ite_eq_left (of_decide_eq_true hp0)]
    · intro hp0
      refine WP.block_nil ⟨ku, by rw [fu.mem]; exact h.lim, by rw [fu.mem]; exact h.d, ?_⟩
      rw [fu.mem, h.acc, slideVal_at a D hp₀, ite_eq_left h0, ite_eq_right (of_decide_eq_false hp0)]

theorem slideStep_ok {a : Spec.Ed25519.Point} {D : Nat → Nat} {b : BitVec 32} {p₀ p : Nat} {s : State}
    (h : SlideAt a D b p₀ (p + 1) s) (hp₀ : p < p₀) (hp : p < 256)
    (hD : ∀ q, D q = 0 ∨ (D q % 2 = 1 ∧ D q < 16)) :
    WP isa (slideStep umaal) s fun t => MulKeep b 1632 6144 s t ∧ SlideAt a D b p₀ p t ∧
      t.z = decide (p = 0) := by
  obtain hDp : D p < 16 := by rcases hD p with e | e <;> omega_using [e]
  rw [slideStep]
  refine WP.seq (WP.mono (slideHead_ok h hp hDp) fun u ⟨uk, uh, uz⟩ => ?_)
  refine WP.seq (WP.mono (slideTail_ok uh uz hp₀ hp hD) fun x ⟨xk, xl, xd, xp⟩ => ?_)
  obtain x11 : x.gpr .r11 = BitVec.ofNat 32 p := (xk.rest.gpr _ (by decide)).trans uh.r11
  refine wp_cmp (op2_imm (by decide)) fun t ft zt => WP.block_nil
    ⟨uk.trans ((MulKeep.of_powers (PowersKeep.of_acc xk)).trans (MulKeep.of_rest (ft.rest []) (by decide) ft.mem)),
      ⟨(xk.ctx uh.ctx).of_rest (ft.rest []) (by decide), by rw [ft.mem]; exact xl, by rw [ft.mem]; exact xd,
        by rw [ft.mem]; exact xp, by rw [ft.gpr]; exact x11,
        fun j hj => by rw [ft.mem, tab_keep xk.frame hj]; exact uh.tab j hj,
        fun q hq => by rw [ft.mem, dig_keep xk.frame hq]; exact uh.dig q hq⟩, ?_⟩
  rw [zt, x11]
  show (BitVec.ofNat 32 p - 0#32 == 0#32) = _
  rw [BitVec.sub_zero]
  exact ofNat_beq_zero (by omega_using [hp])

/-- The digits below the top one's position `p₀ ≥ 1`. -/
theorem slideLoop_ok {a : Spec.Ed25519.Point} {D : Nat → Nat} {b : BitVec 32} {p₀ : Nat} {s : State}
    (h : SlideAt a D b p₀ p₀ s) (h0 : 0 < p₀) (h256 : p₀ ≤ 256)
    (hD : ∀ q, D q = 0 ∨ (D q % 2 = 1 ∧ D q < 16)) :
    WP isa (.loop (slideStep umaal) .ne) s fun t => MulKeep b 1632 6144 s t ∧ SlideAt a D b p₀ 0 t := by
  refine WP.loop (M := isa) (Inv := fun n t => 0 < n ∧ n ≤ p₀ ∧ MulKeep b 1632 6144 s t ∧ SlideAt a D b p₀ n t)
    ?_ p₀ s ⟨h0, le_rfl, MulKeep.refl _ _ _ _, h⟩
  intro n x ⟨n0, np, xk, xa⟩
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega_using [n0]⟩
  refine WP.mono (slideStep_ok xa (by omega_using [np]) (by omega_using [np, h256]) hD) fun t ⟨tk, ta, tz⟩ => ?_
  by_cases hp0 : p = 0
  · subst hp0
    exact .inl ⟨by show some (!t.z) = _; rw [tz]; rfl, xk.trans tk, ta⟩
  · exact .inr ⟨by show some (!t.z) = _; rw [tz, decide_eq_false hp0]; rfl, p, by omega_using [],
      by omega_using [hp0], by omega_using [np], xk.trans tk, ta⟩

/-! ### The top digit -/

/-- Z after a position of the search for the top digit: set if its digit `d` is not zero, or at
position 0. -/
def topZ (d p : Nat) : Bool := if d = 0 then decide (p = 0) else true

/-- The position below `p + 1`, and its digit. -/
theorem topHead_ok {D : Nat → Nat} {b : BitVec 32} {p : Nat} {s : State} (hc : Ctx b s) (hp : p < 256)
    (h11 : s.gpr .r11 = BitVec.ofNat 32 (p + 1))
    (hg : ∀ q < 256, s.mem (State.addr b + BitVec.ofNat 64 (DIG + q)) = BitVec.ofNat 8 (D q)) (hD : D p < 16) :
    WP isa (.block (([.dp .sub .r11 .r11 (.imm 1)] : List Instr) ++ digitLoad)) s fun t =>
      Rest [.r3, .r10, .r11] s t ∧ t.mem = s.mem ∧ t.gpr .r11 = BitVec.ofNat 32 p ∧
      t.gpr .r10 = BitVec.ofNat 32 (D p) ∧ t.z = decide (D p = 0) := by
  rw [WP.block_append_iff]
  refine wp_dp (op2_imm (by decide)) fun u uu => WP.block_nil ?_
  obtain ru : Rest [.r11] s u := uu.rest (by decide)
  obtain u11 : u.gpr .r11 = BitVec.ofNat 32 p := by
    rw [uu.gpr, dpVal, h11]
    exact ofNat_succ_sub_one p
  refine WP.mono (digitLoad_ok (hc.of_rest ru (by decide)) hp u11 (by rw [uu.mem]; exact hg p hp) hD)
    fun t ⟨rt, mt, t10, tz⟩ => ⟨(ru.mono (by decide)).trans (rt.mono (by decide)), mt.trans uu.mem,
      (rt.gpr _ (by decide)).trans u11, t10, tz⟩

theorem topStep_ok {D : Nat → Nat} {b : BitVec 32} {p : Nat} {s : State} (hc : Ctx b s) (hp : p < 256)
    (h11 : s.gpr .r11 = BitVec.ofNat 32 (p + 1))
    (hg : ∀ q < 256, s.mem (State.addr b + BitVec.ofNat 64 (DIG + q)) = BitVec.ofNat 8 (D q)) (hD : D p < 16) :
    WP isa topStep s fun t => Rest [.r3, .r10, .r11] s t ∧ t.mem = s.mem ∧
      t.gpr .r11 = BitVec.ofNat 32 p ∧ t.gpr .r10 = BitVec.ofNat 32 (D p) ∧ t.z = topZ (D p) p := by
  rw [topStep]
  refine WP.seq (WP.mono (topHead_ok hc hp h11 hg hD) fun u ⟨ru, mu, u11, u10, uz⟩ => ?_)
  apply WP.ite (decide (D p = 0)) (by rw [eval_eq, uz])
  · intro hb
    obtain h0 : D p = 0 := of_decide_eq_true hb
    refine wp_cmp (op2_imm (by decide)) fun t ft zt => WP.block_nil
      ⟨ru.trans (ft.rest _), ft.mem.trans mu, by rw [ft.gpr]; exact u11, by rw [ft.gpr]; exact u10, ?_⟩
    rw [zt, u11, topZ, ite_eq_left h0]
    show (BitVec.ofNat 32 p - 0#32 == 0#32) = _
    rw [BitVec.sub_zero]
    exact ofNat_beq_zero (by omega_using [hp])
  · intro hb
    obtain h0 : D p ≠ 0 := of_decide_eq_false hb
    refine wp_cmp (op2_reg _ _) fun t ft zt => WP.block_nil
      ⟨ru.trans (ft.rest _), ft.mem.trans mu, by rw [ft.gpr]; exact u11, by rw [ft.gpr]; exact u10, ?_⟩
    rw [zt, BitVec.sub_self, topZ, ite_eq_right h0]
    rfl

/-- The top digit: its position (`Slide.topPos`) in `r11`, and the digit in `r10`. -/
theorem topDigit_ok {D : Nat → Nat} {b : BitVec 32} {s : State} (hc : Ctx b s)
    (hg : ∀ q < 256, s.mem (State.addr b + BitVec.ofNat 64 (DIG + q)) = BitVec.ofNat 8 (D q))
    (hD : ∀ q, D q < 16) :
    WP isa topDigit s fun t => Rest [.r3, .r10, .r11] s t ∧ t.mem = s.mem ∧
      t.gpr .r11 = BitVec.ofNat 32 (Proof.Ed25519.Slide.topPos D 256) ∧
      t.gpr .r10 = BitVec.ofNat 32 (D (Proof.Ed25519.Slide.topPos D 256)) := by
  rw [topDigit]
  refine WP.seq (wp_mov (op2_imm (by decide)) fun u uu => WP.block_nil ?_)
  refine WP.loop (M := isa) (Inv := fun n t => 0 < n ∧ n ≤ 256 ∧ Rest [.r3, .r10, .r11] s t ∧ t.mem = s.mem ∧
    t.gpr .r11 = BitVec.ofNat 32 n ∧ Proof.Ed25519.Slide.topPos D 256 = Proof.Ed25519.Slide.topPos D n)
    ?_ 256 u ⟨by decide, le_rfl, uu.rest (by decide), uu.mem, uu.gpr, rfl⟩
  intro n x ⟨n0, n256, rx, mx, x11, xt⟩
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega_using [n0]⟩
  refine WP.mono (topStep_ok (hc.of_rest rx (by decide)) (by omega_using [n256]) x11
    (fun q hq => by rw [mx]; exact hg q hq) (hD p)) fun t ⟨rt, mt, t11, t10, tz⟩ => ?_
  rw [topZ] at tz
  by_cases h0 : D p = 0
  · rw [ite_eq_left h0] at tz
    rw [Proof.Ed25519.Slide.topPos_succ_zero h0] at xt
    by_cases hp0 : p = 0
    · subst hp0
      refine .inl ⟨by show some (!t.z) = _; rw [tz]; rfl, rx.trans rt, mt.trans mx, ?_, ?_⟩
      · rw [t11, xt]; rfl
      · rw [t10, xt]; rfl
    · exact .inr ⟨by show some (!t.z) = _; rw [tz, decide_eq_false hp0]; rfl, p, by omega_using [],
        by omega_using [hp0], by omega_using [n256], rx.trans rt, mt.trans mx, t11, xt⟩
  · rw [ite_eq_right h0] at tz
    rw [Proof.Ed25519.Slide.topPos_succ_ne h0] at xt
    exact .inl ⟨by show some (!t.z) = _; rw [tz]; rfl, rx.trans rt, mt.trans mx, by rw [t11, xt],
      by rw [t10, xt]⟩

/-- The sum's start: the top digit's entry, or the identity. -/
theorem slideStart_ok {a : Spec.Ed25519.Point} {D : Nat → Nat} {b : BitVec 32} {p₀ : Nat} {s : State}
    (hc : Ctx b s) (hl : AllLim s.mem b) (hd : env s.mem b 16 = Spec.Ed25519.d)
    (ht : ∀ j < 8, tablePoint s.mem b (TBA + 128 * j) = oddMul a j)
    (hg : ∀ q < 256, s.mem (State.addr b + BitVec.ofNat 64 (DIG + q)) = BitVec.ofNat 8 (D q))
    (h11 : s.gpr .r11 = BitVec.ofNat 32 p₀) (h10 : s.gpr .r10 = BitVec.ofNat 32 (D p₀))
    (hD : D p₀ = 0 ∨ (D p₀ % 2 = 1 ∧ D p₀ < 16)) :
    WP isa slideStart s fun t => AccKeep b s t ∧ SlideAt a D b p₀ p₀ t := by
  obtain hlt : D p₀ < 16 := by rcases hD with e | e <;> omega_using [e]
  rw [slideStart]
  refine WP.seq (wp_cmp (op2_imm (by decide)) fun u fu zu => WP.block_nil ?_)
  obtain ku : AccKeep b s u := AccKeep.of_rest (fu.rest []) (by decide) fu.mem
  obtain cu := ku.ctx hc
  obtain hz : isa.eval .ne u = some (!decide (D p₀ = 0)) := by
    show some (!u.z) = _
    rw [zu, h10]
    show some (!(BitVec.ofNat 32 (D p₀) - 0#32 == 0#32)) = _
    rw [BitVec.sub_zero]
    exact congrArg (fun z => some (!z)) (ofNat_beq_zero (by omega_using [hlt]))
  apply WP.ite (!decide (D p₀ = 0)) hz
  · intro hb
    obtain hne : D p₀ ≠ 0 := by simpa using hb
    obtain ⟨ho, _⟩ := hD.resolve_left hne
    obtain hj : (D p₀ - 1) / 2 < 8 := by omega_using [hlt]
    rw [WP.block_append_iff]
    refine WP.mono (digitAddr_ok cu hlt ho (by rw [fu.gpr]; exact h10)) fun v ⟨vr, vm, vp⟩ => ?_
    obtain cv := cu.of_rest vr (by decide)
    refine WP.mono (pointFromTable_ok cv (by rw [vm, fu.mem]; exact hl) vp (by simp only [TBA]; omega_using [])
      (by simp only [TBA]; omega_using [hj])) fun t ⟨tp, tl, tk⟩ => ?_
    obtain kt : AccKeep b s t :=
      ku.trans ((AccKeep.of_rest vr (by decide) vm).trans (AccKeep.of_table tk (by decide) (by decide)))
    refine ⟨kt, kt.ctx hc, tl, by rw [tk.high 16 (by decide), vm, fu.mem]; exact hd, ?_,
      (kt.rest.gpr _ (by decide)).trans h11, fun j hj => by rw [tab_keep kt.frame hj]; exact ht j hj,
      fun q hq => by rw [dig_keep kt.frame hq]; exact hg q hq⟩
    rw [tp, vm, fu.mem, ht _ hj, Nat.sub_self, slideVal_zero, ite_eq_right hne]
  · intro hb
    obtain h0 : D p₀ = 0 := by simpa using hb
    refine WP.mono (fieldCode_ok _ cu (by rw [fu.mem]; exact hl)) fun t ⟨tk, tl, te⟩ => ?_
    obtain kt : AccKeep b s t := ku.trans (AccKeep.of_keep tk)
    refine ⟨kt, kt.ctx hc, tl, ?_, ?_, (kt.rest.gpr _ (by decide)).trans h11,
      fun j hj => by rw [tab_keep kt.frame hj]; exact ht j hj,
      fun q hq => by rw [dig_keep kt.frame hq]; exact hg q hq⟩
    · rw [te, fu.mem]
      exact hd
    · rw [te, constPoint_eval, Nat.sub_self, slideVal_zero, ite_eq_left h0]

/-- The test of the top digit's position. -/
theorem slideTest_ok {a : Spec.Ed25519.Point} {D : Nat → Nat} {b : BitVec 32} {p₀ : Nat} {s : State}
    (h : SlideAt a D b p₀ p₀ s) (hp₀ : p₀ < 256) :
    WP isa (.block [.cmp .r11 (.imm 0)]) s fun u => MulKeep b 1632 6144 s u ∧ SlideAt a D b p₀ p₀ u ∧
      u.z = decide (p₀ = 0) := by
  refine wp_cmp (op2_imm (by decide)) fun u fu zu => WP.block_nil ?_
  obtain ku : MulKeep b 1632 6144 s u := MulKeep.of_rest (fu.rest []) (by decide) fu.mem
  refine ⟨ku, ⟨ku.ctx h.ctx, by rw [fu.mem]; exact h.lim, by rw [fu.mem]; exact h.d, by rw [fu.mem]; exact h.acc,
    by rw [fu.gpr]; exact h.r11, fun j hj => by rw [fu.mem]; exact h.tab j hj,
    fun q hq => by rw [fu.mem]; exact h.dig q hq⟩, ?_⟩
  rw [zu, h.r11]
  show (BitVec.ofNat 32 p₀ - 0#32 == 0#32) = _
  rw [BitVec.sub_zero]
  exact ofNat_beq_zero (by omega_using [hp₀])

/-- The digits below the top one's, if its position is not 0. -/
theorem slideRest_ok {a : Spec.Ed25519.Point} {D : Nat → Nat} {b : BitVec 32} {p₀ : Nat} {s : State}
    (h : SlideAt a D b p₀ p₀ s) (hp₀ : p₀ < 256) (hD : ∀ q, D q = 0 ∨ (D q % 2 = 1 ∧ D q < 16)) :
    WP isa (slideRest umaal) s fun t => MulKeep b 1632 6144 s t ∧ SlideAt a D b p₀ 0 t := by
  rw [slideRest]
  refine WP.seq (WP.mono (slideTest_ok h hp₀) fun u ⟨ku, hu, zu⟩ => ?_)
  apply WP.ite (!decide (p₀ = 0)) (by show some (!u.z) = _; rw [zu])
  · intro hb
    obtain hne : p₀ ≠ 0 := by simpa using hb
    exact WP.mono (slideLoop_ok hu (by omega_using [hne]) (by omega_using [hp₀]) hD) fun t ⟨tk, ta⟩ =>
      ⟨ku.trans tk, ta⟩
  · intro hb
    obtain h0 : p₀ = 0 := by simpa using hb
    subst h0
    exact WP.block_nil ⟨ku, hu⟩

/-- `[k]A` into slots 0–3, for `A` in slots 0–3 and the 32 bytes of `k` at `r12`. -/
theorem publicMul_ok {s : State} {b ptr : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    (hp : s.gpr .r12 = ptr) (hi : VerifyInput b ptr 32 s) :
    WP isa (publicMul umaal) s fun t => PointKeep b s t ∧ AllLim t.mem b ∧ env t.mem b 16 = Spec.Ed25519.d ∧
      point (env t.mem b) 0 1 2 3 = slide (point (env s.mem b) 0 1 2 3)
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32)) := by
  rw [publicMul]
  refine WP.seq (strLow_ok hc (d := 52) (by decide) .r12 fun u hu => WP.block_nil ?_)
  obtain uf : Frame [⟨State.addr b + BitVec.ofNat 64 52, 4⟩] s.mem u.mem := by
    rw [hu.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain uk : PointKeep b s u := PointKeep.of_small (hu.rest []) (by decide) uf (by decide) (by decide)
  obtain ue := smallFrame_env uf (by decide)
  obtain up : lw u.mem b 52 = ptr := by rw [hu.mem]; exact (Mem.readW_writeW_self32 _ _ _).trans hp
  refine WP.seq (WP.mono (oddTable_ok (uk.ctx hc) (smallFrame_lim uf (by decide) hl)) fun v ⟨vk, vt⟩ => ?_)
  rw [ue] at vt
  obtain kv : PointKeep b u v := PointKeep.of_mul vk
  obtain iu := hi.keep (VerifyKeep.of_point uk)
  obtain pv : lw v.mem b 52 = ptr := (vk.word (by decide) (by decide) 52 (.inr rfl)).trans up
  refine WP.seq (WP.mono (recode_ok vt.ctx pv (iu.keep (VerifyKeep.of_point kv))) fun w ⟨wr, wf, wd⟩ => ?_)
  rw [(iu.bytes (VerifyKeep.of_point kv)).trans (hi.bytes (VerifyKeep.of_point uk))] at wd
  obtain kw : PointKeep b v w := PointKeep.of_small wr (by decide) wf (by decide) (by decide)
  obtain cw := kw.ctx vt.ctx
  obtain tw : TabDone (point (env s.mem b) 0 1 2 3) b w.mem := TabDone.digits ⟨vt.lim, vt.d, vt.tab⟩ wf
  obtain hD := Proof.Ed25519.Slide.digits_odd 256
    (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32))
  refine WP.seq (WP.mono (topDigit_ok cw wd fun q => by rcases hD q with e | e <;> omega_using [e])
    fun x ⟨xr, xm, x11, x10⟩ => ?_)
  obtain kx : PointKeep b w x := PointKeep.of_mul (MulKeep.of_rest xr (by decide) xm)
  rw [← xm] at tw wd
  refine WP.seq (WP.mono (slideStart_ok (kx.ctx cw) tw.1 tw.2.1 tw.2.2 wd x11 x10 (hD _)) fun y ⟨yk, ya⟩ => ?_)
  refine WP.mono (slideRest_ok ya (Proof.Ed25519.Slide.topPos_lt _ (by decide)) hD) fun t ⟨tk, ta⟩ => ?_
  refine ⟨uk.trans (kv.trans (kw.trans (kx.trans ((PointKeep.of_mul (MulKeep.of_powers (PowersKeep.of_acc yk))).trans
    (PointKeep.of_mul tk))))), ta.lim, ta.d, ?_⟩
  rw [ta.acc, Nat.sub_zero]
  rfl

end VG.Proof.Ed25519.Arm
end

/-! The right side reads all 512 challenge bits before the strict equation. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

variable {umaal : Bool}

theorem verifyRhs_ok {b pk sig challenge : BitVec 32} {s : State}
    (hc : VerifyContext b pk sig challenge s) (hl : AllLim s.mem b) :
    WP isa (verifyRhs umaal) s fun t => VerifyKeep b s t ∧ AllLim t.mem b ∧
      t.gpr .r9 = BitVec.ofNat 32 (Spec.Ed25519.pointEqual (tablePoint s.mem b 8032)
        (Spec.Ed25519.pointAdd (tablePoint s.mem b 7904)
          (slide (tablePoint s.mem b 7776)
            (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr challenge) 32))))).toNat := by
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
  refine WP.seq (WP.mono (publicMul_ok cc.ctx (cm ▸ al) cp' ci) fun d ⟨dk, dl, dd, dp⟩ => ?_)
  obtain kd := cpk.trans dk
  obtain dp' : point (env d.mem b) 0 1 2 3 = slide (tablePoint s.mem b 7776)
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr challenge) 32)) := by
    rw [(hc.challengeInput.prefix (n := 32) (by decide)).bytes (VerifyKeep.of_acc kc), capp] at dp
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

variable {umaal : Bool}

theorem verifyLhs_ok {b pk sig challenge T : BitVec 32} {s : State}
    (hc : VerifyContext b pk sig challenge s) (hl : AllLim s.mem b) (ht : VerifyTbl b T s) :
    WP isa (verifyLhs umaal) s fun t => VerifyKeep b s t ∧ AllLim t.mem b ∧
      Proof.Ed25519.Rep (tablePoint t.mem b 8032)
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr (sig + 32)) 32) • Proof.Ed25519.baseAff) ∧
      tablePoint t.mem b 7776 = tablePoint s.mem b 7776 ∧
      tablePoint t.mem b 7904 = tablePoint s.mem b 7904 := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono_syms (loadHeader_ok hc.ctx 8164 (by decide)) fun a ⟨ar, am, ap⟩ sya => ?_
  refine WP.mono_syms (addInput32_ok a) fun c ⟨cr, cm, cp⟩ syc => ?_
  obtain kc : PointKeep b s c := ⟨(ar.mono (by decide)).trans (cr.mono (by decide)), by
    rw [cm, am]; exact Frame.refl _ _⟩
  obtain cc := hc.keep (VerifyKeep.of_point kc)
  have ci := cc.sigInput.suffix32
  obtain cp' : c.gpr .r12 = sig + 32 := by rw [cp, ap, hc.sigHeader]
  obtain cT : TblAt c T := ht.tbl.of_frame (L := []) (by rw [kc.rest.rd, kc.rest.wr])
    (by rw [cm, am]; exact Frame.refl _ _) (fun _ hr => absurd hr List.not_mem_nil)
  refine WP.seq (WP.mono (combMultiply_ok cc.ctx (by rw [cm, am]; exact hl) cp' ci.fit ci.readable ci.separate
    cT ((congrFun (syc.trans sya) _).trans ht.sym) ht.apart) fun e ⟨ek, el, ep⟩ => ?_)
  obtain ke := kc.trans ek
  rw [(hc.sigInput.suffix32).bytes (VerifyKeep.of_point kc)] at ep
  refine WP.mono (pointTableWrite_ok (ke.ctx hc.ctx) el 8032 (by decide) (by decide))
    fun t ⟨tk, tl, _, tp⟩ => ?_
  refine ⟨(VerifyKeep.of_point ke).trans (VerifyKeep.of_powers tk (by decide) (by decide)), tl,
    tp ▸ ep, ?_, ?_⟩
  · exact (tk.frame.point (by decide) (.inl (by decide)) (by decide) (by decide)).trans
      (ke.table (by decide) (by decide))
  · exact (tk.frame.point (by decide) (.inl (by decide)) (by decide) (by decide)).trans
      (ke.table (by decide) (by decide))

end VG.Proof.Ed25519.Arm
end

/-! Compose both sides of the exact, uncofactored verification equation. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

variable {umaal : Bool}

def equationResult (m : Mem) (sig challenge : BitVec 32) (a r : Spec.Ed25519.Point) : Bool :=
  Spec.Ed25519.pointEqual
    (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr (sig + 32)) 32)) Spec.Ed25519.basePoint)
    (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr challenge) 64)) a))

theorem verifyEquationPoints_ok {b pk sig challenge T : BitVec 32} {s : State}
    (hc : VerifyContext b pk sig challenge s) (hl : AllLim s.mem b) (ht : VerifyTbl b T s)
    (hA : ∃ A, Proof.Ed25519.Rep (tablePoint s.mem b 7776) A)
    (hR : ∃ R, Proof.Ed25519.Rep (tablePoint s.mem b 7904) R) :
    WP isa (verifyEquationPoints umaal) s fun t => VerifyKeep b s t ∧ AllLim t.mem b ∧
      t.gpr .r9 = BitVec.ofNat 32 (equationResult s.mem sig challenge
        (tablePoint s.mem b 7776) (tablePoint s.mem b 7904)).toNat := by
  refine WP.seq (WP.mono (verifyLhs_ok hc hl ht) fun u ⟨uk, ul, up, ua, ur⟩ => ?_)
  refine WP.mono (verifyRhs_ok (hc.keep uk) ul) fun t ⟨tk, tl, tv⟩ => ?_
  obtain ⟨A, hA⟩ := hA
  obtain ⟨R, hR⟩ := hR
  refine ⟨uk.trans tk, tl, ?_⟩
  rw [ua, ur, (hc.challengeInput.prefix (n := 32) (by decide)).bytes uk] at tv
  have hk := hc.challengeTop
  rw [tv, equationResult, ← decodeLE_low hk]
  rw [← decodeLE_low hk] at hk
  exact congrArg (fun v : Bool => BitVec.ofNat 32 v.toNat) (pointEqual_rep_both up
    (Proof.Ed25519.pointMul_rep _ Proof.Ed25519.basePoint_rep)
    (Proof.Ed25519.pointAdd_rep hR (slide_rep hA hk))
    (Proof.Ed25519.pointAdd_rep hR (Proof.Ed25519.pointMul_rep _ hA)))

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

variable {umaal : Bool}

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
    WP isa (decodeBody umaal) s fun t => DecAt s₀ b pk sig (k + 1) t ∧ t.z = decide (k = 1) := by
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
    WP isa (decodeBoth umaal) s (DecAt s b pk sig 2) := by
  refine WP.seq (WP.mono (decodeStart_ok hc hl) fun a ha => ?_)
  refine WP.loop (M := isa) (Inv := fun m t => ∃ k, k + m = 2 ∧ k < 2 ∧ DecAt s b pk sig k t) ?_ 2 a
    ⟨0, rfl, by decide, ha⟩
  intro m u ⟨k, hkm, hk, hu⟩
  refine WP.mono (decodeBody_ok hc hk hu) fun t ⟨ht, zt⟩ => ?_
  rcases (by omega_arith : k = 0 ∨ k = 1) with rfl | rfl
  · exact .inr ⟨by show some (!t.z) = _; rw [zt]; rfl, 1, by omega_arith, 1, rfl, by decide, ht⟩
  · exact .inl ⟨by show some (!t.z) = _; rw [zt]; rfl, ht⟩

/-- Both decoded, and the equation if both are points. -/
theorem verifyDecode_ok {b pk sig challenge T : BitVec 32} {s : State}
    (hc : VerifyContext b pk sig challenge s) (hl : AllLim s.mem b) (ht : VerifyTbl b T s) :
    WP isa (verifyDecode umaal) s fun t => VerifyKeep b s t ∧
      t.gpr .r9 = BitVec.ofNat 32 (decodedEquation s.mem pk sig challenge).toNat := by
  refine WP.seq (WP.mono_syms (decodeBoth_ok hc hl) fun a ha sya => ?_)
  obtain ca := (hc.keep ha.keep).ctx
  have test : WP isa (.block [.ldr .r9 .r0 DOK, .cmp .r9 (.imm 0)]) a fun d =>
      VerifyKeep b s d ∧ d.mem = a.mem ∧ isa.eval .ne d = some (decOk s.mem pk sig 2) :=
    ldrLow_ok ca (d := DOK) (by decide) .r9 fun c hc' => wp_cmp (op2_imm (by decide)) fun d hd hz =>
      WP.block_nil ⟨ha.keep.trans (VerifyKeep.of_rest ((hc'.rest (ws := [.r9]) (by decide)).trans
        (hd.rest _)) (by decide) (by rw [hd.mem, hc'.mem])), by rw [hd.mem, hc'.mem], by
        show some (!d.z) = _
        rw [hz]
        rw [hc'.gpr, ha.ok]
        cases decOk s.mem pk sig 2 <;> rfl⟩
  refine WP.seq (WP.mono_syms test fun d ⟨kd, md, hz⟩ syd => ?_)
  apply WP.ite (decOk s.mem pk sig 2) hz
  · intro hok
    rw [decOk_two, Bool.and_eq_true] at hok
    obtain ⟨a0, ha0⟩ := Option.isSome_iff_exists.mp hok.1
    obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.mp hok.2
    obtain tA : tablePoint d.mem b 7776 = a0 := by rw [md]; exact ha.pts 0 (by decide) a0 ha0
    obtain tR : tablePoint d.mem b 7904 = r0 := by rw [md]; exact ha.pts 1 (by decide) r0 hr0
    refine WP.mono (verifyEquationPoints_ok (hc.keep kd) (by rw [md]; exact ha.lim)
      (ht.keep kd (syd.trans sya))
      (by rw [tA]; exact Proof.Ed25519.decodePoint_rep (show Spec.Ed25519.decodePoint
        (Spec.Ed25519.bytesAt s.mem (State.addr pk) 32) = some a0 from ha0))
      (by rw [tR]; exact Proof.Ed25519.decodePoint_rep (show Spec.Ed25519.decodePoint
        (Spec.Ed25519.bytesAt s.mem (State.addr sig) 32) = some r0 from hr0))) fun t ⟨tk, _, tv⟩ =>
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

variable {umaal : Bool}

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

theorem verifyBody_ok {b pk sig challenge T : BitVec 32} {s : State}
    (hc : VerifyContext b pk sig challenge s) (ht : VerifyTbl b T s) :
    WP isa (verifyBody umaal) s fun t => VerifyKeep b s t ∧ t.gpr .r9 = BitVec.ofNat 32
      (Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt s.mem (State.addr pk) 32)
        (Spec.Ed25519.bytesAt s.mem (State.addr sig) 64) (Spec.Ed25519.bytesAt s.mem (State.addr challenge) 64)).toNat := by
  refine WP.seq (WP.mono_syms (verifyScalar_ok hc) fun u ⟨uk, uz⟩ syu => ?_)
  apply WP.ite _ (congrArg some uz)
  · intro hy
    refine WP.seq (WP.mono_syms (initFields_ok (uk.ctx hc.ctx)) fun v ⟨vk, vl, _⟩ syv => ?_)
    obtain kv := uk.trans (VerifyKeep.of_keep vk)
    refine WP.mono (verifyDecode_ok (hc.keep kv) vl (ht.keep kv (syv.trans syu))) fun t ⟨tk, tv⟩ => ?_
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
    s.rd = [pk, sig, challenge, TBL (s.syms combSym)] ∧ s.wr = [ws] ∧ pk.Disjoint ws ∧ sig.Disjoint ws ∧
      challenge.Disjoint ws ∧ (s.gpr .r0).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .r1).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 64 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32 ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 64) < 2 ^ 256 ∧
      (s.syms combSym).toNat + 98304 ≤ 2 ^ 32 ∧
      (∀ j < 64 * 192, s.mem.readW (State.addr (s.syms combSym) + BitVec.ofNat 64 (8 * j)) 64 = combWord j) ∧
      (TBL (s.syms combSym)).Disjoint ws
  post s t := (t.gpr .r0).toNat = if Spec.Ed25519.verifyEquation
    (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r0)) 32)
    (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 64)
    (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 64) then 1 else 0
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧
    s.gpr .r2 = t.gpr .r2 ∧ s.gpr .r3 = t.gpr .r3 ∧ s.syms combSym = t.syms combSym ∧
    (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r0)) 32 ++
      Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 64 ++
      Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 64).map (·.toNat) =
    (Spec.Ed25519.bytesAt t.mem (State.addr (t.gpr .r0)) 32 ++
      Spec.Ed25519.bytesAt t.mem (State.addr (t.gpr .r1)) 64 ++
      Spec.Ed25519.bytesAt t.mem (State.addr (t.gpr .r2)) 64).map (·.toNat)

structure VerifyPre (s : State) : Prop where
  rd : s.rd = [⟨State.addr (s.gpr .r0), 32⟩, ⟨State.addr (s.gpr .r1), 64⟩, ⟨State.addr (s.gpr .r2), 64⟩,
    TBL (s.syms combSym)]
  wr : s.wr = [⟨State.addr (s.gpr .r3), 8192⟩]
  pk_ws : (⟨State.addr (s.gpr .r0), 32⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 8192⟩
  sig_ws : (⟨State.addr (s.gpr .r1), 64⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 8192⟩
  challenge_ws : (⟨State.addr (s.gpr .r2), 64⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 8192⟩
  f0 : (s.gpr .r0).toNat + 32 ≤ 2 ^ 32
  f1 : (s.gpr .r1).toNat + 64 ≤ 2 ^ 32
  f2 : (s.gpr .r2).toNat + 64 ≤ 2 ^ 32
  f3 : (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32
  top : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 64) < 2 ^ 256
  tfit : (s.syms combSym).toNat + 98304 ≤ 2 ^ 32
  words : ∀ j < 64 * 192, s.mem.readW (State.addr (s.syms combSym) + BitVec.ofNat 64 (8 * j)) 64 = combWord j
  tbl_ws : (TBL (s.syms combSym)).Disjoint ⟨State.addr (s.gpr .r3), 8192⟩

theorem VerifyPre.of {s : State} (h : verifyLocal.pre s) : VerifyPre s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem VerifyPre.tbl {s : State} (h : VerifyPre s) : TblAt s (s.syms combSym) :=
  ⟨h.tfit, ⟨_, by rw [h.rd]; simp, Region.contains_self _ _⟩, h.words⟩

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

variable {umaal : Bool}

theorem verifyEquation_correct {s : State} (h : VerifyPre s) :
    WP isa (verifyEquation umaal) s fun t => abiPreserved s t ∧ verifyLocal.post s t := by
  refine WP.seq (WP.mono_syms (verifySetup_ok h) fun u ⟨uc, us, ul, uk, uf⟩ syu => ?_)
  obtain ut : VerifyTbl (s.gpr .r3) (s.syms combSym) u :=
    ⟨h.tbl.of_frame (by rw [uk.rd, uk.wr]) uf fun r hr => by rw [List.mem_singleton.mp hr]; exact h.tbl_ws,
      h.tbl_ws, congrFun syu _⟩
  refine WP.seq (WP.mono (verifyBody_ok uc ut) fun v ⟨vk, vv⟩ => ?_)
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

structure VerifyPublic (m : Mem) (T b pk sig challenge : BitVec 32) (s : State) : Prop where
  ctx : VerifyContext b pk sig challenge s
  tbl : VerifyTbl b T s
  pkBytes : Spec.Ed25519.bytesAt s.mem (State.addr pk) 32 = Spec.Ed25519.bytesAt m (State.addr pk) 32
  sigBytes : Spec.Ed25519.bytesAt s.mem (State.addr sig) 64 = Spec.Ed25519.bytesAt m (State.addr sig) 64
  challengeBytes : Spec.Ed25519.bytesAt s.mem (State.addr challenge) 64 = Spec.Ed25519.bytesAt m (State.addr challenge) 64

theorem VerifyPublic.keep {m : Mem} {T b pk sig challenge : BitVec 32} {s t : State}
    (h : VerifyPublic m T b pk sig challenge s) (hk : VerifyKeep b s t) (hsy : t.syms = s.syms) :
    VerifyPublic m T b pk sig challenge t :=
  ⟨h.ctx.keep hk, h.tbl.keep hk hsy, (h.ctx.pkInput.bytes hk).trans h.pkBytes,
    (h.ctx.sigInput.bytes hk).trans h.sigBytes, (h.ctx.challengeInput.bytes hk).trans h.challengeBytes⟩

theorem VerifyPublic.rBytes {m : Mem} {T b pk sig challenge : BitVec 32} {s : State}
    (h : VerifyPublic m T b pk sig challenge s) :
    Spec.Ed25519.bytesAt s.mem (State.addr sig) 32 = Spec.Ed25519.bytesAt m (State.addr sig) 32 := by
  obtain he := congrArg (List.take 32) h.sigBytes
  simpa only [signatureBytes_take] using he

theorem VerifyPublic.sBytes {m : Mem} {T b pk sig challenge : BitVec 32} {s : State}
    (h : VerifyPublic m T b pk sig challenge s) :
    Spec.Ed25519.bytesAt s.mem (State.addr (sig + 32)) 32 = Spec.Ed25519.bytesAt m (State.addr (sig + 32)) 32 := by
  obtain ep : State.addr (sig + (32 : BitVec 32)) = State.addr sig + BitVec.ofNat 64 32 :=
    addr_add (k := 32) (by have := h.ctx.sigInput.fit; omega_arith)
  rw [ep]
  obtain he := congrArg (List.drop 32) h.sigBytes
  simpa only [signatureBytes_drop] using he

end VG.Proof.Ed25519.Arm
