module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndFrame
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on AArch64: the first block

The frames and the scan's registers after `setup` (`Before`, `setup_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Rnd

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Random

/-- The registers but `rs` are kept. -/
def Keeps (rs : List Reg) (s t : State) : Prop := ∀ r, r ∉ rs → t.gpr r = s.gpr r

theorem Keeps.trans {rs rs' : List Reg} {s t u : State} (h₁ : Keeps rs s t) (h₂ : Keeps rs' t u) :
    Keeps (rs ++ rs') s u := fun r hr => by
  rw [List.mem_append, not_or] at hr
  exact (h₂ r hr.2).trans (h₁ r hr.1)

theorem Keeps.mono {rs rs' : List Reg} {s t : State} (h : Keeps rs s t) (hs : ∀ r ∈ rs, r ∈ rs') :
    Keeps rs' s t := fun r hr => h r fun h' => hr (hs r h')

theorem Keeps.refl (rs : List Reg) (s : State) : Keeps rs s s := fun _ _ => rfl

/-- In the frames, at a point of the body: what the body keeps. -/
structure InFrame (s t : State) : Prop where
  sp : t.sp = Q s
  rd : t.rd = s.rd
  wr : t.wr = (entered s).wr
  v : t.v = s.v
  fr : Frame [⟨Q s, 1104⟩] s.mem t.mem
  ps : t.mem.readW (off (Q s) oPs) 64 = BitVec.ofNat 64 (psLen s)
  lr : t.mem.readW (off (Q s) 1088) 64 = s.gpr .x30

/-- After `setup`. -/
structure Before (s t : State) : Prop extends InFrame s t where
  x11 : t.gpr .x11 = stackArg s 1
  x12 : t.gpr .x12 = stackArg s 2
  x14 : t.gpr .x14 = off (Q s) oBuf
  x15 : t.gpr .x15 = BitVec.ofNat 64 (psLen s)
  x16 : t.gpr .x16 = BitVec.ofNat 64 (psLen s)
  keep : Keeps [.x9, .x11, .x12, .x14, .x15, .x16] s t

theorem psLen_bv {P : Nat} {s : State} (hp : RPre P s) :
    s.gpr .x4 - stackArg s 0 - BitVec.ofNat 64 3 = BitVec.ofNat 64 (psLen s) := by
  have := hp.hml
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, psLen, kOf]
  omega

theorem args_in {P : Nat} {s : State} (hp : RPre P s) {j : Nat} (hj : j < 7) :
    InRegions ((entered s).rd ++ (entered s).wr) (Q s + BitVec.ofNat 64 (1104 + 8 * j)) 8 :=
  ⟨argsR s, by rw [entered_rd, hp.hrd]; simp, by show (argsR s).Contains (off (Q s) (1104 + 8 * j)) 8; rw [← stackArgAddr_Q]; exact arg_contains s hj⟩

theorem frame_in {s : State} {d n : Nat} (h : d + n ≤ frameBytes) :
    InRegions (entered s).wr (Q s + BitVec.ofNat 64 d) n :=
  ⟨⟨Q s, frameBytes⟩, by rw [entered_wr]; simp, Offset.contains_base _ h (by unfold frameBytes at h; omega)⟩

theorem setup_ok {P : Nat} {s : State} (hp : RPre P s) : WP isa (.block setup) (entered s) (Before s) := by
  have a0 : InRegions ((entered s).rd ++ (entered s).wr) (Q s + BitVec.ofNat 64 1104) 8 := args_in hp (j := 0) (by decide)
  have a1 : InRegions ((entered s).rd ++ (entered s).wr) (Q s + BitVec.ofNat 64 1112) 8 := args_in hp (j := 1) (by decide)
  have a2 : InRegions ((entered s).rd ++ (entered s).wr) (Q s + BitVec.ofNat 64 1120) 8 := args_in hp (j := 2) (by decide)
  have m0 : (entered s).mem.read (Q s + BitVec.ofNat 64 1104) 8 = stackArg s 0 := arg_read s (j := 0) (by decide)
  have m1 : (entered s).mem.read (Q s + BitVec.ofNat 64 1112) 8 = stackArg s 1 := arg_read s (j := 1) (by decide)
  have m2 : (entered s).mem.read (Q s + BitVec.ofNat 64 1120) 8 = stackArg s 2 := arg_read s (j := 2) (by decide)
  have w48 : InRegions (entered s).wr (Q s + BitVec.ofNat 64 48) 8 := frame_in (by decide)
  have hps := psLen_bv hp
  apply WP.of_runBlock
  simp only [setup, arg, frameBytes, oPs, oBuf, runBlock_cons, runStep_some, runBlock_nil, reduceExec,
    State.load, State.store, State.read, Size.bits, BitVec.setWidth_eq, Option.map_some,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, ite_true, entered_sp,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq,
    ite_false, a0, a1, a2, m0, m1, m2, w48, Option.some.injEq, exists_eq_left']
  have hv : (s.gpr .x4 - stackArg s 0 - 3#64).setWidth 64 = BitVec.ofNat 64 (psLen s) := by
    rw [BitVec.setWidth_eq]; exact hps
  have hQ := Q_toNat hp
  have hlr : (entered s).mem.readW (Q s + BitVec.ofNat 64 1088) 64 = s.gpr .x30 := by
    rw [entered_mem]; exact Mem.readW_writeW_self64 _ _ _
  refine ⟨⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · show Frame _ s.mem ((entered s).mem.write _ 8 _)
    rw [entered_mem]
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).write (List.mem_singleton_self _) _ ?_
    · exact Offset.contains_base _ (by decide) (by omega)
    · exact Offset.contains_base _ (by decide) (by omega)
  · show ((entered s).mem.write _ 8 _).readW _ 64 = _
    have := Mem.readW_writeW_self (entered s).mem (Q s + BitVec.ofNat 64 48) 8
      ((s.gpr .x4 - stackArg s 0 - 3#64).setWidth 64) (by decide)
    simp only [Mem.writeW, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq] at this
    simp only [oPs, off, entered_gpr]
    rw [this, hps]
  · show ((entered s).mem.write _ 8 _).readW _ 64 = _
    rw [Bytes.readW_write_sep (Offset.sep _ (.inr (by decide)) (by decide) (by decide)) (by decide)]
    exact hlr
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, entered_gpr]
    exact hps
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, entered_gpr,
      BitVec.or_self]
    exact hps
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h9, h11, h12, h14, h15, h16⟩ := hr
    simp only [RegUpd.gpr_write, h9, h11, h12, h14, h15, h16, ite_false, entered_gpr]

end VG.Proof.RsaPkcs1Enc.AArch64.Rnd
