module

-- separate module: an iteration's arithmetic (`Step`) is checked apart from the function around it
public import VerifiedGarbage.Proof.X25519.AArch64.Step
public import VerifiedGarbage.Proof.X25519.AArch64.Top
public import VerifiedGarbage.Proof.Ed25519.AArch64.Divstep
public import VerifiedGarbage.Proof.X25519.Contract
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ed25519.AArch64.DecodeBits
import VerifiedGarbage.Proof.Ed25519.AArch64.PointEncode
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarMemory
import VerifiedGarbage.Proof.Ed25519.AArch64.Codec
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.X25519.AArch64.LadderLit
meta import VerifiedGarbage.Proof.X25519.AArch64.LadderLit
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.X25519.Invert

@[expose] public section

namespace VG.Proof.X25519.AArch64.Ladder

open VG VG.AArch64 VG.Impl.X25519.AArch64.Ladder VG.Impl.Ed25519.AArch64 VG.Impl.Ed25519.AArch64.Pairs
open VG.Impl.X25519.AArch64 (BITS)
open VG.Impl.X25519.AArch64.Squares VG.Proof.X25519.AArch64.Squares
open VG.Proof.Ed25519.AArch64 VG.Proof.Ed25519.AArch64.Pairs VG.Proof.Ed25519.Word64 VG.Proof.X25519
open VG.Spec.X25519 (Fe P decodeScalar25519 decodeUCoordinate ladderStep)

/-! ## One iteration -/

/-- Bit `t < 255` of the scalar `k`, and 0 beyond. -/
def bitOf (k t : Nat) : Nat := if t < 255 then bit k t else 0

theorem bitOf_lt (k t : Nat) : bitOf k t < 2 := by
  unfold bitOf
  split
  · exact Nat.lt_succ_of_le (bit_le k t)
  · decide

/-- The ladder's `swap` before the iteration for bit `n` is bit `n + 1`. -/
theorem swap_eq (k : Nat) (x1 : Fe) {n : Nat} (hn : n < 255) : (ladderAfter k x1 (n + 1)).swap = bitOf k (n + 1) := by
  unfold bitOf
  split
  · rename_i h; rw [ladderAfter_step k x1 h]; rfl
  · rw [show n = 254 by omega_using [hn, ‹¬n + 1 < 255›]]; rfl

/-- The field elements of the ladder in slots 0–4. -/
def Holds (m : Mem) (base : Addr) (x1 : Fe) (l : Spec.X25519.Ladder) : Prop :=
  env m base 0 = x1 ∧ env m base 1 = l.x2 ∧ env m base 2 = l.z2 ∧ env m base 3 = l.x3 ∧ env m base 4 = l.z3

private theorem xor_one : ∀ a < 2, ∀ b < 2, (a ^^^ b = 1) ↔ ¬ b = a := by decide

/-- The loop's invariant before the iteration for bit `n - 1`. -/
structure Inv (s₀ : State) (base : Addr) (k : Nat) (x1 : Fe) (n : Nat) (s : State) : Prop where
  scr : Scr s base false
  zero : s.gpr .x10 = 0
  count : s.gpr .x19 = BitVec.ofNat 64 n
  bits : BitsAt s.mem base (bitOf k)
  small : Sm4 s.mem base
  consts : Consts s.mem base
  holds : Holds s.mem base x1 (ladderAfter k x1 n)
  gpr : ∀ r, r ∉ .x19 :: lclob → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : Outside base 64 1056 s₀.mem s.mem

theorem bitsAt_outside {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (hn : o + n ≤ BITS)
    {b : Nat → Nat} (hb : BitsAt m base b) : BitsAt m' base b := fun t ht => by
  have hB : BITS = 1984 := rfl
  rw [h _ (Or.inr (by rw [ofs_off' base (by omega_using [hB, ht])]; omega_using [hn])), hb t ht]

theorem step_ok {s₀ s : State} {base : Addr} {k : Nat} {x1 : Fe} {n : Nat} (hn : n < 255)
    (h : Inv s₀ base k x1 (n + 1) s) : WP isa (.block step) s (Inv s₀ base k x1 n) := by
  rw [step, WP.block_append_iff]
  refine WP.mono (front_ok h.scr h.zero h.small h.bits hn (bitOf_lt k n) (bitOf_lt k (n + 1)) h.count)
    fun a ⟨a5, a6, a7, a8, a0, a19, a10, ag, ard, awr, asp, am⟩ => ?_
  obtain hsa : Scr a base false := ⟨(ag _ (by decide)).trans h.scr.x0, awr ▸ h.scr.wr, h.scr.nowrap⟩
  obtain am' : Outside base 64 1056 s.mem a.mem := am.mono (by decide) (by decide)
  refine WP.mono (back_ok hsa a10 (h.consts.outside am')) fun t ⟨t0, t1, t2, t3, t4, ts, tl⟩ => ?_
  obtain om := am'.trans tl.mem
  refine ⟨tl.scr hsa, tl.zero a10, (tl.gpr _ (by decide)).trans a19, bitsAt_outside om (by decide) h.bits, ts, h.consts.outside om, ?_,
    fun r hr => ((tl.gpr r fun hm => hr (List.mem_cons_of_mem _ hm)).trans (ag r hr)).trans (h.gpr r hr),
    tl.rd.trans (ard.trans h.rd), tl.wr.trans (awr.trans h.wr), tl.sp.trans (asp.trans h.sp), h.mem.trans om⟩
  obtain ⟨h0, h1, h2, h3, h4⟩ := h.holds
  rw [h1, h2] at a5 a6
  rw [h3, h4] at a5 a6
  rw [h1, h2, h3, h4] at a7 a8
  rw [ladderAfter_step k x1 hn, ladderStep_eq, swap_eq k x1 hn]
  obtain hb : bit k n = bitOf k n := by rw [bitOf, ite_eq_left hn]
  rw [hb]
  obtain hc : ∀ x y : Fe, Spec.X25519.cswap (bitOf k (n + 1) ^^^ bitOf k n) x y =
      if decide (bitOf k n = bitOf k (n + 1)) = true then (x, y) else (y, x) := fun x y => by
    unfold Spec.X25519.cswap
    by_cases hz : bitOf k n = bitOf k (n + 1)
    · rw [ite_eq_right (fun e => (xor_one _ (bitOf_lt k (n + 1)) _ (bitOf_lt k n)).mp e hz),
        ite_eq_left (decide_eq_true hz)]
    · rw [ite_eq_left ((xor_one _ (bitOf_lt k (n + 1)) _ (bitOf_lt k n)).mpr hz),
        ite_eq_right (by simp only [hz, decide_false, Bool.false_eq_true, not_false_eq_true])]
  simp only [hc]
  rw [a5, a6] at t1 t2
  rw [a5, a6, a7, a8] at t3 t4
  rw [a0, h0] at t0 t4
  revert t1 t2 t3 t4
  generalize decide (bitOf k n = bitOf k (n + 1)) = z
  cases z <;> exact fun t1 t2 t3 t4 => ⟨t0, t1, t2, t3, t4⟩

theorem ladder_ok {s : State} {base : Addr} {k : Nat} {x1 : Fe} (h : Inv s base k x1 255 s) :
    WP isa ladder s (Inv s base k x1 0) := by
  rw [ladder]
  apply WP.loop (fun n t => Inv s base k x1 n t ∧ 0 < n ∧ n ≤ 255) (n := 255)
  · intro n t ⟨ht, hn0, hn⟩
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega_using [hn0]⟩
    refine WP.mono (step_ok (by omega_using [hn]) ht) fun u hu => ?_
    obtain hc : isa.eval (.nonzero .x .x19) u = some (decide (j ≠ 0)) := by
      show some (u.read .x .x19 != 0) = _
      rw [read_x, hu.count]
      refine congrArg some ?_
      by_cases hj : j = 0
      · subst hj; rfl
      · rw [decide_eq_true hj, bne_iff_ne]
        intro h0
        have := congrArg BitVec.toNat h0
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn])] at this
        exact hj this
    by_cases hj : j = 0
    · subst hj; exact Or.inl ⟨hc, hu⟩
    · exact Or.inr ⟨by rw [hc, decide_eq_true hj], j, by omega_using [], hu, by omega_using [hj], by omega_using [hn]⟩
  · exact ⟨h, by decide, by decide⟩

/-! ## The setup -/

/-- The precondition, by register: `out` in `x0`, `scalar` in `x1`, `point` in `x2`, `scratch` in `x3`. -/
structure LPre (s : State) : Prop where
  pre : Pre s
  nowrap : (s.gpr .x3).toNat + 4096 ≤ 2 ^ 64

/-- The bits' end, and the pointers moved. -/
def moves : List Instr := [.movz .x .x19 0 0, .strb .x19 .x3 (BITS + 255), mov .x1 .x0, mov .x0 .x3]

theorem moves_ok {b : Addr} {s : State} (hs : Sc b s) :
    WP isa (.block moves) s fun t =>
      t.mem = s.mem.write (off b (BITS + 255)) 1 0 ∧ t.gpr .x1 = s.gpr .x0 ∧ t.gpr .x0 = b ∧
      (∀ r, r ∉ [Reg.x0, .x1, .x19] → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hw : InRegions s.wr (off b (BITS + 255)) 1 :=
    ⟨scR b, hs.wr, Offset.contains_base b (by decide) (by decide)⟩
  apply WP.of_runBlock
  simp only [moves, mov, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.store, State.read,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.wr_write, show 16 * 0 < Size.x.bits from by decide,
    show (0 : Nat) < 4096 from by decide, Nat.mod_one, show BITS + 255 < 4096 * 1 from by decide, and_self,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, hw, hs.x3, BitVec.add_zero,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, trivial, trivial, fun r hr => ?_, rfl, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2.1, hr.2.2, ite_false]

theorem count_ok (s : State) :
    WP isa (.block [.movz .w .x10 0 0, .movz .w .x19 255 0]) s fun t =>
      t.gpr .x10 = 0 ∧ t.gpr .x19 = BitVec.ofNat 64 255 ∧ Keeps [.x10, .x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.w.bits from by decide,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨by decide, by decide, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

private theorem small0 : ∀ i : Fin 22, (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) →
    smallAfterOps [.copy 3 0, .const 1 1, .const 2 0, .const 4 1] (fun i => decide (i = 0)) i = true := by decide

/-- The callee-saved registers' words in the working space. -/
def SavedW (b : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop := ∀ rd ∈ saved, word m b rd.2 = g rd.1

theorem savedW_outside {b : Addr} {g : Reg → BitVec 64} {m m' : Mem} {o n : Nat} (h : Outside b o n m m') (ho : 48 ≤ o)
    (hs : SavedW b g m) : SavedW b g m' := fun rd hrd => by
  rw [h.word (Or.inl (by
    have : rd.2 ≤ 40 := (by decide : ∀ rd ∈ saved, rd.2 ≤ 40) rd hrd
    omega_using [this, ho])) (by
    have : rd.2 ≤ 40 := (by decide : ∀ rd ∈ saved, rd.2 ≤ 40) rd hrd
    omega_using [this]), hs rd hrd]

/-- A frame of the working space's region `[o, o + n)`, as offsets. -/
theorem outside_of_frame {b : Addr} {o n : Nat} (hn : o + n < 2 ^ 64) {m m' : Mem}
    (h : Frame [⟨b + BitVec.ofNat 64 o, n⟩] m m') : Outside b o n m m' := fun x hx => h x fun r hr => by
  rw [List.mem_singleton.mp hr]
  simp only [Region.Contains]
  intro hc
  have := (Offset.lt_iff x b (by omega_using [hn])).mp (show (x - (b + BitVec.ofNat 64 o)).toNat < n by omega_using [hc])
  simp only [ofs] at hx
  omega_using [hx, this]

theorem outside_scR {b : Addr} {o n : Nat} (hn : o + n ≤ 4096) {m m' : Mem} (h : Outside b o n m m') :
    Frame [scR b] m m' := fun x hx => h x (Or.inr (by
  have hc := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hc
  simp only [ofs]
  omega_using [hn, hc]))

/-- The scalar of the bytes at `p`, and the u-coordinate at `q`. -/
abbrev kOf (m : Mem) (p : Addr) : Nat := decodeScalar25519 (Spec.X25519.bytesAt m p 32)
abbrev uOf (m : Mem) (q : Addr) : Fe := toFe (decodeUCoordinate (Spec.X25519.bytesAt m q 32))

theorem setup0_ok {s : State} (hp : LPre s) :
    WP isa (.block setup0) s fun t =>
      Scr t (s.gpr .x3) false ∧ BitsAt t.mem (s.gpr .x3) (bitOf (kOf s.mem (s.gpr .x1))) ∧ Sm4 t.mem (s.gpr .x3) ∧
      Holds t.mem (s.gpr .x3) (uOf s.mem (s.gpr .x2))
        (ladderAfter (kOf s.mem (s.gpr .x1)) (uOf s.mem (s.gpr .x2)) 255) ∧
      SavedW (s.gpr .x3) s.gpr t.mem ∧ t.gpr .x1 = s.gpr .x0 ∧
      (∀ r, r ∉ .x0 :: .x1 :: .x10 :: .x19 :: lclob → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨⟨hrd, hwr, osc, ssc, psc⟩, hn⟩ := hp
  obtain hB : BITS = 1984 := rfl
  obtain ⟨b, hb⟩ : ∃ b, s.gpr .x3 = b := ⟨_, rfl⟩
  rw [hb] at hn hwr osc ssc psc ⊢
  obtain hs : Sc b s := ⟨hb, by rw [hwr]; simp⟩
  rw [show setup0 = VG.Impl.X25519.AArch64.save ++ (VG.Impl.X25519.AArch64.bits ++ (moves ++ (loadY ++
      (store4 (offset 0) ++ fieldCode [.copy 3 0, .const 1 1, .const 2 0, .const 4 1])))) by
    simp only [setup0, moves, List.append_assoc], WP.block_append_iff]
  refine WP.mono (save_ok hs) fun a ⟨wa, fa, ka⟩ => ?_
  obtain hsa := hs.of_kp ka (by decide)
  obtain oa : Outside b 0 48 s.mem a.mem := outside_of_frame (by decide) (by
    rw [show b + BitVec.ofNat 64 0 = b from BitVec.add_zero b]; exact fa)
  obtain sva : SavedW b s.gpr a.mem := fun rd hrd => by
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hrd
    rcases hrd with rfl | rfl | rfl | rfl | rfl | rfl <;> apply BitVec.eq_of_toNat_eq
    · exact wa 0 (by decide)
    · exact wa 1 (by decide)
    · exact wa 2 (by decide)
    · exact wa 3 (by decide)
    · exact wa 4 (by decide)
    · exact wa 5 (by decide)
  obtain ba : Spec.X25519.bytesAt a.mem (s.gpr .x1) 32 = Spec.X25519.bytesAt s.mem (s.gpr .x1) 32 :=
    bytesAt_out (outside_scR (by decide) oa) (fun r hr => by rw [List.mem_singleton.mp hr]; exact fun _ h => h) ssc
  rw [WP.block_append_iff]
  refine WP.mono (bits_ok (sc := s.gpr .x1) hsa (ka.gpr _ (by decide)) (fun i hi => ⟨⟨s.gpr .x1, 32⟩, by
      rw [ka.rd, hrd]; simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩)
    (fun i hi r hr hc => by
      rw [List.mem_singleton.mp hr] at hc
      exact ssc _ (Offset.contains_base (s.gpr .x1) (d := i) (n := 1) (by omega_using [hi]) (by omega_using [hi]))
        (Offset.sub_base b (show BITS + 256 ≤ 4096 by decide) _ hc))) fun c ⟨cb, fc, kc⟩ => ?_
  obtain hsc := hsa.of_kp kc (by decide)
  obtain oc : Outside b BITS 256 a.mem c.mem := outside_of_frame (by decide) fc
  rw [WP.block_append_iff]
  refine WP.mono (moves_ok hsc) fun d ⟨dm, d1, d0, dg, drd, dwr⟩ => ?_
  obtain od : Outside b BITS 256 c.mem d.mem := fun x hx => by
    rw [dm, write1_apply, ite_eq_right]
    rintro rfl
    rw [ofs_off' b (by decide)] at hx
    omega_using [hx]
  obtain rds : d.rd = s.rd := by rw [drd, kc.rd, ka.rd]
  obtain wrs : d.wr = s.wr := by rw [dwr, kc.wr, ka.wr]
  obtain gs : ∀ r, r ∉ [Reg.x0, .x1, .x17, .x19, .x20] → d.gpr r = s.gpr r := fun r hr => by
    rw [dg r fun h => hr ((by decide : ∀ q ∈ [Reg.x0, .x1, .x19], q ∈ [Reg.x0, .x1, .x17, .x19, .x20]) r h),
      kc.gpr r fun h => hr ((by decide : ∀ q ∈ [Reg.x17, .x19, .x20], q ∈ [Reg.x0, .x1, .x17, .x19, .x20]) r h),
      ka.gpr r List.not_mem_nil]
  obtain hd : Scr d b false := ⟨d0, by rw [wrs, hwr]; simp, hn⟩
  -- The bits.
  obtain kd : BitsAt d.mem b (bitOf (kOf s.mem (s.gpr .x1))) := fun t ht => by
    rw [dm, write1_apply]
    by_cases h255 : t = 255
    · subst h255
      rw [ite_eq_left rfl]; rfl
    · rw [ite_eq_right (Offset.add_ofNat_ne b (by omega_using [hB, ht]) (by omega_using [hB]) (by omega_using [h255])),
        bitOf, ite_eq_left (show t < 255 by omega_using [ht, h255])]
      rw [← clampB_eq (m := a.mem) (fun i hi => byte_out (outside_scR (by decide) oa) (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact fun _ h => h) ssc hi) (show t < 255 by omega_using [ht, h255])]
      exact cb t ht
  -- The saved registers.
  obtain svd : SavedW b s.gpr d.mem := savedW_outside od (by decide) (savedW_outside oc (by decide) sva)
  -- The point.
  obtain fd : Frame [scR b] s.mem d.mem := (outside_scR (by decide) oa).trans
    ((outside_scR (by decide) oc).trans (outside_scR (by decide) od))
  obtain pd : Spec.X25519.bytesAt d.mem (s.gpr .x2) 32 = Spec.X25519.bytesAt s.mem (s.gpr .x2) 32 :=
    bytesAt_out fd (fun r hr => by rw [List.mem_singleton.mp hr]; exact fun _ h => h) psc
  rw [WP.block_append_iff]
  refine WP.mono (loadY_ok d (s.gpr .x2) (gs _ (by decide)) fun i hi => ⟨⟨s.gpr .x2, 32⟩, by rw [rds, hrd]; simp,
    Offset.contains_base _ hi (by omega_using [hi])⟩) fun e ⟨ev, ke⟩ => ?_
  obtain he := hd.of_keeps ke (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (store4_ok he (slot_rangeWith (large := false) 0)) fun f hf => ?_
  obtain of : Outside b (offset 0) 32 d.mem f.mem := by
    subst hf
    rw [← ke.mem]
    exact st4_outside _ _ (by decide) _ _ _ _
  obtain ff : fe f.mem b (offset 0) = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt d.mem (s.gpr .x2) 32) % 2 ^ 255 := by
    subst hf
    rw [← ev]
    exact fe_st4 _ _ (by decide) _ _ _ _
  obtain gf : f.gpr = e.gpr := by subst hf; rfl
  obtain rf : f.rd = e.rd := by subst hf; rfl
  obtain wf : f.wr = e.wr := by subst hf; rfl
  obtain hsf : Scr f b false := ⟨by rw [gf]; exact he.x0, by rw [wf]; exact he.wr, hn⟩
  obtain f0 : fe f.mem b (offset 0) < 2 ^ 255 := by rw [ff]; exact Nat.mod_lt _ (by decide)
  obtain uv : env f.mem b 0 = uOf s.mem (s.gpr .x2) := by
    rw [env, F, ff, uOf, decodeUCoordinate_eq (length_bytesAt _ _ _), ← pd, VG.Proof.Ed25519.decodeLE_eq]
    rfl
  refine WP.mono (fieldCode_okS _ hsf (S := fun i => decide (i = 0)) (fun i hi => by
    rw [of_decide_eq_true hi]; omega_using [f0])) fun g ⟨kg, eg, sg⟩ => ?_
  obtain ot : Outside b 64 704 d.mem g.mem := (of.mono (by decide) (by decide)).trans kg.mem
  refine ⟨kg.scr hsf, bitsAt_outside ot (by decide) kd, ?_, ?_, savedW_outside ot (by decide) svd, ?_, fun r hr => ?_, ?_, ?_⟩
  · exact ⟨sg 1 (small0 1 (by decide)), sg 2 (small0 2 (by decide)), sg 3 (small0 3 (by decide)), sg 4 (small0 4 (by decide))⟩
  · rw [Holds, eg, ladderAfter_255]
    simp only [evalOps, evalOp, List.foldl_cons, List.foldl_nil, Fun.update_apply, Fin.reduceEq, ite_true, ite_false]
    exact ⟨uv, rfl, rfl, uv, rfl⟩
  · rw [kg.gpr _ (by decide), gf, ke.gpr _ (by decide), d1, kc.gpr _ (by decide), ka.gpr _ (by decide)]
  · simp only [List.mem_cons, not_or] at hr
    obtain ⟨r0, r1, r10, r19, rl⟩ := hr
    rw [kg.gpr r (fun h => by
        rcases (by decide : ∀ q ∈ clob, q = .x10 ∨ q ∈ lclob) r h with h | h
        · exact r10 h
        · exact rl h), gf, ke.gpr r (fun h => rl ((by decide : ∀ q ∈ [Reg.x4, .x5, .x6, .x7, .x8], q ∈ lclob) r h))]
    refine gs r fun h => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h
    · exact r0 h
    · exact r1 h
    · subst h; exact rl (by decide)
    · exact r19 h
    · subst h; exact rl (by decide)
  · rw [kg.rd, rf, ke.rd, rds]
  · rw [kg.wr, wf, ke.wr, wrs]

theorem setup_ok {s : State} (hp : LPre s) :
    WP isa (.block setup) s fun t =>
      Inv t (s.gpr .x3) (kOf s.mem (s.gpr .x1)) (uOf s.mem (s.gpr .x2)) 255 t ∧
      SavedW (s.gpr .x3) s.gpr t.mem ∧ SavedV (s.gpr .x3) s.v t.mem ∧ t.gpr .x1 = s.gpr .x0 ∧
      (∀ r, r ∉ .x0 :: .x1 :: .x10 :: .x19 :: lclob → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  rw [setup, WP.block_append_iff]
  refine WP.mono (WP.preservedV (setup0_ok hp) (by lit_decide))
    fun a ⟨⟨hsa, ab, as, ah, aw, a1, ag, ard, awr⟩, av⟩ => ?_
  generalize s.gpr .x3 = b at *
  rw [WP.block_append_iff]
  refine WP.mono (constants_ok hsa) fun c ⟨cc, co, cg, crd, cwr, cv⟩ => ?_
  have hsc : Scr c b false := scr_of hsa (cg _ (by decide)) cwr
  rw [WP.block_append_iff]
  refine WP.mono (vsave_ok hsc) fun d ⟨dv, dm, dg, drd, dwr⟩ => ?_
  have hsd : Scr d b false := scr_of hsc (by rw [dg]) dwr
  refine WP.mono (count_ok d) fun t ⟨t10, t19, kt⟩ => ?_
  obtain o : Outside b 1120 192 a.mem t.mem := by
    rw [kt.mem]
    exact (co.mono (by decide) (by decide)).trans (dm.mono (by decide) (by decide))
  have ef : ∀ i : Fin 14, fe t.mem b (offset (i.castLE (by decide))) = fe a.mem b (offset (i.castLE (by decide))) := fun i =>
    o.fe (Or.inl (by simp only [offset, Fin.val_castLE]; omega_arith)) (by simp only [offset, Fin.val_castLE]; omega_arith)
  refine ⟨⟨hsd.of_keeps kt (by decide), t10, t19, ?_, ?_, ?_, ?_, fun _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩,
    ?_, ?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · intro n hn
    have hB : BITS = 1984 := rfl
    rw [o _ (Or.inr (by rw [ofs_off' b (by omega_using [hB, hn])]; omega_using [hB])), ab n hn]
  · exact ⟨Nat.lt_of_le_of_lt (Nat.le_of_eq (ef 1)) as.1, Nat.lt_of_le_of_lt (Nat.le_of_eq (ef 2)) as.2.1, Nat.lt_of_le_of_lt (Nat.le_of_eq (ef 3)) as.2.2.1, Nat.lt_of_le_of_lt (Nat.le_of_eq (ef 4)) as.2.2.2⟩
  · rw [kt.mem]
    refine ⟨fun e he => ?_, fun e he => ?_, fun e he => ?_, fun k hk => ?_⟩
    · rw [read16_outside dm (by decide) (by decide)]; exact cc.k51 e he
    · rw [read16_outside dm (by decide) (by decide)]; exact cc.k26 e he
    · rw [read16_outside dm (by decide) (by decide)]; exact cc.k25 e he
    · rw [read16_outside dm (by decide) (by decide)]; exact cc.k19 k hk
  · exact ⟨(congrArg toFe (ef 0)).trans ah.1, (congrArg toFe (ef 1)).trans ah.2.1, (congrArg toFe (ef 2)).trans ah.2.2.1,
      (congrArg toFe (ef 3)).trans ah.2.2.2.1, (congrArg toFe (ef 4)).trans ah.2.2.2.2⟩
  · exact savedW_outside o (by decide) aw
  · rw [kt.mem]
    intro k hk
    have hm : ∀ k < 8, vsaved k ∈ preservedV ∧ vsaved k ≠ .v0 := by decide
    rw [dv k hk, cv _ (hm k hk).2, av _ (hm k hk).1]
  · rw [kt.gpr _ (by decide), dg, cg _ (by decide), a1]
  · simp only [List.mem_cons, not_or] at hr
    rw [kt.gpr r (by simp [hr.2.2.1, hr.2.2.2.1]), dg, cg r fun h => hr.2.2.2.2 (h ▸ by decide),
      ag r (by simp only [List.mem_cons, not_or]; exact hr)]
  · rw [kt.rd, drd, crd, ard]
  · rw [kt.wr, dwr, cwr, awr]

/-! ## The finish -/

theorem out_ok {s : State} {q : Addr} (hq : s.gpr .x1 = q) (hw : (⟨q, 32⟩ : Region) ∈ s.wr) :
    WP isa (.block [.str .x .x4 .x1 0, .str .x .x5 .x1 8, .str .x .x6 .x1 16, .str .x .x7 .x1 24]) s
      fun t => t = { s with mem := st4 s.mem q 0 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) } := by
  have w : ∀ d, d + 8 ≤ 32 → InRegions s.wr (off q d) 8 :=
    fun d hd => ⟨_, hw, Offset.contains_base q hd (by omega_using [hd])⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, State.store, read_x,
    hq, BitVec.setWidth_eq, Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self, ite_true,
    w 0 (by omega_using []), w 8 (by omega_using []), w 16 (by omega_using []), w 24 (by omega_using []),
    Option.bind_some, Option.some.injEq, exists_eq_left']
  simp only [st4, Mem.writeW, BitVec.setWidth_eq, Nat.zero_add]

theorem restore_ok {s : State} {b : Addr} (hs : Scr s b false) {g : Reg → BitVec 64} (hsv : SavedW b g s.mem) :
    WP isa (.block (saved.map fun (r, o) => ld r o)) s fun t =>
      (∀ rd ∈ saved, t.gpr rd.1 = g rd.1) ∧ Keeps [.x19, .x20, .x21, .x22, .x23, .x24] s t := by
  apply WP.of_runBlock
  have h0 := hs
  have h1 := h0.write (r := .x19) (by decide) (word s.mem b 0)
  have h2 := h1.write (r := .x20) (by decide) (word s.mem b 8)
  have h3 := h2.write (r := .x21) (by decide) (word s.mem b 16)
  have h4 := h3.write (r := .x22) (by decide) (word s.mem b 24)
  have h5 := h4.write (r := .x23) (by decide) (word s.mem b 32)
  simp only [saved, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil,
    load_sc h0 (show 0 % 8 = 0 from rfl) (by decide), load_sc h1 (show 8 % 8 = 0 from rfl) (by decide),
    load_sc h2 (show 16 % 8 = 0 from rfl) (by decide), load_sc h3 (show 24 % 8 = 0 from rfl) (by decide),
    load_sc h4 (show 32 % 8 = 0 from rfl) (by decide), load_sc h5 (show 40 % 8 = 0 from rfl) (by decide),
    RegUpd.mem_write, Option.some.injEq, exists_eq_left']
  refine ⟨fun rd hrd => ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [← hsv rd hrd]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrd
    rcases hrd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]

/-! ## The whole function -/

theorem x25519_wp [VG.Proof.Ed25519.AArch64.Divstep.Sound] {s : State} (hp : LPre s) :
    WP isa x25519 s fun t => ((∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
      ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) ∧
      Spec.X25519.bytesAt t.mem (s.gpr .x0) 32 =
        Spec.X25519.x25519 (Spec.X25519.bytesAt s.mem (s.gpr .x1) 32) (Spec.X25519.bytesAt s.mem (s.gpr .x2) 32) := by
  obtain ⟨b, hb⟩ : ∃ b, s.gpr .x3 = b := ⟨_, rfl⟩
  obtain osc := hp.pre.out_sc
  obtain hwr := hp.pre.wr
  rw [x25519]
  refine WP.seq (WP.mono (setup_ok hp) fun a ⟨ia, sva, svv, a1, ag, _, awr⟩ => ?_)
  rw [hb] at ia sva svv osc hwr
  refine WP.seq (WP.mono (ladder_ok ia) fun c ic => ?_)
  refine WP.seq (WP.mono (vrestore_ok ic.scr (svv.outside ic.mem (by decide))) fun r ⟨rv, rm, rg, _, rwr⟩ => ?_)
  obtain hr : Scr r b false := scr_of ic.scr (by rw [rg]) rwr
  obtain svc : SavedW b s.gpr r.mem := by rw [rm]; exact savedW_outside ic.mem (by decide) sva
  suffices h : WP isa (.seq Divstep.invert (.block VG.Impl.X25519.AArch64.Word.finish)) r fun t =>
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ Spec.X25519.bytesAt t.mem (s.gpr .x0) 32 =
        Spec.X25519.x25519 (Spec.X25519.bytesAt s.mem (s.gpr .x1) 32) (Spec.X25519.bytesAt s.mem (s.gpr .x2) 32) by
    refine WP.mono (WP.preservedV h (by lit_decide)) fun t ⟨⟨tg, tb⟩, tv⟩ => ⟨⟨tg, fun q hq => ?_⟩, tb⟩
    obtain ⟨k, hk, rfl⟩ : ∃ k, k < 8 ∧ q = vsaved k := by
      simp only [preservedV, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩,
        ⟨7, by decide⟩]
    rw [tv _ hq, rv k hk]
  refine WP.seq (WP.mono (Divstep.invert_ok hr) fun d ⟨dv, kd, d1, od⟩ => ?_)
  obtain svd := savedW_outside od (by decide) svc
  obtain hd : Scr d b false := ⟨(kd.gpr _ (by decide)).trans hr.x0, kd.wr ▸ hr.wr, hr.nowrap⟩
  simp only [VG.Impl.X25519.AArch64.Word.finish, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (mul_ok hd (slot_rangeWith (large := false) 1) (slot_rangeWith (large := false) 1)
    (slot_rangeWith (large := false) 15)) fun e ⟨oe, ev⟩ => ?_
  obtain he : Scr e b false := ⟨(oe.gpr _ (by decide)).trans hd.x0, oe.wr ▸ hd.wr, hd.nowrap⟩
  obtain sve := savedW_outside oe.mem (by decide) svd
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok he (slot_rangeWith (large := false) 1)) fun f ⟨fv, kf⟩ => ?_
  obtain wrf : f.wr = s.wr := by rw [kf.wr, oe.wr, kd.wr, rwr, ic.wr, awr]
  obtain f1 : f.gpr .x1 = s.gpr .x0 := by
    rw [kf.gpr _ (by decide), oe.gpr _ (by decide), d1, rg, ic.gpr _ (by decide), a1]
  rw [WP.block_append_iff]
  refine WP.mono (out_ok f1 (by rw [wrf, hwr]; simp)) fun g hg => ?_
  obtain og : Outside (s.gpr .x0) 0 32 f.mem g.mem := by subst hg; exact st4_outside _ _ (by decide) _ _ _ _
  obtain svg : SavedW b s.gpr g.mem := fun rd hrd => by
    obtain hlt : rd.2 ≤ 40 := (by decide : ∀ rd ∈ saved, rd.2 ≤ 40) rd hrd
    rw [← sve rd hrd, ← kf.mem]
    refine (Mem.readW_congr fun i hi => (og _ ?_).symm).symm
    refine Decidable.byContradiction fun hn => ?_
    refine osc (off b rd.2 + BitVec.ofNat 64 i) ?_ ?_
    · simp only [Region.Contains]; simp only [ofs] at hn; omega_using [hn]
    · rw [off, Offset.add_add]
      exact Offset.contains_base b (by omega_using [hlt, hi]) (by omega_using [hlt, hi])
  obtain hsg : Scr g b false := by
    subst hg
    exact ⟨(kf.gpr _ (by decide)).trans he.x0, by rw [show (State.wr _) = f.wr from rfl, kf.wr]; exact he.wr, he.nowrap⟩
  refine WP.mono (restore_ok hsg svg) fun t ⟨tr, kt⟩ => ⟨fun r hr => ?_, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tr (.x19, 0) (by decide)
    · exact tr (.x20, 8) (by decide)
    · exact tr (.x21, 16) (by decide)
    · exact tr (.x22, 24) (by decide)
    · exact tr (.x23, 32) (by decide)
    · exact tr (.x24, 40) (by decide)
    all_goals
      rw [kt.gpr _ (by decide), show g.gpr = f.gpr by subst hg; rfl, kf.gpr _ (by decide), oe.gpr _ (by decide),
        kd.gpr _ (by decide), rg, ic.gpr _ (by decide), ag _ (by decide)]
  · rw [kt.mem]
    subst hg
    show Spec.X25519.bytesAt (st4 _ _ _ _ _ _ _) _ 32 = _
    obtain ⟨-, h2, h3, -, -⟩ := ic.holds
    obtain z : (ladderAfter (kOf s.mem (s.gpr .x1)) (uOf s.mem (s.gpr .x2)) 0).swap = 0 := by
      rw [ladderAfter_step _ _ (by decide : 0 < 255)]
      show bit _ 0 = 0
      rw [scalar_bit (length_bytesAt _ _ _) (by decide)]
      rfl
    obtain e1 : F d.mem b (offset 1) = env r.mem b 1 := congrArg toFe (od.fe (by decide) (by decide))
    rw [bytesAt_st4, fv, x25519_eq]
    simp only [z, Spec.X25519.cswap, show (0 : Nat) ≠ 1 from by decide, ite_false]
    rw [encodeUCoordinate_eq, ← h2, ← h3, ← rm, ← e1, ← dv, show env d.mem b 15 = F d.mem b (offset 15) from rfl, ← ev,
      F, toFe_val]

/-- `vg_x25519`'s contract by register, an internal function's. -/
def local25519 : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .x1, 32⟩, ⟨s.gpr .x2, 32⟩] ∧ s.wr = [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x3, 4096⟩] ∧
    (⟨s.gpr .x0, 32⟩ : Region).Disjoint ⟨s.gpr .x3, 4096⟩ ∧ (⟨s.gpr .x1, 32⟩ : Region).Disjoint ⟨s.gpr .x3, 4096⟩ ∧
    (⟨s.gpr .x2, 32⟩ : Region).Disjoint ⟨s.gpr .x3, 4096⟩ ∧ (s.gpr .x3).toNat + 4096 ≤ 2 ^ 64
  post s s' := Spec.X25519.bytesAt s'.mem (s.gpr .x0) 32 =
    Spec.X25519.x25519 (Spec.X25519.bytesAt s.mem (s.gpr .x1) 32) (Spec.X25519.bytesAt s.mem (s.gpr .x2) 32)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

theorem x25519_ok [VG.Proof.Ed25519.AArch64.Divstep.Sound] (s : State) (hs : local25519.pre s) :
    ∃ t s', Exec isa x25519 s t s' ∧ abiPreserved s s' ∧ local25519.post s s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs
  obtain ⟨t, s', he, ⟨hg, hv⟩, hp⟩ := x25519_wp ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hv⟩, hp⟩

theorem x25519_ct : ConstantTime isa local25519.pre local25519.pub x25519 := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, h2, h3, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

end VG.Proof.X25519.AArch64.Ladder

namespace VG.Proof.X25519.AArch64

/-- A state satisfying the precondition of `vg_x25519` and of its exchange. -/
def sat : AArch64.State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 4096⟩]

end VG.Proof.X25519.AArch64

namespace VG.Proof.X25519.AArch64.Ladder

open VG VG.AArch64 VG.Impl.X25519.AArch64.Ladder

theorem x25519_verified [VG.Proof.Ed25519.AArch64.Divstep.Sound] :
    Verified AArch64.target x25519 (Proof.X25519.x25519Contract AArch64.abi) :=
  Verified.of_correct x25519_ok x25519_ct (by
    contract_implies [Proof.X25519.x25519Contract, Proof.X25519.x25519Sig, local25519, AArch64.abi, AArch64.argRegs]
      [VG.Proof.X25519.AArch64.sat] using VG.Proof.X25519.AArch64.sat)

end VG.Proof.X25519.AArch64.Ladder
