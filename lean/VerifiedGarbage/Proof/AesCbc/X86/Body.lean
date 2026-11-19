module

public import VerifiedGarbage.Proof.AesCbc.Mem32
import VerifiedGarbage.Proof.CmacAes.X86.UpdateLoop
import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Aes.X86.BlocksVariant
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.AesCbc.X86.Call
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.X86.Spill

/-! ### `AesCbc.X86.Loop`, which this module and modules that import it used -/

section

/-!
# AES-CBC on x86: the loop, for any mode on whole blocks

The invariant after `k` blocks (`LInv`): `esi` points at the next block,
`esp` is unchanged, only the chaining value, the data, the first 2064 bytes
of the scratch buffer and the 24 bytes below `esp` have changed since the
registers were saved, the first `k` blocks are the mode's (`Mode.out`) of
the first `k` blocks on entry and the rest are unchanged, and the chaining
value is the mode's after them (`Mode.chain`). CBC is `cbcMode`; other
modes' functions with the same arguments reuse the loop. Everything else is
reloaded from the stack arguments, which nothing writes.

`whole_wp`: if one run of `body` takes the invariant from `k` to `k + 1`
blocks and sets ZF when none are left (`BodyOk`), `whole body` meets the
contract.
-/

@[expose] public section

namespace VG.Proof.AesCbc.X86

open VG VG.X86 VG.Impl.AesCbc.X86
open VG.Impl.CmacAes.X86 (argOp setup advance restore saved)
open VG.Proof.CmacAes.X86 (wp_arg wp_addArg saved_fits saved_bound saved_ne_eax saveMem_slot restore_eq
  setup_eq ofNat_and_self_beq arg_ofNat advance_eq adv_zf add0 add0')
open VG.Proof.MdStream.X86 (Upd wp_addi wp_add wp_cmp wp_test eval_e eval_ne)
open VG.Spec.Aes (bytesAt)

section
variable (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev W : BitVec 32 := arg s₀ 0
abbrev R : Nat := (arg s₀ 1).toNat
abbrev Iv : BitVec 32 := arg s₀ 2
abbrev Dp : BitVec 32 := arg s₀ 3
abbrev N : Nat := (arg s₀ 4).toNat
abbrev S : BitVec 32 := arg s₀ 5

abbrev schR : Region := ⟨(W s₀).setWidth 64, 240⟩
abbrev ivR : Region := ⟨(Iv s₀).setWidth 64, 16⟩
abbrev dataR : Region := ⟨(Dp s₀).setWidth 64, 16 * N s₀⟩
abbrev scrR : Region := ⟨(S s₀).setWidth 64, 2176⟩
abbrev argsR : Region := ⟨argAddr s₀ 0, 24⟩
abbrev retR : Region := ⟨(E s₀).setWidth 64, 4⟩
abbrev stkR : Region := ⟨(E s₀).setWidth 64 - BitVec.ofNat 64 24, 24⟩

/-- The blocks on entry. -/
abbrev blks : List (List Byte) := Spec.Cbc.blocksAt s₀.mem ((Dp s₀).setWidth 64) (N s₀)

/-- The chaining value on entry. -/
abbrev iv0 : List Byte := bytesAt s₀.mem ((Iv s₀).setWidth 64) 16

/-- The address of block `k`. -/
abbrev blk (k : Nat) : Addr := (Dp s₀).setWidth 64 + BitVec.ofNat 64 (16 * k)

/-- The memory after saving the registers in the scratch buffer. -/
def savedMem : Mem := Spill.saveMem s₀.mem ((S s₀).setWidth 64 + BitVec.ofNat 64 ·) s₀.gpr saved

end

/-- The precondition, by name. -/
structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [schR s₀, argsR s₀]
  wr : s₀.wr = [ivR s₀, dataR s₀, scrR s₀]
  sch_iv : (schR s₀).Disjoint (ivR s₀)
  sch_data : (schR s₀).Disjoint (dataR s₀)
  sch_scr : (schR s₀).Disjoint (scrR s₀)
  iv_data : (ivR s₀).Disjoint (dataR s₀)
  iv_scr : (ivR s₀).Disjoint (scrR s₀)
  data_scr : (dataR s₀).Disjoint (scrR s₀)
  args_iv : (argsR s₀).Disjoint (ivR s₀)
  args_data : (argsR s₀).Disjoint (dataR s₀)
  args_scr : (argsR s₀).Disjoint (scrR s₀)
  ret_iv : (retR s₀).Disjoint (ivR s₀)
  ret_data : (retR s₀).Disjoint (dataR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)
  b_sch : (stkR s₀).Disjoint (schR s₀)
  b_iv : (stkR s₀).Disjoint (ivR s₀)
  b_data : (stkR s₀).Disjoint (dataR s₀)
  b_scr : (stkR s₀).Disjoint (scrR s₀)
  sch_fit : (W s₀).toNat + 240 ≤ 2 ^ 32
  iv_fit : (Iv s₀).toNat + 16 ≤ 2 ^ 32
  data_fit : (Dp s₀).toNat + 16 * N s₀ ≤ 2 ^ 32
  scr_fit : (S s₀).toNat + 2176 ≤ 2 ^ 32
  esp24 : 24 ≤ (E s₀).toNat
  esp_fit : (E s₀).toNat + 28 ≤ 2 ^ 32
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14

theorem UPre.of {M : Mode} {s₀ : State} (h : (modeX86 M).pre s₀) : UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w, x, y, z⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w, x, y, z⟩

/-- The key schedule as the mode uses it. -/
abbrev wK (s₀ : State) : List Byte := bytesAt s₀.mem ((W s₀).setWidth 64) (16 * (R s₀ + 1))

/-- The first `k` blocks after the mode. -/
abbrev outK (M : Mode) (s₀ : State) (k : Nat) : List (List Byte) :=
  M.out (R s₀) (wK s₀) (iv0 s₀) ((blks s₀).take k)

/-- The chaining value after the first `k` blocks. -/
abbrev chainK (M : Mode) (s₀ : State) (k : Nat) : List Byte :=
  M.chain (R s₀) (wK s₀) (iv0 s₀) ((blks s₀).take k)

/-- The loop invariant, after `k` blocks. -/
structure LInv (M : Mode) (s₀ : State) (k : Nat) (s : State) : Prop where
  esi : s.gpr .esi = Dp s₀ + BitVec.ofNat 32 (16 * k)
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) s.mem
  data : Spec.Cbc.blocksAt s.mem ((Dp s₀).setWidth 64) (N s₀) = outK M s₀ k ++ (blks s₀).drop k
  iv : bytesAt s.mem ((Iv s₀).setWidth 64) 16 = chainK M s₀ k

/-! ## Addresses and regions -/

/-- The regions the function writes, with the stack below it. -/
abbrev Big (s₀ : State) : List Region := [ivR s₀, dataR s₀, scrR s₀, stkR s₀]

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.below_eq : below (E s₀) 24 = stkR s₀ := by
  simp only [below]; rw [Taint.sub_setWidth hp.esp24]

theorem UPre.argA {i : Nat} (hi : i < 6) : argAddr s₀ i = argAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
  have : (s₀.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.esp_fit
  simp only [argAddr]
  rw [show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * i) from rfl,
    show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * 0) from rfl,
    addr_eq (by omega_using [hi, this]), addr_eq (by omega_using [this]), Offset.add_add]

theorem UPre.arg_sub {i : Nat} (hi : i < 6) : Region.Sub ⟨argAddr s₀ i, 4⟩ (argsR s₀) := by
  rw [hp.argA hi]; exact Offset.sub_base _ (by omega_using [hi])

theorem UPre.arg_in {i : Nat} (hi : i < 6) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 := by
  refine ⟨argsR s₀, by simp [hp.rd], ?_⟩
  rw [hp.argA hi]; exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])

theorem UPre.args_stk : (argsR s₀).Disjoint (stkR s₀) := by
  have : (s₀.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.esp_fit
  have e : argAddr s₀ 0 = (E s₀).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega_using [this])
  show Region.Disjoint ⟨argAddr s₀ 0, 24⟩ _
  rw [e]; exact (Offset.disjoint_below_above _ (by decide)).symm

/-- The stack arguments are unchanged where only `Big` changes. -/
theorem UPre.arg_keep {m : Mem} (hf : Frame (Big s₀) s₀.mem m) {i : Nat} (hi : i < 6) :
    m.readW (argAddr s₀ i) 32 = arg s₀ i :=
  hf.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.args_iv.sub_left (hp.arg_sub hi)
    · exact hp.args_data.sub_left (hp.arg_sub hi)
    · exact hp.args_scr.sub_left (hp.arg_sub hi)
    · exact hp.args_stk.sub_left (hp.arg_sub hi)) (by decide)

theorem UPre.dataA {k : Nat} (hk : k < N s₀) : addr (Dp s₀) (16 * k) = blk s₀ k :=
  addr_eq (by have := hp.data_fit; omega_using [hk, this])

theorem UPre.dataN {k : Nat} (hk : k < N s₀) :
    (Dp s₀ + BitVec.ofNat 32 (16 * k)).toNat = (Dp s₀).toNat + 16 * k := by
  have := hp.data_fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * k) (by omega_using [hk, this]),
    Nat.mod_eq_of_lt (by omega_using [hk, this])]

theorem UPre.blk_disjoint {j k : Nat} (hj : j < N s₀) (hk : k < N s₀) (hjk : j ≠ k) :
    (⟨blk s₀ j, 16⟩ : Region).Disjoint ⟨blk s₀ k, 16⟩ := by
  have := hp.data_fit
  exact Offset.disjoint _ (by omega_using [hjk]) (by omega_using [hj, this]) (by omega_using [hk, this])

end

theorem UPre.scr_sub {s₀ : State} {d n : Nat} (h : d + n ≤ 2176) :
    Region.Sub ⟨(S s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩ (scrR s₀) :=
  Offset.sub_base _ h

theorem UPre.data_sub {s₀ : State} {k : Nat} (hk : k < N s₀) : Region.Sub ⟨blk s₀ k, 16⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega_using [hk])

theorem savedMem_frame (s₀ : State) : Frame [scrR s₀] s₀.mem (savedMem s₀) :=
  Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p hp =>
    have := saved_bound p hp; Offset.contains_base _ (by omega_using [this]) (by omega_using [this])

theorem savedMem_slot (s₀ : State) {r : Reg} {d : Nat} (h : (r, d) ∈ saved) :
    (savedMem s₀).readW ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r :=
  saveMem_slot _ _ _ h

/-- `savedMem` changes only `Big`. -/
theorem savedMem_big (s₀ : State) : Frame (Big s₀) s₀.mem (savedMem s₀) :=
  (savedMem_frame s₀).mono (by simp)

theorem UPre.big_of {s₀ : State} {m : Mem}
    (hf : Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) m) :
    Frame (Big s₀) s₀.mem m :=
  (savedMem_big s₀).trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.sched_bytes {m : Mem} (hf : Frame (Big s₀) s₀.mem m) :
    bytesAt m ((W s₀).setWidth 64) (16 * (R s₀ + 1)) = bytesAt s₀.mem ((W s₀).setWidth 64) (16 * (R s₀ + 1)) := by
  have hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega_using [hR])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.sch_iv.sub_left (Region.sub_prefix hR)
  · exact hp.sch_data.sub_left (Region.sub_prefix hR)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hR)
  · exact hp.b_sch.symm.sub_left (Region.sub_prefix hR)

/-- The blocks after a step that changed only block `k`, the chaining
value, the first 2064 bytes of the scratch buffer and the stack. -/
theorem UPre.blocksAt_step {m m' : Mem} {k : Nat} (hk : k < N s₀)
    (hf : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] m m') :
    Spec.Cbc.blocksAt m' ((Dp s₀).setWidth 64) (N s₀) =
      (Spec.Cbc.blocksAt m ((Dp s₀).setWidth 64) (N s₀)).set k (bytesAt m' (blk s₀ k) 16) := by
  refine blocksAt_set fun j hj hjk => Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.blk_disjoint hj hk hjk
  · exact hp.iv_data.symm.sub_left (UPre.data_sub hj)
  · exact (hp.data_scr.sub_left (UPre.data_sub hj)).sub_right (Region.sub_prefix (by decide))
  · exact hp.b_data.symm.sub_left (UPre.data_sub hj)

omit hp in
/-- Block `k` of a memory whose first `k` blocks are the mode's and whose
others are still the original ones. -/
theorem block_of_data {M : Mode} {k : Nat} {m : Mem}
    (hd : Spec.Cbc.blocksAt m ((Dp s₀).setWidth 64) (N s₀) = outK M s₀ k ++ (blks s₀).drop k) (hk : k < N s₀) :
    bytesAt m (blk s₀ k) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
  have hl : (outK M s₀ k).length = k := by
    rw [outK, M.length_out]; simp [Spec.Cbc.blocksAt]; omega_using [hk]
  have := congrArg (·[k]?) hd
  simp only [List.getElem?_eq_getElem (show k < (Spec.Cbc.blocksAt m ((Dp s₀).setWidth 64) (N s₀)).length by
      rw [length_blocksAt]; exact hk),
    List.getElem?_append_right (show (outK M s₀ k).length ≤ k by omega_using [hl]), hl, Nat.sub_self,
    List.getElem?_drop, Nat.add_zero,
    List.getElem?_eq_getElem (show k < (blks s₀).length by simp [Spec.Cbc.blocksAt]; exact hk)] at this
  show bytesAt m ((Dp s₀).setWidth 64 + BitVec.ofNat 64 (16 * k)) 16 = _
  rw [← getElem_blocksAt _ _ hk]
  exact Option.some.inj this

omit hp in
/-- Block `k` before the step, from the invariant. -/
theorem LInv.block {M : Mode} {k : Nat} {s : State} (h : LInv M s₀ k s) (hk : k < N s₀) :
    bytesAt s.mem (blk s₀ k) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) :=
  block_of_data h.data hk

end

theorem take_succ_blks (s₀ : State) {k : Nat} (hk : k < N s₀) :
    (blks s₀).take (k + 1) = (blks s₀).take k ++ [(blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk)] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cbc.blocksAt]; exact hk)]
  rfl

/-! ## The prologue -/

theorem prologue_wp {M : Mode} {s₀ : State} (hp : UPre s₀) :
    WP isa (.block setup) s₀ fun s => (LInv M s₀ 0 s ∧ s.zf = some (decide (N s₀ = 0))) ∧ s.mem = savedMem s₀ := by
  have hsc := hp.scr_fit
  rw [setup_eq]
  refine wp_arg (s₀ := s₀) rfl (hp.arg_in (by decide)) rfl fun s₁ u₁ => ?_
  have h₁ : s₁.gpr .eax = S s₀ := u₁.gpr
  refine Spill.save_ofNat_ok saved saved_fits (by rw [h₁]; omega_using [hsc]) (fun p hp' => ?_) fun s₂ u₂ => ?_
  · have hb := saved_bound p hp'
    rw [h₁, u₁.wr, hp.wr]
    exact ⟨scrR s₀, by simp, Offset.contains_base _ (by omega_using [hb]) (by omega_using [hb])⟩
  have hm₂ : s₂.mem = savedMem s₀ := by
    rw [u₂.mem, u₁.mem, h₁, savedMem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (saved_ne_eax p hp')
  have esp₂ : s₂.gpr .esp = s₀.gpr .esp := by rw [u₂.gpr, u₁.other _ (by decide)]
  have rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]
  refine wp_arg (s₀ := s₀) esp₂ (by rw [rw₂]; exact hp.arg_in (by decide))
    (by rw [hm₂]; exact hp.arg_keep (savedMem_big s₀) (by decide)) fun s₃ u₃ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₃.other _ (by decide), esp₂])
    (by rw [u₃.rd, u₃.wr, rw₂]; exact hp.arg_in (by decide))
    (by rw [u₃.mem, hm₂]; exact hp.arg_keep (savedMem_big s₀) (by decide)) fun s₄ u₄ => ?_
  have f₀ := savedMem_frame s₀
  have ivS : bytesAt (savedMem s₀) ((Iv s₀).setWidth 64) 16 = iv0 s₀ :=
    Proof.Cmac.bytesAt_frame f₀ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_scr) (by decide)
  have dataS : Spec.Cbc.blocksAt (savedMem s₀) ((Dp s₀).setWidth 64) (N s₀) = blks s₀ := by
    simp only [Spec.Cbc.blocksAt]
    refine List.map_congr_left fun j hj => Proof.Cmac.bytesAt_frame f₀ (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.data_scr.sub_left (UPre.data_sub (List.mem_range.mp hj))
  refine wp_test fun s₅ f₅ z₅ => WP.block_nil ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, by rw [f₅.mem, u₄.mem, u₃.mem, hm₂]⟩
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.gpr, Nat.mul_zero, add0']
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), esp₂]
  · rw [f₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [f₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [f₅.mem, u₄.mem, u₃.mem, hm₂]; exact Frame.refl _ _
  · rw [f₅.mem, u₄.mem, u₃.mem, hm₂, dataS]
    rw [outK, List.take_zero, M.out_nil, List.drop_zero, List.nil_append]
  · rw [f₅.mem, u₄.mem, u₃.mem, hm₂, ivS]
    rw [chainK, List.take_zero, M.chain_nil]
  · rw [z₅, u₄.gpr, arg_ofNat s₀ 4, ofNat_and_self_beq (arg s₀ 4).isLt]

/-! ## The end of a block -/

theorem advance_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (hesi : s.gpr .esi = Dp s₀ + BitVec.ofNat 32 (16 * k)) (hesp : s.gpr .esp = E s₀)
    (hargs : ∀ i < 6, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i) (hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr) :
    WP isa (.block advance) s fun s' => s'.gpr .esi = Dp s₀ + BitVec.ofNat 32 (16 * (k + 1)) ∧
      s'.gpr .esp = E s₀ ∧ (∀ r, r ≠ .eax → r ≠ .esi → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = some (decide (k + 1 = N s₀)) := by
  rw [advance_eq]
  refine wp_addi fun s₁ u₁ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₁.other _ (by decide), hesp]) (by rw [u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₁.mem]; exact hargs 4 (by decide)) fun s₂ u₂ => ?_
  refine wp_add fun s₃ u₃ => wp_add fun s₄ u₄ => wp_add fun s₅ u₅ => wp_add fun s₆ u₆ => ?_
  refine wp_addArg (s₀ := s₀)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hesp])
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]
        exact hp.arg_in (by decide))
    (by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact hargs 3 (by decide)) fun s₇ u₇ => ?_
  refine wp_cmp fun s₈ f₈ _ z₈ => WP.block_nil ⟨?_, ?_, fun r h₁ h₂ => ?_, ?_, ?_, ?_, ?_⟩
  · rw [f₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hesi, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl,
      Offset.add_add_eq _ (c := 16 * (k + 1)) (by omega_using [])]
  · rw [f₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hesp]
  · rw [f₈.gpr, u₇.other _ h₁, u₆.other _ h₁, u₅.other _ h₁, u₄.other _ h₁, u₃.other _ h₁, u₂.other _ h₁,
      u₁.other _ h₂]
  · rw [f₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [f₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [f₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [z₈, u₇.gpr, u₇.other _ (by decide), u₆.gpr, u₆.other _ (by decide), u₅.gpr, u₅.other _ (by decide),
      u₄.gpr, u₄.other _ (by decide), u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₂.other _ (by decide), u₁.gpr, hesi]
    exact congrArg some (adv_zf hk hp.data_fit)

/-! ## The loop -/

/-- One run of `body` takes the invariant from `k` blocks to `k + 1`, and sets
ZF if no blocks are left. -/
def BodyOk (M : Mode) (body : Prog isa) : Prop :=
  ∀ {s₀ : State}, UPre s₀ → ∀ {k : Nat}, k < N s₀ → ∀ {s : State}, LInv M s₀ k s →
    WP isa body s fun s' => LInv M s₀ (k + 1) s' ∧ s'.zf = some (decide (k + 1 = N s₀))

theorem loop_ok {M : Mode} {body : Prog isa} (hb : BodyOk M body) {s₀ : State} (hp : UPre s₀) {k : Nat}
    (hk : k < N s₀) {s : State} (h : LInv M s₀ k s) : WP isa (.loop body .ne) s (LInv M s₀ (N s₀)) := by
  refine WP.loop (M := isa) (body := body) (c := .ne) (Q := LInv M s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv M s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (hb hp hk h) fun s' ⟨h', hz⟩ => ?_
  have ev : isa.eval .ne s' = some !decide (k + 1 = N s₀) := by
    show VG.X86.eval .ne s' = _; rw [eval_ne, hz]; rfl
  by_cases hz' : k + 1 = N s₀
  · left
    refine ⟨by rw [ev]; simp [hz'], ?_⟩
    rwa [← hz']
  · right
    refine ⟨by rw [ev]; simp [hz'], N s₀ - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hk, hz'], h'⟩

/-- What a step may change for a block function that writes only the first
`b` bytes of the working space: the chaining value, the data, those bytes,
the saved ciphertext block and the stack below `esp`. -/
abbrev FB (s₀ : State) (b : Nat) : List Region :=
  [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, b⟩, ⟨(S s₀).setWidth 64 + BitVec.ofNat 64 2048, 16⟩, stkR s₀]

/-- `BodyOk`, changing memory only within `FB s₀ b`. -/
def BodyOkB (M : Mode) (body : Prog isa) (b : Nat) : Prop :=
  ∀ {s₀ : State}, UPre s₀ → ∀ {k : Nat}, k < N s₀ → ∀ {s : State}, LInv M s₀ k s →
    WP isa body s fun s' => (LInv M s₀ (k + 1) s' ∧ s'.zf = some (decide (k + 1 = N s₀))) ∧
      Frame (FB s₀ b) s.mem s'.mem

theorem BodyOkB.ok {M : Mode} {body : Prog isa} {b : Nat} (h : BodyOkB M body b) : BodyOk M body := by
  intro s₀ hp k hk s hs
  exact (h hp hk hs).mono fun _ h => h.1

theorem loop_okB {M : Mode} {body : Prog isa} {b : Nat} (hb : BodyOkB M body b) {s₀ : State} (hp : UPre s₀)
    {k : Nat} (hk : k < N s₀) {s : State} (h : LInv M s₀ k s) :
    WP isa (.loop body .ne) s fun t => LInv M s₀ (N s₀) t ∧ Frame (FB s₀ b) s.mem t.mem := by
  refine WP.loop (M := isa) (body := body) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv M s₀ j t ∧ Frame (FB s₀ b) s.mem t.mem)
    ?_ (N s₀ - k) s ⟨k, rfl, hk, h, Frame.refl _ _⟩
  rintro n t ⟨k, rfl, hk, h, hf⟩
  refine WP.mono (hb hp hk h) fun s' ⟨⟨h', hz⟩, hf'⟩ => ?_
  have ev : isa.eval .ne s' = some !decide (k + 1 = N s₀) := by
    show VG.X86.eval .ne s' = _; rw [eval_ne, hz]; rfl
  by_cases hz' : k + 1 = N s₀
  · left
    refine ⟨by rw [ev]; simp [hz'], ?_, hf.trans hf'⟩
    rwa [← hz']
  · right
    refine ⟨by rw [ev]; simp [hz'], N s₀ - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hk, hz'], h', hf.trans hf'⟩

/-- No blocks, or `mid` on all of them. -/
theorem ends_mid_wp {M : Mode} {mid : Prog isa} {s₀ : State} {s₁ : State}
    (hm : 0 < N s₀ → WP isa mid s₁ (LInv M s₀ (N s₀)))
    (h : LInv M s₀ 0 s₁) (hz : s₁.zf = some (decide (N s₀ = 0))) :
    WP isa (.ite .e (.block []) mid) s₁ (LInv M s₀ (N s₀)) := by
  have ev : isa.eval .e s₁ = some (decide (N s₀ = 0)) := by
    show VG.X86.eval .e s₁ = _; rw [eval_e, hz]
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev]; simp [hn]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact hm (by omega_using [hn])

/-! ## The epilogue -/

theorem slot_read {s₀ : State} (hp : UPre s₀) {m : Mem}
    (hf : Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) m) {d : Nat}
    (h₁ : 2064 ≤ d) (h₂ : d + 4 ≤ 2080) :
    m.readW ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 =
      (savedMem s₀).readW ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 :=
  hf.readW (r := ⟨(S s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.iv_scr.symm.sub_left (UPre.scr_sub (by omega_using [h₂]))
    · exact hp.data_scr.symm.sub_left (UPre.scr_sub (by omega_using [h₂]))
    · exact Offset.disjoint_base _ h₁ (by omega_using [h₂])
    · exact hp.b_scr.symm.sub_left (UPre.scr_sub (by omega_using [h₂]))) (by decide)

theorem UPre.ret_stk {s₀ : State} (_hp : UPre s₀) : (retR s₀).Disjoint (stkR s₀) := by
  have := Offset.disjoint_below_above ((E s₀).setWidth 64) (m := 24) (a := 0) (l := 4) (by decide)
  rw [add0] at this
  exact this.symm

/-- The return address, which nothing writes. -/
theorem ret_read {s₀ : State} (hp : UPre s₀) {m : Mem}
    (hf : Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) m) :
    m.readW ((E s₀).setWidth 64) 32 = s₀.mem.readW ((E s₀).setWidth 64) 32 :=
  (UPre.big_of hf).readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.ret_iv
    · exact hp.ret_data
    · exact hp.ret_scr
    · exact hp.ret_stk) (by decide)

theorem epilogue_wp {M : Mode} {s₀ : State} (hp : UPre s₀) {s : State} (h : LInv M s₀ (N s₀) s) :
    WP isa (.block (restore 5)) s fun s' => (abiPreserved s₀ s' ∧ (modeX86 M).post s₀ s') ∧
      s'.mem = s.mem ∧ s'.gpr .esp = E s₀ ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hsc : (arg s₀ 5).toNat + 2176 ≤ 2 ^ 32 := hp.scr_fit
  have rdwr : s.rd ++ s.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have sl : ∀ r d, (r, d) ∈ saved → s.mem.readW ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r :=
    fun r d hrd => by
      have hb := saved_bound _ hrd
      rw [slot_read hp h.frame hb.1 hb.2, savedMem_slot s₀ hrd]
  have hall : (blks s₀).take (N s₀) = blks s₀ := List.take_of_length_le (by simp [Spec.Cbc.blocksAt])
  have hnil : (blks s₀).drop (N s₀) = [] := List.drop_of_length_le (by simp [Spec.Cbc.blocksAt])
  rw [restore_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide))
    (hp.arg_keep (UPre.big_of h.frame) (by decide)) fun s₁ u₁ => ?_
  refine Spill.restore_ofNat_ok saved saved_fits (by rw [u₁.gpr]; omega_using [hsc]) saved_ne_eax (fun p hp' => ?_)
    (fun p hp' => by rw [u₁.gpr, u₁.mem]; exact sl p.1 p.2 hp') fun s₂ r₂ => WP.block_nil ⟨?_, by rw [r₂.mem, u₁.mem],
      by rw [r₂.abi (by decide) (by decide) (by rw [u₁.other _ (by decide), h.esp]) .esp (by simp [calleeSaved])],
      by rw [r₂.rd, u₁.rd], by rw [r₂.wr, u₁.wr]⟩
  · have hb := saved_bound p hp'
    rw [u₁.gpr, u₁.rd, u₁.wr, rdwr]
    exact ⟨scrR s₀, by simp, Offset.contains_base _ (by omega_using [hb]) (by omega_using [hb])⟩
  refine ⟨⟨r₂.abi (by decide) (by decide) (by rw [u₁.other _ (by decide), h.esp]), ?_⟩, ?_, ?_⟩
  · rw [r₂.mem, u₁.mem]; exact ret_read hp h.frame
  · show Spec.Cbc.blocksAt s₂.mem ((Dp s₀).setWidth 64) (N s₀) = _
    rw [r₂.mem, u₁.mem, h.data]; simp only [outK, hall, hnil, List.append_nil]
  · show bytesAt s₂.mem ((Iv s₀).setWidth 64) 16 = _
    rw [r₂.mem, u₁.mem, h.iv]; simp only [chainK, hall]

/-- The registers saved and the arguments set up, `mid` run unless there are
no blocks, and the registers restored, when `mid` takes the invariant from no
blocks to all of them (as `body`'s loop does, `whole_wp`). -/
theorem ends_wp {M : Mode} {mid : Prog isa} {s₀ : State} (h0 : (modeX86 M).pre s₀)
    (hm : UPre s₀ → 0 < N s₀ → ∀ {s₁ : State}, LInv M s₀ 0 s₁ → WP isa mid s₁ (LInv M s₀ (N s₀))) :
    WP isa (.seq (.block setup) (.seq (.ite .e (.block []) mid) (.block (restore 5)))) s₀
      fun s' => abiPreserved s₀ s' ∧ (modeX86 M).post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ ⟨⟨h₁, hz⟩, _⟩ =>
    WP.seq (WP.mono (ends_mid_wp (fun hn => hm hp hn h₁) h₁ hz) fun _ h₂ =>
      (epilogue_wp hp h₂).mono fun _ h => h.1))

theorem whole_wp {M : Mode} {body : Prog isa} (hb : BodyOk M body) {s₀ : State} (h0 : (modeX86 M).pre s₀) :
    WP isa (whole body) s₀ fun s' => abiPreserved s₀ s' ∧ (modeX86 M).post s₀ s' :=
  ends_wp h0 fun hp hn _ h => loop_ok hb hp hn h

end VG.Proof.AesCbc.X86

end

end

/-!
# AES-CBC on x86: one block

`encBody_ok` and `decBody_ok`: one run of `encBody` or `decBody` takes the
loop invariant from `k` blocks to `k + 1` (`BodyOk`), for any implementation
of the block functions (`BlocksImpl`).
-/

@[expose] public section

namespace VG.Proof.AesCbc.X86

open VG VG.X86 VG.Impl.AesCbc.X86
open VG.Impl.CmacAes.X86 (argOp advance xor4 zero4)
open VG.Proof.CmacAes.X86 (wp_arg xor4_ok zero4_ok add0 arg_ofNat saved_bound)
open VG.Proof.MdStream.X86 (Upd wp_mov wp_movi)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Spec.Aes (bytesAt)

/-- The block `esi` points at, as a 32-bit address. -/
abbrev D32 (s₀ : State) (k : Nat) : BitVec 32 := Dp s₀ + BitVec.ofNat 32 (16 * k)

/-- The saved ciphertext block. -/
abbrev Sv (s₀ : State) : Addr := (S s₀).setWidth 64 + BitVec.ofNat 64 2048

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.d32 {k : Nat} (hk : k < N s₀) : (D32 s₀ k).setWidth 64 = blk s₀ k := hp.dataA hk

theorem UPre.blk_iv {k : Nat} (hk : k < N s₀) : (⟨blk s₀ k, 16⟩ : Region).Disjoint (ivR s₀) :=
  hp.iv_data.symm.sub_left (UPre.data_sub hk)

theorem UPre.blk_sv {k : Nat} (hk : k < N s₀) : (⟨blk s₀ k, 16⟩ : Region).Disjoint ⟨Sv s₀, 16⟩ :=
  (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (UPre.scr_sub (by decide))

theorem UPre.iv_sv : (ivR s₀).Disjoint ⟨Sv s₀, 16⟩ := hp.iv_scr.sub_right (UPre.scr_sub (by decide))

theorem UPre.sv_scr : (⟨Sv s₀, 16⟩ : Region).Disjoint ⟨(S s₀).setWidth 64, 2048⟩ :=
  Offset.disjoint_base _ (by decide) (by have := hp.scr_fit; omega_using [])

/-- The stack arguments, in a state whose memory differs only within `Big`. -/
theorem UPre.args_of {m : Mem} (hf : Frame (Big s₀) s₀.mem m) :
    ∀ i < 6, m.readW (argAddr s₀ i) 32 = arg s₀ i := fun _ hi => hp.arg_keep hf hi

/-- The arguments of a call on block `k`, with the working space at the start
of the scratch buffer. -/
theorem UPre.blkPre {k : Nat} (hk : k < N s₀) {s : State}
    (eax : s.gpr .eax = W s₀) (ecx : s.gpr .ecx = arg s₀ 1) (ebx : s.gpr .ebx = D32 s₀ k)
    (edi : s.gpr .edi = 1) (ebp : s.gpr .ebp = S s₀) (esp : s.gpr .esp = E s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    BlkPre s (W s₀) (D32 s₀ k) (S s₀) (R s₀) := by
  obtain hb : below (s.gpr .esp) 24 = stkR s₀ := by rw [esp]; exact hp.below_eq
  obtain hd := hp.d32 hk
  obtain qN := hp.dataN hk
  have hdf := hp.data_fit
  refine ⟨eax, by rw [ecx]; exact arg_ofNat s₀ 1, ebx, edi, ebp, hp.rounds, by rw [esp]; exact hp.esp24,
    ?_, hp.sch_scr.sub_right (Region.sub_prefix (by decide)), ?_, by rw [hb]; exact hp.b_sch, ?_,
    by rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide)), hp.sch_fit, ?_,
    by have := hp.scr_fit; omega_using [this], ?_, ?_⟩
  · rw [hd]; exact hp.sch_data.sub_right (UPre.data_sub hk)
  · rw [hd]; exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide))
  · rw [hb, hd]; exact hp.b_data.sub_right (UPre.data_sub hk)
  · rw [qN]; omega_using [hk, hdf]
  · rw [hrd, hwr, hp.rd, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
  · rw [hwr, hp.wr, hd]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨dataR s₀, by simp, 16 * k, rfl, by simp; omega_using [hk]⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

omit hp in
theorem covBlk {k : Nat} (hk : k < N s₀) {rs : List Region} (h : dataR s₀ ∈ rs) :
    Covers [⟨blk s₀ k, 16⟩] rs :=
  Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨dataR s₀, h, 16 * k, rfl, by simp; omega_using [hk]⟩

omit hp in
theorem covIv {rs : List Region} (h : ivR s₀ ∈ rs) : Covers [⟨(Iv s₀).setWidth 64, 16⟩] rs :=
  Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨ivR s₀, h, 0, by simp, by simp⟩

omit hp in
theorem covSv {rs : List Region} (h : scrR s₀ ∈ rs) : Covers [⟨Sv s₀, 16⟩] rs :=
  Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s₀, h, 2048, rfl, by simp⟩

end

section
variable {s₀ : State}

/-- The frame of a step, in the regions the invariant allows. -/
theorem stepFrame {k : Nat} (hk : k < N s₀) {m m' : Mem}
    (hf : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] m m') :
    Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨dataR s₀, by simp, UPre.data_sub hk⟩
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, fun _ h => h⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩

/-- A frame within the regions a step may change, from the frames of its pieces. -/
theorem stepIn {k : Nat} {r : Region}
    (h : r = ⟨blk s₀ k, 16⟩ ∨ r = ivR s₀ ∨ Region.Sub r ⟨(S s₀).setWidth 64, 2064⟩ ∨ r = stkR s₀) :
    ∃ r' ∈ [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀], Region.Sub r r' := by
  rcases h with rfl | rfl | h | rfl
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

end

theorem one {r : Region} {P : Addr} (hd : (⟨P, 16⟩ : Region).Disjoint r) :
    ∀ r' ∈ [r], (⟨P, 16⟩ : Region).Disjoint r' := fun r' hr' => by
  simp only [List.mem_singleton] at hr'; subst hr'; exact hd

/-! ## The arguments of the call -/

/-- What the code before the call leaves. -/
structure PreA (s₀ : State) (k : Nat) (s : State) (m : Mem) (s₁ : State) : Prop where
  pre : BlkPre s₁ (W s₀) (D32 s₀ k) (S s₀) (R s₀)
  esi : s₁.gpr .esi = s.gpr .esi
  esp : s₁.gpr .esp = s.gpr .esp
  mem : s₁.mem = m
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem callArgs_eq : callArgs = [.mov .eax (argOp 0), .mov .ecx (argOp 1), .mov .ebx (.reg .esi),
    .mov .edi (.imm 1), .mov .ebp (argOp 5)] := rfl

theorem callArgs_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (hesi : s.gpr .esi = D32 s₀ k) (hesp : s.gpr .esp = E s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hargs : ∀ i < 6, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i) :
    WP isa (.block callArgs) s (PreA s₀ k s s.mem) := by
  obtain hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [hrd, hwr]
  rw [callArgs_eq]
  refine wp_arg (s₀ := s₀) hesp (by rw [hrw]; exact hp.arg_in (by decide)) (hargs 0 (by decide)) fun s₁ u₁ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₁.other _ (by decide), hesp]) (by rw [u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₁.mem]; exact hargs 1 (by decide)) fun s₂ u₂ => ?_
  refine wp_mov fun s₃ u₃ => wp_movi fun s₄ u₄ => ?_
  refine wp_arg (s₀ := s₀)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hesp])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact hargs 5 (by decide)) fun s₅ u₅ => WP.block_nil ?_
  obtain keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .ebx → r ≠ .edi → r ≠ .ebp → s₅.gpr r = s.gpr r :=
    fun r ha hc hb hd hp' => by
      rw [u₅.other _ hp', u₄.other _ hd, u₃.other _ hb, u₂.other _ hc, u₁.other _ ha]
  obtain rd₅ : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain wr₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  obtain esp₅ : s₅.gpr .esp = E s₀ := by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hesp]
  refine ⟨hp.blkPre hk ?_ ?_ ?_ ?_ u₅.gpr esp₅ (by rw [rd₅, hrd]) (by rw [wr₅, hwr]),
    keep _ (by decide) (by decide) (by decide) (by decide) (by decide), by rw [esp₅, hesp],
    by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem], rd₅, wr₅⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide),
      hesi]
  · rw [u₅.other _ (by decide), u₄.gpr]

/-! ## Encryption -/

theorem encPre_eq : encPre = .mov .ebx (argOp 2) :: (xor4 .esi .ebx .esi 0 0 0 ++ callArgs) := rfl

theorem encA_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀)
    {s : State} (h : LInv (cbcMode true) s₀ k s) :
    WP isa (.block encPre) s (PreA s₀ k s
      (Proof.Cmac.xor4Mem s.mem (blk s₀ k) (blk s₀ k) ((Iv s₀).setWidth 64))) := by
  obtain hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  obtain big := UPre.big_of h.frame
  obtain hargs := hp.args_of big
  obtain hd := hp.d32 hk
  obtain qN := hp.dataN hk
  have hdf := hp.data_fit
  have hiv := hp.iv_fit
  rw [encPre_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide)) (hargs 2 (by decide)) fun s₁ u₁ => ?_
  obtain i₁ : s₁.gpr .esi = D32 s₀ k := by rw [u₁.other _ (by decide), h.esi]
  have b₁ : s₁.gpr .ebx = Iv s₀ := u₁.gpr
  obtain rw₁ : s₁.rd ++ s₁.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [u₁.rd, u₁.wr, h.rd, h.wr, hp.rd, hp.wr]; rfl
  obtain w₁ : s₁.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [u₁.wr, h.wr, hp.wr]
  refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [i₁, qN]; omega_using [hk, hdf]) (by rw [b₁]; omega_using [hiv]) (by rw [i₁, qN]; omega_using [hk, hdf])
    (by rw [i₁, add0, hd, rw₁]; exact covBlk hk (by simp))
    (by rw [b₁, add0, rw₁]; exact covIv (by simp))
    (by rw [i₁, add0, hd, w₁]; exact covBlk hk (by simp)) fun s₂ g₂ => ?_
  obtain m₂ : s₂.mem = Proof.Cmac.xor4Mem s.mem (blk s₀ k) (blk s₀ k) ((Iv s₀).setWidth 64) := by
    rw [g₂.mem, i₁, b₁, add0, add0, hd, u₁.mem]
  obtain f₂ : Frame [⟨blk s₀ k, 16⟩] s.mem s₂.mem := by rw [m₂]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  obtain big₂ : Frame (Big s₀) s₀.mem s₂.mem := big.trans (f₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, UPre.data_sub hk⟩)
  refine WP.mono (callArgs_wp hp hk (by rw [g₂.gpr _ (by decide) (by decide), i₁])
    (by rw [g₂.gpr _ (by decide) (by decide), u₁.other _ (by decide), h.esp])
    (by rw [g₂.rd, u₁.rd, h.rd]) (by rw [g₂.wr, u₁.wr, h.wr]) (hp.args_of big₂)) fun s₃ a => ?_
  exact ⟨a.pre, by rw [a.esi, g₂.gpr _ (by decide) (by decide), u₁.other _ (by decide)],
    by rw [a.esp, g₂.gpr _ (by decide) (by decide), u₁.other _ (by decide)], by rw [a.mem, m₂],
    by rw [a.rd, g₂.rd, u₁.rd], by rw [a.wr, g₂.wr, u₁.wr]⟩

theorem encPost_eq : encPost = .mov .ebx (argOp 2) :: (zero4 .ebx 0 ++ (xor4 .ebx .esi .ebx 0 0 0 ++ advance)) := rfl

theorem encBody_okB (v : BlocksImpl) : BodyOkB (cbcMode true) (encBody v.enc) v.encWritten := by
  intro s₀ hp k hk s h
  have hd := hp.d32 hk
  have qN := hp.dataN hk
  have hdf := hp.data_fit
  have hiv := hp.iv_fit
  refine WP.seq (WP.mono (encA_wp hp hk h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (blk_call_tail v.encOk v.encWrittenOk v.encNosp v.encStack a.pre) fun s₂ ⟨c, fc⟩ => ?_)
  have esp₁ : s₁.gpr .esp = E s₀ := by rw [a.esp, h.esp]
  have hb : below (s₁.gpr .esp) 24 = stkR s₀ := by rw [esp₁]; exact hp.below_eq
  -- Memory so far.
  have f₁ : Frame [⟨blk s₀ k, 16⟩] s.mem s₁.mem := by rw [a.mem]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  have f₂ : Frame [⟨blk s₀ k, 16⟩, ⟨(S s₀).setWidth 64, 2048⟩, stkR s₀] s₁.mem s₂.mem := by
    have fr := c.frame; rw [hb, hd] at fr; exact fr
  have fs₂ : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s₂.mem :=
    (f₁.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inl rfl)).trans
      (f₂.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact stepIn (.inl rfl)
        · exact stepIn (.inr (.inr (.inl (Region.sub_prefix (by decide)))))
        · exact stepIn (.inr (.inr (.inr rfl))))
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem := (UPre.big_of h.frame).trans (f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, UPre.data_sub hk⟩)
  have big₂ : Frame (Big s₀) s₀.mem s₂.mem := (UPre.big_of h.frame).trans ((stepFrame hk fs₂).sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  have esi₂ : s₂.gpr .esi = D32 s₀ k := by rw [c.saved .esi (by simp [calleeSaved]), a.esi, h.esi]
  have esp₂ : s₂.gpr .esp = E s₀ := by rw [c.saved .esp (by simp [calleeSaved]), esp₁]
  have rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [c.rd, c.wr, a.rd, a.wr, h.rd, h.wr]
  have w₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [c.wr, a.wr, h.wr, hp.wr]
  rw [encPost_eq]
  refine wp_arg (s₀ := s₀) esp₂ (by rw [rw₂]; exact hp.arg_in (by decide)) (hp.args_of big₂ 2 (by decide))
    fun s₃ u₃ => ?_
  have b₃ : s₃.gpr .ebx = Iv s₀ := u₃.gpr
  refine zero4_ok (by decide) (by rw [b₃]; omega_using [hiv]) (by rw [b₃, add0, u₃.wr, w₂]; exact covIv (by simp))
    fun s₄ g₄ m₄ rd₄ wr₄ => ?_
  have b₄ : s₄.gpr .ebx = Iv s₀ := by rw [g₄ _ (by decide), b₃]
  have i₄ : s₄.gpr .esi = D32 s₀ k := by rw [g₄ _ (by decide), u₃.other _ (by decide), esi₂]
  have rw₄ : s₄.rd ++ s₄.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rd₄, wr₄, u₃.rd, u₃.wr, rw₂, hp.rd, hp.wr]; rfl
  refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [b₄]; omega_using [hiv]) (by rw [i₄, qN]; omega_using [hk, hdf]) (by rw [b₄]; omega_using [hiv])
    (by rw [b₄, add0, rw₄]; exact covIv (by simp))
    (by rw [i₄, add0, hd, rw₄]; exact covBlk hk (by simp))
    (by rw [b₄, add0, wr₄, u₃.wr, w₂]; exact covIv (by simp)) fun s₅ g₅ => ?_
  have m₅ : s₅.mem = copy4Mem s₂.mem ((Iv s₀).setWidth 64) (blk s₀ k) := by
    rw [g₅.mem, b₄, i₄, add0, add0, hd, m₄, b₃, add0, u₃.mem]; rfl
  have f₅ : Frame [ivR s₀] s₂.mem s₅.mem := by rw [m₅]; exact copy4Mem_frame _ _ _
  have fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s₅.mem :=
    fs₂.trans (f₅.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inr (.inl rfl)))
  have big₅ : Frame (Big s₀) s₀.mem s₅.mem := (UPre.big_of h.frame).trans ((stepFrame hk fStep).sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  refine WP.mono (advance_wp hp hk (by rw [g₅.gpr _ (by decide) (by decide), i₄])
    (by rw [g₅.gpr _ (by decide) (by decide), g₄ _ (by decide), u₃.other _ (by decide), esp₂])
    (hp.args_of big₅) (by rw [g₅.rd, g₅.wr, rd₄, wr₄, u₃.rd, u₃.wr, rw₂]))
    fun s₆ ⟨esi₆, esp₆, _, mem₆, rd₆, wr₆, zf₆⟩ => ⟨⟨?_, zf₆⟩, ?_⟩
  -- The new block, and the chaining value.
  have hblk := h.block hk
  have newBlk : bytesAt s₆.mem (blk s₀ k) 16 =
      Spec.Cbc.aesWith (R s₀) (bytesAt s₀.mem ((W s₀).setWidth 64) (16 * (R s₀ + 1)))
        (Spec.Cbc.xor ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk))
          (Spec.Cbc.next (iv0 s₀) (outK (cbcMode true) s₀ k))) := by
    rw [mem₆, Proof.Cmac.bytesAt_frame f₅ (one (hp.blk_iv hk)) (by decide), ← hd, c.out, hd,
      ← UPre.sched_bytes hp big₁, ← aesWith_state, a.mem, xorIn4_bytes _ (hp.blk_iv hk), hblk, h.iv]
    rfl
  have newIv : bytesAt s₆.mem ((Iv s₀).setWidth 64) 16 = bytesAt s₆.mem (blk s₀ k) 16 := by
    rw [mem₆, m₅, copy4Mem_bytes _ (hp.blk_iv hk).symm,
      Proof.Cmac.bytesAt_frame (copy4Mem_frame s₂.mem ((Iv s₀).setWidth 64) (blk s₀ k)) (one (hp.blk_iv hk))
        (by decide)]
  have hl : (outK (cbcMode true) s₀ k).length = k := by
    rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega_using [hk]
  have outSucc :
      outK (cbcMode true) s₀ (k + 1) = outK (cbcMode true) s₀ k ++ [bytesAt s₆.mem (blk s₀ k) 16] := by
    rw [newBlk]
    simp only [outK, cbcMode_out, cbc, ciphOf, ite_true, take_succ_blks s₀ hk, encrypt_snoc]
  refine ⟨esi₆, esp₆, by rw [rd₆, g₅.rd, rd₄, u₃.rd, c.rd, a.rd, h.rd],
    by rw [wr₆, g₅.wr, wr₄, u₃.wr, c.wr, a.wr, h.wr], by rw [mem₆]; exact h.frame.trans (stepFrame hk fStep),
    ?_, ?_⟩
  · rw [mem₆, hp.blocksAt_step hk fStep, h.data, ← mem₆, outSucc,
      set_prefix _ _ _ hl (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [newIv]
    simp only [chainK, cbcMode_chain, cts, ite_true, outSucc, next_snoc]
  -- What the step changed.
  have fc' : Frame [⟨blk s₀ k, 16⟩, ⟨(S s₀).setWidth 64, v.encWritten⟩, stkR s₀] s₁.mem s₂.mem := by
    have fr := fc; rw [hb, hd] at fr; exact fr
  rw [mem₆]
  refine (f₁.sub fun r hr => ?_).trans ((fc'.sub fun r hr => ?_).trans (f₅.sub fun r hr => ?_))
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, UPre.data_sub hk⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨dataR s₀, by simp, UPre.data_sub hk⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩

theorem encBody_ok (v : BlocksImpl) : BodyOk (cbcMode true) (encBody v.enc) := BodyOkB.ok (encBody_okB v)

/-! ## Decryption -/

theorem decPre_eq : decPre = .mov .ebp (argOp 5) :: (zero4 .ebp cOff ++ (xor4 .ebp .esi .ebp cOff 0 cOff ++ callArgs)) :=
  rfl

theorem decA_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀)
    {s : State} (h : LInv (cbcMode false) s₀ k s) :
    WP isa (.block decPre) s (PreA s₀ k s (copy4Mem s.mem (Sv s₀) (blk s₀ k))) := by
  obtain hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  obtain big := UPre.big_of h.frame
  obtain hargs := hp.args_of big
  obtain hd := hp.d32 hk
  obtain qN := hp.dataN hk
  have hdf := hp.data_fit
  have hsc := hp.scr_fit
  rw [decPre_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide)) (hargs 5 (by decide)) fun s₁ u₁ => ?_
  have p₁ : s₁.gpr .ebp = S s₀ := u₁.gpr
  obtain w₁ : s₁.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [u₁.wr, h.wr, hp.wr]
  refine zero4_ok (by decide) (by rw [p₁]; unfold cOff; omega_using [hsc]) (by rw [p₁, w₁]; exact covSv (by simp))
    fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  obtain p₂ : s₂.gpr .ebp = S s₀ := by rw [g₂ _ (by decide), p₁]
  obtain i₂ : s₂.gpr .esi = D32 s₀ k := by rw [g₂ _ (by decide), u₁.other _ (by decide), h.esi]
  obtain rw₂ : s₂.rd ++ s₂.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rd₂, wr₂, u₁.rd, u₁.wr, h.rd, h.wr, hp.rd, hp.wr]; rfl
  refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [p₂]; unfold cOff; omega_using [hsc]) (by rw [i₂, qN]; omega_using [hk, hdf]) (by rw [p₂]; unfold cOff; omega_using [hsc])
    (by rw [p₂, rw₂]; exact covSv (by simp))
    (by rw [i₂, add0, hd, rw₂]; exact covBlk hk (by simp))
    (by rw [p₂, wr₂, w₁]; exact covSv (by simp)) fun s₃ g₃ => ?_
  obtain m₃ : s₃.mem = copy4Mem s.mem (Sv s₀) (blk s₀ k) := by
    rw [g₃.mem, p₂, i₂, add0, hd, m₂, p₁, u₁.mem]; rfl
  obtain f₃ : Frame [⟨Sv s₀, 16⟩] s.mem s₃.mem := by rw [m₃]; exact copy4Mem_frame _ _ _
  obtain big₃ : Frame (Big s₀) s₀.mem s₃.mem := big.trans (f₃.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩)
  refine WP.mono (callArgs_wp hp hk (by rw [g₃.gpr _ (by decide) (by decide), i₂])
    (by rw [g₃.gpr _ (by decide) (by decide), g₂ _ (by decide), u₁.other _ (by decide), h.esp])
    (by rw [g₃.rd, rd₂, u₁.rd, h.rd]) (by rw [g₃.wr, wr₂, u₁.wr, h.wr]) (hp.args_of big₃)) fun s₄ a => ?_
  exact ⟨a.pre, by rw [a.esi, g₃.gpr _ (by decide) (by decide), g₂ _ (by decide), u₁.other _ (by decide)],
    by rw [a.esp, g₃.gpr _ (by decide) (by decide), g₂ _ (by decide), u₁.other _ (by decide)], by rw [a.mem, m₃],
    by rw [a.rd, g₃.rd, rd₂, u₁.rd], by rw [a.wr, g₃.wr, wr₂, u₁.wr]⟩

theorem decPost_eq : decPost = .mov .ebx (argOp 2) :: (xor4 .esi .ebx .esi 0 0 0 ++
    (.mov .ebp (argOp 5) :: (zero4 .ebx 0 ++ (xor4 .ebx .ebp .ebx 0 cOff 0 ++ advance)))) := rfl

theorem decBody_okB (v : BlocksImpl) : BodyOkB (cbcMode false) (decBody v.dec) v.decWritten := by
  intro s₀ hp k hk s h
  have hd := hp.d32 hk
  have qN := hp.dataN hk
  have hdf := hp.data_fit
  have hiv := hp.iv_fit
  have hsc := hp.scr_fit
  refine WP.seq (WP.mono (decA_wp hp hk h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (blk_call_tail v.decOk v.decWrittenOk v.decNosp v.decStack a.pre) fun s₂ ⟨c, fc⟩ => ?_)
  have esp₁ : s₁.gpr .esp = E s₀ := by rw [a.esp, h.esp]
  have hb : below (s₁.gpr .esp) 24 = stkR s₀ := by rw [esp₁]; exact hp.below_eq
  have svSub : Region.Sub ⟨Sv s₀, 16⟩ ⟨(S s₀).setWidth 64, 2064⟩ := Offset.sub_base _ (by decide)
  -- Memory so far.
  have f₁ : Frame [⟨Sv s₀, 16⟩] s.mem s₁.mem := by rw [a.mem]; exact copy4Mem_frame _ _ _
  have f₂ : Frame [⟨blk s₀ k, 16⟩, ⟨(S s₀).setWidth 64, 2048⟩, stkR s₀] s₁.mem s₂.mem := by
    have fr := c.frame; rw [hb, hd] at fr; exact fr
  have fs₂ : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s₂.mem :=
    (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inr (.inr (.inl svSub)))).trans
      (f₂.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact stepIn (.inl rfl)
        · exact stepIn (.inr (.inr (.inl (Region.sub_prefix (by decide)))))
        · exact stepIn (.inr (.inr (.inr rfl))))
  have bigOf : ∀ {m : Mem}, Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem m →
      Frame (Big s₀) s₀.mem m := fun hf => (UPre.big_of h.frame).trans ((stepFrame hk hf).sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem := bigOf (f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inr (.inr (.inl svSub))))
  have big₂ := bigOf fs₂
  have esi₂ : s₂.gpr .esi = D32 s₀ k := by rw [c.saved .esi (by simp [calleeSaved]), a.esi, h.esi]
  have esp₂ : s₂.gpr .esp = E s₀ := by rw [c.saved .esp (by simp [calleeSaved]), esp₁]
  have rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [c.rd, c.wr, a.rd, a.wr, h.rd, h.wr]
  have rwl : s₂.rd ++ s₂.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rw₂, hp.rd, hp.wr]; rfl
  have w₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [c.wr, a.wr, h.wr, hp.wr]
  rw [decPost_eq]
  refine wp_arg (s₀ := s₀) esp₂ (by rw [rw₂]; exact hp.arg_in (by decide)) (hp.args_of big₂ 2 (by decide))
    fun s₃ u₃ => ?_
  have b₃ : s₃.gpr .ebx = Iv s₀ := u₃.gpr
  have i₃ : s₃.gpr .esi = D32 s₀ k := by rw [u₃.other _ (by decide), esi₂]
  refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [i₃, qN]; omega_using [hk, hdf]) (by rw [b₃]; omega_using [hiv]) (by rw [i₃, qN]; omega_using [hk, hdf])
    (by rw [i₃, add0, hd, u₃.rd, u₃.wr, rwl]; exact covBlk hk (by simp))
    (by rw [b₃, add0, u₃.rd, u₃.wr, rwl]; exact covIv (by simp))
    (by rw [i₃, add0, hd, u₃.wr, w₂]; exact covBlk hk (by simp)) fun s₄ g₄ => ?_
  have m₄ : s₄.mem = Proof.Cmac.xor4Mem s₂.mem (blk s₀ k) (blk s₀ k) ((Iv s₀).setWidth 64) := by
    rw [g₄.mem, i₃, b₃, add0, add0, hd, u₃.mem]
  have f₄ : Frame [⟨blk s₀ k, 16⟩] s₂.mem s₄.mem := by rw [m₄]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  have big₄ : Frame (Big s₀) s₀.mem s₄.mem := bigOf (fs₂.trans (f₄.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inl rfl)))
  have esp₄ : s₄.gpr .esp = E s₀ := by rw [g₄.gpr _ (by decide) (by decide), u₃.other _ (by decide), esp₂]
  have rw₄ : s₄.rd ++ s₄.wr = s₀.rd ++ s₀.wr := by rw [g₄.rd, g₄.wr, u₃.rd, u₃.wr, rw₂]
  refine wp_arg (s₀ := s₀) esp₄ (by rw [rw₄]; exact hp.arg_in (by decide)) (hp.args_of big₄ 5 (by decide))
    fun s₅ u₅ => ?_
  have b₅ : s₅.gpr .ebx = Iv s₀ := by rw [u₅.other _ (by decide), g₄.gpr _ (by decide) (by decide), b₃]
  have p₅ : s₅.gpr .ebp = S s₀ := u₅.gpr
  have w₅ : s₅.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [u₅.wr, g₄.wr, u₃.wr, w₂]
  refine zero4_ok (by decide) (by rw [b₅]; omega_using [hiv]) (by rw [b₅, add0, w₅]; exact covIv (by simp))
    fun s₆ g₆ m₆ rd₆ wr₆ => ?_
  have b₆ : s₆.gpr .ebx = Iv s₀ := by rw [g₆ _ (by decide), b₅]
  have p₆ : s₆.gpr .ebp = S s₀ := by rw [g₆ _ (by decide), p₅]
  have rw₆ : s₆.rd ++ s₆.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rd₆, wr₆, u₅.rd, u₅.wr, rw₄, hp.rd, hp.wr]; rfl
  refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [b₆]; omega_using [hiv]) (by rw [p₆]; unfold cOff; omega_using [hsc]) (by rw [b₆]; omega_using [hiv])
    (by rw [b₆, add0, rw₆]; exact covIv (by simp))
    (by rw [p₆, rw₆]; exact covSv (by simp))
    (by rw [b₆, add0, wr₆, w₅]; exact covIv (by simp)) fun s₇ g₇ => ?_
  have m₇ : s₇.mem = copy4Mem s₄.mem ((Iv s₀).setWidth 64) (Sv s₀) := by
    rw [g₇.mem, b₆, p₆, add0, m₆, b₅, add0, u₅.mem]; rfl
  have f₇ : Frame [ivR s₀] s₄.mem s₇.mem := by rw [m₇]; exact copy4Mem_frame _ _ _
  have fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s₇.mem :=
    (fs₂.trans (f₄.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inl rfl))).trans
      (f₇.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inr (.inl rfl)))
  refine WP.mono (advance_wp hp hk
    (by rw [g₇.gpr _ (by decide) (by decide), g₆ _ (by decide), u₅.other _ (by decide),
      g₄.gpr _ (by decide) (by decide), i₃])
    (by rw [g₇.gpr _ (by decide) (by decide), g₆ _ (by decide), u₅.other _ (by decide), esp₄])
    (hp.args_of (bigOf fStep)) (by rw [g₇.rd, g₇.wr, rd₆, wr₆, u₅.rd, u₅.wr, rw₄]))
    fun s₈ ⟨esi₈, esp₈, _, mem₈, rd₈, wr₈, zf₈⟩ => ⟨⟨?_, zf₈⟩, ?_⟩
  have callIv : ∀ r ∈ [⟨blk s₀ k, 16⟩, ⟨(S s₀).setWidth 64, 2048⟩, stkR s₀], (ivR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.blk_iv hk).symm
    · exact hp.iv_scr.sub_right (Region.sub_prefix (by decide))
    · exact hp.b_iv.symm
  have callSv : ∀ r ∈ [⟨blk s₀ k, 16⟩, ⟨(S s₀).setWidth 64, 2048⟩, stkR s₀], (⟨Sv s₀, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.blk_sv hk).symm
    · exact hp.sv_scr
    · exact (hp.b_scr.sub_right (UPre.scr_sub (by decide))).symm
  have hblk := h.block hk
  have ivIn : bytesAt s₂.mem ((Iv s₀).setWidth 64) 16 = Spec.Cbc.next (iv0 s₀) ((blks s₀).take k) := by
    rw [Proof.Cmac.bytesAt_frame f₂ callIv (by decide), a.mem,
      Proof.Cmac.bytesAt_frame (copy4Mem_frame _ _ _) (one hp.iv_sv) (by decide), h.iv]
    rfl
  have blkIn : bytesAt s₁.mem (blk s₀ k) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
    rw [a.mem, Proof.Cmac.bytesAt_frame (copy4Mem_frame _ _ _) (one (hp.blk_sv hk)) (by decide), hblk]
  have newBlk : bytesAt s₈.mem (blk s₀ k) 16 =
      Spec.Cbc.xor (Spec.Cbc.aesInvWith (R s₀) (bytesAt s₀.mem ((W s₀).setWidth 64) (16 * (R s₀ + 1)))
          ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk)))
        (Spec.Cbc.next (iv0 s₀) ((blks s₀).take k)) := by
    rw [mem₈, Proof.Cmac.bytesAt_frame f₇ (one (hp.blk_iv hk)) (by decide), m₄, xorIn4_bytes _ (hp.blk_iv hk),
      ivIn, ← hd, c.out, hd, ← UPre.sched_bytes hp big₁, ← aesInvWith_state, blkIn]
  have newIv : bytesAt s₈.mem ((Iv s₀).setWidth 64) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
    rw [mem₈, m₇, copy4Mem_bytes _ hp.iv_sv, m₄,
      Proof.Cmac.bytesAt_frame (Proof.Cmac.xor4Mem_frame _ _ _ _) (one (hp.blk_sv hk).symm) (by decide),
      Proof.Cmac.bytesAt_frame f₂ callSv (by decide), a.mem, copy4Mem_bytes _ (hp.blk_sv hk).symm, hblk]
  have hl : (outK (cbcMode false) s₀ k).length = k := by
    rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega_using [hk]
  have outSucc :
      outK (cbcMode false) s₀ (k + 1) = outK (cbcMode false) s₀ k ++ [bytesAt s₈.mem (blk s₀ k) 16] := by
    rw [newBlk]
    simp only [outK, cbcMode_out, cbc, ciphOf, Bool.false_eq_true, ite_false, take_succ_blks s₀ hk, decrypt_snoc]
  refine ⟨esi₈, esp₈, by rw [rd₈, g₇.rd, rd₆, u₅.rd, g₄.rd, u₃.rd, c.rd, a.rd, h.rd],
    by rw [wr₈, g₇.wr, wr₆, u₅.wr, g₄.wr, u₃.wr, c.wr, a.wr, h.wr],
    by rw [mem₈]; exact h.frame.trans (stepFrame hk fStep), ?_, ?_⟩
  · rw [mem₈, hp.blocksAt_step hk fStep, h.data, ← mem₈, outSucc,
      set_prefix _ _ _ hl (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [newIv]
    simp only [chainK, cbcMode_chain, cts, Bool.false_eq_true, ite_false, take_succ_blks s₀ hk, next_snoc]
  -- What the step changed.
  have fc' : Frame [⟨blk s₀ k, 16⟩, ⟨(S s₀).setWidth 64, v.decWritten⟩, stkR s₀] s₁.mem s₂.mem := by
    have fr := fc; rw [hb, hd] at fr; exact fr
  rw [mem₈]
  refine (f₁.sub fun r hr => ?_).trans ((fc'.sub fun r hr => ?_).trans
    ((f₄.sub fun r hr => ?_).trans (f₇.sub fun r hr => ?_)))
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨dataR s₀, by simp, UPre.data_sub hk⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, UPre.data_sub hk⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩

theorem decBody_ok (v : BlocksImpl) : BodyOk (cbcMode false) (decBody v.dec) := BodyOkB.ok (decBody_okB v)


/-! ## Zeroing the saved block and registers -/

theorem zero4_at (m : Mem) (c : Addr) {j : Nat} (hj : j < 16) :
    Proof.Cmac.zero4 m c (c + BitVec.ofNat 64 j) = 0 := by
  obtain h := congrArg (·[j]?) (Proof.Cmac.zero4_bytes m c)
  simp only [bytesAt, Spec.Cmac.zeros, List.getElem?_map, List.getElem?_range hj, List.getElem?_replicate, hj,
    ite_true, Option.map_some, Option.some.injEq] at h
  exact h

theorem not_contains {x : Addr} {R : Region} (h : Region.Disjoint ⟨x, 1⟩ R) : ¬ R.Contains x 1 :=
  h x (Region.contains_self _ _)

/-- The prologue, no blocks or `mid` on all of them, and the epilogue that
zeroes what was saved, for a `mid` that changes memory only within
`FB s₀ b`: the contract, and every byte of the scratch buffer from offset
`b` on unchanged or zero. -/
theorem endsZ_wp {M : Mode} {mid : Prog isa} {b : Nat} {s₀ : State} (h0 : (modeX86 M).pre s₀)
    (hmid : ∀ {s₁ : State}, LInv M s₀ 0 s₁ → 0 < N s₀ →
      WP isa mid s₁ fun t => LInv M s₀ (N s₀) t ∧ Frame (FB s₀ b) s₁.mem t.mem) :
    WP isa (.seq (.block Impl.CmacAes.X86.setup)
      (.seq (.ite .e (.block []) mid) (.block (Impl.CmacAes.X86.restore 5 ++ zeroSaved)))) s₀ fun s' =>
      abiPreserved s₀ s' ∧ (modeX86 M).post s₀ s' ∧
      ∀ i, b ≤ i → i < 2176 →
        s'.mem ((S s₀).setWidth 64 + BitVec.ofNat 64 i) = s₀.mem ((S s₀).setWidth 64 + BitVec.ofNat 64 i) ∨
          s'.mem ((S s₀).setWidth 64 + BitVec.ofNat 64 i) = 0 := by
  obtain hp := UPre.of h0
  have hsc := hp.scr_fit
  refine WP.seq (WP.mono (prologue_wp (M := M) hp) fun s₁ ⟨⟨h₁, hz⟩, hm₁⟩ => ?_)
  obtain hite : WP isa (.ite .e (.block []) mid) s₁ fun t =>
      LInv M s₀ (N s₀) t ∧ Frame (FB s₀ b) s₁.mem t.mem := by
    have ev : isa.eval .e s₁ = some (decide (N s₀ = 0)) := by
      show VG.X86.eval .e s₁ = _; rw [MdStream.X86.eval_e, hz]
    by_cases hn : N s₀ = 0
    · refine WP.ite true (by rw [ev]; simp [hn]) (fun _ => WP.block_nil ⟨?_, Frame.refl _ _⟩) (fun h => by cases h)
      rw [hn]; exact h₁
    · exact WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => hmid h₁ (by omega_using [hn])
  refine WP.seq (WP.mono hite fun t ⟨ht, hft⟩ => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (epilogue_wp hp ht) fun s₂ ⟨⟨habi, hpost⟩, hm₂, hesp₂, hrd₂, hwr₂⟩ => ?_
  rw [zeroSaved, List.append_assoc, List.singleton_append]
  refine wp_arg (s₀ := s₀) hesp₂ (by rw [hrd₂, hwr₂, ht.rd, ht.wr]; exact hp.arg_in (by decide))
    (by rw [hm₂]; exact hp.arg_keep (UPre.big_of ht.frame) (by decide)) fun s₃ u₃ => ?_
  have c₃ : s₃.gpr .ecx = S s₀ := u₃.gpr
  obtain w₃ : s₃.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [u₃.wr, hwr₂, ht.wr, hp.wr]
  refine zero4_ok (b := .ecx) (d := cOff) (by decide) (by rw [c₃]; unfold cOff; omega_using [hsc])
    (by rw [c₃, w₃]; exact covSv (by simp)) fun s₄ g₄ m₄ rd₄ wr₄ => ?_
  obtain c₄ : s₄.gpr .ecx = S s₀ := by rw [g₄ _ (by decide), c₃]
  refine zero4_ok (b := .ecx) (d := cOff + 16) (is := []) (by decide) (by rw [c₄]; unfold cOff; omega_using [hsc])
    (by
      rw [c₄, wr₄, w₃]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨scrR s₀, by simp, 2064, rfl, by simp⟩) fun s₅ g₅ m₅ rd₅ wr₅ => WP.block_nil ?_
  rw [c₄] at m₅
  rw [c₃] at m₄
  -- Memory: only `[2048, 2080)` of the scratch buffer changed since the restore, to zero.
  let Z : Region := ⟨(S s₀).setWidth 64 + BitVec.ofNat 64 2048, 32⟩
  obtain fz : Frame [Z] s₂.mem s₅.mem := by
    rw [m₅, m₄, u₃.mem]
    refine (Proof.Cmac.frame_store4 _ 0 0 0 0 |>.sub fun r hr => ?_).trans
      (Proof.Cmac.frame_store4 _ 0 0 0 0 |>.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨Z, List.mem_singleton_self _, Offset.sub _ (by unfold cOff; omega_using []) (by unfold cOff; omega_using [])⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨Z, List.mem_singleton_self _, Offset.sub _ (by unfold cOff; omega_using []) (by unfold cOff; omega_using [])⟩
  obtain zS : Region.Sub Z (scrR s₀) := UPre.scr_sub (by decide)
  obtain g₅' : ∀ r, r ≠ .eax → r ≠ .ecx → s₅.gpr r = s₂.gpr r := fun r h1 h2 => by
    rw [g₅ r h1, g₄ r h1, u₃.other r h2]
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, fun i h1 h2 => ?_⟩
  · have h1 : r ≠ .eax := by rintro rfl; simp [calleeSaved] at hr
    obtain h2 : r ≠ .ecx := by rintro rfl; simp [calleeSaved] at hr
    rw [g₅' r h1 h2]; exact habi.1 r hr
  · rw [fz.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.ret_scr.sub_right zS) (by decide)]
    exact habi.2
  · obtain ⟨hd, hi⟩ := hpost
    refine ⟨?_, ?_⟩
    · show Spec.Cbc.blocksAt s₅.mem ((Dp s₀).setWidth 64) (N s₀) = _
      rw [← hd]
      simp only [Spec.Cbc.blocksAt]
      refine List.map_congr_left fun j hj => Proof.Cmac.bytesAt_frame fz (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_scr.sub_left (UPre.data_sub (List.mem_range.mp hj))).sub_right zS
    · show bytesAt s₅.mem ((Iv s₀).setWidth 64) 16 = _
      rw [← hi]
      exact Proof.Cmac.bytesAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_scr.sub_right zS) (by decide)
  · have hx1 : (scrR s₀).Contains ((S s₀).setWidth 64 + BitVec.ofNat 64 i) 1 :=
      Offset.contains_base _ (by omega_using [h2]) (by omega_using [h2])
    rw [show cOff = 2048 from rfl] at m₄ m₅
    by_cases hzi : 2048 ≤ i ∧ i < 2080
    · right
      rw [m₅]
      by_cases hhi : 2064 ≤ i
      · rw [show i = 2048 + 16 + (i - 2064) by omega_using [hhi], BitVec.ofNat_add (2048 + 16), ← BitVec.add_assoc]
        exact zero4_at _ _ (by omega_using [hzi])
      · have zf : Frame [⟨(S s₀).setWidth 64 + BitVec.ofNat 64 (2048 + 16), 16⟩] s₄.mem
            (Proof.Cmac.zero4 s₄.mem ((S s₀).setWidth 64 + BitVec.ofNat 64 (2048 + 16))) :=
          Proof.Cmac.frame_store4 _ 0 0 0 0
        rw [zf _ fun r hr => ?_, m₄]
        · rw [show i = 2048 + (i - 2048) by omega_using [hzi], BitVec.ofNat_add 2048, ← BitVec.add_assoc]
          exact zero4_at _ _ (by omega_using [hhi])
        · simp only [List.mem_singleton] at hr; subst hr
          exact not_contains (Offset.disjoint _ (.inl (by omega_using [hhi])) (by omega_using [h2]) (by omega_using []))
    · left
      rw [fz _ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact not_contains (Offset.disjoint _ (by omega_using [hzi]) (by omega_using [h2]) (by omega_using [])),
        hm₂, hft _ fun r hr => ?_, hm₁]
      · refine Spill.saveMem_frame (rs := [⟨(S s₀).setWidth 64 + BitVec.ofNat 64 2064, 16⟩])
          (List.mem_singleton_self _) _ _ _ _ (fun p hp' => ?_) _ fun r hr => ?_
        · have := saved_bound p hp'
          exact Offset.contains _ this.1 (by omega_using [this]) (by omega_using [])
        · simp only [List.mem_singleton] at hr; subst hr
          exact not_contains (Offset.disjoint _ (by omega_using [hzi]) (by omega_using [h2]) (by omega_using []))
      · simp only [FB, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact fun hc => hp.iv_scr _ hc hx1
        · exact fun hc => hp.data_scr _ hc hx1
        · exact not_contains (Offset.disjoint_base _ h1 (by omega_using [h2]))
        · exact not_contains (Offset.disjoint _ (by omega_using [hzi]) (by omega_using [h2]) (by omega_using []))
        · exact fun hc => hp.b_scr _ hc hx1

/-- `wholeZ body`, for a `body` that changes memory only within `FB s₀ b`:
the contract, and every byte of the scratch buffer from offset `b` on
unchanged or zero. -/
theorem wholeZ_wp {M : Mode} {body : Prog isa} {b : Nat} (hb : BodyOkB M body b)
    {s₀ : State} (h0 : (modeX86 M).pre s₀) :
    WP isa (wholeZ body) s₀ fun s' => abiPreserved s₀ s' ∧ (modeX86 M).post s₀ s' ∧
      ∀ i, b ≤ i → i < 2176 →
        s'.mem ((S s₀).setWidth 64 + BitVec.ofNat 64 i) = s₀.mem ((S s₀).setWidth 64 + BitVec.ofNat 64 i) ∨
          s'.mem ((S s₀).setWidth 64 + BitVec.ofNat 64 i) = 0 :=
  endsZ_wp h0 fun h hn => loop_okB hb (UPre.of h0) hn h

end VG.Proof.AesCbc.X86
