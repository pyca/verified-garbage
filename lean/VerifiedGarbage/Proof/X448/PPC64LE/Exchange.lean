module

public import VerifiedGarbage.Proof.X448.Contract
public import VerifiedGarbage.Proof.Xdh.PPC64LE
public import VerifiedGarbage.Proof.X448.PPC64LE.Verified
public import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Xdh.PPC64LE
meta import VerifiedGarbage.Proof.X448.PPC64LE.Verified
meta import VerifiedGarbage.Spec.X448.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.X448.Contract

/-!
# X448 exchange, with RFC 7748's check, on PPC64LE

Untrusted: everything here is checked by Lean. `vg_x448` is a callee of
`Impl.Xdh.PPC64LE.exchange` (`callee`) by its shared contract, so
`vg_x448_exchange`, which calls it and checks its result
(`Proof/Xdh/PPC64LE.lean`), is `Verified` against its shared contract, with
the 48 bytes of stack its frame uses (`exchange_verified`). `vg_x448_base`
calls it too, with the base point in its frame (`Base.verified`).
-/

@[expose] public section

namespace VG.Proof.X448.PPC64LE.Exchange

open VG VG.PPC64LE VG.Proof.Xdh.PPC64LE

theorem callee : Callee 56 8192 Spec.X448.x448 Impl.X448.PPC64LE.x448
    (Proof.X448.x448Contract PPC64LE.abi) where
  hv := Proof.X448.PPC64LE.x448_verified.1
  hct := Proof.X448.PPC64LE.x448_verified.2.1
  pre s h := by
    obtain ⟨rd, wr, d1, d2, d3, d4, d5, b0, b1, b2, b3⟩ := h
    sig_pre [Proof.X448.x448Contract, Proof.X448.x448Sig, PPC64LE.abi, PPC64LE.argRegs]
    sig_reduce [Proof.X448.x448Contract, Proof.X448.x448Sig, PPC64LE.abi, PPC64LE.argRegs, List.getD]
    sig_and_intros
    all_goals first
      | with_reducible assumption
      | trivial
      | omega
      | exact Region.Disjoint.symm ‹_›
  post s s' h := by
    sig_post [Proof.X448.x448Contract, Proof.X448.x448Sig, PPC64LE.abi, PPC64LE.argRegs] at h
    exact h
  pub s₁ s₂ h := by
    obtain ⟨q0, q1, q2, q3, qsp⟩ := h
    sig_pub [Proof.X448.x448Contract, Proof.X448.x448Sig, PPC64LE.abi, PPC64LE.argRegs]
    sig_reduce [Proof.X448.x448Contract, Proof.X448.x448Sig, PPC64LE.abi, PPC64LE.argRegs]
    sig_and_intros
    all_goals first | with_reducible assumption | trivial
  nf := by lit_decide

theorem exchange_verified :
    Verified PPC64LE.target (Impl.Xdh.PPC64LE.exchange "vg_x448" Impl.X448.PPC64LE.x448 56)
      (Spec.X448.exchangeContract PPC64LE.abi 48) :=
  Verified.of_correct (k := exContract 56 8192 Spec.X448.x448) (exchange_correct callee (by decide))
    (exchange_ct callee ⟨_, by taint_decide⟩) (by
      contract_implies [Spec.X448.exchangeContract, Spec.X448.exchangeSig, Proof.X448.x448Sig,
        exContract, ExPre, CallPre, ExPost, Pub, PPC64LE.abi, PPC64LE.argRegs]
        [Proof.X448.PPC64LE.x448Sat] using Proof.X448.PPC64LE.x448Sat)

end VG.Proof.X448.PPC64LE.Exchange

/-! ## `vg_x448_base`

`Impl.X448.PPC64LE.x448Base` calls `vg_x448` by its contract (`callee`),
with the base point in its frame: addresses on the stack are offsets of
`K s`, the frame's back chain (`sp - 96` on entry); the link register is at
`K s + 32`, the point's 56 bytes at `K s + 40`, and the call enters with
`sp = K s`. -/

namespace VG.Proof.X448.PPC64LE.Base

open VG VG.PPC64LE VG.Impl.X448.PPC64LE

/-- The contract, with the 96 bytes of stack the frame uses. -/
abbrev spec : Contract isa := Spec.X448.x448BaseContract PPC64LE.abi 96

/-- The frame's back chain, the lowest byte of the stack used. -/
abbrev K (s : State) : Addr := s.sp - BitVec.ofNat 64 96

abbrev OUT (s : State) : Region := ⟨s.gpr .r3, 56⟩
abbrev SC (s : State) : Region := ⟨s.gpr .r4, 56⟩
abbrev WS (s : State) : Region := ⟨s.gpr .r5, 8192⟩
abbrev STK (s : State) : Region := ⟨K s, 96⟩
/-- The frame's local variables, and the point within them. -/
abbrev AR (s : State) : Region := ⟨K s + BitVec.ofNat 64 32, 64⟩
abbrev PT (s : State) : Region := ⟨K s + BitVec.ofNat 64 40, 56⟩

/-- The precondition, spelled out. -/
structure Pre (s : State) : Prop where
  sp : 96 ≤ s.sp.toNat
  rd : s.rd = [SC s]
  wr : s.wr = [OUT s, WS s]
  os : (OUT s).Disjoint (SC s)
  ow : (OUT s).Disjoint (WS s)
  sw : (SC s).Disjoint (WS s)
  ko : (STK s).Disjoint (OUT s)
  ks : (STK s).Disjoint (SC s)
  kw : (STK s).Disjoint (WS s)
  no : (s.gpr .r3).toNat + 56 ≤ 2 ^ 64
  ns : (s.gpr .r4).toNat + 56 ≤ 2 ^ 64
  nw : (s.gpr .r5).toNat + 8192 ≤ 2 ^ 64

theorem pre_of {s : State} (h : spec.pre s) : Pre s := by
  sig_pre [Spec.X448.x448BaseContract, Spec.X448.x448BaseSig, PPC64LE.abi, PPC64LE.argRegs, stackBelow] at h
  obtain ⟨sp, rd, wr, os, ow, sw, ko, ks, kw, no, ns, nw⟩ := h
  exact ⟨sp, rd, wr, os, ow, sw, ko, ks, kw, no, ns, nw⟩

theorem spec_of {s : State} (h : Pre s) : spec.pre s := by
  sig_pre [Spec.X448.x448BaseContract, Spec.X448.x448BaseSig, PPC64LE.abi, PPC64LE.argRegs, stackBelow]
  exact ⟨h.sp, h.rd, h.wr, h.os, h.ow, h.sw, h.ko, h.ks, h.kw, h.no, h.ns, h.nw⟩

/-! ## Addresses on the stack -/

theorem add_add (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem K_toNat {s : State} (h : Pre s) {d : Nat} (hd : d ≤ 96) :
    (K s + BitVec.ofNat 64 d).toNat = (K s).toNat + d := by
  have hk : (K s).toNat + 96 = s.sp.toNat := by
    have := h.sp
    simp only [K, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_using [this]
  have := s.sp.isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_using [hd, hk]

theorem stk_sub (s : State) {d n : Nat} (h : d + n ≤ 96) : Region.Sub ⟨K s + BitVec.ofNat 64 d, n⟩ (STK s) :=
  Offset.sub_base _ h

namespace Pre

variable {s : State}

theorem kO (h : Pre s) {d n : Nat} (hd : d + n ≤ 96) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (OUT s) :=
  h.ko.sub_left (stk_sub s hd)
theorem kS (h : Pre s) {d n : Nat} (hd : d + n ≤ 96) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (SC s) :=
  h.ks.sub_left (stk_sub s hd)
theorem kW (h : Pre s) {d n : Nat} (hd : d + n ≤ 96) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (WS s) :=
  h.kw.sub_left (stk_sub s hd)

end Pre

/-! ## The point -/

/-- A byte at `B + i` of a doubleword written at `B + j`. -/
theorem byte_writeW (m : Mem) (B : Addr) {i j : Nat} (hi : i < 2 ^ 32) (hj : j < 2 ^ 32) (v : BitVec 64) :
    (m.writeW (B + BitVec.ofNat 64 j) v) (B + BitVec.ofNat 64 i) =
      if j ≤ i ∧ i < j + 8 then v.extractLsb' (8 * (i - j)) 8 else m (B + BitVec.ofNat 64 i) := by
  have e : (B + BitVec.ofNat 64 i - (B + BitVec.ofNat 64 j)).toNat = (2 ^ 64 - j + i) % 2 ^ 64 := by
    rw [show B + BitVec.ofNat 64 i - (B + BitVec.ofNat 64 j) = BitVec.ofNat 64 i - BitVec.ofNat 64 j by
      rw [← BitVec.sub_sub, BitVec.add_comm B, BitVec.add_sub_cancel], BitVec.toNat_sub, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega_using [hi]), Nat.mod_eq_of_lt (a := j) (by omega_using [hj])]
  simp only [Mem.writeW, Mem.write, e]
  split <;> split
  · rw [show (2 ^ 64 - j + i) % 2 ^ 64 = i - j by omega_using [‹j ≤ i ∧ i < j + 8›, hi, hj]]; rfl
  · omega
  · omega
  · rfl

/-- The `n` bytes at `p` are `l`, from each of them. -/
theorem bytesAt_eq {m : Mem} {p : Addr} {n : Nat} {l : List Byte} (hl : l.length = n)
    (h : ∀ i < n, m (p + BitVec.ofNat 64 i) = l.getD i 0) : Spec.X448.bytesAt m p n = l := by
  refine List.ext_getElem (by simp [Spec.X448.bytesAt, hl]) fun i h₁ h₂ => ?_
  simp only [Spec.X448.bytesAt, List.getElem_map, List.getElem_range]
  rw [h i (by simpa [Spec.X448.bytesAt] using h₁), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂,
    Option.getD_some]

theorem five_bytes : ∀ i < 8, (5 : BitVec 64).extractLsb' (8 * i) 8 = Spec.X448.basePoint.getD i 0 := by decide

theorem zero_bytes : ∀ i, 8 ≤ i → i < 56 → Spec.X448.basePoint.getD i 0 = 0 := by
  intro i h₁ h₂
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega_using [h₁]⟩
  simp only [Spec.X448.basePoint, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
    List.getElem?_replicate, show j < 55 by omega_using [h₂], ite_true, Option.getD_some]

/-! ## Within the frame -/

/-- What holds within the frame, for the entry state `s`. -/
structure Ctx (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = AR s :: s.wr
  sp : t.sp = K s
  cs : ∀ r ∈ preserved, t.gpr r = s.gpr r
  lr : t.mem.readW (K s + BitVec.ofNat 64 32) 64 = s.lr
  frame : Frame [OUT s, WS s, STK s] s.mem t.mem

theorem exec_addSp12 (t : State) : exec (.addSp .r12 32) t = some (t.write .r12 (t.sp + BitVec.ofNat 64 32)) := rfl

/-- The link register saved, the point written, and the callee's arguments. -/
theorem enter_ok (s : State) :
    WP isa (.block baseEnter) (allocated 96 s) fun t => Ctx s t ∧ t.gpr .r3 = s.gpr .r3 ∧
      t.gpr .r4 = s.gpr .r4 ∧ t.gpr .r5 = K s + BitVec.ofNat 64 40 ∧ t.gpr .r6 = s.gpr .r5 ∧
      Spec.X448.bytesAt t.mem (K s + BitVec.ofNat 64 40) 56 = Spec.X448.basePoint := by
  have e0 : (allocated 96 s).sp = K s := rfl
  have ew : (allocated 96 s).wr = AR s :: s.wr := by
    show (⟨s.sp - BitVec.ofNat 64 96 + BitVec.ofNat 64 32, 96 - 32⟩ : Region) :: s.wr = _
    rfl
  have em : (allocated 96 s).mem = s.mem.write (K s) 8 s.sp := rfl
  have eg : (allocated 96 s).gpr = s.gpr := rfl
  have el : (allocated 96 s).lr = s.lr := rfl
  have er : (allocated 96 s).rd = s.rd := rfl
  generalize allocated 96 s = u at e0 ew em eg el er
  have ha : ∀ d, u.sp + BitVec.ofNat 64 32 + BitVec.ofNat 64 d = K s + BitVec.ofNat 64 (32 + d) := fun d => by
    simp only [e0, add_add]
  have hin : ∀ d, d + 8 ≤ 64 → InRegions u.wr (u.sp + BitVec.ofNat 64 32 + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [ew, ha]
    exact ⟨AR s, by simp, Offset.contains _ (by omega_using []) (by omega_using [hd]) (by omega_using [])⟩
  refine WP.cons exec_mflr ?_
  refine WP.cons (exec_addSp12 _) ?_
  refine WP.cons (exec_store_d (t := .r0) (n := .r12) (off := 0) (by decide) (by decide) (hin 0 (by decide))) ?_
  refine WP.cons (exec_li (d := .r7) (imm := 5) (by decide)) ?_
  refine WP.cons (exec_store_d (t := .r7) (n := .r12) (off := 8) (by decide) (by decide) (hin 8 (by decide))) ?_
  refine WP.cons (exec_li (d := .r7) (imm := 0) (by decide)) ?_
  refine WP.cons (exec_store_d (t := .r7) (n := .r12) (off := 16) (by decide) (by decide) (hin 16 (by decide))) ?_
  refine WP.cons (exec_store_d (t := .r7) (n := .r12) (off := 24) (by decide) (by decide) (hin 24 (by decide))) ?_
  refine WP.cons (exec_store_d (t := .r7) (n := .r12) (off := 32) (by decide) (by decide) (hin 32 (by decide))) ?_
  refine WP.cons (exec_store_d (t := .r7) (n := .r12) (off := 40) (by decide) (by decide) (hin 40 (by decide))) ?_
  refine WP.cons (exec_store_d (t := .r7) (n := .r12) (off := 48) (by decide) (by decide) (hin 48 (by decide))) ?_
  refine WP.cons (exec_store_d (t := .r7) (n := .r12) (off := 56) (by decide) (by decide) (hin 56 (by decide))) ?_
  refine WP.cons (exec_addi (d := .r6) (n := .r5) (imm := 0) (by decide) (by decide)) ?_
  refine WP.cons (exec_addi (d := .r5) (n := .r12) (imm := 8) (by decide) (by decide)) (wp_nil ?_)
  -- The memory, and the registers, after the block.
  refine (?_ : ∀ t : State, t.rd = u.rd → t.wr = u.wr → t.sp = u.sp →
      (∀ r ∈ preserved, t.gpr r = u.gpr r) → t.gpr .r3 = u.gpr .r3 → t.gpr .r4 = u.gpr .r4 →
      t.gpr .r5 = u.sp + BitVec.ofNat 64 32 + BitVec.ofNat 64 8 → t.gpr .r6 = u.gpr .r5 + BitVec.ofNat 64 0 →
      t.mem = (((((((((u.mem.writeW (u.sp + BitVec.ofNat 64 32 + BitVec.ofNat 64 0) u.lr).writeW
        (u.sp + BitVec.ofNat 64 32 + BitVec.ofNat 64 8) (BitVec.ofNat 64 5)).writeW
        (u.sp + BitVec.ofNat 64 32 + BitVec.ofNat 64 16) (BitVec.ofNat 64 0)).writeW
        (u.sp + BitVec.ofNat 64 32 + BitVec.ofNat 64 24) (BitVec.ofNat 64 0)).writeW
        (u.sp + BitVec.ofNat 64 32 + BitVec.ofNat 64 32) (BitVec.ofNat 64 0)).writeW
        (u.sp + BitVec.ofNat 64 32 + BitVec.ofNat 64 40) (BitVec.ofNat 64 0)).writeW
        (u.sp + BitVec.ofNat 64 32 + BitVec.ofNat 64 48) (BitVec.ofNat 64 0)).writeW
        (u.sp + BitVec.ofNat 64 32 + BitVec.ofNat 64 56) (BitVec.ofNat 64 0))) →
      Ctx s t ∧ t.gpr .r3 = s.gpr .r3 ∧ t.gpr .r4 = s.gpr .r4 ∧ t.gpr .r5 = K s + BitVec.ofNat 64 40 ∧
        t.gpr .r6 = s.gpr .r5 ∧ Spec.X448.bytesAt t.mem (K s + BitVec.ofNat 64 40) 56 = Spec.X448.basePoint)
    _ rfl rfl rfl (fun r hr => by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl <;> rfl) rfl rfl rfl rfl rfl
  intro t trd twr tsp tcs t3 t4 t5 t6 tm
  simp only [ha, em, Nat.reduceAdd] at tm
  rw [BitVec.add_zero] at t6
  have hk : STK s ∈ [OUT s, WS s, STK s] := by simp
  have kc : ∀ {d : Nat}, d + 8 ≤ 96 → (STK s).Contains (K s + BitVec.ofNat 64 d) 8 :=
    fun hd => Offset.contains_base _ hd (by omega_using [hd])
  refine ⟨⟨trd.trans er, twr.trans ew, tsp.trans e0, fun r hr => (tcs r hr).trans (congrFun eg r), ?_, ?_⟩,
    by rw [t3, eg], by rw [t4, eg], by rw [t5, ha], by rw [t6, eg], ?_⟩
  · have sep : ∀ {e : Nat}, 40 ≤ e → e + 8 ≤ 96 →
        Mem.Sep (K s + BitVec.ofNat 64 32) (64 / 8) (K s + BitVec.ofNat 64 e) (64 / 8) :=
      fun h₁ h₂ => Offset.sep _ (Or.inl (by omega_using [h₁])) (by omega_using []) (by omega_using [h₂])
    rw [tm, Mem.readW_writeW_sep (sep (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep (by decide) (by decide)) (by decide), Mem.readW_writeW_self64, el]
  · rw [tm]
    have f0 : Frame [OUT s, WS s, STK s] s.mem (s.mem.write (K s) 8 s.sp) :=
      (Frame.refl _ _).write hk (n := 8) s.sp (Region.contains_self' (a := K s) (by decide))
    have fw : ∀ {m m' : Mem}, Frame [OUT s, WS s, STK s] m m' → ∀ d, d + 8 ≤ 96 → ∀ v : BitVec 64,
        Frame [OUT s, WS s, STK s] m (m'.writeW (K s + BitVec.ofNat 64 d) v) :=
      fun f _ hd v => f.writeW hk v (kc hd)
    exact fw (fw (fw (fw (fw (fw (fw (fw f0 32 (by decide) _) 40 (by decide) _) 48 (by decide) _) 56 (by decide) _)
      64 (by decide) _) 72 (by decide) _) 80 (by decide) _) 88 (by decide) _
  · rw [tm]
    refine bytesAt_eq (by decide) fun i hi => ?_
    have b : ∀ j, j < 2 ^ 32 → ∀ (m : Mem) (v : BitVec 64), (m.writeW (K s + BitVec.ofNat 64 j) v)
        (K s + BitVec.ofNat 64 (40 + i)) = if j ≤ 40 + i ∧ 40 + i < j + 8 then v.extractLsb' (8 * (40 + i - j)) 8
          else m (K s + BitVec.ofNat 64 (40 + i)) :=
      fun j hj m v => byte_writeW m (K s) (by omega_using [hi]) hj v
    rw [add_add, b 88 (by decide), b 80 (by decide), b 72 (by decide), b 64 (by decide), b 56 (by decide),
      b 48 (by decide), b 40 (by decide), b 32 (by decide)]
    repeat' split
    all_goals first
      | omega
      | (rw [show 40 + i - 40 = i by omega_using []]; exact five_bytes i (by omega))
      | (rw [zero_bytes i (by omega) hi]; simp)

/-! ## The call -/

/-- Bytes outside the regions a frame lists are kept. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.X448.bytesAt m' p n = Spec.X448.bytesAt m p n :=
  List.map_congr_left fun _ hi => Frame.bytes hf (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- What `vg_x448` may read and write. -/
abbrev callRd (s : State) : List Region := [SC s, PT s]
abbrev callWr (s : State) : List Region := [OUT s, WS s]

theorem call_gpr (t : State) (rd wr : List Region) {r : Reg} (hr : r ∈ [Reg.r3, .r4, .r5, .r6]) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ (by revert r; decide)]

theorem call_pre {s t : State} (h : Pre s) (h3 : t.gpr .r3 = s.gpr .r3) (h4 : t.gpr .r4 = s.gpr .r4)
    (h5 : t.gpr .r5 = K s + BitVec.ofNat 64 40) (h6 : t.gpr .r6 = s.gpr .r5) :
    Xdh.PPC64LE.CallPre 56 8192 (t.callEntry.withRegions (callRd s) (callWr s)) := by
  simp only [Xdh.PPC64LE.CallPre, Xdh.PPC64LE.outR, Xdh.PPC64LE.scR, Xdh.PPC64LE.ptR, Xdh.PPC64LE.wsR,
    State.withRegions_rd, State.withRegions_wr, call_gpr t _ _ (r := .r3) (by simp), call_gpr t _ _ (r := .r4) (by simp),
    call_gpr t _ _ (r := .r5) (by simp), call_gpr t _ _ (r := .r6) (by simp), h3, h4, h5, h6]
  refine ⟨trivial, trivial, h.os, (h.kO (by decide)).symm, h.ow, h.sw, h.kW (by decide), h.no, h.ns, ?_, h.nw⟩
  rw [K_toNat h (by decide)]
  have hk : (K s).toNat + 96 = s.sp.toNat := by
    have := h.sp
    simp only [K, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_using [this]
  have := s.sp.isLt
  omega_using [hk, this]

theorem call_cov {s t : State} (hc : Ctx s t) (h : Pre s) :
    Covers (callRd s ++ callWr s) (t.rd ++ t.wr) ∧ Covers (callWr s) t.wr := by
  rw [hc.rd, hc.wr, h.rd, h.wr]
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨SC s, by simp, 0, (BitVec.add_zero _).symm, Nat.le_of_eq (Nat.zero_add _)⟩
    · exact ⟨AR s, by simp, 8, by rw [add_add], (by decide : 8 + 56 ≤ 64)⟩
    · exact ⟨OUT s, by simp, 0, (BitVec.add_zero _).symm, Nat.le_of_eq (Nat.zero_add _)⟩
    · exact ⟨WS s, by simp, 0, (BitVec.add_zero _).symm, Nat.le_of_eq (Nat.zero_add _)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨OUT s, by simp, 0, (BitVec.add_zero _).symm, Nat.le_of_eq (Nat.zero_add _)⟩
    · exact ⟨WS s, by simp, 0, (BitVec.add_zero _).symm, Nat.le_of_eq (Nat.zero_add _)⟩

/-- The call: `X448(k, 5)` at `out`. -/
theorem call_ok {s t : State} (h : Pre s) (hc : Ctx s t) (h3 : t.gpr .r3 = s.gpr .r3)
    (h4 : t.gpr .r4 = s.gpr .r4) (h5 : t.gpr .r5 = K s + BitVec.ofNat 64 40) (h6 : t.gpr .r6 = s.gpr .r5)
    (hpt : Spec.X448.bytesAt t.mem (K s + BitVec.ofNat 64 40) 56 = Spec.X448.basePoint) :
    WP isa (.call "vg_x448" x448) t fun t' => Ctx s t' ∧
      Spec.X448.bytesAt t'.mem (s.gpr .r3) 56 =
        Spec.X448.x448 (Spec.X448.bytesAt s.mem (s.gpr .r4) 56) Spec.X448.basePoint := by
  refine WP.call Exchange.callee.hv (Exchange.callee.pre _ (call_pre h h3 h4 h5 h6)) (call_cov hc h).1
    (call_cov hc h).2 (fun t' rd' wr' sp' fr' pres' _ post' => ⟨?_, ?_⟩) Exchange.callee.nf
  · have keep : t'.mem.readW (K s + BitVec.ofNat 64 32) 64 = t.mem.readW (K s + BitVec.ofNat 64 32) 64 :=
      fr'.readW (r := ⟨K s + BitVec.ofNat 64 32, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.kO (by decide)
        · exact h.kW (by decide)) (by decide)
    refine ⟨rd'.trans hc.rd, wr'.trans hc.wr, sp'.trans hc.sp, fun r hr => (pres' r hr).trans (hc.cs r hr),
      keep.trans hc.lr, hc.frame.trans (fr'.sub fun r hr => ?_)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · have hpost := Exchange.callee.post _ _ post'
    change Spec.X448.bytesAt _ _ 56 = Spec.X448.x448 (Spec.X448.bytesAt _ _ 56) (Spec.X448.bytesAt _ _ 56) at hpost
    simp only [State.withRegions_mem, State.callEntry_mem, call_gpr t _ _ (r := .r3) (by simp),
      call_gpr t _ _ (r := .r4) (by simp), call_gpr t _ _ (r := .r5) (by simp), h3, h4, h5, hpt] at hpost
    rw [hpost, bytesAt_frame hc.frame (fun r hr => ?_) (by decide)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.os.symm
    · exact h.sw
    · exact h.ks.symm

/-! ## The link register, and the whole function -/

theorem leave_ok {s t : State} (hc : Ctx s t) :
    WP isa (.block baseLeave) t fun t' => t'.sp = t.sp ∧ t'.mem = t.mem ∧
      (∀ r ∈ preserved, t'.gpr r = s.gpr r) ∧ t'.lr = s.lr := by
  refine WP.cons (exec_addSp12 _) ?_
  refine WP.cons (exec_load_d (t := .r0) (n := .r12) (off := 0) (by decide) (by decide) ?_) ?_
  · show InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 32 + BitVec.ofNat 64 0) 8
    rw [hc.wr, hc.sp, add_add]
    exact ⟨AR s, by simp, Offset.contains _ (by omega_using []) (by omega_using []) (by omega_using [])⟩
  refine WP.cons exec_mtlr (wp_nil ⟨rfl, rfl, fun r hr => ?_, ?_⟩)
  · have h0 : ¬r = .r0 := by rintro rfl; revert hr; decide
    have h12 : ¬r = .r12 := by rintro rfl; revert hr; decide
    simp only [RegUpd.gpr_write_of_ne (h := h0), RegUpd.gpr_write_of_ne (h := h12)]; exact hc.cs r hr
  · simp only [RegUpd.gpr_write_self]
    show t.mem.readW (t.sp + BitVec.ofNat 64 32 + BitVec.ofNat 64 0) 64 = _
    rw [hc.sp, add_add]; exact hc.lr

theorem base_ok {s : State} (hs : spec.pre s) :
    WP isa x448Base s fun s' => abiPreserved s s' ∧ spec.post s s' := by
  have h := pre_of hs
  refine WP.alloc (by decide) h.sp (WP.seq (WP.mono (enter_ok s) fun t ⟨hc, h3, h4, h5, h6, hpt⟩ =>
    WP.seq (WP.mono (call_ok h hc h3 h4 h5 h6 hpt) fun t' ⟨hc', hO⟩ =>
      WP.mono (leave_ok hc') fun u ⟨hsp, hm, hcs, hlr⟩ m _ f => ⟨⟨hcs, ?_, hlr⟩, ?_⟩)))
  · show u.sp + BitVec.ofNat 64 96 = s.sp
    rw [hsp, hc'.sp, K, BitVec.sub_add_cancel]
  · sig_post [Spec.X448.x448BaseContract, Spec.X448.x448BaseSig, PPC64LE.abi, PPC64LE.argRegs]
    -- The `free` loses the frame's bytes, which lie apart from `out`.
    rw [← hO, ← hm]
    exact List.map_congr_left fun i hi => lost_byte f h.ko.symm (List.mem_range.mp hi)

/-! ## Constant time, a witness, and the artifact's obligation -/

theorem base_ct : ConstantTime isa spec.pre spec.pub x448Base :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5]) (fun s₁ s₂ _ _ hp => by
    sig_pub [Spec.X448.x448BaseContract, Spec.X448.x448BaseSig, PPC64LE.abi, PPC64LE.argRegs] at hp
    obtain ⟨hsp, h3, h4, h5⟩ := hp
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption) (by taint_decide)

/-- A state satisfying the precondition: `out` at `0x1000`, the scalar at `0x2000`, `scratch` at
`0x4000` and the stack below `0x10000`. -/
def satState : State where
  gpr r := match r with | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x4000 | _ => 0
  lr := 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 56⟩]
  wr := [⟨0x1000, 56⟩, ⟨0x4000, 8192⟩]

theorem sat_pre : Pre satState :=
  ⟨by decide, rfl, rfl, Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), by decide, by decide, by decide⟩

theorem verified : Verified PPC64LE.target x448Base spec :=
  ⟨fun _ h => base_ok h, base_ct, ⟨_, spec_of sat_pre⟩⟩

end VG.Proof.X448.PPC64LE.Base
