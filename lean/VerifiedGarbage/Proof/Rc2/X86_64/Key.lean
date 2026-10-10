import VerifiedGarbage.Proof.Rc2.X86_64.ConstantTime
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Rc2.Contract
import VerifiedGarbage.Proof.Rc2.X86_64.KeyLoop

section

/-! # Public effective-key mask selection -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

theorem small_imm (i : Nat) (hi : i < 256) :
    (BitVec.ofNat 32 i).signExtend 64 = BitVec.ofNat 64 i := by
  rw [index_imm i hi]
  bv_omega

theorem cmpMask_ok (s : State) (i : Nat) (hi : i < 7) :
    ∃ s', runBlock isa [.alu .cmp .r9 (.imm (BitVec.ofNat 32 (i + 1)))] s = some s' ∧
      s'.zf = some (s.gpr .r9 == BitVec.ofNat 64 (i + 1)) ∧ Keep [] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some]
    rfl, ?_⟩
  constructor
  · rw [zf_arithFlags, small_imm _ (by omega_arith)]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    bv_omega
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem setMask_ok (s : State) (i : Nat) (hi : i < 7) :
    ∃ s', runBlock isa [imm .rdx (2 ^ (i + 1) - 1)] s = some s' ∧
      s'.gpr .rdx = BitVec.ofNat 64 (2 ^ (i + 1) - 1) ∧ Keep [.rdx] s s' := by
  refine ⟨_, by
    simp only [imm, runBlock_cons, exec, readSrc]
    rfl, ?_⟩
  constructor
  · rw [gpr_setReg_self]
    apply small_imm
    have bound : ∀ i < 7, 2 ^ (i + 1) - 1 < 256 := by decide
    exact bound i hi
  · exact ⟨fun r hr => gpr_setReg_of_ne _ _ (by simpa using hr), rfl, rfl, rfl⟩

theorem maskBranch_ok (s : State) (i : Nat) (hi : i < 7) :
    WP isa (.seq (.block [.alu .cmp .r9 (.imm (BitVec.ofNat 32 (i + 1)))])
      (.ite .e (.block [imm .rdx (2 ^ (i + 1) - 1)]) (.block []))) s (fun s' =>
        s'.gpr .rdx = (if s.gpr .r9 = BitVec.ofNat 64 (i + 1)
          then BitVec.ofNat 64 (2 ^ (i + 1) - 1) else s.gpr .rdx) ∧ Keep [.rdx] s s') := by
  apply WP.seq
  obtain ⟨s₁, run₁, flag₁, keep₁⟩ := cmpMask_ok s i hi
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  apply WP.ite (s.gpr .r9 == BitVec.ofNat 64 (i + 1)) (by exact flag₁)
  · intro he
    have eq := beq_iff_eq.mp he
    obtain ⟨s₂, run₂, out₂, keep₂⟩ := setMask_ok s₁ i hi
    apply WP.of_runBlock
    refine ⟨s₂, run₂, ?_, ?_⟩
    · rw [ite_eq_left eq]; exact out₂
    · exact (keep₁.weaken (by simp)).trans keep₂
  · intro he
    have ne : s.gpr .r9 ≠ BitVec.ofNat 64 (i + 1) := by simpa using he
    apply WP.block_nil
    refine ⟨?_, keep₁.weaken (by simp)⟩
    rw [ite_eq_right ne]
    exact keep₁.reg .rdx (by simp)

private theorem seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop} :
    WP isa (.seq (.seq a b) c) s Q ↔ WP isa (.seq a (.seq b c)) s Q := by
  constructor
  · intro h
    exact WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)
  · intro h
    exact WP.seq (WP.seq (WP.mono (WP.seq_iff.mp h) fun _ h => WP.seq_iff.mp h))

theorem maskBranches_ok (is : List Nat) (hi : ∀ i ∈ is, i < 7)
    (s : State) (k : Nat) (hk : k < 8) (index : s.gpr .r9 = BitVec.ofNat 64 k) :
    WP isa (is.foldr (fun i rest =>
      .seq (.block [.alu .cmp .r9 (.imm (BitVec.ofNat 32 (i + 1)))])
        (.seq (.ite .e (.block [imm .rdx (2 ^ (i + 1) - 1)]) (.block [])) rest)) (.block []))
      s (fun s' => s'.gpr .rdx = (if k ∈ is.map (· + 1) then
        BitVec.ofNat 64 (2 ^ k - 1) else s.gpr .rdx) ∧ Keep [.rdx] s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨by simp, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.foldr_cons, ← seq_assoc]
    apply WP.seq
    apply WP.mono (maskBranch_ok s i (hi i List.mem_cons_self))
    intro s₁ h₁
    have index₁ := (h₁.2.reg .r9 (by decide)).trans index
    apply WP.mono (ih (fun j hj => hi j (List.mem_cons_of_mem _ hj)) s₁ index₁)
    intro s₂ h₂
    refine ⟨?_, h₁.2.trans h₂.2⟩
    rw [h₂.1, h₁.1, index]
    have eq : BitVec.ofNat 64 k = BitVec.ofNat 64 (i + 1) ↔ k = i + 1 := by
      have bound := hi i List.mem_cons_self
      bv_omega
    simp only [eq, List.map_cons, List.mem_cons]
    by_cases he : k = i + 1
    · subst k; simp
    · by_cases hm : k ∈ is.map (· + 1) <;> simp [he, hm]

theorem maskStart_ok (s : State) :
    ∃ s', runBlock isa [rr .r9 .r15, .alu .and .r9 (.imm 7), imm .rdx 255] s = some s' ∧
      s'.gpr .r9 = s.gpr .r15 &&& 7 ∧ s'.gpr .rdx = 255 ∧ Keep [.rdx, .r9] s s' := by
  refine ⟨_, by
    simp only [rr, imm, runBlock_cons, exec, readSrc]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true]
    rfl
  · exact gpr_setReg_self _ _ _
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags]
    · simp only [rd_setReg, rd_arithFlags]
    · simp only [wr_setReg, wr_arithFlags]

theorem maskCode_ok (s : State) (bits : Nat) (hb : 1 ≤ bits) (hb' : bits ≤ 1024)
    (input : s.gpr .r15 = BitVec.ofNat 64 bits) :
    WP isa maskCode s (fun s' =>
      (s'.gpr .rdx).setWidth 8 = BitVec.ofNat 8 (255 % 2 ^ (8 + bits - 8 * ((bits + 7) / 8))) ∧
      Keep [.rdx, .r9] s s') := by
  rw [maskCode]
  apply WP.seq
  obtain ⟨s₁, run₁, index₁, mask₁, keep₁⟩ := maskStart_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have index : s₁.gpr .r9 = BitVec.ofNat 64 (bits % 8) := by
    rw [index₁, input]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    change bits % 2 ^ 64 &&& (2 ^ 3 - 1) = bits % 8 % 2 ^ 64
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega_arith
  apply WP.mono (maskBranches_ok (List.range 7) (by simp)
    s₁ (bits % 8) (Nat.mod_lt _ (by decide)) index)
  intro s₂ h₂
  refine ⟨?_, keep₁.trans (h₂.2.weaken (by simp))⟩
  rw [h₂.1, mask₁]
  have exponent : 8 + bits - 8 * ((bits + 7) / 8) = if bits % 8 = 0 then 8 else bits % 8 := by
    split <;> omega_arith
  rw [exponent]
  have fact : ∀ r < 8,
      ((if r ∈ (List.range 7).map (· + 1) then BitVec.ofNat 64 (2 ^ r - 1)
        else 255).setWidth 8) = BitVec.ofNat 8 (255 % 2 ^ (if r = 0 then 8 else r)) := by decide
  exact fact _ (Nat.mod_lt _ (by decide))

end VG.Proof.Rc2.X86_64

end

section

section

/-! # The descending effective-key reduction loop -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.Impl.Rc2.X86_64

theorem descendLoop_ok (s : State)
    (hlookup : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 64) 16) (l : KeyBytes) (t8 : Nat) (ht : 1 ≤ t8) (ht' : t8 < 128)
    (len : s.gpr .rbp = BitVec.ofNat 64 t8) (start : s.gpr .rbx = BitVec.ofNat 64 (128 - t8))
    (writable : ∀ i < 128, InRegions s.wr (s.gpr .r14 + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (s.gpr .r14) l 128) :
    WP isa (.loop (.block descendKey) .ne) s (fun s' =>
      s'.gpr .rbx = 0 ∧ KeyFrame s s' ∧
      BytesPrefix s'.mem (s.gpr .r14) (descend l t8 (128 - t8)) 128) := by
  let I (j : Nat) (s' : State) := s'.gpr .rbx = BitVec.ofNat 64 (128 - t8 - j) ∧ KeyFrame s s' ∧
    BytesPrefix s'.mem (s.gpr .r14) (descend l t8 j) 128
  have finish : I (128 - t8) = (fun s' => s'.gpr .rbx = 0 ∧ KeyFrame s s' ∧
      BytesPrefix s'.mem (s.gpr .r14) (descend l t8 (128 - t8)) 128) := by
    funext s'
    simp only [I, Nat.sub_self]
    rfl
  rw [← finish]
  apply forwardLoop (.block descendKey) I (128 - t8) _ 0 (by omega_arith) s
    ⟨start, KeyFrame.refl s, initialPrefix⟩
  intro j hj s₁ ⟨index₁, frame₁, prefix₁⟩
  have outPtr := frame₁.reg .r14 (by decide)
  have len₁ := (frame₁.reg .rbp (by decide)).trans len
  have indexNew : s₁.gpr .rbx - 1#64 = BitVec.ofNat 64 (127 - t8 - j) := by
    rw [index₁, Offset.ofNat_sub_ofNat (show 1 ≤ 128 - t8 - j by omega_arith)]
    congr 1; omega_arith
  have loAddr : s₁.gpr .r14 + (s₁.gpr .rbx - 1#64) + 1#64 =
      s.gpr .r14 + BitVec.ofNat 64 (127 - t8 - j + 1) := by
    rw [outPtr, indexNew, BitVec.add_assoc]
    exact congrArg (s.gpr .r14 + ·) (counter_add _)
  have hiAddr : s₁.gpr .r14 + (s₁.gpr .rbx - 1#64 + s₁.gpr .rbp) =
      s.gpr .r14 + BitVec.ofNat 64 (127 - t8 - j + t8) := by
    rw [outPtr, indexNew, len₁, ← BitVec.ofNat_add]
  have read₁ (i : Nat) (hi : i < 128) :
      InRegions (s₁.rd ++ s₁.wr) (s.gpr .r14 + BitVec.ofNat 64 i) 1 := by
    obtain ⟨r, hr, hc⟩ := writable i hi
    rw [frame₁.wr]
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have write₁ : InRegions s₁.wr (s₁.gpr .r14 + (s₁.gpr .rbx - 1#64)) 1 := by
    rw [frame₁.wr, outPtr, indexNew]
    exact writable _ (by omega_arith)
  have readLo : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .r14 + (s₁.gpr .rbx - 1#64) + 1#64) 1 := by
    rw [loAddr]; exact read₁ _ (by omega_arith)
  have readHi : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .r14 + (s₁.gpr .rbx - 1#64 + s₁.gpr .rbp)) 1 := by
    rw [hiAddr]; exact read₁ _ (by omega_arith)
  apply WP.mono (descendKey_ok s₁ (by
    rw [frame₁.wr, frame₁.reg .r8 (by decide)]; exact hlookup) readLo readHi write₁)
  intro s₂ h₂
  let b := Spec.Rc2.pi ((descend l t8 j).getD (127 - t8 - j + 1) 0 ^^^
    (descend l t8 j).getD (127 - t8 - j + t8) 0)
  have keep₂ : Keep keyTemps {s₁ with
      mem := s₁.mem.writeW (s.gpr .r14 + BitVec.ofNat 64 (127 - t8 - j)) b} s₂ := by
    have h := h₂.2.2
    rw [loAddr, hiAddr, prefix₁ _ (by omega_arith), prefix₁ _ (by omega_arith), outPtr, indexNew] at h
    exact h
  constructor
  · refine ⟨?_, frame₁.step (127 - t8 - j) (by omega_arith) b keep₂, ?_⟩
    · rw [h₂.1]
      change s₁.gpr .rbx - 1#64 = _
      rw [indexNew]
      congr 1; omega_arith
    · rw [keep₂.mem, descend_succ]
      exact prefix₁.write (by decide) (by omega_arith) b
  · rw [h₂.2.1]
    change some ((s₁.gpr .rbx - 1#64) == 0#64) = _
    rw [indexNew]
    have he : 127 - t8 - j = 0 ↔ j + 1 = 128 - t8 := by omega_arith
    have eqZero := counter_eq (127 - t8 - j) 0 (by omega_arith) (by decide)
    simp only [BitVec.sub_zero] at eqZero
    rw [eqZero]
    simp only [he]

end VG.Proof.Rc2.X86_64

end

section

/-! # Forward expansion to 128 bytes -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.Impl.Rc2.X86_64

theorem fillLoop_ok (s : State)
    (hlookup : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 64) 16) (key : List Byte) (ht : 1 ≤ key.length) (ht' : key.length < 128)
    (len : s.gpr .r13 = BitVec.ofNat 64 key.length) (start : s.gpr .rbx = BitVec.ofNat 64 key.length)
    (writable : ∀ i < 128, InRegions s.wr (s.gpr .r14 + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (s.gpr .r14) (fill key 0) key.length) :
    WP isa (.loop (.block fillKey) .ne) s (fun s' =>
      s'.gpr .rbx = 128 ∧ KeyFrame s s' ∧
      BytesPrefix s'.mem (s.gpr .r14) (fill key (128 - key.length)) 128) := by
  let I (j : Nat) (s' : State) := s'.gpr .rbx = BitVec.ofNat 64 (key.length + j) ∧ KeyFrame s s' ∧
    BytesPrefix s'.mem (s.gpr .r14) (fill key j) (key.length + j)
  have finish : I (128 - key.length) = (fun s' => s'.gpr .rbx = 128 ∧ KeyFrame s s' ∧
      BytesPrefix s'.mem (s.gpr .r14) (fill key (128 - key.length)) 128) := by
    funext s'
    simp only [I, Nat.add_sub_of_le (Nat.le_of_lt ht')]
    rfl
  rw [← finish]
  apply forwardLoop (.block fillKey) I (128 - key.length) _ 0 (by omega_arith) s
    ⟨start, KeyFrame.refl s, initialPrefix⟩
  intro j hj s₁ ⟨index₁, frame₁, prefix₁⟩
  have outPtr := frame₁.reg .r14 (by decide)
  have len₁ := (frame₁.reg .r13 (by decide)).trans len
  have loAddr : s₁.gpr .r14 + s₁.gpr .rbx - 1#64 =
      s.gpr .r14 + BitVec.ofNat 64 (key.length + j - 1) := by
    rw [outPtr, index₁]
    exact Offset.add_ofNat_sub _ (by omega_arith)
  have hiAddr : s₁.gpr .r14 + (s₁.gpr .rbx - s₁.gpr .r13) =
      s.gpr .r14 + BitVec.ofNat 64 j := by
    rw [outPtr, index₁, len₁, Offset.ofNat_sub_ofNat (by omega_arith), Nat.add_sub_cancel_left]
  have read₁ (i : Nat) (hi : i < 128) :
      InRegions (s₁.rd ++ s₁.wr) (s.gpr .r14 + BitVec.ofNat 64 i) 1 := by
    obtain ⟨r, hr, hc⟩ := writable i hi
    rw [frame₁.wr]
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have write₁ : InRegions s₁.wr (s₁.gpr .r14 + s₁.gpr .rbx) 1 := by
    rw [frame₁.wr, outPtr, index₁]
    exact writable _ (by omega_arith)
  have readLo : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .r14 + s₁.gpr .rbx - 1#64) 1 := by
    rw [loAddr]; exact read₁ _ (by omega_arith)
  have readHi : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .r14 + (s₁.gpr .rbx - s₁.gpr .r13)) 1 := by
    rw [hiAddr]; exact read₁ _ (by omega_arith)
  apply WP.mono (fillKey_ok s₁ (by
    rw [frame₁.wr, frame₁.reg .r8 (by decide)]; exact hlookup) readLo readHi write₁)
  intro s₂ h₂
  let b := Spec.Rc2.pi ((fill key j).getD (key.length + j - 1) 0 + (fill key j).getD j 0)
  have keep₂ : Keep keyTemps {s₁ with
      mem := s₁.mem.writeW (s.gpr .r14 + BitVec.ofNat 64 (key.length + j)) b} s₂ := by
    have h := h₂.2.2
    rw [loAddr, hiAddr, prefix₁ _ (by omega_arith), prefix₁ _ (by omega_arith), outPtr, index₁] at h
    exact h
  constructor
  · refine ⟨?_, frame₁.step (key.length + j) (by omega_arith) b keep₂, ?_⟩
    · rw [h₂.1, index₁, counter_add, Nat.add_assoc]
    · rw [keep₂.mem, fill_succ]
      have h := prefix₁.extend (show key.length + j < 128 by omega_arith) b
      simpa only [fillStep, Nat.add_sub_cancel_left, Nat.add_assoc] using h
  · rw [h₂.2.1, index₁, counter_add]
    have he : key.length + j + 1 = 128 ↔ j + 1 = 128 - key.length := by omega_arith
    change some ((BitVec.ofNat 64 (key.length + j + 1) - BitVec.ofNat 64 128) == 0#64) = _
    rw [counter_eq _ _ (by omega_arith) (by decide)]
    simp only [he]

end VG.Proof.Rc2.X86_64

end

section

/-! # The key-copy loop -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.Impl.Rc2.X86_64

theorem copyLoop_ok (s : State) (t : Nat) (ht : 1 ≤ t) (ht' : t ≤ 128)
    (len : s.gpr .r13 = BitVec.ofNat 64 t) (zero : s.gpr .rbx = 0)
    (readable : ∀ i < t, InRegions (s.rd ++ s.wr) (s.gpr .r12 + BitVec.ofNat 64 i) 1)
    (writable : ∀ i < 128, InRegions s.wr (s.gpr .r14 + BitVec.ofNat 64 i) 1)
    (sep : (Region.mk (s.gpr .r12) t).Disjoint ⟨s.gpr .r14, 128⟩) :
    WP isa (.loop (.block copyKey) .ne) s (fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 t ∧ KeyFrame s s' ∧
      BytesPrefix s'.mem (s.gpr .r14) (fill (Spec.Rc2.bytesAt s.mem (s.gpr .r12) t) 0) t) := by
  let key := Spec.Rc2.bytesAt s.mem (s.gpr .r12) t
  let I (i : Nat) (s' : State) := s'.gpr .rbx = BitVec.ofNat 64 i ∧ KeyFrame s s' ∧
    BytesPrefix s'.mem (s.gpr .r14) (fill key 0) i
  apply forwardLoop (.block copyKey) I t _ 0 (by omega_arith) s
    ⟨zero, KeyFrame.refl s, fun i hi => by omega_arith⟩
  intro i hi s₁ ⟨index₁, frame₁, prefix₁⟩
  have keyPtr := frame₁.reg .r12 (by decide)
  have outPtr := frame₁.reg .r14 (by decide)
  have len₁ := (frame₁.reg .r13 (by decide)).trans len
  have read₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .r12 + s₁.gpr .rbx) 1 := by
    rw [frame₁.rd, frame₁.wr, keyPtr, index₁]
    exact readable i hi
  have write₁ : InRegions s₁.wr (s₁.gpr .r14 + s₁.gpr .rbx) 1 := by
    rw [frame₁.wr, outPtr, index₁]
    exact writable i (by omega_arith)
  have byte₁ : s₁.mem (s₁.gpr .r12 + s₁.gpr .rbx) = key.getD i 0 := by
    rw [keyPtr, index₁, bytesAt_getD _ _ _ _ hi]
    exact frame₁.mem.bytes (by simpa using sep) (by change t ≤ 2 ^ 64; omega_arith) hi
  obtain ⟨s₂, run₂, index₂, flag₂, keep₂⟩ := copyKey_ok s₁ read₁ write₁
  have keep₂' : Keep keyTemps
      {s₁ with mem := s₁.mem.writeW (s.gpr .r14 + BitVec.ofNat 64 i) (key.getD i 0)} s₂ := by
    rw [byte₁] at keep₂
    simpa only [outPtr, index₁] using keep₂
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  constructor
  · refine ⟨?_, frame₁.step i (by omega_arith) _ keep₂', ?_⟩
    · rw [index₂, index₁, counter_add]
    · rw [keep₂'.mem]
      have prefix₂ := prefix₁.extend (show i < 128 by omega_arith) (key.getD i 0)
      rw [initial_set key i] at prefix₂
      exact prefix₂
  · rw [flag₂, index₁, len₁, counter_add]
    exact congrArg some (counter_eq (i + 1) t (by omega_arith) (by omega_arith))

end VG.Proof.Rc2.X86_64

end

/-! # Key-expansion control and register setup -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

theorem cmp128_ok (s : State) :
    ∃ s', runBlock isa [.alu .cmp .rbx (.imm 128)] s = some s' ∧
      s'.zf = some ((s.gpr .rbx - 128) == 0) ∧ Keep [] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some]
    rfl, ?_⟩
  exact ⟨zf_arithFlags _ _ _ _, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩

theorem maybeFill_ok (s : State)
    (hlookup : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 64) 16) (key : List Byte) (ht : 1 ≤ key.length) (ht' : key.length ≤ 128)
    (len : s.gpr .r13 = BitVec.ofNat 64 key.length) (start : s.gpr .rbx = BitVec.ofNat 64 key.length)
    (writable : ∀ i < 128, InRegions s.wr (s.gpr .r14 + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (s.gpr .r14) (fill key 0) key.length) :
    WP isa (.seq (.block [.alu .cmp .rbx (.imm 128)])
      (.ite .ne (.loop (.block fillKey) .ne) (.block []))) s (fun s' =>
        s'.gpr .rbx = 128 ∧ KeyFrame s s' ∧
        BytesPrefix s'.mem (s.gpr .r14) (fill key (128 - key.length)) 128) := by
  apply WP.seq
  obtain ⟨s₁, run₁, flag₁, keep₁⟩ := cmp128_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have frame₁ := (KeyFrame.refl s).keep (keep₁.weaken (by simp))
  have flag : s₁.zf = some (decide (key.length = 128)) := by
    rw [flag₁, start]
    exact congrArg some (counter_eq _ _ (by omega_arith) (by decide))
  have ptr₁ := keep₁.reg .r14 (by simp)
  by_cases he : key.length = 128
  · apply WP.ite false (by simp only [eval, flag, he, decide_true, Option.map_some, Bool.not_true])
    · simp
    · intro _
      apply WP.block_nil
      refine ⟨?_, frame₁, ?_⟩
      · rw [keep₁.reg .rbx (by simp), start, he]; rfl
      · rw [keep₁.mem]
        simpa only [he, Nat.sub_self] using initialPrefix
  · apply WP.ite true (by simp only [eval, flag, he, decide_false, Option.map_some, Bool.not_false])
    · intro _
      have writes : ∀ i < 128, InRegions s₁.wr (s₁.gpr .r14 + BitVec.ofNat 64 i) 1 := by
        rw [keep₁.wr, ptr₁]; exact writable
      have initial : BytesPrefix s₁.mem (s₁.gpr .r14) (fill key 0) key.length := by
        rw [keep₁.mem, ptr₁]; exact initialPrefix
      apply WP.mono (fillLoop_ok s₁ (by
        rw [keep₁.wr, keep₁.reg .r8 (by simp)]; exact hlookup) key ht (by omega_arith)
        ((keep₁.reg .r13 (by simp)).trans len) ((keep₁.reg .rbx (by simp)).trans start) writes initial)
      intro s₂ h₂
      exact ⟨h₂.1, frame₁.trans h₂.2.1, by rw [ptr₁] at h₂; exact h₂.2.2⟩
    · simp

theorem setReduction_ok (s : State) (bits : Nat) (hb : 1 ≤ bits) (hb' : bits ≤ 1024)
    (input : s.gpr .r15 = BitVec.ofNat 64 bits) :
    ∃ s', runBlock isa [rr .rbp .r15, .alu .add .rbp (.imm 7), .shift .shr .rbp 3,
      imm .rbx 128, .alu .sub .rbx (.reg .rbp)] s = some s' ∧
      s'.gpr .rbp = BitVec.ofNat 64 ((bits + 7) / 8) ∧
      s'.gpr .rbx = BitVec.ofNat 64 (128 - (bits + 7) / 8) ∧ Keep [.rbp, .rbx] s s' := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reduceSub, Nat.reducePow, and_self, BitVec.reduceSignExtend, rr, imm, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, execShift, readSrc, Option.bind_some, Option.map_some,
      gpr_setReg]
    rfl, ?_⟩
  have t8 : (s.gpr .r15 + 7#64) >>> 3 = BitVec.ofNat 64 ((bits + 7) / 8) := by
    rw [input]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_arith
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_true, ite_false]
    exact t8
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_true, ite_false]
    change 128#64 - (s.gpr .r15 + 7#64) >>> 3 = _
    rw [t8]
    exact Offset.ofNat_sub_ofNat (by omega_arith)
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr.1, hr.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    · simp only [rd_setReg, rd_arithFlags, rd_setFlags]
    · simp only [wr_setReg, wr_arithFlags, wr_setFlags]

theorem maybeDescend_ok (s : State)
    (hlookup : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 64) 16) (l : KeyBytes) (t8 : Nat) (ht : 1 ≤ t8) (ht' : t8 ≤ 128)
    (len : s.gpr .rbp = BitVec.ofNat 64 t8) (start : s.gpr .rbx = BitVec.ofNat 64 (128 - t8))
    (writable : ∀ i < 128, InRegions s.wr (s.gpr .r14 + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (s.gpr .r14) l 128) :
    WP isa (.seq (.block [.alu .cmp .rbx (.imm 0)])
      (.ite .ne (.loop (.block descendKey) .ne) (.block []))) s (fun s' =>
        KeyFrame s s' ∧ BytesPrefix s'.mem (s.gpr .r14) (descend l t8 (128 - t8)) 128) := by
  apply WP.seq
  obtain ⟨s₁, run₁, flag₁, keep₁⟩ := cmpZero_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have frame₁ := (KeyFrame.refl s).keep (keep₁.weaken (by simp))
  have flag : s₁.zf = some (decide (t8 = 128)) := by
    rw [flag₁, start]
    have eqZero := counter_eq (128 - t8) 0 (by omega_arith) (by decide)
    simp only [BitVec.sub_zero] at eqZero
    change some (BitVec.ofNat 64 (128 - t8) == 0#64) = _
    rw [eqZero]
    have he : 128 - t8 = 0 ↔ t8 = 128 := by omega_arith
    simp only [he]
  have ptr₁ := keep₁.reg .r14 (by simp)
  by_cases he : t8 = 128
  · apply WP.ite false (by simp only [eval, flag, he, decide_true, Option.map_some, Bool.not_true])
    · simp
    · intro _
      apply WP.block_nil
      refine ⟨frame₁, ?_⟩
      rw [keep₁.mem, he]
      exact initialPrefix
  · apply WP.ite true (by simp only [eval, flag, he, decide_false, Option.map_some, Bool.not_false])
    · intro _
      have writes : ∀ i < 128, InRegions s₁.wr (s₁.gpr .r14 + BitVec.ofNat 64 i) 1 := by
        rw [keep₁.wr, ptr₁]; exact writable
      have initial : BytesPrefix s₁.mem (s₁.gpr .r14) l 128 := by
        rw [keep₁.mem, ptr₁]; exact initialPrefix
      apply WP.mono (descendLoop_ok s₁ (by
        rw [keep₁.wr, keep₁.reg .r8 (by simp)]; exact hlookup) l t8 ht (by omega_arith)
        ((keep₁.reg .rbp (by simp)).trans len) ((keep₁.reg .rbx (by simp)).trans start) writes initial)
      intro s₂ h₂
      exact ⟨frame₁.trans h₂.2.1, by rw [ptr₁] at h₂; exact h₂.2.2⟩
    · simp

end VG.Proof.Rc2.X86_64

end

section

/-! # Composing the RC2 key-expansion stages -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.Impl.Rc2.X86_64

def coreRegs : List Reg := [.r8, .rsp, .r14]

structure CoreFrame (s₀ s : State) : Prop where
  reg : ∀ r ∈ coreRegs, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Frame [⟨s₀.gpr .r14, 128⟩] s₀.mem s.mem

theorem CoreFrame.of_keep {s s' : State} {rs : List Reg} (keep : Keep rs s s')
    (sep : ∀ r ∈ coreRegs, r ∉ rs) : CoreFrame s s' := by
  refine ⟨fun r hr => keep.reg r (sep r hr), keep.rd, keep.wr, ?_⟩
  rw [keep.mem]; exact Frame.refl _ _

theorem CoreFrame.of_key {s s' : State} (h : KeyFrame s s') : CoreFrame s s' := by
  have sep : ∀ r ∈ coreRegs, r ∉ keyTemps := by decide
  exact ⟨fun r hr => h.reg r (sep r hr), h.rd, h.wr, h.mem⟩

theorem CoreFrame.trans {s₀ s₁ s₂ : State} (h₁ : CoreFrame s₀ s₁) (h₂ : CoreFrame s₁ s₂) :
    CoreFrame s₀ s₂ := by
  refine ⟨fun r hr => (h₂.reg r hr).trans (h₁.reg r hr), h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, ?_⟩
  have frame₂ := h₂.mem
  rw [h₁.reg .r14 (by decide)] at frame₂
  exact h₁.mem.trans frame₂

theorem expandCopyFill_ok (s : State)
    (hlookup : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 64) 16) (t : Nat) (ht : 1 ≤ t) (ht' : t ≤ 128)
    (len : s.gpr .r13 = BitVec.ofNat 64 t) (zero : s.gpr .rbx = 0)
    (readable : ∀ i < t, InRegions (s.rd ++ s.wr) (s.gpr .r12 + BitVec.ofNat 64 i) 1)
    (writable : ∀ i < 128, InRegions s.wr (s.gpr .r14 + BitVec.ofNat 64 i) 1)
    (sep : (Region.mk (s.gpr .r12) t).Disjoint ⟨s.gpr .r14, 128⟩) :
    WP isa expandCopyFill s (fun s' => KeyFrame s s' ∧
      BytesPrefix s'.mem (s.gpr .r14) (fill (Spec.Rc2.bytesAt s.mem (s.gpr .r12) t) (128 - t)) 128) := by
  rw [expandCopyFill]
  apply WP.seq
  apply WP.mono (copyLoop_ok s t ht ht' len zero readable writable sep)
  intro s₁ h₁
  have length : (Spec.Rc2.bytesAt s.mem (s.gpr .r12) t).length = t := by
    simp [Spec.Rc2.bytesAt]
  have ptr₁ := h₁.2.1.reg .r14 (by decide)
  have writes : ∀ i < 128, InRegions s₁.wr (s₁.gpr .r14 + BitVec.ofNat 64 i) 1 := by
    rw [h₁.2.1.wr, ptr₁]; exact writable
  apply WP.mono (maybeFill_ok s₁ (by
    rw [h₁.2.1.wr, h₁.2.1.reg .r8 (by decide)]; exact hlookup) (Spec.Rc2.bytesAt s.mem (s.gpr .r12) t)
    (by rw [length]; exact ht) (by rw [length]; exact ht')
    (by rw [length]; exact (h₁.2.1.reg .r13 (by decide)).trans len)
    (by rw [length]; exact h₁.1) writes (by rw [ptr₁, length]; exact h₁.2.2))
  intro s₂ h₂
  exact ⟨h₁.2.1.trans h₂.2.1, by rw [length, ptr₁] at h₂; exact h₂.2.2⟩

theorem reduceDescend_ok (s : State)
    (hlookup : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 64) 16) (l : KeyBytes) (bits : Nat) (hb : 1 ≤ bits) (hb' : bits ≤ 1024)
    (len : s.gpr .rbp = BitVec.ofNat 64 ((bits + 7) / 8))
    (index : s.gpr .rbx = BitVec.ofNat 64 (128 - (bits + 7) / 8))
    (mask : (s.gpr .rdx).setWidth 8 = BitVec.ofNat 8 (255 % 2 ^ (8 + bits - 8 * ((bits + 7) / 8))))
    (writable : ∀ i < 128, InRegions s.wr (s.gpr .r14 + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (s.gpr .r14) l 128) :
    WP isa (.seq (.block reduceKey) (.seq (.block [.alu .cmp .rbx (.imm 0)])
      (.ite .ne (.loop (.block descendKey) .ne) (.block [])))) s (fun s' =>
        KeyFrame s s' ∧ BytesPrefix s'.mem (s.gpr .r14)
          (descend (reduce l bits) ((bits + 7) / 8) (128 - (bits + 7) / 8)) 128) := by
  have bound : 1 ≤ (bits + 7) / 8 ∧ (bits + 7) / 8 ≤ 128 := by omega_arith
  have writes : InRegions s.wr (s.gpr .r14 + s.gpr .rbx) 1 := by
    rw [index]; exact writable _ (by omega_arith)
  have reads : InRegions (s.rd ++ s.wr) (s.gpr .r14 + s.gpr .rbx) 1 := by
    obtain ⟨r, hr, hc⟩ := writes
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  apply WP.seq
  apply WP.mono (reduceKey_ok s hlookup reads writes)
  intro s₁ h₁
  have keep₁ := h₁.2
  rw [index, initialPrefix _ (by omega_arith), mask] at keep₁
  have frame₁ := (KeyFrame.refl s).step _ (by omega_arith) _ keep₁
  have ptr₁ := keep₁.reg .r14 (by decide)
  have prefix₁ : BytesPrefix s₁.mem (s.gpr .r14) (reduce l bits) 128 := by
    rw [keep₁.mem]
    exact initialPrefix.write (by decide) (by omega_arith) _
  have write₁ : ∀ i < 128, InRegions s₁.wr (s₁.gpr .r14 + BitVec.ofNat 64 i) 1 := by
    rw [keep₁.wr, ptr₁]; exact writable
  apply WP.mono (maybeDescend_ok s₁ (by
    rw [keep₁.wr, keep₁.reg .r8 (by decide)]; exact hlookup) (reduce l bits) ((bits + 7) / 8) bound.1 bound.2
    ((keep₁.reg .rbp (by decide)).trans len) (h₁.1.trans index) write₁
    (by rw [ptr₁]; exact prefix₁))
  intro s₂ h₂
  exact ⟨frame₁.trans h₂.1, by rw [ptr₁] at h₂; exact h₂.2⟩

theorem expandReduce_ok (s : State)
    (hlookup : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 64) 16) (l : KeyBytes) (bits : Nat) (hb : 1 ≤ bits) (hb' : bits ≤ 1024)
    (input : s.gpr .r15 = BitVec.ofNat 64 bits)
    (writable : ∀ i < 128, InRegions s.wr (s.gpr .r14 + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (s.gpr .r14) l 128) :
    WP isa expandReduce s (fun s' => CoreFrame s s' ∧ BytesPrefix s'.mem (s.gpr .r14)
      (descend (reduce l bits) ((bits + 7) / 8) (128 - (bits + 7) / 8)) 128) := by
  rw [expandReduce]
  apply WP.seq
  obtain ⟨s₁, run₁, len₁, index₁, keep₁⟩ := setReduction_ok s bits hb hb' input
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  apply WP.seq
  apply WP.mono (maskCode_ok s₁ bits hb hb' ((keep₁.reg .r15 (by decide)).trans input))
  intro s₂ h₂
  have frame := (CoreFrame.of_keep keep₁ (by decide)).trans (CoreFrame.of_keep h₂.2 (by decide))
  have ptr₂ := frame.reg .r14 (by decide)
  have writes : ∀ i < 128, InRegions s₂.wr (s₂.gpr .r14 + BitVec.ofNat 64 i) 1 := by
    rw [frame.wr, ptr₂]; exact writable
  apply WP.mono (reduceDescend_ok s₂ (by
    rw [frame.wr, frame.reg .r8 (by decide)]; exact hlookup) l bits hb hb'
    ((h₂.2.reg .rbp (by decide)).trans len₁) ((h₂.2.reg .rbx (by decide)).trans index₁) h₂.1 writes
    (by rw [ptr₂, h₂.2.mem, keep₁.mem]; exact initialPrefix))
  intro s₃ h₃
  exact ⟨frame.trans (CoreFrame.of_key h₃.1), by rw [ptr₂] at h₃; exact h₃.2⟩

end VG.Proof.Rc2.X86_64

end

section

/-! # Register setup and scratch saves for key expansion -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

def savedReg (i : Nat) : Reg := saved.getD i .rbx

theorem keySave_eq : save .r8 0 = saveCode .r8 savedReg 6 := by rfl

theorem keyRestore_eq : restore .r8 0 = restoreCode .r8 savedReg (List.range 6) := by rfl

theorem pinKey_ok (s : State) :
    ∃ s', runBlock isa [rr .r12 .rdi, rr .r13 .rsi, rr .r14 .rcx, rr .r15 .rdx, imm .rbx 0] s = some s' ∧
      s'.gpr .r12 = s.gpr .rdi ∧ s'.gpr .r13 = s.gpr .rsi ∧
      s'.gpr .r14 = s.gpr .rcx ∧ s'.gpr .r15 = s.gpr .rdx ∧ s'.gpr .rbx = 0 ∧ Keep saved s s' := by
  refine ⟨_, by
    simp only [rr, imm, runBlock_cons, exec, readSrc]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · exact gpr_setReg_self _ _ _
  · constructor
    · intro r hr
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, hr.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]
    · simp only [mem_setReg]
    · simp only [rd_setReg]
    · simp only [wr_setReg]

theorem bytesAt_frame {m m' : Mem} {p : Addr} {n : Nat} {rs : List Region}
    (frame : Frame rs m m') (sep : ∀ r ∈ rs, (Region.mk p n).Disjoint r) (bound : n ≤ 2 ^ 64) :
    Spec.Rc2.bytesAt m' p n = Spec.Rc2.bytesAt m p n := by
  unfold Spec.Rc2.bytesAt
  apply List.map_congr_left
  intro i hi
  exact frame.bytes sep bound (List.mem_range.mp hi)

end VG.Proof.Rc2.X86_64

end

/-! # Verified RC2 key expansion -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.Impl.Rc2.X86_64

def keyContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let out : Region := ⟨s.gpr .rcx, 128⟩
    let scratch : Region := ⟨s.gpr .r8, 512⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [out, scratch] ∧ key.Disjoint out ∧ key.Disjoint scratch ∧
      out.Disjoint scratch ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      Spec.Rc2.validKey (s.gpr .rsi).toNat (s.gpr .rdx).toNat
  post s s' := Spec.Rc2.scheduleAt s'.mem (s.gpr .rcx) =
    Spec.Rc2.expandKey (Spec.Rc2.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (s.gpr .rdx).toNat
  pub := PublicRegs [.rdi, .rsi, .rdx, .rcx, .r8]

theorem key_body_correct (s : State) (hs : keyContract.pre s) :
    WP isa expandKey s (fun s' => gprPreserved s s' ∧ keyContract.post s s') := by
  obtain ⟨hrd, hwr, keyOut, keyScratch, outScratch, retOut, retScratch, ht, ht', hb, hb'⟩ := hs
  have writes : ∀ i < 6, InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .r8, 512⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  rw [expandKey]
  apply WP.seq
  rw [WP.block_append_iff, keySave_eq]
  apply WP.mono (saveCode_ok s .r8 savedReg 6 writes)
  intro s₁ h₁
  obtain ⟨s₂, run₂, key₂, len₂, ptr₂, bits₂, zero₂, keep₂⟩ := pinKey_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have scratchFrame : Frame [⟨s.gpr .r8, 512⟩] s.mem s₂.mem := by
    rw [keep₂.mem, h₁.2.2.2]
    exact saveMem_frame_le _ _ _ 6 64 (by decide) (by decide)
  rw [h₁.1] at key₂ len₂ ptr₂ bits₂
  have rd₂ : s₂.rd = s.rd := keep₂.rd.trans h₁.2.1
  have wr₂ : s₂.wr = s.wr := keep₂.wr.trans h₁.2.2.1
  have r8₂ : s₂.gpr .r8 = s.gpr .r8 := (keep₂.reg .r8 (by decide)).trans (congrFun h₁.1 .r8)
  have rsp₂ : s₂.gpr .rsp = s.gpr .rsp := (keep₂.reg .rsp (by decide)).trans (congrFun h₁.1 .rsp)
  have source₂ : Spec.Rc2.bytesAt s₂.mem (s₂.gpr .r12) (s.gpr .rsi).toNat =
      Spec.Rc2.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat := by
    rw [key₂]
    exact bytesAt_frame scratchFrame (by simpa using keyScratch) (by omega_arith)
  have read₂ : ∀ i < (s.gpr .rsi).toNat,
      InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .r12 + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [rd₂, wr₂, key₂, hrd, hwr]
    exact ⟨⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, by simp,
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have write₂ : ∀ i < 128, InRegions s₂.wr (s₂.gpr .r14 + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [wr₂, ptr₂, hwr]
    exact ⟨⟨s.gpr .rcx, 128⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have lookup₂ : InRegions s₂.wr (s₂.gpr .r8 + BitVec.ofNat 64 64) 16 := by
    rw [wr₂, r8₂, hwr]
    exact ⟨⟨s.gpr .r8, 512⟩, by simp, Offset.contains_base _ (by decide) (by decide)⟩
  apply WP.seq
  apply WP.mono (expandCopyFill_ok s₂ lookup₂ (s.gpr .rsi).toNat ht ht'
    (by simpa using len₂) zero₂ read₂ write₂ (by rw [key₂, ptr₂]; exact keyOut))
  intro s₃ h₃
  apply WP.seq
  have write₃ : ∀ i < 128, InRegions s₃.wr (s₃.gpr .r14 + BitVec.ofNat 64 i) 1 := by
    rw [h₃.1.wr, h₃.1.reg .r14 (by decide)]; exact write₂
  apply WP.mono (expandReduce_ok s₃ (by
    rw [h₃.1.wr, h₃.1.reg .r8 (by decide)]; exact lookup₂) _ (s.gpr .rdx).toNat hb hb'
    (by simpa using (h₃.1.reg .r15 (by decide)).trans bits₂) write₃
    (by rw [h₃.1.reg .r14 (by decide)]; exact h₃.2))
  intro s₄ h₄
  have core := (CoreFrame.of_key h₃.1).trans h₄.1
  have outFrame : Frame [⟨s.gpr .rcx, 128⟩] s₂.mem s₄.mem := by
    have h := core.mem
    rw [ptr₂] at h; exact h
  have r8₄ : s₄.gpr .r8 = s.gpr .r8 := (core.reg .r8 (by decide)).trans r8₂
  have rsp₄ : s₄.gpr .rsp = s.gpr .rsp := (core.reg .rsp (by decide)).trans rsp₂
  have rd₄ := core.rd.trans rd₂
  have wr₄ := core.wr.trans wr₂
  have expanded : BytesPrefix s₄.mem (s.gpr .rcx)
      (Spec.Rc2.expandBytes (Spec.Rc2.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (s.gpr .rdx).toNat) 128 := by
    have h := h₄.2
    rw [h₃.1.reg .r14 (by decide), ptr₂, source₂] at h
    rw [expandBytes_eq]
    have length : (Spec.Rc2.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat).length = (s.gpr .rsi).toNat := by
      simp [Spec.Rc2.bytesAt]
    rw [length]; exact h
  have scratchRead : ∀ i ∈ List.range 6,
      InRegions (s₄.rd ++ s₄.wr) (s₄.gpr .r8 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [rd₄, wr₄, r8₄, hrd, hwr]
    have bound := List.mem_range.mp hi
    exact ⟨⟨s.gpr .r8, 512⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have stored : ∀ i ∈ List.range 6,
      s₄.mem.readW (s₄.gpr .r8 + BitVec.ofNat 64 (8 * i)) 64 = s.gpr (savedReg i) := by
    intro i hi
    have bound := List.mem_range.mp hi
    rw [r8₄, outFrame.readW (r := ⟨s.gpr .r8, 512⟩)
      (Offset.contains_base _ (by omega_arith) (by omega_arith)) (by simpa using outScratch.symm) (by decide),
      keep₂.mem, h₁.2.2.2]
    exact saveMem_read _ _ _ 6 (by decide) i bound
  rw [keyRestore_eq]
  apply WP.mono (restoreCode_ok s₄ .r8 savedReg (List.range 6) s.gpr
    (by decide) scratchRead stored)
  intro s₅ h₅
  constructor
  · constructor
    · intro r hr
      by_cases hm : r ∈ (List.range 6).map savedReg
      · exact h₅.1 r hm
      · have covered : ∀ r ∈ calleeSaved, r ∈ (List.range 6).map savedReg ∨ r = .rsp := by decide
        have he := (covered r hr).resolve_left hm
        subst r
        exact (h₅.2.reg .rsp hm).trans rsp₄
    · have frame : Frame [⟨s.gpr .rcx, 128⟩, ⟨s.gpr .r8, 512⟩] s.mem s₅.mem := by
        rw [h₅.2.mem]
        exact (scratchFrame.mono (fun _ hr => List.mem_cons_of_mem _ hr)).trans
          (outFrame.mono (by simp))
      exact frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _)
        (by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with h | h
          · subst r; exact retOut
          · subst r; exact retScratch) (by decide)
  · change Spec.Rc2.scheduleAt s₅.mem (s.gpr .rcx) = _
    rw [h₅.2.mem]
    exact scheduleAt_expanded expanded

def keySatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 1 | .rdx => 8 | .rcx => 0x2000 | .r8 => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 512⟩]

theorem key_correct (s : State) (hs : keyContract.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ keyContract.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := key_body_correct s hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ha, hp⟩

theorem publicRegs_five (s₁ s₂ : State) : PublicRegs [.rdi, .rsi, .rdx, .rcx, .r8] s₁ s₂ ↔
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 := by
  simp [PublicRegs]

theorem key_verified : Verified target expandKey (Spec.Rc2.expandKeyContract abi) := by
  refine Verified.of_correct key_correct (expandKey_constantTime _) ?_
  sig_implies [Spec.Rc2.expandKeyContract, Spec.Rc2.expandKeySig, abi, argRegs,
    keyContract, publicRegs_five, Spec.Rc2.validKey] [keySatState] using keySatState

end VG.Proof.Rc2.X86_64
