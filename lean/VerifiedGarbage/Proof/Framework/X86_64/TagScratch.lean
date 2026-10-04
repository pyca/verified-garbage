import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.Framework.TagScratch

/-!
# A tag passed through a buffer on the stack (x86-64)

`Verified.tagScratch`: code verified for a function one of whose arguments,
at word `q`, is a buffer of working space whose first 16 bytes also carry a
tag in or out (its contract `sigI.contract`), runs as a function whose
argument there is a pointer to the 16-byte tag alone (`sigO.contract`), when
`withTagScratch` allocates the buffer in a frame on the stack, with `bytes`
more bytes of stack. The frame holds what the code expects at and above
`rsp` on entry, as `withStackArgScratch`'s does (a quadword for its return
address and a copy of the stack arguments), then the tag pointer and the
buffer. Before the code, the frame copies the tag into the buffer and passes
the buffer in the tag pointer's place (`tagSetup`); after it, it copies the
buffer's first 16 bytes back to the tag (`tagOut`). The code runs from the
state after `tagSetup`, with the permissions of its contract (`narrowT`), and
its run there is its run from that state (`Exec.widen`).

The two contracts are related by the caller (`hpre`, `hpost`, `hleak`): the
inner contract's precondition, postcondition and leakage, on the arguments
with the buffer in the tag pointer's place, follow from or give the outer
ones', for memory that agrees on the function's buffers and holds the tag in
the buffer (`TagAgree`) and, on return, holds the buffer's first 16 bytes in
the tag and is otherwise the code's.
-/

namespace VG.X86_64

open VG.Impl.StackScratch.X86_64

/-! ## The blocks -/

theorem ofInt_zero64 : BitVec.ofInt 64 ((0 : Nat) : Int) = 0 := rfl

/-- Byte `i` of a copied quadword. -/
theorem Mem.writeW_readW_apply (m₀ m : Mem) (w t : Addr) {i : Nat} (hi : i < 8) :
    (m.writeW w (m₀.readW t 64)) (w + BitVec.ofNat 64 i) = m₀ (t + BitVec.ofNat 64 i) := by
  simp only [Mem.writeW, Mem.write, Mem.sub_ofNat_toNat w (show i < 2 ^ 64 by omega),
    show i < 64 / 8 by omega, ite_true, Mem.readW, show 64 / 8 = 8 from rfl]
  rw [show (BitVec.setWidth (8 * 8) (BitVec.setWidth 64 (Mem.read m₀ t 8))) = Mem.read m₀ t 8 by
    simp]
  exact Mem.extractLsb'_read m₀ t hi

/-- A quadword write leaves the other bytes. -/
theorem Mem.writeW_apply_of_not {m : Mem} {w x : Addr} {v : BitVec 64}
    (h : ¬ (x - w).toNat < 8) : (m.writeW w v) x = m x := by
  simp only [Mem.writeW, Mem.write, show 64 / 8 = 8 from rfl, h, ite_false]


/-- The state after `tagIn m` from `u`: the tag pointer (`r11`) saved at
`rsp + 8 + 8m` and the tag's two quadwords copied to `rsp + 16 + 8m`. -/
def tagInState (m : Nat) (u : State) : State :=
  let M₁ := u.mem.writeW (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * m)) (u.gpr .r11)
  let M₂ := M₁.writeW (u.gpr .rsp + BitVec.ofNat 64 (16 + 8 * m)) (M₁.readW (u.gpr .r11) 64)
  let v := M₂.readW (u.gpr .r11 + 8#64) 64
  { (u.setReg .r10 (M₁.readW (u.gpr .r11) 64)).setReg .r10 v with
    mem := M₂.writeW (u.gpr .rsp + BitVec.ofNat 64 (24 + 8 * m)) v }

theorem tagIn_run {m : Nat} {u : State}
    (h₁ : InRegions u.wr (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * m)) 8)
    (h₂ : InRegions (u.rd ++ u.wr) (u.gpr .r11) 8)
    (h₃ : InRegions u.wr (u.gpr .rsp + BitVec.ofNat 64 (16 + 8 * m)) 8)
    (h₄ : InRegions (u.rd ++ u.wr) (u.gpr .r11 + 8#64) 8)
    (h₅ : InRegions u.wr (u.gpr .rsp + BitVec.ofNat 64 (24 + 8 * m)) 8) :
    execBlock isa (tagIn m) u = some (tagInState m u,
      [.addr (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * m)), .addr (u.gpr .r11),
        .addr (u.gpr .rsp + BitVec.ofNat 64 (16 + 8 * m)), .addr (u.gpr .r11 + 8#64),
        .addr (u.gpr .rsp + BitVec.ofNat 64 (24 + 8 * m))]) := by
  simp only [tagIn, atSp, execBlock, isa, exec, readSrc, State.load64, State.store64, State.ea,
    ofInt_natCast, addrs, srcAddrs]
  simp [h₁, h₂, h₃, h₄, h₅, State.setReg, tagInState]

/-- The memory after `tagIn m`, from memory `M` with `rsp = p` and `r11 = t`. -/
def tagInMem (m : Nat) (M : Mem) (p t : Addr) : Mem :=
  let M₁ := M.writeW (p + BitVec.ofNat 64 (8 + 8 * m)) t
  let M₂ := M₁.writeW (p + BitVec.ofNat 64 (16 + 8 * m)) (M₁.readW t 64)
  M₂.writeW (p + BitVec.ofNat 64 (24 + 8 * m)) (M₂.readW (t + 8#64) 64)

theorem tagInState_mem_eq (m : Nat) (u : State) :
    (tagInState m u).mem = tagInMem m u.mem (u.gpr .rsp) (u.gpr .r11) := rfl

/-- What `tagIn` leaves in memory, if the tag lies outside the 24 bytes it
writes (the saved pointer and the buffer's first 16 bytes): the pointer, and
the tag's bytes in the buffer. -/
theorem tagInMem_facts {m : Nat} {M : Mem} {p t : Addr} (hm : 32 + 8 * m ≤ 2 ^ 64)
    (hd : (⟨t, 16⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 (8 + 8 * m), 24⟩) :
    Frame [⟨p + BitVec.ofNat 64 (8 + 8 * m), 24⟩] M (tagInMem m M p t) ∧
      (tagInMem m M p t).readW (p + BitVec.ofNat 64 (8 + 8 * m)) 64 = t ∧
      ∀ i < 16, tagInMem m M p t (p + BitVec.ofNat 64 (16 + 8 * m) + BitVec.ofNat 64 i) =
        M (t + BitVec.ofNat 64 i) := by
  have hsub : ∀ {d : Nat}, 8 + 8 * m ≤ d → d + 8 ≤ 32 + 8 * m →
      Region.Sub ⟨p + BitVec.ofNat 64 d, 8⟩ ⟨p + BitVec.ofNat 64 (8 + 8 * m), 24⟩ :=
    fun h₁ h₂ => Offset.sub _ h₁ (by omega)
  have f₁ : Frame [⟨p + BitVec.ofNat 64 (8 + 8 * m), 8⟩] M
      (M.writeW (p + BitVec.ofNat 64 (8 + 8 * m)) t) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  generalize hM₁ : M.writeW (p + BitVec.ofNat 64 (8 + 8 * m)) t = M₁ at f₁
  have f₂ : Frame [⟨p + BitVec.ofNat 64 (16 + 8 * m), 8⟩] M₁
      (M₁.writeW (p + BitVec.ofNat 64 (16 + 8 * m)) (M₁.readW t 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hw₂ := fun i (hi : i < 8) => Mem.writeW_readW_apply M₁ M₁ (p + BitVec.ofNat 64 (16 + 8 * m)) t hi
  generalize hM₂ : M₁.writeW (p + BitVec.ofNat 64 (16 + 8 * m)) (M₁.readW t 64) = M₂ at f₂ hw₂
  have f₃ : Frame [⟨p + BitVec.ofNat 64 (24 + 8 * m), 8⟩] M₂
      (M₂.writeW (p + BitVec.ofNat 64 (24 + 8 * m)) (M₂.readW (t + 8#64) 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hw₃ := fun i (hi : i < 8) => Mem.writeW_readW_apply M₂ M₂ (p + BitVec.ofNat 64 (24 + 8 * m))
    (t + 8#64) hi
  have hmem : tagInMem m M p t =
      M₂.writeW (p + BitVec.ofNat 64 (24 + 8 * m)) (M₂.readW (t + 8#64) 64) := by
    simp only [tagInMem, hM₁, hM₂]
  rw [hmem]
  -- The tag's bytes are unchanged by the writes.
  have ht₁ : ∀ i < 16, M₁ (t + BitVec.ofNat 64 i) = M (t + BitVec.ofNat 64 i) := fun i hi =>
    f₁.bytes (R := ⟨t, 16⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hd.sub_right (hsub (Nat.le_refl _) (by omega))) (show 16 ≤ 2 ^ 64 by decide) hi
  have ht₂ : ∀ i < 16, M₂ (t + BitVec.ofNat 64 i) = M₁ (t + BitVec.ofNat 64 i) := fun i hi =>
    f₂.bytes (R := ⟨t, 16⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hd.sub_right (hsub (by omega) (by omega))) (show 16 ≤ 2 ^ 64 by decide) hi
  refine ⟨?_, ?_, fun i hi => ?_⟩
  · refine ((f₁.sub ?_).trans (f₂.sub ?_)).trans (f₃.sub ?_) <;>
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, hsub (by omega) (by omega)⟩
  · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide),
      ← hM₂, Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide),
      ← hM₁, Mem.readW_writeW_self64]
  · rcases Nat.lt_or_ge i 8 with h8 | h8
    · -- The first quadword, which `M₂` holds.
      rw [f₃.bytes (R := ⟨p + BitVec.ofNat 64 (16 + 8 * m), 8⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)) (show 8 ≤ 2 ^ 64 by decide) h8,
        hw₂ i h8, ht₁ i hi]
    · -- The second, which the last write holds.
      have ha : p + BitVec.ofNat 64 (16 + 8 * m) + BitVec.ofNat 64 i =
          p + BitVec.ofNat 64 (24 + 8 * m) + BitVec.ofNat 64 (i - 8) := by
        rw [Offset.add_add, Offset.add_add]; congr 2; omega
      have hb : t + 8#64 + BitVec.ofNat 64 (i - 8) = t + BitVec.ofNat 64 i := by
        rw [show (8#64 : Addr) = BitVec.ofNat 64 8 from rfl, Offset.add_add]; congr 2; omega
      rw [ha, hw₃ (i - 8) (by omega), hb, ht₂ i hi, ht₁ i hi]

theorem signExtend_ofNat32 {d : Nat} (h : d < 2 ^ 31) :
    (BitVec.ofNat 32 d).signExtend 64 = BitVec.ofNat 64 d := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend]
  have : (BitVec.ofNat 32 d).msb = false := by
    rw [BitVec.msb_eq_decide]; simp; omega
  simp [this]
  omega

theorem loadTagPtr_reg_run (bytes : Nat) (r : Reg) (u : State) :
    execBlock isa (loadTagPtr bytes (.reg r)) u = some (u.setReg .r11 (u.gpr r), []) := rfl

theorem loadTagPtr_stack_run {bytes j : Nat} {u : State}
    (h : InRegions (u.rd ++ u.wr) (u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * j)) 8) :
    execBlock isa (loadTagPtr bytes (.stack j)) u =
      some (u.setReg .r11 (u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * j)) 64),
        [.addr (u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * j))]) := by
  simp only [loadTagPtr, atSp, execBlock, isa, exec, readSrc, State.load64, State.ea,
    ofInt_natCast, addrs, srcAddrs]
  simp [h]

/-- `pointTag m (.reg r)` puts the buffer's address in `r`, changing only
`rax`, `r` and the flags. -/
theorem pointTag_reg_run {m : Nat} {r : Reg} {u : State} (hm : 16 + 8 * m < 2 ^ 31) :
    ∃ u', execBlock isa (pointTag m (.reg r)) u = some (u', []) ∧
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.mxcsr = u.mxcsr ∧ u'.mem = u.mem ∧
      (∀ q, q ≠ .rax → q ≠ r → u'.gpr q = u.gpr q) ∧
      u'.gpr r = u.gpr .rsp + BitVec.ofNat 64 (16 + 8 * m) := by
  simp only [pointTag, execBlock, isa, exec, readSrc, execAlu, Option.map_some, Option.bind_some,
    addrs, srcAddrs]
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, fun q h₁ h₂ => ?_, ?_⟩
  · simp [State.setReg, arithFlags, State.setFlags, h₁, h₂]
  · simp [State.setReg, arithFlags, State.setFlags, signExtend_ofNat32 hm]

/-- `pointTag m (.stack j)` stores the buffer's address at `rsp + 8 + 8j`,
changing only `rax` and the flags. -/
theorem pointTag_stack_run {m j : Nat} {u : State} (hm : 16 + 8 * m < 2 ^ 31)
    (hw : InRegions u.wr (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * j)) 8) :
    ∃ u', execBlock isa (pointTag m (.stack j)) u =
        some (u', [.addr (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * j))]) ∧
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.mxcsr = u.mxcsr ∧
      u'.mem = u.mem.writeW (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * j))
        (u.gpr .rsp + BitVec.ofNat 64 (16 + 8 * m)) ∧
      (∀ q, q ≠ .rax → u'.gpr q = u.gpr q) := by
  simp only [pointTag, atSp, execBlock, isa, exec, readSrc, execAlu, Option.map_some,
    Option.bind_some, addrs, srcAddrs, State.store64, State.ea, ofInt_natCast]
  simp [State.setReg, arithFlags, State.setFlags, hw, signExtend_ofNat32 hm]
  intro q hq; simp [hq]

/-- The memory after `tagOut m`, from memory `M` with `rsp = p`: the 16
bytes at `p + 16 + 8m` copied to the tag whose pointer is at `p + 8 + 8m`. -/
def tagOutMem (m : Nat) (M : Mem) (p : Addr) : Mem :=
  let t := M.readW (p + BitVec.ofNat 64 (8 + 8 * m)) 64
  let M₁ := M.writeW t (M.readW (p + BitVec.ofNat 64 (16 + 8 * m)) 64)
  M₁.writeW (t + 8#64) (M₁.readW (p + BitVec.ofNat 64 (24 + 8 * m)) 64)

theorem tagOut_run {m : Nat} {u : State}
    (h₁ : InRegions (u.rd ++ u.wr) (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * m)) 8)
    (h₂ : InRegions (u.rd ++ u.wr) (u.gpr .rsp + BitVec.ofNat 64 (16 + 8 * m)) 8)
    (h₃ : InRegions u.wr (u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * m)) 64) 8)
    (h₄ : InRegions (u.rd ++ u.wr) (u.gpr .rsp + BitVec.ofNat 64 (24 + 8 * m)) 8)
    (h₅ : InRegions u.wr (u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * m)) 64 + 8#64) 8) :
    ∃ u', execBlock isa (tagOut m) u = some (u',
        [.addr (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * m)),
          .addr (u.gpr .rsp + BitVec.ofNat 64 (16 + 8 * m)),
          .addr (u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * m)) 64),
          .addr (u.gpr .rsp + BitVec.ofNat 64 (24 + 8 * m)),
          .addr (u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * m)) 64 + 8#64)]) ∧
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.mxcsr = u.mxcsr ∧
      u'.mem = tagOutMem m u.mem (u.gpr .rsp) ∧
      (∀ q, q ≠ .r10 → q ≠ .r11 → u'.gpr q = u.gpr q) := by
  simp only [tagOut, atSp, execBlock, isa, exec, readSrc, State.load64, State.store64, State.ea,
    ofInt_natCast, addrs, srcAddrs]
  simp [h₁, h₂, h₃, h₄, h₅, State.setReg, tagOutMem]
  intro q h₁ h₂; simp [h₁, h₂]

/-- What `tagOut` leaves in memory, if the tag lies outside the 24 bytes it
reads: the buffer's first 16 bytes in the tag, and nothing else written. -/
theorem tagOutMem_facts {m : Nat} {M : Mem} {p : Addr}
    (hd : (⟨M.readW (p + BitVec.ofNat 64 (8 + 8 * m)) 64, 16⟩ : Region).Disjoint
      ⟨p + BitVec.ofNat 64 (8 + 8 * m), 24⟩) :
    Frame [⟨M.readW (p + BitVec.ofNat 64 (8 + 8 * m)) 64, 16⟩] M (tagOutMem m M p) ∧
      ∀ i < 16, tagOutMem m M p (M.readW (p + BitVec.ofNat 64 (8 + 8 * m)) 64 + BitVec.ofNat 64 i) =
        M (p + BitVec.ofNat 64 (16 + 8 * m) + BitVec.ofNat 64 i) := by
  generalize ht : M.readW (p + BitVec.ofNat 64 (8 + 8 * m)) 64 = t at hd
  have hmem : tagOutMem m M p =
      (M.writeW t (M.readW (p + BitVec.ofNat 64 (16 + 8 * m)) 64)).writeW (t + 8#64)
        ((M.writeW t (M.readW (p + BitVec.ofNat 64 (16 + 8 * m)) 64)).readW
          (p + BitVec.ofNat 64 (24 + 8 * m)) 64) := by
    simp only [tagOutMem, ht]
  rw [hmem]
  have hsub : ∀ {d : Nat}, 8 + 8 * m ≤ d → d + 8 ≤ 32 + 8 * m →
      Region.Sub ⟨p + BitVec.ofNat 64 d, 8⟩ ⟨p + BitVec.ofNat 64 (8 + 8 * m), 24⟩ :=
    fun h₁ h₂ => Offset.sub _ h₁ (by omega)
  generalize hv : M.readW (p + BitVec.ofNat 64 (16 + 8 * m)) 64 = v
  have hw₁ := fun i (hi : i < 8) => Mem.writeW_readW_apply M M t (p + BitVec.ofNat 64 (16 + 8 * m)) hi
  rw [hv] at hw₁
  have f₁ : Frame [⟨t, 16⟩] M (M.writeW t v) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by simp [Region.Contains])
  generalize hM₁ : M.writeW t v = M₁ at f₁ hw₁
  have hw₂ := fun i (hi : i < 8) =>
    Mem.writeW_readW_apply M₁ M₁ (t + 8#64) (p + BitVec.ofNat 64 (24 + 8 * m)) hi
  have f₂ : Frame [⟨t, 16⟩] M₁ (M₁.writeW (t + 8#64) (M₁.readW (p + BitVec.ofNat 64 (24 + 8 * m)) 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base t (d := 8) (n := 8) (k := 16) (by omega) (by omega))
  have f₂' : Frame [⟨t + 8#64, 8⟩] M₁
      (M₁.writeW (t + 8#64) (M₁.readW (p + BitVec.ofNat 64 (24 + 8 * m)) 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  generalize M₁.writeW (t + 8#64) (M₁.readW (p + BitVec.ofNat 64 (24 + 8 * m)) 64) = M₂ at f₂ f₂' hw₂
  refine ⟨f₁.trans f₂, fun i hi => ?_⟩
  rcases Nat.lt_or_ge i 8 with h8 | h8
  · rw [f₂'.bytes (R := ⟨t, 8⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint t (e := 8) (n := 8) (k := 8) (Nat.le_refl _) (by omega))
        (show 8 ≤ 2 ^ 64 by decide) h8, hw₁ i h8]
  · have ha : t + BitVec.ofNat 64 i = t + 8#64 + BitVec.ofNat 64 (i - 8) := by
      rw [show (8#64 : Addr) = BitVec.ofNat 64 8 from rfl, Offset.add_add]; congr 2; omega
    have hb : p + BitVec.ofNat 64 (24 + 8 * m) + BitVec.ofNat 64 (i - 8) =
        p + BitVec.ofNat 64 (16 + 8 * m) + BitVec.ofNat 64 i := by
      rw [Offset.add_add, Offset.add_add]; congr 2; omega
    rw [ha, hw₂ (i - 8) (by omega), ← hM₁]
    rw [show M.writeW t v (p + BitVec.ofNat 64 (24 + 8 * m) + BitVec.ofNat 64 (i - 8)) =
        M (p + BitVec.ofNat 64 (24 + 8 * m) + BitVec.ofNat 64 (i - 8)) from
      ((Frame.refl _ _).writeW (rs := [⟨t, 16⟩]) (List.mem_singleton_self _) v
        (by simp [Region.Contains])).bytes (R := ⟨p + BitVec.ofNat 64 (24 + 8 * m), 8⟩)
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hd.sub_right (hsub (by omega) (by omega))).symm) (show 8 ≤ 2 ^ 64 by decide)
        (show i - 8 < 8 by omega), hb]

/-! ## The setup -/

/-- The tag pointer where `a` says, from the state after the frame's push of
`bytes`: in its register, or in the caller's stack argument. -/
def tagPtr (bytes : Nat) (a : TagArg) (u : State) : Addr :=
  match a with
  | .reg r => u.gpr r
  | .stack j => u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * j)) 64

/-- The addresses `loadTagPtr bytes a` accesses, from `rsp = sp`. -/
def loadTrace (bytes : Nat) (a : TagArg) (sp : Addr) : List Leak :=
  match a with
  | .reg _ => []
  | .stack j => [.addr (sp + BitVec.ofNat 64 (bytes + 8 + 8 * j))]

/-- The addresses `pointTag m a` accesses, from `rsp = sp`. -/
def pointTrace (a : TagArg) (sp : Addr) : List Leak :=
  match a with
  | .reg _ => []
  | .stack j => [.addr (sp + BitVec.ofNat 64 (8 + 8 * j))]

/-- The addresses `tagSetup bytes m a` accesses, from `rsp = sp`, for the tag
at `t`. -/
def tagSetupTrace (bytes m : Nat) (a : TagArg) (sp t : Addr) : List Leak :=
  copyTrace bytes sp m ++ loadTrace bytes a sp ++
    [.addr (sp + BitVec.ofNat 64 (8 + 8 * m)), .addr t, .addr (sp + BitVec.ofNat 64 (16 + 8 * m)),
      .addr (t + 8#64), .addr (sp + BitVec.ofNat 64 (24 + 8 * m))] ++ pointTrace a sp

/-- The state after `tagSetup bytes m a` from `u`, if it runs. -/
def tagSetupState (bytes m : Nat) (a : TagArg) (u : State) : State :=
  ((execBlock isa (tagSetup bytes m a) u).map Prod.fst).getD u

/-- Where the tag pointer may be: a register `tagSetup` does not use, or one
of the `m` stack arguments. -/
def tagArgOk (m : Nat) : TagArg → Prop
  | .reg r => r ≠ .rax ∧ r ≠ .rsp ∧ r ≠ .r10 ∧ r ≠ .r11
  | .stack j => j < m

theorem setReg_gpr_ne {u : State} {r q : Reg} {v : BitVec 64} (h : q ≠ r) :
    (u.setReg r v).gpr q = u.gpr q := by
  simp [State.setReg, h]

/-- `pointTag`, for either place. -/
theorem pointTag_run {m : Nat} {a : TagArg} {w : State} (hm : 16 + 8 * m < 2 ^ 31) (ha : tagArgOk m a)
    (hF : ∀ j < m, InRegions w.wr (w.gpr .rsp + BitVec.ofNat 64 (8 + 8 * j)) 8) :
    ∃ w', execBlock isa (pointTag m a) w = some (w', pointTrace a (w.gpr .rsp)) ∧
      w'.rd = w.rd ∧ w'.wr = w.wr ∧ w'.mxcsr = w.mxcsr ∧
      (∀ r, r ≠ .rax → w'.gpr r =
        if a = .reg r then w.gpr .rsp + BitVec.ofNat 64 (16 + 8 * m) else w.gpr r) ∧
      Frame [⟨w.gpr .rsp + 8, 8 * m⟩] w.mem w'.mem ∧
      (∀ j < m, w'.mem.readW (w.gpr .rsp + BitVec.ofNat 64 (8 + 8 * j)) 64 =
        if a = .stack j then w.gpr .rsp + BitVec.ofNat 64 (16 + 8 * m)
        else w.mem.readW (w.gpr .rsp + BitVec.ofNat 64 (8 + 8 * j)) 64) := by
  have h8 : w.gpr .rsp + 8 = w.gpr .rsp + BitVec.ofNat 64 8 := rfl
  cases a with
  | reg r =>
    obtain ⟨w', hrun, hrd, hwr, hmx, hmem, hg, hr⟩ := pointTag_reg_run (r := r) (u := w) hm
    refine ⟨w', hrun, hrd, hwr, hmx, fun q hq => ?_, by rw [hmem]; exact Frame.refl _ _,
      fun j _ => by simp [hmem]⟩
    by_cases hqr : q = r
    · subst hqr; simp [hr]
    · rw [hg q hq hqr]
      split
      · next h => exact absurd (TagArg.reg.inj h).symm hqr
      · rfl
  | stack j₀ =>
    have hj₀ : j₀ < m := ha
    obtain ⟨w', hrun, hrd, hwr, hmx, hmem, hg⟩ := pointTag_stack_run (j := j₀) (u := w) hm
      (hF j₀ hj₀)
    refine ⟨w', hrun, hrd, hwr, hmx, fun q hq => by rw [hg q hq]; simp, ?_, fun j hj => ?_⟩
    · rw [hmem]
      refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_
      rw [h8]
      exact Offset.contains _ (by omega) (by omega) (by omega)
    · rw [hmem]
      by_cases hjj : j = j₀
      · subst hjj; rw [Mem.readW_writeW_self64]; simp
      · rw [Mem.readW_writeW_sep]
        · split
          · next h => exact absurd (TagArg.stack.inj h).symm hjj
          · rfl
        · exact Offset.sep _ (by omega) (by omega) (by omega)
        · decide

/-- `tagSetup`, from the state after the frame's push (`u`, whose `rsp` is
the frame's base): the stack arguments copied into the frame, the tag pointer
saved after them and the tag copied to the buffer after that, and the
buffer's address in the tag pointer's place; nothing else written, and only
`rax`, `r10`, `r11` and the tag pointer's register changed. -/
theorem tagSetup_run {bytes m : Nat} {a : TagArg} {u : State}
    (hfit : bytes + 16 + 8 * m ≤ 2 ^ 64) (hb : 32 + 8 * m ≤ bytes) (hm : 16 + 8 * m < 2 ^ 31)
    (hF : (⟨u.gpr .rsp, bytes⟩ : Region) ∈ u.wr)
    (hr : ∀ j < m, InRegions (u.rd ++ u.wr) (u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * j)) 8)
    (ha : tagArgOk m a)
    (htw : (⟨tagPtr bytes a u, 16⟩ : Region) ∈ u.wr)
    (htd : (⟨tagPtr bytes a u, 16⟩ : Region).Disjoint ⟨u.gpr .rsp, bytes⟩) :
    execBlock isa (tagSetup bytes m a) u =
        some (tagSetupState bytes m a u, tagSetupTrace bytes m a (u.gpr .rsp) (tagPtr bytes a u)) ∧
      (tagSetupState bytes m a u).rd = u.rd ∧ (tagSetupState bytes m a u).wr = u.wr ∧
      (tagSetupState bytes m a u).mxcsr = u.mxcsr ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → (tagSetupState bytes m a u).gpr r =
        if a = .reg r then u.gpr .rsp + BitVec.ofNat 64 (16 + 8 * m) else u.gpr r) ∧
      Frame [⟨u.gpr .rsp + 8, 8 * m + 24⟩] u.mem (tagSetupState bytes m a u).mem ∧
      (∀ j < m, (tagSetupState bytes m a u).mem.readW (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * j)) 64 =
        if a = .stack j then u.gpr .rsp + BitVec.ofNat 64 (16 + 8 * m)
        else u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * j)) 64) ∧
      (tagSetupState bytes m a u).mem.readW (u.gpr .rsp + BitVec.ofNat 64 (8 + 8 * m)) 64 =
        tagPtr bytes a u ∧
      ∀ i < 16, (tagSetupState bytes m a u).mem
          (u.gpr .rsp + BitVec.ofNat 64 (16 + 8 * m) + BitVec.ofNat 64 i) =
        u.mem (tagPtr bytes a u + BitVec.ofNat 64 i) := by
  have hc8 : ∀ {d : Nat}, d + 8 ≤ bytes → InRegions u.wr (u.gpr .rsp + BitVec.ofNat 64 d) 8 :=
    fun h => ⟨_, hF, Offset.contains_base _ h (by omega)⟩
  have h8 : u.gpr .rsp + 8 = u.gpr .rsp + BitVec.ofNat 64 8 := rfl
  -- The copies.
  have hcp := copies_run (bytes := bytes) (u := u) m hr (fun j hj => hc8 (by omega))
  obtain ⟨f₁, hv₁⟩ := copiedState_mem (bytes := bytes) (u := u) m (by omega) (by omega)
  have e₁ := copiedState_rsp bytes u m
  have r₁ := copiedState_rd bytes u m
  have wr₁ := copiedState_wr bytes u m
  have mx₁ := copiedState_mxcsr bytes u m
  have g₁ : ∀ r, r ≠ .rax → (copiedState bytes u m).gpr r = u.gpr r :=
    fun r h => copiedState_gpr bytes u h m
  generalize copiedState bytes u m = w₁ at hcp f₁ hv₁ e₁ r₁ wr₁ mx₁ g₁
  -- The tag pointer.
  have hld : execBlock isa (loadTagPtr bytes a) w₁ =
      some (w₁.setReg .r11 (tagPtr bytes a u), loadTrace bytes a (u.gpr .rsp)) := by
    cases a with
    | reg r => rw [loadTagPtr_reg_run, g₁ r ha.1]; rfl
    | stack j =>
      have hj : j < m := ha
      rw [loadTagPtr_stack_run (by rw [r₁, wr₁, e₁]; exact hr j hj), e₁]
      simp only [tagPtr, loadTrace]
      rw [f₁.readW (r := ⟨u.gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * j), 8⟩)
        (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
      simp only [List.mem_singleton] at hr; subst hr
      rw [h8]
      exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  generalize tagPtr bytes a u = t at hld htw htd ⊢
  -- The tag lies outside the frame.
  have ht₁ : ∀ i < 16, w₁.mem (t + BitVec.ofNat 64 i) = u.mem (t + BitVec.ofNat 64 i) :=
    fun i hi => f₁.bytes (R := ⟨t, 16⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h8]; exact htd.sub_right (Offset.sub_base _ (by omega))) (show 16 ≤ 2 ^ 64 by decide) hi
  -- Saving the pointer and copying the tag.
  have s₂ : (w₁.setReg .r11 t).gpr .rsp = u.gpr .rsp := by rw [setReg_gpr_ne (by decide), e₁]
  have s₁₁ : (w₁.setReg .r11 t).gpr .r11 = t := by simp [State.setReg]
  have hti := tagIn_run (m := m) (u := w₁.setReg .r11 t)
    (by rw [s₂]; exact wr₁ ▸ hc8 (by omega))
    (by rw [s₁₁]; exact ⟨_, List.mem_append_right _ (wr₁ ▸ htw), by simp [Region.Contains]⟩)
    (by rw [s₂]; exact wr₁ ▸ hc8 (by omega))
    (by rw [s₁₁]; exact ⟨_, List.mem_append_right _ (wr₁ ▸ htw),
      Offset.contains_base t (d := 8) (n := 8) (k := 16) (by omega) (by omega)⟩)
    (by rw [s₂]; exact wr₁ ▸ hc8 (by omega))
  rw [s₂, s₁₁] at hti
  obtain ⟨f₃, hslot, hW⟩ := tagInMem_facts (m := m) (M := w₁.mem) (p := u.gpr .rsp) (t := t)
    (by omega) (htd.sub_right (Offset.sub_base _ (by omega)))
  have hm₃ : (tagInState m (w₁.setReg .r11 t)).mem = tagInMem m w₁.mem (u.gpr .rsp) t := by
    rw [tagInState_mem_eq, s₂, s₁₁]; rfl
  rw [← hm₃] at f₃ hslot hW
  have e₃ : (tagInState m (w₁.setReg .r11 t)).gpr .rsp = u.gpr .rsp := by
    simp only [tagInState]; rw [setReg_gpr_ne (by decide), setReg_gpr_ne (by decide), s₂]
  have g₃ : ∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 →
      (tagInState m (w₁.setReg .r11 t)).gpr r = u.gpr r := fun r h₁ h₂ h₃ => by
    simp only [tagInState]
    rw [setReg_gpr_ne h₂, setReg_gpr_ne h₂, setReg_gpr_ne h₃, g₁ r h₁]
  have r₃ : (tagInState m (w₁.setReg .r11 t)).rd = u.rd := r₁
  have wr₃ : (tagInState m (w₁.setReg .r11 t)).wr = u.wr := wr₁
  have mx₃ : (tagInState m (w₁.setReg .r11 t)).mxcsr = u.mxcsr := mx₁
  generalize tagInState m (w₁.setReg .r11 t) = w₃ at hti f₃ hslot hW e₃ g₃ r₃ wr₃ mx₃
  -- Passing the buffer.
  obtain ⟨w₄, hpt, r₄, wr₄, mx₄, g₄, f₄, hv₄⟩ := pointTag_run (a := a) (w := w₃) hm ha
    (fun j hj => by rw [wr₃, e₃]; exact hc8 (by omega))
  rw [e₃] at hpt g₄ f₄ hv₄
  have hrun : execBlock isa (tagSetup bytes m a) u = some (w₄, tagSetupTrace bytes m a (u.gpr .rsp) t) := by
    rw [tagSetup, execBlock_append, execBlock_append, execBlock_append, hcp]
    simp only [Option.bind_some, hld, Option.map_some, hti, hpt, tagSetupTrace, List.append_assoc]
  have hst : tagSetupState bytes m a u = w₄ := by simp [tagSetupState, hrun]
  rw [hst]
  -- The 24 bytes `tagIn` writes are outside the copies.
  have hout : ∀ {d : Nat}, 8 * m + 8 ≤ d → d + 8 ≤ 32 + 8 * m →
      ∀ r ∈ ([⟨u.gpr .rsp + 8, 8 * m⟩] : List Region),
        Region.Disjoint ⟨u.gpr .rsp + BitVec.ofNat 64 d, 8⟩ r := fun h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [h8]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  refine ⟨hrun, r₄.trans r₃, wr₄.trans wr₃, mx₄.trans mx₃, fun r h₁ h₂ h₃ => ?_, ?_,
    fun j hj => ?_, ?_, fun i hi => ?_⟩
  · rw [g₄ r h₁, g₃ r h₁ h₂ h₃]
  · have hsub : ∀ {d k : Nat}, 8 ≤ d → d + k ≤ 8 * m + 32 →
        ∀ r ∈ ([⟨u.gpr .rsp + BitVec.ofNat 64 d, k⟩] : List Region),
          ∃ r' ∈ ([⟨u.gpr .rsp + 8, 8 * m + 24⟩] : List Region), Region.Sub r r' :=
      fun h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, by rw [h8]; exact Offset.sub _ h₁ (by omega)⟩
    refine ((f₁.sub ?_).trans (f₃.sub (hsub (by omega) (by omega)))).trans (f₄.sub ?_)
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
  · rw [hv₄ j hj]
    split
    · rfl
    · rw [f₃.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide), hv₁ j hj]
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  · rw [f₄.readW (Region.contains_self _ _) (hout (by omega) (by omega)) (by decide), hslot]
  · rw [f₄.bytes (R := ⟨u.gpr .rsp + BitVec.ofNat 64 (16 + 8 * m), 16⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [h8]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega))
      (show 16 ≤ 2 ^ 64 by decide) hi, hW i hi, ht₁ i hi]

/-! ## The state the code runs from -/

/-- Where argument word `k` of a function is passed: in an argument
register, or on the stack. -/
def tagArgAt (k : Nat) : TagArg := if k < 6 then .reg (argRegs.getD k .rax) else .stack (k - 6)

/-- The word of `sig`'s parameter `q`. -/
abbrev tagWord (sig : Sig) (q : Nat) : Nat := (Sig.psWords (sig.params.take q) abi.ptrBits).length

/-- The buffer's address, from the state `s` on entry. -/
abbrev tagBuf (sig : Sig) (bytes : Nat) (s : State) : Addr :=
  s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (16 + 8 * nStack sig)

/-- The copy of the stack arguments, read-only, if there are any. -/
def copyArea (sig : Sig) (bytes : Nat) (s : State) : List (Region × Bool) :=
  if nStack sig = 0 then [] else [(⟨s.gpr .rsp - BitVec.ofNat 64 bytes + 8, 8 * nStack sig⟩, false)]

/-- The regions of the code's contract, from the state `s` on entry: the
buffers, with the working space in the tag's place, and the copy of the
stack arguments. -/
def innerRegions (sig : Sig) (q : Nat) (nm : String) (e : Elem) (n bytes : Nat) (s : State) :
    List (Region × Bool) :=
  Sig.bufs (sig.tagWork q nm e n).params ((allArgs sig s).set (tagWord sig q) (tagBuf sig bytes s)) ++
    copyArea sig bytes s

/-- The state the code runs from, with the permissions of its contract: the
state after the frame's push and `tagSetup`. -/
def narrowT (sig : Sig) (q : Nat) (nm : String) (e : Elem) (n bytes : Nat) (s : State) : State :=
  (tagSetupState bytes (nStack sig) (tagArgAt (tagWord sig q)) (allocState bytes s)).withRegions
    (((innerRegions sig q nm e n bytes s).filter (!·.2)).map (·.1))
    (((innerRegions sig q nm e n bytes s).filter (·.2)).map (·.1))

theorem narrowT_gpr (sig : Sig) (q : Nat) (nm : String) (e : Elem) (n bytes : Nat) (s : State) :
    (narrowT sig q nm e n bytes s).gpr =
      (tagSetupState bytes (nStack sig) (tagArgAt (tagWord sig q)) (allocState bytes s)).gpr := rfl
theorem narrowT_mem (sig : Sig) (q : Nat) (nm : String) (e : Elem) (n bytes : Nat) (s : State) :
    (narrowT sig q nm e n bytes s).mem =
      (tagSetupState bytes (nStack sig) (tagArgAt (tagWord sig q)) (allocState bytes s)).mem := rfl
theorem narrowT_mxcsr (sig : Sig) (q : Nat) (nm : String) (e : Elem) (n bytes : Nat) (s : State) :
    (narrowT sig q nm e n bytes s).mxcsr =
      (tagSetupState bytes (nStack sig) (tagArgAt (tagWord sig q)) (allocState bytes s)).mxcsr := rfl

theorem allArgs_getElem (sig : Sig) (s : State) {i : Nat} (h : i < (allArgs sig s).length) :
    (allArgs sig s)[i] = if i < 6 then s.gpr (argRegs.getD i .rax) else stackArg s (i - 6) := by
  have h6 : (argRegs.map s.gpr).length = 6 := rfl
  by_cases hi : i < 6
  · simp only [allArgs, List.getElem_append, h6, hi, dite_true, ite_true, List.getElem_map]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < argRegs.length from hi)]
  · simp only [allArgs, List.getElem_append, h6, hi, dite_false, ite_false, List.getElem_map,
      List.getElem_range]

theorem argRegs_ok : ∀ k < 6, argRegs.getD k .rax ≠ .rax ∧ argRegs.getD k .rax ≠ .rsp ∧
    argRegs.getD k .rax ≠ .r10 ∧ argRegs.getD k .rax ≠ .r11 ∧ argRegs.getD k .rax ∉ calleeSaved ∧
    ∀ i < 6, argRegs.getD k .rax = argRegs.getD i .rax → k = i := by
  decide

section
variable {sig : Sig} {q : Nat} {nmT nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {wa : Bool} {stack bytes : Nat}

theorem tagWord_lt (hq : sig.params[q]? = some (nmT, .array true .u8 16)) :
    tagWord sig q < (sig.words abi.ptrBits).length := by
  rw [Sig.words_split _ hq, List.length_append, List.length_cons]; simp only [tagWord]; omega

theorem allArgs_tagWork (hq : sig.params[q]? = some (nmT, .array true .u8 16)) (s : State) :
    allArgs (sig.tagWork q nm e n) s = allArgs sig s := by
  rw [allArgs, allArgs, Sig.words_tagWork _ _ _ _ hq]

theorem tagArgAt_ok {k : Nat} (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hlt : k < (sig.words abi.ptrBits).length) : tagArgOk (nStack sig) (tagArgAt k) := by
  unfold tagArgAt
  split
  · next h => obtain ⟨h₁, h₂, h₃, h₄, -⟩ := argRegs_ok k h; exact ⟨h₁, h₂, h₃, h₄⟩
  · show k - 6 < nStack sig; simp only [nStack]; omega

/-- The tag pointer `tagSetup` reads is argument word `k`. -/
theorem tagPtr_alloc {k : Nat} (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hlt : k < (sig.words abi.ptrBits).length) (s : State) :
    tagPtr bytes (tagArgAt k) (allocState bytes s) = (allArgs sig s).getD k 0 := by
  have hl := allArgs_length sig s hk
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
    allArgs_getElem]
  unfold tagArgAt
  split
  · next h =>
    show (allocState bytes s).gpr _ = _
    rw [allocState_gpr' _ _ (argRegs_ok k h).2.1]
  · next h =>
    show (allocState bytes s).mem.readW _ 64 = s.mem.readW (stackArgAddr s (k - 6)) 64
    rw [allocState_rsp', stackArgAddr,
      show bytes + 8 + 8 * (k - 6) = bytes + 8 * (k - 6 + 1) by omega, BitVec.ofNat_add,
      ← BitVec.add_assoc, BitVec.sub_add_cancel]
    rfl

/-- `tagArgAt k` is no callee-saved register, nor `rsp`. -/
theorem tagArgAt_ne {k : Nat} {r : Reg} (hr : r = .rsp ∨ r ∈ calleeSaved) : tagArgAt k ≠ .reg r := by
  unfold tagArgAt
  split
  · next h =>
    obtain ⟨-, h₂, -, -, h₅, -⟩ := argRegs_ok k h
    intro e
    have e' := TagArg.reg.inj e
    rcases hr with rfl | hr
    · exact h₂ e'
    · exact h₅ (e' ▸ hr)
  · exact fun e => TagArg.noConfusion e

/-- `tagArgAt k` is register argument `i` exactly if `i` is `k`. -/
theorem tagArgAt_reg {k i : Nat} (hi : i < 6) : tagArgAt k = .reg (argRegs.getD i .rax) ↔ k = i := by
  unfold tagArgAt
  split
  · next h =>
    constructor
    · intro e; exact (argRegs_ok k h).2.2.2.2.2 i hi (TagArg.reg.inj e)
    · rintro rfl; rfl
  · next h => exact ⟨fun e => TagArg.noConfusion e, fun e => absurd (by omega : k < 6) h⟩

/-- `tagArgAt k` is stack argument `i - 6` exactly if `i` is `k`, for `6 ≤ i`. -/
theorem tagArgAt_stack {k i : Nat} (hi : 6 ≤ i) : tagArgAt k = .stack (i - 6) ↔ k = i := by
  unfold tagArgAt
  split
  · next h => exact ⟨fun e => TagArg.noConfusion e, fun e => by omega⟩
  · next h =>
    constructor
    · intro e; have := TagArg.stack.inj e; omega
    · rintro rfl; rfl

/-- What `tagSetup` gives, from a state satisfying the function's
precondition: the run, from the frame's push; and the state the code runs
from, which keeps what the function must keep, passes the arguments with
the buffer in the tag's place, and holds the tag pointer after the copied
stack arguments and the tag in the buffer, having written only there. -/
theorem narrowT_facts (hq : sig.params[q]? = some (nmT, .array true .u8 16))
    (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 32 + 8 * nStack sig ≤ bytes) (hb1 : bytes < 4096)
    {s : State} (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s)
    (hl : Sig.noLists sig.params = true) :
    execBlock isa (tagSetup bytes (nStack sig) (tagArgAt (tagWord sig q))) (allocState bytes s) =
        some (tagSetupState bytes (nStack sig) (tagArgAt (tagWord sig q)) (allocState bytes s),
          tagSetupTrace bytes (nStack sig) (tagArgAt (tagWord sig q))
            (s.gpr .rsp - BitVec.ofNat 64 bytes) ((allArgs sig s).getD (tagWord sig q) 0)) ∧
      (tagSetupState bytes (nStack sig) (tagArgAt (tagWord sig q)) (allocState bytes s)).rd =
        (allocState bytes s).rd ∧
      (tagSetupState bytes (nStack sig) (tagArgAt (tagWord sig q)) (allocState bytes s)).wr =
        (allocState bytes s).wr ∧
      (narrowT sig q nm e n bytes s).mxcsr = s.mxcsr ∧
      (narrowT sig q nm e n bytes s).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes ∧
      (∀ r ∈ calleeSaved, r ≠ .rsp → (narrowT sig q nm e n bytes s).gpr r = s.gpr r) ∧
      allArgs (sig.tagWork q nm e n) (narrowT sig q nm e n bytes s) =
        (allArgs sig s).set (tagWord sig q) (tagBuf sig bytes s) ∧
      Frame [⟨s.gpr .rsp - BitVec.ofNat 64 bytes + 8, 8 * nStack sig + 24⟩] s.mem
        (narrowT sig q nm e n bytes s).mem ∧
      (narrowT sig q nm e n bytes s).mem.readW
          (s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (8 + 8 * nStack sig)) 64 =
        (allArgs sig s).getD (tagWord sig q) 0 ∧
      ∀ i < 16, (narrowT sig q nm e n bytes s).mem (tagBuf sig bytes s + BitVec.ofNat 64 i) =
        s.mem ((allArgs sig s).getD (tagWord sig q) 0 + BitVec.ofNat 64 i) := by
  have hlt := tagWord_lt hq
  have hlen := allArgs_length sig s hk
  have hsplit := List.split_at (vs := allArgs sig s) (k := tagWord sig q) (by omega)
  have hl₁ : ((allArgs sig s).take (tagWord sig q)).length =
      (Sig.psWords (sig.params.take q) abi.ptrBits).length := by
    rw [List.length_take_of_le (by omega)]
  have hbufs := Sig.bufs_split abi.ptrBits hq _ ((allArgs sig s).drop (tagWord sig q + 1))
    ((allArgs sig s).getD (tagWord sig q) 0) hl₁
  rw [← hsplit] at hbufs
  have hptr := tagPtr_alloc (bytes := bytes) hk hlt s
  generalize (allArgs sig s).getD (tagWord sig q) 0 = t at hbufs hptr ⊢
  rw [pre_args hk hl] at hs
  obtain ⟨⟨hst, -⟩, hrd, hwr, -, hres, -, -⟩ := hs
  have hsb : stack + bytes ≤ (s.gpr .rsp).toNat := by rcases hst with h | h <;> omega
  have hbelow : below (s.gpr .rsp) (stack + bytes) ∈
      (⟨s.gpr .rsp, 8⟩ :: stackBelow (s.gpr .rsp) (stack + bytes) : List Region) := by
    rw [stackBelow_pos _ (by omega)]; simp
  have htb : ((⟨t, 16⟩ : Region), true) ∈ Sig.bufs sig.params (allArgs sig s) := by
    rw [hbufs]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have htw : (⟨t, 16⟩ : Region) ∈ s.wr := by
    rw [hwr]
    exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨List.mem_append_left _ htb, rfl⟩, rfl⟩
  have htd : (⟨t, 16⟩ : Region).Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :=
    (Region.Disjoint.symm (hres _ hbelow _ (List.mem_append_left _ htb))).sub_right
      (Offset.sub_below _ (by omega) (by omega))
  -- The caller's stack arguments hold the sources.
  have hesp : (allocState bytes s).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes := allocState_rsp' _ _
  have hsrc : ∀ j, (allocState bytes s).gpr .rsp + BitVec.ofNat 64 (bytes + 8 + 8 * j) =
      stackArgAddr s j := fun j => by
    rw [hesp, stackArgAddr, show bytes + 8 + 8 * j = bytes + 8 * (j + 1) by omega, BitVec.ofNat_add,
      ← BitVec.add_assoc, BitVec.sub_add_cancel]
  have hargs : ∀ j < nStack sig,
      InRegions ((allocState bytes s).rd ++ (allocState bytes s).wr) (stackArgAddr s j) 8 := fun j hj => by
    have h0 : ¬ (sig.words abi.ptrBits).length - 6 = 0 := by simp only [nStack] at hj; omega
    have hmem : (⟨stackArgAddr s 0, 8 * nStack sig⟩, false) ∈ allRegions sig s := by
      simp [allRegions, argArea, h0]
    have hc : (⟨stackArgAddr s 0, 8 * nStack sig⟩ : Region).Contains (stackArgAddr s j) 8 := by
      simp only [stackArgAddr]
      exact Offset.contains _ (d := 8 * (j + 1)) (n := 8) (e := 8 * (0 + 1)) (k := 8 * nStack sig)
        (by omega) (by omega) (by omega)
    refine ⟨_, List.mem_append_left _ ?_, hc⟩
    show _ ∈ s.rd
    rw [hrd]
    exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hmem, rfl⟩, rfl⟩
  obtain ⟨hrun, hrd', hwr', hmx, hg, hf, hv, hslot, hW⟩ := tagSetup_run (bytes := bytes)
    (m := nStack sig) (a := tagArgAt (tagWord sig q)) (u := allocState bytes s) (by omega) hb (by omega)
    (by rw [hesp]; exact List.mem_cons_self ..) (fun j hj => by rw [hsrc]; exact hargs j hj)
    (tagArgAt_ok hk hlt) (by rw [hptr]; exact List.mem_cons_of_mem _ htw)
    (by rw [hptr, hesp]; exact htd)
  rw [hptr] at hrun hslot hW
  have hcs : ∀ r ∈ calleeSaved, r ≠ .rax ∧ r ≠ .r10 ∧ r ≠ .r11 := by decide
  have hrspT : (tagSetupState bytes (nStack sig) (tagArgAt (tagWord sig q)) (allocState bytes s)).gpr .rsp =
      (allocState bytes s).gpr .rsp := by
    rw [hg .rsp (by decide) (by decide) (by decide)]
    simp only [tagArgAt_ne (.inl rfl), ↓reduceIte]
  rw [hesp] at hrun hf hslot hW
  refine ⟨hrun, hrd', hwr', by rw [narrowT_mxcsr, hmx]; rfl, by rw [narrowT_gpr, hrspT, hesp],
    fun r hr hr' => ?_, ?_, by rw [narrowT_mem]; exact hf, by rw [narrowT_mem]; exact hslot,
    fun i hi => by rw [narrowT_mem]; exact hW i hi⟩
  · obtain ⟨o₁, o₂, o₃⟩ := hcs r hr
    rw [narrowT_gpr, hg r o₁ o₂ o₃]
    simp only [tagArgAt_ne (.inr hr), ↓reduceIte]
    exact allocState_gpr' _ _ hr'
  · rw [allArgs_tagWork hq]
    have hlenT := allArgs_length sig (narrowT sig q nm e n bytes s) hk
    apply List.ext_getElem (by rw [hlenT, List.length_set, hlen])
    intro i h₁ h₂
    rw [allArgs_getElem, List.getElem_set, allArgs_getElem]
    by_cases hi : i < 6
    · obtain ⟨o₁, o₂, o₃, o₄, -, -⟩ := argRegs_ok i hi
      simp only [hi, ↓reduceIte]
      rw [narrowT_gpr, hg _ o₁ o₃ o₄, allocState_gpr' _ _ o₂, hesp]
      simp only [tagArgAt_reg hi]
    · have hj : i - 6 < nStack sig := by simp only [nStack]; omega
      simp only [hi, ↓reduceIte]
      rw [show stackArg (narrowT sig q nm e n bytes s) (i - 6) =
          (tagSetupState bytes (nStack sig) (tagArgAt (tagWord sig q)) (allocState bytes s)).mem.readW
            ((allocState bytes s).gpr .rsp + BitVec.ofNat 64 (8 + 8 * (i - 6))) 64 by
        rw [stackArg, stackArgAddr, narrowT_mem, narrowT_gpr, hrspT,
          show 8 * (i - 6 + 1) = 8 + 8 * (i - 6) by omega]]
      rw [hv (i - 6) hj, hsrc]
      simp only [tagArgAt_stack (by omega : 6 ≤ i)]
      rw [hesp]
      rfl

/-- The arguments and the buffers of the function and of the code: those of
the function around the tag (at `t`), and the code's with the buffer (at
`W`) in its place. -/
theorem tag_bufs (hq : sig.params[q]? = some (nmT, .array true .u8 16))
    (hk : 6 ≤ (sig.words abi.ptrBits).length) (s : State) (W : Addr) :
    ((allArgs sig s).take (tagWord sig q)).length =
        (Sig.psWords (sig.params.take q) abi.ptrBits).length ∧
      ((allArgs sig s).drop (tagWord sig q + 1)).length =
        (Sig.psWords (sig.params.drop (q + 1)) abi.ptrBits).length ∧
      allArgs sig s = (allArgs sig s).take (tagWord sig q) ++
        (allArgs sig s).getD (tagWord sig q) 0 :: (allArgs sig s).drop (tagWord sig q + 1) ∧
      (allArgs sig s).set (tagWord sig q) W =
        (allArgs sig s).take (tagWord sig q) ++ W :: (allArgs sig s).drop (tagWord sig q + 1) ∧
      Sig.bufs sig.params (allArgs sig s) =
        Sig.bufs (sig.params.take q) ((allArgs sig s).take (tagWord sig q)) ++
          (⟨(allArgs sig s).getD (tagWord sig q) 0, 16⟩, true) ::
            Sig.bufs (sig.params.drop (q + 1)) ((allArgs sig s).drop (tagWord sig q + 1)) ∧
      Sig.bufs (sig.tagWork q nm e n).params ((allArgs sig s).set (tagWord sig q) W) =
        Sig.bufs (sig.params.take q) ((allArgs sig s).take (tagWord sig q)) ++
          (⟨W, n * e.size⟩, true) ::
            Sig.bufs (sig.params.drop (q + 1)) ((allArgs sig s).drop (tagWord sig q + 1)) := by
  have hlt := tagWord_lt hq
  have hlen := allArgs_length sig s hk
  have hw := Sig.words_split abi.ptrBits hq
  have hl₁ : ((allArgs sig s).take (tagWord sig q)).length =
      (Sig.psWords (sig.params.take q) abi.ptrBits).length := List.length_take_of_le (by omega)
  have hl₂ : ((allArgs sig s).drop (tagWord sig q + 1)).length =
      (Sig.psWords (sig.params.drop (q + 1)) abi.ptrBits).length := by
    rw [List.length_drop, hlen, hw, List.length_append, List.length_cons]; simp only [tagWord]; omega
  have hsplit := List.split_at (vs := allArgs sig s) (k := tagWord sig q) (by omega)
  have hset : (allArgs sig s).set (tagWord sig q) W =
      (allArgs sig s).take (tagWord sig q) ++ W :: (allArgs sig s).drop (tagWord sig q + 1) := by
    rw [List.set_eq_take_append_cons_drop]
    simp only [show tagWord sig q < (allArgs sig s).length by omega, ↓reduceIte]
  refine ⟨hl₁, hl₂, hsplit, hset, ?_, ?_⟩
  · conv => lhs; rw [hsplit]
    exact Sig.bufs_split abi.ptrBits hq _ _ _ hl₁
  · rw [hset]; exact Sig.bufs_tagWork nm e n abi.ptrBits hq _ _ _ hl₁

theorem allRegions_narrowT (hq : sig.params[q]? = some (nmT, .array true .u8 16))
    (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 32 + 8 * nStack sig ≤ bytes) (hb1 : bytes < 4096) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) (hl : Sig.noLists sig.params = true) :
    allRegions (sig.tagWork q nm e n) (narrowT sig q nm e n bytes s) = innerRegions sig q nm e n bytes s := by
  obtain ⟨-, -, -, -, hrsp, -, hargs, -⟩ := narrowT_facts (nm := nm) (e := e) (n := n) hq hk hb hb1 hs hl
  rw [allRegions, hargs, innerRegions]
  congr 1
  rw [argArea, copyArea, Sig.words_tagWork _ _ _ _ hq]
  simp only [nStack, stackArgAddr, hrsp]
  rfl

/-- The relation of `Sig.contract`'s disjointness is symmetric. -/
theorem disj_symm {x y : Region × Bool} (h : (x.2 || y.2) → x.1.Disjoint y.1) :
    (y.2 || x.2) → y.1.Disjoint x.1 :=
  fun hb => (h (by rw [Bool.or_comm]; exact hb)).symm

/-- The code's precondition holds in `narrowT`, from the function's. -/
theorem narrowT_pre (hq : sig.params[q]? = some (nmT, .array true .u8 16))
    (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 32 + 8 * nStack sig ≤ bytes ∧ 16 + 8 * nStack sig + n * e.size ≤ bytes) (hb1 : bytes < 4096)
    {preI : Curry ((sig.tagWork q nm e n).words abi.ptrBits) (Mem → Prop)}
    {postI : (sig.tagWork q nm e n).Post abi.ptrBits}
    {leakI : Option (Curry ((sig.tagWork q nm e n).words abi.ptrBits) (Mem → List Nat))}
    (ho : sig.TagFrame q nm e n abi.ptrBits pre post leak preI postI leakI)
    {s : State} (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s)
    (hl : Sig.noLists sig.params = true) :
    ((sig.tagWork q nm e n).contract abi preI postI wa stack leakI).pre (narrowT sig q nm e n bytes s) := by
  obtain ⟨-, -, -, -, hrsp, -, hargs, hf, -, hW⟩ :=
    narrowT_facts (nm := nm) (e := e) (n := n) hq hk hb.1 hb1 hs hl
  have hall := allRegions_narrowT (nm := nm) (e := e) (n := n) hq hk hb.1 hb1 hs hl
  have hkI : 6 ≤ ((sig.tagWork q nm e n).words abi.ptrBits).length := by
    rw [Sig.words_tagWork _ _ _ _ hq]; exact hk
  obtain ⟨hl₁, hl₂, hsplit, hset, hbO, hbI⟩ :=
    tag_bufs (nm := nm) (e := e) (n := n) hq hk s (tagBuf sig bytes s)
  rw [pre_args hk hl] at hs
  obtain ⟨⟨hst, -⟩, -, -, hpw, hres, hnw, hpr⟩ := hs
  have hsb : stack + bytes ≤ (s.gpr .rsp).toNat := by rcases hst with h | h <;> omega
  have hscr : tagBuf sig bytes s = s.gpr .rsp - BitVec.ofNat 64 (bytes - (16 + 8 * nStack sig)) :=
    sub_add_ofNat _ (by omega)
  have harea : s.gpr .rsp - BitVec.ofNat 64 bytes + 8 = s.gpr .rsp - BitVec.ofNat 64 (bytes - 8) :=
    sub_add_ofNat _ (d := 8) (by omega)
  have hbelow : below (s.gpr .rsp) (stack + bytes) ∈
      (⟨s.gpr .rsp, 8⟩ :: stackBelow (s.gpr .rsp) (stack + bytes) : List Region) := by
    rw [stackBelow_pos _ (by omega)]; simp
  -- The buffers lie outside the frame.
  have hout : ∀ a ∈ Sig.bufs sig.params (allArgs sig s), ∀ {x k : Nat}, x ≤ stack + bytes →
      stack + bytes - x + k ≤ stack + bytes →
      a.1.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 x, k⟩ := fun a ha _ _ hx hk =>
    (Region.Disjoint.symm (hres _ hbelow a (List.mem_append_left _ ha))).sub_right
      (Offset.sub_below _ hx hk)
  -- The other buffers are the function's.
  have hB : ∀ b ∈ Sig.bufs (sig.params.take q) ((allArgs sig s).take (tagWord sig q)) ++
      Sig.bufs (sig.params.drop (q + 1)) ((allArgs sig s).drop (tagWord sig q + 1)),
      b ∈ Sig.bufs sig.params (allArgs sig s) := fun b hb => by
    rw [hbO]
    rcases List.mem_append.mp hb with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  have hpwB : (Sig.bufs (sig.params.take q) ((allArgs sig s).take (tagWord sig q)) ++
      Sig.bufs (sig.params.drop (q + 1)) ((allArgs sig s).drop (tagWord sig q + 1))).Pairwise
        (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) := by
    rw [allRegions, hbO, List.pairwise_append, List.pairwise_middle disj_symm] at hpw
    exact (List.pairwise_cons.mp hpw.1).2
  have hWB : ∀ b ∈ Sig.bufs (sig.params.take q) ((allArgs sig s).take (tagWord sig q)) ++
      Sig.bufs (sig.params.drop (q + 1)) ((allArgs sig s).drop (tagWord sig q + 1)),
      (⟨tagBuf sig bytes s, n * e.size⟩ : Region).Disjoint b.1 := fun b hb => by
    rw [hscr]; exact (hout b (hB b hb) (by omega) (by omega)).symm
  have hCA : ∀ a ∈ copyArea sig bytes s, a = (⟨s.gpr .rsp - BitVec.ofNat 64 bytes + 8, 8 * nStack sig⟩, false) :=
    fun a ha => by
      unfold copyArea at ha; split at ha
      · simp at ha
      · simpa using ha
  refine (pre_args (sig := sig.tagWork q nm e n) (pre := preI) (post := postI) (leak := leakI) hkI
    (Sig.noLists_tagWork _ _ _ hq hl)).mpr ?_
  rw [hall, hrsp, hargs]
  refine ⟨⟨.inr ?_, .inr ?_⟩, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [toNat_sub_ofNat (by omega)]; omega
  · rw [Sig.words_tagWork _ _ _ _ hq, toNat_sub_ofNat (by omega)]; simp only [nStack] at hb; omega
  · -- Pairwise disjoint.
    rw [innerRegions, hbI, List.pairwise_append, List.pairwise_middle disj_symm]
    refine ⟨List.pairwise_cons.mpr ⟨fun b hb _ => hWB b hb, hpwB⟩, ?_, fun a ha b hb _ => ?_⟩
    · unfold copyArea; split <;> simp
    · obtain rfl := hCA b hb
      rcases List.mem_append.mp ha with ha | ha
      · rw [harea]; exact hout a (hB a (List.mem_append_left _ ha)) (by omega) (by omega)
      · rcases List.mem_cons.mp ha with rfl | ha
        · show Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (16 + 8 * nStack sig), _⟩
            ⟨s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 8, _⟩
          exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
        · rw [harea]; exact hout a (hB a (List.mem_append_right _ ha)) (by omega) (by omega)
  · -- The reserved stack: the frame's first quadword and the stack below it.
    intro r hr a ha
    have hr' : r = ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, 8⟩ ∨
        (0 < stack ∧ r = below (s.gpr .rsp - BitVec.ofNat 64 bytes) stack) := by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact .inl rfl
      · rcases Nat.eq_zero_or_pos stack with h0 | h0
        · subst h0; simp [stackBelow] at hr
        · rw [stackBelow_pos _ h0, List.mem_singleton] at hr; exact .inr ⟨h0, hr⟩
    have hbuf : ∀ a ∈ Sig.bufs sig.params (allArgs sig s), r.Disjoint a.1 := fun a ha => by
      rcases hr' with rfl | ⟨-, rfl⟩
      · exact Region.Disjoint.symm (hout a ha (by omega) (by omega))
      · exact (Region.Disjoint.symm (hout a ha (x := stack + bytes) (k := stack + bytes)
          (by omega) (by omega))).sub_left (below_below _ bytes stack)
    have hframe : ∀ {d k : Nat}, 8 ≤ d → d + k ≤ bytes →
        r.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 d, k⟩ := fun h₁ h₂ => by
      rcases hr' with rfl | ⟨h0, rfl⟩
      · exact Offset.base_disjoint _ h₁ (by omega)
      · exact Region.Disjoint.symm (Offset.disjoint_below _ (by omega))
    rw [innerRegions, hbI] at ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · exact hbuf a (hB a (List.mem_append_left _ ha))
      · rcases List.mem_cons.mp ha with rfl | ha
        · exact hframe (by omega) (by omega)
        · exact hbuf a (hB a (List.mem_append_right _ ha))
    · obtain rfl := hCA a ha
      exact hframe (d := 8) (by omega) (by omega)
  · -- No buffer wraps around.
    intro a ha
    rw [hbI] at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hnw a (hB a (List.mem_append_left _ ha))
    · rcases List.mem_cons.mp ha with rfl | ha
      · show (tagBuf sig bytes s).toNat + n * e.size ≤ 2 ^ 64
        rw [hscr, toNat_sub_ofNat (by omega)]
        have := (s.gpr .rsp).isLt
        omega
      · exact hnw a (hB a (List.mem_append_right _ ha))
  · -- The precondition.
    rw [hset]
    refine ho.pre _ _ _ _ _ _ hl₁ hl₂ ⟨fun b hb x hx => (hf x fun r hr hc => ?_).symm, hW⟩
      (by rw [← hsplit]; exact hpr)
    simp only [List.mem_singleton] at hr; subst hr
    rw [harea] at hc
    exact hout b (hB b hb) (x := bytes - 8) (k := 8 * nStack sig + 24) (by omega) (by omega) x hx hc

/-- The tag lies outside the other buffers, and the code's memory agrees
with the function's on them and holds the tag in the buffer (`TagIn`). -/
theorem narrowT_tagIn (hq : sig.params[q]? = some (nmT, .array true .u8 16))
    (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 32 + 8 * nStack sig ≤ bytes) (hb1 : bytes < 4096)
    {s : State} (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s)
    (hl : Sig.noLists sig.params = true) :
    TagIn (Sig.bufs (sig.params.take q) ((allArgs sig s).take (tagWord sig q)) ++
        Sig.bufs (sig.params.drop (q + 1)) ((allArgs sig s).drop (tagWord sig q + 1)))
      ((allArgs sig s).getD (tagWord sig q) 0) (tagBuf sig bytes s) s.mem
      (narrowT sig q nm e n bytes s).mem ∧
    ∀ b ∈ Sig.bufs (sig.params.take q) ((allArgs sig s).take (tagWord sig q)) ++
        Sig.bufs (sig.params.drop (q + 1)) ((allArgs sig s).drop (tagWord sig q + 1)),
      b.1.Disjoint ⟨(allArgs sig s).getD (tagWord sig q) 0, 16⟩ := by
  obtain ⟨-, -, -, -, -, -, -, hf, -, hW⟩ :=
    narrowT_facts (nm := nm) (e := e) (n := n) hq hk hb hb1 hs hl
  obtain ⟨-, -, -, -, hbO, -⟩ := tag_bufs (nm := nm) (e := e) (n := n) hq hk s (tagBuf sig bytes s)
  rw [pre_args hk hl] at hs
  obtain ⟨⟨hst, -⟩, -, -, hpw, hres, -, -⟩ := hs
  have hsb : stack + bytes ≤ (s.gpr .rsp).toNat := by rcases hst with h | h <;> omega
  have harea : s.gpr .rsp - BitVec.ofNat 64 bytes + 8 = s.gpr .rsp - BitVec.ofNat 64 (bytes - 8) :=
    sub_add_ofNat _ (d := 8) (by omega)
  have hbelow : below (s.gpr .rsp) (stack + bytes) ∈
      (⟨s.gpr .rsp, 8⟩ :: stackBelow (s.gpr .rsp) (stack + bytes) : List Region) := by
    rw [stackBelow_pos _ (by omega)]; simp
  have hB : ∀ b ∈ Sig.bufs (sig.params.take q) ((allArgs sig s).take (tagWord sig q)) ++
      Sig.bufs (sig.params.drop (q + 1)) ((allArgs sig s).drop (tagWord sig q + 1)),
      b ∈ Sig.bufs sig.params (allArgs sig s) := fun b hb => by
    rw [hbO]
    rcases List.mem_append.mp hb with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  refine ⟨⟨fun b hb x hx => (hf x fun r hr hc => ?_).symm, hW⟩, fun b hb => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    rw [harea] at hc
    exact (Region.Disjoint.symm (hres _ hbelow b (List.mem_append_left _ (hB b hb)))).sub_right
      (Offset.sub_below _ (a := bytes - 8) (n := 8 * nStack sig + 24) (by omega) (by omega)) x hx hc
  · rw [allRegions, hbO, List.pairwise_append, List.pairwise_middle disj_symm] at hpw
    exact (((List.pairwise_cons.mp hpw.1).1 b hb rfl)).symm

/-- What a contract's `leak` says of the values and memory of two runs:
nothing, if it has none. -/
def leakAgree {ws : List ArgWord} : Option (Curry ws (Mem → List Nat)) → List (BitVec 64) → Mem →
    List (BitVec 64) → Mem → Prop
  | none, _, _, _, _ => True
  | some f, vs₁, m₁, vs₂, m₂ => Curry.apply ws f vs₁ m₁ = Curry.apply ws f vs₂ m₂

/-- The public data of a contract with at least six argument words. -/
theorem pubL_args {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {s₁ s₂ : State}
    (hk : 6 ≤ (sig.words abi.ptrBits).length) (hl : Sig.noLists sig.params = true) :
    (sig.contract abi pre post wa stack leak).pub s₁ s₂ ↔
      (s₁.gpr .rsp = s₂.gpr .rsp ∧ leakAgree leak (allArgs sig s₁) s₁.mem (allArgs sig s₂) s₂.mem) ∧
      ∀ i, (sig.params.flatMap (·.2.pubs)).getD i false = true →
        ((allArgs sig s₁).getD i 0).setWidth (((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64) =
          ((allArgs sig s₂).getD i 0).setWidth (((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64) := by
  simp only [Sig.contract]
  rw [args_some sig hk]
  simp only [Sig.descs_of_noLists _ _ _ hl, List.not_mem_nil, false_implies, implies_true, and_true]
  cases leak with
  | none => simp only [leakAgree, and_true]; exact Iff.rfl
  | some f => exact Iff.rfl

theorem getD_set_ne {l : List (BitVec 64)} {k i : Nat} {a : BitVec 64} (h : k ≠ i) :
    (l.set k a).getD i 0 = l.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

theorem getD_set_self {l : List (BitVec 64)} {k : Nat} {a : BitVec 64} (h : k < l.length) :
    (l.set k a).getD k 0 = a := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set_self h, Option.getD_some]

/-- The function's public data is the code's public data in `narrowT`. -/
theorem narrowT_pub (hq : sig.params[q]? = some (nmT, .array true .u8 16))
    (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 32 + 8 * nStack sig ≤ bytes) (hb1 : bytes < 4096)
    {preI : Curry ((sig.tagWork q nm e n).words abi.ptrBits) (Mem → Prop)}
    {postI : (sig.tagWork q nm e n).Post abi.ptrBits}
    {leakI : Option (Curry ((sig.tagWork q nm e n).words abi.ptrBits) (Mem → List Nat))}
    (ho : sig.TagFrame q nm e n abi.ptrBits pre post leak preI postI leakI) {s₁ s₂ : State}
    (h₁ : (sig.contract abi pre post wa (stack + bytes) leak).pre s₁)
    (h₂ : (sig.contract abi pre post wa (stack + bytes) leak).pre s₂)
    (hp : (sig.contract abi pre post wa (stack + bytes) leak).pub s₁ s₂)
    (hl : Sig.noLists sig.params = true) :
    ((sig.tagWork q nm e n).contract abi preI postI wa stack leakI).pub
      (narrowT sig q nm e n bytes s₁) (narrowT sig q nm e n bytes s₂) := by
  have hkI : 6 ≤ ((sig.tagWork q nm e n).words abi.ptrBits).length := by
    rw [Sig.words_tagWork _ _ _ _ hq]; exact hk
  have hlt := tagWord_lt hq
  rw [pubL_args hk hl] at hp
  obtain ⟨⟨hsp, hlk⟩, hpa⟩ := hp
  obtain ⟨-, -, -, -, e₁, -, a₁, -⟩ := narrowT_facts (nm := nm) (e := e) (n := n) hq hk hb hb1 h₁ hl
  obtain ⟨-, -, -, -, e₂, -, a₂, -⟩ := narrowT_facts (nm := nm) (e := e) (n := n) hq hk hb hb1 h₂ hl
  obtain ⟨t₁, -⟩ := narrowT_tagIn (nm := nm) (e := e) (n := n) hq hk hb hb1 h₁ hl
  obtain ⟨t₂, -⟩ := narrowT_tagIn (nm := nm) (e := e) (n := n) hq hk hb hb1 h₂ hl
  obtain ⟨l₁, l₁', s₁', st₁, -, -⟩ := tag_bufs (nm := nm) (e := e) (n := n) hq hk s₁ (tagBuf sig bytes s₁)
  obtain ⟨l₂, l₂', s₂', st₂, -, -⟩ := tag_bufs (nm := nm) (e := e) (n := n) hq hk s₂ (tagBuf sig bytes s₂)
  refine (pubL_args (sig := sig.tagWork q nm e n) (pre := preI) (post := postI) (leak := leakI) hkI
    (Sig.noLists_tagWork _ _ _ hq hl)).mpr ⟨⟨by rw [e₁, e₂, hsp], ?_⟩, fun i hi => ?_⟩
  · rw [a₁, a₂, st₁, st₂]
    have hol := ho.leak
    revert hlk hol
    cases leak <;> cases leakI <;> simp only [leakAgree, imp_self, implies_true, false_implies]
    rename_i f g
    intro hlk hol
    have p₁ := ((pre_args hk hl).mp h₁).2.2.2.2.2.2
    have p₂ := ((pre_args hk hl).mp h₂).2.2.2.2.2.2
    rw [s₁'] at p₁
    rw [s₂'] at p₂
    rw [hol _ _ _ _ _ _ l₁ l₁' t₁ p₁, hol _ _ _ _ _ _ l₂ l₂' t₂ p₂, ← s₁', ← s₂']
    exact hlk
  · rw [Sig.pubs_tagWork _ _ _ hq] at hi
    rw [a₁, a₂, Sig.words_tagWork _ _ _ _ hq]
    by_cases hik : tagWord sig q = i
    · subst hik
      rw [getD_set_self (by rw [allArgs_length _ _ hk]; exact hlt),
        getD_set_self (by rw [allArgs_length _ _ hk]; exact hlt), tagBuf, tagBuf, hsp]
    · rw [getD_set_ne hik, getD_set_ne hik]
      exact hpa i hi

/-! ## The run -/

/-- The addresses `tagOut m` accesses, from `rsp = sp`, for the tag at `t`. -/
def tagOutTrace (m : Nat) (sp t : Addr) : List Leak :=
  [.addr (sp + BitVec.ofNat 64 (8 + 8 * m)), .addr (sp + BitVec.ofNat 64 (16 + 8 * m)), .addr t,
    .addr (sp + BitVec.ofNat 64 (24 + 8 * m)), .addr (t + 8#64)]

/-- The state after `tagOut m` from `u`, if it runs. -/
def tagOutState (m : Nat) (u : State) : State :=
  ((execBlock isa (tagOut m) u).map Prod.fst).getD u

/-- Every region of the code's contract is one of the function's buffers,
the working space, or the copy of the stack arguments. -/
theorem mem_innerRegions (hq : sig.params[q]? = some (nmT, .array true .u8 16))
    (hk : 6 ≤ (sig.words abi.ptrBits).length) {s : State} {a : Region × Bool}
    (ha : a ∈ innerRegions sig q nm e n bytes s) :
    a ∈ Sig.bufs sig.params (allArgs sig s) ∨ a = (⟨tagBuf sig bytes s, n * e.size⟩, true) ∨
      a = (⟨s.gpr .rsp - BitVec.ofNat 64 bytes + 8, 8 * nStack sig⟩, false) := by
  obtain ⟨-, -, -, -, hbO, hbI⟩ := tag_bufs (nm := nm) (e := e) (n := n) hq hk s (tagBuf sig bytes s)
  rw [innerRegions, hbI] at ha
  rw [hbO]
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · exact .inl (List.mem_append_left _ ha)
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact .inr (.inl rfl)
      · exact .inl (List.mem_append_right _ (List.mem_cons_of_mem _ ha))
  · unfold copyArea at ha; split at ha
    · simp at ha
    · exact .inr (.inr (by simpa using ha))

/-- A run of the code from `narrowT s` is a run of `withTagScratch` from
`s`, after `tagSetup`'s accesses and before `tagOut`'s, which keeps what the
calling convention requires, and whose memory is the code's with the
buffer's first 16 bytes copied to the tag, and whose `rax` is the code's. -/
theorem withTagScratch_run {c : Prog isa} (hq : sig.params[q]? = some (nmT, .array true .u8 16))
    (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 32 + 8 * nStack sig ≤ bytes ∧ 16 + 8 * nStack sig + n * e.size ≤ bytes ∧ bytes < 4096 ∧
      bytes % 8 = 0)
    (hst : stack + bytes + 8 ≤ 2 ^ 64) (hsafe : SpSafe c) (hd : c.x86_64Depth ≤ stack) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) {t : List Leak} {s₃ : State}
    (he : Exec isa c (narrowT sig q nm e n bytes s) t s₃)
    (ha : abiPreserved (narrowT sig q nm e n bytes s) s₃) (hl : Sig.noLists sig.params = true) :
    Exec isa (withTagScratch bytes (nStack sig) (tagArgAt (tagWord sig q)) c) s
        (tagSetupTrace bytes (nStack sig) (tagArgAt (tagWord sig q)) (s.gpr .rsp - BitVec.ofNat 64 bytes)
            ((allArgs sig s).getD (tagWord sig q) 0) ++
          (t ++ tagOutTrace (nStack sig) (s.gpr .rsp - BitVec.ofNat 64 bytes)
            ((allArgs sig s).getD (tagWord sig q) 0)))
        (popState bytes s (tagOutState (nStack sig)
          (s₃.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)))) ∧
      abiPreserved s (popState bytes s (tagOutState (nStack sig)
        (s₃.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)))) ∧
      TagOut ((allArgs sig s).getD (tagWord sig q) 0) (tagBuf sig bytes s) s₃.mem
        (popState bytes s (tagOutState (nStack sig)
          (s₃.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)))).mem ∧
      (popState bytes s (tagOutState (nStack sig)
        (s₃.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)))).gpr .rax =
        s₃.gpr .rax := by
  obtain ⟨hb32, hb, hb1, hb2⟩ := hb
  obtain ⟨hrun, hrd', hwr', hmx, hrsp, hcs, -, hf, hslot, -⟩ :=
    narrowT_facts (nm := nm) (e := e) (n := n) hq hk hb32 hb1 hs hl
  obtain ⟨-, -, -, -, hbO, -⟩ := tag_bufs (nm := nm) (e := e) (n := n) hq hk s (tagBuf sig bytes s)
  rw [pre_args hk hl] at hs
  obtain ⟨⟨hwf, -⟩, hrd, hwr, -, hres, hnw, -⟩ := hs
  have hsb : stack + bytes ≤ (s.gpr .rsp).toNat := by rcases hwf with h | h <;> omega
  have hbelow : below (s.gpr .rsp) (stack + bytes) ∈
      (⟨s.gpr .rsp, 8⟩ :: stackBelow (s.gpr .rsp) (stack + bytes) : List Region) := by
    rw [stackBelow_pos _ (by omega)]; simp
  generalize hT : (allArgs sig s).getD (tagWord sig q) 0 = tg at hbO hrun hslot ⊢
  -- The frame's push.
  have hpush : isa.push (.alloc bytes) s = some (allocState bytes s) := by
    simp only [isa, push, allocState]
    exact ite_eq_left ⟨by omega, hb1, hb2, by omega⟩
  have hF : ∀ {a k : Nat}, a ≤ bytes → bytes - a + k ≤ bytes →
      Covers [⟨s.gpr .rsp - BitVec.ofNat 64 a, k⟩] (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) :=
    fun ha hk => Covers.one ⟨_, List.mem_cons_self .., Offset.contains_below _ ha hk (by omega)⟩
  have hscr : tagBuf sig bytes s = s.gpr .rsp - BitVec.ofNat 64 (bytes - (16 + 8 * nStack sig)) :=
    sub_add_ofNat _ (by omega)
  have harea : s.gpr .rsp - BitVec.ofNat 64 bytes + 8 = s.gpr .rsp - BitVec.ofNat 64 (bytes - 8) :=
    sub_add_ofNat _ (d := 8) (by omega)
  have hbufR : ∀ a ∈ Sig.bufs sig.params (allArgs sig s), a.2 = false → a.1 ∈ s.rd := fun a ha h => by
    rw [hrd]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ ha, by simp [h]⟩, rfl⟩
  have hbufW : ∀ a ∈ Sig.bufs sig.params (allArgs sig s), a.2 = true → a.1 ∈ s.wr := fun a ha h => by
    rw [hwr]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ ha, h⟩, rfl⟩
  have htb : ((⟨tg, 16⟩ : Region), true) ∈ Sig.bufs sig.params (allArgs sig s) := by
    rw [hbO]; exact List.mem_append_right _ (List.mem_cons_self ..)
  -- The code runs within the function's regions and the frame.
  have hcovW : Covers (((innerRegions sig q nm e n bytes s).filter (·.2)).map (·.1))
      (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) := by
    refine Covers.of_forall fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    rcases mem_innerRegions hq hk ha with ha | rfl | rfl
    · exact Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact List.mem_cons_of_mem _ (hbufW a ha hf')
    · rw [hscr]; exact hF (by omega) (by omega)
    · simp at hf'
  have hcovR : Covers (((innerRegions sig q nm e n bytes s).filter (!·.2)).map (·.1))
      (s.rd ++ ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) := by
    refine Covers.of_forall fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    rcases mem_innerRegions hq hk ha with ha | rfl | rfl
    · exact Covers.left (Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact hbufR a ha (by simpa using hf'))
    · simp at hf'
    · exact Covers.right (by rw [harea]; exact hF (by omega) (by omega))
  have hw := Exec.widen he (rd := s.rd) (wr := ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)
    (Covers.append_left hcovR (Covers.right hcovW)) hcovW
  rw [show (narrowT sig q nm e n bytes s).withRegions s.rd
      (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) =
      tagSetupState bytes (nStack sig) (tagArgAt (tagWord sig q)) (allocState bytes s) by
    rw [narrowT, State.withRegions_withRegions,
      show s.rd = (allocState bytes s).rd from rfl, ← hrd',
      show ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr = (allocState bytes s).wr from rfl,
      ← hwr', State.withRegions_self]] at hw
  -- What the code leaves: the tag pointer, and `rsp`.
  have hrsp₃ : s₃.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes :=
    (ha.1 .rsp (by simp [calleeSaved])).trans hrsp
  have hfs := Exec.stackFrame hsafe he (by omega)
  rw [hrsp] at hfs
  -- The regions the code may write, and the stack it uses, lie outside the
  -- tag pointer and the return address.
  have hcode : ∀ {R : Region}, (∀ a ∈ Sig.bufs sig.params (allArgs sig s), R.Disjoint a.1) →
      R.Disjoint ⟨tagBuf sig bytes s, n * e.size⟩ →
      R.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 bytes - BitVec.ofNat 64 c.x86_64Depth, c.x86_64Depth⟩ →
      ∀ r ∈ (narrowT sig q nm e n bytes s).wr ++
        [below (s.gpr .rsp - BitVec.ofNat 64 bytes) c.x86_64Depth], R.Disjoint r := by
    intro R h₁ h₂ h₃ r hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
      rcases mem_innerRegions hq hk ha with ha | rfl | rfl
      · exact h₁ a ha
      · exact h₂
      · simp at hf'
    · simp only [List.mem_singleton] at hr; subst hr; exact h₃
  have hslot₃ : s₃.mem.readW (s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (8 + 8 * nStack sig)) 64 =
      tg := by
    rw [hfs.readW (Region.contains_self _ _) (hcode ?_ ?_ ?_) (by decide), narrowT_mem]
    · exact hslot
    · intro a ha
      rw [show s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (8 + 8 * nStack sig) =
        s.gpr .rsp - BitVec.ofNat 64 (bytes - (8 + 8 * nStack sig)) from sub_add_ofNat _ (by omega)]
      exact (hres _ hbelow a (List.mem_append_left _ ha)).sub_left
        (Offset.sub_below _ (a := bytes - (8 + 8 * nStack sig)) (n := 8) (b := stack + bytes)
          (m := stack + bytes) (by omega) (by omega))
    · show Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (8 + 8 * nStack sig), 8⟩
        ⟨s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (16 + 8 * nStack sig), _⟩
      exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
    · exact Offset.disjoint_below _ (by omega)
  -- `tagOut`, with the function's regions and the frame.
  have e₃ : (s₃.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)).gpr .rsp =
      s.gpr .rsp - BitVec.ofNat 64 bytes := hrsp₃
  have hfr : ∀ {d : Nat}, d + 8 ≤ bytes → InRegions
      ((s₃.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)).rd ++
        (s₃.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)).wr)
      (s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 d) 8 :=
    fun h => ⟨_, List.mem_append_right _ (List.mem_cons_self ..), Offset.contains_base _ h (by omega)⟩
  have htw : (⟨tg, 16⟩ : Region) ∈ s.wr := hbufW _ htb rfl
  obtain ⟨u₄, hto, r₄, w₄, mx₄, mem₄, g₄⟩ := tagOut_run (m := nStack sig)
    (u := s₃.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr))
    (by rw [e₃]; exact hfr (by omega)) (by rw [e₃]; exact hfr (by omega))
    (by rw [State.withRegions_mem, e₃, hslot₃]
        exact ⟨_, List.mem_cons_of_mem _ htw, by simp [Region.Contains]⟩)
    (by rw [e₃]; exact hfr (by omega))
    (by rw [State.withRegions_mem, e₃, hslot₃]
        exact ⟨_, List.mem_cons_of_mem _ htw,
          Offset.contains_base tg (d := 8) (n := 8) (k := 16) (by omega) (by omega)⟩)
  rw [State.withRegions_mem, e₃, hslot₃] at hto
  rw [State.withRegions_mem, e₃] at mem₄
  have hst₄ : tagOutState (nStack sig)
      (s₃.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)) = u₄ := by
    simp [tagOutState, hto]
  rw [hst₄]
  -- The pop.
  have hrsp₄ : u₄.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes :=
    (g₄ .rsp (by decide) (by decide)).trans e₃
  have hu₄ : u₄.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) = u₄ := by
    rw [show s.rd = u₄.rd from r₄.symm,
      show (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr : List Region) = u₄.wr from w₄.symm,
      State.withRegions_self]
  have hpop : isa.pop (.free bytes) (allocState bytes s)
      (u₄.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)) =
      some (popState bytes s u₄) := by
    simp only [isa, pop, State.withRegions_gpr, State.withRegions_wr]
    refine ite_eq_left ⟨by omega, hb1, hb2, ?_, rfl, ?_⟩
    · rw [hrsp₄]; simp [allocState, State.setReg]
    · simp [allocState, State.setReg]
  rw [hu₄] at hpop
  have hex := Exec.frame hpush (Exec.seq (Exec.block hrun) (Exec.seq hw (Exec.block hto))) hpop
  simp only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] at hex
  have hR : ∀ {x k : Nat}, x ≤ stack + bytes → stack + bytes - x + k ≤ stack + bytes →
      (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 x, k⟩ := fun hx hk =>
    (Offset.base_disjoint_below _ (n := stack + bytes) (k := 8) (by omega)).sub_right
      (Offset.sub_below _ hx hk)
  have hcs' : ∀ r ∈ calleeSaved, r ≠ .r10 ∧ r ≠ .r11 := by decide
  obtain ⟨fo, fv⟩ := tagOutMem_facts (m := nStack sig) (M := s₃.mem)
    (p := s.gpr .rsp - BitVec.ofNat 64 bytes) (by
      rw [hslot₃, show s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (8 + 8 * nStack sig) =
        s.gpr .rsp - BitVec.ofNat 64 (bytes - (8 + 8 * nStack sig)) from sub_add_ofNat _ (by omega)]
      exact (Region.Disjoint.symm (hres _ hbelow _ (List.mem_append_left _ htb))).sub_right
        (Offset.sub_below _ (by omega) (by omega)))
  rw [hslot₃] at fo fv
  refine ⟨hex, ⟨fun r hr => ?_, ?_, ?_⟩,
    ⟨fun x hx => by
      show u₄.mem x = _
      rw [mem₄]; exact fo x fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hx,
     fun i hi => by show u₄.mem _ = _; rw [mem₄]; exact fv i hi⟩, ?_⟩
  · -- The callee-saved registers.
    simp only [popState, State.setReg, State.withRegions_gpr]
    by_cases hqs : r = .rsp
    · subst hqs; simp only [ite_true, hrsp₄, BitVec.sub_add_cancel]
    · simp only [hqs, ite_false]
      rw [g₄ r (hcs' r hr).1 (hcs' r hr).2, State.withRegions_gpr, ha.1 r hr, hcs r hr hqs]
  · -- The return address: `tagOut` writes only the tag, the code its regions
    -- and below `rsp`, and `tagSetup` only the frame.
    show u₄.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64
    rw [mem₄, fo.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hres _ (List.mem_cons_self ..) _ (List.mem_append_left _ htb)) (by decide),
      hfs.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (hcode
        (fun a ha => hres _ (List.mem_cons_self ..) a (List.mem_append_left _ ha))
        (by rw [hscr]; exact hR (by omega) (by omega))
        (by rw [BitVec.sub_sub, ← BitVec.ofNat_add]; exact hR (by omega) (by omega))) (by decide),
      narrowT_mem]
    rw [← narrowT_mem]
    exact hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [harea]; exact hR (by omega) (by omega))
      (by decide)
  · -- MXCSR.
    show u₄.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
    rw [mx₄]
    show s₃.mxcsr.extractLsb' 6 10 = _
    rw [ha.2.2, hmx]
  · simp only [popState, State.setReg, State.withRegions_gpr, show Reg.rax ≠ Reg.rsp by decide,
      ↓reduceIte]
    rw [g₄ .rax (by decide) (by decide)]
    rfl

/-- The tag pointer is public. -/
theorem tag_pub (hq : sig.params[q]? = some (nmT, .array true .u8 16))
    (hk : 6 ≤ (sig.words abi.ptrBits).length) {s₁ s₂ : State}
    (hp : (sig.contract abi pre post wa stack leak).pub s₁ s₂) (hl : Sig.noLists sig.params = true) :
    (allArgs sig s₁).getD (tagWord sig q) 0 = (allArgs sig s₂).getD (tagWord sig q) 0 := by
  obtain ⟨-, hpa⟩ := (pubL_args hk hl).mp hp
  have hpub : (sig.params.flatMap (·.2.pubs)).getD (tagWord sig q) false = true := by
    conv => lhs; rw [Sig.params_split hq]
    rw [List.flatMap_append, List.flatMap_cons, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [Sig.pubs_length _ abi.ptrBits]),
      Sig.pubs_length _ abi.ptrBits]
    simp only [tagWord, Nat.sub_self]
    rfl
  have hw : ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD (tagWord sig q) 64 = 64 := by
    rw [Sig.words_split _ hq, List.map_append, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [List.length_map])]
    simp [ArgWord.bits, abi]
  have h := hpa _ hpub
  rw [hw] at h
  simpa using h

/-- Code verified for a function whose parameter `q` is working space that
also carries a 16-byte tag in its first 16 bytes (`Sig.tagWork`), with
`stack` bytes of stack, is verified for the function whose parameter `q` is
the tag, which allocates the working space in a frame of `bytes` more bytes
of stack (`withTagScratch`), if the two contracts are related by
`Sig.TagFrame`. -/
theorem Verified.tagScratch {c : Prog isa}
    {preI : Curry ((sig.tagWork q nm e n).words abi.ptrBits) (Mem → Prop)}
    {postI : (sig.tagWork q nm e n).Post abi.ptrBits}
    {leakI : Option (Curry ((sig.tagWork q nm e n).words abi.ptrBits) (Mem → List Nat))}
    (h : Verified target c ((sig.tagWork q nm e n).contract abi preI postI wa stack leakI))
    (ho : sig.TagFrame q nm e n abi.ptrBits pre post leak preI postI leakI)
    (hq : sig.params[q]? = some (nmT, .array true .u8 16))
    (hk : 6 ≤ (sig.words abi.ptrBits).length)
    (hb : 32 + 8 * nStack sig ≤ bytes ∧ 16 + 8 * nStack sig + n * e.size ≤ bytes ∧ bytes < 4096 ∧
      bytes % 8 = 0)
    (hst : stack + bytes + 8 ≤ 2 ^ 64)
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ stack)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes) leak).pre s)
    (hl : Sig.noLists sig.params = true := by decide) :
    Verified target (withTagScratch bytes (nStack sig) (tagArgAt (tagWord sig q)) c)
      (sig.contract abi pre post wa (stack + bytes) leak) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hsafe := SpSafe.of_all hsp
  have hkI : 6 ≤ ((sig.tagWork q nm e n).words abi.ptrBits).length := by
    rw [Sig.words_tagWork _ _ _ _ hq]; exact hk
  -- Every run is `tagSetup`, the code's run from `narrowT`, and `tagOut`.
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes) leak).pre s → ∃ t s₃,
      Exec isa c (narrowT sig q nm e n bytes s) t s₃ ∧
      ((sig.tagWork q nm e n).contract abi preI postI wa stack leakI).post
        (narrowT sig q nm e n bytes s) s₃ ∧
      Exec isa (withTagScratch bytes (nStack sig) (tagArgAt (tagWord sig q)) c) s
        (tagSetupTrace bytes (nStack sig) (tagArgAt (tagWord sig q)) (s.gpr .rsp - BitVec.ofNat 64 bytes)
            ((allArgs sig s).getD (tagWord sig q) 0) ++
          (t ++ tagOutTrace (nStack sig) (s.gpr .rsp - BitVec.ofNat 64 bytes)
            ((allArgs sig s).getD (tagWord sig q) 0)))
        (popState bytes s (tagOutState (nStack sig)
          (s₃.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)))) ∧
      abiPreserved s (popState bytes s (tagOutState (nStack sig)
        (s₃.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)))) ∧
      TagOut ((allArgs sig s).getD (tagWord sig q) 0) (tagBuf sig bytes s) s₃.mem
        (popState bytes s (tagOutState (nStack sig)
          (s₃.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)))).mem ∧
      (popState bytes s (tagOutState (nStack sig)
        (s₃.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)))).gpr .rax =
        s₃.gpr .rax := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq'⟩ := hcor _ (narrowT_pre hq hk ⟨hb.1, hb.2.1⟩ hb.2.2.1 ho hs hl)
    exact ⟨t, s₃, he, hq', withTagScratch_run hq hk hb hst hsafe hd hs he ha hl⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, -, hpost, hex, ha, hto, hrax⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    rw [post_args hk]
    have hq' := (post_args (sig := sig.tagWork q nm e n) (pre := preI) (post := postI) (leak := leakI)
      hkI).mp hpost
    obtain ⟨-, -, -, -, -, -, hargs, -⟩ :=
      narrowT_facts (nm := nm) (e := e) (n := n) hq hk hb.1 hb.2.2.1 hs hl
    obtain ⟨hl₁, hl₂, hsplit, hset, -, -⟩ :=
      tag_bufs (nm := nm) (e := e) (n := n) hq hk s (tagBuf sig bytes s)
    obtain ⟨hin, hdis⟩ := narrowT_tagIn (nm := nm) (e := e) (n := n) hq hk hb.1 hb.2.2.1 hs hl
    have hpr := ((pre_args hk hl).mp hs).2.2.2.2.2.2
    rw [hargs, hset] at hq'
    rw [hsplit] at hpr
    rw [hrax, hsplit]
    exact ho.post _ _ _ _ _ _ _ _ _ hl₁ hl₂ hin hpr hdis hto hq'
  · obtain ⟨u₁, r₁, f₁, -, x₁, -⟩ := hrun s₁ h₁
    obtain ⟨u₂, r₂, f₂, -, x₂, -⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1, ((pubL_args hk hl).mp hp).1.1, tag_pub hq hk hp hl,
      hct _ _ _ _ _ _ (narrowT_pre hq hk ⟨hb.1, hb.2.1⟩ hb.2.2.1 ho h₁ hl)
        (narrowT_pre hq hk ⟨hb.1, hb.2.1⟩ hb.2.2.1 ho h₂ hl)
        (narrowT_pub hq hk hb.1 hb.2.2.1 ho h₁ h₂ hp hl) f₁ f₂]

end

/-- `withTagScratch` writes `rsp` only in its frame if its code does. -/
theorem withTagScratch_spSafe {bytes m k : Nat} {c : Prog isa}
    (h : c.all (fun i => !isa.writesSp i) = true) :
    (withTagScratch bytes m (tagArgAt k) c).all (fun i => !isa.writesSp i) = true := by
  have hc : ((List.range m).flatMap (copyArg bytes)).all (fun i => !isa.writesSp i) = true :=
    List.all_eq_true.mpr fun i hi => by
      obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hi
      simp only [copyArg, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl <;> rfl
  have ha : (loadTagPtr bytes (tagArgAt k) ++ tagIn m ++ pointTag m (tagArgAt k)).all
      (fun i => !isa.writesSp i) = true := by
    unfold tagArgAt
    split
    · next hk =>
      have hr : argRegs[k]?.getD .rax ≠ .rsp := by
        rw [← List.getD_eq_getElem?_getD]; exact (argRegs_ok k hk).2.1
      simp [loadTagPtr, tagIn, pointTag, Instr.dst, hr]
    · simp [loadTagPtr, tagIn, pointTag, Instr.dst]
  simp only [withTagScratch, tagSetup, Code.all, List.all_append, h, hc, Bool.true_and]
  simp only [List.all_append] at ha
  simp only [ha]
  rfl

end VG.X86_64
