module

public import VerifiedGarbage.Proof.MlDsa.Arm.PreparedKey.Body
public import VerifiedGarbage.Proof.Argon2.Arm.Push
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.Mem

/-!
# ML-DSA on ARMv7, preparing keys: the entry

The precondition of the contracts, spelled out (`EntryPre`); the frame
saving `r4`, `r7`, `r8` and `lr`, and the moves of the arguments, after which
the buffers are a layout (`entry_lay`); and the loads and the pop that
restore the registers saved, so that a body that prepares the key prepares
it in `prepared` and keeps the registers the ABI preserves (`entry_correct`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.PreparedKey

open VG VG.Arm VG.Spec.MlDsa
open VG.Impl.MlDsa.Arm.PreparedKey
open VG.Impl.MlDsa.Arm.Sign (Prims Ptr)
open VG.Proof.MlDsa.Arm.Sign
open VG.Spec.Sha3 (bytesAt)

/-- The stack of the calls of the body. -/
abbrev callStack : Nat := 28

/-- The stack of the preparations: their frame (16 bytes) and that of the calls. -/
abbrev prepStack : Nat := 44

/-- The precondition of `preparePublicKeyContract` and `prepareSecretKeyContract`,
for a key of `bytes` bytes and `count` polynomials. -/
structure EntryPre (bytes count : Nat) (s : State) : Prop where
  stk : prepStack ≤ s.sp.toNat
  rd : s.rd = [⟨State.addr (s.gpr .r0), bytes⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r1), bytes + 1024 * count⟩, ⟨State.addr (s.gpr .r2), 1024⟩]
  io : Region.Disjoint ⟨State.addr (s.gpr .r0), bytes⟩ ⟨State.addr (s.gpr .r1), bytes + 1024 * count⟩
  it : Region.Disjoint ⟨State.addr (s.gpr .r0), bytes⟩ ⟨State.addr (s.gpr .r2), 1024⟩
  ot : Region.Disjoint ⟨State.addr (s.gpr .r1), bytes + 1024 * count⟩ ⟨State.addr (s.gpr .r2), 1024⟩
  si : (Argon2.Arm.stkR s.sp prepStack).Disjoint ⟨State.addr (s.gpr .r0), bytes⟩
  so : (Argon2.Arm.stkR s.sp prepStack).Disjoint ⟨State.addr (s.gpr .r1), bytes + 1024 * count⟩
  st : (Argon2.Arm.stkR s.sp prepStack).Disjoint ⟨State.addr (s.gpr .r2), 1024⟩
  ni : (s.gpr .r0).toNat + bytes ≤ 2 ^ 32
  no : (s.gpr .r1).toNat + (bytes + 1024 * count) ≤ 2 ^ 32
  nt : (s.gpr .r2).toNat + 1024 ≤ 2 ^ 32

theorem publicBytes_eq (p : Params) : preparedPublicKeyBytes p = p.pkLen + 1024 * p.k := by
  unfold preparedPublicKeyBytes n; omega

theorem secretBytes_eq (p : Params) : preparedSecretKeyBytes p = p.skLen + 1024 * (p.ℓ + 2 * p.k) := by
  unfold preparedSecretKeyBytes n; omega

theorem public_pre {p : Params} {s : State} (h : (preparePublicKeyContract p Arm.abi prepStack).pre s) :
    EntryPre p.pkLen p.k s := by
  sig_pre [preparePublicKeyContract, preparePublicKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  rw [publicBytes_eq] at h
  obtain ⟨h0, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem secret_pre {p : Params} {s : State} (h : (prepareSecretKeyContract p Arm.abi prepStack).pre s) :
    EntryPre p.skLen (p.ℓ + 2 * p.k) s := by
  sig_pre [prepareSecretKeyContract, prepareSecretKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  rw [secretBytes_eq] at h
  obtain ⟨h0, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-! ## The moves of the arguments -/

/-- The registers saved. -/
abbrev saved : List Reg := [.r4, .r7, .r8, .lr]

theorem movs_ok (s : State) :
    WP isa (.block [.mov .r4 (.reg .r0), .mov .r8 (.reg .r1), .mov .r7 (.reg .r2)]) s fun u =>
      u.gpr .r4 = s.gpr .r0 ∧ u.gpr .r8 = s.gpr .r1 ∧ u.gpr .r7 = s.gpr .r2 ∧
      (∀ r, r ≠ .r4 → r ≠ .r8 → r ≠ .r7 → u.gpr r = s.gpr r) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧
      u.sp = s.sp := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.sp_setReg, ↓reduceIte, reduceCtorEq, and_self]
  exact ⟨trivial, trivial, trivial, fun r h4 h8 h7 => by simp only [h4, h8, h7, ite_false], trivial⟩

section
variable {bytes count : Nat} {σ : State} (h : EntryPre bytes count σ)
include h

theorem h16 : 16 ≤ σ.sp.toNat := by have := h.stk; simp only [prepStack] at this; omega

/-- The frame, below `σ`'s stack pointer. -/
theorem frame_sub : Region.Sub (Argon2.Arm.stkR σ.sp 16) (Argon2.Arm.stkR σ.sp prepStack) :=
  Argon2.Arm.stkR_sub (by decide) h.stk

/-- The buffers, in `σ`. -/
theorem buf_disj {u : State} (h4 : u.gpr .r4 = σ.gpr .r0) (h8 : u.gpr .r8 = σ.gpr .r1)
    (h7 : u.gpr .r7 = σ.gpr .r2) :
    ∀ b ∈ input bytes ++ output bytes count,
      (Argon2.Arm.stkR σ.sp prepStack).Disjoint ⟨State.addr (u.gpr b.1), b.2⟩ := by
  intro b hb
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · rw [h4]; exact h.si
  · rw [h8]; exact h.so
  · rw [h7]; exact h.st

/-- After the push and the moves, the buffers are a layout. -/
theorem entry_lay (hb : bytes < 2 ^ 32) (ho : bytes + 1024 * count < 2 ^ 32) {u : State}
    (h4 : u.gpr .r4 = σ.gpr .r0) (h8 : u.gpr .r8 = σ.gpr .r1) (h7 : u.gpr .r7 = σ.gpr .r2)
    (hsp : u.sp = σ.sp - BitVec.ofNat 32 16) (hrd : u.rd = σ.rd)
    (hwr : u.wr = ⟨State.addr (σ.sp - BitVec.ofNat 32 16), 16⟩ :: σ.wr) :
    Lay callStack (input bytes) (output bytes count) u := by
  have h16 := h16 h
  have hst : Region.Sub (belowA u.sp callStack) (Argon2.Arm.stkR σ.sp prepStack) := by
    rw [hsp]; exact Argon2.Arm.stkR_inner (by decide) h.stk
  have mem : ∀ R ∈ σ.rd ++ σ.wr, InRegions (u.rd ++ u.wr) R.base R.len := fun R hR =>
    ⟨R, by
      rw [hrd, hwr]
      rcases List.mem_append.mp hR with hR | hR
      · exact List.mem_append_left _ hR
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hR), Region.contains_self _ _⟩
  refine ⟨?_, ?_, fun b hb => ((buf_disj h h4 h8 h7) b hb).sub_left hst, ?_, ?_, ?_, ?_⟩
  · intro b hb'
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb'
    rcases hb' with rfl | rfl | rfl
    exacts [hb, ho, by decide]
  · intro b hb' b' hb'' hne _
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb' hb''
    rcases hb' with rfl | rfl | rfl <;> rcases hb'' with rfl | rfl | rfl <;>
      first
      | exact absurd rfl hne
      | simp only [h4, h8, h7]
        first | exact h.io | exact h.it | exact h.ot | exact h.io.symm | exact h.it.symm | exact h.ot.symm
  · intro b hb'
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb'
    rcases hb' with rfl | rfl | rfl <;> simp only [h4, h8, h7]
    exacts [h.ni, h.no, h.nt]
  · intro b hb'
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb'
    rcases hb' with rfl | rfl | rfl <;> simp only [h4, h8, h7]
    · exact mem ⟨State.addr (σ.gpr .r0), bytes⟩ (by rw [h.rd, h.wr]; simp)
    · exact mem ⟨State.addr (σ.gpr .r1), bytes + 1024 * count⟩ (by rw [h.rd, h.wr]; simp)
    · exact mem ⟨State.addr (σ.gpr .r2), 1024⟩ (by rw [h.rd, h.wr]; simp)
  · intro b hb'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
    rcases hb' with rfl | rfl <;> simp only [h8, h7] <;>
      exact ⟨_, by rw [hwr, h.wr]; simp, Region.contains_self _ _⟩
  · rw [hsp, FrameStack.sub_toNat' (by omega)]
    have := h.stk; simp only [prepStack, callStack] at this ⊢; omega

/-- The word `i` of the frame. -/
theorem word_sub {i : Nat} (hi : i < 4) :
    Region.Sub ⟨State.addr (σ.sp - BitVec.ofNat 32 16 + BitVec.ofNat 32 (4 * i)), 4⟩ (Argon2.Arm.stkR σ.sp 16) := by
  have h16 := h16 h
  have e : State.addr (σ.sp - BitVec.ofNat 32 16 + BitVec.ofNat 32 (4 * i)) =
      (State.addr σ.sp - BitVec.ofNat 64 16) + BitVec.ofNat 64 (4 * i) := by
    rw [addr_add (by rw [FrameStack.sub_toNat' h16]; have := σ.sp.isLt; omega), FrameStack.addr_sub' h16]
  rw [e]
  exact Offset.sub_base _ (by omega)

end

/-! ## The loads of the registers saved -/

theorem ldrSp_ok (r : Reg) {off : Nat} (ho : off < 4096) (s : State)
    (hA : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 off)) 4) :
    WP isa (.block [.ldrSp r off]) s (· = s.setReg r (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, State.load32, hA, ho, ↓reduceIte,
    Option.map_some, Option.some.injEq, exists_eq_left']

/-- The address of word `i` of the frame. -/
theorem word_addr {sp : BitVec 32} (h16 : 16 ≤ sp.toNat) {i : Nat} (hi : i < 4) :
    State.addr (sp - BitVec.ofNat 32 16 + BitVec.ofNat 32 (4 * i)) =
      State.addr (sp - BitVec.ofNat 32 16) + BitVec.ofNat 64 (4 * i) :=
  addr_add (by rw [FrameStack.sub_toNat' h16]; have := sp.isLt; omega)

/-! ## The entry -/

theorem entry_correct {body : Prog isa} {bytes count : Nat} {B : Mem → Addr → Prop}
    (W : State → List Region) (hb : bytes < 2 ^ 32) (ho : bytes + 1024 * count < 2 ^ 32)
    (hW : ∀ u, ∀ R ∈ W u, ∃ b ∈ input bytes ++ output bytes count, Region.Sub R ⟨State.addr (u.gpr b.1), b.2⟩)
    (hbody : ∀ u, Lay callStack (input bytes) (output bytes count) u → WP isa body u fun t =>
      PostB callStack u t (W u) ∧ CS u t ∧
      bytesAt t.mem (pa t (.r8, 0)) bytes = bytesAt u.mem (pa u (.r4, 0)) bytes ∧ B t.mem (pa t (.r8, 0)))
    {σ : State} (h : EntryPre bytes count σ) :
    WP isa (entry body) σ fun s' => abiPreserved σ s' ∧
      bytesAt s'.mem (State.addr (σ.gpr .r1)) bytes = bytesAt σ.mem (State.addr (σ.gpr .r0)) bytes ∧
      B s'.mem (State.addr (σ.gpr .r1)) := by
  have h16 := h16 h
  unfold entry
  refine WP.frame (rs := saved) (r := .r4) (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
    (by decide) ?_
  refine WP.seq (WP.mono (movs_ok _) fun u ⟨g4, g8, g7, g, gm, grd, gwr, gsp⟩ => ?_)
  have u4 : u.gpr .r4 = σ.gpr .r0 := by rw [g4, pushed_gpr]
  have u8 : u.gpr .r8 = σ.gpr .r1 := by rw [g8, pushed_gpr]
  have u7 : u.gpr .r7 = σ.gpr .r2 := by rw [g7, pushed_gpr]
  have usp : u.sp = σ.sp - BitVec.ofNat 32 16 := by rw [gsp, pushed_sp]; rfl
  have urd : u.rd = σ.rd := by rw [grd, pushed_rd]
  have uwr : u.wr = ⟨State.addr (σ.sp - BitVec.ofNat 32 16), 16⟩ :: σ.wr := by rw [gwr, pushed_wr]; rfl
  have L := entry_lay h hb ho u4 u8 u7 usp urd uwr
  refine WP.seq (WP.mono (hbody u L) fun t ⟨hP, hcs, henc, hB⟩ => ?_)
  have umem : u.mem = storeWords σ.mem (σ.sp - BitVec.ofNat 32 16) (saved.map σ.gpr) := gm
  -- The words of the frame are kept.
  have word : ∀ i (hi : i < 4), t.mem.readW (State.addr (σ.sp - BitVec.ofNat 32 16 + BitVec.ofNat 32 (4 * i))) 32 =
      (saved.map σ.gpr)[i]'(by simpa using hi) := by
    intro i hi
    rw [hP.frame.readW (Region.contains_self _ _) ?_ (by decide), umem]
    · exact Argon2.Arm.storeWords_readW _ _ _ (by rw [FrameStack.sub_toNat' h16]; have := σ.sp.isLt; simp; omega)
        (by simpa using hi)
    · intro R hR
      have ws := word_sub h hi
      rcases List.mem_append.mp hR with hR | hR
      · obtain ⟨b, hb', hsub⟩ := hW u R hR
        exact (((buf_disj h u4 u8 u7) b hb').sub_left fun x hx => frame_sub h x (ws x hx)).sub_right hsub
      · rw [List.mem_singleton] at hR; subst hR
        rw [usp, word_addr h16 hi]
        show Region.Disjoint _ ⟨State.addr (σ.sp - BitVec.ofNat 32 16) - BitVec.ofNat 64 callStack, callStack⟩
        exact Offset.disjoint_below _ (by simp only [callStack]; omega)
  have tsp : t.sp = σ.sp - BitVec.ofNat 32 16 := hP.sp.trans usp
  have twr : t.wr = ⟨State.addr (σ.sp - BitVec.ofNat 32 16), 16⟩ :: σ.wr := hP.wr.trans uwr
  have inF : ∀ (s : State) (i : Nat), i < 4 → s.sp = σ.sp - BitVec.ofNat 32 16 →
      s.wr = ⟨State.addr (σ.sp - BitVec.ofNat 32 16), 16⟩ :: σ.wr →
      InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 (4 * i))) 4 := fun s i hi hs hw =>
    ⟨_, List.mem_append_right _ (by rw [hw]; exact List.mem_cons_self ..), by
      rw [hs, word_addr h16 hi]; exact Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.seq (WP.mono (ldrSp_ok .r7 (off := 4 * 1) (by decide) t (inF t 1 (by decide) tsp twr)) fun t₁ e₁ => ?_)
  subst e₁
  refine WP.seq (WP.mono (ldrSp_ok .r8 (off := 4 * 2) (by decide) _ (inF _ 2 (by decide) tsp twr)) fun t₂ e₂ => ?_)
  subst e₂
  refine WP.mono (ldrSp_ok .lr (off := 4 * 3) (by decide) _ (inF _ 3 (by decide) tsp twr)) fun t₃ e₃ => ?_
  subst e₃
  have w0 := word 0 (by decide)
  have w1 := word 1 (by decide)
  have w2 := word 2 (by decide)
  have w3 := word 3 (by decide)
  simp only [Nat.mul_zero, BitVec.add_zero, List.map_cons, List.map_nil, List.getElem_cons_zero,
    List.getElem_cons_succ] at w0 w1 w2 w3
  simp only [RegUpd.sp_setReg, RegUpd.mem_setReg, tsp]
  rw [w1, w2, w3]
  have e8 : t.gpr .r8 = σ.gpr .r1 := (hP.bs .r8 (by decide)).trans u8
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_⟩
  all_goals simp only [popped, RegUpd.sp_setReg, RegUpd.mem_setReg]
  · simp only [RegUpd.gpr_setReg]
    by_cases e4 : r = .r4
    · subst e4; simp only [↓reduceIte]; rw [tsp, w0]
    by_cases e7 : r = .r7
    · subst e7; simp only [↓reduceIte, reduceCtorEq]
    by_cases e8' : r = .r8
    · subst e8'; simp only [↓reduceIte, reduceCtorEq]
    by_cases el : r = .lr
    · subst el; simp only [↓reduceIte, reduceCtorEq]
    simp only [e4, e7, e8', el, ite_false]
    rw [hcs r hr el, g r e4 e8' e7, pushed_gpr]
  · rw [tsp]; exact BitVec.sub_add_cancel _ _
  · have ek : bytesAt u.mem (State.addr (σ.gpr .r0)) bytes = bytesAt σ.mem (State.addr (σ.gpr .r0)) bytes := by
      rw [gm]
      exact VG.Proof.MlKem.bytesAt_frame (Argon2.Arm.pushed_stk (rs := saved) (s := σ)
        (by simp only [List.length_cons, List.length_nil]; omega)) (fun R hR => by
          simp only [List.mem_singleton] at hR; subst hR; exact (h.si.sub_left (frame_sub h)).symm) (by omega)
    simp only [pa, BitVec.add_zero, e8, u4] at henc
    rw [henc, ek]
  · simp only [pa, BitVec.add_zero, e8] at hB; exact hB

end VG.Proof.MlDsa.Arm.PreparedKey
