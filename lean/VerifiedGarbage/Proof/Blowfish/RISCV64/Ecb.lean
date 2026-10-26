module

public import VerifiedGarbage.Proof.Blowfish.RISCV64.Cipher
public import VerifiedGarbage.Proof.Blowfish.RISCV64.Frame
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Blowfish.Blocks
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.RISCV64.Steps

/-!
# Blowfish on RISC-V: ECB

`ecb_wp`: every block becomes its encryption or decryption, one at a time,
under the schedule copied into the frame, which is zeroed (`Zeroed`)
before returning. The structure of PPC64LE's (`Proof/Blowfish/PPC64LE/Ecb.lean`).
-/

@[expose] public section

namespace VG.Proof.Blowfish.RISCV64

open VG VG.RISCV64 VG.RISCV64.ByteLoad VG.Impl.Blowfish.RISCV64 VG.Spec.Blowfish VG.Proof.Blowfish
open VG.WriteBytes (writeBytes)

/-! ## Blocks in and out of the halves -/

theorem beWord_byte (m : Mem) (p : Addr) (off : Nat) {b : Nat} (hb : b < 4) :
    (beWord m p off).extractLsb' (8 * b) 8 = m (p + BitVec.ofNat 64 (off + (3 - b))) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [beWord, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;>
    simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right] <;> congr 1 <;> omega

/-- The big-endian word at offset `o` of the block at `q`. -/
theorem beWord_block (m : Mem) (q : Addr) {o : Nat} (ho : o ≤ 4) :
    beWord m q o = decodeWord (blockAt m q) o := by
  refine word_ext fun b hb => ?_
  rw [beWord_byte _ _ _ hb, decodeWord_byte _ _ hb, blockAt_getD _ _ (by omega)]

/-- The block at `a1` into the halves, as big-endian words. -/
theorem loadBlock_run (u : State) {q : Addr} (hq : u.gpr .a1 = q)
    (r : InRegions (u.rd ++ u.wr) q 8) :
    WP isa (.block loadBlock) u fun t =>
      lo (t.gpr .a3) = decodeWord (blockAt u.mem q) 0 ∧ lo (t.gpr .a4) = decodeWord (blockAt u.mem q) 4 ∧
        Keep [.a3, .a4, .t4] u t ∧ t.mem = u.mem := by
  unfold loadBlock
  rw [WP.block_append_iff]
  refine WP.mono (loadBE32_ok (d := .a3) (tmp := .t4) (n := .a1) (off := 0) (by decide) (by decide)
    (by decide) (by decide) (by rw [hq]; exact CallLay.inRegions_sub r (by decide) (by decide)))
    fun u₁ e₁ => ?_
  subst e₁
  refine WP.mono (loadBE32_ok (d := .a4) (tmp := .t4) (n := .a1) (off := 4) (by decide) (by decide)
    (by decide) (by decide) (by
      simp only [RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, reduceCtorEq, ite_false, hq]
      exact CallLay.inRegions_sub r (by decide) (by decide))) fun u₂ e₂ => ?_
  subst e₂
  refine ⟨?_, ?_, ⟨fun r hr => ?_, rfl, rfl⟩, rfl⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, lo_ext, hq,
      beWord_block _ _ (o := 0) (by decide)]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, lo_ext, RegUpd.mem_write, hq,
      beWord_block _ _ (o := 4) (by decide)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

/-- The halves to the block at `a1`, the next block's pointer, and the
counter less one. -/
theorem storeBlock_run (u : State) {q : Addr} (hq : u.gpr .a1 = q) (w : InRegions u.wr q 8) :
    WP isa (.block storeBlock) u fun t =>
      t.mem = writeBytes u.mem q (beBytes 4 (u.gpr .a3) ++ beBytes 4 (u.gpr .a4)) ∧
      t.gpr .a1 = q + 8#64 ∧ t.gpr .a2 = u.gpr .a2 - 1#64 ∧ Keep [.t4, .a1, .a2] u t := by
  unfold storeBlock
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (storeBE_ok (v := .a3) (tmp := .t4) (n := .a1) (off := 0) (w := 4) (by decide) (by decide)
    (by decide) (by decide) (by decide) fun j hj => by
      rw [hq]; exact CallLay.inRegions_sub w (by omega) (by decide)) fun u₁ e₁ => ?_
  subst e₁
  refine WP.mono (storeBE_ok (v := .a4) (tmp := .t4) (n := .a1) (off := 4) (w := 4) (by decide) (by decide)
    (by decide) (by decide) (by decide) fun j hj => by
      simp only [RegUpd.gpr_write, RegUpd.wr_write, reduceCtorEq, ite_false, hq]
      exact CallLay.inRegions_sub w (by omega) (by decide)) fun u₂ e₂ => ?_
  subst e₂
  have h1 : u.gpr .a1 = q := hq
  refine WP.mono (WP.keep [.a1, .a2] (Q := fun t => t.gpr .a1 = q + 8#64 ∧ t.gpr .a2 = u.gpr .a2 - 1#64 ∧
      t.mem = writeBytes u.mem q (beBytes 4 (u.gpr .a3) ++ beBytes 4 (u.gpr .a4))) (by
    brun [RegUpd.gpr_write, RegUpd.mem_write, h1]
    have h := WriteBytes.writeBytes_append u.mem q (beBytes 4 (u.gpr .a3)) (beBytes 4 (u.gpr .a4)) (by
      simp only [beBytes_length]; decide)
    rwa [beBytes_length] at h) (by decide) rfl) fun t ⟨⟨t1, t2, tm⟩, tk⟩ => ⟨tm, t1, ?_, ?_⟩
  · exact t2
  · refine ⟨fun r hr => ?_, tk.2.1, tk.2.2⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [tk.gpr (by simp [hr.2.1, hr.2.2])]
    simp only [RegUpd.gpr_write, hr.1, ite_false]

theorem shr_lo (x : BitVec 64) {k : Nat} (hk : k ≤ 24) :
    (x >>> k).setWidth 8 = (lo x).extractLsb' k 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi, show k + i < 32 by omega]

/-- What the stores leave: the block. -/
theorem stored_block (m : Mem) (q : Addr) (x y : BitVec 64) :
    blockAt (writeBytes m q (beBytes 4 x ++ beBytes 4 y)) q = encodeBlock (lo x) (lo y) := by
  refine blockAt_eq _ _ _ fun i hi => ?_
  rw [encodeBlock_getD _ _ hi]
  simp only [writeBytes, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
    List.length_append, beBytes_length, show i < 4 + 4 by omega, ite_true]
  by_cases h4 : i < 4
  · rw [ite_eq_left h4, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [beBytes_length]; exact h4)]
    simp only [beBytes, List.getElem?_map, List.getElem?_range h4, Option.map_some, Option.getD_some]
    rw [shr_lo _ (by omega)]
  · rw [ite_eq_right h4, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [beBytes_length]; omega), beBytes_length]
    simp only [beBytes, List.getElem?_map, List.getElem?_range (show i - 4 < 4 by omega), Option.map_some,
      Option.getD_some]
    rw [shr_lo _ (by omega)]
    congr 2; omega

theorem stored_frame (m : Mem) (q : Addr) (x y : BitVec 64) :
    Frame [⟨q, 8⟩] m (writeBytes m q (beBytes 4 x ++ beBytes 4 y)) :=
  WriteBytes.writeBytes_frame _ _ _ (by
    simp only [List.length_append, beBytes_length]
    exact Region.contains_self q 8)

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 8⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, Vector.getElem_ofFn]
  exact hf.bytes (R := ⟨p, 8⟩) hd (by show 8 ≤ 2 ^ 64; decide) hi

/-! ## The loop -/

/-- A block's encryption (`up`) or decryption. -/
def blockOut (K : Schedule) (up : Bool) (b : Block) : Block :=
  if up then encryptBlock K b else decryptBlock K b

theorem blockOut_eq (K : Schedule) (up : Bool) (b : Block) :
    blockOut K up b = encodeBlock (feistel K (ord up) (decodeWord b 0) (decodeWord b 4)).1
      (feistel K (ord up) (decodeWord b 0) (decodeWord b 4)).2 := by
  cases up <;> rfl

/-- The block `b` of the data at `D`. -/
abbrev wAt (D : Addr) (b : Nat) : Addr := D + BitVec.ofNat 64 (8 * b)

/-- The registers the loop writes. -/
def loopRegs : List Reg := [.a1, .a2, .a3, .a4, .a5, .a6, .t0, .t1, .t2, .t3, .t4, .t5, .t6]

/-- The loop's fixed facts, about the state `s₀` before it: the schedule at
`S` (the frame) and the `n` blocks at `D`. -/
structure LoopEnv (S D : Addr) (n : Nat) (s₀ : State) : Prop where
  a7 : s₀.gpr .a7 = S
  al : S.toNat % 4 = 0
  al8 : S.toNat % 8 = 0
  key : ∀ o, o % 4 = 0 → o + 4 ≤ 4168 → InRegions (s₀.rd ++ s₀.wr) (S + BitVec.ofNat 64 o) 4
  key8 : ∀ o, o % 8 = 0 → o + 8 ≤ 4168 → InRegions (s₀.rd ++ s₀.wr) (S + BitVec.ofNat 64 o) 8
  data : (⟨D, 8 * n⟩ : Region) ∈ s₀.wr
  keyData : (⟨S, 4168⟩ : Region).Disjoint ⟨D, 8 * n⟩
  fit : D.toNat + 8 * n ≤ 2 ^ 64

/-- After `k` blocks. -/
structure EInv (S D : Addr) (n : Nat) (up : Bool) (s₀ : State) (k : Nat) (u : State) : Prop where
  le : k ≤ n
  ptr : u.gpr .a1 = wAt D k
  cnt : u.gpr .a2 = BitVec.ofNat 64 (n - k)
  keep : Keep loopRegs s₀ u
  done : ∀ b < k, blockAt u.mem (wAt D b) = blockOut (scheduleAt s₀.mem S) up (blockAt s₀.mem (wAt D b))
  rest : ∀ b, k ≤ b → b < n → blockAt u.mem (wAt D b) = blockAt s₀.mem (wAt D b)
  frame : Frame [⟨D, 8 * n⟩] s₀.mem u.mem

theorem ecb_step {S D : Addr} {n : Nat} {up : Bool} {s₀ : State} (L : LoopEnv S D n s₀) {k : Nat}
    (hk : k < n) {u : State} (I : EInv S D n up s₀ k u) :
    WP isa (.seq (.block loadBlock) (.seq (cipher up) (.block storeBlock))) u
      (fun u' => EInv S D n up s₀ (k + 1) u' ∧ u'.gpr .a2 = BitVec.ofNat 64 (n - (k + 1))) := by
  have fit := L.fit
  have hrd : u.rd ++ u.wr = s₀.rd ++ s₀.wr := by rw [I.keep.2.1, I.keep.2.2]
  have dR : (⟨D, 8 * n⟩ : Region) ∈ u.wr := by rw [I.keep.2.2]; exact L.data
  have inD : InRegions u.wr (wAt D k) 8 :=
    ⟨_, dR, Offset.contains_base D (by omega) (by omega)⟩
  have inD' : InRegions (u.rd ++ u.wr) (wAt D k) 8 :=
    let ⟨r, hr, hc⟩ := inD; ⟨r, List.mem_append_right _ hr, hc⟩
  apply WP.seq
  refine WP.mono (loadBlock_run u I.ptr inD') fun u₁ ⟨l₁, h₁, k₁, m₁⟩ => ?_
  have hK : scheduleAt u.mem S = scheduleAt s₀.mem S :=
    scheduleAt_eq_of_frame S I.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.keyData
  have Ku₁ : Keep loopRegs s₀ u₁ := (I.keep.trans k₁).mono (by decide)
  have E : LookEnv u₁ := by
    refine ⟨fun o ha ho => ?_, fun o ha ho => ?_, by rw [Ku₁.gpr (by decide), L.a7]; exact L.al,
      by rw [Ku₁.gpr (by decide), L.a7]; exact L.al8⟩
    · rw [Ku₁.gpr (by decide), L.a7, Ku₁.2.1, Ku₁.2.2]
      exact L.key o ha ho
    · rw [Ku₁.gpr (by decide), L.a7, Ku₁.2.1, Ku₁.2.2]
      exact L.key8 o ha ho
  apply WP.seq
  refine WP.mono (cipher_run E up) fun u₂ ⟨c₂, k₂, m₂⟩ => ?_
  have Ku₂ : Keep loopRegs s₀ u₂ := (Ku₁.trans k₂).mono (by decide)
  have wr₂ : u₂.wr = u.wr := by rw [k₂.2.2, k₁.2.2]
  have p₂ : u₂.gpr .a1 = wAt D k := by rw [k₂.gpr (by decide), k₁.gpr (by decide), I.ptr]
  refine WP.mono (storeBlock_run u₂ p₂ (by rw [wr₂]; exact inD)) fun u₃ ⟨m₃, p₃, c₃, k₃⟩ => ?_
  have subK : Region.Sub ⟨wAt D k, 8⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega)
  have hc₂ : u₂.gpr .a2 = BitVec.ofNat 64 (n - k) := by
    rw [k₂.gpr (by decide), k₁.gpr (by decide), I.cnt]
  have other : ∀ b, b < n → b ≠ k → blockAt u₃.mem (wAt D b) = blockAt u.mem (wAt D b) := fun b hb hne => by
    rw [m₃, blockAt_frame (stored_frame _ _ _ _) fun r hr => ?_, m₂, m₁]
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint D (by omega) (by omega) (by omega)
  have c₃' : u₃.gpr .a2 = BitVec.ofNat 64 (n - (k + 1)) := by
    rw [c₃, hc₂]; apply BitVec.eq_of_toNat_eq; simp; omega
  refine ⟨⟨by omega, ?_, c₃', (Ku₂.trans k₃).mono (by decide), fun b hb => ?_, fun b h1 h2 => ?_, ?_⟩, c₃'⟩
  · rw [p₃, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, wAt, wAt, Offset.add_add]
    congr 2
  · by_cases hbk : b = k
    · subst hbk
      have e1 := congrArg Prod.fst c₂
      have e2 := congrArg Prod.snd c₂
      simp only at e1 e2
      rw [m₃, stored_block, e1, e2, l₁, h₁, m₁, Ku₁.gpr (by decide), L.a7, hK, I.rest b (by omega) hk,
        blockOut_eq]
    · rw [other b (by omega) hbk]; exact I.done b (by omega)
  · rw [other b h2 (by omega)]; exact I.rest b (by omega) h2
  · rw [m₃]
    refine I.frame.trans ?_
    rw [← m₁, ← m₂]
    exact (stored_frame _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, subK⟩

theorem loop_run {S D : Addr} {n : Nat} {up : Bool} {s₀ : State} (L : LoopEnv S D n s₀) (hn : 0 < n)
    {u : State} (I : EInv S D n up s₀ 0 u) :
    WP isa (.loop (.seq (.block loadBlock) (.seq (cipher up) (.block storeBlock))) (.nonzero cnt)) u
      (EInv S D n up s₀ n) := by
  refine WP.loop (M := isa) (Q := EInv S D n up s₀ n)
    (fun m v => ∃ k, k < n ∧ m = n - k ∧ EInv S D n up s₀ k v) ?_ n u ⟨0, hn, rfl, I⟩
  intro m v ⟨k, hk, hm, J⟩
  refine WP.mono (ecb_step L hk J) fun v' ⟨J', hz⟩ => ?_
  have hn64 : n < 2 ^ 64 := by have := L.fit; omega
  rw [cnt, Steps.eval_nonzero, hz, ofNat_bne_zero' (by omega)]
  by_cases e : k + 1 = n
  · left
    exact ⟨by simp [e], e ▸ J'⟩
  · right
    exact ⟨by simp; omega, n - (k + 1), by omega, k + 1, by omega, rfl, J'⟩

/-! ## The function -/

/-- A schedule copied byte for byte. -/
theorem scheduleAt_copy {m m' : Mem} {p q : Addr}
    (h : ∀ i < 4168, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    scheduleAt m' q = scheduleAt m p := by
  apply Vector.ext; intro i hi
  simp only [scheduleAt, Vector.getElem_ofFn]
  split
  · rw [h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega)]
  · rw [h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega)]

/-- `Region.Disjoint` as `Mem.Sep`. -/
theorem sep_of_disjoint {r₁ r₂ : Region} (h : r₁.Disjoint r₂) : Mem.Sep r₁.base r₁.len r₂.base r₂.len :=
  fun x hx hy => h x (by simp only [Region.Contains]; omega) (by simp only [Region.Contains]; omega)

/-- What ECB may assume: the schedule readable, the `n` blocks writable,
apart from each other and from the 4176 bytes below the stack pointer, the
blocks not wrapping around. -/
structure EcbPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a0, 4168⟩]
  wr : s.wr = [⟨s.gpr .a1, 8 * (s.gpr .a2).toNat⟩]
  keyData : (⟨s.gpr .a0, 4168⟩ : Region).Disjoint ⟨s.gpr .a1, 8 * (s.gpr .a2).toNat⟩
  fit : (s.gpr .a1).toNat + 8 * (s.gpr .a2).toNat ≤ 2 ^ 64
  al : s.sp.toNat % 16 = 0
  sp : 4176 ≤ s.sp.toNat
  stackKey : (⟨s.sp - 4176, 4176⟩ : Region).Disjoint ⟨s.gpr .a0, 4168⟩
  stackData : (⟨s.sp - 4176, 4176⟩ : Region).Disjoint ⟨s.gpr .a1, 8 * (s.gpr .a2).toNat⟩

/-- The schedule's length, as `slli` builds it. -/
theorem shl_4168 : BitVec.ofNat 64 1042 <<< 2 = BitVec.ofNat 64 4168 := by decide

theorem ecb_wp (up : Bool) {s : State} (h : EcbPre s) :
    WP isa (Impl.Blowfish.RISCV64.ecb up) s fun s' => (∀ b < (s.gpr .a2).toNat,
      blockAt s'.mem (wAt (s.gpr .a1) b) =
        blockOut (scheduleAt s.mem (s.gpr .a0)) up (blockAt s.mem (wAt (s.gpr .a1) b))) ∧
      ((s.gpr .a2).toNat = 0 ∨ Zeroed (frameBase s) s'.mem) := by
  have fit := h.fit
  let D := s.gpr .a1
  let n := (s.gpr .a2).toNat
  have hF : (frameBase s) = s.sp - 4176 := frameBase_eq s
  have hFal : (frameBase s).toNat % 16 = 0 := frameBase_al s h.al h.sp
  unfold Impl.Blowfish.RISCV64.ecb
  refine WP.ite (s.gpr .a2 == 0) (by rw [cnt, Steps.eval_zero]) (fun hz => ?_) (fun hz => ?_)
  · have hn : (s.gpr .a2).toNat = 0 := by simp only [beq_iff_eq] at hz; simp [hz]
    exact WP.block_nil ⟨fun b hb => absurd hb (by omega), .inl hn⟩
  have hn : 0 < n := by
    have : s.gpr .a2 ≠ 0 := by simpa using hz
    have : (s.gpr .a2).toNat ≠ 0 := fun e => this (BitVec.eq_of_toNat_eq e)
    omega
  refine inFrame_wp h.sp ?_
  unfold ecbMain
  -- The frame, and the schedule's length.
  apply WP.seq
  refine WP.mono (WP.keep [.a7, .t0, .t4] (Q := fun t => t.gpr .a7 = (frameBase s) ∧ t.gpr .t0 = (frameBase s) ∧
      t.gpr .t4 = BitVec.ofNat 64 4168 ∧ t.mem = s.mem) (by
    unfold li4168
    brun [inner_sp, inner_mem, shl_4168]
    all_goals rfl) (by decide) rfl) fun a ⟨⟨a7, a0, a4, am⟩, ak⟩ => ?_
  have ag : ∀ r, r ∉ [Reg.a7, .t0, .t4] → a.gpr r = s.gpr r := fun r hr => ak.gpr hr
  have ard : a.rd = s.rd := ak.2.1
  have awr : a.wr = (inner s).wr := ak.2.2
  -- The schedule copied into the frame.
  apply WP.seq
  refine WP.mono (copyLoop_ok (tmp := .t1) (src := .a0) (dst := .t0) (cnt := .t4) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) a (N := 4168) (by decide) (by decide) a4
    (fun i hi => ⟨⟨s.gpr .a0, 4168⟩, by rw [ard, h.rd]; simp,
      by rw [ag _ (by decide)]; exact Offset.contains_base _ (by omega) (by omega)⟩)
    (fun i hi => by rw [awr, a0]; exact frame_in s (by omega) (by omega))
    (by
      rw [a0, ag _ (by decide)]
      intro x hx hy
      have hx' : (x - (s.sp - BitVec.ofNat 64 4176)).toNat < 4176 := by rw [← frameBase_eq]; omega
      exact sep_of_disjoint h.stackKey x hx' hy))
    fun c ⟨cc, cf, ck⟩ => ?_
  rw [a0, ag .a0 (by decide), am] at cc
  rw [a0, am] at cf
  have cg : ∀ r, r ∉ [Reg.t1, .a0, .t0, .t4] → r ∉ [Reg.a7, .t0, .t4] → c.gpr r = s.gpr r :=
    fun r h1 h2 => (ck.gpr h1).trans (ag r h2)
  have c7 : c.gpr .a7 = (frameBase s) := (ck.gpr (by decide)).trans a7
  have cwr : c.wr = (inner s).wr := ck.2.2.trans awr
  have crd : c.rd = s.rd := ck.2.1.trans ard
  have hdata : ∀ b < n, blockAt c.mem (wAt D b) = blockAt s.mem (wAt D b) := fun b hb =>
    blockAt_frame cf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((h.stackData.sub_left (r₁' := ⟨(frameBase s), 4168⟩) (by rw [hF]; exact Region.sub_prefix (by decide))).sub_right
        (r₂' := ⟨wAt D b, 8⟩) (Offset.sub_base _ (by omega))).symm
  have hK : scheduleAt c.mem (frameBase s) = scheduleAt s.mem (s.gpr .a0) := scheduleAt_copy cc
  -- The blocks.
  have L : LoopEnv (frameBase s) D n c := by
    refine ⟨c7, by omega, by omega, fun o ha ho => ?_, fun o ha ho => ?_, ?_, ?_, fit⟩
    · obtain ⟨r, hr, hc⟩ := frame_in s (o := o) (n := 4) (by omega) (by omega)
      exact ⟨r, List.mem_append_right _ (by rw [cwr]; exact hr), hc⟩
    · obtain ⟨r, hr, hc⟩ := frame_in s (o := o) (n := 8) (by omega) (by omega)
      exact ⟨r, List.mem_append_right _ (by rw [cwr]; exact hr), hc⟩
    · rw [cwr, inner_wr, h.wr]; simp [D, n]
    · rw [hF]; exact h.stackData.sub_left (Region.sub_prefix (by decide))
  have I0 : EInv (frameBase s) D n up c 0 c :=
    ⟨by omega, by rw [cg .a1 (by decide) (by decide)]; simp [wAt, D],
      by rw [cg .a2 (by decide) (by decide)]; simp [n], Keep.refl _ _,
      fun b hb => absurd hb (by omega), fun _ _ _ => rfl, Frame.refl _ _⟩
  apply WP.seq
  refine WP.mono (loop_run L hn I0) fun e E => ?_
  -- The frame zeroed.
  have e7 : e.gpr .a7 = (frameBase s) := (E.keep.gpr (by decide)).trans c7
  have ewr : e.wr = (inner s).wr := E.keep.2.2.trans cwr
  unfold wipe
  apply WP.seq
  refine WP.mono (WP.keep [.t1, .t0, .t4] (Q := fun t => t.gpr .t0 = (frameBase s) ∧ t.gpr .t4 = BitVec.ofNat 64 522 ∧
      t.gpr .t1 = 0#64 ∧ t.mem = e.mem) (by brun [e7]) (by decide) rfl) fun f ⟨⟨f0, f4, f1, fm⟩, fk⟩ => ?_
  refine WP.mono (fillLoop_ok (v := .t1) (ptr := .t0) (cnt := .t4) (by decide) (by decide) (by decide) f
    (N := 522) (by decide) (by decide) f4 (by rw [f0]; omega)
    (fun i hi => by rw [fk.2.2, ewr, f0]; exact frame_in s (by omega) (by omega)))
    fun t ⟨tz, tf, _⟩ => ⟨fun b hb => ?_, .inr fun j hj => by rw [← f0, ← f1]; exact tz j hj⟩
  rw [f0, fm] at tf
  show blockAt t.mem (wAt D b) = _
  rw [blockAt_frame tf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((h.stackData.sub_left (r₁' := ⟨(frameBase s), 8 * 522⟩) (by rw [hF]; exact Region.sub_prefix (by decide))).sub_right
        (r₂' := ⟨wAt D b, 8⟩) (Offset.sub_base _ (by omega))).symm,
    E.done b hb, hK, hdata b hb]

end VG.Proof.Blowfish.RISCV64
