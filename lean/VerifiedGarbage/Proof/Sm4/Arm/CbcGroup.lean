module

public import VerifiedGarbage.Proof.Sm4.Arm.CbcFill
public import VerifiedGarbage.Spec.Sm4.Cbc
import VerifiedGarbage.Proof.Sm4.Arm.BatchCalls
import VerifiedGarbage.Proof.Sm4.Arm.BatchGroup
public import VerifiedGarbage.Proof.Sm4.Arm.PreparedBody
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.MdStream.Arm.Common
public import VerifiedGarbage.Proof.Sm4.Prepared

/-! # One batch of CBC decryption -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.CbcGroup
open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchXor VG.Proof.Sm4.Arm.BatchChain
open VG.Proof.Sm4.Arm.BatchGroup (blockAt_of_ecb table_frame count_wp difference_zero)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Sm4.Prepared (Holds)

def regions (B I D : BitVec 32) (g : Nat) : List Region :=
  [⟨State.addr B, 4 * slots⟩, ⟨counterAddr B, 16⟩, ⟨State.addr I, 16⟩, ⟨State.addr D, 16 * g⟩]

def prevBlock (m : Mem) (B D : BitVec 32) (k : Nat) : List Byte :=
  if k = 0 then bytesAt m (counterAddr B) 16 else bytesAt m (dataAddr D (k - 1)) 16

theorem decrypted_lane {K : Spec.Sm4.Schedule} {m m' : Mem} {B : BitVec 32}
    (h : Spec.Sm4.blocksAt m' (State.addr B + BitVec.ofNat 64 layout.buf) layout.blocks =
      Spec.Sm4.ecb K .decrypt (Spec.Sm4.blocksAt m (State.addr B + BitVec.ofNat 64 layout.buf) layout.blocks))
    {j : Nat} (hj : j < 8) :
    bytesAt m' (bufferAddr B j) 16 = Spec.Sm4.invCipher K (bytesAt m (bufferAddr B j) 16) := by
  have hb := blockAt_of_ecb h hj
  have ha : State.addr B + BitVec.ofNat 64 layout.buf + BitVec.ofNat 64 (16 * j) = bufferAddr B j := by
    rw [Offset.add_add]; rfl
  rw [ha] at hb
  rw [Proof.Sm4.bytesAt_eq_blockAt, hb]
  rw [Spec.Sm4.invCipher, Proof.Sm4.bytesAt_eq_blockAt, Proof.Sm4.ofFn_toList]
  rfl

structure BatchPost (s : State) (B I D : BitVec 32) (K : Spec.Sm4.Schedule) (g : Nat) (s' : State) : Prop where
  regs : ∀ r ∈ [.r4, .r5, .r6, .r7, .r8, .r11], s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame (regions B I D g) s.mem s'.mem
  table : Holds layout s'.mem (State.addr B) K .decrypt
  counter : bytesAt s'.mem (counterAddr B) 16 = bytesAt s.mem (dataAddr D (g - 1)) 16
  blocks : ∀ k < g, bytesAt s'.mem (dataAddr D k) 16 =
    Spec.Cbc.xor (Spec.Sm4.invCipher K (bytesAt s.mem (dataAddr D k) 16)) (prevBlock s.mem B D k)

def batch : Prog isa := .seq BatchCbc.fill
  (.seq BatchCtr.crypt (.seq (BatchCbc.chooseXor 0 8) (.block BatchCtr.copyCounterIn)))

theorem batch_wp {s : State} {B I D : BitVec 32} {K : Spec.Sm4.Schedule} {g : Nat}
    (h : CbcFill.Pre B I D g s) (hg : 1 ≤ g) (hg8 : g ≤ 8)
    (hH : Holds layout s.mem (State.addr B) K .decrypt) : WP isa batch s (BatchPost s B I D K g) := by
  refine WP.seq (WP.mono (CbcFill.fill_wp h hg hg8) fun s₁ f => ?_)
  have p₁ := f.toInv.pre h
  have hH₁ : Holds layout s₁.mem (State.addr B) K .decrypt := table_frame hH f.kept.frame fun r hr => by
    simp only [CbcFill.regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
    · exact h.ib.symm.sub_left (Offset.sub_base _ (by decide))
  have counter₁ : bytesAt s₁.mem (counterAddr B) 16 = bytesAt s.mem (counterAddr B) 16 := by
    apply bytes_frame f.kept.frame
    intro r hr
    simp only [CbcFill.regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
    · exact h.ib.symm.sub_left CfbFill.counter_frame
  have wc : Covers [⟨State.addr B, 4 * slots⟩] s₁.wr := by
    rw [f.kept.wr]
    simpa only [BitVec.add_zero] using workspace_part h.core.hw 0 (4 * slots) (by decide)
  refine WP.seq (WP.mono (BatchCalls.crypt_wp p₁.core.base
    (by have := h.core.fitB; change B.toNat + 1456 ≤ 2 ^ 32; change B.toNat + 1512 ≤ 2 ^ 32 at this; omega)
    wc hH₁) fun s₂ ⟨c, table₂, ecb₂⟩ => ?_)
  have p₂ : CbcFill.Pre B I D g s₂ := ⟨⟨(c.regs _ (by decide) (by decide)).trans p₁.core.base,
    (c.regs _ (by decide) (by decide)).trans p₁.core.data, (c.regs _ (by decide) (by decide)).trans p₁.core.group,
    h.core.fitB, h.core.fitD, by rw [c.wr]; exact p₁.core.hw, by rw [c.wr]; exact p₁.core.wd, h.core.sep⟩,
    (c.regs _ (by decide) (by decide)).trans p₁.iv, h.fitI, by rw [c.wr]; exact p₁.hi, h.id, h.ib⟩
  have iv₂ : bytesAt s₂.mem (State.addr I) 16 = bytesAt s.mem (dataAddr D (g - 1)) 16 := by
    rw [bytes_frame (P := State.addr I) c.frame (fun r hr => ?_), f.iv]
    simp only [List.mem_singleton] at hr; subst hr
    exact h.ib.sub_right (Region.sub_prefix (by decide))
  have data₂ : ∀ k < g, bytesAt s₂.mem (dataAddr D k) 16 = bytesAt s.mem (dataAddr D k) 16 := by
    intro k hk
    rw [bytes_frame (P := dataAddr D k) c.frame (fun r hr => ?_), f.toInv.data_kept h hk]
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.core.sep.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix (by decide))
  have counter₂ : bytesAt s₂.mem (counterAddr B) 16 = bytesAt s.mem (counterAddr B) 16 := by
    rw [bytes_frame (P := counterAddr B) c.frame (fun r hr => ?_), counter₁]
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_base _ (by decide) (by decide)
  have plain₂ : ∀ k < g, bytesAt s₂.mem (bufferAddr B k) 16 = Spec.Sm4.invCipher K (bytesAt s.mem (dataAddr D k) 16) := by
    intro k hk
    rw [decrypted_lane ecb₂ (by omega), f.lanes k hk]
  refine WP.seq (WP.mono (CbcReverse.xor_wp p₂.core hg hg8) fun s₃ ⟨x, blocks⟩ => ?_)
  have p₃ : ChainPre s₃ B I := ⟨(x.regs _ (by decide) (by decide)).trans p₂.core.base,
    (x.regs _ (by decide) (by decide)).trans p₂.iv, h.core.fitB, h.fitI,
    by rw [x.wr]; exact p₂.core.hw, by rw [x.wr]; exact p₂.hi, h.ib⟩
  have iv₃ : bytesAt s₃.mem (State.addr I) 16 = bytesAt s.mem (dataAddr D (g - 1)) 16 := by
    rw [bytes_frame (P := State.addr I) x.frame (fun r hr => ?_), iv₂]
    simp only [List.mem_singleton] at hr; subst hr
    exact h.id
  have table₃ := table_frame table₂ x.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.core.sep.symm.sub_left (Offset.sub_base _ (by decide)))
  refine WP.mono (counterIn_wp p₃) fun s₄ v => ?_
  have ff : Frame (regions B I D g) s.mem s₁.mem := f.kept.frame.sub fun r hr => by
    simp only [CbcFill.regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨State.addr B, 4 * slots⟩, List.mem_cons_self, Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr I, 16⟩, by simp [regions], fun _ h => h⟩
  have fc : Frame (regions B I D g) s₁.mem s₂.mem := c.frame.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self
  have fx : Frame (regions B I D g) s₂.mem s₃.mem := x.frame.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [regions]
  have fv : Frame (regions B I D g) s₃.mem s₄.mem := v.frame.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [regions]
  refine ⟨?_, v.rd.trans (x.rd.trans (c.rd.trans f.kept.rd)), v.wr.trans (x.wr.trans (c.wr.trans f.kept.wr)),
    v.sp.trans (x.sp.trans (c.sp.trans f.kept.sp)), ((ff.trans fc).trans fx).trans fv, ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [v.regs _ (by decide) (by decide), x.regs _ (by decide) (by decide), c.regs _ (by decide) (by decide), f.kept.regs _ (by decide) (by decide)]
  · exact table_frame table₃ v.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide))
  · rw [v.block, iv₃]
  · intro k hk
    rw [bytes_frame (P := dataAddr D k) v.frame (fun r hr => ?_), blocks k hk]
    unfold CbcReverse.outBlock
    rw [plain₂ k hk]
    by_cases he : k = 0
    · simp only [CbcReverse.prevAddr, prevBlock, he, ↓reduceIte]
      rw [counter₂]
    · simp only [CbcReverse.prevAddr, prevBlock, he, ↓reduceIte]
      rw [data₂ (k - 1) (by omega)]
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.core.sep.sub_left (Offset.sub_base _ (by omega))).sub_right CfbFill.counter_frame

structure Pre (B I D : BitVec 32) (n : Nat) (s : State) : Prop where
  base : s.gpr sb = B
  iv : s.gpr .r5 = I
  data : s.gpr .r6 = D
  left : s.gpr .r7 = BitVec.ofNat 32 n
  fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32
  fitI : I.toNat + 16 ≤ 2 ^ 32
  fitD : D.toNat + 16 * n ≤ 2 ^ 32
  hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr
  hi : Covers [⟨State.addr I, 16⟩] s.wr
  wd : Covers [⟨State.addr D, 16 * n⟩] s.wr
  id : Region.Disjoint ⟨State.addr I, 16⟩ ⟨State.addr D, 16 * n⟩
  ib : Region.Disjoint ⟨State.addr I, 16⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩
  db : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩

structure GroupPost (s : State) (B I D : BitVec 32) (K : Spec.Sm4.Schedule) (n : Nat) (s' : State) : Prop where
  regs : ∀ r ∈ [.r4, .r5, .r8], s'.gpr r = s.gpr r
  data : s'.gpr .r6 = D + BitVec.ofNat 32 (16 * min n 8)
  left : s'.gpr .r7 = BitVec.ofNat 32 (n - min n 8)
  z : s'.z = decide (n = min n 8)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame (regions B I D (min n 8)) s.mem s'.mem
  table : Holds layout s'.mem (State.addr B) K .decrypt
  counter : bytesAt s'.mem (counterAddr B) 16 = bytesAt s.mem (dataAddr D (min n 8 - 1)) 16
  blocks : ∀ k < min n 8, bytesAt s'.mem (dataAddr D k) 16 =
    Spec.Cbc.xor (Spec.Sm4.invCipher K (bytesAt s.mem (dataAddr D k) 16)) (prevBlock s.mem B D k)

theorem shift_group (g : Nat) : (BitVec.ofNat 32 g <<< 4) = BitVec.ofNat 32 (16 * g) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 32 g * BitVec.ofNat 32 16 = _
  rw [← BitVec.ofNat_mul, Nat.mul_comm]

theorem group_wp {s : State} {B I D : BitVec 32} {K : Spec.Sm4.Schedule} {n : Nat}
    (h : Pre B I D n s) (hn : 1 ≤ n) (hn32 : n < 2 ^ 32)
    (hH : Holds layout s.mem (State.addr B) K .decrypt) : WP isa BatchCbc.group s (GroupPost s B I D K n) := by
  have hgN : min n 8 ≤ n := Nat.min_le_left _ _
  have hg8 : min n 8 ≤ 8 := Nat.min_le_right _ _
  have hg : 1 ≤ min n 8 := by omega
  refine WP.seq (WP.mono (count_wp h.left hn32) fun s₁ ⟨g₁, o₁, m₁, rd₁, wr₁, sp₁⟩ => ?_)
  have wd₁ : Covers [⟨State.addr D, 16 * min n 8⟩] s₁.wr := by
    rw [wr₁]
    apply Covers.trans (rs' := [⟨State.addr D, 16 * n⟩]) _ h.wd
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr D, 16 * n⟩, List.mem_singleton_self _, 0, by rw [BitVec.add_zero], by change 0 + 16 * min n 8 ≤ 16 * n; omega⟩
  have fp : CbcFill.Pre B I D (min n 8) s₁ := ⟨⟨(o₁ _ (by decide) (by decide)).trans h.base,
    (o₁ _ (by decide) (by decide)).trans h.data, g₁, h.fitB, by have := h.fitD; omega,
    by rw [wr₁]; exact h.hw, wd₁, h.db.sub_left (Region.sub_prefix (by omega))⟩,
    (o₁ _ (by decide) (by decide)).trans h.iv, h.fitI, by rw [wr₁]; exact h.hi,
    h.id.sub_right (Region.sub_prefix (by omega)), h.ib⟩
  refine WP.seq (WP.mono (batch_wp fp hg hg8 (by rw [m₁]; exact hH)) fun s₂ b => ?_)
  have d₂ : s₂.gpr .r6 = D := (b.regs _ (by simp)).trans fp.core.data
  have n₂ : s₂.gpr .r7 = BitVec.ofNat 32 n := (b.regs _ (by simp)).trans ((o₁ _ (by decide) (by decide)).trans h.left)
  have g₂ : s₂.gpr .r11 = BitVec.ofNat 32 (min n 8) := (b.regs _ (by simp)).trans g₁
  refine Proof.MdStream.Arm.wp_mov (show Op2.eval s₂ (.shifted .r11 .lsl 4) = some (s₂.gpr .r11 <<< 4) from rfl) fun s₃ u₃ => ?_
  refine Proof.MdStream.Arm.wp_add (Proof.MdStream.Arm.op2_reg s₃ .r0) fun s₄ u₄ => ?_
  refine Proof.MdStream.Arm.wp_subs (Proof.MdStream.Arm.op2_reg s₄ .r11) fun s₅ u₅ hz => ?_
  refine WP.block_nil ⟨?_, ?_, ?_, ?_, u₅.rd.trans (u₄.rd.trans (u₃.rd.trans (b.rd.trans rd₁))),
    u₅.wr.trans (u₄.wr.trans (u₃.wr.trans (b.wr.trans wr₁))), u₅.sp.trans (u₄.sp.trans (u₃.sp.trans (b.sp.trans sp₁))), ?_, ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), b.regs _ (by simp), o₁ _ (by decide) (by decide)]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), d₂, u₃.gpr, g₂, shift_group]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), n₂,
      u₄.other _ (by decide), u₃.other _ (by decide), g₂]
    exact Offset.ofNat_sub_ofNat hgN
  · rw [hz, u₄.other _ (by decide), u₃.other _ (by decide), n₂,
      u₄.other _ (by decide), u₃.other _ (by decide), g₂]
    exact difference_zero hn32 hgN
  · rw [u₅.mem, u₄.mem, u₃.mem, ← m₁]; exact b.frame
  · rw [u₅.mem, u₄.mem, u₃.mem]; exact b.table
  · rw [u₅.mem, u₄.mem, u₃.mem, b.counter, m₁]
  · intro k hk
    rw [u₅.mem, u₄.mem, u₃.mem, b.blocks k hk, m₁]

end VG.Proof.Sm4.Arm.CbcGroup
