module
public import VerifiedGarbage.Proof.CmacTripleDes.Stream
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.Arm.Contract
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.Arm.Inline

import VerifiedGarbage.Proof.CmacTripleDes.Stream.Arm.Common
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.CmacTripleDes.Words
import VerifiedGarbage.Proof.CmacTripleDes.Arm.Update
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.CmacTripleDes.Arm.Finalize
import VerifiedGarbage.Proof.CmacTripleDes.Arm.FinalizeCorrect
import VerifiedGarbage.Proof.CmacTripleDes.Arm.Init
import VerifiedGarbage.Proof.CmacTripleDes.InlineCT
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Aes.Blocks
meta import VerifiedGarbage.Proof.Cmac.Block
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Cmac.Stream
meta import VerifiedGarbage.Proof.CmacTripleDes.Arm.Finalize
meta import VerifiedGarbage.Proof.CmacTripleDes.Arm.FinalizeCorrect
meta import VerifiedGarbage.Proof.CmacTripleDes.Arm.Init
meta import VerifiedGarbage.Proof.CmacTripleDes.Arm.Update
meta import VerifiedGarbage.Proof.CmacTripleDes.InlineCT
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.Arm.Inline
meta import VerifiedGarbage.Proof.CmacTripleDes.Words
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.CallF
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha256.Stream

/-!
# Streaming TDEA-CMAC on ARMv7: `vg_cmac_triple_des_finish`

The code copies the chaining value to `out`, computes the number of bytes
held back, and runs `finalize` with the state as its key and `out` as its
state: its result is the MAC of the message the state represents
(`repr_finish`). The code before `finalize` is constant time by the taint
analysis, and `finalize` by its own proof (`fin_rel`), its arguments pinned
by `HMid`.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.Arm

open VG VG.Arm VG.Impl.CmacTripleDes.Stream.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_add wp_sub wp_and wp_orr wp_cmp wp_ldr
  wp_str wp_ldrSp)
open VG.Proof.CmacTripleDes.Stream (held held_le held_zero)

/-- The precondition, by name: the state `St`, `out` (`O`) and the scratch
buffer `S`. -/
structure HPre (s₀ : State) (St O S : BitVec 32) : Prop where
  r0 : s₀.gpr .r0 = St
  a0 : stackArg s₀ 0 = O
  a1 : stackArg s₀ 1 = S
  rd : s₀.rd = [⟨stackArgAddr s₀ 0, 8⟩]
  wr : s₀.wr = [⟨State.addr St, 416⟩, ⟨State.addr O, 8⟩, ⟨State.addr S, 640⟩]
  st_o : (⟨State.addr St, 416⟩ : Region).Disjoint ⟨State.addr O, 8⟩
  st_s : (⟨State.addr St, 416⟩ : Region).Disjoint ⟨State.addr S, 640⟩
  o_s : (⟨State.addr O, 8⟩ : Region).Disjoint ⟨State.addr S, 640⟩
  a_st : (⟨stackArgAddr s₀ 0, 8⟩ : Region).Disjoint ⟨State.addr St, 416⟩
  a_o : (⟨stackArgAddr s₀ 0, 8⟩ : Region).Disjoint ⟨State.addr O, 8⟩
  a_s : (⟨stackArgAddr s₀ 0, 8⟩ : Region).Disjoint ⟨State.addr S, 640⟩
  b_st : (blw4 s₀).Disjoint ⟨State.addr St, 416⟩
  b_o : (blw4 s₀).Disjoint ⟨State.addr O, 8⟩
  b_s : (blw4 s₀).Disjoint ⟨State.addr S, 640⟩
  fSt : St.toNat + 416 ≤ 2 ^ 32
  fO : O.toNat + 8 ≤ 2 ^ 32
  fS : S.toNat + 640 ≤ 2 ^ 32
  sp : 4 ≤ s₀.sp.toNat
  spf : s₀.sp.toNat + 8 ≤ 2 ^ 32

theorem HPre.of {s₀ : State} (h : finishArm.pre s₀) :
    HPre s₀ (s₀.gpr .r0) (stackArg s₀ 0) (stackArg s₀ 1) :=
  let ⟨a, b, c, d, e, f, g, i, j, k, l, m, n, o, p, q⟩ := h
  ⟨rfl, rfl, rfl, a, b, c, d, e, f, g, i, j, k, l, m, n, o, p, q⟩

/-! ## Arguments on the stack -/

theorem arg1_eq {s : State} (h : s.sp.toNat + 8 ≤ 2 ^ 32) :
    stackArgAddr s 1 = stackArgAddr s 0 + BitVec.ofNat 64 4 := by
  simp only [stackArgAddr]
  rw [addr_add (by omega), addr_add (by omega)]
  simp

theorem arg_in {s : State} (h : s.sp.toNat + 8 ≤ 2 ^ 32) {rs : List Region} (hr : ⟨stackArgAddr s 0, 8⟩ ∈ rs)
    {k : Nat} (hk : k < 2) : InRegions rs (stackArgAddr s k) 4 := by
  refine ⟨_, hr, ?_⟩
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · simpa using Offset.contains_base (stackArgAddr s 0) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
  · rw [arg1_eq h]; exact Offset.contains_base _ (by decide) (by decide)

/-! ## The chaining value, copied to `out` -/

/-- The memory after copying the block at `p` to `o`, a word at a time. -/
def cvMem (m : Mem) (o p : Addr) : Mem :=
  (m.writeW o (m.readW p 32)).writeW (o + BitVec.ofNat 64 4) (m.readW (p + BitVec.ofNat 64 4) 32)

theorem cvMem_bytes (m : Mem) (o p : Addr) : Spec.Aes.bytesAt (cvMem m o p) o 8 = Spec.Aes.bytesAt m p 8 := by
  rw [cvMem, ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW, Proof.CmacTripleDes.readW64_split,
    Mem.readW_writeW_self32, Proof.CmacTripleDes.Arm.readW_lo_of_hi, ← Proof.CmacTripleDes.readW64_split]

theorem cvMem_frame (m : Mem) (o p : Addr) : Frame [⟨o, 8⟩] m (cvMem m o p) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
    simpa using Offset.contains_base o (d := 0) (n := 4) (k := 8) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base o (d := 4) (n := 4) (k := 8) (by decide) (by decide))

/-! ## Before `finalize` -/

/-- What the block before `lastLen` leaves. -/
structure HBlk (s₀ : State) (St O S : BitVec 32) (s : State) : Prop where
  r0 : s.gpr .r0 = St
  r1 : s.gpr .r1 = O
  r2 : s.gpr .r2 = St + BitVec.ofNat 32 408
  r3 : s.gpr .r3 = ((s₀.gpr .r2 - 1) &&& 7) + 1
  z : s.z = ((s₀.gpr .r2 ||| s₀.gpr .r3) - 0 == 0)
  mem : s.mem = cvMem s₀.mem (State.addr O) (State.addr St + BitVec.ofNat 64 400)
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r ∈ preserved, s.gpr r = s₀.gpr r

theorem finishPre_wp {s₀ : State} {St O S : BitVec 32} (hp : HPre s₀ St O S) :
    WP isa (.block finishPre) s₀ (HBlk s₀ St O S) := by
  have hSt := hp.fSt
  have hO := hp.fO
  have aO : State.addr (O + BitVec.ofNat 32 0) = State.addr O := by rw [BitVec.add_zero]
  have aO4 : State.addr (O + BitVec.ofNat 32 4) = State.addr O + BitVec.ofNat 64 4 := addr_add (by omega)
  have a400 : State.addr (St + BitVec.ofNat 32 400) = State.addr St + BitVec.ofNat 64 400 := addr_add (by omega)
  have a404 : State.addr (St + BitVec.ofNat 32 404) = State.addr St + BitVec.ofNat 64 400 + BitVec.ofNat 64 4 := by
    rw [Offset.add_add]; exact addr_add (by omega)
  have inSt (d : Nat) (hd : d + 4 ≤ 416) :
      InRegions (s₀.rd ++ s₀.wr) (State.addr St + BitVec.ofNat 64 d) 4 := by
    rw [hp.rd, hp.wr]; exact ⟨⟨State.addr St, 416⟩, by simp, Offset.contains_base _ hd (by omega)⟩
  have inO (d : Nat) (hd : d + 4 ≤ 8) : InRegions s₀.wr (State.addr O + BitVec.ofNat 64 d) 4 := by
    rw [hp.wr]; exact ⟨⟨State.addr O, 8⟩, by simp, Offset.contains_base _ hd (by omega)⟩
  have dW : (⟨State.addr O, 4⟩ : Region).Disjoint ⟨State.addr St + BitVec.ofNat 64 400 + BitVec.ofNat 64 4, 4⟩ := by
    rw [Offset.add_add]
    exact (hp.st_o.sub_left (Offset.sub_base _ (by decide))).symm.sub_left (Region.sub_prefix (by decide))
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) rfl
    (arg_in hp.spf (by rw [hp.rd]; simp) (by decide)) fun s₁ u₁ => ?_
  have h1 : s₁.gpr .r1 = O := by rw [u₁.gpr]; exact hp.a0
  refine wp_ldr (a := State.addr St + BitVec.ofNat 64 400) (by decide)
    (by rw [u₁.other _ (by decide), hp.r0, a400]) (by rw [u₁.rd, u₁.wr]; exact inSt 400 (by decide))
    fun s₂ u₂ => ?_
  refine wp_str (a := State.addr O) (by decide) (by rw [u₂.other _ (by decide), h1, aO])
    (by rw [u₂.wr, u₁.wr]; simpa using inO 0 (by decide)) fun s₃ v₃ => ?_
  refine wp_ldr (a := State.addr St + BitVec.ofNat 64 400 + BitVec.ofNat 64 4) (by decide)
    (by rw [v₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hp.r0, a404])
    (by rw [v₃.rd, v₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, Offset.add_add]; exact inSt 404 (by decide)) fun s₄ u₄ => ?_
  refine wp_str (a := State.addr O + BitVec.ofNat 64 4) (by decide)
    (by rw [u₄.other _ (by decide), v₃.gpr, u₂.other _ (by decide), h1, aO4])
    (by rw [u₄.wr, v₃.wr, u₂.wr, u₁.wr]; exact inO 4 (by decide)) fun s₅ v₅ => ?_
  refine wp_orr (op2_reg _ _) fun s₆ u₆ => wp_sub (op2_imm (by decide)) fun s₇ u₇ =>
    wp_and (op2_imm (by decide)) fun s₈ u₈ => wp_add (op2_imm (by decide)) fun s₉ u₉ =>
    wp_add (op2_imm (by decide)) fun s₁₀ u₁₀ => wp_cmp (op2_imm (by decide)) fun s₁₁ f₁₁ z₁₁ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s₁₁.gpr r = s₀.gpr r := fun r a b c d => by
    rw [f₁₁.gpr, u₁₀.other _ b, u₉.other _ c, u₈.other _ c, u₇.other _ c, u₆.other _ d, v₅.gpr,
      u₄.other _ d, v₃.gpr, u₂.other _ d, u₁.other _ a]
  have m₁₁ : s₁₁.mem = cvMem s₀.mem (State.addr O) (State.addr St + BitVec.ofNat 64 400) := by
    rw [f₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, v₅.mem, u₄.gpr, u₄.mem, v₃.mem, u₂.gpr,
      u₂.mem, u₁.mem, cvMem,
      Mem.readW_writeW_sep (dW.symm.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)]
  refine ⟨by rw [g .r0 (by decide) (by decide) (by decide) (by decide)]; exact hp.r0, ?_, ?_, ?_, ?_, m₁₁,
    ?_, ?_, ?_, fun r hr => ?_⟩
  · rw [f₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.other _ (by decide), v₅.gpr, u₄.other _ (by decide), v₃.gpr, u₂.other _ (by decide),
      h1]
  · rw [f₁₁.gpr, u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.other _ (by decide), v₅.gpr, u₄.other _ (by decide), v₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hp.r0]; rfl
  · rw [f₁₁.gpr, u₁₀.other _ (by decide), u₉.gpr, u₈.gpr, u₇.gpr, u₆.other _ (by decide),
      v₅.gpr, u₄.other _ (by decide), v₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [z₁₁]
    simp (disch := decide) only [u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.gpr, v₅.gpr, u₄.other, v₃.gpr,
      u₂.other, u₁.other]
  · rw [f₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, v₅.sp, u₄.sp, v₃.sp, u₂.sp, u₁.sp]
  · rw [f₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, v₅.rd, u₄.rd, v₃.rd, u₂.rd, u₁.rd]
  · rw [f₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, v₅.wr, u₄.wr, v₃.wr, u₂.wr, u₁.wr]
  · have : r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact g r this.1 this.2.1 this.2.2.1 this.2.2.2

/-- What the code before `finalize` leaves. -/
structure HMid (s₀ : State) (St O S : BitVec 32) (s : State) : Prop where
  args : FArgs s St O (St + BitVec.ofNat 32 408) S (held (countArm s₀).toNat)
  mem : s.mem = cvMem s₀.mem (State.addr O) (State.addr St + BitVec.ofNat 64 400)
  keep : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem HPre.aL {s₀ : State} {St O S : BitVec 32} (hp : HPre s₀ St O S) :
    State.addr (St + BitVec.ofNat 32 408) = State.addr St + BitVec.ofNat 64 408 := addr_add (by have := hp.fSt; omega)

theorem HPre.fargs {s₀ s : State} {St O S : BitVec 32} {L : Nat} (hp : HPre s₀ St O S) (hL : L ≤ 8)
    (r0 : s.gpr .r0 = St) (r1 : s.gpr .r1 = O) (r2 : s.gpr .r2 = St + BitVec.ofNat 32 408)
    (r3 : s.gpr .r3 = BitVec.ofNat 32 L) (r12 : s.gpr .r12 = S)
    (sp : s.sp = s₀.sp) (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) :
    FArgs s St O (St + BitVec.ofNat 32 408) S L := by
  have hw := hp.fSt
  have pSt : Region.Sub ⟨State.addr (St + BitVec.ofNat 32 408), L⟩ ⟨State.addr St, 416⟩ := by
    rw [hp.aL]; exact Offset.sub_base _ (by omega)
  have hb : blw4 s = blw4 s₀ := by rw [blw4, sp]
  exact
  { r0 := r0, r1 := r1, r2 := r2, r3 := r3, r12 := r12, len := hL
    hsp := by rw [sp]; exact hp.sp
    kst := hp.st_o.sub_left (Region.sub_prefix (by decide))
    ks := hp.st_s.sub_left (Region.sub_prefix (by decide))
    pst := hp.st_o.sub_left pSt
    ps := hp.st_s.sub_left pSt
    sts := hp.o_s
    bk := by rw [hb]; exact hp.b_st.sub_right (Region.sub_prefix (by decide))
    bp := by rw [hb]; exact hp.b_st.sub_right pSt
    bst := by rw [hb]; exact hp.b_o
    bs := by rw [hb]; exact hp.b_s
    fK := by omega
    fSt := hp.fO
    fP := by rw [toNat_add_ofNat (by omega)]; omega
    fS := hp.fS
    reads := by
      rw [rd, wr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨State.addr St, 416⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
      · exact ⟨⟨State.addr St, 416⟩, by simp, 408, hp.aL, by simp; omega⟩
    writes := by
      rw [wr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨State.addr O, 8⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
      · exact ⟨⟨State.addr S, 640⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩ }

theorem finPre_wp {s₀ : State} {St O S : BitVec 32} (hp : HPre s₀ St O S) :
    WP isa finPre s₀ (HMid s₀ St O S) := by
  refine WP.seq (WP.mono (finishPre_wp hp) fun s₁ h₁ => ?_)
  have hc := (countArm s₀).isLt
  have ev : isa.eval .eq s₁ = some (decide ((countArm s₀).toNat = 0)) := by
    show VG.Arm.eval .eq s₁ = _
    rw [VG.Proof.MdStream.Arm.eval_eq, h₁.z, or_beq_zero (count_eq s₀) hc]
  have tail : ∀ {t : State} {L : Nat}, L ≤ 8 → t.gpr .r3 = BitVec.ofNat 32 L → L = held (countArm s₀).toNat →
      (∀ r, r ≠ .r3 → t.gpr r = s₁.gpr r) → t.mem = s₁.mem → t.sp = s₁.sp → t.rd = s₁.rd → t.wr = s₁.wr →
      WP isa (.block finArgs) t (HMid s₀ St O S) := fun {t L} hL h3 hLe g m sp rd wr => by
    refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) (by rw [sp, h₁.sp]; rfl)
      (by rw [rd, wr, h₁.rd, h₁.wr]; exact arg_in hp.spf (by rw [hp.rd]; simp) (by decide))
      fun t₁ u₁ => WP.block_nil ?_
    have hS : t₁.gpr .r12 = S := by
      rw [u₁.gpr, m, h₁.mem, ← hp.a1]
      exact (cvMem_frame _ _ _).readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.a_o.sub_left (by rw [arg1_eq hp.spf]; exact Offset.sub_base _ (by decide))) (by decide)
    refine ⟨hLe ▸ hp.fargs hL (by rw [u₁.other _ (by decide), g _ (by decide), h₁.r0])
      (by rw [u₁.other _ (by decide), g _ (by decide), h₁.r1]) (by rw [u₁.other _ (by decide), g _ (by decide), h₁.r2])
      (by rw [u₁.other _ (by decide), h3]) hS (by rw [u₁.sp, sp, h₁.sp]) (by rw [u₁.rd, rd, h₁.rd])
      (by rw [u₁.wr, wr, h₁.wr]), by rw [u₁.mem, m, h₁.mem], fun r hr => ?_, by rw [u₁.sp, sp, h₁.sp],
      by rw [u₁.rd, rd, h₁.rd], by rw [u₁.wr, wr, h₁.wr]⟩
    have : r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [u₁.other _ this.2, g _ this.1, h₁.keep r hr]
  refine WP.seq ?_
  by_cases h0 : (countArm s₀).toNat = 0
  · refine WP.ite true (by rw [ev, h0]; rfl) (fun _ => ?_) (fun h => by cases h)
    refine wp_mov (op2_imm (by decide)) fun t u => WP.block_nil ?_
    exact tail (L := 0) (by decide) u.gpr (by rw [h0]; rfl) (fun r h => u.other r h) u.mem u.sp u.rd u.wr
  · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => WP.block_nil ?_
    refine tail (held_le _) ?_ rfl (fun _ _ => rfl) rfl rfl rfl rfl
    rw [h₁.r3]
    exact held_lo (count_eq s₀) hc h0

/-! ## The whole function -/

theorem finish_wp {s₀ : State} (h0 : finishArm.pre s₀) :
    WP isa finish s₀ fun s' => abiPreserved s₀ s' ∧ finishArm.post s₀ s' := by
  have hp := HPre.of h0
  generalize s₀.gpr .r0 = St at hp
  generalize stackArg s₀ 0 = O at hp
  generalize stackArg s₀ 1 = S at hp
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.mono (fin_wp h₁.args) fun s₂ h₂ => ?_
  have f₁ : Frame [⟨State.addr O, 8⟩] s₀.mem s₁.mem := by rw [h₁.mem]; exact cvMem_frame _ _ _
  refine ⟨⟨fun r hr => by rw [h₂.saved r hr, h₁.keep r hr], by rw [h₂.sp, h₁.sp]⟩, ?_⟩
  intro key msg hr hc hlen
  rw [hp.r0] at hr
  rw [hp.a0]
  have hr₁ : Spec.Cmac.tdesRepr s₁.mem (State.addr St) key msg :=
    Proof.CmacTripleDes.Stream.repr_congr_416 (fun i hi => f₁.bytes (R := ⟨State.addr St, 416⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.st_o) (by show 416 ≤ 2 ^ 64; decide) hi) hr
  obtain ⟨hm, hne, hst, happ⟩ := Proof.CmacTripleDes.Stream.repr_finish hr₁
  rw [Proof.CmacTripleDes.Stream.repr_iff] at hr₁
  obtain ⟨⟨_, hks, hsk⟩, -, -⟩ := hr₁
  have hn : (countArm s₀).toNat = msg.length := by rw [hc, toNat_ofNat64 hlen]
  have hciph : Proof.CmacTripleDes.Arm.ciphAt s₁.mem (State.addr St) = Spec.Cmac.tdes key := by
    simp only [Proof.CmacTripleDes.Arm.ciphAt, hks, Spec.Cmac.tdes]
  have e₂ : Spec.Aes.bytesAt s₁.mem (State.addr O) 8 = Spec.Aes.bytesAt s₁.mem (State.addr St + 400) 8 := by
    rw [h₁.mem, cvMem_bytes, show State.addr St + 400 = State.addr St + BitVec.ofNat 64 400 from rfl]
    exact (Proof.Cmac.bytesAt_frame (cvMem_frame _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_o.sub_left (Offset.sub_base _ (d := 400) (n := 8) (by decide))) (by decide)).symm
  have out := h₂.out (by rw [hciph]; exact hsk) _ hm (by rw [hn]; exact hne)
    (by rw [hciph, e₂]; exact hst)
  rw [out, hciph, hn, hp.aL, show State.addr St + BitVec.ofNat 64 408 = State.addr St + 408 from rfl, happ,
    Proof.CmacTripleDes.Stream.tdesCmac_eq]

/-! ## Constant time -/

/-- The stack arguments of a state satisfying the precondition, for the
taint analysis. -/
theorem HPre.wfA {s₀ : State} {St O S : BitVec 32} (hp : HPre s₀ St O S) :
    s₀.sp.toNat + 8 ≤ 2 ^ 32 ∧ ∀ r ∈ s₀.wr, Region.Disjoint ⟨State.addr s₀.sp, 8⟩ r := by
  have e : (⟨State.addr s₀.sp, 8⟩ : Region) = ⟨stackArgAddr s₀ 0, 8⟩ := by simp [stackArgAddr]
  refine ⟨hp.spf, ?_⟩
  rw [e, hp.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hp.a_st
  · exact hp.a_o
  · exact hp.a_s

theorem finish_rel {s₀ s₀' : State} (h0 : finishArm.pre s₀) (h0' : finishArm.pre s₀')
    (hq : finishArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') finish fun _ _ => True := by
  obtain ⟨q1, q2, q4, q5, q6, q7⟩ := hq
  have hp := HPre.of h0
  have hp' : HPre s₀' (s₀.gpr .r0) (stackArg s₀ 0) (stackArg s₀ 1) := by
    rw [q2, q6, q7]; exact HPre.of h0'
  have hc : (countArm s₀').toNat = (countArm s₀).toNat := by simp only [countArm, q4, q5]
  have wf := hp.wfA
  have wf' := hp'.wfA
  generalize s₀.gpr .r0 = St at hp hp'
  generalize stackArg s₀ 0 = O at hp hp'
  generalize stackArg s₀ 1 = S at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (argTaint [.r0, .r2, .r3] 8) finPre h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := HMid s₀ St O S)
    (G' := HMid s₀' St O S) (argTaint [.r0, .r2, .r3] 8)
    (fun s s' e e' => by
      subst e e'
      refine agree_argTaint (fun r hr => ?_) q1 wf wf' (argMem_of (j := 2) q1 hp.spf fun i hi => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        exacts [q2, q4, q5]
      · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · exact q6
        · exact q7) ⟨_, hA⟩
    (fun s e => by rw [e]; exact finPre_wp hp) (fun s e => by rw [e]; exact finPre_wp hp')
  have c := fin_rel (sp₀ := s₀.sp) (Pr := fun s s' => HMid s₀ St O S s ∧ HMid s₀' St O S s')
    fun _ _ h => ⟨h.1.args, by rw [← hc]; exact h.2.args, h.1.sp, h.2.sp.trans q1.symm⟩
  exact a.seq c

theorem finish_ct : ConstantTime isa finishArm.pre finishArm.pub finish :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (finish_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacTripleDes.Stream.Arm
