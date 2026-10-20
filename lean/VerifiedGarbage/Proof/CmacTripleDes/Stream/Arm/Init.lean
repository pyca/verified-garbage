module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.Arm.Contract
import VerifiedGarbage.Proof.CmacTripleDes.Arm.Lit
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.Arm
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.CmacTripleDes.Words
import VerifiedGarbage.Proof.CmacTripleDes.Stream.Arm.Inline
import VerifiedGarbage.Proof.CmacTripleDes.Arm.Update
import VerifiedGarbage.Proof.CmacTripleDes.Stream
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.Arm.Contract
meta import VerifiedGarbage.Proof.CmacTripleDes.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.CmacTripleDes.Stream.Arm
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.CmacTripleDes.Words
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.Arm.Inline
meta import VerifiedGarbage.Proof.CmacTripleDes.Arm.Update
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Streaming TDEA-CMAC on ARMv7: `vg_cmac_triple_des_stream_init`

The code zeroes the chaining value and runs `init` with the state as its
`out`, which writes the key schedule and the subkeys before it: the state
then represents the empty message. The taint analysis checks it whole, the
code of `init` too, from the public arguments, with `r0` pointing at the
state and `r3` at the scratch buffer (where `init` keeps its pointers).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.Arm

open VG VG.Arm VG.Impl.CmacTripleDes.Stream.Arm
open VG.Impl.CmacTripleDes.Arm (mov)
open VG.Proof.MdStream.Arm (Upd Mupd op2_imm op2_reg wp_mov wp_str addr_toNat)

/-- The precondition, by name: the state `St`, the key `Kp` of `KL` bytes
and the scratch buffer `S`. -/
structure IPre (s₀ : State) (St Kp S : BitVec 32) (KL : Nat) : Prop where
  r0 : s₀.gpr .r0 = St
  r1 : s₀.gpr .r1 = Kp
  r2 : (s₀.gpr .r2).toNat = KL
  r3 : s₀.gpr .r3 = S
  rd : s₀.rd = [⟨State.addr Kp, KL⟩]
  wr : s₀.wr = [⟨State.addr St, 416⟩, ⟨State.addr S, 640⟩]
  st_k : (⟨State.addr St, 416⟩ : Region).Disjoint ⟨State.addr Kp, KL⟩
  st_s : (⟨State.addr St, 416⟩ : Region).Disjoint ⟨State.addr S, 640⟩
  k_s : (⟨State.addr Kp, KL⟩ : Region).Disjoint ⟨State.addr S, 640⟩
  fSt : St.toNat + 416 ≤ 2 ^ 32
  fK : Kp.toNat + KL ≤ 2 ^ 32
  fS : S.toNat + 640 ≤ 2 ^ 32
  klen : Spec.TripleDes.validKey KL

theorem IPre.of {s₀ : State} (h : initArm.pre s₀) :
    IPre s₀ (s₀.gpr .r0) (s₀.gpr .r1) (s₀.gpr .r3) (s₀.gpr .r2).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i⟩

/-- The memory after zeroing the chaining value at `p`, a word at a time. -/
def zeroCv (m : Mem) (p : Addr) : Mem :=
  (m.writeW p (0 : BitVec 32)).writeW (p + BitVec.ofNat 64 4) (0 : BitVec 32)

theorem zeroCv_bytes (m : Mem) (p : Addr) : Spec.Aes.bytesAt (zeroCv m p) p 8 = Spec.Cmac.zeros 8 := by
  rw [zeroCv, ← Proof.Cmac.le8_readW, Proof.CmacTripleDes.readW64_split, Mem.readW_writeW_self32,
    Proof.CmacTripleDes.Arm.readW_lo_of_hi]
  decide

theorem zeroCv_frame (m : Mem) (p : Addr) : Frame [⟨p, 8⟩] m (zeroCv m p) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
    simpa using Offset.contains_base p (d := 0) (n := 4) (k := 8) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base p (d := 4) (n := 4) (k := 8) (by decide) (by decide))

theorem initPre_wp {s₀ : State} {St Kp S : BitVec 32} {KL : Nat} (hp : IPre s₀ St Kp S KL) :
    WP isa (.block initPre) s₀ fun s₁ => s₁.gpr .r0 = Kp ∧ s₁.gpr .r1 = BitVec.ofNat 32 KL ∧
      s₁.gpr .r2 = St ∧ s₁.gpr .r3 = S ∧ (∀ r ∈ preserved, s₁.gpr r = s₀.gpr r) ∧ s₁.sp = s₀.sp ∧
      s₁.mem = zeroCv s₀.mem (State.addr St + BitVec.ofNat 64 400) ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
  have hSt := hp.fSt
  have hKL : s₀.gpr .r2 = BitVec.ofNat 32 KL :=
    BitVec.eq_of_toNat_eq (by rw [hp.r2, toNat_ofNat32 (by rcases hp.klen with h | h <;> omega)])
  have inSt (d : Nat) (hd : d + 4 ≤ 416) : InRegions s₀.wr (State.addr St + BitVec.ofNat 64 d) 4 := by
    rw [hp.wr]; exact ⟨⟨State.addr St, 416⟩, by simp, Offset.contains_base _ hd (by omega)⟩
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
  refine wp_str (a := State.addr St + BitVec.ofNat 64 400) (by decide)
    (by rw [u₁.other _ (by decide), hp.r0]; exact addr_add (by omega)) (by rw [u₁.wr]; exact inSt 400 (by decide))
    fun s₂ v₂ => ?_
  refine wp_str (a := State.addr St + BitVec.ofNat 64 400 + BitVec.ofNat 64 4) (by decide)
    (by rw [v₂.gpr, u₁.other _ (by decide), hp.r0, Offset.add_add]; exact addr_add (by omega))
    (by rw [v₂.wr, u₁.wr, Offset.add_add]; exact inSt 404 (by decide)) fun s₃ v₃ => ?_
  refine wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ => wp_mov (op2_reg _ _) fun s₆ u₆ =>
    wp_mov (op2_reg _ _) fun s₇ u₇ => WP.block_nil ?_
  have g (r : Reg) (a : r ≠ .r0) (b : r ≠ .r1) (c : r ≠ .r2) (d : r ≠ .r12) : s₇.gpr r = s₀.gpr r := by
    rw [u₇.other _ c, u₆.other _ b, u₅.other _ a, u₄.other _ d, v₃.gpr, v₂.gpr, u₁.other _ d]
  refine ⟨?_, ?_, ?_, g _ (by decide) (by decide) (by decide) (by decide) |>.trans hp.r3,
    fun r hr => ?_, by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, v₃.sp, v₂.sp, u₁.sp], ?_,
    by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, v₃.rd, v₂.rd, u₁.rd], by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, v₃.wr, v₂.wr, u₁.wr]⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), v₃.gpr, v₂.gpr,
      u₁.other _ (by decide), hp.r1]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), v₃.gpr, v₂.gpr,
      u₁.other _ (by decide), hKL]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, v₃.gpr, v₂.gpr, u₁.other _ (by decide),
      hp.r0]
  · have : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact g r this.1 this.2.1 this.2.2.1 this.2.2.2
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, v₃.mem, v₂.mem, v₂.gpr, u₁.gpr, u₁.mem, zeroCv]

theorem init_wp {s₀ : State} (h0 : initArm.pre s₀) :
    WP isa streamInit s₀ fun s' => abiPreserved s₀ s' ∧ initArm.post s₀ s' := by
  have hp := IPre.of h0
  generalize s₀.gpr .r0 = St at hp
  generalize s₀.gpr .r1 = Kp at hp
  generalize s₀.gpr .r3 = S at hp
  generalize (s₀.gpr .r2).toNat = KL at hp
  have hw := hp.fSt
  refine WP.seq (WP.mono (initPre_wp hp) fun s₁ ⟨r0₁, r1₁, r2₁, r3₁, sv₁, sp₁, m₁, rd₁, wr₁⟩ => ?_)
  have oSt : Region.Sub ⟨State.addr St, 400⟩ ⟨State.addr St, 416⟩ := Region.sub_prefix (by decide)
  have args : IArgs s₁ Kp St S KL :=
    { r0 := r0₁, r1 := r1₁, r2 := r2₁, r3 := r3₁, klen := hp.klen
      ko := (hp.st_k.sub_left oSt).symm
      ks := hp.k_s
      os := hp.st_s.sub_left oSt
      fK := hp.fK
      fO := by omega
      fS := hp.fS
      reads := by
        rw [rd₁, wr₁, hp.rd, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨⟨State.addr Kp, KL⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨State.addr St, 416⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨State.addr S, 640⟩, by simp, 0, by simp, by simp⟩
      writes := by
        rw [wr₁, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨⟨State.addr St, 416⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨State.addr S, 640⟩, by simp, 0, by simp, by simp⟩ }
  refine WP.mono (init_inline_wp args) fun s₂ h₂ => ?_
  have f₁ : Frame [⟨State.addr St + BitVec.ofNat 64 400, 8⟩] s₀.mem s₁.mem := by rw [m₁]; exact zeroCv_frame _ _
  refine ⟨⟨fun r hr => by rw [h₂.saved r hr, sv₁ r hr], by rw [h₂.sp, sp₁]⟩, ?_⟩
  show Spec.Cmac.tdesRepr s₂.mem (State.addr (s₀.gpr .r0))
    (Spec.TripleDes.bytesAt s₀.mem (State.addr (s₀.gpr .r1)) (s₀.gpr .r2).toNat) []
  rw [hp.r0, hp.r1, hp.r2, Proof.CmacTripleDes.Stream.repr_iff]
  have hkey : Spec.TripleDes.bytesAt s₁.mem (State.addr Kp) KL = Spec.TripleDes.bytesAt s₀.mem (State.addr Kp) KL := by
    simp only [Spec.TripleDes.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact f₁.bytes (R := ⟨State.addr Kp, KL⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_k.symm.sub_right (Offset.sub_base _ (by decide)))
      (by show KL ≤ 2 ^ 64; have := hp.fK; omega) (List.mem_range.mp hi)
  have hlen : (Spec.TripleDes.bytesAt s₀.mem (State.addr Kp) KL).length = KL := by simp [Spec.TripleDes.bytesAt]
  obtain ⟨hs, hk⟩ := h₂.out
  rw [hkey] at hs hk
  refine ⟨⟨by rw [hlen]; exact hp.klen, hs, hk⟩, ?_, by
    simp [Proof.CmacTripleDes.Stream.held_zero, Spec.Aes.bytesAt]⟩
  rw [show State.addr St + 400 = State.addr St + BitVec.ofNat 64 400 from rfl,
    Proof.Cmac.bytesAt_frame h₂.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint_base _ (d := 400) (by decide) (by decide)
      · exact (hp.st_s.sub_left (Offset.sub_base _ (by decide)))) (by decide), m₁, zeroCv_bytes]
  rfl

/-! ## Constant time -/

/-- `stream_init`'s initial taint: the arguments are public; `r0` and `r3`
point at the state and the scratch buffer. -/
def initTaint : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [416, 640], bases := [(.r0, 0), (.r3, 1)] }

theorem initTaint_wf {s : State} (h : initArm.pre s) : VG.Arm.Taint.Wf initTaint s := by
  have hp := IPre.of h
  refine ⟨fun _ => ⟨by simp [hp.wr, initTaint], ?_, ?_⟩, fun p hp' => ?_, fun h => absurd h (by decide),
    fun _ h => (List.not_mem_nil h).elim⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, false_implies, implies_true, and_true]
    exact hp.st_s
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    have := hp.fSt; have := hp.fS
    rintro r (rfl | rfl) <;> simp only [addr_toNat] <;> omega
  · simp only [initTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> simp [VG.Arm.Taint.region, hp.wr]

theorem init_ct : ConstantTime isa initArm.pre initArm.pub streamInit := by
  refine VG.Taint.constantTime (A := taint) initTaint ?_ (by taint_decide)
  intro s t hs ht ⟨hsp, h0, h1, h2, h3⟩
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, initTaint_wf hs, initTaint_wf ht,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (by decide), fun k hk => absurd hk (by simp [initTaint])⟩
  · simp only [initTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [h0, h1, h2, h3]
  · rw [(IPre.of hs).wr, (IPre.of ht).wr, h0, h3]

end VG.Proof.CmacTripleDes.Stream.Arm
