module
public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Call

public import VerifiedGarbage.Impl.AesGcm.X86_64.DirectGather
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.CT
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CopyCT
meta import VerifiedGarbage.Impl.AesGcm.X86_64.DirectGather
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-! The prepared gather path calls the same out-of-place fused block kernel as split sealing. -/

@[expose] public section
namespace VG.Proof.AesGcm.X86_64.DirectGather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64.DirectGather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

structure FirstArgs (SP P D S : Addr) (n sl : Nat) (s : State) : Prop where
  desc : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = P
  dst : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = D
  len : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 n
  src : s.mem.readW P 64 = S
  size : s.mem.readW (P + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 sl
  descR : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 8) 8
  dstR : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 24) 8
  lenR : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 32) 8
  srcR : InRegions (s.rd ++ s.wr) P 8
  sizeR : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 8) 8

def firstMem (m : Mem) (W S D : Addr) (n : Nat) : Mem :=
  ((m.writeW (W + BitVec.ofNat 64 224) S).writeW (W + BitVec.ofNat 64 200) D).writeW
    (W + BitVec.ofNat 64 192) (BitVec.ofNat 64 n)

structure Prepared (Ctx W SP D S : Addr) (n sl : Nat) (s t : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP t
  count : t.gpr .rax = BitVec.ofNat 64 (sl / 16)
  zero : t.zf = some (decide (sl / 16 = 0))
  mem : t.mem = firstMem s.mem W S D n
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem firstArgs_wp {Ctx W SP P D S : Addr} {n sl : Nat} {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (h : FirstArgs SP P D S n sl s)
    (hsl : sl < 2 ^ 64) : WP isa (.block firstArgs) s (Prepared Ctx W SP D S n sl s) := by
  obtain ⟨dp, dd, dn, ds, dl, rp, rd, rn, rs, rl⟩ := h
  have w₁ := he.perm.wW (show 224 + 8 ≤ 2560 by decide)
  have w₂ := he.perm.wW (show 200 + 8 ≤ 2560 by decide)
  have w₃ := he.perm.wW (show 192 + 8 ≤ 2560 by decide)
  have h4 := shr4 sl hsl
  have hz := and_self_beq (show sl / 16 < 2 ^ 64 by omega)
  unfold firstArgs store
  apply WP.of_runBlock
  refine ⟨_, by xrun [BitVec.add_zero, he.rsp, he.r15, dp, dd, dn, ds, dl, rp, rd, rn, rs, rl, w₁, w₂, w₃, h4], ?_⟩
  constructor
  · apply he.keep
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_setFlags]
    all_goals rfl
  · simp [gpr_setReg]
  · simp only [zf_arithFlags, hz]
  all_goals rfl

/-- A reference state for the block call after the three workspace slots are set. -/
def callState (s : State) (W S D : Addr) (n : Nat) : State :=
  {s with mem := firstMem s.mem W S D n}

theorem firstMem_frame (m : Mem) (W S D : Addr) (n : Nat) :
    Frame [⟨W, 2560⟩] m (firstMem m W S D n) := by
  have slot (d : Nat) (hd : d + 8 ≤ 2560) : (⟨W, 2560⟩ : Region).Contains (W + BitVec.ofNat 64 d) 8 :=
    Offset.contains_base _ hd (by omega)
  exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) S (slot 224 (by decide))).writeW
    (List.mem_singleton_self _) D (slot 200 (by decide))).writeW (List.mem_singleton_self _)
    (BitVec.ofNat 64 n) (slot 192 (by decide))

theorem firstMem_slots (m : Mem) (W S D : Addr) (n : Nat) :
    (firstMem m W S D n).readW (W + 224#64) 64 = S ∧
    (firstMem m W S D n).readW (W + 200#64) 64 = D ∧
    (firstMem m W S D n).readW (W + 192#64) 64 = BitVec.ofNat 64 n ∧
    (firstMem m W S D n).readW (W + 176#64) 64 = m.readW (W + 176#64) 64 := by
  have sep (a b : Nat) (h : a + 8 ≤ b ∨ b + 8 ≤ a) (ha : a + 8 ≤ 2560) (hb : b + 8 ≤ 2560) :
      Mem.Sep (W + BitVec.ofNat 64 a) (64 / 8) (W + BitVec.ofNat 64 b) (64 / 8) :=
    Offset.sep W h (by omega) (by omega)
  unfold firstMem
  refine ⟨?_, ?_, Mem.readW_writeW_self64 .., ?_⟩
  · rw [Mem.readW_writeW_sep (sep 224 192 (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_sep (sep 224 200 (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 200 192 (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 176 192 (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_sep (sep 176 200 (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_sep (sep 176 224 (by decide) (by decide) (by decide)) (by decide)]

theorem firstBlocks_wp {M : CtxMode} (T : BlocksTo.SealFn M) {Ctx W SP P D S : Addr} {R n sl : Nat} {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (h : FirstArgs SP P D S n sl s)
    (c : Split.CallInputs M Ctx W SP D S R n sl (callState s W S D n)) :
    WP isa (firstBlocks T.fn) s (Split.Mid2 Ctx W SP D S R sl (callState s W S D n)) := by
  have hs : sl < 2 ^ 64 := Nat.lt_of_le_of_lt c.sl_le c.data.ok.lt
  unfold firstBlocks
  refine WP.seq (WP.mono (firstArgs_wp he h hs) fun t a => ?_)
  refine WP.ite (decide (sl / 16 = 0)) (by simp only [eval, a.zero]) (fun hz => ?_) (fun _ => ?_)
  · exact WP.block_nil (Split.mid2_zero ⟨a.env, a.count, a.zero, a.mem, a.rd, a.wr⟩ (of_decide_eq_true hz))
  · exact Split.Compact.call_ok c T a.env a.count a.mem a.rd a.wr

open VG.Impl.AesGcm.X86_64 (at_)

theorem loadDesc_wp {s : State} (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsp + 8#64) 8) :
    WP isa (.block [.mov .r10 (.mem (at_ .rsp 8))]) s (Gather.LdF .r10 .rsp 8 s) := by
  refine WP.of_runBlock ⟨_, by xrun [hr], ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg]
  · intro r hr; simp [gpr_setReg, hr]
  all_goals rfl

theorem desc_check : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .r10 (.mem (at_ .rsp 8))]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem rest_check : ∃ hc, (taint.check (Taint.ofRegs [.r10, .rsp, .r15]) (.block firstArgs.tail) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem firstArgs_rel {Ctx W SP P D S : Addr} {n sl : Nat} {s t : State}
    (es : Env Ctx (W + 16#64) W SP s) (et : Env Ctx (W + 16#64) W SP t)
    (a : FirstArgs SP P D S n sl s) (b : FirstArgs SP P D S n sl t) :
    RelCT isa (fun x y => x = s ∧ y = t) (.block firstArgs) fun _ _ => True := by
  have agree : ∀ x y : State, x = s ∧ y = t → ∀ r ∈ [Reg.rsp, .r15], x.gpr r = y.gpr r := by
    rintro _ _ ⟨rfl, rfl⟩ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [es.rsp, et.rsp]
    · rw [es.r15, et.r15]
  refine Gather.rel_ld (l := firstArgs.tail) (Gather.LdF .r10 .rsp 8) ?_ ?_ ?_
  · rintro _ _ ⟨rfl, rfl⟩
    exact ⟨loadDesc_wp (es.rsp ▸ a.descR), loadDesc_wp (et.rsp ▸ b.descR)⟩
  · exact rel_taint [.rsp] (fun x y h r hr => agree x y h r (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using (Or.inl (List.mem_singleton.mp hr) : r = .rsp ∨ r = .r15))) desc_check
  · refine rel_taint [.r10, .rsp, .r15] (Gather.ld_agree agree ?_) rest_check
    rintro _ _ ⟨rfl, rfl⟩
    rw [es.rsp, et.rsp, a.desc, b.desc]

theorem firstBlocks_rel {M : CtxMode} (T : BlocksTo.SealFn M) {Ctx W SP P D S : Addr} {R n sl : Nat} {s t : State}
    (es : Env Ctx (W + 16#64) W SP s) (et : Env Ctx (W + 16#64) W SP t)
    (a : FirstArgs SP P D S n sl s) (b : FirstArgs SP P D S n sl t)
    (c : Split.CallInputs M Ctx W SP D S R n sl (callState s W S D n))
    (c' : Split.CallInputs M Ctx W SP D S R n sl (callState t W S D n)) :
    RelCT isa (fun x y => x = s ∧ y = t) (firstBlocks T.fn) fun _ _ => True := by
  have hs : sl < 2 ^ 64 := Nat.lt_of_le_of_lt c.sl_le c.data.ok.lt
  unfold firstBlocks
  refine RelCT.seq ((firstArgs_rel es et a b).wp (F₁ := Prepared Ctx W SP D S n sl s) (F₂ := Prepared Ctx W SP D S n sl t) (fun _ _ h => ?_)) ?_
  · obtain ⟨rfl, rfl⟩ := h
    exact ⟨firstArgs_wp es a hs, firstArgs_wp et b hs⟩
  · refine RelCT.ite (fun _ _ h => by simp only [eval, h.2.1.zero, h.2.2.zero]) ?_ ?_
    · exact StreamTo.skip_rel fun _ _ _ => trivial
    · exact (Split.Compact.callPart_rel c c' T).mono (fun _ _ h =>
        ⟨⟨h.1.2.1.env, h.1.2.1.count, h.1.2.1.mem, h.1.2.1.rd, h.1.2.1.wr⟩,
         ⟨h.1.2.2.env, h.1.2.2.count, h.1.2.2.mem, h.1.2.2.rd, h.1.2.2.wr⟩⟩) fun _ _ _ => trivial

end VG.Proof.AesGcm.X86_64.DirectGather
