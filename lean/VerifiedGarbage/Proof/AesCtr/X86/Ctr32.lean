module

public import VerifiedGarbage.Impl.AesCtr.X86
public import VerifiedGarbage.Proof.AesCbc.X86.CT
public import VerifiedGarbage.Proof.AesCtr.Ctr32
public import VerifiedGarbage.Proof.AesCtr.Rounds
public import VerifiedGarbage.Proof.AesCtr.Spec
public import VerifiedGarbage.Proof.Aes.X86.Variant
public import VerifiedGarbage.Spec.Ctr.Contract
public import VerifiedGarbage.Proof.AesCtr.X86.Steps
public import VerifiedGarbage.Proof.AesGcm.X86.Callee
public import VerifiedGarbage.Proof.MdStream.X86.Common
import VerifiedGarbage.Proof.AesCbc.X86.Verified
import VerifiedGarbage.Proof.AesCcm.X86.Callee
import VerifiedGarbage.Proof.CmacAes.X86.UpdateLoop
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Impl.AesCtr.X86
meta import VerifiedGarbage.Proof.AesCbc.X86.CT

/-!
# AES-CTR on x86 (32-bit), over `vg_aes_ctr32_to`

`crypt32_verified`: `crypt32` (`Impl/AesCtr/X86.lean`), for any
implementation `v` of `vg_aes_ctr32_to` (`Ctr32Impl`), meets
`Proof.AesCtr.roundsContract` with 32 bytes of stack: each call pushes the
callee's seven arguments and the return address.

The loop is AES-CBC's (`Proof/AesCbc/X86/Body.lean`: the prologue, the
regions, the saved registers), with the 32 bytes below `esp` where its
invariant has 24 (`LInv32`), and steps of as many blocks as a call takes
(`mOf`): what is left, but no further than where the last 32 bits of the
counter block wrap around.
-/

@[expose] public section

namespace VG.Proof.AesCtr.X86.Ctr32

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCtr.X86
open VG.Impl.CmacAes.X86 (argOp at_ setup restore saved ctrCall)
open VG.Impl.AesCbc.X86 (whole)
open VG.Proof.AesCbc.X86
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ctr (next toNat ofNat)
open VG.Proof.AesGcm.X86 (CtrCall CtrPost)
open VG.Proof.MdStream.X86 (Upd wp_mov wp_movm wp_bswap wp_shr wp_sub wp_subi wp_add wp_cmp wp_test)
open VG.Proof.CmacAes.X86 (wp_arg wp_addArg ea_at' arg_ofNat)

/-- `vg_aes_ctr(schedule, rounds, ctr, data, n, scratch)` over
`vg_aes_ctr32_to`: AES-CBC's contract for `ctrMode` (`modeX86`), with the 32
bytes below `esp` for the calls, and two runs agreeing on the last 32 bits
of the counter block too. -/
def ctr32X86 : Contract isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 240⟩
    let iv : Region := ⟨(arg s 2).setWidth 64, 16⟩
    let data : Region := ⟨(arg s 3).setWidth 64, 16 * (arg s 4).toNat⟩
    let scr : Region := ⟨(arg s 5).setWidth 64, 2176⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 32, 32⟩
    s.rd = [sched, args] ∧ s.wr = [iv, data, scr] ∧
      sched.Disjoint iv ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧ iv.Disjoint data ∧ iv.Disjoint scr ∧
      data.Disjoint scr ∧ args.Disjoint iv ∧ args.Disjoint data ∧ args.Disjoint scr ∧
      ret.Disjoint iv ∧ ret.Disjoint data ∧ ret.Disjoint scr ∧
      stack.Disjoint sched ∧ stack.Disjoint iv ∧ stack.Disjoint data ∧ stack.Disjoint scr ∧
      (arg s 0).toNat + 240 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 16 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 16 * (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + 2176 ≤ 2 ^ 32 ∧
      32 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
      ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14)
  post := (modeX86 AesCtr.ctrMode).post
  pub s₁ s₂ := (modeX86 AesCtr.ctrMode).pub s₁ s₂ ∧ AesCtr.lo32 (iv0 s₁) = AesCtr.lo32 (iv0 s₂)

/-- The 32 bytes below the stack pointer on entry. -/
abbrev stk32 (s₀ : State) : Region := ⟨(E s₀).setWidth 64 - BitVec.ofNat 64 32, 32⟩

theorem stkR_sub (s₀ : State) : Region.Sub (stkR s₀) (stk32 s₀) := by
  intro x hx
  exact Offset.below_mono _ (a := 24) (b := 32) (by decide) (by decide) x hx

/-- The precondition, by name: AES-CBC's, and the 32 bytes below `esp`. -/
structure XPre (s₀ : State) : Prop where
  u : UPre s₀
  esp32 : 32 ≤ (E s₀).toNat
  x_sch : (stk32 s₀).Disjoint (schR s₀)
  x_iv : (stk32 s₀).Disjoint (ivR s₀)
  x_data : (stk32 s₀).Disjoint (dataR s₀)
  x_scr : (stk32 s₀).Disjoint (scrR s₀)

theorem XPre.of {s₀ : State} (h : ctr32X86.pre s₀) : XPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w, x, y, z⟩ := h
  ⟨⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o.sub_left (stkR_sub s₀), p.sub_left (stkR_sub s₀),
    q.sub_left (stkR_sub s₀), r.sub_left (stkR_sub s₀), t, u, v, w, Nat.le_trans (by decide) x, y, z⟩, x, o, p, q, r⟩

/-- The loop invariant, after `k` blocks: AES-CBC's for `ctrMode` (`LInv`),
with the 32 bytes below `esp`. -/
structure LInv32 (s₀ : State) (k : Nat) (s : State) : Prop where
  esi : s.gpr .esi = Dp s₀ + BitVec.ofNat 32 (16 * k)
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stk32 s₀] (savedMem s₀) s.mem
  data : Spec.Cbc.blocksAt s.mem ((Dp s₀).setWidth 64) (N s₀) = outK AesCtr.ctrMode s₀ k ++ (blks s₀).drop k
  iv : bytesAt s.mem ((Iv s₀).setWidth 64) 16 = chainK AesCtr.ctrMode s₀ k

theorem LInv32.of {s₀ : State} {k : Nat} {s : State} (h : LInv AesCtr.ctrMode s₀ k s) : LInv32 s₀ k s :=
  ⟨h.esi, h.esp, h.rd, h.wr, h.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨stk32 s₀, by simp, stkR_sub s₀⟩, h.data, h.iv⟩

/-- The regions the function writes, with the stack below it. -/
abbrev Big32 (s₀ : State) : List Region := [ivR s₀, dataR s₀, scrR s₀, stk32 s₀]

theorem big32_of {s₀ : State} {m : Mem}
    (hf : Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stk32 s₀] (savedMem s₀) m) :
    Frame (Big32 s₀) s₀.mem m :=
  ((savedMem_frame s₀).mono (by simp)).trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stk32 s₀, by simp, fun _ h => h⟩)

section
variable {s₀ : State} (hp : XPre s₀)
include hp

theorem XPre.below_eq : below (E s₀) 32 = stk32 s₀ := by
  simp only [below]; rw [Taint.sub_setWidth hp.esp32]

theorem XPre.args_stk : (argsR s₀).Disjoint (stk32 s₀) := by
  have : (s₀.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.u.esp_fit
  have e : argAddr s₀ 0 = (E s₀).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega_using [this])
  show Region.Disjoint ⟨argAddr s₀ 0, 24⟩ _
  rw [e]; exact (Offset.disjoint_below_above _ (by decide)).symm

omit hp in
theorem ret_stk32 (s₀ : State) : (retR s₀).Disjoint (stk32 s₀) := by
  have := Offset.disjoint_below_above ((E s₀).setWidth 64) (m := 32) (a := 0) (l := 4) (by decide)
  rw [VG.Proof.CmacAes.X86.add0] at this
  exact this.symm

/-- The stack arguments are unchanged where only `Big32` changes. -/
theorem XPre.arg_keep {m : Mem} (hf : Frame (Big32 s₀) s₀.mem m) {i : Nat} (hi : i < 6) :
    m.readW (argAddr s₀ i) 32 = arg s₀ i :=
  hf.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.u.args_iv.sub_left (hp.u.arg_sub hi)
    · exact hp.u.args_data.sub_left (hp.u.arg_sub hi)
    · exact hp.u.args_scr.sub_left (hp.u.arg_sub hi)
    · exact hp.args_stk.sub_left (hp.u.arg_sub hi)) (by decide)

theorem XPre.sched_bytes {m : Mem} (hf : Frame (Big32 s₀) s₀.mem m) :
    bytesAt m ((W s₀).setWidth 64) (16 * (R s₀ + 1)) = bytesAt s₀.mem ((W s₀).setWidth 64) (16 * (R s₀ + 1)) := by
  have hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.u.rounds with h | h | h <;> omega_using [h]
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega_using [hR])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.u.sch_iv.sub_left (Region.sub_prefix hR)
  · exact hp.u.sch_data.sub_left (Region.sub_prefix hR)
  · exact hp.u.sch_scr.sub_left (Region.sub_prefix hR)
  · exact hp.x_sch.symm.sub_left (Region.sub_prefix hR)

theorem slot_read32 {m : Mem}
    (hf : Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stk32 s₀] (savedMem s₀) m) {d : Nat}
    (h₁ : 2064 ≤ d) (h₂ : d + 4 ≤ 2080) :
    m.readW ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 =
      (savedMem s₀).readW ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 :=
  hf.readW (r := ⟨(S s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.u.iv_scr.symm.sub_left (UPre.scr_sub (by omega_using [h₂]))
    · exact hp.u.data_scr.symm.sub_left (UPre.scr_sub (by omega_using [h₂]))
    · exact Offset.disjoint_base _ h₁ (by omega_using [h₂])
    · exact hp.x_scr.symm.sub_left (UPre.scr_sub (by omega_using [h₂]))) (by decide)

/-- The return address, which nothing writes. -/
theorem ret_read32 {m : Mem}
    (hf : Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stk32 s₀] (savedMem s₀) m) :
    m.readW ((E s₀).setWidth 64) 32 = s₀.mem.readW ((E s₀).setWidth 64) 32 :=
  (big32_of hf).readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.u.ret_iv
    · exact hp.u.ret_data
    · exact hp.u.ret_scr
    · exact ret_stk32 s₀) (by decide)

theorem epilogue_wp32 {s : State} (h : LInv32 s₀ (N s₀) s) :
    WP isa (.block (restore 5)) s fun s' => abiPreserved s₀ s' ∧ ctr32X86.post s₀ s' := by
  have hsc : (arg s₀ 5).toNat + 2176 ≤ 2 ^ 32 := hp.u.scr_fit
  have rdwr : s.rd ++ s.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [h.rd, h.wr, hp.u.rd, hp.u.wr]; rfl
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have sl : ∀ r d, (r, d) ∈ saved → s.mem.readW ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r :=
    fun r d hrd => by
      have hb := VG.Proof.CmacAes.X86.saved_bound _ hrd
      rw [slot_read32 hp h.frame hb.1 hb.2, savedMem_slot s₀ hrd]
  have hall : (blks s₀).take (N s₀) = blks s₀ := List.take_of_length_le (by simp [Spec.Cbc.blocksAt])
  have hnil : (blks s₀).drop (N s₀) = [] := List.drop_of_length_le (by simp [Spec.Cbc.blocksAt])
  rw [VG.Proof.CmacAes.X86.restore_eq]
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.u.arg_in (by decide))
    (hp.arg_keep (big32_of h.frame) (by decide)) fun s₁ u₁ => ?_
  refine Spill.restore_ofNat_ok saved VG.Proof.CmacAes.X86.saved_fits (by rw [u₁.gpr]; omega_using [hsc])
    VG.Proof.CmacAes.X86.saved_ne_eax (fun p hp' => ?_)
    (fun p hp' => by rw [u₁.gpr, u₁.mem]; exact sl p.1 p.2 hp') fun s₂ r₂ => WP.block_nil ?_
  · have hb := VG.Proof.CmacAes.X86.saved_bound p hp'
    rw [u₁.gpr, u₁.rd, u₁.wr, rdwr]
    exact ⟨scrR s₀, by simp, Offset.contains_base _ (by omega_using [hb]) (by omega_using [hb])⟩
  refine ⟨⟨r₂.abi (by decide) (by decide) (by rw [u₁.other _ (by decide), h.esp]), ?_⟩, ?_, ?_⟩
  · rw [r₂.mem, u₁.mem]; exact ret_read32 hp h.frame
  · show Spec.Cbc.blocksAt s₂.mem ((Dp s₀).setWidth 64) (N s₀) = _
    rw [r₂.mem, u₁.mem, h.data]; simp only [outK, hall, hnil, List.append_nil]
  · show bytesAt s₂.mem ((Iv s₀).setWidth 64) 16 = _
    rw [r₂.mem, u₁.mem, h.iv]; simp only [chainK, hall]

end

/-- The registers saved and the arguments set up, `mid` run unless there are
no blocks, and the registers restored, when `mid` takes the invariant from no
blocks to all of them. -/
theorem ends_wp32 {mid : Prog isa} {s₀ : State} (h0 : ctr32X86.pre s₀)
    (hm : XPre s₀ → 0 < N s₀ → ∀ {s₁ : State}, LInv32 s₀ 0 s₁ → WP isa mid s₁ (LInv32 s₀ (N s₀))) :
    WP isa (.seq (.block setup) (.seq (.ite .e (.block []) mid) (.block (restore 5)))) s₀
      fun s' => abiPreserved s₀ s' ∧ ctr32X86.post s₀ s' := by
  have hp := XPre.of h0
  refine WP.seq (WP.mono (prologue_wp (M := AesCtr.ctrMode) hp.u) fun s₁ ⟨⟨h₁, hz⟩, _⟩ => WP.seq ?_)
  have ev : isa.eval .e s₁ = some (decide (N s₀ = 0)) := by
    show VG.X86.eval .e s₁ = _; rw [VG.Proof.MdStream.X86.eval_e, hz]
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev]; simp [hn]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    exact epilogue_wp32 hp (by rw [hn]; exact LInv32.of h₁)
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact WP.mono (hm hp (by omega_using [hn]) (LInv32.of h₁)) fun _ h₂ => epilogue_wp32 hp h₂

/-! ## One instruction at a time, where the shared lemmas have none -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

open VG.Proof.MdStream.X86 (Upd)

theorem wp_xori {d : Reg} {v : BitVec 32} (k : ∀ s', Upd s s' d (s.gpr d ^^^ v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.imm v) :: is)) s Q :=
  VG.Proof.MdStream.X86.WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

/-- `sub d, [esp + 4 + 4 i]`. -/
theorem wp_subArg {d : Reg} {i : Nat} {s₀ : State} (hesp : s.gpr .esp = s₀.gpr .esp)
    (hin : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4) (hv : s.mem.readW (argAddr s₀ i) 32 = arg s₀ i)
    (k : ∀ s', Upd s s' d (s.gpr d - arg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (argOp i) :: is)) s Q := by
  refine VG.Proof.MdStream.X86.WP.cons (s' := (arithFlags s (s.gpr d - arg s₀ i)
    ((s.gpr d).toNat < (arg s₀ i).toNat) (subOverflow (s.gpr d) (arg s₀ i) (s.gpr d - arg s₀ i))).setReg d
      (s.gpr d - arg s₀ i)) ?_ (k _ (Upd.flags _ _ _ _ _ _))
  have ea : s.ea (at_ .esp (4 + 4 * i)) = argAddr s₀ i := by rw [VG.Proof.CmacAes.X86.ea_at', hesp]; rfl
  simp [exec, execAlu, readSrc, argOp, State.load32, ea, hin, hv]

end

/-! ## The blocks of a call -/

/-- The blocks of the call after `k` blocks: what is left, but no further
than where the last 32 bits of the counter block wrap around. -/
def mOf (s₀ : State) (k : Nat) : Nat := min (N s₀ - k) (2 ^ 32 - (toNat (iv0 s₀) + k) % 2 ^ 32)

theorem length_iv0 (s₀ : State) : (iv0 s₀).length = 16 := Proof.Cmac.bytesAt_length _ _ _

theorem mOf_pos {s₀ : State} {k : Nat} (hk : k < N s₀) : 0 < mOf s₀ k := by
  unfold mOf; have := Nat.mod_lt (toNat (iv0 s₀) + k) (show 0 < 2 ^ 32 by decide); omega_using [hk]

theorem mOf_le (s₀ : State) (k : Nat) : mOf s₀ k ≤ N s₀ - k := Nat.min_le_left _ _

theorem lo32_mOf (s₀ : State) (k : Nat) : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k ≤ 2 ^ 32 := by
  rw [AesCtr.lo32_next (length_iv0 s₀)]; unfold mOf; omega_using []

theorem chainK_ctr (s₀ : State) {k : Nat} (hk : k ≤ N s₀) : chainK AesCtr.ctrMode s₀ k = next (iv0 s₀) k := by
  rw [chainK, AesCtr.ctrMode_chain, List.length_take, Proof.AesCbc.length_blocksAt, Nat.min_eq_left hk]

/-- The smaller of two words, plus 1, by a mask of their comparison. -/
theorem min_ok (s : State) :
    ∃ s', runBlock isa [.alu .cmp .ecx (.reg .edi), .alu .sbb .eax (.reg .eax), .alu .xor .ecx (.reg .edi),
        .alu .and .ecx (.reg .eax), .alu .xor .edi (.reg .ecx), .alu .add .edi (.imm 1)] s = some s' ∧
      s'.gpr .edi = (if (s.gpr .ecx).toNat < (s.gpr .edi).toNat then s.gpr .ecx else s.gpr .edi) + 1 ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edi → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags, cf_arithFlags]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [↓reduceIte, gpr_setReg]
    by_cases h : (s.gpr .ecx).toNat < (s.gpr .edi).toNat
    · have e : s.gpr .eax - s.gpr .eax - BitVec.setWidth 32 (BitVec.ofBool true) = BitVec.allOnes 32 := by
        rw [BitVec.sub_self]; decide
      simp only [h, decide_true, ↓reduceIte, e, BitVec.and_allOnes]
      rw [BitVec.xor_comm (s.gpr .ecx), ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    · have e : s.gpr .eax - s.gpr .eax - BitVec.setWidth 32 (BitVec.ofBool false) = 0#32 := by
        rw [BitVec.sub_self]; decide
      simp only [h, decide_false, ↓reduceIte, e]
      rw [BitVec.and_zero, BitVec.xor_zero]
  · intro r h₁ h₂ h₃
    simp [gpr_setReg, h₁, h₂, h₃]
  all_goals rfl

/-! ## The code before the call -/

/-- The blocks left after `k`, less 1: `n` less the blocks before `esi`. -/
theorem left_eq {D n : BitVec 32} {k : Nat} (hk : k < n.toNat) (hfit : D.toNat + 16 * n.toNat ≤ 2 ^ 32) :
    n - ((D + BitVec.ofNat 32 (16 * k) - D) >>> 4) - 1 = BitVec.ofNat 32 (n.toNat - k - 1) := by
  have e : D + BitVec.ofNat 32 (16 * k) - D = BitVec.ofNat 32 (16 * k) := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel]
  rw [e]
  apply BitVec.eq_of_toNat_eq
  have := n.isLt
  have h1 : (1 : BitVec 32).toNat = 1 := rfl
  simp only [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, h1]
  omega_using [hk, hfit, this]

/-- The blocks of a call, from the last 32 bits `c` of the counter block and
the blocks left. -/
theorem m_eq {c : BitVec 32} {n k : Nat} (hk : k < n) (hn : 16 * n ≤ 2 ^ 32) :
    (if (c ^^^ 0xFFFFFFFF).toNat < (BitVec.ofNat 32 (n - k - 1)).toNat then c ^^^ 0xFFFFFFFF
      else BitVec.ofNat 32 (n - k - 1)) + 1 = BitVec.ofNat 32 (min (n - k) (2 ^ 32 - c.toNat)) := by
  have hx : (c ^^^ 0xFFFFFFFF).toNat = 2 ^ 32 - 1 - c.toNat := by
    rw [show (0xFFFFFFFF : BitVec 32) = BitVec.allOnes 32 by decide, BitVec.xor_allOnes, BitVec.toNat_not]
  have hl : (BitVec.ofNat 32 (n - k - 1)).toNat = n - k - 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn])]
  have hc := c.isLt
  have h1 : (1 : BitVec 32).toNat = 1 := rfl
  rw [hx, hl]
  apply BitVec.eq_of_toNat_eq
  split
  · rename_i h
    rw [BitVec.toNat_add, hx, h1, BitVec.toNat_ofNat]
    omega_using [h, hk, hn, hc]
  · rename_i h
    rw [BitVec.toNat_add, hl, h1, BitVec.toNat_ofNat]
    omega_using [h, hk, hn, hc]

/-- What the first part of `count` leaves. -/
structure CountA (s₀ : State) (k : Nat) (s s₁ : State) : Prop where
  edx : s₁.gpr .edx = Iv s₀
  ecx : s₁.gpr .ecx = bswap (s.mem.readW ((Iv s₀).setWidth 64 + BitVec.ofNat 64 12) 32) ^^^ 0xFFFFFFFF
  edi : s₁.gpr .edi = BitVec.ofNat 32 (N s₀ - k - 1)
  esi : s₁.gpr .esi = s.gpr .esi
  esp : s₁.gpr .esp = s.gpr .esp
  mem : s₁.mem = s.mem
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem countA_wp {s₀ : State} (hp : XPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv32 s₀ k s) :
    WP isa (.block [.mov .edx (argOp 2), .mov .ecx (.mem (at_ .edx 12)), .bswap .ecx,
      .alu .xor .ecx (.imm 0xFFFFFFFF), .mov .edi (argOp 4), .mov .eax (.reg .esi), .alu .sub .eax (argOp 3),
      .shift .shr .eax 4, .alu .sub .edi (.reg .eax), .alu .sub .edi (.imm 1)]) s (CountA s₀ k s) := by
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have hargs : ∀ i < 6, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i :=
    fun i hi => hp.arg_keep (big32_of h.frame) hi
  have hiv : (arg s₀ 2).toNat + 16 ≤ 2 ^ 32 := hp.u.iv_fit
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.u.arg_in (by decide)) (hargs 2 (by decide)) fun s₁ u₁ => ?_
  refine wp_movm (a := (Iv s₀).setWidth 64 + BitVec.ofNat 64 12)
    (by rw [ea_at', u₁.gpr]; exact addr_eq (by omega_using [hiv]))
    (by rw [u₁.rd, u₁.wr, hrw, hp.u.rd, hp.u.wr]
        exact ⟨ivR s₀, by simp, Offset.contains_base _ (by decide) (by decide)⟩) fun s₂ u₂ => ?_
  refine wp_bswap fun s₃ u₃ => ?_
  refine wp_xori fun s₄ u₄ => ?_
  have esp₄ : s₄.gpr .esp = s₀.gpr .esp := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.esp]
  have rw₄ : s₄.rd ++ s₄.wr = s₀.rd ++ s₀.wr := by
    rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine wp_arg (s₀ := s₀) esp₄ (by rw [rw₄]; exact hp.u.arg_in (by decide))
    (by rw [m₄]; exact hargs 4 (by decide)) fun s₅ u₅ => ?_
  refine wp_mov fun s₆ u₆ => ?_
  refine wp_subArg (s₀ := s₀) (by rw [u₆.other _ (by decide), u₅.other _ (by decide), esp₄])
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, rw₄]; exact hp.u.arg_in (by decide))
    (by rw [u₆.mem, u₅.mem, m₄]; exact hargs 3 (by decide)) fun s₇ u₇ => ?_
  refine wp_shr (by decide) fun s₈ u₈ => ?_
  refine wp_sub fun s₉ u₉ _ => ?_
  refine wp_subi fun s₁₀ u₁₀ _ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr, u₁.mem]
  · have esi₅ : s₅.gpr .esi = Dp s₀ + BitVec.ofNat 32 (16 * k) := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), h.esi]
    rw [u₁₀.gpr, u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
      u₈.gpr, u₇.gpr, u₆.gpr, esi₅]
    exact left_eq hk hp.u.data_fit
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), esp₄, h.esp]
  · rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄]
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

theorem count_eq : count ++ args =
    ([.mov .edx (argOp 2), .mov .ecx (.mem (at_ .edx 12)), .bswap .ecx, .alu .xor .ecx (.imm 0xFFFFFFFF),
      .mov .edi (argOp 4), .mov .eax (.reg .esi), .alu .sub .eax (argOp 3), .shift .shr .eax 4,
      .alu .sub .edi (.reg .eax), .alu .sub .edi (.imm 1)] : List Instr) ++
    (([.alu .cmp .ecx (.reg .edi), .alu .sbb .eax (.reg .eax), .alu .xor .ecx (.reg .edi),
      .alu .and .ecx (.reg .eax), .alu .xor .edi (.reg .ecx), .alu .add .edi (.imm 1)] : List Instr) ++
      ([.mov .eax (argOp 0), .mov .ecx (argOp 1), .mov .ebx (.reg .esi), .mov .ebp (argOp 5)] : List Instr)) := rfl

section
variable {s₀ : State} (hp : XPre s₀)
include hp

omit hp in
theorem seg_sub {k m : Nat} (hkm : k + m ≤ N s₀) : Region.Sub ⟨blk s₀ k, 16 * m⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega_using [hkm])

theorem XPre.n16 : 16 * N s₀ ≤ 2 ^ 32 := by have := hp.u.data_fit; omega_using [this]

/-- The arguments of the call after `k` blocks. -/
theorem XPre.ctrCall {k : Nat} (hk : k < N s₀) {s : State}
    (eax : s.gpr .eax = W s₀) (ecx : s.gpr .ecx = arg s₀ 1) (edx : s.gpr .edx = Iv s₀)
    (ebx : s.gpr .ebx = D32 s₀ k) (edi : s.gpr .edi = BitVec.ofNat 32 (mOf s₀ k)) (ebp : s.gpr .ebp = S s₀)
    (esp : s.gpr .esp = E s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CtrCall s (W s₀) (Iv s₀) (D32 s₀ k) (S s₀) (R s₀) (mOf s₀ k) := by
  have hle := mOf_le s₀ k
  have hkm : k + mOf s₀ k ≤ N s₀ := by omega_using [hk, hle]
  obtain hb : below (s.gpr .esp) 32 = stk32 s₀ := by rw [esp]; exact hp.below_eq
  obtain hd : VG.Proof.AesGcm.X86.w64 (D32 s₀ k) = blk s₀ k := hp.u.d32 hk
  have hdf := hp.u.data_fit
  have hsf := hp.u.scr_fit
  refine ⟨eax, by rw [ecx]; exact arg_ofNat s₀ 1, edx, ebx, edi, ebp, hp.u.rounds, by rw [esp]; exact hp.esp32,
    hp.u.sch_iv, ?_, hp.u.sch_scr.sub_right (Region.sub_prefix (by decide)), ?_,
    hp.u.iv_scr.sub_right (Region.sub_prefix (by decide)), ?_, by rw [hb]; exact hp.x_sch,
    by rw [hb]; exact hp.x_iv, ?_, by rw [hb]; exact hp.x_scr.sub_right (Region.sub_prefix (by decide)),
    hp.u.sch_fit, hp.u.iv_fit, ?_, by omega_using [hsf], ?_, ?_⟩
  · rw [hd]; exact hp.u.sch_data.sub_right (seg_sub hkm)
  · rw [hd]; exact hp.u.iv_data.sub_right (seg_sub hkm)
  · rw [hd]; exact (hp.u.data_scr.sub_left (seg_sub hkm)).sub_right (Region.sub_prefix (by decide))
  · rw [hb, hd]; exact hp.x_data.sub_right (seg_sub hkm)
  · rw [hp.u.dataN hk]; omega_using [hdf, hkm]
  · rw [hrd, hwr, hp.u.rd, hp.u.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
  · rw [hwr, hp.u.wr, hd]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨dataR s₀, by simp, 16 * k, rfl, by simp; omega_using [hkm]⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

/-- What the code before the call leaves. -/
structure Pre32 (s₀ : State) (k : Nat) (s s₁ : State) : Prop where
  call : CtrCall s₁ (W s₀) (Iv s₀) (D32 s₀ k) (S s₀) (R s₀) (mOf s₀ k)
  esi : s₁.gpr .esi = s.gpr .esi
  esp : s₁.gpr .esp = s.gpr .esp
  mem : s₁.mem = s.mem
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem pre_wp {k : Nat} (hk : k < N s₀) {s : State} (h : LInv32 s₀ k s) :
    WP isa (.block (count ++ args)) s (Pre32 s₀ k s) := by
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have hargs : ∀ i < 6, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i :=
    fun i hi => hp.arg_keep (big32_of h.frame) hi
  rw [count_eq, WP.block_append_iff]
  refine WP.mono (countA_wp hp hk h) fun s₁ a => ?_
  obtain ⟨s₂, run₂, edi₂, g₂, mem₂, rd₂, wr₂⟩ := min_ok s₁
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have esp₂ : s₂.gpr .esp = s₀.gpr .esp := by rw [g₂ _ (by decide) (by decide) (by decide), a.esp, h.esp]
  have rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [rd₂, wr₂, a.rd, a.wr, hrw]
  have m₂ : s₂.mem = s.mem := by rw [mem₂, a.mem]
  refine wp_arg (s₀ := s₀) esp₂ (by rw [rw₂]; exact hp.u.arg_in (by decide))
    (by rw [m₂]; exact hargs 0 (by decide)) fun s₃ u₃ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₃.other _ (by decide), esp₂])
    (by rw [u₃.rd, u₃.wr, rw₂]; exact hp.u.arg_in (by decide))
    (by rw [u₃.mem, m₂]; exact hargs 1 (by decide)) fun s₄ u₄ => ?_
  refine wp_mov fun s₅ u₅ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), esp₂])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rw₂]; exact hp.u.arg_in (by decide))
    (by rw [u₅.mem, u₄.mem, u₃.mem, m₂]; exact hargs 5 (by decide)) fun s₆ u₆ => WP.block_nil ?_
  -- The number of blocks.
  have hiv : bytesAt s.mem ((Iv s₀).setWidth 64) 16 = next (iv0 s₀) k := by
    rw [h.iv, chainK_ctr s₀ (by omega_using [hk])]
  have hlo := AesCtr.lo32_bytesAt s.mem ((Iv s₀).setWidth 64)
  rw [hiv, AesCtr.lo32_next (length_iv0 s₀)] at hlo
  have hm : s₂.gpr .edi = BitVec.ofNat 32 (mOf s₀ k) := by
    rw [edi₂, a.ecx, a.edi, m_eq hk hp.n16]
    unfold mOf
    rw [show bswap (s.mem.readW ((Iv s₀).setWidth 64 + BitVec.ofNat 64 12) 32) =
      AesCtr.rv32 (s.mem.readW ((Iv s₀).setWidth 64 + BitVec.ofNat 64 12) 32) from rfl, ← hlo]
  have esi₂ : s₂.gpr .esi = s.gpr .esi := by rw [g₂ _ (by decide) (by decide) (by decide), a.esi]
  have esi₆ : s₆.gpr .esi = s.gpr .esi := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), esi₂]
  have esp₆ : s₆.gpr .esp = s₀.gpr .esp := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), esp₂]
  have rd₆ : s₆.rd = s.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, a.rd]
  have wr₆ : s₆.wr = s.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, a.wr]
  refine ⟨hp.ctrCall hk ?_ ?_ ?_ ?_ ?_ u₆.gpr esp₆ (by rw [rd₆, h.rd]) (by rw [wr₆, h.wr]), esi₆,
    by rw [esp₆, h.esp], by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂], rd₆, wr₆⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      g₂ _ (by decide) (by decide) (by decide), a.edx]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), esi₂, h.esi]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), hm]

end

/-! ## The carry into the first 96 bits -/

/-- The block at `P` plus `2³²` as three 32-bit words: the reversed words
`rv32 wᵢ` stored at `P + 8`, `P + 4` and `P`, each the word read there plus
the carry out of the words after it, the first carry being 1. -/
theorem carry_words32 (m : Mem) (P : Addr) (w0 w1 w2 : BitVec 32)
    (h2 : w2.toNat = ((AesCtr.rv32 (m.readW (P + BitVec.ofNat 64 8) 32)).toNat + 1) % 2 ^ 32)
    (h1 : w1.toNat = ((AesCtr.rv32 (m.readW (P + BitVec.ofNat 64 4) 32)).toNat +
      ((AesCtr.rv32 (m.readW (P + BitVec.ofNat 64 8) 32)).toNat + 1) / 2 ^ 32) % 2 ^ 32)
    (h0 : w0.toNat = ((AesCtr.rv32 (m.readW P 32)).toNat +
      ((AesCtr.rv32 (m.readW (P + BitVec.ofNat 64 4) 32)).toNat +
        ((AesCtr.rv32 (m.readW (P + BitVec.ofNat 64 8) 32)).toNat + 1) / 2 ^ 32) / 2 ^ 32) % 2 ^ 32) :
    bytesAt (((m.writeW (P + BitVec.ofNat 64 8) (AesCtr.rv32 w2)).writeW (P + BitVec.ofNat 64 4)
      (AesCtr.rv32 w1)).writeW P (AesCtr.rv32 w0)) P 16 = ofNat (toNat (bytesAt m P 16) + 2 ^ 32) 16 := by
  have split (m' : Mem) : bytesAt m' P 16 = bytesAt m' P 4 ++ (bytesAt m' (P + BitVec.ofNat 64 4) 4 ++
      (bytesAt m' (P + BitVec.ofNat 64 8) 4 ++ bytesAt m' (P + BitVec.ofNat 64 12) 4)) := by
    rw [show (16 : Nat) = 4 + 12 from rfl, AesCtr.bytesAt_append, show (12 : Nat) = 4 + 8 from rfl,
      AesCtr.bytesAt_append, show (8 : Nat) = 4 + 4 from rfl, AesCtr.bytesAt_append,
      Offset.add_add_eq P (show 4 + 4 = 8 from rfl), Offset.add_add_eq P (show 8 + 4 = 12 from rfl)]
  rw [split, split m]
  -- The words of the result.
  rw [AesCtr.bytesAt_writeW_rv32, AesCtr.bytesAt_writeW_sep _ _ _ (by decide) (by decide),
    AesCtr.bytesAt_writeW_rv32, AesCtr.bytesAt_writeW_sep _ _ _ (by decide) (by decide),
    AesCtr.bytesAt_writeW_sep' _ _ _ (by decide) (by decide), AesCtr.bytesAt_writeW_rv32,
    AesCtr.bytesAt_writeW_sep _ _ _ (by decide) (by decide),
    AesCtr.bytesAt_writeW_sep' _ _ _ (by decide) (by decide),
    AesCtr.bytesAt_writeW_sep' _ _ _ (by decide) (by decide)]
  -- The words of the counter block.
  rw [AesCtr.bytesAt_rv32 m P, AesCtr.bytesAt_rv32 m (P + BitVec.ofNat 64 4),
    AesCtr.bytesAt_rv32 m (P + BitVec.ofNat 64 8), AesCtr.bytesAt_rv32 m (P + BitVec.ofNat 64 12)]
  have b0 := (AesCtr.rv32 (m.readW P 32)).isLt
  have b1 := (AesCtr.rv32 (m.readW (P + BitVec.ofNat 64 4) 32)).isLt
  have b2 := (AesCtr.rv32 (m.readW (P + BitVec.ofNat 64 8) 32)).isLt
  have b3 := (AesCtr.rv32 (m.readW (P + BitVec.ofNat 64 12) 32)).isLt
  generalize (AesCtr.rv32 (m.readW P 32)).toNat = A0 at *
  generalize (AesCtr.rv32 (m.readW (P + BitVec.ofNat 64 4) 32)).toNat = A1 at *
  generalize (AesCtr.rv32 (m.readW (P + BitVec.ofNat 64 8) 32)).toNat = A2 at *
  generalize (AesCtr.rv32 (m.readW (P + BitVec.ofNat 64 12) 32)).toNat = A3 at *
  have hv : toNat (ofNat A0 4 ++ (ofNat A1 4 ++ (ofNat A2 4 ++ ofNat A3 4))) =
      A0 * 2 ^ 96 + A1 * 2 ^ 64 + A2 * 2 ^ 32 + A3 := by
    simp only [AesCtr.toNat_append, AesCtr.toNat_ofNat, AesCtr.length_ofNat, List.length_append, Nat.reducePow,
      Nat.reduceAdd]
    simp only [Nat.reducePow] at b0 b1 b2 b3
    rw [Nat.mod_eq_of_lt b0, Nat.mod_eq_of_lt b1, Nat.mod_eq_of_lt b2, Nat.mod_eq_of_lt b3]
    omega_using []
  rw [hv, show (16 : Nat) = 4 + (4 + (4 + 4)) from rfl, AesCtr.ofNat_add, AesCtr.ofNat_add, AesCtr.ofNat_add]
  simp only [Nat.reducePow, Nat.reduceAdd] at *
  exact congr (congrArg HAppend.hAppend (AesCtr.ofNat_congr (by omega_using [h0, b0, b1, b2, b3])))
    (congr (congrArg HAppend.hAppend (AesCtr.ofNat_congr (by omega_using [h1, b1, b2, b3])))
      (congr (congrArg HAppend.hAppend (AesCtr.ofNat_congr (by omega_using [h2, b2, b3])))
        (AesCtr.ofNat_congr (by omega_using [b3]))))

/-- The memory after `carry` on the block at `Q`. -/
def carryMem (m : Mem) (Q : Addr) : Mem :=
  let a2 := bswap (m.readW (Q + BitVec.ofNat 64 8) 32)
  let a1 := bswap (m.readW (Q + BitVec.ofNat 64 4) 32)
  let a0 := bswap (m.readW Q 32)
  let c2 := decide (2 ^ 32 ≤ a2.toNat + (1 : BitVec 32).toNat)
  let c1 := cout a1 c2
  ((m.writeW (Q + BitVec.ofNat 64 8) (bswap (a2 + 1))).writeW (Q + BitVec.ofNat 64 4) (bswap (adc0 a1 c2))).writeW
    Q (bswap (adc0 a0 c1))

theorem carry_ok (s : State) {Q : Addr} (hq : (s.gpr .edx).setWidth 64 = Q) (hfit : (s.gpr .edx).toNat + 16 ≤ 2 ^ 32)
    (hr : ∀ d n, d + n ≤ 16 → InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 d) n)
    (hw : ∀ d n, d + n ≤ 16 → InRegions s.wr (Q + BitVec.ofNat 64 d) n) :
    ∃ s', runBlock isa carry s = some s' ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .ebx → s'.gpr r = s.gpr r) ∧
      s'.mem = carryMem s.mem Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have a (d : Nat) (hd : d < 16) : addr (s.gpr .edx) d = Q + BitVec.ofNat 64 d := by
    rw [addr_eq (by omega_using [hfit, hd]), hq]
  have a0 : addr (s.gpr .edx) 0 = Q := by rw [a 0 (by decide)]; simp
  have r0 : InRegions (s.rd ++ s.wr) Q 4 := by simpa using hr 0 4 (by decide)
  have w0 : InRegions s.wr Q 4 := by simpa using hw 0 4 (by decide)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, carry, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load32, State.store32, ea_at', execAlu, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, cf_setReg, cf_arithFlags, a0, a 4 (by decide), a 8 (by decide),
      r0, hr 4 4 (by decide), hr 8 4 (by decide), w0, hw 4 4 (by decide), hw 8 4 (by decide)]
    rfl, ?_⟩
  refine ⟨fun r h₁ h₂ h₃ => ?_, rfl, rfl, rfl⟩
  simp [gpr_setReg, h₁, h₂, h₃]

theorem carryMem_bytes (m : Mem) (Q : Addr) :
    bytesAt (carryMem m Q) Q 16 = ofNat (toNat (bytesAt m Q 16) + 2 ^ 32) 16 := by
  have c2 : (decide (2 ^ 32 ≤ (bswap (m.readW (Q + BitVec.ofNat 64 8) 32)).toNat + (1 : BitVec 32).toNat)).toNat =
      ((bswap (m.readW (Q + BitVec.ofNat 64 8) 32)).toNat + 1) / 2 ^ 32 := by
    have := (bswap (m.readW (Q + BitVec.ofNat 64 8) 32)).isLt
    have e₁ : (1 : BitVec 32).toNat = 1 := rfl
    rw [e₁]
    by_cases h : 2 ^ 32 ≤ (bswap (m.readW (Q + BitVec.ofNat 64 8) 32)).toNat + 1
    · rw [decide_eq_true h]; simp only [Bool.toNat_true]; omega_using [h, this]
    · rw [decide_eq_false h]; simp only [Bool.toNat_false]; omega_using [h]
  apply carry_words32
  · show (bswap _ + 1).toNat = ((bswap _).toNat + 1) % 2 ^ 32
    rw [BitVec.toNat_add]; rfl
  · show (adc0 _ _).toNat = _
    rw [adc0_toNat, c2]; rfl
  · show (adc0 _ _).toNat = _
    rw [adc0_toNat, cout_toNat, c2]; rfl

theorem carryMem_frame (m : Mem) (Q : Addr) : Frame [⟨Q, 16⟩] m (carryMem m Q) :=
  (((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains_base Q (d := 8) (n := 4) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base Q (d := 4) (n := 4) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (by simpa using Offset.contains_base Q (d := 0) (n := 4) (k := 16) (by decide) (by decide))

/-! ## The call -/

section
variable {s₀ : State} (hp : XPre s₀)
include hp

/-- What the call leaves, after `k` blocks. -/
structure Mid32 (s₀ : State) (k : Nat) (s : State) : Prop where
  esi : s.gpr .esi = D32 s₀ k
  edi : s.gpr .edi = BitVec.ofNat 32 (mOf s₀ k)
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stk32 s₀] (savedMem s₀) s.mem
  data : Spec.Cbc.blocksAt s.mem ((Dp s₀).setWidth 64) (N s₀) =
    outK AesCtr.ctrMode s₀ (k + mOf s₀ k) ++ (blks s₀).drop (k + mOf s₀ k)
  /-- The counter block: `t + k + m`, less `2³²` if its last 32 bits
  wrapped around. -/
  iv : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k < 2 ^ 32 →
    bytesAt s.mem ((Iv s₀).setWidth 64) 16 = next (iv0 s₀) (k + mOf s₀ k)
  ivw : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32 →
    bytesAt s.mem ((Iv s₀).setWidth 64) 16 = ofNat (toNat (next (iv0 s₀) k) + mOf s₀ k - 2 ^ 32) 16

/-- The call, after the code before it. -/
theorem mid_wp (v : Ctr32Impl) {k : Nat} (hk : k < N s₀) {s s₁ : State} (h : LInv32 s₀ k s)
    (a : Pre32 s₀ k s s₁) : WP isa (ctrCall v.callee) s₁ (Mid32 s₀ k) := by
  refine WP.mono (Proof.AesCcm.X86.ctrFrame_ok v a.call) fun s₂ c => ?_
  obtain hm0 := mOf_pos hk
  obtain hle := mOf_le s₀ k
  have hdf := hp.u.data_fit
  obtain hesp : s₁.gpr .esp = E s₀ := by rw [a.esp, h.esp]
  obtain hd : VG.Proof.AesGcm.X86.w64 (D32 s₀ k) = blk s₀ k := hp.u.d32 hk
  have fc := c.frame
  have cout := c.out
  have cctr := c.ctr
  have cedi := a.call.edi
  rw [hesp, hp.below_eq, hd, a.mem] at fc
  rw [hd, a.mem] at cout
  rw [a.mem] at cctr
  generalize hmd : mOf s₀ k = m at hm0 hle fc cout cctr cedi
  obtain segSub : Region.Sub ⟨blk s₀ k, 16 * m⟩ (dataR s₀) := seg_sub (by omega_using [hk, hle])
  obtain fAll : Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stk32 s₀] s.mem s₂.mem :=
    fc.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨dataR s₀, by simp, segSub⟩
      · exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨stk32 s₀, by simp, fun _ h => h⟩
  -- The data and the counter block before the call.
  obtain hiv : bytesAt s.mem ((Iv s₀).setWidth 64) 16 = next (iv0 s₀) k := by
    rw [h.iv, chainK_ctr s₀ (by omega_using [hk])]
  obtain sched : bytesAt s.mem ((W s₀).setWidth 64) (16 * (R s₀ + 1)) = wK s₀ := hp.sched_bytes (big32_of h.frame)
  obtain hlen : (blks s₀).length = N s₀ := Proof.AesCbc.length_blocksAt _ _ _
  -- Blocks outside the call's.
  have outside (j : Nat) (hj : j < N s₀) (ho : j < k ∨ k + m ≤ j) :
      ∀ r ∈ [ivR s₀, ⟨blk s₀ k, 16 * m⟩, ⟨(S s₀).setWidth 64, 2048⟩, stk32 s₀],
        (⟨(Dp s₀).setWidth 64 + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint r := by
    intro r hr
    obtain dj : Region.Sub ⟨(Dp s₀).setWidth 64 + BitVec.ofNat 64 (16 * j), 16⟩ (dataR s₀) :=
      Offset.sub_base _ (by omega_using [hj])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.u.iv_data.symm.sub_left dj
    · exact Offset.disjoint _ (by omega_using [ho]) (by omega_using [hj, hdf]) (by omega_using [hk, hle, hdf])
    · exact (hp.u.data_scr.sub_left dj).sub_right (Region.sub_prefix (by decide))
    · exact hp.x_data.symm.sub_left dj
  have keepBlocks {p : Addr} {b n : Nat} (hp' : p = (Dp s₀).setWidth 64 + BitVec.ofNat 64 (16 * b))
      (hn : b + n ≤ N s₀) (ho : b + n ≤ k ∨ k + m ≤ b) :
      Spec.Cbc.blocksAt s₂.mem p n = Spec.Cbc.blocksAt s.mem p n := by
    subst hp'
    refine AesCtr.blocksAt_frame fc fun j hj r hr => ?_
    rw [Offset.add_add, show 16 * b + 16 * j = 16 * (b + j) by omega_using []]
    exact outside (b + j) (by omega_using [hj, hn]) (by omega_using [hj, ho]) r hr
  have dataS := h.data
  rw [outK, AesCtr.ctrMode_out] at dataS
  -- The call's blocks.
  obtain segIn : Spec.Cbc.blocksAt s.mem (blk s₀ k) m = ((blks s₀).drop k).take m := by
    rw [← AesCtr.blocksAt_take _ _ (show m ≤ N s₀ - k by omega_using [hle]),
      ← AesCtr.blocksAt_drop _ _ (by omega_using [hk]), dataS,
      List.drop_left' (by rw [AesCtr.length_crypt, List.length_take, hlen, Nat.min_eq_left (by omega_using [hk])])]
  obtain seg := AesCtr.ctr32_crypt (k := m) (by rw [hiv, ← hmd]; exact lo32_mOf s₀ k) cout
  rw [sched, hiv, segIn] at seg
  have g (r : Reg) (hr : r ∈ calleeSaved) : s₂.gpr r = s₁.gpr r := c.saved r hr
  refine ⟨by rw [g .esi (by simp [calleeSaved]), a.esi, h.esi], by rw [hmd, g .edi (by simp [calleeSaved]), cedi],
    by rw [g .esp (by simp [calleeSaved]), hesp], by rw [c.rd, a.rd, h.rd], by rw [c.wr, a.wr, h.wr],
    h.frame.trans fAll, ?_, ?_, ?_⟩
  · -- The data: the first `k` blocks and those after the call's as they were, and the call's.
    obtain hlc : (Spec.Ctr.crypt (Spec.Cbc.aesWith (R s₀) (wK s₀)) (iv0 s₀) ((blks s₀).take k)).length = k := by
      rw [AesCtr.length_crypt, List.length_take, hlen, Nat.min_eq_left (by omega_using [hk])]
    obtain hA : Spec.Cbc.blocksAt s.mem ((Dp s₀).setWidth 64) k =
        Spec.Ctr.crypt (Spec.Cbc.aesWith (R s₀) (wK s₀)) (iv0 s₀) ((blks s₀).take k) := by
      rw [← AesCtr.blocksAt_take _ _ (show k ≤ N s₀ by omega_using [hk]), dataS, List.take_left' hlc]
    obtain hC : Spec.Cbc.blocksAt s.mem ((Dp s₀).setWidth 64 + BitVec.ofNat 64 (16 * (k + m))) (N s₀ - (k + m)) =
        (blks s₀).drop (k + m) := by
      rw [← AesCtr.blocksAt_drop _ _ (show k + m ≤ N s₀ by omega_using [hk, hle]), dataS]
      conv => lhs; rw [show k + m = (Spec.Ctr.crypt (Spec.Cbc.aesWith (R s₀) (wK s₀)) (iv0 s₀)
        ((blks s₀).take k)).length + m by rw [hlc]]
      rw [List.drop_append, List.drop_eq_nil_of_le (by omega_using []), List.nil_append, hlc, Nat.add_sub_cancel_left]
      exact List.drop_drop
    rw [hmd, AesCtr.blocksAt_three s₂.mem ((Dp s₀).setWidth 64) (a := k) (b := m) (by omega_using [hk, hle]),
      keepBlocks (b := 0) (by simp) (by omega_using [hk]) (by omega_using []),
      keepBlocks (b := k + m) rfl (by omega_using [hk, hle]) (by omega_using []),
      show (Dp s₀).setWidth 64 + BitVec.ofNat 64 (16 * k) = blk s₀ k from rfl, seg, hA, hC, outK, AesCtr.ctrMode_out]
    exact AesCtr.crypt_step _ _ _ (by omega_using [hk, hle, hlen])
  · intro hw
    rw [hmd] at hw
    rw [hmd, AesCtr.ctr32_next (by rw [hiv]; omega_using [hw]) cctr, hiv, AesCtr.next_add]
  · intro hw
    rw [hmd] at hw
    rw [hmd, AesCtr.ctr32_wrap (by rw [hiv]; omega_using [hw]) cctr, hiv]

end

/-! ## After the call -/

theorem adv_eq : adv = [.mov .eax (.reg .edi), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
    .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .esi (.reg .eax), .mov .edx (argOp 2),
    .mov .eax (.mem (at_ .edx 12)), .alu .test .eax (.reg .eax)] := rfl

theorem done_eq : done = [.mov .eax (argOp 4), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
    .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (argOp 3),
    .alu .cmp .esi (.reg .eax)] := rfl

/-- `esi` has reached `data + 16 n` after `0 < j ≤ n` blocks exactly when
`j = n`. -/
theorem done_zf {D n : BitVec 32} {j : Nat} (hj0 : 0 < j) (hj : j ≤ n.toNat)
    (hfit : D.toNat + 16 * n.toNat ≤ 2 ^ 32) :
    (D + BitVec.ofNat 32 (16 * j) - ((n + n + (n + n) + (n + n + (n + n)) +
      (n + n + (n + n) + (n + n + (n + n)))) + D) == 0) = decide (j = n.toNat) := by
  rw [VG.Proof.CmacAes.X86.dbl4, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj]
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]
  have := D.isLt
  have h0 : (0 : BitVec 32).toNat = 0 := rfl
  omega

section
variable {s₀ : State} (hp : XPre s₀)
include hp

/-- What `adv` leaves. -/
structure After32 (s₀ : State) (k : Nat) (s s₂ : State) : Prop where
  gpr : ∀ r, r ≠ .eax → r ≠ .edx → r ≠ .esi → s₂.gpr r = s.gpr r
  esi : s₂.gpr .esi = D32 s₀ (k + mOf s₀ k)
  edx : s₂.gpr .edx = Iv s₀
  mem : s₂.mem = s.mem
  rd : s₂.rd = s.rd
  wr : s₂.wr = s.wr
  zf : s₂.zf = some (decide (AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32))

/-- On past the call's blocks, and ZF set if the counter wrapped around. -/
theorem adv_wp {k : Nat} (hk : k < N s₀) {s : State} (h : Mid32 s₀ k s) : WP isa (.block adv) s (After32 s₀ k s) := by
  obtain hm0 := mOf_pos hk
  obtain hle := mOf_le s₀ k
  obtain hlo := lo32_mOf s₀ k
  have hn16 := hp.n16
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have hargs : ∀ i < 6, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i :=
    fun i hi => hp.arg_keep (big32_of h.frame) hi
  have hiv : (arg s₀ 2).toNat + 16 ≤ 2 ^ 32 := hp.u.iv_fit
  rw [adv_eq]
  refine wp_mov fun s₁ u₁ => ?_
  refine wp_add fun s₂ u₂ => wp_add fun s₃ u₃ => wp_add fun s₄ u₄ => wp_add fun s₅ u₅ => ?_
  refine wp_add fun s₆ u₆ => ?_
  have esp₆ : s₆.gpr .esp = s₀.gpr .esp := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.esp]
  have rw₆ : s₆.rd ++ s₆.wr = s₀.rd ++ s₀.wr := by
    rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]
  have m₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine wp_arg (s₀ := s₀) esp₆ (by rw [rw₆]; exact hp.u.arg_in (by decide))
    (by rw [m₆]; exact hargs 2 (by decide)) fun s₇ u₇ => ?_
  refine wp_movm (a := (Iv s₀).setWidth 64 + BitVec.ofNat 64 12)
    (by rw [ea_at', u₇.gpr]; exact addr_eq (by omega_using [hiv]))
    (by rw [u₇.rd, u₇.wr, rw₆, hp.u.rd, hp.u.wr]
        exact ⟨ivR s₀, by simp, Offset.contains_base _ (by decide) (by decide)⟩) fun s₈ u₈ => ?_
  refine wp_test fun s₉ f₉ z₉ => WP.block_nil ⟨fun r h₁ h₂ h₃ => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f₉.gpr, u₈.other _ h₁, u₇.other _ h₂, u₆.other _ h₃, u₅.other _ h₁, u₄.other _ h₁, u₃.other _ h₁,
      u₂.other _ h₁, u₁.other _ h₁]
  · have e16 : s₅.gpr .eax = BitVec.ofNat 32 (16 * mOf s₀ k) := by
      rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, h.edi, VG.Proof.CmacAes.X86.dbl4, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega_using [hk, hle, hn16])]
    rw [f₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.esi, e16,
      D32, D32, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]
  · rw [f₉.gpr, u₈.other _ (by decide), u₇.gpr]
  · rw [f₉.mem, u₈.mem, u₇.mem, m₆]
  · rw [f₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [f₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · -- The counter's last 32 bits are zero exactly when they wrapped around.
    obtain hb := AesCtr.toNat_lt (show (next (iv0 s₀) k).length = 16 by
      rw [AesCtr.next_eq (length_iv0 s₀)]; exact AesCtr.length_ofNat _ _)
    obtain hlo2 := AesCtr.lo32_bytesAt s.mem ((Iv s₀).setWidth 64)
    rw [z₉, u₈.gpr, u₇.mem, m₆, BitVec.and_self]
    by_cases hw : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32
    · have e := h.ivw hw
      rw [e, AesCtr.lo32, AesCtr.toNat_ofNat] at hlo2
      have hw' := hw
      unfold AesCtr.lo32 at hw'
      have : (AesCtr.rv32 (s.mem.readW ((Iv s₀).setWidth 64 + BitVec.ofNat 64 12) 32)).toNat = 0 := by
        rw [← hlo2]; omega_using [hw', hb]
      obtain h0 := AesCtr.rv32_eq_zero.mp (BitVec.eq_of_toNat_eq this)
      simp [h0, hw]
    · have e := h.iv (by omega_using [hw, hlo])
      rw [e, AesCtr.lo32_next (length_iv0 s₀)] at hlo2
      rw [AesCtr.lo32_next (length_iv0 s₀)] at hw hlo
      have : (AesCtr.rv32 (s.mem.readW ((Iv s₀).setWidth 64 + BitVec.ofNat 64 12) 32)).toNat ≠ 0 := by
        rw [← hlo2]; omega_using [hw, hlo, hm0]
      obtain h0 : s.mem.readW ((Iv s₀).setWidth 64 + BitVec.ofNat 64 12) 32 ≠ 0 := fun h0 => this (by rw [h0]; rfl)
      rw [AesCtr.lo32_next (length_iv0 s₀)]
      simp only [hw, decide_false, Option.some.injEq, beq_eq_false_iff_ne]
      exact h0

end

section
variable {s₀ : State} (hp : XPre s₀)
include hp

/-- ZF set if no blocks are left. -/
theorem done_wp {j : Nat} (hj0 : 0 < j) (hj : j ≤ N s₀) {s : State} (hesi : s.gpr .esi = D32 s₀ j)
    (hesp : s.gpr .esp = E s₀) (hargs : ∀ i < 6, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i)
    (hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr) :
    WP isa (.block done) s fun s' => (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.zf = some (decide (j = N s₀)) := by
  rw [done_eq]
  refine wp_arg (s₀ := s₀) hesp (by rw [hrw]; exact hp.u.arg_in (by decide)) (hargs 4 (by decide)) fun s₁ u₁ => ?_
  refine wp_add fun s₂ u₂ => wp_add fun s₃ u₃ => wp_add fun s₄ u₄ => wp_add fun s₅ u₅ => ?_
  refine wp_addArg (s₀ := s₀)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hesp])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]
        exact hp.u.arg_in (by decide))
    (by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact hargs 3 (by decide)) fun s₆ u₆ => ?_
  refine wp_cmp fun s₇ f₇ _ z₇ => WP.block_nil ⟨fun r h₁ => ?_, ?_, ?_, ?_, ?_⟩
  · rw [f₇.gpr, u₆.other _ h₁, u₅.other _ h₁, u₄.other _ h₁, u₃.other _ h₁, u₂.other _ h₁, u₁.other _ h₁]
  · rw [f₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [f₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [f₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [z₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hesi, u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
    exact congrArg some (done_zf hj0 hj hp.u.data_fit)

/-- The invariant after `k + m` blocks, from the facts the iteration ends with. -/
theorem finish {k m : Nat} (hkm : k + m ≤ N s₀) {s s' : State} (h : Mid32 s₀ k s) (hmd : mOf s₀ k = m)
    (esi : s'.gpr .esi = D32 s₀ (k + m)) (esp : s'.gpr .esp = E s₀)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame [ivR s₀] s.mem s'.mem)
    (hiv : bytesAt s'.mem ((Iv s₀).setWidth 64) 16 = next (iv0 s₀) (k + m)) :
    LInv32 s₀ (k + m) s' where
  esi := esi
  esp := esp
  rd := by rw [hrd, h.rd]
  wr := by rw [hwr, h.wr]
  frame := h.frame.trans (hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨ivR s₀, by simp, fun _ h => h⟩)
  data := by
    rw [AesCtr.blocksAt_frame hf (fun j hj r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.u.iv_data.symm.sub_left (Offset.sub_base _ (by omega_using [hj]))), h.data, hmd]
  iv := by rw [hiv, chainK_ctr s₀ hkm]

/-- The carry if the counter wrapped around, and ZF set if no blocks are
left. -/
theorem fin_wp {k : Nat} (hk : k < N s₀) {s s₂ : State} (h : Mid32 s₀ k s) (a : After32 s₀ k s s₂) :
    WP isa (.seq (.ite .e (.block carry) (.block [])) (.block done)) s₂
      fun s' => LInv32 s₀ (k + mOf s₀ k) s' ∧ s'.zf = some (decide (k + mOf s₀ k = N s₀)) := by
  obtain hm0 := mOf_pos hk
  obtain hle := mOf_le s₀ k
  have hkm : k + mOf s₀ k ≤ N s₀ := by omega_using [hk, hle]
  have hivf : (arg s₀ 2).toNat + 16 ≤ 2 ^ 32 := hp.u.iv_fit
  have hargs : ∀ i < 6, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i :=
    fun i hi => hp.arg_keep (big32_of h.frame) hi
  have hrw : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [a.rd, a.wr, h.rd, h.wr]
  have esp₂ : s₂.gpr .esp = E s₀ := by rw [a.gpr _ (by decide) (by decide) (by decide), h.esp]
  refine WP.seq ?_
  by_cases hw : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32
  · have ev : isa.eval .e s₂ = some true := by
      show s₂.zf = _; rw [a.zf]; simp [hw]
    refine WP.ite true ev (fun _ => ?_) (fun h => by cases h)
    have inIv (d n : Nat) (hdn : d + n ≤ 16) :
        (ivR s₀).Contains ((Iv s₀).setWidth 64 + BitVec.ofNat 64 d) n :=
      Offset.contains_base _ hdn (by omega_using [hdn])
    obtain ⟨s₃, run₃, g₃, mem₃, rd₃, wr₃⟩ := carry_ok s₂ (Q := (Iv s₀).setWidth 64) (by rw [a.edx])
      (by rw [a.edx]; exact hivf)
      (fun d n hdn => by rw [hrw, hp.u.rd, hp.u.wr]; exact ⟨ivR s₀, by simp, inIv d n hdn⟩)
      (fun d n hdn => by rw [a.wr, h.wr, hp.u.wr]; exact ⟨ivR s₀, by simp, inIv d n hdn⟩)
    refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
    have f₃ : Frame [ivR s₀] s.mem s₃.mem := by rw [mem₃, a.mem]; exact carryMem_frame _ _
    have esi₃ : s₃.gpr .esi = D32 s₀ (k + mOf s₀ k) := by rw [g₃ _ (by decide) (by decide) (by decide), a.esi]
    have esp₃ : s₃.gpr .esp = E s₀ := by rw [g₃ _ (by decide) (by decide) (by decide), esp₂]
    have hargs₃ : ∀ i < 6, s₃.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi =>
      (f₃.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.u.args_iv.sub_left (hp.u.arg_sub hi)) (by decide)).trans (hargs i hi)
    refine WP.mono (done_wp hp (by omega_using [hm0]) hkm esi₃ esp₃ hargs₃ (by rw [rd₃, wr₃, hrw]))
      fun s₄ ⟨g₄, mem₄, rd₄, wr₄, z₄⟩ => ⟨?_, z₄⟩
    refine finish hp hkm h rfl (by rw [g₄ _ (by decide), esi₃]) (by rw [g₄ _ (by decide), esp₃])
      (by rw [rd₄, rd₃, a.rd]) (by rw [wr₄, wr₃, a.wr]) (by rw [mem₄]; exact f₃) ?_
    rw [mem₄, mem₃, carryMem_bytes, a.mem, h.ivw hw]
    exact AesCtr.carry_next (length_iv0 s₀) hw
  · have ev : isa.eval .e s₂ = some false := by
      show s₂.zf = _; rw [a.zf]; simp [hw]
    refine WP.ite false ev (fun h => by cases h) (fun _ => WP.block_nil ?_)
    refine WP.mono (done_wp hp (by omega_using [hm0]) hkm a.esi esp₂ (by rw [a.mem]; exact hargs) hrw)
      fun s₄ ⟨g₄, mem₄, rd₄, wr₄, z₄⟩ => ⟨?_, z₄⟩
    refine finish hp hkm h rfl (by rw [g₄ _ (by decide), a.esi]) (by rw [g₄ _ (by decide), esp₂])
      (by rw [rd₄, a.rd]) (by rw [wr₄, a.wr]) (by rw [mem₄, a.mem]; exact Frame.refl _ _) ?_
    rw [mem₄, a.mem, h.iv (by have := lo32_mOf s₀ k; omega_using [hw, this])]

/-- One iteration. -/
theorem iter_wp (v : Ctr32Impl) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv32 s₀ k s) :
    WP isa (body32 v.callee) s
      fun s' => LInv32 s₀ (k + mOf s₀ k) s' ∧ s'.zf = some (decide (k + mOf s₀ k = N s₀)) :=
  WP.seq (WP.mono (pre_wp hp hk h) fun _ a =>
    WP.seq (WP.mono (mid_wp hp v hk h a) fun _ hm =>
      WP.seq (WP.mono (adv_wp hp hk hm) fun _ x => fin_wp hp hk hm x)))

/-- The loop, from `k` blocks to all of them. -/
theorem loop_wp (v : Ctr32Impl) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv32 s₀ k s) :
    WP isa (.loop (body32 v.callee) .ne) s (LInv32 s₀ (N s₀)) := by
  refine WP.loop (M := isa) (body := body32 v.callee) (c := .ne) (Q := LInv32 s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv32 s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨j, rfl, hj, h⟩
  refine WP.mono (iter_wp hp v hj h) fun s' ⟨h', hz⟩ => ?_
  obtain hm0 := mOf_pos hj
  obtain hle := mOf_le s₀ j
  obtain ev : isa.eval .ne s' = some !decide (j + mOf s₀ j = N s₀) := by
    show VG.X86.eval .ne s' = _; rw [VG.Proof.MdStream.X86.eval_ne, hz]; rfl
  by_cases hz' : j + mOf s₀ j = N s₀
  · left
    refine ⟨by rw [ev]; simp [hz'], ?_⟩
    rwa [← hz']
  · right
    refine ⟨by rw [ev]; simp [hz'], N s₀ - (j + mOf s₀ j), by omega_using [hj, hm0], j + mOf s₀ j, rfl,
      by omega_using [hj, hle, hz'], h'⟩

end

/-- The whole function. -/
theorem crypt32_wp (v : Ctr32Impl) {s₀ : State} (h0 : ctr32X86.pre s₀) :
    WP isa (crypt32 v.callee) s₀ fun s' => abiPreserved s₀ s' ∧ ctr32X86.post s₀ s' :=
  ends_wp32 h0 fun hp hN _ h => loop_wp hp v hN h

/-! ## Constant time

The taint analysis does not analyse frames, so two runs from states that
agree on the public arguments and on the last 32 bits of the counter block
(`ctr32X86.pub`, which the contract's `leak` declares) are related piece by
piece (`RelCT`), as AES-CBC's are (`Proof/AesCbc/X86/CT.lean`): the taint
analysis covers the code between the call and the branches, from `esp`, the
stack arguments and the registers the correctness proof pins to the public
data; the call is constant time by its own proof (AES-GCM's `ctr_ct`), with
the same arguments in both runs, since the number of blocks it takes
depends only on the public data (`mOf_eq`); and the branches (the carry,
the loop) are on facts the correctness proof gives in terms of the public
data (`After32.zf`, `iter_wp`). -/

theorem LInv32.pt {s₀ : State} (hp : XPre s₀) {k : Nat} {s : State} (h : LInv32 s₀ k s) : Pt s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.arg_keep (big32_of h.frame) hi⟩

theorem Mid32.pt {s₀ : State} (hp : XPre s₀) {k : Nat} {s : State} (h : Mid32 s₀ k s) : Pt s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.arg_keep (big32_of h.frame) hi⟩

theorem pre_taint : ∃ h, (taint.check (argTaint [.esi] (4 + 4 * 6)) (.block (count ++ args)) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem adv_taint : ∃ h, (taint.check (argTaint [.esi, .edi] (4 + 4 * 6)) (.block adv) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem carry_taint : ∃ h, (taint.check (τr [.edx]) (.block carry) h).isSome = true := ⟨_, by taint_decide⟩

theorem done_taint : ∃ h, (taint.check (argTaint [.esi] (4 + 4 * 6)) (.block done) h).isSome = true :=
  ⟨_, by taint_decide⟩

section
variable {s₀ s₀' : State} (hq : (modeX86 AesCtr.ctrMode).pub s₀ s₀')
  (hl : AesCtr.lo32 (iv0 s₀) = AesCtr.lo32 (iv0 s₀'))
include hq hl

omit hq in
theorem lo32_next_eq (k : Nat) : AesCtr.lo32 (next (iv0 s₀) k) = AesCtr.lo32 (next (iv0 s₀') k) := by
  rw [AesCtr.lo32_next (length_iv0 _), AesCtr.lo32_next (length_iv0 _)]
  unfold AesCtr.lo32 at hl
  omega_using [hl]

theorem mOf_eq (k : Nat) : mOf s₀ k = mOf s₀' k := by
  have e := lo32_next_eq hl k
  rw [AesCtr.lo32_next (length_iv0 _), AesCtr.lo32_next (length_iv0 _)] at e
  unfold mOf
  rw [e, pub_N hq]

omit hl in
theorem pub_Iv : Iv s₀ = Iv s₀' := pub_arg hq (by decide)

/-- What the two runs agree on between the carry and the last test. -/
structure Fin32 (s₀ : State) (j : Nat) (s : State) : Prop where
  esi : s.gpr .esi = D32 s₀ j
  pt : Pt s₀ s

omit hq hl in
/-- The carry, for the code after it. -/
theorem carry_fin {s₀ : State} (hp : XPre s₀) {k : Nat} {s s₂ : State} (h : Mid32 s₀ k s)
    (a : After32 s₀ k s s₂) : WP isa (.block carry) s₂ (Fin32 s₀ (k + mOf s₀ k)) := by
  have hivf : (arg s₀ 2).toNat + 16 ≤ 2 ^ 32 := hp.u.iv_fit
  have hrw : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [a.rd, a.wr, h.rd, h.wr]
  have inIv (d n : Nat) (hdn : d + n ≤ 16) :
      (ivR s₀).Contains ((Iv s₀).setWidth 64 + BitVec.ofNat 64 d) n :=
    Offset.contains_base _ hdn (by omega_using [hdn])
  obtain ⟨s₃, run₃, g₃, mem₃, rd₃, wr₃⟩ := carry_ok s₂ (Q := (Iv s₀).setWidth 64) (by rw [a.edx])
    (by rw [a.edx]; exact hivf)
    (fun d n hdn => by rw [hrw, hp.u.rd, hp.u.wr]; exact ⟨ivR s₀, by simp, inIv d n hdn⟩)
    (fun d n hdn => by rw [a.wr, h.wr, hp.u.wr]; exact ⟨ivR s₀, by simp, inIv d n hdn⟩)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have f₃ : Frame [ivR s₀] s.mem s₃.mem := by rw [mem₃, a.mem]; exact carryMem_frame _ _
  exact ⟨by rw [g₃ _ (by decide) (by decide) (by decide), a.esi],
    by rw [g₃ _ (by decide) (by decide) (by decide), a.gpr _ (by decide) (by decide) (by decide), h.esp],
    by rw [wr₃, a.wr, h.wr], fun i hi =>
      (f₃.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.u.args_iv.sub_left (hp.u.arg_sub hi)) (by decide)).trans
        (hp.arg_keep (big32_of h.frame) hi)⟩

/-- One iteration, in two runs. -/
theorem body_rel (v : Ctr32Impl) (hp : XPre s₀) (hp' : XPre s₀') {k : Nat} (hk : k < N s₀) :
    RelCT isa (fun a b => LInv32 s₀ k a ∧ LInv32 s₀' k b) (body32 v.callee)
      fun a b => (LInv32 s₀ (k + mOf s₀ k) a ∧ a.zf = some (decide (k + mOf s₀ k = N s₀))) ∧
        (LInv32 s₀' (k + mOf s₀' k) b ∧ b.zf = some (decide (k + mOf s₀' k = N s₀'))) := by
  have hk' : k < N s₀' := by rw [← pub_N hq]; exact hk
  obtain ⟨_, hA⟩ := pre_taint
  obtain ⟨_, hB⟩ := adv_taint
  obtain ⟨_, hC⟩ := carry_taint
  obtain ⟨_, hD⟩ := done_taint
  -- The code before the call.
  have p1 := ((RelCT.taint (A := taint) (P := fun a b => LInv32 s₀ k a ∧ LInv32 s₀' k b)
    (argTaint [.esi] (4 + 4 * 6))
    (fun _ _ h => Pt.agree hq hp.u hp'.u (h.1.pt hp) (h.2.pt hp') fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.esi, h.2.esi, pub_Dp hq]) hA).wp
    (F₁ := fun s₁ => ∃ s, LInv32 s₀ k s ∧ Pre32 s₀ k s s₁)
    (F₂ := fun s₁ => ∃ s, LInv32 s₀' k s ∧ Pre32 s₀' k s s₁)
    fun a b h => ⟨WP.mono (pre_wp hp hk h.1) fun _ x => ⟨a, h.1, x⟩,
      WP.mono (pre_wp hp' hk' h.2) fun _ x => ⟨b, h.2, x⟩⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  -- The call, with the same arguments in both runs.
  have c2 : RelCT isa (fun a b => (∃ s, LInv32 s₀ k s ∧ Pre32 s₀ k s a) ∧ (∃ s, LInv32 s₀' k s ∧ Pre32 s₀' k s b))
      (ctrCall v.callee) fun _ _ => True :=
    RelCT.mono (Proof.AesGcm.X86.ctr_ct ⟨v, .scalar⟩
      (I := fun s => CtrCall s (W s₀) (Iv s₀) (D32 s₀ k) (S s₀) (R s₀) (mOf s₀ k) ∧ s.gpr .esp = E s₀)
      fun _ h => h)
      (fun a b h => by
        obtain ⟨⟨s, hs, pa⟩, ⟨t, ht, pb⟩⟩ := h
        refine ⟨⟨pa.call, by rw [pa.esp, hs.esp]⟩, ?_, by rw [pb.esp, ht.esp, pub_E hq]⟩
        rw [pub_W hq, pub_Iv hq, pub_D32 hq k, pub_S hq, pub_R hq, mOf_eq hq hl k]; exact pb.call)
      (fun _ _ h => h)
  have p2 := c2.wp (F₁ := Mid32 s₀ k) (F₂ := Mid32 s₀' k) fun a b h => by
    obtain ⟨⟨s, hs, pa⟩, ⟨t, ht, pb⟩⟩ := h
    exact ⟨mid_wp hp v hk hs pa, mid_wp hp' v hk' ht pb⟩
  -- On past the call's blocks.
  have p3 := ((RelCT.taint (A := taint) (P := fun a b => Mid32 s₀ k a ∧ Mid32 s₀' k b)
    (argTaint [.esi, .edi] (4 + 4 * 6))
    (fun _ _ h => Pt.agree hq hp.u hp'.u (h.1.pt hp) (h.2.pt hp') fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.esi, h.2.esi, pub_D32 hq]
      · rw [h.1.edi, h.2.edi, mOf_eq hq hl]) hB).wp
    (F₁ := fun s₂ => ∃ s, Mid32 s₀ k s ∧ After32 s₀ k s s₂)
    (F₂ := fun s₂ => ∃ s, Mid32 s₀' k s ∧ After32 s₀' k s s₂)
    fun a b h => ⟨WP.mono (adv_wp hp hk h.1) fun _ x => ⟨a, h.1, x⟩,
      WP.mono (adv_wp hp' hk' h.2) fun _ x => ⟨b, h.2, x⟩⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  -- The carry if the counter wrapped around in both runs, and the test.
  have p4 : RelCT isa (fun a b => (∃ s, Mid32 s₀ k s ∧ After32 s₀ k s a) ∧ (∃ s, Mid32 s₀' k s ∧ After32 s₀' k s b))
      (.seq (.ite .e (.block carry) (.block [])) (.block done)) fun _ _ => True := by
    refine RelCT.seq (R := fun a b => Fin32 s₀ (k + mOf s₀ k) a ∧ Fin32 s₀' (k + mOf s₀' k) b)
      (RelCT.ite (fun a b h => ?_) ?_ (RelCT.nil fun a b h => ?_)) ?_
    · obtain ⟨⟨s, hs, xa⟩, ⟨t, ht', xb⟩⟩ := h
      show a.zf = b.zf
      rw [xa.zf, xb.zf, lo32_next_eq hl, mOf_eq hq hl]
    · refine ((RelCT.taint (A := taint) (τr [.edx]) (fun a b h => agree_regs fun r hr => ?_) hC).wp
        (F₁ := Fin32 s₀ (k + mOf s₀ k)) (F₂ := Fin32 s₀' (k + mOf s₀' k)) fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      · obtain ⟨⟨⟨s, hs, xa⟩, ⟨t, ht', xb⟩⟩, _⟩ := h
        simp only [List.mem_singleton] at hr; subst hr
        rw [xa.edx, xb.edx, pub_Iv hq]
      · obtain ⟨⟨⟨s, hs, xa⟩, ⟨t, ht', xb⟩⟩, _⟩ := h
        exact ⟨carry_fin hp hs xa, carry_fin hp' ht' xb⟩
    · obtain ⟨⟨⟨s, hs, xa⟩, ⟨t, ht', xb⟩⟩, _⟩ := h
      exact ⟨⟨xa.esi, by rw [xa.gpr _ (by decide) (by decide) (by decide), hs.esp], by rw [xa.wr, hs.wr],
          fun i hi => by rw [xa.mem]; exact hp.arg_keep (big32_of hs.frame) hi⟩,
        ⟨xb.esi, by rw [xb.gpr _ (by decide) (by decide) (by decide), ht'.esp], by rw [xb.wr, ht'.wr],
          fun i hi => by rw [xb.mem]; exact hp'.arg_keep (big32_of ht'.frame) hi⟩⟩
    · exact RelCT.taint (A := taint) (argTaint [.esi] (4 + 4 * 6))
        (fun _ _ h => Pt.agree hq hp.u hp'.u h.1.pt h.2.pt fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [h.1.esi, h.2.esi, mOf_eq hq hl, pub_D32 hq]) hD
  have p5 := p4.wp
    (F₁ := fun (s' : State) => LInv32 s₀ (k + mOf s₀ k) s' ∧ s'.zf = some (decide (k + mOf s₀ k = N s₀)))
    (F₂ := fun (s' : State) => LInv32 s₀' (k + mOf s₀' k) s' ∧ s'.zf = some (decide (k + mOf s₀' k = N s₀')))
    fun a b h => by
      obtain ⟨⟨s, hs, xa⟩, ⟨t, ht', xb⟩⟩ := h
      exact ⟨fin_wp hp hk hs xa, fin_wp hp' hk' ht' xb⟩
  exact p1.seq ((p2.mono (fun _ _ h => h) fun _ _ h => h.2).seq (p3.seq (p5.mono (fun _ _ h => h) fun _ _ h => h.2)))

/-- The loop's relation, with the number of blocks left. -/
def LRel32 (s₀ s₀' : State) (n : Nat) (a b : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ LInv32 s₀ k a ∧ LInv32 s₀' k b

theorem loop_rel (v : Ctr32Impl) (hp : XPre s₀) (hp' : XPre s₀') (n : Nat) :
    RelCT isa (LRel32 s₀ s₀' n) (.loop (body32 v.callee) .ne)
      fun a b => LInv32 s₀ (N s₀) a ∧ LInv32 s₀' (N s₀') b := by
  refine RelCT.loop (M := isa) (LRel32 s₀ s₀') (fun n => ?_) n
  have hN := pub_N hq
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : LRel32 s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  by_cases hk : k < N s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2.1
  have hm := mOf_eq hq hl k
  have hm0 := mOf_pos hk
  have hle := mOf_le s₀ k
  refine (body_rel hq hl v hp hp' hk).mono (fun _ _ h => ⟨h.2.2.1, h.2.2.2⟩)
    fun s₁ s₂ ⟨⟨l₁, z₁⟩, ⟨l₂, z₂⟩⟩ => ?_
  rw [← hm] at l₂
  rw [← hm, ← hN] at z₂
  have e₁ : isa.eval .ne s₁ = some !decide (k + mOf s₀ k = N s₀) := by
    show VG.X86.eval .ne s₁ = _; rw [VG.Proof.MdStream.X86.eval_ne, z₁]; rfl
  have e₂ : isa.eval .ne s₂ = some !decide (k + mOf s₀ k = N s₀) := by
    show VG.X86.eval .ne s₂ = _; rw [VG.Proof.MdStream.X86.eval_ne, z₂]; rfl
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : k + mOf s₀ k = N s₀ := by simpa using hf
    exact ⟨h0 ▸ l₁, by rw [← hN, ← h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : k + mOf s₀ k ≠ N s₀ := by simpa using ht
    exact ⟨N s₀ - (k + mOf s₀ k), by omega_using [hk, hm0], k + mOf s₀ k, rfl, by omega_using [hk, hle, h0], l₁, l₂⟩

end

/-- The whole function, in two runs that agree on the public data. -/
theorem crypt32_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : ctr32X86.pre s₀) (h0' : ctr32X86.pre s₀')
    (hq : ctr32X86.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (crypt32 v.callee) fun _ _ => True := by
  have hp := XPre.of h0
  have hp' := XPre.of h0'
  have hN := pub_N hq.1
  have pt₀ : ∀ {t : State}, Pt t t := ⟨rfl, rfl, fun _ _ => rfl⟩
  have pro := ((RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') (argTaint [] (4 + 4 * 6))
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact Pt.agree hq.1 hp.u hp'.u pt₀ pt₀ fun r hr => by simp at hr)
    (c := .block setup) (by taint_decide)).wp
    (F₁ := fun (s : State) => LInv32 s₀ 0 s ∧ s.zf = some (decide (N s₀ = 0)))
    (F₂ := fun (s : State) => LInv32 s₀' 0 s ∧ s.zf = some (decide (N s₀' = 0)))
    fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨(prologue_wp (M := AesCtr.ctrMode) hp.u).mono fun _ h => ⟨LInv32.of h.1.1, h.1.2⟩,
        (prologue_wp (M := AesCtr.ctrMode) hp'.u).mono fun _ h => ⟨LInv32.of h.1.1, h.1.2⟩⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  have ev {s : State} (h : s.zf = some (decide (N s₀ = 0))) : isa.eval .e s = some (decide (N s₀ = 0)) := by
    show VG.X86.eval .e s = _; rw [VG.Proof.MdStream.X86.eval_e, h]
  have ev' {s : State} (h : s.zf = some (decide (N s₀' = 0))) : isa.eval .e s = some (decide (N s₀ = 0)) := by
    show VG.X86.eval .e s = _; rw [VG.Proof.MdStream.X86.eval_e, h, hN]
  have mid : RelCT isa (fun a b => (LInv32 s₀ 0 a ∧ a.zf = some (decide (N s₀ = 0))) ∧
      (LInv32 s₀' 0 b ∧ b.zf = some (decide (N s₀' = 0))))
      (.ite .e (.block []) (.loop (body32 v.callee) .ne))
      (fun a b => LInv32 s₀ (N s₀) a ∧ LInv32 s₀' (N s₀') b) := by
    refine RelCT.ite (fun a b h => by rw [ev h.1.2, ev' h.2.2]) (RelCT.nil fun a b h => ?_) ?_
    · have h0 : N s₀ = 0 := by
        have := h.2; rw [ev h.1.1.2] at this; simpa using this
      exact ⟨h0 ▸ h.1.1.1, by rw [← hN, h0]; exact h.1.2.1⟩
    · refine (loop_rel hq.1 hq.2 v hp hp' (N s₀ - 0)).mono (fun a b h => ⟨0, rfl, ?_, h.1.1.1, h.1.2.1⟩)
        fun _ _ h => h
      have := h.2; rw [ev h.1.1.2] at this
      have : N s₀ ≠ 0 := by simpa using this
      omega_using [this]
  have epi := RelCT.taint (A := taint) (P := fun a b => LInv32 s₀ (N s₀) a ∧ LInv32 s₀' (N s₀') b)
    (argTaint [] (4 + 4 * 6))
    (fun _ _ h => Pt.agree hq.1 hp.u hp'.u (h.1.pt hp) (h.2.pt hp') fun r hr => by simp at hr)
    (c := .block (restore 5)) (by taint_decide)
  exact pro.seq (mid.seq epi)

theorem crypt32_ct (v : Ctr32Impl) : ConstantTime isa ctr32X86.pre ctr32X86.pub (crypt32 v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (crypt32_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `Verified` -/

theorem crypt32_spSafe (v : Ctr32Impl) : (crypt32 v.callee).all (fun i => !isa.writesSp i) = true := by
  simp only [crypt32, whole, body32, ctrCall, Code.all, v.spSafe]
  decide +kernel

/-- Correctness and constant time, for any implementation `v` of
`vg_aes_ctr32_to`, against the shared contract's on the key schedule it is
given, whose `leak` (the counter block's last four bytes) gives the
agreement on the last 32 bits of the counter block that `crypt32_ct`
assumes. -/
theorem crypt32_verified (v : Ctr32Impl) :
    Verified X86.target (crypt32 v.callee) (Proof.AesCtr.roundsContract X86.abi 32) :=
  Verified.of_correct (T := X86.target) (k := ctr32X86) (fun _ hs => crypt32_wp v hs) (crypt32_ct v)
    { pre := by sig_implies_pre [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, ctr32X86]
      -- `ctrMode.chain` counts the blocks, which are `n`.
      post := by
        intro s s' _ h
        sig_post [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes, ctr32X86, modeX86, AesCtr.ctrMode]
        sig_reduce [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes, ctr32X86, modeX86, AesCtr.ctrMode] at h
        sig_simp [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes, ctr32X86, modeX86, AesCtr.ctrMode] [] at h
        rwa [VG.Proof.AesCbc.length_blocksAt] at h
      pub := by
        have hm : ∀ s₁ s₂, (Proof.AesCtr.roundsContract X86.abi 32).pre s₁ →
            (Proof.AesCtr.roundsContract X86.abi 32).pre s₂ →
            (Proof.AesCtr.roundsContract X86.abi 32).pub s₁ s₂ → (modeX86 AesCtr.ctrMode).pub s₁ s₂ := by
          sig_implies_pub [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, X86.abi, X86.argSlots,
            X86.argVal, X86.argBytes, modeX86]
        intro s₁ s₂ h₁ h₂ h
        refine ⟨hm s₁ s₂ h₁ h₂ h, ?_⟩
        sig_pub [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, Spec.Ctr.ctrLeak, X86.abi, X86.argSlots,
          X86.argVal, X86.argBytes] at h
        sig_split h
        exact AesCtr.lo32_of_leak (Proof.Cmac.bytesAt_length _ _ _) (Proof.Cmac.bytesAt_length _ _ _)
          (by assumption)
      sat := by
        have a0 : arg sat 0 = 0x1000 := by decide
        have a1 : arg sat 1 = 10 := by decide
        have a2 : arg sat 2 = 0x2000 := by decide
        have a3 : arg sat 3 = 0x3000 := by decide
        have a4 : arg sat 4 = 0 := by decide
        have a5 : arg sat 5 = 0x4000 := by decide
        have e : argAddr sat 0 = 0x8004 := by decide
        have esp : sat.gpr .esp = 0x8000 := rfl
        sig_implies_sat [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, X86.abi, X86.argSlots,
          X86.argVal, X86.argBytes, ctr32X86] [a0, a1, a2, a3, a4, a5, e, esp] using sat }

end VG.Proof.AesCtr.X86.Ctr32
