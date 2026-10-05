import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Verified
import VerifiedGarbage.Impl.Rc2.X86_64.Stream
import VerifiedGarbage.Proof.Rc2.X86_64.Key
import VerifiedGarbage.Proof.Rc2.Stream
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Rc2.Scratch
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchWipe

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86_64.Stream.Lit`. -/
section

/-! # Literal streaming functions -/

namespace VG

materialize_code Impl.Rc2.X86_64.Stream.init
materialize_code Impl.Rc2.X86_64.Stream.encryptUpdate
materialize_code Impl.Rc2.X86_64.Stream.decryptUpdate

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86_64.Stream.Steps`. -/
section

section

section

/-! # Streaming RC2-CBC on x86-64: the byte-copy loop -/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64 VG.X86_64.RegUpd VG.WriteBytes VG.Impl.Rc2.X86_64.Stream

/-- The copy routine's registers: none is its index `r10` or byte `r11`. -/
structure CopyRegs (src dst cnt : Reg) : Prop where
  src10 : src ≠ .r10
  src11 : src ≠ .r11
  dst10 : dst ≠ .r10
  dst11 : dst ≠ .r11
  cnt10 : cnt ≠ .r10
  cnt11 : cnt ≠ .r11

theorem ea_at10 (s : State) (b : Reg) (d i : Nat) (hi : s.gpr .r10 = BitVec.ofNat 64 i) :
    s.ea (at10 b d) = s.gpr b + BitVec.ofNat 64 d + BitVec.ofNat 64 i := by
  simp only [State.ea, at10, hi, BitVec.mul_one, Int.ofNat_eq_natCast, BitVec.ofInt_natCast]
  rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 i)]

theorem copyStep_ok (s : State) {src dst cnt : Reg} (hr : VG.Proof.Rc2.X86_64.Stream.CopyRegs src dst cnt) {S D : Addr} {sd dd i n : Nat}
    (hs : s.gpr src + BitVec.ofNat 64 sd = S) (hd : s.gpr dst + BitVec.ofNat 64 dd = D)
    (hi : s.gpr .r10 = BitVec.ofNat 64 i) (hn : s.gpr cnt = BitVec.ofNat 64 n)
    (r : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) 1) (w : InRegions s.wr (D + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa (copyBody src sd dst dd cnt) s = some s' ∧
      s'.mem = s.mem.writeW (D + BitVec.ofNat 64 i) (s.mem (S + BitVec.ofNat 64 i)) ∧
      s'.gpr .r10 = BitVec.ofNat 64 i + 1 ∧
      s'.zf = some (BitVec.ofNat 64 i + 1 - BitVec.ofNat 64 n == 0) ∧
      (∀ r, r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea₁ : s.ea (at10 src sd) = S + BitVec.ofNat 64 i := by rw [VG.Proof.Rc2.X86_64.Stream.ea_at10 s src sd i hi, hs]
  have ea₂ : (s.setReg .r11 ((s.mem (S + BitVec.ofNat 64 i)).setWidth 64)).ea (at10 dst dd) =
      D + BitVec.ofNat 64 i := by
    rw [VG.Proof.Rc2.X86_64.Stream.ea_at10 _ dst dd i (by rw [gpr_setReg_of_ne _ _ (by decide)]; exact hi), gpr_setReg_of_ne _ _ hr.dst11, hd]
  have n₁ : (s.setReg .r11 ((s.mem (S + BitVec.ofNat 64 i)).setWidth 64)).gpr cnt = BitVec.ofNat 64 n := by
    rw [gpr_setReg_of_ne _ _ hr.cnt11, hn]
  refine ⟨_, by
    simp only [↓reduceIte, Nat.reducePow, BitVec.reduceSignExtend, copyBody, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, State.load8, State.store8, Option.bind_some, Option.map_some, ea₁, ea₂, r, w,
      wr_setReg, rd_setReg, mem_setReg]
    rfl, ?_⟩
  have h10 : (s.setReg .r11 ((s.mem (S + BitVec.ofNat 64 i)).setWidth 64)).gpr .r10 = BitVec.ofNat 64 i := by
    rw [gpr_setReg_of_ne _ _ (by decide), hi]
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl⟩
  · simp only [mem_arithFlags, mem_setReg, gpr_setReg_self,
      BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide), BitVec.setWidth_eq]
  · simp only [gpr_arithFlags, gpr_setReg_self, h10]; rfl
  · simp only [zf_arithFlags, gpr_setReg_self, h10, gpr_setReg_of_ne _ _ hr.cnt10, gpr_arithFlags, n₁]; rfl
  · intro r' h₁ h₂
    simp only [gpr_arithFlags, gpr_setReg_of_ne _ _ h₁, gpr_setReg_of_ne _ _ h₂]

theorem beq_zero {x : Nat} (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x == 0) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro he
    have := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this
    simpa using this
  · intro he; rw [he]; rfl

theorem guard_ok (s : State) {cnt : Reg} (hc : cnt ≠ .r10) {n : Nat} (hn : s.gpr cnt = BitVec.ofNat 64 n)
    (hn' : n < 2 ^ 64) :
    ∃ s', runBlock isa [.mov32 .r10 (.imm 0), .alu .test cnt (.reg cnt)] s = some s' ∧
      s'.gpr .r10 = BitVec.ofNat 64 0 ∧ s'.zf = some (decide (n = 0)) ∧
      (∀ r, r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu, State.setReg32,
      Option.map_some, Option.bind_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp only [gpr_arithFlags, gpr_setReg_self]; rfl
  · simp only [zf_arithFlags, gpr_setReg_of_ne _ _ hc, hn, BitVec.and_self, VG.Proof.Rc2.X86_64.Stream.beq_zero hn']
  · intro r h; simp only [gpr_arithFlags, gpr_setReg_of_ne _ _ h]

theorem succ_ofNat (i : Nat) : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := (BitVec.ofNat_add i 1).symm

/-- The copy routine: `n` bytes from `S = src + sd` to `D = dst + dd`, for
separate ranges. -/
theorem copy_ok (s : State) {src dst cnt : Reg} (hr : VG.Proof.Rc2.X86_64.Stream.CopyRegs src dst cnt) {S D : Addr} {sd dd n : Nat}
    (hs : s.gpr src + BitVec.ofNat 64 sd = S) (hd : s.gpr dst + BitVec.ofNat 64 dd = D)
    (hn : s.gpr cnt = BitVec.ofNat 64 n) (hn' : n < 2 ^ 64)
    (rd : ∀ i < n, InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) 1)
    (wr : ∀ i < n, InRegions s.wr (D + BitVec.ofNat 64 i) 1)
    (sep : (Region.mk S n).Disjoint ⟨D, n⟩) :
    WP isa (copy src sd dst dd cnt) s fun s' => s'.mem = writeBytes s.mem D (Spec.Rc2.bytesAt s.mem S n) ∧
      (∀ r, r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, r10₁, zf₁, g₁, mem₁, rd₁, wr₁⟩ := VG.Proof.Rc2.X86_64.Stream.guard_ok s hr.cnt10 hn hn'
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (by simpa [eval] using zf₁) (fun h0 => ?_) (fun h0 => ?_)
  · have h0 : n = 0 := of_decide_eq_true h0
    subst h0
    exact WP.block_nil ⟨by rw [mem₁]; simp [Spec.Rc2.bytesAt, writeBytes_nil],
      fun r h₁ _ => g₁ r h₁, rd₁, wr₁⟩
  have hn₀ : 0 < n := Nat.pos_of_ne_zero (of_decide_eq_false h0)
  refine WP.loop (M := isa) (body := .block (copyBody src sd dst dd cnt)) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .r10 = BitVec.ofNat 64 i ∧
      t.mem = writeBytes s.mem D (Spec.Rc2.bytesAt s.mem S i) ∧
      (∀ r, r ≠ .r10 → r ≠ .r11 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, hn₀, r10₁, by rw [mem₁]; simp [Spec.Rc2.bytesAt, writeBytes_nil],
      fun r h₁ _ => g₁ r h₁, rd₁, wr₁⟩
  rintro k t ⟨i, rfl, hi, r10, mem, g, trd, twr⟩
  obtain ⟨t', run', mem', r10', zf', g', rd', wr'⟩ := VG.Proof.Rc2.X86_64.Stream.copyStep_ok t hr
    (by rw [g _ hr.src10 hr.src11, hs]) (by rw [g _ hr.dst10 hr.dst11, hd]) r10
    (by rw [g _ hr.cnt10 hr.cnt11, hn]) (by rw [trd, twr]; exact rd i hi) (by rw [twr]; exact wr i hi)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (Spec.Rc2.bytesAt s.mem S i).length = i := bytesAt_length _ _ _
  have hx : writeBytes s.mem D (Spec.Rc2.bytesAt s.mem S i) (S + BitVec.ofNat 64 i) = s.mem (S + BitVec.ofNat 64 i) :=
    (writeBytes_frame s.mem D _ (R := ⟨D, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact sep _ (Offset.contains_base S (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)
  have hmem : t'.mem = writeBytes s.mem D (Spec.Rc2.bytesAt s.mem S (i + 1)) := by
    rw [mem', mem, hx, bytesAt_succ, writeBytes_snoc s.mem D (Spec.Rc2.bytesAt s.mem S i)
      (s.mem (S + BitVec.ofNat 64 i)) (by rw [hlen]; omega), hlen]
  have hz : t'.zf = some (decide (i + 1 = n)) := by
    rw [zf', VG.Proof.Rc2.X86_64.Stream.succ_ofNat, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  have gg : ∀ r, r ≠ .r10 → r ≠ .r11 → t'.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g' r h₁ h₂, g r h₁ h₂]
  by_cases he : i + 1 = n
  · left
    refine ⟨by simp [eval, hz, he], by rw [hmem, he], gg, by rw [rd', trd], by rw [wr', twr]⟩
  · right
    refine ⟨by simp [eval, hz, he], n - (i + 1), by omega, i + 1, rfl, by omega, by rw [r10', VG.Proof.Rc2.X86_64.Stream.succ_ofNat], hmem, gg,
      by rw [rd', trd], by rw [wr', twr]⟩

end VG.Proof.Rc2.X86_64.Stream

end

/-! # Streaming RC2-CBC on x86-64: the function-level contracts -/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64

/-- `vg_rc2_cbc_init(key = rdi, key_len = rsi, effective_bits = rdx, iv = rcx,
iv_len = r8, ctx = r9, scratch = [rsp + 8])`, which calls key expansion. -/
def initContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let iv : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let ctx : Region := ⟨s.gpr .r9, 144⟩
    let buf : Region := ⟨stackArg s 0, 576⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 8
    8 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 16 ≤ 2 ^ 64 ∧
      s.rd = [key, iv, args] ∧ s.wr = [ctx, buf] ∧
      key.Disjoint ctx ∧ key.Disjoint buf ∧ iv.Disjoint ctx ∧ iv.Disjoint buf ∧ ctx.Disjoint buf ∧
      ctx.Disjoint args ∧ buf.Disjoint args ∧
      ret.Disjoint key ∧ ret.Disjoint iv ∧ ret.Disjoint ctx ∧ ret.Disjoint buf ∧ ret.Disjoint args ∧
      stack.Disjoint key ∧ stack.Disjoint iv ∧ stack.Disjoint ctx ∧ stack.Disjoint buf ∧ stack.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r9).toNat + 144 ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + 576 ≤ 2 ^ 64
  post s s' :=
    ∀ direction, match Spec.Rc2.initWithEffectiveBits (Spec.Rc2.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
        (Spec.Rc2.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) direction (s.gpr .rdx).toNat with
      | .ok c => (s'.gpr .rax).setWidth 32 = 0 ∧ Spec.Rc2.contextAt s'.mem (s.gpr .r9) direction 0 = c
      | .error e => ((s'.gpr .rax).setWidth 32).toNat = e.code
  pub s₁ s₂ := PublicRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] s₁ s₂ ∧ stackArg s₁ 0 = stackArg s₂ 0

/-- The update functions (`ctx = rdi, pending_len = rsi, data = rdx,
len = rcx, out = r8, out_len = r9, scratch = [rsp + 8]`), which call CBC. -/
def updateContract (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .rdi, 144⟩
    let data : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let out : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let buf : Region := ⟨stackArg s 0, 576⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 16
    16 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 16 ≤ 2 ^ 64 ∧
      s.rd = [data, args] ∧ s.wr = [ctx, out, buf] ∧
      ctx.Disjoint data ∧ ctx.Disjoint out ∧ ctx.Disjoint buf ∧ ctx.Disjoint args ∧
      data.Disjoint out ∧ data.Disjoint buf ∧ out.Disjoint buf ∧ out.Disjoint args ∧ buf.Disjoint args ∧
      ret.Disjoint ctx ∧ ret.Disjoint data ∧ ret.Disjoint out ∧ ret.Disjoint buf ∧ ret.Disjoint args ∧
      stack.Disjoint ctx ∧ stack.Disjoint data ∧ stack.Disjoint out ∧ stack.Disjoint buf ∧ stack.Disjoint args ∧
      (s.gpr .rdi).toNat + 144 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + 576 ≤ 2 ^ 64 ∧
      (s.gpr .rsi).toNat < 8 ∧ (s.gpr .r9).toNat = ((s.gpr .rsi).toNat + (s.gpr .rcx).toNat) / 8 * 8
  post s s' :=
    let result := Spec.Rc2.update (Spec.Rc2.contextAt s.mem (s.gpr .rdi) d (s.gpr .rsi).toNat)
      (Spec.Rc2.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    Spec.Rc2.contextAt s'.mem (s.gpr .rdi) d (((s.gpr .rsi).toNat + (s.gpr .rcx).toNat) % 8) = result.1 ∧
      Spec.Rc2.bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat = result.2
  pub s₁ s₂ := PublicRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] s₁ s₂ ∧ stackArg s₁ 0 = stackArg s₂ 0

def updateSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rdx => 0x2000 | .r8 => 0x3000 | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6009 then 0x40 else 0
  rd := [⟨0x2000, 0⟩, ⟨0x6008, 8⟩]
  wr := [⟨0x1000, 144⟩, ⟨0x3000, 0⟩, ⟨0x4000, 576⟩]

def initSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rcx => 0x2000 | .r9 => 0x3000 | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6009 then 0x40 else 0
  rd := [⟨0x1000, 0⟩, ⟨0x2000, 0⟩, ⟨0x6008, 8⟩]
  wr := [⟨0x3000, 144⟩, ⟨0x4000, 576⟩]

theorem publicRegs_seven (s₁ s₂ : State) : PublicRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] s₁ s₂ ↔
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp := by
  simp [PublicRegs]

theorem stackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

theorem args_getD (s : State) : (s.gpr .rdi :: s.gpr .rsi :: s.gpr .rdx :: s.gpr .rcx :: s.gpr .r8 :: s.gpr .r9 ::
    List.map (stackArg s) (List.range 1)).getD 6 0 = stackArg s 0 := rfl

theorem update_implies (d : Spec.Rc2.Direction) : (VG.Proof.Rc2.X86_64.Stream.updateContract d).Implies (Proof.Rc2.cbcUpdateScratchContract abi d 16) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Proof.Rc2.cbcUpdateScratchContract, Proof.Rc2.cbcUpdateScratchSig, Spec.Rc2.cbcUpdatePre, Spec.Rc2.cbcUpdatePost, abi, argRegs, VG.Proof.Rc2.X86_64.Stream.updateContract, VG.Proof.Rc2.X86_64.Stream.publicRegs_seven, VG.Proof.Rc2.X86_64.Stream.args_getD, VG.Proof.Rc2.X86_64.Stream.stackArgs_one, List.append_eq] at h
    sig_pre [Proof.Rc2.cbcUpdateScratchContract, Proof.Rc2.cbcUpdateScratchSig, Spec.Rc2.cbcUpdatePre, Spec.Rc2.cbcUpdatePost, abi, argRegs, VG.Proof.Rc2.X86_64.Stream.updateContract, VG.Proof.Rc2.X86_64.Stream.publicRegs_seven, VG.Proof.Rc2.X86_64.Stream.args_getD, VG.Proof.Rc2.X86_64.Stream.stackArgs_one, List.append_eq] at h
    sig_split h
    sig_reduce [Proof.Rc2.cbcUpdateScratchContract, Proof.Rc2.cbcUpdateScratchSig, Spec.Rc2.cbcUpdatePre, Spec.Rc2.cbcUpdatePost, abi, argRegs, VG.Proof.Rc2.X86_64.Stream.updateContract, VG.Proof.Rc2.X86_64.Stream.publicRegs_seven, VG.Proof.Rc2.X86_64.Stream.args_getD, VG.Proof.Rc2.X86_64.Stream.stackArgs_one, List.append_eq]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
  post := by sig_implies_post [Proof.Rc2.cbcUpdateScratchContract, Proof.Rc2.cbcUpdateScratchSig, Spec.Rc2.cbcUpdatePre, Spec.Rc2.cbcUpdatePost, abi, argRegs, VG.Proof.Rc2.X86_64.Stream.updateContract, VG.Proof.Rc2.X86_64.Stream.publicRegs_seven, VG.Proof.Rc2.X86_64.Stream.args_getD, VG.Proof.Rc2.X86_64.Stream.stackArgs_one, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Proof.Rc2.cbcUpdateScratchContract, Proof.Rc2.cbcUpdateScratchSig, Spec.Rc2.cbcUpdatePre, Spec.Rc2.cbcUpdatePost, abi, argRegs, VG.Proof.Rc2.X86_64.Stream.updateContract, VG.Proof.Rc2.X86_64.Stream.publicRegs_seven, VG.Proof.Rc2.X86_64.Stream.args_getD, VG.Proof.Rc2.X86_64.Stream.stackArgs_one, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    sig_split h
    rename_i h1 h2 h3 h4 h5 h6 h7
    exact ⟨(VG.Proof.Rc2.X86_64.Stream.publicRegs_seven _ _).2 ⟨h2, h3, h4, h5, h6, h7, h1⟩, h⟩
  sat := by sig_implies_sat [Proof.Rc2.cbcUpdateScratchContract, Proof.Rc2.cbcUpdateScratchSig, Spec.Rc2.cbcUpdatePre, Spec.Rc2.cbcUpdatePost, abi, argRegs, VG.Proof.Rc2.X86_64.Stream.updateContract, VG.Proof.Rc2.X86_64.Stream.publicRegs_seven, VG.Proof.Rc2.X86_64.Stream.args_getD, VG.Proof.Rc2.X86_64.Stream.stackArgs_one, List.append_eq] [updateSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using VG.Proof.Rc2.X86_64.Stream.updateSatState

theorem init_implies : initContract.Implies (Proof.Rc2.cbcInitScratchContract abi 8) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Proof.Rc2.cbcInitScratchContract, Proof.Rc2.cbcInitScratchSig, Spec.Rc2.cbcInitPost, abi, argRegs, VG.Proof.Rc2.X86_64.Stream.initContract, VG.Proof.Rc2.X86_64.Stream.publicRegs_seven, VG.Proof.Rc2.X86_64.Stream.args_getD, VG.Proof.Rc2.X86_64.Stream.stackArgs_one, List.append_eq] at h
    sig_pre [Proof.Rc2.cbcInitScratchContract, Proof.Rc2.cbcInitScratchSig, Spec.Rc2.cbcInitPost, abi, argRegs, VG.Proof.Rc2.X86_64.Stream.initContract, VG.Proof.Rc2.X86_64.Stream.publicRegs_seven, VG.Proof.Rc2.X86_64.Stream.args_getD, VG.Proof.Rc2.X86_64.Stream.stackArgs_one, List.append_eq] at h
    sig_split h
    sig_reduce [Proof.Rc2.cbcInitScratchContract, Proof.Rc2.cbcInitScratchSig, Spec.Rc2.cbcInitPost, abi, argRegs, VG.Proof.Rc2.X86_64.Stream.initContract, VG.Proof.Rc2.X86_64.Stream.publicRegs_seven, VG.Proof.Rc2.X86_64.Stream.args_getD, VG.Proof.Rc2.X86_64.Stream.stackArgs_one, List.append_eq]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
  post := by sig_implies_post [Proof.Rc2.cbcInitScratchContract, Proof.Rc2.cbcInitScratchSig, Spec.Rc2.cbcInitPost, abi, argRegs, VG.Proof.Rc2.X86_64.Stream.initContract, VG.Proof.Rc2.X86_64.Stream.publicRegs_seven, VG.Proof.Rc2.X86_64.Stream.args_getD, VG.Proof.Rc2.X86_64.Stream.stackArgs_one, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Proof.Rc2.cbcInitScratchContract, Proof.Rc2.cbcInitScratchSig, Spec.Rc2.cbcInitPost, abi, argRegs, VG.Proof.Rc2.X86_64.Stream.initContract, VG.Proof.Rc2.X86_64.Stream.publicRegs_seven, VG.Proof.Rc2.X86_64.Stream.args_getD, VG.Proof.Rc2.X86_64.Stream.stackArgs_one, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    sig_split h
    rename_i h1 h2 h3 h4 h5 h6 h7
    exact ⟨(VG.Proof.Rc2.X86_64.Stream.publicRegs_seven _ _).2 ⟨h2, h3, h4, h5, h6, h7, h1⟩, h⟩
  sat := by sig_implies_sat [Proof.Rc2.cbcInitScratchContract, Proof.Rc2.cbcInitScratchSig, Spec.Rc2.cbcInitPost, abi, argRegs, VG.Proof.Rc2.X86_64.Stream.initContract, VG.Proof.Rc2.X86_64.Stream.publicRegs_seven, VG.Proof.Rc2.X86_64.Stream.args_getD, VG.Proof.Rc2.X86_64.Stream.stackArgs_one, List.append_eq] [initSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using VG.Proof.Rc2.X86_64.Stream.initSatState

end VG.Proof.Rc2.X86_64.Stream

end

/-! # Streaming RC2-CBC on x86-64: the straight-line blocks -/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64 VG.Impl.Rc2.X86_64.Stream

theorem toNat_eq (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by simp

/-- `test r, r`: ZF is set iff `r` is 0. -/
theorem test_ok (s : State) (r : Reg) {n : Nat} (hn : s.gpr r = BitVec.ofNat 64 n) (hn' : n < 2 ^ 64) :
    ∃ s', runBlock isa [.alu .test r (.reg r)] s = some s' ∧ s'.zf = some (decide (n = 0)) ∧ Keep [] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some]
    rfl, ?_⟩
  refine ⟨?_, ⟨fun r _ => by rw [gpr_arithFlags], rfl, rfl, rfl⟩⟩
  rw [zf_arithFlags, hn, BitVec.and_self, VG.Proof.Rc2.X86_64.Stream.beq_zero hn']

theorem shortArgs_ok (s : State) :
    ∃ s', runBlock isa [rr .rax .rdi, .alu .add .rax (.reg .rsi)] s = some s' ∧
      s'.gpr .rax = s.gpr .rdi + s.gpr .rsi ∧ Keep [.rax] s s' := by
  refine ⟨_, by
    simp only [reduceCtorEq, Nat.reducePow, not_false_eq_true, rr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, Option.bind_some, Option.map_some, gpr_setReg_self, gpr_setReg_of_ne]
    rfl, ?_⟩
  refine ⟨by rw [gpr_setReg_self], fun r hr => ?_, rfl, rfl, rfl⟩
  have hr : r ≠ .rax := by simpa using hr
  rw [gpr_setReg_of_ne _ _ hr, gpr_arithFlags, gpr_setReg_of_ne _ _ hr]

theorem toOut_ok (s : State) :
    ∃ s', runBlock isa toOut s = some s' ∧
      s'.gpr .r9 = s.gpr .r9 - s.gpr .rsi ∧ s'.gpr .r8 = s.gpr .r8 + s.gpr .rsi ∧ Keep [.r9, .r8] s s' := by
  refine ⟨_, by
    simp only [reduceCtorEq, Nat.reducePow, not_false_eq_true, toOut, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, Option.bind_some, gpr_setReg_of_ne, gpr_arithFlags]
    rfl, ?_⟩
  refine ⟨?_, by rw [gpr_setReg_self], fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [gpr_setReg_of_ne _ _ (by decide), gpr_arithFlags, gpr_setReg_self]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg_of_ne _ _ hr.2, gpr_arithFlags, gpr_setReg_of_ne _ _ hr.1]

theorem toPending_ok (s : State) :
    ∃ s', runBlock isa toPending s = some s' ∧
      s'.gpr .rdx = s.gpr .rdx + s.gpr .r9 ∧ s'.gpr .rcx = s.gpr .rcx - s.gpr .r9 ∧ Keep [.rdx, .rcx] s s' := by
  refine ⟨_, by
    simp only [reduceCtorEq, Nat.reducePow, not_false_eq_true, toPending, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, Option.bind_some, gpr_setReg_of_ne, gpr_arithFlags]
    rfl, ?_⟩
  refine ⟨?_, by rw [gpr_setReg_self], fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [gpr_setReg_of_ne _ _ (by decide), gpr_arithFlags, gpr_setReg_self]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg_of_ne _ _ hr.2, gpr_arithFlags, gpr_setReg_of_ne _ _ hr.1]

theorem cbcArgs_ok (s : State) (h : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa cbcArgs s = some s' ∧
      s'.gpr .rdi = s.gpr .rdi ∧ s'.gpr .rsi = s.gpr .rdi + 128 ∧ s'.gpr .rdx = s.gpr .r8 - s.gpr .rsi ∧
      s'.gpr .rcx = (s.gpr .r9 + s.gpr .rsi) >>> 3 ∧
      s'.gpr .r8 = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 8) 64 ∧
      Keep [.r8, .r9, .rdx, .rcx, .rsi] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [cbcArgs, rr, memOp, runBlock_cons, runStep_some, runBlock_nil,
      exec, readSrc, execAlu, execShift, State.load64, State.ea, offset_nat, Option.bind_some, Option.map_some,
      gpr_setReg_self, gpr_setReg_of_ne, gpr_arithFlags, gpr_setFlags, rd_setReg, wr_setReg, rd_arithFlags,
      wr_arithFlags, rd_setFlags, wr_setFlags, mem_setReg, mem_arithFlags, mem_setFlags, h, ite_true]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals try simp (config := {decide := true}) only [gpr_setReg_self, gpr_setReg_of_ne, gpr_arithFlags,
    gpr_setFlags, reduceCtorEq, not_false_eq_true]
  · rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hr
    simp only [gpr_setReg_of_ne _ _ h₁, gpr_setReg_of_ne _ _ h₂, gpr_setReg_of_ne _ _ h₃,
      gpr_setReg_of_ne _ _ h₄, gpr_setReg_of_ne _ _ h₅, gpr_arithFlags, gpr_setFlags]

end VG.Proof.Rc2.X86_64.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86_64.Stream.Long`. -/
section

section

/-! # Streaming RC2-CBC on x86-64: an update without a complete block -/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64 VG.X86_64.RegUpd VG.WriteBytes VG.Impl.Rc2.X86_64 VG.Impl.Rc2.X86_64.Stream

/-- With `out_len = 0` (so `pending_len + len < 8`), from a state `t` that
differs from the entry state `s` only in its flags. -/
theorem short_ok (d : Spec.Rc2.Direction) (s : State) (hs : (VG.Proof.Rc2.X86_64.Stream.updateContract d).pre s)
    (hz : (s.gpr .r9).toNat = 0) (t : State) (ht : Keep [] s t) :
    WP isa short t (fun s' => gprPreserved s s' ∧ (VG.Proof.Rc2.X86_64.Stream.updateContract d).post s s') := by
  obtain ⟨_, _, hrd, hwr, ctxData, _, _, _, _, _, _, _, _, retCtx, _, _, _, _,
    _, _, _, _, _, _, _, _, _, hp, hN⟩ := hs
  have hshort : (s.gpr .rsi).toNat + (s.gpr .rcx).toNat < 8 := by omega
  obtain ⟨t₁, run₁, rax₁, keep₁⟩ := VG.Proof.Rc2.X86_64.Stream.shortArgs_ok t
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have g₁ (r : Reg) (hr : r ≠ .rax) : t₁.gpr r = s.gpr r := (keep₁.reg r (by simpa using hr)).trans (ht.reg r (by simp))
  have rd₁ : t₁.rd = s.rd := keep₁.rd.trans ht.rd
  have wr₁ : t₁.wr = s.wr := keep₁.wr.trans ht.wr
  have mem₁ : t₁.mem = s.mem := keep₁.mem.trans ht.mem
  -- The destination, `ctx + 136 + pending_len`.
  have hD : t₁.gpr .rax + BitVec.ofNat 64 136 =
      s.gpr .rdi + BitVec.ofNat 64 (136 + (s.gpr .rsi).toNat) := by
    rw [rax₁, ht.reg _ (by simp), ht.reg _ (by simp), VG.Proof.Rc2.X86_64.Stream.toNat_eq (s.gpr .rsi), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (s.gpr .rsi).isLt, Offset.add_add, Nat.add_comm]
  have dstSub : Region.Sub ⟨s.gpr .rdi + BitVec.ofNat 64 (136 + (s.gpr .rsi).toNat), (s.gpr .rcx).toNat⟩
      ⟨s.gpr .rdi, 144⟩ := Offset.sub_base _ (by omega)
  apply WP.mono (VG.Proof.Rc2.X86_64.Stream.copy_ok t₁ (src := .rdx) (dst := .rax) (cnt := .rcx) (sd := 0) (dd := 136)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (S := s.gpr .rdx) (D := s.gpr .rdi + BitVec.ofNat 64 (136 + (s.gpr .rsi).toNat))
    (n := (s.gpr .rcx).toNat) (by rw [g₁ _ (by decide)]; exact BitVec.add_zero _) hD
    (by rw [g₁ _ (by decide)]; exact VG.Proof.Rc2.X86_64.Stream.toNat_eq _) (s.gpr .rcx).isLt
    (fun i hi => by
      rw [rd₁, wr₁, hrd]
      exact ⟨⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩)
    (fun i hi => by
      rw [wr₁, hwr, Offset.add_add]
      exact ⟨⟨s.gpr .rdi, 144⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩)
    (ctxData.symm.sub_right dstSub))
  rintro s' ⟨mem', g', rd', wr'⟩
  rw [mem₁] at mem'
  have frame : Frame [⟨s.gpr .rdi + BitVec.ofNat 64 (136 + (s.gpr .rsi).toNat), (s.gpr .rcx).toNat⟩]
      s.mem s'.mem := by
    rw [mem']
    exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · have hr' : r ≠ .rax ∧ r ≠ .r10 ∧ r ≠ .r11 := by
      revert hr; revert r; decide
    rw [g' r hr'.2.1 hr'.2.2, g₁ r hr'.1]
  · apply frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (hn := by decide)
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact retCtx.sub_right dstSub
  · show Spec.Rc2.contextAt s'.mem (s.gpr .rdi) d _ = _ ∧ _
    rw [hN]
    refine update_post_short hshort ?_ ?_ ?_
    · exact scheduleAt_frame frame _ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by omega) (by omega))
    · rw [show s.gpr .rdi + 128 = s.gpr .rdi + BitVec.ofNat 64 128 from rfl]
      exact blockAt_frame frame _ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega))
    · rw [show s.gpr .rdi + 136 = s.gpr .rdi + BitVec.ofNat 64 136 from rfl, bytesAt_add,
        show s.gpr .rdi + BitVec.ofNat 64 136 + BitVec.ofNat 64 (s.gpr .rsi).toNat =
          s.gpr .rdi + BitVec.ofNat 64 (136 + (s.gpr .rsi).toNat) from Offset.add_add _ _ _,
        Proof.Rc2.bytesAt_frame frame _ _ (by omega) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)),
        mem']
      congr 1
      have h := bytesAt_writeBytes_self s.mem (s.gpr .rdi + BitVec.ofNat 64 (136 + (s.gpr .rsi).toNat))
        (Spec.Rc2.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (by rw [bytesAt_length]; exact (s.gpr .rcx).isLt)
      rwa [bytesAt_length] at h

end VG.Proof.Rc2.X86_64.Stream

end

/-! # Streaming RC2-CBC on x86-64: the copies before CBC

With `out_len ≠ 0`: the pending bytes and the first `out_len - pending_len`
bytes of data to `out`, the rest of the data to `ctx + 136`, and the
arguments of the CBC function (`Mid`). -/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64 VG.X86_64.RegUpd VG.WriteBytes VG.Impl.Rc2.X86_64 VG.Impl.Rc2.X86_64.Stream

/-- The state before the call of the CBC function, from the entry state `s`. -/
structure Mid (s t : State) : Prop where
  rdi : t.gpr .rdi = s.gpr .rdi
  rsi : t.gpr .rsi = s.gpr .rdi + 128
  rdx : t.gpr .rdx = s.gpr .r8
  rcx : t.gpr .rcx = BitVec.ofNat 64 ((s.gpr .r9).toNat / 8)
  r8 : t.gpr .r8 = stackArg s 0
  rsp : t.gpr .rsp = s.gpr .rsp
  callee : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  /-- Memory changed only in `out` and the pending block. -/
  frame : Frame [⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨s.gpr .rdi + BitVec.ofNat 64 136, 8⟩] s.mem t.mem
  out : Spec.Rc2.bytesAt t.mem (s.gpr .r8) (s.gpr .r9).toNat =
    Spec.Rc2.bytesAt s.mem (s.gpr .rdi + 136) (s.gpr .rsi).toNat ++
      Spec.Rc2.bytesAt s.mem (s.gpr .rdx) ((s.gpr .r9).toNat - (s.gpr .rsi).toNat)
  pend : Spec.Rc2.bytesAt t.mem (s.gpr .rdi + 136) (((s.gpr .rsi).toNat + (s.gpr .rcx).toNat) % 8) =
    Spec.Rc2.bytesAt s.mem (s.gpr .rdx + BitVec.ofNat 64 ((s.gpr .r9).toNat - (s.gpr .rsi).toNat))
      (((s.gpr .rsi).toNat + (s.gpr .rcx).toNat) % 8)

theorem long_ok (d : Spec.Rc2.Direction) (s : State) (hs : (VG.Proof.Rc2.X86_64.Stream.updateContract d).pre s)
    (hnz : (s.gpr .r9).toNat ≠ 0) (t : State) (ht : Keep [] s t) :
    WP isa longPre t (VG.Proof.Rc2.X86_64.Stream.Mid s) := by
  obtain ⟨_, _, hrd, hwr, ctxData, ctxOut, _, ctxArgs, dataOut, _, _, outArgs, _, _, _, _, _, _,
    _, _, _, _, _, _, fitData, fitOut, _, hp, hN⟩ := hs
  -- Names for the arguments.
  generalize hC : s.gpr .rdi = C at *
  generalize hP : (s.gpr .rsi).toNat = P at *
  generalize hA : s.gpr .rdx = A at *
  generalize hL : (s.gpr .rcx).toNat = L at *
  generalize hO : s.gpr .r8 = O at *
  generalize hNN : (s.gpr .r9).toNat = N at *
  have h8 : 8 ≤ N := by omega
  have hPN : P ≤ N := by omega
  have hNL : N - P ≤ L := by omega
  have hR : L - (N - P) = (P + L) % 8 := by omega
  have rsi₀ : s.gpr .rsi = BitVec.ofNat 64 P := by rw [← hP]; exact VG.Proof.Rc2.X86_64.Stream.toNat_eq _
  have rcx₀ : s.gpr .rcx = BitVec.ofNat 64 L := by rw [← hL]; exact VG.Proof.Rc2.X86_64.Stream.toNat_eq _
  have r9₀ : s.gpr .r9 = BitVec.ofNat 64 N := by rw [← hNN]; exact VG.Proof.Rc2.X86_64.Stream.toNat_eq _
  have K_def : N - P + (P + L) % 8 = L := by omega
  have hRlt : (P + L) % 8 < 8 := Nat.mod_lt _ (by decide)
  have dataR (i n : Nat) (h : i + n ≤ L) : InRegions s.rd (A + BitVec.ofNat 64 i) n := by
    rw [hrd]; exact ⟨⟨A, L⟩, by simp, Offset.contains_base _ h (by omega)⟩
  have outW (i n : Nat) (h : i + n ≤ N) : InRegions s.wr (O + BitVec.ofNat 64 i) n := by
    rw [hwr]; exact ⟨⟨O, N⟩, by simp, Offset.contains_base _ h (by omega)⟩
  have ctxW (i n : Nat) (h : i + n ≤ 144) : InRegions s.wr (C + BitVec.ofNat 64 i) n := by
    rw [hwr]; exact ⟨⟨C, 144⟩, by simp, Offset.contains_base _ h (by omega)⟩
  have rdwr {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n := by
    obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩
  have rdrd {a : Addr} {n : Nat} (h : InRegions s.rd a n) : InRegions (s.rd ++ s.wr) a n := by
    obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_left _ hr, hc⟩
  -- The pending bytes to `out`.
  refine WP.seq (WP.mono (VG.Proof.Rc2.X86_64.Stream.copy_ok t (src := .rdi) (dst := .r8) (cnt := .rsi) (sd := 136) (dd := 0)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (S := C + BitVec.ofNat 64 136) (D := O) (n := P)
    (by rw [ht.reg _ (by simp), hC]) (by rw [ht.reg _ (by simp), hO]; exact BitVec.add_zero _)
    (by rw [ht.reg _ (by simp), rsi₀]) (by omega)
    (fun i hi => by rw [ht.rd, ht.wr, Offset.add_add]; exact rdwr (ctxW _ _ (by omega)))
    (fun i hi => by rw [ht.wr]; exact outW _ _ (by omega))
    ((ctxOut.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix hPN))) ?_)
  rintro s₁ ⟨mem₁, g₁, rd₁, wr₁⟩
  rw [ht.mem] at mem₁
  have f₁ : Frame [⟨O, P⟩] s.mem s₁.mem := by
    rw [mem₁]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have c₁ : Spec.Rc2.bytesAt s₁.mem O P = Spec.Rc2.bytesAt s.mem (C + BitVec.ofNat 64 136) P := by
    have h := bytesAt_writeBytes_self s.mem O (Spec.Rc2.bytesAt s.mem (C + BitVec.ofNat 64 136) P)
      (by rw [bytesAt_length]; omega)
    rwa [bytesAt_length, ← mem₁] at h
  clear mem₁
  have k₁ (r : Reg) (h₁ : r ≠ .r10) (h₂ : r ≠ .r11) : s₁.gpr r = s.gpr r := (g₁ r h₁ h₂).trans (ht.reg r (by simp))
  -- The registers for the data.
  obtain ⟨s₂, run₂, r9₂, r8₂, keep₂⟩ := VG.Proof.Rc2.X86_64.Stream.toOut_ok s₁
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have k₂ (r : Reg) (h₁ : r ≠ .r10) (h₂ : r ≠ .r11) (h₃ : r ≠ .r9) (h₄ : r ≠ .r8) : s₂.gpr r = s.gpr r :=
    (keep₂.reg r (by simp [h₃, h₄])).trans (k₁ r h₁ h₂)
  rw [k₁ _ (by decide) (by decide), k₁ _ (by decide) (by decide), r9₀, rsi₀,
    Offset.ofNat_sub_ofNat hPN] at r9₂
  rw [k₁ _ (by decide) (by decide), k₁ _ (by decide) (by decide), hO, rsi₀] at r8₂
  -- The first `out_len - pending_len` bytes of data to `out + pending_len`.
  refine WP.seq (WP.mono (VG.Proof.Rc2.X86_64.Stream.copy_ok s₂ (src := .rdx) (dst := .r8) (cnt := .r9) (sd := 0) (dd := 0)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (S := A) (D := O + BitVec.ofNat 64 P) (n := N - P)
    (by rw [k₂ _ (by decide) (by decide) (by decide) (by decide), hA]; exact BitVec.add_zero _)
    (by rw [r8₂]; exact BitVec.add_zero _) r9₂ (by omega)
    (fun i hi => by rw [keep₂.rd, keep₂.wr, rd₁, wr₁, ht.rd, ht.wr]; exact rdrd (dataR _ _ (by omega)))
    (fun i hi => by rw [keep₂.wr, wr₁, ht.wr, Offset.add_add]; exact outW _ _ (by omega))
    ((dataOut.sub_left (Region.sub_prefix hNL)).sub_right (Offset.sub_base _ (by omega)))) ?_)
  rintro s₃ ⟨mem₃, g₃, rd₃, wr₃⟩
  rw [keep₂.mem] at mem₃
  have f₃ : Frame [⟨O + BitVec.ofNat 64 P, N - P⟩] s₁.mem s₃.mem := by
    rw [mem₃]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have c₃ : Spec.Rc2.bytesAt s₃.mem (O + BitVec.ofNat 64 P) (N - P) = Spec.Rc2.bytesAt s₁.mem A (N - P) := by
    have h := bytesAt_writeBytes_self s₁.mem (O + BitVec.ofNat 64 P) (Spec.Rc2.bytesAt s₁.mem A (N - P))
      (by rw [bytesAt_length]; omega)
    rwa [bytesAt_length, ← mem₃] at h
  clear mem₃
  have k₃ (r : Reg) (h₁ : r ≠ .r10) (h₂ : r ≠ .r11) : s₃.gpr r = s₂.gpr r := g₃ r h₁ h₂
  -- The registers for the rest.
  obtain ⟨s₄, run₄, rdx₄, rcx₄, keep₄⟩ := VG.Proof.Rc2.X86_64.Stream.toPending_ok s₃
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  rw [k₃ _ (by decide) (by decide), k₃ _ (by decide) (by decide), r9₂,
    k₂ _ (by decide) (by decide) (by decide) (by decide), hA] at rdx₄
  rw [k₃ _ (by decide) (by decide), k₃ _ (by decide) (by decide), r9₂,
    k₂ _ (by decide) (by decide) (by decide) (by decide), rcx₀, Offset.ofNat_sub_ofNat hNL, hR] at rcx₄
  -- The rest to `ctx + 136`.
  refine WP.seq (WP.mono (VG.Proof.Rc2.X86_64.Stream.copy_ok s₄ (src := .rdx) (dst := .rdi) (cnt := .rcx) (sd := 0) (dd := 136)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (S := A + BitVec.ofNat 64 (N - P)) (D := C + BitVec.ofNat 64 136) (n := (P + L) % 8)
    (by rw [rdx₄]; exact BitVec.add_zero _)
    (by rw [keep₄.reg _ (by simp), k₃ _ (by decide) (by decide),
      k₂ _ (by decide) (by decide) (by decide) (by decide), hC]) rcx₄ (by omega)
    (fun i hi => by
      rw [keep₄.rd, keep₄.wr, rd₃, wr₃, keep₂.rd, keep₂.wr, rd₁, wr₁, ht.rd, ht.wr, Offset.add_add]
      exact rdrd (dataR _ _ (by omega)))
    (fun i hi => by
      rw [keep₄.wr, wr₃, keep₂.wr, wr₁, ht.wr, Offset.add_add]; exact ctxW _ _ (by omega))
    ((ctxData.symm.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega)))) ?_)
  rintro s₅ ⟨mem₅, g₅, rd₅, wr₅⟩
  rw [keep₄.mem] at mem₅
  have f₅ : Frame [⟨C + BitVec.ofNat 64 136, (P + L) % 8⟩] s₃.mem s₅.mem := by
    rw [mem₅]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have c₅ : Spec.Rc2.bytesAt s₅.mem (C + BitVec.ofNat 64 136) ((P + L) % 8) =
      Spec.Rc2.bytesAt s₃.mem (A + BitVec.ofNat 64 (N - P)) ((P + L) % 8) := by
    have h := bytesAt_writeBytes_self s₃.mem (C + BitVec.ofNat 64 136)
      (Spec.Rc2.bytesAt s₃.mem (A + BitVec.ofNat 64 (N - P)) ((P + L) % 8)) (by rw [bytesAt_length]; omega)
    rwa [bytesAt_length, ← mem₅] at h
  clear mem₅
  have k₅ (r : Reg) (h₁ : r ≠ .r10) (h₂ : r ≠ .r11) (h₃ : r ≠ .r9) (h₄ : r ≠ .r8) (h₅ : r ≠ .rdx)
      (h₆ : r ≠ .rcx) : s₅.gpr r = s.gpr r := by
    rw [g₅ r h₁ h₂, keep₄.reg r (by simp [h₅, h₆]), k₃ r h₁ h₂, k₂ r h₁ h₂ h₃ h₄]
  have rd₅' : s₅.rd = s.rd := by rw [rd₅, keep₄.rd, rd₃, keep₂.rd, rd₁, ht.rd]
  have wr₅' : s₅.wr = s.wr := by rw [wr₅, keep₄.wr, wr₃, keep₂.wr, wr₁, ht.wr]
  -- Memory changed only in `out` and the pending block.
  have frame : Frame [⟨O, N⟩, ⟨C + BitVec.ofNat 64 136, 8⟩] s.mem s₅.mem := by
    refine ((f₁.sub ?_).trans (f₃.sub ?_)).trans (f₅.sub ?_) <;> intro r hr <;>
      simp only [List.mem_singleton] at hr <;> subst hr
    · exact ⟨_, List.mem_cons_self .., Region.sub_prefix hPN⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by omega)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by omega)⟩
  have argsAddr : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := rfl
  have argsSep : ∀ r ∈ [(⟨O, N⟩ : Region), ⟨C + BitVec.ofNat 64 136, 8⟩],
      (Region.mk (stackArgAddr s 0) 8).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact outArgs.symm
    · exact ctxArgs.symm.sub_right (Offset.sub_base _ (by omega))
  -- The arguments of the CBC function.
  obtain ⟨s₆, run₆, rdi₆, rsi₆, rdx₆, rcx₆, r8₆, keep₆⟩ := VG.Proof.Rc2.X86_64.Stream.cbcArgs_ok s₅ (by
    rw [rd₅', wr₅', k₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ← argsAddr]
    exact rdrd (by rw [hrd]; exact ⟨_, by simp, Region.contains_self _ _⟩))
  refine WP.of_runBlock ⟨s₆, run₆, ?_⟩
  have s5rdi : s₅.gpr .rdi = C := by
    rw [k₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hC]
  have s5rsi : s₅.gpr .rsi = BitVec.ofNat 64 P := by
    rw [k₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rsi₀]
  have s5r8 : s₅.gpr .r8 = O + BitVec.ofNat 64 P := by
    rw [g₅ _ (by decide) (by decide), keep₄.reg _ (by simp), k₃ _ (by decide) (by decide), r8₂]
  have s5r9 : s₅.gpr .r9 = BitVec.ofNat 64 (N - P) := by
    rw [g₅ _ (by decide) (by decide), keep₄.reg _ (by simp), k₃ _ (by decide) (by decide), r9₂]
  have mem₆ : s₆.mem = s₅.mem := keep₆.mem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rdi₆, s5rdi, hC]
  · rw [rsi₆, s5rdi, hC]
  · rw [rdx₆, s5r8, s5rsi, BitVec.add_sub_cancel, hO]
  · rw [rcx₆, s5r9, s5rsi, ← BitVec.ofNat_add, Nat.sub_add_cancel hPN, hNN]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [r8₆, k₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ← argsAddr]
    exact frame.readW (Region.contains_self _ _) argsSep (by decide)
  · rw [keep₆.reg _ (by simp), k₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  · intro r hr
    have h : r ∉ [Reg.r8, .r9, .rdx, .rcx, .rsi] ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r9 ∧ r ≠ .r8 ∧ r ≠ .rdx ∧
        r ≠ .rcx := by
      revert hr; revert r; decide
    rw [keep₆.reg _ h.1, k₅ _ h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2]
  · rw [keep₆.rd, rd₅']
  · rw [keep₆.wr, wr₅']
  · rw [mem₆, hO, hNN, hC]; exact frame
  · -- `out`: the pending bytes, then the data.
    rw [mem₆, hO, hNN, hC, hP, hA, show C + 136 = C + BitVec.ofNat 64 136 from rfl,
      show N = P + (N - P) by omega, bytesAt_add, Nat.add_sub_cancel_left]
    have outSub : ∀ r ∈ [(⟨C + BitVec.ofNat 64 136, (P + L) % 8⟩ : Region)], (Region.mk O N).Disjoint r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact ctxOut.symm.sub_right (Offset.sub_base _ (by omega))
    refine congr (congrArg HAppend.hAppend ?_) ?_
    · rw [Proof.Rc2.bytesAt_frame f₅ _ _ (by omega) (fun r hr => (outSub r hr).sub_left (Region.sub_prefix hPN)),
        Proof.Rc2.bytesAt_frame f₃ _ _ (by omega) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.base_disjoint _ (by omega) (by omega)), c₁]
    · rw [Proof.Rc2.bytesAt_frame f₅ _ _ (by omega)
          (fun r hr => (outSub r hr).sub_left (Offset.sub_base _ (by omega))), c₃,
        Proof.Rc2.bytesAt_frame f₁ _ _ (by omega) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (dataOut.sub_left (Region.sub_prefix hNL)).sub_right (Region.sub_prefix hPN))]
  · -- The pending block: the rest of the data.
    rw [mem₆, hC, hP, hL, hA, hNN, show C + 136 = C + BitVec.ofNat 64 136 from rfl, c₅]
    have dataSub : Region.Sub ⟨A + BitVec.ofNat 64 (N - P), (P + L) % 8⟩ ⟨A, L⟩ := Offset.sub_base _ (by omega)
    rw [Proof.Rc2.bytesAt_frame f₃ _ _ (by omega) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (dataOut.sub_left dataSub).sub_right (Offset.sub_base _ (by omega))),
      Proof.Rc2.bytesAt_frame f₁ _ _ (by omega) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (dataOut.sub_left dataSub).sub_right (Region.sub_prefix hPN))]
end VG.Proof.Rc2.X86_64.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86_64.Stream.Verified`. -/
section

section

/-! # Streaming RC2-CBC on x86-64: the update functions -/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64 VG.X86_64.RegUpd VG.WriteBytes VG.Impl.Rc2.X86_64 VG.Impl.Rc2.X86_64.Stream

def cbcName : Spec.Rc2.Direction → String
  | .encrypt => "vg_rc2_cbc_encrypt"
  | .decrypt => "vg_rc2_cbc_decrypt"

theorem cbcCall_eq (d : Spec.Rc2.Direction) : cbcCall d = .call (VG.Proof.Rc2.X86_64.Stream.cbcName d) (Cbc.cbc d) := by
  cases d <;> rfl

theorem cbc_correct (d : Spec.Rc2.Direction) (s : State) (hs : (Cbc.contract d).pre s) :
    ∃ t s', Exec isa (Cbc.cbc d) s t s' ∧ abiPreserved s s' ∧ (Cbc.contract d).post s s' := by
  cases d
  · exact Cbc.encrypt_correct s hs
  · exact Cbc.decrypt_correct s hs

theorem cbc_noSp (d : Spec.Rc2.Direction) : NoSp (Cbc.cbc d) := by
  have h : ((instrs (Cbc.cbc d)).all fun i => !Taint.clobbers i .rsp) = true := by
    cases d
    · change ((instrs Cbc.encrypt).all _) = true
      rw [← Code.allInstrs_eq]; lit_decide
    · change ((instrs Cbc.decrypt).all _) = true
      rw [← Code.allInstrs_eq]; lit_decide
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem cbc_depth (d : Spec.Rc2.Direction) : (Cbc.cbc d).depth = 1 := by
  cases d <;> rfl

/-- The regions the CBC function is given: the schedule, and the chaining
value, `out` and its scratch space. -/
def callRd (s : State) : List Region := [⟨s.gpr .rdi, 128⟩]
def callWr (s : State) : List Region :=
  [⟨s.gpr .rdi + 128, 8⟩, ⟨s.gpr .r8, 8 * ((s.gpr .r9).toNat / 8)⟩, ⟨stackArg s 0, 512⟩]

/-- The CBC function's precondition at the call, and its regions within ours. -/
theorem call_pre (d : Spec.Rc2.Direction) (s : State) (hs : (VG.Proof.Rc2.X86_64.Stream.updateContract d).pre s)
    (hnz : (s.gpr .r9).toNat ≠ 0) (t : State) (ht : VG.Proof.Rc2.X86_64.Stream.Mid s t) :
    (Cbc.contract d).pre (t.callEntry.withRegions (VG.Proof.Rc2.X86_64.Stream.callRd s) (VG.Proof.Rc2.X86_64.Stream.callWr s)) ∧
      Covers (VG.Proof.Rc2.X86_64.Stream.callRd s ++ VG.Proof.Rc2.X86_64.Stream.callWr s) (t.rd ++ t.wr) ∧ Covers (VG.Proof.Rc2.X86_64.Stream.callWr s) t.wr := by
  obtain ⟨hsp, _, hrd, hwr, ctxData, ctxOut, ctxBuf, _, dataOut, _, outBuf, _, _, retCtx, _, retOut, retBuf, _,
    stCtx, _, stOut, stBuf, _, _, _, fitOut, _, hp, hN⟩ := hs
  obtain ⟨rdi₁, rsi₁, rdx₁, rcx₁, r8₁, rsp₁, callee₁, rd₁, wr₁, frame₁, out₁, pend₁⟩ := ht
  simp only [VG.Proof.Rc2.X86_64.Stream.callRd, VG.Proof.Rc2.X86_64.Stream.callWr]
  generalize hC : s.gpr .rdi = C at *
  generalize hNN : (s.gpr .r9).toNat = N at *
  generalize hO : s.gpr .r8 = O at *
  generalize hB : stackArg s 0 = B at *
  generalize hSP : s.gpr .rsp = SP at *
  have h8 : 8 ≤ N := by omega
  have hNN8 : 8 * (N / 8) = N := by omega
  have e128 : C + 128 = C + BitVec.ofNat 64 128 := rfl
  have stackSub : Region.Sub (below (SP - 8) 8) (below SP 16) := below_callee _ _
  have retSub : Region.Sub ⟨SP - 8, 8⟩ (below SP 16) := Offset.sub_below SP (by decide) (by decide)
  have ivSub : Region.Sub ⟨C + BitVec.ofNat 64 128, 8⟩ ⟨C, 144⟩ := Offset.sub_base _ (by decide)
  have keySub : Region.Sub ⟨C, 128⟩ ⟨C, 144⟩ := Region.sub_prefix (by decide)
  have bufSub : Region.Sub ⟨B, 512⟩ ⟨B, 576⟩ := Region.sub_prefix (by decide)
  refine ⟨?_, ?_, ?_⟩
  · simp only [Cbc.contract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_rsp, State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp),
      rdi₁, rsi₁, rdx₁, rcx₁, r8₁, rsp₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show N / 8 < 2 ^ 64 by omega),
      hNN8, e128]
    refine ⟨trivial, trivial, Offset.base_disjoint _ (by decide) (by decide), ctxOut.sub_left keySub,
      (ctxBuf.sub_left keySub).sub_right bufSub, ctxOut.sub_left ivSub, (ctxBuf.sub_left ivSub).sub_right bufSub,
      outBuf.sub_right bufSub, (stCtx.sub_left retSub).sub_right ivSub, stOut.sub_left retSub,
      (stBuf.sub_left retSub).sub_right bufSub, (stCtx.sub_left stackSub).sub_right keySub,
      (stCtx.sub_left stackSub).sub_right ivSub, stOut.sub_left stackSub,
      (stBuf.sub_left stackSub).sub_right bufSub, fitOut⟩
  · rw [rd₁, wr₁, hrd, hwr]
    apply Covers.of_sub
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨C, 144⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨C, 144⟩, by simp, 128, rfl, by simp⟩
    · exact ⟨⟨O, N⟩, by simp, 0, by simp, by simp only [hNN8]; omega⟩
    · exact ⟨⟨B, 576⟩, by simp, 0, by simp, by simp⟩
  · rw [wr₁, hwr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨C, 144⟩, by simp, 128, rfl, by simp⟩
    · exact ⟨⟨O, N⟩, by simp, 0, by simp, by simp only [hNN8]; omega⟩
    · exact ⟨⟨B, 576⟩, by simp, 0, by simp, by simp⟩

/-- The call of the CBC function, and the update's postcondition. -/
theorem call_ok (d : Spec.Rc2.Direction) (s : State) (hs : (VG.Proof.Rc2.X86_64.Stream.updateContract d).pre s)
    (hnz : (s.gpr .r9).toNat ≠ 0) (t : State) (ht : VG.Proof.Rc2.X86_64.Stream.Mid s t) :
    WP isa (cbcCall d) t (fun s' => ((∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64) ∧
      (Spec.Rc2.contextAt s'.mem (s.gpr .rdi) d (((s.gpr .rsi).toNat + (s.gpr .rcx).toNat) % 8) =
        (Spec.Rc2.update (Spec.Rc2.contextAt s.mem (s.gpr .rdi) d (s.gpr .rsi).toNat)
          (Spec.Rc2.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)).1 ∧
      Spec.Rc2.bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat =
        (Spec.Rc2.update (Spec.Rc2.contextAt s.mem (s.gpr .rdi) d (s.gpr .rsi).toNat)
          (Spec.Rc2.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)).2)) := by
  obtain ⟨hpre, hcov, hwcov⟩ := VG.Proof.Rc2.X86_64.Stream.call_pre d s hs hnz t ht
  simp only [VG.Proof.Rc2.X86_64.Stream.callRd, VG.Proof.Rc2.X86_64.Stream.callWr] at hpre hcov hwcov
  obtain ⟨hsp, _, hrd, hwr, ctxData, ctxOut, ctxBuf, _, dataOut, _, outBuf, _, _, retCtx, _, retOut, retBuf, _,
    stCtx, _, stOut, stBuf, _, _, _, fitOut, _, hp, hN⟩ := hs
  obtain ⟨rdi₁, rsi₁, rdx₁, rcx₁, r8₁, rsp₁, callee₁, rd₁, wr₁, frame₁, out₁, pend₁⟩ := ht
  generalize hC : s.gpr .rdi = C at *
  generalize hP : (s.gpr .rsi).toNat = P at *
  generalize hA : s.gpr .rdx = A at *
  generalize hL : (s.gpr .rcx).toNat = L at *
  generalize hO : s.gpr .r8 = O at *
  generalize hNN : (s.gpr .r9).toNat = N at *
  generalize hB : stackArg s 0 = B at *
  generalize hSP : s.gpr .rsp = SP at *
  have h8 : 8 ≤ N := by omega
  have hNN8 : 8 * (N / 8) = N := by omega
  have e128 : C + 128 = C + BitVec.ofNat 64 128 := rfl
  have e136 : C + 136 = C + BitVec.ofNat 64 136 := rfl
  have stackSub : Region.Sub (below (SP - 8) 8) (below SP 16) := below_callee _ _
  have retSub : Region.Sub ⟨SP - 8, 8⟩ (below SP 16) := Offset.sub_below SP (by decide) (by decide)
  have ivSub : Region.Sub ⟨C + BitVec.ofNat 64 128, 8⟩ ⟨C, 144⟩ := Offset.sub_base _ (by decide)
  have keySub : Region.Sub ⟨C, 128⟩ ⟨C, 144⟩ := Region.sub_prefix (by decide)
  have bufSub : Region.Sub ⟨B, 512⟩ ⟨B, 576⟩ := Region.sub_prefix (by decide)
  rw [VG.Proof.Rc2.X86_64.Stream.cbcCall_eq]
  refine WP.call (k := Cbc.contract d) (VG.Proof.Rc2.X86_64.Stream.cbc_correct d) (VG.Proof.Rc2.X86_64.Stream.cbc_noSp d) (by rw [VG.Proof.Rc2.X86_64.Stream.cbc_depth]; decide)
    (rd := [⟨C, 128⟩]) (wr := [⟨C + 128, 8⟩, ⟨O, 8 * (N / 8)⟩, ⟨B, 512⟩]) hpre hcov hwcov ?_
  intro s' rd' wr' callee' frame' _ ⟨s₂, mem₂, _, post₂⟩
  rw [VG.Proof.Rc2.X86_64.Stream.cbc_depth, rsp₁, hNN8, e128] at frame'
  -- What the call leaves.
  have stackFrame : Frame [below SP 8] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, rsp₁]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (below_call _ (by decide) (by decide))
  have stack8 : Region.Sub (below SP 8) (below SP 16) := Offset.sub_below SP (by decide) (by decide)
  simp only [Cbc.contract, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    rdi₁, rsi₁, rdx₁, rcx₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show N / 8 < 2 ^ 64 by omega), mem₂] at post₂
  rw [scheduleAt_frame stackFrame C (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ((stCtx.sub_left stack8).sub_right keySub).symm),
    blockAt_frame stackFrame (C + 128) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [e128]; exact ((stCtx.sub_left stack8).sub_right ivSub).symm),
    blocksAt_frame stackFrame O (N / 8) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [hNN8]; exact (stOut.sub_left stack8).symm)] at post₂
  -- Regions the call leaves alone.
  have callSep (R : Region) (hiv : R.Disjoint ⟨C + BitVec.ofNat 64 128, 8⟩) (hout : R.Disjoint ⟨O, N⟩)
      (hbuf : R.Disjoint ⟨B, 576⟩) (hst : R.Disjoint (below SP 16)) :
      ∀ r ∈ [(⟨C + BitVec.ofNat 64 128, 8⟩ : Region), ⟨O, N⟩, ⟨B, 512⟩] ++ [below SP 16], R.Disjoint r := by
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hiv
    · exact hout
    · exact hbuf.sub_right bufSub
    · exact hst
  have midSep (R : Region) (hout : R.Disjoint ⟨O, N⟩) (hpend : R.Disjoint ⟨C + BitVec.ofNat 64 136, 8⟩) :
      ∀ r ∈ [(⟨O, N⟩ : Region), ⟨C + BitVec.ofNat 64 136, 8⟩], R.Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hout
    · exact hpend
  have pendSub : Region.Sub ⟨C + BitVec.ofNat 64 136, 8⟩ ⟨C, 144⟩ := Offset.sub_base _ (by decide)
  refine ⟨⟨fun r hr => (callee' r hr).trans (callee₁ r hr), ?_⟩, ?_⟩
  · rw [frame'.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (callSep _ (retCtx.sub_right ivSub) retOut
        retBuf (Offset.base_disjoint_below _ (by decide))) (by decide),
      frame₁.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (midSep _ retOut (retCtx.sub_right pendSub))
        (by decide)]
  · rw [hN] at out₁ pend₁ post₂ ⊢
    rw [Nat.mul_div_cancel _ (by decide : 0 < 8)] at post₂
    have keyMid := scheduleAt_frame frame₁ C (midSep _ (ctxOut.sub_left keySub)
      (Offset.base_disjoint _ (by decide) (by decide)))
    refine update_post_long hp (by omega) out₁ keyMid ?_ ?_ ?_ post₂.1 post₂.2
    · rw [e128]
      exact blockAt_frame frame₁ _ (midSep _ (ctxOut.sub_left ivSub) (Offset.disjoint _ (by decide) (by decide) (by decide)))
    · rw [e136, Proof.Rc2.bytesAt_frame frame' _ _ (by omega) (callSep _
          (Offset.disjoint _ (by omega) (by omega) (by decide)) (ctxOut.sub_left (Offset.sub_base _ (by omega)))
          (ctxBuf.sub_left (Offset.sub_base _ (by omega))) (stCtx.symm.sub_left (Offset.sub_base _ (by omega)))),
        ← e136, pend₁]
    · exact scheduleAt_frame frame' C (callSep _ (Offset.base_disjoint _ (by decide) (by decide))
        (ctxOut.sub_left keySub) (ctxBuf.sub_left keySub) (stCtx.symm.sub_left keySub))

theorem update_body_correct (d : Spec.Rc2.Direction) (s : State) (hs : (VG.Proof.Rc2.X86_64.Stream.updateContract d).pre s) :
    WP isa (update d) s (fun s' => gprPreserved s s' ∧ (VG.Proof.Rc2.X86_64.Stream.updateContract d).post s s') := by
  obtain ⟨t₁, run₁, zf₁, keep₁⟩ := VG.Proof.Rc2.X86_64.Stream.test_ok s .r9 (VG.Proof.Rc2.X86_64.Stream.toNat_eq _) (s.gpr .r9).isLt
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite (decide ((s.gpr .r9).toNat = 0)) (by simpa [eval] using zf₁) (fun h => ?_) (fun h => ?_)
  · exact VG.Proof.Rc2.X86_64.Stream.short_ok d s hs (of_decide_eq_true h) t₁ keep₁
  · exact WP.seq (WP.mono (VG.Proof.Rc2.X86_64.Stream.long_ok d s hs (of_decide_eq_false h) t₁ keep₁) fun t ht =>
      WP.mono (VG.Proof.Rc2.X86_64.Stream.call_ok d s hs (of_decide_eq_false h) t ht) fun _ h => h)

theorem update_correct (d : Spec.Rc2.Direction) (s : State) (hs : (VG.Proof.Rc2.X86_64.Stream.updateContract d).pre s) :
    ∃ t s', Exec isa (update d) s t s' ∧ abiPreserved s s' ∧ (VG.Proof.Rc2.X86_64.Stream.updateContract d).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := VG.Proof.Rc2.X86_64.Stream.update_body_correct d s hs
  refine ⟨t, s', he, abiPreserved_of_exec ?_ he ha, hp⟩
  cases d
  · change encryptUpdate.allInstrs _ = true; lit_decide
  · change decryptUpdate.allInstrs _ = true; lit_decide

end VG.Proof.Rc2.X86_64.Stream

end

section

section

/-! # Streaming RC2-CBC on x86-64: `init`'s length checks -/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64 VG.Impl.Rc2.X86_64.Stream

/-- What `init` returns for invalid lengths, in `initWithEffectiveBits`'s
order, and 0 for valid ones. -/
def code (keyLen effectiveBits ivLen : Nat) : Nat :=
  if ¬(1 ≤ keyLen ∧ keyLen ≤ 128) then 1
  else if ¬(1 ≤ effectiveBits ∧ effectiveBits ≤ 1024) then 2 else if ivLen ≠ 8 then 3 else 0

theorem code_le (a b c : Nat) : VG.Proof.Rc2.X86_64.Stream.code a b c ≤ 3 := by
  unfold VG.Proof.Rc2.X86_64.Stream.code; split <;> (try split) <;> (try split) <;> omega

theorem sub_one_lt (x : BitVec 64) {n : Nat} (hn : n < 2 ^ 64) :
    (x - 1).toNat < n ↔ 1 ≤ x.toNat ∧ x.toNat ≤ n := by
  have := x.isLt
  rw [BitVec.toNat_sub, show (1 : BitVec 64).toNat = 1 from rfl]
  omega

/-- `mov32 rax, c`, then `r10 = r - 1` compared with `n`: CF is set iff `r` is
in `1..=n`. -/
theorem checkRange_ok (s : State) (r : Reg) (hr : r ≠ .rax) (c n : Nat) (hc : c < 2 ^ 32) (hn : n < 2 ^ 63)
    (hs : (BitVec.signExtend 64 (BitVec.ofNat 32 n)).toNat = n) :
    ∃ s', runBlock isa [.mov32 .rax (.imm (BitVec.ofNat 32 c)), rr .r10 r, .alu .sub .r10 (.imm 1),
        .alu .cmp .r10 (.imm (BitVec.ofNat 32 n))] s = some s' ∧
      s'.gpr .rax = BitVec.ofNat 64 c ∧ s'.cf = some (decide (1 ≤ (s.gpr r).toNat ∧ (s.gpr r).toNat ≤ n)) ∧
      Keep [.rax, .r10] s s' := by
  refine ⟨_, by
    simp only [rr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
      State.setReg32, Option.bind_some, Option.map_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ⟨fun r' hr' => ?_, rfl, rfl, rfl⟩⟩
  · rw [gpr_arithFlags, gpr_setReg_of_ne _ _ (by decide), gpr_arithFlags, gpr_setReg_of_ne _ _ (by decide),
      gpr_setReg_self]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc,
      Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega)]
  · simp only [cf_arithFlags, gpr_setReg_self, gpr_setReg_of_ne _ _ hr, hs,
      show BitVec.signExtend 64 (1 : BitVec 32) = 1 by decide, VG.Proof.Rc2.X86_64.Stream.sub_one_lt _ (show n < 2 ^ 64 by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    simp only [gpr_arithFlags, gpr_setReg_of_ne _ _ hr'.2, gpr_setReg_of_ne _ _ hr'.1]

theorem checkIv_ok (s : State) :
    ∃ s', runBlock isa checkIv s = some s' ∧
      s'.gpr .rax = BitVec.ofNat 64 3 ∧ s'.zf = some (decide ((s.gpr .r8).toNat = 8)) ∧ Keep [.rax, .r10] s s' := by
  refine ⟨_, by
    simp only [checkIv, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
      State.setReg32, Option.bind_some, Option.map_some]
    rfl, ?_⟩
  refine ⟨by rw [gpr_arithFlags, gpr_setReg_self]; rfl, ?_, ⟨fun r' hr' => ?_, rfl, rfl, rfl⟩⟩
  · rw [zf_arithFlags, gpr_setReg_of_ne _ _ (by decide), VG.Proof.Rc2.X86_64.Stream.toNat_eq (s.gpr .r8),
      show BitVec.signExtend 64 (8 : BitVec 32) = BitVec.ofNat 64 8 by decide,
      Offset.ofNat_sub_ofNat_beq (s.gpr .r8).isLt (by decide), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (s.gpr .r8).isLt]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    simp only [gpr_arithFlags, gpr_setReg_of_ne _ _ hr'.1]

theorem zero_ok (s : State) :
    ∃ s', runBlock isa [.mov32 .rax (.imm 0)] s = some s' ∧ s'.gpr .rax = BitVec.ofNat 64 0 ∧ Keep [.rax, .r10] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, Option.map_some]
    rfl, ?_⟩
  refine ⟨by rw [gpr_setReg_self]; rfl, ⟨fun r' hr' => ?_, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
  simp only [gpr_setReg_of_ne _ _ hr'.1]

theorem keep_trans {s s' s'' : State} (h : Keep [.rax, .r10] s s') (h' : Keep [.rax, .r10] s' s'') :
    Keep [.rax, .r10] s s'' :=
  ⟨fun r hr => (h'.reg r hr).trans (h.reg r hr), h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr⟩

theorem checks_ok (s : State) :
    WP isa checks s fun t => Keep [.rax, .r10] s t ∧
      t.zf = some (decide (VG.Proof.Rc2.X86_64.Stream.code (s.gpr .rsi).toNat (s.gpr .rdx).toNat (s.gpr .r8).toNat = 0)) ∧
      t.gpr .rax = BitVec.ofNat 64 (VG.Proof.Rc2.X86_64.Stream.code (s.gpr .rsi).toNat (s.gpr .rdx).toNat (s.gpr .r8).toNat) := by
  refine WP.seq (WP.mono (Q := fun (t : State) => Keep [.rax, .r10] s t ∧
      t.gpr .rax = BitVec.ofNat 64 (VG.Proof.Rc2.X86_64.Stream.code (s.gpr .rsi).toNat (s.gpr .rdx).toNat (s.gpr .r8).toNat)) ?_ ?_)
  · obtain ⟨s₁, run₁, rax₁, cf₁, keep₁⟩ := VG.Proof.Rc2.X86_64.Stream.checkRange_ok s .rsi (by decide) 1 128 (by decide) (by decide) (by decide)
    refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
    refine WP.ite _ (by simp only [eval, cf₁]; rfl) (fun h => WP.block_nil ⟨keep₁, ?_⟩) (fun h => ?_)
    · rw [rax₁, VG.Proof.Rc2.X86_64.Stream.code, ite_eq_left_of_eq_true _ _ (eq_true (by simp at h ⊢; omega))]
    obtain ⟨s₂, run₂, rax₂, cf₂, keep₂⟩ := VG.Proof.Rc2.X86_64.Stream.checkRange_ok s₁ .rdx (by decide) 2 1024 (by decide) (by decide) (by decide)
    have hk : 1 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ 128 := by simpa using h
    rw [keep₁.reg _ (by decide)] at cf₂
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    refine WP.ite _ (by simp only [eval, cf₂]; rfl) (fun h => WP.block_nil ⟨VG.Proof.Rc2.X86_64.Stream.keep_trans keep₁ keep₂, ?_⟩)
      (fun h => ?_)
    · rw [rax₂, VG.Proof.Rc2.X86_64.Stream.code, ite_eq_right_of_eq_false _ _ (eq_false (fun h => h hk)), ite_eq_left_of_eq_true _ _ (eq_true (by simp at h ⊢; omega))]
    have he : 1 ≤ (s.gpr .rdx).toNat ∧ (s.gpr .rdx).toNat ≤ 1024 := by simpa using h
    obtain ⟨s₃, run₃, rax₃, zf₃, keep₃⟩ := VG.Proof.Rc2.X86_64.Stream.checkIv_ok s₂
    rw [keep₂.reg _ (by decide), keep₁.reg _ (by decide)] at zf₃
    refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
    refine WP.ite _ (by simp only [eval, zf₃]; rfl) (fun h => WP.block_nil ⟨VG.Proof.Rc2.X86_64.Stream.keep_trans (VG.Proof.Rc2.X86_64.Stream.keep_trans keep₁ keep₂) keep₃, ?_⟩)
      (fun h => ?_)
    · rw [rax₃, VG.Proof.Rc2.X86_64.Stream.code, ite_eq_right_of_eq_false _ _ (eq_false (fun h => h hk)), ite_eq_right_of_eq_false _ _ (eq_false (fun h => h he)), ite_eq_left_of_eq_true _ _ (eq_true (by simp at h ⊢; omega))]
    obtain ⟨s₄, run₄, rax₄, keep₄⟩ := VG.Proof.Rc2.X86_64.Stream.zero_ok s₃
    refine WP.of_runBlock ⟨s₄, run₄, VG.Proof.Rc2.X86_64.Stream.keep_trans (VG.Proof.Rc2.X86_64.Stream.keep_trans (VG.Proof.Rc2.X86_64.Stream.keep_trans keep₁ keep₂) keep₃) keep₄, ?_⟩
    rw [rax₄, VG.Proof.Rc2.X86_64.Stream.code, ite_eq_right_of_eq_false _ _ (eq_false (fun h => h hk)), ite_eq_right_of_eq_false _ _ (eq_false (fun h => h he)), ite_eq_right_of_eq_false _ _ (eq_false (by simp at h ⊢; omega))]
  · rintro t ⟨keep, rax⟩
    obtain ⟨t', run, zf, keep'⟩ := VG.Proof.Rc2.X86_64.Stream.test_ok t .rax rax (by have := VG.Proof.Rc2.X86_64.Stream.code_le (s.gpr .rsi).toNat (s.gpr .rdx).toNat (s.gpr .r8).toNat; omega)
    refine WP.of_runBlock ⟨t', run, ⟨fun r hr => (keep'.reg r (by simp)).trans (keep.reg r hr),
      keep'.mem.trans keep.mem, keep'.rd.trans keep.rd, keep'.wr.trans keep.wr⟩, zf, ?_⟩
    rw [keep'.reg _ (by simp), rax]

end VG.Proof.Rc2.X86_64.Stream

end

/-! # Streaming RC2-CBC on x86-64: `vg_rc2_cbc_init` -/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64 VG.Impl.Rc2.X86_64.Stream

theorem initArgs_ok (s : State) (riv : InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofNat 64 0) 8)
    (wctx : InRegions s.wr (s.gpr .r9 + BitVec.ofNat 64 128) 8)
    (rarg : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa initArgs s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .r9 + BitVec.ofNat 64 128) (s.mem.readW (s.gpr .rcx + BitVec.ofNat 64 0) 64) ∧
      s'.gpr .rcx = s.gpr .r9 ∧ s'.gpr .r8 = s'.mem.readW (s.gpr .rsp + BitVec.ofNat 64 8) 64 ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r8 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, not_false_eq_true, initArgs, rr, memOp, runBlock_cons, runStep_some,
      exec, readSrc, State.load64, State.store64, State.ea, offset_nat, Option.map_some,
      gpr_setReg_self, gpr_setReg_of_ne, rd_setReg, wr_setReg, mem_setReg, riv, wctx]
    simp only [rarg, ite_true, Option.map_some]
    rfl, ?_⟩
  refine ⟨rfl, ?_, ?_, fun r h₁ h₂ h₃ => ?_, rfl, rfl⟩
  · simp only [reduceCtorEq, not_false_eq_true, gpr_setReg_self, gpr_setReg_of_ne]
  · simp only [gpr_setReg_self, mem_setReg]
  · simp only [gpr_setReg_of_ne _ _ h₁, gpr_setReg_of_ne _ _ h₂, gpr_setReg_of_ne _ _ h₃]

/-- The state before the call of key expansion, from the entry state `σ`. -/
structure KeyPre (σ t : State) : Prop where
  rdi : t.gpr .rdi = σ.gpr .rdi
  rsi : t.gpr .rsi = σ.gpr .rsi
  rdx : t.gpr .rdx = σ.gpr .rdx
  rcx : t.gpr .rcx = σ.gpr .r9
  r8 : t.gpr .r8 = stackArg σ 0
  rsp : t.gpr .rsp = σ.gpr .rsp
  callee : ∀ r ∈ calleeSaved, t.gpr r = σ.gpr r
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  mem : t.mem = σ.mem.writeW (σ.gpr .r9 + BitVec.ofNat 64 128) (σ.mem.readW (σ.gpr .rcx) 64)

/-- Valid lengths. -/
def Valid (σ : State) : Prop :=
  (1 ≤ (σ.gpr .rsi).toNat ∧ (σ.gpr .rsi).toNat ≤ 128) ∧ (1 ≤ (σ.gpr .rdx).toNat ∧ (σ.gpr .rdx).toNat ≤ 1024) ∧
    (σ.gpr .r8).toNat = 8

theorem valid_of_code {σ : State} (h : VG.Proof.Rc2.X86_64.Stream.code (σ.gpr .rsi).toNat (σ.gpr .rdx).toNat (σ.gpr .r8).toNat = 0) :
    VG.Proof.Rc2.X86_64.Stream.Valid σ := by
  unfold VG.Proof.Rc2.X86_64.Stream.code at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · refine ⟨?_, ?_, ?_⟩ <;> simp_all

theorem initArgs_pre (σ : State) (hs : initContract.pre σ) (hv : VG.Proof.Rc2.X86_64.Stream.Valid σ) (t : State) (ht : Keep [.rax, .r10] σ t) :
    WP isa (.block initArgs) t (VG.Proof.Rc2.X86_64.Stream.KeyPre σ) := by
  obtain ⟨_, _, hrd, hwr, _, _, _, _, _, ctxArgs, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hs
  have rdwr {a : Addr} {n : Nat} (h : InRegions σ.rd a n) : InRegions (σ.rd ++ σ.wr) a n := by
    obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_left _ hr, hc⟩
  have argsAddr : stackArgAddr σ 0 = σ.gpr .rsp + BitVec.ofNat 64 8 := rfl
  obtain ⟨t', run, mem', rcx', r8', g', rd', wr'⟩ := VG.Proof.Rc2.X86_64.Stream.initArgs_ok t
    (by rw [ht.rd, ht.wr, ht.reg _ (by decide)]
        exact rdwr (by rw [hrd]; exact ⟨⟨σ.gpr .rcx, (σ.gpr .r8).toNat⟩, by simp,
          Offset.contains_base _ (by have := hv.2.2; omega) (by decide)⟩))
    (by rw [ht.wr, ht.reg _ (by decide), hwr]
        exact ⟨⟨σ.gpr .r9, 144⟩, by simp, Offset.contains_base _ (by decide) (by decide)⟩)
    (by rw [ht.rd, ht.wr, ht.reg _ (by decide), ← argsAddr]
        exact rdwr (by rw [hrd]; exact ⟨⟨stackArgAddr σ 0, 8⟩, by simp, Region.contains_self _ _⟩))
  refine WP.of_runBlock ⟨t', run, ?_⟩
  have m : t'.mem = σ.mem.writeW (σ.gpr .r9 + BitVec.ofNat 64 128) (σ.mem.readW (σ.gpr .rcx) 64) := by
    rw [mem', ht.mem, ht.reg _ (by decide), ht.reg _ (by decide),
      show σ.gpr .rcx + BitVec.ofNat 64 0 = σ.gpr .rcx from BitVec.add_zero _]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, by rw [rd', ht.rd], by rw [wr', ht.wr], m⟩
  · rw [g' _ (by decide) (by decide) (by decide), ht.reg _ (by decide)]
  · rw [g' _ (by decide) (by decide) (by decide), ht.reg _ (by decide)]
  · rw [g' _ (by decide) (by decide) (by decide), ht.reg _ (by decide)]
  · rw [rcx', ht.reg _ (by decide)]
  · rw [r8', ht.reg _ (by decide), m, ← argsAddr]
    exact (frame_store64 _ _ _).readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ctxArgs.symm.sub_right (Offset.sub_base _ (by decide))) (by decide)
  · rw [g' _ (by decide) (by decide) (by decide), ht.reg _ (by decide)]
  · have h : r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .r8 ∧ r ∉ [Reg.rax, .r10] := by revert hr; revert r; decide
    rw [g' _ h.1 h.2.1 h.2.2.1, ht.reg _ h.2.2.2]

def keyRd (σ : State) : List Region := [⟨σ.gpr .rdi, (σ.gpr .rsi).toNat⟩]
def keyWr (σ : State) : List Region := [⟨σ.gpr .r9, 128⟩, ⟨stackArg σ 0, 512⟩]

/-- Key expansion's precondition at the call, and its regions within ours. -/
theorem key_pre (σ : State) (hs : initContract.pre σ) (hv : VG.Proof.Rc2.X86_64.Stream.Valid σ) (t : State) (ht : VG.Proof.Rc2.X86_64.Stream.KeyPre σ t) :
    keyContract.pre (t.callEntry.withRegions (VG.Proof.Rc2.X86_64.Stream.keyRd σ) (VG.Proof.Rc2.X86_64.Stream.keyWr σ)) ∧
      Covers (VG.Proof.Rc2.X86_64.Stream.keyRd σ ++ VG.Proof.Rc2.X86_64.Stream.keyWr σ) (t.rd ++ t.wr) ∧ Covers (VG.Proof.Rc2.X86_64.Stream.keyWr σ) t.wr := by
  obtain ⟨_, _, hrd, hwr, keyCtx, keyBuf, _, _, ctxBuf, _, _, _, _, _, _, _, _, _, stCtx, stBuf, _, _, _, _, _⟩ := hs
  have keySub : Region.Sub ⟨σ.gpr .r9, 128⟩ ⟨σ.gpr .r9, 144⟩ := Region.sub_prefix (by decide)
  have bufSub : Region.Sub ⟨stackArg σ 0, 512⟩ ⟨stackArg σ 0, 576⟩ := Region.sub_prefix (by decide)
  refine ⟨?_, ?_, ?_⟩
  · simp only [keyContract, VG.Proof.Rc2.X86_64.Stream.keyRd, VG.Proof.Rc2.X86_64.Stream.keyWr, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_rsp, State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp),
      ht.rdi, ht.rsi, ht.rdx, ht.rcx, ht.r8, ht.rsp]
    exact ⟨trivial, trivial, keyCtx.sub_right keySub, keyBuf.sub_right bufSub, (ctxBuf.sub_left keySub).sub_right bufSub,
      stCtx.sub_right keySub, stBuf.sub_right bufSub, hv.1.1, hv.1.2, hv.2.1.1, hv.2.1.2⟩
  · rw [ht.rd, ht.wr, hrd, hwr]
    apply Covers.of_sub
    intro r hr
    simp only [VG.Proof.Rc2.X86_64.Stream.keyRd, VG.Proof.Rc2.X86_64.Stream.keyWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨σ.gpr .rdi, (σ.gpr .rsi).toNat⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨σ.gpr .r9, 144⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨stackArg σ 0, 576⟩, by simp, 0, by simp, by simp⟩
  · rw [ht.wr, hwr]
    apply Covers.of_sub
    intro r hr
    simp only [VG.Proof.Rc2.X86_64.Stream.keyWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨σ.gpr .r9, 144⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨stackArg σ 0, 576⟩, by simp, 0, by simp, by simp⟩

theorem expandKey_noSp : NoSp expandKey := by
  have h : ((instrs expandKey).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem expandKey_depth : expandKey.depth = 0 := rfl

/-- The postcondition of `init`, spelled out. -/
def InitPost (σ s' : State) : Prop :=
  ((∀ r ∈ calleeSaved, s'.gpr r = σ.gpr r) ∧ s'.mem.readW (σ.gpr .rsp) 64 = σ.mem.readW (σ.gpr .rsp) 64) ∧
  ∀ direction, match Spec.Rc2.initWithEffectiveBits (Spec.Rc2.bytesAt σ.mem (σ.gpr .rdi) (σ.gpr .rsi).toNat)
      (Spec.Rc2.bytesAt σ.mem (σ.gpr .rcx) (σ.gpr .r8).toNat) direction (σ.gpr .rdx).toNat with
    | .ok c => (s'.gpr .rax).setWidth 32 = 0 ∧ Spec.Rc2.contextAt s'.mem (σ.gpr .r9) direction 0 = c
    | .error e => ((s'.gpr .rax).setWidth 32).toNat = e.code

theorem keyCall_ok (σ : State) (hs : initContract.pre σ) (hv : VG.Proof.Rc2.X86_64.Stream.Valid σ) (t : State) (ht : VG.Proof.Rc2.X86_64.Stream.KeyPre σ t) :
    WP isa (.seq keyCall (.block [.mov32 .rax (.imm 0)])) t (VG.Proof.Rc2.X86_64.Stream.InitPost σ) := by
  obtain ⟨hpre, hc, hw⟩ := VG.Proof.Rc2.X86_64.Stream.key_pre σ hs hv t ht
  simp only [VG.Proof.Rc2.X86_64.Stream.keyRd, VG.Proof.Rc2.X86_64.Stream.keyWr] at hpre hc hw
  obtain ⟨_, _, hrd, hwr, keyCtx, keyBuf, _, _, ctxBuf, _, _, retKey, _, retCtx, retBuf, _, stKey, _, stCtx, stBuf, _,
    _, _, _, _⟩ := hs
  have pendSub : Region.Sub ⟨σ.gpr .r9 + BitVec.ofNat 64 128, 8⟩ ⟨σ.gpr .r9, 144⟩ := Offset.sub_base _ (by decide)
  have bufSub : Region.Sub ⟨stackArg σ 0, 512⟩ ⟨stackArg σ 0, 576⟩ := Region.sub_prefix (by decide)
  have keySub : Region.Sub ⟨σ.gpr .r9, 128⟩ ⟨σ.gpr .r9, 144⟩ := Region.sub_prefix (by decide)
  refine WP.seq (WP.call (k := keyContract) key_correct VG.Proof.Rc2.X86_64.Stream.expandKey_noSp (by rw [VG.Proof.Rc2.X86_64.Stream.expandKey_depth]; decide)
    hpre hc hw ?_)
  intro s' _ _ callee' frame' _ ⟨s₂, mem₂, _, post₂⟩
  rw [VG.Proof.Rc2.X86_64.Stream.expandKey_depth, ht.rsp] at frame'
  have stackFrame : Frame [below (σ.gpr .rsp) 8] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, ht.rsp]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (below_call _ (by decide) (by decide))
  simp only [keyContract, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    ht.rdi, ht.rsi, ht.rdx, ht.rcx, mem₂] at post₂
  rw [Proof.Rc2.bytesAt_frame stackFrame _ _ (by omega) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact stKey.symm),
    ht.mem, Proof.Rc2.bytesAt_frame (frame_store64 _ _ _) _ _ (by omega) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact keyCtx.sub_right pendSub)] at post₂
  obtain ⟨s'', run, rax'', keep''⟩ := VG.Proof.Rc2.X86_64.Stream.zero_ok s'
  refine WP.of_runBlock ⟨s'', run, ⟨fun r hr => ?_, ?_⟩, fun direction => ?_⟩
  · rw [keep''.reg r (by revert hr; revert r; decide), callee' r hr, ht.callee r hr]
  · have callSep (R : Region) (hctx : R.Disjoint ⟨σ.gpr .r9, 144⟩) (hbuf : R.Disjoint ⟨stackArg σ 0, 576⟩)
        (hst : R.Disjoint (below (σ.gpr .rsp) 8)) :
        ∀ r ∈ [(⟨σ.gpr .r9, 128⟩ : Region), ⟨stackArg σ 0, 512⟩] ++ [below (σ.gpr .rsp) 8], R.Disjoint r := by
      intro r hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hctx.sub_right keySub
      · exact hbuf.sub_right bufSub
      · exact hst
    rw [keep''.mem, frame'.readW (r := ⟨σ.gpr .rsp, 8⟩) (Region.contains_self _ _)
        (callSep _ retCtx retBuf (Offset.base_disjoint_below _ (by decide))) (by decide), ht.mem,
      (frame_store64 _ _ _).readW (r := ⟨σ.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact retCtx.sub_right pendSub) (by decide)]
  · refine init_post (m' := s''.mem) (r := (s''.gpr .rax).setWidth 32) hv.1 hv.2.1 hv.2.2 (by rw [rax'']; rfl) (by rw [keep''.mem]; exact post₂) (iv := σ.gpr .rcx) ?_ direction
    rw [keep''.mem, show σ.gpr .r9 + 128 = σ.gpr .r9 + BitVec.ofNat 64 128 from rfl,
      blockAt_frame frame' _ (fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.disjoint_base _ (by decide) (by decide)
        · exact (ctxBuf.sub_left pendSub).sub_right bufSub
        · exact (stCtx.sub_right pendSub).symm),
      ht.mem, blockAt_copy]

theorem code_ne {a b c : Nat} (h : VG.Proof.Rc2.X86_64.Stream.code a b c ≠ 0) :
    VG.Proof.Rc2.X86_64.Stream.code a b c = if ¬(1 ≤ a ∧ a ≤ 128) then 1 else if ¬(1 ≤ b ∧ b ≤ 1024) then 2 else 3 := by
  unfold VG.Proof.Rc2.X86_64.Stream.code at h ⊢
  by_cases h₃ : c ≠ 8
  · simp [h₃]
  · simp only [h₃, ↓reduceIte] at h ⊢
    split at h <;> simp_all

theorem init_body_correct (σ : State) (hs : initContract.pre σ) : WP isa init σ (VG.Proof.Rc2.X86_64.Stream.InitPost σ) := by
  refine WP.seq (WP.mono (VG.Proof.Rc2.X86_64.Stream.checks_ok σ) fun t ⟨keep, zf, rax⟩ => ?_)
  refine WP.ite _ (by simp only [eval, zf]; rfl) (fun h => WP.block_nil ?_) (fun h => ?_)
  · have hc : VG.Proof.Rc2.X86_64.Stream.code (σ.gpr .rsi).toNat (σ.gpr .rdx).toNat (σ.gpr .r8).toNat ≠ 0 := by simpa using h
    have hr : ((t.gpr .rax).setWidth 32).toNat = VG.Proof.Rc2.X86_64.Stream.code (σ.gpr .rsi).toNat (σ.gpr .rdx).toNat (σ.gpr .r8).toNat := by
      have := VG.Proof.Rc2.X86_64.Stream.code_le (σ.gpr .rsi).toNat (σ.gpr .rdx).toNat (σ.gpr .r8).toNat
      rw [rax, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    refine ⟨⟨fun r hr' => keep.reg r (by revert hr'; revert r; decide), by rw [keep.mem]⟩, ?_⟩
    refine init_post_error (hr.trans (VG.Proof.Rc2.X86_64.Stream.code_ne hc)) (fun hv => hc ?_)
    simp only [VG.Proof.Rc2.X86_64.Stream.code, hv.1, hv.2.1, hv.2.2, not_true_eq_false, and_self, ↓reduceIte, ne_eq]
  · have hv := VG.Proof.Rc2.X86_64.Stream.valid_of_code (σ := σ) (by simpa using h)
    exact WP.seq (WP.mono (VG.Proof.Rc2.X86_64.Stream.initArgs_pre σ hs hv t keep) fun t' ht' => VG.Proof.Rc2.X86_64.Stream.keyCall_ok σ hs hv t' ht')

theorem init_correct (σ : State) (hs : initContract.pre σ) :
    ∃ t s', Exec isa init σ t s' ∧ abiPreserved σ s' ∧ initContract.post σ s' := by
  obtain ⟨t, s', he, ha, hp⟩ := VG.Proof.Rc2.X86_64.Stream.init_body_correct σ hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ha, hp⟩

end VG.Proof.Rc2.X86_64.Stream

end

section

/-! # Streaming RC2-CBC on x86-64: the update functions are constant time

The taint analysis checks the code before the call of the CBC function from
the public arguments; the call is constant time by the CBC function's proof,
with the arguments that correctness fixes (`Mid`), which are the same in two
runs that agree on the public arguments (the scratch pointer among them,
which the analysis cannot follow through its load from the stack). -/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64 VG.Impl.Rc2.X86_64 VG.Impl.Rc2.X86_64.Stream

def args : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]

def InitRel (d : Spec.Rc2.Direction) (s₁ s₂ : State) : Prop :=
  (VG.Proof.Rc2.X86_64.Stream.updateContract d).pre s₁ ∧ (VG.Proof.Rc2.X86_64.Stream.updateContract d).pre s₂ ∧ (VG.Proof.Rc2.X86_64.Stream.updateContract d).pub s₁ s₂

/-- After the test of `out_len`, from related entry states. -/
def TestRel (d : Spec.Rc2.Direction) (σ₁ σ₂ s₁ s₂ : State) : Prop :=
  VG.Proof.Rc2.X86_64.Stream.InitRel d σ₁ σ₂ ∧ Keep [] σ₁ s₁ ∧ Keep [] σ₂ s₂ ∧ s₁.zf = some (decide ((σ₁.gpr .r9).toNat = 0)) ∧
    s₂.zf = some (decide ((σ₂.gpr .r9).toNat = 0))

theorem cbc_constantTime (d : Spec.Rc2.Direction) :
    ConstantTime isa (Cbc.contract d).pre (Cbc.contract d).pub (Cbc.cbc d) := by
  cases d
  · exact Cbc.encrypt_constantTime _
  · exact Cbc.decrypt_constantTime _

theorem testRel_args {d : Spec.Rc2.Direction} {σ₁ σ₂ s₁ s₂ : State} (h : VG.Proof.Rc2.X86_64.Stream.TestRel d σ₁ σ₂ s₁ s₂) :
    ∀ r ∈ VG.Proof.Rc2.X86_64.Stream.args, s₁.gpr r = s₂.gpr r := by
  intro r hr
  rw [h.2.1.reg r (by simp), h.2.2.1.reg r (by simp)]
  exact h.1.2.2.1 r hr

theorem update_constantTime (d : Spec.Rc2.Direction) :
    ConstantTime isa (VG.Proof.Rc2.X86_64.Stream.updateContract d).pre (VG.Proof.Rc2.X86_64.Stream.updateContract d).pub (update d) := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  -- The test of `out_len`.
  have test : RelCT isa (VG.Proof.Rc2.X86_64.Stream.InitRel d) (.block [.alu .test .r9 (.reg .r9)])
      (fun s₁ s₂ => ∃ σ₁ σ₂, VG.Proof.Rc2.X86_64.Stream.TestRel d σ₁ σ₂ s₁ s₂) := by
    have ct := RelCT.taint (P := VG.Proof.Rc2.X86_64.Stream.InitRel d) (A := taint) (Taint.ofRegs VG.Proof.Rc2.X86_64.Stream.args)
      (fun _ _ h => Taint.agree_ofRegs h.2.2.1) (c := .block [.alu .test .r9 (.reg .r9)]) (by taint_decide)
    have hw (s : State) : WP isa (.block [.alu .test .r9 (.reg .r9)]) s
        (fun s' => Keep [] s s' ∧ s'.zf = some (decide ((s.gpr .r9).toNat = 0))) := by
      obtain ⟨s', run, zf, keep⟩ := VG.Proof.Rc2.X86_64.Stream.test_ok s .r9 (VG.Proof.Rc2.X86_64.Stream.toNat_eq _) (s.gpr .r9).isLt
      exact WP.of_runBlock ⟨s', run, keep, zf⟩
    refine (ct.wpDep (F := fun (s s' : State) => Keep [] s s' ∧ s'.zf = some (decide ((s.gpr .r9).toNat = 0)))
      (fun s₁ s₂ _ => ⟨hw s₁, hw s₂⟩)).mono (fun _ _ h => h) ?_
    rintro s₁ s₂ ⟨-, σ₁, σ₂, hp, ⟨k₁, z₁⟩, ⟨k₂, z₂⟩⟩
    exact ⟨σ₁, σ₂, hp, k₁, k₂, z₁, z₂⟩
  change RelCT isa (VG.Proof.Rc2.X86_64.Stream.InitRel d) (.seq _ (.ite .e short (.seq longPre (cbcCall d)))) (fun _ _ => True)
  refine test.seq (RelCT.exists_ fun σ₁ => RelCT.exists_ fun σ₂ => ?_)
  by_cases hI : VG.Proof.Rc2.X86_64.Stream.InitRel d σ₁ σ₂
  swap
  · exact RelCT.of_false fun _ _ h => hI h.1
  obtain ⟨hp₁, hp₂, hpub, hB⟩ := hI
  refine RelCT.ite (fun s₁ s₂ h => ?_) ?_ ?_
  · simp only [eval, h.2.2.2.1, h.2.2.2.2, hpub .r9 (by decide)]
  · -- No complete block: the taint analysis alone.
    exact RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Rc2.X86_64.Stream.args) (fun _ _ h => Taint.agree_ofRegs (VG.Proof.Rc2.X86_64.Stream.testRel_args h.1))
      (by taint_decide)
  · -- The copies, then the call.
    by_cases hz : (σ₁.gpr .r9).toNat = 0
    · refine RelCT.of_false fun s₁ s₂ h => ?_
      have e := h.2; simp only [eval, h.1.2.2.2.1, hz] at e; simp at e
    have hz₂ : (σ₂.gpr .r9).toNat ≠ 0 := by rw [← hpub .r9 (by decide)]; exact hz
    have pre := (RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Rc2.X86_64.Stream.args)
      (P := fun s₁ s₂ => VG.Proof.Rc2.X86_64.Stream.TestRel d σ₁ σ₂ s₁ s₂ ∧ isa.eval .e s₁ = some false)
      (fun _ _ h => Taint.agree_ofRegs (VG.Proof.Rc2.X86_64.Stream.testRel_args h.1)) (c := longPre)
      (by taint_decide)).wp (F₁ := VG.Proof.Rc2.X86_64.Stream.Mid σ₁) (F₂ := VG.Proof.Rc2.X86_64.Stream.Mid σ₂) fun s₁ s₂ h =>
        ⟨VG.Proof.Rc2.X86_64.Stream.long_ok d σ₁ hp₁ hz s₁ h.1.2.1, VG.Proof.Rc2.X86_64.Stream.long_ok d σ₂ hp₂ hz₂ s₂ h.1.2.2.1⟩
    refine RelCT.seq pre ?_
    have hrd : VG.Proof.Rc2.X86_64.Stream.callRd σ₂ = VG.Proof.Rc2.X86_64.Stream.callRd σ₁ := by simp only [VG.Proof.Rc2.X86_64.Stream.callRd, hpub .rdi (by decide)]
    have hwr : VG.Proof.Rc2.X86_64.Stream.callWr σ₂ = VG.Proof.Rc2.X86_64.Stream.callWr σ₁ := by
      simp only [VG.Proof.Rc2.X86_64.Stream.callWr, hpub .rdi (by decide), hpub .r8 (by decide), hpub .r9 (by decide), hB]
    rw [VG.Proof.Rc2.X86_64.Stream.cbcCall_eq]
    refine RelCT.call (VG.Proof.Rc2.X86_64.Stream.cbc_correct d) (VG.Proof.Rc2.X86_64.Stream.cbc_constantTime d) (VG.Proof.Rc2.X86_64.Stream.callRd σ₁) (VG.Proof.Rc2.X86_64.Stream.callWr σ₁) ?_
    rintro s₁ s₂ ⟨-, m₁, m₂⟩
    obtain ⟨pre₁, c₁, w₁⟩ := VG.Proof.Rc2.X86_64.Stream.call_pre d σ₁ hp₁ hz s₁ m₁
    obtain ⟨pre₂, c₂, w₂⟩ := VG.Proof.Rc2.X86_64.Stream.call_pre d σ₂ hp₂ hz₂ s₂ m₂
    rw [hrd, hwr] at pre₂ c₂
    rw [hwr] at w₂
    refine ⟨pre₁, pre₂, ?_, c₁, w₁, c₂, w₂, by rw [m₁.rsp, m₂.rsp, hpub .rsp (by decide)]⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [State.withRegions_gpr, State.callEntry_rsp, State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp),
        m₁.rdi, m₂.rdi, m₁.rsi, m₂.rsi, m₁.rdx, m₂.rdx, m₁.rcx, m₂.rcx, m₁.r8, m₂.r8, m₁.rsp, m₂.rsp,
        hpub .rdi (by decide), hpub .r8 (by decide), hpub .r9 (by decide), hpub .rsp (by decide), hB]

end VG.Proof.Rc2.X86_64.Stream

end

section

/-! # Streaming RC2-CBC on x86-64: `vg_rc2_cbc_init` is constant time

The length checks and the IV copy are checked by the taint analysis from the
public arguments; the call of key expansion is constant time by its proof,
with the arguments that correctness fixes (`KeyPre`). -/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64 VG.Impl.Rc2.X86_64 VG.Impl.Rc2.X86_64.Stream

def InitRelI (s₁ s₂ : State) : Prop := initContract.pre s₁ ∧ initContract.pre s₂ ∧ initContract.pub s₁ s₂

/-- After the checks, from related entry states. -/
def ChecksRel (σ₁ σ₂ s₁ s₂ : State) : Prop :=
  VG.Proof.Rc2.X86_64.Stream.InitRelI σ₁ σ₂ ∧ Keep [.rax, .r10] σ₁ s₁ ∧ Keep [.rax, .r10] σ₂ s₂ ∧
    s₁.zf = some (decide (VG.Proof.Rc2.X86_64.Stream.code (σ₁.gpr .rsi).toNat (σ₁.gpr .rdx).toNat (σ₁.gpr .r8).toNat = 0)) ∧
    s₂.zf = some (decide (VG.Proof.Rc2.X86_64.Stream.code (σ₂.gpr .rsi).toNat (σ₂.gpr .rdx).toNat (σ₂.gpr .r8).toNat = 0))

theorem checksRel_args {σ₁ σ₂ s₁ s₂ : State} (h : VG.Proof.Rc2.X86_64.Stream.ChecksRel σ₁ σ₂ s₁ s₂) : ∀ r ∈ VG.Proof.Rc2.X86_64.Stream.args, s₁.gpr r = s₂.gpr r := by
  intro r hr
  have hr' : r ∉ [Reg.rax, .r10] := by revert hr; revert r; decide
  rw [h.2.1.reg r hr', h.2.2.1.reg r hr']
  exact h.1.2.2.1 r hr

theorem init_constantTime : ConstantTime isa initContract.pre initContract.pub init := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  have chk : RelCT isa VG.Proof.Rc2.X86_64.Stream.InitRelI checks (fun s₁ s₂ => ∃ σ₁ σ₂, VG.Proof.Rc2.X86_64.Stream.ChecksRel σ₁ σ₂ s₁ s₂) := by
    have ct := RelCT.taint (P := VG.Proof.Rc2.X86_64.Stream.InitRelI) (A := taint) (Taint.ofRegs VG.Proof.Rc2.X86_64.Stream.args)
      (fun _ _ h => Taint.agree_ofRegs h.2.2.1) (c := checks) (by taint_decide)
    refine (ct.wpDep (fun s₁ s₂ _ => ⟨VG.Proof.Rc2.X86_64.Stream.checks_ok s₁, VG.Proof.Rc2.X86_64.Stream.checks_ok s₂⟩)).mono (fun _ _ h => h) ?_
    rintro s₁ s₂ ⟨-, σ₁, σ₂, hp, ⟨k₁, z₁, -⟩, ⟨k₂, z₂, -⟩⟩
    exact ⟨σ₁, σ₂, hp, k₁, k₂, z₁, z₂⟩
  change RelCT isa VG.Proof.Rc2.X86_64.Stream.InitRelI (.seq checks (.ite .ne (.block []) (.seq (.block initArgs)
    (.seq keyCall (.block [.mov32 .rax (.imm 0)]))))) (fun _ _ => True)
  refine chk.seq (RelCT.exists_ fun σ₁ => RelCT.exists_ fun σ₂ => ?_)
  by_cases hI : VG.Proof.Rc2.X86_64.Stream.InitRelI σ₁ σ₂
  swap
  · exact RelCT.of_false fun _ _ h => hI h.1
  obtain ⟨hp₁, hp₂, hpub, hB⟩ := hI
  have hcode : VG.Proof.Rc2.X86_64.Stream.code (σ₂.gpr .rsi).toNat (σ₂.gpr .rdx).toNat (σ₂.gpr .r8).toNat =
      VG.Proof.Rc2.X86_64.Stream.code (σ₁.gpr .rsi).toNat (σ₁.gpr .rdx).toNat (σ₁.gpr .r8).toNat := by
    rw [hpub .rsi (by decide), hpub .rdx (by decide), hpub .r8 (by decide)]
  refine RelCT.ite (fun s₁ s₂ h => ?_) (RelCT.block_nil fun _ _ _ => trivial) ?_
  · simp only [eval, h.2.2.2.1, h.2.2.2.2, hcode]
  by_cases hz : VG.Proof.Rc2.X86_64.Stream.code (σ₁.gpr .rsi).toNat (σ₁.gpr .rdx).toNat (σ₁.gpr .r8).toNat = 0
  swap
  · refine RelCT.of_false fun s₁ s₂ h => ?_
    have e := h.2; simp only [eval, h.1.2.2.2.1, hz] at e; simp at e
  have hv₁ := VG.Proof.Rc2.X86_64.Stream.valid_of_code hz
  have hv₂ := VG.Proof.Rc2.X86_64.Stream.valid_of_code (σ := σ₂) (by rw [hcode]; exact hz)
  have pre := (RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Rc2.X86_64.Stream.args)
    (P := fun s₁ s₂ => VG.Proof.Rc2.X86_64.Stream.ChecksRel σ₁ σ₂ s₁ s₂ ∧ isa.eval .ne s₁ = some false)
    (fun _ _ h => Taint.agree_ofRegs (VG.Proof.Rc2.X86_64.Stream.checksRel_args h.1)) (c := .block initArgs)
    (by taint_decide)).wp (F₁ := VG.Proof.Rc2.X86_64.Stream.KeyPre σ₁) (F₂ := VG.Proof.Rc2.X86_64.Stream.KeyPre σ₂) fun s₁ s₂ h =>
      ⟨VG.Proof.Rc2.X86_64.Stream.initArgs_pre σ₁ hp₁ hv₁ s₁ h.1.2.1, VG.Proof.Rc2.X86_64.Stream.initArgs_pre σ₂ hp₂ hv₂ s₂ h.1.2.2.1⟩
  refine RelCT.seq pre (RelCT.seq (R := fun _ _ => True) ?_ (RelCT.taint (A := taint) (Taint.ofRegs [])
    (P := fun _ _ => True) (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)))
  have hrd : VG.Proof.Rc2.X86_64.Stream.keyRd σ₂ = VG.Proof.Rc2.X86_64.Stream.keyRd σ₁ := by simp only [VG.Proof.Rc2.X86_64.Stream.keyRd, hpub .rdi (by decide), hpub .rsi (by decide)]
  have hwr : VG.Proof.Rc2.X86_64.Stream.keyWr σ₂ = VG.Proof.Rc2.X86_64.Stream.keyWr σ₁ := by simp only [VG.Proof.Rc2.X86_64.Stream.keyWr, hpub .r9 (by decide), hB]
  refine RelCT.call key_correct (expandKey_constantTime _) (VG.Proof.Rc2.X86_64.Stream.keyRd σ₁) (VG.Proof.Rc2.X86_64.Stream.keyWr σ₁) ?_
  rintro s₁ s₂ ⟨-, m₁, m₂⟩
  obtain ⟨pre₁, c₁, w₁⟩ := VG.Proof.Rc2.X86_64.Stream.key_pre σ₁ hp₁ hv₁ s₁ m₁
  obtain ⟨pre₂, c₂, w₂⟩ := VG.Proof.Rc2.X86_64.Stream.key_pre σ₂ hp₂ hv₂ s₂ m₂
  rw [hrd, hwr] at pre₂ c₂
  rw [hwr] at w₂
  refine ⟨pre₁, pre₂, ?_, c₁, w₁, c₂, w₂, by rw [m₁.rsp, m₂.rsp, hpub .rsp (by decide)]⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    simp only [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp),
      m₁.rdi, m₂.rdi, m₁.rsi, m₂.rsi, m₁.rdx, m₂.rdx, m₁.rcx, m₂.rcx, m₁.r8, m₂.r8,
      hpub .rdi (by decide), hpub .rsi (by decide), hpub .rdx (by decide), hpub .r9 (by decide), hB]

end VG.Proof.Rc2.X86_64.Stream

end

/-! # Streaming RC2-CBC on x86-64: verified against the shared contracts -/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64 VG.Impl.Rc2.X86_64.Stream

theorem init_verified : Verified target init (Proof.Rc2.cbcInitScratchContract abi 8) :=
  Verified.of_correct VG.Proof.Rc2.X86_64.Stream.init_correct VG.Proof.Rc2.X86_64.Stream.init_constantTime VG.Proof.Rc2.X86_64.Stream.init_implies

theorem encryptUpdate_verified :
    Verified target encryptUpdate (Proof.Rc2.cbcEncryptUpdateScratchContract abi 16) :=
  Verified.of_correct (VG.Proof.Rc2.X86_64.Stream.update_correct .encrypt) (VG.Proof.Rc2.X86_64.Stream.update_constantTime .encrypt) (VG.Proof.Rc2.X86_64.Stream.update_implies .encrypt)

theorem decryptUpdate_verified :
    Verified target decryptUpdate (Proof.Rc2.cbcDecryptUpdateScratchContract abi 16) :=
  Verified.of_correct (VG.Proof.Rc2.X86_64.Stream.update_correct .decrypt) (VG.Proof.Rc2.X86_64.Stream.update_constantTime .decrypt) (VG.Proof.Rc2.X86_64.Stream.update_implies .decrypt)

end VG.Proof.Rc2.X86_64.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86_64.Stream.Frame`. -/
section

/-!
# RC2-CBC's streaming functions on x86-64, with their working space on the stack

`init` and the updates have six argument words, so their working space was
their first stack argument. They run their code, proved with it as an
argument (`Verified.lean`), in a frame of 592 bytes that allocates it, after
a quadword standing for the return address and the buffer's address
(`Verified.stackArgScratchWiped`), and zero its 576 bytes before returning.
-/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64

/-- A state satisfying `vg_rc2_cbc_init`'s precondition, without the working
space. -/
def initFrameSat : State :=
  { VG.Proof.Rc2.X86_64.Stream.initSatState with
                      rd := [⟨0x1000, 0⟩, ⟨0x2000, 0⟩], wr := [⟨0x3000, 144⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Rc2.cbcInitContract X86_64.abi 600).pre s := by
  implies_sat [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, Spec.Rc2.cbcInitPost, X86_64.abi,
    X86_64.argRegs] [initFrameSat, initSatState] using VG.Proof.Rc2.X86_64.Stream.initFrameSat

theorem init_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratchWiped 592 0 72 Impl.Rc2.X86_64.Stream.init)
      (Spec.Rc2.cbcInitContract X86_64.abi 600) :=
  X86_64.Verified.stackArgScratchWiped (sig := Spec.Rc2.cbcInitSig) (nm := "scratch") (e := .u64)
    (n := 72) (post := Spec.Rc2.cbcInitPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 592) (words := 72) VG.Proof.Rc2.X86_64.Stream.init_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (cbcInitPost_local _)
    (cbcInitPostOut_local _) VG.Proof.Rc2.X86_64.Stream.initFrameSat_pre

/-- A state satisfying the update functions' precondition, without the
working space. -/
def updateFrameSat : State :=
  { VG.Proof.Rc2.X86_64.Stream.updateSatState with
                        rd := [⟨0x2000, 0⟩], wr := [⟨0x1000, 144⟩, ⟨0x3000, 0⟩] }

theorem updateFrameSat_pre (d : Spec.Rc2.Direction) :
    ∃ s, (Spec.Rc2.cbcUpdateContract X86_64.abi d 608).pre s := by
  implies_sat [Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig, Spec.Rc2.cbcUpdatePre,
    Spec.Rc2.cbcUpdatePost, X86_64.abi, X86_64.argRegs] [updateFrameSat, updateSatState]
    using VG.Proof.Rc2.X86_64.Stream.updateFrameSat

theorem encryptUpdate_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratchWiped 592 0 72
        Impl.Rc2.X86_64.Stream.encryptUpdate)
      (Spec.Rc2.cbcEncryptUpdateContract X86_64.abi 608) :=
  X86_64.Verified.stackArgScratchWiped (sig := Spec.Rc2.cbcUpdateSig) (nm := "scratch") (e := .u64)
    (n := 72) (pre := Spec.Rc2.cbcUpdatePre X86_64.abi.ptrBits)
    (post := Spec.Rc2.cbcUpdatePost .encrypt X86_64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 592) (words := 72) VG.Proof.Rc2.X86_64.Stream.encryptUpdate_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (cbcUpdatePre_local _) (cbcUpdatePost_local _ _) (cbcUpdatePostOut_local _ _)
    (VG.Proof.Rc2.X86_64.Stream.updateFrameSat_pre .encrypt)

theorem decryptUpdate_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratchWiped 592 0 72
        Impl.Rc2.X86_64.Stream.decryptUpdate)
      (Spec.Rc2.cbcDecryptUpdateContract X86_64.abi 608) :=
  X86_64.Verified.stackArgScratchWiped (sig := Spec.Rc2.cbcUpdateSig) (nm := "scratch") (e := .u64)
    (n := 72) (pre := Spec.Rc2.cbcUpdatePre X86_64.abi.ptrBits)
    (post := Spec.Rc2.cbcUpdatePost .decrypt X86_64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 592) (words := 72) VG.Proof.Rc2.X86_64.Stream.decryptUpdate_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (cbcUpdatePre_local _) (cbcUpdatePost_local _ _) (cbcUpdatePostOut_local _ _)
    (VG.Proof.Rc2.X86_64.Stream.updateFrameSat_pre .decrypt)

end VG.Proof.Rc2.X86_64.Stream

end
